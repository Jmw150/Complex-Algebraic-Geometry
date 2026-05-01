"""cag-tactic: Llemma-backed Rocq tactic suggester.

Usage:
    cag-tactic [-]                          # read goal from stdin
    cag-tactic --goal-file goal.txt
    cag-tactic --goal "forall x, P x -> Q x"
    cag-tactic --top-k 8                    # # of retrieved lemmas
    cag-tactic --max-tokens 512
    cag-tactic --raw                        # print model output verbatim

Configuration via environment variables:
    LLAMA_CLI       (default: ~/llama.cpp/build/bin/llama-cli)
    LLEMMA_MODEL    (default: ~/models/llemma_7b.Q4_K_M.gguf)

The tool retrieves potentially relevant lemmas from the project via
cag-search, builds a prompt, calls llama-cli on Llemma 7B, and parses
out tactic suggestions. The retrieval, prompt, and parser are all
local — no internet needed once the model is on disk.
"""

from __future__ import annotations

import argparse
import os
import re
import sqlite3
import subprocess
import sys
from pathlib import Path
from typing import Optional

from cag_search.index import open_db, search


# Identifier-like tokens (Rocq names) that we use as retrieval keys.
_IDENT = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']{2,}\b")
# Reserved Rocq tokens to ignore when picking retrieval keys.
_STOPWORDS = {
    "forall", "exists", "fun", "let", "in", "match", "with", "end",
    "if", "then", "else", "Type", "Set", "Prop", "True", "False",
    "and", "or", "not", "iff", "eq", "refl",
    "Lemma", "Theorem", "Corollary", "Definition", "Axiom",
    "Parameter", "Inductive", "Record",
    "Goal", "Goals", "subgoal", "subgoals",
    "Print", "Check", "Compute",
}


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def _extract_keywords(goal: str, max_n: int = 8) -> list[str]:
    """Pick out the most distinctive identifiers from the goal text."""
    seen: dict[str, int] = {}
    for tok in _IDENT.findall(goal):
        if tok in _STOPWORDS:
            continue
        # Lower-case-only short words probably aren't useful keys.
        if len(tok) <= 2:
            continue
        seen[tok] = seen.get(tok, 0) + 1
    # Order: tokens that appear once, in original order. (Frequent tokens
    # are usually variable names — less useful for retrieval.)
    ordered = []
    written = set()
    for tok in _IDENT.findall(goal):
        if tok in seen and tok not in written:
            ordered.append(tok)
            written.add(tok)
        if len(ordered) >= max_n:
            break
    return ordered


def _retrieve(conn: sqlite3.Connection, goal: str, top_k: int) -> list[tuple]:
    """Return up to top_k relevant declarations."""
    keys = _extract_keywords(goal)
    if not keys:
        return []
    # FTS5 query: OR over the keys, weighted by how many match.
    fts_query = " OR ".join(f'"{k}"' for k in keys)
    return list(search(conn, fts_query, limit=top_k))


def _format_retrieved(rows: list[tuple]) -> str:
    if not rows:
        return "(no relevant lemmas retrieved)"
    out = []
    for _score, name, kind, file, line, first_line in rows:
        snippet = first_line.strip()
        out.append(f"- [{kind}] {name}  ({Path(file).name}:{line})\n  {snippet}")
    return "\n".join(out)


PROMPT_TEMPLATE = """You are an expert in the Rocq (Coq) proof assistant. \
A user is trying to prove a goal in a project that has its own lemmas. \
Suggest 3 to 5 specific Rocq tactics that may make progress on the goal. \
Prefer tactics that use lemmas from the retrieved list. Be concrete: \
include the lemma names where relevant.

Format your answer EXACTLY as:

TACTIC: <tactic>
WHY: <short reason>

(repeat for each suggestion)

GOAL:
{goal}

POTENTIALLY RELEVANT LEMMAS FROM THIS PROJECT:
{retrieved}

ANSWER:
"""


def _llama_cli_path() -> str:
    return os.environ.get(
        "LLAMA_CLI",
        os.path.expanduser("~/llama.cpp/build/bin/llama-cli"),
    )


def _model_path() -> str:
    return os.environ.get(
        "LLEMMA_MODEL",
        os.path.expanduser("~/models/llemma_7b.Q4_K_M.gguf"),
    )


def _call_llama(prompt: str, max_tokens: int, temp: float = 0.2) -> str:
    cli = _llama_cli_path()
    model = _model_path()
    if not Path(cli).exists():
        raise SystemExit(f"error: llama-cli not found at {cli}")
    if not Path(model).exists():
        raise SystemExit(f"error: model not found at {model}")
    cmd = [
        cli,
        "-m", model,
        "-p", prompt,
        "-n", str(max_tokens),
        "--temp", str(temp),
        "--no-display-prompt",
        "-no-cnv",
        "-c", "4096",
        "--threads", str(os.cpu_count() or 2),
    ]
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode != 0:
        sys.stderr.write(out.stderr)
        raise SystemExit(f"llama-cli exited {out.returncode}")
    return out.stdout


_TACTIC_BLOCK = re.compile(
    r"TACTIC:\s*(?P<tac>.+?)\s*\n\s*WHY:\s*(?P<why>.+?)(?=\n(?:TACTIC:|\Z|---))",
    re.DOTALL,
)


def _parse_suggestions(text: str) -> list[tuple[str, str]]:
    out = []
    for m in _TACTIC_BLOCK.finditer(text):
        tac = m.group("tac").strip().splitlines()[0]
        why = m.group("why").strip().splitlines()[0]
        out.append((tac, why))
    return out


def _read_goal(args) -> str:
    if args.goal:
        return args.goal
    if args.goal_file:
        return Path(args.goal_file).read_text(encoding="utf-8")
    if args.positional == ["-"] or not args.positional:
        return sys.stdin.read()
    # If positional args were given, treat them as the goal text.
    return " ".join(args.positional)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="cag-tactic", description=__doc__)
    p.add_argument("positional", nargs="*", help="goal text (or '-' to read stdin)")
    p.add_argument("--goal", help="goal text on the command line")
    p.add_argument("--goal-file", help="read goal from a file")
    p.add_argument("--top-k", type=int, default=8, help="# retrieved lemmas")
    p.add_argument("--max-tokens", type=int, default=512, help="cap on model output")
    p.add_argument("--temp", type=float, default=0.2, help="sampling temperature")
    p.add_argument("--raw", action="store_true", help="print model output verbatim")
    p.add_argument("--root", help="Project root (default: walk up from CWD)")
    p.add_argument("--db", help="path to cag-search index DB")
    p.add_argument(
        "--show-retrieved",
        action="store_true",
        help="print the retrieved-lemma list and exit (no model call)",
    )
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    db_path = Path(args.db) if args.db else (root / ".cag" / "cag-index.db")
    if not db_path.exists():
        raise SystemExit(
            f"error: index DB not found at {db_path}; run `cag-search --rebuild` first"
        )
    conn = open_db(db_path)

    goal = _read_goal(args).strip()
    if not goal:
        raise SystemExit("error: empty goal; pass via stdin, --goal, or --goal-file")

    rows = _retrieve(conn, goal, args.top_k)
    retrieved = _format_retrieved(rows)

    if args.show_retrieved:
        print("RETRIEVED LEMMAS:\n" + retrieved)
        return 0

    prompt = PROMPT_TEMPLATE.format(goal=goal, retrieved=retrieved)
    output = _call_llama(prompt, args.max_tokens, args.temp)

    if args.raw:
        sys.stdout.write(output)
        return 0

    suggestions = _parse_suggestions(output)
    if not suggestions:
        print("(no tactics parsed; rerun with --raw to see model output)")
        sys.stdout.write(output)
        return 1

    print("RETRIEVED:\n" + retrieved + "\n")
    print("SUGGESTED TACTICS:\n")
    for i, (tac, why) in enumerate(suggestions, 1):
        print(f"  {i}. {tac}")
        print(f"     -> {why}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
