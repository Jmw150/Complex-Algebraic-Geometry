"""Hint-driven hammer probe.

Improvement over `hammer_probe.py`: for each axiom, retrieve the top-K
relevant lemmas via cag-search's FTS5 index, then try

  Proof. sauto use: lem1, lem2, ... unfold: defn1, defn2, ... .

If sauto fails, try

  Proof. hammer.

Hint candidates come from a keyword-based query against the axiom's
type, filtered by Kind in (Lemma, Theorem, Corollary). Top-K is small
(default 6) to keep the prompt to sauto reasonable.

Usage:
    python -m cag_audit.hint_probe --timeout 12 --top-k 6
    python -m cag_audit.hint_probe --only-file FreeGroup
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

from cag_lib.rocq_parse import Declaration, walk_theories
from cag_audit.hammer_probe import (
    _detect_root,
    extract_type,
    file_to_module,
)
from cag_search.index import open_db, search


# Identifier-like tokens (Rocq names) that we use as retrieval keys.
_IDENT = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']{2,}\b")
_STOP = {
    "forall","exists","fun","let","in","match","with","end","if","then","else",
    "Type","Set","Prop","True","False","and","or","not","iff","eq","refl",
    "Lemma","Theorem","Corollary","Definition","Axiom","Parameter",
}


def keywords_of(typ: str, max_n: int = 8) -> list[str]:
    seen: dict[str, int] = {}
    for tok in _IDENT.findall(typ):
        if tok in _STOP or len(tok) <= 2:
            continue
        seen[tok] = seen.get(tok, 0) + 1
    out = []
    written = set()
    for tok in _IDENT.findall(typ):
        if tok in seen and tok not in written:
            out.append(tok)
            written.add(tok)
        if len(out) >= max_n:
            break
    return out


def fetch_hints(conn, typ: str, top_k: int, axiom_name: str) -> list[str]:
    keys = keywords_of(typ)
    if not keys:
        return []
    fts_query = " OR ".join(f'"{k}"' for k in keys)
    rows = list(search(conn, fts_query, kind="Lemma", limit=top_k * 2))
    rows += list(search(conn, fts_query, kind="Theorem", limit=top_k))
    rows += list(search(conn, fts_query, kind="Corollary", limit=top_k))
    rows.sort(key=lambda r: r[0])  # ascending bm25 score
    out = []
    for _score, name, _kind, _file, _line, _first in rows:
        if name == axiom_name:
            continue
        if name not in out:
            out.append(name)
        if len(out) >= top_k:
            break
    return out


def make_probe(out_dir: Path, axiom: Declaration, root: Path,
               hints: list[str], tactic: str, atp_limit: int) -> Path | None:
    typ = extract_type(axiom.statement)
    if typ is None:
        return None
    module = file_to_module(axiom.file, root)
    use_clause = ", ".join(hints) if hints else ""
    tactic_full = (
        f"{tactic} use: {use_clause}" if use_clause and tactic in ("sauto", "hauto", "qauto")
        else tactic
    )
    probe = out_dir / f"_hp_{axiom.name}.v"
    probe.write_text(
        f"From Hammer Require Import Hammer Tactics.\n"
        f"Require Import {module}.\n"
        f"Set Hammer ATPLimit {atp_limit}.\n"
        f"Goal {typ}.\n"
        f"Proof. {tactic_full}. Qed.\n",
        encoding="utf-8",
    )
    return probe


def run_probe(root: Path, probe: Path, wall_timeout: int) -> tuple[bool, float, str]:
    cmd = ["rocq", "compile", "-Q", "theories", "CAG", str(probe)]
    t0 = time.monotonic()
    try:
        res = subprocess.run(cmd, cwd=str(root),
                             capture_output=True, text=True, timeout=wall_timeout)
        dt = time.monotonic() - t0
        if res.returncode == 0:
            return True, dt, ""
        last = (res.stderr.strip().splitlines() or
                res.stdout.strip().splitlines() or [""])[-1]
        return False, dt, last[:200]
    except subprocess.TimeoutExpired:
        return False, wall_timeout, "TIMEOUT"


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="cag-hint-probe", description=__doc__)
    p.add_argument("--root", help="Project root")
    p.add_argument("--db", help="Path to cag-search index DB")
    p.add_argument("--timeout", type=int, default=15)
    p.add_argument("--atp-limit", type=int, default=10)
    p.add_argument("--top-k", type=int, default=6)
    p.add_argument("--limit", type=int, default=None)
    p.add_argument("--only-file", help="Restrict by file path substring")
    p.add_argument("--report", help="JSON output path")
    p.add_argument("--keep-probes", action="store_true")
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    db_path = Path(args.db) if args.db else (root / ".cag" / "cag-index.db")
    conn = open_db(db_path)

    axioms = []
    for d in walk_theories(root / "theories"):
        if d.kind != "Axiom":
            continue
        if args.only_file and args.only_file not in d.file:
            continue
        axioms.append(d)
    if args.limit:
        axioms = axioms[: args.limit]

    out_dir = root / ".cag" / "probes"
    out_dir.mkdir(parents=True, exist_ok=True)
    report_path = (
        Path(args.report) if args.report else (root / ".cag" / "hint_probe_report.json")
    )
    report = {
        "started": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "timeout": args.timeout, "atp_limit": args.atp_limit, "top_k": args.top_k,
        "results": [],
    }
    closed_total = 0
    print(f"# probing {len(axioms)} axioms with hint-driven sauto+hammer "
          f"(timeout {args.timeout}s, top-k {args.top_k})")

    for i, ax in enumerate(axioms, 1):
        rel = str(Path(ax.file).resolve().relative_to(root))
        typ = extract_type(ax.statement)
        if typ is None:
            print(f"[{i}/{len(axioms)}] {ax.name:<40s} SKIP")
            report["results"].append(
                {"name": ax.name, "file": rel, "line": ax.line, "status": "skipped"})
            continue
        hints = fetch_hints(conn, typ, args.top_k, ax.name)
        # First try sauto + hints
        result = {"name": ax.name, "file": rel, "line": ax.line, "hints": hints}
        probe = make_probe(out_dir, ax, root, hints, "sauto", args.atp_limit)
        ok, dt, msg = run_probe(root, probe, args.timeout)
        if not args.keep_probes:
            probe.unlink(missing_ok=True)
        if ok:
            result.update({"status": "closed", "tactic": "sauto-hint", "secs": round(dt, 2)})
            print(f"[{i}/{len(axioms)}] {ax.name:<40s} ✓ sauto+hint {dt:4.1f}s")
            closed_total += 1
            report["results"].append(result)
            if i % 10 == 0:
                report_path.write_text(json.dumps(report, indent=2))
            continue
        # Then try hammer (no hints — hammer's own predictor takes over)
        probe = make_probe(out_dir, ax, root, [], "hammer", args.atp_limit)
        ok, dt2, msg2 = run_probe(root, probe, args.timeout)
        if not args.keep_probes:
            probe.unlink(missing_ok=True)
        if ok:
            result.update({"status": "closed", "tactic": "hammer", "secs": round(dt2, 2)})
            print(f"[{i}/{len(axioms)}] {ax.name:<40s} ✓ hammer    {dt2:4.1f}s")
            closed_total += 1
        else:
            status = "timeout" if msg2 == "TIMEOUT" else "failed"
            result.update({"status": status, "secs": round(dt2, 2), "msg": msg2})
            print(f"[{i}/{len(axioms)}] {ax.name:<40s} {status:7s} ({dt2:4.1f}s)")
        report["results"].append(result)
        if i % 10 == 0:
            report_path.write_text(json.dumps(report, indent=2))

    report["finished"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    report["total"] = len(axioms)
    report["closed"] = closed_total
    report_path.write_text(json.dumps(report, indent=2))
    print(f"\n# done: {closed_total}/{len(axioms)} closed -> {report_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
