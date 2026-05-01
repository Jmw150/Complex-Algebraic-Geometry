"""Apply the hits from a hammer-probe report.

Reads .cag/hammer_probe_report.json (from cag_audit.hammer_probe) and, for each
"closed" entry, rewrites the source file to convert
    Axiom NAME : <type>.
to
    Theorem NAME : <type>.
    Proof. <tactic>. Qed.

Default mode: dry-run, prints a unified diff. Pass --apply to actually edit.

Usage:
  python -m cag_audit.apply_hits                # dry-run
  python -m cag_audit.apply_hits --apply        # in-place edit
  python -m cag_audit.apply_hits --report PATH
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from pathlib import Path


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def make_axiom_re(name: str) -> re.Pattern:
    """Match `Axiom NAME : <type>.` (multi-line, balanced)."""
    return re.compile(
        r"(?P<head>^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
        r"(?:Axiom|Parameter)\s+" + re.escape(name) + r"\s*:\s*)"
        r"(?P<body>.*?)"
        r"(?P<dot>\.\s*$)",
        re.MULTILINE | re.DOTALL,
    )


def find_axiom_block(src: str, name: str) -> tuple[int, int, str] | None:
    """Locate the `Axiom NAME : ... .` block. Returns (start, end, body_type)."""
    # Find the line that starts with `Axiom NAME` etc.
    pat = re.compile(
        r"^(?P<head>\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
        r"(?:Axiom|Parameter)\s+" + re.escape(name) + r"\s*:\s*)",
        re.MULTILINE,
    )
    m = pat.search(src)
    if not m:
        return None
    start = m.start()
    # Walk forward through the source to find the statement-end `.`,
    # respecting parens/braces/brackets and string literals.
    i = m.end()
    depth = 0
    in_string = False
    n = len(src)
    while i < n:
        c = src[i]
        if in_string:
            if c == '"':
                if i + 1 < n and src[i + 1] == '"':
                    i += 2
                    continue
                in_string = False
            i += 1
            continue
        if c == '"':
            in_string = True
            i += 1
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "." and depth == 0:
            if i + 1 == n or src[i + 1] in " \t\n\r":
                end = i + 1
                body = src[m.end():i].strip()
                return (start, end, body)
        i += 1
    return None


def make_replacement(orig_src: str, start: int, end: int, name: str,
                     body: str, tactic: str) -> str:
    # Preserve leading whitespace of the original line.
    line_start = orig_src.rfind("\n", 0, start) + 1
    indent = orig_src[line_start:start]
    new_block = (
        f"{indent}Theorem {name} : {body}.\n"
        f"{indent}Proof. {tactic}. Qed."
    )
    return orig_src[:start] + new_block + orig_src[end:]


def patch_file(file: Path, hits: list[dict], tactic: str) -> tuple[str, str, int]:
    src = file.read_text(encoding="utf-8")
    cur = src
    n_applied = 0
    for h in hits:
        block = find_axiom_block(cur, h["name"])
        if block is None:
            print(f"  warn: could not find Axiom {h['name']} in {file}", file=sys.stderr)
            continue
        start, end, body = block
        cur = make_replacement(cur, start, end, h["name"], body, tactic)
        n_applied += 1
    return src, cur, n_applied


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="cag-apply-hits", description=__doc__)
    p.add_argument("--report", help="Probe report JSON (default: .cag/hammer_probe_report.json)")
    p.add_argument("--root", help="Project root")
    p.add_argument("--apply", action="store_true", help="Actually rewrite files")
    p.add_argument("--tactic-override", help="Use this tactic in place of report's tactic")
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    report_path = (
        Path(args.report) if args.report else (root / ".cag" / "hammer_probe_report.json")
    )
    if not report_path.exists():
        print(f"error: no probe report at {report_path}", file=sys.stderr)
        return 2
    report = json.loads(report_path.read_text())
    hits = [r for r in report["results"] if r["status"] == "closed"]
    if not hits:
        print("(no closed axioms in this report — nothing to apply)")
        return 0

    tactic = args.tactic_override or report["tactic"]

    # Group by file.
    by_file: dict[str, list[dict]] = {}
    for h in hits:
        by_file.setdefault(h["file"], []).append(h)

    n_applied_total = 0
    for rel, file_hits in by_file.items():
        file = root / rel
        if not file.exists():
            print(f"  warn: missing {file}", file=sys.stderr)
            continue
        before, after, n = patch_file(file, file_hits, tactic)
        if n == 0:
            continue
        n_applied_total += n
        if args.apply:
            file.write_text(after, encoding="utf-8")
            print(f"  edited {rel}: {n} axiom(s) -> theorem")
        else:
            diff = difflib.unified_diff(
                before.splitlines(keepends=True),
                after.splitlines(keepends=True),
                fromfile=f"a/{rel}", tofile=f"b/{rel}",
            )
            sys.stdout.writelines(diff)

    if not args.apply:
        print(f"\n# dry run: {n_applied_total} edit(s) would be made; use --apply to commit")
    else:
        print(f"\n# applied {n_applied_total} edit(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
