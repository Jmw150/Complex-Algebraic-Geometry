"""Seed the hammer attempted-set from a completed hammer_probe report.

Reads .cag/hammer_probe_all_assumptions.json (or other report path),
and writes .cag/hammer_attempted.txt with one key per non-closed entry.
Keys are name::file::statement-hash, matching hammer_probe.py's _attempt_key.

Usage:
  python -m cag_audit.seed_attempted [--report PATH] [--out PATH]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from cag_lib.rocq_parse import walk_theories


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def _attempt_key(name: str, file: str, statement: str) -> str:
    h = hashlib.sha256(statement.encode("utf-8")).hexdigest()[:12]
    return f"{name}::{file}::{h}"


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--root", help="Project root (default: walk up)")
    p.add_argument("--report", help="hammer_probe report JSON")
    p.add_argument("--out", help="Output attempted-set file")
    args = p.parse_args()

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    report_path = (
        Path(args.report) if args.report
        else root / ".cag" / "hammer_probe_all_assumptions.json"
    )
    out_path = (
        Path(args.out) if args.out
        else root / ".cag" / "hammer_attempted.txt"
    )

    if not report_path.exists():
        raise SystemExit(f"error: report not found at {report_path}")

    report = json.loads(report_path.read_text(encoding="utf-8"))

    # Build a name -> (file, statement) lookup from current source.
    by_name = {}
    for d in walk_theories(root / "theories"):
        if d.kind in ("Axiom", "Parameter", "Conjecture"):
            rel = str(Path(d.file).resolve().relative_to(root))
            by_name[d.name] = (rel, d.statement)

    keys = set()
    matched = unmatched = 0
    for r in report.get("results", []):
        if r["status"] not in ("failed", "timeout"):
            continue
        info = by_name.get(r["name"])
        if info is None:
            unmatched += 1
            continue
        rel, statement = info
        keys.add(_attempt_key(r["name"], rel, statement))
        matched += 1

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(sorted(keys)) + "\n", encoding="utf-8")
    print(f"# seeded {len(keys)} keys to {out_path}")
    print(f"# matched={matched}, unmatched={unmatched} (renamed/removed since report)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
