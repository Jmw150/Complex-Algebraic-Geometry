"""cag-dups: report duplicate / near-duplicate declarations across the project.

Two checks:
  1. Exact name duplicates: same NAME appears in different files. (Coq's
     Module-qualified naming makes this *legal* but often unintentional.)
  2. Near-duplicate statements within a kind: if two distinct declarations
     have nearly identical statements (after stripping comments and
     whitespace), they may be redundant.

Run via cag-search's existing SQLite index (`.cag/cag-index.db`).

Usage:
  python -m cag_audit.dups                  # both checks
  python -m cag_audit.dups --names-only     # just exact-name duplicates
  python -m cag_audit.dups --bodies-only    # just statement-similarity
  python -m cag_audit.dups --kind Axiom     # restrict to a kind
"""

from __future__ import annotations

import argparse
import re
import sqlite3
import sys
from pathlib import Path


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def _normalize_body(body: str) -> str:
    """Strip the `Kind name :` head and normalize whitespace."""
    head = re.match(
        r"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
        r"(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark|"
        r"Definition|Fixpoint|CoFixpoint|Axiom|Parameter|Hypothesis|"
        r"Conjecture|Example|Inductive|CoInductive|Class|Instance|"
        r"Record|Structure|Variant)\s+\w+\s*",
        body,
    )
    rest = body[head.end():] if head else body
    rest = rest.lstrip(":").strip().rstrip(".")
    rest = re.sub(r"\s+", " ", rest)
    return rest


def name_duplicates(db: sqlite3.Connection, kind: str | None) -> list[tuple]:
    """Returns [(name, [(file,line,kind,statement)...])]."""
    sql = (
        "SELECT name, file, line, kind, statement FROM decls "
        "WHERE name IN (SELECT name FROM decls "
        + (f"WHERE kind = ? " if kind else "")
        + "GROUP BY name HAVING COUNT(*) > 1) "
        + (f"AND kind = ? " if kind else "")
        + "ORDER BY name, file"
    )
    args = (kind, kind) if kind else ()
    by_name: dict[str, list[tuple]] = {}
    for name, file, line, k, statement in db.execute(sql, args):
        by_name.setdefault(name, []).append((file, line, k, statement))
    return [(n, locs) for n, locs in sorted(by_name.items()) if len(locs) > 1]


def body_similar(db: sqlite3.Connection, kind: str | None,
                 min_chars: int = 40) -> list[tuple]:
    """Find pairs of declarations with identical normalized bodies."""
    sql = "SELECT name, file, line, kind, statement FROM decls"
    args = ()
    if kind:
        sql += " WHERE kind = ?"
        args = (kind,)
    rows = list(db.execute(sql, args))
    by_norm: dict[str, list[tuple]] = {}
    for name, file, line, k, st in rows:
        n = _normalize_body(st)
        if len(n) < min_chars:
            continue
        by_norm.setdefault(n, []).append((name, file, line, k))
    out = []
    for body, hits in by_norm.items():
        if len(hits) > 1:
            distinct_names = {h[0] for h in hits}
            if len(distinct_names) > 1:
                out.append((body, hits))
    out.sort(key=lambda t: (-len(t[1]), t[0]))
    return out


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="cag-dups", description=__doc__)
    p.add_argument("--root", help="Project root")
    p.add_argument("--db", help="Path to cag-search index DB")
    p.add_argument("--kind", help="Filter to a single Kind (Axiom, Lemma, ...)")
    p.add_argument("--names-only", action="store_true", help="Only check exact name duplicates")
    p.add_argument("--bodies-only", action="store_true", help="Only check near-identical statements")
    p.add_argument("--limit", type=int, default=80)
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    db_path = Path(args.db) if args.db else (root / ".cag" / "cag-index.db")
    if not db_path.exists():
        raise SystemExit(f"error: no index at {db_path}; run cag-search --rebuild")

    db = sqlite3.connect(str(db_path))

    if not args.bodies_only:
        kind = args.kind.capitalize() if args.kind else None
        dups = name_duplicates(db, kind)
        print(f"=== Name duplicates ({len(dups)} names) ===")
        for name, locs in dups[: args.limit]:
            kinds = sorted({k for (_, _, k, _) in locs})
            print(f"\n{name}  (×{len(locs)})  [{', '.join(kinds)}]")
            for file, line, _k, _ in locs:
                rel = file.replace(str(root) + "/", "")
                print(f"  {rel}:{line}")
        if len(dups) > args.limit:
            print(f"\n... and {len(dups) - args.limit} more (use --limit N)")

    if not args.names_only:
        kind = args.kind.capitalize() if args.kind else None
        sim = body_similar(db, kind)
        print(f"\n=== Identical-body pairs across distinct names ({len(sim)} groups) ===")
        for body, hits in sim[: args.limit]:
            preview = body[:80]
            print(f"\n  body: {preview}{'...' if len(body) > 80 else ''}")
            for n, file, line, k in hits:
                rel = file.replace(str(root) + "/", "")
                print(f"    [{k}] {n}  {rel}:{line}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
