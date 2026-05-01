"""cag-search CLI."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

from cag_search.index import open_db, rebuild, search, stats


# Default DB path is project_root/.cag/cag-index.db
def _default_db_path(project_root: Path) -> Path:
    return project_root / ".cag" / "cag-index.db"


def _detect_project_root(start: Path) -> Path:
    """Walk up from `start` to find the project root (has _CoqProject)."""
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit("error: no _CoqProject found in any parent of " + str(start))


def _color(text: str, code: str) -> str:
    if not sys.stdout.isatty() or os.environ.get("NO_COLOR"):
        return text
    return f"\033[{code}m{text}\033[0m"


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        prog="cag-search",
        description="Search the CAG project for declarations by keyword/kind/file.",
    )
    p.add_argument("query", nargs="*", help="FTS5 query (e.g. 'core free' or 'CReal arith')")
    p.add_argument("--kind", "-k", help="Filter by declaration kind (Lemma, Axiom, ...)")
    p.add_argument("--file", "-f", help="Filter by file-path substring (e.g. 'DecisionProblems')")
    p.add_argument("--limit", "-n", type=int, default=20, help="Max results")
    p.add_argument("--rebuild", action="store_true", help="Drop and rebuild the index")
    p.add_argument("--stats", action="store_true", help="Print index statistics")
    p.add_argument("--db", help="Path to index DB (default: <project>/.cag/cag-index.db)")
    p.add_argument(
        "--root",
        help="Project root (default: walk up from CWD until _CoqProject is found)",
    )
    args = p.parse_args(argv)

    if args.root:
        root = Path(args.root)
    else:
        root = _detect_project_root(Path.cwd())

    db_path = Path(args.db) if args.db else _default_db_path(root)
    conn = open_db(db_path)

    if args.rebuild:
        n, secs = rebuild(conn, root)
        print(f"indexed {n} declarations in {secs:.2f}s -> {db_path}")
        return 0

    if args.stats:
        s = stats(conn)
        print(f"total: {s['total']}")
        for kind, count in s["by_kind"].items():
            print(f"  {kind:14} {count}")
        print(f"db: {db_path}")
        return 0

    # Auto-build index if missing.
    if next(conn.execute("SELECT 1 FROM decls LIMIT 1"), None) is None:
        print(f"index empty, building from {root}/theories ...")
        n, secs = rebuild(conn, root)
        print(f"  -> {n} decls in {secs:.2f}s")

    query = " ".join(args.query)
    # Normalize kind capitalization to match what the parser stores.
    kind = args.kind.capitalize() if args.kind else None

    results = list(
        search(
            conn,
            query,
            kind=kind,
            file_substr=args.file,
            limit=args.limit,
        )
    )

    if not results:
        print("(no results)")
        return 1

    for score, name, kind_, file, line, first_line in results:
        rel = file
        try:
            rel = str(Path(file).resolve().relative_to(root))
        except ValueError:
            pass
        loc = f"{rel}:{line}"
        kind_str = _color(f"[{kind_}]", "33")  # yellow
        name_str = _color(name, "1;36")  # bold cyan
        loc_str = _color(loc, "2")  # dim
        print(f"{kind_str} {name_str}  {loc_str}")
        if first_line.strip():
            preview = first_line.strip()
            if len(preview) > 100:
                preview = preview[:97] + "..."
            print(f"    {preview}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
