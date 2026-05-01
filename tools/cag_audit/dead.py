"""Find Axioms that are not referenced ANYWHERE in the project, including
their own file (excluding the declaration line itself).

Truly dead axioms can be removed outright with no functional consequence.
"""

from __future__ import annotations

import argparse
import re
import subprocess
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


def name_uses_outside_decl(name: str, file: Path, decl_line: int,
                           src_root: Path) -> int:
    """Count whole-word references to NAME in any .v file, excluding the
    line of NAME's own declaration."""
    out = subprocess.run(
        ["grep", "-rn", "-w", name, str(src_root / "theories"),
         "--include=*.v"],
        capture_output=True, text=True,
    )
    if out.returncode not in (0, 1):
        return -1
    own = str(file.resolve())
    count = 0
    for line in out.stdout.splitlines():
        try:
            path, lineno, _ = line.split(":", 2)
        except ValueError:
            continue
        try:
            same_file = Path(path).resolve() == Path(own).resolve()
        except Exception:
            same_file = False
        if same_file and lineno == str(decl_line):
            continue  # the declaration line itself
        count += 1
    return count


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="cag-dead", description=__doc__)
    p.add_argument("--root", help="Project root")
    p.add_argument("--kind", default="Axiom",
                   help="Kind to scan (Axiom or Parameter)")
    p.add_argument("--limit", type=int, default=None)
    args = p.parse_args(argv)
    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    kind_norm = args.kind.capitalize()

    decls = [d for d in walk_theories(root / "theories") if d.kind == kind_norm]
    print(f"# scanning {len(decls)} {kind_norm}s for any non-decl reference")
    dead = []
    for d in decls:
        n = name_uses_outside_decl(d.name, Path(d.file), d.line, root)
        if n == 0:
            dead.append(d)
        if args.limit and len(dead) >= args.limit:
            break
    print(f"\n=== {len(dead)} truly dead {kind_norm}s ===")
    by_dir: dict[str, int] = {}
    for d in dead:
        rel = str(Path(d.file).resolve().relative_to(root))
        print(f"  {d.name:<45s} {rel}:{d.line}")
        top = rel.split("/")[1] if "/" in rel else rel
        by_dir[top] = by_dir.get(top, 0) + 1
    print("\nBy file/directory:")
    for k, v in sorted(by_dir.items(), key=lambda kv: -kv[1]):
        print(f"  {k:30s} {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
