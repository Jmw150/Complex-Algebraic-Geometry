"""Find Axioms / Parameters not referenced anywhere in the codebase.

A declaration is "unused" if its name does not appear (as a whole word)
in any .v file other than the one it's declared in. Limitations:
  - Whole-word grep, no module qualification awareness.
  - Doesn't run [Print Assumptions] — only static text search.

Useful for spotting Axioms that can probably be deleted outright.

Usage:
    python -m cag_audit.unused
    python -m cag_audit.unused --kind axiom    # axioms only
    python -m cag_audit.unused --kind parameter
"""

from __future__ import annotations

import argparse
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


def is_referenced_outside(name: str, src_root: Path, exclude: Path) -> bool:
    out = subprocess.run(
        ["grep", "-rn", "-w", name, str(src_root / "theories"), "--include=*.v"],
        capture_output=True, text=True,
    )
    if out.returncode not in (0, 1):
        return True
    excl = str(exclude.resolve())
    for line in out.stdout.splitlines():
        path = line.split(":", 1)[0]
        try:
            same = Path(path).resolve() == Path(excl).resolve()
        except Exception:
            same = False
        if not same:
            return True
    return False


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="cag-unused", description=__doc__)
    p.add_argument("--root", help="Project root")
    p.add_argument("--kind", default="Axiom",
                   help="Kind to scan (Axiom, Parameter, Lemma, ...)")
    p.add_argument("--include-singletons", action="store_true",
                   help="Also include declarations whose only reference is the declaration itself")
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    kind_norm = args.kind.capitalize()

    decls = [d for d in walk_theories(root / "theories") if d.kind == kind_norm]
    print(f"# scanning {len(decls)} {kind_norm}s for external references")
    unused = []
    for d in decls:
        ref = is_referenced_outside(d.name, root, Path(d.file))
        if not ref:
            unused.append(d)
    print(f"\n=== {len(unused)} unused {kind_norm}s ===")
    by_dir: dict[str, int] = {}
    for d in unused:
        rel = str(Path(d.file).resolve().relative_to(root))
        print(f"  {d.name:<40s} {rel}:{d.line}")
        top = rel.split("/")[1] if "/" in rel else rel
        by_dir[top] = by_dir.get(top, 0) + 1
    print("\nBy file/directory:")
    for k, v in sorted(by_dir.items(), key=lambda kv: -kv[1]):
        print(f"  {k:30s} {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
