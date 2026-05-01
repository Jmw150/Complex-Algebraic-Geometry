"""cag-audit: axiom/parameter monitoring for the CAG project.

Subcommands:
    list       — list all Axioms / Parameters
    diff       — compare current state against the last snapshot
    snapshot   — write a fresh snapshot to .cag/audit-snapshot.json
    suspect    — flag suspicious axioms (placeholder bodies, True-type, etc.)
    check NAME — run `rocq` Print Assumptions on a theorem and display its deps
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


SNAPSHOT_FILE = "audit-snapshot.json"


# ----- snapshot / diff -------------------------------------------------------


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def _collect(root: Path) -> list[Declaration]:
    decls = []
    for d in walk_theories(root / "theories"):
        if d.kind in ("Axiom", "Parameter"):
            decls.append(d)
    return decls


def _key(d: Declaration) -> str:
    return f"{d.kind}::{d.name}"


def cmd_list(root: Path, args) -> int:
    decls = _collect(root)
    if args.kind:
        decls = [d for d in decls if d.kind == args.kind.capitalize()]
    if args.file:
        decls = [d for d in decls if args.file in d.file]
    by_kind: dict[str, int] = {}
    for d in decls:
        by_kind[d.kind] = by_kind.get(d.kind, 0) + 1
        try:
            rel = str(Path(d.file).resolve().relative_to(root))
        except ValueError:
            rel = d.file
        if not args.summary:
            first = d.statement.splitlines()[0]
            print(f"[{d.kind}] {d.name}  {rel}:{d.line}")
            if first.strip():
                print(f"    {first.strip()[:100]}")
    print(f"\ntotal: {len(decls)}")
    for k, v in sorted(by_kind.items(), key=lambda kv: -kv[1]):
        print(f"  {k:14} {v}")
    return 0


def cmd_snapshot(root: Path, args) -> int:
    decls = _collect(root)
    snap = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "total": len(decls),
        "items": [
            {
                "kind": d.kind,
                "name": d.name,
                "file": str(Path(d.file).resolve().relative_to(root))
                if Path(d.file).is_absolute()
                else d.file,
                "line": d.line,
                "statement_first_line": (d.statement.splitlines()[0] if d.statement else ""),
            }
            for d in decls
        ],
    }
    out = root / ".cag" / SNAPSHOT_FILE
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(snap, indent=2))
    print(f"snapshot: {len(decls)} entries -> {out}")
    return 0


def cmd_diff(root: Path, args) -> int:
    snap_path = root / ".cag" / SNAPSHOT_FILE
    if not snap_path.exists():
        print(
            f"no snapshot at {snap_path}; run `cag-audit snapshot` first to create one",
            file=sys.stderr,
        )
        return 2
    snap = json.loads(snap_path.read_text())
    snap_keys = {f"{i['kind']}::{i['name']}": i for i in snap["items"]}
    cur_decls = _collect(root)
    cur_keys = {_key(d): d for d in cur_decls}

    added = sorted(set(cur_keys) - set(snap_keys))
    removed = sorted(set(snap_keys) - set(cur_keys))

    print(f"snapshot: {snap['generated']}, {snap['total']} entries")
    print(f"current : {len(cur_decls)} entries")
    print(f"delta   : +{len(added)} / -{len(removed)}")
    if added:
        print("\nADDED:")
        for k in added:
            d = cur_keys[k]
            try:
                rel = str(Path(d.file).resolve().relative_to(root))
            except ValueError:
                rel = d.file
            print(f"  + [{d.kind}] {d.name}  {rel}:{d.line}")
    if removed:
        print("\nREMOVED:")
        for k in removed:
            i = snap_keys[k]
            print(f"  - [{i['kind']}] {i['name']}  {i['file']}:{i['line']}")
    return 0 if not added and not removed else 1


# ----- suspect detection -----------------------------------------------------


_TRUE_BODY = re.compile(r":\s*True\s*\.")
_VACUOUS_FORALL = re.compile(r"forall\s+\w+\s*:\s*True\s*,")


def cmd_suspect(root: Path, args) -> int:
    decls = _collect(root)
    flagged: list[tuple[str, Declaration]] = []
    for d in decls:
        body = d.statement
        if _TRUE_BODY.search(body):
            flagged.append(("type-is-True", d))
        elif _VACUOUS_FORALL.search(body):
            flagged.append(("vacuous-forall", d))
    if not flagged:
        print("no suspect axioms found")
        return 0
    for tag, d in flagged:
        try:
            rel = str(Path(d.file).resolve().relative_to(root))
        except ValueError:
            rel = d.file
        print(f"[{tag}] [{d.kind}] {d.name}  {rel}:{d.line}")
        first = d.statement.splitlines()[0]
        print(f"    {first.strip()[:100]}")
    return 1


# ----- Print Assumptions runner ---------------------------------------------


def _find_decl_module(root: Path, name: str) -> str | None:
    """Heuristic: find which module declares `name`, return its CAG.<...> path."""
    for d in walk_theories(root / "theories"):
        if d.name == name:
            try:
                rel = Path(d.file).resolve().relative_to(root / "theories")
            except ValueError:
                return None
            module = ".".join(rel.with_suffix("").parts)
            return f"CAG.{module}"
    return None


def cmd_check(root: Path, args) -> int:
    name = args.name
    module = _find_decl_module(root, name)
    if module is None:
        print(f"error: no declaration named '{name}' found in the project", file=sys.stderr)
        return 2

    tmpfile = root / ".cag" / f"_check_{name}.v"
    tmpfile.parent.mkdir(parents=True, exist_ok=True)
    tmpfile.write_text(
        f"Require Import {module}.\n"
        f"Print Assumptions {name}.\n",
        encoding="utf-8",
    )

    rocq = os.environ.get("ROCQ", "rocq")
    cmd = [rocq, "compile", "-Q", "theories", "CAG", str(tmpfile)]
    print(f"$ {' '.join(cmd)}")
    out = subprocess.run(
        cmd,
        cwd=str(root),
        capture_output=True,
        text=True,
    )
    if out.returncode != 0:
        print("rocq failed:", out.stderr or out.stdout, file=sys.stderr)
        return out.returncode
    sys.stdout.write(out.stdout)
    if out.stderr.strip():
        sys.stderr.write(out.stderr)
    return 0


# ----- driver ----------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="cag-audit", description=__doc__)
    p.add_argument("--root", help="Project root (default: walk up from CWD)")
    sub = p.add_subparsers(dest="cmd")

    p_list = sub.add_parser("list", help="List all Axioms/Parameters")
    p_list.add_argument("--kind", help="Filter to Axiom or Parameter")
    p_list.add_argument("--file", help="Filter by file-path substring")
    p_list.add_argument("--summary", "-s", action="store_true", help="Only print counts")

    sub.add_parser("snapshot", help="Save current state to .cag/audit-snapshot.json")
    sub.add_parser("diff", help="Compare current state vs snapshot")
    sub.add_parser("suspect", help="Flag suspicious-shape axioms")

    p_check = sub.add_parser("check", help="Run `Print Assumptions` on a theorem")
    p_check.add_argument("name", help="Theorem/Lemma name to inspect")

    args = p.parse_args(argv)
    if not args.cmd:
        p.print_help()
        return 0

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    return {
        "list": cmd_list,
        "snapshot": cmd_snapshot,
        "diff": cmd_diff,
        "suspect": cmd_suspect,
        "check": cmd_check,
    }[args.cmd](root, args)


if __name__ == "__main__":
    sys.exit(main())
