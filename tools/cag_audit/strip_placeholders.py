"""Strip True-bodied placeholder Theorems / Lemmas / Corollaries.

For each declaration of the shape

    [Theorem|Lemma|Corollary] NAME : <type ending in `True`>.
    Proof. <ends with `exact I.` or similar>. Qed.

verify that the name is not referenced elsewhere in the codebase, then
remove the declaration and replace it with a one-line comment recording
its prior existence.

Usage:
    python -m cag_audit.strip_placeholders                  # dry-run
    python -m cag_audit.strip_placeholders --apply
    python -m cag_audit.strip_placeholders --only-file X    # one file
"""

from __future__ import annotations

import argparse
import difflib
import re
import sqlite3
import subprocess
import sys
from pathlib import Path
from typing import Iterable

from cag_lib.rocq_parse import iter_declarations


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def is_true_bodied(statement: str) -> bool:
    head = statement.split(":", 1)
    if len(head) < 2:
        return False
    body = head[1].strip()
    if body.endswith("."):
        body = body[:-1]
    body_norm = re.sub(r"\s+", " ", body).strip()
    return (
        body_norm.endswith(", True")
        or body_norm.endswith(": True")
        or body_norm == "True"
    )


def find_full_proof_block(src: str, decl_start: int) -> tuple[int, str] | None:
    """From the start of `Theorem name : ...` find the end of `... Qed.`
    (or `Defined.` / `Admitted.`).
    Returns (end_offset_exclusive, text_of_block)."""
    # Walk forward looking for terminators.
    i = decl_start
    n = len(src)
    in_string = False
    depth = 0
    saw_period_after_qed = False
    while i < n:
        c = src[i]
        if in_string:
            if c == '"':
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
        # Look for Qed/Defined/Admitted at top-level.
        if depth == 0:
            for kw in ("Qed.", "Defined.", "Admitted.", "Abort."):
                if src[i:i + len(kw)] == kw:
                    nxt = i + len(kw)
                    return (nxt, src[decl_start:nxt])
        i += 1
    return None


def is_referenced(name: str, src_root: Path, exclude_file: Path) -> bool:
    """Run grep across all .v files to see if `name` is referenced anywhere
    other than the declaration site. Crude but adequate."""
    out = subprocess.run(
        ["grep", "-rn", "-w", name,
         str(src_root / "theories"),
         "--include=*.v"],
        capture_output=True, text=True,
    )
    if out.returncode not in (0, 1):
        return True  # be safe if grep barfs
    excl = str(exclude_file.resolve())
    for line in out.stdout.splitlines():
        path = line.split(":", 1)[0]
        try:
            same = Path(path).resolve() == Path(excl).resolve()
        except Exception:
            same = False
        if not same:
            return True
    return False


def patch_file(file: Path, src_root: Path, dry_run: bool) -> tuple[int, int]:
    src = file.read_text(encoding="utf-8")
    decls = list(iter_declarations(file))
    targets = []
    for d in decls:
        if d.kind not in ("Theorem", "Lemma", "Corollary"):
            continue
        if not is_true_bodied(d.statement):
            continue
        targets.append(d)
    if not targets:
        return (0, 0)

    new_src = src
    n_skipped = 0
    n_applied = 0
    # Process targets in REVERSE source order so offsets stay valid.
    for d in sorted(targets, key=lambda x: -x.line):
        if is_referenced(d.name, src_root, file):
            n_skipped += 1
            continue
        # Find the declaration start in the current new_src.
        # Match by name+kind at the right line; safer to grep on a wider window.
        pat = re.compile(
            r"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
            + d.kind + r"\s+" + re.escape(d.name) + r"\b",
            re.MULTILINE,
        )
        m = pat.search(new_src)
        if m is None:
            n_skipped += 1
            continue
        block = find_full_proof_block(new_src, m.start())
        if block is None:
            n_skipped += 1
            continue
        end, _block_text = block
        comment = (
            f"(* Removed True-bodied placeholder {d.kind} `{d.name}` on "
            f"2026-04-30 cleanup pass; not referenced elsewhere. *)"
        )
        new_src = new_src[: m.start()] + comment + new_src[end:]
        n_applied += 1

    if n_applied == 0:
        return (0, n_skipped)

    if not dry_run:
        file.write_text(new_src, encoding="utf-8")
    else:
        diff = difflib.unified_diff(
            src.splitlines(keepends=True),
            new_src.splitlines(keepends=True),
            fromfile=f"a/{file}", tofile=f"b/{file}",
        )
        sys.stdout.writelines(diff)
    return (n_applied, n_skipped)


def main(argv=None):
    p = argparse.ArgumentParser(prog="cag-strip-placeholders", description=__doc__)
    p.add_argument("--root", help="Project root")
    p.add_argument("--apply", action="store_true", help="Actually rewrite files")
    p.add_argument("--only-file", help="Restrict to files containing this string")
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())

    files = sorted((root / "theories").rglob("*.v"))
    if args.only_file:
        files = [f for f in files if args.only_file in str(f)]

    total_applied = 0
    total_skipped = 0
    for f in files:
        applied, skipped = patch_file(f, root, dry_run=not args.apply)
        if applied or skipped:
            rel = f.relative_to(root)
            tag = "applied" if args.apply else "would apply"
            print(f"{rel}: {tag} {applied}, skipped (referenced) {skipped}")
        total_applied += applied
        total_skipped += skipped
    print(f"\n# total: {total_applied} placeholder(s) "
          f"{'removed' if args.apply else 'would be removed'}, "
          f"{total_skipped} skipped (referenced elsewhere)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
