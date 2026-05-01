"""Remove truly dead Axioms (no references anywhere except their own declaration).

Replaces each
    Axiom NAME : <type>.
with a one-line comment recording the removal. Same shape as
[strip_placeholders.py] but for Axioms.

Default mode: dry-run, prints unified diff.
Pass --apply to actually rewrite files.

Usage:
  python -m cag_audit.strip_dead                # dry run
  python -m cag_audit.strip_dead --apply
  python -m cag_audit.strip_dead --only-file Vanishing
"""

from __future__ import annotations

import argparse
import difflib
import re
import subprocess
import sys
from pathlib import Path

from cag_lib.rocq_parse import iter_declarations


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def name_uses_outside_decl(name: str, file: Path, decl_line: int,
                           src_root: Path) -> int:
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
            continue
        count += 1
    return count


_KIND_RE = (
    r"(?:Axiom|Parameter|Theorem|Lemma|Corollary|Proposition|Fact|Remark|"
    r"Definition|Fixpoint|CoFixpoint|Hypothesis|Conjecture|Example|"
    r"Inductive|CoInductive|Class|Instance|Record|Structure|Variant)"
)


def find_decl_block(src: str, name: str) -> tuple[int, int] | None:
    """Find the byte span of `<KIND> NAME ...` plus its proof block (if any).

    For Axiom/Parameter this is `<head> ... .`.
    For Theorem/Lemma/etc with a proof, this extends through `Qed.`/`Defined.`/`Admitted.`.
    For Definition foo := body. this stops at the first balanced `.`.
    """
    pat = re.compile(
        r"^(?P<head>\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
        + _KIND_RE + r"\s+" + re.escape(name) + r"\s*[:\s({])",
        re.MULTILINE,
    )
    m = pat.search(src)
    if not m:
        return None
    start = m.start()
    # First find the end of the declaration's *type* (the first balanced `.`).
    n = len(src)
    i = m.end()
    depth = 0
    in_string = False
    decl_end = None
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
        elif c == "." and depth == 0:
            if i + 1 == n or src[i + 1] in " \t\n\r":
                decl_end = i + 1
                break
        i += 1
    if decl_end is None:
        return None
    # Look ahead for an attached proof block. Skip whitespace/comments.
    j = decl_end
    while j < n and src[j] in " \t\r\n":
        j += 1
    # Scan past `(* ... *)` comments.
    while j < n and src[j:j + 2] == "(*":
        depth_c = 1
        j += 2
        while j < n and depth_c > 0:
            if src[j:j + 2] == "(*":
                depth_c += 1
                j += 2
            elif src[j:j + 2] == "*)":
                depth_c -= 1
                j += 2
            else:
                j += 1
        while j < n and src[j] in " \t\r\n":
            j += 1
    # If the next token is "Proof", scan to Qed/Defined/Admitted/Abort.
    if src[j:j + 5] == "Proof":
        i = j
        while i < n:
            for kw in ("Qed.", "Defined.", "Admitted.", "Abort."):
                if src[i:i + len(kw)] == kw:
                    return (start, i + len(kw))
            i += 1
        return (start, n)
    return (start, decl_end)


# Backwards-compat alias for callers.
find_axiom_block = find_decl_block


def patch_file(file: Path, src_root: Path, dry_run: bool, kinds: tuple[str, ...] = ("Axiom",)) -> tuple[int, int]:
    src = file.read_text(encoding="utf-8")
    decls = [
        d for d in iter_declarations(file)
        if d.kind in kinds
    ]
    targets = []
    for d in decls:
        if name_uses_outside_decl(d.name, file, d.line, src_root) == 0:
            targets.append(d)
    if not targets:
        return (0, 0)

    new_src = src
    n_applied = 0
    n_skipped = 0
    for d in sorted(targets, key=lambda x: -x.line):
        block = find_axiom_block(new_src, d.name)
        if block is None:
            n_skipped += 1
            continue
        start, end = block
        comment = (
            f"(* Removed dead {d.kind} `{d.name}` on 2026-04-30 cleanup pass; "
            f"no references anywhere in the codebase. *)"
        )
        new_src = new_src[:start] + comment + new_src[end:]
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


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="cag-strip-dead", description=__doc__)
    p.add_argument("--root", help="Project root")
    p.add_argument("--apply", action="store_true")
    p.add_argument("--only-file", help="Restrict by file path substring")
    p.add_argument("--kinds", nargs="+", default=["Axiom"],
                   help="Kinds to strip (default: Axiom; pass also Parameter)")
    args = p.parse_args(argv)
    root = Path(args.root) if args.root else _detect_root(Path.cwd())

    files = sorted((root / "theories").rglob("*.v"))
    if args.only_file:
        files = [f for f in files if args.only_file in str(f)]

    kinds = tuple(k.capitalize() for k in args.kinds)
    total_applied = 0
    total_skipped = 0
    for f in files:
        applied, skipped = patch_file(f, root, dry_run=not args.apply, kinds=kinds)
        if applied or skipped:
            rel = f.relative_to(root)
            tag = "applied" if args.apply else "would apply"
            print(f"{rel}: {tag} {applied}, skipped {skipped}")
        total_applied += applied
        total_skipped += skipped
    print(f"\n# total: {total_applied} dead Axiom(s) "
          f"{'removed' if args.apply else 'would be removed'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
