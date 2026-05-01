"""cag-extract: one-command extraction of a Rocq Definition to runnable OCaml.

Usage:
    cag-extract NAME                    # extract NAME, compile to .ml, place in .cag/extract/
    cag-extract NAME --run "args..."    # also build a tiny driver and run it
    cag-extract NAME --output-dir DIR

The tool:
  1. Locates `NAME` in the project via cag-search's index.
  2. Generates a temporary .v file:
        Require Import <module>.
        Require Import Extraction.
        Extraction Language OCaml.
        Extraction "<NAME>.ml" <NAME>.
  3. Runs `rocq compile` on it (with the same -Q theories CAG flags).
  4. Optionally compiles the produced .ml with ocamlfind / ocamlc.

Note: extraction works only for *computable* definitions (no Axioms,
no opaque Qed proofs in dependencies). The tool will fail loudly if
extraction is impossible for a given name.
"""

from __future__ import annotations

import argparse
import os
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


def _find_module(root: Path, name: str) -> str | None:
    for d in walk_theories(root / "theories"):
        if d.name == name:
            try:
                rel = Path(d.file).resolve().relative_to(root / "theories")
            except ValueError:
                return None
            return "CAG." + ".".join(rel.with_suffix("").parts)
    return None


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="cag-extract", description=__doc__)
    p.add_argument("name", help="Definition / Fixpoint to extract")
    p.add_argument("--root", help="Project root")
    p.add_argument("--output-dir", help="Where to put the generated .ml (default: .cag/extract/)")
    p.add_argument("--build", action="store_true", help="Compile the generated .ml with ocamlc")
    p.add_argument("--run", help="Compile + run; argument is the OCaml driver body")
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    name = args.name

    module = _find_module(root, name)
    if module is None:
        print(f"error: no declaration named '{name}' found", file=sys.stderr)
        return 2

    out_dir = (
        Path(args.output_dir) if args.output_dir else (root / ".cag" / "extract")
    )
    out_dir.mkdir(parents=True, exist_ok=True)

    stub = out_dir / f"_extract_{name}.v"
    stub.write_text(
        f"Require Import {module}.\n"
        f"Require Coq.extraction.Extraction.\n"
        f"Extraction Language OCaml.\n"
        f'Cd "{out_dir}".\n'
        f'Extraction "{name}" {name}.\n',
        encoding="utf-8",
    )

    rocq = os.environ.get("ROCQ", "rocq")
    cmd = [rocq, "compile", "-Q", "theories", "CAG", str(stub)]
    print(f"$ {' '.join(cmd)}")
    res = subprocess.run(cmd, cwd=str(root), capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stderr)
        sys.stderr.write(res.stdout)
        return res.returncode

    ml = out_dir / f"{name}.ml"
    if not ml.exists():
        print(f"error: extraction did not produce {ml}", file=sys.stderr)
        return 3
    print(f"extracted: {ml}")
    print(f"           {out_dir / (name + '.mli')}")

    if args.build or args.run:
        if not _have("ocamlfind"):
            print("warn: ocamlfind not found; skipping build", file=sys.stderr)
            return 0
        # Naive build — for projects with stdlib dependencies you'd need
        # additional packages.
        build_cmd = ["ocamlfind", "ocamlc", "-package", "str", "-c", str(ml)]
        print(f"$ {' '.join(build_cmd)}")
        bres = subprocess.run(build_cmd, cwd=str(out_dir), capture_output=True, text=True)
        if bres.returncode != 0:
            sys.stderr.write(bres.stderr)
            return bres.returncode

        if args.run:
            driver = out_dir / f"_run_{name}.ml"
            driver.write_text(
                f'open {name.capitalize()}\n'
                f"let () =\n  {args.run}\n"
            )
            link_cmd = [
                "ocamlfind", "ocamlc", "-package", "str", "-linkpkg",
                f"{name}.cmo", str(driver), "-o", f"_run_{name}",
            ]
            print(f"$ {' '.join(link_cmd)}")
            lres = subprocess.run(link_cmd, cwd=str(out_dir), capture_output=True, text=True)
            if lres.returncode != 0:
                sys.stderr.write(lres.stderr)
                return lres.returncode
            run_cmd = [str(out_dir / f"_run_{name}")]
            print(f"$ {' '.join(run_cmd)}")
            sres = subprocess.run(run_cmd, capture_output=True, text=True)
            sys.stdout.write(sres.stdout)
            if sres.stderr:
                sys.stderr.write(sres.stderr)
            return sres.returncode

    return 0


def _have(prog: str) -> bool:
    try:
        return (
            subprocess.run(
                ["which", prog], capture_output=True, text=True
            ).returncode
            == 0
        )
    except FileNotFoundError:
        return False


if __name__ == "__main__":
    sys.exit(main())
