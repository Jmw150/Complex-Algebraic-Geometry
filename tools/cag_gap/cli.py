"""cag-gap: bridge to the GAP computer algebra system.

Subcommands:
    eval     — evaluate a GAP expression and print the result
    run      — run a GAP script file
    q15      — run the bundled Q1.5 candidate-search script

The bundled q15_search.g iterates over GAP's small-groups library looking
for non-conjugate, core-free, Q-coset-equivalent subgroup pairs. Any such
pair is a *candidate* counterexample to KLMRS Question 1.5; Z-coset
equivalence still has to be verified separately on each candidate.

Configuration:
    GAP    (default: /usr/bin/gap)
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent


def _gap() -> str:
    return os.environ.get("GAP", shutil.which("gap") or "/usr/bin/gap")


def _write_tmp_script(body: str) -> Path:
    import tempfile
    fd, name = tempfile.mkstemp(suffix=".g")
    os.close(fd)
    Path(name).write_text(body, encoding="utf-8")
    return Path(name)


def cmd_eval(args) -> int:
    expr = args.expr.rstrip(";").strip()
    script = _write_tmp_script(f'Print({expr}, "\\n");\nQUIT;\n')
    try:
        cmd = [_gap(), "-q", "-b", str(script)]
        res = subprocess.run(cmd, capture_output=True, text=True)
        if res.returncode != 0:
            sys.stderr.write(res.stderr)
            return res.returncode
        sys.stdout.write(res.stdout)
        return 0
    finally:
        script.unlink(missing_ok=True)


def cmd_run(args) -> int:
    cmd = [_gap(), "-q", "-b", str(args.script)]
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stderr)
    sys.stdout.write(res.stdout)
    return res.returncode


def cmd_q15(args) -> int:
    script = HERE / "q15_search.g"
    if not script.exists():
        print(f"error: bundled script not found at {script}", file=sys.stderr)
        return 2
    cmd = [
        _gap(),
        "-q",
        "-b",
        "--norepl",
        "-c",
        f"MIN_ORD := {args.min_order}; MAX_ORD := {args.max_order};",
        str(script),
    ]
    print(f"# scanning small groups of order {args.min_order}..{args.max_order}", file=sys.stderr)
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stderr)
        return res.returncode

    # Parse JSON-shaped lines, count and summarize.
    candidates = []
    for line in res.stdout.splitlines():
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            candidates.append(json.loads(line))
        except json.JSONDecodeError:
            print(f"warn: unparseable line: {line!r}", file=sys.stderr)

    sys.stdout.write(res.stdout)
    print("---", file=sys.stderr)
    print(f"candidates found: {len(candidates)}", file=sys.stderr)
    nonisos = [c for c in candidates if not c["iso"]]
    if nonisos:
        print(f"NON-ISOMORPHIC candidates (potential Q1.5 leads): {len(nonisos)}", file=sys.stderr)
        for c in nonisos:
            print(f"  order {c['order']} id {c['id']}  subgroups {c['i']},{c['j']} (size {c['size']})", file=sys.stderr)
    else:
        print("no non-isomorphic candidate in this range — Q1.5 holds for all small G in scope (assuming Q ⇒ Z screen).", file=sys.stderr)
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="cag-gap", description=__doc__)
    sub = p.add_subparsers(dest="cmd")

    p_eval = sub.add_parser("eval", help="Eval a single GAP expression")
    p_eval.add_argument("expr")

    p_run = sub.add_parser("run", help="Run a GAP script file")
    p_run.add_argument("script", type=Path)

    p_q15 = sub.add_parser("q15", help="Run Q1.5 candidate search")
    p_q15.add_argument("--min-order", type=int, default=1)
    p_q15.add_argument("--max-order", type=int, default=63)

    args = p.parse_args(argv)
    if not args.cmd:
        p.print_help()
        return 0

    if not Path(_gap()).exists():
        print(f"error: GAP not found at {_gap()}; install with apt or set GAP=...", file=sys.stderr)
        return 2

    return {"eval": cmd_eval, "run": cmd_run, "q15": cmd_q15}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
