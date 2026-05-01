"""Batch-probe every Axiom with CoqHammer / sauto.

For each Axiom in the project:
  1. Extract its statement type (everything after `Axiom name :` up to the final `.`).
  2. Generate a probe file
       From Hammer Require Import Hammer Tactics.
       Require Import <module>.
       Goal <type>. <tactic>. Qed.
  3. Run `rocq compile` with a wall-clock timeout.
  4. Record the result.

Output: JSON to .cag/hammer_probe_report.json.
Stdout: streaming progress (one line per axiom).

Usage:
  python -m cag_audit.hammer_probe                 # try sauto on all axioms
  python -m cag_audit.hammer_probe --tactic hammer
  python -m cag_audit.hammer_probe --timeout 8 --limit 100
  python -m cag_audit.hammer_probe --only-file FiniteLifts
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Iterable

from cag_lib.rocq_parse import Declaration, walk_theories


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


# Regex: pull `<type>` out of `Axiom name : <type>.` (with possible
# `Axiom` prefixed by `Local`, `Polymorphic`, etc.)
_AXIOM_PREFIX = re.compile(
    r"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
    r"(?:Axiom|Parameter|Conjecture)\s+\w+\s*",
    re.MULTILINE,
)


def extract_type(statement: str) -> str | None:
    """Extract the axiom's body (the type) from its full Axiom declaration."""
    m = _AXIOM_PREFIX.match(statement)
    if not m:
        return None
    rest = statement[m.end():].lstrip()
    # rest should start with `:`
    if not rest.startswith(":"):
        return None
    rest = rest[1:].strip()
    # Strip the final `.` that terminates the declaration.
    rest = rest.rstrip()
    if rest.endswith("."):
        rest = rest[:-1].rstrip()
    # If it ends with `(...truncated...)` from the parser, skip.
    if rest.endswith("(...truncated...)"):
        return None
    return rest


def file_to_module(file: str, root: Path) -> str:
    rel = Path(file).resolve().relative_to(root / "theories")
    parts = list(rel.with_suffix("").parts)
    return "CAG." + ".".join(parts)


def make_probe(out_dir: Path, axiom: Declaration, root: Path,
               tactic: str, atp_limit: int) -> Path | None:
    typ = extract_type(axiom.statement)
    if typ is None:
        return None
    module = file_to_module(axiom.file, root)
    probe = out_dir / f"_probe_{axiom.name}.v"
    probe.write_text(
        f"From Hammer Require Import Hammer Tactics.\n"
        f"Require Import {module}.\n"
        f"Set Hammer ATPLimit {atp_limit}.\n"
        f"Goal {typ}.\n"
        f"Proof. {tactic}. Qed.\n",
        encoding="utf-8",
    )
    return probe


def run_probe(root: Path, probe: Path, wall_timeout: int) -> tuple[bool, float, str]:
    """Returns (closed, secs, last_stderr_line)."""
    cmd = ["rocq", "compile", "-Q", "theories", "CAG", str(probe)]
    t0 = time.monotonic()
    try:
        res = subprocess.run(
            cmd, cwd=str(root),
            capture_output=True, text=True, timeout=wall_timeout,
        )
        dt = time.monotonic() - t0
        if res.returncode == 0:
            return True, dt, ""
        last = (res.stderr.strip().splitlines() or
                res.stdout.strip().splitlines() or [""])[-1]
        return False, dt, last[:200]
    except subprocess.TimeoutExpired:
        return False, wall_timeout, "TIMEOUT"


_ASSUMPTION_KINDS = {"Axiom", "Parameter", "Conjecture"}


def _attempt_key(name: str, file: str, statement: str) -> str:
    """Stable key for the attempted-set: name + relative file + statement-hash.

    The statement-hash ensures that if a declaration is renamed or
    re-stated, it gets re-probed.
    """
    import hashlib
    h = hashlib.sha256(statement.encode("utf-8")).hexdigest()[:12]
    return f"{name}::{file}::{h}"


def load_attempted_set(path: Path) -> set[str]:
    if not path.exists():
        return set()
    return set(path.read_text(encoding="utf-8").splitlines())


def write_attempted_set(path: Path, keys: Iterable[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(sorted(keys)) + "\n", encoding="utf-8")


def collect_axioms(root: Path, only_file: str | None) -> list[Declaration]:
    out = []
    for d in walk_theories(root / "theories"):
        if d.kind not in _ASSUMPTION_KINDS:
            continue
        if only_file and only_file not in d.file:
            continue
        out.append(d)
    return out


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="cag-hammer-probe", description=__doc__)
    p.add_argument("--tactic", default="sauto",
                   help="Reconstruction tactic to try (sauto, hammer, hauto, qauto)")
    p.add_argument("--atp-limit", type=int, default=10,
                   help="Per-ATP limit (Set Hammer ATPLimit). Only matters for hammer.")
    p.add_argument("--timeout", type=int, default=15,
                   help="Wall-clock timeout per probe (seconds)")
    p.add_argument("--limit", type=int, default=None,
                   help="Only try the first N axioms")
    p.add_argument("--only-file", help="Restrict to axioms whose file path contains this string")
    p.add_argument("--root", help="Project root")
    p.add_argument("--report", help="Output JSON path (default: .cag/hammer_probe_report.json)")
    p.add_argument("--keep-probes", action="store_true",
                   help="Don't delete probe files after running")
    p.add_argument("--skip-attempted", action="store_true",
                   help="Skip assumptions present in --attempted-file (probed before, not closed)")
    p.add_argument("--attempted-file",
                   help="Path to attempted-set file (default: .cag/hammer_attempted.txt). "
                        "Read with --skip-attempted; updated after the run with new failures.")
    args = p.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    out_dir = root / ".cag" / "probes"
    out_dir.mkdir(parents=True, exist_ok=True)

    attempted_path = (
        Path(args.attempted_file) if args.attempted_file
        else root / ".cag" / "hammer_attempted.txt"
    )
    attempted_keys = load_attempted_set(attempted_path)

    all_axioms = collect_axioms(root, args.only_file)
    if args.skip_attempted and attempted_keys:
        before = len(all_axioms)
        axioms = [a for a in all_axioms
                  if _attempt_key(a.name, str(Path(a.file).resolve().relative_to(root)),
                                  a.statement) not in attempted_keys]
        print(f"# skip-attempted: {before - len(axioms)} of {before} skipped "
              f"(in {attempted_path.name})", flush=True)
    else:
        axioms = all_axioms
    if args.limit:
        axioms = axioms[: args.limit]

    report_path = (
        Path(args.report) if args.report else (root / ".cag" / "hammer_probe_report.json")
    )
    report = {
        "tactic": args.tactic,
        "timeout": args.timeout,
        "atp_limit": args.atp_limit,
        "started": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "results": [],
    }

    closed = 0
    skipped = 0
    print(f"# probing {len(axioms)} axioms with `{args.tactic}` (timeout {args.timeout}s)")
    sys.stdout.flush()

    for i, ax in enumerate(axioms, 1):
        rel = str(Path(ax.file).resolve().relative_to(root))
        probe = make_probe(out_dir, ax, root, args.tactic, args.atp_limit)
        if probe is None:
            skipped += 1
            print(f"[{i}/{len(axioms)}] {ax.name:<40s} SKIP (unparseable type)")
            sys.stdout.flush()
            report["results"].append({
                "name": ax.name, "file": rel, "line": ax.line,
                "status": "skipped",
            })
            continue
        ok, dt, msg = run_probe(root, probe, args.timeout)
        status = "closed" if ok else ("timeout" if msg == "TIMEOUT" else "failed")
        if ok:
            closed += 1
            print(f"[{i}/{len(axioms)}] {ax.name:<40s} ✓ {dt:5.1f}s")
        else:
            print(f"[{i}/{len(axioms)}] {ax.name:<40s} {status} ({dt:4.1f}s)")
        sys.stdout.flush()
        report["results"].append({
            "name": ax.name, "file": rel, "line": ax.line,
            "status": status, "secs": round(dt, 2),
            "msg": msg if not ok else "",
        })
        if not args.keep_probes:
            probe.unlink(missing_ok=True)

        # Save partial report periodically.
        if i % 10 == 0:
            report_path.write_text(json.dumps(report, indent=2))

    report["finished"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    report["total"] = len(axioms)
    report["closed"] = closed
    report["skipped"] = skipped
    report_path.write_text(json.dumps(report, indent=2))

    # Update the attempted-set: union the prior set with new failures/timeouts,
    # remove any keys that have been newly closed (so a later code change
    # doesn't keep them excluded forever).
    new_attempted = set(attempted_keys)
    statement_by_name = {ax.name: ax.statement for ax in axioms}
    for r in report["results"]:
        key = _attempt_key(
            r["name"], r["file"],
            statement_by_name.get(r["name"], "")
        )
        if r["status"] in ("failed", "timeout"):
            new_attempted.add(key)
        elif r["status"] == "closed":
            new_attempted.discard(key)
    write_attempted_set(attempted_path, new_attempted)

    print(f"\n# done: {closed}/{len(axioms)} closed ({skipped} skipped)")
    print(f"# attempted-set: {len(new_attempted)} keys at {attempted_path}")
    print(f"# report: {report_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
