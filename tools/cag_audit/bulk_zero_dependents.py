"""Bulk-comment zero-dependent assumptions, then use full builds to restore failures."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

from cag_audit.remove_zero_dependents import REMOVE_KINDS, _comment_range, deletion_span


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def load_candidates(graph: Path, include_conjectures: bool) -> list[dict]:
    data = json.loads(graph.read_text(encoding="utf-8"))
    kinds = set(REMOVE_KINDS)
    if include_conjectures:
        kinds.add("Conjecture")
    return [
        a
        for a in data["assumptions"]
        if a["kind"] in kinds and a["dependent_count"] == 0
    ]


def comment_bulk(root: Path, candidates: list[dict], backup_dir: Path) -> tuple[list[dict], list[dict]]:
    grouped: dict[str, list[dict]] = defaultdict(list)
    for item in candidates:
        grouped[item["file"]].append(item)

    commented: list[dict] = []
    skipped: list[dict] = []
    backup_dir.mkdir(parents=True, exist_ok=True)

    for file, items in sorted(grouped.items()):
        path = root / file
        if not path.exists():
            skipped.extend({**i, "skip_reason": "file missing"} for i in items)
            continue
        original = path.read_text(encoding="utf-8", errors="replace")
        backup = backup_dir / (file.replace("/", "__") + ".bak")
        if not backup.exists():
            backup.write_text(original, encoding="utf-8")

        src = original
        spans = []
        for item in items:
            try:
                start, end = deletion_span(src, item)
                spans.append((start, end, item))
            except Exception as exc:  # noqa: BLE001
                skipped.append({**item, "skip_reason": str(exc)})
        for start, end, item in sorted(spans, key=lambda x: x[0], reverse=True):
            src = _comment_range(src, start, end, item)
            commented.append(item)
        if src != original:
            path.write_text(src, encoding="utf-8")
    return commented, skipped


ERROR_FILE_RE = re.compile(r'File "\./(?P<file>[^"]+\.v)", line \d+')


def full_compile(root: Path, log: Path, iteration: int) -> tuple[bool, str | None]:
    cmd = "eval $(opam env --switch=rocq-9.0 --set-switch) && make -j2"
    with log.open("a", encoding="utf-8") as fh:
        fh.write(f"\n\n# bulk full compile iteration {iteration} {time.strftime('%Y-%m-%dT%H:%M:%S')}\n")
        fh.write(f"$ {cmd}\n")
        fh.flush()
        res = subprocess.run(
            ["bash", "-lc", cmd],
            cwd=str(root),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        fh.write(res.stdout)
        fh.write(f"\n# exit {res.returncode}\n")
    if res.returncode == 0:
        return True, None

    matches = ERROR_FILE_RE.findall(res.stdout)
    if matches:
        return False, matches[-1]
    return False, None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="Project root")
    parser.add_argument("--graph", default=".cag/dependency-graph.json")
    parser.add_argument("--backup-dir", default=".cag/bulk-zero-backups")
    parser.add_argument("--log", default=".cag/bulk-zero-compile.log")
    parser.add_argument("--summary", default=".cag/bulk-zero-summary.json")
    parser.add_argument("--max-restores", type=int, default=40)
    parser.add_argument("--include-conjectures", action="store_true")
    args = parser.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    candidates = load_candidates(root / args.graph, args.include_conjectures)
    commented, skipped = comment_bulk(root, candidates, root / args.backup_dir)

    print(f"bulk candidates: {len(candidates)}")
    print(f"newly commented: {len(commented)} {dict(Counter(i['kind'] for i in commented))}")
    print(f"skipped/already absent: {len(skipped)}")

    restored: list[str] = []
    log = root / args.log
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(f"# bulk-zero compile log {time.strftime('%Y-%m-%dT%H:%M:%S')}\n")

    for iteration in range(1, args.max_restores + 2):
        ok, failed_file = full_compile(root, log, iteration)
        if ok:
            break
        if failed_file is None:
            summary = {
                "commented": commented,
                "skipped": skipped,
                "restored_files": restored,
                "unparsed_failure": True,
            }
            (root / args.summary).write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
            print("full compile failed; could not parse failing file")
            print(f"log: {log}")
            return 1
        backup = root / args.backup_dir / (failed_file.replace("/", "__") + ".bak")
        if not backup.exists():
            print(f"full compile failed in {failed_file}, but no backup exists")
            print(f"log: {log}")
            return 1
        shutil.copyfile(backup, root / failed_file)
        restored.append(failed_file)
        print(f"RESTORED {failed_file}; retrying full compile")
    else:
        print("restore limit exceeded")
        return 1

    summary = {
        "commented": commented,
        "skipped": skipped,
        "restored_files": restored,
    }
    (root / args.summary).write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"full compile succeeded")
    print(f"restored files: {len(restored)}")
    print(f"log: {log}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
