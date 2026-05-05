"""Comment out zero-dependent assumption declarations with compile checks."""

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


REMOVE_KINDS = {"Axiom", "Parameter", "Admitted"}
PROOF_KINDS = "Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example"


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def _line_starts(src: str) -> list[int]:
    starts = [0]
    for i, ch in enumerate(src):
        if ch == "\n":
            starts.append(i + 1)
    return starts


def _line_of(starts: list[int], offset: int) -> int:
    lo, hi = 0, len(starts)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if starts[mid] <= offset:
            lo = mid
        else:
            hi = mid
    return lo + 1


def _line_start(starts: list[int], line: int) -> int:
    if line <= 1:
        return 0
    if line - 1 < len(starts):
        return starts[line - 1]
    return len(starts)


def _skip_comment(src: str, i: int) -> int:
    depth = 1
    i += 2
    while i < len(src) and depth:
        if src.startswith("(*", i):
            depth += 1
            i += 2
        elif src.startswith("*)", i):
            depth -= 1
            i += 2
        else:
            i += 1
    return i


def _stmt_end(src: str, start: int) -> int:
    depth = 0
    i = start
    in_string = False
    while i < len(src):
        if src.startswith("(*", i) and not in_string:
            i = _skip_comment(src, i)
            continue
        c = src[i]
        if in_string:
            if c == '"':
                if i + 1 < len(src) and src[i + 1] == '"':
                    i += 2
                    continue
                in_string = False
            i += 1
            continue
        if c == '"':
            in_string = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif c == "." and depth == 0:
            if i + 1 == len(src) or src[i + 1] in " \t\r\n":
                return i + 1
        i += 1
    raise ValueError("statement terminator not found")


def _comment_range(src: str, start: int, end: int, item: dict) -> str:
    while end < len(src) and src[end] in " \t":
        end += 1
    if end < len(src) and src[end] == "\n":
        end += 1
    chunk = src[start:end]
    marker = f"CAG zero-dependent {item['kind']} {item['name']} {item['file']}:{item['line']}"
    commented = f"(* {marker} BEGIN\n{chunk}   {marker} END *)\n"
    return src[:start] + commented + src[end:]


def _find_decl_start(src: str, line: int, kind: str, name: str) -> int:
    starts = _line_starts(src)
    if kind in {"Axiom", "Parameter", "Conjecture"}:
        decl_re = re.compile(
            rf"(?m)^[ \t]*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
            rf"{kind}\s+{re.escape(name)}\b"
        )
    else:
        decl_re = re.compile(
            rf"(?m)^[ \t]*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
            rf"(?:{PROOF_KINDS})\s+{re.escape(name)}\b"
        )

    matches = list(decl_re.finditer(src))
    if not matches:
        raise ValueError(f"could not find {kind} {name}")
    target = line
    scored = sorted(
        matches,
        key=lambda m: (
            0 if _line_of(starts, m.start()) <= target else 1,
            abs(_line_of(starts, m.start()) - target),
        ),
    )
    return scored[0].start()


def deletion_span(src: str, item: dict) -> tuple[int, int]:
    kind = item["kind"]
    name = item["name"]
    line = item["line"]
    start = _find_decl_start(src, line, kind, name)
    if kind in {"Axiom", "Parameter", "Conjecture"}:
        return start, _stmt_end(src, start)
    m = re.search(r"\bAdmitted\s*\.", src[start:])
    if m is None:
        raise ValueError(f"could not find Admitted for {name}")
    return start, start + m.end()


def compile_file(root: Path, file: str, log: Path) -> bool:
    target = file[:-2] + ".vo" if file.endswith(".v") else file + ".vo"
    cmd = (
        "eval $(opam env --switch=rocq-9.0 --set-switch) "
        f"&& make -B {target}"
    )
    with log.open("a", encoding="utf-8") as fh:
        fh.write(f"\n\n$ {cmd}\n")
        fh.flush()
        res = subprocess.run(
            ["bash", "-lc", cmd],
            cwd=str(root),
            stdout=fh,
            stderr=subprocess.STDOUT,
            text=True,
        )
        fh.write(f"\n# exit {res.returncode}\n")
    return res.returncode == 0


def load_candidates(root: Path, graph: Path, limit_files: int | None) -> dict[str, list[dict]]:
    data = json.loads(graph.read_text(encoding="utf-8"))
    candidates = [
        a
        for a in data["assumptions"]
        if a["kind"] in REMOVE_KINDS and a["dependent_count"] == 0
    ]
    grouped: dict[str, list[dict]] = defaultdict(list)
    for item in candidates:
        grouped[item["file"]].append(item)
    ordered = dict(sorted(grouped.items()))
    if limit_files is not None:
        ordered = dict(list(ordered.items())[:limit_files])
    return ordered


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="Project root")
    parser.add_argument("--graph", default=".cag/dependency-graph.json")
    parser.add_argument("--log", default=".cag/remove-zero-dependents.log")
    parser.add_argument("--backup-dir", default=".cag/remove-zero-backups")
    parser.add_argument("--limit-files", type=int)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    graph = root / args.graph
    log = root / args.log
    backup_dir = root / args.backup_dir
    backup_dir.mkdir(parents=True, exist_ok=True)
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(f"# remove-zero-dependents {time.strftime('%Y-%m-%dT%H:%M:%S')}\n")

    grouped = load_candidates(root, graph, args.limit_files)
    total = sum(len(v) for v in grouped.values())
    print(f"candidate files: {len(grouped)}")
    print(f"candidate declarations: {total}")
    print("candidate kinds:", dict(Counter(i["kind"] for items in grouped.values() for i in items)))
    if args.dry_run:
        return 0

    commented: list[dict] = []
    restored: list[tuple[str, str]] = []
    for file, items in grouped.items():
        path = root / file
        original = path.read_text(encoding="utf-8", errors="replace")
        backup = backup_dir / (file.replace("/", "__") + ".bak")
        backup.write_text(original, encoding="utf-8")

        src = original
        try:
            spans = []
            for item in items:
                spans.append((*deletion_span(src, item), item))
            for start, end, item in sorted(spans, key=lambda x: x[0], reverse=True):
                src = _comment_range(src, start, end, item)
            path.write_text(src, encoding="utf-8")
        except Exception as exc:  # noqa: BLE001
            path.write_text(original, encoding="utf-8")
            restored.append((file, f"edit failed: {exc}"))
            print(f"RESTORED edit-failed {file}: {exc}")
            continue

        if compile_file(root, file, log):
            commented.extend(items)
            print(f"OK {file}: commented {len(items)}")
        else:
            shutil.copyfile(backup, path)
            restored.append((file, "compile failed"))
            print(f"RESTORED compile-failed {file}")

    summary = {
        "commented": commented,
        "restored": [{"file": f, "reason": r} for f, r in restored],
    }
    (root / ".cag/remove-zero-dependents-summary.json").write_text(
        json.dumps(summary, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"commented declarations: {len(commented)}")
    print(f"restored files: {len(restored)}")
    print(f"log: {log}")
    return 0 if not restored else 1


if __name__ == "__main__":
    sys.exit(main())
