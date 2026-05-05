"""Build a declaration dependency graph from Rocq .glob files.

The graph is conservative and project-local: each edge means one compiled
project declaration references another project declaration according to the
.glob metadata emitted by Rocq. It is meant for audit and cleanup triage, not
for editing source files.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import re
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

from cag_audit.label_assumptions import collect_sites
from cag_lib.rocq_parse import walk_theories


DECL_GLOB_KINDS = {
    "ax": "Axiom",
    "prf": "Proof",
    "def": "Definition",
    "ind": "Inductive",
    "rec": "Record",
    "proj": "Projection",
    "class": "Class",
    "inst": "Instance",
}

GLOB_DECL_RE = re.compile(
    r"^(?P<tag>[A-Za-z_][A-Za-z0-9_]*)\s+"
    r"(?P<start>\d+):(?P<end>\d+)\s+<> (?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
GLOB_REF_RE = re.compile(
    r"^R(?P<start>\d+):(?P<end>\d+)\s+"
    r"(?P<module>\S+)\s+<> (?P<name>[A-Za-z_][A-Za-z0-9_']*)\s+(?P<tag>\S+)"
)
GLOB_MODULE_RE = re.compile(r"^F(?P<module>\S+)\s*$")


@dataclasses.dataclass(frozen=True)
class Node:
    key: str
    name: str
    kind: str
    file: str
    line: int
    module: str


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def _rel(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root))
    except ValueError:
        return str(path)


def file_to_module(file: str) -> str:
    p = Path(file)
    if p.parts and p.parts[0] == "theories":
        p = Path(*p.parts[1:])
    return "CAG." + ".".join(p.with_suffix("").parts)


def project_vfiles(root: Path) -> set[str]:
    project = root / "_CoqProject"
    out: set[str] = set()
    if not project.exists():
        return out
    for raw in project.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or line.startswith("-"):
            continue
        if line.endswith(".v"):
            out.add(line)
    return out


def glob_to_file(glob: Path, root: Path) -> str:
    rel = glob.resolve().relative_to(root)
    return str(rel.with_suffix(".v"))


def _line_offsets(src: str) -> list[int]:
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


def collect_nodes(root: Path, allowed_files: set[str] | None = None) -> dict[str, Node]:
    allowed_files = allowed_files or set()
    nodes: dict[str, Node] = {}
    for d in walk_theories(root / "theories"):
        file = _rel(Path(d.file), root)
        if allowed_files and file not in allowed_files:
            continue
        module = file_to_module(file)
        key = f"{module}.{d.name}"
        nodes[key] = Node(
            key=key,
            name=d.name,
            kind=d.kind,
            file=file,
            line=d.line,
            module=module,
        )
    return nodes


def parse_glob_edges(
    root: Path,
    nodes: dict[str, Node],
    allowed_files: set[str] | None = None,
) -> set[tuple[str, str]]:
    allowed_files = allowed_files or set()
    edges: set[tuple[str, str]] = set()
    name_index: dict[tuple[str, str], str] = {
        (n.module, n.name): key for key, n in nodes.items()
    }

    for glob in sorted((root / "theories").rglob("*.glob")):
        if any(part in {"_build", "lib", ".git"} for part in glob.parts):
            continue
        rel_file = glob_to_file(glob, root)
        if allowed_files and rel_file not in allowed_files:
            continue
        module = file_to_module(rel_file)
        current: str | None = None

        for line in glob.read_text(encoding="utf-8", errors="replace").splitlines():
            m_module = GLOB_MODULE_RE.match(line)
            if m_module:
                module = m_module.group("module")
                continue

            m_decl = GLOB_DECL_RE.match(line)
            if m_decl and m_decl.group("tag") in DECL_GLOB_KINDS:
                name = m_decl.group("name")
                current = name_index.get((module, name), f"{module}.{name}")
                continue

            m_ref = GLOB_REF_RE.match(line)
            if not m_ref or current is None:
                continue
            ref_module = m_ref.group("module")
            ref_name = m_ref.group("name")
            if not ref_module.startswith("CAG."):
                continue
            target = name_index.get((ref_module, ref_name))
            if target is None:
                continue
            if target != current:
                edges.add((current, target))
    return edges


def assumption_keys(root: Path, allowed_files: set[str] | None = None) -> dict[str, dict]:
    allowed_files = allowed_files or set()
    sites = collect_sites(root)
    out = {}
    for s in sites:
        if s.kind == "admit_tactic":
            continue
        if allowed_files and s.file not in allowed_files:
            continue
        module = file_to_module(s.file)
        key = f"{module}.{s.name}"
        out[key] = dataclasses.asdict(s)
        out[key]["key"] = key
    return out


def write_json(root: Path, nodes: dict[str, Node], edges: set[tuple[str, str]],
               assumptions: dict[str, dict], out: Path) -> None:
    dependents: dict[str, list[str]] = defaultdict(list)
    dependencies: dict[str, list[str]] = defaultdict(list)
    for src, dst in edges:
        dependents[dst].append(src)
        dependencies[src].append(dst)

    payload = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "nodes": [dataclasses.asdict(n) for n in nodes.values()],
        "edges": [{"from": src, "to": dst} for src, dst in sorted(edges)],
        "assumptions": [
            {
                **site,
                "dependent_count": len(set(dependents.get(key, []))),
                "dependency_count": len(set(dependencies.get(key, []))),
                "dependents": sorted(set(dependents.get(key, []))),
                "dependencies": sorted(set(dependencies.get(key, []))),
            }
            for key, site in sorted(assumptions.items())
        ],
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _node_site(nodes: dict[str, Node], key: str) -> str:
    n = nodes.get(key)
    if n is None:
        return key
    return f"{n.file}:{n.line}"


def write_markdown(root: Path, nodes: dict[str, Node], edges: set[tuple[str, str]],
                   assumptions: dict[str, dict], out: Path) -> None:
    dependents: dict[str, set[str]] = defaultdict(set)
    dependencies: dict[str, set[str]] = defaultdict(set)
    for src, dst in edges:
        dependents[dst].add(src)
        dependencies[src].add(dst)

    enriched = []
    for key, site in assumptions.items():
        enriched.append(
            {
                **site,
                "dependent_count": len(dependents.get(key, set())),
                "dependency_count": len(dependencies.get(key, set())),
            }
        )
    zero = [x for x in enriched if x["dependent_count"] == 0]
    zero_by_kind = Counter(x["kind"] for x in zero)
    zero_by_label = Counter(x["label"] for x in zero)
    all_by_kind = Counter(x["kind"] for x in enriched)
    all_by_label = Counter(x["label"] for x in enriched)

    lines = [
        "# CAG Assumption Dependency Report",
        "",
        "Generated from current `_CoqProject` files and compiled `.glob` metadata",
        "by `tools/bin/cag-audit deps`.",
        "This report does not edit source files.",
        "",
        "## Summary",
        "",
        f"- Project declaration nodes: {len(nodes)}",
        f"- Project-local dependency edges: {len(edges)}",
        f"- Assumption declarations tracked: {len(enriched)}",
        f"- Assumption declarations with zero compiled project dependents: {len(zero)}",
        "",
        "## Zero-Dependent Assumptions By Kind",
        "",
    ]
    for kind, count in zero_by_kind.most_common():
        lines.append(f"- `{kind}`: {count} of {all_by_kind[kind]}")

    lines.extend(["", "## Zero-Dependent Assumptions By Label", ""])
    for label, count in zero_by_label.most_common():
        lines.append(f"- `{label}`: {count} of {all_by_label[label]}")

    lines.extend(
        [
            "",
            "## Cleanup Candidates",
            "",
            "These have zero compiled project dependents. Commenting them out still needs",
            "a compile check because parsing/notation side effects are not represented as",
            "ordinary declaration edges.",
            "",
            "| Kind | Label | Site | Name | Dependencies |",
            "| --- | --- | --- | --- | ---: |",
        ]
    )
    for x in sorted(zero, key=lambda y: (y["file"], y["line"], y["kind"], y["name"])):
        lines.append(
            f"| `{x['kind']}` | `{x['label']}` | `{x['file']}:{x['line']}` | "
            f"`{x['name']}` | {x['dependency_count']} |"
        )

    lines.extend(
        [
            "",
            "## Highest Fan-In Assumptions",
            "",
            "| Dependents | Kind | Label | Site | Name |",
            "| ---: | --- | --- | --- | --- |",
        ]
    )
    for x in sorted(enriched, key=lambda y: (-y["dependent_count"], y["file"], y["line"]))[:80]:
        lines.append(
            f"| {x['dependent_count']} | `{x['kind']}` | `{x['label']}` | "
            f"`{x['file']}:{x['line']}` | `{x['name']}` |"
        )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_dot(root: Path, nodes: dict[str, Node], edges: set[tuple[str, str]],
              assumptions: dict[str, dict], out: Path) -> None:
    dependents: dict[str, set[str]] = defaultdict(set)
    for src, dst in edges:
        if dst in assumptions:
            dependents[dst].add(src)

    shown_nodes = set(assumptions)
    for ds in dependents.values():
        shown_nodes.update(ds)

    lines = ["digraph cag_assumption_dependencies {", "  rankdir=LR;"]
    for key in sorted(shown_nodes):
        n = nodes.get(key)
        label = n.name if n else key.rsplit(".", 1)[-1]
        if key in assumptions:
            shape = "box"
            color = "red" if len(dependents.get(key, set())) == 0 else "black"
        else:
            shape = "ellipse"
            color = "gray40"
        lines.append(
            f'  "{key}" [label="{label}", shape={shape}, color="{color}"];'
        )
    for src, dst in sorted(edges):
        if dst in assumptions:
            lines.append(f'  "{src}" -> "{dst}";')
    lines.append("}")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="Project root")
    parser.add_argument("--json", default=".cag/dependency-graph.json")
    parser.add_argument("--markdown", default=".cag/ASSUMPTION_DEPENDENCIES.md")
    parser.add_argument("--dot", default=".cag/assumption-dependencies.dot")
    args = parser.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    allowed_files = project_vfiles(root)
    nodes = collect_nodes(root, allowed_files)
    edges = parse_glob_edges(root, nodes, allowed_files)
    assumptions = assumption_keys(root, allowed_files)

    write_json(root, nodes, edges, assumptions, root / args.json)
    write_markdown(root, nodes, edges, assumptions, root / args.markdown)
    write_dot(root, nodes, edges, assumptions, root / args.dot)

    dependents: dict[str, set[str]] = defaultdict(set)
    for src, dst in edges:
        dependents[dst].add(src)
    zero = [k for k in assumptions if len(dependents.get(k, set())) == 0]
    print(f"nodes: {len(nodes)}")
    print(f"edges: {len(edges)}")
    print(f"assumptions: {len(assumptions)}")
    print(f"zero-dependent assumptions: {len(zero)}")
    print(f"markdown: {root / args.markdown}")
    print(f"json: {root / args.json}")
    print(f"dot: {root / args.dot}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
