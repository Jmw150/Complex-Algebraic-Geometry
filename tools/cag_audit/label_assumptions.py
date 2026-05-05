"""Label assumption-like sites in the CAG Rocq sources.

The labels are intentionally an audit overlay. This module does not edit Rocq
sources or remove any declarations.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import re
import sys
import time
from collections import Counter
from pathlib import Path

from cag_lib.rocq_parse import Declaration, iter_declarations, strip_comments, walk_theories


ASSUMPTION_KINDS = {"Axiom", "Parameter", "Conjecture"}
PROOF_KINDS = {"Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark", "Example"}

DEEP_KEYWORDS = {
    "abel", "adjunction", "artin", "beilinson", "bernstein", "bertini",
    "bezout", "borel", "chow", "decomposition", "dolbeault", "elliptic",
    "finite_dim", "finiteness", "galois", "garding", "green", "hard_lefschetz",
    "hilbert", "hodge", "hodge_riemann", "hitchin", "kahler", "kodaira",
    "langlands", "lef_schetz", "lefschetz", "nakano", "nilpotent",
    "poincare", "proper", "residue", "riemann", "riesz", "spectral",
    "sylow", "vanishing", "weyl",
}

STRUCTURAL_KEYWORDS = {
    "assoc", "comm", "compatible", "distrib", "functorial", "homomorphism",
    "identity", "inverse", "isomorphism", "linear", "map", "monoid",
    "morphism", "mul", "operation", "ring", "semigroup", "tensor", "unit",
    "well_defined",
}

PLACEHOLDER_PATTERNS = [
    re.compile(r":\s*True\s*\.", re.DOTALL),
    re.compile(r"\bTrue\b"),
    re.compile(r"\bexists\s+\w+\s*,\s*\w+\s*=\s*\w+\s*\.?$", re.DOTALL),
    re.compile(r"\bforall\b.*?,\s*\w+\s*=\s*\w+\s*\.?$", re.DOTALL),
]


@dataclasses.dataclass
class AssumptionSite:
    kind: str
    name: str
    file: str
    line: int
    label: str
    reason: str
    snippet: str


def _detect_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "_CoqProject").exists():
            return p
        p = p.parent
    raise SystemExit(f"error: no _CoqProject above {start}")


def _rel_file(path: str | Path, root: Path) -> str:
    p = Path(path)
    try:
        return str(p.resolve().relative_to(root))
    except ValueError:
        return str(p)


def _one_line(text: str, limit: int = 140) -> str:
    out = " ".join(text.split())
    return out if len(out) <= limit else out[: limit - 3] + "..."


def _decl_text(d: Declaration) -> str:
    return f"{d.name} {d.statement}".lower().replace("_", " ")


def classify_declaration(d: Declaration) -> tuple[str, str]:
    text = _decl_text(d)
    statement = d.statement

    if d.kind == "Parameter":
        return "INTERFACE_PARAMETER", "opaque interface declaration; not necessarily a proof hole"

    if any(p.search(statement) for p in PLACEHOLDER_PATTERNS):
        return "SCAFFOLD_PLACEHOLDER", "statement has a vacuous or reflexive placeholder shape"

    if any(k.replace("_", " ") in text for k in DEEP_KEYWORDS):
        return "TRUSTED_EXTERNAL", "name or statement matches a standard external theorem/theme"

    if d.kind == "Axiom" and any(k in text for k in STRUCTURAL_KEYWORDS):
        return "STRUCTURAL_AXIOM", "algebraic/interface law that should likely be packaged structurally"

    return "UNKNOWN", "needs manual triage"


def classify_proof_hole(kind: str, name: str, body: str) -> tuple[str, str]:
    text = f"{name} {body}".lower().replace("_", " ")
    if any(p.search(body) for p in PLACEHOLDER_PATTERNS):
        return "SCAFFOLD_PLACEHOLDER", "admitted proof for a placeholder-shaped statement"
    if any(k.replace("_", " ") in text for k in DEEP_KEYWORDS):
        return "TRUSTED_EXTERNAL", "admitted proof names a standard external theorem/theme"
    if kind == "admit_tactic":
        return "LOCAL_PROOF", "explicit admit tactic inside an unfinished proof"
    return "LOCAL_PROOF", "unfinished local proof ending in Admitted"


def _line_of(src: str, offset: int) -> int:
    return src.count("\n", 0, offset) + 1


DECL_RE = re.compile(
    r"^[ \t]*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
    r"(?P<kind>Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b",
    re.MULTILINE,
)


def collect_proof_holes(root: Path) -> list[AssumptionSite]:
    sites: list[AssumptionSite] = []
    for path in sorted((root / "theories").rglob("*.v")):
        if any(part in {"_build", "lib", ".git"} for part in path.parts):
            continue
        clean = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        decls = list(DECL_RE.finditer(clean))
        for i, m in enumerate(decls):
            start = m.start()
            end = decls[i + 1].start() if i + 1 < len(decls) else len(clean)
            body = clean[start:end]
            name = m.group("name")
            rel = _rel_file(path, root)

            admitted_positions = [x.start() for x in re.finditer(r"\bAdmitted\s*\.", body)]
            admit_positions = [
                x.start()
                for x in re.finditer(r"(?<![A-Za-z0-9_'])admit(?![A-Za-z0-9_'])", body)
            ]

            for pos in admitted_positions:
                line = _line_of(clean, start + pos)
                label, reason = classify_proof_hole("Admitted", name, body)
                sites.append(
                    AssumptionSite(
                        kind="Admitted",
                        name=name,
                        file=rel,
                        line=line,
                        label=label,
                        reason=reason,
                        snippet=_one_line(body),
                    )
                )

            for pos in admit_positions:
                line = _line_of(clean, start + pos)
                label, reason = classify_proof_hole("admit_tactic", name, body)
                sites.append(
                    AssumptionSite(
                        kind="admit_tactic",
                        name=name,
                        file=rel,
                        line=line,
                        label=label,
                        reason=reason,
                        snippet=_one_line(body),
                    )
                )
    return sites


def collect_sites(root: Path) -> list[AssumptionSite]:
    sites: list[AssumptionSite] = []
    for d in walk_theories(root / "theories"):
        if d.kind not in ASSUMPTION_KINDS:
            continue
        label, reason = classify_declaration(d)
        sites.append(
            AssumptionSite(
                kind=d.kind,
                name=d.name,
                file=_rel_file(d.file, root),
                line=d.line,
                label=label,
                reason=reason,
                snippet=_one_line(d.statement),
            )
        )
    sites.extend(collect_proof_holes(root))
    return sorted(sites, key=lambda s: (s.file, s.line, s.kind, s.name))


def write_json(root: Path, sites: list[AssumptionSite], out: Path) -> None:
    payload = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "total": len(sites),
        "counts_by_kind": dict(Counter(s.kind for s in sites)),
        "counts_by_label": dict(Counter(s.label for s in sites)),
        "items": [dataclasses.asdict(s) for s in sites],
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def write_markdown(root: Path, sites: list[AssumptionSite], out: Path) -> None:
    by_kind = Counter(s.kind for s in sites)
    by_label = Counter(s.label for s in sites)
    by_file = Counter(s.file for s in sites)

    lines = [
        "# CAG Assumption Labels",
        "",
        "Generated by `tools/bin/cag-audit label`. This is an audit overlay only:",
        "no Rocq source declarations were deleted or rewritten.",
        "",
        "## Summary",
        "",
        f"- Total assumption-like sites: {len(sites)}",
        f"- Strict holes (`Axiom` + `Conjecture` + `Admitted`): "
        f"{by_kind['Axiom'] + by_kind['Conjecture'] + by_kind['Admitted']}",
        f"- Strict holes plus explicit `admit` tactics: "
        f"{by_kind['Axiom'] + by_kind['Conjecture'] + by_kind['Admitted'] + by_kind['admit_tactic']}",
        f"- Interface `Parameter` declarations: {by_kind['Parameter']}",
        "",
        "## Counts By Label",
        "",
    ]
    for label, count in by_label.most_common():
        lines.append(f"- `{label}`: {count}")

    lines.extend(["", "## Counts By Kind", ""])
    for kind, count in by_kind.most_common():
        lines.append(f"- `{kind}`: {count}")

    lines.extend(["", "## Top Files", ""])
    for file, count in by_file.most_common(20):
        lines.append(f"- `{file}`: {count}")

    lines.extend(
        [
            "",
            "## Label Meanings",
            "",
            "- `INTERFACE_PARAMETER`: opaque interface declarations; these are counted separately from proof holes.",
            "- `TRUSTED_EXTERNAL`: deep or standard mathematical facts likely intended as imported library theorems.",
            "- `LOCAL_PROOF`: unfinished proofs that look local to the file/module.",
            "- `SCAFFOLD_PLACEHOLDER`: vacuous or reflexive placeholder-shaped statements.",
            "- `STRUCTURAL_AXIOM`: algebraic or interface laws that probably belong in records/classes.",
            "- `UNKNOWN`: requires manual triage.",
            "",
            "## Detailed Labels",
            "",
            "| Kind | Label | Site | Name | Reason | Snippet |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for s in sites:
        site = f"{s.file}:{s.line}"
        snippet = s.snippet.replace("|", "\\|")
        reason = s.reason.replace("|", "\\|")
        lines.append(f"| `{s.kind}` | `{s.label}` | `{site}` | `{s.name}` | {reason} | `{snippet}` |")

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="Project root")
    parser.add_argument("--json", default=".cag/assumption-labels.json", help="JSON output path")
    parser.add_argument("--markdown", default=".cag/ASSUMPTION_LABELS.md", help="Markdown output path")
    args = parser.parse_args(argv)

    root = Path(args.root) if args.root else _detect_root(Path.cwd())
    sites = collect_sites(root)
    json_out = root / args.json
    md_out = root / args.markdown
    write_json(root, sites, json_out)
    write_markdown(root, sites, md_out)

    by_kind = Counter(s.kind for s in sites)
    by_label = Counter(s.label for s in sites)
    print(f"wrote {len(sites)} labeled sites")
    print(f"markdown: {md_out}")
    print(f"json: {json_out}")
    print("counts by kind:")
    for kind, count in by_kind.most_common():
        print(f"  {kind:14} {count}")
    print("counts by label:")
    for label, count in by_label.most_common():
        print(f"  {label:20} {count}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
