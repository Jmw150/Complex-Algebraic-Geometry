"""Rocq file parser.

Extracts top-level declarations (Lemma, Theorem, Axiom, Parameter, ...) from
.v files. Not a full Rocq parser — uses regex with comment stripping and a
lightweight statement-end heuristic. Good enough for indexing.

Public API:
    iter_declarations(path: Path) -> Iterator[Declaration]
    walk_theories(root: Path) -> Iterator[Declaration]
"""

from __future__ import annotations

import dataclasses
import re
from pathlib import Path
from typing import Iterator


# Declaration kinds we care about. Order matters for regex (longer first).
KINDS = [
    "Theorem",
    "Lemma",
    "Corollary",
    "Proposition",
    "Fact",
    "Remark",
    "Definition",
    "Fixpoint",
    "CoFixpoint",
    "Axiom",
    "Parameter",
    "Hypothesis",
    "Conjecture",
    "Example",
    "Inductive",
    "CoInductive",
    "Class",
    "Instance",
    "Record",
    "Structure",
    "Variant",
]

# Match kind + name at start of a logical declaration. A declaration can be
# preceded by `Local`, `Global`, `Polymorphic`, `Monomorphic`, `#[...]`, etc.
_PREFIX = r"(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*"
_KIND = r"(?P<kind>" + "|".join(KINDS) + r")"
_NAME = r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
_DECL_RE = re.compile(
    r"^[ \t]*" + _PREFIX + _KIND + r"[ \t\n]+" + _NAME + r"\b",
    re.MULTILINE,
)

# Comment-stripping regex: handles nested (* ... *) comments by repeated pass.
_COMMENT_OUTER = re.compile(r"\(\*[^()]*?\*\)", re.DOTALL)


@dataclasses.dataclass
class Declaration:
    name: str
    kind: str
    statement: str
    file: str  # path relative to project root if known, else absolute
    line: int  # 1-based line number where the declaration begins
    raw: str  # full snippet including the kind+name prefix


def strip_comments(src: str) -> str:
    """Strip Rocq (* ... *) comments. Repeated pass handles nesting."""
    prev = None
    cur = src
    while prev != cur:
        prev = cur
        cur = _COMMENT_OUTER.sub(" ", cur)
    return cur


def _line_of(src: str, offset: int) -> int:
    return src.count("\n", 0, offset) + 1


def _find_statement_end(src: str, start: int) -> int:
    """Return the offset of the end of the statement starting at `start`.

    Heuristic: walk forward until we hit `.` followed by whitespace/EOF,
    while tracking parenthesis/brace/bracket nesting and skipping strings.
    For Definition / Fixpoint, accept `:=` as also ending the *statement*
    portion; we still capture up to the next `.` to include the body.
    Returns offset of the `.` (inclusive).
    """
    depth = 0
    i = start
    n = len(src)
    in_string = False
    while i < n:
        c = src[i]
        if in_string:
            if c == '"':
                # Rocq strings double the quote to escape: ""
                if i + 1 < n and src[i + 1] == '"':
                    i += 2
                    continue
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
            # End of statement: `.` followed by whitespace or EOF or another
            # declaration. Avoid matching `..` (ellipsis in patterns).
            if i + 1 == n or src[i + 1] in " \t\n\r":
                return i
            # Otherwise (e.g. `Module.Foo`), skip
        i += 1
    return n  # ran off end — return whole rest


def iter_declarations(path: Path) -> Iterator[Declaration]:
    """Yield Declaration for each top-level declaration in `path`."""
    src = path.read_text(encoding="utf-8", errors="replace")
    clean = strip_comments(src)

    # Remember mapping clean offset → original offset by aligning newlines.
    # Since comment stripping replaces with space, line numbers are preserved.
    # So we can use clean offsets directly to compute original line numbers.
    rel_file = str(path)

    for m in _DECL_RE.finditer(clean):
        kind = m.group("kind")
        name = m.group("name")
        start = m.start()
        end = _find_statement_end(clean, m.end())
        snippet = clean[start : end + 1]
        # Truncate enormous statements (e.g. very long Records) to keep
        # the index reasonable.
        if len(snippet) > 4000:
            snippet = snippet[:4000] + " (...truncated...)"
        statement = snippet
        line = _line_of(clean, start)
        yield Declaration(
            name=name,
            kind=kind,
            statement=statement,
            file=rel_file,
            line=line,
            raw=snippet,
        )


def walk_theories(root: Path) -> Iterator[Declaration]:
    """Yield Declaration for every .v file under `root` recursively.

    Skips files in build artifact directories (_build, lib, .git).
    """
    skip_parts = {"_build", "lib", ".git"}
    for p in sorted(root.rglob("*.v")):
        if any(part in skip_parts for part in p.parts):
            continue
        try:
            yield from iter_declarations(p)
        except Exception as exc:  # noqa: BLE001
            # Don't let one bad file kill the whole index.
            print(f"WARN: failed to parse {p}: {exc}")
