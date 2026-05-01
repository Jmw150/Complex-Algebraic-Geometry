"""SQLite FTS5 index of project declarations.

Schema:
    decls(id, name, kind, statement, file, line, mtime)
    decls_fts (FTS5) covers name, kind, statement.

Public API:
    open_db(path) -> Connection
    rebuild(conn, project_root)
    search(conn, query, *, kind=None, file_substr=None, limit=20)
"""

from __future__ import annotations

import sqlite3
import time
from pathlib import Path
from typing import Iterable, Iterator, Optional

from cag_lib.rocq_parse import Declaration, walk_theories


SCHEMA = """
CREATE TABLE IF NOT EXISTS decls (
    id        INTEGER PRIMARY KEY,
    name      TEXT NOT NULL,
    kind      TEXT NOT NULL,
    statement TEXT NOT NULL,
    file      TEXT NOT NULL,
    line      INTEGER NOT NULL
);

CREATE VIRTUAL TABLE IF NOT EXISTS decls_fts USING fts5(
    name, kind, statement,
    content='decls', content_rowid='id',
    tokenize='unicode61'
);

-- Triggers to keep FTS index in sync.
CREATE TRIGGER IF NOT EXISTS decls_ai AFTER INSERT ON decls BEGIN
    INSERT INTO decls_fts(rowid, name, kind, statement)
    VALUES (new.id, new.name, new.kind, new.statement);
END;

CREATE TRIGGER IF NOT EXISTS decls_ad AFTER DELETE ON decls BEGIN
    INSERT INTO decls_fts(decls_fts, rowid, name, kind, statement)
    VALUES ('delete', old.id, old.name, old.kind, old.statement);
END;

CREATE INDEX IF NOT EXISTS decls_kind ON decls(kind);
CREATE INDEX IF NOT EXISTS decls_file ON decls(file);
"""


def open_db(path: Path) -> sqlite3.Connection:
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(str(path))
    conn.executescript(SCHEMA)
    return conn


def _insert(conn: sqlite3.Connection, decls: Iterable[Declaration]) -> int:
    rows = (
        (d.name, d.kind, d.statement, d.file, d.line) for d in decls
    )
    cur = conn.executemany(
        "INSERT INTO decls(name, kind, statement, file, line) VALUES (?,?,?,?,?)",
        rows,
    )
    return cur.rowcount


def rebuild(conn: sqlite3.Connection, project_root: Path) -> tuple[int, float]:
    """Drop and rebuild the entire index. Returns (count, seconds)."""
    t0 = time.monotonic()
    with conn:
        conn.execute("DELETE FROM decls")
        conn.execute("INSERT INTO decls_fts(decls_fts) VALUES('rebuild')")
        n = _insert(conn, walk_theories(project_root / "theories"))
    return n, time.monotonic() - t0


def search(
    conn: sqlite3.Connection,
    query: str,
    *,
    kind: Optional[str] = None,
    file_substr: Optional[str] = None,
    limit: int = 20,
) -> Iterator[tuple]:
    """Run a query against the FTS index.

    If `query` is empty, falls back to filtering by kind/file_substr only.
    Yields tuples (rank, name, kind, file, line, statement_first_line).
    """
    args: list = []
    where_clauses: list[str] = []

    if query.strip():
        sql = (
            "SELECT d.id, d.name, d.kind, d.file, d.line, d.statement, "
            "       bm25(decls_fts) AS score "
            "FROM decls d "
            "JOIN decls_fts f ON d.id = f.rowid "
            "WHERE decls_fts MATCH ?"
        )
        args.append(query)
    else:
        sql = (
            "SELECT d.id, d.name, d.kind, d.file, d.line, d.statement, "
            "       0 AS score FROM decls d WHERE 1=1"
        )

    if kind:
        sql += " AND d.kind = ?"
        args.append(kind)
    if file_substr:
        sql += " AND d.file LIKE ?"
        args.append(f"%{file_substr}%")

    if query.strip():
        sql += " ORDER BY score LIMIT ?"
    else:
        sql += " ORDER BY d.file, d.line LIMIT ?"
    args.append(limit)

    for row in conn.execute(sql, args):
        _id, name, kind_, file, line, statement, score = row
        first_line = statement.splitlines()[0] if statement else ""
        yield (score, name, kind_, file, line, first_line)


def stats(conn: sqlite3.Connection) -> dict:
    rows = list(
        conn.execute("SELECT kind, COUNT(*) FROM decls GROUP BY kind ORDER BY 2 DESC")
    )
    total = sum(c for _, c in rows)
    return {"total": total, "by_kind": dict(rows)}
