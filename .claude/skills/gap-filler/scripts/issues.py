#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Lightweight, file-system-based issue tracker for the skills pipeline.

A counterpart to repoprover's ``issues/*.yaml``: each concern raised by a
script (``[UNVERIFIED]`` mathlib annotation, notation candidate skipped
because of a scope conflict, an open question for the user) lands as a
single YAML file under ``<references-root>/issues/`` so it survives
across Claude sessions and can be greppable / closeable later.

Subcommands:

- ``add``    Create a new issue YAML. Idempotent on
             ``(kind, slug, concept, candidate)`` — re-adding a matching
             open issue is a no-op so callers can run on every
             invocation without flooding the directory.
- ``list``   Print every issue (default: open only) as JSON.
- ``close``  Move a single issue file or every match for a
             ``--kind`` / ``--slug`` filter into ``issues/closed/``.

Issue file schema (plain key/value YAML; nested mappings unsupported):

    opened: 2026-05-04T10:30:00+00:00
    opened_by: verify_mathlib_refs.mark_unverified
    kind: unverified-mathlib-ref
    slug: araki-1976
    concept: "cyclic vector"
    candidate: "Mathlib.Foo.Bar"
    reason: "lean_verify did not accept any candidate"
    suggested_action: "Re-search or open gap-filler"
    status: open

Usage:

    python3 issues.py add <references-root> --kind <kind> [--slug ...]
                                            [--concept ...] [--candidate ...]
                                            [--reason ...] [--opened-by ...]
                                            [--suggested-action ...]
    python3 issues.py list <references-root> [--kind ...] [--slug ...]
                                             [--include-closed]
    python3 issues.py close <references-root> (--id <basename>
                                               | --kind <kind> [--slug ...])

The script is dependency-free; the YAML it emits is a strict subset that
``parse_issue`` round-trips losslessly.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path


SAFE_FILENAME = re.compile(r"[^A-Za-z0-9._-]+")


def _now_iso() -> str:
    return _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")


def _safe(token: str, fallback: str = "x") -> str:
    """Reduce *token* to filename-safe characters."""
    if not token:
        return fallback
    out = SAFE_FILENAME.sub("-", token).strip("-")
    return out[:50] or fallback


def _yaml_quote(value: str) -> str:
    """Quote *value* if it contains characters YAML would otherwise misread.

    Conservative: any quote, colon, ``#``, leading/trailing whitespace, or
    line break forces double-quoting with the same escape set Python's
    ``json.dumps`` uses (``\\n``, ``\\"``, ``\\\\``).
    """
    if not value:
        return '""'
    needs_quote = (
        any(ch in value for ch in ('"', "'", ":", "#", "\n", "\r"))
        or value != value.strip()
        or value.lower() in {"true", "false", "null", "~"}
    )
    if not needs_quote:
        return value
    escaped = (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
    )
    return f'"{escaped}"'


def _yaml_unquote(raw: str) -> str:
    raw = raw.strip()
    if (raw.startswith('"') and raw.endswith('"')) or (
        raw.startswith("'") and raw.endswith("'")
    ):
        body = raw[1:-1]
        body = (
            body.replace("\\n", "\n")
            .replace("\\r", "\r")
            .replace('\\"', '"')
            .replace("\\\\", "\\")
        )
        return body
    return raw


# Order of fields when writing — keeps issue files visually consistent so
# diffs are reviewable.
FIELD_ORDER: tuple[str, ...] = (
    "opened",
    "opened_by",
    "kind",
    "slug",
    "concept",
    "candidate",
    "reason",
    "suggested_action",
    "status",
    "closed",
    "closed_by",
)


def render_issue(payload: dict) -> str:
    lines: list[str] = []
    seen: set[str] = set()
    for key in FIELD_ORDER:
        if key in payload and payload[key] is not None:
            lines.append(f"{key}: {_yaml_quote(str(payload[key]))}")
            seen.add(key)
    for key, value in payload.items():
        if key in seen or value is None:
            continue
        lines.append(f"{key}: {_yaml_quote(str(value))}")
    return "\n".join(lines) + "\n"


def parse_issue(text: str) -> dict:
    out: dict = {}
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        m = re.match(r"^([A-Za-z_][\w-]*)\s*:\s*(.*)$", line)
        if not m:
            continue
        out[m.group(1)] = _yaml_unquote(m.group(2))
    return out


def issues_dir(references_root: Path, *, closed: bool = False) -> Path:
    base = references_root / "issues"
    return base / "closed" if closed else base


def iter_issue_files(references_root: Path, *, include_closed: bool):
    base = issues_dir(references_root)
    if base.is_dir():
        for entry in sorted(base.iterdir()):
            if entry.is_file() and entry.suffix == ".yaml":
                yield entry
    if include_closed:
        closed_dir = issues_dir(references_root, closed=True)
        if closed_dir.is_dir():
            for entry in sorted(closed_dir.iterdir()):
                if entry.is_file() and entry.suffix == ".yaml":
                    yield entry


def find_open_match(
    references_root: Path,
    *,
    kind: str,
    slug: str | None,
    concept: str | None,
    candidate: str | None,
) -> Path | None:
    """Return the first open issue that matches the dedup key, if any."""
    for path in iter_issue_files(references_root, include_closed=False):
        try:
            payload = parse_issue(path.read_text(encoding="utf-8"))
        except OSError:
            continue
        if payload.get("kind") != kind:
            continue
        if slug is not None and payload.get("slug") != slug:
            continue
        if concept is not None and payload.get("concept") != concept:
            continue
        if candidate is not None and payload.get("candidate") != candidate:
            continue
        return path
    return None


def add_issue(
    references_root: Path,
    *,
    kind: str,
    slug: str | None,
    concept: str | None,
    candidate: str | None,
    reason: str | None,
    suggested_action: str | None,
    opened_by: str | None,
) -> dict:
    base = issues_dir(references_root)
    base.mkdir(parents=True, exist_ok=True)

    existing = find_open_match(
        references_root,
        kind=kind,
        slug=slug,
        concept=concept,
        candidate=candidate,
    )
    if existing is not None:
        return {"action": "skip-duplicate", "path": str(existing)}

    timestamp = _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    name_parts = [timestamp, _safe(kind, fallback="issue")]
    if slug:
        name_parts.append(_safe(slug))
    if concept:
        name_parts.append(_safe(concept))
    filename = "-".join(name_parts) + ".yaml"
    path = base / filename

    payload = {
        "opened": _now_iso(),
        "opened_by": opened_by or "manual",
        "kind": kind,
        "slug": slug or "",
        "concept": concept or "",
        "candidate": candidate or "",
        "reason": reason or "",
        "suggested_action": suggested_action or "",
        "status": "open",
    }
    # Drop empty optional fields so the YAML stays readable.
    payload = {k: v for k, v in payload.items() if v != "" or k in ("status",)}
    path.write_text(render_issue(payload), encoding="utf-8")
    return {"action": "created", "path": str(path)}


def list_issues(
    references_root: Path,
    *,
    include_closed: bool,
    kind: str | None,
    slug: str | None,
) -> list[dict]:
    out: list[dict] = []
    for path in iter_issue_files(references_root, include_closed=include_closed):
        try:
            payload = parse_issue(path.read_text(encoding="utf-8"))
        except OSError:
            continue
        if kind is not None and payload.get("kind") != kind:
            continue
        if slug is not None and payload.get("slug") != slug:
            continue
        payload["_path"] = str(path)
        payload["_id"] = path.name
        out.append(payload)
    return out


def close_issue(
    references_root: Path,
    *,
    issue_id: str | None,
    kind: str | None,
    slug: str | None,
    closed_by: str | None,
) -> dict:
    if issue_id is None and kind is None:
        raise ValueError("close: pass --id or --kind to select what to close")
    closed_dir = issues_dir(references_root, closed=True)
    closed_dir.mkdir(parents=True, exist_ok=True)
    moved: list[str] = []
    base = issues_dir(references_root)
    if not base.is_dir():
        return {"closed": [], "count": 0}
    for path in sorted(base.iterdir()):
        if not (path.is_file() and path.suffix == ".yaml"):
            continue
        if issue_id is not None and path.name != issue_id:
            continue
        payload = parse_issue(path.read_text(encoding="utf-8"))
        if kind is not None and payload.get("kind") != kind:
            continue
        if slug is not None and payload.get("slug") != slug:
            continue
        payload["status"] = "closed"
        payload["closed"] = _now_iso()
        if closed_by:
            payload["closed_by"] = closed_by
        target = closed_dir / path.name
        target.write_text(render_issue(payload), encoding="utf-8")
        path.unlink()
        moved.append(path.name)
    return {"closed": moved, "count": len(moved)}


def count_open(references_root: Path) -> int:
    base = issues_dir(references_root)
    if not base.is_dir():
        return 0
    return sum(
        1 for entry in base.iterdir() if entry.is_file() and entry.suffix == ".yaml"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_add = sub.add_parser("add", help="Create a new issue (idempotent)")
    p_add.add_argument("references_root")
    p_add.add_argument("--kind", required=True)
    p_add.add_argument("--slug", default=None)
    p_add.add_argument("--concept", default=None)
    p_add.add_argument("--candidate", default=None)
    p_add.add_argument("--reason", default=None)
    p_add.add_argument("--suggested-action", default=None)
    p_add.add_argument("--opened-by", default=None)

    p_list = sub.add_parser("list", help="List issues as JSON")
    p_list.add_argument("references_root")
    p_list.add_argument("--include-closed", action="store_true")
    p_list.add_argument("--kind", default=None)
    p_list.add_argument("--slug", default=None)

    p_close = sub.add_parser("close", help="Move open issue(s) into issues/closed/")
    p_close.add_argument("references_root")
    p_close.add_argument("--id", dest="issue_id", default=None, help="Exact basename")
    p_close.add_argument("--kind", default=None)
    p_close.add_argument("--slug", default=None)
    p_close.add_argument("--closed-by", default=None)

    args = parser.parse_args()

    root = Path(args.references_root).expanduser().resolve()
    if not root.is_dir():
        print(f"[error] not a directory: {root}", file=sys.stderr)
        return 2

    if args.cmd == "add":
        result = add_issue(
            root,
            kind=args.kind,
            slug=args.slug,
            concept=args.concept,
            candidate=args.candidate,
            reason=args.reason,
            suggested_action=args.suggested_action,
            opened_by=args.opened_by,
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0

    if args.cmd == "list":
        out = list_issues(
            root,
            include_closed=args.include_closed,
            kind=args.kind,
            slug=args.slug,
        )
        print(json.dumps(out, indent=2, ensure_ascii=False))
        return 0

    if args.cmd == "close":
        try:
            result = close_issue(
                root,
                issue_id=args.issue_id,
                kind=args.kind,
                slug=args.slug,
                closed_by=args.closed_by,
            )
        except ValueError as exc:
            print(f"[error] {exc}", file=sys.stderr)
            return 2
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return 0

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
