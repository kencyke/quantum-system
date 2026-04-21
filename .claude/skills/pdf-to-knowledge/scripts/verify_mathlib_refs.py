#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
r"""Audit ``→ mathlib: ...`` annotations in ``references/*/INDEX.md`` files.

This script does not itself call the Lean toolchain — the actual existence
check is performed by the caller (Claude) via the
``mcp__lean-lsp__lean_verify`` MCP tool, one symbol at a time. The script
is the mechanical half:

- ``extract``   Walk the references root, pull every ``→ mathlib: ...``
                annotation into a JSON worklist. The caller feeds each
                candidate symbol to ``lean_verify`` and records failures
                in a ``failed.json``.
- ``mark-unverified``   Given the caller's ``failed.json``, rewrite each
                offending INDEX.md bullet so the annotation becomes
                ``→ mathlib: \`<path>\` [UNVERIFIED]`` — a marker that
                ``gap-filler``'s ``detect_gaps.py`` reads as ``suspect``
                status.

Rationale: we do not want to trust Claude's judgement on whether a Lean
declaration exists. The T1-A remediation is to externalise verification
to the Lean MCP and mark anything that can not be proven to exist.

Usage:
    python3 verify_mathlib_refs.py extract <references-root> [--output worklist.json]
    python3 verify_mathlib_refs.py mark-unverified <references-root> \\
        --from failed.json [--dry-run]

The ``failed.json`` schema expected by ``mark-unverified`` is:

    [
      {
        "slug": "arxiv-2202.03357",
        "line": 47,
        "reason": "Mathlib.FakeName.notAReal not found by lean_verify"
      },
      ...
    ]
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path


KEY_CONCEPTS_HEADER = re.compile(r"^##\s+Key concepts\s*$", re.IGNORECASE)
NEXT_H2 = re.compile(r"^##\s+")
BULLET = re.compile(r"^\s*-\s+(.*)$")
ANNOT_SPLIT = re.compile(r"(\s*→\s*mathlib\s*:\s*)", re.IGNORECASE)
TICKED = re.compile(r"`([^`]+)`")
UNVERIFIED_MARKER = "[UNVERIFIED]"
VERIFIED_FIELD = "mathlib_verified"
STALE_SKEW_SECONDS = 5


def _read_slug(md_text: str, fallback: str) -> str:
    in_front = False
    for line in md_text.splitlines():
        if line.strip() == "---":
            if not in_front:
                in_front = True
                continue
            break
        if in_front:
            m = re.match(r"^slug\s*:\s*(.+)$", line)
            if m:
                return m.group(1).strip().strip('"').strip("'")
    return fallback


def _extract_concept_name(body: str) -> str:
    m = re.match(r"^`([^`]+)`", body)
    if m:
        return m.group(1).strip()
    head = body.split("—", 1)[0].split(":", 1)[0].split("(", 1)[0].strip()
    return head[:80]


IDENT_OR_QUALIFIED = re.compile(r"^[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*$")


def _collect_candidates(annotation_body: str, concept: str) -> list[str]:
    """Enumerate things the caller should try passing to ``lean_verify``.

    Order of preference:
    1. Backticked tokens in the annotation (both module paths and decl names).
    2. Bare ``Foo.Bar.baz`` tokens in the annotation (typical of bullets
       where the author wrapped only the concept, not the mathlib path).
    3. The bullet's leading backticked concept head itself — often a decl
       name (e.g. ``VonNeumannAlgebra``) that exists without any extra
       hint in the annotation.

    Duplicates are preserved (order matters for the verifier; we try the
    more specific candidate first) but obvious module-path tokens are
    kept because ``lean_verify`` can also check a namespace.
    """
    candidates: list[str] = []

    for token in TICKED.findall(annotation_body):
        token = token.strip()
        if IDENT_OR_QUALIFIED.match(token):
            candidates.append(token)

    for bare in re.findall(r"[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)+", annotation_body):
        if bare not in candidates:
            candidates.append(bare)

    concept = concept.strip()
    if concept and IDENT_OR_QUALIFIED.match(concept) and concept not in candidates:
        candidates.append(concept)

    return candidates


def iter_index_files(root: Path):
    for entry in sorted(root.iterdir()):
        if not entry.is_dir():
            continue
        index = entry / "INDEX.md"
        if index.is_file():
            yield entry.name, index


def extract(root: Path) -> dict:
    items: list[dict] = []
    for slug_dirname, index_path in iter_index_files(root):
        text = index_path.read_text(encoding="utf-8", errors="replace")
        slug = _read_slug(text, slug_dirname)
        lines = text.splitlines()
        inside = False
        for idx, line in enumerate(lines, start=1):
            if KEY_CONCEPTS_HEADER.match(line):
                inside = True
                continue
            if inside and NEXT_H2.match(line):
                break
            if not inside:
                continue
            bullet = BULLET.match(line)
            if not bullet:
                continue
            body = bullet.group(1).strip()
            if not body or body.startswith("<!--"):
                continue
            parts = ANNOT_SPLIT.split(body, maxsplit=1)
            if len(parts) < 3:
                continue
            annotation = parts[1] + parts[2]
            if UNVERIFIED_MARKER in annotation:
                continue  # already flagged; leave alone
            concept = _extract_concept_name(body)
            candidates = _collect_candidates(parts[2], concept)
            if not candidates:
                continue
            items.append(
                {
                    "slug": slug,
                    "index_path": str(index_path),
                    "line": idx,
                    "concept": concept,
                    "raw_annotation": annotation.strip(),
                    "candidates": candidates,
                }
            )
    return {
        "references_root": str(root),
        "total_items": len(items),
        "items": items,
    }


def _frontmatter_span(text: str) -> tuple[int, int] | None:
    """Return ``(open_line, close_line)`` of the YAML fences (1-indexed, inclusive)."""
    lines = text.splitlines()
    if not lines or lines[0].strip() != "---":
        return None
    for i in range(1, len(lines)):
        if lines[i].strip() == "---":
            return (1, i + 1)
    return None


def _set_frontmatter_field(index_path: Path, field: str, value: str) -> bool:
    text = index_path.read_text(encoding="utf-8", errors="replace")
    span = _frontmatter_span(text)
    if span is None:
        return False
    had_trailing_nl = text.endswith("\n")
    lines = text.splitlines(keepends=True)
    open_ln, close_ln = span
    field_re = re.compile(rf"^{re.escape(field)}\s*:\s*.*$")
    # Replace existing field if present.
    for idx in range(open_ln, close_ln - 1):
        stripped = lines[idx].rstrip("\n")
        if field_re.match(stripped):
            lines[idx] = f"{field}: {value}\n"
            index_path.write_text("".join(lines), encoding="utf-8")
            return True
    # Otherwise insert directly before the closing fence.
    insert_at = close_ln - 1
    lines.insert(insert_at, f"{field}: {value}\n")
    patched = "".join(lines)
    if not had_trailing_nl and patched.endswith("\n"):
        patched = patched.rstrip("\n")
    index_path.write_text(patched, encoding="utf-8")
    return True


def _read_frontmatter_field(index_path: Path, field: str) -> str | None:
    text = index_path.read_text(encoding="utf-8", errors="replace")
    span = _frontmatter_span(text)
    if span is None:
        return None
    lines = text.splitlines()
    field_re = re.compile(rf"^{re.escape(field)}\s*:\s*(.+)$")
    for idx in range(span[0], span[1] - 1):
        m = field_re.match(lines[idx])
        if m:
            return m.group(1).strip().strip('"').strip("'")
    return None


def _mark_one(index_path: Path, line_no: int, reason: str, *, dry_run: bool) -> bool:
    text = index_path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines(keepends=True)
    if line_no < 1 or line_no > len(lines):
        print(f"[warn] out-of-range line {line_no} in {index_path}", file=sys.stderr)
        return False
    original = lines[line_no - 1]
    if UNVERIFIED_MARKER in original:
        return False  # nothing to do
    had_trailing_nl = original.endswith("\n")
    stripped = original.rstrip("\n")
    # Append the marker at the very end of the bullet; reason optional.
    if reason:
        patched = f"{stripped} {UNVERIFIED_MARKER} ({reason})"
    else:
        patched = f"{stripped} {UNVERIFIED_MARKER}"
    lines[line_no - 1] = patched + ("\n" if had_trailing_nl else "")
    if dry_run:
        print(f"[dry-run] {index_path}:{line_no}: {stripped!r} -> {patched!r}")
        return True
    index_path.write_text("".join(lines), encoding="utf-8")
    return True


def mark_unverified(root: Path, failures: list[dict], *, dry_run: bool) -> dict:
    marked = 0
    skipped = 0
    per_slug: dict[str, list[int]] = {}
    for failure in failures:
        slug = failure.get("slug")
        line_no = failure.get("line")
        reason = (failure.get("reason") or "").strip()
        if not slug or not line_no:
            skipped += 1
            continue
        index_path = root / slug / "INDEX.md"
        if not index_path.is_file():
            print(f"[warn] missing INDEX.md for slug {slug!r}", file=sys.stderr)
            skipped += 1
            continue
        if _mark_one(index_path, int(line_no), reason, dry_run=dry_run):
            marked += 1
            per_slug.setdefault(slug, []).append(int(line_no))
        else:
            skipped += 1
    # After patching (real mode), stamp every INDEX.md with a fresh
    # ``mathlib_verified`` marker so ``check-done`` can prove the
    # verification cycle actually ran on this tree.
    stamped: list[str] = []
    if not dry_run:
        timestamp = _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")
        for slug_dirname, index_path in iter_index_files(root):
            if _set_frontmatter_field(index_path, VERIFIED_FIELD, timestamp):
                stamped.append(slug_dirname)
    return {
        "marked": marked,
        "skipped": skipped,
        "per_slug": per_slug,
        "dry_run": dry_run,
        "stamped_slugs": stamped,
    }


def check_done(root: Path) -> dict:
    """Confirm every INDEX.md under ``root`` carries a fresh verification marker.

    Returns a report with ``ok`` (True when the tree is verified clean),
    ``unverified`` (slugs whose INDEX.md lacks the stamp or has a
    malformed timestamp) and ``stale`` (slugs whose INDEX.md was edited
    after the last verification).
    """
    unverified: list[dict] = []
    stale: list[dict] = []
    ok_slugs: list[str] = []
    for slug_dirname, index_path in iter_index_files(root):
        stamp_raw = _read_frontmatter_field(index_path, VERIFIED_FIELD)
        if not stamp_raw:
            unverified.append(
                {"slug": slug_dirname, "path": str(index_path), "reason": "no mathlib_verified field"}
            )
            continue
        try:
            stamp = _dt.datetime.fromisoformat(stamp_raw)
            if stamp.tzinfo is None:
                stamp = stamp.replace(tzinfo=_dt.timezone.utc)
        except ValueError:
            unverified.append(
                {
                    "slug": slug_dirname,
                    "path": str(index_path),
                    "reason": f"unparseable timestamp {stamp_raw!r}",
                }
            )
            continue
        mtime = _dt.datetime.fromtimestamp(
            index_path.stat().st_mtime, _dt.timezone.utc
        )
        if mtime > stamp + _dt.timedelta(seconds=STALE_SKEW_SECONDS):
            stale.append(
                {
                    "slug": slug_dirname,
                    "path": str(index_path),
                    "verified_at": stamp.isoformat(),
                    "mtime": mtime.isoformat(),
                }
            )
            continue
        ok_slugs.append(slug_dirname)
    return {
        "ok": not unverified and not stale,
        "verified_slugs": ok_slugs,
        "unverified": unverified,
        "stale": stale,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_extract = sub.add_parser("extract", help="Extract mathlib annotation worklist")
    p_extract.add_argument("references_root")
    p_extract.add_argument("--output", default=None)

    p_mark = sub.add_parser("mark-unverified", help="Patch INDEX.md with [UNVERIFIED]")
    p_mark.add_argument("references_root")
    p_mark.add_argument("--from", dest="failures_path", required=True)
    p_mark.add_argument("--dry-run", action="store_true")

    p_check = sub.add_parser(
        "check-done",
        help="Exit 1 if any INDEX.md lacks a fresh mathlib_verified stamp",
    )
    p_check.add_argument("references_root")

    args = parser.parse_args()

    root = Path(args.references_root).expanduser().resolve()
    if not root.is_dir():
        print(f"[error] not a directory: {root}", file=sys.stderr)
        return 2

    if args.cmd == "extract":
        report = extract(root)
        payload = json.dumps(report, indent=2, ensure_ascii=False)
        if args.output:
            Path(args.output).write_text(payload + "\n", encoding="utf-8")
            print(
                f"[ok] wrote {args.output}: {report['total_items']} mathlib annotations",
                file=sys.stderr,
            )
        else:
            print(payload)
        return 0

    if args.cmd == "mark-unverified":
        failures_raw = Path(args.failures_path).read_text(encoding="utf-8")
        try:
            failures = json.loads(failures_raw)
        except json.JSONDecodeError as exc:
            print(f"[error] bad JSON: {exc}", file=sys.stderr)
            return 2
        if not isinstance(failures, list):
            print("[error] failures JSON must be a list of objects", file=sys.stderr)
            return 2
        summary = mark_unverified(root, failures, dry_run=args.dry_run)
        print(json.dumps(summary, indent=2, ensure_ascii=False))
        return 0

    if args.cmd == "check-done":
        report = check_done(root)
        print(json.dumps(report, indent=2, ensure_ascii=False))
        if report["ok"]:
            return 0
        print(
            f"[fail] {len(report['unverified'])} unverified + "
            f"{len(report['stale'])} stale INDEX.md under {root}",
            file=sys.stderr,
        )
        return 1

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
