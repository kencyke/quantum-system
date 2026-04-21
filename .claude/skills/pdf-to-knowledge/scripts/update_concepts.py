#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Rebuild ``<references-root>/CONCEPTS.md`` from every ``INDEX.md`` under it.

Runs after a new PDF is ingested so concepts mentioned across multiple
documents appear in one cross-document index. The script is intentionally
dependency-free so it can execute with ``python3 update_concepts.py``.

Usage:
    python3 update_concepts.py <references-root>

Example:
    python3 update_concepts.py ./references

Behaviour:
- Walks each subdirectory of ``<references-root>`` that contains an
  ``INDEX.md`` and extracts bullets under ``## Key concepts``.
- Groups entries by the leading backtick-quoted identifier, so
  ``- `modular automorphism group` via Tomita-Takesaki ... → needs formalization``
  is keyed by ``modular automorphism group``.
- Writes ``<references-root>/CONCEPTS.md`` with one section per concept,
  sorted alphabetically by display name; existing file is overwritten.
- Bullets without a backtick-led identifier fall under
  ``Unnamed concepts`` so nothing is silently lost.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path


KEY_CONCEPTS_HEADER = re.compile(r"^##\s+Key concepts\s*$", re.IGNORECASE)
NEXT_H2 = re.compile(r"^##\s+")
BULLET = re.compile(r"^\s*-\s+(.*)$")
LEADING_CODE = re.compile(r"^`([^`]+)`(.*)$")
# Characters that plausibly separate a concept name from its description when
# the author forgot to wrap the name in backticks (iteration-5 fallback).
PLAIN_SEPARATOR = re.compile(r"\s*(?:[—–:]|\s-\s|\()\s*")
ANNOTATION_SPLIT = re.compile(r"\s*→\s")


def _fallback_concept_name(body: str) -> tuple[str, str]:
    r"""Best-effort concept extraction for bullets that lack a backtick head.

    Strategy: strip any trailing ``→ mathlib:`` / ``→ needs formalization``
    annotation, then split on the first em-dash, en-dash, colon, " - ", or
    opening parenthesis. The left side becomes the concept name; the right
    side (plus the original annotation) becomes the body. If no separator is
    found, collapse names longer than 60 chars so they do not dominate the
    concept index header.
    """
    # Preserve the annotation so it travels with the bullet in CONCEPTS.md.
    annotation = ""
    parts = ANNOTATION_SPLIT.split(body, maxsplit=1)
    head = parts[0].strip()
    if len(parts) == 2:
        annotation = "→ " + parts[1].strip()

    m = PLAIN_SEPARATOR.search(head)
    if m:
        name = head[: m.start()].strip()
        rest = head[m.end() :].strip()
        # If we split on "(" leave the content so the user sees the full
        # phrasing, but close a dangling paren if the close-paren was the
        # last char.
        if m.group(0).startswith("(") and rest.endswith(")"):
            rest = rest[:-1].rstrip()
    else:
        name = head
        rest = ""

    # Avoid absurdly long "names" when the bullet is really one long sentence.
    if len(name) > 60:
        name = name[:60].rstrip(" -") + "…"

    body_parts = [p for p in (rest, annotation) if p]
    return name, "  ".join(body_parts)


def extract_key_concepts(md: str) -> list[tuple[str, str]]:
    """Return ``(concept_name, rest_of_bullet)`` pairs from an INDEX.md body.

    Preference order:
    1. Leading ```backtick``-quoted identifier (contracted format from step 4c).
    2. Heuristic fallback (see ``_fallback_concept_name``).
    3. Empty name — bullet lands under ``Unnamed concepts``.
    """
    lines = md.splitlines()
    inside = False
    collected: list[tuple[str, str]] = []

    for line in lines:
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
        m = LEADING_CODE.match(body)
        if m:
            name = m.group(1).strip()
            rest = m.group(2).lstrip(" -—:").rstrip()
        else:
            name, rest = _fallback_concept_name(body)
        collected.append((name, rest))
    return collected


def load_index_files(references_root: Path) -> dict[str, Path]:
    """Return ``{slug: index_md_path}`` for every ``<slug>/INDEX.md`` under the root."""
    mapping: dict[str, Path] = {}
    for entry in sorted(references_root.iterdir()):
        if not entry.is_dir():
            continue
        index = entry / "INDEX.md"
        if index.is_file():
            mapping[entry.name] = index
    return mapping


def build_concepts_md(references_root: Path, script_rel: str) -> str:
    """Render the final ``CONCEPTS.md`` text."""
    # group[display_name] = list of (slug, rest_of_bullet)
    grouped: dict[str, list[tuple[str, str]]] = defaultdict(list)
    display_name: dict[str, str] = {}

    for slug, index_path in load_index_files(references_root).items():
        text = index_path.read_text(encoding="utf-8", errors="replace")
        for name, rest in extract_key_concepts(text):
            key = name.lower() if name else ""
            if name and key not in display_name:
                display_name[key] = name
            grouped[key].append((slug, rest))

    out: list[str] = [
        "# Concepts index",
        "",
        "Auto-generated from references/*/INDEX.md. Do not edit by hand —",
        f"rerun `{script_rel} references/` to refresh.",
        "",
    ]

    if not grouped:
        out.append("_No concepts found yet._")
        out.append("")
        return "\n".join(out)

    def sort_key(k: str) -> tuple[int, str]:
        # Non-empty names first, sorted alphabetically; unnamed bucket last.
        return (1 if k == "" else 0, display_name.get(k, "Unnamed concepts").lower())

    for key in sorted(grouped, key=sort_key):
        header = display_name.get(key, "Unnamed concepts") if key else "Unnamed concepts"
        out.append(f"## {header}")
        out.append("")
        for slug, rest in grouped[key]:
            link = f"[{slug}]({slug}/INDEX.md)"
            if rest:
                out.append(f"- {link} — {rest}")
            else:
                out.append(f"- {link}")
        out.append("")

    return "\n".join(out)


def audit_freshness(references_root: Path) -> dict:
    """Return the list of ``<slug>/INDEX.md`` newer than ``CONCEPTS.md``.

    Used by ``--check-fresh`` to surface staleness caused by edits that
    skipped the concept-index refresh (T3-A guard). ``CONCEPTS.md`` absent
    is itself a staleness signal.
    """
    concepts = references_root / "CONCEPTS.md"
    missing_concepts = not concepts.is_file()
    concepts_mtime = concepts.stat().st_mtime if concepts.is_file() else 0.0
    newer: list[dict] = []
    for slug, index_path in load_index_files(references_root).items():
        idx_mtime = index_path.stat().st_mtime
        # Small skew tolerance (1 s) so a CONCEPTS.md written in the same
        # second as the INDEX.md still passes.
        if idx_mtime > concepts_mtime + 1:
            newer.append(
                {
                    "slug": slug,
                    "path": str(index_path),
                    "index_mtime": idx_mtime,
                    "concepts_mtime": concepts_mtime,
                }
            )
    return {
        "concepts_present": not missing_concepts,
        "concepts_path": str(concepts),
        "concepts_mtime": concepts_mtime,
        "newer_index_files": newer,
        "is_fresh": not missing_concepts and not newer,
    }


def audit_strict(references_root: Path) -> list[dict]:
    r"""Return a list of ``{slug, line, body}`` violations of the format contract.

    The contract (SKILL.md step 4c) says every Key concepts bullet must
    start with a ``\`backtick\`-quoted`` identifier. This auditor flags:

    - Bullets that do not start with a backtick token at all (the ones
      that collapse into the synthetic ``Unnamed concepts`` bucket).
    - Bullets whose leading backtick contains whitespace but no
      punctuation (ambiguous identifier).

    The returned list is empty when the tree complies.
    """
    violations: list[dict] = []
    for slug, index_path in load_index_files(references_root).items():
        text = index_path.read_text(encoding="utf-8", errors="replace")
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
            if not LEADING_CODE.match(body):
                violations.append(
                    {
                        "slug": slug,
                        "index_path": str(index_path),
                        "line": idx,
                        "body": body,
                    }
                )
    return violations


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("references_root", help="Directory that contains per-slug subdirs")
    parser.add_argument(
        "--strict",
        action="store_true",
        help=(
            "Exit non-zero if any Key concepts bullet does not start with a "
            "backtick-quoted identifier. Use in CI / post-ingestion hooks "
            "to catch format drift that would otherwise silently collapse "
            "into the 'Unnamed concepts' bucket."
        ),
    )
    parser.add_argument(
        "--check-fresh",
        action="store_true",
        help=(
            "Read-only staleness check: exit 1 if any references/<slug>/INDEX.md "
            "was modified after references/CONCEPTS.md (or CONCEPTS.md is "
            "missing). Does not regenerate — combine with a separate "
            "invocation to refresh. Use in hooks / CI to fail fast when the "
            "concept index falls out of sync."
        ),
    )
    args = parser.parse_args()

    references_root = Path(args.references_root).expanduser().resolve()
    if not references_root.is_dir():
        print(f"[error] not a directory: {references_root}", file=sys.stderr)
        return 2

    if args.check_fresh:
        report = audit_freshness(references_root)
        if report["is_fresh"]:
            print(f"[ok] CONCEPTS.md fresh: {report['concepts_path']}")
            return 0
        if not report["concepts_present"]:
            print(
                f"[fail] {report['concepts_path']} does not exist — run "
                "update_concepts.py without --check-fresh to generate it.",
                file=sys.stderr,
            )
        else:
            print(
                f"[fail] {len(report['newer_index_files'])} INDEX.md file(s) "
                "newer than CONCEPTS.md — re-run update_concepts.py to refresh:",
                file=sys.stderr,
            )
            for item in report["newer_index_files"]:
                print(f"  {item['slug']}  {item['path']}", file=sys.stderr)
        return 1

    if args.strict:
        violations = audit_strict(references_root)
        if violations:
            print(
                f"[fail] {len(violations)} Key concepts bullet(s) miss the "
                "leading `backtick` identifier contract:",
                file=sys.stderr,
            )
            for v in violations:
                snippet = v["body"][:100] + ("…" if len(v["body"]) > 100 else "")
                print(
                    f"  {v['slug']} INDEX.md:{v['line']}  {snippet}",
                    file=sys.stderr,
                )
            print(
                "[hint] rewrite each offending bullet so it starts with a "
                "`backtick-quoted` concept name — this is what "
                "scripts/update_concepts.py keys off for the cross-document "
                "index (SKILL.md step 4c).",
                file=sys.stderr,
            )
            return 1

    script_rel = ".claude/skills/pdf-to-knowledge/scripts/update_concepts.py"
    md = build_concepts_md(references_root, script_rel)
    target = references_root / "CONCEPTS.md"
    target.write_text(md.rstrip() + "\n", encoding="utf-8")

    concept_count = sum(1 for line in md.splitlines() if line.startswith("## "))
    print(f"[ok] wrote {target} ({concept_count} concepts)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
