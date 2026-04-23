#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Rank a paper's bibliography by in-text centrality.

Given a ``references/<slug>/`` directory that contains an ``INDEX.md`` with
a ``bibliography:`` YAML frontmatter list and a ``content.md`` body, this
script counts how often each bibliography entry is cited in the body —
weighted by position, with citations closer to the top (abstract /
introduction / early theorems) counted double.

Output JSON lists uninvested entries (``ingested: false``) ranked by
weighted citation score, with any ``arxiv`` / ``doi`` IDs surfaced so a
gap-filler loop can decide what to pull in next.

Usage:
    python3 rank_bibliography.py <slug-dir> [--output ranked.json]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


# --- minimal YAML frontmatter reader (no external deps) ---

_FRONT_BEGIN = re.compile(r"^---\s*$")


def _split_frontmatter(text: str) -> tuple[str, str]:
    lines = text.splitlines()
    if not lines or not _FRONT_BEGIN.match(lines[0]):
        return "", text
    out: list[str] = []
    i = 1
    while i < len(lines) and not _FRONT_BEGIN.match(lines[i]):
        out.append(lines[i])
        i += 1
    body = "\n".join(lines[i + 1 :]) if i < len(lines) else ""
    return "\n".join(out), body


_LIST_ITEM = re.compile(r"^\s{0,4}-\s+(.*)$")
_KV = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*)$")


def _strip_yaml_scalar(value: str) -> object:
    value = value.strip()
    if value in ("null", "~", ""):
        return None
    if value == "true":
        return True
    if value == "false":
        return False
    if value.startswith('"') and value.endswith('"'):
        return value[1:-1]
    if value.startswith("'") and value.endswith("'"):
        return value[1:-1]
    if value.startswith("["):
        # best-effort inline list, used by `authors`.
        inner = value.strip("[]")
        return [s.strip().strip('"').strip("'") for s in inner.split(",") if s.strip()]
    try:
        return int(value)
    except ValueError:
        pass
    try:
        return float(value)
    except ValueError:
        pass
    return value


def parse_bibliography(frontmatter: str) -> list[dict]:
    """Extract the ``bibliography:`` list from raw YAML frontmatter text."""
    lines = frontmatter.splitlines()
    entries: list[dict] = []
    in_bib = False
    current: dict | None = None
    bib_indent: int | None = None
    for line in lines:
        stripped = line.lstrip()
        indent = len(line) - len(stripped)
        if not in_bib:
            if re.match(r"^bibliography\s*:\s*$", line):
                in_bib = True
                bib_indent = None
            continue
        if line.strip() == "":
            continue
        # Exiting on a dedented top-level key.
        if indent == 0 and stripped and not stripped.startswith("-"):
            break
        item = _LIST_ITEM.match(line)
        if item:
            if current is not None:
                entries.append(current)
            current = {}
            bib_indent = indent
            rest = item.group(1)
            kv = _KV.match(rest)
            if kv:
                current[kv.group(1)] = _strip_yaml_scalar(kv.group(2))
            continue
        kv = _KV.match(line)
        if kv and current is not None:
            current[kv.group(1)] = _strip_yaml_scalar(kv.group(2))
    if current is not None:
        entries.append(current)
    return entries


# --- citation counting ---


def _strip_references_section(body: str) -> str:
    """Drop the ``## References`` tail so bib entries are not counted there."""
    lines = body.splitlines()
    for i, line in enumerate(lines):
        if re.match(r"^##\s+(References|Bibliography)\s*$", line, re.IGNORECASE):
            return "\n".join(lines[:i])
    return body


def _candidate_tokens(entry: dict) -> list[str]:
    """Produce literal tokens we will search for in the body.

    Covers four common in-text citation styles:

    1. Custom key — ``Ara76``, ``Kos86a`` (author-year).
    2. Numeric bracketed — ``[1]`` etc. (for ``refNN`` keys).
    3. Parenthetical / inline author-year — ``Araki 1976`` or
       ``(Araki, 1976)`` or ``Araki [1]``.
    4. "et al." variants — ``Araki et al.``.

    Returned list is de-duplicated in order of emission so the caller's
    ``_count_weighted`` sums them without double-counting.
    """
    tokens: list[str] = []

    def _add(tok: str) -> None:
        tok = tok.strip()
        if tok and tok not in tokens:
            tokens.append(tok)

    key = entry.get("key")
    if key:
        _add(str(key))
        # numeric keys like ``ref01`` — also scan for the bracketed number ``[1]``.
        m = re.match(r"^ref0*(\d+)$", str(key), re.IGNORECASE)
        if m:
            num = m.group(1)
            _add(f"[{num}]")
            _add(f"({num})")  # some authors use ``(1)`` for numeric cites
    authors = entry.get("authors") or []
    surnames: list[str] = []
    if isinstance(authors, list) and authors:
        for author in authors[:3]:
            head = str(author).strip()
            if not head:
                continue
            surname = head.split()[-1]
            if surname and len(surname) > 2:
                surnames.append(surname)
    year = entry.get("year")
    if surnames:
        first = surnames[0]
        _add(first)
        if year:
            # Space-separated "Araki 1976".
            _add(f"{first} {year}")
            # Parenthetical variants commonly used in math prose.
            _add(f"{first}, {year}")
            _add(f"({first} {year})")
            _add(f"({first}, {year})")
            # Compact "Araki(1976)" form sometimes seen in typeset bibs.
            _add(f"{first} ({year})")
        if len(surnames) >= 2:
            _add(f"{surnames[0]} and {surnames[1]}")
            _add(f"{surnames[0]}-{surnames[1]}")  # "Pimsner-Popa"
            _add(f"{surnames[0]}–{surnames[1]}")  # en-dash variant
        if len(surnames) >= 3:
            _add(f"{first} et al.")
            _add(f"{first} et al")
    title = entry.get("title")
    if isinstance(title, str) and len(title) > 20:
        head = title.strip(". ")
        words = [w for w in re.split(r"\W+", head.lower()) if len(w) > 3]
        if words:
            _add(" ".join(words[:3]))
    return tokens


# Math-strong university domains whose faculty publicly host coherent
# student-facing lecture notes. Rotate through these when a bibliography
# entry lacks an arxiv / DOI but the concept is a standard topic — the
# resulting PDFs are typically clearer than original research papers or
# Wikipedia articles. Users can edit this list in-place to add local
# favourites (e.g. domestic universities, specialised centres).
UNIVERSITY_DOMAINS: tuple[str, ...] = (
    "caltech.edu",
    "mit.edu",
    "math.berkeley.edu",
    "math.stanford.edu",
    "math.princeton.edu",
    "math.harvard.edu",
    "math.columbia.edu",
    "math.uchicago.edu",
    "math.ucla.edu",
    "cam.ac.uk",
    "ox.ac.uk",
    "ihes.fr",
    "ens.fr",
    "math.u-tokyo.ac.jp",
    "kurims.kyoto-u.ac.jp",
    "ms.u-tokyo.ac.jp",
    "mpim-bonn.mpg.de",
    "math.ias.edu",
)


def _title_keywords(entry: dict, max_words: int = 6) -> str:
    """Pick the most distinctive noun-ish words from the entry's title."""
    title = entry.get("title") or ""
    if not isinstance(title, str):
        return ""
    tokens = [w.strip(".,;:()[]") for w in title.split() if len(w.strip(".,;:()[]")) > 3]
    # Drop generic words that do not narrow search results.
    generic = {
        "theory",
        "theorem",
        "paper",
        "article",
        "note",
        "notes",
        "results",
        "proof",
        "introduction",
        "remarks",
        "comments",
    }
    keep = [t for t in tokens if t.lower() not in generic]
    return " ".join((keep or tokens)[:max_words])


# Pre-1995 mathematics predates institutional preprint hosting; universities
# rarely surface the paper itself, but the concept is usually covered in
# modern lecture notes and open-access archives. Post-1995 papers are more
# likely to live on faculty homepages. The cutoff is empirical, calibrated
# from iteration-2's end-to-end eval: Jon83/PP86/Kos86a all drew blanks on
# every university domain, while Jones's 2009 Berkeley notes succeeded
# immediately on the math.berkeley.edu rotation.
PRE_INSTITUTIONAL_HOSTING_YEAR = 1995


def _suggest_search_queries(entry: dict, domains_per_entry: int = 3) -> list[dict]:
    """Produce search-engine queries that an agent can feed to WebSearch.

    Strategy: the bibliography has many pre-arxiv / no-arxiv entries
    (common in operator algebra, older physics). Which query strategy
    surfaces the paper depends strongly on publication year:

    - **``year >= 1995`` (modern)**: university faculty pages host
      lecture notes, and the author often self-hosts — try the
      university domain rotation first.
    - **``year < 1995`` (legacy)**: university domains almost always
      miss; the paper was never posted to an institutional server.
      Promote the lecture-notes fallback plus open-access publisher
      archives (NUMDAM, Project Euclid) to the front and demote
      university-PDF queries to the tail. Validated in iter-2 where
      PP86 hit NUMDAM and Kos86a hit Carlen's AZ-school lecture notes
      from the lecture-notes query; all three university domains
      drew blanks.

    When ``year`` is missing, fall through to the modern ordering.
    """
    title_kws = _title_keywords(entry)
    authors = entry.get("authors") or []
    first_surname = ""
    if isinstance(authors, list) and authors:
        head = str(authors[0]).strip()
        first_surname = head.split()[-1] if head else ""

    base_terms: list[str] = []
    if title_kws:
        base_terms.append(title_kws)
    if first_surname:
        base_terms.append(first_surname)
    if not base_terms:
        return []

    term = " ".join(base_terms)

    def _university_queries() -> list[dict]:
        return [
            {
                "strategy": f"university-pdf:{domain}",
                "query": f"{term} pdf site:{domain}",
            }
            for domain in UNIVERSITY_DOMAINS[:domains_per_entry]
        ]

    def _lecture_and_oa_queries(is_legacy: bool) -> list[dict]:
        out: list[dict] = [
            {
                "strategy": "lecture-notes",
                "query": f'{term} "lecture notes" filetype:pdf',
            }
        ]
        if is_legacy:
            # Open-access archives that host classical math / physics
            # journal papers. Pulled to the front for legacy entries
            # because university domains miss consistently on this era.
            out.append(
                {
                    "strategy": "numdam",
                    "query": f"{term} site:numdam.org",
                }
            )
            out.append(
                {
                    "strategy": "project-euclid",
                    "query": f"{term} site:projecteuclid.org",
                }
            )
            out.append(
                {
                    "strategy": "open-access-pdf",
                    "query": f"{term} filetype:pdf",
                }
            )
        return out

    def _encyclopedia_queries() -> list[dict]:
        if not title_kws:
            return []
        return [
            {"strategy": "nlab", "query": f"{title_kws} site:ncatlab.org"},
            {"strategy": "wikipedia", "query": f"{title_kws} wikipedia"},
        ]

    year = entry.get("year")
    is_legacy = isinstance(year, int) and year < PRE_INSTITUTIONAL_HOSTING_YEAR

    if is_legacy:
        # Promote lecture-notes + OA archives; demote university-PDF.
        return (
            _lecture_and_oa_queries(is_legacy=True)
            + _encyclopedia_queries()
            + _university_queries()
        )
    # Modern / unknown-year: university-PDF first (current behaviour).
    return (
        _university_queries()
        + _lecture_and_oa_queries(is_legacy=False)
        + _encyclopedia_queries()
    )


def _count_weighted(body: str, token: str) -> tuple[int, float]:
    """Return (raw_count, weighted_score)."""
    if not token:
        return 0, 0.0
    pattern = re.compile(re.escape(token))
    length = max(len(body), 1)
    # First 30% is "early" (weight 2), the rest is weight 1.
    boundary = int(length * 0.3)
    early = weighted = raw = 0
    for m in pattern.finditer(body):
        raw += 1
        if m.start() < boundary:
            weighted += 2
            early += 1
        else:
            weighted += 1
    return raw, float(weighted)


def rank(references_slug_dir: Path) -> dict:
    index_md = references_slug_dir / "INDEX.md"
    content_md = references_slug_dir / "content.md"
    if not index_md.is_file():
        raise SystemExit(f"missing INDEX.md: {index_md}")
    if not content_md.is_file():
        raise SystemExit(f"missing content.md: {content_md}")

    fm, _ = _split_frontmatter(index_md.read_text(encoding="utf-8", errors="replace"))
    entries = parse_bibliography(fm)

    body = content_md.read_text(encoding="utf-8", errors="replace")
    body_main = _strip_references_section(body)

    ranked = []
    for entry in entries:
        tokens = _candidate_tokens(entry)
        total_raw = 0
        total_weighted = 0.0
        matched_token: str | None = None
        for token in tokens:
            raw, weighted = _count_weighted(body_main, token)
            if raw > total_raw:
                matched_token = token
            total_raw += raw
            total_weighted += weighted
        record = {
            "key": entry.get("key"),
            "title": entry.get("title"),
            "authors": entry.get("authors"),
            "year": entry.get("year"),
            "arxiv": entry.get("arxiv"),
            "doi": entry.get("doi"),
            "ingested": entry.get("ingested", False),
            "citations_raw": total_raw,
            "citation_score": round(total_weighted, 2),
            "matched_token": matched_token,
        }
        # Pre-compute search-engine queries for uninvested entries that do
        # not have an arxiv / DOI — these are the ones the gap-filler loop
        # needs to discover a URL for.
        if not record["ingested"] and not record["arxiv"] and not record["doi"]:
            record["suggested_search_queries"] = _suggest_search_queries(entry)
        ranked.append(record)

    ranked.sort(key=lambda r: (r["ingested"], -r["citation_score"], -r["citations_raw"]))
    uninvested = [r for r in ranked if not r["ingested"]]
    ingested = [r for r in ranked if r["ingested"]]
    return {
        "slug_dir": str(references_slug_dir),
        "entry_count": len(entries),
        "uninvested_top": uninvested[:15],
        "uninvested_rest": uninvested[15:],
        "ingested": ingested,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("slug_dir", help="Directory like references/arxiv-2202.03357/")
    parser.add_argument("--output", default=None, help="Write JSON here; default: stdout")
    args = parser.parse_args()

    slug_dir = Path(args.slug_dir).expanduser().resolve()
    report = rank(slug_dir)

    payload = json.dumps(report, indent=2, ensure_ascii=False)
    if args.output:
        Path(args.output).write_text(payload + "\n", encoding="utf-8")
        print(
            f"[ok] wrote {args.output}: {len(report['uninvested_top'])} top + "
            f"{len(report['uninvested_rest'])} remaining uninvested entries",
            file=sys.stderr,
        )
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
