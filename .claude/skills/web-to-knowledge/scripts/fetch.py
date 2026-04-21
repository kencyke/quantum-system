#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "beautifulsoup4>=4.12",
#   "markdownify>=0.14",
#   "lxml>=5.0",
# ]
# ///
"""Fetch a web page and save it as agent-friendly Markdown + image assets.

Mirrors the output layout of ``pdf-to-knowledge``'s ``convert.py`` so that
``scripts/update_concepts.py`` (from that skill) aggregates concepts across
PDF and web sources into a single ``references/CONCEPTS.md``.

Produces under ``<output-dir>/<slug>/``:

- ``INDEX.md``  Metadata, ToC, scaffolded Summary / Key concepts / bibliography
                sections that the caller (Claude) fills in after reading
                ``content.md``.
- ``content.md`` Full page Markdown with preserved LaTeX math (``$...$`` /
                ``$$...$$``) and relative image links.
- ``assets/``   Downloaded images referenced from ``content.md``.

Design choices:
- HTML parsing uses BeautifulSoup + markdownify (both permissive licenses).
  ``trafilatura`` was considered for content extraction but it strips
  ``<math>`` elements silently; doing the cleanup ourselves lets us preserve
  LaTeX via ``alt`` attributes and ``annotation encoding="application/x-tex"``.
- No section splitting: web pages do not have a natural page count; agents
  jump via the H2/H3 anchors in the INDEX.md ToC instead.

Usage:
    uv run fetch.py <url> [--output-dir DIR] [--slug SLUG]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Iterable


def slugify(text: str) -> str:
    text = text.lower().strip()
    # Treat connectors as word separators BEFORE stripping non-word chars so
    # nLab titles like "relative+entropy" stay "relative-entropy" and
    # Wikipedia titles like "Tomita–Takesaki_theory" (with en-dash) keep
    # the split.
    text = re.sub(r"[\s_+\-\u2010-\u2015]+", "-", text)
    text = re.sub(r"[^\w-]", "", text, flags=re.UNICODE)
    text = re.sub(r"-+", "-", text)
    return text[:80].strip("-") or "page"


def derive_slug(url: str) -> str:
    """Pick a descriptive slug based on known hosts and URL path."""
    parsed = urllib.parse.urlparse(url)
    host = parsed.netloc.lower()
    path = urllib.parse.unquote(parsed.path)

    # Wikipedia: https://en.wikipedia.org/wiki/<Title>
    m = re.match(r"^/wiki/([^/?#]+)$", path)
    if m and "wikipedia.org" in host:
        return f"wiki-{slugify(m.group(1))}"

    # nLab: https://ncatlab.org/nlab/show/<title>
    m = re.match(r"^/nlab/show/(.+)$", path)
    if m and "ncatlab.org" in host:
        return f"nlab-{slugify(m.group(1))}"

    # Generic: host-path slug
    base_host = host.split(".")[-2] if "." in host else host
    tail = Path(path).name or Path(path).stem or "index"
    return f"web-{base_host}-{slugify(tail)}"


def fetch_html(url: str) -> tuple[str, str]:
    """Download HTML. Returns (html_text, final_url) — the URL may redirect."""
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "web-to-knowledge/1.0 (+https://github.com/anthropics/claude-code)"
        },
    )
    with urllib.request.urlopen(req, timeout=60) as resp:
        final_url = resp.url
        raw = resp.read()
        charset = resp.headers.get_content_charset() or "utf-8"
    return raw.decode(charset, errors="replace"), final_url


def find_main_content(soup):
    """Locate the substantive body of the page using common conventions."""
    for selector in [
        "main",
        "article",
        "[role=main]",
        ".mw-parser-output",
        "#mw-content-text",
        "#content",
    ]:
        found = soup.select_one(selector)
        if found:
            return found
    return soup.body or soup


def strip_non_content(root) -> None:
    """Remove navigation, footers, scripts, styles, and known sidebars."""
    noisy_tags = ["script", "style", "nav", "footer", "aside", "noscript", "iframe"]
    for tag in root.find_all(noisy_tags):
        tag.decompose()
    # Wikipedia / nLab specific noise.
    noise_class_patterns = [
        r"mw-editsection",
        r"mw-cite-backlink",
        r"navbox",
        r"navigation-not-searchable",
        r"reference-list-only",
        r"printfooter",
        r"toc\b",
        r"sidebar",
        r"noprint",
        r"catlinks",
    ]
    compiled = re.compile("|".join(noise_class_patterns))
    for tag in root.find_all(class_=compiled):
        tag.decompose()
    for tag in root.find_all(id=re.compile(r"^(toc|siteSub|contentSub|footer|mw-navigation|catlinks|jump-to-nav)$")):
        tag.decompose()


_MATHML_TEX_ENCODING = re.compile(r"x-tex|TeX", re.IGNORECASE)
_DISPLAYSTYLE_WRAPPER = re.compile(r"^\s*\{\\displaystyle\s+(.+)\}\s*$", re.DOTALL)


def _strip_displaystyle(tex: str) -> str:
    """Unwrap ``{\\displaystyle ...}`` added by Wikipedia MathML rendering."""
    tex = tex.strip()
    m = _DISPLAYSTYLE_WRAPPER.match(tex)
    if m:
        inner = m.group(1).strip()
        # Only unwrap when braces balance in the inner body, to avoid breaking
        # LaTeX with intentional outer braces.
        if inner.count("{") == inner.count("}"):
            return inner
    return tex


def _extract_tex_from_math(math) -> str | None:
    ann = math.find("annotation", attrs={"encoding": _MATHML_TEX_ENCODING})
    if ann and ann.get_text(strip=True):
        return ann.get_text(strip=True)
    if math.get("alttext"):
        return math["alttext"].strip()
    return None


def preserve_math_tags(root, NavigableString) -> int:
    """Rewrite common math embeddings to inline/display LaTeX.

    Returns the number of formulas found. Handles:

    - Wikipedia wrapper ``<span class="mwe-math-element">`` containing both a
      ``<math>`` and a fallback ``<img>`` — collapsed to a single LaTeX span.
    - Bare ``<math>`` with ``<annotation encoding="application/x-tex">TeX</annotation>``
      or ``alttext="TeX"`` (nLab, MediaWiki without the wrapper).
    - Bare ``<img class="mwe-math-fallback-image-*" alt="TeX">`` without the
      wrapper span.
    - MathJax ``<script type="math/tex">...</script>`` /
      ``<script type="math/tex; mode=display">``.

    ``{\\displaystyle ...}`` wrappers that Wikipedia injects around every
    inline MathML expression are unwrapped so the emitted LaTeX reads
    naturally.
    """
    count = 0

    # 1. Wikipedia math-element wrappers — unify the MathML + image fallback.
    for span in root.find_all("span", class_="mwe-math-element"):
        math = span.find("math")
        tex = _extract_tex_from_math(math) if math else None
        if not tex:
            img = span.find("img", class_=re.compile(r"mwe-math-fallback-image"))
            if img and img.get("alt"):
                tex = img["alt"].strip()
        if not tex:
            continue
        classes = span.get("class") or []
        display = any("mwe-math-element" in c and "display" in c for c in classes)
        if not display and math is not None:
            display = math.get("display") == "block"
        tex = _strip_displaystyle(tex)
        wrapped = f"$$\n{tex}\n$$" if display else f"${tex}$"
        span.replace_with(NavigableString(wrapped))
        count += 1

    # 2. Bare MathML elements not wrapped by MediaWiki.
    for math in root.find_all("math"):
        tex = _extract_tex_from_math(math)
        if not tex:
            continue
        display = math.get("display") == "block"
        tex = _strip_displaystyle(tex)
        wrapped = f"$$\n{tex}\n$$" if display else f"${tex}$"
        math.replace_with(NavigableString(wrapped))
        count += 1

    # 3. Bare Wikipedia fallback images.
    for img in root.find_all("img", class_=re.compile(r"mwe-math-fallback-image")):
        alt = img.get("alt", "").strip()
        if not alt:
            continue
        classes = img.get("class") or []
        display = any("display" in c for c in classes)
        alt = _strip_displaystyle(alt)
        wrapped = f"$$\n{alt}\n$$" if display else f"${alt}$"
        img.replace_with(NavigableString(wrapped))
        count += 1

    # 4. MathJax scripts.
    for script in root.find_all(
        "script", attrs={"type": re.compile(r"math/tex", re.IGNORECASE)}
    ):
        tex = script.get_text().strip()
        if not tex:
            continue
        type_attr = script.get("type") or ""
        display = "display" in type_attr.lower()
        tex = _strip_displaystyle(tex)
        wrapped = f"$$\n{tex}\n$$" if display else f"${tex}$"
        script.replace_with(NavigableString(wrapped))
        count += 1

    return count


def download_image(url: str, dest: Path) -> bool:
    """Fetch ``url`` to ``dest``. Returns True on success, False otherwise."""
    try:
        req = urllib.request.Request(
            url, headers={"User-Agent": "web-to-knowledge/1.0"}
        )
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = resp.read()
        dest.write_bytes(data)
        return True
    except Exception as exc:
        print(f"[warn] image download failed: {url} ({exc})", file=sys.stderr)
        return False


def safe_image_name(url: str) -> str:
    """Derive a filename from an image URL, preserving the extension."""
    parsed = urllib.parse.urlparse(url)
    raw = Path(urllib.parse.unquote(parsed.path)).name or "image"
    # Collapse overly long / weird chars; keep extension.
    stem = Path(raw).stem
    suffix = Path(raw).suffix.lower()
    if suffix not in {".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp"}:
        suffix = ".img"
    return slugify(stem)[:60] + suffix


def collect_and_rewrite_images(
    md_text: str, base_url: str, assets_dir: Path
) -> tuple[str, int]:
    """Download ``![...](src)`` images to ``assets/`` and rewrite refs.

    Returns the rewritten Markdown and the number of images saved.
    """
    pattern = re.compile(r"!\[([^\]]*)\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
    seen: dict[str, str] = {}
    saved = 0

    def replace(match: re.Match) -> str:
        nonlocal saved
        alt = match.group(1)
        src = match.group(2)
        if src.startswith("data:"):
            return ""  # drop inline data URIs
        if src in seen:
            return f"![{alt}](assets/{seen[src]})"
        abs_url = urllib.parse.urljoin(base_url, src)
        name = safe_image_name(abs_url)
        # Avoid collisions with an incrementing counter.
        candidate = name
        n = 1
        while (assets_dir / candidate).exists():
            candidate = f"{Path(name).stem}-{n}{Path(name).suffix}"
            n += 1
        assets_dir.mkdir(parents=True, exist_ok=True)
        if download_image(abs_url, assets_dir / candidate):
            seen[src] = candidate
            saved += 1
            return f"![{alt}](assets/{candidate})"
        return f"![{alt}]({src})"  # keep original on failure

    return pattern.sub(replace, md_text), saved


def extract_page_title(soup, fallback: str) -> str:
    for selector in ["h1.firstHeading", "h1", "title"]:
        el = soup.select_one(selector)
        if el and el.get_text(strip=True):
            return el.get_text(strip=True)
    return fallback


# Common LaTeX control sequences that survive markdownify only when the page
# already served inline ``$...$`` text (rare) or when MathJax rendered to
# HTML without an accompanying ``<math>`` / ``<script type=math/tex>`` node.
# Seeing many of these with ``formula_count == 0`` strongly suggests the
# page uses JS-only rendering and our math preservation layer missed it.
_MATH_HINTS = re.compile(
    r"\\(?:log|frac|sum|int|prod|sqrt|alpha|beta|gamma|delta|sigma|tau|phi|psi|lambda|rho|Omega|Delta|partial|times|cdot|mapsto|rightarrow|Rightarrow|forall|exists|mathbb|mathcal|mathrm|operatorname|ldots|cdots)\b"
)


def diagnose_math_loss(md_text: str, formula_count: int) -> str | None:
    """Return a warning string when formulas appear to be silently lost.

    Heuristic: fetch.py preserved zero math blocks, but the body still
    contains many raw LaTeX control sequences. This is the
    pattern you get from a page whose math was rendered purely by
    client-side MathJax without a paired ``<math>`` or
    ``<script type=math/tex>`` element — our server-side HTML parsing
    cannot see the result, so nothing gets wrapped in ``$...$``.
    """
    if formula_count > 0:
        return None
    hits = len(_MATH_HINTS.findall(md_text))
    if hits < 5:
        return None
    return (
        f"{hits} LaTeX-like tokens (e.g. \\log, \\frac, \\sum) appear in the "
        "markdown but formula_count is 0 — the page likely renders math "
        "entirely client-side. Formulas will NOT round-trip as LaTeX; "
        "treat the extracted content.md as lossy for equations."
    )


def _heading_level(line: str) -> int:
    m = re.match(r"^(#{1,6}) \S", line)
    return len(m.group(1)) if m else 0


def _github_anchor(heading: str) -> str:
    slug = heading.strip().lower()
    slug = re.sub(r"[^\w\s-]", "", slug, flags=re.UNICODE)
    slug = re.sub(r"\s+", "-", slug)
    return slug.strip("-")


def _build_toc(md: str, max_entries: int = 30) -> list[str]:
    lines = ["- [Full content](content.md)"]
    count = 0
    for line in md.splitlines():
        m = re.match(r"^(##{1,2}) (.+)", line)
        if not m:
            continue
        level = len(m.group(1))
        title = m.group(2).strip()
        indent = "  " if level == 2 else "    "
        anchor = _github_anchor(title)
        lines.append(f"{indent}- [{title}](content.md#{anchor})")
        count += 1
        if count >= max_entries:
            break
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("url", help="URL of the page to fetch")
    parser.add_argument(
        "--output-dir",
        default="references",
        help="Parent directory; output goes under <output-dir>/<slug>/",
    )
    parser.add_argument("--slug", default=None, help="Override the auto-derived slug")
    args = parser.parse_args()

    # Lazy imports so --help works without deps installed.
    from bs4 import BeautifulSoup, NavigableString
    from markdownify import markdownify

    print(f"[info] Fetching {args.url}", file=sys.stderr)
    html_text, final_url = fetch_html(args.url)
    slug = args.slug or derive_slug(final_url)
    output_root = Path(args.output_dir).expanduser().resolve()
    output_dir = output_root / slug
    output_dir.mkdir(parents=True, exist_ok=True)

    soup = BeautifulSoup(html_text, "lxml")
    title = extract_page_title(soup, slug.replace("-", " ").title())

    article = find_main_content(soup)
    # Work on a fresh parsed copy to avoid mutating the original for title lookup.
    article_soup = BeautifulSoup(str(article), "lxml")
    strip_non_content(article_soup)
    formula_count = preserve_math_tags(article_soup, NavigableString)
    print(f"[info] Preserved {formula_count} math blocks", file=sys.stderr)

    md_text = markdownify(
        str(article_soup),
        heading_style="ATX",
        escape_asterisks=False,
        escape_underscores=False,
        strip=["a"] if False else None,  # keep links by default
    )
    md_text = re.sub(r"\n{3,}", "\n\n", md_text).strip() + "\n"

    assets_dir = output_dir / "assets"
    md_text, image_count = collect_and_rewrite_images(md_text, final_url, assets_dir)

    warning = diagnose_math_loss(md_text, formula_count)
    if warning:
        print(f"[warn] {warning}", file=sys.stderr)

    (output_dir / "content.md").write_text(md_text, encoding="utf-8")

    toc_lines = _build_toc(md_text)
    index = [
        "---",
        f"title: {json.dumps(title, ensure_ascii=False)}",
        f"source: {json.dumps(args.url, ensure_ascii=False)}",
        f"final_url: {json.dumps(final_url, ensure_ascii=False)}",
        f"slug: {slug}",
        f"assets: {image_count}",
        f"formulas: {formula_count}",
        "---",
        "",
        f"# {title}",
        "",
        "## Summary",
        "",
        "<!-- TODO: 3-5 sentence summary of what this page covers and why a coding",
        "     agent would consult it. Fill in after reading content.md. -->",
        "",
        "## Key concepts",
        "",
        "<!-- TODO: Bullet list of identifiers an agent would grep for. Each bullet",
        "     MUST start with a `backtick-quoted` identifier — this drives the",
        "     cross-document concept index shared with pdf-to-knowledge. Omit the",
        "     section if the page has no greppable terminology. -->",
        "",
        "## External links",
        "",
        "<!-- TODO: Optional — list related pages the current one links out to",
        "     (especially other Wikipedia / nLab articles an agent may want to",
        "     ingest next). Free-form; not a strict YAML schema. -->",
        "",
        "## Contents",
        "",
        *toc_lines,
        "",
    ]
    (output_dir / "INDEX.md").write_text("\n".join(index), encoding="utf-8")

    summary = {
        "slug": slug,
        "output_dir": str(output_dir),
        "index_path": str(output_dir / "INDEX.md"),
        "image_count": image_count,
        "formula_count": formula_count,
        "final_url": final_url,
        "math_loss_warning": warning,
    }
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
