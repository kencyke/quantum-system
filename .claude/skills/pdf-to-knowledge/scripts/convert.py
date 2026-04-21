#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Convert a PDF into agent-friendly Markdown + image assets using MinerU.

Produces under ``<output-dir>/<slug>/``:

- ``INDEX.md``     Metadata, ToC, and scaffolded Summary / Key concepts / Bibliography
                   frontmatter sections that the caller (Claude) fills in after
                   reading the content.
- ``content.md``   Full Markdown (if total pages <= max-pages-per-section).
- ``sections/``    Split Markdown files (if total pages exceed the threshold and
                   the document has top-level ``#`` / ``## `` headings to split on).
- ``assets/``      Images referenced from the Markdown.

This script is a thin post-processor around the MinerU CLI. MinerU's
``pipeline`` backend runs entirely on CPU and, unlike Docling's formula VLM,
decodes mathematical formulas into LaTeX in a few minutes per paper. We gave
up on Docling in iteration-6 after its formula VLM crawled on CPU.

Usage:
    uv run convert.py <pdf-url-or-path> [--output-dir DIR] [--slug SLUG]
                                        [--max-pages-per-section N] [--ocr]
                                        [--keep-raw]

Prerequisite:
    ``mineru`` must be on PATH. One-off install:
        uv tool install "mineru[all]"
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
import urllib.request
from pathlib import Path


def slugify(text: str) -> str:
    """Lowercase, ASCII-friendly filesystem slug, capped at 60 chars."""
    text = text.lower().strip()
    text = re.sub(r"[^\w\s-]", "", text, flags=re.UNICODE)
    text = re.sub(r"[\s_-]+", "-", text)
    return text[:60].strip("-") or "document"


def derive_slug(source: str) -> str:
    """Pick a readable slug from a URL or local path."""
    m = re.search(r"arxiv\.org/(?:pdf|abs)/([\w.-]+?)(?:v\d+)?(?:\.pdf)?(?:[?#]|$)", source)
    if m:
        return f"arxiv-{m.group(1)}"
    if source.startswith(("http://", "https://")):
        parsed = urllib.parse.urlparse(source)
        basename = Path(parsed.path).stem or parsed.netloc
        return slugify(basename)
    return slugify(Path(source).stem)


def normalise_pdf_url(url: str) -> str:
    """Rewrite arxiv ``abs/`` URLs to their ``pdf/`` counterparts."""
    m = re.match(r"^(https?://arxiv\.org)/abs/([\w.-]+?)(?:v\d+)?/?$", url)
    if m:
        return f"{m.group(1)}/pdf/{m.group(2)}"
    return url


def download_pdf(url: str, dest: Path) -> None:
    req = urllib.request.Request(url, headers={"User-Agent": "pdf-to-knowledge/1.0"})
    with urllib.request.urlopen(req, timeout=120) as response, dest.open("wb") as out:
        while chunk := response.read(65536):
            out.write(chunk)


def _heading_level(line: str) -> int:
    """Return the Markdown heading level (1..6) of ``line``, or 0 if not a heading."""
    m = re.match(r"^(#{1,6}) \S", line)
    return len(m.group(1)) if m else 0


def split_markdown_by_top_headings(md: str) -> list[tuple[str, str]]:
    """Split Markdown at its top-most heading level. Returns ``[(title, body), ...]``."""
    has_h1 = any(_heading_level(line) == 1 for line in md.splitlines())
    split_level = 1 if has_h1 else 2

    sections: list[tuple[str, str]] = []
    current_title: str | None = None
    current_body: list[str] = []
    for line in md.splitlines(keepends=True):
        if _heading_level(line.rstrip("\n")) == split_level:
            if current_title is not None:
                sections.append((current_title, "".join(current_body)))
            current_title = line.lstrip("#").strip()
            current_body = [line]
        else:
            if current_title is None:
                current_title = "front-matter"
                current_body = []
            current_body.append(line)
    if current_title is not None:
        sections.append((current_title, "".join(current_body)))
    return sections


def extract_document_title(md: str, fallback: str) -> str:
    """Return the first heading (any level) in ``md``, or ``fallback``."""
    for line in md.splitlines():
        m = re.match(r"^#{1,6} (.+)", line)
        if m:
            return m.group(1).strip()
    return fallback


def _github_anchor(heading: str) -> str:
    """Compute a GitHub-style Markdown anchor for a heading."""
    slug = heading.strip().lower()
    slug = re.sub(r"[^\w\s-]", "", slug, flags=re.UNICODE)
    slug = re.sub(r"\s+", "-", slug)
    return slug.strip("-")


def extract_toc_headings(md: str, max_entries: int = 20) -> list[tuple[int, str]]:
    """Extract H2/H3 headings from ``md`` for navigation."""
    entries: list[tuple[int, str]] = []
    for line in md.splitlines():
        m = re.match(r"^(##{1,2}) (.+)", line)
        if m:
            level = len(m.group(1))
            title = m.group(2).strip()
            entries.append((level, title))
            if len(entries) >= max_entries:
                break
    return entries


def _flat_toc_for_content(md: str) -> list[str]:
    """Build ToC Markdown lines for the single-file ``content.md`` case."""
    lines = ["- [Full content](content.md)"]
    for level, title in extract_toc_headings(md):
        indent = "  " if level == 2 else "    "
        anchor = _github_anchor(title)
        lines.append(f"{indent}- [{title}](content.md#{anchor})")
    return lines


def _has_gpu() -> bool:
    """Detect an NVIDIA GPU via ``nvidia-smi``. Returns False on any error.

    MinerU's `hybrid-auto-engine` backend uses GPU when available and is
    dramatically faster than `pipeline` for the formula-recognition stage.
    Falls back to CPU `pipeline` cleanly when `nvidia-smi` is absent.
    """
    if shutil.which("nvidia-smi") is None:
        return False
    try:
        result = subprocess.run(
            ["nvidia-smi", "--query-gpu=name", "--format=csv,noheader"],
            capture_output=True,
            text=True,
            timeout=5,
        )
    except (subprocess.TimeoutExpired, OSError):
        return False
    return result.returncode == 0 and bool(result.stdout.strip())


def run_mineru(pdf_path: Path, output_base: Path, ocr: bool) -> tuple[Path, Path, Path]:
    """Invoke the MinerU CLI. Returns (md_path, images_dir, content_list_json)."""
    if shutil.which("mineru") is None:
        print(
            "[error] 'mineru' not found on PATH. Install with: "
            "uv tool install \"mineru[all]\"",
            file=sys.stderr,
        )
        sys.exit(3)

    method = "ocr" if ocr else "auto"
    # Auto-select backend: hybrid-auto-engine uses GPU when available and
    # can be >5x faster for formula-heavy papers; pipeline is CPU-only.
    backend = "hybrid-auto-engine" if _has_gpu() else "pipeline"
    print(f"[info] MinerU backend: {backend}", file=sys.stderr)
    cmd = [
        "mineru",
        "-p", str(pdf_path),
        "-o", str(output_base),
        "-b", backend,
        "-l", "en",
        "-m", method,
    ]
    print(f"[info] Running: {' '.join(cmd)}", file=sys.stderr)
    subprocess.run(cmd, check=True)

    name = pdf_path.stem
    auto_dir = output_base / name / "auto"
    md_path = auto_dir / f"{name}.md"
    images_dir = auto_dir / "images"
    content_list_json = auto_dir / f"{name}_content_list.json"
    if not md_path.is_file():
        print(f"[error] MinerU did not produce {md_path}", file=sys.stderr)
        sys.exit(4)
    return md_path, images_dir, content_list_json


def page_count_from_content_list(content_list_json: Path) -> int:
    """Read max ``page_idx`` from MinerU's content_list.json and return page count."""
    try:
        data = json.loads(content_list_json.read_text(encoding="utf-8"))
    except Exception:
        return 0
    max_idx = 0
    for item in data:
        idx = item.get("page_idx")
        if isinstance(idx, int):
            max_idx = max(max_idx, idx)
    return max_idx + 1 if data else 0


_IMAGE_REF = re.compile(r"!\[[^\]]*\]\(images/([^)]+)\)")


def rewrite_and_collect_image_refs(md: str) -> tuple[str, set[str]]:
    """Rewrite ``images/...`` references to ``assets/...`` and return referenced names."""
    referenced: set[str] = set()

    def _sub(match: re.Match) -> str:
        name = match.group(1)
        referenced.add(name)
        return match.group(0).replace("images/", "assets/", 1)

    return _IMAGE_REF.sub(_sub, md), referenced


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="PDF URL or local path")
    parser.add_argument(
        "--output-dir",
        default="references",
        help="Parent directory; output is placed under <output-dir>/<slug>/",
    )
    parser.add_argument("--slug", default=None, help="Override the auto-derived slug")
    parser.add_argument(
        "--max-pages-per-section",
        type=int,
        default=20,
        help="Split into sections/ if the document exceeds this many pages (default: 20)",
    )
    parser.add_argument(
        "--ocr",
        action="store_true",
        help="Use MinerU's OCR method (for scanned PDFs). Default is 'auto'.",
    )
    parser.add_argument(
        "--keep-raw",
        action="store_true",
        help=(
            "Keep MinerU's raw auxiliary outputs (middle.json, layout.pdf, span.pdf, "
            "model.json, content_list_v2.json) under <output-dir>/<slug>/mineru-raw/. "
            "Off by default — they are debugging artefacts unsuitable for agents."
        ),
    )
    args = parser.parse_args()

    source: str = args.source
    slug = args.slug or derive_slug(source)
    output_root = Path(args.output_dir).expanduser().resolve()
    output_dir = output_root / slug
    output_dir.mkdir(parents=True, exist_ok=True)
    assets_dir = output_dir / "assets"

    # Resolve input to a local path.
    if source.startswith(("http://", "https://")):
        fetch_url = normalise_pdf_url(source)
        tmpdir = Path(tempfile.mkdtemp(prefix="pdf-to-knowledge-"))
        pdf_path = tmpdir / f"{slug}.pdf"
        print(f"[info] Downloading {fetch_url}", file=sys.stderr)
        download_pdf(fetch_url, pdf_path)
    else:
        pdf_path = Path(source).expanduser().resolve()
        if not pdf_path.exists():
            print(f"[error] Not found: {pdf_path}", file=sys.stderr)
            return 2

    # Run MinerU into a fresh scratch directory so we fully own the layout.
    mineru_scratch = Path(tempfile.mkdtemp(prefix="mineru-"))
    md_path, images_src, content_list_json = run_mineru(
        pdf_path, mineru_scratch, ocr=args.ocr
    )

    page_count = page_count_from_content_list(content_list_json)
    print(f"[info] Pages: {page_count}", file=sys.stderr)

    md_text = md_path.read_text(encoding="utf-8")
    md_text, referenced_images = rewrite_and_collect_image_refs(md_text)

    # Copy referenced images only — MinerU occasionally extracts formula clips
    # that are not referenced from the Markdown; keeping them clutters agents.
    image_count = 0
    if referenced_images and images_src.is_dir():
        assets_dir.mkdir(exist_ok=True)
        for name in referenced_images:
            src = images_src / name
            if src.is_file():
                shutil.copy(src, assets_dir / name)
                image_count += 1

    # Optionally keep MinerU's raw auxiliary outputs for debugging.
    if args.keep_raw:
        raw_dir = output_dir / "mineru-raw"
        raw_dir.mkdir(exist_ok=True)
        for aux in md_path.parent.iterdir():
            if aux.name == md_path.name or aux == images_src:
                continue
            if aux.is_file():
                shutil.copy(aux, raw_dir / aux.name)

    # Clean up the scratch tree now that we have what we need.
    shutil.rmtree(mineru_scratch, ignore_errors=True)

    # Write content.md / sections/ based on page count.
    content_md = output_dir / "content.md"
    title = extract_document_title(md_text, slug.replace("-", " ").title())

    sectioned = False
    toc_lines: list[str] = []
    if page_count > args.max_pages_per_section:
        parts = split_markdown_by_top_headings(md_text)
        real_parts = [(t, b) for t, b in parts if t != "front-matter" or b.strip()]
        if len(real_parts) > 1:
            sections_dir = output_dir / "sections"
            sections_dir.mkdir(exist_ok=True)
            for i, (section_title, body) in enumerate(real_parts, start=1):
                sec_slug = slugify(section_title)
                sec_file = sections_dir / f"{i:02d}-{sec_slug}.md"
                sec_file.write_text(body, encoding="utf-8")
                toc_lines.append(f"- [{section_title}](sections/{sec_file.name})")
            sectioned = True
        else:
            content_md.write_text(md_text, encoding="utf-8")
            toc_lines.extend(_flat_toc_for_content(md_text))
    else:
        content_md.write_text(md_text, encoding="utf-8")
        toc_lines.extend(_flat_toc_for_content(md_text))

    # Scaffold INDEX.md (Claude fills Summary / Key concepts / authors /
    # bibliography / mathlib annotations per SKILL.md steps 4a-4f).
    index = [
        "---",
        f"title: {json.dumps(title, ensure_ascii=False)}",
        f"source: {json.dumps(source, ensure_ascii=False)}",
        f"pages: {page_count}",
        f"slug: {slug}",
        f"assets: {image_count}",
        "---",
        "",
        f"# {title}",
        "",
        "## Summary",
        "",
        "<!-- TODO: 3-5 sentence summary of what this document covers and why a",
        "     coding agent would consult it. Fill in after reading the content. -->",
        "",
        "## Key concepts",
        "",
        "<!-- TODO: Bullet list of identifiers an agent would grep for. Each bullet",
        "     MUST start with a `backtick-quoted` identifier — this drives the",
        "     cross-document concept index. Omit the section if no greppable",
        "     terminology exists (e.g. pure prose papers). -->",
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
        "page_count": page_count,
        "image_count": image_count,
        "sectioned": sectioned,
    }
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
