#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Fetch one source into the math-extract corpus cache.

Usage:
    uv run .claude/skills/math-extract/scripts/ingest.py <arxiv-id | url | path>
                                                         [--slug SLUG]
                                                         [--cache-dir DIR]

Tries the ladder in order and stops at the first rung that yields text:

    1. arXiv LaTeX source (arxiv.org/e-print/<id>) -- the original text, with
       every formula exactly as the author wrote it.  Quotes taken from here
       need no further checking.
    2. arXiv HTML (arxiv.org/html/<id>) -- LaTeXML output.
    3. Any other URL, or a local .html/.txt/.tex file -- tags stripped.

    A PDF exits 5 without converting: the converter is a separate, slow, serial
    rung that is not wired up here yet.  See references/ingestion.md.  An arXiv
    *pdf* URL is not a PDF for this purpose -- the identifier is recovered from
    it and rung 1 fetches the LaTeX instead, which is strictly better.

Writes into <cache-dir>/<slug>/ (default cache-dir: references/, gitignored):

    raw/            the bytes as fetched, unmodified
    source.txt      concatenated plain text, one line per source line
    source.flat.txt the same text with each paragraph flattened onto one line

`source.flat.txt` is what the skill's quote check greps: a verbatim quotation
spanning a line break in the original matches there and nowhere else.

Prints a JSON summary to stdout and exits 0 on success.  Exit codes: 2 bad
arguments, 3 every rung failed, 4 fetched but effectively empty, 5 the source is
a PDF and needs the converter.
"""

from __future__ import annotations

import argparse
import gzip
import io
import json
import re
import sys
import tarfile
import unicodedata
import urllib.error
import urllib.request
from datetime import date
from html.parser import HTMLParser
from pathlib import Path

USER_AGENT = "math-extract/1.0 (Lean formalization research; contact via repository)"
TIMEOUT = 60
TEX_SUFFIXES = {".tex", ".ltx", ".bbl"}
MIN_USEFUL_CHARS = 400

# 2202.03357 / 2202.03357v2 / math/0604123 / math-ph/0411058v1
ARXIV_NEW = re.compile(r"(?<!\d)(\d{4}\.\d{4,5})(v\d+)?(?!\d)")
ARXIV_OLD = re.compile(r"([a-z-]+(?:\.[A-Z]{2})?/\d{7})(v\d+)?")


class TextExtractor(HTMLParser):
    """Collect visible text, dropping script/style and marking block ends."""

    SKIP = {"script", "style", "noscript", "head", "nav", "footer"}
    BLOCK = {"p", "div", "section", "article", "li", "tr", "br",
             "h1", "h2", "h3", "h4", "h5", "h6", "blockquote", "pre", "table"}

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self._skip_depth = 0

    def handle_starttag(self, tag: str, attrs: object) -> None:
        if tag in self.SKIP:
            self._skip_depth += 1
        elif tag in self.BLOCK:
            self.parts.append("\n")

    def handle_endtag(self, tag: str) -> None:
        if tag in self.SKIP and self._skip_depth:
            self._skip_depth -= 1
        elif tag in self.BLOCK:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        if not self._skip_depth:
            self.parts.append(data)

    def text(self) -> str:
        return "".join(self.parts)


def fetch(url: str) -> tuple[bytes, str]:
    """GET a URL, returning its body and content type."""
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=TIMEOUT) as response:
        return response.read(), response.headers.get("Content-Type", "")


def arxiv_id_of(target: str) -> str | None:
    """Recover a bare arXiv identifier from an id, an abs URL, or a pdf URL."""
    if "arxiv.org" in target or not target.startswith(("http://", "https://")):
        for pattern in (ARXIV_NEW, ARXIV_OLD):
            match = pattern.search(target)
            if match:
                return match.group(1)
    return None


def slugify(value: str, limit: int = 60) -> str:
    normalised = unicodedata.normalize("NFKD", value).encode("ascii", "ignore").decode()
    cleaned = re.sub(r"[^a-zA-Z0-9]+", "-", normalised).strip("-").lower()
    return (cleaned[:limit].rstrip("-")) or "source"


def derive_slug(target: str, arxiv_id: str | None) -> str:
    if arxiv_id:
        return "arxiv-" + arxiv_id.replace("/", "-")
    if target.startswith(("http://", "https://")):
        tail = target.rstrip("/").rsplit("/", 1)[-1]
        return slugify(tail or target)
    return slugify(Path(target).stem)


def flatten(text: str) -> str:
    """Collapse each blank-line-separated paragraph onto a single line.

    A quotation that runs across a line break in the source is one contiguous
    string here, which is what makes `grep -F` a usable check on it.
    """
    paragraphs = re.split(r"\n\s*\n", text)
    flattened = (" ".join(paragraph.split()) for paragraph in paragraphs)
    return "\n".join(p for p in flattened if p) + "\n"


def unpack_eprint(payload: bytes, raw_dir: Path) -> list[tuple[str, str]]:
    """Unpack an arXiv e-print into (name, text) pairs of its TeX members."""
    members: list[tuple[str, str]] = []
    try:
        with tarfile.open(fileobj=io.BytesIO(payload), mode="r:gz") as archive:
            for member in archive.getmembers():
                if not member.isfile():
                    continue
                if Path(member.name).suffix.lower() not in TEX_SUFFIXES:
                    continue
                handle = archive.extractfile(member)
                if handle is None:
                    continue
                body = handle.read().decode("utf-8", errors="replace")
                (raw_dir / Path(member.name).name).write_text(body, encoding="utf-8")
                members.append((member.name, body))
    except tarfile.ReadError:
        # A single-file submission arrives as bare gzip rather than a tarball.
        body = gzip.decompress(payload).decode("utf-8", errors="replace")
        (raw_dir / "main.tex").write_text(body, encoding="utf-8")
        members.append(("main.tex", body))
    # The file carrying \documentclass or \begin{document} comes first: it is
    # the one a reader would open, and ordering here orders source.txt.
    members.sort(key=lambda item: 0 if re.search(
        r"\\documentclass|\\begin\{document\}", item[1]) else 1)
    return members


def rung_arxiv_source(arxiv_id: str, raw_dir: Path) -> tuple[str, str] | None:
    payload, _ = fetch(f"https://arxiv.org/e-print/{arxiv_id}")
    if payload[:4] == b"%PDF":
        return None  # source withdrawn; the HTML rung may still work
    members = unpack_eprint(payload, raw_dir)
    if not members:
        return None
    joined = "\n\n".join(f"% ==== {name} ====\n{body}" for name, body in members)
    return joined, "arxiv-latex"


def rung_html(url: str, raw_dir: Path, stage: str) -> tuple[str, str] | None:
    payload, content_type = fetch(url)
    if payload[:4] == b"%PDF" or "application/pdf" in content_type:
        raise SystemExit(pdf_refusal(url))
    (raw_dir / "page.html").write_bytes(payload)
    parser = TextExtractor()
    parser.feed(payload.decode("utf-8", errors="replace"))
    return parser.text(), stage


def rung_local(path: Path, raw_dir: Path) -> tuple[str, str]:
    payload = path.read_bytes()
    if payload[:4] == b"%PDF":
        raise SystemExit(pdf_refusal(str(path)))
    (raw_dir / path.name).write_bytes(payload)
    body = payload.decode("utf-8", errors="replace")
    if path.suffix.lower() in {".html", ".htm"}:
        parser = TextExtractor()
        parser.feed(body)
        return parser.text(), "local-html"
    return body, "local-text"


def pdf_refusal(target: str) -> int:
    report({
        "ok": False,
        "reason": "pdf",
        "target": target,
        "message": "PDF sources need the converter rung, which is not wired up "
                   "here yet. See .claude/skills/math-extract/references/"
                   "ingestion.md, and record the source as not retrieved in "
                   "sources.md if it cannot be obtained another way.",
    })
    return 5


def report(payload: dict) -> None:
    json.dump(payload, sys.stdout, indent=2, ensure_ascii=False)
    sys.stdout.write("\n")


def main() -> int:
    parser = argparse.ArgumentParser(description="Fetch one source into the corpus cache.")
    parser.add_argument("target", help="arXiv id, URL, or local path")
    parser.add_argument("--slug", help="override the derived cache slug")
    parser.add_argument("--cache-dir", default="references", help="cache root (default: references)")
    args = parser.parse_args()

    target = args.target.strip()
    if not target:
        print("[error] empty target", file=sys.stderr)
        return 2

    arxiv_id = arxiv_id_of(target)
    slug = args.slug or derive_slug(target, arxiv_id)
    out_dir = Path(args.cache_dir) / slug
    raw_dir = out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)

    attempts: list[dict] = []
    result: tuple[str, str] | None = None

    local_path = Path(target)
    if local_path.exists():
        result = rung_local(local_path, raw_dir)
        attempts.append({"rung": result[1], "ok": True})
    else:
        ladder = []
        if arxiv_id:
            ladder.append(("arxiv-latex", lambda: rung_arxiv_source(arxiv_id, raw_dir)))
            ladder.append(("arxiv-html",
                           lambda: rung_html(f"https://arxiv.org/html/{arxiv_id}", raw_dir, "arxiv-html")))
        if target.startswith(("http://", "https://")):
            ladder.append(("url-html", lambda: rung_html(target, raw_dir, "url-html")))
        if not ladder:
            print(f"[error] cannot interpret target: {target}", file=sys.stderr)
            return 2

        for name, rung in ladder:
            try:
                result = rung()
            except urllib.error.HTTPError as error:
                attempts.append({"rung": name, "ok": False, "error": f"HTTP {error.code}"})
                continue
            except (urllib.error.URLError, OSError, gzip.BadGzipFile) as error:
                attempts.append({"rung": name, "ok": False, "error": str(error)})
                continue
            if result is None:
                attempts.append({"rung": name, "ok": False, "error": "no text at this rung"})
                continue
            attempts.append({"rung": name, "ok": True})
            break

    if result is None:
        report({"ok": False, "reason": "unreachable", "slug": slug,
                "stage_attempts": attempts,
                "message": "Every rung failed. Record the source as not retrieved "
                           "in sources.md, with what was tried, and cap every claim "
                           "resting on it at tier (d) — no locators."})
        return 3

    text, stage = result
    (out_dir / "source.txt").write_text(text, encoding="utf-8")
    flat = flatten(text)
    (out_dir / "source.flat.txt").write_text(flat, encoding="utf-8")

    summary = {
        "ok": True,
        "slug": slug,
        "stage": stage,
        "verbatim": stage == "arxiv-latex",
        "cache": str(out_dir),
        "quote_check_file": str(out_dir / "source.flat.txt"),
        "chars": len(text),
        "retrieved": date.today().isoformat(),
        "arxiv_id": arxiv_id,
        "stage_attempts": attempts,
    }
    if len(flat.strip()) < MIN_USEFUL_CHARS:
        summary["ok"] = False
        summary["reason"] = "empty"
        summary["message"] = ("Fetched, but there is almost no text. Treat the source "
                              "as not retrieved unless the cache says otherwise.")
        report(summary)
        return 4

    report(summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
