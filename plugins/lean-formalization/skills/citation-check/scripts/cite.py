# /// script
# requires-python = ">=3.12"
# dependencies = [
#   "defusedxml>=0.7.1",
#   "pillow>=13.0.0",  # for pypdfium2's to_pil()
#   "protego>=0.7.0",
#   "pydantic>=2.14.3",
#   "pypdfium2>=5.15.0",
#   "ruamel.yaml>=0.19.1",
# ]
# ///
"""Citation checks for the `citation-check` skill: canonical metadata, source text, and the ledger.

Run with `uv run <skill directory>/scripts/cite.py <command> ...` from inside the project; every command prints
JSON. The ledger defaults to `formalization.yaml` at the root of the git work tree containing the current
directory; a missing ledger is reported as status `no-ledger`.

Politeness (this is the one statement of it). The sources are five APIs — the arXiv API at export.arxiv.org (its
terms: one request per 3 s on one connection, over all of a user's machines together, which the locks below hold
on this machine only), the Crossref REST API public pool, for a DOI that Crossref does not hold, the DOI
proxy's registration-agency lookup at doi.org/doiRA/ and the DataCite REST API, and the OpenAlex API without a
key, for the copies of a work (`copies`) — and documents: arXiv PDFs from
arxiv.org, whose robots.txt allows them (export.arxiv.org's disallows everything), or any openly served URL.
Before any request outside the APIs, robots.txt is read (RFC 9309, kept a day) and the request is dropped when
the rules for `citation-check` or for `Claude-User` disallow it; a robots.txt answering 4xx, a refusal included,
sets no rules (RFC 9309, 2.3.1.3), and one that cannot be reached disallows everything (2.3.1.4). Requests
to one host go one at a time, across processes, at least an interval apart: the larger of `INTERVAL` and the
robots.txt `Crawl-delay` or `Request-rate`. A 408, a 429, a 5xx other than 501 and 505, or a dropped connection
is retried after its `Retry-After`, else after an exponential backoff with jitter that every process shares; a
wait past `WAIT_BUDGET` ends the run with status `retry-later`, and no run contacts that host before then. A
refusal (401, 403, 410) is not retried, and counts as a failure of its host. Redirects are followed by hand, at
most 5, each hop checked as the first: http(s) only, to public addresses only. Every answer is validated
(pydantic models; XML with no DTD) before it is used or cached. `fetch-text --file` reads a copy that the user
obtained and saved, and makes no request.

The cache is `$XDG_CACHE_HOME/lean-formalization-citation-check` (`~/.cache/…` when unset). One directory for
every entry point (the skill's verifier, Claude in a session, a shell), because its `state/` (the locks, and per
host the last request and the backoff) is what holds the rules above across processes; a per-plugin data
directory would split that from the shell, and this script also runs as a project skill, without a plugin. It
keeps a validated answer for 7 days after its fetch and a site's robots.txt answer for one day. It keeps no
error, refusal or 404, nor an answer that finds nothing: a search with no candidate that could be the claimed
work, a DOI that doi.org does not know, a page with no document text. A `lookup` whose status would be `mismatch` or `not-found`
after reading an answer from the cache asks the source again, so that a negative answer always comes from the
source. Past 1 GiB the oldest answers go first. A command that fetches first deletes what has expired. To empty the
cache, delete the directory — before uninstalling the plugin, since nothing else removes it. The script needs a
POSIX system (Linux, macOS, WSL) for its file locks, and a Claude Code sandbox must allow writes to the cache
directory (`sandbox.filesystem.allowWrite`).
"""

import argparse
import datetime
import difflib
import email.utils
import hashlib
import html.parser
import http.client
import io
import ipaddress
import json
import math
import os
import random
import re
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import traceback
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import Annotated, Any, Literal, Self

try:
    import fcntl
except ImportError:  # Windows: no file locks, so no shared cache and no polite interval
    print(json.dumps({"status": "error", "error": "cite.py needs a POSIX system (Linux, macOS, WSL): no fcntl"}))
    sys.exit(2)

import pypdfium2 as pdfium
from defusedxml import DefusedXmlException
from defusedxml import ElementTree as SafeET
from protego import Protego
from pydantic import BaseModel, BeforeValidator, ConfigDict, Field, StringConstraints, ValidationError
from ruamel.yaml import YAML
from ruamel.yaml.comments import CommentedMap, CommentedSeq
from ruamel.yaml.scalarstring import LiteralScalarString
from ruamel.yaml.util import load_yaml_guess_indent

LEDGER_NAME = "formalization.yaml"
# The product token, and a page that says what the script is and whose it is (Crossref asks for both; DataCite asks
# frequent clients for a `mailto:` as well, and this script asks it only for DOIs that Crossref does not hold).
USER_AGENT = "citation-check (+https://github.com/kencyke/quantum-system/tree/main/plugins/lean-formalization)"
# The robots.txt rules a request obeys: this script's, and those for fetches a user asks Claude for.
ROBOT_TOKENS = ("citation-check", "Claude-User")
# The APIs (host, path prefix): their terms govern them, not robots.txt.
API = {
    "export.arxiv.org": "/api/",
    "api.crossref.org": "/",
    "doi.org": "/doiRA/",
    "api.datacite.org": "/dois/",
    "api.openalex.org": "/works/",
}
# The largest answer taken, by kind, and the seconds one answer may take in all (a socket timeout bounds one read).
MAX_BODY = {"api": 4 * 2**20, "robots": 512 * 2**10, "document": 200 * 2**20}
DEADLINE = 300.0
# Seconds between requests to one host at least: the arXiv API's terms set 3 s, arxiv.org's robots.txt 15 s;
# DataCite's firewall allows 3000 requests in 5 minutes, and doi.org states no limit. OpenAlex allows 10 requests
# per second without a key and a daily budget, and answers a 429 past either, with `Retry-After` for the daily one
# (https://help.openalex.org/how-to-use-the-api/rate-limits-and-authentication, read 2026-11-08); its data is CC0.
INTERVAL = {
    "export.arxiv.org": 3.0,
    "arxiv.org": 15.0,
    "api.crossref.org": 1.0,
    "api.datacite.org": 1.0,
    "api.openalex.org": 1.0,
}
DEFAULT_INTERVAL = 1.0
# Tries of one request; seconds one run may wait in all (under the Bash tool's 120 s default); caps on a backoff.
ATTEMPTS = 3
WAIT_BUDGET = 90.0
MAX_BACKOFF = 3600.0
MAX_BLOCK = 7 * 86400.0
MAX_REDIRECTS = 5
RETRY = {408, 429, *range(500, 600)} - {501, 505}
REFUSAL = {401, 403, 410}
# The answers that show one URL cannot be read here, by `fetch-text`'s reason; any other is an error, not a verdict.
UNREADABLE = {401: "refused", 403: "refused", 451: "refused", 404: "not found", 410: "not found"}
REDIRECT = {301, 302, 303, 307, 308}
# Seconds a cache entry stays, by kind (a temporary file a write left behind is `temp`), and the answers' total size.
TTL = {"answer": 7 * 86400, "robots": 86400, "temp": 86400}
MAX_CACHE = 2**30
# Pages of a PDF taken, the scale pages are rendered at, and the pixels of one rendered page.
MAX_PAGES = 2000
SCALE = 2.5
MAX_PIXELS = 40_000_000
ATOM = {"a": "http://www.w3.org/2005/Atom", "arxiv": "http://arxiv.org/schemas/atom"}
ARXIV_ID = r"(?:\d{4}\.\d{4,5}|[a-z]+(?:-[a-z]+)?(?:\.[A-Za-z-]+)?/\d{7})(?:v\d+)?"
# What a fetch can raise besides an HTTP status: DNS and connection errors, a read timeout, a short body.
NETWORK_ERRORS = (urllib.error.URLError, TimeoutError, ConnectionError, http.client.HTTPException)

type Record = dict[str, Any]


def repo_root() -> Path:
    """The root of the git work tree containing the current directory, else the current directory."""
    try:
        out = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return Path.cwd()
    return Path(out.stdout.strip())


# ---------- answers and their failures ----------


@dataclass
class Reply:
    """One answer, fetched now or read from the cache; `final` is the URL it came from after redirects."""

    url: str
    status: int
    type: str
    body: bytes
    fetched_at: float
    cached: bool
    final: str = ""


def report(replies: list[Reply]) -> Record:
    """`cached` if any answer came from the cache, `fetched_at` (ISO 8601, UTC; its first ten characters are the
    date) of the oldest one, and `read_at` where the one answer ended after redirects; nothing before a request."""
    if not replies:
        return {}
    oldest = min(replies, key=lambda r: r.fetched_at)
    when = datetime.datetime.fromtimestamp(oldest.fetched_at, datetime.UTC).isoformat(timespec="seconds")
    out: Record = {"cached": any(r.cached for r in replies), "fetched_at": when}
    if len(replies) == 1 and replies[0].final and replies[0].final != replies[0].url:
        out["read_at"] = replies[0].final
    return out


class Http(Exception):
    def __init__(self, reply: Reply):
        super().__init__(f"HTTP {reply.status} for {reply.url}")
        self.code, self.reply = reply.status, reply


class RetryLater(Exception):
    """A host not to be contacted before `until` (epoch seconds): its backoff, a wait past the run's budget, or a
    held lock."""

    def __init__(self, host: str, until: float, reason: str):
        super().__init__(f"{host}: {reason}")
        self.host, self.until, self.reason = host, until, reason

    def report(self) -> Record:
        at = datetime.datetime.fromtimestamp(self.until, datetime.UTC).isoformat(timespec="seconds")
        wait = max(0, math.ceil(self.until - time.time()))
        return {"status": "retry-later", "host": self.host, "reason": self.reason, "retry_after": wait, "retry_at": at}


class Disallowed(Exception):
    """A request the site's robots.txt rules out."""

    def __init__(self, url: str, reason: str):
        super().__init__(f"{reason} disallows {url}")
        self.reason = reason


class Malformed(Exception):
    """An answer not in its source's format: an outage page, a bot check, a broken PDF."""


class Unsafe(ValueError):
    """A URL this script does not fetch: not http(s), or to an address that is not public."""


class Oversize(http.client.HTTPException):
    """An answer refused for its size or the time it takes."""


class NoLedger(Exception):
    pass


class Refused(Exception):
    """A request carried out in no part: a record that lacks a field, a title the ledger lists under another id."""


class Registered(Exception):
    """A DOI that exists, with a registration agency whose metadata this script does not read."""

    def __init__(self, doi: str, agency: str):
        super().__init__(f"{doi} is registered with {agency}")
        self.doi, self.agency = doi, agency

    def report(self) -> Record:
        return {"status": "registered", "agency": self.agency, "url": f"https://doi.org/{self.doi}"}


FAILURES = (RetryLater, Disallowed, Malformed, Unsafe, *NETWORK_ERRORS)


def failure(e: BaseException) -> Record:
    """The JSON status of a fetch that failed other than by an HTTP status."""
    if isinstance(e, RetryLater):
        return e.report()
    if isinstance(e, Disallowed):
        return {"status": "inaccessible", "reason": e.reason}
    if isinstance(e, Malformed):
        return {"status": "error", "reason": "malformed", "error": str(e)}
    return {"status": "error", "error": str(e)}


# ---------- validated answers ----------


class Answer(BaseModel):
    model_config = ConfigDict(extra="ignore", frozen=True, populate_by_name=True)


def _count(v: Any) -> int | None:
    return int(v) if isinstance(v, str) and v.strip().isdigit() else None


def _retry_after(v: Any) -> float | None:
    """`Retry-After` in seconds from now, from delta-seconds or an HTTP-date."""
    if not isinstance(v, str):
        return None
    if v.strip().isdigit():
        return float(v)
    try:
        when = email.utils.parsedate_to_datetime(v)
    except (TypeError, ValueError, IndexError):
        return None
    if when.tzinfo is None:
        when = when.replace(tzinfo=datetime.UTC)
    return max(0.0, when.timestamp() - time.time())


class Headers(Answer):
    """The headers this script acts on; a value it cannot read counts as absent."""

    content_type: str = Field("", alias="content-type")
    content_length: Annotated[int | None, BeforeValidator(_count)] = Field(None, alias="content-length")
    location: str | None = None
    retry_after: Annotated[float | None, BeforeValidator(_retry_after)] = Field(None, alias="retry-after")

    @classmethod
    def of(cls, msg: Any) -> Self:
        return cls.model_validate({k.lower(): v for k, v in (msg.items() if msg is not None else [])})


class CacheMeta(Answer):
    url: str
    final: str = ""
    status: int
    type: str = ""
    fetched_at: float
    expires_at: float


class HostState(Answer):
    """What every run knows of one host: its last request, its backoff, and the interval its robots.txt asks for."""

    model_config = ConfigDict(frozen=False)
    last_request: float = 0.0
    blocked_until: float = 0.0
    failures: int = Field(0, ge=0)
    robots_delay: float = Field(0.0, ge=0)


class RobotsFile(Answer):
    text: Annotated[str, StringConstraints(max_length=MAX_BODY["robots"])]


class ArxivEntry(Answer):
    id: Annotated[str, StringConstraints(pattern=rf"^https?://arxiv\.org/abs/{ARXIV_ID}$")]
    title: Annotated[str, StringConstraints(min_length=1)]
    authors: list[Annotated[str, StringConstraints(min_length=1)]]
    published: datetime.datetime
    updated: datetime.datetime | None = None
    journal_ref: str | None = None
    doi: str | None = None

    def record(self) -> Record:
        return {
            "source": "arxiv",
            "id": "arXiv:" + re.sub(r"^https?://arxiv\.org/abs/", "", self.id),
            "title": self.title,
            "authors": self.authors,
            "year": self.published.year,
            "updated": self.updated.isoformat() if self.updated else None,
            "journal_ref": self.journal_ref,
            "doi": self.doi,
            "url": self.id,
        }


class CrossrefAuthor(Answer):
    given: str | None = None
    family: str | None = None
    name: str | None = None

    def full(self) -> str:
        return " ".join(filter(None, [self.given, self.family])) or self.name or ""


class CrossrefDate(Answer):
    date_parts: list[list[int | None]] = Field(default_factory=list, alias="date-parts")

    def iso(self) -> str | None:
        """`YYYY`, `YYYY-MM` or `YYYY-MM-DD`, as far as the parts go."""
        parts = [p for p in (self.date_parts[0] if self.date_parts else []) if p is not None]
        return "-".join(f"{p:02d}" if i else str(p) for i, p in enumerate(parts[:3])) or None


class CrossrefUpdate(Answer):
    """One notice that updates a work — a retraction, a correction, an expression of concern. Crossref's
    documentation (https://www.crossref.org/documentation/retrieve-metadata/retraction-watch/) describes the notice's
    own record, whose `update-to` names the work; the work's record lists its notices the other way round, under
    `updated-by`, with the same fields: `type` and `label`, the notice's `DOI`, `updated`, and `source`,
    `publisher` or `retraction-watch` (the same notice may be listed once from each)."""

    doi: str = Field(alias="DOI")
    type: str = ""
    label: str = ""
    source: str = ""
    updated: CrossrefDate | None = None

    def record(self) -> Record:
        date = self.updated.iso() if self.updated else None
        return {"type": self.type, "label": self.label, "doi": self.doi, "date": date, "source": self.source}


class CrossrefWork(Answer):
    doi: Annotated[str, StringConstraints(pattern=r"^10\.")] = Field(alias="DOI")
    title: list[str] = Field(default_factory=list)
    author: list[CrossrefAuthor] = Field(default_factory=list)
    editor: list[CrossrefAuthor] = Field(default_factory=list)
    issued: CrossrefDate | None = None
    container_title: list[str] = Field(default_factory=list, alias="container-title")
    volume: str | None = None
    page: str | None = None
    type: str | None = None
    url: str | None = Field(None, alias="URL")
    updated_by: list[CrossrefUpdate] = Field(default_factory=list, alias="updated-by")

    def record(self) -> Record:
        parts = self.issued.date_parts if self.issued else []
        return {
            "source": "crossref",
            "id": "doi:" + self.doi,
            "title": " ".join(self.title[0].split()) if self.title else "",
            "authors": [a.full() for a in self.author],
            "editors": [a.full() for a in self.editor],
            "year": parts[0][0] if parts and parts[0] else None,
            "container": self.container_title[0] if self.container_title else None,
            "volume": self.volume,
            "page": self.page,
            "type": self.type,
            "url": self.url,
            # The notices Crossref knows of (`updated-by`): only a Crossref record carries this, and an empty
            # list says that Crossref lists none, not that there is none.
            "updates": [u.record() for u in self.updated_by],
        }


class CrossrefList(Answer):
    items: list[CrossrefWork] = Field(default_factory=list)


class CrossrefWorkAnswer(Answer):
    status: Literal["ok"]
    message_type: Literal["work"] = Field(alias="message-type")
    message: CrossrefWork


class CrossrefListAnswer(Answer):
    status: Literal["ok"]
    message_type: Literal["work-list"] = Field(alias="message-type")
    message: CrossrefList


class DoiAgency(Answer):
    """One DOI's answer from doi.org/doiRA/: its registration agency, else a status such as `DOI does not exist`."""

    doi: str = Field(alias="DOI")
    ra: str | None = Field(None, alias="RA")
    status: str | None = None


class DataciteName(Answer):
    name: str | None = None
    given_name: str | None = Field(None, alias="givenName")
    family_name: str | None = Field(None, alias="familyName")
    contributor_type: str | None = Field(None, alias="contributorType")

    def full(self) -> str:
        return " ".join(filter(None, [self.given_name, self.family_name])) or self.name or ""


class DataciteTitle(Answer):
    title: str = ""
    title_type: str | None = Field(None, alias="titleType")


class DataciteContainer(Answer):
    title: str | None = None


class DataciteTypes(Answer):
    resource_type_general: str | None = Field(None, alias="resourceTypeGeneral")


def _name(v: Any) -> Any:
    """DataCite's publisher: a string, or an object with a name."""
    return v.get("name") if isinstance(v, dict) else v


class DataciteAttributes(Answer):
    doi: Annotated[str, StringConstraints(pattern=r"^10\.")]
    titles: list[DataciteTitle] = Field(default_factory=list)
    creators: list[DataciteName] = Field(default_factory=list)
    contributors: list[DataciteName] = Field(default_factory=list)
    publication_year: int | None = Field(None, alias="publicationYear")
    publisher: Annotated[str | None, BeforeValidator(_name)] = None
    container: DataciteContainer | None = None
    types: DataciteTypes | None = None
    url: str | None = None

    def record(self) -> Record:
        main = [t.title for t in self.titles if not t.title_type] or [t.title for t in self.titles]
        return {
            "source": "datacite",
            "id": "doi:" + self.doi,
            "title": " ".join(main[0].split()) if main else "",
            "authors": [c.full() for c in self.creators],
            "editors": [c.full() for c in self.contributors if c.contributor_type == "Editor"],
            "year": self.publication_year,
            "container": (self.container.title if self.container else None) or self.publisher,
            "type": self.types.resource_type_general if self.types else None,
            "url": self.url,
        }


class DataciteData(Answer):
    type: Literal["dois"]
    attributes: DataciteAttributes


class DataciteAnswer(Answer):
    data: DataciteData


class OpenAlexSource(Answer):
    display_name: str | None = None
    type: str | None = None


class OpenAlexLocation(Answer):
    """One copy of a work (https://help.openalex.org/data/locations/): where it is read, its version — `publishedVersion`,
    `acceptedVersion` or `submittedVersion`, as OpenAlex names them — and its licence, each null when unknown."""

    is_oa: bool | None = None
    landing_page_url: str | None = None
    pdf_url: str | None = None
    version: str | None = None
    license: str | None = None
    source: OpenAlexSource | None = None

    def record(self) -> Record:
        return {
            "landing_page_url": self.landing_page_url,
            "pdf_url": self.pdf_url,
            "version": self.version,
            "license": self.license,
            "is_oa": self.is_oa,
            "source": self.source.display_name if self.source else None,
            "source_type": self.source.type if self.source else None,
        }


# The fields of a work this script reads (https://help.openalex.org/data/works/attributes/; `select` takes top-level
# fields only).
OPENALEX_FIELDS = "id,doi,title,publication_year,is_retracted,updated_date,best_oa_location,locations"


class OpenAlexWork(Answer):
    id: Annotated[str, StringConstraints(pattern=r"^https://openalex\.org/W\d+$")]
    doi: str | None = None
    title: str | None = None
    publication_year: int | None = None
    is_retracted: bool | None = None
    updated_date: str | None = None
    best_oa_location: OpenAlexLocation | None = None
    locations: list[OpenAlexLocation] = Field(default_factory=list)

    def record(self) -> Record:
        return {
            "source": "openalex",
            "id": self.id,
            "doi": self.doi,
            "title": " ".join(self.title.split()) if self.title else "",
            "year": self.publication_year,
            # Per OpenAlex, from the Retraction Watch database; `updated_date` is when OpenAlex's record last changed.
            "is_retracted": self.is_retracted,
            "updated_date": self.updated_date,
            "best": self.best_oa_location.record() if self.best_oa_location else None,
            "copies": [loc.record() for loc in self.locations],
        }


@dataclass
class Document:
    """A fetched document: its kind, its text, and for a PDF the parsed file (for rendering pages)."""

    kind: Literal["pdf", "html", "text"]
    text: str
    pdf: pdfium.PdfDocument | None = None

    @property
    def usable(self) -> bool:
        """A bot check or an empty landing page answers 200 with no document in it; a scan without text is still
        one. A page with text may still be a landing page (an abstract, a table of contents), which only its
        reader can tell from the document."""
        return self.kind == "pdf" or len(self.text.split()) >= 200


def validated[M: BaseModel](model: type[M], data: bytes | Record, where: str) -> M:
    """`data` (JSON, or fields already parsed) as a `model`; else `Malformed`, naming `where` it came from."""
    try:
        return model.model_validate_json(data) if isinstance(data, bytes) else model.model_validate(data)
    except ValidationError as e:
        first = e.errors()[0]
        loc = ".".join(map(str, first["loc"])) or "<root>"
        raise Malformed(f"{where}: not in the source's format ({loc}: {first['msg']})") from e


# ---------- cache ----------


@dataclass
class Cache:
    """The cache directory, the answers this run used, what it has spent of `WAIT_BUDGET`, and whether its answers
    must come from the source (`fresh`) rather than the cache."""

    dir: Path
    replies: list[Reply] = field(default_factory=list)
    waited: float = 0.0
    fresh: bool = False


def cache_path() -> Path:
    xdg = os.environ.get("XDG_CACHE_HOME")
    return (Path(xdg) if xdg else Path.home() / ".cache") / "lean-formalization-citation-check"


def cache_dir(cache: Cache) -> Path:
    cache.dir.mkdir(mode=0o700, parents=True, exist_ok=True)
    return cache.dir


def state_dir(cache: Path) -> Path:
    """The locks and the hosts' state."""
    folder = cache / "state"
    folder.mkdir(mode=0o700, parents=True, exist_ok=True)
    return folder


def entry_key(url: str) -> str:
    return hashlib.sha256(url.encode()).hexdigest()


def is_html(body: bytes, ctype: str) -> bool:
    return "html" in ctype or body.lstrip()[:1] == b"<"


ENTRY_NAME = re.compile(r"[0-9a-f]{64}")


def entry_path(cache: Path, url: str) -> Path:
    return cache / entry_key(url)


def read_head(path: Path) -> CacheMeta | None:
    """The metadata on the first line of the entry at `path`, else None (no entry, or an unreadable one)."""
    try:
        with path.open("rb") as f:
            return CacheMeta.model_validate_json(f.readline())
    except (OSError, ValidationError):
        return None


def sweep(cache: Path) -> None:
    """Delete expired entries, what an interrupted write left (a temporary file a day old), and the oldest answers
    past `MAX_CACHE`."""
    now = time.time()
    try:
        files = [p for p in cache.iterdir() if p.is_file()]
        files += [p for p in (cache / "state").glob(".*") if p.is_file()]
    except OSError:
        return
    kept: list[tuple[float, Path, int]] = []
    for p in files:
        try:
            if p.name.startswith("."):
                if now - p.stat().st_mtime > TTL["temp"]:
                    p.unlink(missing_ok=True)
            elif ENTRY_NAME.fullmatch(p.name):
                meta = read_head(p)
                if meta and meta.expires_at > now:
                    kept.append((meta.fetched_at, p, p.stat().st_size))
                else:
                    p.unlink(missing_ok=True)
        except OSError:
            continue
    size = sum(s for *_, s in kept)
    for _, p, s in sorted(kept):
        if size <= MAX_CACHE:
            break
        p.unlink(missing_ok=True)
        size -= s


def drop_entry(cache: Path, url: str) -> None:
    entry_path(cache, url).unlink(missing_ok=True)


def read_entry(url: str, cache: Path) -> Reply | None:
    """The unexpired cached answer for `url`, else None (no entry, an unreadable one, or one a peer's sweep took)."""
    try:
        head, _, body = entry_path(cache, url).read_bytes().partition(b"\n")
        meta = CacheMeta.model_validate_json(head)
    except (OSError, ValidationError):
        return None
    if meta.url != url or meta.expires_at <= time.time():
        return None
    return Reply(url, meta.status, meta.type, body, meta.fetched_at, True, meta.final)


def write_entry(cache: Path, reply: Reply, ttl: float) -> None:
    """Cache `reply` for `ttl` seconds in one file, its metadata on the first line and its body after it, so that
    an entry is whole or absent."""
    meta = CacheMeta(
        url=reply.url,
        final=reply.final,
        status=reply.status,
        type=reply.type,
        fetched_at=reply.fetched_at,
        expires_at=reply.fetched_at + ttl,
    )
    write_atomic(entry_path(cache, reply.url), meta.model_dump_json().encode() + b"\n" + reply.body)


# ---------- hosts: one connection, the interval, the backoff ----------


def host_key(host: str) -> str:
    """One name per site, for its lock and its state: arXiv's mirrors are arxiv.org, as its robots.txt says."""
    h = host.lower().rstrip(".")
    try:
        h = h.encode("idna").decode("ascii")
    except UnicodeError:
        pass
    h = h.removeprefix("www.")
    if h.endswith(".arxiv.org") and h != "export.arxiv.org":
        h = "arxiv.org"
    return re.sub(r"[^a-z0-9.:_-]", "_", h) or "_"


def load_state(path: Path) -> HostState:
    try:
        return HostState.model_validate_json(path.read_bytes())
    except FileNotFoundError:
        return HostState()
    except (OSError, ValidationError):  # unreadable: as if the host had just been contacted
        return HostState(last_request=time.time())


def backoff(failures: int, retry_after: float | None, interval: float) -> float:
    """Seconds before the next request: `Retry-After` when given, else exponential in `failures` with equal jitter;
    never less than `interval`."""
    if retry_after is not None:
        return min(max(retry_after, interval), MAX_BLOCK)
    d = min(MAX_BACKOFF, max(interval, 1.0) * 2.0 ** min(failures, 30))
    return max(interval, d / 2 + random.uniform(0, d / 2))


@dataclass
class Slot:
    key: str
    file: Path
    state: HostState
    interval: float

    def succeed(self) -> None:
        self.state.failures, self.state.blocked_until = 0, 0.0

    def fail(self, retry_after: float | None) -> None:
        self.state.failures += 1
        self.state.blocked_until = time.time() + backoff(self.state.failures, retry_after, self.interval)

    def save(self) -> None:
        write_atomic(self.file, self.state.model_dump_json())


def pause(cache: Cache, key: str, seconds: float, until: float, reason: str) -> None:
    """Sleep `seconds` out of the run's `WAIT_BUDGET`, or end the run with `retry-later` when it does not cover them."""
    if cache.waited + seconds > WAIT_BUDGET:
        raise RetryLater(key, until, reason)
    time.sleep(seconds)
    cache.waited += seconds


@contextmanager
def host_state(cache: Cache, host: str, robots_delay: float | None = None) -> Iterator[Slot]:
    """Hold `host`'s lock and its state, saved on release; `robots_delay` is what its robots.txt now asks for."""
    key = host_key(host)
    folder = state_dir(cache.dir)
    with (folder / f"{key}.lock").open("a+") as f:
        base = INTERVAL.get(key, DEFAULT_INTERVAL)
        while True:
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                pause(cache, key, 0.25, time.time() + base, "another run holds the host")
        slot = Slot(key, folder / f"{key}.json", load_state(folder / f"{key}.json"), base)
        if robots_delay is not None:
            slot.state.robots_delay = robots_delay
        slot.interval = max(base, slot.state.robots_delay)
        try:
            yield slot
        finally:
            slot.save()


@contextmanager
def host_slot(cache: Cache, host: str, robots_delay: float | None = None) -> Iterator[Slot]:
    """`host_state` for one request, sent outside the host's backoff and an interval after its last request. The
    request is written down before it goes out, so that a run killed in it still counts."""
    with host_state(cache, host, robots_delay) as slot:
        state, now = slot.state, time.time()
        # A clock set back cannot stretch the interval, nor a stored backoff pass `MAX_BLOCK`.
        blocked = min(state.blocked_until, now + MAX_BLOCK)
        until = max(blocked, min(state.last_request, now) + slot.interval)
        if until > now:
            pause(cache, slot.key, until - now, until, "backoff" if blocked >= until else "interval")
        state.last_request = time.time()
        slot.save()
        try:
            yield slot
        finally:
            state.last_request = max(state.last_request, time.time())


# ---------- the network ----------


def read_body(r: Any, limit: int, truncate: bool = False) -> bytes:
    """The body of an answer: past `limit` bytes cut there (`truncate`) or refused; refused past `DEADLINE` s."""
    deadline, chunks, size = time.monotonic() + DEADLINE, [], 0
    while chunk := r.read1(1 << 16):
        if size + len(chunk) > limit:
            if truncate:
                chunks.append(chunk[: limit - size])
                break
            raise Oversize(f"answer larger than {limit:,} bytes")
        size += len(chunk)
        if time.monotonic() > deadline:
            raise Oversize(f"answer not complete in {DEADLINE:.0f} s")
        chunks.append(chunk)
    return b"".join(chunks)


class _Manual(urllib.request.HTTPRedirectHandler):
    """Redirects are not followed here: `fetch` checks each hop as it checks the first."""

    def redirect_request(self, *args: Any, **kwargs: Any) -> None:
        return None


def _opener() -> urllib.request.OpenerDirector:
    """http(s) only (urllib's default opener also serves file:, ftp: and data:), with no redirect followed."""
    opener = urllib.request.OpenerDirector()
    for handler in (
        urllib.request.UnknownHandler(),
        urllib.request.ProxyHandler(),
        urllib.request.HTTPHandler(),
        urllib.request.HTTPSHandler(),
        urllib.request.HTTPDefaultErrorHandler(),
        _Manual(),
        urllib.request.HTTPErrorProcessor(),
    ):
        opener.add_handler(handler)
    return opener


OPENER = _opener()


def open_url(url: str, limit: int, truncate: bool = False) -> tuple[int, Headers, bytes]:
    """One GET: the status, the headers and, for a 2xx, the body."""
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with OPENER.open(req, timeout=60) as r:
            headers = Headers.of(r.headers)
            if not truncate and (headers.content_length or 0) > limit:
                raise Oversize(f"answer larger than {limit:,} bytes")
            return r.status, headers, read_body(r, limit, truncate)
    except urllib.error.HTTPError as e:
        try:
            return e.code, Headers.of(e.headers), b""
        finally:
            e.close()


def addresses(host: str, port: int) -> list[str]:
    return [info[4][0] for info in socket.getaddrinfo(host, port, type=socket.SOCK_STREAM)]


def check_url(url: str) -> urllib.parse.SplitResult:
    """`url` split, once it is http(s) to a host whose every address is public; behind a proxy that looks names up
    itself, a name this machine cannot resolve is left to the proxy. The name is looked up again to connect, so a
    name whose answer changes in between (DNS rebinding) is not caught."""
    parts = urllib.parse.urlsplit(url)
    if parts.scheme not in ("http", "https") or not parts.hostname:
        raise Unsafe(f"not an http(s) URL: {url}")
    if parts.username is not None or parts.password is not None:
        raise Unsafe(f"credentials in the URL: {url}")
    port = parts.port or (443 if parts.scheme == "https" else 80)
    proxied = bool(urllib.request.getproxies().get(parts.scheme)) and not urllib.request.proxy_bypass(parts.hostname)
    try:
        found = addresses(parts.hostname, port)
    except OSError as e:
        if proxied:
            return parts
        raise urllib.error.URLError(e) from e
    private = [a for a in found if not ipaddress.ip_address(a.split("%")[0]).is_global]
    if private:
        raise Unsafe(f"{parts.hostname} resolves to {private[0]}, which is not a public address")
    return parts


def is_api(parts: urllib.parse.SplitResult) -> bool:
    prefix = API.get((parts.hostname or "").lower())
    return prefix is not None and parts.path.startswith(prefix)


def transient(e: BaseException) -> bool:
    """A dropped or timed-out connection, which is retried; a name that does not resolve is not."""
    reason = e.reason if isinstance(e, urllib.error.URLError) else e
    return isinstance(reason, (TimeoutError, ConnectionError, http.client.IncompleteRead))


def request(url: str, host: str, cache: Cache, kind: str, robots_delay: float | None) -> tuple[int, Headers, bytes]:
    """GET `url` in `host`'s slot; a 429, a 5xx in `RETRY` or a dropped connection is retried after `Retry-After`
    or a backoff, up to `ATTEMPTS` times, and then reported as `RetryLater`."""
    last = ""
    for _ in range(ATTEMPTS):
        with host_slot(cache, host, robots_delay) as slot:
            try:
                status, headers, body = open_url(url, MAX_BODY[kind], truncate=kind == "robots")
            except NETWORK_ERRORS as e:
                if not transient(e):
                    raise
                slot.fail(None)
                last = str(e)
                continue
            if status not in RETRY:
                if status in REFUSAL:
                    slot.fail(None)
                else:
                    slot.succeed()
                return status, headers, body
            slot.fail(headers.retry_after)
            last = f"HTTP {status}"
    raise RetryLater(slot.key, slot.state.blocked_until, last)


def robots(parts: urllib.parse.SplitResult, cache: Cache) -> Protego | None:
    """The robots.txt of the site of `parts`, kept a day; None when it has none (a 4xx)."""
    netloc = parts.hostname if parts.port is None else f"{parts.hostname}:{parts.port}"
    url = f"{parts.scheme}://{netloc}/robots.txt"
    reply = read_entry(url, cache.dir)
    if reply is None:
        reply = fetch(url, cache, "robots")
        if reply.status == 200 or 400 <= reply.status < 500:
            write_entry(cache.dir, reply, TTL["robots"])
    if 400 <= reply.status < 500:
        return None
    if reply.status != 200:  # unreachable: RFC 9309 has it read as disallowing everything
        raise Disallowed(url, f"robots.txt answering HTTP {reply.status}")
    return Protego.parse(RobotsFile(text=reply.body.decode("utf-8", "replace")).text)


def robots_allow(url: str, parts: urllib.parse.SplitResult, cache: Cache) -> float:
    """Raise `Disallowed` unless the site's robots.txt lets every token in `ROBOT_TOKENS` fetch `url`; else the
    interval it asks for."""
    rules = robots(parts, cache)
    if rules is None:
        return 0.0
    if not all(rules.can_fetch(url, token) for token in ROBOT_TOKENS):
        raise Disallowed(url, "robots.txt")
    delays = [0.0]
    for token in ROBOT_TOKENS:
        delays.append(float(rules.crawl_delay(token) or 0))
        rate = rules.request_rate(token)
        if rate and rate.requests:
            delays.append(rate.seconds / rate.requests)
    return max(delays)


def fetch(url: str, cache: Cache, kind: str) -> Reply:
    """GET `url` politely, as the module docstring says: robots.txt first outside the APIs, each redirect hop
    checked as the first."""
    current = url
    for _ in range(MAX_REDIRECTS + 1):
        parts = check_url(current)
        delay = None if kind == "robots" or is_api(parts) else robots_allow(current, parts, cache)
        status, headers, body = request(current, parts.hostname or "", cache, kind, delay)
        if status in REDIRECT and headers.location:
            current = urllib.parse.urljoin(current, headers.location)
            continue
        return Reply(url, status, headers.content_type, body, time.time(), False, current)
    raise http.client.HTTPException(f"more than {MAX_REDIRECTS} redirects from {url}")


def get[T](
    url: str, cache: Cache, kind: str, parse: Callable[[Reply], T], keep: Callable[[T], bool] = bool
) -> tuple[Reply, T]:
    """The answer for `url` and what `parse` makes of it, from the cache unless expired; a fetched answer is cached
    once `parse` takes it and `keep` finds something in it. A status other than 200 raises `Http`, uncached."""
    reply = None if cache.fresh else read_entry(url, cache.dir)
    if reply is None:
        reply = fetch(url, cache, kind)
    cache.replies.append(reply)
    if reply.status != 200:
        raise Http(reply)
    try:
        value = parse(reply)
    except Malformed:
        if reply.cached:
            drop_entry(cache.dir, url)
        raise
    if not reply.cached and keep(value):
        write_entry(cache.dir, reply, TTL["answer"])
    return reply, value


# ---------- normalisation and matching ----------


def fold(s: str) -> str:
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = re.sub(r"\$|\\[a-zA-Z]+|[{}^_*⋆]", " ", s.lower())
    return " ".join(re.sub(r"[^\w\s]", " ", s).split())


def family(name: str) -> str:
    """The last word of the family name, in either order: `van der Waerden, B.` and `B. van der Waerden` agree."""
    parts = fold(name.split(",")[0] if "," in name else name).split()
    return parts[-1] if parts else ""


def compare(claim: Record, found: Record) -> Record:
    """How the claimed fields agree with a found record: `match`, `partial` (to be settled by hand) or `mismatch`.
    The claimed names are compared with the record's authors and editors (an edited volume lists only editors); a
    record with no names leaves the authors `unknown`, which makes the verdict `partial` at best."""
    out: Record = {}
    if claim.get("title"):
        out["title_similarity"] = round(
            difflib.SequenceMatcher(None, fold(claim["title"]), fold(found.get("title", ""))).ratio(), 3
        )
    authors, editors = found.get("authors") or [], found.get("editors") or []
    if claim.get("authors") and not (authors or editors):
        out["authors_unknown"] = True
    elif claim.get("authors"):
        mine = {family(a) for a in claim["authors"]}
        out["authors_missing"] = sorted(mine - {family(a) for a in authors + editors})
        firsts = {family(names[0]) for names in (authors, editors) if names}
        out["first_author_match"] = family(claim["authors"][0]) in firsts
    if claim.get("year") and found.get("year"):
        out["year_difference"] = abs(int(claim["year"]) - int(found["year"]))
    title_ok = out.get("title_similarity", 1.0)
    authors_ok = not out.get("authors_missing") and not out.get("authors_unknown")
    year_ok = out.get("year_difference", 0) <= 1
    if title_ok >= 0.9 and authors_ok and year_ok:
        out["verdict"] = "match"
    elif title_ok >= 0.75 and (authors_ok or out.get("first_author_match") or out.get("authors_unknown")):
        out["verdict"] = "partial"
    else:
        out["verdict"] = "mismatch"
    return out


def any_candidate(claim: Record, works: list[Record]) -> bool:
    """Whether a search found a candidate for the claimed work: only such an answer is cached."""
    return any(compare(claim, w)["verdict"] != "mismatch" for w in works)


# ---------- arXiv ----------


def arxiv_feed(reply: Reply) -> list[Record]:
    """The works of an arXiv API answer: an Atom feed, read with no DTD (so no entity of any kind)."""
    try:
        root = SafeET.fromstring(reply.body, forbid_dtd=True)
    except (SafeET.ParseError, DefusedXmlException) as e:
        raise Malformed(f"{reply.url}: not an Atom feed ({type(e).__name__}: {e})") from e
    if root.tag != f"{{{ATOM['a']}}}feed":
        raise Malformed(f"{reply.url}: not an Atom feed (root {root.tag})")
    out = []
    for e in root.findall("a:entry", ATOM):
        title = " ".join(e.findtext("a:title", "", ATOM).split())
        ident = e.findtext("a:id", "", ATOM)
        if title == "Error" or "/api/errors" in ident:
            continue
        fields = {
            "id": ident,
            "title": title,
            "authors": [a.findtext("a:name", "", ATOM) for a in e.findall("a:author", ATOM)],
            "published": e.findtext("a:published", None, ATOM),
            "updated": e.findtext("a:updated", None, ATOM),
            "journal_ref": e.findtext("arxiv:journal_ref", None, ATOM),
            "doi": e.findtext("arxiv:doi", None, ATOM),
        }
        out.append(validated(ArxivEntry, fields, f"{reply.url}: entry {ident!r}").record())
    return out


def bare_arxiv(ident: str) -> str:
    bare = re.sub(r"^(arxiv:|https?://arxiv\.org/(abs|pdf)/)", "", ident.strip(), flags=re.IGNORECASE)
    return bare.removesuffix(".pdf")


def arxiv_id(ident: str) -> str:
    """The bare arXiv identifier in `ident`, refused unless it is one (it goes into a URL path)."""
    bare = bare_arxiv(ident)
    if not re.fullmatch(ARXIV_ID, bare):
        raise Refused(f"not an arXiv identifier: {ident!r}")
    return bare


def arxiv_query(
    params: dict[str, str | int], cache: Cache, keep: Callable[[list[Record]], bool] = bool
) -> list[Record]:
    url = f"https://export.arxiv.org/api/query?{urllib.parse.urlencode(params)}"
    return get(url, cache, "api", arxiv_feed, keep)[1]


def lookup_arxiv(ident: str, cache: Cache) -> list[Record]:
    return arxiv_query({"id_list": arxiv_id(ident)}, cache)


def search_arxiv(claim: Record, cache: Cache) -> list[Record]:
    words = [w for w in fold(claim["title"]).split() if len(w) > 2][:8]
    author = first_author(claim)
    terms = [f"ti:{w}" for w in words] + ([f"au:{family(author)}"] if author else [])
    params: dict[str, str | int] = {"search_query": " AND ".join(terms), "max_results": 5}
    return arxiv_query(params, cache, keep=lambda works: any_candidate(claim, works))


def first_author(claim: Record) -> str | None:
    return claim["authors"][0] if claim.get("authors") else None


# ---------- Crossref ----------


def bare_doi(ident: str) -> str:
    return re.sub(r"^(doi:|https?://(dx\.)?doi\.org/)", "", ident.strip(), flags=re.IGNORECASE)


def doi(ident: str) -> str:
    """The bare DOI in `ident`, refused unless it is one (it goes into a URL path)."""
    bare = bare_doi(ident)
    if not re.fullmatch(r"10\.\d{4,9}/\S+", bare) or {".", ".."} & set(bare.split("/")):
        raise Refused(f"not a DOI: {ident!r}")
    return bare


def lookup_doi(ident: str, cache: Cache) -> list[Record]:
    """The work a DOI names; none only when doi.org does not know the DOI. Crossref is asked first; a DOI it does
    not hold is looked up with its registration agency: DataCite's REST API for DataCite (arXiv's and Zenodo's
    DOIs among them), and `Registered` for any other agency."""
    bare = doi(ident)
    url = f"https://api.crossref.org/works/{urllib.parse.quote(bare)}"
    try:
        return [get(url, cache, "api", lambda r: validated(CrossrefWorkAnswer, r.body, r.url).message.record())[1]]
    except Http as e:
        if e.code != 404:
            raise
    agency = get(f"https://doi.org/doiRA/{urllib.parse.quote(bare)}", cache, "api", doi_agency)[1]
    if agency is None:
        return []
    if agency != "DataCite":
        raise Registered(bare, agency)
    url = f"https://api.datacite.org/dois/{urllib.parse.quote(bare)}"
    return [get(url, cache, "api", lambda r: validated(DataciteAnswer, r.body, r.url).data.attributes.record())[1]]


def doi_agency(reply: Reply) -> str | None:
    """The registration agency in a doi.org/doiRA/ answer for one DOI; None when the DOI does not exist."""
    try:
        answers = json.loads(reply.body)
    except ValueError as e:
        raise Malformed(f"{reply.url}: not JSON ({e})") from e
    if not (isinstance(answers, list) and len(answers) == 1):
        raise Malformed(f"{reply.url}: not one DOI's answer")
    answer = validated(DoiAgency, answers[0], reply.url)
    if answer.ra:
        return answer.ra
    if answer.status == "DOI does not exist":
        return None
    raise Malformed(f"{reply.url}: {answer.status or 'no agency'}")


def openalex_work(ident: str, cache: Cache) -> Record:
    """The OpenAlex record of the work a DOI names: its copies, with their versions, and whether it is retracted."""
    url = f"https://api.openalex.org/works/doi:{urllib.parse.quote(doi(ident))}?select={OPENALEX_FIELDS}"
    return get(url, cache, "api", lambda r: validated(OpenAlexWork, r.body, r.url).record())[1]


def cmd_copies(args: argparse.Namespace, cache: Cache) -> int:
    sweep(cache_dir(cache))
    try:
        out = openalex_work(args.doi, cache)
    except Http as e:
        out = {"status": "not-found" if e.code == 404 else "error", "http": e.code}
        print(json.dumps(out | report(cache.replies), ensure_ascii=False, indent=2))
        return 2
    except FAILURES as e:
        print(json.dumps(failure(e) | report(cache.replies), ensure_ascii=False, indent=2))
        return 2
    print(json.dumps({"status": "ok"} | out | report(cache.replies), ensure_ascii=False, indent=2))
    return 0


def search_crossref(claim: Record, cache: Cache) -> list[Record]:
    params: dict[str, str | int] = {"query.bibliographic": claim["title"], "rows": 5}
    if author := first_author(claim):
        params["query.author"] = author
    url = f"https://api.crossref.org/works?{urllib.parse.urlencode(params)}"

    def works(r: Reply) -> list[Record]:
        return [w.record() for w in validated(CrossrefListAnswer, r.body, r.url).message.items]

    return get(url, cache, "api", works, keep=lambda found: any_candidate(claim, found))[1]


# ---------- commands ----------


# The statuses that say the claimed work was not found; each needs every source's answer, fetched now.
NEGATIVE = ("mismatch", "not-found")
RANK = {"match": 0, "partial": 1, "mismatch": 2}


def find(args: argparse.Namespace, claim: Record, cache: Cache) -> Record:
    """The candidates, best verdict first, and the status: the best verdict, `ambiguous`, or `not-found`. A search
    that failed leaves a negative status unproved, so the status is then the failure's."""
    errors: list[str] = []
    later: list[RetryLater] = []
    if args.arxiv:
        found = lookup_arxiv(args.arxiv, cache)
    elif args.doi:
        found = lookup_doi(args.doi, cache)
    else:
        if not args.title:
            raise Refused("lookup needs --arxiv, --doi or --title")
        found = []
        for search in (search_crossref, search_arxiv):
            try:
                found += search(claim, cache)
            except (Http, *FAILURES) as e:
                errors.append(f"{search.__name__}: {e}")
                later += [e] if isinstance(e, RetryLater) else []
    for f in found:
        f["comparison"] = compare(claim, f)
    found.sort(key=lambda f: (RANK[f["comparison"]["verdict"]], -f["comparison"].get("title_similarity", 0)))
    best = found[0]["comparison"]["verdict"] if found else "not-found"
    # Sequels and journal/preprint twins match alike; the caller settles them by venue and pages.
    if sum(f["comparison"]["verdict"] == "match" and f["source"] == found[0]["source"] for f in found) > 1:
        best = "ambiguous"
    out: Record = {"status": best, "candidates": found, "errors": errors}
    if errors and best in NEGATIVE:
        out |= max(later, key=lambda e: e.until).report() if later else {"status": "error"}
    return out


def cmd_lookup(args: argparse.Namespace, cache: Cache) -> int:
    sweep(cache_dir(cache))
    claim = {
        "title": args.title,
        "authors": [a.strip() for a in args.authors.split(";")] if args.authors else None,
        "year": args.year,
    }
    try:
        out = find(args, claim, cache)
        if out["status"] in NEGATIVE and any(r.cached for r in cache.replies):
            cache.fresh, cache.replies = True, []  # a negative answer comes from the source, never the cache
            out = find(args, claim, cache)
    except Registered as e:
        print(json.dumps(e.report() | report(cache.replies), ensure_ascii=False, indent=2))
        return 0
    except (Http, *FAILURES) as e:
        print(json.dumps(failure(e) | report(cache.replies), ensure_ascii=False, indent=2))
        return 2
    print(json.dumps(out | report(cache.replies), ensure_ascii=False, indent=2))
    return 0


def pdf_text(pdf: pdfium.PdfDocument) -> str:
    pages = (pdf[i].get_textpage().get_text_range() for i in range(len(pdf)))
    return "\n".join(f"=== page {i} ===\n{t}" for i, t in enumerate(pages, 1)).replace("\r\n", "\n")


def page_numbers(spec: str) -> list[int]:
    pages: list[int] = []
    for part in spec.split(","):
        lo, _, hi = part.strip().partition("-")
        pages += range(int(lo), int(hi or lo) + 1)
    return pages


def render_pages(pdf: pdfium.PdfDocument, pages: list[int], out: Path, stem: str) -> list[str]:
    """Render PDF pages (1-indexed, in file order) to PNG for reading formulas off the page."""
    bad = [p for p in pages if not 1 <= p <= len(pdf)]
    if bad:
        raise ValueError(f"pages {bad} outside 1..{len(pdf)}")
    for p in pages:
        width, height = pdf[p - 1].get_size()
        if width * height * SCALE**2 > MAX_PIXELS:
            raise ValueError(f"page {p} is {width:.0f} x {height:.0f} pt, over {MAX_PIXELS:,} pixels at scale {SCALE}")
    paths = []
    for p in pages:
        path = out / f"{stem}-p{p}.png"
        pdf[p - 1].render(scale=SCALE).to_pil().save(path)
        paths.append(str(path))
    return paths


class _Text(html.parser.HTMLParser):
    """The text of an HTML page outside `script` and `style`, in one pass."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self.hidden = 0

    def handle_starttag(self, tag: str, attrs: Any) -> None:
        if tag in ("script", "style"):
            self.hidden += 1

    def handle_endtag(self, tag: str) -> None:
        if tag in ("script", "style") and self.hidden:
            self.hidden -= 1

    def handle_data(self, data: str) -> None:
        if not self.hidden:
            self.parts.append(data)


def html_text(body: bytes) -> str:
    parser = _Text()
    parser.feed(body.decode("utf-8", "replace"))
    parser.close()
    return " ".join(parser.parts)


def document(reply: Reply) -> Document:
    """The document in an answer: a PDF (at most `MAX_PAGES` pages), an HTML page, or text."""
    return parse_document(reply.body, reply.type, reply.url)


def parse_document(body: bytes, ctype: str, where: str) -> Document:
    if body[:5] == b"%PDF-":
        try:
            pdf = pdfium.PdfDocument(body)
            if len(pdf) > MAX_PAGES:
                raise Malformed(f"{where}: a PDF of {len(pdf)} pages, over {MAX_PAGES}")
            return Document(kind="pdf", text=pdf_text(pdf), pdf=pdf)
        except pdfium.PdfiumError as e:
            raise Malformed(f"{where}: an unreadable PDF ({e})") from e
    if is_html(body, ctype):
        return Document(kind="html", text=html_text(body))
    return Document(kind="text", text=body.decode("utf-8", "replace"))


def local_document(path: Path) -> Document:
    """A copy the user obtained and saved, read from disk with no request, bounded as a fetched document."""
    limit = MAX_BODY["document"]
    with path.open("rb") as f:
        body = f.read(limit + 1)
    if len(body) > limit:
        raise Malformed(f"{path}: over {limit} bytes")
    return parse_document(body, "text/html" if path.suffix.lower() in (".html", ".htm") else "", str(path))


def cmd_fetch_text(args: argparse.Namespace, cache: Cache) -> int:
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    if args.file:
        path = Path(args.file).resolve()
        where: Record = {"file": str(path)}
        try:
            doc = local_document(path)
        except (OSError, Malformed) as e:
            print(json.dumps({"status": "error", "error": str(e)} | where))
            return 2
        where["opened_at"] = datetime.datetime.now(datetime.UTC).isoformat(timespec="seconds")
        key = str(path)
    else:
        sweep(cache_dir(cache))
        url = f"https://arxiv.org/pdf/{arxiv_id(args.arxiv)}" if args.arxiv else args.url
        try:
            _, doc = get(url, cache, "document", document, keep=lambda d: d.usable)
        except Http as e:
            if e.code in UNREADABLE:
                err: Record = {"status": "inaccessible", "reason": UNREADABLE[e.code]}
            else:  # a 3xx with no Location, a 400, a 501: no evidence about the source
                err = {"status": "error", "reason": f"HTTP {e.code}"}
            print(json.dumps(err | {"http": e.code, "url": url} | report(cache.replies)))
            return 2
        except FAILURES as e:
            print(json.dumps(failure(e) | {"url": url} | report(cache.replies)))
            return 2
        where = {"url": url} | report(cache.replies)
        key = url
    if args.render_pages and doc.pdf is None:
        print(json.dumps({"status": "error", "error": "--render-pages needs a PDF"} | where))
        return 2
    if not doc.usable:
        # A site answering no text has shown nothing of the work; a file the user saved is only the wrong file.
        status: Record = {"status": "error", "error": "no document text"}
        if not args.file:
            status = {"status": "inaccessible", "reason": "no document text"}
        print(json.dumps(status | where | {"head": doc.text[:200]}))
        return 2
    stem = entry_key(key)[:16]
    result: Record = {"status": "ok", "kind": doc.kind} | where
    if args.render_pages and doc.pdf is not None:
        try:
            result["images"] = render_pages(doc.pdf, page_numbers(args.render_pages), out, stem)
        except (ValueError, pdfium.PdfiumError) as e:
            print(json.dumps({"status": "error", "error": str(e)} | where))
            return 2
    path = out / f"{stem}.txt"
    path.write_text(doc.text)
    result |= {"text": str(path), "chars": len(doc.text)}
    print(json.dumps(result))
    return 0


def ledger_yaml(text: str) -> YAML:
    """A round-trip YAML for the ledger `text`: writing back keeps its comments, quoting and sequence layout."""
    _, sequence, offset = load_yaml_guess_indent(text)
    y = YAML()
    y.preserve_quotes = True
    y.width = 100
    y.indent(mapping=2, sequence=sequence or 4, offset=2 if offset is None else offset)
    return y


def load_ledger(path: Path) -> tuple[Any, YAML]:
    if not path.is_file():
        raise NoLedger(str(path))
    text = path.read_text()
    y = ledger_yaml(text)
    return y.load(text), y


@contextmanager
def ledger_lock(path: Path, cache: Path) -> Iterator[None]:
    """Hold an exclusive lock on the ledger at `path` from its read to its write."""
    key = hashlib.sha256(str(path.resolve()).encode()).hexdigest()[:16]
    with (state_dir(cache) / f"ledger-{key}.lock").open("a+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        yield


def write_atomic(path: Path, data: str | bytes) -> None:
    """Replace `path` by `data` in one rename, so a reader sees the old file or the new one, never a part."""
    mode = "wb" if isinstance(data, bytes) else "w"
    with tempfile.NamedTemporaryFile(mode, dir=path.parent, prefix=f".{path.name}.", delete=False) as f:
        tmp = Path(f.name)
        try:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        except BaseException:
            tmp.unlink()
            raise
    try:
        if path.exists():
            shutil.copymode(path, tmp)
        os.replace(tmp, path)
    except BaseException:
        tmp.unlink(missing_ok=True)
        raise


def node(value: Any) -> Any:
    """`value` as ruamel nodes: small leaves on one line (`authors: [...]`, `{page: ..., date: ...}`), the rest
    in blocks, and text with line breaks as a literal block."""
    if isinstance(value, str):
        return LiteralScalarString(value) if "\n" in value else value
    if isinstance(value, dict):
        out: Any = CommentedMap((k, node(v)) for k, v in value.items())
        leaves = list(value.values())
    elif isinstance(value, list):
        out, leaves = CommentedSeq(node(v) for v in value), value
    else:
        return value
    if leaves and all(isinstance(v, str | int) and len(str(v)) <= 40 for v in leaves):
        out.fa.set_flow_style()
    return out


def dump_ledger(doc: Any, y: YAML, path: Path) -> None:
    """Write `doc` back to `path`. ruamel ends a folded plain line with a space, dropped when that changes nothing."""
    buf = io.StringIO()
    y.dump(doc, buf)
    text = buf.getvalue()
    trimmed = re.sub(r" +$", "", text, flags=re.MULTILINE)
    write_atomic(path, trimmed if plain(YAML().load(trimmed)) == plain(doc) else text)


def norm_id(ident: str) -> str:
    ident = ident.strip()
    if re.match(r"(?i)^(arxiv:|https?://arxiv\.org/)", ident):
        return "arxiv:" + re.sub(r"v\d+$", "", bare_arxiv(ident)).lower()
    if re.match(r"(?i)^(doi:|https?://(dx\.)?doi\.org/|10\.)", ident):
        return "doi:" + bare_doi(ident).lower()
    return ident.lower()


def plain(node: Any) -> Any:
    return json.loads(json.dumps(node, default=str))


def sources_of(doc: Any) -> list[Record]:
    """The ledger's sources; none when the file is not a mapping with a list of mappings there."""
    sources = doc.get("sources") if isinstance(doc, dict) else None
    return [s for s in sources if isinstance(s, dict)] if isinstance(sources, list) else []


def find_sources(doc: Any, ident: str | None, title: str | None) -> list[Record]:
    def same(s: Record) -> bool:
        if ident and s.get("id") and norm_id(str(s["id"])) == norm_id(ident):
            return True
        return bool(title) and difflib.SequenceMatcher(None, fold(title), fold(str(s.get("title", "")))).ratio() >= 0.85

    return [s for s in sources_of(doc) if same(s)]


def cmd_ledger_get(args: argparse.Namespace, cache: Cache) -> int:
    doc, _ = load_ledger(Path(args.ledger))
    print(json.dumps(plain(find_sources(doc, args.id, args.title)), ensure_ascii=False, indent=2))
    return 0


def locator_problems(source: Record) -> list[str]:
    checked = source.get("checked")
    if checked is None:
        return []
    where = source.get("id")
    if not isinstance(checked, dict):
        return [f"{where}: checked is not a mapping"]
    problems = [] if checked.get("url") else [f"{where}: checked.url missing"]
    locators = checked.get("locators") or {}
    if not isinstance(locators, dict):
        return [*problems, f"{where}: checked.locators is not a mapping"]
    for location, rec in locators.items():
        problems += [f"{where} / {location}: {p}" for p in record_problems(rec or {})]
    return problems


def record_problems(rec: Any) -> list[str]:
    """What a locator record lacks: a mapping with a page and a date as YYYY-MM-DD."""
    if not isinstance(rec, dict):
        return ["not a mapping"]
    problems = [f"{key} missing" for key in ("page", "date") if not rec.get(key)]
    if "version" in rec and not isinstance(rec["version"], str):
        problems.append("version is not a string")
    if rec.get("date"):
        try:
            datetime.date.fromisoformat(str(rec["date"]))
        except ValueError:
            problems.append(f"date {rec['date']!r} is not YYYY-MM-DD")
    return problems


def cmd_ledger_add(args: argparse.Namespace, cache: Cache) -> int:
    rec = json.loads(Path(args.json).read_text())
    src, loc, url = rec.get("source") or {}, rec.get("locator") or {}, rec.get("url")
    problems = [f"source.{k} missing" for k in ("id", "title") if not src.get(k)]
    problems += [] if url else ["url missing"]
    problems += [] if loc.get("location") else ["locator.location missing"]
    problems += [f"locator.{p}" for p in record_problems(loc)]
    if problems:
        raise Refused(f"record: {'; '.join(problems)}")
    ledger = Path(args.ledger)
    with ledger_lock(ledger, cache_dir(cache)):
        entry = add_locator(ledger, src, url, loc, args.new_source)
    print(json.dumps({"status": "ok", "id": str(entry["id"]), "location": loc["location"]}, ensure_ascii=False))
    return 0


def add_locator(ledger: Path, src: Record, url: str, loc: Record, new_source: bool) -> Record:
    doc, y = load_ledger(ledger)
    if not isinstance(doc, dict):
        raise Refused(f"{ledger} is not a YAML mapping")
    hits = find_sources(doc, src["id"], None)
    if not hits and not new_source:
        # One work under two ids (a DOI here, a landing page there) would split its record in two.
        twins = find_sources(doc, None, src["title"])
        if twins:
            under = f"id {str(twins[0]['id'])!r}" if twins[0].get("id") else "no id"
            raise Refused(
                f"the ledger lists {str(twins[0].get('title'))!r} under {under}: if that is this work, use its id; "
                "if another, pass --new-source"
            )
    if hits:
        # A project may list a work once per locator, in the format's own `location`: take the entry for this one.
        entry = next((h for h in hits if fold(str(h.get("location", ""))) == fold(loc["location"])), hits[0])
    else:
        sources = doc.get("sources")
        if not sources:
            sources = doc["sources"] = CommentedSeq()
        if not isinstance(sources, list):
            raise Refused(f"{ledger}: sources is not a list")
        keys = ("title", "authors", "id", "type", "relationship", "note")
        entry = CommentedMap((k, node(src[k])) for k in keys if src.get(k))
        sources.append(entry)
    if entry.get("checked") is None:
        entry["checked"] = CommentedMap()
    checked = entry["checked"]
    if not isinstance(checked, dict):
        raise Refused(f"{src['id']}: checked is not a mapping")
    checked.setdefault("url", url)
    if checked.get("locators") is None:
        checked["locators"] = CommentedMap()
    locators = checked["locators"]
    if not isinstance(locators, dict):
        raise Refused(f"{src['id']}: checked.locators is not a mapping")
    key = next((k for k in locators if fold(str(k)) == fold(loc["location"])), loc["location"])
    record = {"page": str(loc["page"]), "date": str(loc["date"])}
    if loc.get("version"):
        record["version"] = loc["version"]  # the version of the work the page numbers belong to
    if url != checked["url"]:
        record["url"] = url  # this locator was read from another copy than the source's `url`
    locators[key] = node(record)
    dump_ledger(doc, y, ledger)
    return entry


def cmd_validate(args: argparse.Namespace, cache: Cache) -> int:
    """Check what this script writes, the `checked` records; the format as a whole is the project's to check."""
    doc, _ = load_ledger(Path(args.ledger))
    problems = []
    if not isinstance(doc, dict):
        problems.append("<root>: not a mapping")
    elif not isinstance(doc.get("sources"), list):
        problems.append("sources: not a list")
    for s in sources_of(doc):
        problems += locator_problems(s)
    print(json.dumps({"status": "ok" if not problems else "invalid", "problems": problems}, indent=2))
    return 0 if not problems else 1


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--ledger", help=f"ledger file (default: {LEDGER_NAME} at the root of the git work tree)")
    sub = p.add_subparsers(dest="cmd", required=True)

    lk = sub.add_parser("lookup", help="canonical metadata, compared with the claimed fields")
    g = lk.add_mutually_exclusive_group()
    g.add_argument("--arxiv")
    g.add_argument("--doi")
    lk.add_argument("--title", help="claimed title (searched when no identifier is given)")
    lk.add_argument("--authors", help="claimed authors, separated by ';'")
    lk.add_argument("--year", type=int, help="claimed year")
    lk.set_defaults(fn=cmd_lookup)

    cp = sub.add_parser("copies", help="the copies of a work known to OpenAlex, with their versions, by its DOI")
    cp.add_argument("--doi", required=True)
    cp.set_defaults(fn=cmd_copies)

    ft = sub.add_parser("fetch-text", help="download one openly served document and extract its text")
    g = ft.add_mutually_exclusive_group(required=True)
    g.add_argument("--arxiv")
    g.add_argument("--url")
    g.add_argument("--file", help="read a copy the user obtained and saved, with no request")
    ft.add_argument("--out", required=True)
    ft.add_argument("--render-pages", help="also render these PDF pages to PNG, e.g. 11,12 or 11-13 (file order)")
    ft.set_defaults(fn=cmd_fetch_text)

    lg = sub.add_parser("ledger", help="read or extend the ledger in formalization.yaml")
    lsub = lg.add_subparsers(dest="lcmd", required=True)
    gt = lsub.add_parser("get")
    gt.add_argument("--id")
    gt.add_argument("--title")
    gt.set_defaults(fn=cmd_ledger_get)
    ad = lsub.add_parser(
        "add", help='JSON file {"source": {...}, "url": "...", "locator": {location, page, date, version?}}'
    )
    ad.add_argument("--json", required=True)
    ad.add_argument(
        "--new-source", action="store_true", help="add the source even if the ledger lists its title under another id"
    )
    ad.set_defaults(fn=cmd_ledger_add)

    va = sub.add_parser(
        "validate", help="check the `checked` records in formalization.yaml (not the format as a whole)"
    )
    va.set_defaults(fn=cmd_validate)
    args = p.parse_args()
    args.ledger = args.ledger or str(repo_root() / LEDGER_NAME)
    cache = Cache(cache_path())
    # A run stopped by SIGTERM (a tool's timeout) still runs its `finally` blocks, which write the hosts' state.
    signal.signal(signal.SIGTERM, lambda signum, _: sys.exit(128 + signum))
    try:
        return args.fn(args, cache)
    except NoLedger as e:
        print(json.dumps({"status": "no-ledger", "ledger": str(e)}))
        return 3
    except Refused as e:
        print(json.dumps({"status": "refused", "error": str(e)}, ensure_ascii=False))
        return 1
    except Exception as e:  # anything unforeseen is answered in JSON as well, for the agent reading the output
        frame = traceback.extract_tb(e.__traceback__)[-1]
        error = f"{type(e).__name__}: {e} ({Path(frame.filename).name}:{frame.lineno})"
        print(json.dumps({"status": "error", "error": error}, ensure_ascii=False))
        return 2


if __name__ == "__main__":
    sys.exit(main())
