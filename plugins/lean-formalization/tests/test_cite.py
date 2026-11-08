"""Tests of cite.py: its cache (what it keeps and for how long), its politeness (the interval, the backoff,
robots.txt, redirects), what it accepts, the ledger it writes, and its JSON answers.

Run in the environment `cite.py.lock` pins: `uv export --script <cite.py> --locked -o req.txt`, then
`uv run --no-project --with-requirements req.txt --with pytest pytest <this file>`. No request leaves the
machine: `cite.open_url` is replaced by a fake that serves the answers each test sets up, name lookups by a fake
public address, and `time.sleep` by a record of the waits.
"""

import email.utils
import fcntl
import http.client
import io
import ipaddress
import json
import os
import sys
import time
import urllib.error
import urllib.request
import urllib.response
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "skills" / "citation-check" / "scripts"))
import cite  # noqa: E402

REAL_OPEN_URL = cite.open_url


PDF_URL = "https://arxiv.org/pdf/2010.05513v2"
ROBOTS_URL = "https://arxiv.org/robots.txt"
API_URL = "https://export.arxiv.org/api/query?id_list=2010.05513"
CROSSREF_URL = "https://api.crossref.org/works/10.1000/x"
AGENCY_URL = "https://doi.org/doiRA/10.1000/x"
DATACITE_URL = "https://api.datacite.org/dois/10.1000/x"
JSON = "application/json"
NO_SUCH_DOI = (200, JSON, b'[{"DOI": "10.1000/x", "status": "DOI does not exist"}]')
EMPTY_FEED = b'<?xml version="1.0"?><feed xmlns="http://www.w3.org/2005/Atom"></feed>'
ONE_ENTRY = (
    b'<?xml version="1.0"?><feed xmlns="http://www.w3.org/2005/Atom"><entry>'
    b"<id>http://arxiv.org/abs/2010.05513v2</id><title>A title</title><published>2020-10-12T00:00:00Z</published>"
    b"<author><name>A. Author</name></author></entry></feed>"
)
NO_ROBOTS = (404, "text/html", b"")
OPENALEX_URL = f"https://api.openalex.org/works/doi:10.1000/x?select={cite.OPENALEX_FIELDS}"
OPENALEX_WORK = json.dumps(
    {
        "id": "https://openalex.org/W1",
        "doi": "https://doi.org/10.1000/x",
        "title": "A  title",
        "publication_year": 2020,
        "is_retracted": False,
        "updated_date": "2026-11-07T11:25:07.637180",
        "best_oa_location": {
            "is_oa": True,
            "landing_page_url": "http://arxiv.org/abs/1000.00001",
            "pdf_url": "https://arxiv.org/pdf/1000.00001",
            "version": "submittedVersion",
            "license": None,
            "source": {"display_name": "arXiv", "type": "repository"},
        },
        "locations": [
            {"is_oa": False, "landing_page_url": "https://doi.org/10.1000/x", "pdf_url": None,
             "version": "publishedVersion", "license": None, "source": {"display_name": "A Journal", "type": "journal"}},
            {"is_oa": True, "landing_page_url": "http://arxiv.org/abs/1000.00001", "pdf_url": "https://arxiv.org/pdf/1000.00001",
             "version": "submittedVersion", "license": None, "source": {"display_name": "arXiv", "type": "repository"}},
        ],
    }
).encode()
ATOM = "application/atom+xml"
WORDS = b"<html><body>" + b"word " * 300 + b"</body></html>"


class Fake:
    """A stand-in for `cite.open_url`: serves `answers[url]`, a (status, headers, body) triple or a list of them
    taken in turn (headers: a dict, or a content type), and records the calls."""

    def __init__(self, answers):
        self.answers, self.calls = answers, []

    def __call__(self, url, limit, truncate=False):
        self.calls.append(url)
        answer = self.answers[url]
        status, headers, body = answer.pop(0) if isinstance(answer, list) else answer
        headers = {"Content-Type": headers} if isinstance(headers, str) else headers
        body = cite.read_body(_Body(body), limit, truncate) if 200 <= status < 300 else b""
        return status, cite.Headers.of(headers), body


class _Body:
    def __init__(self, body):
        self._body = body

    def read1(self, n):
        chunk, self._body = self._body[:n], self._body[n:]
        return chunk


def public(host, port):
    try:
        return [str(ipaddress.ip_address(host))]
    except ValueError:
        return ["93.184.216.34"]


@pytest.fixture(autouse=True)
def isolated(tmp_path, monkeypatch):
    """A cache of its own, no proxy, public addresses, no network, and waits recorded instead of slept."""
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "xdg"))
    for var in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "no_proxy", "NO_PROXY", "all_proxy"):
        monkeypatch.delenv(var, raising=False)
    monkeypatch.setattr(cite, "addresses", public)
    monkeypatch.setattr(cite, "open_url", Fake({}))  # any request raises KeyError
    slept = []
    monkeypatch.setattr(cite.time, "sleep", slept.append)
    return slept


@pytest.fixture
def slept(isolated):
    return isolated


@pytest.fixture
def cache(monkeypatch):
    monkeypatch.setattr(cite, "INTERVAL", {})
    monkeypatch.setattr(cite, "DEFAULT_INTERVAL", 0.0)
    return cite.Cache(cite.cache_path())


def serve(monkeypatch, answers):
    fake = Fake(answers)
    monkeypatch.setattr(cite, "open_url", fake)
    return fake


def run(monkeypatch, capsys, *argv):
    """`cite.py *argv`: its exit code and its output, which must be JSON."""
    monkeypatch.setattr(sys, "argv", ["cite.py", *argv])
    code = cite.main()
    return code, json.loads(capsys.readouterr().out)


def meta_of(cache, url):
    return json.loads((cache.dir / cite.entry_key(url)).read_bytes().partition(b"\n")[0])


def cached(cache, url):
    return (cache.dir / cite.entry_key(url)).exists()


def state_of(cache, host):
    return json.loads((cache.dir / "state" / f"{host}.json").read_text())


def fetch_text_args(tmp_path, arxiv="2010.05513v2", render_pages=None, url=None):
    return type("A", (), {"arxiv": arxiv, "url": url, "out": str(tmp_path / "t"), "render_pages": render_pages})


# ---------- the cache ----------


def test_bot_check_html_for_a_pdf_url_is_not_kept(cache, monkeypatch, tmp_path, capsys):
    serve(
        monkeypatch, {ROBOTS_URL: NO_ROBOTS, PDF_URL: (200, "text/html", b"<html><body>Are you a robot?</body></html>")}
    )
    assert cite.cmd_fetch_text(fetch_text_args(tmp_path), cache) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["status"] == "inaccessible" and out["reason"] == "no document text"
    assert not cached(cache, PDF_URL)


def test_an_unreadable_pdf_is_answered_in_json_and_not_kept(cache, monkeypatch, tmp_path, capsys):
    serve(monkeypatch, {ROBOTS_URL: NO_ROBOTS, PDF_URL: (200, "application/pdf", b"%PDF-1.4 not a document")})
    assert cite.cmd_fetch_text(fetch_text_args(tmp_path), cache) == 2
    out = json.loads(capsys.readouterr().out)
    assert out["status"] == "error" and out["reason"] == "malformed"
    assert not cached(cache, PDF_URL)


def test_an_answer_is_replayed_for_a_week(cache, monkeypatch):
    fake = serve(monkeypatch, {API_URL: (200, ATOM, ONE_ENTRY)})
    cite.cache_dir(cache)
    assert cite.lookup_arxiv("2010.05513", cache)[0]["id"] == "arXiv:2010.05513v2"
    assert cite.lookup_arxiv("2010.05513", cache)[0]["title"] == "A title"
    assert len(fake.calls) == 1
    meta = meta_of(cache, API_URL)
    assert meta["expires_at"] - meta["fetched_at"] == pytest.approx(cite.TTL["answer"])


def test_an_empty_lookup_answer_is_not_kept(cache, monkeypatch):
    fake = serve(monkeypatch, {API_URL: (200, ATOM, EMPTY_FEED)})
    cite.cache_dir(cache)
    for _ in range(2):
        assert cite.lookup_arxiv("2010.05513", cache) == []
    assert len(fake.calls) == 2 and not cached(cache, API_URL)


def test_an_unreadable_entry_is_a_miss_and_is_swept(cache, monkeypatch):
    fake = serve(monkeypatch, {ROBOTS_URL: NO_ROBOTS, PDF_URL: (200, "application/pdf", b"%PDF-1.4 ...")})
    cite.cache_dir(cache)
    entry = cache.dir / cite.entry_key(PDF_URL)
    entry.write_bytes(json.dumps({"url": PDF_URL, "status": 200}).encode() + b"\n%PDF-1.4 ...")  # no fetch time
    assert cite.read_entry(PDF_URL, cache.dir) is None
    cite.sweep(cache.dir)
    assert not entry.exists()
    assert cite.fetch(PDF_URL, cache, "document").status == 200 and len(fake.calls) == 2


def test_the_oldest_answers_go_past_the_size_cap(cache, monkeypatch):
    cite.cache_dir(cache)
    for i, url in enumerate(("https://a.example/1", "https://a.example/2")):
        reply = cite.Reply(url, 200, "text/plain", b"x" * 100, time.time() - 10 + i, False)
        cite.write_entry(cache.dir, reply, cite.TTL["answer"])
    monkeypatch.setattr(cite, "MAX_CACHE", (cache.dir / cite.entry_key("https://a.example/2")).stat().st_size)
    cite.sweep(cache.dir)
    assert not cached(cache, "https://a.example/1") and cached(cache, "https://a.example/2")


def test_a_refusal_is_not_kept_and_counts_as_a_failure(cache, monkeypatch):
    fake = serve(monkeypatch, {ROBOTS_URL: NO_ROBOTS, PDF_URL: (403, "", b"")})
    cite.cache_dir(cache)
    with pytest.raises(cite.Http):
        cite.get(PDF_URL, cache, "document", cite.document)
    assert fake.calls == [ROBOTS_URL, PDF_URL] and not cached(cache, PDF_URL)
    assert state_of(cache, "arxiv.org")["failures"] == 1


def test_a_404_is_not_kept(cache, monkeypatch):
    fake = serve(monkeypatch, {CROSSREF_URL: (404, "", b""), AGENCY_URL: NO_SUCH_DOI})
    cite.cache_dir(cache)
    for _ in range(2):
        assert cite.lookup_doi("10.1000/x", cache) == []
    assert fake.calls == [CROSSREF_URL, AGENCY_URL] * 2
    assert not cached(cache, CROSSREF_URL) and not cached(cache, AGENCY_URL)


def test_sweep_removes_what_an_interrupted_write_left(cache):
    cite.cache_dir(cache)
    temps = [cache.dir / ".0123.body.k3j2l9x8", cite.state_dir(cache.dir) / ".arxiv.org.json.x8k3j2"]
    for temp in temps:
        temp.write_bytes(b"half")
    cite.sweep(cache.dir)
    assert all(t.exists() for t in temps)  # they may belong to a write still running
    for temp in temps:
        os.utime(temp, (0, 0))
    cite.sweep(cache.dir)
    assert not any(t.exists() for t in temps)


# ---------- politeness ----------


def test_requests_to_one_host_wait_its_interval(cache, monkeypatch, slept):
    monkeypatch.setattr(cite, "INTERVAL", {"arxiv.org": 15.0})
    for _ in range(2):
        with cite.host_slot(cache, "arxiv.org"):
            pass
    assert slept and 14.0 < slept[-1] <= 15.0


def test_the_request_is_written_down_before_it_goes_out(cache, monkeypatch):
    seen = []

    def answer(url, limit, truncate=False):
        seen.append(state_of(cache, "export.arxiv.org"))
        return 200, cite.Headers.of({"Content-Type": ATOM}), ONE_ENTRY

    monkeypatch.setattr(cite, "open_url", answer)
    cite.cache_dir(cache)
    before = time.time()
    cite.lookup_arxiv("2010.05513", cache)
    assert seen[0]["last_request"] >= before


def test_a_clock_set_back_waits_one_interval_at_most(cache, monkeypatch, slept):
    monkeypatch.setattr(cite, "INTERVAL", {"arxiv.org": 15.0})
    cite.write_atomic(cite.state_dir(cache.dir) / "arxiv.org.json", json.dumps({"last_request": time.time() + 1e6}))
    with cite.host_slot(cache, "arxiv.org"):
        pass
    assert slept and slept[-1] <= 15.0


def test_a_lock_held_too_long_ends_the_run(cache):
    with (cite.state_dir(cache.dir) / "arxiv.org.lock").open("a+") as held:
        fcntl.flock(held, fcntl.LOCK_EX)
        with pytest.raises(cite.RetryLater, match="another run holds the host"), cite.host_slot(cache, "arxiv.org"):
            pass
    assert cache.waited <= cite.WAIT_BUDGET


def test_retry_after_in_seconds_is_obeyed(cache, monkeypatch, slept):
    fake = serve(monkeypatch, {API_URL: [(503, {"Retry-After": "7"}, b""), (200, ATOM, ONE_ENTRY)]})
    assert cite.lookup_arxiv("2010.05513", cache)[0]["title"] == "A title"
    assert len(fake.calls) == 2 and 6.0 < max(slept) <= 7.0
    assert state_of(cache, "export.arxiv.org")["failures"] == 0


def test_retry_after_as_a_date_is_obeyed(cache, monkeypatch, slept):
    when = email.utils.formatdate(time.time() + 20, usegmt=True)
    serve(monkeypatch, {API_URL: [(429, {"Retry-After": when}, b""), (200, ATOM, ONE_ENTRY)]})
    cite.lookup_arxiv("2010.05513", cache)
    assert 17.0 < max(slept) <= 20.0


def test_the_intervals_keep_the_sources_terms():
    """The intervals as set, so that a change to one is a change here too, made against the source's terms cited
    in the comment on `cite.INTERVAL`; the `cache` fixture zeroes the intervals for every other test."""
    assert cite.INTERVAL == {
        "export.arxiv.org": 3.0,  # the arXiv API's terms
        "arxiv.org": 15.0,  # arxiv.org's robots.txt
        "api.crossref.org": 1.0,
        "api.datacite.org": 1.0,  # well under 3000 requests in 5 minutes
        "api.openalex.org": 1.0,  # well under 10 requests per second without a key
    }
    assert cite.DEFAULT_INTERVAL >= 1.0  # an interval for every other host


def test_without_retry_after_the_backoff_doubles_with_jitter(monkeypatch):
    monkeypatch.setattr(cite.random, "uniform", lambda a, b: b)
    assert [cite.backoff(n, None, 3.0) for n in (1, 2, 3)] == [6.0, 12.0, 24.0]
    assert cite.backoff(40, None, 3.0) == cite.MAX_BACKOFF
    monkeypatch.setattr(cite.random, "uniform", lambda a, b: a)
    assert cite.backoff(2, None, 3.0) == 6.0  # half the delay at least
    assert cite.backoff(0, None, 3.0) == 3.0  # never below the interval: half of 3.0 is raised to it
    assert cite.backoff(1, 0.0, 3.0) == 3.0 and cite.backoff(1, 1e9, 3.0) == cite.MAX_BLOCK


def test_a_long_wait_ends_the_run_and_holds_back_the_next(cache, monkeypatch, capsys):
    fake = serve(monkeypatch, {API_URL: (503, {"Retry-After": "3600"}, b"")})
    code, out = run(monkeypatch, capsys, "lookup", "--arxiv", "2010.05513")
    assert code == 2 and out["status"] == "retry-later" and 3590 <= out["retry_after"] <= 3600
    assert out["host"] == "export.arxiv.org" and len(fake.calls) == 1
    assert state_of(cache, "export.arxiv.org")["blocked_until"] > time.time() + 3500
    code, out = run(monkeypatch, capsys, "lookup", "--arxiv", "2010.05513")  # the next run, at once
    assert out["status"] == "retry-later" and len(fake.calls) == 1


def test_a_dropped_connection_is_retried_and_a_bad_name_is_not(cache, monkeypatch):
    def dropped(url, limit, truncate=False):
        raise urllib.error.URLError(ConnectionResetError("reset"))

    monkeypatch.setattr(cite, "open_url", dropped)
    with pytest.raises(cite.RetryLater):
        cite.lookup_arxiv("2010.05513", cache)
    assert state_of(cache, "export.arxiv.org")["failures"] == cite.ATTEMPTS

    def unknown(url, limit, truncate=False):
        raise urllib.error.URLError(OSError("Name or service not known"))

    monkeypatch.setattr(cite, "open_url", unknown)
    with pytest.raises(urllib.error.URLError):
        cite.lookup_doi("10.1000/x", cache)


# ---------- robots.txt ----------


def fetch_page(cache, url):
    return cite.get(url, cache, "document", cite.document)[1]


def test_robots_txt_rules_for_any_of_the_tokens_refuse(cache, monkeypatch):
    for robots in (
        b"User-agent: *\nDisallow: /private\n",
        b"User-agent: Claude-User\nDisallow: /\n\nUser-agent: *\nAllow: /\n",
        b"User-agent: citation-check\nDisallow: /private\n",
    ):
        c = cite.Cache(cache.dir / robots.hex()[:16])
        serve(monkeypatch, {"https://a.example/robots.txt": (200, "text/plain", robots)})
        with pytest.raises(cite.Disallowed, match="robots.txt"):
            fetch_page(c, "https://a.example/private/x")


def test_robots_txt_allows_and_sets_the_interval(cache, monkeypatch, slept):
    robots = b"User-agent: *\nCrawl-delay: 30\nDisallow: /private\n"
    fake = serve(
        monkeypatch,
        {
            "https://a.example/robots.txt": (200, "text/plain", robots),
            "https://a.example/pub": (200, "text/html", WORDS),
        },
    )
    assert fetch_page(cache, "https://a.example/pub").kind == "html"
    assert 29.0 < slept[-1] <= 30.0 and state_of(cache, "a.example")["robots_delay"] == 30.0
    fetch_page(cite.Cache(cache.dir), "https://a.example/pub")
    assert fake.calls.count("https://a.example/robots.txt") == 1
    meta = meta_of(cache, "https://a.example/robots.txt")
    assert meta["expires_at"] - meta["fetched_at"] == pytest.approx(cite.TTL["robots"])


def test_robots_txt_missing_allows_and_unreachable_refuses(cache, monkeypatch):
    serve(monkeypatch, {"https://a.example/robots.txt": NO_ROBOTS, "https://a.example/x": (200, "text/html", WORDS)})
    assert fetch_page(cache, "https://a.example/x").usable
    serve(monkeypatch, {"https://b.example/robots.txt": (501, "", b"")})
    with pytest.raises(cite.Disallowed, match="HTTP 501"):
        fetch_page(cache, "https://b.example/x")
    serve(monkeypatch, {"https://c.example/robots.txt": (503, {"Retry-After": "3600"}, b"")})
    with pytest.raises(cite.RetryLater):
        fetch_page(cache, "https://c.example/x")


def test_the_apis_are_not_checked_against_robots_txt(cache, monkeypatch):
    fake = serve(monkeypatch, {API_URL: (200, ATOM, ONE_ENTRY), OPENALEX_URL: (200, JSON, OPENALEX_WORK)})
    cite.lookup_arxiv("2010.05513", cache)
    cite.openalex_work("10.1000/x", cache)
    assert fake.calls == [API_URL, OPENALEX_URL]


# ---------- redirects and addresses ----------


def test_each_redirect_hop_is_checked_as_the_first(cache, monkeypatch):
    fake = serve(
        monkeypatch,
        {
            "https://a.example/robots.txt": NO_ROBOTS,
            "https://b.example/robots.txt": (200, "text/plain", b"User-agent: *\nDisallow: /no\n"),
            "https://a.example/x": (302, {"Location": "https://b.example/y"}, b""),
            "https://b.example/y": (200, "text/html", WORDS),
            "https://a.example/to-no": (301, {"Location": "https://b.example/no"}, b""),
            "https://a.example/to-file": (302, {"Location": "file:///etc/passwd"}, b""),
            "https://a.example/to-metadata": (302, {"Location": "http://169.254.169.254/latest"}, b""),
            "https://a.example/loop": (302, {"Location": "/loop"}, b""),
        },
    )
    reply, doc = cite.get("https://a.example/x", cache, "document", cite.document)
    assert doc.usable and cite.report([reply])["read_at"] == "https://b.example/y"
    assert {"a.example", "b.example"} <= {p.stem for p in (cache.dir / "state").glob("*.json")}
    with pytest.raises(cite.Disallowed):
        fetch_page(cache, "https://a.example/to-no")
    with pytest.raises(cite.Unsafe, match="not an http"):
        fetch_page(cache, "https://a.example/to-file")
    with pytest.raises(cite.Unsafe, match="not a public address"):
        fetch_page(cache, "https://a.example/to-metadata")
    with pytest.raises(cite.http.client.HTTPException, match="more than 5 redirects"):
        fetch_page(cite.Cache(cache.dir), "https://a.example/loop")
    assert "file:///etc/passwd" not in fake.calls  # refused before any request


def test_a_name_resolving_to_a_private_address_is_refused(cache, monkeypatch, capsys, tmp_path):
    monkeypatch.setattr(cite, "addresses", lambda host, port: ["93.184.216.34", "10.0.0.7"])
    code, out = run(monkeypatch, capsys, "fetch-text", "--url", "https://intranet.example/x", "--out", str(tmp_path))
    assert code == 2 and "not a public address" in out["error"]


def test_the_opener_speaks_http_only_follows_no_redirect_and_names_the_project(monkeypatch):
    with pytest.raises(urllib.error.URLError, match="unknown url type"):
        cite.OPENER.open("file:///etc/hostname")
    sent = []

    def https_open(self, req):
        """The connection: a 302 from a.example, a page from anywhere else."""
        sent.append(req)
        headers = http.client.HTTPMessage()
        redirect = req.full_url == "https://a.example/"
        if redirect:
            headers["Location"] = "https://b.example/"
        body, status, reason = (b"", 302, "Found") if redirect else (b"page", 200, "OK")
        response = urllib.response.addinfourl(io.BytesIO(body), headers, req.full_url, status)
        response.msg = reason
        return response

    monkeypatch.setattr(urllib.request.HTTPSHandler, "https_open", https_open)
    status, headers, body = REAL_OPEN_URL("https://a.example/", 100)
    assert (status, headers.location, body) == (302, "https://b.example/", b"")
    assert [req.full_url for req in sent] == ["https://a.example/"]  # the redirect is left to `fetch`
    agent = sent[0].get_header("User-agent")
    assert agent.startswith("citation-check ") and "https://github.com/" in agent


def test_fetch_takes_http_only_and_bounds_the_answer(cache, monkeypatch, capsys, tmp_path):
    code, out = run(monkeypatch, capsys, "fetch-text", "--url", "file:///etc/hostname", "--out", str(tmp_path / "t"))
    assert code == 2 and out["status"] == "error" and "not an http(s) URL" in out["error"]
    assert not list(cache.dir.glob("state/*.lock"))  # no lock file for an empty host name
    serve(monkeypatch, {ROBOTS_URL: NO_ROBOTS, PDF_URL: (200, "application/pdf", b"%PDF-" + b"x" * 64)})
    monkeypatch.setattr(cite, "MAX_BODY", cite.MAX_BODY | {"document": 32})
    cite.cache_dir(cache)
    with pytest.raises(cite.Oversize, match="larger than"):
        cite.get(PDF_URL, cache, "document", cite.document)
    assert not cached(cache, PDF_URL)
    assert cite.read_body(_Body(b"x" * 100), 10, truncate=True) == b"x" * 10  # robots.txt: cut, not refused


# ---------- what is accepted ----------


def test_an_answer_not_in_the_api_format_is_not_kept(cache, monkeypatch):
    fake = serve(
        monkeypatch,
        {
            CROSSREF_URL: (200, "text/html", b"<html>Just a moment...</html>"),
            API_URL: (200, "text/html", b"<html>Service unavailable<br></html>"),
        },
    )
    cite.cache_dir(cache)
    with pytest.raises(cite.Malformed):
        cite.lookup_doi("10.1000/x", cache)
    with pytest.raises(cite.Malformed):
        cite.lookup_arxiv("2010.05513", cache)
    for url in (CROSSREF_URL, API_URL):
        assert not cached(cache, url)
    assert len(fake.calls) == 2


def test_a_malformed_crossref_answer_does_not_stop_the_arxiv_search(cache, monkeypatch, capsys):
    bad = {"status": "ok", "message-type": "work-list", "message": {"items": [{"DOI": "10.1000/x", "author": ["X"]}]}}
    search = "https://api.crossref.org/works?query.bibliographic=A+title&rows=5&query.author=A.+Author"
    arxiv = "https://export.arxiv.org/api/query?search_query=ti%3Atitle+AND+au%3Aauthor&max_results=5"
    serve(monkeypatch, {search: (200, "application/json", json.dumps(bad).encode()), arxiv: (200, ATOM, ONE_ENTRY)})
    code, out = run(monkeypatch, capsys, "lookup", "--title", "A title", "--authors", "A. Author", "--year", "2020")
    assert code == 0 and out["status"] == "match" and out["candidates"][0]["source"] == "arxiv"
    assert out["errors"][0].startswith("search_crossref:") and not cached(cache, search)


def test_xml_with_a_dtd_is_refused(cache, monkeypatch):
    attacks = [
        (
            b'<?xml version="1.0"?><!DOCTYPE feed [<!ENTITY x SYSTEM "file:///etc/passwd">]>'
            b'<feed xmlns="http://www.w3.org/2005/Atom"><entry><title>&x;</title></entry></feed>'
        ),
        (
            b'<?xml version="1.0"?><!DOCTYPE feed [<!ENTITY a "aaaaaaaaaa"><!ENTITY b "&a;&a;&a;&a;&a;&a;&a;&a;">]>'
            b'<feed xmlns="http://www.w3.org/2005/Atom"><title>&b;</title></feed>'
        ),
        b'<?xml version="1.0"?><!DOCTYPE feed [<!ENTITY t "Fake Title">]>' + ONE_ENTRY.split(b"?>", 1)[1],
    ]
    for body in attacks:
        reply = cite.Reply(API_URL, 200, ATOM, body, time.time(), False)
        with pytest.raises(cite.Malformed):
            cite.arxiv_feed(reply)


def test_crossref_answers_are_validated(cache):
    def work(message):
        body = json.dumps({"status": "ok", "message-type": "work", "message": message}).encode()
        return cite.validated(cite.CrossrefWorkAnswer, body, CROSSREF_URL)

    record = work({"DOI": "10.1000/x", "title": ["A  title"], "issued": {"date-parts": [[None]]}}).message.record()
    assert record["title"] == "A title" and record["year"] is None
    for message in ({"DOI": "x"}, {"DOI": "10.1/x", "author": ["X"]}, {"DOI": "10.1/x", "title": "T"}):
        with pytest.raises(cite.Malformed):
            work(message)


def test_the_notices_that_update_a_work_are_reported(cache):
    notices = [
        {"DOI": "10.1000/c", "type": "correction", "label": "Correction", "source": "retraction-watch",
         "updated": {"date-parts": [[2004, 3, 6]]}, "record-id": "1"},
        {"DOI": "10.1000/r", "type": "retraction", "source": "publisher", "updated": {"date-parts": [[2010]]}},
    ]
    record = cite.validated(cite.CrossrefWork, work("10.1000/x", "A title") | {"updated-by": notices}, "w").record()
    assert record["updates"] == [
        {"type": "correction", "label": "Correction", "doi": "10.1000/c", "date": "2004-03-06", "source": "retraction-watch"},
        {"type": "retraction", "label": "", "doi": "10.1000/r", "date": "2010", "source": "publisher"},
    ]
    assert cite.validated(cite.CrossrefWork, work("10.1000/x", "A title"), "w").record()["updates"] == []
    with pytest.raises(cite.Malformed):
        cite.validated(cite.CrossrefWork, work("10.1000/x", "A title") | {"updated-by": [{"type": "x"}]}, "w")


def test_identifiers_going_into_a_path_are_checked(monkeypatch, capsys, tmp_path):
    for good in ("arXiv:2010.05513v2", "math.OA/0601001", "hep-th/9901001v1", "https://arxiv.org/abs/2010.05513"):
        cite.arxiv_id(good)
    for bad in ("../e-print/2101.00001", "2101.00001/../../x", "2101.00001?x=1"):
        with pytest.raises(cite.Refused):
            cite.arxiv_id(bad)
    assert cite.doi("https://doi.org/10.1007/BF01234") == "10.1007/BF01234"
    for bad in ("10.1000/../x", "10.1000/x y", "11.1000/x"):
        with pytest.raises(cite.Refused):
            cite.doi(bad)
    code, out = run(monkeypatch, capsys, "fetch-text", "--arxiv", "../e-print/2101.00001", "--out", str(tmp_path))
    assert code == 1 and out["status"] == "refused"


def test_html_text_is_linear_on_unclosed_tags():
    assert " ".join(cite.html_text(b"<p>a<script>x</script>b<style>y</style>c &amp; d</p>").split()) == "a b c & d"
    start = time.perf_counter()
    cite.html_text(b"text " + b"<script>" * 50_000)
    cite.html_text(b"text " + b"<!--" * 50_000)
    cite.html_text(b"text " + b"<a " * 50_000)
    assert time.perf_counter() - start < 5.0


def test_a_huge_page_is_not_rendered(tmp_path):
    pdf = cite.pdfium.PdfDocument.new()
    pdf.new_page(612, 792)
    pdf.new_page(14400, 14400)
    assert len(cite.render_pages(pdf, [1], tmp_path, "s")) == 1
    with pytest.raises(ValueError, match="pixels"):
        cite.render_pages(pdf, [2], tmp_path, "s")


def test_host_names_are_canonical():
    assert cite.host_key("WWW.arXiv.org.") == cite.host_key("de.arxiv.org") == "arxiv.org"
    assert cite.host_key("export.arxiv.org") == "export.arxiv.org"
    assert cite.host_key("Example.COM") == "example.com"


# ---------- lookup verdicts ----------


SEARCH = "https://api.crossref.org/works?query.bibliographic=A+title&rows=5&query.author=A.+Author"
ARXIV_SEARCH = "https://export.arxiv.org/api/query?search_query=ti%3Atitle+AND+au%3Aauthor&max_results=5"
OTHER_ENTRY = ONE_ENTRY.replace(b"A title", b"Something unrelated").replace(b"A. Author", b"B. Other")
CLAIM = ("--title", "A title", "--authors", "A. Author", "--year", "2020")


def work(doi, title, *authors, editors=()):
    def names(people):
        return [{"given": p.split()[0], "family": p.split()[-1]} for p in people]

    return {
        "DOI": doi,
        "title": [title],
        "author": names(authors),
        "editor": names(editors),
        "issued": {"date-parts": [[2020]]},
    }


def works(*items):
    return (
        200,
        JSON,
        json.dumps({"status": "ok", "message-type": "work-list", "message": {"items": list(items)}}).encode(),
    )


def test_a_search_with_no_candidate_is_asked_again(cache, monkeypatch, capsys):
    fake = serve(
        monkeypatch,
        {SEARCH: works(work("10.1000/z", "Something unrelated", "B. Other")), ARXIV_SEARCH: (200, ATOM, EMPTY_FEED)},
    )
    for _ in range(2):
        code, out = run(monkeypatch, capsys, "lookup", *CLAIM)
        assert code == 0 and out["status"] == "mismatch" and not out["cached"]
    assert len(fake.calls) == 4 and not cached(cache, SEARCH)


def test_a_negative_status_is_never_read_from_the_cache(cache, monkeypatch, capsys):
    fake = serve(monkeypatch, {API_URL: (200, ATOM, ONE_ENTRY)})
    _, out = run(monkeypatch, capsys, "lookup", "--arxiv", "2010.05513", *CLAIM)
    assert out["status"] == "match" and cached(cache, API_URL)
    _, out = run(monkeypatch, capsys, "lookup", "--arxiv", "2010.05513", "--title", "Quite another paper")
    assert out["status"] == "mismatch" and not out["cached"] and len(fake.calls) == 2


def test_the_status_is_the_best_verdict_not_the_closest_title(cache, monkeypatch, capsys):
    namesake = work("10.1000/a", "A title", "B. Other")  # the very title, by other authors
    sequel = work("10.1000/b", "A titles", "A. Author")
    serve(monkeypatch, {SEARCH: works(namesake, sequel), ARXIV_SEARCH: (200, ATOM, EMPTY_FEED)})
    _, out = run(monkeypatch, capsys, "lookup", *CLAIM)
    assert out["status"] == "match" and out["candidates"][0]["id"] == "doi:10.1000/b"


def test_a_failed_search_leaves_a_negative_unproved(cache, monkeypatch, capsys, tmp_path):
    serve(monkeypatch, {SEARCH: (503, {"Retry-After": "3600"}, b""), ARXIV_SEARCH: (200, ATOM, OTHER_ENTRY)})
    _, out = run(monkeypatch, capsys, "lookup", *CLAIM)
    assert out["status"] == "retry-later" and out["host"] == "api.crossref.org" and out["candidates"]
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "other"))
    serve(
        monkeypatch,
        {SEARCH: (200, "text/html", b"<html>Just a moment...</html>"), ARXIV_SEARCH: (200, ATOM, OTHER_ENTRY)},
    )
    _, out = run(monkeypatch, capsys, "lookup", *CLAIM)
    assert out["status"] == "error" and out["errors"][0].startswith("search_crossref:")


def test_an_edited_volume_is_compared_with_its_editors():
    claim = {"title": "A volume", "authors": ["E. Editor"], "year": 2020}
    record = cite.validated(cite.CrossrefWork, work("10.1000/v", "A volume", editors=["E. Editor"]), "w").record()
    assert record["authors"] == [] and record["editors"] == ["E. Editor"]
    assert cite.compare(claim, record)["verdict"] == "match"
    unnamed = cite.compare(claim, record | {"editors": []})
    assert unnamed["verdict"] == "partial" and unnamed["authors_unknown"]


def test_a_doi_crossref_does_not_hold_is_asked_of_its_agency(cache, monkeypatch, capsys):
    datacite = {
        "data": {
            "id": "10.1000/x",
            "type": "dois",
            "attributes": {
                "doi": "10.1000/x",
                "titles": [{"title": "A title"}],
                "creators": [{"name": "Author, A.", "givenName": "A.", "familyName": "Author"}],
                "publicationYear": 2020,
                "publisher": {"name": "arXiv"},
                "types": {"resourceTypeGeneral": "Preprint"},
            },
        }
    }
    fake = serve(
        monkeypatch,
        {
            CROSSREF_URL: (404, "", b""),
            AGENCY_URL: (200, JSON, b'[{"DOI": "10.1000/x", "RA": "DataCite"}]'),
            DATACITE_URL: (200, JSON, json.dumps(datacite).encode()),
            "https://api.crossref.org/works/10.1000/y": (404, "", b""),
            "https://doi.org/doiRA/10.1000/y": (200, JSON, b'[{"DOI": "10.1000/y", "RA": "JaLC"}]'),
        },
    )
    code, out = run(monkeypatch, capsys, "lookup", "--doi", "10.1000/x", *CLAIM)
    assert code == 0 and out["status"] == "match" and out["candidates"][0]["source"] == "datacite"
    assert out["candidates"][0]["container"] == "arXiv"
    assert fake.calls == [CROSSREF_URL, AGENCY_URL, DATACITE_URL]
    code, out = run(monkeypatch, capsys, "lookup", "--doi", "doi:10.1000/y", *CLAIM)
    assert code == 0 and out["status"] == "registered" and out["agency"] == "JaLC"
    assert out["url"] == "https://doi.org/10.1000/y"


def test_copies_lists_the_versions_openalex_knows(cache, monkeypatch, capsys):
    fake = serve(monkeypatch, {OPENALEX_URL: (200, JSON, OPENALEX_WORK)})
    code, out = run(monkeypatch, capsys, "copies", "--doi", "https://doi.org/10.1000/x")
    assert code == 0 and out["status"] == "ok" and out["title"] == "A title" and out["is_retracted"] is False
    assert out["best"]["pdf_url"] == "https://arxiv.org/pdf/1000.00001" and out["best"]["version"] == "submittedVersion"
    assert [c["version"] for c in out["copies"]] == ["publishedVersion", "submittedVersion"]
    assert out["copies"][0]["source"] == "A Journal" and out["copies"][0]["source_type"] == "journal"
    code, out = run(monkeypatch, capsys, "copies", "--doi", "10.1000/x")
    assert code == 0 and out["cached"] and len(fake.calls) == 1
    serve(monkeypatch, {OPENALEX_URL: (200, "text/html", b"<html>Just a moment...</html>")})
    monkeypatch.setattr(cite, "read_entry", lambda url, cache: None)
    code, out = run(monkeypatch, capsys, "copies", "--doi", "10.1000/x")
    assert code == 2 and out["status"] == "error" and out["reason"] == "malformed"
    cite.drop_entry(cache.dir, OPENALEX_URL)
    serve(monkeypatch, {OPENALEX_URL: (404, JSON, b"")})
    code, out = run(monkeypatch, capsys, "copies", "--doi", "10.1000/x")
    assert code == 2 and out["status"] == "not-found" and not cached(cache, OPENALEX_URL)


def test_fetch_text_tells_a_refusal_from_an_outage(cache, monkeypatch, capsys, tmp_path):
    answers = {"https://a.example/robots.txt": NO_ROBOTS}
    cases = [(403, "inaccessible", "refused"), (404, "inaccessible", "not found"), (400, "error", "HTTP 400")]
    cases += [(522, "retry-later", "HTTP 522")]  # last: it holds the host back
    for status, _, _ in cases:
        answers[f"https://a.example/{status}"] = (status, "", b"")
    serve(monkeypatch, answers)
    for status, verdict, reason in cases:
        url = f"https://a.example/{status}"
        code, out = run(monkeypatch, capsys, "fetch-text", "--url", url, "--out", str(tmp_path / "t"))
        assert code == 2 and (out["status"], out["reason"]) == (verdict, reason)


# ---------- the ledger ----------


def test_validate_checks_the_checked_records_without_the_network(tmp_path, monkeypatch, capsys):
    ledger = tmp_path / "checked.yaml"
    checked = (
        "    checked:\n      url: https://a.example/x.pdf\n      locators: {Theorem 1: {page: '3', date: 2026-11-07}}\n"
    )
    ledger.write_text(LEDGER.replace("    relationship: background\n", "    relationship: background\n" + checked))
    monkeypatch.setattr(sys, "argv", ["cite.py", "--ledger", str(ledger), "validate"])
    assert cite.main() == 0
    assert json.loads(capsys.readouterr().out)["status"] == "ok"
    broken = tmp_path / "formalization.yaml"
    broken.write_text("sources:\n  - id: doi:10.1000/x\n    checked:\n      locators: {Theorem 1: {page: '3'}}\n")
    monkeypatch.setattr(sys, "argv", ["cite.py", "--ledger", str(broken), "validate"])
    assert cite.main() == 1
    problems = json.loads(capsys.readouterr().out)["problems"]
    assert problems == ["doi:10.1000/x: checked.url missing", "doi:10.1000/x / Theorem 1: date missing"]


LEDGER = """\
# A comment before everything.
version: v0.4
project:
  name: Demo  # a comment on a key

sources:
  - title: A paper on well known results
    authors: [A. Author]
    id: doi:10.1000/x
    type: article
    relationship: background

# A comment before the next section.
review:
  status: none
"""


def add(monkeypatch, capsys, tmp_path, ledger, record, *extra):
    record_file = tmp_path / f"r{len(list(tmp_path.glob('r*.json')))}.json"
    record_file.write_text(json.dumps(record))
    return run(monkeypatch, capsys, "--ledger", str(ledger), "ledger", "add", "--json", str(record_file), *extra)


def test_ledger_add_keeps_comments_and_the_url_each_locator_was_read_at(monkeypatch, capsys, tmp_path):
    ledger = tmp_path / "formalization.yaml"
    ledger.write_text(LEDGER)
    src = {"id": "doi:10.1000/X", "title": "A paper on well known results"}
    one = {
        "source": src,
        "url": "https://a.example/x.pdf",
        "locator": {"location": "Theorem 1", "page": 3, "date": "2026-11-07"},
    }
    two = {
        "source": src,
        "url": "https://b.example/x.pdf",
        "locator": {"location": "Lemma 2", "page": "7", "date": "2026-11-07", "version": "arXiv:1000.00001v3"},
    }
    assert add(monkeypatch, capsys, tmp_path, ledger, one)[0] == 0
    assert add(monkeypatch, capsys, tmp_path, ledger, two)[0] == 0
    text = ledger.read_text()
    for comment in ("# A comment before everything.", "# a comment on a key", "# A comment before the next section."):
        assert comment in text
    assert not [line for line in text.splitlines() if line != line.rstrip()]
    doc, _ = cite.load_ledger(ledger)
    checked = doc["sources"][0]["checked"]
    assert checked["url"] == "https://a.example/x.pdf"
    assert dict(checked["locators"]["Theorem 1"]) == {"page": "3", "date": "2026-11-07"}
    assert dict(checked["locators"]["Lemma 2"]) == {
        "page": "7",
        "date": "2026-11-07",
        "version": "arXiv:1000.00001v3",
        "url": "https://b.example/x.pdf",
    }
    assert len(doc["sources"]) == 1


def test_ledger_add_refuses_a_title_listed_under_another_id(monkeypatch, capsys, tmp_path):
    ledger = tmp_path / "formalization.yaml"
    ledger.write_text(LEDGER)
    record = {
        "source": {"id": "https://landing.example/x", "title": "A paper on well-known results"},
        "url": "https://a.example/x.pdf",
        "locator": {"location": "Theorem 1", "page": "3", "date": "2026-11-07"},
    }
    code, out = add(monkeypatch, capsys, tmp_path, ledger, record)
    assert code == 1 and out["status"] == "refused" and "doi:10.1000/x" in out["error"]
    assert ledger.read_text() == LEDGER
    assert add(monkeypatch, capsys, tmp_path, ledger, record, "--new-source")[0] == 0
    assert len(cite.load_ledger(ledger)[0]["sources"]) == 2
    assert "\n  - title: A paper on well-known results\n    id: https://landing.example/x\n" in ledger.read_text()


def test_ledger_add_takes_the_entry_for_its_location(monkeypatch, capsys, tmp_path):
    ledger = tmp_path / "formalization.yaml"
    entry = "  - title: A paper on well known results\n    id: doi:10.1000/x\n    location: {}\n"
    ledger.write_text("sources:\n" + entry.format("Theorem 1") + entry.format("Lemma 2"))
    record = {
        "source": {"id": "doi:10.1000/x", "title": "A paper on well known results"},
        "url": "https://a.example/x.pdf",
        "locator": {"location": "Lemma 2", "page": "7", "date": "2026-11-07"},
    }
    assert add(monkeypatch, capsys, tmp_path, ledger, record)[0] == 0
    first, second = cite.load_ledger(ledger)[0]["sources"]
    assert "checked" not in first and list(second["checked"]["locators"]) == ["Lemma 2"]


def test_failures_are_answered_in_json(monkeypatch, capsys, tmp_path):
    ledger = tmp_path / "formalization.yaml"
    ledger.write_text(LEDGER)
    bad_date = {
        "source": {"id": "doi:10.1000/x", "title": "T"},
        "url": "u",
        "locator": {"location": "Theorem 1", "page": "3", "date": "7 Nov 2026"},
    }
    code, out = add(monkeypatch, capsys, tmp_path, ledger, bad_date)
    assert code == 1 and out["status"] == "refused" and "YYYY-MM-DD" in out["error"]
    no_page = bad_date | {"locator": {"location": "Theorem 1", "date": "2026-11-07"}}
    code, out = add(monkeypatch, capsys, tmp_path, ledger, no_page)
    assert code == 1 and out["error"] == "record: locator.page missing"
    code, out = run(monkeypatch, capsys, "lookup")
    assert code == 1 and out["status"] == "refused"
    ledger.write_text("sources: [unclosed\n")
    code, out = run(monkeypatch, capsys, "--ledger", str(ledger), "validate")
    assert code == 2 and out["status"] == "error"


def test_family_names_agree_in_either_order():
    assert cite.family("van der Waerden, B. L.") == cite.family("B. L. van der Waerden") == "waerden"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
