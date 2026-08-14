# Building the corpus

How `math-extract` obtains source texts, what each rung costs, and what to do
when one fails. `SKILL.md` step 2 points here; read it when a fetch fails or
when a PDF has to be converted.

Everything lands under `references/<slug>/`, which is gitignored. **The cache is
navigation; the note under `docs/math/` is the product.** Nothing here is a
deliverable and the whole directory may be deleted at any time.

## The ladder

```bash
uv run .claude/skills/math-extract/scripts/ingest.py "<arxiv-id | url | path>"
```

The script walks the rungs in order and stops at the first that yields text. It
prints a JSON summary and exits 0 on success.

| Rung | Source | Faithfulness | Cost |
|---|---|---|---|
| 1 | `arxiv.org/e-print/<id>` — LaTeX | **the original text** | seconds |
| 2 | `arxiv.org/html/<id>` — LaTeXML | high; formulas re-rendered | seconds |
| 3 | any other URL, or a local `.html`/`.txt`/`.tex` | tags stripped | seconds |
| 4 | a PDF through MinerU, with `--allow-mineru` | **model inference, not text** | minutes, serial |
| 5 | not obtainable | — | — |

**Rung 1 is the reason to check arXiv even for a published paper.** The LaTeX
source is what the author wrote, so a quotation taken from it is verbatim by
construction and reaches tier (a) with no further work. Every other rung
produces a derived text.

An arXiv *pdf* URL is not a PDF here: the identifier is recovered from it and
rung 1 runs instead.

## Output

```
references/<slug>/
├── raw/              the bytes as fetched, unmodified
├── source.txt        concatenated text, one line per source line
└── source.flat.txt   the same, each paragraph flattened onto one line
```

**`source.flat.txt` is what the quote check greps.** A sentence in a LaTeX
source is wrapped across several lines, so a verbatim quotation of it matches
nothing in `source.txt`; flattening paragraphs onto single lines is what makes
`grep -F` usable. Measured on `math-ph/0411058`: a real sentence matches in
`source.flat.txt`, fails in `source.txt`, and a sentence with a plausible clause
appended fails in both.

The JSON summary carries `verbatim: true` exactly when the text came from rung 1.
That flag is the input to the tier rule: quotes from a `verbatim` cache are
(a); quotes from any other rung are (b) until checked against the original.

## Exit codes

| Code | Meaning | What to do |
|---|---|---|
| 0 | text cached | proceed |
| 2 | target uninterpretable | fix the argument |
| 3 | every rung failed, or the conversion failed or timed out | record `not retrieved` in `sources.md` with what was tried; every claim resting on the source is capped at tier (d), no locators |
| 4 | fetched but almost no text | treat as not retrieved unless the cache shows otherwise |
| 5 | the source is a PDF and `--allow-mineru` was not given, or was given and `mineru` is not installed | rung 4, below |

A non-zero exit **does not stop the extraction**. It lowers what can be claimed:
the source joins the unfetchable list, and every lane is told that no locator may
be written for it.

## Rung 4 — converting a PDF

**Opt-in per call.** A PDF without the flag exits 5 and states what the
conversion would cost; the script never installs the converter for you.

```bash
uv run .claude/skills/math-extract/scripts/ingest.py <file.pdf> --allow-mineru
uv run .claude/skills/math-extract/scripts/ingest.py <file.pdf> --allow-mineru --pages 40-62
```

The converter installs with a plain `uv sync` — it is the `mineru` dependency
group in `pyproject.toml`, which is in `default-groups`. To skip it deliberately,
`uv sync --no-group mineru` drops ~100 packages including torch.

The script takes the largest Markdown file MinerU produces and writes
`source.txt` and `source.flat.txt` from it exactly as for the other rungs — so
the quote check works the same way. The JSON summary comes back with
`verbatim: false`, the `backend` used, and a `caveat` field spelling out the
tier consequence.

### GPU

The devcontainer passes the host GPU through. **The setting takes effect on a
container rebuild**; the post-rebuild verification procedure lives in
`.devcontainer/gpu-verification.md` and is deliberately self-contained.

- **The default backend stays `pipeline` even on GPU.** torch picks up CUDA by
  itself, so pipeline gets the speedup with no configuration and cannot OOM the
  way the VLM backends can.
- `--backend hybrid-engine --effort high` opts into the higher-accuracy VLM
  path. **This machine's 8GB of VRAM is that backend's minimum, shared with the
  Windows desktop** — on `CUDA out of memory`, drop the flag and rerun; the
  pipeline result is the fallback, not a failure.
- Models survive rebuilds in the `hf-models` named volume, and
  `mineru-models-download` fetches them ahead of time. The devcontainer pins the
  origin (see its comment on `MINERU_MODEL_SOURCE`); to fetch from elsewhere
  once, prefix the single command — `MINERU_MODEL_SOURCE=modelscope mineru …` —
  rather than unpinning.

Things that are easy to get wrong, and cost a lot when got wrong:

- **The script always passes `-b` explicitly.** MinerU 3.x defaults to
  `hybrid-engine`, which is the wrong default at 8GB of shared VRAM.
- **Install `mineru[pipeline,vlm]`, not `mineru[all]`.** The `all` extra pulls
  in vllm, lmdeploy and mlx — serving stacks that are useless here and large.
  `[core]` would also work but drags in gradio.
- **`--pages START-END` takes a page range.** Converting the twenty pages that
  matter instead of a four-hundred-page book is the difference between minutes
  and an afternoon. Use it.
- `-f/--formula` and `-t/--table` are already on by default. Leave `-l` unset:
  the language is detected, and the option's value list does not include a plain
  English code.
- **Conversion is serial.** Concurrent runs hit the per-task timeout and fail.
  This is why step 2 of the skill builds the corpus before dispatching lanes,
  and why the lane briefs say *do not run the converter*.
- Roughly seven minutes for eighteen pages on CPU, far less on GPU; a long
  paper on CPU is half an hour. **Four or more PDFs means telling the user the
  estimate first.**
- The container already has `libgl1` and `libglib2.0-0`, which MinerU's OpenCV
  dependency needs.

**A converted PDF is model output, not text.** MinerU's formula recognition can
produce plausible, wrong LaTeX, and presenting that as a verbatim quotation is
the worst failure this skill has. A quote from converted Markdown is tier (b)
with `mineru-unchecked` attached, and reaches (a) only after being compared
against the page image. Measured example: on a five-page paper set in Knuth's
small-caps font, the CPU pipeline rendered the byline as
`D<sub>on</sub> K<sub>nu</sub>th` — ordinary body text and formulas came out
clean, but unusual typography gets mangled silently.

## What is deliberately not used

- **`pymupdf`, `poppler`, `marker-pdf`** — license-incompatible with this
  project. This also means the `Read` tool cannot open PDFs here: it shells out
  to `pdftoppm`, which is part of poppler and is not installed.
- **Docling** — its formula model makes no useful progress on CPU, and without
  it every equation comes out as a placeholder. For a mathematics corpus that is
  the whole content.
- **MinerU's Python API** — the CLI is the stable interface; importing the
  library pulls in a far heavier dependency graph.

Recording this here is the point: the next person to look for a PDF converter
should find out in one place what was already tried and why it was rejected.

## Rate limits and manners

arXiv asks for roughly one request every three seconds. The script is serial and
the skill fetches the whole corpus in one pass before dispatching, so this takes
care of itself — but a lane that decides to fetch on its own can violate it. The
lane briefs say to read the cache instead, for this reason as well as the
converter's.
