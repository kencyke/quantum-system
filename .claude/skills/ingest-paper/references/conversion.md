# Conversion reference

Read this only when the `convert.py` command errors, the output layout needs
tweaking, or you are debugging a bad conversion. The happy path needs nothing
here.

## Output contract

Everything lands under `<output-dir>/<slug>/` (default `references/<slug>/`,
which this project keeps in `.gitignore`):

```
references/<slug>/
├── INDEX.md      # metadata frontmatter + Summary + Key concepts + Contents (you fill 2 sections)
├── content.md    # present when page count <= max-pages-per-section (default 20)
├── sections/     # present instead of content.md when pages > threshold AND the PDF has top-level headings
│   ├── 01-<title>.md
│   └── ...
├── assets/       # only images actually referenced from the Markdown, rewritten as assets/...
│   └── image_*.jpg
└── mineru-raw/   # only when --keep-raw is passed; debugging artefacts, not for agents
```

`INDEX.md` frontmatter carries `title`, `source`, `pages`, `slug`, `assets`.
`content.md`/`sections/` and `assets/` are read directly by any later agent
without re-running the conversion.

## All flags

- `--output-dir <dir>` — parent of `<slug>/`. Default `references/`.
- `--slug <name>` — override the derived slug. arXiv IDs are auto-preserved
  (`arxiv-2202.03357`); other sources slugify the filename.
- `--max-pages-per-section N` — split threshold (default 20). Leave alone unless
  asked.
- `--ocr` — MinerU OCR mode for scanned PDFs. Default `auto` picks text
  extraction when a text layer exists. OCR adds minutes — confirm before using.
- `--keep-raw` — keep MinerU's auxiliary outputs (middle.json, layout.pdf, etc.)
  under `mineru-raw/`. Several MB; off by default.

## Runtime prerequisites

- **`uv`** on `PATH`. The script is stdlib-only but runs under `uv run` for
  invocation hygiene.
- **`mineru` CLI** on `PATH`. One-off install: `uv tool install "mineru[all]"`
  (~4 GB of packages + model weights on first run; cached afterwards).
- **Disk + memory.** Budget ~4 GB for the tool environment; per-paper runtime
  memory peaks at 3–4 GB.
- **GPU (optional).** When `nvidia-smi` reports a working GPU the script switches
  MinerU to its `hybrid-auto-engine` backend (much faster on formula
  recognition). Otherwise it silently uses CPU `pipeline`. No flag needed.

## Failure modes

- **Download error** — script exits non-zero; ask the user for a local path.
- **Scanned PDF (no text layer)** — output Markdown is nearly empty; re-run with
  `--ocr` after confirming with the user.
- **>20 pages but no top-level headings** — falls back to a single `content.md`.
  Intentional; do not hand-split.
- **Very large docs (>100 pages)** — first-run CPU conversion takes several
  minutes; warn the user so they do not cancel.
- **Parallel runs on CPU** — MinerU's per-task timeout makes concurrent
  conversions fail. Convert one PDF at a time; a single paper runs ~30–40 min on
  CPU.

## Why MinerU

MinerU's `pipeline` backend decodes every formula (display and inline) to LaTeX
on CPU in minutes and preserves equation numbers via `\tag{...}`. Docling was
dropped earlier: its formula VLM emitted `<!-- formula-not-decoded -->` by
default and the opt-in path was GPU-bound and unusable on CPU. The script shells
out to the `mineru` CLI rather than importing its Python API (more stable, lighter
dependency graph). The agent — not the script — writes Summary and Key concepts,
because summarization and identifier extraction are judgement calls a heuristic
would get wrong often enough to harm.
