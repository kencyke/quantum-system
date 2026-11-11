# lean-formalization

Claude Code skills and agents for formalizing mathematics in Lean 4.

## Skills

- `/lean-formalization:math-review [path | dir | main...HEAD]` — reviews the current change (or the
  named target) through parallel `math-reviewer` agents, one per perspective: statement fidelity,
  checked against a blind readback of each claim by a `statement-reader` agent; deferred hypotheses;
  conformance with the abstract setting and the literature; notation, naming and docs;
  counterexample models and vacuity. Read-only: it reports findings and proposed fixes, and applies
  none. It leaves literature citations to `citation-check`.
- `/lean-formalization:citation-check [path | dir | main...HEAD]` — checks every literature citation
  in the target, Lean sources, documentation and BibTeX files alike, against its source; corrects the citations
  shown wrong, removes those that cannot stand, records the verified ones in the project's
  ledger, and reports the retraction, correction and expression-of-concern notices that Crossref and
  OpenAlex list for a cited work (reported only, never acted on). It writes to the working tree.
- `/lean-formalization:lint-fix [path | dir | main...HEAD]` — applies the Mathlib-style lint rules
  and the project's own rules to the change, verifies with `lake build`, and reports what it
  deliberately left alone. It writes to the working tree.

The `math-reviewer` agent's description asks Claude Code to use it proactively, whenever a theorem is
stated or proved or an important structure is added; installed at user scope, that applies in every
Lean project.

## Project conventions the skills read

The skills read the project's instruction file (`CLAUDE.md` or `AGENTS.md`), and it overrides their
defaults:

- **Review policy.** `math-review` judges findings and fixes by four defaults, stated in
  `agents/math-reviewer.md`: prove what is provable instead of deferring it to a hypothesis, state
  objects at the generality of the literature, use the library's object instead of bridging to a
  local copy, and raise the code to its docs rather than trimming the docs. A different policy in
  the instruction file governs.
- **Domain models and conventions.** `math-review` also instantiates the degenerate models and checks
  the conventions that the instruction file lists for the project's domain.
- **Citation rule.** `citation-check` counts a citation as verified by the standard in
  `agents/citation-verifier.md` — the cited passage was read and states what the text attributes to
  it — and by the instruction file's own citation rule where it states one. Whatever the rule, a
  citation whose source it cannot read is kept and reported as unverified, with no recommendation:
  the user may hold a copy it cannot reach. It deletes such a citation only when the user asks.
- **Lint rules.** `lint-fix` applies `skills/lint-fix/references/rules.md` together with the rules
  file the instruction file names; the project's rules win where the two differ.

The headings are free; the skills look for the content. An instruction file that sets the last three
reads, for example:

```markdown
## Lint Rules

The project's own rules — prohibited tokens, pinned files, commit style, the line limit — live in
`docs/style.md`, on top of the generic rules that ship with the `lint-fix` skill.

## Mathematical Review

`/math-review` checks the following on top of its generic models and conventions:

- Degenerate models: a measure space with a single atom.
- Conventions to pin in the module doc: whether measures are normalised to probability measures.

## Citations

A citation names the edition it was checked in; a locator read in another edition does not count.
```

## Requirements

- the [lean-lsp MCP server](https://github.com/oOo0oOo/lean-lsp-mcp), registered under the name `lean-lsp`
  (`claude mcp add --scope user lean-lsp -- uvx lean-lsp-mcp`): the skills and agents reach its tools
  under that name only. Without them, `math-review` and the `math-reviewer` agent stop, and `lint-fix`
  writes no docstring and renames nothing, and reports those fixes as left alone;
- [uv](https://docs.astral.sh/uv/), which runs the bundled citation script; the script needs Python 3.12
  or later, which `uv` downloads when the machine has none, and a POSIX system (Linux, macOS, WSL) for
  its file locks — it does not run on native Windows;
- with Claude Code's sandbox on, `sandbox.filesystem.allowWrite` must list `~/.cache` (or
  `$XDG_CACHE_HOME`): both `uv` and the citation script write there, and the sandbox allows only the
  working directory and the temporary directory by default. On a machine without Python 3.12 or later,
  it must list `~/.local/share/uv` as well, where `uv` installs the Python it downloads.

The skills also use the following when the project has them, and skip the check otherwise:

- a `lintDriver` in the lakefile, for `lake lint`;
- Mathlib's `mk_all`;
- commitizen;
- a `formalization.yaml` ledger of checked citations;
- a lint rules file named by `CLAUDE.md` or `AGENTS.md`.

## Install

```text
/plugin marketplace add kencyke/quantum-system
/plugin install lean-formalization@quantum-system
```

From a shell, `claude plugin install lean-formalization --marketplace kencyke/quantum-system` adds the
marketplace and installs the plugin in one step.

The plugin carries no `version`: its version is the last commit that touched `plugins/lean-formalization/`,
so `claude plugin update` fetches every change to the plugin and ignores the rest of the repository.

Before publishing a change, validate the plugin and the marketplace from the repository root:

```text
claude plugin validate ./plugins/lean-formalization && claude plugin validate .
```

## Citation ledger

`skills/citation-check/scripts/cite.py` fetches sources, checks bibliographic metadata, and keeps the
ledger of checked citations in the project's `formalization.yaml`, under a `checked` key of each
source, this plugin's extension of the format, which the format's schema admits since it allows extra
keys: the URL read and, per locator, the page, the date, the version of the work that page number belongs
to (`version`, optional) and, when that locator was read in another copy, its URL. Its `validate` checks
the `checked` records only; checking the file against the format's schema is
the project's own business (a `yaml-language-server` `$schema` line in the file, or a CI step). Run it
with `uv run <path to cite.py> --help`. Writing the ledger keeps
its comments; long lines of text may be rewrapped.

Where the script goes is limited by `skills/citation-check/citation-check.toml`, bundled with the skill,
and by the project's own file of that name at the root of its git work tree, which adds hosts to the
bundled list and replaces an entry of the same name (`--config` names one file to read instead of both).
A project's hosts go in its own file: the bundled one is replaced when the plugin is updated.

```toml
[hosts."arxiv.org"]                                  # also covers its subdomains
terms = "https://info.arxiv.org/help/robots.html"    # the site's terms, as read
reviewed = 2026-11-10                                # the date they were read
# interval = 10                                      # seconds between requests, when the terms set one
```

A host is listed only after its terms of use were read and allow fetching single documents for research;
each entry names the page read and its date, and a configuration with a host lacking them stops every
fetch, as does one that is missing or cannot be read. The bibliographic APIs the script queries are always
allowed. Any other request, every redirect hop included, goes only to a listed host; elsewhere the script
answers `not-allowed` without making a request, and the `citation-check` skill keeps such a citation as
unchecked rather than removing it. An entry's `interval` holds over the host and its subdomains together.
Beyond robots.txt's rules, the script honours its `Content-Signal` line: `ai-input=no` or `use=immediate`,
set for the script's own token or for `Claude-User` (for `*` where a token has no group of its own),
refuses the fetch.

The script's dependencies are pinned, with hashes, in `cite.py.lock` next to it, which `uv run`
follows; `uv lock --script <path to cite.py> --upgrade` refreshes it.

The script is a polite client, and its `--help` text is the one statement of how it treats the sources and
of what it caches where. Its cache is not under the plugin's own data, so delete it before uninstalling the
plugin; `--help` names the directory.
