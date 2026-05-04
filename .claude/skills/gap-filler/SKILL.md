---
name: gap-filler
description: Recursively expand `references/` to cover the prerequisites of a formalization goal. Use this skill whenever the user asks to "fill the gaps", "find prerequisite knowledge", "expand references", "follow citations", "plan a formalization", or says they need to know what is still missing to formalize a topic in Lean 4. Given an existing ingested paper (slug) or a goal description, this skill identifies concepts that are still `→ needs formalization`, ranks the paper's bibliography by in-text centrality, and proposes which sources to ingest next via pdf-to-knowledge (PDFs, arxiv) or web-to-knowledge (Wikipedia, nLab). Do NOT invoke for a single-source ingestion request — those go directly to pdf-to-knowledge or web-to-knowledge. Trigger even when the user does not explicitly say "gap" — e.g. "what else do I need to ingest for Araki relative entropy?" should trigger.
---

# gap-filler

Turn a formalization goal into a bounded recursive ingestion plan and,
with user approval, execute it. Orchestrates the existing
`pdf-to-knowledge` and `web-to-knowledge` skills.

## When to invoke

- The user references an already-ingested slug and asks what else is
  needed: "for the Araki paper I just ingested, what's still missing
  before I can formalize relative entropy?".
- The user states a formalization goal and wants a plan: "plan the
  ingestion to cover the prerequisites of Araki's relative entropy".
- The user wants to "follow the citations" of an ingested paper to pull
  in the most-cited references.

Do **not** invoke for:

- A single PDF / URL ingestion (use the source-specific skill).
- A purely literature-review question with no Lean formalisation
  angle — this skill's mathlib annotation loop makes it Lean-specific.

## Output contract

The skill does not write a new standalone directory. Instead it:

1. Writes a `references/gaps.json` — machine-readable snapshot of the
   current gap situation (resolved / gaps / ambiguous / other_knowledge
   counts per concept).
2. Writes a `references/<slug>/bibliography-ranked.json` — ordered list of
   bibliography entries by in-text citation centrality, with `ingested`
   flags and any arxiv / doi IDs surfaced.
3. Optionally triggers `pdf-to-knowledge` or `web-to-knowledge` to ingest
   top-ranked gaps, then re-runs the concept index and re-scores.

Both JSON files are regenerated on each invocation; they are safe to
commit if you want audit history, or to `.gitignore` for ephemeral runs.

## Workflow

1. **Identify the target.** Pull from the user's message one of:
   - A slug that exists under `references/` (e.g. `arxiv-2202.03357`).
   - A short goal description (e.g. "formalize Araki's relative
     entropy in Lean 4") — in this case ask which existing slug is the
     canonical source, and if none, suggest running `pdf-to-knowledge`
     first.

2. **Detect gaps.**
   ```bash
   python3 .claude/skills/gap-filler/scripts/detect_gaps.py \
       references/ --target-slug <target-slug> --output references/gaps.json
   ```

   When the project has a `goals.yaml` (a fixed list of formalization
   targets — see "Side channels" below), pass
   `--goals goals.yaml --lean-root <Lean tree>` so the report adds
   per-goal status verified against the actual Lean declarations, plus
   `goal_coverage_score = verified_declarations / total_declarations`.
   The plain `coverage_score` keeps its meaning ("ingestion-wide
   knowledge coverage"); use whichever the user asked for. Both can
   appear in the same report.
   The report lists every Key concepts bullet's status across all
   ingested slugs:
   - `formalized` — at least one source annotated
     `→ formalized: QuantumSystem.X.y` (a local proof in this repo) and
     `verify_mathlib_refs.py` did not flag it. Strongest tier; outranks
     `resolved` because a local proof is harder evidence than a mathlib
     match.
   - `resolved` — at least one source annotated `→ mathlib: ...` and
     `verify_mathlib_refs.py` did not flag it as `[UNVERIFIED]`.
   - `suspect` — a source annotated `→ mathlib: ...` but
     `verify_mathlib_refs.py` (run as part of pdf-to-knowledge /
     web-to-knowledge step 4g / 6) could not confirm the declaration
     exists — the annotation has an `[UNVERIFIED]` marker. Treat as a
     stronger signal than `gap`: **the previous search was a false
     positive** and the concept needs either a corrected annotation or
     genuine formalisation.
   - `partial` — target slug still annotates `→ needs formalization`,
     but another ingested slug discusses the concept (e.g. a
     Wikipedia / nLab page). Locally readable even though mathlib
     lacks it. Often the most cost-effective tier to prioritise next.
   - `gap` — target slug annotates `→ needs formalization` and no
     other slug documents the concept. This is where future recursive
     ingestion should focus.
   - `ambiguous` — no annotation (rarely happens if previous
     ingestions followed the SKILL.md contract).
   - `other_knowledge` — concepts coming from non-target slugs (may
     still be useful prerequisites). Its `status` field uses the
     strongest available source-tier vocabulary (`formalized`,
     `resolved`, `suspect`, `gap`, or `ambiguous`), including `suspect`
     when the only known annotation is an `[UNVERIFIED]` false positive.

   When `--goals` is enabled, the goal block introduces two more status
   vocabularies:
   - goal-concept `status` may also be `unknown` — the concept was
     pinned to specific `sources[*].slug` entries, but none of those
     slugs currently document it.
   - goal `goal_status` is one of `satisfied`, `partially_satisfied`,
     `missing`, or `unverified`.

   Concept-name matching is normalised aggressively: `Connes cocycle`,
   `Connes.cocycle`, `ConnesCocycle`, and `connes-cocycle` all merge.
   camelCase / PascalCase identifiers are split on case transitions,
   then lowercased and punctuation-stripped.

   The report also exposes `coverage_score`, a single 0..1 number
   equal to
   `(formalized × 1.0 + resolved × 1.0 + partial × 0.5) / target_total`.
   Use this as the headline progress metric when reporting to the user —
   it captures "local proof + mathlib coverage + local-reference
   coverage" in one figure, so an ingestion that adds 3 Wikipedia pages
   moves the number even when `formalized` and `resolved` stay flat.

3. **Rank the target's bibliography by centrality.**
   ```bash
   python3 .claude/skills/gap-filler/scripts/rank_bibliography.py \
       references/<target-slug>/ --output references/<target-slug>/bibliography-ranked.json
   ```
   The ranking counts how many times each bibliography key is cited in
   `content.md`, weighting the first 30 % of the body double (i.e.
   abstract / intro / early theorems count more than late appendices).
   Already-ingested entries (`ingested: true`) go to the back.

   For each **uninvested entry without arxiv / DOI** — the common case
   for operator algebra, older physics and pre-2000 math — the script
   also emits `suggested_search_queries`. The ordering switches on
   publication year (`year >= 1995` favours university-domain PDFs;
   `year < 1995` favours `lecture-notes` + NUMDAM / Project Euclid).
    See [./references/workflow.md](./references/workflow.md) for the
    calibration story and a concrete sample of the emitted queries.

4. **Synthesise a plan.** Read both JSON files and compose a **short
   ingestion plan**:

   a. For each gap concept, decide a primary source in this order:

      1. **arxiv / DOI in the bibliography** — top of the ranked list
         with a discoverable URL → `pdf-to-knowledge`.
      2. **University lecture-notes PDF** — when the entry has no arxiv
         ID but the topic is covered in standard graduate curricula
         (subfactor theory, modular theory, KMS states, entropy
         inequalities). Feed the `suggested_search_queries` to
         `WebSearch`, pick the most reputable PDF hit (faculty page >
         course page > personal blog), hand it to `pdf-to-knowledge`.
         For math-heavy gaps lecture notes usually beat Wikipedia
         (single author, coherent notation); see
         [./references/workflow.md](./references/workflow.md) for the
         comparison.
      3. **Wikipedia / nLab** — good for broadly-known math
         (`Von_Neumann_entropy`, `Tomita–Takesaki_theory`) and as a
         zero-effort fallback when the lecture-notes search returns
         nothing → `web-to-knowledge`.
      4. **Needs human action** — no URL discoverable via the above;
         ask the user.

   b. **Bound the plan**. By default pick at most 3 ingestions per
      invocation to avoid runaway recursion. Increase only when the user
      explicitly opts in.
   c. Present the plan to the user before executing — list the 3
      proposed ingestions with their rationale (gap they close, citation
      score if applicable, source type, URL found via which search
      strategy).

5. **Execute (with user OK).** For each approved entry in the plan:
   - If the source is an arxiv ID: invoke `pdf-to-knowledge` with
     `https://arxiv.org/pdf/<id>`.
   - If the source is a DOI with a direct open PDF URL, or an open-access
     publisher PDF URL discovered from that DOI: invoke `pdf-to-knowledge`
     with the PDF URL. If only a DOI landing page is available, ask before
     using a weaker HTML fallback.
   - If the source is a discovered university / course / faculty PDF URL:
     invoke `pdf-to-knowledge` with that PDF URL.
   - If the source is a Wikipedia / nLab URL: invoke
     `web-to-knowledge` with that URL.
   - After **each** ingestion, re-run
     `python3 .claude/skills/pdf-to-knowledge/scripts/update_concepts.py references/`
     so `CONCEPTS.md` and downstream diagnostics stay consistent.

6. **Re-measure and report.** Re-run step 2 to produce a new
   `gaps.json`, then report the delta to the user: how many gaps closed,
   how many remain, which ones might require a different source type.
   Do not loop automatically — hand control back to the user and wait
   for them to approve another round.

## Side channels

Three optional outputs that complement `gaps.json`. Every one has a
worked example in [./references/workflow.md](./references/workflow.md);
the summary below gives just the contract.

- **`references/gaps-history.jsonl`** — append-only JSONL, one record per
  `detect_gaps.py` run with `timestamp / coverage_score /
  goal_coverage_score / counts / issues_open`. Use it to attribute
  progress to specific ingestions. `--no-history` suppresses;
  `--history-log <path>` redirects.

- **`references/issues/*.yaml`** — file-system tracker for items the
  pipeline could not auto-resolve (`[UNVERIFIED]` mathlib refs, skipped
  notation candidates, open questions). `verify_mathlib_refs.py
  mark-unverified` opens these automatically (idempotent on
  `kind + slug + concept + candidate`); manual ones go through
  `scripts/issues.py {add,list,close}`. `detect_gaps.py` reports
  `issues.open` in its summary.

- **`goals.yaml`** (project root, checked into git) — pins the
  formalization targets so the headline metric tracks "what we promised
  to prove", not "what we happened to ingest". Pass
  `--goals goals.yaml --lean-root <Lean tree>` to `detect_gaps.py`.

  **Truth source = `declarations`.** Each goal lists fully-qualified
  Lean declaration names (`Matrix.vonNeumannEntropy_nonneg`,
  `gelfand_naimark_theorem`, …). The script walks `<lean-root>/**/*.lean`,
  builds the set of every `theorem`/`def`/`structure`/`class`/
  `instance`/`inductive`/`abbrev`/`axiom` (tracking `namespace`/`end`
  stacks), and compares. Verified ⇒ goal counted toward
  `goal_coverage_score`. Without `--lean-root`, declarations are
  reported as `unverified` (no guess).

  Malformed goal entries are a hard error, not a soft fallback: missing
  `id` / `description`, non-list `declarations` / `concepts`, or a
  structured `sources:` entry without a `slug` makes `detect_gaps.py`
  exit 2 with an `[error] invalid goals file: ...` message.

  **`concepts` is informational** — prerequisite knowledge hints used
  by `gap-filler`'s plan output, not by the satisfaction judgement. A
  concept may be a bare string (any INDEX.md mentioning it counts) or
  a structured entry pinning the prerequisite to specific slugs and
  optional anchors:

  ```yaml
  goals:
    - id: gns-construction
      description: "Cyclic representation π_ω …"
      declarations:
        - GNS.Representation
        - GNS.Construction.isFaithful_iff_separating
      concepts:
        - GNS representation                          # bare string
        - name: Tomita-Takesaki modular operator      # structured
          sources:
            - { slug: arxiv-2507.00900, anchor: { theorem: "2.3" } }
            - { slug: "92737", anchor: { definition: "modular operator" } }

    - id: ssa-abstract-local-net
      description: "TODO."
      declarations: []                                # → counts as 1 missing
      concepts:
        - name: localNet
          sources:
            - { slug: "92737" }
  ```

  `anchor` is a single-key map keyed by the locator kind
  (`chapter` / `section` / `subsection` / `theorem` / `definition` /
  `lemma` / `proposition` / `corollary` / `equation` / `page` /
  `example`). It is human-readable navigation; the matcher only uses
  `slug` for filtering.

  **Coverage formula.** `goal_coverage_score =
  verified_declarations / total_declarations`, where a goal with
  `declarations: []` contributes 1 to the denominator (an unfulfilled
  TODO slot, so the score does not silently inflate).

## Why this design

- **Bounded, user-visible plan.** Gap-filling has blast radius (each
  ingestion is multi-minute CPU work plus disk space). Showing the 3
  proposed sources before executing lets the user redirect instead of
  burning compute on the wrong path.
- **Citation centrality, not just "first in list".** The original user
  request specifically called out the heuristic: *"引用数の上位や参考
  アイデアと引用位置の近さ"* — we implement both via the weighted
  count in `rank_bibliography.py`.
- **Reuse existing skills.** The recursion engine is Claude-orchestrated
  markdown, not a new binary. Adding a source type = teaching Claude to
  dispatch to a different sibling skill, not rewriting a DAG.
- **Concept index is the ground truth.** `CONCEPTS.md` already unifies
  PDF and web sources. Every script here reads from that layer rather
  than re-parsing raw papers.

## Runtime prerequisites

- **Sibling skills available.** `pdf-to-knowledge` and
  `web-to-knowledge` must be installed under `.claude/skills/` with
  their own dependencies in place. This skill does not re-implement
  their work.
- **`uv`** on PATH (same reason as the sibling skills).
- No other Python deps — the scripts here use stdlib only.

## Failure modes to watch for

- **Bibliography is empty or absent.** The target slug's INDEX.md was
  ingested before bibliography extraction was added, or the paper had
  no `## References`. In that case `rank_bibliography.py` returns an
  empty list; pivot to web sources for the identified gaps.
- **Every top-ranked entry lacks a discoverable URL.** Older math papers
  cite each other in print journals. If none of the top entries have
  arxiv / doi, the skill should suggest a Wikipedia article on the
  concept instead of forcing the user to chase a hard-to-find PDF.
- **Recursive cycles.** If paper A cites paper B and B cites A, the
  default budget of 3 ingestions / round prevents a loop.
- **Goal outside the current references set.** If the user provides a
  goal string with no matching slug, instruct them to run
  `pdf-to-knowledge` on a primary source first, then come back here.

See [./references/workflow.md](./references/workflow.md) for a worked
example on the Araki relative-entropy paper, including the expected
`gaps.json` output and a sample 3-step ingestion plan.
