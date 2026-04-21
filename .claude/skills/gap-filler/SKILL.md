---
name: gap-filler
description: Recursively expand `references/` to cover the prerequisites of a formalization goal. Use this skill whenever the user asks to "fill the gaps", "find prerequisite knowledge", "expand references", "follow citations", "plan a formalization", or says they need to know what is still missing to formalize a topic in Lean 4. Given an existing ingested paper (slug) or a goal description, this skill identifies concepts that are still `→ needs formalization`, ranks the paper's bibliography by in-text centrality, and proposes which sources to ingest next via pdf-to-knowledge (PDFs, arxiv) or web-to-knowledge (Wikipedia, nLab). Do NOT invoke for a single-source ingestion request — those go directly to pdf-to-knowledge or web-to-knowledge. Trigger even when the user does not explicitly say "gap" — e.g. "what else do I need to ingest for Araki relative entropy?" should trigger.
---

# gap-filler

Turn a formalization goal into a bounded recursive ingestion plan, then
execute it. Orchestrates the existing `pdf-to-knowledge` and
`web-to-knowledge` skills.

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
   The report lists every Key concepts bullet's status across all
   ingested slugs:
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
     still be useful prerequisites).

   Concept-name matching is normalised aggressively: `Connes cocycle`,
   `Connes.cocycle`, `ConnesCocycle`, and `connes-cocycle` all merge.
   camelCase / PascalCase identifiers are split on case transitions,
   then lowercased and punctuation-stripped.

   The report also exposes `coverage_score`, a single 0..1 number
   equal to `(resolved × 1.0 + partial × 0.5) / target_total`. Use
   this as the headline progress metric when reporting to the user —
   it captures "real mathlib coverage plus local-reference coverage"
   in one figure, so an ingestion that adds 3 Wikipedia pages moves
   the number even when `resolved` stays flat.

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
   also emits `suggested_search_queries`. The order depends on the
   entry's publication year:

   - ``year >= 1995``: university-domain PDF rotation first
     (`caltech.edu`, `mit.edu`, `math.berkeley.edu`, `cam.ac.uk`,
     `ihes.fr`, `kurims.kyoto-u.ac.jp`, ...), then `lecture-notes`,
     then `nlab` / `wikipedia`. Matches the iter-2 win of Jones's
     2009 Berkeley lecture notes.
   - ``year < 1995``: `lecture-notes` leads, followed by NUMDAM /
     Project Euclid / open-access-pdf fallbacks, with university
     domains demoted to the tail. The iter-2 eval found that 3
     university domains × 2 legacy entries (PP86, Kos86a) drew zero
     useful hits while `"lecture notes" filetype:pdf` surfaced
     NUMDAM's OA host of PP86 and Carlen's AZ-school notes for
     Kos86a.

   See step 4 for how to consume the queries.

4. **Synthesise a plan.** Read both JSON files and compose a **short
   ingestion plan**:

   a. For each gap concept, decide a primary source in this order:

      1. **arxiv / DOI in the bibliography** — top of the ranked list
         with a discoverable URL → `pdf-to-knowledge`.
      2. **University lecture-notes PDF** — when the bibliography entry
         has no arxiv ID but the topic is covered in standard graduate
         curricula (subfactor theory, modular theory, KMS states,
         entropy inequalities). Use the `suggested_search_queries`
         emitted by `rank_bibliography.py`: feed them to `WebSearch`,
         pick the most reputable PDF hit (faculty page > course page
         > personal blog), hand the URL to `pdf-to-knowledge`.
         **Why this usually beats Wikipedia**: lecture notes are
         written by a single modern author with a coherent narrative,
         whereas Wikipedia articles on advanced operator-algebraic
         topics are often stubs or written by different editors with
         mismatched notation. Do not skip this step for math-heavy
         gaps.
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
- No other Python deps — the two scripts here use stdlib only.

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

See `references/workflow.md` for a worked example on the Araki
relative-entropy paper, including the expected `gaps.json` output and a
sample 3-step ingestion plan.
