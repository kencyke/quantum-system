---
name: math-extract
description: Extract the mathematics of an object from the literature before any Lean is written — definitional variants and their conventions, results and what they rest on, each hypothesis sorted into provable / model-dependent / open, degenerate cases, and rejected formulations with the object that rules each out — via parallel per-lane `math-extractor` sub-agents. Writes a tracked note under docs/math/; proposes no Lean.
argument-hint: "<mathematical object> [-- arXiv id | pdf path | url]"
disable-model-invocation: true
---

Dispatch the extraction to `math-extractor` agents, one per lane, and merge what
they return into one tracked note. The extraction methodology — the lane
definitions, the evidence tiers, the locator rule, the rejection discipline —
lives in `.claude/agents/math-extractor.md`; the note's format lives in
`references/note-format.md`. Never duplicate either here.

**This skill stops at the mathematics.** `references/note-format.md` states what
that bars from the note; step 6 fails the run if any of it reaches the note.

For reviewing Lean that already exists, use `math-review` instead.

## Process

### 1. Pin the object

Take the first non-empty option:

1. An explicit argument — the mathematical object, with optional sources after
   `--`.
2. If none, ask. There is no useful default, and extracting the wrong object
   costs a full run.

Derive `<slug>` in English kebab-case from the object's conventional name
(`split-inclusion`, `umegaki-relative-entropy`). Check whether
`docs/math/<slug>.md` already exists:

- **new** — the note will be created.
- **re-extraction** — read the existing note now. Its `## Rejected
  formulations and refuted claims` and `## Sources` tables are **append-only**
  and must be carried forward verbatim; every other section will be replaced.
  Carry the rejected rows into step 3 as a do-not-re-explore list.

Read `sources.md` (next to this file) as well — you need the retrieval history
and the locator adjudications before you spend time on a source someone already
failed to obtain.

Announce the resolved object, the slug, and new-or-re-extraction before doing
anything else, so a wrong reading costs one word to correct.

*Done when:* the object is stated in one mathematical sentence, the slug is
fixed, the existing note (if any) is in hand, and the announcement is made.

### 2. Scope and build the corpus

**Serial. Do not fan out here.** Two reasons, and both are structural: you
cannot write good lane briefs before you know what the literature looks like,
and the PDF converter fails when several conversions run at once.

Start wide. Read a survey or a recent citing paper first — not to extract from,
but to learn the shape of the field: who defines the object, how many
definitional variants are in circulation, which results matter. This is the
measurement that sizes the run in step 3.

Then obtain the sources, most faithful first. `references/ingestion.md` owns the
ladder, the commands, and the failure modes; read it when a fetch fails. The
short form:

1. arXiv LaTeX source — the original text, formulas exactly as written.
2. arXiv HTML.
3. Any other URL.
4. A PDF through the converter — **slow, serial, and not verbatim**. Opt-in per
   call with `--allow-mineru`, and `--pages START-END` to convert the chapter
   that matters rather than the whole book. The default backend is the CPU/GPU
   pipeline; `--backend hybrid-engine --effort high` opts into the
   higher-accuracy VLM path, which can exhaust this machine's VRAM — on
   `CUDA out of memory`, drop both flags and rerun. Neither choice raises the
   tier: converted text is (b) either way.
5. Not obtainable — record it and move on.

Everything lands in `references/<slug-of-source>/`, which is gitignored and may
be deleted at any time.

Keep two lists as you go: the **corpus** (source key → cache path → how it was
obtained) and the **unfetchable list** (source key → what was tried). Both go to
every lane in step 3. The unfetchable list is what stops a lane from writing a
theorem number for a book nobody opened.

**If four or more PDFs need converting, stop and give the user an estimate
before starting.** Conversion is minutes per paper and cannot be parallelised;
that is the user's time to spend, not yours. Sources reachable as arXiv LaTeX do
not count against this.

*Done when:* the corpus and unfetchable lists are written down, each corpus
entry has a cache path and a provenance, and the scoping read has produced a
first count of definitional variants.

### 3. Size the run and dispatch

Count three numbers from step 2:

- **S** — sources in the corpus.
- **D** — definitional variants sighted.
- **R** — results that will appear in the note.

Read the table top to bottom and take the **first** row whose condition holds.
Largest first, because one number out of range is enough to make a run large:
a corpus of three that disagrees irreconcilably is not a medium run.

| Size | Condition | Lanes |
|---|---|---|
| **large** | D ≥ 3, or S ≥ 4, or R ≥ 9, or the sources disagree irreconcilably | all five, one agent each, plus step 4 |
| **small** | D ≤ 1 and S ≤ 2 and R ≤ 3 | **Do not fan out** — see below |
| **medium** | neither of the above | three agents: **1+2**, **3+4**, **5** |

At **small**, launch a single `math-extractor` with no lane assigned — its agent
file then has it cover all five lanes itself, in 5–15 tool calls. Continue with
steps 5 and 6, and skip step 4.

The pairings are not arbitrary. Lanes 1 and 2 read the same source linearly, so
one agent reading once is cheaper than two. Lanes 3 and 4 both need falsifying
models, and splitting them has two agents construct the same object twice. Lane
5's tools are disjoint from everyone else's.

**Announce the size and the lane set before dispatching**, so a wrong call costs
one word.

Launch all agents in a single message (Agent tool,
`subagent_type: math-extractor`). Write each prompt as a research memo, not a
task ticket. Every prompt must state:

- **the assigned lane by number and name, as a role** — "You are one of N
  lane-specific extractors running in parallel over this object; work lane K
  (<name>) only". Do not restate the lane's definition; the agent file owns it.
- **the object**, in the same one sentence you announced in step 1;
- **the corpus** — source key, cache path, and how it was obtained, for each
  entry. Say plainly: *read these paths; do not run the converter; it fails when
  run concurrently.*
- **the unfetchable list**, with the rule attached: no locator for anything on
  it, and the substitution sentence instead;
- **the relevant rows of `sources.md`**, verbatim — retrieval attempts already
  made and locator adjudications already recorded, as a do-not-repeat list;
- **the rejected rows carried forward** from a previous extraction, as a
  do-not-re-explore list;
- **the absolute path of the notes file** it must append rows to as it goes:
  `<your scratchpad>/math-extract/<slug>/lane-<K>.md`. Pass *your* scratchpad
  path, not the agent's — a file written where you cannot read it is no use when
  the agent dies;
- **your forecast** — what you expect this lane to find, and why. Require the
  agent to **write its own prediction before opening the first source** and to
  report the divergence afterwards. A hit saves a sweep; a miss is itself
  information, and the written prediction is what exposes anchoring;
- **explicit permission to contradict this brief.** "Every branch of the
  forecast was wrong" and "this lane is the wrong lens for this object" are
  findings to report, not failures to apologise for. A lane that believes it
  must confirm the brief will find a way to.

If the platform refuses to launch all of them at once, start as many as it
allows and launch the next as each completes.

**If an agent does not return**, read the notes file you assigned it rather than
dropping its lane. Rows that reached disk are usable; mark the lane partial and
record in `## Not investigated` how far it got.

*Done when:* every lane has completed, or been declared dead with its notes file
recovered.

### 4. Refute

Large runs only. Collect two things: every row at tier **(c)** or **(d)**, and
every `rejected` row whose discriminator looks thin. If there are none, skip.

Launch one further `math-extractor` in the refutation role. Its agent file
defines the outcomes; hand it the rows and the corpus, and require it to attack
the **adopted general form** as well — vacuity at a degenerate model, a standard
object from the literature the form fails to cover, and any hypothesis attached
to it that is actually provable.

Dispositions:

- **refuted** — the row leaves the note, except that a refuted *claim about the
  literature* is recorded in `## Rejected formulations and refuted claims` with
  the evidence that killed it;
- **promoted to (a)/(b)** — the row stays at its new tier;
- **survives at (c)/(d)** — the row stays, marked `unverified`, and may not
  carry the adopted general form on its own;
- **discriminator does not discriminate** — the `rejected` row is demoted to
  `preference-only`, which makes it weightless.

One adversarial pass, not a vote. The tiers already carry the extractor's own
confidence; another vote buys another round of fetching and no new information.

*Done when:* every collected row has exactly one disposition, and the adopted
general form has been attacked on all three fronts.

### 5. Merge and write the note

Write `docs/math/<slug>.md` to the format in `references/note-format.md`.

If any quote you merge carries a macro its source defines — `\lok`, `\A`, `\bC` —
the note opens with the macro preamble that format specifies. Never edit a quote
to make it render.

Three things are **yours**, not any lane's:

1. **The adopted general form.** Lane 1 supplies the variants and lane 4 the
   discriminators, but they run in parallel and neither sees the other. Write
   the paragraph, and cite the discriminator that justifies the choice by its
   `(X#)`. If no discriminator justifies it, say that the choice is provisional
   — do not manufacture a reason.
2. **The `[ext]` gap.** Compute the set difference between the external results
   lane 2 marked and the ones lane 5 actually checked, and put the remainder in
   `## Not investigated`. Nobody else can compute it; if you skip it, the note
   silently claims coverage it does not have.
3. **`worst-tier`** — the minimum tier over the rows the adopted form and the
   main results rest on. Not the average, and not the best.
4. **The variant comparison grid.** Lane 1's (D#) rows are its only input, but
   choosing the axes — the columns along which the variants genuinely differ —
   needs all the rows at once, which no lane has. The grid is a derived index
   and carries no tier; when it disagrees with a (D#) block, the grid is wrong.

On a re-extraction, carry `## Rejected formulations and refuted claims` and
`## Sources` forward verbatim and append to them; replace every other section.
Add a `revisions:` entry. Carry `implemented-as` forward unchanged too — it is
`math-review`'s field, not yours, and a re-extraction that resets it to `none`
silently deletes the back-link to a formalization that still exists.

Do not soften or drop what the lanes returned. Rows from different lanes that
touch the same object stay separate; only `## Out of lane` items get
de-duplicated.

*Done when:* the note exists, every section is present, `## Not investigated` is
non-empty, and the append-only tables have lost no rows.

### 6. Verify, then report

Run all five checks against the note. **They are the acceptance criteria, not a
formality** — this is the one step that costs your own tool calls rather than an
agent's, and it is worth it, because a fabricated quote or an invented theorem
number is the worst thing this skill can produce, and a note that renders as a
wall of `ParseError` is the worst thing a reader can be handed.

The commands below are the detection half; the judgement is yours. Each was
measured against a note written to violate all four, and each flagged the bad
rows without flagging the good ones — but a grep finds candidates, not verdicts,
so read every hit rather than counting them.

1. **Firewall.**

   ````bash
   grep -nE '```lean|^\s*(theorem|lemma|def|structure|class|instance|example)\b' docs/math/<slug>.md
   ````

   A Lean fence is a hard fail: remove it and the material around it. A prose
   hit — a sentence opening "Definition of …" — is fine.

2. **Quote check.** For each blockquote, `grep -F` its text against
   **`source.flat.txt` of the source that row cites**, not against the cache at
   large: matching some other file proves the sentence exists somewhere, which
   is not the claim. Use the flattened file, since a quotation crossing a line
   break in the original matches there and nowhere else. A quote that does not
   match is downgraded to (b) or deleted. Report the counts.

3. **Locator check.**

   ```bash
   grep -nE 'tier \([cd]\)|\| *[cd] *\|' docs/math/<slug>.md |
     grep -E 'Theorem|Thm|Lemma|Prop|Cor|§|p\. ?[0-9]|eq\. ?\('
   ```

   Both spellings of the tier are needed: the prose rows write `tier (c)`, while
   the `## Hypotheses`, `## Rejected` and `## Sources` rows carry a bare `c` or
   `d` in a column. The second alternative costs some false positives on any
   one-letter cell, which is the right trade here — a missed (c) row with a
   theorem number is the failure this check exists to catch.

   Every hit is a violation: the row must carry the substitution sentence
   instead of the number. Then read the `[ext: …]` markers and the
   `## Sources` rows for anything on the unfetchable list.

4. **Discipline check.**

   ```bash
   awk -F'|' '/model-dependent/ { w=$6; gsub(/^[ \t]+|[ \t]+$/,"",w)
     if (w=="" || w=="—" || w=="-") print NR": no witness: "$2 }' docs/math/<slug>.md
   awk -F'|' '/\| rejected \|/ { if ($5 !~ /\(X[1-5]\)/) print NR": untyped: "$2 }' docs/math/<slug>.md
   grep -niE 'harder to formalize|awkward in a proof assistant|not standard|more lemmas' docs/math/<slug>.md
   ```

   A `model-dependent` row with no witness becomes `open`. A `rejected` row with
   no typed discriminator, or resting on a banned ground, becomes
   `preference-only`. Then check by eye that every degeneracy checklist item has
   a row — including the ones with no effect, and including the
   `intended case is nonvacuous` row (a named instance or an explicit
   "none found — <what was searched>") — and that `## Not investigated` is
   present **and** non-empty. Finally, for each `(R#)` carrying a
   `Proof route:`, cross-check route against `Depends on:` both ways: an edge a
   step consumes but the list omits is the exact omission the field exists to
   catch; a listed edge no step consumes is an error in one of the two.

5. **Render check.**

   ```bash
   uv run .claude/skills/math-extract/scripts/check_render.py docs/math/<slug>.md
   ```

   Every math span must parse **on its own**, because that is how a markdown
   previewer renders it. The script reports two classes of defect and exits
   non-zero on either:

   - a command KaTeX does not define — almost always a source's private macro
     (`\Tr`, `\A`, `\U`) that leaked out of a quote and into the note's own
     prose, or an in-note macro definition, which never carries;
   - with the pipeline installed, a **real render of the document** through
     markdown-it and the plugin VS Code's preview uses, which catches what an
     allowlist cannot: an unbraced argument (`\widetilde\mathcal U`), a
     mis-paired delimiter, and *portability hazards* — spans that typeset here
     but rely on behaviour engines disagree about, such as a subscripted thin
     space (`\mathrm{Tr}\,_2`).

   Enable the real render once per checkout with
   `(cd .claude/skills/math-extract && npm install --no-save markdown-it @vscode/markdown-it-katex)`;
   `node_modules/` is gitignored. Without it the script still runs, says so, and
   leaves brace and span-boundary errors unchecked — a partial check, not a pass.

   **Do not silence a finding with a macro preamble.** Measured through that
   plugin, **no** definition form carries to the next math span — not
   `\newcommand`, not `\gdef`, not `\global\def` — because each span is
   rendered with fresh options. A note cannot define macros for itself. The two
   fixes, in `references/note-format.md`, are: plain KaTeX in the note's own
   voice, and code (a fenced block, or backticks for an inlined fragment) around
   anything verbatim that carries source macros.

Then update `sources.md`: one row per source attempted this run, and a `Notes`
entry for any locator you adjudicated. **This is the only step that writes to
that file.**

Report to the user in Japanese, in this shape:

```markdown
# Math Extract — <object>

**Note**: `docs/math/<slug>.md` — <new | re-extracted>
**Size**: S=<n> sources · D=<n> variants · R=<n> results → <small|medium|large>, <k> lanes
**Worst tier among load-bearing rows**: (<a|b|c|d>)

## Adopted general form — 判断を仰ぐ点
<one paragraph: the form the note adopts and the discriminator that justifies
 it. This is the single decision the reader has to make; everything else is
 reportable fact.>

## Checks
- Firewall: <clean | HITS — a defect>
- Quote check: <n>/<n> matched; <n> downgraded; <n> deleted
- Locator check: <n> tier-(c)/(d) rows, all carrying a statement instead of a number
- Discipline: <n> model-dependent rows, all with witnesses; <n> rejected rows, all with typed discriminators
- Render: <n> math spans parsed independently, <n> ParseErrors <| real KaTeX parse not available — brace errors unchecked>

## Corpus
| Key | How obtained | Cost |
|---|---|---|
<and the sources attempted and not obtained, with what was tried>

## Discriminators found
<the (X#) rows carrying real weight, one line each, with their type>

## Per-lane summary
| Lane | rows | forecast | verdict |
|---|---|---|---|
<every lane present, including clean ones; forecast is hit / miss / n.a.>

## What changed          <!-- re-extraction only -->
<what the previous note said that this one contradicts>

## Refuted               <!-- only if step 4 ran and killed something -->
<one line each: the claim and the evidence>

## Not investigated
<mirrors the note's section, including the [ext] gap computed in step 5>
```

Omit an empty optional section; never omit `## Checks`, `## Per-lane summary`,
or `## Not investigated`.

## Why lanes, not sources

One agent per source would reconcile nothing. The note's whole value is in the
comparisons — this source defines it that way and that one differently, this
hypothesis is standing there and local here, this result is proved in one place
and asserted in another — and a comparison needs one reader holding both texts
at once. So the lanes cut across the corpus, not through it.

The cut is by tool budget as much as by topic, which is what keeps the lanes
from duplicating work. Lanes 1 and 2 read the corpus and nothing else. Lane 3
reads it and argues. Lane 4 constructs objects. Lane 5 is the only one that
searches Mathlib and the web. Two lanes that would contend for the same scarce
tool are paired into one agent at medium size for exactly that reason.

Conversion is deliberately outside all of this: it is serial, minutes long, and
breaks under concurrency, so it happens once in step 2 and the lanes only read
what it produced.
