---
name: math-review
description: Review the current Lean change — or an explicitly named file, directory, or commit range — from a mathematician's/physicist's viewpoint via parallel per-perspective `math-reviewer` sub-agents: statement fidelity (checked against a blind `lean-readback` of the claims), deferred hypotheses, abstraction/literature conformance, notation/naming/docs, and counterexample models/vacuity.
argument-hint: "[path | dir | main...HEAD]"
disable-model-invocation: true
---

Dispatch the math/physics review to `math-reviewer` agents, one per review
perspective. The review methodology (the perspective definitions, the
elaborated-type discipline, the per-agent output format) lives in
`.claude/agents/math-reviewer.md` — never duplicate it here.

## Process

### 1. Pin the target

Take the first non-empty option:

1. An explicit argument — a file, a directory (expand with Glob), or a
   commit range.
2. The union of the local change and the branch change, so that a stray
   working-tree edit cannot shadow committed branch work:
   - `git diff --name-only --diff-filter=ACMR HEAD -- '*.lean'` (working tree
     and index),
   - `git ls-files --others --exclude-standard -- '*.lean'` (untracked new
     files — `git diff` never lists these),
   - `git diff --name-only --diff-filter=ACMR <base>...HEAD -- '*.lean'`,
     where `<base>` is `main`, falling back to `origin/main`, then
     `origin/HEAD`; if none resolves, drop this component rather than failing.

Filter to `.lean` files *before* testing an option for emptiness — reviewing
"no issues" over an empty scope is the worst outcome this skill has. Deleted
files never appear under `--diff-filter=ACMR`; enumerate them separately with
`--diff-filter=D` over the same bases and list them as unreviewed — they have
no elaborated type to inspect. If every option is empty, ask the user what to
review.

For diff-derived targets, also collect the changed line ranges per file with
`git diff -U0 <base> -- <file>` — step 3 hands them to the reviewers. An
explicit file or directory target has no diff; its scope is the entire file.

Announce the resolved target before dispatching, so a wrong default costs one
word to correct.

### 2. Read the claims back blind

A reviewer who has read the docstring reads the code through it. Before any
reviewer starts, have the target's claims read back by an agent that has seen
neither the docstring nor the source:

1. Select the public `theorem` / `lemma` / `def` / `structure` / `class`
   declarations in the scope whose docstring states a mathematical claim, at
   most 20, theorems first; list the rest under `## Not reviewed`.
2. Build one packet per declaration, numbered `d1`, `d2`, … : its source, the
   `variable` / `open` / `namespace` lines governing it, and the repository
   definitions its statement mentions, with every docstring (`/-- … -/`), module
   doc and comment removed.
3. Write the prompt — the packets and nothing else — to
   `<your scratchpad>/math-review/readback-input.md`, then launch **one**
   `lean-readback` agent (`subagent_type: lean-readback`) with that text pasted
   into the prompt: it has no tools, so the prompt is all it sees. Do not add
   file paths, docstrings, citations or your reading of the intent.
4. Save its reply verbatim to `<your scratchpad>/math-review/readback.md`,
   followed by a table mapping each `d<N>` to its declaration name and file.

If no declaration qualifies, skip this step and say so in the report.

### 3. Spawn one sub-agent per perspective

**Scale to the target first.** When the scope is small — roughly three target
declarations or fewer, or a small diff in a single file — do not fan out:
launch a **single** `math-reviewer` with no perspective assigned (its agent
file then has it cover all five perspectives itself), and continue with
step 4 unchanged. The fan-out below is for real diffs.

Launch five `math-reviewer` agents (Agent tool,
`subagent_type: math-reviewer`) — one per perspective defined in the agent
file:

1. Statement fidelity
2. Deferred hypotheses
3. Abstraction & literature conformance
4. Notation, naming & documentation
5. Counterexample models & vacuity

all in a single message. Every agent receives the **same scope**: the full
list of target files with their changed line ranges (the agent expands them to
declarations itself). Write each prompt as a research memo, not a task ticket —
it carries the target and explicit permission to contradict the brief. Each
prompt must state:

- the assigned perspective by number and name, framed as a role: "You are one
  of five perspective-specific reviewers running in parallel over this change;
  review it under perspective N (<name>) only" — do not restate the
  perspective's definition, the agent file owns it;
- the target files, with the changed line ranges collected in step 1 — or
  *entire file* for an explicit target that has no diff;
- for perspective 1, and for a single reviewer with no perspective assigned,
  the absolute path of the readback file from step 2;
- **the absolute path of the notes file** it must append confirmed findings to
  as it goes: `<your scratchpad>/math-review/perspective-<N>.md`. Pass *your*
  scratchpad path, not the agent's — a file written where you cannot read it is
  no use when the agent dies;
- **explicit permission to contradict this brief**. "The assigned lens is the
  wrong one for this change" is a finding to report, not a failure to apologise
  for. Say so in the prompt — a reviewer that believes it must confirm the brief
  will find a way to.

Do not re-implement the review yourself. If the platform refuses to launch all
five at once, start as many as it allows, wait for one to complete, and
immediately launch the next — every perspective must run before aggregation.

**If an agent does not return**, do not simply drop its perspective: read the
notes file you assigned it, which it appends to as it works. Findings that
reached disk are usable even when the agent died mid-sweep; mark that perspective
as partial and record in `## Not reviewed` how far it got.

### 4. Aggregate

Wait for every perspective to complete.

Emit one markdown report to the chat, grouped by severity. Do not soften,
merge, or drop findings; findings from different perspectives on the same line
stay separate entries. The one exception: the reviewers' `## Out of
perspective` sections (defects fitting no perspective — layout violations,
Mathlib duplicates) may name the same defect several times; de-duplicate those
and file each once, under the severity it deserves.

**Cap unverified claims.** A finding at evidence tier **(c)** — recalled, not
verified — is reported marked `unverified` and capped at should-fix: no blocker
rests on (c) alone. The tier is the reviewer's own confidence statement; do not
launch further passes to vote on it.

**Verify every blocker yourself before printing it.** Open the declaration and
confirm the claim with `lean_goal` / `lean_term_goal` from your own seat —
re-reading the reviewer's argument is relaying, not verifying. A blocker you could not confirm drops to
should-fix and is marked `aggregator-unverified`; it is not deleted, because
failing to confirm is not refuting. This is the one place the skill spends your
own LSP calls rather than an agent's, and it is worth it: a false blocker costs
the reader more than a missed nit.

**Attribute claims to whoever made them.** Write "the perspective 2 reviewer
reports X; I confirmed the elaborated type at Y" — not "X is a bug". You are
reporting what the review produced and how far you checked it, and those are two
different statements. Keep them separate in the prose.

Template:

```markdown
# Math Review — <target>

**Scope**: <N> files / <M> declarations   <!-- from the agents' reviewed-declaration lists -->
**Verdict**: <worst severity present, or ✅ no findings>

## 🛑 Blocker
### 1. <one-line title>
- `file:line` `declName` — [<perspective>/<a|b|c>]
- **Problem**: …
- **Fix**: …
- **Verified**: <what you confirmed yourself, or `aggregator-unverified`>

## ⚠️ Should-fix
…same shape…

## 💡 Nit
…same shape…

## Ranked risks
<descending by concern, independent of severity; for each, whether it
 **could make a theorem false** or is **presentation only**. State plainly which
 findings, if any, can actually kill a result — and say so when none can.>

## What this change does not claim
<what a reader might wrongly take away: the generality the statements stop
 short of, the cases left uncovered, the corollaries that do not follow>

## Per-perspective summary
| Perspective | blocker | should-fix | nit | verdict |
|---|---|---|---|---|
<all five perspectives, every row present; ✅ for a clean perspective>

## Not reviewed
<deleted files; files no agent could reach; perspectives that returned partial;
 claims left without a readback beyond the cap of step 2; and — always — the
 **unexamined dependencies the verdict rests on**: the
 declarations the reviewers relied upon without opening, taken from each
 reviewer's per-finding confidence split. The risk lives here, not in what was
 checked, so this section is never omitted.>
```

Omit an empty severity section, never an empty summary row, and never
`## Not reviewed`.

## Why perspectives, not files

A diff hunk is not a reviewable unit in Lean: a statement's elaborated type is
fixed by binders, `variable` blocks, and `open scoped` lines that sit outside
the hunk, and one hunk routinely spans several declarations. That expansion
belongs to the `math-reviewer` agent; this skill only resolves *which files*
enter the review.

Nor is a file the unit of judgement: deferred hypotheses are discharged — or
silently left standing — across files, and abstraction drift shows up only
when the definition and its uses are read together. One reviewer per
perspective sees the whole change at once, and caps the fan-out at five reviewers.
