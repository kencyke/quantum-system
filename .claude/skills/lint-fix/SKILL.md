---
name: lint-fix
description: Fix a change — or an explicitly named file, directory, or commit range — into conformance with the project lint rules: whitespace, 120-column layout, naming, docstrings, English comments, prohibited tokens, pinned files, and Conventional Commits. Applies the safe fixes, verifies with `lake build`, and reports what it deliberately left alone.
argument-hint: "[path | dir | main...HEAD]"
disable-model-invocation: true
---

Bring the target files into conformance with the project lint rules: detect the
violations, apply the fixes that are genuinely mechanical, and report the rest
rather than forcing them. The rules are the ones `lake exe runLinter`,
`cz check`, and Mathlib review would eventually catch — this skill closes them
now, at the cost of touching the working tree, so the discipline about *which*
fixes are safe matters more than the detection.

The failure mode to avoid is a fix that makes the lint report clean while making
the code worse: deleting a `sorry` does not prove a theorem, dropping a
`set_option` does not make a proof fast, and inventing a docstring for a lemma
you have not read is a false claim in the repository. Those are reported, not
fixed.

## Rules

The rules live in `references/rules.md`, next to this file — never duplicate them
here. That file is their authoritative home: `AGENTS.md` points readers at it for
the rules alone, without dragging in this skill's fixing machinery, and keeping
one copy is what stops a rule from being tightened in one place and left stale in
the other.

Read it in step 3; detection does not work without it.

## What may be fixed, and what may not

Sort every violation into one of three tiers before touching a file. The tier
decides the action; when a violation could belong to two tiers, take the more
cautious one.

**Tier A — apply directly.** Purely textual, no effect on the elaborated term.

- Tabs → spaces at the surrounding indentation width (2-space steps).
- Trailing whitespace on a line you are already editing.
- Layout nits: `by` placement, `calc` alignment on the relation, `case _ =>` →
  `·`, indentation that is not a multiple of two.
- Non-English comments → English, preserving the technical content.

**Tier B — apply, then prove it survived.** The fix is known but can change
elaboration or break callers, so each one is verified in step 5.

- Lines over 120 columns: re-wrap. Never shorten by deleting content, weakening
  a statement, or renaming to something shorter — wrap at a binder, an
  argument, or a `calc` step instead.
- Missing docstrings: read the declaration's *elaborated* statement first
  (`lean_hover_info`, or `lean_goal` for a theorem) and describe what it
  actually establishes. A docstring that overstates the code is worse than none,
  because the repo's own principle is to raise the code to the docs — writing an
  aspirational summary silently manufactures that debt.
- Naming violations: rename, then update every reference. Find them with
  `lean_references` (not grep — grep misses qualified and re-exported uses) and
  fix all of them in the same pass; a half-renamed declaration does not build.
- `set_option`: remove it and rebuild. If the build then fails, the option was
  load-bearing — restore it and report the finding, noting *which* proof depends
  on it. That dependency is a real defect worth naming rather than a lint nit,
  and discovering it is more useful than silently keeping the line.
- `namespace`/`section QuantumSystem`: removing it re-qualifies every
  declaration inside, so treat it as a rename of all of them — sweep references
  the same way, and expect to touch importers.

**Tier C — never fix here; report it.** Either no mechanical fix exists, or the
fix destroys work.

- `sorry`, `admit`, `axiom`: the only real fix is a proof, which is mathematical
  work, not linting. Deleting the token leaves an unproved goal or removes a
  declaration others depend on. Report as a blocker and stop there.
- `unsafe`: removing it means rewriting the definition to be safe — a design
  change, not a lint fix.
- Edits to `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: the fix is
  `git checkout -- <file>`, which discards whatever the user did. Print the
  command and let them decide.
- Commit messages: correcting one means `git commit --amend` or a rebase, which
  rewrites history. Print the corrected message and the command; do not run it
  without the user saying so in this conversation.
- `System` / `Lean.Elab` / `Lean.Meta` / `Lean.Compiler` uses: dropping the
  import or the reference requires replacing the functionality. Report it.

## Process

### 1. Pin the target

Take the first non-empty option:

1. An explicit argument — a file, a directory (expand with Glob), or a commit range.
2. The union of the local change and the branch change, so that a stray
   working-tree edit cannot shadow committed branch work:
   - `git diff --name-only --diff-filter=ACMR HEAD` (working tree and index),
   - `git ls-files --others --exclude-standard` (untracked new files — `git diff` never lists these),
   - `git diff --name-only --diff-filter=ACMR <base>...HEAD`, where `<base>` is
     `main`, falling back to `origin/main`, then `origin/HEAD`; if none
     resolves, drop this component rather than failing.

Do **not** filter to `.lean` here — the tab and pinned-file rules apply to every
file in the change. If every option is empty, ask the user what to fix rather
than reporting a clean pass over nothing.

Announce the resolved target before editing anything. This skill writes to the
working tree, so a wrong default is expensive — one word of correction now beats
a revert later.

### 2. Record the baseline

Before the first edit, capture what "no *new* errors" will be measured against:

- `git status --short` — note pre-existing modifications, so your fixes stay
  distinguishable from the user's own work in the final diff.
- `lake build` on the target modules. If the build is already broken, say so and
  fix only Tier A violations: with a red baseline you cannot tell whether a
  Tier B fix broke something. Detection still runs in full — every Tier B
  violation you find gets reported as deferred, with the pre-existing error that
  blocked it. Omitting them would read as "nothing else to fix", which is the
  opposite of what a red baseline means.

### 3. Detect (Bash, restricted to the target files)

Read `references/rules.md` first. The commands below encode the rules that happen
to be greppable; the rules themselves — and the reasons behind them, which are
what let you judge a case the grep does not literally cover — are in that file.

A grep hit is a *lead*, not a verdict: open the line and confirm it before
fixing. A token inside a string literal, a docstring quoting the rule, or this
skill file itself is not a violation — and a fix applied to a false positive is
a real defect introduced by the fixer.

- **Tabs** (all files): `grep -nP '\t' <files>`
- **Line length** (`.lean` files only — the 120-column rule is Lean layout style;
  the repo's own markdown exceeds it):
  `awk 'length > 120 {print FILENAME ":" FNR ": " length($0) " cols"}' <files>`
- **Pinned files**: check whether the target list contains `lakefile.toml`,
  `lean-toolchain`, or `lake-manifest.json`.
- **Prohibited tokens** (`.lean` files only):
  - `grep -nwE 'sorry|admit|axiom|set_option|unsafe' <files>`
  - `grep -nE 'open System|Lean\.(Elab|Meta|Compiler)' <files>`
  - `grep -nw 'System' <files>` — then judge each hit in context; `System` is a
    common English word in comments, and only the Lean namespace is prohibited.
- **Forbidden namespace** (`.lean` files only):
  `grep -nE '^\s*(namespace|section)\s+QuantumSystem\b' <files>`
- **Commit messages** (only when the target is a commit range): for each commit
  in the range run `uv run cz check -m "$(git log -1 --format=%s <sha>)"`, then
  additionally check the type against the narrower project vocabulary
  (`feat|fix|chore|docs|refactor|test|perf`) — `cz check` alone accepts more
  types than the project convention does.

Then read the changed declarations for what cannot be grepped, judging each
against the corresponding section of `references/rules.md`: naming (its
*Naming* bullets), docstring presence and whether the first sentence is a
self-contained summary, module docs on new files (*Docstrings*), comment
language (*Editing Hygiene*), and layout (*Layout*).

Confine this to the changed declarations (use the diff's line ranges); do not
re-litigate untouched code in a diff-derived run. An explicit file or directory
target has no diff — cover the whole file.

### 4. Apply the fixes

Work one rule at a time across all files, not one file at a time across all
rules: a diff whose hunks each address a single rule is reviewable, and a
mixed-up one is not. Fix Tier A first — it cannot break the build, so it gets
the later verification for free — then Tier B, unless step 2 found a red
baseline, in which case Tier B is deferred rather than attempted.

Keep the fixes separable from any semantic change. If a fix tempts you into
altering a statement, a hypothesis, or a proof, stop: that is the repository's
"prove what is provable" territory, and it belongs in its own change with its
own review, not smuggled in under a lint pass.

### 5. Verify

A fix is not done because the file was written; it is done when the build agrees.

- `lake build` on the edited modules **and their downstream importers** — Tier B
  renames and namespace removals fail precisely there.
- Compare against the step 2 baseline: no new errors and no new warnings.
- Re-run the step 3 detection over the same targets to confirm the violations
  are actually gone and that no fix introduced a new one (a re-wrap that lands
  on a tab, a rename that collides).
- If a Tier B fix cannot be made to build, revert that fix and report it as
  unfixed with the error. Never reach for `try`, `<;>`, or `set_option` to make
  a broken fix compile — that trades a lint violation for a worse one.

## Report

Lead with what changed in the working tree, since that is what the user has to
review. Then what was left, and why — the deliberate omissions are the part
only this pass knows about.

```markdown
# Lint Fix — <target>

**Scope**: <N> files (<M> .lean) / <commit range if any>
**Result**: <K> fixed, <L> left unfixed, <D> deferred (see below)
**Build**: <lake build outcome vs. baseline, naming the modules built>

## ✅ Fixed
- `file:line` — <rule>: <what it was> → <what it is now>. [Tier A|B]

## 🛑 Left unfixed — blockers
<Tier C, and any Tier B fix reverted in step 5. For each: `file:line`, the rule,
 why it was not fixed, and the concrete next action — the command to run, or the
 proof obligation to discharge.>

## ⚠️ Left unfixed — needs a decision
<violations whose fix would discard the user's work or rewrite history: pinned
 files, commit messages. Give the exact command, do not run it.>

## ⏸️ Deferred — baseline build was red      <!-- only when step 2 found a broken build -->
<Tier B violations that were detected but not attempted, because verification was
 impossible. `file:line` and the rule for each, plus the pre-existing build error
 that blocked the pass, so that re-running once the build is green picks them up.
 These are not judgements that the code is fine — they are unexamined.>

## Not checked
<files skipped (binary, generated), checks not applicable (no commit range → no
 commit-message check), and any grep hit dismissed as a false positive — name it
 and say why, so the dismissal is auditable>
```

If nothing needed fixing, say so explicitly (✅) together with the scope
covered — a clean report over the wrong scope is worse than no report.
