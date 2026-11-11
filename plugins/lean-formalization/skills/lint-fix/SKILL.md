---
name: lint-fix
description: Fix a change — or an explicitly named file, directory, or commit range — into conformance with the lint rules of a Lean project (Mathlib-style rules plus the project's own rules file): whitespace, line length, naming, docstrings, comment language, prohibited tokens, pinned files, and commit messages. Leaves what `lake build` and `lake lint` already detect to them, applies the safe fixes, verifies with both, and reports what it deliberately left alone.
argument-hint: "[path | dir | main...HEAD]"
disable-model-invocation: true
---

Bring the target files into conformance with the lint rules. `lake build`
and `lake lint` detect part of the rules; this skill detects the rest, fixes what
is genuinely mechanical in both, and reports everything else. It writes to the
working tree, so the discipline about *which* fixes are safe matters more than
the detection.

The failure mode to avoid is a fix that makes the report clean while making the
code worse: deleting a `sorry` does not prove a theorem, dropping a `set_option`
does not make a proof fast, a `nolint` does not make a lint finding wrong, and
inventing a docstring for a lemma you have not read is a false claim in the
repository. Those are reported, not fixed.

## Rules

The rules live in two files — never duplicate them here:

- `references/rules.md`, next to this file: the rules of any Lean project in
  Mathlib style;
- the project's rules file: the one the project's instruction file (`CLAUDE.md` /
  `AGENTS.md`) names for its lint rules, or, if it names none, the instruction
  file itself. Its rules add to the generic ones and win where the two differ
  (a line limit, docstring coverage, which tokens are prohibited, which files
  are pinned, the commit vocabulary). A project with neither gets the generic
  rules alone; say so in the report.

One copy of each rule is what stops it from being tightened in one place and
left stale in the other. Read both in step 3; detection does not work without
them. Below, "the project rules" means the project's rules file.

## What the tools already detect

Do not re-detect these by hand: steps 2 and 5 run the tools, and a second
detector only drifts out of step with the first. What they detect depends on
the lakefile (`lakefile.toml` or `lakefile.lean`), so read it first and note,
for each `lean_lib`, its name and its `leanOptions`:

- `lake build` — tabs in `.lean` files are a Lean lexer error regardless.
  - With `warningAsError` set, every warning is an error, so the build rejects
    `sorry`/`admit`. Without it, they are only warnings: step 3 greps for them.
  - With `linter.mathlibStandardSet` set, the style linters flag `.` in place of
    `·` (`style.cdot`), commands not starting at column 0 and binder spacing
    (`style.whitespace`), blank lines inside a declaration (`style.emptyLine`),
    debug options (`style.setOption`, which sees only
    `pp`/`trace`/`profiler`/`debug`), and long lines (`style.longLine`, unless
    switched off). Without it, step 3 checks these layout rules by reading.
- `lake lint` — only when the lakefile sets `lintDriver` (typically Batteries'
  `runLinter`): missing docstrings on definitions, structures and classes
  (`docBlame`), a `_` in a definition name (`defsWithUnderscore`), `simpNF`,
  `unusedArguments`, and the rest of its default set. Without a `lintDriver`,
  skip it and list it under `## Not checked`.

Both tools see only the modules that a library's root file (`<Lib>.lean` for the
`lean_lib` named `<Lib>`) imports. A `.lean` file not yet registered there is
invisible to them, so step 2 checks registration and step 3 greps such files for
what the tools would otherwise catch.

## What may be fixed, and what may not

Sort every violation into one of three tiers before touching a file. The tier
decides the action; when a violation could belong to two tiers, take the more
cautious one.

**Tier A — apply directly.** Purely textual, no effect on the elaborated term.

- Tabs in non-Lean files the project rules hold to the no-tab rule → spaces at
  the surrounding indentation width (2-space steps); never in a file where a tab
  is syntax (a Makefile recipe, a TSV).
- Trailing whitespace on a line you are already editing.
- Layout nits: `by` placement, `calc` alignment on the relation, `case _ =>` →
  `·`, indentation that is not a multiple of two.
- Comments in a language the project rules exclude → the required language,
  preserving the technical content.

**Tier B — apply, then prove it survived.** The fix is known but can change
elaboration or break callers, so each one is verified in step 5. Docstrings and
renames need the tools of the lean-lsp MCP server (`lean_hover_info`,
`lean_goal`, `lean_references`); without them, make neither fix and report each
under what you left alone, as needing lean-lsp.

- Lines over the limit (the project rules' limit, else Mathlib's 100): re-wrap.
  Never shorten by deleting content, weakening
  a statement, or renaming to something shorter — wrap at a binder, an
  argument, or a `calc` step instead.
- Missing docstrings: read the declaration's *elaborated* statement first
  (`lean_hover_info`, or `lean_goal` for a theorem) and describe what it
  actually establishes. A docstring that overstates the code is worse than none:
  a reader takes the docstring for the intended claim, so an aspirational summary
  silently manufactures a gap between what the repository says and what it
  proves.
- Naming violations: rename, then update every reference. Find them with
  `lean_references` (not grep — grep misses qualified and re-exported uses) and
  fix all of them in the same pass; a half-renamed declaration does not build.
- `set_option`, where the project rules prohibit it outside their approved
  exceptions: remove it and rebuild. If the build then fails, the option was
  load-bearing — restore it and report the finding, noting *which* proof depends
  on it. That dependency is a real defect worth naming rather than a lint nit,
  and discovering it is more useful than silently keeping the line.
- Visibility the project rules call for (say, `private` for declarations used
  only in their own file): in a file that starts with `module`, a declaration
  that the body of an exposed definition (`@[expose]`, or one in an
  `@[expose] public section`) refers to — including a lemma used in one of its
  proof fields — cannot be `private`; the build rejects it. Leave such a
  declaration public and report why, rather than restructuring the definition.
- A `namespace`/`section` the project rules forbid: removing it re-qualifies
  every declaration inside, so treat it as a rename of all of them — sweep
  references the same way, and expect to touch importers.
- Other `lake lint` findings (`simpNF`, `unusedArguments`, …): fix the code.
  Treat the finding as right until an experiment shows otherwise. For `simpNF`,
  run plain `simp` on the lemma's own statement; a lemma that `simp` cannot use
  should lose `@[simp]`, not gain `nolint`. `@[nolint …]` is acceptable only
  when the finding is shown wrong for this declaration, with the reason in a
  comment next to it — e.g. an instance argument the body does not use but the
  docstring's scope requires.

**Tier C — never fix here; report it.** Either no mechanical fix exists, or the
fix destroys work.

- `sorry`, `admit` (the build fails on them under `warningAsError`), `axiom`: the only real fix is a
  proof, which is mathematical work, not linting. Deleting the token leaves an
  unproved goal or removes a declaration others depend on. Report as a blocker.
- `unsafe`, where the project rules prohibit it: removing it means rewriting
  the definition to be safe — a design change, not a lint fix.
- Edits to the files the project rules mark as pinned (typically
  `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`): such a rule binds
  agents only, and a diff cannot tell an agent's edit from the user's or an
  update workflow's, which are legitimate. Never edit or revert these files;
  list the changed ones so the user can confirm they were intended.
- Commit messages: correcting one means `git commit --amend` or a rebase, which
  rewrites history. Print the corrected message and the command; do not run it
  without the user saying so in this conversation.
- Imports or namespaces the project rules prohibit (say, the elaborator's
  `Lean.Elab` in a mathematics project): dropping the import or the reference
  requires replacing the functionality. Report it.
- Metaprogramming the project rules prohibit — `macro`, `meta def`,
  delaborators, unexpanders — other than the approved exceptions they list: the
  fix reshapes definitions so that an ordinary `notation` displays, a design
  change. Report it.

## Process

### 1. Pin the target

Take the first non-empty option:

1. An explicit argument — a file, a directory (expand with Glob), or a commit range.
2. The union of the local change and the branch change, so that a stray
   working-tree edit cannot shadow committed branch work:
   - `git diff --name-only --diff-filter=ACMR HEAD` (working tree and index),
   - `git ls-files --others --exclude-standard` (untracked new files — `git diff` never lists these),
   - `git diff --name-only --diff-filter=ACMR <base>...HEAD`, where `<base>` is
     the remote default branch that `origin/HEAD` names
     (`git symbolic-ref --short refs/remotes/origin/HEAD`), falling back to
     `origin/main`, then `main`, then `master` — the remote ref first, because a
     local default branch that is never pulled goes stale and drags every
     commit since into the scope; if none resolves, drop this component rather
     than failing.

Do **not** filter to `.lean` here — the pinned-file rule, and a tab rule the
project rules extend beyond Lean sources, apply to every file in the change. If
every option is empty, ask the user what to fix rather than reporting a clean
pass over nothing.

Announce the resolved target before editing anything. This skill writes to the
working tree, so a wrong default is expensive — one word of correction now beats
a revert later.

### 2. Record the baseline

Before the first edit, capture what "no *new* errors" will be measured against:

- `git status --short` — note pre-existing modifications, so your fixes stay
  distinguishable from the user's own work in the final diff.
- Registration: for each `lean_lib` `<Lib>` whose sources hold a target file,
  `lake exe mk_all --check --lib <Lib>` when the project depends on Mathlib
  (`mk_all` is Mathlib's script); without Mathlib, check by hand whether
  `<Lib>.lean` imports each target module. Every target `.lean` file missing
  from its root file is *unregistered*: neither tool below checks it. Note those
  files for step 3. Do not regenerate the root file here; report the missing
  registration instead.
- `lake build`, then `lake lint` if the lakefile sets a `lintDriver` (it reads
  the built `.olean`s). Their findings in the target files are violations to
  fix; the rest is the baseline step 5 compares against.
- If the build is already broken, say so and fix only Tier A violations: with a
  red baseline you cannot tell whether a Tier B fix broke something. Detection
  still runs in full — every Tier B violation you find gets reported as
  deferred, with the pre-existing error that blocked it. Omitting them would read
  as "nothing else to fix", which is the opposite of what a red baseline means.

### 3. Detect (Bash, restricted to the target files)

Read `references/rules.md` and the project rules first. The commands below
cover the rules that no tool detects but a grep can; the reasons behind the
rules, which let you judge a case the grep does not literally cover, are in
those files.

A grep hit is a *lead*, not a verdict: open the line and confirm it before
fixing. A token inside a string literal, a docstring quoting the rule, or this
skill file itself is not a violation — and a fix applied to a false positive is
a real defect introduced by the fixer.

- **Tabs** (unregistered `.lean` files, and non-Lean files the project rules
  hold to the no-tab rule): `grep -nP '\t' <files>`
- **Line length** (`.lean` files only — the limit is Lean layout style; markdown
  is not held to it unless the project rules say so), with `<N>` the project
  rules' limit, else 100:
  `grep -nP '^.{<N+1>,}' <files>` in a UTF-8 locale, which counts characters
  (awk counts bytes in mawk, so Unicode-heavy Lean lines come out too long; and a
  dollar-digit token in this file would be replaced by the skill's argument).
  Skip this when `style.longLine` is on and the limit is Mathlib's: the build
  already checks it.
- **Pinned files**: check whether the target list contains a file the project
  rules mark as pinned.
- **Unfinished proofs** (`.lean` files only):
  - `grep -nw 'axiom' <files>`
  - `grep -nwE 'sorry|admit' <files>` — over unregistered files only when the
    library sets `warningAsError` (the build rejects them in the rest).
- **Prohibited tokens and namespaces** (`.lean` files only): for each token,
  import or namespace the project rules prohibit, grep for it, and set aside the
  hits their approved exceptions cover. Build the patterns from that list:
  - `grep -nwE '<token>|<token>' <files>` for tokens, imports and namespaces
    (`set_option|unsafe`; escape the dots of a module name, `Lean\.Meta`);
  - `grep -nE 'meta def|macro |app_unexpander|delab|open Lean' <files>` when
    the project rules prohibit metaprogramming;
  - `grep -nE '^\s*(namespace|section)\s+<Forbidden>\b' <files>` for a
    forbidden namespace or section name;
  - for a token that is also a common English word, `grep -nw` and judge each
    hit in context: only the Lean name is prohibited, not the word in a comment.
- **Commit messages** (only when the target is a commit range, and the project
  rules state a commit convention):
  - with commitizen configured (`[tool.commitizen]` in `pyproject.toml`, or a
    `.cz.toml` / `cz.toml` / `.cz.json` / `cz.json`), run for each commit in the
    range `uv run cz check -m "$(git log -1 --format=%s <sha>)"` (`cz check …`
    when there is no `pyproject.toml`);
  - then check the type against the vocabulary the project rules list, which
    may be narrower than what `cz check` accepts;
  - without commitizen, check the subjects against the convention by reading.

Then read the changed declarations for what neither a tool nor a grep catches,
judging each against `references/rules.md`:

- *Naming* of theorems and lemmas (`defsWithUnderscore` sees definitions only),
  and `theorem` versus `lemma` where the project rules distinguish them.
- *Docstrings*: presence on the declarations the rules require it for — on
  theorems and lemmas `docBlame` cannot help, since it skips them — a
  self-contained first sentence on every docstring, module docs on new files.
- *Editing Hygiene*: comment language, where the project rules fix one.
- *Layout*: `by` placement, `calc` alignment, `case _ =>` instead of `·`,
  indentation in steps of two, trailing whitespace.

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
altering a statement, a hypothesis, or a proof, stop: that is mathematical
work, and it belongs in its own change with its own review, not smuggled in
under a lint pass.

### 5. Verify

A fix is not done because the file was written; it is done when the build agrees.

- `lake build` on the edited modules **and their downstream importers** — Tier B
  renames and namespace removals fail precisely there.
- `lake lint` afterwards, if step 2 ran it. Against the step 2 baseline: no new
  error, warning or lint finding.
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
**Build**: <lake build and lake lint outcome vs. baseline, naming the modules built>

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
 commit-message check), checks the project lacks the tool for (no `lintDriver`,
 no Mathlib `mk_all`, no commitizen, no project rules file), and any grep hit
 dismissed as a false positive — name it and say why, so the dismissal is
 auditable>
```

If nothing needed fixing, say so explicitly (✅) together with the scope
covered — a clean report over the wrong scope is worse than no report.
