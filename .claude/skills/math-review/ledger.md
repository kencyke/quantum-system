# Refuted-findings ledger

A do-not-repeat list for `math-review`. Step 3 (the refutation pass) appends to
it; step 2 hands each perspective reviewer its own rows so the same claim is not
re-filed run after run.

## What goes in

**One row per *claim*, not per finding.** The same defect reported twice under
different wording is one claim. Reference the target by **declaration name** —
never by line number, which moves with the next edit.

Only claims the refutation pass **refuted** are recorded. A finding that
survived refutation — whether promoted to (a)/(b) or still at tier (c) —
belongs in the report, not here.

## Expiry — read this before trusting a row

Every refutation rests on something: an elaborated type, an instance, a
docstring. The `Depends on` column names it; the `Commit` column records when
it was measured. **When a declaration listed under `Depends on` has changed
since `Commit`, the row is void and the claim may be filed again.** The check
is mechanical, not a judgement call:

1. `git diff <Commit>..HEAD -- <file>` for each file housing a `Depends on`
   declaration; untouched files mean the row stands.
2. If a file changed, re-fetch the declaration's current elaborated type and
   compare it against the evidence quoted in `Refutation`.
3. A `Depends on` declaration that no longer resolves — renamed or deleted —
   voids the row unconditionally.

A stale ledger suppressing a true finding is the one real danger of this file.
When in doubt about whether a row still holds, re-file rather than stay
silent. Rows are never deleted for being old — only by step 3 of the skill,
when they are void under this rule or when the claim is re-filed and
re-adjudicated (the new adjudication replaces the old row).

## Format

| Target | P | Claim | Refutation | Depends on | Commit | Date |
|---|---|---|---|---|---|---|

- **Target** — `path/to/File.lean:declarationName` (no line numbers)
- **P** — perspective 1–5 that filed the claim
- **Claim** — what was asserted to be wrong, in one line
- **Refutation** — the concrete evidence, quotable: an elaborated type or a
  fully-qualified declaration name
- **Depends on** — the declaration(s) the refutation rests on; the expiry trigger
- **Commit** — `git rev-parse --short HEAD` when the row was appended; the
  baseline the expiry check diffs against
- **Date** — `YYYY-MM-DD` the row was appended

## Entries

| Target | P | Claim | Refutation | Depends on | Commit | Date |
|---|---|---|---|---|---|---|
<!-- Append below. Newest last. -->
