# Sources ledger

The `math-extract` skill's memory across runs, keyed by **source**. The notes
under `docs/math/` are keyed by **object**; this file holds what a note
structurally cannot, because it is true of the source no matter which object was
being extracted when it was discovered.

Step 1 of the skill reads it. Step 6 writes it. Nothing else touches it.

## What goes in

**One row per work, not per run.** Three kinds of fact:

1. **Retrieval attempts.** That a book could not be obtained is true for every
   object that cites it. Without this row the next extraction spends the same
   ten minutes discovering the same thing.
2. **Locator adjudications.** When someone finally opens a source and finds that
   a widely-copied theorem number does not say what it is said to say, the
   correction belongs to the source. Recorded once, read forever. This is the
   row type that pays for the file.
3. **Edition and version drift.** Preprint versus published numbering, second
   editions, arXiv versions. A locator is meaningless without knowing which one
   it indexes.

**What does not go in:** anything about a mathematical object. Definitions,
results, hypotheses, rejected formulations and their discriminators all live in
`docs/math/<slug>.md`. A fact that would change if you were extracting a
different object is in the wrong file.

## Expiry — read this before trusting a row

- A **`retrieved`** row does not expire. The text does not change.
- A **`not retrieved`** row expires **six months** after `Last tried`. Paywalls
  lift, scans appear, authors post copies. A stale `not retrieved` that stops
  someone from trying again is the one real danger of this file, so when in
  doubt, try again rather than trust the row.
- A **locator adjudication** does not expire, but it is bound to the edition in
  `Version/Ed.`. An adjudication made against the second edition says nothing
  about the first.
- An **arXiv** row is bound to its version. When a new version appears, locators
  taken from the old one may have moved; the mathematics has not. Only the
  locators in notes citing that source are affected.

## Format

| Key | Work | Status | Cache | Version/Ed. | Last tried | Notes |
|---|---|---|---|---|---|---|

- **Key** — the short citation key used in the notes (`DL84`, `TAK-I`,
  `BHATIA`). Stable; notes cite it.
- **Work** — author(s), *title*, venue or publisher, year. Enough to identify
  the work without a locator.
- **Status** — `retrieved` | `partial` (abstract or fragment only) |
  `not retrieved` | `no digital copy known`.
- **Cache** — path under `references/`, or `—`.
- **Version/Ed.** — arXiv version, edition, or `published` / `preprint`.
- **Last tried** — `YYYY-MM-DD` of the most recent retrieval attempt.
- **Notes** — what was tried and where, locator adjudications, numbering drift
  between editions. Adjudications are written as
  `locator X: says <what it actually says>` or
  `locator X: not found in this edition`.

## Entries

| Key | Work | Status | Cache | Version/Ed. | Last tried | Notes |
|---|---|---|---|---|---|---|

<!-- Append below. Newest last. -->
