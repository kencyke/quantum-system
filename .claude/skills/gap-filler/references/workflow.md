# gap-filler workflow — worked example

Concrete trace of running the skill on the Araki / Longo-Witten paper
(`arxiv-2202.03357`) from `references/` in this project. Use this as a
reference when you need to calibrate expectations against the synthetic
behaviour described in `SKILL.md`.

## Starting state

```
references/
├── CONCEPTS.md                          # aggregated concept index
├── arxiv-2202.03357/
│   ├── INDEX.md                         # Longo–Witten "A note on continuous entropy"
│   ├── content.md                       # MinerU output with 184 LaTeX spans
│   └── assets/                          # empty (no figures)
```

INDEX.md has 14–22 Key concepts bullets (varies across iterations) and a
bibliography of ~24 entries with author-year keys (Ara76, Kos86a, Tak03,
Wit21, …).

## 0. Optional: pin formalization targets (`goals.yaml`)

Without a goals file, `coverage_score` reports knowledge ingestion
coverage (does mathlib have a home for the concepts mentioned in
ingested papers?). To track *project-level* progress — "have we
proven the theorems we promised?" — anchor on a `goals.yaml` listing
**the actual Lean declarations** that constitute each promise:

```yaml
goals:
  - id: gns-construction
    description: "Cyclic representation π_ω with ω(a)=⟨Ω_ω, π_ω(a) Ω_ω⟩."
    declarations:
      - GNS.Representation
      - GNS.Construction.isFaithful_iff_separating
      - GNS.Representation.unique_up_to_unitary_equivalence
    concepts:
      - GNS representation                          # bare string

  - id: ssa-abstract-local-net
    description: "TODO. Abstract SSA over a generic local net."
    declarations: []                                # empty → counts as 1 missing
    concepts:
      - name: localNet
        sources:
          - { slug: "92737", anchor: { definition: "localNet" } }
      - name: Tomita-Takesaki modular operator
        sources:
          - { slug: arxiv-2507.00900, anchor: { theorem: "2.3" } }
          - { slug: arxiv-2507.00900, anchor: { section: "2.1" } }
```

**Two parallel concerns**, kept separate so each is judged by the
right tool:

| Field | Truth source | Influences `goal_coverage_score`? |
| --- | --- | --- |
| `declarations` | scanner over `<lean-root>/**/*.lean` | **yes** |
| `concepts` | `references/<slug>/INDEX.md` Key concepts bullets | no — pure hint for `gap-filler` planning |

`anchor` is a single-key map; the supported kinds are `chapter`,
`section`, `subsection`, `theorem`, `definition`, `lemma`,
`proposition`, `corollary`, `equation`, `page`, `example`. The
matcher uses only `slug` for filtering — the kind/value pair is
human-readable navigation so a developer (or `gap-filler`'s plan
output) knows exactly which page to consult.

Pass `--goals goals.yaml --lean-root QuantumSystem` (or whatever your
Lean tree is) to step 1 to get the per-goal block. Without
`--lean-root`, declarations are tagged `unverified` rather than
guessed — `goal_coverage_score` then reads as the absence of evidence.

## 1. Detect gaps

```bash
python3 .claude/skills/gap-filler/scripts/detect_gaps.py \
    references/ --target-slug arxiv-2202.03357 --output references/gaps.json
```

Expected shape of `gaps.json` (truncated):

```json
{
  "target_slug": "arxiv-2202.03357",
  "counts": {
    "formalized": 1,
    "resolved": 2,
    "partial": 0,
    "suspect": 1,
    "gaps": 10,
    "ambiguous": 0,
    "other_knowledge": 0
  },
  "issues": {"open": 1, "directory": "references/issues"},
  "coverage_score": 0.214,
  "formalized": [
    {"concept": "Umegaki relative entropy", "sources": [...],
     "formalized_annotation": "→ formalized: QuantumSystem.RelativeEntropy.umegaki"}
  ],
  "resolved": [
    {"concept": "C*-algebra",
     "mathlib_annotation": "→ mathlib: Mathlib.Analysis.CStarAlgebra.Classes",
     "sources": [{"slug": "arxiv-2202.03357", "annotation": "..."}]}
  ],
  "suspect": [
    {"concept": "Modular automorphism group",
     "mathlib_annotation": "→ mathlib: Mathlib.Foo.Bar [UNVERIFIED] (...)",
     "sources": [...]}
  ],
  "gaps": [
    {"concept": "Araki relative entropy", "sources": [...]},
    {"concept": "Kosaki variational formula", "sources": [...]},
    {"concept": "Jones index", "sources": [...]}
  ]
}
```

With `--goals goals.yaml --lean-root QuantumSystem` the report also
carries:

```json
{
  "lean_root": "/abs/path/QuantumSystem",
  "lean_declarations_count": 714,
  "goals_summary": {
    "total": 8,
    "satisfied": 7,
    "partially_satisfied": 0,
    "missing": 1,
    "unverified": 0,
    "declarations_total": 20,
    "declarations_verified": 19,
    "goal_coverage_score": 0.95,
    "formula": "verified_declarations / total_declarations"
  },
  "goals": [
    {"id": "gns-construction",
     "goal_status": "satisfied",
     "declarations": [
       {"name": "GNS.Representation", "status": "verified"},
       {"name": "GNS.Construction.isFaithful_iff_separating", "status": "verified"}
     ],
     "missing_declarations": [],
     "concepts": [{"name": "GNS representation",
                   "status": "gap",
                   "matched_sources": [{"slug": "92737", "annotation": "..."}]}]},
    {"id": "ssa-abstract-local-net",
     "goal_status": "missing",
     "declarations": [],
     "missing_declarations": [],
     "missing_concepts": ["Tomita-Takesaki modular operator"]}
  ]
}
```

The TODO goal contributes 1 to `declarations_total` (so empty
`declarations: []` does not silently inflate the score) but 0 to
`declarations_verified`.

## 2. Rank the bibliography

```bash
python3 .claude/skills/gap-filler/scripts/rank_bibliography.py \
    references/arxiv-2202.03357/ \
    --output references/arxiv-2202.03357/bibliography-ranked.json
```

Expected top of `uninvested_top` (abridged; each entry now also carries
a `suggested_search_queries` list). **Query ordering depends on the
entry's publication year**:

- ``year >= 1995`` (modern): `university-pdf:<domain>` rotation is listed
  first (faculty pages often host the paper or author's lecture notes),
  then `lecture-notes`, then `nlab`/`wikipedia`.
- ``year < 1995`` (legacy): `lecture-notes` leads, followed by the
  open-access archives `numdam` and `projecteuclid` and a bare
  `filetype:pdf` pass. University-PDF rotation is **demoted to the
  tail** — iteration-2 showed university domains almost never host
  1980s-era operator-algebra journal papers, so burning WebSearch
  budget on them first is wasteful.

The cutoff is empirical (1995 ≈ onset of institutional preprint
hosting) and editable in
`gap-filler/scripts/rank_bibliography.py::PRE_INSTITUTIONAL_HOSTING_YEAR`.
When `year` is absent from the bibliography entry, the modern ordering
is used as a safe default.

```json
[
  {
    "key": "Jon83", "title": "Index for subfactors",
    "authors": ["Vaughan Jones"], "year": 1983,
    "arxiv": null, "doi": null, "ingested": false,
    "citations_raw": 13, "citation_score": 19.0,
    "matched_token": "Jon83",
    "suggested_search_queries": [
      {"strategy": "lecture-notes",
       "query": "Index subfactors Jones \"lecture notes\" filetype:pdf"},
      {"strategy": "numdam",
       "query": "Index subfactors Jones site:numdam.org"},
      {"strategy": "project-euclid",
       "query": "Index subfactors Jones site:projecteuclid.org"},
      {"strategy": "open-access-pdf",
       "query": "Index subfactors Jones filetype:pdf"},
      {"strategy": "nlab", "query": "Index subfactors site:ncatlab.org"},
      {"strategy": "wikipedia", "query": "Index subfactors wikipedia"},
      {"strategy": "university-pdf:caltech.edu",
       "query": "Index subfactors Jones pdf site:caltech.edu"}
    ]
  }
]
```

## 3. Synthesise a plan

Cross-reference gaps with the ranked bibliography. **When a top entry has
no arxiv/DOI (the common case for operator algebra), try its
`suggested_search_queries` with WebSearch before falling back to
Wikipedia**. For legacy entries this means lecture notes / open-access
archives first; for modern entries it means faculty-hosted PDFs first.
Both routes usually give a cleaner treatment than encyclopedia pages:

| Gap | Best source (preferred) | Mechanism |
|---|---|---|
| `Jones index` (Jon83) | lecture-notes PDF or open-access archive (try `lecture-notes` → `numdam` → `project-euclid` via the emitted queries) | `pdf-to-knowledge` once a PDF URL is found |
| `Kosaki variational formula` (Kos86a) | lecture-notes / open-access PDF first, nLab as fallback | `pdf-to-knowledge` or `web-to-knowledge` depending on what turns up |
| `Modular operator` / `Tomita-Takesaki` (Tak03) | Wikipedia is fine here — it is a well-maintained article | `web-to-knowledge` |

Fall back to Wikipedia / nLab only when the PDF / archive search finds
nothing relevant. The trade-off: WebSearch costs a few tool calls per
concept, but the resulting PDFs tend to carry definitions, proofs, and
worked examples in one place — far more useful than stitching together
a Wikipedia stub plus scattered nLab entries.

A typical plan covers the 3 gaps with the highest intersection of
"blocks many other concepts" and "has a discoverable URL" — the three
rows above.

## 4. Execute (with user approval)

For the first two entries, call `web-to-knowledge`:

```bash
uv run .claude/skills/web-to-knowledge/scripts/fetch.py \
    "https://en.wikipedia.org/wiki/Tomita%E2%80%93Takesaki_theory"
uv run .claude/skills/web-to-knowledge/scripts/fetch.py \
    "https://ncatlab.org/nlab/show/relative+entropy"
```

Then **always** refresh the concept index:

```bash
python3 .claude/skills/pdf-to-knowledge/scripts/update_concepts.py references/
```

## 5. Re-measure

Run step 1 again. Expected delta:

- `resolved` grows by any concepts that now carry a `→ mathlib:`
  annotation on the freshly ingested INDEX.md (Wikipedia Tomita-Takesaki
  typically resolves `VonNeumannAlgebra.commutant`; nLab relative
  entropy resolves `InformationTheory.klDiv`, `MeasureTheory.rnDeriv`).
- `gaps` shrinks by the resolved count.
- `other_knowledge` grows — bullets from the new slugs that the target
  paper does not mention directly but which supplement the topic.

## Side channel — issue tracker (`references/issues/`)

When `verify_mathlib_refs.py mark-unverified` flags a bullet, it
auto-creates a YAML under `references/issues/` so the false positive is
not forgotten across sessions. Re-running the same loop is a no-op (the
dedup key is `kind + slug + concept + candidate`):

```bash
# Manually open an issue (e.g. paper-notation-refactor skipped a candidate)
python3 .claude/skills/gap-filler/scripts/issues.py add references \
    --kind notation-skipped \
    --slug arxiv-2202.03357 \
    --concept "modular automorphism group" \
    --reason "Mathlib scope conflict on σ"

python3 .claude/skills/gap-filler/scripts/issues.py list references
python3 .claude/skills/gap-filler/scripts/issues.py close references \
    --kind unverified-mathlib-ref --slug arxiv-2202.03357 \
    --closed-by "human review"
```

`detect_gaps.py` surfaces `report.issues.open`; treat that count as the
"system already knows about" backlog complementary to `gaps`. A typical
pattern across one ingestion cycle:

```
baseline:    formalized=1 resolved=1 gap=12  issues=0  cov=0.214
after lean_verify rejects modular operator:
             formalized=1 suspect=1 gap=12  issues=1  cov=0.143
after notation-refactor adds → formalized: for it:
             formalized=2 resolved=0 gap=12  issues=0  cov=0.214
```

Note that the third row's `coverage_score` returns to baseline even
though the underlying state changed — the project just discovered that
mathlib's annotation was wrong and replaced it with a local proof. The
trajectory shows up clearly in the history log.

## Side channel — progress history (`references/gaps-history.jsonl`)

Each `detect_gaps.py` run appends one record. Quick way to see what
moved the needle:

```bash
jq -c '{ts: .timestamp, cov: .coverage_score, goal: .goals.goal_coverage_score, issues: .issues_open, fmlz: .counts.formalized, susp: .counts.suspect}' \
    references/gaps-history.jsonl
```

Sample output across a 5-step cycle:

```
{"ts":"2026-05-04T10:00:00Z","cov":0.5,"goal":0.667,"issues":0,"fmlz":1,"susp":0}
{"ts":"2026-05-04T10:05:00Z","cov":0.25,"goal":0.333,"issues":1,"fmlz":1,"susp":1}
{"ts":"2026-05-04T10:10:00Z","cov":0.5,"goal":0.667,"issues":0,"fmlz":2,"susp":0}
```

Pass `--no-history` to suppress, or `--history-log path/elsewhere.jsonl`
to redirect when the default `references/` tree is gitignored.

## When to stop

- `gaps` shrinks to a stable set whose entries are genuinely unformalised
  in mathlib (no amount of recursive ingestion helps).
- The only remaining sources lack discoverable URLs (pre-arxiv 1970s
  math journals) — promote those to the user as "needs human action".
- The ingestion budget (default 3 per invocation) has been used; ask the
  user before approving another round.
