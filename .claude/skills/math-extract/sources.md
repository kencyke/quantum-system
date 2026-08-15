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
| KOE03 | S. Köster, *Structure of Coset Models*, dissertation, arXiv math-ph/0308031 (2003) | retrieved | `references/arxiv-math-ph-0308031/` | arXiv | 2026-08-14 | arXiv LaTeX (rung 1), verbatim; single source file `mathphkoediss.tex` |
| HS17 | S. Hollands, K. Sanders, *Entanglement measures and their properties in quantum field theory*, arXiv 1702.04924 | retrieved | `references/arxiv-1702.04924/` | arXiv | 2026-08-14 | arXiv LaTeX (rung 1), verbatim. Citation-key trap: HS17's `buchholz_4` = Buchholz–Wichmann 1986, *not* Buchholz 1974; `buchholz_2` = BDF87; `doplicher_4` = DL84 (verified against its bibliography) |
| dB74 | D. Buchholz, *Product states for local algebras*, Comm. Math. Phys. 36 (1974) 287–304 | partial | `references/buchholz-1974-product-states/` | published | 2026-08-15 | Project Euclid PDF; MinerU `hybrid-engine --effort high`, pp. 1–8 of 18; mineru-unchecked. Cor. 2.4 proves product state ⇒ interpolating type I factors; the converse is asserted just after it. **locator p. 292 (Ch. II items a) and b)) is adjudicated**: the page number was recovered by extracting the OCR text layer of `mineru/downloaded/hybrid_auto/downloaded_origin.pdf` with `pypdf`, **independently of MinerU** — the page carries the running head `292 D. Buchholz` and reproduces the passage word for word including the typo `maped`. Tier stays **(b)** (`mineru-cross-checked-against-PDF-text-layer`) because no page *image* comparison is possible: `pdftoppm`, `pdftotext`, `mutool` and `gs` are all absent from this container. The same extraction resolves item b)'s footnote — it reads *This example is due to Araki*, so that construction is **Araki's, not Buchholz's**. The paper carries **three** different separation relations (translation buffer in Thm 2.2, closure in Ch. II a), positive distance in Ch. III); citing "dB74's separation condition" without saying which is ambiguous |
| DL84 | S. Doplicher, R. Longo, *Standard and split inclusions of von Neumann algebras*, Invent. Math. 75 (1984) 493–536 | partial | `references/doplicher-longo-1984-standard-split/` | published | 2026-08-14 | GDZ digitization (volume `PPN356556735_0075`, article div `LOG_0034`, found via the METS file); MinerU `hybrid-engine --effort high`, pp. 1–14 of 44 (§0–§4); mineru-unchecked. locator Prop. 1.2: says joint cyclic-separating vectors exist *under* standard action / properly infinite commutants — citing it for bare "properly infinite on separable ℋ" (as KOE03 does at its source.txt 6666–6669) drops needed hypotheses. §9–10 (the non-split field theories) not converted. Its §0 phrases the split property's separation as `space-like separated by non-zero distance` and cites dB74, whose cached scope (§III, smooth boundaries + positive distance, free neutral massive scalar) is **narrower** than that paraphrase |

<!-- Append below. Newest last. -->
| HM06 | H. Halvorson, M. Müger, *Algebraic Quantum Field Theory*, in *Handbook of the Philosophy of Physics*, arXiv math-ph/0602036 | retrieved | `references/arxiv-math-ph-0602036/` | arXiv | 2026-08-15 | arXiv LaTeX (rung 1), verbatim; single source file `reconstruction.tex`. Leaves "spacelike separated" **undefined** and writes the causal complement `O'` with no formula, so it cannot be cited for either. Its `\begin{fact}` (strictly ⇒ strongly spacelike separated) carries no proof and no citation. Prop. `frees` is stated for *strongly* but its proof's first line says *strictly* — a typo; the proposition as stated is proved |
| GLRV99 | D. Guido, R. Longo, J. E. Roberts, R. Verch, *Charged sectors, spin and statistics in quantum field theory on curved spacetimes*, arXiv math-ph/9906019 | retrieved | `references/arxiv-math-ph-9906019/` | arXiv | 2026-08-15 | arXiv LaTeX (rung 1), verbatim; single source file `main.tex`. **Notation trap: `𝒪^⊥` denotes both the sieve `{𝒪₁ ∈ 𝒦 : 𝒪₁ ⊥ 𝒪}` (§3.1) and the point set `M ∖ J̄(𝒪)` (§2.1), in one paper.** Cross-reference errata: the Extension Theorem's proof cites "Lemma 3.A.4" where 3A.5 is needed and prints three spellings of one label; Lemma 3.6 says `dimension $\geq 2$` then treats dimension two as the remaining case; §3.5 refers to `hatduality` as a Lemma where the environment is a Proposition. locator §3.1 (`source.txt` 1218–1223): the axiom list for ⊥ is a),b),c) **only**, and the source says the list is a floor (`The necessary properties will be introduced as needed`); a **fourth** condition appears at `source.txt` 1878–1882, before Theorem 3.13 |
| NAA13 | P. Naaijkens, *Quantum spin systems on infinite lattices*, arXiv 1311.2717 | retrieved | `references/arxiv-1311.2717/` | arXiv | 2026-08-15 | arXiv LaTeX (rung 1), verbatim; multi-file (`aqft.tex`, `qlattice.tex`, `opalg.tex`, …), macros in `qlattice.tex`. The only corpus source stating `𝒪 = 𝒪″` for double cones, and it states it without proof. Its `𝒫_f(Γ)` **contains `∅`**, with `𝒜(∅) = ℂI` fixed explicitly — so any claim that the lattice index set fails an existence-of-a-⊥-partner condition is false for *this* index set |
| BGL93 | R. Brunetti, D. Guido, R. Longo, *Modular structure and duality in conformal quantum field theory*, arXiv funct-an/9302008 | retrieved | `references/arxiv-funct-an-9302008/` | arXiv | 2026-08-15 | arXiv LaTeX (rung 1), verbatim; single source file `main.tex`. locator Cor. 2.7: discharged by `\proof Immediate, see [\ref(Long1)].` and conditional on Remark 2.6's spectral hypothesis — do not cite it as an unconditional type III₁ result. locator Thm 3.3: its proof cites a **Lemma 3.4 that does not exist**; Lemma 3.2 is meant. Its "distal split property" (§3 assumption (b)) is an **existential over one pair of regions**, not a metric strengthening of the separation relation. Its non-split net `ℬ(𝒪) = 𝒜(π⁻¹𝒪)` is attributed to a **private remark** of Buchholz, so no locator can ever exist for the attribution |
| BFV01 | R. Brunetti, K. Fredenhagen, R. Verch, *The generally covariant locality principle*, arXiv math-ph/0112041 | retrieved | `references/arxiv-math-ph-0112041/` | arXiv | 2026-08-15 | arXiv LaTeX (rung 1), verbatim. **The distributed source contains two complete `\begin{document}…\end{document}` bodies** — `source.txt` lines 118–2851 and 2957–4225 (`source.flat.txt` offsets 3687 and 144453). Only the first is the compiled paper; the second is a shorter earlier draft that even defines `\frakA` differently. **Take every locator from the first body**, and expect `grep -F` to return 2 for shared passages — that is not a duplicate-quote defect. Its `𝒦(M,ḡ)` is defined by two conditions only (relatively compact, causally convex), and openness/connectedness/non-emptiness are forced only by the *next* sentence's demand that each region be an object of `𝔐`; the two readings give different index sets. `cf.\ condition $(ii)$` points at orientation-preservation where causal convexity is condition (i), in **both** bodies, so authorial |
