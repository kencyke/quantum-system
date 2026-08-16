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
| `QuantumSystem/Algebra/LocalNet/SplitProperty.lean:ProperContainment` | 3 | The causal collar field `exists_orthogonal_of_properlyContained` is a repository invention carried by no literature definition of the split property — **re-adjudicated 2026-08-15 against the strengthened field, which now also demands `¬ O₃ ≤ O₁`**; this row replaces the `4d8a21b` row, voided by expiry when the field changed | KOE03 defines its own `⋐` by "its *causal complement* `I' := S¹ ∖ Ī` is not the empty set" (`references/arxiv-math-ph-0308031/source.txt:925`); with `I₂` open and `Ī₁` closed, `Ī₁ ⊂ I₂` forces a nonempty connected component `J` of `I₂ ∖ Ī₁`, which is a proper interval with `J ≤ I₂` and `I₁ ⟂ J` — the collar, derived from the source's own separation condition. The added `¬ O₃ ≤ O₁` clause is carried by the same derivation one step further: `J` is nonempty and disjoint from `I₁`, so `¬ J ≤ I₁` is free. dB74 states the thickening shape `O + N ⊂ Ô` that `ofThicken` implements (`references/buchholz-1974-product-states/source.txt:15`), and `ofThicken` proves the clause from strictness of `thicken Λ₁ ⊂ Λ₂` | `ProperContainment`, `ProperContainment.ofThicken` | 4ec09ec (field measured in the **working tree**, not yet committed — re-check on the commit that lands it) | 2026-08-15 |
| `QuantumSystem/Algebra/LocalNet/Net.lean:LocalNet` (also `LocalNet.Faithful`, the `Finset` `CausalOrthogonality` instance, `QuasiLocalAlgebra.lean` module doc) | 4 | The docstring citation "Naaijkens 2012" is a mis-dated citation of NAA13 (arXiv 1311.2717, 2013) with section numbers that match neither work | "Naaijkens 2012" is a different work: P. Naaijkens, *Anyons in Infinite Quantum Systems: QFT in d=2+1 and the Toric Code*, PhD dissertation, Radboud Universiteit Nijmegen, 2012 (handle `2066/92737`). The repo expands the cite itself (`QuantumSystem/Algebra/CStarAlgebra/Representation/Conjugation.lean:45`: "Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.2"), and all cited sections match the thesis TOC (§1.3 "Inductive limits" — quasi-local algebra; §3.2 "Algebraic quantum field theory" — covariance axiom; §3.4 "Quantum lattice systems" — lattice net over 𝒫_f(L)); against NAA13 the same section numbers are nonsense (§1.3 = "Topics not covered"). The note-locator comparison (NAA13 §1.2/§2.4) was made against the wrong work. Residual: a disambiguation nit (expand the bare short cite), not a drift | `LocalNet`, `LocalNet.Faithful` (docstrings); the full cite at `QuantumSystem/Algebra/CStarAlgebra/Representation/Conjugation.lean` | 4ec09ec (working tree) | 2026-08-15 |
| `QuantumSystem/Algebra/LocalNet/Covariance.lean:LocalNet.Covariance` (module doc) | 4 | "Verch 2025 §1.2" appears in no extraction note's source table and could not be verified — suspected phantom citation | Resolves to R. Verch, *Lecture Notes on Operator Algebras and Quantum Field Theory*, arXiv:2507.00900 (2025-07-01); its subsection 1.2 ("Algebraic QFT on Minkowski Spacetime: Haag-Kastler Nets of Local Algebras") states exactly the cited covariance axiom `α_L(𝒜(O)) = 𝒜(L(O))` (source `York-Notes2025.tex` lines 351–353). The extraction notes index only their own corpora, so absence from their source tables is not drift | `LocalNet.Covariance` (module doc) | 4ec09ec (working tree) | 2026-08-15 |
| `QuantumSystem/Algebra/LocalNet/Examples.lean:zeroHom` | 1 | The `zeroHom`/`zeroRep` docstring ("this still exhibits the property rather than trivialising it away") contradicts the repo's own statements that the zero representation trivialises the split property | "Trivialising it away" means annihilation on the zero *space* (where `IsSplitInclusion` is identically false), not trivial satisfaction: the clause "`𝓡(O)` contains `1` regardless, since a von Neumann algebra is unital" is shared verbatim with `SplitProperty.lean`'s `VonNeumannNet.SplitProperty` module prose, whose next sentence states the nonzero-space/zero-space dichotomy the docstring restates; and `Examples.lean`'s own module header concedes the triviality at length ("stated so it is not mistaken for evidence"). The mathematical residue (collapse to `ℂ1` for *any* representation on `ℂ`, sole witness) survives — only the contradiction reading was refuted | `zeroHom` (docstring), `VonNeumannNet.SplitProperty` (module prose), `Examples.lean` module header | 351f5dd (working tree) | 2026-08-15 |
| `QuantumSystem/Algebra/LocalNet/SplitProperty.lean:VonNeumannNet.SplitProperty.isSplitInclusion_commutant` (and `LocalNet.SplitProperty.isSplitInclusion_commutant`) | 4 | The two `isSplitInclusion_commutant` docstrings contradict each other | The two theorems have the same shape (`O₁ ⋐ O₂`, `O₂ ⟂ O_B` ⊢ `IsSplitInclusion 𝓡(O₁) 𝓡(O_B)′`), the second is a one-line specialisation of the first, and the second docstring's summary of the first (Haag duality for the converse, Buchholz's four-term chain) is accurate; no proposition on which they disagree exists in the current tree. Confirmed by the aggregator reading both docstrings in source | `VonNeumannNet.SplitProperty.isSplitInclusion_commutant`, `LocalNet.SplitProperty.isSplitInclusion_commutant` (both docstrings) | 351f5dd (working tree) | 2026-08-15 |
| `QuantumSystem/Algebra/CStarAlgebra/GelfandNaimark.lean:gelfand_naimark_theorem` | 1/3 | The conclusion omits **nondegeneracy** of the representation, which the standard universal-representation statement of Gelfand–Naimark carries — a scope gap in the formalized statement (filed together with a separability half, which is *not* refuted and survives at (c)) | The two existentials are **equivalent**, so nondegeneracy cannot strengthen the conclusion: given isometric `φ : A →⋆ₙₐ[ℂ] 𝓑(H)`, set `K := closure (span (φ(A) H))`; `φ(A)` is `*`-closed so `Kᗮ = {ξ | ∀ a, φ a ξ = 0}`, hence `‖φ a‖ = ‖(φ a)|_K‖` and the corestriction `A → 𝓑(K)` is an isometric `*`-hom that is nondegenerate by construction. Independently, the witness actually used *is* nondegenerate: `GNS.Representation.cyclic : Dense ↑(Submodule.span ℂ {x | ∃ a, self.π a self.ξ = x})` is a field of the GNS triplet, cyclic ⟹ nondegenerate, and an ℓ²-direct sum of nondegenerate representations is nondegenerate. Note the naive route fails and was *not* used: nondegeneracy is not automatic from `Isometry` for a fixed `φ` (`a ↦ φ a ⊕ 0` on `H ⊕ ℂ` is isometric and degenerate) | `GNS.Representation.cyclic`, `GNS.DirectSum.Hilbert`, `GNS.DirectSum.directSumAlgHom`, `GNS.DirectSum.directSumAlgHom_isometry` | 2e21b4b | 2026-08-15 |
| `QuantumSystem/Algebra/VonNeumannAlgebra/StructureTheorem.lean:IsFactor.exists_spatial_tensor_decomposition` (module docs of `StructureTheorem.lean` and `TensorFactor.lean` also cite it) | 4 | Citation "J. Yngvason, arXiv:1401.2652, §5.1, eqs. (38)/(39)" is unverifiable — no `references/` cache exists for it, unlike every other of the nine sources cited in this file set, and neither resolved extraction note lists it in its `## Sources` table | Fetched arXiv:1401.2652 directly (PDF → `pdftotext`): confirmed author J. Yngvason, confirmed §5.1 titled "Causal Independence and Split Property", confirmed eqs. (38)/(39) verbatim-match the docstrings' `𝒜₁ ⊂ 𝒩 ⊂ 𝒜₂′` / tensor-decomposition content, down to which symbol plays which role. The "no cache ⇒ suspicious" inference does not hold — it is a caching-completeness gap (8/9 sources cached), not a correctness signal | `StructureTheorem.lean` module doc + `IsFactor.exists_spatial_tensor_decomposition` docstring, `TensorFactor.lean` module doc | 351f5dd (working tree) | 2026-08-15 |
| `QuantumSystem/Algebra/CStarAlgebra/GelfandNaimark.lean` (module doc) | 4 | The four textbook locators — Murphy *C\*-algebras and Operator Theory* Thm 3.4.1, Pedersen *C\*-Algebras and Their Automorphism Groups* §3.7, Blackadar *Operator Algebras* II.6.4, Takesaki *Theory of Operator Algebras I* I.9.18 — are unverifiable/phantom citations, since the repo's own same-day extraction note `docs/math/separable-faithful-representation.md` records all five books (plus Dixmier) as **not retrieved**, with no `references/` cache and its own `## Not investigated` calling the attribution "unverified" | Independently-fetched bibliographic data (OpenLibrary + a 2007 Library-of-Congress TOC snapshot via the Wayback Machine, for Murphy; Crossref chapter listings for Pedersen/Blackadar/Takesaki) confirms each cited chapter is *exactly* the chapter where the noncommutative Gelfand–Naimark theorem belongs in that book's published structure — Murphy ch. 3 "Ideals and Positive Functionals"; Pedersen ch. 3 "Functionals and Representations"; Blackadar ch. II "C\*-Algebras"; Takesaki ch. I "Fundamentals of Banach Algebras and C\*-Algebras" — not a mismatch to an unrelated topic. This refutes the "phantom citation" reading (chapter-level, tier b). The exact section/theorem digit within each chapter (3.4.1 / §3.7 / II.6.4 / I.9.18) could not be independently pinned down by any source reachable in this sandbox and remains open at tier (c) — reported separately, not as a blocker | module doc of `GelfandNaimark.lean` (no Lean declaration dependency; refutation rests on external bibliographic sources, not on repo code) | a2fa4f5 | 2026-08-16 |
