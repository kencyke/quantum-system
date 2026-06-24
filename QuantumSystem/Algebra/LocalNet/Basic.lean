module

public import QuantumSystem.Channel

/-!
# Local Net of Matrix Algebras — basic data

This file carries the **data** of a local net of matrix algebras and the region-index
combinatorics on which the AQFT net properties are built. An AQFT system assigns to each
lattice region `Λ` an algebra `𝔄(Λ)` of observables; for finite-dimensional quantum spin
systems this specialises to:

- a lattice of **sites** `L` (an arbitrary type with `DecidableEq`),
- a finite local index type `ℂ^{n_x}` at each site `x`,
- regions `Λ : Finset L.sites`,
- local algebra `𝔄(Λ) = ⊗_{x ∈ Λ} M_{n_x}(ℂ)` realised as
  `Matrix (Π s ∈ Λ, idx s) (Π s ∈ Λ, idx s) ℂ`.

This file provides the carrier structure, the derived region-index types, the index-combiner
equivalence `combineIdx` realising `regionIdx Λ_total ≃ regionIdx Λ × regionIdx (Λ_total \ Λ)`,
the cardinality factorisation, the transport `regionIdxCongr`, and the bipartite and tripartite
region factorisation equivalences (`regionIdxPairEquiv`, `regionIdxTripleEquiv`).

The net **properties** built on this data live in sibling modules:
`LocalNet.Isotony` (the embedding `𝔄(Λ) ↪ 𝔄(Λ_total)` + functoriality), `LocalNet.Locality`
(disjoint regions commute), `LocalNet.QuasiLocal` (quasi-local C⋆-algebra), `LocalNet.Covariance`
(symmetry action). Restriction / partial trace lives in `Analysis/Matrix/PartialTrace.lean`.

## References

* Verch 2025 (`https://arxiv.org/abs/2507.00900`)
* Naaijkens 2012 (`https://repository.ubn.ru.nl/handle/2066/92737`)
-/

@[expose] public section

/-- Data for a **local net of matrix algebras** on a (possibly infinite) lattice of sites.
    Each site `s : sites` carries a finite index type `localIdx s` whose cardinality is the
    local Hilbert-space dimension. The local algebra at a *finite* region `Λ : Finset sites`
    is then the matrix algebra on the dependent product `Π s ∈ Λ, localIdx s` — finite even
    when `sites` is infinite, since regions are finite subsets. Leaving `sites` unrestricted
    (only `DecidableEq`) is what allows the quasi-local algebra to be a genuine inductive
    limit over the directed set of finite regions, as in Naaijkens 2012 §1.3 and
    Bratteli–Robinson Vol.2 §6.2. -/
structure LocalNet where
  /-- Lattice of sites — an arbitrary type; regions are its finite subsets. -/
  sites : Type*
  [sitesDecEq : DecidableEq sites]
  /-- Local Hilbert-space index type at each site. -/
  localIdx : sites → Type*
  [localFintype : ∀ s, Fintype (localIdx s)]
  [localDecEq : ∀ s, DecidableEq (localIdx s)]

namespace LocalNet

attribute [instance] sitesDecEq localFintype localDecEq

variable (L : LocalNet)

/-- Index type of a region: dependent product of local indices over the sites in `Λ`. -/
abbrev regionIdx (Λ : Finset L.sites) : Type _ := ∀ s : Λ, L.localIdx s.val

/-- A region's index type stays nonempty when restricting to a sub-region: any element of
    `regionIdx Λ_total` restricts to an element of `regionIdx Λ` along `h : Λ ⊆ Λ_total`. -/
lemma regionIdx_nonempty_of_subset {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    [hne : Nonempty (L.regionIdx Λ_total)] : Nonempty (L.regionIdx Λ) :=
  hne.elim fun f => ⟨fun s => f ⟨s.val, h s.property⟩⟩

/-- Local algebra `𝔄(Λ)` at a region — concrete matrix algebra over `ℂ`. -/
abbrev localAlgebra (Λ : Finset L.sites) : Type _ :=
  Matrix (L.regionIdx Λ) (L.regionIdx Λ) ℂ

/-- Density matrices on a region (positive semi-definite, trace 1). -/
abbrev densityMatrix (Λ : Finset L.sites) : Type _ :=
  DensityMatrix (L.regionIdx Λ)

/-! ### Combining region indices via disjoint union -/

/-- For `Λ ⊆ Λ_total`, the index type of the larger region splits as a product:
    `regionIdx Λ × regionIdx (Λ_total \ Λ) ≃ regionIdx Λ_total`. This realises the tensor
    factorisation `ℋ_Λ_total = ℋ_Λ ⊗ ℋ_{Λ_total \ Λ}` underlying isotony and partial trace.
    The factorisation is made formal at the operator level by `LocalNet.tensorEquiv`
    (`TensorDecomposition`), an algebra isomorphism of the corresponding operator algebras. -/
def combineIdx {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    (L.regionIdx Λ × L.regionIdx (Λ_total \ Λ)) ≃ L.regionIdx Λ_total where
  toFun ab s :=
    if hs : s.val ∈ Λ then ab.1 ⟨s.val, hs⟩
    else ab.2 ⟨s.val, Finset.mem_sdiff.mpr ⟨s.property, hs⟩⟩
  invFun f :=
    (fun s => f ⟨s.val, h s.property⟩,
     fun s => f ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩)
  left_inv := by
    rintro ⟨a, b⟩
    ext1
    · funext s
      have hs : s.val ∈ Λ := s.property
      simp [hs]
    · funext s
      have hns : s.val ∉ Λ := (Finset.mem_sdiff.mp s.property).2
      simp [hns]
  right_inv := by
    intro f
    funext s
    by_cases hs : s.val ∈ Λ <;> simp [hs]

/-! ### Pointwise behaviour of `combineIdx` -/

variable {L} in
@[simp] lemma combineIdx_apply_mem
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (a : L.regionIdx Λ) (b : L.regionIdx (Λ_total \ Λ))
    (s : ↥Λ_total) (hs : s.val ∈ Λ) :
    (L.combineIdx h (a, b)) s = a ⟨s.val, hs⟩ := by
  simp only [combineIdx, Equiv.coe_fn_mk]
  rw [dif_pos hs]

variable {L} in
@[simp] lemma combineIdx_apply_not_mem
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (a : L.regionIdx Λ) (b : L.regionIdx (Λ_total \ Λ))
    (s : ↥Λ_total) (hs : s.val ∉ Λ) :
    (L.combineIdx h (a, b)) s
      = b ⟨s.val, Finset.mem_sdiff.mpr ⟨s.property, hs⟩⟩ := by
  simp only [combineIdx, Equiv.coe_fn_mk]
  rw [dif_neg hs]

/-- Cardinality factorisation for region indices induced by `combineIdx`. -/
theorem card_regionIdx_total {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    Fintype.card (L.regionIdx Λ_total) =
      Fintype.card (L.regionIdx Λ) * Fintype.card (L.regionIdx (Λ_total \ Λ)) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (L.combineIdx h).symm

/-- Transport `regionIdx` along a Finset equality. -/
def regionIdxCongr {Λ Λ' : Finset L.sites} (h : Λ = Λ') :
    L.regionIdx Λ ≃ L.regionIdx Λ' :=
  h ▸ Equiv.refl _

@[simp] lemma regionIdxCongr_apply
    {Λ Λ' : Finset L.sites} (h : Λ = Λ') (x : L.regionIdx Λ)
    {s : L.sites} (hs : s ∈ Λ) (hs' : s ∈ Λ') :
    (L.regionIdxCongr h x) ⟨s, hs'⟩ = x ⟨s, hs⟩ := by
  subst h
  rfl

/-! ### Region equivalences

Bipartite and tripartite factorisations of a region's index type over arbitrary site types:
`regionIdx {a, b} ≃ localIdx a × localIdx b` and the right-associated three-element analogue.
Both are direct definitions with concrete `toFun`, so every projection evaluates by `rfl`. -/

variable (L : LocalNet)

/-- **1-element factorisation**: `regionIdx {a} ≃ localIdx a`. Evaluation at the single site `a`. -/
def regionIdxSingletonEquiv (a : L.sites) :
    L.regionIdx ({a} : Finset L.sites) ≃ L.localIdx a where
  toFun f := f ⟨a, Finset.mem_singleton_self a⟩
  invFun x := fun ⟨s, hs⟩ => (Finset.mem_singleton.mp hs) ▸ x
  left_inv f := by
    funext ⟨s, hs⟩
    obtain rfl : s = a := Finset.mem_singleton.mp hs
    rfl
  right_inv x := rfl

@[simp] lemma regionIdxSingletonEquiv_apply (a : L.sites)
    (f : L.regionIdx ({a} : Finset L.sites)) :
    L.regionIdxSingletonEquiv a f = f ⟨a, Finset.mem_singleton_self a⟩ := rfl

/-- **2-element factorisation**: `regionIdx {a, b} ≃ localIdx a × localIdx b` when
    `a ≠ b`. Direct definition with concrete `toFun` so both projections evaluate by `rfl`. -/
def regionIdxPairEquiv {a b : L.sites} (hab : a ≠ b) :
    L.regionIdx ({a, b} : Finset L.sites) ≃ L.localIdx a × L.localIdx b where
  toFun f :=
    (f ⟨a, Finset.mem_insert_self a {b}⟩,
     f ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)⟩)
  invFun ab := fun ⟨s, hs⟩ =>
    if h : s = a then h ▸ ab.1
    else
      have hsb : s = b := by
        rcases Finset.mem_insert.mp hs with h' | h'
        · exact absurd h' h
        · exact Finset.mem_singleton.mp h'
      hsb ▸ ab.2
  left_inv f := by
    funext ⟨s, hs⟩
    by_cases hsa : s = a
    · subst hsa
      simp
    · have hsb : s = b := by
        rcases Finset.mem_insert.mp hs with h' | h'
        · exact absurd h' hsa
        · exact Finset.mem_singleton.mp h'
      subst hsb
      simp [hsa]
  right_inv ab := by
    have hba : b ≠ a := fun h_eq => hab h_eq.symm
    ext1
    · simp
    · simp [hba]

/-- Closed-form unfolding of `regionIdxPairEquiv` as a pair. -/
@[simp] lemma regionIdxPairEquiv_apply {a b : L.sites} (hab : a ≠ b)
    (f : L.regionIdx ({a, b} : Finset L.sites)) :
    L.regionIdxPairEquiv hab f =
      (f ⟨a, Finset.mem_insert_self a {b}⟩,
       f ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)⟩) := rfl

/-- Closed-form first projection of `regionIdxPairEquiv` — picks out the value at site `a`. -/
@[simp] lemma regionIdxPairEquiv_apply_fst {a b : L.sites} (hab : a ≠ b)
    (f : L.regionIdx ({a, b} : Finset L.sites)) :
    (L.regionIdxPairEquiv hab f).1 = f ⟨a, Finset.mem_insert_self a {b}⟩ := rfl

/-- Closed-form second projection of `regionIdxPairEquiv` — picks out the value at site `b`. -/
@[simp] lemma regionIdxPairEquiv_apply_snd {a b : L.sites} (hab : a ≠ b)
    (f : L.regionIdx ({a, b} : Finset L.sites)) :
    (L.regionIdxPairEquiv hab f).2 =
      f ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)⟩ := rfl

/-- **3-element factorisation (right-associated)**:
    `regionIdx {a, b, c} ≃ localIdx a × localIdx b × localIdx c` when the sites are
    pairwise distinct. Direct definition with concrete `toFun` so all three projections
    evaluate by `rfl`. -/
def regionIdxTripleEquiv {a b c : L.sites} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    L.regionIdx ({a, b, c} : Finset L.sites) ≃
      L.localIdx a × L.localIdx b × L.localIdx c where
  toFun f :=
    (f ⟨a, Finset.mem_insert_self a {b, c}⟩,
     f ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self b {c})⟩,
     f ⟨c, Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))⟩)
  invFun abc := fun ⟨s, hs⟩ =>
    if h : s = a then h ▸ abc.1
    else if h' : s = b then h' ▸ abc.2.1
    else
      have hsc : s = c := by
        rcases Finset.mem_insert.mp hs with hh | hh
        · exact absurd hh h
        · rcases Finset.mem_insert.mp hh with hh | hh
          · exact absurd hh h'
          · exact Finset.mem_singleton.mp hh
      hsc ▸ abc.2.2
  left_inv f := by
    funext ⟨s, hs⟩
    by_cases hsa : s = a
    · subst hsa; simp
    by_cases hsb : s = b
    · subst hsb; simp [hsa]
    have hsc : s = c := by
      rcases Finset.mem_insert.mp hs with hh | hh
      · exact absurd hh hsa
      · rcases Finset.mem_insert.mp hh with hh | hh
        · exact absurd hh hsb
        · exact Finset.mem_singleton.mp hh
    subst hsc; simp [hsa, hsb]
  right_inv abc := by
    have hba : b ≠ a := fun h => hab h.symm
    have hca : c ≠ a := fun h => hac h.symm
    have hcb : c ≠ b := fun h => hbc h.symm
    ext1
    · simp
    · ext1
      · simp [hba]
      · simp [hca, hcb]

/-- Closed-form first projection of `regionIdxTripleEquiv` — value at site `a`. -/
@[simp] lemma regionIdxTripleEquiv_apply_fst {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : L.regionIdx ({a, b, c} : Finset L.sites)) :
    (L.regionIdxTripleEquiv hab hbc hac f).1 = f ⟨a, Finset.mem_insert_self a {b, c}⟩ := rfl

/-- Second projection of `regionIdxTripleEquiv` — value at site `b`. -/
@[simp] lemma regionIdxTripleEquiv_apply_snd_fst {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : L.regionIdx ({a, b, c} : Finset L.sites)) :
    (L.regionIdxTripleEquiv hab hbc hac f).2.1 =
      f ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self b {c})⟩ := rfl

/-- Third projection of `regionIdxTripleEquiv` — value at site `c`. -/
@[simp] lemma regionIdxTripleEquiv_apply_snd_snd {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : L.regionIdx ({a, b, c} : Finset L.sites)) :
    (L.regionIdxTripleEquiv hab hbc hac f).2.2 =
      f ⟨c, Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))⟩ := rfl

/-- **Compatibility of the triple factorisation with the `{a, b}`-cut.** Reading a region index
of `{a, b, c}` that was assembled from an `{a, b}`-part `ab` and a complement-part `cc` (via
`combineIdx`) through the three-element factorisation returns the `a`- and `b`-values from `ab`
(via `regionIdxPairEquiv`) and the `c`-value from `cc`. This is the index-level statement that
the associative regrouping `(localIdx a × localIdx b) × localIdx c` underlying `combineIdx` for
`{a, b} ⊆ {a, b, c}` agrees with the right-associated `regionIdxTripleEquiv`. -/
theorem regionIdxTripleEquiv_combineIdx {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_ab : ({a, b} : Finset L.sites) ⊆ {a, b, c})
    (ab : L.regionIdx ({a, b} : Finset L.sites))
    (cc : L.regionIdx (({a, b, c} : Finset L.sites) \ {a, b}))
    (hc : c ∈ ({a, b, c} : Finset L.sites) \ {a, b}) :
    L.regionIdxTripleEquiv hab hbc hac (L.combineIdx h_ab (ab, cc))
      = ((L.regionIdxPairEquiv hab ab).1, (L.regionIdxPairEquiv hab ab).2, cc ⟨c, hc⟩) := by
  have hca : c ∉ ({a, b} : Finset L.sites) := (Finset.mem_sdiff.mp hc).2
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hca]

/-- **Compatibility of the triple factorisation with the `{b, c}`-cut.** The dual of
`regionIdxTripleEquiv_combineIdx` for the inclusion `{b, c} ⊆ {a, b, c}`: the `a`-value comes from
the complement part, the `b`- and `c`-values from the `{b, c}`-part via `regionIdxPairEquiv`. -/
theorem regionIdxTripleEquiv_combineIdx_bc {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_bc : ({b, c} : Finset L.sites) ⊆ {a, b, c})
    (bc : L.regionIdx ({b, c} : Finset L.sites))
    (aa : L.regionIdx (({a, b, c} : Finset L.sites) \ {b, c}))
    (ha : a ∈ ({a, b, c} : Finset L.sites) \ {b, c}) :
    L.regionIdxTripleEquiv hab hbc hac (L.combineIdx h_bc (bc, aa))
      = (aa ⟨a, ha⟩, (L.regionIdxPairEquiv hbc bc).1, (L.regionIdxPairEquiv hbc bc).2) := by
  have haa : a ∉ ({b, c} : Finset L.sites) := (Finset.mem_sdiff.mp ha).2
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [haa]

/-- **Compatibility of the pair factorisation with the `{a}`-cut.** For `{a} ⊆ {a, b}`, the
`a`-value comes from the singleton part, the `b`-value from the complement part. -/
theorem regionIdxPairEquiv_combineIdx {a b : L.sites} (hab : a ≠ b)
    (h_a : ({a} : Finset L.sites) ⊆ {a, b})
    (ma : L.regionIdx ({a} : Finset L.sites))
    (mb : L.regionIdx (({a, b} : Finset L.sites) \ {a}))
    (hb : b ∈ ({a, b} : Finset L.sites) \ {a}) :
    L.regionIdxPairEquiv hab (L.combineIdx h_a (ma, mb))
      = (L.regionIdxSingletonEquiv a ma, mb ⟨b, hb⟩) := by
  have hba : b ∉ ({a} : Finset L.sites) := (Finset.mem_sdiff.mp hb).2
  refine Prod.ext ?_ ?_ <;> simp [hba]

end LocalNet
