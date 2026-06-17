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
the cardinality factorisation, the transport `regionIdxCongr`, and the `n`-partite region
factorisation equivalences (`regionIdxPairEquiv`, `regionIdxTripleEquiv`, `regionIdxCompl*`).

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
    factorisation `ℋ_Λ_total = ℋ_Λ ⊗ ℋ_{Λ_total \ Λ}` underlying isotony and partial trace. -/
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

Generic equivalences over arbitrary site types — used both directly (for any finite region)
and as building blocks for the bipartite (`regionIdxPairEquiv`) and tripartite
(`regionIdxTripleEquiv`, `regionIdxTripleEquiv'`) factorisations below. -/

variable (L : LocalNet)

/-- Singleton region: `regionIdx {s} ≃ localIdx s`. -/
def singletonRegionIdxEquiv (s : L.sites) :
    L.regionIdx ({s} : Finset L.sites) ≃ L.localIdx s where
  toFun f := f ⟨s, Finset.mem_singleton.mpr rfl⟩
  invFun x := fun ⟨v, hv⟩ =>
    (Finset.mem_singleton.mp hv).symm ▸ x
  left_inv f := by
    funext ⟨v, hv⟩
    have hvs : v = s := Finset.mem_singleton.mp hv
    subst hvs
    rfl
  right_inv x := rfl

@[simp] private lemma singletonRegionIdxEquiv_apply (s : L.sites)
    (f : L.regionIdx ({s} : Finset L.sites)) :
    L.singletonRegionIdxEquiv s f = f ⟨s, Finset.mem_singleton.mpr rfl⟩ := rfl

/-! ### Generic n-partite primitives

Building blocks for any finite region: `regionIdx ∅ ≃ PUnit`, an `insert`-based recursive
split, and (for finite site types) the universal product form
`regionIdx Finset.univ ≃ Π s, localIdx s`. Two- and three-element factor equivs are derived
from the recursive split — adding more partite counts (4, 5, ...) is now a one-liner with no
new boilerplate. -/

/-- The empty region: `regionIdx ∅ ≃ PUnit`. The dependent product over the empty
    subtype has a unique element. -/
def regionIdxEmptyEquiv : L.regionIdx (∅ : Finset L.sites) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := fun s => absurd s.property (Finset.notMem_empty _)
  left_inv f := by
    funext s
    exact absurd s.property (Finset.notMem_empty _)
  right_inv _ := rfl

/-- **Recursive split (region composition rule)**: for `s ∉ Λ`,
    `regionIdx (insert s Λ) ≃ localIdx s × regionIdx Λ`.

    This is the core composition primitive — repeated application gives factorisation
    of any finitely-enumerated region into per-site factors. Built from `combineIdx`
    applied to the singleton `{s} ⊆ insert s Λ`, with the complementary region
    `insert s Λ \ {s}` reducing to `Λ`. -/
def regionIdxInsertEquiv {s : L.sites} {Λ : Finset L.sites} (hs : s ∉ Λ) :
    L.regionIdx (insert s Λ) ≃ L.localIdx s × L.regionIdx Λ :=
  have h_sub : ({s} : Finset L.sites) ⊆ insert s Λ :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self s Λ)
  have h_compl_eq : insert s Λ \ {s} = Λ := by
    rw [Finset.insert_sdiff_of_mem _ (Finset.mem_singleton_self s),
        Finset.sdiff_eq_self_iff_disjoint.mpr (Finset.disjoint_singleton_right.mpr hs)]
  (L.combineIdx h_sub).symm.trans
    (Equiv.prodCongr (L.singletonRegionIdxEquiv s) (L.regionIdxCongr h_compl_eq))

/-- The universal region: `regionIdx Finset.univ ≃ Π s : sites, localIdx s`.
    Collapses the `Finset.univ`-subtype back to the underlying type. Requires `Fintype sites`
    (the only place a finite site set is needed; the rest of the API runs on infinite lattices). -/
def regionIdxUnivEquiv [Fintype L.sites] : L.regionIdx (Finset.univ : Finset L.sites) ≃
    ∀ s : L.sites, L.localIdx s where
  toFun f s := f ⟨s, Finset.mem_univ s⟩
  invFun g := fun ⟨s, _⟩ => g s
  left_inv f := by funext ⟨s, _⟩; rfl
  right_inv _ := rfl

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
@[simp] private lemma regionIdxPairEquiv_apply_fst {a b : L.sites} (hab : a ≠ b)
    (f : L.regionIdx ({a, b} : Finset L.sites)) :
    (L.regionIdxPairEquiv hab f).1 = f ⟨a, Finset.mem_insert_self a {b}⟩ := rfl

/-- Closed-form second projection of `regionIdxPairEquiv` — picks out the value at site `b`. -/
@[simp] private lemma regionIdxPairEquiv_apply_snd {a b : L.sites} (hab : a ≠ b)
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
@[simp] private lemma regionIdxTripleEquiv_apply_fst {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : L.regionIdx ({a, b, c} : Finset L.sites)) :
    (L.regionIdxTripleEquiv hab hbc hac f).1 = f ⟨a, Finset.mem_insert_self a {b, c}⟩ := rfl

/-- Second projection of `regionIdxTripleEquiv` — value at site `b`. -/
@[simp] private lemma regionIdxTripleEquiv_apply_snd_fst {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : L.regionIdx ({a, b, c} : Finset L.sites)) :
    (L.regionIdxTripleEquiv hab hbc hac f).2.1 =
      f ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self b {c})⟩ := rfl

/-- Third projection of `regionIdxTripleEquiv` — value at site `c`. -/
@[simp] private lemma regionIdxTripleEquiv_apply_snd_snd {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : L.regionIdx ({a, b, c} : Finset L.sites)) :
    (L.regionIdxTripleEquiv hab hbc hac f).2.2 =
      f ⟨c, Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))⟩ := rfl

/-- **3-element factorisation (left-associated)**: the alternate
    `regionIdx {a, b, c} ≃ (localIdx a × localIdx b) × localIdx c` view, used when the
    bipartite split sees the pair `(a, b)` together against `c`. -/
def regionIdxTripleEquiv' {a b c : L.sites} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    L.regionIdx ({a, b, c} : Finset L.sites) ≃
      (L.localIdx a × L.localIdx b) × L.localIdx c :=
  (L.regionIdxTripleEquiv hab hbc hac).trans (Equiv.prodAssoc _ _ _).symm

/-- **Pair-complement on the left site**: for the two-element region `{a, b}` with
    `a ≠ b`, the index type of the complement of `{a}` reduces to `localIdx b`.
    Direct realisation of "evaluate at the unique remaining site `b`". -/
def regionIdxComplLeftSite {a b : L.sites} (hab : a ≠ b) :
    L.regionIdx (({a, b} : Finset L.sites) \ {a}) ≃ L.localIdx b where
  toFun f := f ⟨b, Finset.mem_sdiff.mpr
    ⟨Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl),
     Finset.notMem_singleton.mpr (fun h => hab h.symm)⟩⟩
  invFun y := fun ⟨s, hs⟩ =>
    have hsb : s = b := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs.1 with h | h
      · exact absurd h hs.2
      · exact h
    hsb ▸ y
  left_inv f := by
    funext ⟨s, hs⟩
    have hsb : s = b := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs.1 with h | h
      · exact absurd h hs.2
      · exact h
    subst hsb
    rfl
  right_inv y := rfl

/-- **Pair-complement on the right site**: dual of `regionIdxComplLeftSite` — the
    complement of `{b}` in `{a, b}` reduces to `localIdx a`. -/
def regionIdxComplRightSite {a b : L.sites} (hab : a ≠ b) :
    L.regionIdx (({a, b} : Finset L.sites) \ {b}) ≃ L.localIdx a where
  toFun f := f ⟨a, Finset.mem_sdiff.mpr
    ⟨Finset.mem_insert_self a {b}, Finset.notMem_singleton.mpr hab⟩⟩
  invFun y := fun ⟨s, hs⟩ =>
    have hsa : s = a := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs.1 with h | h
      · exact h
      · exact absurd h hs.2
    hsa ▸ y
  left_inv f := by
    funext ⟨s, hs⟩
    have hsa : s = a := by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs.1 with h | h
      · exact h
      · exact absurd h hs.2
    subst hsa
    rfl
  right_inv y := rfl

/-- **Triple-complement, first site**: for pairwise-distinct `a, b, c : L.sites`,
    `regionIdx ({a, b, c} \ {a}) ≃ localIdx b × localIdx c`. Direct construction
    (no `regionIdxCongr` transport) so pointwise evaluation reduces by computation,
    enabling the marginal-compatibility helpers used by SSA-style proofs. -/
noncomputable def regionIdxComplFirst {a b c : L.sites}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    L.regionIdx (({a, b, c} : Finset L.sites) \ ({a} : Finset _)) ≃
      L.localIdx b × L.localIdx c where
  toFun f :=
    (f ⟨b, Finset.mem_sdiff.mpr ⟨
            Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
            Finset.notMem_singleton.mpr hab.symm⟩⟩,
     f ⟨c, Finset.mem_sdiff.mpr ⟨
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)),
            Finset.notMem_singleton.mpr hac.symm⟩⟩)
  invFun xbc := fun ⟨v, hv⟩ =>
    if h : v = b then h ▸ xbc.1
    else
      have hvc : v = c := by
        rw [Finset.mem_sdiff] at hv
        rcases Finset.mem_insert.mp hv.1 with rfl | h2
        · exact absurd (Finset.mem_singleton_self _) hv.2
        · rcases Finset.mem_insert.mp h2 with rfl | h3
          · exact absurd rfl h
          · exact Finset.mem_singleton.mp h3
      hvc ▸ xbc.2
  left_inv f := by
    funext ⟨v, hv⟩
    rw [Finset.mem_sdiff] at hv
    by_cases hvb : v = b
    · subst hvb; simp
    · have hvc : v = c := by
        rcases Finset.mem_insert.mp hv.1 with rfl | h2
        · exact absurd (Finset.mem_singleton_self _) hv.2
        · rcases Finset.mem_insert.mp h2 with rfl | h3
          · exact absurd rfl hvb
          · exact Finset.mem_singleton.mp h3
      subst hvc; simp [hvb]
  right_inv := by
    rintro ⟨xb, xc⟩
    have hcb : c ≠ b := hbc.symm
    ext1 <;> simp [hcb]

/-- **Triple-complement, first two sites**: for pairwise-distinct
    `a, b, c : L.sites`, `regionIdx ({a, b, c} \ {a, b}) ≃ localIdx c`. Direct
    construction (no `regionIdxCongr` transport) so pointwise evaluation reduces
    by computation. -/
noncomputable def regionIdxComplPairFirstTwo {a b c : L.sites}
    (hac : a ≠ c) (hbc : b ≠ c) :
    L.regionIdx (({a, b, c} : Finset L.sites) \ ({a, b} : Finset _)) ≃ L.localIdx c where
  toFun f := f ⟨c, Finset.mem_sdiff.mpr ⟨
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)),
    by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
       exact ⟨hac.symm, hbc.symm⟩⟩⟩
  invFun xc := fun ⟨v, hv⟩ =>
    have hvc : v = c := by
      rw [Finset.mem_sdiff] at hv
      rcases Finset.mem_insert.mp hv.1 with rfl | h2
      · exact absurd (Finset.mem_insert_self _ _) hv.2
      · rcases Finset.mem_insert.mp h2 with rfl | h3
        · exact absurd
            (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)) hv.2
        · exact Finset.mem_singleton.mp h3
    hvc ▸ xc
  left_inv f := by
    funext ⟨v, hv⟩
    rw [Finset.mem_sdiff] at hv
    have hvc : v = c := by
      rcases Finset.mem_insert.mp hv.1 with rfl | h2
      · exact absurd (Finset.mem_insert_self _ _) hv.2
      · rcases Finset.mem_insert.mp h2 with rfl | h3
        · exact absurd
            (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)) hv.2
        · exact Finset.mem_singleton.mp h3
    subst hvc; rfl
  right_inv := by intro xc; rfl

/-- **Triple-complement, last two sites**: for pairwise-distinct
    `a, b, c : L.sites`, `regionIdx ({a, b, c} \ {b, c}) ≃ localIdx a`. Direct
    construction (no `regionIdxCongr` transport) so pointwise evaluation reduces
    by computation. -/
noncomputable def regionIdxComplPairLastTwo {a b c : L.sites}
    (hab : a ≠ b) (hac : a ≠ c) :
    L.regionIdx (({a, b, c} : Finset L.sites) \ ({b, c} : Finset _)) ≃ L.localIdx a where
  toFun f := f ⟨a, Finset.mem_sdiff.mpr ⟨
    Finset.mem_insert_self _ _,
    by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
       exact ⟨hab, hac⟩⟩⟩
  invFun xa := fun ⟨v, hv⟩ =>
    have hva : v = a := by
      rw [Finset.mem_sdiff] at hv
      rcases Finset.mem_insert.mp hv.1 with rfl | h2
      · rfl
      · rcases Finset.mem_insert.mp h2 with rfl | h3
        · exact absurd (Finset.mem_insert_self _ _) hv.2
        · have hvc : v = c := Finset.mem_singleton.mp h3
          subst hvc
          exact absurd
            (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)) hv.2
    hva ▸ xa
  left_inv f := by
    funext ⟨v, hv⟩
    rw [Finset.mem_sdiff] at hv
    have hva : v = a := by
      rcases Finset.mem_insert.mp hv.1 with rfl | h2
      · rfl
      · rcases Finset.mem_insert.mp h2 with rfl | h3
        · exact absurd (Finset.mem_insert_self _ _) hv.2
        · have hvc : v = c := Finset.mem_singleton.mp h3
          subst hvc
          exact absurd
            (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)) hv.2
    subst hva; rfl
  right_inv := by intro xa; rfl

/-- `{b} ⊆ {a, b, c}` for any sites `a, b, c`. Pure Finset membership; the
    arguments `a` and `c` are kept positional so call sites can pass them
    explicitly when convenient. -/
lemma singleton_b_subset_triple (a b c : L.sites) :
    ({b} : Finset L.sites) ⊆ ({a, b, c} : Finset L.sites) :=
  Finset.singleton_subset_iff.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))

end LocalNet
