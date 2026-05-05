module

public import QuantumSystem.Channel

/-!
# Local Net of Matrix Algebras (finite-dim)

This file defines the data of a **local net of matrix algebras** on a finite lattice.
An AQFT system assigns to each spacetime / lattice region `Λ` an
algebra `𝔄(Λ)` of observables, with **isotony** (`Λ₁ ⊆ Λ₂ ⟹ 𝔄(Λ₁) ⊆ 𝔄(Λ₂)`), **locality**
(disjoint regions commute), and—in the spacetime version—**covariance**.

For finite-dimensional quantum spin systems, the construction specialises to:

- a finite set of **sites** `L`,
- a local index type `ℂ^{n_x}` at each site `x ∈ L`,
- regions `Λ ∈ 𝒫(L)` (`Finset L.sites`),
- local algebra `𝔄(Λ) = ⊗_{x ∈ Λ} M_{n_x}(ℂ)` realised concretely as
  `Matrix (Π s ∈ Λ, idx s) (Π s ∈ Λ, idx s) ℂ`.

This file provides:

1. the structure carrying the lattice + per-site Hilbert-space data, the derived region index
   types, and the index-combiner equivalence relating `regionIdx Λ_total` to the product
   `regionIdx Λ × regionIdx (Λ_total \ Λ)`;
2. the **restriction** (Schrödinger-picture partial trace): given regions `Λ ⊆ Λ_total`,
   the restriction of a state on `𝔄(Λ_total)` to `𝔄(Λ)`. In density-matrix language this is
   exactly the partial trace over the complementary region `Λ_total \ Λ`.
   The restriction is the Schrödinger-picture dual of the algebra
   inclusion `𝔄(Λ) ↪ 𝔄(Λ_total)`. There is no positional ("left/right") concept — the
   operation is parameterised by the region itself.

## Main definitions

* `LocalNet` — data carrier: sites + per-site finite index types
* `LocalNet.regionIdx` — index type of a region (dependent product)
* `LocalNet.localAlgebra` — the matrix algebra at a region
* `LocalNet.densityMatrix` — density matrices at a region
* `LocalNet.combineIdx` — `regionIdx Λ × regionIdx (Λ_total \ Λ) ≃ regionIdx Λ_total`
* `LocalNet.includeAlgebra` — isotony embedding `𝔄(Λ) ↪ 𝔄(Λ_total)`
* `LocalNet.regionIdxInsertEquiv` — recursive split: `regionIdx (insert s Λ) ≃ localIdx s × regionIdx Λ`
* `LocalNet.regionIdxPairEquiv` / `regionIdxTripleEquiv` / `regionIdxTripleEquiv'` —
  factorisation of `n`-element regions into per-site product types
* `LocalNet.regionIdxComplLeftSite` / `regionIdxComplRightSite` —
  `regionIdx ({a, b} \ {a}) ≃ localIdx b` and its right-site dual

The generic primitives above subsume any partite count; the bipartite / tripartite
factorisation specialisations are exposed below as `regionIdxPairEquiv`,
`regionIdxTripleEquiv`, and `regionIdxTripleEquiv'`.

The partial-trace / restriction operations (`Matrix.restrict`, `Matrix.restrictKraus`,
`Matrix.QuantumChannel.restrict`, `DensityMatrix.restrict`, and the paper notation
`ρ ↾ Λ`) are defined in `QuantumSystem/Analysis/Matrix/PartialTrace.lean`.

## References

* Verch 2025 (`https://arxiv.org/abs/2507.00900`)
* Naaijkens 2012 (`https://repository.ubn.ru.nl/handle/2066/92737`)
-/

@[expose] public section

/-- Data for a **local net of matrix algebras** on a (possibly infinite) lattice of sites.
    Each site `s : sites` carries a finite index type `localIdx s` whose cardinality is the
    local Hilbert-space dimension. The local algebra at a finite region `Λ ⊆ sites` is then
    the matrix algebra on the dependent product `Π s ∈ Λ, localIdx s`.

    The site set itself is not required to be `Fintype`: lemmas that genuinely need
    `Finset.univ : Finset sites` take `[Fintype sites]` as an explicit instance argument. -/
structure LocalNet where
  /-- Lattice of sites — `DecidableEq` only, possibly infinite. -/
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

variable {L} in
/-- Pointwise evaluation of the `Λ`-component of `(combineIdx h).symm`. -/
@[simp] lemma combineIdx_symm_apply_fst
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (f : L.regionIdx Λ_total) (a : ↥Λ) :
    ((L.combineIdx h).symm f).1 a = f ⟨a.val, h a.property⟩ := rfl

variable {L} in
/-- Pointwise evaluation of the `Λ_total \ Λ`-component of `(combineIdx h).symm`. -/
@[simp] lemma combineIdx_symm_apply_snd
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (f : L.regionIdx Λ_total) (a : ↥(Λ_total \ Λ)) :
    ((L.combineIdx h).symm f).2 a = f ⟨a.val, (Finset.mem_sdiff.mp a.property).1⟩ := rfl

/-- Cardinality factorisation for region indices induced by `combineIdx`. -/
theorem card_regionIdx_total {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    Fintype.card (L.regionIdx Λ_total) =
      Fintype.card (L.regionIdx Λ) * Fintype.card (L.regionIdx (Λ_total \ Λ)) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (L.combineIdx h).symm

/-! ### Isotony embedding (algebra inclusion)

The isotony embedding `𝔄(Λ) ↪ 𝔄(Λ_total)` is realised concretely as the tensor with
identity on the complement, `A ↦ A ⊗ I_{Λ_total \ Λ}`. We bundle it as a unital
`*`-algebra homomorphism (`StarAlgHom`) so that the AQFT axioms (Naaijkens 2012 §1.3
line 211, Verch 2025 §1.2 axiom (i), Bratteli–Robinson Vol.2 §6.2) — preservation of
unit, product, and adjoint — are guaranteed at the type level.

Pipeline: entry-wise underlying function `includeAlgebraFun` → algebraic identities
`includeAlgebraFun_{one,mul,star,...}` → bundled `includeAlgebra : _ →⋆ₐ[ℂ] _`. -/

/-- Entry-wise underlying function for `includeAlgebra`, defined separately so the
    structural simp lemmas (`includeAlgebraFun_apply`, `..._apply_combineIdx`) reduce
    by `rfl`/`simp` without going through the `StarAlgHom` coercion. -/
noncomputable def includeAlgebraFun {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) : L.localAlgebra Λ_total :=
  Matrix.of fun s s' =>
    if ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2 then
      X ((L.combineIdx h).symm s).1 ((L.combineIdx h).symm s').1
    else 0

@[simp] lemma includeAlgebraFun_apply {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) (X : L.localAlgebra Λ) (s s' : L.regionIdx Λ_total) :
    L.includeAlgebraFun h X s s' =
      if ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2 then
        X ((L.combineIdx h).symm s).1 ((L.combineIdx h).symm s').1
      else 0 := rfl

/-- Entry-wise behaviour of `includeAlgebraFun` at combined indices: the off-diagonal
    components in the complementary region vanish, leaving `X a a'` on the diagonal. -/
@[simp] lemma includeAlgebraFun_apply_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) (X : L.localAlgebra Λ)
    (a a' : L.regionIdx Λ) (b b' : L.regionIdx (Λ_total \ Λ)) :
    L.includeAlgebraFun h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b')) =
      if b = b' then X a a' else 0 := by
  simp [includeAlgebraFun, Equiv.symm_apply_apply]

lemma includeAlgebraFun_zero {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.includeAlgebraFun h 0 = 0 := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.zero_apply]
  split_ifs <;> rfl

lemma includeAlgebraFun_add {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X Y : L.localAlgebra Λ) :
    L.includeAlgebraFun h (X + Y) =
      L.includeAlgebraFun h X + L.includeAlgebraFun h Y := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.add_apply]
  split_ifs with hbb
  · rfl
  · rw [add_zero]

lemma includeAlgebraFun_smul {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (c : ℂ) (X : L.localAlgebra Λ) :
    L.includeAlgebraFun h (c • X) = c • L.includeAlgebraFun h X := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with hbb
  · rfl
  · rw [mul_zero]

lemma includeAlgebraFun_one {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.includeAlgebraFun h 1 = 1 := by
  ext s s'
  by_cases hss : s = s'
  · subst hss
    rw [includeAlgebraFun_apply, if_pos rfl, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [includeAlgebraFun_apply, Matrix.one_apply_ne hss]
    -- Translate `s ≠ s'` to a disjunction on the two coordinates of `(combineIdx h).symm`.
    have hne : (L.combineIdx h).symm s ≠ (L.combineIdx h).symm s' := fun heq =>
      hss ((L.combineIdx h).symm.injective heq)
    rw [Ne, Prod.ext_iff, not_and_or] at hne
    by_cases h2 : ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2
    · rw [if_pos h2]
      rcases hne with h1 | h2'
      · rw [Matrix.one_apply_ne h1]
      · exact absurd h2 h2'
    · rw [if_neg h2]

lemma includeAlgebraFun_star {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) :
    L.includeAlgebraFun h (star X) = star (L.includeAlgebraFun h X) := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.star_apply]
  by_cases h2 : ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2
  · rw [if_pos h2, if_pos h2.symm]
  · rw [if_neg h2, if_neg (fun hh => h2 hh.symm), star_zero]

lemma includeAlgebraFun_mul {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X Y : L.localAlgebra Λ) :
    L.includeAlgebraFun h (X * Y) =
      L.includeAlgebraFun h X * L.includeAlgebraFun h Y := by
  ext s s'
  -- Express both rows/columns through `combineIdx` so the `_apply_combineIdx` simp lemma fires.
  set sa := ((L.combineIdx h).symm s).1 with hsa
  set sb := ((L.combineIdx h).symm s).2 with hsb
  set s'a := ((L.combineIdx h).symm s').1 with hs'a
  set s'b := ((L.combineIdx h).symm s').2 with hs'b
  have hs : s = L.combineIdx h (sa, sb) := by
    simp [sa, sb, Equiv.apply_symm_apply]
  have hs' : s' = L.combineIdx h (s'a, s'b) := by
    simp [s'a, s'b, Equiv.apply_symm_apply]
  rw [hs, hs', includeAlgebraFun_apply_combineIdx, Matrix.mul_apply]
  -- Reindex the RHS sum (over `regionIdx Λ_total`) via `combineIdx`.
  rw [show ((L.includeAlgebraFun h X * L.includeAlgebraFun h Y)
              (L.combineIdx h (sa, sb)) (L.combineIdx h (s'a, s'b))) =
      ∑ p : L.regionIdx Λ × L.regionIdx (Λ_total \ Λ),
        L.includeAlgebraFun h X (L.combineIdx h (sa, sb)) (L.combineIdx h p) *
          L.includeAlgebraFun h Y (L.combineIdx h p) (L.combineIdx h (s'a, s'b)) from by
    rw [Matrix.mul_apply]
    exact ((L.combineIdx h).sum_comp _).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [includeAlgebraFun_apply_combineIdx]
  -- Goal:
  -- (if sb = s'b then ∑ a'', X sa a'' * Y a'' s'a else 0)
  --   = ∑ a'', ∑ b'', (if sb = b'' then X sa a'' else 0) * (if b'' = s'b then Y a'' s'a else 0)
  by_cases hbb : sb = s'b
  · rw [if_pos hbb]
    refine Finset.sum_congr rfl fun a'' _ => ?_
    rw [Finset.sum_eq_single sb
      (fun b'' _ hb'' => by rw [if_neg fun heq => hb'' heq.symm, zero_mul])
      (fun h_not_mem => absurd (Finset.mem_univ sb) h_not_mem)]
    rw [if_pos rfl, ← hbb, if_pos rfl]
  · rw [if_neg hbb]
    refine (Finset.sum_eq_zero fun a'' _ => ?_).symm
    refine Finset.sum_eq_zero fun b'' _ => ?_
    by_cases hb_sb : sb = b''
    · subst hb_sb
      rw [if_neg hbb, mul_zero]
    · rw [if_neg hb_sb, zero_mul]

lemma includeAlgebraFun_algebraMap {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) (c : ℂ) :
    L.includeAlgebraFun h ((algebraMap ℂ (L.localAlgebra Λ)) c) =
      (algebraMap ℂ (L.localAlgebra Λ_total)) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      includeAlgebraFun_smul, includeAlgebraFun_one]

/-- **Isotony embedding** `𝔄(Λ) ↪ 𝔄(Λ_total)`: tensor a local matrix with the identity on
    the complementary region. Realises the inclusion `A ↦ A ⊗ I_{Λ_total \ Λ}` from
    Naaijkens 2012 §1.3 line 211, Verch 2025 §1.2 axiom (i), Bratteli–Robinson Vol.2 §6.2.
    Bundled as a unital `*`-algebra homomorphism so that `map_one`, `map_mul`, `map_star`
    are available via the `StarAlgHom` API. Entry-wise:
    `(includeAlgebra h X) s s' = X (combineIdx⁻¹ s).1 (combineIdx⁻¹ s').1` when the
    complementary indices match, else `0`. -/
noncomputable def includeAlgebra {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.localAlgebra Λ →⋆ₐ[ℂ] L.localAlgebra Λ_total where
  toFun := L.includeAlgebraFun h
  map_zero' := L.includeAlgebraFun_zero h
  map_add' := L.includeAlgebraFun_add h
  map_one' := L.includeAlgebraFun_one h
  map_mul' := L.includeAlgebraFun_mul h
  commutes' := L.includeAlgebraFun_algebraMap h
  map_star' := L.includeAlgebraFun_star h

/-- Entry-wise unfolding of `includeAlgebra h X`: at indices `(s, s')` of the larger
    region, the embedded matrix equals `X` on the diagonal (in the complementary index)
    and zero off-diagonal. -/
@[simp] lemma includeAlgebra_apply {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) (s s' : L.regionIdx Λ_total) :
    L.includeAlgebra h X s s' =
      if ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2 then
        X ((L.combineIdx h).symm s).1 ((L.combineIdx h).symm s').1
      else 0 := rfl

/-- **Injectivity of the isotony embedding** (the `↪` of `𝔄(Λ) ↪ 𝔄(Λ_total)`): under
    the standing AQFT non-degeneracy assumption that the complementary region has a
    non-empty index type, `includeAlgebra h` is injective as a map of `*`-algebras. -/
theorem includeAlgebra_injective {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    [hne : Nonempty (L.regionIdx (Λ_total \ Λ))] :
    Function.Injective (L.includeAlgebra h) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  ext a a'
  obtain ⟨b⟩ := hne
  have heq : L.includeAlgebra h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) =
      0 := by rw [hX]; rfl
  have key : L.includeAlgebra h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) =
      X a a' := by
    change L.includeAlgebraFun h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) = X a a'
    rw [includeAlgebraFun_apply_combineIdx, if_pos rfl]
  rw [key] at heq
  simpa using heq

/-! ### Region equivalences

Generic equivalences over arbitrary `Fintype` site sets — used both directly (for any
finite site set) and as building blocks for the bipartite (`regionIdxPairEquiv`) and
tripartite (`regionIdxTripleEquiv`, `regionIdxTripleEquiv'`) factorisations below. -/

variable (L : LocalNet)

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

Building blocks for any finite site set: `regionIdx ∅ ≃ PUnit`, an `insert`-based
recursive split, and the universal product form `regionIdx Finset.univ ≃ Π s, localIdx s`.
Two- and three-element factor equivs are derived from the recursive split — adding more
partite counts (4, 5, ...) is now a one-liner with no new boilerplate. -/

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
    Collapses the `Finset.univ`-subtype back to the underlying type.
    Requires `[Fintype L.sites]` for `Finset.univ` to be available. -/
def regionIdxUnivEquiv [Fintype L.sites] :
    L.regionIdx (Finset.univ : Finset L.sites) ≃
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

/-! ### Locality (Einstein causality)

For finite-dimensional `LocalNet`, the isotony embedding is **automatically local**:
the images of disjoint regions commute. This realises Verch 2025 §1.2 axiom (ii) /
Naaijkens 2012 §1.3 line 213 in the finite-lattice slice. The locality predicate is
exposed both as a `Prop` (`IsLocal`) and as a `theorem` (`isLocal`) so that future
abstract Haag–Kastler structures can consume it as an axiom field. -/

/-- **Locality (Haag–Kastler axiom (ii)).** Two disjoint subregions of a common
    enclosing region give commuting images under the isotony embedding. -/
def IsLocal (L : LocalNet) : Prop :=
  ∀ {Λ₁ Λ₂ Λ_total : Finset L.sites}
    (h₁ : Λ₁ ⊆ Λ_total) (h₂ : Λ₂ ⊆ Λ_total),
    Disjoint Λ₁ Λ₂ →
    ∀ (a : L.localAlgebra Λ₁) (b : L.localAlgebra Λ₂),
      Commute (L.includeAlgebra h₁ a) (L.includeAlgebra h₂ b)

/-- Closed form for `includeAlgebra h X` when both arguments are expressed via
    the `combineIdx h` decomposition. Lifts `includeAlgebraFun_apply_combineIdx`
    through the `StarAlgHom` coercion. -/
lemma includeAlgebra_apply_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) (X : L.localAlgebra Λ)
    (a a' : L.regionIdx Λ) (b b' : L.regionIdx (Λ_total \ Λ)) :
    L.includeAlgebra h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b')) =
      if b = b' then X a a' else 0 :=
  L.includeAlgebraFun_apply_combineIdx h X a a' b b'

/-- The Λ₂-restriction of `combineIdx h₁ (α, γ)` depends only on `γ` (not `α`),
    via the inclusion `Λ₂ ⊆ Λ_total \ Λ₁` from disjointness. Concretely,
    for `x : ↥Λ₂`, the value is `γ` evaluated at `x` (with appropriate
    inclusion proof). -/
private lemma combineIdx_restrict_compl
    {Λ₁ Λ₂ Λ_total : Finset L.sites}
    (h₁ : Λ₁ ⊆ Λ_total) (h₂ : Λ₂ ⊆ Λ_total)
    (hΛ₂_compl : Λ₂ ⊆ Λ_total \ Λ₁)
    (α : L.regionIdx Λ₁) (γ : L.regionIdx (Λ_total \ Λ₁))
    (x : ↥Λ₂) :
    (L.combineIdx h₁ (α, γ)) ⟨x.val, h₂ x.property⟩ =
      γ ⟨x.val, hΛ₂_compl x.property⟩ := by
  have hxn : x.val ∉ Λ₁ := (Finset.mem_sdiff.mp (hΛ₂_compl x.property)).2
  rw [combineIdx_apply_not_mem h₁ α γ ⟨x.val, h₂ x.property⟩ hxn]

/-- **Cross-decomposition**: when `Λ₁` and `Λ₂` are disjoint inside `Λ_total`,
    the entry of `includeAlgebra h₂ b` at points expressed via `combineIdx h₁`
    factors as: `α`-equality on the first factor times the `includeAlgebra` of
    `b` taken inside the smaller ambient region `Λ_total \ Λ₁` (where `Λ₂` lives
    as a subset by disjointness). Realises the kronecker decomposition
    `includeAlgebra h₂ b = 1_{Λ₁} ⊗ includeAlgebra (Λ₂ ⊆ Λ_total\Λ₁) b` in the
    `combineIdx h₁` picture. -/
private lemma includeAlgebra_h₂_combineIdx_h₁
    {Λ₁ Λ₂ Λ_total : Finset L.sites}
    (h₁ : Λ₁ ⊆ Λ_total) (h₂ : Λ₂ ⊆ Λ_total)
    (hΛ₂_compl : Λ₂ ⊆ Λ_total \ Λ₁)
    (b : L.localAlgebra Λ₂)
    (α α' : L.regionIdx Λ₁) (γ γ' : L.regionIdx (Λ_total \ Λ₁)) :
    L.includeAlgebra h₂ b (L.combineIdx h₁ (α, γ)) (L.combineIdx h₁ (α', γ')) =
      if α = α' then L.includeAlgebra hΛ₂_compl b γ γ' else 0 := by
  rw [includeAlgebra_apply, includeAlgebra_apply]
  -- Auxiliary: Λ₁ ⊆ Λ_total \ Λ₂ from disjoint
  have hΛ₁_compl : Λ₁ ⊆ Λ_total \ Λ₂ := fun y hy =>
    Finset.mem_sdiff.mpr ⟨h₁ hy, fun hyΛ₂ => by
      have : y ∈ Λ₁ := hy
      have : y ∉ Λ₁ := (Finset.mem_sdiff.mp (hΛ₂_compl hyΛ₂)).2
      exact absurd hy this⟩
  -- Case on α = α'
  by_cases hα : α = α'
  · subst hα
    rw [if_pos rfl]
    -- Both LHS and RHS are conditionals on `γ-rest` agreement.
    -- Show conditions are equivalent.
    by_cases hγ_rest : ((L.combineIdx hΛ₂_compl).symm γ).2 =
                        ((L.combineIdx hΛ₂_compl).symm γ').2
    · rw [if_pos hγ_rest]
      -- LHS condition: agree on Λ_total\Λ₂. Reduces to "γ-rest" since α-part is identical.
      have h_h₂_cond : ((L.combineIdx h₂).symm (L.combineIdx h₁ (α, γ))).2 =
                        ((L.combineIdx h₂).symm (L.combineIdx h₁ (α, γ'))).2 := by
        funext y
        change (L.combineIdx h₁ (α, γ)) ⟨y.val, (Finset.mem_sdiff.mp y.property).1⟩
            = (L.combineIdx h₁ (α, γ')) ⟨y.val, (Finset.mem_sdiff.mp y.property).1⟩
        by_cases hyΛ₁ : y.val ∈ Λ₁
        · rw [combineIdx_apply_mem h₁ α γ _ hyΛ₁,
              combineIdx_apply_mem h₁ α γ' _ hyΛ₁]
        · rw [combineIdx_apply_not_mem h₁ α γ _ hyΛ₁,
              combineIdx_apply_not_mem h₁ α γ' _ hyΛ₁]
          have hy_in_rest : y.val ∈ (Λ_total \ Λ₁) \ Λ₂ :=
            Finset.mem_sdiff.mpr
              ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp y.property).1, hyΛ₁⟩,
               (Finset.mem_sdiff.mp y.property).2⟩
          exact congrArg (fun f => f ⟨y.val, hy_in_rest⟩) hγ_rest
      rw [if_pos h_h₂_cond]
      -- Match values: b on Λ₂-restrictions
      congr 1
      · funext x
        exact L.combineIdx_restrict_compl h₁ h₂ hΛ₂_compl α γ x
      · funext x
        exact L.combineIdx_restrict_compl h₁ h₂ hΛ₂_compl α γ' x
    · rw [if_neg hγ_rest]
      -- γ-rest fails ⟹ LHS condition fails too.
      rw [if_neg]
      intro h_eq
      apply hγ_rest
      funext z
      -- z : ↥((Λ_total\Λ₁)\Λ₂)
      -- Goal: ((combineIdx hΛ₂_compl).symm γ).2 z = ((combineIdx hΛ₂_compl).symm γ').2 z
      -- LHS = γ ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩
      -- RHS = γ' ⟨z.val, ...⟩
      change γ ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩
          = γ' ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩
      have hzΛ_total : z.val ∈ Λ_total := by
        have : z.val ∈ Λ_total \ Λ₁ := (Finset.mem_sdiff.mp z.property).1
        exact (Finset.mem_sdiff.mp this).1
      have hzn_Λ₂ : z.val ∉ Λ₂ := (Finset.mem_sdiff.mp z.property).2
      have hzn_Λ₁ : z.val ∉ Λ₁ :=
        (Finset.mem_sdiff.mp ((Finset.mem_sdiff.mp z.property).1)).2
      have hz_in_compl_Λ₂ : z.val ∈ Λ_total \ Λ₂ :=
        Finset.mem_sdiff.mpr ⟨hzΛ_total, hzn_Λ₂⟩
      have := congrArg (fun f => f ⟨z.val, hz_in_compl_Λ₂⟩) h_eq
      simp only at this
      -- Both sides equal (combineIdx h₁ (α, γ/γ')) at the corresponding point.
      have lhs_val : (L.combineIdx h₁ (α, γ)) ⟨z.val, hzΛ_total⟩
          = γ ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩ := by
        rw [combineIdx_apply_not_mem h₁ α γ ⟨z.val, hzΛ_total⟩ hzn_Λ₁]
      have rhs_val : (L.combineIdx h₁ (α, γ')) ⟨z.val, hzΛ_total⟩
          = γ' ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩ := by
        rw [combineIdx_apply_not_mem h₁ α γ' ⟨z.val, hzΛ_total⟩ hzn_Λ₁]
      change (L.combineIdx h₁ (α, γ)) _ = (L.combineIdx h₁ (α, γ')) _ at this
      rw [lhs_val, rhs_val] at this
      exact this
  · rw [if_neg hα]
    -- α ≠ α' ⟹ LHS condition fails.
    rw [if_neg]
    intro h_eq
    apply hα
    funext x
    have hx_compl_Λ₂ : x.val ∈ Λ_total \ Λ₂ := hΛ₁_compl x.property
    have hcong := congrArg (fun f => f ⟨x.val, hx_compl_Λ₂⟩) h_eq
    have lhs_val : (L.combineIdx h₁ (α, γ)) ⟨x.val, h₁ x.property⟩
        = α ⟨x.val, x.property⟩ := by
      rw [combineIdx_apply_mem h₁ α γ ⟨x.val, h₁ x.property⟩ x.property]
    have rhs_val : (L.combineIdx h₁ (α', γ')) ⟨x.val, h₁ x.property⟩
        = α' ⟨x.val, x.property⟩ := by
      rw [combineIdx_apply_mem h₁ α' γ' ⟨x.val, h₁ x.property⟩ x.property]
    change (L.combineIdx h₁ (α, γ)) _ = (L.combineIdx h₁ (α', γ')) _ at hcong
    rw [lhs_val, rhs_val] at hcong
    exact hcong

/-- **Locality holds for any `LocalNet`**. This is the finite-dimensional
    realisation of the Haag–Kastler locality axiom: disjoint subregions give
    commuting isotony images. The proof reindexes the sum over the larger region
    via `combineIdx h₁`, factors the products into `α`-collapse on `X` and
    `α`-collapse on `Y` via `includeAlgebra_h₂_combineIdx_h₁`, and concludes by
    multiplicative commutativity in `ℂ`. -/
theorem isLocal (L : LocalNet) : L.IsLocal := by
  intro Λ₁ Λ₂ Λ_total h₁ h₂ hd a b
  have hΛ₂_compl : Λ₂ ⊆ Λ_total \ Λ₁ := fun x hx =>
    Finset.mem_sdiff.mpr ⟨h₂ hx, fun hxΛ₁ => Finset.disjoint_left.mp hd hxΛ₁ hx⟩
  change (L.includeAlgebra h₁ a) * (L.includeAlgebra h₂ b)
      = (L.includeAlgebra h₂ b) * (L.includeAlgebra h₁ a)
  ext s s'
  obtain ⟨sα, sγ, hs⟩ : ∃ α γ, L.combineIdx h₁ (α, γ) = s :=
    ⟨_, _, (L.combineIdx h₁).apply_symm_apply s⟩
  obtain ⟨s'α, s'γ, hs'⟩ : ∃ α γ, L.combineIdx h₁ (α, γ) = s' :=
    ⟨_, _, (L.combineIdx h₁).apply_symm_apply s'⟩
  subst hs
  subst hs'
  rw [Matrix.mul_apply, Matrix.mul_apply,
      show (∑ t, (L.includeAlgebra h₁ a) (L.combineIdx h₁ (sα, sγ)) t
                * (L.includeAlgebra h₂ b) t (L.combineIdx h₁ (s'α, s'γ)) : ℂ)
        = ∑ p : L.regionIdx Λ₁ × L.regionIdx (Λ_total \ Λ₁),
            (L.includeAlgebra h₁ a) (L.combineIdx h₁ (sα, sγ)) (L.combineIdx h₁ p)
            * (L.includeAlgebra h₂ b) (L.combineIdx h₁ p) (L.combineIdx h₁ (s'α, s'γ))
      from ((L.combineIdx h₁).sum_comp _).symm,
      show (∑ t, (L.includeAlgebra h₂ b) (L.combineIdx h₁ (sα, sγ)) t
                * (L.includeAlgebra h₁ a) t (L.combineIdx h₁ (s'α, s'γ)) : ℂ)
        = ∑ p : L.regionIdx Λ₁ × L.regionIdx (Λ_total \ Λ₁),
            (L.includeAlgebra h₂ b) (L.combineIdx h₁ (sα, sγ)) (L.combineIdx h₁ p)
            * (L.includeAlgebra h₁ a) (L.combineIdx h₁ p) (L.combineIdx h₁ (s'α, s'γ))
      from ((L.combineIdx h₁).sum_comp _).symm,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
  -- Now goals have ∑ α, ∑ γ, ... with explicit (α, γ) in combineIdx applications.
  -- Apply Y cross-decomposition; X uses includeAlgebraFun_apply_combineIdx
  -- (since `includeAlgebra h₁ a = includeAlgebraFun h₁ a` definitionally).
  simp_rw [L.includeAlgebra_h₂_combineIdx_h₁ h₁ h₂ hΛ₂_compl b,
           L.includeAlgebra_apply_combineIdx h₁ a]
  -- Both sides: outer sum over α, inner over γ. Inner γ-sum collapses via X-condition;
  -- outer α-sum collapses via Y-condition.
  -- LHS: ∑ α, ∑ γ, (if sγ = γ then a sα α else 0) * (if α = s'α then M_b sγ s'γ else 0)
  --   inner sum collapses to γ = sγ:
  --     = ∑ α, a sα α * (if α = s'α then M_b sγ s'γ else 0)
  --   outer sum collapses to α = s'α:
  --     = a sα s'α * M_b sγ s'γ
  -- RHS: ∑ α, ∑ γ, (if α = sα then M_b sγ s'γ else 0) * (if γ = s'γ then a α s'α else 0)
  --   inner sum collapses to γ = s'γ:
  --     = ∑ α, (if α = sα then M_b sγ s'γ else 0) * a α s'α
  --   outer sum collapses to α = sα:
  --     = M_b sγ s'γ * a sα s'α
  -- Match via mul_comm.
  have lhs_eval :
      ∀ (α : L.regionIdx Λ₁),
        (∑ γ : L.regionIdx (Λ_total \ Λ₁),
            (if sγ = γ then a sα α else 0)
            * (if α = s'α then L.includeAlgebra hΛ₂_compl b γ s'γ else 0))
        = a sα α * (if α = s'α then L.includeAlgebra hΛ₂_compl b sγ s'γ else 0) := by
    intro α
    rw [Finset.sum_eq_single sγ]
    · rw [if_pos rfl]
    · intros γ _ hγ
      rw [if_neg fun h => hγ h.symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ sγ) h
  have rhs_eval :
      ∀ (α : L.regionIdx Λ₁),
        (∑ γ : L.regionIdx (Λ_total \ Λ₁),
            (if sα = α then L.includeAlgebra hΛ₂_compl b sγ γ else 0)
            * (if γ = s'γ then a α s'α else 0))
        = (if sα = α then L.includeAlgebra hΛ₂_compl b sγ s'γ else 0) * a α s'α := by
    intro α
    rw [Finset.sum_eq_single s'γ]
    · rw [if_pos rfl]
    · intros γ _ hγ
      rw [if_neg hγ, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ s'γ) h
  simp_rw [lhs_eval, rhs_eval]
  -- LHS: ∑ α, a sα α * (if α = s'α then ... else 0). Collapse on α = s'α.
  rw [Finset.sum_eq_single s'α (fun α _ hα => by rw [if_neg hα, mul_zero])
        (fun h => absurd (Finset.mem_univ s'α) h),
      if_pos rfl]
  -- RHS: ∑ α, (if sα = α then ... else 0) * a α s'α. Collapse on α = sα.
  rw [Finset.sum_eq_single sα
        (fun α _ hα => by rw [if_neg fun h => hα h.symm, zero_mul])
        (fun h => absurd (Finset.mem_univ sα) h),
      if_pos rfl]
  -- Match via ℂ-commutativity.
  ring

end LocalNet
