module

public import QuantumSystem.State

/-!
# Local net of matrix algebras for finite lattice regions

This file defines the data of a **local net of matrix algebras** over finite
lattice regions.  It is the finite-dimensional, quantum-spin-system analogue of
the local-net part of the Haag–Kastler framework.  Continuous-spacetime AQFT
uses a different region geometry and is handled separately.

A lattice local net assigns to each finite region `Λ` an algebra `𝔄(Λ)` of
observables, with **isotony** (`Λ₁ ⊆ Λ₂ ⟹ 𝔄(Λ₁) ⊆ 𝔄(Λ₂)`) and **locality**
(disjoint regions commute).  Covariance is added in the group-action modules.

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
2. the **isotony embedding** `𝔄(Λ) ↪ 𝔄(Λ_total)` realised as `A ↦ A ⊗ I_{Λ_total \ Λ}`,
   bundled as a unital `*`-algebra homomorphism, together with its injectivity (under the
   standard non-degeneracy assumption on the complementary region) and functoriality along
   `Subset.refl` / `Subset.trans`;
3. the **locality predicate** `IsLocal` and the constructive proof `isLocal` showing that
   every `LocalNet` satisfies it: disjoint sub-regions of a common ambient region have
   commuting images under the isotony embedding.

## Main definitions

* `LocalNet` — data carrier: sites + per-site finite index types
* `LocalNet.regionIdx` — index type of a region (dependent product)
* `LocalNet.localAlgebra` — the matrix algebra at a region
* `LocalNet.densityMatrix` — density matrices at a region
* `LocalNet.combineIdx` — `regionIdx Λ × regionIdx (Λ_total \ Λ) ≃ regionIdx Λ_total`
* `LocalNet.includeAlgebra` — isotony embedding `𝔄(Λ) ↪ 𝔄(Λ_total)`
* `LocalNet.regionIdxCongr` — transport `regionIdx` along a Finset equality
* `LocalNet.IsLocal` / `LocalNet.isLocal` — locality predicate and its constructive proof

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

/-- **Functoriality (composition):** the isotony embedding respects composition of
inclusions.  This is the `*`-algebra version of the fact that tensoring with the
identity on `Λ₃ \ Λ₁` factors as tensoring with the identity on `Λ₂ \ Λ₁` followed
by tensoring with the identity on `Λ₃ \ Λ₂`. -/
theorem includeAlgebra_comp {Λ₁ Λ₂ Λ₃ : Finset L.sites}
    (h₁₂ : Λ₁ ⊆ Λ₂) (h₂₃ : Λ₂ ⊆ Λ₃) :
    L.includeAlgebra (h₁₂.trans h₂₃)
      = (L.includeAlgebra h₂₃).comp (L.includeAlgebra h₁₂) := by
  ext X s s'
  rw [StarAlgHom.coe_comp, Function.comp_apply,
    includeAlgebra_apply, includeAlgebra_apply, includeAlgebra_apply]
  -- Equivalence of the conditional guards.  The LHS condition says `s` and `s'`
  -- agree on every site of `Λ₃ \ Λ₁`; the RHS conjunction says they agree on
  -- `Λ₃ \ Λ₂` and on `Λ₂ \ Λ₁`, which together cover `Λ₃ \ Λ₁`.
  have hcond_iff :
      ((L.combineIdx (h₁₂.trans h₂₃)).symm s).2 =
          ((L.combineIdx (h₁₂.trans h₂₃)).symm s').2
        ↔ ((L.combineIdx h₂₃).symm s).2 = ((L.combineIdx h₂₃).symm s').2 ∧
          ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm s).1).2 =
            ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm s').1).2 := by
    refine ⟨fun h => ⟨?_, ?_⟩, ?_⟩
    · -- (→) outer condition: s|Λ₃\Λ₂ = s'|Λ₃\Λ₂.
      funext d
      have hd_props := Finset.mem_sdiff.mp d.property
      have hd : d.val ∈ Λ₃ \ Λ₁ :=
        Finset.mem_sdiff.mpr ⟨hd_props.1, fun hin => hd_props.2 (h₁₂ hin)⟩
      have key := congrFun h ⟨d.val, hd⟩
      simp only [combineIdx_symm_apply_snd] at key ⊢
      exact key
    · -- (→) inner condition: (s|Λ₂)|Λ₂\Λ₁ = (s'|Λ₂)|Λ₂\Λ₁.
      funext e
      have he_props := Finset.mem_sdiff.mp e.property
      have he : e.val ∈ Λ₃ \ Λ₁ :=
        Finset.mem_sdiff.mpr ⟨h₂₃ he_props.1, he_props.2⟩
      have key := congrFun h ⟨e.val, he⟩
      simp only [combineIdx_symm_apply_snd, combineIdx_symm_apply_fst] at key ⊢
      exact key
    · -- (←) given the outer + inner conditions, derive the LHS condition.
      rintro ⟨hQ, hR⟩
      funext c
      have hc_in_Λ₃ : c.val ∈ Λ₃ := (Finset.mem_sdiff.mp c.property).1
      have hc_notin_Λ₁ : c.val ∉ Λ₁ := (Finset.mem_sdiff.mp c.property).2
      by_cases hc_Λ₂ : c.val ∈ Λ₂
      · have he : c.val ∈ Λ₂ \ Λ₁ :=
          Finset.mem_sdiff.mpr ⟨hc_Λ₂, hc_notin_Λ₁⟩
        have key := congrFun hR ⟨c.val, he⟩
        simp only [combineIdx_symm_apply_snd, combineIdx_symm_apply_fst] at key ⊢
        exact key
      · have hd : c.val ∈ Λ₃ \ Λ₂ :=
          Finset.mem_sdiff.mpr ⟨hc_in_Λ₃, hc_Λ₂⟩
        have key := congrFun hQ ⟨c.val, hd⟩
        simp only [combineIdx_symm_apply_snd] at key ⊢
        exact key
  -- The X-arguments coincide by the same restriction-to-Λ₁ identity.
  have hX_arg :
      ∀ t : L.regionIdx Λ₃,
        ((L.combineIdx (h₁₂.trans h₂₃)).symm t).1 =
          ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm t).1).1 := by
    intro t
    funext a
    simp only [combineIdx_symm_apply_fst]
  -- Case analysis on the two RHS conditions.
  by_cases h_outer :
      ((L.combineIdx h₂₃).symm s).2 = ((L.combineIdx h₂₃).symm s').2
  · rw [if_pos h_outer]
    by_cases h_inner :
        ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm s).1).2 =
          ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm s').1).2
    · rw [if_pos h_inner, if_pos (hcond_iff.mpr ⟨h_outer, h_inner⟩),
        hX_arg s, hX_arg s']
    · rw [if_neg h_inner,
        if_neg (fun h => h_inner (hcond_iff.mp h).2)]
  · rw [if_neg h_outer,
      if_neg (fun h => h_outer (hcond_iff.mp h).1)]

/-! ### Transport along Finset equality

`regionIdxCongr` carries `regionIdx Λ` to `regionIdx Λ'` whenever `Λ = Λ'`,
giving a small reindexing utility consumed by the downstream covariance
lemmas. -/

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
