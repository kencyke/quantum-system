module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import QuantumSystem.Algebra.QuasiLocalAlgebra.InfiniteTensor.RegionDirectedOmega

/-!
# Paper notation `⨂[Λ]` for finite-region tensor products

Paper-style notation for the basis-indexed tensor product over a finite
region `Λ : Finset L` of a unit-vector family at each site:

`⨂[Λ] ξ : globalHilbertOmega L Ω hΩ`

where `ξ : (s : Λ) → siteHilbert s.1` is a tuple of vectors at the sites of
`Λ`. The tensor first lives in the finite-region Hilbert space
`regionHilbert Λ` as `mkRegionTensor Λ ξ`, then gets pushed to the algebraic
colimit via `tensorPreHilbertΩ.of` and finally completed into
`globalHilbertOmega`.

The defining inner-product identity matches the standard formula
`⟪⨂[Λ] ξ, ⨂[Λ] η⟫_ℂ = ∏ s : Λ, ⟪ξ s, η s⟫_ℂ`
of Bratteli–Robinson II §2.7.2.

## Main definitions

* `LocalNetLike.mkRegionTensor Λ ξ` — the basis-indexed region tensor in
  `regionHilbert Λ`.
* `LocalNetLike.tprodFinite Ω hΩ Λ ξ` — push-forward into
  `globalHilbertOmega L Ω hΩ`.
* `scoped notation "⨂[" Λ "]" ξ` — paper notation, scoped to `LocalNetLike`.

## Main results

* `LocalNetLike.mkRegionTensor_inner` — the basis-indexed tensor inner
  product factors as the product of per-site inner products.
* `LocalNetLike.tprodFinite_inner` — the same identity for the lifted
  tensor inside `globalHilbertOmega`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2 (incomplete infinite tensor product).
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

/-! ### The basis-indexed region tensor `mkRegionTensor` -/

/-- The basis-indexed tensor `⊗_{s ∈ Λ} ξ s` realised inside the
finite-region Hilbert space `regionHilbert Λ`.  Its component at the basis
index `f : regionIdx Λ` is `∏ s : Λ, (ξ s) (f s)`. -/
noncomputable def mkRegionTensor (Λ : Finset L)
    (ξ : (s : Λ) → siteHilbert (L := L) s.1) :
    regionHilbert (L := L) Λ :=
  (WithLp.equiv 2 (regionIdx (L := L) Λ → ℂ)).symm
    fun f : regionIdx Λ => ∏ s : Λ, ξ s (f s)

@[simp]
theorem mkRegionTensor_ofLp_apply (Λ : Finset L)
    (ξ : (s : Λ) → siteHilbert (L := L) s.1) (f : regionIdx (L := L) Λ) :
    (mkRegionTensor Λ ξ).ofLp f = ∏ s : Λ, (ξ s).ofLp (f s) := rfl

/-- The inner product of two basis-indexed region tensors factors as the
product of per-site inner products. -/
theorem mkRegionTensor_inner (Λ : Finset L)
    (ξ η : (s : Λ) → siteHilbert (L := L) s.1) :
    ⟪mkRegionTensor Λ ξ, mkRegionTensor Λ η⟫_ℂ
      = ∏ s : Λ, ⟪ξ s, η s⟫_ℂ := by
  -- Expand both sides into basis-component sums.
  rw [PiLp.inner_apply]
  -- Per-site inner product on `siteHilbert s.1` is also a finite ℓ² sum.
  conv_rhs =>
    enter [2, s]
    rw [PiLp.inner_apply]
  -- Reduce inner products on ℂ to `star a * b`.
  simp_rw [RCLike.inner_apply (𝕜 := ℂ)]
  -- The LHS's per-`f` term is
  --   star (∏_s (ξ s) (f s)) * ∏_s (η s) (f s)
  --   = (∏_s star ((ξ s) (f s))) * (∏_s (η s) (f s))
  --   = ∏_s (star ((ξ s) (f s)) * (η s) (f s)).
  conv_lhs =>
    enter [2, f]
    rw [show (mkRegionTensor Λ ξ) f = ∏ s : Λ, ξ s (f s) from rfl,
        show (mkRegionTensor Λ η) f = ∏ s : Λ, η s (f s) from rfl,
        map_prod, ← Finset.prod_mul_distrib]
  -- Apply distributivity of `∏` over `∑` in reverse.
  -- LHS: ∑_{f ∈ univ} ∏_s g s (f s);  RHS: ∏_s ∑_i g s i.
  exact ((Finset.prod_univ_sum
      (fun _ : Λ => (Finset.univ : Finset (LocalNetLike.localIdx (L := L) _)))
      (fun s i => (η s).ofLp i * (starRingEnd ℂ) ((ξ s).ofLp i))).symm).trans rfl

/-! ### The lifted tensor `tprodFinite` -/

variable (Ω : (s : L) → siteHilbert (L := L) s) (hΩ : ∀ s, ‖Ω s‖ = 1)

/-- The Bratteli–Robinson §2.7.2 finite-region tensor
`⨂_{s ∈ Λ} ξ s` realised inside the incomplete-infinite-tensor-product
reference sector `globalHilbertOmega L Ω hΩ`.

Concretely: build the basis-indexed region tensor in `regionHilbert Λ`,
push it into the algebraic colimit `tensorPreHilbertΩ` via the canonical
`of`, and embed into the Cauchy completion. -/
noncomputable def tprodFinite (Λ : Finset L)
    (ξ : (s : Λ) → siteHilbert (L := L) s.1) :
    globalHilbertOmega L Ω hΩ :=
  (tensorPreHilbertΩ.of Ω hΩ Λ (mkRegionTensor Λ ξ) :
    UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ))

/-- Paper notation `⨂[Λ] ξ` for the finite-region tensor `tprodFinite Λ ξ`,
scoped to the `LocalNetLike` namespace.  The reference family `Ω` and its
unit-norm hypothesis `hΩ` are inferred from the surrounding `globalHilbertOmega`
target. -/
scoped notation:max "⨂[" Λ "]" ξ => tprodFinite _ _ Λ ξ

/-! ### Inner-product formula for the lifted tensor -/

/-- The lifted finite-region tensor inner product factors as the product of
per-site inner products, matching the Bratteli–Robinson formula. -/
theorem tprodFinite_inner (Λ : Finset L)
    (ξ η : (s : Λ) → siteHilbert (L := L) s.1) :
    ⟪tprodFinite Ω hΩ Λ ξ, tprodFinite Ω hΩ Λ η⟫_ℂ
      = ∏ s : Λ, ⟪ξ s, η s⟫_ℂ := by
  unfold tprodFinite
  rw [UniformSpace.Completion.inner_coe, tensorPreHilbertΩ.inner_of_of]
  -- `innerWithLin Λ y Λ x` unfolds to a star-conjugated inner product in
  -- `regionHilbert (Λ ∪ Λ)` taken via two `regionEmbedLeΩ` along proof-
  -- irrelevant equal proofs `Λ ⊆ Λ ∪ Λ`.  Use `change` to coerce to the
  -- common map and apply `LinearIsometry.inner_map_map`.
  change star ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ))
                  (mkRegionTensor Λ η),
                regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ))
                  (mkRegionTensor Λ ξ)⟫_ℂ
        = _
  rw [(regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ))).inner_map_map]
  exact (inner_conj_symm (mkRegionTensor Λ ξ) (mkRegionTensor Λ η)).trans
    (mkRegionTensor_inner Λ ξ η)

end LocalNetLike
