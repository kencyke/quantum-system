module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.LocalEmbed

/-!
# Region-to-global vector embedding

For each `Λ : Finset L`, the canonical isometric embedding of `regionHilbert Λ`
into `globalHilbert L Ω`,

`regionEmbed Λ : regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L Ω`,

sending `EuclideanSpace.single f 1 ↦ lp.single 2 (extendRegionTuple Λ f) 1`.
This is the vector counterpart of `localEmbed Λ`, corresponding to the formal
tensor `ξ ↦ ξ ⊗ |Ω⟩_{Λᶜ}`.

## Main definitions

* `LocalNetLike.regionEmbed Λ` — the isometric embedding.

## Main results

* `LocalNetLike.regionEmbed_apply_basis` — action on basis vectors.
* `LocalNetLike.regionEmbed_inner` — inner products are preserved.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace
open Module

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- The basis-vector family `g ↦ lp.single 2 g 1 : globalHilbert L Ω` is
orthonormal. -/
private theorem orthonormal_lp_single_globalIdx :
    Orthonormal ℂ (fun g : globalIdx L Ω =>
      (lp.single 2 g (1 : ℂ) : globalHilbert L Ω)) := by
  refine ⟨fun g => ?_, fun g g' hgg' => ?_⟩
  · -- ‖lp.single 2 g 1‖ = ‖(1:ℂ)‖ = 1
    change ‖(lp.single 2 g (1 : ℂ) : globalHilbert L Ω)‖ = 1
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    simp
  · -- inner is 0 on distinct basis vectors
    change inner ℂ (lp.single 2 g (1 : ℂ) : globalHilbert L Ω)
        (lp.single 2 g' (1 : ℂ) : globalHilbert L Ω) = 0
    rw [lp.inner_single_left]
    simp [lp.single_apply, hgg']

/-- Region-to-global isometric embedding (vector level).  Sends the region-basis
vector `EuclideanSpace.single f 1` to the global-basis vector
`lp.single 2 (extendRegionTuple Λ f) 1` and extends ℂ-linearly. -/
noncomputable def regionEmbed
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s) (Λ : Finset L) :
    regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L Ω :=
  LinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
    ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f => (lp.single 2 (extendRegionTuple (Ω := Ω) Λ f) (1 : ℂ)
        : globalHilbert L Ω))
    (by
      change Orthonormal ℂ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
      rw [OrthonormalBasis.coe_toBasis]
      exact (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).orthonormal)
    (by
      have hlp := (orthonormal_lp_single_globalIdx (L := L) (Ω := Ω)).comp
        (extendRegionTuple (Ω := Ω) Λ) (extendRegionTuple_injective (Ω := Ω) Λ)
      have hfun :
          (⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
                fun f => (lp.single 2 (extendRegionTuple (Ω := Ω) Λ f) (1 : ℂ) :
                          globalHilbert L Ω))
              ∘ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis))
            = (fun f : regionIdx (L := L) Λ =>
                (lp.single 2 (extendRegionTuple (Ω := Ω) Λ f) (1 : ℂ)
                  : globalHilbert L Ω)) := by
        funext i
        simp [Function.comp_apply]
      rw [hfun]
      exact hlp)

@[simp]
theorem regionEmbed_apply_basis
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s) (Λ : Finset L)
    (f : regionIdx (L := L) Λ) :
    regionEmbed Ω Λ (EuclideanSpace.single f (1 : ℂ))
      = (lp.single 2 (extendRegionTuple (Ω := Ω) Λ f) (1 : ℂ)
          : globalHilbert L Ω) := by
  change ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f' => (lp.single 2 (extendRegionTuple (Ω := Ω) Λ f') (1 : ℂ)
        : globalHilbert L Ω))
      (EuclideanSpace.single f (1 : ℂ)) = _
  rw [show (EuclideanSpace.single f (1 : ℂ) : regionHilbert Λ)
        = (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis f
      from by rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]]
  simp

/-- The region-to-global embedding preserves inner products. -/
theorem regionEmbed_inner
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s) (Λ : Finset L)
    (ξ η : regionHilbert Λ) :
    ⟪regionEmbed Ω Λ ξ, regionEmbed Ω Λ η⟫_ℂ = ⟪ξ, η⟫_ℂ :=
  (regionEmbed Ω Λ).inner_map_map ξ η

end LocalNetLike
