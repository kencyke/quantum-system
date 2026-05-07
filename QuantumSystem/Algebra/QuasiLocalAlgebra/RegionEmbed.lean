module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.LocalEmbed

/-!
# Region-to-global vector embedding (Phase 1)

For each finite region `Λ : Finset L` we build the canonical isometric embedding
of the finite-region Hilbert space `regionHilbert Λ` into the reference-sector
infinite-site Hilbert space `globalHilbert L`,

`regionEmbed Λ : regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L`,

defined on basis vectors by
`regionEmbed Λ (EuclideanSpace.single f 1) = lp.single 2 (extendRegionTuple Λ f) 1`
and extended by linearity.  This is the *vector* counterpart of the *operator*
embedding `localEmbed Λ` from `LocalEmbed.lean`: in the standard
Naaijkens / Bratteli–Robinson picture it corresponds to the formal tensor
`ξ ↦ ξ ⊗ |Ω⟩_{Λᶜ}`, completing a region vector by the reference basis on the
complement.

## Main definitions

* `LocalNetLike.regionEmbed Λ` — the linear isometric embedding
  `regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L`.

## Main results

* `LocalNetLike.regionEmbed_apply_basis` — sends region-basis vectors to
  global-basis vectors via `extendRegionTuple`.
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
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- The basis-vector family `g ↦ lp.single 2 g 1 : globalHilbert L` is
orthonormal. -/
private theorem orthonormal_lp_single_globalIdx :
    Orthonormal ℂ (fun g : globalIdx L =>
      (lp.single 2 g (1 : ℂ) : globalHilbert L)) := by
  refine ⟨fun g => ?_, fun g g' hgg' => ?_⟩
  · -- ‖lp.single 2 g 1‖ = ‖(1:ℂ)‖ = 1
    change ‖(lp.single 2 g (1 : ℂ) : globalHilbert L)‖ = 1
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    simp
  · -- inner is 0 on distinct basis vectors
    change inner ℂ (lp.single 2 g (1 : ℂ) : globalHilbert L)
        (lp.single 2 g' (1 : ℂ) : globalHilbert L) = 0
    rw [lp.inner_single_left]
    simp [lp.single_apply, hgg']

/-- Region-to-global isometric embedding (vector level).  Sends the region-basis
vector `EuclideanSpace.single f 1` to the global-basis vector
`lp.single 2 (extendRegionTuple Λ f) 1` and extends ℂ-linearly. -/
noncomputable def regionEmbed (Λ : Finset L) :
    regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L :=
  LinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
    ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f => (lp.single 2 (extendRegionTuple Λ f) (1 : ℂ) : globalHilbert L))
    (by
      change Orthonormal ℂ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
      rw [OrthonormalBasis.coe_toBasis]
      exact (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).orthonormal)
    (by
      have hlp := (orthonormal_lp_single_globalIdx (L := L)).comp
        (extendRegionTuple Λ) (extendRegionTuple_injective Λ)
      have hfun :
          (⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
                fun f => (lp.single 2 (extendRegionTuple Λ f) (1 : ℂ) :
                          globalHilbert L))
              ∘ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis))
            = (fun f : regionIdx (L := L) Λ =>
                (lp.single 2 (extendRegionTuple Λ f) (1 : ℂ) : globalHilbert L)) := by
        funext i
        simp [Function.comp_apply]
      rw [hfun]
      exact hlp)

@[simp]
theorem regionEmbed_apply_basis (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    regionEmbed Λ (EuclideanSpace.single f (1 : ℂ))
      = (lp.single 2 (extendRegionTuple Λ f) (1 : ℂ) : globalHilbert L) := by
  -- regionEmbed Λ is the LinearIsometry from isometryOfOrthonormal whose
  -- underlying linear map is (basisFun.toBasis).constr ℂ (...).
  -- Apply Basis.constr_basis after recognising the input as basisFun.toBasis f.
  change ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f' => (lp.single 2 (extendRegionTuple Λ f') (1 : ℂ) : globalHilbert L))
      (EuclideanSpace.single f (1 : ℂ)) = _
  rw [show (EuclideanSpace.single f (1 : ℂ) : regionHilbert Λ)
        = (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis f
      from by rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]]
  simp

/-- The region-to-global embedding preserves inner products. -/
theorem regionEmbed_inner (Λ : Finset L) (ξ η : regionHilbert Λ) :
    ⟪regionEmbed Λ ξ, regionEmbed Λ η⟫_ℂ = ⟪ξ, η⟫_ℂ :=
  (regionEmbed Λ).inner_map_map ξ η

end LocalNetLike
