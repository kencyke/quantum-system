module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The completed Hilbert-space tensor product and operator amplification

For complex inner product spaces `H₁` and `H₂`, Mathlib equips the *algebraic* tensor product
`H₁ ⊗[ℂ] H₂` with an inner product (`TensorProduct.instInnerProductSpace`), with
`⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, but it is left incomplete (an explicit `TODO` in
`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`). This file packages its completion

`HilbertTensor H₁ H₂ := UniformSpace.Completion (H₁ ⊗[ℂ] H₂)`,

which inherits an `InnerProductSpace ℂ` structure from
`UniformSpace.Completion.innerProductSpace` and is complete, hence a genuine complex Hilbert
space — the object physicists write `H₁ ⊗ H₂` for Hilbert spaces.

It then constructs the **amplifications** of bounded operators,

`amplifyLeft  : B(H₁) → B(HilbertTensor H₁ H₂)`, `A ↦ A ⊗̂ 1`,
`amplifyRight : B(H₂) → B(HilbertTensor H₁ H₂)`, `B ↦ 1 ⊗̂ B`,

obtained by extending the bounded operator `A ⊗ 1` (resp. `1 ⊗ B`) from the dense algebraic
tensor product to the completion. The key analytic input is the cross-norm bound
`‖(A ⊗ 1) z‖ ≤ ‖A‖ * ‖z‖`, proved by writing `z` along an orthonormal family of the second
factor.

## Notation

The textbook symbols `⊗̂` (completed tensor) and `⊗ₕ` (pure tensor) live in the opt-in
`HilbertTensor` scope; activate them with `open scoped HilbertTensor`.

| Symbol | Expansion | How to activate |
|---|---|---|
| `H₁ ⊗̂ H₂` | `HilbertTensor H₁ H₂` | `open scoped HilbertTensor` |
| `x ⊗ₕ y` | `HilbertTensor.tmul x y` | `open scoped HilbertTensor` |

## Main definitions

* `HilbertTensor H₁ H₂` — the completed Hilbert-space tensor product.
* `HilbertTensor.tmul x y` — the pure tensor `x ⊗ y` viewed in the completion.
* `HilbertTensor.amplifyLeft A`, `HilbertTensor.amplifyRight B` — the amplified operators.
* `HilbertTensor.amplifyLeftₐ`, `HilbertTensor.amplifyRightₐ` — the amplifications bundled as
  unital `⋆`-algebra homomorphisms (on genuine Hilbert spaces).

## Main results

* `HilbertTensor.inner_tmul` — the inner product on pure tensors factorises.
* `HilbertTensor.add_tmul` / `tmul_add` / `tmul_smul_left` / `smul_tmul_right` — `tmul` is
  bilinear.
* `TensorProduct.norm_map_left_le` / `norm_map_right_le` — the cross-norm bounds on the
  algebraic tensor product.
* `HilbertTensor.amplifyLeft_tmul` / `amplifyRight_tmul` — the action on pure tensors.
* `HilbertTensor.amplifyLeft_one` / `amplifyLeft_mul` / `amplifyLeft_add` / `amplifyLeft_smul`
  (and the right analogues) — the amplifications are unital `ℂ`-algebra homomorphisms.
-/

@[expose] public section

open scoped TensorProduct

/-! ### Completion of a linear isometric equivalence and of a finite-dimensional space

These are general facts about `UniformSpace.Completion` phrased for normed spaces; they are the
analytic inputs to the constructions below. The completion of a linear isometric equivalence
extends it to the completions, and the completion of a finite-dimensional space is again
finite-dimensional. -/

section Completion

open UniformSpace UniformSpace.Completion

namespace LinearIsometryEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The completed forward map of a linear isometric equivalence, as a continuous linear map. -/
noncomputable def completionCLM (f : E ≃ₗᵢ[𝕜] F) : Completion E →L[𝕜] Completion F :=
  f.toLinearIsometry.toContinuousLinearMap.completion

@[simp] theorem completionCLM_coe (f : E ≃ₗᵢ[𝕜] F) (a : E) :
    f.completionCLM (a : Completion E) = (f a : Completion F) := by
  rw [completionCLM, ContinuousLinearMap.completion_apply_coe,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

theorem completionCLM_left (f : E ≃ₗᵢ[𝕜] F) (x : Completion E) :
    f.symm.completionCLM (f.completionCLM x) = x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq ((map_continuous _).comp (map_continuous _)) continuous_id
  | ih a => rw [completionCLM_coe, completionCLM_coe, LinearIsometryEquiv.symm_apply_apply]

/-- The completion of a linear isometric equivalence `f : E ≃ₗᵢ[𝕜] F`, a linear isometric
equivalence `Completion E ≃ₗᵢ[𝕜] Completion F`. -/
noncomputable def completion (f : E ≃ₗᵢ[𝕜] F) : Completion E ≃ₗᵢ[𝕜] Completion F where
  toFun := f.completionCLM
  invFun := f.symm.completionCLM
  map_add' x y := _root_.map_add f.completionCLM x y
  map_smul' m x := _root_.map_smul f.completionCLM m x
  left_inv := f.completionCLM_left
  right_inv x := by
    have h := f.symm.completionCLM_left x
    rwa [LinearIsometryEquiv.symm_symm] at h
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (continuous_norm.comp f.completionCLM.continuous) continuous_norm
    | ih a =>
      change ‖f.completionCLM (a : Completion E)‖ = ‖(a : Completion E)‖
      rw [completionCLM_coe, Completion.norm_coe, Completion.norm_coe, f.norm_map]

@[simp] theorem completion_coe (f : E ≃ₗᵢ[𝕜] F) (a : E) :
    f.completion (a : Completion E) = (f a : Completion F) := by
  change f.completionCLM (a : Completion E) = _
  exact f.completionCLM_coe a

end LinearIsometryEquiv

/-- The completion of a finite-dimensional normed space (over a complete field) is
finite-dimensional. The coercion `toComplL : E → Completion E` is a linear map with dense range
whose image is a finite-dimensional (hence closed) subspace, so it is surjective, and
finite-dimensionality transfers along a surjection. -/
theorem FiniteDimensional.completion {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    FiniteDimensional 𝕜 (Completion E) := by
  set f : E →L[𝕜] Completion E := Completion.toComplL with hf
  have hdense : DenseRange f := by
    simpa [hf, Completion.coe_toComplL] using Completion.denseRange_coe (α := E)
  have hclosed : IsClosed (Set.range f) := by
    have h := (LinearMap.range (f : E →ₗ[𝕜] Completion E)).closed_of_finiteDimensional
    rwa [LinearMap.coe_range] at h
  have hsurj : Function.Surjective f := by
    have hu : Set.range f = Set.univ := by rw [← hclosed.closure_eq, hdense.closure_eq]
    exact Set.range_eq_univ.mp hu
  exact Module.Finite.of_surjective (f : E →ₗ[𝕜] Completion E) hsurj

end Completion

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- The **completed Hilbert-space tensor product** of two complex inner product spaces: the
completion of the algebraic tensor product `H₁ ⊗[ℂ] H₂` with respect to the inner-product norm
`‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`. As the completion of an inner product space it is again an
`InnerProductSpace ℂ`, and being a completion it is a `CompleteSpace`, so it is a complex
Hilbert space. -/
abbrev HilbertTensor (H₁ H₂ : Type*)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] : Type _ :=
  UniformSpace.Completion (H₁ ⊗[ℂ] H₂)

/-- The completed tensor product of two finite-dimensional Hilbert spaces is finite-dimensional:
the algebraic tensor product is already finite-dimensional (hence complete), so completing it
changes nothing. -/
instance instFiniteDimensionalHilbertTensor [FiniteDimensional ℂ H₁] [FiniteDimensional ℂ H₂] :
    FiniteDimensional ℂ (HilbertTensor H₁ H₂) := by
  haveI : FiniteDimensional ℂ (H₁ ⊗[ℂ] H₂) := Module.Finite.tensorProduct ℂ H₁ H₂
  exact FiniteDimensional.completion

namespace HilbertTensor

/-- A pure tensor `x ⊗ y` regarded as an element of the completed tensor product. -/
noncomputable def tmul (x : H₁) (y : H₂) : HilbertTensor H₁ H₂ :=
  ((x ⊗ₜ[ℂ] y : H₁ ⊗[ℂ] H₂) : HilbertTensor H₁ H₂)

/-- `H₁ ⊗̂ H₂` denotes the completed Hilbert-space tensor product `HilbertTensor H₁ H₂`. The hat
distinguishes it from Mathlib's algebraic tensor product `H₁ ⊗[ℂ] H₂`. -/
scoped infixr:35 " ⊗̂ " => HilbertTensor

/-- `x ⊗ₕ y` denotes the pure tensor `HilbertTensor.tmul x y` in the completed tensor product. The
subscript `h` (Hilbert) distinguishes it from Mathlib's algebraic pure tensor `x ⊗ₜ y`. -/
scoped infixr:100 " ⊗ₕ " => HilbertTensor.tmul

/-- The inner product of two pure tensors in the completed tensor product factorises as the
product of the inner products of the factors. -/
@[simp] theorem inner_tmul (x x' : H₁) (y y' : H₂) :
    inner ℂ (x ⊗ₕ y) (x' ⊗ₕ y') = inner ℂ x x' * inner ℂ y y' := by
  rw [tmul, tmul, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

/-- The norm of a pure tensor factorises. -/
@[simp] theorem norm_tmul (x : H₁) (y : H₂) : ‖x ⊗ₕ y‖ = ‖x‖ * ‖y‖ := by
  rw [tmul, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

/-- The pure tensor is additive in its right argument. -/
theorem tmul_add (x : H₁) (y y' : H₂) : x ⊗ₕ (y + y') = x ⊗ₕ y + x ⊗ₕ y' := by
  rw [tmul, tmul, tmul, ← UniformSpace.Completion.coe_add, TensorProduct.tmul_add]

/-- The pure tensor is additive in its left argument. -/
theorem add_tmul (x x' : H₁) (y : H₂) : (x + x') ⊗ₕ y = x ⊗ₕ y + x' ⊗ₕ y := by
  rw [tmul, tmul, tmul, ← UniformSpace.Completion.coe_add, TensorProduct.add_tmul]

/-- A scalar in the left argument of a pure tensor factors out. -/
theorem tmul_smul_left (c : ℂ) (x : H₁) (y : H₂) : (c • x) ⊗ₕ y = c • x ⊗ₕ y := by
  rw [tmul, tmul, ← UniformSpace.Completion.coe_smul, TensorProduct.smul_tmul']

/-- A scalar in the right argument of a pure tensor factors out. -/
theorem smul_tmul_right (c : ℂ) (x : H₁) (y : H₂) : x ⊗ₕ (c • y) = c • x ⊗ₕ y := by
  rw [tmul, tmul, ← UniformSpace.Completion.coe_smul, TensorProduct.tmul_smul]

/-- A pure tensor with a zero left argument vanishes. -/
@[simp] theorem zero_tmul (y : H₂) : (0 : H₁) ⊗ₕ y = 0 := by
  rw [tmul, TensorProduct.zero_tmul, UniformSpace.Completion.coe_zero]

/-- A pure tensor with a zero right argument vanishes. -/
@[simp] theorem tmul_zero (x : H₁) : x ⊗ₕ (0 : H₂) = 0 := by
  rw [tmul, TensorProduct.tmul_zero, UniformSpace.Completion.coe_zero]

/-- The bounded inclusion `H₁ → H₁ ⊗̂ H₂`, `x ↦ x ⊗ z`, for a fixed `z ∈ H₂`. Its operator norm is
`‖z‖` (`‖tmulLeftL z x‖ = ‖x‖ * ‖z‖`), so it is an isometry exactly when `‖z‖ = 1`. This is the
mirror image of `tmulRightL`, fixing the second factor instead of the first. -/
noncomputable def tmulLeftL (z : H₂) : H₁ →L[ℂ] HilbertTensor H₁ H₂ :=
  UniformSpace.Completion.toComplL.comp
    (LinearMap.mkContinuous ((TensorProduct.mk ℂ H₁ H₂).flip z) ‖z‖ fun x => by
      rw [LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.norm_tmul, mul_comm])

@[simp] theorem tmulLeftL_apply (z : H₂) (x : H₁) : tmulLeftL z x = tmul x z := by
  rw [tmulLeftL, ContinuousLinearMap.comp_apply, LinearMap.mkContinuous_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  rfl

end HilbertTensor

namespace TensorProduct

/-- Every element of the algebraic tensor product can be written as a finite sum
`∑ ξ i ⊗ₜ e i` where the second factors `e i` form an orthonormal family of `H₂`. This is the
analytic normal form behind the cross-norm bound: choose a finite-dimensional submodule of `H₂`
carrying the element and take an orthonormal basis of it. -/
theorem exists_orthonormal_rep (z : H₁ ⊗[ℂ] H₂) :
    ∃ (n : ℕ) (e : Fin n → H₂) (ξ : Fin n → H₁),
      Orthonormal ℂ e ∧ z = ∑ i, ξ i ⊗ₜ[ℂ] e i := by
  obtain ⟨N', hN'fin, hz⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite {z} (Set.finite_singleton z)
  obtain ⟨z₀, hz₀⟩ := hz (Set.mem_singleton z)
  haveI : FiniteDimensional ℂ N' := hN'fin
  let b := stdOrthonormalBasis ℂ N'
  set ξ : Fin (Module.finrank ℂ N') → H₁ :=
    fun i => TensorProduct.equivFinsuppOfBasisRight b.toBasis z₀ i with hξ
  have hrep : z₀ = ∑ i, ξ i ⊗ₜ[ℂ] b.toBasis i := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm_apply_apply z₀]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
      Finsupp.sum_fintype _ _ (fun i => by simp)]
  refine ⟨Module.finrank ℂ N', fun i => (b i : H₂), ξ,
    b.orthonormal.comp_linearIsometry N'.subtypeₗᵢ, ?_⟩
  calc z = (LinearMap.lTensor H₁ N'.subtype) z₀ := hz₀.symm
    _ = (LinearMap.lTensor H₁ N'.subtype) (∑ i, ξ i ⊗ₜ[ℂ] b.toBasis i) := by rw [← hrep]
    _ = ∑ i, ξ i ⊗ₜ[ℂ] (b i : H₂) := by
        rw [map_sum]; simp_rw [LinearMap.lTensor_tmul]; rfl

/-- **Cross-norm bound (left factor).** On the algebraic Hilbert tensor product, amplifying a
bounded operator `A` on the first factor by the identity does not increase the norm beyond a
factor of `‖A‖`: `‖(A ⊗ 1) z‖ ≤ ‖A‖ * ‖z‖`. -/
theorem norm_map_left_le (A : H₁ →L[ℂ] H₁) (z : H₁ ⊗[ℂ] H₂) :
    ‖TensorProduct.map A.toLinearMap LinearMap.id z‖ ≤ ‖A‖ * ‖z‖ := by
  obtain ⟨n, e, ξ, he, rfl⟩ := exists_orthonormal_rep z
  classical
  have key : ∀ (η : Fin n → H₁), ‖∑ i, η i ⊗ₜ[ℂ] e i‖ ^ 2 = ∑ i, ‖η i‖ ^ 2 := by
    intro η
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have h : inner ℂ (∑ i, η i ⊗ₜ[ℂ] e i) (∑ i, η i ⊗ₜ[ℂ] e i)
        = ∑ i, inner ℂ (η i) (η i) := by
      rw [sum_inner]
      simp_rw [inner_sum, TensorProduct.inner_tmul, orthonormal_iff_ite.mp he]
      simp [Finset.sum_ite_eq]
    rw [h, map_sum]
    simp_rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [map_sum]
  simp_rw [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, ContinuousLinearMap.coe_coe]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (mul_nonneg (norm_nonneg A) (norm_nonneg _))]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, key, key, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_pow]
  gcongr
  exact A.le_opNorm (ξ i)

/-- The commutation isometry intertwines the two one-sided amplifications on the algebraic
tensor product: swapping the factors turns `1 ⊗ B` into `B ⊗ 1`. -/
theorem commIsometry_map_id (B : H₂ →L[ℂ] H₂) (z : H₁ ⊗[ℂ] H₂) :
    commIsometry ℂ H₁ H₂ (TensorProduct.map LinearMap.id B.toLinearMap z)
      = TensorProduct.map B.toLinearMap LinearMap.id (commIsometry ℂ H₁ H₂ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [map_add, ha, hb]

/-- **Cross-norm bound (right factor).** `‖(1 ⊗ B) z‖ ≤ ‖B‖ * ‖z‖`, obtained from the left bound
by conjugating with the commutation isometry. -/
theorem norm_map_right_le (B : H₂ →L[ℂ] H₂) (z : H₁ ⊗[ℂ] H₂) :
    ‖TensorProduct.map LinearMap.id B.toLinearMap z‖ ≤ ‖B‖ * ‖z‖ := by
  rw [← (commIsometry ℂ H₁ H₂).norm_map (TensorProduct.map LinearMap.id B.toLinearMap z),
    commIsometry_map_id, ← (commIsometry ℂ H₁ H₂).norm_map z]
  exact norm_map_left_le B _

end TensorProduct

namespace HilbertTensor

open UniformSpace

/-- The amplification `A ⊗ 1` as a bounded operator on the *algebraic* tensor product, packaged
from the cross-norm bound `TensorProduct.norm_map_left_le`. -/
noncomputable def algAmplifyLeft (A : H₁ →L[ℂ] H₁) : (H₁ ⊗[ℂ] H₂) →L[ℂ] (H₁ ⊗[ℂ] H₂) :=
  LinearMap.mkContinuous (TensorProduct.map A.toLinearMap LinearMap.id) ‖A‖
    (TensorProduct.norm_map_left_le A)

/-- The amplification `1 ⊗ B` as a bounded operator on the *algebraic* tensor product. -/
noncomputable def algAmplifyRight (B : H₂ →L[ℂ] H₂) : (H₁ ⊗[ℂ] H₂) →L[ℂ] (H₁ ⊗[ℂ] H₂) :=
  LinearMap.mkContinuous (TensorProduct.map LinearMap.id B.toLinearMap) ‖B‖
    (TensorProduct.norm_map_right_le B)

@[simp] theorem algAmplifyLeft_tmul (A : H₁ →L[ℂ] H₁) (x : H₁) (y : H₂) :
    algAmplifyLeft (H₂ := H₂) A (x ⊗ₜ[ℂ] y) = (A x) ⊗ₜ[ℂ] y := by
  simp [algAmplifyLeft]

@[simp] theorem algAmplifyRight_tmul (B : H₂ →L[ℂ] H₂) (x : H₁) (y : H₂) :
    algAmplifyRight (H₁ := H₁) B (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (B y) := by
  simp [algAmplifyRight]

/-- The **left amplification** `A ↦ A ⊗̂ 1` of a bounded operator on the first factor to a bounded
operator on the completed Hilbert tensor product, obtained by extending `algAmplifyLeft A` from
the dense algebraic tensor product to the completion. -/
noncomputable def amplifyLeft (A : H₁ →L[ℂ] H₁) :
    HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂ where
  toFun := Completion.map (algAmplifyLeft A)
  map_add' x y := by
    refine Completion.induction_on₂ x y
      (isClosed_eq ((Completion.continuous_map (f := algAmplifyLeft A)).comp continuous_add)
        (((Completion.continuous_map (f := algAmplifyLeft A)).comp continuous_fst).add
          ((Completion.continuous_map (f := algAmplifyLeft A)).comp continuous_snd)))
      (fun a b => ?_)
    rw [← Completion.coe_add, Completion.map_coe (algAmplifyLeft A).uniformContinuous,
      Completion.map_coe (algAmplifyLeft A).uniformContinuous,
      Completion.map_coe (algAmplifyLeft A).uniformContinuous, ← Completion.coe_add, map_add]
  map_smul' c x := by
    refine Completion.induction_on x
      (isClosed_eq
        ((Completion.continuous_map (f := algAmplifyLeft A)).comp (continuous_const_smul c))
        ((continuous_const_smul c).comp (Completion.continuous_map (f := algAmplifyLeft A))))
      (fun a => ?_)
    rw [← Completion.coe_smul, Completion.map_coe (algAmplifyLeft A).uniformContinuous,
      Completion.map_coe (algAmplifyLeft A).uniformContinuous, ← Completion.coe_smul, map_smul]
    rfl
  cont := Completion.continuous_map

/-- The **right amplification** `B ↦ 1 ⊗̂ B`. -/
noncomputable def amplifyRight (B : H₂ →L[ℂ] H₂) :
    HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂ where
  toFun := Completion.map (algAmplifyRight B)
  map_add' x y := by
    refine Completion.induction_on₂ x y
      (isClosed_eq ((Completion.continuous_map (f := algAmplifyRight B)).comp continuous_add)
        (((Completion.continuous_map (f := algAmplifyRight B)).comp continuous_fst).add
          ((Completion.continuous_map (f := algAmplifyRight B)).comp continuous_snd)))
      (fun a b => ?_)
    rw [← Completion.coe_add, Completion.map_coe (algAmplifyRight B).uniformContinuous,
      Completion.map_coe (algAmplifyRight B).uniformContinuous,
      Completion.map_coe (algAmplifyRight B).uniformContinuous, ← Completion.coe_add, map_add]
  map_smul' c x := by
    refine Completion.induction_on x
      (isClosed_eq
        ((Completion.continuous_map (f := algAmplifyRight B)).comp (continuous_const_smul c))
        ((continuous_const_smul c).comp (Completion.continuous_map (f := algAmplifyRight B))))
      (fun a => ?_)
    rw [← Completion.coe_smul, Completion.map_coe (algAmplifyRight B).uniformContinuous,
      Completion.map_coe (algAmplifyRight B).uniformContinuous, ← Completion.coe_smul, map_smul]
    rfl
  cont := Completion.continuous_map

@[simp] theorem amplifyLeft_tmul (A : H₁ →L[ℂ] H₁) (x : H₁) (y : H₂) :
    amplifyLeft A (x ⊗ₕ y) = (A x) ⊗ₕ y := by
  rw [amplifyLeft, tmul]
  change Completion.map (algAmplifyLeft A) _ = _
  rw [Completion.map_coe (algAmplifyLeft A).uniformContinuous, algAmplifyLeft_tmul, tmul]

@[simp] theorem amplifyRight_tmul (B : H₂ →L[ℂ] H₂) (x : H₁) (y : H₂) :
    amplifyRight B (x ⊗ₕ y) = x ⊗ₕ (B y) := by
  rw [amplifyRight, tmul]
  change Completion.map (algAmplifyRight B) _ = _
  rw [Completion.map_coe (algAmplifyRight B).uniformContinuous, algAmplifyRight_tmul, tmul]

/-- The defining action of the left amplification on the image of the algebraic tensor product. -/
@[simp] theorem amplifyLeft_coe (A : H₁ →L[ℂ] H₁) (a : H₁ ⊗[ℂ] H₂) :
    amplifyLeft A (a : HilbertTensor H₁ H₂)
      = ((algAmplifyLeft A a : H₁ ⊗[ℂ] H₂) : HilbertTensor H₁ H₂) :=
  Completion.map_coe (algAmplifyLeft A).uniformContinuous a

/-- The defining action of the right amplification on the image of the algebraic tensor product. -/
@[simp] theorem amplifyRight_coe (B : H₂ →L[ℂ] H₂) (a : H₁ ⊗[ℂ] H₂) :
    amplifyRight B (a : HilbertTensor H₁ H₂)
      = ((algAmplifyRight B a : H₁ ⊗[ℂ] H₂) : HilbertTensor H₁ H₂) :=
  Completion.map_coe (algAmplifyRight B).uniformContinuous a

/-! ### Multiplicativity and unitality

The amplifications are unital algebra homomorphisms onto their images: they send the identity to
the identity and turn composition in `B(H₁)` (resp. `B(H₂)`) into composition in
`B(HilbertTensor H₁ H₂)`. -/

theorem algAmplifyLeft_one_apply (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyLeft (H₂ := H₂) (1 : H₁ →L[ℂ] H₁) a = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add p q hp hq => simp [map_add, hp, hq]

theorem algAmplifyLeft_mul_apply (A B : H₁ →L[ℂ] H₁) (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyLeft (A * B) a = algAmplifyLeft A (algAmplifyLeft B a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.mul_apply]
  | add p q hp hq => simp [map_add, hp, hq]

theorem algAmplifyRight_one_apply (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyRight (H₁ := H₁) (1 : H₂ →L[ℂ] H₂) a = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add p q hp hq => simp [map_add, hp, hq]

theorem algAmplifyRight_mul_apply (A B : H₂ →L[ℂ] H₂) (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyRight (A * B) a = algAmplifyRight A (algAmplifyRight B a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.mul_apply]
  | add p q hp hq => simp [map_add, hp, hq]

@[simp] theorem amplifyLeft_one :
    amplifyLeft (1 : H₁ →L[ℂ] H₁) = (1 : HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂) := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyLeft _).continuous (ContinuousLinearMap.continuous 1)) (fun a => ?_)
  simp [algAmplifyLeft_one_apply]

theorem amplifyLeft_mul (A B : H₁ →L[ℂ] H₁) :
    amplifyLeft (H₂ := H₂) (A * B) = amplifyLeft A * amplifyLeft B := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyLeft _).continuous
      ((amplifyLeft A).continuous.comp (amplifyLeft B).continuous)) (fun a => ?_)
  simp [ContinuousLinearMap.mul_apply, algAmplifyLeft_mul_apply]

@[simp] theorem amplifyRight_one :
    amplifyRight (1 : H₂ →L[ℂ] H₂) = (1 : HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂) := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyRight _).continuous (ContinuousLinearMap.continuous 1)) (fun a => ?_)
  simp [algAmplifyRight_one_apply]

theorem amplifyRight_mul (A B : H₂ →L[ℂ] H₂) :
    amplifyRight (H₁ := H₁) (A * B) = amplifyRight A * amplifyRight B := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyRight _).continuous
      ((amplifyRight A).continuous.comp (amplifyRight B).continuous)) (fun a => ?_)
  simp [ContinuousLinearMap.mul_apply, algAmplifyRight_mul_apply]

/-! ### Additivity and homogeneity in the amplified operator

The amplifications `A ↦ A ⊗̂ 1` and `B ↦ 1 ⊗̂ B` are themselves `ℂ`-linear in the operator
being amplified: they preserve `0`, addition, and scalar multiplication. -/

theorem algAmplifyLeft_zero_apply (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyLeft (H₂ := H₂) (0 : H₁ →L[ℂ] H₁) a = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add p q hp hq => simp [map_add, hp, hq]

theorem algAmplifyLeft_add_apply (A B : H₁ →L[ℂ] H₁) (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyLeft (A + B) a = algAmplifyLeft A a + algAmplifyLeft B a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.add_apply, TensorProduct.add_tmul]
  | add p q hp hq => simp only [map_add, hp, hq]; abel

theorem algAmplifyLeft_smul_apply (c : ℂ) (A : H₁ →L[ℂ] H₁) (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyLeft (c • A) a = c • algAmplifyLeft A a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.smul_apply, TensorProduct.smul_tmul']
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]

theorem algAmplifyRight_zero_apply (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyRight (H₁ := H₁) (0 : H₂ →L[ℂ] H₂) a = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add p q hp hq => simp [map_add, hp, hq]

theorem algAmplifyRight_add_apply (A B : H₂ →L[ℂ] H₂) (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyRight (A + B) a = algAmplifyRight A a + algAmplifyRight B a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.add_apply, TensorProduct.tmul_add]
  | add p q hp hq => simp only [map_add, hp, hq]; abel

theorem algAmplifyRight_smul_apply (c : ℂ) (B : H₂ →L[ℂ] H₂) (a : H₁ ⊗[ℂ] H₂) :
    algAmplifyRight (c • B) a = c • algAmplifyRight B a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.smul_apply, TensorProduct.tmul_smul]
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]

@[simp] theorem amplifyLeft_zero :
    amplifyLeft (0 : H₁ →L[ℂ] H₁) = (0 : HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂) := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyLeft _).continuous (ContinuousLinearMap.continuous 0)) (fun a => ?_)
  rw [amplifyLeft_coe, algAmplifyLeft_zero_apply, UniformSpace.Completion.coe_zero,
    ContinuousLinearMap.zero_apply]

theorem amplifyLeft_add (A B : H₁ →L[ℂ] H₁) :
    amplifyLeft (H₂ := H₂) (A + B) = amplifyLeft A + amplifyLeft B := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyLeft _).continuous
      ((amplifyLeft A).continuous.add (amplifyLeft B).continuous)) (fun a => ?_)
  rw [amplifyLeft_coe, algAmplifyLeft_add_apply, UniformSpace.Completion.coe_add,
    ContinuousLinearMap.add_apply, amplifyLeft_coe, amplifyLeft_coe]

theorem amplifyLeft_smul (c : ℂ) (A : H₁ →L[ℂ] H₁) :
    amplifyLeft (H₂ := H₂) (c • A) = c • amplifyLeft A := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyLeft _).continuous
      ((continuous_const_smul c).comp (amplifyLeft A).continuous)) (fun a => ?_)
  rw [amplifyLeft_coe, algAmplifyLeft_smul_apply, UniformSpace.Completion.coe_smul,
    ContinuousLinearMap.smul_apply, amplifyLeft_coe]

@[simp] theorem amplifyRight_zero :
    amplifyRight (0 : H₂ →L[ℂ] H₂) = (0 : HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂) := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyRight _).continuous (ContinuousLinearMap.continuous 0)) (fun a => ?_)
  rw [amplifyRight_coe, algAmplifyRight_zero_apply, UniformSpace.Completion.coe_zero,
    ContinuousLinearMap.zero_apply]

theorem amplifyRight_add (A B : H₂ →L[ℂ] H₂) :
    amplifyRight (H₁ := H₁) (A + B) = amplifyRight A + amplifyRight B := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyRight _).continuous
      ((amplifyRight A).continuous.add (amplifyRight B).continuous)) (fun a => ?_)
  rw [amplifyRight_coe, algAmplifyRight_add_apply, UniformSpace.Completion.coe_add,
    ContinuousLinearMap.add_apply, amplifyRight_coe, amplifyRight_coe]

theorem amplifyRight_smul (c : ℂ) (B : H₂ →L[ℂ] H₂) :
    amplifyRight (H₁ := H₁) (c • B) = c • amplifyRight B := by
  ext z
  refine Completion.induction_on z
    (isClosed_eq (amplifyRight _).continuous
      ((continuous_const_smul c).comp (amplifyRight B).continuous)) (fun a => ?_)
  rw [amplifyRight_coe, algAmplifyRight_smul_apply, UniformSpace.Completion.coe_smul,
    ContinuousLinearMap.smul_apply, amplifyRight_coe]

/-! ### The commutation (swap) equivalence

Swapping the two tensor factors is a linear isometric equivalence
`HilbertTensor H₁ H₂ ≃ₗᵢ HilbertTensor H₂ H₁`, the completion of Mathlib's algebraic
`TensorProduct.commIsometry`. Conjugating by it turns a right amplification `1 ⊗̂ B` into the left
amplification `B ⊗̂ 1` on the swapped space, which is what lets the right-hand slice lemma be
reused verbatim on the left. -/

/-- The **commutation (swap) equivalence** `x ⊗̂ y ↦ y ⊗̂ x`, a linear isometric equivalence
`HilbertTensor H₁ H₂ ≃ₗᵢ HilbertTensor H₂ H₁`, obtained by completing `TensorProduct.commIsometry`. -/
noncomputable def commEquiv : HilbertTensor H₁ H₂ ≃ₗᵢ[ℂ] HilbertTensor H₂ H₁ :=
  (TensorProduct.commIsometry ℂ H₁ H₂).completion

@[simp] theorem commEquiv_tmul (x : H₁) (y : H₂) : commEquiv (x ⊗ₕ y) = y ⊗ₕ x := by
  rw [commEquiv, tmul, LinearIsometryEquiv.completion_coe, TensorProduct.commIsometry_apply,
    TensorProduct.comm_tmul, tmul]

@[simp] theorem commEquiv_symm_tmul (y : H₂) (x : H₁) :
    commEquiv.symm (y ⊗ₕ x) = x ⊗ₕ y := by
  rw [← commEquiv_tmul x y, LinearIsometryEquiv.symm_apply_apply]

/-- Conjugating a right amplification `1 ⊗̂ B` by the swap equivalence yields the left
amplification `B ⊗̂ 1` on the swapped space. -/
theorem conjStarAlgEquiv_commEquiv_amplifyRight (B : H₂ →L[ℂ] H₂) :
    commEquiv.conjStarAlgEquiv (amplifyRight (H₁ := H₁) B) = amplifyLeft (H₂ := H₁) B := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  refine UniformSpace.Completion.induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun a => ?_)
  induction a using TensorProduct.induction_on with
  | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
  | tmul y x =>
      change commEquiv (amplifyRight B (commEquiv.symm (y ⊗ₕ x))) = amplifyLeft B (y ⊗ₕ x)
      rw [commEquiv_symm_tmul, amplifyRight_tmul, commEquiv_tmul, amplifyLeft_tmul]
  | add p q hp hq =>
      simp only [UniformSpace.Completion.coe_add, map_add, hp, hq]

/-- Conjugating a right amplification `1 ⊗̂ S` by the *inverse* swap equivalence yields the left
amplification `S ⊗̂ 1`. This is the back-transport companion of
`conjStarAlgEquiv_commEquiv_amplifyRight`, used to carry the right-hand slice lemma back to the
original space. -/
theorem conjStarAlgEquiv_symm_commEquiv_amplifyRight (S : H₁ →L[ℂ] H₁) :
    commEquiv.conjStarAlgEquiv.symm (amplifyRight (H₁ := H₂) S) = amplifyLeft (H₂ := H₂) S := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply]
  refine UniformSpace.Completion.induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun a => ?_)
  induction a using TensorProduct.induction_on with
  | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
  | tmul x y =>
      change commEquiv.symm (amplifyRight S (commEquiv (x ⊗ₕ y))) = amplifyLeft S (x ⊗ₕ y)
      rw [commEquiv_tmul, amplifyRight_tmul, commEquiv_symm_tmul, amplifyLeft_tmul]
  | add p q hp hq =>
      simp only [UniformSpace.Completion.coe_add, map_add, hp, hq]

/-! ### Adjoints

On genuine Hilbert spaces (`CompleteSpace H₁`, `CompleteSpace H₂`) the amplifications are
`*`-homomorphisms: they intertwine the adjoint on `B(H₁)` (resp. `B(H₂)`) with the adjoint on
`B(HilbertTensor H₁ H₂)`, hence preserve the `star` operation. Together with
`amplifyLeft_one`/`amplifyLeft_mul`/`amplifyLeft_add`/`amplifyLeft_smul` this exhibits
`amplifyLeft` and `amplifyRight` as unital `*`-algebra homomorphisms, bundled as
`amplifyLeftₐ` and `amplifyRightₐ`. -/

section Adjoint

variable [CompleteSpace H₁] [CompleteSpace H₂]

omit [CompleteSpace H₂] in
theorem algAmplifyLeft_inner_adjoint (A : H₁ →L[ℂ] H₁) (a b : H₁ ⊗[ℂ] H₂) :
    inner ℂ (algAmplifyLeft (ContinuousLinearMap.adjoint A) a) b
      = inner ℂ a (algAmplifyLeft A b) := by
  simp only [algAmplifyLeft, LinearMap.mkContinuous_apply]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
        simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, ContinuousLinearMap.coe_coe,
          TensorProduct.inner_tmul]
        rw [ContinuousLinearMap.adjoint_inner_left]
    | add p q hp hq => simp only [inner_add_right, map_add, hp, hq]
  | add p q hp hq => simp only [inner_add_left, map_add, hp, hq]

omit [CompleteSpace H₁] in
theorem algAmplifyRight_inner_adjoint (B : H₂ →L[ℂ] H₂) (a b : H₁ ⊗[ℂ] H₂) :
    inner ℂ (algAmplifyRight (ContinuousLinearMap.adjoint B) a) b
      = inner ℂ a (algAmplifyRight B b) := by
  simp only [algAmplifyRight, LinearMap.mkContinuous_apply]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
        simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, ContinuousLinearMap.coe_coe,
          TensorProduct.inner_tmul]
        rw [ContinuousLinearMap.adjoint_inner_left]
    | add p q hp hq => simp only [inner_add_right, map_add, hp, hq]
  | add p q hp hq => simp only [inner_add_left, map_add, hp, hq]

omit [CompleteSpace H₂] in
/-- The adjoint of the left amplification of `A` is the left amplification of the adjoint of `A`. -/
theorem amplifyLeft_adjoint (A : H₁ →L[ℂ] H₁) :
    ContinuousLinearMap.adjoint (amplifyLeft (H₂ := H₂) A)
      = amplifyLeft (ContinuousLinearMap.adjoint A) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  refine Completion.induction_on₂ u v (isClosed_eq (by fun_prop) (by fun_prop)) (fun a b => ?_)
  rw [amplifyLeft_coe, amplifyLeft_coe, UniformSpace.Completion.inner_coe,
    UniformSpace.Completion.inner_coe, algAmplifyLeft_inner_adjoint]

omit [CompleteSpace H₁] in
/-- The adjoint of the right amplification of `B` is the right amplification of the adjoint of
`B`. -/
theorem amplifyRight_adjoint (B : H₂ →L[ℂ] H₂) :
    ContinuousLinearMap.adjoint (amplifyRight (H₁ := H₁) B)
      = amplifyRight (ContinuousLinearMap.adjoint B) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  refine Completion.induction_on₂ u v (isClosed_eq (by fun_prop) (by fun_prop)) (fun a b => ?_)
  rw [amplifyRight_coe, amplifyRight_coe, UniformSpace.Completion.inner_coe,
    UniformSpace.Completion.inner_coe, algAmplifyRight_inner_adjoint]

omit [CompleteSpace H₂] in
/-- The left amplification preserves the `star` (adjoint) operation. -/
@[simp] theorem amplifyLeft_star (A : H₁ →L[ℂ] H₁) :
    star (amplifyLeft (H₂ := H₂) A) = amplifyLeft (star A) :=
  amplifyLeft_adjoint A

omit [CompleteSpace H₁] in
/-- The right amplification preserves the `star` (adjoint) operation. -/
@[simp] theorem amplifyRight_star (B : H₂ →L[ℂ] H₂) :
    star (amplifyRight (H₁ := H₁) B) = amplifyRight (star B) :=
  amplifyRight_adjoint B

omit [CompleteSpace H₂] in
/-- The **left amplification** `A ↦ A ⊗̂ 1`, bundled as a unital `⋆`-algebra homomorphism
`B(H₁) →⋆ₐ[ℂ] B(HilbertTensor H₁ H₂)`. This packages `amplifyLeft_one`, `amplifyLeft_mul`,
`amplifyLeft_add`, `amplifyLeft_smul`, and `amplifyLeft_star` into a single morphism. -/
noncomputable def amplifyLeftₐ :
    (H₁ →L[ℂ] H₁) →⋆ₐ[ℂ] (HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂) where
  toFun := amplifyLeft
  map_one' := amplifyLeft_one
  map_mul' := amplifyLeft_mul
  map_zero' := amplifyLeft_zero
  map_add' := amplifyLeft_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, amplifyLeft_smul,
      amplifyLeft_one]
  map_star' A := (amplifyLeft_star A).symm

omit [CompleteSpace H₂] in
@[simp] theorem amplifyLeftₐ_apply (A : H₁ →L[ℂ] H₁) :
    amplifyLeftₐ (H₂ := H₂) A = amplifyLeft A := rfl

omit [CompleteSpace H₁] in
/-- The **right amplification** `B ↦ 1 ⊗̂ B`, bundled as a unital `⋆`-algebra homomorphism
`B(H₂) →⋆ₐ[ℂ] B(HilbertTensor H₁ H₂)`. -/
noncomputable def amplifyRightₐ :
    (H₂ →L[ℂ] H₂) →⋆ₐ[ℂ] (HilbertTensor H₁ H₂ →L[ℂ] HilbertTensor H₁ H₂) where
  toFun := amplifyRight
  map_one' := amplifyRight_one
  map_mul' := amplifyRight_mul
  map_zero' := amplifyRight_zero
  map_add' := amplifyRight_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, amplifyRight_smul,
      amplifyRight_one]
  map_star' B := (amplifyRight_star B).symm

omit [CompleteSpace H₁] in
@[simp] theorem amplifyRightₐ_apply (B : H₂ →L[ℂ] H₂) :
    amplifyRightₐ (H₁ := H₁) B = amplifyRight B := rfl

end Adjoint

/-! ### The tensor bridge `ℓ²(ι) ⊗̂ K ≃ lp (fun _ : ι => K) 2`

The completed Hilbert tensor product of `ℓ²(ι) = lp (fun _ : ι => ℂ) 2` with a Hilbert space `K`
is, canonically, the `ℓ²` sum of `ι`-many copies of `K`. The isomorphism sends the pure tensor
`δᵢ ⊗ k` (with `δᵢ = lp.single 2 i 1` the `i`-th standard basis vector of `ℓ²(ι)`) to the single
`lp.single 2 i k`. It is built by exhibiting the inclusions `k ↦ δᵢ ⊗ k` as an orthogonal family
whose total span is dense, i.e. as a Hilbert sum (`IsHilbertSum`). -/

section LpTensorBridge

open scoped ENNReal

variable {ι : Type*} [DecidableEq ι]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The isometric inclusion `K → ℓ²(ι) ⊗̂ K`, `k ↦ δᵢ ⊗ k`, where `δᵢ = lp.single 2 i 1` is the
`i`-th standard basis vector of `ℓ²(ι) = lp (fun _ : ι => ℂ) 2`. As `δᵢ` is a unit vector this is a
genuine linear isometry; the family `i ↦ tmulSingleₗᵢ i` exhibits `ℓ²(ι) ⊗̂ K` as the Hilbert sum
of copies of `K`. -/
noncomputable def tmulSingleₗᵢ (i : ι) :
    K →ₗᵢ[ℂ] (lp (fun _ : ι => ℂ) 2) ⊗̂ K where
  toFun k := tmul (lp.single 2 i (1 : ℂ)) k
  map_add' k k' := tmul_add _ k k'
  map_smul' c k := by
    rw [RingHom.id_apply, tmul, tmul, TensorProduct.tmul_smul, UniformSpace.Completion.coe_smul]
  norm_map' k := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_tmul]
    rw [lp.norm_single (p := 2) (by norm_num), norm_one, one_mul]

@[simp] theorem tmulSingleₗᵢ_apply (i : ι) (k : K) :
    tmulSingleₗᵢ i k = tmul (lp.single 2 i (1 : ℂ)) k := by rfl

/-- Distinct standard basis vectors of `ℓ²(ι)` are orthogonal, so the inclusions `tmulSingleₗᵢ`
form an orthogonal family. -/
theorem orthogonalFamily_tmulSingleₗᵢ :
    OrthogonalFamily ℂ (fun _ : ι => K) (fun i => tmulSingleₗᵢ (K := K) i) := by
  intro i j hij k k'
  have hδ : inner ℂ (lp.single 2 i (1 : ℂ) : lp (fun _ : ι => ℂ) 2) (lp.single 2 j (1 : ℂ)) = 0 := by
    rw [lp.inner_single_left, lp.coeFn_single, Pi.single_eq_of_ne hij, inner_zero_right]
  rw [tmulSingleₗᵢ_apply, tmulSingleₗᵢ_apply, inner_tmul, hδ, zero_mul]

/-- The orthogonal family `tmulSingleₗᵢ` has dense total span, exhibiting `ℓ²(ι) ⊗̂ K` as the
Hilbert sum of `ι`-many copies of `K`. Density is proved by approximating a pure tensor
`a ⊗ k` (`a ∈ ℓ²(ι)`) by the convergent series `∑ᵢ (a i) • (δᵢ ⊗ k)`, each term of which lies in
the range of `tmulSingleₗᵢ i`. -/
theorem isHilbertSum_tmulSingleₗᵢ [CompleteSpace K] :
    IsHilbertSum ℂ (fun _ : ι => K) (fun i => tmulSingleₗᵢ (K := K) i) := by
  haveI : ∀ _ : ι, CompleteSpace K := fun _ => inferInstance
  refine IsHilbertSum.mk orthogonalFamily_tmulSingleₗᵢ ?_
  set M : Submodule ℂ (HilbertTensor (lp (fun _ : ι => ℂ) 2) K) :=
    ⨆ i, LinearMap.range (tmulSingleₗᵢ (K := K) i).toLinearMap with hM
  have key : ∀ z : (lp (fun _ : ι => ℂ) 2) ⊗[ℂ] K,
      ((z : HilbertTensor (lp (fun _ : ι => ℂ) 2) K)) ∈ M.topologicalClosure := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [UniformSpace.Completion.coe_zero]
        exact (M.topologicalClosure).zero_mem
    | add p q hp hq =>
        rw [UniformSpace.Completion.coe_add]
        exact (M.topologicalClosure).add_mem hp hq
    | tmul a k =>
        change tmul a k ∈ M.topologicalClosure
        have hsum : HasSum (fun i => tmul (lp.single 2 i (a i)) k) (tmul a k) := by
          have h := (lp.hasSum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num) a).mapL
            (tmulLeftL (H₁ := lp (fun _ : ι => ℂ) 2) (H₂ := K) k)
          simpa only [tmulLeftL_apply] using h
        have hmem : ∀ i, tmul (lp.single 2 i (a i)) k ∈ M := by
          intro i
          have heq : tmul (lp.single 2 i (a i)) k = (a i) • tmulSingleₗᵢ (K := K) i k := by
            rw [tmulSingleₗᵢ_apply,
              show (lp.single 2 i (a i) : lp (fun _ : ι => ℂ) 2)
                  = (a i) • lp.single 2 i (1 : ℂ) by
                rw [← lp.single_smul, smul_eq_mul, mul_one],
              tmul, tmul, ← TensorProduct.smul_tmul', UniformSpace.Completion.coe_smul]
          rw [heq]
          exact Submodule.smul_mem _ _
            (Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ k))
        have hcl : tmul a k ∈ closure (M : Set (HilbertTensor (lp (fun _ : ι => ℂ) 2) K)) :=
          mem_closure_of_tendsto hsum
            (Filter.Eventually.of_forall fun s =>
              SetLike.mem_coe.mpr (Submodule.sum_mem _ fun i _ => hmem i))
        rwa [← Submodule.topologicalClosure_coe, SetLike.mem_coe] at hcl
  have hsub : Set.range ((↑) : (lp (fun _ : ι => ℂ) 2 ⊗[ℂ] K) →
      HilbertTensor (lp (fun _ : ι => ℂ) 2) K) ⊆ (M.topologicalClosure : Set _) := by
    rintro _ ⟨z, rfl⟩
    exact key z
  rw [top_le_iff]
  apply SetLike.coe_injective
  rw [Submodule.top_coe]
  apply Set.eq_univ_of_univ_subset
  rw [← UniformSpace.Completion.denseRange_coe.closure_range]
  exact closure_minimal hsub M.isClosed_topologicalClosure

/-- **Tensor bridge.** The `ℓ²` sum of `ι`-many copies of a Hilbert space `K` is isometrically the
completed Hilbert tensor product `ℓ²(ι) ⊗̂ K`, where `ℓ²(ι) = lp (fun _ : ι => ℂ) 2`. Under the
bijection the single `lp.single 2 i k` corresponds to the pure tensor `δᵢ ⊗ k`
(`lpTensorEquiv_single`). -/
noncomputable def lpTensorEquiv [CompleteSpace K] :
    lp (fun _ : ι => K) 2 ≃ₗᵢ[ℂ] (lp (fun _ : ι => ℂ) 2) ⊗̂ K :=
  isHilbertSum_tmulSingleₗᵢ.linearIsometryEquiv.symm

@[simp] theorem lpTensorEquiv_single [CompleteSpace K] (i : ι) (k : K) :
    lpTensorEquiv (lp.single 2 i k) = (lp.single 2 i (1 : ℂ)) ⊗ₕ k := by
  rw [lpTensorEquiv,
    IsHilbertSum.linearIsometryEquiv_symm_apply_single isHilbertSum_tmulSingleₗᵢ,
    tmulSingleₗᵢ_apply]

end LpTensorBridge

end HilbertTensor
