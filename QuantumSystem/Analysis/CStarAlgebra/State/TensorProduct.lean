/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.GNS.Construction
public import QuantumSystem.Analysis.CStarAlgebra.Representation.VectorFunctional
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Minimal

/-!
# Product states on the minimal tensor product

For positive functionals `f` on a C⋆-algebra `A` and `g` on a C⋆-algebra `B`, the product functional
`f ⊗ g` is the positive functional on the minimal tensor product `A ⊗ₘᵢₙ B` with
`(f ⊗ g)(a ⊗ b) = f(a) g(b)`. It is constructed as the vector functional of `ξ_f ⊗ ξ_g` in the
tensor product `CStarRep.tensorProduct` of the GNS representations of `f` and `g`, and it is the
only positive functional with these values on pure tensors, the algebraic tensor product being
dense in `A ⊗ₘᵢₙ B`. For states `ω` and `φ` it has norm one: the product state `ω ⊗ φ`.

The algebras are not assumed unital. `A ⊗ₘᵢₙ B` carries its spectral order.

## Main definitions

* `PositiveLinearMap.minTensorProduct f g` — the product functional `f ⊗ g` on `A ⊗ₘᵢₙ B` of positive
  functionals.
* `State.minTensorProduct ω φ` — the product state `ω ⊗ φ` on `A ⊗ₘᵢₙ B`, the case of two states.
* `State.marginalLeft ω`, `State.marginalRight ω` — the marginals `ω(· ⊗ 1)`, for unital `B`, and
  `ω(1 ⊗ ·)`, for unital `A`, of a state `ω` of `A ⊗ₘᵢₙ B`: its restrictions to the factors.

## Main results

* `PositiveLinearMap.minTensorProduct_of_tmul`, `State.minTensorProduct_of_tmul` —
  `(f ⊗ g)(a ⊗ b) = f(a) g(b)`.
* `PositiveLinearMap.opNorm_minTensorProduct` — `‖f ⊗ g‖ = ‖f‖ ‖g‖`.
* `PositiveLinearMap.eq_minTensorProduct`, `State.eq_minTensorProduct` — `f ⊗ g` is the only
  positive functional, and `ω ⊗ φ` the only state, with these values on the pure tensors
  (`MinTensorProduct.ext_of_tmul`).
* `State.marginalLeft_minTensorProduct`, `State.marginalRight_minTensorProduct` — the marginals of
  `ω ⊗ φ` are `ω` and `φ`.
* `State.exists_eq_minTensorProduct_iff`, `State.eq_minTensorProduct_marginal_iff` — a state is a
  product state iff it is the product of its marginals, iff it factorizes over the pure tensors.
* `CStarRep.vectorFunctional_tensorProduct_of_tmul` — the vector functional of `ξ ⊗ η` in the
  tensor product of two representations is, on pure tensors, the product of the vector functionals
  of `ξ` and `η`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace MinTensorProduct GNS ComplexOrder

open UniformSpace

universe u v w₁ w₂

namespace CStarRep

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The vector functional of `ξ ⊗ η` in the tensor product of two representations is, on pure
tensors, the product of the vector functionals of `ξ` and `η`:
`⟪ξ ⊗ η, (π ⊗ ρ)(a ⊗ b) (ξ ⊗ η)⟫ = ⟪ξ, π(a) ξ⟫ * ⟪η, ρ(b) η⟫`. -/
lemma vectorFunctional_tensorProduct_of_tmul (R : CStarRep A) (S : CStarRep B)
    (ξ : R.H) (η : S.H) (a : A) (b : B) :
    (R.tensorProduct S).vectorFunctional
        ((ξ ⊗ₜ[ℂ] η : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H))
        (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) =
      R.vectorFunctional ξ a * S.vectorFunctional η b := by
  have h : (R.tensorProduct S).vectorFunctional
      ((ξ ⊗ₜ[ℂ] η : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H))
      (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) =
        ⟪((ξ ⊗ₜ[ℂ] η : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H)),
          R.spatial S (a ⊗ₜ[ℂ] b) (ξ ⊗ₜ[ℂ] η : R.H ⊗[ℂ] S.H)⟫_ℂ :=
    congrArg (fun T : Completion (R.H ⊗[ℂ] S.H) →L[ℂ] Completion (R.H ⊗[ℂ] S.H) =>
      ⟪((ξ ⊗ₜ[ℂ] η : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H)), T (ξ ⊗ₜ[ℂ] η : R.H ⊗[ℂ] S.H)⟫_ℂ)
      (tensorProduct_π_of R S (a ⊗ₜ[ℂ] b))
  rw [h, spatial_tmul, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
    Completion.inner_coe, TensorProduct.inner_tmul]
  rfl

end CStarRep

namespace PositiveLinearMap

variable {A : Type u} {B : Type v}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The **product functional** `f ⊗ g` on the minimal tensor product `A ⊗ₘᵢₙ B` of positive
functionals `f` on `A` and `g` on `B`: the vector functional of `ξ_f ⊗ ξ_g` in the tensor product
of the GNS representations of `f` and `g`. It is the positive functional with
`(f ⊗ g)(a ⊗ b) = f(a) g(b)` (`PositiveLinearMap.minTensorProduct_of_tmul`,
`PositiveLinearMap.eq_minTensorProduct`). -/
noncomputable def minTensorProduct (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) : (A ⊗ₘᵢₙ B) →ₚ[ℂ] ℂ :=
  .mk₀ (WeakDual.toStrongDual (CStarRep.vectorFunctional
      (CStarRep.tensorProduct (GNS.Representation.canonical f).toCStarRep
        (GNS.Representation.canonical g).toCStarRep)
      (UniformSpace.Completion.coe'
        ((GNS.Representation.canonical f).ξ ⊗ₜ[ℂ] (GNS.Representation.canonical g).ξ)))).toLinearMap
    (CStarRep.vectorFunctional_nonneg _ _)

/-- **The product functional on pure tensors**: `(f ⊗ g)(a ⊗ b) = f(a) g(b)`. -/
@[simp] lemma minTensorProduct_of_tmul (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) (a : A) (b : B) :
    f.minTensorProduct g (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) = f a * g b := by
  change CStarRep.vectorFunctional _ _ _ = _
  rw [CStarRep.vectorFunctional_tensorProduct_of_tmul, CStarRep.vectorFunctional_apply,
    CStarRep.vectorFunctional_apply]
  exact congrArg₂ (· * ·) ((GNS.Representation.canonical f).gns_condition a).symm
    ((GNS.Representation.canonical g).gns_condition b).symm

/-- The product functional `f ⊗ g` is the only positive functional on `A ⊗ₘᵢₙ B` with the values
`f(a) g(b)` on the pure tensors: positive functionals are continuous, and the algebraic tensor
product is dense. -/
lemma eq_minTensorProduct {f : A →ₚ[ℂ] ℂ} {g : B →ₚ[ℂ] ℂ} {ψ : (A ⊗ₘᵢₙ B) →ₚ[ℂ] ℂ}
    (h : ∀ (a : A) (b : B), ψ (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) = f a * g b) :
    ψ = f.minTensorProduct g :=
  MinTensorProduct.ext_of_tmul (map_continuous ψ) (map_continuous _) fun a b => by
    rw [h, minTensorProduct_of_tmul]

open scoped PositiveLinearMap in
/-- **The norm of the product functional is the product of the norms**: `‖f ⊗ g‖ = ‖f‖ ‖g‖`. The
vector `ξ_f ⊗ ξ_g` has norm `√‖f‖ √‖g‖`, and `f ⊗ g` takes the values `f(a) g(b)` on the pure
tensors, whose norm is `‖a‖ * ‖b‖`. -/
theorem opNorm_minTensorProduct (f : A →ₚ[ℂ] ℂ) (g : B →ₚ[ℂ] ℂ) :
    ‖f.minTensorProduct g‖ₒₚ = ‖f‖ₒₚ * ‖g‖ₒₚ := by
  refine le_antisymm ?_ ?_
  · rw [opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (opNorm_nonneg f) (opNorm_nonneg g))
      fun x => ?_
    have h := (WeakDual.toStrongDual (CStarRep.vectorFunctional
      (CStarRep.tensorProduct (GNS.Representation.canonical f).toCStarRep
        (GNS.Representation.canonical g).toCStarRep)
      (UniformSpace.Completion.coe'
        ((GNS.Representation.canonical f).ξ ⊗ₜ[ℂ] (GNS.Representation.canonical g).ξ)))).le_of_opNorm_le
      (CStarRep.opNorm_vectorFunctional_le _ _) x
    have hv : ‖(((GNS.Representation.canonical f).ξ ⊗ₜ[ℂ] (GNS.Representation.canonical g).ξ :
        (GNS.Representation.canonical f).H ⊗[ℂ] (GNS.Representation.canonical g).H) :
        Completion ((GNS.Representation.canonical f).H ⊗[ℂ] (GNS.Representation.canonical g).H))‖ ^ 2 =
        ‖f‖ₒₚ * ‖g‖ₒₚ := by
      rw [Completion.norm_coe, TensorProduct.norm_tmul, mul_pow, GNS.Representation.norm_ξ_sq,
        GNS.Representation.norm_ξ_sq]
    exact h.trans_eq (congrArg (· * ‖x‖) hv)
  · have key (a : A) (b : B) : ‖f a‖ * ‖g b‖ ≤ ‖f.minTensorProduct g‖ₒₚ * (‖a‖ * ‖b‖) := by
      have h := norm_apply_le_opNorm_mul (f.minTensorProduct g) (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b))
      rwa [minTensorProduct_of_tmul, norm_mul, MinTensorProduct.norm_of_tmul] at h
    have hg (a : A) : ‖f a‖ * ‖g‖ₒₚ ≤ ‖f.minTensorProduct g‖ₒₚ * ‖a‖ := by
      have h : ‖(‖f a‖ : ℂ) • (PositiveContinuousLinearMap.ofClass g : B →L[ℂ] ℂ)‖ ≤
          ‖f.minTensorProduct g‖ₒₚ * ‖a‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (opNorm_nonneg _) (norm_nonneg _))
          fun b => by
            rw [smul_apply, norm_smul, Complex.norm_real, norm_norm, mul_assoc]
            exact key a b
      rwa [norm_smul, Complex.norm_real, norm_norm, ← opNorm_def] at h
    have hf : ‖(‖g‖ₒₚ : ℂ) • (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ ≤
        ‖f.minTensorProduct g‖ₒₚ :=
      ContinuousLinearMap.opNorm_le_bound _ (opNorm_nonneg _) fun a => by
        rw [smul_apply, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (opNorm_nonneg g), mul_comm]
        exact hg a
    rwa [norm_smul, Complex.norm_real, Real.norm_of_nonneg (opNorm_nonneg g), ← opNorm_def,
      mul_comm] at hf

end PositiveLinearMap

namespace State

variable {A : Type u} {B : Type v}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The **product state** `ω ⊗ φ` on the minimal tensor product `A ⊗ₘᵢₙ B` of states `ω` of `A` and
`φ` of `B`: the product functional `PositiveLinearMap.minTensorProduct` of `ω` and `φ`, which has
norm one (`PositiveLinearMap.opNorm_minTensorProduct`). It is the state with
`(ω ⊗ φ)(a ⊗ b) = ω(a) φ(b)` (`State.minTensorProduct_of_tmul`, `State.eq_minTensorProduct`). -/
noncomputable def minTensorProduct (ω : State A) (φ : State B) : State (A ⊗ₘᵢₙ B) :=
  ofContinuousLinearMap
    (PositiveContinuousLinearMap.ofClass
      ((PositiveLinearMap.ofClass ω).minTensorProduct (PositiveLinearMap.ofClass φ)))
    (fun _ h => map_nonneg
      ((PositiveLinearMap.ofClass ω).minTensorProduct (PositiveLinearMap.ofClass φ)) h) (by
    rw [← PositiveLinearMap.opNorm_def, PositiveLinearMap.opNorm_minTensorProduct,
      ω.opNorm_ofClass_eq_one, φ.opNorm_ofClass_eq_one, one_mul])

/-- The positive functional underlying a product state is the product of the underlying positive
functionals. -/
@[simp] lemma ofClass_minTensorProduct (ω : State A) (φ : State B) :
    PositiveLinearMap.ofClass (ω.minTensorProduct φ) =
      (PositiveLinearMap.ofClass ω).minTensorProduct (PositiveLinearMap.ofClass φ) :=
  rfl

/-- **The product state on pure tensors**: `(ω ⊗ φ)(a ⊗ b) = ω(a) φ(b)`. -/
@[simp] lemma minTensorProduct_of_tmul (ω : State A) (φ : State B) (a : A) (b : B) :
    ω.minTensorProduct φ (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) = ω a * φ b :=
  PositiveLinearMap.minTensorProduct_of_tmul (PositiveLinearMap.ofClass ω)
    (PositiveLinearMap.ofClass φ) a b

/-- The product state `ω ⊗ φ` is the only state of `A ⊗ₘᵢₙ B` with the values `ω(a) φ(b)` on the
pure tensors. -/
lemma eq_minTensorProduct {ω : State A} {φ : State B} {ψ : State (A ⊗ₘᵢₙ B)}
    (h : ∀ (a : A) (b : B), ψ (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) = ω a * φ b) :
    ψ = ω.minTensorProduct φ :=
  MinTensorProduct.ext_of_tmul ψ.continuous (ω.minTensorProduct φ).continuous fun a b => by
    rw [h, minTensorProduct_of_tmul]

end State

/-! ### Marginals -/

namespace State

open Filter Topology
open scoped PositiveLinearMap

section Restriction

variable {A : Type u} {D : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- The restriction `ω ∘ j` of a state `ω` of `D` along a `⋆`-homomorphism `j : A → D` has norm one
when `j(e) y → y` along the approximate unit of `A` for `y` in a dense subset of `D`: by the
Cauchy–Schwarz inequality, `|ω(j(e) y)|² ≤ ω(j(e²)) ω(y⋆ y) ≤ ‖ω ∘ j‖ ‖y‖²` for `0 ≤ e` with
`‖e‖ ≤ 1`, so `|ω(y)|² ≤ ‖ω ∘ j‖ ‖y‖²` for every `y`. -/
private lemma opNorm_comp_eq_one (ω : State D) (j : A →⋆ₙₐ[ℂ] D) {ι : Type*} {g : ι → D}
    (hg : DenseRange g)
    (hj : ∀ x, Tendsto (fun e => j e * g x) (CStarAlgebra.approximateUnit A) (𝓝 (g x))) :
    ‖(PositiveLinearMap.ofClass ω).comp (PositiveLinearMap.ofClass j)‖ₒₚ = 1 := by
  set f := (PositiveLinearMap.ofClass ω).comp (PositiveLinearMap.ofClass j)
  have hc : 0 ≤ ‖f‖ₒₚ := PositiveLinearMap.opNorm_nonneg f
  refine le_antisymm ?_ ?_
  · rw [PositiveLinearMap.opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
    rw [one_mul]
    exact (ω.norm_apply_le (j a)).trans (NonUnitalStarAlgHom.norm_apply_le j a)
  · have hl := CStarAlgebra.increasingApproximateUnit A
    have key (y : D) : ‖ω y‖ ^ 2 ≤ ‖f‖ₒₚ * ‖y‖ ^ 2 := by
      refine hg.induction_on y (isClosed_le (ω.continuous.norm.pow 2)
        (continuous_const.mul (continuous_norm.pow 2))) fun x => ?_
      have hlim : Tendsto (fun e => ‖ω (j e * g x)‖ ^ 2) (CStarAlgebra.approximateUnit A)
          (𝓝 (‖ω (g x)‖ ^ 2)) :=
        (((ω.continuous.tendsto (g x)).comp (hj x)).norm).pow 2
      refine le_of_tendsto hlim ?_
      filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
      have hs : star (j e) = j e := by rw [← map_star, he₀.isSelfAdjoint.star_eq]
      have hcs := PositiveLinearMap.norm_map_star_mul_sq_le (PositiveLinearMap.ofClass ω) (j e) (g x)
      rw [hs, ← map_mul] at hcs
      have h₁ : ‖ω (j (e * e))‖ ≤ ‖f‖ₒₚ := calc
        ‖ω (j (e * e))‖ = ‖f (e * e)‖ := rfl
        _ ≤ ‖f‖ₒₚ * ‖e * e‖ := PositiveLinearMap.norm_apply_le_opNorm_mul f (e * e)
        _ ≤ ‖f‖ₒₚ * 1 := by
          gcongr
          exact (norm_mul_le e e).trans ((mul_le_mul he₁ he₁ (norm_nonneg e) zero_le_one).trans_eq (one_mul 1))
        _ = ‖f‖ₒₚ := mul_one _
      have h₂ : ‖ω (star (g x) * g x)‖ ≤ ‖g x‖ ^ 2 := by
        rw [sq, ← CStarRing.norm_star_mul_self]
        exact ω.norm_apply_le _
      exact hcs.trans (mul_le_mul h₁ h₂ (norm_nonneg _) hc)
    have hω : (1 : ℝ) ≤ √‖f‖ₒₚ := by
      rw [← ω.norm_eq_one]
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
      rw [mul_pow, Real.sq_sqrt hc]
      exact key y
    simpa [Real.sq_sqrt hc] using pow_le_pow_left₀ zero_le_one hω 2

end Restriction

section Left

variable {A : Type u} {B : Type v}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
/-- Along the approximate unit of `A`, `(e ⊗ 1) x → x` for `x` in the algebraic tensor product: on a
pure tensor, `(e ⊗ 1)(a ⊗ b) = (e a) ⊗ b → a ⊗ b`. -/
private lemma tendsto_inl_mul (x : A ⊗[ℂ] B) :
    Tendsto (fun e => MinTensorProduct.inl A B e * MinTensorProduct.of A B x)
      (CStarAlgebra.approximateUnit A) (𝓝 (MinTensorProduct.of A B x)) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    have hcont : Continuous fun a' : A => MinTensorProduct.of A B (a' ⊗ₜ[ℂ] b) :=
      AddMonoidHomClass.continuous_of_bound
        ((MinTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) ∘ₗ (TensorProduct.mk ℂ A B).flip b) ‖b‖
        fun a' =>
          ((MinTensorProduct.norm_of_tmul a' b).trans (mul_comm _ _)).le
    refine ((hcont.tendsto a).comp (hl.tendsto_mul_right a)).congr fun e => ?_
    rw [Function.comp_apply, MinTensorProduct.inl_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simpa only [map_add, mul_add] using hx.add hy

/-- The **marginal** `ω_A = ω(· ⊗ 1)` on the first factor of a state `ω` of `A ⊗ₘᵢₙ B`, for unital
`B`: the restriction of `ω` along `a ↦ a ⊗ 1` (`MinTensorProduct.inl`). It is a state also for
non-unital `A`, `e ⊗ 1` running through an approximate unit of `A ⊗ₘᵢₙ B` as `e` runs through one
of `A`. -/
noncomputable def marginalLeft (ω : State (A ⊗ₘᵢₙ B)) : State A :=
  ofContinuousLinearMap
    (PositiveContinuousLinearMap.ofClass
      ((PositiveLinearMap.ofClass ω).comp (PositiveLinearMap.ofClass (MinTensorProduct.inl A B))))
    (fun _ h => map_nonneg
      ((PositiveLinearMap.ofClass ω).comp (PositiveLinearMap.ofClass (MinTensorProduct.inl A B))) h)
    (by
      rw [← PositiveLinearMap.opNorm_def]
      exact opNorm_comp_eq_one ω _ MinTensorProduct.denseRange_of tendsto_inl_mul)

omit [PartialOrder B] [StarOrderedRing B] in
/-- The marginal on the first factor evaluates `ω` on `a ⊗ 1`. -/
@[simp] lemma marginalLeft_apply (ω : State (A ⊗ₘᵢₙ B)) (a : A) :
    ω.marginalLeft a = ω (MinTensorProduct.of A B (a ⊗ₜ[ℂ] 1)) :=
  rfl

/-- The marginal of the product state `ω ⊗ φ` on the first factor is `ω`. -/
@[simp] lemma marginalLeft_minTensorProduct (ω : State A) (φ : State B) :
    (ω.minTensorProduct φ).marginalLeft = ω := by
  ext a
  rw [marginalLeft_apply, minTensorProduct_of_tmul, φ.apply_one, mul_one]

end Left

section Right

variable {A : Type u} {B : Type v}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Along the approximate unit of `B`, `(1 ⊗ e) x → x` for `x` in the algebraic tensor product: on a
pure tensor, `(1 ⊗ e)(a ⊗ b) = a ⊗ (e b) → a ⊗ b`. -/
private lemma tendsto_inr_mul (x : A ⊗[ℂ] B) :
    Tendsto (fun e => MinTensorProduct.inr A B e * MinTensorProduct.of A B x)
      (CStarAlgebra.approximateUnit B) (𝓝 (MinTensorProduct.of A B x)) := by
  have hl := CStarAlgebra.increasingApproximateUnit B
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    have hcont : Continuous fun b' : B => MinTensorProduct.of A B (a ⊗ₜ[ℂ] b') :=
      AddMonoidHomClass.continuous_of_bound
        ((MinTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) ∘ₗ TensorProduct.mk ℂ A B a) ‖a‖
        fun b' =>
          (MinTensorProduct.norm_of_tmul a b').le
    refine ((hcont.tendsto b).comp (hl.tendsto_mul_right b)).congr fun e => ?_
    rw [Function.comp_apply, MinTensorProduct.inr_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simpa only [map_add, mul_add] using hx.add hy

/-- The **marginal** `ω_B = ω(1 ⊗ ·)` on the second factor of a state `ω` of `A ⊗ₘᵢₙ B`, for unital
`A`: the restriction of `ω` along `b ↦ 1 ⊗ b` (`MinTensorProduct.inr`). It is a state also for
non-unital `B`. -/
noncomputable def marginalRight (ω : State (A ⊗ₘᵢₙ B)) : State B :=
  ofContinuousLinearMap
    (PositiveContinuousLinearMap.ofClass
      ((PositiveLinearMap.ofClass ω).comp (PositiveLinearMap.ofClass (MinTensorProduct.inr A B))))
    (fun _ h => map_nonneg
      ((PositiveLinearMap.ofClass ω).comp (PositiveLinearMap.ofClass (MinTensorProduct.inr A B))) h)
    (by
      rw [← PositiveLinearMap.opNorm_def]
      exact opNorm_comp_eq_one ω _ MinTensorProduct.denseRange_of tendsto_inr_mul)

omit [PartialOrder A] [StarOrderedRing A] in
/-- The marginal on the second factor evaluates `ω` on `1 ⊗ b`. -/
@[simp] lemma marginalRight_apply (ω : State (A ⊗ₘᵢₙ B)) (b : B) :
    ω.marginalRight b = ω (MinTensorProduct.of A B (1 ⊗ₜ[ℂ] b)) :=
  rfl

/-- The marginal of the product state `ω ⊗ φ` on the second factor is `φ`. -/
@[simp] lemma marginalRight_minTensorProduct (ω : State A) (φ : State B) :
    (ω.minTensorProduct φ).marginalRight = φ := by
  ext b
  rw [marginalRight_apply, minTensorProduct_of_tmul, ω.apply_one, one_mul]

end Right

variable {A : Type u} {B : Type v}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **A state is a product state iff it factorizes over the pure tensors through its marginals**:
`ω = ω_A ⊗ ω_B` iff `ω(a ⊗ b) = ω_A(a) ω_B(b)` for all `a` and `b`. -/
theorem eq_minTensorProduct_marginal_iff {ω : State (A ⊗ₘᵢₙ B)} :
    ω = ω.marginalLeft.minTensorProduct ω.marginalRight ↔
      ∀ (a : A) (b : B), ω (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) =
        ω (MinTensorProduct.of A B (a ⊗ₜ[ℂ] 1)) * ω (MinTensorProduct.of A B (1 ⊗ₜ[ℂ] b)) :=
  ⟨fun h a b => by
    rw [← marginalLeft_apply, ← marginalRight_apply, ← minTensorProduct_of_tmul, ← h],
    fun h => eq_minTensorProduct h⟩

/-- A state of `A ⊗ₘᵢₙ B` is a product state iff it is the product of its marginals. -/
theorem exists_eq_minTensorProduct_iff {ω : State (A ⊗ₘᵢₙ B)} :
    (∃ (ω₁ : State A) (ω₂ : State B), ω = ω₁.minTensorProduct ω₂) ↔
      ω = ω.marginalLeft.minTensorProduct ω.marginalRight :=
  ⟨by
    rintro ⟨ω₁, ω₂, rfl⟩
    rw [marginalLeft_minTensorProduct, marginalRight_minTensorProduct], fun h => ⟨_, _, h⟩⟩

end State
