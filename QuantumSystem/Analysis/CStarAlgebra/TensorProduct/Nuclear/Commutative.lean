/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Minimal.Slice
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Nuclear
public import QuantumSystem.ForMathlib.Topology.PartitionOfUnity.Approximation

/-!
# Commutative C⋆-algebras are nuclear

Every `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B`, for a commutative C⋆-algebra `A`, into a C⋆-algebra is
bounded by the norm of the minimal tensor product. The proof uses no maximal tensor product:

1. *The key inequality.* For positive `h j ∈ A` with `h j * ∑ h ≤ h j`,
   `‖Φ (∑ h j ⊗ c j)‖ ≤ max ‖c j‖`. With `y = ∑ h j ⊗ c j`, the element `∑ h j ⊗ c j⋆ c j - y⋆ y` is
   a sum of elements `p ⊗ d⋆ d` with `p ≥ 0`, so `‖Φ y‖² ≤ ‖Φ (∑ h j ⊗ c j⋆ c j)‖`; iterating raises
   the exponent to `2 ^ m`, and the cross norm bound gives the `2 ^ m`-th root of a constant times
   `max ‖c j‖`.
2. *Approximation.* Through the Gelfand transform of the unitization, finitely many `aᵢ ∈ A` are
   approximated by `∑ χ j (aᵢ) • h j` for a partition of unity `h j` vanishing at the point at
   infinity and characters `χ j`; then `z = ∑ aᵢ ⊗ bᵢ` is close to `∑ h j ⊗ c j` with
   `c j = ∑ χ j (aᵢ) bᵢ`.
3. *Slices.* `‖c j‖`, the norm of the slice of `z` by `χ j`, is at most the norm of `z` in
   `A ⊗ₘᵢₙ B`.

## Main results

* `NonUnitalStarAlgHom.norm_apply_sum_tmul_le_of_mul_sum_le` — the key inequality.
* `CommCStarAlgebra.exists_approx_partitionOfUnity` — the approximation along a partition of unity.
* `MinTensorProduct.norm_lid_rTensor_nonUnitalStarAlgHom_le` — slices by `⋆`-homomorphisms into `ℂ` are
  contractive for the minimal norm, a case of `MinTensorProduct.norm_lid_rTensor_le`.
* `CStarAlgebra.IsNuclear.of_commutative` — commutative C⋆-algebras are nuclear.
-/

@[expose] public section

open scoped TensorProduct MinTensorProduct ComplexOrder CStarAlgebra

open Filter Topology

universe u v w

/-! ### Sums of tensors along a partition of unity -/

namespace TensorProduct

variable {A B C : Type*} [NonUnitalCommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A `⋆`-homomorphism of `A ⊗[ℂ] B` sends `p ⊗ d⋆ d` to a positive element when `p` is positive:
`p` is a sum of elements `s⋆ s`, and `s⋆ s ⊗ d⋆ d = (s ⊗ d)⋆ (s ⊗ d)`. -/
lemma apply_tmul_star_mul_self_nonneg (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) {p : A} (hp : 0 ≤ p) (d : B) :
    0 ≤ Φ (p ⊗ₜ[ℂ] (star d * d)) := by
  rw [StarOrderedRing.nonneg_iff] at hp
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [← Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.star_tmul, map_mul, map_star]
    exact star_mul_self_nonneg _
  | zero => rw [TensorProduct.zero_tmul, map_zero]
  | add x y _ _ hx hy => rw [TensorProduct.add_tmul, map_add]; exact add_nonneg hx hy

variable {ι : Type*}

omit [PartialOrder A] [StarOrderedRing A] in
/-- The identity behind `TensorProduct.norm_apply_sum_tmul_sq_le`: for self-adjoint `h j` in a
commutative `A` and `y = ∑ h j ⊗ c j`,
`∑ h j ⊗ c j⋆ c j - y⋆ y = ½ ∑ h j h k ⊗ (c j - c k)⋆ (c j - c k) + ∑ (h j - h j ∑ h) ⊗ c j⋆ c j`. -/
lemma sum_tmul_star_mul_self_sub_star_mul_self (s : Finset ι) (h : ι → A)
    (hh : ∀ j, IsSelfAdjoint (h j)) (c : ι → B) :
    ∑ j ∈ s, h j ⊗ₜ[ℂ] (star (c j) * c j) -
        star (∑ j ∈ s, h j ⊗ₜ[ℂ] c j) * ∑ j ∈ s, h j ⊗ₜ[ℂ] c j =
      (2⁻¹ : ℂ) • ∑ j ∈ s, ∑ k ∈ s, (h j * h k) ⊗ₜ[ℂ] (star (c j - c k) * (c j - c k)) +
        ∑ j ∈ s, (h j - h j * ∑ k ∈ s, h k) ⊗ₜ[ℂ] (star (c j) * c j) := by
  set P := ∑ j ∈ s, ∑ k ∈ s, (h j * h k) ⊗ₜ[ℂ] (star (c j) * c j)
  set Q := ∑ j ∈ s, ∑ k ∈ s, (h j * h k) ⊗ₜ[ℂ] (star (c j) * c k)
  have hQ : star (∑ j ∈ s, h j ⊗ₜ[ℂ] c j) * ∑ j ∈ s, h j ⊗ₜ[ℂ] c j = Q := by
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.star_tmul, (hh j).star_eq, Algebra.TensorProduct.tmul_mul_tmul]
  have hP : ∑ j ∈ s, (h j * ∑ k ∈ s, h k) ⊗ₜ[ℂ] (star (c j) * c j) = P := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, TensorProduct.sum_tmul]
  have hP' : ∑ j ∈ s, ∑ k ∈ s, (h j * h k) ⊗ₜ[ℂ] (star (c k) * c k) = P := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hQ' : ∑ j ∈ s, ∑ k ∈ s, (h j * h k) ⊗ₜ[ℂ] (star (c k) * c j) = Q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hT : ∑ j ∈ s, ∑ k ∈ s, (h j * h k) ⊗ₜ[ℂ] (star (c j - c k) * (c j - c k)) =
      P + P - Q - Q := by
    have he (j k : ι) : (h j * h k) ⊗ₜ[ℂ] (star (c j - c k) * (c j - c k)) =
        (h j * h k) ⊗ₜ[ℂ] (star (c j) * c j) + (h j * h k) ⊗ₜ[ℂ] (star (c k) * c k) -
          (h j * h k) ⊗ₜ[ℂ] (star (c j) * c k) - (h j * h k) ⊗ₜ[ℂ] (star (c k) * c j) := by
      rw [star_sub, ← TensorProduct.tmul_add, ← TensorProduct.tmul_sub, ← TensorProduct.tmul_sub]
      congr 1
      noncomm_ring
    simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, hP', hQ']
    rfl
  have hw : ∑ j ∈ s, (h j - h j * ∑ k ∈ s, h k) ⊗ₜ[ℂ] (star (c j) * c j) =
      ∑ j ∈ s, h j ⊗ₜ[ℂ] (star (c j) * c j) - P := by
    rw [← hP, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => TensorProduct.sub_tmul _ _ _
  rw [hQ, hT, hw]
  module

omit [PartialOrder C] [StarOrderedRing C] in
/-- **One step of the key inequality.** For positive `h j` in a commutative C⋆-algebra with
`h j * ∑ h ≤ h j`, a `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra satisfies
`‖Φ (∑ h j ⊗ c j)‖² ≤ ‖Φ (∑ h j ⊗ c j⋆ c j)‖`: the difference of `Φ (∑ h j ⊗ c j⋆ c j)` and
`Φ(y)⋆ Φ(y)` is positive, by `TensorProduct.sum_tmul_star_mul_self_sub_star_mul_self`. -/
lemma norm_apply_sum_tmul_sq_le (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (s : Finset ι) (h : ι → A)
    (hh : ∀ j, 0 ≤ h j) (hsum : ∀ j ∈ s, h j * ∑ k ∈ s, h k ≤ h j) (c : ι → B) :
    ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] c j)‖ ^ 2 ≤ ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] (star (c j) * c j))‖ := by
  let := CStarAlgebra.spectralOrder C
  have := CStarAlgebra.spectralOrderedRing C
  set y := ∑ j ∈ s, h j ⊗ₜ[ℂ] c j
  set w := ∑ j ∈ s, h j ⊗ₜ[ℂ] (star (c j) * c j)
  have hdiff : 0 ≤ Φ w - star (Φ y) * Φ y := by
    rw [← map_star, ← map_mul, ← map_sub,
      sum_tmul_star_mul_self_sub_star_mul_self s h (fun j => IsSelfAdjoint.of_nonneg (hh j)) c,
      map_add, map_smul, map_sum, map_sum]
    refine add_nonneg ?_ (Finset.sum_nonneg fun j hj => ?_)
    · have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by norm_num
      rw [h2, Complex.coe_smul]
      refine smul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => ?_)
      rw [map_sum]
      exact Finset.sum_nonneg fun k _ => apply_tmul_star_mul_self_nonneg Φ
        (Commute.mul_nonneg (hh j) (hh k) (Commute.all _ _)) _
    · exact apply_tmul_star_mul_self_nonneg Φ (sub_nonneg.2 (hsum j hj)) _
  rw [sq, ← CStarRing.norm_star_mul_self]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_nonneg.1 hdiff) (star_mul_self_nonneg _)

/-- If `a ^ 2 ^ m ≤ K * M ^ 2 ^ m` for every `m`, then `a ≤ M`. -/
private lemma le_of_forall_pow_two_pow_le {a M K : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (h : ∀ m : ℕ, a ^ 2 ^ m ≤ K * M ^ 2 ^ m) : a ≤ M := by
  by_contra hlt
  push Not at hlt
  have ha0 : 0 < a := hM.trans_lt hlt
  have hr : M / a < 1 := (div_lt_one ha0).2 hlt
  have hr0 : 0 ≤ M / a := div_nonneg hM ha
  have ht : Tendsto (fun m : ℕ => K * (M / a) ^ 2 ^ m) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).comp
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℕ)))).const_mul K
  have h1 (m : ℕ) : 1 ≤ K * (M / a) ^ 2 ^ m := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos ha0 _), one_mul]
    exact h m
  exact absurd (ge_of_tendsto' ht h1) (by norm_num)

end TensorProduct

namespace NonUnitalStarAlgHom

variable {A B C : Type*} [NonUnitalCommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C] {ι : Type*}

/-- **The key inequality.** For positive `h j` in a commutative C⋆-algebra with `h j * ∑ h ≤ h j`,
every `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra satisfies
`‖Φ (∑ h j ⊗ c j)‖ ≤ M` when `‖c j‖ ≤ M` for every `j`. Iterating
`TensorProduct.norm_apply_sum_tmul_sq_le` bounds `‖Φ (∑ h j ⊗ c j)‖ ^ 2 ^ m` by
`(∑ ‖h j‖) * M ^ 2 ^ m`, and the `2 ^ m`-th root tends to `M`. -/
theorem norm_apply_sum_tmul_le_of_mul_sum_le (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (s : Finset ι) (h : ι → A)
    (hh : ∀ j, 0 ≤ h j) (hsum : ∀ j ∈ s, h j * ∑ k ∈ s, h k ≤ h j) (c : ι → B) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ j ∈ s, ‖c j‖ ≤ M) : ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] c j)‖ ≤ M := by
  let e : ℕ → B → B := fun m => (fun b => star b * b)^[m]
  have he (m : ℕ) (b : B) : ‖e m b‖ = ‖b‖ ^ 2 ^ m := by
    induction m with
    | zero => simp [e]
    | succ m ih =>
      simp only [e, Function.iterate_succ_apply'] at ih ⊢
      rw [CStarRing.norm_star_mul_self, ih, pow_succ, pow_mul, sq]
  have hstep (m : ℕ) : ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] c j)‖ ^ 2 ^ m ≤
      ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] e m (c j))‖ := by
    induction m with
    | zero => simp [e]
    | succ m ih =>
      calc ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] c j)‖ ^ 2 ^ (m + 1)
          = (‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] c j)‖ ^ 2 ^ m) ^ 2 := by rw [pow_succ, pow_mul]
        _ ≤ ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] e m (c j))‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) ih 2
        _ ≤ ‖Φ (∑ j ∈ s, h j ⊗ₜ[ℂ] e (m + 1) (c j))‖ := by
          simp only [e, Function.iterate_succ_apply']
          exact TensorProduct.norm_apply_sum_tmul_sq_le Φ s h hh hsum _
  refine TensorProduct.le_of_forall_pow_two_pow_le (K := ∑ j ∈ s, ‖h j‖) (norm_nonneg _) hM fun m =>
    (hstep m).trans ?_
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (NonUnitalStarAlgHom.norm_apply_tmul_le Φ _ _).trans ?_
  rw [he]
  gcongr
  exact hc j hj

end NonUnitalStarAlgHom

/-! ### Approximation along a partition of unity -/

namespace CommCStarAlgebra

open scoped ComplexOrder in
/-- **In a commutative C⋆-algebra, finitely many elements are approximated along a partition of
unity**: for `ε > 0` there are positive `h j` with `h j * ∑ h ≤ h j` and `⋆`-homomorphisms
`χ j : A → ℂ` such that `‖f k - ∑ j, χ j (f k) • h j‖ ≤ ε` for every `k`. Through the Gelfand
transform of the unitization, the `h j` are a partition of unity on the character space that
vanishes at the character `(a, λ) ↦ λ`, and the `χ j` are evaluations at points of it. -/
theorem exists_approx_partitionOfUnity {A : Type*} [NonUnitalCommCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {K : Type*} [Finite K] (f : K → A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (h : Fin n → A) (χ : Fin n → A →⋆ₙₐ[ℂ] ℂ), (∀ j, 0 ≤ h j) ∧
      (∀ j, h j * ∑ k, h k ≤ h j) ∧ ∀ k, ‖f k - ∑ j, χ j (f k) • h j‖ ≤ ε := by
  set Γ := gelfandStarTransform (Unitization ℂ A)
  let x₀ : WeakDual.characterSpace ℂ (Unitization ℂ A) :=
    WeakDual.CharacterSpace.equivAlgHom.symm (Unitization.fstHom ℂ A)
  have hx₀ (a : Unitization ℂ A) : Γ a x₀ = a.fst := by
    rw [gelfandStarTransform_apply_apply, WeakDual.CharacterSpace.equivAlgHom_symm_coe,
      Unitization.fstHom_apply]
  obtain ⟨n, φ, x, hφ0, hφ1, hφx₀, happrox⟩ := ContinuousMap.exists_approx_partitionOfUnity
    (fun k => Γ (f k : Unitization ℂ A)) x₀ (fun k => by rw [hx₀, Unitization.fst_inr]) hε
  let φc : Fin n → C(WeakDual.characterSpace ℂ (Unitization ℂ A), ℂ) :=
    fun j => ⟨fun y => (φ j y : ℂ), by fun_prop⟩
  let h' : Fin n → Unitization ℂ A := fun j => Γ.symm (φc j)
  have hΓh' (j : Fin n) : Γ (h' j) = φc j := Γ.apply_symm_apply _
  have hinr (j : Fin n) : ((h' j).snd : Unitization ℂ A) = h' j := by
    refine Unitization.ext ?_ rfl
    rw [Unitization.fst_inr, ← hx₀, hΓh']
    simp [φc, hφx₀]
  let χ : Fin n → A →⋆ₙₐ[ℂ] ℂ := fun j =>
    ((ContinuousMap.evalStarAlgHom ℂ ℂ (x j)).comp Γ.toStarAlgHom).toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hχ (j : Fin n) (a : A) : χ j a = Γ (a : Unitization ℂ A) (x j) := rfl
  have hcoe_sum (a : Fin n → A) :
      ((∑ j, a j : A) : Unitization ℂ A) = ∑ j, (a j : Unitization ℂ A) :=
    map_sum (Unitization.inrNonUnitalStarAlgHom ℂ A) a Finset.univ
  -- positivity is read through `Γ`, as pointwise positivity of continuous functions
  have hpos {u : Unitization ℂ A} (hu : ∀ y, 0 ≤ Γ u y) : 0 ≤ u := by
    have h0 : 0 ≤ Γ u := ContinuousMap.le_def.2 fun y => by simpa using hu y
    simpa using map_nonneg Γ.symm h0
  refine ⟨n, fun j => (h' j).snd, χ, fun j => ?_, fun j => ?_, fun k => ?_⟩
  · rw [← Unitization.inr_nonneg_iff, hinr]
    refine hpos fun y => ?_
    rw [hΓh']
    exact Complex.zero_le_real.2 (hφ0 j y)
  · beta_reduce
    rw [← sub_nonneg, ← Unitization.inr_nonneg_iff, Unitization.inr_sub, Unitization.inr_mul,
      hcoe_sum]
    simp only [hinr]
    refine hpos fun y => ?_
    rw [map_sub, map_mul, map_sum, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
      ContinuousMap.sum_apply]
    simp only [hΓh', φc, ContinuousMap.coe_mk]
    have h1 : 0 ≤ φ j y - φ j y * ∑ k, φ k y :=
      sub_nonneg.2 (mul_le_of_le_one_right (hφ0 j y) (hφ1 y))
    exact_mod_cast Complex.zero_le_real.2 h1
  · rw [← Unitization.norm_inr (𝕜 := ℂ), ← StarAlgEquiv.norm_map Γ,
      ContinuousMap.norm_le _ hε.le]
    intro y
    beta_reduce
    rw [Unitization.inr_sub, hcoe_sum, map_sub, map_sum, ContinuousMap.sub_apply,
      ContinuousMap.sum_apply]
    refine le_of_eq_of_le ?_ (happrox k y)
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Unitization.inr_smul ℂ (χ j (f k)) ((h' j).snd), map_smul, ContinuousMap.smul_apply,
      hinr, hΓh', hχ, smul_eq_mul, Complex.real_smul, mul_comm]
    rfl

end CommCStarAlgebra

/-! ### Slices by characters -/

namespace MinTensorProduct

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The **slice** `a ⊗ b ↦ χ(a) b` of `A ⊗[ℂ] B` by a `⋆`-homomorphism `χ : A → ℂ` is bounded by
the norm of the minimal tensor product: `χ` is a bounded functional of norm at most `1`
(`MinTensorProduct.norm_lid_rTensor_le`). -/
lemma norm_lid_rTensor_nonUnitalStarAlgHom_le (χ : A →⋆ₙₐ[ℂ] ℂ) (z : A ⊗[ℂ] B) :
    ‖TensorProduct.lid ℂ B ((χ : A →ₗ[ℂ] ℂ).rTensor B z)‖ ≤ ‖of A B z‖ := by
  have hχ (a : A) : ‖(χ : A →ₗ[ℂ] ℂ) a‖ ≤ 1 * ‖a‖ := by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le χ a
  exact (norm_lid_rTensor_le ((χ : A →ₗ[ℂ] ℂ).mkContinuous 1 hχ) z).trans
    (mul_le_of_le_one_left (norm_nonneg _) (LinearMap.mkContinuous_norm_le _ zero_le_one _))

end MinTensorProduct

/-! ### Nuclearity -/

namespace CStarAlgebra.IsNuclear

/-- **Commutative C⋆-algebras are nuclear.** For `z = ∑ aᵢ ⊗ bᵢ` and `ε > 0`, approximate the `aᵢ`
along a partition of unity `h j` with characters `χ j` (`CommCStarAlgebra.exists_approx_partitionOfUnity`):
`z` is close to `∑ h j ⊗ c j` with `c j = ∑ χ j (aᵢ) bᵢ`, whose image under any `⋆`-homomorphism
has norm at most `max ‖c j‖` (`NonUnitalStarAlgHom.norm_apply_sum_tmul_le_of_mul_sum_le`), and each
`‖c j‖` is at most the norm of `z` in `A ⊗ₘᵢₙ B`
(`MinTensorProduct.norm_lid_rTensor_nonUnitalStarAlgHom_le`). -/
instance of_commutative {A : Type u} [NonUnitalCommCStarAlgebra A] : IsNuclear.{v, w} A := by
  refine ⟨fun B _ C _ Φ z => ?_⟩
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  set L := ∑ i ∈ S, ‖i.2‖
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (L + 1) := div_pos hε (by positivity)
  obtain ⟨n, h, χ, hh, hsum, happrox⟩ :=
    CommCStarAlgebra.exists_approx_partitionOfUnity (fun i : S => i.1.1) hδ
  set z := ∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2
  let c : Fin n → B := fun j => ∑ i ∈ S, χ j i.1 • i.2
  have hc (j : Fin n) : ‖c j‖ ≤ ‖MinTensorProduct.of A B z‖ := by
    refine le_of_eq_of_le ?_ (MinTensorProduct.norm_lid_rTensor_nonUnitalStarAlgHom_le (χ j) z)
    simp [c, z, map_sum]
  have hdiff : z - ∑ j, h j ⊗ₜ[ℂ] c j = ∑ i ∈ S, (i.1 - ∑ j, χ j i.1 • h j) ⊗ₜ[ℂ] i.2 := by
    simp only [c, z, TensorProduct.tmul_sum, TensorProduct.sub_tmul, Finset.sum_sub_distrib,
      TensorProduct.sum_tmul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
    rw [Finset.sum_comm]
  have hmain : ‖Φ (∑ j, h j ⊗ₜ[ℂ] c j)‖ ≤ ‖MinTensorProduct.of A B z‖ :=
    NonUnitalStarAlgHom.norm_apply_sum_tmul_le_of_mul_sum_le Φ Finset.univ h hh
      (fun j _ => hsum j) c (norm_nonneg _) fun j _ => hc j
  have herr : ‖Φ (z - ∑ j, h j ⊗ₜ[ℂ] c j)‖ ≤ ε := by
    rw [hdiff, map_sum]
    calc ‖∑ i ∈ S, Φ ((i.1 - ∑ j, χ j i.1 • h j) ⊗ₜ[ℂ] i.2)‖
        ≤ ∑ i ∈ S, ε / (L + 1) * ‖i.2‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          refine (NonUnitalStarAlgHom.norm_apply_tmul_le Φ _ _).trans ?_
          gcongr
          exact happrox ⟨i, hi⟩
      _ = ε / (L + 1) * L := by rw [Finset.mul_sum]
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [Finset.sum_nonneg fun i (_ : i ∈ S) => norm_nonneg i.2]
  calc ‖Φ z‖ = ‖Φ (∑ j, h j ⊗ₜ[ℂ] c j) + Φ (z - ∑ j, h j ⊗ₜ[ℂ] c j)‖ := by
        rw [← map_add, add_sub_cancel]
    _ ≤ ‖Φ (∑ j, h j ⊗ₜ[ℂ] c j)‖ + ‖Φ (z - ∑ j, h j ⊗ₜ[ℂ] c j)‖ := norm_add_le _ _
    _ ≤ ‖MinTensorProduct.of A B z‖ + ε := add_le_add hmain herr

end CStarAlgebra.IsNuclear
