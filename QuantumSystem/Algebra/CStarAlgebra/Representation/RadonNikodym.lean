/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Radon–Nikodym theorem for functionals dominated by a vector functional

Let `ρ : A → B(K)` be a representation of a unital C⋆-algebra, `ζ ∈ K`, and `f` a positive
functional on `A` dominated by the vector functional of `ζ`: `f(a⋆a) ≤ ‖ρ(a) ζ‖²` for all `a`.
Then there is `T` commuting with `ρ(A)` with `0 ≤ T ≤ 1` and `f(a) = ⟪T ζ, ρ(a) ζ⟫`
(Sakai, *C\*-algebras and W\*-algebras*, 1.24.4; Bratteli–Robinson, *Operator Algebras and
Quantum Statistical Mechanics 1*, Thm. 2.3.19); with `R = √T`, `f = ω_{R ζ}` is itself a vector
functional. The von Neumann algebra form (`T ∈ N′`) is
`QuantumSystem.Algebra.VonNeumannAlgebra.RadonNikodym`.

The proof goes through the GNS representation `π_f` of `f` on `GNS(f)` (Mathlib's
`PositiveLinearMap.GNS`): the domination makes `ρ(a) ζ ↦ [a]_f` a contraction from `[ρ(A) ζ]`,
which extends by `0` on `[ρ(A) ζ]ᗮ` to `W : K → GNS(f)` with `W ρ(a) = π_f(a) W`, and `T = W†W`.

The statement is for a *unital* `⋆`-homomorphism `ρ : A →⋆ₐ[ℂ] B(K)` into the operators of a
given Hilbert space `K`, not for a bundled `CStarRep A`: the proof uses `ρ 1 = 1`, which a
non-unital `CStarRep` does not provide, and the von Neumann algebra application needs `K` to be
the fixed space on which `N` acts. Stating it for an abstract `A` rather than for the subalgebra
`↥N` directly also means every GNS object is elaborated through the single C⋆-algebra structure
of `A`, whereas for `↥N` the functional's type and the GNS space would be built through different
instance paths on the subtype.

## Main results

* `CStarAlgebra.exists_commute_of_apply_star_mul_self_le` — **Radon–Nikodym** for a
  representation: `f(a) = ⟪T ζ, ρ(a) ζ⟫` with `T` commuting with `ρ(A)`, `0 ≤ T ≤ 1`.
* `CStarAlgebra.exists_commute_inner_eq_of_apply_star_mul_self_le` — the vector form
  `f = ω_{R ζ}` with `0 ≤ R` commuting with `ρ(A)`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace (cyclicSubspace cyclicSubspace_le)
open ContinuousLinearMap PositiveLinearMap

namespace CStarAlgebra

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {A : Type*} [CStarAlgebra A] (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ζ : K)

/-- `[ρ(A) ζ]`, the cyclic subspace of `ζ` under the representation. -/
noncomputable abbrev cyclicRange : Submodule ℂ K := (cyclicSubspace (Set.range ρ) ζ).toSubmodule

/-- `a ↦ ρ(a) ζ`, as a linear map into `[ρ(A) ζ]`. -/
noncomputable def cyclicApplyₗ : A →ₗ[ℂ] cyclicRange ρ ζ where
  toFun a := ⟨ρ a ζ, InnerProductSpace.apply_mem_cyclicSubspace ζ ⟨a, rfl⟩⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

variable {ρ ζ}

/-- The orbit `ρ(A) ζ` is dense in `[ρ(A) ζ]`. -/
lemma denseRange_cyclicApplyₗ : DenseRange (cyclicApplyₗ ρ ζ) := by
  set L : A →ₗ[ℂ] K := (ContinuousLinearMap.apply ℂ K ζ).toLinearMap ∘ₗ ρ.toLinearMap
  have hle : cyclicSubspace (Set.range ρ) ζ ≤ (LinearMap.range L).closure :=
    cyclicSubspace_le fun _ ⟨a, ha⟩ =>
      Submodule.le_topologicalClosure _ ⟨a, by rw [← ha]; rfl⟩
  rw [DenseRange, Subtype.dense_iff]
  intro v hv
  have hv' : v ∈ closure (LinearMap.range L : Set K) :=
    (Submodule.topologicalClosure_coe _).subset (hle hv)
  refine closure_mono ?_ hv'
  rintro _ ⟨a, rfl⟩
  exact ⟨_, ⟨a, rfl⟩, rfl⟩

/-- `[ρ(A) ζ]` is invariant under `ρ(A)`. -/
lemma apply_mem_cyclicSubspace_range (a : A) {v : K} (hv : v ∈ cyclicRange ρ ζ) : ρ a v ∈ cyclicRange ρ ζ := by
  have hle : cyclicSubspace (Set.range ρ) ζ ≤
      ⟨(cyclicRange ρ ζ).comap (ρ a : K →ₗ[ℂ] K), (cyclicSubspace (Set.range ρ) ζ).isClosed.preimage
        (ρ a).continuous⟩ :=
    cyclicSubspace_le fun T ⟨b, hb⟩ => by
      subst hb
      change ρ a (ρ b ζ) ∈ cyclicRange ρ ζ
      rw [← mul_apply_eq_comp, ← map_mul]
      exact InnerProductSpace.apply_mem_cyclicSubspace ζ ⟨a * b, rfl⟩
  exact hle hv

/-- The projection onto `[ρ(A) ζ]` commutes with `ρ(A)`. -/
lemma commute_starProjection_cyclicSubspace (a : A) : Commute (ρ a) (cyclicRange ρ ζ).starProjection := by
  have hred : InnerProductSpace.IsReducing (Set.range ρ) (cyclicRange ρ ζ) := by
    rintro _ ⟨b, rfl⟩
    refine ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun v hv =>
      apply_mem_cyclicSubspace_range b hv,
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun v hv => ?_⟩
    change adjoint (ρ b) v ∈ cyclicRange ρ ζ
    rw [← star_eq_adjoint, ← map_star]
    exact apply_mem_cyclicSubspace_range (star b) hv
  exact InnerProductSpace.starProjection_mem_centralizer_of_isReducing _ _ hred (ρ a) ⟨a, rfl⟩

variable [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

/-- `a ↦ [a]_f`, from `A` into the GNS space of `f`. -/
noncomputable def toGNSₗ : A →ₗ[ℂ] f.GNS :=
  (UniformSpace.Completion.toComplL : f.PreGNS →L[ℂ] f.GNS).toLinearMap ∘ₗ f.toPreGNS.toLinearMap

/-- `toGNSₗ f a` is the class of `a` in the completion. -/
lemma toGNSₗ_apply (a : A) : toGNSₗ f a = ((f.toPreGNS a : f.PreGNS) : f.GNS) := rfl

/-- `π_f(a) [b]_f = [a b]_f`. -/
lemma gnsStarAlgHom_toGNSₗ (a b : A) : f.gnsStarAlgHom a (toGNSₗ f b) = toGNSₗ f (a * b) := by
  change f.gnsNonUnitalStarAlgHom a ((f.toPreGNS b : f.PreGNS) : f.GNS) = _
  rw [gnsNonUnitalStarAlgHom_apply_coe, leftMulMapPreGNS_apply]
  rfl

/-- `⟪[a]_f, [b]_f⟫ = f(a⋆b)`. -/
lemma inner_toGNSₗ (a b : A) : ⟪toGNSₗ f a, toGNSₗ f b⟫_ℂ = f (star a * b) := by
  rw [toGNSₗ_apply, toGNSₗ_apply, UniformSpace.Completion.inner_coe, preGNS_inner_def]
  rfl

variable {f}

/-- Under domination, `‖[a]_f‖ ≤ ‖ρ(a) ζ‖`. -/
lemma norm_toGNSₗ_le (hf : ∀ a, ‖f (star a * a)‖ ≤ ‖ρ a ζ‖ ^ 2) (a : A) :
    ‖toGNSₗ f a‖ ≤ 1 * ‖cyclicApplyₗ ρ ζ a‖ := by
  rw [one_mul, toGNSₗ_apply, UniformSpace.Completion.norm_coe, preGNS_norm_def']
  calc √‖f (star (f.ofPreGNS (f.toPreGNS a)) * f.ofPreGNS (f.toPreGNS a))‖
      = √‖f (star a * a)‖ := rfl
    _ ≤ √(‖ρ a ζ‖ ^ 2) := Real.sqrt_le_sqrt (hf a)
    _ = ‖cyclicApplyₗ ρ ζ a‖ := Real.sqrt_sq (norm_nonneg _)

variable (ρ ζ f) in
/-- The intertwiner `W : K → GNS(f)`: `ρ(a) ζ ↦ [a]_f` on `[ρ(A) ζ]`, `0` on `[ρ(A) ζ]ᗮ`. -/
noncomputable def gnsIntertwiner : K →L[ℂ] f.GNS :=
  (toGNSₗ f).extendOfNorm (cyclicApplyₗ ρ ζ) ∘L (cyclicRange ρ ζ).orthogonalProjectionOnto

/-- `W` factors through the projection onto `[ρ(A) ζ]`. -/
lemma gnsIntertwiner_starProjection (w : K) :
    gnsIntertwiner ρ ζ f w = gnsIntertwiner ρ ζ f ((cyclicRange ρ ζ).starProjection w) := by
  simp only [gnsIntertwiner, ContinuousLinearMap.comp_apply, Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

section Intertwiner

variable (hf : ∀ a, ‖f (star a * a)‖ ≤ ‖ρ a ζ‖ ^ 2)
include hf

/-- `W (ρ(a) ζ) = [a]_f`. -/
lemma gnsIntertwiner_apply (a : A) : gnsIntertwiner ρ ζ f (ρ a ζ) = toGNSₗ f a := by
  change (toGNSₗ f).extendOfNorm (cyclicApplyₗ ρ ζ)
    ((cyclicRange ρ ζ).orthogonalProjectionOnto (cyclicApplyₗ ρ ζ a : K)) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact LinearMap.extendOfNorm_eq (f := toGNSₗ f) (e := cyclicApplyₗ ρ ζ)
    denseRange_cyclicApplyₗ ⟨1, norm_toGNSₗ_le hf⟩ a

/-- `‖W‖ ≤ 1`. -/
lemma norm_gnsIntertwiner_le : ‖gnsIntertwiner ρ ζ f‖ ≤ 1 := by
  have h₁ : ‖(toGNSₗ f).extendOfNorm (cyclicApplyₗ ρ ζ)‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le (f := toGNSₗ f) (e := cyclicApplyₗ ρ ζ)
      denseRange_cyclicApplyₗ zero_le_one (norm_toGNSₗ_le hf)
  have h₂ : ‖(cyclicRange ρ ζ).orthogonalProjectionOnto‖ ≤ 1 := Submodule.orthogonalProjectionOnto_norm_le _
  calc ‖gnsIntertwiner ρ ζ f‖
      ≤ ‖(toGNSₗ f).extendOfNorm (cyclicApplyₗ ρ ζ)‖ * ‖(cyclicRange ρ ζ).orthogonalProjectionOnto‖ :=
        opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul h₁ h₂ (by positivity) zero_le_one
    _ = 1 := one_mul 1

/-- **Intertwining.** `W ρ(a) = π_f(a) W`. -/
lemma gnsIntertwiner_comp (a : A) :
    gnsIntertwiner ρ ζ f ∘L ρ a = f.gnsStarAlgHom a ∘L gnsIntertwiner ρ ζ f := by
  set W := gnsIntertwiner ρ ζ f
  set D : K →L[ℂ] f.GNS := W ∘L ρ a - f.gnsStarAlgHom a ∘L W
  have hle : cyclicSubspace (Set.range ρ) ζ ≤ ⟨LinearMap.ker (D : K →ₗ[ℂ] f.GNS), D.isClosed_ker⟩ :=
    cyclicSubspace_le fun T ⟨b, hb⟩ => by
      subst hb
      change W (ρ a (ρ b ζ)) - f.gnsStarAlgHom a (W (ρ b ζ)) = 0
      rw [← mul_apply_eq_comp, ← map_mul, gnsIntertwiner_apply hf, gnsIntertwiner_apply hf,
        gnsStarAlgHom_toGNSₗ, sub_self]
  have hP := (commute_starProjection_cyclicSubspace (ρ := ρ) (ζ := ζ) a).eq
  ext w
  change W (ρ a w) = f.gnsStarAlgHom a (W w)
  have hD : D ((cyclicRange ρ ζ).starProjection w) = 0 := hle ((cyclicRange ρ ζ).starProjection_apply_mem w)
  change W (ρ a ((cyclicRange ρ ζ).starProjection w)) -
    f.gnsStarAlgHom a (W ((cyclicRange ρ ζ).starProjection w)) = 0 at hD
  rw [sub_eq_zero, ← gnsIntertwiner_starProjection] at hD
  rw [gnsIntertwiner_starProjection (w := ρ a w), ← mul_apply_eq_comp, ← hP, mul_apply_eq_comp, hD]

end Intertwiner

/-- **Radon–Nikodym theorem for a representation.** If a positive functional `f` on `A` satisfies
`f(a⋆a) ≤ ‖ρ(a) ζ‖²` for all `a`, there is `T` commuting with `ρ(A)`, with `0 ≤ T ≤ 1` and
`f(a) = ⟪T ζ, ρ(a) ζ⟫` for all `a`. -/
theorem exists_commute_of_apply_star_mul_self_le (hf : ∀ a, ‖f (star a * a)‖ ≤ ‖ρ a ζ‖ ^ 2) :
    ∃ T : K →L[ℂ] K, (∀ a, Commute T (ρ a)) ∧ 0 ≤ T ∧ T ≤ 1 ∧
      ∀ a, f a = ⟪T ζ, ρ a ζ⟫_ℂ := by
  set W := gnsIntertwiner ρ ζ f
  have h0 : 0 ≤ adjoint W ∘L W := nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self W)
  refine ⟨adjoint W ∘L W, fun a => ?_, h0, ?_, fun a => ?_⟩
  · have h₁ := gnsIntertwiner_comp hf a
    have h₂ := congrArg adjoint (gnsIntertwiner_comp hf (star a))
    simp only [adjoint_comp, map_star, star_eq_adjoint, adjoint_adjoint] at h₂
    change (adjoint W ∘L W) ∘L ρ a = ρ a ∘L (adjoint W ∘L W)
    rw [ContinuousLinearMap.comp_assoc, h₁, ← ContinuousLinearMap.comp_assoc, ← h₂,
      ContinuousLinearMap.comp_assoc]
  · refine (CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mp ?_
    rw [norm_adjoint_comp_self]
    have := norm_gnsIntertwiner_le hf
    nlinarith [norm_nonneg W]
  · rw [ContinuousLinearMap.comp_apply, adjoint_inner_left]
    have hζ : ζ = ρ 1 ζ := by rw [map_one, one_apply_eq_self]
    rw [hζ, gnsIntertwiner_apply hf, ← hζ, gnsIntertwiner_apply hf, inner_toGNSₗ, star_one,
      one_mul]

/-- **Radon–Nikodym for a representation, vector form.** If `f(a⋆a) ≤ ‖ρ(a) ζ‖²` for all `a`,
then `f` is the vector functional of `R ζ` for some positive `R` commuting with `ρ(A)`:
`f(a) = ⟪R ζ, ρ(a) (R ζ)⟫`. -/
theorem exists_commute_inner_eq_of_apply_star_mul_self_le
    (hf : ∀ a, ‖f (star a * a)‖ ≤ ‖ρ a ζ‖ ^ 2) :
    ∃ R : K →L[ℂ] K, (∀ a, Commute R (ρ a)) ∧ 0 ≤ R ∧ ∀ a, f a = ⟪R ζ, ρ a (R ζ)⟫_ℂ := by
  obtain ⟨T, hc, hT0, -, hfT⟩ := exists_commute_of_apply_star_mul_self_le hf
  have hR : ∀ a, Commute (CFC.sqrt T) (ρ a) := fun a => (hc a).cfcₙ_nnreal NNReal.sqrt
  refine ⟨CFC.sqrt T, hR, CFC.sqrt_nonneg T, fun a => ?_⟩
  have hsa : adjoint (CFC.sqrt T) = CFC.sqrt T := by
    rw [← star_eq_adjoint]; exact (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq
  rw [hfT a]
  nth_rw 1 [← CFC.sqrt_mul_sqrt_self T hT0]
  rw [mul_apply_eq_comp, ← hsa, adjoint_inner_left, hsa, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
    (hR a).eq]

end CStarAlgebra
