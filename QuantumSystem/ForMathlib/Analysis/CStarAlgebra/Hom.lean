/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# ⋆-homomorphisms between C⋆-algebras

Every value `π a` of a ⋆-homomorphism `π : A → B` between C⋆-algebras has a preimage of the same
norm (`NonUnitalStarAlgHom.exists_apply_eq_norm_eq`): with `r = ‖π a‖` and
`k(t) = r / √(max t r²) - 1`, the element `b = a + a k(a⋆ a)` satisfies `b⋆ b = h(a⋆ a)` with
`h(t) = min t r²`, so `‖b‖ ≤ r`, and `π b = π a`, as `k = 0` on `[0, r²]`, which contains the spectrum
of `π(a)⋆ π(a)`.

A family of ⋆-homomorphisms `φᵢ : A → Bᵢ` with no common kernel bounds the norm of `A`: a common
bound `r ≥ 0` of the norms `‖φᵢ a‖` bounds `‖a‖`
(`NonUnitalStarAlgHom.norm_le_of_forall_norm_apply_le`).

Continuous ⋆-homomorphisms out of a topological ⋆-algebra into a Hausdorff one agree when they agree on a set that
generates it as a closed ⋆-subalgebra (`StarAlgHom.ext_of_topologicalClosure_adjoin_eq_top`), the
topological form of `StarAlgHom.ext_of_adjoin_eq_top`.

The algebras are not assumed unital in the first two results.

## Main results

* `NonUnitalStarAlgHom.exists_apply_eq_norm_eq` — values of `π` have preimages of the same norm.
* **`NonUnitalStarAlgHom.norm_le_of_forall_norm_apply_le`** — a family of ⋆-homomorphisms out of a
  C⋆-algebra with no common kernel bounds its norm: `‖a‖ ≤ r` when `0 ≤ r` and `‖φᵢ a‖ ≤ r` for
  all `i`.
* `StarAlgHom.ext_of_topologicalClosure_adjoin_eq_top` — ⋆-homomorphisms agreeing on a topological
  generating set agree.
-/

@[expose] public section

open scoped CStarAlgebra
open Filter Topology

namespace StarAlgHom

/-- Continuous ⋆-homomorphisms `f, g : A → B` into a Hausdorff ⋆-algebra agree when they agree on a
set `s` whose generated closed ⋆-subalgebra is `A`: their equalizer is a closed ⋆-subalgebra
containing `s`. -/
lemma ext_of_topologicalClosure_adjoin_eq_top {F R A B : Type*} [CommSemiring R] [StarRing R]
    [TopologicalSpace A] [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [TopologicalSpace B] [Semiring B] [Algebra R B]
    [StarRing B] [T2Space B] [FunLike F A B] [AlgHomClass F R A B] [StarHomClass F A B] {s : Set A}
    (h : (StarAlgebra.adjoin R s).topologicalClosure = ⊤) {f g : F} (hf : Continuous f)
    (hg : Continuous g) (hs : s.EqOn f g) : f = g := by
  have hcl := StarSubalgebra.topologicalClosure_minimal
    (adjoin_le_equalizer (StarAlgHom.ofClass f) (StarAlgHom.ofClass g) hs) (isClosed_eq hf hg)
  rw [h] at hcl
  exact DFunLike.ext _ _ fun x => hcl trivial

end StarAlgHom

namespace NonUnitalStarAlgHom

/-- For a bundled ⋆-homomorphism `π` between C⋆-algebras, every value `π a` is `π b` for some `b`
with `‖b‖ ≤ ‖π a‖`. With `r = ‖π a‖` and `k(t) = r / √(max t r²) - 1`, which vanishes on `[0, r²]`,
take `b = a + a k(a⋆ a)`: then `b⋆ b = h(a⋆ a)` with `h(t) = t (1 + k(t))² = min t r²`, so
`‖b‖² ≤ r²`, and `π b = π a + π a · k(π(a)⋆ π(a)) = π a`, as `[0, r²]` contains the spectrum of
`π(a)⋆ π(a)`. -/
private lemma exists_apply_eq_norm_le {A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] (π : A →⋆ₙₐ[ℂ] B) (a : A) : ∃ b, π b = π a ∧ ‖b‖ ≤ ‖π a‖ := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  rcases eq_or_lt_of_le (norm_nonneg (π a)) with hr0 | hr0
  · exact ⟨0, by rw [map_zero, norm_eq_zero.mp hr0.symm], by rw [norm_zero]; exact norm_nonneg _⟩
  let k : ℝ → ℝ := fun t => ‖π a‖ / Real.sqrt (max t (‖π a‖ ^ 2)) - 1
  have hpos : ∀ t, 0 < Real.sqrt (max t (‖π a‖ ^ 2)) := fun t =>
    Real.sqrt_pos.mpr ((pow_pos hr0 2).trans_le (le_max_right _ _))
  have hk : Continuous k :=
    (continuous_const.div (Real.continuous_sqrt.comp (continuous_id.max continuous_const))
      fun t => (hpos t).ne').sub continuous_const
  have hk1 : ∀ t, t ≤ ‖π a‖ ^ 2 → k t = 0 := fun t ht => by
    simp only [k, max_eq_right ht, Real.sqrt_sq (norm_nonneg _), div_self hr0.ne', sub_self]
  have hk0 : k 0 = 0 := hk1 0 (sq_nonneg _)
  have hxsa : IsSelfAdjoint (star a * a) := IsSelfAdjoint.star_mul_self a
  have hKsa : star (cfcₙ k (star a * a)) = cfcₙ k (star a * a) :=
    (cfcₙ_predicate k (star a * a)).star_eq
  have hid : cfcₙ (fun t : ℝ => t) (star a * a) = star a * a := cfcₙ_id' ℝ (star a * a)
  refine ⟨a + a * cfcₙ k (star a * a), ?_, ?_⟩
  · rw [map_add, map_mul, π.map_cfcₙ k (star a * a) hk.continuousOn hk0 (map_continuous π) hxsa
      (hxsa.map π)]
    have h0 : cfcₙ k (π (star a * a)) = 0 := by
      refine (cfcₙ_congr fun t ht => ?_).trans (cfcₙ_zero ℝ _)
      have h := quasispectrum.norm_le_norm_of_mem ht
      rw [map_mul, map_star, CStarRing.norm_star_mul_self, ← sq, Real.norm_eq_abs] at h
      exact hk1 t ((le_abs_self t).trans h)
    rw [h0, mul_zero, add_zero]
  · have hb : star (a + a * cfcₙ k (star a * a)) * (a + a * cfcₙ k (star a * a)) =
        cfcₙ (fun t : ℝ => t + t * k t + (k t * t + k t * t * k t)) (star a * a) := by
      rw [cfcₙ_add (fun t : ℝ => t + t * k t) (fun t : ℝ => k t * t + k t * t * k t) (star a * a)
          (by fun_prop) (by simp [hk0]) (by fun_prop) (by simp [hk0]),
        cfcₙ_add (fun t : ℝ => t) (fun t : ℝ => t * k t) (star a * a)
          (by fun_prop) (by simp) (by fun_prop) (by simp),
        cfcₙ_add (fun t : ℝ => k t * t) (fun t : ℝ => k t * t * k t) (star a * a)
          (by fun_prop) (by simp) (by fun_prop) (by simp),
        cfcₙ_mul (fun t : ℝ => t) k (star a * a) (by fun_prop) (by simp) hk.continuousOn hk0,
        cfcₙ_mul k (fun t : ℝ => t) (star a * a) hk.continuousOn hk0 (by fun_prop) (by simp),
        cfcₙ_mul (fun t : ℝ => k t * t) k (star a * a) (by fun_prop) (by simp) hk.continuousOn hk0,
        cfcₙ_mul k (fun t : ℝ => t) (star a * a) hk.continuousOn hk0 (by fun_prop) (by simp),
        hid, star_add, star_mul, hKsa]
      noncomm_ring
    have h2 : ‖a + a * cfcₙ k (star a * a)‖ * ‖a + a * cfcₙ k (star a * a)‖ ≤ ‖π a‖ * ‖π a‖ := by
      rw [← CStarRing.norm_star_mul_self, hb, ← sq]
      refine norm_cfcₙ_le fun t ht => ?_
      have ht0 : 0 ≤ t := quasispectrum_nonneg_of_nonneg _ (star_mul_self_nonneg a) t ht
      have hF : t + t * k t + (k t * t + k t * t * k t) = t * (1 + k t) ^ 2 := by ring
      rw [hF, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (sq_nonneg _))]
      rcases le_or_gt t (‖π a‖ ^ 2) with h | h
      · rw [hk1 t h, add_zero, one_pow, mul_one]
        exact h
      · have hgt : 1 + k t = ‖π a‖ / Real.sqrt t := by
          simp only [k, max_eq_left h.le]
          ring
        have htne : t ≠ 0 := ((sq_nonneg _).trans_lt h).ne'
        rw [hgt, div_pow, Real.sq_sqrt ht0, mul_div_assoc', mul_comm, mul_div_assoc, div_self htne,
          mul_one]
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr h2

/-- **Lifts of the same norm.** Every value `π a` of a ⋆-homomorphism between C⋆-algebras is `π b`
for some `b` of the same norm, `‖b‖ = ‖π a‖`: there is one with `‖b‖ ≤ ‖π a‖`, and `π` is
contractive. The algebras are not assumed unital. -/
lemma exists_apply_eq_norm_eq {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] (π : F) (a : A) :
    ∃ b, π b = π a ∧ ‖b‖ = ‖π a‖ := by
  obtain ⟨b, hb, hle⟩ := exists_apply_eq_norm_le (NonUnitalStarAlgHom.ofClass π) a
  have hb' : π b = π a := hb
  exact ⟨b, hb', le_antisymm hle (hb' ▸ NonUnitalStarAlgHom.norm_apply_le π b)⟩

/-- **A family of ⋆-homomorphisms with no common kernel bounds the norm**: if the
⋆-homomorphisms `φᵢ : A → Bᵢ` of C⋆-algebras vanish together at `0` only, a common bound `r ≥ 0` of
the norms `‖φᵢ a‖` bounds `‖a‖`. For `f(t) = max (|t| - r², 0)`, each `φᵢ` sends `f(a⋆ a)` to
`f(φᵢ(a)⋆ φᵢ(a)) = 0`, so `f(a⋆ a) = 0` and the spectrum of `a⋆ a` lies in `[-r², r²]`. The case of
one injective ⋆-homomorphism is `NonUnitalStarAlgHom.norm_map`. -/
theorem norm_le_of_forall_norm_apply_le {ι : Type*} {A : Type*} [NonUnitalCStarAlgebra A]
    {B : ι → Type*} [∀ i, NonUnitalCStarAlgebra (B i)] (φ : ∀ i, A →⋆ₙₐ[ℂ] B i)
    (hφ : ∀ a : A, (∀ i, φ i a = 0) → a = 0) {a : A} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ‖φ i a‖ ≤ r) : ‖a‖ ≤ r := by
  have hp : IsSelfAdjoint (star a * a) := IsSelfAdjoint.star_mul_self a
  let f : ℝ → ℝ := fun t => max (|t| - r ^ 2) 0
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = 0 := by simp [f, sq_nonneg]
  have hq : cfcₙ f (star a * a) = 0 := by
    refine hφ _ fun i => ?_
    rw [(φ i).map_cfcₙ f (star a * a) hf.continuousOn hf0 (map_continuous (φ i)) hp
      (hp.map (φ i))]
    refine (cfcₙ_congr fun x hx => ?_).trans (cfcₙ_zero ℝ _)
    have hx' : ‖x‖ ≤ ‖φ i (star a * a)‖ := quasispectrum.norm_le_norm_of_mem hx
    rw [map_mul, map_star, CStarRing.norm_star_mul_self] at hx'
    have : |x| ≤ r ^ 2 := hx'.trans (by nlinarith [h i, norm_nonneg (φ i a)])
    simp [f, this]
  have hle : ‖star a * a‖ ≤ r ^ 2 := by
    rw [← cfcₙ_id' ℝ (star a * a)]
    refine norm_cfcₙ_le fun x hx => ?_
    have h0 := norm_apply_le_norm_cfcₙ f (star a * a) hx
    rw [hq, norm_zero] at h0
    have h1 : max (|x| - r ^ 2) 0 = 0 := by simpa [f] using h0
    have := le_max_left (|x| - r ^ 2) 0
    rw [Real.norm_eq_abs]
    linarith
  rw [CStarRing.norm_star_mul_self] at hle
  exact (abs_le_of_sq_le_sq' (by nlinarith [norm_nonneg a]) hr).2

end NonUnitalStarAlgHom
