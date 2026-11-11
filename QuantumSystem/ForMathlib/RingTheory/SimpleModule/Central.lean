/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Central semisimple algebras are simple

A nontrivial semisimple algebra `A` over a field `K` that is central (`Algebra.IsCentral K A`) is a
simple ring. By the Wedderburn–Artin theorem `A ≃ₐ[K] Π i, Mₙᵢ(Dᵢ)` with division algebras `Dᵢ`; the
unit of each block is a nonzero central idempotent of `A`, so it is `1` in a central algebra, and
the units of two different blocks multiply to `0`, so there is exactly one block.

## Main results

* `IsSemisimpleRing.isSimpleRing_of_isCentral` — a nontrivial central semisimple algebra over a
  field is simple.
* `Algebra.IsCentral.eq_one_of_isIdempotentElem` — in a central algebra over an integral domain,
  faithful as a module, a nonzero central idempotent is `1`.

## TODO

Upstream `Algebra.IsCentral.eq_one_of_isIdempotentElem` to `Mathlib.Algebra.Central.Basic`, which
needs nothing from Wedderburn–Artin.
-/

@[expose] public section

namespace Algebra.IsCentral

variable {K A : Type*} [CommRing K] [IsDomain K] [Ring A] [Algebra K A] [FaithfulSMul K A]
  [Algebra.IsCentral K A]

/-- In a central algebra over an integral domain `K`, faithful as a `K`-module, a nonzero central
idempotent is `1`. -/
lemma eq_one_of_isIdempotentElem {z : A} (hz : z ∈ Subalgebra.center K A) (hzz : IsIdempotentElem z)
    (hz0 : z ≠ 0) : z = 1 := by
  obtain ⟨c, rfl⟩ := (Algebra.IsCentral.mem_center_iff K).mp hz
  have hinj := FaithfulSMul.algebraMap_injective K A
  have hcc : c * c = c := hinj (by rw [map_mul]; exact hzz)
  have hc0 : c ≠ 0 := fun h => hz0 (by rw [h, map_zero])
  rw [show c = 1 from mul_left_cancel₀ hc0 (hcc.trans (mul_one c).symm), map_one]

end Algebra.IsCentral

/-- **A central semisimple algebra is simple**: a nontrivial semisimple algebra `A` over a field `K`
with `Algebra.IsCentral K A` is a simple ring. By Wedderburn–Artin
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing`) `A ≃ₐ[K] Π i, Mₙᵢ(Dᵢ)`; the unit of each
block is a nonzero central idempotent, hence `1` (`Algebra.IsCentral.eq_one_of_isIdempotentElem`),
and the units of two different blocks multiply to `0`, so there is exactly one block. -/
theorem IsSemisimpleRing.isSimpleRing_of_isCentral (K : Type*) {A : Type*} [Field K] [Ring A]
    [Algebra K A] [IsSemisimpleRing A] [Nontrivial A] [Algebra.IsCentral K A] : IsSimpleRing A := by
  classical
  obtain ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing K A
  have : ∀ i, Nonempty (Fin (d i)) := fun i => have := hd i; inferInstance
  -- the unit of the `i`-th block
  let p : Fin n → Π i, Matrix (Fin (d i)) (Fin (d i)) (D i) := fun i => Pi.single i 1
  have hp_central : ∀ i (y : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)), y * p i = p i * y :=
    fun i y => by
      funext j
      by_cases hji : j = i
      · subst hji; simp [p]
      · simp [p, hji]
  have hp_idem : ∀ i, p i * p i = p i := fun i => by
    funext j
    by_cases hji : j = i
    · subst hji; simp [p]
    · simp [p, hji]
  have hp_ne : ∀ i, p i ≠ 0 := fun i h =>
    one_ne_zero (α := Matrix (Fin (d i)) (Fin (d i)) (D i)) (by simpa [p] using congrFun h i)
  have hx_one : ∀ i, e.symm (p i) = 1 := fun i => by
    refine Algebra.IsCentral.eq_one_of_isIdempotentElem (K := K)
      (Subalgebra.mem_center_iff.mpr fun y => ?_) (by rw [IsIdempotentElem, ← map_mul, hp_idem]) ?_
    · rw [← e.symm_apply_apply y, ← map_mul, ← map_mul, hp_central]
    · exact fun h => hp_ne i (e.symm.injective (h.trans (map_zero _).symm))
  -- there is a block, as `A` is nontrivial
  have hne : Nonempty (Fin n) := by
    rw [← not_isEmpty_iff]
    intro _
    exact one_ne_zero (e.injective (Subsingleton.elim _ _) : (1 : A) = 0)
  -- and only one, as two units of different blocks multiply to `0`
  have hsub : Subsingleton (Fin n) := by
    refine ⟨fun i j => by_contra fun hij => ?_⟩
    have hpij : p i * p j = 0 := by
      funext k
      by_cases hki : k = i
      · subst hki; simp [p, hij]
      · simp [p, hki]
    have h1 : (1 : A) = 0 := by
      rw [← hx_one i, ← mul_one (e.symm (p i)), ← hx_one j, ← map_mul, hpij, map_zero]
    exact one_ne_zero h1
  have : Unique (Fin n) := ⟨⟨hne.some⟩, fun i => Subsingleton.elim _ _⟩
  exact IsSimpleRing.of_ringEquiv (e.toRingEquiv.trans (RingEquiv.piUnique _)).symm inferInstance
