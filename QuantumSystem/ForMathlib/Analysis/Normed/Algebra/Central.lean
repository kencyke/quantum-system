/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.RingTheory.SimpleRing.Field

/-!
# Simple complex normed algebras are central

A simple complex normed algebra `A` is central: its centre is `ℂ 1`. The centre `Z` of the simple
ring `A` is a field and a commutative normed algebra. For `z ∈ Z`, the spectrum of `z` in the
completion of `Z` has a point `c` (Gelfand–Mazur), so `c - z` is not invertible in `Z`, and is
therefore `0`. Neither the dimension nor the completeness of `A` plays a role.

Simplicity is that of a ring (`IsSimpleRing`): no two-sided ideal other than `⊥` and `⊤`. For a
unital Banach algebra, such as a C⋆-algebra, it agrees with having no non-trivial closed two-sided
ideal, as every proper ideal lies in a maximal one, which is closed; that agreement is not
formalized.

## Main results

* `NormedRing.isCentral_of_isSimpleRing` — a simple complex normed algebra is central, as an
  instance.
-/

@[expose] public section

open UniformSpace

/-- **A simple complex normed algebra is central.** The centre `Z` of the simple ring `A` is a
field (`IsSimpleRing.isField_center`). For `z ∈ Z`, the spectrum of `z` in the completion of the
commutative normed algebra `Z` has a point `c` (Gelfand–Mazur, `spectrum.nonempty`), so `c - z` is
not invertible in `Z`, hence `c - z = 0`. -/
instance NormedRing.isCentral_of_isSimpleRing {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [IsSimpleRing A] : Algebra.IsCentral ℂ A where
  out z hz := by
    let Z := Subalgebra.center ℂ A
    let _ : NormedCommRing Z := { (inferInstance : NormedRing Z) with mul_comm := mul_comm }
    have : Nontrivial (Completion Z) := ⟨⟨1, 0, by
      simpa only [Completion.coe_one, Completion.coe_zero] using
        (Completion.coe_injective Z).ne (one_ne_zero (α := Z))⟩⟩
    obtain ⟨c, hc⟩ := spectrum.nonempty ((⟨z, hz⟩ : Z) : Completion Z)
    have hw : algebraMap ℂ A c - z ∈ Subring.center A := Subring.sub_mem _
      (Subring.mem_center_iff.mpr fun g => Algebra.commutes c g |>.symm)
      (Subring.mem_center_iff.mpr fun g => Subalgebra.mem_center_iff.mp hz g)
    by_cases h0 : algebraMap ℂ A c - z = 0
    · exact Algebra.mem_bot.mpr ⟨c, sub_eq_zero.mp h0⟩
    obtain ⟨v, hv⟩ := (IsSimpleRing.isField_center A).mul_inv_cancel
      (a := ⟨_, hw⟩) fun h => h0 (congrArg Subtype.val h)
    have hvZ : (v : A) ∈ Z := Subalgebra.mem_center_iff.mpr fun g =>
      (Subring.mem_center_iff.mp v.2 g)
    have hu := (IsUnit.of_mul_eq_one (b := (⟨v, hvZ⟩ : Z)) (a := algebraMap ℂ Z c - ⟨z, hz⟩)
      (Subtype.ext (congrArg Subtype.val hv))).map (Completion.coeRingHom (α := Z))
    rw [map_sub, Algebra.algebraMap_eq_smul_one] at hu
    refine absurd ?_ hc
    rw [resolventSet, Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one]
    convert hu using 2
    · change _ = ((c • 1 : Z) : Completion Z)
      rw [Completion.coe_smul, Completion.coe_one]
    · rfl
