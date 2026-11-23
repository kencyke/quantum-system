/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.Central.TensorProduct
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The tensor product of central algebras is central

Mathlib's `Mathlib.Algebra.Central.TensorProduct` proves that the factors of a central tensor
product over a field are central. This file proves the converse: over a field, the tensor product
of two central algebras is central. An element of the center commutes with `B ⊗ 1`, so it lies in
`Z(B) ⊗ C = 1 ⊗ C` (`Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct`), and
commuting with `1 ⊗ C` it is `1 ⊗ c` for a central, hence scalar, `c`.

## Main results

* `Algebra.IsCentral.tensorProduct` — over a field, `B ⊗[K] C` is central when `B` and `C` are.

## TODO

Upstream to `Mathlib.Algebra.Central.TensorProduct`, next to `Algebra.IsCentral.left_of_tensor`.
-/

@[expose] public section

open TensorProduct Algebra.TensorProduct

namespace Algebra.IsCentral

variable (K B C : Type*) [Field K] [Ring B] [Ring C] [Algebra K B] [Algebra K C]

/-- Over a field, an element of `B ⊗[K] C` commuting with `B ⊗ 1` is `1 ⊗ c`, when `B` is
central. -/
lemma mem_range_includeRight_of_mem_centralizer [IsCentral K B] {z : B ⊗[K] C}
    (hz : z ∈ Subalgebra.centralizer K (includeLeft : B →ₐ[K] B ⊗[K] C).range) :
    z ∈ (includeRight : C →ₐ[K] B ⊗[K] C).range := by
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at hz
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul b c =>
    obtain ⟨k, hk⟩ := IsCentral.out b.2
    refine ⟨k • c, ?_⟩
    change includeRight (k • c) = Algebra.TensorProduct.map (Subalgebra.center K B).val
      (AlgHom.id K C) (b ⊗ₜ[K] c)
    have hk' : (b : B) = k • 1 := by rw [← hk]; exact Algebra.algebraMap_eq_smul_one k
    rw [Algebra.TensorProduct.map_tmul, Subalgebra.coe_val, AlgHom.coe_id, id_eq, hk',
      includeRight_apply, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

/-- **Over a field, the tensor product of central algebras is central.** -/
instance tensorProduct [IsCentral K B] [IsCentral K C] : IsCentral K (B ⊗[K] C) where
  out z hz := by
    rcases subsingleton_or_nontrivial B with hB | hB
    · have h1 : (1 : B ⊗[K] C) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : B) 0, TensorProduct.zero_tmul]
      exact ⟨0, by rw [map_zero, ← mul_one z, h1, mul_zero]⟩
    have hz' : z ∈ Subalgebra.centralizer K (includeLeft : B →ₐ[K] B ⊗[K] C).range := by
      rintro _ ⟨b, rfl⟩
      exact Subalgebra.mem_center_iff.mp hz _
    obtain ⟨c, rfl⟩ := mem_range_includeRight_of_mem_centralizer K B C hz'
    have hc : c ∈ Subalgebra.center K C := by
      refine Subalgebra.mem_center_iff.mpr fun c' => includeRight_injective (R := K)
        (FaithfulSMul.algebraMap_injective K B) ?_
      rw [map_mul, map_mul]
      exact Subalgebra.mem_center_iff.mp hz _
    obtain ⟨k, rfl⟩ := IsCentral.out hc
    exact ⟨k, by simp [AlgHom.commutes]⟩

end Algebra.IsCentral
