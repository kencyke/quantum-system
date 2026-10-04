/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.QuantumChannel.TensorProduct
public import QuantumSystem.Analysis.Entropy.VonNeumann.MutualInformation

/-!
# Strong subadditivity of the von Neumann entropy

Let `H_A`, `H_B`, `H_C` be finite-dimensional complex Hilbert spaces and `ω` a state on
`B((H_A ⊗ H_B) ⊗ H_C)`. **Strong subadditivity** (Lieb–Ruskai) is
`S(ω_ABC) + S(ω_B) ≤ S(ω_AB) + S(ω_BC)` (`State.vonNeumannEntropy_strong_subadditivity`), with the
marginals
* `ω_AB = ω.traceRight`, the restriction to `B(H_A ⊗ H_B) ⊗ 1`;
* `ω_B = ω.traceRight.traceLeft`, the restriction to `(1 ⊗ B(H_B)) ⊗ 1`;
* `ω_BC = ω.traceFirst`, the restriction along `B(H_B ⊗ H_C) → B((H_A ⊗ H_B) ⊗ H_C)`,
  `Y ⊗ Z ↦ (1 ⊗ Y) ⊗ Z` (`CompletelyPositiveMap.lTensorTensor`).

## Proof

Strong subadditivity is the monotonicity of the mutual information `I(B:C) ≤ I(AB:C)`. The mutual
information `I(AB:C)` is that of `ω` itself for the splitting `(H_A ⊗ H_B) ⊗ H_C`, and `I(B:C)` that
of `ω_BC`. The unital completely positive map `j : Y ⊗ Z ↦ (1 ⊗ Y) ⊗ Z` pulls `ω` back to `ω_BC` and
`ω_AB ⊗ ω_C` back to `ω_B ⊗ ω_C`, so the data-processing inequality along `j`
(`umegakiEntropy_comp_le_of_kPositiveMap`) and `D(ω ‖ ω_A ⊗ ω_B) = I(A:B)`
(`State.umegakiEntropy_eq_mutualInformation`) give `I(B:C) ≤ I(AB:C)`. No associator and no
partial-trace channel is used.

## Implementation notes

The declarations of this file carry `set_option maxSynthPendingDepth 2 in`. Operators on the
three-fold tensor product `(H_A ⊗ H_B) ⊗ H_C` need the normed structure of the inner factor
`H_A ⊗ H_B` while unifying instance arguments, a nested instance search at depth `2`; with the default
depth `1`, the C⋆-algebra and Loewner order of `B((H_A ⊗ H_B) ⊗ H_C)` and the composites with `j`
are not found or time out (see the section *Nested tensor products* of
`QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct`). This is the one exception to
the project's ban on `set_option`, recorded in the lint rules.

## Main definitions

* `CompletelyPositiveMap.lTensorTensor H_A H_B H_C` — the embedding `Y ⊗ Z ↦ (1 ⊗ Y) ⊗ Z` of
  `B(H_B ⊗ H_C)` into `B((H_A ⊗ H_B) ⊗ H_C)`.
* `State.traceFirst ω` — the marginal `ω_BC` of a state on `B((H_A ⊗ H_B) ⊗ H_C)`.

## Main results

* `State.vonNeumannEntropy_strong_subadditivity` — `S(ω_ABC) + S(ω_B) ≤ S(ω_AB) + S(ω_BC)`.

## References

* E. H. Lieb, M. B. Ruskai, *Proof of the strong subadditivity of quantum-mechanical entropy*,
  J. Math. Phys. 14 (1973), 1938–1941.
* G. Lindblad, *Completely positive maps and entropy inequalities*, Comm. Math. Phys. 40 (1975),
  147–151.
-/

@[expose] public section

open ContinuousLinearMap TensorProduct
open scoped InnerProductSpace ComplexOrder QuantumInfo TensorProduct CStarAlgebra

variable {H_A H_B H_C : Type*}
  [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A] [FiniteDimensional ℂ H_A]
  [NormedAddCommGroup H_B] [InnerProductSpace ℂ H_B] [FiniteDimensional ℂ H_B]
  [NormedAddCommGroup H_C] [InnerProductSpace ℂ H_C] [FiniteDimensional ℂ H_C]

namespace CompletelyPositiveMap

variable (H_A H_B H_C) in
set_option maxSynthPendingDepth 2 in
/-- The embedding `Y ⊗ Z ↦ (1 ⊗ Y) ⊗ Z` of `B(H_B ⊗ H_C)` into `B((H_A ⊗ H_B) ⊗ H_C)`: the tensor
product of the ampliation `Y ↦ 1 ⊗ Y` with the identity of `B(H_C)`. -/
noncomputable def lTensorTensor :
    (H_B ⊗[ℂ] H_C →L[ℂ] H_B ⊗[ℂ] H_C) →CP
      ((H_A ⊗[ℂ] H_B) ⊗[ℂ] H_C →L[ℂ] (H_A ⊗[ℂ] H_B) ⊗[ℂ] H_C) :=
  tensorProduct
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (lTensorStarAlgHom ℂ H_B H_A))
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.id ℂ (H_C →L[ℂ] H_C)))

set_option maxSynthPendingDepth 2 in
/-- `(Y ⊗ Z) ↦ (1 ⊗ Y) ⊗ Z`. -/
theorem lTensorTensor_mapL (Y : H_B →L[ℂ] H_B) (Z : H_C →L[ℂ] H_C) :
    lTensorTensor H_A H_B H_C (mapL Y Z) = mapL (Y.lTensor H_A) Z :=
  tensorProduct_mapL _ _ Y Z

set_option maxSynthPendingDepth 2 in
/-- The embedding is unital. -/
theorem lTensorTensor_one : lTensorTensor H_A H_B H_C 1 = 1 := by
  have h₁ : (1 : H_B ⊗[ℂ] H_C →L[ℂ] H_B ⊗[ℂ] H_C) = mapL 1 1 := by
    rw [one_def, one_def, one_def, mapL_id_id]
  have h₂ : (1 : (H_A ⊗[ℂ] H_B) ⊗[ℂ] H_C →L[ℂ] (H_A ⊗[ℂ] H_B) ⊗[ℂ] H_C) = mapL 1 1 := by
    rw [one_def, one_def, one_def, mapL_id_id]
  rw [h₁, lTensorTensor_mapL, h₂, lTensor_one]

end CompletelyPositiveMap

namespace State

variable (ω : State ((H_A ⊗[ℂ] H_B) ⊗[ℂ] H_C →L[ℂ] (H_A ⊗[ℂ] H_B) ⊗[ℂ] H_C))

set_option maxSynthPendingDepth 2 in
/-- The **marginal** `ω_BC` of a state on `B((H_A ⊗ H_B) ⊗ H_C)`: its restriction along
`Y ⊗ Z ↦ (1 ⊗ Y) ⊗ Z` (`CompletelyPositiveMap.lTensorTensor`). Only the first factor `H_A` is
traced out; `H_B` and `H_C` are kept, unlike `traceLeft`, which traces out all of `H_A ⊗ H_B`. -/
noncomputable def traceFirst : State (H_B ⊗[ℂ] H_C →L[ℂ] H_B ⊗[ℂ] H_C) :=
  ω.comp (CompletelyPositiveMap.lTensorTensor H_A H_B H_C) CompletelyPositiveMap.lTensorTensor_one

set_option maxSynthPendingDepth 2 in
/-- `traceFirst` evaluates `ω` on the ampliation `X ↦ 1 ⊗ X`. -/
theorem traceFirst_apply (X : H_B ⊗[ℂ] H_C →L[ℂ] H_B ⊗[ℂ] H_C) :
    ω.traceFirst X = ω (CompletelyPositiveMap.lTensorTensor H_A H_B H_C X) :=
  rfl

set_option maxSynthPendingDepth 2 in
/-- **Strong subadditivity** (Lieb–Ruskai): `S(ω_ABC) + S(ω_B) ≤ S(ω_AB) + S(ω_BC)` for a state
`ω` on `B((H_A ⊗ H_B) ⊗ H_C)`, with `ω_AB = ω.traceRight`, `ω_B = ω.traceRight.traceLeft` and
`ω_BC = ω.traceFirst`. -/
theorem vonNeumannEntropy_strong_subadditivity :
    S(ω) + S(ω.traceRight.traceLeft) ≤ S(ω.traceRight) + S(ω.traceFirst) := by
  set j := CompletelyPositiveMap.lTensorTensor H_A H_B H_C
  -- the marginals of `ω_BC`
  have hR : ω.traceFirst.traceRight = ω.traceRight.traceLeft := State.ext fun Y => by
    have h : Y.rTensor H_C = mapL Y 1 := ContinuousLinearMap.coe_inj.mp <| ext' fun _ _ => rfl
    have h' : (Y.lTensor H_A).rTensor H_C = mapL (Y.lTensor H_A) 1 :=
      ContinuousLinearMap.coe_inj.mp <| ext' fun _ _ => rfl
    rw [traceRight_apply, traceFirst_apply, h, CompletelyPositiveMap.lTensorTensor_mapL,
      traceLeft_apply, traceRight_apply, h']
  have hL : ω.traceFirst.traceLeft = ω.traceLeft := State.ext fun Z => by
    have h : Z.lTensor H_B = mapL 1 Z := ContinuousLinearMap.coe_inj.mp <| ext' fun _ _ => rfl
    have h' : Z.lTensor (H_A ⊗[ℂ] H_B) = mapL ((1 : H_B →L[ℂ] H_B).lTensor H_A) Z := by
      rw [lTensor_one]
      exact ContinuousLinearMap.coe_inj.mp <| ext' fun _ _ => rfl
    rw [traceLeft_apply, traceFirst_apply, h, CompletelyPositiveMap.lTensorTensor_mapL,
      traceLeft_apply, h']
  -- the product of the marginals pulls back to the product of the marginals
  have hprod : ∀ X, ω.traceRight.tensorProduct ω.traceLeft (j X) =
      ω.traceRight.traceLeft.tensorProduct ω.traceLeft X := fun X => by
    have h := ext_mapL (𝕜 := ℂ) (E := H_B) (F := H_B) (G := H_C) (H := H_C) (M := ℂ)
      (u := (PositiveLinearMap.ofClass (ω.traceRight.tensorProduct ω.traceLeft)).toLinearMap ∘ₗ
        j.toLinearMap)
      (v := (PositiveLinearMap.ofClass (ω.traceRight.traceLeft.tensorProduct ω.traceLeft)).toLinearMap)
      fun Y Z => by
      change ω.traceRight.tensorProduct ω.traceLeft (j (mapL Y Z)) =
        ω.traceRight.traceLeft.tensorProduct ω.traceLeft (mapL Y Z)
      rw [CompletelyPositiveMap.lTensorTensor_mapL, tensorProduct_mapL, tensorProduct_mapL,
        traceLeft_apply ω.traceRight]
    exact LinearMap.congr_fun h X
  -- the data-processing inequality along `j`, read as `I(B:C) ≤ I(AB:C)`
  have hD := umegakiEntropy_comp_le_of_kPositiveMap j CompletelyPositiveMap.lTensorTensor_one
    (ψ₁ := ω.traceFirst) (φ₁ := ω.traceFirst.traceRight.tensorProduct ω.traceFirst.traceLeft)
    (ψ := ω) (φ := ω.traceRight.tensorProduct ω.traceLeft) (fun _ => rfl)
    (fun X => by rw [hR, hL]; exact (hprod X).symm)
  rw [umegakiEntropy_eq_mutualInformation, umegakiEntropy_eq_mutualInformation] at hD
  have hI : ω.traceFirst.mutualInformation ≤ ω.mutualInformation := by exact_mod_cast hD
  rw [mutualInformation, mutualInformation, hR, hL] at hI
  linarith

end State
