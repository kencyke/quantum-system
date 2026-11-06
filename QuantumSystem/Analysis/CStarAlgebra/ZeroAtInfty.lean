/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Quotient
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.lpSpace
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.ZeroAtInfty

/-!
# The c₀-direct sum as a closed two-sided ideal of `ℓ^∞`

For a family `A` of C⋆-algebras, the c₀-direct sum `lp.zeroAtInfty ℂ A` is a closed two-sided
ideal of `ℓ^∞(A)`, so it is a C⋆-algebra and the quotient `ℓ^∞(A) ⧸ c₀(A)` is a C⋆-algebra, unital
when every `A i` is unital.
-/

@[expose] public section

open scoped ENNReal

namespace lp

variable {𝕜 ι : Type*} {B : ι → Type*} [NormedField 𝕜] [∀ i, NonUnitalNormedRing (B i)]
  [∀ i, NormedSpace 𝕜 (B i)]

/-- The c₀-direct sum of normed rings is a two-sided ideal of `ℓ^∞(B)`. -/
instance : (zeroAtInfty 𝕜 B).IsTwoSidedIdeal where
  mul_mem_left f _ hg := zeroAtInfty.mul_mem_left f hg
  mul_mem_right g _ hf := zeroAtInfty.mul_mem_right g hf

end lp

section Examples

variable {ι : Type*} {A : ι → Type*}

noncomputable example [∀ i, NonUnitalCStarAlgebra (A i)] :
    NonUnitalCStarAlgebra (lp.zeroAtInfty ℂ A).toNonUnitalStarSubalgebra :=
  inferInstance

noncomputable example [∀ i, NonUnitalCStarAlgebra (A i)] :
    NonUnitalCStarAlgebra (lp A ∞ ⧸ lp.zeroAtInfty ℂ A) :=
  inferInstance

noncomputable example [∀ i, CStarAlgebra (A i)] : CStarAlgebra (lp A ∞ ⧸ lp.zeroAtInfty ℂ A) :=
  inferInstance

end Examples
