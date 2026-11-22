/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Nuclear.InductiveLimit
public import QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra

/-!
# Nuclearity of the quasi-local algebra

The quasi-local C⋆-algebra of a faithful local net is the inductive limit of its local algebras, so
it is nuclear when they are.

## Main results

* `LocalNet.isNuclear_quasiLocalCStarAlgebra` — the quasi-local C⋆-algebra of a faithful local net
  with nuclear local algebras is nuclear.
-/

@[expose] public section

universe v w

namespace LocalNet

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
  (N : LocalNet K) [N.Faithful]

/-- **The quasi-local C⋆-algebra of a faithful local net with nuclear local algebras is nuclear**:
the local algebras embed isometrically, increasingly along the directed set of regions, with dense
union (`CStarAlgebra.IsNuclear.of_dense_iUnion`). -/
theorem isNuclear_quasiLocalCStarAlgebra [∀ O, CStarAlgebra.IsNuclear.{v, w} (N.algebra O)] :
    CStarAlgebra.IsNuclear.{v, w} N.quasiLocalCStarAlgebra :=
  CStarAlgebra.IsNuclear.of_dense_iUnion (fun O => (N.ιLocalCStar O).toNonUnitalStarAlgHom)
    N.ιLocalCStar_injective
    (fun O₁ O₂ => by
      obtain ⟨O, h₁, h₂⟩ := directed_of (· ≤ ·) O₁ O₂
      refine ⟨O, ?_, ?_⟩ <;> rintro _ ⟨X, rfl⟩
      · exact ⟨N.incl h₁ X, N.ιLocalCStar_incl h₁ X⟩
      · exact ⟨N.incl h₂ X, N.ιLocalCStar_incl h₂ X⟩)
    N.denseRange_iUnion_ιLocalCStar

end LocalNet
