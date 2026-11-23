/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.DynamicalSystem
public import QuantumSystem.Analysis.SpectralTheory.UnitaryRepresentation
public import QuantumSystem.Analysis.VonNeumannAlgebra.NormalFunctional

/-!
# W⋆-dynamical systems

A **W⋆-dynamical system** `(M, G, α)` is a von Neumann algebra `M ⊆ B(H)`, a topological group `G`
and an action of `G` on `M` by ⋆-automorphisms, continuous in the point-σ-weak topology:
`g ↦ α g x` is σ-weakly continuous for every `x ∈ M`. It is spelled as a continuous homomorphism
`α : G →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak)` into the ⋆-automorphisms of `M.sigmaWeak`, the copy of
`M` carrying the σ-weak topology (`VonNeumannAlgebra.sigmaWeak`, a ⋆-algebra over `ℂ` isomorphic to
`M` by `VonNeumannAlgebra.sigmaWeakEquiv`). The topology of pointwise convergence on ⋆-isomorphisms
(`QuantumSystem.Analysis.CStarAlgebra.StarAlgEquiv`) is there the point-σ-weak topology,
as it is the point-norm topology on `M ≃⋆ₐ[ℂ] M`; `α g` acts on `x ∈ M` by
`M.ofSigmaWeak (α g (M.toSigmaWeak x))`. An additive group `V`, such as the time axis `ℝ`, acts by a
continuous additive character `α : ContinuousAddChar V (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak)`, the
continuous homomorphism `α.toContinuousMonoidHom` from `Multiplicative V`. As for C⋆-dynamical
systems, no separate name is given to the type of `α`: Mathlib's `ContinuousMonoidHom` is the object.
The fixed-point algebra `M^α` is `StarAlgEquiv.fixedPoints α.toMonoidHom`, and the points fixed by a
dense subset of `G` are fixed by
`G` (`StarAlgEquiv.mem_fixedPoints_iff_of_dense`, `M.sigmaWeak` being Hausdorff). `G` need not be a
topological group for the statements below: none of them uses a compatibility of the topology of `G`
with its multiplication.

The point-norm topology is finer than the point-σ-weak one, so a C⋆-dynamical system on `M` is a
W⋆-dynamical system (`VonNeumannAlgebra.toSigmaWeakAut`). The inner action of the unitary group of
`M` is one even for the strong operator topology on the unitaries (`VonNeumannAlgebra.unitarySOT`,
`VonNeumannAlgebra.conjSigmaWeakAut`), which is coarser than the norm topology.

A strongly continuous unitary representation `U` of `G` on `H` whose unitaries normalize `M`,
`U g x U g⋆ ∈ M` for `x ∈ M`, acts on `M` by `x ↦ U g x U g⋆` as a W⋆-dynamical system
(`UnitaryRepresentation.conjSigmaWeakAut`); every `U` normalizes `B(H)`
(`UnitaryRepresentation.conjSigmaWeakAutBoundedLinearOperators`). Its continuity rests on the σ-weak continuity of
`g ↦ U g x U g⋆` for every operator `x` (`UnitaryRepresentation.continuous_ofCLM_mul_mul_star`):
`∑ₙ ⟪ξₙ, U g x U g⋆ ηₙ⟫ = ∑ₙ ⟪(U g)⁻¹ ξₙ, x (U g)⁻¹ ηₙ⟫`, whose terms are continuous in `g` and bounded
by `‖x‖ (‖ξₙ‖² + ‖ηₙ‖²)`, a summable bound independent of `g`.

## Main definitions

* `VonNeumannAlgebra.toSigmaWeakAut M` — the continuous homomorphism
  `(M ≃⋆ₐ[ℂ] M) →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak)`, through which a C⋆-dynamical system on `M` is a
  W⋆-dynamical system.
* `VonNeumannAlgebra.unitarySOT M` — the unitary group of `M` with the strong operator topology.
* `VonNeumannAlgebra.conjSigmaWeakAut M` — the inner action `x ↦ u x u⋆` of `M.unitarySOT`.
* `UnitaryRepresentation.conjSigmaWeakAut U M hU` — the action `x ↦ U g x U g⋆` on `M`;
  `UnitaryRepresentation.conjSigmaWeakAutBoundedLinearOperators U` — on `B(H)`, with no hypothesis.

## Main results

* **`VonNeumannAlgebra.continuous_apply_apply_of_continuous`** — for a W⋆-dynamical system `α`,
  `g ↦ ω (α g x)` is continuous for every σ-weakly continuous functional `ω`, in particular for every
  normal positive one (`VonNeumannAlgebra.continuous_apply_apply_of_isNormal`).
* **`UnitaryRepresentation.continuous_ofCLM_mul_mul_star`** — `g ↦ U g x U g⋆` is σ-weakly
  continuous for every operator `x`.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped InnerProductSpace lp ComplexOrder

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-- **A C⋆-dynamical system on a von Neumann algebra is a W⋆-dynamical system**: carrying a
⋆-automorphism of `M` to `M.sigmaWeak` (`StarAlgEquiv.autCongr` along `M.sigmaWeakEquiv`) is
continuous from the point-norm topology to the point-σ-weak topology, the σ-weak topology being
coarser than the norm topology. Composing with it turns `G →ₜ* (M ≃⋆ₐ[ℂ] M)` into
`G →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak)`. -/
def toSigmaWeakAut : (M ≃⋆ₐ[ℂ] M) →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak) :=
  ⟨(StarAlgEquiv.autCongr M.sigmaWeakEquiv).toMonoidHom,
    StarAlgEquiv.continuous_iff.mpr fun T =>
      continuous_toSigmaWeak.comp (continuous_eval_const (M.ofSigmaWeak T))⟩

variable {M}

/-- `toSigmaWeakAut` does not change the action. -/
@[simp] lemma toSigmaWeakAut_apply (α : M ≃⋆ₐ[ℂ] M) (T : M.sigmaWeak) :
    toSigmaWeakAut M α T = M.toSigmaWeak (α (M.ofSigmaWeak T)) :=
  rfl

/-- For a W⋆-dynamical system `α`, the functions `g ↦ ω (α g x)` are continuous for every σ-weakly
continuous functional `ω` on `M`, positive or not, and every `x ∈ M`. -/
theorem continuous_apply_apply_of_continuous {G : Type*} [Monoid G] [TopologicalSpace G]
    (α : G →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak)) {ω : M → ℂ}
    (hω : Continuous fun T : M.sigmaWeak => ω (M.ofSigmaWeak T)) (x : M) :
    Continuous fun g => ω (M.ofSigmaWeak (α g (M.toSigmaWeak x))) :=
  hω.comp (StarAlgEquiv.continuous_iff.mp α.continuous (M.toSigmaWeak x))

/-- For a W⋆-dynamical system `α`, the functions `g ↦ ω (α g x)` are continuous for every normal
positive functional `ω` on `M` and every `x ∈ M`: `ω` is σ-weakly continuous and `g ↦ α g x` is
σ-weakly continuous. `G` is any monoid with a topology. -/
lemma continuous_apply_apply_of_isNormal {G : Type*} [Monoid G] [TopologicalSpace G]
    (α : G →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak)) {ω : M →ₚ[ℂ] ℂ} (hω : M.IsNormal ω) (x : M) :
    Continuous fun g => ω (M.ofSigmaWeak (α g (M.toSigmaWeak x))) :=
  continuous_apply_apply_of_continuous α (ω := ⇑ω) hω x

end VonNeumannAlgebra

namespace UnitaryRepresentation

variable {G H : Type*} [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **`g ↦ U g x U g⋆` is σ-weakly continuous** for every operator `x`, for a strongly continuous
unitary representation `U` of a monoid `G` with a topology. The σ-weak functional
`∑ₙ ⟪ξₙ, U g x U g⋆ ηₙ⟫` equals `∑ₙ ⟪(U g)⁻¹ ξₙ, x (U g)⁻¹ ηₙ⟫`; its terms are continuous in `g`,
inversion being continuous on the unitary group with the strong operator topology, and bounded by
`‖x‖ (‖ξₙ‖² + ‖ηₙ‖²)`, `(U g)⁻¹` being isometric, so the sum is continuous (`continuous_tsum`). -/
theorem continuous_ofCLM_mul_mul_star [Monoid G] (U : UnitaryRepresentation G H) (x : H →L[ℂ] H) :
    Continuous fun g => ContinuousLinearMapSigmaWeak.ofCLM
      ((U g : H →L[ℂ] H) * x * star (U g : H →L[ℂ] H)) := by
  refine ContinuousLinearMapSigmaWeak.continuous_of_tsum_inner_apply_continuous fun ξ η => ?_
  have key (g : G) (n : ℕ) :
      ⟪ξ n, (ContinuousLinearMapSigmaWeak.ofCLM ((U g : H →L[ℂ] H) * x * star (U g : H →L[ℂ] H)) :
        H →σw[ℂ] H) (η n)⟫_ℂ =
        ⟪(((U g)⁻¹ : UnitarySOT ℂ H) : H →L[ℂ] H) (ξ n),
          x ((((U g)⁻¹ : UnitarySOT ℂ H) : H →L[ℂ] H) (η n))⟫_ℂ := by
    rw [UnitarySOT.coe_inv, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  simp_rw [key]
  have hinv : Continuous fun g => ((U g)⁻¹ : UnitarySOT ℂ H) := U.continuous.inv
  refine continuous_tsum (u := fun n => ‖x‖ * (‖ξ n‖ ^ 2 + ‖η n‖ ^ 2)) (fun n => ?_)
    (((lp.summable_norm_sq ξ).add (lp.summable_norm_sq η)).mul_left _) fun n g => ?_
  · have h₁ := (UnitarySOT.continuous_apply (ξ n)).comp hinv
    have h₂ := (UnitarySOT.continuous_apply (η n)).comp hinv
    exact h₁.inner (x.continuous.comp h₂)
  · calc ‖⟪(((U g)⁻¹ : UnitarySOT ℂ H) : H →L[ℂ] H) (ξ n),
          x ((((U g)⁻¹ : UnitarySOT ℂ H) : H →L[ℂ] H) (η n))⟫_ℂ‖
        ≤ ‖(((U g)⁻¹ : UnitarySOT ℂ H) : H →L[ℂ] H) (ξ n)‖ *
            ‖x ((((U g)⁻¹ : UnitarySOT ℂ H) : H →L[ℂ] H) (η n))‖ := norm_inner_le_norm _ _
      _ ≤ ‖ξ n‖ * (‖x‖ * ‖η n‖) := by
        rw [UnitarySOT.norm_apply]
        gcongr
        exact (x.le_opNorm _).trans_eq (by rw [UnitarySOT.norm_apply])
      _ ≤ ‖x‖ * (‖ξ n‖ ^ 2 + ‖η n‖ ^ 2) := by
        nlinarith [norm_nonneg x, norm_nonneg (ξ n), norm_nonneg (η n),
          mul_nonneg (norm_nonneg x) (sq_nonneg (‖ξ n‖ - ‖η n‖))]

variable [Group G]

variable (U : UnitaryRepresentation G H) (M : VonNeumannAlgebra H)
  (hU : ∀ g, ∀ x ∈ M, (U g : H →L[ℂ] H) * x * star (U g : H →L[ℂ] H) ∈ M)

/-- A strongly continuous unitary representation `U` whose unitaries normalize the von Neumann
algebra `M` acts on `M` by `x ↦ U g x U g⋆` as a **W⋆-dynamical system**: the inner action of the
unitary group of `B(H)` along `U`, restricted to `M` (`StarAlgEquiv.restrictHom`), is continuous in
the point-σ-weak topology by `UnitaryRepresentation.continuous_ofCLM_mul_mul_star`. -/
def conjSigmaWeakAut : G →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak) :=
  ⟨(StarAlgEquiv.autCongr M.sigmaWeakEquiv).toMonoidHom.comp
    (StarAlgEquiv.restrictHom ((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H)).comp
      ((UnitarySOT.ofUnitary ℂ H).symm.toMonoidHom.comp U.toMonoidHom)) M hU),
    StarAlgEquiv.continuous_iff.mpr fun T =>
      (U.continuous_ofCLM_mul_mul_star (M.ofSigmaWeak T : H →L[ℂ] H)).subtype_mk _⟩

/-- The action `conjSigmaWeakAut` is conjugation by the unitaries of `U`. -/
@[simp] lemma coe_conjSigmaWeakAut_apply (g : G) (T : M.sigmaWeak) :
    ((M.ofSigmaWeak (U.conjSigmaWeakAut M hU g T) : M) : H →L[ℂ] H) =
      (U g : H →L[ℂ] H) * (M.ofSigmaWeak T : M) * star (U g : H →L[ℂ] H) :=
  rfl

/-- Every strongly continuous unitary representation `U` on `H` acts on `B(H)` by `x ↦ U g x U g⋆` as
a W⋆-dynamical system: `conjSigmaWeakAut` for the von Neumann algebra of all operators, which every
unitary normalizes. -/
def conjSigmaWeakAutBoundedLinearOperators (U : UnitaryRepresentation G H) :
    G →ₜ* ((VonNeumannAlgebra.boundedLinearOperators H).sigmaWeak ≃⋆ₐ[ℂ]
      (VonNeumannAlgebra.boundedLinearOperators H).sigmaWeak) :=
  U.conjSigmaWeakAut _ fun _ _ _ => VonNeumannAlgebra.mem_boundedLinearOperators _

end UnitaryRepresentation

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-- The **unitary group of a von Neumann algebra** `M` with the strong operator topology: the
unitaries of `B(H)` lying in `M`, a subgroup of `UnitarySOT ℂ H`. -/
def unitarySOT : Subgroup (UnitarySOT ℂ H) where
  carrier := {u | (u : H →L[ℂ] H) ∈ M}
  mul_mem' {u v} hu hv := by
    change ((u * v : UnitarySOT ℂ H) : H →L[ℂ] H) ∈ M
    rw [UnitarySOT.coe_mul]
    exact M.mul_mem hu hv
  one_mem' := by
    change ((1 : UnitarySOT ℂ H) : H →L[ℂ] H) ∈ M
    rw [UnitarySOT.coe_one]
    exact M.one_mem
  inv_mem' {u} hu := by
    change ((u⁻¹ : UnitarySOT ℂ H) : H →L[ℂ] H) ∈ M
    rw [UnitarySOT.coe_inv]
    exact star_mem hu

variable {M} in
@[simp] lemma mem_unitarySOT {u : UnitarySOT ℂ H} : u ∈ M.unitarySOT ↔ (u : H →L[ℂ] H) ∈ M :=
  Iff.rfl

/-- The **inner action** `x ↦ u x u⋆` of the unitary group of a von Neumann algebra `M`, with the
strong operator topology, is a W⋆-dynamical system: `UnitaryRepresentation.conjSigmaWeakAut` for the
inclusion of `M.unitarySOT` in the unitary group of `B(H)`, whose unitaries normalize `M`. -/
def conjSigmaWeakAut : M.unitarySOT →ₜ* (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak) :=
  UnitaryRepresentation.conjSigmaWeakAut ⟨M.unitarySOT.subtype, continuous_subtype_val⟩ M
    fun u _ hx => by
      have hu : ((u : UnitarySOT ℂ H) : H →L[ℂ] H) ∈ M := u.2
      exact mul_mem (mul_mem hu hx) (star_mem hu)

/-- The inner action sends `x` to `u x u⋆`. -/
@[simp] lemma coe_conjSigmaWeakAut_apply (u : M.unitarySOT) (T : M.sigmaWeak) :
    ((M.ofSigmaWeak (M.conjSigmaWeakAut u T) : M) : H →L[ℂ] H) =
      ((u : UnitarySOT ℂ H) : H →L[ℂ] H) * (M.ofSigmaWeak T : M) *
        star ((u : UnitarySOT ℂ H) : H →L[ℂ] H) :=
  rfl

end VonNeumannAlgebra
