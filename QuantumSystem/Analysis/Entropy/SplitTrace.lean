module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import QuantumSystem.Algebra.LocalNet.TensorDecomposition

/-!
# Trace on a split net and its preservation under the marginal

The first brick of the **representation-free quantum-information layer** built on the split
property (`LocalNet.Split`). The split structure identifies each local algebra with the type I
factor `End ℂ (ℋ Λ)` of operators on a finite-dimensional action space, which carries the
canonical trace `LinearMap.trace`. This file:

* records the general fact that the partial trace along a tensor decomposition preserves the
  trace (`LinearMap.trace_partialTrace`, via the operator factorisation `partialTraceRight`);
* defines the trace `LocalNet.Split.trace` on the local algebra of a split net;
* proves it is preserved by the marginal `LocalNet.Split.restrict` (`trace_restrict`).

These are the building blocks for density operators, von Neumann entropy and strong
subadditivity stated directly on the abstract split net, with no matrix index substrate.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable {R : Type*} [CommRing R] {M N : Type*}
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]

/-- The partial trace over the second factor relates to the full trace through the operator
tensor decomposition: `trace_M (partialTraceRight S) = trace_{M ⊗ N} (endTensorEndAlgEquiv S)`.
On a pure operator tensor both sides are `trace Y * trace Z`. -/
theorem trace_partialTraceRight (S : Module.End R M ⊗[R] Module.End R N) :
    LinearMap.trace R M (partialTraceRight S) =
      LinearMap.trace R (M ⊗[R] N) (endTensorEndAlgEquiv S) := by
  induction S using TensorProduct.induction_on with
  | zero => simp
  | tmul Y Z =>
    rw [partialTraceRight_tmul, endTensorEndAlgEquiv_tmul, LinearMap.trace_tensorProduct',
      map_smul, smul_eq_mul]
    ring
  | add S₁ S₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end TensorProduct

namespace LinearMap

open scoped TensorProduct

variable {𝕜 ℋ A B : Type*} [Field 𝕜]
  [AddCommGroup ℋ] [Module 𝕜 ℋ]
  [AddCommGroup A] [Module 𝕜 A] [Module.Finite 𝕜 A] [Module.Free 𝕜 A]
  [AddCommGroup B] [Module 𝕜 B] [Module.Finite 𝕜 B] [Module.Free 𝕜 B]

/-- **The partial trace preserves the trace**: tracing out the second factor of a decomposition
`e : ℋ ≃ₗ A ⊗ B` and then taking the trace over `A` recovers the trace over `ℋ`. -/
theorem trace_partialTrace (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (ρ : Module.End 𝕜 ℋ) :
    LinearMap.trace 𝕜 A (LinearMap.partialTrace e ρ) = LinearMap.trace 𝕜 ℋ ρ := by
  rw [LinearMap.partialTrace_apply, TensorProduct.trace_partialTraceRight,
    AlgEquiv.apply_symm_apply]
  exact LinearMap.trace_conj' ρ e

end LinearMap

namespace LocalNet.Split

variable {sites : Type*} [DecidableEq sites] {N : LocalNet sites} {ℋ : Finset sites → Type*}
  [∀ Λ, NormedAddCommGroup (ℋ Λ)] [∀ Λ, InnerProductSpace ℂ (ℋ Λ)]
  [∀ Λ, FiniteDimensional ℂ (ℋ Λ)]
  (S : Split N ℋ)

/-- The **trace** on a local algebra of a split net: the canonical operator trace on the action
space `ℋ Λ`, transported along the type I identification `act Λ`. -/
noncomputable def trace (Λ : Finset sites) : N.algebra Λ →ₗ[ℂ] ℂ :=
  LinearMap.trace ℂ (ℋ Λ) ∘ₗ (S.act Λ).toLinearMap

theorem trace_apply (Λ : Finset sites) (X : N.algebra Λ) :
    S.trace Λ X = LinearMap.trace ℂ (ℋ Λ) (S.act Λ X) :=
  rfl

/-- **The marginal preserves the trace**: `trace (restrict h M) = trace M`. The split partial
trace is trace-preserving, the property that makes it the Schrödinger-picture dual of the
isotony embedding. -/
theorem trace_restrict {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (M : N.algebra Λ') :
    S.trace Λ (S.restrict h M) = S.trace Λ' M := by
  rw [trace_apply, trace_apply, restrict_apply, AlgEquiv.apply_symm_apply,
    LinearMap.trace_partialTrace]

/-- The trace is **cyclic**: `trace (A * B) = trace (B * A)` (it is the operator trace through the
type I identification `act`, transported from `LinearMap.trace_mul_comm`). -/
theorem trace_mul_comm {Λ : Finset sites} (A B : N.algebra Λ) :
    S.trace Λ (A * B) = S.trace Λ (B * A) := by
  rw [trace_apply, trace_apply, map_mul (S.act Λ), map_mul (S.act Λ), LinearMap.trace_mul_comm]

/-- **Heisenberg / trace duality** between the isotony embedding `incl` (Heisenberg picture) and the
marginal `restrict` (Schrödinger picture): `trace (ρ · incl h X) = trace (restrict h ρ · X)`. The
marginal `restrict h` is the predual of the inclusion `incl h`. Derived purely from
`restrict_incl_mul` and `trace_restrict` (no tensor data), so it holds for the abstract net. -/
theorem trace_mul_incl {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (ρ : N.algebra Λ') (X : N.algebra Λ) :
    S.trace Λ' (ρ * N.incl h X) = S.trace Λ (S.restrict h ρ * X) := by
  have key := congrArg (S.trace Λ) (S.restrict_incl_mul h X ρ)
  rw [S.trace_restrict h (N.incl h X * ρ), S.trace_mul_comm (N.incl h X) ρ,
    S.trace_mul_comm X (S.restrict h ρ)] at key
  exact key

/-- A **density operator** of the split net at region `Λ`: an element of the local algebra whose
operator image `act Λ ρ` is positive (the Loewner order on `End ℂ (ℋ Λ)`) and whose trace is one.
Since `act` is a `*`-isomorphism (`act_star`), positivity of `act Λ ρ` is the genuine C⋆-positivity
of `ρ`; this is the representation-free analogue of a density matrix, stated with no index basis. -/
def IsDensity {Λ : Finset sites} (ρ : N.algebra Λ) : Prop :=
  0 ≤ S.act Λ ρ ∧ S.trace Λ ρ = 1

theorem IsDensity.trace_eq_one {Λ : Finset sites} {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    S.trace Λ ρ = 1 :=
  hρ.2

theorem IsDensity.nonneg {Λ : Finset sites} {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    0 ≤ S.act Λ ρ :=
  hρ.1

end LocalNet.Split
