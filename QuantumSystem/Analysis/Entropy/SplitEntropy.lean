module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import QuantumSystem.Analysis.Entropy.SplitTrace

/-!
# Von Neumann entropy on a split net

The von Neumann entropy of a state of a split net, stated **representation-free** on the local
C⋆-algebra. The local algebra `N.algebra Λ` of a split net is a unital C⋆-algebra, so it carries
the continuous functional calculus `cfc`; combined with the split trace `LocalNet.Split.trace`
this defines

  `S(ρ) = Tr (negMulLog ρ) = -Tr (ρ log ρ)`,

exactly mirroring the matrix definition `Matrix.vonNeumannEntropy` (`vonNeumannEntropy_eq_cfc_re`)
but with no index basis. Here `Real.negMulLog x = -x * log x` is Mathlib's entropy integrand, with
the `0 log 0 = 0` convention built in.

Its quantitative properties (non-negativity, strong subadditivity) are obtained in later files by
transporting the matrix theory along an orthonormal basis of the action space.
-/

@[expose] public section

namespace LocalNet.Split

variable {sites : Type*} [DecidableEq sites] {N : LocalNet sites} {ℋ : Finset sites → Type*}
  [∀ Λ, NormedAddCommGroup (ℋ Λ)] [∀ Λ, InnerProductSpace ℂ (ℋ Λ)]
  [∀ Λ, FiniteDimensional ℂ (ℋ Λ)]
  (S : Split N ℋ)

/-- **Von Neumann entropy** of a state `ρ` of a split net at region `Λ`:
`S(ρ) = Tr (negMulLog ρ)`, the representation-free analogue of `Matrix.vonNeumannEntropy`. The
trace is the split trace `Split.trace` and `negMulLog ρ` is the continuous functional calculus of
`Real.negMulLog` on the local C⋆-algebra. -/
noncomputable def entropy {Λ : Finset sites} (ρ : N.algebra Λ) : ℝ :=
  (S.trace Λ (cfc Real.negMulLog ρ)).re

theorem entropy_def {Λ : Finset sites} (ρ : N.algebra Λ) :
    S.entropy ρ = (S.trace Λ (cfc Real.negMulLog ρ)).re :=
  rfl

end LocalNet.Split
