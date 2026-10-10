/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import QuantumSystem.ForMathlib.Algebra.Order.Module.PositiveLinearMap
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TraceDual
public import QuantumSystem.InformationTheory.Entropy.Araki.FiniteDimensional
public import QuantumSystem.Notation

/-!
# Umegaki's relative entropy

Let `H` be a finite-dimensional complex Hilbert space. **Umegaki's relative entropy** of positive
functionals `ψ, φ` on `B(H) = H →L[ℂ] H`, with densities `ρ_ψ`, `ρ_φ`
(`ContinuousLinearMap.density`, `ψ(A) = tr(ρ_ψ A)`), is
`D(ψ ‖ φ) = tr ρ_ψ (log ρ_ψ - log ρ_φ)` if the support of `ψ` lies in that of `φ`, and `+∞`
otherwise (Umegaki 1962). Neither functional needs to be a state. It is defined here as the
finite-dimensional case of Araki's relative entropy: `umegakiEntropy ψ φ` is `S(ψ ‖ φ)` for `ψ, φ`
as normal functionals of the von Neumann algebra `𝓑(H)` (`PositiveLinearMap.toNormalFunctional`,
`VonNeumannAlgebra.arakiEntropy`), and Umegaki's trace formula is the theorem
`umegakiEntropy_eq_ite`. Logarithms are natural, so the unit is the nat; `log` is Mathlib's
`CFC.log`. The functionals may be taken from any type with `FunLike`, `LinearMapClass` and
`OrderHomClass` instances — positive linear maps `B(H) →ₚ[ℂ] ℂ` and states alike — and `D(ψ ‖ φ)`
depends only on the functions (`umegakiEntropy_congr`).

The support condition is stated through null ideals: `supp ψ ⊆ supp φ` means that `φ(A⋆A) = 0`
implies `ψ(A⋆A) = 0`, equivalently `s(ψ) ≤ s(φ)` for the support projections
(`VonNeumannAlgebra.NormalFunctional.supportProj_le_supportProj_iff`).

## Main definitions

* `umegakiEntropy ψ φ` — `D(ψ ‖ φ) ∈ EReal`, with notation `D(ψ ∥ φ)` in scope
  `QuantumInfo` (the code notation uses `∥`, U+2225, where the prose writes `‖`).

## Main results

* `umegakiEntropy_eq_ite`, `umegakiEntropy_eq_re_apply`,
  `umegakiEntropy_eq_top_iff` — **Umegaki's formula**.
* `umegakiEntropy_eq_sum` — the formula in orthonormal eigenbases of the
  densities, `Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² (log rᵢ - log sⱼ)`.
* `mul_log_le_umegakiEntropy` — **Klein's inequality** `ψ(1) log (ψ(1) / φ(1)) ≤ D(ψ ‖ φ)`;
  `umegakiEntropy_nonneg` — `0 ≤ D(ψ ‖ φ)` when `φ(1) ≤ ψ(1)`.
* `umegakiEntropy_eq_zero_iff` — **faithfulness**: `D(ψ ‖ φ) = 0 ↔ ψ = φ` when
  `ψ(1) = φ(1)`.
* `umegakiEntropy_smul`, `umegakiEntropy_smul_left`,
  `umegakiEntropy_smul_right` — **scaling**, `D(c ψ ‖ c φ) = c D(ψ ‖ φ)`.
* `umegakiEntropy_ne_bot`, `umegakiEntropy_self`, `umegakiEntropy_congr`.
* `ContinuousLinearMap.exists_orthonormalBasis_density_apply`,
  `ContinuousLinearMap.nonneg_of_density_apply`,
  `ContinuousLinearMap.apply_eq_sum_of_density_apply` — a positive functional in an orthonormal
  eigenbasis of its density, `f(A) = Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫`.
* `ContinuousLinearMap.mul_norm_inner_sq_eq_zero_of_apply_star_mul_self`,
  `ContinuousLinearMap.apply_star_mul_self_eq_zero_of_apply_rankOne` — the support condition in
  eigenbases, in both directions.

Monotonicity is `QuantumSystem.InformationTheory.Entropy.Umegaki.Monotonicity` and joint convexity
`QuantumSystem.InformationTheory.Entropy.Umegaki.JointConvexity`.

## Proofs

Umegaki's formula: Araki's entropy of the purifications in the eigenbases `b`, `c` of `ρ_ψ`, `ρ_φ`
is the eigenvalue sum `Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² (log rᵢ - log sⱼ)`
(`VonNeumannAlgebra.arakiEntropy_boundedLinearOperators_eq_sum`), which is the trace formula by
`ContinuousLinearMap.trace_comp_cfc_eq_sum`; the case `+∞` is Araki's support condition
`VonNeumannAlgebra.arakiEntropy_eq_top_of_apply_star_mul_self`. Faithfulness writes the eigenvalue
sum as a sum of Kullback–Leibler terms `|⟪cⱼ, bᵢ⟫|² sⱼ klFun(rᵢ / sⱼ)`.

## Notation

`D(ψ ∥ φ)` is `umegakiEntropy ψ φ`; activate it with `open scoped QuantumInfo`.

## References

* H. Umegaki, *Conditional expectation in an operator algebra IV (entropy and information)*,
  Kodai Math. Sem. Rep. 14 (1962), 59–85.
* H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976), 809–833.
* M. Ohya, D. Petz, *Quantum Entropy and Its Use*, Springer (1993).
-/

@[expose] public section

open ContinuousLinearMap
open InnerProductSpace (rankOne)
open scoped InnerProductSpace ComplexOrder VonNeumannAlgebra Araki NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-! ### Eigenbases of densities -/

namespace ContinuousLinearMap

variable {G : Type*} [FunLike G (H →L[ℂ] H) ℂ] [LinearMapClass G ℂ (H →L[ℂ] H) ℂ]

/-- The density of a positive functional has an orthonormal eigenbasis with nonnegative
eigenvalues (the spectral theorem, `LinearMap.IsSymmetric.eigenvectorBasis`). -/
theorem exists_orthonormalBasis_density_apply [OrderHomClass G (H →L[ℂ] H) ℂ] (f : G) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H) (r : Fin (Module.finrank ℂ H) → ℝ),
      (∀ i, 0 ≤ r i) ∧ ∀ i, density f (b i) = (r i : ℂ) • b i := by
  have hpos := (nonneg_iff_isPositive.1 (density_nonneg f)).toLinearMap
  exact ⟨hpos.isSymmetric.eigenvectorBasis rfl, hpos.isSymmetric.eigenvalues rfl,
    hpos.nonneg_eigenvalues rfl, hpos.isSymmetric.apply_eigenvectorBasis rfl⟩

variable {ι : Type*} [Fintype ι]

/-- A functional evaluated in an orthonormal eigenbasis `b` of its density, with eigenvalues `r`:
`f(A) = tr(ρ_f A) = Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫`. -/
theorem apply_eq_sum_of_density_apply (f : G) (b : OrthonormalBasis ι ℂ H) {r : ι → ℝ}
    (hb : ∀ i, density f (b i) = (r i : ℂ) • b i) (A : H →L[ℂ] H) :
    f A = ∑ i, (r i : ℂ) * ⟪b i, A (b i)⟫_ℂ := by
  rw [← trace_density_comp, trace_comp_comm', trace_comp_eq_sum b hb]

/-- `f(1) = Σᵢ rᵢ` in an orthonormal eigenbasis of the density. -/
theorem apply_one_eq_sum_of_density_apply (f : G) (b : OrthonormalBasis ι ℂ H) {r : ι → ℝ}
    (hb : ∀ i, density f (b i) = (r i : ℂ) • b i) : f 1 = ((∑ i, r i : ℝ) : ℂ) := by
  classical
  rw [apply_eq_sum_of_density_apply f b hb, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_apply_eq_self, b.inner_eq_one, mul_one]

/-- The eigenvalues of the density of a positive functional are nonnegative:
`rᵢ = ⟪bᵢ, ρ_f bᵢ⟫ = f(|bᵢ⟩⟨bᵢ|) ≥ 0`. -/
theorem nonneg_of_density_apply [OrderHomClass G (H →L[ℂ] H) ℂ] {f : G}
    {b : OrthonormalBasis ι ℂ H} {r : ι → ℝ} (hb : ∀ i, density f (b i) = (r i : ℂ) • b i)
    (i : ι) : 0 ≤ r i := by
  have h := map_nonneg f (nonneg_iff_isPositive.2
    (InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) (b i)))
  rw [← inner_density_apply, hb, inner_smul_right, b.inner_eq_one, mul_one] at h
  exact_mod_cast h

/-- **The support condition in eigenbases.** If the null ideal of `φ` lies in that of `ψ`, then for
orthonormal eigenbases `b`, `c` of the densities with eigenvalues `r`, `s`,
`rᵢ |⟪cⱼ, bᵢ⟫|² = 0` whenever `sⱼ = 0`: test the null ideals on the projection `|cⱼ⟩⟨cⱼ|`. -/
theorem mul_norm_inner_sq_eq_zero_of_apply_star_mul_self [OrderHomClass G (H →L[ℂ] H) ℂ]
    {G' : Type*} [FunLike G' (H →L[ℂ] H) ℂ] [LinearMapClass G' ℂ (H →L[ℂ] H) ℂ] {ψ : G} {φ : G'}
    (h : ∀ A : H →L[ℂ] H, φ (star A * A) = 0 → ψ (star A * A) = 0)
    {b c : OrthonormalBasis ι ℂ H} {r s : ι → ℝ}
    (hb : ∀ i, density ψ (b i) = (r i : ℂ) • b i) (hc : ∀ j, density φ (c j) = (s j : ℂ) • c j)
    (i j : ι) (hj : s j = 0) : r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 = 0 := by
  classical
  have hP := InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) (c.norm_eq_one j)
  have hP' : star (rankOne ℂ (c j) (c j)) * rankOne ℂ (c j) (c j) = rankOne ℂ (c j) (c j) := by
    rw [hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
  have hφ : φ (star (rankOne ℂ (c j) (c j)) * rankOne ℂ (c j) (c j)) = 0 := by
    rw [hP', ← inner_density_apply, hc, inner_smul_right, hj, Complex.ofReal_zero, zero_mul]
  have hψ := h _ hφ
  rw [hP', ← inner_density_apply, inner_apply_self_eq_sum b hb, Complex.ofReal_eq_zero] at hψ
  have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
    mul_nonneg (nonneg_of_density_apply hb k) (sq_nonneg _)).mp hψ i
    (Finset.mem_univ i)
  rwa [norm_inner_symm] at this

/-- **The support condition from eigenbases.** If for an orthonormal eigenbasis `c` of the
density of `φ`, with eigenvalues `s`, `ψ` vanishes on `|cₖ⟩⟨cₖ|` whenever `sₖ = 0`, then the
null ideal of `φ` lies in that of `ψ`: `φ(Z⋆Z) = Σₖ sₖ ‖Z cₖ‖²` kills `Z cₖ` for `sₖ > 0`, and
`ψ(Z⋆Z) = Σₖ ⟪ρ_ψ cₖ, Z⋆Z cₖ⟫` with `ρ_ψ cₖ = 0` for `sₖ = 0`. -/
theorem apply_star_mul_self_eq_zero_of_apply_rankOne [OrderHomClass G (H →L[ℂ] H) ℂ]
    {G' : Type*} [FunLike G' (H →L[ℂ] H) ℂ] [LinearMapClass G' ℂ (H →L[ℂ] H) ℂ]
    [OrderHomClass G' (H →L[ℂ] H) ℂ] {ψ : G} {φ : G'} {c : OrthonormalBasis ι ℂ H} {s : ι → ℝ}
    (hc : ∀ k, density φ (c k) = (s k : ℂ) • c k)
    (h : ∀ k, s k = 0 → ψ (rankOne ℂ (c k) (c k)) = 0) (Z : H →L[ℂ] H)
    (hZ : φ (star Z * Z) = 0) : ψ (star Z * Z) = 0 := by
  have hZZ : ∀ x, ⟪x, (star Z * Z) x⟫_ℂ = ((‖Z x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    change ⟪x, adjoint Z (Z x)⟫_ℂ = _
    rw [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [apply_eq_sum_of_density_apply φ c hc] at hZ
  simp_rw [hZZ, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hZ
  have hk := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
    mul_nonneg (nonneg_of_density_apply hc k) (sq_nonneg _)).mp hZ
  have hρ := density_nonneg ψ
  rw [← trace_density_comp, LinearMap.trace_eq_sum_inner _ c]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [coe_coe, comp_apply]
  by_cases hs0 : s k = 0
  · have h0 : density ψ (c k) = 0 := apply_eq_zero_of_inner_apply_self_eq_zero hρ
      (by rw [inner_density_apply]; exact h k hs0)
    rw [← adjoint_inner_left, (IsSelfAdjoint.of_nonneg hρ).adjoint_eq, h0, inner_zero_left]
  · have hZk : Z (c k) = 0 := by
      have := hk k (Finset.mem_univ k)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
        ((mul_eq_zero.mp this).resolve_left hs0))
    change ⟪c k, density ψ (adjoint Z (Z (c k)))⟫_ℂ = 0
    rw [hZk, map_zero, map_zero, inner_zero_right]

end ContinuousLinearMap

/-! ### Definition -/

section Definition

variable {G G' : Type*} [FunLike G (H →L[ℂ] H) ℂ] [LinearMapClass G ℂ (H →L[ℂ] H) ℂ]
  [OrderHomClass G (H →L[ℂ] H) ℂ] [FunLike G' (H →L[ℂ] H) ℂ] [LinearMapClass G' ℂ (H →L[ℂ] H) ℂ]
  [OrderHomClass G' (H →L[ℂ] H) ℂ]

/-- **Umegaki's relative entropy** `D(ψ ‖ φ)` of positive functionals on `B(H)`, `H`
finite-dimensional (Umegaki 1962), defined as Araki's relative entropy `S(ψ ‖ φ)` of `ψ` and `φ` as
normal functionals of `𝓑(H)` (`PositiveLinearMap.toNormalFunctional`). Neither functional needs to
be a state: the definition covers states as well as unnormalised references such as the trace in
`D(ω ‖ tr) = -S(ω)`. Umegaki's formula — `tr ρ_ψ (log ρ_ψ - log ρ_φ)` if `supp ψ ⊆ supp φ`, and
`+∞` otherwise — is `umegakiEntropy_eq_ite`. Logarithms are natural, so the unit is the nat.

The functionals are taken from any types with `FunLike`, `LinearMapClass` and `OrderHomClass`
instances, so that positive linear maps `B(H) →ₚ[ℂ] ℂ` and states `State B(H)` are covered alike;
the value depends only on the functions (`umegakiEntropy_congr`). -/
noncomputable def umegakiEntropy (ψ : G) (φ : G') : EReal :=
  S⟦(PositiveLinearMap.ofClass ψ).toNormalFunctional ∥
    (PositiveLinearMap.ofClass φ).toNormalFunctional⟧

/-- `D(ψ ∥ φ)` is Umegaki's relative entropy `umegakiEntropy ψ φ`. -/
scoped[QuantumInfo] notation "D(" ψ " ∥ " φ ")" => umegakiEntropy ψ φ

open scoped QuantumInfo

variable (ψ : G) (φ : G')

/-- `D(ψ ‖ φ)` is Araki's `S(ψ ‖ φ)` on `𝓑(H)`. -/
theorem umegakiEntropy_def :
    D(ψ ∥ φ) = S⟦(PositiveLinearMap.ofClass ψ).toNormalFunctional ∥
      (PositiveLinearMap.ofClass φ).toNormalFunctional⟧ :=
  rfl

/-- `D(ψ ‖ φ)` depends only on the functions `ψ`, `φ`. -/
theorem umegakiEntropy_congr {G₁ G₁' : Type*} [FunLike G₁ (H →L[ℂ] H) ℂ]
    [LinearMapClass G₁ ℂ (H →L[ℂ] H) ℂ] [OrderHomClass G₁ (H →L[ℂ] H) ℂ]
    [FunLike G₁' (H →L[ℂ] H) ℂ] [LinearMapClass G₁' ℂ (H →L[ℂ] H) ℂ]
    [OrderHomClass G₁' (H →L[ℂ] H) ℂ] {ψ₁ : G₁} {φ₁ : G₁'} (hψ : ∀ A, ψ A = ψ₁ A)
    (hφ : ∀ A, φ A = φ₁ A) : D(ψ ∥ φ) = D(ψ₁ ∥ φ₁) := by
  have e₁ : (PositiveLinearMap.ofClass ψ).toNormalFunctional =
      (PositiveLinearMap.ofClass ψ₁).toNormalFunctional :=
    Subtype.ext (PositiveLinearMap.ext fun x => hψ x)
  have e₂ : (PositiveLinearMap.ofClass φ).toNormalFunctional =
      (PositiveLinearMap.ofClass φ₁).toNormalFunctional :=
    Subtype.ext (PositiveLinearMap.ext fun x => hφ x)
  rw [umegakiEntropy_def, umegakiEntropy_def, e₁, e₂]

/-- `D(ψ ‖ φ) ≠ -∞`. -/
theorem umegakiEntropy_ne_bot : D(ψ ∥ φ) ≠ ⊥ :=
  VonNeumannAlgebra.arakiEntropy_ne_bot _ _

/-- `D(ψ ‖ ψ) = 0`. -/
@[simp] theorem umegakiEntropy_self : D(ψ ∥ ψ) = 0 :=
  VonNeumannAlgebra.arakiEntropy_self _

variable {ψ φ}

/-- **Klein's inequality**: `ψ(1) log (ψ(1) / φ(1)) ≤ D(ψ ‖ φ)`, for positive functionals of any
mass (Araki's `VonNeumannAlgebra.mul_log_le_arakiEntropy`). With Mathlib's conventions the left side
is `0` when `ψ(1) = 0` or `φ(1) = 0`. -/
theorem mul_log_le_umegakiEntropy :
    (((ψ 1).re * Real.log ((ψ 1).re / (φ 1).re) : ℝ) : EReal) ≤ D(ψ ∥ φ) :=
  VonNeumannAlgebra.mul_log_le_arakiEntropy (PositiveLinearMap.ofClass ψ).toNormalFunctional
    (PositiveLinearMap.ofClass φ).toNormalFunctional

/-- **Klein's inequality**, normalised form: `0 ≤ D(ψ ‖ φ)` when `φ(1) ≤ ψ(1)`, in particular for
two states; a consequence of `mul_log_le_umegakiEntropy`, since `ψ(1) log (ψ(1) / φ(1)) ≥ 0` then. -/
theorem umegakiEntropy_nonneg (h : (φ 1).re ≤ (ψ 1).re) : 0 ≤ D(ψ ∥ φ) :=
  VonNeumannAlgebra.arakiEntropy_nonneg h

/-! ### Umegaki's formula -/

/-- **The support condition, `+∞` side**: if `φ(A⋆A) = 0` but `ψ(A⋆A) ≠ 0` for some `A`, then
`D(ψ ‖ φ) = +∞` (`VonNeumannAlgebra.arakiEntropy_eq_top_of_apply_star_mul_self`). -/
theorem umegakiEntropy_eq_top_of_apply_star_mul_self (A : H →L[ℂ] H) (hφ : φ (star A * A) = 0)
    (hψ : ψ (star A * A) ≠ 0) : D(ψ ∥ φ) = ⊤ :=
  VonNeumannAlgebra.arakiEntropy_eq_top_of_apply_star_mul_self (x := ⟨A, trivial⟩) hφ hψ

variable {ι : Type*} [Fintype ι]

/-- **Umegaki's formula in eigenbases.** For orthonormal eigenbases `b`, `c` of the densities of
`ψ`, `φ` with eigenvalues `r`, `s` and `supp ψ ⊆ supp φ`,
`D(ψ ‖ φ) = Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² (log rᵢ - log sⱼ)`. -/
theorem umegakiEntropy_eq_sum (h : ∀ A : H →L[ℂ] H, φ (star A * A) = 0 → ψ (star A * A) = 0)
    {b c : OrthonormalBasis ι ℂ H} {r s : ι → ℝ} (hb : ∀ i, density ψ (b i) = (r i : ℂ) • b i)
    (hc : ∀ j, density φ (c j) = (s j : ℂ) • c j) :
    D(ψ ∥ φ) =
      ((∑ i, ∑ j, r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 * (Real.log (r i) - Real.log (s j)) : ℝ) : EReal) :=
  VonNeumannAlgebra.arakiEntropy_boundedLinearOperators_eq_sum (nonneg_of_density_apply hb)
    (nonneg_of_density_apply hc) (fun x => apply_eq_sum_of_density_apply ψ b hb x)
    (fun x => apply_eq_sum_of_density_apply φ c hc x)
    (mul_norm_inner_sq_eq_zero_of_apply_star_mul_self h hb hc)

/-- The trace in Umegaki's formula, in eigenbases: `tr ρ_ψ (log ρ_ψ - log ρ_φ)` is
`Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² (log rᵢ - log sⱼ)`. -/
theorem trace_density_comp_log_sub_log {b c : OrthonormalBasis ι ℂ H} {r s : ι → ℝ}
    (hb : ∀ i, density ψ (b i) = (r i : ℂ) • b i) (hc : ∀ j, density φ (c j) = (s j : ℂ) • c j) :
    Tr (density ψ ∘L (CFC.log (density ψ) - CFC.log (density φ))) =
      ((∑ i, ∑ j, r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 * (Real.log (r i) - Real.log (s j)) : ℝ) : ℂ) := by
  classical
  have hψsa : IsSelfAdjoint (density ψ) := IsSelfAdjoint.of_nonneg (density_nonneg ψ)
  have hφsa : IsSelfAdjoint (density φ) := IsSelfAdjoint.of_nonneg (density_nonneg φ)
  rw [comp_sub, toLinearMap_sub, map_sub, CFC.log, CFC.log, trace_comp_cfc_eq_sum hψsa b hb,
    trace_comp_cfc_eq_sum hφsa c hc]
  have h₁ : ∀ i, ⟪b i, density ψ (b i)⟫_ℂ = r i := fun i => by
    rw [hb, inner_smul_right, b.inner_eq_one, mul_one]
  have h₂ : ∀ j, ⟪c j, density ψ (c j)⟫_ℂ = ((∑ i, r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun j => by
    rw [inner_apply_self_eq_sum b hb]
    simp_rw [norm_inner_symm]
  simp_rw [h₁, h₂]
  push_cast
  rw [Finset.sum_comm (f := fun i j => (r i : ℂ) * (‖⟪c j, b i⟫_ℂ‖ : ℂ) ^ 2 *
    ((Real.log (r i) : ℂ) - (Real.log (s j) : ℂ)))]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hP := c.sum_sq_norm_inner_right (b i)
    rw [b.norm_eq_one, one_pow] at hP
    have hP' : ∑ j, ((‖⟪c j, b i⟫_ℂ‖ : ℂ)) ^ 2 = 1 := by
      exact_mod_cast hP
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP', mul_one, mul_comm]
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring

/-- **Umegaki's formula**: `D(ψ ‖ φ) = tr ρ_ψ (log ρ_ψ - log ρ_φ)` if the null ideal of `φ` lies in
that of `ψ` (`supp ψ ⊆ supp φ`), and `+∞` otherwise. -/
theorem umegakiEntropy_eq_ite
    [Decidable (∀ A : H →L[ℂ] H, φ (star A * A) = 0 → ψ (star A * A) = 0)] :
    D(ψ ∥ φ) = if ∀ A : H →L[ℂ] H, φ (star A * A) = 0 → ψ (star A * A) = 0 then
      (((Tr (density ψ ∘L (CFC.log (density ψ) - CFC.log (density φ)))).re : ℝ) : EReal)
    else ⊤ := by
  split_ifs with h
  · obtain ⟨b, r, hr, hb⟩ := exists_orthonormalBasis_density_apply ψ
    obtain ⟨c, s, hs, hc⟩ := exists_orthonormalBasis_density_apply φ
    rw [umegakiEntropy_eq_sum h hb hc, trace_density_comp_log_sub_log hb hc,
      Complex.ofReal_re]
  · push Not at h
    obtain ⟨A, hφ, hψ⟩ := h
    exact umegakiEntropy_eq_top_of_apply_star_mul_self A hφ hψ

/-- **Umegaki's formula**, finite case, as an expectation value:
`D(ψ ‖ φ) = Re ψ(log ρ_ψ - log ρ_φ)` when `supp ψ ⊆ supp φ`. -/
theorem umegakiEntropy_eq_re_apply
    (h : ∀ A : H →L[ℂ] H, φ (star A * A) = 0 → ψ (star A * A) = 0) :
    D(ψ ∥ φ) = (((ψ (CFC.log (density ψ) - CFC.log (density φ))).re : ℝ) : EReal) := by
  classical
  rw [umegakiEntropy_eq_ite, ite_eq_left_iff.mpr fun h' => absurd h h', trace_density_comp]

/-- **Umegaki's formula**, infinite case: `D(ψ ‖ φ) = +∞` iff `supp ψ ⊄ supp φ`. -/
theorem umegakiEntropy_eq_top_iff :
    D(ψ ∥ φ) = ⊤ ↔ ∃ A : H →L[ℂ] H, φ (star A * A) = 0 ∧ ψ (star A * A) ≠ 0 := by
  classical
  refine ⟨fun hD => ?_, fun ⟨A, hφ, hψ⟩ => umegakiEntropy_eq_top_of_apply_star_mul_self A hφ hψ⟩
  by_contra! hne
  rw [umegakiEntropy_eq_ite, ite_eq_left_iff.mpr fun h' => absurd hne h'] at hD
  exact EReal.coe_ne_top _ hD

end Definition

open scoped QuantumInfo

/-! ### Scaling -/

section Scaling

variable {ψ φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ}

/-- **Scaling the second functional**: `D(ψ ‖ c φ) = D(ψ ‖ φ) - ψ(1) log c` for `c > 0`. -/
theorem umegakiEntropy_smul_right {c : ℝ≥0} (hc : 0 < c) :
    D(ψ ∥ c • φ) = D(ψ ∥ φ) - (((ψ 1).re * Real.log c : ℝ) : EReal) :=
  VonNeumannAlgebra.arakiEntropy_of_apply_eq_mul_right (NNReal.coe_pos.mpr hc) fun x => by
    change (c • φ) (x : H →L[ℂ] H) = ((c : ℝ) : ℂ) * φ (x : H →L[ℂ] H)
    simp [NNReal.smul_def]

/-- **Scaling the first functional**: `D(c ψ ‖ φ) = c (D(ψ ‖ φ) + ψ(1) log c)`. -/
theorem umegakiEntropy_smul_left (c : ℝ≥0) :
    D(c • ψ ∥ φ) = ((c : ℝ) : EReal) * (D(ψ ∥ φ) + (((ψ 1).re * Real.log c : ℝ) : EReal)) :=
  VonNeumannAlgebra.arakiEntropy_of_apply_eq_mul_left fun x => by
    change (c • ψ) (x : H →L[ℂ] H) = ((c : ℝ) : ℂ) * ψ (x : H →L[ℂ] H)
    simp [NNReal.smul_def]

/-- **Positive homogeneity**: `D(c ψ ‖ c φ) = c D(ψ ‖ φ)` for `c ≥ 0`. -/
theorem umegakiEntropy_smul (c : ℝ≥0) : D(c • ψ ∥ c • φ) = ((c : ℝ) : EReal) * D(ψ ∥ φ) := by
  rcases eq_zero_or_pos c with rfl | hc
  · rw [umegakiEntropy_smul_left, NNReal.coe_zero, EReal.coe_zero, zero_mul, zero_mul]
  rw [umegakiEntropy_smul_left, umegakiEntropy_smul_right hc, EReal.sub_add_cancel]

end Scaling

/-! ### Faithfulness -/

section Faithfulness

variable {G : Type*} [FunLike G (H →L[ℂ] H) ℂ] [LinearMapClass G ℂ (H →L[ℂ] H) ℂ]
  [OrderHomClass G (H →L[ℂ] H) ℂ] {ψ φ : G}

/-- **Faithfulness**: for positive functionals of equal mass, `D(ψ ‖ φ) = 0` iff `ψ = φ`. The mass
condition cannot be dropped: for a rank-one projection `P` on `ℂ²`, `D(tr(P ·) ‖ tr) = 0`.

In eigenbases, `D(ψ ‖ φ) = Σᵢⱼ |⟪cⱼ, bᵢ⟫|² sⱼ klFun(rᵢ / sⱼ) + Σᵢⱼ |⟪cⱼ, bᵢ⟫|² (rᵢ - sⱼ)`; the
second sum is `ψ(1) - φ(1) = 0` and the first has nonnegative terms, so `rᵢ = sⱼ` whenever
`⟪cⱼ, bᵢ⟫ ≠ 0`, i.e. `⟪cⱼ, ρ_ψ bᵢ⟫ = ⟪cⱼ, ρ_φ bᵢ⟫`. -/
theorem umegakiEntropy_eq_zero_iff (h1 : ψ 1 = φ 1) : D(ψ ∥ φ) = 0 ↔ ψ = φ := by
  classical
  refine ⟨fun hD => ?_, fun h => h ▸ umegakiEntropy_self ψ⟩
  by_cases h : ∀ A : H →L[ℂ] H, φ (star A * A) = 0 → ψ (star A * A) = 0
  swap
  · push Not at h
    obtain ⟨A, hφ, hψ⟩ := h
    rw [umegakiEntropy_eq_top_of_apply_star_mul_self A hφ hψ] at hD
    exact absurd hD EReal.top_ne_zero
  obtain ⟨b, r, hr, hb⟩ := exists_orthonormalBasis_density_apply ψ
  obtain ⟨c, s, hs, hc⟩ := exists_orthonormalBasis_density_apply φ
  have hsupp := mul_norm_inner_sq_eq_zero_of_apply_star_mul_self h hb hc
  set w : _ → _ → ℝ := fun i j => ‖⟪c j, b i⟫_ℂ‖ ^ 2 with hw
  rw [umegakiEntropy_eq_sum h hb hc, EReal.coe_eq_zero] at hD
  -- the eigenvalue sum as Kullback–Leibler terms plus mass differences
  have hterm : ∀ i j, r i * w i j * (Real.log (r i) - Real.log (s j)) =
      w i j * s j * InformationTheory.klFun (r i / s j) + w i j * (r i - s j) := fun i j => by
    unfold InformationTheory.klFun
    rcases (hs j).lt_or_eq with hsj | hsj
    · rcases (hr i).lt_or_eq with hri | hri
      · rw [Real.log_div hri.ne' hsj.ne']
        field_simp
        ring
      · simp [← hri]
    · have := hsupp i j hsj.symm
      simp only [← hsj, div_zero, mul_zero, Real.log_zero, zero_mul, sub_zero, zero_add]
      linear_combination (Real.log (r i)) * this - this
  have hmass : ∑ i, ∑ j, w i j * (r i - s j) = 0 := by
    have hrow : ∀ i, ∑ j, w i j = 1 := fun i => by
      have hP := c.sum_sq_norm_inner_right (b i)
      rwa [b.norm_eq_one, one_pow] at hP
    have hcol : ∀ j, ∑ i, w i j = 1 := fun j => by
      have hP := b.sum_sq_norm_inner_right (c j)
      rw [c.norm_eq_one, one_pow] at hP
      simpa only [hw, norm_inner_symm] using hP
    have hψ1 := apply_one_eq_sum_of_density_apply ψ b hb
    have hφ1 := apply_one_eq_sum_of_density_apply φ c hc
    have hrs : ∑ i, r i = ∑ j, s j := by
      have := h1
      rw [hψ1, hφ1] at this
      exact_mod_cast this
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => w i j * s j)]
    simp_rw [← Finset.sum_mul, hcol, hrow, one_mul, hrs, sub_self]
  have hkl : ∑ i, ∑ j, w i j * s j * InformationTheory.klFun (r i / s j) = 0 := by
    have h2 : ∑ i, ∑ j, r i * w i j * (Real.log (r i) - Real.log (s j)) = 0 := hD
    simp_rw [hterm, Finset.sum_add_distrib] at h2
    linarith
  have hnonneg : ∀ i j, 0 ≤ w i j * s j * InformationTheory.klFun (r i / s j) := fun i j =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (hs j))
      (InformationTheory.klFun_nonneg (div_nonneg (hr i) (hs j)))
  have hzero : ∀ i j, w i j * s j * InformationTheory.klFun (r i / s j) = 0 := fun i j =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnonneg i j).mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => hnonneg i j).mp hkl i (Finset.mem_univ i)) j
      (Finset.mem_univ j)
  -- `⟪cⱼ, bᵢ⟫ rᵢ = ⟪cⱼ, bᵢ⟫ sⱼ`
  have hstep : ∀ i j, (r i : ℂ) * ⟪c j, b i⟫_ℂ = (s j : ℂ) * ⟪c j, b i⟫_ℂ := fun i j => by
    by_cases hcb : ⟪c j, b i⟫_ℂ = 0
    · rw [hcb, mul_zero, mul_zero]
    have hw0 : w i j ≠ 0 := by simpa [hw] using hcb
    rcases (hs j).lt_or_eq with hsj | hsj
    · rcases mul_eq_zero.mp (hzero i j) with h' | h'
      · exact absurd h' (mul_ne_zero hw0 hsj.ne')
      · have := (div_eq_one_iff_eq hsj.ne').mp
          ((InformationTheory.klFun_eq_zero_iff (div_nonneg (hr i) (hs j))).mp h')
        rw [this]
    · have := hsupp i j hsj.symm
      rw [← hsj, (mul_eq_zero.mp this).resolve_right hw0]
  have hdens : density ψ = density φ := by
    refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun i => ?_)
    rw [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
    refine c.toBasis.ext_elem_iff.mpr fun j => ?_
    rw [c.coe_toBasis_repr_apply, c.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.repr_apply_apply, hb, inner_smul_right, inner_apply_eq_mul c hc]
    exact hstep i j
  exact DFunLike.ext _ _ fun A => (density_eq_density_iff.mp hdens) A

end Faithfulness
