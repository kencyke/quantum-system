/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.Power
public import QuantumSystem.Analysis.SpectralTheory.ScalarSpectralMeasure
public import QuantumSystem.Analysis.UnboundedOperator.Adjoint
public import QuantumSystem.Analysis.SpectralTheory.PolarDecomposition
public import QuantumSystem.Analysis.VonNeumannAlgebra.Modular.RelativeTomita
public import QuantumSystem.Analysis.VonNeumannAlgebra.SupportProjection

/-!
# The relative modular operator

For a von Neumann algebra `M` on `H` and `ξ, η ∈ H`, the **relative modular operator** is
`Δ_{η,ξ} = S̄†S̄`, where `S̄` is the closure of the relative Tomita operator
`S_{η,ξ} : x ξ + ζ ↦ s(ξ) x⋆ η` (`VonNeumannAlgebra.relativeTomita`). As `S̄` is conjugate-linear,
closed and densely defined, `S̄†S̄`, the composite of two conjugate-linear operators
(`LinearPMap.adjointₛₗ`, `LinearPMap.compNat`), is a complex-linear, positive self-adjoint operator
(von Neumann's theorem, `LinearPMap.isSelfAdjoint_adjointₛₗ_compNat_self`).

The spectral measure `μ_ξ` of `Δ_{η,ξ}` at `ξ` is the input of Araki's relative entropy
`S(ω_ξ ‖ ω_η) = -∫ log λ dμ_ξ(λ)`. Its atom at `0` detects the support condition: `μ_ξ {0} = 0` iff
`s(ξ) ≤ s(η)`, the vector form of `ω_ξ ≪ ω_η` in the sense of *support inclusion*
`s(ω_ξ) ≤ s(ω_η)` (not domination `ω_ξ ≤ c ω_η`). No atom at `0` does not make
`-∫ log λ dμ_ξ` finite: in infinite dimensions the entropy can be `+∞` even when
`s(ξ) ≤ s(η)`.

## Without Tomita–Takesaki theory

Defining `Δ_{η,ξ}` needs no result of Tomita–Takesaki theory, only general unbounded operator
theory: `S_{η,ξ}` is well defined, densely defined and closable
(`QuantumSystem.Analysis.VonNeumannAlgebra.Modular.RelativeTomita`), and for any closed densely
defined `T` the operator `T†T` is positive self-adjoint (von Neumann's theorem,
`LinearPMap.isSelfAdjoint_adjointₛₗ_compNat_self`). The theorems of Tomita–Takesaki theory —
the polar decomposition `S̄ = J Δ^{1/2}`, `J M J = M′`, `Δ^{it} M Δ^{-it} = M`, the modular
automorphism group and the KMS condition — describe *properties* of `Δ` and are not used
anywhere in the construction of the relative entropy or in its monotonicity
(`QuantumSystem.InformationTheory.Entropy.Araki.Monotonicity`). The polar decomposition
`S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}` is the general `IsSelfAdjoint.eq_polarIsometry_compPMap`, with the
relative modular conjugation `J_{η,ξ}` (`VonNeumannAlgebra.relativeModularConj`), antiunitary for
`ξ`, `η` cyclic and separating (`VonNeumannAlgebra.relativeModularConjEquiv`, which rests on
`S_{η,ξ}† = F̄_{η,ξ}`). For a cyclic
and separating `Ω`, `Δ_{Ω,Ω}` is the modular operator of the standard subspace
`H_M = closure (M_sa Ω)` (`VonNeumannAlgebra.relativeModular_self_eq_modular`,
`QuantumSystem.Analysis.VonNeumannAlgebra.Modular.StandardSubspace`), so `S̄_{Ω,Ω} = J Δ^{1/2}` with
the modular conjugation `J` of `H_M`, `Δ^{it} H_M = H_M`, `J H_M = (H_M)' = H_{M′}` and the analytic
continuation of the modular orbits hold. Not formalised: the von Neumann algebra statements
`J M J = M′` and `Δ^{it} M Δ^{-it} = M`, the modular automorphism group `σ_t` of `M` and the KMS
condition of `ω_Ω`.

## Main definitions

* `VonNeumannAlgebra.relativeModular M η ξ` — the relative modular operator `Δ_{η,ξ} = S̄†S̄`, for
  the closure `S̄` of the relative Tomita operator.
* `VonNeumannAlgebra.relativeModularMeasure M η ξ` — its spectral measure `μ_ξ` at `ξ`.
* `VonNeumannAlgebra.relativeModularGroup M η ξ t` — the relative modular group
  `Δ_{η,ξ}^{it} = ∫_{(0,∞)} λ^{it} dE(λ)`, a group of partial isometries on `(ker Δ_{η,ξ})ᗮ`
  vanishing on `ker Δ_{η,ξ}`.

## Notation

The scoped notations `Δ[M]⟦η, ξ⟧`, `Δ[M]⟦η, ξ⟧^{1/2}`, `E_Δ[M]⟦η, ξ⟧` (the spectral measure of
`Δ_{η,ξ}`), `Δ[M]⟦η, ξ⟧^{±i t}` and `μ[M]⟦η, ξ⟧` are activated with
`open scoped VonNeumannAlgebra`.

With the algebra `M` fixed, this file writes `S⟦η, ξ⟧`, `Δ⟦η, ξ⟧` and `μ⟦η, ξ⟧` for
`S[M]⟦η, ξ⟧`, `Δ[M]⟦η, ξ⟧` and `μ[M]⟦η, ξ⟧` (local notations, not exported); the latter are
the exported `scoped` notations for `relativeTomita M η ξ`, `relativeModular M η ξ` and
`relativeModularMeasure M η ξ`. The closure `S̄_{η,ξ}` is `S⟦η, ξ⟧.closureₛₗ`. The scoped
notations `Δ[M]⟦η, ξ⟧^{1/2}`, `Δ[M]⟦η, ξ⟧^{i t}` and `Δ[M]⟦η, ξ⟧^{-i t}` write the square root
`Δ_{η,ξ}^{1/2}` and the relative modular group `Δ_{η,ξ}^{±it}`; the exponent `t` is parsed at `max`
precedence (`Δ[M]⟦η, ξ⟧^{i (s + t)}`).

## Main results

* `VonNeumannAlgebra.isSelfAdjoint_relativeModular`, `VonNeumannAlgebra.isPositive_relativeModular`
  — `Δ_{η,ξ}` is positive self-adjoint.
* `VonNeumannAlgebra.relativeModular_def` — `Δ_{η,ξ} = S̄†S̄`.
* `VonNeumannAlgebra.re_inner_eq_norm_sq_of_mem_graph_relativeModular` — `re ⟪u, Δ u⟫ = ‖S̄ u‖²`.
* `VonNeumannAlgebra.ker_relativeModular` — `ker Δ_{η,ξ} = ker S̄`.
* `VonNeumannAlgebra.relativeModularGroup_add`, `VonNeumannAlgebra.relativeModularGroup_zero` —
  `Δ_{η,ξ}^{it}` is a group of partial isometries with unit the support projection of `Δ_{η,ξ}`.
* `VonNeumannAlgebra.measure_pvm_relativeModular_singleton_zero_eq_zero_iff` — **support
  theorem**: `μ_ξ {0} = 0 ↔ s(ξ) ≤ s(η)`.
* `VonNeumannAlgebra.lintegral_measure_pvm_relativeModular_le`,
  `VonNeumannAlgebra.lintegral_measure_pvm_relativeModular_eq` — `∫ λ dμ_ξ = ‖s(ξ) η‖²`.
* `VonNeumannAlgebra.self_mem_graph_relativeModular_self`,
  `VonNeumannAlgebra.measure_pvm_relativeModular_self` — `Δ_{ξ,ξ} ξ = ξ`, hence
  `μ_ξ = ‖ξ‖² δ₁` for `Δ_{ξ,ξ}`.
* `VonNeumannAlgebra.relativeModular_apply_left`, `VonNeumannAlgebra.relativeModular_smul_left`,
  `VonNeumannAlgebra.relativeModular_smul_right` — `Δ_{w′ η, ξ} = r Δ_{η,ξ}` for `w′ ∈ M′` with
  `w′⋆ w′ η = r η`; `Δ_{a η, ξ} = |a|² Δ_{η,ξ}`; `Δ_{η, c ξ} = |c|⁻² Δ_{η,ξ}`.
* `VonNeumannAlgebra.compPMap_relativeModular_le_of_mem_commutant` — `w′ Δ_{η,ξ} ⊆ Δ_{η, w′ ξ} w′`
  for `w′ ∈ M′` with `w′⋆ w′ ξ = ξ`.
* `VonNeumannAlgebra.measure_pvm_relativeModular_apply_left`,
  `VonNeumannAlgebra.measure_pvm_relativeModular_smul_left`,
  `VonNeumannAlgebra.measure_pvm_relativeModular_smul_right`,
  `VonNeumannAlgebra.measure_pvm_relativeModular_apply_right` — the corresponding statements
  for the spectral measure `μ_ξ` (for `w′ ∈ M′` with `w′⋆ w′ ξ = ξ`, `μ_{w′ξ}` of `Δ_{η, w′ ξ}` is
  `μ_ξ` of `Δ_{η,ξ}`).
* `VonNeumannAlgebra.relativeModular_eq_of_inner_eq_left`,
  `VonNeumannAlgebra.measure_pvm_relativeModular_eq_of_inner_eq_right`,
  `VonNeumannAlgebra.measure_pvm_relativeModular_eq_of_inner_eq` — **independence of the
  vector representatives**: `μ_ξ` of `Δ_{η,ξ}` depends only on the vector functionals `ω_ξ`, `ω_η`.

Transformations along bounded intertwiners between different Hilbert spaces (spatial
isomorphisms, amplifications) are in `QuantumSystem.Analysis.VonNeumannAlgebra.Modular.Intertwiner`.

## References

* H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976).
* H. Araki, T. Masuda, *Positive cones and Lp-spaces for von Neumann algebras*, Publ. RIMS 18
  (1982), §2 — the relative modular operators and groups for vectors that are not cyclic and
  separating.
-/

@[expose] public section

open Complex ClosedSubmodule MeasureTheory
open scoped InnerProductSpace ComplexConjugate VonNeumannAlgebra LinearPMap
open InnerProductSpace (cyclicSubspace)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (η ξ : H)

/-- `S⟦η, ξ⟧` is the relative Tomita operator `S_{η,ξ}` of the algebra `M` fixed in this file. -/
local notation "S⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeTomita M η ξ

/-! ### The closure of the relative Tomita operator -/

/-- The closure `S̄_{η,ξ}` is closed. -/
lemma isClosed_closure_relativeTomita : (S⟦η, ξ⟧).closureₛₗ.IsClosedₛₗ :=
  (isClosable_relativeTomita M η ξ).isClosedₛₗ_closureₛₗ

variable {M η ξ} in
/-- `S_{η,ξ} ⊆ S̄_{η,ξ}` (`LinearPMap.le_closureₛₗ`) at a single graph point, for computations of
`S̄_{η,ξ}` on given vectors. -/
lemma mem_graph_closure_relativeTomita {p : H × H} (hp : p ∈ (S⟦η, ξ⟧).graphₛₗ) :
    p ∈ (S⟦η, ξ⟧).closureₛₗ.graphₛₗ :=
  LinearPMap.le_graphₛₗ_of_le (LinearPMap.le_closureₛₗ _) hp

/-! ### The relative modular operator -/

/-- The **relative modular operator** `Δ_{η,ξ} = S̄†S̄`, for `S̄` the closure of the relative Tomita
operator `S_{η,ξ}`: the composite of the conjugate-linear `S̄` and its conjugate-linear adjoint is
complex-linear. -/
noncomputable def relativeModular : H →ₗ.[ℂ] H :=
  (S⟦η, ξ⟧).closureₛₗ.adjointₛₗ.compNat (S⟦η, ξ⟧).closureₛₗ

/-- `Δ[M]⟦η, ξ⟧` is the relative modular operator `Δ_{η,ξ}` of the von Neumann algebra `M`. -/
scoped notation "Δ[" M "]⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeModular M η ξ

/-- `Δ⟦η, ξ⟧` is `Δ[M]⟦η, ξ⟧` for the algebra `M` fixed in this file. -/
local notation "Δ⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeModular M η ξ

/-- `Δ_{η,ξ} = S̄†S̄`. -/
lemma relativeModular_def :
    Δ⟦η, ξ⟧ = (S⟦η, ξ⟧).closureₛₗ.adjointₛₗ.compNat (S⟦η, ξ⟧).closureₛₗ :=
  rfl

variable {M η ξ} in
/-- `Δ_{η,ξ} = S̄†S̄` (`VonNeumannAlgebra.relativeModular_def`) at a single graph point, for
computations of `Δ_{η,ξ}` on given vectors. -/
lemma mem_graph_relativeModular_iff {p : H × H} :
    p ∈ (Δ⟦η, ξ⟧).graph ↔
      p ∈ ((S⟦η, ξ⟧).closureₛₗ.adjointₛₗ.compNat (S⟦η, ξ⟧).closureₛₗ).graphₛₗ := by
  rw [LinearPMap.mem_graphₛₗ_iff_mem_graph, relativeModular_def]

/-- `Δ_{η,ξ}` is self-adjoint (von Neumann's theorem). -/
theorem isSelfAdjoint_relativeModular : IsSelfAdjoint (Δ⟦η, ξ⟧) :=
  LinearPMap.isSelfAdjoint_adjointₛₗ_compNat_self (isClosed_closure_relativeTomita M η ξ)
    (LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η ξ))

/-- `Δ_{η,ξ}` is positive. -/
theorem isPositive_relativeModular : (Δ⟦η, ξ⟧).IsPositive :=
  LinearPMap.isPositive_adjointₛₗ_compNat_self
    (LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η ξ))

/-- `Δ[M]⟦η, ξ⟧^{1/2}` is the positive square root `Δ_{η,ξ}^{1/2} = |S̄_{η,ξ}|` of the relative
modular operator. -/
scoped notation "Δ[" M "]⟦" η ", " ξ "⟧^{1/2}" =>
  IsSelfAdjoint.sqrt (VonNeumannAlgebra.isSelfAdjoint_relativeModular M η ξ)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborator displaying `IsSelfAdjoint.sqrt (VonNeumannAlgebra.isSelfAdjoint_relativeModular M η ξ)`
as `Δ[M]⟦η, ξ⟧^{1/2}`; an unexpander cannot do this, since the proof argument is elided as `⋯`. -/
@[scoped delab app.IsSelfAdjoint.sqrt]
meta def delabSqrtRelativeModular : Delab := do
  let e ← getExpr
  guard <| e.appArg!.isAppOfArity ``VonNeumannAlgebra.isSelfAdjoint_relativeModular 7
  let M ← withAppArg <| withNaryArg 4 delab
  let η ← withAppArg <| withNaryArg 5 delab
  let ξ ← withAppArg <| withNaryArg 6 delab
  `(Δ[$M]⟦$η, $ξ⟧^{1/2})

/-- `E_Δ[M]⟦η, ξ⟧` is the projection-valued (spectral) measure `E_Δ` of the relative modular
operator `Δ_{η,ξ}` on the Borel sets of `ℝ`, so that `E_Δ[M]⟦η, ξ⟧ (Set.Ioi 0)` is `E_Δ((0, ∞))`. -/
scoped notation "E_Δ[" M "]⟦" η ", " ξ "⟧" =>
  IsSelfAdjoint.pvm (VonNeumannAlgebra.isSelfAdjoint_relativeModular M η ξ)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborator displaying `IsSelfAdjoint.pvm (VonNeumannAlgebra.isSelfAdjoint_relativeModular M η ξ)`
as `E_Δ[M]⟦η, ξ⟧`; as for `Δ[M]⟦η, ξ⟧^{1/2}`, an unexpander cannot see the elided proof argument. -/
@[scoped delab app.IsSelfAdjoint.pvm]
meta def delabPvmRelativeModular : Delab := do
  let e ← getExpr
  guard <| e.appArg!.isAppOfArity ``VonNeumannAlgebra.isSelfAdjoint_relativeModular 7
  let M ← withAppArg <| withNaryArg 4 delab
  let η ← withAppArg <| withNaryArg 5 delab
  let ξ ← withAppArg <| withNaryArg 6 delab
  `(E_Δ[$M]⟦$η, $ξ⟧)

/-- The **relative modular group** `t ↦ Δ_{η,ξ}^{it} = ∫_{(0,∞)} λ^{it} dE(λ)`
(`IsSelfAdjoint.imaginaryPower`, with `0^{it} = 0`): partial isometries with initial and final space
`E_Δ((0, ∞)) H = (ker Δ_{η,ξ})ᗮ` (`IsSelfAdjoint.pvm_Ioi_eq_starProjection_orthogonal`,
`IsSelfAdjoint.norm_imaginaryPower_apply`,
`IsSelfAdjoint.pvm_Ioi_imaginaryPower_apply`), strongly continuous in `t`
(`IsSelfAdjoint.continuous_imaginaryPower_apply`), and a group of partial isometries on
`E_Δ((0, ∞)) H`: `Δ_{η,ξ}^{i(s+t)} = Δ_{η,ξ}^{is} Δ_{η,ξ}^{it}`
(`VonNeumannAlgebra.relativeModularGroup_add`) with unit `Δ_{η,ξ}^{i0} = E_Δ((0, ∞))`
(`VonNeumannAlgebra.relativeModularGroup_zero`). It is the family of Araki–Masuda 1982 and of Connes'
cocycle `(Dη : Dξ)_t = Δ_{η,ξ}^{it} Δ_ξ^{-it}`. For `ξ` cyclic and `η` separating, `Δ_{η,ξ}` is injective
(`VonNeumannAlgebra.ker_relativeModular_eq_bot`) and `Δ_{η,ξ}^{it}` is the unitary group generated
by `log Δ_{η,ξ}` (`VonNeumannAlgebra.relativeModularGroup_eq_unitaryGroup`); for a cyclic and separating `Ω`,
`Δ_{Ω,Ω}^{it}` is the modular group of the standard subspace `H_M`
(`VonNeumannAlgebra.relativeModularGroup_self`). -/
noncomputable def relativeModularGroup (t : ℝ) : H →L[ℂ] H :=
  (isSelfAdjoint_relativeModular M η ξ).imaginaryPower t

/-- `Δ[M]⟦η, ξ⟧^{i t}` is the partial isometry `Δ_{η,ξ}^{it}` of the relative modular group. The
exponent is parsed at `max` precedence, so a compound exponent needs parentheses. -/
scoped notation "Δ[" M "]⟦" η ", " ξ "⟧^{i " t:max "}" => VonNeumannAlgebra.relativeModularGroup M η ξ t

/-- `Δ[M]⟦η, ξ⟧^{-i t}` is `Δ_{η,ξ}^{-it} = Δ_{η,ξ}^{i(-t)}`. -/
scoped notation "Δ[" M "]⟦" η ", " ξ "⟧^{-i " t:max "}" =>
  VonNeumannAlgebra.relativeModularGroup M η ξ (-t)

/-- Displays `VonNeumannAlgebra.relativeModularGroup M η ξ t` as `Δ[M]⟦η, ξ⟧^{i t}`, and
`VonNeumannAlgebra.relativeModularGroup M η ξ (-t)` as `Δ[M]⟦η, ξ⟧^{-i t}`. -/
@[scoped app_unexpander VonNeumannAlgebra.relativeModularGroup]
meta def relativeModularGroupUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $M $η $ξ $t) => match t with
    | `(-$t') => `(Δ[$M]⟦$η, $ξ⟧^{-i $t'})
    | _ => `(Δ[$M]⟦$η, $ξ⟧^{i $t})
  | _ => throw ()

/-- **Group law** of the relative modular group: `Δ_{η,ξ}^{i(s+t)} = Δ_{η,ξ}^{is} Δ_{η,ξ}^{it}`. -/
lemma relativeModularGroup_add (s t : ℝ) :
    Δ[M]⟦η, ξ⟧^{i (s + t)} = Δ[M]⟦η, ξ⟧^{i s} * Δ[M]⟦η, ξ⟧^{i t} :=
  (isSelfAdjoint_relativeModular M η ξ).imaginaryPower_add s t

/-- The unit of the relative modular group is the support projection
`Δ_{η,ξ}^{i0} = E_Δ((0, ∞))` of `Δ_{η,ξ}`, the projection onto `(ker Δ_{η,ξ})ᗮ`
(`IsSelfAdjoint.pvm_Ioi_eq_starProjection_orthogonal`). -/
lemma relativeModularGroup_zero :
    Δ[M]⟦η, ξ⟧^{i 0} = E_Δ[M]⟦η, ξ⟧ (Set.Ioi 0) :=
  (isSelfAdjoint_relativeModular M η ξ).imaginaryPower_zero

/-- The **spectral measure** `μ_ξ = ⟪E_{Δ_{η,ξ}}(·) ξ, ξ⟫` of the relative modular operator at
`ξ`: the finite measure on `ℝ` of total mass `‖ξ‖²` whose `-∫ log λ dμ_ξ(λ)` is Araki's relative
entropy. -/
noncomputable abbrev relativeModularMeasure : Measure ℝ :=
  (E_Δ[M]⟦η, ξ⟧).measure ξ

/-- `μ[M]⟦η, ξ⟧` is the spectral measure `μ_ξ` of `Δ_{η,ξ}` at `ξ`, for the von Neumann algebra
`M`. -/
scoped notation "μ[" M "]⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeModularMeasure M η ξ

/-- `μ⟦η, ξ⟧` is `μ[M]⟦η, ξ⟧` for the algebra `M` fixed in this file. -/
local notation "μ⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeModularMeasure M η ξ

variable {M η ξ}

/-- `re ⟪u, Δ_{η,ξ} u⟫ = ‖S̄_{η,ξ} u‖²`, in graph form. -/
theorem re_inner_eq_norm_sq_of_mem_graph_relativeModular {u u' y : H}
    (hu : (u, u') ∈ (Δ⟦η, ξ⟧).graph)
    (hy : (u, y) ∈ (S⟦η, ξ⟧).closureₛₗ.graphₛₗ) : re ⟪u, u'⟫_ℂ = ‖y‖ ^ 2 :=
  (isSelfAdjoint_relativeModular M η ξ).re_inner_eq_norm_sq_of_eq_adjointₛₗ_compNat
    (relativeModular_def M η ξ) hu hy

/-- **`ker Δ_{η,ξ} = ker S̄_{η,ξ}`**, since `Δ_{η,ξ} = S̄†S̄`. -/
lemma ker_relativeModular : (Δ⟦η, ξ⟧).ker = (S⟦η, ξ⟧).closureₛₗ.ker :=
  (isSelfAdjoint_relativeModular M η ξ).ker_eq_of_eq_adjointₛₗ_compNat (relativeModular_def M η ξ)

/-- A vector `u` in the kernel of `S̄_{η,ξ}` is orthogonal to the range of the relative Tomita
operator `F_{η,ξ}` of `M′`: `F_{η,ξ} ⊆ S̄_{η,ξ}†` and `ker S̄` is a complex subspace. -/
private lemma inner_eq_zero_of_mem_graph_closure {u v v' : H}
    (hu : (u, 0) ∈ (S⟦η, ξ⟧).closureₛₗ.graphₛₗ)
    (hv : (v, v') ∈ (S[M′]⟦η, ξ⟧).graphₛₗ) : ⟪u, v'⟫_ℂ = 0 := by
  have hd := LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η ξ)
  have hadj : (v, v') ∈ (S⟦η, ξ⟧).closureₛₗ.adjointₛₗ.graphₛₗ := by
    rw [LinearPMap.adjointₛₗ_closureₛₗ (dense_domain_relativeTomita M η ξ)]
    exact LinearPMap.le_graphₛₗ_of_le (relativeTomita_commutant_le_adjoint M η ξ) hv
  have h0 := LinearPMap.inner_eq_of_mem_graphₛₗ_adjointₛₗ hd hu hadj
  rw [inner_zero_right, map_zero] at h0
  rw [← inner_conj_symm, h0, map_zero]

/-- **Support theorem.** The spectral measure `μ_ξ` of `Δ_{η,ξ}` has no atom at `0` iff
`s(ξ) ≤ s(η)`, i.e. iff the support of `ω_ξ` lies under that of `ω_η` (support inclusion, not
domination). -/
theorem measure_pvm_relativeModular_singleton_zero_eq_zero_iff :
    μ⟦η, ξ⟧ {0} = 0 ↔ M.supportProj ξ ≤ M.supportProj η := by
  set S := S⟦η, ξ⟧
  have hΔ := isSelfAdjoint_relativeModular M η ξ
  have hK : ∀ u, u ∈ (hΔ.isClosed.eigenspace ((0 : ℝ) : ℂ)).toSubmodule ↔
      (u, 0) ∈ S.closureₛₗ.graphₛₗ := fun u => by
    rw [ClosedSubmodule.mem_toSubmodule_iff, LinearPMap.IsClosed.mem_eigenspace_iff, ofReal_zero,
      zero_smul, LinearPMap.mem_graph_zero_iff_mem_ker, LinearPMap.mem_graphₛₗ_zero_iff_mem_ker,
      ← ker_relativeModular]
  have hsη := M.isStarProjection_supportProj η
  rw [hΔ.measure_pvm_singleton_eq_zero_iff, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.mem_orthogonal]
  simp_rw [hK]
  constructor
  · -- `(1 - s(η)) ξ ∈ ker S`, so `⟪(1 - s(η)) ξ, ξ⟫ = 0`.
    intro h
    rw [supportProj_le_iff_inner_eq_zero hsη (M.supportProj_mem η)]
    have hmem : ((1 - M.supportProj η) ξ, 0) ∈ S.closureₛₗ.graphₛₗ := by
      refine mem_graph_closure_relativeTomita ?_
      convert apply_mem_graph_relativeTomita (η := η) (ξ := ξ)
        (sub_mem (one_mem M) (M.supportProj_mem η)) using 2
      rw [star_sub, star_one, hsη.isSelfAdjoint.star_eq, sub_apply, one_apply_eq_self,
        supportProj_apply_self, sub_self, map_zero]
    rw [← inner_conj_symm, h _ hmem, map_zero]
  · -- `ξ` lies in the closure of the range of `F_{η,ξ}`, which is orthogonal to `ker S̄`.
    intro hle u hu
    have hs : M.supportProj η ξ = ξ := (supportProj_le_iff hsη (M.supportProj_mem η)).mp hle
    have hξ : ξ ∈ closure (Set.range fun y : M′ => (y : H →L[ℂ] H) η) := by
      rw [← coe_cyclicSubspace, ← hs]
      exact Submodule.starProjection_apply_mem _ ξ
    have hξ' : ξ ∈ closure (Set.range fun y : M′ => M′.supportProj ξ ((y : H →L[ℂ] H) η)) := by
      have h := map_mem_closure (M′.supportProj ξ).continuous hξ
        (t := Set.range fun y : M′ => M′.supportProj ξ ((y : H →L[ℂ] H) η))
        fun _ ⟨y, hy⟩ => ⟨y, by rw [← hy]⟩
      rwa [supportProj_apply_self] at h
    refine closure_minimal (s := Set.range fun y : M′ => M′.supportProj ξ ((y : H →L[ℂ] H) η))
      (t := {z | ⟪u, z⟫_ℂ = 0}) ?_ (isClosed_eq (continuous_const.inner continuous_id)
        continuous_const) hξ'
    rintro _ ⟨y, rfl⟩
    have := apply_mem_graph_relativeTomita (M := M′) (η := η) (ξ := ξ) (star_mem y.2)
    rw [star_star] at this
    exact inner_eq_zero_of_mem_graph_closure hu this

/-- **Form bound.** `∫ λ dμ_ξ(λ) ≤ ‖s(ξ) η‖²` for the spectral measure `μ_ξ` of `Δ_{η,ξ}`, since
`S̄_{η,ξ} ξ = s(ξ) η`; equality holds (`VonNeumannAlgebra.lintegral_measure_pvm_relativeModular_eq`). -/
theorem lintegral_measure_pvm_relativeModular_le :
    ∫⁻ t, ENNReal.ofReal t ∂μ⟦η, ξ⟧ ≤ ENNReal.ofReal (‖M.supportProj ξ η‖ ^ 2) :=
  (isSelfAdjoint_relativeModular M η ξ).lintegral_measure_pvm_le_norm_sq
    (relativeModular_def M η ξ)
    (mem_graph_closure_relativeTomita (self_mem_graph_relativeTomita M η ξ))

/-- **Form identity.** `∫ λ dμ_ξ(λ) = ‖s(ξ) η‖² = ‖Δ_{η,ξ}^{1/2} ξ‖²` for the spectral measure
`μ_ξ` of `Δ_{η,ξ}`, since `S̄_{η,ξ} ξ = s(ξ) η` and `S̄_{η,ξ}` is closed. -/
lemma lintegral_measure_pvm_relativeModular_eq :
    ∫⁻ t, ENNReal.ofReal t ∂μ⟦η, ξ⟧ = ENNReal.ofReal (‖M.supportProj ξ η‖ ^ 2) :=
  (isSelfAdjoint_relativeModular M η ξ).lintegral_measure_pvm_eq_norm_sq
    (relativeModular_def M η ξ) (isClosed_closure_relativeTomita M η ξ)
    (mem_graph_closure_relativeTomita (self_mem_graph_relativeTomita M η ξ))

variable (M ξ)

/-- `Δ_{ξ,ξ} ξ = ξ`: `S̄_{ξ,ξ} ξ = s(ξ) ξ = ξ` and `S̄_{ξ,ξ}† ξ = F_{ξ,ξ} ξ = s′(ξ) ξ = ξ`. -/
theorem self_mem_graph_relativeModular_self : (ξ, ξ) ∈ (Δ⟦ξ, ξ⟧).graph := by
  rw [mem_graph_relativeModular_iff, LinearPMap.mem_graphₛₗ_compNat]
  refine ⟨ξ, ?_, ?_⟩
  · simpa using mem_graph_closure_relativeTomita (self_mem_graph_relativeTomita M ξ ξ)
  · rw [LinearPMap.adjointₛₗ_closureₛₗ (dense_domain_relativeTomita M ξ ξ)]
    refine LinearPMap.le_graphₛₗ_of_le (relativeTomita_commutant_le_adjoint M ξ ξ) ?_
    simpa using self_mem_graph_relativeTomita M′ ξ ξ

/-- For `Δ_{ξ,ξ}`, the spectral measure at `ξ` is `‖ξ‖² δ₁`. -/
theorem measure_pvm_relativeModular_self :
    μ⟦ξ, ξ⟧ = (‖ξ‖₊ ^ 2) • Measure.dirac 1 :=
  (isSelfAdjoint_relativeModular M ξ ξ).measure_pvm_of_mem_graph (c := 1)
    (by simpa using self_mem_graph_relativeModular_self M ξ)

/-! ### Scaling and change of vector representatives -/

variable {M ξ} {w : H →L[ℂ] H}

/-- For `w′ ∈ M′` with `w′⋆ w′ η = r η`, `w′⋆ w′` acts as `r` on the range of `S_{η,ξ}`, which lies
in `M η`. -/
private lemma star_apply_apply_of_mem_graph (hw : w ∈ M′) {r : ℂ} (hwη : star w (w η) = r • η)
    {u v : H} (h : (u, v) ∈ (S⟦η, ξ⟧).graphₛₗ) : star w (w v) = r • v := by
  obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  have hy : M.supportProj ξ * star x ∈ M := mul_mem (M.supportProj_mem ξ) (star_mem hx)
  change star w (w ((M.supportProj ξ * star x) η)) = r • (M.supportProj ξ * star x) η
  rw [apply_apply_of_mem_commutant hw hy, apply_apply_of_mem_commutant (star_mem hw) hy, hwη,
    map_smul]

/-- **Changing `η` along the commutant.** For `w′ ∈ M′` with `w′⋆ w′ η = r η` (`r > 0`),
`Δ_{w′ η, ξ} = r Δ_{η,ξ}`: with `C = r⁻¹ w′⋆`, `S_{w′ η, ξ} = w′ S_{η,ξ}` and
`C S_{w′ η, ξ} = S_{η,ξ}`, so `w′ S̄_{η,ξ} ⊆ S̄_{w′ η, ξ}` and `C S̄_{w′ η, ξ} ⊆ S̄_{η,ξ}`. -/
theorem relativeModular_apply_left (hw : w ∈ M′) {r : ℝ} (hr : 0 < r)
    (hwη : star w (w η) = (r : ℂ) • η) :
    Δ⟦w η, ξ⟧ = (r : ℂ) • Δ⟦η, ξ⟧ := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  set C : H →L[ℂ] H := (r : ℂ)⁻¹ • star w
  have hS₂ : S⟦w η, ξ⟧ = (w : H →ₗ[ℂ] H).compPMap (S⟦η, ξ⟧) := relativeTomita_apply_left hw
  -- `w′⋆ w′ = r` on the range of `S_{η,ξ}`
  have hCw : (C : H →ₗ[ℂ] H).compPMap (S⟦w η, ξ⟧) = S⟦η, ξ⟧ := by
    rw [hS₂, ← LinearPMap.compPMap_comp]
    refine LinearPMap.ext rfl fun x hx _ => ?_
    change (r : ℂ)⁻¹ • star w (w (S⟦η, ξ⟧ ⟨x, hx⟩)) = S⟦η, ξ⟧ ⟨x, hx⟩
    rw [star_apply_apply_of_mem_graph hw hwη ((S⟦η, ξ⟧).mem_graphₛₗ ⟨x, hx⟩), inv_smul_smul₀ hr0]
  have hB : (w : H →ₗ[ℂ] H).compPMap (S⟦η, ξ⟧).closureₛₗ ≤ (S⟦w η, ξ⟧).closureₛₗ := by
    have h := LinearPMap.compPMap_closureₛₗ_le (isClosable_relativeTomita M η ξ) w
      (hS₂ ▸ isClosable_relativeTomita M (w η) ξ)
    rwa [← hS₂] at h
  have hC : (C : H →ₗ[ℂ] H).compPMap (S⟦w η, ξ⟧).closureₛₗ ≤ (S⟦η, ξ⟧).closureₛₗ := by
    have h := LinearPMap.compPMap_closureₛₗ_le (isClosable_relativeTomita M (w η) ξ) C
      (hCw ▸ isClosable_relativeTomita M η ξ)
    rwa [hCw] at h
  exact LinearPMap.adjointₛₗ_compNat_self_eq_smul
    (LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η ξ))
    (LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M (w η) ξ)) hr.ne' hB hC
    fun y y' => by
      rw [smul_apply, inner_smul_left, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left, ← ofReal_inv, conj_ofReal, ← mul_assoc, ofReal_inv,
        mul_inv_cancel₀ hr0, one_mul]

/-- **Scaling `η`.** `Δ_{a η, ξ} = |a|² Δ_{η,ξ}` for `a ≠ 0`. -/
theorem relativeModular_smul_left {a : ℂ} (ha : a ≠ 0) :
    Δ⟦a • η, ξ⟧ = ((‖a‖ ^ 2 : ℝ) : ℂ) • Δ⟦η, ξ⟧ := by
  have hw : a • (1 : H →L[ℂ] H) ∈ M′ := SMulMemClass.smul_mem a (one_mem M′)
  have h := relativeModular_apply_left (ξ := ξ) (η := η) hw (r := ‖a‖ ^ 2) (by positivity) (by
    simp only [star_smul, star_one, smul_apply, one_apply_eq_self, smul_smul, Complex.star_def]
    rw [conj_mul', ofReal_pow])
  simpa using h

/-- **Scaling `ξ`.** `Δ_{η, c ξ} = |c|⁻² Δ_{η,ξ}` for `c ≠ 0`: with `B = c̄⁻¹` and `C = c̄`,
`S_{η, c ξ} = B S_{η,ξ}` and `C S_{η, c ξ} = S_{η,ξ}`. -/
theorem relativeModular_smul_right {c : ℂ} (hc : c ≠ 0) :
    Δ⟦η, c • ξ⟧ = (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) • Δ⟦η, ξ⟧ := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).mpr hc
  have hn : 0 < ‖c‖ ^ 2 := by positivity
  set B : H →L[ℂ] H := (conj c)⁻¹ • 1
  set C : H →L[ℂ] H := conj c • 1
  have hS₂ : S⟦η, c • ξ⟧ = (B : H →ₗ[ℂ] H).compPMap (S⟦η, ξ⟧) := by
    rw [relativeTomita_smul_right hc]
    exact LinearPMap.ext rfl fun _ _ _ => rfl
  have hCB : (C : H →ₗ[ℂ] H).compPMap (S⟦η, c • ξ⟧) = S⟦η, ξ⟧ := by
    rw [hS₂, ← LinearPMap.compPMap_comp]
    refine LinearPMap.ext rfl fun x hx _ => ?_
    change conj c • ((conj c)⁻¹ • S⟦η, ξ⟧ ⟨x, hx⟩) = S⟦η, ξ⟧ ⟨x, hx⟩
    rw [smul_smul, mul_inv_cancel₀ hc', one_smul]
  have hB : (B : H →ₗ[ℂ] H).compPMap (S⟦η, ξ⟧).closureₛₗ ≤ (S⟦η, c • ξ⟧).closureₛₗ := by
    have h := LinearPMap.compPMap_closureₛₗ_le (isClosable_relativeTomita M η ξ) B
      (hS₂ ▸ isClosable_relativeTomita M η (c • ξ))
    rwa [← hS₂] at h
  have hC : (C : H →ₗ[ℂ] H).compPMap (S⟦η, c • ξ⟧).closureₛₗ ≤ (S⟦η, ξ⟧).closureₛₗ := by
    have h := LinearPMap.compPMap_closureₛₗ_le (isClosable_relativeTomita M η (c • ξ)) C
      (hCB ▸ isClosable_relativeTomita M η ξ)
    rwa [hCB] at h
  exact LinearPMap.adjointₛₗ_compNat_self_eq_smul
    (LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η ξ))
    (LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η (c • ξ)))
    (inv_ne_zero hn.ne') hB hC
    fun y y' => by
      simp only [B, C, smul_apply, one_apply_eq_self, inner_smul_left, inner_smul_right,
        conj_conj]
      rw [Complex.inv_def, conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, mul_comm c,
        mul_assoc, ofReal_inv]

/-- `w′⋆ w′` fixes `[M ξ]` and preserves `[M ξ]ᗮ`, so `S_{η,ξ} ⊆ S_{η,ξ} w′⋆ w′`. -/
private lemma relativeTomita_le_compNat_star_mul (hw : w ∈ M′) (hwξ : star w (w ξ) = ξ) :
    S⟦η, ξ⟧ ≤ S⟦η, ξ⟧.compNat (((star w * w : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) := by
  -- the generating vectors `x ξ + ζ` of the domain are fixed one by one
  refine LinearPMap.le_iff_mem_graphₛₗ.mpr fun a a' ha =>
    LinearPMap.mem_graphₛₗ_compNat_toPMap.mpr ?_
  obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp ha
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  have hwζ : star w (w ζ) ∈ (cyclicSubspace M ξ).toSubmoduleᗮ := by
    rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
    intro b hb
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      apply_apply_of_mem_commutant hw hb, apply_apply_of_mem_commutant (star_mem hw) hb, hwξ]
    exact hζ b hb
  convert mk_mem_graph_relativeTomita (η := η) hx hwζ using 2
  change star w (w (x ξ + ζ)) = x ξ + star w (w ζ)
  rw [map_add, map_add, apply_apply_of_mem_commutant hw hx,
    apply_apply_of_mem_commutant (star_mem hw) hx, hwξ]

/-- **Changing `ξ` along the commutant.** For `w′ ∈ M′` with `w′⋆ w′ ξ = ξ`,
`w′ Δ_{η,ξ} ⊆ Δ_{η, w′ ξ} w′`. With `S′ = S_{η, w′ ξ} = S_{η,ξ} w′⋆`: `S̄_{η,ξ} ⊆ S̄′ w′`, since
`S_{η,ξ} ⊆ S_{η,ξ} w′⋆ w′ = S′ w′` and `S̄′ w′` is closed, and
`w′ S̄_{η,ξ}† ⊆ (S̄_{η,ξ} w′⋆)† ⊆ S̄′†`, since `S̄′ ⊆ S̄_{η,ξ} w′⋆`; hence `w′ S̄† S̄ ⊆ S̄′† S̄′ w′`. -/
lemma compPMap_relativeModular_le_of_mem_commutant (hw : w ∈ M′) (hwξ : star w (w ξ) = ξ) :
    (w : H →ₗ[ℂ] H).compPMap Δ⟦η, ξ⟧ ≤ Δ⟦η, w ξ⟧.compNat ((w : H →ₗ[ℂ] H).toPMap ⊤) := by
  set S := S⟦η, ξ⟧
  set S' := S⟦η, w ξ⟧
  have hS := isClosable_relativeTomita M η ξ
  have hS' := isClosable_relativeTomita M η (w ξ)
  have hd := LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η ξ)
  have hd' := LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η (w ξ))
  have hS'eq : S' = S.compNat (((star w : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) :=
    relativeTomita_apply_right hw hwξ
  -- `S̄ ⊆ S̄′ w′`
  have h₁ : S.closureₛₗ ≤ S'.closureₛₗ.compNat ((w : H →ₗ[ℂ] H).toPMap ⊤) := by
    have hle : S ≤ S'.closureₛₗ.compNat ((w : H →ₗ[ℂ] H).toPMap ⊤) := by
      calc S ≤ S.compNat (((star w * w : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) :=
            relativeTomita_le_compNat_star_mul hw hwξ
        _ = S'.compNat ((w : H →ₗ[ℂ] H).toPMap ⊤) := by
            rw [hS'eq, ← LinearPMap.compNat_toPMap_comp]
            rfl
        _ ≤ S'.closureₛₗ.compNat ((w : H →ₗ[ℂ] H).toPMap ⊤) :=
            LinearPMap.compNat_mono (LinearPMap.le_closureₛₗ _) le_rfl
    have hc := hS'.isClosedₛₗ_closureₛₗ.compNat_toPMap w
    have h := hc.isClosableₛₗ.closureₛₗ_mono hle
    rwa [hc.closureₛₗ_eq] at h
  -- `w′ S̄† ⊆ S̄′†`
  have h₂ : (w : H →ₗ[ℂ] H).compPMap S.closureₛₗ.adjointₛₗ ≤ S'.closureₛₗ.adjointₛₗ := by
    have hle : S'.closureₛₗ ≤ S.closureₛₗ.compNat (((star w : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) := by
      rw [hS'eq]
      exact LinearPMap.closureₛₗ_compNat_toPMap_le hS (star w)
    have hadj := LinearPMap.compPMap_adjoint_le_adjointₛₗ_compNat_toPMap hd (star w)
      (hd'.mono hle.1)
    rw [← ContinuousLinearMap.star_eq_adjoint, star_star] at hadj
    exact hadj.trans (LinearPMap.adjointₛₗ_anti hd' hle)
  rw [relativeModular_def, relativeModular_def]
  calc (w : H →ₗ[ℂ] H).compPMap (S.closureₛₗ.adjointₛₗ.compNat S.closureₛₗ)
      = ((w : H →ₗ[ℂ] H).compPMap S.closureₛₗ.adjointₛₗ).compNat S.closureₛₗ :=
        (LinearPMap.compPMap_compNat _ _ _).symm
    _ ≤ S'.closureₛₗ.adjointₛₗ.compNat (S'.closureₛₗ.compNat ((w : H →ₗ[ℂ] H).toPMap ⊤)) :=
        LinearPMap.compNat_mono h₂ h₁
    _ = (S'.closureₛₗ.adjointₛₗ.compNat S'.closureₛₗ).compNat ((w : H →ₗ[ℂ] H).toPMap ⊤) :=
        (LinearPMap.compNat_assoc _ _ _).symm

/-! ### Spectral measures -/

/-- For `w′ ∈ M′` with `w′⋆ w′ η = r η` (`r > 0`), the spectral measure of `Δ_{w′ η, ξ}` at `ξ` is
the image of that of `Δ_{η,ξ}` under `λ ↦ r λ`. -/
theorem measure_pvm_relativeModular_apply_left (hw : w ∈ M′) {r : ℝ} (hr : 0 < r)
    (hwη : star w (w η) = (r : ℂ) • η) :
    μ⟦w η, ξ⟧ = (μ⟦η, ξ⟧).map fun t => r * t := by
  have h := relativeModular_apply_left (ξ := ξ) hw hr hwη
  unfold relativeModularMeasure
  have hrA : IsSelfAdjoint ((r : ℂ) • Δ⟦η, ξ⟧) :=
    h ▸ isSelfAdjoint_relativeModular M (w η) ξ
  rw [IsSelfAdjoint.pvm_congr _ hrA h]
  exact (isSelfAdjoint_relativeModular M η ξ).measure_pvm_ofReal_smul ξ hr.ne' hrA

/-- **Scaling `η`.** For `a ≠ 0`, the spectral measure of `Δ_{a η, ξ}` at `ξ` is the image of that
of `Δ_{η,ξ}` under `λ ↦ |a|² λ`. -/
theorem measure_pvm_relativeModular_smul_left {a : ℂ} (ha : a ≠ 0) :
    μ⟦a • η, ξ⟧ = (μ⟦η, ξ⟧).map fun t => ‖a‖ ^ 2 * t := by
  have h := relativeModular_smul_left (η := η) (ξ := ξ) (M := M) ha
  unfold relativeModularMeasure
  have hrA : IsSelfAdjoint (((‖a‖ ^ 2 : ℝ) : ℂ) • Δ⟦η, ξ⟧) :=
    h ▸ isSelfAdjoint_relativeModular M (a • η) ξ
  rw [IsSelfAdjoint.pvm_congr _ hrA h]
  exact (isSelfAdjoint_relativeModular M η ξ).measure_pvm_ofReal_smul ξ (by positivity) hrA

/-- **Scaling `ξ`.** The spectral measure of `Δ_{η, c ξ}` at `c ξ` is `|c|²` times the image of
that of `Δ_{η,ξ}` at `ξ` under `λ ↦ |c|⁻² λ` (both sides vanish for `c = 0`). -/
theorem measure_pvm_relativeModular_smul_right (c : ℂ) :
    μ⟦η, c • ξ⟧ = (‖c‖₊ ^ 2) • (μ⟦η, ξ⟧).map fun t => (‖c‖ ^ 2)⁻¹ * t := by
  unfold relativeModularMeasure
  rcases eq_or_ne c 0 with rfl | hc
  · rw [ProjectionValuedMeasure.measure_smul]
    simp
  have h := relativeModular_smul_right (η := η) (ξ := ξ) (M := M) hc
  have hrA : IsSelfAdjoint ((((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) • Δ⟦η, ξ⟧) :=
    h ▸ isSelfAdjoint_relativeModular M η (c • ξ)
  rw [IsSelfAdjoint.pvm_congr _ hrA h, hrA.pvm.measure_smul,
    (isSelfAdjoint_relativeModular M η ξ).measure_pvm_ofReal_smul ξ (by positivity) hrA]

/-- **Changing `ξ` along the commutant.** For `w′ ∈ M′` with `w′⋆ w′ ξ = ξ`, the spectral measure of
`Δ_{η, w′ ξ}` at `w′ ξ` equals that of `Δ_{η,ξ}` at `ξ`. -/
theorem measure_pvm_relativeModular_apply_right (hw : w ∈ M′) (hwξ : star w (w ξ) = ξ) :
    μ⟦η, w ξ⟧ = μ⟦η, ξ⟧ :=
  (isSelfAdjoint_relativeModular M η ξ).measure_pvm_intertwiner
    (isSelfAdjoint_relativeModular M η (w ξ))
    (compPMap_relativeModular_le_of_mem_commutant hw hwξ)
    (by rw [← ContinuousLinearMap.star_eq_adjoint]; exact hwξ)

/-! ### Independence of the vector representatives -/

/-- **Independence of the representative of `ω_η`.** If `η, η′` have the same vector functional on
`M`, then `Δ_{η′,ξ} = Δ_{η,ξ}`. -/
theorem relativeModular_eq_of_inner_eq_left {η' : H}
    (h : ∀ x ∈ M, ⟪η, x η⟫_ℂ = ⟪η', x η'⟫_ℂ) :
    Δ⟦η', ξ⟧ = Δ⟦η, ξ⟧ := by
  obtain ⟨v, hv, -, rfl, hvv, -⟩ := exists_partialIsometry_mem_commutant_of_inner_eq h
  have hvη : star v (v η) = ((1 : ℝ) : ℂ) • η := by
    rw [ofReal_one, one_smul, ← mul_apply_eq_comp, hvv, supportProj_apply_self]
  rw [relativeModular_apply_left hv one_pos hvη, ofReal_one, one_smul]

/-- **Independence of the representative of `ω_ξ`.** If `ξ, ξ′` have the same vector functional on
`M`, then the spectral measure of `Δ_{η,ξ′}` at `ξ′` equals that of `Δ_{η,ξ}` at `ξ`. -/
theorem measure_pvm_relativeModular_eq_of_inner_eq_right {ξ' : H}
    (h : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪ξ', x ξ'⟫_ℂ) :
    μ⟦η, ξ'⟧ = μ⟦η, ξ⟧ := by
  obtain ⟨v, hv, -, rfl, hvv, -⟩ := exists_partialIsometry_mem_commutant_of_inner_eq h
  refine measure_pvm_relativeModular_apply_right hv ?_
  rw [← mul_apply_eq_comp, hvv, supportProj_apply_self]

/-- **Independence of the vector representatives.** If `ω_ξ = ω_ξ′` and `ω_η = ω_η′` on `M`, then
the spectral measure of `Δ_{η′,ξ′}` at `ξ′` equals that of `Δ_{η,ξ}` at `ξ`. -/
theorem measure_pvm_relativeModular_eq_of_inner_eq {ξ' η' : H}
    (hξ : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪ξ', x ξ'⟫_ℂ) (hη : ∀ x ∈ M, ⟪η, x η⟫_ℂ = ⟪η', x η'⟫_ℂ) :
    μ⟦η', ξ'⟧ = μ⟦η, ξ⟧ := by
  unfold relativeModularMeasure
  rw [IsSelfAdjoint.pvm_congr _ (isSelfAdjoint_relativeModular M η ξ')
    (relativeModular_eq_of_inner_eq_left hη)]
  exact measure_pvm_relativeModular_eq_of_inner_eq_right hξ

end VonNeumannAlgebra
