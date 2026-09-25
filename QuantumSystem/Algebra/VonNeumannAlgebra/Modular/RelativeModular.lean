/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.RelativeTomita
public import QuantumSystem.Algebra.VonNeumannAlgebra.Support
public import QuantumSystem.Analysis.UnboundedOperator.SpectralCalculus

/-!
# The relative modular operator

For a von Neumann algebra `M` on `H` and `ξ, η ∈ H`, the **relative modular operator** is
`Δ_{η,ξ} = S̄†S̄`, where `S̄` is the closure of the relative Tomita operator
`S_{η,ξ} : x ξ + ζ ↦ s(ξ) x⋆ η` (`VonNeumannAlgebra.relativeTomita`). As `S̄` is conjugate-linear,
closed and densely defined, `S̄†S̄` is a complex-linear, positive self-adjoint operator (von
Neumann's theorem), regarded as a complex operator through `LinearPMap.IsComplexLinear.toComplex`.

The spectral measure `μ_ξ` of `Δ_{η,ξ}` at `ξ` is the input of Araki's relative entropy
`S(ω_ξ ‖ ω_η) = -∫ log λ dμ_ξ(λ)`. Its atom at `0` detects the support condition: `μ_ξ {0} = 0` iff
`s(ξ) ≤ s(η)`, the vector form of `ω_ξ ≪ ω_η` in the sense of *support inclusion*
`s(ω_ξ) ≤ s(ω_η)` (not domination `ω_ξ ≤ c ω_η`). No atom at `0` does not make
`-∫ log λ dμ_ξ` finite: in infinite dimensions the entropy can be `+∞` even when
`s(ξ) ≤ s(η)`.

## Main definitions

* `VonNeumannAlgebra.relativeModular M η ξ` — the relative modular operator `Δ_{η,ξ}`.

## Main results

* `VonNeumannAlgebra.isSelfAdjoint_relativeModular`, `VonNeumannAlgebra.isPositive_relativeModular`
  — `Δ_{η,ξ}` is positive self-adjoint.
* `VonNeumannAlgebra.restrictScalars_relativeModular` — `Δ_{η,ξ} = S̄†S̄` as real operators.
* `VonNeumannAlgebra.re_inner_eq_norm_sq_of_mem_graph_relativeModular` — `re ⟪u, Δ u⟫ = ‖S̄ u‖²`.
* `VonNeumannAlgebra.mem_graph_relativeModular_zero_iff` — `ker Δ_{η,ξ} = ker S̄`.
* `VonNeumannAlgebra.spectralMeasure_relativeModular_singleton_zero_eq_zero_iff` — **support
  theorem**: `μ_ξ {0} = 0 ↔ s(ξ) ≤ s(η)`.
* `VonNeumannAlgebra.lintegral_spectralMeasure_relativeModular_le` — `∫ λ dμ_ξ ≤ ‖s(ξ) η‖²`.
* `VonNeumannAlgebra.self_mem_graph_relativeModular_self`,
  `VonNeumannAlgebra.spectralMeasure_relativeModular_self` — `Δ_{ξ,ξ} ξ = ξ`, hence
  `μ_ξ = ‖ξ‖² δ₁` for `Δ_{ξ,ξ}`.
* `VonNeumannAlgebra.relativeModular_apply_left`, `VonNeumannAlgebra.relativeModular_smul_left`,
  `VonNeumannAlgebra.relativeModular_smul_right` — `Δ_{w′ η, ξ} = r Δ_{η,ξ}` for `w′ ∈ M′` with
  `w′⋆ w′ η = r η`; `Δ_{a η, ξ} = |a|² Δ_{η,ξ}`; `Δ_{η, c ξ} = |c|⁻² Δ_{η,ξ}`.
* `VonNeumannAlgebra.spectralMeasure_relativeModular_apply_left`,
  `VonNeumannAlgebra.spectralMeasure_relativeModular_smul_left`,
  `VonNeumannAlgebra.spectralMeasure_relativeModular_smul_right`,
  `VonNeumannAlgebra.spectralMeasure_relativeModular_apply_right` — the corresponding statements
  for the spectral measure `μ_ξ` (for `v′ ∈ M′` with `v′⋆ v′ ξ = ξ`, `μ_{v′ξ}` of `Δ_{η, v′ ξ}` is
  `μ_ξ` of `Δ_{η,ξ}`).
* `VonNeumannAlgebra.relativeModular_eq_of_inner_eq_left`,
  `VonNeumannAlgebra.spectralMeasure_relativeModular_eq_of_inner_eq_right`,
  `VonNeumannAlgebra.spectralMeasure_relativeModular_eq_of_inner_eq` — **independence of the
  vector representatives**: `μ_ξ` of `Δ_{η,ξ}` depends only on the vector functionals `ω_ξ`, `ω_η`.

Transformations along isometric intertwiners between different Hilbert spaces (spatial
isomorphisms, amplifications) are in `QuantumSystem.Algebra.VonNeumannAlgebra.Modular.Spatial`.
-/

@[expose] public section

open Complex ClosedSubmodule MeasureTheory
open scoped InnerProductSpace ComplexConjugate VonNeumannAlgebra LinearPMap
open InnerProductSpace (cyclicSubspace)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (η ξ : H)

/-! ### The closure of the relative Tomita operator -/

/-- The closure `S̄_{η,ξ}` is conjugate-linear. -/
lemma isConjLinear_closure_relativeTomita :
    LinearPMap.IsConjLinear (M.relativeTomita η ξ).closure :=
  (isConjLinear_relativeTomita M η ξ).closure

/-- The closure `S̄_{η,ξ}` is closed. -/
lemma isClosed_closure_relativeTomita : (M.relativeTomita η ξ).closure.IsClosed :=
  (isClosable_relativeTomita M η ξ).closure_isClosed

/-- The closure `S̄_{η,ξ}` is densely defined. -/
lemma dense_domain_closure_relativeTomita :
    Dense ((M.relativeTomita η ξ).closure.domain : Set H) :=
  (dense_domain_relativeTomita M η ξ).mono (LinearPMap.le_closure _).1

variable {M η ξ} in
/-- The graph of `S_{η,ξ}` lies in that of its closure. -/
lemma mem_graph_closure_relativeTomita {p : H × H} (hp : p ∈ (M.relativeTomita η ξ).graph) :
    p ∈ (M.relativeTomita η ξ).closure.graph :=
  LinearPMap.le_graph_of_le (LinearPMap.le_closure _) hp

/-- `S̄_{η,ξ}† S̄_{η,ξ}` is complex-linear. -/
lemma isComplexLinear_adjoint_compNat_closure_relativeTomita :
    LinearPMap.IsComplexLinear
      ((M.relativeTomita η ξ).closure†.compNat (M.relativeTomita η ξ).closure) :=
  ((isConjLinear_closure_relativeTomita M η ξ).adjoint
    (dense_domain_closure_relativeTomita M η ξ)).compNat (isConjLinear_closure_relativeTomita M η ξ)

/-! ### The relative modular operator -/

/-- The **relative modular operator** `Δ_{η,ξ} = S̄†S̄`, for `S̄` the closure of the relative Tomita
operator `S_{η,ξ}`, as a complex operator. -/
noncomputable def relativeModular : H →ₗ.[ℂ] H :=
  (isComplexLinear_adjoint_compNat_closure_relativeTomita M η ξ).toComplex

/-- `Δ_{η,ξ} = S̄†S̄` as real operators. -/
theorem restrictScalars_relativeModular :
    (M.relativeModular η ξ).restrictScalars ℝ =
      (M.relativeTomita η ξ).closure†.compNat (M.relativeTomita η ξ).closure :=
  LinearPMap.IsComplexLinear.restrictScalars_toComplex _

variable {M η ξ} in
/-- The graph of `Δ_{η,ξ}` is that of `S̄†S̄`. -/
theorem mem_graph_relativeModular {p : H × H} :
    p ∈ (M.relativeModular η ξ).graph ↔
      p ∈ ((M.relativeTomita η ξ).closure†.compNat (M.relativeTomita η ξ).closure).graph :=
  LinearPMap.IsComplexLinear.mem_graph_toComplex _

/-- `Δ_{η,ξ}` is self-adjoint (von Neumann's theorem). -/
theorem isSelfAdjoint_relativeModular : IsSelfAdjoint (M.relativeModular η ξ) :=
  LinearPMap.IsComplexLinear.isSelfAdjoint_toComplex _
    (LinearPMap.isSelfAdjoint_adjoint_compNat_self (isClosed_closure_relativeTomita M η ξ)
      (dense_domain_closure_relativeTomita M η ξ))

/-- `Δ_{η,ξ}` is positive. -/
theorem isPositive_relativeModular : (M.relativeModular η ξ).IsPositive :=
  LinearPMap.IsComplexLinear.isPositive_toComplex _
    (LinearPMap.isPositive_adjoint_compNat_self (dense_domain_closure_relativeTomita M η ξ))

variable {M η ξ}

/-- `re ⟪u, Δ_{η,ξ} u⟫ = ‖S̄_{η,ξ} u‖²`, in graph form. -/
theorem re_inner_eq_norm_sq_of_mem_graph_relativeModular {u u' y : H} (hu : (u, u') ∈ (M.relativeModular η ξ).graph)
    (hy : (u, y) ∈ (M.relativeTomita η ξ).closure.graph) : re ⟪u, u'⟫_ℂ = ‖y‖ ^ 2 :=
  (isSelfAdjoint_relativeModular M η ξ).re_inner_eq_norm_sq_of_restrictScalars_eq
    (restrictScalars_relativeModular M η ξ) hu hy

/-- `ker Δ_{η,ξ} = ker S̄_{η,ξ}`, in graph form. -/
theorem mem_graph_relativeModular_zero_iff {u : H} :
    (u, 0) ∈ (M.relativeModular η ξ).graph ↔ (u, 0) ∈ (M.relativeTomita η ξ).closure.graph := by
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_adjoint_compNat_self_zero_iff
    (dense_domain_closure_relativeTomita M η ξ)]

/-- A vector `u` in the kernel of `S̄_{η,ξ}` is orthogonal to the range of the relative Tomita
operator `F_{η,ξ}` of `M′`: `F_{η,ξ} ⊆ S̄_{η,ξ}†` and `ker S̄` is a complex subspace. -/
private lemma inner_eq_zero_of_mem_graph_closure {u v v' : H}
    (hu : (u, 0) ∈ (M.relativeTomita η ξ).closure.graph)
    (hv : (v, v') ∈ (M′.relativeTomita η ξ).graph) : ⟪u, v'⟫_ℂ = 0 := by
  have hd := dense_domain_closure_relativeTomita M η ξ
  have hadj : (v, v') ∈ (M.relativeTomita η ξ).closure†.graph := by
    rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita M η ξ)]
    exact LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint M η ξ) hv
  have hIu : (I • u, 0) ∈ (M.relativeTomita η ξ).closure.graph := by
    simpa using isConjLinear_closure_relativeTomita M η ξ I u 0 hu
  have h₁ := LinearPMap.inner_eq_of_mem_graph_adjoint hd hu hadj
  have h₂ := LinearPMap.inner_eq_of_mem_graph_adjoint hd hIu hadj
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner, inner_zero_right, zero_re] at h₁ h₂
  rw [inner_smul_right, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_eq_zero] at h₂
  have h0 : ⟪v', u⟫_ℂ = 0 := Complex.ext (by simpa using h₁) (by simpa using h₂)
  rw [← inner_conj_symm, h0, map_zero]

/-- **Support theorem.** The spectral measure `μ_ξ` of `Δ_{η,ξ}` has no atom at `0` iff
`s(ξ) ≤ s(η)`, i.e. iff the support of `ω_ξ` lies under that of `ω_η` (support inclusion, not
domination). -/
theorem spectralMeasure_relativeModular_singleton_zero_eq_zero_iff :
    (isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ {0} = 0 ↔
      M.supportProj ξ ≤ M.supportProj η := by
  set S := M.relativeTomita η ξ
  have hΔ := isSelfAdjoint_relativeModular M η ξ
  have hK : ∀ u, u ∈ (hΔ.isClosed.eigenspace ((0 : ℝ) : ℂ)).toSubmodule ↔ (u, 0) ∈ S.closure.graph :=
    fun u => by
      rw [ClosedSubmodule.mem_toSubmodule_iff, LinearPMap.IsClosed.mem_eigenspace_iff, ofReal_zero,
        zero_smul, mem_graph_relativeModular_zero_iff]
  have hsη := M.isStarProjection_supportProj η
  rw [hΔ.spectralMeasure_singleton_eq_zero_iff, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.mem_orthogonal]
  simp_rw [hK]
  constructor
  · -- `(1 - s(η)) ξ ∈ ker S`, so `⟪(1 - s(η)) ξ, ξ⟫ = 0`.
    intro h
    rw [supportProj_le_iff_inner_eq_zero hsη (M.supportProj_mem η)]
    have hmem : ((1 - M.supportProj η) ξ, 0) ∈ S.closure.graph := by
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
`S̄_{η,ξ} ξ = s(ξ) η`. (Equality holds, `S̄` being closed; only this inequality is formalised.) -/
theorem lintegral_spectralMeasure_relativeModular_le :
    ∫⁻ t, ENNReal.ofReal t ∂(isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ ≤
      ENNReal.ofReal (‖M.supportProj ξ η‖ ^ 2) :=
  (isSelfAdjoint_relativeModular M η ξ).lintegral_spectralMeasure_le_norm_sq
    (restrictScalars_relativeModular M η ξ)
    (mem_graph_closure_relativeTomita (self_mem_graph_relativeTomita M η ξ))

variable (M ξ)

/-- `Δ_{ξ,ξ} ξ = ξ`: `S̄_{ξ,ξ} ξ = s(ξ) ξ = ξ` and `S̄_{ξ,ξ}† ξ = F_{ξ,ξ} ξ = s′(ξ) ξ = ξ`. -/
theorem self_mem_graph_relativeModular_self : (ξ, ξ) ∈ (M.relativeModular ξ ξ).graph := by
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  refine ⟨ξ, ?_, ?_⟩
  · simpa using mem_graph_closure_relativeTomita (self_mem_graph_relativeTomita M ξ ξ)
  · rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita M ξ ξ)]
    refine LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint M ξ ξ) ?_
    simpa using self_mem_graph_relativeTomita M′ ξ ξ

/-- For `Δ_{ξ,ξ}`, the spectral measure at `ξ` is `‖ξ‖² δ₁`. -/
theorem spectralMeasure_relativeModular_self :
    (isSelfAdjoint_relativeModular M ξ ξ).spectralMeasure ξ = (‖ξ‖₊ ^ 2) • Measure.dirac 1 :=
  (isSelfAdjoint_relativeModular M ξ ξ).spectralMeasure_of_mem_graph (c := 1)
    (by simpa using self_mem_graph_relativeModular_self M ξ)

/-! ### Scaling and change of vector representatives -/

variable {M ξ} {w : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- `((r : ℂ) • T)` regarded as a real operator is `r • T`. -/
private lemma restrictScalars_ofReal_smul (T : H →ₗ.[ℂ] H) (r : ℝ) :
    ((r : ℂ) • T).restrictScalars ℝ = r • T.restrictScalars ℝ :=
  LinearPMap.eq_of_eq_graph <| Submodule.ext fun ⟨u, z⟩ => by
    rw [LinearPMap.mem_graph_restrictScalars, LinearPMap.mem_graph_smul, LinearPMap.mem_graph_smul]
    simp_rw [LinearPMap.mem_graph_restrictScalars, Complex.coe_smul]

/-- For `w′ ∈ M′` with `w′⋆ w′ η = r η`, `w′⋆ w′` acts as `r` on the range of `S_{η,ξ}`, which lies
in `M η`. -/
private lemma star_apply_apply_of_mem_graph (hw : w ∈ M′) {r : ℂ} (hwη : star w (w η) = r • η)
    {u v : H} (h : (u, v) ∈ (M.relativeTomita η ξ).graph) : star w (w v) = r • v := by
  obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  have hy : M.supportProj ξ * star x ∈ M := mul_mem (M.supportProj_mem ξ) (star_mem hx)
  change star w (w ((M.supportProj ξ * star x) η)) = r • (M.supportProj ξ * star x) η
  rw [apply_apply_of_mem_commutant hw hy, apply_apply_of_mem_commutant (star_mem hw) hy, hwη,
    map_smul]

/-- **Changing `η` along the commutant.** For `w′ ∈ M′` with `w′⋆ w′ η = r η` (`r > 0`),
`Δ_{w′ η, ξ} = r Δ_{η,ξ}`. -/
theorem relativeModular_apply_left (hw : w ∈ M′) {r : ℝ} (hr : 0 < r)
    (hwη : star w (w η) = (r : ℂ) • η) :
    M.relativeModular (w η) ξ = (r : ℂ) • M.relativeModular η ξ := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  set C : H →L[ℂ] H := (r : ℂ)⁻¹ • star w
  have key := LinearPMap.adjoint_compNat_self_eq_smul (𝕜 := ℝ)
    (T₁ := (M.relativeTomita η ξ).closure) (T₂ := (M.relativeTomita (w η) ξ).closure)
    (dense_domain_closure_relativeTomita M η ξ) (dense_domain_closure_relativeTomita M (w η) ξ)
    (B := w.restrictScalars ℝ) (C := C.restrictScalars ℝ) hr.ne'
    (fun u v h => LinearPMap.mem_graph_closure_of_mapsTo
      (isClosable_relativeTomita M (w η) ξ) (f := fun p : H × H => (p.1, w p.2))
      (by fun_prop) (fun ⟨p₁, p₂⟩ hp =>
        (mem_graph_relativeTomita_apply_left_iff hw).mpr ⟨p₂, hp, rfl⟩) h)
    (fun u v h => LinearPMap.mem_graph_closure_of_mapsTo
      (isClosable_relativeTomita M η ξ) (f := fun p : H × H => (p.1, C p.2))
      (by fun_prop) (fun ⟨p₁, p₂⟩ hp => by
        obtain ⟨v₀, hv₀, rfl⟩ := (mem_graph_relativeTomita_apply_left_iff hw).mp hp
        convert hv₀ using 2
        change (r : ℂ)⁻¹ • star w (w v₀) = v₀
        rw [star_apply_apply_of_mem_graph hw hwη hv₀, inv_smul_smul₀ hr0]) h)
    (fun y y' => by
      change re ⟪y', w y⟫_ℂ = r * re ⟪((r : ℂ)⁻¹ • star w) y', y⟫_ℂ
      rw [smul_apply, inner_smul_left, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left, ← ofReal_inv, conj_ofReal, re_ofReal_mul,
        ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul])
  refine LinearPMap.restrictScalars_injective (R := ℝ) ?_
  rw [restrictScalars_ofReal_smul, restrictScalars_relativeModular, restrictScalars_relativeModular,
    key]
  rfl

/-- **Scaling `η`.** `Δ_{a η, ξ} = |a|² Δ_{η,ξ}` for `a ≠ 0`. -/
theorem relativeModular_smul_left {a : ℂ} (ha : a ≠ 0) :
    M.relativeModular (a • η) ξ = ((‖a‖ ^ 2 : ℝ) : ℂ) • M.relativeModular η ξ := by
  have hw : a • (1 : H →L[ℂ] H) ∈ M′ := SMulMemClass.smul_mem a (one_mem M′)
  have h := relativeModular_apply_left (ξ := ξ) (η := η) hw (r := ‖a‖ ^ 2) (by positivity) (by
    simp only [star_smul, star_one, smul_apply, one_apply_eq_self, smul_smul, Complex.star_def]
    rw [conj_mul', ofReal_pow])
  simpa using h

/-- **Scaling `ξ`.** `Δ_{η, c ξ} = |c|⁻² Δ_{η,ξ}` for `c ≠ 0`. -/
theorem relativeModular_smul_right {c : ℂ} (hc : c ≠ 0) :
    M.relativeModular η (c • ξ) = (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) • M.relativeModular η ξ := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).mpr hc
  have hn : 0 < ‖c‖ ^ 2 := by positivity
  set B : H →L[ℂ] H := (conj c)⁻¹ • 1
  set C : H →L[ℂ] H := conj c • 1
  have key := LinearPMap.adjoint_compNat_self_eq_smul (𝕜 := ℝ)
    (T₁ := (M.relativeTomita η ξ).closure) (T₂ := (M.relativeTomita η (c • ξ)).closure)
    (dense_domain_closure_relativeTomita M η ξ) (dense_domain_closure_relativeTomita M η (c • ξ))
    (B := B.restrictScalars ℝ) (C := C.restrictScalars ℝ) (inv_ne_zero hn.ne')
    (fun u v h => LinearPMap.mem_graph_closure_of_mapsTo
      (isClosable_relativeTomita M η (c • ξ)) (f := fun p : H × H => (p.1, B p.2))
      (by fun_prop) (fun ⟨p₁, p₂⟩ hp =>
        (mem_graph_relativeTomita_smul_right_iff hc).mpr ⟨p₂, hp, by simp [B]⟩) h)
    (fun u v h => LinearPMap.mem_graph_closure_of_mapsTo
      (isClosable_relativeTomita M η ξ) (f := fun p : H × H => (p.1, C p.2))
      (by fun_prop) (fun ⟨p₁, p₂⟩ hp => by
        obtain ⟨v₀, hv₀, rfl⟩ := (mem_graph_relativeTomita_smul_right_iff hc).mp hp
        convert hv₀ using 2
        simp [C, smul_smul, inv_mul_cancel₀ hc']) h)
    (fun y y' => by
      change re ⟪y', B y⟫_ℂ = (‖c‖ ^ 2)⁻¹ * re ⟪C y', y⟫_ℂ
      simp only [B, C, smul_apply, one_apply_eq_self, inner_smul_left, inner_smul_right,
        conj_conj]
      rw [Complex.inv_def, conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, mul_comm c,
        mul_assoc, re_ofReal_mul])
  refine LinearPMap.restrictScalars_injective (R := ℝ) ?_
  rw [restrictScalars_ofReal_smul, restrictScalars_relativeModular, restrictScalars_relativeModular,
    key]
  rfl

/-- **Changing `ξ` along the commutant.** For `v′ ∈ M′` with `v′⋆ v′ ξ = ξ`, `v′` maps the graph of
`Δ_{η,ξ}` into that of `Δ_{η, v′ ξ}`. -/
theorem mem_graph_relativeModular_apply_right (hw : w ∈ M′) (hwξ : star w (w ξ) = ξ) {u z : H}
    (h : (u, z) ∈ (M.relativeModular η ξ).graph) :
    (w u, w z) ∈ (M.relativeModular η (w ξ)).graph := by
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat] at h ⊢
  obtain ⟨y, hy, hyz⟩ := h
  rw [LinearPMap.mem_graph_adjoint_iff (dense_domain_closure_relativeTomita M η ξ)] at hyz
  -- `w⋆ w` fixes `[M ξ]` and preserves `[M ξ]ᗮ`.
  have hww : ∀ a a', (a, a') ∈ (M.relativeTomita η ξ).graph → (star w (w a), a') ∈
      (M.relativeTomita η ξ).graph := fun a a' ha => by
    obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp ha
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    have hwζ : star w (w ζ) ∈ (cyclicSubspace (M : Set (H →L[ℂ] H)) ξ).toSubmoduleᗮ := by
      rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
      intro b hb
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        apply_apply_of_mem_commutant hw hb, apply_apply_of_mem_commutant (star_mem hw) hb, hwξ]
      exact hζ b hb
    convert mk_mem_graph_relativeTomita (η := η) hx hwζ using 2
    rw [map_add, map_add, apply_apply_of_mem_commutant hw hx,
      apply_apply_of_mem_commutant (star_mem hw) hx, hwξ]
  refine ⟨y, LinearPMap.mem_graph_closure_of_mapsTo
    (isClosable_relativeTomita M η (w ξ)) (f := fun p : H × H => (w p.1, p.2)) (by fun_prop)
    (fun ⟨p₁, p₂⟩ hp => (mem_graph_relativeTomita_apply_right_iff hw hwξ).mpr (hww _ _ hp)) hy,
    ?_⟩
  rw [LinearPMap.mem_graph_adjoint_iff (dense_domain_closure_relativeTomita M η (w ξ))]
  intro b b' hb
  have hb' := LinearPMap.mem_graph_closure_of_mapsTo
    (isClosable_relativeTomita M η ξ) (f := fun p : H × H => (star w p.1, p.2)) (by fun_prop)
    (fun ⟨p₁, p₂⟩ hp => (mem_graph_relativeTomita_apply_right_iff hw hwξ).mp hp) hb
  rw [hyz _ _ hb', inner_real_eq_re_inner, inner_real_eq_re_inner,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-! ### Spectral measures -/

/-- For `w′ ∈ M′` with `w′⋆ w′ η = r η` (`r > 0`), the spectral measure of `Δ_{w′ η, ξ}` at `ξ` is
the image of that of `Δ_{η,ξ}` under `λ ↦ r λ`. -/
theorem spectralMeasure_relativeModular_apply_left (hw : w ∈ M′) {r : ℝ} (hr : 0 < r)
    (hwη : star w (w η) = (r : ℂ) • η) :
    (isSelfAdjoint_relativeModular M (w η) ξ).spectralMeasure ξ =
      ((isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ).map fun t => r * t := by
  have h := relativeModular_apply_left (ξ := ξ) hw hr hwη
  have hrA : IsSelfAdjoint ((r : ℂ) • M.relativeModular η ξ) :=
    h ▸ isSelfAdjoint_relativeModular M (w η) ξ
  rw [IsSelfAdjoint.spectralMeasure_congr _ hrA h]
  exact (isSelfAdjoint_relativeModular M η ξ).spectralMeasure_ofReal_smul ξ hr.ne' hrA

/-- **Scaling `η`.** For `a ≠ 0`, the spectral measure of `Δ_{a η, ξ}` at `ξ` is the image of that
of `Δ_{η,ξ}` under `λ ↦ |a|² λ`. -/
theorem spectralMeasure_relativeModular_smul_left {a : ℂ} (ha : a ≠ 0) :
    (isSelfAdjoint_relativeModular M (a • η) ξ).spectralMeasure ξ =
      ((isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ).map fun t => ‖a‖ ^ 2 * t := by
  have h := relativeModular_smul_left (η := η) (ξ := ξ) (M := M) ha
  have hrA : IsSelfAdjoint (((‖a‖ ^ 2 : ℝ) : ℂ) • M.relativeModular η ξ) :=
    h ▸ isSelfAdjoint_relativeModular M (a • η) ξ
  rw [IsSelfAdjoint.spectralMeasure_congr _ hrA h]
  exact (isSelfAdjoint_relativeModular M η ξ).spectralMeasure_ofReal_smul ξ (by positivity) hrA

/-- **Scaling `ξ`.** The spectral measure of `Δ_{η, c ξ}` at `c ξ` is `|c|²` times the image of
that of `Δ_{η,ξ}` at `ξ` under `λ ↦ |c|⁻² λ` (both sides vanish for `c = 0`). -/
theorem spectralMeasure_relativeModular_smul_right (c : ℂ) :
    (isSelfAdjoint_relativeModular M η (c • ξ)).spectralMeasure (c • ξ) =
      (‖c‖₊ ^ 2) • ((isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ).map
        fun t => (‖c‖ ^ 2)⁻¹ * t := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [IsSelfAdjoint.spectralMeasure_smul]
    simp
  have h := relativeModular_smul_right (η := η) (ξ := ξ) (M := M) hc
  have hrA : IsSelfAdjoint ((((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) • M.relativeModular η ξ) :=
    h ▸ isSelfAdjoint_relativeModular M η (c • ξ)
  rw [IsSelfAdjoint.spectralMeasure_congr _ hrA h, hrA.spectralMeasure_smul,
    (isSelfAdjoint_relativeModular M η ξ).spectralMeasure_ofReal_smul ξ (by positivity) hrA]

/-- **Changing `ξ` along the commutant.** For `v′ ∈ M′` with `v′⋆ v′ ξ = ξ`, the spectral measure of
`Δ_{η, v′ ξ}` at `v′ ξ` equals that of `Δ_{η,ξ}` at `ξ`. -/
theorem spectralMeasure_relativeModular_apply_right (hw : w ∈ M′) (hwξ : star w (w ξ) = ξ) :
    (isSelfAdjoint_relativeModular M η (w ξ)).spectralMeasure (w ξ) =
      (isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ :=
  (isSelfAdjoint_relativeModular M η ξ).spectralMeasure_intertwiner
    (isSelfAdjoint_relativeModular M η (w ξ))
    (fun _ _ h => mem_graph_relativeModular_apply_right hw hwξ h)
    (by rw [← ContinuousLinearMap.star_eq_adjoint]; exact hwξ)

/-! ### Independence of the vector representatives -/

/-- **Independence of the representative of `ω_η`.** If `η, η′` have the same vector functional on
`M`, then `Δ_{η′,ξ} = Δ_{η,ξ}`. -/
theorem relativeModular_eq_of_inner_eq_left {η' : H}
    (h : ∀ x ∈ M, ⟪η, x η⟫_ℂ = ⟪η', x η'⟫_ℂ) :
    M.relativeModular η' ξ = M.relativeModular η ξ := by
  obtain ⟨v, hv, -, rfl, hvv, -⟩ := exists_partialIsometry_mem_commutant_of_inner_eq h
  have hvη : star v (v η) = ((1 : ℝ) : ℂ) • η := by
    rw [ofReal_one, one_smul, ← mul_apply_eq_comp, hvv, supportProj_apply_self]
  rw [relativeModular_apply_left hv one_pos hvη, ofReal_one, one_smul]

/-- **Independence of the representative of `ω_ξ`.** If `ξ, ξ′` have the same vector functional on
`M`, then the spectral measure of `Δ_{η,ξ′}` at `ξ′` equals that of `Δ_{η,ξ}` at `ξ`. -/
theorem spectralMeasure_relativeModular_eq_of_inner_eq_right {ξ' : H}
    (h : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪ξ', x ξ'⟫_ℂ) :
    (isSelfAdjoint_relativeModular M η ξ').spectralMeasure ξ' =
      (isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ := by
  obtain ⟨v, hv, -, rfl, hvv, -⟩ := exists_partialIsometry_mem_commutant_of_inner_eq h
  refine spectralMeasure_relativeModular_apply_right hv ?_
  rw [← mul_apply_eq_comp, hvv, supportProj_apply_self]

/-- **Independence of the vector representatives.** If `ω_ξ = ω_ξ′` and `ω_η = ω_η′` on `M`, then
the spectral measure of `Δ_{η′,ξ′}` at `ξ′` equals that of `Δ_{η,ξ}` at `ξ`. -/
theorem spectralMeasure_relativeModular_eq_of_inner_eq {ξ' η' : H}
    (hξ : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪ξ', x ξ'⟫_ℂ) (hη : ∀ x ∈ M, ⟪η, x η⟫_ℂ = ⟪η', x η'⟫_ℂ) :
    (isSelfAdjoint_relativeModular M η' ξ').spectralMeasure ξ' =
      (isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ := by
  rw [IsSelfAdjoint.spectralMeasure_congr _ (isSelfAdjoint_relativeModular M η ξ')
    (relativeModular_eq_of_inner_eq_left hη)]
  exact spectralMeasure_relativeModular_eq_of_inner_eq_right hξ

end VonNeumannAlgebra
