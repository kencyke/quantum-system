/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.TraceDual
public import QuantumSystem.InformationTheory.Entropy.Araki.Monotonicity
public import QuantumSystem.InformationTheory.Entropy.Umegaki.Basic

/-!
# Monotonicity of Umegaki's relative entropy

Let `H` and `K` be finite-dimensional complex Hilbert spaces. The **data-processing inequality**
`D(ψ ∘ α ‖ φ ∘ α) ≤ D(ψ ‖ φ)` holds for positive functionals `ψ, φ` on `B(H)` and every unital
Schwarz map `α : B(K) → B(H)`, `α(a)⋆ α(a) ≤ α(a⋆ a)` (`umegakiEntropy_comp_le`).
It is Araki's data-processing inequality `VonNeumannAlgebra.arakiEntropy_comp_le` on the von
Neumann algebras `𝓑(K)` and `𝓑(H)`, where every map is normal in finite dimension.

By the Kadison–Schwarz inequality, unital `2`-positive maps, in particular unital completely
positive maps and `⋆`-homomorphisms, are Schwarz maps. For a CPTP map `Φ : B(H) → B(K)` the
Schrödinger-picture output of `ψ` is `ψ ∘ Φ*`, with `Φ*` the trace dual, and its density is
`Φ(ρ_ψ)` (`CPTPMap.density_comp_traceDual`); so monotonicity under CPTP maps is
`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)` (`CPTPMap.umegakiEntropy_comp_traceDual_le`), and more generally
under `2`-positive trace-preserving maps.

## Main definitions

* `SchwarzMap.onBoundedLinearOperators T : SchwarzMap 𝓑(K) 𝓑(H)` — a Schwarz map `B(K) → B(H)`
  between operator algebras, transported to the bundled von Neumann algebras; it is normal in
  finite dimension (`VonNeumannAlgebra.isNormalMap_of_finiteDimensional`), which is what lets
  Araki's inequality apply.

## Main results

* `umegakiEntropy_comp_le` — the data-processing inequality for unital Schwarz
  maps; `umegakiEntropy_comp_le_of_kPositiveMap` for unital `2`-positive maps.
* `umegakiEntropy_comp_traceDual_le_of_kPositiveMap`,
  `CPTPMap.umegakiEntropy_comp_traceDual_le` — monotonicity under `2`-positive
  trace-preserving maps and CPTP maps, in the Schrödinger picture.
* `umegakiEntropy_comp_starAlgEquiv` — invariance under `⋆`-isomorphisms
  (unitary conjugations) `B(K) ≃ B(H)`.
* `umegakiEntropy_comp_eq_of_recoverable` — equality in monotonicity when the map
  is reversible on `ψ` and `φ`.

## Recovery and equality

If a CPTP map `R` recovers both inputs, `R(Φ(ρ)) = ρ` and `R(Φ(σ)) = σ`, equality holds in
monotonicity (`umegakiEntropy_comp_eq_of_recoverable`). Petz's theorem gives the
converse, with the Petz recovery map `R(·) = σ^(1/2) Φ*(Φ(σ)^(-1/2) · Φ(σ)^(-1/2)) σ^(1/2)`; that
converse is **not** formalised here.

## TODO

* Monotonicity holds for every positive trace-preserving map (Müller-Hermes–Reeb). Only the
  `2`-positive case is proved here: its proof needs the dual to be a Schwarz map, which the
  Kadison–Schwarz inequality gives for `2`-positive maps but not for merely positive ones. For
  a positive map the inequality is guaranteed only at normal elements
  (`OrderHomClass.le_map_star_mul_of_isStarNormal`), which does not make it a Schwarz map.

## References

* A. Uhlmann, *Relative entropy and the Wigner–Yanase–Dyson–Lieb concavity in an interpolation
  theory*, Comm. Math. Phys. 54 (1977), 21–32.
* G. Lindblad, *Completely positive maps and entropy inequalities*, Comm. Math. Phys. 40 (1975),
  147–151.
* D. Petz, *Monotonicity of quantum relative entropy revisited*, Rev. Math. Phys. 15 (2003), 79–91.
* A. Müller-Hermes, D. Reeb, *Monotonicity of the quantum relative entropy under positive maps*,
  Ann. Henri Poincaré 18 (2017), 1777–1788.
-/

@[expose] public section

open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder VonNeumannAlgebra Araki QuantumInfo

namespace SchwarzMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A Schwarz map `B(K) → B(H)` between operator algebras, as a Schwarz map between the bundled
von Neumann algebras `𝓑(K) → 𝓑(H)`. Stated over variable Hilbert spaces, so that the order and
`⋆`-structure of `↥𝓑(K)` are found generically. -/
noncomputable def onBoundedLinearOperators (T : SchwarzMap (K →L[ℂ] K) (H →L[ℂ] H)) :
    SchwarzMap 𝓑(K) 𝓑(H) where
  toFun x := ⟨T x, VonNeumannAlgebra.mem_boundedLinearOperators _⟩
  map_add' x y := Subtype.ext (map_add T (x : K →L[ℂ] K) y)
  map_smul' c x := Subtype.ext (map_smul T c (x : K →L[ℂ] K))
  le_map_star_mul' x := by
    rw [← Subtype.coe_le_coe]
    exact T.le_map_star_mul' (x : K →L[ℂ] K)

/-- `T.onBoundedLinearOperators` acts as `T` on the underlying operators. -/
@[simp] lemma coe_onBoundedLinearOperators_apply (T : SchwarzMap (K →L[ℂ] K) (H →L[ℂ] H))
    (x : 𝓑(K)) : (T.onBoundedLinearOperators x : H →L[ℂ] H) = T x := rfl

end SchwarzMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

section DPI

variable {G G' G₁ G₁' : Type*}
  [FunLike G (H →L[ℂ] H) ℂ] [LinearMapClass G ℂ (H →L[ℂ] H) ℂ] [OrderHomClass G (H →L[ℂ] H) ℂ]
  [FunLike G' (H →L[ℂ] H) ℂ] [LinearMapClass G' ℂ (H →L[ℂ] H) ℂ] [OrderHomClass G' (H →L[ℂ] H) ℂ]
  [FunLike G₁ (K →L[ℂ] K) ℂ] [LinearMapClass G₁ ℂ (K →L[ℂ] K) ℂ] [OrderHomClass G₁ (K →L[ℂ] K) ℂ]
  [FunLike G₁' (K →L[ℂ] K) ℂ] [LinearMapClass G₁' ℂ (K →L[ℂ] K) ℂ]
  [OrderHomClass G₁' (K →L[ℂ] K) ℂ]
  {ψ : G} {φ : G'} {ψ₁ : G₁} {φ₁ : G₁'}

/-- **Data-processing inequality**: `D(ψ ∘ α ‖ φ ∘ α) ≤ D(ψ ‖ φ)` for positive functionals `ψ, φ`
on `B(H)` and every unital Schwarz map `α : B(K) → B(H)`, stated for any functionals `ψ₁ = ψ ∘ α`,
`φ₁ = φ ∘ α` on `B(K)` (for instance `ψ.comp α`, or `ω.comp α hα` for a state). This is Araki's
`VonNeumannAlgebra.arakiEntropy_comp_le` on `𝓑(K)` and `𝓑(H)`: `α` transported to the von Neumann
algebras (`SchwarzMap.onBoundedLinearOperators`) is normal in finite dimension
(`VonNeumannAlgebra.isNormalMap_of_finiteDimensional`). -/
theorem umegakiEntropy_comp_le {F : Type*} [FunLike F (K →L[ℂ] K) (H →L[ℂ] H)]
    [LinearMapClass F ℂ (K →L[ℂ] K) (H →L[ℂ] H)] [SchwarzMapClass F (K →L[ℂ] K) (H →L[ℂ] H)]
    (α : F) (hα : α 1 = 1) (hψ : ∀ A, ψ₁ A = ψ (α A)) (hφ : ∀ A, φ₁ A = φ (α A)) :
    D(ψ₁ ∥ φ₁) ≤ D(ψ ∥ φ) := by
  set α' := SchwarzMap.onBoundedLinearOperators (SchwarzMapClass.toSchwarzMap α)
  have hn : VonNeumannAlgebra.IsNormalMap α' := VonNeumannAlgebra.isNormalMap_of_finiteDimensional _
  have e₁ : (PositiveLinearMap.ofClass ψ₁).toNormalFunctional =
      (PositiveLinearMap.ofClass ψ).toNormalFunctional.comp α' hn :=
    Subtype.ext (PositiveLinearMap.ext fun x => hψ x)
  have e₂ : (PositiveLinearMap.ofClass φ₁).toNormalFunctional =
      (PositiveLinearMap.ofClass φ).toNormalFunctional.comp α' hn :=
    Subtype.ext (PositiveLinearMap.ext fun x => hφ x)
  rw [umegakiEntropy_def, umegakiEntropy_def, e₁, e₂]
  exact VonNeumannAlgebra.arakiEntropy_comp_le α' (Subtype.ext hα) hn _ _

/-- **Data-processing inequality** for unital `2`-positive maps `α : B(K) → B(H)`, in particular
unital completely positive maps: a Schwarz map by the Kadison–Schwarz inequality
(`KPositiveMapClass.toSchwarzMap`). -/
theorem umegakiEntropy_comp_le_of_kPositiveMap {F : Type*} [FunLike F (K →L[ℂ] K) (H →L[ℂ] H)]
    [LinearMapClass F ℂ (K →L[ℂ] K) (H →L[ℂ] H)] [KPositiveMapClass F 2 (K →L[ℂ] K) (H →L[ℂ] H)]
    (α : F) (hα : α 1 = 1) (hψ : ∀ A, ψ₁ A = ψ (α A)) (hφ : ∀ A, φ₁ A = φ (α A)) :
    D(ψ₁ ∥ φ₁) ≤ D(ψ ∥ φ) :=
  umegakiEntropy_comp_le (KPositiveMapClass.toSchwarzMap α hα.le) hα hψ hφ

/-- **Monotonicity under `2`-positive trace-preserving maps**, in the Schrödinger picture: for
`Φ : B(H) → B(K)` the output of `ψ` is `ψ ∘ Φ*`, with density `Φ(ρ_ψ)`
(`ContinuousLinearMap.density_eq_apply_density`), and `D(ψ ∘ Φ* ‖ φ ∘ Φ*) ≤ D(ψ ‖ φ)`, i.e.
`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`. The trace dual `Φ*` is unital (`isTracePreserving_iff_traceDual_one`)
and `2`-positive (`KPositiveMap.traceDual`). -/
theorem umegakiEntropy_comp_traceDual_le_of_kPositiveMap {F : Type*}
    [FunLike F (H →L[ℂ] H) (K →L[ℂ] K)] [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)]
    [KPositiveMapClass F 2 (H →L[ℂ] H) (K →L[ℂ] K)] (Φ : F) (hΦ : IsTracePreserving Φ)
    (hψ : ∀ B, ψ₁ B = ψ (traceDual Φ B)) (hφ : ∀ B, φ₁ B = φ (traceDual Φ B)) :
    D(ψ₁ ∥ φ₁) ≤ D(ψ ∥ φ) :=
  umegakiEntropy_comp_le_of_kPositiveMap (KPositiveMap.traceDual 2 Φ)
    (isTracePreserving_iff_traceDual_one.1 hΦ) hψ hφ

/-- **Invariance under `⋆`-isomorphisms**: `D(ψ ∘ π ‖ φ ∘ π) = D(ψ ‖ φ)` for `π : B(K) ≃⋆ B(H)`,
in particular for unitary conjugations `A ↦ U A U†`. Both `π` and `π⁻¹` are unital
`⋆`-homomorphisms, hence Schwarz maps, so the data-processing inequality applies both ways. -/
lemma umegakiEntropy_comp_starAlgEquiv (π : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hψ : ∀ A, ψ₁ A = ψ (π A)) (hφ : ∀ A, φ₁ A = φ (π A)) : D(ψ₁ ∥ φ₁) = D(ψ ∥ φ) :=
  le_antisymm (umegakiEntropy_comp_le π (map_one π) hψ hφ)
    (umegakiEntropy_comp_le π.symm (map_one π.symm)
      (fun A => by rw [hψ, StarAlgEquiv.apply_symm_apply])
      (fun A => by rw [hφ, StarAlgEquiv.apply_symm_apply]))

/-- **Equality in monotonicity for reversible maps**: if a unital Schwarz map `β : B(H) → B(K)`
undoes `α` on `ψ` and `φ`, `ψ ∘ α ∘ β = ψ` and `φ ∘ α ∘ β = φ`, then
`D(ψ ∘ α ‖ φ ∘ α) = D(ψ ‖ φ)`. For a CPTP map `Φ` with `α = Φ*` and a recovery CPTP map `R`
with `β = R*`, the hypotheses say `R(Φ(ρ)) = ρ` and `R(Φ(σ)) = σ`. -/
theorem umegakiEntropy_comp_eq_of_recoverable {F F' : Type*}
    [FunLike F (K →L[ℂ] K) (H →L[ℂ] H)] [LinearMapClass F ℂ (K →L[ℂ] K) (H →L[ℂ] H)]
    [SchwarzMapClass F (K →L[ℂ] K) (H →L[ℂ] H)] [FunLike F' (H →L[ℂ] H) (K →L[ℂ] K)]
    [LinearMapClass F' ℂ (H →L[ℂ] H) (K →L[ℂ] K)] [SchwarzMapClass F' (H →L[ℂ] H) (K →L[ℂ] K)]
    (α : F) (hα : α 1 = 1) (β : F') (hβ : β 1 = 1) (hψ : ∀ A, ψ₁ A = ψ (α A))
    (hφ : ∀ A, φ₁ A = φ (α A)) (hψβ : ∀ A, ψ (α (β A)) = ψ A) (hφβ : ∀ A, φ (α (β A)) = φ A) :
    D(ψ₁ ∥ φ₁) = D(ψ ∥ φ) :=
  le_antisymm (umegakiEntropy_comp_le α hα hψ hφ)
    (umegakiEntropy_comp_le β hβ (fun A => by rw [hψ, hψβ]) (fun A => by rw [hφ, hφβ]))

end DPI

namespace CPTPMap

/-- The Schrödinger-picture output `ψ ∘ Φ*` of a functional `ψ` under a CPTP map `Φ` has density
`Φ(ρ_ψ)`. -/
lemma density_comp_traceDual (Φ : CPTPMap H K) (ψ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    density (ψ.comp (.ofClass (CompletelyPositiveMap.traceDual Φ))) = Φ (density ψ) :=
  density_eq_apply_density Φ fun _ => rfl

/-- **Monotonicity under CPTP maps**: `D(ψ ∘ Φ* ‖ φ ∘ Φ*) ≤ D(ψ ‖ φ)`, i.e.
`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)` for the densities (`CPTPMap.density_comp_traceDual`). -/
theorem umegakiEntropy_comp_traceDual_le (Φ : CPTPMap H K) (ψ φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    D(ψ.comp (.ofClass (CompletelyPositiveMap.traceDual Φ)) ∥
        φ.comp (.ofClass (CompletelyPositiveMap.traceDual Φ))) ≤ D(ψ ∥ φ) :=
  umegakiEntropy_comp_le_of_kPositiveMap (CompletelyPositiveMap.traceDual Φ) Φ.traceDual_one
    (fun _ => rfl) (fun _ => rfl)

end CPTPMap
