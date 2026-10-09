/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.BorchersTranslation

/-!
# Borchers triples

Let `V` be a finite-dimensional real normed space (the translations of spacetime) with two closed
convex cones `C` (the positive-energy cone of the spectrum condition, e.g. the closed forward light
cone) and `W` (the wedge, e.g. the closed right Rindler wedge). A **Borchers triple** `(M, T, Ω)`
relative to `(C, W)` (`BorchersTriple V C W H`) consists of a von Neumann algebra `M` on `H`, a
strongly continuous unitary representation `T` of `V` and a vector `Ω` such that
* `T` satisfies the **spectrum condition**: its projection-valued measure `E_T` on the dual space
  (the SNAG theorem) vanishes off the dual cone `C* = {p | ∀ a ∈ C, 0 ≤ p a}`;
* `T(x) M T(x)⋆ ⊆ M` for `x ∈ W`;
* `T(x) Ω = Ω`, and `Ω` is cyclic and separating for `M`.

**Borchers' theorem** for Borchers triples (`BorchersTriple.modularGroup_mul_mul_eq_boost`,
`BorchersTriple.modularConj_apply_eq_reflection`): for `a ∈ W ∩ C`, `b ∈ W ∩ -C` and
`z ∈ W ∩ -W`, the modular group `Δ^{it}` and the modular conjugation `J` of `(M, Ω)` satisfy
`Δ^{it} T(r a + s b + z) Δ^{-it} = T(e^{-2πt} r a + e^{2πt} s b + z)` and
`J T(r a + s b + z) J = T(-r a - s b + z)`. Its specialisation to the forward light cone and the
Rindler wedge of Minkowski space is
`QuantumSystem.Algebra.VonNeumannAlgebra.Modular.BorchersTriple.RindlerWedge`.

## Main definitions

* `BorchersTriple V C W H` — Borchers triples relative to the cones `C` and `W`.
* `BorchersTriple.standardSubspace B` — the standard subspace `H_M` of `(M, Ω)`, whose modular
  objects are those of `(M, Ω)`.
* `BorchersTriple.trivial V C W` — the trivial Borchers triple `(𝓑(ℂ), 1, 1)` on `ℂ`, relative to
  any cones; it shows that the fields of `BorchersTriple`, the spectrum condition included, are
  consistent.

## Main results

* `BorchersTriple.subset_spectralCone` — the spectrum condition says that every `a ∈ C` generates
  a translation group with positive generator.
* `BorchersTriple.modularGroup_mul_mul_eq_boost`, `BorchersTriple.modularConj_apply_eq_reflection` —
  **Borchers' theorem** for Borchers triples.

## TODO

* **Wedge-local nets** (Buchholz–Lechner–Summers 2011, §4): a Borchers triple generates the net of
  wedge algebras `W + x ↦ T(x) M T(x)⋆`, and its relative commutants give the local algebras of
  double cones. That construction is a local net in the sense of
  `QuantumSystem.Algebra.LocalNet.Net` and belongs under `QuantumSystem.Algebra.LocalNet`, importing
  this file.

## References

* H.-J. Borchers, *On the use of modular groups in quantum field theory*,
  Ann. Inst. H. Poincaré Phys. Théor. 63 (1995), 331–382
* D. Buchholz, G. Lechner, S. J. Summers, *Warped convolutions, Rieffel deformations and the
  construction of quantum field theories*, Comm. Math. Phys. 304 (2011), 95–123, §4
-/

@[expose] public section

open InnerProductSpace (IsCyclicVector IsSeparatingVector)

open Set Complex
open scoped InnerProductSpace VonNeumannAlgebra StandardSubspace Real

/-- A **Borchers triple** `(M, T, Ω)` relative to closed convex cones `C` (spectrum) and `W`
(wedge) in a finite-dimensional real normed space `V`: a von Neumann algebra `M`, a strongly
continuous unitary representation `T` of `V` whose projection-valued measure on the dual space
vanishes off the dual cone of `C` (the **spectrum condition**), with `T(x) M T(x)⋆ ⊆ M` for
`x ∈ W`, and a `T`-invariant vector `Ω` that is cyclic and separating for `M`. -/
structure BorchersTriple (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (C W : ProperCone ℝ V) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The von Neumann algebra (of the wedge `W`). -/
  M : VonNeumannAlgebra H
  /-- The unitary representation of the translations. -/
  T : AddChar V (unitary (H →L[ℂ] H))
  /-- The vacuum vector. -/
  Ω : H
  /-- The translations are strongly continuous. -/
  isStronglyContinuous : T.IsStronglyContinuous
  /-- **Spectrum condition**: the projection-valued measure of `T` on the dual space vanishes off
  the dual cone `{p | ∀ a ∈ C, 0 ≤ p a}`. -/
  pvm_compl_dual_eq_zero : isStronglyContinuous.pvm (topDualPairing ℝ V)
    (ProperCone.dual (topDualPairing ℝ V).flip (C : Set V) : Set (StrongDual ℝ V))ᶜ = 0
  /-- Translations into the wedge map `M` into itself. -/
  mul_mul_star_mem : ∀ x ∈ W, ∀ y ∈ M, (T x : H →L[ℂ] H) * y * star (T x : H →L[ℂ] H) ∈ M
  /-- The vacuum is invariant under translations. -/
  apply_vacuum : ∀ x, (T x : H →L[ℂ] H) Ω = Ω
  /-- The vacuum is cyclic for `M`. -/
  isCyclicVector : IsCyclicVector M Ω
  /-- The vacuum is separating for `M`. -/
  isSeparatingVector : IsSeparatingVector M Ω

/-! The norm on `V` is only used to equip the dual space `StrongDual ℝ V` with its Borel
σ-algebra, which the spectrum condition needs; every finite-dimensional Hausdorff topological
vector space is normable, so no generality is lost. -/

namespace BorchersTriple

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {C W : ProperCone ℝ V} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (B : BorchersTriple V C W H)

/-- The standard subspace `H_M` of `(M, Ω)`; its modular group and modular conjugation are those
of `(M, Ω)` (`VonNeumannAlgebra.relativeModular_self_eq_modular`). -/
noncomputable abbrev standardSubspace : StandardSubspace H :=
  B.M.standardSubspace B.Ω B.isCyclicVector B.isSeparatingVector

/-- The spectrum condition: every `a ∈ C` generates translations `s ↦ T(s a)` with positive
generator. -/
lemma subset_spectralCone : (C : Set V) ⊆ B.isStronglyContinuous.spectralCone :=
  (B.isStronglyContinuous.subset_spectralCone_iff (topDualPairing ℝ V) C).mpr
    B.pvm_compl_dual_eq_zero

variable {a b z : V}

/-- **Borchers' theorem** for Borchers triples, modular group: for `a ∈ W ∩ C`, `b ∈ W ∩ -C` and
`z ∈ W ∩ -W`, `Δ^{it} T(r a + s b + z) Δ^{-it} = T(e^{-2πt} r a + e^{2πt} s b + z)`. -/
theorem modularGroup_mul_mul_eq_boost (ha : a ∈ W) (haC : a ∈ C) (hb : b ∈ W) (hbC : -b ∈ C)
    (hz : z ∈ W) (hz' : -z ∈ W) (r s t : ℝ) :
    B.standardSubspace.modularGroup t * B.T (r • a + s • b + z) *
      B.standardSubspace.modularGroup (-t) =
        B.T ((Real.exp (-2 * π * t) * r) • a + (Real.exp (2 * π * t) * s) • b + z) :=
  VonNeumannAlgebra.modularGroup_mul_mul_eq_boost B.isCyclicVector B.isSeparatingVector
    B.isStronglyContinuous (fun v _ => B.apply_vacuum v) B.mul_mul_star_mem ha (B.subset_spectralCone haC) hb
    (B.subset_spectralCone hbC) hz hz' r s t

/-- **Borchers' theorem** for Borchers triples, modular conjugation: for `a ∈ W ∩ C`,
`b ∈ W ∩ -C` and `z ∈ W ∩ -W`, `J T(r a + s b + z) J = T(-r a - s b + z)`. -/
theorem modularConj_apply_eq_reflection (ha : a ∈ W) (haC : a ∈ C) (hb : b ∈ W) (hbC : -b ∈ C)
    (hz : z ∈ W) (hz' : -z ∈ W) (r s : ℝ) (x : H) :
    J[B.standardSubspace] ((B.T (r • a + s • b + z) : H →L[ℂ] H) (J[B.standardSubspace] x)) =
      (B.T (-(r • a) - s • b + z) : H →L[ℂ] H) x :=
  VonNeumannAlgebra.modularConj_apply_eq_reflection B.isCyclicVector B.isSeparatingVector
    B.isStronglyContinuous (fun v _ => B.apply_vacuum v) B.mul_mul_star_mem ha (B.subset_spectralCone haC) hb
    (B.subset_spectralCone hbC) hz hz' r s x

end BorchersTriple

/-! ### A witness -/

namespace BorchersTriple

/-- **The trivial Borchers triple** on `ℂ`, relative to any cones `C` and `W`: `M = 𝓑(ℂ)`,
trivial translations and `Ω = 1`. The spectrum condition holds because the projection-valued
measure of the trivial representation is the Dirac measure at `0`
(`AddChar.IsStronglyContinuous.pvm_one`), and `0` lies in every dual cone. -/
noncomputable def trivial (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (C W : ProperCone ℝ V) : BorchersTriple V C W ℂ where
  M := 𝓑(ℂ)
  T := 1
  Ω := 1
  isStronglyContinuous := AddChar.isStronglyContinuous_iff.mpr fun y => by
    simpa using continuous_const
  pvm_compl_dual_eq_zero := by
    rw [AddChar.IsStronglyContinuous.pvm_one, MeasureTheory.ProjectionValuedMeasure.dirac_apply _
      (ProperCone.isClosed _).measurableSet.compl]
    simp
  mul_mul_star_mem _ _ _ _ := VonNeumannAlgebra.mem_boundedLinearOperators _
  apply_vacuum _ := by simp
  isCyclicVector := by
    refine eq_top_iff.mpr fun v _ => ?_
    simpa using InnerProductSpace.apply_mem_cyclicSubspace (S := ((𝓑(ℂ) :
      VonNeumannAlgebra ℂ) : Set (ℂ →L[ℂ] ℂ))) (1 : ℂ) (a := v • (1 : ℂ →L[ℂ] ℂ))
      (VonNeumannAlgebra.mem_boundedLinearOperators _)
  isSeparatingVector x _ hx := ContinuousLinearMap.ext_ring (by simpa using hx)

end BorchersTriple
