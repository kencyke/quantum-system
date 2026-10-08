/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.BorchersTriple.Basic
public import QuantumSystem.Geometry.Minkowski

/-!
# Borchers' theorem for the Rindler wedge

Specialise Borchers triples (`QuantumSystem.Algebra.VonNeumannAlgebra.Modular.BorchersTriple.Basic`)
to Minkowski space `ℝ × E` (`QuantumSystem.Geometry.Minkowski`), with the closed forward light cone
`V̄₊` as spectrum cone and the closed Rindler wedge `W̄` of a unit vector `e ∈ E` as wedge. Writing
`x = r ℓ₊ + s ℓ₋ + z` (`Minkowski.eq_lightPlus_add`) with `ℓ₊ ∈ W̄ ∩ V̄₊`, `ℓ₋ ∈ W̄ ∩ -V̄₊` and
`z ∈ W̄ ∩ -W̄`, Borchers' theorem becomes
`Δ^{it} T(x) Δ^{-it} = T(Λ_W(-2πt) x)` and `J T(x) J = T(j_W x)`, with the wedge boost `Λ_W`
(`Minkowski.wedgeBoost`) and the wedge reflection `j_W` (`Minkowski.wedgeReflection`).

## Main results

* `BorchersTriple.modularGroup_mul_mul_eq_wedgeBoost`,
  `BorchersTriple.modularConj_apply_eq_wedgeReflection` — **Borchers' theorem** for the Rindler
  wedge: `Δ^{it} T(x) Δ^{-it} = T(Λ_W(-2πt) x)` and `J T(x) J = T(j_W x)`.

## TODO

* **Causal Borchers triples** (Buchholz–Lechner–Summers 2011, Definition 4.1): a strongly
  continuous representation of the whole proper orthochronous Poincaré group `P₊↑` with the
  causality condition `λ W ⊆ W' ⇒ U(λ) M U(λ)⁻¹ ⊆ M'`. They are to be introduced as a structure
  extending `BorchersTriple` (forgetting the Lorentz part and causality gives a Borchers triple, so
  the results here apply to them); besides the Minkowski form (`Minkowski.form`) this needs the
  Lorentz group and the wedges `λ W_R`, which are not formalised.
* In two spacetime dimensions, Borchers (1992) shows that `(Δ^{it}, J, T)` generate a
  representation of the proper Poincaré group `P₊` and that wedge locality `J M J = M′` holds
  automatically. This relies on Tomita's theorem `J M J = M′` for von Neumann algebras, which is
  not formalised; it is recorded here as a literature note only.

## References

* H.-J. Borchers, *The CPT-theorem in two-dimensional theories of local observables*,
  Comm. Math. Phys. 143 (1992), 315–332
* H.-J. Borchers, *On the use of modular groups in quantum field theory*,
  Ann. Inst. H. Poincaré Phys. Théor. 63 (1995), 331–382
* D. Buchholz, G. Lechner, S. J. Summers, *Warped convolutions, Rieffel deformations and the
  construction of quantum field theories*, Comm. Math. Phys. 304 (2011), 95–123, §4
-/

@[expose] public section

open scoped InnerProductSpace StandardSubspace Real

namespace BorchersTriple

open Minkowski

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {e : E}
  (he : ‖e‖ = 1) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (B : BorchersTriple (ℝ × E) (forwardCone E) (wedge e) H)

include he in
/-- **Borchers' theorem for the Rindler wedge**, modular group: for a Borchers triple relative to
the forward light cone and the Rindler wedge of a unit vector `e`, the modular group of `(M, Ω)`
acts on the translations as the wedge boosts, `Δ^{it} T(x) Δ^{-it} = T(Λ_W(-2πt) x)`. -/
theorem modularGroup_mul_mul_eq_wedgeBoost (t : ℝ) (x : ℝ × E) :
    B.standardSubspace.modularGroup t * B.T x * B.standardSubspace.modularGroup (-t) =
      B.T (wedgeBoost e (-(2 * π * t)) x) := by
  conv_lhs => rw [eq_lightPlus_add e x]
  rw [B.modularGroup_mul_mul_eq_boost (lightPlus_mem_wedge he) (lightPlus_mem_forwardCone he)
    (lightMinus_mem_wedge he) (neg_lightMinus_mem_forwardCone he) (edge_mem_wedge he x)
    (neg_edge_mem_wedge he x)]
  congr 1
  have hc : Real.cosh (-(2 * π * t)) = (Real.exp (-2 * π * t) + Real.exp (2 * π * t)) / 2 := by
    rw [Real.cosh_eq, neg_neg, show -(2 * π * t) = -2 * π * t by ring]
  have hs : Real.sinh (-(2 * π * t)) = (Real.exp (-2 * π * t) - Real.exp (2 * π * t)) / 2 := by
    rw [Real.sinh_eq, neg_neg, show -(2 * π * t) = -2 * π * t by ring]
  simp only [wedgeBoost_apply, hc, hs]
  refine Prod.ext ?_ ?_
  · simp only [neg_mul, Prod.smul_mk, smul_eq_mul, mul_one, mul_neg, Prod.mk_add_mk, add_zero]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, edge, lightPlus, lightMinus]
    module

include he in
/-- **Borchers' theorem for the Rindler wedge**, modular conjugation: for a Borchers triple
relative to the forward light cone and the Rindler wedge of a unit vector `e`, the modular
conjugation of `(M, Ω)` acts on the translations as the wedge reflection, `J T(x) J = T(j_W x)`. -/
theorem modularConj_apply_eq_wedgeReflection (x : ℝ × E) (y : H) :
    J[B.standardSubspace] ((B.T x : H →L[ℂ] H) (J[B.standardSubspace] y)) =
      (B.T (wedgeReflection e x) : H →L[ℂ] H) y := by
  conv_lhs => rw [eq_lightPlus_add e x]
  rw [B.modularConj_apply_eq_reflection (lightPlus_mem_wedge he) (lightPlus_mem_forwardCone he)
    (lightMinus_mem_wedge he) (neg_lightMinus_mem_forwardCone he) (edge_mem_wedge he x)
    (neg_edge_mem_wedge he x)]
  congr 3
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.neg_mk, mul_neg, Prod.mk_sub_mk,
      sub_neg_eq_add, Prod.mk_add_mk, add_zero, wedgeReflection_apply]
    ring
  · simp only [wedgeReflection_apply, Prod.snd_add, Prod.snd_sub, Prod.snd_neg, Prod.smul_snd, edge,
      lightPlus, lightMinus]
    module

end BorchersTriple
