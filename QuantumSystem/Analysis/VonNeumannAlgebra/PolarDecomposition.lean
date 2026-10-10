/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection
public import QuantumSystem.Analysis.VonNeumannAlgebra.MurrayVonNeumann
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Abs

/-!
# Polar decomposition in a von Neumann algebra

Every bounded operator `x` on a Hilbert space factors as `x = v |x|`, where `|x| = (x⋆ x)^{1/2}` is
the absolute value of the continuous functional calculus (`CFC.abs`) and `v` is a partial isometry
whose source projection is the range projection `R(x⋆)`, the projection onto
`closure (ran x⋆) = (ker x)ᗮ`, and whose range projection is `R(x)`, the projection onto
`closure (ran x)` (`ContinuousLinearMap.rangeProj`). When `x` lies in a von Neumann algebra `N`, so
do `|x|` (`VonNeumannAlgebra.cfcAbs_mem`) and `v`. This is the form of the polar decomposition used
by the comparison theory of projections (`QuantumSystem.Analysis.VonNeumannAlgebra.Comparison`): it
makes the range projections of `x⋆` and of `x` Murray–von Neumann equivalent in `N`.

The identity `‖|x| η‖ = ‖x η‖` (`ContinuousLinearMap.norm_cfcAbs_apply`) makes `|x| η ↦ x η` an
isometry on the range of `|x|`, and `exists_isPartialIsometry_mem_centralizer_of_norm_eq` extends it
to a partial isometry `v` with `v |x| = x`, source projection onto `closure (ran |x|)` and range
projection onto `closure (ran x)`; the first closure is `closure (ran x⋆)`
(`ContinuousLinearMap.topologicalClosure_range_cfcAbs`). Since every element of the commutant `N′`
commutes with `x` and `|x|`, `v` can be taken in the centralizer of `N′`, which is `N = N″`. The
same lemma, applied to `a ↦ a ξ` and `a ↦ a η`, gives the uniqueness of vector representatives
(`QuantumSystem.Analysis.VonNeumannAlgebra.SupportProjection`).

The polar decomposition of closed, densely defined operators
(`QuantumSystem.Analysis.SpectralTheory.PolarDecomposition`) covers bounded operators too, but it
does not record membership in a von Neumann algebra. The statement here is existential, and its
witness is the elementary bounded construction above; it is nevertheless determined by `x`, since
an operator `v` with `x = v |x|` and source projection `R(x⋆)` is unique
(`ContinuousLinearMap.eq_of_eq_mul_cfcAbs`). The two constructions agree on a bounded `x`
(`QuantumSystem.Analysis.SpectralTheory.BoundedPolarDecomposition`): the square root of
`T†T` for `T = x.toPMap ⊤` is `|x|` (`ContinuousLinearMap.sqrt_eq_toPMap_cfcAbs`), and the partial
isometry of `T = U |T|` is the `v` given here
(`ContinuousLinearMap.polarIsometry_eq_of_eq_mul_cfcAbs`).

## Main results

* `VonNeumannAlgebra.exists_isPartialIsometry_eq_mul_cfcAbs` — **polar decomposition**: for
  `x ∈ N` there is a partial isometry `v ∈ N` with `x = v |x|`, source projection `R(x⋆)` and
  range projection `R(x)`.
* `VonNeumannAlgebra.mvNEquiv_rangeProj` — `R(x⋆) ∼[N] R(x)`: the range projections of `x⋆` and
  of `x` are Murray–von Neumann equivalent in `N`.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras II*, §6.1
  (the polar decomposition of a bounded operator and its partial isometry).
-/

@[expose] public section

open scoped CFC VonNeumannAlgebra

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Polar decomposition in a von Neumann algebra.** Every `x ∈ N` factors as `x = v |x|`, with
`|x| = (x⋆ x)^{1/2}` (`CFC.abs`) and `v ∈ N` a partial isometry whose source projection is the
range projection `R(x⋆)`, the projection onto `closure (ran x⋆) = (ker x)ᗮ`, and whose range
projection is `R(x)`, the projection onto `closure (ran x)`. Such a `v` is unique
(`ContinuousLinearMap.eq_of_eq_mul_cfcAbs`). -/
theorem exists_isPartialIsometry_eq_mul_cfcAbs {N : VonNeumannAlgebra H} {x : H →L[ℂ] H}
    (hx : x ∈ N) :
    ∃ v ∈ N, IsPartialIsometry v ∧ x = v * |x| ∧
      star v * v = (star x).rangeProj ∧ v * star v = x.rangeProj := by
  have haN : CFC.abs x ∈ N := cfcAbs_mem hx
  -- Every `s ∈ N′` intertwines `|x| η ↦ x η`, as it commutes with `|x|` and `x`.
  obtain ⟨v, hvN, hv, hva, hsrc, hrng⟩ := exists_isPartialIsometry_mem_centralizer_of_norm_eq
    (|x| : H →L[ℂ] H) (x : H →ₗ[ℂ] H) (ContinuousLinearMap.norm_cfcAbs_apply x)
    (S := (N′ : Set (H →L[ℂ] H))) (fun _ hs => star_mem (s := N′) hs) fun s hs η => ⟨s η, by
      simp only [ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp,
        mem_commutant_iff.mp hs _ haN, mem_commutant_iff.mp hs _ hx, and_self]⟩
  refine ⟨v, ?_, hv, ContinuousLinearMap.ext fun η => (hva η).symm, ?_, hrng⟩
  · rwa [coe_commutant, centralizer_centralizer] at hvN
  · rw [hsrc, ← ContinuousLinearMap.rangeProj_cfcAbs]; rfl

/-- **The range projections of `x⋆` and `x` are equivalent.** For `x ∈ N`, the range projections
`R(x⋆)` and `R(x)` are Murray–von Neumann equivalent in `N`, through the
partial isometry of the polar decomposition `x = v |x|`
(`exists_isPartialIsometry_eq_mul_cfcAbs`). -/
lemma mvNEquiv_rangeProj {N : VonNeumannAlgebra H} {x : H →L[ℂ] H} (hx : x ∈ N) :
    (star x).rangeProj ∼[N] x.rangeProj :=
  let ⟨v, hvN, hv, _, h₁, h₂⟩ := exists_isPartialIsometry_eq_mul_cfcAbs hx
  ⟨v, hvN, hv, h₁, h₂⟩

end VonNeumannAlgebra
