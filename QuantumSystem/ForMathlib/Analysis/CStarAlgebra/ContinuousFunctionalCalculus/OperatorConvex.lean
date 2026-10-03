/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

/-!
# Operator convex and matrix convex functions, and Jensen's operator inequality

A continuous real function `f` on a set `s ⊆ ℝ` is *operator convex* (`IsOperatorConvexOn`)
when, in every unital C⋆-algebra, `a ↦ f(a)` (the continuous functional calculus `cfc f`) is convex
on the self-adjoint elements with spectrum in `s`. Quantifying over the matrix algebras `M_n(ℂ)`
alone gives *matrix convexity* (`IsMatrixConvexOn`; Bhatia, Chapter V; Effros), which needs no
continuity, since matrices have finite spectra. For `f` continuous on `s` the two agree, but they
differ on discontinuous functions: on `[0, ∞)`, `f(0) = 1` and `f(t) = 0` for `t > 0` gives the
projection `f(A)` onto `ker A`, and is matrix convex (`isMatrixConvexOn_indicator_zero`) but not
operator convex (`not_isOperatorConvexOn_indicator_zero`). The separation is one of conventions: the
obstruction is the continuity that operator convexity requires (Hansen–Pedersen), while the
argument for matrix convexity, `ker(a A + b B) = ker A ∩ ker B`, is algebraic. Bhatia's operator
convexity is matrix convexity in every size, without continuity. Both notions are kept. This file
proves the specialisation `IsOperatorConvexOn.isMatrixConvexOn` (operator convex ⇒ matrix convex),
and the converse direction (matrix convex ⇒ operator convex) for continuous `f` on bounded operators
on a Hilbert space, `IsMatrixConvexOn.convexOn_continuousLinearMap`. The converse in every
C⋆-algebra transfers the Hilbert space case along a faithful representation (Gelfand–Naimark,
`ConvexOn.cfc_of_injective`); it needs the Gelfand–Naimark theorem, which Mathlib does not provide
and which the project builds from direct sums of Mathlib's GNS representations
(`GNS.DirectSum.repStarAlgHom`), and is proved outside `ForMathlib` in
`QuantumSystem/Analysis/CStarAlgebra/OperatorConvex.lean`
(`IsMatrixConvexOn.isOperatorConvexOn`), together with the resulting independence of
`IsOperatorConvexOn` from the universe of the C⋆-algebras it quantifies over
(`isOperatorConvexOn_congr_universe`). The set `s` of a matrix convex function is an interval
(`IsMatrixConvexOn.ordConnected`), and hence so is that of an operator convex one.

The core of Jensen's operator inequality is stated over an arbitrary unital C⋆-algebra `A`, from
the convexity of `cfc f` over the matrix algebra `CStarMatrix ι ι A` and the continuity of `f` on
the spectra that occur; the matrix forms for matrix convex `f` follow by presenting
`CStarMatrix ι ι (Matrix m m ℂ)` as `Matrix (ι × m) (ι × m) ℂ`, and are stated outside `ForMathlib`
in `QuantumSystem/Analysis/Matrix/Order.lean` (`IsMatrixConvexOn.cfc_sum_le`).

## Main definitions

* `IsOperatorConvexOn s f`: `f` is continuous on `s` and, in every unital C⋆-algebra, `cfc f` is
  convex on `{a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s}`.
* `IsMatrixConvexOn s f`: in every matrix size, `cfc f` is convex on the self-adjoint matrices with
  spectrum in `s`.

## Main results

* `setOf_isSelfAdjoint_spectrum_subset_Ici`, `setOf_isSelfAdjoint_spectrum_subset_Ioi`: for
  `s = [0, ∞)` the domain is `Set.Ici 0`, for `s = (0, ∞)` the strictly positive elements;
  `Set.OrdConnected.convex_setOf_isSelfAdjoint_spectrum_subset`: it is convex for an interval `s`,
  and conversely `Set.OrdConnected.of_convex_setOf_isSelfAdjoint_spectrum_subset` for nontrivial
  `A`.
* `exists_algebraMap_le_and_le_algebraMap`, `Set.OrdConnected.spectrum_subset_of_algebraMap_le`:
  common scalar bounds `lo ≤ xᵢ ≤ hi` in `s` of a nonempty finite family of elements of the domain
  of a nontrivial algebra, and the converse passage from scalar bounds to the spectrum.
* `ConvexOn.cfc_of_injective`: convexity of `cfc f` on the domain pulls back along an injective
  unital ⋆-homomorphism, without continuity assumptions.
* `cfc_sum_le_of_convexOn_cstarMatrix` (the implication from convexity to Jensen's inequality in
  Hansen–Pedersen 2003, Theorem 2.1): Jensen's operator inequality
  `f(Σᵢ aᵢ⋆ xᵢ aᵢ) ≤ Σᵢ aᵢ⋆ f(xᵢ) aᵢ` for `Σᵢ aᵢ⋆ aᵢ = 1`, from the convexity of `cfc f` on
  `CStarMatrix ι ι A`, presented through an injective unital ⋆-homomorphism.
* `cfc_sum_le_of_le_one_of_forall` (after Hansen–Pedersen 1982): the
  unital inequality implies the sub-unital one for `Σᵢ aᵢ⋆ aᵢ ≤ 1`, on `s ∋ 0` with `f(0) ≤ 0`.
* `IsOperatorConvexOn.cfc_sum_le`, `IsOperatorConvexOn.cfc_sum_le_of_le_one`: Jensen's operator
  inequality for an operator convex `f`, in the unital and the sub-unital form, in every unital
  C⋆-algebra. The converses of Hansen–Pedersen, from Jensen's inequality back to operator
  convexity, are not stated.
* `IsOperatorConvexOn.isMatrixConvexOn`: an operator convex function is matrix convex;
  `IsMatrixConvexOn.ordConnected`: a matrix convex function is defined on an interval.
* `IsMatrixConvexOn.convexOn_continuousLinearMap`: a continuous matrix convex function is convex on
  the self-adjoint operators on every complex Hilbert space.
* `isOperatorConvexOn_neg_rpow`: `-tᵖ` (`0 ≤ p ≤ 1`) is operator convex on `[0, ∞)`
  (Mathlib's `CFC.concaveOn_rpow`); `isOperatorConvexOn_neg_log`, `isOperatorConvexOn_inv`:
  `-log t` and `t⁻¹` are operator convex on `(0, ∞)` (Mathlib's `CFC.concaveOn_log`,
  `CStarAlgebra.convexOn_ringInverse`).
* `isMatrixConvexOn_neg_rpow`: `-tᵖ` (`0 ≤ p ≤ 1`) is matrix convex on `[0, ∞)`;
  `isMatrixConvexOn_neg_log`, `isMatrixConvexOn_inv`: `-log t` and `t⁻¹` are matrix convex on
  `(0, ∞)`.
* `isMatrixConvexOn_indicator_zero`, `not_isOperatorConvexOn_indicator_zero`: the indicator of
  `{0}` is matrix convex but not operator convex on `[0, ∞)`.

## Implementation notes

The proof of Jensen's inequality follows Hansen–Pedersen. For a partial isometry `v` with
`e = v⋆ v`, `P = v v⋆` and the symmetry `S = 2P - 1`, convexity gives
`f((x + S x S) / 2) ≤ (f(x) + S f(x) S) / 2`, and `v⋆` intertwines `(x + S x S) / 2` with
`v⋆ x v + t (1 - e)`, so compressing by `v` gives `f(v⋆ x v + t (1 - e)) e ≤ v⋆ f(x) v`. The
`n`-term inequality takes `x = diag(xᵢ)` and the column `v` of the `aᵢ` in `CStarMatrix ι ι A` and
reads off a diagonal entry. Every statement about `cfc` in the Jensen inequality is made over an
abstract C⋆-algebra, whose real algebra structure is `Algebra.complexToReal`, so that it applies to
`CStarMatrix` without an instance mismatch; only `IsMatrixConvexOn` uses `cfc` on
`Matrix (Fin n) (Fin n) ℂ` with its own real algebra structure. `cfc_sum_le_of_convexOn_cstarMatrix`
receives the convexity over `CStarMatrix ι ι A` through an injective unital ⋆-homomorphism `ψ` into
another C⋆-algebra `B` (the generality of `ConvexOn.cfc_of_injective`) for two reasons: the matrix
form of Jensen's inequality (`IsMatrixConvexOn.cfc_sum_le` in
`QuantumSystem/Analysis/Matrix/Order.lean`), for `A = Matrix m m ℂ`, takes the convexity of `cfc f`
on `B = Matrix (ι × m) (ι × m) ℂ` from matrix convexity, and operator convexity in the universe of
`A` reaches `CStarMatrix ι ι A` only after reindexing `ι` by `Fin n`; in both cases `ψ` is a
⋆-isomorphism.

The converse on a Hilbert space `H` tests positivity of `t f(X) + u f(Y) - f(tX + uY)` in a
vector state `ξ`. The spectra of `X`, `Y` lie in an interval `[lo, hi] ⊆ s`, on which `f` is
uniformly within `δ` of a polynomial `p` (Weierstrass). On the finite-dimensional Krylov subspace
`F` spanned by the words of length at most `deg p` in `X` and `Y` applied to `ξ`, the compressions
`Z_F` of `Z = X, Y, tX + uY` satisfy `p(Z_F) ξ = p(Z) ξ` and have spectrum in `[lo, hi]`; matrix
convexity applies to them through an orthonormal basis of `F`. The six estimates `f ≈ p`, weighted
by `t` and `u`, cost `4 δ ‖ξ‖²`, and `δ` is arbitrary. No limit of operators is taken.

## TODO

* Operator monotone, antitone and concave functions (`IsOperatorMonotoneOn` and the like), as
  C⋆-algebra predicates alongside `IsOperatorConvexOn`, with the classical examples: `tᵖ`
  (`0 ≤ p ≤ 1`) and `log` (on `(0, ∞)`) are operator monotone and operator concave, `t⁻¹` is
  operator antitone, and `log` is not operator monotone on `[0, ∞)` (Mathlib's `Real.log 0 = 0`).
  Concavity is currently stated only through negation (`isOperatorConvexOn_neg_rpow`,
  `isOperatorConvexOn_neg_log`).
* `tᵖ` is operator convex on `(0, ∞)` for `-1 ≤ p ≤ 0` and on `[0, ∞)` for `1 ≤ p ≤ 2`
  (Bhatia, Chapter V), stated as `IsOperatorConvexOn`; both are also TODOs in Mathlib's
  `Rpow/Order.lean`.
* The converses of Jensen's operator inequality (Hansen–Pedersen 1982 and 2003, Theorem 2.1): a
  continuous `f` satisfying `f(Σᵢ aᵢ⋆ xᵢ aᵢ) ≤ Σᵢ aᵢ⋆ f(xᵢ) aᵢ` is operator convex.
* Jensen's operator inequality for continuous fields of operators (Hansen–Pedersen 2003),
  `f(∫ aₜ⋆ xₜ aₜ dμ(t)) ≤ ∫ aₜ⋆ f(xₜ) aₜ dμ(t)` for `∫ aₜ⋆ aₜ dμ(t) = 1`; only finite families are
  stated here.

## References

* F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
  Math. Ann. 258 (1982), 229–241
* F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, Bull. London Math. Soc. 35 (2003),
  553–564
* R. Bhatia, *Matrix Analysis*, Chapter V (1997)
* E. G. Effros, *A matrix convexity approach to some celebrated quantum inequalities*, Proc. Natl.
  Acad. Sci. USA 106 (2009), 1006–1008
-/

@[expose] public section

open Set

/-! ### The domain of an operator function -/

section Domain

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

/-- The self-adjoint elements with spectrum in `[0, ∞)` are the nonnegative elements. -/
theorem setOf_isSelfAdjoint_spectrum_subset_Ici :
    {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ici 0} = Ici 0 := by
  ext a
  refine ⟨fun ⟨ha, h⟩ => (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a ha).2
      fun x hx => h hx,
    fun h => ⟨IsSelfAdjoint.of_nonneg h, fun x hx =>
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a (IsSelfAdjoint.of_nonneg h)).1 h x hx⟩⟩

/-- The self-adjoint elements with spectrum in `(0, ∞)` are the strictly positive elements. -/
theorem setOf_isSelfAdjoint_spectrum_subset_Ioi :
    {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ioi 0} = {a | IsStrictlyPositive a} := by
  ext a
  refine ⟨fun ⟨ha, h⟩ => (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) a ha).2
      fun x hx => h hx,
    fun h => ⟨h.isSelfAdjoint, fun x hx =>
      (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) a h.isSelfAdjoint).1 h x hx⟩⟩

omit [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] in
/-- A real scalar `t ∈ s` lies in the domain for `s`. -/
theorem algebraMap_mem_setOf_isSelfAdjoint_spectrum_subset [StarModule ℝ A] {s : Set ℝ} {t : ℝ}
    (ht : t ∈ s) : algebraMap ℝ A t ∈ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} :=
  ⟨IsSelfAdjoint.algebraMap _ (.all t),
    (CFC.spectrum_algebraMap_subset t).trans (singleton_subset_iff.2 ht)⟩

omit [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] in
/-- The zero element lies in the domain for `s ∋ 0`. -/
theorem zero_mem_setOf_isSelfAdjoint_spectrum_subset [StarModule ℝ A] {s : Set ℝ}
    (h0 : (0 : ℝ) ∈ s) : (0 : A) ∈ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} :=
  map_zero (algebraMap ℝ A) ▸ algebraMap_mem_setOf_isSelfAdjoint_spectrum_subset h0

omit [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] in
/-- If the self-adjoint elements with spectrum in `s` of a nontrivial algebra form a convex set,
then `s` is an interval: it contains the convex combinations of the scalars in it. -/
theorem Set.OrdConnected.of_convex_setOf_isSelfAdjoint_spectrum_subset [StarModule ℝ A]
    [Nontrivial A] {s : Set ℝ} (h : Convex ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s}) :
    s.OrdConnected := by
  rw [← convex_iff_ordConnected]
  intro r hr r' hr' α β hα hβ hαβ
  have h' := (h (algebraMap_mem_setOf_isSelfAdjoint_spectrum_subset hr)
    (algebraMap_mem_setOf_isSelfAdjoint_spectrum_subset hr') hα hβ hαβ).2
  rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul, ← map_add, spectrum.scalar_eq]
    at h'
  exact h' rfl

/-- Scalar bounds `lo ≤ a ≤ hi` with `lo, hi` in an order-connected `s` confine the spectrum of a
self-adjoint `a` to `s`. -/
theorem Set.OrdConnected.spectrum_subset_of_algebraMap_le {s : Set ℝ} (hs : s.OrdConnected)
    {a : A} (ha : IsSelfAdjoint a) {lo hi : ℝ} (hlo : lo ∈ s) (hhi : hi ∈ s)
    (h₁ : algebraMap ℝ A lo ≤ a) (h₂ : a ≤ algebraMap ℝ A hi) : spectrum ℝ a ⊆ s :=
  fun x hx => hs.out hlo hhi ⟨(algebraMap_le_iff_le_spectrum ha).1 h₁ x hx,
    (le_algebraMap_iff_spectrum_le ha).1 h₂ x hx⟩

/-- A nonempty finite family of self-adjoint elements of a nontrivial algebra with spectra in `s`
has common scalar bounds `lo ≤ xᵢ ≤ hi` with `lo, hi ∈ s`: the least and the greatest point of the
compact union of the spectra. -/
theorem exists_algebraMap_le_and_le_algebraMap [Nontrivial A] {ι : Type*} [Finite ι] [Nonempty ι]
    {s : Set ℝ} {x : ι → A} (hx : ∀ i, x i ∈ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s}) :
    ∃ lo ∈ s, ∃ hi ∈ s, ∀ i, algebraMap ℝ A lo ≤ x i ∧ x i ≤ algebraMap ℝ A hi := by
  have hK : IsCompact (⋃ i, spectrum ℝ (x i)) :=
    isCompact_iUnion fun i => ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) (x i)
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hne : (⋃ i, spectrum ℝ (x i)).Nonempty :=
    ⟨_, mem_iUnion.2 ⟨i₁,
      (ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (x i₁) (hx i₁).1).some_mem⟩⟩
  obtain ⟨lo, hlo⟩ := hK.exists_isLeast hne
  obtain ⟨hi, hhi⟩ := hK.exists_isGreatest hne
  have hmem {r : ℝ} (hr : r ∈ ⋃ i, spectrum ℝ (x i)) : r ∈ s := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hr
    exact (hx i).2 hi
  exact ⟨lo, hmem hlo.1, hi, hmem hhi.1, fun i =>
    ⟨(algebraMap_le_iff_le_spectrum (hx i).1).2 fun y hy => hlo.2 (mem_iUnion.2 ⟨i, hy⟩),
      (le_algebraMap_iff_spectrum_le (hx i).1).2 fun y hy => hhi.2 (mem_iUnion.2 ⟨i, hy⟩)⟩⟩

/-- For an order-connected `s ⊆ ℝ`, the self-adjoint elements with spectrum in `s` form a convex
set. -/
theorem Set.OrdConnected.convex_setOf_isSelfAdjoint_spectrum_subset [StarModule ℝ A]
    {s : Set ℝ} (hs : s.OrdConnected) :
    Convex ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} := by
  rintro a ha b hb t u ht hu htu
  have hc : IsSelfAdjoint (t • a + u • b) :=
    ((IsSelfAdjoint.all t).smul ha.1).add ((IsSelfAdjoint.all u).smul hb.1)
  refine ⟨hc, ?_⟩
  rcases subsingleton_or_nontrivial A with _ | _
  · simp [spectrum.of_subsingleton]
  obtain ⟨lo, hlo, hi, hhi, hbd⟩ :=
    exists_algebraMap_le_and_le_algebraMap (x := ![a, b]) (Fin.forall_fin_two.2 ⟨ha, hb⟩)
  have h := convex_Icc (𝕜 := ℝ) (algebraMap ℝ A lo) (algebraMap ℝ A hi) (hbd 0) (hbd 1) ht hu htu
  exact hs.spectrum_subset_of_algebraMap_le hc hlo hhi h.1 h.2

end Domain

section Pi

variable {ι A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

/-- A continuous ⋆-homomorphism out of `ι → A` intertwines the continuous functional calculus
coordinatewise: `f(φ(d)) = φ(i ↦ f(dᵢ))` for self-adjoint `dᵢ`. -/
private lemma StarAlgHom.cfc_map_pi [Finite ι] (φ : (ι → A) →⋆ₐ[ℂ] C) (hφ : Continuous φ)
    (f : ℝ → ℝ) (d : ι → A) (hd : ∀ i, IsSelfAdjoint (d i))
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (d i))) :
    cfc f (φ d) = φ fun i => cfc f (d i) := by
  have := Fintype.ofFinite ι
  let _ : Algebra ℝ (ι → A) := Algebra.complexToReal
  have hd' : IsSelfAdjoint d := funext hd
  have hspec : spectrum ℝ d = ⋃ i, spectrum ℝ (d i) := Pi.spectrum_eq d
  have hpi : cfc f d = fun i => cfc f (d i) := by
    funext i
    exact (Pi.evalStarAlgHom ℂ (fun _ => A) i).map_cfc f d (by rwa [hspec]) (continuous_apply i)
      hd' (hd i)
  rw [← hpi]
  exact (φ.map_cfc f d (by rwa [hspec]) hφ hd' (hd'.map φ)).symm

/-- A ⋆-homomorphism out of `ι → A` maps an element into one whose real spectrum lies in the union
of the spectra of the coordinates. -/
private lemma StarAlgHom.spectrum_map_pi_subset (φ : (ι → A) →⋆ₐ[ℂ] C) (d : ι → A) :
    spectrum ℝ (φ d) ⊆ ⋃ i, spectrum ℝ (d i) := by
  let _ : Algebra ℝ (ι → A) := Algebra.complexToReal
  have hspec : spectrum ℝ d = ⋃ i, spectrum ℝ (d i) := Pi.spectrum_eq d
  rw [← hspec]
  exact AlgHom.spectrum_apply_subset (φ.toAlgHom.restrictScalars ℝ) d

/-- An injective ⋆-homomorphism out of `ι → A` preserves the real spectrum of a self-adjoint
element, which is the union of the spectra of its coordinates. -/
private lemma StarAlgHom.spectrum_map_pi [Finite ι] (φ : (ι → A) →⋆ₐ[ℂ] C)
    (hφ : Function.Injective φ) (hφ' : Continuous φ) (d : ι → A) (hd : ∀ i, IsSelfAdjoint (d i)) :
    spectrum ℝ (φ d) = ⋃ i, spectrum ℝ (d i) := by
  have := Fintype.ofFinite ι
  let _ : Algebra ℝ (ι → A) := Algebra.complexToReal
  let _ : ContinuousFunctionalCalculus ℝ (ι → A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hd' : IsSelfAdjoint d := funext hd
  have hspec : spectrum ℝ d = ⋃ i, spectrum ℝ (d i) := Pi.spectrum_eq d
  rw [← hspec]
  exact hd'.map_spectrum_real φ hφ hφ'

end Pi

namespace CStarMatrix

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal embedding `(ι → A) → CStarMatrix ι ι A` as a ⋆-algebra homomorphism. -/
private noncomputable def diagonalStarAlgHom [CStarAlgebra A] :
    (ι → A) →⋆ₐ[ℂ] CStarMatrix ι ι A where
  toFun d := ofMatrix (Matrix.diagonal d)
  map_one' := by
    ext i j
    simp only [ofMatrix_apply, Matrix.diagonal_apply, Pi.one_apply]
    rfl
  map_mul' a b := by
    ext i j
    simp only [mul_apply, Matrix.diagonal_apply, ofMatrix_apply, ite_mul, zero_mul, Pi.mul_apply]
    split_ifs with h <;> simp [h]
  map_zero' := by
    ext i j
    simp [zero_apply, ofMatrix_apply]
  map_add' a b := by
    ext i j
    simp [Matrix.diagonal_apply, ofMatrix_apply, apply_ite₂ (· + ·)]
  commutes' r := by
    ext i j
    simp [algebraMap_apply, Matrix.diagonal_apply, ofMatrix_apply]
  map_star' d := by
    ext i j
    simp only [star_apply, ofMatrix_apply, Matrix.diagonal_apply, Pi.star_apply]
    split_ifs with h h' h' <;> simp_all

@[simp] private lemma diagonalStarAlgHom_apply [CStarAlgebra A] (d : ι → A) (i j : ι) :
    diagonalStarAlgHom d i j = if i = j then d i else 0 :=
  rfl

private lemma continuous_diagonalStarAlgHom [CStarAlgebra A] :
    Continuous (diagonalStarAlgHom (ι := ι) (A := A)) :=
  continuous_pi fun i => continuous_pi fun j => by
    simp only [diagonalStarAlgHom_apply]
    split_ifs <;> fun_prop

/-- The diagonal embedding is injective. -/
private lemma diagonalStarAlgHom_injective [CStarAlgebra A] :
    Function.Injective (diagonalStarAlgHom (ι := ι) (A := A)) := fun d d' h => by
  funext i
  simpa using congrFun (congrFun (congrArg (fun M : CStarMatrix ι ι A => (M : ι → ι → A)) h) i) i

end CStarMatrix

namespace CStarMatrix

variable {ι A : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The diagonal entries of a nonnegative matrix over a C⋆-algebra are nonnegative. -/
private lemma apply_self_nonneg {M : CStarMatrix ι ι A} (hM : 0 ≤ M) (i : ι) : 0 ≤ M i i := by
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    change 0 ≤ (star y * y) i i
    rw [mul_apply]
    exact Finset.sum_nonneg fun k _ => by simp [star_apply]
  | zero => exact le_of_eq (zero_apply i i).symm
  | add x y _ _ hx hy => simpa using add_nonneg hx hy

/-- The diagonal entries are monotone in the order of matrices over a C⋆-algebra. -/
private lemma apply_self_le_apply_self {M N : CStarMatrix ι ι A} (h : M ≤ N) (i : ι) :
    M i i ≤ N i i := by
  have := apply_self_nonneg (sub_nonneg.2 h) i
  rwa [sub_apply, sub_nonneg] at this

end CStarMatrix

section Intertwining

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- `Commute.cfc_real` with the real functional calculus of the C⋆-algebra structure. Stated over
an abstract C⋆-algebra `C`, so that at `C = CStarMatrix ι ι B` the real functional calculus is the
one coming from `CStarAlgebra` (through `Algebra.complexToReal`); applied there directly,
`Commute.cfc_real` looks for `ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι B) IsSelfAdjoint`
with `CStarMatrix`'s own real algebra structure and finds no instance. -/
private lemma commute_cfc_real {C : Type*} [CStarAlgebra C] {a b : C} (h : Commute a b)
    (f : ℝ → ℝ) : Commute (cfc f a) b :=
  h.cfc_real f

/-- **Intertwining**: if `y a = b y` for self-adjoint `a, b`, then `y f(a) = f(b) y` for every `f`
continuous on the spectra. The proof applies `Commute.cfc_real` to `a ⊕ b` and the off-diagonal
matrix `(0 0; y 0)` in `CStarMatrix (Fin 2) (Fin 2) B`. -/
private lemma SemiconjBy.cfc_real {a b y : B} (h : SemiconjBy y a b) (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a ∪ spectrum ℝ b)) :
    SemiconjBy y (cfc f a) (cfc f b) := by
  let d : Fin 2 → B := ![a, b]
  let z : CStarMatrix (Fin 2) (Fin 2) B := CStarMatrix.ofMatrix !![0, 0; y, 0]
  have hd : ∀ i, IsSelfAdjoint (d i) := Fin.forall_fin_two.2 ⟨ha, hb⟩
  have hdf : ContinuousOn f (⋃ i, spectrum ℝ (d i)) := by
    refine hf.mono fun r hr => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 hr
    fin_cases i
    exacts [Or.inl hi, Or.inr hi]
  have hcomm : Commute (CStarMatrix.diagonalStarAlgHom d) z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CStarMatrix.mul_apply, d, z, CStarMatrix.ofMatrix_apply, h.eq]
  have hc := commute_cfc_real hcomm f
  rw [StarAlgHom.cfc_map_pi _ CStarMatrix.continuous_diagonalStarAlgHom f d hd hdf] at hc
  have h10 := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) B => M 1 0) hc.eq
  change y * cfc f a = cfc f b * y
  simpa [CStarMatrix.mul_apply, Fin.sum_univ_two, d, z, CStarMatrix.ofMatrix_apply] using h10.symm

/-- Jensen's inequality for a partial isometry `v`, the core of Hansen–Pedersen's proof: with
`e = v⋆ v` a projection, `t ∈ s` and `n = v⋆ x v + t (1 - e)`, `f(n) e ≤ v⋆ f(x) v`. -/
private lemma cfc_mul_le_of_isIdempotentElem {s : Set ℝ} {f : ℝ → ℝ} (hs : s.OrdConnected)
    (hcont : ∀ b : B, IsSelfAdjoint b → spectrum ℝ b ⊆ s → ContinuousOn f (spectrum ℝ b))
    (hconv : ConvexOn ℝ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} (cfc f))
    {v x n : B} (hv : IsIdempotentElem (star v * v)) (hx : IsSelfAdjoint x)
    (hxs : spectrum ℝ x ⊆ s) {t : ℝ} (ht : t ∈ s)
    (hn : star v * x * v + (t : ℂ) • (1 - star v * v) = n) :
    cfc f n * (star v * v) ≤ star v * cfc f x * v := by
  subst hn
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact le_of_eq (Subsingleton.elim _ _)
  set e := star v * v with he_def
  have he_sa : IsSelfAdjoint e := by simp [e, IsSelfAdjoint, star_mul]
  have hee : e * e = e := hv.eq
  have hve : v * e = v := by
    have h0 : star (v - v * e) * (v - v * e) = 0 := by
      rw [star_sub, star_mul, he_sa.star_eq]
      calc (star v - e * star v) * (v - v * e) = e - e * e - e * e + e * e * e := by
            simp only [he_def]; noncomm_ring
        _ = 0 := by rw [hee, hee]; abel
    exact (sub_eq_zero.1 ((CStarRing.star_mul_self_eq_zero_iff _).1 h0)).symm
  have hsve : e * star v = star v := by
    have := congrArg star hve
    rwa [star_mul, he_sa.star_eq] at this
  set P := v * star v with hP_def
  have hPv : P * v = v := by rw [hP_def, mul_assoc, ← he_def, hve]
  have hvP : star v * P = star v := by rw [hP_def, ← mul_assoc, ← he_def, hsve]
  have hPP : P * P = P := by
    calc P * P = P * v * star v := by simp only [hP_def, mul_assoc]
      _ = P := by rw [hPv]
  have hP_sa : star P = P := by simp [hP_def, star_mul]
  set S := P + P - 1 with hS_def
  have hS_sa : star S = S := by simp [hS_def, hP_sa]
  have hSS : S * S = 1 := by
    calc S * S = (P * P + P * P + P * P + P * P) - (P + P + P + P) + 1 := by
          rw [hS_def]; noncomm_ring
      _ = 1 := by rw [hPP]; abel
  let U : unitary B := ⟨S, Unitary.mem_iff.2 ⟨by rw [hS_sa, hSS], by rw [hS_sa, hSS]⟩⟩
  have hSv : S * v = v := by
    rw [hS_def, sub_mul, add_mul, one_mul, hPv, add_sub_cancel_right]
  have hvS : star v * S = star v := by
    rw [hS_def, mul_sub, mul_add, mul_one, hvP, add_sub_cancel_right]
  -- the conjugate `S x S`
  have hx' : IsSelfAdjoint (S * x * S) := by simpa [hS_sa] using hx.conjugate S
  have hx's : spectrum ℝ (S * x * S) ⊆ s := by
    have h : spectrum ℝ ((U : B) * x * star (U : B)) = spectrum ℝ x :=
      Unitary.spectrum_star_right_conjugate
    simp only [U, hS_sa] at h
    rwa [h]
  have hconj : cfc f (S * x * S) = S * cfc f x * S := by
    have hφ : ⇑(Unitary.conjStarAlgAut ℂ B U) = fun z => (U : B) * z * star (U : B) :=
      funext fun z => Unitary.conjStarAlgAut_apply U z
    have h := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ B U) f x (hcont x hx hxs)
      (by rw [hφ]; fun_prop) hx (hx.map _)
    simpa [hφ, U, hS_sa] using h.symm
  -- the pinching `M = (x + S x S) / 2`
  have hxmem : x ∈ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} := ⟨hx, hxs⟩
  have hx'mem : S * x * S ∈ {a : B | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} := ⟨hx', hx's⟩
  have hMmem := hconv.1 hxmem hx'mem (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hMle := hconv.2 hxmem hx'mem (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hM_eq : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (S * x * S) = P * x * P + (1 - P) * x * (1 - P) := by
    rw [hS_def]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
    module
  -- the corner `n = v⋆ x v + t (1 - e)`
  have hcoe : ((t : ℂ) • (1 - e) : B) = t • (1 - e) :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) t (1 - e)).symm
  have he0 : 0 ≤ e := star_mul_self_nonneg v
  have he1 : 0 ≤ 1 - e := by
    have h : star (1 - e) * (1 - e) = 1 - e := by
      rw [star_sub, star_one, he_sa.star_eq, sub_mul, one_mul, mul_sub, mul_one, hee, sub_self,
        sub_zero]
    exact h ▸ star_mul_self_nonneg (1 - e)
  have hN_sa : IsSelfAdjoint (star v * x * v + (t : ℂ) • (1 - e)) := by
    rw [hcoe]
    exact (hx.conjugate' v).add ((IsSelfAdjoint.all t).smul ((IsSelfAdjoint.one B).sub he_sa))
  have hNs : spectrum ℝ (star v * x * v + (t : ℂ) • (1 - e)) ⊆ s := by
    obtain ⟨lo, hlo, hi, hhi, hbd⟩ :=
      exists_algebraMap_le_and_le_algebraMap (x := fun _ : Unit => x) fun _ => hxmem
    have hscal (r : ℝ) : star v * algebraMap ℝ B r * v = r • e := by
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
    have hsplit (r : ℝ) : algebraMap ℝ B r = r • e + r • (1 - e) := by
      rw [← smul_add, add_sub_cancel, Algebra.algebraMap_eq_smul_one]
    refine hs.spectrum_subset_of_algebraMap_le hN_sa (min_rec' (· ∈ s) hlo ht)
      (max_rec' (· ∈ s) hhi ht) ?_ ?_
    · rw [hcoe, hsplit, ← hscal]
      exact add_le_add (star_left_conjugate_le_conjugate
          ((algebraMap_mono B (min_le_left lo t)).trans (hbd ()).1) v)
        (smul_le_smul_of_nonneg_right (min_le_right lo t) he1)
    · rw [hcoe, hsplit, ← hscal]
      exact add_le_add (star_left_conjugate_le_conjugate
          ((hbd ()).2.trans (algebraMap_mono B (le_max_left hi t))) v)
        (smul_le_smul_of_nonneg_right (le_max_right hi t) he1)
  have hsemi : SemiconjBy (star v) ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (S * x * S))
      (star v * x * v + (t : ℂ) • (1 - e)) := by
    have h1 : star v * (1 - P) = 0 := by rw [mul_sub, mul_one, hvP, sub_self]
    have h2 : (1 - e) * star v = 0 := by rw [sub_mul, one_mul, hsve, sub_self]
    rw [SemiconjBy, hM_eq]
    calc star v * (P * x * P + (1 - P) * x * (1 - P))
        = star v * P * x * P + star v * (1 - P) * x * (1 - P) := by noncomm_ring
      _ = star v * x * v * star v := by
          rw [hvP, h1, hP_def]; simp only [mul_assoc, zero_mul, add_zero]
      _ = (star v * x * v + (t : ℂ) • (1 - e)) * star v := by
          rw [add_mul, smul_mul_assoc, h2, smul_zero, add_zero]
  have hint := hsemi.cfc_real hMmem.1 hN_sa f
    ((hcont _ hMmem.1 hMmem.2).union_of_isClosed (hcont _ hN_sa hNs)
      (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) _).isClosed
      (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) _).isClosed)
  calc cfc f (star v * x * v + (t : ℂ) • (1 - e)) * e
      = cfc f (star v * x * v + (t : ℂ) • (1 - e)) * star v * v := (mul_assoc _ _ _).symm
    _ = star v * cfc f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (S * x * S)) * v := by rw [hint.eq]
    _ ≤ star v * ((1 / 2 : ℝ) • cfc f x + (1 / 2 : ℝ) • cfc f (S * x * S)) * v :=
        star_left_conjugate_le_conjugate hMle v
    _ = star v * cfc f x * v := by
        have h : star v * (S * cfc f x * S) * v = star v * cfc f x * v := by
          calc star v * (S * cfc f x * S) * v = star v * S * cfc f x * (S * v) := by
                simp only [mul_assoc]
            _ = star v * cfc f x * v := by rw [hvS, hSv]
        rw [hconj, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
          h, ← add_smul]
        norm_num

end Intertwining

/-! ### Transport along injective ⋆-homomorphisms -/

section Transport

variable {F B C : Type*} [CStarAlgebra B] [CStarAlgebra C] [PartialOrder B] [PartialOrder C]
  [StarOrderedRing B] [StarOrderedRing C] [FunLike F B C] [AlgHomClass F ℂ B C] [StarHomClass F B C]
  {s : Set ℝ} {f : ℝ → ℝ}

omit [PartialOrder B] [PartialOrder C] [StarOrderedRing B] [StarOrderedRing C] in
/-- An injective ⋆-homomorphism of C⋆-algebras commutes with the real functional calculus of a
self-adjoint element, for every `f`: when `f` is not continuous on the spectrum, both sides are
`0`. -/
private lemma map_cfc_real_of_injective (φ : F) (hφ : Function.Injective φ) (f : ℝ → ℝ) {b : B}
    (hb : IsSelfAdjoint b) :
    φ (cfc f b) = cfc f (φ b) := by
  have hcont : Continuous φ := (NonUnitalStarAlgHom.isometry φ hφ).continuous
  by_cases hc : ContinuousOn f (spectrum ℝ b)
  · exact StarAlgHomClass.map_cfc φ f b hc hcont hb (hb.map φ)
  · rw [cfc_apply_of_not_continuousOn b hc, map_zero, cfc_apply_of_not_continuousOn (φ b)]
    rwa [hb.map_spectrum_real φ hφ hcont]

omit [PartialOrder B] [PartialOrder C] [StarOrderedRing B] [StarOrderedRing C] in
/-- An injective ⋆-homomorphism maps an element into the self-adjoint elements with spectrum
in `s` exactly when the element is self-adjoint with spectrum in `s`. -/
private lemma map_mem_setOf_isSelfAdjoint_spectrum_subset_iff (φ : F) (hφ : Function.Injective φ)
    {b : B} :
    φ b ∈ {c : C | IsSelfAdjoint c ∧ spectrum ℝ c ⊆ s} ↔
      b ∈ {b : B | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s} := by
  have hcont : Continuous φ := (NonUnitalStarAlgHom.isometry φ hφ).continuous
  constructor
  · rintro ⟨h₁, h₂⟩
    have hb : IsSelfAdjoint b := h₁.of_map φ hφ
    exact ⟨hb, by rwa [hb.map_spectrum_real φ hφ hcont] at h₂⟩
  · rintro ⟨hb, hs⟩
    exact ⟨hb.map φ, by rwa [hb.map_spectrum_real φ hφ hcont]⟩

omit [PartialOrder B] [PartialOrder C] [StarOrderedRing B] [StarOrderedRing C] in
/-- Continuity of `f` on the spectra of the self-adjoint elements with spectrum in `s` pulls back
along an injective ⋆-homomorphism. -/
private lemma continuousOn_spectrum_of_forall_of_injective (φ : F) (hφ : Function.Injective φ)
    (hcont : ∀ c : C, IsSelfAdjoint c → spectrum ℝ c ⊆ s → ContinuousOn f (spectrum ℝ c)) :
    ∀ b : B, IsSelfAdjoint b → spectrum ℝ b ⊆ s → ContinuousOn f (spectrum ℝ b) :=
  fun b hb hbs => by
    have h := (map_mem_setOf_isSelfAdjoint_spectrum_subset_iff φ hφ).2 ⟨hb, hbs⟩
    rw [← hb.map_spectrum_real φ hφ (NonUnitalStarAlgHom.isometry φ hφ).continuous]
    exact hcont (φ b) h.1 h.2

omit [PartialOrder B] [PartialOrder C] [StarOrderedRing B] [StarOrderedRing C]
  [StarHomClass F B C] in
/-- A homomorphism of complex algebras is `ℝ`-linear. -/
private lemma map_real_smul_of_algHomClass (φ : F) (r : ℝ) (b : B) :
    φ (r • b) = r • φ b := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, ← RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- Convexity of `cfc f` on the self-adjoint elements with spectrum in `s` pulls back along an
injective unital ⋆-homomorphism of C⋆-algebras, without any continuity of `f`. An injective
⋆-homomorphism preserves the spectrum of a self-adjoint element, commutes with `cfc f`, and
reflects the order (`NonUnitalStarAlgHom.map_le_map_iff`). This covers ⋆-isomorphisms and faithful
representations on a Hilbert space alike. -/
lemma ConvexOn.cfc_of_injective (φ : F) (hφ : Function.Injective φ)
    (h : ConvexOn ℝ {c : C | IsSelfAdjoint c ∧ spectrum ℝ c ⊆ s} (cfc f)) :
    ConvexOn ℝ {b : B | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s} (cfc f) := by
  have hmem {b : B} := map_mem_setOf_isSelfAdjoint_spectrum_subset_iff (s := s) φ hφ (b := b)
  refine ⟨fun b₁ hb₁ b₂ hb₂ t u ht hu htu => ?_, fun b₁ hb₁ b₂ hb₂ t u ht hu htu => ?_⟩
  · rw [← hmem, map_add, map_real_smul_of_algHomClass, map_real_smul_of_algHomClass]
    exact h.1 (hmem.2 hb₁) (hmem.2 hb₂) ht hu htu
  · have hsa : IsSelfAdjoint (t • b₁ + u • b₂) :=
      ((IsSelfAdjoint.all t).smul hb₁.1).add ((IsSelfAdjoint.all u).smul hb₂.1)
    rw [← NonUnitalStarAlgHom.map_le_map_iff φ hφ, map_cfc_real_of_injective φ hφ f hsa]
    simp only [map_add, map_real_smul_of_algHomClass, map_cfc_real_of_injective φ hφ f hb₁.1,
      map_cfc_real_of_injective φ hφ f hb₂.1]
    exact h.2 (hmem.2 hb₁) (hmem.2 hb₂) ht hu htu

end Transport

/-! ### Operator convex and matrix convex functions -/

/-- A real function `f` is **operator convex** on `s ⊆ ℝ`: it is continuous on `s`, and in every
unital C⋆-algebra `a ↦ f(a)` is convex on the self-adjoint elements with spectrum in `s`.

The C⋆-algebras range over a universe `u`, so `IsOperatorConvexOn.{u} s f` is a priori one predicate
per universe; `IsOperatorConvexOn.isMatrixConvexOn` reads the matrix algebras off any of them. The
predicates agree across universes, since each is equivalent to continuity and matrix convexity
(Hansen–Pedersen). The direction from matrix convexity to operator convexity needs
Gelfand–Naimark and is proved outside `ForMathlib`, in
`QuantumSystem/Analysis/CStarAlgebra/OperatorConvex.lean` (`isOperatorConvexOn_congr_universe`);
the examples below are proved uniformly in every C⋆-algebra and hold in every universe.

The field `continuousOn` follows the definition of Hansen–Pedersen; Bhatia's operator convexity,
which asks for no continuity, is `IsMatrixConvexOn`. It
is not independent of `convexOn`: Mathlib's junk value `cfc f a = 0` for `f` discontinuous on the
spectrum of `a` makes convexity in every C⋆-algebra force continuity, but that derivation has no
mathematical content, so continuity is kept as a field. When `s` has at most one point the domain
is at most a scalar and both predicates hold for every `f` continuous on `s`. -/
structure IsOperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop where
  /-- `f` is continuous on `s`. -/
  continuousOn : ContinuousOn f s
  /-- In every unital C⋆-algebra, `cfc f` is convex on the self-adjoint elements with spectrum
  in `s`. -/
  convexOn : ∀ (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
    ConvexOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} (cfc f)

section MatrixPredicates

universe u

open scoped MatrixOrder

/-- A real function `f` is **matrix convex** on `s ⊆ ℝ` (Bhatia, Chapter V; Effros 2009): in every
matrix size, `A ↦ f(A)` is convex in the Löwner order on the self-adjoint matrices with spectrum
in `s`. -/
def IsMatrixConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ConvexOn ℝ {A : Matrix (Fin n) (Fin n) ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s} (cfc f)

variable {s : Set ℝ} {f : ℝ → ℝ}

open scoped Matrix.Norms.L2Operator

/-- An operator convex function is matrix convex: in universe `u`, the operator convexity applies to
the matrices indexed by `ULift.{u} (Fin n)`, and reindexing along `Equiv.ulift` pulls it back to
`Fin n` (`ConvexOn.cfc_of_injective`).

The universe `u` does not occur in the conclusion, so a universe-polymorphic hypothesis must fix it
at the call site, e.g. `isOperatorConvexOn_inv.{0}.isMatrixConvexOn`. The lemma is stated for every
`u` because the independence of the universe (`isOperatorConvexOn_congr_universe` in
`QuantumSystem/Analysis/CStarAlgebra/OperatorConvex.lean`) is proved from it, together with the
direction from matrix convexity to operator convexity. -/
lemma IsOperatorConvexOn.isMatrixConvexOn (hf : IsOperatorConvexOn.{u} s f) :
    IsMatrixConvexOn s f := fun n => by
  let e : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) ℂ :=
    StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ Equiv.ulift.symm) fun M => by
      simp [Matrix.coe_reindexAlgEquiv, Matrix.star_eq_conjTranspose]
  exact ConvexOn.cfc_of_injective e e.injective (hf.convexOn _)

/-- The set `s` of a matrix convex function is an interval: its domain in `M_1(ℂ)` is convex. -/
lemma IsMatrixConvexOn.ordConnected (hf : IsMatrixConvexOn s f) : s.OrdConnected :=
  Set.OrdConnected.of_convex_setOf_isSelfAdjoint_spectrum_subset (hf 1).1

end MatrixPredicates

/-! ### Jensen's operator inequality -/

section JensenTheorems

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {s : Set ℝ} {f : ℝ → ℝ}

omit [PartialOrder A] [StarOrderedRing A] in
/-- A sum `Σᵢ aᵢ⋆ xᵢ aᵢ` of conjugates of self-adjoint elements is self-adjoint. -/
private lemma isSelfAdjoint_sum_star_mul_mul {ι : Type*} [Fintype ι] (a x : ι → A)
    (hx : ∀ i, IsSelfAdjoint (x i)) : IsSelfAdjoint (∑ i, star (a i) * x i * a i) :=
  isSelfAdjoint_sum _ fun i _ => (hx i).conjugate' (a i)

/-- A combination `Σᵢ aᵢ⋆ xᵢ aᵢ` with `Σᵢ aᵢ⋆ aᵢ = 1` of self-adjoint elements with spectra in an
interval `s` has its spectrum in `s`. -/
private lemma spectrum_sum_star_mul_mul_subset {ι : Type*} [Fintype ι] (hs : s.OrdConnected)
    (a x : ι → A) (hx : ∀ i, x i ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s})
    (ha : ∑ i, star (a i) * a i = 1) :
    spectrum ℝ (∑ i, star (a i) * x i * a i) ⊆ s := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · simp [spectrum.of_subsingleton]
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at ha
  obtain ⟨lo, hlo, hi, hhi, hbd⟩ := exists_algebraMap_le_and_le_algebraMap hx
  have hscal (r : ℝ) : ∑ i, star (a i) * algebraMap ℝ A r * a i = algebraMap ℝ A r := by
    simp_rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      ← Finset.smul_sum, ha]
  refine hs.spectrum_subset_of_algebraMap_le (isSelfAdjoint_sum_star_mul_mul a x fun i => (hx i).1)
    hlo hhi ?_ ?_
  · rw [← hscal]
    exact Finset.sum_le_sum fun i _ => star_left_conjugate_le_conjugate (hbd i).1 _
  · rw [← hscal]
    exact Finset.sum_le_sum fun i _ => star_left_conjugate_le_conjugate (hbd i).2 _

/-- **Jensen's operator inequality from matrix convexity over `A`**: if `cfc f` is convex on the
self-adjoint elements of `CStarMatrix ι ι A` with spectrum in `s`, and `f` is continuous on the
spectrum of every such element, then `f(Σᵢ aᵢ⋆ xᵢ aᵢ) ≤ Σᵢ aᵢ⋆ f(xᵢ) aᵢ` for every family
`aᵢ` with `Σᵢ aᵢ⋆ aᵢ = 1` and self-adjoint `xᵢ ∈ A` with spectrum in `s`. The convexity and the
continuity are received on a C⋆-algebra `B` through an injective unital ⋆-homomorphism
`ψ : CStarMatrix ι ι A → B`, along which both pull back (`ConvexOn.cfc_of_injective`). This covers
⋆-isomorphisms, so that `B` may be a matrix algebra `Matrix (ι × m) (ι × m) ℂ` when
`A = Matrix m m ℂ`: this is the form that matrix convexity alone supplies
(`IsMatrixConvexOn.cfc_sum_le`, outside `ForMathlib` in `QuantumSystem/Analysis/Matrix/Order.lean`).
For operator convex `f` (`IsOperatorConvexOn.cfc_sum_le`), `ψ` is the reindexing
`CStarMatrix.reindexₐ` along `Fintype.equivFin ι` onto `CStarMatrix (Fin n) (Fin n) A`,
`n = card ι`, which lies in the universe of `A`. It also covers faithful representations of
`CStarMatrix ι ι A` on a Hilbert space. The proof reads the inequality for the partial isometry `v`
with the `aᵢ` in a column and `x = diag(xᵢ)` off a diagonal entry. -/
theorem cfc_sum_le_of_convexOn_cstarMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {F : Type*} [FunLike F (CStarMatrix ι ι A) B] [AlgHomClass F ℂ (CStarMatrix ι ι A) B]
    [StarHomClass F (CStarMatrix ι ι A) B] (ψ : F) (hψ : Function.Injective ψ)
    (hconv : ConvexOn ℝ {b : B | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s} (cfc f))
    (hcont : ∀ b : B, IsSelfAdjoint b → spectrum ℝ b ⊆ s → ContinuousOn f (spectrum ℝ b))
    (a x : ι → A) (hx : ∀ i, x i ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s})
    (ha : ∑ i, star (a i) * a i = 1) :
    cfc f (∑ i, star (a i) * x i * a i) ≤ ∑ i, star (a i) * cfc f (x i) * a i := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact le_of_eq (Subsingleton.elim _ _)
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at ha
  have : Nonempty ι := ⟨i₀⟩
  have hconv' := ConvexOn.cfc_of_injective (B := CStarMatrix ι ι A) ψ hψ hconv
  have hcont' := continuousOn_spectrum_of_forall_of_injective (B := CStarMatrix ι ι A) ψ hψ hcont
  have hs := Set.OrdConnected.of_convex_setOf_isSelfAdjoint_spectrum_subset hconv'.1
  obtain ⟨t, ht⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (x i₀) (hx i₀).1
  have ht : t ∈ s := (hx i₀).2 ht
  let φ := CStarMatrix.diagonalStarAlgHom (ι := ι) (A := A)
  let v : CStarMatrix ι ι A := CStarMatrix.ofMatrix (Matrix.of fun i j => if j = i₀ then a i else 0)
  have hconj (h : ι → A) :
      star v * φ h * v = φ (Pi.single i₀ (∑ i, star (a i) * h i * a i)) := by
    ext j j'
    simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, v, φ, CStarMatrix.ofMatrix_apply,
      Matrix.of_apply, CStarMatrix.diagonalStarAlgHom_apply, Pi.single_apply]
    by_cases hj : j = i₀
    · subst hj
      by_cases hj' : j' = j
      · subst hj'
        simp [mul_ite, Finset.sum_ite_eq']
      · simp [hj', Ne.symm hj']
    · simp [hj]
  have hvv : star v * v = φ (Pi.single i₀ 1) := by
    have := hconj 1
    simpa only [map_one, mul_one, Pi.one_apply, ha] using this
  have hys := spectrum_sum_star_mul_mul_subset hs a x hx ha
  have hysa := isSelfAdjoint_sum_star_mul_mul a x fun i => (hx i).1
  let dN : ι → A := Pi.single i₀ (∑ i, star (a i) * x i * a i) + (t : ℂ) • (1 - Pi.single i₀ 1)
  have hdN : ∀ j, dN j ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s} := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      simpa [dN] using And.intro hysa hys
    · have h : dN j = algebraMap ℝ A t := by
        rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)]
        simp [dN, hj]
      rw [h]
      exact algebraMap_mem_setOf_isSelfAdjoint_spectrum_subset ht
  have hmap (d : ι → A) (hd : ∀ i, d i ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s}) :=
    StarAlgHom.cfc_map_pi φ CStarMatrix.continuous_diagonalStarAlgHom f d (fun i => (hd i).1)
      (by
        rw [← StarAlgHom.spectrum_map_pi φ CStarMatrix.diagonalStarAlgHom_injective
          CStarMatrix.continuous_diagonalStarAlgHom d fun i => (hd i).1]
        exact hcont' _ ((show IsSelfAdjoint d from funext fun i => (hd i).1).map φ)
          ((StarAlgHom.spectrum_map_pi_subset φ d).trans (iUnion_subset fun i => (hd i).2)))
  have hX : IsSelfAdjoint (φ x) := (show IsSelfAdjoint x from funext fun i => (hx i).1).map φ
  have hXs : spectrum ℝ (φ x) ⊆ s :=
    (StarAlgHom.spectrum_map_pi_subset φ x).trans (iUnion_subset fun i => (hx i).2)
  have hidem : IsIdempotentElem (star v * v) := by
    rw [hvv]
    change φ _ * φ _ = φ _
    rw [← map_mul]
    congr 1
    ext j
    by_cases hj : j = i₀ <;> simp [hj]
  have hN : star v * φ x * v + (t : ℂ) • (1 - star v * v) = φ dN := by
    rw [hconj, hvv, ← map_one φ, ← map_sub, ← map_smul, ← map_add]
  have key := cfc_mul_le_of_isIdempotentElem hs hcont' hconv' hidem hX hXs ht hN
  rw [hmap dN hdN, hmap x hx, hvv, hconj, ← map_mul] at key
  simpa [φ, dN] using CStarMatrix.apply_self_le_apply_self key i₀

/-- **The unital Jensen inequality implies the sub-unital one** (Hansen–Pedersen 1982): if
`f(Σᵢ aᵢ⋆ xᵢ aᵢ) ≤ Σᵢ aᵢ⋆ f(xᵢ) aᵢ` holds for every family indexed by `Option ι` with
`Σᵢ aᵢ⋆ aᵢ = 1`, then it holds for families indexed by `ι` with `Σᵢ aᵢ⋆ aᵢ ≤ 1`, provided `0 ∈ s`
and `f(0) ≤ 0`: the defect `d = (1 - Σᵢ aᵢ⋆ aᵢ)^{1/2}` joins the family with `x = 0`, and
`d⋆ f(0) d ≤ 0`. -/
theorem cfc_sum_le_of_le_one_of_forall (h0 : (0 : ℝ) ∈ s) (hf0 : f 0 ≤ 0) {ι : Type*} [Fintype ι]
    (hJ : ∀ (a x : Option ι → A), (∀ i, x i ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s}) →
      ∑ i, star (a i) * a i = 1 →
      cfc f (∑ i, star (a i) * x i * a i) ≤ ∑ i, star (a i) * cfc f (x i) * a i)
    (a x : ι → A) (hx : ∀ i, x i ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s})
    (ha : ∑ i, star (a i) * a i ≤ 1) :
    cfc f (∑ i, star (a i) * x i * a i) ≤ ∑ i, star (a i) * cfc f (x i) * a i := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact le_of_eq (Subsingleton.elim _ _)
  set d := CFC.sqrt (1 - ∑ i, star (a i) * a i) with hd
  have hd0 : 0 ≤ 1 - ∑ i, star (a i) * a i := sub_nonneg.2 ha
  have hdd : star d * d = 1 - ∑ i, star (a i) * a i := by
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hd0]
  have h0mem : (0 : A) ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s} :=
    zero_mem_setOf_isSelfAdjoint_spectrum_subset h0
  have h := hJ (Option.elim · d a) (Option.elim · 0 x)
    (fun i => match i with
      | none => h0mem
      | some i => hx i)
    (by rw [Fintype.sum_option]; simp [hdd])
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, mul_zero, zero_mul,
    zero_add, cfc_apply_zero] at h
  refine h.trans (add_le_of_nonpos_left ?_)
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, hdd]
  exact smul_nonpos_of_nonpos_of_nonneg hf0 hd0

/-- **Jensen's operator inequality** (Hansen–Pedersen 2003, Theorem 2.1, the implication from
operator convexity): for `f` operator convex on `s`, a finite family `aᵢ ∈ A` with
`Σᵢ aᵢ⋆ aᵢ = 1` and self-adjoint `xᵢ ∈ A` with spectrum in `s`,
`f(Σᵢ aᵢ⋆ xᵢ aᵢ) ≤ Σᵢ aᵢ⋆ f(xᵢ) aᵢ`. This is `cfc_sum_le_of_convexOn_cstarMatrix` with the
convexity of `cfc f` over `CStarMatrix (Fin n) (Fin n) A`, `n = card ι`, and the continuity of `f`
on `s` read off `IsOperatorConvexOn` itself; the operator convexity is used in the universe of `A`,
while the index type `ι` is arbitrary. -/
theorem IsOperatorConvexOn.cfc_sum_le {ι : Type*} [Fintype ι]
    (hf : IsOperatorConvexOn.{u} s f) (a x : ι → A)
    (hx : ∀ i, x i ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s})
    (ha : ∑ i, star (a i) * a i = 1) :
    cfc f (∑ i, star (a i) * x i * a i) ≤ ∑ i, star (a i) * cfc f (x i) * a i := by
  classical
  exact cfc_sum_le_of_convexOn_cstarMatrix
    (B := CStarMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A)
    (CStarMatrix.reindexₐ ℂ A (Fintype.equivFin ι)) (EquivLike.injective _)
    (hf.convexOn _) (fun _ _ hbs => hf.continuousOn.mono hbs) a x hx ha

/-- **Jensen's operator inequality, sub-unital form** (Hansen–Pedersen 1982, Theorem 2.1, the
implication from operator convexity): for `f` operator convex on `s ∋ 0` with `f(0) ≤ 0`, a
finite family `aᵢ ∈ A` with `Σᵢ aᵢ⋆ aᵢ ≤ 1` and self-adjoint `xᵢ ∈ A` with spectrum in `s`,
`f(Σᵢ aᵢ⋆ xᵢ aᵢ) ≤ Σᵢ aᵢ⋆ f(xᵢ) aᵢ`. -/
theorem IsOperatorConvexOn.cfc_sum_le_of_le_one {ι : Type*} [Fintype ι]
    (hf : IsOperatorConvexOn.{u} s f) (h0 : (0 : ℝ) ∈ s) (hf0 : f 0 ≤ 0) (a x : ι → A)
    (hx : ∀ i, x i ∈ {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s})
    (ha : ∑ i, star (a i) * a i ≤ 1) :
    cfc f (∑ i, star (a i) * x i * a i) ≤ ∑ i, star (a i) * cfc f (x i) * a i :=
  cfc_sum_le_of_le_one_of_forall h0 hf0 (fun a x hx ha => hf.cfc_sum_le a x hx ha) a x hx ha

end JensenTheorems

/-! ### Examples -/

/-- The negated power function `-tᵖ` (`0 ≤ p ≤ 1`) is operator convex on `[0, ∞)`: this is the
operator concavity of `tᵖ` (Mathlib's `CFC.concaveOn_rpow`). -/
lemma isOperatorConvexOn_neg_rpow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsOperatorConvexOn (Ici 0) (fun t => -(t ^ p)) := by
  refine ⟨(Real.continuous_rpow_const hp0).neg.continuousOn, fun A _ _ _ => ?_⟩
  rw [setOf_isSelfAdjoint_spectrum_subset_Ici]
  exact (CFC.concaveOn_rpow ⟨hp0, hp1⟩).neg.congr fun a ha => by
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := a) ha, Pi.neg_apply]

/-- The negated logarithm `-log t` is operator convex on `(0, ∞)`: this is the operator concavity
of `log` (Mathlib's `CFC.concaveOn_log`). -/
lemma isOperatorConvexOn_neg_log : IsOperatorConvexOn (Ioi 0) (fun t => -Real.log t) := by
  refine ⟨(Real.continuousOn_log.mono fun t ht => ht.ne').neg, fun A _ _ _ => ?_⟩
  rw [setOf_isSelfAdjoint_spectrum_subset_Ioi]
  exact CFC.concaveOn_log.neg.congr fun a _ => by rw [cfc_neg, Pi.neg_apply]; rfl

/-- The inverse `t⁻¹` is operator convex on `(0, ∞)` (Mathlib's
`CStarAlgebra.convexOn_ringInverse`). -/
lemma isOperatorConvexOn_inv : IsOperatorConvexOn (Ioi 0) (fun t => t⁻¹) := by
  refine ⟨continuousOn_inv₀.mono fun t ht => ht.ne', fun A _ _ _ => ?_⟩
  rw [setOf_isSelfAdjoint_spectrum_subset_Ioi]
  exact CStarAlgebra.convexOn_ringInverse.congr fun a ha =>
    (cfc_ringInverse_id (R := ℝ) (a := a) ha.isUnit).symm

/-- The negated power function `-tᵖ` (`0 ≤ p ≤ 1`) is matrix convex on `[0, ∞)`
(`isOperatorConvexOn_neg_rpow`). -/
lemma isMatrixConvexOn_neg_rpow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsMatrixConvexOn (Ici 0) (fun t => -(t ^ p)) :=
  (isOperatorConvexOn_neg_rpow.{0} hp0 hp1).isMatrixConvexOn

/-- The negated logarithm `-log t` is matrix convex on `(0, ∞)` (`isOperatorConvexOn_neg_log`). -/
lemma isMatrixConvexOn_neg_log : IsMatrixConvexOn (Ioi 0) (fun t => -Real.log t) :=
  isOperatorConvexOn_neg_log.{0}.isMatrixConvexOn

/-- The inverse `t⁻¹` is matrix convex on `(0, ∞)` (`isOperatorConvexOn_inv`). -/
lemma isMatrixConvexOn_inv : IsMatrixConvexOn (Ioi 0) (fun t => t⁻¹) :=
  isOperatorConvexOn_inv.{0}.isMatrixConvexOn

/-! ### A matrix convex function that is not operator convex

The indicator `f = 1_{\{0\}}` of `{0}` on `[0, ∞)` sends `A ⪰ 0` to the projection `f(A)` onto
`ker A`. For `A, B ⪰ 0` and `a, b > 0`, `ker(a A + b B) = ker A ∩ ker B`, so the projection onto
`ker(a A + b B)` lies below those onto `ker A` and `ker B`, and `f` is matrix convex. It is not
continuous at `0`, so it is not operator convex: the obstruction is the continuity in the
definition of `IsOperatorConvexOn`, not the kernel argument.
-/

section IndicatorZero

variable {A : Type*} [CStarAlgebra A]

/-- For `X` with finite spectrum, `1_{\{0\}}(X)` is a projection. -/
private lemma isStarProjection_cfc_indicator_zero {X : A} (hX : (spectrum ℝ X).Finite) :
    IsStarProjection (cfc (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) X) := by
  refine ⟨?_, cfc_predicate _ _⟩
  rw [IsIdempotentElem, ← cfc_mul (hf := hX.continuousOn _) (hg := hX.continuousOn _)]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

/-- `X · 1_{\{0\}}(X) = 0` for self-adjoint `X` with finite spectrum: the range of `1_{\{0\}}(X)`
lies in `ker X`. -/
private lemma mul_cfc_indicator_zero {X : A} (hX : IsSelfAdjoint X) (hfin : (spectrum ℝ X).Finite) :
    X * cfc (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) X = 0 := by
  have h := cfc_mul (fun x : ℝ => x) (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) X
    (hfin.continuousOn _) (hfin.continuousOn _)
  rw [cfc_id' ℝ X] at h
  rw [← h, show (fun x : ℝ => x * ({0} : Set ℝ).indicator (1 : ℝ → ℝ) x) = (0 : ℝ → ℝ) from
    funext fun x => by by_cases hx : x = 0 <;> simp [hx]]
  simp

/-- `1 - 1_{\{0\}}(X) = X⁻¹ X` with `0⁻¹ = 0`, for self-adjoint `X` with finite spectrum: the
complementary projection factors through `X`. -/
private lemma one_sub_cfc_indicator_zero {X : A} (hX : IsSelfAdjoint X)
    (hfin : (spectrum ℝ X).Finite) :
    1 - cfc (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) X = cfc (fun x : ℝ => x⁻¹) X * X := by
  have h := cfc_mul (fun x : ℝ => x⁻¹) (fun x : ℝ => x) X (hfin.continuousOn _)
    (hfin.continuousOn _)
  rw [cfc_id' ℝ X] at h
  rw [← h, ← cfc_one ℝ X, ← cfc_sub (hf := hfin.continuousOn _) (hg := hfin.continuousOn _)]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

variable [PartialOrder A] [StarOrderedRing A]

/-- For self-adjoint `X` with finite spectrum, a projection `P` with `X P = 0`, i.e. with range in
`ker X`, lies below the projection `1_{\{0\}}(X)` onto `ker X`. -/
private lemma le_cfc_indicator_zero {X P : A} (hX : IsSelfAdjoint X)
    (hfin : (spectrum ℝ X).Finite) (hP : IsStarProjection P) (hXP : X * P = 0) :
    P ≤ cfc (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) X := by
  refine hP.le_of_mul_eq_right (isStarProjection_cfc_indicator_zero hfin) ?_
  have h : (1 - cfc (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) X) * P = 0 := by
    rw [one_sub_cfc_indicator_zero hX hfin, mul_assoc, hXP, mul_zero]
  rwa [sub_mul, one_mul, sub_eq_zero, eq_comm] at h

/-- For `a ≥ 0`, `q⋆ a q = 0` forces `a q = 0`. -/
private lemma mul_eq_zero_of_star_mul_mul_eq_zero {a q : A} (ha : 0 ≤ a)
    (h : star q * a * q = 0) : a * q = 0 := by
  obtain ⟨d, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  have hdq : d * q = 0 := by
    rw [← CStarRing.star_mul_self_eq_zero_iff, star_mul, ← h]
    noncomm_ring
  rw [mul_assoc, hdq, mul_zero]

end IndicatorZero

/-- The indicator `1_{\{0\}}` of `{0}` is matrix convex on `[0, ∞)`: `1_{\{0\}}(A)` is the
projection onto `ker A`, and `ker(a A + b B) = ker A ∩ ker B` for `A, B ⪰ 0` and `a, b > 0`. It
is not continuous, hence not operator convex (`not_isOperatorConvexOn_indicator_zero`): the two
notions differ on discontinuous functions, through the continuity that operator convexity
requires. -/
theorem isMatrixConvexOn_indicator_zero :
    IsMatrixConvexOn (Ici 0) (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) := fun n => by
  open scoped MatrixOrder Matrix.Norms.L2Operator in
  refine ⟨ordConnected_Ici.convex_setOf_isSelfAdjoint_spectrum_subset, ?_⟩
  intro A hA B hB a b ha hb hab
  rw [setOf_isSelfAdjoint_spectrum_subset_Ici] at hA hB
  change 0 ≤ A at hA
  change 0 ≤ B at hB
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    simp [hab]
  rcases hb.eq_or_lt with rfl | hb'
  · rw [add_zero] at hab
    simp [hab]
  set Q := cfc (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) (a • A + b • B) with hQ
  have hC : 0 ≤ a • A + b • B := add_nonneg (smul_nonneg ha hA) (smul_nonneg hb hB)
  have hQP : IsStarProjection Q :=
    isStarProjection_cfc_indicator_zero (a • A + b • B).finite_real_spectrum
  -- `Q⋆ (a A + b B) Q = 0` splits into two nonnegative terms, so `Q⋆ A Q = Q⋆ B Q = 0`.
  have hsum : a • (star Q * A * Q) + b • (star Q * B * Q) = 0 := by
    have h : star Q * (a • A + b • B) * Q = 0 := by
      rw [mul_assoc, mul_cfc_indicator_zero hC.isSelfAdjoint (a • A + b • B).finite_real_spectrum,
        mul_zero]
    simpa only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc] using h
  have h0 := (add_eq_zero_iff_of_nonneg (smul_nonneg ha (star_left_conjugate_nonneg hA Q))
    (smul_nonneg hb (star_left_conjugate_nonneg hB Q))).1 hsum
  have hQA := le_cfc_indicator_zero hA.isSelfAdjoint A.finite_real_spectrum hQP
    (mul_eq_zero_of_star_mul_mul_eq_zero hA ((smul_eq_zero.1 h0.1).resolve_left ha'.ne'))
  have hQB := le_cfc_indicator_zero hB.isSelfAdjoint B.finite_real_spectrum hQP
    (mul_eq_zero_of_star_mul_mul_eq_zero hB ((smul_eq_zero.1 h0.2).resolve_left hb'.ne'))
  calc Q = a • Q + b • Q := by rw [← add_smul, hab, one_smul]
    _ ≤ _ := add_le_add (smul_le_smul_of_nonneg_left hQA ha) (smul_le_smul_of_nonneg_left hQB hb)

/-- The indicator `1_{\{0\}}` of `{0}` is not operator convex on `[0, ∞)`, in any universe: it is
not continuous at `0`, and the proof uses only the field `IsOperatorConvexOn.continuousOn`. It is
matrix convex (`isMatrixConvexOn_indicator_zero`). -/
theorem not_isOperatorConvexOn_indicator_zero :
    ¬ IsOperatorConvexOn (Ici 0) (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) := fun h => by
  have hc : Filter.Tendsto (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) (nhdsWithin 0 (Ioi 0))
      (nhds (({0} : Set ℝ).indicator (1 : ℝ → ℝ) 0)) :=
    (h.continuousOn 0 self_mem_Ici).mono Ioi_subset_Ici_self
  have h0 : Filter.Tendsto (({0} : Set ℝ).indicator (1 : ℝ → ℝ)) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => by
      simp [(mem_Ioi.1 hx).ne'])
  simpa using tendsto_nhds_unique hc h0

/-! ### Matrix convexity on bounded operators -/

section MatrixConvexBoundedOperators

open Polynomial
open scoped InnerProductSpace InnerProduct

/-! #### Compression to a finite-dimensional subspace -/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compression `ι† X ι` of an operator `X` on `H` to a closed subspace `F`, where
`ι : F → H` is the inclusion. -/
private noncomputable def compress (F : Submodule ℂ H) [CompleteSpace F] (X : H →L[ℂ] H) :
    F →L[ℂ] F :=
  F.subtypeL† ∘L X ∘L F.subtypeL

variable {F : Submodule ℂ H} [CompleteSpace F]

private lemma compress_apply (X : H →L[ℂ] H) (v : F) :
    compress F X v = F.orthogonalProjectionOnto (X v) := by
  simp [compress, Submodule.adjoint_subtypeL]

/-- The compression of `X` acts as `X` on a vector `v ∈ F` with `X v ∈ F`. -/
private lemma coe_compress_apply_of_mem (X : H →L[ℂ] H) (v : F) (hv : X v ∈ F) :
    (compress F X v : H) = X v := by
  rw [compress_apply, show X v = ((⟨X v, hv⟩ : F) : H) from rfl,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

private lemma compress_one : compress F 1 = 1 := by
  ext v
  simp [compress_apply]

private lemma compress_add_smul (t u : ℝ) (X Y : H →L[ℂ] H) :
    compress F (t • X + u • Y) = t • compress F X + u • compress F Y := by
  ext v
  simp [compress_apply, map_add, map_smul_of_tower]

private lemma compress_algebraMap (r : ℝ) :
    compress F (algebraMap ℝ (H →L[ℂ] H) r) = algebraMap ℝ (F →L[ℂ] F) r := by
  ext v
  simp [compress_apply, Algebra.algebraMap_eq_smul_one, map_smul_of_tower]

private lemma compress_sub (X Y : H →L[ℂ] H) :
    compress F (X - Y) = compress F X - compress F Y := by
  simp [compress, sub_comp, comp_sub]

private lemma isSelfAdjoint_compress {X : H →L[ℂ] H} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (compress F X) := by
  rw [IsSelfAdjoint, star_eq_adjoint, compress, adjoint_comp, adjoint_comp, adjoint_adjoint,
    ← star_eq_adjoint X, hX.star_eq, comp_assoc]

private lemma compress_mono {X Y : H →L[ℂ] H} (h : X ≤ Y) : compress F X ≤ compress F Y := by
  rw [← sub_nonneg, ← compress_sub, nonneg_iff_isPositive]
  exact (nonneg_iff_isPositive.1 (sub_nonneg.2 h)).adjoint_conj F.subtypeL

/-- Scalar bounds `lo ≤ X ≤ hi` pass to the compression. -/
private lemma algebraMap_le_compress {X : H →L[ℂ] H} {r : ℝ}
    (h : algebraMap ℝ (H →L[ℂ] H) r ≤ X) : algebraMap ℝ (F →L[ℂ] F) r ≤ compress F X :=
  compress_algebraMap (F := F) r ▸ compress_mono h

private lemma compress_le_algebraMap {X : H →L[ℂ] H} {r : ℝ}
    (h : X ≤ algebraMap ℝ (H →L[ℂ] H) r) : compress F X ≤ algebraMap ℝ (F →L[ℂ] F) r :=
  compress_algebraMap (F := F) r ▸ compress_mono h

/-- If the powers `Z^k ξ`, `k ≤ d`, lie in `F`, then the powers of the compression of `Z` agree
with them on `ξ`. -/
private lemma coe_compress_pow_apply {Z : H →L[ℂ] H} {ξ : F} {d : ℕ}
    (hZ : ∀ k ≤ d, (Z ^ k) ξ ∈ F) : ∀ k ≤ d, (((compress F Z) ^ k) ξ : H) = (Z ^ k) ξ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    have h := ih (Nat.le_of_succ_le hk)
    have hk' : Z ((Z ^ k) ξ) ∈ F := by
      simpa [pow_succ', mul_apply_eq_comp] using hZ (k + 1) hk
    rw [pow_succ', mul_apply_eq_comp, coe_compress_apply_of_mem _ _ (h ▸ hk'), h, pow_succ',
      mul_apply_eq_comp]

/-- A real polynomial of degree at most `d` in the compression of `Z` agrees with the same
polynomial in `Z` on `ξ`, if the powers `Z^k ξ`, `k ≤ d`, lie in `F`. -/
private lemma coe_aeval_compress_apply {Z : H →L[ℂ] H} {ξ : F} {p : ℝ[X]}
    (hZ : ∀ k ≤ p.natDegree, (Z ^ k) ξ ∈ F) :
    (aeval (compress F Z) p ξ : H) = aeval Z p ξ := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [sum_apply, smul_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coe_compress_pow_apply hZ k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

end ContinuousLinearMap

/-! #### Krylov subspaces -/

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The subspace spanned by the words of length at most `k` in `X` and `Y` applied to `ξ`. -/
private noncomputable def krylov (X Y : H →L[ℂ] H) (ξ : H) : ℕ → Submodule ℂ H
  | 0 => ℂ ∙ ξ
  | k + 1 => krylov X Y ξ k ⊔ (krylov X Y ξ k).map (X : H →ₗ[ℂ] H) ⊔
      (krylov X Y ξ k).map (Y : H →ₗ[ℂ] H)

variable {X Y : H →L[ℂ] H} {ξ : H}

private lemma finiteDimensional_krylov (k : ℕ) : FiniteDimensional ℂ (krylov X Y ξ k) := by
  induction k with
  | zero => exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton ξ)
  | succ k ih =>
    have := Module.Finite.map (krylov X Y ξ k) (X : H →ₗ[ℂ] H)
    have := Module.Finite.map (krylov X Y ξ k) (Y : H →ₗ[ℂ] H)
    simp only [krylov]
    exact Submodule.finiteDimensional_sup _ _ (h₁ := Submodule.finiteDimensional_sup _ _)

private lemma krylov_mono : Monotone (krylov X Y ξ) :=
  monotone_nat_of_le_succ fun _ => le_sup_left.trans le_sup_left

private lemma mem_krylov_zero : ξ ∈ krylov X Y ξ 0 :=
  Submodule.mem_span_singleton_self ξ

/-- `t X + u Y` maps the `k`-th Krylov subspace into the next one. -/
private lemma add_smul_apply_mem_krylov (t u : ℝ) {k : ℕ} {v : H} (hv : v ∈ krylov X Y ξ k) :
    (t • X + u • Y) v ∈ krylov X Y ξ (k + 1) := by
  have hX : X v ∈ krylov X Y ξ (k + 1) :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem hv))
  have hY : Y v ∈ krylov X Y ξ (k + 1) := Submodule.mem_sup_right (Submodule.mem_map_of_mem hv)
  simpa using Submodule.add_mem _ (Submodule.smul_of_tower_mem _ t hX)
    (Submodule.smul_of_tower_mem _ u hY)

/-- If `Z` maps each Krylov subspace into the next one, the powers `Z^k ξ`, `k ≤ d`, lie in the
`d`-th one. -/
private lemma pow_apply_mem_krylov {Z : H →L[ℂ] H}
    (hZ : ∀ k v, v ∈ krylov X Y ξ k → Z v ∈ krylov X Y ξ (k + 1)) {d : ℕ} :
    ∀ k ≤ d, (Z ^ k) ξ ∈ krylov X Y ξ d := by
  suffices h : ∀ k, (Z ^ k) ξ ∈ krylov X Y ξ k from fun k hk => krylov_mono hk (h k)
  intro k
  induction k with
  | zero => simpa using mem_krylov_zero
  | succ k ih => simpa [pow_succ', mul_apply_eq_comp] using hZ k _ ih

end ContinuousLinearMap

/-! #### Approximation by polynomials -/

section Approximation

open ContinuousLinearMap

/-- A self-adjoint element with scalar bounds `lo ≤ Z ≤ hi` has spectrum in `[lo, hi]`. -/
private lemma spectrum_subset_Icc {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {Z : A} (hZ : IsSelfAdjoint Z) {lo hi : ℝ}
    (h₁ : algebraMap ℝ A lo ≤ Z) (h₂ : Z ≤ algebraMap ℝ A hi) : spectrum ℝ Z ⊆ Icc lo hi :=
  fun x hx => ⟨(algebraMap_le_iff_le_spectrum hZ).1 h₁ x hx,
    (le_algebraMap_iff_spectrum_le hZ).1 h₂ x hx⟩

/-- If `|p - f| < ε` on an interval containing the spectrum of `Z`, then `‖f(Z) - p(Z)‖ ≤ ε`. -/
private lemma norm_cfc_sub_aeval_le {A : Type*} [CStarAlgebra A] {f : ℝ → ℝ} {lo hi ε : ℝ}
    (hε : 0 ≤ ε) (hf : ContinuousOn f (Icc lo hi)) {p : ℝ[X]}
    (hp : ∀ x ∈ Icc lo hi, |p.eval x - f x| < ε) {Z : A} (hZ : IsSelfAdjoint Z)
    (hZs : spectrum ℝ Z ⊆ Icc lo hi) : ‖cfc f Z - aeval Z p‖ ≤ ε := by
  rw [← cfc_polynomial p Z, ← cfc_sub f (fun x => p.eval x) Z (hf.mono hZs)]
  refine norm_cfc_le hε fun x hx => ?_
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact (hp x (hZs hx)).le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma abs_re_inner_sub_le (T S : E →L[ℂ] E) (ξ : E) {δ : ℝ} (h : ‖T - S‖ ≤ δ) :
    |RCLike.re ⟪T ξ, ξ⟫_ℂ - RCLike.re ⟪S ξ, ξ⟫_ℂ| ≤ δ * ‖ξ‖ ^ 2 := by
  rw [← map_sub, ← inner_sub_left, ← sub_apply]
  calc _ ≤ ‖⟪(T - S) ξ, ξ⟫_ℂ‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖(T - S) ξ‖ * ‖ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖T - S‖ * ‖ξ‖ * ‖ξ‖ := by gcongr; exact le_opNorm _ _
    _ ≤ δ * ‖ξ‖ ^ 2 := by rw [mul_assoc, ← sq]; gcongr

private lemma re_inner_add_smul_sub_apply (t u : ℝ) (A B C : E →L[ℂ] E) (ξ : E) :
    RCLike.re ⟪(t • A + u • B - C) ξ, ξ⟫_ℂ =
      t * RCLike.re ⟪A ξ, ξ⟫_ℂ + u * RCLike.re ⟪B ξ, ξ⟫_ℂ - RCLike.re ⟪C ξ, ξ⟫_ℂ := by
  rw [sub_apply, add_apply, smul_apply, smul_apply, inner_sub_left, inner_add_left,
    RCLike.real_smul_eq_coe_smul (K := ℂ) t, RCLike.real_smul_eq_coe_smul (K := ℂ) u,
    inner_smul_real_left, inner_smul_real_left, map_sub, map_add, RCLike.smul_re, RCLike.smul_re]

end Approximation

/-! #### The converse on a Hilbert space -/

section BoundedOperators

open ContinuousLinearMap

variable {s : Set ℝ} {f : ℝ → ℝ}

/-- A matrix convex function is convex on the operators of a finite-dimensional Hilbert space,
through an orthonormal basis (`Matrix.toEuclideanCLM`). -/
private lemma IsMatrixConvexOn.convexOn_finiteDimensional (hf : IsMatrixConvexOn s f)
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ K] :
    ConvexOn ℝ {T : K →L[ℂ] K | IsSelfAdjoint T ∧ spectrum ℝ T ⊆ s} (cfc f) := by
  open scoped Matrix.Norms.L2Operator MatrixOrder in
  exact ConvexOn.cfc_of_injective
    ((stdOrthonormalBasis ℂ K).repr.conjStarAlgEquiv.trans Matrix.toEuclideanCLM.symm)
    (EquivLike.injective _) (hf _)

/-- In a vector state, `f(Z)` and `p(Z)` are `δ`-close if `|p - f| < δ` on `[lo, hi]` and
`lo ≤ Z ≤ hi`. -/
private lemma abs_re_inner_cfc_sub_aeval_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {lo hi δ : ℝ} (hδ : 0 ≤ δ)
    (hcI : ContinuousOn f (Icc lo hi)) {p : ℝ[X]} (hp : ∀ x ∈ Icc lo hi, |p.eval x - f x| < δ)
    {Z : E →L[ℂ] E} (hZ : IsSelfAdjoint Z) (hZb : algebraMap ℝ _ lo ≤ Z ∧ Z ≤ algebraMap ℝ _ hi)
    (η : E) : |RCLike.re ⟪cfc f Z η, η⟫_ℂ - RCLike.re ⟪aeval Z p η, η⟫_ℂ| ≤ δ * ‖η‖ ^ 2 :=
  abs_re_inner_sub_le _ _ η (norm_cfc_sub_aeval_le hδ hcI hp hZ (spectrum_subset_Icc hZ hZb.1 hZb.2))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The core estimate: for `f` continuous and matrix convex on `s`, self-adjoint `X, Y` with
spectra in `[lo, hi] ⊆ s`, a vector `ξ` and `ε > 0`, the vector state of `ξ` satisfies
`⟪f(tX + uY) ξ, ξ⟫ ≤ t ⟪f(X) ξ, ξ⟫ + u ⟪f(Y) ξ, ξ⟫ + ε`. A polynomial `p` with `|p - f| < δ` on
`[lo, hi]` has `p(Z) ξ = p(Z_F) ξ` for the compressions `Z_F` of `Z = X, Y, tX + uY` to the Krylov
subspace `F` of the words of length at most `deg p` in `X, Y` applied to `ξ`, and matrix convexity
applies on `F`. -/
private lemma re_inner_cfc_add_smul_le (hc : ContinuousOn f s) (hf : IsMatrixConvexOn s f)
    {lo hi : ℝ} (hlo : lo ∈ s) (hhi : hi ∈ s) {X Y : H →L[ℂ] H} (hX : IsSelfAdjoint X)
    (hY : IsSelfAdjoint Y) (hXb : algebraMap ℝ _ lo ≤ X ∧ X ≤ algebraMap ℝ _ hi)
    (hYb : algebraMap ℝ _ lo ≤ Y ∧ Y ≤ algebraMap ℝ _ hi) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (htu : t + u = 1) (ξ : H) {ε : ℝ} (hε : 0 < ε) :
    RCLike.re ⟪cfc f (t • X + u • Y) ξ, ξ⟫_ℂ ≤
      t * RCLike.re ⟪cfc f X ξ, ξ⟫_ℂ + u * RCLike.re ⟪cfc f Y ξ, ξ⟫_ℂ + ε := by
  have hIcc : Icc lo hi ⊆ s := hf.ordConnected.out hlo hhi
  have hcI : ContinuousOn f (Icc lo hi) := hc.mono hIcc
  set δ := ε / (4 * (‖ξ‖ ^ 2 + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδn : 4 * (δ * ‖ξ‖ ^ 2) < ε := by
    rw [hδ_def]
    have h1 : 0 < ‖ξ‖ ^ 2 + 1 := by positivity
    calc 4 * (ε / (4 * (‖ξ‖ ^ 2 + 1)) * ‖ξ‖ ^ 2) = ε * (‖ξ‖ ^ 2 / (‖ξ‖ ^ 2 + 1)) := by
          field_simp
      _ < ε * 1 := by
          gcongr
          rw [div_lt_one h1]
          linarith
      _ = ε := mul_one ε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn lo hi f hcI δ hδ
  let F := krylov X Y ξ p.natDegree
  have : FiniteDimensional ℂ F := finiteDimensional_krylov _
  let ξ' : F := ⟨ξ, krylov_mono (Nat.zero_le _) mem_krylov_zero⟩
  have hξ' : ‖ξ'‖ = ‖ξ‖ := rfl
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  have hsa {P Q : H →L[ℂ] H} (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q) :
      IsSelfAdjoint (t • P + u • Q) :=
    ((IsSelfAdjoint.all t).smul hP).add ((IsSelfAdjoint.all u).smul hQ)
  have hcompb {Z : H →L[ℂ] H} (hZb : algebraMap ℝ _ lo ≤ Z ∧ Z ≤ algebraMap ℝ _ hi) :
      algebraMap ℝ (F →L[ℂ] F) lo ≤ compress F Z ∧ compress F Z ≤ algebraMap ℝ _ hi :=
    ⟨algebraMap_le_compress hZb.1, compress_le_algebraMap hZb.2⟩
  -- `p(Z) ξ = p(Z_F) ξ'` for `Z = X, Y, tX + uY`
  have hK {Z : H →L[ℂ] H}
      (hZ : ∀ k v, v ∈ krylov X Y ξ k → Z v ∈ krylov X Y ξ (k + 1)) :
      RCLike.re ⟪aeval (compress F Z) p ξ', ξ'⟫_ℂ = RCLike.re ⟪aeval Z p ξ, ξ⟫_ℂ := by
    rw [Submodule.coe_inner, coe_aeval_compress_apply (pow_apply_mem_krylov hZ)]
  have hKX := hK (Z := X) fun k v hv => by simpa using add_smul_apply_mem_krylov 1 0 hv
  have hKY := hK (Z := Y) fun k v hv => by simpa using add_smul_apply_mem_krylov 0 1 hv
  have hKW := hK (Z := t • X + u • Y) fun k v hv => add_smul_apply_mem_krylov t u hv
  have hWb := convex_Icc (𝕜 := ℝ) (algebraMap ℝ (H →L[ℂ] H) lo) (algebraMap ℝ _ hi) hXb hYb ht hu htu
  have hW := hsa hX hY
  have hFX := hcompb hXb
  have hFY := hcompb hYb
  have hFW := hcompb hWb
  have hcX := isSelfAdjoint_compress (F := F) hX
  have hcY := isSelfAdjoint_compress (F := F) hY
  have hcW := isSelfAdjoint_compress (F := F) hW
  -- matrix convexity on `F`
  have hconvF := (hf.convexOn_finiteDimensional F).2
    ⟨hcX, (spectrum_subset_Icc hcX hFX.1 hFX.2).trans hIcc⟩
    ⟨hcY, (spectrum_subset_Icc hcY hFY.1 hFY.2).trans hIcc⟩ ht hu htu
  have hconv := (nonneg_iff_isPositive.1 (sub_nonneg.2 hconvF)).re_inner_nonneg_left ξ'
  rw [re_inner_add_smul_sub_apply] at hconv
  have e1 := abs_le.1 (abs_re_inner_cfc_sub_aeval_le hδ.le hcI hp hW hWb ξ)
  have e2 := abs_le.1 (abs_re_inner_cfc_sub_aeval_le hδ.le hcI hp hcW (compress_add_smul (F := F) t u X Y ▸ hFW) ξ')
  have e3 := abs_le.1 (abs_re_inner_cfc_sub_aeval_le hδ.le hcI hp hcX hFX ξ')
  have e4 := abs_le.1 (abs_re_inner_cfc_sub_aeval_le hδ.le hcI hp hcY hFY ξ')
  have e5 := abs_le.1 (abs_re_inner_cfc_sub_aeval_le hδ.le hcI hp hX hXb ξ)
  have e6 := abs_le.1 (abs_re_inner_cfc_sub_aeval_le hδ.le hcI hp hY hYb ξ)
  rw [hξ', compress_add_smul] at e2
  rw [hξ'] at e3 e4
  rw [compress_add_smul] at hKW
  rw [hKW] at e2
  rw [hKX] at e3
  rw [hKY] at e4
  nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2]

variable (H) in
/-- **Matrix convexity implies convexity on bounded operators**: for `f` continuous and matrix
convex on `s`, `X ↦ f(X)` is convex on the self-adjoint operators on a complex Hilbert space `H`
with spectrum in `s`, in every universe. Positivity of `t f(X) + u f(Y) - f(tX + uY)` is tested
in the vector states, on the compressions to finite-dimensional Krylov subspaces. This is the
Hilbert-space case of convexity in every C⋆-algebra, and the step that case is reduced to through
a faithful representation (Gelfand–Naimark). -/
theorem IsMatrixConvexOn.convexOn_continuousLinearMap (hc : ContinuousOn f s)
    (hf : IsMatrixConvexOn s f) :
    ConvexOn ℝ {X : H →L[ℂ] H | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s} (cfc f) := by
  refine ⟨hf.ordConnected.convex_setOf_isSelfAdjoint_spectrum_subset,
    fun X hX Y hY t u ht hu htu => ?_⟩
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with _ | _
  · exact le_of_eq (Subsingleton.elim _ _)
  obtain ⟨lo, hlo, hi, hhi, hbd⟩ :=
    exists_algebraMap_le_and_le_algebraMap (x := ![X, Y]) (Fin.forall_fin_two.2 ⟨hX, hY⟩)
  rw [← sub_nonneg, nonneg_iff_isPositive, isPositive_def']
  refine ⟨(((IsSelfAdjoint.all t).smul (cfc_predicate f X)).add
    ((IsSelfAdjoint.all u).smul (cfc_predicate f Y))).sub (cfc_predicate f _), fun ξ => ?_⟩
  rw [reApplyInnerSelf_apply, re_inner_add_smul_sub_apply, sub_nonneg]
  exact le_of_forall_pos_le_add fun ε hε =>
    re_inner_cfc_add_smul_le hc hf hlo hhi hX.1 hY.1 (hbd 0) (hbd 1) ht hu htu ξ hε

end BoundedOperators

end MatrixConvexBoundedOperators
