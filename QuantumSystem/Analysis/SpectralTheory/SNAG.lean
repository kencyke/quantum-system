/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Topology.Algebra.Module.TopDualPairing
public import QuantumSystem.Analysis.SpectralTheory.UnitaryRepresentation
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearMap
public import QuantumSystem.ForMathlib.MeasureTheory.Measure.CharacteristicFunction.Bochner

/-!
# The SNAG theorem

Let `V` be a finite-dimensional real vector space and `U` a **strongly continuous** unitary
representation of `V` on a complex Hilbert space `H`: a `UnitaryAddRepresentation V H`,
continuous into the unitary group with the strong operator topology (defined in
`QuantumSystem.Analysis.SpectralTheory.UnitaryRepresentation`), whose unitary at `v : V` is
`U v`. Let `L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ` be a
continuous perfect pairing (`LinearMap.IsContPerfPair`), which realises `W` as the dual of `V`, and
equip `W` with its Borel σ-algebra. The **SNAG theorem** (Stone–Naimark–Ambrose–Godement) states
that there is a unique projection-valued measure `E_U` on `W` with
`U v = ∫ exp (i L(p, v)) dE_U(p)`, i.e. `U` is the Fourier transform
`E_U.fourierOfIsContPerfPair L` of `E_U`
(`MeasureTheory.ProjectionValuedMeasure.fourierOfIsContPerfPair`). Conversely the Fourier transform of
every projection-valued measure on `W` is a strongly continuous unitary representation, with that
measure as its projection-valued measure, so `E ↦ E.fourierOfIsContPerfPair L` is a bijection from
the projection-valued measures on `W` onto the strongly continuous unitary representations of `V`.

The classical statement on the dual space is the case `W = StrongDual ℝ V`,
`L = topDualPairing ℝ V` (`UnitaryAddRepresentation.existsUnique_fourier_eq_strongDual`). For
`V = W = ℝ` and `L = LinearMap.mul ℝ ℝ` it is the spectral form of Stone's theorem; this is the
pairing along which `IsSelfAdjoint.unitaryGroup` is the Fourier transform of the spectral measure.
The measurability and the continuity of the pairing, and the first countability of `V`, required by
`ProjectionValuedMeasure.fourierRepresentation`, are
`LinearMap.measurable_flip_apply_of_isContPerfPair`,
`LinearMap.continuous_of_isContPerfPair` and `LinearMap.firstCountableTopology_of_isContPerfPair`;
`ProjectionValuedMeasure.fourierOfIsContPerfPair` supplies them.

## Construction

1. For `y : H` the matrix coefficient `φ_y(v) = ⟪y, U v y⟫` is continuous and positive definite:
   `(φ_y(xᵢ - xⱼ))ᵢⱼ` is the Gram matrix of the vectors `U (-xᵢ) y`. Bochner's theorem
   (`IsPositiveDefinite.exists_finiteMeasure`, for the pairing `L`) gives a finite measure `μ_y` on
   `W` with `φ_y(v) = ∫ exp (i L(p, v)) dμ_y(p)`, of total mass `‖y‖²`.
2. **Fourier uniqueness** for complex combinations of finite measures: if `∑ cᵢ ρ̂ᵢ = 0`, then
   `∑ cᵢ ρᵢ(s) = 0` on every measurable set. The real and imaginary parts of the coefficients
   separate since `ρ̂ᵢ(-v) = conj ρ̂ᵢ(v)`, and a real combination splits into two finite measures
   with the same Fourier transform. Every identity between matrix coefficients `⟪x, U v y⟫`
   therefore passes to the polarized values
   `μ_{x,y}(s) = ¼ (μ_{x+y}(s) - μ_{x-y}(s)) + i ¼ (μ_{x-iy}(s) - μ_{x+iy}(s))`, which are
   sesquilinear in `(x, y)`, real on the diagonal and bounded. They are represented by self-adjoint
   operators `E(s)` with `⟪x, E(s) y⟫ = μ_{x,y}(s)` and `E(W) = 1`.
3. **Covariance**: `μ_{U w y + c y}` has density `|exp (i L(p, w)) + c|²` with respect to `μ_y`
   (the two measures have the same Fourier transform). Polarizing `⟪U (-v) y, E(t) y⟫` with these
   densities gives `⟪y, U v E(t) y⟫ = ∫_t exp (i L(p, v)) dμ_y(p)`, so `⟪x, U v E(t) y⟫` is the
   Fourier transform of `μ_{x,y}` restricted to `t`, and Fourier uniqueness gives
   `μ_{x, E(t) y} = μ_{x,y}|_t`, i.e. `E(s) E(t) = E(s ∩ t)`. Each `E(s)` is then an orthogonal
   projection, with `‖E(s) y‖² = μ_y(s)`.
4. A map to orthogonal projections whose diagonal set functions `s ↦ ‖E(s) y‖²` are measures is a
   projection-valued measure: weak countable additivity on the diagonal implies strong countable
   additivity (`MeasureTheory.ProjectionValuedMeasure.ofMeasure`). The diagonal measures of `E_U`
   are the `μ_y`, so the Fourier transform of `E_U` has the matrix coefficients `⟪y, U v y⟫` and is
   `U`. Uniqueness: the diagonal measures of a projection-valued measure with Fourier transform `U`
   have the Fourier transforms `φ_y`, hence are the `μ_y`, and a projection-valued measure is
   determined by its diagonal measures.

## Main definitions

* `UnitaryAddRepresentation.pvm U L` — the projection-valued measure `E_U` on `W` of a strongly
  continuous unitary representation `U`.

## Main results

* `UnitaryAddRepresentation.isPositiveDefinite_inner_apply` — the matrix coefficients
  `v ↦ ⟪y, U v y⟫` of an additive character into the unitary group, continuous or not, are positive
  definite.
* `UnitaryAddRepresentation.fourier_pvm`, `UnitaryAddRepresentation.eq_pvm_of_fourier_eq`
  — existence and uniqueness: `U v = ∫ exp (i L(p, v)) dE_U(p)`, and `E_U` is the only
  projection-valued measure on `W` with Fourier transform `U`.
* `UnitaryAddRepresentation.existsUnique_fourier_eq` — **SNAG theorem**: `U` is the Fourier
  transform of a unique projection-valued measure on `W`.
* `UnitaryAddRepresentation.existsUnique_fourier_eq_strongDual` — **SNAG theorem** on the dual
  space: `U v = ∫ exp (i p v) dE(p)` for a unique `E` on `StrongDual ℝ V`.
* `UnitaryAddRepresentation.pvm_one` — the trivial representation has the Dirac measure at `0`.
* `UnitaryAddRepresentation.inner_apply_eq_integral_measure_pvm` — the diagonal measures:
  `⟪y, U v y⟫ = ∫ exp (i L(p, v)) dE_y(p)`.
* `UnitaryAddRepresentation.pvm_compContinuousAddMonoidHom`,
  `UnitaryAddRepresentation.pvm_compContinuousAddMonoidHom_strongDual` — **functoriality**: for
  `φ : V' →L[ℝ] V` the projection-valued measure of `U ∘ φ` is the image of `E_U` under the
  transpose of `φ`, `p ↦ p ∘ φ` on the dual spaces.
* `MeasureTheory.ProjectionValuedMeasure.pvm_fourier` — the converse: a projection-valued measure on
  `W` is the projection-valued measure of its Fourier transform.

## TODO

* The SNAG theorem for a locally compact abelian group `G` (Folland, Theorem 4.44): a strongly
  continuous unitary representation of `G` is `U g = ∫ ⟨χ, g⟩ dE(χ)` for a unique regular
  projection-valued measure `E` on the Pontryagin dual `Ĝ`. The proof above carries over once
  Bochner's theorem on LCA groups (see the TODO of
  `QuantumSystem.ForMathlib.MeasureTheory.Measure.CharacteristicFunction.Bochner`) and the
  Pontryagin dual with its Borel structure are available; only finite-dimensional real vector
  spaces are treated here.
* Weakly measurable representations: on a separable Hilbert space a unitary representation of `V`
  for which every matrix coefficient `v ↦ ⟪x, U v y⟫` is (Lebesgue) measurable is automatically
  strongly continuous (von Neumann), so the SNAG theorem holds for weakly measurable
  representations. This automatic continuity theorem is not formalized.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, CRC Press (1995), Theorem 4.44
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265 (2012),
  §6.1 (Stone's theorem, the case `V = ℝ`)
-/

@[expose] public section

open Set Filter Function Topology ContinuousLinearMap MeasureTheory Complex
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

/-! ### Unitary representations -/

namespace UnitaryAddRepresentation

/-! The lemmas of this section are algebraic: they hold for every additive character `U` of `G` into
the unitary group, a `UnitaryAddRepresentation G H` or an `AddChar G (UnitarySOT ℂ H)` on which no
continuity is imposed; `G` need not be commutative. -/

variable {G H F : Type*} [AddGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FunLike F G (UnitarySOT ℂ H)]
  [AddCharClass F G (UnitarySOT ℂ H)] (U : F)

/-- `U v (U w y) = U (v + w) y`. -/
lemma apply_apply (v w : G) (y : H) :
    U v (U w y) = U (v + w) y := by
  rw [map_add_eq_mul, UnitarySOT.coe_mul, mul_apply_eq_comp]

/-- The adjoint of `U w` is `U (-w)`: `⟪U w x, y⟫ = ⟪x, U (-w) y⟫`. -/
lemma inner_apply_left (w : G) (x y : H) :
    ⟪U w x, y⟫_ℂ = ⟪x, U (-w) y⟫_ℂ := by
  rw [map_neg_eq_inv, UnitarySOT.coe_inv, star_eq_adjoint, adjoint_inner_right]

/-- The matrix coefficient `v ↦ ⟪y, U v y⟫` of an additive character `U` into the unitary group,
continuous or not, is positive definite: the matrix `(⟪y, U (xᵢ - xⱼ) y⟫)ᵢⱼ` is the Gram matrix of the
vectors `U (-xᵢ) y`. -/
lemma isPositiveDefinite_inner_apply (y : H) :
    IsPositiveDefinite fun v : G => ⟪y, U v y⟫_ℂ := fun n x => by
  convert Matrix.posSemidef_gram ℂ fun i => U (-x i) y using 1
  ext i j
  rw [Matrix.of_apply, Matrix.gram_apply, inner_apply_left, neg_neg, apply_apply,
    sub_eq_add_neg]

end UnitaryAddRepresentation

namespace UnitaryAddRepresentation

variable {G H F : Type*} [AddCommGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FunLike F G (UnitarySOT ℂ H)]
  [AddCharClass F G (UnitarySOT ℂ H)] (U : F)

/-- The matrix coefficients of `U w y + c y`:
`⟪U w y + c y, U v (U w y + c y)⟫ = (1 + c c̄) φ(v) + c̄ φ(v + w) + c φ(v - w)` with
`φ(v) = ⟪y, U v y⟫`. -/
private lemma inner_add_smul_apply_unitary (v w : G) (c : ℂ) (y : H) :
    ⟪U w y + c • y,
        U v (U w y + c • y)⟫_ℂ =
      (1 + c * conj c) * ⟪y, U v y⟫_ℂ +
        conj c * ⟪y, (U (v + w) : H →L[ℂ] H) y⟫_ℂ +
          c * ⟪y, U (v - w) y⟫_ℂ := by
  have h₁ : ⟪U w y,
      U v (U w y)⟫_ℂ =
        ⟪y, U v y⟫_ℂ := by
    rw [inner_apply_left U, apply_apply U, apply_apply U,
      show -w + v + w = v by abel]
  have h₂ : ⟪U w y, U v y⟫_ℂ =
      ⟪y, U (v - w) y⟫_ℂ := by
    rw [inner_apply_left U, apply_apply U, neg_add_eq_sub]
  have h₃ : ⟪y, U v (U w y)⟫_ℂ =
      ⟪y, (U (v + w) : H →L[ℂ] H) y⟫_ℂ := by
    rw [apply_apply U]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    h₁, h₂, h₃]
  ring

end UnitaryAddRepresentation

/-! ### The Fourier transform along a continuous perfect pairing -/

namespace MeasureTheory.ProjectionValuedMeasure

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **Fourier transform** `v ↦ ∫ exp (i L(p, v)) dE(p)` of a projection-valued measure `E` on `W`
along a continuous perfect pairing `L` of `W` with a finite-dimensional `V`, as a strongly continuous
unitary representation of `V`: `ProjectionValuedMeasure.fourierRepresentation`, the measurability and
the continuity of the pairing and the first countability of `V` being supplied by the pairing. -/
noncomputable def fourierOfIsContPerfPair (E : ProjectionValuedMeasure W H)
    (L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ) [L.IsContPerfPair] : UnitaryAddRepresentation V H :=
  haveI := L.firstCountableTopology_of_isContPerfPair
  E.fourierRepresentation L L.measurable_flip_apply_of_isContPerfPair
    fun _ => L.continuous_of_isContPerfPair

/-- The unitaries of `fourierOfIsContPerfPair` are those of `fourier`. -/
@[simp] lemma fourierOfIsContPerfPair_apply (E : ProjectionValuedMeasure W H)
    (L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ) [L.IsContPerfPair] (v : V) :
    E.fourierOfIsContPerfPair L v = E.fourier L L.measurable_flip_apply_of_isContPerfPair v :=
  rfl

end MeasureTheory.ProjectionValuedMeasure

/-! ### Fourier uniqueness for complex combinations of finite measures -/

/-- Integration against a finite combination `∑ cᵢ ρᵢ` of measures with nonnegative coefficients. -/
private lemma integral_sum_smul_measure {X ι E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Finset ι) (ρ : ι → Measure X) (c : ι → ℝ≥0) {g : X → E}
    (hg : ∀ i, Integrable g (ρ i)) :
    ∫ x, g x ∂(∑ i ∈ S, c i • ρ i) = ∑ i ∈ S, (c i : ℝ) • ∫ x, g x ∂ρ i := by
  rw [integral_finsetSum_measure fun i _ => (hg i).smul_measure_nnreal]
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def]

section FourierUniqueness

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] {L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  [L.IsContPerfPair] {ι : Type*}

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] in
/-- The phases `w ↦ exp (i L(w, v))` are integrable against every finite measure. -/
private lemma integrable_cexp_pairing (μ : Measure W) [IsFiniteMeasure μ] (v : V) :
    Integrable (fun w => cexp (L w v * I)) μ :=
  Integrable.of_bound ((Complex.measurable_ofReal.comp
    (L.flip.continuous_of_isContPerfPair (x := v)).measurable).mul_const _).cexp.aestronglyMeasurable
    1 (ae_of_all _ fun w => by simp [norm_exp_ofReal_mul_I])

/-- **Fourier uniqueness**, real combinations: if `∑ aᵢ ρ̂ᵢ = 0` for finite measures `ρᵢ` and real
coefficients `aᵢ`, then `∑ aᵢ ρᵢ(s) = 0` on every measurable set. The positive and negative parts
of the combination are finite measures with the same Fourier transform. -/
private lemma sum_mul_measureReal_eq_zero_of_real (S : Finset ι) (ρ : ι → Measure W)
    [∀ i, IsFiniteMeasure (ρ i)] (a : ι → ℝ)
    (h : ∀ v, ∑ i ∈ S, (a i : ℂ) * ∫ w, cexp (L w v * I) ∂ρ i = 0) {s : Set W}
    (hs : MeasurableSet s) : ∑ i ∈ S, a i * (ρ i).real s = 0 := by
  have hpn : ∀ i, ((a i).toNNReal : ℝ) - ((-a i).toNNReal : ℝ) = a i := fun i => by
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    exact max_zero_sub_max_neg_zero_eq_self (a i)
  have hPN : ∑ i ∈ S, (a i).toNNReal • ρ i = ∑ i ∈ S, (-a i).toNNReal • ρ i := by
    refine Measure.ext_of_integral_cexp_eq (L := L) fun v => ?_
    rw [integral_sum_smul_measure _ _ _ fun i => integrable_cexp_pairing (ρ i) v,
      integral_sum_smul_measure _ _ _ fun i => integrable_cexp_pairing (ρ i) v, ← sub_eq_zero,
      ← Finset.sum_sub_distrib, ← h v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.real_smul, Complex.real_smul, ← sub_mul, ← ofReal_sub, hpn]
  have hint : ∀ i, Integrable (s.indicator (1 : W → ℝ)) (ρ i) := fun i =>
    (integrable_const 1).indicator hs
  have hreal := congrArg (fun μ : Measure W => ∫ w, s.indicator (1 : W → ℝ) w ∂μ) hPN
  simp only [integral_sum_smul_measure _ _ _ hint, integral_indicator_one hs, smul_eq_mul] at hreal
  rw [← sub_eq_zero.mpr hreal, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_mul, hpn]

/-- **Fourier uniqueness** for complex combinations of finite measures: if
`∑ cᵢ ∫ exp (i L(w, v)) dρᵢ(w) = 0` for every `v`, then `∑ cᵢ ρᵢ(s) = 0` on every measurable set.
Since `ρ̂ᵢ(-v) = conj ρ̂ᵢ(v)`, the real and imaginary parts of the coefficients separately give
vanishing combinations. -/
private lemma sum_mul_measureReal_eq_zero (S : Finset ι) (ρ : ι → Measure W)
    [∀ i, IsFiniteMeasure (ρ i)] (c : ι → ℂ)
    (h : ∀ v, ∑ i ∈ S, c i * ∫ w, cexp (L w v * I) ∂ρ i = 0) {s : Set W} (hs : MeasurableSet s) :
    ∑ i ∈ S, c i * ((ρ i).real s : ℂ) = 0 := by
  have hconj : ∀ i v, ∫ w, cexp (L w (-v) * I) ∂ρ i = conj (∫ w, cexp (L w v * I) ∂ρ i) :=
    fun i v => by
      rw [← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      simp only [← Complex.exp_conj, map_mul, conj_ofReal, conj_I, map_neg, ofReal_neg, neg_mul,
        mul_neg]
  have h' : ∀ v, ∑ i ∈ S, conj (c i) * ∫ w, cexp (L w v * I) ∂ρ i = 0 := fun v => by
    have := congrArg conj (h (-v))
    simpa only [map_sum, map_mul, hconj, Complex.conj_conj, map_zero] using this
  have hre : ∀ v, ∑ i ∈ S, ((c i).re : ℂ) * ∫ w, cexp (L w v * I) ∂ρ i = 0 := fun v => by
    simp_rw [re_eq_add_conj, div_mul_eq_mul_div, add_mul, ← Finset.sum_div,
      Finset.sum_add_distrib, h v, h' v, add_zero, zero_div]
  have him : ∀ v, ∑ i ∈ S, ((c i).im : ℂ) * ∫ w, cexp (L w v * I) ∂ρ i = 0 := fun v => by
    simp_rw [im_eq_sub_conj, div_mul_eq_mul_div, sub_mul, ← Finset.sum_div,
      Finset.sum_sub_distrib, h v, h' v, sub_zero, zero_div]
  have h₁ := sum_mul_measureReal_eq_zero_of_real S ρ _ hre hs
  have h₂ := sum_mul_measureReal_eq_zero_of_real S ρ _ him hs
  calc ∑ i ∈ S, c i * ((ρ i).real s : ℂ)
      = ((∑ i ∈ S, (c i).re * (ρ i).real s : ℝ) : ℂ) +
          ((∑ i ∈ S, (c i).im * (ρ i).real s : ℝ) : ℂ) * I := by
        push_cast
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [← re_add_im (c i)]
        ring
    _ = 0 := by rw [h₁, h₂]; simp

/-- **Fourier uniqueness** for formal complex combinations of two families of finite measures: if
the combinations `f` of the `ρᵢ` and `g` of the `σⱼ` have the same Fourier transform, they agree
on every measurable set. -/
private lemma linearCombination_measureReal_eq {κ : Type*} {ρ : ι → Measure W}
    {σ : κ → Measure W} [∀ i, IsFiniteMeasure (ρ i)] [∀ j, IsFiniteMeasure (σ j)] {f : ι →₀ ℂ}
    {g : κ →₀ ℂ}
    (h : Finsupp.linearCombination ℂ (fun i v => ∫ w, cexp (L w v * I) ∂ρ i) f =
      Finsupp.linearCombination ℂ (fun j v => ∫ w, cexp (L w v * I) ∂σ j) g)
    {s : Set W} (hs : MeasurableSet s) :
    Finsupp.linearCombination ℂ (fun i => ((ρ i).real s : ℂ)) f =
      Finsupp.linearCombination ℂ (fun j => ((σ j).real s : ℂ)) g := by
  have : ∀ k, IsFiniteMeasure (Sum.elim ρ σ k) := by
    rintro (i | j) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  set F := Finsupp.mapDomain Sum.inl f - Finsupp.mapDomain Sum.inr g
  have key : ∀ (φ : Measure W → ℂ),
      Finsupp.linearCombination ℂ (fun k => φ (Sum.elim ρ σ k)) F =
        Finsupp.linearCombination ℂ (fun i => φ (ρ i)) f -
          Finsupp.linearCombination ℂ (fun j => φ (σ j)) g := fun φ => by
    simp only [F, map_sub, Finsupp.linearCombination_mapDomain]
    rfl
  have hF := sum_mul_measureReal_eq_zero (L := L) F.support (Sum.elim ρ σ) F (s := s)
    (fun v => by
      have hv := congrFun h v
      have := key fun μ => ∫ w, cexp (L w v * I) ∂μ
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hv this ⊢
      rw [this, hv, sub_self]) hs
  have := key fun μ => (μ.real s : ℂ)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] at this ⊢
  rw [← sub_eq_zero, ← this, hF]

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] in
/-- The pairing `w ↦ L(w, v)` is continuous. -/
private lemma continuous_pairing_left (v : V) : Continuous fun w => L w v :=
  L.flip.continuous_of_isContPerfPair

variable (L) in
/-- The Fourier transforms `v ↦ ∫ exp (i L(w, v)) dρᵢ(w)` of a family of measures, extended
linearly to formal combinations. -/
private noncomputable abbrev ft (ρ : ι → Measure W) : (ι →₀ ℂ) →ₗ[ℂ] V → ℂ :=
  Finsupp.linearCombination ℂ fun i v => ∫ w, cexp (L w v * I) ∂ρ i

/-- The values `ρᵢ(s)` (`0` off the measurable sets) of a family of finite measures, extended
linearly to formal combinations. -/
private noncomputable abbrev ev (ρ : ι → Measure W) [∀ i, IsFiniteMeasure (ρ i)] (s : Set W) :
    (ι →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun i => ((ρ i).toSignedMeasure s : ℂ)

omit [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [BorelSpace W] in
/-- `ev` vanishes off the measurable sets. -/
private lemma ev_of_not_measurableSet (ρ : ι → Measure W) [∀ i, IsFiniteMeasure (ρ i)]
    {s : Set W} (hs : ¬MeasurableSet s) (f : ι →₀ ℂ) : ev ρ s f = 0 := by
  have h : ∀ i, (ρ i).toSignedMeasure s = 0 := fun i => VectorMeasure.not_measurable _ hs
  simp [ev, h, Finsupp.linearCombination_apply]

/-- **Fourier uniqueness** for formal combinations: combinations with the same Fourier transform
take the same values. -/
private lemma ev_eq_of_ft_eq {κ : Type*} {ρ : ι → Measure W} {σ : κ → Measure W}
    [∀ i, IsFiniteMeasure (ρ i)] [∀ j, IsFiniteMeasure (σ j)] {f : ι →₀ ℂ} {g : κ →₀ ℂ}
    (h : ft L ρ f = ft L σ g) (s : Set W) : ev ρ s f = ev σ s g := by
  by_cases hs : MeasurableSet s
  · simp only [ev, Measure.toSignedMeasure_apply_measurable hs]
    exact linearCombination_measureReal_eq h hs
  · rw [ev_of_not_measurableSet ρ hs, ev_of_not_measurableSet σ hs]

end FourierUniqueness

/-! ### Formal polarization -/

section Polarization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The formal polarization `¼ ([x+y] - [x-y]) + i ¼ ([x-iy] - [x+iy])` of a pair of vectors, a
finitely supported combination of vectors: `⟪x, G y⟫` is the corresponding combination of the
values `⟪u, G u⟫` of the quadratic form of `G`. -/
private noncomputable def pol (x y : H) : H →₀ ℂ :=
  Finsupp.single (x + y) 4⁻¹ - Finsupp.single (x - y) 4⁻¹ + Finsupp.single (x - I • y) (I * 4⁻¹) -
    Finsupp.single (x + I • y) (I * 4⁻¹)

private lemma linearCombination_pol {M : Type*} [AddCommGroup M] [Module ℂ M] (g : H → M)
    (x y : H) :
    Finsupp.linearCombination ℂ g (pol x y) =
      (4⁻¹ : ℂ) • (g (x + y) - g (x - y)) + (I * 4⁻¹) • (g (x - I • y) - g (x + I • y)) := by
  simp only [pol, map_add, map_sub, Finsupp.linearCombination_single, smul_sub]
  abel

private lemma inner_apply_eq_linearCombination_pol (G : H →L[ℂ] H) (x y : H) :
    ⟪x, G y⟫_ℂ = Finsupp.linearCombination ℂ (fun u => ⟪u, G u⟫_ℂ) (pol x y) := by
  rw [linearCombination_pol, G.inner_apply_eq_polarization, smul_eq_mul, smul_eq_mul,
    Complex.real_smul, Complex.real_smul]
  push_cast
  ring

private lemma linearCombination_apply_apply {ι V : Type*} (g : ι → V → ℂ) (f : ι →₀ ℂ) (v : V) :
    Finsupp.linearCombination ℂ g f v = Finsupp.linearCombination ℂ (fun i => g i v) f := by
  simp [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]

/-- Scalar polarization: `¼ (|z+1|² - |z-1|²) + i ¼ (|z-i|² - |z+i|²) = z̄`. -/
private lemma polarization_norm_sq (z : ℂ) :
    (4⁻¹ : ℂ) • (((‖z + 1‖ ^ 2 : ℝ) : ℂ) - ((‖z + -1‖ ^ 2 : ℝ) : ℂ)) +
      (I * 4⁻¹) • (((‖z + -I‖ ^ 2 : ℝ) : ℂ) - ((‖z + I‖ ^ 2 : ℝ) : ℂ)) = conj z := by
  apply Complex.ext <;> simp [Complex.sq_norm, Complex.normSq_apply] <;> ring

end Polarization

/-! ### The SNAG theorem -/

namespace UnitaryAddRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] {L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  [L.IsContPerfPair] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : UnitaryAddRepresentation V H)

/-! #### The scalar measures `μ_y` -/

variable (L) in
/-- The finite measure `μ_y` on `W` with `⟪y, U v y⟫ = ∫ exp (i L(p, v)) dμ_y(p)`, given by
Bochner's theorem. It is the diagonal measure of `U.pvm L` (`measure_pvm`). -/
private noncomputable def bochner (y : H) : Measure W :=
  ((isPositiveDefinite_inner_apply U y).exists_finiteMeasure L
    (UnitaryRepresentation.continuous_inner_apply U y y)).choose

private instance (y : H) : IsFiniteMeasure (U.bochner L y) := by
  unfold bochner
  infer_instance

/-- `∫ exp (i L(p, v)) dμ_y(p) = ⟪y, U v y⟫`. -/
private lemma integral_bochner (y : H) (v : V) :
    ∫ p, cexp (L p v * I) ∂U.bochner L y = ⟪y, U v y⟫_ℂ :=
  (((isPositiveDefinite_inner_apply U y).exists_finiteMeasure L
    (UnitaryRepresentation.continuous_inner_apply U y y)).choose_spec v).symm

/-- The total mass of `μ_y` is `‖y‖²`. -/
private lemma measureReal_bochner_univ (y : H) : (U.bochner L y).real univ = ‖y‖ ^ 2 := by
  have h := U.integral_bochner (L := L) y 0
  simp only [map_zero, ofReal_zero, zero_mul, Complex.exp_zero, integral_const, Complex.real_smul,
    mul_one, map_zero_eq_one, UnitarySOT.coe_one, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (h.trans (by push_cast; rfl))

/-! #### Fourier transforms of formal combinations -/

/-- The Fourier transform of the polarization of `(x, y)` is the matrix coefficient
`v ↦ ⟪x, U v y⟫`. -/
private lemma ft_pol (x y : H) :
    ft L (U.bochner L) (pol x y) = fun v => ⟪x, U v y⟫_ℂ := by
  funext v
  rw [linearCombination_apply_apply]
  simp_rw [U.integral_bochner (L := L)]
  rw [← inner_apply_eq_linearCombination_pol]

/-! #### The sesquilinear forms `(x, y) ↦ μ_{x,y}(s)` -/

variable (L) in
/-- The value `μ_{x,y}(s)` of the polarized measure, `¼ (μ_{x+y} - μ_{x-y}) + i ¼ (μ_{x-iy} -
μ_{x+iy})` on `s`. -/
private noncomputable def form (s : Set W) (x y : H) : ℂ :=
  ev (U.bochner L) s (pol x y)

private lemma form_add_left (s : Set W) (x x' y : H) :
    U.form L s (x + x') y = U.form L s x y + U.form L s x' y := by
  rw [form, form, form, ← map_add]
  refine ev_eq_of_ft_eq (L := L) ?_ s
  rw [map_add, U.ft_pol (L := L), U.ft_pol (L := L), U.ft_pol (L := L)]
  funext v
  simp [inner_add_left]

private lemma form_smul_left (s : Set W) (c : ℂ) (x y : H) :
    U.form L s (c • x) y = conj c * U.form L s x y := by
  rw [form, form, ← smul_eq_mul, ← map_smul]
  refine ev_eq_of_ft_eq (L := L) ?_ s
  rw [map_smul, U.ft_pol (L := L), U.ft_pol (L := L)]
  funext v
  simp [inner_smul_left]

private lemma form_add_right (s : Set W) (x y y' : H) :
    U.form L s x (y + y') = U.form L s x y + U.form L s x y' := by
  rw [form, form, form, ← map_add]
  refine ev_eq_of_ft_eq (L := L) ?_ s
  rw [map_add, U.ft_pol (L := L), U.ft_pol (L := L), U.ft_pol (L := L)]
  funext v
  simp [inner_add_right]

private lemma form_smul_right (s : Set W) (c : ℂ) (x y : H) :
    U.form L s x (c • y) = c * U.form L s x y := by
  rw [form, form, ← smul_eq_mul, ← map_smul]
  refine ev_eq_of_ft_eq (L := L) ?_ s
  rw [map_smul, U.ft_pol (L := L), U.ft_pol (L := L)]
  funext v
  simp [inner_smul_right]

/-- On the diagonal, `μ_{y,y}(s) = μ_y(s)`. -/
private lemma form_self (s : Set W) (y : H) :
    U.form L s y y = ((U.bochner L y).toSignedMeasure s : ℂ) := by
  have h : ev (U.bochner L) s (pol y y) = ev (U.bochner L) s (Finsupp.single y 1) := by
    refine ev_eq_of_ft_eq (L := L) ?_ s
    rw [U.ft_pol (L := L), Finsupp.linearCombination_single, one_smul]
    funext v
    rw [U.integral_bochner (L := L)]
  rw [form, h, Finsupp.linearCombination_single, one_smul]

/-- `0 ≤ μ_y(s) ≤ ‖y‖²`. -/
private lemma toSignedMeasure_bochner_mem (s : Set W) (y : H) :
    0 ≤ (U.bochner L y).toSignedMeasure s ∧ (U.bochner L y).toSignedMeasure s ≤ ‖y‖ ^ 2 := by
  by_cases hs : MeasurableSet s
  · rw [Measure.toSignedMeasure_apply_measurable hs, ← U.measureReal_bochner_univ (L := L) y]
    exact ⟨measureReal_nonneg, measureReal_mono (subset_univ s)⟩
  · rw [VectorMeasure.not_measurable _ hs]
    exact ⟨le_rfl, by positivity⟩

/-- A crude bound, `‖μ_{x,y}(s)‖ ≤ ‖x‖² + ‖y‖²`, from the polarization formula and the
parallelogram law. -/
private lemma norm_form_le_sq (s : Set W) (x y : H) :
    ‖U.form L s x y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have p₁ := parallelogram_law_with_norm ℂ x y
  have p₂ := parallelogram_law_with_norm ℂ x (I • y)
  rw [norm_smul, norm_I, one_mul] at p₂
  obtain ⟨a₀, a₁⟩ := U.toSignedMeasure_bochner_mem (L := L) s (x + y)
  obtain ⟨b₀, b₁⟩ := U.toSignedMeasure_bochner_mem (L := L) s (x - y)
  obtain ⟨c₀, c₁⟩ := U.toSignedMeasure_bochner_mem (L := L) s (x - I • y)
  obtain ⟨d₀, d₁⟩ := U.toSignedMeasure_bochner_mem (L := L) s (x + I • y)
  set a := (U.bochner L (x + y)).toSignedMeasure s
  set b := (U.bochner L (x - y)).toSignedMeasure s
  set c := (U.bochner L (x - I • y)).toSignedMeasure s
  set d := (U.bochner L (x + I • y)).toSignedMeasure s
  have hform : U.form L s x y = ((4⁻¹ * (a - b) : ℝ) : ℂ) + ((4⁻¹ * (c - d) : ℝ) : ℂ) * I := by
    rw [form, linearCombination_pol]
    simp only [smul_eq_mul, a, b, c, d]
    push_cast
    ring
  rw [hform]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_I, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have e₁ : |4⁻¹ * (a - b)| ≤ 4⁻¹ * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith
  have e₂ : |4⁻¹ * (c - d)| ≤ 4⁻¹ * (‖x + I • y‖ ^ 2 + ‖x - I • y‖ ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith
  nlinarith

/-- **Boundedness**: `‖μ_{x,y}(s)‖ ≤ 2 ‖x‖ ‖y‖`, by rescaling `(x, y)` to `(t x, t⁻¹ y)`, which
leaves `μ_{x,y}` unchanged, in the crude bound. -/
private lemma norm_form_le (s : Set W) (x y : H) :
    ‖U.form L s x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using U.form_smul_left (L := L) s 0 0 y
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using U.form_smul_right (L := L) s 0 x 0
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set t := √(‖y‖ / ‖x‖)
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hy' hx')
  have ht2 : t ^ 2 = ‖y‖ / ‖x‖ := Real.sq_sqrt (div_pos hy' hx').le
  have key : U.form L s ((t : ℂ) • x) ((t⁻¹ : ℝ) • y) = U.form L s x y := by
    rw [U.form_smul_left (L := L), ← Complex.coe_smul, U.form_smul_right (L := L), conj_ofReal, ← mul_assoc,
      ← ofReal_mul, mul_inv_cancel₀ ht.ne', ofReal_one, one_mul]
  have h := U.norm_form_le_sq (L := L) s ((t : ℂ) • x) ((t⁻¹ : ℝ) • y)
  rw [key, norm_smul, norm_smul, norm_real, Real.norm_of_nonneg ht.le,
    Real.norm_of_nonneg (inv_pos.mpr ht).le, mul_pow, mul_pow, inv_pow, ht2] at h
  calc _ ≤ ‖y‖ / ‖x‖ * ‖x‖ ^ 2 + (‖y‖ / ‖x‖)⁻¹ * ‖y‖ ^ 2 := h
    _ = 2 * ‖x‖ * ‖y‖ := by
      field_simp
      ring

/-! #### The operators `E(s)` -/

variable (L) in
/-- The bounded sesquilinear form `(x, y) ↦ μ_{x,y}(s)`, conjugate-linear in `x`. -/
private noncomputable def formCLM (s : Set W) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (U.form L s)
      (fun x x' y => U.form_add_left s x x' y) (fun c x y => U.form_smul_left (L := L) s c x y)
      (fun x y y' => U.form_add_right s x y y') (fun c x y => U.form_smul_right (L := L) s c x y))
    2 fun x y => U.norm_form_le s x y

variable (L) in
/-- The operator `E(s)` represented by the form `(x, y) ↦ μ_{x,y}(s)`; it is the value on `s` of
the projection-valued measure `U.pvm`. -/
private noncomputable def op (s : Set W) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (U.formCLM L s)

/-- `⟪E(s) x, y⟫ = μ_{x,y}(s)`. -/
private lemma inner_op_left (s : Set W) (x y : H) :
    ⟪U.op L s x, y⟫_ℂ = U.form L s x y :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ x y

/-- `E(s)` is self-adjoint, since its quadratic form `y ↦ μ_y(s)` is real. -/
private lemma isSelfAdjoint_op (s : Set W) : IsSelfAdjoint (U.op L s) := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    ((LinearMap.isSymmetric_iff_inner_map_self_real _).mpr fun x => ?_)
  rw [ContinuousLinearMap.coe_coe, inner_op_left, form_self, conj_ofReal]

/-- `⟪x, E(s) y⟫ = μ_{x,y}(s)`. -/
private lemma inner_op (s : Set W) (x y : H) :
    ⟪x, U.op L s y⟫_ℂ = U.form L s x y := by
  rw [← inner_op_left, ← ContinuousLinearMap.adjoint_inner_left, ← star_eq_adjoint,
    (U.isSelfAdjoint_op s).star_eq]

/-- `E(s) = 0` off the measurable sets. -/
private lemma op_of_not_measurableSet {s : Set W} (hs : ¬MeasurableSet s) :
    U.op L s = 0 :=
  ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => by
    simp [inner_op, form, ev_of_not_measurableSet _ hs]

/-- `E(X) = 1`: `μ_{x,y}(X)` is the matrix coefficient `⟪x, U 0 y⟫ = ⟪x, y⟫`. -/
private lemma op_univ : U.op L univ = (1 : H →L[ℂ] H) :=
  ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => by
    have h : ev (U.bochner L) univ (pol x y) = ft L (U.bochner L) (pol x y) 0 := by
      rw [linearCombination_apply_apply]
      refine congrArg (fun g => Finsupp.linearCombination ℂ g (pol x y)) (funext fun u => ?_)
      simp only [map_zero, ofReal_zero, zero_mul, Complex.exp_zero, integral_const,
        Measure.toSignedMeasure_apply_measurable MeasurableSet.univ, Complex.real_smul, mul_one]
    rw [inner_op, form, h, U.ft_pol (L := L)]
    beta_reduce
    rw [map_zero_eq_one, UnitarySOT.coe_one]

/-! #### Covariance and multiplicativity -/

/-- **Covariance**: `μ_{U w y + c y}` has density `|exp (i L(p, w)) + c|²` with respect to `μ_y`, since
both measures have Fourier transform `(1 + |c|²) φ(v) + c̄ φ(v + w) + c φ(v - w)`. -/
private lemma bochner_add_smul (w : V) (c : ℂ) (y : H) :
    U.bochner L (U w y + c • y) =
      (U.bochner L y).withDensity fun p => ENNReal.ofReal (‖cexp (L p w * I) + c‖ ^ 2) := by
  have := continuous_pairing_left (L := L) w
  have hcont : Continuous fun p : W => ‖cexp (L p w * I) + c‖ ^ 2 := by fun_prop
  have hint : Integrable (fun p : W => ‖cexp (L p w * I) + c‖ ^ 2) (U.bochner L y) :=
    Integrable.of_bound hcont.aestronglyMeasurable ((1 + ‖c‖) ^ 2) (ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      exact (norm_add_le _ _).trans_eq (by rw [norm_exp_ofReal_mul_I]))
  have : IsFiniteMeasure ((U.bochner L y).withDensity
      fun p => ENNReal.ofReal (‖cexp (L p w * I) + c‖ ^ 2)) :=
    isFiniteMeasure_withDensity_ofReal hint.2
  have hpt : ∀ (v : V) (p : W),
      (ENNReal.ofReal (‖cexp (L p w * I) + c‖ ^ 2)).toReal • cexp (L p v * I) =
        (1 + c * conj c) * cexp (L p v * I) + conj c * cexp (L p (v + w) * I) +
          c * cexp (L p (v - w) * I) := fun v p => by
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul, ofReal_pow, ← mul_conj', map_add]
    have ha : cexp (L p w * I) * conj (cexp (L p w * I)) = 1 := by
      rw [mul_conj', norm_exp_ofReal_mul_I]
      simp
    have h₁ : cexp (L p w * I) * cexp (L p v * I) = cexp (L p (v + w) * I) := by
      rw [← Complex.exp_add, map_add]
      push_cast
      ring_nf
    have h₂ : conj (cexp (L p w * I)) * cexp (L p v * I) = cexp (L p (v - w) * I) := by
      rw [← Complex.exp_conj, ← Complex.exp_add, map_sub]
      simp only [map_mul, conj_ofReal, conj_I]
      push_cast
      ring_nf
    linear_combination cexp (L p v * I) * ha + conj c * h₁ + c * h₂
  refine Measure.ext_of_integral_cexp_eq (L := L) fun v => ?_
  rw [U.integral_bochner (L := L), inner_add_smul_apply_unitary U, integral_withDensity_eq_integral_toReal_smul
    hcont.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [hpt v]
  have hi : ∀ (a : ℂ) (u : V), Integrable (fun p : W => a * cexp (L p u * I))
      (U.bochner L y) := fun a u => (integrable_cexp_pairing _ u).const_mul a
  have hi₂ : Integrable (fun p : W => (1 + c * conj c) * cexp (L p v * I) +
      conj c * cexp (L p (v + w) * I)) (U.bochner L y) := (hi _ v).add (hi _ (v + w))
  rw [integral_add hi₂ (hi _ (v - w)),
    integral_add (hi _ v) (hi _ (v + w)), integral_const_mul, integral_const_mul,
    integral_const_mul, U.integral_bochner (L := L), U.integral_bochner (L := L), U.integral_bochner (L := L)]

/-- `μ_{U w y + c y}(t) = ∫_t |exp (i L(p, w)) + c|² dμ_y(p)`. -/
private lemma measureReal_bochner_add_smul (w : V) (c : ℂ) (y : H) {t : Set W}
    (ht : MeasurableSet t) :
    (U.bochner L (U w y + c • y)).real t =
      ∫ p in t, ‖cexp (L p w * I) + c‖ ^ 2 ∂U.bochner L y := by
  have := continuous_pairing_left (L := L) w
  have hcont : Continuous fun p : W => ‖cexp (L p w * I) + c‖ ^ 2 := by fun_prop
  rw [U.bochner_add_smul, measureReal_def, withDensity_apply _ ht,
    ← integral_toReal hcont.measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun p => ENNReal.toReal_ofReal (by positivity))

/-- **The key identity** `⟪y, U v E(t) y⟫ = ∫_t exp (i L(p, v)) dμ_y(p)`: polarizing
`⟪U (-v) y, E(t) y⟫` expresses it through the measures `μ_{U (-v) y + c y}`, and the covariance
`μ_{U (-v) y + c y} = |exp (-i L(p, v)) + c|² μ_y` turns the polarization into the integral of
`exp (i L(p, v))`. -/
private lemma inner_apply_op_self (v : V) {t : Set W} (ht : MeasurableSet t)
    (y : H) :
    ⟪y, U v (U.op L t y)⟫_ℂ = ∫ p in t, cexp (L p v * I) ∂U.bochner L y := by
  have hm : ∀ c : ℂ, ((U.bochner L (U (-v) y + c • y)).toSignedMeasure t : ℂ) =
      ∫ p in t, ((‖cexp (L p (-v) * I) + c‖ ^ 2 : ℝ) : ℂ) ∂U.bochner L y := fun c => by
    rw [Measure.toSignedMeasure_apply_measurable ht, U.measureReal_bochner_add_smul _ _ _ ht,
      integral_complex_ofReal]
  have h₁ := hm 1
  rw [one_smul] at h₁
  have h₂ := hm (-1)
  rw [neg_smul, one_smul, ← sub_eq_add_neg] at h₂
  have h₃ := hm (-I)
  rw [neg_smul, ← sub_eq_add_neg] at h₃
  have h₄ := hm I
  have := continuous_pairing_left (L := L) (-v)
  have hint : ∀ c : ℂ, Integrable (fun p : W => ((‖cexp (L p (-v) * I) + c‖ ^ 2 : ℝ) : ℂ))
      ((U.bochner L y).restrict t) := fun c => by
    refine Integrable.of_bound (by fun_prop) ((1 + ‖c‖) ^ 2) (ae_of_all _ fun p => ?_)
    rw [norm_real, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact (norm_add_le _ _).trans_eq (by rw [norm_exp_ofReal_mul_I])
  have hleft : ⟪y, U v (U.op L t y)⟫_ℂ =
      ⟪U (-v) y, U.op L t y⟫_ℂ := by
    rw [inner_apply_left U, neg_neg]
  have hA : Integrable (fun p : W => (4⁻¹ : ℂ) •
      (((‖cexp (L p (-v) * I) + 1‖ ^ 2 : ℝ) : ℂ) - ((‖cexp (L p (-v) * I) + -1‖ ^ 2 : ℝ) : ℂ)))
      ((U.bochner L y).restrict t) := ((hint 1).sub (hint (-1))).smul (4⁻¹ : ℂ)
  have hB : Integrable (fun p : W => (I * 4⁻¹) •
      (((‖cexp (L p (-v) * I) + -I‖ ^ 2 : ℝ) : ℂ) - ((‖cexp (L p (-v) * I) + I‖ ^ 2 : ℝ) : ℂ)))
      ((U.bochner L y).restrict t) := ((hint (-I)).sub (hint I)).smul (I * 4⁻¹)
  rw [hleft, inner_op, form, linearCombination_pol, h₁, h₂, h₃, h₄,
    ← integral_sub (hint 1) (hint (-1)), ← integral_sub (hint (-I)) (hint I), ← integral_smul,
    ← integral_smul, ← integral_add hA hB]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  beta_reduce
  rw [polarization_norm_sq, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, map_neg, ofReal_neg]
  ring_nf

/-- The polarized key identity: `⟪x, U v E(t) y⟫` is the Fourier transform of the polarization of
the measures `μ_u` restricted to `t`. -/
private lemma ft_restrict_pol {t : Set W} (ht : MeasurableSet t) (x y : H) :
    ft L (fun u => (U.bochner L u).restrict t) (pol x y) =
      fun v => ⟪x, U v (U.op L t y)⟫_ℂ := by
  funext v
  rw [linearCombination_apply_apply]
  simp_rw [← U.inner_apply_op_self v ht]
  exact (inner_apply_eq_linearCombination_pol ((U v : H →L[ℂ] H).comp (U.op L t)) x y).symm

/-- **Multiplicativity**: `E(s) E(t) = E(s ∩ t)` for measurable `s` and `t`. The polarized measures
satisfy `μ_{x, E(t) y} = μ_{x,y}|_t`, since both have Fourier transform `v ↦ ⟪x, U v E(t) y⟫`. -/
private lemma op_mul_op {s t : Set W} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    U.op L s * U.op L t = U.op L (s ∩ t) :=
  ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => by
    have hr : ev (fun u => (U.bochner L u).restrict t) s (pol x y) =
        ev (U.bochner L) (s ∩ t) (pol x y) := by
      refine congrArg (fun g => Finsupp.linearCombination ℂ g (pol x y)) (funext fun u => ?_)
      rw [Measure.toSignedMeasure_apply_measurable hs,
        Measure.toSignedMeasure_apply_measurable (hs.inter ht), measureReal_restrict_apply hs]
    rw [mul_apply_eq_comp, inner_op, inner_op, form, form, ← hr]
    exact ev_eq_of_ft_eq (L := L) (by rw [U.ft_pol (L := L), U.ft_restrict_pol ht]) s

/-- `E(s)` is an orthogonal projection. -/
private lemma isStarProjection_op (s : Set W) : IsStarProjection (U.op L s) := by
  by_cases hs : MeasurableSet s
  · refine ⟨?_, U.isSelfAdjoint_op s⟩
    rw [IsIdempotentElem, U.op_mul_op hs hs, inter_self]
  · rw [U.op_of_not_measurableSet hs]
    exact .zero _

/-- `μ_y(s) = ‖E(s) y‖²`. -/
private lemma bochner_apply (y : H) {s : Set W} (hs : MeasurableSet s) :
    U.bochner L y s = ‖U.op L s y‖ₑ ^ 2 := by
  have h := (U.isStarProjection_op (L := L) s).inner_apply_self y
  rw [inner_op, form_self, Measure.toSignedMeasure_apply_measurable hs] at h
  rw [← ofReal_measureReal, Complex.ofReal_injective h, ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]

/-! #### The projection-valued measure -/

variable (L) in
/-- The **projection-valued measure** `E_U` on `W` of a strongly continuous unitary representation
`U` of `V`: the unique projection-valued measure with `U v = ∫ exp (i L(p, v)) dE_U(p)`
(`UnitaryAddRepresentation.fourier_pvm`, `UnitaryAddRepresentation.eq_pvm_of_fourier_eq`).
For `L = topDualPairing ℝ V` it is a projection-valued measure on the dual `StrongDual ℝ V`. -/
@[no_expose] noncomputable def pvm : ProjectionValuedMeasure W H :=
  ProjectionValuedMeasure.ofMeasure (U.op L) (U.bochner L)
    (fun _ hs => U.op_of_not_measurableSet hs) U.isStarProjection_op U.op_univ
    fun y _ hs => U.bochner_apply y hs

/-- The diagonal measures of `E_U` are the Bochner measures `μ_y`. -/
private lemma measure_pvm (y : H) : (U.pvm L).measure y = U.bochner L y :=
  ProjectionValuedMeasure.measure_ofMeasure _ _ _ _ _ _ y

variable (L) in
/-- **Diagonal measures**: the matrix coefficient `⟪y, U v y⟫` is the Fourier transform
`∫ exp (i L(p, v)) dE_y(p)` of the diagonal measure `E_y` of `E_U`. -/
lemma inner_apply_eq_integral_measure_pvm (v : V) (y : H) :
    ⟪y, U v y⟫_ℂ = ∫ p, cexp (L p v * I) ∂((U.pvm L).measure y) := by
  rw [U.measure_pvm, U.integral_bochner]

variable (L) in
/-- **SNAG theorem**, existence: a strongly continuous unitary representation is the Fourier
transform of its projection-valued measure, `U v = ∫ exp (i L(p, v)) dE_U(p)`. -/
lemma fourier_pvm : (U.pvm L).fourierOfIsContPerfPair L = U := by
  refine ContinuousAddChar.ext fun v => UnitarySOT.ext <| ContinuousLinearMap.ext_inner_self
    fun y => ?_
  rw [ProjectionValuedMeasure.fourierOfIsContPerfPair_apply,
    ProjectionValuedMeasure.inner_fourier_apply_self,
    U.inner_apply_eq_integral_measure_pvm L]

/-- **SNAG theorem**, uniqueness: `E_U` is the only projection-valued measure on `W` whose Fourier
transform along `L` is `U`. The diagonal measures of such a measure have the Fourier transforms
`v ↦ ⟪y, U v y⟫`, hence are those of `E_U`. -/
lemma eq_pvm_of_fourier_eq {E : ProjectionValuedMeasure W H}
    (hE : E.fourierOfIsContPerfPair L = U) : E = U.pvm L := by
  refine E.ext_of_measure fun y => Measure.ext_of_integral_cexp_eq (L := L) fun v => ?_
  rw [← E.inner_fourier_apply_self L L.measurable_flip_apply_of_isContPerfPair v y,
    ← E.fourierOfIsContPerfPair_apply L, hE]
  exact U.inner_apply_eq_integral_measure_pvm L v y

variable (L) in
/-- **SNAG theorem** (Stone–Naimark–Ambrose–Godement): a strongly continuous unitary representation
`U` of a finite-dimensional real vector space `V` is the Fourier transform
`U v = ∫ exp (i L(p, v)) dE(p)` of a unique projection-valued measure `E` on `W`, for a continuous
perfect pairing `L` of `W` with `V`. -/
theorem existsUnique_fourier_eq :
    ∃! E : ProjectionValuedMeasure W H, E.fourierOfIsContPerfPair L = U :=
  ⟨U.pvm L, U.fourier_pvm L, fun _ hE => U.eq_pvm_of_fourier_eq hE⟩

variable (L) in
/-- The projection-valued measure of the trivial representation is the Dirac measure at `0`. -/
lemma pvm_one :
    (1 : UnitaryAddRepresentation V H).pvm L = ProjectionValuedMeasure.dirac H 0 := by
  refine ((1 : UnitaryAddRepresentation V H).eq_pvm_of_fourier_eq
    (ContinuousAddChar.ext fun v => UnitarySOT.ext ?_)).symm
  rw [ProjectionValuedMeasure.fourierOfIsContPerfPair_apply,
    ProjectionValuedMeasure.coe_fourier_apply,
    ProjectionValuedMeasure.integral_dirac (ProjectionValuedMeasure.measurable_exp_pairing L
      L.measurable_flip_apply_of_isContPerfPair v) ⟨1, fun _ => (norm_exp_ofReal_mul_I _).le⟩]
  simp

end UnitaryAddRepresentation

/-! ### The dual space -/

namespace UnitaryAddRepresentation

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] [MeasurableSpace (StrongDual ℝ V)]
  [BorelSpace (StrongDual ℝ V)] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **SNAG theorem** with the projection-valued measure on the dual space: a strongly continuous
unitary representation `U` of a finite-dimensional real vector space `V` is
`U v = ∫ exp (i L(p, v)) dE(p)` for a unique projection-valued measure `E` on `StrongDual ℝ V`. This is
the case `L = topDualPairing ℝ V` of `UnitaryAddRepresentation.existsUnique_fourier_eq`. -/
theorem existsUnique_fourier_eq_strongDual (U : UnitaryAddRepresentation V H) :
    ∃! E : ProjectionValuedMeasure (StrongDual ℝ V) H,
      E.fourierOfIsContPerfPair (topDualPairing ℝ V) = U :=
  U.existsUnique_fourier_eq (topDualPairing ℝ V)

end UnitaryAddRepresentation

/-! ### Functoriality -/

namespace UnitaryAddRepresentation

variable {V W V' W' : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] {L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ}
  [L.IsContPerfPair] [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V']
  [IsTopologicalAddGroup V'] [ContinuousSMul ℝ V'] [FiniteDimensional ℝ V']
  [AddCommGroup W'] [Module ℝ W'] [TopologicalSpace W'] [IsTopologicalAddGroup W']
  [ContinuousSMul ℝ W'] [MeasurableSpace W'] [BorelSpace W'] {L' : W' →ₗ[ℝ] V' →ₗ[ℝ] ℝ}
  [L'.IsContPerfPair] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (U : UnitaryAddRepresentation V H)

/-- **Functoriality** of the projection-valued measure: if `φ : V' → V` and `ψ : W → W'` are
adjoint for the pairings, `L'(ψ w, v') = L(w, φ v')`, then the projection-valued measure of the
pullback `U ∘ φ` is the image `ψ_* E_U` of that of `U`. (The adjoint `ψ` of `φ` is unique, the
transpose of `φ`.) -/
lemma pvm_compContinuousAddMonoidHom (φ : V' →L[ℝ] V) (ψ : W →L[ℝ] W')
    (hφψ : ∀ w v', L' (ψ w) v' = L w (φ v')) :
    pvm L' (U.compContinuousAddMonoidHom (φ : V' →ₜ+ V)) =
      (U.pvm L).map ψ ψ.continuous.measurable := by
  refine (eq_pvm_of_fourier_eq (U.compContinuousAddMonoidHom (φ : V' →ₜ+ V)) ?_).symm
  refine ContinuousAddChar.ext fun v' => UnitarySOT.ext ?_
  rw [ProjectionValuedMeasure.fourierOfIsContPerfPair_apply,
    ProjectionValuedMeasure.coe_fourier_apply,
    ProjectionValuedMeasure.integral_map (ProjectionValuedMeasure.measurable_exp_pairing L'
      L'.measurable_flip_apply_of_isContPerfPair v') ⟨1, fun _ => (norm_exp_ofReal_mul_I _).le⟩
      ψ.continuous.measurable]
  have h : ((fun w' => cexp (L' w' v' * I)) ∘ ψ) = fun w => cexp (L w (φ v') * I) := by
    ext w
    simp [hφψ]
  rw [h, ← ProjectionValuedMeasure.coe_fourier_apply _ _ L.measurable_flip_apply_of_isContPerfPair,
    ← ProjectionValuedMeasure.fourierOfIsContPerfPair_apply, U.fourier_pvm L]
  rfl

variable [T2Space V] [T2Space V'] [MeasurableSpace (StrongDual ℝ V)]
  [BorelSpace (StrongDual ℝ V)] [MeasurableSpace (StrongDual ℝ V')] [BorelSpace (StrongDual ℝ V')]

/-- **Functoriality** on the dual spaces: the projection-valued measure of `U ∘ φ` on
`StrongDual ℝ V'` is the image of that of `U` under the transpose `p ↦ p ∘ φ`. -/
lemma pvm_compContinuousAddMonoidHom_strongDual (φ : V' →L[ℝ] V) :
    pvm (topDualPairing ℝ V') (U.compContinuousAddMonoidHom (φ : V' →ₜ+ V)) =
      (U.pvm (topDualPairing ℝ V)).map (fun p => p.comp φ)
        (ContinuousLinearMap.precomp ℝ φ).continuous.measurable :=
  U.pvm_compContinuousAddMonoidHom φ (ContinuousLinearMap.precomp ℝ φ) fun _ _ => rfl

end UnitaryAddRepresentation

/-! ### The converse -/

namespace MeasureTheory.ProjectionValuedMeasure

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] (L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  [L.IsContPerfPair] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : ProjectionValuedMeasure W H)

/-- **SNAG theorem**, converse: a projection-valued measure `E` on `W` is the projection-valued
measure of its Fourier transform along `L`. With `UnitaryAddRepresentation.fourier_pvm`,
`E ↦ E.fourierOfIsContPerfPair L` is a bijection from the projection-valued measures on `W` onto
the strongly continuous unitary representations of `V`. -/
lemma pvm_fourier : (E.fourierOfIsContPerfPair L).pvm L = E :=
  ((E.fourierOfIsContPerfPair L).eq_pvm_of_fourier_eq rfl).symm

end MeasureTheory.ProjectionValuedMeasure
