/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.Power

/-!
# Polar decomposition

Let `T : E → F` be a closed, densely defined `σ`-semilinear operator between complex Hilbert
spaces, `σ` the identity or the complex conjugation (`T : E →ₛₗ.[σ] F`, with adjoint
`T† = LinearPMap.adjointₛₗ T`), and let `A` be a self-adjoint operator with `A = T†T`; the
composite `T†T` (`LinearPMap.compNat`) is complex-linear. The operator `|T| = A^{1/2}`
(`IsSelfAdjoint.sqrt`) has the same domain as `T` and `‖|T| x‖ = ‖T x‖`
(`IsSelfAdjoint.domain_sqrt_eq_domain`, `IsSelfAdjoint.norm_eq_of_mem_graph_sqrt`): both are
closed, `dom A` is a core for both (von Neumann's theorem and the spectral cutoffs), and on `dom A`
the identity is `‖|T| x‖² = ⟪x, A x⟫ = ‖T x‖²`. The **polar decomposition** `T = U |T|`
(`IsSelfAdjoint.eq_polarIsometry_compPMap`) has the `σ`-semilinear partial isometry
`U x = lim T (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A(λ)) x` (`IsSelfAdjoint.polarIsometry`), isometric on
`E_A((0, ∞)) E` and zero on `ker T`. The decomposition is unique
(`IsSelfAdjoint.eq_sqrt_of_eq_compPMap`, `IsSelfAdjoint.eq_polarIsometry_of_eq_compPMap`): `T = V B`
with `B` positive self-adjoint and `V` isometric on the range of `B` forces `B B = A` and
`B = A^{1/2}`, and if moreover `V` vanishes on `ker B`, then `V = U`. Letting `σ` vary treats
complex-linear and conjugate-linear operators at once.

If `T` is injective with dense range, then `A = T†T` is injective, `E_A((0, ∞)) = 1`, and `U` is a
`σ`-semilinear isometric equivalence of `E` onto `F` (`IsSelfAdjoint.polarIsometryEquiv`): it is
isometric, and its range is closed and contains the range of `T`. A `σ`-semilinear closed
**involution** `S` (`S x = v` iff `S v = x`), such as the Tomita operator of a standard subspace,
is injective with dense range (its range is its domain), so `U = J` is an isometric equivalence,
and uniqueness applied to
`S = S⁻¹ = J⁻¹ (J Δ^{-1/2} J⁻¹)` gives `J² = 1` and `J Δ^{1/2} J = Δ^{-1/2}`; in spectral form
`J E_Δ J = inv_* E_Δ`, so `J f(Δ) J = (σ ∘ f ∘ inv)(Δ)`, for instance `J Δ^{it} J = Δ^{it}`.

For a bounded operator `x`, `T = x.toPMap ⊤` is closed and `T†T = (x⋆ x).toPMap ⊤`, and the
construction here agrees with the bounded one of the continuous functional calculus: `|T|` is
`CFC.abs x` and `U` is the partial isometry of `x = v |x|` with source projection the range
projection `R(x⋆)` (`ContinuousLinearMap.sqrt_eq_toPMap_cfcAbs`,
`ContinuousLinearMap.polarIsometry_eq_of_eq_mul_cfcAbs`, in
`QuantumSystem.Analysis.SpectralTheory.PolarDecomposition.CFCAbs`). For bounded operators the
project uses `CFC.abs`.

## Notation

* `U†` — for a bounded `σ`-semilinear `U : E →SL[σ] F`, its adjoint
  `ContinuousLinearMap.adjointₛₗ U`, with `⟪U† y, x⟫ = σ ⟪y, U x⟫`; for a conjugate-linear `U`
  this is the antilinear adjoint `⟪U† y, x⟫ = conj ⟪y, U x⟫` of the literature.
* `𝐉` — in the section on involutions, the isometric part `J` of `S = J |S|`; the notation is local,
  so the statements display `hA.polarIsometryEquiv hAS hS _ _` elsewhere.

## Main definitions

* `IsSelfAdjoint.polarIsometry hA hAT hT` — the partial isometry `U` of `T = U |T|`, a bounded
  `σ`-semilinear operator.
* `IsSelfAdjoint.polarIsometryEquiv` — for an injective `T` with dense range, the isometric part
  `U` as a semilinear isometric equivalence.

## Main results

* `LinearPMap.exists_mem_graphₛₗ_norm_eq_of_mem_closure`, `LinearPMap.HasCore.mem_closure` —
  closed operators isometric to each other on a common core.
* `IsSelfAdjoint.domain_le_domain_sqrt_of_eq_adjointₛₗ_compNat` — `dom T ⊆ dom A^{1/2}` for any `T`
  with `A = T†T`.
* `IsSelfAdjoint.domain_sqrt_eq_domain`, `IsSelfAdjoint.norm_eq_of_mem_graph_sqrt` —
  `dom |T| = dom T` and `‖|T| x‖ = ‖T x‖`.
* `IsSelfAdjoint.norm_polarIsometry_apply` — `‖U x‖ = ‖E_A((0, ∞)) x‖`.
* `IsSelfAdjoint.eq_polarIsometry_compPMap` — **polar decomposition** `T = U |T|`.
* `IsSelfAdjoint.pvm_compPMap_sqrt_le`, `IsSelfAdjoint.pvm_Ioi_compPMap_sqrt` —
  `E_A(s) A^{1/2} ⊆ A^{1/2} E_A(s)` and `E_A((0, ∞)) A^{1/2} = A^{1/2}`.
* `IsSelfAdjoint.eq_sqrt_of_eq_compPMap`, `IsSelfAdjoint.eq_polarIsometry_of_eq_compPMap` —
  **uniqueness** of the polar decomposition.
* `IsSelfAdjoint.adjointₛₗ_polarIsometry_compPMap` — `|T| = U† T`.
* `IsSelfAdjoint.adjointₛₗ_polarIsometry_apply_polarIsometry`,
  `IsSelfAdjoint.inner_polarIsometry_apply`, `IsSelfAdjoint.adjointₛₗ_polarIsometry_apply_eq_zero`,
  `IsSelfAdjoint.isClosed_range_polarIsometry`,
  `IsSelfAdjoint.polarIsometry_apply_mem_closure_range` — `U` is a partial isometry:
  `U† U = E_A((0, ∞))`, `⟪U x, U y⟫ = σ ⟪E_A((0, ∞)) x, E_A((0, ∞)) y⟫`, `U†` vanishes on
  `(ran U)ᗮ`, and `ran U` is the closure of `ran T`.
* `IsSelfAdjoint.pvm_Ioi_apply_eq_self`, `IsSelfAdjoint.ker_le_ker_pvm_Ioi` —
  `E_A((0, ∞)) E = (ker T)ᗮ`.
* `IsSelfAdjoint.lintegral_measure_pvm_eq_norm_sq` — the **form identity** `∫ λ dμ_x = ‖T x‖²`.
* `IsSelfAdjoint.ker_eq_of_eq_adjointₛₗ_compNat`,
  `IsSelfAdjoint.ker_eq_bot_iff_of_eq_adjointₛₗ_compNat` — `ker T†T = ker T`.
* `IsSelfAdjoint.pvm_Ioi_eq_one_of_ker_eq_bot`, `IsSelfAdjoint.norm_polarIsometry_of_ker_eq_bot`,
  `IsSelfAdjoint.surjective_polarIsometry_of_dense_range` — for an injective `T`,
  `E_A((0, ∞)) = 1` and `U` is an isometry, onto `F` if `T` has dense range.
* `LinearPMap.ker_eq_bot_of_involution`, `LinearPMap.dense_range_of_involution` — a densely
  defined involution is injective with dense range.
* `IsSelfAdjoint.polarIsometryEquiv_apply_apply`, `IsSelfAdjoint.polarIsometryEquiv_symm_apply` —
  `J² = 1`.
* `IsSelfAdjoint.sqrt_compNat_polarIsometryEquiv` — `Δ^{1/2} J = J Δ^{-1/2}`, i.e.
  `J Δ^{1/2} J = Δ^{-1/2}` (`LinearPMap.inverse`).
* `IsSelfAdjoint.pvm_transport_polarIsometryEquiv`, `IsSelfAdjoint.polarIsometryEquiv_integral_apply`
  — `J E_Δ J = inv_* E_Δ` and `J f(Δ) J = (σ ∘ f ∘ inv)(Δ)`.

## References

* [K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*][schmudgen2012], §7.1
* [O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*][bratteli1987],
  Proposition 2.5.11
-/

@[expose] public section

open Set Filter Topology MeasureTheory Complex
open scoped InnerProductSpace InnerProduct ComplexConjugate LinearPMap

/-! ### Closed operators isometric on a common core -/

namespace LinearPMap

variable {R R₁ R₂ : Type*} [Ring R] [Ring R₁] [Ring R₂] {σ₁ : R →+* R₁} {σ₂ : R →+* R₂}
  {E F₁ F₂ : Type*} [NormedAddCommGroup E] [Module R E]
  [NormedAddCommGroup F₁] [Module R₁ F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [Module R₂ F₂]

/-- Let `S` be closed, `D` a subspace of its domain on which `‖S x‖ = ‖T x‖`, and `(x, v)` a limit
of points `(d, T d)` with `d ∈ D`. Then `x ∈ dom S` and `‖S x‖ = ‖v‖`. -/
lemma exists_mem_graphₛₗ_norm_eq_of_mem_closure {S : E →ₛₗ.[σ₁] F₁} {T : E →ₛₗ.[σ₂] F₂}
    {D : Submodule R E} (hS : S.IsClosedₛₗ) (hDS : D ≤ S.domain)
    (hnorm : ∀ d ∈ D, ∀ u w, (d, u) ∈ S.graphₛₗ → (d, w) ∈ T.graphₛₗ → ‖u‖ = ‖w‖)
    {x : E} {v : F₂} (hxv : (x, v) ∈ _root_.closure {p : E × F₂ | p.1 ∈ D ∧ p ∈ T.graphₛₗ}) :
    ∃ u, (x, u) ∈ S.graphₛₗ ∧ ‖u‖ = ‖v‖ := by
  obtain ⟨p, hp, hpt⟩ := mem_closure_iff_seq_limit.mp hxv
  choose hpD hpT using hp
  set u : ℕ → F₁ := fun n => S ⟨(p n).1, hDS (hpD n)⟩
  have hu : ∀ n, ((p n).1, u n) ∈ S.graphₛₗ := fun n => S.mem_graphₛₗ ⟨_, hDS (hpD n)⟩
  have hdist : ∀ m n, dist (u m) (u n) = dist (p m).2 (p n).2 := fun m n => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hnorm _ (D.sub_mem (hpD m) (hpD n)) _ _ (S.graphₛₗ.sub_mem (hu m) (hu n))
      (T.graphₛₗ.sub_mem (hpT m) (hpT n))
  have hp2 : Tendsto (fun n => (p n).2) atTop (𝓝 v) := (continuous_snd.tendsto _).comp hpt
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hp2.cauchySeq ε hε
    exact ⟨N, fun m hm n hn => by rw [hdist]; exact hN m hm n hn⟩
  obtain ⟨u₀, hu₀⟩ := cauchySeq_tendsto_of_complete hcau
  have hmem : (x, u₀) ∈ S.graphₛₗ := by
    refine (_root_.IsClosed.closure_eq hS).subset ?_
    exact mem_closure_of_tendsto (((continuous_fst.tendsto _).comp hpt).prodMk_nhds hu₀)
      (Eventually.of_forall hu)
  refine ⟨u₀, hmem, tendsto_nhds_unique hu₀.norm ?_⟩
  have : (fun n => ‖u n‖) = fun n => ‖(p n).2‖ :=
    funext fun n => hnorm _ (hpD n) _ _ (hu n) (hpT n)
  rw [this]
  exact hp2.norm

section Core

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F] [ContinuousAdd E] [ContinuousAdd F]
  [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- A point of the graph of `f` is a limit of points of the graph over a core. -/
lemma HasCore.mem_closure {f : E →ₗ.[R] F} {D : Submodule R E} (h : f.HasCore D)
    {p : E × F} (hp : p ∈ f.graph) :
    p ∈ _root_.closure {q : E × F | q.1 ∈ D ∧ q ∈ f.graph} := by
  have hsub : ((f.domRestrict D).graph : Set (E × F)) ⊆ {q : E × F | q.1 ∈ D ∧ q ∈ f.graph} :=
    fun q hq => by
      obtain ⟨q₁, q₂⟩ := q
      exact mem_graph_domRestrict.mp hq
  rw [← h.closure_eq] at hp
  by_cases hc : (f.domRestrict D).IsClosable
  · rw [← hc.graph_closure_eq_closure_graph] at hp
    exact closure_mono hsub hp
  · rw [closure_def' hc] at hp
    exact subset_closure (hsub hp)

end Core

end LinearPMap

/-! ### The square root of `T†T` -/

namespace IsSelfAdjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ]
  {T : E →ₛₗ.[σ] F}

/-- `∫ λ² dμ_y < ∞` forces `∫ |√λ|² dμ_y < ∞`. -/
lemma memLp_sqrt_of_memLp {y : E} (h : MemLp (fun t : ℝ => (t : ℂ)) 2 (hA.pvm.measure y)) :
    MemLp (fun t : ℝ => (Real.sqrt t : ℂ)) 2 (hA.pvm.measure y) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (Real.sqrt t : ℂ)) (hA.pvm.measure y) :=
    (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ((h.integrable one_le_two).norm.mono'
    (by fun_prop) (Eventually.of_forall fun t => ?_))
  rcases le_total 0 t with ht | ht
  · simp [Real.sq_sqrt ht, abs_of_nonneg ht]
  · simp [Real.sqrt_eq_zero_of_nonpos ht]

include hA in
/-- The domain of `A` lies in that of `A^{1/2}`. -/
lemma domain_le_domain_sqrt : A.domain ≤ hA.sqrt.domain := fun _ hy =>
  hA.memLp_sqrt_of_memLp ((hA.mem_domain_iff_memLp).mp hy)

include hA in
/-- For positive `A`, the spectral cutoffs `E_A {‖√λ‖ ≤ n} y` lie in the domain of `A`. -/
lemma mem_domain_apply_cutoff_sqrt (hpos : A.IsPositive) (n : ℕ) (y : E) :
    hA.pvm {t : ℝ | ‖(Real.sqrt t : ℂ)‖ ≤ n} y ∈ A.domain := by
  have hs : MeasurableSet {t : ℝ | ‖(Real.sqrt t : ℂ)‖ ≤ n} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [hA.mem_domain_iff_memLp, ProjectionValuedMeasure.measure_apply_eq_restrict hs]
  refine MemLp.of_bound (by fun_prop) ((n : ℝ) ^ 2) ?_
  rw [ae_restrict_iff' hs]
  filter_upwards [hA.ae_nonneg_measure_pvm y hpos] with t ht hts
  have hts' : Real.sqrt t ≤ n := by
    simpa [abs_of_nonneg (Real.sqrt_nonneg t)] using hts
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]

include hA in
/-- For positive `A`, the domain of `A` is a core for `A^{1/2}`. -/
lemma hasCore_sqrt (hpos : A.IsPositive) : hA.sqrt.HasCore A.domain :=
  hA.pvm.hasCore_integralPMap (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)
    hA.domain_le_domain_sqrt (hA.mem_domain_apply_cutoff_sqrt hpos)

variable (hAT : A = T.adjointₛₗ.compNat T)
include hAT

omit [CompleteSpace F] in
include hA in
/-- For `A = T†T` and `x ∈ dom A`, `‖A^{1/2} x‖ = ‖T x‖` (in graph form). -/
lemma norm_eq_of_mem_graph_sqrt_of_mem_domain {x : E} (hx : x ∈ A.domain) {u : E} {v : F}
    (hu : (x, u) ∈ hA.sqrt.graph) (hv : (x, v) ∈ T.graphₛₗ) : ‖u‖ = ‖v‖ := by
  have hpos := hA.isPositive_of_eq_adjointₛₗ_compNat hAT
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  obtain ⟨hux, rfl⟩ := (hA.pvm.mem_graph_integralPMap).mp hu
  have hAx := A.mem_graph ⟨x, hx⟩
  have h₁ := hA.re_inner_eq_norm_sq_of_eq_adjointₛₗ_compNat hAT hAx hv
  rw [hA.inner_eq_integral_of_mem_graph hAx, integral_complex_ofReal, ofReal_re] at h₁
  have h₂ := hA.pvm.norm_integralApply_sq hsq hux
  have h₃ : ∫ t, ‖(Real.sqrt t : ℂ)‖ ^ 2 ∂(hA.pvm.measure x) = ∫ t, t ∂(hA.pvm.measure x) :=
    integral_congr_ae ((hA.ae_nonneg_measure_pvm x hpos).mono fun t ht => by
      simp [Real.sq_sqrt ht])
  rw [h₃, h₁] at h₂
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h₂

omit [CompleteSpace F] in
/-- For `A = T†T`, the domain of `A` lies in that of `T`. -/
lemma domain_le_domain_of_eq_adjointₛₗ_compNat : A.domain ≤ T.domain :=
  hAT ▸ LinearPMap.compNat_domain_le

omit [CompleteSpace F] in
include hA in
/-- **`dom T ⊆ dom |T|`**: for `A = T†T`, the domain of `T` lies in that of `A^{1/2}`, the form
domain of `A`, by the form bound `∫ λ dμ_x ≤ ‖T x‖²`
(`IsSelfAdjoint.lintegral_measure_pvm_le_norm_sq`). -/
lemma domain_le_domain_sqrt_of_eq_adjointₛₗ_compNat : T.domain ≤ hA.sqrt.domain := by
  intro x hx
  have hle := hA.lintegral_measure_pvm_le_norm_sq hAT (T.mem_graphₛₗ ⟨x, hx⟩)
  change MemLp (fun t : ℝ => (Real.sqrt t : ℂ)) 2 (hA.pvm.measure x)
  refine (memLp_two_iff_integrable_sq_norm (by fun_prop : Measurable _).aestronglyMeasurable).mpr
    ⟨(by fun_prop : Measurable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => by positivity)]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun t => ?_)) (hle.trans_lt ENNReal.ofReal_lt_top)
  rcases le_total 0 t with ht | ht
  · simp [Real.sq_sqrt ht]
  · simp [Real.sqrt_eq_zero'.mpr ht, ENNReal.ofReal_of_nonpos ht]

include hA in
/-- `dom |T| = dom T`, pointwise. -/
private lemma exists_mem_graph_sqrt_iff (hT : T.IsClosedₛₗ) {x : E} :
    (∃ u, (x, u) ∈ hA.sqrt.graph) ↔ ∃ v, (x, v) ∈ T.graphₛₗ := by
  have hpos := hA.isPositive_of_eq_adjointₛₗ_compNat hAT
  have hDT := domain_le_domain_of_eq_adjointₛₗ_compNat hAT
  have hTd : Dense (T.domain : Set E) := hA.dense_domain.mono hDT
  have hS : hA.sqrt.IsClosedₛₗ := LinearPMap.isClosedₛₗ_iff_isClosed.mpr hA.isSelfAdjoint_sqrt.isClosed
  have hnorm : ∀ d ∈ A.domain, ∀ u w, (d, u) ∈ hA.sqrt.graphₛₗ → (d, w) ∈ T.graphₛₗ → ‖u‖ = ‖w‖ :=
    fun d hd u w hu hw => hA.norm_eq_of_mem_graph_sqrt_of_mem_domain hAT hd
      (LinearPMap.mem_graphₛₗ_iff_mem_graph.mp hu) hw
  constructor
  · rintro ⟨u, hu⟩
    have hcl := (hA.hasCore_sqrt hpos).mem_closure hu
    simp_rw [← LinearPMap.mem_graphₛₗ_iff_mem_graph] at hcl
    obtain ⟨v, hv, -⟩ := LinearPMap.exists_mem_graphₛₗ_norm_eq_of_mem_closure hT hDT
      (fun d hd w u hw hu => (hnorm d hd u w hu hw).symm) hcl
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    have hcl := LinearPMap.mem_closure_graphₛₗ_adjointₛₗ_compNat_self hT hTd hv
    rw [← hAT] at hcl
    obtain ⟨u, hu, -⟩ := LinearPMap.exists_mem_graphₛₗ_norm_eq_of_mem_closure hS
      (fun d hd => hA.domain_le_domain_sqrt hd) hnorm hcl
    exact ⟨u, LinearPMap.mem_graphₛₗ_iff_mem_graph.mp hu⟩

include hA in
/-- **`dom |T| = dom T`**: for `A = T†T` with `T` closed, the domain of `A^{1/2}` is that of `T`;
`‖A^{1/2} x‖ = ‖T x‖` there (`IsSelfAdjoint.norm_eq_of_mem_graph_sqrt`). -/
lemma domain_sqrt_eq_domain (hT : T.IsClosedₛₗ) : hA.sqrt.domain = T.domain :=
  le_antisymm (fun _ hx => LinearPMap.mem_domain_iff_exists_mem_graphₛₗ.mpr
      ((hA.exists_mem_graph_sqrt_iff hAT hT).mp (LinearPMap.mem_domain_iff.mp hx)))
    (hA.domain_le_domain_sqrt_of_eq_adjointₛₗ_compNat hAT)

include hA in
/-- **`‖|T| x‖ = ‖T x‖`**: for `A = T†T` with `T` closed, `‖A^{1/2} x‖ = ‖T x‖` (on graph points). -/
lemma norm_eq_of_mem_graph_sqrt (hT : T.IsClosedₛₗ) {x u : E} {v : F}
    (hu : (x, u) ∈ hA.sqrt.graph) (hv : (x, v) ∈ T.graphₛₗ) : ‖u‖ = ‖v‖ := by
  have hDT := domain_le_domain_of_eq_adjointₛₗ_compNat hAT
  have hTd : Dense (T.domain : Set E) := hA.dense_domain.mono hDT
  have hS : hA.sqrt.IsClosedₛₗ := LinearPMap.isClosedₛₗ_iff_isClosed.mpr hA.isSelfAdjoint_sqrt.isClosed
  have hcl := LinearPMap.mem_closure_graphₛₗ_adjointₛₗ_compNat_self hT hTd hv
  rw [← hAT] at hcl
  obtain ⟨u', hu', hnorm⟩ := LinearPMap.exists_mem_graphₛₗ_norm_eq_of_mem_closure hS
    (fun d hd => hA.domain_le_domain_sqrt hd)
    (fun d hd u w hu hw => hA.norm_eq_of_mem_graph_sqrt_of_mem_domain hAT hd
      (LinearPMap.mem_graphₛₗ_iff_mem_graph.mp hu) hw) hcl
  have huu : u' = u := hA.sqrt.mem_graph_snd_inj (LinearPMap.mem_graphₛₗ_iff_mem_graph.mp hu') hu rfl
  rwa [huu] at hnorm

include hA in
/-- **Form identity**: for `A = T†T` with `T` closed and `u ∈ dom T`, `∫ λ dμ_u(λ) = ‖T u‖²`; the
inequality `≤` holds without closedness (`IsSelfAdjoint.lintegral_measure_pvm_le_norm_sq`). -/
lemma lintegral_measure_pvm_eq_norm_sq (hT : T.IsClosedₛₗ) {u : E} {u' : F}
    (hu : (u, u') ∈ T.graphₛₗ) :
    ∫⁻ s, ENNReal.ofReal s ∂(hA.pvm.measure u) = ENNReal.ofReal (‖u'‖ ^ 2) := by
  have hpos := hA.isPositive_of_eq_adjointₛₗ_compNat hAT
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  obtain ⟨w, hw⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mpr ⟨u', hu⟩
  have hnorm := hA.norm_eq_of_mem_graph_sqrt hAT hT hw hu
  rw [sqrt, ProjectionValuedMeasure.sqrt] at hw
  obtain ⟨hwx, rfl⟩ := hA.pvm.mem_graph_integralPMap.mp hw
  rw [← hnorm, hA.pvm.norm_integralApply_sq hsq hwx,
    ofReal_integral_eq_lintegral_ofReal (hwx.integrable_norm_pow two_ne_zero)
      (Eventually.of_forall fun t => by positivity)]
  refine lintegral_congr_ae ((hA.ae_nonneg_measure_pvm u hpos).mono fun t ht => ?_)
  simp [Real.sq_sqrt ht]

omit hAT in
/-- `E_A(s_n) y → E_A((0, ∞)) y` for the sets `s_n = (1/(n+1), ∞)`. -/
lemma tendsto_pvm_Ioi_inv (y : E) :
    Tendsto (fun n : ℕ => hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y) atTop (𝓝 (hA.pvm (Ioi 0) y)) := by
  have hmono : Monotone fun n : ℕ => Ioi ((n : ℝ) + 1)⁻¹ ∪ Iic 0 := fun m n hmn =>
    union_subset_union_left _ (Ioi_subset_Ioi (inv_anti₀ (by positivity) (by gcongr)))
  have hU : ⋃ n : ℕ, (Ioi ((n : ℝ) + 1)⁻¹ ∪ Iic 0) = univ := by
    refine eq_univ_of_forall fun t => ?_
    rcases le_or_gt t 0 with ht | ht
    · exact mem_iUnion.mpr ⟨0, Or.inr ht⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
      exact mem_iUnion.mpr ⟨n, Or.inl (by simpa [one_div] using hn)⟩
  have h := hA.pvm.tendsto_apply_of_monotone
    (fun n => measurableSet_Ioi.union measurableSet_Iic) hmono hU y
  have hsplit : ∀ n : ℕ, hA.pvm (Ioi ((n : ℝ) + 1)⁻¹ ∪ Iic 0) y =
      hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y + hA.pvm (Iic 0) y := fun n => by
    rw [hA.pvm.apply_union (Set.Iic_disjoint_Ioi (inv_pos.mpr (by positivity)).le).symm
      measurableSet_Ioi measurableSet_Iic, add_apply]
  have hy : hA.pvm (Ioi 0) y = y - hA.pvm (Iic 0) y := by
    rw [eq_sub_iff_add_eq, ← add_apply, ← hA.pvm.apply_union (Set.Iic_disjoint_Ioi le_rfl).symm
      measurableSet_Ioi measurableSet_Iic, Ioi_union_Iic, ProjectionValuedMeasure.apply_univ,
      one_apply_eq_self]
  simp_rw [hsplit] at h
  have h' := h.sub (tendsto_const_nhds (x := hA.pvm (Iic 0) y))
  simp only [add_sub_cancel_right] at h'
  rw [hy]
  exact h'

end IsSelfAdjoint

/-! ### The partial isometry -/

namespace IsSelfAdjoint

/-- The cutoffs `1_{λ > 1/(n+1)} λ^{-1/2}`, from which the partial isometry of a polar decomposition
is built (`IsSelfAdjoint.polarIsometry`). -/
noncomputable def polarCutoff (n : ℕ) : ℝ → ℂ :=
  (Ioi ((n : ℝ) + 1)⁻¹).indicator fun t => ((Real.sqrt t)⁻¹ : ℂ)

/-- The cutoffs are measurable. -/
lemma measurable_polarCutoff (n : ℕ) : Measurable (polarCutoff n) := by
  unfold polarCutoff
  exact Measurable.indicator (by fun_prop) measurableSet_Ioi

/-- The cutoffs are bounded: `|1_{λ > 1/(n+1)} λ^{-1/2}| ≤ √(n+1)`. -/
lemma norm_polarCutoff_le (n : ℕ) (t : ℝ) : ‖polarCutoff n t‖ ≤ Real.sqrt (n + 1) := by
  rw [polarCutoff, indicator]
  split_ifs with ht
  · have ht : ((n : ℝ) + 1)⁻¹ < t := ht
    have hpos : 0 < t := (inv_pos.mpr (by positivity)).trans ht
    have h1 : 1 < ((n : ℝ) + 1) * t := by
      have := mul_lt_mul_of_pos_left ht (by positivity : (0 : ℝ) < n + 1)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t),
      inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hpos), ← Real.sqrt_mul (by positivity),
      Real.one_le_sqrt]
    exact h1.le
  · simp

/-- `√λ · 1_{λ > 1/(n+1)} λ^{-1/2} = 1_{λ > 1/(n+1)}`. -/
lemma sqrt_mul_polarCutoff (n : ℕ) :
    (fun t : ℝ => (Real.sqrt t : ℂ)) * polarCutoff n = (Ioi ((n : ℝ) + 1)⁻¹).indicator 1 := by
  ext t
  simp only [Pi.mul_apply, polarCutoff, indicator]
  split_ifs with ht
  · have hpos : 0 < t := (inv_pos.mpr (by positivity)).trans ht
    rw [Pi.one_apply, mul_inv_cancel₀ (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne')]
  · rw [mul_zero]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {σ : ℂ →+* ℂ}

/-- The partial isometry `x ↦ lim T (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A(λ)) x` of the polar
decomposition of `T`, for `A = T†T`, as a function; `IsSelfAdjoint.polarIsometry` is the bounded
semilinear operator. -/
noncomputable def polarIsometryFun (T : E →ₛₗ.[σ] F) (x : E) : F :=
  limUnder atTop fun n : ℕ => Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x)

variable [RingHomInvPair σ σ] [RingHomIsometric σ] {T : E →ₛₗ.[σ] F}

/-- `A^{1/2} (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A) x = E_A((1/(n+1), ∞)) x`. -/
private lemma mem_graph_sqrt_integral_polarCutoff (n : ℕ) (x : E) :
    (hA.pvm.integral (polarCutoff n) x, hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) x) ∈ hA.sqrt.graph := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hb : ∀ t, ‖((Ioi ((n : ℝ) + 1)⁻¹).indicator (1 : ℝ → ℂ)) t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ioi ((n : ℝ) + 1)⁻¹ <;> simp [ht]
  have hmem : MemLp ((fun t : ℝ => (Real.sqrt t : ℂ)) * polarCutoff n) 2 (hA.pvm.measure x) := by
    rw [sqrt_mul_polarCutoff]
    exact hA.pvm.memLp_measure_of_bound (measurable_one.indicator measurableSet_Ioi) hb x
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.sqrt,
    ProjectionValuedMeasure.mem_graph_integralPMap]
  refine ⟨(hA.pvm.memLp_measure_integral_apply_iff hsq (measurable_polarCutoff n)
    ⟨_, norm_polarCutoff_le n⟩ x).mpr hmem, ?_⟩
  rw [hA.pvm.integralApply_integral_apply hsq (measurable_polarCutoff n) ⟨_, norm_polarCutoff_le n⟩
    hmem, sqrt_mul_polarCutoff, ← hA.pvm.integral_apply (measurable_one.indicator measurableSet_Ioi)
    ⟨1, hb⟩, hA.pvm.integral_indicator_one measurableSet_Ioi]

variable (hAT : A = T.adjointₛₗ.compNat T) (hT : T.IsClosedₛₗ)
include hAT hT

/-- The approximants `T (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A) x` of the partial isometry. -/
private lemma mem_graph_polarCutoff (n : ℕ) (x : E) :
    (hA.pvm.integral (polarCutoff n) x,
      Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x)) ∈ T.graphₛₗ := by
  obtain ⟨v, hv⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mp
    ⟨_, hA.mem_graph_sqrt_integral_polarCutoff n x⟩
  exact LinearPMap.mem_graphₛₗ_extend (LinearPMap.mem_domain_of_mem_graphₛₗ hv)

/-- The approximants of the partial isometry converge. -/
lemma tendsto_polarIsometryFun (x : E) :
    Tendsto (fun n : ℕ => Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x))
      atTop (𝓝 (hA.polarIsometryFun T x)) := by
  set w : ℕ → F := fun n => Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x)
  have hdist : ∀ m n, dist (w m) (w n) =
      dist (hA.pvm (Ioi ((m : ℝ) + 1)⁻¹) x) (hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) x) := fun m n => by
    rw [dist_eq_norm, dist_eq_norm]
    exact (hA.norm_eq_of_mem_graph_sqrt hAT hT
      (hA.sqrt.graph.sub_mem (hA.mem_graph_sqrt_integral_polarCutoff m x)
        (hA.mem_graph_sqrt_integral_polarCutoff n x))
      (T.graphₛₗ.sub_mem (hA.mem_graph_polarCutoff hAT hT m x)
        (hA.mem_graph_polarCutoff hAT hT n x))).symm
  have hcau : CauchySeq w := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hA.tendsto_pvm_Ioi_inv x).cauchySeq ε hε
    exact ⟨N, fun m hm n hn => by rw [hdist]; exact hN m hm n hn⟩
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hcau)

/-- `‖U x‖ = ‖E_A((0, ∞)) x‖`: the partial isometry is isometric on the closure of the range of
`|T|` and vanishes on `ker T`. -/
lemma norm_polarIsometryFun (x : E) :
    ‖hA.polarIsometryFun T x‖ = ‖hA.pvm (Ioi 0) x‖ := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT x).norm ?_
  have h : ∀ n : ℕ, ‖Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x)‖ =
      ‖hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) x‖ := fun n =>
    (hA.norm_eq_of_mem_graph_sqrt hAT hT (hA.mem_graph_sqrt_integral_polarCutoff n x)
      (hA.mem_graph_polarCutoff hAT hT n x)).symm
  simp_rw [h]
  exact (hA.tendsto_pvm_Ioi_inv x).norm

/-- The value of `T` on the approximating vectors is additive. -/
private lemma extend_polarCutoff_add (n : ℕ) (x y : E) :
    Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) (x + y)) =
      Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x) +
        Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) y) := by
  have h := T.graphₛₗ.add_mem (hA.mem_graph_polarCutoff hAT hT n x)
    (hA.mem_graph_polarCutoff hAT hT n y)
  rw [Prod.mk_add_mk, ← map_add] at h
  exact LinearPMap.mem_graphₛₗ_snd_inj (hA.mem_graph_polarCutoff hAT hT n (x + y)) h

/-- `U` is additive. -/
lemma polarIsometryFun_add (x y : E) :
    hA.polarIsometryFun T (x + y) = hA.polarIsometryFun T x + hA.polarIsometryFun T y := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT (x + y)) ?_
  simp_rw [hA.extend_polarCutoff_add hAT hT]
  exact (hA.tendsto_polarIsometryFun hAT hT x).add (hA.tendsto_polarIsometryFun hAT hT y)

/-- `U` is `σ`-semilinear: `U (c x) = σ c U x`. -/
lemma polarIsometryFun_smul (c : ℂ) (x : E) :
    hA.polarIsometryFun T (c • x) = σ c • hA.polarIsometryFun T x := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT (c • x)) ?_
  have h : ∀ n : ℕ, Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) (c • x)) =
      σ c • Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x) := fun n => by
    have h := LinearPMap.smul_mem_graphₛₗ c (hA.mem_graph_polarCutoff hAT hT n x)
    rw [← map_smul] at h
    exact LinearPMap.mem_graphₛₗ_snd_inj (hA.mem_graph_polarCutoff hAT hT n (c • x)) h
  simp_rw [h]
  exact (hA.tendsto_polarIsometryFun hAT hT x).const_smul (σ c)

/-- The **partial isometry** `U` of the polar decomposition `T = U |T|`, for `A = T†T` and `T`
closed: a bounded `σ`-semilinear operator, isometric on `E_A((0, ∞)) E` and zero on `ker T`
(`IsSelfAdjoint.norm_polarIsometry_apply`). -/
noncomputable def polarIsometry : E →SL[σ] F :=
  LinearMap.mkContinuous
    { toFun := hA.polarIsometryFun T
      map_add' := hA.polarIsometryFun_add hAT hT
      map_smul' := hA.polarIsometryFun_smul hAT hT }
    1 fun x => by
      change ‖hA.polarIsometryFun T x‖ ≤ 1 * ‖x‖
      rw [one_mul, hA.norm_polarIsometryFun hAT hT]
      exact hA.pvm.norm_apply_le _ x

/-- `U` is the function `polarIsometryFun`. -/
lemma polarIsometry_apply (x : E) : hA.polarIsometry hAT hT x = hA.polarIsometryFun T x := rfl

/-- `‖U x‖ = ‖E_A((0, ∞)) x‖`. -/
lemma norm_polarIsometry_apply (x : E) :
    ‖hA.polarIsometry hAT hT x‖ = ‖hA.pvm (Ioi 0) x‖ :=
  hA.norm_polarIsometryFun hAT hT x

/-! ### The polar decomposition -/

omit hAT hT in
/-- `E_A(s)` commutes with `A^{1/2}`, pointwise. -/
private lemma mem_graph_sqrt_apply {y u : E} (hu : (y, u) ∈ hA.sqrt.graph) {s : Set ℝ}
    (hs : MeasurableSet s) : (hA.pvm s y, hA.pvm s u) ∈ hA.sqrt.graph := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have h1 : Measurable (s.indicator (1 : ℝ → ℂ)) := measurable_one.indicator hs
  have h1b : ∀ t, ‖s.indicator (1 : ℝ → ℂ) t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ s <;> simp [ht]
  have hmul : (fun t : ℝ => (Real.sqrt t : ℂ)) * s.indicator 1 =
      s.indicator fun t : ℝ => (Real.sqrt t : ℂ) := by
    ext t
    by_cases ht : t ∈ s <;> simp [ht]
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.sqrt,
    ProjectionValuedMeasure.mem_graph_integralPMap] at hu ⊢
  obtain ⟨hy, rfl⟩ := hu
  have hmem : MemLp ((fun t : ℝ => (Real.sqrt t : ℂ)) * s.indicator 1) 2 (hA.pvm.measure y) := by
    rw [hmul]
    exact hy.indicator hs
  rw [← hA.pvm.integral_indicator_one hs]
  refine ⟨(hA.pvm.memLp_measure_integral_apply_iff hsq h1 ⟨1, h1b⟩ y).mpr hmem, ?_⟩
  rw [hA.pvm.integralApply_integral_apply hsq h1 ⟨1, h1b⟩ hmem, hmul,
    hA.pvm.integral_indicator_one hs, hA.pvm.apply_integralApply hsq hs hy]

omit hAT hT in
/-- **`E_A(s)` commutes with `A^{1/2}`**: `E_A(s) A^{1/2} ⊆ A^{1/2} E_A(s)`. -/
lemma pvm_compPMap_sqrt_le {s : Set ℝ} (hs : MeasurableSet s) :
    ((hA.pvm s : E →L[ℂ] E) : E →ₗ[ℂ] E).compPMap hA.sqrt ≤
      hA.sqrt.compNat (((hA.pvm s : E →L[ℂ] E) : E →ₗ[ℂ] E).toPMap ⊤) :=
  -- a computation of spectral integrals at each vector
  LinearPMap.compPMap_le_compNat_toPMap_iff.mpr fun _ _ hu => hA.mem_graph_sqrt_apply hu hs

omit hAT hT in
/-- `E_A((-∞, 0]) A^{1/2} y = 0`. -/
private lemma pvm_Iic_apply_of_mem_graph_sqrt {y u : E} (hu : (y, u) ∈ hA.sqrt.graph) :
    hA.pvm (Iic 0) u = 0 := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.sqrt,
    ProjectionValuedMeasure.mem_graph_integralPMap] at hu
  obtain ⟨hy, rfl⟩ := hu
  have h0 : (Iic (0 : ℝ)).indicator (fun t : ℝ => (Real.sqrt t : ℂ)) = 0 := by
    ext t
    by_cases ht : t ∈ Iic (0 : ℝ)
    · simp [ht, Real.sqrt_eq_zero_of_nonpos (show t ≤ 0 from ht)]
    · simp [ht]
  rw [hA.pvm.apply_integralApply hsq measurableSet_Iic hy, h0, ← enorm_eq_zero,
    hA.pvm.enorm_integralApply measurable_zero (by simp)]
  simp

omit hAT hT in
/-- `(∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A) A^{1/2} y = E_A((1/(n+1), ∞)) y`. -/
private lemma integral_polarCutoff_apply_of_mem_graph_sqrt {y u : E} (hu : (y, u) ∈ hA.sqrt.graph)
    (n : ℕ) : hA.pvm.integral (polarCutoff n) u = hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hb : ∀ t, ‖((Ioi ((n : ℝ) + 1)⁻¹).indicator (1 : ℝ → ℂ)) t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ioi ((n : ℝ) + 1)⁻¹ <;> simp [ht]
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.sqrt,
    ProjectionValuedMeasure.mem_graph_integralPMap] at hu
  obtain ⟨hy, rfl⟩ := hu
  rw [hA.pvm.integral_integralApply hsq (measurable_polarCutoff n) ⟨_, norm_polarCutoff_le n⟩ hy,
    mul_comm, sqrt_mul_polarCutoff, ← hA.pvm.integral_apply
      (measurable_one.indicator measurableSet_Ioi) ⟨1, hb⟩,
    hA.pvm.integral_indicator_one measurableSet_Ioi]

/-- **Polar decomposition**, pointwise: `U (|T| y) = T y`. -/
private lemma polarIsometry_apply_of_mem_graph {y u : E} {v : F} (hu : (y, u) ∈ hA.sqrt.graph)
    (hv : (y, v) ∈ T.graphₛₗ) : hA.polarIsometry hAT hT u = v := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT u) ?_
  simp_rw [hA.integral_polarCutoff_apply_of_mem_graph_sqrt hu]
  -- `E_A(s_n) y ∈ dom T`, with `T E_A(s_n) y → T y`
  have hmem : ∀ n : ℕ, (hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y,
      Function.extend Subtype.val T 0 (hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y)) ∈ T.graphₛₗ := fun n => by
    obtain ⟨w, hw⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mp
      ⟨_, hA.mem_graph_sqrt_apply hu measurableSet_Ioi⟩
    exact LinearPMap.mem_graphₛₗ_extend (LinearPMap.mem_domain_of_mem_graphₛₗ hw)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n : ℕ, ‖Function.extend Subtype.val T 0 (hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y) - v‖ =
      ‖hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) u - u‖ := fun n =>
    (hA.norm_eq_of_mem_graph_sqrt hAT hT
      (hA.sqrt.graph.sub_mem (hA.mem_graph_sqrt_apply hu measurableSet_Ioi) hu)
      (T.graphₛₗ.sub_mem (hmem n) hv)).symm
  simp_rw [hnorm]
  have h := (hA.tendsto_pvm_Ioi_inv u).sub (tendsto_const_nhds (x := u))
  have hu0 : hA.pvm (Ioi 0) u = u := by
    have hsplit := hA.pvm.apply_union (Set.Iic_disjoint_Ioi (le_refl (0 : ℝ))).symm
      measurableSet_Ioi measurableSet_Iic
    rw [Ioi_union_Iic, ProjectionValuedMeasure.apply_univ] at hsplit
    have := congrArg (fun P => P u) hsplit
    simp only [one_apply_eq_self, add_apply, hA.pvm_Iic_apply_of_mem_graph_sqrt hu, add_zero]
      at this
    exact this.symm
  rw [hu0, sub_self] at h
  exact h.norm.trans (by simp)

/-- **Polar decomposition** `T = U |T|`: for `A = T†T` with `T` closed, `T` is the composite of
`|T| = A^{1/2}` with the partial isometry `U`. -/
theorem eq_polarIsometry_compPMap :
    T = (hA.polarIsometry hAT hT : E →ₛₗ[σ] F).compPMap hA.sqrt := by
  refine LinearPMap.ext ?_ fun y hy hy' => ?_
  · ext y
    change y ∈ T.domain ↔ y ∈ hA.sqrt.domain
    rw [hA.domain_sqrt_eq_domain hAT hT]
  · change T ⟨y, hy⟩ = hA.polarIsometry hAT hT (hA.sqrt ⟨y, hy'⟩)
    exact (hA.polarIsometry_apply_of_mem_graph hAT hT (hA.sqrt.mem_graph ⟨y, hy'⟩)
      (T.mem_graphₛₗ ⟨y, hy⟩)).symm

omit hT [CompleteSpace F] in
/-- **Uniqueness of the positive part of the polar decomposition**: if `T = V B` with `B` positive
self-adjoint and `V` a bounded `σ`-semilinear map isometric on the range of `B`, then
`B = |T| = (T†T)^{1/2}`. -/
theorem eq_sqrt_of_eq_compPMap {B : E →ₗ.[ℂ] E} (hB : IsSelfAdjoint B) (hBpos : B.IsPositive)
    (V : E →SL[σ] F) (hV : ∀ y ∈ LinearMap.range B.toFun, ‖V y‖ = ‖y‖)
    (hTVB : T = (V : E →ₛₗ[σ] F).compPMap B) : B = hA.sqrt := by
  -- the inner products below are taken at graph points
  replace hV : ∀ x y, (x, y) ∈ B.graph → ‖V y‖ = ‖y‖ := fun x y h =>
    hV y (LinearPMap.mem_range_iff.mpr ⟨x, h⟩)
  have hTd : Dense (T.domain : Set E) :=
    hA.dense_domain.mono (domain_le_domain_of_eq_adjointₛₗ_compNat hAT)
  -- the graph of `T = V B`
  have hgraph : ∀ a b, (a, b) ∈ T.graphₛₗ ↔ ∃ c, (a, c) ∈ B.graph ∧ V c = b := fun a b => by
    rw [hTVB, LinearPMap.mem_graphₛₗ_compPMap]
    simp only [LinearPMap.mem_graphₛₗ_iff_mem_graph]
    rfl
  -- `B B ⊆ T†T = A`
  have hle : B.compNat B ≤ A := by
    refine LinearPMap.le_of_le_graph fun ⟨x, z⟩ hxz => ?_
    obtain ⟨w, hxw, hwz⟩ := LinearPMap.mem_graph_compNat.mp hxz
    rw [← LinearPMap.mem_graphₛₗ_iff_mem_graph, hAT, LinearPMap.mem_graphₛₗ_compNat]
    refine ⟨V w, (hgraph x (V w)).mpr ⟨w, hxw, rfl⟩, ?_⟩
    rw [LinearPMap.mem_graphₛₗ_adjointₛₗ_iff_re hTd]
    intro a b hab
    obtain ⟨c, hac, rfl⟩ := (hgraph a b).mp hab
    have h := hB.isFormalAdjoint.inner_eq_of_mem_graph hwz hac
    have hVi : (⟪V w, V c⟫_ℂ).re = (⟪w, c⟫_ℂ).re := by
      simp only [← RCLike.re_to_complex]
      rw [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ),
        re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ),
        ← map_add, hV _ _ (B.graph.add_mem hxw hac), hV _ _ hxw, hV _ _ hac]
    rw [hVi, h]
  -- `B B` is self-adjoint
  have hsa : IsSelfAdjoint (B.compNat B) := by
    have hid : Measurable fun t : ℝ => (t : ℂ) := Complex.measurable_ofReal
    have h := hB.eq_integralPMap_pvm
    rw [h, hB.pvm.compNat_integralPMap hid hid fun y hy => memLp_of_memLp_mul_self hid hy]
    exact hB.pvm.isSelfAdjoint_integralPMap (hid.mul hid) fun t => by simp
  exact hA.eq_sqrt_of_compNat_self_eq hB hBpos (IsSelfAdjoint.eq_of_le hsa hA.isFormalAdjoint hle).symm

omit hAT hT in
/-- `A^{1/2} E_A((-∞, 0]) x = 0`. -/
private lemma mem_graph_sqrt_pvm_Iic_apply_zero (x : E) : (hA.pvm (Iic 0) x, 0) ∈ hA.sqrt.graph := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hg : Measurable ((Iic (0 : ℝ)).indicator (1 : ℝ → ℂ)) :=
    measurable_one.indicator measurableSet_Iic
  have hgb : ∃ C, ∀ t, ‖(Iic (0 : ℝ)).indicator (1 : ℝ → ℂ) t‖ ≤ C :=
    ⟨1, fun t => by by_cases ht : t ∈ Iic (0 : ℝ) <;> simp [ht]⟩
  have hzero : (fun t : ℝ => (Real.sqrt t : ℂ)) * (Iic (0 : ℝ)).indicator 1 = fun _ => 0 := by
    funext t
    by_cases ht : t ∈ Iic (0 : ℝ)
    · simp [ht, Real.sqrt_eq_zero'.mpr (mem_Iic.mp ht)]
    · simp [ht]
  have hmem : MemLp ((fun t : ℝ => (Real.sqrt t : ℂ)) * (Iic (0 : ℝ)).indicator 1) 2
      (hA.pvm.measure x) := by
    rw [hzero]
    exact memLp_const 0
  rw [← hA.pvm.integral_indicator_one measurableSet_Iic, IsSelfAdjoint.sqrt,
    ProjectionValuedMeasure.sqrt, ProjectionValuedMeasure.mem_graph_integralPMap]
  refine ⟨(hA.pvm.memLp_measure_integral_apply_iff hsq hg hgb x).mpr hmem, ?_⟩
  rw [hA.pvm.integralApply_integral_apply hsq hg hgb hmem, hzero,
    ← hA.pvm.integral_apply measurable_const ⟨0, fun _ => norm_zero.le⟩,
    ProjectionValuedMeasure.integral_const,
    zero_smul, zero_apply]

/-- **Uniqueness of the polar decomposition**: if `T = V B` with `B` positive self-adjoint and `V` a
bounded `σ`-semilinear map isometric on the range of `B` and vanishing on `ker B`, then `B = |T|`
(`IsSelfAdjoint.eq_sqrt_of_eq_compPMap`) and `V = U` is the partial isometry. -/
theorem eq_polarIsometry_of_eq_compPMap {B : E →ₗ.[ℂ] E} (hB : IsSelfAdjoint B)
    (hBpos : B.IsPositive) (V : E →SL[σ] F) (hV : ∀ y ∈ LinearMap.range B.toFun, ‖V y‖ = ‖y‖)
    (hVker : B.ker ≤ LinearMap.ker (V : E →ₛₗ[σ] F))
    (hTVB : T = (V : E →ₛₗ[σ] F).compPMap B) :
    V = hA.polarIsometry hAT hT := by
  obtain rfl := hA.eq_sqrt_of_eq_compPMap hAT hB hBpos V hV hTVB
  set U := hA.polarIsometry hAT hT
  set P := hA.pvm
  -- `V = U` on `E_A((0, ∞)) E`, as limits on the ranges of `E_A((1/(n+1), ∞))`
  have hIoi : ∀ x, V (P (Ioi 0) x) = U (P (Ioi 0) x) := fun x => by
    have hn : ∀ n : ℕ, V (P (Ioi ((n : ℝ) + 1)⁻¹) x) = U (P (Ioi ((n : ℝ) + 1)⁻¹) x) := fun n => by
      have hu := hA.mem_graph_sqrt_integral_polarCutoff n x
      have hv : (P.integral (polarCutoff n) x, V (P (Ioi ((n : ℝ) + 1)⁻¹) x)) ∈ T.graphₛₗ := by
        rw [hTVB, LinearPMap.mem_graphₛₗ_compPMap]
        exact ⟨_, LinearPMap.mem_graphₛₗ_iff_mem_graph.mpr hu, rfl⟩
      exact (hA.polarIsometry_apply_of_mem_graph hAT hT hu hv).symm
    exact tendsto_nhds_unique ((V.continuous.tendsto _).comp (hA.tendsto_pvm_Ioi_inv x))
      (((U.continuous.tendsto _).comp (hA.tendsto_pvm_Ioi_inv x)).congr fun n => (hn n).symm)
  -- both vanish on `E_A((-∞, 0]) E ⊆ ker A^{1/2}`
  have hIic : ∀ x, V (P (Iic 0) x) = U (P (Iic 0) x) := fun x => by
    have h0 : V (P (Iic 0) x) = 0 :=
      hVker (LinearPMap.mem_graph_zero_iff_mem_ker.mp (hA.mem_graph_sqrt_pvm_Iic_apply_zero x))
    rw [h0, eq_comm, ← norm_eq_zero,
      hA.norm_polarIsometry_apply hAT hT, ← mul_apply_eq_comp, ← P.apply_inter measurableSet_Ioi
        measurableSet_Iic, Ioi_inter_Iic, Ioc_self, ProjectionValuedMeasure.apply_empty,
      zero_apply, norm_zero]
  have hsplit : ∀ x, x = P (Iic 0) x + P (Ioi 0) x := fun x => by
    have h := P.apply_union (Set.Iic_disjoint_Ioi (le_refl (0 : ℝ))) measurableSet_Iic
      measurableSet_Ioi
    rw [Iic_union_Ioi, ProjectionValuedMeasure.apply_univ] at h
    rw [← add_apply, ← h, one_apply_eq_self]
  ext x
  rw [hsplit x, map_add, map_add, hIic, hIoi]

/-! ### The partial isometry as an operator -/

omit [CompleteSpace F] hAT hT in
/-- `E_A((0, ∞)) A^{1/2} x = A^{1/2} x`. -/
private lemma pvm_Ioi_apply_eq_self_of_mem_graph_sqrt {x u : E} (hu : (x, u) ∈ hA.sqrt.graph) :
    hA.pvm (Ioi 0) u = u := by
  have h₀ : hA.pvm (Iic 0) u = 0 := sub_eq_zero.mp (hA.sqrt.graph_fst_eq_zero_snd
    (hA.sqrt.graph.sub_mem (hA.mem_graph_sqrt_apply hu measurableSet_Iic)
      (hA.mem_graph_sqrt_pvm_Iic_apply_zero x)) (sub_self _))
  have h := hA.pvm.apply_union (Set.Iic_disjoint_Ioi (le_refl (0 : ℝ))) measurableSet_Iic
    measurableSet_Ioi
  rw [Iic_union_Ioi, ProjectionValuedMeasure.apply_univ] at h
  have hsplit : u = hA.pvm (Iic 0) u + hA.pvm (Ioi 0) u := by
    rw [← add_apply, ← h, one_apply_eq_self]
  rw [h₀, zero_add] at hsplit
  exact hsplit.symm

omit [CompleteSpace F] hAT hT in
/-- **The range of `A^{1/2}` lies in `E_A((0, ∞)) E`**: `E_A((0, ∞)) A^{1/2} = A^{1/2}`. -/
lemma pvm_Ioi_compPMap_sqrt :
    ((hA.pvm (Ioi 0) : E →L[ℂ] E) : E →ₗ[ℂ] E).compPMap hA.sqrt = hA.sqrt :=
  LinearPMap.ext rfl fun x hx _ =>
    hA.pvm_Ioi_apply_eq_self_of_mem_graph_sqrt (hA.sqrt.mem_graph ⟨x, hx⟩)

/-- **`ker T ⊆ ker E_A((0, ∞))`**: the kernel of `T` lies in `E_A((-∞, 0]) E`. -/
lemma ker_le_ker_pvm_Ioi :
    T.ker ≤ LinearMap.ker ((hA.pvm (Ioi 0) : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
  intro k hk
  -- the spectral cutoffs are evaluated at the single vector `k`
  replace hk := LinearPMap.mem_graphₛₗ_zero_iff_mem_ker.mpr hk
  change hA.pvm (Ioi 0) k = 0
  obtain ⟨u, hu⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mpr ⟨0, hk⟩
  have hu0 : u = 0 := norm_eq_zero.mp ((hA.norm_eq_of_mem_graph_sqrt hAT hT hu hk).trans norm_zero)
  subst hu0
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  -- `E_A((1/(n+1), ∞)) k = A^{1/2} (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A) k = 0`
  have hn : ∀ n : ℕ, hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) k = 0 := fun n => by
    have h₁ := hA.mem_graph_sqrt_integral_polarCutoff n k
    have h₂ := LinearPMap.compPMap_le_compNat_toPMap_iff.mp
      (hA.pvm.integral_compPMap_integralPMap_le hsq (measurable_polarCutoff n)
        ⟨_, norm_polarCutoff_le n⟩) hu
    rw [map_zero] at h₂
    exact sub_eq_zero.mp (hA.sqrt.graph_fst_eq_zero_snd (hA.sqrt.graph.sub_mem h₁ h₂) (sub_self _))
  exact tendsto_nhds_unique (hA.tendsto_pvm_Ioi_inv k)
    (tendsto_const_nhds.congr fun n => (hn n).symm)

/-- **`(ker T)ᗮ ⊆ E_A((0, ∞)) E`**: vectors orthogonal to the kernel of `T` lie in `E_A((0, ∞)) E`. -/
lemma pvm_Ioi_apply_eq_self {z : E} (hz : z ∈ T.kerᗮ) : hA.pvm (Ioi 0) z = z := by
  set k := hA.pvm (Iic 0) z
  have hk : (k, 0) ∈ T.graphₛₗ := by
    obtain ⟨v, hv⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mp
      ⟨0, hA.mem_graph_sqrt_pvm_Iic_apply_zero z⟩
    have hv0 : v = 0 := norm_eq_zero.mp
      ((hA.norm_eq_of_mem_graph_sqrt hAT hT (hA.mem_graph_sqrt_pvm_Iic_apply_zero z) hv).symm.trans
        norm_zero)
    rwa [hv0] at hv
  have h₀ : k = 0 := by
    have h := Submodule.inner_right_of_mem_orthogonal
      (LinearPMap.mem_graphₛₗ_zero_iff_mem_ker.mp hk) hz
    have hkk : ⟪k, k⟫_ℂ = ⟪k, z⟫_ℂ := by
      simp only [k]
      rw [← hA.pvm.inner_apply_left, hA.pvm.apply_apply_self measurableSet_Iic]
    rw [← hkk] at h
    exact inner_self_eq_zero.mp h
  have h := hA.pvm.apply_union (Set.Iic_disjoint_Ioi (le_refl (0 : ℝ))) measurableSet_Iic
    measurableSet_Ioi
  rw [Iic_union_Ioi, ProjectionValuedMeasure.apply_univ] at h
  have hsplit : z = hA.pvm (Iic 0) z + hA.pvm (Ioi 0) z := by
    rw [← add_apply, ← h, one_apply_eq_self]
  change z = k + hA.pvm (Ioi 0) z at hsplit
  rw [h₀, zero_add] at hsplit
  exact hsplit.symm

/-- The partial isometry only sees `E_A((0, ∞)) x`: `U E_A((0, ∞)) = U`. -/
lemma polarIsometry_pvm_Ioi_apply (x : E) :
    hA.polarIsometry hAT hT (hA.pvm (Ioi 0) x) = hA.polarIsometry hAT hT x := by
  rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hA.norm_polarIsometry_apply hAT hT, map_sub,
    hA.pvm.apply_apply_self measurableSet_Ioi, sub_self, norm_zero]

/-- `re ⟪U x, U y⟫ = re ⟪E_A((0, ∞)) x, E_A((0, ∞)) y⟫`: `U` is isometric on `E_A((0, ∞)) E`. -/
private lemma re_inner_polarIsometry_apply (x y : E) :
    (⟪hA.polarIsometry hAT hT x, hA.polarIsometry hAT hT y⟫_ℂ).re =
      (⟪hA.pvm (Ioi 0) x, hA.pvm (Ioi 0) y⟫_ℂ).re := by
  simp only [← RCLike.re_to_complex]
  rw [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add (hA.polarIsometry hAT hT), ← map_add (hA.pvm (Ioi 0)),
    hA.norm_polarIsometry_apply hAT hT, hA.norm_polarIsometry_apply hAT hT,
    hA.norm_polarIsometry_apply hAT hT]

/-- `U† U = E_A((0, ∞))`, for the adjoint `U†` of the partial isometry. -/
lemma adjointₛₗ_polarIsometry_apply_polarIsometry (x : E) :
    (hA.polarIsometry hAT hT).adjointₛₗ (hA.polarIsometry hAT hT x) = hA.pvm (Ioi 0) x := by
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ), ← inner_self_ofReal_re, RCLike.ofReal_eq_zero,
    RCLike.re_to_complex]
  -- `re ⟪U† U x, y⟫ = re ⟪U x, U y⟫ = re ⟪E x, E y⟫ = re ⟪E x, y⟫` for every `y`
  have hre : ∀ z : ℂ, (σ z).re = z.re := fun z => by
    rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
    · rfl
    · exact conj_re z
  have h : ∀ y, (⟪(hA.polarIsometry hAT hT).adjointₛₗ (hA.polarIsometry hAT hT x), y⟫_ℂ).re =
      (⟪hA.pvm (Ioi 0) x, y⟫_ℂ).re := fun y => by
    rw [ContinuousLinearMap.adjointₛₗ_inner_left, hre, hA.re_inner_polarIsometry_apply hAT hT,
      ← hA.pvm.inner_apply_left, hA.pvm.apply_apply_self measurableSet_Ioi]
  rw [inner_sub_left, sub_re, h, sub_self]

/-- `⟪U x, U y⟫ = σ ⟪E_A((0, ∞)) x, E_A((0, ∞)) y⟫`: `U` is isometric on `E_A((0, ∞)) E`. -/
lemma inner_polarIsometry_apply (x y : E) :
    ⟪hA.polarIsometry hAT hT x, hA.polarIsometry hAT hT y⟫_ℂ =
      σ ⟪hA.pvm (Ioi 0) x, hA.pvm (Ioi 0) y⟫_ℂ := by
  rw [← hA.pvm.inner_apply_left, hA.pvm.apply_apply_self measurableSet_Ioi,
    ← hA.adjointₛₗ_polarIsometry_apply_polarIsometry hAT hT, ContinuousLinearMap.adjointₛₗ_inner_left,
    RingHomInvPair.comp_apply_eq₂]

/-- `U†` vanishes on the orthogonal complement of the range of `U`. -/
lemma adjointₛₗ_polarIsometry_apply_eq_zero {y : F}
    (hy : ∀ x, ⟪y, hA.polarIsometry hAT hT x⟫_ℂ = 0) :
    (hA.polarIsometry hAT hT).adjointₛₗ y = 0 :=
  ContinuousLinearMap.adjointₛₗ_apply_eq _ fun x => by rw [hy, map_zero, inner_zero_left]

/-- The range of the partial isometry is closed. -/
lemma isClosed_range_polarIsometry : IsClosed (range (hA.polarIsometry hAT hT)) := by
  set U := hA.polarIsometry hAT hT
  have h : range U = {y | U (U.adjointₛₗ y) = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change U (U.adjointₛₗ (U x)) = U x
      rw [hA.adjointₛₗ_polarIsometry_apply_polarIsometry hAT hT,
        hA.polarIsometry_pvm_Ioi_apply hAT hT]
    · intro hy
      exact ⟨_, hy⟩
  rw [h]
  exact isClosed_eq (U.continuous.comp U.adjointₛₗ.continuous) continuous_id

/-- The partial isometry takes values in the closure of the range of `T`. -/
lemma polarIsometry_apply_mem_closure_range (x : E) :
    hA.polarIsometry hAT hT x ∈ closure (range T) :=
  mem_closure_of_tendsto (hA.tendsto_polarIsometryFun hAT hT x) (Eventually.of_forall fun n => by
    obtain ⟨p, -, hp⟩ := hA.mem_graph_polarCutoff hAT hT n x
    exact ⟨p, hp⟩)

/-- The range of `T` lies in that of the partial isometry: `T x = U |T| x`. -/
lemma range_subset_range_polarIsometry : range T ⊆ range (hA.polarIsometry hAT hT) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨u, hu⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mpr ⟨_, T.mem_graphₛₗ x⟩
  exact ⟨u, hA.polarIsometry_apply_of_mem_graph hAT hT hu (T.mem_graphₛₗ x)⟩

/-- The partial isometry is a contraction: `‖U‖ ≤ 1`. -/
lemma norm_polarIsometry_le : ‖hA.polarIsometry hAT hT‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, hA.norm_polarIsometry_apply hAT hT]
    exact hA.pvm.norm_apply_le _ x

/-- The adjoint of the partial isometry is a contraction: `‖U†‖ ≤ 1`. -/
lemma norm_adjointₛₗ_polarIsometry_le : ‖(hA.polarIsometry hAT hT).adjointₛₗ‖ ≤ 1 :=
  (ContinuousLinearMap.norm_adjointₛₗ_le _).trans (hA.norm_polarIsometry_le hAT hT)

/-- **`|T| = U† T`**: the adjoint `U†` inverts `U` on the range of `|T|`
(`IsSelfAdjoint.adjointₛₗ_polarIsometry_apply_polarIsometry`, `IsSelfAdjoint.pvm_Ioi_compPMap_sqrt`),
so `U† T = U† U |T| = E_A((0, ∞)) |T| = |T|`. -/
lemma adjointₛₗ_polarIsometry_compPMap :
    ((hA.polarIsometry hAT hT).adjointₛₗ : F →ₛₗ[σ] E).compPMap T = hA.sqrt := by
  set U := hA.polarIsometry hAT hT
  have hUU : (U.adjointₛₗ : F →ₛₗ[σ] E).comp (U : E →ₛₗ[σ] F) =
      ((hA.pvm (Ioi 0) : E →L[ℂ] E) : E →ₗ[ℂ] E) :=
    LinearMap.ext (hA.adjointₛₗ_polarIsometry_apply_polarIsometry hAT hT)
  calc (U.adjointₛₗ : F →ₛₗ[σ] E).compPMap T
      = (U.adjointₛₗ : F →ₛₗ[σ] E).compPMap ((U : E →ₛₗ[σ] F).compPMap hA.sqrt) :=
        congrArg (fun S => (U.adjointₛₗ : F →ₛₗ[σ] E).compPMap S)
          (hA.eq_polarIsometry_compPMap hAT hT)
    _ = hA.sqrt := by
        rw [← LinearPMap.compPMap_comp, hUU, hA.pvm_Ioi_compPMap_sqrt]

/-- `T ⊇ U |T|`, pointwise. -/
private lemma mem_graph_polarIsometry_apply {x u : E} (hu : (x, u) ∈ hA.sqrt.graph) :
    (x, hA.polarIsometry hAT hT u) ∈ T.graphₛₗ :=
  LinearPMap.le_graphₛₗ_of_le (hA.eq_polarIsometry_compPMap hAT hT).ge
    (LinearPMap.mem_graphₛₗ_compPMap.mpr ⟨u, LinearPMap.mem_graphₛₗ_iff_mem_graph.mpr hu, rfl⟩)

end IsSelfAdjoint

/-! ### Injective operators with dense range -/

namespace IsSelfAdjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ]
  {T : E →ₛₗ.[σ] F} (hAT : A = T.adjointₛₗ.compNat T) (hT : T.IsClosedₛₗ) (hTk : T.ker = ⊥)

omit [CompleteSpace F] in
include hA hAT in
/-- **`ker T†T = ker T`**: for `A = T†T`, the kernel of `A` is that of `T`. -/
lemma ker_eq_of_eq_adjointₛₗ_compNat : A.ker = T.ker := by
  rw [hAT, LinearPMap.ker_adjointₛₗ_compNat_self
    (hA.dense_domain.mono (domain_le_domain_of_eq_adjointₛₗ_compNat hAT))]

omit [CompleteSpace F] in
include hA hAT in
/-- For `A = T†T`, `A` is injective iff `T` is
(`IsSelfAdjoint.ker_eq_of_eq_adjointₛₗ_compNat`). -/
lemma ker_eq_bot_iff_of_eq_adjointₛₗ_compNat : A.ker = ⊥ ↔ T.ker = ⊥ := by
  rw [hA.ker_eq_of_eq_adjointₛₗ_compNat hAT]

include hAT hTk

omit [CompleteSpace F] in
include hA in
/-- For an injective `T`, `A = T†T` is positive and injective, so `E_A((0, ∞)) = 1`
(`IsSelfAdjoint.pvm_Ioi_eq_one`). -/
lemma pvm_Ioi_eq_one_of_ker_eq_bot : hA.pvm (Ioi 0) = 1 :=
  hA.pvm_Ioi_eq_one (hA.isPositive_of_eq_adjointₛₗ_compNat hAT)
    ((hA.ker_eq_bot_iff_of_eq_adjointₛₗ_compNat hAT).mpr hTk)

include hA hT in
/-- For an injective `T`, the partial isometry of `T = U |T|` is an isometry. -/
lemma norm_polarIsometry_of_ker_eq_bot (x : E) : ‖hA.polarIsometry hAT hT x‖ = ‖x‖ := by
  rw [hA.norm_polarIsometry_apply hAT hT, hA.pvm_Ioi_eq_one_of_ker_eq_bot hAT hTk,
    one_apply_eq_self]

variable (hTr : Dense (range T))
include hTr

omit hTk in
include hA hT in
/-- For `T` with dense range, the partial isometry of `T = U |T|` is surjective: its range is closed
and contains the range of `T`. -/
lemma surjective_polarIsometry_of_dense_range : Function.Surjective (hA.polarIsometry hAT hT) := by
  rw [← range_eq_univ, ← (hA.isClosed_range_polarIsometry hAT hT).closure_eq]
  exact (hTr.mono (hA.range_subset_range_polarIsometry hAT hT)).closure_eq

/-- The **isometric part** `U` of the polar decomposition `T = U |T|` of a `σ`-semilinear closed
injective operator `T` with dense range, as a semilinear isometric equivalence. -/
noncomputable def polarIsometryEquiv : E ≃ₛₗᵢ[σ] F :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (hA.polarIsometry hAT hT : E →ₛₗ[σ] F)
      norm_map' := hA.norm_polarIsometry_of_ker_eq_bot hAT hT hTk }
    (hA.surjective_polarIsometry_of_dense_range hAT hT hTr)

/-- `U` is the partial isometry of the polar decomposition. -/
lemma polarIsometryEquiv_apply (x : E) :
    hA.polarIsometryEquiv hAT hT hTk hTr x = hA.polarIsometry hAT hT x := rfl

end IsSelfAdjoint

/-! ### Involutions -/

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ]
  {S : E →ₛₗ.[σ] E} (hAS : A = S.adjointₛₗ.compNat S) (hS : S.IsClosedₛₗ)
  (hinv : S.compNat S = (LinearMap.id : E →ₗ[ℂ] E).toPMap S.domain)
include hAS hinv

omit [CompleteSpace E] [RingHomIsometric σ] hAS in
/-- An involution is injective. -/
lemma _root_.LinearPMap.ker_eq_bot_of_involution : S.ker = ⊥ :=
  -- `S x = 0` gives `x = S 0 = 0`, at the single vector `x`
  LinearPMap.ker_eq_bot_iff_mem_graphₛₗ.mpr fun _ hx =>
    LinearPMap.graphₛₗ_fst_eq_zero_snd (LinearPMap.compNat_self_eq_id_iff.mp hinv hx) rfl

omit [CompleteSpace E] [RingHomIsometric σ] hAS in
/-- A densely defined involution has dense range: its range is its domain. -/
lemma _root_.LinearPMap.dense_range_of_involution (hd : Dense (S.domain : Set E)) :
    Dense (range S) := by
  refine hd.mono ?_
  intro x hx
  exact LinearPMap.mem_range_iff_mem_graphₛₗ.mpr
    ⟨_, LinearPMap.compNat_self_eq_id_iff.mp hinv (S.mem_graphₛₗ ⟨x, hx⟩)⟩

/-- `𝐉` is the isometric part `J` of the polar decomposition `S = J |S|` of the involution `S`,
`hA.polarIsometryEquiv hAS hS _ _`, which exists since `S` is injective with dense range
(`LinearPMap.ker_eq_bot_of_involution`, `LinearPMap.dense_range_of_involution`). The notation is
local to this section: outside it, the statements below display the expanded form. -/
local notation "𝐉" => hA.polarIsometryEquiv hAS hS (LinearPMap.ker_eq_bot_of_involution hinv)
  (LinearPMap.dense_range_of_involution hinv
    (hA.dense_domain.mono (domain_le_domain_of_eq_adjointₛₗ_compNat hAS)))

/-- From `S = J |S|` and `S² = 1`: `|S| J u = J⁻¹ x` for `|S| x = u` (in graph form). -/
private lemma mem_graph_sqrt_polarIsometryEquiv {x u : E} (hu : (x, u) ∈ hA.sqrt.graph) :
    (𝐉 u, (𝐉).symm x) ∈ hA.sqrt.graph := by
  set J := 𝐉
  have h₁ := LinearPMap.compNat_self_eq_id_iff.mp hinv (hA.mem_graph_polarIsometry_apply hAS hS hu)
  obtain ⟨w, hw⟩ := (hA.exists_mem_graph_sqrt_iff hAS hS).mpr ⟨_, h₁⟩
  have h₂ := hA.mem_graph_polarIsometry_apply hAS hS hw
  have hx : J w = x := LinearPMap.mem_graphₛₗ_snd_inj h₂ h₁
  rwa [← hx, LinearIsometryEquiv.symm_apply_apply]

/-- **`J² = 1`** for the isometric part of a `σ`-semilinear closed involution `S = J |S|`. -/
lemma polarIsometryEquiv_apply_apply (x : E) :
    𝐉 (𝐉 x) = x := by
  set J := 𝐉
  set E' := hA.pvm
  have hSk := LinearPMap.ker_eq_bot_of_involution hinv
  have hpos := hA.isPositive_of_eq_adjointₛₗ_compNat hAS
  have hc : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hc0 : ∀ y, ∀ᵐ t ∂(E'.measure y), (Real.sqrt t : ℂ) ≠ 0 := fun y => by
    have h := measure_eq_zero_iff_ae_notMem.mp (hA.measure_pvm_Iic_zero hpos
      ((hA.ker_eq_bot_iff_of_eq_adjointₛₗ_compNat hAS).mpr hSk) y)
    exact h.mono fun t ht => ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (not_le.mp ht)).ne'
  -- `P = J |S|⁻¹ J⁻¹`, the transported inverse of `|S|`
  set P := (E'.transport J).integralPMap fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
  have hcinv : Measurable fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable.inv
  have hP : ∀ y z, (y, z) ∈ P.graph ↔ (J.symm z, J.symm y) ∈ hA.sqrt.graph := fun y z => by
    -- `P J = J |S|⁻¹`, evaluated at the graph point `(J⁻¹ y, J⁻¹ z)`
    have hT := (LinearPMap.compNat_toPMap_eq_compPMap_iff J.toLinearEquiv).mp
      (E'.integralPMap_transport_compNat J hcinv) (J.symm y) (J.symm z)
    simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.apply_symm_apply] at hT
    rw [← hT]
    simp_rw [RingHom.apply_ofReal_of_ringHomInvPair σ, ofReal_inv]
    rw [E'.integralPMap_inv hc hc0]
    exact LinearPMap.mem_graph_inverse_iff (E'.ker_integralPMap_eq_bot hc hc0)
  have hPsa : IsSelfAdjoint P :=
    (E'.transport J).isSelfAdjoint_integralPMap_ofReal Real.continuous_sqrt.measurable.inv
  have hPpos : P.IsPositive :=
    (E'.transport J).isPositive_integralPMap_ofReal Real.continuous_sqrt.measurable.inv
      fun t => inv_nonneg.mpr (Real.sqrt_nonneg t)
  -- `|S| = W P` with the complex-linear isometry `W = J⁻¹ J⁻¹`
  let W : E →L[ℂ] E := (J.symm : E →SL[σ] E).comp (J.symm : E →SL[σ] E)
  have hW : ∀ x, ‖W x‖ = ‖x‖ := fun x => by simp [W]
  have hCP : ∀ x u, (x, u) ∈ hA.sqrt.graph ↔ ∃ z, (x, z) ∈ P.graph ∧ W z = u := fun x u => by
    constructor
    · intro hu
      refine ⟨J (J u), (hP _ _).mpr ?_, by simp [W]⟩
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hu
    · rintro ⟨z, hz, rfl⟩
      have h := hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv ((hP _ _).mp hz)
      rwa [LinearIsometryEquiv.apply_symm_apply] at h
  have hCWP : hA.sqrt = (W : E →ₗ[ℂ] E).compPMap P := by
    refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨x, u⟩ => ?_)
    rw [hCP, LinearPMap.mem_graph_compPMap]
    rfl
  -- `A = |S|†|S|`
  have hAC : A = hA.sqrt.adjointₛₗ.compNat hA.sqrt := by
    rw [LinearPMap.adjointₛₗ_eq_adjoint, LinearPMap.isSelfAdjoint_def.mp hA.isSelfAdjoint_sqrt,
      hA.sqrt_compNat_sqrt hpos]
  have hPC : P = hA.sqrt := hA.eq_sqrt_of_eq_compPMap hAC hPsa hPpos W (fun y _ => hW y) hCWP
  -- `J (J u) = u` on the range of `|S|`, which is dense
  have hJJ : ∀ x u, (x, u) ∈ hA.sqrt.graph → J (J u) = u := fun x u hu => by
    have h' : (x, J (J u)) ∈ hA.sqrt.graph := by
      rw [← hPC, hP, LinearIsometryEquiv.symm_apply_apply]
      exact hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hu
    exact hA.sqrt.mem_graph_snd_inj h' hu rfl
  have hall : ∀ y, J (J y) = y := fun y => by
    have hclosed : IsClosed {u : E | J (J u) = u} :=
      isClosed_eq (J.continuous.comp J.continuous) continuous_id
    have hlim := hA.tendsto_pvm_Ioi_inv y
    rw [hA.pvm_Ioi_eq_one_of_ker_eq_bot hAS hSk, one_apply_eq_self] at hlim
    exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n =>
      hJJ _ _ (hA.mem_graph_sqrt_integral_polarCutoff n y))
  exact hall x

/-- `J⁻¹ = J`. -/
lemma polarIsometryEquiv_symm_apply (x : E) :
    (𝐉).symm x = 𝐉 x := by
  conv_lhs => rw [← hA.polarIsometryEquiv_apply_apply hAS hS hinv x]
  exact LinearIsometryEquiv.symm_apply_apply _ _

/-- `J |S| J = |S|⁻¹` in graph form: `|S| x = u` iff `|S| (J u) = J x`. -/
private lemma mem_graph_sqrt_polarIsometryEquiv_swap {x u : E} :
    (x, u) ∈ hA.sqrt.graph ↔
      (𝐉 u, 𝐉 x) ∈ hA.sqrt.graph := by
  constructor
  · intro hu
    have h := hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hu
    rwa [polarIsometryEquiv_symm_apply] at h
  · intro hu
    have h := hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hu
    rwa [polarIsometryEquiv_symm_apply, polarIsometryEquiv_apply_apply,
      polarIsometryEquiv_apply_apply] at h

/-- **`|S| J = J |S|⁻¹`**, i.e. `J |S| J⁻¹ = |S|⁻¹`, for a `σ`-semilinear closed involution
`S = J |S|`. For the Tomita operator this is `J Δ^{1/2} J = Δ^{-1/2}`. -/
lemma sqrt_compNat_polarIsometryEquiv :
    hA.sqrt.compNat ((𝐉 : E →ₛₗ[σ] E).toPMap ⊤) = (𝐉 : E →ₛₗ[σ] E).compPMap hA.sqrt.inverse := by
  -- the swap `|S| x = u ↔ |S| (J u) = J x` is a statement about graph points
  refine (LinearPMap.compNat_toPMap_eq_compPMap_iff (𝐉).toLinearEquiv).mpr fun x u => ?_
  simp only [LinearIsometryEquiv.coe_toLinearEquiv]
  rw [LinearPMap.mem_graph_inverse_iff (hA.ker_sqrt_eq_bot (hA.isPositive_of_eq_adjointₛₗ_compNat hAS)
    ((hA.ker_eq_bot_iff_of_eq_adjointₛₗ_compNat hAS).mpr (LinearPMap.ker_eq_bot_of_involution hinv)))]
  exact hA.mem_graph_sqrt_polarIsometryEquiv_swap hAS hS hinv

/-- **`J Δ J = Δ⁻¹`** for a `σ`-semilinear closed involution `S = J Δ^{1/2}` with `Δ = S†S`, in
spectral form: transporting `E_Δ` along `J` gives its image under `λ ↦ λ⁻¹`. -/
lemma pvm_transport_polarIsometryEquiv :
    hA.pvm.transport (𝐉) = hA.pvm.map (fun t => t⁻¹) measurable_inv := by
  set J := 𝐉
  set E' := hA.pvm
  have hSk := LinearPMap.ker_eq_bot_of_involution hinv
  have hpos := hA.isPositive_of_eq_adjointₛₗ_compNat hAS
  have hc : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hpos' : ∀ y, ∀ᵐ t ∂(E'.measure y), 0 < t := fun y =>
    (measure_eq_zero_iff_ae_notMem.mp (hA.measure_pvm_Iic_zero hpos
      ((hA.ker_eq_bot_iff_of_eq_adjointₛₗ_compNat hAS).mpr hSk) y)).mono
      fun t ht => not_le.mp ht
  have hc0 : ∀ y, ∀ᵐ t ∂(E'.measure y), (Real.sqrt t : ℂ) ≠ 0 := fun y =>
    (hpos' y).mono fun t ht => ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have hsqrt := Real.continuous_sqrt.measurable
  -- `|S| J = J |S|⁻¹`, then as projection-valued measures
  have hCi := E'.isSelfAdjoint_integralPMap_ofReal hsqrt.inv
  have hinvS : (E'.integralPMap fun t => (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) = hA.sqrt.inverse := by
    simp_rw [ofReal_inv]
    exact E'.integralPMap_inv hc hc0
  have h₁ := hCi.pvm_eq_transport hA.isSelfAdjoint_sqrt J
    (by convert hA.sqrt_compNat_polarIsometryEquiv hAS hS hinv using 2)
  change (E'.isSelfAdjoint_integralPMap_ofReal hsqrt).pvm = _ at h₁
  rw [E'.pvm_integralPMap_ofReal hsqrt, E'.pvm_integralPMap_ofReal hsqrt.inv] at h₁
  -- apply `λ ↦ λ²` to both sides
  have hsq : Measurable fun t : ℝ => t ^ 2 := measurable_id.pow_const 2
  have h₂ := congrArg (fun F => F.map (fun t : ℝ => t ^ 2) hsq) h₁
  rw [ProjectionValuedMeasure.map_map, ProjectionValuedMeasure.transport_map,
    ProjectionValuedMeasure.map_map] at h₂
  rw [E'.map_congr_ae (hsq.comp hsqrt) measurable_id fun y => (hpos' y).mono fun t ht => by
      simp [Real.sq_sqrt ht.le], ProjectionValuedMeasure.map_id,
    E'.map_congr_ae (hsq.comp hsqrt.inv) measurable_inv fun y => (hpos' y).mono fun t ht => by
      simp [inv_pow, Real.sq_sqrt ht.le]] at h₂
  have hJJ := hA.polarIsometryEquiv_apply_apply hAS hS hinv
  conv_lhs => rw [h₂]
  exact ProjectionValuedMeasure.transport_transport _ _ hJJ

/-- **`J f(Δ) J = (σ ∘ f ∘ inv)(Δ)`** for bounded measurable `f`, for a `σ`-semilinear closed
involution `S = J Δ^{1/2}` with `Δ = S†S`. For the Tomita operator (`σ` the conjugation) and
`f(λ) = λ^{it}` this is `J Δ^{it} J = Δ^{it}`. -/
lemma polarIsometryEquiv_integral_apply {f : ℝ → ℂ} (hf : Measurable f)
    (hfb : ∃ C, ∀ t, ‖f t‖ ≤ C) (y : E) :
    𝐉 (hA.pvm.integral f (𝐉 y)) = hA.pvm.integral (fun t => σ (f t⁻¹)) y := by
  set J := 𝐉
  have hσc : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun _ => RingHomIsometric.norm_map).continuous
  obtain ⟨C, hC⟩ := hfb
  have hg : Measurable fun t => σ (f t) := hσc.measurable.comp hf
  have hgb : ∃ C, ∀ t, ‖σ (f t)‖ ≤ C := ⟨C, fun t => by rw [RingHomIsometric.norm_map]; exact hC t⟩
  have h := congrArg (fun T => T y) (hA.pvm.integral_transport J hg hgb)
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, RingHomInvPair.comp_apply_eq] at h
  rw [hA.pvm_transport_polarIsometryEquiv hAS hS hinv,
    ProjectionValuedMeasure.integral_map hg hgb measurable_inv hA.pvm,
    hA.polarIsometryEquiv_symm_apply hAS hS hinv] at h
  exact h.symm

end IsSelfAdjoint
