/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.UnboundedOperator.Power

/-!
# Polar decomposition

Let `T : E → F` be a closed, densely defined real-linear operator between complex Hilbert spaces
(adjoints are real adjoints for `re ⟪·, ·⟫`, `open ClosedSubmodule`), and let `A` be a self-adjoint
complex operator with `A = T†T` as real operators. The operator `|T| = A^{1/2}`
(`IsSelfAdjoint.sqrt`) has the same domain as `T` and `‖|T| x‖ = ‖T x‖`
(`IsSelfAdjoint.exists_mem_graph_sqrt_iff`, `IsSelfAdjoint.norm_eq_of_mem_graph_sqrt`): both are
closed, `dom A` is a core for both (von Neumann's theorem and the spectral cutoffs), and on `dom A`
the identity is `‖|T| x‖² = ⟪x, A x⟫ = ‖T x‖²`. The **polar decomposition** `T = U |T|`
(`IsSelfAdjoint.eq_polarIsometry_compPMap`) has the partial isometry
`U x = lim T (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A(λ)) x` (`IsSelfAdjoint.polarIsometry`), isometric on
`E_A((0, ∞)) E` and zero on `ker T`; `U` is `σ`-semilinear when `T` is. The decomposition is
unique (`IsSelfAdjoint.eq_sqrt_of_eq_compPMap`, `IsSelfAdjoint.eq_polarIsometry_of_eq_compPMap`):
`T = V B` with `B` positive self-adjoint and `V` isometric on the range of `B` forces `B B = A` and
`B = A^{1/2}`, and if moreover `V` vanishes on `ker B`, then `V = U`. Making `T` real-linear treats complex-linear and
conjugate-linear operators at once.

For a `σ`-semilinear closed **involution** `S` (`S x = v` iff `S v = x`), such as the Tomita
operator of a standard subspace, `Δ = S†S` is injective, `U = J` is a `σ`-semilinear isometric
equivalence (`IsSelfAdjoint.polarIsometryEquiv`), and uniqueness applied to
`S = S⁻¹ = J⁻¹ (J Δ^{-1/2} J⁻¹)` gives `J² = 1` and `J Δ^{1/2} J = Δ^{-1/2}`; in spectral form
`J E_Δ J = inv_* E_Δ`, so `J f(Δ) J = (σ ∘ f ∘ inv)(Δ)`, for instance `J Δ^{it} J = Δ^{it}`.

## Main definitions

* `IsSelfAdjoint.polarIsometry hA hAT hT` — the partial isometry `U` of `T = U |T|`, a bounded
  real-linear operator.
* `IsSelfAdjoint.polarIsometryEquiv` — for an involution, the isometric part `J` as a semilinear
  isometric equivalence.

## Main results

* `LinearPMap.exists_mem_graph_norm_eq_of_mem_closure`, `LinearPMap.HasCore.mem_closure` — closed
  operators isometric to each other on a common core.
* `IsSelfAdjoint.exists_mem_graph_sqrt_iff`, `IsSelfAdjoint.norm_eq_of_mem_graph_sqrt` —
  `dom |T| = dom T` and `‖|T| x‖ = ‖T x‖`.
* `IsSelfAdjoint.norm_polarIsometry_apply`, `IsSelfAdjoint.polarIsometry_smul_of_isSemilinear` —
  `‖U x‖ = ‖E_A((0, ∞)) x‖`, and `U` is semilinear with `T`.
* `IsSelfAdjoint.polarIsometry_apply_of_mem_graph`, `IsSelfAdjoint.eq_polarIsometry_compPMap` —
  **polar decomposition** `T = U |T|`.
* `IsSelfAdjoint.eq_sqrt_of_eq_compPMap`, `IsSelfAdjoint.eq_polarIsometry_of_eq_compPMap` —
  **uniqueness** of the polar decomposition.
* `IsSelfAdjoint.ker_eq_bot_of_involution`, `IsSelfAdjoint.ker_sqrt_eq_bot_of_involution`,
  `IsSelfAdjoint.pvm_Iic_eq_zero_of_involution`, `IsSelfAdjoint.norm_polarIsometry_of_involution`,
  `IsSelfAdjoint.surjective_polarIsometry_of_involution` — for an involution, `Δ` is injective and
  `J` is an isometry onto `E`.
* `IsSelfAdjoint.polarIsometryEquiv_apply_apply`, `IsSelfAdjoint.polarIsometryEquiv_symm_apply` —
  `J² = 1`.
* `IsSelfAdjoint.mem_graph_inverse_sqrt_iff` — `J Δ^{1/2} J = Δ^{-1/2}` (`LinearPMap.inverse`).
* `IsSelfAdjoint.pvm_transport_polarIsometryEquiv`, `IsSelfAdjoint.polarIsometryEquiv_integral_apply`
  — `J E_Δ J = inv_* E_Δ` and `J f(Δ) J = (σ ∘ f ∘ inv)(Δ)`.

## References

* [K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*][schmudgen2012], §7.1
* [O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*][bratteli1987],
  Proposition 2.5.11
-/

@[expose] public section

open Set Filter Topology MeasureTheory Complex ClosedSubmodule
open scoped InnerProductSpace ComplexConjugate LinearPMap

/-! ### Closed operators isometric on a common core -/

namespace LinearPMap

variable {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- Let `S` be closed, `D` a subspace of its domain on which `‖S x‖ = ‖T x‖`, and `(x, v)` a limit
of points `(d, T d)` with `d ∈ D`. Then `x ∈ dom S` and `‖S x‖ = ‖v‖`. -/
lemma exists_mem_graph_norm_eq_of_mem_closure {S : E →ₗ.[ℝ] F₁} {T : E →ₗ.[ℝ] F₂}
    {D : Submodule ℝ E} (hS : S.IsClosed) (hDS : D ≤ S.domain)
    (hnorm : ∀ d ∈ D, ∀ u w, (d, u) ∈ S.graph → (d, w) ∈ T.graph → ‖u‖ = ‖w‖)
    {x : E} {v : F₂} (hxv : (x, v) ∈ _root_.closure {p : E × F₂ | p.1 ∈ D ∧ p ∈ T.graph}) :
    ∃ u, (x, u) ∈ S.graph ∧ ‖u‖ = ‖v‖ := by
  obtain ⟨p, hp, hpt⟩ := mem_closure_iff_seq_limit.mp hxv
  choose hpD hpT using hp
  set u : ℕ → F₁ := fun n => S ⟨(p n).1, hDS (hpD n)⟩
  have hu : ∀ n, ((p n).1, u n) ∈ S.graph := fun n => S.mem_graph ⟨_, hDS (hpD n)⟩
  have hdist : ∀ m n, dist (u m) (u n) = dist (p m).2 (p n).2 := fun m n => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hnorm _ (D.sub_mem (hpD m) (hpD n)) _ _ (S.graph.sub_mem (hu m) (hu n))
      (T.graph.sub_mem (hpT m) (hpT n))
  have hp2 : Tendsto (fun n => (p n).2) atTop (𝓝 v) := (continuous_snd.tendsto _).comp hpt
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hp2.cauchySeq ε hε
    exact ⟨N, fun m hm n hn => by rw [hdist]; exact hN m hm n hn⟩
  obtain ⟨u₀, hu₀⟩ := cauchySeq_tendsto_of_complete hcau
  have hmem : (x, u₀) ∈ S.graph := by
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
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {T : E →ₗ.[ℝ] F}

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

variable (hAT : A.restrictScalars ℝ = T†.compNat T)
include hAT

omit [CompleteSpace F] in
include hA in
/-- For `A = T†T` and `x ∈ dom A`, `‖A^{1/2} x‖ = ‖T x‖` (in graph form). -/
lemma norm_eq_of_mem_graph_sqrt_of_mem_domain {x : E} (hx : x ∈ A.domain) {u : E} {v : F}
    (hu : (x, u) ∈ hA.sqrt.graph) (hv : (x, v) ∈ T.graph) : ‖u‖ = ‖v‖ := by
  have hpos := hA.isPositive_of_restrictScalars_eq hAT
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  obtain ⟨hux, rfl⟩ := (hA.pvm.mem_graph_integralPMap).mp hu
  have hAx := A.mem_graph ⟨x, hx⟩
  have h₁ := hA.re_inner_eq_norm_sq_of_restrictScalars_eq hAT hAx hv
  rw [hA.inner_eq_integral_of_mem_graph hAx, integral_complex_ofReal, ofReal_re] at h₁
  have h₂ := hA.pvm.norm_integralApply_sq hsq hux
  have h₃ : ∫ t, ‖(Real.sqrt t : ℂ)‖ ^ 2 ∂(hA.pvm.measure x) = ∫ t, t ∂(hA.pvm.measure x) :=
    integral_congr_ae ((hA.ae_nonneg_measure_pvm x hpos).mono fun t ht => by
      simp [Real.sq_sqrt ht])
  rw [h₃, h₁] at h₂
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h₂

omit [CompleteSpace F] in
/-- For `A = T†T`, the domain of `A` lies in that of `T`. -/
lemma domain_le_domain_of_restrictScalars_eq : A.domain.restrictScalars ℝ ≤ T.domain := by
  rw [← LinearPMap.restrictScalars_domain, hAT]
  exact LinearPMap.compNat_domain_le

include hA in
/-- **`dom T = dom |T|`**: for `A = T†T` with `T` closed, `x ∈ dom A^{1/2}` iff `x ∈ dom T`, and
`‖A^{1/2} x‖ = ‖T x‖` there (`IsSelfAdjoint.norm_eq_of_mem_graph_sqrt`). -/
lemma exists_mem_graph_sqrt_iff (hT : T.IsClosed) {x : E} :
    (∃ u, (x, u) ∈ hA.sqrt.graph) ↔ ∃ v, (x, v) ∈ T.graph := by
  have hpos := hA.isPositive_of_restrictScalars_eq hAT
  have hDT := domain_le_domain_of_restrictScalars_eq hAT
  have hTd : Dense (T.domain : Set E) := hA.dense_domain.mono hDT
  have hnorm : ∀ d ∈ A.domain.restrictScalars ℝ, ∀ u w, (d, u) ∈ hA.sqrt.graph →
      (d, w) ∈ T.graph → ‖u‖ = ‖w‖ := fun d hd u w hu hw =>
    hA.norm_eq_of_mem_graph_sqrt_of_mem_domain hAT hd hu hw
  constructor
  · rintro ⟨u, hu⟩
    have hcl := (hA.hasCore_sqrt hpos).mem_closure hu
    have hset : {q : E × E | q.1 ∈ A.domain ∧ q ∈ hA.sqrt.graph} =
        {q : E × E | q.1 ∈ A.domain.restrictScalars ℝ ∧ q ∈ (hA.sqrt.restrictScalars ℝ).graph} := by
      ext q
      exact and_congr Iff.rfl LinearPMap.mem_graph_restrictScalars.symm
    rw [hset] at hcl
    obtain ⟨v, hv, -⟩ := LinearPMap.exists_mem_graph_norm_eq_of_mem_closure hT hDT
      (fun d hd w u hw hu => (hnorm d hd u w (LinearPMap.mem_graph_restrictScalars.mp hu) hw).symm)
      hcl
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    have hcl := (LinearPMap.hasCore_adjoint_compNat_self hT hTd).mem_closure hv
    rw [← hAT] at hcl
    obtain ⟨u, hu, -⟩ := LinearPMap.exists_mem_graph_norm_eq_of_mem_closure
      (LinearPMap.isClosed_restrictScalars_iff.mpr hA.isSelfAdjoint_sqrt.isClosed)
      (fun d hd => hA.domain_le_domain_sqrt hd)
      (fun d hd u w hu hw => hnorm d hd u w (LinearPMap.mem_graph_restrictScalars.mp hu) hw) hcl
    exact ⟨u, LinearPMap.mem_graph_restrictScalars.mp hu⟩

include hA in
/-- **`‖|T| x‖ = ‖T x‖`**: for `A = T†T` with `T` closed, `‖A^{1/2} x‖ = ‖T x‖` (in graph form). -/
lemma norm_eq_of_mem_graph_sqrt (hT : T.IsClosed) {x u : E} {v : F}
    (hu : (x, u) ∈ hA.sqrt.graph) (hv : (x, v) ∈ T.graph) : ‖u‖ = ‖v‖ := by
  have hpos := hA.isPositive_of_restrictScalars_eq hAT
  have hDT := domain_le_domain_of_restrictScalars_eq hAT
  have hTd : Dense (T.domain : Set E) := hA.dense_domain.mono hDT
  have hcl := (LinearPMap.hasCore_adjoint_compNat_self hT hTd).mem_closure hv
  rw [← hAT] at hcl
  obtain ⟨u', hu', hnorm⟩ := LinearPMap.exists_mem_graph_norm_eq_of_mem_closure
    (LinearPMap.isClosed_restrictScalars_iff.mpr hA.isSelfAdjoint_sqrt.isClosed)
    (fun d hd => hA.domain_le_domain_sqrt hd)
    (fun d hd u w hu hw => hA.norm_eq_of_mem_graph_sqrt_of_mem_domain hAT hd
      (LinearPMap.mem_graph_restrictScalars.mp hu) hw) hcl
  have huu : u' = u := sub_eq_zero.mp (hA.sqrt.graph_fst_eq_zero_snd
    (hA.sqrt.graph.sub_mem (LinearPMap.mem_graph_restrictScalars.mp hu') hu) (sub_self x))
  rwa [huu] at hnorm

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
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {T : E →ₗ.[ℝ] F}

/-- The partial isometry `x ↦ lim T (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A(λ)) x` of the polar
decomposition of `T`, for `A = T†T`, as a function; `IsSelfAdjoint.polarIsometry` is the bounded
real-linear operator. -/
noncomputable def polarIsometryFun (T : E →ₗ.[ℝ] F) (x : E) : F :=
  limUnder atTop fun n : ℕ => Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x)

end IsSelfAdjoint

namespace LinearPMap

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Extending a partially defined map by zero does not change it on its domain. -/
lemma mem_graph_extend {T : E →ₗ.[R] F} {v : E} (hv : v ∈ T.domain) :
    (v, Function.extend Subtype.val T 0 v) ∈ T.graph := by
  have h := Subtype.val_injective.extend_apply T 0 ⟨v, hv⟩
  rw [h]
  exact T.mem_graph ⟨v, hv⟩

end LinearPMap

namespace IsSelfAdjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {T : E →ₗ.[ℝ] F}

/-- `A^{1/2} (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A) x = E_A((1/(n+1), ∞)) x`. -/
lemma mem_graph_sqrt_integral_polarCutoff (n : ℕ) (x : E) :
    (hA.pvm.integral (polarCutoff n) x, hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) x) ∈ hA.sqrt.graph := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hb : ∀ t, ‖((Ioi ((n : ℝ) + 1)⁻¹).indicator (1 : ℝ → ℂ)) t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ioi ((n : ℝ) + 1)⁻¹ <;> simp [ht]
  have hmem : MemLp ((fun t : ℝ => (Real.sqrt t : ℂ)) * polarCutoff n) 2 (hA.pvm.measure x) := by
    rw [sqrt_mul_polarCutoff]
    exact hA.pvm.memLp_measure_of_bound (measurable_one.indicator measurableSet_Ioi) hb x
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.mem_graph_integralPMap]
  refine ⟨(hA.pvm.memLp_measure_integral_apply_iff hsq (measurable_polarCutoff n)
    ⟨_, norm_polarCutoff_le n⟩ x).mpr hmem, ?_⟩
  rw [hA.pvm.integralApply_integral_apply hsq (measurable_polarCutoff n) ⟨_, norm_polarCutoff_le n⟩
    hmem, sqrt_mul_polarCutoff, ← hA.pvm.integral_apply (measurable_one.indicator measurableSet_Ioi)
    ⟨1, hb⟩, hA.pvm.integral_indicator_one measurableSet_Ioi]

variable (hAT : A.restrictScalars ℝ = T†.compNat T) (hT : T.IsClosed)
include hAT hT

/-- The approximants `T (∫ 1_{λ > 1/(n+1)} λ^{-1/2} dE_A) x` of the partial isometry. -/
private lemma mem_graph_polarCutoff (n : ℕ) (x : E) :
    (hA.pvm.integral (polarCutoff n) x,
      Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x)) ∈ T.graph := by
  obtain ⟨v, hv⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mp
    ⟨_, hA.mem_graph_sqrt_integral_polarCutoff n x⟩
  exact LinearPMap.mem_graph_extend (LinearPMap.mem_domain_of_mem_graph hv)

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
      (T.graph.sub_mem (hA.mem_graph_polarCutoff hAT hT m x)
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

/-- The value of `T` on the approximating vectors is additive and homogeneous. -/
private lemma extend_polarCutoff_add (n : ℕ) (x y : E) :
    Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) (x + y)) =
      Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x) +
        Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) y) := by
  have h := T.graph.add_mem (hA.mem_graph_polarCutoff hAT hT n x)
    (hA.mem_graph_polarCutoff hAT hT n y)
  rw [Prod.mk_add_mk, ← map_add] at h
  exact sub_eq_zero.mp (T.graph_fst_eq_zero_snd
    (T.graph.sub_mem (hA.mem_graph_polarCutoff hAT hT n (x + y)) h) (sub_self _))

/-- `U` is additive. -/
lemma polarIsometryFun_add (x y : E) :
    hA.polarIsometryFun T (x + y) = hA.polarIsometryFun T x + hA.polarIsometryFun T y := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT (x + y)) ?_
  simp_rw [hA.extend_polarCutoff_add hAT hT]
  exact (hA.tendsto_polarIsometryFun hAT hT x).add (hA.tendsto_polarIsometryFun hAT hT y)

/-- `U` is real-linear. -/
lemma polarIsometryFun_smul (r : ℝ) (x : E) :
    hA.polarIsometryFun T (r • x) = r • hA.polarIsometryFun T x := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT (r • x)) ?_
  have h : ∀ n : ℕ, Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) (r • x)) =
      r • Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x) := fun n => by
    have h := T.graph.smul_mem r (hA.mem_graph_polarCutoff hAT hT n x)
    rw [Prod.smul_mk, ← ContinuousLinearMap.map_smul_of_tower] at h
    exact sub_eq_zero.mp (T.graph_fst_eq_zero_snd
      (T.graph.sub_mem (hA.mem_graph_polarCutoff hAT hT n (r • x)) h) (sub_self _))
  simp_rw [h]
  exact (hA.tendsto_polarIsometryFun hAT hT x).const_smul r

/-- `U` is `σ`-semilinear when `T` is: `U (c x) = σ c U x`. -/
lemma polarIsometryFun_smul_of_isSemilinear {σ : ℂ →+* ℂ} (hσ : LinearPMap.IsSemilinear σ T)
    (c : ℂ) (x : E) : hA.polarIsometryFun T (c • x) = σ c • hA.polarIsometryFun T x := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT (c • x)) ?_
  have h : ∀ n : ℕ, Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) (c • x)) =
      σ c • Function.extend Subtype.val T 0 (hA.pvm.integral (polarCutoff n) x) := fun n => by
    have h := hσ c _ _ (hA.mem_graph_polarCutoff hAT hT n x)
    rw [← map_smul] at h
    exact sub_eq_zero.mp (T.graph_fst_eq_zero_snd
      (T.graph.sub_mem (hA.mem_graph_polarCutoff hAT hT n (c • x)) h) (sub_self _))
  simp_rw [h]
  exact (hA.tendsto_polarIsometryFun hAT hT x).const_smul (σ c)

/-- The **partial isometry** `U` of the polar decomposition `T = U |T|`, for `A = T†T` and `T`
closed: a bounded real-linear operator, isometric on `E_A((0, ∞)) E` and zero on `ker T`
(`IsSelfAdjoint.norm_polarIsometry_apply`), semilinear when `T` is
(`IsSelfAdjoint.polarIsometry_smul_of_isSemilinear`). -/
noncomputable def polarIsometry : E →L[ℝ] F :=
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

/-- `U` is `σ`-semilinear when `T` is. -/
lemma polarIsometry_smul_of_isSemilinear {σ : ℂ →+* ℂ} (hσ : LinearPMap.IsSemilinear σ T)
    (c : ℂ) (x : E) : hA.polarIsometry hAT hT (c • x) = σ c • hA.polarIsometry hAT hT x :=
  hA.polarIsometryFun_smul_of_isSemilinear hAT hT hσ c x

/-! ### The polar decomposition -/

omit hAT hT in
/-- `E_A(s)` maps the domain of `A^{1/2}` into itself and commutes with `A^{1/2}`. -/
lemma mem_graph_sqrt_apply {y u : E} (hu : (y, u) ∈ hA.sqrt.graph) {s : Set ℝ}
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
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.mem_graph_integralPMap] at hu ⊢
  obtain ⟨hy, rfl⟩ := hu
  have hmem : MemLp ((fun t : ℝ => (Real.sqrt t : ℂ)) * s.indicator 1) 2 (hA.pvm.measure y) := by
    rw [hmul]
    exact hy.indicator hs
  rw [← hA.pvm.integral_indicator_one hs]
  refine ⟨(hA.pvm.memLp_measure_integral_apply_iff hsq h1 ⟨1, h1b⟩ y).mpr hmem, ?_⟩
  rw [hA.pvm.integralApply_integral_apply hsq h1 ⟨1, h1b⟩ hmem, hmul,
    hA.pvm.integral_indicator_one hs, hA.pvm.apply_integralApply hsq hs hy]

omit hAT hT in
/-- The range of `A^{1/2}` lies in `E_A((0, ∞)) E`: `E_A((-∞, 0]) A^{1/2} y = 0`. -/
lemma pvm_Iic_apply_of_mem_graph_sqrt {y u : E} (hu : (y, u) ∈ hA.sqrt.graph) :
    hA.pvm (Iic 0) u = 0 := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.mem_graph_integralPMap] at hu
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
lemma integral_polarCutoff_apply_of_mem_graph_sqrt {y u : E} (hu : (y, u) ∈ hA.sqrt.graph)
    (n : ℕ) : hA.pvm.integral (polarCutoff n) u = hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y := by
  have hsq : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hb : ∀ t, ‖((Ioi ((n : ℝ) + 1)⁻¹).indicator (1 : ℝ → ℂ)) t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ioi ((n : ℝ) + 1)⁻¹ <;> simp [ht]
  rw [IsSelfAdjoint.sqrt, ProjectionValuedMeasure.mem_graph_integralPMap] at hu
  obtain ⟨hy, rfl⟩ := hu
  rw [hA.pvm.integral_integralApply hsq (measurable_polarCutoff n) ⟨_, norm_polarCutoff_le n⟩ hy,
    mul_comm, sqrt_mul_polarCutoff, ← hA.pvm.integral_apply
      (measurable_one.indicator measurableSet_Ioi) ⟨1, hb⟩,
    hA.pvm.integral_indicator_one measurableSet_Ioi]

/-- **Polar decomposition**, pointwise: `U (|T| y) = T y` (in graph form). -/
lemma polarIsometry_apply_of_mem_graph {y u : E} {v : F} (hu : (y, u) ∈ hA.sqrt.graph)
    (hv : (y, v) ∈ T.graph) : hA.polarIsometry hAT hT u = v := by
  refine tendsto_nhds_unique (hA.tendsto_polarIsometryFun hAT hT u) ?_
  simp_rw [hA.integral_polarCutoff_apply_of_mem_graph_sqrt hu]
  -- `E_A(s_n) y ∈ dom T`, with `T E_A(s_n) y → T y`
  have hmem : ∀ n : ℕ, (hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y,
      Function.extend Subtype.val T 0 (hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y)) ∈ T.graph := fun n => by
    obtain ⟨w, hw⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mp
      ⟨_, hA.mem_graph_sqrt_apply hu measurableSet_Ioi⟩
    exact LinearPMap.mem_graph_extend (LinearPMap.mem_domain_of_mem_graph hw)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n : ℕ, ‖Function.extend Subtype.val T 0 (hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) y) - v‖ =
      ‖hA.pvm (Ioi ((n : ℝ) + 1)⁻¹) u - u‖ := fun n =>
    (hA.norm_eq_of_mem_graph_sqrt hAT hT
      (hA.sqrt.graph.sub_mem (hA.mem_graph_sqrt_apply hu measurableSet_Ioi) hu)
      (T.graph.sub_mem (hmem n) hv)).symm
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
    T = (hA.polarIsometry hAT hT : E →ₗ[ℝ] F).compPMap (hA.sqrt.restrictScalars ℝ) := by
  refine LinearPMap.ext ?_ fun y hy hy' => ?_
  · ext y
    change y ∈ T.domain ↔ y ∈ hA.sqrt.domain
    constructor
    · intro hy
      obtain ⟨u, hu⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mpr ⟨_, T.mem_graph ⟨y, hy⟩⟩
      exact LinearPMap.mem_domain_of_mem_graph hu
    · intro hy
      obtain ⟨v, hv⟩ := (hA.exists_mem_graph_sqrt_iff hAT hT).mp ⟨_, hA.sqrt.mem_graph ⟨y, hy⟩⟩
      exact LinearPMap.mem_domain_of_mem_graph hv
  · change T ⟨y, hy⟩ = hA.polarIsometry hAT hT (hA.sqrt ⟨y, hy'⟩)
    exact (hA.polarIsometry_apply_of_mem_graph hAT hT (hA.sqrt.mem_graph ⟨y, hy'⟩)
      (T.mem_graph ⟨y, hy⟩)).symm

omit hT [CompleteSpace F] in
/-- **Uniqueness of the positive part of the polar decomposition**: if `T = V B` with `B` positive
self-adjoint and `V` a real-linear map isometric on the range of `B`, then `B = |T| = (T†T)^{1/2}`.
-/
theorem eq_sqrt_of_eq_compPMap {B : E →ₗ.[ℂ] E} (hB : IsSelfAdjoint B) (hBpos : B.IsPositive)
    (V : E →L[ℝ] F) (hV : ∀ x y, (x, y) ∈ B.graph → ‖V y‖ = ‖y‖)
    (hTVB : T = (V : E →ₗ[ℝ] F).compPMap (B.restrictScalars ℝ)) : B = hA.sqrt := by
  have hTd : Dense (T.domain : Set E) :=
    hA.dense_domain.mono (domain_le_domain_of_restrictScalars_eq hAT)
  -- the graph of `T = V B`
  have hgraph : ∀ a b, (a, b) ∈ T.graph ↔ ∃ c, (a, c) ∈ B.graph ∧ V c = b := fun a b => by
    rw [hTVB, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨⟨a', ha'⟩, rfl, rfl⟩
      exact ⟨B ⟨a', ha'⟩, B.mem_graph ⟨a', ha'⟩, rfl⟩
    · rintro ⟨c, hac, rfl⟩
      obtain ⟨⟨a', ha'⟩, rfl, rfl⟩ := (LinearPMap.mem_graph_iff B).mp hac
      exact ⟨⟨a', ha'⟩, rfl, rfl⟩
  -- `B B ⊆ T†T = A`
  have hle : B.compNat B ≤ A := by
    refine LinearPMap.le_of_le_graph fun ⟨x, z⟩ hxz => ?_
    obtain ⟨w, hxw, hwz⟩ := LinearPMap.mem_graph_compNat.mp hxz
    rw [← LinearPMap.mem_graph_restrictScalars (R := ℝ), hAT, LinearPMap.mem_graph_compNat]
    refine ⟨V w, (hgraph x (V w)).mpr ⟨w, hxw, rfl⟩, ?_⟩
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint hTd, Submodule.mem_adjoint_iff]
    intro a b hab
    obtain ⟨c, hac, rfl⟩ := (hgraph a b).mp hab
    have h := hB.isFormalAdjoint.inner_eq_of_mem_graph hac hwz
    have hVi : inner ℝ (V c) (V w) = inner ℝ c w := by
      rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
        real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
        hV _ _ (B.graph.add_mem hac hxw), hV _ _ hac, hV _ _ hxw]
    rw [hVi, inner_real_eq_re_inner, inner_real_eq_re_inner, h, sub_self]
  -- `B B` is self-adjoint
  have hsa : IsSelfAdjoint (B.compNat B) := by
    have hid : Measurable fun t : ℝ => (t : ℂ) := Complex.measurable_ofReal
    have h := hB.eq_integralPMap_pvm
    rw [h, hB.pvm.compNat_integralPMap hid hid fun y hy => memLp_of_memLp_mul_self hid hy]
    exact hB.pvm.isSelfAdjoint_integralPMap (hid.mul hid) fun t => by simp
  exact hA.eq_sqrt_of_compNat_self_eq hB hBpos (IsSelfAdjoint.eq_of_le hsa hA.isFormalAdjoint hle).symm

omit hAT hT in
/-- The kernel of `A^{1/2}` contains the spectral subspace of `(-∞, 0]`. -/
lemma mem_graph_sqrt_pvm_Iic_apply_zero (x : E) : (hA.pvm (Iic 0) x, 0) ∈ hA.sqrt.graph := by
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
    ProjectionValuedMeasure.mem_graph_integralPMap]
  refine ⟨(hA.pvm.memLp_measure_integral_apply_iff hsq hg hgb x).mpr hmem, ?_⟩
  rw [hA.pvm.integralApply_integral_apply hsq hg hgb hmem, hzero,
    ← hA.pvm.integral_apply measurable_const ⟨0, fun _ => norm_zero.le⟩,
    ProjectionValuedMeasure.integral_const,
    zero_smul, zero_apply]

/-- **Uniqueness of the polar decomposition**: if `T = V B` with `B` positive self-adjoint and `V` a
real-linear map isometric on the range of `B` and vanishing on `ker B`, then `B = |T|`
(`IsSelfAdjoint.eq_sqrt_of_eq_compPMap`) and `V = U` is the partial isometry. -/
theorem eq_polarIsometry_of_eq_compPMap {B : E →ₗ.[ℂ] E} (hB : IsSelfAdjoint B)
    (hBpos : B.IsPositive) (V : E →L[ℝ] F) (hV : ∀ x y, (x, y) ∈ B.graph → ‖V y‖ = ‖y‖)
    (hVker : ∀ x, (x, 0) ∈ B.graph → V x = 0)
    (hTVB : T = (V : E →ₗ[ℝ] F).compPMap (B.restrictScalars ℝ)) :
    V = hA.polarIsometry hAT hT := by
  obtain rfl := hA.eq_sqrt_of_eq_compPMap hAT hB hBpos V hV hTVB
  set U := hA.polarIsometry hAT hT
  set P := hA.pvm
  -- `V = U` on `E_A((0, ∞)) E`, as limits on the ranges of `E_A((1/(n+1), ∞))`
  have hIoi : ∀ x, V (P (Ioi 0) x) = U (P (Ioi 0) x) := fun x => by
    have hn : ∀ n : ℕ, V (P (Ioi ((n : ℝ) + 1)⁻¹) x) = U (P (Ioi ((n : ℝ) + 1)⁻¹) x) := fun n => by
      have hu := hA.mem_graph_sqrt_integral_polarCutoff n x
      have hv : (P.integral (polarCutoff n) x, V (P (Ioi ((n : ℝ) + 1)⁻¹) x)) ∈ T.graph := by
        rw [hTVB, LinearPMap.mem_graph_compPMap]
        exact ⟨_, LinearPMap.mem_graph_restrictScalars.mpr hu, rfl⟩
      exact (hA.polarIsometry_apply_of_mem_graph hAT hT hu hv).symm
    exact tendsto_nhds_unique ((V.continuous.tendsto _).comp (hA.tendsto_pvm_Ioi_inv x))
      (((U.continuous.tendsto _).comp (hA.tendsto_pvm_Ioi_inv x)).congr fun n => (hn n).symm)
  -- both vanish on `E_A((-∞, 0]) E ⊆ ker A^{1/2}`
  have hIic : ∀ x, V (P (Iic 0) x) = U (P (Iic 0) x) := fun x => by
    rw [hVker _ (hA.mem_graph_sqrt_pvm_Iic_apply_zero x), eq_comm, ← norm_eq_zero,
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

end IsSelfAdjoint

/-! ### Involutions -/

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {S : E →ₗ.[ℝ] E}
  (hAS : A.restrictScalars ℝ = S†.compNat S) (hS : S.IsClosed)
  (hinv : ∀ x v, (x, v) ∈ S.graph → (v, x) ∈ S.graph)
include hAS hS hinv

omit hS in
include hA in
/-- For an involution `S` (its graph is invariant under the flip), `A = S†S` is injective. -/
lemma ker_eq_bot_of_involution : A.ker = ⊥ := by
  refine LinearPMap.ker_eq_bot_iff_mem_graph.mpr fun x hx => ?_
  have hSd : Dense (S.domain : Set E) :=
    hA.dense_domain.mono (domain_le_domain_of_restrictScalars_eq hAS)
  rw [← LinearPMap.mem_graph_restrictScalars (R := ℝ), hAS,
    LinearPMap.mem_graph_adjoint_compNat_self_zero_iff hSd] at hx
  exact S.graph_fst_eq_zero_snd (hinv x 0 hx) rfl

omit hS in
include hA in
/-- For an involution `S`, the projection-valued measure of `A = S†S` lives on `(0, ∞)`. -/
lemma pvm_Iic_eq_zero_of_involution : hA.pvm (Iic 0) = 0 :=
  (hA.pvm.apply_eq_zero_iff measurableSet_Iic).mpr fun y =>
    hA.measure_pvm_Iic_zero (hA.isPositive_of_restrictScalars_eq hAS)
      (hA.ker_eq_bot_of_involution hAS hinv) y

omit hS in
include hA in
/-- For an involution `S`, `|S| = A^{1/2}` is injective. -/
lemma ker_sqrt_eq_bot_of_involution : hA.sqrt.ker = ⊥ :=
  hA.pvm.ker_integralPMap_eq_bot (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)
    fun y => (measure_eq_zero_iff_ae_notMem.mp (hA.measure_pvm_Iic_zero
      (hA.isPositive_of_restrictScalars_eq hAS) (hA.ker_eq_bot_of_involution hAS hinv) y)).mono
      fun _ ht => ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (not_le.mp ht)).ne'

omit hS in
include hA in
/-- For an involution `S`, `E_A((0, ∞)) = 1`. -/
lemma pvm_Ioi_eq_one_of_involution : hA.pvm (Ioi 0) = 1 := by
  have h := hA.pvm.apply_union (Set.Iic_disjoint_Ioi (le_refl (0 : ℝ))).symm measurableSet_Ioi
    measurableSet_Iic
  rwa [Ioi_union_Iic, ProjectionValuedMeasure.apply_univ,
    hA.pvm_Iic_eq_zero_of_involution hAS hinv, add_zero, eq_comm] at h

include hA in
/-- For an involution `S`, the partial isometry of `S = U |S|` is an isometry. -/
lemma norm_polarIsometry_of_involution (x : E) : ‖hA.polarIsometry hAS hS x‖ = ‖x‖ := by
  rw [hA.norm_polarIsometry_apply hAS hS, hA.pvm_Ioi_eq_one_of_involution hAS hinv,
    one_apply_eq_self]

include hA in
/-- For an involution `S`, the partial isometry of `S = U |S|` is surjective. -/
lemma surjective_polarIsometry_of_involution : Function.Surjective (hA.polarIsometry hAS hS) := by
  have hSd : Dense (S.domain : Set E) :=
    hA.dense_domain.mono (domain_le_domain_of_restrictScalars_eq hAS)
  set Ui : E →ₗᵢ[ℝ] E :=
    { toLinearMap := hA.polarIsometry hAS hS, norm_map' := hA.norm_polarIsometry_of_involution hAS hS hinv }
  have hcl : IsClosed (range (hA.polarIsometry hAS hS)) :=
    Ui.antilipschitzWith.isClosed_range Ui.isometry.uniformContinuous
  -- the domain of `S` lies in the range: `x = S (S x) = U (|S| (S x))`
  have hsub : (S.domain : Set E) ⊆ range (hA.polarIsometry hAS hS) := fun x hx => by
    have hxv := S.mem_graph ⟨x, hx⟩
    have hvx := hinv _ _ hxv
    obtain ⟨u, hu⟩ := (hA.exists_mem_graph_sqrt_iff hAS hS).mpr ⟨_, hvx⟩
    exact ⟨u, hA.polarIsometry_apply_of_mem_graph hAS hS hu hvx⟩
  rw [← range_eq_univ, ← hcl.closure_eq]
  exact (hSd.mono hsub).closure_eq

omit [CompleteSpace E] hAS hS hinv in
/-- `(g ∘ f)ℝ = gℝ ∘ fℝ`: restriction of scalars commutes with composition. -/
private lemma restrictScalars_compNat (g f : E →ₗ.[ℂ] E) :
    (g.compNat f).restrictScalars ℝ = (g.restrictScalars ℝ).compNat (f.restrictScalars ℝ) :=
  LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨x, z⟩ => by
    simp only [LinearPMap.mem_graph_restrictScalars, LinearPMap.mem_graph_compNat])

variable {σ σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (hσ : LinearPMap.IsSemilinear σ S)

/-- The **isometric part** `J` of the polar decomposition `S = J |S|` of a `σ`-semilinear closed
involution `S`, as a semilinear isometric equivalence. -/
noncomputable def polarIsometryEquiv : E ≃ₛₗᵢ[σ] E :=
  LinearIsometryEquiv.ofSurjective
    { toFun := hA.polarIsometry hAS hS
      map_add' := map_add _
      map_smul' := hA.polarIsometry_smul_of_isSemilinear hAS hS hσ
      norm_map' := hA.norm_polarIsometry_of_involution hAS hS hinv }
    (hA.surjective_polarIsometry_of_involution hAS hS hinv)

/-- `J` is the partial isometry of the polar decomposition. -/
lemma polarIsometryEquiv_apply (x : E) :
    hA.polarIsometryEquiv hAS hS hinv hσ x = hA.polarIsometry hAS hS x := rfl

/-- `S x = J |S| x` (in graph form). -/
private lemma mem_graph_of_mem_graph_sqrt_of_involution {x u : E} (hu : (x, u) ∈ hA.sqrt.graph) :
    (x, hA.polarIsometryEquiv hAS hS hinv hσ u) ∈ S.graph := by
  obtain ⟨v, hv⟩ := (hA.exists_mem_graph_sqrt_iff hAS hS).mp ⟨u, hu⟩
  rwa [polarIsometryEquiv_apply, hA.polarIsometry_apply_of_mem_graph hAS hS hu hv]

/-- From `S = J |S|` and `S² = 1`: `|S| J u = J⁻¹ x` for `|S| x = u` (in graph form). -/
private lemma mem_graph_sqrt_polarIsometryEquiv {x u : E} (hu : (x, u) ∈ hA.sqrt.graph) :
    (hA.polarIsometryEquiv hAS hS hinv hσ u, (hA.polarIsometryEquiv hAS hS hinv hσ).symm x) ∈
      hA.sqrt.graph := by
  set J := hA.polarIsometryEquiv hAS hS hinv hσ
  have h₁ := hinv _ _ (hA.mem_graph_of_mem_graph_sqrt_of_involution hAS hS hinv hσ hu)
  obtain ⟨w, hw⟩ := (hA.exists_mem_graph_sqrt_iff hAS hS).mpr ⟨_, h₁⟩
  have h₂ := hA.mem_graph_of_mem_graph_sqrt_of_involution hAS hS hinv hσ hw
  have hx : J w = x := sub_eq_zero.mp (S.graph_fst_eq_zero_snd (S.graph.sub_mem h₂ h₁) (sub_self _))
  rwa [← hx, LinearIsometryEquiv.symm_apply_apply]

/-- **`J² = 1`** for the isometric part of a `σ`-semilinear closed involution `S = J |S|`. -/
theorem polarIsometryEquiv_apply_apply [RingHomIsometric σ] (x : E) :
    hA.polarIsometryEquiv hAS hS hinv hσ (hA.polarIsometryEquiv hAS hS hinv hσ x) = x := by
  set J := hA.polarIsometryEquiv hAS hS hinv hσ
  set E' := hA.pvm
  have hpos := hA.isPositive_of_restrictScalars_eq hAS
  have hc : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hc0 : ∀ y, ∀ᵐ t ∂(E'.measure y), (Real.sqrt t : ℂ) ≠ 0 := fun y => by
    have h := measure_eq_zero_iff_ae_notMem.mp (hA.measure_pvm_Iic_zero hpos
      (hA.ker_eq_bot_of_involution hAS hinv) y)
    exact h.mono fun t ht => ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (not_le.mp ht)).ne'
  -- `P = J |S|⁻¹ J⁻¹`, the transported inverse of `|S|`
  set P := (E'.transport J).integralPMap fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
  have hcinv : Measurable fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable.inv
  have hP : ∀ y z, (y, z) ∈ P.graph ↔ (J.symm z, J.symm y) ∈ hA.sqrt.graph := fun y z => by
    rw [ProjectionValuedMeasure.mem_graph_integralPMap_transport _ _ hcinv]
    simp_rw [RingHom.apply_ofReal_of_ringHomInvPair σ, ofReal_inv]
    rw [E'.integralPMap_inv hc hc0]
    exact LinearPMap.mem_graph_inverse_iff (E'.ker_integralPMap_eq_bot hc hc0)
  have hPsa : IsSelfAdjoint P :=
    (E'.transport J).isSelfAdjoint_integralPMap_ofReal Real.continuous_sqrt.measurable.inv
  have hPpos : P.IsPositive :=
    (E'.transport J).isPositive_integralPMap_ofReal Real.continuous_sqrt.measurable.inv
      fun t => inv_nonneg.mpr (Real.sqrt_nonneg t)
  -- `|S| = W P` with the real isometry `W = J⁻¹ J⁻¹`
  have hJr : ∀ (r : ℝ) (x : E), J.symm (r • x) = r • J.symm x := fun r x => by
    rw [← Complex.coe_smul, J.symm.map_smulₛₗ, RingHom.apply_ofReal_of_ringHomInvPair σ, Complex.coe_smul]
  let Wl : E →ₗ[ℝ] E :=
    { toFun := fun x => J.symm (J.symm x)
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp only [RingHom.id_apply, hJr] }
  let W : E →L[ℝ] E := Wl.mkContinuous 1 fun x => by simp [Wl]
  have hW : ∀ x, ‖W x‖ = ‖x‖ := fun x => by simp [W, Wl]
  have hCP : ∀ x u, (x, u) ∈ hA.sqrt.graph ↔ ∃ z, (x, z) ∈ P.graph ∧ W z = u := fun x u => by
    constructor
    · intro hu
      refine ⟨J (J u), (hP _ _).mpr ?_, by simp [W, Wl]⟩
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hσ hu
    · rintro ⟨z, hz, rfl⟩
      have h := hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hσ ((hP _ _).mp hz)
      rwa [LinearIsometryEquiv.apply_symm_apply] at h
  have hCWP : hA.sqrt.restrictScalars ℝ = (W : E →ₗ[ℝ] E).compPMap (P.restrictScalars ℝ) := by
    refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨x, u⟩ => ?_)
    rw [LinearPMap.mem_graph_restrictScalars, hCP, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨⟨x', hx'⟩, rfl, rfl⟩ := (LinearPMap.mem_graph_iff P).mp hz
      exact ⟨⟨x', hx'⟩, rfl, rfl⟩
    · rintro ⟨⟨x', hx'⟩, rfl, rfl⟩
      exact ⟨P ⟨x', hx'⟩, P.mem_graph ⟨x', hx'⟩, rfl⟩
  -- `A = |S|†|S|` as real operators
  have hAC : A.restrictScalars ℝ =
      (hA.sqrt.restrictScalars ℝ)†.compNat (hA.sqrt.restrictScalars ℝ) := by
    rw [LinearPMap.adjoint_restrictScalars hA.isSelfAdjoint_sqrt.dense_domain,
      LinearPMap.isSelfAdjoint_def.mp hA.isSelfAdjoint_sqrt, ← restrictScalars_compNat,
      hA.sqrt_compNat_sqrt hpos]
  have hPC : P = hA.sqrt := hA.eq_sqrt_of_eq_compPMap hAC hPsa hPpos W (fun _ y _ => hW y) hCWP
  -- `J (J u) = u` on the range of `|S|`, which is dense
  have hJJ : ∀ x u, (x, u) ∈ hA.sqrt.graph → J (J u) = u := fun x u hu => by
    have h := (hCP x u).mp hu
    have h' : (x, J (J u)) ∈ hA.sqrt.graph := by
      rw [← hPC, hP, LinearIsometryEquiv.symm_apply_apply]
      exact hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hσ hu
    exact sub_eq_zero.mp (hA.sqrt.graph_fst_eq_zero_snd (hA.sqrt.graph.sub_mem h' hu) (sub_self _))
  have hall : ∀ y, J (J y) = y := fun y => by
    have hclosed : IsClosed {u : E | J (J u) = u} :=
      isClosed_eq (J.continuous.comp J.continuous) continuous_id
    have hlim := hA.tendsto_pvm_Ioi_inv y
    rw [hA.pvm_Ioi_eq_one_of_involution hAS hinv, one_apply_eq_self] at hlim
    exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n =>
      hJJ _ _ (hA.mem_graph_sqrt_integral_polarCutoff n y))
  exact hall x

/-- `J⁻¹ = J`. -/
lemma polarIsometryEquiv_symm_apply [RingHomIsometric σ] (x : E) :
    (hA.polarIsometryEquiv hAS hS hinv hσ).symm x = hA.polarIsometryEquiv hAS hS hinv hσ x := by
  conv_lhs => rw [← hA.polarIsometryEquiv_apply_apply hAS hS hinv hσ x]
  exact LinearIsometryEquiv.symm_apply_apply _ _

/-- `J |S| J = |S|⁻¹` in graph form: `|S| x = u` iff `|S| (J u) = J x`. -/
private lemma mem_graph_sqrt_polarIsometryEquiv_swap [RingHomIsometric σ] {x u : E} :
    (x, u) ∈ hA.sqrt.graph ↔
      (hA.polarIsometryEquiv hAS hS hinv hσ u, hA.polarIsometryEquiv hAS hS hinv hσ x) ∈
        hA.sqrt.graph := by
  constructor
  · intro hu
    have h := hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hσ hu
    rwa [polarIsometryEquiv_symm_apply] at h
  · intro hu
    have h := hA.mem_graph_sqrt_polarIsometryEquiv hAS hS hinv hσ hu
    rwa [polarIsometryEquiv_symm_apply, polarIsometryEquiv_apply_apply,
      polarIsometryEquiv_apply_apply] at h

/-- **`J |S| J = |S|⁻¹`** for a `σ`-semilinear closed involution `S = J |S|`. For the Tomita
operator this is `J Δ^{1/2} J = Δ^{-1/2}`. -/
theorem mem_graph_inverse_sqrt_iff [RingHomIsometric σ] {x u : E} :
    (x, u) ∈ hA.sqrt.inverse.graph ↔
      (hA.polarIsometryEquiv hAS hS hinv hσ x, hA.polarIsometryEquiv hAS hS hinv hσ u) ∈
        hA.sqrt.graph := by
  rw [LinearPMap.mem_graph_inverse_iff (hA.ker_sqrt_eq_bot_of_involution hAS hinv)]
  exact hA.mem_graph_sqrt_polarIsometryEquiv_swap hAS hS hinv hσ

/-- **`J Δ J = Δ⁻¹`** for a `σ`-semilinear closed involution `S = J Δ^{1/2}` with `Δ = S†S`, in
spectral form: transporting `E_Δ` along `J` gives its image under `λ ↦ λ⁻¹`. -/
lemma pvm_transport_polarIsometryEquiv [RingHomIsometric σ] :
    hA.pvm.transport (hA.polarIsometryEquiv hAS hS hinv hσ) = hA.pvm.map (fun t => t⁻¹)
      measurable_inv := by
  set J := hA.polarIsometryEquiv hAS hS hinv hσ
  set E' := hA.pvm
  have hpos := hA.isPositive_of_restrictScalars_eq hAS
  have hc : Measurable fun t : ℝ => (Real.sqrt t : ℂ) :=
    Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hpos' : ∀ y, ∀ᵐ t ∂(E'.measure y), 0 < t := fun y =>
    (measure_eq_zero_iff_ae_notMem.mp (hA.measure_pvm_Iic_zero hpos
      (hA.ker_eq_bot_of_involution hAS hinv) y)).mono
      fun t ht => not_le.mp ht
  have hc0 : ∀ y, ∀ᵐ t ∂(E'.measure y), (Real.sqrt t : ℂ) ≠ 0 := fun y =>
    (hpos' y).mono fun t ht => ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have hsqrt := Real.continuous_sqrt.measurable
  -- `|S|⁻¹ = J |S| J` as a graph relation, then as projection-valued measures
  have hCi := E'.isSelfAdjoint_integralPMap_ofReal hsqrt.inv
  have hgraph : ∀ u x, (u, x) ∈ (E'.integralPMap fun t => (((Real.sqrt t)⁻¹ : ℝ) : ℂ)).graph ↔
      (J u, J x) ∈ hA.sqrt.graph := fun u x => by
    simp_rw [ofReal_inv]
    rw [E'.integralPMap_inv hc hc0]
    exact hA.mem_graph_inverse_sqrt_iff hAS hS hinv hσ
  have h₁ := hCi.pvm_eq_transport hA.isSelfAdjoint_sqrt J hgraph
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
  have hJJ := hA.polarIsometryEquiv_apply_apply hAS hS hinv hσ
  conv_lhs => rw [h₂]
  exact ProjectionValuedMeasure.transport_transport _ _ hJJ

/-- **`J f(Δ) J = (σ ∘ f ∘ inv)(Δ)`** for bounded measurable `f`, for a `σ`-semilinear closed
involution `S = J Δ^{1/2}` with `Δ = S†S`. For the Tomita operator (`σ` the conjugation) and
`f(λ) = λ^{it}` this is `J Δ^{it} J = Δ^{it}`. -/
lemma polarIsometryEquiv_integral_apply [RingHomIsometric σ] {f : ℝ → ℂ} (hf : Measurable f)
    (hfb : ∃ C, ∀ t, ‖f t‖ ≤ C) (y : E) :
    hA.polarIsometryEquiv hAS hS hinv hσ (hA.pvm.integral f (hA.polarIsometryEquiv hAS hS hinv hσ y))
      = hA.pvm.integral (fun t => σ (f t⁻¹)) y := by
  set J := hA.polarIsometryEquiv hAS hS hinv hσ
  have hσc : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun _ => RingHomIsometric.norm_map).continuous
  obtain ⟨C, hC⟩ := hfb
  have hg : Measurable fun t => σ (f t) := hσc.measurable.comp hf
  have hgb : ∃ C, ∀ t, ‖σ (f t)‖ ≤ C := ⟨C, fun t => by rw [RingHomIsometric.norm_map]; exact hC t⟩
  have h := congrArg (fun T => T y) (hA.pvm.integral_transport J hg hgb)
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, RingHomInvPair.comp_apply_eq] at h
  rw [hA.pvm_transport_polarIsometryEquiv hAS hS hinv hσ,
    ProjectionValuedMeasure.integral_map hg hgb measurable_inv hA.pvm,
    hA.polarIsometryEquiv_symm_apply hAS hS hinv hσ] at h
  exact h.symm

end IsSelfAdjoint
