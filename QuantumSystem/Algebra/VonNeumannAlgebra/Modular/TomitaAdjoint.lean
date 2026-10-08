/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.StandardSubspace
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The adjoint of the Tomita operator

Let `ξ` be cyclic and separating for a von Neumann algebra `M` and `η` cyclic for `M`, with
relative Tomita operators `S_{η,ξ} : x ξ ↦ x⋆ η` (`x ∈ M`) and `F_{η,ξ} : x′ ξ ↦ x′⋆ η`
(`x′ ∈ M′`; `VonNeumannAlgebra.relativeTomita`, where the support projections are `1`). Then
`S_{η,ξ}† = F̄_{η,ξ}` (`VonNeumannAlgebra.adjoint_relativeTomita_eq_closure_commutant`;
Bratteli–Robinson, Proposition 2.5.11, for `η = ξ`). The inclusion `F ⊆ S†` is
`VonNeumannAlgebra.relativeTomita_commutant_le_adjoint`. For the converse let `(φ, ψ)` be in the
graph of `S†`, so that `⟪ψ, x ξ⟫ = ⟪η, x φ⟫` for `x ∈ M`. The operator `Q : x ξ ↦ x φ` on `M ξ`
commutes with `M`, and `(y η, y ψ)` lies in the graph of `Q†` for `y ∈ M`; as `η` is cyclic, `Q`
is closable, with `Q̄† η = ψ`. The closure `Q̄` and the positive self-adjoint `A = Q̄† Q̄` commute
with every unitary of `M`, hence so do the spectral projections `E_n = E_A({|λ| ≤ n})`
(`IsSelfAdjoint.pvm_eq_transport`), and the bounded operators `y_n = Q̄ E_n` lie in `M′`
(`VonNeumannAlgebra.mem_commutant_of_forall_unitary`). Finally `y_n ξ → Q̄ ξ = φ`, since
`‖Q̄ v‖ = ‖A^{1/2} v‖` (`IsSelfAdjoint.norm_eq_of_mem_graph_sqrt`) and `A^{1/2}` commutes with
`E_n`, and `y_n⋆ η = E_n Q̄† η = E_n ψ → ψ`. Thus `(φ, ψ)` is a limit of points `(y_n ξ, y_n⋆ η)`
of the graph of `F`.

For `η = ξ` this gives that the standard subspace of the commutant is the symplectic complement,
`H_{M′} = (H_M)'` (`VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp`).

## Main results

* `VonNeumannAlgebra.adjoint_relativeTomita_eq_closure_commutant`,
  `VonNeumannAlgebra.adjoint_relativeTomita_commutant_eq_closure` — `S_{η,ξ}† = F̄_{η,ξ}`, and
  `F_{η,ξ}† = S̄_{η,ξ}` when `η` is also separating.
* `VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp` — `H_{M′} = (H_M)'`.

## TODO

* `S_{η,ξ}† = F̄_{η,ξ}` for arbitrary vectors (Araki 1976; Araki–Masuda 1982, §2). When `ξ` is not
  cyclic and separating or `η` is not cyclic, the argument has to be cut down by the supports:
  `Q : x ξ ↦ x s(ξ) φ` on `M ξ`, extended by `0` on `[M ξ]ᗮ` (the range of `1 - s′(ξ)`,
  `s′(ξ) ∈ M′`), with `(y η, y s′(ξ) ψ)` in the graph of `Q†`; closability of `Q` then needs the
  density of `M η + [M η]ᗮ` together with a bound on the part of `Q†` off `[M η]`, and the
  approximants `y_n` have to be compressed by `s′(ξ)`.

## References

* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, Springer
  (1987), Proposition 2.5.11
* H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976), 809–833
* H. Araki, T. Masuda, *Positive cones and Lp-spaces for von Neumann algebras*, Publ. RIMS 18
  (1982), 339–411, §2
-/

@[expose] public section

open Set Filter Topology Complex ClosedSubmodule MeasureTheory
open scoped InnerProductSpace ComplexConjugate VonNeumannAlgebra LinearPMap StandardSubspace
open scoped InnerProduct
open InnerProductSpace (cyclicSubspace IsCyclicVector IsSeparatingVector)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-! ### Bounded approximants of a closed operator -/

section Approximation

variable {Q : H →ₗ.[ℝ] H} {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
  (hAQ : A.restrictScalars ℝ = Q†.compNat Q)

/-- The spectral cutoff sets `{λ | |λ| ≤ n}`. -/
private abbrev cutoffSet (n : ℕ) : Set ℝ := {t | ‖(t : ℂ)‖ ≤ n}

private lemma measurableSet_cutoffSet (n : ℕ) : MeasurableSet (cutoffSet n) :=
  measurableSet_le Complex.measurable_ofReal.norm measurable_const

include hAQ in
/-- `E_A({|λ| ≤ n}) v` lies in the domain of `A`, hence of `Q`. -/
private lemma pvm_cutoffSet_mem_domain (n : ℕ) (v : H) : hA.pvm (cutoffSet n) v ∈ Q.domain :=
  IsSelfAdjoint.domain_le_domain_of_restrictScalars_eq hAQ
    (hA.mem_domain_iff_memLp.mpr (hA.pvm.memLp_measure_apply_cutoff Complex.measurable_ofReal n v))

include hAQ in
/-- `‖Q E_n v‖² ≤ n ‖v‖²`: `‖Q z‖² = re ⟪z, A z⟫ = ∫ λ dE_z(λ)` and `E_z` lives on `|λ| ≤ n`. -/
private lemma norm_apply_pvm_cutoffSet_le (n : ℕ) (v : H) :
    ‖Q ⟨hA.pvm (cutoffSet n) v, pvm_cutoffSet_mem_domain hA hAQ n v⟩‖ ≤ Real.sqrt n * ‖v‖ := by
  set z := hA.pvm (cutoffSet n) v
  have hzA : z ∈ A.domain :=
    hA.mem_domain_iff_memLp.mpr (hA.pvm.memLp_measure_apply_cutoff Complex.measurable_ofReal n v)
  have hgA := A.mem_graph ⟨z, hzA⟩
  have hsq := hA.re_inner_eq_norm_sq_of_restrictScalars_eq hAQ hgA
    (Q.mem_graph ⟨z, pvm_cutoffSet_mem_domain hA hAQ n v⟩)
  rw [hA.inner_eq_integral_of_mem_graph hgA, integral_complex_ofReal, ofReal_re,
    hA.pvm.measure_apply_eq_restrict (measurableSet_cutoffSet n)] at hsq
  have hbound : ∫ t : ℝ, t ∂((hA.pvm.measure v).restrict (cutoffSet n)) ≤ n * ‖v‖ ^ 2 := by
    have hae : ∀ᵐ t : ℝ ∂((hA.pvm.measure v).restrict (cutoffSet n)), t ≤ (n : ℝ) :=
      (ae_restrict_iff' (measurableSet_cutoffSet n)).mpr (ae_of_all _ fun t ht =>
        (le_abs_self t).trans (by simpa using ht))
    calc ∫ t, t ∂((hA.pvm.measure v).restrict (cutoffSet n))
        ≤ ∫ _t, (n : ℝ) ∂((hA.pvm.measure v).restrict (cutoffSet n)) := by
          refine integral_mono_ae ?_ (integrable_const _) hae
          refine Integrable.of_bound (by fun_prop) (n : ℝ) ?_
          exact (ae_restrict_iff' (measurableSet_cutoffSet n)).mpr (ae_of_all _ fun t ht => by
            simpa [Real.norm_eq_abs] using ht)
      _ = n * (hA.pvm.measure v).real (cutoffSet n) := by
          rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm]
      _ ≤ n * ‖v‖ ^ 2 := by
          gcongr
          rw [← hA.pvm.measureReal_univ v]
          exact measureReal_mono (subset_univ _)
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (hsq ▸ hbound)

variable (hQl : Q.IsSemilinear (RingHom.id ℂ))

include hAQ hQl in
/-- The bounded operators `y_n = Q E_A({|λ| ≤ n})`. -/
private noncomputable def approx (n : ℕ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun v => Q ⟨hA.pvm (cutoffSet n) v, pvm_cutoffSet_mem_domain hA hAQ n v⟩
      map_add' := fun v w => by
        rw [← LinearPMap.map_add]
        congr 1
        ext
        simp
      map_smul' := fun c v => by
        have h := hQl c _ _ (Q.mem_graph ⟨hA.pvm (cutoffSet n) v, pvm_cutoffSet_mem_domain hA hAQ n v⟩)
        simp only [RingHom.id_apply] at h ⊢
        refine ((LinearPMap.image_iff _).mpr ?_).symm
        rwa [map_smul] }
    (Real.sqrt n) (norm_apply_pvm_cutoffSet_le hA hAQ n)

/-- `(E_n v, y_n v)` lies in the graph of `Q`. -/
private lemma mem_graph_approx (n : ℕ) (v : H) :
    (hA.pvm (cutoffSet n) v, approx hA hAQ hQl n v) ∈ Q.graph :=
  Q.mem_graph ⟨_, pvm_cutoffSet_mem_domain hA hAQ n v⟩

/-- `y_n x → Q x` for `x` in the domain of a closed `Q`: `‖y_n x - Q x‖ = ‖E_n w - w‖` for
`w = A^{1/2} x`, since `‖Q v‖ = ‖A^{1/2} v‖`. -/
private lemma tendsto_approx (hQ : Q.IsClosed) {x z : H} (h : (x, z) ∈ Q.graph) :
    Tendsto (fun n => approx hA hAQ hQl n x) atTop (𝓝 z) := by
  obtain ⟨w, hw⟩ := (hA.exists_mem_graph_sqrt_iff hAQ hQ).mpr ⟨z, h⟩
  have hnorm : ∀ n : ℕ, ‖approx hA hAQ hQl n x - z‖ = ‖hA.pvm (cutoffSet n) w - w‖ := fun n => by
    have h₁ : (hA.pvm (cutoffSet n) x - x, hA.pvm (cutoffSet n) w - w) ∈ hA.sqrt.graph :=
      hA.sqrt.graph.sub_mem (hA.mem_graph_sqrt_apply hw (measurableSet_cutoffSet n)) hw
    have h₂ : (hA.pvm (cutoffSet n) x - x, approx hA hAQ hQl n x - z) ∈ Q.graph :=
      Q.graph.sub_mem (mem_graph_approx hA hAQ hQl n x) h
    exact (hA.norm_eq_of_mem_graph_sqrt hAQ hQ h₁ h₂).symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  exact tendsto_iff_norm_sub_tendsto_zero.mp (hA.pvm.tendsto_apply_cutoff Complex.measurable_ofReal w)

/-- `y_n† x = E_n Q† x` for `x` in the domain of `Q†`. -/
private lemma adjoint_approx_apply (hQd : Dense (Q.domain : Set H)) {x z : H}
    (h : (x, z) ∈ Q†.graph) (n : ℕ) :
    ((approx hA hAQ hQl n)†) x = hA.pvm (cutoffSet n) z := by
  refine ext_inner_left ℂ fun v => ?_
  have h' := hQl.inner_eq_of_mem_graph_adjoint hQd (mem_graph_approx hA hAQ hQl n v) h
  rw [RingHom.id_apply] at h'
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, ← h', inner_conj_symm,
    ProjectionValuedMeasure.inner_apply_left]

/-- If a unitary `u` leaves the graph of `Q` invariant, it commutes with every `y_n`: it leaves
the graphs of `Q†` and `A = Q†Q` invariant, so it commutes with the spectral projections of `A`
(`IsSelfAdjoint.pvm_eq_transport`). -/
private lemma approx_comm (hQd : Dense (Q.domain : Set H)) {u : unitary (H →L[ℂ] H)}
    (hu : ∀ a b, (a, b) ∈ Q.graph ↔ ((u : H →L[ℂ] H) a, (u : H →L[ℂ] H) b) ∈ Q.graph)
    (n : ℕ) :
    (u : H →L[ℂ] H) * approx hA hAQ hQl n = approx hA hAQ hQl n * (u : H →L[ℂ] H) := by
  set U := (u : H →L[ℂ] H)
  set U' := ((star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  have hUU' : ∀ a, U (U' a) = a := fun a => by
    rw [← mul_apply_eq_comp, ← Submonoid.coe_mul, Unitary.mul_star_self, OneMemClass.coe_one,
      one_apply_eq_self]
  have hU'U : ∀ a, U' (U a) = a := fun a => by
    rw [← mul_apply_eq_comp, ← Submonoid.coe_mul, Unitary.star_mul_self, OneMemClass.coe_one,
      one_apply_eq_self]
  have hinner : ∀ a b, ⟪a, U b⟫_ℂ = ⟪U' a, b⟫_ℂ := fun a b => by
    rw [← hUU' a, Unitary.inner_map_map, hU'U]
  -- the graph of `Q†` is invariant
  have hadj : ∀ a b, (a, b) ∈ Q†.graph ↔ (U a, U b) ∈ Q†.graph := fun a b => by
    simp only [LinearPMap.mem_graph_adjoint_iff hQd, inner_real_eq_re_inner]
    refine ⟨fun h v v' hv => ?_, fun h v v' hv => ?_⟩
    · have hv' : (U' v, U' v') ∈ Q.graph := by rwa [hu, hUU', hUU']
      rw [hinner, hinner]
      exact h _ _ hv'
    · have := h _ _ ((hu v v').mp hv)
      rwa [Unitary.inner_map_map, Unitary.inner_map_map] at this
  -- the graph of `A = Q†Q` is invariant
  have hgA : ∀ a b, (a, b) ∈ A.graph ↔ (U a, U b) ∈ A.graph := fun a b => by
    have key : ∀ a b, (a, b) ∈ A.graph ↔ ∃ c, (a, c) ∈ Q.graph ∧ (c, b) ∈ Q†.graph := fun a b => by
      rw [← LinearPMap.mem_graph_restrictScalars (R := ℝ) (T := A), hAQ, LinearPMap.mem_graph_compNat]
    rw [key, key]
    refine ⟨fun ⟨c, h₁, h₂⟩ => ⟨U c, (hu a c).mp h₁, (hadj c b).mp h₂⟩, fun ⟨c, h₁, h₂⟩ => ?_⟩
    refine ⟨U' c, ?_, ?_⟩
    · rw [hu, hUU']
      exact h₁
    · rw [hadj, hUU']
      exact h₂
  -- hence `E_n` commutes with `u`
  have hE : ∀ v, hA.pvm (cutoffSet n) (U v) = U (hA.pvm (cutoffSet n) v) := fun v => by
    have ht := IsSelfAdjoint.pvm_eq_transport hA hA (Unitary.linearIsometryEquiv u) hgA
    conv_lhs => rw [ht]
    rw [ProjectionValuedMeasure.transport_apply]
    exact congrArg U (congrArg (hA.pvm (cutoffSet n)) ((Unitary.linearIsometryEquiv u).symm_apply_apply v))
  refine ContinuousLinearMap.ext fun v => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp]
  refine (LinearPMap.image_iff (pvm_cutoffSet_mem_domain hA hAQ n (U v))).mpr ?_
  rw [hE]
  exact (hu _ _).mp (mem_graph_approx hA hAQ hQl n v)

end Approximation

/-! ### The operator `x ξ ↦ x φ` -/

section Orbit

/-- A set containing the orbit `M η` of a cyclic vector `η` is dense. -/
private lemma dense_of_forall_apply_mem {η : H} (hc : IsCyclicVector M η) {s : Set H}
    (h : ∀ y ∈ M, y η ∈ s) : Dense s := by
  have hsub := cyclicSubspace_subset (M := M) (ξ := η) isClosed_closure fun y hy =>
    subset_closure (h y hy)
  exact dense_iff_closure_eq.mpr (eq_univ_of_univ_subset fun v _ => hsub (hc.mem v))

variable (M) in
/-- The real graph `{(x ξ, x φ) | x ∈ M}`. -/
private noncomputable def orbitGraph (ξ φ : H) : Submodule ℝ (H × H) :=
  (LinearMap.range ((M.applyₗ ξ).prod (M.applyₗ φ))).restrictScalars ℝ

private lemma mem_orbitGraph {ξ φ : H} {p : H × H} :
    p ∈ orbitGraph M ξ φ ↔ ∃ x ∈ M, (x ξ, x φ) = p := by
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

variable (M) in
/-- The operator `x ξ ↦ x φ` with domain `M ξ`. -/
private noncomputable def orbitOp (ξ φ : H) : H →ₗ.[ℝ] H := (orbitGraph M ξ φ).toLinearPMap

variable {ξ : H} (hs : IsSeparatingVector M ξ)
include hs

/-- For a separating `ξ`, the graph of `x ξ ↦ x φ` is `{(x ξ, x φ) | x ∈ M}`. -/
private lemma mem_graph_orbitOp {φ u v : H} :
    (u, v) ∈ (orbitOp M ξ φ).graph ↔ ∃ x ∈ M, x ξ = u ∧ x φ = v := by
  have hg : (orbitOp M ξ φ).graph = orbitGraph M ξ φ :=
    Submodule.toLinearPMap_graph_eq _ fun p hp hp0 => by
      obtain ⟨x, hx, rfl⟩ := mem_orbitGraph.mp hp
      change x φ = 0
      rw [hs x hx hp0, zero_apply]
  rw [hg, mem_orbitGraph]
  simp only [Prod.mk.injEq]

/-- `x ξ ↦ x φ` is complex-linear. -/
private lemma isSemilinear_orbitOp (φ : H) :
    (orbitOp M ξ φ).IsSemilinear (RingHom.id ℂ) := fun c u v h => by
  obtain ⟨x, hx, rfl, rfl⟩ := (mem_graph_orbitOp hs).mp h
  exact (mem_graph_orbitOp hs).mpr ⟨c • x, SMulMemClass.smul_mem c hx, rfl, rfl⟩

/-- `x ξ ↦ x φ` commutes with `M`. -/
private lemma apply_mem_graph_orbitOp {φ u v : H} {b : H →L[ℂ] H} (hb : b ∈ M)
    (h : (u, v) ∈ (orbitOp M ξ φ).graph) : (b u, b v) ∈ (orbitOp M ξ φ).graph := by
  obtain ⟨x, hx, rfl, rfl⟩ := (mem_graph_orbitOp hs).mp h
  exact (mem_graph_orbitOp hs).mpr ⟨b * x, mul_mem hb hx, rfl, rfl⟩

/-- For a cyclic `ξ`, `x ξ ↦ x φ` is densely defined. -/
private lemma dense_domain_orbitOp (hc : IsCyclicVector M ξ) (φ : H) :
    Dense ((orbitOp M ξ φ).domain : Set H) :=
  dense_of_forall_apply_mem hc fun x hx =>
    LinearPMap.mem_domain_of_mem_graph ((mem_graph_orbitOp hs).mpr ⟨x, hx, rfl, rfl⟩)

/-- If `⟪ψ, x ξ⟫ = ⟪η, x φ⟫` for `x ∈ M`, then `(y η, y ψ)` lies in the graph of the adjoint of
`x ξ ↦ x φ` for `y ∈ M`: `⟪x φ, y η⟫ = ⟪(y⋆ x) φ, η⟫ = ⟪(y⋆ x) ξ, ψ⟫ = ⟪x ξ, y ψ⟫`. -/
private lemma mem_graph_adjoint_orbitOp (hc : IsCyclicVector M ξ) {φ ψ η : H}
    (hrel : ∀ x ∈ M, ⟪ψ, x ξ⟫_ℂ = ⟪η, x φ⟫_ℂ) {y : H →L[ℂ] H} (hy : y ∈ M) :
    (y η, y ψ) ∈ (orbitOp M ξ φ)†.graph := by
  rw [LinearPMap.mem_graph_adjoint_iff (dense_domain_orbitOp hs hc φ)]
  intro v v' hvv'
  obtain ⟨x, hx, rfl, rfl⟩ := (mem_graph_orbitOp hs).mp hvv'
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner]
  congr 1
  have h := hrel (star y * x) (mul_mem (star_mem hy) hx)
  have e₁ : ⟪x φ, y η⟫_ℂ = ⟪(star y * x) φ, η⟫_ℂ := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have e₂ : ⟪x ξ, y ψ⟫_ℂ = ⟪(star y * x) ξ, ψ⟫_ℂ := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  rw [e₁, e₂, ← inner_conj_symm, ← h, inner_conj_symm]

end Orbit

/-! ### `S† = F̄` -/

variable {ξ η : H} (hc : IsCyclicVector M ξ) (hs : IsSeparatingVector M ξ)
  (hcη : IsCyclicVector M η)

include hc hs hcη in
/-- **`S† ⊆ F̄`**: a point `(φ, ψ)` of the graph of `S_{η,ξ}†` is the limit of the points
`(y_n ξ, y_n⋆ η)` of the graph of `F_{η,ξ}`, with `y_n = Q̄ E_n ∈ M′` for `Q : x ξ ↦ x φ`. -/
private lemma mem_closure_graph_of_mem_graph_adjoint {φ ψ : H}
    (h : (φ, ψ) ∈ (S[M]⟦η, ξ⟧)†.graph) :
    (φ, ψ) ∈ (S[M′]⟦η, ξ⟧).graph.topologicalClosure := by
  -- the relation `⟪ψ, x ξ⟫ = ⟪η, x φ⟫`
  have hrel : ∀ x ∈ M, ⟪ψ, x ξ⟫_ℂ = ⟪η, x φ⟫_ℂ := fun x hx => by
    have huv :=
      (mem_graph_relativeTomita_iff_of_isCyclicVector_of_isSeparatingVector hc hs (η := η)).mpr
        ⟨x, hx, rfl, rfl⟩
    rw [(isSemilinear_relativeTomita M η ξ).inner_eq_of_mem_graph_adjoint
      (dense_domain_relativeTomita M η ξ) huv h, inner_conj_symm,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  set Q := orbitOp M ξ φ
  have hQd := dense_domain_orbitOp hs hc φ
  have hQl := isSemilinear_orbitOp hs φ
  have hadj : ∀ y ∈ M, (y η, y ψ) ∈ Q†.graph := fun y hy =>
    mem_graph_adjoint_orbitOp hs hc hrel hy
  have hQc : Q.IsClosable :=
    (LinearPMap.isClosable_iff_dense_adjoint_domain hQd).mpr
      (dense_of_forall_apply_mem hcη fun y hy => LinearPMap.mem_domain_of_mem_graph (hadj y hy))
  -- the closure `Q̄` and `A = Q̄† Q̄`
  have hQcc : Q.closure.IsClosed := hQc.closure_isClosed
  have hQcd : Dense (Q.closure.domain : Set H) := LinearPMap.dense_domain_closure hQd
  have hQcl := hQl.closure
  set A := Q.adjointCompClosure hQl hQd
  have hA : IsSelfAdjoint A := Q.isSelfAdjoint_adjointCompClosure hQl hQd hQc
  have hAQ : A.restrictScalars ℝ = Q.closure†.compNat Q.closure :=
    LinearPMap.restrictScalars_adjointCompClosure hQl hQd
  -- `(ξ, φ) ∈ graph Q̄` and `(η, ψ) ∈ graph Q̄†`
  have hξφ : (ξ, φ) ∈ Q.closure.graph :=
    LinearPMap.le_graph_of_le (LinearPMap.le_closure Q)
      ((mem_graph_orbitOp hs).mpr ⟨1, one_mem M, rfl, rfl⟩)
  have hηψ : (η, ψ) ∈ Q.closure†.graph := by
    rw [LinearPMap.adjoint_closure hQd]
    simpa using hadj 1 (one_mem M)
  -- `Q̄` commutes with `M`
  have hinv : ∀ b ∈ M, ∀ a c, (a, c) ∈ Q.closure.graph → (b a, b c) ∈ Q.closure.graph := by
    intro b hb a c hac
    rw [← hQc.graph_closure_eq_closure_graph] at hac ⊢
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hac ⊢
    change Prod.map b b (a, c) ∈ _
    exact map_mem_closure (b.continuous.prodMap b.continuous) hac fun p hp =>
      apply_mem_graph_orbitOp hs hb (u := p.1) (v := p.2) hp
  -- the approximants lie in `M′`
  have hyM : ∀ n, approx hA hAQ hQcl n ∈ M′ := fun n =>
    mem_commutant_of_forall_unitary fun u => by
      obtain ⟨U, hU⟩ : ∃ U : unitary (H →L[ℂ] H), (U : H →L[ℂ] H) = ((u : M) : H →L[ℂ] H) :=
        ⟨⟨_, coe_mem_unitary u⟩, rfl⟩
      rw [← hU]
      refine approx_comm hA hAQ hQcl hQcd (fun a c =>
        ⟨hinv _ (by rw [hU]; exact (u : M).2) a c, fun h' => ?_⟩) n
      have := hinv (star (U : H →L[ℂ] H)) (by rw [hU]; exact star_mem (u : M).2) _ _ h'
      rwa [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← Unitary.coe_star, ← Submonoid.coe_mul,
        Unitary.star_mul_self, OneMemClass.coe_one, one_apply_eq_self, one_apply_eq_self] at this
  -- convergence
  have h₁ := tendsto_approx hA hAQ hQcl hQcc hξφ
  have h₂ : Tendsto (fun n => star (approx hA hAQ hQcl n) η) atTop (𝓝 ψ) := by
    simp_rw [ContinuousLinearMap.star_eq_adjoint, adjoint_approx_apply hA hAQ hQcl hQcd hηψ]
    exact hA.pvm.tendsto_apply_cutoff Complex.measurable_ofReal ψ
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto (h₁.prodMk_nhds h₂) (Eventually.of_forall fun n => ?_)
  exact (mem_graph_relativeTomita_iff_of_isCyclicVector_of_isSeparatingVector
    hs.isCyclicVector_commutant hc.isSeparatingVector_commutant).mpr ⟨_, hyM n, rfl, rfl⟩

include hc hs hcη in
/-- **`S† = F̄`** (Bratteli–Robinson, Proposition 2.5.11, in the relative form of Araki): for `ξ`
cyclic and separating for `M` and `η` cyclic, the adjoint of the relative Tomita operator
`S_{η,ξ} : x ξ ↦ x⋆ η` of `M` is the closure of the relative Tomita operator
`F_{η,ξ} : x′ ξ ↦ x′⋆ η` of the commutant `M′`. -/
theorem adjoint_relativeTomita_eq_closure_commutant :
    (S[M]⟦η, ξ⟧)† = (S[M′]⟦η, ξ⟧).closure := by
  have hSd := dense_domain_relativeTomita M η ξ
  have hFc := isClosable_relativeTomita M′ η ξ
  refine le_antisymm (LinearPMap.le_of_le_graph fun ⟨φ, ψ⟩ hp => ?_) ?_
  · rw [← hFc.graph_closure_eq_closure_graph]
    exact mem_closure_graph_of_mem_graph_adjoint hc hs hcη hp
  · calc (S[M′]⟦η, ξ⟧).closure ≤ (S[M]⟦η, ξ⟧)†.closure :=
          (LinearPMap.adjoint_isClosed hSd).isClosable.closure_mono
            (relativeTomita_commutant_le_adjoint M η ξ)
      _ = (S[M]⟦η, ξ⟧)† := (LinearPMap.adjoint_isClosed hSd).closure_eq

include hc hs in
/-- **`F† = S̄`**, the second half of Bratteli–Robinson 2.5.11: for `ξ` cyclic and separating and
`η` separating (that is, cyclic for `M′`), the adjoint of `F_{η,ξ}` is the closure of `S_{η,ξ}`. -/
lemma adjoint_relativeTomita_commutant_eq_closure (hsη : IsSeparatingVector M η) :
    (S[M′]⟦η, ξ⟧)† = (S[M]⟦η, ξ⟧).closure := by
  have h := adjoint_relativeTomita_eq_closure_commutant (M := M′) hs.isCyclicVector_commutant
    hc.isSeparatingVector_commutant hsη.isCyclicVector_commutant
  rwa [commutant_commutant] at h

include hc hs in
/-- **`H_{M′} = (H_M)'`**: for `ξ` cyclic and separating, the standard subspace of the commutant is
the symplectic complement of `H_M`. The Tomita operators agree: `S_{(H_M)'} = S_{H_M}† = S̄† = F̄ =
S_{H_{M′}}`. -/
theorem standardSubspace_commutant_eq_symplComp :
    H[M′, ξ] = H[M, ξ].symplComp := by
  have h : S[H[M′, ξ]] = S[H[M, ξ].symplComp] := by
    rw [StandardSubspace.tomita_symplComp, ← closure_relativeTomita_self_eq_tomita hc hs,
      LinearPMap.adjoint_closure (dense_domain_relativeTomita M ξ ξ),
      adjoint_relativeTomita_eq_closure_commutant hc hs hc,
      closure_relativeTomita_self_eq_tomita hs.isCyclicVector_commutant
        hc.isSeparatingVector_commutant]
  refine SetLike.ext fun v => ?_
  rw [StandardSubspace.mem_iff_mem_graph_tomita, StandardSubspace.mem_iff_mem_graph_tomita, h]

end VonNeumannAlgebra
