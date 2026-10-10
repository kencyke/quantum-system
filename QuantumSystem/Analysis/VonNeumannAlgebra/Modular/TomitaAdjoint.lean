/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.Modular.StandardSubspace
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The adjoint of the relative Tomita operator

Let `M` be a von Neumann algebra on `H` and `η, ξ ∈ H` arbitrary vectors, with relative Tomita
operators `S_{η,ξ} : x ξ + ζ ↦ s(ξ) x⋆ η` (`x ∈ M`, `ζ ⊥ [M ξ]`) and
`F_{η,ξ} : x′ ξ + ζ′ ↦ s′(ξ) x′⋆ η` (`x′ ∈ M′`, `ζ′ ⊥ [M′ ξ]`; `VonNeumannAlgebra.relativeTomita`),
where `s(ξ) = P_{[M′ ξ]} ∈ M` and `s′(ξ) = P_{[M ξ]} ∈ M′` are the supports. Then
`S_{η,ξ}† = F̄_{η,ξ}` (`VonNeumannAlgebra.adjoint_relativeTomita_eq_closure_commutant`; Araki 1976,
Araki–Masuda 1982, §2; Bratteli–Robinson, Proposition 2.5.11, for `η = ξ` cyclic and separating).

The inclusion `F ⊆ S†` is `VonNeumannAlgebra.relativeTomita_commutant_le_adjoint`. For the converse
let `(φ, ψ)` be in the graph of `S†`, and put `e = s(ξ) ∈ M`, `p = s′(η) = P_{[M η]} ∈ M′` and
`φ₀ = p e φ`. The adjoint relation gives `ψ ⊥ [M ξ]ᗮ`, so `ψ ∈ [M ξ]`, and
`⟪ψ, x ξ⟫ = ⟪η, x e φ⟫ = ⟪η, x φ₀⟫` for `x ∈ M`, using `p η = η`. The operator
`Q : x ξ + ζ ↦ x φ₀` (`x ∈ M`, `ζ ⊥ [M ξ]`) is well defined, since `x ξ = 0` forces `x e = 0`,
densely defined, and commutes with `M`; moreover `(y η + ζ″, y ψ)` lies in the graph of `Q†` for
`y ∈ M`, `ζ″ ⊥ [M η]`, as `x φ₀ ∈ [M η]` and `y ψ ∈ [M ξ]`. Hence `Q` is closable, with
`Q̄ ξ = φ₀` and `Q̄† η = ψ`. The closure `Q̄` and the positive self-adjoint `A = Q̄† Q̄` commute with
every unitary of `M`, hence so do the spectral projections `E_n = E_A({|λ| ≤ n})`
(`IsSelfAdjoint.pvm_eq_transport`), and the bounded operators `y_n = Q̄ E_n` lie in `M′`
(`VonNeumannAlgebra.mem_commutant_of_forall_unitary`). Now `y_n ξ → Q̄ ξ = φ₀`, since
`‖Q̄ v‖ = ‖A^{1/2} v‖` (`IsSelfAdjoint.norm_eq_of_mem_graph_sqrt`) and `A^{1/2}` commutes with
`E_n`, and `s′(ξ) y_n⋆ η = s′(ξ) E_n ψ → s′(ξ) ψ = ψ`. Thus `(φ₀, ψ)` is a limit of points
`(y_n ξ, s′(ξ) y_n⋆ η)` of the graph of `F`. Finally `φ - φ₀ = (1 - e) φ + (1 - p) e φ`, where
`((1 - e) φ, 0)` lies in the graph of `F` (as `(1 - e) φ ⊥ [M′ ξ]`), and `((1 - p) e φ, 0)` is a
limit of the points `((1 - p) y′ ξ, 0) = ((1 - p) y′ ξ, s′(ξ) y′⋆ (1 - p) η)` of the graph of `F`,
with `y′ ∈ M′` and `y′ ξ → e φ ∈ [M′ ξ]`.

Applied to the commutant, this gives `F_{η,ξ}† = S̄_{η,ξ}`
(`VonNeumannAlgebra.adjoint_relativeTomita_commutant_eq_closure`). For `η = ξ` cyclic and
separating it gives that the standard subspace of the commutant is the symplectic complement,
`H_{M′} = (H_M)'` (`VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp`).

## Main results

* `VonNeumannAlgebra.adjoint_relativeTomita_eq_closure_commutant`,
  `VonNeumannAlgebra.adjoint_relativeTomita_commutant_eq_closure` — `S_{η,ξ}† = F̄_{η,ξ}` and
  `F_{η,ξ}† = S̄_{η,ξ}` for arbitrary vectors `η, ξ` (**`S† = F̄`**).
* `VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp` — **`H_{M′} = (H_M)'`**.

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
  obtain ⟨w, hw⟩ := LinearPMap.mem_domain_iff.mp
    ((hA.domain_sqrt_eq_domain hAQ hQ).ge (LinearPMap.mem_domain_of_mem_graph h))
  have hnorm : ∀ n : ℕ, ‖approx hA hAQ hQl n x - z‖ = ‖hA.pvm (cutoffSet n) w - w‖ := fun n => by
    have h₁ : (hA.pvm (cutoffSet n) x - x, hA.pvm (cutoffSet n) w - w) ∈ hA.sqrt.graph :=
      hA.sqrt.graph.sub_mem (LinearPMap.compPMap_le_compNat_toPMap_iff.mp
        (hA.pvm_compPMap_sqrt_le (measurableSet_cutoffSet n)) hw) hw
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
    have ht := IsSelfAdjoint.pvm_eq_transport hA hA (Unitary.linearIsometryEquiv u)
      ((LinearPMap.compNat_toPMap_eq_compPMap_iff (Unitary.linearIsometryEquiv u).toLinearEquiv).mpr
        fun a b => hgA a b)
    conv_lhs => rw [ht]
    rw [ProjectionValuedMeasure.transport_apply]
    exact congrArg U (congrArg (hA.pvm (cutoffSet n)) ((Unitary.linearIsometryEquiv u).symm_apply_apply v))
  refine ContinuousLinearMap.ext fun v => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp]
  refine (LinearPMap.image_iff (pvm_cutoffSet_mem_domain hA hAQ n (U v))).mpr ?_
  rw [hE]
  exact (hu _ _).mp (mem_graph_approx hA hAQ hQl n v)

end Approximation

/-! ### The operator `x ξ + ζ ↦ x φ` -/

section Orbit

variable (M) in
/-- The graph `{(x ξ + ζ, x φ) | x ∈ M, ζ ⊥ [M ξ]}`, a complex subspace of `H × H`. -/
private def orbitGraph (ξ φ : H) : Submodule ℂ (H × H) where
  carrier := {q | ∃ x ∈ M, ∃ ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ, q = (x ξ + ζ, x φ)}
  add_mem' := by
    rintro _ _ ⟨x, hx, ζ, hζ, rfl⟩ ⟨y, hy, ζ', hζ', rfl⟩
    refine ⟨x + y, add_mem hx hy, ζ + ζ', add_mem hζ hζ', ?_⟩
    simp only [Prod.mk_add_mk, add_apply]
    abel_nf
  zero_mem' := ⟨0, zero_mem M, 0, zero_mem _, by simp; rfl⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, ζ, hζ, rfl⟩
    exact ⟨c • x, SMulMemClass.smul_mem c hx, c • ζ, Submodule.smul_mem _ c hζ, by simp [smul_add]⟩

variable (M) in
/-- The operator `x ξ + ζ ↦ x φ` (`x ∈ M`, `ζ ⊥ [M ξ]`) with domain `M ξ + [M ξ]ᗮ`. -/
private noncomputable def orbitOp (ξ φ : H) : H →ₗ.[ℝ] H :=
  ((orbitGraph M ξ φ).restrictScalars ℝ).toLinearPMap

variable {ξ φ : H} (hφ : ∀ x ∈ M, x ξ = 0 → x φ = 0)
include hφ

/-- If `x ξ = 0` forces `x φ = 0` on `M`, the graph of `x ξ + ζ ↦ x φ` is
`{(x ξ + ζ, x φ) | x ∈ M, ζ ⊥ [M ξ]}`: `x ξ + ζ = 0` forces `x ξ = 0`, as `x ξ ∈ [M ξ]`. -/
private lemma mem_graph_orbitOp {q : H × H} :
    q ∈ (orbitOp M ξ φ).graph ↔ q ∈ orbitGraph M ξ φ := by
  have hg : (orbitOp M ξ φ).graph = (orbitGraph M ξ φ).restrictScalars ℝ :=
    Submodule.toLinearPMap_graph_eq _ fun q hq hq0 => by
      obtain ⟨x, hx, ζ, hζ, rfl⟩ := hq
      have hxK : x ξ ∈ (cyclicSubspace M ξ).toSubmodule :=
        InnerProductSpace.apply_mem_cyclicSubspace ξ hx
      have hxξ : x ξ = 0 := by
        have h : ζ = -x ξ := eq_neg_of_add_eq_zero_right hq0
        rw [h, neg_mem_iff] at hζ
        exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hxK hζ)
      exact hφ x hx hxξ
  rw [hg, Submodule.restrictScalars_mem]

/-- `x ξ + ζ ↦ x φ` is complex-linear. -/
private lemma isSemilinear_orbitOp : (orbitOp M ξ φ).IsSemilinear (RingHom.id ℂ) :=
  fun c _ _ h =>
    (mem_graph_orbitOp hφ).mpr ((orbitGraph M ξ φ).smul_mem c ((mem_graph_orbitOp hφ).mp h))

/-- `x ξ + ζ ↦ x φ` commutes with `M`: `b ζ ⊥ [M ξ]` for `b ∈ M`, since `[M ξ]` is invariant under
`b⋆ ∈ M`. -/
private lemma apply_mem_graph_orbitOp {u v : H} {b : H →L[ℂ] H} (hb : b ∈ M)
    (h : (u, v) ∈ (orbitOp M ξ φ).graph) : (b u, b v) ∈ (orbitOp M ξ φ).graph := by
  obtain ⟨x, hx, ζ, hζ, h⟩ := (mem_graph_orbitOp hφ).mp h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  have hbζ : b ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ := by
    rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
    intro a ha
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp]
    exact hζ _ (mul_mem (star_mem hb) ha)
  refine (mem_graph_orbitOp hφ).mpr ⟨b * x, mul_mem hb hx, b ζ, hbζ, ?_⟩
  simp only [map_add, mul_apply_eq_comp]

/-- `x ξ + ζ ↦ x φ` is densely defined: its domain `M ξ + [M ξ]ᗮ` is that of the relative Tomita
operator. -/
private lemma dense_domain_orbitOp : Dense ((orbitOp M ξ φ).domain : Set H) :=
  (dense_domain_relativeTomita M ξ ξ).mono fun u hu => by
    obtain ⟨x, hx, ζ, hζ, rfl⟩ := mem_domain_relativeTomita_iff.mp hu
    exact LinearPMap.mem_domain_of_mem_graph ((mem_graph_orbitOp hφ).mpr ⟨x, hx, ζ, hζ, rfl⟩)

/-- If `⟪ψ, x ξ⟫ = ⟪η, x φ⟫` for `x ∈ M`, with `ψ ∈ [M ξ]` and `φ ∈ [M η]`, then
`(y η + ζ″, y ψ)` lies in the graph of the adjoint of `x ξ + ζ ↦ x φ` for `y ∈ M` and
`ζ″ ⊥ [M η]`: `⟪x φ, y η⟫ = ⟪(y⋆ x) φ, η⟫ = ⟪(y⋆ x) ξ, ψ⟫ = ⟪x ξ, y ψ⟫`, while `x φ ∈ [M η]` is
orthogonal to `ζ″` and `y ψ ∈ [M ξ]` to `ζ`. -/
private lemma mem_graph_adjoint_orbitOp {ψ η : H} (hrel : ∀ x ∈ M, ⟪ψ, x ξ⟫_ℂ = ⟪η, x φ⟫_ℂ)
    (hψ : ψ ∈ cyclicSubspace M ξ) (hφη : φ ∈ cyclicSubspace M η) {y : H →L[ℂ] H} (hy : y ∈ M)
    {ζ'' : H} (hζ'' : ζ'' ∈ (cyclicSubspace M η).toSubmoduleᗮ) :
    (y η + ζ'', y ψ) ∈ (orbitOp M ξ φ)†.graph := by
  rw [LinearPMap.mem_graph_adjoint_iff (dense_domain_orbitOp hφ)]
  intro v v' hvv'
  obtain ⟨x, hx, ζ, hζ, h⟩ := (mem_graph_orbitOp hφ).mp hvv'
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner]
  congr 1
  have h := hrel (star y * x) (mul_mem (star_mem hy) hx)
  have e₁ : ⟪x φ, y η⟫_ℂ = ⟪(star y * x) φ, η⟫_ℂ := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have e₂ : ⟪x ξ, y ψ⟫_ℂ = ⟪(star y * x) ξ, ψ⟫_ℂ := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have e₃ : ⟪x φ, ζ''⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (apply_mem_cyclicSubspace hx hφη) hζ''
  have e₄ : ⟪ζ, y ψ⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (apply_mem_cyclicSubspace hy hψ) hζ
  rw [inner_add_right, inner_add_left, e₃, e₄, add_zero, add_zero, e₁, e₂, ← inner_conj_symm, ← h,
    inner_conj_symm]

end Orbit

/-! ### `S† = F̄` -/

variable {ξ η : H}

/-- **`S† ⊆ F̄`**: a point `(φ, ψ)` of the graph of `S_{η,ξ}†` is a limit of points of the graph of
`F_{η,ξ}`. With `e = s(ξ)` and `p = s′(η)`, the main part `(p e φ, ψ)` is the limit of the points
`(y_n ξ, s′(ξ) y_n⋆ η)` with `y_n = Q̄ E_n ∈ M′` for `Q : x ξ + ζ ↦ x p e φ`; the remainder
`((1 - e) φ, 0)` lies in the graph of `F`, and `((1 - p) e φ, 0)` is the limit of the points
`((1 - p) y′_k ξ, 0)` of the graph of `F` with `y′_k ξ → e φ`, `y′_k ∈ M′`. -/
private lemma mem_closure_graph_of_mem_graph_adjoint {φ ψ : H}
    (h : (φ, ψ) ∈ (S[M]⟦η, ξ⟧)†.graph) :
    (φ, ψ) ∈ (S[M′]⟦η, ξ⟧).graph.topologicalClosure := by
  set K := (cyclicSubspace M ξ).toSubmodule
  set e := M.supportProj ξ
  set p := M′.supportProj η
  have hp : p ∈ M′ := M′.supportProj_mem η
  have hpsa : ∀ a b, ⟪p a, b⟫_ℂ = ⟪a, p b⟫_ℂ := fun a b => by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      (M′.isStarProjection_supportProj η).isSelfAdjoint.star_eq]
  have hpη : p η = η := M′.supportProj_apply_self η
  -- the relation `⟪ψ, x ξ + ζ⟫ = ⟪η, x e φ⟫`
  have hrel₀ : ∀ x ∈ M, ∀ ζ ∈ Kᗮ, ⟪ψ, x ξ + ζ⟫_ℂ = ⟪η, x (e φ)⟫_ℂ := fun x hx ζ hζ => by
    rw [(isSemilinear_relativeTomita M η ξ).inner_eq_of_mem_graph_adjoint
      (dense_domain_relativeTomita M η ξ) (mk_mem_graph_relativeTomita (η := η) hx hζ) h,
      inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, (M.isStarProjection_supportProj ξ).isSelfAdjoint.star_eq,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  -- `ψ ∈ [M ξ]`
  have hψ : ψ ∈ cyclicSubspace M ξ := by
    change ψ ∈ K
    rw [← K.orthogonal_orthogonal, Submodule.mem_orthogonal']
    intro ζ hζ
    simpa using hrel₀ 0 (zero_mem M) ζ hζ
  -- `φ₀ = p e φ`
  set φ₀ := p (e φ)
  have hrel : ∀ x ∈ M, ⟪ψ, x ξ⟫_ℂ = ⟪η, x φ₀⟫_ℂ := fun x hx => by
    rw [← add_zero (x ξ), hrel₀ x hx 0 (zero_mem _), ← hpη, hpsa, hpη,
      apply_apply_of_mem_commutant hp hx]
  have hφη : φ₀ ∈ cyclicSubspace M η := by
    change p (e φ) ∈ (cyclicSubspace M η).toSubmodule
    rw [show p = _ from supportProj_commutant M η]
    exact Submodule.starProjection_apply_mem _ _
  have hφ : ∀ x ∈ M, x ξ = 0 → x φ₀ = 0 := fun x hx hxξ => by
    rw [← apply_apply_of_mem_commutant hp hx, ← mul_apply_eq_comp x e,
      (mul_supportProj_eq_zero_iff hx).mpr hxξ, zero_apply, map_zero]
  set Q := orbitOp M ξ φ₀
  have hQd := dense_domain_orbitOp hφ
  have hQl := isSemilinear_orbitOp hφ
  have hadj : ∀ y ∈ M, ∀ ζ ∈ (cyclicSubspace M η).toSubmoduleᗮ, (y η + ζ, y ψ) ∈ Q†.graph :=
    fun y hy ζ hζ => mem_graph_adjoint_orbitOp hφ hrel hψ hφη hy hζ
  have hQc : Q.IsClosable :=
    (LinearPMap.isClosable_iff_dense_adjoint_domain hQd).mpr
      ((dense_domain_relativeTomita M η η).mono fun u hu => by
        obtain ⟨y, hy, ζ, hζ, rfl⟩ := mem_domain_relativeTomita_iff.mp hu
        exact LinearPMap.mem_domain_of_mem_graph (hadj y hy ζ hζ))
  -- the closure `Q̄` and `A = Q̄† Q̄`
  have hQcc : Q.closure.IsClosed := hQc.closure_isClosed
  have hQcd : Dense (Q.closure.domain : Set H) := LinearPMap.dense_domain_closure hQd
  have hQcl := hQl.closure
  set A := Q.adjointCompClosure hQl hQd
  have hA : IsSelfAdjoint A := Q.isSelfAdjoint_adjointCompClosure hQl hQd hQc
  have hAQ : A.restrictScalars ℝ = Q.closure†.compNat Q.closure :=
    LinearPMap.restrictScalars_adjointCompClosure hQl hQd
  -- `(ξ, φ₀) ∈ graph Q̄` and `(η, ψ) ∈ graph Q̄†`
  have hξφ : (ξ, φ₀) ∈ Q.closure.graph :=
    LinearPMap.le_graph_of_le (LinearPMap.le_closure Q)
      ((mem_graph_orbitOp hφ).mpr ⟨1, one_mem M, 0, zero_mem _, by simp⟩)
  have hηψ : (η, ψ) ∈ Q.closure†.graph := by
    rw [LinearPMap.adjoint_closure hQd]
    simpa using hadj 1 (one_mem M) 0 (zero_mem _)
  -- `Q̄` commutes with `M`
  have hinv : ∀ b ∈ M, ∀ a c, (a, c) ∈ Q.closure.graph → (b a, b c) ∈ Q.closure.graph := by
    intro b hb a c hac
    rw [← hQc.graph_closure_eq_closure_graph] at hac ⊢
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hac ⊢
    change Prod.map b b (a, c) ∈ _
    exact map_mem_closure (b.continuous.prodMap b.continuous) hac fun q hq =>
      apply_mem_graph_orbitOp hφ hb (u := q.1) (v := q.2) hq
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
  -- the main part: `(φ₀, ψ)` is a limit of `(y_n ξ, s′(ξ) y_n⋆ η)`
  have h₁ := tendsto_approx hA hAQ hQcl hQcc hξφ
  have h₂ : Tendsto (fun n => M′.supportProj ξ (star (approx hA hAQ hQcl n) η)) atTop (𝓝 ψ) := by
    have hsψ : M′.supportProj ξ ψ = ψ := by
      rw [supportProj_commutant]
      exact Submodule.starProjection_eq_self_iff.mpr hψ
    rw [← hsψ]
    refine ((M′.supportProj ξ).continuous.tendsto ψ).comp ?_
    simp_rw [ContinuousLinearMap.star_eq_adjoint, adjoint_approx_apply hA hAQ hQcl hQcd hηψ]
    exact hA.pvm.tendsto_apply_cutoff Complex.measurable_ofReal ψ
  have hmain : (φ₀, ψ) ∈ (S[M′]⟦η, ξ⟧).graph.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact mem_closure_of_tendsto (h₁.prodMk_nhds h₂) (Eventually.of_forall fun n =>
      apply_mem_graph_relativeTomita (hyM n))
  -- the remainder `((1 - e) φ, 0)` lies in the graph of `F`
  have hrem₁ : (φ - e φ, 0) ∈ (S[M′]⟦η, ξ⟧).graph := by
    have hζ : φ - e φ ∈ (cyclicSubspace M′ ξ).toSubmoduleᗮ :=
      Submodule.sub_starProjection_mem_orthogonal φ
    have h0 := mk_mem_graph_relativeTomita (M := M′) (η := η) (zero_mem M′) hζ
    rwa [zero_apply, zero_add, star_zero, zero_apply, map_zero] at h0
  -- the remainder `((1 - p) e φ, 0)` is a limit of `((1 - p) y′ ξ, 0)`, `y′ ∈ M′`
  have hrem₂ : (e φ - φ₀, 0) ∈ (S[M′]⟦η, ξ⟧).graph.topologicalClosure := by
    have hsub : (cyclicSubspace M′ ξ : Set H) ⊆
        (fun v => (v - p v, (0 : H))) ⁻¹' (S[M′]⟦η, ξ⟧).graph.topologicalClosure := by
      refine cyclicSubspace_subset ((Submodule.isClosed_topologicalClosure _).preimage
        ((continuous_id.sub p.continuous).prodMk continuous_const)) fun y hy => ?_
      refine Submodule.le_topologicalClosure _ ?_
      have hpη' : star p η = η := by
        rw [(M′.isStarProjection_supportProj η).isSelfAdjoint.star_eq, hpη]
      convert apply_mem_graph_relativeTomita (η := η) (ξ := ξ) (sub_mem hy (mul_mem hp hy))
        using 2
      · simp [mul_apply_eq_comp]
      · simp [star_mul, mul_apply_eq_comp, hpη']
    have heφ : e φ ∈ (cyclicSubspace M′ ξ).toSubmodule := Submodule.starProjection_apply_mem _ φ
    exact hsub heφ
  have hsum := add_mem (add_mem hmain (Submodule.le_topologicalClosure _ hrem₁)) hrem₂
  convert hsum using 1
  simp only [Prod.mk_add_mk, add_zero]
  congr 1
  abel

/-- **`S† = F̄`** (Bratteli–Robinson, Proposition 2.5.11, in the relative form of Araki and
Araki–Masuda): for arbitrary vectors `η, ξ`, the adjoint of the relative Tomita operator
`S_{η,ξ} : x ξ + ζ ↦ s(ξ) x⋆ η` of `M` is the closure of the relative Tomita operator
`F_{η,ξ} : x′ ξ + ζ′ ↦ s′(ξ) x′⋆ η` of the commutant `M′`. -/
theorem adjoint_relativeTomita_eq_closure_commutant :
    (S[M]⟦η, ξ⟧)† = (S[M′]⟦η, ξ⟧).closure := by
  have hSd := dense_domain_relativeTomita M η ξ
  have hFc := isClosable_relativeTomita M′ η ξ
  refine le_antisymm (LinearPMap.le_of_le_graph fun ⟨φ, ψ⟩ hp => ?_) ?_
  · rw [← hFc.graph_closure_eq_closure_graph]
    exact mem_closure_graph_of_mem_graph_adjoint hp
  · calc (S[M′]⟦η, ξ⟧).closure ≤ (S[M]⟦η, ξ⟧)†.closure :=
          (LinearPMap.adjoint_isClosed hSd).isClosable.closure_mono
            (relativeTomita_commutant_le_adjoint M η ξ)
      _ = (S[M]⟦η, ξ⟧)† := (LinearPMap.adjoint_isClosed hSd).closure_eq

/-- **`F† = S̄`**, the second half of Bratteli–Robinson 2.5.11: for arbitrary vectors `η, ξ`, the
adjoint of `F_{η,ξ}` is the closure of `S_{η,ξ}`. -/
lemma adjoint_relativeTomita_commutant_eq_closure :
    (S[M′]⟦η, ξ⟧)† = (S[M]⟦η, ξ⟧).closure := by
  have h := adjoint_relativeTomita_eq_closure_commutant (M := M′) (η := η) (ξ := ξ)
  rwa [commutant_commutant] at h

section Commutant

variable (hc : IsCyclicVector M ξ) (hs : IsSeparatingVector M ξ)

include hc hs in
/-- **`H_{M′} = (H_M)'`**: for `ξ` cyclic and separating, the standard subspace of the commutant is
the symplectic complement of `H_M`. The Tomita operators agree: `S_{(H_M)'} = S_{H_M}† = S̄† = F̄ =
S_{H_{M′}}`. -/
theorem standardSubspace_commutant_eq_symplComp :
    H[M′, ξ] = H[M, ξ].symplComp := by
  have h : S[H[M′, ξ]] = S[H[M, ξ].symplComp] := by
    rw [StandardSubspace.tomita_symplComp, ← closure_relativeTomita_self_eq_tomita hc hs,
      LinearPMap.adjoint_closure (dense_domain_relativeTomita M ξ ξ),
      adjoint_relativeTomita_eq_closure_commutant,
      closure_relativeTomita_self_eq_tomita hs.isCyclicVector_commutant
        hc.isSeparatingVector_commutant]
  refine SetLike.ext fun v => ?_
  rw [StandardSubspace.mem_iff_mem_graph_tomita, StandardSubspace.mem_iff_mem_graph_tomita, h]

end Commutant

end VonNeumannAlgebra
