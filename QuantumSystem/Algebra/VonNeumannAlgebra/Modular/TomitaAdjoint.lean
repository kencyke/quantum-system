/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.StandardSubspace
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The adjoint of the Tomita operator and the relative modular conjugation

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

The second half of the file studies the polar decomposition `S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}` for
arbitrary vectors (`VonNeumannAlgebra.relativeModularConj`). The kernel of `S̄_{η,ξ}` is that of
`s(η) s′(ξ)`, and its range is dense in `s(ξ) s′(η) H`, so `J_{η,ξ}` is a partial isometry from
`s(η) s′(ξ) H` onto `s(ξ) s′(η) H`; `S̄_{ξ,η}` inverts `S̄_{η,ξ}` between these supports, which
by uniqueness of the polar decomposition gives `J_{η,ξ}† = J_{ξ,η}`. With `S† = F̄`, `ξ` cyclic and
`η` separating make `S̄_{η,ξ}` injective, hence `Δ_{η,ξ}` injective and `J_{η,ξ}` isometric, and
for `ξ`, `η` cyclic and separating `J_{η,ξ}` is antiunitary.

## Main definitions

* `VonNeumannAlgebra.relativeModularConj M η ξ` — the **relative modular conjugation** `J_{η,ξ}`,
  the partial isometry of `S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}`, a conjugate-linear contraction.
* `VonNeumannAlgebra.relativeModularConjEquiv` — `J_{η,ξ}` as an antiunitary, for `ξ`, `η` cyclic
  and separating.

## Notation

* `J[M]⟦η, ξ⟧` (`open scoped VonNeumannAlgebra`) — `J_{η,ξ}`, with the index order of
  `S_{η,ξ}` and `Δ_{η,ξ}`: Araki's `J_{Φ,Ψ}` with `Φ = η` and `Ψ = ξ`, where
  `S_{Φ,Ψ} x Ψ = x⋆ Φ`.
* `U†` (`open scoped InnerProduct`) — the adjoint of a bounded real-linear `U` for the real inner
  products `re ⟪·, ·⟫`; for the conjugate-linear `J_{η,ξ}` it is the antilinear adjoint
  `⟪J† y, x⟫ = ⟪J x, y⟫` of the literature (`VonNeumannAlgebra.inner_relativeModularConj_left`).

## Main results

* `VonNeumannAlgebra.adjoint_relativeTomita_eq_closure_commutant`,
  `VonNeumannAlgebra.adjoint_relativeTomita_commutant_eq_closure` — `S_{η,ξ}† = F̄_{η,ξ}` and
  `F_{η,ξ}† = S̄_{η,ξ}` for arbitrary vectors `η, ξ` (**`S† = F̄`**).
* `VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp` — **`H_{M′} = (H_M)'`**.
* `VonNeumannAlgebra.closure_relativeTomita_compNat_le`, `VonNeumannAlgebra.ker_closure_relativeTomita`,
  `VonNeumannAlgebra.supportProj_compPMap_closure_relativeTomita` — `S̄_{ξ,η} S̄_{η,ξ} ⊆ s(η) s′(ξ)`,
  `ker S̄_{η,ξ} = ker s(η) s′(ξ)` and `ran S̄_{η,ξ} ⊆ s(ξ) s′(η) H` for arbitrary `η, ξ`.
* `VonNeumannAlgebra.ker_closure_relativeTomita_eq_orthogonal`,
  `VonNeumannAlgebra.ker_relativeModular_eq_orthogonal` — for `ξ` cyclic,
  `ker S̄_{η,ξ} = ker Δ_{η,ξ} = [M′ η]ᗮ`.
* `VonNeumannAlgebra.ker_closure_relativeTomita_eq_bot` — for `ξ` cyclic and `η` separating,
  `S̄_{η,ξ}` is injective;
  `VonNeumannAlgebra.dense_range_closure_relativeTomita` — for `ξ` separating and `η` cyclic,
  `S̄_{η,ξ}` has dense range `⊇ M η`.
* `VonNeumannAlgebra.ker_relativeModular_eq_bot`, `VonNeumannAlgebra.relativeModularGroup_eq_unitaryGroup`
  — for `ξ` cyclic and `η` separating, `Δ_{η,ξ}` is injective and `Δ_{η,ξ}^{it}` is the unitary
  group generated by `log Δ_{η,ξ}`.
* `VonNeumannAlgebra.relativeModularConj`, `VonNeumannAlgebra.closure_relativeTomita_eq_compPMap`
  — the relative
  modular conjugation `J_{η,ξ}` (`J[M]⟦η, ξ⟧`) of arbitrary vectors `η, ξ`, the partial isometry of
  the polar decomposition `S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}`.
* `VonNeumannAlgebra.adjoint_relativeModularConj`,
  `VonNeumannAlgebra.inner_relativeModularConj_left`,
  `VonNeumannAlgebra.relativeModularConj_comp_relativeModularConj` —
  `J_{ξ,η} = J_{η,ξ}†` for arbitrary `η, ξ`, so `J_{ξ,η} J_{η,ξ} = E_Δ((0, ∞))`, the support
  projection of `Δ_{η,ξ}`.
* `VonNeumannAlgebra.pvm_Ioi_relativeModular`, `VonNeumannAlgebra.range_relativeModularConj` —
  `J_{η,ξ}` is a partial isometry with initial projection `E_Δ((0, ∞)) = s(η) s′(ξ)` and final
  space `s(ξ) s′(η) H`.
* `VonNeumannAlgebra.relativeModularConj_relativeModularConj` — `J_{ξ,η} J_{η,ξ} = 1` for `ξ`
  cyclic and `η` separating.
* `VonNeumannAlgebra.norm_relativeModularConj_apply`, `VonNeumannAlgebra.surjective_relativeModularConj`
  — for `ξ` cyclic and `η` separating `J_{η,ξ}` is isometric, and for `η` cyclic and `ξ`
  separating it is onto.
* `VonNeumannAlgebra.relativeModularConjEquiv`, `VonNeumannAlgebra.relativeModularConjEquiv_symm_apply`
  — `J_{η,ξ}` is antiunitary for `ξ`, `η` cyclic and separating, with inverse `J_{ξ,η}`.
* `VonNeumannAlgebra.relativeModularConj_self` — `J_{Ω,Ω} = J_{H_M}`.

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

/-! ### The relative modular conjugation -/

section RelativeModularConj

variable {η ξ : H}

/-- A set containing the orbit `M η` of a cyclic vector `η` is dense. -/
private lemma dense_of_forall_apply_mem (hc : IsCyclicVector M η) {s : Set H}
    (h : ∀ y ∈ M, y η ∈ s) : Dense s := by
  have hsub := cyclicSubspace_subset (M := M) (ξ := η) isClosed_closure fun y hy =>
    subset_closure (h y hy)
  exact dense_iff_closure_eq.mpr (eq_univ_of_univ_subset fun v _ => hsub (hc.mem v))

/-- For `ξ` separating and `η` cyclic, `S̄_{η,ξ}` has dense range: it contains `M η`. -/
lemma dense_range_closure_relativeTomita (hs : IsSeparatingVector M ξ)
    (hcη : IsCyclicVector M η) : Dense (range (S[M]⟦η, ξ⟧).closure) := by
  have hsupp : M.supportProj ξ = 1 := supportProj_eq_one_iff.mpr hs.isCyclicVector_commutant
  refine dense_of_forall_apply_mem hcη fun y hy => ?_
  have h := mem_graph_closure_relativeTomita (apply_mem_graph_relativeTomita (η := η) (ξ := ξ)
    (star_mem hy))
  rw [hsupp, star_star, one_apply_eq_self] at h
  obtain ⟨p, -, hp⟩ := ((S[M]⟦η, ξ⟧).closure.mem_graph_iff).mp h
  exact ⟨p, hp⟩

variable (M η ξ) in
/-- The **relative modular conjugation** `J_{η,ξ}` of a pair of vectors: the partial isometry of the
polar decomposition `S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}`
(`VonNeumannAlgebra.closure_relativeTomita_eq_compPMap`; Araki–Masuda 1982, §2), a conjugate-linear
bounded operator written `J[M]⟦η, ξ⟧`, isometric on `(ker S̄_{η,ξ})ᗮ`
(`IsSelfAdjoint.norm_polarIsometry_apply`). Its adjoint is `J_{ξ,η}`
(`VonNeumannAlgebra.inner_relativeModularConj_left`), so `J_{ξ,η} J_{η,ξ} = E_Δ((0, ∞))`
(`VonNeumannAlgebra.relativeModularConj_comp_relativeModularConj`),
and everywhere for `ξ` cyclic and `η` separating
(`VonNeumannAlgebra.relativeModularConj_relativeModularConj`). For `η = ξ` cyclic and separating
it is the modular conjugation of the standard subspace `H_M`
(`VonNeumannAlgebra.relativeModularConj_self`). -/
noncomputable def relativeModularConj : H →L⋆[ℂ] H :=
  (isSelfAdjoint_relativeModular M η ξ).polarIsometrySL (restrictScalars_relativeModular M η ξ)
    (isClosed_closure_relativeTomita M η ξ) (isSemilinear_closure_relativeTomita M η ξ)

/-- `J[M]⟦η, ξ⟧` is the relative modular conjugation `J_{η,ξ}` of `M`
(`VonNeumannAlgebra.relativeModularConj`). -/
scoped notation "J[" M "]⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeModularConj M η ξ

/-- Displays `VonNeumannAlgebra.relativeModularConj M η ξ` as `J[M]⟦η, ξ⟧`. -/
@[scoped app_unexpander VonNeumannAlgebra.relativeModularConj]
meta def relativeModularConjUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $M $η $ξ) => `(J[$M]⟦$η, $ξ⟧)
  | _ => throw ()

variable (M η ξ) in
/-- `J_{η,ξ}` is the partial isometry of the polar decomposition of `S̄_{η,ξ}`
(`IsSelfAdjoint.polarIsometry`). -/
lemma relativeModularConj_apply (x : H) :
    J[M]⟦η, ξ⟧ x = (isSelfAdjoint_relativeModular M η ξ).polarIsometry
      (restrictScalars_relativeModular M η ξ) (isClosed_closure_relativeTomita M η ξ) x := rfl

/-- `J_{η,ξ}` is a contraction. -/
lemma norm_relativeModularConj_le : ‖J[M]⟦η, ξ⟧‖ ≤ 1 :=
  (isSelfAdjoint_relativeModular M η ξ).norm_polarIsometrySL_le _ _ _

/-- **Polar decomposition** `S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}` for arbitrary `η, ξ`, as real-linear
operators. -/
lemma closure_relativeTomita_eq_compPMap :
    (S[M]⟦η, ξ⟧).closure =
      ((J[M]⟦η, ξ⟧ : H →L[ℝ] H) : H →ₗ[ℝ] H).compPMap (Δ[M]⟦η, ξ⟧^{1/2}.restrictScalars ℝ) :=
  (isSelfAdjoint_relativeModular M η ξ).eq_polarIsometry_compPMap
    (restrictScalars_relativeModular M η ξ) (isClosed_closure_relativeTomita M η ξ)

/-- `S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}`, pointwise. -/
private lemma mem_graph_closure_relativeTomita_iff {u v : H} :
    (u, v) ∈ (S[M]⟦η, ξ⟧).closure.graph ↔
      ∃ w, (u, w) ∈ Δ[M]⟦η, ξ⟧^{1/2}.graph ∧ J[M]⟦η, ξ⟧ w = v := by
  have h := closure_relativeTomita_eq_compPMap (M := M) (η := η) (ξ := ξ)
  constructor
  · intro huv
    obtain ⟨w, hw, rfl⟩ := LinearPMap.mem_graph_compPMap.mp (LinearPMap.le_graph_of_le h.le huv)
    exact ⟨w, LinearPMap.mem_graph_restrictScalars.mp hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact LinearPMap.le_graph_of_le h.ge
      (LinearPMap.mem_graph_compPMap.mpr ⟨w, LinearPMap.mem_graph_restrictScalars.mpr hw, rfl⟩)

/-! #### Supports, and `S̄_{ξ,η}` as the inverse of `S̄_{η,ξ}` -/

/-- `S̄_{ξ,η} S̄_{η,ξ} ⊆ s(η) s′(ξ)`, pointwise: for `(a, b)` in the graph of `S̄_{η,ξ}`,
`(b, s(η) s′(ξ) a)` lies in the graph of `S̄_{ξ,η}`. On `x ξ + ζ` (`x ∈ M`, `ζ ⊥ [M ξ]`) this is
`S_{ξ,η} (s(ξ) x⋆ η) = s(η) x s(ξ) ξ = s(η) x ξ`; the closure is a limit argument. -/
private lemma mem_graph_closure_relativeTomita_swap {a b : H}
    (h : (a, b) ∈ (S[M]⟦η, ξ⟧).closure.graph) :
    (b, M.supportProj η (M′.supportProj ξ a)) ∈ (S[M]⟦ξ, η⟧).closure.graph := by
  have hS : ∀ p ∈ ((S[M]⟦η, ξ⟧).graph : Set (H × H)),
      (p.2, M.supportProj η (M′.supportProj ξ p.1)) ∈ (S[M]⟦ξ, η⟧).graph := by
    intro p hp
    obtain ⟨x, hx, ζ, hζ, rfl⟩ := mem_graph_relativeTomita.mp hp
    have hy : M.supportProj ξ * star x ∈ M := mul_mem (M.supportProj_mem ξ) (star_mem hx)
    have h₁ := apply_mem_graph_relativeTomita (η := ξ) (ξ := η) hy
    have hxξ : M′.supportProj ξ (x ξ) = x ξ := by
      rw [supportProj_commutant, Submodule.starProjection_eq_self_iff]
      exact apply_mem_cyclicSubspace hx (self_mem_cyclicSubspace M ξ)
    have hζ0 : M′.supportProj ξ ζ = 0 := by
      rw [supportProj_commutant]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hζ
    convert h₁ using 2
    · rw [mul_apply_eq_comp]
    · rw [star_mul, star_star, (M.isStarProjection_supportProj ξ).isSelfAdjoint.star_eq,
        mul_apply_eq_comp, supportProj_apply_self, map_add, hxξ, hζ0, add_zero]
  rw [← (isClosable_relativeTomita M η ξ).graph_closure_eq_closure_graph] at h
  rw [← (isClosable_relativeTomita M ξ η).graph_closure_eq_closure_graph]
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h ⊢
  have hc : Continuous fun p : H × H => (p.2, M.supportProj η (M′.supportProj ξ p.1)) :=
    continuous_snd.prodMk ((M.supportProj η).continuous.comp
      ((M′.supportProj ξ).continuous.comp continuous_fst))
  exact map_mem_closure (f := fun p : H × H => (p.2, M.supportProj η (M′.supportProj ξ p.1))) hc h hS

/-- `ker S̄_{η,ξ} ⊇ (1 - s(η) s′(ξ)) H`: it contains `[M ξ]ᗮ` and `(1 - s(η)) [M ξ]`, as
`S_{η,ξ} ((1 - s(η)) x ξ) = s(ξ) x⋆ (1 - s(η)) η = 0`; the closure is a limit argument. -/
private lemma mem_graph_closure_relativeTomita_of_supportProj_apply_eq_zero {z : H}
    (hz : M.supportProj η (M′.supportProj ξ z) = 0) :
    (z, 0) ∈ (S[M]⟦η, ξ⟧).closure.graph := by
  set w := M′.supportProj ξ z
  -- `z - w ⊥ [M ξ]`
  have hζ : (z - w, 0) ∈ (S[M]⟦η, ξ⟧).closure.graph := by
    have hmem : z - w ∈ (cyclicSubspace M ξ).toSubmoduleᗮ := by
      simp only [w, supportProj_commutant]
      exact Submodule.sub_starProjection_mem_orthogonal z
    have h := mk_mem_graph_relativeTomita (η := η) (zero_mem M) hmem
    simp only [zero_apply, zero_add, star_zero, map_zero] at h
    exact mem_graph_closure_relativeTomita h
  -- `w ∈ [M ξ]` with `s(η) w = 0` is a limit of the kernel vectors `(1 - s(η)) x ξ`
  have hw : (w, 0) ∈ (S[M]⟦η, ξ⟧).closure.graph := by
    have hφ : Continuous fun v : H => (v - M.supportProj η v, (0 : H)) :=
      (continuous_id.sub (M.supportProj η).continuous).prodMk continuous_const
    have hS : ∀ v ∈ Set.range fun x : M => (x : H →L[ℂ] H) ξ,
        (v - M.supportProj η v, (0 : H)) ∈ (((S[M]⟦η, ξ⟧).closure.graph : Submodule ℝ (H × H)) :
          Set (H × H)) := by
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      have hy : (1 - M.supportProj η) * x ∈ M := mul_mem (sub_mem (one_mem M) (M.supportProj_mem η)) hx
      have h := apply_mem_graph_relativeTomita (η := η) (ξ := ξ) hy
      have h0 : star ((1 - M.supportProj η) * x) η = 0 := by
        rw [star_mul, star_sub, star_one, (M.isStarProjection_supportProj η).isSelfAdjoint.star_eq,
          mul_apply_eq_comp, sub_apply, one_apply_eq_self, supportProj_apply_self, sub_self, map_zero]
      rw [h0, map_zero, mul_apply_eq_comp, sub_apply, one_apply_eq_self] at h
      exact mem_graph_closure_relativeTomita h
    have hwmem : w ∈ closure (Set.range fun x : M => (x : H →L[ℂ] H) ξ) := by
      rw [← coe_cyclicSubspace]
      simp only [w, supportProj_commutant]
      exact Submodule.starProjection_apply_mem _ z
    have h := map_mem_closure hφ hwmem hS
    have hcl : IsClosed (((S[M]⟦η, ξ⟧).closure.graph : Submodule ℝ (H × H)) : Set (H × H)) :=
      isClosed_closure_relativeTomita M η ξ
    rw [hcl.closure_eq] at h
    rwa [hz, sub_zero] at h
  have h := (S[M]⟦η, ξ⟧).closure.graph.add_mem hζ hw
  rwa [Prod.mk_add_mk, sub_add_cancel, add_zero] at h

/-- `ker S̄_{η,ξ} = ker s(η) s′(ξ)`, pointwise. -/
private lemma mem_graph_closure_relativeTomita_zero_iff {x : H} :
    (x, 0) ∈ (S[M]⟦η, ξ⟧).closure.graph ↔ M.supportProj η (M′.supportProj ξ x) = 0 :=
  ⟨fun hx => (S[M]⟦ξ, η⟧).closure.graph_fst_eq_zero_snd
    (mem_graph_closure_relativeTomita_swap hx) rfl,
    mem_graph_closure_relativeTomita_of_supportProj_apply_eq_zero⟩

/-- **`S̄_{ξ,η} S̄_{η,ξ} ⊆ s(η) s′(ξ)`**: `S̄_{ξ,η}` inverts `S̄_{η,ξ}` between the supports. -/
lemma closure_relativeTomita_compNat_le :
    (S[M]⟦ξ, η⟧).closure.compNat (S[M]⟦η, ξ⟧).closure ≤
      (((M.supportProj η * M′.supportProj ξ : H →L[ℂ] H) : H →ₗ[ℂ] H).restrictScalars ℝ).toPMap ⊤ :=
  LinearPMap.le_iff_mem_graph.mpr fun a c hac => by
    -- the graph of `S̄_{ξ,η}` is that of a function
    obtain ⟨b, hab, hbc⟩ := LinearPMap.mem_graph_compNat.mp hac
    obtain rfl : c = M.supportProj η (M′.supportProj ξ a) :=
      sub_eq_zero.mp ((S[M]⟦ξ, η⟧).closure.graph_fst_eq_zero_snd
        ((S[M]⟦ξ, η⟧).closure.graph.sub_mem hbc (mem_graph_closure_relativeTomita_swap hab))
        (sub_self b))
    exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨a, Submodule.mem_top⟩, rfl, mul_apply_eq_comp (M.supportProj η) (M′.supportProj ξ) a⟩

/-- **`ker S̄_{η,ξ} = ker s(η) s′(ξ)`** for arbitrary `η, ξ` (Araki–Masuda 1982, §2: the support of
`Δ_{η,ξ}` is `s(η) s′(ξ)`): `S̄_{ξ,η} S̄_{η,ξ} ⊆ s(η) s′(ξ)`
(`VonNeumannAlgebra.closure_relativeTomita_compNat_le`), and conversely `(1 - s(η) s′(ξ)) H` lies
in the kernel, as `S_{η,ξ} ((1 - s(η)) x ξ) = 0` and `S_{η,ξ} [M ξ]ᗮ = 0`. -/
lemma ker_closure_relativeTomita :
    (S[M]⟦η, ξ⟧).closure.ker =
      (LinearMap.ker ((M.supportProj η * M′.supportProj ξ : H →L[ℂ] H) : H →ₗ[ℂ] H)).restrictScalars
        ℝ := by
  ext x
  rw [← LinearPMap.mem_graph_zero_iff_mem_ker, Submodule.restrictScalars_mem, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, mul_apply_eq_comp]
  exact mem_graph_closure_relativeTomita_zero_iff

/-- **`ker S̄_{η,ξ} = [M′ η]ᗮ`** for `ξ` cyclic: then `s′(ξ) = 1`, and `s(η)` is the projection
onto `[M′ η]` (`VonNeumannAlgebra.ker_closure_relativeTomita`). -/
lemma ker_closure_relativeTomita_eq_orthogonal (hc : IsCyclicVector M ξ) :
    (S[M]⟦η, ξ⟧).closure.ker = (cyclicSubspace M′ η).toSubmoduleᗮ.restrictScalars ℝ := by
  have hsupp : M′.supportProj ξ = 1 := by
    rw [supportProj_eq_one_iff, commutant_commutant]
    exact hc
  ext x
  rw [ker_closure_relativeTomita, hsupp, mul_one, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, supportProj,
    Submodule.starProjection_apply_eq_zero_iff]

/-- For `ξ` cyclic and `η` separating, `S̄_{η,ξ}` is injective: its kernel `[M′ η]ᗮ`
(`VonNeumannAlgebra.ker_closure_relativeTomita_eq_orthogonal`) is `0`. -/
lemma ker_closure_relativeTomita_eq_bot (hc : IsCyclicVector M ξ)
    (hsη : IsSeparatingVector M η) : (S[M]⟦η, ξ⟧).closure.ker = ⊥ := by
  rw [ker_closure_relativeTomita_eq_orthogonal hc, hsη.isCyclicVector_commutant]
  simp

/-- **`ker Δ_{η,ξ} = [M′ η]ᗮ`** for `ξ` cyclic: `ker Δ_{η,ξ} = ker S̄_{η,ξ}`
(`VonNeumannAlgebra.ker_relativeModular`, `VonNeumannAlgebra.ker_closure_relativeTomita_eq_orthogonal`). -/
lemma ker_relativeModular_eq_orthogonal (hc : IsCyclicVector M ξ) :
    (Δ[M]⟦η, ξ⟧).ker.restrictScalars ℝ = (cyclicSubspace M′ η).toSubmoduleᗮ.restrictScalars ℝ :=
  ker_relativeModular.trans (ker_closure_relativeTomita_eq_orthogonal hc)

/-- For `ξ` cyclic and `η` separating, `Δ_{η,ξ}` is injective: `ker Δ_{η,ξ} = ker S̄_{η,ξ}`. -/
lemma ker_relativeModular_eq_bot (hc : IsCyclicVector M ξ) (hsη : IsSeparatingVector M η) :
    (Δ[M]⟦η, ξ⟧).ker = ⊥ :=
  ((isSelfAdjoint_relativeModular M η ξ).ker_eq_bot_iff_of_restrictScalars_eq
    (restrictScalars_relativeModular M η ξ)).mpr (ker_closure_relativeTomita_eq_bot hc hsη)

/-- For `ξ` cyclic and `η` separating, the relative modular group `Δ_{η,ξ}^{it}` is the unitary
group generated by `log Δ_{η,ξ}` (`IsSelfAdjoint.unitaryGroup`). -/
lemma relativeModularGroup_eq_unitaryGroup (hc : IsCyclicVector M ξ) (hsη : IsSeparatingVector M η)
    (t : ℝ) : Δ[M]⟦η, ξ⟧^{i t} =
      ((isSelfAdjoint_relativeModular M η ξ).isSelfAdjoint_logPMap.unitaryGroup t : H →L[ℂ] H) :=
  (isSelfAdjoint_relativeModular M η ξ).imaginaryPower_eq_unitaryGroup
    (isPositive_relativeModular M η ξ) (ker_relativeModular_eq_bot hc hsη) t

/-- `ran S̄_{η,ξ} ⊆ s(ξ) s′(η) H`, pointwise; the closure is a limit argument. -/
private lemma supportProj_apply_supportProj_of_mem_graph_closure {a b : H}
    (h : (a, b) ∈ (S[M]⟦η, ξ⟧).closure.graph) :
    M.supportProj ξ (M′.supportProj η b) = b := by
  have hS : ∀ p ∈ ((S[M]⟦η, ξ⟧).graph : Set (H × H)),
      M.supportProj ξ (M′.supportProj η p.2) = p.2 := by
    intro p hp
    obtain ⟨x, hx, ζ, hζ, rfl⟩ := mem_graph_relativeTomita.mp hp
    have hxη : M′.supportProj η (star x η) = star x η := by
      rw [supportProj_commutant, Submodule.starProjection_eq_self_iff]
      exact apply_mem_cyclicSubspace (star_mem hx) (self_mem_cyclicSubspace M η)
    dsimp only
    rw [← mul_apply_eq_comp (M′.supportProj η), ← (commute_supportProj_supportProj_commutant M ξ η).eq,
      mul_apply_eq_comp, hxη, ← mul_apply_eq_comp (M.supportProj ξ),
      (M.isStarProjection_supportProj ξ).isIdempotentElem.eq]
  have hcl : IsClosed {p : H × H | M.supportProj ξ (M′.supportProj η p.2) = p.2} :=
    isClosed_eq ((M.supportProj ξ).continuous.comp ((M′.supportProj η).continuous.comp
      continuous_snd)) continuous_snd
  rw [← (isClosable_relativeTomita M η ξ).graph_closure_eq_closure_graph, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe] at h
  have h' : (a, b) ∈ {p : H × H | M.supportProj ξ (M′.supportProj η p.2) = p.2} :=
    closure_minimal (s := ((S[M]⟦η, ξ⟧).graph : Set (H × H))) hS hcl h
  exact h'

/-- **`ran S̄_{η,ξ} ⊆ s(ξ) s′(η) H`**: `s(ξ) s′(η) S̄_{η,ξ} = S̄_{η,ξ}`, since
`S_{η,ξ} (x ξ + ζ) = s(ξ) x⋆ η ∈ s(ξ) [M η]`. -/
lemma supportProj_compPMap_closure_relativeTomita :
    (M.supportProj ξ * M′.supportProj η) ⬝ (S[M]⟦η, ξ⟧).closure = (S[M]⟦η, ξ⟧).closure :=
  LinearPMap.ext rfl fun x hx _ => by
    change (M.supportProj ξ * M′.supportProj η) ((S[M]⟦η, ξ⟧).closure ⟨x, hx⟩) = _
    rw [mul_apply_eq_comp]
    exact supportProj_apply_supportProj_of_mem_graph_closure ((S[M]⟦η, ξ⟧).closure.mem_graph ⟨x, hx⟩)

/-- **`s(ξ) s′(η) H ⊆ closure (ran S̄_{η,ξ})`**: `s(ξ) x η = S_{η,ξ} (x⋆ ξ)` for `x ∈ M`. -/
lemma supportProj_apply_supportProj_mem_closure_range (z : H) :
    M.supportProj ξ (M′.supportProj η z) ∈ closure (Set.range (S[M]⟦η, ξ⟧).closure) := by
  have hS : ∀ v ∈ Set.range fun x : M => (x : H →L[ℂ] H) η,
      M.supportProj ξ v ∈ Set.range (S[M]⟦η, ξ⟧).closure := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have h := mem_graph_closure_relativeTomita (apply_mem_graph_relativeTomita (η := η) (ξ := ξ)
      (star_mem hx))
    rw [star_star] at h
    obtain ⟨p, -, hp⟩ := ((S[M]⟦η, ξ⟧).closure.mem_graph_iff).mp h
    exact ⟨p, hp⟩
  have hmem : M′.supportProj η z ∈ closure (Set.range fun x : M => (x : H →L[ℂ] H) η) := by
    rw [← coe_cyclicSubspace, supportProj_commutant]
    exact Submodule.starProjection_apply_mem _ z
  exact map_mem_closure (M.supportProj ξ).continuous hmem hS

/-- `ran J_{η,ξ} ⊆ s(ξ) s′(η) H`: `J_{η,ξ}` maps into the closure of `ran S̄_{η,ξ}`
(`IsSelfAdjoint.polarIsometry_apply_mem_closure_range`), which `s(ξ) s′(η)` fixes. -/
lemma supportProj_apply_supportProj_relativeModularConj (x : H) :
    M.supportProj ξ (M′.supportProj η (J[M]⟦η, ξ⟧ x)) = J[M]⟦η, ξ⟧ x := by
  have hcl : IsClosed {v : H | M.supportProj ξ (M′.supportProj η v) = v} :=
    isClosed_eq ((M.supportProj ξ).continuous.comp (M′.supportProj η).continuous) continuous_id
  have hsub : Set.range (S[M]⟦η, ξ⟧).closure ⊆
      {v : H | M.supportProj ξ (M′.supportProj η v) = v} := by
    rintro _ ⟨p, rfl⟩
    exact supportProj_apply_supportProj_of_mem_graph_closure ((S[M]⟦η, ξ⟧).closure.mem_graph p)
  exact closure_minimal hsub hcl
    ((isSelfAdjoint_relativeModular M η ξ).polarIsometry_apply_mem_closure_range
      (restrictScalars_relativeModular M η ξ) (isClosed_closure_relativeTomita M η ξ) x)

/-- **`ran J_{η,ξ} = s(ξ) s′(η) H`** for arbitrary `η, ξ` (Araki–Masuda 1982, §2): the final space
of the partial isometry `J_{η,ξ}`. The range of `J_{η,ξ}` is closed and contains `ran S̄_{η,ξ}`,
which is dense in `s(ξ) s′(η) H` (`VonNeumannAlgebra.supportProj_apply_supportProj_mem_closure_range`).
-/
lemma range_relativeModularConj :
    Set.range J[M]⟦η, ξ⟧ = Set.range (M.supportProj ξ * M′.supportProj η) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨J[M]⟦η, ξ⟧ x, ?_⟩
    rw [mul_apply_eq_comp]
    exact supportProj_apply_supportProj_relativeModularConj x
  · rintro ⟨y, rfl⟩
    have h := supportProj_apply_supportProj_mem_closure_range (M := M) (η := η) (ξ := ξ) y
    rw [← mul_apply_eq_comp] at h
    have hA := isSelfAdjoint_relativeModular M η ξ
    have hAT := restrictScalars_relativeModular M η ξ
    have hT := isClosed_closure_relativeTomita M η ξ
    exact (hA.isClosed_range_polarIsometry hAT hT).closure_subset_iff.mpr
      (hA.range_subset_range_polarIsometry hAT hT) h

/-- `J_{η,ξ}† = J_{ξ,η}` for the polar isometries (`adjoint_relativeModularConj`). -/
private lemma adjoint_polarIsometry_relativeModular :
    ((isSelfAdjoint_relativeModular M η ξ).polarIsometry
      (restrictScalars_relativeModular M η ξ) (isClosed_closure_relativeTomita M η ξ))† =
    (isSelfAdjoint_relativeModular M ξ η).polarIsometry (restrictScalars_relativeModular M ξ η)
      (isClosed_closure_relativeTomita M ξ η) := by
  set hA := isSelfAdjoint_relativeModular M η ξ
  set hAT := restrictScalars_relativeModular M η ξ
  set hT := isClosed_closure_relativeTomita M η ξ
  set T := (S[M]⟦η, ξ⟧).closure
  set T' := (S[M]⟦ξ, η⟧).closure
  set J := hA.polarIsometry hAT hT
  set W := J†
  set P := hA.pvm (Ioi 0)
  -- the supports `e = s(ξ) s′(η)` (final space of `J`) and `f = s(η) s′(ξ)` (initial space)
  set e := M.supportProj ξ * M′.supportProj η
  set f := M.supportProj η * M′.supportProj ξ
  have he : IsStarProjection e := (M.isStarProjection_supportProj ξ).mul
    (M′.isStarProjection_supportProj η) (commute_supportProj_supportProj_commutant M ξ η)
  have hf : IsStarProjection f := (M.isStarProjection_supportProj η).mul
    (M′.isStarProjection_supportProj ξ) (commute_supportProj_supportProj_commutant M η ξ)
  have hsym : ∀ {q : H →L[ℂ] H}, IsStarProjection q → ∀ a b, inner ℝ (q a) b = inner ℝ a (q b) :=
    fun hq a b => by
      rw [inner_real_eq_re_inner, inner_real_eq_re_inner, ← ContinuousLinearMap.adjoint_inner_right,
        ← ContinuousLinearMap.star_eq_adjoint, hq.isSelfAdjoint.star_eq]
  have hidem : ∀ {q : H →L[ℂ] H}, IsStarProjection q → ∀ a, q (q a) = q a := fun hq a => by
    rw [← mul_apply_eq_comp, hq.isIdempotentElem.eq]
  have hP : ∀ a b, inner ℝ (P a) b = inner ℝ a (P b) := hsym (hA.pvm.isStarProjection _)
  -- polar decomposition of `T` and the swap
  have hpol : ∀ w v, (w, v) ∈ T.graph ↔ ∃ q, (w, q) ∈ hA.sqrt.graph ∧ J q = v := fun w v =>
    mem_graph_closure_relativeTomita_iff
  have hswap : ∀ y w, (y, w) ∈ T'.graph → (w, e y) ∈ T.graph := fun y w h => by
    simpa only [e, mul_apply_eq_comp] using mem_graph_closure_relativeTomita_swap h
  have hkey : ∀ y w, (y, w) ∈ T'.graph → ∃ q, (w, q) ∈ hA.sqrt.graph ∧ J q = e y :=
    fun y w h => (hpol w (e y)).mp (hswap y w h)
  have hPq : ∀ w q, (w, q) ∈ hA.sqrt.graph → P q = q := fun w q h => by
    -- `E_Δ((0, ∞)) Δ^{1/2} = Δ^{1/2}` at the graph point `(w, q)`
    have h' : (w, P q) ∈ hA.sqrt.graph := by
      rw [← hA.pvm_Ioi_compPMap_sqrt]
      exact LinearPMap.mem_graph_compPMap.mpr ⟨q, h, rfl⟩
    exact sub_eq_zero.mp (hA.sqrt.graph_fst_eq_zero_snd (hA.sqrt.graph.sub_mem h' h) (sub_self w))
  -- `ran J ⊆ e H`
  have hJe : ∀ x, e (J x) = J x := fun x => by
    rw [mul_apply_eq_comp]
    exact supportProj_apply_supportProj_relativeModularConj x
  -- `ran S̄_{ξ,η} ⊆ f H ⊆ E_Δ((0, ∞)) H`
  have hran : ∀ y w, (y, w) ∈ T'.graph → P w = w := fun y w h => by
    have hfw : f w = w := by
      rw [mul_apply_eq_comp]
      exact supportProj_apply_supportProj_of_mem_graph_closure h
    refine hA.pvm_Ioi_apply_eq_self hAT hT ((Submodule.mem_orthogonal _ _).mpr fun k hk => ?_)
    have hfk : f k = 0 := by
      rw [mul_apply_eq_comp]
      exact mem_graph_closure_relativeTomita_zero_iff.mp (LinearPMap.mem_graph_zero_iff_mem_ker.mpr hk)
    rw [← hfw, ← hsym hf, hfk, inner_zero_left]
  have hWJ : ∀ w, W (J w) = P w := hA.adjoint_polarIsometry_apply_polarIsometry hAT hT
  have hJq : ∀ w q, (w, q) ∈ hA.sqrt.graph → ∀ a, inner ℝ (J a) (J q) = inner ℝ a q :=
    fun w q h a => by
      rw [hA.inner_polarIsometry_apply hAT hT, hP, hidem (hA.pvm.isStarProjection _), hPq w q h]
  -- `R = J S̄_{ξ,η}`
  set R : H →ₗ.[ℝ] H := (J : H →ₗ[ℝ] H).compPMap T'
  have hRg : ∀ y v, (y, v) ∈ R.graph ↔ ∃ w, (y, w) ∈ T'.graph ∧ J w = v := fun _ _ =>
    LinearPMap.mem_graph_compPMap
  have hRsemi : LinearPMap.IsSemilinear (RingHom.id ℂ) R := fun c y v h => by
    obtain ⟨w, hw, rfl⟩ := (hRg y v).mp h
    refine (hRg _ _).mpr ⟨_, isSemilinear_closure_relativeTomita M ξ η c y w hw, ?_⟩
    rw [hA.polarIsometry_smul_of_isSemilinear hAT hT (isSemilinear_closure_relativeTomita M η ξ),
      starRingEnd_self_apply, RingHom.id_apply]
  -- `⟪J w, y'⟫ = ⟪w, q'⟫` for `(y', w') ∈ S̄_{ξ,η}`, `Δ^{1/2} w' = q'`
  have hside : ∀ w y' w' q', (y', w') ∈ T'.graph → (w', q') ∈ hA.sqrt.graph → J q' = e y' →
      inner ℝ (J w) y' = inner ℝ w q' := fun w y' w' q' _ hq' hJq' => by
    rw [← hJe w, hsym he, ← hJq', hJq w' q' hq']
  have hRsym : R.IsFormalAdjoint R := LinearPMap.isFormalAdjoint_of_mem_graph
    fun y v y' v' h h' => by
      obtain ⟨w, hw, rfl⟩ := (hRg y v).mp h
      obtain ⟨w', hw', rfl⟩ := (hRg y' v').mp h'
      obtain ⟨q, hq, hJq₁⟩ := hkey y w hw
      obtain ⟨q', hq', hJq₂⟩ := hkey y' w' hw'
      rw [hside w y' w' q' hw' hq' hJq₂, real_inner_comm (J w') y, hside w' y w q hw hq hJq₁,
        inner_real_eq_re_inner, inner_real_eq_re_inner,
        ← hA.isSelfAdjoint_sqrt.isFormalAdjoint.inner_eq_of_mem_graph hq hq', ← inner_conj_symm,
        conj_re]
  have hRpos : R.IsPositive := by
    refine ⟨hRsym, fun x => ?_⟩
    obtain ⟨w, hw, hJw⟩ := (hRg x (R x)).mp (R.mem_graph x)
    obtain ⟨q, hq, hJq₁⟩ := hkey x w hw
    obtain ⟨⟨w₀, hw₀⟩, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp hq
    have h := hA.isPositive_sqrt.re_inner_nonneg_left ⟨w₀, hw₀⟩
    rw [RCLike.re_to_real, ← hJw, hside _ _ _ _ hw (hA.sqrt.mem_graph ⟨w₀, hw₀⟩) hJq₁,
      inner_real_eq_re_inner, ← inner_conj_symm, conj_re]
    exact h
  -- `ran (R + 1) = H`
  have hrange : ∀ z, ∃ y v, (y, v) ∈ R.graph ∧ v + y = z := by
    intro z
    have hez : e z ∈ Set.range J :=
      (range_relativeModularConj (M := M) (η := η) (ξ := ξ)).ge ⟨z, rfl⟩
    obtain ⟨p₀, hp₀⟩ := hez
    have hres := LinearPMap.IsPositive.mem_resolventSet hA.isSelfAdjoint_sqrt hA.isPositive_sqrt
      (z := (-1 : ℂ)) (by simp)
    have hr := hA.sqrt.graph.neg_mem (LinearPMap.resolvent_mem_graph hres p₀)
    set a := -hA.sqrt.resolvent (-1) p₀
    set c := -((-1 : ℂ) • hA.sqrt.resolvent (-1) p₀ - p₀)
    have hac : a + c = p₀ := by
      simp only [a, c, neg_smul, one_smul, neg_sub, sub_neg_eq_add]
      abel
    have h₁ : (a, J c) ∈ T.graph := (hpol _ _).mpr ⟨c, hr, rfl⟩
    have h₂ := mem_graph_closure_relativeTomita_swap h₁
    rw [← mul_apply_eq_comp] at h₂
    have hJfa : J (f a) = J a := by
      have hk : (a - f a, 0) ∈ T.graph := by
        refine mem_graph_closure_relativeTomita_of_supportProj_apply_eq_zero ?_
        rw [← mul_apply_eq_comp, map_sub, hidem hf, sub_self]
      have hk0 : hA.pvm (Ioi 0) (a - f a) = 0 :=
        hA.ker_le_ker_pvm_Ioi hAT hT (LinearPMap.mem_graph_zero_iff_mem_ker.mp hk)
      have hJk : J (a - f a) = 0 := norm_eq_zero.mp (by
        rw [hA.norm_polarIsometry_apply hAT hT, hk0, norm_zero])
      rw [map_sub, sub_eq_zero] at hJk
      exact hJk.symm
    have h₃ : (z - e z, 0) ∈ T'.graph := by
      refine mem_graph_closure_relativeTomita_of_supportProj_apply_eq_zero ?_
      rw [← mul_apply_eq_comp, map_sub, hidem he, sub_self]
    refine ⟨J c + (z - e z), J a + 0, (hRg _ _).mpr ⟨f a + 0, T'.graph.add_mem h₂ h₃, ?_⟩, ?_⟩
    · rw [add_zero, add_zero, hJfa]
    · rw [add_zero, ← add_assoc, ← map_add, hac, hp₀, add_sub_cancel]
  have hRsa : IsSelfAdjoint R := hRsym.isSelfAdjoint_of_surjective 1
    (LinearPMap.surjective_vadd_iff.mpr fun z => by
      obtain ⟨y, v, h, hvy⟩ := hrange z
      exact ⟨y, v, h, by rw [← hvy, add_comm, LinearMap.smul_apply, LinearMap.id_apply,
        RCLike.ofReal_one, one_smul]⟩)
  have hBg : ∀ y v, (y, v) ∈ hRsemi.toLinearPMap.graph ↔ (y, v) ∈ R.graph := fun _ _ =>
    hRsemi.mem_graph_toLinearPMap
  refine (isSelfAdjoint_relativeModular M ξ η).eq_polarIsometry_of_eq_compPMap
    (restrictScalars_relativeModular M ξ η) (isClosed_closure_relativeTomita M ξ η)
    (hRsemi.isSelfAdjoint_toLinearPMap hRsa) (hRsemi.isPositive_toLinearPMap hRpos) W
    (fun y hy => ?_) (fun x hx => ?_) ?_
  · obtain ⟨x, h⟩ := LinearPMap.mem_range_iff.mp hy
    obtain ⟨w, -, rfl⟩ := (hRg x y).mp ((hBg x y).mp h)
    rw [hWJ, hA.norm_polarIsometry_apply hAT hT]
  · have h := LinearPMap.mem_graph_zero_iff_mem_ker.mpr hx
    change W x = 0
    obtain ⟨w, hw, hJw⟩ := (hRg x 0).mp ((hBg x 0).mp h)
    obtain ⟨q, hq, hJq₁⟩ := hkey x w hw
    have hPw : P w = 0 := by
      rw [← norm_eq_zero, ← hA.norm_polarIsometry_apply hAT hT, hJw, norm_zero]
    have hq0 : q = 0 := by
      have h' := LinearPMap.compPMap_le_compNat_toPMap_iff.mp
        (hA.pvm_compPMap_sqrt_le (measurableSet_Ioi (a := (0 : ℝ)))) hq
      simp only [ContinuousLinearMap.coe_coe] at h'
      rw [hPw, hPq w q hq] at h'
      exact hA.sqrt.graph_fst_eq_zero_snd h' rfl
    have hex : e x = 0 := by rw [← hJq₁, hq0, map_zero]
    refine hA.adjoint_polarIsometry_apply_eq_zero hAT hT fun v => ?_
    rw [← hJe v, ← hsym he, hex, inner_zero_left]
  · rw [hRsemi.restrictScalars_toLinearPMap]
    refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨y, v⟩ => ?_)
    rw [LinearPMap.mem_graph_compPMap]
    constructor
    · intro h
      exact ⟨J v, (hRg _ _).mpr ⟨v, h, rfl⟩, by rw [ContinuousLinearMap.coe_coe, hWJ, hran y v h]⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (hRg _ _).mp hu
      rw [ContinuousLinearMap.coe_coe, hWJ, hran y w hw]
      exact hw

/-- **`J_{η,ξ}† = J_{ξ,η}`** for arbitrary `η, ξ` (Araki–Masuda 1982, §2): the real adjoint `J†` of
the polar isometry `J = J_{η,ξ}` of `S̄_{η,ξ}` is the polar isometry of `S̄_{ξ,η}`; in complex form,
`⟪J_{ξ,η} x, y⟫ = ⟪J_{η,ξ} y, x⟫` (`VonNeumannAlgebra.inner_relativeModularConj_left`).

The proof is the uniqueness of the polar decomposition
(`IsSelfAdjoint.eq_polarIsometry_of_eq_compPMap`). `S̄_{ξ,η}` inverts `S̄_{η,ξ}` between the supports
(`VonNeumannAlgebra.closure_relativeTomita_compNat_le`), so on the supports
`S̄_{ξ,η} = S̄_{η,ξ}⁻¹ = Δ_{η,ξ}^{-1/2} J†`, and `R = J S̄_{ξ,η}`, which is `J Δ_{η,ξ}^{-1/2} J†`
there, is positive and self-adjoint (`LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_surjective`); then
`S̄_{ξ,η} = J† R` is a polar decomposition of `S̄_{ξ,η}`.

TODO: the same computation gives `Δ_{ξ,η} = J_{η,ξ} Δ_{η,ξ}^{-1} J_{η,ξ}†` and
`Δ_{ξ,η}^{it} = J_{η,ξ} Δ_{η,ξ}^{it} J_{η,ξ}†`. With it the boundary value
`Δ_{η₂,Ω₂}^{-it} J_{Ω₂,η₂} V J_{η₁,Ω₁} Δ_{η₁,Ω₁}^{it}` of the relative Theorem A
(`VonNeumannAlgebra.exists_relativeModularGroup_continuation`) becomes
`J_{Ω₂,η₂} Ṽ(t) J_{η₁,Ω₁}` with `Ṽ(t) = Δ_{Ω₂,η₂}^{-it} V Δ_{Ω₁,η₁}^{it}`, the continuation for the
swapped pairs; it is Borchers' form `J V(t) J` only for `ηᵢ = Ωᵢ`. -/
lemma adjoint_relativeModularConj : ((J[M]⟦η, ξ⟧ : H →L[ℝ] H)†) = J[M]⟦ξ, η⟧ :=
  adjoint_polarIsometry_relativeModular

/-- **`J_{ξ,η} J_{η,ξ} = E_Δ((0, ∞))`**, the support projection of `Δ_{η,ξ}`, for arbitrary `η, ξ`
(Araki–Masuda 1982, §2, where `J_{η,ξ}† = J_{ξ,η}`): `J_{η,ξ}` is a partial isometry with initial
space `E_Δ((0, ∞)) H`, so `J_{ξ,η} J_{η,ξ} Δ_{η,ξ}^{1/2} = Δ_{η,ξ}^{1/2}`
(`IsSelfAdjoint.pvm_Ioi_compPMap_sqrt`). -/
lemma relativeModularConj_comp_relativeModularConj :
    (J[M]⟦ξ, η⟧.comp J[M]⟦η, ξ⟧ : H →L[ℂ] H) = (isSelfAdjoint_relativeModular M η ξ).pvm (Ioi 0) := by
  ext u
  change J[M]⟦ξ, η⟧ (J[M]⟦η, ξ⟧ u) = _
  rw [relativeModularConj_apply, relativeModularConj_apply, ← adjoint_polarIsometry_relativeModular,
    IsSelfAdjoint.adjoint_polarIsometry_apply_polarIsometry]

/-- **The initial projection of `J_{η,ξ}`**: the support projection `E_Δ((0, ∞))` of `Δ_{η,ξ}` is
`s(η) s′(ξ)` for arbitrary `η, ξ` (Araki–Masuda 1982, §2), since `E_Δ((0, ∞))` projects onto
`(ker Δ_{η,ξ})ᗮ` (`IsSelfAdjoint.pvm_Ioi_eq_starProjection_orthogonal`) and
`ker Δ_{η,ξ} = ker S̄_{η,ξ} = ker s(η) s′(ξ)` (`VonNeumannAlgebra.ker_relativeModular`,
`VonNeumannAlgebra.ker_closure_relativeTomita`). -/
lemma pvm_Ioi_relativeModular :
    (isSelfAdjoint_relativeModular M η ξ).pvm (Ioi 0) = M.supportProj η * M′.supportProj ξ := by
  have hf : IsStarProjection (M.supportProj η * M′.supportProj ξ) :=
    (M.isStarProjection_supportProj η).mul (M′.isStarProjection_supportProj ξ)
      (commute_supportProj_supportProj_commutant M η ξ)
  obtain ⟨K, hK, hfK⟩ := isStarProjection_iff_eq_starProjection.mp hf
  have hker : (Δ[M]⟦η, ξ⟧).ker = Kᗮ := by
    apply Submodule.restrictScalars_injective ℝ
    rw [ker_relativeModular, ker_closure_relativeTomita, hfK, Submodule.ker_starProjection]
  rw [(isSelfAdjoint_relativeModular M η ξ).pvm_Ioi_eq_starProjection_orthogonal
    (isPositive_relativeModular M η ξ), hfK]
  have h : (Δ[M]⟦η, ξ⟧).kerᗮ = K := by rw [hker, Submodule.orthogonal_orthogonal]
  subst h
  rfl

/-- **The modular conjugation of `(M, Ω)`**: for a cyclic and separating `Ω`, `J_{Ω,Ω}` is the
modular conjugation `J_{H_M}` of the standard subspace `H_M`. Both are the isometric part of the
polar decomposition of `S̄_{Ω,Ω} = S_{H_M}` (`VonNeumannAlgebra.closure_relativeTomita_self_eq_tomita`),
which is unique (`IsSelfAdjoint.eq_polarIsometry_of_eq_compPMap`). -/
lemma relativeModularConj_self {Ω : H} (hc : IsCyclicVector M Ω) (hs : IsSeparatingVector M Ω) :
    J[M]⟦Ω, Ω⟧ = (J[H[M, Ω]] : H →L⋆[ℂ] H) := by
  refine ContinuousLinearMap.ext fun x => ?_
  set K := H[M, Ω]
  set Jr := K.isSelfAdjoint_modular.polarIsometry K.restrictScalars_modular K.isClosed_tomita
  have hJr : ∀ y, J[K] y = Jr y := fun _ => rfl
  have hT : (S[M]⟦Ω, Ω⟧).closure =
      (Jr : H →ₗ[ℝ] H).compPMap (Δ[K]^{1/2}.restrictScalars ℝ) := by
    rw [closure_relativeTomita_self_eq_tomita hc hs]
    exact K.tomita_eq_modularConj_compPMap
  have h := (isSelfAdjoint_relativeModular M Ω Ω).eq_polarIsometry_of_eq_compPMap
    (restrictScalars_relativeModular M Ω Ω) (isClosed_closure_relativeTomita M Ω Ω)
    K.isSelfAdjoint_modular.isSelfAdjoint_sqrt K.isSelfAdjoint_modular.isPositive_sqrt Jr
    (fun y _ => K.isSelfAdjoint_modular.norm_polarIsometry_of_ker_eq_bot K.restrictScalars_modular
      K.isClosed_tomita K.ker_tomita_eq_bot y)
    (by rw [K.ker_sqrt_modular_eq_bot, Submodule.restrictScalars_bot]; exact bot_le) hT
  change J[M]⟦Ω, Ω⟧ x = J[K] x
  rw [relativeModularConj_apply, hJr, h]

/-- **`J_{ξ,η} = J_{η,ξ}†`** for arbitrary `η, ξ` (Araki–Masuda 1982, §2):
`⟪J_{ξ,η} x, y⟫ = ⟪J_{η,ξ} y, x⟫`, the adjoint relation of conjugate-linear operators. -/
lemma inner_relativeModularConj_left (x y : H) :
    ⟪J[M]⟦ξ, η⟧ x, y⟫_ℂ = ⟪J[M]⟦η, ξ⟧ y, x⟫_ℂ := by
  have hre : ∀ x, re ⟪J[M]⟦ξ, η⟧ x, y⟫_ℂ = re ⟪x, J[M]⟦η, ξ⟧ y⟫_ℂ := fun x => by
    rw [← inner_real_eq_re_inner, ← inner_real_eq_re_inner, relativeModularConj_apply,
      relativeModularConj_apply, ← adjoint_polarIsometry_relativeModular,
      ContinuousLinearMap.adjoint_inner_left]
  have h₁ := hre x
  have h₂ := hre (I • x)
  rw [map_smulₛₗ, inner_smul_left, inner_smul_left, starRingEnd_self_apply, conj_I] at h₂
  simp only [mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_re, neg_mul] at h₂
  refine Complex.ext ?_ ?_
  · rw [h₁, ← inner_conj_symm, conj_re]
  · rw [← inner_conj_symm (J[M]⟦η, ξ⟧ y), conj_im]
    linarith

/-- **`J_{ξ,η} J_{η,ξ} = 1`** for `ξ` cyclic and `η` separating: then `S̄_{η,ξ}` is injective
(`VonNeumannAlgebra.ker_closure_relativeTomita_eq_bot`), so `J_{η,ξ}` is isometric and
`J_{ξ,η} = J_{η,ξ}†` (`VonNeumannAlgebra.inner_relativeModularConj_left`) is a left inverse. -/
lemma relativeModularConj_relativeModularConj (hc : IsCyclicVector M ξ)
    (hsη : IsSeparatingVector M η) (x : H) : J[M]⟦ξ, η⟧ (J[M]⟦η, ξ⟧ x) = x := by
  rw [relativeModularConj_apply, relativeModularConj_apply, ← adjoint_polarIsometry_relativeModular,
    IsSelfAdjoint.adjoint_polarIsometry_apply_polarIsometry,
    IsSelfAdjoint.pvm_Ioi_eq_one_of_ker_eq_bot _ (restrictScalars_relativeModular M η ξ)
      (ker_closure_relativeTomita_eq_bot hc hsη), one_apply_eq_self]

/-- For `ξ` cyclic and `η` separating, `J_{η,ξ}` is isometric, since `S̄_{η,ξ}` is injective. -/
lemma norm_relativeModularConj_apply (hc : IsCyclicVector M ξ) (hsη : IsSeparatingVector M η)
    (x : H) : ‖J[M]⟦η, ξ⟧ x‖ = ‖x‖ := by
  rw [relativeModularConj_apply]
  exact (isSelfAdjoint_relativeModular M η ξ).norm_polarIsometry_of_ker_eq_bot
    (restrictScalars_relativeModular M η ξ) (isClosed_closure_relativeTomita M η ξ)
    (ker_closure_relativeTomita_eq_bot hc hsη) x

/-- For `η` cyclic and `ξ` separating, `J_{η,ξ}` is onto, with right inverse `J_{ξ,η}`. Together
with `VonNeumannAlgebra.norm_relativeModularConj_apply`, `J_{η,ξ}` is **antiunitary** for `ξ`, `η`
cyclic and separating (`VonNeumannAlgebra.relativeModularConjEquiv`). -/
lemma surjective_relativeModularConj (hcη : IsCyclicVector M η) (hs : IsSeparatingVector M ξ) :
    Function.Surjective J[M]⟦η, ξ⟧ := fun x =>
  ⟨J[M]⟦ξ, η⟧ x, relativeModularConj_relativeModularConj hcη hs x⟩

/-- **The relative modular conjugation is antiunitary** for `ξ`, `η` cyclic and separating:
`J_{η,ξ}` as a conjugate-linear isometric equivalence, the isometric part
(`IsSelfAdjoint.polarIsometryEquiv`) of `S̄_{η,ξ} = J_{η,ξ} Δ_{η,ξ}^{1/2}`, which is injective
(`VonNeumannAlgebra.ker_closure_relativeTomita_eq_bot`) with dense range
(`VonNeumannAlgebra.dense_range_closure_relativeTomita`). Its inverse is `J_{ξ,η}`
(`VonNeumannAlgebra.relativeModularConjEquiv_symm_apply`). -/
noncomputable def relativeModularConjEquiv (hc : IsCyclicVector M ξ)
    (hs : IsSeparatingVector M ξ) (hcη : IsCyclicVector M η) (hsη : IsSeparatingVector M η) :
    H ≃ₗᵢ⋆[ℂ] H :=
  (isSelfAdjoint_relativeModular M η ξ).polarIsometryEquiv (restrictScalars_relativeModular M η ξ)
    (isClosed_closure_relativeTomita M η ξ) (ker_closure_relativeTomita_eq_bot hc hsη)
    (dense_range_closure_relativeTomita hs hcη) (isSemilinear_closure_relativeTomita M η ξ)

section Equiv

variable (hc : IsCyclicVector M ξ) (hs : IsSeparatingVector M ξ) (hcη : IsCyclicVector M η)
  (hsη : IsSeparatingVector M η)

/-- The antiunitary `relativeModularConjEquiv` is `J_{η,ξ}`. -/
@[simp]
lemma relativeModularConjEquiv_apply (x : H) :
    relativeModularConjEquiv hc hs hcη hsη x = J[M]⟦η, ξ⟧ x := rfl

/-- The inverse of the antiunitary `J_{η,ξ}` is `J_{ξ,η}`. -/
@[simp]
lemma relativeModularConjEquiv_symm_apply (x : H) :
    (relativeModularConjEquiv hc hs hcη hsη).symm x = J[M]⟦ξ, η⟧ x :=
  (LinearIsometryEquiv.symm_apply_eq _).mpr
    (relativeModularConj_relativeModularConj hcη hs x).symm

end Equiv

end RelativeModularConj

end VonNeumannAlgebra
