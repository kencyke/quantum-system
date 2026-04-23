module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import QuantumSystem.Analysis.CFC.TraceClass.Basic

/-!
# Duality of trace-class operators and bounded operators

This file establishes the duality between trace-class operators and bounded operators:
the dual space of `TraceClass H` is isometrically isomorphic to `H →L[ℂ] H` via the trace pairing.

This duality shows that bounded operators on a Hilbert space form a W*-algebra (von Neumann algebra
in the abstract sense), with the trace-class operators as the predual.


## Main results

* `instBoundedOperatorsWStarAlgebra`: `H →L[ℂ] H` is a W*-algebra.
-/

@[expose] public section


namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

section Dual

/-- For each bounded operator A, the map T ↦ Tr(AT) is a continuous linear functional. -/
noncomputable def toTraceClassDual (A : H →L[ℂ] H) : TraceClass H →L[ℂ] ℂ := by
  refine LinearMap.mkContinuous
    { toFun := tracePairing A
      map_add' := tracePairing_add_right A
      map_smul' := fun c T => by
        rw [tracePairing_smul_right, RingHom.id_apply, smul_eq_mul] }
    ‖A‖ ?_
  intro T
  unfold tracePairing
  calc ‖trace (mulLeft A T)‖
      ≤ ‖A‖ * traceNorm T := abs_trace_mul_le A T
    _ = ‖A‖ * ‖T‖ := rfl

/-- The norm bound: ‖toTraceClassDual A‖ ≤ ‖A‖. -/
lemma toTraceClassDual_norm_le (A : H →L[ℂ] H) : ‖toTraceClassDual A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro T
  have h := abs_trace_mul_le A T
  simp only [toTraceClassDual]
  unfold tracePairing
  calc ‖trace (mulLeft A T)‖
      ≤ ‖A‖ * traceNorm T := h
    _ = ‖A‖ * ‖T‖ := rfl

/-- The map A ↦ (T ↦ Tr(AT)) is injective. -/
lemma toTraceClassDual_injective : Function.Injective (toTraceClassDual (H := H)) := by
  intro A B h_eq
  ext x
  apply ext_inner_left ℂ
  intro y
  let T : TraceClass H := ⟨rankOne x y, isTraceClass_rankOne x y⟩
  have h : toTraceClassDual A T = toTraceClassDual B T := by
    exact congrFun (congrArg DFunLike.coe h_eq) T
  -- toTraceClassDual A T = tracePairing A T = trace (mulLeft A T) = trace ⟨A * T.toFun, _⟩
  -- And trace ⟨A * rankOne x y, _⟩ = ⟨y, Ax⟩ by trace_mul_rankOne
  have hA : toTraceClassDual A T = ⟪y, A x⟫_ℂ := by
    unfold toTraceClassDual tracePairing mulLeft
    simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact trace_mul_rankOne A x y
  have hB : toTraceClassDual B T = ⟪y, B x⟫_ℂ := by
    unfold toTraceClassDual tracePairing mulLeft
    simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact trace_mul_rankOne B x y
  rw [hA, hB] at h
  exact h

/-- The inverse map from dual functionals to bounded operators, constructed using Riesz
    representation. For φ : (TraceClass H)^*, we define A such that φ(|x⟩⟨y|) = ⟨y, Ax⟩.

    Construction: For fixed x, the map y ↦ φ(|x⟩⟨y|) is antilinear and continuous.
    Conjugating gives the linear functional y ↦ conj(φ(|x⟩⟨y|)).
    By Riesz representation, this equals y ↦ ⟨Ax, y⟩ for unique Ax ∈ H.
    So φ(|x⟩⟨y|) = conj(⟨Ax, y⟩) = ⟨y, Ax⟩. -/
noncomputable def fromTraceClassDual (φ : TraceClass H →L[ℂ] ℂ) : H →L[ℂ] H := by
  -- For each x, define the linear functional on H: y ↦ star(φ(rankOneLeft y x))
  -- Since rankOneLeft y x = rankOne x y which is antilinear in y,
  -- φ(rankOneLeft y x) is antilinear in y, so star of that is linear in y.
  -- By Riesz, this functional equals y ↦ ⟨F(x), y⟩ for a unique F(x).
  -- Then ⟨y, F(x)⟩ = star(⟨F(x), y⟩) = star(star(φ(...))) = φ(rankOneLeft y x).

  -- First, define the linear functional for each x
  let L : H → (H →L[ℂ] ℂ) := fun x => {
    toFun := fun y => star (φ (rankOneLeft y x))
    map_add' := fun y₁ y₂ => by
      -- rankOneLeft (y₁ + y₂) x = ⟨rankOne x (y₁ + y₂), _⟩
      -- rankOne x (y₁ + y₂) = rankOne x y₁ + rankOne x y₂
      have h : rankOneLeft (y₁ + y₂) x = rankOneLeft y₁ x + rankOneLeft y₂ x := by
        simp only [rankOneLeft_apply]
        ext1
        ext z
        change rankOne x (y₁ + y₂) z = (rankOneLeft y₁ x + rankOneLeft y₂ x).toFun z
        simp only [add_toFun, rankOneLeft_apply, rankOne_apply, inner_add_left, add_smul]
        rfl
      simp only [h, map_add, star_add]
    map_smul' := fun c y => by
      -- rankOneLeft (c • y) x = ⟨rankOne x (c • y), _⟩
      -- rankOne x (c • y) = star(c) • rankOne x y (antilinear in second arg)
      have h : rankOneLeft (c • y) x = (starRingEnd ℂ c) • rankOneLeft y x := by
        simp only [rankOneLeft_apply]
        ext1
        ext z
        simp only [smul_toFun]
        calc _ = rankOne x (c • y) z := rfl
          _ = ⟪c • y, z⟫_ℂ • x := rankOne_apply x (c • y) z
          _ = (star c * ⟪y, z⟫_ℂ) • x := by rw [inner_smul_left, starRingEnd_apply]
          _ = star c • (⟪y, z⟫_ℂ • x) := by rw [smul_smul]
          _ = star c • rankOne x y z := by rw [rankOne_apply]
          _ = _ := rfl
      simp only [h, map_smul, smul_eq_mul, star_mul, RingHom.id_apply, starRingEnd_apply, star_star]
      ring
    cont := by
      apply Continuous.comp Complex.continuous_conj
      apply Continuous.comp φ.cont
      -- Need continuity of y ↦ rankOneLeft y x
      -- This is Lipschitz: ‖rankOneLeft y₁ x - rankOneLeft y₂ x‖ = ‖x‖ * ‖y₁ - y₂‖
      apply LipschitzWith.continuous
      case K => exact ⟨‖x‖, norm_nonneg x⟩
      case hf =>
        intro y₁ y₂
        simp only [edist_dist]
        rw [dist_eq_norm, dist_eq_norm]
        have h : rankOneLeft y₁ x - rankOneLeft y₂ x = rankOneLeft (y₁ - y₂) x := by
          apply ext'
          ext z
          simp only [sub_toFun, rankOneLeft_apply, rankOne_apply, inner_sub_left, sub_smul]
          rfl
        rw [h, rankOneLeft_apply, TraceClass.norm_eq_traceNorm, traceNorm_rankOne, mul_comm]
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
        rw [← ENNReal.ofReal_eq_coe_nnreal (norm_nonneg x)]
        exact le_of_eq (mul_comm _ _) }
  -- Define F(x) via Riesz representation
  let F : H → H := fun x => (InnerProductSpace.toDual ℂ H).symm (L x)
  -- Show F is additive
  have hF_add : ∀ x₁ x₂, F (x₁ + x₂) = F x₁ + F x₂ := fun x₁ x₂ => by
    apply (InnerProductSpace.toDual ℂ H).injective
    ext y
    simp only [F, L, LinearIsometryEquiv.apply_symm_apply, map_add, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, star_add]
  -- Show F is scalar-multiplicative
  have hF_smul : ∀ (c : ℂ) (x : H), F (c • x) = c • F x := by
    intro c x
    apply (InnerProductSpace.toDual ℂ H).injective
    simp only [F, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.map_smulₛₗ]
    ext y
    simp only [ContinuousLinearMap.smul_apply, L, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, smul_eq_mul, starRingEnd_apply]
    have hrk : rankOneLeft y (c • x) = c • rankOneLeft y x := by
      simp only [rankOneLeft_apply]
      ext1; simp only [smul_toFun, rankOne_smul_left]
    rw [hrk, map_smul, smul_eq_mul, star_mul, mul_comm]
  -- Show F is bounded
  have hF_bound : ∀ x, ‖F x‖ ≤ ‖φ‖ * ‖x‖ := fun x => by
    simp only [F]
    rw [(InnerProductSpace.toDual ℂ H).symm.norm_map]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro y
    simp only [L, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    rw [norm_star]
    calc ‖φ (rankOneLeft y x)‖
        ≤ ‖φ‖ * ‖rankOneLeft y x‖ := φ.le_opNorm _
      _ = ‖φ‖ * (‖x‖ * ‖y‖) := by
          simp only [rankOneLeft_apply, TraceClass.norm_eq_traceNorm, traceNorm_rankOne]
      _ = ‖φ‖ * ‖x‖ * ‖y‖ := by ring
  exact LinearMap.mkContinuous ⟨⟨F, hF_add⟩, hF_smul⟩ ‖φ‖ hF_bound

/-- The key property: fromTraceClassDual φ satisfies ⟨y, (fromTraceClassDual φ) x⟩ = φ(|x⟩⟨y|). -/
lemma inner_fromTraceClassDual (φ : TraceClass H →L[ℂ] ℂ) (x y : H) :
    ⟪y, fromTraceClassDual φ x⟫_ℂ = φ (rankOneLeft y x) := by
  unfold fromTraceClassDual
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  conv_lhs => rw [← inner_conj_symm]
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, starRingEnd_apply]
  rw [star_star]

/-- Trace of A times rank-one equals the value from fromTraceClassDual. -/
lemma toTraceClassDual_rankOneLeft (A : H →L[ℂ] H) (x y : H) :
    toTraceClassDual A (rankOneLeft y x) = ⟪y, A x⟫_ℂ := by
  simp only [toTraceClassDual, rankOneLeft_apply]
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact trace_mul_rankOne A x y

/-- fromTraceClassDual is a left inverse to toTraceClassDual. -/
lemma fromTraceClassDual_toTraceClassDual (A : H →L[ℂ] H) :
    fromTraceClassDual (toTraceClassDual A) = A := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [inner_fromTraceClassDual, toTraceClassDual_rankOneLeft]

/-- toTraceClassDual is a right inverse to fromTraceClassDual on rank-one operators. -/
lemma toTraceClassDual_fromTraceClassDual_rankOne (φ : TraceClass H →L[ℂ] ℂ) (x y : H) :
    toTraceClassDual (fromTraceClassDual φ) (rankOneLeft y x) = φ (rankOneLeft y x) := by
  rw [toTraceClassDual_rankOneLeft, inner_fromTraceClassDual]

/-- The operator norm equals the trace dual norm: ‖A‖ = ‖toTraceClassDual A‖.

This is a key isometry result establishing that the map A ↦ toTraceClassDual A
preserves the operator norm. -/
lemma toTraceClassDual_norm (A : H →L[ℂ] H) : ‖toTraceClassDual A‖ = ‖A‖ := by
  apply le_antisymm (toTraceClassDual_norm_le A)
  -- Lower bound: ‖A‖ ≤ ‖toTraceClassDual A‖
  -- Use |⟪y, Ax⟩| = |toTraceClassDual A (rankOneLeft y x)| ≤ ‖toTraceClassDual A‖ * ‖rankOneLeft y x‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · -- ‖Ax‖ = sup_{‖y‖=1} |⟪y, Ax⟩| is attained at y = Ax/‖Ax‖
    by_cases hAx : A x = 0
    · simp only [hAx, norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · -- There exists unit y with |⟪y, Ax⟩| = ‖Ax‖
      -- Use y = Ax / ‖Ax‖ (as scalar multiplication)
      let y := ((‖A x‖ : ℝ)⁻¹ : ℂ) • A x
      have hAx_norm_ne : ‖A x‖ ≠ 0 := norm_ne_zero_iff.mpr hAx
      have hy_norm : ‖y‖ = 1 := by
        simp only [y, norm_smul]
        rw [show ‖((‖A x‖ : ℝ)⁻¹ : ℂ)‖ = ‖A x‖⁻¹ by
          rw [show ((‖A x‖ : ℝ)⁻¹ : ℂ) = ((‖A x‖ : ℝ) : ℂ)⁻¹ by simp]
          rw [norm_inv]
          congr 1
          have h := @RCLike.norm_ofReal ℂ _ ‖A x‖
          convert h using 2
          exact (abs_norm _).symm]
        exact inv_mul_cancel₀ hAx_norm_ne
      have h_inner : ‖⟪y, A x⟫_ℂ‖ = ‖A x‖ := by
        simp only [y, inner_smul_left]
        rw [inner_self_eq_norm_sq_to_K]
        rw [map_inv₀, Complex.conj_ofReal]
        have h : ((‖A x‖ : ℝ) : ℂ)⁻¹ * ((‖A x‖ : ℝ) : ℂ) ^ 2 = ((‖A x‖ : ℝ) : ℂ) := by
          rw [sq]; field_simp
        calc ‖((‖A x‖ : ℝ) : ℂ)⁻¹ * ((‖A x‖ : ℝ) : ℂ) ^ 2‖
            = ‖((‖A x‖ : ℝ) : ℂ)‖ := by rw [h]
          _ = |‖A x‖| := @RCLike.norm_ofReal ℂ _ ‖A x‖
          _ = ‖A x‖ := abs_norm _
      calc ‖A x‖
          = ‖⟪y, A x⟫_ℂ‖ := h_inner.symm
        _ = ‖toTraceClassDual A (rankOneLeft y x)‖ := by rw [toTraceClassDual_rankOneLeft]
        _ ≤ ‖toTraceClassDual A‖ * ‖rankOneLeft y x‖ := (toTraceClassDual A).le_opNorm _
        _ = ‖toTraceClassDual A‖ * (‖x‖ * ‖y‖) := by
            rw [rankOneLeft_apply, TraceClass.norm_eq_traceNorm, traceNorm_rankOne]
        _ = ‖toTraceClassDual A‖ * ‖x‖ := by rw [hy_norm, mul_one]

/-- toTraceClassDual is a right inverse to fromTraceClassDual.

The proof uses density of rank-one operators: both sides are continuous linear maps
that agree on rank-one operators (by toTraceClassDual_fromTraceClassDual_rankOne),
so they must agree on all of TraceClass H by density and continuity. -/
lemma toTraceClassDual_fromTraceClassDual
    (φ : TraceClass H →L[ℂ] ℂ) : toTraceClassDual (fromTraceClassDual φ) = φ := by
  -- Use ContinuousLinearMap.ext_on: two continuous linear maps agreeing on a dense
  -- generating set must be equal
  apply ContinuousLinearMap.ext_on dense_span_rankOne
  -- Show they agree on rank-one operators
  intro T hT
  obtain ⟨x, y, rfl⟩ := hT
  -- T = ⟨rankOne x y, isTraceClass_rankOne x y⟩ = rankOneLeft y x
  have h : (⟨rankOne x y, isTraceClass_rankOne x y⟩ : TraceClass H) = rankOneLeft y x := by
    simp only [rankOneLeft_apply]
  rw [h]
  exact toTraceClassDual_fromTraceClassDual_rankOne φ x y

/-- fromTraceClassDual is injective. -/
lemma fromTraceClassDual_injective :
    Function.Injective (fromTraceClassDual (H := H)) := by
  intro φ₁ φ₂ h
  have h' : toTraceClassDual (fromTraceClassDual φ₁) = toTraceClassDual (fromTraceClassDual φ₂) := by
    rw [h]
  rw [toTraceClassDual_fromTraceClassDual, toTraceClassDual_fromTraceClassDual] at h'
  exact h'

/-- fromTraceClassDual is additive. -/
lemma fromTraceClassDual_add (φ₁ φ₂ : TraceClass H →L[ℂ] ℂ) :
    fromTraceClassDual (φ₁ + φ₂) = fromTraceClassDual φ₁ + fromTraceClassDual φ₂ := by
  -- Use extensionality: two operators are equal iff they agree on all inner products
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.add_apply, inner_add_right,
      inner_fromTraceClassDual, inner_fromTraceClassDual, inner_fromTraceClassDual,
      ContinuousLinearMap.add_apply]

/-- fromTraceClassDual is scalar-homogeneous. -/
lemma fromTraceClassDual_smul (c : ℂ) (φ : TraceClass H →L[ℂ] ℂ) :
    fromTraceClassDual (c • φ) = c • fromTraceClassDual φ := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.smul_apply, inner_smul_right,
      inner_fromTraceClassDual, inner_fromTraceClassDual, ContinuousLinearMap.smul_apply]
  rfl

/-- The norm of fromTraceClassDual φ equals the norm of φ.

This follows from the bijection with toTraceClassDual and the isometry property. -/
lemma fromTraceClassDual_norm (φ : TraceClass H →L[ℂ] ℂ) :
    ‖fromTraceClassDual φ‖ = ‖φ‖ := by
  -- Use: ‖fromTraceClassDual φ‖ = ‖toTraceClassDual (fromTraceClassDual φ)‖ = ‖φ‖
  calc ‖fromTraceClassDual φ‖
      = ‖toTraceClassDual (fromTraceClassDual φ)‖ := (toTraceClassDual_norm _).symm
    _ = ‖φ‖ := by rw [toTraceClassDual_fromTraceClassDual]

end Dual

section WStarAlgebra

/-- Bounded operators on a Hilbert space form a W*-algebra, with trace-class operators
    as the predual.

This is a fundamental result in operator algebra theory. The construction uses:
1. The map `toTraceClassDual : B(H) → (TraceClass H)^*` given by `A ↦ (T ↦ Tr(AT))`
2. The inverse `fromTraceClassDual : (TraceClass H)^* → B(H)` via Riesz representation
3. The isometry property follows from the trace duality

Note: This establishes B(H) as a W*-algebra in the sense of Sakai, where a W*-algebra is
a C*-algebra that is the dual of some Banach space (called the predual). -/
instance instBoundedOperatorsWStarAlgebra : WStarAlgebra (H →L[ℂ] H) := by
  refine WStarAlgebra.mk ?_
  use TraceClass H
  use inferInstance  -- NormedAddCommGroup
  use inferInstance  -- NormedSpace ℂ
  use inferInstance  -- CompleteSpace
  -- We construct a conjugate-linear isometric equivalence
  -- (TraceClass H)^* ≃ₗᵢ⋆[ℂ] B(H)
  --
  -- The map: φ ↦ adjoint (fromTraceClassDual φ)
  -- The inverse: A ↦ toTraceClassDual (adjoint A)
  --
  -- This is conjugate-linear: (c • φ) ↦ adjoint (c • fromTraceClassDual φ) = conj(c) • adjoint (fromTraceClassDual φ)
  -- This is isometry: ‖adjoint (fromTraceClassDual φ)‖ = ‖fromTraceClassDual φ‖ = ‖φ‖
  -- This is bijection: composition of two bijections
  constructor
  -- Build the LinearIsometryEquiv
  let adj := adjoint (𝕜 := ℂ) (E := H) (F := H)
  refine LinearIsometryEquiv.mk ?_ ?_
  · -- The underlying LinearEquiv (starRingEnd ℂ)
    -- First create the semilinear map
    let f : StrongDual ℂ (TraceClass H) →ₛₗ[starRingEnd ℂ] (H →L[ℂ] H) :=
      { toFun := fun φ => adj (fromTraceClassDual φ)
        map_add' := fun φ₁ φ₂ => by
          change adj (fromTraceClassDual (φ₁ + φ₂)) = adj (fromTraceClassDual φ₁) + adj (fromTraceClassDual φ₂)
          rw [fromTraceClassDual_add, map_add]
        map_smul' := fun c φ => by
          change adj (fromTraceClassDual (c • φ)) = (starRingEnd ℂ) c • adj (fromTraceClassDual φ)
          rw [fromTraceClassDual_smul, adj.map_smulₛₗ] }
    refine LinearEquiv.ofBijective f ?_
    constructor
    · -- Injective
      intro φ₁ φ₂ h
      simp only [f] at h
      have h' : fromTraceClassDual φ₁ = fromTraceClassDual φ₂ := adj.injective h
      exact fromTraceClassDual_injective h'
    · -- Surjective
      intro A
      use toTraceClassDual (adj A)
      change adj (fromTraceClassDual (toTraceClassDual (adj A))) = A
      rw [fromTraceClassDual_toTraceClassDual, adjoint_adjoint]
  · -- Norm preservation: ‖adjoint (fromTraceClassDual φ)‖ = ‖φ‖
    intro φ
    rw [LinearEquiv.ofBijective_apply]
    change ‖adj (fromTraceClassDual φ)‖ = ‖φ‖
    rw [adj.norm_map, fromTraceClassDual_norm]

end WStarAlgebra

end TraceClass

end ContinuousLinearMap
