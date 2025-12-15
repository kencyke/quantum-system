import Mathlib.Analysis.InnerProductSpace.Completion
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.HilbertSpace
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Ideal
import QuantumSystem.Algebra.CStarAlgebra.State.Continuity


namespace GNS

namespace Construction

open ComplexConjugate NNReal Topology

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable (ω : State ℂ A)

private def Nω : CStarAlgebraIdeal A where
  carrier := { x : A | ω (star x * x) = 0 }
  zero_mem' := by
    change ω (star (0 : A) * (0 : A)) = 0
    simp [star_zero]
  add_mem' := by
    intro x y hx hy
    exact State.kernel_closed_under_add (ω := ω) (x := x) (y := y) hx hy
  neg_mem' := by
    intro x hx
    simpa [star_neg] using hx
  mul_mem' := by
    intro a x hx
    exact State.kernel_closed_under_left_mul (ω := ω) (a := a) (x := x) hx
  smul_mem' := by
    intro c x hx
    exact State.kernel_closed_under_smul (ω := ω) (c := c) (x := x) hx

local notation "Nω" => (Nω ω)

/-- Inner product on the quotient `A ⧸ Nω` defined by
`⟪[x], [y]⟫ = ω (star x * y)`.  Well-defined because the kernel ideal `Nω` is the null space
with respect to the positive sesquilinear form coming from the state `ω` (ultimately a
consequence of the Cauchy–Schwarz inequality for states). -/
private def innerQuotient (xq yq : A ⧸ Nω) : ℂ :=
  Quotient.liftOn₂' xq yq (fun x y => ω (star x * y))
    (fun x₁ y₁ x₂ y₂ (hx : CStarAlgebraIdeal.leftRel Nω x₁ x₂) (hy : CStarAlgebraIdeal.leftRel Nω y₁ y₂) => by
      rw [CStarAlgebraIdeal.leftRel, QuotientAddGroup.leftRel_apply] at hx hy
      show ω (star x₁ * y₁) = ω (star x₂ * y₂)
      have hx' : ω (star (x₂ - x₁) * (x₂ - x₁)) = 0 := by simp only [sub_eq_neg_add]; exact hx
      have hy' : ω (star (y₂ - y₁) * (y₂ - y₁)) = 0 := by simp only [sub_eq_neg_add]; exact hy
      calc ω (star x₁ * y₁)
          = ω (star x₂ * y₁) := (State.equiv_left (ω := ω) (x₁ := x₂) (x₂ := x₁) (y := y₁) hx').symm
        _ = ω (star x₂ * y₂) := (State.equiv_right (ω := ω) (x := x₂) (y₁ := y₂) (y₂ := y₁) hy').symm)

/-- The inner product space core structure on the quotient. -/
instance instInnerProductSpaceCore : InnerProductSpace.Core ℂ (A ⧸ Nω) where
  inner := innerQuotient ω
  conj_inner_symm := fun x y => Quotient.inductionOn₂' x y fun a b => by
    simp only [innerQuotient, Quotient.liftOn₂'_mk'']
    rw [State.conj_sym ω (x := b) (y := a)]
  re_inner_nonneg := fun x => Quotient.inductionOn' x fun a => by
    simp only [innerQuotient, Quotient.liftOn₂'_mk'']
    obtain ⟨r, hr⟩ := ω.positive a
    have hr' : ω (star a * a) = RCLike.ofReal (r : ℝ) := by
      simpa [State.toLinearMap_apply] using hr
    rw [hr']
    exact r.property
  add_left := fun x y z => Quotient.inductionOn₃' x y z fun a b c => by
    unfold innerQuotient
    show Quotient.liftOn₂' (Quotient.mk'' (a + b)) (Quotient.mk'' c) _ _ = _
    simp only [Quotient.liftOn₂'_mk'']
    rw [star_add, add_mul]
    exact ω.map_add (star a * c) (star b * c)
  smul_left := fun x y c => Quotient.inductionOn₂' x y fun a b => by
    unfold innerQuotient
    show Quotient.liftOn₂' (Quotient.mk'' (c • a)) (Quotient.mk'' b) _ _ = _
    simp only [Quotient.liftOn₂'_mk'']
    rw [star_smul, smul_mul_assoc]
    exact ω.map_smul (conj c) (star a * b)
  definite := fun x hx => Quotient.inductionOn' x (fun a ha => by
    simp [innerQuotient] at ha
    exact Quotient.sound' (by simpa [CStarAlgebraIdeal.leftRel, QuotientAddGroup.leftRel_apply] using ha)) hx

-- Pattern adapted from Mathlib 4.25+ Matrix.PosDef
-- First define NormedAddCommGroup from the Core (not an instance yet)
noncomputable def normedAddCommGroupQuot : NormedAddCommGroup (A ⧸ Nω) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (instInnerProductSpaceCore (ω := ω))

-- Then define InnerProductSpace using ofCore with explicit SeminormedAddCommGroup
noncomputable def innerProductSpaceQuot : @InnerProductSpace ℂ (A ⧸ Nω) _ (normedAddCommGroupQuot (ω := ω)).toSeminormedAddCommGroup :=
  letI : InnerProductSpace.Core ℂ (A ⧸ Nω) := instInnerProductSpaceCore (ω := ω)
  @InnerProductSpace.ofCore ℂ _ _ (normedAddCommGroupQuot (ω := ω)).toAddCommGroup _ inferInstance

-- Now make them instances
noncomputable instance instNormedAddCommGroupQuot : NormedAddCommGroup (A ⧸ Nω) :=
  normedAddCommGroupQuot (ω := ω)

noncomputable instance instInnerProductSpaceQuot : InnerProductSpace ℂ (A ⧸ Nω) :=
  innerProductSpaceQuot (ω := ω)

/-- The squared norm of the class `[x]` equals the real part `Re (ω (star x * x))`. -/
private lemma norm_sq_eq_inner (x : A) :
    @norm (A ⧸ Nω) (instNormedAddCommGroupQuot ω).toNorm (Quotient.mk'' x) ^ 2 = (ω (star x * x)).re := by
  rw [@norm_sq_eq_re_inner ℂ (A ⧸ Nω) _ _]
  show ((@inner ℂ (A ⧸ Nω) _ (Quotient.mk'' x) (Quotient.mk'' x))).re = (ω (star x * x)).re
  change (innerQuotient ω (Quotient.mk'' x) (Quotient.mk'' x)).re = (ω (star x * x)).re
  unfold innerQuotient
  simp only [Quotient.liftOn₂'_mk'']

/-- Inner products with elements of the kernel ideal vanish: if `s ∈ Nω` then
`ω (star x * s) = 0`. -/
private lemma inner_kernel_elem_zero (x : A) (s : Nω) : ω (star x * s.val) = 0 :=
  State.kernel_degenerate_left (ω := ω) (x := s.val) (a := x) s.property

/-- The GNS Hilbert space `Hω`, defined as the completion of the quotient `A ⧸ Nω`. -/
abbrev Hω := UniformSpace.Completion (A ⧸ Nω)
local notation "Hω" => (Hω (ω := ω))

noncomputable instance instHilbertSpaceCompletion : ComplexHilbertSpace Hω :=
  { toNormedAddCommGroup := inferInstance
    toInnerProductSpace := inferInstance
    toCompleteSpace := inferInstance }

/-- Left multiplication action on the quotient: `πω'(a)[b] = [a b]`.
It is bounded (`‖πω'(a)[b]‖ ≤ ‖a‖ · ‖[b]‖`), multiplicative, and *-compatible, and thus
extends (after completion) to the bounded operator representation `πω : A → 𝓑(Hω)`. -/
private def πω' (a : A) (bq : A ⧸ Nω) : A ⧸ Nω :=
  Quotient.liftOn' bq (fun b => Quotient.mk'' (a * b))
    (fun b₁ b₂ (hb : CStarAlgebraIdeal.leftRel Nω b₁ b₂) => by
      rw [CStarAlgebraIdeal.leftRel, QuotientAddGroup.leftRel_apply] at hb
      apply Quotient.sound'
      rw [CStarAlgebraIdeal.leftRel, QuotientAddGroup.leftRel_apply]
      show -(a * b₁) + a * b₂ ∈ (Nω).toAddSubgroup
      rw [show -(a * b₁) + a * b₂ = a * (-b₁ + b₂) by simp only [mul_neg, mul_add]]
      exact (Nω).mul_mem' a hb)

/-- Action of `πω'` on a representative. -/
private lemma πω'_mk (a b : A) : πω' ω a (Quotient.mk'' b) = Quotient.mk'' (a * b) := rfl

/-- `πω'(0)` is the zero map. -/
private lemma πω'_zero (x : A ⧸ Nω) : πω' ω (0 : A) x = 0 := by
  refine Quotient.inductionOn' x fun b => ?_
  rw [πω'_mk, zero_mul]
  rfl

/-- Quadratic norm inequality on the pre-Hilbert quotient: `‖πω'(a)[b]‖^2 ≤ ‖a‖^2 ‖[b]‖^2`. -/
private lemma πω'_norm_sq_le (a : A) (b : A ⧸ Nω) : ‖πω' ω a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  refine Quotient.inductionOn' b fun b' => ?_
  -- Unfold the definition on a representative and rewrite the norm squared via inner product
  simp_rw [πω', Quotient.liftOn'_mk'', sq]
  -- Use inner_self = ‖·‖ * ‖·‖ in a pre-Hilbert setting (core inner product structure)
  rw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ) (E := A ⧸ Nω) (Quotient.mk'' (a * b'))]
  rw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ) (E := A ⧸ Nω) (Quotient.mk'' b')]
  show (innerQuotient ω (Quotient.mk'' (a * b')) (Quotient.mk'' (a * b'))).re ≤
    ‖a‖ * ‖a‖ * (innerQuotient ω (Quotient.mk'' b') (Quotient.mk'' b')).re
  unfold innerQuotient; simp only [Quotient.liftOn₂'_mk'']
  -- Algebraic rearrangement: bring star inside and reassociate to isolate star a * a
  rw [show star (a * b') * (a * b') = star b' * star a * a * b' by rw [star_mul, mul_assoc, mul_assoc, mul_assoc]]
  -- Apply the C*-algebraic Cauchy–Schwarz style inequality packaged in star_mul_bound
  obtain ⟨r, hr⟩ := State.star_mul_bound (ω := ω) (a := a) (b := b')
  -- Extract the real part inequality from the complex identity hr
  have h_re : (‖a‖ * ‖a‖ : ℝ) * (ω (star b' * b')).re = (ω (star b' * star a * a * b')).re + (r : ℝ) := by
    have h := congr_arg Complex.re hr
    simp only [Complex.mul_re, Complex.add_re] at h
    norm_cast at h
    simp only [zero_mul, sub_zero] at h
    rw [sq] at h
    exact h
  have : ‖a‖ * ‖a‖ * (ω (star b' * b')).re = ‖a‖ * (‖a‖ * (ω (star b' * b')).re) := mul_assoc _ _ _
  have hr_nonneg : (0 : ℝ) ≤ r := r.property
  -- Finish with linear arithmetic: nonneg remainder r gives desired ≤
  linarith

/-- Multiplicativity: πω'(ab) = πω'(a) ∘ πω'(b). -/
private lemma πω'_mul (a b : A) (c : A ⧸ Nω) : πω' ω (a * b) c = πω' ω a (πω' ω b c) :=
  Quotient.inductionOn' c fun c' => by unfold πω'; simp [mul_assoc]

/-- Adjoint property of the algebraic action: `⟪πω'(a) b, c⟫ = ⟪b, πω'(a*) c⟫`. -/
private lemma πω'_inner (a : A) (b c : A ⧸ Nω) :
    @inner ℂ (A ⧸ Nω) _ (πω' ω a b) c = @inner ℂ (A ⧸ Nω) _ b (πω' ω (star a) c) := by
  refine Quotient.inductionOn₂' b c fun b' c' => ?_
  unfold πω'
  simp only [Quotient.liftOn'_mk'']
  show innerQuotient ω (Quotient.mk'' (a * b')) (Quotient.mk'' c') = innerQuotient ω (Quotient.mk'' b') (Quotient.mk'' (star a * c'))
  unfold innerQuotient
  simp only [Quotient.liftOn₂'_mk'', star_mul, mul_assoc]

/-- Additivity: πω'(a)(b + c) = πω'(a)b + πω'(a)c. -/
private lemma πω'_add (a : A) (b c : A ⧸ Nω) : πω' ω a (b + c) = πω' ω a b + πω' ω a c := by
  refine Quotient.inductionOn₂' b c fun b' c' => ?_
  change πω' ω a (Quotient.mk'' (b' + c')) = πω' ω a (Quotient.mk'' b') + πω' ω a (Quotient.mk'' c')
  unfold πω'
  simp only [Quotient.liftOn'_mk'']
  congr 1
  exact mul_add a b' c'

/-- Scalar multiplication: πω'(a)(z • b) = z • πω'(a)b. -/
private lemma πω'_smul (a : A) (z : ℂ) (b : A ⧸ Nω) : πω' ω a (z • b) = z • πω' ω a b := by
  refine Quotient.inductionOn' b fun b' => ?_
  change πω' ω a (Quotient.mk'' (z • b')) = z • πω' ω a (Quotient.mk'' b')
  unfold πω'
  simp only [Quotient.liftOn'_mk'']
  congr 1
  exact mul_smul_comm z a b'

/-- Linear norm bound: `‖πω'(a) b‖ ≤ ‖a‖ · ‖b‖`, deduced from the quadratic bound. -/
private lemma πω'_norm_le (a : A) (b : A ⧸ Nω) : ‖πω' ω a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h_sq := πω'_norm_sq_le ω a b
  rw [show ‖a‖ ^ 2 * ‖b‖ ^ 2 = (‖a‖ * ‖b‖) ^ 2 by ring] at h_sq
  simpa [Real.sqrt_sq (norm_nonneg _), mul_nonneg (norm_nonneg a) (norm_nonneg b)] using
    Real.sqrt_le_sqrt h_sq

/-- Lipschitz continuity of `b ↦ πω'(a)b` with optimal constant `‖a‖`. -/
private lemma πω'_lipschitz (a : A) : ∃ C : ℝ≥0, ∀ b : A ⧸ Nω, ‖πω' ω a b‖ ≤ C * ‖b‖ :=
  ⟨⟨‖a‖, norm_nonneg a⟩, fun b => by simpa using πω'_norm_le (ω := ω) a b⟩

/-- Continuous linear map version of the pre-representation: `πω'(a) : A ⧸ Nω →L[ℂ] A ⧸ Nω`. -/
private noncomputable def πω'CLM (a : A) : (A ⧸ Nω) →L[ℂ] (A ⧸ Nω) :=
  LinearMap.mkContinuous
    { toFun := πω' ω a
      map_add' := πω'_add ω a
      map_smul' := πω'_smul ω a }
    ‖a‖
    (fun b => by
      simpa using πω'_norm_le (ω := ω) a b)

/-- The (completed) GNS representation `πω : A → 𝓑(Hω)` extending the action `πω'` from the
dense quotient into its Hilbert space completion. -/
noncomputable def πω (a : A) : 𝓑(Hω) :=
  ContinuousLinearMap.extend
    (UniformSpace.Completion.toComplL.comp (πω'CLM ω a))
    (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := A ⧸ Nω))

/-- Agreement on the dense subspace: `πω(a) (↑x) = ↑(πω'(a) x)` for `x : A ⧸ Nω`. -/
private lemma πω_apply_coe (a : A) (x : A ⧸ Nω) :
    πω ω a (↑x : Hω) = (↑(πω' ω a x) : Hω) := by
  unfold πω
  erw [ContinuousLinearMap.extend_eq
    (h_dense := UniformSpace.Completion.denseRange_coe (α := A ⧸ Nω))
    (h_e := (UniformSpace.Completion.isUniformEmbedding_coe (α := A ⧸ Nω)).isUniformInducing)]
  rfl

/-- Extensionality principle for operators on the completion: if they agree on the dense subspace, they are equal. -/
private lemma ext_on_completion (f g : 𝓑(Hω)) (h : ∀ x : A ⧸ Nω, f (↑x : Hω) = g (↑x : Hω)) : f = g := by
  ext x
  refine DenseRange.induction_on (p := fun y => f y = g y) UniformSpace.Completion.denseRange_coe x
    (isClosed_eq f.continuous g.continuous) fun y => by simpa using h y

/-- Multiplicativity of the extended representation: `πω(a b) = πω(a) ∘L πω(b)`. -/
lemma πω_mul (a b : A) : πω ω (a * b) = πω ω a ∘L πω ω b := by
  refine ext_on_completion (ω := ω) (πω ω (a * b)) (πω ω a ∘L πω ω b) ?_
  intro x
  simp [ContinuousLinearMap.comp_apply, πω_apply_coe, πω'_mul]

/-- *-preservation: `(πω(a)).adjoint = πω (star a)`. -/
private lemma πω_star (a : A) : (πω ω a).adjoint = πω ω (star a) := by
  ext x
  refine DenseRange.induction_on (p := fun x => (πω ω a).adjoint x = πω ω (star a) x)
    (UniformSpace.Completion.denseRange_coe (α := A ⧸ Nω)) x
    (isClosed_eq ((πω ω a).adjoint).continuous (πω ω (star a)).continuous)
    (fun c => ?_)
  -- Reduce to checking equality of inner products with arbitrary y (Riesz representation)
  have : ∀ y, @inner ℂ (Hω) _ ((πω ω a).adjoint (↑c)) y = @inner ℂ (Hω) _ (πω ω (star a) (↑c)) y := by
    intro y
    refine DenseRange.induction_on
      (p := fun y => @inner ℂ (Hω) _ ((πω ω a).adjoint (↑c)) y = @inner ℂ (Hω) _ (πω ω (star a) (↑c)) y)
      (UniformSpace.Completion.denseRange_coe (α := A ⧸ Nω)) y
      (isClosed_eq (Continuous.inner continuous_const continuous_id)
                    (Continuous.inner continuous_const continuous_id))
      (fun d => ?_)
    -- Now both vectors are in the dense subspace; rewrite via the quotient-level identity
    show @inner ℂ (Hω) _ ((πω ω a).adjoint (↑c)) (↑d) = @inner ℂ (Hω) _ (πω ω (star a) (↑c)) (↑d)
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [πω_apply_coe]
    rw [UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
    rw [πω'_inner, star_star]
  exact ext_inner_right ℂ this

/-- Additivity: `πω(a + b) = πω(a) + πω(b)`. -/
private lemma πω_add (a b : A) : πω ω (a + b) = πω ω a + πω ω b := by
  refine ext_on_completion (ω := ω) (πω ω (a + b)) (πω ω a + πω ω b) ?_
  intro x
  have : πω' ω (a + b) x = πω' ω a x + πω' ω b x :=
    Quotient.inductionOn' x fun c => by unfold πω'; simp only [Quotient.liftOn'_mk'', add_mul]; rfl
  simp [ContinuousLinearMap.add_apply, πω_apply_coe, this, UniformSpace.Completion.coe_add]

/-- Compatibility with scalar multiplication: `πω(z • a) = z • πω(a)`. -/
private lemma πω_smul (z : ℂ) (a : A) : πω ω (z • a) = z • πω ω a := by
  refine ext_on_completion (ω := ω) (πω ω (z • a)) (z • πω ω a) ?_
  intro x
  have : πω' ω (z • a) x = z • πω' ω a x :=
    Quotient.inductionOn' x fun c => by unfold πω'; simp only [Quotient.liftOn'_mk'', smul_mul_assoc]; rfl
  simp [ContinuousLinearMap.smul_apply, πω_apply_coe, this, UniformSpace.Completion.coe_smul]

/-- Subtraction compatibility for the extended representation. -/
lemma πω_sub (a b : A) : πω ω (a - b) = πω ω a - πω ω b := by
  have h_add := πω_add (ω := ω) a (-b)
  have h_neg : πω ω (-b) = -πω ω b := by
    simpa using πω_smul (ω := ω) (-1 : ℂ) b
  simpa [sub_eq_add_neg, h_neg] using h_add

/-- Zero element maps to zero operator: `πω(0) = 0`. -/
private lemma πω_zero : πω ω (0 : A) = 0 :=
  ext_on_completion (ω := ω) (πω ω 0) 0 fun x => by simp [πω_apply_coe, πω'_zero, UniformSpace.Completion.coe_zero]

/-- The bundled non‑unital *-homomorphism `πω : A →⋆ₙₐ[ℂ] 𝓑(Hω)`. -/
noncomputable def πωStarHom : A →⋆ₙₐ[ℂ] 𝓑(Hω) where
  toFun := πω ω
  map_smul' := fun z a => πω_smul ω z a
  map_zero' := πω_zero ω
  map_add' := πω_add ω
  map_mul' := fun a b => by
    rw [πω_mul ω a b]
    rfl
  map_star' := fun a => by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (πω_star ω a).symm

/-- Operator norm contraction: `‖πω(a)‖ ≤ ‖a‖`. -/
private lemma πω_opNorm_le (a : A) : ‖πω ω a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg a
  · intro x
    refine DenseRange.induction_on (p := fun x => ‖πω ω a x‖ ≤ ‖a‖ * ‖x‖)
      (UniformSpace.Completion.denseRange_coe (α := A ⧸ Nω)) x ?_ ?_
    · apply isClosed_le
      · exact continuous_norm.comp (πω ω a).continuous
      · exact continuous_const.mul continuous_norm
    · intro y
      rw [πω_apply_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact πω'_norm_le ω a y

/-- The induced linear functional on the quotient: `ω̃([x]) = ω x`, well-defined because
`ω` vanishes on the ideal `Nω`. -/
private noncomputable def stateOnQuotFun (xq : A ⧸ Nω) : ℂ :=
  Quotient.liftOn' xq (fun x => ω x)
    (fun x₁ x₂ hx => by
      rw [CStarAlgebraIdeal.leftRel, QuotientAddGroup.leftRel_apply] at hx
      have h_mem : x₂ - x₁ ∈ Nω := by simpa [sub_eq_add_neg, add_comm] using hx
      have : ω (x₂ - x₁) = 0 := State.kernel_vanish_on_elem (ω := ω) (x := x₂ - x₁) h_mem
      rw [← sub_eq_zero, ← map_sub, ← neg_sub x₂ x₁, map_neg, this, neg_zero])

/-- Additivity of the induced functional: `ω̃(x + y) = ω̃ x + ω̃ y`. -/
private lemma stateOnQuotFun_add (x y : A ⧸ Nω) :
    stateOnQuotFun ω (x + y) = stateOnQuotFun ω x + stateOnQuotFun ω y :=
  Quotient.inductionOn₂' x y fun a b => ω.map_add a b

/-- Scalar compatibility: `ω̃(c • x) = c • ω̃ x`. -/
private lemma stateOnQuotFun_smul (c : ℂ) (x : A ⧸ Nω) :
    stateOnQuotFun ω (c • x) = c • stateOnQuotFun ω x :=
  Quotient.inductionOn' x fun a => ω.map_smul c a

/-- Bound on the quotient functional: `‖ω̃ x‖ ≤ ‖x‖`. -/
private lemma stateOnQuotFun_bound (x : A ⧸ Nω) : ‖stateOnQuotFun ω x‖ ≤ 1 * ‖x‖ := by
  refine Quotient.inductionOn' x fun a => ?_
  -- Use the quotient NormedAddCommGroup instance introduced above
  -- Provide the NormedAddCommGroup instance explicitly for local typeclass resolution
  letI : NormedAddCommGroup (A ⧸ Nω) := instNormedAddCommGroupQuot ω
  simp only [stateOnQuotFun, Quotient.liftOn'_mk'', one_mul]
  -- Express quotient norm squared via ω to connect functional values to norms
  have h_sq : ‖(Quotient.mk'' a : A ⧸ Nω)‖ ^ 2 = (ω (star a * a)).re := norm_sq_eq_inner ω a
  have h_ω_lip : LipschitzWith 1 ω := State.lipschitzWith_one ω
  have h_approx := CStarAlgebra.increasingApproximateUnit (A := A)
  -- Convergence: ω(e*a) → ω a, hence norms squared tend to ‖ω a‖^2
  have h_tendsto : Filter.Tendsto (fun e => ‖ω (e * a)‖ ^ 2) (CStarAlgebra.approximateUnit A)
      (𝓝 (‖ω a‖ ^ 2)) :=
    (continuous_norm.pow 2).tendsto _ |>.comp <| h_ω_lip.continuous.tendsto _ |>.comp
      (h_approx.tendsto_mul_right a)
  -- Eventually bound: use Cauchy–Schwarz for states to dominate ‖ω(e*a)‖^2 by (ω(star a * a)).re
  have h_eventually : ∀ᶠ e in CStarAlgebra.approximateUnit A,
      ‖ω (e * a)‖ ^ 2 ≤ (ω (star a * a)).re :=
    (h_approx.eventually_star_eq.and h_approx.eventually_nnnorm).mono fun e he =>
      State.approx_unit_cauchy_schwarz_bound ω a e he.1 (by simpa using he.2)
  -- Derive global bound by contradiction if limit were strictly larger
  have : ‖ω a‖ ^ 2 ≤ (ω (star a * a)).re := by
    haveI : (CStarAlgebra.approximateUnit A).NeBot := h_approx.toIsApproximateUnit.neBot
    by_contra hlt; push_neg at hlt
    set δ : ℝ := (‖ω a‖ ^ 2 - (ω (star a * a)).re) / 2
    have hδ_pos : 0 < δ := half_pos (sub_pos.mpr hlt)
    have h_close := (Metric.tendsto_nhds.mp h_tendsto) δ hδ_pos
    have h_eventually_gt : ∀ᶠ e in CStarAlgebra.approximateUnit A,
        (ω (star a * a)).re < ‖ω (e * a)‖ ^ 2 := h_close.mono fun e he => by
      obtain ⟨h_low, _⟩ := abs_sub_lt_iff.mp he
      calc (ω (star a * a)).re
          < (‖ω a‖ ^ 2 + (ω (star a * a)).re) / 2 := by linarith
        _ = ‖ω a‖ ^ 2 - δ := by unfold δ; field_simp; ring
        _ < ‖ω (e * a)‖ ^ 2 := by linarith
    obtain ⟨e, he⟩ := (h_eventually.and h_eventually_gt).exists
    exact absurd he.2 (not_lt.mpr he.1)
  -- Turn squared inequality into desired norm inequality using sqrt monotonicity
  calc ‖ω a‖
      = Real.sqrt (‖ω a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((ω (star a * a)).re) := Real.sqrt_le_sqrt this
    _ = Real.sqrt (‖(Quotient.mk'' a : A ⧸ Nω)‖ ^ 2) := by rw [h_sq]
    _ = ‖(Quotient.mk'' a : A ⧸ Nω)‖ := Real.sqrt_sq (norm_nonneg _)

/-- The bounded functional `ω̃ : A ⧸ Nω →L[ℂ] ℂ` with operator norm ≤ 1. -/
private noncomputable def stateOnQuot : (A ⧸ Nω) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := stateOnQuotFun ω
      map_add' := stateOnQuotFun_add ω
      map_smul' := stateOnQuotFun_smul ω }
    1
    (fun x => by simpa using stateOnQuotFun_bound ω x)

    open Filter Topology

    local notation "lₐ" => CStarAlgebra.approximateUnit A

/-- The continuous extension of `ω̃` to the Hilbert space completion `Hω`. -/
private noncomputable def stateOnHilbert : Hω →L[ℂ] ℂ :=
  ContinuousLinearMap.extend
    (stateOnQuot ω)
    (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := A ⧸ Nω))

/-- The canonical cyclic vector `ξω ∈ Hω` obtained via the Riesz representation of the
continuous functional `stateOnHilbert`. -/
noncomputable def ξω : Hω :=
  (@InnerProductSpace.toDual ℂ Hω _ _ _ _).symm (stateOnHilbert ω)

/-- Agreement on representatives: `stateOnQuot [x] = ω x`. -/
private lemma stateOnQuot_mk (x : A) : stateOnQuot ω (Quotient.mk'' x) = ω x := rfl

/-- Extension compatibility: on representatives `x`, we have
`stateOnHilbert (↑x) = stateOnQuot x`. -/
private lemma stateOnHilbert_coe (x : A ⧸ Nω) :
    stateOnHilbert ω (↑x : Hω) = stateOnQuot ω x := by
  unfold stateOnHilbert
  erw [ContinuousLinearMap.extend_eq
    (h_dense := UniformSpace.Completion.denseRange_coe (α := A ⧸ Nω))
    (h_e := (UniformSpace.Completion.isUniformEmbedding_coe (α := A ⧸ Nω)).isUniformInducing)]

/-- Riesz identification: `⟪ξω, x⟫ = stateOnHilbert x`. -/
lemma inner_ξω_eq (x : Hω) : @inner ℂ Hω _ (ξω ω) x = stateOnHilbert ω x := by
  unfold ξω
  rw [@InnerProductSpace.toDual_symm_apply ℂ Hω _ _ _ _]

/-- Recovery of the original state on the quotient: `ω x = ⟪ξω, [x]⟫`. -/
private lemma state_recovery_quot (x : A) :
    ω x = @inner ℂ Hω _ (ξω ω) (↑(Quotient.mk'' x : A ⧸ Nω) : Hω) := by
  rw [inner_ξω_eq]
  rw [stateOnHilbert_coe]
  rfl

/-- Representation action on a quotient representative: `πω(a) [b] = [a b]`. -/
private lemma πω_apply_quotient_coe (a b : A) :
    πω ω a (↑(Quotient.mk'' b : A ⧸ Nω) : Hω) = (↑(Quotient.mk'' (a * b) : A ⧸ Nω) : Hω) := by
  rw [πω_apply_coe]
  rfl

/-- Fundamental identity: `πω(b) ξω = [b]`.  Proven by comparing inner products with an
arbitrary dense set of vectors. -/
private lemma πω_cyclic_identity (b : A) :
    πω ω b (ξω ω) = (↑(Quotient.mk'' b : A ⧸ Nω) : Hω) := by
  apply ext_inner_right ℂ
  intro x
  have h_dense := UniformSpace.Completion.denseRange_coe (α := A ⧸ Nω)
  refine h_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro yq
  obtain ⟨c, rfl⟩ := Quotient.exists_rep yq
  -- Typeclass instances are resolved using the renamed quotient instances
  calc @inner ℂ Hω _ (πω ω b (ξω ω)) (↑(Quotient.mk'' c : A ⧸ Nω))
      = @inner ℂ Hω _ (ξω ω) (ContinuousLinearMap.adjoint (πω ω b) (↑(Quotient.mk'' c : A ⧸ Nω))) := by
        rw [ContinuousLinearMap.adjoint_inner_right]
    _ = @inner ℂ Hω _ (ξω ω) (πω ω (star b) (↑(Quotient.mk'' c : A ⧸ Nω))) := by
        rw [πω_star]
    _ = @inner ℂ Hω _ (ξω ω) (↑(Quotient.mk'' (star b * c) : A ⧸ Nω)) := by rw [πω_apply_quotient_coe]
    _ = stateOnHilbert ω (↑(Quotient.mk'' (star b * c) : A ⧸ Nω)) := by rw [inner_ξω_eq]
    _ = stateOnQuot ω (Quotient.mk'' (star b * c)) := by rw [stateOnHilbert_coe]
    _ = ω (star b * c) := rfl
    _ = innerQuotient ω (Quotient.mk'' b) (Quotient.mk'' c) := by
      unfold innerQuotient; simp
    _ = @inner ℂ (A ⧸ Nω) _ (Quotient.mk'' b) (Quotient.mk'' c) := rfl
    _ = @inner ℂ Hω _ (↑(Quotient.mk'' b : A ⧸ Nω)) (↑(Quotient.mk'' c : A ⧸ Nω)) := by
      -- Lift inner product from dense subspace into completion
      simp [UniformSpace.Completion.inner_coe]

/-- The quotient image of any element lies in the closure of the cyclic orbit. -/
private lemma quotient_in_cyclic_closure (b : A) :
    (↑(Quotient.mk'' b : A ⧸ Nω) : Hω) ∈ closure (⋃ (a : A), {πω ω a (ξω ω)}) := by
  rw [← πω_cyclic_identity]
  exact subset_closure (Set.mem_iUnion.mpr ⟨b, rfl⟩)

/-- Cyclicity of `ξω`: the span of `{πω a ξω | a : A}` is dense in `Hω`. -/
lemma ξω_is_cyclic : Dense (↑(Submodule.span ℂ {πω ω a (ξω ω) | a : A}) : Set Hω) := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨y_quot, hy_dist⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y_quot
  use πω ω b (ξω ω)
  constructor
  · rwa [Metric.mem_ball, πω_cyclic_identity, dist_comm]
  · apply Submodule.subset_span
    exact ⟨b, rfl⟩

/-- GNS identity for the constructed triplet: `ω a = ⟪ξω, πω a ξω⟫`. -/
lemma state_recovery (a : A) :
    ω a = @inner ℂ Hω _ (ξω ω) (πω ω a (ξω ω)) := by
  rw [πω_cyclic_identity]
  exact state_recovery_quot ω a

/-- Normalisation of the cyclic vector: `‖ξω‖ = 1`. -/
lemma ξω_norm : ‖ξω ω‖ = 1 := by
  have h_upper : ‖stateOnHilbert ω‖ ≤ 1 := by
    -- Show operator norm ≤ 1 by bounding on dense subset and extending by continuity
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    refine DenseRange.induction_on (p := fun x => ‖stateOnHilbert ω x‖ ≤ 1 * ‖x‖)
      (UniformSpace.Completion.denseRange_coe (α := A ⧸ Nω)) x
      (isClosed_le ((stateOnHilbert ω).continuous.norm) (continuous_const.mul continuous_norm)) ?_
    intro y
    simp only [one_mul]
    calc ‖stateOnHilbert ω (↑y : Hω)‖
        = ‖stateOnQuot ω y‖ := by rw [stateOnHilbert_coe]
      _ ≤ ‖y‖ := by
          calc ‖stateOnQuot ω y‖
              = ‖stateOnQuotFun ω y‖ := rfl
            _ ≤ ‖y‖ := by simpa using stateOnQuotFun_bound ω y
      _ = ‖(↑y : Hω)‖ := by rw [UniformSpace.Completion.norm_coe]
  have h_lower : 1 ≤ ‖stateOnHilbert ω‖ := by
    -- Lower bound: evaluate functional at cyclic vector to show norm ≥ 1
    have h2 : ‖stateOnQuot ω‖ ≤ ‖stateOnHilbert ω‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (stateOnHilbert ω)) fun x ↦ by
        simpa [stateOnHilbert_coe, UniformSpace.Completion.norm_coe] using
          ContinuousLinearMap.le_opNorm (stateOnHilbert ω) (↑x : Hω)
    suffices 1 ≤ ‖stateOnQuot ω‖ from this.trans h2
    have h_norm : ‖ω‖ = 1 := ω.norm_eq_one
    rw [← h_norm]
    by_contra h_not; push_neg at h_not
    -- Expand definition of norm via supremum over ratios ‖ω a‖/‖a‖
    rw [State.norm_def] at h_not
    obtain ⟨_, ⟨a, ha, rfl⟩, h_r_large⟩ : ∃ r ∈ {s : ℝ | ∃ a : A, a ≠ 0 ∧ s = ‖ω a‖ / ‖a‖}, ‖stateOnQuot ω‖ < r := by
      by_contra h_no; push_neg at h_no
      have : sSup {s : ℝ | ∃ a : A, a ≠ 0 ∧ s = ‖ω a‖ / ‖a‖} ≤ ‖stateOnQuot ω‖ := by
        refine csSup_le ?_ h_no
        by_contra h_empty
        simp only [Set.not_nonempty_iff_eq_empty] at h_empty
        rw [h_empty, Real.sSup_empty] at h_not
        linarith [norm_nonneg (stateOnQuot ω)]
      linarith
      -- Use the quotient norm instance for subsequent norm computations
    -- Provide the NormedAddCommGroup instance explicitly for local computations
    letI : NormedAddCommGroup (A ⧸ Nω) := instNormedAddCommGroupQuot ω
    -- Bound any ratio by operator norm of stateOnQuot using quotient representative
    have h_bound : ‖ω a‖ / ‖a‖ ≤ ‖stateOnQuot ω‖ := by
      have h_pos : 0 < ‖a‖ := by simpa [norm_pos_iff] using ha
      have h_quot_norm : ‖(Quotient.mk'' a : A ⧸ Nω)‖ ≤ ‖a‖ := by
        have hsq : ‖(Quotient.mk'' a : A ⧸ Nω)‖ ^ 2 ≤ ‖a‖ ^ 2 := by
          calc ‖(Quotient.mk'' a : A ⧸ Nω)‖ ^ 2
              = (ω (star a * a)).re := norm_sq_eq_inner ω a
            _ ≤ ‖ω (star a * a)‖ := Complex.re_le_norm _
            _ ≤ ‖star a * a‖ := State.norm_le_norm ω (star a * a)
            _ ≤ ‖a‖ ^ 2 := by simpa [sq, norm_star] using norm_mul_le (star a) a
        simpa [abs_of_nonneg (norm_nonneg _)] using abs_le_of_sq_le_sq hsq (norm_nonneg _)
      calc ‖ω a‖ / ‖a‖
          = ‖stateOnQuot ω (Quotient.mk'' a)‖ / ‖a‖ := by rw [stateOnQuot_mk]
        _ ≤ (‖stateOnQuot ω‖ * ‖(Quotient.mk'' a : A ⧸ Nω)‖) / ‖a‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖stateOnQuot ω‖ := by
            calc ‖stateOnQuot ω‖ * ‖(Quotient.mk'' a : A ⧸ Nω)‖ / ‖a‖
                ≤ ‖stateOnQuot ω‖ * ‖a‖ / ‖a‖ := by gcongr
              _ = ‖stateOnQuot ω‖ := by field_simp
    exact (lt_of_le_of_lt h_bound h_r_large).false
  calc ‖ξω ω‖
      = ‖(@InnerProductSpace.toDual ℂ Hω _ _ _ _) (ξω ω)‖ := by
          rw [(@InnerProductSpace.toDual ℂ Hω _ _ _ _).norm_map (ξω ω)]
    _ = ‖stateOnHilbert ω‖ := by unfold ξω; simp [LinearIsometryEquiv.apply_symm_apply]
    _ = 1 := le_antisymm h_upper h_lower

/-- Public lemma: The GNS representation π satisfies ‖π(a)‖ ≤ ‖a‖. -/
lemma πωStarHom_opNorm_le (a : A) : ‖(πωStarHom ω) a‖ ≤ ‖a‖ :=
  πω_opNorm_le ω a

/-- The orbit vector `πω(a) ξω` has norm at most `‖a‖`. -/
lemma πω_vector_norm_le (a : A) : ‖πω ω a (ξω ω)‖ ≤ ‖a‖ := by
  have h_le := ContinuousLinearMap.le_opNorm (πω ω a) (ξω ω)
  have h_norm : ‖ξω ω‖ = 1 := ξω_norm (ω := ω)
  have h_le' : ‖πω ω a (ξω ω)‖ ≤ ‖πω ω a‖ := by simpa [h_norm] using h_le
  exact h_le'.trans (πω_opNorm_le (ω := ω) a)

/-! ### Approximate unit convergence (small-step build-up)

We now prepare lemmas showing the canonical approximate unit acts as the identity on the
GNS representation.  We proceed incrementally to keep proof obligations manageable.
-/

open Filter

/-- Approximate-unit elements act as contractions under the GNS representation. -/
lemma eventually_opNorm_le_one :
    ∀ᶠ e in CStarAlgebra.approximateUnit A, ‖πω ω e‖ ≤ (1 : ℝ) := by
  have hl : (CStarAlgebra.approximateUnit A).IsIncreasingApproximateUnit :=
    CStarAlgebra.increasingApproximateUnit (A := A)
  have hnorm := hl.eventually_norm
  refine hnorm.mono ?_
  intro e he
  exact (πωStarHom_opNorm_le (ω := ω) e).trans he

/-- Approximate units act as the identity on the vectors `πω(a) ξω`. -/
lemma tendsto_on_generator (a : A) :
    Tendsto (fun e : A => πω ω e (πω ω a (ξω ω))) (CStarAlgebra.approximateUnit A)
      (nhds (πω ω a (ξω ω))) := by
  classical
  have hl : (CStarAlgebra.approximateUnit A).IsIncreasingApproximateUnit :=
    CStarAlgebra.increasingApproximateUnit (A := A)
  have h_mul := hl.tendsto_mul_right a
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have h_event := (Metric.tendsto_nhds.mp h_mul) ε hε
  refine h_event.mono ?_
  intro e he
  have h_mul_apply : πω ω e (πω ω a (ξω ω)) = πω ω (e * a) (ξω ω) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun (T : 𝓑(Hω)) => T (ξω ω)) (πω_mul ω e a).symm
  have h_sub_op : πω ω ((e * a) - a) = πω ω (e * a) - πω ω a := πω_sub (ω := ω) (e * a) a
  have h_sub_vec : πω ω ((e * a) - a) (ξω ω)
      = πω ω (e * a) (ξω ω) - πω ω a (ξω ω) := by
    simpa [ContinuousLinearMap.sub_apply] using
      congrArg (fun T : 𝓑(Hω) => T (ξω ω)) h_sub_op
  have h_diff :
      πω ω e (πω ω a (ξω ω)) - πω ω a (ξω ω)
        = πω ω ((e * a) - a) (ξω ω) := by
    simp [h_mul_apply, h_sub_vec]
  have h_dist :
      dist (πω ω e (πω ω a (ξω ω))) (πω ω a (ξω ω))
        = ‖πω ω ((e * a) - a) (ξω ω)‖ := by
    simp [dist_eq_norm, h_diff]
  have h_bound := πω_vector_norm_le (ω := ω) ((e * a) - a)
  have h_target : ‖πω ω ((e * a) - a) (ξω ω)‖ < ε := by
    have h_lt : ‖(e * a) - a‖ < ε := by simpa [dist_eq_norm, sub_eq_add_neg]
        using he
    exact lt_of_le_of_lt h_bound h_lt
  simpa [h_dist] using h_target

/-- Approximate units act as the identity on the cyclic span generated by `ξω`. -/
lemma tendsto_on_cyclic_span {x : Hω}
    (hx : x ∈ Submodule.span ℂ {πω ω a (ξω ω) | a : A}) :
    Tendsto (fun e : A => πω ω e x) (CStarAlgebra.approximateUnit A) (nhds x) := by
  classical
  set l := CStarAlgebra.approximateUnit A
  have h_zero : Tendsto (fun _ : A => (0 : Hω)) l (nhds (0 : Hω)) := tendsto_const_nhds
  refine
    Submodule.span_induction
      (p := fun x _ => Tendsto (fun e : A => πω ω e x) l (nhds x))
      ?h_mem (by simpa [ContinuousLinearMap.map_zero] using h_zero)
      ?h_add ?h_smul hx
  · intro y hy
    rcases hy with ⟨a, rfl⟩
    simpa using tendsto_on_generator (ω := ω) a
  · intro x y hx hy hx_t hy_t
    have h_prod := hx_t.prodMk hy_t
    have h_add := (continuous_fst.add continuous_snd).tendsto (x, y)
    have h_add' :
        Tendsto (fun p : Hω × Hω => p.1 + p.2)
          (nhds x ×ˢ nhds y) (nhds (x + y)) := by
      simpa [nhds_prod_eq] using h_add
    have h_comp :
        Tendsto (fun e : A => πω ω e x + πω ω e y) l (nhds (x + y)) := by
      simpa [Function.comp] using h_add'.comp h_prod
    have h_eq :
        (fun e : A => πω ω e x + πω ω e y) =
          fun e : A => πω ω e (x + y) := by
      funext e; simp [map_add]
    simpa [h_eq] using h_comp
  · intro z x hx hx_t
    have h_map :=
        ((continuous_const : Continuous fun _ : Hω => z).smul continuous_id).tendsto x
    have h_comp :
        Tendsto (fun e : A => z • πω ω e x) l (nhds (z • x)) := by
      simpa [Function.comp] using h_map.comp hx_t
    have h_eq :
        (fun e : A => z • πω ω e x) =
          fun e : A => πω ω e (z • x) := by
      funext e; simp [map_smul]
    simpa [h_eq] using h_comp

/- Approximate units act as the identity on all of `Hω`. -/
lemma tendsto_on_vector (x : Hω) :
    Tendsto (fun e : A => πω ω e x) (CStarAlgebra.approximateUnit A) (nhds x) := by
  classical
  set l := CStarAlgebra.approximateUnit A
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε4 : 0 < ε / 4 := by
    have : (0 : ℝ) < 4 := by norm_num
    exact div_pos hε this
  have h_dense := ξω_is_cyclic (ω := ω)
  obtain ⟨y, hy_mem, hy_dist⟩ := h_dense.exists_dist_lt x hε4
  have hy_span : y ∈ Submodule.span ℂ {πω ω a (ξω ω) | a : A} := hy_mem
  have hy_norm : ‖x - y‖ < ε / 4 := by
    have hy_dist' : dist x y < ε / 4 := by simpa [dist_comm] using hy_dist
    simpa [dist_eq_norm] using hy_dist'
  have hy_tendsto := tendsto_on_cyclic_span (ω := ω) (x := y) hy_span
  have hy_event := (Metric.tendsto_nhds.mp hy_tendsto) (ε / 2) hε2
  have h_contr := eventually_opNorm_le_one (ω := ω)
  have h_contr_vec :
      ∀ᶠ e in l, ‖πω ω e (x - y)‖ ≤ ‖x - y‖ := by
    refine h_contr.mono ?_
    intro e he
    have h_le := ContinuousLinearMap.le_opNorm (πω ω e) (x - y)
    have h_mul := mul_le_mul_of_nonneg_right he (norm_nonneg (x - y))
    simpa [one_mul] using h_le.trans h_mul
  have h_event := (h_contr_vec.and hy_event)
  have h_goal : ∀ᶠ e in l, dist (πω ω e x) x < ε := by
    refine h_event.mono ?_
    intro e he
    have h_bound : ‖πω ω e (x - y)‖ ≤ ‖x - y‖ := he.1
    have h_y : ‖πω ω e y - y‖ < ε / 2 := by
      have := he.2
      simpa [dist_eq_norm] using this
    have h_first :
        ‖πω ω e (x - y) - (x - y)‖ ≤ 2 * ‖x - y‖ := by
      calc
        ‖πω ω e (x - y) - (x - y)‖
            ≤ ‖πω ω e (x - y)‖ + ‖x - y‖ := norm_sub_le _ _
        _ ≤ ‖x - y‖ + ‖x - y‖ := by
            exact add_le_add h_bound le_rfl
        _ = 2 * ‖x - y‖ := by ring
    have h_two : 2 * ‖x - y‖ < ε / 2 := by
      have h_mul := mul_lt_mul_of_pos_left hy_norm (by norm_num : 0 < (2 : ℝ))
      have h_half : 2 * (ε / 4) = ε / 2 := by ring
      simpa [h_half] using h_mul
    have h_first_lt : ‖πω ω e (x - y) - (x - y)‖ < ε / 2 := lt_of_le_of_lt h_first h_two
    have h_decomp :
        πω ω e x - x
          = (πω ω e (x - y) - (x - y)) + (πω ω e y - y) := by
      have h_sum : (x - y) + y = x := sub_add_cancel x y
      calc
        πω ω e x - x
            = πω ω e ((x - y) + y) - ((x - y) + y) := by
                exact congrArg (fun t => πω ω e t - t) h_sum.symm
        _ = (πω ω e (x - y) + πω ω e y) - ((x - y) + y) := by
            exact congrArg (fun t => t - ((x - y) + y)) (map_add (πω ω e) (x - y) y)
        _ = (πω ω e (x - y) - (x - y)) + (πω ω e y - y) := by
          grind [sub_eq_add_neg]
    have h_norm_le :
        ‖πω ω e x - x‖
          ≤ ‖πω ω e (x - y) - (x - y)‖ + ‖πω ω e y - y‖ := by
      simpa [h_decomp] using
        norm_add_le (πω ω e (x - y) - (x - y)) (πω ω e y - y)
    have h_sum_lt :
        ‖πω ω e (x - y) - (x - y)‖ + ‖πω ω e y - y‖ < ε := by
      have := add_lt_add_of_lt_of_lt h_first_lt h_y
      have h_halves : ε / 2 + ε / 2 = ε := by ring
      simpa [h_halves] using this
    have h_total : ‖πω ω e x - x‖ < ε := lt_of_le_of_lt h_norm_le h_sum_lt
    simpa [dist_eq_norm] using h_total
  exact h_goal

/-- Evaluation of the state along the approximate unit converges to `1`. -/
lemma approxUnit_eval_tendsto_one :
    Tendsto (fun e : A => ω e) (CStarAlgebra.approximateUnit A) (nhds (1 : ℂ)) := by
  classical
  have h_vec := tendsto_on_vector (ω := ω) (x := ξω ω)
  have h_inner : Continuous fun v : Hω => @inner ℂ Hω _ (ξω ω) v :=
    Continuous.inner continuous_const continuous_id
  have h_comp :
      Tendsto (fun e : A => @inner ℂ Hω _ (ξω ω) (πω ω e (ξω ω)))
        (CStarAlgebra.approximateUnit A)
        (nhds (@inner ℂ Hω _ (ξω ω) (ξω ω))) :=
    (h_inner.tendsto (ξω ω)).comp h_vec
  have h_eq :
      (fun e : A => @inner ℂ Hω _ (ξω ω) (πω ω e (ξω ω))) =
        fun e : A => ω e := by
    funext e
    simpa using (state_recovery (ω := ω) e).symm
  have h_norm := ξω_norm (ω := ω)
  rw [h_eq] at h_comp
  convert h_comp using 2
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), h_norm]
  norm_num

end Construction

end GNS
