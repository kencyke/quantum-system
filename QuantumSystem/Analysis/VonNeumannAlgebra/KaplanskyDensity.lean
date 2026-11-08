/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import QuantumSystem.Analysis.VonNeumannAlgebra.DoubleCommutant.SOTClosedSubalgebra
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring
public import QuantumSystem.ForMathlib.Analysis.LocallyConvex.ConvexOperatorClosure

/-!
# The Kaplansky density theorem

For a `⋆`-subalgebra `A` of `B(H)`, the unit ball of `A` is strongly dense in the unit ball of the
strong closure of `A` (Kaplansky, *A theorem on rings of operators*, Pacific J. Math. 1 (1951),
Theorem 1), and likewise for the self-adjoint and the positive parts of the unit balls. By the
bicommutant theorem the strong closure of a non-degenerate `A` is its double commutant `A′′`, so
the unit ball of `A` is strongly dense in that of the von Neumann algebra `A′′`.

No closedness or non-degeneracy is assumed of `A` except in the double commutant form. The strong
closure is stated in Mathlib's type copy `H →Lₚₜ[ℂ] H` carrying the strong operator topology, as
`closure (Set.toSOT S)`.

## Main results

* **`NonUnitalStarSubalgebra.closure_toSOT_closedBall`**: Kaplansky density for the unit ball.
* **`NonUnitalStarSubalgebra.closure_toSOT_selfAdjoint_closedBall`**: for its self-adjoint part.
* **`NonUnitalStarSubalgebra.closure_toSOT_nonneg_closedBall`**: for its positive part.
* **`NonUnitalStarSubalgebra.closure_toSOT_closedBall_eq_doubleCommutant`**: the von Neumann
  algebra form, for a non-degenerate `A`.
* **`NonUnitalStarSubalgebra.closure_toWOT_closedBall`**: the weak form, for the weak closure.

The strong and the weak closure of a convex set of operators agree
(`Convex.toPointwiseConvergenceCLM_mem_closure_image_iff`), so the strong closure of `A` is also
its weak closure. Not formalized: the density of the unitary group of `A` in that of its strong
closure, for a unital norm-closed `A`; and the strong* form, the approximation of `T` and `T⋆` along
one net, which the `2 × 2` matrix device of `closure_toSOT_closedBall` produces but which has no type
copy carrying the strong* topology to be stated in.

## Proof

1. The adjoint is weakly continuous, but not strongly continuous on an infinite-dimensional `H`;
   since the strong and the weak closure of a convex set agree, a self-adjoint element of the
   strong closure is a strong limit of self-adjoint elements of `A`.
2. The function `f(t) = 2t / (1 + t²)` is strongly continuous on self-adjoint operators, by the
   resolvent identity `f(a) - f(b) = 2 R(a) (a - b) R(b) - 2 a R(a) (a - b) b R(b)` with
   `R(t) = (1 + t²)⁻¹`; no bound on the approximating net is needed. It maps `ℝ` into `[-1, 1]`
   and `[-1, 1]` onto itself. A self-adjoint contraction `T` of the strong closure is `f(S)` for the
   self-adjoint `S = f⁻¹(T)` of the strong closure; approximating `S` by self-adjoint `aᵢ ∈ A`,
   the self-adjoint contractions `f(aᵢ)` converge strongly to `T`. This needs `A` norm-closed, for
   `f(aᵢ) ∈ A`; the norm closure of `A` has the same strong closure, and its self-adjoint
   contractions are norm limits of those of `A`.
3. A contraction `T` is the corner of the self-adjoint contraction `[[0, T], [T⋆, 0]]` on `H ⊕ H`,
   which lies in the strong closure of the `2 × 2` matrices over `A`; the corners of the
   approximants from step 2 approximate `T`.
4. A positive contraction `T` is `S²` for the self-adjoint contraction `S = √T`; the squares of
   self-adjoint contractions approximating `S` are positive contractions approximating `T`, as
   multiplication is jointly strongly continuous on bounded sets.
-/

@[expose] public section

open StrongOperatorTopology WeakOperatorTopology
open ContinuousLinearMap (toUniformConvergenceCLM)
open scoped Topology

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "B" => (H →L[ℂ] H)
local notation "BSOT" => (H →Lₚₜ[ℂ] H)
local notation "BWOT" => (H →WOT[ℂ] H)
/-- `K` is the Hilbert sum `H ⊕ H`, as `ℓ²(Fin 2; H)`. Local to this file. -/
local notation "K" => InnerProductSpace.Hn H 2
/-- `Φ` identifies the `2 × 2` operator matrices over `B(H)` with the operators on `K`. Local to this
file. -/
local notation "Φ" => CStarMatrix.toPiLpStarAlgEquiv (Fin 2) H

/-- `S′` denotes the commutant `Set.centralizer S` of a set of operators, so that `S′′` is the double
commutant. Local to this file. -/
local postfix:max "′" => Set.centralizer

namespace StrongOperatorTopology

/-- For a convex set `C` of operators, `T` is in the strong closure of `C` iff it is in its weak
closure; the case `E = F = H` of `Convex.toPointwiseConvergenceCLM_mem_closure_image_iff`, in the
spelling `Set.toSOT`, `Set.toWOT` of the strong and weak copies. -/
private lemma mem_closure_toSOT_iff_of_convex {C : Set B} (hC : Convex ℝ C) (T : B) :
    ↑ₚₜ T ∈ closure (Set.toSOT C) ↔ sotToWOT (↑ₚₜ T) ∈ closure (Set.toWOT C) := by
  have e1 : Set.toSOT C = ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H '' C :=
    ((toUniformConvergenceCLM _ _ _).image_eq_preimage_symm C).symm
  have e2 : Set.toWOT C = ContinuousLinearMapWOT.ofCLM '' C := by
    ext Y
    exact ⟨fun h => ⟨_, h, rfl⟩, by rintro ⟨S, hS, rfl⟩; exact hS⟩
  rw [e1, e2]
  exact hC.toPointwiseConvergenceCLM_mem_closure_image_iff T

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- An operator lies in the SOT copy `Set.toSOT S` of a set `S` exactly when it lies in `S`. -/
private lemma toSOT_mem_toSOT_iff {S : Set B} {T : B} : ↑ₚₜ T ∈ Set.toSOT S ↔ T ∈ S := Iff.rfl

/-! ### The function `t ↦ 2t / (1 + t²)` is strongly continuous on self-adjoint operators -/

namespace Kaplansky

/-- The resolvent-type function `t ↦ (1 + t²)⁻¹`. -/
private noncomputable def resolv (t : ℝ) : ℝ := (1 + t ^ 2)⁻¹

/-- The function `t ↦ 2t / (1 + t²)`, which is `sin (2 arctan t)`; it maps `ℝ` into `[-1, 1]` and
`[-1, 1]` onto itself. -/
private noncomputable def sinTwoArctan (t : ℝ) : ℝ := 2 * (t * resolv t)

/-- The inverse of `sinTwoArctan` on `[-1, 1]`: `t ↦ t / (1 + √(1 - t²))`, which is
`tan (arcsin t / 2)` there. -/
private noncomputable def tanHalfArcsin (t : ℝ) : ℝ := t / (1 + √(1 - t ^ 2))

private lemma one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

@[fun_prop] private lemma continuous_resolv : Continuous resolv :=
  (continuous_const.add (continuous_pow 2)).inv₀ fun t => (one_add_sq_pos t).ne'

@[fun_prop] private lemma continuous_sinTwoArctan : Continuous sinTwoArctan := by
  unfold sinTwoArctan; fun_prop

@[fun_prop] private lemma continuous_tanHalfArcsin : Continuous tanHalfArcsin :=
  continuous_id.div (continuous_const.add (by fun_prop)) fun t => by positivity

private lemma sinTwoArctan_zero : sinTwoArctan 0 = 0 := by simp [sinTwoArctan]

private lemma tanHalfArcsin_zero : tanHalfArcsin 0 = 0 := by simp [tanHalfArcsin]

private lemma abs_resolv_le (t : ℝ) : |resolv t| ≤ 1 := by
  rw [resolv, abs_of_pos (inv_pos.mpr (one_add_sq_pos t))]
  exact inv_le_one_of_one_le₀ (by nlinarith)

private lemma abs_mul_resolv_le (t : ℝ) : |t * resolv t| ≤ 1 := by
  rw [resolv, ← div_eq_mul_inv, abs_div, abs_of_pos (one_add_sq_pos t),
    div_le_one (one_add_sq_pos t)]
  nlinarith [abs_nonneg t, sq_abs t]

private lemma abs_sinTwoArctan_le (t : ℝ) : |sinTwoArctan t| ≤ 1 := by
  rw [sinTwoArctan, resolv, ← div_eq_mul_inv, ← mul_div_assoc, abs_div, abs_of_pos (one_add_sq_pos t),
    div_le_one (one_add_sq_pos t), abs_mul, abs_two]
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

private lemma sinTwoArctan_tanHalfArcsin {t : ℝ} (ht : |t| ≤ 1) : sinTwoArctan (tanHalfArcsin t) = t := by
  have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  set r := √(1 - t ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 - t ^ 2 := Real.sq_sqrt h1
  have hpos : 0 < 1 + r := by linarith
  simp only [sinTwoArctan, resolv, tanHalfArcsin, ← hr]
  field_simp
  linear_combination (-t) * hr2

variable {a b : H →L[ℂ] H}

private lemma cfc_one_add_sq (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc (fun t : ℝ => 1 + t ^ 2) a = 1 + a * a := by
  rw [cfc_add .., cfc_const_one .., cfc_pow .., cfc_id' ℝ a ha, sq]

private lemma cfc_resolv_mul (ha : IsSelfAdjoint a := by cfc_tac) : cfc resolv a * (1 + a * a) = 1 := by
  rw [← cfc_one_add_sq ha, ← cfc_mul ..]
  refine (cfc_congr fun t _ => ?_).trans (cfc_const_one ℝ a)
  exact inv_mul_cancel₀ (one_add_sq_pos t).ne'

private lemma mul_cfc_resolv (ha : IsSelfAdjoint a := by cfc_tac) : (1 + a * a) * cfc resolv a = 1 := by
  rw [← cfc_one_add_sq ha, ← cfc_mul ..]
  refine (cfc_congr fun t _ => ?_).trans (cfc_const_one ℝ a)
  exact mul_inv_cancel₀ (one_add_sq_pos t).ne'

private lemma commute_cfc_resolv (ha : IsSelfAdjoint a := by cfc_tac) :
    a * cfc resolv a = cfc resolv a * a :=
  calc a * cfc resolv a = cfc (fun t => t * resolv t) a := by
        rw [cfc_mul (fun t : ℝ => t) resolv a, cfc_id' ℝ a ha]
    _ = cfc (fun t => resolv t * t) a := cfc_congr fun t _ => mul_comm _ _
    _ = cfc resolv a * a := by rw [cfc_mul resolv (fun t : ℝ => t) a, cfc_id' ℝ a ha]

private lemma cfc_sinTwoArctan (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc sinTwoArctan a = (2 : ℝ) • (a * cfc resolv a) := by
  have : sinTwoArctan = fun t => 2 * ((fun t : ℝ => t) t * resolv t) := rfl
  rw [this, cfc_const_mul .., cfc_mul .., cfc_id' ℝ a ha]

private lemma norm_cfc_resolv_le : ‖cfc resolv a‖ ≤ 1 :=
  norm_cfc_le (a := a) zero_le_one fun t _ => by rw [Real.norm_eq_abs]; exact abs_resolv_le t

private lemma norm_mul_cfc_resolv_le (ha : IsSelfAdjoint a := by cfc_tac) : ‖a * cfc resolv a‖ ≤ 1 := by
  rw [show a * cfc resolv a = cfc (fun t => t * resolv t) a by
    rw [cfc_mul (fun t : ℝ => t) resolv a, cfc_id' ℝ a ha]]
  exact norm_cfc_le (a := a) zero_le_one fun t _ => by rw [Real.norm_eq_abs]; exact abs_mul_resolv_le t

private lemma norm_cfc_sinTwoArctan_le : ‖cfc sinTwoArctan a‖ ≤ 1 :=
  norm_cfc_le (a := a) zero_le_one fun t _ => by rw [Real.norm_eq_abs]; exact abs_sinTwoArctan_le t

/-- The resolvent identity behind the strong continuity of `sinTwoArctan`:
`a R(a) - b R(b) = R(a) (a - b) R(b) - a R(a) (a - b) b R(b)` for `R(t) = (1 + t²)⁻¹`. -/
private lemma mul_cfc_resolv_sub (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    a * cfc resolv a - b * cfc resolv b =
      cfc resolv a * (a - b) * cfc resolv b -
        a * cfc resolv a * (a - b) * (b * cfc resolv b) := by
  set Ra := cfc resolv a
  set Rb := cfc resolv b
  have e1 : a * Ra = Ra * (a + a * b * b) * Rb := by
    calc a * Ra = a * Ra * ((1 + b * b) * Rb) := by rw [mul_cfc_resolv hb, mul_one]
      _ = Ra * a * ((1 + b * b) * Rb) := by rw [commute_cfc_resolv ha]
      _ = Ra * (a + a * b * b) * Rb := by noncomm_ring
  have e2 : b * Rb = Ra * (b + a * a * b) * Rb := by
    calc b * Rb = (Ra * (1 + a * a)) * (b * Rb) := by rw [cfc_resolv_mul ha, one_mul]
      _ = Ra * (b + a * a * b) * Rb := by noncomm_ring
  conv_lhs => rw [e1, e2]
  conv_rhs => rw [commute_cfc_resolv ha]
  noncomm_ring

/-- `sinTwoArctan` is strongly continuous on self-adjoint operators: if self-adjoint `aᵢ → b` strongly,
then `sinTwoArctan aᵢ → sinTwoArctan b` strongly. No bound on `‖aᵢ‖` is needed. -/
private lemma tendsto_cfc_sinTwoArctan {ι : Type*} {l : Filter ι} {c : ι → B} {b : B}
    (hc : ∀ᶠ i in l, IsSelfAdjoint (c i)) (hb : IsSelfAdjoint b)
    (h : ∀ x, Filter.Tendsto (fun i => c i x) l (𝓝 (b x))) (x : H) :
    Filter.Tendsto (fun i => cfc sinTwoArctan (c i) x) l (𝓝 (cfc sinTwoArctan b x)) := by
  set y := cfc resolv b x
  set z := (b * cfc resolv b) x
  have hy := tendsto_iff_norm_sub_tendsto_zero.mp (h y)
  have hz := tendsto_iff_norm_sub_tendsto_zero.mp (h z)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hc.mono fun i hi => ?_) ((((hy.add hz)).const_mul 2).trans (by simp))
  set Ra := cfc resolv (c i)
  have key : cfc sinTwoArctan (c i) - cfc sinTwoArctan b =
      (2 : ℝ) • (Ra * (c i - b) * cfc resolv b - c i * Ra * (c i - b) * (b * cfc resolv b)) := by
    rw [cfc_sinTwoArctan hi, cfc_sinTwoArctan hb, ← smul_sub, mul_cfc_resolv_sub hi hb]
  have hx : cfc sinTwoArctan (c i) x - cfc sinTwoArctan b x =
      (2 : ℝ) • (Ra ((c i - b) y) - (c i * Ra) ((c i - b) z)) := by
    have := congrArg (fun T : B => T x) key
    simpa [y, z] using this
  rw [hx, norm_smul, Real.norm_two]
  gcongr
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (Ra.le_opNorm _).trans ?_
    simpa using mul_le_of_le_one_left (norm_nonneg _) norm_cfc_resolv_le
  · refine ((c i * Ra).le_opNorm _).trans ?_
    simpa using mul_le_of_le_one_left (norm_nonneg _) (norm_mul_cfc_resolv_le hi)

/-- A closed `⋆`-subalgebra is closed under `cfc` of a real function vanishing at `0`. -/
private lemma cfc_mem_of_isClosed {A : NonUnitalStarSubalgebra ℂ B} (hA : IsClosed (A : Set B))
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) {a : B} (ha : a ∈ A) :
    cfc f a ∈ A := by
  -- `cfcₙ_mem` finds the closedness of `A` by instance search
  have := hA
  rw [← cfcₙ_eq_cfc hf.continuousOn hf0]
  exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) f ha

private lemma abs_le_norm_of_mem_spectrum {T : B} {t : ℝ} (ht : t ∈ spectrum ℝ T) :
    |t| ≤ ‖T‖ := by
  rcases subsingleton_or_nontrivial H with _ | _
  · exact absurd ht (by simp [spectrum.of_subsingleton])
  rw [← Real.norm_eq_abs]
  exact spectrum.norm_le_norm_of_mem ht

private lemma sinTwoArctan_cfc_tanHalfArcsin {T : B} (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) :
    cfc sinTwoArctan (cfc tanHalfArcsin T) = T := by
  rw [← cfc_comp' sinTwoArctan tanHalfArcsin T]
  refine (cfc_congr fun t ht => ?_).trans (cfc_id' ℝ T hT)
  exact sinTwoArctan_tanHalfArcsin ((abs_le_norm_of_mem_spectrum ht).trans hn)

end Kaplansky

/-! ### Strongly closed sets of operators -/

omit [CompleteSpace H] in
private lemma isClosed_toSOT_norm_le_one : IsClosed (Set.toSOT {T : B | ‖T‖ ≤ 1}) := by
  have : Set.toSOT {T : B | ‖T‖ ≤ 1} = ⋂ x : H, {Y : BSOT | ‖Y x‖ ≤ ‖x‖} := by
    ext Y
    simp only [Set.mem_toSOT_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      ContinuousLinearMap.opNorm_le_iff zero_le_one, one_mul]
    rfl
  rw [this]
  exact isClosed_iInter fun x => isClosed_le (continuous_eval_const x).norm continuous_const

private lemma isClosed_toSOT_isSelfAdjoint : IsClosed (Set.toSOT {T : B | IsSelfAdjoint T}) := by
  have : Set.toSOT {T : B | IsSelfAdjoint T} =
      ⋂ x : H, ⋂ y : H, {Y : BSOT | inner ℂ (Y x) y = inner ℂ x (Y y)} := by
    ext Y
    simp only [Set.mem_toSOT_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    rfl
  rw [this]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
    ((continuous_eval_const x).inner continuous_const)
    (continuous_const.inner (continuous_eval_const y))

omit [CompleteSpace H] in
private lemma isClosed_toSOT_nonneg : IsClosed (Set.toSOT {T : B | 0 ≤ T}) := by
  have : Set.toSOT {T : B | 0 ≤ T} = ⋂ x : H, {Y : BSOT |
      ((RCLike.re (inner ℂ (Y x) x) : ℝ) : ℂ) = inner ℂ (Y x) x ∧
        0 ≤ RCLike.re (inner ℂ (Y x) x)} := by
    ext Y
    simp only [Set.mem_toSOT_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    rfl
  rw [this]
  have hc : ∀ x : H, Continuous fun Y : BSOT => inner ℂ (Y x) x := fun x =>
    (continuous_eval_const x).inner continuous_const
  exact isClosed_iInter fun x => (isClosed_eq (Complex.continuous_ofReal.comp
    (RCLike.continuous_re.comp (hc x))) (hc x)).inter
    (isClosed_le continuous_const (RCLike.continuous_re.comp (hc x)))

/-- A self-adjoint contraction in the norm closure of `A` is a norm limit of self-adjoint
contractions of `A`. -/
private lemma Kaplansky.mem_closure_selfAdjoint_closedBall {A : NonUnitalStarSubalgebra ℂ B}
    {x : B} (hx : x ∈ closure (A : Set B)) (hsa : IsSelfAdjoint x)
    (hn : ‖x‖ ≤ 1) : x ∈ closure {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1} := by
  let re : B → B := fun y => (2⁻¹ : ℂ) • (y + star y)
  let φ : B → B := fun y => (((max 1 ‖re y‖)⁻¹ : ℝ) : ℂ) • re y
  have hmax : ∀ r : ℝ, 0 < max 1 r := fun r => zero_lt_one.trans_le (le_max_left _ _)
  have hφ : Continuous φ := by
    refine (Complex.continuous_ofReal.comp ((continuous_const.max ?_).inv₀
      fun y => (hmax _).ne')).smul ?_ <;> fun_prop
  have hre : re x = x := by
    change (2⁻¹ : ℂ) • (x + star x) = x
    rw [hsa.star_eq, ← two_smul ℂ x, smul_smul]
    norm_num
  have hφx : φ x = x := by
    change (((max 1 ‖re x‖)⁻¹ : ℝ) : ℂ) • re x = x
    rw [hre, max_eq_left hn]
    simp
  have h := map_mem_closure (t := {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1}) hφ hx fun y hy => by
    have hrey : re y ∈ A := SMulMemClass.smul_mem _ (A.add_mem hy (star_mem (s := A) hy))
    refine ⟨SMulMemClass.smul_mem _ hrey, ?_, ?_⟩
    · exact (show IsSelfAdjoint (((max 1 ‖re y‖)⁻¹ : ℝ) : ℂ) from Complex.conj_ofReal _).smul
        ((IsSelfAdjoint.ofNat (R := ℂ) 2).inv₀.smul
        (IsSelfAdjoint.add_star_self _))
    · change ‖(((max 1 ‖re y‖)⁻¹ : ℝ) : ℂ) • re y‖ ≤ 1
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hmax _)),
        inv_mul_le_iff₀ (hmax _), mul_one]
      exact le_max_right _ _
  rwa [hφx] at h

omit [CompleteSpace H] in
/-- Products of strongly convergent nets converge strongly when the left factors have norm at
most `1`. -/
private lemma Kaplansky.tendsto_mul_apply {ι : Type*} {l : Filter ι} {c d : ι → B}
    {b e : B} (hc : ∀ᶠ i in l, ‖c i‖ ≤ 1) (hcb : ∀ x, Filter.Tendsto (fun i => c i x) l (𝓝 (b x)))
    (hde : ∀ x, Filter.Tendsto (fun i => d i x) l (𝓝 (e x))) (x : H) :
    Filter.Tendsto (fun i => (c i * d i) x) l (𝓝 ((b * e) x)) := by
  have h1 := tendsto_iff_norm_sub_tendsto_zero.mp (hde x)
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (hcb (e x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (hc.mono fun i hi => ?_) ((h1.add h2).trans (by simp))
  have : (c i * d i) x - (b * e) x = c i (d i x - e x) + (c i (e x) - b (e x)) := by
    simp [map_sub]
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
  exact ((c i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hi)

/-! ### The `2 × 2` matrix trick -/

namespace Kaplansky

/-- The `2 × 2` operator matrices `(aᵢⱼ)` on `H ⊕ H` with entries in `A`. -/
private noncomputable def matrixTwo (A : NonUnitalStarSubalgebra ℂ B) :
    NonUnitalStarSubalgebra ℂ (K →L[ℂ] K) where
  carrier := {X | ∀ i j, (Φ).symm X i j ∈ A}
  zero_mem' i j := by simp
  add_mem' {X Y} hX hY i j := by
    have h : (Φ).symm (X + Y) =
        (Φ).symm X + (Φ).symm Y :=
      (Φ).symm.map_add' X Y
    rw [h, CStarMatrix.add_apply]
    exact A.add_mem (hX i j) (hY i j)
  smul_mem' c X hX i j := by
    have h : (Φ).symm (c • X) =
        c • (Φ).symm X :=
      (Φ).symm.map_smul' c X
    rw [h, CStarMatrix.smul_apply]
    exact SMulMemClass.smul_mem c (hX i j)
  mul_mem' {X Y} hX hY i j := by
    have h : (Φ).symm (X * Y) =
        (Φ).symm X * (Φ).symm Y :=
      (Φ).symm.map_mul' X Y
    rw [h, CStarMatrix.mul_apply]
    exact sum_mem fun k _ => A.mul_mem (hX i k) (hY k j)
  star_mem' {X} hX i j := by
    have h : (Φ).symm (star X) =
        star ((Φ).symm X) :=
      (Φ).symm.map_star' X
    rw [h, CStarMatrix.star_apply]
    exact star_mem (s := A) (hX j i)

/-- The `(0, 1)` entry of an operator on `H ⊕ H`, `x ↦ (X (0, x))₀`. -/
private noncomputable def corner (X : K →L[ℂ] K) :
    B :=
  (Φ).symm X 0 1

private lemma corner_apply (X : K →L[ℂ] K) (x : H) :
    corner X x = (X (PiLp.single 2 1 x)).ofLp 0 :=
  rfl

private lemma norm_corner_le (X : K →L[ℂ] K) :
    ‖corner X‖ ≤ ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [corner_apply]
  refine (PiLp.norm_apply_le _ _).trans ((X.le_opNorm _).trans_eq ?_)
  rw [PiLp.norm_single]

private lemma continuous_corner :
    Continuous fun Y : K →Lₚₜ[ℂ] K =>
      ↑ₚₜ (corner ((toUniformConvergenceCLM _ _ _).symm Y)) := by
  refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun x => ?_
  exact ((PiLp.continuous_apply 2 _ 0).comp (continuous_eval_const _))

private lemma corner_toPiLpStarAlgEquiv (N : CStarMatrix (Fin 2) (Fin 2) B) :
    corner (Φ N) = N 0 1 := by
  change (Φ).symm ((Φ) N) 0 1 = N 0 1
  rw [StarAlgEquiv.symm_apply_apply]

end Kaplansky

end StrongOperatorTopology

namespace NonUnitalStarSubalgebra

open StrongOperatorTopology.Kaplansky

variable [CompleteSpace H]

/-- The strong closure of a `⋆`-subalgebra is a `⋆`-subalgebra. Star-closedness is the point:
the adjoint is not strongly continuous on an infinite-dimensional `H`, but the strong closure agrees
with the weak one, in which it is, because `A` is convex. -/
private noncomputable def sotClosureSubalgebra (A : NonUnitalStarSubalgebra ℂ B) :
    NonUnitalStarSubalgebra ℂ B where
  carrier := (ContinuousLinearMap.toSOT : B →L[ℂ] BSOT) ⁻¹' closure (Set.toSOT (A : Set B))
  zero_mem' := subset_closure (s := Set.toSOT (A : Set B)) (toSOT_mem_toSOT_iff.mpr A.zero_mem)
  add_mem' {T S} hT hS := by
    let M : Submodule ℂ BSOT := A.toSubmodule.comap (toUniformConvergenceCLM _ _ _).symm.toLinearMap
    exact (M.topologicalClosure.add_mem (x := ↑ₚₜ T) hT hS : _)
  smul_mem' c T hT := by
    let M : Submodule ℂ BSOT := A.toSubmodule.comap (toUniformConvergenceCLM _ _ _).symm.toLinearMap
    exact (M.topologicalClosure.smul_mem c (x := ↑ₚₜ T) hT : _)
  mul_mem' {T S} hT hS := by
    have hleft : ∀ a ∈ A, ∀ S : B, ↑ₚₜ S ∈ closure (Set.toSOT (A : Set B)) →
        ↑ₚₜ (a * S) ∈ closure (Set.toSOT (A : Set B)) := fun a ha S hS =>
      map_mem_closure (f := PointwiseConvergenceCLM.postcomp H a)
        (PointwiseConvergenceCLM.postcomp H a).continuous hS
        fun R hR => toSOT_mem_toSOT_iff.mpr (A.mul_mem ha (toSOT_mem_toSOT_iff.mp hR))
    have h := map_mem_closure (f := PointwiseConvergenceCLM.precomp H S)
      (t := closure (Set.toSOT (A : Set B)))
      (PointwiseConvergenceCLM.precomp H S).continuous hT
      fun R hR => hleft _ (toSOT_mem_toSOT_iff.mp hR) S hS
    rwa [closure_closure] at h
  star_mem' {T} hT := by
    have hconv : Convex ℝ (A : Set B) := (A.toSubmodule.restrictScalars ℝ).convex
    change ↑ₚₜ T ∈ closure (Set.toSOT (A : Set B)) at hT
    change ↑ₚₜ (star T) ∈ closure (Set.toSOT (A : Set B))
    rw [mem_closure_toSOT_iff_of_convex hconv] at hT ⊢
    exact map_mem_closure (f := star) continuous_star hT fun R hR => star_mem (s := A) (Set.mem_toWOT_iff.mp hR)

/-- `T` lies in the strong closure of `A` exactly when its SOT copy lies in the closure of the SOT
copy of `A`. -/
private lemma mem_sotClosureSubalgebra_iff {A : NonUnitalStarSubalgebra ℂ B} {T : B} :
    T ∈ A.sotClosureSubalgebra ↔ ↑ₚₜ T ∈ closure (Set.toSOT (A : Set B)) :=
  Iff.rfl

/-- The strong closure of `A` is norm-closed. -/
private lemma isClosed_sotClosureSubalgebra (A : NonUnitalStarSubalgebra ℂ B) :
    IsClosed (A.sotClosureSubalgebra : Set B) :=
  isClosed_closure.preimage (ContinuousLinearMap.toSOT (σ := RingHom.id ℂ) (E := H) (F := H)).continuous

/-- A self-adjoint element of the strong closure of `A` is a strong limit of self-adjoint
elements of `A`. -/
private lemma mem_closure_toSOT_selfAdjoint {A : NonUnitalStarSubalgebra ℂ B}
    {T : B} (hT : T ∈ A.sotClosureSubalgebra) (hsa : IsSelfAdjoint T) :
    ↑ₚₜ T ∈ closure (Set.toSOT {a | a ∈ A ∧ IsSelfAdjoint a}) := by
  have hconvA : Convex ℝ (A : Set B) := (A.toSubmodule.restrictScalars ℝ).convex
  have hconv : Convex ℝ {a | a ∈ A ∧ IsSelfAdjoint a} := by
    intro a ha b hb s t _ _ _
    refine ⟨hconvA ha.1 hb.1 ‹_› ‹_› ‹_›, ?_⟩
    exact ((IsSelfAdjoint.all s).smul ha.2).add ((IsSelfAdjoint.all t).smul hb.2)
  have hT' := A.mem_sotClosureSubalgebra_iff.mp hT
  rw [mem_closure_toSOT_iff_of_convex hconvA] at hT'
  rw [mem_closure_toSOT_iff_of_convex hconv]
  let re : BWOT → BWOT := fun X => (2⁻¹ : ℂ) • (X + star X)
  have hre : Continuous re := by fun_prop
  have h := map_mem_closure (f := re) (t := Set.toWOT {a | a ∈ A ∧ IsSelfAdjoint a}) hre hT'
    fun X hX => by
      have hX := Set.mem_toWOT_iff.mp hX
      refine Set.mem_toWOT_iff.mpr ⟨SMulMemClass.smul_mem _ (A.add_mem hX (star_mem (s := A) hX)), ?_⟩
      exact (IsSelfAdjoint.ofNat (R := ℂ) 2).inv₀.smul (IsSelfAdjoint.add_star_self _)
  have hfix : re (sotToWOT (↑ₚₜ T)) = sotToWOT (↑ₚₜ T) := by
    refine ContinuousLinearMapWOT.ext fun x => ?_
    change (2⁻¹ : ℂ) • (T x + (star T) x) = T x
    rw [hsa.star_eq, ← two_smul ℂ (T x), smul_smul]
    norm_num
  rwa [hfix] at h

/-- **Kaplansky density, self-adjoint part, for a norm-closed algebra.** -/
private lemma mem_closure_selfAdjoint_closedBall_of_isClosed {A : NonUnitalStarSubalgebra ℂ B}
    (hA : IsClosed (A : Set B)) {T : B} (hT : T ∈ A.sotClosureSubalgebra)
    (hsa : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) :
    ↑ₚₜ T ∈ closure (Set.toSOT {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1}) := by
  set S := cfc tanHalfArcsin T
  have hSmem : S ∈ A.sotClosureSubalgebra :=
    cfc_mem_of_isClosed A.isClosed_sotClosureSubalgebra continuous_tanHalfArcsin tanHalfArcsin_zero hT
  have hSsa : IsSelfAdjoint S := cfc_predicate _ _
  have hS := NonUnitalStarSubalgebra.mem_closure_toSOT_selfAdjoint hSmem hSsa
  -- the filter below is nontrivial because `↑ₚₜ S` is in the closure
  have := mem_closure_iff_nhdsWithin_neBot.mp hS
  let toB : BSOT → B := (toUniformConvergenceCLM _ _ _).symm
  refine mem_closure_of_tendsto (f := fun Y => ↑ₚₜ (cfc sinTwoArctan (toB Y)))
    (b := 𝓝[Set.toSOT {a | a ∈ A ∧ IsSelfAdjoint a}] (↑ₚₜ S)) ?_ ?_
  · rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro x
    rw [← sinTwoArctan_cfc_tanHalfArcsin hsa hn]
    refine tendsto_cfc_sinTwoArctan (c := toB) (eventually_nhdsWithin_of_forall fun Y hY => hY.2) hSsa
      (fun y => ?_) x
    exact PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp
      (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id) y
  · refine eventually_nhdsWithin_of_forall fun Y hY => ?_
    exact ⟨cfc_mem_of_isClosed hA continuous_sinTwoArctan sinTwoArctan_zero hY.1, cfc_predicate _ _,
      norm_cfc_sinTwoArctan_le⟩

/-- An operator matrix whose entries lie in the strong closure of `A` lies in the strong closure
of `matrixTwo A`. -/
private lemma mem_sotClosureSubalgebra_matrixTwo {A : NonUnitalStarSubalgebra ℂ B}
    {N : CStarMatrix (Fin 2) (Fin 2) B} (hN : ∀ i j, N i j ∈ A.sotClosureSubalgebra) :
    Φ N ∈ (matrixTwo A).sotClosureSubalgebra := by
  let toB : BSOT → B := (toUniformConvergenceCLM _ _ _).symm
  let G : (Fin 2 → Fin 2 → H →SLₚₜ[RingHom.id ℂ] H) →
      K →Lₚₜ[ℂ] K :=
    fun M => ContinuousLinearMap.toSOT
      (Φ (CStarMatrix.ofMatrix fun i j => toB (M i j)))
  have hG : Continuous G := by
    refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun ξ => ?_
    have : (fun M => G M ξ) = fun M => WithLp.toLp 2 (fun i => ∑ j, M i j (ξ.ofLp j)) := by
      funext M
      ext i
      exact CStarMatrix.toPiLpStarAlgEquiv_apply _ ξ i
    rw [this]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_finsetSum _
      fun j _ => (continuous_eval_const _).comp ((continuous_apply j).comp (continuous_apply i)))
  have hM : (fun i j => ↑ₚₜ (N i j)) ∈
      closure (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
        Set.toSOT (A : Set B)) := by
    rw [closure_pi_set]
    intro i _
    rw [closure_pi_set]
    exact fun j _ => hN i j
  have h := map_mem_closure (t := Set.toSOT (matrixTwo A : Set _)) hG hM fun M hM => by
    change (toUniformConvergenceCLM _ _ _).symm (G M) ∈ matrixTwo A
    intro i j
    change (Φ).symm
      ((Φ) _) i j ∈ A
    rw [StarAlgEquiv.symm_apply_apply]
    exact hM i trivial j trivial
  have hGN : G (fun i j => ↑ₚₜ (N i j)) = ContinuousLinearMap.toSOT (Φ N) := by
    change ContinuousLinearMap.toSOT _ = _
    congr 2
  rw [NonUnitalStarSubalgebra.mem_sotClosureSubalgebra_iff, ← hGN]
  exact h

/-! ### The closed unit ball, its self-adjoint part and its positive part, as sets -/

private lemma inter_closedBall_eq (A : NonUnitalStarSubalgebra ℂ B) :
    (A : Set B) ∩ Metric.closedBall 0 1 = {a | a ∈ A ∧ ‖a‖ ≤ 1} := by
  ext a
  exact and_congr_right fun _ => mem_closedBall_zero_iff

private lemma inter_selfAdjoint_inter_closedBall_eq (A : NonUnitalStarSubalgebra ℂ B) :
    (A : Set B) ∩ selfAdjoint B ∩ Metric.closedBall 0 1 = {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1} := by
  ext a
  simp only [Set.mem_inter_iff, SetLike.mem_coe, selfAdjoint.mem_iff, mem_closedBall_zero_iff,
    Set.mem_ofPred_eq, and_assoc]
  rfl

private lemma inter_nonneg_inter_closedBall_eq (A : NonUnitalStarSubalgebra ℂ B) :
    (A : Set B) ∩ {a | 0 ≤ a} ∩ Metric.closedBall 0 1 = {a | a ∈ A ∧ 0 ≤ a ∧ ‖a‖ ≤ 1} := by
  ext a
  simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_closedBall_zero_iff, Set.mem_ofPred_eq,
    and_assoc]

private lemma selfAdjoint_inter_closedBall_eq :
    (selfAdjoint B : Set B) ∩ Metric.closedBall 0 1 = {a | IsSelfAdjoint a ∧ ‖a‖ ≤ 1} := by
  ext a
  simp only [Set.mem_inter_iff, SetLike.mem_coe, selfAdjoint.mem_iff, mem_closedBall_zero_iff,
    Set.mem_ofPred_eq]
  rfl

omit [CompleteSpace H] in
private lemma nonneg_inter_closedBall_eq :
    {a : B | 0 ≤ a} ∩ Metric.closedBall 0 1 = {a | 0 ≤ a ∧ ‖a‖ ≤ 1} := by
  ext a
  simp only [Set.mem_inter_iff, mem_closedBall_zero_iff, Set.mem_ofPred_eq]

omit [CompleteSpace H] in
private lemma closedBall_eq : (Metric.closedBall 0 1 : Set B) = {a | ‖a‖ ≤ 1} := by
  ext a
  exact mem_closedBall_zero_iff

/-- **Kaplansky density theorem, self-adjoint part.** For a `⋆`-subalgebra `A` of `B(H)`, the
self-adjoint contractions of `A` are strongly dense in the self-adjoint contractions of the strong
closure of `A`. -/
theorem closure_toSOT_selfAdjoint_closedBall (A : NonUnitalStarSubalgebra ℂ B) :
    closure (Set.toSOT (A ∩ selfAdjoint B ∩ Metric.closedBall 0 1)) =
      closure (Set.toSOT (A : Set B)) ∩ Set.toSOT (selfAdjoint B ∩ Metric.closedBall 0 1) := by
  rw [inter_selfAdjoint_inter_closedBall_eq, selfAdjoint_inter_closedBall_eq]
  refine subset_antisymm (closure_minimal (fun Y hY => ⟨subset_closure hY.1, hY.2⟩)
    (isClosed_closure.inter (isClosed_toSOT_isSelfAdjoint.inter isClosed_toSOT_norm_le_one))) ?_
  rintro Y ⟨hY, hsa, hn⟩
  set T : B := (toUniformConvergenceCLM _ _ _).symm Y
  have hYT : Y = ↑ₚₜ T := ((toUniformConvergenceCLM _ _ _).apply_symm_apply Y).symm
  rw [hYT] at hY ⊢
  let C := A.topologicalClosure
  have hTC : T ∈ C.sotClosureSubalgebra :=
    closure_mono (s := Set.toSOT (A : Set B)) (t := Set.toSOT (C : Set B))
      (Set.preimage_mono A.le_topologicalClosure) hY
  have h := mem_closure_selfAdjoint_closedBall_of_isClosed A.isClosed_topologicalClosure hTC
    hsa hn
  refine closure_minimal (s := Set.toSOT {a | a ∈ C ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1})
    (t := closure (Set.toSOT {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1})) (fun Z hZ => ?_)
    isClosed_closure h
  obtain ⟨hZC, hZsa, hZn⟩ := hZ
  have hZ := ((toUniformConvergenceCLM _ _ _).apply_symm_apply Z).symm
  rw [hZ]
  exact map_mem_closure (ContinuousLinearMap.toSOT (σ := RingHom.id ℂ) (E := H) (F := H)).continuous
    (Kaplansky.mem_closure_selfAdjoint_closedBall hZC hZsa hZn) fun a ha => ha

/-- **Kaplansky density theorem, positive part.** For a `⋆`-subalgebra `A` of `B(H)`, the
positive contractions of `A` are strongly dense in the positive contractions of the strong
closure of `A`. -/
theorem closure_toSOT_nonneg_closedBall (A : NonUnitalStarSubalgebra ℂ B) :
    closure (Set.toSOT (A ∩ {a | 0 ≤ a} ∩ Metric.closedBall 0 1)) =
      closure (Set.toSOT (A : Set B)) ∩ Set.toSOT ({a | 0 ≤ a} ∩ Metric.closedBall 0 1) := by
  rw [inter_nonneg_inter_closedBall_eq, nonneg_inter_closedBall_eq]
  refine subset_antisymm (closure_minimal (fun Y hY => ⟨subset_closure hY.1, hY.2⟩)
    (isClosed_closure.inter (isClosed_toSOT_nonneg.inter isClosed_toSOT_norm_le_one))) ?_
  rintro Y ⟨hY, hpos, hn⟩
  set T : B := (toUniformConvergenceCLM _ _ _).symm Y
  have hYT : Y = ↑ₚₜ T := ((toUniformConvergenceCLM _ _ _).apply_symm_apply Y).symm
  rw [hYT] at hY ⊢
  have hTsa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hpos
  set S := cfc Real.sqrt T
  have hSmem : S ∈ A.sotClosureSubalgebra :=
    Kaplansky.cfc_mem_of_isClosed A.isClosed_sotClosureSubalgebra Real.continuous_sqrt Real.sqrt_zero hY
  have hSsa : IsSelfAdjoint S := cfc_predicate _ _
  have hSn : ‖S‖ ≤ 1 := norm_cfc_le (a := T) zero_le_one fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
    exact (le_abs_self t).trans (Kaplansky.abs_le_norm_of_mem_spectrum ht |>.trans hn)
  have hSS : S * S = T := by
    rw [← cfc_mul ..]
    refine (cfc_congr fun t ht => ?_).trans (cfc_id' ℝ T hTsa)
    exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hpos ht)
  have hS : ↑ₚₜ S ∈ closure (Set.toSOT {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1}) := by
    have h := A.closure_toSOT_selfAdjoint_closedBall
    rw [inter_selfAdjoint_inter_closedBall_eq, selfAdjoint_inter_closedBall_eq] at h
    rw [h]
    exact ⟨hSmem, hSsa, hSn⟩
  -- the filter below is nontrivial because `↑ₚₜ S` is in the closure
  have := mem_closure_iff_nhdsWithin_neBot.mp hS
  let toB : BSOT → B := (toUniformConvergenceCLM _ _ _).symm
  have hlim : ∀ x, Filter.Tendsto (fun Y => toB Y x)
      (𝓝[Set.toSOT {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1}] (↑ₚₜ S)) (𝓝 (S x)) := fun x =>
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp
      (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id) x
  refine mem_closure_of_tendsto (f := fun Y => ↑ₚₜ (toB Y * toB Y))
    (b := 𝓝[Set.toSOT {a | a ∈ A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1}] (↑ₚₜ S)) ?_ ?_
  · rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto, ← hSS]
    exact Kaplansky.tendsto_mul_apply (eventually_nhdsWithin_of_forall fun Y hY => hY.2.2) hlim hlim
  · refine eventually_nhdsWithin_of_forall fun Y hY => ?_
    obtain ⟨hmem, hsa, hle⟩ := hY
    refine ⟨A.mul_mem hmem hmem, ?_, ?_⟩
    · have h := star_mul_self_nonneg (toB Y)
      rw [hsa.star_eq] at h
      exact h
    · exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (toB Y)])

/-- **Kaplansky density theorem.** For a `⋆`-subalgebra `A` of `B(H)`, the contractions of `A`
are strongly dense in the contractions of the strong closure of `A`. -/
theorem closure_toSOT_closedBall (A : NonUnitalStarSubalgebra ℂ B) :
    closure (Set.toSOT (A ∩ Metric.closedBall 0 1)) =
      closure (Set.toSOT (A : Set B)) ∩ Set.toSOT (Metric.closedBall 0 1) := by
  rw [inter_closedBall_eq, closedBall_eq]
  refine subset_antisymm (closure_minimal (fun Y hY => ⟨subset_closure hY.1, hY.2⟩)
    (isClosed_closure.inter isClosed_toSOT_norm_le_one)) ?_
  rintro Y ⟨hY, hn⟩
  set T : B := (toUniformConvergenceCLM _ _ _).symm Y
  have hYT : Y = ↑ₚₜ T := ((toUniformConvergenceCLM _ _ _).apply_symm_apply Y).symm
  rw [hYT] at hY ⊢
  let N : CStarMatrix (Fin 2) (Fin 2) B := CStarMatrix.ofMatrix !![0, T; star T, 0]
  have hNsa : star N = N := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N, CStarMatrix.star_apply]
  have hXsa : IsSelfAdjoint (Φ N) := by
    have h1 : (Φ) (star N) =
        star ((Φ) N) :=
      (Φ).map_star' N
    change star _ = _
    rw [← h1, hNsa]
  have hXn : ‖Φ N‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
    rw [one_mul]
    have hT1 : ‖T‖ ≤ 1 := hn
    have hb : ∀ (S : B), ‖S‖ ≤ 1 → ∀ x, ‖S x‖ ≤ ‖x‖ := fun S hS x =>
      (S.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hS)
    have h0 : (Φ N ξ).ofLp 0 = T (ξ.ofLp 1) := by
      simp [CStarMatrix.toPiLpStarAlgEquiv_apply, Fin.sum_univ_two, N]
    have h1 : (Φ N ξ).ofLp 1 = star T (ξ.ofLp 0) := by
      simp [CStarMatrix.toPiLpStarAlgEquiv_apply, Fin.sum_univ_two, N]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_two, h0, h1, add_comm (‖ξ.ofLp 0‖ ^ 2)]
    gcongr
    · exact hb T hT1 _
    · exact hb (star T) (by rwa [norm_star]) _
  have hXmem : Φ N ∈ (Kaplansky.matrixTwo A).sotClosureSubalgebra := by
    refine mem_sotClosureSubalgebra_matrixTwo fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact zero_mem _
    · exact hY
    · exact star_mem (s := A.sotClosureSubalgebra) hY
    · exact zero_mem _
  have h : (ContinuousLinearMap.toSOT (Φ N) :
      K →Lₚₜ[ℂ] K) ∈
      closure (Set.toSOT {a | a ∈ Kaplansky.matrixTwo A ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ 1}) := by
    have h := (Kaplansky.matrixTwo A).closure_toSOT_selfAdjoint_closedBall
    rw [inter_selfAdjoint_inter_closedBall_eq, selfAdjoint_inter_closedBall_eq] at h
    rw [h]
    exact ⟨hXmem, hXsa, hXn⟩
  have h' := map_mem_closure (t := Set.toSOT {a | a ∈ A ∧ ‖a‖ ≤ 1}) Kaplansky.continuous_corner h
    fun Z hZ => ⟨hZ.1 0 1, (Kaplansky.norm_corner_le _).trans hZ.2.2⟩
  have hc : Kaplansky.corner ((toUniformConvergenceCLM _ _ _).symm
      (ContinuousLinearMap.toSOT (Φ N) :
        K →Lₚₜ[ℂ] K)) = T := by
    change Kaplansky.corner ((Φ) N) = T
    rw [Kaplansky.corner_toPiLpStarAlgEquiv]
    rfl
  rwa [hc] at h'

/-- **Kaplansky density theorem, von Neumann algebra form.** For a `⋆`-subalgebra `A` of `B(H)`
acting non-degenerately, the contractions of `A` are strongly dense in the contractions of the
double commutant `A′′`. -/
theorem closure_toSOT_closedBall_eq_doubleCommutant
    (A : NonUnitalStarSubalgebra ℂ B) (hnd : InnerProductSpace.ActsNondegenerately (A : Set B)) :
    closure (Set.toSOT (A ∩ Metric.closedBall 0 1)) = Set.toSOT ((A : Set B)′′ ∩ Metric.closedBall 0 1) := by
  rw [A.closure_toSOT_closedBall, A.sotClosure_eq_doubleCommutant hnd]
  rfl

/-- **Kaplansky density theorem, weak form.** For a `⋆`-subalgebra `A` of `B(H)`, the contractions
of `A` are weakly dense in the contractions of the weak closure of `A`. -/
theorem closure_toWOT_closedBall (A : NonUnitalStarSubalgebra ℂ B) :
    closure (Set.toWOT (A ∩ Metric.closedBall 0 1)) =
      closure (Set.toWOT (A : Set B)) ∩ Set.toWOT (Metric.closedBall 0 1) := by
  have hconvA : Convex ℝ (A : Set B) := (A.toSubmodule.restrictScalars ℝ).convex
  have hconv : Convex ℝ ((A : Set B) ∩ Metric.closedBall 0 1) :=
    hconvA.inter (convex_closedBall 0 1)
  ext Y
  have hY : Y = sotToWOT (↑ₚₜ (ContinuousLinearMapWOT.toCLM Y)) := rfl
  rw [hY, ← mem_closure_toSOT_iff_of_convex hconv, Set.mem_inter_iff,
    ← mem_closure_toSOT_iff_of_convex hconvA, A.closure_toSOT_closedBall]
  rfl

end NonUnitalStarSubalgebra

end
