/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSystem.ChoiEffros
public import QuantumSystem.Analysis.OperatorSystem.Injective
public import QuantumSystem.Analysis.OperatorSystem.KPositiveMap

/-!
# The injective envelope of an operator system

Every operator system `V` has an injective envelope (`OperatorSystem.IsInjectiveEnvelope`)
`κ : V → I(V)` (`OperatorSystem.isInjectiveEnvelope_toInjectiveEnvelope`), into the injective
operator system `I(V) = OperatorSystem.InjectiveEnvelope V`: a unital complete order embedding that
is rigid, in that the only completely positive map `γ : I(V) → I(V)` with `γ ∘ κ = κ` is the
identity. Every injective envelope of `V` is completely order isomorphic to it over `V`
(`OperatorSystem.IsInjectiveEnvelope.exists_linearEquiv`).

With `V` an operator subsystem `S` of `B(H)` (by the Choi–Effros theorem,
`OperatorSystem.isCompleteOrderEmbedding_directSumMap`), `I(V)` is the range of a minimal completely
positive map fixing `S`. The completely positive maps `φ : B(H) → B(H)` fixing every element of `S`
(`OperatorSubsystem.FixingMap`) are preordered by `φ ≤ ψ ↔ ∀ x, ‖φ x‖ ≤ ‖ψ x‖`. They are unital,
hence contractions. They are compact in the product of weak operator topologies
(`CompletelyPositiveMap'.exists_forall_isClosed`), and the norm is lower semicontinuous there, so
Zorn's lemma gives a minimal one (`OperatorSubsystem.FixingMap.exists_isMin`).

For a minimal `φ` and any `γ` fixing `S`, the Cesàro means `n⁻¹ ∑_{k<n} γᵏ φ` fix `S` and lie below
`φ`, hence have the same norms as `φ`. With `γ = φ` this gives `‖φ x - φ² x‖ ≤ 2 ‖x‖ / n`, so `φ` is
idempotent (`OperatorSubsystem.FixingMap.isIdempotentElem_of_isMin`); with `γ` replaced by `φ γ` it
gives `φ γ φ = φ` (`OperatorSubsystem.FixingMap.mul_mul_self_of_isMin`). The range
(`OperatorSubsystem.FixingMap.range`) of an idempotent map fixing `S` is a retract of the injective
`B(H)`, hence injective (`OperatorSubsystem.FixingMap.injective_range`); for a minimal `φ`, every
completely positive map of the range into itself fixing `S` is the identity
(`OperatorSubsystem.FixingMap.eq_id_of_isMin`). Two minimal maps have ranges that are completely
order isomorphic over `S`.

## Main definitions

* `OperatorSubsystem.FixingMap S` — the completely positive maps on `B(H)` fixing `S`, preordered by
  their norms.
* `OperatorSubsystem.FixingMap.range φ` — the range of a map `φ` fixing `S`; for minimal `φ`, the
  injective envelope of `S`.
* `OperatorSubsystem.FixingMap.minimal S` — a minimal map fixing `S`.
* `OperatorSystem.InjectiveEnvelope V`, with the scoped notation `I(V)`,
  `OperatorSystem.toInjectiveEnvelope V` — the injective
  envelope of an operator system `V` and the embedding of `V` into it.

## Main results

* `OperatorSubsystem.FixingMap.exists_isMin` — minimal maps fixing `S` exist.
* `OperatorSubsystem.FixingMap.isIdempotentElem_of_isMin` — they are idempotent.
* `OperatorSubsystem.FixingMap.mul_mul_self_of_isMin` — `φ γ φ = φ` for every `γ` fixing `S`.
* `OperatorSubsystem.FixingMap.injective_range` — the range of an idempotent map fixing `S` is
  injective.
* `OperatorSubsystem.FixingMap.eq_id_of_isMin` — the range of a minimal `φ` is rigid.
* `OperatorSubsystem.FixingMap.isInjectiveEnvelope_inclusion` — the range of a minimal `φ` is an
  injective envelope of `S`, unique up to complete order isomorphism over `S`
  (`OperatorSubsystem.FixingMap.exists_linearEquiv_range`).
* **`OperatorSystem.isInjectiveEnvelope_toInjectiveEnvelope`** — every operator system has an
  injective envelope.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra NNReal
open Filter Topology ContinuousLinearMapWOT

namespace OperatorSubsystem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : OperatorSubsystem (H →L[ℂ] H))

/-- The completely positive maps on `B(H)` that fix every element of `S`, preordered by
`φ ≤ ψ ↔ ∀ x, ‖φ x‖ ≤ ‖ψ x‖`. -/
structure FixingMap where
  /-- The underlying completely positive map. -/
  toMap : (H →L[ℂ] H) →CP' (H →L[ℂ] H)
  map_eq_self : ∀ s ∈ S, toMap s = s

namespace FixingMap

variable {S}

/-- Maps fixing `S` are preordered by `φ ≤ ψ ↔ ∀ x, ‖φ x‖ ≤ ‖ψ x‖`. -/
instance : Preorder (FixingMap S) where
  le φ ψ := ∀ x, ‖φ.toMap x‖ ≤ ‖ψ.toMap x‖
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ x := (h₁ x).trans (h₂ x)

/-- `φ ≤ ψ` when `‖φ x‖ ≤ ‖ψ x‖` for every `x`. -/
lemma le_def {φ ψ : FixingMap S} : φ ≤ ψ ↔ ∀ x, ‖φ.toMap x‖ ≤ ‖ψ.toMap x‖ := Iff.rfl

/-- The identity map fixes `S`. -/
instance : One (FixingMap S) := ⟨⟨1, fun _ _ => rfl⟩⟩

/-- The composition of maps fixing `S` fixes `S`. -/
instance : Mul (FixingMap S) := ⟨fun ψ φ => ⟨ψ.toMap * φ.toMap, fun s hs => by
  rw [CompletelyPositiveMap'.mul_apply, φ.map_eq_self s hs, ψ.map_eq_self s hs]⟩⟩

/-- The identity map, as a map fixing `S`, is `1`. -/
@[simp] lemma toMap_one : (1 : FixingMap S).toMap = 1 := rfl

/-- The composition of maps fixing `S` is their product. -/
@[simp] lemma toMap_mul (ψ φ : FixingMap S) : (ψ * φ).toMap = ψ.toMap * φ.toMap := rfl

/-- A map fixing `S` is unital. -/
lemma map_one (φ : FixingMap S) : φ.toMap 1 = 1 := φ.map_eq_self 1 (one_mem S)

/-- A map fixing `S` is a contraction: it is a unital `2`-positive map, hence a Schwarz map. -/
lemma norm_apply_le (φ : FixingMap S) (x : H →L[ℂ] H) : ‖φ.toMap x‖ ≤ ‖x‖ :=
  SchwarzMapClass.norm_apply_le (KPositiveMapClass.toSchwarzMap φ.toMap φ.map_one.le) x

/-- **Existence of minimal maps fixing `S`.** The maps fixing `S` are compact in the product of
weak operator topologies (`CompletelyPositiveMap'.exists_forall_isClosed`), and `‖φ x‖` is lower
semicontinuous there (`ContinuousLinearMapWOT.isClosed_closedBall`), so a chain has a cluster point
below each of its elements; Zorn's lemma gives a minimal element. -/
lemma exists_isMin : ∃ φ : FixingMap S, IsMin φ := by
  obtain ⟨φ, hφ⟩ := zorn_le (α := (FixingMap S)ᵒᵈ) fun c hc => by
    rcases c.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨OrderDual.toDual 1, by simp⟩
    have : Nonempty c := ⟨⟨a, ha⟩⟩
    have : IsDirected c (· ≤ ·) := ⟨fun x y => (hc.total x.2 y.2).elim
      (fun h => ⟨y, h, le_rfl⟩) fun h => ⟨x, le_rfl, h⟩⟩
    obtain ⟨ψ₀, hψ₀⟩ := CompletelyPositiveMap'.exists_forall_isClosed (l := atTop)
      (fun i : c => (OrderDual.ofDual i.1).toMap) (c := ‖(1 : H →L[ℂ] H)‖)
      fun i => by rw [map_one]
    have hfix : ∀ s ∈ S, ψ₀ s = s := fun s hs => congrArg toCLM <|
      hψ₀ {g | g s = ofCLM s} (isClosed_eq (continuous_apply s) continuous_const)
        (Eventually.of_forall fun i => by
          change ofCLM ((OrderDual.ofDual i.1).toMap s) = ofCLM s
          rw [(OrderDual.ofDual i.1).map_eq_self s hs])
    refine ⟨OrderDual.toDual ⟨ψ₀, hfix⟩, fun b hb => ?_⟩
    change ∀ x, ‖ψ₀ x‖ ≤ ‖(OrderDual.ofDual b).toMap x‖
    intro x
    have h := hψ₀ ((fun g => g x) ⁻¹' (ofCLM '' Metric.closedBall 0 ‖(OrderDual.ofDual b).toMap x‖))
      ((isClosed_closedBall 0 _).preimage (continuous_apply x)) ?_
    · simpa using h
    filter_upwards [eventually_ge_atTop ⟨b, hb⟩] with i hi
    exact ⟨_, mem_closedBall_zero_iff.mpr (hi x), rfl⟩
  exact ⟨OrderDual.ofDual φ, hφ.ofDual⟩

variable (S) in
/-- A minimal map fixing `S` (`OperatorSubsystem.FixingMap.exists_isMin`). -/
def minimal : FixingMap S := (exists_isMin (S := S)).choose

/-- `OperatorSubsystem.FixingMap.minimal S` is minimal. -/
instance : Fact (IsMin (minimal S)) := ⟨(exists_isMin (S := S)).choose_spec⟩

/-- The powers of a map fixing `S` fix `S`. -/
lemma pow_apply_of_mem (γ : FixingMap S) (k : ℕ) {s : H →L[ℂ] H} (hs : s ∈ S) : (γ.toMap ^ k) s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, CompletelyPositiveMap'.mul_apply, γ.map_eq_self s hs, ih]

/-- The powers of a map fixing `S` are contractions. -/
lemma norm_pow_apply_le (γ : FixingMap S) (k : ℕ) (x : H →L[ℂ] H) : ‖(γ.toMap ^ k) x‖ ≤ ‖x‖ := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => exact (ih _).trans (γ.norm_apply_le x)

/-- The Cesàro mean `n⁻¹ ∑_{k<n} γᵏ φ` of maps fixing `S`, for `n > 0`, fixes `S`. -/
def mean (γ φ : FixingMap S) (n : ℕ) (hn : 0 < n) : FixingMap S :=
  ⟨(n : ℝ≥0)⁻¹ • ∑ k ∈ Finset.range n, γ.toMap ^ k * φ.toMap, fun s hs => by
    simp only [CompletelyPositiveMap'.smul_apply, CompletelyPositiveMap'.coe_sum, Finset.sum_apply,
      CompletelyPositiveMap'.mul_apply, φ.map_eq_self s hs, pow_apply_of_mem γ _ hs, Finset.sum_const,
      Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [NNReal.coe_inv, NNReal.coe_natCast, Complex.ofReal_inv, Complex.ofReal_natCast,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul]⟩

/-- `mean γ φ n hn` sends `x` to `n⁻¹ ∑_{k<n} γᵏ (φ x)`. -/
lemma mean_apply (γ φ : FixingMap S) (n : ℕ) (hn : 0 < n) (x : H →L[ℂ] H) :
    (mean γ φ n hn).toMap x = (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, (γ.toMap ^ k) (φ.toMap x) := by
  simp [mean, CompletelyPositiveMap'.smul_apply, Finset.sum_apply]

/-- The Cesàro mean `n⁻¹ ∑_{k<n} γᵏ φ` lies below `φ`, as the powers of `γ` are contractions. -/
lemma mean_le (γ φ : FixingMap S) (n : ℕ) (hn : 0 < n) : mean γ φ n hn ≤ φ := fun x => by
  rw [mean_apply, norm_smul]
  calc ‖(n : ℂ)⁻¹‖ * ‖∑ k ∈ Finset.range n, (γ.toMap ^ k) (φ.toMap x)‖
      ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ‖φ.toMap x‖ := by
        rw [norm_inv, Complex.norm_natCast]
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_pow_apply_le γ k _)
    _ = ‖φ.toMap x‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_mul]

variable {φ : FixingMap S}

/-! ### Minimal maps

Minimality enters as a `Fact` instance, so that the idempotence of a minimal map, which the
C⋆-algebra structure on its range (`ChoiEffros`) takes as an instance in
`QuantumSystem.Analysis.OperatorSystem.CStarEnvelope`, is found by instance search. -/

section Minimal

variable [hφ : Fact (IsMin φ)]

variable (φ) in
/-- For a minimal `φ` fixing `S`, `‖φ w‖` is at most the norm of every Cesàro mean
`n⁻¹ ∑_{k<n} γᵏ (φ w)`: the mean lies below `φ` (`FixingMap.mean_le`), hence has the same norms. -/
lemma norm_apply_le_of_isMin (γ : FixingMap S) {n : ℕ} (hn : 0 < n)
    (w : H →L[ℂ] H) : ‖φ.toMap w‖ ≤ (n : ℝ)⁻¹ * ‖∑ k ∈ Finset.range n, (γ.toMap ^ k) (φ.toMap w)‖ := by
  have h := hφ.out (mean_le γ φ n hn) w
  rwa [mean_apply, norm_smul, norm_inv, Complex.norm_natCast] at h

/-- `∑_{k<n} θᵏ (y - θ y) = y - θⁿ y`. -/
private lemma sum_pow_apply_sub (θ : (H →L[ℂ] H) →CP' (H →L[ℂ] H)) (n : ℕ) (y : H →L[ℂ] H) :
    ∑ k ∈ Finset.range n, (θ ^ k) (y - θ y) = y - (θ ^ n) y := by
  have h (k : ℕ) : (θ ^ k) (y - θ y) = (θ ^ k) y - (θ ^ (k + 1)) y := by
    rw [map_sub, pow_succ, CompletelyPositiveMap'.mul_apply]
  simp only [h]
  rw [Finset.sum_range_sub', pow_zero, CompletelyPositiveMap'.one_apply]

omit [CompleteSpace H] in
/-- An operator of norm at most `C / n` for every `n > 0` is zero. -/
private lemma eq_zero_of_forall_norm_le {v : H →L[ℂ] H} {C : ℝ}
    (h : ∀ n : ℕ, 0 < n → ‖v‖ ≤ (n : ℝ)⁻¹ * C) : v = 0 := by
  refine norm_le_zero_iff.mp (ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat C) ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [div_eq_inv_mul]
  exact h n hn

/-- For `n > 0`, `‖y - θⁿ y‖ ≤ 2 ‖y‖` when the powers of `θ` are contractions. -/
private lemma norm_sub_pow_apply_le (γ : FixingMap S) (n : ℕ) (y : H →L[ℂ] H) :
    ‖y - (γ.toMap ^ n) y‖ ≤ 2 * ‖y‖ :=
  (norm_sub_le _ _).trans (by linarith [norm_pow_apply_le γ n y])

variable (φ) in
/-- **A minimal map fixing `S` is idempotent.** With the Cesàro means of the powers of `φ`,
`‖φ x - φ² x‖ = ‖φ (x - φ x)‖ ≤ n⁻¹ ‖φ x - φⁿ⁺¹ x‖ ≤ 2 ‖x‖ / n` for every `n > 0`. -/
lemma isIdempotentElem_of_isMin : IsIdempotentElem φ.toMap := by
  change φ.toMap * φ.toMap = φ.toMap
  refine CompletelyPositiveMap'.ext fun x => ?_
  have h : φ.toMap (x - φ.toMap x) = 0 := eq_zero_of_forall_norm_le (C := 2 * ‖x‖) fun n hn => by
    refine (norm_apply_le_of_isMin φ φ hn _).trans ?_
    rw [map_sub φ.toMap x, sum_pow_apply_sub]
    gcongr
    exact (norm_sub_pow_apply_le φ n _).trans (by gcongr; exact φ.norm_apply_le x)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

variable (φ) in
/-- **Rigidity of a minimal map fixing `S`.** For every `γ` fixing `S`, `φ γ φ = φ`. With
`θ = φ γ` and `y = φ x`, `w = y - θ y` is fixed by `φ`
(`OperatorSubsystem.FixingMap.isIdempotentElem_of_isMin`), and the Cesàro means of the powers of `θ`
give `‖w‖ = ‖φ w‖ ≤ n⁻¹ ‖y - θⁿ y‖ ≤ 2 ‖x‖ / n`. -/
lemma mul_mul_self_of_isMin (γ : FixingMap S) : φ.toMap * γ.toMap * φ.toMap = φ.toMap := by
  have hφφ (z : H →L[ℂ] H) : φ.toMap (φ.toMap z) = φ.toMap z :=
    DFunLike.congr_fun (isIdempotentElem_of_isMin φ).eq z
  refine CompletelyPositiveMap'.ext fun x => ?_
  set θ := φ * γ
  set y := φ.toMap x
  have hw : φ.toMap (y - θ.toMap y) = y - θ.toMap y := by
    simp only [θ, y, toMap_mul, map_sub, CompletelyPositiveMap'.mul_apply, hφφ]
  have h : y - θ.toMap y = 0 := eq_zero_of_forall_norm_le (C := 2 * ‖x‖) fun n hn => by
    refine hw ▸ (norm_apply_le_of_isMin φ θ hn _).trans ?_
    rw [hw, sum_pow_apply_sub]
    gcongr
    exact (norm_sub_pow_apply_le θ n y).trans (by gcongr; exact φ.norm_apply_le x)
  rw [sub_eq_zero] at h
  exact h.symm

end Minimal

/-! ### The injective envelope -/

variable (φ) in
/-- The range of a map `φ` fixing `S`, as an operator subsystem of `B(H)`; for minimal `φ`, the
injective envelope of `S`. -/
def range : OperatorSubsystem (H →L[ℂ] H) := φ.toMap.range φ.map_one

/-- `S` lies in the range of every map fixing it. -/
lemma mem_range {s : H →L[ℂ] H} (hs : s ∈ S) : s ∈ φ.range := ⟨s, φ.map_eq_self s hs⟩

variable (φ) in
/-- The map `φ` with values in its range `φ.range`. -/
def projection : (H →L[ℂ] H) →CP' φ.range :=
  φ.toMap.codRestrict φ.range (φ.toMap.mem_range_self φ.map_one)

variable (φ) in
/-- The inclusion of `S` into the range of a map fixing it. -/
def inclusion : S →CP' φ.range := S.subtype.codRestrict φ.range fun s => mem_range s.2

/-- `φ.inclusion s` is `s`. -/
@[simp] lemma coe_inclusion_apply (s : S) : (φ.inclusion s : H →L[ℂ] H) = s := rfl

/-- The inclusion of `S` into the range of `φ` is unital. -/
lemma inclusion_one : φ.inclusion 1 = 1 := rfl

variable (φ) in
/-- The inclusion of `S` into the range of `φ` is a complete order embedding, both carrying the
matrix orders of `B(H)`. -/
lemma isCompleteOrderEmbedding_inclusion : φ.inclusion.toLinearMap.IsCompleteOrderEmbedding :=
  fun _ _ => Iff.rfl

/-- `φ.projection x` is `φ x`. -/
@[simp] lemma coe_projection_apply (x : H →L[ℂ] H) : (φ.projection x : H →L[ℂ] H) = φ.toMap x := rfl

/-- An idempotent map fixing `S`, such as a minimal one
(`OperatorSubsystem.FixingMap.isIdempotentElem_of_isMin`), fixes its range. -/
lemma apply_eq_self_of_isIdempotentElem (hφ : IsIdempotentElem φ.toMap) {x : H →L[ℂ] H}
    (hx : x ∈ φ.range) : φ.toMap x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact DFunLike.congr_fun hφ.eq y

/-- **The range of an idempotent map fixing `S` is injective**, in particular the injective envelope,
the range of a minimal map: `φ` itself is a completely positive retraction of the injective `B(H)`
(`OperatorSystem.injective_continuousLinearMap`) onto it
(`OperatorSubsystem.injective_iff_exists_retraction`). -/
lemma injective_range (hφ : IsIdempotentElem φ.toMap) : OperatorSystem.Injective φ.range :=
  (injective_iff_exists_retraction (OperatorSystem.injective_continuousLinearMap H) φ.range).mpr
    ⟨φ.projection, fun r => Subtype.ext (apply_eq_self_of_isIdempotentElem hφ r.2)⟩

/-- **The injective envelope is rigid.** A completely positive map `γ` of the range of a minimal `φ`
fixing `S` into itself that fixes `S` is the identity: `γ ∘ φ`, as a map on `B(H)`, fixes `S`, so
`φ (γ (φ x)) = φ x` (`OperatorSubsystem.FixingMap.mul_mul_self_of_isMin`), and `φ` fixes the values of
`γ`. -/
lemma eq_id_of_isMin [Fact (IsMin φ)] (γ : φ.range →CP' φ.range)
    (hγ : ∀ s, γ (φ.inclusion s) = φ.inclusion s) : γ = CompletelyPositiveMap'.id φ.range := by
  have hφ' := isIdempotentElem_of_isMin φ
  have hproj (r : φ.range) : φ.projection r = r :=
    Subtype.ext (apply_eq_self_of_isIdempotentElem hφ' r.2)
  let γ' : FixingMap S := ⟨φ.range.subtype.comp (γ.comp φ.projection), fun s hs => by
    change (γ (φ.projection s) : H →L[ℂ] H) = s
    rw [show φ.projection s = φ.inclusion ⟨s, hs⟩ from Subtype.ext (φ.map_eq_self s hs), hγ]
    rfl⟩
  refine CompletelyPositiveMap'.ext fun r => Subtype.ext ?_
  have h := DFunLike.congr_fun (mul_mul_self_of_isMin φ γ') (r : H →L[ℂ] H)
  simp only [CompletelyPositiveMap'.mul_apply, apply_eq_self_of_isIdempotentElem hφ' r.2] at h
  change φ.toMap (γ (φ.projection (r : H →L[ℂ] H)) : H →L[ℂ] H) = r at h
  rwa [hproj, apply_eq_self_of_isIdempotentElem hφ' (γ r).2] at h

/-- **The range of a minimal map fixing `S` is an injective envelope of `S`**: the inclusion is a
unital complete order embedding into an injective operator system
(`OperatorSubsystem.FixingMap.injective_range`), and it is rigid
(`OperatorSubsystem.FixingMap.eq_id_of_isMin`). -/
theorem isInjectiveEnvelope_inclusion (φ : FixingMap S) [Fact (IsMin φ)] :
    OperatorSystem.IsInjectiveEnvelope φ.inclusion.toLinearMap where
  map_one := inclusion_one
  isCompleteOrderEmbedding := isCompleteOrderEmbedding_inclusion φ
  injective := injective_range (isIdempotentElem_of_isMin φ)
  rigid := eq_id_of_isMin

/-- **Uniqueness of the injective envelope.** The ranges of two minimal maps `φ`, `ψ` fixing `S` are
completely order isomorphic over `S`, both being injective envelopes of `S`
(`OperatorSystem.IsInjectiveEnvelope.exists_linearEquiv`). -/
lemma exists_linearEquiv_range (φ ψ : FixingMap S) [Fact (IsMin φ)] [Fact (IsMin ψ)] :
    ∃ e : φ.range ≃ₗ[ℂ] ψ.range, (e : φ.range →ₗ[ℂ] ψ.range).IsCompleteOrderEmbedding ∧
      ∀ s, e (φ.inclusion s) = ψ.inclusion s :=
  (isInjectiveEnvelope_inclusion φ).exists_linearEquiv (isInjectiveEnvelope_inclusion ψ)

end FixingMap

end OperatorSubsystem

namespace OperatorSystem

variable (V : Type*) [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V] [PartialOrder V]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [One V] [OperatorSystem V]

/-- **The injective envelope** `I(V)` of an operator system `V`: the range of a minimal completely
positive map on `B(H)` fixing the image of `V` (`OperatorSubsystem.FixingMap.minimal`). -/
abbrev InjectiveEnvelope : Type _ := (OperatorSubsystem.FixingMap.minimal (rangeDirectSumMap V)).range

@[inherit_doc] scoped[OperatorSystem] notation "I(" V ")" => OperatorSystem.InjectiveEnvelope V

/-- The embedding of `V` into its injective envelope. -/
def toInjectiveEnvelope : V →ₗ[ℂ] I(V) :=
  LinearMap.codRestrict _ (directSumMap V) fun v =>
    OperatorSubsystem.FixingMap.mem_range (S := rangeDirectSumMap V) ⟨v, rfl⟩

/-- The underlying operator of `toInjectiveEnvelope V v` is `directSumMap V v`. -/
@[simp] lemma coe_toInjectiveEnvelope_apply (v : V) :
    (toInjectiveEnvelope V v : DirectSumSpace V →L[ℂ] DirectSumSpace V) = directSumMap V v :=
  rfl

/-- **Existence of the injective envelope.** The embedding of an operator system `V` into
`OperatorSystem.InjectiveEnvelope V` is an injective envelope of `V`: the range of a minimal map
fixing the image of `V` is injective (`OperatorSubsystem.FixingMap.injective_range`) and rigid
(`OperatorSubsystem.FixingMap.eq_id_of_isMin`). Every injective envelope of `V` is completely
order isomorphic to it over `V` (`OperatorSystem.IsInjectiveEnvelope.exists_linearEquiv`). -/
theorem isInjectiveEnvelope_toInjectiveEnvelope : IsInjectiveEnvelope (toInjectiveEnvelope V) where
  map_one := Subtype.ext (directSumMap_one V)
  isCompleteOrderEmbedding := fun k X => isCompleteOrderEmbedding_directSumMap V k X
  injective :=
    OperatorSubsystem.FixingMap.injective_range (OperatorSubsystem.FixingMap.isIdempotentElem_of_isMin _)
  rigid γ hγ := by
    refine OperatorSubsystem.FixingMap.eq_id_of_isMin
      (φ := OperatorSubsystem.FixingMap.minimal (rangeDirectSumMap V)) γ ?_
    rintro ⟨s, v, rfl⟩
    exact hγ v

end OperatorSystem
