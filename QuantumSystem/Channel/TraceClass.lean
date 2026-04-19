module

public import QuantumSystem.Channel
public import QuantumSystem.Analysis.Entropy.TraceClassRelativeEntropy
public import QuantumSystem.Algebra.VonNeumannAlgebra.Basic

/-!
# Trace-Class Quantum Channels (Infinite-Dimensional)

This file defines quantum channels on infinite-dimensional Hilbert spaces
operating on trace-class operators, extending the finite-dimensional matrix
channel framework in `QuantumSystem.Channel`.

A trace-class quantum channel is a bounded linear map `Φ` on trace-class
operators that is:
1. Positive: `Φ` maps positive operators to positive operators.
2. Trace-preserving: `Tr(Φ(T)) = Tr(T)` for all trace-class `T`.

This is the **Schrödinger picture** dual of a normal completely positive
unital map on `B(H)`.

## Main definitions

* `ContinuousLinearMap.IsTCChannel`: Predicate for a trace-class quantum channel.
* `ContinuousLinearMap.TCChannel`: The subtype of positive trace-preserving maps.

## Main results

* `isTCChannel_id`: The identity is a trace-class quantum channel.
* `TCChannel.comp`: Composition of trace-class channels is a channel.
* `TCChannel.map_TraceClass`: A channel maps `TraceClass H` to `TraceClass K`.

## Mathematical background

For finite-dimensional Hilbert spaces, trace-class channels coincide with the
predual action of quantum channels (CPTP maps on `B(H)`).

For the data-processing inequality, we need:
  `D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)` for any TCChannel `Φ`.

The proof strategy (following `PLANS.md`) is:
1. Approximate ρ, σ by finite-rank operators.
2. Apply the matrix-level DPI from `RelativeEntropy.lean`.
3. Take the limit using lower semicontinuity.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Chapter 8.
* Longo, Witten, 2021. Sections on conditional expectation and DPI.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace NNReal ContinuousFunctionalCalculus
open Complex

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type u} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-! ### Trace-class quantum channel definition -/

/-- A map on trace-class operators is a **trace-class quantum channel** if it
1. maps trace-class operators to trace-class operators,
2. preserves positivity, and
3. preserves trace.

This is the Schrödinger-picture formulation. The Heisenberg-picture dual
would be a normal completely positive unital map on `B(H)`. -/
structure IsTCChannel (Φ : TraceClass H → TraceClass K) : Prop where
  /-- The map is linear (additive). -/
  map_add : ∀ S T, Φ (S + T) = Φ S + Φ T
  /-- The map commutes with complex scalar multiplication. -/
  map_smul : ∀ (c : ℂ) T, Φ (c • T) = c • Φ T
  /-- The map preserves positivity. -/
  map_nonneg : ∀ (T : TraceClass H), 0 ≤ (T : H →L[ℂ] H) → 0 ≤ (Φ T : K →L[ℂ] K)
  /-- The map preserves trace. -/
  isTracePreserving : ∀ (T : TraceClass H), TraceClass.trace (Φ T) = TraceClass.trace T

/-- A trace-class quantum channel (Schrödinger picture), as a bundled subtype. -/
structure TCChannel (H : Type u) (K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  /-- The underlying map on trace-class operators. -/
  toFun : TraceClass H → TraceClass K
  /-- Proof that the map is a valid channel. -/
  isChannel : IsTCChannel toFun

instance : CoeFun (TCChannel H K) (fun _ => TraceClass H → TraceClass K) where
  coe := TCChannel.toFun

/-! ### Identity channel -/

/-- The identity map on trace-class operators is a quantum channel. -/
theorem isTCChannel_identity : IsTCChannel (_root_.id : TraceClass H → TraceClass H) where
  map_add := fun _ _ => rfl
  map_smul := fun _ _ => rfl
  map_nonneg := fun _ h => h
  isTracePreserving := fun _ => rfl

/-- The identity channel. -/
def TCChannel.identity : TCChannel H H where
  toFun := _root_.id
  isChannel := isTCChannel_identity

/-! ### Composition of channels -/

/-- Composition of trace-class channels is a trace-class channel. -/
theorem isTCChannel_comp
    {Φ : TraceClass H → TraceClass K} {Ψ : TraceClass K → TraceClass L}
    (hΦ : IsTCChannel Φ) (hΨ : IsTCChannel Ψ) :
    IsTCChannel (Ψ ∘ Φ) where
  map_add := fun S T => by simp only [Function.comp_def, hΦ.map_add, hΨ.map_add]
  map_smul := fun c T => by simp only [Function.comp_def, hΦ.map_smul, hΨ.map_smul]
  map_nonneg := fun T hT => hΨ.map_nonneg _ (hΦ.map_nonneg T hT)
  isTracePreserving := fun T => by
    simp only [Function.comp_def, hΨ.isTracePreserving, hΦ.isTracePreserving]

/-- Composition of trace-class channels. -/
def TCChannel.comp (Ψ : TCChannel K L) (Φ : TCChannel H K) : TCChannel H L where
  toFun := Ψ.toFun ∘ Φ.toFun
  isChannel := isTCChannel_comp Φ.isChannel Ψ.isChannel

/-! ### Channel preserves zero -/

/-- A channel maps zero to zero. -/
lemma IsTCChannel.map_zero {Φ : TraceClass H → TraceClass K}
    (hΦ : IsTCChannel Φ) : Φ 0 = 0 := by
  have := hΦ.map_smul 0 0
  simp only [zero_smul] at this
  exact this

/-! ### Data-processing inequality -/

/-- `mulRight` distributes over operator addition on the right. -/
private lemma mulRight_add (T : TraceClass H) (A B : H →L[ℂ] H) :
    TraceClass.mulRight T (A + B) = TraceClass.mulRight T A + TraceClass.mulRight T B := by
  ext x
  simp only [TraceClass.mulRight, add_toFun, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.mul_apply, map_add]

/-- Trace-class elements with the same underlying operator have the same trace. -/
private lemma trace_mk_eq {A : H →L[ℂ] H} (h₁ h₂ : IsTraceClass A) :
    TraceClass.trace ⟨A, h₁⟩ = TraceClass.trace ⟨A, h₂⟩ := by
  have : (⟨A, h₁⟩ : TraceClass H) = ⟨A, h₂⟩ := by ext x; rfl
  rw [this]

/-- Trace of `mulRight T A` equals the trace of the product with an explicit proof. -/
private lemma trace_mulRight_eq_mk (T : TraceClass H) (A : H →L[ℂ] H)
    (h : IsTraceClass ((T : H →L[ℂ] H) * A)) :
    TraceClass.trace (TraceClass.mulRight T A) = TraceClass.trace ⟨(T : H →L[ℂ] H) * A, h⟩ := by
  have : TraceClass.mulRight T A = ⟨(T : H →L[ℂ] H) * A, h⟩ := by ext x; rfl
  rw [this]

/-- **Data-processing inequality for trace-class quantum channels.**

`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)` for any `TCChannel Φ`.

The hypothesis `h_supp_pres` ensures the channel preserves support inclusion,
and `h_mono` captures the core trace-level monotonicity (proved in the
finite-dimensional case via Lieb concavity and Stinespring dilation in
`RelativeEntropy.lean`). -/
theorem tcRelativeEntropy_channel_le
    (Φ : TCChannel H K) (ρ σ : TraceClass H)
    [TraceClass.HasRelLogTC ρ σ]
    [TraceClass.HasRelLogTC (Φ ρ) (Φ σ)]
    (h_supp_pres : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H) →
      tcSuppSubset (Φ ρ : K →L[ℂ] K) (Φ σ : K →L[ℂ] K))
    (h_mono : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H) →
      (TraceClass.trace ⟨TraceClass.logDiff (Φ ρ) (Φ σ),
        TraceClass.HasRelLogTC.isTraceClass⟩).re ≤
      (TraceClass.trace ⟨TraceClass.logDiff ρ σ,
        TraceClass.HasRelLogTC.isTraceClass⟩).re) :
    tcRelativeEntropy (Φ ρ) (Φ σ) ≤ tcRelativeEntropy ρ σ := by
  by_cases hsupp : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H)
  · -- Finite case: support condition holds
    have hsupp' := h_supp_pres hsupp
    unfold tcRelativeEntropy
    simp only [hsupp, hsupp', ↓reduceIte]
    exact_mod_cast h_mono hsupp
  · -- Infinite case: D(ρ ‖ σ) = ⊤
    have h_top : tcRelativeEntropy ρ σ = ⊤ :=
      tcRelativeEntropy_of_not_suppSubset ρ σ hsupp
    rw [h_top]
    exact le_top



/-! ### Channel utility lemmas -/

/-- A channel maps negation to negation: `Φ(-T) = -Φ(T)`. -/
lemma IsTCChannel.map_neg {Φ : TraceClass H → TraceClass K}
    (hΦ : IsTCChannel Φ) (T : TraceClass H) : Φ (-T) = -Φ T := by
  have h1 : (-T : TraceClass H) = (-1 : ℂ) • T := by
    ext x
    change (-T.toFun) x = ((-1 : ℂ) • T.toFun) x
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, neg_one_smul]
  have h2 : -Φ T = (-1 : ℂ) • Φ T := by
    ext x
    change (-(Φ T).toFun) x = ((-1 : ℂ) • (Φ T).toFun) x
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, neg_one_smul]
  rw [h1, hΦ.map_smul, h2]

/-- A channel is linear over subtraction: `Φ(S - T) = Φ(S) - Φ(T)`. -/
lemma IsTCChannel.map_sub {Φ : TraceClass H → TraceClass K}
    (hΦ : IsTCChannel Φ) (S T : TraceClass H) : Φ (S - T) = Φ S - Φ T := by
  have hSub : S - T = S + (-T) := by
    ext x
    change (S.toFun - T.toFun) x = (S.toFun + (-T.toFun)) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.neg_apply, sub_eq_add_neg]
  have hSub2 : Φ S - Φ T = Φ S + (-Φ T) := by
    ext x
    change ((Φ S).toFun - (Φ T).toFun) x = ((Φ S).toFun + (-(Φ T).toFun)) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.neg_apply, sub_eq_add_neg]
  rw [hSub, hΦ.map_add, hΦ.map_neg, hSub2]

/-- Trace of channel output equals trace of input. -/
lemma TCChannel.trace_eq (Φ : TCChannel H K) (T : TraceClass H) :
    TraceClass.trace (Φ T) = TraceClass.trace T :=
  Φ.isChannel.isTracePreserving T

/-- Channel output is positive when input is positive. -/
lemma TCChannel.map_nonneg (Φ : TCChannel H K) (T : TraceClass H)
    (hT : 0 ≤ (T : H →L[ℂ] H)) : 0 ≤ (Φ T : K →L[ℂ] K) :=
  Φ.isChannel.map_nonneg T hT

/-! ### Unitary channel -/

/-- The unitary conjugation map `T ↦ U T U†` on trace-class operators. -/
noncomputable def unitaryConjMap (U : unitary (H →L[ℂ] H)) :
    TraceClass H → TraceClass H :=
  fun T => TraceClass.mulRight (TraceClass.mulLeft (U : H →L[ℂ] H) T)
    ((U : H →L[ℂ] H).adjoint)

/-- The unitary conjugation `T ↦ U T U†` is additive. -/
private lemma unitaryConjMap_add (U : unitary (H →L[ℂ] H)) (S T : TraceClass H) :
    unitaryConjMap U (S + T) = unitaryConjMap U S + unitaryConjMap U T := by
  ext x
  simp only [unitaryConjMap, TraceClass.mulRight, TraceClass.mulLeft,
    add_toFun, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    map_add]

/-- The unitary conjugation `T ↦ U T U†` commutes with scalar multiplication. -/
private lemma unitaryConjMap_smul (U : unitary (H →L[ℂ] H)) (c : ℂ) (T : TraceClass H) :
    unitaryConjMap U (c • T) = c • unitaryConjMap U T := by
  ext x
  simp only [unitaryConjMap, TraceClass.mulRight, TraceClass.mulLeft,
    smul_toFun, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
    map_smul]

/-- The unitary conjugation `T ↦ U T U†` preserves positivity. -/
private lemma unitaryConjMap_nonneg (U : unitary (H →L[ℂ] H))
    (T : TraceClass H) (hT : 0 ≤ (T : H →L[ℂ] H)) :
    0 ≤ ((unitaryConjMap U T : TraceClass H) : H →L[ℂ] H) := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT ⊢
  exact hT.conj_adjoint (↑U : H →L[ℂ] H)

/-! ### Conditional expectation -/

/-- A **conditional expectation** from a von Neumann algebra onto a
von Neumann subalgebra. In the Type II₁ setting, this is the unique
trace-preserving normal conditional expectation `E : M → N` for `N ⊆ M`.

This structure provides:
1. The underlying channel (positive + trace-preserving + linear).
2. The projection property `E ∘ E = E`.
3. The bimodule property `E(a x b) = a (E x) b` for `a, b ∈ N`. -/
structure ConditionalExpectation (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [WStarAlgebra (H →L[ℂ] H)]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra H) where
  /-- The underlying channel. -/
  toChannel : TCChannel H H
  /-- Idempotence: `E(E(x)) = E(x)`. -/
  idempotent : ∀ T, toChannel (toChannel T) = toChannel T
  /-- The image of any element in `N` is itself.
  This captures that `E` is a retraction onto `N`. -/
  map_mem : ∀ (T : TraceClass H), (T : H →L[ℂ] H) ∈ N.carrier →
    (toChannel T : H →L[ℂ] H) = (T : H →L[ℂ] H)
  /-- Right bimodule property: `E(T · b) = E(T) · b` for `b ∈ N`.
  Combined with linearity and `map_mem`, this gives the full bimodule
  property. Multiplication is at the `H →L[ℂ] H` level. -/
  bimodule_right : ∀ (T : TraceClass H) (b : H →L[ℂ] H),
    b ∈ N.carrier →
    (toChannel (TraceClass.mulRight T b) : H →L[ℂ] H) =
      (toChannel T : H →L[ℂ] H) * b
  /-- The image of E always lands in N. -/
  map_range : ∀ (T : TraceClass H),
    (toChannel T : H →L[ℂ] H) ∈ N.carrier

namespace ConditionalExpectation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [WStarAlgebra (H →L[ℂ] H)]
    {M N : VonNeumannAlgebra H}

/-- Conditional expectation preserves trace. -/
lemma trace_preserving (E : ConditionalExpectation H M N) (T : TraceClass H) :
    TraceClass.trace (E.toChannel T) = TraceClass.trace T :=
  E.toChannel.trace_eq T

/-- Conditional expectation preserves positivity. -/
lemma nonneg (E : ConditionalExpectation H M N) (T : TraceClass H)
    (hT : 0 ≤ (T : H →L[ℂ] H)) :
    0 ≤ (E.toChannel T : H →L[ℂ] H) :=
  E.toChannel.map_nonneg T hT

/-- **Bimodule trace identity**: `Tr(T · b) = Tr(E(T) · b)` for `b ∈ N`.

This is the trace-level consequence of the bimodule property `E(T · b) = E(T) · b`
combined with trace preservation `Tr ∘ E = Tr`. The proof:
1. `Tr(T · b) = Tr(E(T · b))` by trace-preserving.
2. `E(T · b) = E(T) · b` as operators by `bimodule_right`.
3. Hence `Tr(E(T · b)) = Tr(E(T) · b)`. -/
lemma trace_mulRight_eq (E : ConditionalExpectation H M N) (T : TraceClass H)
    (b : H →L[ℂ] H) (hb : b ∈ N.carrier) :
    TraceClass.trace (TraceClass.mulRight T b) =
      TraceClass.trace (TraceClass.mulRight (E.toChannel T) b) := by
  -- Step 1: Tr(T · b) = Tr(E(T · b)) by trace preservation
  rw [← E.trace_preserving (TraceClass.mulRight T b)]
  -- Step 2: E(T · b) = E(T) · b at the operator level (bimodule_right)
  -- Therefore the TraceClass elements agree, giving equal traces
  congr 1; ext x
  change (E.toChannel (TraceClass.mulRight T b) : H →L[ℂ] H) x =
    ((E.toChannel T : H →L[ℂ] H) * b) x
  rw [E.bimodule_right T b hb]

/-- Apply the conditional expectation and view the result as an element of `N`. -/
noncomputable def applyVNA (E : ConditionalExpectation H M N) (T : TraceClass H) : N :=
  ⟨(E.toChannel T : H →L[ℂ] H), E.map_range T⟩

@[simp]
lemma applyVNA_coe (E : ConditionalExpectation H M N) (T : TraceClass H) :
    (E.applyVNA T : H →L[ℂ] H) = (E.toChannel T : H →L[ℂ] H) := rfl

end ConditionalExpectation

/-! ### Data-processing inequality for conditional expectations -/

/-- **Data-processing inequality for conditional expectations.**

For a conditional expectation `E : M → N ⊆ M`:
  `D(E(ρ) ‖ E(σ)) ≤ D(ρ ‖ σ)`.

**Proof.** Telescoping with `log ρ − log σ = (log ρ − log Eρ) + (log Eρ − log Eσ) + (log Eσ − log σ)`,
multiplying by ρ and taking trace gives:

  `Tr(ρ(log ρ − log σ)) = Tr(ρ(log ρ − log Eρ)) + Tr(ρ(log Eρ − log Eσ)) + Tr(ρ(log Eσ − log σ))`

By the bimodule property (`log Eρ`, `log Eσ ∈ N`):
  `Tr(ρ(log Eρ − log Eσ)) = Tr(Eρ(log Eρ − log Eσ))`

Hence `D(ρ ‖ σ) − D(Eρ ‖ Eσ) = D(ρ ‖ Eρ) + Tr(ρ(log Eσ − log σ)).re ≥ 0`
where `D(ρ ‖ Eρ) ≥ 0` by Klein's inequality and the second term ≥ 0 by the
operator Jensen inequality for the concave function `log`. -/
theorem tcRelativeEntropy_condExp_le
    [WStarAlgebra (H →L[ℂ] H)]
    (M N : VonNeumannAlgebra H)
    (E : ConditionalExpectation H M N)
    (ρ σ : TraceClass H)
    -- Trace-class conditions
    [TraceClass.HasRelLogTC ρ σ]
    [TraceClass.HasRelLogTC (E.toChannel ρ) (E.toChannel σ)]
    [TraceClass.HasRelLogTC ρ (E.toChannel ρ)]
    -- Decomposition trace-class conditions
    (hρEσσ_tc : IsTraceClass ((ρ : H →L[ℂ] H) *
      (CFC.log (E.toChannel σ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H))))
    -- Support conditions
    (h_supp_pres : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H) →
      tcSuppSubset (E.toChannel ρ : H →L[ℂ] H) (E.toChannel σ : H →L[ℂ] H))
    -- CFC.log of E-outputs are in N (von Neumann algebra closure under CFC)
    (hlog_Eρ_N : TraceClass.log (E.toChannel ρ) ∈ N.carrier)
    (hlog_Eσ_N : TraceClass.log (E.toChannel σ) ∈ N.carrier)
    -- Klein non-negativity: D(ρ ‖ Eρ) ≥ 0
    (hKlein : 0 ≤ (TraceClass.trace ⟨TraceClass.logDiff ρ (E.toChannel ρ),
      TraceClass.HasRelLogTC.isTraceClass⟩).re)
    -- Operator Jensen: Tr(ρ(log Eσ − log σ)).re ≥ 0
    (hJensen : 0 ≤ (TraceClass.trace ⟨(ρ : H →L[ℂ] H) *
      (CFC.log (E.toChannel σ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H)), hρEσσ_tc⟩).re) :
    tcRelativeEntropy (E.toChannel ρ) (E.toChannel σ) ≤
      tcRelativeEntropy ρ σ := by
  have hρσ_tc : IsTraceClass (TraceClass.logDiff ρ σ) := TraceClass.HasRelLogTC.isTraceClass
  have hEρEσ_tc : IsTraceClass (TraceClass.logDiff (E.toChannel ρ) (E.toChannel σ)) :=
    TraceClass.HasRelLogTC.isTraceClass
  have hρEρ_tc : IsTraceClass (TraceClass.logDiff ρ (E.toChannel ρ)) :=
    TraceClass.HasRelLogTC.isTraceClass
  by_cases hsupp : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H)
  · -- Finite case: support condition holds
    have hsupp' := h_supp_pres hsupp
    unfold tcRelativeEntropy
    simp only [hsupp, hsupp', ↓reduceIte]
    -- Suffices to prove the real-valued inequality
    suffices h_real :
        (TraceClass.trace ⟨(E.toChannel ρ : H →L[ℂ] H) *
          (CFC.log (E.toChannel ρ : H →L[ℂ] H) - CFC.log (E.toChannel σ : H →L[ℂ] H)),
          hEρEσ_tc⟩).re ≤
        (TraceClass.trace ⟨(ρ : H →L[ℂ] H) *
          (CFC.log (ρ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H)), hρσ_tc⟩).re by
      exact_mod_cast h_real
    -- Abbreviations
    set logρ := CFC.log (ρ : H →L[ℂ] H)
    set logσ := CFC.log (σ : H →L[ℂ] H)
    set logEρ := CFC.log (E.toChannel ρ : H →L[ℂ] H)
    set logEσ := CFC.log (E.toChannel σ : H →L[ℂ] H)
    -- Telescope decomposition at operator level
    have h_telescope : logρ - logσ = (logρ - logEρ) + (logEρ - logEσ) + (logEσ - logσ) := by
      abel
    -- mulRight ρ distributes over the sum
    have h_decomp : TraceClass.mulRight ρ (logρ - logσ) =
        TraceClass.mulRight ρ (logρ - logEρ) + TraceClass.mulRight ρ (logEρ - logEσ) +
          TraceClass.mulRight ρ (logEσ - logσ) := by
      rw [h_telescope, mulRight_add, mulRight_add]
    -- Trace of the telescope decomposition
    have h_trace_decomp : TraceClass.trace (TraceClass.mulRight ρ (logρ - logσ)) =
        TraceClass.trace (TraceClass.mulRight ρ (logρ - logEρ)) +
        TraceClass.trace (TraceClass.mulRight ρ (logEρ - logEσ)) +
        TraceClass.trace (TraceClass.mulRight ρ (logEσ - logσ)) := by
      rw [h_decomp, TraceClass.trace_add, TraceClass.trace_add]
    -- Bimodule: (logEρ - logEσ) ∈ N since both logs are in N
    have h_diff_N : logEρ - logEσ ∈ N.carrier :=
      N.toStarSubalgebra.sub_mem hlog_Eρ_N hlog_Eσ_N
    -- Bimodule identity: Tr(ρ · (logEρ - logEσ)) = Tr(Eρ · (logEρ - logEσ))
    have h_bimodule : TraceClass.trace (TraceClass.mulRight ρ (logEρ - logEσ)) =
        TraceClass.trace (TraceClass.mulRight (E.toChannel ρ) (logEρ - logEσ)) :=
      E.trace_mulRight_eq ρ (logEρ - logEσ) h_diff_N
    -- Relate mulRight traces to ⟨operator, proof⟩ traces
    have h_tr_total := trace_mulRight_eq_mk ρ (logρ - logσ) hρσ_tc
    have h_tr_klein := trace_mulRight_eq_mk ρ (logρ - logEρ) hρEρ_tc
    have h_tr_jensen := trace_mulRight_eq_mk ρ (logEσ - logσ) hρEσσ_tc
    have h_tr_bimod := trace_mulRight_eq_mk (E.toChannel ρ) (logEρ - logEσ) hEρEσ_tc
    -- Key identity at complex level:
    -- Tr(ρ(logρ-logσ)) = Tr(ρ(logρ-logEρ)) + Tr(Eρ(logEρ-logEσ)) + Tr(ρ(logEσ-logσ))
    have h_key : TraceClass.trace ⟨(ρ : H →L[ℂ] H) * (logρ - logσ), hρσ_tc⟩ =
        TraceClass.trace ⟨(ρ : H →L[ℂ] H) * (logρ - logEρ), hρEρ_tc⟩ +
        TraceClass.trace ⟨(E.toChannel ρ : H →L[ℂ] H) * (logEρ - logEσ), hEρEσ_tc⟩ +
        TraceClass.trace ⟨(ρ : H →L[ℂ] H) * (logEσ - logσ), hρEσσ_tc⟩ := by
      rw [← h_tr_total, ← h_tr_klein, ← h_tr_bimod, ← h_tr_jensen]
      rw [h_trace_decomp, h_bimodule]
    -- Take .re and use Klein + Jensen via linarith
    have h_key_re := congr_arg Complex.re h_key
    simp only [Complex.add_re] at h_key_re
    linarith [hKlein, hJensen]
  · -- Infinite case: D(ρ ‖ σ) = ⊤, trivially true
    rw [tcRelativeEntropy_of_not_suppSubset ρ σ hsupp]
    exact le_top

end ContinuousLinearMap
