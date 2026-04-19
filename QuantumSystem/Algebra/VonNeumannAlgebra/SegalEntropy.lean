module

public import QuantumSystem.Analysis.Entropy.TraceClassRelativeEntropy
public import QuantumSystem.Algebra.VonNeumannAlgebra.NormalState
public import QuantumSystem.Channel.TraceClass

/-!
# Segal Entropy and Von Neumann Entropy for Trace-Class Operators

This file defines the von Neumann entropy for trace-class operators on an
infinite-dimensional Hilbert space and the Segal entropy for normal states on
von Neumann algebras, following Longo-Witten (2021).

## Main definitions

* `tcVonNeumannEntropy`: Von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` for positive
  trace-class operators.
* `VonNeumannAlgebra.segalEntropy`: Segal entropy `S_ω(ρ) = -(ω̃(ρ log ρ)).re` for a
  normal state `ω` on a von Neumann algebra and an element `ρ`.
* `VonNeumannAlgebra.NormalState.IsTracial`: Predicate for tracial normal states
  (`ω(xy) = ω(yx)`).

## Main results

* `tcVonNeumannEntropy_zero`: `S(0) = 0`.
* `segalEntropy_of_one`: `S_ω(1) = 0` (entropy of the identity element is zero).
* `segalEntropy_of_zero_elt`: `S_ω(0) = 0`.
* `tcVonNeumannEntropy_eq_neg_tcRelativeEntropy_one`: `S(ρ) = -D(ρ ‖ 1)` when the
  identity is trace-class (bridge lemma for finite-rank Hilbert spaces).

## Mathematical background

### Longo-Witten route

For a Type II₁ factor `(M, τ)` with faithful normal tracial state `τ`, and `φ = τ(ρ·)`,
Longo-Witten Proposition 2.4 identifies the relative modular operator as `Δ_{ξτ,ξφ} = ρ⁻¹`,
bypassing the full Tomita modular theory. The Segal entropy is then:

  `S_τ(φ) = -τ(ρ log ρ) = -S_Araki(φ ‖ τ)`

and monotonicity `S_τ(φ|_B) ≥ S_τ(φ)` follows from the data-processing inequality
for the conditional expectation `E_B : M → B`.

## References

* Longo, Witten. *An algebraic construction of boundary quantum field theory* (2021).
* Segal. *A note on the concept of entropy* (1960).
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace NNReal ContinuousFunctionalCalculus
open Complex

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Trace-class von Neumann entropy -/

/-- **Trace-class von Neumann entropy** `S(ρ) = -Tr(ρ log ρ)` for positive trace-class
operators. This is the infinite-dimensional analogue of `Matrix.vonNeumannEntropy`.
The operator logarithm is computed via `CFC.log` (i.e., `cfc Real.log`). -/
noncomputable def tcVonNeumannEntropy (ρ : TraceClass H)
    [TraceClass.HasLogTC ρ] : EReal :=
  ↑(-(TraceClass.trace ⟨TraceClass.mulLog ρ, TraceClass.HasLogTC.isTraceClass⟩).re)

/-- Von Neumann entropy of the zero operator is zero: `S(0) = 0`. -/
lemma tcVonNeumannEntropy_zero :
    let _ : TraceClass.HasLogTC (0 : TraceClass H) := by
      constructor
      change IsTraceClass ((0 : H →L[ℂ] H) * CFC.log (0 : H →L[ℂ] H))
      rw [zero_mul]; exact zero_isTraceClass
    tcVonNeumannEntropy (0 : TraceClass H) = 0 := by
  intro _
  unfold tcVonNeumannEntropy
  suffices h : TraceClass.trace ⟨TraceClass.mulLog (0 : TraceClass H),
      TraceClass.HasLogTC.isTraceClass⟩ = 0 by
    rw [h]; simp
  have h0 : (⟨TraceClass.mulLog (0 : TraceClass H),
      TraceClass.HasLogTC.isTraceClass⟩ : TraceClass H) = 0 := by
    ext x; change (TraceClass.mulLog (0 : TraceClass H)) x = 0
    change ((0 : H →L[ℂ] H) * CFC.log (0 : H →L[ℂ] H)) x = 0; simp
  rw [h0]
  unfold TraceClass.trace
  simp [inner_zero_right]

/-! ### Bridge: von Neumann entropy as negative relative entropy with identity

When the identity operator is trace-class (i.e., in finite-rank Hilbert spaces),
`S(ρ) = -D(ρ ‖ 1)`. This is the key connection between Segal entropy and the
data-processing inequality. -/

/-- When the identity is trace-class (finite-dimensional), the von Neumann entropy equals
the negative relative entropy against the identity: `S(ρ) = -D(ρ ‖ 1)`.

The condition `hI_tc` holds precisely when `H` is finite-dimensional. -/
lemma tcVonNeumannEntropy_eq_neg_tcRelativeEntropy_one
    (ρ : TraceClass H)
    (hI_tc : IsTraceClass (1 : H →L[ℂ] H))
    [TraceClass.HasLogTC ρ]
    [TraceClass.HasRelLogTC ρ ⟨1, hI_tc⟩]
    (hsupp : tcSuppSubset (ρ : H →L[ℂ] H) (1 : H →L[ℂ] H)) :
    tcVonNeumannEntropy ρ =
      -(@tcRelativeEntropy _ _ _ _ ρ ⟨1, hI_tc⟩ ‹_›) := by
  unfold tcVonNeumannEntropy tcRelativeEntropy
  simp only [hsupp, ↓reduceIte]
  -- CFC.log 1 = 0 by Mathlib
  have h_log1 : CFC.log (1 : H →L[ℂ] H) = 0 := CFC.log_one
  -- Therefore log ρ - log 1 = log ρ - 0 = log ρ
  have h_sub : CFC.log (ρ : H →L[ℂ] H) - CFC.log (1 : H →L[ℂ] H) =
      CFC.log (ρ : H →L[ℂ] H) := by rw [h_log1, sub_zero]
  -- The two trace-class operators agree
  have h_eq : (TraceClass.mk _ (TraceClass.HasRelLogTC.isTraceClass (ρ := ρ) (σ := ⟨1, hI_tc⟩)) :
      TraceClass H) =
      (TraceClass.mk _ (TraceClass.HasLogTC.isTraceClass (ρ := ρ)) : TraceClass H) := by
    ext x
    change ((ρ : H →L[ℂ] H) * (CFC.log (ρ : H →L[ℂ] H) - CFC.log (1 : H →L[ℂ] H))) x =
           ((ρ : H →L[ℂ] H) * CFC.log (ρ : H →L[ℂ] H)) x
    rw [h_sub]
  rw [h_eq]
  simp only [EReal.coe_neg]

/-- **Non-positivity of trace-class Von Neumann entropy** via Klein's inequality.

When the identity is trace-class (i.e., in a finite-dimensional Hilbert space)
and Klein's operator positivity holds (i.e., `0 ≤ ρ * (log ρ − log 1) = ρ * log ρ`),
we have `S(ρ) ≤ 0`.

Combined with `tcVonNeumannEntropy_eq_neg_tcRelativeEntropy_one`, this is:
  `S(ρ) = -D(ρ ‖ 1) ≤ 0` since `D(ρ ‖ 1) ≥ 0`. -/
theorem tcVonNeumannEntropy_le_zero
    (ρ : TraceClass H)
    (hI_tc : IsTraceClass (1 : H →L[ℂ] H))
    [TraceClass.IsNonneg ρ]
    [TraceClass.HasLogTC ρ]
    [TraceClass.HasRelLogTC ρ ⟨1, hI_tc⟩]
    (hsupp : tcSuppSubset (ρ : H →L[ℂ] H) (1 : H →L[ℂ] H))
    (hρI_pos : 0 ≤ TraceClass.logDiff ρ ⟨1, hI_tc⟩) :
    tcVonNeumannEntropy ρ ≤ 0 := by
  rw [tcVonNeumannEntropy_eq_neg_tcRelativeEntropy_one ρ hI_tc hsupp]
  rw [EReal.neg_le_zero]
  haveI : TraceClass.IsNonneg ⟨(1 : H →L[ℂ] H), hI_tc⟩ :=
    ⟨(nonneg_iff_isPositive _).mpr isPositive_one⟩
  exact tcRelativeEntropy_nonneg ρ ⟨1, hI_tc⟩ hρI_pos

end ContinuousLinearMap

/-! ## Segal entropy for von Neumann algebras -/

namespace VonNeumannAlgebra

open scoped InnerProductSpace NNReal ContinuousFunctionalCalculus
open ContinuousLinearMap Complex

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [WStarAlgebra (H →L[ℂ] H)]
variable (S : VonNeumannAlgebra H) (ω : NormalState S)

/-! ### Tracial normal states -/

/-- A normal state `ω` on a von Neumann algebra is **tracial** if `ω(xy) = ω(yx)` for all
elements `x, y`. In Type II₁ factors, the unique faithful normal tracial state is the
canonical trace. -/
def NormalState.IsTracial
    {S : VonNeumannAlgebra H} (ω : NormalState S) : Prop :=
  ∀ x y : S, ω (x * y) = ω (y * x)

/-! ### Segal entropy -/

/-- The self-log product `ρ · log ρ` for an element of a von Neumann algebra,
computed in `B(H)` via the continuous functional calculus. -/
noncomputable abbrev mulLog {S : VonNeumannAlgebra H} (ρ : S) : H →L[ℂ] H :=
  (ρ : H →L[ℂ] H) * CFC.log (ρ : H →L[ℂ] H)

/-- **Segal entropy** for an element of a von Neumann algebra with respect to a normal state.

For a von Neumann algebra `S ⊆ B(H)`, a normal state `ω` on `S`, and an element `ρ ∈ S`,
the Segal entropy is `S_ω(ρ) = -(ω̃(ρ log ρ)).re`, where `ω̃ = ω.extension` is the
normal extension to `B(H)`.

When `S` is a Type II₁ factor and `ω` is the unique tracial state `τ`, this recovers
the Segal entropy `S_τ(ρ) = -τ(ρ log ρ)` of Longo-Witten (2021), Proposition 2.4. -/
noncomputable def segalEntropy (ρ : S) : EReal :=
  ↑(-(ω.extension (mulLog ρ)).re)

/-- The Segal entropy of the identity element is zero: `S_ω(1) = 0`.

Since `log(1) = 0`, we get `1 · log(1) = 0`, and `ω̃(0) = 0`. -/
lemma segalEntropy_of_one :
    segalEntropy S ω (1 : S) = 0 := by
  unfold segalEntropy mulLog
  have h1 : ((1 : S) : H →L[ℂ] H) * CFC.log ((1 : S) : H →L[ℂ] H) = 0 := by
    have : ((1 : S) : H →L[ℂ] H) = 1 := rfl
    rw [this, CFC.log_one, mul_zero]
  rw [h1, map_zero, Complex.zero_re, neg_zero, EReal.coe_zero]

/-- The Segal entropy of the zero element is zero: `S_ω(0) = 0`. -/
lemma segalEntropy_of_zero :
    segalEntropy S ω (0 : S) = 0 := by
  unfold segalEntropy mulLog
  have h0 : ((0 : S) : H →L[ℂ] H) * CFC.log ((0 : S) : H →L[ℂ] H) = 0 :=
    zero_mul _
  rw [h0, map_zero, Complex.zero_re, neg_zero, EReal.coe_zero]

/-- When ρ ∈ S and CFC.log ρ ∈ S (functional calculus stays in the von Neumann algebra),
the Segal entropy can be computed using ω directly (without the extension). -/
lemma segalEntropy_eq_of_mem (ρ : S)
    (ρlogρ : S)
    (hρlogρ : (ρlogρ : H →L[ℂ] H) = mulLog ρ) :
    segalEntropy S ω ρ = ↑(-(ω ρlogρ).re) := by
  unfold segalEntropy
  congr 1; congr 1; congr 1
  rw [← hρlogρ, ω.extension_extends ρlogρ]

/-! ### Connection to GNS representation

The GNS construction (in `GNS.Construction`) provides:
- Hilbert space `Hω` as completion of `A / ker(ω)`
- Representation `πω : A → B(Hω)` with `πω(ab) = πω(a) ∘ πω(b)`
- Cyclic vector `ξω ∈ Hω` with `ω(a) = ⟨ξω, πω(a) ξω⟩`
  (proved as `GNS.Construction.state_recovery`)

When `ρ ∈ S` and `ρ log ρ ∈ S`, the Segal entropy becomes:
  `S_ω(ρ) = -(⟨ξω, πω(ρ log ρ) ξω⟩).re`
via the state recovery formula. This connects the algebraic entropy definition
to the Hilbert-space inner product, which is the starting point for the
Longo-Witten monotonicity proof via modular theory. -/

/-! ### Monotonicity of Segal entropy under conditional expectations

The key result: for a conditional expectation `E : M → N ⊆ M` and a tracial
normal state `τ`, the Segal entropy is monotone:

  `S_τ(ρ|_N) ≥ S_τ(ρ)`, equivalently `S_τ(E(ρ)) ≥ S_τ(ρ)`.

**Proof strategy (Longo-Witten route)**:

  `τ(ρ log ρ) - τ(E(ρ) log E(ρ))`
  `= τ(ρ log ρ - ρ log E(ρ)) + τ(ρ log E(ρ) - E(ρ) log E(ρ))`
  `= D_τ(ρ, E(ρ)) + 0`
  `≥ 0`

where:
- `D_τ(ρ, E(ρ)) = τ(ρ(log ρ - log E(ρ))) ≥ 0` by Klein's inequality.
- The second term vanishes by the bimodule property:
  `τ(ρ · log E(ρ)) = τ(E(ρ · log E(ρ))) = τ(E(ρ) · log E(ρ))`
  using `τ ∘ E = τ` and `E(x · b) = E(x) · b` for `b ∈ N`. -/

/-- **Monotonicity of Segal entropy under conditional expectations.**

For a von Neumann algebra `M` with subalgebra `N ⊆ M`, a tracial normal state `ω`,
and a conditional expectation `E : M → N`, the Segal entropy is monotone:
`S_ω(E(ρ)) ≥ S_ω(ρ)`.

This is the trace-level formulation. The hypotheses encode:
- `ρ_tc`: the trace-class representative of `ρ`
- `E` : conditional expectation with bimodule property
- `hKlein`: the Klein inequality `ω̃(ρ(log ρ - log E(ρ))) ≥ 0`
- `hbimodule`: the bimodule trace identity `ω̃(ρ · log E(ρ)) = ω̃(E(ρ) · log E(ρ))`

Together these give the monotonicity. -/
theorem segalEntropy_mono_of_subalgebra
    (M N : VonNeumannAlgebra H)
    (ω : NormalState M)
    (ωN : NormalState N)
    (ρ : M) (Eρ : N)
    -- Klein inequality: the relative entropy term is non-negative
    (hKlein :
      (ω.extension (mulLog ρ)).re -
      (ω.extension ((ρ : H →L[ℂ] H) * CFC.log (Eρ : H →L[ℂ] H))).re ≥ 0)
    -- Bimodule identity: τ(ρ · log E(ρ)) = τ(E(ρ) · log E(ρ))
    (hbimodule :
      (ω.extension ((ρ : H →L[ℂ] H) * CFC.log (Eρ : H →L[ℂ] H))).re =
      (ω.extension (mulLog Eρ)).re)
    -- The extension agrees on N elements
    (hEρ_ext :
      (ωN.extension (mulLog Eρ)).re =
      (ω.extension (mulLog Eρ)).re) :
    segalEntropy N ωN Eρ ≥ segalEntropy M ω ρ := by
  unfold segalEntropy mulLog
  simp only [EReal.coe_le_coe_iff, neg_le_neg_iff]
  -- Need: (ω̃(ρ · log ρ)).re ≥ (ω̃N(Eρ · log Eρ)).re
  rw [hEρ_ext]
  -- Now: (ω̃(ρ · log ρ)).re ≥ (ω̃(Eρ · log Eρ)).re
  -- From Klein: (ω̃(ρ · log ρ)).re - (ω̃(ρ · log Eρ)).re ≥ 0
  -- From bimodule: (ω̃(ρ · log Eρ)).re = (ω̃(Eρ · log Eρ)).re
  linarith [hKlein, hbimodule]

section CondExpMonotonicity

variable (M N : VonNeumannAlgebra H)
    (E : ContinuousLinearMap.ConditionalExpectation H M N)
    (ω : NormalState M) (ωN : NormalState N)
    [ω.IsTraceExtension] [ωN.IsTraceExtension]
    (ρ : M) (ρ_tc : TraceClass H)
    (hρ_tc : (ρ_tc : H →L[ℂ] H) = (ρ : H →L[ℂ] H))
    (hlog_N : CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H) ∈ N.carrier)

include hρ_tc hlog_N

/-- **Monotonicity of Segal entropy via conditional expectation.**

This strengthens `segalEntropy_mono_of_subalgebra` by deriving the bimodule
identity from a `ConditionalExpectation` structure and the `IsTraceExtension`
instances (which state that the normal extensions agree with `TraceClass.trace`).

The bimodule identity `ω̃(ρ · log E(ρ)) = ω̃(E(ρ) · log E(ρ))` is proved as:
1. `ω̃(A) = Tr(A)` for trace-class `A` (from `IsTraceExtension`).
2. `Tr(ρ · log E(ρ)) = Tr(E(ρ) · log E(ρ))` by
   `ConditionalExpectation.trace_mulRight_eq` with `b = CFC.log E(ρ) ∈ N`.

This applies to the Type II₁ factor setting where `ω = τ` is the
faithful normal tracial state, for which `τ̃(A) = Tr(A)`. -/
theorem segalEntropy_mono_of_condExp
    (hKlein :
      (ω.extension (mulLog ρ)).re -
      (ω.extension ((ρ : H →L[ℂ] H) * CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H))).re ≥ 0) :
    segalEntropy N ωN (E.applyVNA ρ_tc) ≥ segalEntropy M ω ρ := by
  -- Derive the bimodule identity from ConditionalExpectation properties
  have hbimodule :
      (ω.extension ((ρ : H →L[ℂ] H) * CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H))).re =
      (ω.extension ((E.applyVNA ρ_tc : H →L[ℂ] H) *
        CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H))).re := by
    set logEρ := CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H)
    have h_mul_ρ : (ρ : H →L[ℂ] H) * logEρ =
        (TraceClass.mulRight ρ_tc logEρ : H →L[ℂ] H) := by
      change (ρ : H →L[ℂ] H) * logEρ = ρ_tc.toFun * logEρ; rw [hρ_tc]
    have eq_lhs : ω.extension ((ρ : H →L[ℂ] H) * logEρ) =
        TraceClass.trace (TraceClass.mulRight ρ_tc logEρ) := by
      rw [h_mul_ρ]; exact NormalState.IsTraceExtension.extension_eq_trace (ω := ω) _
    have eq_rhs : ω.extension ((E.applyVNA ρ_tc : H →L[ℂ] H) * logEρ) =
        TraceClass.trace (TraceClass.mulRight (E.toChannel ρ_tc) logEρ) := by
      change ω.extension (TraceClass.mulRight (E.toChannel ρ_tc) logEρ : H →L[ℂ] H) = _
      exact NormalState.IsTraceExtension.extension_eq_trace (ω := ω) _
    rw [eq_lhs, eq_rhs]
    exact congr_arg Complex.re (E.trace_mulRight_eq ρ_tc logEρ hlog_N)
  -- Derive extension agreement from IsTraceExtension
  have hEρ_ext :
      (ωN.extension ((E.applyVNA ρ_tc : H →L[ℂ] H) *
        CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H))).re =
      (ω.extension ((E.applyVNA ρ_tc : H →L[ℂ] H) *
        CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H))).re := by
    have h_tc : (E.applyVNA ρ_tc : H →L[ℂ] H) * CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H) =
        (TraceClass.mulRight (E.toChannel ρ_tc)
          (CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H)) : H →L[ℂ] H) := rfl
    rw [h_tc, NormalState.IsTraceExtension.extension_eq_trace (ω := ωN),
        NormalState.IsTraceExtension.extension_eq_trace (ω := ω)]
  exact segalEntropy_mono_of_subalgebra M N ω ωN ρ (E.applyVNA ρ_tc)
    hKlein hbimodule hEρ_ext

/-- **Monotonicity of Segal entropy — fully assembled.**

This is the main monotonicity theorem, eliminating all abstract trace-identity
hypotheses (Klein, bimodule, extension agreement) in favor of concrete
operator-level conditions:

- **Klein**: derived from `trace_re_nonneg_of_nonneg` + `hρEρ_pos`
- **Bimodule**: derived from `ConditionalExpectation.trace_mulRight_eq` + `hlog_N`
- **Extension agreement**: derived from `IsTraceExtension` instances

Remaining hypotheses are:
1. Structural: von Neumann algebras M ⊇ N, conditional expectation E, states ω/ωN
2. Trace-class data: ρ_tc representing ρ, connected via hρ_tc
3. Positivity: the operator-level Klein inequality `ρ(log ρ − log Eρ) ≥ 0`
4. CFC.log Eρ ∈ N: the functional calculus preserves the subalgebra -/
theorem segalEntropy_mono
    [TraceClass.HasRelLogTC ρ_tc (E.toChannel ρ_tc)]
    (hρEρ_pos : 0 ≤ TraceClass.logDiff ρ_tc (E.toChannel ρ_tc)) :
    segalEntropy N ωN (E.applyVNA ρ_tc) ≥ segalEntropy M ω ρ := by
  -- Derive the Klein inequality from trace_re_nonneg_of_nonneg
  have hKlein :
      (ω.extension ((ρ : H →L[ℂ] H) * CFC.log (ρ : H →L[ℂ] H))).re -
      (ω.extension ((ρ : H →L[ℂ] H) *
        CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H))).re ≥ 0 := by
    set relEnt : TraceClass H :=
      ⟨TraceClass.logDiff ρ_tc (E.toChannel ρ_tc),
       TraceClass.HasRelLogTC.isTraceClass⟩
    have h_rel_op : (ρ : H →L[ℂ] H) * CFC.log (ρ : H →L[ℂ] H) -
        (ρ : H →L[ℂ] H) * CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H) =
        (relEnt : H →L[ℂ] H) := by
      change (ρ : H →L[ℂ] H) * CFC.log (ρ : H →L[ℂ] H) -
          (ρ : H →L[ℂ] H) * CFC.log (E.toChannel ρ_tc : H →L[ℂ] H) = _
      simp only [relEnt, ← mul_sub, ← hρ_tc]
    have h_re_eq :
        (ω.extension ((ρ : H →L[ℂ] H) * CFC.log (ρ : H →L[ℂ] H))).re -
        (ω.extension ((ρ : H →L[ℂ] H) *
          CFC.log (E.applyVNA ρ_tc : H →L[ℂ] H))).re =
        (TraceClass.trace relEnt).re := by
      rw [← Complex.sub_re, ← map_sub, h_rel_op,
          NormalState.IsTraceExtension.extension_eq_trace (ω := ω)]
    linarith [h_re_eq, TraceClass.trace_re_nonneg_of_nonneg relEnt hρEρ_pos]
  exact segalEntropy_mono_of_condExp M N E ω ωN ρ ρ_tc hρ_tc hlog_N hKlein

end CondExpMonotonicity

/-! ### Non-positivity of Segal entropy

The Segal entropy `S_ω(ρ) ≤ 0` under the natural condition that the
normal state extension evaluates `ρ log ρ` to a value with non-negative real part.

In the Type II₁ factor setting with tracial state `τ` and `τ(ρ) = τ(1) = 1`,
this follows from Klein's trace-level inequality:
  `τ(ρ log ρ) = D_τ(ρ, 1) ≥ τ(ρ - 1) = 0`.

The abstract version below takes the non-negativity of `Re(ω̃(ρ log ρ))` as a hypothesis,
which can be derived from:
- Klein's inequality when `ω` is tracial and `ω(ρ) = ω(1)`, or
- Operator positivity `0 ≤ ρ * CFC.log ρ` when combined with positivity of `ω̃`. -/

/-- **Non-positivity of Segal entropy.**

`S_ω(ρ) ≤ 0` when `Re(ω̃(ρ log ρ)) ≥ 0`.

This is the abstract version; in the Type II₁ factor setting with `τ(ρ) = τ(1) = 1`,
the hypothesis follows from Klein's trace inequality `τ(ρ log ρ) ≥ τ(ρ - 1) = 0`. -/
theorem segalEntropy_le_zero (ρ : S)
    (h_re_nonneg : 0 ≤ (ω.extension (mulLog ρ)).re) :
    segalEntropy S ω ρ ≤ 0 := by
  unfold segalEntropy mulLog
  rw [EReal.coe_nonpos]
  linarith

section TraceExtensionEntropy

variable [ω.IsTraceExtension] (ρ : S)
    (ρlogρ_tc : TraceClass H)
    (hρlogρ : (ρlogρ_tc : H →L[ℂ] H) = mulLog ρ)
    (hρlogρ_pos : 0 ≤ (ρlogρ_tc : H →L[ℂ] H))

include ρlogρ_tc hρlogρ hρlogρ_pos

/-- **Non-positivity from trace and operator positivity.**

When `ω̃ = Tr` on trace-class operators and `ρ log ρ ≥ 0`, the Segal entropy
is non-positive. This applies when `ρ` has spectrum in `[1, ∞) ∪ {0}`. -/
theorem segalEntropy_le_zero_of_trace :
    segalEntropy S ω ρ ≤ 0 := by
  apply segalEntropy_le_zero
  rw [← hρlogρ, NormalState.IsTraceExtension.extension_eq_trace]
  exact TraceClass.trace_re_nonneg_of_nonneg ρlogρ_tc hρlogρ_pos

/-! ### Equality condition for Segal entropy

The Segal entropy `S_ω(ρ) = 0` iff `ρ log ρ = 0` (when `ω̃ = Tr` and `ρ log ρ ≥ 0`).

The condition `ρ log ρ = 0` characterizes operators whose spectrum is contained in
`{0, 1}`, i.e., orthogonal projections. In the Type II₁ setting where `ρ` is a density
matrix (`Tr(ρ) = 1`) and `ω = τ` is the tracial state, `S_τ(ρ) = 0 ↔ ρ = 1`. -/

/-- **Equality condition for Segal entropy.**

`S_ω(ρ) = 0 ↔ ρ log ρ = 0` when `ω̃ = Tr` on trace-class elements and `ρ log ρ ≥ 0`.

The forward direction uses: `S_ω(ρ) = 0` ⟹ `Tr(ρ log ρ).re = 0` ⟹ `ρ log ρ = 0`
(positive trace-class with zero trace is zero).

The backward direction: `ρ log ρ = 0` ⟹ `ω̃(0) = 0` ⟹ `S_ω(ρ) = 0`. -/
theorem segalEntropy_eq_zero_iff :
    segalEntropy S ω ρ = 0 ↔ mulLog ρ = 0 := by
  constructor
  · -- Forward: S_ω(ρ) = 0 → ρ log ρ = 0
    intro h
    unfold segalEntropy at h
    rw [EReal.coe_eq_zero, neg_eq_zero] at h
    rw [← hρlogρ, NormalState.IsTraceExtension.extension_eq_trace] at h
    have h_zero := ContinuousLinearMap.nonneg_traceClass_eq_zero_of_trace_re_eq_zero
      ρlogρ_tc hρlogρ_pos h
    rw [← hρlogρ]; exact h_zero
  · -- Backward: ρ log ρ = 0 → S_ω(ρ) = 0
    intro h
    unfold segalEntropy
    rw [show mulLog ρ = 0 from h, map_zero, Complex.zero_re, neg_zero, EReal.coe_zero]

end TraceExtensionEntropy

end VonNeumannAlgebra
