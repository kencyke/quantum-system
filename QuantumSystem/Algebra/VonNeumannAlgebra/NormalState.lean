module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Basic
public import QuantumSystem.Analysis.CFC.TraceClass.Basic

@[expose] public section

namespace WStarAlgebra

variable (M : Type*) [CStarAlgebra M] [WStarAlgebra M]

/-! ### The predual of a W*-algebra -/

/-- The predual of a W*-algebra, extracted from `WStarAlgebra.exists_predual`.

For a W*-algebra M, the predual M_* is (classically) unique up to isometric isomorphism,
and satisfies M ≅ (M_*)*.

In this file we pick a specific witness using choice, and define "normal functionals"
to mean those coming from this chosen predual.
-/
noncomputable def Predual : Type _ :=
  (WStarAlgebra.exists_predual (M := M)).choose

noncomputable instance Predual.instNormedAddCommGroup : NormedAddCommGroup (Predual M) :=
  (WStarAlgebra.exists_predual (M := M)).choose_spec.choose

noncomputable instance Predual.instNormedSpace : NormedSpace ℂ (Predual M) :=
  (WStarAlgebra.exists_predual (M := M)).choose_spec.choose_spec.choose

noncomputable instance Predual.instCompleteSpace : CompleteSpace (Predual M) :=
  (WStarAlgebra.exists_predual (M := M)).choose_spec.choose_spec.choose_spec.choose

/-- The isometric *-isomorphism between the dual of the predual and the W*-algebra.

This witnesses that M is the dual of its predual: M ≅ (M_*)*.
Note: `StrongDual ℂ X` is an abbreviation for `X →L[ℂ] ℂ`.
-/
noncomputable def predualDualEquiv : (Predual M →L[ℂ] ℂ) ≃ₗᵢ⋆[ℂ] M :=
  (WStarAlgebra.exists_predual (M := M)).choose_spec.choose_spec.choose_spec.choose_spec.some

/-- The evaluation pairing between the predual and the algebra.

For x ∈ M_* and m ∈ M, this gives ⟨x, m⟩ := (predualDualEquiv⁻¹ m)(x).
This views m ∈ M ≅ (M_*)* as a functional on M_* and evaluates it at x.
-/
noncomputable def predualPairing (x : Predual M) (m : M) : ℂ :=
  (predualDualEquiv M).symm m x

/-- A linear functional on a W*-algebra is **normal** if it belongs to the predual.

Mathematically, f : M → ℂ is normal iff f ∈ M_*, i.e., there exists x ∈ M_* such that
for all m ∈ M, f(m) = ⟨x, m⟩ where ⟨·,·⟩ is the predual pairing.

This file *defines* normality via the predual. Classically, this is equivalent to (and
often *characterizes* normal functionals as):
- f is σ-weak (ultraweak) continuous
- f preserves suprema of increasing nets of positive operators
-/
def IsNormal (f : M →L[ℂ] ℂ) : Prop :=
  ∃ x : Predual M, ∀ m : M, f m = predualPairing M x m

end WStarAlgebra

namespace WStarAlgebra

variable (M : Type*) [CStarAlgebra M] [WStarAlgebra M]

/-! ### Normal states on W*-algebras -/

/-- A normal state on a W*-algebra is a positive, normalized *normal* functional. -/
structure NormalState where
  /-- The underlying continuous linear functional. -/
  toLinearMap : M →L[ℂ] ℂ
  /-- Positivity: on elements of the form `x†x`, the value is a nonnegative real. -/
  positive : ∀ x : M, ∃ r : NNReal, toLinearMap (star x * x) = ↑(r : ℝ)
  /-- The state evaluates to 1 on the identity. -/
  unit : toLinearMap 1 = 1
  /-- Normality: the functional belongs to the predual. -/
  normal : IsNormal (M := M) toLinearMap

end WStarAlgebra

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A `VonNeumannAlgebra` is a module over `ℂ` (inherited from the underlying StarSubalgebra). -/
instance instModule (S : VonNeumannAlgebra H) : Module ℂ S :=
  S.toStarSubalgebra.instModuleSubtypeMem

/-! ### Normal states on von Neumann algebras -/

/-- A normal state on a von Neumann algebra `S ⊆ B(H)` is a positive, normalized
linear functional on `S` that extends to a **normal** functional on `B(H)`.

This matches the standard definition: normality is encoded by belonging to the
predual of `B(H)` (i.e., σ-weak continuity).
-/
structure NormalState (S : VonNeumannAlgebra H) [WStarAlgebra (H →L[ℂ] H)] where
  /-- The underlying continuous linear functional on the von Neumann algebra. -/
  toLinearMap : S →L[ℂ] ℂ
  /-- Positivity: on elements of the form `x†x`, the value is a nonnegative real. -/
  positive : ∀ x : S, ∃ r : NNReal, toLinearMap (star x * x) = ↑(r : ℝ)
  /-- The state evaluates to 1 on the identity. -/
  unit : toLinearMap 1 = 1
  /-- There exists a normal extension to `B(H)` (in the predual sense). -/
  normal :
    ∃ (f : (H →L[ℂ] H) →L[ℂ] ℂ),
      WStarAlgebra.IsNormal (M := H →L[ℂ] H) f ∧
        ∀ x : S, toLinearMap x = f (x : H →L[ℂ] H)

namespace NormalState

variable {S : VonNeumannAlgebra H} [WStarAlgebra (H →L[ℂ] H)]

instance : FunLike (NormalState S) S ℂ where
  coe ω := ω.toLinearMap
  coe_injective' ω₁ ω₂ h := by
    cases ω₁
    cases ω₂
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (NormalState S) ℂ S ℂ where
  map_add ω := ω.toLinearMap.map_add
  map_smulₛₗ ω := ω.toLinearMap.map_smul

@[simp]
lemma toLinearMap_apply (ω : NormalState S) (x : S) : ω.toLinearMap x = ω x := rfl

@[ext]
lemma ext {ω₁ ω₂ : NormalState S} (h : ∀ x, ω₁ x = ω₂ x) : ω₁ = ω₂ :=
  DFunLike.ext ω₁ ω₂ h

/-- A normal state evaluates to 1 on the identity. -/
@[simp]
lemma apply_one (ω : NormalState S) : ω 1 = 1 := ω.unit

/-- A normal state is positive: `ω(x* x) ≥ 0`. -/
lemma apply_star_self_nonneg (ω : NormalState S) (x : S) :
    ∃ r : NNReal, ω (star x * x) = ↑(r : ℝ) :=
  ω.positive x

/-- The normal extension of a state to `B(H)`. -/
noncomputable def extension (ω : NormalState S) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  ω.normal.choose

lemma extension_isNormal (ω : NormalState S) :
    WStarAlgebra.IsNormal (M := H →L[ℂ] H) ω.extension :=
  ω.normal.choose_spec.1

lemma extension_extends (ω : NormalState S) (x : S) : ω.extension (x : H →L[ℂ] H) = ω x :=
  (ω.normal.choose_spec.2 x).symm

/-- A normal state whose extension agrees with the trace on all trace-class operators.
In the Type II₁ factor setting, the tracial state `τ` satisfies this. -/
class IsTraceExtension (ω : NormalState S) : Prop where
  extension_eq_trace : ∀ (T : ContinuousLinearMap.TraceClass H),
    ω.extension (T : H →L[ℂ] H) = ContinuousLinearMap.TraceClass.trace T

/-- Two `IsTraceExtension` states agree on trace-class operators. -/
lemma IsTraceExtension.extensions_agree
    {S₁ S₂ : VonNeumannAlgebra H}
    {ω₁ : NormalState S₁} {ω₂ : NormalState S₂}
    [ω₁.IsTraceExtension] [ω₂.IsTraceExtension]
    (T : ContinuousLinearMap.TraceClass H) :
    ω₁.extension (T : H →L[ℂ] H) = ω₂.extension (T : H →L[ℂ] H) := by
  rw [IsTraceExtension.extension_eq_trace, IsTraceExtension.extension_eq_trace]

end NormalState

end VonNeumannAlgebra
