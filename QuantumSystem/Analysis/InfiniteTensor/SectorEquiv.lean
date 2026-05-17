module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import QuantumSystem.Analysis.InfiniteTensor.Product
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.C0Triangle

/-!
# Sector equivalence relations on unit-vector families

For a Hilbert family `H : ι → Type*` and unit-vector reference families
`Ω, Ω' : UnitFamily H`, we introduce the standard hierarchy of equivalence
relations following Bratteli–Robinson Vol. 2 §2.7.2 / Naaijkens 2012 §3.5.

```
referenceRel Ω Ω' iff  Ω i = Ω' i for all but finitely many i
strongRel    Ω Ω' iff  Σ_i ‖Ω i - Ω' i‖² < ∞
c0Rel        Ω Ω' iff  Σ_i (1 - ‖⟪Ω i, Ω' i⟫_ℂ‖) < ∞     (Bratteli–Robinson C₀)
```

Each is bundled into a `Setoid` `referenceEquiv`, `strongEquiv`, `c0Equiv`.
The `c0Equiv` Setoid is the canonical Bratteli–Robinson sector relation: the
BR sector decomposition Hilbert space (defined later, once `ITPSector` is
available) is indexed by `c0Equiv`-classes.

## Inclusion chain

The following inclusions hold and are proved here:

* `referenceRel ⊆ strongRel` — finite support implies `ℓ²` summability.
* `strongRel ⊆ c0Rel` — via the unit-vector bound
  `1 - ‖⟪u, v⟫_ℂ‖ ≤ ‖u - v‖² / 2`, which follows from `Re z ≤ ‖z‖`.
* `cRel ⊆ c0Rel` — via the inequality `‖1 - z‖ ≥ 1 - ‖z‖` for `‖z‖ ≤ 1`.

The von Neumann `C`-relation `cRel Ω Ω' iff Σ_i ‖1 - ⟪Ω i, Ω' i⟫_ℂ‖ < ∞` is
defined here, and the inclusion `cRel ⊆ c0Rel` is proved.  Its `Setoid`
transitivity is deferred: the proof requires the orthogonal-decomposition
identity `⟪a, c⟫ - ⟪a, b⟫⟪b, c⟫ = ⟪a⊥, c⊥⟫` for unit `b`, which is heavier
than the C₀-version available from `ForMathlib.c0_triangle`.

## On the plan's `strongRel ⊆ cRel` claim

The migration plan `infinite-tensor-product.md` lists the chain
`referenceRel ⊆ strongRel ⊆ cRel ⊆ c0Rel`.  The intermediate link
`strongRel ⊆ cRel` does **not** hold in general:  for unit `b i` and a
phase rotation `Ω' i := exp(i θ_i) • b i` with `θ_i = 1/i`, one has
`‖Ω i - Ω' i‖² ≍ θ_i² ∈ ℓ¹` (so `strongRel` holds) while
`‖1 - ⟪Ω i, Ω' i⟫_ℂ‖ ≍ |θ_i| ∉ ℓ¹` (so `cRel` fails).  The mathematical
content is therefore the *parallel* inclusion structure documented above:
`strongRel` and `cRel` are two strictly finer refinements of `c0Rel`,
neither implying the other.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* `QuantumSystem/ForMathlib/Analysis/InnerProductSpace/C0Triangle.lean` —
  the C₀-triangle inequality.
-/

@[expose] public section

open scoped InnerProductSpace

namespace InfiniteTensor

namespace UnitFamily

/-! ### `referenceRel` / `referenceEquiv` — agreement off a finite set -/

section ReferenceRel

variable {ι : Type*} {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]

/-- The "agreement off a finite set" relation: `Ω` and `Ω'` differ at only
finitely many indices. -/
def referenceRel (Ω Ω' : UnitFamily H) : Prop :=
  Set.Finite { i : ι | (Ω i : H i) ≠ Ω' i }

theorem referenceRel.refl (Ω : UnitFamily H) : referenceRel Ω Ω := by
  change Set.Finite _
  simp only [ne_eq, not_true_eq_false, Set.setOf_false, Set.finite_empty]

theorem referenceRel.symm {Ω Ω' : UnitFamily H} (h : referenceRel Ω Ω') :
    referenceRel Ω' Ω := by
  change Set.Finite _
  have heq : { i : ι | (Ω' i : H i) ≠ Ω i }
      = { i : ι | (Ω i : H i) ≠ Ω' i } := by
    ext i; exact ⟨fun hi heq => hi heq.symm, fun hi heq => hi heq.symm⟩
  rw [heq]; exact h

theorem referenceRel.trans {Ω Ω' Ω'' : UnitFamily H}
    (h₁ : referenceRel Ω Ω') (h₂ : referenceRel Ω' Ω'') :
    referenceRel Ω Ω'' := by
  change Set.Finite _
  refine (h₁.union h₂).subset ?_
  intro i hi
  rw [Set.mem_setOf_eq, ne_eq] at hi
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  by_contra hns
  push Not at hns
  exact hi (hns.1.trans hns.2)

/-- The "agreement off a finite set" Setoid on unit-vector families. -/
def referenceEquiv : Setoid (UnitFamily H) where
  r := referenceRel
  iseqv := ⟨referenceRel.refl, referenceRel.symm, referenceRel.trans⟩

end ReferenceRel

/-! ### `strongRel` / `strongEquiv` — `ℓ²` summable difference -/

section StrongRel

variable {ι : Type*} {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]

/-- The strong (ℓ²) relation on unit-vector families. -/
def strongRel (Ω Ω' : UnitFamily H) : Prop :=
  Summable fun i : ι => ‖(Ω i : H i) - Ω' i‖ ^ 2

theorem strongRel.refl (Ω : UnitFamily H) : strongRel Ω Ω := by
  change Summable _
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  exact summable_zero

theorem strongRel.symm {Ω Ω' : UnitFamily H} (h : strongRel Ω Ω') :
    strongRel Ω' Ω := by
  change Summable _
  have hpt : (fun i : ι => ‖(Ω' i : H i) - Ω i‖ ^ 2)
      = fun i => ‖(Ω i : H i) - Ω' i‖ ^ 2 := by
    funext i; rw [norm_sub_rev]
  rw [hpt]; exact h

theorem strongRel.trans {Ω Ω' Ω'' : UnitFamily H}
    (h₁ : strongRel Ω Ω') (h₂ : strongRel Ω' Ω'') :
    strongRel Ω Ω'' := by
  change Summable _
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?bound
    ((h₁.mul_left 2).add (h₂.mul_left 2))
  intro i
  have hT : ‖(Ω i : H i) - Ω'' i‖
      ≤ ‖(Ω i : H i) - Ω' i‖ + ‖(Ω' i : H i) - Ω'' i‖ := by
    have hsplit : (Ω i : H i) - Ω'' i
        = ((Ω i : H i) - Ω' i) + ((Ω' i : H i) - Ω'' i) :=
      (sub_add_sub_cancel _ _ _).symm
    rw [hsplit]
    exact norm_add_le _ _
  have hsq : ‖(Ω i : H i) - Ω'' i‖ ^ 2
      ≤ (‖(Ω i : H i) - Ω' i‖ + ‖(Ω' i : H i) - Ω'' i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hT 2
  nlinarith [sq_nonneg
    (‖(Ω i : H i) - Ω' i‖ - ‖(Ω' i : H i) - Ω'' i‖)]

/-- The strong (ℓ²) Setoid on unit-vector families. -/
def strongEquiv : Setoid (UnitFamily H) where
  r := strongRel
  iseqv := ⟨strongRel.refl, strongRel.symm, strongRel.trans⟩

/-- Agreement off a finite set implies `ℓ²` summability of the per-site
difference, since the relevant sequence vanishes off a finite set. -/
theorem referenceRel_le_strongRel {Ω Ω' : UnitFamily H}
    (h : referenceRel Ω Ω') : strongRel Ω Ω' := by
  change Summable _
  refine summable_of_ne_finset_zero (s := h.toFinset) ?_
  intro i hi
  have hagree : (Ω i : H i) = Ω' i := by
    by_contra hne
    apply hi
    exact Set.Finite.mem_toFinset h |>.mpr hne
  rw [hagree, sub_self, norm_zero]
  simp

end StrongRel

/-! ### `c0Rel` / `c0Equiv` — Bratteli–Robinson canonical sector relation -/

section C0Rel

variable {ι : Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]

/-- The Bratteli–Robinson C₀ relation on unit-vector families. -/
def c0Rel (Ω Ω' : UnitFamily H) : Prop :=
  Summable fun i : ι => 1 - ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖

theorem c0Rel.refl (Ω : UnitFamily H) : c0Rel Ω Ω := by
  change Summable _
  have h0 : ∀ i : ι, 1 - ‖⟪(Ω i : H i), Ω i⟫_ℂ‖ = 0 := by
    intro i
    have hnorm : ‖(Ω i : H i)‖ = 1 := Ω.norm_apply i
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  simp_rw [h0]
  exact summable_zero

theorem c0Rel.symm {Ω Ω' : UnitFamily H} (h : c0Rel Ω Ω') : c0Rel Ω' Ω := by
  change Summable _
  have hpt : (fun i : ι => 1 - ‖⟪(Ω' i : H i), Ω i⟫_ℂ‖)
      = fun i => 1 - ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖ := by
    funext i
    rw [← inner_conj_symm (𝕜 := ℂ), RCLike.norm_conj]
  rw [hpt]; exact h

theorem c0Rel.trans {Ω Ω' Ω'' : UnitFamily H}
    (h₁ : c0Rel Ω Ω') (h₂ : c0Rel Ω' Ω'') : c0Rel Ω Ω'' := by
  change Summable _
  refine Summable.of_nonneg_of_le ?nonneg ?bound
    ((h₁.mul_left 2).add (h₂.mul_left 2))
  · intro i
    have hub : ‖⟪(Ω i : H i), Ω'' i⟫_ℂ‖ ≤ 1 := by
      calc ‖⟪(Ω i : H i), Ω'' i⟫_ℂ‖
          ≤ ‖(Ω i : H i)‖ * ‖(Ω'' i : H i)‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [Ω.norm_apply i, Ω''.norm_apply i]; ring
    linarith
  · intro i
    exact ForMathlib.c0_triangle (Ω i) (Ω' i) (Ω'' i)
      (Ω.norm_apply i) (Ω'.norm_apply i) (Ω''.norm_apply i)

/-- The Bratteli–Robinson C₀ Setoid on unit-vector families.

This is the canonical sector relation: the BR sector decomposition Hilbert
space is indexed by `c0Equiv`-classes. -/
def c0Equiv : Setoid (UnitFamily H) where
  r := c0Rel
  iseqv := ⟨c0Rel.refl, c0Rel.symm, c0Rel.trans⟩

/-- Strong (`ℓ²`) equivalence implies the canonical Bratteli–Robinson
C₀-relation, via the pointwise bound `1 - ‖⟪u, v⟫_ℂ‖ ≤ ‖u - v‖² / 2` for
unit vectors (which follows from `Re z ≤ ‖z‖`). -/
theorem strongRel_le_c0Rel {Ω Ω' : UnitFamily H}
    (h : strongRel Ω Ω') : c0Rel Ω Ω' := by
  change Summable _
  refine Summable.of_nonneg_of_le ?nonneg ?bound (h.mul_left (1 / 2))
  · intro i
    have hub : ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖ ≤ 1 := by
      calc ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖
          ≤ ‖(Ω i : H i)‖ * ‖(Ω' i : H i)‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [Ω.norm_apply i, Ω'.norm_apply i]; ring
    linarith
  · intro i
    have hsub : ‖(Ω i : H i) - Ω' i‖ ^ 2
        = 2 - 2 * RCLike.re ⟪(Ω i : H i), Ω' i⟫_ℂ := by
      rw [@norm_sub_sq ℂ _ _ _ _ (Ω i) (Ω' i), Ω.norm_apply i, Ω'.norm_apply i]
      ring
    have hre_le_abs :
        RCLike.re ⟪(Ω i : H i), Ω' i⟫_ℂ ≤ ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖ :=
      RCLike.re_le_norm _
    linarith

/-- `referenceRel ⊆ c0Rel`, via the chain
`referenceRel ⊆ strongRel ⊆ c0Rel`. -/
theorem referenceRel_le_c0Rel {Ω Ω' : UnitFamily H}
    (h : referenceRel Ω Ω') : c0Rel Ω Ω' :=
  strongRel_le_c0Rel (referenceRel_le_strongRel h)

/-! ### `cRel` — von Neumann's `C`-relation (without Setoid structure) -/

/-- The von Neumann C-relation on unit-vector families: `Ω ≈ Ω'` iff
`Σ_i ‖1 - ⟪Ω i, Ω' i⟫_ℂ‖ < ∞`.

Strictly finer than `c0Rel`; not comparable to `strongRel` (see the module
docstring for the phase-rotation counterexample to the plan's
`strongRel ⊆ cRel` claim).

Transitivity (so that `cRel` would lift to a `Setoid`) is a more delicate
fact than the corresponding `c0Rel` transitivity: it uses the orthogonal
decomposition `⟪a, c⟫ - ⟪a, b⟫⟪b, c⟫ = ⟪a⊥, c⊥⟫` and is deferred to a
follow-up commit. -/
def cRel (Ω Ω' : UnitFamily H) : Prop :=
  Summable fun i : ι => ‖1 - ⟪(Ω i : H i), Ω' i⟫_ℂ‖

/-- The von Neumann C-relation implies the canonical Bratteli–Robinson
C₀-relation, via the pointwise bound `‖1 - z‖ ≥ 1 - ‖z‖` for `‖z‖ ≤ 1`. -/
theorem cRel_le_c0Rel {Ω Ω' : UnitFamily H}
    (h : cRel Ω Ω') : c0Rel Ω Ω' := by
  change Summable _
  refine Summable.of_nonneg_of_le ?nonneg ?bound h
  · intro i
    have hub : ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖ ≤ 1 := by
      calc ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖
          ≤ ‖(Ω i : H i)‖ * ‖(Ω' i : H i)‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [Ω.norm_apply i, Ω'.norm_apply i]; ring
    linarith
  · intro i
    -- `1 - ‖z‖ ≤ ‖1 - z‖` for any complex `z`, via `‖1 - z‖² = 1 - 2 Re z + ‖z‖²`
    -- and `Re z ≤ ‖z‖`.
    have hub : ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖ ≤ 1 := by
      calc ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖
          ≤ ‖(Ω i : H i)‖ * ‖(Ω' i : H i)‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [Ω.norm_apply i, Ω'.norm_apply i]; ring
    have hkey : (1 - ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖) ^ 2
        ≤ ‖(1 : ℂ) - ⟪(Ω i : H i), Ω' i⟫_ℂ‖ ^ 2 := by
      -- `(1 - ‖z‖)² ≤ ‖1 - z‖²` for `‖z‖ ≤ 1`.
      have habs := norm_sub_norm_le (1 : ℂ) ⟪(Ω i : H i), Ω' i⟫_ℂ
      have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
      rw [h1] at habs
      -- habs : 1 - ‖⟪Ω i, Ω' i⟫_ℂ‖ ≤ ‖1 - ⟪Ω i, Ω' i⟫_ℂ‖.
      have hnn : 0 ≤ 1 - ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖ := by linarith
      have := sq_le_sq' (by linarith [norm_nonneg ((1 : ℂ) - ⟪(Ω i : H i), Ω' i⟫_ℂ)]) habs
      exact this
    -- From `(1 - ‖z‖)² ≤ ‖1 - z‖²` and `1 - ‖z‖ ≥ 0` we get `1 - ‖z‖ ≤ ‖1 - z‖`.
    have hnn : 0 ≤ 1 - ‖⟪(Ω i : H i), Ω' i⟫_ℂ‖ := by linarith
    have hnn' : 0 ≤ ‖(1 : ℂ) - ⟪(Ω i : H i), Ω' i⟫_ℂ‖ := norm_nonneg _
    nlinarith

end C0Rel

end UnitFamily

end InfiniteTensor
