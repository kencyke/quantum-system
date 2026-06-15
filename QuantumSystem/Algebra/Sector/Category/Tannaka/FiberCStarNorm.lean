module

public import Mathlib.Analysis.Seminorm
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberCStarCompletion

/-!
# The C\*-seminorm on the fiber algebra — S14 (R7-E4, Müger Prop 2.22–2.24)

The concrete Tannaka theorem reconstructs the group as the Gelfand spectrum of the
**C\*-completion** of the fiber algebra `A(E)` (`FiberCStarCompletion.lean`, roadmap S4
fixes the completion as the interface `HasCStarCompletion`).  The substantive analytic
content (Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Propositions
2.22–2.24) is the construction of the **C\*-norm** itself: a submultiplicative `ℂ`-seminorm
on `A(E)` satisfying the C\*-identity `p(a⋆ a) = p(a)²`.  Its construction via the GNS
representation / state space supremum is Mathlib-absent (the "barrier 4" of
`implementation-notes.md`).

This file fixes the **seminorm interface** (roadmap S14): a class `HasCStarSeminorm E`
recording such a seminorm, and proves the genuine algebraic consequences that follow from
the C\*-identity alone — independently of how the seminorm is constructed:

* it is **∗-invariant**, `p(a⋆) = p(a)` (`HasCStarSeminorm.seminorm_star`), the standard
  `C\*`-argument specialised to the commutative algebra `A(E)`;
* the unit has seminorm `0` or `1` (`HasCStarSeminorm.seminorm_one`);
* the **null space** `{a | p a = 0}` is a ∗-ideal (`seminorm_star_eq_zero`,
  `seminorm_mul_eq_zero_of_left`), so the seminorm descends to a genuine C\*-*norm* on the
  separated quotient — the dense pre-image of the C\*-completion `𝓐(E)`;
* the seminorm bundles to a Mathlib `Seminorm ℂ (A(E))` (`HasCStarSeminorm.toSeminorm`).

The completion of that normed ∗-algebra to a commutative unital C\*-algebra — supplying the
`HasCStarCompletion` instance — is the remaining analytic step (it transports the C\*-identity
along `UniformSpace.Completion`); it is recorded here as the forward bridge `HasCStarCompletion`
consumes (roadmap S16/S19).  This is **S14** of the Tannaka roadmap (`implementation-notes.md`
§4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory FiberFunctor.preAlgebra

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerMonoidalCategory V] [DaggerLinear V]

/-- **A C\*-seminorm on the fiber algebra** `A(E)` (Müger Propositions 2.22–2.24; roadmap
S14): a `ℂ`-seminorm on the commutative star algebra `A(E)` that is *submultiplicative* and
satisfies the *C\*-identity* `p(a⋆ a) = p(a)²`.  This is the intermediate datum from which
the C\*-completion `HasCStarCompletion` is built — the seminorm is the substantive analytic
content (constructed via the GNS representation / state space supremum, Mathlib-absent), so
it is carried as a hypothesis class here in the style of the rest of this development.  The
seminorm is recorded as a plain function with its (semi)norm laws as fields and bundled to a
Mathlib `Seminorm` by `toSeminorm`. -/
class FiberFunctor.HasCStarSeminorm (E : FiberFunctor C V) [E.IsStar] where
  /-- The underlying real-valued seminorm `p : A(E) → ℝ`. -/
  seminorm : algebra E E → ℝ
  /-- The seminorm is **non-negative**. -/
  nonneg : ∀ a : algebra E E, 0 ≤ seminorm a
  /-- The seminorm is **subadditive**: `p(a + b) ≤ p(a) + p(b)`. -/
  add_le : ∀ a b : algebra E E, seminorm (a + b) ≤ seminorm a + seminorm b
  /-- The seminorm is **absolutely homogeneous**: `p(c • a) = ‖c‖ · p(a)`. -/
  smul : ∀ (c : ℂ) (a : algebra E E), seminorm (c • a) = ‖c‖ * seminorm a
  /-- The seminorm is **submultiplicative**: `p(a · b) ≤ p(a) · p(b)`. -/
  mul_le : ∀ a b : algebra E E, seminorm (a * b) ≤ seminorm a * seminorm b
  /-- The **C\*-identity**: `p(a⋆ · a) = p(a)²`. -/
  cstar : ∀ a : algebra E E, seminorm (star a * a) = seminorm a ^ 2

namespace FiberFunctor.HasCStarSeminorm

variable {E : FiberFunctor C V} [E.IsStar] [E.HasCStarSeminorm]

/-- The C\*-seminorm bundled as a Mathlib `ℂ`-seminorm on `A(E)` (built from the
subadditivity and absolute homogeneity fields). -/
noncomputable def toSeminorm (E : FiberFunctor C V) [E.IsStar] [E.HasCStarSeminorm] :
    Seminorm ℂ (algebra E E) :=
  Seminorm.of (seminorm (E := E)) add_le smul

@[simp] lemma toSeminorm_apply (a : algebra E E) : toSeminorm E a = seminorm a := rfl

/-- The C\*-seminorm is **∗-invariant**: `p(a⋆) = p(a)` (Müger §2.3).  In the commutative
algebra `A(E)` the C\*-identity gives `p(a)² = p(a⋆ a) = p(a a⋆) = p((a⋆)⋆ a⋆) = p(a⋆)²`,
and both seminorms are non-negative. -/
lemma seminorm_star (a : algebra E E) : seminorm (star a) = seminorm a := by
  have h1 : seminorm (star a * a) = seminorm a ^ 2 := cstar a
  have h2 : seminorm (star (star a) * star a) = seminorm (star a) ^ 2 := cstar (star a)
  rw [star_star, mul_comm] at h2
  have hsq : seminorm a ^ 2 = seminorm (star a) ^ 2 := by rw [← h1, h2]
  exact ((pow_left_inj₀ (nonneg a) (nonneg (star a)) two_ne_zero).mp hsq).symm

/-- The unit of `A(E)` has seminorm `0` or `1`: from the C\*-identity `p(1) = p(1⋆ · 1) =
p(1)²`, so `p(1)(1 - p(1)) = 0`. -/
lemma seminorm_one :
    seminorm (1 : algebra E E) = 0 ∨ seminorm (1 : algebra E E) = 1 := by
  have h1 : seminorm (1 : algebra E E) = seminorm (1 : algebra E E) ^ 2 := by
    have := cstar (1 : algebra E E)
    rwa [star_one, mul_one] at this
  have hfac : seminorm (1 : algebra E E) * (seminorm (1 : algebra E E) - 1) = 0 := by
    rw [mul_sub, mul_one, ← sq, ← h1, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h1'
  · exact Or.inl h0
  · exact Or.inr (by linarith [sub_eq_zero.mp h1'])

/-- The **null space** of the C\*-seminorm is closed under the ∗-involution: `p(a) = 0`
implies `p(a⋆) = 0` (`seminorm_star`).  Together with subadditivity and submultiplicativity
this makes `{a | p a = 0}` a ∗-ideal, so `p` descends to a genuine C\*-*norm* on the
separated quotient — the dense pre-image of the C\*-completion `𝓐(E)`
(`HasCStarCompletion`). -/
lemma seminorm_star_eq_zero {a : algebra E E} (ha : seminorm a = 0) :
    seminorm (star a) = 0 := by
  rw [seminorm_star, ha]

/-- The null space `{a | p a = 0}` is **multiplicatively absorbing**: `p(a) = 0` implies
`p(a · b) = 0` for all `b` (from submultiplicativity), so it is an ideal of `A(E)`. -/
lemma seminorm_mul_eq_zero_of_left {a : algebra E E} (ha : seminorm a = 0) (b : algebra E E) :
    seminorm (a * b) = 0 := by
  refine le_antisymm ?_ (nonneg (a * b))
  have := mul_le a b
  rwa [ha, zero_mul] at this

end FiberFunctor.HasCStarSeminorm

end CategoryTheory
