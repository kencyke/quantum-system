module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.RepF
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Compact (super)groups and the central grading — S12 (R7-C)

The Doplicher–Roberts reconstruction (Müger, *Abstract Duality Theory for Symmetric
Tensor ∗-Categories*, Theorem 2.18) identifies a symmetric tensor ∗-category with the
representation category `RepF(G, k)` of a compact **supergroup** `(G, k)`: a compact
topological group `G` together with a central involution `k ∈ Z(G)`, `k² = 1`, whose
adjoint action provides the `ℤ/2`-grading (parity) of the representations.  The even
case `k = 1` (Müger Theorem 2.12) recovers an ordinary compact group.

This file fixes the **group input** of the reconstruction (roadmap R7-C):

* `Supergroup` — a compact group with a central involution `k`, with the genuine group
  algebra of `k` (it is its own inverse, central, idempotent up to `²`);
* `Supergroup.IsEven` — the even case `k = 1`;
* the **central grading operator** `Σ_k` (Müger Lemma 2.16) realised abstractly: an
  *involutive* element of a fiber functor's reconstruction group acts on every fibre as a
  self-inverse isomorphism, and — for a unitary such element — as a **self-adjoint
  unitary** (a symmetry), exactly the grading/twist `Θ(H, π) = π(k)` of the supergroup.

The representation category `RepF(G)` *as a symmetric tensor ∗-category* (C2/C3) is the
abstract `TannakianStructure` interface fixed in `RepF.lean` (roadmap S5): a category is
`RepF(G)` for some `G` precisely when it carries a ∗-preserving symmetric fiber functor to
a Tannaka target, and the reconstruction theorem (roadmap S19) produces such a structure.
This file adds only the supergroup-specific grading layer on top, in the minimal-interface
spirit of `HasIndCompletion`/`MonoidObject`.  This is **S12** of the Tannaka roadmap
(`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ u₁ u₂ u

/-! ### Compact supergroups -/

/-- A **compact supergroup** `(G, k)` (Müger §2.4 / Lemma 2.16): a compact topological
group `G` together with a central involution `k ∈ Z(G)`, `k² = 1`.  The adjoint action of
`k` gives the `ℤ/2`-grading (parity) of the representation category; the even case `k = 1`
(`IsEven`, Müger Theorem 2.12) recovers an ordinary compact group.  This is the group input
of the Doplicher–Roberts reconstruction (Müger Theorem 2.18). -/
structure Supergroup where
  /-- The underlying group. -/
  carrier : Type u
  /-- The group structure. -/
  [group : Group carrier]
  /-- The topology on the group. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The group operations are continuous. -/
  [isTopologicalGroup : IsTopologicalGroup carrier]
  /-- The group is compact. -/
  [compactSpace : CompactSpace carrier]
  /-- The central involution `k`. -/
  k : carrier
  /-- `k` lies in the centre of `G`. -/
  k_mem_center : k ∈ Subgroup.center carrier
  /-- `k` is an involution: `k² = 1`. -/
  k_sq : k ^ 2 = 1

namespace Supergroup

attribute [instance] group topologicalSpace isTopologicalGroup compactSpace

variable (S : Supergroup)

/-- `k` commutes with every element of the group (it is central). -/
lemma k_comm (g : S.carrier) : g * S.k = S.k * g :=
  Subgroup.mem_center_iff.mp S.k_mem_center g

/-- `k * k = 1`, the unfolded involution relation. -/
@[simp] lemma k_mul_self : S.k * S.k = 1 := by
  rw [← sq]; exact S.k_sq

/-- `k` is its own inverse (`k² = 1`). -/
@[simp] lemma k_inv : S.k⁻¹ = S.k :=
  inv_eq_of_mul_eq_one_right S.k_mul_self

/-- The supergroup is **even** when its central involution is trivial, `k = 1` (Müger
Theorem 2.12): the representation category is then an ordinary (`ℤ/2`-trivially graded)
symmetric tensor ∗-category. -/
def IsEven : Prop := S.k = 1

/-- In an even supergroup the involution is the identity, so it acts trivially. -/
lemma k_eq_one_of_isEven (h : S.IsEven) : S.k = 1 := h

end Supergroup

/-! ### The central grading operator `Σ_k` on the fibres

The twist `Θ(H, π) = π(k)` of Müger Lemma 2.16 is realised abstractly through the
reconstruction group of a fiber functor: a *central involution* of the reconstructed group
is an element `g` of the reconstruction group `Aut_⊗(Id)` with `g² = 1`, and its fibrewise
action `act g X` is the grading operator `Σ_k` on the fibre.  We prove its defining
properties (self-inverse isomorphism; self-adjoint unitary symmetry in the ∗-preserving
case) directly from the group structure of `reconstructionGroup`. -/

namespace FiberFunctor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V]

/-- The **grading (twist) operator** `Σ_k` of an involutive reconstruction-group element
(Müger Lemma 2.16, `Θ(H, π) = π(k)`): the fibrewise action `act g X` of an element `g`
with `g² = 1`.  Its square is the identity (`gradingOperator_involutive`); for a unitary
`g` it is moreover self-adjoint, hence a symmetry. -/
noncomputable def gradingOperator {E : FiberFunctor C V} (g : E.reconstructionGroup) (X : C) :
    E.functor.obj X ⟶ E.functor.obj X :=
  reconstructionGroup.act g X

/-- The grading operator of an involution is **self-inverse**: `Σ_k ≫ Σ_k = 𝟙`, since the
fibrewise action is a homomorphism and `g² = 1`. -/
lemma gradingOperator_involutive {E : FiberFunctor C V} {g : E.reconstructionGroup}
    (hg : g ^ 2 = 1) (X : C) :
    gradingOperator g X ≫ gradingOperator g X = 𝟙 (E.functor.obj X) := by
  rw [gradingOperator, ← reconstructionGroup.act_mul, ← sq, hg, reconstructionGroup.act_one]

/-- The grading operator of an involution is an **isomorphism**, being its own inverse. -/
lemma isIso_gradingOperator {E : FiberFunctor C V} {g : E.reconstructionGroup}
    (hg : g ^ 2 = 1) (X : C) : IsIso (gradingOperator g X) :=
  ⟨⟨gradingOperator g X, gradingOperator_involutive hg X, gradingOperator_involutive hg X⟩⟩

/-- For a **unitary** involution the grading operator is **self-adjoint**: `Σ_k† = Σ_k`.
Combined with `gradingOperator_involutive` (`Σ_k² = 𝟙`) and unitarity this exhibits `Σ_k`
as a *symmetry* (a self-adjoint unitary), the standard form of the `ℤ/2`-grading operator
`π(k)` of a supergroup representation. -/
lemma gradingOperator_selfAdjoint [DaggerCategory V] {E : FiberFunctor C V}
    {g : E.reconstructionGroup} (hg : g ^ 2 = 1)
    (hu : g ∈ unitaryReconstructionSubgroup E) (X : C) :
    (gradingOperator g X)† = gradingOperator g X := by
  rw [gradingOperator, reconstructionGroup.dagger_act hu]
  have hinv : g⁻¹ = g := by
    rw [inv_eq_of_mul_eq_one_right]; rw [← sq]; exact hg
  rw [hinv]

end FiberFunctor

end CategoryTheory
