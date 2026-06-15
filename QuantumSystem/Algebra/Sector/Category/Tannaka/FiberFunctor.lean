module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import QuantumSystem.Algebra.Sector.Category.Dagger

/-!
# Fiber functors — R7-D2

A **fiber functor** (Müger, *Abstract Duality Theory for Symmetric Tensor
∗-Categories*, Definition 2.1) is a faithful, `ℂ`-linear, symmetric strong-monoidal
functor from a symmetric tensor (∗-)category `C` to a symmetric monoidal `ℂ`-linear
target `V` — intended to be finite-dimensional vector spaces (`Vect_ℂ`) or, in the
∗-preserving case, finite-dimensional Hilbert spaces (`Hilb`).

This file fixes the **abstract type** of a fiber functor (parametrised by the target
`V`, per AGENTS "Abstraction first"; the finite-dimensional / Hilbert specialisation
is R7-D1/D3).  Both halves of the reconstruction operate on this structure:

* the *concrete* Tannaka theorem (Müger Thm 2.6, R7-E) reconstructs the group as the
  unitary monoidal natural automorphisms of a fiber functor;
* the *existence* theorem (Müger Thm 2.11/2.40, R7-F) constructs a fiber functor on
  any symmetric tensor ∗-category.

This is **R7-D2** of the staged plan in `implementation-notes.md` (§4 R7).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ u₁ u₂

/-- A **fiber functor** (Müger Definition 2.1, target-`V` version): a faithful,
`ℂ`-linear, symmetric strong-monoidal functor `C ⥤ V`.  `Functor.Braided` bundles
the strong-monoidal structure (`Functor.Monoidal`) together with braiding
preservation; since `C` and `V` are symmetric, a braided functor is symmetric
(Müger 1.21). -/
structure FiberFunctor (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C]
    (V : Type u₂) [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] where
  /-- The underlying functor `C ⥤ V`. -/
  functor : C ⥤ V
  /-- The functor is faithful. -/
  faithful : functor.Faithful
  /-- The functor is `ℂ`-linear. -/
  linear : functor.Linear ℂ
  /-- The functor is symmetric strong-monoidal (`Functor.Braided` between symmetric
  categories). -/
  braided : functor.Braided

namespace FiberFunctor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V]

/-- The underlying functor of a fiber functor is faithful. -/
instance (E : FiberFunctor C V) : E.functor.Faithful := E.faithful

/-- The underlying functor of a fiber functor is `ℂ`-linear. -/
instance (E : FiberFunctor C V) : E.functor.Linear ℂ := E.linear

/-- The underlying functor of a fiber functor is symmetric strong-monoidal. -/
instance (E : FiberFunctor C V) : E.functor.Braided := E.braided

/-- A fiber functor between dagger categories is **∗-preserving** (Müger
Definitions 1.30, 2.1) when its underlying functor commutes with the dagger:
`E(f†) = E(f)†`.  This is the property distinguishing the ∗-preserving symmetric
fiber functors used in the concrete C\*-Tannaka theorem (R7-E) from the bare
Vect-valued ones.  This is **R7-D3**. -/
def IsStarPreserving [DaggerCategory C] [DaggerCategory V] (E : FiberFunctor C V) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y),
    E.functor.map (DaggerCategory.dagger f) = DaggerCategory.dagger (E.functor.map f)

/-- A ∗-preserving fiber functor sends **unitary** morphisms to unitary morphisms:
`E(f) ≫ E(f)† = E(f ≫ f†) = E(𝟙) = 𝟙` and dually.  This is why the elements of the
reconstructed group (unitary monoidal natural automorphisms) act unitarily on each
fibre (R7-E). -/
lemma IsStarPreserving.map_unitary [DaggerCategory C] [DaggerCategory V]
    {E : FiberFunctor C V} (hE : E.IsStarPreserving) {X Y : C} {f : X ⟶ Y}
    (hf : Unitary f) : Unitary (E.functor.map f) := by
  refine ⟨?_, ?_⟩
  · rw [← hE f, ← E.functor.map_comp, hf.1, E.functor.map_id]
  · rw [← hE f, ← E.functor.map_comp, hf.2, E.functor.map_id]

/-- A ∗-preserving fiber functor sends **self-adjoint** endomorphisms to
self-adjoint ones: `E(f)† = E(f†) = E(f)`. -/
lemma IsStarPreserving.map_selfAdjoint [DaggerCategory C] [DaggerCategory V]
    {E : FiberFunctor C V} (hE : E.IsStarPreserving) {X : C} {f : X ⟶ X}
    (hf : DaggerCategory.dagger f = f) :
    DaggerCategory.dagger (E.functor.map f) = E.functor.map f := by
  rw [← hE f, hf]

/-- A ∗-preserving fiber functor sends **isometries** to isometries (Müger Def 1.29):
from `f ≫ f† = 𝟙_X` one gets `E(f) ≫ E(f)† = E(f ≫ f†) = E(𝟙) = 𝟙`. -/
lemma IsStarPreserving.map_isometry [DaggerCategory C] [DaggerCategory V]
    {E : FiberFunctor C V} (hE : E.IsStarPreserving) {X Y : C} {f : X ⟶ Y}
    (hf : f ≫ DaggerCategory.dagger f = 𝟙 X) :
    E.functor.map f ≫ DaggerCategory.dagger (E.functor.map f) = 𝟙 (E.functor.obj X) := by
  rw [← hE f, ← E.functor.map_comp, hf, E.functor.map_id]

/-- A ∗-preserving fiber functor sends **coisometries** to coisometries (the dual of
`map_isometry`): from `f† ≫ f = 𝟙_Y` one gets `E(f)† ≫ E(f) = E(f† ≫ f) = 𝟙`. -/
lemma IsStarPreserving.map_coisometry [DaggerCategory C] [DaggerCategory V]
    {E : FiberFunctor C V} (hE : E.IsStarPreserving) {X Y : C} {f : X ⟶ Y}
    (hf : DaggerCategory.dagger f ≫ f = 𝟙 Y) :
    DaggerCategory.dagger (E.functor.map f) ≫ E.functor.map f = 𝟙 (E.functor.obj Y) := by
  rw [← hE f, ← E.functor.map_comp, hf, E.functor.map_id]

/-- A ∗-preserving fiber functor sends **projections** (`p ≫ p = p`, `p† = p`,
Müger Def 1.29) to projections: idempotency is preserved by any functor, and
self-adjointness by `map_selfAdjoint`.  Needed so that subobjects (R9 / R7-E) map
coherently. -/
lemma IsStarPreserving.map_projection [DaggerCategory C] [DaggerCategory V]
    {E : FiberFunctor C V} (hE : E.IsStarPreserving) {X : C} {p : X ⟶ X}
    (hidem : p ≫ p = p) (hsa : DaggerCategory.dagger p = p) :
    E.functor.map p ≫ E.functor.map p = E.functor.map p ∧
      DaggerCategory.dagger (E.functor.map p) = E.functor.map p :=
  ⟨by rw [← E.functor.map_comp, hidem], hE.map_selfAdjoint hsa⟩

/-- A ∗-preserving fiber functor preserves **positivity** (Müger Def 1.28): if
`p = f ≫ f†` then `E(p) = E(f) ≫ E(f)†`, so positive endomorphisms — in particular
the dimensions `d(X)` — map to positive endomorphisms.  Needed for the concrete
C\*-Tannaka theorem (R7-E). -/
lemma IsStarPreserving.map_isPositiveEndo [DaggerCategory C] [DaggerCategory V]
    {E : FiberFunctor C V} (hE : E.IsStarPreserving) {X : C} {p : X ⟶ X}
    (hp : IsPositiveEndo p) : IsPositiveEndo (E.functor.map p) := by
  obtain ⟨Y, f, rfl⟩ := hp
  exact ⟨E.functor.obj Y, E.functor.map f, by rw [E.functor.map_comp, hE f]⟩

/-- The **reconstruction group** `Nat_⊗(E) = Aut E` of a fiber functor (Müger
Theorem 2.6, R7-D4): the group of monoidal natural automorphisms of the underlying
monoidal functor.  The concrete Tannaka theorem (R7-E) identifies this group — once
refined to its unitary part and equipped with the weak-∗ topology via Gelfand
duality — with the reconstructed compact group `G_E`. -/
noncomputable def reconstructionGroup (E : FiberFunctor C V) : Type (max u₁ v₂) :=
  Aut (LaxMonoidalFunctor.of E.functor)

noncomputable instance (E : FiberFunctor C V) : Group E.reconstructionGroup :=
  inferInstanceAs (Group (Aut _))

/-- The tautological **action** of a reconstruction-group element on the fibre over
`X`: the `X`-component of the underlying monoidal natural automorphism (Müger Thm 2.6,
R7-E2).  Each `g` acts as an automorphism of the fibre `E.functor.obj X`; the concrete
Tannaka theorem upgrades this to the defining (unitary, in the ∗-preserving case)
representation of the reconstructed group on the fibres. -/
noncomputable def reconstructionGroup.act {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (X : C) : E.functor.obj X ⟶ E.functor.obj X :=
  g.hom.hom.app X

/-- The identity of the reconstruction group acts as the identity on every fibre. -/
@[simp] lemma reconstructionGroup.act_one {E : FiberFunctor C V} (X : C) :
    reconstructionGroup.act (1 : E.reconstructionGroup) X = 𝟙 (E.functor.obj X) :=
  rfl

/-- The reconstruction-group action composes contravariantly in the categorical
composition (functor-application) order: `act (g * h) = act h ≫ act g`, reflecting
`Aut.mul_def` (`g * h = h ≪≫ g`) and `NatTrans` composition. -/
@[simp] lemma reconstructionGroup.act_mul {E : FiberFunctor C V}
    (g h : E.reconstructionGroup) (X : C) :
    reconstructionGroup.act (g * h) X
      = reconstructionGroup.act h X ≫ reconstructionGroup.act g X :=
  rfl

/-- `act g` and `act g⁻¹` are mutually inverse on each fibre (one direction): from
`g⁻¹ * g = 1` and `act_mul`/`act_one`. -/
@[simp] lemma reconstructionGroup.act_comp_act_inv {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (X : C) :
    reconstructionGroup.act g X ≫ reconstructionGroup.act g⁻¹ X = 𝟙 (E.functor.obj X) := by
  rw [← reconstructionGroup.act_mul, inv_mul_cancel, reconstructionGroup.act_one]

/-- `act g` and `act g⁻¹` are mutually inverse on each fibre (other direction). -/
@[simp] lemma reconstructionGroup.act_inv_comp_act {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (X : C) :
    reconstructionGroup.act g⁻¹ X ≫ reconstructionGroup.act g X = 𝟙 (E.functor.obj X) := by
  rw [← reconstructionGroup.act_mul, mul_inv_cancel, reconstructionGroup.act_one]

/-- Each reconstruction-group element acts as an **isomorphism** on every fibre, with
inverse the action of `g⁻¹`.  This is the underlying linear isomorphism of the
defining representation reconstructed by the concrete Tannaka theorem (R7-E2). -/
instance reconstructionGroup.act_isIso {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (X : C) : IsIso (reconstructionGroup.act g X) :=
  ⟨⟨reconstructionGroup.act g⁻¹ X,
    reconstructionGroup.act_comp_act_inv g X, reconstructionGroup.act_inv_comp_act g X⟩⟩

/-- The categorical inverse of the action of `g` is the action of `g⁻¹`. -/
@[simp] lemma reconstructionGroup.inv_act {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (X : C) :
    inv (reconstructionGroup.act g X) = reconstructionGroup.act g⁻¹ X :=
  IsIso.inv_eq_of_hom_inv_id (reconstructionGroup.act_comp_act_inv g X)

/-- The reconstruction-group action is **natural** in the object: it intertwines the
images of every morphism, `E(f) ≫ act g Y = act g X ≫ E(f)`.  This naturality — the
fact that each `g` commutes with `E(f)` for all `f` — is exactly what makes the
elements of `reconstructionGroup` tensor-natural automorphisms, and hence the data the
concrete Tannaka theorem reconstructs the group from (Müger Thm 2.6). -/
lemma reconstructionGroup.act_naturality {E : FiberFunctor C V}
    (g : E.reconstructionGroup) {X Y : C} (f : X ⟶ Y) :
    E.functor.map f ≫ reconstructionGroup.act g Y
      = reconstructionGroup.act g X ≫ E.functor.map f :=
  g.hom.hom.naturality f

/-- For a **∗-preserving** fiber functor the action also commutes with the *adjoints*
of images: `E(f)† ≫ act g X = act g Y ≫ E(f)†`.  Combined with `act_naturality` this
shows the reconstruction-group action respects the full dagger structure on morphisms
(not just composition). -/
lemma reconstructionGroup.act_naturality_dagger [DaggerCategory C] [DaggerCategory V]
    {E : FiberFunctor C V} (hE : E.IsStarPreserving) (g : E.reconstructionGroup)
    {X Y : C} (f : X ⟶ Y) :
    DaggerCategory.dagger (E.functor.map f) ≫ reconstructionGroup.act g X
      = reconstructionGroup.act g Y ≫ DaggerCategory.dagger (E.functor.map f) := by
  rw [← hE f]
  exact reconstructionGroup.act_naturality g (DaggerCategory.dagger f)

/-- The reconstruction-group action is **monoidal**: it is compatible with the
tensorators, `μ ≫ act g (X ⊗ Y) = (act g X ⊗ₘ act g Y) ≫ μ`.  This is what upgrades the
fibrewise representation to a *tensor* representation (Müger Thm 2.6). -/
lemma reconstructionGroup.act_tensor {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (X Y : C) :
    Functor.LaxMonoidal.μ E.functor X Y ≫ reconstructionGroup.act g (X ⊗ Y)
      = (reconstructionGroup.act g X ⊗ₘ reconstructionGroup.act g Y)
        ≫ Functor.LaxMonoidal.μ E.functor X Y :=
  g.hom.isMonoidal.tensor X Y

/-- The reconstruction-group action is compatible with the **unit** tensorator,
`ε ≫ act g (𝟙) = ε`: it fixes the image of the monoidal unit. -/
lemma reconstructionGroup.act_unit {E : FiberFunctor C V} (g : E.reconstructionGroup) :
    Functor.LaxMonoidal.ε E.functor ≫ reconstructionGroup.act g (𝟙_ C)
      = Functor.LaxMonoidal.ε E.functor :=
  g.hom.isMonoidal.unit

/-- The **unitary part** of the reconstruction group: the subgroup of elements whose
action is unitary on every fibre.  In the ∗-preserving case this is the subgroup that
the concrete Tannaka theorem (Müger Thm 2.6), via Gelfand duality and the weak-∗
topology, identifies with the reconstructed compact group `G_E`.  Closure under the
group operations is exactly `Unitary.id`/`Unitary.comp`/`Unitary.dagger` transported
along `act_one`/`act_mul` and the inverse relation. -/
def unitaryReconstructionSubgroup [DaggerCategory V] (E : FiberFunctor C V) :
    Subgroup E.reconstructionGroup where
  carrier := {g | ∀ X, Unitary (reconstructionGroup.act g X)}
  one_mem' := by
    intro X
    rw [reconstructionGroup.act_one]
    exact Unitary.id _
  mul_mem' := by
    intro a b ha hb X
    rw [reconstructionGroup.act_mul]
    exact (hb X).comp (ha X)
  inv_mem' := by
    intro a ha X
    have hinv : reconstructionGroup.act a⁻¹ X = (reconstructionGroup.act a X)† := by
      calc reconstructionGroup.act a⁻¹ X
          = reconstructionGroup.act a⁻¹ X
              ≫ (reconstructionGroup.act a X ≫ (reconstructionGroup.act a X)†) := by
            rw [(ha X).1, Category.comp_id]
        _ = (reconstructionGroup.act a⁻¹ X ≫ reconstructionGroup.act a X)
              ≫ (reconstructionGroup.act a X)† := by rw [Category.assoc]
        _ = (reconstructionGroup.act a X)† := by
            rw [reconstructionGroup.act_inv_comp_act, Category.id_comp]
    rw [hinv]
    exact (ha X).dagger

/-- Membership in the unitary reconstruction group is exactly fibrewise unitarity. -/
@[simp] lemma mem_unitaryReconstructionSubgroup [DaggerCategory V] {E : FiberFunctor C V}
    {g : E.reconstructionGroup} :
    g ∈ unitaryReconstructionSubgroup E ↔ ∀ X, Unitary (reconstructionGroup.act g X) :=
  Iff.rfl

/-- The unitary reconstruction group acts **unitarily** on every fibre (by definition
of the subgroup): this is the unitary representation reconstructed by the concrete
Tannaka theorem (Müger Thm 2.6). -/
lemma unitaryReconstructionSubgroup.unitary_act [DaggerCategory V] {E : FiberFunctor C V}
    {g : E.reconstructionGroup} (hg : g ∈ unitaryReconstructionSubgroup E) (X : C) :
    Unitary (reconstructionGroup.act g X) := hg X

/-- For a **unitary** reconstruction-group element the fibrewise adjoint is the action
of the inverse, `(act g X)† = act g⁻¹ X`.  This is the ∗-structure (`π(g)* = π(g⁻¹)`)
of the reconstructed unitary representation. -/
lemma reconstructionGroup.dagger_act [DaggerCategory V] {E : FiberFunctor C V}
    {g : E.reconstructionGroup} (hg : g ∈ unitaryReconstructionSubgroup E) (X : C) :
    (reconstructionGroup.act g X)† = reconstructionGroup.act g⁻¹ X := by
  have huni : Unitary (reconstructionGroup.act g X) := hg X
  calc (reconstructionGroup.act g X)†
      = (reconstructionGroup.act g X)†
          ≫ (reconstructionGroup.act g X ≫ reconstructionGroup.act g⁻¹ X) := by
        rw [reconstructionGroup.act_comp_act_inv, Category.comp_id]
    _ = ((reconstructionGroup.act g X)† ≫ reconstructionGroup.act g X)
          ≫ reconstructionGroup.act g⁻¹ X := by rw [Category.assoc]
    _ = reconstructionGroup.act g⁻¹ X := by rw [huni.2, Category.id_comp]

/-- For a unitary reconstruction-group element the fibrewise **adjoint equals the
categorical inverse**, `(act g X)† = inv (act g X)`: the action is a dagger isomorphism
(categorically unitary).  Combines `dagger_act` and `inv_act`. -/
lemma reconstructionGroup.dagger_act_eq_inv [DaggerCategory V] {E : FiberFunctor C V}
    {g : E.reconstructionGroup} (hg : g ∈ unitaryReconstructionSubgroup E) (X : C) :
    (reconstructionGroup.act g X)† = inv (reconstructionGroup.act g X) := by
  rw [reconstructionGroup.dagger_act hg, reconstructionGroup.inv_act]

/-- The **fibre representation** over `X`: the group homomorphism sending each
reconstruction-group element to its action on the fibre `E.functor.obj X`, viewed as an
automorphism (well-defined by `act_isIso`).  The contravariance of `act_mul` matches
that of `Aut`'s multiplication (`Aut_mul_def`), so this is a genuine homomorphism — the
defining representation of the reconstructed group on each fibre (Müger Thm 2.6). -/
noncomputable def fibreRep (E : FiberFunctor C V) (X : C) :
    E.reconstructionGroup →* Aut (E.functor.obj X) where
  toFun g := asIso (reconstructionGroup.act g X)
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

/-- The fibrewise actions **determine** a reconstruction-group element: if `g` and `h`
act identically on every fibre, they are equal.  This injectivity of the total
representation `g ↦ (act g X)_X` — proved by the `Aut → LaxMonoidalFunctor.Hom →
NatTrans` extensionality chain — is the faithfulness underlying Tannaka reconstruction
(Müger Thm 2.6). -/
@[ext] lemma reconstructionGroup.ext {E : FiberFunctor C V} {g h : E.reconstructionGroup}
    (H : ∀ X, reconstructionGroup.act g X = reconstructionGroup.act h X) : g = h := by
  apply Aut.ext
  ext X
  exact H X

/-- The **total fibre representation**: the group homomorphism assembling the fibrewise
representations `fibreRep E X` over all objects `X` into a single homomorphism to the
product group `∀ X, Aut (E.functor.obj X)`. -/
noncomputable def totalFibreRep (E : FiberFunctor C V) :
    E.reconstructionGroup →* (∀ X, Aut (E.functor.obj X)) where
  toFun g X := fibreRep E X g
  map_one' := by funext X; exact (fibreRep E X).map_one
  map_mul' g h := by funext X; exact (fibreRep E X).map_mul g h

/-- The total fibre representation is **injective** — the faithfulness of Tannaka
reconstruction (Müger Thm 2.6): a reconstruction-group element is determined by its
action on all fibres (`reconstructionGroup.ext`). -/
lemma totalFibreRep_injective (E : FiberFunctor C V) :
    Function.Injective (totalFibreRep E) := by
  intro g h hgh
  apply reconstructionGroup.ext
  intro X
  have hX := congrFun hgh X
  simpa only [totalFibreRep, fibreRep, MonoidHom.coe_mk, OneHom.coe_mk, asIso_hom]
    using congrArg Iso.hom hX

/-- The underlying **natural automorphism** of the fiber functor determined by a
reconstruction-group element (the image under the forgetful map `LaxMonoidalFunctor C V
→ (C ⥤ V)`).  Its component at `X` is the fibrewise action `act g X`. -/
noncomputable def reconstructionGroup.toFunctorIso {E : FiberFunctor C V}
    (g : E.reconstructionGroup) : E.functor ≅ E.functor where
  hom := g.hom.hom
  inv := g.inv.hom
  hom_inv_id := by ext X; exact reconstructionGroup.act_comp_act_inv g X
  inv_hom_id := by ext X; exact reconstructionGroup.act_inv_comp_act g X

/-- The component of the underlying natural automorphism is the fibrewise action. -/
@[simp] lemma reconstructionGroup.toFunctorIso_hom_app {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (X : C) :
    g.toFunctorIso.hom.app X = reconstructionGroup.act g X := rfl

end FiberFunctor

end CategoryTheory
