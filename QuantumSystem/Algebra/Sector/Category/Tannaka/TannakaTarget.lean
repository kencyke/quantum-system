module

public import Mathlib.CategoryTheory.Linear.Basic
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberAlgebra

/-!
# Tannaka target categories and the trace pairing — R7-0c (S3)

The concrete Tannaka theorem (Müger, *Abstract Duality Theory for Symmetric Tensor
∗-Categories*, Theorem 2.6) reconstructs the group as the spectrum of the coend
algebra `A(E) = ∫^X End_V(E X)` of a fiber functor `E : C ⥤ V`.  Its continuous dual
is `Nat(E)`, the monoidal natural transformations, and the identification
`Nat(E) ≅ A(E)^*` is implemented by the **trace pairing** (Müger Proposition 2.27)

```
⟨α, [X, s]⟩ = Tr_V (s ≫ α_X).
```

For this pairing to make sense the target `V` must carry a categorical trace — a
`ℂ`-valued functional on each endomorphism space that is **cyclic**
(`Tr (f ≫ g) = Tr (g ≫ f)`), **multiplicative under tensor**
(`Tr (f ⊗ g) = Tr f · Tr g`) and **normalised** (`Tr 𝟙_{𝟙_V} = 1`).  The abstract
`FiberFunctor C V` target (`FiberFunctor.lean`) is only required to be symmetric
monoidal `ℂ`-linear, which is the right level for the coend *algebra* `A(E)`
(`FiberAlgebra.lean`); the **trace** is the extra structure the *characters* need, so
it is introduced here as a separate class `TannakaTarget V` (per `implementation-notes.md`
§4 R7-0c / roadmap S3).  Concretely it is realised by finite-dimensional Hilbert spaces
`Hilb_f` (the rigid C\*-target of the concrete theorem, where the trace is the right
trace of the rigid structure); that instance is built when needed (roadmap S13).

This file fixes the `TannakaTarget` interface and proves the **prototype lemma** the
roadmap names as S3's completion condition: the trace pairing kills the generators of
the naturality ideal `naturalityRel`, hence descends to a well-defined `ℂ`-linear
functional `pairing α : A(E₁, E₂) →ₗ[ℂ] ℂ` on the coend.  Multiplicativity of the
pairing (the characters ↔ monoidal natural transformations correspondence, Müger
Prop 2.27/2.28) and the ∗-compatibility `Tr (f†) = conj (Tr f)` are the next stage
(roadmap S15).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory DirectSum Limits

-- A single canonical classical `DecidableEq` on every type, for the `DirectSum`
-- injections indexed by the object type of `C` (matching `FiberAlgebra.lean`).
attribute [local instance] Classical.propDecidable

universe v₁ v₂ u₁ u₂

/-- A **Tannaka target** (Müger, *Abstract Duality Theory for Symmetric Tensor
∗-Categories*, §2.3): a `ℂ`-linear monoidal category `V` equipped with a `ℂ`-valued
**categorical trace** on each endomorphism space, which is cyclic, multiplicative under
the tensor product, and normalised on the unit.  This is the structure the *characters*
of the coend algebra `A(E)` require, beyond the bare symmetric monoidal `ℂ`-linear
structure used to build `A(E)` itself (`FiberAlgebra.lean`).  The intended model is the
rigid C\*-category of finite-dimensional Hilbert spaces, where the trace is the right
trace of the rigid structure (roadmap S13).

Nondegeneracy of the trace pairing and ∗-compatibility (`Tr (f†) = conj (Tr f)`) are
deliberately *not* fields here: they are needed only for fullness/faithfulness and the
∗-character correspondence (roadmap S15/S17) and are added as separate refinements when
consumed, keeping this interface minimal and easy to instantiate. -/
class TannakaTarget (V : Type u₂) [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] where
  /-- The `ℂ`-valued categorical trace on each endomorphism space, as a `ℂ`-linear
  functional. -/
  trace : {X : V} → (X ⟶ X) →ₗ[ℂ] ℂ
  /-- **Cyclicity** of the trace (Müger §1.4): `Tr (f ≫ g) = Tr (g ≫ f)`. -/
  trace_comp_comm : ∀ {X Y : V} (f : X ⟶ Y) (g : Y ⟶ X), trace (f ≫ g) = trace (g ≫ f)
  /-- **Tensor multiplicativity** of the trace: `Tr (f ⊗ g) = Tr f · Tr g`. -/
  trace_tensor : ∀ {X Y : V} (f : X ⟶ X) (g : Y ⟶ Y), trace (f ⊗ₘ g) = trace f * trace g
  /-- **Normalisation**: the trace of the identity on the unit object is `1`
  (`dim 𝟙_V = 1`). -/
  trace_id_unit : trace (𝟙 (𝟙_ V)) = (1 : ℂ)

namespace TannakaTarget

variable {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [TannakaTarget V]

/-- The trace is **invariant under conjugation by an isomorphism** (Müger §1.4):
`Tr (φ⁻¹ ≫ f ≫ φ) = Tr f`.  A direct consequence of cyclicity. -/
lemma trace_conj {X Y : V} (φ : X ≅ Y) (f : X ⟶ X) :
    trace (φ.inv ≫ f ≫ φ.hom) = trace f := by
  rw [trace_comp_comm φ.inv (f ≫ φ.hom), Category.assoc, φ.hom_inv_id, Category.comp_id]

/-- **Isomorphic objects have the same identity trace** (Müger §1.4): `X ≅ Y` implies
`Tr 𝟙_X = Tr 𝟙_Y`.  This is what makes the categorical dimension `Tr 𝟙_X` an invariant
of the isomorphism class. -/
lemma trace_id_of_iso {X Y : V} (φ : X ≅ Y) : trace (𝟙 X) = trace (𝟙 Y) := by
  rw [← φ.hom_inv_id, trace_comp_comm, φ.inv_hom_id]

/-- An object **isomorphic to the unit has identity trace `1`** (Müger §1.4 + Lemma 1.42,
`dim 𝟙 = 1`): combine `trace_id_of_iso` with the normalisation `trace_id_unit`.  In
particular `Tr 𝟙_{E 𝟙_C} = 1` for any (strong-)monoidal functor `E`, since `E 𝟙_C ≅ 𝟙_V`. -/
lemma trace_id_eq_one_of_iso_unit {X : V} (φ : X ≅ 𝟙_ V) : trace (𝟙 X) = (1 : ℂ) := by
  rw [trace_id_of_iso φ, trace_id_unit]

end TannakaTarget

namespace FiberFunctor.preAlgebra

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [TannakaTarget V]
    {E₁ E₂ : FiberFunctor C V}

/-- The **pre-pairing** of a natural transformation `α : E₁ ⟹ E₂` with the pre-algebra
`A₀(E₁, E₂) = ⨁_X Hom_V(E₂ X, E₁ X)` (Müger Proposition 2.27): the `ℂ`-linear functional
sending the homogeneous generator `[X, s]` to the trace `Tr_V (s ≫ α_X)`, where
`s : E₂ X ⟶ E₁ X` and `α_X : E₁ X ⟶ E₂ X`, so `s ≫ α_X` is an endomorphism of `E₂ X`. -/
noncomputable def pairingPre (α : E₁.functor ⟶ E₂.functor) :
    E₁.preAlgebra E₂ →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ C ℂ fun X =>
    (TannakaTarget.trace (V := V)).comp (Linear.rightComp ℂ (E₂.functor.obj X) (α.app X))

@[simp] lemma pairingPre_mk (α : E₁.functor ⟶ E₂.functor) (X : C)
    (s : E₂.functor.obj X ⟶ E₁.functor.obj X) :
    pairingPre α (mk X s) = TannakaTarget.trace (s ≫ α.app X) := by
  change DirectSum.toModule ℂ C ℂ
      (fun X => (TannakaTarget.trace (V := V)).comp
        (Linear.rightComp ℂ (E₂.functor.obj X) (α.app X)))
      (DirectSum.lof ℂ C (fun X => E₂.functor.obj X ⟶ E₁.functor.obj X) X s)
    = TannakaTarget.trace (s ≫ α.app X)
  rw [DirectSum.toModule_lof]
  rfl

/-- **The trace pairing kills the naturality ideal** (Müger Proposition 2.27, the S3
completion condition): the pre-pairing `pairingPre α` vanishes on every generator
`[X, E₂ f ≫ g] - [Y, g ≫ E₁ f]` of `naturalityRel`, hence on the whole submodule.  The
generator computation uses only the **cyclicity** of the target trace and the
**naturality** of `α`:
`Tr ((E₂ f ≫ g) ≫ α_X) = Tr (g ≫ α_X ≫ E₂ f) = Tr (g ≫ E₁ f ≫ α_Y) = Tr ((g ≫ E₁ f) ≫ α_Y)`. -/
lemma naturalityRel_le_ker_pairingPre (α : E₁.functor ⟶ E₂.functor) :
    naturalityRel E₁ E₂ ≤ LinearMap.ker (pairingPre α) := by
  rw [naturalityRel, Submodule.span_le]
  rintro _ ⟨X, Y, f, g, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, pairingPre_mk, pairingPre_mk, sub_eq_zero]
  simp only [Category.assoc]
  rw [TannakaTarget.trace_comp_comm (E₂.functor.map f) (g ≫ α.app X)]
  simp only [Category.assoc]
  rw [← α.naturality f]

/-- The **trace pairing** of a natural transformation `α : E₁ ⟹ E₂` with the coend
`A(E₁, E₂) = ∫^X Hom_V(E₂ X, E₁ X)` (Müger Proposition 2.27): the well-defined descent of
`pairingPre α` through the naturality ideal, given by `⟨α, [X, s]⟩ = Tr_V (s ≫ α_X)`.  This
is the map implementing `Nat(E₁, E₂) → A(E₁, E₂)^*` whose multiplicativity (for monoidal `α`)
identifies the characters of `A(E)` with the monoidal natural transformations (roadmap S15). -/
noncomputable def pairing (α : E₁.functor ⟶ E₂.functor) : algebra E₁ E₂ →ₗ[ℂ] ℂ :=
  (naturalityRel E₁ E₂).liftQ (pairingPre α) (naturalityRel_le_ker_pairingPre α)

@[simp] lemma pairing_toAlgebra (α : E₁.functor ⟶ E₂.functor) (a : E₁.preAlgebra E₂) :
    pairing α (toAlgebra E₁ E₂ a) = pairingPre α a := rfl

/-- The trace pairing **on a generator** of the coend (Müger Proposition 2.27):
`⟨α, [X, s]⟩ = Tr_V (s ≫ α_X)`. -/
@[simp] lemma pairing_toAlgebra_mk (α : E₁.functor ⟶ E₂.functor) (X : C)
    (s : E₂.functor.obj X ⟶ E₁.functor.obj X) :
    pairing α (toAlgebra E₁ E₂ (mk X s)) = TannakaTarget.trace (s ≫ α.app X) := by
  rw [pairing_toAlgebra, pairingPre_mk]

/-- The pairing with the **identity natural transformation** recovers the bare target
trace: `⟨𝟙_E, [X, s]⟩ = Tr_V s`.  This is the value of the *counit*-style functional and,
on `[X, 𝟙]`, returns the categorical dimension `Tr_V 𝟙_{E X}` of the fibre. -/
@[simp] lemma pairing_id {E : FiberFunctor C V} (X : C)
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    pairing (𝟙 E.functor) (toAlgebra E E (mk X s)) = TannakaTarget.trace s := by
  rw [pairing_toAlgebra_mk]
  simp only [NatTrans.id_app, Category.comp_id]

/-! ### Multiplicativity of the trace pairing — characters ↔ monoidal natural transformations

The forward half of Müger Proposition 2.27/2.28: a **monoidal** natural transformation pairs
with the coend algebra `A(E)` as a *character* (`ℂ`-algebra homomorphism `A(E) → ℂ`).  This is
where the `trace_tensor` and `trace_id_unit` fields of `TannakaTarget` are used; combined with
the (deferred) C\*-completion and Gelfand duality (roadmap S14/S16) it yields the reconstructed
group as the character space of `A(E)`. -/

variable [MonoidalPreadditive V] [MonoidalLinear ℂ V]

/-- **The trace pairing is multiplicative for a monoidal natural transformation** (Müger
Proposition 2.27): if `α : E ⟹ E` is compatible with the tensorators
(`μ ≫ α_{X⊗Y} = (α_X ⊗ α_Y) ≫ μ`), then `⟨α, A · B⟩ = ⟨α, A⟩ · ⟨α, B⟩`.  On generators this is the
chain
`Tr (homMul s t ≫ α_{X⊗Y}) = Tr ((s≫α_X) ⊗ (t≫α_Y)) = Tr (s≫α_X) · Tr (t≫α_Y)`,
using the strong-monoidal inverse `μ ≫ δ = 𝟙`, the interchange law, cyclicity, and the tensor
multiplicativity of the target trace; the general case follows since every element of `A(E)` is a
single generator (`exists_toAlgebra_mk`). -/
lemma pairing_mul_of_monoidal [HasBinaryBiproducts C] {E : FiberFunctor C V}
    (α : E.functor ⟶ E.functor)
    (htensor : ∀ X Y : C, Functor.LaxMonoidal.μ E.functor X Y ≫ α.app (X ⊗ Y)
      = (α.app X ⊗ₘ α.app Y) ≫ Functor.LaxMonoidal.μ E.functor X Y)
    (A B : algebra E E) :
    pairing α (A * B) = pairing α A * pairing α B := by
  obtain ⟨X, s, rfl⟩ := exists_toAlgebra_mk E A
  obtain ⟨Y, t, rfl⟩ := exists_toAlgebra_mk E B
  rw [toAlgebra_mk_mul, pairing_toAlgebra_mk, pairing_toAlgebra_mk, pairing_toAlgebra_mk,
    FiberFunctor.homMul, Category.assoc, Category.assoc, htensor X Y,
    ← Category.assoc (s ⊗ₘ t), MonoidalCategory.tensorHom_comp_tensorHom,
    TannakaTarget.trace_comp_comm (Functor.OplaxMonoidal.δ E.functor X Y),
    Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id, TannakaTarget.trace_tensor]

/-- **The trace pairing sends the unit of `A(E)` to `1` for a monoidal natural transformation**
(Müger Proposition 2.27): if `α : E ⟹ E` fixes the unit comparison (`ε ≫ α_{𝟙_C} = ε`), then
`⟨α, 1⟩ = 1`.  Unitarity of `ε` forces `α_{𝟙_C} = 𝟙`, and `E 𝟙_C ≅ 𝟙_V` gives
`Tr 𝟙_{E 𝟙_C} = 1` (`trace_id_eq_one_of_iso_unit`). -/
lemma pairing_one_of_unit {E : FiberFunctor C V} (α : E.functor ⟶ E.functor)
    (hunit : Functor.LaxMonoidal.ε E.functor ≫ α.app (𝟙_ C) = Functor.LaxMonoidal.ε E.functor) :
    pairing α (1 : algebra E E) = 1 := by
  have happ : α.app (𝟙_ C) = 𝟙 (E.functor.obj (𝟙_ C)) := by
    rw [← cancel_epi (Functor.Monoidal.εIso E.functor).hom, Functor.Monoidal.εIso_hom,
      Category.comp_id]
    exact hunit
  rw [← oneQ_eq_one E, oneQ_def]
  change pairing α (toAlgebra E E (mk (𝟙_ C) (𝟙 (E.functor.obj (𝟙_ C))))) = 1
  rw [pairing_toAlgebra_mk, Category.id_comp, happ]
  exact TannakaTarget.trace_id_eq_one_of_iso_unit (Functor.Monoidal.εIso E.functor).symm

/-- **A reconstruction-group element pairs as a multiplicative functional** (Müger Prop 2.27):
specialising `pairing_mul_of_monoidal` to `α = g.toFunctorIso.hom` via the monoidality of the
reconstruction-group action (`reconstructionGroup.act_tensor`). -/
lemma pairing_act_mul [HasBinaryBiproducts C] {E : FiberFunctor C V} (g : E.reconstructionGroup)
    (A B : algebra E E) :
    pairing g.toFunctorIso.hom (A * B)
      = pairing g.toFunctorIso.hom A * pairing g.toFunctorIso.hom B := by
  refine pairing_mul_of_monoidal _ (fun X Y => ?_) A B
  simpa only [reconstructionGroup.toFunctorIso_hom_app] using reconstructionGroup.act_tensor g X Y

/-- **A reconstruction-group element pairs as a unital functional** (Müger Prop 2.27):
specialising `pairing_one_of_unit` to `α = g.toFunctorIso.hom` via `reconstructionGroup.act_unit`. -/
lemma pairing_act_one {E : FiberFunctor C V} (g : E.reconstructionGroup) :
    pairing g.toFunctorIso.hom (1 : algebra E E) = 1 := by
  refine pairing_one_of_unit _ ?_
  simpa only [reconstructionGroup.toFunctorIso_hom_app] using reconstructionGroup.act_unit g

/-- **The character of the coend algebra defined by a reconstruction-group element** (Müger
Theorem 2.6 / Proposition 2.27): the trace pairing `A(E) → ℂ` against `g`, packaged as a
`ℂ`-algebra homomorphism.  This is the map `Nat_⊗(E) → χ(A(E))` from monoidal natural
automorphisms to characters whose image — once `A(E)` is completed to a commutative C\*-algebra
and Gelfand duality is invoked (roadmap S14/S16) — recovers the reconstructed compact group. -/
noncomputable def reconstructionCharacter [HasBinaryBiproducts C] {E : FiberFunctor C V}
    (g : E.reconstructionGroup) : algebra E E →ₐ[ℂ] ℂ :=
  AlgHom.mk'
    { toFun := pairing g.toFunctorIso.hom
      map_one' := pairing_act_one g
      map_mul' := pairing_act_mul g
      map_zero' := map_zero _
      map_add' := map_add _ }
    fun c A => (pairing g.toFunctorIso.hom).map_smul c A

@[simp] lemma reconstructionCharacter_apply [HasBinaryBiproducts C] {E : FiberFunctor C V}
    (g : E.reconstructionGroup) (A : algebra E E) :
    reconstructionCharacter g A = pairing g.toFunctorIso.hom A := rfl

end FiberFunctor.preAlgebra

end CategoryTheory
