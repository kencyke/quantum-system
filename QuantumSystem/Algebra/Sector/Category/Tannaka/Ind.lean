module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Minimal Ind-completion interface — R7-0e (S5)

The hardest step of the reconstruction is the *existence* of a fiber functor (Müger,
*Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Theorem 2.11/2.40): it is built
inside the **Ind-completion** `Ind C` of the tensor category, where the symmetric algebra `S(X)`
and the absorbing commutative monoid live (Müger §2.4, roadmap S20–S22).  The full `Ind C` is an
abelian category obtained by freely adjoining filtered colimits; constructing it and its monoidal
/ monoid / module / ideal theory is a multi-session epic.

This file fixes only the **minimal target API** that the existence theorem consumes (roadmap
R7-0e / S5): a category `Ind` with finite biproducts and filtered colimits, together with a fully
faithful embedding `C ⥤ Ind`.  The symmetric-algebra, monoid and quotient layers are built on top
of this interface when the existence theorem is tackled (epic S20–S22); fixing the API now lets the
later stages be stated without committing to a particular construction of `Ind C`. -/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

/-- **A minimal Ind-completion of a category** (roadmap R7-0e / S5): a preadditive category `Ind`
with finite biproducts and filtered colimits, equipped with a fully faithful embedding `C ⥤ Ind`.
This records exactly the categorical structure the fiber-functor *existence* theorem (Müger
Theorem 2.40) needs — finite direct sums (for the determinant / generator package) and filtered
colimits (to host the symmetric algebra `S(X)` and the absorbing monoid).  The abelian / monoidal
/ monoid layers are added on top when the existence theorem is built (epic S20–S22). -/
class HasIndCompletion (C : Type u₁) [Category.{v₁} C] where
  /-- The Ind-completion category. -/
  Ind : Type u₂
  /-- The category structure on the Ind-completion. -/
  [category : Category.{v₂} Ind]
  /-- The Ind-completion is preadditive (so it has zero morphisms and biproducts make sense). -/
  [preadditive : Preadditive Ind]
  /-- The Ind-completion has finite biproducts (finite direct sums). -/
  [hasFiniteBiproducts : HasFiniteBiproducts Ind]
  /-- The Ind-completion has filtered colimits (to host symmetric algebras / colimit objects). -/
  [hasFilteredColimits : HasFilteredColimits Ind]
  /-- The embedding `C ⥤ Ind`. -/
  incl : C ⥤ Ind
  /-- The embedding is full. -/
  [full : incl.Full]
  /-- The embedding is faithful. -/
  [faithful : incl.Faithful]

namespace HasIndCompletion

variable (C : Type u₁) [Category.{v₁} C] [h : HasIndCompletion C]

instance instCategory : Category (Ind C) := h.category

instance instPreadditive : Preadditive (Ind C) := h.preadditive

instance instHasFiniteBiproducts : HasFiniteBiproducts (Ind C) := h.hasFiniteBiproducts

instance instHasFilteredColimits : HasFilteredColimits (Ind C) := h.hasFilteredColimits

instance instFull : h.incl.Full := h.full

instance instFaithful : h.incl.Faithful := h.faithful

end HasIndCompletion

end CategoryTheory
