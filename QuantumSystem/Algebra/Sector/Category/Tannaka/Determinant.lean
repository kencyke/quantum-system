module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.DimensionProperties
public import QuantumSystem.Algebra.Sector.Category.Tannaka.TensorPower

/-!
# Integrality of the dimension and the determinant — S10 (R7-B5)

Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Lemmas
2.45–2.53: in a symmetric tensor ∗-category the dimension of every object is a
**non-negative integer**, and every object `X` has a one-dimensional **determinant**
`det X` (the image of the top antisymmetrizer on `X⊗ⁿ`, `n = dim X`) which is
multiplicative, `det(X ⊕ Y) ≅ det X ⊗ det Y`.

This file fixes:

* the integrality conclusion as the hypothesis class `HasIntegralDimension`
  (`dim X ∈ ℕ`), together with the genuine arithmetic it entails — the extracted
  natural dimension `STCStar.dimNat` is **multiplicative** over `⊗`, **additive**
  over `⊞`, and **`≥ 1`** on nonzero objects (`dimNat_tensor`, `dimNat_biprod`,
  `one_le_dimNat`), proved from `HasStandardDimension`;
* the determinant as the interface `HasDeterminant` (one-dimensional + multiplicative).

The integrality argument itself and the determinant construction (via the higher
antisymmetrizers of `TensorPower` and their splitting) are the deferred content of
Müger Lemmas 2.45–2.53, carried as hypothesis interfaces here in the style of the
rest of this development.  This is **S10** of the Tannaka roadmap
(`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidSymmetricDaggerCategory C] [CStarLinearCategory C]
    [∀ X Y : C, CompleteSpace (X ⟶ Y)]
    [HasBinaryBiproducts C] [IsIdempotentComplete C] [STCStar C]

/-! ### Integrality of the dimension -/

/-- The dimension is **integral** (Müger Lemmas 2.45–2.53): `dim X ∈ ℕ` for every
object.  This is the conclusion of the determinant/integrality argument; it is carried
as a hypothesis class (built on the real `≥ 1` dimension of `HasStandardDimension`), in
the style of the other deferred statements of this development. -/
class HasIntegralDimension (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidSymmetricDaggerCategory C] [CStarLinearCategory C]
    [∀ X Y : C, CompleteSpace (X ⟶ Y)] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    [STCStar C] : Prop where
  /-- The scalar dimension of every object is a natural number. -/
  dim_isNat : ∀ X : C, ∃ k : ℕ, STCStar.dim X = (k : ℂ)

open Classical in
/-- The **natural dimension** `dimNat X ∈ ℕ` of an object (Müger Lemmas 2.45–2.53). -/
noncomputable def STCStar.dimNat [HasIntegralDimension C] (X : C) : ℕ :=
  (HasIntegralDimension.dim_isNat X).choose

open Classical in
/-- The natural dimension recovers the scalar dimension: `dim X = dimNat X`. -/
lemma STCStar.dim_eq_dimNat [HasIntegralDimension C] (X : C) :
    STCStar.dim X = (STCStar.dimNat X : ℂ) :=
  (HasIntegralDimension.dim_isNat X).choose_spec

/-- The natural dimension is **multiplicative** over tensor products:
`dimNat (X ⊗ Y) = dimNat X · dimNat Y` (from `HasStandardDimension.dim_tensor`). -/
lemma STCStar.dimNat_tensor [HasIntegralDimension C] [HasStandardDimension C] (X Y : C) :
    STCStar.dimNat (X ⊗ Y) = STCStar.dimNat X * STCStar.dimNat Y := by
  have h := HasStandardDimension.dim_tensor (C := C) X Y
  rw [STCStar.dim_eq_dimNat, STCStar.dim_eq_dimNat, STCStar.dim_eq_dimNat] at h
  exact_mod_cast h

/-- The natural dimension is **additive** over binary direct sums:
`dimNat (X ⊞ Y) = dimNat X + dimNat Y` (from `HasStandardDimension.dim_biprod`). -/
lemma STCStar.dimNat_biprod [HasIntegralDimension C] [HasStandardDimension C] (X Y : C) :
    STCStar.dimNat (X ⊞ Y) = STCStar.dimNat X + STCStar.dimNat Y := by
  have h := HasStandardDimension.dim_biprod (C := C) X Y
  rw [STCStar.dim_eq_dimNat, STCStar.dim_eq_dimNat, STCStar.dim_eq_dimNat] at h
  exact_mod_cast h

/-- Every nonzero object has natural dimension **`≥ 1`** (from
`HasStandardDimension.one_le_dim_re`). -/
lemma STCStar.one_le_dimNat [HasIntegralDimension C] [HasStandardDimension C] {X : C}
    (hX : ‖𝟙 X‖ ≠ 0) : 1 ≤ STCStar.dimNat X := by
  have h := HasStandardDimension.one_le_dim_re (C := C) X hX
  rw [STCStar.dim_eq_dimNat] at h
  simp only [Complex.natCast_re] at h
  exact_mod_cast h

/-! ### The determinant -/

/-- The **determinant** functor on objects (Müger Lemmas 2.45–2.53), as an interface:
every object has a one-dimensional determinant `det X`, multiplicative in the sense
`det (X ⊕ Y) ≅ det X ⊗ det Y`.  The construction (the top antisymmetrizer of
`TensorPower` and its splitting) is the deferred content of §2; the API is fixed here. -/
class HasDeterminant (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidSymmetricDaggerCategory C] [CStarLinearCategory C]
    [∀ X Y : C, CompleteSpace (X ⟶ Y)] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    [STCStar C] where
  /-- The determinant object `det X`. -/
  det : C → C
  /-- The determinant is **one-dimensional**: `dim (det X) = 1`. -/
  det_dim : ∀ X : C, STCStar.dim (det X) = 1
  /-- The determinant is **multiplicative** over direct sums: `det (X ⊕ Y) ≅ det X ⊗ det Y`. -/
  det_biprod : ∀ X Y : C, Nonempty (det (X ⊞ Y) ≅ det X ⊗ det Y)

end CategoryTheory
