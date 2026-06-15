module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.STCStar

/-!
# Simple objects, Schur's lemma and semisimplicity — S6 (R7-B3 + A6)

In a C\*-tensor category (Müger, *Abstract Duality Theory for Symmetric Tensor
∗-Categories*, §1.5) an object `X` is **simple** (irreducible) when its
endomorphism algebra is one-dimensional, `End X = ℂ · 𝟙` (Müger Definition 1.32).
The two structural facts proved here are entirely C\*-analytic and need no further
hypotheses beyond the C\*-linear enrichment:

* **Schur's lemma** (`isIso_of_isSimpleObject`): a nonzero morphism between simple
  objects is an isomorphism.  The proof is the standard C\*-argument: for `f ≠ 0`
  the positive endomorphism `f ≫ f†` is a *nonzero* scalar `c • 𝟙` (the C\*-identity
  `‖f ≫ f†‖ = ‖f‖²` forces `c ≠ 0`), so `c⁻¹ • f†` is a right inverse; an idempotent
  argument on the simple codomain promotes it to a two-sided inverse.
* **the monoidal unit is simple** (`unit_isSimple`): this is exactly
  `STCStar.irreducible_unit`.

The **semisimplicity** of the category — that every object is a finite orthogonal
direct sum of simple objects (Müger §1.5, the substantive existence statement that
rests on finite-dimensionality of hom-spaces) — is captured as the hypothesis class
`IsSemisimple`, with the decomposition packaged diamond-free (no zero object) as
`SimpleDecomposition`.  This is the entry point of **Phase 1** of the Tannaka
roadmap (`implementation-notes.md` §4, S6); the standard-solution construction (S7)
and the dimension theory (S8) consume it.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u

/-! ### Simple objects -/

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]

/-- An object `X` is **simple** (irreducible, Müger Definition 1.32): every
endomorphism is a scalar multiple of the identity, `End X = ℂ · 𝟙`.  For the
monoidal unit this is `STCStar.irreducible_unit`. -/
def IsSimpleObject (X : C) : Prop :=
  ∀ f : X ⟶ X, ∃ c : ℂ, f = c • 𝟙 X

/-- The defining scalar of an endomorphism of a simple object. -/
lemma IsSimpleObject.exists_scalar {X : C} (hX : IsSimpleObject X) (f : X ⟶ X) :
    ∃ c : ℂ, f = c • 𝟙 X := hX f

section Dagger

variable [DaggerCategory C]

/-! ### Orthonormal decomposition into simples -/

/-- A finite **orthonormal decomposition of `X` into simple objects** (Müger §1.5):
a family of isometric inclusions `incl i : Sᵢ ⟶ X` of simple objects `Sᵢ` whose
range projections `inclᵢ† ≫ inclᵢ` are mutually orthogonal and sum to `𝟙 X`.

This is the diamond-free (zero-object-free) packaging of "`X ≅ ⊕ᵢ Sᵢ`" suited to a
C\*-category: the data is an orthonormal system of partial isometries summing to the
identity, exactly the internal direct-sum datum used elsewhere in this development
(`StarEndo.IsometryPair`).  Composition is diagrammatic (`(f ≫ g).t = g.t * f.t`),
so `incl ≫ incl†` is an endomorphism of `Sᵢ` (the isometry relation) and
`incl† ≫ incl` an endomorphism of `X` (the range projection). -/
structure SimpleDecomposition (X : C) where
  /-- The number of simple summands. -/
  n : ℕ
  /-- The simple summands `Sᵢ`. -/
  obj : Fin n → C
  /-- Each summand is simple. -/
  simple : ∀ i, IsSimpleObject (obj i)
  /-- The isometric inclusions `Sᵢ ⟶ X`. -/
  incl : ∀ i, obj i ⟶ X
  /-- Each inclusion is an isometry: `inclᵢ ≫ inclᵢ† = 𝟙 Sᵢ`. -/
  isometry : ∀ i, incl i ≫ (incl i)† = 𝟙 (obj i)
  /-- Distinct inclusions have orthogonal ranges: `inclᵢ ≫ inclⱼ† = 0` for `i ≠ j`. -/
  orthogonal : ∀ {i j}, i ≠ j → incl i ≫ (incl j)† = 0
  /-- The range projections are **complete**: `∑ᵢ inclᵢ† ≫ inclᵢ = 𝟙 X`. -/
  complete : ∑ i, (incl i)† ≫ incl i = 𝟙 X

namespace SimpleDecomposition

variable {X : C} (d : SimpleDecomposition X)

/-- The range **projection** onto the `i`-th simple summand, `pᵢ = inclᵢ† ≫ inclᵢ : X ⟶ X`. -/
def proj (i : Fin d.n) : X ⟶ X := (d.incl i)† ≫ d.incl i

/-- Each range projection is **self-adjoint**: `pᵢ† = pᵢ`. -/
lemma proj_selfAdjoint (i : Fin d.n) : (d.proj i)† = d.proj i := by
  simp only [proj, DaggerCategory.dagger_comp, DaggerCategory.dagger_dagger]

/-- Each range projection is **idempotent**: `pᵢ ≫ pᵢ = pᵢ`, using the isometry relation. -/
lemma proj_idempotent (i : Fin d.n) : d.proj i ≫ d.proj i = d.proj i := by
  simp only [proj, Category.assoc]
  rw [← Category.assoc (d.incl i) ((d.incl i)†) (d.incl i), d.isometry, Category.id_comp]

end SimpleDecomposition

/-- The category is **semisimple** (Müger §1.5): every object has a finite
orthonormal decomposition into simple objects.  This existence statement rests on
the finite-dimensionality of the hom-spaces of a C\*-tensor category; it is carried
as a hypothesis class here and discharged for concrete categories.  The
standard-solution construction (S7) and the dimension additivity (S8) are stated
relative to `[IsSemisimple C]`. -/
class IsSemisimple (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] : Prop where
  /-- Every object admits a finite orthonormal decomposition into simple objects. -/
  nonempty_simpleDecomposition : ∀ X : C, Nonempty (SimpleDecomposition X)

/-- A chosen simple decomposition of an object in a semisimple category. -/
noncomputable def simpleDecomposition [IsSemisimple C] (X : C) : SimpleDecomposition X :=
  (IsSemisimple.nonempty_simpleDecomposition X).some

end Dagger

/-! ### Schur's lemma -/

section Schur

variable [MonoidalCategory C] [DaggerCategory C] [CStarLinearCategory C]

/-- **Schur's lemma** (Müger §1.5): a nonzero morphism between simple objects is an
isomorphism.  The positive endomorphism `f ≫ f†` of the simple source is a scalar
`c • 𝟙` with `c ≠ 0` (the C\*-identity `‖f ≫ f†‖ = ‖f‖²` rules out `c = 0`), so
`g = c⁻¹ • f†` is a right inverse of `f`.  On the simple codomain `g ≫ f` is a scalar
idempotent, hence `0` or `𝟙`; the former would force `f = 0`, so `g ≫ f = 𝟙` and `f`
is invertible. -/
theorem isIso_of_isSimpleObject {X Y : C} (hX : IsSimpleObject X) (hY : IsSimpleObject Y)
    {f : X ⟶ Y} (hf : f ≠ 0) : IsIso f := by
  have hY0 : (𝟙 Y : Y ⟶ Y) ≠ 0 := fun h => hf (by rw [← Category.comp_id f, h, comp_zero])
  obtain ⟨c, hc⟩ := hX (f ≫ f†)
  have hc0 : c ≠ 0 := by
    intro hc0'
    refine hf (norm_eq_zero.mp ?_)
    have hnorm : ‖f‖ ^ 2 = 0 := by
      have h1 : ‖f‖ ^ 2 = ‖f ≫ f†‖ := by
        simp only [CStarLinearCategory.norm_eq_homNorm, CStarLinearCategory.norm_comp_dagger]
      rw [h1, hc, hc0', zero_smul, norm_zero]
    rw [pow_two] at hnorm
    exact mul_self_eq_zero.mp hnorm
  set g : Y ⟶ X := c⁻¹ • f† with hg
  have hfg : f ≫ g = 𝟙 X := by
    rw [hg, Linear.comp_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨⟨g, hfg, ?_⟩⟩
  obtain ⟨e, he⟩ := hY (g ≫ f)
  have hidem : (g ≫ f) ≫ (g ≫ f) = g ≫ f := by
    rw [Category.assoc, ← Category.assoc f g f, hfg, Category.id_comp]
  have hee : (e * e) • 𝟙 Y = e • 𝟙 Y := by
    have h1 : (g ≫ f) ≫ (g ≫ f) = (e * e) • 𝟙 Y := by
      rw [he, Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul]
    rw [← h1, hidem, he]
  have he2 : e * e = e := CStarCategory.smul_id_inj (norm_ne_zero_iff.mpr hY0) hee
  have hfac : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he2, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h1
  · exfalso
    apply hf
    have hgf0 : g ≫ f = 0 := by rw [he, h0, zero_smul]
    calc f = (f ≫ g) ≫ f := by rw [hfg, Category.id_comp]
      _ = f ≫ (g ≫ f) := Category.assoc f g f
      _ = f ≫ 0 := by rw [hgf0]
      _ = 0 := comp_zero
  · rw [he, sub_eq_zero.mp h1, one_smul]

/-- A morphism between simple objects that is **not** an isomorphism is zero (the
vanishing half of Schur's lemma): non-isomorphic simple objects have no nonzero
morphisms between them. -/
theorem eq_zero_of_not_isIso {X Y : C} (hX : IsSimpleObject X) (hY : IsSimpleObject Y)
    {f : X ⟶ Y} (h : ¬ IsIso f) : f = 0 := by
  by_contra hf
  exact h (isIso_of_isSimpleObject hX hY hf)

end Schur

/-! ### The monoidal unit is simple -/

section Unit

variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidSymmetricDaggerCategory C] [CStarLinearCategory C]
    [∀ X Y : C, CompleteSpace (X ⟶ Y)]
    [HasBinaryBiproducts C] [IsIdempotentComplete C] [STCStar C]

/-- The **monoidal unit is simple** (Müger Definition 1.32): `End 𝟙 = ℂ · 𝟙`.  This
is exactly `STCStar.irreducible_unit`, the irreducibility of the unit that defines an
`STCStar`. -/
theorem unit_isSimple : IsSimpleObject (𝟙_ C) :=
  STCStar.irreducible_unit

end Unit

end CategoryTheory
