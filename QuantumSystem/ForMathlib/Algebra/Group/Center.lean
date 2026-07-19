module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Centralizers under multiplicative bijections

A multiplicative bijection carries the centralizer of a set onto the centralizer of the image.
This is the algebraic core of the fact that a spatial isomorphism of von Neumann algebras
commutes with taking commutants.
-/

@[expose] public section

/-- A multiplicative bijection carries the centralizer of a set onto the centralizer of the image:
`φ '' s' = (φ '' s)'`. -/
theorem Set.image_centralizer {M₁ M₂ F : Type*} [Mul M₁] [Mul M₂]
    [EquivLike F M₁ M₂] [MulEquivClass F M₁ M₂] (φ : F) (s : Set M₁) :
    ⇑φ '' Set.centralizer s = Set.centralizer (⇑φ '' s) := by
  ext y
  simp only [Set.mem_image, Set.mem_centralizer_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, hx a ha]
  · intro hy
    obtain ⟨x, rfl⟩ := EquivLike.surjective φ y
    refine ⟨x, fun a ha => ?_, rfl⟩
    have h := hy (φ a) ⟨a, ha, rfl⟩
    apply EquivLike.injective φ
    rw [map_mul, map_mul, h]
