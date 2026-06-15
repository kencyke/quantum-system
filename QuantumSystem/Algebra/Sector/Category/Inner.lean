module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import QuantumSystem.Algebra.Sector.Category.Statistics

/-!
# Inner endomorphisms `Ad u` of `End(A)`

For a unitary `u` of a C\*-algebra `A`, conjugation `Ad u : a ↦ u · a · u⋆` is a
unital `*`-automorphism of `A` (Mathlib's `Unitary.conjStarAlgAut`), hence an
object of the endomorphism category `StarEndoCat A`.

This is developed at the **abstract** C\*-algebra level (any `CStarAlgebra A`):
the algebraic facts — the apply formula and that `Ad u`, `Ad v` commute whenever
`u`, `v` commute — are proved here once, with `A` a free variable (so typeclass
synthesis is cheap).  The net-level consequences (localisation, the disjoint
locality theorem) are instantiated with `A := quasiLocal L Ω` in `Sector/Net/`.
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

/-! ### Conjugation algebra (general monoid) -/

/-- Conjugation by `u` (with right inverse `w`, `w · u = 1`) distributes over
multiplication. -/
theorem cAd_mul {M : Type*} [Monoid M] (u a b w : M) (h : w * u = 1) :
    u * (a * b) * w = (u * a * w) * (u * b * w) := by
  rw [← mul_assoc (u * a * w) (u * b) w, mul_assoc (u * a) w (u * b),
    ← mul_assoc w u b, h, one_mul, mul_assoc u a b]

/-- Two conjugations `Ad u`, `Ad v` commute when the elements `u`, `v` commute. -/
theorem cAd_comm {M : Type*} [Monoid M] [StarMul M] (u v a : M) (huv : u * v = v * u) :
    u * (v * a * star v) * star u = v * (u * a * star u) * star v := by
  have hsuv : star v * star u = star u * star v := by
    rw [← star_mul, ← star_mul, huv]
  calc u * (v * a * star v) * star u
      = u * v * a * (star v * star u) := by simp only [mul_assoc]
    _ = v * u * a * (star u * star v) := by rw [huv, hsuv]
    _ = v * (u * a * star u) * star v := by simp only [mul_assoc]

/-! ### Inner endomorphisms -/

variable {A : Type*} [CStarAlgebra A]

/-- The **inner endomorphism** `Ad u : a ↦ u · a · u⋆` of a unitary `u`, as an
object of `StarEndoCat A` (the `*`-automorphism `Unitary.conjStarAlgAut`). -/
noncomputable def innerEndo (u : A) (hu : u ∈ unitary A) : StarEndoCat A where
  endo := (Unitary.conjStarAlgAut ℂ A ⟨u, hu⟩ : A →⋆ₐ[ℂ] A)

@[simp] lemma innerEndo_endo_apply (u : A) (hu : u ∈ unitary A) (a : A) :
    (innerEndo u hu).endo a = u * a * star u := by
  change (Unitary.conjStarAlgAut ℂ A ⟨u, hu⟩) a = u * a * star u
  exact Unitary.conjStarAlgAut_apply ⟨u, hu⟩ a

/-- **Commuting inner endomorphisms.**  If `u`, `v` commute then so do `Ad u`,
`Ad v` (this is the abstract core of the inner-case locality theorem). -/
lemma commutes_innerEndo_of_commute {u v : A} (hu : u ∈ unitary A) (hv : v ∈ unitary A)
    (huv : u * v = v * u) :
    Commutes (innerEndo u hu) (innerEndo v hv) := by
  intro a
  simp only [innerEndo_endo_apply]
  exact cAd_comm u v a huv

end StarEndo

end CategoryTheory
