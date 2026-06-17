module

public import QuantumSystem.Algebra.Sector.Category.CStarLinearCategory
public import QuantumSystem.Algebra.Sector.Category.DaggerLinear

/-!
# `StarEndoCat A` is dagger-linear and C\*-linear

Discharges the two abstract analytic interfaces `DaggerLinear` and
`CStarLinearCategory` on the concrete endomorphism category `StarEndoCat A` of a
(nontrivial) C\*-algebra `A`.  Every axiom is a theorem of the C\*-algebra `A`:

* the dagger is the adjoint `star` on the underlying elements, hence additive and
  conjugate-`ℂ`-linear (`star_add`, `StarEndo.dagger_smul`);
* the hom-norm is the operator norm `‖·‖` of the underlying element, which is
  non-negative, `ℂ`-homogeneous, subadditive, definite, submultiplicative under
  composition (`norm_mul_le`), and satisfies the C\*-identity
  (`CStarRing.norm_star_mul_self`, packaged as `StarEndo.norm_comp_dagger`);
* the monoidal unit's identity has underlying element `1`, of nonzero norm
  whenever `A` is nontrivial.

These instances turn the previously dormant interfaces into proven facts: `End(A)`
is a genuine C\*-linear category.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

namespace StarEndo

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The dagger of `StarEndoCat A` is conjugate-linear (additive and
conjugate-`ℂ`-homogeneous): it is the adjoint `star` on the underlying elements
of `A`. -/
instance : DaggerLinear (StarEndoCat A) where
  dagger_add f g := by
    apply Intertwiner.ext
    change star (f.t + g.t) = star f.t + star g.t
    exact star_add f.t g.t
  dagger_smul c f := StarEndo.dagger_smul c f

/-- `StarEndoCat A` is a **C\*-linear category** when `A` is nontrivial: the
hom-norm is the operator norm, submultiplicative under composition and satisfying
the C\*-identity, and the monoidal unit's identity (underlying element `1`) has
nonzero norm. -/
noncomputable instance [Nontrivial A] : CStarLinearCategory (StarEndoCat A) where
  homNorm f := ‖f‖
  norm_nonneg f := _root_.norm_nonneg f
  norm_smul c f := _root_.norm_smul c f
  norm_triangle f g := norm_add_le f g
  norm_eq_zero_iff f := norm_eq_zero
  norm_comp_le f g := by
    calc ‖f ≫ g‖ = ‖g.t * f.t‖ := by rw [norm_t, comp_t]
      _ ≤ ‖g.t‖ * ‖f.t‖ := norm_mul_le _ _
      _ = ‖f‖ * ‖g‖ := by rw [norm_t f, norm_t g]; exact mul_comm _ _
  norm_comp_dagger f := StarEndo.norm_comp_dagger f
  unit_id_norm_ne_zero := by
    change ‖𝟙 (𝟙_ (StarEndoCat A))‖ ≠ 0
    rw [norm_t, id_t]
    exact norm_ne_zero_iff.mpr one_ne_zero

end StarEndo

end CategoryTheory
