module

public import Mathlib.CategoryTheory.Retract
public import QuantumSystem.Algebra.Sector.Category.CStarCategory

/-!
# Subobjects of endomorphisms: splitting projections

A C\*-tensor category is **closed under subobjects** (Müger §1.6): every projection
`e : ρ ⟶ ρ` (an idempotent, self-adjoint intertwiner) splits, i.e. there is an
object `ρ_e` and morphisms `ρ_e ⇄ ρ` exhibiting `ρ_e` as the image of `e`.

In the concrete model `StarEndoCat A`, the projection `e` has an underlying
projection `e.t ∈ A` (`e.t² = e.t = e.t⋆`).  It splits as soon as `A` contains an
isometry `w` whose range projection is `e.t`:

```
w⋆ w = 1,   w w⋆ = e.t.
```

(Such `w` exists when `A` is properly infinite — e.g. the quasi-local algebra of an
infinite system — where any projection equivalent to `1` is the range of an
isometry.)  Given `w`, the **subobject** is `ρ_e(a) := w⋆ ρ(a) w`, a unital
`*`-endomorphism, and `w : ρ_e ⟶ ρ`, `w⋆ : ρ ⟶ ρ_e` satisfy

```
(w⋆ : ρ ⟶ ρ_e) ≫ (w : ρ_e ⟶ ρ) = e,    (w : ρ_e ⟶ ρ) ≫ (w⋆ : ρ ⟶ ρ_e) = 𝟙 ρ_e,
```

so `e` splits through `ρ_e`.  This is the subobject half of the C\*-completeness
required by the Doplicher–Roberts reconstruction (Müger Theorem 2.18) — in
particular the device that extracts a conjugate from the antisymmetric projection
on a tensor power.

## References

* Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.6.
* Doplicher, Roberts, *A new duality theory for compact groups*, Invent. Math.
  98 (1989).
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ### Splitting data for a projection -/

/-- **Splitting data** for an intertwiner `e : ρ ⟶ ρ`: an isometry `w ∈ A` whose
range projection is `e.t`.  Its existence (a properly-infinite property of `A`)
makes the projection `e` split.  Note `e.t = w w⋆` is automatically idempotent and
self-adjoint, and `e` is automatically an intertwiner, so this is genuinely the
datum that `e` splits. -/
structure SplitData {ρ : StarEndoCat A} (e : ρ ⟶ ρ) where
  /-- The realising isometry. -/
  w : A
  /-- `w` is an isometry. -/
  isom : star w * w = 1
  /-- The range projection of `w` is `e.t`. -/
  range : w * star w = e.t

namespace SplitData

variable {ρ : StarEndoCat A} {e : ρ ⟶ ρ} (s : SplitData e)

/-- `w w⋆ w = w`: the isometry absorbs its range projection. -/
lemma w_range_w : s.w * star s.w * s.w = s.w := by rw [mul_assoc, s.isom, mul_one]

/-- The range projection `w w⋆ = e.t` commutes with `ρ` (it is an intertwiner). -/
lemma range_comm (a : A) : (s.w * star s.w) * ρ.endo a = ρ.endo a * (s.w * star s.w) := by
  rw [s.range]; exact e.intertwines a

/-! ### The subobject endomorphism -/

/-- The underlying `*`-homomorphism of the subobject `ρ_e`: `a ↦ w⋆ ρ(a) w`. -/
noncomputable def subHom : A →⋆ₐ[ℂ] A where
  toFun a := star s.w * ρ.endo a * s.w
  map_one' := by rw [map_one, mul_one, s.isom]
  map_mul' a b := by
    rw [map_mul,
      show (star s.w * ρ.endo a * s.w) * (star s.w * ρ.endo b * s.w)
        = star s.w * ρ.endo a * ((s.w * star s.w) * ρ.endo b) * s.w from by noncomm_ring,
      s.range_comm,
      show star s.w * ρ.endo a * (ρ.endo b * (s.w * star s.w)) * s.w
        = star s.w * (ρ.endo a * ρ.endo b) * (s.w * star s.w * s.w) from by noncomm_ring,
      s.w_range_w]
  map_zero' := by rw [map_zero, mul_zero, zero_mul]
  map_add' a b := by rw [map_add]; noncomm_ring
  commutes' r := by
    rw [AlgHomClass.commutes ρ.endo r, ← Algebra.commutes r (star s.w), mul_assoc, s.isom, mul_one]
  map_star' a := by
    simp only [star_mul, star_star, map_star, mul_assoc]

/-- The **subobject** `ρ_e` of `ρ` cut out by the projection `e` (with splitting
data `s`): the unital `*`-endomorphism `a ↦ w⋆ ρ(a) w`. -/
noncomputable def subEndo : StarEndoCat A := ⟨s.subHom⟩

@[simp] lemma subEndo_endo_apply (a : A) : s.subEndo.endo a = star s.w * ρ.endo a * s.w := rfl

/-! ### The splitting morphisms -/

/-- The inclusion `ρ_e ⟶ ρ` of the subobject, with underlying element `w`. -/
noncomputable def incl : s.subEndo ⟶ ρ where
  t := s.w
  intertwines a := by
    rw [subEndo_endo_apply,
      show s.w * (star s.w * ρ.endo a * s.w) = (s.w * star s.w) * ρ.endo a * s.w from by
        noncomm_ring,
      s.range_comm,
      show ρ.endo a * (s.w * star s.w) * s.w = ρ.endo a * (s.w * star s.w * s.w) from by
        noncomm_ring,
      s.w_range_w]

/-- The projection `ρ ⟶ ρ_e` onto the subobject, with underlying element `w⋆`. -/
noncomputable def proj : ρ ⟶ s.subEndo where
  t := star s.w
  intertwines a := by
    rw [subEndo_endo_apply,
      show (star s.w * ρ.endo a * s.w) * star s.w
        = star s.w * (ρ.endo a * (s.w * star s.w)) from by noncomm_ring,
      ← s.range_comm a,
      show star s.w * ((s.w * star s.w) * ρ.endo a) = (star s.w * (s.w * star s.w)) * ρ.endo a
        from by noncomm_ring,
      show star s.w * (s.w * star s.w) = star s.w from by
        rw [← mul_assoc, s.isom, one_mul]]

@[simp] lemma incl_t : s.incl.t = s.w := rfl
@[simp] lemma proj_t : s.proj.t = star s.w := rfl

/-- **The subobject is a retract of `ρ`**: `incl ≫ proj = 𝟙 ρ_e`. -/
lemma incl_proj : s.incl ≫ s.proj = 𝟙 s.subEndo :=
  Intertwiner.ext <| by rw [comp_t, proj_t, incl_t, id_t]; exact s.isom

/-- **The projection `e` splits through `ρ_e`**: `proj ≫ incl = e`. -/
lemma proj_incl : s.proj ≫ s.incl = e :=
  Intertwiner.ext <| by rw [comp_t, incl_t, proj_t]; exact s.range

/-- The subobject `ρ_e` is a **retract** of `ρ` (Mathlib `CategoryTheory.Retract`),
via the inclusion and projection. -/
noncomputable def retract : Retract s.subEndo ρ where
  i := s.incl
  r := s.proj
  retract := s.incl_proj

end SplitData

/-! ### The antisymmetric projection of a self-adjoint involution

The projection that `SplitData` splits arises, in the Doplicher–Roberts
construction, as the **antisymmetric projection** of a symmetry: when `s` is the
statistics operator `ε` of a sector with permutation (`ε² = 𝟙`) statistics, the
self-adjoint idempotent `½(𝟙 - s)` projects a tensor power onto its antisymmetric
part, whose splitting carries the conjugate (Müger §1.4–1.6).  The construction is
abstract — it needs only a self-adjoint involution in the C\*-category. -/

variable {X : StarEndoCat A}

/-- The **antisymmetric projection** `½(𝟙 - s)` of a self-adjoint involution
`s : X ⟶ X`.  It is a projection precisely when `s` is self-adjoint (`s† = s`) and
an involution (`s ≫ s = 𝟙`); see `reflectionProjection_dagger` and
`reflectionProjection_comp`. -/
noncomputable def reflectionProjection (s : X ⟶ X) : X ⟶ X := (2⁻¹ : ℂ) • (𝟙 X - s)

@[simp] lemma reflectionProjection_t (s : X ⟶ X) :
    (reflectionProjection s).t = (2⁻¹ : ℂ) • (1 - s.t) := by
  simp only [reflectionProjection]
  rw [smul_t, sub_t, id_t]

/-- The antisymmetric projection is **self-adjoint** when `s` is. -/
lemma reflectionProjection_dagger {s : X ⟶ X} (hsa : s† = s) :
    (reflectionProjection s)† = reflectionProjection s := by
  have hst : star s.t = s.t := by
    have h := congrArg Intertwiner.t hsa; rwa [dagger_t] at h
  apply Intertwiner.ext
  simp only [dagger_t, reflectionProjection_t]
  rw [star_smul, star_sub, star_one, hst]
  simp

/-- The antisymmetric projection is **idempotent** when `s` is an involution, so
together with `reflectionProjection_dagger` it is a genuine projection. -/
lemma reflectionProjection_comp {s : X ⟶ X} (hinv : s ≫ s = 𝟙 X) :
    reflectionProjection s ≫ reflectionProjection s = reflectionProjection s := by
  have hss : s.t * s.t = 1 := by
    have h := congrArg Intertwiner.t hinv; rwa [comp_t, id_t] at h
  apply Intertwiner.ext
  simp only [comp_t, reflectionProjection_t]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    show (1 - s.t) * (1 - s.t) = 1 - s.t - s.t + s.t * s.t from by noncomm_ring, hss]
  module

/-- The reflection projection `½(𝟙 - s)` of a self-adjoint involution `s` is a
**positive** endomorphism: it is a self-adjoint idempotent (`reflectionProjection_comp`,
`reflectionProjection_dagger`), hence positive by `IsPositiveEndo.of_projection`.  This
links the antisymmetric subobject construction (R3) to C\*-positivity (R7-B). -/
lemma reflectionProjection_isPositive {s : X ⟶ X} (hsa : s† = s) (hinv : s ≫ s = 𝟙 X) :
    IsPositiveEndo (reflectionProjection s) :=
  IsPositiveEndo.of_projection (reflectionProjection_comp hinv)
    (reflectionProjection_dagger hsa)

end StarEndo

end CategoryTheory
