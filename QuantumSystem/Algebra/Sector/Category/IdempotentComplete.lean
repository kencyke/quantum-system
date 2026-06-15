module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import QuantumSystem.Algebra.Sector.Category.Subobject
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.IdempotentProjection

/-!
# Idempotent completeness of `End(A)`

A C\*-tensor category is **closed under subobjects** (Müger §1.6): every idempotent
splits.  For `StarEndoCat A` this is `CategoryTheory.IsIdempotentComplete`, and it
holds once `A` is *properly infinite* — precisely, once every projection of `A` is
the range projection of an isometry (`HasIsometryProjections`).

The argument combines the two analytic/structural inputs already in place:

* a general idempotent intertwiner `q` is *similar* to a self-adjoint projection
  `p` (`exists_isStarProjection_similar_of_isIdempotentElem`), with `p q = q`,
  `q p = p`, and `p` inheriting `q`'s intertwining;
* the projection `p`, being the range of an isometry `w`, splits via the subobject
  `SplitData` machinery.

The similarity then transports the splitting of `p` to a splitting of `q`: with
`i = w` (the inclusion of the subobject) and `e = w⋆ q` one has `i ≫ e = 𝟙` and
`e ≫ i = q`.  This is the subobject half of the C\*-completeness required by the
Doplicher–Roberts reconstruction (Müger Theorem 2.18).
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `A` **has isometries for projections** — the properly-infinite property used
for idempotent completeness: every star projection `p` is the range projection of
an isometry (`w⋆ w = 1`, `w w⋆ = p`).  It holds for the quasi-local algebra of an
infinite quantum system and is the existence input discharged by concrete models. -/
class HasIsometryProjections (A : Type u) [CStarAlgebra A] : Prop where
  /-- Every star projection has a witnessing isometry. -/
  exists_isometry : ∀ {p : A}, IsStarProjection p → ∃ w : A, star w * w = 1 ∧ w * star w = p

open CStarAlgebra in
/-- **`End(A)` is idempotent complete** when `A` is properly infinite
(`HasIsometryProjections`).  A general idempotent intertwiner `q` is similar to a
self-adjoint projection `p`; the isometry of `p` splits it, and the similarity
transports the splitting to `q`.  This is the subobject half of C\*-completeness
(Müger §1.6, R9(b)); the `HasIsometryProjections` hypothesis is discharged for
concrete nets (R8). -/
theorem isIdempotentComplete_of_hasIsometryProjections [HasIsometryProjections A] :
    IsIdempotentComplete (StarEndoCat A) where
  idempotents_split ρ q hqq := by
    have hq : q.t * q.t = q.t := by
      have h := congrArg Intertwiner.t hqq; rwa [comp_t] at h
    obtain ⟨p, hp_proj, hpe, hep, hpcomm⟩ :=
      exists_isStarProjection_similar_of_isIdempotentElem (e := q.t) hq
    obtain ⟨w, hw_isom, hw_range⟩ := HasIsometryProjections.exists_isometry hp_proj
    -- `p` is an intertwiner: it commutes with `ρ.endo a` because `q.t` and `star q.t` do
    let pHom : ρ ⟶ ρ :=
      { t := p
        intertwines := fun a =>
          (hpcomm (ρ.endo a) (q.intertwines a).symm ((homDagger q).intertwines a).symm).symm }
    let sd : SplitData pHom := { w := w, isom := hw_isom, range := hw_range }
    -- `q.t` absorbs `w` on the right
    have hqtw : q.t * w = w := by
      have h : q.t * (w * star w) = w * star w := by rw [hw_range, hep]
      calc q.t * w
          = q.t * (w * star w) * w := by
            rw [show q.t * (w * star w) * w = q.t * w * (star w * w) from by noncomm_ring,
              hw_isom, mul_one]
        _ = (w * star w) * w := by rw [h]
        _ = w := by
            rw [show (w * star w) * w = w * (star w * w) from by noncomm_ring, hw_isom, mul_one]
    refine ⟨sd.subEndo, sd.incl, q ≫ sd.proj, ?_, ?_⟩
    · apply Intertwiner.ext
      simp only [comp_t, id_t, SplitData.incl_t, SplitData.proj_t]
      rw [mul_assoc, hqtw, hw_isom]
    · apply Intertwiner.ext
      simp only [comp_t, SplitData.incl_t, SplitData.proj_t]
      rw [← mul_assoc, hw_range, hpe]

end StarEndo

end CategoryTheory
