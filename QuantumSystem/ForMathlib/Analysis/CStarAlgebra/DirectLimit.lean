module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# The C⋆-inductive limit of a directed system of C⋆-algebras

For a directed system of (complex) C⋆-algebras whose connecting maps are *injective* unital
`*`-homomorphisms, the connecting maps are isometric (`NonUnitalStarAlgHom.norm_map`), so the
algebraic direct limit carries a well-defined C⋆-norm `‖⟦⟨i, x⟩⟧‖ = ‖x‖`. Its completion is the
**C⋆-inductive limit** (Bratteli–Robinson Vol.1 §2.6), a `CStarAlgebra`.

This file provides the norm `cstarNorm`, the bundled `cstarRingNorm`, and the resulting
`NormedRing` structure (`cstarNormedRing`) on `DirectLimit F f`, all parametrised by injectivity
of the connecting maps. The `*`-algebra-over-`ℂ` structure is supplied by `DirectLimitStar`.

These are general facts and are candidates for upstreaming to Mathlib.
-/

@[expose] public section

namespace DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {F : ι → Type*}
  {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
  [∀ i j (h : i ≤ j), FunLike (T h) (F i) (F j)] [DirectedSystem F (f · · ·)]
  [∀ i, CStarAlgebra (F i)] [∀ i j (h : i ≤ j), AlgHomClass (T h) ℂ (F i) (F j)]
  [∀ i j (h : i ≤ j), StarHomClass (T h) (F i) (F j)]
  (hf : ∀ i j (h : i ≤ j), Function.Injective (f i j h))

/-- The C⋆-norm on the direct limit: `‖⟦⟨i, x⟩⟧‖ = ‖x‖`, well defined since the connecting maps —
    being injective unital `*`-homomorphisms of C⋆-algebras — are isometric
    (`NonUnitalStarAlgHom.norm_map`). -/
noncomputable def cstarNorm : DirectLimit F f → ℝ :=
  DirectLimit.lift f (fun _ x => ‖x‖)
    (fun i j h x => (NonUnitalStarAlgHom.norm_map (f i j h) (hf i j h) x).symm)

omit [Nonempty ι] in
@[simp] theorem cstarNorm_mk (i) (x : F i) :
    cstarNorm hf (⟦⟨i, x⟩⟧ : DirectLimit F f) = ‖x‖ := rfl

/-- The bundled ring norm on the direct limit. -/
noncomputable def cstarRingNorm : RingNorm (DirectLimit F f) where
  toFun := cstarNorm hf
  map_zero' := by
    rw [show (0 : DirectLimit F f) = ⟦⟨Classical.arbitrary _, 0⟩⟧ from
      DirectLimit.zero_def _, cstarNorm_mk, norm_zero]
  add_le' a b := by
    induction a, b using DirectLimit.induction₂ with
    | _ i x y => rw [DirectLimit.add_def, cstarNorm_mk, cstarNorm_mk, cstarNorm_mk]
                 exact norm_add_le x y
  neg' a := by
    induction a using DirectLimit.induction with
    | _ i x => rw [DirectLimit.neg_def, cstarNorm_mk, cstarNorm_mk, norm_neg]
  mul_le' a b := by
    induction a, b using DirectLimit.induction₂ with
    | _ i x y => rw [DirectLimit.mul_def, cstarNorm_mk, cstarNorm_mk, cstarNorm_mk]
                 exact norm_mul_le x y
  eq_zero_of_map_eq_zero' a := by
    induction a using DirectLimit.induction with
    | _ i x =>
      intro hx
      rw [cstarNorm_mk, norm_eq_zero] at hx
      rw [hx]
      exact (DirectLimit.zero_def i).symm

/-- The `NormedRing` structure on the direct limit induced by the C⋆-norm. -/
@[reducible] noncomputable def cstarNormedRing : NormedRing (DirectLimit F f) :=
  (cstarRingNorm hf).toNormedRing

end DirectLimit
