module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.GlobalHilbert

/-!
# Region embeddings into the global Hilbert space (Phase 5'a step 4)

For each finite region `Λ : Finset L` we construct the canonical isometric
embedding

`regionEmbed Λ : regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L`

following Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2 §2.7.2.
The construction extends each region tuple `f : (s : Λ) → localIdx s` to a
global tuple by filling outside-`Λ` coordinates with the chosen reference
basis index, then maps the corresponding `EuclideanSpace`-basis vector of
`regionHilbert Λ` to the `lp.single` vector of `globalHilbert L`.  The
extended tuples are pairwise distinct, so the image vectors form an
orthonormal family in `globalHilbert L`, which yields a linear isometry via
`LinearMap.isometryOfOrthonormal`.

## Main definitions

* `LocalNetLike.extendRegionTuple Λ f` — extension of a region tuple to a
  global tuple by filling outside-`Λ` coordinates with `referenceBasis L`.
* `LocalNetLike.regionEmbed Λ` — the isometric embedding
  `regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- Equality on `globalIdx L` is classically decidable; we register this as a
noncomputable instance so that `lp.single 2 (· : globalIdx L) 1` is well-typed
in the embedding below. -/
noncomputable instance instDecidableEqGlobalIdx : DecidableEq (globalIdx L) :=
  Classical.decEq _

/-- Extension of a region tuple `f : regionIdx Λ` to a global tuple in
`globalIdx L` by filling sites outside `Λ` with the reference basis index. -/
noncomputable def extendRegionTuple (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    globalIdx L :=
  ⟨fun s => if h : s ∈ Λ then f ⟨s, h⟩ else referenceBasis L s,
   ⟨Λ, fun _ hs => dif_neg hs⟩⟩

@[simp]
theorem extendRegionTuple_val_apply_of_mem (Λ : Finset L)
    (f : regionIdx (L := L) Λ) {s : L} (hs : s ∈ Λ) :
    (extendRegionTuple Λ f).val s = f ⟨s, hs⟩ :=
  dif_pos hs

theorem extendRegionTuple_val_apply_of_not_mem (Λ : Finset L)
    (f : regionIdx (L := L) Λ) {s : L} (hs : s ∉ Λ) :
    (extendRegionTuple Λ f).val s = referenceBasis L s :=
  dif_neg hs

/-- The extension `extendRegionTuple Λ` is injective. -/
theorem extendRegionTuple_injective (Λ : Finset L) :
    Function.Injective (extendRegionTuple (L := L) Λ) := by
  intro f g h
  ext ⟨s, hs⟩
  have hval : (extendRegionTuple Λ f).val = (extendRegionTuple Λ g).val :=
    congrArg Subtype.val h
  have := congrFun hval s
  simpa [extendRegionTuple_val_apply_of_mem, hs] using this

/-- Image of a region tuple under the embedding: `lp.single 2 (extendRegionTuple Λ f) 1`,
viewed as an element of `globalHilbert L`. -/
noncomputable def regionEmbedTarget (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    globalHilbert L :=
  lp.single 2 (extendRegionTuple Λ f) (1 : ℂ)

/-- The image vectors `regionEmbedTarget Λ f` form an orthonormal family in
`globalHilbert L`. -/
theorem orthonormal_regionEmbedTarget (Λ : Finset L) :
    Orthonormal ℂ (regionEmbedTarget (L := L) Λ) := by
  rw [orthonormal_iff_ite]
  intro f g
  simp only [regionEmbedTarget]
  rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases hfg : f = g
  · subst hfg; simp
  · have hne : extendRegionTuple Λ f ≠ extendRegionTuple Λ g :=
      fun h => hfg (extendRegionTuple_injective Λ h)
    rw [if_neg hne, if_neg hfg]
    simp

/-- Auxiliary linear map underlying `regionEmbed`: defined on the standard
basis of `regionHilbert Λ` by sending each basis vector to the corresponding
`lp.single` vector in `globalHilbert L`. -/
noncomputable def regionEmbedAux (Λ : Finset L) :
    regionHilbert (L := L) Λ →ₗ[ℂ] globalHilbert L :=
  (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
    (regionEmbedTarget Λ)

theorem regionEmbedAux_basis (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    regionEmbedAux Λ ((EuclideanSpace.basisFun (regionIdx Λ) ℂ).toBasis f)
      = regionEmbedTarget Λ f :=
  (EuclideanSpace.basisFun (regionIdx Λ) ℂ).toBasis.constr_basis ℂ
    (regionEmbedTarget Λ) f

/-- The isometric embedding `regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L`. -/
noncomputable def regionEmbed (Λ : Finset L) :
    regionHilbert (L := L) Λ →ₗᵢ[ℂ] globalHilbert L :=
  LinearMap.isometryOfOrthonormal (regionEmbedAux Λ)
    (v := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
    (by
      rw [(EuclideanSpace.basisFun (regionIdx Λ) ℂ).coe_toBasis]
      exact (EuclideanSpace.basisFun (regionIdx Λ) ℂ).orthonormal)
    (by
      have hcomp :
          (regionEmbedAux Λ : regionHilbert Λ → globalHilbert L)
              ∘ ((EuclideanSpace.basisFun (regionIdx Λ) ℂ).toBasis : _ → _)
            = regionEmbedTarget Λ := by
        funext f
        exact regionEmbedAux_basis Λ f
      rw [hcomp]
      exact orthonormal_regionEmbedTarget Λ)

end LocalNetLike
