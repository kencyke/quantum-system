module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Embedding

/-!
# Local algebra embedding into `B(globalHilbert L)` (Phase 5'b)

For each finite region `Λ : Finset L` we build the canonical *unital*
`*`-algebra embedding

`localEmbed Λ : (regionHilbert Λ →L[ℂ] regionHilbert Λ) →⋆ₐ[ℂ]
                  (globalHilbert L →L[ℂ] globalHilbert L)`

following Naaijkens 2012 §1.3 and Bratteli–Robinson Vol. 2 §2.7.2: an
operator `M` on the region Hilbert space is sent to `M ⊗ 1_{Λᶜ}`, the
operator on the infinite-site Hilbert space that acts as `M` on the Λ
factor and as the identity on the complement.  In our basis-indexed model
this is realised on basis vectors `e_g = lp.single 2 g 1` by

`localEmbed Λ M (e_g) = ∑_{f : regionIdx Λ} M_{f, g|Λ} e_{(f, g|Λᶜ)}`

where `g|Λ : regionIdx Λ` is the Λ-restriction of the global tuple `g`,
and `(f, g|Λᶜ) : globalIdx L` is the global tuple obtained by replacing
the Λ component of `g` with `f`.

This file installs the structural helpers that make the formula above
well-defined.  The continuous-linear-map upgrade, the `StarAlgHom`
structure, and the resulting `localSubalgebra Λ : StarSubalgebra ℂ _`
are added in subsequent commits.

## Main definitions

* `LocalNetLike.regionRestrict Λ g` — the Λ-restriction
  `g ↦ g|Λ : regionIdx Λ` of a global tuple.
* `LocalNetLike.globalSwap Λ f g` — the global tuple obtained from `g`
  by replacing its Λ component with `f`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- Restrict a global tuple to a finite region `Λ`.  The result
`regionRestrict Λ g : regionIdx Λ` lists `g`'s coordinates at the sites
of `Λ`. -/
def regionRestrict (Λ : Finset L) (g : globalIdx L) : regionIdx (L := L) Λ :=
  fun s => g.val s.1

@[simp]
theorem regionRestrict_apply (Λ : Finset L) (g : globalIdx L) (s : ↥Λ) :
    regionRestrict Λ g s = g.val s.1 := rfl

/-- Replace the Λ component of a global tuple `g` with a region tuple `f`.
The Λᶜ component is left unchanged.  Outside `Λ ∪ Γ`, where `Γ` is any
finite witness for `g`'s finite-variation property, the result still
agrees with the reference basis. -/
noncomputable def globalSwap (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) : globalIdx L :=
  ⟨fun s => if h : s ∈ Λ then f ⟨s, h⟩ else g.val s, by
    obtain ⟨Γ, hΓ⟩ := g.property
    refine ⟨Γ ∪ Λ, fun s hs => ?_⟩
    have hsΛ : s ∉ Λ := fun h => hs (Finset.mem_union_right _ h)
    have hsΓ : s ∉ Γ := fun h => hs (Finset.mem_union_left _ h)
    simp only [dif_neg hsΛ]
    exact hΓ s hsΓ⟩

@[simp]
theorem globalSwap_val_apply_of_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) {s : L} (hs : s ∈ Λ) :
    (globalSwap Λ f g).val s = f ⟨s, hs⟩ :=
  dif_pos hs

@[simp]
theorem globalSwap_val_apply_of_not_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) {s : L} (hs : s ∉ Λ) :
    (globalSwap Λ f g).val s = g.val s :=
  dif_neg hs

/-- Restricting `globalSwap Λ f g` to `Λ` recovers `f`. -/
@[simp]
theorem regionRestrict_globalSwap (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) :
    regionRestrict Λ (globalSwap Λ f g) = f := by
  funext ⟨s, hs⟩
  simp [regionRestrict, globalSwap_val_apply_of_mem _ _ _ hs]

/-- Outside `Λ`, `globalSwap Λ f g` and `g` carry the same coordinates. -/
theorem globalSwap_eq_of_not_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) {s : L} (hs : s ∉ Λ) :
    (globalSwap Λ f g).val s = g.val s :=
  globalSwap_val_apply_of_not_mem Λ f g hs

/-- `globalSwap Λ f g = globalSwap Λ f' g'` exactly when the Λ parts agree
(`f = f'`) and the Λᶜ parts of the underlying global tuples agree. -/
theorem globalSwap_injective_left (Λ : Finset L) (g : globalIdx L) :
    Function.Injective (fun f : regionIdx (L := L) Λ => globalSwap Λ f g) := by
  intro f f' h
  funext ⟨s, hs⟩
  have hval : (globalSwap Λ f g).val = (globalSwap Λ f' g).val :=
    congrArg Subtype.val h
  have := congrFun hval s
  simpa [globalSwap_val_apply_of_mem, hs] using this

/-- The extension `extendRegionTuple Λ f` is exactly `globalSwap Λ f` applied
to the canonical "vacuum" global tuple obtained by extending a region tuple
of the empty region (i.e. the constant `referenceBasis`-tuple). -/
theorem extendRegionTuple_eq_globalSwap_referenceTuple (Λ : Finset L)
    (f : regionIdx (L := L) Λ) :
    extendRegionTuple Λ f =
      globalSwap Λ f ⟨fun s => referenceBasis L s, ⟨∅, fun _ _ => rfl⟩⟩ := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [extendRegionTuple_val_apply_of_mem _ _ hs,
      globalSwap_val_apply_of_mem _ _ _ hs]
  · simp [extendRegionTuple_val_apply_of_not_mem _ _ hs,
      globalSwap_val_apply_of_not_mem _ _ _ hs]

/-- Restoring `g` from `(globalSwap Λ f g, regionRestrict Λ g)`: replacing
the Λ part of `globalSwap Λ f g` with `regionRestrict Λ g` gives back `g`. -/
@[simp]
theorem globalSwap_regionRestrict_globalSwap (Λ : Finset L)
    (f : regionIdx (L := L) Λ) (g : globalIdx L) :
    globalSwap Λ (regionRestrict Λ g) (globalSwap Λ f g) = g := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [globalSwap_val_apply_of_mem _ _ _ hs, regionRestrict]
  · simp [globalSwap_val_apply_of_not_mem _ _ _ hs]

/-- The involution on `globalIdx L × regionIdx Λ` that records the
"swap-and-restrict" pairing: `(g, f) ↔ (globalSwap Λ f g, regionRestrict Λ g)`.
This bijection is the key reindexing tool used to count contributions of
`(M ⊗ 1)`-style operators across complement classes. -/
theorem globalSwap_pair_involutive (Λ : Finset L) :
    Function.Involutive
      (fun gf : globalIdx L × regionIdx (L := L) Λ =>
        (globalSwap Λ gf.2 gf.1, regionRestrict Λ gf.1)) := by
  rintro ⟨g, f⟩
  simp [globalSwap_regionRestrict_globalSwap]

/-- The swap-and-restrict bijection on `globalIdx L × regionIdx Λ`. -/
noncomputable def globalSwapEquiv (Λ : Finset L) :
    globalIdx L × regionIdx (L := L) Λ ≃ globalIdx L × regionIdx (L := L) Λ :=
  (globalSwap_pair_involutive Λ).toPerm

@[simp]
theorem globalSwapEquiv_apply (Λ : Finset L)
    (gf : globalIdx L × regionIdx (L := L) Λ) :
    globalSwapEquiv Λ gf = (globalSwap Λ gf.2 gf.1, regionRestrict Λ gf.1) :=
  rfl

/-! ### Pointwise action of `M ⊗ 1` on global tuples -/

/-- The pointwise coefficients of `(M ⊗ 1_{Λᶜ}) w`: at the global tuple `g`,
`localEmbedCoeff Λ M w g = ∑_{f : regionIdx Λ} M_{g|Λ, f} · w(globalSwap Λ f g)`,
where `M_{a, b} = (M (EuclideanSpace.single b 1)) a` is the matrix element. -/
noncomputable def localEmbedCoeff (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (w : globalHilbert L) (g : globalIdx L) : ℂ :=
  ∑ f : regionIdx (L := L) Λ,
    (M (EuclideanSpace.single f (1 : ℂ))) (regionRestrict Λ g) *
      (w : lp (fun _ : globalIdx L => ℂ) 2) (globalSwap Λ f g)

end LocalNetLike
