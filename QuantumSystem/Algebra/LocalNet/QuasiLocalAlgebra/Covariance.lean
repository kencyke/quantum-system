module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.QuasiLocal

/-!
# Group action data for the quasi-local algebra (Phase 5'd kinematics)

We introduce the kinematic data for a `G`-equivariant `LocalNetLike`,
which is the input to the covariance axiom (Verch 2025 §1.2 axiom iii /
Naaijkens 2012 §1.3).  The data parallels `LocalNet.HasGroupAction` but
lives at the `LocalNetLike` level and additionally requires the per-site
equivalences to preserve the reference basis (`referenceBasis L`); that
compatibility is what allows the action to descend to the subtype of
finite-variation tuples `globalIdx L`, on which the operator-algebra
constructions are built.

The combinatorial action on `globalIdx L`, the unitary representation
on `globalHilbert L`, the resulting `*`-algebra automorphism on
`globalHilbert L →L[ℂ] globalHilbert L`, and the full covariance theorem
are the natural follow-ups; the present file installs the structural
data plus the region-image API which they consume.

## Main definitions

* `LocalNetLike.HasGroupAction L G` — group action on sites with per-site
  index equivalences preserving the reference basis.
* `LocalNetLike.HasGroupAction.regionImage g Λ` — the `G`-translate of a
  finite region.
* `LocalNetLike.HasGroupAction.piAction g` — the function-level
  permutation of `(s : L) → localIdx s` induced by the action; promoted
  to `globalIdx L ≃ globalIdx L` in a follow-up commit using the
  reference-basis compatibility.

## References

* Verch 2025 (https://arxiv.org/abs/2507.00900) §1.2 axiom (iii).
* Naaijkens 2012 §1.3.
-/

@[expose] public section

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- **Group action data** for a `LocalNetLike`.  Carries the same fields as
`LocalNet.HasGroupAction` plus a compatibility condition with the chosen
`referenceBasis L`.

* `siteAction g : Equiv.Perm L` — the action on the site set.
* `siteIdxEquiv g s : localIdx s ≃ localIdx (siteAction g s)` — the per-site
  identification of local Hilbert spaces.
* `siteIdxEquiv_referenceBasis` — the per-site identifications send the
  reference basis at `s` to the reference basis at `siteAction g s`.  This
  ensures the action descends to `globalIdx L`. -/
structure HasGroupAction (G : Type*) [Group G] where
  /-- Action on sites as a group hom into permutations. -/
  siteAction : G →* Equiv.Perm L
  /-- Per-site equivalence of local Hilbert-space indices. -/
  siteIdxEquiv : ∀ (g : G) (s : L),
    LocalNetLike.localIdx (L := L) s
      ≃ LocalNetLike.localIdx (L := L) (siteAction g s)
  /-- The action preserves the reference basis. -/
  siteIdxEquiv_referenceBasis :
    ∀ (g : G) (s : L),
      siteIdxEquiv g s (referenceBasis L s) = referenceBasis L (siteAction g s)

namespace HasGroupAction

variable {L}
variable {G : Type*} [Group G]

/-- The `G`-translate of a finite region: the Finset image under `siteAction g`. -/
def regionImage (act : HasGroupAction L G) (g : G) (Λ : Finset L) : Finset L :=
  Λ.image (act.siteAction g)

@[simp]
theorem regionImage_one (act : HasGroupAction L G) (Λ : Finset L) :
    act.regionImage 1 Λ = Λ := by
  unfold regionImage
  rw [act.siteAction.map_one]
  exact Λ.image_id

/-- `regionImage` is multiplicative: `(gh) · Λ = g · (h · Λ)`. -/
theorem regionImage_mul (act : HasGroupAction L G) (g h : G) (Λ : Finset L) :
    act.regionImage (g * h) Λ = act.regionImage g (act.regionImage h Λ) := by
  unfold regionImage
  rw [act.siteAction.map_mul, Finset.image_image]
  rfl

/-- The function-level permutation of `(s : L) → localIdx s` induced by the
action.  This is the un-restricted action on dependent function spaces;
the restriction to the finite-variation subtype `globalIdx L` (using
`siteIdxEquiv_referenceBasis`) is set up in a follow-up commit. -/
noncomputable def piAction (act : HasGroupAction L G) (g : G) :
    ((s : L) → LocalNetLike.localIdx (L := L) s)
      ≃ ((s : L) → LocalNetLike.localIdx (L := L) s) :=
  Equiv.piCongr (act.siteAction g) (fun s => act.siteIdxEquiv g s)

/-- Pointwise formula for `piAction` evaluated at `siteAction g s`. -/
theorem piAction_apply_apply
    (act : HasGroupAction L G) (g : G)
    (f : (s : L) → LocalNetLike.localIdx (L := L) s) (s : L) :
    piAction act g f (act.siteAction g s) = act.siteIdxEquiv g s (f s) :=
  Equiv.piCongr_apply_apply (act.siteAction g)
    (fun s => act.siteIdxEquiv g s) f s

/-- The `g`-translate sends finite-variation tuples to finite-variation
tuples: a `Γ`-witness for `f` translates to a `Γ.image (siteAction g)`-witness
for `piAction g f`. -/
theorem piAction_finite_variation
    (act : HasGroupAction L G) (g : G)
    {f : (s : L) → LocalNetLike.localIdx (L := L) s}
    {Γ : Finset L} (hf : ∀ s ∉ Γ, f s = referenceBasis L s) :
    ∀ t ∉ Γ.image (act.siteAction g),
      piAction act g f t = referenceBasis L t := by
  intro t ht
  -- Replace `t` by `act.siteAction g s` to bypass the dependent-type cast.
  obtain ⟨s, rfl⟩ : ∃ s, act.siteAction g s = t :=
    ⟨(act.siteAction g).symm t, Equiv.apply_symm_apply _ _⟩
  have hs : s ∉ Γ := fun hin => ht (Finset.mem_image.mpr ⟨s, hin, rfl⟩)
  rw [piAction_apply_apply, hf s hs, act.siteIdxEquiv_referenceBasis]

/-- Symmetric statement: the inverse `piAction g` also preserves finite
variation, with the witness translating along `(siteAction g).symm`. -/
theorem piAction_symm_finite_variation
    (act : HasGroupAction L G) (g : G)
    {h : (s : L) → LocalNetLike.localIdx (L := L) s}
    {Γ' : Finset L} (hh : ∀ t ∉ Γ', h t = referenceBasis L t) :
    ∀ s ∉ Γ'.image (act.siteAction g).symm,
      (piAction act g).symm h s = referenceBasis L s := by
  intro s hs
  have ht : act.siteAction g s ∉ Γ' := by
    intro hin
    apply hs
    rw [Finset.mem_image]
    exact ⟨act.siteAction g s, hin, Equiv.symm_apply_apply _ _⟩
  -- (piAction g).symm h s = (siteIdxEquiv g s).symm (h (siteAction g s)).
  have hsym :
      (piAction act g).symm h
        = fun s => (act.siteIdxEquiv g s).symm (h (act.siteAction g s)) :=
    Equiv.piCongr_symm_apply (act.siteAction g)
      (fun s => act.siteIdxEquiv g s) h
  rw [show (piAction act g).symm h s
        = (act.siteIdxEquiv g s).symm (h (act.siteAction g s)) from
      congrFun hsym s]
  rw [hh _ ht, ← act.siteIdxEquiv_referenceBasis g s]
  exact (act.siteIdxEquiv g s).symm_apply_apply _

/-- The lift of the site action to a permutation of `globalIdx L`. -/
noncomputable def globalIdxAction (act : HasGroupAction L G) (g : G) :
    globalIdx L ≃ globalIdx L :=
  Equiv.subtypeEquiv (act.piAction g) (fun f => by
    refine ⟨fun ⟨Γ, hΓ⟩ => ⟨Γ.image (act.siteAction g),
              piAction_finite_variation act g hΓ⟩,
            fun ⟨Γ', hΓ'⟩ => ⟨Γ'.image (act.siteAction g).symm, ?_⟩⟩
    -- We need ∀ s ∉ Γ'.image (siteAction g).symm, f s = referenceBasis L s.
    -- Use that f = (piAction g).symm (piAction g f) and apply
    -- piAction_symm_finite_variation.
    have hf_eq : f = (act.piAction g).symm (act.piAction g f) :=
      ((act.piAction g).symm_apply_apply f).symm
    intro s hs
    rw [hf_eq]
    exact piAction_symm_finite_variation act g hΓ' s hs)

end HasGroupAction

end LocalNetLike
