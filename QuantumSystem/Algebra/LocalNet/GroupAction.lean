module

public import QuantumSystem.Algebra.LocalNet

/-!
# Group action data on a `LocalNet`

Provides the **kinematic data** for a `G`-equivariant `LocalNet`: a group action on
the underlying site set together with per-site type isomorphisms intertwining the
local Hilbert spaces. This is the input data for the covariance axiom (Verch 2025
§1.2 axiom (iii) / Naaijkens 2012 §1.3) — the action lifts to a `*`-automorphism
family `α_g : 𝔄(Λ) ≃⋆ₐ 𝔄(g · Λ)` constructed in `LocalNet/Covariance.lean`.

## Main definitions

* `LocalNet.HasGroupAction` — group action + per-site Hilbert-space equivalences.
* `LocalNet.HasGroupAction.regionImage` — the Finset image `g · Λ` of a region.

## References

* Verch 2025 (`https://arxiv.org/abs/2507.00900`) §1.2 axiom (iii)
* Naaijkens 2012 (`https://repository.ubn.ru.nl/handle/2066/92737`) §1.3
-/

@[expose] public section

namespace LocalNet

variable (L : LocalNet)

/-- **Group action data** for a `LocalNet`. Carries:

  - `siteAction` — a group homomorphism `G → Equiv.Perm L.sites` (action on sites
    by permutations). The unit and multiplication laws follow from the
    `Equiv.Perm` group structure since `siteAction` is a `MonoidHom`.
  - `siteIdxEquiv` — for each `(g, s)`, an isomorphism between the local
    Hilbert space at `s` and the one at `g · s`. This intertwines the action with
    the per-site dependent type `localIdx`. -/
structure HasGroupAction (G : Type*) [Group G] where
  /-- Action on sites as a group hom into permutations. -/
  siteAction : G →* Equiv.Perm L.sites
  /-- Per-site equivalence between the local Hilbert space at `s` and at `g · s`. -/
  siteIdxEquiv : ∀ (g : G) (s : L.sites), L.localIdx s ≃ L.localIdx (siteAction g s)

namespace HasGroupAction

variable {L G} [Group G]

/-- The `G`-translate of a region `Λ`: the Finset image of `Λ` under `siteAction g`. -/
def regionImage (act : L.HasGroupAction G) (g : G) (Λ : Finset L.sites) :
    Finset L.sites :=
  Λ.image (act.siteAction g)

@[simp] lemma regionImage_one (act : L.HasGroupAction G) (Λ : Finset L.sites) :
    act.regionImage 1 Λ = Λ := by
  unfold regionImage
  rw [act.siteAction.map_one]
  exact Λ.image_id

/-- `regionImage` distributes over `\\` because `siteAction g` is a bijection. -/
lemma regionImage_sdiff (act : L.HasGroupAction G) (g : G) (Λ Λ' : Finset L.sites) :
    act.regionImage g (Λ \ Λ') = act.regionImage g Λ \ act.regionImage g Λ' :=
  Finset.image_sdiff Λ Λ' (act.siteAction g).injective

/-- `regionImage (g * h) Λ = regionImage g (regionImage h Λ)`: compatibility with the
    group product, derived from `MonoidHom.map_mul` and `Finset.image_image`. -/
lemma regionImage_mul (act : L.HasGroupAction G) (g h : G) (Λ : Finset L.sites) :
    act.regionImage (g * h) Λ = act.regionImage g (act.regionImage h Λ) := by
  unfold regionImage
  rw [act.siteAction.map_mul, Finset.image_image]
  rfl

/-- Lift the site action `act.siteAction g` to a bijection `↥Λ ≃ ↥(g · Λ)`
    on the Subtypes of region members. -/
def siteSubtypeEquiv (act : L.HasGroupAction G) (g : G) (Λ : Finset L.sites) :
    ↥Λ ≃ ↥(act.regionImage g Λ) where
  toFun a := ⟨act.siteAction g a.val,
    Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩
  invFun b := ⟨(act.siteAction g).symm b.val, by
    obtain ⟨u, hu, hgu⟩ := Finset.mem_image.mp b.property
    have : (act.siteAction g).symm b.val = u := by
      rw [← hgu]; exact (act.siteAction g).symm_apply_apply u
    rw [this]; exact hu⟩
  left_inv a := by
    apply Subtype.ext
    exact (act.siteAction g).symm_apply_apply a.val
  right_inv b := by
    apply Subtype.ext
    exact (act.siteAction g).apply_symm_apply b.val

/-- The action on `regionIdx`: an `Equiv` between local Hilbert-space data on `Λ`
    and on `g · Λ`. Built from the site permutation (`siteSubtypeEquiv`) and the
    per-site type isomorphisms (`siteIdxEquiv`) via `Equiv.piCongr`. -/
def regionIdxEquivOfAction (act : L.HasGroupAction G) (g : G) (Λ : Finset L.sites) :
    L.regionIdx Λ ≃ L.regionIdx (act.regionImage g Λ) :=
  (act.siteSubtypeEquiv g Λ).piCongr (fun a => act.siteIdxEquiv g a.val)

end HasGroupAction

/-- The lifted algebra automorphism family `α_g : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(g · Λ)`.
    Realised by `Matrix.reindexStarAlgEquiv` applied to the region equivalence
    `regionIdxEquivOfAction g Λ : regionIdx Λ ≃ regionIdx (g · Λ)`. -/
noncomputable def algebraAut {L : LocalNet} {G : Type*} [Group G]
    (act : L.HasGroupAction G) (g : G) (Λ : Finset L.sites) :
    L.localAlgebra Λ ≃⋆ₐ[ℂ] L.localAlgebra (act.regionImage g Λ) :=
  Matrix.reindexStarAlgEquiv (R := ℂ) (act.regionIdxEquivOfAction g Λ)

/-- **Covariance (Haag–Kastler axiom (iii)) — Prop form.** The algebra
    automorphism family `α_g` intertwines the isotony embedding: applying
    `α_g` to an embedded element equals embedding its `α_g`-translate.
    Reserved as a `Prop` so that future abstract `HaagKastlerNet` structures
    can take this as an axiom field. -/
def IsCovariant (L : LocalNet) {G : Type*} [Group G]
    (act : L.HasGroupAction G) : Prop :=
  ∀ (g : G) {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ),
    L.algebraAut act g Λ_total (L.includeAlgebra h X) =
      L.includeAlgebra (Finset.image_subset_image h) (L.algebraAut act g Λ X)

/-! ### Uniform local-index structure

Quantum spin systems (Naaijkens 2012 §1.3, Bratteli–Robinson Vol.2 §6.2) have
a **uniform** local Hilbert space — every site carries a copy of the same
finite-dimensional space `T = ℂ^d`. This section captures that uniformity as
a typeclass, plus a derived `HasGroupActionUniform` whose group action splits
into a permutation of sites and an action on `T`. The bridge to the generic
`HasGroupAction` is given by `HasGroupActionUniform.toHasGroupAction`, where
`siteIdxEquiv` is **constructed** by transport through `T` — making the
cocycle laws (`algebraAut_one`, `algebraAut_mul`) automatic from the
`MonoidHom` structure of `localAction`. -/

/-- **Uniform local indices**: an isomorphism between every site's local index
    type and a fixed finite type `T`. Captures the spin-system case where every
    site has the same local Hilbert-space dimension. -/
class HasUniformLocalIdx (L : LocalNet) (T : Type*)
    [Fintype T] [DecidableEq T] where
  /-- The per-site identification with the uniform index `T`. -/
  iso : ∀ s : L.sites, L.localIdx s ≃ T

/-- **Group action on a `LocalNet` with uniform local indices**. Splits into a
    permutation action on sites (`siteAction`) and a permutation action on the
    uniform local index type (`localAction`). The site equivalence
    `siteIdxEquiv` of the induced `HasGroupAction` is *derived* by transport
    through `T`, so the unit/multiplication laws come for free from
    `MonoidHom.map_one` / `map_mul` on `localAction`. -/
structure HasGroupActionUniform (L : LocalNet) (T : Type*)
    [Fintype T] [DecidableEq T] [L.HasUniformLocalIdx T]
    (G : Type*) [Group G] where
  /-- Action on sites as a group hom into permutations. -/
  siteAction : G →* Equiv.Perm L.sites
  /-- Action on the uniform local index type. -/
  localAction : G →* Equiv.Perm T

namespace HasGroupActionUniform

variable {L : LocalNet} {T : Type*} [Fintype T] [DecidableEq T]
  [L.HasUniformLocalIdx T] {G : Type*} [Group G]

/-- Every uniform group action gives a generic `HasGroupAction` whose
    `siteIdxEquiv g s` is constructed as
    `iso s ∘ localAction g ∘ (iso (siteAction g s))⁻¹` — transport the value
    at site `s` to `T`, apply `localAction g`, transport back to the new site. -/
def toHasGroupAction (actU : L.HasGroupActionUniform T G) :
    L.HasGroupAction G where
  siteAction := actU.siteAction
  siteIdxEquiv g s :=
    (HasUniformLocalIdx.iso s).trans
      ((actU.localAction g).trans
        (HasUniformLocalIdx.iso (actU.siteAction g s)).symm)

@[simp] lemma toHasGroupAction_siteAction (actU : L.HasGroupActionUniform T G) :
    actU.toHasGroupAction.siteAction = actU.siteAction := rfl

@[simp] lemma toHasGroupAction_siteIdxEquiv
    (actU : L.HasGroupActionUniform T G) (g : G) (s : L.sites) :
    actU.toHasGroupAction.siteIdxEquiv g s =
      (HasUniformLocalIdx.iso s).trans
        ((actU.localAction g).trans
          (HasUniformLocalIdx.iso (actU.siteAction g s)).symm) := rfl

end HasGroupActionUniform

end LocalNet

