module

public import QuantumSystem.Algebra.LocalNet.Covariance

/-!
# Group-action functoriality of `algebraAut` on uniform `LocalNet`s

For a `LocalNet` with uniform local indices (`HasUniformLocalIdx`) and a uniform
group action (`HasGroupActionUniform`), the algebra automorphism family `α_g` is
itself a group action on the algebras — `α_1 = id` and `α_{gh} = α_g ∘ α_h`,
modulo the obvious `regionImage` reindexings. The proofs work because
`localAction : G →* Equiv.Perm T` is a `MonoidHom`, so the unit/multiplication
laws come for free without HEq.

## Main results

* `LocalNet.algebraAut_one_apply` — `(α_1 M) i j = M (i ↾) (j ↾)` modulo
  `regionImage_one` reindex.
* `LocalNet.algebraAut_mul_apply` — `(α_{gh} M) i j = (α_g (α_h M)) (i ↾) (j ↾)`
  modulo `regionImage_mul` reindex.
* `LocalNet.siteAction_mul_apply`, `localAction_mul_apply` — pointwise
  compositionality of the site / local actions.
-/

@[expose] public section

namespace LocalNet

variable {L : LocalNet} {T : Type*} [Fintype T] [DecidableEq T]
  [L.HasUniformLocalIdx T] {G : Type*} [Group G]

namespace HasGroupActionUniform

/-- For a uniform group action, `siteIdxEquiv 1 s` reduces to `iso s ∘ iso _.symm`
    (the `localAction 1 = 1` factor disappears via `MonoidHom.map_one`). -/
lemma siteIdxEquiv_one (actU : L.HasGroupActionUniform T G) (s : L.sites) :
    actU.toHasGroupAction.siteIdxEquiv 1 s =
      (HasUniformLocalIdx.iso (T := T) s).trans
        (HasUniformLocalIdx.iso (T := T) (actU.siteAction 1 s)).symm := by
  change (HasUniformLocalIdx.iso (T := T) s).trans
        ((actU.localAction 1).trans
          (HasUniformLocalIdx.iso (T := T) (actU.siteAction 1 s)).symm) = _
  rw [actU.localAction.map_one]
  ext x
  simp

end HasGroupActionUniform

/-- The site action at the identity equals the identity permutation pointwise. -/
private lemma siteAction_one_apply
    (actU : L.HasGroupActionUniform T G) (s : L.sites) :
    actU.siteAction 1 s = s := by
  rw [actU.siteAction.map_one]
  rfl

/-- Pointwise: `(regionIdxEquivOfAction 1 Λ).symm` agrees with the canonical
    transport `regionIdxCongr (regionImage_one Λ)`. -/
private lemma regionIdxEquivOfAction_one_symm_apply_uniform
    (actU : L.HasGroupActionUniform T G) {Λ : Finset L.sites}
    (i : L.regionIdx (actU.toHasGroupAction.regionImage 1 Λ)) (a : ↥Λ) :
    (actU.toHasGroupAction.regionIdxEquivOfAction 1 Λ).symm i a =
      L.regionIdxCongr (actU.toHasGroupAction.regionImage_one Λ) i a := by
  -- LHS: ((siteSubtypeEquiv 1 Λ).piCongr siteIdxEquiv).symm i a
  --    = (siteIdxEquiv 1 a.val).symm (i (siteSubtypeEquiv 1 Λ a))
  --    = (siteIdxEquiv 1 a.val).symm (i ⟨siteAction 1 a.val, mem_image⟩)
  change (actU.toHasGroupAction.siteIdxEquiv 1 a.val).symm
        (i ⟨actU.siteAction 1 a.val,
            Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩) = _
  -- Convert `e.symm x = y` to `x = e y` to avoid awkward symm-trans normalisation.
  rw [Equiv.symm_apply_eq, HasGroupActionUniform.siteIdxEquiv_one]
  -- Goal: i ⟨siteAction 1 a.val, _⟩
  --      = ((iso a.val).trans (iso (siteAction 1 a.val)).symm) (regionIdxCongr ... i a)
  have hmem_a : a.val ∈ actU.toHasGroupAction.regionImage 1 Λ := by
    rw [actU.toHasGroupAction.regionImage_one]; exact a.property
  rw [L.regionIdxCongr_apply (actU.toHasGroupAction.regionImage_one Λ) i hmem_a a.property]
  -- Substitute `siteAction 1 a.val = a.val` via a generic motive (so `subst` applies).
  have h1 : actU.siteAction 1 a.val = a.val := siteAction_one_apply actU a.val
  have motive : ∀ (x : L.sites) (_ : x = a.val)
      (mem' : x ∈ actU.toHasGroupAction.regionImage 1 Λ),
      i ⟨x, mem'⟩
        = ((HasUniformLocalIdx.iso (T := T) a.val).trans
            (HasUniformLocalIdx.iso (T := T) x).symm) (i ⟨a.val, hmem_a⟩) := by
    intro x hx _
    subst hx
    rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  exact motive (actU.siteAction 1 a.val) h1 _

/-- **`algebraAut` is functorial in the unit element**: `α_1 M = M`, modulo
    the canonical reindexing along `regionImage_one`. Entry-wise statement. -/
theorem algebraAut_one_apply
    (actU : L.HasGroupActionUniform T G) {Λ : Finset L.sites}
    (M : L.localAlgebra Λ) (i j : L.regionIdx (actU.toHasGroupAction.regionImage 1 Λ)) :
    L.algebraAut actU.toHasGroupAction 1 Λ M i j =
      M (L.regionIdxCongr (actU.toHasGroupAction.regionImage_one Λ) i)
        (L.regionIdxCongr (actU.toHasGroupAction.regionImage_one Λ) j) := by
  rw [algebraAut_apply]
  congr 1
  · funext a; exact regionIdxEquivOfAction_one_symm_apply_uniform actU i a
  · funext a; exact regionIdxEquivOfAction_one_symm_apply_uniform actU j a

/-! ### Multiplicative cocycle -/

/-- The site action at a product equals the composition pointwise. -/
lemma siteAction_mul_apply
    (actU : L.HasGroupActionUniform T G) (g h : G) (s : L.sites) :
    actU.siteAction (g * h) s = actU.siteAction g (actU.siteAction h s) := by
  rw [actU.siteAction.map_mul]; rfl

/-- The local action at a product equals the composition pointwise. -/
lemma localAction_mul_apply
    (actU : L.HasGroupActionUniform T G) (g h : G) (x : T) :
    actU.localAction (g * h) x = actU.localAction g (actU.localAction h x) := by
  rw [actU.localAction.map_mul]; rfl

/-- Pointwise: `(regionIdxEquivOfAction (g * h) Λ).symm` factors through
    successive `(regionIdxEquivOfAction h Λ).symm` and
    `(regionIdxEquivOfAction g (regionImage h Λ)).symm`, modulo the
    `regionImage_mul` reindexing. -/
private lemma regionIdxEquivOfAction_mul_symm_apply_uniform
    (actU : L.HasGroupActionUniform T G) (g h : G) {Λ : Finset L.sites}
    (i : L.regionIdx (actU.toHasGroupAction.regionImage (g * h) Λ)) (a : ↥Λ) :
    (actU.toHasGroupAction.regionIdxEquivOfAction (g * h) Λ).symm i a =
      (actU.toHasGroupAction.regionIdxEquivOfAction h Λ).symm
        ((actU.toHasGroupAction.regionIdxEquivOfAction g
            (actU.toHasGroupAction.regionImage h Λ)).symm
          (L.regionIdxCongr (actU.toHasGroupAction.regionImage_mul g h Λ) i))
        a := by
  -- The site `siteAction g (siteAction h a.val)` lies in `regionImage (g*h) Λ`.
  have hmem_g_h : actU.siteAction g (actU.siteAction h a.val) ∈
      actU.toHasGroupAction.regionImage (g * h) Λ := by
    rw [actU.toHasGroupAction.regionImage_mul g h Λ]
    exact Finset.mem_image.mpr
      ⟨actU.siteAction h a.val,
        Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩, rfl⟩
  -- Reduce the RHS's `regionIdxCongr` to a direct `i`-evaluation.
  change (actU.toHasGroupAction.siteIdxEquiv (g * h) a.val).symm
        (i ⟨actU.siteAction (g * h) a.val,
            Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩)
      = (actU.toHasGroupAction.siteIdxEquiv h a.val).symm
          ((actU.toHasGroupAction.siteIdxEquiv g (actU.siteAction h a.val)).symm
            ((L.regionIdxCongr (actU.toHasGroupAction.regionImage_mul g h Λ) i)
              ⟨actU.siteAction g (actU.siteAction h a.val),
                Finset.mem_image.mpr
                  ⟨actU.siteAction h a.val,
                    Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩, rfl⟩⟩))
  rw [L.regionIdxCongr_apply (actU.toHasGroupAction.regionImage_mul g h Λ) i hmem_g_h _]
  -- Both sides feature `(iso a.val).symm` of a `T`-value. Use the algebraic
  -- decomposition of `(siteIdxEquiv g s).symm` (via `Equiv.symm_trans_apply`),
  -- which is `rfl`, to push everything into a common shape.
  change (HasUniformLocalIdx.iso (T := T) a.val).symm
        ((actU.localAction (g * h)).symm
          ((HasUniformLocalIdx.iso (T := T) (actU.siteAction (g * h) a.val))
            (i ⟨actU.siteAction (g * h) a.val, _⟩)))
      = (HasUniformLocalIdx.iso (T := T) a.val).symm
          ((actU.localAction h).symm
            ((HasUniformLocalIdx.iso (T := T) (actU.siteAction h a.val))
              ((HasUniformLocalIdx.iso (T := T) (actU.siteAction h a.val)).symm
                ((actU.localAction g).symm
                  ((HasUniformLocalIdx.iso (T := T)
                      (actU.siteAction g (actU.siteAction h a.val)))
                    (i ⟨actU.siteAction g (actU.siteAction h a.val), hmem_g_h⟩))))))
  -- Cancel the `iso ∘ iso.symm` in the middle of the RHS.
  rw [Equiv.apply_symm_apply]
  -- Combine `(localAction (g*h)).symm` to `(localAction h).symm ∘ (localAction g).symm`.
  rw [actU.localAction.map_mul]
  -- Now goal:
  --   (iso a.val).symm ((localAction g * localAction h).symm
  --     ((iso (siteAction (g*h) a.val)) (i ⟨siteAction (g*h) a.val, _⟩)))
  --     = (iso a.val).symm ((localAction h).symm ((localAction g).symm
  --         ((iso (siteAction g (siteAction h a.val)))
  --           (i ⟨siteAction g (siteAction h a.val), hmem_g_h⟩))))
  -- The two `(localAction g * localAction h).symm` and `(localAction h).symm ∘
  -- (localAction g).symm` agree by Perm group inversion law.
  congr 1
  -- Goal: (localAction g * localAction h).symm (iso (siteAction (g*h) a.val) (i ⟨..., _⟩))
  --     = (localAction h).symm ((localAction g).symm (iso (siteAction g (siteAction h a.val)) (i ⟨..., _⟩)))
  rw [show (actU.localAction g * actU.localAction h).symm
        = (actU.localAction h).symm * (actU.localAction g).symm from
        mul_inv_rev (actU.localAction g) (actU.localAction h)]
  rw [Equiv.Perm.mul_apply]
  -- Goal: (localAction h).symm ((localAction g).symm (iso (siteAction (g*h) a.val) (i ⟨..., _⟩)))
  --     = (localAction h).symm ((localAction g).symm (iso (siteAction g (siteAction h a.val)) (i ⟨..., _⟩)))
  -- Reduce to the inner T-value equality.
  congr 2
  -- Goal: iso (siteAction (g*h) a.val) (i ⟨siteAction (g*h) a.val, _⟩)
  --     = iso (siteAction g (siteAction h a.val)) (i ⟨siteAction g (siteAction h a.val), hmem_g_h⟩)
  -- Use the motive trick to substitute siteAction (g*h) a.val = siteAction g (siteAction h a.val).
  have h_mul : actU.siteAction (g * h) a.val =
      actU.siteAction g (actU.siteAction h a.val) :=
    siteAction_mul_apply actU g h a.val
  have motive : ∀ (s : L.sites)
      (_ : s = actU.siteAction g (actU.siteAction h a.val))
      (mem' : s ∈ actU.toHasGroupAction.regionImage (g * h) Λ),
      (HasUniformLocalIdx.iso (T := T) s) (i ⟨s, mem'⟩)
        = (HasUniformLocalIdx.iso (T := T)
            (actU.siteAction g (actU.siteAction h a.val)))
          (i ⟨actU.siteAction g (actU.siteAction h a.val), hmem_g_h⟩) := by
    intro s hs _
    subst hs
    rfl
  exact motive (actU.siteAction (g * h) a.val) h_mul _

/-- **`algebraAut` is functorial in the multiplicative structure**: applying
    `α_(g*h)` equals applying `α_h` then `α_g`, modulo the canonical reindex
    along `regionImage_mul`. Entry-wise statement. -/
theorem algebraAut_mul_apply
    (actU : L.HasGroupActionUniform T G) (g h : G) {Λ : Finset L.sites}
    (M : L.localAlgebra Λ)
    (i j : L.regionIdx (actU.toHasGroupAction.regionImage (g * h) Λ)) :
    L.algebraAut actU.toHasGroupAction (g * h) Λ M i j =
      L.algebraAut actU.toHasGroupAction g
          (actU.toHasGroupAction.regionImage h Λ)
        (L.algebraAut actU.toHasGroupAction h Λ M)
        (L.regionIdxCongr (actU.toHasGroupAction.regionImage_mul g h Λ) i)
        (L.regionIdxCongr (actU.toHasGroupAction.regionImage_mul g h Λ) j) := by
  rw [algebraAut_apply, algebraAut_apply, algebraAut_apply]
  congr 1
  · funext a; exact regionIdxEquivOfAction_mul_symm_apply_uniform actU g h i a
  · funext a; exact regionIdxEquivOfAction_mul_symm_apply_uniform actU g h j a

end LocalNet
