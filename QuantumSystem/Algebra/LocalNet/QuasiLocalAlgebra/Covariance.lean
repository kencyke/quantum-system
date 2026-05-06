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

@[simp]
theorem globalIdxAction_val (act : HasGroupAction L G) (g : G) (f : globalIdx L) :
    (globalIdxAction act g f).val = piAction act g f.val := rfl

/-! ### Unitary representation on `globalHilbert L` -/

/-- Membership in `lp (... ℂ) 2` is preserved by reindexing along an `Equiv`
on the index. -/
theorem lp_memℓp_reindex (e : globalIdx L ≃ globalIdx L)
    {f : globalIdx L → ℂ} (hf : Memℓp f 2) :
    Memℓp (fun a => f (e.symm a)) 2 := by
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  rw [memℓp_gen_iff htwo] at hf ⊢
  exact (e.symm.summable_iff
    (f := fun b => ‖f b‖ ^ ((2 : ENNReal).toReal))).mpr hf

/-- The unitary representation on `globalHilbert L` induced by the site
action: a basis-permutation isometry sending `lp.single 2 j 1` to
`lp.single 2 (globalIdxAction g j) 1`. -/
noncomputable def unitaryAction (act : HasGroupAction L G) (g : G) :
    globalHilbert L ≃ₗᵢ[ℂ] globalHilbert L where
  toFun f :=
    ⟨fun a => (f : globalIdx L → ℂ) ((globalIdxAction act g).symm a),
      lp_memℓp_reindex (globalIdxAction act g) (lp.memℓp f)⟩
  invFun f :=
    ⟨fun a => (f : globalIdx L → ℂ) (globalIdxAction act g a),
      by
        have hf : Memℓp (fun a => (f : globalIdx L → ℂ)
              ((globalIdxAction act g).symm.symm a)) 2 :=
          lp_memℓp_reindex (globalIdxAction act g).symm (lp.memℓp f)
        simp only [Equiv.symm_symm] at hf
        exact hf⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    change (f : globalIdx L → ℂ)
        ((globalIdxAction act g).symm (globalIdxAction act g a)) = _
    rw [Equiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext a
    change (f : globalIdx L → ℂ)
        (globalIdxAction act g ((globalIdxAction act g).symm a)) = _
    rw [Equiv.apply_symm_apply]
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext a
    change ((f₁ + f₂ : lp (fun _ : globalIdx L => ℂ) 2) : globalIdx L → ℂ)
            ((globalIdxAction act g).symm a)
        = (f₁ : globalIdx L → ℂ) ((globalIdxAction act g).symm a)
          + (f₂ : globalIdx L → ℂ) ((globalIdxAction act g).symm a)
    exact congrFun (lp.coeFn_add f₁ f₂) _
  map_smul' c f := by
    apply Subtype.ext
    funext a
    change ((c • f : lp (fun _ : globalIdx L => ℂ) 2) : globalIdx L → ℂ)
            ((globalIdxAction act g).symm a)
        = c • (f : globalIdx L → ℂ) ((globalIdxAction act g).symm a)
    exact congrFun (lp.coeFn_smul c f) _
  norm_map' f := by
    have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
      rw [ENNReal.toReal_ofNat]; norm_num
    -- The toFun image, viewed as a `globalHilbert L` element.
    set Uf : globalHilbert L :=
      ⟨fun a => (f : globalIdx L → ℂ) ((globalIdxAction act g).symm a),
        lp_memℓp_reindex (globalIdxAction act g) (lp.memℓp f)⟩
    change ‖Uf‖ = ‖f‖
    have hLHS := lp.norm_rpow_eq_tsum (E := fun _ : globalIdx L => ℂ) (p := 2)
      htwo Uf
    have hRHS := lp.norm_rpow_eq_tsum (E := fun _ : globalIdx L => ℂ) (p := 2)
      htwo f
    have hsum :
        ∑' a : globalIdx L,
            ‖(f : globalIdx L → ℂ) ((globalIdxAction act g).symm a)‖
              ^ ((2 : ENNReal).toReal)
          = ∑' b : globalIdx L,
              ‖(f : globalIdx L → ℂ) b‖ ^ ((2 : ENNReal).toReal) :=
      Equiv.tsum_eq (globalIdxAction act g).symm
        (fun b => ‖(f : globalIdx L → ℂ) b‖ ^ ((2 : ENNReal).toReal))
    have hpow : ‖Uf‖ ^ ((2 : ENNReal).toReal) = ‖f‖ ^ ((2 : ENNReal).toReal) := by
      rw [hLHS, hRHS]; exact hsum
    have h2real : (2 : ENNReal).toReal = 2 := by simp
    rw [h2real] at hpow
    -- Convert `^ (2 : ℝ)` to `^ (2 : ℕ)`.
    have hpow_nat : ‖Uf‖ ^ (2 : ℕ) = ‖f‖ ^ (2 : ℕ) := by
      have hUf := Real.rpow_natCast ‖Uf‖ 2
      have hf := Real.rpow_natCast ‖f‖ 2
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from rfl] at hUf hf
      rw [← hUf, ← hf]; exact_mod_cast hpow
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow_nat

@[simp]
theorem unitaryAction_apply_val (act : HasGroupAction L G) (g : G)
    (f : globalHilbert L) (a : globalIdx L) :
    ((unitaryAction act g f : globalHilbert L) : globalIdx L → ℂ) a
      = (f : globalIdx L → ℂ) ((globalIdxAction act g).symm a) := rfl

/-! ### Algebra automorphism via conjugation by the unitary representation -/

/-- The `*`-algebra automorphism of `B(globalHilbert L)` induced by conjugation
by the unitary representation `unitaryAction g`.  This is the operator-level
realisation of the action used in the covariance axiom (Verch 2025 §1.2 axiom
iii). -/
noncomputable def algebraAut (act : HasGroupAction L G) (g : G) :
    (globalHilbert L →L[ℂ] globalHilbert L)
      ≃⋆ₐ[ℂ] (globalHilbert L →L[ℂ] globalHilbert L) :=
  (act.unitaryAction g).conjStarAlgEquiv

theorem algebraAut_apply (act : HasGroupAction L G) (g : G)
    (T : globalHilbert L →L[ℂ] globalHilbert L) :
    act.algebraAut g T
      = (act.unitaryAction g).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (T.comp (act.unitaryAction g).symm.toContinuousLinearEquiv.toContinuousLinearMap) :=
  LinearIsometryEquiv.conjStarAlgEquiv_apply _ _

end HasGroupAction

end LocalNetLike
