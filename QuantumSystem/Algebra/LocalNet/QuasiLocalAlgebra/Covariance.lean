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

open scoped LocalNetLike

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

/-! ### Genuine group actions

The fields of `HasGroupAction` make each group element act on sites and local fibres,
but they do not on their own require the fibre equivalences to compose coherently.
For a genuine `G`-action on the quasi-local algebra, this composition coherence is
needed, and we record it at the already-built dependent-function action level so
the public API avoids fragile dependent casts. -/

/-- Promotes a `HasGroupAction` from "data only" to a **genuine** `G`-action: the
induced dependent-function permutation `piAction` is a monoid homomorphism
`G →* Equiv.Perm ((s : L) → localIdx s)`.  Without this mixin, `HasGroupAction`
carries the per-group-element data but no compositionality, so `piAction` and its
downstream lifts (`globalIdxAction`, `unitaryAction`, `algebraAut`, `quasiLocalAut`)
are merely well-defined per element rather than functorial in `G`. -/
class IsGenuineAction (act : HasGroupAction L G) : Prop where
  /-- The identity group element acts trivially on dependent site-index tuples. -/
  piAction_one : act.piAction 1 = Equiv.refl _
  /-- Multiplication is respected by the dependent site-index action. -/
  piAction_mul (g h : G) :
    act.piAction (g * h) = (act.piAction h).trans (act.piAction g)

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

/-- Under a genuine action, the identity element acts trivially on `globalIdx`. -/
theorem globalIdxAction_one (act : HasGroupAction L G) [act.IsGenuineAction] :
    act.globalIdxAction 1 = Equiv.refl (globalIdx L) := by
  ext f
  apply Subtype.ext
  simp [globalIdxAction_val, IsGenuineAction.piAction_one (act := act)]

/-- Under a genuine action, multiplication is respected on `globalIdx`. -/
theorem globalIdxAction_mul (act : HasGroupAction L G) [act.IsGenuineAction]
    (g h : G) :
    act.globalIdxAction (g * h) = (act.globalIdxAction h).trans (act.globalIdxAction g) := by
  ext f
  apply Subtype.ext
  simp [globalIdxAction_val, IsGenuineAction.piAction_mul (act := act) g h]

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

/-- Under a genuine action, the identity element is implemented by the identity unitary. -/
theorem unitaryAction_one (act : HasGroupAction L G) [act.IsGenuineAction] :
    act.unitaryAction 1 = LinearIsometryEquiv.refl ℂ (globalHilbert L) := by
  ext f a
  simp [unitaryAction_apply_val, globalIdxAction_one]

/-- Under a genuine action, the implementing unitaries multiply according to the group law. -/
theorem unitaryAction_mul (act : HasGroupAction L G) [act.IsGenuineAction]
    (g h : G) :
    act.unitaryAction (g * h) = (act.unitaryAction h).trans (act.unitaryAction g) := by
  ext f a
  simp [unitaryAction_apply_val, globalIdxAction_mul]

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

/-- Under a genuine action, the identity group element induces the identity automorphism. -/
theorem algebraAut_one (act : HasGroupAction L G) [act.IsGenuineAction] :
    act.algebraAut 1 =
      StarAlgEquiv.refl (R := ℂ) (A := globalHilbert L →L[ℂ] globalHilbert L) := by
  unfold algebraAut
  rw [unitaryAction_one]
  exact LinearIsometryEquiv.conjStarAlgEquiv_refl

/-- Under a genuine action, the induced automorphisms compose according to the group law. -/
theorem algebraAut_mul (act : HasGroupAction L G) [act.IsGenuineAction]
    (g h : G) :
    act.algebraAut (g * h) = (act.algebraAut h).trans (act.algebraAut g) := by
  unfold algebraAut
  rw [unitaryAction_mul]
  exact LinearIsometryEquiv.conjStarAlgEquiv_trans _ _

/-! ### Region-level transport: lifting `g` to `regionHilbert` -/

/-- The `g`-translate of `↥Λ` to `↥(regionImage g Λ)`. -/
def siteSubtypeEquiv (act : HasGroupAction L G) (g : G) (Λ : Finset L) :
    ↥Λ ≃ ↥(act.regionImage g Λ) where
  toFun a := ⟨act.siteAction g a.val,
    Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩
  invFun b := ⟨(act.siteAction g).symm b.val, by
    obtain ⟨u, hu, hgu⟩ := Finset.mem_image.mp b.property
    have : (act.siteAction g).symm b.val = u := by
      rw [← hgu]; exact (act.siteAction g).symm_apply_apply u
    rw [this]; exact hu⟩
  left_inv a := Subtype.ext ((act.siteAction g).symm_apply_apply a.val)
  right_inv b := Subtype.ext ((act.siteAction g).apply_symm_apply b.val)

/-- The induced bijection on region-level indices: `regionIdx Λ ≃ regionIdx (g · Λ)`. -/
noncomputable def regionIdxAction (act : HasGroupAction L G) (g : G)
    (Λ : Finset L) :
    regionIdx (L := L) Λ ≃ regionIdx (L := L) (act.regionImage g Λ) :=
  Equiv.piCongr (act.siteSubtypeEquiv g Λ) (fun a => act.siteIdxEquiv g a.val)

/-- The unitary `regionHilbert Λ ≃ₗᵢ[ℂ] regionHilbert (g · Λ)` induced by the
group action.  Built from the orthonormal basis of `EuclideanSpace ℂ` on each
side via `OrthonormalBasis.equiv` and the index bijection `regionIdxAction`. -/
noncomputable def regionTransport (act : HasGroupAction L G) (g : G)
    (Λ : Finset L) :
    ℋ(Λ) ≃ₗᵢ[ℂ] ℋ(act.regionImage g Λ) :=
  (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).equiv
    (EuclideanSpace.basisFun (regionIdx (L := L) (act.regionImage g Λ)) ℂ)
    (act.regionIdxAction g Λ)

/-- The `*`-algebra automorphism on `B(regionHilbert Λ)` and `B(regionHilbert (g · Λ))`
induced by `regionTransport`, used to express the covariance theorem. -/
noncomputable def regionTransportAlg (act : HasGroupAction L G) (g : G)
    (Λ : Finset L) :
    (ℋ(Λ) →L[ℂ] ℋ(Λ))
      ≃⋆ₐ[ℂ]
      (ℋ(act.regionImage g Λ)
        →L[ℂ] ℋ(act.regionImage g Λ)) :=
  (act.regionTransport g Λ).conjStarAlgEquiv

/-! ### Combinatorial identities used in the covariance theorem -/

/-- The pointwise formula for `regionTransport`: it sends a vector `v : H_Λ`
to a vector in `H_{g·Λ}` whose `a'`-coordinate is the `(regionIdxAction g Λ).symm a'`-
coordinate of `v`. -/
theorem regionTransport_apply_val
    (act : HasGroupAction L G) (g : G) (Λ : Finset L)
    (v : ℋ(Λ))
    (a' : regionIdx (L := L) (act.regionImage g Λ)) :
    ((act.regionTransport g Λ v
        : ℋ(act.regionImage g Λ))
        : regionIdx (L := L) (act.regionImage g Λ) → ℂ) a'
      = (v : regionIdx (L := L) Λ → ℂ)
          ((act.regionIdxAction g Λ).symm a') := by
  -- Decompose `v` along the standard basis, push regionTransport through, then evaluate.
  have hbasis : v = ∑ i : regionIdx (L := L) Λ,
      (v : regionIdx (L := L) Λ → ℂ) i • EuclideanSpace.single i (1 : ℂ) := by
    have := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).sum_repr v
    simpa [EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using this.symm
  conv_lhs => rw [hbasis]
  -- regionTransport (∑) = ∑ regionTransport (...) by linearity.
  rw [map_sum]
  -- Each summand: c • regionTransport (basis vector) = c • basisVector at translated index.
  have hbasis_to_single : ∀ i : regionIdx (L := L) Λ,
      (act.regionTransport g Λ) (EuclideanSpace.single i (1 : ℂ))
        = EuclideanSpace.single ((act.regionIdxAction g Λ) i) (1 : ℂ) := by
    intro i
    unfold regionTransport
    rw [← EuclideanSpace.basisFun_apply (𝕜 := ℂ) (ι := regionIdx (L := L) Λ) i,
      OrthonormalBasis.equiv_apply_basis,
      EuclideanSpace.basisFun_apply]
  conv_lhs =>
    enter [1, 2, i]
    rw [LinearIsometryEquiv.map_smul, hbasis_to_single]
  -- Now the sum is ∑ i, v.ofLp i • EuclideanSpace.single (e i) 1; evaluate at a'.
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single ((act.regionIdxAction g Λ).symm a')]
  · -- The i = e.symm a' summand: c • EuclideanSpace.single a' 1 evaluated at a' = c.
    rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
      Equiv.apply_symm_apply]
    simp
  · intro i _ hi
    have hne : a' ≠ (act.regionIdxAction g Λ) i := by
      intro h
      apply hi
      have := congrArg (act.regionIdxAction g Λ).symm h.symm
      rw [Equiv.symm_apply_apply] at this
      exact this
    rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply, if_neg hne]
    simp
  · intro hni
    exact absurd (Finset.mem_univ _) hni

/-- Key identity: the inverse `regionIdxAction` reconciles the Λ-restriction at the
translated region `g·Λ` with the Λ-restriction at `Λ` of the inverse-translated tuple. -/
theorem regionIdxAction_symm_regionRestrict (act : HasGroupAction L G) (g : G)
    (Λ : Finset L) (g_idx : globalIdx L) :
    (act.regionIdxAction g Λ).symm (regionRestrict (act.regionImage g Λ) g_idx)
      = regionRestrict Λ ((act.globalIdxAction g).symm g_idx) := by
  funext s
  -- LHS at s = (siteIdxEquiv g s.1).symm (g_idx.val (siteAction g s.1)).
  -- RHS at s = ((globalIdxAction g).symm g_idx).val s.1.
  -- Both reduce to (siteIdxEquiv g s.1).symm (g_idx.val (siteAction g s.1)).
  have hLHS :
      (act.regionIdxAction g Λ).symm (regionRestrict (act.regionImage g Λ) g_idx) s
        = (act.siteIdxEquiv g s.1).symm
            (g_idx.val (act.siteAction g s.1)) := by
    change (Equiv.piCongr (act.siteSubtypeEquiv g Λ)
            (fun a => act.siteIdxEquiv g a.1)).symm
              (regionRestrict (act.regionImage g Λ) g_idx) s
        = _
    rw [Equiv.piCongr_symm_apply]
    rfl
  have hRHS :
      regionRestrict Λ ((act.globalIdxAction g).symm g_idx) s
        = (act.siteIdxEquiv g s.1).symm
            (g_idx.val (act.siteAction g s.1)) := by
    change (act.piAction g).symm g_idx.val s.1 = _
    rw [show (act.piAction g).symm g_idx.val
            = fun s => (act.siteIdxEquiv g s).symm
                (g_idx.val (act.siteAction g s)) from
        Equiv.piCongr_symm_apply (act.siteAction g)
          (fun s => act.siteIdxEquiv g s) g_idx.val]
  rw [hLHS, hRHS]

/-- Key identity: applying the `g`-action to a `Λ`-swap of the inverse-translated
global tuple yields the corresponding `(g·Λ)`-swap. -/
theorem globalIdxAction_globalSwap (act : HasGroupAction L G) (g : G)
    (Λ : Finset L) (b : regionIdx (L := L) Λ) (g_idx : globalIdx L) :
    act.globalIdxAction g
        (globalSwap Λ b ((act.globalIdxAction g).symm g_idx))
      = globalSwap (act.regionImage g Λ) (act.regionIdxAction g Λ b) g_idx := by
  apply Subtype.ext
  funext t
  -- Replace t by siteAction g s for some s.
  obtain ⟨s, rfl⟩ : ∃ s, act.siteAction g s = t :=
    ⟨(act.siteAction g).symm t, Equiv.apply_symm_apply _ _⟩
  -- Compute LHS via piAction_apply_apply.
  change (piAction act g (globalSwap Λ b
          ((act.globalIdxAction g).symm g_idx)).val) (act.siteAction g s) = _
  rw [piAction_apply_apply]
  -- siteIdxEquiv g s ((globalSwap ...).val s) = ?
  by_cases hs : s ∈ Λ
  · -- Λ part: globalSwap inner = b ⟨s, hs⟩.
    rw [globalSwap_val_apply_of_mem _ _ _ hs]
    -- LHS = siteIdxEquiv g s (b ⟨s, hs⟩).
    -- RHS: t = siteAction g s ∈ regionImage g Λ; globalSwap (g·Λ) ... gives
    -- (regionIdxAction g Λ b) ⟨t, ht⟩.
    have ht : act.siteAction g s ∈ act.regionImage g Λ :=
      Finset.mem_image.mpr ⟨s, hs, rfl⟩
    rw [globalSwap_val_apply_of_mem _ _ _ ht]
    -- (regionIdxAction g Λ b) ⟨siteAction g s, ht⟩ = siteIdxEquiv g s (b ⟨s, hs⟩).
    have key := Equiv.piCongr_apply_apply (W := fun a : ↥Λ => localIdx a.1)
      (Z := fun b : ↥(act.regionImage g Λ) => localIdx b.1)
      (act.siteSubtypeEquiv g Λ)
      (fun a => act.siteIdxEquiv g a.1) b ⟨s, hs⟩
    -- key : (piCongr ...) b (siteSubtypeEquiv g Λ ⟨s, hs⟩) = siteIdxEquiv g s (b ⟨s, hs⟩).
    -- siteSubtypeEquiv g Λ ⟨s, hs⟩ is definitionally ⟨siteAction g s, ht⟩.
    exact key.symm
  · -- Λᶜ part: globalSwap inner = ((globalIdxAction g).symm g_idx).val s.
    rw [globalSwap_val_apply_of_not_mem _ _ _ hs]
    -- = (siteIdxEquiv g s).symm (g_idx.val (siteAction g s)).
    have hpi : ((act.globalIdxAction g).symm g_idx).val s
        = (act.siteIdxEquiv g s).symm
            (g_idx.val (act.siteAction g s)) := by
      change (act.piAction g).symm g_idx.val s = _
      rw [show (act.piAction g).symm g_idx.val
              = fun s' => (act.siteIdxEquiv g s').symm
                (g_idx.val (act.siteAction g s')) from
          Equiv.piCongr_symm_apply (act.siteAction g)
            (fun s' => act.siteIdxEquiv g s') g_idx.val]
    rw [hpi]
    -- LHS = siteIdxEquiv g s ((siteIdxEquiv g s).symm (g_idx.val (siteAction g s)))
    --     = g_idx.val (siteAction g s).
    rw [Equiv.apply_symm_apply]
    -- RHS: t = siteAction g s ∉ regionImage g Λ (since s ∉ Λ).
    have ht_nm : act.siteAction g s ∉ act.regionImage g Λ := by
      intro h
      obtain ⟨u, hu, hgu⟩ := Finset.mem_image.mp h
      apply hs
      have : u = s := (act.siteAction g).injective hgu
      rwa [this] at hu
    rw [globalSwap_val_apply_of_not_mem _ _ _ ht_nm]

/-! ### Covariance theorem -/

/-- Compatibility lemma: the inverse `regionTransport` of the local restriction
at the translated region equals the local restriction of the inverse-translated
state at the inverse-translated index. -/
private theorem regionTransport_symm_wRestrict
    (act : HasGroupAction L G) (g : G) (Λ : Finset L)
    (w : globalHilbert L) (g_idx : globalIdx L) :
    (act.regionTransport g Λ).symm (wRestrict (act.regionImage g Λ) w g_idx)
      = wRestrict Λ ((act.unitaryAction g).symm w)
          ((act.globalIdxAction g).symm g_idx) := by
  apply (act.regionTransport g Λ).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext b'
  rw [act.regionTransport_apply_val]
  -- Now: (wRestrict Λ ((unitaryAction g).symm w) ((globalIdxAction g).symm g_idx))
  --        ((regionIdxAction g Λ).symm b')
  --      = (wRestrict (g·Λ) w g_idx) b'
  rw [wRestrict_apply, wRestrict_apply]
  -- Goal: w (globalSwap (g·Λ) b' g_idx) = ((unitaryAction g).symm w) (globalSwap Λ
  --        ((regionIdxAction g Λ).symm b') ((globalIdxAction g).symm g_idx))
  -- Use unitaryAction.symm formula.
  change (w : globalIdx L → ℂ) (globalSwap (act.regionImage g Λ) b' g_idx)
        = (((act.unitaryAction g).symm w : globalHilbert L) : globalIdx L → ℂ)
            (globalSwap Λ ((act.regionIdxAction g Λ).symm b')
              ((act.globalIdxAction g).symm g_idx))
  -- ((unitaryAction g).symm w).val a = w.val (globalIdxAction g a) by definition.
  have hsymm : ∀ a : globalIdx L,
      (((act.unitaryAction g).symm w : globalHilbert L) : globalIdx L → ℂ) a
        = (w : globalIdx L → ℂ) (act.globalIdxAction g a) := by
    intro a
    -- (unitaryAction g).symm sends f ↦ ⟨fun a => f.val (globalIdxAction g a), _⟩.
    rfl
  rw [hsymm]
  -- Apply globalIdxAction_globalSwap and simplify Equiv.apply_symm_apply.
  rw [act.globalIdxAction_globalSwap g Λ ((act.regionIdxAction g Λ).symm b') g_idx,
    Equiv.apply_symm_apply]

/-- **Covariance** (Verch 2025 §1.2 axiom (iii) / Naaijkens 2012 §1.3): the
operator-level action `algebraAut g` intertwines the embedding `localEmbed`
with the region-level transport `regionTransportAlg g Λ`:

`algebraAut g (localEmbed Λ M) = localEmbed (g · Λ) (regionTransportAlg g Λ M)`. -/
theorem algebraAut_localEmbed (act : HasGroupAction L G) (g : G)
    (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    act.algebraAut g (localEmbed Λ M)
      = localEmbed (act.regionImage g Λ) (act.regionTransportAlg g Λ M) := by
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  funext g_idx
  -- LHS at g_idx (via algebraAut = unitaryAction g ∘ · ∘ unitaryAction g.symm).
  have hLHS_eq :
      (((act.algebraAut g) (localEmbed Λ M) w : globalHilbert L)
            : globalIdx L → ℂ) g_idx
        = (((M (wRestrict Λ ((act.unitaryAction g).symm w)
                  ((act.globalIdxAction g).symm g_idx))
                : ℋ(Λ)) : regionIdx (L := L) Λ → ℂ)
                (regionRestrict Λ ((act.globalIdxAction g).symm g_idx))) := by
    -- algebraAut g T = unitaryAction g ∘L T ∘L (unitaryAction g).symm.
    rw [act.algebraAut_apply]
    -- (... ) w  unfolds to unitaryAction g (T ((unitaryAction g).symm w)).
    -- Coordinate at g_idx: by unitaryAction_apply_val.
    change (((act.unitaryAction g)
            (localEmbed Λ M ((act.unitaryAction g).symm w))
              : globalHilbert L) : globalIdx L → ℂ) g_idx
        = _
    rw [act.unitaryAction_apply_val,
      localEmbed_apply_apply]
    rfl
  -- RHS at g_idx via regionTransportAlg + regionTransport_apply_val + regionIdxAction_symm_regionRestrict.
  have hRHS_eq :
      ((localEmbed (act.regionImage g Λ) (act.regionTransportAlg g Λ M) w
            : globalHilbert L) : globalIdx L → ℂ) g_idx
        = (((M ((act.regionTransport g Λ).symm
                  (wRestrict (act.regionImage g Λ) w g_idx))
                : ℋ(Λ)) : regionIdx (L := L) Λ → ℂ)
                (regionRestrict Λ ((act.globalIdxAction g).symm g_idx))) := by
    rw [localEmbed_apply_apply]
    unfold localEmbedCoeff
    -- ((regionTransportAlg g Λ M) (wRestrict (g·Λ) w g_idx)).val (regionRestrict (g·Λ) g_idx)
    -- = (regionTransport g Λ (M (regionTransport.symm (wRestrict ...)))).val
    --     (regionRestrict (g·Λ) g_idx)
    -- = (M (regionTransport.symm (wRestrict ...))).val ((regionIdxAction g Λ).symm (regionRestrict (g·Λ) g_idx))
    -- = (M (...)).val (regionRestrict Λ ((globalIdxAction g).symm g_idx))
    --   [via regionIdxAction_symm_regionRestrict]
    change (((act.regionTransportAlg g Λ M)
              (wRestrict (act.regionImage g Λ) w g_idx)
                : ℋ(act.regionImage g Λ))
              : regionIdx (L := L) (act.regionImage g Λ) → ℂ)
                (regionRestrict (act.regionImage g Λ) g_idx) = _
    rw [show (act.regionTransportAlg g Λ M)
              (wRestrict (act.regionImage g Λ) w g_idx)
            = (act.regionTransport g Λ)
                (M ((act.regionTransport g Λ).symm
                      (wRestrict (act.regionImage g Λ) w g_idx))) from
        LinearIsometryEquiv.conjStarAlgEquiv_apply
          (act.regionTransport g Λ) M ▸ rfl]
    rw [regionTransport_apply_val, regionIdxAction_symm_regionRestrict]
  rw [hLHS_eq, hRHS_eq]
  -- Both sides have form (M(?)) (regionRestrict Λ ((globalIdxAction g).symm g_idx)).
  -- The arguments to M are equal by regionTransport_symm_wRestrict.
  rw [regionTransport_symm_wRestrict]

/-- Covariance at the StarSubalgebra level: `algebraAut g` maps
`localSubalgebra Λ` into `localSubalgebra (g · Λ)`. -/
theorem algebraAut_localSubalgebra_le (act : HasGroupAction L G) (g : G)
    (Λ : Finset L) :
    ∀ T ∈ localSubalgebra Λ,
      act.algebraAut g T ∈ localSubalgebra (act.regionImage g Λ) := by
  intro T hT
  obtain ⟨M, hM⟩ := (mem_localSubalgebra Λ T).mp hT
  refine (mem_localSubalgebra (act.regionImage g Λ) _).mpr
    ⟨act.regionTransportAlg g Λ M, ?_⟩
  rw [← hM, act.algebraAut_localEmbed]

/-! ### Lift to the quasi-local algebra

The covariance theorems above act on individual local subalgebras
`localSubalgebra Λ`.  We now lift them through the supremum
`quasiLocalSubalg L = ⨆ Λ, localSubalgebra Λ` and through its
norm closure `quasiLocal L`. -/

/-- Covariance at the algebraic-core level: `algebraAut g` maps
`quasiLocalSubalg L` into itself.  This is the algebraic preparation for
the lift to the full quasi-local algebra (see `algebraAut_quasiLocal_le`). -/
theorem algebraAut_quasiLocalSubalg_le (act : HasGroupAction L G) (g : G) :
    ∀ T ∈ quasiLocalSubalg L,
      act.algebraAut g T ∈ quasiLocalSubalg L := by
  -- It suffices to show `quasiLocalSubalg L ≤ comap (algebraAut g) (quasiLocalSubalg L)`.
  intro T hT
  suffices h : quasiLocalSubalg L
      ≤ (quasiLocalSubalg L).comap
          ((act.algebraAut g : _ →⋆ₐ[ℂ] _)) by
    exact h hT
  -- Decompose `⨆ ≤ X` via `iSup_le` and use the Galois connection
  -- `map_le_iff_le_comap` to reduce to `algebraAut_localSubalgebra_le`.
  refine iSup_le ?_
  intro Λ
  rw [← StarSubalgebra.map_le_iff_le_comap]
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := hT'
  exact localSubalgebra_le_quasiLocalSubalg L (act.regionImage g Λ)
    (algebraAut_localSubalgebra_le act g Λ T hT)

/-- The operator-algebra automorphism `algebraAut g` is continuous in the
operator-norm topology: it factors through the continuous algebra equivalence
`(unitaryAction g).toContinuousLinearEquiv.conjContinuousAlgEquiv`. -/
theorem continuous_algebraAut (act : HasGroupAction L G) (g : G) :
    Continuous (act.algebraAut g) := by
  -- algebraAut g = StarAlgEquiv.ofAlgEquiv (conjContinuousAlgEquiv (unitaryAction g)).
  -- Both are the same function, and conjContinuousAlgEquiv is continuous.
  change Continuous
    fun T : globalHilbert L →L[ℂ] globalHilbert L =>
      (act.unitaryAction g).toContinuousLinearEquiv.conjContinuousAlgEquiv T
  exact (act.unitaryAction g).toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous_toFun

/-- **Covariance** at the quasi-local level (Verch 2025 §1.2 axiom (iii) /
Naaijkens 2012 §1.3): the operator-level action `algebraAut g` maps the full
quasi-local algebra `quasiLocal L` into itself.

The proof combines the algebraic lift `algebraAut_quasiLocalSubalg_le` with
continuity of `algebraAut g`: the comap of `quasiLocal L` under `algebraAut g`
contains `quasiLocalSubalg L` and is closed, hence contains the topological
closure `quasiLocal L`. -/
theorem algebraAut_quasiLocal_le (act : HasGroupAction L G) (g : G) :
    ∀ T ∈ quasiLocal L,
      act.algebraAut g T ∈ quasiLocal L := by
  intro T hT
  suffices h : quasiLocal L
      ≤ (quasiLocal L).comap ((act.algebraAut g : _ →⋆ₐ[ℂ] _)) by
    exact h hT
  -- Apply `topologicalClosure_minimal`.  We need (a) `qsa ≤ comap` and
  -- (b) the comap is closed.
  refine StarSubalgebra.topologicalClosure_minimal ?_ ?_
  · -- (a): for `T ∈ qsa`, `algebraAut g T ∈ qsa ⊆ quasiLocal L`.
    intro T' hT'
    change act.algebraAut g T' ∈ quasiLocal L
    exact quasiLocalSubalg_le_quasiLocal L
      (algebraAut_quasiLocalSubalg_le act g T' hT')
  · -- (b): preimage of a closed set under a continuous map is closed.
    rw [StarSubalgebra.coe_comap]
    exact (isClosed_quasiLocal L).preimage (continuous_algebraAut act g)

/-- The covariance endomorphism induced on the bundled quasi-local algebra.

This packages `algebraAut_quasiLocal_le` as a `*`-algebra homomorphism
`quasiLocal L →⋆ₐ[ℂ] quasiLocal L`, so downstream statements can work inside the
quasi-local algebra subtype rather than repeatedly carrying membership proofs. -/
noncomputable def quasiLocalEnd (act : HasGroupAction L G) (g : G) :
    quasiLocal L →⋆ₐ[ℂ] quasiLocal L where
  toFun T := ⟨act.algebraAut g T.1, algebraAut_quasiLocal_le act g T.1 T.2⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' T U := by
    apply Subtype.ext
    simp
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' T U := by
    apply Subtype.ext
    simp
  commutes' c := by
    apply Subtype.ext
    exact (act.algebraAut g).toAlgEquiv.toAlgHom.commutes c
  map_star' T := by
    apply Subtype.ext
    exact map_star (act.algebraAut g) (T : globalHilbert L →L[ℂ] globalHilbert L)

@[simp]
theorem quasiLocalEnd_apply (act : HasGroupAction L G) (g : G) (T : quasiLocal L) :
    (act.quasiLocalEnd g T : globalHilbert L →L[ℂ] globalHilbert L) =
      act.algebraAut g (T : globalHilbert L →L[ℂ] globalHilbert L) :=
  rfl

/-! ### Genuine covariance as automorphisms of the quasi-local algebra -/

/-- Under a genuine action, each group element induces a `*`-algebra automorphism of the
bundled quasi-local algebra.  The inverse is the automorphism induced by `g⁻¹`. -/
noncomputable def quasiLocalAut (act : HasGroupAction L G) [act.IsGenuineAction]
    (g : G) :
    quasiLocal L ≃⋆ₐ[ℂ] quasiLocal L where
  toFun T := ⟨act.algebraAut g T.1, algebraAut_quasiLocal_le act g T.1 T.2⟩
  invFun T := ⟨act.algebraAut g⁻¹ T.1, algebraAut_quasiLocal_le act g⁻¹ T.1 T.2⟩
  left_inv T := by
    apply Subtype.ext
    have h := congrArg
      (fun e : (globalHilbert L →L[ℂ] globalHilbert L)
          ≃⋆ₐ[ℂ] (globalHilbert L →L[ℂ] globalHilbert L) =>
        e (T : globalHilbert L →L[ℂ] globalHilbert L))
      (act.algebraAut_mul g⁻¹ g)
    simpa [inv_mul_cancel, algebraAut_one] using h.symm
  right_inv T := by
    apply Subtype.ext
    have h := congrArg
      (fun e : (globalHilbert L →L[ℂ] globalHilbert L)
          ≃⋆ₐ[ℂ] (globalHilbert L →L[ℂ] globalHilbert L) =>
        e (T : globalHilbert L →L[ℂ] globalHilbert L))
      (act.algebraAut_mul g g⁻¹)
    simpa [mul_inv_cancel, algebraAut_one] using h.symm
  map_mul' T U := by
    apply Subtype.ext
    exact map_mul (act.algebraAut g)
      (T : globalHilbert L →L[ℂ] globalHilbert L)
      (U : globalHilbert L →L[ℂ] globalHilbert L)
  map_add' T U := by
    apply Subtype.ext
    exact map_add (act.algebraAut g)
      (T : globalHilbert L →L[ℂ] globalHilbert L)
      (U : globalHilbert L →L[ℂ] globalHilbert L)
  map_star' T := by
    apply Subtype.ext
    exact map_star (act.algebraAut g)
      (T : globalHilbert L →L[ℂ] globalHilbert L)
  map_smul' c T := by
    apply Subtype.ext
    exact map_smul (act.algebraAut g) c
      (T : globalHilbert L →L[ℂ] globalHilbert L)

@[simp]
theorem quasiLocalAut_apply (act : HasGroupAction L G) [act.IsGenuineAction]
    (g : G) (T : quasiLocal L) :
    (act.quasiLocalAut g T : globalHilbert L →L[ℂ] globalHilbert L) =
      act.algebraAut g (T : globalHilbert L →L[ℂ] globalHilbert L) :=
  rfl

/-- The quasi-local automorphism assigned to the identity acts trivially. -/
theorem quasiLocalAut_one_apply (act : HasGroupAction L G) [act.IsGenuineAction]
    (T : quasiLocal L) :
    act.quasiLocalAut 1 T = T := by
  apply Subtype.ext
  simp [quasiLocalAut_apply, algebraAut_one]

/-- The quasi-local automorphisms compose according to group multiplication. -/
theorem quasiLocalAut_mul_apply (act : HasGroupAction L G) [act.IsGenuineAction]
    (g h : G) (T : quasiLocal L) :
    act.quasiLocalAut (g * h) T = act.quasiLocalAut g (act.quasiLocalAut h T) := by
  apply Subtype.ext
  simp [quasiLocalAut_apply, algebraAut_mul]

end HasGroupAction

end LocalNetLike
