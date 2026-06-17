module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.QuasiLocal

/-!
# Group action data and the covariance theorem for the quasi-local algebra

Kinematic data for a `G`-equivariant `LocalNetLike` (Verch 2025 §1.2 axiom iii /
Naaijkens 2012 §1.3): a site permutation together with per-site index
equivalences preserving the sector tuple `Ω`.  The compatibility lifts the
action to `globalIdx L Ω`, a unitary representation on `globalHilbert L Ω`,
a `*`-algebra automorphism on `B(globalHilbert L Ω)`, and finally to a
`*`-algebra automorphism of the quasi-local algebra `quasiLocal L Ω`.

## Main definitions

* `LocalNetLike.HasGroupAction L Ω G` — group action data with sector
  compatibility.
* `LocalNetLike.HasGroupAction.globalIdxAction g` / `unitaryAction g` /
  `algebraAut g` — successive lifts of the site action.
* `LocalNetLike.HasGroupAction.quasiLocalEnd g` / `quasiLocalAut g` —
  endomorphism / automorphism of `quasiLocal L Ω`.
* `LocalNetLike.HasGroupAction.algebraAut_quasiLocal_le` — the covariance
  theorem at the quasi-local level.

## References

* Verch 2025 (https://arxiv.org/abs/2507.00900) §1.2 axiom (iii).
* Naaijkens 2012 §1.3.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
variable (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)

/-- **Group action data** for a `LocalNetLike` at the sector tuple `Ω`.

* `siteAction g : Equiv.Perm L` — site permutation.
* `siteIdxEquiv g s : localIdx s ≃ localIdx (siteAction g s)` — per-site
  identification of local Hilbert spaces.
* `siteIdxEquiv_sectorVec` — sector compatibility: `siteIdxEquiv g s (Ω s) =
  Ω (siteAction g s)`.  Ensures the action descends to `globalIdx L Ω`.
* `siteIdxEquiv_one` / `siteIdxEquiv_mul` — functoriality of the fibre
  equivalences: they form a genuine `G`-action on the index bundle.  These are
  the coherence laws that make `piAction` a monoid homomorphism (see
  `piAction_one` / `piAction_mul`).  They are stated at the level of elements
  via `HEq`, since the codomain `localIdx (siteAction g s)` depends on `g` and a
  plain `Equiv` equation would be ill-typed. -/
structure HasGroupAction (G : Type*) [Group G] where
  /-- Action on sites as a group hom into permutations. -/
  siteAction : G →* Equiv.Perm L
  /-- Per-site equivalence of local Hilbert-space indices. -/
  siteIdxEquiv : ∀ (g : G) (s : L),
    LocalNetLike.localIdx (L := L) s
      ≃ LocalNetLike.localIdx (L := L) (siteAction g s)
  /-- The action preserves the sector tuple `Ω`. -/
  siteIdxEquiv_sectorVec :
    ∀ (g : G) (s : L),
      siteIdxEquiv g s (Ω s) = Ω (siteAction g s)
  /-- Identity coherence: the unit acts as the identity on each fibre. -/
  siteIdxEquiv_one : ∀ (s : L) (x : LocalNetLike.localIdx (L := L) s),
    HEq (siteIdxEquiv 1 s x) x
  /-- Composition coherence: the fibre equivalences compose along the group
  law, so they assemble into a genuine `G`-action on the index bundle. -/
  siteIdxEquiv_mul : ∀ (g h : G) (s : L) (x : LocalNetLike.localIdx (L := L) s),
    HEq (siteIdxEquiv (g * h) s x)
        (siteIdxEquiv g (siteAction h s) (siteIdxEquiv h s x))

namespace HasGroupAction

variable {L Ω}
variable {G : Type*} [Group G]

/-- The `G`-translate of a finite region: the Finset image under `siteAction g`. -/
def regionImage (act : HasGroupAction L Ω G) (g : G) (Λ : Finset L) : Finset L :=
  Λ.image (act.siteAction g)

/-- The induced permutation of `(s : L) → localIdx s`.  Its restriction to
the finite-variation subtype `globalIdx L Ω` is `globalIdxAction`. -/
noncomputable def piAction (act : HasGroupAction L Ω G) (g : G) :
    ((s : L) → LocalNetLike.localIdx (L := L) s)
      ≃ ((s : L) → LocalNetLike.localIdx (L := L) s) :=
  Equiv.piCongr (act.siteAction g) (fun s => act.siteIdxEquiv g s)

/-- Pointwise formula for `piAction` evaluated at `siteAction g s`. -/
theorem piAction_apply_apply
    (act : HasGroupAction L Ω G) (g : G)
    (f : (s : L) → LocalNetLike.localIdx (L := L) s) (s : L) :
    piAction act g f (act.siteAction g s) = act.siteIdxEquiv g s (f s) :=
  Equiv.piCongr_apply_apply (act.siteAction g)
    (fun s => act.siteIdxEquiv g s) f s

/-! ### Functoriality of the action

The fibre coherence laws `siteIdxEquiv_one` / `siteIdxEquiv_mul` bundled into
`HasGroupAction` make `piAction` a monoid homomorphism
`G →* Equiv.Perm ((s : L) → localIdx s)`.  This functoriality is what the
downstream lifts (`globalIdxAction`, `unitaryAction`, `algebraAut`,
`quasiLocalAut`) need to be functorial in `G`; we prove it here from the
coherence data rather than assuming it. -/

/-- The identity group element acts trivially on dependent site-index tuples. -/
theorem piAction_one (act : HasGroupAction L Ω G) :
    act.piAction 1 = Equiv.refl _ := by
  ext f t
  obtain ⟨s, rfl⟩ : ∃ s, act.siteAction 1 s = t :=
    ⟨(act.siteAction 1).symm t, Equiv.apply_symm_apply _ _⟩
  rw [piAction_apply_apply, Equiv.refl_apply]
  have h1 : act.siteAction 1 s = s := by rw [map_one]; rfl
  exact eq_of_heq ((act.siteIdxEquiv_one s (f s)).trans (congr_arg_heq f h1.symm))

/-- Multiplication is respected by the dependent site-index action. -/
theorem piAction_mul (act : HasGroupAction L Ω G) (g h : G) :
    act.piAction (g * h) = (act.piAction h).trans (act.piAction g) := by
  ext f t
  obtain ⟨s, rfl⟩ : ∃ s, act.siteAction (g * h) s = t :=
    ⟨(act.siteAction (g * h)).symm t, Equiv.apply_symm_apply _ _⟩
  have hsplit : act.siteAction (g * h) s = act.siteAction g (act.siteAction h s) := by
    rw [map_mul]; rfl
  rw [piAction_apply_apply, Equiv.trans_apply]
  refine eq_of_heq (HEq.trans (act.siteIdxEquiv_mul g h s (f s)) ?_)
  have e1 : act.piAction g (act.piAction h f) (act.siteAction g (act.siteAction h s))
              = act.siteIdxEquiv g (act.siteAction h s)
                  (act.piAction h f (act.siteAction h s)) :=
    piAction_apply_apply act g (act.piAction h f) (act.siteAction h s)
  have e2 : act.piAction h f (act.siteAction h s) = act.siteIdxEquiv h s (f s) :=
    piAction_apply_apply act h f s
  rw [e2] at e1
  exact (heq_of_eq e1).symm.trans
    (congr_arg_heq (act.piAction g (act.piAction h f)) hsplit).symm

/-- The `g`-translate sends finite-variation tuples to finite-variation
tuples: a `Γ`-witness for `f` translates to a `Γ.image (siteAction g)`-witness
for `piAction g f`. -/
theorem piAction_finite_variation
    (act : HasGroupAction L Ω G) (g : G)
    {f : (s : L) → LocalNetLike.localIdx (L := L) s}
    {Γ : Finset L} (hf : ∀ s ∉ Γ, f s = Ω s) :
    ∀ t ∉ Γ.image (act.siteAction g),
      piAction act g f t = Ω t := by
  intro t ht
  obtain ⟨s, rfl⟩ : ∃ s, act.siteAction g s = t :=
    ⟨(act.siteAction g).symm t, Equiv.apply_symm_apply _ _⟩
  have hs : s ∉ Γ := fun hin => ht (Finset.mem_image.mpr ⟨s, hin, rfl⟩)
  rw [piAction_apply_apply, hf s hs, act.siteIdxEquiv_sectorVec]

/-- Symmetric statement: the inverse `piAction g` also preserves finite
variation, with the witness translating along `(siteAction g).symm`. -/
theorem piAction_symm_finite_variation
    (act : HasGroupAction L Ω G) (g : G)
    {h : (s : L) → LocalNetLike.localIdx (L := L) s}
    {Γ' : Finset L} (hh : ∀ t ∉ Γ', h t = Ω t) :
    ∀ s ∉ Γ'.image (act.siteAction g).symm,
      (piAction act g).symm h s = Ω s := by
  intro s hs
  have ht : act.siteAction g s ∉ Γ' := by
    intro hin
    apply hs
    rw [Finset.mem_image]
    exact ⟨act.siteAction g s, hin, Equiv.symm_apply_apply _ _⟩
  have hsym :
      (piAction act g).symm h
        = fun s => (act.siteIdxEquiv g s).symm (h (act.siteAction g s)) :=
    Equiv.piCongr_symm_apply (act.siteAction g)
      (fun s => act.siteIdxEquiv g s) h
  rw [show (piAction act g).symm h s
        = (act.siteIdxEquiv g s).symm (h (act.siteAction g s)) from
      congrFun hsym s]
  rw [hh _ ht, ← act.siteIdxEquiv_sectorVec g s]
  exact (act.siteIdxEquiv g s).symm_apply_apply _

/-- The lift of the site action to a permutation of `globalIdx L Ω`. -/
noncomputable def globalIdxAction (act : HasGroupAction L Ω G) (g : G) :
    globalIdx L Ω ≃ globalIdx L Ω :=
  Equiv.subtypeEquiv (act.piAction g) (fun f => by
    refine ⟨fun ⟨Γ, hΓ⟩ => ⟨Γ.image (act.siteAction g),
              piAction_finite_variation act g hΓ⟩,
            fun ⟨Γ', hΓ'⟩ => ⟨Γ'.image (act.siteAction g).symm, ?_⟩⟩
    have hf_eq : f = (act.piAction g).symm (act.piAction g f) :=
      ((act.piAction g).symm_apply_apply f).symm
    intro s hs
    rw [hf_eq]
    exact piAction_symm_finite_variation act g hΓ' s hs)

@[simp]
theorem globalIdxAction_val (act : HasGroupAction L Ω G) (g : G) (f : globalIdx L Ω) :
    (globalIdxAction act g f).val = piAction act g f.val := rfl

/-- Under a genuine action, the identity element acts trivially on `globalIdx`. -/
theorem globalIdxAction_one (act : HasGroupAction L Ω G) :
    act.globalIdxAction 1 = Equiv.refl (globalIdx L Ω) := by
  ext f
  apply Subtype.ext
  simp [globalIdxAction_val, act.piAction_one]

/-- Under a genuine action, multiplication is respected on `globalIdx`. -/
theorem globalIdxAction_mul (act : HasGroupAction L Ω G)
    (g h : G) :
    act.globalIdxAction (g * h) = (act.globalIdxAction h).trans (act.globalIdxAction g) := by
  ext f
  apply Subtype.ext
  simp [globalIdxAction_val, act.piAction_mul g h]

/-! ### Unitary representation on `globalHilbert L Ω` -/

/-- Membership in `lp (... ℂ) 2` is preserved by reindexing along an `Equiv`
on the index. -/
theorem lp_memℓp_reindex (e : globalIdx L Ω ≃ globalIdx L Ω)
    {f : globalIdx L Ω → ℂ} (hf : Memℓp f 2) :
    Memℓp (fun a => f (e.symm a)) 2 := by
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  rw [memℓp_gen_iff htwo] at hf ⊢
  exact (e.symm.summable_iff
    (f := fun b => ‖f b‖ ^ ((2 : ENNReal).toReal))).mpr hf

/-- The unitary representation on `globalHilbert L Ω` induced by the site
action: a basis-permutation isometry sending `lp.single 2 j 1` to
`lp.single 2 (globalIdxAction g j) 1`. -/
noncomputable def unitaryAction (act : HasGroupAction L Ω G) (g : G) :
    globalHilbert L Ω ≃ₗᵢ[ℂ] globalHilbert L Ω where
  toFun f :=
    ⟨fun a => (f : globalIdx L Ω → ℂ) ((globalIdxAction act g).symm a),
      lp_memℓp_reindex (globalIdxAction act g) (lp.memℓp f)⟩
  invFun f :=
    ⟨fun a => (f : globalIdx L Ω → ℂ) (globalIdxAction act g a),
      by
        have hf : Memℓp (fun a => (f : globalIdx L Ω → ℂ)
              ((globalIdxAction act g).symm.symm a)) 2 :=
          lp_memℓp_reindex (globalIdxAction act g).symm (lp.memℓp f)
        simp only [Equiv.symm_symm] at hf
        exact hf⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    change (f : globalIdx L Ω → ℂ)
        ((globalIdxAction act g).symm (globalIdxAction act g a)) = _
    rw [Equiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext a
    change (f : globalIdx L Ω → ℂ)
        (globalIdxAction act g ((globalIdxAction act g).symm a)) = _
    rw [Equiv.apply_symm_apply]
  map_add' f₁ f₂ := by
    apply Subtype.ext
    funext a
    change ((f₁ + f₂ : lp (fun _ : globalIdx L Ω => ℂ) 2) : globalIdx L Ω → ℂ)
            ((globalIdxAction act g).symm a)
        = (f₁ : globalIdx L Ω → ℂ) ((globalIdxAction act g).symm a)
          + (f₂ : globalIdx L Ω → ℂ) ((globalIdxAction act g).symm a)
    exact congrFun (lp.coeFn_add f₁ f₂) _
  map_smul' c f := by
    apply Subtype.ext
    funext a
    change ((c • f : lp (fun _ : globalIdx L Ω => ℂ) 2) : globalIdx L Ω → ℂ)
            ((globalIdxAction act g).symm a)
        = c • (f : globalIdx L Ω → ℂ) ((globalIdxAction act g).symm a)
    exact congrFun (lp.coeFn_smul c f) _
  norm_map' f := by
    have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
      rw [ENNReal.toReal_ofNat]; norm_num
    set Uf : globalHilbert L Ω :=
      ⟨fun a => (f : globalIdx L Ω → ℂ) ((globalIdxAction act g).symm a),
        lp_memℓp_reindex (globalIdxAction act g) (lp.memℓp f)⟩
    change ‖Uf‖ = ‖f‖
    have hLHS := lp.norm_rpow_eq_tsum (E := fun _ : globalIdx L Ω => ℂ) (p := 2)
      htwo Uf
    have hRHS := lp.norm_rpow_eq_tsum (E := fun _ : globalIdx L Ω => ℂ) (p := 2)
      htwo f
    have hsum :
        ∑' a : globalIdx L Ω,
            ‖(f : globalIdx L Ω → ℂ) ((globalIdxAction act g).symm a)‖
              ^ ((2 : ENNReal).toReal)
          = ∑' b : globalIdx L Ω,
              ‖(f : globalIdx L Ω → ℂ) b‖ ^ ((2 : ENNReal).toReal) :=
      Equiv.tsum_eq (globalIdxAction act g).symm
        (fun b => ‖(f : globalIdx L Ω → ℂ) b‖ ^ ((2 : ENNReal).toReal))
    have hpow : ‖Uf‖ ^ ((2 : ENNReal).toReal) = ‖f‖ ^ ((2 : ENNReal).toReal) := by
      rw [hLHS, hRHS]; exact hsum
    have h2real : (2 : ENNReal).toReal = 2 := by simp
    rw [h2real] at hpow
    have hpow_nat : ‖Uf‖ ^ (2 : ℕ) = ‖f‖ ^ (2 : ℕ) := by
      have hUf := Real.rpow_natCast ‖Uf‖ 2
      have hf := Real.rpow_natCast ‖f‖ 2
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from rfl] at hUf hf
      rw [← hUf, ← hf]; exact_mod_cast hpow
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow_nat

@[simp]
theorem unitaryAction_apply_val (act : HasGroupAction L Ω G) (g : G)
    (f : globalHilbert L Ω) (a : globalIdx L Ω) :
    ((unitaryAction act g f : globalHilbert L Ω) : globalIdx L Ω → ℂ) a
      = (f : globalIdx L Ω → ℂ) ((globalIdxAction act g).symm a) := rfl

/-- Under a genuine action, the identity element is implemented by the identity unitary. -/
theorem unitaryAction_one (act : HasGroupAction L Ω G) :
    act.unitaryAction 1 = LinearIsometryEquiv.refl ℂ (globalHilbert L Ω) := by
  ext f a
  simp [unitaryAction_apply_val, globalIdxAction_one]

/-- Under a genuine action, the implementing unitaries multiply according to the group law. -/
theorem unitaryAction_mul (act : HasGroupAction L Ω G)
    (g h : G) :
    act.unitaryAction (g * h) = (act.unitaryAction h).trans (act.unitaryAction g) := by
  ext f a
  simp [unitaryAction_apply_val, globalIdxAction_mul]

/-! ### Algebra automorphism via conjugation by the unitary representation -/

/-- The `*`-algebra automorphism of `B(globalHilbert L Ω)` induced by conjugation
by the unitary representation `unitaryAction g`.  This is the operator-level
realisation of the action used in the covariance axiom (Verch 2025 §1.2 axiom
iii). -/
noncomputable def algebraAut (act : HasGroupAction L Ω G) (g : G) :
    (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
      ≃⋆ₐ[ℂ] (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :=
  (act.unitaryAction g).conjStarAlgEquiv

theorem algebraAut_apply (act : HasGroupAction L Ω G) (g : G)
    (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :
    act.algebraAut g T
      = (act.unitaryAction g).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (T.comp (act.unitaryAction g).symm.toContinuousLinearEquiv.toContinuousLinearMap) :=
  LinearIsometryEquiv.conjStarAlgEquiv_apply _ _

/-- Under a genuine action, the identity group element induces the identity automorphism. -/
theorem algebraAut_one (act : HasGroupAction L Ω G) :
    act.algebraAut 1 =
      StarAlgEquiv.refl (R := ℂ) (A := globalHilbert L Ω →L[ℂ] globalHilbert L Ω) := by
  unfold algebraAut
  rw [unitaryAction_one]
  exact LinearIsometryEquiv.conjStarAlgEquiv_refl

/-- Under a genuine action, the induced automorphisms compose according to the group law. -/
theorem algebraAut_mul (act : HasGroupAction L Ω G)
    (g h : G) :
    act.algebraAut (g * h) = (act.algebraAut h).trans (act.algebraAut g) := by
  unfold algebraAut
  rw [unitaryAction_mul]
  exact LinearIsometryEquiv.conjStarAlgEquiv_trans _ _

/-! ### Region-level transport: lifting `g` to `regionHilbert` -/

/-- The `g`-translate of `↥Λ` to `↥(regionImage g Λ)`. -/
def siteSubtypeEquiv (act : HasGroupAction L Ω G) (g : G) (Λ : Finset L) :
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
noncomputable def regionIdxAction (act : HasGroupAction L Ω G) (g : G)
    (Λ : Finset L) :
    regionIdx (L := L) Λ ≃ regionIdx (L := L) (act.regionImage g Λ) :=
  Equiv.piCongr (act.siteSubtypeEquiv g Λ) (fun a => act.siteIdxEquiv g a.val)

/-- The unitary `regionHilbert Λ ≃ₗᵢ[ℂ] regionHilbert (g · Λ)` induced by the
group action.  Built from the orthonormal basis of `EuclideanSpace ℂ` on each
side via `OrthonormalBasis.equiv` and the index bijection `regionIdxAction`. -/
noncomputable def regionTransport (act : HasGroupAction L Ω G) (g : G)
    (Λ : Finset L) :
    ℋ(Λ) ≃ₗᵢ[ℂ] ℋ(act.regionImage g Λ) :=
  (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).equiv
    (EuclideanSpace.basisFun (regionIdx (L := L) (act.regionImage g Λ)) ℂ)
    (act.regionIdxAction g Λ)

/-- The `*`-algebra automorphism on `B(regionHilbert Λ)` and `B(regionHilbert (g · Λ))`
induced by `regionTransport`, used to express the covariance theorem. -/
noncomputable def regionTransportAlg (act : HasGroupAction L Ω G) (g : G)
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
    (act : HasGroupAction L Ω G) (g : G) (Λ : Finset L)
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
  rw [map_sum]
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
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single ((act.regionIdxAction g Λ).symm a')]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
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
theorem regionIdxAction_symm_regionRestrict (act : HasGroupAction L Ω G) (g : G)
    (Λ : Finset L) (g_idx : globalIdx L Ω) :
    (act.regionIdxAction g Λ).symm (regionRestrict (act.regionImage g Λ) g_idx)
      = regionRestrict Λ ((act.globalIdxAction g).symm g_idx) := by
  funext s
  -- Both sides reduce to `(siteIdxEquiv g s.1).symm (g_idx.val (siteAction g s.1))`.
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
theorem globalIdxAction_globalSwap (act : HasGroupAction L Ω G) (g : G)
    (Λ : Finset L) (b : regionIdx (L := L) Λ) (g_idx : globalIdx L Ω) :
    act.globalIdxAction g
        (globalSwap Λ b ((act.globalIdxAction g).symm g_idx))
      = globalSwap (act.regionImage g Λ) (act.regionIdxAction g Λ b) g_idx := by
  apply Subtype.ext
  funext t
  obtain ⟨s, rfl⟩ : ∃ s, act.siteAction g s = t :=
    ⟨(act.siteAction g).symm t, Equiv.apply_symm_apply _ _⟩
  change (piAction act g (globalSwap Λ b
          ((act.globalIdxAction g).symm g_idx)).val) (act.siteAction g s) = _
  rw [piAction_apply_apply]
  by_cases hs : s ∈ Λ
  · rw [globalSwap_val_apply_of_mem _ _ _ hs]
    have ht : act.siteAction g s ∈ act.regionImage g Λ :=
      Finset.mem_image.mpr ⟨s, hs, rfl⟩
    rw [globalSwap_val_apply_of_mem _ _ _ ht]
    have key := Equiv.piCongr_apply_apply (W := fun a : ↥Λ => localIdx a.1)
      (Z := fun b : ↥(act.regionImage g Λ) => localIdx b.1)
      (act.siteSubtypeEquiv g Λ)
      (fun a => act.siteIdxEquiv g a.1) b ⟨s, hs⟩
    exact key.symm
  · rw [globalSwap_val_apply_of_not_mem _ _ _ hs]
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
    rw [Equiv.apply_symm_apply]
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
    (act : HasGroupAction L Ω G) (g : G) (Λ : Finset L)
    (w : globalHilbert L Ω) (g_idx : globalIdx L Ω) :
    (act.regionTransport g Λ).symm (wRestrict (act.regionImage g Λ) w g_idx)
      = wRestrict Λ ((act.unitaryAction g).symm w)
          ((act.globalIdxAction g).symm g_idx) := by
  apply (act.regionTransport g Λ).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext b'
  rw [act.regionTransport_apply_val]
  rw [wRestrict_apply, wRestrict_apply]
  change (w : globalIdx L Ω → ℂ) (globalSwap (act.regionImage g Λ) b' g_idx)
        = (((act.unitaryAction g).symm w : globalHilbert L Ω) : globalIdx L Ω → ℂ)
            (globalSwap Λ ((act.regionIdxAction g Λ).symm b')
              ((act.globalIdxAction g).symm g_idx))
  -- `((unitaryAction g).symm w).val a = w.val (globalIdxAction g a)` by definition.
  have hsymm : ∀ a : globalIdx L Ω,
      (((act.unitaryAction g).symm w : globalHilbert L Ω) : globalIdx L Ω → ℂ) a
        = (w : globalIdx L Ω → ℂ) (act.globalIdxAction g a) := fun _ => rfl
  rw [hsymm]
  rw [act.globalIdxAction_globalSwap g Λ ((act.regionIdxAction g Λ).symm b') g_idx,
    Equiv.apply_symm_apply]

/-- **Covariance** (Verch 2025 §1.2 axiom (iii) / Naaijkens 2012 §1.3): the
operator-level action `algebraAut g` intertwines the embedding `localEmbed`
with the region-level transport `regionTransportAlg g Λ`:

`algebraAut g (localEmbed Λ M) = localEmbed (g · Λ) (regionTransportAlg g Λ M)`. -/
theorem algebraAut_localEmbed (act : HasGroupAction L Ω G) (g : G)
    (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    act.algebraAut g (localEmbed Λ M)
      = localEmbed (act.regionImage g Λ) (act.regionTransportAlg g Λ M) := by
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  funext g_idx
  have hLHS_eq :
      (((act.algebraAut g) (localEmbed Λ M) w : globalHilbert L Ω)
            : globalIdx L Ω → ℂ) g_idx
        = (((M (wRestrict Λ ((act.unitaryAction g).symm w)
                  ((act.globalIdxAction g).symm g_idx))
                : ℋ(Λ)) : regionIdx (L := L) Λ → ℂ)
                (regionRestrict Λ ((act.globalIdxAction g).symm g_idx))) := by
    rw [act.algebraAut_apply]
    change (((act.unitaryAction g)
            (localEmbed Λ M ((act.unitaryAction g).symm w))
              : globalHilbert L Ω) : globalIdx L Ω → ℂ) g_idx
        = _
    rw [act.unitaryAction_apply_val,
      localEmbed_apply_apply]
    rfl
  have hRHS_eq :
      ((localEmbed (act.regionImage g Λ) (act.regionTransportAlg g Λ M) w
            : globalHilbert L Ω) : globalIdx L Ω → ℂ) g_idx
        = (((M ((act.regionTransport g Λ).symm
                  (wRestrict (act.regionImage g Λ) w g_idx))
                : ℋ(Λ)) : regionIdx (L := L) Λ → ℂ)
                (regionRestrict Λ ((act.globalIdxAction g).symm g_idx))) := by
    rw [localEmbed_apply_apply]
    unfold localEmbedCoeff
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
  -- Both sides match after equating the arguments of `M` via `regionTransport_symm_wRestrict`.
  rw [regionTransport_symm_wRestrict]

/-- Covariance at the StarSubalgebra level: `algebraAut g` maps
`localSubalgebra (Ω := Ω) Λ` into `localSubalgebra (g · Λ)`. -/
theorem algebraAut_localSubalgebra_le (act : HasGroupAction L Ω G) (g : G)
    (Λ : Finset L) :
    ∀ T ∈ localSubalgebra (Ω := Ω) Λ,
      act.algebraAut g T ∈ localSubalgebra (act.regionImage g Λ) := by
  intro T hT
  obtain ⟨M, hM⟩ := (mem_localSubalgebra (Ω := Ω) Λ T).mp hT
  refine (mem_localSubalgebra (act.regionImage g Λ) _).mpr
    ⟨act.regionTransportAlg g Λ M, ?_⟩
  rw [← hM, act.algebraAut_localEmbed]

/-! ### Lift to the quasi-local algebra

The local covariance above lifts through the supremum
`quasiLocalSubalg L Ω = ⨆ Λ, localSubalgebra (Ω := Ω) Λ` and its norm
closure `quasiLocal L Ω`. -/

/-- Covariance at the algebraic-core level: `algebraAut g` maps
`quasiLocalSubalg L Ω` into itself. -/
theorem algebraAut_quasiLocalSubalg_le (act : HasGroupAction L Ω G) (g : G) :
    ∀ T ∈ quasiLocalSubalg L Ω,
      act.algebraAut g T ∈ quasiLocalSubalg L Ω := by
  intro T hT
  suffices h : quasiLocalSubalg L Ω
      ≤ (quasiLocalSubalg L Ω).comap
          ((act.algebraAut g : _ →⋆ₐ[ℂ] _)) by
    exact h hT
  refine iSup_le ?_
  intro Λ
  rw [← StarSubalgebra.map_le_iff_le_comap]
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := hT'
  exact localSubalgebra_le_quasiLocalSubalg L Ω (act.regionImage g Λ)
    (algebraAut_localSubalgebra_le act g Λ T hT)

/-- The operator-algebra automorphism `algebraAut g` is continuous in the
operator-norm topology: it factors through the continuous algebra equivalence
`(unitaryAction g).toContinuousLinearEquiv.conjContinuousAlgEquiv`. -/
theorem continuous_algebraAut (act : HasGroupAction L Ω G) (g : G) :
    Continuous (act.algebraAut g) := by
  -- algebraAut g = StarAlgEquiv.ofAlgEquiv (conjContinuousAlgEquiv (unitaryAction g)).
  -- Both are the same function, and conjContinuousAlgEquiv is continuous.
  change Continuous
    fun T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω =>
      (act.unitaryAction g).toContinuousLinearEquiv.conjContinuousAlgEquiv T
  exact (act.unitaryAction g).toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous_toFun

/-- **Covariance** at the quasi-local level (Verch 2025 §1.2 axiom (iii) /
Naaijkens 2012 §1.3): the operator-level action `algebraAut g` maps the full
quasi-local algebra `quasiLocal L Ω` into itself.

The proof combines the algebraic lift `algebraAut_quasiLocalSubalg_le` with
continuity of `algebraAut g`: the comap of `quasiLocal L Ω` under `algebraAut g`
contains `quasiLocalSubalg L Ω` and is closed, hence contains the topological
closure `quasiLocal L Ω`. -/
theorem algebraAut_quasiLocal_le (act : HasGroupAction L Ω G) (g : G) :
    ∀ T ∈ quasiLocal L Ω,
      act.algebraAut g T ∈ quasiLocal L Ω := by
  intro T hT
  suffices h : quasiLocal L Ω
      ≤ (quasiLocal L Ω).comap ((act.algebraAut g : _ →⋆ₐ[ℂ] _)) by
    exact h hT
  refine StarSubalgebra.topologicalClosure_minimal ?_ ?_
  · intro T' hT'
    change act.algebraAut g T' ∈ quasiLocal L Ω
    exact quasiLocalSubalg_le_quasiLocal L Ω
      (algebraAut_quasiLocalSubalg_le act g T' hT')
  · rw [StarSubalgebra.coe_comap]
    exact (isClosed_quasiLocal L Ω).preimage (continuous_algebraAut act g)

/-- The covariance endomorphism `algebraAut_quasiLocal_le` packaged as a
`*`-algebra homomorphism `quasiLocal L Ω →⋆ₐ[ℂ] quasiLocal L Ω`. -/
noncomputable def quasiLocalEnd (act : HasGroupAction L Ω G) (g : G) :
    quasiLocal L Ω →⋆ₐ[ℂ] quasiLocal L Ω where
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
    exact map_star (act.algebraAut g) (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)

@[simp]
theorem quasiLocalEnd_apply (act : HasGroupAction L Ω G) (g : G) (T : quasiLocal L Ω) :
    (act.quasiLocalEnd g T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) =
      act.algebraAut g (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :=
  rfl

/-! ### Genuine covariance as automorphisms of the quasi-local algebra -/

/-- Under a genuine action, each group element induces a `*`-algebra automorphism of the
bundled quasi-local algebra.  The inverse is the automorphism induced by `g⁻¹`. -/
noncomputable def quasiLocalAut (act : HasGroupAction L Ω G)
    (g : G) :
    quasiLocal L Ω ≃⋆ₐ[ℂ] quasiLocal L Ω where
  toFun T := ⟨act.algebraAut g T.1, algebraAut_quasiLocal_le act g T.1 T.2⟩
  invFun T := ⟨act.algebraAut g⁻¹ T.1, algebraAut_quasiLocal_le act g⁻¹ T.1 T.2⟩
  left_inv T := by
    apply Subtype.ext
    have h := congrArg
      (fun e : (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
          ≃⋆ₐ[ℂ] (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) =>
        e (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω))
      (act.algebraAut_mul g⁻¹ g)
    simpa [inv_mul_cancel, algebraAut_one] using h.symm
  right_inv T := by
    apply Subtype.ext
    have h := congrArg
      (fun e : (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
          ≃⋆ₐ[ℂ] (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) =>
        e (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω))
      (act.algebraAut_mul g g⁻¹)
    simpa [mul_inv_cancel, algebraAut_one] using h.symm
  map_mul' T U := by
    apply Subtype.ext
    exact map_mul (act.algebraAut g)
      (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
      (U : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
  map_add' T U := by
    apply Subtype.ext
    exact map_add (act.algebraAut g)
      (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
      (U : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
  map_star' T := by
    apply Subtype.ext
    exact map_star (act.algebraAut g)
      (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
  map_smul' c T := by
    apply Subtype.ext
    exact map_smul (act.algebraAut g) c
      (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)

@[simp]
theorem quasiLocalAut_apply (act : HasGroupAction L Ω G)
    (g : G) (T : quasiLocal L Ω) :
    (act.quasiLocalAut g T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) =
      act.algebraAut g (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :=
  rfl

/-- The quasi-local automorphism assigned to the identity acts trivially. -/
theorem quasiLocalAut_one_apply (act : HasGroupAction L Ω G)
    (T : quasiLocal L Ω) :
    act.quasiLocalAut 1 T = T := by
  apply Subtype.ext
  simp [quasiLocalAut_apply, algebraAut_one]

/-- The quasi-local automorphisms compose according to group multiplication. -/
theorem quasiLocalAut_mul_apply (act : HasGroupAction L Ω G)
    (g h : G) (T : quasiLocal L Ω) :
    act.quasiLocalAut (g * h) T = act.quasiLocalAut g (act.quasiLocalAut h T) := by
  apply Subtype.ext
  simp [quasiLocalAut_apply, algebraAut_mul]

end HasGroupAction

end LocalNetLike
