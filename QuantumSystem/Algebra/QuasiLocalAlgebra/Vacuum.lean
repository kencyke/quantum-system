module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.Covariance

/-!
# Vacuum vector and `G`-invariance

The **vacuum vector** of the lattice system is the basis vector
`lp.single 2 (referenceTuple L Ω) 1` in `globalHilbert L Ω`, where
`referenceTuple L Ω : globalIdx L Ω` is the constant `Ω`-tuple
(Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2 §2.7.2).

A `G`-action fixes this vector when the per-site compatibility
`siteIdxEquiv_sectorVec` lifts to `globalIdxAction g (referenceTuple L Ω) =
referenceTuple L Ω`.  This is the basis-indexed invariance, not the
relativistic positive-energy vacuum condition.

## Main definitions / theorems

* `LocalNetLike.referenceTuple L Ω` — the constant `Ω`-tuple in `globalIdx L Ω`.
* `LocalNetLike.vacuumVector L Ω` — the vacuum basis vector in `globalHilbert L Ω`.
* `LocalNetLike.HasGroupAction.globalIdxAction_referenceTuple` — every
  `G`-action fixes `referenceTuple L Ω`.
* `LocalNetLike.HasGroupAction.unitaryAction_vacuumVector` — every `G`-translate
  of `vacuumVector L Ω` equals `vacuumVector L Ω`.

## References

* Naaijkens 2012 §3.5.
* Bratteli–Robinson Vol. 2 §2.7.2.
* Verch 2025 (https://arxiv.org/abs/2507.00900) §1.2.
-/

@[expose] public section

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
variable (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)

/-- The constant `Ω`-tuple `referenceTuple L Ω : globalIdx L Ω`. -/
noncomputable def referenceTuple : globalIdx L Ω :=
  ⟨fun s => Ω s, ⟨∅, fun _ _ => rfl⟩⟩

/-- The **reference/vacuum vector** of the lattice system: the basis vector of
`globalHilbert L Ω` at `referenceTuple L Ω`. -/
noncomputable def vacuumVector : globalHilbert L Ω :=
  lp.single 2 (referenceTuple L Ω) (1 : ℂ)

namespace HasGroupAction

variable {L} {Ω}
variable {G : Type*} [Group G]

/-- Every `G`-action fixes the reference tuple: the global counterpart of
the per-site condition `siteIdxEquiv_sectorVec`. -/
theorem globalIdxAction_referenceTuple (act : HasGroupAction L Ω G) (g : G) :
    globalIdxAction act g (referenceTuple L Ω) = referenceTuple L Ω := by
  apply Subtype.ext
  funext t
  change piAction act g (fun s => Ω s) t = Ω t
  have := piAction_finite_variation (act := act) (g := g)
    (f := fun s => Ω s) (Γ := (∅ : Finset L))
    (fun s _ => rfl) t
  apply this
  intro hin
  rcases Finset.mem_image.mp hin with ⟨_, ha, _⟩
  exact absurd ha (Finset.notMem_empty _)

end HasGroupAction

/-- **`G`-invariance of the vacuum vector**: the unitary representation
`unitaryAction g` fixes `vacuumVector L Ω`. -/
theorem HasGroupAction.unitaryAction_vacuumVector
    {G : Type*} [Group G] (act : HasGroupAction L Ω G) (g : G) :
    act.unitaryAction g (vacuumVector L Ω) = vacuumVector L Ω := by
  apply Subtype.ext
  funext a
  rw [HasGroupAction.unitaryAction_apply_val]
  change (vacuumVector L Ω : lp (fun _ : globalIdx L Ω => ℂ) 2)
        ((act.globalIdxAction g).symm a)
      = (vacuumVector L Ω : lp (fun _ : globalIdx L Ω => ℂ) 2) a
  unfold vacuumVector
  rw [lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
  have hsymm_ref : (act.globalIdxAction g).symm (referenceTuple L Ω)
                    = referenceTuple L Ω := by
    have h := act.globalIdxAction_referenceTuple g
    have hcong :
        (act.globalIdxAction g).symm ((act.globalIdxAction g) (referenceTuple L Ω))
          = (act.globalIdxAction g).symm (referenceTuple L Ω) :=
      congrArg _ h
    rw [Equiv.symm_apply_apply] at hcong
    exact hcong.symm
  have hiff : ((act.globalIdxAction g).symm a = referenceTuple L Ω)
                ↔ (a = referenceTuple L Ω) := by
    constructor
    · intro h
      have := congrArg (act.globalIdxAction g) h
      rw [Equiv.apply_symm_apply, act.globalIdxAction_referenceTuple] at this
      exact this
    · rintro rfl
      exact hsymm_ref
  by_cases hcase : a = referenceTuple L Ω
  · rw [if_pos (hiff.mpr hcase), if_pos hcase]
  · rw [if_neg (fun h => hcase (hiff.mp h)), if_neg hcase]

/-! ### Bundled vacuum functional and `G`-invariance -/

/-- The **vacuum functional** `T ↦ ⟪Ω, T Ω⟫` on `B(globalHilbert L Ω)`, where
`Ω = vacuumVector L Ω`. -/
noncomputable def vacuumFunctional :
    (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) →L[ℂ] ℂ :=
  (innerSL ℂ (vacuumVector L Ω)).comp
    (ContinuousLinearMap.apply ℂ (globalHilbert L Ω) (vacuumVector L Ω))

@[simp]
theorem vacuumFunctional_apply
    (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :
    vacuumFunctional L Ω T = inner ℂ (vacuumVector L Ω) (T (vacuumVector L Ω)) := rfl

/-- The inverse unitary also fixes the vacuum vector. -/
theorem HasGroupAction.unitaryAction_symm_vacuumVector
    {G : Type*} [Group G] (act : HasGroupAction L Ω G) (g : G) :
    (act.unitaryAction g).symm (vacuumVector L Ω) = vacuumVector L Ω := by
  have h := HasGroupAction.unitaryAction_vacuumVector L Ω act g
  have := congrArg (act.unitaryAction g).symm h
  rw [LinearIsometryEquiv.symm_apply_apply] at this
  exact this.symm

/-- **`G`-invariance of the vacuum functional at the `B(H)` level**:
`ω(α_g T) = ω(T)`. -/
theorem HasGroupAction.vacuumFunctional_algebraAut
    {G : Type*} [Group G] (act : HasGroupAction L Ω G) (g : G)
    (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :
    vacuumFunctional L Ω (act.algebraAut g T) = vacuumFunctional L Ω T := by
  rw [vacuumFunctional_apply, vacuumFunctional_apply, act.algebraAut_apply]
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [HasGroupAction.unitaryAction_symm_vacuumVector L Ω act g]
  calc inner ℂ (vacuumVector L Ω)
            ((act.unitaryAction g) (T (vacuumVector L Ω)))
      = inner ℂ ((act.unitaryAction g) (vacuumVector L Ω))
              ((act.unitaryAction g) (T (vacuumVector L Ω))) := by
            rw [HasGroupAction.unitaryAction_vacuumVector L Ω act g]
    _ = inner ℂ (vacuumVector L Ω) (T (vacuumVector L Ω)) :=
            (act.unitaryAction g).inner_map_map _ _

/-! ### Vacuum functional on the bundled quasi-local algebra -/

/-- The vacuum functional on `quasiLocal L Ω`, bundled as
`↥(quasiLocal L Ω) →L[ℂ] ℂ`.

Not yet a bundled positive, normalised C\*-state; positivity and normalisation
should be added before using it as a formal `state` object. -/
noncomputable def vacuumFunctionalOnQuasiLocal :
    ↥(quasiLocal L Ω) →L[ℂ] ℂ :=
  (vacuumFunctional L Ω).comp (quasiLocal L Ω).toSubalgebra.toSubmodule.subtypeL

/-- **`G`-invariance of the vacuum functional** on the quasi-local algebra:
`ω(α_g T) = ω(T)`. -/
theorem HasGroupAction.vacuumFunctionalOnQuasiLocal_quasiLocalEnd
    {G : Type*} [Group G] (act : HasGroupAction L Ω G) (g : G)
    (T : ↥(quasiLocal L Ω)) :
    vacuumFunctionalOnQuasiLocal L Ω (act.quasiLocalEnd g T)
      = vacuumFunctionalOnQuasiLocal L Ω T := by
  change vacuumFunctional L Ω
      (act.algebraAut g (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω))
      = vacuumFunctional L Ω (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
  exact HasGroupAction.vacuumFunctional_algebraAut L Ω act g
    (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)

end LocalNetLike
