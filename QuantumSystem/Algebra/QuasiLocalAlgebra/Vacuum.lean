module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.Covariance

/-!
# Vacuum vector and `G`-invariance

We define the canonical **reference/vacuum vector** of the lattice system as the
basis vector `lp.single 2 (referenceTuple L) 1` in `globalHilbert L`,
where `referenceTuple L : globalIdx L` is the global tuple that takes the
value `referenceBasis L s` at every site.  This is the Naaijkens-Bratteli
"reference" / "vacuum" vector selecting the incomplete infinite tensor product
sector modelled by `globalHilbert L` (Naaijkens 2012 §3.5 /
Bratteli–Robinson Vol. 2 §2.7.2).

As in `GlobalHilbert.lean`, this is a basis-indexed reference-sector model, not
a separate bundled construction of the full infinite tensor product.

The combinatorial *invariance* condition for a `G`-action is that the
action fixes the reference tuple, i.e. `globalIdxAction g (referenceTuple L)
= referenceTuple L` — this is the natural strengthening of
`siteIdxEquiv_referenceBasis` from sites to global tuples.  The full
operator-algebra statement (`ω(α_g T) = ω(T)` for the vector functional
associated with the reference vector) is a separate state layer.  It should
not be confused with the relativistic positive-energy vacuum condition.

## Main definitions / theorems

* `LocalNetLike.referenceTuple L` — the constant `referenceBasis`-tuple in
  `globalIdx L`.
* `LocalNetLike.vacuumVector L` — the reference/vacuum basis vector
  `lp.single 2 (referenceTuple L) 1` in the reference sector `globalHilbert L`.
* `LocalNetLike.HasGroupAction.globalIdxAction_referenceTuple` — every
  `G`-action fixes `referenceTuple L`.
* `LocalNetLike.HasGroupAction.unitaryAction_vacuumVector` — every `G`-translate
  of `vacuumVector L` equals `vacuumVector L`.

## References

* Naaijkens 2012 §3.5.
* Bratteli–Robinson Vol. 2 §2.7.2.
* Verch 2025 (https://arxiv.org/abs/2507.00900) §1.2 for the distinction between
  invariant implementing vectors and relativistic vacuum states.
-/

@[expose] public section

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- The canonical "vacuum tuple" `referenceTuple L : globalIdx L`: at every
site `s : L`, take the chosen `referenceBasis L s`.  This is the unique
element of `globalIdx L` whose all coordinates agree with the reference. -/
noncomputable def referenceTuple : globalIdx L :=
  ⟨fun s => referenceBasis L s, ⟨∅, fun _ _ => rfl⟩⟩

/-- The **reference/vacuum vector** of the lattice system: the basis vector of
`globalHilbert L` at `referenceTuple L`. -/
noncomputable def vacuumVector : globalHilbert L :=
  lp.single 2 (referenceTuple L) (1 : ℂ)

/-- Paper notation `Ω(L)` for the reference/vacuum vector at the lattice
system `L`, scoped to `LocalNetLike`.  Open `scoped LocalNetLike` to use
it.  See Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2 §2.7.2 for the
rendering this notation matches; the `(L)` argument is a project-level
parameterisation of the paper's bare `Ω`. -/
scoped notation:max "Ω(" L ")" => LocalNetLike.vacuumVector L

namespace HasGroupAction

variable {L}
variable {G : Type*} [Group G]

/-- Every `G`-action fixes the reference tuple: this is the global
counterpart of the per-site condition `siteIdxEquiv_referenceBasis`. -/
theorem globalIdxAction_referenceTuple (act : HasGroupAction L G) (g : G) :
    globalIdxAction act g (referenceTuple L) = referenceTuple L := by
  apply Subtype.ext
  funext t
  -- (globalIdxAction g (referenceTuple L)).val t = referenceTuple L .val t
  -- = referenceBasis L t.
  -- The LHS unfolds to piAction g (constant-reference) t, and we apply
  -- piAction_finite_variation with Γ = ∅.
  change piAction act g (fun s => referenceBasis L s) t = referenceBasis L t
  -- Take Γ = ∅.  Every t ∉ ∅, and the hypothesis is `s ∉ ∅ → ref = ref` (vacuous).
  have := piAction_finite_variation (act := act) (g := g)
    (f := fun s => referenceBasis L s) (Γ := (∅ : Finset L))
    (fun s _ => rfl) t
  -- t ∉ ∅.image (siteAction g) = ∅ is automatic.
  apply this
  intro hin
  rcases Finset.mem_image.mp hin with ⟨_, ha, _⟩
  exact absurd ha (Finset.notMem_empty _)

end HasGroupAction

/-- **`G`-invariance of the reference/vacuum vector**: the unitary representation
`unitaryAction g` fixes `vacuumVector L`. -/
theorem HasGroupAction.unitaryAction_vacuumVector
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    act.unitaryAction g (vacuumVector L) = vacuumVector L := by
  apply Subtype.ext
  funext a
  rw [HasGroupAction.unitaryAction_apply_val]
  -- (vacuumVector L).val (g.symm a) = (vacuumVector L).val a
  -- Both equal `if · = referenceTuple L then 1 else 0`; equivalence follows from
  -- `globalIdxAction g (referenceTuple L) = referenceTuple L`.
  change (vacuumVector L : lp (fun _ : globalIdx L => ℂ) 2)
        ((act.globalIdxAction g).symm a)
      = (vacuumVector L : lp (fun _ : globalIdx L => ℂ) 2) a
  unfold vacuumVector
  rw [lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
  -- if (g.symm a = referenceTuple L) then 1 else 0
  -- = if (a = referenceTuple L) then 1 else 0
  have hsymm_ref : (act.globalIdxAction g).symm (referenceTuple L)
                    = referenceTuple L := by
    have h := act.globalIdxAction_referenceTuple g
    have hcong :
        (act.globalIdxAction g).symm ((act.globalIdxAction g) (referenceTuple L))
          = (act.globalIdxAction g).symm (referenceTuple L) :=
      congrArg _ h
    rw [Equiv.symm_apply_apply] at hcong
    exact hcong.symm
  have hiff : ((act.globalIdxAction g).symm a = referenceTuple L)
                ↔ (a = referenceTuple L) := by
    constructor
    · intro h
      have := congrArg (act.globalIdxAction g) h
      rw [Equiv.apply_symm_apply, act.globalIdxAction_referenceTuple] at this
      exact this
    · rintro rfl
      exact hsymm_ref
  by_cases hcase : a = referenceTuple L
  · rw [if_pos (hiff.mpr hcase), if_pos hcase]
  · rw [if_neg (fun h => hcase (hiff.mp h)), if_neg hcase]

/-! ### Bundled reference-vector functional and `G`-invariance -/

/-- The **reference-vector functional** on the represented operator algebra
`B(globalHilbert L)`, bundled as a continuous linear map.  At a bounded
operator `T` it returns `⟪Ω, T Ω⟫`, where `Ω = vacuumVector L`. -/
noncomputable def vacuumFunctional :
    (globalHilbert L →L[ℂ] globalHilbert L) →L[ℂ] ℂ :=
  (innerSL ℂ (vacuumVector L)).comp
    (ContinuousLinearMap.apply ℂ (globalHilbert L) (vacuumVector L))

@[simp]
theorem vacuumFunctional_apply
    (T : globalHilbert L →L[ℂ] globalHilbert L) :
    vacuumFunctional L T = inner ℂ (vacuumVector L) (T (vacuumVector L)) := rfl

/-- The inverse unitary also fixes the vacuum vector. -/
theorem HasGroupAction.unitaryAction_symm_vacuumVector
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    (act.unitaryAction g).symm (vacuumVector L) = vacuumVector L := by
  have h := HasGroupAction.unitaryAction_vacuumVector L act g
  have := congrArg (act.unitaryAction g).symm h
  rw [LinearIsometryEquiv.symm_apply_apply] at this
  exact this.symm

/-- **`G`-invariance of the vacuum functional at the `B(H)` level**:
`ω(α_g T) = ω(T)` for every bounded operator `T` and every group element `g`. -/
theorem HasGroupAction.vacuumFunctional_algebraAut
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (T : globalHilbert L →L[ℂ] globalHilbert L) :
    vacuumFunctional L (act.algebraAut g T) = vacuumFunctional L T := by
  rw [vacuumFunctional_apply, vacuumFunctional_apply, act.algebraAut_apply]
  -- LHS: ⟪Ω, U (T (U.symm Ω))⟫.
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [HasGroupAction.unitaryAction_symm_vacuumVector L act g]
  -- Goal: ⟪Ω, U (T Ω)⟫ = ⟪Ω, T Ω⟫.  Use `inner_map_map` on the RHS.
  calc inner ℂ (vacuumVector L)
            ((act.unitaryAction g) (T (vacuumVector L)))
      = inner ℂ ((act.unitaryAction g) (vacuumVector L))
              ((act.unitaryAction g) (T (vacuumVector L))) := by
            rw [HasGroupAction.unitaryAction_vacuumVector L act g]
    _ = inner ℂ (vacuumVector L) (T (vacuumVector L)) :=
            (act.unitaryAction g).inner_map_map _ _

/-! ### Reference-vector functional on the bundled quasi-local algebra -/

/-- The **reference-vector functional** on the quasi-local algebra `quasiLocal L`,
bundled as a continuous linear functional `↥(quasiLocal L) →L[ℂ] ℂ`.

This declaration is not yet a bundled positive, normalised C\*-state; positivity
and normalisation should be added before using it as a formal `state` object. -/
noncomputable def vacuumFunctionalOnQuasiLocal :
    ↥(quasiLocal L) →L[ℂ] ℂ :=
  (vacuumFunctional L).comp (quasiLocal L).toSubalgebra.toSubmodule.subtypeL

/-- Paper notation `ω(L)` for the reference-vector functional on the quasi-local
algebra `quasiLocal L`, scoped to `LocalNetLike`.  Open `scoped LocalNetLike` to
use it.  See Naaijkens 2012 §3.5 for the C⋆-state convention; the `(L)`
argument is a project-level parameterisation of the paper's bare `ω`. -/
scoped notation:max "ω(" L ")" => LocalNetLike.vacuumFunctionalOnQuasiLocal L

/-- **`G`-invariance of the reference-vector functional** on the quasi-local algebra:
`ω(α_g T) = ω(T)` for every `T ∈ quasiLocal L` and every group element `g`. -/
theorem HasGroupAction.vacuumFunctionalOnQuasiLocal_quasiLocalEnd
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (T : ↥(quasiLocal L)) :
    vacuumFunctionalOnQuasiLocal L (act.quasiLocalEnd g T)
      = vacuumFunctionalOnQuasiLocal L T := by
  change vacuumFunctional L
      (act.algebraAut g (T : globalHilbert L →L[ℂ] globalHilbert L))
      = vacuumFunctional L (T : globalHilbert L →L[ℂ] globalHilbert L)
  exact HasGroupAction.vacuumFunctional_algebraAut L act g
    (T : globalHilbert L →L[ℂ] globalHilbert L)

end LocalNetLike
