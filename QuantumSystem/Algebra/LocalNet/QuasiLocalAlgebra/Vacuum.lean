module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Covariance

/-!
# Vacuum vector and `G`-invariance Prop (Phase 5'd)

We define the canonical **vacuum vector** of the lattice system as the
basis vector `lp.single 2 (referenceTuple L) 1` in `globalHilbert L`,
where `referenceTuple L : globalIdx L` is the global tuple that takes the
value `referenceBasis L s` at every site.  This is the Naaijkens-Bratteli
"reference" / "vacuum" vector that the inductive limit is built around
(Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2 §2.7.2).

The combinatorial *invariance* condition for a `G`-action is that the
action fixes the reference tuple, i.e. `globalIdxAction g (referenceTuple L)
= referenceTuple L` — this is the natural strengthening of
`siteIdxEquiv_referenceBasis` from sites to global tuples.  The full
operator-algebra statement (`ω(α_g T) = ω(T)` for the vacuum state
associated with the vacuum vector) is the natural follow-up after the
unitary representation is in place.

## Main definitions / theorems

* `LocalNetLike.referenceTuple L` — the constant `referenceBasis`-tuple in
  `globalIdx L`.
* `LocalNetLike.vacuumState L` — the vacuum vector
  `lp.single 2 (referenceTuple L) 1` in `globalHilbert L`.
* `LocalNetLike.HasGroupAction.globalIdxAction_referenceTuple` — every
  `G`-action fixes `referenceTuple L`.
* `LocalNetLike.IsVacuumInvariant act` — Prop saying every `G`-translate
  of `vacuumState L` equals `vacuumState L`; automatic from
  `globalIdxAction_referenceTuple` once the unitary representation
  is in place.

## References

* Naaijkens 2012 §3.5.
* Bratteli–Robinson Vol. 2 §2.7.2.
* Verch 2025 (https://arxiv.org/abs/2507.00900) §1.2 axiom (iv).
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

@[simp]
theorem referenceTuple_val (s : L) :
    (referenceTuple L).val s = referenceBasis L s := rfl

/-- The **vacuum vector** of the lattice system: the basis vector of
`globalHilbert L` at `referenceTuple L`. -/
noncomputable def vacuumState : globalHilbert L :=
  lp.single 2 (referenceTuple L) (1 : ℂ)

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

/-- **`G`-invariance of the vacuum vector** (Verch 2025 §1.2 axiom (iv) /
Naaijkens 2012 §1.3): the unitary representation `unitaryAction g` fixes
the vacuum vector. -/
theorem HasGroupAction.unitaryAction_vacuumState
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    act.unitaryAction g (vacuumState L) = vacuumState L := by
  apply Subtype.ext
  funext a
  rw [HasGroupAction.unitaryAction_apply_val]
  -- (vacuumState L).val (g.symm a) = (vacuumState L).val a
  -- Both equal `if · = referenceTuple L then 1 else 0`; equivalence follows from
  -- `globalIdxAction g (referenceTuple L) = referenceTuple L`.
  change (vacuumState L : lp (fun _ : globalIdx L => ℂ) 2)
        ((act.globalIdxAction g).symm a)
      = (vacuumState L : lp (fun _ : globalIdx L => ℂ) 2) a
  unfold vacuumState
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

end LocalNetLike
