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

/-- **`G`-invariance of the vacuum state** (Verch 2025 §1.2 axiom (iv) /
Naaijkens 2012 §1.3): a placeholder Prop stating that every `G`-translate
of the vacuum vector equals the vacuum vector.  Once the unitary
representation `unitaryAction g : globalHilbert L ≃ₗᵢ globalHilbert L` is
constructed (in a follow-up phase), this Prop is automatic from
`globalIdxAction_referenceTuple` because the unitary acts as a basis
permutation.  Stated here as data so that downstream `*`-algebra
constructions (the GNS-style vacuum state on `quasiLocal L`) can quote it. -/
def IsVacuumInvariant {G : Type*} [Group G]
    (_act : HasGroupAction L G)
    (U : G → globalHilbert L → globalHilbert L) : Prop :=
  ∀ g : G, U g (vacuumState L) = vacuumState L

end LocalNetLike
