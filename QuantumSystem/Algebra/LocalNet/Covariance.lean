module

public import QuantumSystem.Algebra.LocalNet.GroupAction

/-!
# Covariance theorem for `LocalNet`

Proves the **covariance axiom (Haag–Kastler axiom (iii))** for any `LocalNet`
equipped with a `HasGroupAction` data: the `*`-automorphism family `α_g`
intertwines the isotony embedding. Realises Verch 2025 §1.2 axiom (iii) /
Naaijkens 2012 §1.3 line 215 in the finite-lattice slice.

The proof is entry-wise: both sides expand via `includeAlgebra_apply` and
`algebraAut_apply` to conditional matrix entries on the `combineIdx`
decomposition, and the `HasGroupAction` data gives a structural
compatibility (`combineIdx_action_fst_eq` and `combineIdx_action_snd_iff`)
between the `combineIdx` decompositions on the source and target regions.

## Main results

* `LocalNet.algebraAut_apply` — entry-wise unfolding of `algebraAut`.
* `LocalNet.isCovariant` — the constructive proof of the covariance axiom.

## References

* Verch 2025 (`https://arxiv.org/abs/2507.00900`) §1.2 axiom (iii)
* Naaijkens 2012 (`https://repository.ubn.ru.nl/handle/2066/92737`) §1.3
-/

@[expose] public section

namespace LocalNet

variable {L : LocalNet}

/-! ### Pointwise unfolding of `algebraAut` -/

/-- Entry-wise behaviour of `algebraAut`: the `(i, j)`-entry of `α_g M` is the
    `((e.symm i), (e.symm j))`-entry of `M`, where
    `e = regionIdxEquivOfAction g Λ`. -/
@[simp] lemma algebraAut_apply
    {G : Type*} [Group G]
    (act : L.HasGroupAction G) (g : G) {Λ : Finset L.sites}
    (M : L.localAlgebra Λ) (i j : L.regionIdx (act.regionImage g Λ)) :
    L.algebraAut act g Λ M i j =
      M ((act.regionIdxEquivOfAction g Λ).symm i)
        ((act.regionIdxEquivOfAction g Λ).symm j) := rfl

namespace HasGroupAction

variable {G : Type*} [Group G]

/-- Pointwise evaluation of `(regionIdxEquivOfAction g Λ).symm`: factor as
    `(siteIdxEquiv g a.val).symm` applied to a value transported via
    `siteSubtypeEquiv`. -/
@[simp] lemma regionIdxEquivOfAction_symm_apply
    (act : L.HasGroupAction G) (g : G) {Λ : Finset L.sites}
    (f : L.regionIdx (act.regionImage g Λ)) (a : ↥Λ) :
    (act.regionIdxEquivOfAction g Λ).symm f a =
      (act.siteIdxEquiv g a.val).symm (f (act.siteSubtypeEquiv g Λ a)) := rfl

end HasGroupAction

/-! ### Compatibility lemmas for the action and `combineIdx` -/

variable {G : Type*} [Group G]

/-- The `Λ`-component of the `combineIdx h` decomposition of
    `(regionIdxEquivOfAction g Λ_total).symm i` agrees with applying
    `(regionIdxEquivOfAction g Λ).symm` to the `regionImage g Λ`-component
    of the `combineIdx (image_subset_image h)` decomposition of `i`. Holds by
    pointwise computation (definitional proof irrelevance for the membership
    proofs in the `siteSubtypeEquiv`). -/
private lemma combineIdx_action_fst_eq
    (act : L.HasGroupAction G) (g : G)
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (i : L.regionIdx (act.regionImage g Λ_total)) :
    ((L.combineIdx h).symm
        ((act.regionIdxEquivOfAction g Λ_total).symm i)).1 =
      (act.regionIdxEquivOfAction g Λ).symm
        ((L.combineIdx (Finset.image_subset_image h)).symm i).1 := rfl

/-- Helper: under `siteAction g`, every site `a ∈ Λ_total \ Λ` lands in
    `regionImage g Λ_total \ regionImage g Λ` (uses injectivity of
    `siteAction g`). -/
private lemma siteAction_mem_image_sdiff
    (act : L.HasGroupAction G) (g : G)
    {Λ Λ_total : Finset L.sites} (a : ↥(Λ_total \ Λ)) :
    act.siteAction g a.val ∈
      act.regionImage g Λ_total \ act.regionImage g Λ := by
  rw [Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨a.val,
      (Finset.mem_sdiff.mp a.property).1, rfl⟩
  · intro hin
    obtain ⟨v, hv, hgv⟩ := Finset.mem_image.mp hin
    have hva : v = a.val := (act.siteAction g).injective hgv
    exact (Finset.mem_sdiff.mp a.property).2 (hva ▸ hv)


/-- The `Λ_total \ Λ`-component equality test of the `combineIdx h`
    decomposition of `(regionIdxEquivOfAction g Λ_total).symm i` (and `j`)
    is equivalent to the corresponding test on the
    `regionImage g Λ_total \ regionImage g Λ`-component of the
    `combineIdx (image_subset_image h)` decomposition of `i` (and `j`).

    Proof: both equalities of dependent functions reduce to "for every
    `a ∈ Λ_total \ Λ` (resp. `b ∈ regionImage g Λ_total \ regionImage g Λ`),
    the values of `i` and `j` at `siteAction g a.val` (resp. `b.val`) coincide".
    The two universals match because `siteAction g` is a bijection
    `Λ_total \ Λ ↔ regionImage g Λ_total \ regionImage g Λ`. -/
private lemma combineIdx_action_snd_iff
    (act : L.HasGroupAction G) (g : G)
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (i j : L.regionIdx (act.regionImage g Λ_total)) :
    ((L.combineIdx h).symm
          ((act.regionIdxEquivOfAction g Λ_total).symm i)).2
        = ((L.combineIdx h).symm
            ((act.regionIdxEquivOfAction g Λ_total).symm j)).2
      ↔ ((L.combineIdx (Finset.image_subset_image h)).symm i).2
        = ((L.combineIdx (Finset.image_subset_image h)).symm j).2 := by
  rw [funext_iff, funext_iff]
  refine ⟨fun hL b => ?_, fun hR a => ?_⟩
  · -- (∀ a, γ-LHS i a = γ-LHS j a) → (∀ b, γ-RHS i b = γ-RHS j b)
    -- Pick the preimage of `b.val` under `siteAction g`.
    obtain ⟨v, hv_total, hv_eq⟩ :=
      Finset.mem_image.mp (Finset.mem_sdiff.mp b.property).1
    have hv_not_in : v ∉ Λ := fun hv_in =>
      (Finset.mem_sdiff.mp b.property).2
        (Finset.mem_image.mpr ⟨v, hv_in, hv_eq⟩)
    have hv_sdiff : v ∈ Λ_total \ Λ :=
      Finset.mem_sdiff.mpr ⟨hv_total, hv_not_in⟩
    have key := hL ⟨v, hv_sdiff⟩
    -- Reduce `key` to per-site comparison at `siteAction g v`.
    simp only [combineIdx_symm_apply_snd,
               HasGroupAction.regionIdxEquivOfAction_symm_apply] at key
    have key' : i (act.siteSubtypeEquiv g Λ_total ⟨v, hv_total⟩)
              = j (act.siteSubtypeEquiv g Λ_total ⟨v, hv_total⟩) :=
      (act.siteIdxEquiv g v).symm.injective key
    -- Bridge the index `b` with `siteSubtypeEquiv ⟨v, hv_total⟩` via `Subtype.ext`,
    -- then `rw` (motive depends only on the Subtype element, not on `b.val`).
    have hbv : b.val ∈ act.regionImage g Λ_total :=
      (Finset.mem_sdiff.mp b.property).1
    have hsub : (⟨b.val, hbv⟩ : ↥(act.regionImage g Λ_total))
              = act.siteSubtypeEquiv g Λ_total ⟨v, hv_total⟩ :=
      Subtype.ext hv_eq.symm
    change i ⟨b.val, hbv⟩ = j ⟨b.val, hbv⟩
    rw [hsub]
    exact key'
  · -- (∀ b, γ-RHS i b = γ-RHS j b) → (∀ a, γ-LHS i a = γ-LHS j a)
    -- Apply `hR` at the `siteAction g`-image of `a`.
    have hmem := siteAction_mem_image_sdiff act g a
    have key := hR ⟨act.siteAction g a.val, hmem⟩
    -- The goal reduces to `(siteIdxEquiv g a.val).symm (_ ⟨siteAction g a.val, _⟩)`
    -- = same with j; `key` gives the inner equality up to proof irrelevance.
    change (act.siteIdxEquiv g a.val).symm
            (i ⟨act.siteAction g a.val, _⟩)
        = (act.siteIdxEquiv g a.val).symm
            (j ⟨act.siteAction g a.val, _⟩)
    exact congrArg _ key

/-! ### Main covariance theorem -/

/-- **Covariance holds for any `LocalNet` with `HasGroupAction` data.** This is
    the finite-dimensional realisation of the Haag–Kastler covariance axiom:
    the algebra automorphism `α_g` intertwines the isotony embedding
    `𝔄(Λ) ↪ 𝔄(Λ_total)` along the `g`-translate
    `𝔄(g · Λ) ↪ 𝔄(g · Λ_total)`. -/
theorem isCovariant (L : LocalNet) {G : Type*} [Group G]
    (act : L.HasGroupAction G) : L.IsCovariant act := by
  intro g Λ Λ_total h X
  ext i j
  rw [algebraAut_apply, includeAlgebra_apply, includeAlgebra_apply,
      algebraAut_apply]
  -- LHS: if (γ-LHS i = γ-LHS j) then X (α-LHS i) (α-LHS j) else 0
  -- RHS: if (γ-RHS i = γ-RHS j) then X (e_Λ.symm (α-RHS i)) (e_Λ.symm (α-RHS j)) else 0
  -- Bridge conditions via combineIdx_action_snd_iff;
  -- bridge values via combineIdx_action_fst_eq.
  by_cases hcond : ((L.combineIdx (Finset.image_subset_image h)).symm i).2
                    = ((L.combineIdx (Finset.image_subset_image h)).symm j).2
  · rw [if_pos hcond,
        if_pos ((combineIdx_action_snd_iff act g h i j).mpr hcond),
        combineIdx_action_fst_eq act g h i,
        combineIdx_action_fst_eq act g h j]
  · have hLcond_neg :
        ((L.combineIdx h).symm
            ((act.regionIdxEquivOfAction g Λ_total).symm i)).2
          ≠ ((L.combineIdx h).symm
              ((act.regionIdxEquivOfAction g Λ_total).symm j)).2 :=
      fun heq => hcond ((combineIdx_action_snd_iff act g h i j).mp heq)
    rw [if_neg hcond, if_neg hLcond_neg]

end LocalNet
