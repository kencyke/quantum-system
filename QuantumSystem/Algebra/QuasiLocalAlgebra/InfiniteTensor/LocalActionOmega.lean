module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Module.Completion
public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionSplit
public import QuantumSystem.Algebra.QuasiLocalAlgebra.InfiniteTensor.RegionDirectedOmega

/-!
# Operator-algebra action on Ω-extended sectors

For an arbitrary unit-vector family `Ω : (s : L) → siteHilbert s` and a
finite-region operator `M : ℋ(Λ₀) →L[ℂ] ℋ(Λ₀)` we construct the continuous
linear operator

  `localEmbedΩ Λ₀ Ω hΩ M : globalHilbertOmega L Ω hΩ →L[ℂ] globalHilbertOmega L Ω hΩ`

obtained by lifting the basis-relabelled action `tensorWithId h M`
(`RegionSplit.lean`) through the directed-system colimit
`tensorPreHilbertΩ` (`RegionDirectedOmega.lean`) and then to its Cauchy
completion `globalHilbertOmega`.

This generalises `localEmbedΩRef` (`LocalAction.lean`), which transported
the `globalHilbert L`-side embedding `localEmbed` along the canonical
reference-basis equivalence `globalHilbertOmegaReferenceBasisEquiv`.  The
construction here is intrinsic to the colimit and works for any `Ω`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace
open Module

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

/-! ### Pointwise formula for `tensorWithId`

Direct coordinate expansion of `(tensorWithId h M v).ofLp g`, used to
establish the coherence between `tensorWithId` and `regionEmbedLeΩ`. -/

/-- Pointwise expansion of `tensorWithId h M v` at coordinate `g : regionIdx Λ'`. -/
theorem tensorWithId_ofLp_apply {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (v : regionHilbert (L := L) Λ') (g : regionIdx (L := L) Λ') :
    (tensorWithId h M v).ofLp g
      = (M (regionSplitSlice (Λ' := Λ')
              (regionHilbertSplitEquiv h v) (regionIdxSplit h g).2)).ofLp
          (regionIdxSplit h g).1 := by
  rw [tensorWithId_apply]
  change ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regionIdxEquiv h)).symm
      (tensorWithIdSplit (Λ' := Λ') M (regionHilbertSplitEquiv h v))).ofLp g = _
  rw [LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  -- Goal: (Equiv.piCongrLeft' (fun _ => ℂ) (regionIdxEquiv h).symm
  --        (tensorWithIdSplit M (regionHilbertSplitEquiv h v))).ofLp g
  --    = (M (regionSplitSlice ... )).ofLp (regionIdxSplit h g).1
  change (tensorWithIdSplit (Λ' := Λ') M (regionHilbertSplitEquiv h v)).ofLp
      (regionIdxSplit h g) = _
  rw [tensorWithIdSplit_apply]

/-! ### Coherence between `regionEmbedLeΩ` and `tensorWithId`

The key naturality identity: extending the source of a `tensorWithId` action
along the directed-system embedding `regionEmbedLeΩ` agrees with extending the
target.  We prove this on the basis vector `EuclideanSpace.single f 1`, which
suffices for the colimit lift in `LocalAction.lean`-style constructions. -/

/-- The `regionHilbertSplitEquiv` image of a basis vector is again a basis
vector, indexed by the `regionIdxEquiv` image. -/
private theorem regionHilbertSplitEquiv_single
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') (f : regionIdx (L := L) Λ') :
    regionHilbertSplitEquiv h (EuclideanSpace.single f (1 : ℂ))
      = EuclideanSpace.single (regionIdxSplit h f) (1 : ℂ) := by
  unfold regionHilbertSplitEquiv
  rw [EuclideanSpace.piLpCongrLeft_single]
  rfl

/-- Slice of a basis vector at coordinate `b`: it equals `single a₀ 1` if
`b = b₀` and zero otherwise, where `(a₀, b₀)` is the basis index. -/
private theorem regionSplitSlice_single
    {Λ Λ' : Finset L} (a₀ : regionIdx (L := L) Λ)
    (b₀ b : regionIdx (L := L) (Λ' \ Λ)) :
    regionSplitSlice (Λ' := Λ')
        (EuclideanSpace.single (a₀, b₀) (1 : ℂ)) b
      = if b = b₀ then EuclideanSpace.single a₀ (1 : ℂ) else 0 := by
  ext a
  rw [regionSplitSlice_apply]
  rw [show EuclideanSpace.single (a₀, b₀) (1 : ℂ) = PiLp.single 2 (a₀, b₀) (1 : ℂ) from rfl]
  rw [PiLp.single_apply]
  by_cases hb : b = b₀
  · rw [if_pos hb, show (EuclideanSpace.single a₀ (1 : ℂ) : EuclideanSpace ℂ (regionIdx Λ))
          = PiLp.single 2 a₀ (1 : ℂ) from rfl, PiLp.ofLp_single, Pi.single_apply]
    by_cases ha : a = a₀
    · rw [if_pos ha]
      rw [if_pos (Prod.mk.injEq .. |>.mpr ⟨ha, hb⟩)]
    · rw [if_neg ha]
      rw [if_neg (fun hp : (a, b) = (a₀, b₀) => ha (Prod.mk.injEq .. |>.mp hp).1)]
  · rw [if_neg hb]
    rw [if_neg (fun hp : (a, b) = (a₀, b₀) => hb (Prod.mk.injEq .. |>.mp hp).2)]
    rfl

/-- Auxiliary "outside" factor in the coordinate-wise expansion of the
coherence identity: the product of the `A \ Λ₀`-indicators and the
`A' \ A`-Ω-factors evaluated at `g`. -/
private noncomputable def coherenceFactor
    (Ω : (s : L) → siteHilbert s) (Λ₀ : Finset L) {A A' : Finset L}
    (f : regionIdx (L := L) A) (g : regionIdx (L := L) A') : ℂ :=
  (∏ s : A',
      if hs : s.1 ∈ A then
        (if s.1 ∈ Λ₀ then (1 : ℂ)
         else if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
      else (Ω s.1) (g s))

/-- Coherence between `regionEmbedLeΩ` and `tensorWithId` on basis vectors.

For `Λ₀ ⊆ A ⊆ A'` and `M : ℋ(Λ₀) →L[ℂ] ℋ(Λ₀)`, applying `tensorWithId` over
`A` to a basis vector `single f 1` and then extending along `A ⊆ A'` via
`regionEmbedLeΩ` agrees with first extending the basis vector to
`mkRegionVectorΩ` over `A'` and then applying `tensorWithId` over `A'`. -/
theorem regionEmbedLeΩ_tensorWithId_apply_basis
    {Λ₀ A A' : Finset L} (h₀ : Λ₀ ⊆ A) (h : A ⊆ A')
    (Ω : (s : L) → siteHilbert s) (hΩ : ∀ s, ‖Ω s‖ = 1)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (f : regionIdx (L := L) A) :
    regionEmbedLeΩ Ω hΩ h (tensorWithId h₀ M (EuclideanSpace.single f (1 : ℂ)))
      = tensorWithId (h₀.trans h) M (mkRegionVectorΩ (L := L) Ω h f) := by
  -- Key abbreviations.
  set p := regionIdxSplit h₀ f with hp_def
  ext g
  -- We derive both sides into the form
  --   coherenceFactor Ω Λ₀ f g * (M (single p.1 1)).ofLp (regionIdxSplit (h₀.trans h) g).1.
  -- Step 1 (RHS form).
  have hRHS :
      ((tensorWithId (h₀.trans h) M) (mkRegionVectorΩ Ω h f)).ofLp g
        = coherenceFactor Ω Λ₀ f g
          * (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp
              (regionIdxSplit (h₀.trans h) g).1 := by
    rw [tensorWithId_ofLp_apply]
    -- Show: slice = γ • single p.1 1.
    have hslice :
        regionSplitSlice (Λ' := A')
          (regionHilbertSplitEquiv (h₀.trans h) (mkRegionVectorΩ Ω h f))
          (regionIdxSplit (h₀.trans h) g).2
          = coherenceFactor Ω Λ₀ f g • EuclideanSpace.single p.1 (1 : ℂ) := by
      ext a
      rw [regionSplitSlice_apply]
      -- LHS_slice (a) = (regionHilbertSplitEquiv ...) (a, β).
      -- = (mkRegionVectorΩ Ω h f).ofLp (regionIdxCombine (h₀.trans h) a β).
      change (regionHilbertSplitEquiv (h₀.trans h) (mkRegionVectorΩ Ω h f)).ofLp
          (a, (regionIdxSplit (h₀.trans h) g).2) = _
      rw [show regionHilbertSplitEquiv (h₀.trans h) (mkRegionVectorΩ Ω h f)
            = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
                (regionIdxEquiv (h₀.trans h)) (mkRegionVectorΩ Ω h f) from rfl]
      rw [LinearIsometryEquiv.piLpCongrLeft_apply]
      change (mkRegionVectorΩ Ω h f).ofLp
          (regionIdxCombine (h₀.trans h) a
            (regionIdxSplit (h₀.trans h) g).2) = _
      rw [mkRegionVectorΩ_ofLp_apply]
      -- Set up notation; let `β := (regionIdxSplit (h₀.trans h) g).2`.
      set β := (regionIdxSplit (h₀.trans h) g).2 with hβ_def
      -- Note: β is defined so that for s : A' \ Λ₀, β ⟨s.1, ...⟩ = g ⟨s.1, _⟩.
      -- The combine identifies with: a if s.1 ∈ Λ₀; β ⟨s.1, mem_sdiff⟩ otherwise.
      -- The product's factor at s : A' depends on whether s.1 ∈ A and s.1 ∈ Λ₀.
      -- Show it equals coherenceFactor times [a = p.1].
      rw [show (coherenceFactor Ω Λ₀ f g • EuclideanSpace.single p.1 (1 : ℂ)).ofLp a
            = coherenceFactor Ω Λ₀ f g
                * (EuclideanSpace.single p.1 (1 : ℂ)).ofLp a from by
          rw [WithLp.ofLp_smul]
          rfl]
      rw [show (EuclideanSpace.single p.1 (1 : ℂ) : EuclideanSpace ℂ (regionIdx Λ₀)).ofLp a
            = if a = p.1 then (1 : ℂ) else 0 from by
          rw [show (EuclideanSpace.single p.1 (1 : ℂ) : EuclideanSpace ℂ (regionIdx Λ₀))
                = PiLp.single 2 p.1 (1 : ℂ) from rfl]
          rw [PiLp.ofLp_single, Pi.single_apply]]
      -- Now reformulate the LHS product to match `coherenceFactor * [a = p.1]`.
      -- Key: every factor at s : A' equals
      --   * if s.1 ∈ Λ₀: indicator [a ⟨s.1, _⟩ = p.1 ⟨s.1, _⟩]
      --   * if s.1 ∈ A \ Λ₀: indicator [g s = f ⟨s.1, hs⟩] (which is the coherence factor)
      --   * if s.1 ∉ A: (Ω s.1) (g s) (also the coherence factor)
      have hcomb_in : ∀ s : A', ∀ hs : s.1 ∈ Λ₀,
          regionIdxCombine (h₀.trans h) a β s = a ⟨s.1, hs⟩ := by
        intro s hs
        exact regionIdxCombine_of_mem (h₀.trans h) a β hs
      have hcomb_out : ∀ s : A', ∀ hs : s.1 ∉ Λ₀,
          regionIdxCombine (h₀.trans h) a β s
            = β ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, hs⟩⟩ := by
        intro s hs
        exact regionIdxCombine_of_not_mem (h₀.trans h) a β hs
      -- β ⟨s.1, ...⟩ = g ⟨s.1, ...⟩ for the right ambient region.
      have hβ_eq : ∀ s : A', ∀ hsΛ₀ : s.1 ∉ Λ₀,
          β ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, hsΛ₀⟩⟩
            = g ⟨s.1, s.2⟩ := by
        intro s hsΛ₀
        rfl
      -- f ⟨s.1, hsA⟩ for s.1 ∈ Λ₀: equals p.1 ⟨s.1, hsΛ₀⟩.
      have hf_in : ∀ s : A', ∀ hsA : s.1 ∈ A, ∀ hsΛ₀ : s.1 ∈ Λ₀,
          f ⟨s.1, hsA⟩ = p.1 ⟨s.1, hsΛ₀⟩ := by
        intro s hsA hsΛ₀
        change f ⟨s.1, hsA⟩ = (regionIdxSplit h₀ f).1 ⟨s.1, hsΛ₀⟩
        rfl
      -- Now compute the product term by term.
      by_cases hap : a = p.1
      · -- Case a = p.1: each Λ₀-factor is 1; product equals coherenceFactor.
        rw [if_pos hap, mul_one]
        -- coherenceFactor's definition: product over A' of...
        -- LHS product: at each s, the factor is either [combine s = f ⟨s.1, hsA⟩] (if s.1 ∈ A)
        -- or (Ω s.1).ofLp (combine s) (if s.1 ∉ A).
        unfold coherenceFactor
        refine Finset.prod_congr rfl fun s _ => ?_
        by_cases hsA : s.1 ∈ A
        · rw [dif_pos hsA, dif_pos hsA]
          by_cases hsΛ₀ : s.1 ∈ Λ₀
          · rw [if_pos hsΛ₀]
            rw [hcomb_in s hsΛ₀, hf_in s hsA hsΛ₀]
            -- Now: [a ⟨s.1, hsΛ₀⟩ = p.1 ⟨s.1, hsΛ₀⟩] = 1.
            rw [if_pos (by rw [hap])]
          · rw [if_neg hsΛ₀]
            rw [hcomb_out s hsΛ₀, hβ_eq s hsΛ₀]
        · rw [dif_neg hsA, dif_neg hsA]
          have hsΛ₀ : s.1 ∉ Λ₀ := fun h => hsA (h₀ h)
          rw [hcomb_out s hsΛ₀, hβ_eq s hsΛ₀]
      · -- Case a ≠ p.1: there's a witness t where a t ≠ p.1 t.
        rw [if_neg hap, mul_zero]
        obtain ⟨t, ht⟩ := Function.ne_iff.mp hap
        -- Pick s : A' from t.
        let sₜ : A' := ⟨t.1, h₀.trans h t.2⟩
        have hsₜA : sₜ.1 ∈ A := h₀ t.2
        have hsₜΛ₀ : sₜ.1 ∈ Λ₀ := t.2
        -- Show the factor at sₜ is 0.
        apply Finset.prod_eq_zero (Finset.mem_univ sₜ)
        rw [dif_pos hsₜA, hcomb_in sₜ hsₜΛ₀, hf_in sₜ hsₜA hsₜΛ₀]
        -- The factor: [a ⟨sₜ.1, hsₜΛ₀⟩ = p.1 ⟨sₜ.1, hsₜΛ₀⟩] = 0.
        have hat : a ⟨sₜ.1, hsₜΛ₀⟩ = a t := by
          congr 1
        have hpt : p.1 ⟨sₜ.1, hsₜΛ₀⟩ = p.1 t := by
          congr 1
        rw [if_neg (by rw [hat, hpt]; exact ht)]
    rw [hslice, ContinuousLinearMap.map_smul]
    -- Now: ((coherenceFactor ...) • M (single p.1 1)).ofLp α = (coherenceFactor ...) * (M (single p.1 1)).ofLp α
    rw [WithLp.ofLp_smul]
    rfl
  -- Step 2 (LHS form).
  have hLHS :
      ((regionEmbedLeΩ Ω hΩ h) ((tensorWithId h₀ M) (EuclideanSpace.single f (1 : ℂ)))).ofLp g
        = coherenceFactor Ω Λ₀ f g
          * (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp
              (regionIdxSplit (h₀.trans h) g).1 := by
    -- Expand regionEmbedLeΩ as a sum of basis vectors weighted by components.
    rw [regionEmbedLeΩ_apply]
    -- Push `.ofLp g` inside the sum.
    rw [show (∑ f' : regionIdx A,
              (tensorWithId h₀ M (EuclideanSpace.single f (1 : ℂ))).ofLp f'
                • mkRegionVectorΩ Ω h f').ofLp g
            = ∑ f' : regionIdx A,
                (tensorWithId h₀ M (EuclideanSpace.single f (1 : ℂ))).ofLp f'
                  * (mkRegionVectorΩ Ω h f').ofLp g
        from by simp [smul_eq_mul]]
    -- Reindex over `regionIdxEquiv h₀` to split as (a', b').
    rw [show (∑ f' : regionIdx A,
              (tensorWithId h₀ M (EuclideanSpace.single f (1 : ℂ))).ofLp f'
                * (mkRegionVectorΩ Ω h f').ofLp g)
            = ∑ q' : regionIdx Λ₀ × regionIdx (A \ Λ₀),
                (tensorWithId h₀ M
                    (EuclideanSpace.single f (1 : ℂ))).ofLp
                  ((regionIdxEquiv h₀).symm q')
                  * (mkRegionVectorΩ Ω h
                      ((regionIdxEquiv h₀).symm q')).ofLp g
        from by
          rw [← Equiv.sum_comp (regionIdxEquiv h₀).symm
            (fun f' => (tensorWithId h₀ M (EuclideanSpace.single f (1 : ℂ))).ofLp f'
              * (mkRegionVectorΩ Ω h f').ofLp g)]]
    -- Compute (tensorWithId h₀ M (single f 1)).ofLp ((regionIdxEquiv h₀).symm q')
    -- using tensorWithId_ofLp_apply and regionHilbertSplitEquiv_single, regionSplitSlice_single.
    -- Note: regionIdxSplit h₀ ((regionIdxEquiv h₀).symm q') = q' by definition.
    have hT : ∀ q' : regionIdx Λ₀ × regionIdx (A \ Λ₀),
        (tensorWithId h₀ M (EuclideanSpace.single f (1 : ℂ))).ofLp
            ((regionIdxEquiv h₀).symm q')
          = if q'.2 = p.2 then (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp q'.1
            else 0 := by
      intro q'
      rw [tensorWithId_ofLp_apply, regionHilbertSplitEquiv_single]
      rw [show regionIdxSplit h₀ ((regionIdxEquiv h₀).symm q') = q' from
        (regionIdxEquiv h₀).apply_symm_apply q']
      rw [regionSplitSlice_single]
      split_ifs with hq2
      · rfl
      · simp
    -- Use it to rewrite the sum.
    rw [show (∑ q' : regionIdx Λ₀ × regionIdx (A \ Λ₀),
              (tensorWithId h₀ M (EuclideanSpace.single f (1 : ℂ))).ofLp
                ((regionIdxEquiv h₀).symm q')
                * (mkRegionVectorΩ Ω h ((regionIdxEquiv h₀).symm q')).ofLp g)
            = ∑ q' : regionIdx Λ₀ × regionIdx (A \ Λ₀),
                (if q'.2 = p.2 then (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp q'.1
                  else 0)
                * (mkRegionVectorΩ Ω h ((regionIdxEquiv h₀).symm q')).ofLp g
        from Finset.sum_congr rfl (fun q' _ => by rw [hT q'])]
    -- Now expand as ∑_b' ∑_a'.
    rw [Fintype.sum_prod_type]
    -- For each a', ∑_b' (if b' = p.2 then ... else 0) * mkRegionVectorΩ ((symm (a', b'))) g.
    -- Collapse the b' sum.
    rw [show (∑ a' : regionIdx Λ₀,
              ∑ b' : regionIdx (A \ Λ₀),
                (if b' = p.2 then (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp a' else 0)
                  * (mkRegionVectorΩ Ω h ((regionIdxEquiv h₀).symm (a', b'))).ofLp g)
            = ∑ a' : regionIdx Λ₀,
                (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp a'
                  * (mkRegionVectorΩ Ω h
                      ((regionIdxEquiv h₀).symm (a', p.2))).ofLp g
        from by
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [Finset.sum_eq_single p.2]
          · rw [if_pos rfl]
          · intro b' _ hbne
            rw [if_neg hbne, zero_mul]
          · intro h
            exact absurd (Finset.mem_univ _) h]
    -- Now: ∑ a', (M(single p.1 1)).ofLp a' * (mkRegionVectorΩ Ω h ((regionIdxEquiv h₀).symm (a', p.2))).ofLp g
    --   = coherenceFactor * (M(single p.1 1)).ofLp α  where α := (regionIdxSplit (h₀.trans h) g).1.
    -- Goal: collapse the a' sum to a single non-zero term where a' = α.
    -- Show: (mkRegionVectorΩ ... ((regionIdxEquiv h₀).symm (a', p.2))).ofLp g
    --       = (if a' = (regionIdxSplit (h₀.trans h) g).1 then 1 else 0) * coherenceFactor.
    have hMK : ∀ a' : regionIdx Λ₀,
        (mkRegionVectorΩ Ω h ((regionIdxEquiv h₀).symm (a', p.2))).ofLp g
          = (if a' = (regionIdxSplit (h₀.trans h) g).1 then (1 : ℂ) else 0)
              * coherenceFactor Ω Λ₀ f g := by
      intro a'
      rw [mkRegionVectorΩ_ofLp_apply]
      -- Reformulate each factor as the product of an "a'-dependent" indicator
      -- on Λ₀-sites and a "coherence" factor.
      -- We rewrite the product as
      --   ∏ s, ((Λ₀-factor s) * (coherence-factor s))
      -- and split via Finset.prod_mul_distrib.
      rw [show (∏ s : A',
                if hs : s.1 ∈ A then
                  (if g s = ((regionIdxEquiv h₀).symm (a', p.2)) ⟨s.1, hs⟩ then (1 : ℂ) else 0)
                else (Ω s.1) (g s))
              = (∏ s : A',
                  ((if hsΛ₀ : s.1 ∈ Λ₀ then
                      (if g s = a' ⟨s.1, hsΛ₀⟩ then (1 : ℂ) else 0)
                    else (1 : ℂ))
                    *
                    (if hs : s.1 ∈ A then
                      (if s.1 ∈ Λ₀ then (1 : ℂ)
                       else if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
                    else (Ω s.1) (g s))))
          from by
            refine Finset.prod_congr rfl fun s _ => ?_
            by_cases hsA : s.1 ∈ A
            · rw [dif_pos hsA, dif_pos hsA]
              by_cases hsΛ₀ : s.1 ∈ Λ₀
              · rw [dif_pos hsΛ₀, if_pos hsΛ₀]
                -- ((regionIdxEquiv h₀).symm (a', p.2)) ⟨s.1, hsA⟩
                --   = regionIdxCombine h₀ a' p.2 ⟨s.1, hsA⟩ = a' ⟨s.1, hsΛ₀⟩.
                rw [show ((regionIdxEquiv h₀).symm (a', p.2) : regionIdx A)
                      = regionIdxCombine h₀ a' p.2 from rfl]
                rw [regionIdxCombine_of_mem h₀ a' p.2 hsΛ₀]
                rw [mul_one]
              · rw [dif_neg hsΛ₀, if_neg hsΛ₀]
                rw [show ((regionIdxEquiv h₀).symm (a', p.2) : regionIdx A)
                      = regionIdxCombine h₀ a' p.2 from rfl]
                rw [regionIdxCombine_of_not_mem h₀ a' p.2 hsΛ₀]
                rw [one_mul]
                -- Need: p.2 ⟨s.1, mem_sdiff.mpr ⟨hsA, hsΛ₀⟩⟩ = f ⟨s.1, hsA⟩.
                rw [show p.2 ⟨s.1, Finset.mem_sdiff.mpr ⟨hsA, hsΛ₀⟩⟩
                      = f ⟨s.1, hsA⟩ from rfl]
            · rw [dif_neg hsA, dif_neg hsA]
              have hsΛ₀ : s.1 ∉ Λ₀ := fun hL => hsA (h₀ hL)
              rw [dif_neg hsΛ₀]
              rw [one_mul]]
      rw [Finset.prod_mul_distrib]
      -- The second product is exactly `coherenceFactor`.
      change (∏ s : A',
              if hsΛ₀ : s.1 ∈ Λ₀ then
                (if g s = a' ⟨s.1, hsΛ₀⟩ then (1 : ℂ) else 0)
              else (1 : ℂ))
              * coherenceFactor Ω Λ₀ f g = _
      congr 1
      -- Now: ∏ s : A', (if s.1 ∈ Λ₀ then [g s = a' ⟨s.1, _⟩] else 1)
      --     = if a' = (regionIdxSplit (h₀.trans h) g).1 then 1 else 0.
      -- The product reduces to a product over the "Λ₀-image" subfamily of A'.
      by_cases ha : a' = (regionIdxSplit (h₀.trans h) g).1
      · rw [if_pos ha]
        refine Finset.prod_eq_one fun s _ => ?_
        by_cases hsΛ₀ : s.1 ∈ Λ₀
        · rw [dif_pos hsΛ₀]
          rw [if_pos]
          -- a' ⟨s.1, hsΛ₀⟩ = (regionIdxSplit (h₀.trans h) g).1 ⟨s.1, hsΛ₀⟩ = g ⟨s.1, _⟩ = g s.
          rw [ha]
          rfl
        · rw [dif_neg hsΛ₀]
      · rw [if_neg ha]
        obtain ⟨t, ht⟩ := Function.ne_iff.mp ha
        let sₜ : A' := ⟨t.1, h₀.trans h t.2⟩
        have hsₜΛ₀ : sₜ.1 ∈ Λ₀ := t.2
        apply Finset.prod_eq_zero (Finset.mem_univ sₜ)
        rw [dif_pos hsₜΛ₀]
        rw [if_neg]
        -- The condition is `g sₜ = a' ⟨sₜ.1, hsₜΛ₀⟩`, equivalent to `a' t = g ⟨t.1, _⟩`.
        intro heq
        apply ht
        -- ht : a' t ≠ (regionIdxSplit (h₀.trans h) g).1 t.
        -- We have `g sₜ = a' ⟨sₜ.1, hsₜΛ₀⟩`. By def, `g sₜ = g ⟨t.1, _⟩` and `a' ⟨sₜ.1, hsₜΛ₀⟩ = a' t`.
        -- Also `(regionIdxSplit (h₀.trans h) g).1 t = g ⟨t.1, _⟩`.
        have hat : a' ⟨sₜ.1, hsₜΛ₀⟩ = a' t := by congr 1
        have hg_sₜ : g sₜ = (regionIdxSplit (h₀.trans h) g).1 t := rfl
        rw [← hat, ← hg_sₜ, heq]
    rw [show (∑ a' : regionIdx Λ₀,
              (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp a'
                * (mkRegionVectorΩ Ω h
                    ((regionIdxEquiv h₀).symm (a', p.2))).ofLp g)
            = ∑ a' : regionIdx Λ₀,
                (M (EuclideanSpace.single p.1 (1 : ℂ))).ofLp a'
                  * ((if a' = (regionIdxSplit (h₀.trans h) g).1 then (1 : ℂ) else 0)
                      * coherenceFactor Ω Λ₀ f g)
        from Finset.sum_congr rfl (fun a' _ => by rw [hMK a'])]
    rw [Finset.sum_eq_single (regionIdxSplit (h₀.trans h) g).1]
    · rw [if_pos rfl, one_mul]; ring
    · intro a' _ haNe
      rw [if_neg haNe, zero_mul, mul_zero]
    · intro hcontra
      exact absurd (Finset.mem_univ _) hcontra
  rw [hLHS, hRHS]

/-- Coherence (general form): for `Λ₀ ⊆ A ⊆ A'`, the Ω-extension
`regionEmbedLeΩ (A ⊆ A')` commutes with `tensorWithId Λ₀ M` on every
vector of `regionHilbert A`.  Follows from the basis-vector coherence by
linearity. -/
theorem regionEmbedLeΩ_tensorWithId_apply
    {Λ₀ A A' : Finset L} (h₀ : Λ₀ ⊆ A) (h : A ⊆ A')
    (Ω : (s : L) → siteHilbert s) (hΩ : ∀ s, ‖Ω s‖ = 1)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (v : regionHilbert (L := L) A) :
    regionEmbedLeΩ Ω hΩ h (tensorWithId h₀ M v)
      = tensorWithId (h₀.trans h) M (regionEmbedLeΩ Ω hΩ h v) := by
  have hv : v
      = ∑ f : regionIdx (L := L) A,
          v.ofLp f • (EuclideanSpace.single f (1 : ℂ) : regionHilbert (L := L) A) := by
    ext j
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  rw [regionEmbedLeΩ_apply_basis]
  exact regionEmbedLeΩ_tensorWithId_apply_basis h₀ h Ω hΩ M f

/-! ### Per-region family of linear maps

For each finite region `Λ`, we define a linear map
`regionHilbert Λ →ₗ[ℂ] tensorPreHilbertΩ L Ω hΩ` by first Ω-extending into
`regionHilbert (Λ ∪ Λ₀)`, then applying `tensorWithId` over `Λ ∪ Λ₀`, and
finally injecting into the colimit.  The compatibility along the directed
system follows from the coherence theorem above. -/

variable (Ω : (s : L) → siteHilbert s) (hΩ : ∀ s, ‖Ω s‖ = 1)

/-- Per-region linear map sending `x : regionHilbert Λ` to the colimit element
obtained by Ω-extending into `Λ ∪ Λ₀`, applying `tensorWithId` over `Λ ∪ Λ₀`,
and `of`-injecting into `tensorPreHilbertΩ L Ω hΩ`. -/
noncomputable def localEmbedΩFamily (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (Λ : Finset L) :
    regionHilbert (L := L) Λ →ₗ[ℂ] tensorPreHilbertΩ L Ω hΩ :=
  (tensorPreHilbertΩ.of Ω hΩ (Λ ∪ Λ₀)).comp
    (((tensorWithId (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ₀)) M).toLinearMap).comp
      (regionEmbedLeΩ Ω hΩ
        (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ₀))).toLinearMap)

@[simp]
theorem localEmbedΩFamily_apply (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (Λ : Finset L) (x : regionHilbert (L := L) Λ) :
    localEmbedΩFamily (L := L) Ω hΩ Λ₀ M Λ x
      = tensorPreHilbertΩ.of Ω hΩ (Λ ∪ Λ₀)
          (tensorWithId (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ₀)) M
            (regionEmbedLeΩ Ω hΩ
              (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ₀)) x)) := rfl

/-- Helper: the composition of two `regionEmbedLeΩ`'s applied to a vector
agrees with the single `regionEmbedLeΩ` of the composed inclusion. -/
private theorem regionEmbedLeΩ_comp_apply
    {α β γ : Finset L} (h_ab : α ⊆ β) (h_bc : β ⊆ γ)
    (z : regionHilbert (L := L) α) :
    regionEmbedLeΩ Ω hΩ h_bc (regionEmbedLeΩ Ω hΩ h_ab z)
      = regionEmbedLeΩ Ω hΩ (h_ab.trans h_bc) z :=
  (congrArg
    (fun (f : regionHilbert (L := L) α →ₗᵢ[ℂ] regionHilbert (L := L) γ) => f z)
    (regionEmbedLeΩ_trans Ω hΩ h_ab h_bc)).symm

/-- Compatibility of the per-region family along the directed system. -/
theorem localEmbedΩFamily_compat (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') (x : regionHilbert (L := L) Λ) :
    localEmbedΩFamily (L := L) Ω hΩ Λ₀ M Λ' (regionEmbedLeΩ Ω hΩ h x)
      = localEmbedΩFamily (L := L) Ω hΩ Λ₀ M Λ x := by
  rw [localEmbedΩFamily_apply, localEmbedΩFamily_apply]
  have hUL : Λ ∪ Λ₀ ⊆ Λ' ∪ Λ₀ := Finset.union_subset_union_left h
  -- Combine the regionEmbedLeΩ pair on the LHS-of-of-Λ' into a single regionEmbedLeΩ.
  rw [regionEmbedLeΩ_comp_apply (L := L) Ω hΩ h
    (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ₀)) x]
  rw [← regionEmbedLeΩ_comp_apply (L := L) Ω hΩ
    (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ₀)) hUL x]
  -- Goal: of (Λ' ∪ Λ₀) (tensorWithId hR' M (regionEmbedLeΩ hUL (regionEmbedLeΩ (Λ⊆Λ∪Λ₀) x)))
  --     = of (Λ ∪ Λ₀) (tensorWithId hR M (regionEmbedLeΩ (Λ⊆Λ∪Λ₀) x)).
  -- Apply coherence backward on the LHS.
  rw [← regionEmbedLeΩ_tensorWithId_apply
    (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ₀)) hUL Ω hΩ M
    (regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ₀)) x)]
  -- Collapse via of_regionEmbedLeΩ.
  rw [tensorPreHilbertΩ.of_regionEmbedLeΩ]

/-! ### Colimit-level operator -/

/-- Colimit-level linear operator obtained by lifting the family
`localEmbedΩFamily` through `Module.DirectLimit.lift`. -/
noncomputable def localEmbedΩPre (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀) :
    tensorPreHilbertΩ L Ω hΩ →ₗ[ℂ] tensorPreHilbertΩ L Ω hΩ :=
  Module.DirectLimit.lift ℂ (Finset L)
    (fun Λ : Finset L => regionHilbert (L := L) Λ)
    (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap)
    (fun Λ => localEmbedΩFamily (L := L) Ω hΩ Λ₀ M Λ)
    (fun _ _ h x => localEmbedΩFamily_compat (L := L) Ω hΩ Λ₀ M h x)

@[simp]
theorem localEmbedΩPre_of (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (Λ : Finset L) (x : regionHilbert (L := L) Λ) :
    localEmbedΩPre (L := L) Ω hΩ Λ₀ M (tensorPreHilbertΩ.of Ω hΩ Λ x)
      = localEmbedΩFamily (L := L) Ω hΩ Λ₀ M Λ x :=
  Module.DirectLimit.lift_of (R := ℂ) (ι := Finset L)
    (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
    (f := fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap) _ _ _

/-! ### Norm bounds and continuous extension

The colimit injection `tensorPreHilbertΩ.of Λ` is an isometry into
`tensorPreHilbertΩ`, which makes `localEmbedΩPre` Lipschitz and lets us
extend it first to a continuous operator on the algebraic colimit and then
to the completion `globalHilbertOmega`. -/

/-- The colimit injection `tensorPreHilbertΩ.of Ω hΩ Λ` is norm-preserving:
`‖of Λ x‖ = ‖x‖`.  This is the key step in showing that the inner product on
`tensorPreHilbertΩ` reduces to the inner product on each finite region. -/
theorem tensorPreHilbertΩ_norm_of_apply (Λ : Finset L)
    (x : regionHilbert (L := L) Λ) :
    ‖tensorPreHilbertΩ.of Ω hΩ Λ x‖
      = ‖x‖ := by
  -- Reduce to squared norms via `re ⟪·, ·⟫`.
  have hLHS_sq : ‖tensorPreHilbertΩ.of Ω hΩ Λ x‖ ^ 2
      = ‖x‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ]
    rw [tensorPreHilbertΩ.inner_of_of]
    -- Goal: re (star (innerWithLin Λ x Λ x)) = ‖x‖ ^ 2.
    -- Unfold innerWithLin: it equals ⟪regionEmbedLeΩ_L x, regionEmbedLeΩ_R x⟫,
    -- and the two embeddings coincide by proof-irrelevance for Λ ⊆ Λ ∪ Λ.
    change RCLike.re
        (star ⟪regionEmbedLeΩ Ω hΩ
                  (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ)) x,
                regionEmbedLeΩ Ω hΩ
                  (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ)) x⟫_ℂ)
        = ‖x‖ ^ 2
    have hemb :
        regionEmbedLeΩ Ω hΩ
            (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ)) x
          = regionEmbedLeΩ Ω hΩ
              (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ)) x := rfl
    rw [hemb, RCLike.star_def, RCLike.conj_re,
      @inner_self_eq_norm_sq ℂ, LinearIsometry.norm_map]
  -- Conclude `‖of Λ x‖ = ‖x‖` from squared equality and nonnegativity.
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hLHS_sq

/-- Operator-norm bound for `localEmbedΩPre`: `‖localEmbedΩPre Λ₀ M z‖ ≤ ‖M‖ * ‖z‖`.

Reduced to the `of Λ x` case via `induction_on`, where the bound follows from
the operator-norm bound on `tensorWithId` (`tensorWithId_norm_apply_le`),
the isometry `regionEmbedLeΩ`, and the isometry of `of Λ`. -/
theorem norm_localEmbedΩPre_apply (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (z : tensorPreHilbertΩ L Ω hΩ) :
    ‖localEmbedΩPre (L := L) Ω hΩ Λ₀ M z‖ ≤ ‖M‖ * ‖z‖ := by
  refine z.induction_on (fun Λ x => ?_)
  -- Reduce to the `of Λ x` case.
  rw [show (Module.DirectLimit.of ℂ (Finset L)
            (fun Λ : Finset L => regionHilbert (L := L) Λ)
            (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap) Λ) x
        = tensorPreHilbertΩ.of Ω hΩ Λ x from rfl]
  rw [localEmbedΩPre_of, localEmbedΩFamily_apply]
  rw [tensorPreHilbertΩ_norm_of_apply, tensorPreHilbertΩ_norm_of_apply]
  -- ‖tensorWithId h₂ M (regionEmbedLeΩ h₁ x)‖ ≤ ‖M‖ * ‖x‖.
  refine (tensorWithId_norm_apply_le _ _ _).trans ?_
  rw [LinearIsometry.norm_map]

/-- Continuous lift of `localEmbedΩPre Λ₀ M`: a continuous linear operator
on the algebraic colimit `tensorPreHilbertΩ L Ω hΩ`, with operator-norm
bound `‖M‖`. -/
noncomputable def localEmbedΩPreL (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀) :
    tensorPreHilbertΩ L Ω hΩ →L[ℂ] tensorPreHilbertΩ L Ω hΩ :=
  LinearMap.mkContinuous (localEmbedΩPre (L := L) Ω hΩ Λ₀ M) ‖M‖
    (norm_localEmbedΩPre_apply (L := L) Ω hΩ Λ₀ M)

@[simp]
theorem localEmbedΩPreL_apply (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (z : tensorPreHilbertΩ L Ω hΩ) :
    localEmbedΩPreL (L := L) Ω hΩ Λ₀ M z
      = localEmbedΩPre (L := L) Ω hΩ Λ₀ M z := rfl

@[simp]
theorem localEmbedΩPreL_of (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (Λ : Finset L) (x : regionHilbert (L := L) Λ) :
    localEmbedΩPreL (L := L) Ω hΩ Λ₀ M (tensorPreHilbertΩ.of Ω hΩ Λ x)
      = localEmbedΩFamily (L := L) Ω hΩ Λ₀ M Λ x := by
  rw [localEmbedΩPreL_apply, localEmbedΩPre_of]

/-! ### Completion-level operator `localEmbedΩ` -/

/-- The continuous linear operator on `globalHilbertOmega L Ω hΩ` obtained
by extending the algebraic-colimit-level operator `localEmbedΩPreL Λ₀ M`
along the canonical dense isometric embedding into the Cauchy completion. -/
noncomputable def localEmbedΩ (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀) :
    globalHilbertOmega L Ω hΩ →L[ℂ] globalHilbertOmega L Ω hΩ :=
  ContinuousLinearMap.extend
    ((UniformSpace.Completion.toComplL :
        tensorPreHilbertΩ L Ω hΩ →L[ℂ]
          UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)).comp
      (localEmbedΩPreL (L := L) Ω hΩ Λ₀ M))
    UniformSpace.Completion.toComplL

/-- Density of the canonical embedding `toComplL : tensorPreHilbertΩ L Ω hΩ
→L[ℂ] globalHilbertOmega L Ω hΩ`. -/
private theorem denseRange_toComplL :
    DenseRange (UniformSpace.Completion.toComplL :
      tensorPreHilbertΩ L Ω hΩ →L[ℂ]
        UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)) := by
  rw [show ⇑(UniformSpace.Completion.toComplL :
        tensorPreHilbertΩ L Ω hΩ →L[ℂ]
          UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ))
        = ((↑) : tensorPreHilbertΩ L Ω hΩ →
            UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- Uniform-inducing of the canonical embedding `toComplL`. -/
private theorem isUniformInducing_toComplL :
    IsUniformInducing (UniformSpace.Completion.toComplL :
      tensorPreHilbertΩ L Ω hΩ →L[ℂ]
        UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)) := by
  rw [show ⇑(UniformSpace.Completion.toComplL :
        tensorPreHilbertΩ L Ω hΩ →L[ℂ]
          UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ))
        = ((↑) : tensorPreHilbertΩ L Ω hΩ →
            UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe _

/-- Action of `localEmbedΩ Λ₀ M` on a coerced colimit element. -/
@[simp]
theorem localEmbedΩ_coe_apply (Λ₀ : Finset L)
    (M : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
    (z : tensorPreHilbertΩ L Ω hΩ) :
    localEmbedΩ (L := L) Ω hΩ Λ₀ M (z : globalHilbertOmega L Ω hΩ)
      = (localEmbedΩPreL (L := L) Ω hΩ Λ₀ M z : globalHilbertOmega L Ω hΩ) := by
  change localEmbedΩ (L := L) Ω hΩ Λ₀ M
        ((UniformSpace.Completion.toComplL : tensorPreHilbertΩ L Ω hΩ →L[ℂ]
          UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)) z) = _
  rw [localEmbedΩ, ContinuousLinearMap.extend_eq _
    (denseRange_toComplL Ω hΩ) (isUniformInducing_toComplL Ω hΩ)]
  rfl

/-! ### Structural lemmas -/

/-- Identity action: `localEmbedΩ Λ₀ 1 = 1`. -/
@[simp]
theorem localEmbedΩ_one (Λ₀ : Finset L) :
    localEmbedΩ (L := L) Ω hΩ Λ₀
        (ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ₀))
      = ContinuousLinearMap.id ℂ (globalHilbertOmega L Ω hΩ) := by
  -- Use the uniqueness of `extend`: it suffices to verify that the
  -- identity map agrees with the extended map on the dense subspace.
  refine ContinuousLinearMap.extend_unique _
    (denseRange_toComplL Ω hΩ) (isUniformInducing_toComplL Ω hΩ) _ ?_
  ext z
  change (UniformSpace.Completion.toComplL : tensorPreHilbertΩ L Ω hΩ →L[ℂ]
          UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)) z
      = (UniformSpace.Completion.toComplL : tensorPreHilbertΩ L Ω hΩ →L[ℂ]
          UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ))
          (localEmbedΩPreL (L := L) Ω hΩ Λ₀
            (ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ₀)) z)
  congr 1
  -- localEmbedΩPreL Λ₀ id z = z, by induction on z.
  refine z.induction_on (fun Λ x => ?_)
  change tensorPreHilbertΩ.of Ω hΩ Λ x
      = localEmbedΩPreL (L := L) Ω hΩ Λ₀
            (ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ₀))
            (tensorPreHilbertΩ.of Ω hΩ Λ x)
  rw [localEmbedΩPreL_of, localEmbedΩFamily_apply, tensorWithId_one,
    ContinuousLinearMap.id_apply, tensorPreHilbertΩ.of_regionEmbedLeΩ]

/-- Zero action: `localEmbedΩ Λ₀ 0 = 0`. -/
@[simp]
theorem localEmbedΩ_zero (Λ₀ : Finset L) :
    localEmbedΩ (L := L) Ω hΩ Λ₀
        (0 : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
      = 0 := by
  refine ContinuousLinearMap.extend_unique _
    (denseRange_toComplL Ω hΩ) (isUniformInducing_toComplL Ω hΩ) _ ?_
  ext z
  change (0 : globalHilbertOmega L Ω hΩ)
      = (UniformSpace.Completion.toComplL : tensorPreHilbertΩ L Ω hΩ →L[ℂ]
          UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ))
          (localEmbedΩPreL (L := L) Ω hΩ Λ₀
            (0 : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀) z)
  -- localEmbedΩPreL Λ₀ 0 z = 0 by induction.
  rw [show localEmbedΩPreL (L := L) Ω hΩ Λ₀
          (0 : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀) z = 0 from ?_]
  · exact (map_zero _).symm
  refine z.induction_on (fun Λ x => ?_)
  change localEmbedΩPreL (L := L) Ω hΩ Λ₀
        (0 : regionHilbert (L := L) Λ₀ →L[ℂ] regionHilbert (L := L) Λ₀)
        (tensorPreHilbertΩ.of Ω hΩ Λ x)
      = 0
  rw [localEmbedΩPreL_of, localEmbedΩFamily_apply, tensorWithId_zero,
    ContinuousLinearMap.zero_apply, map_zero]

end LocalNetLike
