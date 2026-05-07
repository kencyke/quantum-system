module

public import Mathlib.Algebra.Colimit.Module
public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionDirected

/-!
# Ω-extended directed system of region Hilbert spaces (Phase 3-A.1)

For each unit-vector family `Ω : (s : L) → siteHilbert s` we build the
isometric embedding `regionEmbedLeΩ Ω hΩ h : regionHilbert Λ →ₗᵢ[ℂ] regionHilbert Λ'`
obtained by *tensoring with `Ω` on the new sites* `Λ' \ Λ`.  This generalises
`regionEmbedLe` (Phase 2-a, which uses the reference basis as Ω) and provides
the directed system whose Hilbert colimit will be `globalHilbertOmega L Ω`
(Phase 3-A).

## Main definitions

* `LocalNetLike.mkRegionVectorΩ Ω h f` — image of the region-basis vector
  `EuclideanSpace.single f 1 : regionHilbert Λ` under the Ω-extension into
  `regionHilbert Λ'`.
* `LocalNetLike.regionEmbedLeΩ Ω hΩ h` — region-to-region isometric
  embedding `regionHilbert Λ →ₗᵢ[ℂ] regionHilbert Λ'` filling `Λ' \ Λ`
  with the components of `Ω`.

## Main results

* `LocalNetLike.regionEmbedLeΩ_apply_basis` — basis-vector behaviour:
  `regionEmbedLeΩ` sends `EuclideanSpace.single f 1` to `mkRegionVectorΩ Ω h f`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2 (incomplete infinite tensor product).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace
open Module

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

/-! ### The Ω-extension of a basis vector -/

/-- Image of the basis vector `EuclideanSpace.single f 1 : regionHilbert Λ`
under the Ω-extended embedding into `regionHilbert Λ'`.  Its component at
`g : regionIdx Λ'` is the Kronecker delta `⟦g↾Λ = f⟧` on the inside indices
times the product of `(Ω s.1) (g s)` on the outside indices `s ∈ Λ' \ Λ`. -/
noncomputable def mkRegionVectorΩ (Ω : (s : L) → siteHilbert s)
    {Λ Λ' : Finset L} (_h : Λ ⊆ Λ') (f : regionIdx (L := L) Λ) :
    regionHilbert (L := L) Λ' :=
  (WithLp.equiv 2 (regionIdx (L := L) Λ' → ℂ)).symm
    fun g => ∏ s : Λ',
      (if hs : s.1 ∈ Λ then
         (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
       else (Ω s.1) (g s))

@[simp]
theorem mkRegionVectorΩ_ofLp_apply (Ω : (s : L) → siteHilbert s)
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') (f : regionIdx (L := L) Λ)
    (g : regionIdx (L := L) Λ') :
    (mkRegionVectorΩ Ω h f).ofLp g
      = ∏ s : Λ',
          (if hs : s.1 ∈ Λ then
             (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
           else (Ω s.1) (g s)) := rfl

/-! ### Norm and inner products of `mkRegionVectorΩ` -/

private theorem norm_sq_factor (Ω : (s : L) → siteHilbert s)
    {Λ Λ' : Finset L} (_h : Λ ⊆ Λ') (f : regionIdx (L := L) Λ)
    (s : Λ') (g : regionIdx (L := L) Λ') :
    ‖(if hs : s.1 ∈ Λ then
         (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
       else (Ω s.1) (g s))‖ ^ 2
      = (if hs : s.1 ∈ Λ then
           (if g s = f ⟨s.1, hs⟩ then (1 : ℝ) else 0)
         else ‖(Ω s.1) (g s)‖ ^ 2) := by
  by_cases hs : s.1 ∈ Λ
  · simp [hs]
    by_cases hg : g s = f ⟨s.1, hs⟩
    · simp [hg]
    · simp [hg]
  · simp [hs]

/-- The Ω-extended basis vector has unit norm when each `Ω s` is a unit
vector. -/
theorem mkRegionVectorΩ_norm_sq (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1)
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') (f : regionIdx (L := L) Λ) :
    ‖mkRegionVectorΩ Ω h f‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  -- LHS = ∑ g, ‖(mkRegionVectorΩ Ω h f).ofLp g‖²
  --     = ∑ g, ‖∏ s, (...)‖²
  --     = ∑ g, ∏ s, ‖...‖²
  -- Then swap ∑/∏ via Fintype.prod_sum.
  have h1 :
      (∑ g : regionIdx (L := L) Λ',
          ‖(mkRegionVectorΩ Ω h f).ofLp g‖ ^ 2)
        = ∑ g : regionIdx (L := L) Λ',
            ∏ s : Λ',
              (if hs : s.1 ∈ Λ then
                 (if g s = f ⟨s.1, hs⟩ then (1 : ℝ) else 0)
               else ‖(Ω s.1) (g s)‖ ^ 2) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mkRegionVectorΩ_ofLp_apply]
    rw [show ‖(∏ s : Λ',
                  (if hs : s.1 ∈ Λ then
                     (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
                   else (Ω s.1) (g s)))‖ ^ 2
            = ∏ s : Λ',
                ‖(if hs : s.1 ∈ Λ then
                     (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
                   else (Ω s.1) (g s))‖ ^ 2 from by
        simp [norm_prod, Finset.prod_pow]]
    refine Finset.prod_congr rfl fun s _ => ?_
    exact norm_sq_factor (L := L) Ω h f s g
  rw [h1]
  -- Now ∑_g ∏_s F s (g s) = ∏_s ∑_x F s x by Fintype.prod_sum.
  rw [show (∑ g : regionIdx (L := L) Λ',
              ∏ s : Λ',
                (if hs : s.1 ∈ Λ then
                   (if g s = f ⟨s.1, hs⟩ then (1 : ℝ) else 0)
                 else ‖(Ω s.1) (g s)‖ ^ 2))
            = ∏ s : Λ',
                ∑ x : localIdx s.1,
                  (if hs : s.1 ∈ Λ then
                     (if x = f ⟨s.1, hs⟩ then (1 : ℝ) else 0)
                   else ‖(Ω s.1) x‖ ^ 2) from
    (Fintype.prod_sum (ι := Λ')
      (κ := fun s : Λ' => localIdx s.1)
      (fun s x =>
        (if hs : s.1 ∈ Λ then
           (if x = f ⟨s.1, hs⟩ then (1 : ℝ) else 0)
         else ‖(Ω s.1) x‖ ^ 2))).symm]
  -- Each factor is 1: in-Λ contributes ∑ delta = 1; out-Λ contributes ‖Ω‖² = 1.
  refine Finset.prod_eq_one fun s _ => ?_
  by_cases hs : s.1 ∈ Λ
  · -- ∑ x, ⟦x = f ⟨s.1, hs⟩⟧ = 1
    have step : ∀ x : localIdx s.1,
        (if hs' : s.1 ∈ Λ then
           (if x = f ⟨s.1, hs'⟩ then (1 : ℝ) else 0)
         else ‖(Ω s.1) x‖ ^ 2)
          = (if x = f ⟨s.1, hs⟩ then (1 : ℝ) else 0) := by
      intro x; simp [hs]
    simp_rw [step]
    rw [Finset.sum_ite_eq' Finset.univ (f ⟨s.1, hs⟩) (fun _ => (1 : ℝ))]
    simp
  · -- ∑ x, ‖Ω s.1 x‖² = ‖Ω s.1‖² = 1
    have step : ∀ x : localIdx s.1,
        (if hs' : s.1 ∈ Λ then
           (if x = f ⟨s.1, hs'⟩ then (1 : ℝ) else 0)
         else ‖(Ω s.1) x‖ ^ 2)
          = ‖(Ω s.1) x‖ ^ 2 := by
      intro x; simp [hs]
    simp_rw [step]
    have hsq : ‖Ω s.1‖ ^ 2 = 1 := by rw [hΩ s.1]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at hsq
    -- hsq : ∑ i, ‖(Ω s.1).ofLp i‖² = 1; (Ω s.1) i = (Ω s.1).ofLp i by rfl.
    exact hsq

/-- The Ω-extended basis vectors corresponding to distinct region tuples are
orthogonal. -/
theorem mkRegionVectorΩ_inner_eq_zero_of_ne (Ω : (s : L) → siteHilbert s)
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') {f f' : regionIdx (L := L) Λ} (hff' : f ≠ f') :
    ⟪mkRegionVectorΩ Ω h f, mkRegionVectorΩ Ω h f'⟫_ℂ = 0 := by
  -- Pick a witness t : Λ where f and f' disagree.
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hff'
  -- The Λ'-element corresponding to t.
  set sₜ : Λ' := ⟨t.1, h t.2⟩ with hsₜ
  have hsₜΛ : sₜ.1 ∈ Λ := t.2
  have hsₜt : (⟨sₜ.1, hsₜΛ⟩ : Λ) = t := Subtype.ext rfl
  -- Expand the inner product as a sum over `regionIdx Λ'`.
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_eq_zero fun g _ => ?_
  change (mkRegionVectorΩ Ω h f').ofLp g * star ((mkRegionVectorΩ Ω h f).ofLp g) = 0
  -- Each summand is `(∏_{f'-factors}) * star (∏_{f-factors})`.
  -- Show one of the two products is zero by showing one factor is zero.
  by_cases hgft : g sₜ = f t
  · -- g sₜ = f t ≠ f' t, so the f'-side factor at sₜ is 0.
    have hgft' : g sₜ ≠ f' ⟨sₜ.1, hsₜΛ⟩ := by
      intro heq
      apply ht
      rw [← hgft, heq]
    have h0 : (mkRegionVectorΩ Ω h f').ofLp g = 0 := by
      rw [mkRegionVectorΩ_ofLp_apply]
      apply Finset.prod_eq_zero (Finset.mem_univ sₜ)
      simp [hsₜΛ, hgft']
    rw [h0, zero_mul]
  · -- g sₜ ≠ f t, so the f-side factor at sₜ is 0.
    have hgft₂ : g sₜ ≠ f ⟨sₜ.1, hsₜΛ⟩ := by
      intro heq
      apply hgft
      rw [heq]
    have h0 : (mkRegionVectorΩ Ω h f).ofLp g = 0 := by
      rw [mkRegionVectorΩ_ofLp_apply]
      apply Finset.prod_eq_zero (Finset.mem_univ sₜ)
      simp [hsₜΛ, hgft₂]
    rw [h0, star_zero, mul_zero]

/-- The image family `mkRegionVectorΩ Ω h ·` is an orthonormal family in
`regionHilbert Λ'` whenever each `Ω s` is a unit vector. -/
private theorem orthonormal_mkRegionVectorΩ (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1)
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    Orthonormal ℂ (fun f : regionIdx (L := L) Λ =>
      mkRegionVectorΩ (L := L) Ω h f) := by
  refine ⟨fun f => ?_, fun f f' hff' => ?_⟩
  · -- ‖mkRegionVectorΩ Ω h f‖ = 1 from norm_sq = 1.
    have hsq : ‖mkRegionVectorΩ (L := L) Ω h f‖ ^ 2 = 1 :=
      mkRegionVectorΩ_norm_sq (L := L) Ω hΩ h f
    have hnn : (0 : ℝ) ≤ ‖mkRegionVectorΩ (L := L) Ω h f‖ := norm_nonneg _
    have : Real.sqrt (‖mkRegionVectorΩ (L := L) Ω h f‖ ^ 2) = Real.sqrt 1 := by
      rw [hsq]
    rwa [Real.sqrt_sq hnn, Real.sqrt_one] at this
  · exact mkRegionVectorΩ_inner_eq_zero_of_ne (L := L) Ω h hff'

/-! ### Region-to-region isometric embedding via Ω -/

/-- Region-to-region isometric embedding induced by extending region tuples
*by the unit vector `Ω`* on `Λ' \ Λ`.  Sends a region-basis vector
`EuclideanSpace.single f 1` to `mkRegionVectorΩ Ω h f`. -/
noncomputable def regionEmbedLeΩ (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1) {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    regionHilbert (L := L) Λ →ₗᵢ[ℂ] regionHilbert (L := L) Λ' :=
  LinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
    ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f : regionIdx (L := L) Λ => mkRegionVectorΩ (L := L) Ω h f)
    (by
      change Orthonormal ℂ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
      rw [OrthonormalBasis.coe_toBasis]
      exact (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).orthonormal)
    (by
      have hortho := orthonormal_mkRegionVectorΩ (L := L) Ω hΩ h
      have hfun :
          (⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
                fun f : regionIdx (L := L) Λ => mkRegionVectorΩ (L := L) Ω h f)
              ∘ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis))
            = (fun f : regionIdx (L := L) Λ => mkRegionVectorΩ (L := L) Ω h f) := by
        funext f
        simp [Function.comp_apply]
      rw [hfun]
      exact hortho)

@[simp]
theorem regionEmbedLeΩ_apply_basis (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1) {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) :
    regionEmbedLeΩ Ω hΩ h (EuclideanSpace.single f (1 : ℂ))
      = mkRegionVectorΩ (L := L) Ω h f := by
  change ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f' : regionIdx (L := L) Λ => mkRegionVectorΩ (L := L) Ω h f')
      (EuclideanSpace.single f (1 : ℂ)) = _
  rw [show (EuclideanSpace.single f (1 : ℂ) : regionHilbert (L := L) Λ)
        = (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis f
      from by rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]]
  simp

/-! ### Basis expansion -/

/-- Expansion of `regionEmbedLeΩ Ω hΩ h x` as a `regionIdx Λ`-indexed linear
combination of the Ω-extended basis vectors `mkRegionVectorΩ Ω h f`. -/
theorem regionEmbedLeΩ_apply (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1) {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (x : regionHilbert (L := L) Λ) :
    regionEmbedLeΩ Ω hΩ h x
      = ∑ f : regionIdx (L := L) Λ,
          x.ofLp f • mkRegionVectorΩ (L := L) Ω h f := by
  -- Decompose x as a linear combination of basis vectors `single f 1`.
  have hx : x
      = ∑ f : regionIdx (L := L) Λ,
          x.ofLp f • (EuclideanSpace.single f (1 : ℂ) : regionHilbert (L := L) Λ) := by
    ext j
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [LinearIsometry.map_smul, regionEmbedLeΩ_apply_basis]

/-! ### Functoriality -/

/-- Specialising the Ω-extension to `Λ ⊆ Λ` recovers the basis-vector
representation. -/
theorem mkRegionVectorΩ_subset_refl (Ω : (s : L) → siteHilbert s)
    (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    mkRegionVectorΩ (L := L) Ω (Finset.Subset.refl Λ) f
      = EuclideanSpace.single f (1 : ℂ) := by
  ext g
  rw [mkRegionVectorΩ_ofLp_apply]
  -- Each factor's `dif_pos s.2` reduces it to `⟦g s = f s⟧`.
  have step : ∀ s : Λ,
      (if hs : s.1 ∈ Λ then
         (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
       else (Ω s.1) (g s))
        = (if g s = f s then (1 : ℂ) else 0) := by
    intro s
    rw [dif_pos s.2]
  simp_rw [step]
  -- Compare the product of indicators to the basis-vector component.
  by_cases hgf : g = f
  · subst hgf
    simp [EuclideanSpace.single]
  · obtain ⟨t, ht⟩ := Function.ne_iff.mp hgf
    rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])]
    have : g ≠ f := hgf
    simp [EuclideanSpace.single, this]

/-- The Ω-extension along the identity inclusion `Λ ⊆ Λ` is the identity
linear isometry. -/
theorem regionEmbedLeΩ_self (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1) (Λ : Finset L) :
    regionEmbedLeΩ Ω hΩ (Finset.Subset.refl Λ) = LinearIsometry.id := by
  refine LinearIsometry.toLinearMap_injective ?_
  refine ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis).ext ?_
  intro f
  simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        regionEmbedLeΩ_apply_basis, mkRegionVectorΩ_subset_refl]

/-- Applying `regionEmbedLeΩ Ω hΩ h₂₃` to a `mkRegionVectorΩ`-image along
`h₁₂ : Λ ⊆ Λ'` recovers the `mkRegionVectorΩ`-image along the composition. -/
private theorem regionEmbedLeΩ_apply_mkRegionVectorΩ (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1) {Λ Λ' Λ'' : Finset L}
    (h₁₂ : Λ ⊆ Λ') (h₂₃ : Λ' ⊆ Λ'') (f : regionIdx (L := L) Λ) :
    regionEmbedLeΩ Ω hΩ h₂₃ (mkRegionVectorΩ (L := L) Ω h₁₂ f)
      = mkRegionVectorΩ (L := L) Ω (h₁₂.trans h₂₃) f := by
  rw [regionEmbedLeΩ_apply]
  ext g
  -- Push `.ofLp g` inside the sum.
  rw [show (∑ f' : regionIdx (L := L) Λ',
          (mkRegionVectorΩ (L := L) Ω h₁₂ f).ofLp f'
            • mkRegionVectorΩ (L := L) Ω h₂₃ f').ofLp g
        = ∑ f' : regionIdx (L := L) Λ',
            (mkRegionVectorΩ (L := L) Ω h₁₂ f).ofLp f'
              * (mkRegionVectorΩ (L := L) Ω h₂₃ f').ofLp g
      from by simp [smul_eq_mul]]
  -- The summand vanishes unless f' = g↾Λ'.
  set restrict : regionIdx (L := L) Λ' :=
    (fun s' : Λ' => g ⟨s'.1, h₂₃ s'.2⟩) with hrestrict_def
  have hcollapse :
      (∑ f' : regionIdx (L := L) Λ',
          (mkRegionVectorΩ (L := L) Ω h₁₂ f).ofLp f'
            * (mkRegionVectorΩ (L := L) Ω h₂₃ f').ofLp g)
        = (mkRegionVectorΩ (L := L) Ω h₁₂ f).ofLp restrict
            * (mkRegionVectorΩ (L := L) Ω h₂₃ restrict).ofLp g := by
    refine Finset.sum_eq_single restrict ?_ ?_
    · intros f' _ hfne
      have hb : (mkRegionVectorΩ (L := L) Ω h₂₃ f').ofLp g = 0 := by
        rw [mkRegionVectorΩ_ofLp_apply]
        obtain ⟨s', hs'⟩ := Function.ne_iff.mp hfne
        apply Finset.prod_eq_zero (Finset.mem_univ ⟨s'.1, h₂₃ s'.2⟩)
        have hsΛ' : (⟨s'.1, h₂₃ s'.2⟩ : Λ'').1 ∈ Λ' := s'.2
        simp only [hsΛ', ↓reduceDIte]
        have hne : g ⟨s'.1, h₂₃ s'.2⟩ ≠ f' ⟨s'.1, hsΛ'⟩ := by
          intro heq
          apply hs'
          change f' ⟨s'.1, hsΛ'⟩ = g ⟨s'.1, h₂₃ s'.2⟩
          exact heq.symm
        simp [hne]
      rw [hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hcollapse]
  -- Step 1: simplify `(mkRegionVectorΩ Ω h₂₃ restrict).ofLp g`.
  have hb_simp : (mkRegionVectorΩ (L := L) Ω h₂₃ restrict).ofLp g
      = ∏ s : Λ'', (if (s : Λ'').1 ∈ Λ' then (1 : ℂ) else (Ω s.1) (g s)) := by
    rw [mkRegionVectorΩ_ofLp_apply]
    refine Finset.prod_congr rfl fun s _ => ?_
    by_cases hs : s.1 ∈ Λ'
    · simp only [hs, dif_pos, if_true]
      have hr : restrict ⟨s.1, hs⟩ = g s := rfl
      rw [hr]
      simp
    · simp [hs]
  rw [hb_simp]
  -- Step 2: convert the `Λ''`-product `if s.1 ∈ Λ' then 1 else Ω-factor`
  -- into a `Λ''.filter (·.1 ∉ Λ')`-product.
  rw [show (∏ s : Λ'', (if (s : Λ'').1 ∈ Λ' then (1 : ℂ) else (Ω s.1) (g s)))
        = ∏ s ∈ (Finset.univ : Finset Λ'').filter (fun s : Λ'' => s.1 ∉ Λ'),
            (Ω s.1) (g s)
      from by
        rw [show (fun s : Λ'' => if (s : Λ'').1 ∈ Λ' then (1 : ℂ) else (Ω s.1) (g s))
                = (fun s : Λ'' => if ¬(s : Λ'').1 ∈ Λ' then (Ω s.1) (g s) else (1 : ℂ))
            from by funext s; by_cases hs : s.1 ∈ Λ' <;> simp [hs]]
        rw [Finset.prod_ite]
        simp]
  rw [mkRegionVectorΩ_ofLp_apply]
  -- Step 3: convert `∏ s' : Λ', (...)` into `∏ s ∈ Λ''.filter (·.1 ∈ Λ'), (lifted ...)`.
  rw [show (∏ s' : Λ',
              (if hs' : s'.1 ∈ Λ then
                 (if g ⟨s'.1, h₂₃ s'.2⟩ = f ⟨s'.1, hs'⟩ then (1 : ℂ) else 0)
               else (Ω s'.1) (restrict s')))
            = ∏ s ∈ (Finset.univ : Finset Λ'').filter (fun s : Λ'' => s.1 ∈ Λ'),
                (if hs : s.1 ∈ Λ then
                   (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
                 else (Ω s.1) (g s))
      from by
        refine Finset.prod_bij (fun s' _ => ⟨s'.1, h₂₃ s'.2⟩) ?_ ?_ ?_ ?_
        · intros s' _
          simp [Finset.mem_filter, s'.2]
        · intros s'₁ _ s'₂ _ heq
          exact Subtype.ext (by simpa using congrArg Subtype.val heq)
        · intros s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          exact ⟨⟨s.1, hs⟩, Finset.mem_univ _, rfl⟩
        · intros s' _
          rfl]
  -- Step 4: split the RHS by `s.1 ∈ Λ'` and pair the factors.
  rw [show (∏ s ∈ (Finset.univ : Finset Λ'').filter (fun s : Λ'' => s.1 ∉ Λ'),
              (Ω s.1) (g s))
        = ∏ s ∈ (Finset.univ : Finset Λ'').filter (fun s : Λ'' => s.1 ∉ Λ'),
            (if hs : s.1 ∈ Λ then (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
             else (Ω s.1) (g s))
      from by
        refine Finset.prod_congr rfl fun s hs => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have hsnot : s.1 ∉ Λ := fun h => hs (h₁₂ h)
        simp [hsnot]]
  rw [mkRegionVectorΩ_ofLp_apply]
  exact Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset Λ'')
    (fun s : Λ'' => s.1 ∈ Λ') _

/-- The Ω-extension is functorial under composition of inclusions. -/
theorem regionEmbedLeΩ_trans (Ω : (s : L) → siteHilbert s)
    (hΩ : ∀ s, ‖Ω s‖ = 1) {Λ Λ' Λ'' : Finset L}
    (h₁₂ : Λ ⊆ Λ') (h₂₃ : Λ' ⊆ Λ'') :
    regionEmbedLeΩ Ω hΩ (h₁₂.trans h₂₃)
      = (regionEmbedLeΩ Ω hΩ h₂₃).comp (regionEmbedLeΩ Ω hΩ h₁₂) := by
  refine LinearIsometry.toLinearMap_injective ?_
  refine ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis).ext ?_
  intro f
  simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        regionEmbedLeΩ_apply_basis, regionEmbedLeΩ_apply_mkRegionVectorΩ]

/-! ### Algebraic colimit of the Ω-extended directed system -/

variable (L) in
/-- The directed colimit of `regionHilbert Λ` along the Ω-extension maps
`regionEmbedLeΩ Ω hΩ`.  This is the algebraic backbone of the Phase 3-A
incomplete-tensor-product construction `globalHilbertOmega L Ω`; the
inner-product structure and Hilbert completion are added in subsequent steps.

The colimit lives in the category of ℂ-modules and inherits `AddCommGroup`
and `Module ℂ` automatically. -/
noncomputable def tensorPreHilbertΩ
    (Ω : (s : L) → siteHilbert s) (hΩ : ∀ s, ‖Ω s‖ = 1) : Type _ :=
  Module.DirectLimit (R := ℂ) (ι := Finset L)
    (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
    (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap)

namespace tensorPreHilbertΩ

variable (Ω : (s : L) → siteHilbert s) (hΩ : ∀ s, ‖Ω s‖ = 1)

noncomputable instance : AddCommGroup (tensorPreHilbertΩ L Ω hΩ) :=
  inferInstanceAs (AddCommGroup
    (Module.DirectLimit (R := ℂ) (ι := Finset L)
      (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
      (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap)))

noncomputable instance : Module ℂ (tensorPreHilbertΩ L Ω hΩ) :=
  inferInstanceAs (Module ℂ
    (Module.DirectLimit (R := ℂ) (ι := Finset L)
      (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
      (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap)))

/-- The canonical embedding of a finite-region Hilbert space into the
Ω-tensor pre-Hilbert colimit. -/
noncomputable def of (Λ : Finset L) :
    regionHilbert (L := L) Λ →ₗ[ℂ] tensorPreHilbertΩ L Ω hΩ :=
  Module.DirectLimit.of ℂ (Finset L)
    (fun Λ : Finset L => regionHilbert (L := L) Λ)
    (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap) Λ

@[simp]
theorem of_regionEmbedLeΩ {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (x : regionHilbert (L := L) Λ) :
    of Ω hΩ Λ' (regionEmbedLeΩ Ω hΩ h x) = of Ω hΩ Λ x :=
  Module.DirectLimit.of_f (R := ℂ) (ι := Finset L)
    (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
    (f := fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap)

/-! ### Linear functional `innerLeft Λ x` -/

/-- For a fixed `x : regionHilbert Λ` and a varying second region `Λ'`, the
linear functional `y ↦ ⟪x ⊗ Ω, y ⊗ Ω⟫_{Λ ∪ Λ'}` lifted to `regionHilbert Λ'`
via Ω-extension to the common upper bound `Λ ∪ Λ'`. -/
noncomputable def innerWithLin (Λ : Finset L) (x : regionHilbert (L := L) Λ)
    (Λ' : Finset L) : regionHilbert (L := L) Λ' →ₗ[ℂ] ℂ where
  toFun y :=
    ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) x,
      regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y⟫_ℂ
  map_add' y₁ y₂ := by simp [inner_add_right]
  map_smul' c y := by simp [inner_smul_right]

/-- Compatibility of `innerWithLin Λ x` along the directed system: extending
the second argument by Ω over a larger region preserves the inner product. -/
theorem innerWithLin_compat (Λ : Finset L)
    (x : regionHilbert (L := L) Λ) {Λ' Λ'' : Finset L} (h : Λ' ⊆ Λ'')
    (y : regionHilbert (L := L) Λ') :
    innerWithLin Ω hΩ Λ x Λ'' (regionEmbedLeΩ Ω hΩ h y)
      = innerWithLin Ω hΩ Λ x Λ' y := by
  -- Bridge via the further extension Λ ∪ Λ' ⊆ Λ ∪ Λ''.
  have hUL : Λ ∪ Λ' ⊆ Λ ∪ Λ'' := Finset.union_subset_union_right h
  -- Use functoriality of regionEmbedLeΩ to factor both sides through Λ ∪ Λ'.
  -- regionEmbedLeΩ (Λ ⊆ Λ ∪ Λ'') = regionEmbedLeΩ hUL ∘ regionEmbedLeΩ (Λ ⊆ Λ ∪ Λ').
  have hxL :
      regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ'')) x
        = regionEmbedLeΩ Ω hΩ hUL
            (regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) x) := by
    have htr := regionEmbedLeΩ_trans Ω hΩ
      (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) hUL
    exact congrArg (fun f : regionHilbert (L := L) Λ →ₗᵢ[ℂ]
        regionHilbert (L := L) (Λ ∪ Λ'') => f x) htr
  -- regionEmbedLeΩ (Λ'' ⊆ Λ ∪ Λ'') ∘ regionEmbedLeΩ h
  --   = regionEmbedLeΩ hUL ∘ regionEmbedLeΩ (Λ' ⊆ Λ ∪ Λ').
  have hyR :
      regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ''))
          (regionEmbedLeΩ Ω hΩ h y)
        = regionEmbedLeΩ Ω hΩ hUL
            (regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y) := by
    have htr1 := regionEmbedLeΩ_trans Ω hΩ h
      (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ''))
    have hyL : regionEmbedLeΩ Ω hΩ
          (h.trans (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ''))) y
        = regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ''))
            (regionEmbedLeΩ Ω hΩ h y) :=
      congrArg (fun f : regionHilbert (L := L) Λ' →ₗᵢ[ℂ]
        regionHilbert (L := L) (Λ ∪ Λ'') => f y) htr1
    have htr2 := regionEmbedLeΩ_trans Ω hΩ
      (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) hUL
    have hyR' : regionEmbedLeΩ Ω hΩ
          ((Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')).trans hUL) y
        = regionEmbedLeΩ Ω hΩ hUL
            (regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y) :=
      congrArg (fun f : regionHilbert (L := L) Λ' →ₗᵢ[ℂ]
        regionHilbert (L := L) (Λ ∪ Λ'') => f y) htr2
    rw [← hyL, ← hyR']
  change ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ'')) x,
        regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ''))
          (regionEmbedLeΩ Ω hΩ h y)⟫_ℂ
      = ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) x,
          regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ'))
            y⟫_ℂ
  rw [hxL, hyR]
  exact (regionEmbedLeΩ Ω hΩ hUL).inner_map_map _ _

/-- The linear functional on `tensorPreHilbertΩ L Ω hΩ` induced by a fixed
`x : regionHilbert Λ`: `z ↦ ⟪x, z⟫`. -/
noncomputable def innerLeft (Λ : Finset L) (x : regionHilbert (L := L) Λ) :
    tensorPreHilbertΩ L Ω hΩ →ₗ[ℂ] ℂ :=
  Module.DirectLimit.lift ℂ (Finset L)
    (fun Λ' : Finset L => regionHilbert (L := L) Λ')
    (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap)
    (fun Λ' => innerWithLin Ω hΩ Λ x Λ')
    (fun _ _ h y => innerWithLin_compat Ω hΩ Λ x h y)

@[simp]
theorem innerLeft_of (Λ Λ' : Finset L) (x : regionHilbert (L := L) Λ)
    (y : regionHilbert (L := L) Λ') :
    innerLeft Ω hΩ Λ x (of Ω hΩ Λ' y) = innerWithLin Ω hΩ Λ x Λ' y :=
  Module.DirectLimit.lift_of (R := ℂ) (ι := Finset L)
    (G := fun Λ' : Finset L => regionHilbert (L := L) Λ')
    (f := fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap) _ _ _

/-- Λ-side compatibility of `innerWithLin`: extending the first argument by Ω
along `Λ ⊆ Λ'` does not change the inner product. -/
theorem innerWithLin_regionEmbedLeΩ {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (x : regionHilbert (L := L) Λ) (Λ'' : Finset L)
    (y : regionHilbert (L := L) Λ'') :
    innerWithLin Ω hΩ Λ' (regionEmbedLeΩ Ω hΩ h x) Λ'' y
      = innerWithLin Ω hΩ Λ x Λ'' y := by
  -- Bridge via the further extension Λ ∪ Λ'' ⊆ Λ' ∪ Λ''.
  have hUL : Λ ∪ Λ'' ⊆ Λ' ∪ Λ'' := Finset.union_subset_union_left h
  -- Factor both sides through Λ ∪ Λ''.
  have hxL :
      regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ''))
          (regionEmbedLeΩ Ω hΩ h x)
        = regionEmbedLeΩ Ω hΩ hUL
            (regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ'')) x) := by
    have htr1 := regionEmbedLeΩ_trans Ω hΩ h
      (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ''))
    have hxL' : regionEmbedLeΩ Ω hΩ
          (h.trans (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ''))) x
        = regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ''))
            (regionEmbedLeΩ Ω hΩ h x) :=
      congrArg (fun f : regionHilbert (L := L) Λ →ₗᵢ[ℂ]
        regionHilbert (L := L) (Λ' ∪ Λ'') => f x) htr1
    have htr2 := regionEmbedLeΩ_trans Ω hΩ
      (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ'')) hUL
    have hxR' : regionEmbedLeΩ Ω hΩ
          ((Finset.subset_union_left (s₁ := Λ) (s₂ := Λ'')).trans hUL) x
        = regionEmbedLeΩ Ω hΩ hUL
            (regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ'')) x) :=
      congrArg (fun f : regionHilbert (L := L) Λ →ₗᵢ[ℂ]
        regionHilbert (L := L) (Λ' ∪ Λ'') => f x) htr2
    rw [← hxL', ← hxR']
  have hyR :
      regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ') (s₂ := Λ'')) y
        = regionEmbedLeΩ Ω hΩ hUL
            (regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ'')) y) := by
    have htr := regionEmbedLeΩ_trans Ω hΩ
      (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ'')) hUL
    exact congrArg (fun f : regionHilbert (L := L) Λ'' →ₗᵢ[ℂ]
      regionHilbert (L := L) (Λ' ∪ Λ'') => f y) htr
  change ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ''))
            (regionEmbedLeΩ Ω hΩ h x),
          regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ') (s₂ := Λ''))
            y⟫_ℂ
        = ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ'')) x,
            regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ''))
              y⟫_ℂ
  rw [hxL, hyR]
  exact (regionEmbedLeΩ Ω hΩ hUL).inner_map_map _ _

/-- Λ-side compatibility of `innerLeft`: extending the first argument by Ω
along `Λ ⊆ Λ'` does not change the linear functional. -/
theorem innerLeft_regionEmbedLeΩ {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (x : regionHilbert (L := L) Λ) (z : tensorPreHilbertΩ L Ω hΩ) :
    innerLeft Ω hΩ Λ' (regionEmbedLeΩ Ω hΩ h x) z = innerLeft Ω hΩ Λ x z := by
  refine z.induction_on (fun Λ'' y => ?_)
  change innerLeft Ω hΩ Λ' (regionEmbedLeΩ Ω hΩ h x) (of Ω hΩ Λ'' y)
        = innerLeft Ω hΩ Λ x (of Ω hΩ Λ'' y)
  rw [innerLeft_of, innerLeft_of]
  exact innerWithLin_regionEmbedLeΩ Ω hΩ h x Λ'' y

/-! ### x-side anti-linearity of `innerLeft` -/

theorem innerLeft_add_x (Λ : Finset L) (x₁ x₂ : regionHilbert (L := L) Λ)
    (z : tensorPreHilbertΩ L Ω hΩ) :
    innerLeft Ω hΩ Λ (x₁ + x₂) z = innerLeft Ω hΩ Λ x₁ z + innerLeft Ω hΩ Λ x₂ z := by
  refine z.induction_on (fun Λ' y => ?_)
  change innerLeft Ω hΩ Λ (x₁ + x₂) (of Ω hΩ Λ' y)
        = innerLeft Ω hΩ Λ x₁ (of Ω hΩ Λ' y) + innerLeft Ω hΩ Λ x₂ (of Ω hΩ Λ' y)
  rw [innerLeft_of, innerLeft_of, innerLeft_of]
  change ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) (x₁ + x₂),
          regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y⟫_ℂ
        = ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) x₁,
            regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y⟫_ℂ
          + ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) x₂,
              regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y⟫_ℂ
  rw [LinearIsometry.map_add, inner_add_left]

theorem innerLeft_smul_x (Λ : Finset L) (c : ℂ) (x : regionHilbert (L := L) Λ)
    (z : tensorPreHilbertΩ L Ω hΩ) :
    innerLeft Ω hΩ Λ (c • x) z = star c * innerLeft Ω hΩ Λ x z := by
  refine z.induction_on (fun Λ' y => ?_)
  change innerLeft Ω hΩ Λ (c • x) (of Ω hΩ Λ' y)
        = star c * innerLeft Ω hΩ Λ x (of Ω hΩ Λ' y)
  rw [innerLeft_of, innerLeft_of]
  change ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) (c • x),
          regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y⟫_ℂ
        = star c * ⟪regionEmbedLeΩ Ω hΩ (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ')) x,
            regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ')) y⟫_ℂ
  rw [LinearIsometry.map_smul, inner_smul_left]
  rfl

/-! ### Bilinear lift: `B z₁ z₂ = star (inner z₁ z₂)` -/

/-- Auxiliary `ℂ`-linear map `regionHilbert Λ →ₗ[ℂ] (tensorPreHilbertΩ →ₛₗ[starRingEnd ℂ] ℂ)`,
sending `y` to the *anti-linear* functional `z ↦ star ⟪of Λ y, z⟫`.  Linearity in `y`
arises because the inner product is anti-linear in its first slot, and `star` flips
that to linearity. -/
noncomputable def starInnerLeft (Λ : Finset L) :
    regionHilbert (L := L) Λ →ₗ[ℂ]
      (tensorPreHilbertΩ L Ω hΩ →ₛₗ[starRingEnd ℂ] ℂ) where
  toFun y :=
    { toFun := fun z => star (innerLeft Ω hΩ Λ y z)
      map_add' := by
        intro z₁ z₂
        simp [map_add, star_add]
      map_smul' := by
        intro c z
        change star (innerLeft Ω hΩ Λ y (c • z)) = star c • star (innerLeft Ω hΩ Λ y z)
        rw [map_smul]
        simp [smul_eq_mul, star_mul, mul_comm] }
  map_add' := by
    intro y₁ y₂
    ext z
    change star (innerLeft Ω hΩ Λ (y₁ + y₂) z)
        = star (innerLeft Ω hΩ Λ y₁ z) + star (innerLeft Ω hΩ Λ y₂ z)
    rw [innerLeft_add_x, star_add]
  map_smul' := by
    intro c y
    ext z
    change star (innerLeft Ω hΩ Λ (c • y) z) = c • star (innerLeft Ω hΩ Λ y z)
    rw [innerLeft_smul_x, star_mul]
    simp [smul_eq_mul, mul_comm]

/-- Compatibility of `starInnerLeft` along the directed system. -/
theorem starInnerLeft_compat {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (y : regionHilbert (L := L) Λ) :
    starInnerLeft Ω hΩ Λ' (regionEmbedLeΩ Ω hΩ h y) = starInnerLeft Ω hΩ Λ y := by
  ext z
  change star (innerLeft Ω hΩ Λ' (regionEmbedLeΩ Ω hΩ h y) z)
        = star (innerLeft Ω hΩ Λ y z)
  rw [innerLeft_regionEmbedLeΩ]

/-- The bilinear-style lift: `B z₁ z₂ = star ⟪z₂, z₁⟫`, viewed as a `ℂ`-linear map
to anti-linear functionals.  Linear in `z₁`, anti-linear in `z₂`. -/
noncomputable def innerStarLift :
    tensorPreHilbertΩ L Ω hΩ →ₗ[ℂ]
      (tensorPreHilbertΩ L Ω hΩ →ₛₗ[starRingEnd ℂ] ℂ) :=
  Module.DirectLimit.lift ℂ (Finset L)
    (fun Λ : Finset L => regionHilbert (L := L) Λ)
    (fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap)
    (fun Λ => starInnerLeft Ω hΩ Λ)
    (fun _ _ h y => starInnerLeft_compat Ω hΩ h y)

@[simp]
theorem innerStarLift_of (Λ : Finset L) (y : regionHilbert (L := L) Λ) :
    innerStarLift Ω hΩ (of Ω hΩ Λ y) = starInnerLeft Ω hΩ Λ y :=
  Module.DirectLimit.lift_of (R := ℂ) (ι := Finset L)
    (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
    (f := fun _ _ h => (regionEmbedLeΩ Ω hΩ h).toLinearMap) _ _ _

theorem innerStarLift_of_apply (Λ : Finset L) (y : regionHilbert (L := L) Λ)
    (z : tensorPreHilbertΩ L Ω hΩ) :
    innerStarLift Ω hΩ (of Ω hΩ Λ y) z = star (innerLeft Ω hΩ Λ y z) := by
  rw [innerStarLift_of]
  rfl

/-! ### `Inner ℂ` instance -/

noncomputable instance instInner : Inner ℂ (tensorPreHilbertΩ L Ω hΩ) where
  inner z₁ z₂ := innerStarLift Ω hΩ z₂ z₁

theorem inner_def (z₁ z₂ : tensorPreHilbertΩ L Ω hΩ) :
    ⟪z₁, z₂⟫_ℂ = innerStarLift Ω hΩ z₂ z₁ := rfl

@[simp]
theorem inner_of_of (Λ Λ' : Finset L) (x : regionHilbert (L := L) Λ)
    (y : regionHilbert (L := L) Λ') :
    ⟪of Ω hΩ Λ x, of Ω hΩ Λ' y⟫_ℂ = star (innerWithLin Ω hΩ Λ' y Λ x) := by
  rw [inner_def, innerStarLift_of_apply, innerLeft_of]

/-! ### Sesquilinear properties of `⟪·, ·⟫` -/

theorem inner_add_left' (z₁ z₂ z₃ : tensorPreHilbertΩ L Ω hΩ) :
    ⟪z₁ + z₂, z₃⟫_ℂ = ⟪z₁, z₃⟫_ℂ + ⟪z₂, z₃⟫_ℂ := by
  simp [inner_def, map_add]

theorem inner_smul_left' (c : ℂ) (z₁ z₂ : tensorPreHilbertΩ L Ω hΩ) :
    ⟪c • z₁, z₂⟫_ℂ = star c * ⟪z₁, z₂⟫_ℂ := by
  change (innerStarLift Ω hΩ z₂) (c • z₁) = star c * (innerStarLift Ω hΩ z₂) z₁
  rw [LinearMap.map_smulₛₗ]
  rfl

theorem inner_add_right' (z₁ z₂ z₃ : tensorPreHilbertΩ L Ω hΩ) :
    ⟪z₁, z₂ + z₃⟫_ℂ = ⟪z₁, z₂⟫_ℂ + ⟪z₁, z₃⟫_ℂ := by
  rw [inner_def, inner_def, inner_def]
  show ((innerStarLift Ω hΩ) (z₂ + z₃)) z₁ = _
  rw [map_add]
  rfl

theorem inner_smul_right' (c : ℂ) (z₁ z₂ : tensorPreHilbertΩ L Ω hΩ) :
    ⟪z₁, c • z₂⟫_ℂ = c * ⟪z₁, z₂⟫_ℂ := by
  rw [inner_def, inner_def]
  show ((innerStarLift Ω hΩ) (c • z₂)) z₁ = _
  rw [map_smul]
  rfl

/-- Hermitian symmetry of the inner product.  Proved by reducing to the
canonical region `Λ₁ ∪ Λ₂` for both sides via the directed-system functoriality
and the isometry of `regionEmbedLeΩ`. -/
theorem conj_inner_symm' (z₁ z₂ : tensorPreHilbertΩ L Ω hΩ) :
    star ⟪z₂, z₁⟫_ℂ = ⟪z₁, z₂⟫_ℂ := by
  refine z₁.induction_on (fun Λ₁ x => ?_)
  refine z₂.induction_on (fun Λ₂ y => ?_)
  change star ⟪of Ω hΩ Λ₂ y, of Ω hΩ Λ₁ x⟫_ℂ = ⟪of Ω hΩ Λ₁ x, of Ω hΩ Λ₂ y⟫_ℂ
  -- Lift representatives further to the canonical join `Λ_K := Λ₁ ∪ Λ₂` and
  -- `Λ_K' := Λ₂ ∪ Λ₁` (equal as sets) so that both inner products are taken
  -- in `regionHilbert Λ_K`.
  have hUL12 : Λ₂ ∪ Λ₁ ⊆ Λ₁ ∪ Λ₂ := fun a ha => by
    rcases Finset.mem_union.mp ha with h | h
    · exact Finset.mem_union.mpr (Or.inr h)
    · exact Finset.mem_union.mpr (Or.inl h)
  have hUL21 : Λ₁ ∪ Λ₂ ⊆ Λ₂ ∪ Λ₁ := fun a ha => by
    rcases Finset.mem_union.mp ha with h | h
    · exact Finset.mem_union.mpr (Or.inr h)
    · exact Finset.mem_union.mpr (Or.inl h)
  -- Replace `of Λ₂ y` by `of (Λ₁ ∪ Λ₂) (regionEmbedLeΩ (Λ₂ ⊆ Λ₁∪Λ₂) y)`,
  -- and similarly for `of Λ₁ x`.  By `of_regionEmbedLeΩ` these are equal.
  rw [← of_regionEmbedLeΩ Ω hΩ
        (Finset.subset_union_right (s₁ := Λ₁) (s₂ := Λ₂)) y,
      ← of_regionEmbedLeΩ Ω hΩ
        (Finset.subset_union_left (s₁ := Λ₁) (s₂ := Λ₂)) x]
  rw [inner_of_of, inner_of_of, star_star]
  -- Goal: innerWithLin (Λ₁ ∪ Λ₂) (regionEmbedLeΩ x) (Λ₁ ∪ Λ₂) (regionEmbedLeΩ y)
  --     = star (innerWithLin (Λ₁ ∪ Λ₂) (regionEmbedLeΩ y) (Λ₁ ∪ Λ₂) (regionEmbedLeΩ x))
  -- Both inner products are in regionHilbert ((Λ₁ ∪ Λ₂) ∪ (Λ₁ ∪ Λ₂)) = regionHilbert (Λ₁ ∪ Λ₂)
  -- (by Finset.union_self), with x and y embedded by regionEmbedLeΩ along the
  -- self-inclusion of (Λ₁ ∪ Λ₂).  By regionEmbedLeΩ_self this is the identity.
  -- Hence the goal reduces to inner_conj_symm on regionHilbert (Λ₁ ∪ Λ₂).
  change ⟪regionEmbedLeΩ Ω hΩ
            (Finset.subset_union_left (s₁ := Λ₁ ∪ Λ₂) (s₂ := Λ₁ ∪ Λ₂))
              (regionEmbedLeΩ Ω hΩ
                (Finset.subset_union_left (s₁ := Λ₁) (s₂ := Λ₂)) x),
          regionEmbedLeΩ Ω hΩ
            (Finset.subset_union_right (s₁ := Λ₁ ∪ Λ₂) (s₂ := Λ₁ ∪ Λ₂))
              (regionEmbedLeΩ Ω hΩ
                (Finset.subset_union_right (s₁ := Λ₁) (s₂ := Λ₂)) y)⟫_ℂ
        = star ⟪regionEmbedLeΩ Ω hΩ
                  (Finset.subset_union_left (s₁ := Λ₁ ∪ Λ₂) (s₂ := Λ₁ ∪ Λ₂))
                    (regionEmbedLeΩ Ω hΩ
                      (Finset.subset_union_right (s₁ := Λ₁) (s₂ := Λ₂)) y),
                regionEmbedLeΩ Ω hΩ
                  (Finset.subset_union_right (s₁ := Λ₁ ∪ Λ₂) (s₂ := Λ₁ ∪ Λ₂))
                    (regionEmbedLeΩ Ω hΩ
                      (Finset.subset_union_left (s₁ := Λ₁) (s₂ := Λ₂)) x)⟫_ℂ
  exact (inner_conj_symm _ _).symm

theorem inner_self_nonneg_re (z : tensorPreHilbertΩ L Ω hΩ) :
    0 ≤ RCLike.re ⟪z, z⟫_ℂ := by
  refine z.induction_on (fun Λ x => ?_)
  change 0 ≤ RCLike.re ⟪of Ω hΩ Λ x, of Ω hΩ Λ x⟫_ℂ
  rw [inner_of_of, RCLike.star_def, RCLike.conj_re]
  change (0 : ℝ) ≤ RCLike.re ⟪regionEmbedLeΩ Ω hΩ
        (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ)) x,
      regionEmbedLeΩ Ω hΩ (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ)) x⟫_ℂ
  exact inner_self_nonneg

/-- The inner product is positive-definite on the algebraic colimit. -/
theorem inner_self_eq_zero' (z : tensorPreHilbertΩ L Ω hΩ)
    (h : ⟪z, z⟫_ℂ = 0) : z = 0 := by
  revert h
  refine z.induction_on (fun Λ x hxx => ?_)
  change ⟪of Ω hΩ Λ x, of Ω hΩ Λ x⟫_ℂ = 0 at hxx
  rw [inner_of_of] at hxx
  have hwx : innerWithLin Ω hΩ Λ x Λ x = 0 := by
    have := congrArg star hxx
    rwa [star_star, star_zero] at this
  -- innerWithLin ...  = ⟪regemb x, regemb x⟫_{Λ ∪ Λ}
  have hxemb : regionEmbedLeΩ Ω hΩ
      (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ)) x = 0 := by
    have : ⟪regionEmbedLeΩ Ω hΩ
            (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ)) x,
          regionEmbedLeΩ Ω hΩ
            (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ)) x⟫_ℂ = 0 := hwx
    -- both subset_union_left and subset_union_right are Λ ⊆ Λ ∪ Λ; the
    -- `regionEmbedLeΩ` value depends only on the Finset Λ ∪ Λ, so the two
    -- arguments to inner are the same vector.
    have heq : regionEmbedLeΩ Ω hΩ
            (Finset.subset_union_left (s₁ := Λ) (s₂ := Λ)) x
        = regionEmbedLeΩ Ω hΩ
            (Finset.subset_union_right (s₁ := Λ) (s₂ := Λ)) x := rfl
    rw [heq] at this
    exact inner_self_eq_zero.mp this
  -- regionEmbedLeΩ is injective (isometric).
  have hx : x = 0 :=
    (regionEmbedLeΩ Ω hΩ _).injective
      (by rw [hxemb, LinearIsometry.map_zero])
  rw [hx]
  exact (of Ω hΩ Λ).map_zero

/-! ### `InnerProductSpace.Core` instance and Hilbert structure -/

noncomputable instance instInnerProductSpaceCore :
    InnerProductSpace.Core ℂ (tensorPreHilbertΩ L Ω hΩ) where
  __ := instInner Ω hΩ
  conj_inner_symm := conj_inner_symm' Ω hΩ
  re_inner_nonneg := inner_self_nonneg_re Ω hΩ
  add_left := inner_add_left' Ω hΩ
  smul_left := fun x y r => inner_smul_left' Ω hΩ r x y
  definite := inner_self_eq_zero' Ω hΩ

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (tensorPreHilbertΩ L Ω hΩ) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

noncomputable instance instInnerProductSpace :
    InnerProductSpace ℂ (tensorPreHilbertΩ L Ω hΩ) :=
  InnerProductSpace.ofCore inferInstance

end tensorPreHilbertΩ

/-! ### `globalHilbertOmega` via Cauchy completion -/

variable (L) in
/-- The Hilbert space `globalHilbertOmega L Ω hΩ` of the incomplete infinite
tensor product attached to the unit-vector reference family `Ω`.  Constructed
as the Cauchy completion of the algebraic colimit `tensorPreHilbertΩ L Ω hΩ`.

This is the von Neumann (Bratteli–Robinson §2.7.2) reference sector containing
`Ω` as the analogue of the vacuum vector. -/
@[reducible] noncomputable def globalHilbertOmega
    (Ω : (s : L) → siteHilbert s) (hΩ : ∀ s, ‖Ω s‖ = 1) : Type _ :=
  UniformSpace.Completion (tensorPreHilbertΩ L Ω hΩ)

end LocalNetLike
