module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.QuasiLocal

/-!
# Locality of the quasi-local algebra (Phase 5'd)

We verify the locality axiom of Naaijkens 2012 §1.3 / Verch 2025 §1.2 (axiom
ii) for the quasi-local algebra `quasiLocal L`: operators supported on
disjoint finite regions commute.

Concretely, for `Λ₁, Λ₂ : Finset L` with `Disjoint Λ₁ Λ₂` and arbitrary
`M₁ : regionHilbert Λ₁ →L[ℂ] regionHilbert Λ₁`,
`M₂ : regionHilbert Λ₂ →L[ℂ] regionHilbert Λ₂`,
we have

`Commute (localEmbed Λ₁ M₁) (localEmbed Λ₂ M₂)`.

This lifts to `localSubalgebra_commute_of_disjoint`: every operator in
`localSubalgebra Λ₁` commutes with every operator in `localSubalgebra Λ₂`.

## Main results

* `LocalNetLike.globalSwap_comm_disjoint`: `globalSwap Λ₁` and `globalSwap Λ₂`
  commute when `Λ₁` and `Λ₂` are disjoint.
* `LocalNetLike.regionRestrict_globalSwap_disjoint_left`: restricting to `Λ₂`
  is unchanged by a swap on the disjoint region `Λ₁`.
* `LocalNetLike.localEmbed_commute_of_disjoint`: the main locality lemma at
  the operator level.
* `LocalNetLike.localSubalgebra_commute_of_disjoint`: locality at the
  StarSubalgebra level.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
* Verch, *Algebraic quantum field theory and operator algebras*, 2025, §1.2.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- Swaps on disjoint regions commute. -/
theorem globalSwap_comm_disjoint
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (f₁ : regionIdx (L := L) Λ₁) (f₂ : regionIdx (L := L) Λ₂)
    (g : globalIdx L) :
    globalSwap Λ₁ f₁ (globalSwap Λ₂ f₂ g)
      = globalSwap Λ₂ f₂ (globalSwap Λ₁ f₁ g) := by
  apply Subtype.ext
  funext s
  by_cases h₁ : s ∈ Λ₁
  · have h₂ : s ∉ Λ₂ := fun h => Finset.disjoint_left.mp hd h₁ h
    simp [globalSwap_val_apply_of_mem _ _ _ h₁,
      globalSwap_val_apply_of_not_mem _ _ _ h₂]
  · by_cases h₂ : s ∈ Λ₂
    · simp [globalSwap_val_apply_of_not_mem _ _ _ h₁,
        globalSwap_val_apply_of_mem _ _ _ h₂]
    · simp [globalSwap_val_apply_of_not_mem _ _ _ h₁,
        globalSwap_val_apply_of_not_mem _ _ _ h₂]

/-- Restricting to one finite region is unchanged by a swap on the disjoint
finite region.  This expresses the geometric fact that `Λ₁` and `Λ₂` are
"non-overlapping" sites. -/
theorem regionRestrict_globalSwap_disjoint_left
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (f₁ : regionIdx (L := L) Λ₁) (g : globalIdx L) :
    regionRestrict Λ₂ (globalSwap Λ₁ f₁ g) = regionRestrict Λ₂ g := by
  funext s
  have h_ns : s.1 ∉ Λ₁ := fun h => Finset.disjoint_right.mp hd s.2 h
  change (globalSwap Λ₁ f₁ g).val s.1 = g.val s.1
  exact globalSwap_val_apply_of_not_mem _ _ _ h_ns

/-! ### Locality at the operator level -/

/-- Operators on disjoint regions commute as continuous linear maps on the
infinite-site Hilbert space.  This is the core formal statement of locality
(Verch 2025 §1.2 axiom ii). -/
theorem localEmbed_commute_of_disjoint
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (M₁ : ℋ(Λ₁) →L[ℂ] ℋ(Λ₁))
    (M₂ : ℋ(Λ₂) →L[ℂ] ℋ(Λ₂)) :
    Commute (localEmbed Λ₁ M₁) (localEmbed Λ₂ M₂) := by
  -- Show `localEmbed Λ₁ M₁ * localEmbed Λ₂ M₂ = localEmbed Λ₂ M₂ * localEmbed Λ₁ M₁`.
  change localEmbed Λ₁ M₁ * localEmbed Λ₂ M₂
        = localEmbed Λ₂ M₂ * localEmbed Λ₁ M₁
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  funext g
  -- Reduce to coordinate equality at `g`.
  rw [show localEmbed Λ₁ M₁ * localEmbed Λ₂ M₂
        = localEmbed Λ₁ M₁ ∘L localEmbed Λ₂ M₂ from rfl,
      show localEmbed Λ₂ M₂ * localEmbed Λ₁ M₁
        = localEmbed Λ₂ M₂ ∘L localEmbed Λ₁ M₁ from rfl,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      localEmbed_apply_apply, localEmbed_apply_apply,
      localEmbedCoeff_eq_sum, localEmbedCoeff_eq_sum]
  -- LHS: Σ_{f₁} (M₁ e_{f₁})_{rR Λ₁ g} * (localEmbed Λ₂ M₂ w).val (gSwap Λ₁ f₁ g)
  -- Expand the inner term via localEmbedCoeff_eq_sum, then simplify with disjointness.
  have hd' : Disjoint Λ₂ Λ₁ := hd.symm
  have hLHS_inner : ∀ f₁ : regionIdx (L := L) Λ₁,
      ((localEmbed Λ₂ M₂ w : globalHilbert L) : globalIdx L → ℂ)
            (globalSwap Λ₁ f₁ g)
        = ∑ f₂ : regionIdx (L := L) Λ₂,
            ((M₂ (EuclideanSpace.single f₂ (1 : ℂ)) : regionIdx (L := L) Λ₂ → ℂ)
                (regionRestrict Λ₂ g))
              * ((w : lp (fun _ : globalIdx L => ℂ) 2) : globalIdx L → ℂ)
                  (globalSwap Λ₂ f₂ (globalSwap Λ₁ f₁ g)) := by
    intro f₁
    rw [localEmbed_apply_apply, localEmbedCoeff_eq_sum]
    refine Finset.sum_congr rfl fun f₂ _ => ?_
    rw [regionRestrict_globalSwap_disjoint_left hd f₁ g]
  have hRHS_inner : ∀ f₂ : regionIdx (L := L) Λ₂,
      ((localEmbed Λ₁ M₁ w : globalHilbert L) : globalIdx L → ℂ)
            (globalSwap Λ₂ f₂ g)
        = ∑ f₁ : regionIdx (L := L) Λ₁,
            ((M₁ (EuclideanSpace.single f₁ (1 : ℂ)) : regionIdx (L := L) Λ₁ → ℂ)
                (regionRestrict Λ₁ g))
              * ((w : lp (fun _ : globalIdx L => ℂ) 2) : globalIdx L → ℂ)
                  (globalSwap Λ₁ f₁ (globalSwap Λ₂ f₂ g)) := by
    intro f₂
    rw [localEmbed_apply_apply, localEmbedCoeff_eq_sum]
    refine Finset.sum_congr rfl fun f₁ _ => ?_
    rw [regionRestrict_globalSwap_disjoint_left hd' f₂ g]
  -- Substitute the inner expansions.
  simp_rw [hLHS_inner, hRHS_inner]
  -- LHS = Σ_{f₁} (M₁)_{r₁, f₁} * (Σ_{f₂} (M₂)_{r₂, f₂} * w.val(swap₂ f₂ (swap₁ f₁ g)))
  -- Use Finset.mul_sum and Finset.sum_comm.
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Both sides are now Σ_{f₂} Σ_{f₁} ... ; compare summands.
  refine Finset.sum_congr rfl fun f₂ _ => ?_
  refine Finset.sum_congr rfl fun f₁ _ => ?_
  -- LHS_summand: (M₁)_{r₁, f₁} * ((M₂)_{r₂, f₂} * w.val(swap Λ₂ f₂ (swap Λ₁ f₁ g)))
  -- RHS_summand: (M₂)_{r₂, f₂} * ((M₁)_{r₁, f₁} * w.val(swap Λ₁ f₁ (swap Λ₂ f₂ g)))
  rw [globalSwap_comm_disjoint hd f₁ f₂ g]
  ring

/-! ### Locality at the StarSubalgebra level -/

/-- Operators in `localSubalgebra Λ₁` commute with operators in
`localSubalgebra Λ₂` whenever `Λ₁` and `Λ₂` are disjoint. -/
theorem localSubalgebra_commute_of_disjoint
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : globalHilbert L →L[ℂ] globalHilbert L}
    (h₁ : T₁ ∈ localSubalgebra Λ₁) (h₂ : T₂ ∈ localSubalgebra Λ₂) :
    Commute T₁ T₂ := by
  obtain ⟨M₁, hM₁⟩ := (mem_localSubalgebra Λ₁ T₁).mp h₁
  obtain ⟨M₂, hM₂⟩ := (mem_localSubalgebra Λ₂ T₂).mp h₂
  rw [← hM₁, ← hM₂]
  exact localEmbed_commute_of_disjoint hd M₁ M₂

end LocalNetLike
