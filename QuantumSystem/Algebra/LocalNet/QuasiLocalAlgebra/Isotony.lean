module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.QuasiLocal

/-!
# Isotony of local subalgebras (Phase 5'd)

We verify the isotony axiom (Verch 2025 §1.2 axiom i / Naaijkens 2012 §1.3)
for the local-subalgebra family: for `Λ ⊆ Λ' : Finset L`,

`localSubalgebra Λ ≤ localSubalgebra Λ'`.

The construction goes through a finite-dimensional analogue of
`localEmbed`: for each `M : regionHilbert Λ →L[ℂ] regionHilbert Λ` we build
`regionLift h M : regionHilbert Λ' →L[ℂ] regionHilbert Λ'` such that
`localEmbed Λ' (regionLift h M) = localEmbed Λ M`.  The lift is the
basis-indexed realisation of `M ⊗ 1_{Λ'\Λ}`.

## Main definitions / theorems

* `LocalNetLike.regionLiftRestrict h a'` — restrict a `regionIdx Λ'`
  tuple to the smaller region `Λ`.
* `LocalNetLike.regionLiftSwap h b a'` — replace the Λ-part of a
  `regionIdx Λ'` tuple with a `regionIdx Λ` tuple.
* `LocalNetLike.regionLift h M` — the lift `M ⊗ 1_{Λ'\Λ}` as a CLM.
* `LocalNetLike.localEmbed_regionLift_eq` — compatibility:
  `localEmbed Λ' (regionLift h M) = localEmbed Λ M`.
* `LocalNetLike.localSubalgebra_le_of_subset` — isotony at the
  StarSubalgebra level.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
* Verch, *Algebraic quantum field theory and operator algebras*, 2025, §1.2.
-/

@[expose] public section

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-! ### Index-level helpers for `Λ ⊆ Λ'` -/

/-- Restrict a `regionIdx Λ'` tuple to a smaller region `Λ ⊆ Λ'`. -/
def regionLiftRestrict {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (a' : regionIdx (L := L) Λ') : regionIdx (L := L) Λ :=
  fun s => a' ⟨s.1, h s.2⟩

/-- Replace the Λ-part of a `regionIdx Λ'` tuple with a `regionIdx Λ` tuple.
The hypothesis `h : Λ ⊆ Λ'` is not used in the construction itself but is
retained to make the lemma signatures uniform across `regionLift` API. -/
def regionLiftSwap {Λ Λ' : Finset L} (_h : Λ ⊆ Λ')
    (b : regionIdx (L := L) Λ) (a' : regionIdx (L := L) Λ') :
    regionIdx (L := L) Λ' :=
  fun s => if h_s : s.1 ∈ Λ then b ⟨s.1, h_s⟩ else a' s

omit hL in
@[simp]
theorem regionLiftSwap_apply_of_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (b : regionIdx (L := L) Λ) (a' : regionIdx (L := L) Λ')
    (s : ↥Λ') (hs : s.1 ∈ Λ) :
    regionLiftSwap h b a' s = b ⟨s.1, hs⟩ :=
  dif_pos hs

omit hL in
@[simp]
theorem regionLiftSwap_apply_of_not_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (b : regionIdx (L := L) Λ) (a' : regionIdx (L := L) Λ')
    (s : ↥Λ') (hs : s.1 ∉ Λ) :
    regionLiftSwap h b a' s = a' s :=
  dif_neg hs

omit hL in
@[simp]
theorem regionLiftRestrict_regionLiftSwap {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (b : regionIdx (L := L) Λ) (a' : regionIdx (L := L) Λ') :
    regionLiftRestrict h (regionLiftSwap h b a') = b := by
  funext ⟨s, hs⟩
  simp [regionLiftRestrict, regionLiftSwap_apply_of_mem h b a' ⟨s, h hs⟩ hs]

/-- Compatibility: a `Λ'`-swap on `g : globalIdx L` whose `Λ'`-part has been
itself swapped on `Λ` collapses to a single `Λ`-swap. -/
theorem globalSwap_regionLiftSwap_regionRestrict {Λ Λ' : Finset L}
    (h : Λ ⊆ Λ') (b : regionIdx (L := L) Λ) (g : globalIdx L) :
    globalSwap Λ' (regionLiftSwap h b (regionRestrict Λ' g)) g
      = globalSwap Λ b g := by
  apply Subtype.ext
  funext s
  by_cases h₁ : s ∈ Λ'
  · rw [globalSwap_val_apply_of_mem _ _ _ h₁]
    by_cases h₂ : s ∈ Λ
    · rw [globalSwap_val_apply_of_mem _ _ _ h₂,
        regionLiftSwap_apply_of_mem h b _ ⟨s, h₁⟩ h₂]
    · rw [globalSwap_val_apply_of_not_mem _ _ _ h₂,
        regionLiftSwap_apply_of_not_mem h b _ ⟨s, h₁⟩ h₂]
      rfl
  · have h₂ : s ∉ Λ := fun hs => h₁ (h hs)
    rw [globalSwap_val_apply_of_not_mem _ _ _ h₁,
      globalSwap_val_apply_of_not_mem _ _ _ h₂]

/-! ### `regionLift` as a finite-dimensional ampliation -/

/-- Local restriction in the finite-dimensional setting: for
`v' : regionHilbert Λ'` and `a' : regionIdx Λ'`, `vRestrict h v' a'` is
the vector in `regionHilbert Λ` whose `b`-th coordinate is the value of
`v'` at the tuple obtained by replacing `a'`'s Λ-part with `b`. -/
noncomputable def vRestrict {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (v' : regionHilbert (L := L) Λ') (a' : regionIdx (L := L) Λ') :
    regionHilbert (L := L) Λ :=
  WithLp.toLp 2 (fun b : regionIdx (L := L) Λ =>
    (v' : regionIdx (L := L) Λ' → ℂ) (regionLiftSwap h b a'))

omit hL in
@[simp]
theorem vRestrict_apply {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (v' : regionHilbert (L := L) Λ') (a' : regionIdx (L := L) Λ')
    (b : regionIdx (L := L) Λ) :
    (vRestrict h v' a' : regionIdx (L := L) Λ → ℂ) b
      = (v' : regionIdx (L := L) Λ' → ℂ) (regionLiftSwap h b a') := rfl

/-- The pointwise coefficient that defines `regionLift h M`: at the
`regionIdx Λ'`-tuple `a'`, evaluate `M` on the local restriction
`vRestrict h v' a'` and read off the entry at `regionLiftRestrict h a'`. -/
noncomputable def regionLiftCoeff {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (v' : regionHilbert (L := L) Λ') (a' : regionIdx (L := L) Λ') : ℂ :=
  (M (vRestrict h v' a') : regionIdx (L := L) Λ → ℂ) (regionLiftRestrict h a')

omit hL in
/-- `regionLiftCoeff h M` is additive in the `H_{Λ'}` argument. -/
private theorem regionLiftCoeff_add {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (v₁ v₂ : regionHilbert (L := L) Λ') (a' : regionIdx (L := L) Λ') :
    regionLiftCoeff h M (v₁ + v₂) a'
      = regionLiftCoeff h M v₁ a' + regionLiftCoeff h M v₂ a' := by
  unfold regionLiftCoeff
  have hadd : vRestrict h (v₁ + v₂) a' = vRestrict h v₁ a' + vRestrict h v₂ a' := by
    ext b
    simp only [vRestrict_apply]
    rfl
  rw [hadd, M.map_add]
  rfl

omit hL in
/-- `regionLiftCoeff h M` is `ℂ`-linear in the `H_{Λ'}` argument. -/
private theorem regionLiftCoeff_smul {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (c : ℂ) (v : regionHilbert (L := L) Λ') (a' : regionIdx (L := L) Λ') :
    regionLiftCoeff h M (c • v) a' = c • regionLiftCoeff h M v a' := by
  unfold regionLiftCoeff
  have hsmul : vRestrict h (c • v) a' = c • vRestrict h v a' := by
    ext b
    simp only [vRestrict_apply]
    rfl
  rw [hsmul, M.map_smul]
  rfl

/-- Underlying linear map of `regionLift h M`: it sends `v' : H_{Λ'}` to the
vector whose `a'`-th coordinate is `regionLiftCoeff h M v' a'`. -/
noncomputable def regionLiftLM {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    regionHilbert (L := L) Λ' →ₗ[ℂ] regionHilbert (L := L) Λ' where
  toFun v' := WithLp.toLp 2 (fun a' : regionIdx (L := L) Λ' =>
    regionLiftCoeff h M v' a')
  map_add' v₁ v₂ := by
    rw [show (fun a' : regionIdx (L := L) Λ' => regionLiftCoeff h M (v₁ + v₂) a')
          = (fun a' => regionLiftCoeff h M v₁ a')
              + (fun a' => regionLiftCoeff h M v₂ a') from
        funext fun a' => regionLiftCoeff_add h M v₁ v₂ a']
    rw [WithLp.toLp_add]
  map_smul' c v := by
    rw [show (fun a' : regionIdx (L := L) Λ' => regionLiftCoeff h M (c • v) a')
          = c • (fun a' => regionLiftCoeff h M v a') from
        funext fun a' => regionLiftCoeff_smul h M c v a']
    rw [WithLp.toLp_smul]
    rfl

/-- The lift `regionLift h M : H_{Λ'} →L[ℂ] H_{Λ'}` of an operator on the
smaller region.  Realises `M ⊗ 1_{Λ'\Λ}` in the basis-indexed model. -/
noncomputable def regionLift {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    regionHilbert (L := L) Λ' →L[ℂ] regionHilbert (L := L) Λ' :=
  LinearMap.toContinuousLinearMap (regionLiftLM h M)

omit hL in
@[simp]
theorem regionLift_apply_apply {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (v' : regionHilbert (L := L) Λ') (a' : regionIdx (L := L) Λ') :
    (regionLift h M v' : regionIdx (L := L) Λ' → ℂ) a'
      = regionLiftCoeff h M v' a' := rfl

/-! ### Compatibility with `localEmbed` -/

/-- The local restriction at `Λ` factors through the lifted restriction at
`Λ'`: `vRestrict h (wRestrict Λ' w g) (regionRestrict Λ' g) = wRestrict Λ w g`. -/
theorem vRestrict_wRestrict_regionRestrict {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (w : globalHilbert L) (g : globalIdx L) :
    vRestrict h (wRestrict Λ' w g) (regionRestrict Λ' g)
      = wRestrict Λ w g := by
  ext b
  simp only [vRestrict_apply, wRestrict_apply]
  rw [globalSwap_regionLiftSwap_regionRestrict h b g]

/-- The Λ-part of a global tuple agrees with the Λ-restriction of its
Λ'-restriction (when `Λ ⊆ Λ'`). -/
theorem regionLiftRestrict_regionRestrict {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (g : globalIdx L) :
    regionLiftRestrict h (regionRestrict Λ' g) = regionRestrict Λ g := by
  funext s
  rfl

/-- Key compatibility: lifting `M` from `Λ` to `Λ'` and embedding via
`localEmbed Λ'` gives the same operator on `globalHilbert L` as embedding
`M` directly via `localEmbed Λ`. -/
theorem localEmbed_regionLift_eq {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbed Λ' (regionLift h M) = localEmbed Λ M := by
  ext w g
  rw [localEmbed_apply_apply, localEmbed_apply_apply]
  unfold localEmbedCoeff
  change ((regionLift h M (wRestrict Λ' w g) : regionHilbert (L := L) Λ')
          : regionIdx (L := L) Λ' → ℂ) (regionRestrict Λ' g)
      = ((M (wRestrict Λ w g) : regionHilbert (L := L) Λ)
          : regionIdx (L := L) Λ → ℂ) (regionRestrict Λ g)
  rw [regionLift_apply_apply]
  unfold regionLiftCoeff
  rw [vRestrict_wRestrict_regionRestrict h w g,
    regionLiftRestrict_regionRestrict h g]

/-! ### Isotony at the StarSubalgebra level -/

/-- Isotony: for `Λ ⊆ Λ'`, the local subalgebra at `Λ` is contained in the
local subalgebra at `Λ'`.  This is Verch 2025 §1.2 axiom (i). -/
theorem localSubalgebra_le_of_subset {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    localSubalgebra Λ ≤ localSubalgebra Λ' := by
  intro T hT
  obtain ⟨M, hM⟩ := (mem_localSubalgebra Λ T).mp hT
  exact (mem_localSubalgebra Λ' T).mpr ⟨regionLift h M, by rw [localEmbed_regionLift_eq, hM]⟩

end LocalNetLike
