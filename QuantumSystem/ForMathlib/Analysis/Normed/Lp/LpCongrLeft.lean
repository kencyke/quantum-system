module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Reindexing an `lp` space along an index equivalence

For a constant-fibre `lp` space `lp (fun _ : ι => E) p` and an index
equivalence `e : ι ≃ ι'`, `LinearIsometryEquiv.lpCongrLeft` reindexes the
coordinates to give a linear isometric equivalence

`lp (fun _ : ι => E) p ≃ₗᵢ[𝕜] lp (fun _ : ι' => E) p`.

This is the `lp` analogue of `LinearIsometryEquiv.piLpCongrLeft` (which only
covers the finite-index `PiLp`).  The construction is stated for exponents with
`0 < p.toReal` (in particular `p = 2`), which lets membership and norm transfer
through `Equiv.summable_iff` / `Equiv.tsum_eq`.
-/

@[expose] public section

open scoped ENNReal

namespace lp

variable {ι ι' E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Reindexing a `0 < p`-summable family by `e.symm` preserves `Memℓp`. -/
theorem memℓp_comp_equiv (hp : 0 < p.toReal) (e : ι ≃ ι')
    (f : ι → E) (hf : Memℓp f p) : Memℓp (fun i' => f (e.symm i')) p := by
  rw [memℓp_gen_iff hp]
  exact (Equiv.summable_iff e.symm).mpr ((memℓp_gen_iff hp).mp hf)

/-- Reindex a constant-fibre `lp` space along an index equivalence `e : ι ≃ ι'`,
as a linear isometric equivalence.  The `lp` analogue of
`LinearIsometryEquiv.piLpCongrLeft`. -/
noncomputable def _root_.LinearIsometryEquiv.lpCongrLeft
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (e : ι ≃ ι') :
    lp (fun _ : ι => E) p ≃ₗᵢ[𝕜] lp (fun _ : ι' => E) p where
  toFun ψ := ⟨fun i' => ψ (e.symm i'), memℓp_comp_equiv hp e _ (lp.memℓp ψ)⟩
  invFun φ := ⟨fun i => φ (e i), by
    have h := memℓp_comp_equiv hp e.symm _ (lp.memℓp φ)
    simpa using h⟩
  map_add' ψ χ := by
    apply Subtype.ext
    funext i'
    rfl
  map_smul' r ψ := by
    apply Subtype.ext
    funext i'
    rfl
  left_inv ψ := by
    apply Subtype.ext
    funext i
    simp
  right_inv φ := by
    apply Subtype.ext
    funext i'
    simp
  norm_map' ψ := by
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    exact Equiv.tsum_eq e.symm (fun i => ‖(ψ : ι → E) i‖ ^ p.toReal)

@[simp] theorem _root_.LinearIsometryEquiv.lpCongrLeft_apply_coe
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (e : ι ≃ ι') (ψ : lp (fun _ : ι => E) p) (i' : ι') :
    (LinearIsometryEquiv.lpCongrLeft 𝕜 hp e ψ : ι' → E) i' = ψ (e.symm i') := rfl

end lp
