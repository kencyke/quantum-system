import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

namespace NonUnitalCStarAlgebra

open Topology

variable {A : Type*} [NonUnitalCStarAlgebra A]

instance cstarPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A

instance cstarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

lemma positive_conjugate_le_norm_smul (a b : A):
    star b * star a * a * b ≤ ‖a‖ ^ 2 • (star b * b) := by
  simpa [mul_assoc, CStarRing.norm_star_mul_self, pow_two] using
    (CStarAlgebra.star_left_conjugate_le_norm_smul (A := A) (a := b) (b := star a * a))


/-- For any element in a non-unital C*-algebra with an approximate unit and any ε > 0,
there exists an approximate unit element `e` such that `‖e * x - x‖ < ε` and `‖e‖ ≤ 1`. -/
lemma exists_approxUnit_mul_close (x : A) {ε : ℝ} (hε : 0 < ε) : ∃ e : A, ‖e * x - x‖ < ε ∧ ‖e‖ ≤ 1 := by
  -- Use the increasing approximate unit tending to the identity on the right.
  have h_approx := CStarAlgebra.increasingApproximateUnit (A := A)
  have h_tendsto : Filter.Tendsto (fun e : A => e * x) (CStarAlgebra.approximateUnit A) (𝓝 x) :=
    h_approx.tendsto_mul_right x
  -- Translate the filter convergence into an ε-ball statement.
  have h_basis := CStarAlgebra.hasBasis_approximateUnit A
  have h_tendsto' := (h_basis.tendsto_iff Metric.nhds_basis_ball).1 h_tendsto
  obtain ⟨a, ha, h_ball⟩ := h_tendsto' ε hε
  rcases ha with ⟨ha_nonneg, ha_norm⟩
  -- Extract an element of the basis set with the desired properties.
  have h_nonempty : ({y : A | a ≤ y} ∩ Metric.closedBall (0 : A) 1).Nonempty := by
    use a
    constructor
    · exact le_refl a
    · simp [Metric.mem_closedBall]
      exact ha_norm.le
  obtain ⟨e, he_ge, he_norm⟩ := h_nonempty
  have h_close : ‖e * x - x‖ < ε := by
    have h_mem : e ∈ {y : A | a ≤ y} ∩ Metric.closedBall (0 : A) 1 := ⟨he_ge, he_norm⟩
    have : e * x ∈ Metric.ball x ε := h_ball e h_mem
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using this
  have h_bound : ‖e‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using he_norm
  exact ⟨e, h_close, h_bound⟩

end NonUnitalCStarAlgebra
