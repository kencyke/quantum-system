module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Separability of `lp` over a countable index

An `lp` space over a **countable** index type, whose summands are separable, is separable —
provided `p ≠ ⊤`. The exponent restriction is essential: `lp G ⊤` is the space of bounded
families, which is not separable over an infinite index even when every summand is `ℂ`.

The proof is the standard one: the singles span a dense subspace, because
`lp.hasSum_single` expands every element as the sum of its coordinates, and a countable
union of continuous images of separable spaces spans a separable submodule.

Mathlib has `PiLp.secondCountableTopology` for the finite-product form and
`WithLp.secondCountableTopology` for the binary one, but nothing for the `lp` subtype; this
file supplies it.

## Main results

* `lp.separableSpace_of_ne_top` — the statement above, for an arbitrary exponent `p ≠ ⊤`.
  The scalar field is an explicit argument, since it appears only in the proof.
* `lp.instSeparableSpaceOfCountable` — the same at `p = 2` over `ℂ`, as an instance; this
  is the case the ℓ²-direct sum of complex Hilbert spaces uses.
-/

@[expose] public section

open TopologicalSpace

open scoped ENNReal

namespace lp

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]

/-- The single-coordinate embedding `G i → lp G p` is continuous.

It is in fact isometric — `lp.norm_single` — but continuity is all that is needed
downstream. The scalar field is explicit because it occurs only in the proof, which routes
through the linear map `lp.lsingle` to get additivity. -/
lemma continuous_single (𝕜 : Type*) [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (G i)]
    [DecidableEq ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : ι) :
    Continuous (fun x : G i => lp.single p i x) := by
  have hp0 : (0 : ℝ≥0∞) < p := lt_of_lt_of_le zero_lt_one Fact.out
  have h : ∀ x : G i, ‖lp.lsingle (𝕜 := 𝕜) p i x‖ = ‖x‖ := fun x => by
    simpa using lp.norm_single hp0 i x
  simpa using (AddMonoidHomClass.isometry_of_norm (lp.lsingle (𝕜 := 𝕜) p i) h).continuous

/-- An `lp` space over a countable index with separable summands is separable, for any
exponent `p ≠ ⊤`.

The hypothesis `p ≠ ⊤` cannot be dropped: `lp (fun _ : ℕ => ℂ) ⊤` is `ℓ^∞`, which is not
separable. The scalar field `𝕜` is explicit because it does not occur in the conclusion. -/
theorem separableSpace_of_ne_top (𝕜 : Type*) [NontriviallyNormedField 𝕜] [SeparableSpace 𝕜]
    [∀ i, NormedSpace 𝕜 (G i)] [Countable ι] [∀ i, SeparableSpace (G i)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SeparableSpace (lp G p) := by
  classical
  set S : Set (lp G p) := ⋃ i, Set.range (fun x : G i => lp.single p i x) with hSdef
  have hS : IsSeparable S :=
    IsSeparable.iUnion fun i => isSeparable_range (continuous_single 𝕜 i)
  have hspan : IsSeparable ((Submodule.span 𝕜 S : Submodule 𝕜 (lp G p)) : Set (lp G p)) :=
    hS.span
  -- The singles span a dense subspace: every element is the sum of its coordinates.
  have hdense : Dense ((Submodule.span 𝕜 S : Submodule 𝕜 (lp G p)) : Set (lp G p)) := by
    intro f
    refine mem_closure_of_tendsto (lp.hasSum_single hp f) ?_
    filter_upwards with s
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self _⟩
  rw [← isSeparable_univ_iff, ← hdense.closure_eq]
  exact hspan.closure

/-- The `p = 2`, `𝕜 = ℂ` case of `lp.separableSpace_of_ne_top`, as an instance.

Both the exponent and the scalar field are fixed here rather than left as variables: an
instance can carry neither the hypothesis `p ≠ ⊤` nor a scalar field absent from its
conclusion. -/
instance instSeparableSpaceOfCountable [∀ i, NormedSpace ℂ (G i)] [Countable ι]
    [∀ i, SeparableSpace (G i)] : SeparableSpace (lp G 2) :=
  separableSpace_of_ne_top ℂ (by simp)

end lp
