/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The standard basis `lp.single 2 i 1` of `ℓ²(ι, 𝕜)`

The standard basis vectors of `ℓ²(ι, 𝕜)` are the vectors of the canonical Hilbert basis
`default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)`, whose representation is the identity. This file records
the consequences of that identification in the `lp.single` spelling.

## Main results

* `lp.coe_default_hilbertBasis` — the canonical Hilbert basis of `ℓ²(ι, 𝕜)` is `lp.single 2 · 1`.
* `lp.orthonormal_single` — the standard basis vectors are orthonormal.
* `lp.dense_span_single` — the standard basis vectors span a dense subspace.
* `lp.instNontrivial` — `ℓ²(ι, 𝕜)` is nontrivial when `ι` is nonempty.
-/

@[expose] public section

open scoped ENNReal

namespace lp

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]

/-- The canonical Hilbert basis of `ℓ²(ι, 𝕜)` is the family of standard basis vectors. -/
lemma coe_default_hilbertBasis [DecidableEq ι] :
    ⇑(default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) = fun i => lp.single 2 i (1 : 𝕜) :=
  funext fun i => ((default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)).repr_symm_single i).symm

/-- The standard basis vectors `lp.single 2 i 1` of `ℓ²(ι, 𝕜)` are orthonormal. -/
lemma orthonormal_single [DecidableEq ι] :
    Orthonormal 𝕜 (fun i : ι => lp.single (E := fun _ : ι => 𝕜) 2 i (1 : 𝕜)) := by
  rw [← coe_default_hilbertBasis]
  exact (default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)).orthonormal

/-- The standard basis vectors `lp.single 2 i 1` span a dense subspace of `ℓ²(ι, 𝕜)`. -/
lemma dense_span_single [DecidableEq ι] :
    Dense (Submodule.span 𝕜 (Set.range fun i : ι => lp.single (E := fun _ : ι => 𝕜) 2 i (1 : 𝕜)) :
      Set ℓ²(ι, 𝕜)) := by
  rw [← coe_default_hilbertBasis]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)).dense_span

/-- `ℓ²(ι, 𝕜)` is nontrivial when `ι` is nonempty: it contains a unit basis vector. -/
instance instNontrivial [Nonempty ι] : Nontrivial ℓ²(ι, 𝕜) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨⟨lp.single 2 i (1 : 𝕜), 0, fun h => by
    simpa [h] using (orthonormal_single (𝕜 := 𝕜) (ι := ι)).1 i⟩⟩

end lp
