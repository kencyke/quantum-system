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
the consequences of that identification in the `lp.single` spelling, together with the dimension
count it yields: a Hilbert space is finite-dimensional exactly when its Hilbert bases are indexed
by finite types, so `ℓ²(ι, 𝕜)` is infinite-dimensional exactly when `ι` is infinite.

## Main results

* `HilbertBasis.finiteDimensional_iff_finite` — a Hilbert space with a Hilbert basis indexed by
  `ι` is finite-dimensional iff `ι` is finite.
* `lp.coe_default_hilbertBasis` — the canonical Hilbert basis of `ℓ²(ι, 𝕜)` is `lp.single 2 · 1`.
* `lp.orthonormal_single` — the standard basis vectors are orthonormal.
* `lp.dense_span_single` — the standard basis vectors span a dense subspace.
* `lp.instNontrivial` — `ℓ²(ι, 𝕜)` is nontrivial when `ι` is nonempty.
* `lp.finiteDimensional_iff_finite` — `ℓ²(ι, 𝕜)` is finite-dimensional iff `ι` is finite.
-/

@[expose] public section

open scoped ENNReal

/-- **A Hilbert space is finite-dimensional iff its Hilbert basis is finite.** A finite Hilbert
basis is an orthonormal basis (`HilbertBasis.toOrthonormalBasis`), so it spans; conversely the
basis vectors are orthonormal, hence linearly independent, hence finitely many in a
finite-dimensional space. -/
lemma HilbertBasis.finiteDimensional_iff_finite {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 E) : FiniteDimensional 𝕜 E ↔ Finite ι := by
  refine ⟨fun _ => b.orthonormal.linearIndependent.finite, fun _ => ?_⟩
  have : Fintype ι := Fintype.ofFinite ι
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

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

/-- **`ℓ²(ι, 𝕜)` is finite-dimensional iff `ι` is finite**, by
`HilbertBasis.finiteDimensional_iff_finite` for the canonical Hilbert basis. In particular `ℓ²(ι)`
is infinite-dimensional exactly when `ι` is infinite. -/
lemma finiteDimensional_iff_finite : FiniteDimensional 𝕜 ℓ²(ι, 𝕜) ↔ Finite ι :=
  (default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)).finiteDimensional_iff_finite

end lp
