module

public import Mathlib.Analysis.Normed.Group.Defs

/-!
# Pure infinite tensor product layer

This file is the entry point of the **pure** infinite tensor product layer.
It is independent of any lattice, quasi-local algebra, or `LocalNetLike`
data: only a Hilbert family `H : ι → Type*` is required.  Lattice realisations
such as `LocalNetLike.siteHilbert` are introduced as inputs to this layer in
later files (Phase 5 of the migration plan), not as part of its definition.

The layer follows Bratteli–Robinson Vol. 2 §2.7.2 / Naaijkens 2012 §3.5.

## Main definitions (Phase 1)

* `InfiniteTensor.UnitFamily H` — a bundled family of unit vectors
  `Ω : (i : ι) → H i` with `‖Ω i‖ = 1` at every index.  This is the
  "reference" data parameterising an incomplete infinite tensor product
  sector.
* `InfiniteTensor.UnitFamily` is equipped with a `FunLike` instance so that
  `Ω i` denotes the underlying vector at index `i` while the bundled form is
  available for sector equivalence relations.

The incomplete sector `InfiniteTensor.ITPSector H Ω` and its Hilbert-space
structure are constructed in Phase 2 of the migration; this file only sets up
the parameter shape so that downstream signatures can already be written.

## Design

The pure layer never imports `LocalNetLike`, `Hilbert.lean`,
`GlobalHilbert.lean`, or any quasi-local algebra module.  Conversely, the
lattice modules will instantiate this layer with `H s := siteHilbert s` via
a separate bridge file.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

namespace InfiniteTensor

variable {ι : Type*}

/-- A **unit-vector family** indexed by `ι`: a function `vec : (i : ι) → H i`
together with the proof that each `vec i` is a unit vector.

This is the bundled "reference" data of an incomplete infinite tensor product
sector following Bratteli–Robinson Vol. 2 §2.7.2 / Naaijkens 2012 §3.5.  The
sector relations `referenceEquiv`, `strongEquiv`, `cEquiv`, and `c0Equiv`
defined in Phase 3 will live on this type. -/
structure UnitFamily (H : ι → Type*) [∀ i, NormedAddCommGroup (H i)] where
  /-- The underlying function picking a vector at each index. -/
  vec : (i : ι) → H i
  /-- Each picked vector is a unit vector. -/
  norm_vec : ∀ i, ‖vec i‖ = 1

namespace UnitFamily

variable {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]

/-- Apply a `UnitFamily` as a function on indices.  The dependent `DFunLike`
instance lets us write `Ω i` for the vector at index `i`. -/
instance instDFunLike : DFunLike (UnitFamily H) ι (fun i => H i) where
  coe Ω := Ω.vec
  coe_injective' := by
    intro Ω₁ Ω₂ h
    cases Ω₁; cases Ω₂
    congr

@[simp]
theorem coe_mk (vec : (i : ι) → H i) (h : ∀ i, ‖vec i‖ = 1) (i : ι) :
    (⟨vec, h⟩ : UnitFamily H) i = vec i := rfl

@[simp]
theorem norm_apply (Ω : UnitFamily H) (i : ι) : ‖(Ω i : H i)‖ = 1 :=
  Ω.norm_vec i

@[ext]
theorem ext {Ω₁ Ω₂ : UnitFamily H} (h : ∀ i, Ω₁ i = Ω₂ i) : Ω₁ = Ω₂ :=
  DFunLike.ext _ _ h

end UnitFamily

end InfiniteTensor
