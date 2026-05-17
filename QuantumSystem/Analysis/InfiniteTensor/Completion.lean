module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import QuantumSystem.Analysis.InfiniteTensor.Extension

/-!
# Hilbert completion: the incomplete infinite tensor product sector

For a Hilbert family `H : ι → Type*` (finite-dim per factor) and a
unit-vector reference family `Ω : UnitFamily H`, this file defines

```
ITPSector H Ω := UniformSpace.Completion (preITPSector Ω)
```

the Hilbert completion of the algebraic colimit of finite tensor products
linked by Ω-extension.  This is the **incomplete infinite tensor product
sector** in the Bratteli–Robinson sense (Vol. 2 §2.7.2, Naaijkens 2012
§3.5), specialised to a single `c0Equiv`-class representative.

The Mathlib `UniformSpace.Completion` machinery automatically provides:

* `NormedAddCommGroup` and `NormedSpace ℂ` (from
  `Mathlib.Analysis.Normed.Module.Completion`);
* `InnerProductSpace ℂ` (from
  `Mathlib.Analysis.InnerProductSpace.Completion`);
* `CompleteSpace` (from `Mathlib.Topology.UniformSpace.Completion`).

Together these give `ITPSector H Ω` the structure of a complex Hilbert
space.

## Main definitions

* `InfiniteTensor.UnitFamily.ITPSector Ω` — the Hilbert sector itself.
* `InfiniteTensor.UnitFamily.ITPSector.embedRegion S` — the canonical
  isometric embedding `regionTensor S → ITPSector H Ω`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical
  Mechanics II*, §2.7.2 (incomplete infinite tensor product sector).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Module _root_.PiTensorProduct

namespace InfiniteTensor

variable {ι : Type*} [DecidableEq ι] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

namespace UnitFamily

/-- The **incomplete infinite tensor product sector** of `H` selected by the
unit-vector reference family `Ω`.  It is the Hilbert completion of the
algebraic colimit `preITPSector Ω` of finite tensor products linked by
Ω-extension.

The Hilbert space structure (`NormedAddCommGroup`, `InnerProductSpace ℂ`,
`CompleteSpace`) is inherited automatically from
`UniformSpace.Completion`. -/
noncomputable def ITPSector (Ω : UnitFamily H) : Type _ :=
  UniformSpace.Completion (preITPSector Ω)

namespace ITPSector

variable (Ω : UnitFamily H)

noncomputable instance : NormedAddCommGroup (ITPSector Ω) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion _))

noncomputable instance : NormedSpace ℂ (ITPSector Ω) :=
  inferInstanceAs (NormedSpace ℂ (UniformSpace.Completion _))

noncomputable instance : InnerProductSpace ℂ (ITPSector Ω) :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion _))

instance : CompleteSpace (ITPSector Ω) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion _))

/-- Canonical isometric embedding `preITPSector Ω → ITPSector Ω` from the
algebraic colimit into its Hilbert completion. -/
noncomputable def fromPre : preITPSector Ω →ₗᵢ[ℂ] ITPSector Ω :=
  UniformSpace.Completion.toComplₗᵢ

/-- Canonical isometric embedding `regionTensor S →ₗᵢ[ℂ] preITPSector Ω`,
upgrading the linear map `preITPSector.of Ω S` using the inner-product
preservation `inner_of_of`. -/
noncomputable def fromRegion (S : Finset ι) :
    regionTensor S (H := H) →ₗᵢ[ℂ] preITPSector Ω :=
  { preITPSector.of Ω S with
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (inner_of_of Ω x x) }

/-- Canonical isometric embedding from a single finite-region tensor space
into the infinite tensor product sector, factoring through `preITPSector`. -/
noncomputable def embedRegion (S : Finset ι) :
    regionTensor S (H := H) →ₗᵢ[ℂ] ITPSector Ω :=
  (fromPre Ω).comp (fromRegion Ω S)

/-! ### Density of the colimit and finite-region images -/

/-- The image of the algebraic colimit `preITPSector Ω` is dense in
`ITPSector Ω`.  This is the Hilbert-completion density. -/
theorem denseRange_fromPre : DenseRange (fromPre (H := H) Ω) :=
  UniformSpace.Completion.denseRange_coe

/-- Every element of `preITPSector Ω` is in the range of some
`fromRegion Ω S`.  This is `Module.DirectLimit.exists_of` repackaged. -/
theorem mem_range_fromRegion (x : preITPSector Ω) :
    ∃ S : Finset ι, x ∈ Set.range (fromRegion Ω S) := by
  obtain ⟨S, x', hx⟩ := preITPSector.exists_of Ω x
  exact ⟨S, x', hx⟩

/-- The union of the images `embedRegion S` over all finite subsets `S` is
dense in `ITPSector Ω`.  This is the central density property powering all
downstream `Completion.extension`-based constructions. -/
theorem denseRange_iUnion_embedRegion :
    Dense (⋃ S : Finset ι, Set.range (embedRegion (H := H) Ω S)) := by
  -- Step 1: the image of `fromPre` is dense.
  have hdense : Dense (Set.range (fromPre (H := H) Ω)) := denseRange_fromPre Ω
  -- Step 2: the image of `fromPre` is contained in the iUnion image.
  refine hdense.mono ?_
  intro y hy
  -- y ∈ Set.range fromPre means y = fromPre x for some x : preITPSector Ω.
  obtain ⟨x, rfl⟩ := hy
  -- x is in the image of some fromRegion Ω S.
  obtain ⟨S, x', rfl⟩ := mem_range_fromRegion Ω x
  -- Hence fromPre (fromRegion S x') = embedRegion S x' ∈ ⋃.
  refine Set.mem_iUnion.mpr ⟨S, x', ?_⟩
  rfl

end ITPSector

end UnitFamily

end InfiniteTensor
