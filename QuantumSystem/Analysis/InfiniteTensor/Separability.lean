module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Countable.Basic
public import Mathlib.Topology.Bases
public import QuantumSystem.Analysis.InfiniteTensor.Completion
public import QuantumSystem.Analysis.InfiniteTensor.OperatorExtension

/-!
# Separability and finite-excitation API for `ITPSector`

When the index set `ι` is countable, the sector Hilbert space
`ITPSector H Ω` is separable.  This file:

* registers `TopologicalSpace.SeparableSpace` instances for
  `regionTensor S`, `preITPSector Ω`, and `ITPSector Ω`, the last
  under the assumption `[Countable ι]`;
* exposes the **finite-excitation embedding** `finiteExcitation Ω S`
  as a synonym of `ITPSector.embedRegion Ω S`, together with its
  density lemma.

The chain of arguments is:

1. each `regionTensor S` is finite-dimensional, hence separable
   (via `stdOrthonormalBasis`);
2. the isometric embedding `fromRegion Ω S : regionTensor S →ₗᵢ[ℂ]
   preITPSector Ω` has separable range; the colimit's universal
   property (`preITPSector.exists_of`) covers `preITPSector Ω` by
   these ranges, indexed by the countable type `Finset ι`;
3. `SeparableSpace` lifts to `ITPSector Ω` via
   `UniformSpace.Completion.separableSpace_completion`.
-/

@[expose] public section

open TopologicalSpace

namespace InfiniteTensor

variable {ι : Type*} [DecidableEq ι] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

namespace UnitFamily

/-- A finite-dimensional complex inner product space is separable: the
standard orthonormal basis presents it as a continuous-surjective image of
the (separable) Euclidean space `EuclideanSpace ℂ (Fin n)`. -/
private lemma separableSpace_of_finiteDim_innerProductSpace
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] : SeparableSpace E := by
  let b := stdOrthonormalBasis ℂ E
  let h := b.repr.toContinuousLinearEquiv.toHomeomorph.symm
  exact h.surjective.denseRange.separableSpace h.continuous

instance instSeparableSpaceRegionTensor (S : Finset ι) :
    SeparableSpace (regionTensor S (H := H)) :=
  separableSpace_of_finiteDim_innerProductSpace _

variable (Ω : UnitFamily H)

/-- The union of the images of all `fromRegion Ω S` covers `preITPSector Ω`.
This is `preITPSector.exists_of` re-expressed as a set equality. -/
theorem iUnion_range_fromRegion_eq_univ :
    (⋃ S : Finset ι, Set.range (ITPSector.fromRegion Ω S))
      = (Set.univ : Set (preITPSector Ω)) := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨S, y, hy⟩ := preITPSector.exists_of Ω x
  exact Set.mem_iUnion.mpr ⟨S, y, hy⟩

instance instSeparableSpacePreITPSector [Countable ι] :
    SeparableSpace (preITPSector Ω) := by
  rw [← isSeparable_univ_iff, ← iUnion_range_fromRegion_eq_univ Ω]
  refine IsSeparable.iUnion fun S => ?_
  exact isSeparable_range (ITPSector.fromRegion Ω S).continuous

instance instSeparableSpaceITPSector [Countable ι] :
    SeparableSpace (ITPSector (H := H) Ω) :=
  inferInstanceAs (SeparableSpace (UniformSpace.Completion _))

/-! ### Finite-excitation API -/

/-- The **finite-excitation embedding**: a synonym for
`ITPSector.embedRegion`, emphasising the interpretation of a
finite-region tensor as a sector vector supported on the finite region
`S`. -/
noncomputable abbrev ITPSector.finiteExcitation (S : Finset ι) :
    regionTensor S (H := H) →ₗᵢ[ℂ] ITPSector Ω :=
  ITPSector.embedRegion Ω S

/-- The union of the images `finiteExcitation Ω S` over all finite
subsets `S` is dense in `ITPSector Ω`. -/
theorem ITPSector.denseRange_iUnion_finiteExcitation :
    Dense (⋃ S : Finset ι, Set.range (ITPSector.finiteExcitation Ω S)) :=
  ITPSector.denseRange_iUnion_embedRegion Ω

end UnitFamily

end InfiniteTensor
