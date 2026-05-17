module

public import Mathlib.LinearAlgebra.PiTensorProduct
public import QuantumSystem.Analysis.InfiniteTensor.Extension

/-!
# Operator-level region extension — helper API (Step B.1)

For a Hilbert family `H : ι → Type*` (finite-dim per factor), this file
collects the helper splittings that the operator-level region extension

```
extendOpLe Ω h A : regionTensor S' →L[ℂ] regionTensor S'
```

(from a finite-region operator `A : regionTensor S →L[ℂ] regionTensor S`
along an inclusion `h : S ⊆ S'`) is built on.

The mathematical recipe `A ⊗ id_{S' \ S}` rests on the splitting

```
regionTensor S' ≃ regionTensor S ⊗ regionTensor (S' \ S)
```

which in turn comes from the subtype decomposition `↥S' ≃ ↥S ⊕ ↥(S' \ S)`
(`subsetSumEquiv`) and `PiTensorProduct.tmulEquivDep`.  `extendOpLe`
itself and its structural lemmas (`_zero`, `_add`, `_smul`, `_one`,
`_mul`, `_adjoint`, `_isotony`, `_disjoint_commute`, `_opNorm_le`)
will be supplied in the next step.
-/

@[expose] public section

open scoped TensorProduct

namespace InfiniteTensor

variable {ι : Type*} [DecidableEq ι]

namespace UnitFamily

/-- The subtype equivalence `↥S' ≃ ↥S ⊕ ↥(S' \ S)` when `S ⊆ S'`.

Index-level shape behind `regionTensor S' ≃ regionTensor S ⊗
regionTensor (S' \ S)`.  Built by transporting `Equiv.Finset.union` along
`S ∪ (S' \ S) = S'`. -/
noncomputable def subsetSumEquiv {S S' : Finset ι} (h : S ⊆ S') :
    {x // x ∈ S'} ≃ {x // x ∈ S} ⊕ {x // x ∈ S' \ S} :=
  have hunion : S ∪ (S' \ S) = S' := Finset.union_sdiff_of_subset h
  have hfeq : (fun x : ι => x ∈ S') = (fun x => x ∈ S ∪ (S' \ S)) := by
    funext x; rw [hunion]
  (Equiv.subtypeEquivProp hfeq).trans
    (Equiv.Finset.union S (S' \ S) Finset.disjoint_sdiff).symm

@[simp]
theorem subsetSumEquiv_symm_inl {S S' : Finset ι} (h : S ⊆ S')
    (s : {x // x ∈ S}) :
    (subsetSumEquiv h).symm (Sum.inl s) = ⟨s.val, h s.property⟩ :=
  Subtype.ext rfl

@[simp]
theorem subsetSumEquiv_symm_inr {S S' : Finset ι} (h : S ⊆ S')
    (s : {x // x ∈ S' \ S}) :
    (subsetSumEquiv h).symm (Sum.inr s) =
      ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩ :=
  Subtype.ext rfl

/-! ### Tensor-product splitting -/

variable {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

/-- `regionTensor S` is finite-dimensional, via the tensor basis
`Basis.piTensorProduct` over the finite-dimensional bases of each factor. -/
instance instFiniteDimensionalRegionTensor (S : Finset ι) :
    FiniteDimensional ℂ (regionTensor S (H := H)) :=
  Module.Finite.of_basis
    (Basis.piTensorProduct
      (fun i : {x // x ∈ S} => Module.finBasis ℂ (H i.val)))

/-- Tensor-product splitting `regionTensor S' ≃ₗ regionTensor S ⊗
regionTensor (S' \ S)` when `S ⊆ S'`.

The forward direction reindexes along `subsetSumEquiv h` to a
`Sum`-indexed tensor product and then applies `PiTensorProduct.tmulEquivDep`
to factor it as a binary tensor product. -/
noncomputable def regionTensorSplit {S S' : Finset ι} (h : S ⊆ S') :
    regionTensor S' (H := H) ≃ₗ[ℂ]
      regionTensor S (H := H) ⊗[ℂ] regionTensor (S' \ S) (H := H) :=
  (PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S'} => H s.val) (subsetSumEquiv h)).trans
    (PiTensorProduct.tmulEquivDep ℂ
      (fun i : {x // x ∈ S} ⊕ {x // x ∈ S' \ S} =>
        H ((subsetSumEquiv h).symm i).val)).symm

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Value of `regionTensorSplit` on an elementary tensor. -/
theorem regionTensorSplit_tprod {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S'}) → H s.val) :
    regionTensorSplit (H := H) h (PiTensorProduct.tprod ℂ ξ) =
      (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => ξ ⟨s.val, h s.property⟩)) ⊗ₜ[ℂ]
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S' \ S} =>
            ξ ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩)) := by
  unfold regionTensorSplit
  rw [LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod]
  -- Goal: (tmulEquivDep ℂ N).symm
  --         (tprod ℂ (fun i => ξ ((subsetSumEquiv h).symm i)))
  --       = tprod ℂ aS ⊗ₜ tprod ℂ aR
  -- We rewrite the LHS argument as the image of (tprod aS ⊗ₜ tprod aR) under
  -- `tmulEquivDep`, then use `LinearEquiv.symm_apply_apply`.
  set N : {x // x ∈ S} ⊕ {x // x ∈ S' \ S} → Type _ :=
    fun i => H ((subsetSumEquiv h).symm i).val with hN
  set aS : (s : {x // x ∈ S}) → N (Sum.inl s) :=
    fun s => ξ ((subsetSumEquiv h).symm (Sum.inl s))
  set aR : (s : {x // x ∈ S' \ S}) → N (Sum.inr s) :=
    fun s => ξ ((subsetSumEquiv h).symm (Sum.inr s))
  have hfun :
      (fun i : {x // x ∈ S} ⊕ {x // x ∈ S' \ S} =>
        ξ ((subsetSumEquiv h).symm i)) =
      fun i => Sum.rec aS aR i := by
    funext i
    cases i <;> rfl
  rw [hfun, ← PiTensorProduct.tmulEquivDep_apply]
  exact (PiTensorProduct.tmulEquivDep ℂ N).symm_apply_apply _

/-- Merge a tuple on `S` with a tuple on the complement `S' \ S` into a
tuple on `S'`. -/
noncomputable def mergeVec {S S' : Finset ι} (_h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val)
    (η : (s : {x // x ∈ S' \ S}) → H s.val) :
    (s' : {x // x ∈ S'}) → H s'.val :=
  fun s' =>
    if hs : s'.val ∈ S then
      ξ ⟨s'.val, hs⟩
    else
      η ⟨s'.val, Finset.mem_sdiff.mpr ⟨s'.property, hs⟩⟩

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem mergeVec_inl {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val)
    (η : (s : {x // x ∈ S' \ S}) → H s.val)
    (s : {x // x ∈ S}) :
    mergeVec (H := H) h ξ η ⟨s.val, h s.property⟩ = ξ s := by
  unfold mergeVec
  rw [dif_pos s.property]

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem mergeVec_inr {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val)
    (η : (s : {x // x ∈ S' \ S}) → H s.val)
    (s : {x // x ∈ S' \ S}) :
    mergeVec (H := H) h ξ η
        ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩ = η s := by
  unfold mergeVec
  rw [dif_neg (Finset.mem_sdiff.mp s.property).2]

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)] in
/-- The complement inclusion induced by `S ⊆ S' ⊆ S''`. -/
theorem sdiff_subset_sdiff {S S' S'' : Finset ι} (_h : S ⊆ S') (h' : S' ⊆ S'') :
    S' \ S ⊆ S'' \ S := by
  intro i hi
  exact Finset.mem_sdiff.mpr ⟨h' (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- Extending a merged tuple is the same as merging the original tuple with the
extended complement tuple. -/
theorem extendVec_mergeVec (Ω : UnitFamily H)
    {S T T' : Finset ι} (h₀ : S ⊆ T) (h : T ⊆ T')
    (ξ : (s : {x // x ∈ S}) → H s.val)
    (η : (s : {x // x ∈ T \ S}) → H s.val) :
    extendVec Ω h (mergeVec (H := H) h₀ ξ η) =
      mergeVec (H := H) (h₀.trans h) ξ
        (extendVec Ω (sdiff_subset_sdiff h₀ h) η) := by
  funext s'
  by_cases hs : s'.val ∈ S
  · simp [extendVec, mergeVec, hs, h₀ hs]
  · by_cases ht : s'.val ∈ T
    · simp [extendVec, mergeVec, hs, ht, Finset.mem_sdiff.mpr ⟨ht, hs⟩]
    · simp [extendVec, mergeVec, hs, ht]

omit [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)] in
/-- Removing `S` and then `S' \ S` from `S''` leaves the same finset as
removing `S'` directly, provided `S ⊆ S'`. -/
theorem sdiff_sdiff_sdiff_eq {S S' S'' : Finset ι} (h : S ⊆ S') :
    (S'' \ S) \ (S' \ S) = S'' \ S' := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_sdiff.mp hi with ⟨hi_left, hi_not_mid⟩
    rcases Finset.mem_sdiff.mp hi_left with ⟨hi_top, hi_not_small⟩
    refine Finset.mem_sdiff.mpr ⟨hi_top, ?_⟩
    intro hi_mid
    exact hi_not_mid (Finset.mem_sdiff.mpr ⟨hi_mid, hi_not_small⟩)
  · intro hi
    rcases Finset.mem_sdiff.mp hi with ⟨hi_top, hi_not_mid⟩
    have hi_not_small : i ∉ S := fun hi_small => hi_not_mid (h hi_small)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hi_top, hi_not_small⟩, ?_⟩
    intro hi_mid_diff
    exact hi_not_mid (Finset.mem_sdiff.mp hi_mid_diff).1

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Applying the inverse splitting to a tensor product of elementary tensors
reconstructs the merged elementary tensor on `S'`. -/
theorem regionTensorSplit_symm_tprod_tprod {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val)
    (η : (s : {x // x ∈ S' \ S}) → H s.val) :
    (regionTensorSplit (H := H) h).symm
        ((PiTensorProduct.tprod ℂ ξ) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ η)) =
      PiTensorProduct.tprod ℂ (mergeVec (H := H) h ξ η) := by
  rw [LinearEquiv.symm_apply_eq]
  rw [regionTensorSplit_tprod]
  congr
  · ext s
    simp
  · ext s
    simp


/-! ### Operator-level region extension

For `A : regionTensor S →L[ℂ] regionTensor S` and `h : S ⊆ S'`, define
`extendOpLe Ω h A : regionTensor S' →L[ℂ] regionTensor S'` by

```
extendOpLe Ω h A
  = regionTensorSplit.symm ∘L (A ⊗ id) ∘L regionTensorSplit
```

The unit-vector family `Ω` is recorded in the signature for downstream
lifts but does not enter the construction — the extension acts as
identity on the complement `S' \ S`. -/
noncomputable def extendOpLe (Ω : UnitFamily H)
    {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    regionTensor S' (H := H) →L[ℂ] regionTensor S' (H := H) :=
  let _Ω_used := Ω  -- record Ω in scope; not consumed by the construction
  let e := regionTensorSplit (H := H) h
  let actL : (regionTensor S (H := H) ⊗[ℂ] regionTensor (S' \ S) (H := H)) →ₗ[ℂ]
      (regionTensor S (H := H) ⊗[ℂ] regionTensor (S' \ S) (H := H)) :=
    TensorProduct.map A.toLinearMap LinearMap.id
  (e.symm.toLinearMap ∘ₗ actL ∘ₗ e.toLinearMap).toContinuousLinearMap

/-- Coordinate-level formula for `extendOpLe` on the underlying linear map. -/
theorem extendOpLe_apply (Ω : UnitFamily H)
    {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor S' (H := H)) :
    extendOpLe Ω h A x =
      (regionTensorSplit (H := H) h).symm
        (TensorProduct.map A.toLinearMap LinearMap.id
          (regionTensorSplit (H := H) h x)) := rfl

/-- Value of `extendOpLe` on an elementary tensor. -/
theorem extendOpLe_apply_tprod (Ω : UnitFamily H)
    {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (ξ : (s : {x // x ∈ S'}) → H s.val) :
    extendOpLe Ω h A (PiTensorProduct.tprod ℂ ξ) =
      (regionTensorSplit (H := H) h).symm
        (A (PiTensorProduct.tprod ℂ
              (fun s : {x // x ∈ S} => ξ ⟨s.val, h s.property⟩)) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ
            (fun s : {x // x ∈ S' \ S} =>
              ξ ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩)) := by
  rw [extendOpLe_apply, regionTensorSplit_tprod, TensorProduct.map_tmul]
  rfl

/-! ### Structural lemmas: zero / add / smul / one / mul -/

@[simp]
theorem extendOpLe_zero (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S') :
    extendOpLe Ω h
        (0 : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) = 0 := by
  ext x
  rw [extendOpLe_apply]
  change (regionTensorSplit h).symm
      (TensorProduct.map (0 : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H))
        LinearMap.id (regionTensorSplit h x)) = 0
  rw [TensorProduct.map_zero_left]
  simp

@[simp]
theorem extendOpLe_add (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (A B : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    extendOpLe Ω h (A + B) = extendOpLe Ω h A + extendOpLe Ω h B := by
  ext x
  simp only [extendOpLe_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_add, TensorProduct.map_add_left, LinearMap.add_apply,
    map_add]

@[simp]
theorem extendOpLe_smul (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (c : ℂ) (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    extendOpLe Ω h (c • A) = c • extendOpLe Ω h A := by
  ext x
  simp only [extendOpLe_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_smul, TensorProduct.map_smul_left, LinearMap.smul_apply,
    LinearEquiv.map_smul]

@[simp]
theorem extendOpLe_one (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S') :
    extendOpLe Ω h
        (ContinuousLinearMap.id ℂ (regionTensor S (H := H))) =
      ContinuousLinearMap.id ℂ (regionTensor S' (H := H)) := by
  ext x
  rw [extendOpLe_apply]
  change (regionTensorSplit h).symm
      (TensorProduct.map (LinearMap.id : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H))
        LinearMap.id (regionTensorSplit h x)) = x
  rw [TensorProduct.map_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

@[simp]
theorem extendOpLe_mul (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (A B : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    extendOpLe Ω h (A.comp B) =
      (extendOpLe Ω h A).comp (extendOpLe Ω h B) := by
  ext x
  simp only [extendOpLe_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.comp_apply]
  rw [LinearEquiv.apply_symm_apply]
  congr 1
  have heq : TensorProduct.map (A.toLinearMap ∘ₗ B.toLinearMap)
        (LinearMap.id : regionTensor (S' \ S) (H := H) →ₗ[ℂ] regionTensor (S' \ S) (H := H))
      = TensorProduct.map A.toLinearMap LinearMap.id
          ∘ₗ TensorProduct.map B.toLinearMap LinearMap.id := by
    have hid : (LinearMap.id : regionTensor (S' \ S) (H := H) →ₗ[ℂ] _)
        = LinearMap.id ∘ₗ LinearMap.id := (LinearMap.id_comp _).symm
    rw [hid]
    exact TensorProduct.map_comp _ _ _ _
  rw [heq]
  rfl

/-! ### Functoriality and commutation lemmas -/

/-- The iterated splitting along `S ⊆ S' ⊆ S''`, first separating `S'` from
`S''` and then separating `S` from `S'`. -/
noncomputable def regionTensorSplitIter {S S' S'' : Finset ι}
    (h : S ⊆ S') (h' : S' ⊆ S'') :
    regionTensor S'' (H := H) ≃ₗ[ℂ]
      regionTensor S (H := H) ⊗[ℂ]
        (regionTensor (S' \ S) (H := H) ⊗[ℂ]
          regionTensor (S'' \ S') (H := H)) :=
  (regionTensorSplit (H := H) h').trans
    ((TensorProduct.congr (regionTensorSplit (H := H) h)
      (LinearEquiv.refl ℂ (regionTensor (S'' \ S') (H := H)))).trans
      (TensorProduct.assoc ℂ (regionTensor S (H := H))
        (regionTensor (S' \ S) (H := H))
        (regionTensor (S'' \ S') (H := H))))

/-- Reindex the residual complement `((S'' \ S) \ (S' \ S))` as `S'' \ S'`. -/
noncomputable def regionTensorSdiffSdiffEquiv {S S' S'' : Finset ι}
    (h : S ⊆ S') :
    regionTensor ((S'' \ S) \ (S' \ S)) (H := H) ≃ₗ[ℂ]
      regionTensor (S'' \ S') (H := H) := by
  let e : {x // x ∈ (S'' \ S) \ (S' \ S)} ≃ {x // x ∈ S'' \ S'} :=
    Equiv.subtypeEquivRight fun i => by
      simp [sdiff_sdiff_sdiff_eq (S := S) (S' := S') (S'' := S'') h]
  simpa using
    (PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S'' \ S'} => H s.val) e.symm).symm

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem regionTensorSdiffSdiffEquiv_tprod {S S' S'' : Finset ι}
    (h : S ⊆ S') (ξ : (i : {x // x ∈ S''}) → H i.val) :
    regionTensorSdiffSdiffEquiv (H := H) h
      (PiTensorProduct.tprod ℂ
        (fun s : {x // x ∈ (S'' \ S) \ (S' \ S)} =>
          ξ ⟨s.val, (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp s.property).1).1⟩)) =
      PiTensorProduct.tprod ℂ
        (fun s : {x // x ∈ S'' \ S'} =>
          ξ ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩) := by
  let e : {x // x ∈ (S'' \ S) \ (S' \ S)} ≃ {x // x ∈ S'' \ S'} :=
    Equiv.subtypeEquivRight fun i => by
      simp [sdiff_sdiff_sdiff_eq (S := S) (S' := S') (S'' := S'') h]
  have hreindex :
      PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S'' \ S'} => H s.val) e.symm
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S'' \ S'} => ξ ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩)) =
      PiTensorProduct.tprod ℂ
        (fun s : {x // x ∈ (S'' \ S) \ (S' \ S)} =>
          ξ ⟨s.val, (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp s.property).1).1⟩) := by
    rw [PiTensorProduct.reindex_tprod]
    rfl
  simpa [regionTensorSdiffSdiffEquiv, e] using
    (LinearEquiv.symm_apply_eq
      (e := PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S'' \ S'} => H s.val) e.symm)).2 hreindex.symm

/-- The direct splitting along `S ⊆ S''`, followed by splitting the
complement `S'' \ S` into `(S' \ S) ∪ (S'' \ S')`. -/
noncomputable def regionTensorSplitDirect {S S' S'' : Finset ι}
    (h : S ⊆ S') (h' : S' ⊆ S'') :
    regionTensor S'' (H := H) ≃ₗ[ℂ]
      regionTensor S (H := H) ⊗[ℂ]
        (regionTensor (S' \ S) (H := H) ⊗[ℂ]
          regionTensor (S'' \ S') (H := H)) :=
  (regionTensorSplit (H := H) (h.trans h')).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ (regionTensor S (H := H)))
      ((regionTensorSplit (H := H) (sdiff_subset_sdiff h h')).trans
        (TensorProduct.congr (LinearEquiv.refl ℂ (regionTensor (S' \ S) (H := H)))
          (regionTensorSdiffSdiffEquiv (H := H) h))))

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem regionTensorSplit_compose {S S' S'' : Finset ι}
    (h : S ⊆ S') (h' : S' ⊆ S'') :
    regionTensorSplitIter (H := H) h h' = regionTensorSplitDirect (H := H) h h' := by
  ext x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
      simp [regionTensorSplitIter, regionTensorSplitDirect, LinearEquiv.trans_apply,
        regionTensorSplit_tprod, TensorProduct.congr_tmul, TensorProduct.assoc_tmul,
        regionTensorSdiffSdiffEquiv_tprod]
  | add x y hx hy =>
      simp [hx, hy]

/-- Applying `regionTensorSplit` after `extendOpLe` exposes the defining
`A ⊗ id` action. -/
theorem regionTensorSplit_extendOpLe (Ω : UnitFamily H)
    {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor S' (H := H)) :
    regionTensorSplit (H := H) h (extendOpLe Ω h A x) =
      TensorProduct.map A.toLinearMap LinearMap.id ((regionTensorSplit (H := H) h) x) := by
  rw [extendOpLe_apply, LinearEquiv.apply_symm_apply]

theorem tensorProduct_congr_refl_map_left
    {M N P : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module ℂ M] [Module ℂ N] [Module ℂ P]
    (F : N ≃ₗ[ℂ] P) (A : M →ₗ[ℂ] M) (x : M ⊗[ℂ] N) :
    (TensorProduct.congr (LinearEquiv.refl ℂ M) F)
        ((TensorProduct.map A LinearMap.id) x) =
      (TensorProduct.map A LinearMap.id)
        ((TensorProduct.congr (LinearEquiv.refl ℂ M) F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.congr_tmul, TensorProduct.map_tmul]
  | add x y hx hy => simp [hx, hy]

theorem regionTensorSplitIter_map_extendOpLe (Ω : UnitFamily H)
    {S S' T : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor S' (H := H) ⊗[ℂ] regionTensor T (H := H)) :
    (TensorProduct.assoc ℂ (regionTensor S (H := H)) (regionTensor (S' \ S) (H := H))
        (regionTensor T (H := H)))
      ((TensorProduct.congr (regionTensorSplit (H := H) h)
          (LinearEquiv.refl ℂ (regionTensor T (H := H))))
        ((TensorProduct.map (extendOpLe Ω h A).toLinearMap LinearMap.id) x)) =
    (TensorProduct.map A.toLinearMap LinearMap.id)
      ((TensorProduct.assoc ℂ (regionTensor S (H := H)) (regionTensor (S' \ S) (H := H))
          (regionTensor T (H := H)))
        ((TensorProduct.congr (regionTensorSplit (H := H) h)
            (LinearEquiv.refl ℂ (regionTensor T (H := H)))) x)) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul y z =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r ξ =>
            calc
              (TensorProduct.assoc ℂ (regionTensor S (H := H))
                  (regionTensor (S' \ S) (H := H)) (regionTensor T (H := H)))
                  ((TensorProduct.congr (regionTensorSplit (H := H) h)
                      (LinearEquiv.refl ℂ (regionTensor T (H := H))))
                    ((TensorProduct.map (↑(Ω.extendOpLe h A)) LinearMap.id)
                      ((r • (PiTensorProduct.tprod ℂ) ξ) ⊗ₜ[ℂ] z)))
                  = r •
                      (TensorProduct.assoc ℂ (regionTensor S (H := H))
                        (regionTensor (S' \ S) (H := H)) (regionTensor T (H := H)))
                        ((TensorProduct.congr (regionTensorSplit (H := H) h)
                            (LinearEquiv.refl ℂ (regionTensor T (H := H))))
                          ((TensorProduct.map (↑(Ω.extendOpLe h A)) LinearMap.id)
                            ((PiTensorProduct.tprod ℂ) ξ ⊗ₜ[ℂ] z))) := by
                    rw [TensorProduct.map_tmul]
                    rw [map_smul]
                    rw [TensorProduct.congr_tmul]
                    rw [map_smul]
                    rw [← TensorProduct.smul_tmul']
                    rw [map_smul]
                    refine congrArg
                      (fun u : regionTensor S (H := H) ⊗[ℂ]
                          (regionTensor (S' \ S) (H := H) ⊗[ℂ]
                            regionTensor T (H := H)) =>
                        r • u) ?_
                    simp [TensorProduct.congr_tmul, TensorProduct.map_tmul]
              _ = r •
                    (TensorProduct.map (↑A) LinearMap.id)
                      ((TensorProduct.assoc ℂ (regionTensor S (H := H))
                          (regionTensor (S' \ S) (H := H)) (regionTensor T (H := H)))
                        ((TensorProduct.congr (regionTensorSplit (H := H) h)
                            (LinearEquiv.refl ℂ (regionTensor T (H := H))))
                          ((PiTensorProduct.tprod ℂ) ξ ⊗ₜ[ℂ] z))) := by
                    refine congrArg
                      (fun u : regionTensor S (H := H) ⊗[ℂ]
                          (regionTensor (S' \ S) (H := H) ⊗[ℂ]
                            regionTensor T (H := H)) =>
                        r • u) ?_
                    simp [regionTensorSplit_extendOpLe, regionTensorSplit_tprod,
                      TensorProduct.congr_tmul, TensorProduct.assoc_tmul,
                      TensorProduct.map_tmul]
              _ = (TensorProduct.map (↑A) LinearMap.id)
                    ((TensorProduct.assoc ℂ (regionTensor S (H := H))
                        (regionTensor (S' \ S) (H := H)) (regionTensor T (H := H)))
                      ((TensorProduct.congr (regionTensorSplit (H := H) h)
                          (LinearEquiv.refl ℂ (regionTensor T (H := H))))
                        ((r • (PiTensorProduct.tprod ℂ) ξ) ⊗ₜ[ℂ] z))) := by
                    rw [← map_smul]
                    simp [regionTensorSplit_tprod, TensorProduct.congr_tmul,
                      TensorProduct.assoc_tmul, TensorProduct.map_tmul,
                      TensorProduct.smul_tmul']
        | add y₁ y₂ ih₁ ih₂ =>
            simpa [TensorProduct.add_tmul, map_add] using congrArg₂ HAdd.hAdd ih₁ ih₂
    | add x y hx hy => simp [hx, hy]

/-- `extendOpLe` is functorial along nested finite-set inclusions. -/
theorem extendOpLe_trans (Ω : UnitFamily H) {S S' S'' : Finset ι}
    (h : S ⊆ S') (h' : S' ⊆ S'')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    extendOpLe Ω (h.trans h') A = extendOpLe Ω h' (extendOpLe Ω h A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (regionTensorSplitIter (H := H) h h').injective
  calc
    regionTensorSplitIter (H := H) h h' (extendOpLe Ω (h.trans h') A x)
      = (TensorProduct.map A.toLinearMap LinearMap.id)
          (regionTensorSplitIter (H := H) h h' x) := by
          have hstart :
              regionTensorSplitIter (H := H) h h' (extendOpLe Ω (h.trans h') A x) =
                (TensorProduct.congr (LinearEquiv.refl ℂ (regionTensor S (H := H)))
                  ((regionTensorSplit (H := H) (sdiff_subset_sdiff h h')) ≪≫ₗ
                    TensorProduct.congr
                      (LinearEquiv.refl ℂ (regionTensor (S' \ S) (H := H)))
                      (regionTensorSdiffSdiffEquiv (H := H) (S'' := S'') h)))
                  ((TensorProduct.map A.toLinearMap LinearMap.id)
                    ((regionTensorSplit (H := H) (h.trans h')) x)) := by
            rw [regionTensorSplit_compose (H := H) h h']
            simp [regionTensorSplitDirect, regionTensorSplit_extendOpLe, LinearEquiv.trans_apply]
          have hcomm := tensorProduct_congr_refl_map_left
            (F := (regionTensorSplit (H := H) (sdiff_subset_sdiff h h')) ≪≫ₗ
              TensorProduct.congr (LinearEquiv.refl ℂ (regionTensor (S' \ S) (H := H)))
                (regionTensorSdiffSdiffEquiv (H := H) (S'' := S'') h))
            (A := A.toLinearMap)
            (x := regionTensorSplit (H := H) (h.trans h') x)
          exact hstart.trans <| hcomm.trans <| by
            simpa [regionTensorSplitDirect, LinearEquiv.trans_apply] using
              congrArg (TensorProduct.map A.toLinearMap LinearMap.id)
              (LinearEquiv.congr_fun (regionTensorSplit_compose (H := H) h h') x).symm
    _ = regionTensorSplitIter (H := H) h h' (extendOpLe Ω h' (extendOpLe Ω h A) x) := by
          symm
          simp [regionTensorSplitIter, LinearEquiv.trans_apply,
            regionTensorSplit_extendOpLe, regionTensorSplitIter_map_extendOpLe]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Extending after re-merging the split tensor equals re-merging after
extending the complementary factor. -/
theorem regionEmbedLe_regionTensorSplit_symm (Ω : UnitFamily H)
    {S T T' : Finset ι} (h₀ : S ⊆ T) (h : T ⊆ T') :
    (regionEmbedLe Ω h).comp ((regionTensorSplit (H := H) h₀).symm.toLinearMap) =
      ((regionTensorSplit (H := H) (h₀.trans h)).symm.toLinearMap).comp
        (TensorProduct.map
          (LinearMap.id : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H))
          (regionEmbedLe Ω (sdiff_subset_sdiff h₀ h))) := by
  apply TensorProduct.ext'
  intro y z
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
      induction z using PiTensorProduct.induction_on with
      | smul_tprod r' η =>
          rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
          simp [regionEmbedLe_tprod, regionTensorSplit_symm_tprod_tprod, extendVec_mergeVec]
      | add z₁ z₂ ih₁ ih₂ =>
        simpa [TensorProduct.tmul_add, LinearMap.comp_apply, map_add] using
        congrArg₂ HAdd.hAdd ih₁ ih₂
  | add y₁ y₂ ih₁ ih₂ =>
      simpa [TensorProduct.add_tmul, LinearMap.comp_apply, map_add] using
      congrArg₂ HAdd.hAdd ih₁ ih₂

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Splitting after `regionEmbedLe` amounts to splitting first and then
extending only the complementary factor. -/
theorem regionTensorSplit_regionEmbedLe (Ω : UnitFamily H)
    {S T T' : Finset ι} (h₀ : S ⊆ T) (h : T ⊆ T') :
    ((regionTensorSplit (H := H) (h₀.trans h)).toLinearMap).comp (regionEmbedLe Ω h) =
      (TensorProduct.map
          (LinearMap.id : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H))
          (regionEmbedLe Ω (sdiff_subset_sdiff h₀ h))).comp
        ((regionTensorSplit (H := H) h₀).toLinearMap) := by
  have hcomm := regionEmbedLe_regionTensorSplit_symm (H := H) Ω h₀ h
  apply LinearMap.ext
  intro x
  have := congrArg
      (fun y => (regionTensorSplit (H := H) (h₀.trans h)) y)
      (LinearMap.congr_fun hcomm ((regionTensorSplit (H := H) h₀) x))
  simpa using this

/-- `regionEmbedLe` commutes with operator extension along nested inclusions. -/
theorem extendOpLe_regionEmbedLe_commute (Ω : UnitFamily H)
    {S T T' : Finset ι} (h₀ : S ⊆ T) (h : T ⊆ T')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    regionEmbedLe Ω h ∘ₗ (extendOpLe Ω h₀ A).toLinearMap =
      (extendOpLe Ω (h₀.trans h) A).toLinearMap ∘ₗ regionEmbedLe Ω h := by
  apply LinearMap.ext
  intro x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    simp [LinearMap.comp_apply, extendOpLe_apply_tprod, regionEmbedLe_tprod]
    have hleft :
        (fun s : {x // x ∈ S} => ξ ⟨s.val, h₀ s.property⟩) =
          fun s : {x // x ∈ S} => Ω.extendVec h ξ ⟨s.val, (h₀.trans h) s.property⟩ := by
      funext s
      simp [extendVec, h₀ s.property]
    have hright_fun :
        Ω.extendVec (sdiff_subset_sdiff h₀ h)
          (fun s : {x // x ∈ T \ S} => ξ ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩) =
          fun s : {x // x ∈ T' \ S} => if hs : s.val ∈ T then ξ ⟨s.val, hs⟩ else Ω s.val := by
      funext s
      by_cases hs : s.val ∈ T
      · simp [extendVec, hs, (Finset.mem_sdiff.mp s.property).2]
      · simp [extendVec, hs]
    have hright :
        PiTensorProduct.tprod ℂ
          (Ω.extendVec (sdiff_subset_sdiff h₀ h)
            (fun s : {x // x ∈ T \ S} => ξ ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩)) =
          PiTensorProduct.tprod ℂ
            (fun s : {x // x ∈ T' \ S} => if hs : s.val ∈ T then ξ ⟨s.val, hs⟩ else Ω s.val) := by
      simpa using congrArg (PiTensorProduct.tprod ℂ) hright_fun
    have hsplit := LinearMap.congr_fun
      (regionEmbedLe_regionTensorSplit_symm (H := H) Ω h₀ h)
      (A (PiTensorProduct.tprod ℂ (fun s : {x // x ∈ S} => ξ ⟨s.val, h₀ s.property⟩)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ T \ S} => ξ ⟨s.val, (Finset.mem_sdiff.mp s.property).1⟩))
    simpa [regionEmbedLe_tprod, extendVec, hleft, hright] using
      congrArg (fun z => r • z) hsplit
  | add x y hx hy =>
    simpa [LinearMap.comp_apply, map_add] using congrArg₂ HAdd.hAdd hx hy

/-! ### Disjoint commutation -/

theorem disjointUnionSdiffRightProp {S S' : Finset ι} (hd : Disjoint S S') :
    (fun x : ι => x ∈ (S ∪ S') \ S) = fun x => x ∈ S' := by
  funext x
  apply propext
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_union, hx_not_mem⟩
    rcases Finset.mem_union.mp hx_union with hxS | hxS'
    · exact False.elim (hx_not_mem hxS)
    · exact hxS'
  · intro hxS'
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hxS'),
      fun hxS => (Finset.disjoint_left.mp hd) hxS hxS'⟩

theorem disjointUnionSdiffLeftProp {S S' : Finset ι} (hd : Disjoint S S') :
    (fun x : ι => x ∈ (S ∪ S') \ S') = fun x => x ∈ S := by
  funext x
  apply propext
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_union, hx_not_mem⟩
    rcases Finset.mem_union.mp hx_union with hxS | hxS'
    · exact hxS
    · exact False.elim (hx_not_mem hxS')
  · intro hxS
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl hxS),
      fun hxS' => (Finset.disjoint_left.mp hd) hxS hxS'⟩

/-- The complement of `S` in the disjoint union `S ∪ S'` reindexes to `S'`. -/
noncomputable def disjointUnionSdiffRightEquiv {S S' : Finset ι} (hd : Disjoint S S') :
    {x // x ∈ (S ∪ S') \ S} ≃ {x // x ∈ S'} :=
  Equiv.subtypeEquivProp (disjointUnionSdiffRightProp (S := S) (S' := S') hd)

/-- The complement of `S'` in the disjoint union `S ∪ S'` reindexes to `S`. -/
noncomputable def disjointUnionSdiffLeftEquiv {S S' : Finset ι} (hd : Disjoint S S') :
    {x // x ∈ (S ∪ S') \ S'} ≃ {x // x ∈ S} :=
  Equiv.subtypeEquivProp (disjointUnionSdiffLeftProp (S := S) (S' := S') hd)

@[simp]
theorem disjointUnionSdiffRightEquiv_symm_apply {S S' : Finset ι} (hd : Disjoint S S')
    (s : {x // x ∈ S'}) :
    (disjointUnionSdiffRightEquiv (S := S) (S' := S') hd).symm s =
      ⟨s.val, Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr s.property),
        fun hs => (Finset.disjoint_left.mp hd) hs s.property⟩⟩ :=
  Subtype.ext rfl

@[simp]
theorem disjointUnionSdiffLeftEquiv_symm_apply {S S' : Finset ι} (hd : Disjoint S S')
    (s : {x // x ∈ S}) :
    (disjointUnionSdiffLeftEquiv (S := S) (S' := S') hd).symm s =
      ⟨s.val, Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inl s.property),
        fun hs' => (Finset.disjoint_left.mp hd) s.property hs'⟩⟩ :=
  Subtype.ext rfl

/-- The residual factor `((S ∪ S') \ S)` identified with `S'` for disjoint unions. -/
noncomputable def regionTensorDisjointRightEquiv {S S' : Finset ι} (hd : Disjoint S S') :
    regionTensor ((S ∪ S') \ S) (H := H) ≃ₗ[ℂ] regionTensor S' (H := H) := by
  let e : {x // x ∈ (S ∪ S') \ S} ≃ {x // x ∈ S'} :=
    disjointUnionSdiffRightEquiv (S := S) (S' := S') hd
  simpa [e] using
    (PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S'} => H s.val) e.symm).symm

/-- The residual factor `((S ∪ S') \ S')` identified with `S` for disjoint unions. -/
noncomputable def regionTensorDisjointLeftEquiv {S S' : Finset ι} (hd : Disjoint S S') :
    regionTensor ((S ∪ S') \ S') (H := H) ≃ₗ[ℂ] regionTensor S (H := H) := by
  let e : {x // x ∈ (S ∪ S') \ S'} ≃ {x // x ∈ S} :=
    disjointUnionSdiffLeftEquiv (S := S) (S' := S') hd
  simpa [e] using
    (PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S} => H s.val) e.symm).symm

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem regionTensorDisjointRightEquiv_tprod {S S' : Finset ι} (hd : Disjoint S S')
    (η : (s : {x // x ∈ (S ∪ S') \ S}) → H s.val) :
    regionTensorDisjointRightEquiv (H := H) (S := S) (S' := S') hd
      (PiTensorProduct.tprod ℂ η) =
      PiTensorProduct.tprod ℂ
        (fun s : {x // x ∈ S'} =>
          η ((disjointUnionSdiffRightEquiv (S := S) (S' := S') hd).symm s)) := by
  let e : {x // x ∈ (S ∪ S') \ S} ≃ {x // x ∈ S'} :=
    disjointUnionSdiffRightEquiv (S := S) (S' := S') hd
  let η' : (s : {x // x ∈ S'}) → H s.val := fun s => η (e.symm s)
  have hreindex :
      PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S'} => H s.val) e.symm
        (PiTensorProduct.tprod ℂ η') =
      PiTensorProduct.tprod ℂ η := by
    rw [PiTensorProduct.reindex_tprod]
    congr
  simpa [regionTensorDisjointRightEquiv, e, η'] using
    (LinearEquiv.symm_apply_eq
      (e := PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S'} => H s.val) e.symm)).2
      hreindex.symm

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem regionTensorDisjointLeftEquiv_tprod {S S' : Finset ι} (hd : Disjoint S S')
    (η : (s : {x // x ∈ (S ∪ S') \ S'}) → H s.val) :
    regionTensorDisjointLeftEquiv (H := H) (S := S) (S' := S') hd
      (PiTensorProduct.tprod ℂ η) =
      PiTensorProduct.tprod ℂ
        (fun s : {x // x ∈ S} =>
          η ((disjointUnionSdiffLeftEquiv (S := S) (S' := S') hd).symm s)) := by
  let e : {x // x ∈ (S ∪ S') \ S'} ≃ {x // x ∈ S} :=
    disjointUnionSdiffLeftEquiv (S := S) (S' := S') hd
  let η' : (s : {x // x ∈ S}) → H s.val := fun s => η (e.symm s)
  have hreindex :
      PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S} => H s.val) e.symm
        (PiTensorProduct.tprod ℂ η') =
      PiTensorProduct.tprod ℂ η := by
    rw [PiTensorProduct.reindex_tprod]
    congr
  simpa [regionTensorDisjointLeftEquiv, e, η'] using
    (LinearEquiv.symm_apply_eq
      (e := PiTensorProduct.reindex ℂ (fun s : {x // x ∈ S} => H s.val) e.symm)).2
      hreindex.symm

/-- The disjoint-union splitting ordered as `S ⊗ S'`. -/
noncomputable def regionTensorSplitDisjointLeft {S S' : Finset ι} (hd : Disjoint S S') :
    regionTensor (S ∪ S') (H := H) ≃ₗ[ℂ]
      regionTensor S (H := H) ⊗[ℂ] regionTensor S' (H := H) :=
  (regionTensorSplit (H := H) (Finset.subset_union_left : S ⊆ S ∪ S')).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ (regionTensor S (H := H)))
      (regionTensorDisjointRightEquiv (H := H) hd))

/-- The disjoint-union splitting ordered as `S' ⊗ S`. -/
noncomputable def regionTensorSplitDisjointRight {S S' : Finset ι} (hd : Disjoint S S') :
    regionTensor (S ∪ S') (H := H) ≃ₗ[ℂ]
      regionTensor S' (H := H) ⊗[ℂ] regionTensor S (H := H) :=
  (regionTensorSplit (H := H) (Finset.subset_union_right : S' ⊆ S ∪ S')).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ (regionTensor S' (H := H)))
      (regionTensorDisjointLeftEquiv (H := H) hd))

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem regionTensorSplitDisjointLeft_tprod {S S' : Finset ι} (hd : Disjoint S S')
    (ξ : (s : {x // x ∈ S ∪ S'}) → H s.val) :
    regionTensorSplitDisjointLeft (H := H) hd (PiTensorProduct.tprod ℂ ξ) =
      (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => ξ ⟨s.val, Finset.mem_union.mpr (Or.inl s.property)⟩)) ⊗ₜ[ℂ]
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S'} => ξ ⟨s.val, Finset.mem_union.mpr (Or.inr s.property)⟩)) := by
  unfold regionTensorSplitDisjointLeft
  rw [LinearEquiv.trans_apply, regionTensorSplit_tprod, TensorProduct.congr_tmul,
    regionTensorDisjointRightEquiv_tprod]
  congr 1

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem regionTensorSplitDisjointRight_tprod {S S' : Finset ι} (hd : Disjoint S S')
    (ξ : (s : {x // x ∈ S ∪ S'}) → H s.val) :
    regionTensorSplitDisjointRight (H := H) hd (PiTensorProduct.tprod ℂ ξ) =
      (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S'} => ξ ⟨s.val, Finset.mem_union.mpr (Or.inr s.property)⟩)) ⊗ₜ[ℂ]
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => ξ ⟨s.val, Finset.mem_union.mpr (Or.inl s.property)⟩)) := by
  unfold regionTensorSplitDisjointRight
  rw [LinearEquiv.trans_apply, regionTensorSplit_tprod, TensorProduct.congr_tmul,
    regionTensorDisjointLeftEquiv_tprod]
  congr 1

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem regionTensorSplitDisjointLeft_eq_right_comm {S S' : Finset ι}
    (hd : Disjoint S S') :
    regionTensorSplitDisjointLeft (H := H) hd =
      (regionTensorSplitDisjointRight (H := H) hd).trans
        (TensorProduct.comm ℂ (regionTensor S' (H := H)) (regionTensor S (H := H))) := by
  ext x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
      simp [regionTensorSplitDisjointLeft_tprod, regionTensorSplitDisjointRight_tprod,
        LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp [hx, hy]

theorem tensorProduct_comm_map
    {M M' N N' : Type*}
    [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module ℂ M] [Module ℂ M'] [Module ℂ N] [Module ℂ N']
    (f : M →ₗ[ℂ] M') (g : N →ₗ[ℂ] N') (x : M ⊗[ℂ] N) :
    (TensorProduct.comm ℂ M' N') ((TensorProduct.map f g) x) =
      (TensorProduct.map g f) ((TensorProduct.comm ℂ M N) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
  | add x y hx hy => simp [hx, hy]

theorem tensorMap_id_eq_rTensor_lm_aux
    {E K : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup K] [Module ℂ K]
    (A : E →ₗ[ℂ] E) :
    (TensorProduct.map A (LinearMap.id : K →ₗ[ℂ] K) :
        E ⊗[ℂ] K →ₗ[ℂ] E ⊗[ℂ] K) =
      LinearMap.rTensor K A := by
  ext x y
  simp [LinearMap.rTensor_tmul, TensorProduct.map_tmul]

theorem tensorMap_id_eq_lTensor_lm_aux
    {E K : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup K] [Module ℂ K]
    (A : K →ₗ[ℂ] K) :
    (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) A :
        E ⊗[ℂ] K →ₗ[ℂ] E ⊗[ℂ] K) =
      LinearMap.lTensor E A := by
  ext x y
  simp [LinearMap.lTensor_tmul, TensorProduct.map_tmul]

theorem regionTensorSplitDisjointLeft_extendOpLe_left (Ω : UnitFamily H)
    {S S' : Finset ι} (hd : Disjoint S S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor (S ∪ S') (H := H)) :
    regionTensorSplitDisjointLeft (H := H) hd
      (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ S') A x) =
      (TensorProduct.map A.toLinearMap
        (LinearMap.id : regionTensor S' (H := H) →ₗ[ℂ] regionTensor S' (H := H)))
        (regionTensorSplitDisjointLeft (H := H) hd x) := by
  unfold regionTensorSplitDisjointLeft
  rw [LinearEquiv.trans_apply, regionTensorSplit_extendOpLe]
  exact tensorProduct_congr_refl_map_left
    (F := regionTensorDisjointRightEquiv (H := H) hd)
    (A := A.toLinearMap)
    (x := regionTensorSplit (H := H) (Finset.subset_union_left : S ⊆ S ∪ S') x)

theorem regionTensorSplitDisjointRight_extendOpLe_right (Ω : UnitFamily H)
    {S S' : Finset ι} (hd : Disjoint S S')
    (B : regionTensor S' (H := H) →L[ℂ] regionTensor S' (H := H))
    (x : regionTensor (S ∪ S') (H := H)) :
    regionTensorSplitDisjointRight (H := H) hd
      (extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B x) =
      (TensorProduct.map B.toLinearMap
        (LinearMap.id : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H)))
        (regionTensorSplitDisjointRight (H := H) hd x) := by
  unfold regionTensorSplitDisjointRight
  rw [LinearEquiv.trans_apply, regionTensorSplit_extendOpLe]
  exact tensorProduct_congr_refl_map_left
    (F := regionTensorDisjointLeftEquiv (H := H) hd)
    (A := B.toLinearMap)
    (x := regionTensorSplit (H := H) (Finset.subset_union_right : S' ⊆ S ∪ S') x)

theorem regionTensorSplitDisjointLeft_extendOpLe_right (Ω : UnitFamily H)
    {S S' : Finset ι} (hd : Disjoint S S')
    (B : regionTensor S' (H := H) →L[ℂ] regionTensor S' (H := H))
    (x : regionTensor (S ∪ S') (H := H)) :
    regionTensorSplitDisjointLeft (H := H) hd
      (extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B x) =
      (TensorProduct.map
        (LinearMap.id : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H))
        B.toLinearMap)
        (regionTensorSplitDisjointLeft (H := H) hd x) := by
  rw [regionTensorSplitDisjointLeft_eq_right_comm, LinearEquiv.trans_apply,
    regionTensorSplitDisjointRight_extendOpLe_right]
  simpa [regionTensorSplitDisjointLeft_eq_right_comm, LinearEquiv.trans_apply] using
    tensorProduct_comm_map
      (f := B.toLinearMap)
      (g := (LinearMap.id : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H)))
      (x := regionTensorSplitDisjointRight (H := H) hd x)

/-- Local operators on disjoint finite regions commute after extension to the union. -/
theorem extendOpLe_disjoint_commute (Ω : UnitFamily H)
    {S S' : Finset ι} (hd : Disjoint S S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (B : regionTensor S' (H := H) →L[ℂ] regionTensor S' (H := H)) :
    (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ S') A).comp
      (extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B) =
    (extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B).comp
      (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ S') A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (regionTensorSplitDisjointLeft (H := H) hd).injective
  have hr :
      (TensorProduct.map A.toLinearMap
        (LinearMap.id : regionTensor S' (H := H) →ₗ[ℂ] regionTensor S' (H := H)) :
          regionTensor S (H := H) ⊗[ℂ] regionTensor S' (H := H) →ₗ[ℂ]
            regionTensor S (H := H) ⊗[ℂ] regionTensor S' (H := H)) =
        LinearMap.rTensor (regionTensor S' (H := H)) A.toLinearMap :=
    tensorMap_id_eq_rTensor_lm_aux A.toLinearMap
  have hl :
      (TensorProduct.map
        (LinearMap.id : regionTensor S (H := H) →ₗ[ℂ] regionTensor S (H := H))
        B.toLinearMap :
          regionTensor S (H := H) ⊗[ℂ] regionTensor S' (H := H) →ₗ[ℂ]
            regionTensor S (H := H) ⊗[ℂ] regionTensor S' (H := H)) =
        LinearMap.lTensor (regionTensor S (H := H)) B.toLinearMap :=
    tensorMap_id_eq_lTensor_lm_aux B.toLinearMap
  have hleft :
      regionTensorSplitDisjointLeft (H := H) hd
        (((extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ S') A).comp
          (extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B)) x) =
      TensorProduct.map A.toLinearMap B.toLinearMap
        (regionTensorSplitDisjointLeft (H := H) hd x) := by
    rw [ContinuousLinearMap.comp_apply, regionTensorSplitDisjointLeft_extendOpLe_left,
      regionTensorSplitDisjointLeft_extendOpLe_right]
    rw [← LinearMap.comp_apply, hr, hl, LinearMap.rTensor_comp_lTensor]
  have hright :
      regionTensorSplitDisjointLeft (H := H) hd
        (((extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B).comp
          (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ S') A)) x) =
      TensorProduct.map A.toLinearMap B.toLinearMap
        (regionTensorSplitDisjointLeft (H := H) hd x) := by
    rw [ContinuousLinearMap.comp_apply, regionTensorSplitDisjointLeft_extendOpLe_right,
      regionTensorSplitDisjointLeft_extendOpLe_left]
    rw [← LinearMap.comp_apply, hl, hr, LinearMap.lTensor_comp_rTensor]
  exact hleft.trans hright.symm

end UnitFamily

end InfiniteTensor
