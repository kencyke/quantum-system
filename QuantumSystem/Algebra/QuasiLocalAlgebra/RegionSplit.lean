module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Hilbert

/-!
# Basis-index decomposition for finite regions

For a pair of finite regions `Λ ⊆ Λ'`, the basis-index type `regionIdx Λ'`
decomposes as a product

`regionIdx Λ' ≃ regionIdx Λ × regionIdx (Λ' \ Λ)`,

reflecting the fact that an assignment of local-basis indices on `Λ'` is the
same data as a pair of assignments on `Λ` and on `Λ' \ Λ`.

This is the Type-level building block for the corresponding finite-region
Hilbert-space tensor decomposition
`regionHilbert Λ' ≃ regionHilbert Λ ⊗_ℂ regionHilbert (Λ' \ Λ)`,
which underlies the construction of "operator `M ⊗ 1_{Λ' \ Λ}`" actions
needed for an operator-algebra action on the incomplete-tensor-product
sectors at arbitrary unit-vector reference families.

## Main definitions

* `LocalNetLike.regionIdxSplit h` — split a region tuple over `Λ'` into its
  `Λ`-part and `Λ' \ Λ`-part.
* `LocalNetLike.regionIdxCombine h` — recombine a pair of `Λ` and `Λ' \ Λ`
  tuples into a `Λ'` tuple.
* `LocalNetLike.regionIdxEquiv h` — the resulting `Equiv`.
* `LocalNetLike.regionHilbertSplitEquiv h` — the corresponding linear
  isometry equivalence
  `regionHilbert Λ' ≃ₗᵢ[ℂ] EuclideanSpace ℂ (regionIdx Λ × regionIdx (Λ'\Λ))`.
* `LocalNetLike.tensorWithId h M` — the operator on `regionHilbert Λ'`
  realising `M ⊗ 1_{Λ'\Λ}` in the basis-relabelled split, with operator-norm
  bound `‖tensorWithId h M‖ ≤ ‖M‖`.
-/

@[expose] public section

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

/-- Forward direction of the basis-index decomposition: split a tuple on
`Λ'` into its `Λ`-part and `Λ' \ Λ`-part. -/
def regionIdxSplit {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ') :
    regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ) :=
  (fun s : Λ => f ⟨s.1, h s.2⟩,
   fun s : (Λ' \ Λ : Finset L) => f ⟨s.1, (Finset.mem_sdiff.mp s.2).1⟩)

/-- Inverse direction: combine a pair of `Λ` and `Λ' \ Λ` tuples into a
single `Λ'` tuple. -/
noncomputable def regionIdxCombine {Λ Λ' : Finset L} (_h : Λ ⊆ Λ')
    (g : regionIdx (L := L) Λ) (g' : regionIdx (L := L) (Λ' \ Λ)) :
    regionIdx (L := L) Λ' :=
  fun s : Λ' =>
    if hs : s.1 ∈ Λ then g ⟨s.1, hs⟩
    else g' ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, hs⟩⟩

@[simp]
theorem regionIdxCombine_of_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (g : regionIdx (L := L) Λ) (g' : regionIdx (L := L) (Λ' \ Λ))
    {s : Λ'} (hs : s.1 ∈ Λ) :
    regionIdxCombine h g g' s = g ⟨s.1, hs⟩ :=
  dif_pos hs

@[simp]
theorem regionIdxCombine_of_not_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (g : regionIdx (L := L) Λ) (g' : regionIdx (L := L) (Λ' \ Λ))
    {s : Λ'} (hs : s.1 ∉ Λ) :
    regionIdxCombine h g g' s
      = g' ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, hs⟩⟩ :=
  dif_neg hs

/-- The basis-index decomposition is an equivalence of types. -/
noncomputable def regionIdxEquiv {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    regionIdx (L := L) Λ' ≃ (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) where
  toFun := regionIdxSplit h
  invFun p := regionIdxCombine h p.1 p.2
  left_inv f := by
    funext s
    change regionIdxCombine h (regionIdxSplit h f).1 (regionIdxSplit h f).2 s = f s
    by_cases hs : s.1 ∈ Λ
    · rw [regionIdxCombine_of_mem h _ _ hs]
      rfl
    · rw [regionIdxCombine_of_not_mem h _ _ hs]
      rfl
  right_inv p := by
    obtain ⟨g, g'⟩ := p
    ext s
    · change regionIdxCombine h g g' ⟨s.1, h s.2⟩ = g s
      rw [regionIdxCombine_of_mem h _ _ s.2]
    · change regionIdxCombine h g g' ⟨s.1, (Finset.mem_sdiff.mp s.2).1⟩ = g' s
      rw [regionIdxCombine_of_not_mem h _ _ (Finset.mem_sdiff.mp s.2).2]

@[simp]
theorem regionIdxEquiv_apply {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ') :
    regionIdxEquiv h f = regionIdxSplit h f := rfl

@[simp]
theorem regionIdxEquiv_symm_apply {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (p : regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) :
    (regionIdxEquiv h).symm p = regionIdxCombine h p.1 p.2 := rfl

/-! ### Hilbert-space relabelling -/

/-- The corresponding `regionHilbert` relabelling: lifting the basis-index
decomposition `regionIdx Λ' ≃ regionIdx Λ × regionIdx (Λ' \ Λ)` to a linear
isometric equivalence of Hilbert spaces

`regionHilbert Λ' ≃ₗᵢ[ℂ] EuclideanSpace ℂ (regionIdx Λ × regionIdx (Λ' \ Λ))`.

This is the basis-relabelled form of the tensor decomposition
`regionHilbert Λ' ≃ₗᵢ[ℂ] regionHilbert Λ ⊗_ℂ regionHilbert (Λ' \ Λ)`
under `EuclideanSpace ℂ ι × EuclideanSpace ℂ κ ≃ EuclideanSpace ℂ (ι × κ)`. -/
noncomputable def regionHilbertSplitEquiv {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    regionHilbert (L := L) Λ'
      ≃ₗᵢ[ℂ] EuclideanSpace ℂ
          (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regionIdxEquiv h)

/-! ### Operator action `M ⊗ 1` on the basis-relabelled split

We realise the heuristic action `M ⊗ 1_{Λ' \ Λ}` as a continuous linear
operator on `regionHilbert Λ'`.  The construction is staged through the
basis-relabelled product `EuclideanSpace ℂ (regionIdx Λ × regionIdx (Λ' \ Λ))`:
on the product side, slicing in the second coordinate gives a family of
vectors in `regionHilbert Λ` to which `M` is applied independently.

The bound `‖tensorWithId h M‖ ≤ ‖M‖` is tight (the right tensor-product norm).
-/

variable {Λ Λ' : Finset L}

/-- Slice of a `(regionIdx Λ × regionIdx (Λ' \ Λ))`-indexed Euclidean vector
at fixed `b : regionIdx (Λ' \ Λ)`: the function `a ↦ f (a, b)` viewed as an
element of `regionHilbert Λ`. -/
noncomputable def regionSplitSlice
    (f : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)))
    (b : regionIdx (L := L) (Λ' \ Λ)) : regionHilbert (L := L) Λ :=
  WithLp.toLp 2 (fun a : regionIdx (L := L) Λ => f (a, b))

@[simp]
theorem regionSplitSlice_apply
    (f : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)))
    (b : regionIdx (L := L) (Λ' \ Λ))
    (a : regionIdx (L := L) Λ) :
    (regionSplitSlice (Λ' := Λ') f b) a = f (a, b) := rfl

theorem regionSplitSlice_add
    (f g : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)))
    (b : regionIdx (L := L) (Λ' \ Λ)) :
    regionSplitSlice (Λ' := Λ') (f + g) b
      = regionSplitSlice (Λ' := Λ') f b + regionSplitSlice (Λ' := Λ') g b := by
  ext a
  simp

theorem regionSplitSlice_smul
    (c : ℂ)
    (f : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)))
    (b : regionIdx (L := L) (Λ' \ Λ)) :
    regionSplitSlice (Λ' := Λ') (c • f) b
      = c • regionSplitSlice (Λ' := Λ') f b := by
  ext a
  simp

/-- Fubini-style identity for the slice norm:
`‖f‖² = ∑_b ‖slice f b‖²`. -/
theorem norm_sq_eq_sum_regionSplitSlice
    (f : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ))) :
    ‖f‖ ^ 2
      = ∑ b : regionIdx (L := L) (Λ' \ Λ),
          ‖regionSplitSlice (Λ' := Λ') f b‖ ^ 2 := by
  have hb : ∀ b : regionIdx (L := L) (Λ' \ Λ),
      ‖regionSplitSlice (Λ' := Λ') f b‖ ^ 2
        = ∑ a : regionIdx (L := L) Λ, ‖f (a, b)‖ ^ 2 := by
    intro b
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right
    (f := fun p : regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ) =>
      ‖f p‖ ^ 2)]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [hb b]

/-- Underlying linear map of `tensorWithIdSplit M`. -/
noncomputable def tensorWithIdSplitLinear
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    EuclideanSpace ℂ (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ))
      →ₗ[ℂ]
    EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) where
  toFun f :=
    WithLp.toLp 2 (fun p : regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ) =>
      (M (regionSplitSlice (Λ' := Λ') f p.2)) p.1)
  map_add' f g := by
    ext p
    change (M (regionSplitSlice (Λ' := Λ') (f + g) p.2)) p.1
      = (M (regionSplitSlice (Λ' := Λ') f p.2)) p.1
        + (M (regionSplitSlice (Λ' := Λ') g p.2)) p.1
    rw [regionSplitSlice_add, ContinuousLinearMap.map_add]
    rfl
  map_smul' c f := by
    ext p
    change (M (regionSplitSlice (Λ' := Λ') (c • f) p.2)) p.1
      = c • (M (regionSplitSlice (Λ' := Λ') f p.2)) p.1
    rw [regionSplitSlice_smul, ContinuousLinearMap.map_smul]
    rfl

@[simp]
theorem tensorWithIdSplitLinear_apply
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (f : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)))
    (p : regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) :
    (tensorWithIdSplitLinear (Λ' := Λ') M f) p
      = (M (regionSplitSlice (Λ' := Λ') f p.2)) p.1 := rfl

/-- The slice of the result reassembles to `M` applied to the input slice. -/
theorem regionSplitSlice_tensorWithIdSplitLinear
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (f : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)))
    (b : regionIdx (L := L) (Λ' \ Λ)) :
    regionSplitSlice (Λ' := Λ')
        (tensorWithIdSplitLinear (Λ' := Λ') M f) b
      = M (regionSplitSlice (Λ' := Λ') f b) := by
  ext a
  rw [regionSplitSlice_apply, tensorWithIdSplitLinear_apply]

/-- The "M ⊗ 1" action on the basis-relabelled split, as a continuous
linear operator with operator-norm bound `‖M‖`. -/
noncomputable def tensorWithIdSplit
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    EuclideanSpace ℂ (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ))
      →L[ℂ]
    EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) :=
  LinearMap.mkContinuous (tensorWithIdSplitLinear (Λ' := Λ') M) ‖M‖
    (fun f => by
      have h_lhs_sq : ‖tensorWithIdSplitLinear (Λ' := Λ') M f‖ ^ 2
          = ∑ b : regionIdx (L := L) (Λ' \ Λ),
              ‖M (regionSplitSlice (Λ' := Λ') f b)‖ ^ 2 := by
        rw [norm_sq_eq_sum_regionSplitSlice]
        refine Finset.sum_congr rfl ?_
        intro b _
        rw [regionSplitSlice_tensorWithIdSplitLinear]
      have h_bound_sq : ‖tensorWithIdSplitLinear (Λ' := Λ') M f‖ ^ 2
          ≤ ‖M‖ ^ 2 * ‖f‖ ^ 2 := by
        rw [h_lhs_sq, norm_sq_eq_sum_regionSplitSlice (Λ' := Λ') f,
          Finset.mul_sum]
        refine Finset.sum_le_sum ?_
        intro b _
        have hop : ‖M (regionSplitSlice (Λ' := Λ') f b)‖
            ≤ ‖M‖ * ‖regionSplitSlice (Λ' := Λ') f b‖ := M.le_opNorm _
        have hsq : ‖M (regionSplitSlice (Λ' := Λ') f b)‖ ^ 2
            ≤ (‖M‖ * ‖regionSplitSlice (Λ' := Λ') f b‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hop 2
        calc ‖M (regionSplitSlice (Λ' := Λ') f b)‖ ^ 2
            ≤ (‖M‖ * ‖regionSplitSlice (Λ' := Λ') f b‖) ^ 2 := hsq
          _ = ‖M‖ ^ 2 * ‖regionSplitSlice (Λ' := Λ') f b‖ ^ 2 := by ring
      have hMf_nn : 0 ≤ ‖M‖ * ‖f‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hbound_sq_form : (‖M‖ * ‖f‖) ^ 2 = ‖M‖ ^ 2 * ‖f‖ ^ 2 := by ring
      have h_sq : ‖tensorWithIdSplitLinear (Λ' := Λ') M f‖ ^ 2
          ≤ (‖M‖ * ‖f‖) ^ 2 := by
        rw [hbound_sq_form]; exact h_bound_sq
      exact (abs_le_of_sq_le_sq' h_sq hMf_nn).2)

@[simp]
theorem tensorWithIdSplit_apply
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (f : EuclideanSpace ℂ
      (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)))
    (p : regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) :
    (tensorWithIdSplit (Λ' := Λ') M f) p
      = (M (regionSplitSlice (Λ' := Λ') f p.2)) p.1 := rfl

theorem tensorWithIdSplit_one :
    tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ')
        (ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ))
      = ContinuousLinearMap.id ℂ
          (EuclideanSpace ℂ
            (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ))) := by
  ext f p
  rw [tensorWithIdSplit_apply, ContinuousLinearMap.id_apply,
    regionSplitSlice_apply, ContinuousLinearMap.id_apply]

theorem tensorWithIdSplit_zero :
    tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ')
        (0 : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
      = 0 := by
  ext f p
  rw [tensorWithIdSplit_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.zero_apply]
  rfl

theorem tensorWithIdSplit_mul
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') (M.comp N)
      = (tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') M).comp
          (tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') N) := by
  ext f p
  rw [tensorWithIdSplit_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensorWithIdSplit_apply]
  congr 1

theorem tensorWithIdSplit_add
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') (M + N)
      = tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') M
          + tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') N := by
  ext f p
  rw [tensorWithIdSplit_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply]
  change (M (regionSplitSlice (Λ' := Λ') f p.2)) p.1
        + (N (regionSplitSlice (Λ' := Λ') f p.2)) p.1
    = (tensorWithIdSplit (Λ' := Λ') M f
        + tensorWithIdSplit (Λ' := Λ') N f).ofLp p
  rw [WithLp.ofLp_add, Pi.add_apply]
  rfl

theorem tensorWithIdSplit_smul (c : ℂ)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') (c • M)
      = c • tensorWithIdSplit (L := L) (Λ := Λ) (Λ' := Λ') M := by
  ext f p
  rw [tensorWithIdSplit_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply]
  change (c • M (regionSplitSlice (Λ' := Λ') f p.2)) p.1
    = (c • tensorWithIdSplit (Λ' := Λ') M f).ofLp p
  rw [WithLp.ofLp_smul, Pi.smul_apply]
  rfl

/-- The operator `M ⊗ 1_{Λ' \ Λ}` on `regionHilbert Λ'`, defined by
conjugating the basis-relabelled action `tensorWithIdSplit M` with the
linear isometric equivalence `regionHilbertSplitEquiv h`. -/
noncomputable def tensorWithId (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    regionHilbert (L := L) Λ' →L[ℂ] regionHilbert (L := L) Λ' :=
  let e := regionHilbertSplitEquiv (L := L) h
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((tensorWithIdSplit (Λ' := Λ') M).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap)

theorem tensorWithId_apply (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (v : regionHilbert (L := L) Λ') :
    tensorWithId h M v
      = (regionHilbertSplitEquiv (L := L) h).symm
          (tensorWithIdSplit (Λ' := Λ') M
            (regionHilbertSplitEquiv (L := L) h v)) := rfl

/-- `tensorWithId h` sends the identity to the identity. -/
@[simp]
theorem tensorWithId_one (h : Λ ⊆ Λ') :
    tensorWithId h (ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ))
      = ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ') := by
  ext v
  rw [tensorWithId_apply, tensorWithIdSplit_one,
    ContinuousLinearMap.id_apply,
    LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]

/-- `tensorWithId h` sends zero to zero. -/
@[simp]
theorem tensorWithId_zero (h : Λ ⊆ Λ') :
    tensorWithId h (0 : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
      = 0 := by
  ext v
  rw [tensorWithId_apply, tensorWithIdSplit_zero,
    ContinuousLinearMap.zero_apply, map_zero, ContinuousLinearMap.zero_apply]

/-- `tensorWithId h` is multiplicative: `tensorWithId h (M ∘ N)
= tensorWithId h M ∘ tensorWithId h N`. -/
theorem tensorWithId_mul (h : Λ ⊆ Λ')
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    tensorWithId h (M.comp N)
      = (tensorWithId h M).comp (tensorWithId h N) := by
  ext v
  rw [tensorWithId_apply, tensorWithIdSplit_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    tensorWithId_apply, tensorWithId_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- `M ↦ tensorWithId h M` is additive in `M`. -/
theorem tensorWithId_add (h : Λ ⊆ Λ')
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    tensorWithId h (M + N) = tensorWithId h M + tensorWithId h N := by
  ext v
  rw [tensorWithId_apply, tensorWithIdSplit_add,
    ContinuousLinearMap.add_apply, map_add,
    ContinuousLinearMap.add_apply, tensorWithId_apply, tensorWithId_apply]

/-- `M ↦ tensorWithId h M` is `ℂ`-linear in `M`. -/
theorem tensorWithId_smul (h : Λ ⊆ Λ') (c : ℂ)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    tensorWithId h (c • M) = c • tensorWithId h M := by
  ext v
  rw [tensorWithId_apply, tensorWithIdSplit_smul,
    ContinuousLinearMap.smul_apply, map_smul,
    ContinuousLinearMap.smul_apply, tensorWithId_apply]

end LocalNetLike
