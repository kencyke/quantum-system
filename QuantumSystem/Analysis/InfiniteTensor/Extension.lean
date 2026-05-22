module

public import Mathlib.Algebra.Colimit.Module
public import QuantumSystem.Analysis.InfiniteTensor.Product
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.PiTensorProduct

/-!
# Ω-extension between finite tensor products on nested finite subsets

For a Hilbert family `H : ι → Type*` (finite-dim per factor) and a unit-vector
reference family `Ω : UnitFamily H`, this file builds the directed-system
data underlying the incomplete infinite tensor product:

* the `regionTensor` Hilbert space at each finite subset `S : Finset ι`,
  realised as `⨂[ℂ] s : S, H s.val`;
* the `regionEmbedLe` linear map between two such spaces along an inclusion
  `S ⊆ S'`, defined on elementary tensors by tensoring with the components
  of `Ω` at the new indices `S' \ S`.

The construction is the pure-layer analogue of the deleted lattice-specific
`RegionDirectedOmega.lean`; it operates on abstract Hilbert factors via
`PiTensorProduct` rather than basis-indexed `EuclideanSpace`.

## Main definitions

* `InfiniteTensor.regionTensor S H` — the finite tensor product Hilbert
  space `⨂[ℂ] s : S, H s.val` (with the inner-product structure from
  `ForMathlib.PiTensorProduct`).
* `InfiniteTensor.UnitFamily.extendVec Ω h ξ` — the function-level extension
  of a tuple `ξ : (s : S) → H s.val` to a tuple over the larger finset `S'`,
  filled with the components of `Ω` at the new indices.
* `InfiniteTensor.UnitFamily.extendMultilinear Ω h` — the multilinear map
  `(s : S) → H s.val ⟶ ⨂[ℂ] s' : S', H s'.val` underlying the extension
  on elementary tensors.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2 (incomplete infinite tensor product).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Module _root_.PiTensorProduct

namespace InfiniteTensor

variable {ι : Type*} [DecidableEq ι] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

/-- The finite tensor product Hilbert space at a finite subset
`S : Finset ι`, realised as `⨂[ℂ] s : S, H s.val`. -/
abbrev regionTensor (S : Finset ι) : Type _ :=
  ⨂[ℂ] s : {x // x ∈ S}, H s.val

namespace UnitFamily

/-- The function-level extension of a finite-region tuple
`ξ : (s : S) → H s.val` along an inclusion `S ⊆ S'`, filling the new
indices `S' \ S` with the components of the unit-vector family `Ω`. -/
noncomputable def extendVec (Ω : UnitFamily H) {S S' : Finset ι}
    (_h : S ⊆ S') (ξ : (s : {x // x ∈ S}) → H s.val) :
    (s' : {x // x ∈ S'}) → H s'.val :=
  fun s' => if hs : s'.val ∈ S then ξ ⟨s'.val, hs⟩ else Ω s'.val

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem extendVec_inside (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val) (s' : {x // x ∈ S'})
    (hs : s'.val ∈ S) :
    extendVec Ω h ξ s' = ξ ⟨s'.val, hs⟩ := by
  unfold extendVec; rw [dif_pos hs]

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem extendVec_outside (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val) (s' : {x // x ∈ S'})
    (hs : s'.val ∉ S) :
    extendVec Ω h ξ s' = Ω s'.val := by
  unfold extendVec; rw [dif_neg hs]

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- Updating `ξ` at index `i : S` corresponds to updating `extendVec Ω h ξ`
at the lifted index `⟨i.val, h i.prop⟩ : S'`.  This is the key compatibility
lemma making `extendVec` interact well with `MultilinearMap.update`. -/
theorem extendVec_update_apply (Ω : UnitFamily H) {S S' : Finset ι}
    (h : S ⊆ S') (ξ : (s : {x // x ∈ S}) → H s.val) (i : {x // x ∈ S})
    (v : H i.val) (s' : {x // x ∈ S'}) :
    extendVec Ω h (Function.update ξ i v) s'
      = Function.update (extendVec Ω h ξ) ⟨i.val, h i.prop⟩ v s' := by
  unfold extendVec
  by_cases hs' : s' = ⟨i.val, h i.prop⟩
  · -- s' is the lifted i.
    subst hs'
    rw [Function.update_self]
    have hi : i.val ∈ S := i.prop
    rw [dif_pos hi]
    -- Goal: Function.update ξ i v ⟨i.val, hi⟩ = v, where ⟨i.val, hi⟩ = i defeq.
    change Function.update ξ i v i = v
    exact Function.update_self ..
  · rw [Function.update_of_ne hs']
    by_cases hs : s'.val ∈ S
    · rw [dif_pos hs, dif_pos hs]
      have hne : (⟨s'.val, hs⟩ : {x // x ∈ S}) ≠ i := by
        intro heq
        apply hs'
        apply Subtype.ext
        change s'.val = i.val
        exact congrArg Subtype.val heq
      rw [Function.update_of_ne hne]
    · rw [dif_neg hs, dif_neg hs]

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- Function-level form of `extendVec_update_apply`. -/
theorem extendVec_update (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val) (i : {x // x ∈ S}) (v : H i.val) :
    extendVec Ω h (Function.update ξ i v)
      = Function.update (extendVec Ω h ξ) ⟨i.val, h i.prop⟩ v := by
  funext s'
  exact extendVec_update_apply Ω h ξ i v s'

/-- The Ω-extension multilinear map from finite-region tuples on `S` to the
finite tensor product Hilbert space at the larger finset `S'`. -/
noncomputable def extendMultilinear (Ω : UnitFamily H) {S S' : Finset ι}
    (h : S ⊆ S') :
    MultilinearMap ℂ (fun s : {x // x ∈ S} => H s.val)
      (regionTensor S' (H := H)) :=
  { toFun := fun ξ => tprod ℂ (extendVec Ω h ξ)
    map_update_add' := by
      intro inst ξ i x y
      -- Convert the local `inst` to the canonical `Subtype` `DecidableEq` via `Subsingleton`.
      have hinst : inst = (fun a b => a.instDecidableEq b) := Subsingleton.elim _ _
      subst hinst
      rw [extendVec_update, extendVec_update, extendVec_update]
      exact (PiTensorProduct.tprod ℂ).map_update_add (extendVec Ω h ξ)
        ⟨i.val, h i.prop⟩ x y
    map_update_smul' := by
      intro inst ξ i c x
      have hinst : inst = (fun a b => a.instDecidableEq b) := Subsingleton.elim _ _
      subst hinst
      rw [extendVec_update, extendVec_update]
      exact (PiTensorProduct.tprod ℂ).map_update_smul (extendVec Ω h ξ)
        ⟨i.val, h i.prop⟩ c x }

omit [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem extendMultilinear_apply (Ω : UnitFamily H) {S S' : Finset ι}
    (h : S ⊆ S') (ξ : (s : {x // x ∈ S}) → H s.val) :
    extendMultilinear Ω h ξ = tprod ℂ (extendVec Ω h ξ) := rfl

/-- The Ω-extension as a linear map `regionTensor S → regionTensor S'`. -/
noncomputable def regionEmbedLe (Ω : UnitFamily H) {S S' : Finset ι}
    (h : S ⊆ S') :
    regionTensor S (H := H) →ₗ[ℂ] regionTensor S' (H := H) :=
  PiTensorProduct.lift (extendMultilinear Ω h)

omit [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem regionEmbedLe_tprod (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (ξ : (s : {x // x ∈ S}) → H s.val) :
    regionEmbedLe Ω h (tprod ℂ ξ) = tprod ℂ (extendVec Ω h ξ) := by
  rw [regionEmbedLe, PiTensorProduct.lift.tprod, extendMultilinear_apply]

/-! ### Isometry property of `regionEmbedLe`

The key fact powering the colimit construction: for unit-vector reference
families `Ω`, the linear map `regionEmbedLe Ω h` preserves the inner
product.  On elementary tensors this reduces to the inner-product formula
`inner_tprod_tprod` together with `‖Ω i‖ = 1` discharging the new-site
factors. -/

/-- The inner product of two Ω-extended elementary tensors equals the
inner product of the original elementary tensors. -/
theorem regionEmbedLe_inner_tprod_tprod (Ω : UnitFamily H) {S S' : Finset ι}
    (h : S ⊆ S') (ξ η : (s : {x // x ∈ S}) → H s.val) :
    ⟪regionEmbedLe Ω h (tprod ℂ ξ), regionEmbedLe Ω h (tprod ℂ η)⟫_ℂ
      = ⟪(tprod ℂ ξ : regionTensor S (H := H)), tprod ℂ η⟫_ℂ := by
  rw [regionEmbedLe_tprod, regionEmbedLe_tprod]
  rw [ForMathlib.PiTensorProduct.inner_tprod_tprod,
    ForMathlib.PiTensorProduct.inner_tprod_tprod]
  -- LHS: ∏ s' : ↥S', ⟪extendVec Ω h ξ s', extendVec Ω h η s'⟫_ℂ
  -- RHS: ∏ s : ↥S, ⟪ξ s, η s⟫_ℂ
  -- Apply `Finset.prod_bij` with the embedding `↥S ↪ ↥S'` carried by `h`.
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun s' : {x // x ∈ S'} => s'.val ∈ S)]
  -- The "not in S" part: each factor reduces to ‖Ω _‖² = 1.
  have hOut :
      (∏ s' ∈ Finset.univ.filter (fun s' : {x // x ∈ S'} => ¬ s'.val ∈ S),
          ⟪extendVec Ω h ξ s', extendVec Ω h η s'⟫_ℂ) = 1 := by
    refine Finset.prod_eq_one fun s' hs' => ?_
    rw [Finset.mem_filter] at hs'
    rw [extendVec_outside _ _ _ _ hs'.2, extendVec_outside _ _ _ _ hs'.2]
    rw [@inner_self_eq_norm_sq_to_K ℂ, Ω.norm_apply s'.val]
    push_cast; ring
  rw [hOut, mul_one]
  -- The "in S" part: reindex via `↥S' ⊇ S ↔ ↥S` bijection.
  symm
  refine Finset.prod_bij
      (fun (s : {x // x ∈ S}) (_ : s ∈ Finset.univ) =>
        (⟨s.val, h s.prop⟩ : {x // x ∈ S'}))
      ?h_mem ?h_inj ?h_surj ?h_eq
  · intro s _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, s.prop⟩
  · intro a _ b _ hab
    -- Beta-reduce hab and extract.
    have : (a : ι) = b := by
      have := congrArg Subtype.val hab
      exact this
    exact Subtype.ext this
  · intro s' hs'
    rw [Finset.mem_filter] at hs'
    refine ⟨⟨s'.val, hs'.2⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro s _
    have hs : (⟨s.val, h s.prop⟩ : {x // x ∈ S'}).val ∈ S := s.prop
    rw [extendVec_inside _ _ _ _ hs, extendVec_inside _ _ _ _ hs]

/-- Sesquilinear lift of `regionEmbedLe_inner_tprod_tprod`: the linear map
`regionEmbedLe Ω h` preserves the inner product on every pair of vectors. -/
theorem regionEmbedLe_inner (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (x y : regionTensor S (H := H)) :
    ⟪regionEmbedLe Ω h x, regionEmbedLe Ω h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  -- Double induction on `x, y` using `PiTensorProduct.induction_on`.
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' η =>
      rw [map_smul, map_smul]
      rw [inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right]
      rw [regionEmbedLe_inner_tprod_tprod]
    | add y₁ y₂ ihy₁ ihy₂ =>
      rw [map_add, inner_add_right, inner_add_right, ihy₁, ihy₂]
  | add x₁ x₂ ihx₁ ihx₂ =>
    rw [map_add, inner_add_left, inner_add_left, ihx₁, ihx₂]

/-- Bundled linear-isometry version of `regionEmbedLe`. -/
noncomputable def regionEmbedLeIsom (Ω : UnitFamily H) {S S' : Finset ι}
    (h : S ⊆ S') :
    regionTensor S (H := H) →ₗᵢ[ℂ] regionTensor S' (H := H) :=
  { (regionEmbedLe Ω h) with
    norm_map' := by
      intro x
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      rw [← regionEmbedLe_inner Ω h x x] }

@[simp]
theorem regionEmbedLeIsom_apply (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (x : regionTensor S (H := H)) :
    regionEmbedLeIsom Ω h x = regionEmbedLe Ω h x := rfl

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- The Ω-extension along the trivial inclusion `S ⊆ S` recovers the input
tuple at every Subtype index. -/
theorem extendVec_self (Ω : UnitFamily H) {S : Finset ι}
    (ξ : (s : {x // x ∈ S}) → H s.val) :
    extendVec Ω (subset_refl S) ξ = ξ := by
  funext s
  unfold extendVec
  rw [dif_pos s.prop]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- `regionEmbedLe` is the identity along the trivial inclusion `S ⊆ S`. -/
@[simp]
theorem regionEmbedLe_self (Ω : UnitFamily H) {S : Finset ι} (x : regionTensor S (H := H)) :
    regionEmbedLe Ω (subset_refl S) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, regionEmbedLe_tprod, extendVec_self]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add, ih₁, ih₂]

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- The Ω-extension is functorial at the tuple level. -/
theorem extendVec_trans (Ω : UnitFamily H) {S S' S'' : Finset ι}
    (h : S ⊆ S') (h' : S' ⊆ S'')
    (ξ : (s : {x // x ∈ S}) → H s.val) :
    extendVec Ω h' (extendVec Ω h ξ) = extendVec Ω (h.trans h') ξ := by
  funext s''
  unfold extendVec
  by_cases hs'' : s''.val ∈ S'
  · rw [dif_pos hs'']
  · rw [dif_neg hs'']
    have hns : s''.val ∉ S := fun hs => hs'' (h hs)
    rw [dif_neg hns]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- `regionEmbedLe` is functorial: extending along `S ⊆ S' ⊆ S''` equals
extending along the composite `S ⊆ S''`. -/
theorem regionEmbedLe_trans (Ω : UnitFamily H) {S S' S'' : Finset ι}
    (h : S ⊆ S') (h' : S' ⊆ S'') (x : regionTensor S (H := H)) :
    regionEmbedLe Ω h' (regionEmbedLe Ω h x) = regionEmbedLe Ω (h.trans h') x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    simp only [map_smul, regionEmbedLe_tprod, extendVec_trans]
  | add x₁ x₂ ih₁ ih₂ =>
    simp only [map_add, ih₁, ih₂]

/-! ### Algebraic colimit of finite-region tensor products -/

/-- The directed system of finite-region tensor products linked by
Ω-extension along finite-subset inclusions. -/
noncomputable def regionDirectedLink (Ω : UnitFamily H) :
    ∀ S S' : Finset ι, S ≤ S' →
      regionTensor S (H := H) →ₗ[ℂ] regionTensor S' (H := H) :=
  fun _ _ h => regionEmbedLe Ω h

instance regionDirectedSystem (Ω : UnitFamily H) :
    DirectedSystem (fun S : Finset ι => regionTensor S (H := H))
      (fun _ _ h => regionDirectedLink Ω _ _ h) where
  map_self := fun {_} x => regionEmbedLe_self Ω x
  map_map := fun {_} {_} {_} hij hjk x => regionEmbedLe_trans Ω hij hjk x

/-- The algebraic (uncompleted) colimit of the directed system of finite
tensor products `regionTensor S` linked by Ω-extension.

This is the pre-Hilbert space whose Hilbert completion will be
`ITPSector H Ω` (Phase 2 step (d)). -/
noncomputable abbrev preITPSector (Ω : UnitFamily H) : Type _ :=
  Module.DirectLimit (fun S : Finset ι => regionTensor S (H := H))
    (regionDirectedLink Ω)

/-- Embedding of a finite-region tensor space into the algebraic colimit. -/
noncomputable def preITPSector.of (Ω : UnitFamily H) (S : Finset ι) :
    regionTensor S (H := H) →ₗ[ℂ] preITPSector Ω :=
  Module.DirectLimit.of ℂ (Finset ι)
    (fun S : Finset ι => regionTensor S (H := H)) (regionDirectedLink Ω) S

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem preITPSector.of_def (Ω : UnitFamily H) (S : Finset ι) :
    preITPSector.of Ω S = Module.DirectLimit.of ℂ (Finset ι)
      (fun S : Finset ι => regionTensor S (H := H)) (regionDirectedLink Ω) S := rfl

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Compatibility with Ω-extension: along an inclusion `S ⊆ S'`, the
embedding `preITPSector.of S` factors as `preITPSector.of S' ∘ regionEmbedLe`. -/
theorem preITPSector.of_extend (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (x : regionTensor S (H := H)) :
    preITPSector.of Ω S' (regionEmbedLe Ω h x) = preITPSector.of Ω S x :=
  Module.DirectLimit.of_f (f := regionDirectedLink Ω)

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Existence of a `preITPSector.of` representative for any colimit element.
This is the `preITPSector.of`-flavoured wrapping of
`Module.DirectLimit.exists_of`. -/
theorem preITPSector.exists_of (Ω : UnitFamily H) (x : preITPSector Ω) :
    ∃ S : Finset ι, ∃ x' : regionTensor S (H := H), preITPSector.of Ω S x' = x :=
  Module.DirectLimit.exists_of x

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- `preITPSector.of`-flavoured wrapping of `Module.DirectLimit.exists_of₂`. -/
theorem preITPSector.exists_of₂ (Ω : UnitFamily H) (x y : preITPSector Ω) :
    ∃ S : Finset ι, ∃ x' y' : regionTensor S (H := H),
      preITPSector.of Ω S x' = x ∧ preITPSector.of Ω S y' = y :=
  Module.DirectLimit.exists_of₂ x y

/-! ### Inner product on `preITPSector Ω` (via Classical.choose)

**CAUTION (technical note for reviewers).**

The inner product on `preITPSector Ω` is defined below using `Classical.choose`
applied to `Module.DirectLimit.exists_of₂`.  Two consequences:

* The definition is *opaque*: the value `innerPreITPSector x y` is not
  syntactically equal to any specific `⟪x', y'⟫_ℂ`.  All downstream proofs
  must instead use the characterisation lemma `innerPreITPSector_of_of`,
  which states `⟪of S x', of S y'⟫_ℂ = ⟪x', y'⟫_ℂ` whenever both arguments
  are pushed forward from a *common* finset `S`.

* The definition relies on `Classical.choice`.  This is unavoidable for any
  Module.DirectLimit-based construction of a sesquilinear form, because
  `Module.DirectLimit.lift` accepts only ℂ-linear maps and the inner product
  is conjugate-linear in its first argument.  The alternative routes
  ((ii) ℝ-bilinear decomposition / (iii) sesquilinear-aware DirectLimit lift)
  are documented in the migration plan.

The well-definedness of `innerPreITPSector` rests on the isometry of
`regionEmbedLe` (`regionEmbedLe_inner`) plus the cocycle / functoriality
property (`regionEmbedLe_trans` and the `DirectedSystem` instance
`regionDirectedSystem`). -/

/-- Inner product on the algebraic colimit `preITPSector Ω`, defined via
`Classical.choose` on `Module.DirectLimit.exists_of₂`.

See `innerPreITPSector_of_of` for the characterising equation.  Direct
unfolding of this definition is opaque; downstream proofs should rely on
the characterising lemma. -/
noncomputable def innerPreITPSector (Ω : UnitFamily H) :
    preITPSector Ω → preITPSector Ω → ℂ := fun x y =>
  let ex := Module.DirectLimit.exists_of₂ x y
  let x' := ex.choose_spec.choose
  let y' := ex.choose_spec.choose_spec.choose
  ⟪x', y'⟫_ℂ

/-- Auxiliary: the inner product of two finite-region representatives is
preserved when both are simultaneously extended to a larger finset. -/
theorem regionEmbedLe_inner_apply (Ω : UnitFamily H) {S S' : Finset ι}
    (h : S ⊆ S') (x' y' : regionTensor S (H := H)) :
    ⟪regionEmbedLe Ω h x', regionEmbedLe Ω h y'⟫_ℂ = ⟪x', y'⟫_ℂ :=
  regionEmbedLe_inner Ω h x' y'

/-- Auxiliary: equality of `of`-images implies inner-product equality across
representatives.  Given representatives `(S, x', y')` and `(T, xT, yT)` of
the same colimit pair (i.e. `of S x' = of T xT` and `of S y' = of T yT`),
the inner products on the respective regionTensors agree. -/
theorem inner_eq_of_of_eq (Ω : UnitFamily H) {S T : Finset ι}
    {x' y' : regionTensor S (H := H)} {xT yT : regionTensor T (H := H)}
    (hx : preITPSector.of Ω S x' = preITPSector.of Ω T xT)
    (hy : preITPSector.of Ω S y' = preITPSector.of Ω T yT) :
    ⟪x', y'⟫_ℂ = ⟪xT, yT⟫_ℂ := by
  -- Lift to a common upper bound U := S ∪ T.
  let U := S ∪ T
  have hSU : S ⊆ U := Finset.subset_union_left
  have hTU : T ⊆ U := Finset.subset_union_right
  -- The lifts of x', xT (and similarly y', yT) to U have equal `of`-images.
  have hxU : preITPSector.of Ω U (regionEmbedLe Ω hSU x')
      = preITPSector.of Ω U (regionEmbedLe Ω hTU xT) := by
    rw [preITPSector.of_extend, preITPSector.of_extend]; exact hx
  have hyU : preITPSector.of Ω U (regionEmbedLe Ω hSU y')
      = preITPSector.of Ω U (regionEmbedLe Ω hTU yT) := by
    rw [preITPSector.of_extend, preITPSector.of_extend]; exact hy
  -- Find common upper bounds where the lifts agree literally.
  obtain ⟨Vx, hUVx, hxV⟩ :=
    Module.DirectLimit.exists_eq_of_of_eq (G := fun S : Finset ι => regionTensor S (H := H))
      (f := regionDirectedLink Ω) hxU
  obtain ⟨Vy, hUVy, hyV⟩ :=
    Module.DirectLimit.exists_eq_of_of_eq (G := fun S : Finset ι => regionTensor S (H := H))
      (f := regionDirectedLink Ω) hyU
  -- Take W := Vx ∪ Vy, where both literal equalities lift.
  let W := Vx ∪ Vy
  have hVxW : Vx ⊆ W := Finset.subset_union_left
  have hVyW : Vy ⊆ W := Finset.subset_union_right
  have hSW : S ⊆ W := hSU.trans (hUVx.trans hVxW)
  have hTW : T ⊆ W := hTU.trans (hUVx.trans hVxW)
  -- Lift hxV to W via regionEmbedLe Ω hVxW.
  have hxW : regionEmbedLe Ω hSW x' = regionEmbedLe Ω hTW xT := by
    have := congrArg (regionEmbedLe Ω hVxW) hxV
    simp only [regionDirectedLink, regionEmbedLe_trans] at this
    exact this
  have hyW : regionEmbedLe Ω hSW y' = regionEmbedLe Ω hTW yT := by
    have := congrArg (regionEmbedLe Ω hVyW) hyV
    simp only [regionDirectedLink, regionEmbedLe_trans] at this
    -- `this` is at level W via Vy; proof irrelevance lets it match the W via Vx version.
    exact this
  -- Now both inner products equal `⟪regionEmbedLe S→W x', regionEmbedLe S→W y'⟫_W`.
  rw [← regionEmbedLe_inner Ω hSW x' y', ← regionEmbedLe_inner Ω hTW xT yT,
    hxW, hyW]

/-- **Characterising equation for `innerPreITPSector`**: when both arguments
are pushed forward from a common finset `S`, the colimit inner product
equals the inner product on `regionTensor S`. -/
theorem innerPreITPSector_of_of (Ω : UnitFamily H) {S : Finset ι}
    (x' y' : regionTensor S (H := H)) :
    innerPreITPSector Ω (preITPSector.of Ω S x') (preITPSector.of Ω S y')
      = ⟪x', y'⟫_ℂ := by
  unfold innerPreITPSector
  -- Apply the well-definedness lemma: the Classical.choose representative
  -- gives the same inner product as `(S, x', y')`.
  exact (inner_eq_of_of_eq Ω
    ((Module.DirectLimit.exists_of₂ (preITPSector.of Ω S x')
        (preITPSector.of Ω S y')).choose_spec.choose_spec.choose_spec.1.symm)
    ((Module.DirectLimit.exists_of₂ (preITPSector.of Ω S x')
        (preITPSector.of Ω S y')).choose_spec.choose_spec.choose_spec.2.symm)).symm

/-- The bundled `Inner ℂ` instance on `preITPSector Ω`. -/
noncomputable instance instInnerPreITPSector (Ω : UnitFamily H) :
    Inner ℂ (preITPSector Ω) where
  inner x y := innerPreITPSector Ω x y

/-- Restate `innerPreITPSector_of_of` in `⟪·, ·⟫_ℂ` notation. -/
theorem inner_of_of (Ω : UnitFamily H) {S : Finset ι}
    (x' y' : regionTensor S (H := H)) :
    ⟪preITPSector.of Ω S x', preITPSector.of Ω S y'⟫_ℂ = ⟪x', y'⟫_ℂ :=
  innerPreITPSector_of_of Ω x' y'

/-- Conjugate-symmetry of the inner product on `preITPSector Ω`. -/
theorem inner_preITPSector_conj_symm (Ω : UnitFamily H) (x y : preITPSector Ω) :
    (starRingEnd ℂ) ⟪y, x⟫_ℂ = ⟪x, y⟫_ℂ := by
  -- Take a common representative (S, x', y') for (x, y).
  obtain ⟨S, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  -- Express both inner products via the characterising equation and use
  -- `inner_conj_symm` on `regionTensor S`.
  have hxy : ⟪x, y⟫_ℂ = ⟪x', y'⟫_ℂ := by rw [← hx, ← hy]; exact inner_of_of Ω x' y'
  have hyx : ⟪y, x⟫_ℂ = ⟪y', x'⟫_ℂ := by rw [← hx, ← hy]; exact inner_of_of Ω y' x'
  rw [hxy, hyx, _root_.inner_conj_symm]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Three-way common-representative helper.  For `x, y, z : preITPSector Ω`,
there is a single finset `S` and elements `x', y', z' : regionTensor S` with
`of S x' = x`, `of S y' = y`, `of S z' = z`. -/
theorem exists_of₃ (Ω : UnitFamily H) (x y z : preITPSector Ω) :
    ∃ S : Finset ι, ∃ x' y' z' : regionTensor S (H := H),
      preITPSector.of Ω S x' = x ∧ preITPSector.of Ω S y' = y
        ∧ preITPSector.of Ω S z' = z := by
  obtain ⟨S₁, _xy, z'', _, hz⟩ := preITPSector.exists_of₂ Ω (x + y) z
  obtain ⟨S₂, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  -- Take U := S₁ ∪ S₂.
  let U := S₁ ∪ S₂
  have hS₁U : S₁ ⊆ U := Finset.subset_union_left
  have hS₂U : S₂ ⊆ U := Finset.subset_union_right
  refine ⟨U, regionEmbedLe Ω hS₂U x', regionEmbedLe Ω hS₂U y',
    regionEmbedLe Ω hS₁U z'', ?_, ?_, ?_⟩ <;>
    [exact (preITPSector.of_extend Ω hS₂U x').trans hx;
     exact (preITPSector.of_extend Ω hS₂U y').trans hy;
     exact (preITPSector.of_extend Ω hS₁U z'').trans hz]

/-- Additivity of the inner product in the first slot. -/
theorem inner_preITPSector_add_left (Ω : UnitFamily H) (x y z : preITPSector Ω) :
    ⟪x + y, z⟫_ℂ = ⟪x, z⟫_ℂ + ⟪y, z⟫_ℂ := by
  obtain ⟨S, x', y', z', hx, hy, hz⟩ := exists_of₃ Ω x y z
  have hxz : ⟪x, z⟫_ℂ = ⟪x', z'⟫_ℂ := by rw [← hx, ← hz]; exact inner_of_of Ω x' z'
  have hyz : ⟪y, z⟫_ℂ = ⟪y', z'⟫_ℂ := by rw [← hy, ← hz]; exact inner_of_of Ω y' z'
  have hxyz : ⟪x + y, z⟫_ℂ = ⟪x' + y', z'⟫_ℂ := by
    rw [← hx, ← hy, ← hz, ← map_add]
    exact inner_of_of Ω (x' + y') z'
  rw [hxz, hyz, hxyz, _root_.inner_add_left]

/-- Conjugate-linearity of the inner product in the first slot. -/
theorem inner_preITPSector_smul_left (Ω : UnitFamily H) (c : ℂ) (x y : preITPSector Ω) :
    ⟪c • x, y⟫_ℂ = (starRingEnd ℂ) c * ⟪x, y⟫_ℂ := by
  obtain ⟨S, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  have hxy : ⟪x, y⟫_ℂ = ⟪x', y'⟫_ℂ := by rw [← hx, ← hy]; exact inner_of_of Ω x' y'
  have hcxy : ⟪c • x, y⟫_ℂ = ⟪c • x', y'⟫_ℂ := by
    rw [← hx, ← hy, ← map_smul]
    exact inner_of_of Ω (c • x') y'
  rw [hxy, hcxy, _root_.inner_smul_left]

/-- Non-negativity of `Re ⟪x, x⟫`. -/
theorem inner_preITPSector_re_self_nonneg (Ω : UnitFamily H) (x : preITPSector Ω) :
    0 ≤ RCLike.re ⟪x, x⟫_ℂ := by
  obtain ⟨S, x', hx⟩ := preITPSector.exists_of Ω x
  rw [← hx, inner_of_of]
  exact _root_.inner_self_nonneg

/-- Definiteness of the inner product. -/
theorem inner_preITPSector_self_eq_zero (Ω : UnitFamily H) {x : preITPSector Ω}
    (hxx : ⟪x, x⟫_ℂ = 0) : x = 0 := by
  obtain ⟨S, x', hxS⟩ := preITPSector.exists_of Ω x
  rw [← hxS, inner_of_of] at hxx
  -- hxx : ⟪x', x'⟫_ℂ = 0 in regionTensor S, hence x' = 0.
  have hx'_zero : x' = 0 := _root_.inner_self_eq_zero.mp hxx
  rw [← hxS, hx'_zero, map_zero]

/-! ### `NormedAddCommGroup` and `InnerProductSpace ℂ` instances on
`preITPSector Ω` -/

/-- The `NormedAddCommGroup` structure on `preITPSector Ω`, induced by the
inner product via `InnerProductSpace.Core.toNormedAddCommGroup`. -/
noncomputable instance instNormedAddCommGroupPreITPSector (Ω : UnitFamily H) :
    NormedAddCommGroup (preITPSector Ω) :=
  letI : InnerProductSpace.Core ℂ (preITPSector Ω) :=
    { inner x y := ⟪x, y⟫_ℂ
      conj_inner_symm x y := inner_preITPSector_conj_symm Ω x y
      re_inner_nonneg x := inner_preITPSector_re_self_nonneg Ω x
      add_left x y z := inner_preITPSector_add_left Ω x y z
      smul_left x y r := inner_preITPSector_smul_left Ω r x y
      definite _ hx := inner_preITPSector_self_eq_zero Ω hx }
  this.toNormedAddCommGroup

/-- The Hilbert (pre-)inner product space structure on `preITPSector Ω`. -/
noncomputable instance instInnerProductSpacePreITPSector (Ω : UnitFamily H) :
    InnerProductSpace ℂ (preITPSector Ω) :=
  InnerProductSpace.ofCore
    ({ inner x y := ⟪x, y⟫_ℂ
       conj_inner_symm x y := inner_preITPSector_conj_symm Ω x y
       re_inner_nonneg x := inner_preITPSector_re_self_nonneg Ω x
       add_left x y z := inner_preITPSector_add_left Ω x y z
       smul_left x y r := inner_preITPSector_smul_left Ω r x y
       : PreInnerProductSpace.Core ℂ (preITPSector Ω) })

end UnitFamily

end InfiniteTensor
