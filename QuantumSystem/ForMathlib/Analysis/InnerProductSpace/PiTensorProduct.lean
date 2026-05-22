module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Inner product space structure on `PiTensorProduct ℂ H` for finite Hilbert families

For a finite index type `ι` and a family of finite-dimensional complex
Hilbert spaces `H : ι → Type*`, this file equips `⨂[ℂ] i, H i` with the
canonical inner product satisfying

```
⟪⨂ ξ, ⨂ η⟫_ℂ = ∏ i, ⟪ξ i, η i⟫_ℂ
```

on elementary tensors.  The construction transports the inner product from
the basis-induced linear equivalence `⨂[ℂ] i, H i ≃ₗ[ℂ] EuclideanSpace ℂ I`
where `I = Π i, Fin (Module.finrank ℂ (H i))` is the multi-index set built
from the standard orthonormal bases of each factor.

The resulting `Inner` and `InnerProductSpace` instances on `⨂[ℂ] i, H i`
are inputs to the construction of the incomplete infinite tensor product
sector `ITPSector H Ω` in `QuantumSystem.Analysis.InfiniteTensor`.

## Main definitions

* `ForMathlib.PiTensorProduct.tensorONB` — the orthonormal basis on
  `⨂[ℂ] i, H i` indexed by `Π i, Fin (Module.finrank ℂ (H i))`, obtained by
  tensoring the standard orthonormal bases of the components.
* `ForMathlib.PiTensorProduct.instInner` — the resulting `Inner ℂ` instance.

## Main results

* `ForMathlib.PiTensorProduct.inner_tprod_tprod` — the elementary-tensor
  formula `⟪⨂ ξ, ⨂ η⟫_ℂ = ∏ i, ⟪ξ i, η i⟫_ℂ`.

## Status

This file is a Mathlib upstream candidate.  It provides:

* the `Inner ℂ` instance, defined through the basis-induced linear equivalence
  to `EuclideanSpace`;
* the elementary-tensor formula `inner_tprod_tprod`, derived from
  `Basis.piTensorProduct_repr_tprod_apply`, `OrthonormalBasis.repr_apply_apply`,
  Parseval (`OrthonormalBasis.sum_inner_mul_inner`), and the
  multi-index ↔ product-of-sums exchange `Finset.prod_univ_sum`;
* basic sesquilinearity (`add_left/right`, `smul_left/right`,
  `conj_inner_symm`, `re_inner_self_nonneg`, `inner_self_eq_zero_iff`);
* the `NormedAddCommGroup` and `InnerProductSpace ℂ` instances obtained from
  the `InnerProductSpace.Core` machinery.

This file deliberately does **not** import
`Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm`, whose
`SeminormedAddCommGroup` instance (the projective seminorm) would conflict
with our inner-product-induced `NormedAddCommGroup` instance.  A future
Mathlib upstream PR should reconcile the two by showing the projective
seminorm and the inner-product norm coincide on finite-dim Hilbert factors.

## References

* Mirrors `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` (the
  binary case) for the n-fold case.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical
  Mechanics II*, §2.7.2.
-/

@[expose] public section

namespace ForMathlib

namespace PiTensorProduct

open scoped InnerProductSpace TensorProduct
open Module _root_.PiTensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (H : ι → Type*)
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

/-- The standard orthonormal basis of each factor.  Used to build the
basis on the tensor product. -/
noncomputable def stdONB (i : ι) :
    OrthonormalBasis (Fin (Module.finrank ℂ (H i))) ℂ (H i) :=
  stdOrthonormalBasis ℂ (H i)

/-- The basis on `⨂[ℂ] i, H i` obtained by tensoring the standard
orthonormal bases of the components.

This is the basis underlying our definition of the inner product.  The
inner-product formula `⟪⨂ ξ, ⨂ η⟫_ℂ = ∏ i, ⟪ξ i, η i⟫_ℂ` will, after
proof, show that the resulting inner product is independent of the basis
choice. -/
noncomputable def tensorBasis :
    Basis ((i : ι) → Fin (Module.finrank ℂ (H i))) ℂ (⨂[ℂ] i, H i) :=
  Basis.piTensorProduct (fun i => (stdONB H i).toBasis)

/-- Linear equivalence between `⨂[ℂ] i, H i` and the Euclidean space
indexed by multi-indices `(i : ι) → Fin (Module.finrank ℂ (H i))`,
obtained by transport along the basis `tensorBasis H`.

This is the workhorse of the construction: the inner product on
`⨂[ℂ] i, H i` is *defined* as the pull-back of the standard `EuclideanSpace`
inner product along this equivalence.  The basis-independence of the
resulting inner product is captured by the elementary-tensor formula
`inner_tprod_tprod`. -/
noncomputable def euclideanEquiv :
    (⨂[ℂ] i, H i) ≃ₗ[ℂ]
      EuclideanSpace ℂ ((i : ι) → Fin (Module.finrank ℂ (H i))) :=
  (tensorBasis H).equivFun ≪≫ₗ (WithLp.linearEquiv 2 ℂ _).symm

/-- The pulled-back inner product on `⨂[ℂ] i, H i`.

Defined as `⟪x, y⟫ := ⟪euclideanEquiv H x, euclideanEquiv H y⟫` on the
Euclidean space side. -/
noncomputable instance instInner : Inner ℂ (⨂[ℂ] i, H i) where
  inner x y := inner ℂ (euclideanEquiv H x) (euclideanEquiv H y)

/-- The inner product unfolded through `euclideanEquiv`. -/
theorem inner_def (x y : ⨂[ℂ] i, H i) :
    ⟪x, y⟫_ℂ = ⟪euclideanEquiv H x, euclideanEquiv H y⟫_ℂ := rfl

/-! ### Sesquilinearity -/

/-- The inner product is conjugate-symmetric. -/
theorem inner_conj_symm (x y : ⨂[ℂ] i, H i) :
    (starRingEnd ℂ) ⟪y, x⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [inner_def, inner_def]
  exact _root_.inner_conj_symm _ _

/-- The inner product is additive in the first argument. -/
theorem inner_add_left (x y z : ⨂[ℂ] i, H i) :
    ⟪x + y, z⟫_ℂ = ⟪x, z⟫_ℂ + ⟪y, z⟫_ℂ := by
  rw [inner_def, inner_def, inner_def, map_add, _root_.inner_add_left]

/-- The inner product is additive in the second argument. -/
theorem inner_add_right (x y z : ⨂[ℂ] i, H i) :
    ⟪x, y + z⟫_ℂ = ⟪x, y⟫_ℂ + ⟪x, z⟫_ℂ := by
  rw [inner_def, inner_def, inner_def, map_add, _root_.inner_add_right]

/-- The inner product is conjugate-linear in the first argument. -/
theorem inner_smul_left (c : ℂ) (x y : ⨂[ℂ] i, H i) :
    ⟪c • x, y⟫_ℂ = (starRingEnd ℂ) c * ⟪x, y⟫_ℂ := by
  rw [inner_def, inner_def, map_smul, _root_.inner_smul_left]

/-- The inner product is linear in the second argument. -/
theorem inner_smul_right (c : ℂ) (x y : ⨂[ℂ] i, H i) :
    ⟪x, c • y⟫_ℂ = c * ⟪x, y⟫_ℂ := by
  rw [inner_def, inner_def, map_smul, _root_.inner_smul_right]

/-- Inner product with itself has non-negative real part. -/
theorem re_inner_self_nonneg (x : ⨂[ℂ] i, H i) :
    0 ≤ RCLike.re ⟪x, x⟫_ℂ := by
  rw [inner_def]
  exact _root_.inner_self_nonneg

/-- The inner product is definite: `⟪x, x⟫_ℂ = 0` implies `x = 0`. -/
theorem inner_self_eq_zero_iff {x : ⨂[ℂ] i, H i} :
    ⟪x, x⟫_ℂ = 0 ↔ x = 0 := by
  rw [inner_def]
  constructor
  · intro hx
    have heq : euclideanEquiv H x = 0 := _root_.inner_self_eq_zero.mp hx
    exact (euclideanEquiv H).injective (by rw [heq]; simp)
  · rintro rfl
    simp

/-! ### `NormedAddCommGroup` and `InnerProductSpace ℂ` instances

The norm on `⨂[ℂ] i, H i` is induced by the inner product through the
standard `InnerProductSpace.Core` to `NormedAddCommGroup` machinery.

Note: this section assumes Mathlib's existing `SeminormedAddCommGroup`
instance from `Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm`
is **not** in scope.  This file deliberately does not import that module. -/

/-- The norm on `⨂[ℂ] i, H i` induced by the inner product. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (⨂[ℂ] i, H i) :=
  letI : InnerProductSpace.Core ℂ (⨂[ℂ] i, H i) :=
    { inner x y := ⟪x, y⟫_ℂ
      conj_inner_symm x y := inner_conj_symm H x y
      re_inner_nonneg x := re_inner_self_nonneg H x
      add_left x y z := inner_add_left H x y z
      smul_left x y r := inner_smul_left H r x y
      definite _ hx := (inner_self_eq_zero_iff H).mp hx }
  this.toNormedAddCommGroup

/-- The Hilbert-space inner product structure on `⨂[ℂ] i, H i`. -/
noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (⨂[ℂ] i, H i) :=
  InnerProductSpace.ofCore
    ({ inner x y := ⟪x, y⟫_ℂ
       conj_inner_symm x y := inner_conj_symm H x y
       re_inner_nonneg x := re_inner_self_nonneg H x
       add_left x y z := inner_add_left H x y z
       smul_left x y r := inner_smul_left H r x y
       : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, H i) })

omit [DecidableEq ι] in
/-- The euclidean coordinates of `tprod ξ` are products of the
component-wise basis-coefficients. -/
theorem euclideanEquiv_tprod_ofLp (ξ : (i : ι) → H i)
    (p : (i : ι) → Fin (Module.finrank ℂ (H i))) :
    (euclideanEquiv H (tprod ℂ ξ)).ofLp p
      = ∏ i, ⟪(stdONB H i) (p i), ξ i⟫_ℂ := by
  change ((tensorBasis H).equivFun (tprod ℂ ξ)) p = _
  rw [Basis.equivFun_apply]
  rw [tensorBasis, Basis.piTensorProduct_repr_tprod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(stdONB H i).coe_toBasis_repr_apply, (stdONB H i).repr_apply_apply]

/-- **The elementary-tensor inner-product formula**:

`⟪⨂ ξ, ⨂ η⟫_ℂ = ∏ i, ⟪ξ i, η i⟫_ℂ`.

This is the canonical identity defining the inner product on a finite tensor
product of Hilbert spaces.  The proof goes through the basis-pull-back
definition of the inner product on `⨂[ℂ] i, H i`, expanding both Euclidean
coordinates and using Parseval's identity factor-wise. -/
theorem inner_tprod_tprod (ξ η : (i : ι) → H i) :
    ⟪(tprod ℂ ξ : ⨂[ℂ] i, H i), (tprod ℂ η : ⨂[ℂ] i, H i)⟫_ℂ
      = ∏ i, ⟪ξ i, η i⟫_ℂ := by
  rw [inner_def, PiLp.inner_apply]
  -- `∑ p, ⟪(euclideanEquiv (tprod ξ)) p, (euclideanEquiv (tprod η)) p⟫_ℂ`
  -- Rewrite each summand using `euclideanEquiv_tprod_ofLp`.
  have hcoord :
      ∀ p : (i : ι) → Fin (Module.finrank ℂ (H i)),
        ⟪(euclideanEquiv H (tprod ℂ ξ)) p,
            (euclideanEquiv H (tprod ℂ η)) p⟫_ℂ
          = ∏ i, ⟪ξ i, (stdONB H i) (p i)⟫_ℂ
              * ⟪(stdONB H i) (p i), η i⟫_ℂ := by
    intro p
    rw [RCLike.inner_apply' (𝕜 := ℂ)]
    rw [show ((euclideanEquiv H (tprod ℂ ξ)) p : ℂ)
            = (euclideanEquiv H (tprod ℂ ξ)).ofLp p from rfl,
        show ((euclideanEquiv H (tprod ℂ η)) p : ℂ)
            = (euclideanEquiv H (tprod ℂ η)).ofLp p from rfl]
    rw [euclideanEquiv_tprod_ofLp, euclideanEquiv_tprod_ofLp]
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (starRingEnd ℂ) ⟪(stdONB H i) (p i), ξ i⟫_ℂ
            = ⟪ξ i, (stdONB H i) (p i)⟫_ℂ from _root_.inner_conj_symm _ _]
  simp_rw [hcoord]
  -- `∑ p, ∏ i, ⟪ξ i, b_i (p i)⟫ * ⟪b_i (p i), η i⟫ = ∏ i, ∑ k, ⟪ξ i, b_i k⟫ * ⟪b_i k, η i⟫`
  -- Step 1: rewrite `Finset.univ` (on the Π-type) as `Fintype.piFinset (fun _ => Finset.univ)`.
  rw [← Fintype.piFinset_univ
        (β := fun i : ι => Fin (Module.finrank ℂ (H i)))]
  -- Step 2: swap `∑` and `∏`.
  rw [← Finset.prod_univ_sum (fun _ : ι => Finset.univ)
        (fun i k => ⟪ξ i, (stdONB H i) k⟫_ℂ * ⟪(stdONB H i) k, η i⟫_ℂ)]
  -- Step 3: apply Parseval per factor.
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (stdONB H i).sum_inner_mul_inner _ _

/-- The diagonal specialisation of `inner_tprod_tprod`:

`⟪⨂ ξ, ⨂ ξ⟫_ℂ = ∏ i, (‖ξ i‖ ^ 2 : ℂ)`. -/
theorem inner_self_tprod (ξ : (i : ι) → H i) :
    ⟪(tprod ℂ ξ : ⨂[ℂ] i, H i), (tprod ℂ ξ : ⨂[ℂ] i, H i)⟫_ℂ
      = ∏ i, ((‖ξ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_tprod_tprod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [@inner_self_eq_norm_sq_to_K ℂ]
  norm_cast

/-! ### Inner-product preservation under tensor product of linear isometries -/

variable {K : ι → Type*}
  [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
  [∀ i, FiniteDimensional ℂ (K i)]

/-- The pointwise tensor product of linear isometric equivalences preserves
inner products on finite tensor products. -/
theorem inner_congr_map_map (V : (i : ι) → (H i ≃ₗᵢ[ℂ] K i))
    (x y : ⨂[ℂ] i, H i) :
    ⟪_root_.PiTensorProduct.map (fun i => (V i).toLinearMap) x,
        _root_.PiTensorProduct.map (fun i => (V i).toLinearMap) y⟫_ℂ
      = ⟪x, y⟫_ℂ := by
  induction x using _root_.PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, inner_smul_left, inner_smul_left]
    congr 1
    induction y using _root_.PiTensorProduct.induction_on with
    | smul_tprod s η =>
      rw [map_smul, inner_smul_right, inner_smul_right]
      congr 1
      rw [_root_.PiTensorProduct.map_tprod, _root_.PiTensorProduct.map_tprod]
      rw [inner_tprod_tprod (H := K), inner_tprod_tprod (H := H)]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (V i).inner_map_map _ _
    | add y₁ y₂ ih₁ ih₂ =>
      rw [map_add, inner_add_right, inner_add_right, ih₁, ih₂]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add, inner_add_left, inner_add_left, ih₁, ih₂]

/-- Bundle `PiTensorProduct.congr` of pointwise linear isometric equivalences
into a `LinearIsometryEquiv` on finite tensor products. -/
noncomputable def piTensorCongrIsom
    (V : (i : ι) → (H i ≃ₗᵢ[ℂ] K i)) :
    (⨂[ℂ] i, H i) ≃ₗᵢ[ℂ] (⨂[ℂ] i, K i) :=
  { _root_.PiTensorProduct.congr (fun i => (V i).toLinearEquiv) with
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      apply congrArg RCLike.re
      have hcongr :
          ((_root_.PiTensorProduct.congr (fun i => (V i).toLinearEquiv)) x : ⨂[ℂ] i, K i)
            = _root_.PiTensorProduct.map (fun i => (V i).toLinearMap) x := by
        induction x using _root_.PiTensorProduct.induction_on with
        | smul_tprod r ξ =>
          rw [map_smul, _root_.PiTensorProduct.congr_tprod, map_smul,
            _root_.PiTensorProduct.map_tprod]
          rfl
        | add x₁ x₂ ih₁ ih₂ =>
          rw [map_add, map_add, ih₁, ih₂]
      rw [hcongr]
      exact inner_congr_map_map (H := H) (K := K) V x x }

@[simp]
theorem piTensorCongrIsom_tprod (V : (i : ι) → (H i ≃ₗᵢ[ℂ] K i))
    (ξ : (i : ι) → H i) :
    piTensorCongrIsom (H := H) (K := K) V (tprod ℂ ξ)
      = tprod ℂ (fun i => V i (ξ i)) := by
  change (_root_.PiTensorProduct.congr (fun i => (V i).toLinearEquiv)) (tprod ℂ ξ) = _
  rw [_root_.PiTensorProduct.congr_tprod]
  rfl

/-- Same-family specialization of `piTensorCongrIsom`. -/
noncomputable def piTensorMapIsom
    (V : (i : ι) → (H i ≃ₗᵢ[ℂ] H i)) :
    (⨂[ℂ] i, H i) ≃ₗᵢ[ℂ] (⨂[ℂ] i, H i) :=
  piTensorCongrIsom (H := H) (K := H) V

@[simp]
theorem piTensorMapIsom_tprod (V : (i : ι) → (H i ≃ₗᵢ[ℂ] H i))
    (ξ : (i : ι) → H i) :
    piTensorMapIsom (H := H) V (tprod ℂ ξ) = tprod ℂ (fun i => V i (ξ i)) := by
  exact piTensorCongrIsom_tprod (H := H) (K := H) V ξ

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι']

/-- Reindexing the tensor factors along an equivalence preserves the inner
product. -/
theorem inner_reindex_map_map (e : ι ≃ ι')
    (x y : ⨂[ℂ] i, H i) :
    ⟪(_root_.PiTensorProduct.reindex ℂ H e x : ⨂[ℂ] i' : ι', H (e.symm i')),
        _root_.PiTensorProduct.reindex ℂ H e y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x using _root_.PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, inner_smul_left, inner_smul_left]
    congr 1
    induction y using _root_.PiTensorProduct.induction_on with
    | smul_tprod s η =>
      rw [map_smul, inner_smul_right, inner_smul_right]
      congr 1
      rw [_root_.PiTensorProduct.reindex_tprod, _root_.PiTensorProduct.reindex_tprod]
      rw [inner_tprod_tprod, inner_tprod_tprod]
      simpa using (e.symm.prod_comp (fun i : ι => ⟪ξ i, η i⟫_ℂ))
    | add y₁ y₂ ih₁ ih₂ =>
      rw [map_add, inner_add_right, inner_add_right, ih₁, ih₂]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add, inner_add_left, inner_add_left, ih₁, ih₂]

/-- Reindex the tensor factors of `⨂[ℂ] i, H i` along an equivalence of the
index type. -/
noncomputable def piTensorReindexIsom (e : ι ≃ ι') :
    (⨂[ℂ] i, H i) ≃ₗᵢ[ℂ] (⨂[ℂ] i' : ι', H (e.symm i')) :=
  { _root_.PiTensorProduct.reindex ℂ H e with
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (inner_reindex_map_map (H := H) e x x) }

@[simp]
theorem piTensorReindexIsom_tprod (e : ι ≃ ι')
    (ξ : (i : ι) → H i) :
    piTensorReindexIsom (H := H) e (tprod ℂ ξ)
      = tprod ℂ (fun i' : ι' => ξ (e.symm i')) := by
  change (_root_.PiTensorProduct.reindex ℂ H e) (tprod ℂ ξ) = _
  rw [_root_.PiTensorProduct.reindex_tprod]

end PiTensorProduct

end ForMathlib
