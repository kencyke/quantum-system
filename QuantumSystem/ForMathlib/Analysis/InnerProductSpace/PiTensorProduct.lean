/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# The inner product on the tensor product of a finite family of inner product spaces

For a finite family `E i` of inner product spaces over `𝕜`, the tensor product `⨂[𝕜] i, E i` carries
the inner product `⟪⨂ x, ⨂ y⟫ = ∏ i, ⟪x i, y i⟫`. Mathlib already puts the projective seminorm on
`⨂[𝕜] i, E i`, which is not the norm of this inner product, so the inner product space is the type
synonym `InnerPiTensorProduct 𝕜 E`, identified with `⨂[𝕜] i, E i` by the linear equivalence
`InnerPiTensorProduct.linearEquiv`. For two factors it is Mathlib's inner product space
`E 0 ⊗[𝕜] E 1`, by the linear isometric equivalence `⨂ m ↦ m 0 ⊗ m 1`
(`InnerPiTensorProduct.linearIsometryEquivTensorProduct`).

The inner product is positive definite: every tensor lies in the tensor product of finite-dimensional
subspaces, where an orthonormal basis of each factor gives an orthonormal basis of the tensor
product.

Splitting the index set along a predicate `p` identifies the tensor product with the binary tensor
product of those over `p` and over `¬p`, isometrically. The tensor product `⨂ T i` of operators
`T i : E i →L F i` is bounded by `∏ ‖T i‖`: by induction on the number of factors, splitting off
one factor and bounding the binary tensor product of operators (`TensorProduct.norm_mapL_le`).

## Main definitions

* `PiTensorProduct.innerₛₗ` — the sesquilinear form `⟪⨂ x, ⨂ y⟫ = ∏ i, ⟪x i, y i⟫` on
  `⨂[𝕜] i, E i`.
* `InnerPiTensorProduct 𝕜 E` — `⨂[𝕜] i, E i` with this inner product, an inner product space.
* `InnerPiTensorProduct.linearEquiv` — the linear equivalence `(⨂[𝕜] i, E i) ≃ₗ[𝕜] InnerPiTensorProduct 𝕜 E`.
* `InnerPiTensorProduct.tprod 𝕜` — the pure tensor `⨂ m` of `InnerPiTensorProduct 𝕜 E`, multilinear
  in `m`: the image of `⨂ₜ[𝕜] i, m i` under `InnerPiTensorProduct.linearEquiv`.
* `PiTensorProduct.tmulFinTwoEquiv R M` — the tensor product over `Fin 2` as the binary tensor
  product, `⨂ m ↦ m 0 ⊗ m 1`; `InnerPiTensorProduct.linearIsometryEquivTensorProduct 𝕜 E` — the same
  as a linear isometric equivalence `InnerPiTensorProduct 𝕜 E ≃ₗᵢ[𝕜] E 0 ⊗[𝕜] E 1`.
* `PiTensorProduct.splitEquiv R M p` — splitting the index set along `p`,
  `⨂ m ↦ (⨂ m|ₚ) ⊗ (⨂ m|¬ₚ)`; `InnerPiTensorProduct.splitLinearIsometryEquiv 𝕜 E p` — the same as a
  linear isometric equivalence.
* `InnerPiTensorProduct.subsingletonLinearIsometryEquiv 𝕜 E i₀` — over a single index `i₀`, the
  linear isometric equivalence `InnerPiTensorProduct 𝕜 E ≃ₗᵢ[𝕜] E i₀`, `⨂ m ↦ m i₀`.
* `InnerPiTensorProduct.finsetSplitLinearIsometryEquiv 𝕜 H h` — for finite sets `s ⊆ t` of indices,
  the tensor product over `t` as the binary tensor product of those over `s` and over `t \ s`.
* `InnerPiTensorProduct.reindexLinearIsometryEquiv 𝕜 E e`,
  `InnerPiTensorProduct.congrLinearIsometryEquiv f` — reindexing along `e : ι ≃ κ` and changing the
  factors along linear isometric equivalences.
* `InnerPiTensorProduct.mapL T` — the tensor product `⨂ T i` of operators `T i : E i →L[𝕜] F i`;
  `InnerPiTensorProduct.mapLMultilinear 𝕜 E F` — the same, multilinear in `T`.

## Main results

* `InnerPiTensorProduct.inner_tprod` — `⟪⨂ x, ⨂ y⟫ = ∏ i, ⟪x i, y i⟫`.
* `InnerPiTensorProduct.norm_tprod` — `‖⨂ x‖ = ∏ i, ‖x i‖`.
* `InnerPiTensorProduct.norm_mapₗ_le`, `InnerPiTensorProduct.norm_mapL_le` — `⨂ T` is bounded by
  `∏ ‖T i‖`: `‖(⨂ T) x‖ ≤ (∏ ‖T i‖) * ‖x‖` and `‖⨂ T i‖ ≤ ∏ ‖T i‖`.
* `InnerPiTensorProduct.mapL_comp`, `InnerPiTensorProduct.mapL_id` — `⨂` is functorial.
* `InnerPiTensorProduct.inner_mapL_adjoint` — the formal adjoint of `⨂ T i` is `⨂ T i†`.
* `InnerPiTensorProduct.splitLinearIsometryEquiv_mapL` — splitting the index set intertwines `⨂ T`
  with `(⨂ T|ₚ) ⊗ (⨂ T|¬ₚ)`; `InnerPiTensorProduct.subsingletonLinearIsometryEquiv_mapL` — over a
  single index `i₀`, `⨂ T` is `T i₀`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace PiTensorProduct

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)]

/-! ### The sesquilinear form -/

variable (𝕜) in
/-- The linear form `y ↦ ∏ i, ⟪m i, y i⟫` on `⨂[𝕜] i, E i`. -/
noncomputable def innerTprod (m : Π i, E i) : (⨂[𝕜] i, E i) →ₗ[𝕜] 𝕜 :=
  lift ((MultilinearMap.mkPiAlgebra 𝕜 ι 𝕜).compLinearMap fun i => innerₛₗ 𝕜 (m i))

/-- `innerTprod 𝕜 m` sends `⨂ n` to `∏ i, ⟪m i, n i⟫`. -/
@[simp] lemma innerTprod_tprod (m n : Π i, E i) :
    innerTprod 𝕜 m (tprod 𝕜 n) = ∏ i, ⟪m i, n i⟫_𝕜 := by
  simp [innerTprod]

/-- The linear form of a family with one coordinate replaced, on a pure tensor. -/
lemma innerTprod_update_tprod [DecidableEq ι] (m : Π i, E i) (i : ι) (a : E i)
    (y : Π i, E i) :
    innerTprod 𝕜 (Function.update m i a) (tprod 𝕜 y) =
      ⟪a, y i⟫_𝕜 * ∏ j ∈ Finset.univ \ {i}, ⟪m j, y j⟫_𝕜 := by
  rw [innerTprod_tprod]
  have h : (fun j => ⟪Function.update m i a j, y j⟫_𝕜) =
      Function.update (fun j => ⟪m j, y j⟫_𝕜) i ⟪a, y i⟫_𝕜 := by
    funext j
    exact Function.apply_update (fun j x => ⟪x, y j⟫_𝕜) m i a j
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ i)]

/-- The linear form `innerTprod 𝕜 m` is additive in each coordinate of `m`. -/
lemma innerTprod_update_add [DecidableEq ι] (m : Π i, E i) (i : ι) (a b : E i) :
    innerTprod 𝕜 (Function.update m i (a + b)) =
      innerTprod 𝕜 (Function.update m i a) + innerTprod 𝕜 (Function.update m i b) :=
  PiTensorProduct.ext <| MultilinearMap.ext fun y => by
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, innerTprod_update_tprod,
      inner_add_left, add_mul]

/-- The linear form `innerTprod 𝕜 m` is conjugate-homogeneous in each coordinate of `m`. -/
lemma innerTprod_update_smul [DecidableEq ι] (m : Π i, E i) (i : ι) (c : 𝕜) (a : E i) :
    innerTprod 𝕜 (Function.update m i (c • a)) = conj c • innerTprod 𝕜 (Function.update m i a) :=
  PiTensorProduct.ext <| MultilinearMap.ext fun y => by
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, innerTprod_update_tprod,
      inner_smul_left, smul_eq_mul, mul_assoc]

/-- The linear form `innerTprod 𝕜 m` vanishes when a coordinate of `m` does. -/
lemma innerTprod_of_eq_zero (m : Π i, E i) (i : ι) (hm : m i = 0) : innerTprod 𝕜 m = 0 :=
  PiTensorProduct.ext <| MultilinearMap.ext fun y => by
    simp only [LinearMap.compMultilinearMap_apply, innerTprod_tprod, LinearMap.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hm, inner_zero_left])

/-- The additive map `x ↦ ⟪x, ·⟫` on `⨂[𝕜] i, E i`, conjugate-linear in `x`. -/
noncomputable def innerAddHom : (⨂[𝕜] i, E i) →+ (⨂[𝕜] i, E i) →ₗ[𝕜] 𝕜 :=
  liftAddHom (fun p => conj p.1 • innerTprod 𝕜 p.2)
    (fun r m i hm => by rw [innerTprod_of_eq_zero m i hm, smul_zero])
    (fun m => by rw [map_zero, zero_smul])
    (fun r m i a b => by rw [innerTprod_update_add, smul_add])
    (fun r r' m => by rw [map_add, add_smul])
    (fun r m i r' => by
      rw [innerTprod_update_smul, Function.update_eq_self, smul_smul, map_mul, mul_comm])

/-- `innerAddHom` sends `r • ⨂ m` to `conj r • innerTprod 𝕜 m`. -/
lemma innerAddHom_tprodCoeff (r : 𝕜) (m : Π i, E i) :
    innerAddHom (tprodCoeff 𝕜 r m) = conj r • innerTprod 𝕜 m :=
  rfl

/-- The additive map `PiTensorProduct.innerAddHom` is conjugate-linear. -/
lemma innerAddHom_smul (c : 𝕜) (x : ⨂[𝕜] i, E i) :
    innerAddHom (c • x) = conj c • innerAddHom x := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r m =>
    rw [smul_tprodCoeff', innerAddHom_tprodCoeff, innerAddHom_tprodCoeff, smul_eq_mul, map_mul,
      mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The **sesquilinear form** `⟪⨂ x, ⨂ y⟫ = ∏ i, ⟪x i, y i⟫` on `⨂[𝕜] i, E i`, conjugate-linear in
the first argument. -/
noncomputable def innerₛₗ : (⨂[𝕜] i, E i) →ₗ⋆[𝕜] (⨂[𝕜] i, E i) →ₗ[𝕜] 𝕜 where
  toFun := innerAddHom
  map_add' := map_add innerAddHom
  map_smul' := innerAddHom_smul

/-- `⟪⨂ x, ⨂ y⟫ = ∏ i, ⟪x i, y i⟫`. -/
@[simp] lemma innerₛₗ_tprod (x y : Π i, E i) :
    innerₛₗ (tprod 𝕜 x) (tprod 𝕜 y) = ∏ i, ⟪x i, y i⟫_𝕜 := by
  change innerAddHom (tprod 𝕜 x) (tprod 𝕜 y) = _
  rw [tprod_eq_tprodCoeff_one, innerAddHom_tprodCoeff, map_one, one_smul, ← tprod_eq_tprodCoeff_one,
    innerTprod_tprod]

/-- The sesquilinear form is conjugate-symmetric. -/
lemma conj_innerₛₗ (x y : ⨂[𝕜] i, E i) : conj (innerₛₗ y x) = innerₛₗ x y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' n =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, innerₛₗ_tprod, smul_eq_mul, map_mul,
        map_prod, inner_conj_symm, RCLike.conj_conj]
      ring
    | add y y' hy hy' => rw [map_add, LinearMap.add_apply, map_add, hy, hy', map_add]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, LinearMap.add_apply]

/-! ### Positivity -/

/-- The inclusions of subspaces preserve the sesquilinear form. -/
lemma innerₛₗ_mapIncl (p : Π i, Submodule 𝕜 (E i)) (x y : ⨂[𝕜] i, p i) :
    innerₛₗ (mapIncl p x) (mapIncl p y) = innerₛₗ x y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' n => simp [Submodule.coe_inner]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

omit [Fintype ι] in
/-- Every tensor lies in the tensor product of finite-dimensional subspaces. -/
lemma exists_finiteDimensional (x : ⨂[𝕜] i, E i) :
    ∃ p : Π i, Submodule 𝕜 (E i), (∀ i, FiniteDimensional 𝕜 (p i)) ∧
      ∃ y : ⨂[𝕜] i, p i, mapIncl p y = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨fun i => 𝕜 ∙ m i, fun i => inferInstance,
      r • tprod 𝕜 fun i => ⟨m i, Submodule.mem_span_singleton_self _⟩, ?_⟩
    simp
  | add x x' hx hx' =>
    obtain ⟨p, hp, y, rfl⟩ := hx
    obtain ⟨q, hq, y', rfl⟩ := hx'
    refine ⟨fun i => p i ⊔ q i, fun i => inferInstance,
      map (fun i => Submodule.inclusion (le_sup_left : p i ≤ p i ⊔ q i)) y +
        map (fun i => Submodule.inclusion (le_sup_right : q i ≤ p i ⊔ q i)) y', ?_⟩
    simp only [map_add, mapIncl, ← LinearMap.comp_apply, ← map_comp, Submodule.subtype_comp_inclusion]

section FiniteDimensional

variable [∀ i, FiniteDimensional 𝕜 (E i)]

open Classical in
/-- The orthonormal basis of `⨂[𝕜] i, E i` made of the tensor products of standard orthonormal
bases of the factors, as a basis. -/
private noncomputable def stdBasis : Module.Basis (Π i, Fin (Module.finrank 𝕜 (E i))) 𝕜 (⨂[𝕜] i, E i) :=
  Basis.piTensorProduct fun i => (stdOrthonormalBasis 𝕜 (E i)).toBasis

open Classical in
private lemma innerₛₗ_stdBasis (k l : Π i, Fin (Module.finrank 𝕜 (E i))) :
    innerₛₗ (stdBasis (𝕜 := 𝕜) (E := E) k) (stdBasis l) = if k = l then 1 else 0 := by
  rw [stdBasis, Basis.piTensorProduct_apply, Basis.piTensorProduct_apply, innerₛₗ_tprod]
  simp only [OrthonormalBasis.coe_toBasis, orthonormal_iff_ite.1 (stdOrthonormalBasis 𝕜 _).orthonormal]
  rw [Finset.prod_boole]
  simp [funext_iff]

open Classical in
private lemma innerₛₗ_self_eq_sum (x : ⨂[𝕜] i, E i) :
    innerₛₗ x x = ∑ k, ((‖stdBasis.repr x k‖ ^ 2 : ℝ) : 𝕜) := by
  conv_lhs => rw [← (stdBasis (𝕜 := 𝕜) (E := E)).sum_repr x]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, innerₛₗ_stdBasis,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, RingHom.id_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [RCLike.mul_conj]

private lemma re_innerₛₗ_self_nonneg_of_finiteDimensional (x : ⨂[𝕜] i, E i) :
    0 ≤ RCLike.re (innerₛₗ x x) := by
  classical
  rw [innerₛₗ_self_eq_sum, map_sum]
  exact Finset.sum_nonneg fun k _ => by rw [RCLike.ofReal_re]; positivity

private lemma eq_zero_of_innerₛₗ_self_of_finiteDimensional (x : ⨂[𝕜] i, E i)
    (hx : innerₛₗ x x = 0) : x = 0 := by
  classical
  rw [innerₛₗ_self_eq_sum, ← RCLike.ofReal_sum, RCLike.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at hx
  refine (stdBasis (𝕜 := 𝕜) (E := E)).ext_elem fun k => ?_
  simpa using hx k (Finset.mem_univ k)

end FiniteDimensional

/-- The sesquilinear form is positive: `0 ≤ re ⟪x, x⟫`. -/
lemma re_innerₛₗ_self_nonneg (x : ⨂[𝕜] i, E i) : 0 ≤ RCLike.re (innerₛₗ x x) := by
  obtain ⟨p, hp, y, rfl⟩ := exists_finiteDimensional x
  rw [innerₛₗ_mapIncl]
  exact re_innerₛₗ_self_nonneg_of_finiteDimensional y

/-- The sesquilinear form is definite: `⟪x, x⟫ = 0` only for `x = 0`. -/
lemma eq_zero_of_innerₛₗ_self (x : ⨂[𝕜] i, E i) (hx : innerₛₗ x x = 0) : x = 0 := by
  obtain ⟨p, hp, y, rfl⟩ := exists_finiteDimensional x
  rw [innerₛₗ_mapIncl] at hx
  rw [eq_zero_of_innerₛₗ_self_of_finiteDimensional y hx, map_zero]

end PiTensorProduct

/-! ### The inner product space -/

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)]

variable (𝕜 E) in
/-- The tensor product `⨂[𝕜] i, E i` of a finite family of inner product spaces, with the inner
product `⟪⨂ x, ⨂ y⟫ = ∏ i, ⟪x i, y i⟫`: a type synonym, as Mathlib puts the projective seminorm on
`⨂[𝕜] i, E i`. -/
def InnerPiTensorProduct : Type _ :=
  ⨂[𝕜] i, E i

namespace InnerPiTensorProduct

/-- The additive group structure of `⨂[𝕜] i, E i`. -/
noncomputable instance : AddCommGroup (InnerPiTensorProduct 𝕜 E) :=
  inferInstanceAs (AddCommGroup (⨂[𝕜] i, E i))

/-- The module structure of `⨂[𝕜] i, E i`. -/
noncomputable instance : Module 𝕜 (InnerPiTensorProduct 𝕜 E) :=
  inferInstanceAs (Module 𝕜 (⨂[𝕜] i, E i))

variable (𝕜 E) in
/-- The identification of `⨂[𝕜] i, E i` with `InnerPiTensorProduct 𝕜 E`. -/
def linearEquiv : (⨂[𝕜] i, E i) ≃ₗ[𝕜] InnerPiTensorProduct 𝕜 E :=
  LinearEquiv.refl 𝕜 _

variable (𝕜) in
/-- The pure tensor `⨂ m` of `InnerPiTensorProduct 𝕜 E`, multilinear in `m`. -/
noncomputable def tprod : MultilinearMap 𝕜 E (InnerPiTensorProduct 𝕜 E) :=
  (linearEquiv 𝕜 E).toLinearMap.compMultilinearMap (PiTensorProduct.tprod 𝕜)

omit [Fintype ι] in
/-- The pure tensor of `InnerPiTensorProduct 𝕜 E` is that of `⨂[𝕜] i, E i`, read through
`InnerPiTensorProduct.linearEquiv`. -/
@[simp] lemma linearEquiv_tprod (m : Π i, E i) : linearEquiv 𝕜 E (⨂ₜ[𝕜] i, m i) = tprod 𝕜 m :=
  rfl

/-- The inner product of `InnerPiTensorProduct 𝕜 E`: the sesquilinear form
`PiTensorProduct.innerₛₗ`. -/
noncomputable instance : Inner 𝕜 (InnerPiTensorProduct 𝕜 E) where
  inner x y := PiTensorProduct.innerₛₗ ((linearEquiv 𝕜 E).symm x) ((linearEquiv 𝕜 E).symm y)

/-- The inner product of `InnerPiTensorProduct 𝕜 E` is `PiTensorProduct.innerₛₗ`. -/
lemma inner_linearEquiv (x y : ⨂[𝕜] i, E i) :
    ⟪linearEquiv 𝕜 E x, linearEquiv 𝕜 E y⟫_𝕜 = PiTensorProduct.innerₛₗ x y :=
  rfl

/-- The norm of `InnerPiTensorProduct 𝕜 E`, that of its inner product, which is positive
definite. -/
noncomputable instance : NormedAddCommGroup (InnerPiTensorProduct 𝕜 E) :=
  letI : InnerProductSpace.Core 𝕜 (InnerPiTensorProduct 𝕜 E) :=
    { conj_inner_symm x y := PiTensorProduct.conj_innerₛₗ ((linearEquiv 𝕜 E).symm x) ((linearEquiv 𝕜 E).symm y)
      add_left x y z := by
        change PiTensorProduct.innerₛₗ ((linearEquiv 𝕜 E).symm (x + y)) ((linearEquiv 𝕜 E).symm z) = _
        rw [map_add, map_add, LinearMap.add_apply]
        rfl
      smul_left x y r := by
        change PiTensorProduct.innerₛₗ ((linearEquiv 𝕜 E).symm (r • x)) ((linearEquiv 𝕜 E).symm y) = _
        rw [LinearEquiv.map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
        rfl
      re_inner_nonneg x := PiTensorProduct.re_innerₛₗ_self_nonneg ((linearEquiv 𝕜 E).symm x)
      definite x hx := PiTensorProduct.eq_zero_of_innerₛₗ_self ((linearEquiv 𝕜 E).symm x) hx }
  this.toNormedAddCommGroup

/-- `InnerPiTensorProduct 𝕜 E` is an inner product space. -/
noncomputable instance : InnerProductSpace 𝕜 (InnerPiTensorProduct 𝕜 E) :=
  .ofCore _

/-- `⟪⨂ x, ⨂ y⟫ = ∏ i, ⟪x i, y i⟫`. -/
@[simp] theorem inner_tprod (x y : Π i, E i) :
    ⟪tprod 𝕜 x, tprod 𝕜 y⟫_𝕜 = ∏ i, ⟪x i, y i⟫_𝕜 :=
  PiTensorProduct.innerₛₗ_tprod x y

/-- `‖⨂ x‖ = ∏ i, ‖x i‖`. -/
@[simp] theorem norm_tprod (x : Π i, E i) :
    ‖tprod 𝕜 x‖ = ∏ i, ‖x i‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)).1 ?_
  rw [@norm_sq_eq_re_inner 𝕜, inner_tprod, ← Finset.prod_pow]
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, ← RCLike.ofReal_prod, RCLike.ofReal_re]

omit [Fintype ι] in
/-- The tensor product of nontrivial inner product spaces is nontrivial: a tensor product of
nonzero vectors has nonzero norm. -/
instance [Finite ι] [∀ i, Nontrivial (E i)] : Nontrivial (InnerPiTensorProduct 𝕜 E) := by
  have := Fintype.ofFinite ι
  choose v hv using fun i => exists_ne (0 : E i)
  refine ⟨⟨tprod 𝕜 v, 0, fun h => ?_⟩⟩
  have hn := norm_tprod (𝕜 := 𝕜) v
  rw [h, norm_zero] at hn
  exact Finset.prod_ne_zero_iff.2 (fun i _ => norm_ne_zero_iff.2 (hv i)) hn.symm

end InnerPiTensorProduct

/-! ### Two factors -/

namespace PiTensorProduct

section FinTwo

variable {R : Type*} [CommSemiring R] {M₂ : Fin 2 → Type*} [∀ i, AddCommMonoid (M₂ i)]
  [∀ i, Module R (M₂ i)]

/-- The multilinear map `m ↦ m 0 ⊗ m 1` on two factors. -/
noncomputable def tmulFinTwoMultilinear : MultilinearMap R M₂ (M₂ 0 ⊗[R] M₂ 1) where
  toFun m := m 0 ⊗ₜ m 1
  map_update_add' m i x y := by
    fin_cases i
    · simp [TensorProduct.add_tmul]
    · simp [TensorProduct.tmul_add]
  map_update_smul' m i c x := by
    fin_cases i
    · simp [TensorProduct.smul_tmul']
    · simp [TensorProduct.tmul_smul]

/-- The bilinear map `a, b ↦ ⨂ ![a, b]` into the tensor product over `Fin 2`. -/
noncomputable def tprodFinTwo : M₂ 0 →ₗ[R] M₂ 1 →ₗ[R] ⨂[R] i, M₂ i :=
  LinearMap.mk₂ R (fun a b => tprod R (Fin.cons a (Fin.cons b finZeroElim) : Π i, M₂ i))
    (fun a a' _ => (tprod R).cons_add _ a a')
    (fun c a _ => (tprod R).cons_smul _ c a)
    (fun a b b' => ((tprod R).curryLeft a).cons_add finZeroElim b b')
    (fun c a b => ((tprod R).curryLeft a).cons_smul finZeroElim c b)

variable (R M₂) in
/-- **The tensor product over `Fin 2` is the binary tensor product**: the linear equivalence
`⨂ m ↦ m 0 ⊗ m 1`. -/
noncomputable def tmulFinTwoEquiv : (⨂[R] i, M₂ i) ≃ₗ[R] M₂ 0 ⊗[R] M₂ 1 :=
  LinearEquiv.ofLinearMap (lift tmulFinTwoMultilinear) (TensorProduct.lift (tprodFinTwo (R := R)))
    (TensorProduct.ext' fun a b => by
      change lift tmulFinTwoMultilinear (tprod R (Fin.cons a (Fin.cons b finZeroElim) : Π i, M₂ i)) =
        a ⊗ₜ b
      rw [lift.tprod]
      rfl)
    (PiTensorProduct.ext <| MultilinearMap.ext fun m => by
      change TensorProduct.lift (tprodFinTwo (R := R)) (lift tmulFinTwoMultilinear (tprod R m)) = tprod R m
      rw [lift.tprod]
      change tprod R (Fin.cons (m 0) (Fin.cons (m 1) finZeroElim) : Π i, M₂ i) = _
      congr 1
      funext i
      fin_cases i <;> rfl)

/-- `PiTensorProduct.tmulFinTwoEquiv R M` sends `⨂ m` to `m 0 ⊗ m 1`. -/
@[simp] lemma tmulFinTwoEquiv_tprod (m : Π i, M₂ i) :
    tmulFinTwoEquiv R M₂ (tprod R m) = m 0 ⊗ₜ m 1 :=
  lift.tprod m

/-- `(PiTensorProduct.tmulFinTwoEquiv R M).symm` sends `a ⊗ b` to `⨂ ![a, b]`. -/
@[simp] lemma tmulFinTwoEquiv_symm_tmul (a : M₂ 0) (b : M₂ 1) :
    (tmulFinTwoEquiv R M₂).symm (a ⊗ₜ b) =
      tprod R (Fin.cons a (Fin.cons b finZeroElim) : Π i, M₂ i) := by
  rw [LinearEquiv.symm_apply_eq, tmulFinTwoEquiv_tprod]
  rfl

end FinTwo

end PiTensorProduct

namespace InnerPiTensorProduct

variable {E₂ : Fin 2 → Type*} [∀ i, NormedAddCommGroup (E₂ i)] [∀ i, InnerProductSpace 𝕜 (E₂ i)]

variable (𝕜 E₂) in
/-- **For two factors, `InnerPiTensorProduct` is Mathlib's inner product space `E 0 ⊗[𝕜] E 1`**:
the identification `⨂ m ↦ m 0 ⊗ m 1` preserves the inner product,
`⟪⨂ m, ⨂ n⟫ = ⟪m 0, n 0⟫ * ⟪m 1, n 1⟫ = ⟪m 0 ⊗ m 1, n 0 ⊗ n 1⟫`. -/
noncomputable def linearIsometryEquivTensorProduct :
    InnerPiTensorProduct 𝕜 E₂ ≃ₗᵢ[𝕜] E₂ 0 ⊗[𝕜] E₂ 1 :=
  ((linearEquiv 𝕜 E₂).symm.trans (PiTensorProduct.tmulFinTwoEquiv 𝕜 E₂)).isometryOfInner
    fun x y => by
      obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E₂).surjective x
      obtain ⟨y, rfl⟩ := (linearEquiv 𝕜 E₂).surjective y
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply, inner_linearEquiv]
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' n =>
          simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
            PiTensorProduct.tmulFinTwoEquiv_tprod, TensorProduct.inner_tmul,
            PiTensorProduct.innerₛₗ_tprod, Fin.prod_univ_two, smul_eq_mul]
        | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
      | add x x' hx hx' => simp only [map_add, inner_add_left, LinearMap.add_apply, hx, hx']

/-- `InnerPiTensorProduct.linearIsometryEquivTensorProduct 𝕜 E` sends `⨂ m` to `m 0 ⊗ m 1`. -/
@[simp] lemma linearIsometryEquivTensorProduct_tprod (m : Π i, E₂ i) :
    linearIsometryEquivTensorProduct 𝕜 E₂ (tprod 𝕜 m) = m 0 ⊗ₜ m 1 :=
  PiTensorProduct.tmulFinTwoEquiv_tprod m

end InnerPiTensorProduct

/-! ### Splitting the index set -/

namespace PiTensorProduct

section Split

variable {R : Type*} [CommSemiring R] {M N : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (p : ι → Prop)
  [DecidablePred p]

omit [Fintype ι] in
variable (R M) in
/-- Splitting the index set along `p`: the linear equivalence `⨂ m ↦ (⨂ m|ₚ) ⊗ (⨂ m|¬ₚ)`. -/
noncomputable def splitEquiv :
    (⨂[R] i, M i) ≃ₗ[R] (⨂[R] i : {i // p i}, M i) ⊗[R] (⨂[R] i : {i // ¬p i}, M i) :=
  (reindex R M (Equiv.sumCompl p).symm).trans <|
    (tmulEquivDep R fun j => M ((Equiv.sumCompl p).symm.symm j)).symm.trans <|
      TensorProduct.congr (PiTensorProduct.congr fun i => LinearEquiv.refl R (M i))
        (PiTensorProduct.congr fun i => LinearEquiv.refl R (M i))

omit [Fintype ι] in
/-- `PiTensorProduct.splitEquiv R M p` sends `⨂ m` to `(⨂ m|ₚ) ⊗ (⨂ m|¬ₚ)`. -/
@[simp] lemma splitEquiv_tprod (m : Π i, M i) :
    splitEquiv R M p (tprod R m) =
      tprod R (fun i : {i // p i} => m i) ⊗ₜ tprod R (fun i : {i // ¬p i} => m i) := by
  rw [splitEquiv, LinearEquiv.trans_apply, reindex_tprod, LinearEquiv.trans_apply,
    tmulEquivDep_symm_apply, TensorProduct.congr_tmul]
  exact congrArg₂ (· ⊗ₜ ·) (congr_tprod _ _) (congr_tprod _ _)

omit [Fintype ι] in
/-- Splitting the index set intertwines `⨂ f` with `(⨂ f|ₚ) ⊗ (⨂ f|¬ₚ)`. -/
lemma splitEquiv_map (f : Π i, M i →ₗ[R] N i) (x : ⨂[R] i, M i) :
    splitEquiv R N p (map f x) =
      TensorProduct.map (map fun i : {i // p i} => f i) (map fun i : {i // ¬p i} => f i)
        (splitEquiv R M p x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Split

end PiTensorProduct

variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]

namespace InnerPiTensorProduct

variable (𝕜 E) (p : ι → Prop) [DecidablePred p] in
/-- **Splitting the index set** along `p` is a linear isometric equivalence
`InnerPiTensorProduct 𝕜 E ≃ₗᵢ (InnerPiTensorProduct over p) ⊗ (InnerPiTensorProduct over ¬p)`,
`⨂ m ↦ (⨂ m|ₚ) ⊗ (⨂ m|¬ₚ)`. -/
noncomputable def splitLinearIsometryEquiv :
    InnerPiTensorProduct 𝕜 E ≃ₗᵢ[𝕜]
      InnerPiTensorProduct 𝕜 (fun i : {i // p i} => E i) ⊗[𝕜]
        InnerPiTensorProduct 𝕜 (fun i : {i // ¬p i} => E i) :=
  ((linearEquiv 𝕜 E).symm.trans ((PiTensorProduct.splitEquiv 𝕜 E p).trans
    (TensorProduct.congr (linearEquiv 𝕜 _) (linearEquiv 𝕜 _)))).isometryOfInner fun x y => by
      obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
      obtain ⟨y, rfl⟩ := (linearEquiv 𝕜 E).surjective y
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, inner_linearEquiv]
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' n =>
          simp only [map_smul, PiTensorProduct.splitEquiv_tprod, TensorProduct.congr_tmul]
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.inner_tmul,
            ← (linearEquiv 𝕜 _).map_smul r, ← (linearEquiv 𝕜 _).map_smul r', inner_linearEquiv,
            inner_linearEquiv]
          simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, PiTensorProduct.innerₛₗ_tprod,
            smul_eq_mul]
          rw [← Fintype.prod_subtype_mul_prod_subtype p fun i => ⟪m i, n i⟫_𝕜]
          ring
        | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
      | add x x' hx hx' => simp only [map_add, inner_add_left, LinearMap.add_apply, hx, hx']

/-- `InnerPiTensorProduct.splitLinearIsometryEquiv 𝕜 E p` sends `⨂ m` to `(⨂ m|ₚ) ⊗ (⨂ m|¬ₚ)`. -/
@[simp] lemma splitLinearIsometryEquiv_tprod (p : ι → Prop) [DecidablePred p] (m : Π i, E i) :
    splitLinearIsometryEquiv 𝕜 E p (tprod 𝕜 m) =
      tprod 𝕜 (fun i : {i // p i} => m i) ⊗ₜ tprod 𝕜 (fun i : {i // ¬p i} => m i) := by
  simp only [← linearEquiv_tprod]
  simp [splitLinearIsometryEquiv, -linearEquiv_tprod]

/-! ### Tensor products of operators -/

omit [Fintype ι] in
/-- The tensor product `⨂ f i` of linear maps, between the inner product spaces:
`PiTensorProduct.map f` read through `InnerPiTensorProduct.linearEquiv`. -/
noncomputable def mapₗ (f : Π i, E i →ₗ[𝕜] F i) :
    InnerPiTensorProduct 𝕜 E →ₗ[𝕜] InnerPiTensorProduct 𝕜 F :=
  (linearEquiv 𝕜 F).toLinearMap ∘ₗ PiTensorProduct.map f ∘ₗ (linearEquiv 𝕜 E).symm.toLinearMap

omit [Fintype ι] in
/-- `mapₗ f` sends `⨂ m` to `⨂ (f i (m i))`. -/
@[simp] lemma mapₗ_tprod (f : Π i, E i →ₗ[𝕜] F i) (m : Π i, E i) :
    mapₗ f (tprod 𝕜 m) = tprod 𝕜 fun i => f i (m i) := by
  simp only [← linearEquiv_tprod]
  simp [mapₗ, -linearEquiv_tprod]

/-- Splitting the index set intertwines `⨂ f` with `(⨂ f|ₚ) ⊗ (⨂ f|¬ₚ)`. -/
lemma splitLinearIsometryEquiv_mapₗ (p : ι → Prop) [DecidablePred p] (f : Π i, E i →ₗ[𝕜] F i)
    (x : InnerPiTensorProduct 𝕜 E) :
    splitLinearIsometryEquiv 𝕜 F p (mapₗ f x) =
      TensorProduct.map (mapₗ fun i : {i // p i} => f i) (mapₗ fun i : {i // ¬p i} => f i)
        (splitLinearIsometryEquiv 𝕜 E p x) := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On a subsingleton index type every tensor is a pure tensor, so `⨂ T` is bounded by `∏ ‖T i‖`. -/
private lemma norm_mapₗ_le_of_subsingleton [Subsingleton ι] (T : Π i, E i →L[𝕜] F i)
    (x : InnerPiTensorProduct 𝕜 E) :
    ‖mapₗ (fun i => (T i).toLinearMap) x‖ ≤ (∏ i, ‖T i‖) * ‖x‖ := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · obtain ⟨c, rfl⟩ := (PiTensorProduct.isEmptyEquiv (R := 𝕜) (s := E)).symm.surjective x
    simp [PiTensorProduct.isEmptyEquiv, norm_smul]
  · obtain ⟨y, rfl⟩ := (PiTensorProduct.subsingletonEquiv (R := 𝕜) (s := E) i₀).symm.surjective x
    rw [PiTensorProduct.subsingletonEquiv_symm_apply, linearEquiv_tprod, mapₗ_tprod, norm_tprod,
      norm_tprod, Fintype.prod_subsingleton _ i₀, Fintype.prod_subsingleton _ i₀,
      Fintype.prod_subsingleton _ i₀, Function.update_self]
    exact (T i₀).le_opNorm y

/-- **`⨂ T` is bounded by `∏ ‖T i‖`**: by induction on the number of factors, splitting off one
factor and bounding the binary tensor product of operators. -/
theorem norm_mapₗ_le (T : Π i, E i →L[𝕜] F i) (x : InnerPiTensorProduct 𝕜 E) :
    ‖mapₗ (fun i => (T i).toLinearMap) x‖ ≤ (∏ i, ‖T i‖) * ‖x‖ := by
  induction h : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | _ n ih =>
  rcases subsingleton_or_nontrivial ι with hι | hι
  · exact norm_mapₗ_le_of_subsingleton T x
  classical
  obtain ⟨i₀⟩ : Nonempty ι := inferInstance
  obtain ⟨j, hj⟩ := exists_ne i₀
  -- a predicate with no special `Fintype` instance on its subtype
  obtain ⟨p, hp⟩ : ∃ p : ι → Prop, p = (· = i₀) := ⟨_, rfl⟩
  have h₁ : Fintype.card {i // p i} < n := h ▸ Fintype.card_subtype_lt (p := p) (by simpa [hp])
  have h₂ : Fintype.card {i // ¬p i} < n :=
    h ▸ Fintype.card_subtype_lt (p := fun i => ¬p i) (x := i₀) (by simp [hp])
  let S₁ := (mapₗ fun i : {i // p i} => (T i).toLinearMap).mkContinuous _
    (ih _ h₁ (fun i : {i // p i} => T i) · rfl)
  let S₂ := (mapₗ fun i : {i // ¬p i} => (T i).toLinearMap).mkContinuous _
    (ih _ h₂ (fun i : {i // ¬p i} => T i) · rfl)
  have hS₁ : ‖S₁‖ ≤ ∏ i : {i // p i}, ‖T i‖ :=
    LinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) _
  have hS₂ : ‖S₂‖ ≤ ∏ i : {i // ¬p i}, ‖T i‖ :=
    LinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) _
  calc ‖mapₗ (fun i => (T i).toLinearMap) x‖
      = ‖TensorProduct.mapL S₁ S₂ (splitLinearIsometryEquiv 𝕜 E p x)‖ := by
        rw [← (splitLinearIsometryEquiv 𝕜 F p).norm_map, splitLinearIsometryEquiv_mapₗ,
          TensorProduct.mapL_apply]
        rfl
    _ ≤ ‖S₁‖ * ‖S₂‖ * ‖x‖ := by
        refine ((TensorProduct.mapL S₁ S₂).le_opNorm _).trans ?_
        rw [LinearIsometryEquiv.norm_map]
        gcongr
        exact TensorProduct.norm_mapL_le S₁ S₂
    _ ≤ (∏ i, ‖T i‖) * ‖x‖ := by
        rw [← Fintype.prod_subtype_mul_prod_subtype p fun i => ‖T i‖]
        gcongr

/-- The **tensor product `⨂ T i` of operators** between the inner product spaces,
`⨂ m ↦ ⨂ (T i (m i))`, bounded by `∏ ‖T i‖` (`InnerPiTensorProduct.norm_mapL_le`). -/
noncomputable def mapL (T : Π i, E i →L[𝕜] F i) :
    InnerPiTensorProduct 𝕜 E →L[𝕜] InnerPiTensorProduct 𝕜 F :=
  (mapₗ fun i => (T i).toLinearMap).mkContinuous (∏ i, ‖T i‖) (norm_mapₗ_le T)

/-- `mapL T` is `mapₗ T` as a linear map. -/
lemma coe_mapL (T : Π i, E i →L[𝕜] F i) :
    (mapL T : InnerPiTensorProduct 𝕜 E →ₗ[𝕜] InnerPiTensorProduct 𝕜 F) =
      mapₗ fun i => (T i).toLinearMap :=
  rfl

/-- `mapL T` sends `⨂ m` to `⨂ (T i (m i))`. -/
@[simp] lemma mapL_tprod (T : Π i, E i →L[𝕜] F i) (m : Π i, E i) :
    mapL T (tprod 𝕜 m) = tprod 𝕜 fun i => T i (m i) :=
  mapₗ_tprod _ m

/-- `‖⨂ T i‖ ≤ ∏ ‖T i‖`. -/
theorem norm_mapL_le (T : Π i, E i →L[𝕜] F i) : ‖mapL T‖ ≤ ∏ i, ‖T i‖ :=
  LinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) _

omit [Fintype ι] in
/-- Two linear maps out of `InnerPiTensorProduct 𝕜 E` agree once they agree on pure tensors. -/
lemma linearMap_ext {M : Type*} [AddCommMonoid M] [Module 𝕜 M]
    {f g : InnerPiTensorProduct 𝕜 E →ₗ[𝕜] M}
    (h : ∀ m : Π i, E i, f (tprod 𝕜 m) = g (tprod 𝕜 m)) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => rw [map_smul, map_smul, map_smul, linearEquiv_tprod, h]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Splitting the index set intertwines `⨂ T` with `(⨂ T|ₚ) ⊗ (⨂ T|¬ₚ)`. -/
lemma splitLinearIsometryEquiv_mapL (p : ι → Prop) [DecidablePred p] (T : Π i, E i →L[𝕜] F i)
    (x : InnerPiTensorProduct 𝕜 E) :
    splitLinearIsometryEquiv 𝕜 F p (mapL T x) =
      TensorProduct.mapL (mapL fun i : {i // p i} => T i) (mapL fun i : {i // ¬p i} => T i)
        (splitLinearIsometryEquiv 𝕜 E p x) := by
  rw [TensorProduct.mapL_apply]
  exact splitLinearIsometryEquiv_mapₗ p _ x

/-! ### A single factor -/

section Subsingleton

variable [Subsingleton ι] (i₀ : ι)

variable (𝕜 E) in
/-- **Over a single index `i₀`, `InnerPiTensorProduct` is `E i₀`**: the identification
`⨂ m ↦ m i₀` preserves the inner product, `⟪⨂ m, ⨂ n⟫ = ⟪m i₀, n i₀⟫`. -/
noncomputable def subsingletonLinearIsometryEquiv : InnerPiTensorProduct 𝕜 E ≃ₗᵢ[𝕜] E i₀ :=
  ((linearEquiv 𝕜 E).symm.trans (PiTensorProduct.subsingletonEquiv i₀)).isometryOfInner
    fun x y => by
      obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
      obtain ⟨y, rfl⟩ := (linearEquiv 𝕜 E).surjective y
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, inner_linearEquiv]
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' n =>
          simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, inner_smul_left,
            inner_smul_right, PiTensorProduct.subsingletonEquiv_apply_tprod,
            PiTensorProduct.innerₛₗ_tprod, smul_eq_mul, Fintype.prod_subsingleton _ i₀]
        | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
      | add x x' hx hx' => simp only [map_add, inner_add_left, LinearMap.add_apply, hx, hx']

/-- `InnerPiTensorProduct.subsingletonLinearIsometryEquiv 𝕜 E i₀` sends `⨂ m` to `m i₀`. -/
@[simp] lemma subsingletonLinearIsometryEquiv_tprod (m : Π i, E i) :
    subsingletonLinearIsometryEquiv 𝕜 E i₀ (tprod 𝕜 m) = m i₀ := by
  simp only [← linearEquiv_tprod]
  simp [subsingletonLinearIsometryEquiv, -linearEquiv_tprod]

/-- Over a single index `i₀`, `⨂ T` is `T i₀`. -/
lemma subsingletonLinearIsometryEquiv_mapL (T : Π i, E i →L[𝕜] F i)
    (x : InnerPiTensorProduct 𝕜 E) :
    subsingletonLinearIsometryEquiv 𝕜 F i₀ (mapL T x) =
      T i₀ (subsingletonLinearIsometryEquiv 𝕜 E i₀ x) := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Subsingleton

section Functorial

variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]

/-- `⨂ (S i ∘ T i) = (⨂ S) ∘ (⨂ T)`. -/
lemma mapL_comp (S : Π i, F i →L[𝕜] G i) (T : Π i, E i →L[𝕜] F i) :
    mapL (fun i => S i ∘L T i) = mapL S ∘L mapL T :=
  ContinuousLinearMap.coe_injective <| linearMap_ext fun m => by simp

/-- `⨂ id = id`. -/
@[simp] lemma mapL_id : mapL (fun i => ContinuousLinearMap.id 𝕜 (E i)) = .id 𝕜 _ :=
  ContinuousLinearMap.coe_injective <| linearMap_ext fun m => by simp

/-- `⨂ (S i * T i) = (⨂ S) * (⨂ T)` for operators on the factors. -/
lemma mapL_mul (S T : Π i, E i →L[𝕜] E i) : mapL (fun i => S i * T i) = mapL S * mapL T :=
  mapL_comp S T

/-- `⨂ 1 = 1`. -/
@[simp] lemma mapL_one : mapL (fun i => (1 : E i →L[𝕜] E i)) = 1 :=
  mapL_id

end Functorial

/-- The formal adjoint of `⨂ T` is `⨂ T†`: `⟪(⨂ T†) x, y⟫ = ⟪x, (⨂ T) y⟫`. The tensor product is
not complete, so this is stated through the inner product. -/
lemma inner_mapL_adjoint [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (F i)]
    (T : Π i, E i →L[𝕜] F i) (x : InnerPiTensorProduct 𝕜 F) (y : InnerPiTensorProduct 𝕜 E) :
    ⟪mapL (fun i => ContinuousLinearMap.adjoint (T i)) x, y⟫_𝕜 = ⟪x, mapL T y⟫_𝕜 := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 F).surjective x
  obtain ⟨y, rfl⟩ := (linearEquiv 𝕜 E).surjective y
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' n =>
      simp only [map_smul, inner_smul_left, inner_smul_right, linearEquiv_tprod, mapL_tprod,
        inner_tprod, ContinuousLinearMap.adjoint_inner_left]
    | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
  | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']

omit [Fintype ι] in
private lemma toLinearMap_update [DecidableEq ι] (T : Π i, E i →L[𝕜] F i) (i : ι)
    (S : E i →L[𝕜] F i) :
    (fun j => (Function.update T i S j).toLinearMap) =
      Function.update (fun j => (T j).toLinearMap) i S.toLinearMap :=
  funext fun j => Function.apply_update (fun _ f => ContinuousLinearMap.toLinearMap f) T i S j

variable (𝕜 E F) in
/-- The tensor product of operators `T ↦ ⨂ T i`, multilinear in `T`. -/
noncomputable def mapLMultilinear :
    MultilinearMap 𝕜 (fun i => E i →L[𝕜] F i)
      (InnerPiTensorProduct 𝕜 E →L[𝕜] InnerPiTensorProduct 𝕜 F) where
  toFun := mapL
  map_update_add' T i S S' := ContinuousLinearMap.coe_injective <| by
    simp only [ContinuousLinearMap.toLinearMap_add, coe_mapL, toLinearMap_update, mapₗ,
      PiTensorProduct.map_update_add, LinearMap.add_comp, LinearMap.comp_add]
  map_update_smul' T i c S := ContinuousLinearMap.coe_injective <| by
    simp only [ContinuousLinearMap.toLinearMap_smul, coe_mapL, toLinearMap_update, mapₗ,
      PiTensorProduct.map_update_smul, LinearMap.smul_comp, LinearMap.comp_smul]

/-- `mapLMultilinear 𝕜 E F T = mapL T`. -/
@[simp] lemma mapLMultilinear_apply (T : Π i, E i →L[𝕜] F i) : mapLMultilinear 𝕜 E F T = mapL T :=
  rfl

section FinTwo

variable {E₂ F₂ : Fin 2 → Type*} [∀ i, NormedAddCommGroup (E₂ i)] [∀ i, InnerProductSpace 𝕜 (E₂ i)]
  [∀ i, NormedAddCommGroup (F₂ i)] [∀ i, InnerProductSpace 𝕜 (F₂ i)]

/-- For two factors, `⨂ T` is the binary operator tensor product `T 0 ⊗ T 1`. -/
lemma linearIsometryEquivTensorProduct_mapL (T : Π i, E₂ i →L[𝕜] F₂ i)
    (x : InnerPiTensorProduct 𝕜 E₂) :
    linearIsometryEquivTensorProduct 𝕜 F₂ (mapL T x) =
      TensorProduct.mapL (T 0) (T 1) (linearIsometryEquivTensorProduct 𝕜 E₂ x) := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E₂).surjective x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end FinTwo

/-! ### Reindexing and changing the factors -/

section Reindex

variable {κ : Type*} [Fintype κ]

variable (𝕜 E) in
/-- **Reindexing** along `e : ι ≃ κ` is a linear isometric equivalence
`InnerPiTensorProduct 𝕜 E ≃ₗᵢ InnerPiTensorProduct 𝕜 (E ∘ e.symm)`, `⨂ m ↦ ⨂ (m ∘ e.symm)`. -/
noncomputable def reindexLinearIsometryEquiv (e : ι ≃ κ) :
    InnerPiTensorProduct 𝕜 E ≃ₗᵢ[𝕜] InnerPiTensorProduct 𝕜 (fun k => E (e.symm k)) :=
  ((linearEquiv 𝕜 E).symm.trans ((PiTensorProduct.reindex 𝕜 E e).trans
    (linearEquiv 𝕜 _))).isometryOfInner fun x y => by
      obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
      obtain ⟨y, rfl⟩ := (linearEquiv 𝕜 E).surjective y
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, inner_linearEquiv]
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' n =>
          simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, PiTensorProduct.reindex_tprod,
            PiTensorProduct.innerₛₗ_tprod, Equiv.prod_comp e.symm fun i => ⟪m i, n i⟫_𝕜]
        | add y y' hy hy' => simp only [map_add, hy, hy']
      | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- `InnerPiTensorProduct.reindexLinearIsometryEquiv 𝕜 E e` sends `⨂ m` to `⨂ (m ∘ e.symm)`. -/
@[simp] lemma reindexLinearIsometryEquiv_tprod (e : ι ≃ κ) (m : Π i, E i) :
    reindexLinearIsometryEquiv 𝕜 E e (tprod 𝕜 m) =
      tprod 𝕜 fun k => m (e.symm k) :=
  PiTensorProduct.reindex_tprod e m

/-- Reindexing intertwines `⨂ T` with `⨂ (T ∘ e.symm)`. -/
lemma reindexLinearIsometryEquiv_mapL (e : ι ≃ κ) (T : Π i, E i →L[𝕜] F i)
    (x : InnerPiTensorProduct 𝕜 E) :
    reindexLinearIsometryEquiv 𝕜 F e (mapL T x) =
      mapL (fun k => T (e.symm k)) (reindexLinearIsometryEquiv 𝕜 E e x) := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Changing the factors** along linear isometric equivalences `f i : E i ≃ₗᵢ F i` is a linear
isometric equivalence, `⨂ m ↦ ⨂ (f i (m i))`. -/
noncomputable def congrLinearIsometryEquiv (f : Π i, E i ≃ₗᵢ[𝕜] F i) :
    InnerPiTensorProduct 𝕜 E ≃ₗᵢ[𝕜] InnerPiTensorProduct 𝕜 F :=
  ((linearEquiv 𝕜 E).symm.trans ((PiTensorProduct.congr fun i => (f i).toLinearEquiv).trans
    (linearEquiv 𝕜 F))).isometryOfInner fun x y => by
      obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
      obtain ⟨y, rfl⟩ := (linearEquiv 𝕜 E).surjective y
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, inner_linearEquiv]
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' n =>
          simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, PiTensorProduct.congr_tprod,
            PiTensorProduct.innerₛₗ_tprod, LinearIsometryEquiv.coe_toLinearEquiv,
            LinearIsometryEquiv.inner_map_map]
        | add y y' hy hy' => simp only [map_add, hy, hy']
      | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- `InnerPiTensorProduct.congrLinearIsometryEquiv f` sends `⨂ m` to `⨂ (f i (m i))`. -/
@[simp] lemma congrLinearIsometryEquiv_tprod (f : Π i, E i ≃ₗᵢ[𝕜] F i) (m : Π i, E i) :
    congrLinearIsometryEquiv f (tprod 𝕜 m) =
      tprod 𝕜 fun i => f i (m i) :=
  PiTensorProduct.congr_tprod _ m

/-- Changing the factors along `f` intertwines `⨂ T` with `⨂ S` when each `f i` intertwines `T i`
with `S i`. -/
lemma congrLinearIsometryEquiv_mapL (f : Π i, E i ≃ₗᵢ[𝕜] F i) {T : Π i, E i →L[𝕜] E i}
    {S : Π i, F i →L[𝕜] F i} (h : ∀ i v, f i (T i v) = S i (f i v))
    (x : InnerPiTensorProduct 𝕜 E) :
    congrLinearIsometryEquiv f (mapL T x) = mapL S (congrLinearIsometryEquiv f x) := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 E).surjective x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp [h]
  | add x y hx hy => simp only [map_add, hx, hy]

end Reindex

/-! ### Finite sets of indices -/

section Finset

variable {κ : Type*} [DecidableEq κ] {H : κ → Type*} [∀ k, NormedAddCommGroup (H k)]
  [∀ k, InnerProductSpace 𝕜 (H k)]

variable (𝕜 H) in
/-- For finite sets `s ⊆ t` of indices, the tensor product over `t` is the tensor product of those
over `s` and over the indices of `t` outside `s`: the linear isometric equivalence
`⨂ m ↦ (⨂ m|ₛ) ⊗ (⨂ m|ₜ₋ₛ)`. -/
noncomputable def finsetSplitLinearIsometryEquiv {s t : Finset κ} (hst : s ⊆ t) :
    InnerPiTensorProduct 𝕜 (fun j : t => H j) ≃ₗᵢ[𝕜]
      InnerPiTensorProduct 𝕜 (fun i : s => H i) ⊗[𝕜]
        InnerPiTensorProduct 𝕜 (fun j : {j : t // (j : κ) ∉ s} => H j) :=
  (splitLinearIsometryEquiv 𝕜 (fun j : t => H j) fun j => (j : κ) ∈ s).trans <|
    LinearIsometryEquiv.rTensor _ <|
      (reindexLinearIsometryEquiv 𝕜 (fun j : {j : t // (j : κ) ∈ s} => H j)
        (Equiv.subtypeSubtypeEquivSubtype fun h => hst h)).trans <|
        congrLinearIsometryEquiv fun i => LinearIsometryEquiv.refl 𝕜 (H i)

/-- `InnerPiTensorProduct.finsetSplitLinearIsometryEquiv 𝕜 H hst` sends `⨂ m` to
`(⨂ m|ₛ) ⊗ (⨂ m|ₜ₋ₛ)`. -/
@[simp] lemma finsetSplitLinearIsometryEquiv_tprod {s t : Finset κ} (hst : s ⊆ t)
    (m : Π j : t, H j) :
    finsetSplitLinearIsometryEquiv 𝕜 H hst (tprod 𝕜 m) =
      tprod 𝕜 (fun i : s => m ⟨i, hst i.2⟩) ⊗ₜ
        tprod 𝕜 (fun j : {j : t // (j : κ) ∉ s} => m j) := by
  simp only [finsetSplitLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
    splitLinearIsometryEquiv_tprod, LinearIsometryEquiv.rTensor_apply]
  rw [LinearEquiv.rTensor_tmul, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.trans_apply, reindexLinearIsometryEquiv_tprod]
  exact congrArg (· ⊗ₜ _) (congrLinearIsometryEquiv_tprod _ _)

/-- The splitting of `InnerPiTensorProduct.finsetSplitLinearIsometryEquiv` intertwines `⨂ T` with
`(⨂ T|ₛ) ⊗ (⨂ T|ₜ₋ₛ)`. -/
lemma finsetSplitLinearIsometryEquiv_mapL {s t : Finset κ} (hst : s ⊆ t)
    (T : Π j : t, H j →L[𝕜] H j) (x : InnerPiTensorProduct 𝕜 fun j : t => H j) :
    finsetSplitLinearIsometryEquiv 𝕜 H hst (mapL T x) =
      TensorProduct.mapL (mapL fun i : s => T ⟨i, hst i.2⟩)
        (mapL fun j : {j : t // (j : κ) ∉ s} => T j) (finsetSplitLinearIsometryEquiv 𝕜 H hst x) := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 _).surjective x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Finset

end InnerPiTensorProduct
