/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# ⋆-representations of full matrix algebras

Let `π : M_m(𝕜) → B(K)` be a ⋆-representation, not necessarily unital, of the full matrix algebra
over `𝕜 = ℝ` or `ℂ` on a Hilbert space `K`, and fix an index `i₀ : m`. With the matrix units
`E_{ij} = Matrix.single i j 1`, the operator `π(E_{i₀i₀})` is an orthogonal projection
(`Matrix.isStarProjection_map_single`); its range is the **multiplicity space**
`E = multiplicitySpace π i₀`. The partial isometries `π(E_{i i₀})`, with initial projection
`π(E_{i₀i₀})` (`Matrix.adjoint_map_single_mul_map_single`), restrict to isometries
`Vᵢ : E → K` (`multiplicityIsometry π i₀ i`) with mutually orthogonal ranges, on which the
representation acts as `π(B) (Vᵢ ξ) = Σⱼ Bⱼᵢ Vⱼ ξ`. Together the ranges span the range of the
projection `π(1)` (`Matrix.iSup_range_multiplicityIsometry`).

For a unital representation `π(1) = 1`, so `(K, V)` is the Hilbert sum of `m` copies of `E`:

`K = ⊕ᵢ Vᵢ(E)`, and `π(B) (Vᵢ ξ) = Σⱼ Bⱼᵢ Vⱼ ξ`.

Read through `K ≅ 𝕜ᵐ ⊗ E`, `δᵢ ⊗ ξ ↦ Vᵢ ξ` for the standard basis `δᵢ` of `𝕜ᵐ`, this says
`π(B) = B ⊗ 1_E`: every unital ⋆-representation of `M_m(𝕜)` is a multiple of the identity
representation on `𝕜ᵐ`, with multiplicity `dim E`. The identification is stated here as the
Hilbert sum `Matrix.isHilbertSum_multiplicityIsometry`, which carries the metric structure,
together with the intertwining relation `Matrix.map_apply_multiplicityIsometry`, and as the
unitary equivalence `Matrix.multiplicityLinearIsometryEquiv π i₀ : K ≃ ℓ²(m, E)`
intertwining `π(B)` with `B ⊗ 1_E` (`Matrix.multiplicityLinearIsometryEquiv_map_apply`); its linear
part is the linear equivalence `Matrix.multiplicityEquiv π i₀ : K ≃ E^m`, whence
`rank K = m · rank E` in any dimension. No structure theory of type I von Neumann algebras is used:
the decomposition comes from the matrix units alone.

When `K` is finite-dimensional and `π` is unital, an orthonormal basis `e` of `E` gives the
orthonormal basis `b (i, k) = Vᵢ (e k)` of `K` (`multiplicityBasis π e`), adapted to
`K ≅ 𝕜ᵐ ⊗ E`, in which `π(B)` has the matrix `B ⊗ 1`.

## Main definitions

* `Matrix.multiplicitySpace π i₀` — the range `E` of `π(E_{i₀i₀})`.
* `Matrix.multiplicityIsometry π i₀ i` — the isometry `Vᵢ = π(E_{i i₀})|_E : E → K`.
* `Matrix.multiplicityEquiv π i₀` — the linear equivalence `K ≃ E^m` for unital `π`.
* `Matrix.multiplicityLinearIsometryEquiv π i₀` — the unitary equivalence `K ≃ ℓ²(m, E)` for
  unital `π`.
* `Matrix.multiplicityBasis π e` — the orthonormal basis `Vᵢ (e k)` of a
  finite-dimensional `K`, for unital `π`.

## Main statements

* `Matrix.map_apply_multiplicityIsometry` — `π(B) (Vᵢ ξ) = Σⱼ Bⱼᵢ Vⱼ ξ`.
* `Matrix.iSup_range_multiplicityIsometry` — the ranges of the `Vᵢ` span `π(1) K`.
* `Matrix.isHilbertSum_multiplicityIsometry` — for unital `π`, `K` is the Hilbert sum
  of the `Vᵢ(E)`.
* `Matrix.multiplicityLinearIsometryEquiv_map_apply` — for unital `π`, the unitary equivalence
  `K ≃ ℓ²(m, E)` intertwines `π(B)` with `B ⊗ 1_E`: `π` is unitarily equivalent to a multiple of
  the identity representation.
* `Matrix.toMatrix_multiplicityBasis` — the matrix of `π(B)` is `B ⊗ 1`.
* `Matrix.rank_eq_card_mul_rank_multiplicitySpace`,
  `Matrix.finrank_eq_card_mul_finrank_multiplicitySpace` — for unital `π`, `rank K = m · rank E`
  and `dim K = m · dim E`, with no finite-dimensionality assumption.

## Implementation notes

The representation is any `π : F` in a class with `NonUnitalAlgHomClass` and `StarHomClass`, which
covers both `→⋆ₙₐ[𝕜]` and `→⋆ₐ[𝕜]`. The statements about `K` as a whole assume in addition
`OneHomClass`, that is `π(1) = 1`.

For unital `π`, the multiplicity space is the `E_{i₀i₀}`-corner of the Morita equivalence between
`M_m(𝕜)`-modules and `𝕜`-modules, `MatrixModCat.toModuleCatObj` in
`Mathlib/RingTheory/Morita/Matrix.lean`, applied to `K` made an `M_m(𝕜)`-module through `π`
(`Module.compHom`); both are the same subspace of `K`. That construction is not used here, for two
reasons. It needs a unital module structure `Module (Matrix m m 𝕜) K`, which a non-unital `π`, with
`π(1) ≠ 1`, does not provide on `K` itself. And even for unital `π` it would require registering
the non-canonical instance `Module.compHom K π` on the Hilbert space `K`. The multiplicity space is
therefore defined directly as the range of `π(E_{i₀i₀})`.
-/

@[expose] public section

open scoped InnerProductSpace Kronecker
open Matrix

namespace Matrix

variable {𝕜 m K : Type*} [RCLike 𝕜] [Fintype m] [DecidableEq m]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
variable {F : Type*} [FunLike F (Matrix m m 𝕜) (K →L[𝕜] K)]
  [NonUnitalAlgHomClass F 𝕜 (Matrix m m 𝕜) (K →L[𝕜] K)] (π : F)
variable {ι : Type*} [Fintype ι]

/-- The matrix units multiply as `π(E_{ij}) π(E_{kl}) = δ_{jk} π(E_{il})`. -/
lemma map_single_mul_map_single (i j k l : m) :
    π (single i j 1) * π (single k l 1) = if j = k then π (single i l 1) else 0 := by
  rw [← map_mul]
  split_ifs with h
  · rw [h, single_mul_single_same, one_mul]
  · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]

/-- `π(E_{ij}) π(E_{kl}) x = δ_{jk} π(E_{il}) x`, applied to a vector. -/
lemma map_single_apply_map_single_apply (i j k l : m) (x : K) :
    π (single i j 1) (π (single k l 1) x) = if j = k then π (single i l 1) x else 0 := by
  rw [← mul_apply_eq_comp, map_single_mul_map_single]
  split_ifs <;> rfl

/-- The multiplicity space of `π` at `i₀`: the range of the projection `π(E_{i₀i₀})`. -/
def multiplicitySpace (i₀ : m) : Submodule 𝕜 K :=
  LinearMap.range (π (single i₀ i₀ 1) : K →ₗ[𝕜] K)

variable {π} in
/-- `x` lies in the multiplicity space iff it is fixed by `π(E_{i₀i₀})`. -/
lemma mem_multiplicitySpace_iff {i₀ : m} {x : K} :
    x ∈ multiplicitySpace π i₀ ↔ π (single i₀ i₀ 1) x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    simp [map_single_apply_map_single_apply]
  · exact fun h => ⟨x, h⟩

/-- `π(E_{i₀ i}) x` lies in the multiplicity space at `i₀`. -/
lemma map_single_apply_mem_multiplicitySpace (i₀ i : m) (x : K) :
    π (single i₀ i 1) x ∈ multiplicitySpace π i₀ := by
  simp [mem_multiplicitySpace_iff, map_single_apply_map_single_apply]

/-- The multiplicity space is closed. -/
lemma isClosed_multiplicitySpace (i₀ : m) : IsClosed (multiplicitySpace π i₀ : Set K) := by
  have : (multiplicitySpace π i₀ : Set K) = {x | π (single i₀ i₀ 1) x = x} :=
    Set.ext fun _ => mem_multiplicitySpace_iff
  rw [this]
  exact isClosed_eq (map_continuous _) continuous_id

variable [CompleteSpace K]

/-- The multiplicity space is a Hilbert space, being a closed subspace of `K`. -/
instance (i₀ : m) : CompleteSpace (multiplicitySpace π i₀) :=
  (isClosed_multiplicitySpace π i₀).completeSpace_coe

variable [StarHomClass F (Matrix m m 𝕜) (K →L[𝕜] K)]

omit [Fintype m] [NonUnitalAlgHomClass F 𝕜 (Matrix m m 𝕜) (K →L[𝕜] K)] in
/-- `π(E_{ij})† = π(E_{ji})`. -/
lemma adjoint_map_single (i j : m) : ContinuousLinearMap.adjoint (π (single i j 1)) = π (single j i 1) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_eq_conjTranspose, conjTranspose_single, star_one]

/-- `π(E_{ii})` is an orthogonal projection; for `i = i₀` its range is the multiplicity space. -/
lemma isStarProjection_map_single (i : m) : IsStarProjection (π (single i i 1)) where
  isIdempotentElem := by simp [IsIdempotentElem, map_single_mul_map_single]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_map_single]

/-- `π(E_{ij})` is a partial isometry with initial projection `π(E_{jj})`:
`π(E_{ij})† π(E_{ij}) = π(E_{jj})`. -/
lemma adjoint_map_single_mul_map_single (i j : m) :
    ContinuousLinearMap.adjoint (π (single i j 1)) * π (single i j 1) = π (single j j 1) := by
  simp [adjoint_map_single, map_single_mul_map_single]

/-- `⟪π(E_{i i₀}) x, π(E_{j i₀}) y⟫ = δ_{ij} ⟪x, y⟫` on the multiplicity space. -/
lemma inner_map_single_apply_map_single_apply {i₀ : m} (i j : m) {x y : K}
    (hy : y ∈ multiplicitySpace π i₀) :
    ⟪π (single i i₀ 1) x, π (single j i₀ 1) y⟫_𝕜 = if i = j then ⟪x, y⟫_𝕜 else 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_map_single, map_single_apply_map_single_apply]
  split_ifs
  · rw [mem_multiplicitySpace_iff.mp hy]
  · rw [inner_zero_right]

/-- The isometry `Vᵢ : E → K`, the restriction of the partial isometry `π(E_{i i₀})` to the
multiplicity space `E` at `i₀`. -/
noncomputable def multiplicityIsometry (i₀ i : m) : multiplicitySpace π i₀ →ₗᵢ[𝕜] K :=
  LinearMap.isometryOfInner
    ((π (single i i₀ 1) : K →ₗ[𝕜] K) ∘ₗ (multiplicitySpace π i₀).subtype) fun x y => by
      simpa using inner_map_single_apply_map_single_apply π (x := (x : K)) i i y.2

/-- `Vᵢ ξ = π(E_{i i₀}) ξ`. -/
@[simp] lemma multiplicityIsometry_apply {i₀ : m} (i : m) (ξ : multiplicitySpace π i₀) :
    multiplicityIsometry π i₀ i ξ = π (single i i₀ 1) ξ :=
  rfl

/-- `⟪Vᵢ ξ, Vⱼ η⟫ = δ_{ij} ⟪ξ, η⟫`. -/
lemma inner_multiplicityIsometry {i₀ : m} (i j : m) (ξ η : multiplicitySpace π i₀) :
    ⟪multiplicityIsometry π i₀ i ξ, multiplicityIsometry π i₀ j η⟫_𝕜 =
      if i = j then ⟪ξ, η⟫_𝕜 else 0 := by
  simpa using inner_map_single_apply_map_single_apply π (x := (ξ : K)) i j η.2

/-- The ranges of the isometries `Vᵢ` are mutually orthogonal. -/
theorem orthogonalFamily_multiplicityIsometry (i₀ : m) :
    OrthogonalFamily 𝕜 (fun _ : m => multiplicitySpace π i₀) (multiplicityIsometry π i₀) :=
  fun i j hij ξ η => by simp only [inner_multiplicityIsometry, hij, ↓reduceIte]

/-- The representation acts on the copies of `E` as `B` acts on `𝕜ᵐ`:
`π(B) (Vᵢ ξ) = Σⱼ Bⱼᵢ Vⱼ ξ`, that is, `π(B) = B ⊗ 1_E` on `K ≅ 𝕜ᵐ ⊗ E`. -/
theorem map_apply_multiplicityIsometry {i₀ : m} (B : Matrix m m 𝕜) (i : m)
    (ξ : multiplicitySpace π i₀) :
    π B (multiplicityIsometry π i₀ i ξ) = ∑ j, B j i • multiplicityIsometry π i₀ j ξ := by
  have hB : B * single i i₀ 1 = ∑ j, B j i • single j i₀ 1 := by
    ext a b
    by_cases h : i₀ = b <;> simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, h]
  simp only [multiplicityIsometry_apply]
  rw [← mul_apply_eq_comp, ← map_mul, hB, map_sum, _root_.sum_apply]
  simp only [map_smul, _root_.smul_apply]

/-- Every vector decomposes along the `Vᵢ` up to the projection `π(1)`:
`π(1) x = Σᵢ Vᵢ (π(E_{i₀ i}) x)`, since `Σᵢ E_{i i₀} E_{i₀ i} = Σᵢ E_{ii} = 1`. -/
lemma sum_multiplicityIsometry_map_single_apply (i₀ : m) (x : K) :
    ∑ i, multiplicityIsometry π i₀ i
      ⟨π (single i₀ i 1) x, map_single_apply_mem_multiplicitySpace π i₀ i x⟩ = π 1 x := by
  simp only [multiplicityIsometry_apply, map_single_apply_map_single_apply, ite_true]
  rw [← _root_.sum_apply, ← map_sum, sum_single_one]

/-- The ranges of the isometries `Vᵢ` span the range of the projection `π(1)`. -/
theorem iSup_range_multiplicityIsometry (i₀ : m) :
    ⨆ i, LinearMap.range (multiplicityIsometry π i₀ i).toLinearMap =
      LinearMap.range (π 1 : K →ₗ[𝕜] K) := by
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · rintro _ ⟨ξ, rfl⟩
    refine ⟨multiplicityIsometry π i₀ i ξ, ?_⟩
    change π 1 (π (single i i₀ 1) ξ) = π (single i i₀ 1) ξ
    rw [← mul_apply_eq_comp, ← map_mul, Matrix.one_mul]
  · rintro _ ⟨x, rfl⟩
    change π 1 x ∈ _
    rw [← sum_multiplicityIsometry_map_single_apply π i₀ x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ _)

/-- The vectors `Vᵢ (e k)` are orthonormal. -/
lemma orthonormal_multiplicityIsometry {i₀ : m}
    (e : OrthonormalBasis ι 𝕜 (multiplicitySpace π i₀)) :
    Orthonormal 𝕜 fun p : m × ι => multiplicityIsometry π i₀ p.1 (e p.2) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, k⟩ ⟨j, l⟩
  rw [inner_multiplicityIsometry, orthonormal_iff_ite.mp e.orthonormal]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl]

/-! ### Unital representations -/

section Unital

variable [OneHomClass F (Matrix m m 𝕜) (K →L[𝕜] K)]

/-- For unital `π`, every vector decomposes along the `Vᵢ`: `x = Σᵢ Vᵢ (π(E_{i₀ i}) x)`. -/
lemma sum_multiplicityIsometry_map_single_apply_eq_self (i₀ : m) (x : K) :
    ∑ i, multiplicityIsometry π i₀ i
      ⟨π (single i₀ i 1) x, map_single_apply_mem_multiplicitySpace π i₀ i x⟩ = x := by
  rw [sum_multiplicityIsometry_map_single_apply, map_one, one_apply_eq_self]

/-- For unital `π`, `K` is the Hilbert sum of `m` copies of the multiplicity space `E`, embedded
by the isometries `Vᵢ`. -/
theorem isHilbertSum_multiplicityIsometry (i₀ : m) :
    IsHilbertSum 𝕜 (fun _ : m => multiplicitySpace π i₀) (multiplicityIsometry π i₀) := by
  refine .mk (orthogonalFamily_multiplicityIsometry π i₀) fun x _ => ?_
  refine Submodule.le_topologicalClosure _ ?_
  rw [← sum_multiplicityIsometry_map_single_apply_eq_self π i₀ x]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ _)

/-- For unital `π`, the linear equivalence `K ≃ E^m`, `x ↦ (π(E_{i₀ i}) x)ᵢ`, with inverse
`f ↦ Σᵢ Vᵢ (f i)`. It is isometric for the `ℓ²` norm on `E^m` by
`Matrix.isHilbertSum_multiplicityIsometry`; only the linear structure is recorded here. -/
noncomputable def multiplicityEquiv (i₀ : m) : K ≃ₗ[𝕜] (m → multiplicitySpace π i₀) where
  toFun x i := ⟨π (single i₀ i 1) x, map_single_apply_mem_multiplicitySpace π i₀ i x⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  invFun f := ∑ i, multiplicityIsometry π i₀ i (f i)
  left_inv x := sum_multiplicityIsometry_map_single_apply_eq_self π i₀ x
  right_inv f := by
    ext j
    simp only [multiplicityIsometry_apply, map_sum, map_single_apply_map_single_apply,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact mem_multiplicitySpace_iff.mp (f j).2

/-- The components of `x` are `π(E_{i₀ i}) x`. -/
@[simp] lemma multiplicityEquiv_apply (i₀ : m) (x : K) (i : m) :
    (multiplicityEquiv π i₀ x i : K) = π (single i₀ i 1) x :=
  rfl

/-- The vector with components `f i` is `Σᵢ Vᵢ (f i)`. -/
@[simp] lemma multiplicityEquiv_symm_apply (i₀ : m) (f : m → multiplicitySpace π i₀) :
    (multiplicityEquiv π i₀).symm f = ∑ i, multiplicityIsometry π i₀ i (f i) :=
  rfl

/-- The components intertwine `π(B)` with `B`: `(π(B) x)ᵢ = Σⱼ Bᵢⱼ xⱼ`, that is, `π(B) = B ⊗ 1_E`
in the coordinates `x ↦ (π(E_{i₀ i}) x)ᵢ`. -/
lemma multiplicityEquiv_map_apply (i₀ : m) (B : Matrix m m 𝕜) (x : K) (i : m) :
    multiplicityEquiv π i₀ (π B x) i = ∑ j, B i j • multiplicityEquiv π i₀ x j := by
  ext
  have hB : single i₀ i 1 * B = ∑ j, B i j • single i₀ j (1 : 𝕜) := by
    ext a b
    by_cases h : i₀ = a <;> simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, h]
  simp only [multiplicityEquiv_apply, Submodule.coe_sum, Submodule.coe_smul]
  rw [← mul_apply_eq_comp, ← map_mul, hB, map_sum, _root_.sum_apply]
  simp only [map_smul, _root_.smul_apply]

/-- For unital `π`, the inner product is the sum of the inner products of the components:
`⟪x, y⟫ = Σᵢ ⟪π(E_{i₀ i}) x, π(E_{i₀ i}) y⟫`. -/
lemma inner_eq_sum_inner_multiplicityEquiv (i₀ : m) (x y : K) :
    ⟪x, y⟫_𝕜 = ∑ i, ⟪multiplicityEquiv π i₀ x i, multiplicityEquiv π i₀ y i⟫_𝕜 := by
  conv_lhs => rw [← sum_multiplicityIsometry_map_single_apply_eq_self π i₀ x,
    ← sum_multiplicityIsometry_map_single_apply_eq_self π i₀ y]
  simp only [sum_inner, inner_sum, inner_multiplicityIsometry, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rfl

/-- For unital `π`, the **unitary equivalence** `K ≃ E^m` of `K` with the Hilbert sum `ℓ²(m, E)`
of `m` copies of the multiplicity space, `x ↦ (π(E_{i₀ i}) x)ᵢ`: the linear equivalence
`Matrix.multiplicityEquiv` is isometric (`Matrix.inner_eq_sum_inner_multiplicityEquiv`). It
intertwines `π(B)` with `B ⊗ 1_E` on `ℓ²(m, E) = 𝕜ᵐ ⊗ E`, `(π(B) x)ᵢ = Σⱼ Bᵢⱼ xⱼ`
(`Matrix.multiplicityLinearIsometryEquiv_map_apply`), so `π` is
unitarily equivalent to the `dim E`-fold multiple of the identity representation. -/
noncomputable def multiplicityLinearIsometryEquiv (i₀ : m) :
    K ≃ₗᵢ[𝕜] PiLp 2 (fun _ : m => multiplicitySpace π i₀) :=
  ((multiplicityEquiv π i₀).trans
    (WithLp.linearEquiv 2 𝕜 (m → multiplicitySpace π i₀)).symm).isometryOfInner fun x y => by
    rw [PiLp.inner_apply, inner_eq_sum_inner_multiplicityEquiv π i₀ x y]
    rfl

/-- The components of the unitary equivalence are `π(E_{i₀ i}) x`. -/
@[simp] lemma multiplicityLinearIsometryEquiv_apply (i₀ : m) (x : K) (i : m) :
    multiplicityLinearIsometryEquiv π i₀ x i = multiplicityEquiv π i₀ x i :=
  rfl

/-- The unitary equivalence intertwines `π(B)` with `B ⊗ 1_E`. -/
lemma multiplicityLinearIsometryEquiv_map_apply (i₀ : m) (B : Matrix m m 𝕜) (x : K) (i : m) :
    multiplicityLinearIsometryEquiv π i₀ (π B x) i =
      ∑ j, B i j • multiplicityLinearIsometryEquiv π i₀ x j :=
  multiplicityEquiv_map_apply π i₀ B x i

/-- For unital `π`, `rank K = m · rank E`, in any dimension. -/
theorem rank_eq_card_mul_rank_multiplicitySpace (i₀ : m) :
    Module.rank 𝕜 K = Fintype.card m * Module.rank 𝕜 (multiplicitySpace π i₀) := by
  have h := (multiplicityEquiv π i₀).lift_rank_eq
  rw [rank_pi, Cardinal.sum_const, Cardinal.mk_fintype] at h
  simp only [Cardinal.lift_mul, Cardinal.lift_natCast, Cardinal.lift_lift] at h
  exact Cardinal.lift_injective (h.trans (by simp))

/-- For unital `π`, `dim K = m · dim E`. Both sides are `0` when `K` is infinite-dimensional. -/
theorem finrank_eq_card_mul_finrank_multiplicitySpace (i₀ : m) :
    Module.finrank 𝕜 K = Fintype.card m * Module.finrank 𝕜 (multiplicitySpace π i₀) := by
  rw [Module.finrank, Module.finrank, rank_eq_card_mul_rank_multiplicitySpace π i₀,
    Cardinal.toNat_mul, Cardinal.toNat_natCast]

/-! ### Finite-dimensional representations -/

section FiniteDimensional

/-- For unital `π`, the vectors `Vᵢ (e k)` span `K`. -/
lemma span_multiplicityIsometry {i₀ : m} (e : OrthonormalBasis ι 𝕜 (multiplicitySpace π i₀)) :
    ⊤ ≤ Submodule.span 𝕜 (Set.range fun p : m × ι => multiplicityIsometry π i₀ p.1 (e p.2)) := by
  intro x _
  rw [← sum_multiplicityIsometry_map_single_apply_eq_self π i₀ x]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← e.sum_repr (⟨_, map_single_apply_mem_multiplicitySpace π i₀ i x⟩), map_sum]
  exact Submodule.sum_mem _ fun k _ => by
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), rfl⟩)

/-- The orthonormal basis `b (i, k) = Vᵢ (e k)` of a finite-dimensional `K` built from an
orthonormal basis `e` of the multiplicity space of a unital `π`, adapted to `K ≅ 𝕜ᵐ ⊗ E`. -/
noncomputable def multiplicityBasis {i₀ : m}
    (e : OrthonormalBasis ι 𝕜 (multiplicitySpace π i₀)) : OrthonormalBasis (m × ι) 𝕜 K :=
  .mk (orthonormal_multiplicityIsometry π e) (span_multiplicityIsometry π e)

/-- `b (i, k) = Vᵢ (e k)`. -/
@[simp] lemma multiplicityBasis_apply {i₀ : m}
    (e : OrthonormalBasis ι 𝕜 (multiplicitySpace π i₀)) (p : m × ι) :
    multiplicityBasis π e p = multiplicityIsometry π i₀ p.1 (e p.2) := by
  simp [multiplicityBasis]

/-- In the basis `b (i, k) = Vᵢ (e k)` the operator `π(B)` has the matrix `B ⊗ 1`. -/
theorem toMatrix_multiplicityBasis [DecidableEq ι] {i₀ : m}
    (e : OrthonormalBasis ι 𝕜 (multiplicitySpace π i₀)) (B : Matrix m m 𝕜) :
    LinearMap.toMatrix (multiplicityBasis π e).toBasis (multiplicityBasis π e).toBasis
      (π B : K →ₗ[𝕜] K) = B ⊗ₖ (1 : Matrix ι ι 𝕜) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, kroneckerMap_apply]
  simp only [multiplicityBasis_apply, ContinuousLinearMap.coe_coe, map_apply_multiplicityIsometry,
    inner_sum, inner_smul_right, inner_multiplicityIsometry, orthonormal_iff_ite.mp e.orthonormal]
  by_cases hkl : k = l <;> simp [hkl, Matrix.one_apply]

end FiniteDimensional

end Unital

end Matrix
