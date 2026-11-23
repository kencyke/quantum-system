/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Nuclear.InductiveLimit
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Nuclear.TensorProduct
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.PiMinimal
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Completion
public import QuantumSystem.ForMathlib.Analysis.Normed.Group.DirectLimit
public import QuantumSystem.ForMathlib.LinearAlgebra.PiTensorProduct.Extend

/-!
# The infinite minimal tensor product of unital C⋆-algebras

For a family `A i` of nontrivial unital C⋆-algebras indexed by an arbitrary type, the minimal tensor
products `⨂ₘᵢₙ i : s, A i` over the finite sets `s` of indices form a directed system
along the `⋆`-homomorphisms `x ↦ x ⊗ 1`, which are isometric. The infinite minimal tensor product
`InfiniteMinTensorProduct A` is the completion of its normed direct limit, a unital C⋆-algebra in
which every finite minimal tensor product embeds isometrically, the union of their images being
dense.

## Main definitions

* `PiTensorProduct.extendStarAlgHom R h` — for `s ⊆ t`, the `⋆`-homomorphism `x ↦ x ⊗ 1` of the
  algebraic tensor products of a family of `⋆`-algebras.
* `PiMinTensorProduct.extend h` — its extension `x ↦ x ⊗ 1` to the minimal tensor products.
* `InfiniteMinTensorProduct A` — the infinite minimal tensor product.
* `InfiniteMinTensorProduct.of A s` — the embedding of the minimal tensor product over the finite
  set `s`.

## Main results

* `PiMinTensorProduct.norm_extend` — `x ↦ x ⊗ 1` is isometric on the minimal tensor products.
* `PiMinTensorProduct.commute_extend_of_disjoint` — elements over disjoint sets of indices commute
  once extended to a common one.
* `PiMinTensorProduct.extend_map` — `x ↦ x ⊗ 1` commutes with the tensor product of unital
  `⋆`-homomorphisms.
* `InfiniteMinTensorProduct.norm_of` — the embeddings of the finite minimal tensor products are
  isometric.
* `InfiniteMinTensorProduct.dense_iUnion_range_of` — the union of their images is dense.
* `InfiniteMinTensorProduct.of_univ_surjective` — for finitely many indices, the minimal tensor
  product over all of them is the whole infinite minimal tensor product.
* `InfiniteMinTensorProduct.instNontrivial` — it is nontrivial, so its unit has norm one.
* `InfiniteMinTensorProduct.isNuclear` — it is nuclear when every factor is;
  `InfiniteMinTensorProduct.isNuclear_of_stages` — when its finite stages are;
  `InfiniteMinTensorProduct.isNuclear_of_finiteDimensional` — when every factor is
  finite-dimensional, in every pair of universes.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace PiMinTensorProduct

open UniformSpace

universe u v w w' uι

/-! ### The extension by `1` as a `⋆`-homomorphism -/

namespace PiTensorProduct

variable {ι R : Type*} [CommSemiring R] [StarRing R] [DecidableEq ι] {A : ι → Type*}
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)]

/-- The extension by `1` commutes with the involutions: `(star x) ⊗ 1 = star (x ⊗ 1)`. -/
lemma extendAlgHom_star {s t : Finset ι} (hst : s ⊆ t) (x : ⨂[R] i : s, A i) :
    extendAlgHom R hst (star x) = star (extendAlgHom R hst x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [star_smul, star_tprod, map_smul, map_smul, star_smul, extendAlgHom_tprod,
      extendAlgHom_tprod, star_tprod]
    congr 2
    funext j
    by_cases hj : (j : ι) ∈ s <;> simp [extendFun, hj]
  | add x y hx hy => rw [star_add, map_add, hx, hy, map_add, star_add]

variable (R) in
/-- For `⋆`-algebras, the extension by `1`, `x ↦ x ⊗ 1`, as a `⋆`-algebra homomorphism. -/
noncomputable def extendStarAlgHom {s t : Finset ι} (hst : s ⊆ t) :
    (⨂[R] i : s, A i) →⋆ₐ[R] ⨂[R] i : t, A i :=
  { extendAlgHom R hst with map_star' := extendAlgHom_star hst }

/-- `PiTensorProduct.extendStarAlgHom R h` is `PiTensorProduct.extendAlgHom R h`. -/
@[simp] lemma extendStarAlgHom_apply {s t : Finset ι} (hst : s ⊆ t) (x : ⨂[R] i : s, A i) :
    extendStarAlgHom R hst x = extendAlgHom R hst x :=
  rfl

omit [StarRing R] [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)] in
/-- **Elements extended from disjoint sets of indices commute**: `x ⊗ 1` and `1 ⊗ y` commute, the
factors of the two elementary tensors being `1` wherever the other is not. -/
lemma commute_extendAlgHom_of_disjoint {s₁ s₂ t : Finset ι} (h₁ : s₁ ⊆ t) (h₂ : s₂ ⊆ t)
    (hd : Disjoint s₁ s₂) (x : ⨂[R] i : s₁, A i) (y : ⨂[R] i : s₂, A i) :
    Commute (extendAlgHom R h₁ x) (extendAlgHom R h₂ y) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' n =>
      rw [map_smul, map_smul, extendAlgHom_tprod, extendAlgHom_tprod]
      refine Commute.smul_left (Commute.smul_right ?_ _) _
      rw [Commute, SemiconjBy, tprod_mul_tprod, tprod_mul_tprod]
      congr 1
      funext j
      by_cases hj₁ : (j : ι) ∈ s₁
      · have hj₂ : (j : ι) ∉ s₂ := Finset.disjoint_left.mp hd hj₁
        simp [extendFun, hj₁, hj₂]
      · simp [extendFun, hj₁]
    | add y y' hy hy' =>
      rw [map_add]
      exact hy.add_right hy'
  | add x x' hx hx' =>
    rw [map_add]
    exact hx.add_left hx'

variable {B : ι → Type*} [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)] [∀ i, StarRing (B i)]
  [∀ i, StarModule R (B i)]

/-- The extension by `1` commutes with the tensor product of unital `⋆`-homomorphisms:
`(⨂ eᵢ)(x) ⊗ 1 = (⨂ eᵢ)(x ⊗ 1)`. -/
lemma extendAlgHom_mapStarAlgHom {s t : Finset ι} (hst : s ⊆ t) (e : Π i, A i →⋆ₐ[R] B i)
    (x : ⨂[R] i : s, A i) :
    extendAlgHom R hst (mapStarAlgHom (fun i : s => e i) x) =
      mapStarAlgHom (fun i : t => e i) (extendAlgHom R hst x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, map_smul, mapStarAlgHom_tprod, extendAlgHom_tprod,
      extendAlgHom_tprod, mapStarAlgHom_tprod]
    congr 2
    funext j
    by_cases hj : (j : ι) ∈ s <;> simp [extendFun, hj]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end PiTensorProduct

/-! ### Faithful representations on nonzero spaces -/

namespace CStarRep

/-- A faithful representation of a nontrivial C⋆-algebra acts on a nontrivial Hilbert space. -/
lemma nontrivial_H_of_injective {A : Type*} [NonUnitalCStarAlgebra A] [Nontrivial A]
    {R : CStarRep A} (hR : Function.Injective R.π) : Nontrivial R.H := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact ha (hR (by ext v; exact Subsingleton.elim _ _))

end CStarRep

/-! ### The extension by `1` on the minimal tensor products -/

namespace PiMinTensorProduct

variable {ι : Type*} [DecidableEq ι] {A : ι → Type u} [∀ i, CStarAlgebra (A i)]

/-- For `s ⊆ t`, the splitting of the Hilbert space over `t` into those over `s` and over `t \ s`
intertwines `π_t(x ⊗ 1)` with `π_s(x) ⊗ 1`, where `π` is the tensor product of the representations
`CStarRep.gelfandNaimark (A i)` on the algebraic tensor product of the operators. -/
lemma finsetSplitLinearIsometryEquiv_piMapL_extendAlgHom {s t : Finset ι} (hst : s ⊆ t)
    (x : ⨂[ℂ] i : s, A i)
    (v : InnerPiTensorProduct ℂ fun j : t => (CStarRep.gelfandNaimark (A j)).H) :
    InnerPiTensorProduct.finsetSplitLinearIsometryEquiv ℂ
        (fun i => (CStarRep.gelfandNaimark (A i)).H) hst
        (NonUnitalStarAlgHom.piMapL (fun j : t => (CStarRep.gelfandNaimark (A j)).π)
          (PiTensorProduct.extendAlgHom ℂ hst x) v) =
      TensorProduct.mapL
        (NonUnitalStarAlgHom.piMapL (fun i : s => (CStarRep.gelfandNaimark (A i)).π) x)
        (ContinuousLinearMap.id ℂ _)
        (InnerPiTensorProduct.finsetSplitLinearIsometryEquiv ℂ
          (fun i => (CStarRep.gelfandNaimark (A i)).H) hst v) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, smul_apply, LinearIsometryEquiv.map_smul,
      TensorProduct.mapL_smul_left, smul_apply, PiTensorProduct.extendAlgHom_tprod,
      NonUnitalStarAlgHom.piMapL_tprod, NonUnitalStarAlgHom.piMapL_tprod,
      InnerPiTensorProduct.finsetSplitLinearIsometryEquiv_mapL]
    congr 3
    · congr 1
      funext i
      rw [PiTensorProduct.extendFun_apply_of_mem 1 m ⟨i, hst i.2⟩ i.2]
    · rw [← InnerPiTensorProduct.mapL_id]
      congr 1
      funext j
      rw [PiTensorProduct.extendFun_apply_of_notMem _ _ _ j.2, Pi.one_apply,
        CStarRep.gelfandNaimark_π_one]
      rfl
  | add x y hx hy =>
    simp only [map_add, add_apply, hx, hy, TensorProduct.mapL_add_left]

/-- `x ↦ x ⊗ 1` does not increase the norm of the tensor product of the representations
`CStarRep.gelfandNaimark (A i)`: `‖π_t(x ⊗ 1)‖ = ‖π_s(x)‖ ‖1‖ ≤ ‖π_s(x)‖`. -/
lemma norm_piSpatial_extendAlgHom_le {s t : Finset ι} (hst : s ⊆ t) (x : ⨂[ℂ] i : s, A i) :
    ‖CStarRep.piSpatial (fun j : t => CStarRep.gelfandNaimark (A j))
        (PiTensorProduct.extendAlgHom ℂ hst x)‖ ≤
      ‖CStarRep.piSpatial (fun i : s => CStarRep.gelfandNaimark (A i)) x‖ := by
  rw [CStarRep.piSpatial, CStarRep.piSpatial, NonUnitalStarAlgHom.piMapLCompletion_apply,
    NonUnitalStarAlgHom.piMapLCompletion_apply, ContinuousLinearMap.norm_completion,
    ContinuousLinearMap.norm_completion, (InnerPiTensorProduct.finsetSplitLinearIsometryEquiv ℂ
      (fun i => (CStarRep.gelfandNaimark (A i)).H) hst).opNorm_eq_of_intertwine
      (finsetSplitLinearIsometryEquiv_piMapL_extendAlgHom hst x), TensorProduct.norm_mapL]
  exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le

/-- The `⋆`-homomorphism `x ↦ of (x ⊗ 1)` of the algebraic tensor product over `s` into the minimal
tensor product over `t`, whose extension is `PiMinTensorProduct.extend`. -/
noncomputable abbrev ofExtend {s t : Finset ι} (hst : s ⊆ t) :
    (⨂[ℂ] i : s, A i) →⋆ₙₐ[ℂ] (⨂ₘᵢₙ i : t, A i) :=
  (of fun i : t => A i).comp (PiTensorProduct.extendStarAlgHom ℂ hst).toNonUnitalStarAlgHom

/-- For `s ⊆ t`, the `⋆`-homomorphism `x ↦ x ⊗ 1` of the minimal tensor product over `s` into that
over `t`: the extension of `PiTensorProduct.extendStarAlgHom`, contractive for the minimal norms,
and isometric when the algebras are nontrivial (`PiMinTensorProduct.norm_extend`). -/
noncomputable def extend {s t : Finset ι} (hst : s ⊆ t) :
    (⨂ₘᵢₙ i : s, A i) →⋆ₐ[ℂ] (⨂ₘᵢₙ i : t, A i) :=
  let f : (⨂ₘᵢₙ i : s, A i) →⋆ₙₐ[ℂ] (⨂ₘᵢₙ i : t, A i) :=
    (NonUnitalStarSubalgebraClass.subtype (ofExtend hst).closureRange).comp
      (NonUnitalStarAlgHom.closureRangeMap
        (φ := CStarRep.piSpatial fun i : s => CStarRep.gelfandNaimark (A i)) (ψ := ofExtend hst)
        fun x => norm_piSpatial_extendAlgHom_le hst x)
  have hf (x : ⨂[ℂ] i : s, A i) : f (of _ x) = of _ (PiTensorProduct.extendAlgHom ℂ hst x) :=
    congrArg Subtype.val (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict
      (φ := CStarRep.piSpatial fun i : s => CStarRep.gelfandNaimark (A i)) (ψ := ofExtend hst)
      (fun x => norm_piSpatial_extendAlgHom_le hst x) x)
  have h1 : f 1 = 1 := by rw [← of_one, hf, map_one, of_one]
  { f with
    map_one' := h1
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one]
      exact (map_smul f r 1).trans (congrArg (r • ·) h1) }

/-- `PiMinTensorProduct.extend h` is `x ↦ x ⊗ 1` on the algebraic tensor product. -/
@[simp] lemma extend_of {s t : Finset ι} (hst : s ⊆ t) (x : ⨂[ℂ] i : s, A i) :
    extend hst (of _ x) = of _ (PiTensorProduct.extendAlgHom ℂ hst x) :=
  congrArg Subtype.val (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict
    (φ := CStarRep.piSpatial fun i : s => CStarRep.gelfandNaimark (A i)) (ψ := ofExtend hst)
    (fun x => norm_piSpatial_extendAlgHom_le hst x) x)

/-- The `⋆`-homomorphisms `x ↦ x ⊗ 1` form a directed system. -/
instance directedSystem :
    DirectedSystem (fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
      (fun _ _ h => extend (A := A) h) where
  map_self s z := by
    induction z using denseRange_of.induction_on with
    | hp => exact isClosed_eq (map_continuous _) continuous_id
    | ih x =>
      rw [extend_of]
      exact congrArg (of _) ((PiTensorProduct.directedSystemAlgHom (R := ℂ) (A := A)).map_self x)
  map_map u t s hst htu z := by
    induction z using denseRange_of.induction_on with
    | hp => exact isClosed_eq ((map_continuous _).comp (map_continuous _)) (map_continuous _)
    | ih x =>
      rw [extend_of, extend_of, extend_of]
      exact congrArg (of _)
        ((PiTensorProduct.directedSystemAlgHom (R := ℂ) (A := A)).map_map hst htu x)

/-- **Elements of the minimal tensor products over disjoint sets of indices commute** once
extended to a common larger set: `x ⊗ 1` and `1 ⊗ y` commute, as they do on the algebraic tensor
products (`PiTensorProduct.commute_extendAlgHom_of_disjoint`), which are dense. -/
theorem commute_extend_of_disjoint {s₁ s₂ t : Finset ι} (h₁ : s₁ ⊆ t) (h₂ : s₂ ⊆ t)
    (hd : Disjoint s₁ s₂) (x : ⨂ₘᵢₙ i : s₁, A i) (y : ⨂ₘᵢₙ i : s₂, A i) :
    Commute (extend h₁ x) (extend h₂ y) := by
  induction x using denseRange_of.induction_on with
  | hp =>
    exact isClosed_eq ((map_continuous _).mul continuous_const)
      (continuous_const.mul (map_continuous _))
  | ih x =>
    induction y using denseRange_of.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const.mul (map_continuous _))
        ((map_continuous _).mul continuous_const)
    | ih y =>
      rw [extend_of, extend_of]
      exact (PiTensorProduct.commute_extendAlgHom_of_disjoint h₁ h₂ hd x y).map (of _)

section Congr

variable {B : ι → Type u} [∀ i, CStarAlgebra (B i)]

/-- **The extension by `1` commutes with the tensor product of unital `⋆`-homomorphisms** on the
minimal tensor products: `(⨂ eᵢ)(z) ⊗ 1 = (⨂ eᵢ)(z ⊗ 1)`. -/
theorem extend_map {s t : Finset ι} (hst : s ⊆ t) (e : Π i, A i →⋆ₐ[ℂ] B i)
    (z : ⨂ₘᵢₙ i : s, A i) :
    extend hst (map (fun i : s => e i) z) = map (fun i : t => e i) (extend hst z) := by
  induction z using denseRange_of.induction_on with
  | hp =>
    exact isClosed_eq ((map_continuous _).comp (map_continuous _))
      ((map_continuous _).comp (map_continuous _))
  | ih x =>
    rw [map_of, extend_of, extend_of, map_of]
    exact congrArg (of _) (PiTensorProduct.extendAlgHom_mapStarAlgHom hst e x)

/-- The extension by `1` commutes with the tensor product of `⋆`-isomorphisms. -/
theorem extend_congr {s t : Finset ι} (hst : s ⊆ t) (e : Π i, A i ≃⋆ₐ[ℂ] B i)
    (z : ⨂ₘᵢₙ i : s, A i) :
    extend hst (congr (fun i : s => e i) z) = congr (fun i : t => e i) (extend hst z) :=
  extend_map hst (fun i => (e i).toStarAlgHom) z

end Congr

variable [∀ i, Nontrivial (A i)]

/-- **`x ↦ x ⊗ 1` preserves the norm of the tensor product of the representations
`CStarRep.gelfandNaimark (A i)`**: `‖π_t(x ⊗ 1)‖ = ‖π_s(x) ⊗ 1‖ = ‖π_s(x)‖`, the algebras being
nontrivial, so that the Hilbert space over `t \ s` is nonzero. -/
lemma norm_piSpatial_extendAlgHom {s t : Finset ι} (hst : s ⊆ t) (x : ⨂[ℂ] i : s, A i) :
    ‖CStarRep.piSpatial (fun j : t => CStarRep.gelfandNaimark (A j))
        (PiTensorProduct.extendAlgHom ℂ hst x)‖ =
      ‖CStarRep.piSpatial (fun i : s => CStarRep.gelfandNaimark (A i)) x‖ := by
  have (i : ι) : Nontrivial (CStarRep.gelfandNaimark (A i)).H :=
    CStarRep.nontrivial_H_of_injective (CStarRep.gelfandNaimark_injective (A i))
  rw [CStarRep.piSpatial, CStarRep.piSpatial, NonUnitalStarAlgHom.piMapLCompletion_apply,
    NonUnitalStarAlgHom.piMapLCompletion_apply, ContinuousLinearMap.norm_completion,
    ContinuousLinearMap.norm_completion]
  refine ((InnerPiTensorProduct.finsetSplitLinearIsometryEquiv ℂ
    (fun i => (CStarRep.gelfandNaimark (A i)).H) hst).opNorm_eq_of_intertwine
    (finsetSplitLinearIsometryEquiv_piMapL_extendAlgHom hst x)).trans ?_
  rw [TensorProduct.norm_mapL, ContinuousLinearMap.norm_id, mul_one]

/-- **`x ↦ x ⊗ 1` is isometric on the minimal tensor products** of nontrivial unital
C⋆-algebras. -/
theorem norm_extend {s t : Finset ι} (hst : s ⊆ t) (z : ⨂ₘᵢₙ i : s, A i) :
    ‖extend hst z‖ = ‖z‖ := by
  induction z using denseRange_of.induction_on with
  | hp => exact isClosed_eq (map_continuous (extend hst)).norm continuous_norm
  | ih x => rw [extend_of, norm_of, norm_of, norm_piSpatial_extendAlgHom]

/-- The minimal tensor product of a finite family of nontrivial unital C⋆-algebras is nontrivial:
its unit is the identity operator of the Hilbert space tensor product of the nonzero spaces of the
representations `CStarRep.gelfandNaimark (A i)`, which contains the nonzero vector `⨂ ξ i`. -/
instance instNontrivial {κ : Type*} [Fintype κ] {B : κ → Type u} [∀ i, CStarAlgebra (B i)]
    [∀ i, Nontrivial (B i)] : Nontrivial (⨂ₘᵢₙ i, B i) := by
  have (i : κ) : Nontrivial (CStarRep.gelfandNaimark (B i)).H :=
    CStarRep.nontrivial_H_of_injective (CStarRep.gelfandNaimark_injective (B i))
  choose ξ hξ using fun i => exists_ne (0 : (CStarRep.gelfandNaimark (B i)).H)
  set v : Completion (InnerPiTensorProduct ℂ fun i => (CStarRep.gelfandNaimark (B i)).H) :=
    ((InnerPiTensorProduct.tprod ℂ ξ :
      InnerPiTensorProduct ℂ fun i => (CStarRep.gelfandNaimark (B i)).H) :
        Completion (InnerPiTensorProduct ℂ fun i => (CStarRep.gelfandNaimark (B i)).H)) with hv
  have hv0 : v ≠ 0 := by
    rw [← norm_ne_zero_iff, hv, Completion.norm_coe, InnerPiTensorProduct.norm_tprod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => norm_ne_zero_iff.2 (hξ i)
  refine ⟨⟨1, 0, fun h => hv0 ?_⟩⟩
  have h1 := congrArg (fun T => subtype B T v) h
  have e1 : subtype B 1 = 1 := rfl
  simpa only [e1, map_zero, one_apply_eq_self, zero_apply] using h1

/-- The `⋆`-homomorphisms `x ↦ x ⊗ 1` form an isometric directed system. -/
instance isometricSystem :
    DirectLimit.IsometricSystem (G := fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
      (fun _ _ h => extend (A := A) h) where
  norm_map _ _ h z := norm_extend h z

end PiMinTensorProduct

/-! ### The infinite minimal tensor product -/

section Definition

variable {ι : Type*} [DecidableEq ι] (A : ι → Type u) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)]

/-- The direct limit of the minimal tensor products over the finite sets of indices along
`x ↦ x ⊗ 1`, with the minimal norms; its completion is the infinite minimal tensor product. -/
def InfiniteMinTensorProduct.Algebraic : Type _ :=
  NormedDirectLimit (fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
    (fun _ _ h => PiMinTensorProduct.extend (A := A) h)

namespace InfiniteMinTensorProduct.Algebraic

/-- The normed ring structure of `Algebraic A`. -/
noncomputable instance instNormedRing : NormedRing (Algebraic A) :=
  NormedDirectLimit.normedRing

/-- The normed algebra structure of `Algebraic A`. -/
noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (Algebraic A) :=
  NormedDirectLimit.normedAlgebra

/-- The star ring structure of `Algebraic A`. -/
noncomputable instance instStarRing : StarRing (Algebraic A) :=
  inferInstanceAs (StarRing (NormedDirectLimit (fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
    (fun _ _ h => PiMinTensorProduct.extend (A := A) h)))

/-- The star of `Algebraic A` is isometric. -/
instance instNormedStarGroup : NormedStarGroup (Algebraic A) :=
  NormedDirectLimit.normedStarGroup

/-- The norm of `Algebraic A` satisfies the C⋆-identity. -/
instance instCStarRing : CStarRing (Algebraic A) :=
  NormedDirectLimit.cstarRing

/-- The star of `Algebraic A` is conjugate-linear. -/
instance instStarModule : StarModule ℂ (Algebraic A) :=
  inferInstanceAs (StarModule ℂ (NormedDirectLimit
    (fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
    (fun _ _ h => PiMinTensorProduct.extend (A := A) h)))

end InfiniteMinTensorProduct.Algebraic

/-- The **infinite minimal tensor product** of a family of nontrivial unital C⋆-algebras: the
completion of the direct limit of the minimal tensor products over the finite sets of indices along
the isometric `⋆`-homomorphisms `x ↦ x ⊗ 1`. -/
abbrev InfiniteMinTensorProduct : Type _ :=
  Completion (InfiniteMinTensorProduct.Algebraic A)

/-- The infinite minimal tensor product is a C⋆-algebra, by the completion instances. -/
noncomputable instance InfiniteMinTensorProduct.instCStarAlgebra :
    CStarAlgebra (InfiniteMinTensorProduct A) :=
  inferInstance

end Definition

namespace InfiniteMinTensorProduct

variable {ι : Type uι} [DecidableEq ι] {A : ι → Type u} [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)]

namespace Algebraic

variable (A) in
/-- The inclusion of the minimal tensor product over the finite set `s` of indices into the direct
limit, as a `⋆`-algebra homomorphism. -/
noncomputable def of (s : Finset ι) : (⨂ₘᵢₙ i : s, A i) →⋆ₐ[ℂ] Algebraic A :=
  { NormedDirectLimit.ofAlgHom (G := fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
      (f := fun _ _ h => PiMinTensorProduct.extend (A := A) h) ℂ s with
    map_star' := fun x => (NormedDirectLimit.mk_star (G := fun s : Finset ι =>
      (⨂ₘᵢₙ i : s, A i)) (f := fun _ _ h => PiMinTensorProduct.extend (A := A) h)
        s x).symm }

/-- The inclusions into the direct limit are isometric. -/
lemma norm_of (s : Finset ι) (x : ⨂ₘᵢₙ i : s, A i) : ‖of A s x‖ = ‖x‖ :=
  NormedDirectLimit.norm_mk (G := fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
    (f := fun _ _ h => PiMinTensorProduct.extend (A := A) h) s x

/-- The inclusions into the direct limit are compatible with `x ↦ x ⊗ 1`. -/
lemma of_extend {s t : Finset ι} (hst : s ⊆ t) (x : ⨂ₘᵢₙ i : s, A i) :
    of A t (PiMinTensorProduct.extend hst x) = of A s x :=
  NormedDirectLimit.mk_map (G := fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
    (f := fun _ _ h => PiMinTensorProduct.extend (A := A) h) s t hst x

end Algebraic

variable (A) in
/-- The embedding of the minimal tensor product over the finite set `s` of indices into the
infinite minimal tensor product: the inclusion into the direct limit, followed by the inclusion into
its completion. -/
noncomputable def of (s : Finset ι) :
    (⨂ₘᵢₙ i : s, A i) →⋆ₐ[ℂ] InfiniteMinTensorProduct A where
  toFun x := (Algebraic.of A s x : InfiniteMinTensorProduct A)
  map_one' := by simp only [map_one, Completion.coe_one]
  map_mul' x y := by simp only [map_mul, Completion.coe_mul]
  map_zero' := by simp only [map_zero, Completion.coe_zero]
  map_add' x y := by simp only [map_add, Completion.coe_add]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, Completion.coe_smul,
      Completion.coe_one]
  map_star' x := by simp only [map_star, Completion.star_coe]

/-- The embedding is the inclusion into the direct limit followed by the inclusion into its
completion. -/
lemma of_apply (s : Finset ι) (x : ⨂ₘᵢₙ i : s, A i) :
    of A s x = (Algebraic.of A s x : InfiniteMinTensorProduct A) :=
  rfl

/-- The embeddings are compatible with `x ↦ x ⊗ 1`. -/
@[simp] lemma of_extend {s t : Finset ι} (hst : s ⊆ t) (x : ⨂ₘᵢₙ i : s, A i) :
    of A t (PiMinTensorProduct.extend hst x) = of A s x := by
  rw [of_apply, of_apply, Algebraic.of_extend]

/-- **The embeddings of the finite minimal tensor products are isometric.** -/
@[simp] theorem norm_of (s : Finset ι) (x : ⨂ₘᵢₙ i : s, A i) :
    ‖of A s x‖ = ‖x‖ := by
  rw [of_apply, Completion.norm_coe, Algebraic.norm_of]

/-- The infinite minimal tensor product of nontrivial unital C⋆-algebras is nontrivial: the minimal
tensor product over the empty set of indices, which is nontrivial, embeds into it. -/
instance instNontrivial : Nontrivial (InfiniteMinTensorProduct A) :=
  (AddMonoidHomClass.isometry_of_norm _ (norm_of (A := A) ∅)).injective.nontrivial

/-- **The union of the images of the finite minimal tensor products is dense.** -/
theorem dense_iUnion_range_of : Dense (⋃ s : Finset ι, Set.range (of A s)) :=
  (NormedDirectLimit.dense_iUnion_range_coe_mk
    (G := fun s : Finset ι => (⨂ₘᵢₙ i : s, A i))
    (f := fun _ _ h => PiMinTensorProduct.extend (A := A) h)).mono <|
      Set.iUnion_mono fun s => by
        rintro _ ⟨y, rfl⟩
        exact ⟨y, of_apply s y⟩

/-- **For a finite index type, the minimal tensor product over all the indices is the whole infinite
minimal tensor product**: the image of its embedding is complete, hence closed, and contains the
dense images of the other finite minimal tensor products. -/
theorem of_univ_surjective [Fintype ι] : Function.Surjective (of A Finset.univ) := by
  have hiso : Isometry (of A Finset.univ) :=
    AddMonoidHomClass.isometry_of_norm _ (norm_of Finset.univ)
  have hclosed : IsClosed (Set.range (of A Finset.univ)) :=
    hiso.isUniformInducing.isComplete_range.isClosed
  have hdense : Dense (Set.range (of A Finset.univ)) := by
    refine dense_iUnion_range_of.mono (Set.iUnion_subset fun s => ?_)
    rintro _ ⟨x, rfl⟩
    exact ⟨PiMinTensorProduct.extend (Finset.subset_univ s) x, of_extend _ x⟩
  exact Set.range_eq_univ.1 (hclosed.closure_eq.symm.trans hdense.closure_eq)

/-! ### Nuclearity -/

/-- The image of the minimal tensor product over `s` lies in that over any larger finite set. -/
lemma range_of_le {s t : Finset ι} (hst : s ⊆ t) :
    NonUnitalStarAlgHom.range (of A s).toNonUnitalStarAlgHom ≤
      NonUnitalStarAlgHom.range (of A t).toNonUnitalStarAlgHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨PiMinTensorProduct.extend hst x, of_extend hst x⟩

/-- The infinite minimal tensor product is nuclear when its finite stages are, as an inductive limit
of them (`CStarAlgebra.IsNuclear.of_dense_iUnion`). -/
lemma isNuclear_of_stages
    [∀ s : Finset ι, CStarAlgebra.IsNuclear.{v, w} (⨂ₘᵢₙ i : s, A i)] :
    CStarAlgebra.IsNuclear.{v, w} (InfiniteMinTensorProduct A) :=
  CStarAlgebra.IsNuclear.of_dense_iUnion (fun s => (of A s).toNonUnitalStarAlgHom)
    (fun s => (AddMonoidHomClass.isometry_of_norm _ (norm_of s)).injective)
    (fun s t => ⟨s ∪ t, range_of_le Finset.subset_union_left, range_of_le Finset.subset_union_right⟩)
    dense_iUnion_range_of

/-- **The infinite minimal tensor product of nuclear C⋆-algebras is nuclear**: its finite stages are
(`CStarAlgebra.IsNuclear.piMinTensorProduct`), and it is their inductive limit. -/
instance isNuclear [∀ i, CStarAlgebra.IsNuclear.{w, max u w} (A i)] :
    CStarAlgebra.IsNuclear.{w, w'} (InfiniteMinTensorProduct A) :=
  isNuclear_of_stages

/-- **The infinite minimal tensor product of finite-dimensional C⋆-algebras is nuclear**, in every
pair of universes: its finite stages are finite-dimensional. -/
lemma isNuclear_of_finiteDimensional [∀ i, FiniteDimensional ℂ (A i)] :
    CStarAlgebra.IsNuclear.{v, w} (InfiniteMinTensorProduct A) :=
  isNuclear_of_stages

end InfiniteMinTensorProduct
