/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Operator.Extend
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.PiTensorProduct
public import QuantumSystem.ForMathlib.Analysis.Normed.Group.DirectLimit
public import QuantumSystem.ForMathlib.LinearAlgebra.PiTensorProduct.Extend

/-!
# The infinite tensor product of inner product spaces with a unit vector in each

For a family `E i` of inner product spaces over `ℝ` or `ℂ`, indexed by an arbitrary type `ι`, and a
unit vector `Ω i` in each, the tensor products `⨂_{i ∈ s} E i` over the finite sets `s` of indices,
with their inner products (`InnerPiTensorProduct`), form a directed system along the maps
`x ↦ x ⊗ (⨂_{j ∈ t \ s} Ω j)` (`InnerPiTensorProduct.extend`), which preserve the inner product as
`⟪Ω j, Ω j⟫ = 1`. The **infinite tensor product** `InfiniteHilbertTensorProduct 𝕜 E Ω` is the
completion of the direct limit, a Hilbert space in which each finite tensor product embeds
isometrically. It depends on the unit vectors `Ω`, which make the product vector `⨂ i, Ω i` a unit
vector of it.

## Main definitions

* `InnerPiTensorProduct.extend Ω h` — `x ↦ x ⊗ (⨂_{j ∈ t \ s} Ω j)`, for `h : s ⊆ t`.
* `InfiniteHilbertTensorProduct.Algebraic 𝕜 E Ω` — the direct limit, before completion.
* `InfiniteHilbertTensorProduct 𝕜 E Ω` — the infinite tensor product along `Ω`.
* `InfiniteHilbertTensorProduct.of 𝕜 Ω s` — the linear isometry of the completed tensor product
  over the finite set `s` of indices into it.
* `InfiniteHilbertTensorProduct.ofTprod 𝕜 Ω s x` — the product vector `⨂_{i ∈ s} x i` in it.
* `InfiniteHilbertTensorProduct.productVector 𝕜 Ω` — the product vector `⨂ i, Ω i`.

## Main results

* `InnerPiTensorProduct.inner_extend` — `x ↦ x ⊗ Ω` preserves the inner product.
* `InfiniteHilbertTensorProduct.of_coe_extend` — the embeddings are compatible with `x ↦ x ⊗ Ω`.
* `InfiniteHilbertTensorProduct.dense_iUnion_range_of` — the union of their ranges is dense.
* `InfiniteHilbertTensorProduct.inner_ofTprod_ofTprod` — the inner product of two product vectors
  given on finite sets `s` and `t` of indices is `∏_{i ∈ s ∪ t} ⟪x i, y i⟫`, each family being
  completed by `Ω`.
* `InfiniteHilbertTensorProduct.ofTprod_eq_productVector`,
  `InfiniteHilbertTensorProduct.norm_productVector` — the product vector restricts to
  `⨂_{i ∈ s} Ω i` on each finite set, and is a unit vector.
* `InfiniteHilbertTensorProduct.of_univ_surjective` — for a finite index type, the embedding of the
  tensor product over all the indices is onto.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace
open UniformSpace

variable {ι 𝕜 : Type*} [DecidableEq ι] [RCLike 𝕜] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] (Ω : ∀ i, Metric.sphere (0 : E i) 1)

namespace InnerPiTensorProduct

/-- The **extension by the unit vectors** `Ω` from the tensor product over `s` to the tensor product
over `t ⊇ s`: `x ↦ x ⊗ (⨂_{j ∈ t \ s} Ω j)`. -/
noncomputable def extend {s t : Finset ι} (h : s ⊆ t) :
    InnerPiTensorProduct 𝕜 (fun i : s => E i) →ₗ[𝕜] InnerPiTensorProduct 𝕜 (fun i : t => E i) :=
  (linearEquiv 𝕜 _).toLinearMap ∘ₗ PiTensorProduct.extend 𝕜 (fun i => (Ω i : E i)) h ∘ₗ
    (linearEquiv 𝕜 _).symm.toLinearMap

/-- Through `InnerPiTensorProduct.linearEquiv`, `InnerPiTensorProduct.extend Ω h` is
`PiTensorProduct.extend` along the unit vectors. -/
lemma extend_linearEquiv {s t : Finset ι} (h : s ⊆ t) (x : ⨂[𝕜] i : s, E i) :
    extend Ω h (linearEquiv 𝕜 _ x) =
      linearEquiv 𝕜 _ (PiTensorProduct.extend 𝕜 (fun i => (Ω i : E i)) h x) :=
  rfl

/-- **`x ↦ x ⊗ Ω` preserves the inner product**, as `⟪Ω j, Ω j⟫ = 1`. -/
theorem inner_extend {s t : Finset ι} (h : s ⊆ t)
    (x y : InnerPiTensorProduct 𝕜 (fun i : s => E i)) :
    ⟪extend Ω h x, extend Ω h y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  obtain ⟨x, rfl⟩ := (linearEquiv 𝕜 (fun i : s => E i)).surjective x
  obtain ⟨y, rfl⟩ := (linearEquiv 𝕜 (fun i : s => E i)).surjective y
  rw [extend_linearEquiv, extend_linearEquiv, inner_linearEquiv, inner_linearEquiv]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' n =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, PiTensorProduct.extend_tprod,
        PiTensorProduct.innerₛₗ_tprod]
      rw [PiTensorProduct.prod_extendFun₂ (fun i => (Ω i : E i)) (fun i => (Ω i : E i)) h
        (fun _ a b => ⟪a, b⟫_𝕜) (fun j => by simp [inner_self_eq_norm_sq_to_K, norm_eq_of_mem_sphere])]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- `x ↦ x ⊗ Ω` is isometric. -/
lemma norm_extend {s t : Finset ι} (h : s ⊆ t) (x : InnerPiTensorProduct 𝕜 (fun i : s => E i)) :
    ‖extend Ω h x‖ = ‖x‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜, @norm_eq_sqrt_re_inner 𝕜, inner_extend]

/-- The extensions by the unit vectors form a directed system over the finite sets of indices. -/
instance directedSystem :
    DirectedSystem (fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
      (fun _ _ h => extend Ω h) where
  map_self _ x := (PiTensorProduct.directedSystem (R := 𝕜) (A := E) (fun i => (Ω i : E i))).map_self x
  map_map _ _ _ hst htu x := PiTensorProduct.extend_extend (R := 𝕜) (fun i => (Ω i : E i)) hst htu x

/-- The extensions by the unit vectors form an isometric directed system. -/
instance isometricSystem :
    DirectLimit.IsometricSystem (G := fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
      (fun _ _ h => extend Ω h) where
  norm_map _ _ h x := norm_extend Ω h x

end InnerPiTensorProduct

section Definition

variable (𝕜 E)

/-- The direct limit of the tensor products over the finite sets of indices along `x ↦ x ⊗ Ω`, with
their inner products; its image in its completion, the infinite tensor product, is dense. -/
def InfiniteHilbertTensorProduct.Algebraic : Type _ :=
  NormedDirectLimit (fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
    (fun _ _ h => InnerPiTensorProduct.extend Ω h)

namespace InfiniteHilbertTensorProduct.Algebraic

/-- The norm of `Algebraic 𝕜 E Ω`. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Algebraic 𝕜 E Ω) :=
  NormedDirectLimit.normedAddCommGroup

/-- The inner product of `Algebraic 𝕜 E Ω`. -/
noncomputable instance instInnerProductSpace : InnerProductSpace 𝕜 (Algebraic 𝕜 E Ω) :=
  NormedDirectLimit.innerProductSpace

end InfiniteHilbertTensorProduct.Algebraic

/-- The **infinite tensor product** of a family of inner product spaces along unit vectors `Ω`: the
completion of the direct limit of the tensor products over the finite sets of indices along
`x ↦ x ⊗ Ω`, a Hilbert space. -/
abbrev InfiniteHilbertTensorProduct : Type _ :=
  Completion (InfiniteHilbertTensorProduct.Algebraic 𝕜 E Ω)

end Definition

namespace InfiniteHilbertTensorProduct

namespace Algebraic

/-- The inclusion of the tensor product over the finite set `s` of indices into the direct
limit. -/
noncomputable def of (s : Finset ι) :
    InnerPiTensorProduct 𝕜 (fun i : s => E i) →ₗᵢ[𝕜] Algebraic 𝕜 E Ω :=
  NormedDirectLimit.ofₗᵢ (G := fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
    (f := fun _ _ h => InnerPiTensorProduct.extend Ω h) 𝕜 s

/-- The inclusions into the direct limit are compatible with `x ↦ x ⊗ Ω`. -/
lemma of_extend {s t : Finset ι} (h : s ⊆ t) (x : InnerPiTensorProduct 𝕜 (fun i : s => E i)) :
    of Ω t (InnerPiTensorProduct.extend Ω h x) = of Ω s x :=
  NormedDirectLimit.mk_map (G := fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
    (f := fun _ _ h => InnerPiTensorProduct.extend Ω h) s t h x

/-- Every element of the direct limit comes from the tensor product over a finite set. -/
@[elab_as_elim] lemma induction {C : Algebraic 𝕜 E Ω → Prop} (ih : ∀ s x, C (of Ω s x))
    (z : Algebraic 𝕜 E Ω) : C z :=
  NormedDirectLimit.induction (G := fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
    (f := fun _ _ h => InnerPiTensorProduct.extend Ω h) ih z

end Algebraic

variable (𝕜) in
/-- The embedding of the completed tensor product over the finite set `s` of indices into the
infinite tensor product, a linear isometry. -/
noncomputable def of (s : Finset ι) :
    Completion (InnerPiTensorProduct 𝕜 (fun i : s => E i)) →ₗᵢ[𝕜] InfiniteHilbertTensorProduct 𝕜 E Ω :=
  (Algebraic.of Ω s).completion

/-- On the tensor product over `s`, the embedding is the inclusion into the direct limit. -/
lemma of_coe (s : Finset ι) (x : InnerPiTensorProduct 𝕜 (fun i : s => E i)) :
    of 𝕜 Ω s x = (Algebraic.of Ω s x : InfiniteHilbertTensorProduct 𝕜 E Ω) :=
  LinearIsometry.completion_apply_coe _ x

/-- The embeddings are compatible with `x ↦ x ⊗ Ω`. -/
lemma of_coe_extend {s t : Finset ι} (h : s ⊆ t) (x : InnerPiTensorProduct 𝕜 (fun i : s => E i)) :
    of 𝕜 Ω t (InnerPiTensorProduct.extend Ω h x) = of 𝕜 Ω s x := by
  rw [of_coe, of_coe, Algebraic.of_extend]

/-- **The union of the ranges of the embeddings of the finite tensor products is dense.** -/
theorem dense_iUnion_range_of : Dense (⋃ s : Finset ι, Set.range (of 𝕜 Ω s)) :=
  (NormedDirectLimit.dense_iUnion_range_coe_mk
    (G := fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
    (f := fun _ _ h => InnerPiTensorProduct.extend Ω h)).mono <|
      Set.iUnion_mono fun s => by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, of_coe Ω s x⟩

variable (𝕜) in
/-- The product vector `⨂_{i ∈ s} x i` of the tensor product over the finite set `s`, in the
infinite tensor product. -/
noncomputable def ofTprod (s : Finset ι) (x : Π i : s, E i) : InfiniteHilbertTensorProduct 𝕜 E Ω :=
  of 𝕜 Ω s (InnerPiTensorProduct.tprod 𝕜 x :
    Completion (InnerPiTensorProduct 𝕜 (fun i : s => E i)))

/-- A product vector given on `s` is the product vector given on `t ⊇ s` completed by `Ω`. -/
lemma ofTprod_extendFun {s t : Finset ι} (h : s ⊆ t) (x : Π i : s, E i) :
    ofTprod 𝕜 Ω t (PiTensorProduct.extendFun (fun i => (Ω i : E i)) x) = ofTprod 𝕜 Ω s x := by
  rw [ofTprod, ofTprod, ← of_coe_extend Ω h, ← InnerPiTensorProduct.linearEquiv_tprod x,
    InnerPiTensorProduct.extend_linearEquiv, PiTensorProduct.extend_tprod,
    InnerPiTensorProduct.linearEquiv_tprod]

/-- **The inner product of two product vectors** given on finite sets `s` and `t` of indices is
`∏_{i ∈ s ∪ t} ⟪x i, y i⟫`, each family being completed by the unit vectors `Ω`. -/
theorem inner_ofTprod_ofTprod {s t : Finset ι} (x : Π i : s, E i) (y : Π i : t, E i) :
    ⟪ofTprod 𝕜 Ω s x, ofTprod 𝕜 Ω t y⟫_𝕜 =
      ∏ i : (s ∪ t : Finset ι), ⟪PiTensorProduct.extendFun (fun i => (Ω i : E i)) x i,
        PiTensorProduct.extendFun (fun i => (Ω i : E i)) y i⟫_𝕜 := by
  rw [← ofTprod_extendFun Ω Finset.subset_union_left x,
    ← ofTprod_extendFun Ω Finset.subset_union_right y, ofTprod, ofTprod,
    LinearIsometry.inner_map_map, Completion.inner_coe, InnerPiTensorProduct.inner_tprod]

variable (𝕜) in
/-- The **product vector** `⨂ i, Ω i` of the infinite tensor product: the image of the empty tensor
product. -/
noncomputable def productVector : InfiniteHilbertTensorProduct 𝕜 E Ω :=
  ofTprod 𝕜 Ω ∅ fun i => (Ω i : E i)

/-- The product vector restricts to `⨂_{i ∈ s} Ω i` on each finite set `s` of indices. -/
lemma ofTprod_eq_productVector (s : Finset ι) :
    ofTprod 𝕜 Ω s (fun i => (Ω i : E i)) = productVector 𝕜 Ω := by
  rw [productVector, ← ofTprod_extendFun Ω (Finset.empty_subset s)]
  congr 1

/-- **The product vector is a unit vector.** -/
theorem norm_productVector : ‖productVector 𝕜 Ω‖ = 1 := by
  rw [productVector, ofTprod, LinearIsometry.norm_map, Completion.norm_coe,
    InnerPiTensorProduct.norm_tprod]
  exact Finset.prod_eq_one fun i _ => norm_eq_of_mem_sphere (Ω i)

/-- **For a finite index type, the embedding of the completed tensor product over all the indices is
onto**: the completion of a component at a greatest index is the whole completion. -/
theorem of_univ_surjective [Fintype ι] : Function.Surjective (of 𝕜 Ω Finset.univ) := by
  rw [of, LinearIsometry.coe_completion]
  exact NormedDirectLimit.completion_map_mk_surjective
    (G := fun s : Finset ι => InnerPiTensorProduct 𝕜 (fun i : s => E i))
    (f := fun _ _ h => InnerPiTensorProduct.extend Ω h) Finset.univ fun s => Finset.subset_univ s

end InfiniteHilbertTensorProduct
