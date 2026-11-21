/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Normed.Algebra.ProjectiveTensorProduct
public import QuantumSystem.ForMathlib.Analysis.Normed.Group.DirectLimit
public import QuantumSystem.ForMathlib.LinearAlgebra.PiTensorProduct.Extend

/-!
# The infinite projective tensor product of unital normed algebras

For a family `E i` of normed spaces over `ℝ` or `ℂ` and a unit vector `ξ i` in each, the extension
`x ↦ x ⊗ (⨂_{j ∈ t \ s} ξ j)` of the tensor product over a finite set `s` of indices to that over
`t ⊇ s` (`PiTensorProduct.extend`) is isometric for the projective seminorms. It does not increase
them, being the linear map of a multilinear map of norm at most one, and it does not decrease them,
having a left inverse of norm at most one that contracts each added factor `j` by a functional `φ`
of norm one with `φ (ξ j) = 1`.

For a family `A i` of unital normed algebras with `‖1‖ = 1`, indexed by an arbitrary type `ι`, the
algebraic tensor products `⨂[𝕜] i : s, A i` over the finite sets `s` of indices therefore form an
isometric directed system along the algebra homomorphisms `x ↦ x ⊗ 1`
(`PiTensorProduct.extendAlgHom`). The **infinite projective tensor product**
`InfiniteProjectiveTensorProduct 𝕜 A` is the completion of its direct limit, a Banach algebra with
`‖1‖ = 1` in which the projective tensor product over each finite set of indices embeds
isometrically.

## Main definitions

* `InfiniteProjectiveTensorProduct.Algebraic 𝕜 A` — the direct limit, before completion.
* `InfiniteProjectiveTensorProduct 𝕜 A` — the infinite projective tensor product.
* `InfiniteProjectiveTensorProduct.of s` — the isometric algebra homomorphism of the projective
  tensor product over the finite set `s` into it.
* `InfiniteProjectiveTensorProduct.lift g` — the algebra homomorphism into a Banach algebra
  extending a compatible family `g` of contractive algebra homomorphisms.

## Main results

* `PiTensorProduct.norm_extend` — the extension by unit vectors is isometric for the projective
  seminorms.
* `InfiniteProjectiveTensorProduct.norm_of` — the embeddings are isometric;
  `InfiniteProjectiveTensorProduct.of_coe_extendAlgHom` — they are compatible with `x ↦ x ⊗ 1`.
* `InfiniteProjectiveTensorProduct.dense_iUnion_range_of` — the union of their ranges is dense.
* `InfiniteProjectiveTensorProduct.lift_of_coe`, `InfiniteProjectiveTensorProduct.norm_lift_le`,
  `InfiniteProjectiveTensorProduct.algHom_ext` — the universal property among contractive algebra
  homomorphisms into Banach algebras.
* `InfiniteProjectiveTensorProduct.of_univ_surjective` — for a finite index type, the embedding of
  the tensor product over all the indices is onto.
-/

@[expose] public section

open scoped TensorProduct
open UniformSpace

namespace PiTensorProduct

variable {ι : Type*} [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜] {E : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {ξ : Π i, E i}

section Contract

variable {s t : Finset ι} (hst : s ⊆ t) (φ : ∀ j, StrongDual 𝕜 (E j))

/-- The scalar factor `∏_{j ∈ t \ s} φ j (m j)` of the contraction. -/
private noncomputable def contractCoeff (m : Π j : t, E j) : 𝕜 :=
  ∏ j : t, if (j : ι) ∈ s then 1 else φ j (m j)

private lemma contractCoeff_update_of_mem [DecidableEq t] (m : Π j : t, E j) (k : t)
    (hk : (k : ι) ∈ s) (x : E k) : contractCoeff (s := s) φ (Function.update m k x) =
      contractCoeff (s := s) φ m :=
  Finset.prod_congr rfl fun j _ => by
    split_ifs with hj
    · rfl
    · rw [Function.update_of_ne (fun h => hj (by rw [h]; exact hk))]

private lemma contractCoeff_update_of_notMem [DecidableEq t] (m : Π j : t, E j) (k : t)
    (hk : (k : ι) ∉ s) (x : E k) : contractCoeff (s := s) φ (Function.update m k x) =
      φ k x * ∏ j ∈ Finset.univ \ {k}, if (j : ι) ∈ s then 1 else φ j (m j) := by
  have h : (fun j : t => if (j : ι) ∈ s then 1 else φ j (Function.update m k x j)) =
      Function.update (fun j : t => if (j : ι) ∈ s then 1 else φ j (m j)) k (φ k x) := by
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp [hk]
    · simp [Function.update_of_ne hjk]
  rw [contractCoeff, h, Finset.prod_update_of_mem (Finset.mem_univ k)]

omit [DecidableEq ι] [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] in
private lemma restrict_update_of_mem [DecidableEq s] [DecidableEq t] (m : Π j : t, E j) (k : t)
    (hk : (k : ι) ∈ s) (x : E k) :
    (fun i : s => Function.update m k x ⟨i, hst i.2⟩) =
      Function.update (fun i : s => m ⟨i, hst i.2⟩) ⟨k, hk⟩ x :=
  Function.update_comp_eq_of_injective' m (f := fun i : s => (⟨i, hst i.2⟩ : t))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h :)) ⟨k, hk⟩ x

omit [DecidableEq ι] [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] in
private lemma restrict_update_of_notMem [DecidableEq t] (m : Π j : t, E j) (k : t)
    (hk : (k : ι) ∉ s) (x : E k) :
    (fun i : s => Function.update m k x ⟨i, hst i.2⟩) = fun i : s => m ⟨i, hst i.2⟩ :=
  funext fun i => Function.update_of_ne (fun h => hk (by rw [← h]; exact i.2)) _ _

/-- The contraction `⨂_{j ∈ t} m j ↦ (∏_{j ∈ t \ s} φ j (m j)) ⨂_{i ∈ s} m i`, as a multilinear
map. -/
private noncomputable def contractMultilinear :
    MultilinearMap 𝕜 (fun j : t => E j) (⨂[𝕜] i : s, E i) where
  toFun m := contractCoeff (s := s) φ m • tprod 𝕜 fun i : s => m ⟨i, hst i.2⟩
  map_update_add' m k x y := by
    classical
    by_cases hk : (k : ι) ∈ s
    · simp only [contractCoeff_update_of_mem φ m k hk, restrict_update_of_mem hst m k hk,
        MultilinearMap.map_update_add, smul_add]
    · simp only [contractCoeff_update_of_notMem φ m k hk, restrict_update_of_notMem hst m k hk,
        map_add, add_mul, add_smul]
  map_update_smul' m k c x := by
    classical
    by_cases hk : (k : ι) ∈ s
    · simp only [contractCoeff_update_of_mem φ m k hk, restrict_update_of_mem hst m k hk,
        MultilinearMap.map_update_smul, smul_comm (contractCoeff φ m) c]
    · simp only [contractCoeff_update_of_notMem φ m k hk, restrict_update_of_notMem hst m k hk,
        map_smul, smul_eq_mul, mul_assoc, mul_smul]

private lemma norm_contractMultilinear_le (hφ : ∀ j, ‖φ j‖ ≤ 1) (m : Π j : t, E j) :
    ‖contractMultilinear hst φ m‖ ≤ 1 * ∏ j, ‖m j‖ := by
  change ‖contractCoeff (s := s) φ m • tprod 𝕜 fun i : s => m ⟨i, hst i.2⟩‖ ≤ _
  rw [norm_smul, one_mul]
  have hc : ‖contractCoeff (s := s) φ m‖ ≤ ∏ j : t, if (j : ι) ∈ s then 1 else ‖m j‖ := by
    rw [contractCoeff, norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
    split_ifs
    · simp
    · exact ((φ j).le_opNorm (m j)).trans (mul_le_of_le_one_left (norm_nonneg _) (hφ j))
  have ht : ‖(tprod 𝕜 fun i : s => m ⟨i, hst i.2⟩ : ⨂[𝕜] i : s, E i)‖ ≤
      ∏ j : t, if (j : ι) ∈ s then ‖m j‖ else 1 :=
    (projectiveSeminorm_tprod_le _).trans_eq (Finset.prod_subtype_eq_prod_ite hst fun j => ‖m j‖)
  refine (mul_le_mul hc ht (norm_nonneg _)
    (Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)).trans_eq ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by split_ifs <;> simp

private lemma lift_contractMultilinear_extend (hφ : ∀ j, φ j (ξ j) = 1) (x : ⨂[𝕜] i : s, E i) :
    lift (contractMultilinear hst φ) (extend 𝕜 ξ hst x) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, extend_tprod, lift.tprod]
    change r • (contractCoeff (s := s) φ (extendFun (t := t) ξ m) •
      tprod 𝕜 fun i : s => extendFun (t := t) ξ m ⟨i, hst i.2⟩) = _
    have hc : contractCoeff (s := s) φ (extendFun (t := t) ξ m) = 1 := by
      unfold contractCoeff
      refine Finset.prod_eq_one fun j _ => ?_
      split_ifs with hj
      · rfl
      · rw [extendFun_apply_of_notMem _ _ _ hj, hφ]
    have hr : (fun i : s => extendFun (t := t) ξ m ⟨i, hst i.2⟩) = m :=
      funext fun i => extendFun_apply_of_mem ξ m (⟨i, hst i.2⟩ : t) i.2
    rw [hc, one_smul, hr]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Contract

section UnitVectors

variable (hξ : ∀ i, ‖ξ i‖ = 1)
include hξ

/-- The norms of the factors of `extendFun ξ m` multiply to those of `m`, the reference vectors
having norm one. -/
lemma prod_norm_extendFun {s t : Finset ι} (hst : s ⊆ t) (m : Π i : s, E i) :
    ∏ j : t, ‖extendFun ξ m j‖ = ∏ i : s, ‖m i‖ :=
  prod_extendFun₂ ξ ξ hst (fun _ a _ => ‖a‖) hξ m m

/-- The extension by unit vectors does not increase the projective seminorm: it is the linear map
of the multilinear map `m ↦ ⨂ extendFun ξ m`, of norm at most one. -/
lemma norm_extend_le {s t : Finset ι} (hst : s ⊆ t) (x : ⨂[𝕜] i : s, E i) :
    ‖extend 𝕜 ξ hst x‖ ≤ ‖x‖ := by
  let F : ContinuousMultilinearMap 𝕜 (fun i : s => E i) (⨂[𝕜] i : t, E i) :=
    (extendMultilinear (R := 𝕜) ξ hst).mkContinuous 1 fun m => by
      rw [one_mul, ← prod_norm_extendFun hξ hst m]
      change ‖(tprod 𝕜 (extendFun (t := t) ξ m) : ⨂[𝕜] i : t, E i)‖ ≤ _
      exact projectiveSeminorm_tprod_le _
  have hF : ‖F‖ ≤ 1 := MultilinearMap.mkContinuous_norm_le _ zero_le_one _
  exact (norm_eval_le_projectiveSeminorm F x).trans (mul_le_of_le_one_left (norm_nonneg _) hF)

/-- **The extension by unit vectors is isometric for the projective seminorms**: it does not
increase the seminorm, and it has a left inverse that does not either, contracting each added
factor `j` by a functional `φ` of norm one with `φ (ξ j) = 1`. -/
theorem norm_extend {s t : Finset ι} (hst : s ⊆ t) (x : ⨂[𝕜] i : s, E i) :
    ‖extend 𝕜 ξ hst x‖ = ‖x‖ := by
  refine le_antisymm (norm_extend_le hξ hst x) ?_
  have hφ : ∀ j, ∃ g : StrongDual 𝕜 (E j), ‖g‖ = 1 ∧ g (ξ j) = 1 := fun j => by
    obtain ⟨g, hg, hg1⟩ := exists_dual_vector 𝕜 (ξ j) (by rw [hξ j]; exact one_ne_zero)
    exact ⟨g, hg, by rw [hg1, hξ j, RCLike.ofReal_one]⟩
  choose φ hφ₁ hφ₂ using hφ
  let C : ContinuousMultilinearMap 𝕜 (fun j : t => E j) (⨂[𝕜] i : s, E i) :=
    (contractMultilinear hst φ).mkContinuous 1 (norm_contractMultilinear_le hst φ fun j => (hφ₁ j).le)
  calc ‖x‖ = ‖lift C.toMultilinearMap (extend 𝕜 ξ hst x)‖ := by
        conv_lhs => rw [← lift_contractMultilinear_extend hst φ hφ₂ x]
        rfl
    _ ≤ ‖C‖ * ‖extend 𝕜 ξ hst x‖ := norm_eval_le_projectiveSeminorm C _
    _ ≤ ‖extend 𝕜 ξ hst x‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (MultilinearMap.mkContinuous_norm_le _ zero_le_one _)

end UnitVectors

/-- For unital normed algebras with `‖1‖ = 1`, the algebra homomorphisms `x ↦ x ⊗ 1` form an
isometric directed system. -/
instance isometricSystem {A : ι → Type*} [∀ i, SeminormedRing (A i)] [∀ i, NormedAlgebra 𝕜 (A i)]
    [∀ i, NormOneClass (A i)] :
    DirectLimit.IsometricSystem (G := fun s : Finset ι => ⨂[𝕜] i : s, A i)
      (fun _ _ h => extendAlgHom 𝕜 (A := A) h) where
  norm_map _ _ h x := norm_extend (fun _ => norm_one) h x

end PiTensorProduct

section Definition

variable {ι : Type*} [DecidableEq ι] (𝕜 : Type*) [RCLike 𝕜] (A : ι → Type*) [∀ i, SeminormedRing (A i)]
  [∀ i, NormedAlgebra 𝕜 (A i)] [∀ i, NormOneClass (A i)]

/-- The direct limit of the tensor products over the finite sets of indices along `x ↦ x ⊗ 1`, with
the projective seminorms; its image in its completion, the infinite projective tensor product, is
dense. -/
def InfiniteProjectiveTensorProduct.Algebraic : Type _ :=
  NormedDirectLimit (fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h)

namespace InfiniteProjectiveTensorProduct.Algebraic

/-- The seminormed ring structure of `Algebraic 𝕜 A`. -/
noncomputable instance instSeminormedRing : SeminormedRing (Algebraic 𝕜 A) :=
  NormedDirectLimit.seminormedRing

/-- The normed algebra structure of `Algebraic 𝕜 A`. -/
noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 (Algebraic 𝕜 A) :=
  NormedDirectLimit.normedAlgebra

end InfiniteProjectiveTensorProduct.Algebraic

/-- The **infinite projective tensor product** of a family of unital normed algebras with
`‖1‖ = 1`: the completion of the direct limit of the tensor products over the finite sets of
indices along `x ↦ x ⊗ 1`, for the projective seminorms. -/
abbrev InfiniteProjectiveTensorProduct : Type _ :=
  Completion (InfiniteProjectiveTensorProduct.Algebraic 𝕜 A)

end Definition

namespace InfiniteProjectiveTensorProduct

variable {ι : Type*} [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜] {A : ι → Type*} [∀ i, SeminormedRing (A i)]
  [∀ i, NormedAlgebra 𝕜 (A i)] [∀ i, NormOneClass (A i)]

/-- The infinite projective tensor product is a normed algebra; its ring structure, norm and
completeness are those of the completion. -/
noncomputable instance instNormedAlgebra :
    NormedAlgebra 𝕜 (InfiniteProjectiveTensorProduct 𝕜 A) where
  norm_smul_le := norm_smul_le

namespace Algebraic

variable (𝕜 A) in
/-- The inclusion of the tensor product over the finite set `s` of indices into the direct
limit. -/
noncomputable def of (s : Finset ι) : (⨂[𝕜] i : s, A i) →ₐ[𝕜] Algebraic 𝕜 A :=
  NormedDirectLimit.ofAlgHom (G := fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (f := fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h) 𝕜 s

/-- The inclusions into the direct limit are isometric. -/
lemma norm_of (s : Finset ι) (y : ⨂[𝕜] i : s, A i) : ‖of 𝕜 A s y‖ = ‖y‖ :=
  NormedDirectLimit.norm_mk (G := fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (f := fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h) s y

/-- The inclusions into the direct limit are compatible with `x ↦ x ⊗ 1`. -/
lemma of_extendAlgHom {s t : Finset ι} (h : s ⊆ t) (y : ⨂[𝕜] i : s, A i) :
    of 𝕜 A t (PiTensorProduct.extendAlgHom 𝕜 h y) = of 𝕜 A s y :=
  NormedDirectLimit.mk_map (G := fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (f := fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h) s t h y

/-- Every element of the direct limit comes from the tensor product over a finite set. -/
@[elab_as_elim] lemma induction {C : Algebraic 𝕜 A → Prop} (ih : ∀ s y, C (of 𝕜 A s y))
    (z : Algebraic 𝕜 A) : C z :=
  NormedDirectLimit.induction (G := fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (f := fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h) ih z

/-- The inclusions into the direct limit are uniformly continuous. -/
lemma uniformContinuous_of (s : Finset ι) : UniformContinuous (of 𝕜 A s) :=
  (AddMonoidHomClass.isometry_of_norm (of 𝕜 A s) (norm_of s)).uniformContinuous

end Algebraic

variable (𝕜 A) in
/-- The embedding of the projective tensor product over the finite set `s` of indices into the
infinite projective tensor product: the completion of the inclusion of the component `s` of the
direct limit. -/
noncomputable def of (s : Finset ι) :
    ProjectiveTensorProduct 𝕜 (fun i : s => A i) →ₐ[𝕜] InfiniteProjectiveTensorProduct 𝕜 A where
  __ := Completion.mapRingHom (Algebraic.of 𝕜 A s).toRingHom (Algebraic.uniformContinuous_of s).continuous
  commutes' r := by
    change Completion.map (Algebraic.of 𝕜 A s) (algebraMap 𝕜 (Completion (⨂[𝕜] i : s, A i)) r) = _
    rw [Completion.algebraMap_def, Completion.algebraMap_def,
      Completion.map_coe (Algebraic.uniformContinuous_of s), AlgHom.commutes]

/-- On the algebraic tensor product over `s`, the embedding is the inclusion into the direct
limit. -/
lemma of_coe (s : Finset ι) (y : ⨂[𝕜] i : s, A i) :
    of 𝕜 A s (y : ProjectiveTensorProduct 𝕜 (fun i : s => A i)) =
      (Algebraic.of 𝕜 A s y : InfiniteProjectiveTensorProduct 𝕜 A) :=
  Completion.map_coe (Algebraic.uniformContinuous_of s) y

/-- The embeddings are continuous. -/
lemma continuous_of (s : Finset ι) : Continuous (of 𝕜 A s) :=
  Completion.continuous_map

/-- **The embeddings of the finite projective tensor products are isometric.** -/
theorem norm_of (s : Finset ι) (x : ProjectiveTensorProduct 𝕜 (fun i : s => A i)) :
    ‖of 𝕜 A s x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_of s).norm continuous_norm
  | ih y =>
    rw [of_coe, Completion.norm_coe, Completion.norm_coe]
    exact Algebraic.norm_of s y

/-- The embeddings are compatible with `x ↦ x ⊗ 1`. -/
lemma of_coe_extendAlgHom {s t : Finset ι} (h : s ⊆ t) (y : ⨂[𝕜] i : s, A i) :
    of 𝕜 A t ((PiTensorProduct.extendAlgHom 𝕜 h y : ⨂[𝕜] i : t, A i) :
      ProjectiveTensorProduct 𝕜 (fun i : t => A i)) =
      of 𝕜 A s (y : ProjectiveTensorProduct 𝕜 (fun i : s => A i)) := by
  rw [of_coe, of_coe, Algebraic.of_extendAlgHom]

/-- **The union of the ranges of the embeddings of the finite projective tensor products is
dense.** -/
theorem dense_iUnion_range_of : Dense (⋃ s : Finset ι, Set.range (of 𝕜 A s)) :=
  (NormedDirectLimit.dense_iUnion_range_coe_mk (G := fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (f := fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h)).mono <|
      Set.iUnion_mono fun s => by
        rintro _ ⟨y, rfl⟩
        exact ⟨y, of_coe s y⟩

/-- **The unit of the infinite projective tensor product has norm one.** -/
instance instNormOneClass : NormOneClass (InfiniteProjectiveTensorProduct 𝕜 A) where
  norm_one := by
    rw [← Completion.coe_one, Completion.norm_coe, ← map_one (Algebraic.of 𝕜 A ∅),
      Algebraic.norm_of, PiTensorProduct.one_def, PiTensorProduct.norm_tprod]
    simp

section Lift

variable {C : Type*} [NormedRing C] [NormedAlgebra 𝕜 C] [CompleteSpace C]
  (g : ∀ s : Finset ι, (⨂[𝕜] i : s, A i) →ₐ[𝕜] C)
  (hcompat : ∀ s t (h : s ⊆ t) x, g t (PiTensorProduct.extendAlgHom 𝕜 h x) = g s x)
  (hg : ∀ s x, ‖g s x‖ ≤ ‖x‖)

/-- The algebra homomorphism out of the direct limit given by a compatible family. -/
noncomputable def liftAlgebraic : Algebraic 𝕜 A →ₐ[𝕜] C :=
  DirectLimit.Algebra.lift (fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h) C g hcompat

omit [CompleteSpace C] in
/-- The algebra homomorphism out of the direct limit restricts to `g s`. -/
lemma liftAlgebraic_of (s : Finset ι) (y : ⨂[𝕜] i : s, A i) :
    liftAlgebraic g hcompat (Algebraic.of 𝕜 A s y) = g s y :=
  rfl

omit [CompleteSpace C] in
include hg in
/-- The algebra homomorphism out of the direct limit of a contractive family is contractive. -/
lemma norm_liftAlgebraic_le (z : Algebraic 𝕜 A) : ‖liftAlgebraic g hcompat z‖ ≤ ‖z‖ := by
  induction z using Algebraic.induction with | _ s y
  rw [liftAlgebraic_of, Algebraic.norm_of]
  exact hg s y

omit [CompleteSpace C] in
include hg in
/-- The algebra homomorphism out of the direct limit of a contractive family is uniformly
continuous. -/
lemma uniformContinuous_liftAlgebraic : UniformContinuous (liftAlgebraic g hcompat) :=
  AddMonoidHomClass.uniformContinuous_of_bound (liftAlgebraic g hcompat) 1 fun z => by
    rw [one_mul]
    exact norm_liftAlgebraic_le g hcompat hg z

/-- **The universal property**: a compatible family `g` of contractive algebra homomorphisms from
the tensor products over the finite sets of indices into a Banach algebra extends to an algebra
homomorphism of the infinite projective tensor product. -/
noncomputable def lift : InfiniteProjectiveTensorProduct 𝕜 A →ₐ[𝕜] C where
  __ := Completion.extensionHom (liftAlgebraic g hcompat).toRingHom
    (uniformContinuous_liftAlgebraic g hcompat hg).continuous
  commutes' r := by
    change Completion.extension (liftAlgebraic g hcompat)
      (algebraMap 𝕜 (InfiniteProjectiveTensorProduct 𝕜 A) r) = _
    rw [Completion.algebraMap_def, Completion.extension_coe (uniformContinuous_liftAlgebraic g hcompat hg),
      AlgHom.commutes]

/-- The extension of `g` restricts to `g s` on the tensor product over `s`. -/
lemma lift_of_coe (s : Finset ι) (y : ⨂[𝕜] i : s, A i) :
    lift g hcompat hg (of 𝕜 A s (y : ProjectiveTensorProduct 𝕜 (fun i : s => A i))) = g s y := by
  rw [of_coe]
  exact (Completion.extension_coe (uniformContinuous_liftAlgebraic g hcompat hg) _).trans
    (liftAlgebraic_of g hcompat s y)

/-- The extension of a contractive family is continuous. -/
lemma continuous_lift : Continuous (lift g hcompat hg) :=
  Completion.continuous_extension

/-- The extension of a contractive family is contractive. -/
theorem norm_lift_le (z : InfiniteProjectiveTensorProduct 𝕜 A) : ‖lift g hcompat hg z‖ ≤ ‖z‖ := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (continuous_lift g hcompat hg).norm continuous_norm
  | ih z =>
    change ‖Completion.extension (liftAlgebraic g hcompat) z‖ ≤ _
    rw [Completion.extension_coe (uniformContinuous_liftAlgebraic g hcompat hg), Completion.norm_coe]
    exact norm_liftAlgebraic_le g hcompat hg z

end Lift

/-- Two continuous algebra homomorphisms out of the infinite projective tensor product that agree on
the tensor products over the finite sets of indices are equal. -/
lemma algHom_ext {C : Type*} [NormedRing C] [NormedAlgebra 𝕜 C]
    {φ ψ : InfiniteProjectiveTensorProduct 𝕜 A →ₐ[𝕜] C} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ (s : Finset ι) (y : ⨂[𝕜] i : s, A i),
      φ (of 𝕜 A s (y : ProjectiveTensorProduct 𝕜 (fun i : s => A i))) =
        ψ (of 𝕜 A s (y : ProjectiveTensorProduct 𝕜 (fun i : s => A i)))) :
    φ = ψ := by
  ext z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq hφ hψ
  | ih z =>
    induction z using Algebraic.induction with | _ s y
    rw [← of_coe]
    exact h s y

/-- **For a finite index type, the embedding of the projective tensor product over all the indices
is onto**: its range is complete, hence closed, and contains the dense direct limit. -/
theorem of_univ_surjective [Fintype ι] :
    Function.Surjective (of 𝕜 A Finset.univ) :=
  NormedDirectLimit.completion_map_mk_surjective (G := fun s : Finset ι => ⨂[𝕜] i : s, A i)
    (f := fun _ _ h => PiTensorProduct.extendAlgHom 𝕜 (A := A) h) Finset.univ
    fun s => Finset.subset_univ s

end InfiniteProjectiveTensorProduct
