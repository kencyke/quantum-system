/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.Multiplier
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Maximal

/-!
# Associativity of the maximal tensor product

A `⋆`-homomorphism `Ψ` of `(A ⊗ₘₐₓ B) ⊗[ℂ] C` into a C⋆-algebra is bounded, on the triple algebraic
tensor product, by the norm of `A ⊗ₘₐₓ (B ⊗ₘₐₓ C)`
(`MaxTensorProduct.norm_apply_le_norm_of_assoc`). The three factors act on the triple tensor product
`(A ⊗[ℂ] B) ⊗[ℂ] C` by left and right multiplication, boundedly for the seminorm of `Ψ`
(`MultiplierAction.norm_map_lmul_le`). The actions therefore extend to commuting `⋆`-homomorphisms
`π_A`, `π_B`, `π_C` into the multiplier algebra of the closure of the range of `Ψ`, with
`π_A(a) π_B(b) π_C(c) = Ψ (a ⊗ b ⊗ c)` (`MultiplierAction.toMultiplier`). Then `π_B × π_C` extends
to `B ⊗ₘₐₓ C`, and its product with `π_A` is a `⋆`-homomorphism of `A ⊗[ℂ] (B ⊗ₘₐₓ C)` agreeing
with `Ψ`; the maximal norm bounds it.

Reversing the order of the factors with `MaxTensorProduct.comm` gives the mirror bound
(`MaxTensorProduct.norm_apply_assoc_le_norm_of`), so the maximal norms of `(A ⊗ₘₐₓ B) ⊗ₘₐₓ C` and of
`A ⊗ₘₐₓ (B ⊗ₘₐₓ C)` agree on the triple algebraic tensor product (`MaxTensorProduct.norm_of_assoc`),
and the two algebras are `⋆`-isomorphic by `(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)` (`MaxTensorProduct.assoc`).

## Main definitions

* `MaxTensorProduct.assoc A B C` — `(A ⊗ₘₐₓ B) ⊗ₘₐₓ C ≃⋆ₐ[ℂ] A ⊗ₘₐₓ (B ⊗ₘₐₓ C)`.

## Main results

* `MaxTensorProduct.norm_apply_le_norm_of_assoc` — the bound of `Ψ` by the norm of
  `A ⊗ₘₐₓ (B ⊗ₘₐₓ C)`.
* `MaxTensorProduct.norm_apply_assoc_le_norm_of` — the mirror bound.
* `MaxTensorProduct.norm_of_assoc` — the associativity of the maximal norm.
-/

@[expose] public section

open scoped TensorProduct MaxTensorProduct MultiplierAlgebra CStarAlgebra

open NonUnitalStarAlgHom

namespace MaxTensorProduct

variable {A B C D : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-! ### The seminorm of a `⋆`-homomorphism of the triple tensor product -/

section Triple

variable (Ψ : (A ⊗ₘₐₓ B) ⊗[ℂ] C →⋆ₙₐ[ℂ] D)

/-- A `⋆`-homomorphism of `(A ⊗ₘₐₓ B) ⊗[ℂ] C`, read on the triple algebraic tensor product. -/
private noncomputable def triple : (A ⊗[ℂ] B) ⊗[ℂ] C →⋆ₙₐ[ℂ] D :=
  Ψ.comp (NonUnitalStarAlgebra.TensorProduct.map (of A B) (NonUnitalStarAlgHom.id ℂ C))

/-- A property of the triple tensor product closed under addition holds once it holds on pure
tensors. -/
private lemma triple_induction {P : (A ⊗[ℂ] B) ⊗[ℂ] C → Prop}
    (h : ∀ a b c, P ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) (hadd : ∀ x y, P x → P y → P (x + y))
    (x : (A ⊗[ℂ] B) ⊗[ℂ] C) : P x := by
  induction x using TensorProduct.inductionOn with
  | tmul y c =>
    induction y using TensorProduct.inductionOn with
    | tmul a b => exact h a b c
    | add y y' hy hy' => rw [TensorProduct.add_tmul]; exact hadd _ _ hy hy'
  | add x x' hx hx' => exact hadd _ _ hx hx'

/-! ### The actions of the three factors -/

variable (A B C) in
/-- The action of `A` on the triple tensor product, through the first factor. -/
private noncomputable abbrev actionA : MultiplierAction ((A ⊗[ℂ] B) ⊗[ℂ] C) A :=
  ((MultiplierAction.self A).rTensor B).rTensor C

variable (A B C) in
/-- The action of `B` on the triple tensor product, through the second factor. -/
private noncomputable abbrev actionB : MultiplierAction ((A ⊗[ℂ] B) ⊗[ℂ] C) B :=
  ((MultiplierAction.self B).lTensor A).rTensor C

variable (A B C) in
/-- The action of `C` on the triple tensor product, through the third factor. -/
private noncomputable abbrev actionC : MultiplierAction ((A ⊗[ℂ] B) ⊗[ℂ] C) C :=
  (MultiplierAction.self C).lTensor (A ⊗[ℂ] B)

end Triple

/-! ### Algebraic identities of the actions -/

section Identities

open MultiplierAction

private lemma lmul_comm_AB (a : A) (b : B) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (actionA A B C).lmul a ((actionB A B C).lmul b x) =
      (actionB A B C).lmul b ((actionA A B C).lmul a x) := by
  induction x using triple_induction with
  | h a' b' c' => rfl
  | hadd x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

private lemma lmul_comm_AC (a : A) (c : C) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (actionA A B C).lmul a ((actionC A B C).lmul c x) =
      (actionC A B C).lmul c ((actionA A B C).lmul a x) := by
  induction x using triple_induction with
  | h a' b' c' => rfl
  | hadd x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

private lemma lmul_comm_BC (b : B) (c : C) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (actionB A B C).lmul b ((actionC A B C).lmul c x) =
      (actionC A B C).lmul c ((actionB A B C).lmul b x) := by
  induction x using triple_induction with
  | h a' b' c' => rfl
  | hadd x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

private lemma lmul_lmul_lmul (a : A) (b : B) (c : C) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (actionA A B C).lmul a ((actionB A B C).lmul b ((actionC A B C).lmul c x)) =
      ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) * x := by
  induction x using triple_induction with
  | h a' b' c' => simp only [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  | hadd x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    exact (map_add (LinearMap.mul ℂ ((A ⊗[ℂ] B) ⊗[ℂ] C) ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) x y).symm

private lemma rmul_rmul_rmul (a : A) (b : B) (c : C) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (actionC A B C).rmul c ((actionB A B C).rmul b ((actionA A B C).rmul a x)) =
      x * ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) := by
  induction x using triple_induction with
  | h a' b' c' => simp only [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  | hadd x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    exact (map_add ((LinearMap.mul ℂ ((A ⊗[ℂ] B) ⊗[ℂ] C)).flip ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) x y).symm

end Identities

/-! ### The multipliers of the three factors -/

section Multipliers

variable (Ψ : (A ⊗ₘₐₓ B) ⊗[ℂ] C →⋆ₙₐ[ℂ] D)

/-- The multipliers by which `A` acts on the closure of the range of `Ψ`. -/
private noncomputable def multA : A →⋆ₙₐ[ℂ] 𝓜(ℂ, (triple Ψ).closureRange) :=
  (actionA A B C).toMultiplier (triple Ψ)

/-- The multipliers by which `B` acts on the closure of the range of `Ψ`. -/
private noncomputable def multB : B →⋆ₙₐ[ℂ] 𝓜(ℂ, (triple Ψ).closureRange) :=
  (actionB A B C).toMultiplier (triple Ψ)

/-- The multipliers by which `C` acts on the closure of the range of `Ψ`. -/
private noncomputable def multC : C →⋆ₙₐ[ℂ] 𝓜(ℂ, (triple Ψ).closureRange) :=
  (actionC A B C).toMultiplier (triple Ψ)

/-- The multiplier `multA Ψ a` acts on the range of `triple Ψ` by the left action of `a`. -/
private lemma multA_fst (a : A) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (multA Ψ a).fst ((triple Ψ).closureRangeRestrict x) =
      (triple Ψ).closureRangeRestrict ((actionA A B C).lmul a x) :=
  MultiplierAction.toMultiplier_fst _ _ a x

/-- The multiplier `multB Ψ b` acts on the range of `triple Ψ` by the left action of `b`. -/
private lemma multB_fst (b : B) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (multB Ψ b).fst ((triple Ψ).closureRangeRestrict x) =
      (triple Ψ).closureRangeRestrict ((actionB A B C).lmul b x) :=
  MultiplierAction.toMultiplier_fst _ _ b x

/-- The multiplier `multC Ψ c` acts on the range of `triple Ψ` by the left action of `c`. -/
private lemma multC_fst (c : C) (x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (multC Ψ c).fst ((triple Ψ).closureRangeRestrict x) =
      (triple Ψ).closureRangeRestrict ((actionC A B C).lmul c x) :=
  MultiplierAction.toMultiplier_fst _ _ c x

/-- The multipliers of `A` and of `B` commute. -/
private lemma commute_multA_multB (a : A) (b : B) : Commute (multA Ψ a) (multB Ψ b) :=
  MultiplierAction.commute_toMultiplier _ _ _ lmul_comm_AB a b

/-- The multipliers of `A` and of `C` commute. -/
private lemma commute_multA_multC (a : A) (c : C) : Commute (multA Ψ a) (multC Ψ c) :=
  MultiplierAction.commute_toMultiplier _ _ _ lmul_comm_AC a c

/-- The multipliers of `B` and of `C` commute. -/
private lemma commute_multB_multC (b : B) (c : C) : Commute (multB Ψ b) (multC Ψ c) :=
  MultiplierAction.commute_toMultiplier _ _ _ lmul_comm_BC b c

/-- The multipliers by which `B ⊗ₘₐₓ C` acts: the extension of `b ⊗ c ↦ π_B(b) π_C(c)`. -/
private noncomputable def multBC : B ⊗ₘₐₓ C →⋆ₙₐ[ℂ] 𝓜(ℂ, (triple Ψ).closureRange) :=
  lift (NonUnitalStarAlgebra.TensorProduct.productMap (multB Ψ) (multC Ψ) (commute_multB_multC Ψ))

/-- `multBC Ψ` sends `b ⊗ c` to the product of the multipliers of `b` and of `c`. -/
private lemma multBC_of_tmul (b : B) (c : C) :
    multBC Ψ (of B C (b ⊗ₜ[ℂ] c)) = multB Ψ b * multC Ψ c := by
  rw [multBC, lift_of, NonUnitalStarAlgebra.TensorProduct.productMap_tmul]

/-- The multipliers of `A` commute with the image of `B ⊗ₘₐₓ C`. -/
private lemma commute_multA_multBC (a : A) (T : B ⊗ₘₐₓ C) : Commute (multA Ψ a) (multBC Ψ T) := by
  have hof (y : B ⊗[ℂ] C) : Commute (multA Ψ a) (multBC Ψ (of B C y)) := by
    induction y using TensorProduct.inductionOn with
    | tmul b c =>
      rw [multBC_of_tmul]
      exact (commute_multA_multB Ψ a b).mul_right (commute_multA_multC Ψ a c)
    | add y y' hy hy' => rw [map_add, map_add]; exact hy.add_right hy'
  have hcont : Continuous (multBC Ψ) := map_continuous _
  exact congrFun (denseRange_of.equalizer (continuous_const.mul hcont)
    (hcont.mul continuous_const) (funext fun y => (hof y).eq)) T

/-- The product of `π_A` and the extension of `π_B × π_C`, a `⋆`-homomorphism of
`A ⊗[ℂ] (B ⊗ₘₐₓ C)`. -/
private noncomputable def assocHom : A ⊗[ℂ] (B ⊗ₘₐₓ C) →⋆ₙₐ[ℂ] 𝓜(ℂ, (triple Ψ).closureRange) :=
  NonUnitalStarAlgebra.TensorProduct.productMap (multA Ψ) (multBC Ψ) (commute_multA_multBC Ψ)

/-- `assocHom Ψ` sends the reassociated pure tensor `a ⊗ (b ⊗ c)` to the product of the multipliers
of `a`, `b` and `c`. -/
private lemma assocHom_assoc_tmul (a : A) (b : B) (c : C) :
    assocHom Ψ (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
        (TensorProduct.assoc ℂ A B C ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c))) =
      multA Ψ a * (multB Ψ b * multC Ψ c) := by
  rw [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_apply, assocHom,
    NonUnitalStarAlgebra.TensorProduct.productMap_tmul, LinearMap.coe_ofClass, multBC_of_tmul]

/-- On the image of the triple tensor product, `assocHom Ψ` of the reassociated tensor `t` acts as
the left multiplication by `t`. -/
private lemma assocHom_fst (t x : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    (assocHom Ψ (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
      (TensorProduct.assoc ℂ A B C t))).fst ((triple Ψ).closureRangeRestrict x) =
      (triple Ψ).closureRangeRestrict (t * x) := by
  induction t using triple_induction with
  | h a b c =>
    rw [assocHom_assoc_tmul, DoubleCentralizer.mul_fst, DoubleCentralizer.mul_fst,
      mul_apply_eq_comp, mul_apply_eq_comp, multC_fst, multB_fst, multA_fst, lmul_lmul_lmul]
  | hadd y z hy hz =>
    rw [map_add, map_add, map_add, DoubleCentralizer.add_fst, add_apply, hy, hz, ← map_add]
    congr 1
    exact (map_add ((LinearMap.mul ℂ ((A ⊗[ℂ] B) ⊗[ℂ] C)).flip x) y z).symm

end Multipliers

/-! ### The bound -/

/-- **A `⋆`-homomorphism of `(A ⊗ₘₐₓ B) ⊗[ℂ] C` is bounded by the norm of `A ⊗ₘₐₓ (B ⊗ₘₐₓ C)`** on
the triple algebraic tensor product. The three factors act on the closure of the range of `Ψ` by
commuting multipliers `π_A`, `π_B`, `π_C`; the product of `π_A` with the extension of `π_B × π_C` to
`B ⊗ₘₐₓ C` is a `⋆`-homomorphism of `A ⊗[ℂ] (B ⊗ₘₐₓ C)` that agrees with `Ψ`, and the multiplier
algebra contains the closure of the range of `Ψ` isometrically. -/
theorem norm_apply_le_norm_of_assoc (Ψ : (A ⊗ₘₐₓ B) ⊗[ℂ] C →⋆ₙₐ[ℂ] D)
    (t : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    ‖Ψ (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id t)‖ ≤
      ‖of A (B ⊗ₘₐₓ C) (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
        (TensorProduct.assoc ℂ A B C t))‖ := by
  set w := TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
    (TensorProduct.assoc ℂ A B C t)
  set Ψr := (triple Ψ).closureRangeRestrict
  have hΨ : ‖Ψ (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id t)‖ =
      ‖Ψr t‖ := rfl
  refine (hΨ.trans_le ?_).trans (norm_apply_le_norm_of (assocHom Ψ) w)
  -- `‖Ψ t‖² = ‖Ψ (t t⋆)‖ = ‖(assocHom Ψ w).fst (Ψ t⋆)‖ ≤ ‖assocHom Ψ w‖ ‖Ψ t‖`
  have hsq : ‖Ψr t‖ * ‖Ψr t‖ ≤ ‖assocHom Ψ w‖ * ‖Ψr t‖ := by
    have h := ((assocHom Ψ w).fst).le_opNorm (Ψr (star t))
    rw [assocHom_fst, map_mul, map_star, CStarRing.norm_self_mul_star, norm_star,
      DoubleCentralizer.norm_fst] at h
    exact h
  rcases (norm_nonneg (Ψr t)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_right hsq hpos

/-- **A `⋆`-homomorphism of `A ⊗[ℂ] (B ⊗ₘₐₓ C)` is bounded by the norm of `(A ⊗ₘₐₓ B) ⊗ₘₐₓ C`** on
the triple algebraic tensor product: the mirror image of
`MaxTensorProduct.norm_apply_le_norm_of_assoc`, obtained from it by reversing the order of the
factors with `MaxTensorProduct.comm`. -/
theorem norm_apply_assoc_le_norm_of (Φ : A ⊗[ℂ] (B ⊗ₘₐₓ C) →⋆ₙₐ[ℂ] D)
    (t : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    ‖Φ (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
        (TensorProduct.assoc ℂ A B C t))‖ ≤
      ‖of (A ⊗ₘₐₓ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id t)‖ := by
  let rev : (A ⊗[ℂ] B) ⊗[ℂ] C →ₗ[ℂ] (C ⊗[ℂ] B) ⊗[ℂ] A :=
    ((TensorProduct.assoc ℂ C B A).symm : C ⊗[ℂ] (B ⊗[ℂ] A) →ₗ[ℂ] (C ⊗[ℂ] B) ⊗[ℂ] A) ∘ₗ
      TensorProduct.map LinearMap.id (TensorProduct.comm ℂ A B : A ⊗[ℂ] B →ₗ[ℂ] B ⊗[ℂ] A) ∘ₗ
      (TensorProduct.comm ℂ (A ⊗[ℂ] B) C : (A ⊗[ℂ] B) ⊗[ℂ] C →ₗ[ℂ] C ⊗[ℂ] (A ⊗[ℂ] B))
  let Ψ : (C ⊗ₘₐₓ B) ⊗[ℂ] A →⋆ₙₐ[ℂ] D :=
    (Φ.comp (NonUnitalStarAlgebra.TensorProduct.map (NonUnitalStarAlgHom.id ℂ A)
      (comm C B).toNonUnitalStarAlgHom)).comp
      (NonUnitalStarAlgebra.TensorProduct.comm (R := ℂ) (A₁ := C ⊗ₘₐₓ B)
        (B₁ := A)).toNonUnitalStarAlgHom
  let G : (A ⊗ₘₐₓ B) ⊗ₘₐₓ C →⋆ₙₐ[ℂ] C ⊗ₘₐₓ (B ⊗ₘₐₓ A) :=
    (map (NonUnitalStarAlgHom.id ℂ C) (comm A B).toNonUnitalStarAlgHom).comp
      (comm (A ⊗ₘₐₓ B) C).toNonUnitalStarAlgHom
  have hL : Ψ (TensorProduct.map (of C B : C ⊗[ℂ] B →ₗ[ℂ] C ⊗ₘₐₓ B) LinearMap.id (rev t)) =
      Φ (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
        (TensorProduct.assoc ℂ A B C t)) := by
    refine LinearMap.congr_fun (f := (Ψ : (C ⊗ₘₐₓ B) ⊗[ℂ] A →ₗ[ℂ] D) ∘ₗ
      TensorProduct.map (of C B : C ⊗[ℂ] B →ₗ[ℂ] C ⊗ₘₐₓ B) LinearMap.id ∘ₗ rev)
      (g := (Φ : A ⊗[ℂ] (B ⊗ₘₐₓ C) →ₗ[ℂ] D) ∘ₗ
        TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C) ∘ₗ
        (TensorProduct.assoc ℂ A B C : (A ⊗[ℂ] B) ⊗[ℂ] C →ₗ[ℂ] A ⊗[ℂ] (B ⊗[ℂ] C))) ?_ t
    refine TensorProduct.ext_threefold fun a b c => ?_
    simp [rev, Ψ]
  have hR : G (of (A ⊗ₘₐₓ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B)
      LinearMap.id t)) = of C (B ⊗ₘₐₓ A) (TensorProduct.map LinearMap.id
        (of B A : B ⊗[ℂ] A →ₗ[ℂ] B ⊗ₘₐₓ A) (TensorProduct.assoc ℂ C B A (rev t))) := by
    refine LinearMap.congr_fun (f := (G : (A ⊗ₘₐₓ B) ⊗ₘₐₓ C →ₗ[ℂ] C ⊗ₘₐₓ (B ⊗ₘₐₓ A)) ∘ₗ
      (of (A ⊗ₘₐₓ B) C : (A ⊗ₘₐₓ B) ⊗[ℂ] C →ₗ[ℂ] (A ⊗ₘₐₓ B) ⊗ₘₐₓ C) ∘ₗ
      TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id)
      (g := (of C (B ⊗ₘₐₓ A) : C ⊗[ℂ] (B ⊗ₘₐₓ A) →ₗ[ℂ] C ⊗ₘₐₓ (B ⊗ₘₐₓ A)) ∘ₗ
        TensorProduct.map LinearMap.id (of B A : B ⊗[ℂ] A →ₗ[ℂ] B ⊗ₘₐₓ A) ∘ₗ
        (TensorProduct.assoc ℂ C B A : (C ⊗[ℂ] B) ⊗[ℂ] A →ₗ[ℂ] C ⊗[ℂ] (B ⊗[ℂ] A)) ∘ₗ rev) ?_ t
    refine TensorProduct.ext_threefold fun a b c => ?_
    simp [rev, G]
  calc _ = ‖Ψ (TensorProduct.map (of C B : C ⊗[ℂ] B →ₗ[ℂ] C ⊗ₘₐₓ B) LinearMap.id (rev t))‖ := by
        rw [hL]
    _ ≤ ‖of C (B ⊗ₘₐₓ A) (TensorProduct.map LinearMap.id (of B A : B ⊗[ℂ] A →ₗ[ℂ] B ⊗ₘₐₓ A)
          (TensorProduct.assoc ℂ C B A (rev t)))‖ := norm_apply_le_norm_of_assoc Ψ (rev t)
    _ = ‖G (of (A ⊗ₘₐₓ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B)
          LinearMap.id t))‖ := by rw [hR]
    _ ≤ _ := NonUnitalStarAlgHom.norm_apply_le G _

/-- **The maximal norm is associative**: on the triple algebraic tensor product, the norm of
`(A ⊗ₘₐₓ B) ⊗ₘₐₓ C` is that of `A ⊗ₘₐₓ (B ⊗ₘₐₓ C)`. -/
theorem norm_of_assoc (t : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    ‖of (A ⊗ₘₐₓ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id t)‖ =
      ‖of A (B ⊗ₘₐₓ C) (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
        (TensorProduct.assoc ℂ A B C t))‖ :=
  le_antisymm (norm_apply_le_norm_of_assoc _ t) (norm_apply_assoc_le_norm_of _ t)

/-! ### The associativity isomorphism -/

/-- The triple algebraic tensor product is dense in `(A ⊗ₘₐₓ B) ⊗ₘₐₓ C`. -/
lemma denseRange_of_map_of_id : DenseRange fun t : (A ⊗[ℂ] B) ⊗[ℂ] C =>
    of (A ⊗ₘₐₓ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id t) :=
  NonUnitalStarAlgHom.denseRange_comp_map (of (A ⊗ₘₐₓ B) C) denseRange_of denseRange_of denseRange_id

/-- The triple algebraic tensor product is dense in `A ⊗ₘₐₓ (B ⊗ₘₐₓ C)`, through
`(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)`. -/
lemma denseRange_of_map_id_of_assoc : DenseRange fun t : (A ⊗[ℂ] B) ⊗[ℂ] C =>
    of A (B ⊗ₘₐₓ C) (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
      (TensorProduct.assoc ℂ A B C t)) := by
  have h := NonUnitalStarAlgHom.denseRange_comp_map (of A (B ⊗ₘₐₓ C)) denseRange_of
    (f := LinearMap.id) denseRange_id (g := (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)) denseRange_of
  unfold DenseRange at h ⊢
  rwa [← (TensorProduct.assoc ℂ A B C).surjective.range_comp] at h

variable (A B C) in
/-- **The associativity of the maximal tensor product**:
`(A ⊗ₘₐₓ B) ⊗ₘₐₓ C ≃⋆ₐ[ℂ] A ⊗ₘₐₓ (B ⊗ₘₐₓ C)`, by the isomorphism that is
`(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)` on the triple algebraic tensor product (`MaxTensorProduct.assoc_of`). -/
noncomputable def assoc : (A ⊗ₘₐₓ B) ⊗ₘₐₓ C ≃⋆ₐ[ℂ] A ⊗ₘₐₓ (B ⊗ₘₐₓ C) := by
  refine NonUnitalStarAlgHom.equivOfDenseRange
    (φ := (of (A ⊗ₘₐₓ B) C).comp
      (NonUnitalStarAlgebra.TensorProduct.map (of A B) (NonUnitalStarAlgHom.id ℂ C)))
    (ψ := ((of A (B ⊗ₘₐₓ C)).comp
      (NonUnitalStarAlgebra.TensorProduct.map (NonUnitalStarAlgHom.id ℂ A) (of B C))).comp
      NonUnitalStarAlgebra.TensorProduct.assoc.toNonUnitalStarAlgHom)
    ?_ ?_ ?_
  · exact denseRange_of_map_of_id
  · exact denseRange_of_map_id_of_assoc
  · exact norm_of_assoc

/-- `MaxTensorProduct.assoc A B C` is `(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)` on the triple algebraic tensor
product. -/
lemma assoc_of (t : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    assoc A B C (of (A ⊗ₘₐₓ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id t)) =
      of A (B ⊗ₘₐₓ C) (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
        (TensorProduct.assoc ℂ A B C t)) :=
  NonUnitalStarAlgHom.equivOfDenseRange_apply _ _ _ t

/-- `MaxTensorProduct.assoc A B C` sends `(a ⊗ b) ⊗ c` to `a ⊗ (b ⊗ c)`. -/
@[simp] lemma assoc_of_tmul (a : A) (b : B) (c : C) :
    assoc A B C (of (A ⊗ₘₐₓ B) C (of A B (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      of A (B ⊗ₘₐₓ C) (a ⊗ₜ[ℂ] of B C (b ⊗ₜ[ℂ] c)) :=
  assoc_of ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)

end MaxTensorProduct
