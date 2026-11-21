/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.CStarNorm
public import QuantumSystem.ForMathlib.Algebra.Star.TensorProductMap

/-!
# Associativity of the minimal tensor product

On the triple algebraic tensor product, the norms of `(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C` and of
`A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C)` agree (`MinTensorProduct.norm_of_assoc`), so the two algebras are
`⋆`-isomorphic by `(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)` (`MinTensorProduct.assoc`), the triple algebraic
tensor product being dense in both. Both are computed in faithful
representations: the tensor product of the Gelfand–Naimark representations of `A` and `B` is a
faithful representation of `A ⊗ₘᵢₙ B` (`CStarRep.tensorProduct_π_injective`), and the norm of a
minimal tensor product does not depend on the faithful representations
(`MinTensorProduct.norm_of_eq_norm_spatial`). The two resulting operators act on
`Completion (Completion (H_A ⊗ H_B) ⊗ H_C)` and on `Completion (H_A ⊗ Completion (H_B ⊗ H_C))`,
both identified with the completion of the triple Hilbert space tensor product, where the
associativity of the algebraic tensor product intertwines them.

## Main definitions

* `MinTensorProduct.assoc A B C` — `(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C ≃⋆ₐ[ℂ] A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C)`.

## Main results

* `MinTensorProduct.norm_of_assoc` — the associativity of the minimal norm.
-/

@[expose] public section

open scoped TensorProduct MinTensorProduct

open UniformSpace

namespace MinTensorProduct

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-! ### Operators on the triple Hilbert space tensor product -/

section Hilbert

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]

private lemma mapL_completion_left (T : E →L[ℂ] E) (S : F →L[ℂ] F) (q : E ⊗[ℂ] F) :
    TensorProduct.mapL T.completion S
        (TensorProduct.mapIsometry (Completion.toComplₗᵢ : E →ₗᵢ[ℂ] Completion E)
          (LinearIsometry.id : F →ₗᵢ[ℂ] F) q) =
      TensorProduct.mapIsometry (Completion.toComplₗᵢ : E →ₗᵢ[ℂ] Completion E)
        (LinearIsometry.id : F →ₗᵢ[ℂ] F) (TensorProduct.mapL T S q) := by
  induction q using TensorProduct.inductionOn with
  | tmul x y => simp [Completion.coe_toComplₗᵢ, ContinuousLinearMap.completion_apply_coe]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

private lemma mapL_completion_right (T : E →L[ℂ] E) (S : F →L[ℂ] F) (q : E ⊗[ℂ] F) :
    TensorProduct.mapL T S.completion
        (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E)
          (Completion.toComplₗᵢ : F →ₗᵢ[ℂ] Completion F) q) =
      TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E)
        (Completion.toComplₗᵢ : F →ₗᵢ[ℂ] Completion F) (TensorProduct.mapL T S q) := by
  induction q using TensorProduct.inductionOn with
  | tmul x y => simp [Completion.coe_toComplₗᵢ, ContinuousLinearMap.completion_apply_coe]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

private lemma assoc_mapL (T₁ : E →L[ℂ] E) (T₂ : F →L[ℂ] F) (T₃ : G →L[ℂ] G)
    (q : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    TensorProduct.assoc ℂ E F G (TensorProduct.mapL (TensorProduct.mapL T₁ T₂) T₃ q) =
      TensorProduct.mapL T₁ (TensorProduct.mapL T₂ T₃) (TensorProduct.assoc ℂ E F G q) := by
  induction q using TensorProduct.inductionOn with
  | tmul y z =>
    induction y using TensorProduct.inductionOn with
    | tmul x y => simp
    | add p p' hp hp' => simp only [TensorProduct.add_tmul, map_add, hp, hp']
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

private lemma intertwine_of_tmul {M₁ M₂ M₃ N₁ N₂ P : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂] [AddCommGroup P] [Module ℂ P] {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {F₁ F₂ : Type*} [FunLike F₁ N₁ (V →L[ℂ] V)] [LinearMapClass F₁ ℂ N₁ (V →L[ℂ] V)]
    [FunLike F₂ N₂ (W →L[ℂ] W)] [LinearMapClass F₂ ℂ N₂ (W →L[ℂ] W)]
    (U : V ≃ₗᵢ[ℂ] W) (φ : F₁) (ψ : F₂) (f : (M₁ ⊗[ℂ] M₂) ⊗[ℂ] M₃ →ₗ[ℂ] N₁) (g : P →ₗ[ℂ] N₂)
    (e : (M₁ ⊗[ℂ] M₂) ⊗[ℂ] M₃ ≃ₗ[ℂ] P)
    (h : ∀ a b c v, U (φ (f ((a ⊗ₜ b) ⊗ₜ c)) v) = ψ (g (e ((a ⊗ₜ b) ⊗ₜ c))) (U v))
    (t : (M₁ ⊗[ℂ] M₂) ⊗[ℂ] M₃) (v : V) : U (φ (f t) v) = ψ (g (e t)) (U v) := by
  induction t using TensorProduct.inductionOn with
  | tmul x c =>
    induction x using TensorProduct.inductionOn with
    | tmul a b => exact h a b c v
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, add_apply, hx, hx']
  | add t t' ht ht' => simp only [map_add, add_apply, ht, ht']

end Hilbert

section Vectors

variable (RA : CStarRep A) (RB : CStarRep B) (RC : CStarRep C)

variable {RA RB RC} in
/-- The identification of the Hilbert spaces of `(π_A ⊗ π_B) ⊗ π_C` and of `π_A ⊗ (π_B ⊗ π_C)`
through the completion of the triple Hilbert space tensor product. -/
noncomputable def assocUnitary (RA : CStarRep A) (RB : CStarRep B) (RC : CStarRep C) :
    Completion (Completion (RA.H ⊗[ℂ] RB.H) ⊗[ℂ] RC.H) ≃ₗᵢ[ℂ]
      Completion (RA.H ⊗[ℂ] Completion (RB.H ⊗[ℂ] RC.H)) :=
  (TensorProduct.completionLeftEquiv ℂ (RA.H ⊗[ℂ] RB.H) RC.H).symm.trans
    ((TensorProduct.assocIsometry ℂ RA.H RB.H RC.H).completion.trans
      (TensorProduct.completionRightEquiv ℂ RA.H (RB.H ⊗[ℂ] RC.H)))

private lemma assocUnitary_completionLeftEquiv (s : (RA.H ⊗[ℂ] RB.H) ⊗[ℂ] RC.H) :
    assocUnitary RA RB RC (TensorProduct.completionLeftEquiv ℂ (RA.H ⊗[ℂ] RB.H) RC.H s) =
      ↑(TensorProduct.mapIsometry (LinearIsometry.id : RA.H →ₗᵢ[ℂ] RA.H)
        (Completion.toComplₗᵢ : RB.H ⊗[ℂ] RC.H →ₗᵢ[ℂ] Completion (RB.H ⊗[ℂ] RC.H))
          (TensorProduct.assoc ℂ RA.H RB.H RC.H s)) := by
  rw [assocUnitary, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.completion_apply_coe,
    TensorProduct.assocIsometry_apply]
  exact LinearIsometry.completionEquivOfDenseRange_coe _ _ _

private lemma completionLeftEquiv_coe (s : (RA.H ⊗[ℂ] RB.H) ⊗[ℂ] RC.H) :
    TensorProduct.completionLeftEquiv ℂ (RA.H ⊗[ℂ] RB.H) RC.H s =
      ↑(TensorProduct.mapIsometry
        (Completion.toComplₗᵢ : RA.H ⊗[ℂ] RB.H →ₗᵢ[ℂ] Completion (RA.H ⊗[ℂ] RB.H))
        (LinearIsometry.id : RC.H →ₗᵢ[ℂ] RC.H) s) :=
  LinearIsometry.completionEquivOfDenseRange_coe _ _ _

private lemma assocUnitary_coe (s : (RA.H ⊗[ℂ] RB.H) ⊗[ℂ] RC.H) :
    assocUnitary RA RB RC ↑(TensorProduct.mapIsometry
        (Completion.toComplₗᵢ : RA.H ⊗[ℂ] RB.H →ₗᵢ[ℂ] Completion (RA.H ⊗[ℂ] RB.H))
        (LinearIsometry.id : RC.H →ₗᵢ[ℂ] RC.H) s) =
      ↑(TensorProduct.mapIsometry (LinearIsometry.id : RA.H →ₗᵢ[ℂ] RA.H)
        (Completion.toComplₗᵢ : RB.H ⊗[ℂ] RC.H →ₗᵢ[ℂ] Completion (RB.H ⊗[ℂ] RC.H))
          (TensorProduct.assoc ℂ RA.H RB.H RC.H s)) := by
  rw [← completionLeftEquiv_coe RA RB RC s]
  exact assocUnitary_completionLeftEquiv RA RB RC s

/-- On the image of the algebraic tensor product, `(π_A ⊗ π_B) ⊗ π_C` acts as the operator tensor
product. -/
private lemma left_apply (a : A) (b : B) (c : C) (y : Completion (RA.H ⊗[ℂ] RB.H) ⊗[ℂ] RC.H) :
    (RA.tensorProduct RB).spatial RC
        (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id
          ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) ↑y =
      ↑(TensorProduct.mapL (TensorProduct.mapL (RA.π a) (RB.π b)).completion (RC.π c) y) := by
  change (RA.tensorProduct RB).spatial RC (of A B (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) ↑y = _
  rw [CStarRep.spatial_tmul, CStarRep.tensorProduct_π_of, CStarRep.spatial_tmul,
    ContinuousLinearMap.completion_apply_coe]

/-- On the image of the algebraic tensor product, `π_A ⊗ (π_B ⊗ π_C)` acts as the operator tensor
product. -/
private lemma right_apply (a : A) (b : B) (c : C) (y : RA.H ⊗[ℂ] Completion (RB.H ⊗[ℂ] RC.H)) :
    RA.spatial (RB.tensorProduct RC)
        (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C)
          (TensorProduct.assoc ℂ A B C ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c))) ↑y =
      ↑(TensorProduct.mapL (RA.π a) (TensorProduct.mapL (RB.π b) (RC.π c)).completion y) := by
  change RA.spatial (RB.tensorProduct RC) (a ⊗ₜ[ℂ] of B C (b ⊗ₜ[ℂ] c)) ↑y = _
  rw [CStarRep.spatial_tmul, CStarRep.tensorProduct_π_of, CStarRep.spatial_tmul,
    ContinuousLinearMap.completion_apply_coe]

/-- `assocUnitary` intertwines `(π_A ⊗ π_B) ⊗ π_C` with `π_A ⊗ (π_B ⊗ π_C)` on a pure tensor. -/
private lemma assocUnitary_intertwine_tmul (a : A) (b : B) (c : C)
    (v : Completion (Completion (RA.H ⊗[ℂ] RB.H) ⊗[ℂ] RC.H)) :
    assocUnitary RA RB RC ((RA.tensorProduct RB).spatial RC
        (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id
          ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) v) =
      RA.spatial (RB.tensorProduct RC)
        (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C)
          (TensorProduct.assoc ℂ A B C ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c))) (assocUnitary RA RB RC v) := by
  obtain ⟨m, rfl⟩ := (TensorProduct.completionLeftEquiv ℂ (RA.H ⊗[ℂ] RB.H) RC.H).surjective v
  induction m using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih s =>
    rw [completionLeftEquiv_coe, left_apply, mapL_completion_left]
    refine (assocUnitary_coe RA RB RC _).trans ?_
    refine Eq.trans ?_ (congrArg _ (assocUnitary_coe RA RB RC s)).symm
    refine Eq.trans ?_ (right_apply RA RB RC a b c _).symm
    exact congrArg _ ((congrArg _ (assoc_mapL _ _ _ s)).trans (mapL_completion_right _ _ _).symm)

/-- `assocUnitary` intertwines `(π_A ⊗ π_B) ⊗ π_C` with `π_A ⊗ (π_B ⊗ π_C)`. -/
private lemma assocUnitary_intertwine (t : (A ⊗[ℂ] B) ⊗[ℂ] C)
    (v : Completion (Completion (RA.H ⊗[ℂ] RB.H) ⊗[ℂ] RC.H)) :
    assocUnitary RA RB RC ((RA.tensorProduct RB).spatial RC
        (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t) v) =
      RA.spatial (RB.tensorProduct RC)
        (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C)
          (TensorProduct.assoc ℂ A B C t)) (assocUnitary RA RB RC v) := by
  exact intertwine_of_tmul (assocUnitary RA RB RC) ((RA.tensorProduct RB).spatial RC)
    (RA.spatial (RB.tensorProduct RC))
    (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id)
    (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C))
    (TensorProduct.assoc ℂ A B C) (assocUnitary_intertwine_tmul RA RB RC) t v

end Vectors

/-- **The minimal norm is associative**: on the triple algebraic tensor product, the norm of
`(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C` is that of `A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C)`. -/
theorem norm_of_assoc (t : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    ‖of (A ⊗ₘᵢₙ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t)‖ =
      ‖of A (B ⊗ₘᵢₙ C) (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C)
        (TensorProduct.assoc ℂ A B C t))‖ := by
  have hA := CStarRep.gelfandNaimark_injective A
  have hB := CStarRep.gelfandNaimark_injective B
  have hC := CStarRep.gelfandNaimark_injective C
  rw [norm_of_eq_norm_spatial (CStarRep.tensorProduct_π_injective hA hB) hC,
    norm_of_eq_norm_spatial hA (CStarRep.tensorProduct_π_injective hB hC)]
  exact (assocUnitary _ _ _).opNorm_eq_of_intertwine (assocUnitary_intertwine _ _ _ t)

/-! ### The associativity isomorphism -/

/-- The triple algebraic tensor product is dense in `(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C`. -/
lemma denseRange_of_map_of_id : DenseRange fun t : (A ⊗[ℂ] B) ⊗[ℂ] C =>
    of (A ⊗ₘᵢₙ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t) :=
  NonUnitalStarAlgHom.denseRange_comp_map (of (A ⊗ₘᵢₙ B) C) denseRange_of denseRange_of denseRange_id

/-- The triple algebraic tensor product is dense in `A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C)`, through
`(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)`. -/
lemma denseRange_of_map_id_of_assoc : DenseRange fun t : (A ⊗[ℂ] B) ⊗[ℂ] C =>
    of A (B ⊗ₘᵢₙ C) (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C)
      (TensorProduct.assoc ℂ A B C t)) := by
  have h := NonUnitalStarAlgHom.denseRange_comp_map (of A (B ⊗ₘᵢₙ C)) denseRange_of
    (f := LinearMap.id) denseRange_id (g := (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C)) denseRange_of
  unfold DenseRange at h ⊢
  rwa [← (TensorProduct.assoc ℂ A B C).surjective.range_comp] at h

variable (A B C) in
/-- **The associativity of the minimal tensor product**:
`(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C ≃⋆ₐ[ℂ] A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C)`, by the isomorphism that is
`(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)` on the triple algebraic tensor product (`MinTensorProduct.assoc_of`). -/
noncomputable def assoc : (A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C ≃⋆ₐ[ℂ] A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C) := by
  refine NonUnitalStarAlgHom.equivOfDenseRange
    (φ := (of (A ⊗ₘᵢₙ B) C).comp
      (NonUnitalStarAlgebra.TensorProduct.map (of A B) (NonUnitalStarAlgHom.id ℂ C)))
    (ψ := ((of A (B ⊗ₘᵢₙ C)).comp
      (NonUnitalStarAlgebra.TensorProduct.map (NonUnitalStarAlgHom.id ℂ A) (of B C))).comp
      NonUnitalStarAlgebra.TensorProduct.assoc.toNonUnitalStarAlgHom)
    ?_ ?_ ?_
  · exact denseRange_of_map_of_id
  · exact denseRange_of_map_id_of_assoc
  · exact norm_of_assoc

/-- `MinTensorProduct.assoc A B C` is `(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)` on the triple algebraic tensor
product. -/
lemma assoc_of (t : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    assoc A B C (of (A ⊗ₘᵢₙ B) C (TensorProduct.map (of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t)) =
      of A (B ⊗ₘᵢₙ C) (TensorProduct.map LinearMap.id (of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C)
        (TensorProduct.assoc ℂ A B C t)) :=
  NonUnitalStarAlgHom.equivOfDenseRange_apply _ _ _ t

/-- `MinTensorProduct.assoc A B C` sends `(a ⊗ b) ⊗ c` to `a ⊗ (b ⊗ c)`. -/
@[simp] lemma assoc_of_tmul (a : A) (b : B) (c : C) :
    assoc A B C (of (A ⊗ₘᵢₙ B) C (of A B (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      of A (B ⊗ₘᵢₙ C) (a ⊗ₜ[ℂ] of B C (b ⊗ₜ[ℂ] c)) :=
  assoc_of ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)

end MinTensorProduct
