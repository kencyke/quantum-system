/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSpace.Paulsen
public import QuantumSystem.Analysis.OperatorSystem.Arveson
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.PiLp

/-!
# Wittstock's extension theorem and the factorization of completely bounded maps

A completely bounded map `φ : E → B(H)` on a subspace `E` of a unital C⋆-algebra `A` extends to a
completely bounded map `A → B(H)` with the same cb norm (`CompletelyBoundedMap.exists_extension`), and
factors as `φ(x) = V₁† π(x) V₂` through a unital ⋆-homomorphism `π : A → B(K)` with
`‖V₁‖ ‖V₂‖ = ‖φ‖_cb` (`CompletelyBoundedMap.exists_factorization`).

Normalize `‖φ‖_cb = 1`. The map `!![λ 1, x; y⋆, μ 1] ↦ !![λ 1, φ x; (φ y)⋆, μ 1]` on the Paulsen system
of `E` is then completely positive (`Submodule.paulsenCompletelyPositiveMap`), so Arveson's extension
theorem extends it to a unital completely positive map `Ψ : M₂(A) → B(H ⊕ H)`. The extension of `φ` is
the corner `a ↦ (Ψ !![0, a; 0, 0])₀₁`, a composite of completely bounded maps of cb norm at most `1`.
A Stinespring dilation `Ψ = W† σ W` of `Ψ` gives the factorization: `!![0, x; 0, 0] = diag(x, x) E₀₁`,
so `φ(x) = (W ι₀)† σ(diag(x, x)) σ(E₀₁) W ι₁`.

## Main results

* `CompletelyBoundedMap.exists_extension` — **Wittstock's extension theorem**.
* `CompletelyBoundedMap.exists_factorization` — the factorization of completely bounded maps.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open CStarMatrix

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace CompletelyBoundedMap

/-- The inclusion of `H` as the `j`-th summand of `H ⊕ H = PiLp 2 (fun _ : Fin 2 ↦ H)`. -/
private abbrev ι (j : Fin 2) : H →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) :=
  (LinearIsometry.piLpSingle 2 ℂ (fun _ : Fin 2 => H) j).toContinuousLinearMap

private lemma ι_apply (j : Fin 2) (ξ : H) : ι j ξ = PiLp.single 2 j ξ :=
  rfl

private lemma norm_ι_le (j : Fin 2) : ‖ι (H := H) j‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

variable [CompleteSpace H] {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {E : Submodule ℂ A}

/-- The corner embedding `a ↦ !![0, a; 0, 0]` of `A` into `M₂(A)` is completely bounded with cb norm
at most `1`: after exchanging the outer and inner indices, `X.map corner` is `!![0, X; 0, 0]`. -/
def cornerCB : A →CB CStarMatrix (Fin 2) (Fin 2) A where
  toLinearMap :=
    { toFun := fun a => ofMatrix !![0, a; 0, 0]
      map_add' := fun a b => by
        refine CStarMatrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp [ofMatrix_apply]
      map_smul' := fun c a => by
        refine CStarMatrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j <;> simp [ofMatrix_apply] }
  exists_bound' := ⟨1, fun k X => by
    rw [one_mul, ← NonUnitalStarAlgHom.norm_map (transposeBlocksStarAlgEquiv k 2 A)
      (transposeBlocksStarAlgEquiv k 2 A).injective, transposeBlocksStarAlgEquiv_apply]
    refine le_of_eq_of_le (congrArg norm ?_) (norm_ofMatrix_zero_one_le X)
    refine CStarMatrix.ext fun i j => CStarMatrix.ext fun a b => ?_
    fin_cases i <;> fin_cases j <;> rfl⟩

/-- `cornerCB a` is `!![0, a; 0, 0]`. -/
lemma cornerCB_apply (a : A) : cornerCB a = ofMatrix !![0, a; 0, 0] :=
  rfl

/-- The corner embedding has cb norm at most `1`. -/
lemma norm_cornerCB_le : ‖(cornerCB : A →CB CStarMatrix (Fin 2) (Fin 2) A)‖ ≤ 1 :=
  norm_le_bound _ zero_le_one fun k X => by
    rw [one_mul, ← NonUnitalStarAlgHom.norm_map (transposeBlocksStarAlgEquiv k 2 A)
      (transposeBlocksStarAlgEquiv k 2 A).injective, transposeBlocksStarAlgEquiv_apply]
    refine le_of_eq_of_le (congrArg norm ?_) (norm_ofMatrix_zero_one_le X)
    refine CStarMatrix.ext fun i j => CStarMatrix.ext fun a b => ?_
    fin_cases i <;> fin_cases j <;> rfl

/-- The unital completely positive extension to `M₂(A)` of the map induced by a complete
contraction `φ` on the Paulsen system: Arveson's extension theorem applied to
`Submodule.paulsenCompletelyPositiveMap`, transported to `B(H ⊕ H)`. -/
private lemma exists_completelyPositiveMap_paulsen [Nontrivial A] (φ : E →CB (H →L[ℂ] H))
    (hφ : ‖φ‖ ≤ 1) :
    ∃ Ψ : CStarMatrix (Fin 2) (Fin 2) A →CP (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
        PiLp 2 (fun _ : Fin 2 => H)), Ψ 1 = 1 ∧
      ∀ (x : E) (ξ η : H), ⟪ι (H := H) 0 η, Ψ (cornerCB (x : A)) (ι (H := H) 1 ξ)⟫_ℂ =
        ⟪η, φ x ξ⟫_ℂ := by
  let e := toPiLpStarAlgEquiv (n := Fin 2) (H := H)
  let eCP : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) →CP' (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
      PiLp 2 (fun _ : Fin 2 => H)) :=
    CompletelyPositiveMapClass'.toCompletelyPositiveMap' e
  let Φ := eCP.comp (E.paulsenCompletelyPositiveMap φ hφ)
  obtain ⟨Ψ, hΨ⟩ := CompletelyPositiveMap.exists_extension_of_operatorSubsystem Φ
  have hcorner : ∀ x : E, cornerCB (x : A) ∈ E.paulsenSystem := fun x =>
    ⟨zero_mem _, x.2, by rw [show (cornerCB (x : A)) 1 0 = 0 from rfl, star_zero]; exact zero_mem _,
      zero_mem _⟩
  refine ⟨Ψ, ?_, fun x ξ η => ?_⟩
  · have h := hΨ 1
    change Ψ 1 = e (Submodule.paulsenMap φ.toLinearMap 1) at h
    rw [h]
    have : Submodule.paulsenMap φ.toLinearMap (1 : E.paulsenSystem) = 1 := by
      have h₁ : Submodule.coeffOne (A := A) ⟨1, Submodule.mem_span_singleton_self 1⟩ = 1 := by
        rw [Submodule.coeffOne, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq,
          LinearEquiv.toSpanNonzeroSingleton_one]
      refine CStarMatrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · change Submodule.coeffOne (A := A) ⟨1, _⟩ • (1 : H →L[ℂ] H) = 1
        rw [h₁, one_smul]
      · change φ ⟨0, _⟩ = 0
        exact map_zero φ
      · change star (φ ⟨star ((1 : CStarMatrix (Fin 2) (Fin 2) A) 1 0), _⟩) = 0
        rw [star_eq_zero]
        convert map_zero φ
        exact star_zero A
      · change Submodule.coeffOne (A := A) ⟨1, _⟩ • (1 : H →L[ℂ] H) = 1
        rw [h₁, one_smul]
    rw [this, map_one]
  · have h := hΨ ⟨cornerCB (x : A), hcorner x⟩
    change Ψ (cornerCB (x : A)) = e (Submodule.paulsenMap φ.toLinearMap ⟨_, hcorner x⟩) at h
    rw [h, ι_apply, ι_apply, PiLp.inner_single_left, toPiLpStarAlgEquiv_apply, Fin.sum_univ_two,
      PiLp.ofLp_single]
    simp only [Pi.single_apply, Fin.isValue, zero_ne_one, ↓reduceIte, map_zero, zero_add]
    rfl

/-- The corner `a ↦ ι₀† Ψ(!![0, a; 0, 0]) ι₁` of a completely positive map `Ψ` on `M₂(A)`, as a
completely bounded map of cb norm at most `‖Ψ 1‖`. -/
private def cornerOf
    (Ψ : CStarMatrix (Fin 2) (Fin 2) A →CP (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
      PiLp 2 (fun _ : Fin 2 => H))) : A →CB (H →L[ℂ] H) :=
  (ContinuousLinearMap.compressionCB (ι (H := H) 0) (ι (H := H) 1)).comp
    (Ψ.toCompletelyBoundedMap.comp cornerCB)

private lemma norm_cornerOf_le
    (Ψ : CStarMatrix (Fin 2) (Fin 2) A →CP (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
      PiLp 2 (fun _ : Fin 2 => H))) : ‖cornerOf Ψ‖ ≤ ‖Ψ 1‖ := by
  let c := ContinuousLinearMap.compressionCB (ι (H := H) 0) (ι (H := H) 1)
  let Ψc : A →CB (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H)) :=
    Ψ.toCompletelyBoundedMap.comp cornerCB
  have h₁ : ‖c‖ ≤ 1 := by
    have hc := ContinuousLinearMap.norm_compressionCB_le (ι (H := H) 0)
      (ι (H := H) 1)
    have h0 := norm_ι_le (H := H) 0
    have h1 := norm_ι_le (H := H) 1
    have h1' := (ι (H := H) 1).opNorm_nonneg
    have h0' := (ι (H := H) 0).opNorm_nonneg
    refine hc.trans ?_
    nlinarith
  have h₂ : ‖Ψc‖ ≤ ‖Ψ 1‖ := by
    refine (norm_comp_le Ψ.toCompletelyBoundedMap cornerCB).trans ?_
    rw [CompletelyPositiveMap.norm_toCompletelyBoundedMap]
    exact mul_le_of_le_one_right (norm_nonneg _) norm_cornerCB_le
  have h₃ : ‖c.comp Ψc‖ ≤ ‖c‖ * ‖Ψc‖ := norm_comp_le c Ψc
  calc ‖cornerOf Ψ‖ = ‖c.comp Ψc‖ := rfl
    _ ≤ ‖c‖ * ‖Ψc‖ := h₃
    _ ≤ 1 * ‖Ψ 1‖ := mul_le_mul h₁ h₂ Ψc.norm_nonneg' zero_le_one
    _ = ‖Ψ 1‖ := one_mul _

/-- **Wittstock's extension theorem.** A completely bounded map `φ : E → B(H)` on a subspace `E` of a
unital C⋆-algebra `A` extends to a completely bounded map `ψ : A → B(H)` with the same cb norm. -/
theorem exists_extension (φ : E →CB (H →L[ℂ] H)) :
    ∃ ψ : A →CB (H →L[ℂ] H), ψ.restrict E = φ ∧ ‖ψ‖ = ‖φ‖ := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · exact ⟨0, ext fun _ => rfl, by rw [norm_zero', norm_zero']⟩
  have hA : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hφ (ext fun x => by
      rw [show x = 0 from Subtype.ext (Subsingleton.elim _ _), map_zero, map_zero])
  have hr : 0 < ‖φ‖ := norm_pos' hφ
  set r := ‖φ‖
  set φ' : E →CB (H →L[ℂ] H) := (r⁻¹ : ℂ) • φ
  have hφ' : ‖φ'‖ ≤ 1 := by
    rw [norm_smul', norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ hr.ne']
  obtain ⟨Ψ, hΨ1, hΨ⟩ := exists_completelyPositiveMap_paulsen φ' hφ'
  have hres : ((r : ℂ) • cornerOf Ψ).restrict E = φ := ext fun x => by
    change (r : ℂ) • cornerOf Ψ x = φ x
    have hx : cornerOf Ψ (x : A) = φ' x := ContinuousLinearMap.ext fun ξ =>
      ext_inner_left ℂ fun η => by
        change ⟪η, ContinuousLinearMap.adjoint (ι (H := H) 0) (Ψ (cornerCB (x : A))
          (ι (H := H) 1 ξ))⟫_ℂ = _
        rw [ContinuousLinearMap.adjoint_inner_right, hΨ]
    rw [hx, show φ' x = (r⁻¹ : ℂ) • φ x from rfl, smul_smul, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  refine ⟨(r : ℂ) • cornerOf Ψ, hres, le_antisymm ?_ ?_⟩
  · rw [norm_smul', Complex.norm_real, Real.norm_of_nonneg hr.le]
    refine mul_le_of_le_one_right hr.le ((norm_cornerOf_le Ψ).trans ?_)
    rw [hΨ1]
    exact ContinuousLinearMap.norm_id_le
  · have h := norm_restrict_le ((r : ℂ) • cornerOf Ψ) E
    rwa [hres] at h

/-- **Factorization of completely bounded maps.** A completely bounded map `φ : E → B(H)` on a
subspace `E` of a unital C⋆-algebra `A` factors as `φ(x) = V₁† π(x) V₂` through a unital
⋆-homomorphism `π : A → B(K)`, with `‖V₁‖ ‖V₂‖ = ‖φ‖_cb`. -/
theorem exists_factorization (φ : E →CB (H →L[ℂ] H)) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V₁ V₂ : H →L[ℂ] K),
      (∀ x : E, φ x = ContinuousLinearMap.adjoint V₁ ∘L π x ∘L V₂) ∧ ‖V₁‖ * ‖V₂‖ = ‖φ‖ := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · let ψ₀ : A →CP (H →L[ℂ] H) :=
      ⟨0, fun _ M _ => le_of_eq (CStarMatrix.ext fun _ _ => rfl).symm⟩
    obtain ⟨K, _, _, _, π, -, -⟩ := CompletelyPositiveMap.exists_unital_stinespring_dilation ψ₀
    exact ⟨K, _, _, _, π, 0, 0, fun x => by ext; simp, by rw [norm_zero', norm_zero, zero_mul]⟩
  have hA : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hφ (ext fun x => by
      rw [show x = 0 from Subtype.ext (Subsingleton.elim _ _), map_zero, map_zero])
  have hr : 0 < ‖φ‖ := norm_pos' hφ
  set r := ‖φ‖
  set φ' : E →CB (H →L[ℂ] H) := (r⁻¹ : ℂ) • φ
  have hφ' : ‖φ'‖ ≤ 1 := by
    rw [norm_smul', norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ hr.ne']
  obtain ⟨Ψ, hΨ1, hΨ⟩ := exists_completelyPositiveMap_paulsen φ' hφ'
  obtain ⟨K, _, _, _, σ, W, hσ, hW, -⟩ := CompletelyPositiveMap.exists_unital_stinespring_dilation Ψ
  let π : A →⋆ₐ[ℂ] (K →L[ℂ] K) := σ.comp (diagonalStarAlgHom (n := Fin 2))
  let E₀₁ : CStarMatrix (Fin 2) (Fin 2) A := ofMatrix !![0, 1; 0, 0]
  have hcorner : ∀ a : A, cornerCB a = diagonalStarAlgHom (n := Fin 2) a * E₀₁ := fun a => by
    refine CStarMatrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [cornerCB_apply, E₀₁, diagonalStarAlgHom_apply, CStarMatrix.mul_apply, ofMatrix_apply,
        Matrix.diagonal_apply]
  let V₁ : H →L[ℂ] K := W ∘L ι (H := H) 0
  let V₂ : H →L[ℂ] K := (r : ℂ) • (σ E₀₁ ∘L W ∘L ι (H := H) 1)
  have hfac : ∀ x : E, φ x = ContinuousLinearMap.adjoint V₁ ∘L π x ∘L V₂ := fun x =>
    ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun η => by
      have h := hΨ x ξ η
      rw [hσ, hcorner, map_mul] at h
      have hφx : φ x = (r : ℂ) • φ' x := by
        rw [show φ' x = (r⁻¹ : ℂ) • φ x from rfl, smul_smul, ← Complex.ofReal_inv,
          ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
      rw [hφx, _root_.smul_apply, inner_smul_right, ← h]
      simp only [V₁, V₂, π, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        _root_.smul_apply, map_smul, inner_smul_right, StarAlgHom.comp_apply, mul_apply_eq_comp]
  have hWn : ‖W‖ ≤ 1 := by
    have h := ContinuousLinearMap.norm_adjoint_comp_self W
    rw [hW, hΨ1] at h
    have h1 : ‖(1 : PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => H))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    nlinarith [W.opNorm_nonneg]
  have hE₀₁ : ‖E₀₁‖ ≤ 1 := (norm_ofMatrix_zero_one_le (1 : A)).trans_eq norm_one
  have hV₁ : ‖V₁‖ ≤ 1 := (W.opNorm_comp_le _).trans
    (by nlinarith [norm_ι_le (H := H) 0, W.opNorm_nonneg,
      (ι (H := H) 0).opNorm_nonneg])
  have hV₂ : ‖V₂‖ ≤ r := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    refine mul_le_of_le_one_right hr.le ?_
    have hσn : ‖σ E₀₁‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le σ E₀₁).trans hE₀₁
    calc ‖σ E₀₁ ∘L W ∘L ι (H := H) 1‖ ≤ ‖σ E₀₁‖ * (‖W‖ * ‖ι (H := H) 1‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (1 * 1) := by
          gcongr
          exact norm_ι_le 1
      _ = 1 := by ring
  refine ⟨K, inferInstance, inferInstance, inferInstance, π, V₁, V₂, hfac, le_antisymm ?_ ?_⟩
  · calc ‖V₁‖ * ‖V₂‖ ≤ 1 * r := mul_le_mul hV₁ hV₂ (norm_nonneg _) zero_le_one
      _ = r := one_mul r
  · have hφeq : φ = (ContinuousLinearMap.compressionCB V₁ V₂).comp
        (π.toNonUnitalStarAlgHom.toCompletelyBoundedMap.comp E.subtypeCB) :=
      ext fun x => hfac x
    have h₁ := norm_comp_le (ContinuousLinearMap.compressionCB V₁ V₂)
      (π.toNonUnitalStarAlgHom.toCompletelyBoundedMap.comp E.subtypeCB)
    have h₂ := norm_comp_le π.toNonUnitalStarAlgHom.toCompletelyBoundedMap E.subtypeCB
    have h₃ := NonUnitalStarAlgHom.norm_toCompletelyBoundedMap_le π.toNonUnitalStarAlgHom
    have h₄ := E.norm_subtypeCB_le
    have h₅ := ContinuousLinearMap.norm_compressionCB_le V₁ V₂
    have h₆ := (π.toNonUnitalStarAlgHom.toCompletelyBoundedMap.comp E.subtypeCB).norm_nonneg'
    have h₇ := π.toNonUnitalStarAlgHom.toCompletelyBoundedMap.norm_nonneg'
    have h₈ := (ContinuousLinearMap.compressionCB V₁ V₂).norm_nonneg'
    have h₉ : ‖π.toNonUnitalStarAlgHom.toCompletelyBoundedMap.comp E.subtypeCB‖ ≤ 1 :=
      h₂.trans ((mul_le_mul h₃ h₄ E.subtypeCB.norm_nonneg' zero_le_one).trans_eq (one_mul 1))
    change ‖φ‖ ≤ ‖V₁‖ * ‖V₂‖
    rw [hφeq]
    exact h₁.trans ((mul_le_of_le_one_right h₈ h₉).trans h₅)

end CompletelyBoundedMap
