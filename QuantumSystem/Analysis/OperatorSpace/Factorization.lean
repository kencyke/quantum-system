/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSpace.Paulsen
public import QuantumSystem.Analysis.OperatorSpace.Ruan
public import QuantumSystem.Analysis.OperatorSystem.Arveson
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.PiLp

/-!
# The fundamental theorem on completely bounded maps

Let `j : F → A` be a complete isometry of an operator space into a C⋆-algebra, for instance the inclusion
of a subspace (`Submodule.isCompleteIsometry_subtype`). The **Wittstock–Paulsen–Haagerup theorem**
describes the completely bounded maps `φ : F → B(H)`: they are the maps `x ↦ V₁† π(j x) V₂` for a
⋆-homomorphism `π : A → B(K)` and operators `V₁, V₂ : H → K`, and `‖φ‖_cb` is the least value of
`‖V₁‖ ‖V₂‖`, attained with `V₁, V₂` multiples of isometries. Every operator space has such an embedding
into some `B(K')` (`OperatorSpace.exists_isCompleteIsometry`, Ruan's theorem), and the
**Arveson–Wittstock–Hahn–Banach theorem** is the special form in which `x ↦ V₁† π(j x) V₂` is read on the
whole space: a completely bounded map on a subspace `E` of an operator space `F` extends to `F` with the
same cb norm.

For nontrivial unital `A` and `‖φ‖_cb ≤ 1`, the map `!![λ 1, x; y⋆, μ 1] ↦ !![λ 1, φ x; (φ y)⋆, μ 1]` on the Paulsen
system of the range of `j` is completely positive (`Submodule.paulsenCompletelyPositiveMap`), so Arveson's
extension theorem extends it to a unital completely positive map `Ψ : M₂(A) → B(H ⊕ H)`, with a
Stinespring dilation `Ψ = W† σ W`. Since `!![0, a; 0, 0] = diag(a, a) E₀₁`, the corner `(0, 1)` gives
`φ x = (W ι₀)† σ(diag(j x, j x)) (σ(E₀₁) W ι₁)`; both operators are isometries, as `Ψ` is unital and
`Ψ(E₀₁⋆ E₀₁) = Ψ(diag(0, 1)) = diag(0, 1)`. A non-unital `A` passes to its unitization; a trivial `A`
forces `φ = 0` and is handled directly in `CompletelyBoundedMap.exists_factorization_unital`.

## Main results

* `CompletelyBoundedMap.exists_isometry_factorization` — `φ x = ‖φ‖_cb • S₁† π(j x) S₂` with
  isometries `S₁, S₂`; `CompletelyBoundedMap.exists_isometry_factorization_unital` with a unital `π` for
  nontrivial unital `A`.
* `CompletelyBoundedMap.exists_factorization`, `CompletelyBoundedMap.exists_factorization_unital` —
  **the Wittstock–Paulsen–Haagerup theorem**: `φ x = V₁† π(j x) V₂` with `‖V₁‖ ‖V₂‖ = ‖φ‖_cb`.
* `CompletelyBoundedMap.norm_le_of_factorization` — conversely, `‖φ‖_cb ≤ ‖V₁‖ ‖V₂‖` for every
  factorization `φ x = V₁† π(j x) V₂`, through any complete contraction `j : F → A` and any `K`.
* `CompletelyBoundedMap.norm_le_one_iff_exists_factorization` — `φ` is completely contractive exactly when
  it factors through contractions.
* `CompletelyBoundedMap.exists_completelyPositiveMap_offDiagonal` — `φ` extends to `ψ : A → B(H)` with the
  same cb norm, and there are completely positive `φ₁, φ₂ : A → B(H)` with `‖φᵢ a‖ ≤ ‖φ‖_cb ‖a‖` for which
  `!![a, b; c, d] ↦ !![φ₁ a, ψ b; ψ(c⋆)⋆, φ₂ d]` is completely positive.
* `CompletelyBoundedMap.exists_completelyPositiveMap_decomposition` — **Wittstock's decomposition**: `φ` is
  the restriction of `(ψ₀ - ψ₂) + i (ψ₁ - ψ₃)` for four completely positive maps `ψₖ : A → B(H)` with
  `‖ψₖ a‖ ≤ ‖φ‖_cb ‖a‖`.
* `CompletelyBoundedMap.exists_isCompleteIsometry_factorization` — **the Wittstock–Paulsen–Haagerup
  theorem for operator spaces**: for a subspace `E` of an operator space `F`, through a complete isometry
  `j : F → B(K')`.
* `CompletelyBoundedMap.exists_extension` — **the Arveson–Wittstock–Hahn–Banach theorem**.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace InnerProduct
open CStarMatrix

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace CompletelyBoundedMap

/-- The inclusion of `H` as the `j`-th summand of `H ⊕ H = PiLp 2 (fun _ : Fin 2 ↦ H)`. -/
private abbrev ι {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : Fin 2) :
    H →L[ℂ] PiLp 2 (fun _ : Fin 2 => H) :=
  (LinearIsometry.piLpSingle 2 ℂ (fun _ : Fin 2 => H) j).toContinuousLinearMap

private lemma ι_apply (j : Fin 2) (ξ : H) : ι j ξ = PiLp.single 2 j ξ :=
  rfl

/-- The `(i, j)` block of an operator matrix is the compression of the operator it defines on
`H ⊕ H` by the inclusions of the summands. -/
private lemma adjoint_ι_comp_toPiLp_comp_ι [CompleteSpace H]
    (T : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) (i j : Fin 2) :
    (ι (H := H) i)† ∘L toPiLpStarAlgEquiv (Fin 2) H T ∘L ι j = T i j := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun η => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ι_apply, ι_apply, PiLp.inner_single_left,
    toPiLpStarAlgEquiv_apply, Fin.sum_univ_two, PiLp.ofLp_single]
  fin_cases j <;> simp

/-- The inclusions of the summands of `H ⊕ H` are orthogonal isometries. -/
private lemma adjoint_ι_comp_ι [CompleteSpace H] (i j : Fin 2) :
    (ι (H := H) i)† ∘L ι j = if i = j then 1 else 0 := by
  have h := adjoint_ι_comp_toPiLp_comp_ι (H := H) 1 i j
  rwa [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, CStarMatrix.one_apply] at h

/-- An isometry has norm at most `1`. -/
private lemma norm_le_one_of_adjoint_comp_self {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace H] [CompleteSpace K] {S : H →L[ℂ] K} (hS : S† ∘L S = 1) : ‖S‖ ≤ 1 :=
  S.opNorm_le_bound zero_le_one fun x => by
    rw [(ContinuousLinearMap.norm_map_iff_adjoint_comp_self S).mpr hS x, one_mul]

variable [CompleteSpace H]

section Unital

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A unital C⋆-algebra has a unital ⋆-homomorphism into the operators on some Hilbert space: the
Stinespring dilation of the zero map. -/
private lemma exists_unital_starAlgHom (H' : Type v) [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      Nonempty (A →⋆ₐ[ℂ] (K →L[ℂ] K)) := by
  let ψ₀ : A →CP (H' →L[ℂ] H') := ⟨0, fun _ M _ => le_of_eq (CStarMatrix.ext fun _ _ => rfl).symm⟩
  obtain ⟨K, _, _, _, π, -, -⟩ := CompletelyPositiveMap.exists_unital_stinespring_dilation ψ₀
  exact ⟨K, inferInstance, inferInstance, inferInstance, ⟨π⟩⟩

variable {E : Submodule ℂ A}

omit [PartialOrder A] [StarOrderedRing A] in
/-- The coefficient of `1` in `1 ∈ ℂ ∙ 1` is `1`. -/
private lemma coeffOne_one [Nontrivial A] :
    Submodule.coeffOne (A := A) ⟨1, Submodule.mem_span_singleton_self 1⟩ = 1 := by
  rw [Submodule.coeffOne, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq,
    LinearEquiv.toSpanNonzeroSingleton_one]

/-- The completely positive extension to `M₂(A)` of the map induced by a complete contraction `φ` on
the Paulsen system (unital, as `1` lies in the Paulsen system and the Paulsen map fixes it): Arveson's
extension theorem applied to `Submodule.paulsenCompletelyPositiveMap`, transported to `B(H ⊕ H)`. -/
private lemma exists_completelyPositiveMap_paulsen [Nontrivial A] (φ : E →CB (H →L[ℂ] H))
    (hφ : ‖φ‖ ≤ 1) :
    ∃ Ψ : CStarMatrix (Fin 2) (Fin 2) A →CP (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
        PiLp 2 (fun _ : Fin 2 => H)),
      ∀ M : E.paulsenSystem,
        Ψ M = toPiLpStarAlgEquiv (Fin 2) H (Submodule.paulsenMap φ.toLinearMap M) := by
  let e := toPiLpStarAlgEquiv (Fin 2) H
  let eCP : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) →CP' (PiLp 2 (fun _ : Fin 2 => H) →L[ℂ]
      PiLp 2 (fun _ : Fin 2 => H)) :=
    CompletelyPositiveMapClass'.toCompletelyPositiveMap' e
  obtain ⟨Ψ, hΨ⟩ := CompletelyPositiveMap.exists_extension_of_operatorSubsystem
    (eCP.comp (E.paulsenCompletelyPositiveMap φ hφ))
  exact ⟨Ψ, hΨ⟩

/-- **Isometric factorization of a complete contraction** on a subspace of a unital C⋆-algebra:
`φ x = S₁† π(x) S₂` with isometries `S₁ = W ι₀`, `S₂ = σ(E₀₁) W ι₁` read off a Stinespring dilation
`Ψ = W† σ W` of the extension of the Paulsen map. -/
private lemma exists_isometry_factorization_of_norm_le_one [Nontrivial A] (φ : E →CB (H →L[ℂ] H))
    (hφ : ‖φ‖ ≤ 1) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (S₁ S₂ : H →L[ℂ] K), S₁† ∘L S₁ = 1 ∧ S₂† ∘L S₂ = 1 ∧
        ∀ x : E, φ x = S₁† ∘L π x ∘L S₂ := by
  obtain ⟨Ψ, hΨ⟩ := exists_completelyPositiveMap_paulsen φ hφ
  obtain ⟨K, _, _, _, σ, W, hσ, -, -⟩ := CompletelyPositiveMap.exists_unital_stinespring_dilation Ψ
  let π : A →⋆ₐ[ℂ] (K →L[ℂ] K) := σ.comp (diagonalStarAlgHom (n := Fin 2))
  let E₀₁ : CStarMatrix (Fin 2) (Fin 2) A := ofMatrix !![0, 1; 0, 0]
  -- the blocks of `W† σ W` on the Paulsen system are those of the Paulsen map
  have hblock : ∀ (N : CStarMatrix (Fin 2) (Fin 2) A) (hN : N ∈ E.paulsenSystem) (i j : Fin 2),
      (ι i)† ∘L (W† ∘L σ N ∘L W) ∘L ι j = Submodule.paulsenMap φ.toLinearMap ⟨N, hN⟩ i j :=
    fun N hN i j => by
      have h := adjoint_ι_comp_toPiLp_comp_ι (Submodule.paulsenMap φ.toLinearMap ⟨N, hN⟩) i j
      rw [← hΨ ⟨N, hN⟩, hσ] at h
      exact h
  have hσmul : ∀ a b, σ (a * b) = σ a ∘L σ b := fun a b => by
    rw [map_mul, ContinuousLinearMap.mul_def]
  have hone : (1 : CStarMatrix (Fin 2) (Fin 2) A) ∈ E.paulsenSystem := OneMemClass.one_mem _
  have hE₁₁ : (ofMatrix !![0, 0; 0, 1] : CStarMatrix (Fin 2) (Fin 2) A) ∈ E.paulsenSystem :=
    ⟨zero_mem _, zero_mem _, by
      rw [show (ofMatrix !![0, 0; 0, 1] : CStarMatrix (Fin 2) (Fin 2) A) 1 0 = 0 from rfl, star_zero]
      exact zero_mem _, Submodule.mem_span_singleton_self 1⟩
  have hcorner : ∀ x : E, (ofMatrix !![0, (x : A); 0, 0] : CStarMatrix (Fin 2) (Fin 2) A) ∈
      E.paulsenSystem := fun x =>
    ⟨zero_mem _, x.2, by
      rw [show (ofMatrix !![0, (x : A); 0, 0] : CStarMatrix (Fin 2) (Fin 2) A) 1 0 = 0 from rfl,
        star_zero]
      exact zero_mem _, zero_mem _⟩
  have hstar : star E₀₁ * E₀₁ = ofMatrix !![0, 0; 0, 1] := by
    refine CStarMatrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [E₀₁, CStarMatrix.mul_apply, CStarMatrix.star_apply, ofMatrix_apply]
  have hdiag : ∀ a : A, (ofMatrix !![0, a; 0, 0] : CStarMatrix (Fin 2) (Fin 2) A) =
      diagonalStarAlgHom (n := Fin 2) a * E₀₁ := fun a => by
    refine CStarMatrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [E₀₁, diagonalStarAlgHom_apply, CStarMatrix.mul_apply, ofMatrix_apply, Matrix.diagonal_apply]
  refine ⟨K, inferInstance, inferInstance, inferInstance, π, W ∘L ι 0, σ E₀₁ ∘L W ∘L ι 1, ?_, ?_, ?_⟩
  · have h := hblock 1 hone 0 0
    rw [map_one σ, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] at h
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc] at h ⊢
    refine h.trans ?_
    change Submodule.coeffOne (A := A) ⟨1, _⟩ • (1 : H →L[ℂ] H) = 1
    rw [coeffOne_one, one_smul]
  · have key : (σ E₀₁ ∘L W ∘L ι 1)† ∘L σ E₀₁ ∘L W ∘L ι 1 =
        (ι 1)† ∘L (W† ∘L σ (ofMatrix !![0, 0; 0, 1]) ∘L W) ∘L ι 1 := by
      rw [← hstar, hσmul, map_star, ContinuousLinearMap.star_eq_adjoint]
      simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
    rw [key, hblock _ hE₁₁ 1 1]
    change Submodule.coeffOne (A := A) ⟨1, _⟩ • (1 : H →L[ℂ] H) = 1
    rw [coeffOne_one, one_smul]
  · intro x
    have key : (W ∘L ι 0)† ∘L π x ∘L σ E₀₁ ∘L W ∘L ι 1 =
        (ι 0)† ∘L (W† ∘L σ (ofMatrix !![0, (x : A); 0, 0]) ∘L W) ∘L ι 1 := by
      rw [hdiag, hσmul]
      simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
      rfl
    rw [key, hblock _ (hcorner x) 0 1]
    rfl

/-- **Wittstock–Paulsen–Haagerup theorem, isometric form, for a unital C⋆-algebra.** A completely
bounded map `φ : F → B(H)` on an operator space completely isometrically embedded in a nontrivial
unital C⋆-algebra `A` by `j` is `φ x = ‖φ‖_cb • S₁† π(j x) S₂` for a unital ⋆-homomorphism
`π : A → B(K)` and isometries `S₁, S₂ : H → K`. -/
lemma exists_isometry_factorization_unital [Nontrivial A] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) F)] [OperatorSpace F]
    {j : F →ₗ[ℂ] A} (hj : OperatorSpace.IsCompleteIsometry j) (φ : F →CB (H →L[ℂ] H)) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (S₁ S₂ : H →L[ℂ] K), S₁† ∘L S₁ = 1 ∧ S₂† ∘L S₂ = 1 ∧
        ∀ x, φ x = (‖φ‖ : ℂ) • (S₁† ∘L π (j x) ∘L S₂) := by
  obtain ⟨φ', hφ', hn⟩ := hj.exists_completelyBoundedMap_range φ
  set r := ‖φ‖
  have hle : ‖(r⁻¹ : ℂ) • φ'‖ ≤ 1 := by
    rw [norm_smul', hn, norm_inv, Complex.norm_real, Real.norm_of_nonneg φ.norm_nonneg']
    rcases φ.norm_nonneg'.eq_or_lt with h | h
    · rw [← h, inv_zero, zero_mul]
      exact zero_le_one
    · rw [inv_mul_cancel₀ h.ne']
  obtain ⟨K, _, _, _, π, S₁, S₂, h₁, h₂, h⟩ := exists_isometry_factorization_of_norm_le_one _ hle
  refine ⟨K, inferInstance, inferInstance, inferInstance, π, S₁, S₂, h₁, h₂, fun x => ?_⟩
  have hx := h ⟨j x, LinearMap.mem_range_self j x⟩
  rw [show ((r⁻¹ : ℂ) • φ') ⟨j x, _⟩ = (r⁻¹ : ℂ) • φ x by rw [coe_smul, Pi.smul_apply, hφ']] at hx
  change _ = (r : ℂ) • (S₁† ∘L π (j x) ∘L S₂)
  rw [← hx]
  rcases φ.norm_nonneg'.eq_or_lt with hr | hr
  · have : φ = 0 := (norm_eq_zero_iff' φ).mp hr.symm
    rw [this]
    simp
  · rw [smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne',
      Complex.ofReal_one, one_smul]

end Unital

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) F)]
  [OperatorSpace F] {j : F →ₗ[ℂ] A}

/-- **Wittstock–Paulsen–Haagerup theorem, isometric form.** A completely bounded map `φ : F → B(H)` on an
operator space completely isometrically embedded in a C⋆-algebra `A` by `j` is
`φ x = ‖φ‖_cb • S₁† π(j x) S₂` for a ⋆-homomorphism `π : A → B(K)` and isometries `S₁, S₂ : H → K`.
The unitization of `A` reduces this to `CompletelyBoundedMap.exists_isometry_factorization_unital`. -/
lemma exists_isometry_factorization (hj : OperatorSpace.IsCompleteIsometry j)
    (φ : F →CB (H →L[ℂ] H)) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (S₁ S₂ : H →L[ℂ] K), S₁† ∘L S₁ = 1 ∧ S₂† ∘L S₂ = 1 ∧
        ∀ x, φ x = (‖φ‖ : ℂ) • (S₁† ∘L π (j x) ∘L S₂) := by
  let := CStarAlgebra.spectralOrder (Unitization ℂ A)
  have := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  let i := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hi := i.isCompleteIsometry Unitization.inr_injective
  obtain ⟨K, _, _, _, π, S₁, S₂, h₁, h₂, h⟩ :=
    exists_isometry_factorization_unital (A := Unitization ℂ A) (hi.comp hj) φ
  exact ⟨K, inferInstance, inferInstance, inferInstance, π.toNonUnitalStarAlgHom.comp i, S₁, S₂, h₁, h₂,
    h⟩

/-- The balanced factorization `φ x = V₁† π(j x) V₂` with `‖Vᵢ‖² ≤ ‖φ‖_cb`, from the isometric one with
`Vᵢ = ‖φ‖_cb^{1/2} • Sᵢ`. -/
private lemma exists_balanced_factorization (hj : OperatorSpace.IsCompleteIsometry j)
    (φ : F →CB (H →L[ℂ] H)) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V₁ V₂ : H →L[ℂ] K), ‖V₁‖ ^ 2 ≤ ‖φ‖ ∧ ‖V₂‖ ^ 2 ≤ ‖φ‖ ∧
        ∀ x, φ x = V₁† ∘L π (j x) ∘L V₂ := by
  obtain ⟨K, _, _, _, π, S₁, S₂, h₁, h₂, h⟩ := exists_isometry_factorization hj φ
  set r := ‖φ‖
  have hr := φ.norm_nonneg'
  let s : ℂ := (Real.sqrt r : ℂ)
  have hs : ‖s‖ = Real.sqrt r := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg r)]
  have hbound : ∀ {S : H →L[ℂ] K}, S† ∘L S = 1 → ‖s • S‖ ^ 2 ≤ r := fun {S} hS => by
    rw [norm_smul, hs, mul_pow, Real.sq_sqrt hr]
    exact mul_le_of_le_one_right hr (pow_le_one₀ (norm_nonneg _) (norm_le_one_of_adjoint_comp_self hS))
  refine ⟨K, inferInstance, inferInstance, inferInstance, π, s • S₁, s • S₂, hbound h₁, hbound h₂,
    fun x => ?_⟩
  rw [h x, map_smulₛₗ, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_smul, smul_smul]
  congr 1
  rw [show (starRingEnd ℂ) s = s from Complex.conj_ofReal _, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hr]

/-- **The converse of the Wittstock–Paulsen–Haagerup theorem.** A completely bounded map `φ : F → B(H)`
that factors as `x ↦ V₁† π(j x) V₂` through a ⋆-homomorphism `π : A → B(K)` and a complete contraction
`j : F → A` has cb norm at most `‖V₁‖ ‖V₂‖`. -/
lemma norm_le_of_factorization (j : F →CB A) (hj : ‖j‖ ≤ 1) (φ : F →CB (H →L[ℂ] H))
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V₁ V₂ : H →L[ℂ] K) (h : ∀ x, φ x = V₁† ∘L π (j x) ∘L V₂) :
    ‖φ‖ ≤ ‖V₁‖ * ‖V₂‖ := by
  have hφ : φ = ((ContinuousLinearMap.compressionCB V₁ V₂).comp π.toCompletelyBoundedMap).comp j := ext h
  rw [hφ]
  exact (norm_comp_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg' _) hj).trans
    (ContinuousLinearMap.norm_compressionCB_comp_le π V₁ V₂))

/-- **Wittstock–Paulsen–Haagerup theorem.** A completely bounded map `φ : F → B(H)` on an operator space
completely isometrically embedded in a C⋆-algebra `A` by `j` factors as `φ x = V₁† π(j x) V₂` through a
⋆-homomorphism `π : A → B(K)`, with `‖V₁‖ ‖V₂‖ = ‖φ‖_cb`. -/
theorem exists_factorization (hj : OperatorSpace.IsCompleteIsometry j) (φ : F →CB (H →L[ℂ] H)) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V₁ V₂ : H →L[ℂ] K),
        (∀ x, φ x = V₁† ∘L π (j x) ∘L V₂) ∧ ‖V₁‖ * ‖V₂‖ = ‖φ‖ := by
  obtain ⟨K, _, _, _, π, V₁, V₂, h₁, h₂, h⟩ := exists_balanced_factorization hj φ
  refine ⟨K, inferInstance, inferInstance, inferInstance, π, V₁, V₂, h, le_antisymm ?_
    (norm_le_of_factorization hj.toCompletelyBoundedMap hj.norm_toCompletelyBoundedMap_le φ π V₁ V₂ h)⟩
  nlinarith [norm_nonneg V₁, norm_nonneg V₂, φ.norm_nonneg', sq_nonneg (‖V₁‖ - ‖V₂‖)]

/-- **Completely contractive maps are the compressions of ⋆-homomorphisms by contractions.** A map
`φ : F → B(H)` on an operator space completely isometrically embedded in a C⋆-algebra `A` by `j` has
`‖φ‖_cb ≤ 1` exactly when `φ x = V₁† π(j x) V₂` for a ⋆-homomorphism `π : A → B(K)` and contractions
`V₁, V₂ : H → K`, with `K` in the universe `max u v` of `A` and `H`; for a `K` in any universe the
converse is `CompletelyBoundedMap.norm_le_of_factorization`. -/
theorem norm_le_one_iff_exists_factorization (hj : OperatorSpace.IsCompleteIsometry j)
    (φ : F →CB (H →L[ℂ] H)) :
    ‖φ‖ ≤ 1 ↔ ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V₁ V₂ : H →L[ℂ] K),
        ‖V₁‖ ≤ 1 ∧ ‖V₂‖ ≤ 1 ∧ ∀ x, φ x = V₁† ∘L π (j x) ∘L V₂ := by
  refine ⟨fun hφ => ?_, fun ⟨K, _, _, _, π, V₁, V₂, h₁, h₂, h⟩ => ?_⟩
  · obtain ⟨K, _, _, _, π, V₁, V₂, h₁, h₂, h⟩ := exists_balanced_factorization hj φ
    refine ⟨K, inferInstance, inferInstance, inferInstance, π, V₁, V₂, ?_, ?_, h⟩ <;>
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by linarith)
  · exact (norm_le_of_factorization hj.toCompletelyBoundedMap hj.norm_toCompletelyBoundedMap_le φ π V₁ V₂
      h).trans ((mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

/-- The map `M ↦ (Vᵢ† π(Mᵢⱼ) Vⱼ)ᵢⱼ` on `M₂(A)` is completely positive: it is the ⋆-homomorphism `π` applied
entrywise, followed by the compression of `B(K ⊕ K)` by `D = V₀ ⊕ V₁`. -/
private lemma exists_completelyPositiveMap_compression {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : Fin 2 → (H →L[ℂ] K)) :
    ∃ Φ : CStarMatrix (Fin 2) (Fin 2) A →CP CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H),
      ∀ M i j, Φ M i j = (V i)† ∘L π (M i j) ∘L V j := by
  let eH := toPiLpStarAlgEquiv (Fin 2) H
  let eK := toPiLpStarAlgEquiv (Fin 2) K
  let D : PiLp 2 (fun _ : Fin 2 => H) →L[ℂ] PiLp 2 (fun _ : Fin 2 => K) :=
    ι (H := K) 0 ∘L V 0 ∘L (ι (H := H) 0)† + ι (H := K) 1 ∘L V 1 ∘L (ι (H := H) 1)†
  have hD : ∀ j, D ∘L ι j = ι j ∘L V j := fun j => by
    simp only [D, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc, adjoint_ι_comp_ι]
    fin_cases j <;> simp [ContinuousLinearMap.one_def]
  let Φ : CStarMatrix (Fin 2) (Fin 2) A →CP CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap eH.symm).comp
      ((ContinuousLinearMap.compressionCP D).comp
        ((CompletelyPositiveMapClass.toCompletelyPositiveLinearMap eK).comp
          (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (mapₙₐ (n := Fin 2) π))))
  refine ⟨Φ, fun M i j => ?_⟩
  have h := adjoint_ι_comp_toPiLp_comp_ι (eH.symm (D† ∘L eK (M.map π) ∘L D)) i j
  rw [StarAlgEquiv.apply_symm_apply] at h
  change eH.symm (D† ∘L eK (M.map π) ∘L D) i j = _
  rw [← h]
  have h2 := adjoint_ι_comp_toPiLp_comp_ι (M.map π) i j
  have hi := congrArg ContinuousLinearMap.adjoint (hD i)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at hi
  calc (ι i)† ∘L (D† ∘L eK (M.map π) ∘L D) ∘L ι j
      = ((ι i)† ∘L D†) ∘L eK (M.map π) ∘L (D ∘L ι j) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = (V i)† ∘L ((ι i)† ∘L eK (M.map π) ∘L ι j) ∘L V j := by
        rw [hi, hD j]
        simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := congrArg (fun T => (V i)† ∘L T ∘L V j) h2

/-- **Completely bounded maps as corners of completely positive maps.** For a completely bounded map
`φ : F → B(H)` on an operator space completely isometrically embedded in a C⋆-algebra `A` by `j`, there
are an extension `ψ : A → B(H)` of `φ` with the same cb norm and completely positive maps
`φ₁, φ₂ : A → B(H)` with `‖φᵢ a‖ ≤ ‖φ‖_cb ‖a‖` such that `!![a, b; c, d] ↦ !![φ₁ a, ψ b; ψ(c⋆)⋆, φ₂ d]`
is completely positive on `M₂(A)`. With `φ x = V₁† π(j x) V₂` balanced, `φᵢ = Vᵢ† π Vᵢ`. -/
lemma exists_completelyPositiveMap_offDiagonal (hj : OperatorSpace.IsCompleteIsometry j)
    (φ : F →CB (H →L[ℂ] H)) :
    ∃ (ψ : A →CB (H →L[ℂ] H)) (φ₁ φ₂ : A →CP (H →L[ℂ] H))
      (Φ : CStarMatrix (Fin 2) (Fin 2) A →CP CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)),
        (∀ x, ψ (j x) = φ x) ∧ ‖ψ‖ = ‖φ‖ ∧ (∀ a, ‖φ₁ a‖ ≤ ‖φ‖ * ‖a‖) ∧ (∀ a, ‖φ₂ a‖ ≤ ‖φ‖ * ‖a‖) ∧
          ∀ M, Φ M = ofMatrix !![φ₁ (M 0 0), ψ (M 0 1); star (ψ (star (M 1 0))), φ₂ (M 1 1)] := by
  obtain ⟨K, _, _, _, π, V₁, V₂, h₁, h₂, h⟩ := exists_balanced_factorization hj φ
  let πCP : A →CP (K →L[ℂ] K) := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap π
  let ψ := (ContinuousLinearMap.compressionCB V₁ V₂).comp π.toCompletelyBoundedMap
  have hψ : ∀ x, ψ (j x) = φ x := fun x => (h x).symm
  have hbound : ∀ (V : H →L[ℂ] K), ‖V‖ ^ 2 ≤ ‖φ‖ → ∀ a,
      ‖((ContinuousLinearMap.compressionCP V).comp πCP) a‖ ≤ ‖φ‖ * ‖a‖ := fun V hV a => by
    change ‖V† ∘L π a ∘L V‖ ≤ _
    calc ‖V† ∘L π a ∘L V‖ ≤ ‖V†‖ * (‖π a‖ * ‖V‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖V‖ ^ 2 * ‖π a‖ := by rw [LinearIsometryEquiv.norm_map]; ring
      _ ≤ ‖φ‖ * ‖a‖ := mul_le_mul hV (NonUnitalStarAlgHom.norm_apply_le π a) (norm_nonneg _)
          φ.norm_nonneg'
  obtain ⟨Φ, hΦ⟩ := exists_completelyPositiveMap_compression π ![V₁, V₂]
  refine ⟨ψ, (ContinuousLinearMap.compressionCP V₁).comp πCP,
    (ContinuousLinearMap.compressionCP V₂).comp πCP, Φ, hψ, le_antisymm ?_ ?_, hbound V₁ h₁,
    hbound V₂ h₂, fun M => ?_⟩
  · refine (ContinuousLinearMap.norm_compressionCB_comp_le π V₁ V₂).trans ?_
    nlinarith [norm_nonneg V₁, norm_nonneg V₂, φ.norm_nonneg', sq_nonneg (‖V₁‖ - ‖V₂‖)]
  · have hφ : φ = ψ.comp hj.toCompletelyBoundedMap := ext fun x => (hψ x).symm
    conv_lhs => rw [hφ]
    exact (norm_comp_le _ _).trans (mul_le_of_le_one_right ψ.norm_nonneg'
      hj.norm_toCompletelyBoundedMap_le)
  · refine CStarMatrix.ext fun i k => ?_
    rw [hΦ]
    fin_cases i <;> fin_cases k
    · rfl
    · rfl
    · change V₂† ∘L π (M 1 0) ∘L V₁ = star (V₁† ∘L π (star (M 1 0)) ∘L V₂)
      rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_adjoint,
        ContinuousLinearMap.comp_assoc]
    · rfl

/-- **Polarization**: `X† T Y = ∑ₖ iᵏ Wₖ† T Wₖ` with `Wₖ = ½ (Y + iᵏ X)`. -/
private lemma adjoint_comp_comp_eq_sum {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (T : K →L[ℂ] K) (X Y : H →L[ℂ] K) :
    X† ∘L T ∘L Y = ∑ k : Fin 4, Complex.I ^ (k : ℕ) •
      (((1 / 2 : ℂ) • (Y + Complex.I ^ (k : ℕ) • X))† ∘L T ∘L
        ((1 / 2 : ℂ) • (Y + Complex.I ^ (k : ℕ) • X))) := by
  simp only [Fin.sum_univ_four, map_smulₛₗ, map_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_add, smul_smul, map_div₀, map_one, map_ofNat]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  match_scalars <;> simp [Complex.ext_iff, pow_succ, Complex.conj_ofNat]
  norm_num

/-- **Wittstock's decomposition.** A completely bounded map `φ : F → B(H)` on an operator space completely
isometrically embedded in a C⋆-algebra `A` by `j` is `φ x = (ψ₀ - ψ₂)(j x) + i (ψ₁ - ψ₃)(j x)` for four
completely positive maps `ψₖ : A → B(H)` with `‖ψₖ a‖ ≤ ‖φ‖_cb ‖a‖`: polarizing `φ x = V₁† π(j x) V₂`,
`ψₖ = Wₖ† π Wₖ` with `Wₖ = ½ (V₂ + iᵏ V₁)`, so that `φ x = ∑ₖ iᵏ ψₖ(j x)`. -/
theorem exists_completelyPositiveMap_decomposition (hj : OperatorSpace.IsCompleteIsometry j)
    (φ : F →CB (H →L[ℂ] H)) :
    ∃ ψ : Fin 4 → (A →CP (H →L[ℂ] H)),
      (∀ x, φ x = ψ 0 (j x) - ψ 2 (j x) + Complex.I • (ψ 1 (j x) - ψ 3 (j x))) ∧
        ∀ k a, ‖ψ k a‖ ≤ ‖φ‖ * ‖a‖ := by
  obtain ⟨K, _, _, _, π, V₁, V₂, h₁, h₂, h⟩ := exists_balanced_factorization hj φ
  let πCP : A →CP (K →L[ℂ] K) := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap π
  let W : Fin 4 → (H →L[ℂ] K) := fun k => (1 / 2 : ℂ) • (V₂ + Complex.I ^ (k : ℕ) • V₁)
  have hr := φ.norm_nonneg'
  have hV : ∀ {V : H →L[ℂ] K}, ‖V‖ ^ 2 ≤ ‖φ‖ → ‖V‖ ≤ Real.sqrt ‖φ‖ := fun hV =>
    Real.le_sqrt_of_sq_le hV
  have hW : ∀ k, ‖W k‖ ^ 2 ≤ ‖φ‖ := fun k => by
    have : ‖W k‖ ≤ Real.sqrt ‖φ‖ := by
      calc ‖W k‖ ≤ 1 / 2 * (‖V₂‖ + ‖V₁‖) := by
            rw [norm_smul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
            gcongr
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
        _ ≤ 1 / 2 * (Real.sqrt ‖φ‖ + Real.sqrt ‖φ‖) := by gcongr <;> exact hV ‹_›
        _ = Real.sqrt ‖φ‖ := by ring
    calc ‖W k‖ ^ 2 ≤ Real.sqrt ‖φ‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = ‖φ‖ := Real.sq_sqrt hr
  refine ⟨fun k => (ContinuousLinearMap.compressionCP (W k)).comp πCP, fun x => ?_, fun k a => ?_⟩
  · rw [h x, adjoint_comp_comp_eq_sum (π (j x)) V₁ V₂, Fin.sum_univ_four]
    change _ = (W 0)† ∘L π (j x) ∘L W 0 - (W 2)† ∘L π (j x) ∘L W 2 +
      Complex.I • ((W 1)† ∘L π (j x) ∘L W 1 - (W 3)† ∘L π (j x) ∘L W 3)
    simp only [W, Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_zero,
      pow_one, Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq, neg_one_mul],
      one_smul, neg_smul]
    module
  · change ‖(W k)† ∘L π a ∘L W k‖ ≤ _
    calc ‖(W k)† ∘L π a ∘L W k‖ ≤ ‖(W k)†‖ * (‖π a‖ * ‖W k‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖W k‖ ^ 2 * ‖π a‖ := by rw [LinearIsometryEquiv.norm_map]; ring
      _ ≤ ‖φ‖ * ‖a‖ := mul_le_mul (hW k) (NonUnitalStarAlgHom.norm_apply_le π a) (norm_nonneg _) hr

end NonUnital

section Unital

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) F)]
  [OperatorSpace F] {j : F →ₗ[ℂ] A}

/-- **Wittstock–Paulsen–Haagerup theorem for a unital C⋆-algebra.** A completely bounded map
`φ : F → B(H)` on an operator space completely isometrically embedded in a unital C⋆-algebra `A` by `j`
factors as `φ x = V₁† π(j x) V₂` through a unital ⋆-homomorphism `π : A → B(K)`, with
`‖V₁‖ ‖V₂‖ = ‖φ‖_cb`. -/
theorem exists_factorization_unital (hj : OperatorSpace.IsCompleteIsometry j) (φ : F →CB (H →L[ℂ] H)) :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V₁ V₂ : H →L[ℂ] K),
        (∀ x, φ x = V₁† ∘L π (j x) ∘L V₂) ∧ ‖V₁‖ * ‖V₂‖ = ‖φ‖ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · -- `F` embeds in the trivial algebra, so `φ = 0`
    have hφ : φ = 0 := ext fun x => by
      rw [show x = 0 from hj.injective (Subsingleton.elim _ _), map_zero, coe_zero, Pi.zero_apply]
    obtain ⟨K, _, _, _, ⟨π⟩⟩ := exists_unital_starAlgHom (A := A) H
    exact ⟨K, inferInstance, inferInstance, inferInstance, π, 0, 0, fun x => by simp [hφ],
      by rw [hφ, norm_zero', norm_zero, zero_mul]⟩
  obtain ⟨K, _, _, _, π, S₁, S₂, h₁, h₂, h⟩ := exists_isometry_factorization_unital hj φ
  have hfac : ∀ x, φ x = S₁† ∘L π (j x) ∘L ((‖φ‖ : ℂ) • S₂) := fun x => by
    rw [h x, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  refine ⟨K, inferInstance, inferInstance, inferInstance, π, S₁, (‖φ‖ : ℂ) • S₂, hfac,
    le_antisymm ?_ (norm_le_of_factorization hj.toCompletelyBoundedMap hj.norm_toCompletelyBoundedMap_le φ
      π.toNonUnitalStarAlgHom S₁ _ hfac)⟩
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg φ.norm_nonneg']
  calc ‖S₁‖ * (‖φ‖ * ‖S₂‖) ≤ 1 * (‖φ‖ * 1) := by
        gcongr
        · exact norm_le_one_of_adjoint_comp_self h₁
        · exact norm_le_one_of_adjoint_comp_self h₂
    _ = ‖φ‖ := by ring

end Unital

section OperatorSpace

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) F)]
  [OperatorSpace F] {E : Submodule ℂ F}

/-- **Wittstock–Paulsen–Haagerup theorem for operator spaces.** A completely bounded map `φ : E → B(H)` on
a subspace `E` of an operator space `F` factors as `φ x = V₁† π(j x) V₂`, where `j : F → B(K')` is a
complete isometry (`OperatorSpace.exists_isCompleteIsometry`, Ruan's theorem) and
`π : B(K') → B(K)` a unital ⋆-homomorphism, with `‖V₁‖ ‖V₂‖ = ‖φ‖_cb`. -/
theorem exists_isCompleteIsometry_factorization (φ : E →CB (H →L[ℂ] H)) :
    ∃ (K' : Type u) (_ : NormedAddCommGroup K') (_ : InnerProductSpace ℂ K') (_ : CompleteSpace K')
      (j : F →ₗ[ℂ] (K' →L[ℂ] K')) (_ : OperatorSpace.IsCompleteIsometry j)
      (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : (K' →L[ℂ] K') →⋆ₐ[ℂ] (K →L[ℂ] K)) (V₁ V₂ : H →L[ℂ] K),
        (∀ x : E, φ x = V₁† ∘L π (j x) ∘L V₂) ∧ ‖V₁‖ * ‖V₂‖ = ‖φ‖ := by
  obtain ⟨K', _, _, _, j, hj⟩ := OperatorSpace.exists_isCompleteIsometry F
  obtain ⟨K, _, _, _, π, V₁, V₂, h, hn⟩ :=
    exists_factorization_unital (hj.comp E.isCompleteIsometry_subtype) φ
  exact ⟨K', inferInstance, inferInstance, inferInstance, j, hj, K, inferInstance, inferInstance,
    inferInstance, π, V₁, V₂, h, hn⟩

/-- **Arveson–Wittstock–Hahn–Banach theorem.** A completely bounded map `φ : E → B(H)` on a subspace `E` of
an operator space `F` extends to a completely bounded map `ψ : F → B(H)` with the same cb norm: the map
`x ↦ V₁† π(j x) V₂` of a factorization of `φ`
(`CompletelyBoundedMap.exists_isCompleteIsometry_factorization`). -/
theorem exists_extension (φ : E →CB (H →L[ℂ] H)) :
    ∃ ψ : F →CB (H →L[ℂ] H), ψ.restrict E = φ ∧ ‖ψ‖ = ‖φ‖ := by
  obtain ⟨K', _, _, _, j, hj, K, _, _, _, π, V₁, V₂, h, hn⟩ := exists_isCompleteIsometry_factorization φ
  let ψ := ((ContinuousLinearMap.compressionCB V₁ V₂).comp
    π.toNonUnitalStarAlgHom.toCompletelyBoundedMap).comp hj.toCompletelyBoundedMap
  have hres : ψ.restrict E = φ := ext fun x => (h x).symm
  refine ⟨ψ, hres, le_antisymm ?_ ?_⟩
  · refine (norm_comp_le _ _).trans ?_
    rw [← hn]
    exact (mul_le_of_le_one_right (norm_nonneg' _) hj.norm_toCompletelyBoundedMap_le).trans
      (ContinuousLinearMap.norm_compressionCB_comp_le _ V₁ V₂)
  · conv_lhs => rw [← hres]
    exact norm_restrict_le ψ E

end OperatorSpace

end CompletelyBoundedMap
