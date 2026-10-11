/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.Choi
public import QuantumSystem.Analysis.InnerProductSpace.PartialTrace
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.BoundedOperatorRepresentation
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProductCompletion

/-!
# Stinespring's theorem for bounded operators

Let `H` and `K` be finite-dimensional complex Hilbert spaces and `b` an orthonormal basis of `H`.
A linear map `Φ : B(H) → B(K)` is completely positive iff `Φ(A) = tr₂(V A V†)` for some
`V : H → K ⊗ ℂʳ`, and a CPTP map iff moreover `V` is an isometry, `V† V = 1`
(`CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespring`,
`CPTPMap.exists_coe_eq_iff_exists_stinespring`). The environment `ℂʳ` has the dimension
`r = rank J_b(Φ)` of the Choi operator, and this is minimal: every such `V : H → K ⊗ E` has
`dim E ≥ rank J_b(Φ)` (`ContinuousLinearMap.finrank_range_choi_le_finrank_of_stinespring`). In
particular a completely positive map has a Kraus representation with exactly `rank J_b(Φ)`
operators (`CompletelyPositiveMap.exists_kraus_finrank_range_choi`).

## Derivation from the general theorem

The existence of `V` is derived from Stinespring's theorem for completely positive maps into
`B(H)` (`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/Stinespring.lean`); no Kraus
representation is chosen. The trace dual `ψ = φ* : B(K) → B(H)` is completely positive
(`CompletelyPositiveMap.traceDual`), so `ψ(B) = W† π(B) W` for the unital Stinespring
representation `π : B(K) → B(L)` and the Stinespring operator `W : H → L`. A unital
⋆-representation of `B(K)` is a multiple of the identity representation
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/BoundedOperatorRepresentation.lean`): a unitary
`U : K ⊗ ℂᵈ ≃ L` has `π(B) U = U (B ⊗ 1)`. Hence `φ*(B) = V† (B ⊗ 1) V` for `V = U† W`, that is,
`φ(A) = tr₂(V A V†)` (`ContinuousLinearMap.traceDual_eq_iff_traceRight`).

The minimality of the Stinespring representation, that the vectors `π(B) W ξ` span `L`, makes the
Kraus blocks `Tₐ = ιₐ† V` of `V` linearly independent: if `Σₐ cₐ Tₐ = 0`, the vector
`U (ξ₀ ⊗ Σₐ c̄ₐ eₐ)` is orthogonal to every `π(B) W ξ`. They are Kraus operators of `φ`, so
`d = rank J_b(φ)` (`ContinuousLinearMap.finrank_range_choi_eq_card_iff_linearIndependent`).

## Conventions

The environment is the **right** factor of `K ⊗ E` and is removed by the partial trace
`tr₂ = ContinuousLinearMap.traceRight`: Watrous's convention `Φ(X) = Tr_Z (A X A*)` with
`A : X → Y ⊗ Z`, and Stinespring's `π(B) = B ⊗ 1`.

## Main definitions

* `ContinuousLinearMap.krausBlock f V a`: the Kraus block `Tₐ = ιₐ† V : H → K` of
  `V : H → K ⊗ E` along an orthonormal basis `f` of `E`, with the insertions `ιₐ : k ↦ k ⊗ fₐ`.
* `CompletelyPositiveMap.ofStinespring V`: `A ↦ tr₂(V A V†)` as a completely positive map.
* `CPTPMap.ofStinespring V hV`: `A ↦ tr₂(V A V†)` for an isometry `V` as a CPTP map.

## Main statements

* `ContinuousLinearMap.traceRight_comp_comp_adjoint`: `tr₂(V A V†) = Σₐ Tₐ A Tₐ†`.
* `ContinuousLinearMap.finrank_range_choi_le_finrank_of_stinespring`,
  `ContinuousLinearMap.finrank_range_choi_eq_card_iff_linearIndependent_krausBlock`:
  **minimality**: every `V : H → K ⊗ E` with `Φ(A) = tr₂(V A V†)` has `dim E ≥ rank J_b(Φ)`, with
  equality iff its Kraus blocks are linearly independent.
* `CompletelyPositiveMap.exists_stinespring`: **Stinespring's theorem**: a CP map is
  `A ↦ tr₂(V A V†)` for some `V : H → K ⊗ ℂʳ`, `r = rank J_b(φ)`.
* `CompletelyPositiveMap.exists_traceDual_eq_stinespring`: **Stinespring's theorem, Heisenberg
  picture**: the trace dual of a CP map is `B ↦ V† (B ⊗ 1) V` for the same kind of `V`.
* `CompletelyPositiveMap.exists_kraus_finrank_range_choi`: a CP map has a Kraus representation with
  exactly `rank J_b(φ)` operators; this rank does not depend on `b`
  (`CompletelyPositiveMap.finrank_range_choi_congr`).
* `CPTPMap.exists_traceDual_eq_stinespring`, `CPTPMap.exists_stinespring`,
  `CPTPMap.exists_kraus_finrank_range_choi`: the same for CPTP maps, with `V† V = 1`
  and `Σₐ Tₐ† Tₐ = 1`.
* `CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespring`,
  `CompletelyPositiveMap.exists_coe_eq_iff_exists_kraus_finrank_range_choi`,
  `CPTPMap.exists_coe_eq_iff_exists_stinespring`,
  `CPTPMap.exists_coe_eq_iff_exists_kraus_finrank_range_choi`: the characterisations of
  completely positive maps and of CPTP maps.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216.
* Watrous, *The Theory of Quantum Information*, Theorem 2.22 and Corollary 2.27 (with the Choi
  operator's factors in the opposite order)
-/

@[expose] public section

open TensorProduct InnerProductSpace ContinuousLinearMap
open scoped TensorProduct InnerProductSpace CStarAlgebra

variable {H K E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

/-! ### Kraus blocks and minimality -/

namespace ContinuousLinearMap

variable {κ : Type*} [Fintype κ]

/-- The **Kraus blocks** `Tₐ = ιₐ† V : H → K` of `V : H → K ⊗ E` along an orthonormal basis `f` of
`E`, with the insertions `ιₐ = (mkL ℂ K E).flip fₐ : k ↦ k ⊗ fₐ`, so that `V ξ = Σₐ Tₐ ξ ⊗ fₐ`.
They are the Kraus operators of `A ↦ tr₂(V A V†)` (`ContinuousLinearMap.traceRight_comp_comp_adjoint`).
-/
noncomputable def krausBlock (f : OrthonormalBasis κ ℂ E) (V : H →L[ℂ] K ⊗[ℂ] E) (a : κ) :
    H →L[ℂ] K :=
  adjoint ((mkL ℂ K E).flip (f a)) ∘L V

/-- Conjugation by `V : H → K ⊗ E` followed by the partial trace is the Kraus map of the Kraus
blocks `Tₐ` of `V`: `tr₂(V A V†) = Σₐ Tₐ A Tₐ†` (`ContinuousLinearMap.traceRight_eq_sum`). -/
lemma traceRight_comp_comp_adjoint (f : OrthonormalBasis κ ℂ E) (V : H →L[ℂ] K ⊗[ℂ] E)
    (A : H →L[ℂ] H) :
    traceRight K E (V ∘L A ∘L adjoint V) =
      ∑ a, krausBlock f V a ∘L A ∘L adjoint (krausBlock f V a) := by
  rw [traceRight_eq_sum f]
  simp only [krausBlock, adjoint_comp, adjoint_adjoint, comp_assoc]

variable {F : Type*} [FunLike F (H →L[ℂ] H) (K →L[ℂ] K)]

/-- **Minimality of the environment**: if `Φ(A) = tr₂(V A V†)` for `V : H → K ⊗ E`, then
`dim E ≥ rank J_b(Φ)`: the Kraus blocks of `V` along an orthonormal basis of `E` are `dim E` Kraus
operators of `Φ` (`ContinuousLinearMap.finrank_range_choi_le_card`). -/
lemma finrank_range_choi_le_finrank_of_stinespring (b : OrthonormalBasis ι ℂ H) {Φ : F}
    (V : H →L[ℂ] K ⊗[ℂ] E) (hV : ∀ A, Φ A = traceRight K E (V ∘L A ∘L adjoint V)) :
    Module.finrank ℂ ((choi b Φ).range) ≤
      Module.finrank ℂ E := by
  have h := finrank_range_choi_le_card b (Φ := Φ) (κ := Fin (Module.finrank ℂ E))
    (T := krausBlock (stdOrthonormalBasis ℂ E) V) fun A => by
      rw [hV, traceRight_comp_comp_adjoint (stdOrthonormalBasis ℂ E)]
  rwa [Fintype.card_fin] at h

/-- The environment of `Φ(A) = tr₂(V A V†)` has the minimal dimension `rank J_b(Φ)` iff the Kraus
blocks of `V` are linearly independent
(`ContinuousLinearMap.finrank_range_choi_eq_card_iff_linearIndependent`). -/
lemma finrank_range_choi_eq_card_iff_linearIndependent_krausBlock (b : OrthonormalBasis ι ℂ H)
    {Φ : F} (f : OrthonormalBasis κ ℂ E) (V : H →L[ℂ] K ⊗[ℂ] E)
    (hV : ∀ A, Φ A = traceRight K E (V ∘L A ∘L adjoint V)) :
    Module.finrank ℂ ((choi b Φ).range) = Fintype.card κ ↔
      LinearIndependent ℂ (krausBlock f V) :=
  finrank_range_choi_eq_card_iff_linearIndependent b fun A => by
    rw [hV, traceRight_comp_comp_adjoint f]

omit [FiniteDimensional ℂ H] in
/-- **Minimal dilations have linearly independent Kraus blocks.** Let `π : B(K) → B(L)` be a
⋆-representation and `W : H → L` an operator such that the vectors `π(B) W ξ` span a dense subspace
of `L`, and let `U : K ⊗ E ≃ L` be a unitary with `π(B) U = U (B ⊗ 1)` and `W = U V`. Then the
Kraus blocks of `V : H → K ⊗ E` are linearly independent: if `Σₐ cₐ Tₐ = 0`, the vector
`U (ξ₀ ⊗ Σₐ c̄ₐ fₐ)` is orthogonal to every `π(B) W ξ`, hence zero, so `Σₐ c̄ₐ fₐ = 0`. A nonzero
`ξ₀ ∈ K` is needed: for `K = 0` and `E ≠ 0` the other hypotheses hold with `L = 0`, while the
Kraus blocks all vanish. -/
lemma linearIndependent_krausBlock_of_dense {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] [CompleteSpace L] (π : (K →L[ℂ] K) →⋆ₐ[ℂ] (L →L[ℂ] L))
    (W : H →L[ℂ] L)
    (hmin : (Submodule.span ℂ (Set.range fun p : (K →L[ℂ] K) × H => π p.1 (W p.2))).topologicalClosure
      = ⊤)
    (U : K ⊗[ℂ] E ≃ₗᵢ[ℂ] L) (hU : ∀ B z, π B (U z) = U (B.rTensor E z)) (V : H →L[ℂ] K ⊗[ℂ] E)
    (hV : ∀ ξ, W ξ = U (V ξ)) {ξ₀ : K} (hξ₀ : ξ₀ ≠ 0) (f : OrthonormalBasis κ ℂ E) :
    LinearIndependent ℂ (krausBlock f V) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc a => ?_
  set y : E := ∑ a, star (c a) • f a with hy_def
  have h1 (k : K) (ξ : H) : ⟪k ⊗ₜ[ℂ] y, V ξ⟫_ℂ = 0 := by
    have h := congrArg (fun T : H →L[ℂ] K => ⟪k, T ξ⟫_ℂ) hc
    simp only [sum_apply, smul_apply, inner_sum, inner_smul_right, zero_apply,
      inner_zero_right] at h
    rw [← h]
    simp only [y, tmul_sum, tmul_smul, sum_inner, krausBlock, comp_apply, adjoint_inner_right,
      flip_apply, mkL_apply_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (inner_smul_left (𝕜 := ℂ) (k ⊗ₜ[ℂ] f i) (V ξ) (star (c i))).trans
      (by rw [starRingEnd_apply, star_star])
  have h2 (k : K) (B : K →L[ℂ] K) (ξ : H) : ⟪k ⊗ₜ[ℂ] y, B.rTensor E (V ξ)⟫_ℂ = 0 := by
    rw [← adjoint_inner_left, adjoint_rTensor, rTensor_tmul, h1]
  have h3 : U (ξ₀ ⊗ₜ y) ∈
      (Submodule.span ℂ (Set.range fun p : (K →L[ℂ] K) × H => π p.1 (W p.2)))ᗮ := by
    refine (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨B, ξ⟩, rfl⟩ := hx
      dsimp only
      rw [hV, hU, LinearIsometryEquiv.inner_map_map, h2]
    | zero => exact inner_zero_right _
    | add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]
    | smul r x _ hx => rw [inner_smul_right, hx, mul_zero]
  rw [(Submodule.topologicalClosure_eq_top_iff).1 hmin, Submodule.mem_bot,
    LinearIsometryEquiv.map_eq_zero_iff] at h3
  have hy : y = 0 := by
    have h := congrArg norm h3
    rw [norm_tmul, norm_zero, mul_eq_zero] at h
    exact norm_eq_zero.1 (h.resolve_left (norm_ne_zero_iff.2 hξ₀))
  have h := congrArg (fun v => ⟪f a, v⟫_ℂ) hy
  simp only [y, inner_sum, inner_smul_right, f.inner_eq_ite, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, inner_zero_right] at h
  exact star_eq_zero.1 h

end ContinuousLinearMap

/-! ### Stinespring's theorem -/

namespace CompletelyPositiveMap

/-- **Stinespring's theorem**, converse: `A ↦ tr₂(V A V†)` for `V : H → K ⊗ E` is completely
positive, as the Kraus map of the Kraus blocks of `V`
(`ContinuousLinearMap.traceRight_comp_comp_adjoint`). -/
noncomputable def ofStinespring (V : H →L[ℂ] K ⊗[ℂ] E) : (H →L[ℂ] H) →CP (K →L[ℂ] K) :=
  ofKraus (krausBlock (stdOrthonormalBasis ℂ E) V)

/-- The completely positive map `CompletelyPositiveMap.ofStinespring V` sends `A` to
`tr₂(V A V†)`. -/
@[simp] lemma ofStinespring_apply (V : H →L[ℂ] K ⊗[ℂ] E) (A : H →L[ℂ] H) :
    ofStinespring V A = traceRight K E (V ∘L A ∘L adjoint V) :=
  (traceRight_comp_comp_adjoint (stdOrthonormalBasis ℂ E) V A).symm

/-- **Stinespring's theorem** with linearly independent Kraus blocks: a completely positive map
`φ : B(H) → B(K)` is `φ(A) = tr₂(V A V†)` for some `V : H → K ⊗ ℂᵈ` whose Kraus blocks along the
standard basis of `ℂᵈ` are linearly independent. The operator `V = U† W` comes from the Stinespring
dilation `φ*(B) = W† π(B) W` of the trace dual and the multiplicity decomposition
`π(B) = U (B ⊗ 1) U†` of the representation `π` of `B(K)`; the Kraus blocks are linearly
independent by minimality of the dilation. -/
lemma exists_stinespring_linearIndependent_krausBlock (φ : (H →L[ℂ] H) →CP (K →L[ℂ] K)) :
    ∃ (d : ℕ) (V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ (Fin d)),
      (∀ A, φ A = traceRight K (EuclideanSpace ℂ (Fin d)) (V ∘L A ∘L adjoint V)) ∧
        LinearIndependent ℂ (krausBlock (EuclideanSpace.basisFun (Fin d) ℂ) V) := by
  classical
  rcases subsingleton_or_nontrivial K with hK | hK
  · refine ⟨0, 0, fun A => ?_, linearIndependent_empty_type⟩
    ext x
    exact Subsingleton.elim _ _
  obtain ⟨ξ₀, hξ₀⟩ := exists_norm_eq K zero_le_one
  set ψ := CompletelyPositiveMap.traceDual φ
  have : FiniteDimensional ℂ ψ.Stinespring := FiniteDimensional.completion
  set π := ψ.stinespringStarAlgHom
  set W := ψ.stinespringOperator
  set S := StarAlgHom.multiplicitySpace π ξ₀
  set e := stdOrthonormalBasis ℂ S
  set ιE : EuclideanSpace ℂ (Fin (Module.finrank ℂ S)) →ₗᵢ[ℂ] ψ.Stinespring :=
    S.subtypeₗᵢ.comp e.repr.symm.toLinearIsometry
  have hιE : LinearMap.range ιE.toLinearMap = S := by
    refine le_antisymm ?_ fun y hy => ⟨e.repr ⟨y, hy⟩, by simp [ιE]⟩
    rintro _ ⟨x, rfl⟩
    exact (e.repr.symm x).2
  set U := StarAlgHom.multiplicityEquiv hξ₀ ιE hιE
  set V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ S)) :=
    (U.symm : ψ.Stinespring →L[ℂ] _) ∘L W
  have hW (ξ : H) : W ξ = U (V ξ) := by simp [V]
  have hHeis (B : K →L[ℂ] K) : traceDual φ B = adjoint V ∘L B.rTensor _ ∘L V := by
    have h1 : traceDual φ B = adjoint W ∘L π B ∘L W :=
      ψ.apply_eq_adjoint_comp_stinespringStarAlgHom_comp B
    refine h1.trans ?_
    ext ξ
    have h2 : π B (W ξ) = U (B.rTensor _ (U.symm (W ξ))) := by
      rw [← StarAlgHom.apply_multiplicityEquiv, LinearIsometryEquiv.apply_symm_apply]
    simp only [V, adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
    exact congrArg (adjoint W) h2
  refine ⟨Module.finrank ℂ S, V, (traceDual_eq_iff_traceRight V).1 hHeis, ?_⟩
  refine linearIndependent_krausBlock_of_dense π W ?_ U
    (fun B z => StarAlgHom.apply_multiplicityEquiv hξ₀ ιE hιE B z) V hW (norm_ne_zero_iff.1
      (by rw [hξ₀]; exact one_ne_zero)) _
  exact ψ.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top

/-- **Stinespring's theorem**: a completely positive map `φ : B(H) → B(K)` is
`φ(A) = tr₂(V A V†)` for some `V : H → K ⊗ ℂʳ` with environment of the minimal dimension
`r = rank J_b(φ)` (`ContinuousLinearMap.finrank_range_choi_le_finrank_of_stinespring`), for any
orthonormal basis `b` of `H`. Conversely every such map is completely positive
(`CompletelyPositiveMap.ofStinespring`). -/
theorem exists_stinespring (b : OrthonormalBasis ι ℂ H) (φ : (H →L[ℂ] H) →CP (K →L[ℂ] K)) :
    ∃ V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ
        (Fin (Module.finrank ℂ ((choi b φ).range))),
      ∀ A, φ A = traceRight K (EuclideanSpace ℂ (Fin _)) (V ∘L A ∘L adjoint V) := by
  have h := exists_stinespring_linearIndependent_krausBlock φ
  obtain ⟨d, V, hV, hli⟩ := h
  have hd := (finrank_range_choi_eq_card_iff_linearIndependent_krausBlock b
    (EuclideanSpace.basisFun (Fin d) ℂ) V hV).2 hli
  rw [Fintype.card_fin] at hd
  subst hd
  exact ⟨V, hV⟩

/-- **Stinespring's theorem, Heisenberg picture**: the trace dual of a completely positive map
`φ : B(H) → B(K)` is `φ*(B) = V† (B ⊗ 1) V` for some `V : H → K ⊗ ℂʳ` with environment of the
minimal dimension `r = rank J_b(φ)`
(`ContinuousLinearMap.finrank_range_choi_le_finrank_of_stinespring`): the Schrödinger form
`CompletelyPositiveMap.exists_stinespring` read through `ContinuousLinearMap.traceDual_eq_iff_traceRight`. -/
theorem exists_traceDual_eq_stinespring (b : OrthonormalBasis ι ℂ H)
    (φ : (H →L[ℂ] H) →CP (K →L[ℂ] K)) :
    ∃ V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ
        (Fin (Module.finrank ℂ ((choi b φ).range))),
      ∀ B : K →L[ℂ] K, ContinuousLinearMap.traceDual φ B = adjoint V ∘L B.rTensor _ ∘L V := by
  have h := exists_stinespring b φ
  obtain ⟨V, hV⟩ := h
  exact ⟨V, (traceDual_eq_iff_traceRight V).2 hV⟩

/-- A completely positive map `φ : B(H) → B(K)` has a Kraus representation `φ(A) = Σₐ Tₐ A Tₐ†`
with exactly `rank J_b(φ)` operators, the minimal number
(`ContinuousLinearMap.finrank_range_choi_le_card`): the Kraus blocks of the Stinespring operator
(`CompletelyPositiveMap.exists_stinespring`). -/
lemma exists_kraus_finrank_range_choi (b : OrthonormalBasis ι ℂ H)
    (φ : (H →L[ℂ] H) →CP (K →L[ℂ] K)) :
    ∃ T : Fin (Module.finrank ℂ ((choi b φ).range)) →
        H →L[ℂ] K,
      ∀ A, φ A = ∑ a, T a ∘L A ∘L adjoint (T a) := by
  have h := exists_stinespring b φ
  obtain ⟨V, hV⟩ := h
  exact ⟨krausBlock (EuclideanSpace.basisFun _ ℂ) V, fun A => by
    rw [hV, traceRight_comp_comp_adjoint (EuclideanSpace.basisFun _ ℂ)]⟩

/-- The rank of the Choi operator of a completely positive map does not depend on the orthonormal
basis: each is the minimal number of Kraus operators (`CompletelyPositiveMap.exists_kraus_finrank_range_choi`,
`ContinuousLinearMap.finrank_range_choi_le_card`). -/
lemma finrank_range_choi_congr {ι' : Type*} [Fintype ι'] (b : OrthonormalBasis ι ℂ H)
    (b' : OrthonormalBasis ι' ℂ H) (φ : (H →L[ℂ] H) →CP (K →L[ℂ] K)) :
    Module.finrank ℂ ((choi b φ).range) =
      Module.finrank ℂ ((choi b' φ).range) := by
  have h := exists_kraus_finrank_range_choi b φ
  have h' := exists_kraus_finrank_range_choi b' φ
  obtain ⟨T, hT⟩ := h
  obtain ⟨T', hT'⟩ := h'
  refine le_antisymm ?_ ?_
  · simpa using finrank_range_choi_le_card b hT'
  · simpa using finrank_range_choi_le_card b' hT

/-- **Stinespring's theorem**: a linear map `Φ : B(H) → B(K)` is completely positive iff
`Φ(A) = tr₂(V A V†)` for some `V : H → K ⊗ ℂʳ` with `r = rank J_b(Φ)`. -/
theorem exists_coe_eq_iff_exists_stinespring (b : OrthonormalBasis ι ℂ H)
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) :
    (∃ φ : (H →L[ℂ] H) →CP (K →L[ℂ] K), (φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) = Φ) ↔
      ∃ V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ
          (Fin (Module.finrank ℂ ((choi b Φ).range))),
        ∀ A, Φ A = traceRight K (EuclideanSpace ℂ (Fin _)) (V ∘L A ∘L adjoint V) :=
  ⟨by rintro ⟨φ, rfl⟩; exact exists_stinespring b φ,
    fun h => by
      obtain ⟨V, hV⟩ := h
      exact ⟨ofStinespring V, LinearMap.ext fun A => by simp [hV]⟩⟩

/-- **Kraus representation of completely positive maps**: a linear map `Φ : B(H) → B(K)` is
completely positive iff `Φ(A) = Σₐ Tₐ A Tₐ†` with `rank J_b(Φ)` operators. -/
theorem exists_coe_eq_iff_exists_kraus_finrank_range_choi (b : OrthonormalBasis ι ℂ H)
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) :
    (∃ φ : (H →L[ℂ] H) →CP (K →L[ℂ] K), (φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) = Φ) ↔
      ∃ T : Fin (Module.finrank ℂ ((choi b Φ).range)) →
          H →L[ℂ] K,
        ∀ A, Φ A = ∑ a, T a ∘L A ∘L adjoint (T a) :=
  ⟨by rintro ⟨φ, rfl⟩; exact exists_kraus_finrank_range_choi b φ,
    fun h => by
      obtain ⟨T, hT⟩ := h
      exact ⟨ofKraus T, LinearMap.ext fun A => (hT A).symm⟩⟩

end CompletelyPositiveMap

/-! ### Completely positive trace-preserving maps -/

namespace CPTPMap

/-- **Stinespring's theorem** for CPTP maps, converse: `A ↦ tr₂(V A V†)` for an isometry
`V : H → K ⊗ E`, `V† V = 1`, is a CPTP map: `tr(tr₂(V A V†)) = tr(A V† V) = tr A`. -/
noncomputable def ofStinespring (V : H →L[ℂ] K ⊗[ℂ] E) (hV : adjoint V ∘L V = 1) :
    CPTPMap H K where
  toCompletelyPositiveMap := CompletelyPositiveMap.ofStinespring V
  isTracePreserving' A := by
    rw [CompletelyPositiveMap.ofStinespring_apply, trace_traceRight, trace_comp_comm', comp_assoc,
      hV, ← mul_def, mul_one]

/-- The CPTP map `CPTPMap.ofStinespring V hV` sends `A` to `tr₂(V A V†)`. -/
@[simp] lemma ofStinespring_apply (V : H →L[ℂ] K ⊗[ℂ] E) (hV : adjoint V ∘L V = 1)
    (A : H →L[ℂ] H) : ofStinespring V hV A = ContinuousLinearMap.traceRight K E (V ∘L A ∘L adjoint V) :=
  CompletelyPositiveMap.ofStinespring_apply V A

/-- **Stinespring's theorem, Heisenberg picture**, for CPTP maps: the trace dual of a
CPTP map `Φ : B(H) → B(K)` is the unital map `Φ*(B) = V† (B ⊗ 1) V` for an isometry
`V : H → K ⊗ ℂʳ`, `V† V = 1`, with `r = rank J_b(Φ)`. The isometry is
`V† V = V† (1 ⊗ 1) V = Φ*(1) = 1` (`CPTPMap.traceDual_one`). -/
theorem exists_traceDual_eq_stinespring (b : OrthonormalBasis ι ℂ H) (Φ : CPTPMap H K) :
    ∃ V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ
        (Fin (Module.finrank ℂ ((choi b Φ).range))),
      adjoint V ∘L V = 1 ∧
        ∀ B : K →L[ℂ] K, ContinuousLinearMap.traceDual Φ B = adjoint V ∘L B.rTensor _ ∘L V := by
  have h := CompletelyPositiveMap.exists_traceDual_eq_stinespring b Φ.toCompletelyPositiveMap
  obtain ⟨V, hV⟩ := h
  refine ⟨V, ?_, hV⟩
  have h1 : ContinuousLinearMap.traceDual Φ 1 = adjoint V ∘L (1 : K →L[ℂ] K).rTensor _ ∘L V :=
    hV 1
  simp only [traceDual_one Φ, rTensor_one] at h1
  simp only [one_def, id_comp] at h1
  exact h1.symm

/-- **Stinespring's theorem** for CPTP maps: a CPTP map `Φ : B(H) → B(K)` is
`Φ(A) = tr₂(V A V†)` for an isometry `V : H → K ⊗ ℂʳ`, `V† V = 1`, with `r = rank J_b(Φ)`: the
Heisenberg form `CPTPMap.exists_traceDual_eq_stinespring` read through
`ContinuousLinearMap.traceDual_eq_iff_traceRight`. -/
theorem exists_stinespring (b : OrthonormalBasis ι ℂ H) (Φ : CPTPMap H K) :
    ∃ V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ
        (Fin (Module.finrank ℂ ((choi b Φ).range))),
      adjoint V ∘L V = 1 ∧ ∀ A, Φ A = ContinuousLinearMap.traceRight K (EuclideanSpace ℂ (Fin _))
        (V ∘L A ∘L adjoint V) := by
  have h := exists_traceDual_eq_stinespring b Φ
  obtain ⟨V, hVV, hV⟩ := h
  exact ⟨V, hVV, (traceDual_eq_iff_traceRight V).1 hV⟩

/-- A CPTP map `Φ : B(H) → B(K)` has a Kraus representation `Φ(A) = Σₐ Tₐ A Tₐ†` with
exactly `rank J_b(Φ)` operators, satisfying the completeness relation `Σₐ Tₐ† Tₐ = 1`
(`isTracePreserving_iff_sum_adjoint_comp_eq_one`). -/
lemma exists_kraus_finrank_range_choi (b : OrthonormalBasis ι ℂ H) (Φ : CPTPMap H K) :
    ∃ T : Fin (Module.finrank ℂ ((choi b Φ).range)) →
        H →L[ℂ] K,
      (∀ A, Φ A = ∑ a, T a ∘L A ∘L adjoint (T a)) ∧ ∑ a, adjoint (T a) ∘L T a = 1 := by
  have h := CompletelyPositiveMap.exists_kraus_finrank_range_choi b Φ.toCompletelyPositiveMap
  obtain ⟨T, hT⟩ := h
  exact ⟨T, hT, (isTracePreserving_iff_sum_adjoint_comp_eq_one hT).1 (isTracePreserving Φ)⟩

/-- **Stinespring's theorem** for CPTP maps: a linear map `Φ : B(H) → B(K)` is a CPTP map iff
`Φ(A) = tr₂(V A V†)` for an isometry `V : H → K ⊗ ℂʳ`, `V† V = 1`, with
`r = rank J_b(Φ)`. -/
theorem exists_coe_eq_iff_exists_stinespring (b : OrthonormalBasis ι ℂ H)
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) :
    (∃ Ψ : CPTPMap H K, (Ψ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) = Φ) ↔
      ∃ V : H →L[ℂ] K ⊗[ℂ] EuclideanSpace ℂ
          (Fin (Module.finrank ℂ ((choi b Φ).range))),
        adjoint V ∘L V = 1 ∧ ∀ A, Φ A = ContinuousLinearMap.traceRight K (EuclideanSpace ℂ (Fin _))
        (V ∘L A ∘L adjoint V) :=
  ⟨by rintro ⟨Ψ, rfl⟩; exact exists_stinespring b Ψ,
    fun h => by
      obtain ⟨V, hVV, hV⟩ := h
      exact ⟨ofStinespring V hVV, LinearMap.ext fun A => by simp [hV]⟩⟩

/-- **Kraus representation of CPTP maps** (Nielsen–Chuang, Theorem 8.1, for the
trace-preserving case `Σₐ Tₐ† Tₐ = 1`): a linear map
`Φ : B(H) → B(K)` is a CPTP map iff `Φ(A) = Σₐ Tₐ A Tₐ†` with `Σₐ Tₐ† Tₐ = 1`, and then
with `rank J_b(Φ)` operators. -/
theorem exists_coe_eq_iff_exists_kraus_finrank_range_choi (b : OrthonormalBasis ι ℂ H)
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) :
    (∃ Ψ : CPTPMap H K, (Ψ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) = Φ) ↔
      ∃ T : Fin (Module.finrank ℂ ((choi b Φ).range)) →
          H →L[ℂ] K,
        (∀ A, Φ A = ∑ a, T a ∘L A ∘L adjoint (T a)) ∧ ∑ a, adjoint (T a) ∘L T a = 1 :=
  ⟨by rintro ⟨Ψ, rfl⟩; exact exists_kraus_finrank_range_choi b Ψ,
    fun h => by
      obtain ⟨T, hT, hTT⟩ := h
      exact ⟨ofKraus T hTT, LinearMap.ext fun A => (hT A).symm⟩⟩

end CPTPMap
