/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Entropy.Umegaki.Monotonicity
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct
public import QuantumSystem.ForMathlib.Data.EReal.BigOperators

/-!
# Joint convexity of Umegaki's relative entropy

Let `H` be a finite-dimensional complex Hilbert space. Umegaki's relative entropy is **jointly
convex**: for positive functionals `ψᵢ, φᵢ` on `B(H)` and weights `wᵢ ≥ 0`,
`D(Σᵢ wᵢ ψᵢ ‖ Σᵢ wᵢ φᵢ) ≤ Σᵢ wᵢ D(ψᵢ ‖ φᵢ)` (`umegakiEntropy_jointly_convex`);
the weights need not sum to one, `D` being positively homogeneous.

## Proof (Lindblad, Uhlmann)

Joint convexity follows from three properties of `D`: monotonicity, additivity on direct sums, and
positive homogeneity. Adjoin a classical register `ℂ^ι` with orthonormal basis `eᵢ`, and let
`Vᵢ : H → ℂ^ι ⊗ H`, `h ↦ eᵢ ⊗ h`, insert `H` as the `i`-th block. The **block-diagonal functional**
`⊕ᵢ χᵢ : Z ↦ Σᵢ χᵢ(Vᵢ† Z Vᵢ)` on `B(ℂ^ι ⊗ H)` (`PositiveLinearMap.blockDiagonal`) has the
block-diagonal density `Σᵢ Vᵢ ρ_{χᵢ} Vᵢ†`, so its logarithm is block diagonal too and Umegaki's
formula splits: `D(⊕ χᵢ ‖ ⊕ θᵢ) = Σᵢ D(χᵢ ‖ θᵢ)` (`umegakiEntropy_blockDiagonal`).
Its restriction along the unital `⋆`-homomorphism `A ↦ 1 ⊗ A` is `Σᵢ χᵢ`, so the data-processing
inequality gives `D(Σᵢ χᵢ ‖ Σᵢ θᵢ) ≤ Σᵢ D(χᵢ ‖ θᵢ)` (`umegakiEntropy_sum_le`); with
`χᵢ = wᵢ ψᵢ`, `θᵢ = wᵢ φᵢ` this is joint convexity.

## Main definitions

* `PositiveLinearMap.blockDiagonal χ` — the block-diagonal functional `Z ↦ Σᵢ χᵢ(Vᵢ† Z Vᵢ)` on
  `B(ℂ^ι ⊗ H)`.

## Main results

* `umegakiEntropy_blockDiagonal` — additivity on direct sums.
* `umegakiEntropy_sum_le` — subadditivity `D(Σᵢ χᵢ ‖ Σᵢ θᵢ) ≤ Σᵢ D(χᵢ ‖ θᵢ)`.
* `umegakiEntropy_jointly_convex` — joint convexity for finite families;
  `umegakiEntropy_smul_add_smul_le` — the two-point form.

## TODO

* Prove joint convexity of Araki's relative entropy `VonNeumannAlgebra.arakiEntropy` for normal
  functionals on an arbitrary von Neumann algebra `M`, by the same three steps on
  `M ⊗ ℓ^∞(ι)`; it needs additivity of Araki's entropy on direct sums, i.e. the decomposition of
  the relative modular operator of a direct sum. The present theorem would then be its case
  `M = 𝓑(H)`.

## References

* G. Lindblad, *Expectations and entropy inequalities for finite quantum systems*, Comm. Math.
  Phys. 39 (1974), 111–119.
* A. Uhlmann, *Relative entropy and the Wigner–Yanase–Dyson–Lieb concavity in an interpolation
  theory*, Comm. Math. Phys. 54 (1977), 21–32.
-/

@[expose] public section

open ContinuousLinearMap TensorProduct
open scoped InnerProductSpace ComplexOrder QuantumInfo NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  {ι : Type*} [Fintype ι]

/-- The insertion `h ↦ eᵢ ⊗ h` of `H` as the `i`-th block of `ℂ^ι ⊗ H`. -/
local notation "𝕍" i => TensorProduct.mkL ℂ (EuclideanSpace ℂ ι) H (EuclideanSpace.basisFun ι ℂ i)

/-- The insertions are isometries: `Vᵢ† Vᵢ = 1`. -/
private lemma adjoint_ins_comp_ins_self (i : ι) : adjoint (𝕍 i) ∘L (𝕍 i) = 1 := by
  rw [adjoint_mkL_comp_mkL, (EuclideanSpace.basisFun ι ℂ).inner_eq_one, one_smul]

/-- The blocks are orthogonal: `Vᵢ† Vⱼ = 0` for `i ≠ j`. -/
private lemma adjoint_ins_comp_ins_of_ne {i j : ι} (h : i ≠ j) : adjoint (𝕍 i) ∘L (𝕍 j) = 0 := by
  rw [adjoint_mkL_comp_mkL, (EuclideanSpace.basisFun ι ℂ).orthonormal.2 h, zero_smul]

private lemma adjoint_ins_comp_ins_self_comp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (i : ι) (X : E →L[ℂ] H) : adjoint (𝕍 i) ∘L (𝕍 i) ∘L X = X := by
  rw [← comp_assoc, adjoint_ins_comp_ins_self, one_def, id_comp]

private lemma adjoint_ins_comp_ins_comp_of_ne {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {i j : ι} (h : i ≠ j) (X : E →L[ℂ] H) :
    adjoint (𝕍 i) ∘L (𝕍 j) ∘L X = 0 := by
  rw [← comp_assoc, adjoint_ins_comp_ins_of_ne h, zero_comp]

/-- `(Vᵢ A Vᵢ†)⋆ (Vᵢ A Vᵢ†) = Vᵢ (A⋆ A) Vᵢ†`. -/
private lemma star_ins_mul_ins (i : ι) (A : H →L[ℂ] H) :
    star ((𝕍 i) ∘L A ∘L adjoint (𝕍 i)) * ((𝕍 i) ∘L A ∘L adjoint (𝕍 i)) =
      (𝕍 i) ∘L (star A * A) ∘L adjoint (𝕍 i) := by
  simp only [star_eq_adjoint, mul_def, adjoint_comp, adjoint_adjoint, comp_assoc,
    adjoint_ins_comp_ins_self_comp]

namespace PositiveLinearMap

/-- The **block-diagonal functional** `⊕ᵢ χᵢ : Z ↦ Σᵢ χᵢ(Vᵢ† Z Vᵢ)` on `B(ℂ^ι ⊗ H)`, reading off
the diagonal blocks of `Z` along the insertions `Vᵢ : h ↦ eᵢ ⊗ h`; its density is
`Σᵢ Vᵢ ρ_{χᵢ} Vᵢ†` (`PositiveLinearMap.density_blockDiagonal`). It is positive since each
compression `Z ↦ Vᵢ† Z Vᵢ` is. For states `χᵢ = pᵢ ωᵢ` it is the classical–quantum state
`Σᵢ pᵢ |i⟩⟨i| ⊗ ρ_{ωᵢ}`. -/
noncomputable def blockDiagonal (χ : ι → (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    (EuclideanSpace ℂ ι ⊗[ℂ] H →L[ℂ] EuclideanSpace ℂ ι ⊗[ℂ] H) →ₚ[ℂ] ℂ :=
  .mk₀
    { toFun := fun Z => ∑ i, χ i (adjoint (𝕍 i) ∘L Z ∘L (𝕍 i))
      map_add' := fun Z W => by
        simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, Finset.sum_add_distrib]
      map_smul' := fun c Z => by simp [Finset.mul_sum] }
    fun Z hZ => Finset.sum_nonneg fun i _ => (χ i).map_nonneg
      (nonneg_iff_isPositive.2 ((nonneg_iff_isPositive.1 hZ).adjoint_conj _))

variable (χ : ι → (H →L[ℂ] H) →ₚ[ℂ] ℂ)

/-- The block-diagonal functional evaluates as `Σᵢ χᵢ(Vᵢ† Z Vᵢ)`. -/
theorem blockDiagonal_apply (Z : EuclideanSpace ℂ ι ⊗[ℂ] H →L[ℂ] EuclideanSpace ℂ ι ⊗[ℂ] H) :
    blockDiagonal χ Z = ∑ i, χ i (adjoint (𝕍 i) ∘L Z ∘L (𝕍 i)) :=
  rfl

/-- On the `i`-th block, `⊕ⱼ χⱼ (Vᵢ B Vᵢ†) = χᵢ(B)`. -/
theorem blockDiagonal_apply_ins (i : ι) (B : H →L[ℂ] H) :
    blockDiagonal χ ((𝕍 i) ∘L B ∘L adjoint (𝕍 i)) = χ i B := by
  rw [blockDiagonal_apply]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [adjoint_ins_comp_ins_comp_of_ne hj, map_zero])
      (by simp), adjoint_ins_comp_ins_self_comp, adjoint_ins_comp_ins_self,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

/-- **The restriction to `1 ⊗ B(H)`** of the block-diagonal functional is `Σᵢ χᵢ`:
`Vᵢ† (1 ⊗ A) Vᵢ = A`. -/
theorem blockDiagonal_comp_lTensor :
    (blockDiagonal χ).comp (.ofClass (lTensorStarAlgHom ℂ H (EuclideanSpace ℂ ι))) = ∑ i, χ i := by
  refine PositiveLinearMap.ext fun A => ?_
  change blockDiagonal χ (A.lTensor (EuclideanSpace ℂ ι)) = _
  rw [blockDiagonal_apply]
  simp only [lTensor_comp_mkL, adjoint_ins_comp_ins_self_comp]
  simp

/-- **The density of the block-diagonal functional is block diagonal**: `Σᵢ Vᵢ ρ_{χᵢ} Vᵢ†`. -/
theorem density_blockDiagonal :
    density (blockDiagonal χ) = ∑ i, (𝕍 i) ∘L density (χ i) ∘L adjoint (𝕍 i) := by
  rw [eq_comm, eq_density_iff]
  intro Z
  rw [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.toLinearMap_sum, map_sum, blockDiagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_assoc]
  rw [← trace_comp_comm' (𝕍 i)]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [trace_density_comp]

/-- The block-diagonal density intertwines the insertions: `ρ_{⊕χ} Vᵢ = Vᵢ ρ_{χᵢ}`. -/
theorem density_blockDiagonal_comp (i : ι) :
    density (blockDiagonal χ) ∘L (𝕍 i) = (𝕍 i) ∘L density (χ i) := by
  rw [density_blockDiagonal, ContinuousLinearMap.finsetSum_comp]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [adjoint_ins_comp_ins_of_ne hj, ContinuousLinearMap.comp_zero,
        ContinuousLinearMap.comp_zero]) (by simp), adjoint_ins_comp_ins_self,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

/-- The real functional calculus of the block-diagonal density is block diagonal:
`Vᵢ† f(ρ_{⊕χ}) Vᵢ = f(ρ_{χᵢ})`. -/
theorem adjoint_ins_comp_cfc_density_blockDiagonal (f : ℝ → ℝ) (i : ι) :
    adjoint (𝕍 i) ∘L cfc f (density (blockDiagonal χ)) ∘L (𝕍 i) = cfc f (density (χ i)) := by
  have ha := IsSelfAdjoint.of_nonneg (density_nonneg (χ i))
  have hb := IsSelfAdjoint.of_nonneg (density_nonneg (blockDiagonal χ))
  rw [← comp_cfc_eq_cfc_comp_real ha hb (density_blockDiagonal_comp χ i).symm
      ((finite_spectrum_real ha).continuousOn f) ((finite_spectrum_real hb).continuousOn f),
    adjoint_ins_comp_ins_self_comp]

/-- `Vⱼ† Z⋆ Z Vⱼ = Σₖ Aₖⱼ⋆ Aₖⱼ` for the blocks `Aₖⱼ = Vₖ† Z Vⱼ` of `Z`
(`TensorProduct.sum_mkL_comp_adjoint_mkL`). -/
private lemma adjoint_ins_comp_star_mul_self_comp_ins
    (Z : EuclideanSpace ℂ ι ⊗[ℂ] H →L[ℂ] EuclideanSpace ℂ ι ⊗[ℂ] H) (j : ι) :
    adjoint (𝕍 j) ∘L (star Z * Z) ∘L (𝕍 j) =
      ∑ k, star (adjoint (𝕍 k) ∘L Z ∘L (𝕍 j)) * (adjoint (𝕍 k) ∘L Z ∘L (𝕍 j)) := by
  have h1 : ∑ k, (𝕍 k) ∘L adjoint (𝕍 k) = 1 :=
    sum_mkL_comp_adjoint_mkL (F := H) (EuclideanSpace.basisFun ι ℂ)
  calc adjoint (𝕍 j) ∘L (star Z * Z) ∘L (𝕍 j)
      = adjoint (𝕍 j) ∘L adjoint Z ∘L (∑ k, (𝕍 k) ∘L adjoint (𝕍 k)) ∘L Z ∘L (𝕍 j) := by
        rw [h1, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
          ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
          ContinuousLinearMap.comp_assoc]
    _ = _ := by
        rw [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_finsetSum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
          ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
          ContinuousLinearMap.comp_assoc]

/-- **The support condition splits over the blocks**: the null ideal of `⊕ θ` lies in that of
`⊕ χ` iff the null ideal of each `θᵢ` lies in that of `χᵢ`. -/
theorem blockDiagonal_null_imp_iff (θ : ι → (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    (∀ Z, blockDiagonal θ (star Z * Z) = 0 → blockDiagonal χ (star Z * Z) = 0) ↔
      ∀ i, ∀ A : H →L[ℂ] H, θ i (star A * A) = 0 → χ i (star A * A) = 0 := by
  refine ⟨fun h i A hA => ?_, fun h Z hZ0 => ?_⟩
  · have := h ((𝕍 i) ∘L A ∘L adjoint (𝕍 i))
      (by rw [star_ins_mul_ins, blockDiagonal_apply_ins]; exact hA)
    rwa [star_ins_mul_ins, blockDiagonal_apply_ins] at this
  · rw [blockDiagonal_apply] at hZ0 ⊢
    simp_rw [adjoint_ins_comp_star_mul_self_comp_ins, map_sum] at hZ0 ⊢
    have hnn : ∀ j k, 0 ≤ θ j (star (adjoint (𝕍 k) ∘L Z ∘L (𝕍 j)) *
        (adjoint (𝕍 k) ∘L Z ∘L (𝕍 j))) := fun j k => (θ j).map_nonneg (star_mul_self_nonneg _)
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => h j _ ?_
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hnn j k).mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => Finset.sum_nonneg fun k _ => hnn j k).mp hZ0 j
        (Finset.mem_univ j)) k (Finset.mem_univ k)

end PositiveLinearMap

open PositiveLinearMap

variable (χ : ι → (H →L[ℂ] H) →ₚ[ℂ] ℂ)

/-- **Additivity on direct sums**: `D(⊕ᵢ χᵢ ‖ ⊕ᵢ θᵢ) = Σᵢ D(χᵢ ‖ θᵢ)`. The logarithms of the
block-diagonal densities are block diagonal
(`PositiveLinearMap.adjoint_ins_comp_cfc_density_blockDiagonal`), so Umegaki's formula
`Re ψ(log ρ_ψ - log ρ_φ)` splits over the blocks; if one block violates the support condition,
both sides are `+∞`. -/
theorem umegakiEntropy_blockDiagonal (θ : ι → (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    D(blockDiagonal χ ∥ blockDiagonal θ) = ∑ i, D(χ i ∥ θ i) := by
  by_cases hs : ∀ i, ∀ A : H →L[ℂ] H, θ i (star A * A) = 0 → χ i (star A * A) = 0
  · rw [umegakiEntropy_eq_re_apply ((blockDiagonal_null_imp_iff χ θ).mpr hs)]
    simp_rw [umegakiEntropy_eq_re_apply (hs _)]
    rw [← EReal.coe_finsetSum, blockDiagonal_apply, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, CFC.log, CFC.log,
      adjoint_ins_comp_cfc_density_blockDiagonal χ,
      adjoint_ins_comp_cfc_density_blockDiagonal θ]
    rfl
  · push Not at hs
    obtain ⟨i, A, hθ, hχ⟩ := hs
    rw [umegakiEntropy_eq_top_of_apply_star_mul_self ((𝕍 i) ∘L A ∘L adjoint (𝕍 i))
      (by rw [star_ins_mul_ins, blockDiagonal_apply_ins]; exact hθ)
      (by rw [star_ins_mul_ins, blockDiagonal_apply_ins]; exact hχ)]
    exact (EReal.finsetSum_eq_top (fun j _ => umegakiEntropy_ne_bot _ _) (Finset.mem_univ i)
      (umegakiEntropy_eq_top_of_apply_star_mul_self A hθ hχ)).symm

/-- **Subadditivity**: `D(Σᵢ χᵢ ‖ Σᵢ θᵢ) ≤ Σᵢ D(χᵢ ‖ θᵢ)`. The sums are the restrictions of the
block-diagonal functionals along the unital `⋆`-homomorphism `A ↦ 1 ⊗ A`
(`PositiveLinearMap.blockDiagonal_comp_lTensor`), so this is the data-processing inequality
followed by additivity (`umegakiEntropy_blockDiagonal`). -/
theorem umegakiEntropy_sum_le (θ : ι → (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    D(∑ i, χ i ∥ ∑ i, θ i) ≤ ∑ i, D(χ i ∥ θ i) := by
  rw [← umegakiEntropy_blockDiagonal]
  exact umegakiEntropy_comp_le (lTensorStarAlgHom ℂ H (EuclideanSpace ℂ ι)) (map_one _)
    (fun A => (DFunLike.congr_fun (blockDiagonal_comp_lTensor χ) A).symm)
    (fun A => (DFunLike.congr_fun (blockDiagonal_comp_lTensor θ) A).symm)

/-- **Joint convexity** of Umegaki's relative entropy: for positive functionals `ψᵢ, φᵢ` on `B(H)`
and weights `wᵢ ≥ 0`, `D(Σᵢ wᵢ ψᵢ ‖ Σᵢ wᵢ φᵢ) ≤ Σᵢ wᵢ D(ψᵢ ‖ φᵢ)`. The weights need not sum to
one. -/
theorem umegakiEntropy_jointly_convex {κ : Type*} (s : Finset κ) (w : κ → ℝ≥0)
    (ψ φ : κ → (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    D(∑ i ∈ s, w i • ψ i ∥ ∑ i ∈ s, w i • φ i) ≤ ∑ i ∈ s, ((w i : ℝ) : EReal) * D(ψ i ∥ φ i) := by
  classical
  have h := umegakiEntropy_sum_le (ι := s) (fun i => w i • ψ i) (fun i => w i • φ i)
  rw [Finset.sum_coe_sort s (fun i => w i • ψ i), Finset.sum_coe_sort s (fun i => w i • φ i)]
    at h
  refine h.trans_eq ?_
  rw [← Finset.sum_coe_sort s (fun i => ((w i : ℝ) : EReal) * D(ψ i ∥ φ i))]
  simp_rw [umegakiEntropy_smul]

/-- **Joint convexity**, two-point form: `D(a ψ₁ + b ψ₂ ‖ a φ₁ + b φ₂) ≤ a D(ψ₁ ‖ φ₁) + b D(ψ₂ ‖ φ₂)`
for `a, b ≥ 0`, in particular for `b = 1 - a`. -/
theorem umegakiEntropy_smul_add_smul_le (a b : ℝ≥0) (ψ₁ ψ₂ φ₁ φ₂ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) :
    D(a • ψ₁ + b • ψ₂ ∥ a • φ₁ + b • φ₂) ≤
      ((a : ℝ) : EReal) * D(ψ₁ ∥ φ₁) + ((b : ℝ) : EReal) * D(ψ₂ ∥ φ₂) := by
  have h := umegakiEntropy_jointly_convex Finset.univ ![a, b] ![ψ₁, ψ₂] ![φ₁, φ₂]
  simpa [Fin.sum_univ_two] using h
