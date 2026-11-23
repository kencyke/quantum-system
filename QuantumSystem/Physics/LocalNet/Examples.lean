/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Circle
public import QuantumSystem.Physics.LocalNet.InfiniteRegion
public import QuantumSystem.Physics.LocalNet.TensorNet

/-!
# Quantum spin systems as local nets

The local-net interfaces are inhabited here by the quantum spin system: spins with `n` levels on
the sites of a lattice, the local algebra of a finite region `Λ` being `⨂_{x ∈ Λ} B(ℂⁿ)`
(`GradedLocalNet.Examples.quantumSpinSystem`, the tensor product net `GradedLocalNet.tensorNet`).

* **Regions of the integer chain.** Under the metric proper containment of width `1`
  (`ProperContainment.ofCThickeningFinset ℤ 1`, `ProperContainment.ofCThickening ℤ 1`), the site
  `{0}` is properly contained in `{-2, …, 2}` (`GradedLocalNet.Examples.properlyContained_singleton`),
  touching regions are not (`GradedLocalNet.Examples.not_properlyContained_touching`), and the same holds
  for half-chains (`GradedLocalNet.Examples.Iic_properlyContained_Iic_two`,
  `GradedLocalNet.Examples.not_Iic_properlyContained_Iic_one`).
* **The split property on finite regions.** The quantum spin system has the split property in its
  universal representation, under any proper containment
  (`GradedLocalNet.Examples.quantumSpinSystem_splitProperty`), and a single site of the chain splits from
  the half-chain to its right (`GradedLocalNet.Examples.quantumSpinChain_isSplitPair_singleton_Ici`). Both
  hold because the algebra of a finite region is a finite-dimensional factor
  (`GradedLocalNet.splitProperty_of_finiteDimensional`); they say nothing about pairs of infinite regions.
* **Translations.** `GradedLocalNet.Examples.translation v` shifts the sites of the chain by `v`, moving the
  regions (`GradedLocalNet.Examples.translation_σ_singleton`) and their algebras along.
* **An on-site `U(1)` symmetry.** `GradedLocalNet.Examples.spinChainRotation` is the circle acting on every
  spin by conjugation with `diag(1, z, …, z^{n-1})`, a C⋆-dynamical system on the quasi-local
  algebra over a group that is not discrete (`GradedLocalNet.onSiteDynamicalSystem`). For `n ≥ 2` it acts
  non-trivially: the rotation by `-1` reverses the matrix unit `|0⟩⟨1|` at the site `0`
  (`GradedLocalNet.Examples.spinChainRotation_neg_one_ne`).

## What is not inhabited here

No net here refutes `VonNeumannNet.SplitProperty`, and no state here inhabits or refutes
`GradedLocalNet.HasHalfChainSplit`: on finite regions the quantum spin system splits in every unital
representation, and the half-chain split property of a state on the spin chain needs a
representation of the quasi-local algebra on an infinite tensor product, which is not built. The
refuter `VonNeumannAlgebra.not_isSplitInclusion_multiplicationAlgebra_count` is at the level of a
single inclusion. No graded-local net that is not local is built here either.
-/

@[expose] public section

open scoped CausalOrthogonality ProperContainment VonNeumannAlgebra TensorProduct
  PiMinTensorProduct

namespace GradedLocalNet.Examples

/-! ### Regions of the integer chain -/

/-- The closed `1`-thickening of the site `0` of the integer chain is `{-1, 0, 1}`. -/
lemma cthickening_one_singleton_zero : Metric.cthickening 1 ({0} : Set ℤ) = Set.Icc (-1) 1 := by
  rw [Metric.cthickening_singleton _ zero_le_one, Int.closedBall_eq_Icc]
  norm_num

/-- **A site is properly contained in a region surrounding it**: under the metric proper
containment of width `1`, `{0} ⋐ {-2, -1, 0, 1, 2}`, the thickening `{-1, 0, 1}` being a strict
subset. So `⋐` relates a genuine pair of finite regions. -/
theorem properlyContained_singleton :
    letI := ProperContainment.ofCThickeningFinset ℤ ⟨1, one_pos⟩
    ({0} : Finset ℤ) ⋐ {-2, -1, 0, 1, 2} := by
  change Metric.cthickening 1 ((({0} : Finset ℤ)) : Set ℤ) < ((({-2, -1, 0, 1, 2} : Finset ℤ)) : Set ℤ)
  rw [Finset.coe_singleton, cthickening_one_singleton_zero, ← Finset.coe_Icc, Finset.coe_ssubset]
  decide

/-- **Touching regions are not properly contained**: `{0} ⋐ {0, 1}` fails, since the thickening of
`{0}` contains the neighbour `-1`. -/
theorem not_properlyContained_touching :
    letI := ProperContainment.ofCThickeningFinset ℤ ⟨1, one_pos⟩
    ¬ ({0} : Finset ℤ) ⋐ {0, 1} := fun h => by
  have h' : Metric.cthickening 1 ((({0} : Finset ℤ)) : Set ℤ) < ((({0, 1} : Finset ℤ)) : Set ℤ) := h
  rw [Finset.coe_singleton, cthickening_one_singleton_zero] at h'
  have := h'.le (show (-1 : ℤ) ∈ Set.Icc (-1) 1 by norm_num)
  simp at this

/-- **The closed `1`-thickening of the left half-chain `(-∞, 0]` is `(-∞, 1]`.** -/
lemma cthickening_one_Iic : Metric.cthickening 1 (Set.Iic (0 : ℤ)) = Set.Iic 1 := by
  refine subset_antisymm (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 <|
      Metric.cthickening_subset_iUnion_closedBall_of_lt (Set.Iic (0 : ℤ))
        (δ := 1) (δ' := 3 / 2) (by norm_num) (by norm_num) hx
    rw [Metric.mem_closedBall, Int.dist_eq] at hxy
    refine Set.mem_Iic.2 (not_lt.1 fun hlt => ?_)
    have h2 : (2 : ℤ) ≤ |x - y| := by rw [abs_of_nonneg (by grind)]; grind
    have : (2 : ℝ) ≤ ((|x - y| : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith
  · rcases le_or_gt x 0 with h | h
    · exact Metric.self_subset_cthickening _ h
    · obtain rfl : x = 1 := le_antisymm hx h
      exact Metric.mem_cthickening_of_dist_le 1 0 1 _ (Set.mem_Iic.2 le_rfl)
        (by simp)

/-- **A half-chain is properly contained in a larger half-chain**: under the metric proper
containment of width `1`, `(-∞, 0] ⋐ (-∞, 2]`, the site `1` being the buffer and `2` the collar. -/
theorem Iic_properlyContained_Iic_two :
    letI := ProperContainment.ofCThickening ℤ ⟨1, one_pos⟩
    Set.Iic (0 : ℤ) ⋐ Set.Iic 2 := by
  change Metric.cthickening 1 (Set.Iic (0 : ℤ)) < Set.Iic 2
  rw [cthickening_one_Iic]
  exact Set.Iic_ssubset_Iic.2 (by norm_num)

/-- **Touching half-chains are not properly contained**: `(-∞, 0] ⋐ (-∞, 1]` fails, the
`1`-thickening of `(-∞, 0]` already filling `(-∞, 1]`. -/
theorem not_Iic_properlyContained_Iic_one :
    letI := ProperContainment.ofCThickening ℤ ⟨1, one_pos⟩
    ¬ Set.Iic (0 : ℤ) ⋐ Set.Iic 1 := by
  change ¬ Metric.cthickening 1 (Set.Iic (0 : ℤ)) < Set.Iic 1
  rw [cthickening_one_Iic]
  exact lt_irrefl _

/-! ### Quantum spin systems -/

variable (sites : Type*) [DecidableEq sites] (n : ℕ)

/-- The **quantum spin system** of `n`-level spins on `sites`: the tensor product net whose local
algebra of a finite region `Λ` is `⨂_{x ∈ Λ} B(ℂⁿ)`, the isotony embeddings being `z ↦ z ⊗ 1`. -/
noncomputable abbrev quantumSpinSystem : GradedLocalNet (Finset sites) :=
  tensorNet sites fun _ => EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)

/-- **The quantum spin system has the split property** in its universal representation (the
Gelfand–Naimark representation of the quasi-local algebra, faithful and unital), under any proper
containment: the algebra of a finite region is a finite-dimensional factor
(`GradedLocalNet.splitProperty_of_finiteDimensional`). The property is automatic on finite regions; its
content for a lattice is on infinite ones. -/
theorem quantumSpinSystem_splitProperty [NeZero n] [ProperContainment (Finset sites)] :
    (quantumSpinSystem sites n).SplitProperty (CStarRep.gelfandNaimark _) :=
  splitProperty_of_finiteDimensional _ _ (CStarRep.gelfandNaimark_π_one _)

/-- **A site of the spin chain splits from the half-chain to its right**, in every unital
representation: `{0}` and `[1, ∞)` are a split pair, the algebra of `{0}` being a type I factor
(`CStarNet.isTypeIFactor_localVonNeumannAlgebra`). The pair is adjacent, with no gap; one of its
regions is finite. -/
theorem quantumSpinChain_isSplitPair_singleton_Ici [NeZero n]
    (R : CStarRep (quantumSpinSystem ℤ n).quasiLocalCStarAlgebra) (hR : R.π 1 = 1) :
    ((quantumSpinSystem ℤ n).vonNeumannNetSet R).IsSplitPair ((({0} : Finset ℤ)) : Set ℤ)
      (Set.Ici 1) := by
  refine VonNeumannNet.isSplitPair_of_isTypeIFactor ?_ ?_
  · rw [vonNeumannNetSet_algebra_coe]
    exact CStarNet.isTypeIFactor_localVonNeumannAlgebra _ R hR _
  · change Disjoint _ _
    rw [Finset.coe_singleton, Set.disjoint_singleton_left]
    simp

/-! ### Translations of the spin chain -/

/-- The **translation** of the spin chain by `v`: the covariance of the shift `x ↦ x + v` of the
sites (`GradedLocalNet.sitePermCovariance`), moving every region and its algebra along. -/
noncomputable def translation (v : ℤ) : (quantumSpinSystem ℤ n).Covariance :=
  sitePermCovariance _ (Equiv.addRight v)

/-- The translation by `v` moves a region `Λ` to `Λ + v`. -/
lemma translation_σ (v : ℤ) (Λ : Finset ℤ) :
    (translation n v).σ Λ = Λ.map (Equiv.addRight v).toEmbedding :=
  rfl

/-- **The translation moves the regions**: it sends the site `x` to `x + v`. -/
theorem translation_σ_singleton (v x : ℤ) : (translation n v).σ {x} = {x + v} := by
  rw [translation_σ]
  simp

/-- The translation carries an elementary tensor `⨂ aₓ` over `Λ` to `⨂ a_{y - v}` over `Λ + v`. -/
lemma translation_β_of_tprod (v : ℤ) (Λ : Finset ℤ)
    (a : Λ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    (translation n v).β Λ (PiMinTensorProduct.of _ (⨂ₜ[ℂ] x, a x)) =
      PiMinTensorProduct.of _ (⨂ₜ[ℂ] y, a ((sitePermEquiv (Equiv.addRight v) Λ).symm y)) :=
  sitePermCovariance_β_of_tprod _ Λ a

/-! ### An on-site `U(1)` symmetry of the spin chain -/

/-- The operator `diag(1, z, …, z^{n-1})` on `ℂⁿ`. -/
noncomputable def phaseOp (z : ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (Matrix.diagonal fun k : Fin n => z ^ (k : ℕ))

/-- `phaseOp z * phaseOp w = phaseOp (z * w)`. -/
lemma phaseOp_mul (z w : ℂ) : phaseOp n z * phaseOp n w = phaseOp n (z * w) := by
  rw [phaseOp, phaseOp, phaseOp, ← map_mul, Matrix.diagonal_mul_diagonal]
  simp_rw [mul_pow]

/-- `(phaseOp z)⋆ = phaseOp z̄`. -/
lemma star_phaseOp (z : ℂ) : star (phaseOp n z) = phaseOp n (star z) := by
  rw [phaseOp, phaseOp, ← map_star, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  simp_rw [Pi.star_def, star_pow]

/-- `phaseOp 1 = 1`. -/
lemma phaseOp_one : phaseOp n 1 = 1 := by
  rw [phaseOp]
  simp

/-- `z ↦ phaseOp z` is continuous. -/
lemma continuous_phaseOp : Continuous (phaseOp n) :=
  (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))).comp
    (Continuous.matrix_diagonal (continuous_pi fun k => continuous_pow (k : ℕ)))

/-- For `z` on the circle, `phaseOp z` is unitary. -/
lemma phaseOp_mem_unitary (z : Circle) : phaseOp n z ∈ unitary _ := by
  have h : star (z : ℂ) * z = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  rw [Unitary.mem_iff, star_phaseOp, phaseOp_mul, phaseOp_mul, h, mul_comm, h, phaseOp_one]
  exact ⟨rfl, rfl⟩

/-- `z ↦ phaseOp z`, as a homomorphism of the circle into the unitaries of `B(ℂⁿ)`. -/
noncomputable def phaseUnitary :
    Circle →* unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) where
  toFun z := ⟨phaseOp n z, phaseOp_mem_unitary n z⟩
  map_one' := Subtype.ext ((congrArg (phaseOp n) Circle.coe_one).trans (phaseOp_one n))
  map_mul' z w :=
    Subtype.ext ((congrArg (phaseOp n) (Circle.coe_mul z w)).trans (phaseOp_mul n z w).symm)

/-- **The `U(1)` rotations of a spin**: the circle acting on `B(ℂⁿ)` by
`x ↦ phaseOp z * x * (phaseOp z)⋆`, a C⋆-dynamical system. -/
noncomputable def rotation :
    Circle →ₜ* ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) :=
  ⟨(Unitary.conjStarAlgAut ℂ _).comp (phaseUnitary n),
    StarAlgEquiv.continuous_iff.mpr fun a => by
      change Continuous fun z : Circle => phaseOp n z * a * star (phaseOp n z)
      simp_rw [star_phaseOp]
      have hz : Continuous fun z : Circle => (z : ℂ) := by fun_prop
      exact (((continuous_phaseOp n).comp hz).mul continuous_const).mul
        ((continuous_phaseOp n).comp (continuous_star.comp hz))⟩

/-- `rotation z x = phaseOp z * x * phaseOp z̄`. -/
lemma rotation_apply (z : Circle) (x : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    rotation n z x = phaseOp n z * x * phaseOp n (star (z : ℂ)) := by
  change phaseOp n z * x * star (phaseOp n z) = _
  rw [star_phaseOp]

/-- **The on-site `U(1)` symmetry of the spin chain**: the circle acting on the quasi-local
C⋆-algebra by the rotation of every spin (`GradedLocalNet.onSiteDynamicalSystem`), a C⋆-dynamical system
whose group is not discrete. -/
noncomputable def spinChainRotation [NeZero n] :
    Circle →ₜ* ((quantumSpinSystem ℤ n).quasiLocalCStarAlgebra ≃⋆ₐ[ℂ]
      (quantumSpinSystem ℤ n).quasiLocalCStarAlgebra) :=
  onSiteDynamicalSystem ℤ (constOnSite ℤ (rotation n))

/-- The matrix unit `|i⟩⟨j|` on `ℂⁿ`. -/
noncomputable def matrixUnit (i j : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (Matrix.single i j 1)

/-- **The rotation by `z` multiplies `|i⟩⟨j|` by `z^i z̄^j`.** -/
lemma rotation_matrixUnit (z : Circle) (i j : Fin n) :
    rotation n z (matrixUnit n i j) =
      ((z : ℂ) ^ (i : ℕ) * star (z : ℂ) ^ (j : ℕ)) • matrixUnit n i j := by
  rw [rotation_apply, phaseOp, phaseOp, matrixUnit, ← map_mul, ← map_mul, ← map_smul]
  congr 1
  ext a b
  rcases eq_or_ne a i with rfl | ha <;> rcases eq_or_ne b j with rfl | hb <;>
    simp [Matrix.mul_diagonal, mul_comm, *, Ne.symm]

/-- The matrix unit `|i⟩⟨j|` at the site `0`, as a local observable of the region `{0}`. -/
noncomputable def matrixUnitAtZero (i j : Fin n) :
    ⨂ₘᵢₙ _ : ({0} : Finset ℤ), EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  PiMinTensorProduct.of _ (⨂ₜ[ℂ] _ : ({0} : Finset ℤ), matrixUnit n i j)

/-- A matrix unit at the site `0` is not zero. -/
lemma matrixUnitAtZero_ne_zero (i j : Fin n) : matrixUnitAtZero n i j ≠ 0 := fun h => by
  have : Subsingleton ({0} : Finset ℤ) := ⟨fun a b => Subtype.ext
    ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  have h2 := congrArg (PiMinTensorProduct.subsingletonEquiv
    (fun _ : ({0} : Finset ℤ) => EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    ⟨0, Finset.mem_singleton_self 0⟩) h
  rw [matrixUnitAtZero, PiMinTensorProduct.subsingletonEquiv_of,
    PiTensorProduct.subsingletonStarAlgEquiv_tprod, map_zero, matrixUnit] at h2
  have h3 := congrArg (fun T => (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm T i j) h2
  simp at h3

/-- **The rotation by `-1` reverses the matrix unit `|0⟩⟨1|` at the site `0`**, for `n ≥ 2`: it
multiplies it by `(-1)⁰ (-1)¹ = -1`. -/
theorem spinChainRotation_neg_one_matrixUnitAtZero [NeZero n] (h : 1 < n) :
    spinChainRotation n (-1)
        ((quantumSpinSystem ℤ n).ιLocalCStar {0} (matrixUnitAtZero n 0 ⟨1, h⟩)) =
      (quantumSpinSystem ℤ n).ιLocalCStar {0} (-matrixUnitAtZero n 0 ⟨1, h⟩) := by
  have hr : rotation n (-1) (matrixUnit n 0 ⟨1, h⟩) = -matrixUnit n 0 ⟨1, h⟩ := by
    rw [rotation_matrixUnit]
    simp only [Circle.coe_neg, Circle.coe_one, Fin.val_zero, pow_zero, one_mul, pow_one, star_neg,
      star_one]
    exact neg_one_smul ℂ (matrixUnit n 0 ⟨1, h⟩)
  have : Subsingleton ({0} : Finset ℤ) := ⟨fun a b => Subtype.ext
    ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  have h3 : PiMinTensorProduct.of (fun _ : ({0} : Finset ℤ) =>
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
        (⨂ₜ[ℂ] x, constOnSite ℤ (rotation n) (-1) x (matrixUnit n 0 ⟨1, h⟩)) =
      -PiMinTensorProduct.of (fun _ : ({0} : Finset ℤ) =>
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
        (⨂ₜ[ℂ] _ : ({0} : Finset ℤ), matrixUnit n 0 ⟨1, h⟩) := by
    refine EquivLike.injective
      (PiMinTensorProduct.subsingletonEquiv _ ⟨0, Finset.mem_singleton_self 0⟩) ?_
    rw [map_neg, PiMinTensorProduct.subsingletonEquiv_of,
      PiMinTensorProduct.subsingletonEquiv_of, PiTensorProduct.subsingletonStarAlgEquiv_tprod,
      PiTensorProduct.subsingletonStarAlgEquiv_tprod]
    exact hr
  unfold spinChainRotation matrixUnitAtZero
  rw [onSiteDynamicalSystem_ιLocalCStar_of_tprod (constOnSite ℤ (rotation n)) (-1) {0}
    fun _ => matrixUnit n 0 ⟨1, h⟩]
  rw [h3]

/-- **The on-site `U(1)` symmetry acts non-trivially** for `n ≥ 2`: the rotation by `-1` moves the
matrix unit `|0⟩⟨1|` at the site `0`, which it reverses. -/
theorem spinChainRotation_neg_one_ne [NeZero n] (h : 1 < n) :
    spinChainRotation n (-1)
        ((quantumSpinSystem ℤ n).ιLocalCStar {0} (matrixUnitAtZero n 0 ⟨1, h⟩)) ≠
      (quantumSpinSystem ℤ n).ιLocalCStar {0} (matrixUnitAtZero n 0 ⟨1, h⟩) := by
  rw [spinChainRotation_neg_one_matrixUnitAtZero n h]
  refine ((quantumSpinSystem ℤ n).ιLocalCStar_injective {0}).ne fun h' => ?_
  have := HasUniqueDiv.of_isTorsionFree ℂ
    (⨂ₘᵢₙ _ : ({0} : Finset ℤ), EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  exact matrixUnitAtZero_ne_zero n 0 ⟨1, h⟩ (neg_eq_self.mp h')

end GradedLocalNet.Examples
