/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Completion
public import QuantumSystem.ForMathlib.RingTheory.PiTensorProduct.NonUnital

/-!
# The projective tensor product of normed algebras

For a finite family `E i` of normed spaces over `𝕜`, the **projective tensor product**
`ProjectiveTensorProduct 𝕜 E` is the completion of `⨂[𝕜] i, E i` for Mathlib's projective seminorm
(`PiTensorProduct.projectiveSeminorm`), a Banach space. Over `ℝ` or `ℂ` the seminorm of a pure tensor
is the product of the norms of the factors. For a family of normed algebras, unital or not, the
projective seminorm is submultiplicative, so the projective tensor product is a Banach algebra.

For a single normed algebra `B`, `B ⊗̂ B` is the projective tensor product
`ProjectiveTensorPower 𝕜 2 B` of two copies of `B`, written `⨂̂[𝕜]^2 B` in the statements. It is a
`B`-bimodule, `a • (b ⊗ c) • a' = (a b) ⊗ (c a')`; the actions are continuous linear maps of
`B ⊗̂ B`, defined without a unit of `B`, and for a unital `B` they are the multiplications by
`a ⊗ 1` and `1 ⊗ a'`. For a Banach algebra `B`, the multiplication `b ⊗ c ↦ b c` extends to a
contractive bimodule map `m : B ⊗̂ B → B`. A **diagonal** of `B` is an element `d` of `B ⊗̂ B` with
`a • d = d • a` and `m(d) a = a` for every `a`; a **bounded approximate diagonal** is a bounded
family, along a nontrivial filter, for which these hold in the limit. A diagonal makes `m(d)` a
unit of `B`; the sequence algebra `C₀(ℕ, 𝕜)` has none, but has a bounded approximate diagonal.

## Main definitions

* `ProjectiveTensorProduct 𝕜 E` — the projective tensor product of a finite family of normed
  spaces; a Banach algebra for a family of normed algebras.
* `ProjectiveTensorPower 𝕜 n B` — the projective tensor product of `n` copies of `B`.
* `ProjectiveTensorProduct.map f` — the tensor product of a family of continuous linear maps.
* `ProjectiveTensorProduct.tmul b c` — the pure tensor `b ⊗ c` of `B ⊗̂ B`.
* `ProjectiveTensorProduct.leftAct 𝕜 B`, `ProjectiveTensorProduct.rightAct 𝕜 B` — the left and
  right actions of `B` on `B ⊗̂ B`.
* `ProjectiveTensorProduct.mul 𝕜 B` — for a Banach algebra `B`, the multiplication
  `B ⊗̂ B →L[𝕜] B`, `b ⊗ c ↦ b c`.
* `ProjectiveTensorProduct.IsDiagonal d` — `d` is a diagonal of `B`.
* `ProjectiveTensorProduct.IsBoundedApproximateDiagonal d l` — `d` is a bounded approximate
  diagonal of `B` along the filter `l`.
* `ProjectiveTensorProduct.groupAverage 𝕜 u` — for a finite group of units `u : G →* Bˣ`, the
  average `|G|⁻¹ ∑ g, (u g)⁻¹ ⊗ u g`.
* `ProjectiveTensorProduct.signUnits 𝕜 n` — the sign vectors `{±1}ⁿ` as units of `Fin n → 𝕜`.
* `ProjectiveTensorProduct.truncDiagonal 𝕜 N` — `∑_{k < N} e_k ⊗ e_k` in `C₀(ℕ, 𝕜) ⊗̂ C₀(ℕ, 𝕜)`.

## Main results

* `PiTensorProduct.norm_tprod` — over `ℝ` or `ℂ`, `‖⨂ₜ i, m i‖ = ∏ i, ‖m i‖`.
* `PiTensorProduct.norm_mul_le_mul` — the projective seminorm is submultiplicative.
* `ProjectiveTensorProduct.norm_mul_apply_le` — the multiplication `B ⊗̂ B → B` is contractive;
  `ProjectiveTensorProduct.mul_leftAct`, `ProjectiveTensorProduct.mul_rightAct` — it is a bimodule
  map.
* `ProjectiveTensorProduct.IsDiagonal.mul_apply_mul`,
  `ProjectiveTensorProduct.IsDiagonal.mul_mul_apply` — the image of a diagonal is a unit of `B`;
  `ProjectiveTensorProduct.IsDiagonal.isBoundedApproximateDiagonal` — a diagonal is a bounded
  approximate diagonal.
* `ProjectiveTensorProduct.isDiagonal_groupAverage` — the average over a finite group of units
  spanning `B` is a diagonal, when the order of the group is invertible in `𝕜`;
  `ProjectiveTensorProduct.norm_groupAverage` — over `ℝ` or `ℂ` the average has norm one when the
  units are contractive and `B` is a nontrivial Banach algebra.
* `ProjectiveTensorProduct.isDiagonal_groupAverage_sign`,
  `ProjectiveTensorProduct.norm_groupAverage_sign` — the average over the sign vectors is a
  diagonal of norm one of `Fin n → 𝕜` with the supremum norm.
* `ProjectiveTensorProduct.isBoundedApproximateDiagonal_truncDiagonal` — the truncated diagonals
  form a bounded approximate diagonal of `C₀(ℕ, 𝕜)`; `ProjectiveTensorProduct.not_isDiagonal_zeroAtInfty` — it
  has no diagonal.

## Notation

Activated by `open scoped ProjectiveTensorProduct`: `⨂̂[𝕜]^n B` — `ProjectiveTensorPower 𝕜 n B`, the
projective counterpart of Mathlib's `⨂[R]^n M`.

## Implementation notes

The ring structure of `⨂[𝕜] i, A i` for non-unital `A i`, which Mathlib lacks, is drafted in
`QuantumSystem/ForMathlib/RingTheory/PiTensorProduct/NonUnital.lean`, and the completion of a
non-unital normed ring in `QuantumSystem/ForMathlib/Analysis/CStarAlgebra/Completion.lean`.
-/

@[expose] public section

open scoped TensorProduct ZeroAtInfty
open Filter Topology UniformSpace

namespace PiTensorProduct

/-! ### The projective seminorm -/

variable {ι : Type*} [Fintype ι]

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)]

/-- **The projective seminorm of a pure tensor is the product of the norms** over `ℝ` or `ℂ`:
`‖⨂ₜ i, m i‖ = ∏ i, ‖m i‖`. It is at most the product by definition; for the reverse inequality,
the product of norming functionals `fᵢ`, `‖fᵢ‖ = 1` and `fᵢ (m i) = ‖m i‖`, is a continuous
multilinear form of norm at most one taking the value `∏ i, ‖m i‖` at `m`. -/
theorem norm_tprod (m : Π i, E i) : ‖(⨂ₜ[𝕜] i, m i)‖ = ∏ i, ‖m i‖ := by
  refine le_antisymm (projectiveSeminorm_tprod_le m) ?_
  by_cases h : ∀ i, ‖m i‖ ≠ 0
  · choose f hf₁ hf₂ using fun i => exists_dual_vector 𝕜 (m i) (h i)
    let F := (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝕜).compContinuousLinearMap f
    have hF : ‖F‖ ≤ 1 := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rcases isEmpty_or_nonempty ι with hι | hι
      · simp
      · simp only [hf₁, Finset.prod_const_one, mul_one]
        exact ContinuousMultilinearMap.norm_mkPiAlgebra_le
    have := norm_eval_le_projectiveSeminorm F (⨂ₜ[𝕜] i, m i)
    rw [lift.tprod] at this
    simp [F, hf₂] at this
    exact this.trans (mul_le_of_le_one_left (norm_nonneg _) hF)
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    exact norm_nonneg _

end RCLike

section Algebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {A : ι → Type*}
  [∀ i, NonUnitalSeminormedRing (A i)] [∀ i, NormedSpace 𝕜 (A i)]
  [∀ i, IsScalarTower 𝕜 (A i) (A i)] [∀ i, SMulCommClass 𝕜 (A i) (A i)]

/-- Left multiplication by a pure tensor is bounded by the product of the norms of its factors:
`‖(⨂ₜ i, m i) * y‖ ≤ (∏ i, ‖m i‖) * ‖y‖`. -/
lemma norm_tprod_mul_le (m : Π i, A i) (y : ⨂[𝕜] i, A i) :
    ‖(⨂ₜ[𝕜] i, m i) * y‖ ≤ (∏ i, ‖m i‖) * ‖y‖ := by
  let G : ContinuousMultilinearMap 𝕜 A (⨂[𝕜] i, A i) :=
    ((mul (tprod 𝕜 m)).compMultilinearMap (tprod 𝕜)).mkContinuous (∏ i, ‖m i‖) fun n => by
      simp only [LinearMap.compMultilinearMap_apply, ← mul_def, tprod_mul_tprod]
      refine (projectiveSeminorm_tprod_le _).trans ?_
      rw [← Finset.prod_mul_distrib]
      gcongr with i
      exact norm_mul_le _ _
  have hG : ‖G‖ ≤ ∏ i, ‖m i‖ :=
    MultilinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun i _ => norm_nonneg _) _
  have hlift : lift G.toMultilinearMap y = (⨂ₜ[𝕜] i, m i) * y := by
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r n => simp [G, mul_def]
    | add p q hp hq => rw [map_add, hp, hq, mul_add]
  rw [← hlift]
  exact (norm_eval_le_projectiveSeminorm G y).trans (by gcongr)

/-- **The projective seminorm is submultiplicative**: `‖x * y‖ ≤ ‖x‖ * ‖y‖`. Right multiplication
by `y` is the linear map of the multilinear map `m ↦ (⨂ₜ i, m i) * y`, of norm at most `‖y‖` by
`PiTensorProduct.norm_tprod_mul_le`. -/
theorem norm_mul_le_mul (x y : ⨂[𝕜] i, A i) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  let G : ContinuousMultilinearMap 𝕜 A (⨂[𝕜] i, A i) :=
    (((mul (R := 𝕜) (A := A)).flip y).compMultilinearMap (tprod 𝕜)).mkContinuous ‖y‖ fun m => by
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.flip_apply, ← mul_def]
      rw [mul_comm ‖y‖]
      exact norm_tprod_mul_le m y
  have hG : ‖G‖ ≤ ‖y‖ := MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  have hlift : lift G.toMultilinearMap x = x * y := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r n => simp [G, mul_def]
    | add p q hp hq => rw [map_add, hp, hq, add_mul]
  rw [← hlift, mul_comm ‖x‖]
  exact (norm_eval_le_projectiveSeminorm G x).trans (by gcongr)

/-- The tensor product of non-unital normed algebras is a non-unital seminormed ring for the
projective seminorm. -/
noncomputable instance instNonUnitalSeminormedRing : NonUnitalSeminormedRing (⨂[𝕜] i, A i) where
  __ : SeminormedAddCommGroup (⨂[𝕜] i, A i) := inferInstance
  __ : NonUnitalRing (⨂[𝕜] i, A i) := inferInstance
  norm_mul_le := norm_mul_le_mul

end Algebra

section UnitalAlgebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {A : ι → Type*} [∀ i, SeminormedRing (A i)]
  [∀ i, NormedAlgebra 𝕜 (A i)]

/-- The tensor product of normed algebras is a seminormed ring for the projective seminorm. -/
noncomputable instance instSeminormedRing : SeminormedRing (⨂[𝕜] i, A i) where
  __ : SeminormedAddCommGroup (⨂[𝕜] i, A i) := inferInstance
  __ : Ring (⨂[𝕜] i, A i) := inferInstance
  norm_mul_le := norm_mul_le_mul

/-- The tensor product of normed algebras is a seminormed algebra for the projective seminorm. -/
noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 (⨂[𝕜] i, A i) where
  norm_smul_le := norm_smul_le

end UnitalAlgebra

end PiTensorProduct

section Definition

variable {ι : Type*} [Fintype ι] (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : ι → Type*)
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- The **projective tensor product** of a finite family of normed spaces: the completion of the
algebraic tensor product `⨂[𝕜] i, E i` for the projective seminorm, a Banach space. For a family of
normed algebras, unital or not, it is a Banach algebra. -/
abbrev ProjectiveTensorProduct : Type _ :=
  Completion (⨂[𝕜] i, E i)

variable (n : ℕ) (B : Type*) [SeminormedAddCommGroup B] [NormedSpace 𝕜 B]

/-- The projective tensor product of `n` copies of a normed space `B`, the projective counterpart of
Mathlib's `TensorPower`; for `n = 2` it is `B ⊗̂ B`. -/
abbrev ProjectiveTensorPower : Type _ :=
  ProjectiveTensorProduct 𝕜 fun _ : Fin n => B

@[inherit_doc] scoped[ProjectiveTensorProduct] notation:max "⨂̂[" 𝕜 "]^" n:arg =>
  ProjectiveTensorPower 𝕜 n

end Definition

namespace ProjectiveTensorProduct

variable {ι : Type*} [Fintype ι] {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The projective tensor product of normed algebras is a normed algebra. Its ring structure, norm
and completeness are those of the completion. -/
noncomputable instance instNormedAlgebra {A : ι → Type*} [∀ i, SeminormedRing (A i)]
    [∀ i, NormedAlgebra 𝕜 (A i)] : NormedAlgebra 𝕜 (ProjectiveTensorProduct 𝕜 A) where
  norm_smul_le := norm_smul_le

/-! ### Tensor products of maps -/

section Map

variable {E F : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, SeminormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- Two continuous linear maps out of the projective tensor product that agree on the pure tensors
are equal. -/
lemma ext {G : Type*} [TopologicalSpace G] [AddCommMonoid G] [Module 𝕜 G] [T2Space G]
    {φ ψ : ProjectiveTensorProduct 𝕜 E →L[𝕜] G}
    (h : ∀ m : Π i, E i, φ ((PiTensorProduct.tprod 𝕜 m : ⨂[𝕜] i, E i) : Completion (⨂[𝕜] i, E i)) =
      ψ ((PiTensorProduct.tprod 𝕜 m : ⨂[𝕜] i, E i) : Completion (⨂[𝕜] i, E i))) :
    φ = ψ := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq φ.continuous ψ.continuous
  | ih y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r m => rw [Completion.coe_smul, map_smul, map_smul, h]
    | add p q hp hq => rw [Completion.coe_add, map_add, map_add, hp, hq]

/-- The **tensor product of continuous linear maps** `f i : E i →L[𝕜] F i`, extended to the
projective tensor products: `⨂ m i ↦ ⨂ f i (m i)`. -/
noncomputable def map (f : Π i, E i →L[𝕜] F i) :
    ProjectiveTensorProduct 𝕜 E →L[𝕜] ProjectiveTensorProduct 𝕜 F :=
  ((Completion.toComplL : (⨂[𝕜] i, F i) →L[𝕜] Completion (⨂[𝕜] i, F i)).comp
    (PiTensorProduct.mapL f)).extend
    (Completion.toComplL : (⨂[𝕜] i, E i) →L[𝕜] Completion (⨂[𝕜] i, E i))

/-- On the algebraic tensor product, `ProjectiveTensorProduct.map f` is `PiTensorProduct.mapL f`. -/
lemma map_coe (f : Π i, E i →L[𝕜] F i) (y : ⨂[𝕜] i, E i) :
    map f (y : Completion (⨂[𝕜] i, E i)) =
      ((PiTensorProduct.mapL f y : ⨂[𝕜] i, F i) : Completion (⨂[𝕜] i, F i)) :=
  ContinuousLinearMap.extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _) y

/-- The tensor product of maps is bounded by the product of their norms:
`‖map f x‖ ≤ (∏ i, ‖f i‖) * ‖x‖`. -/
lemma norm_map_le (f : Π i, E i →L[𝕜] F i) (x : ProjectiveTensorProduct 𝕜 E) :
    ‖map f x‖ ≤ (∏ i, ‖f i‖) * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (map f).continuous.norm (continuous_const.mul continuous_norm)
  | ih y =>
    rw [map_coe, Completion.norm_coe, Completion.norm_coe]
    exact (PiTensorProduct.mapL f).le_of_opNorm_le (PiTensorProduct.opNorm_mapL f) y

end Map

/-! ### Two copies of a normed space -/

section Two

variable {B : Type*} [SeminormedAddCommGroup B] [NormedSpace 𝕜 B]

/-- The pure tensor `b ⊗ c` of `B ⊗̂ B`. -/
noncomputable def tmul (b c : B) : ⨂̂[𝕜]^2 B :=
  ((PiTensorProduct.tprod 𝕜 ![b, c] : ⨂[𝕜] _ : Fin 2, B) : Completion (⨂[𝕜] _ : Fin 2, B))

/-- The norm of a pure tensor `b ⊗ c` is at most `‖b‖ * ‖c‖`. -/
lemma norm_tmul_le (b c : B) :
    ‖(tmul b c : ⨂̂[𝕜]^2 B)‖ ≤ ‖b‖ * ‖c‖ := by
  have h := PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := 𝕜) (E := fun _ : Fin 2 => B) ![b, c]
  rw [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  exact (Completion.norm_coe _).trans_le h

omit [SeminormedAddCommGroup B] [NormedSpace 𝕜 B] in
private lemma update_vec_zero (y c x : B) : Function.update (![y, c] : Fin 2 → B) 0 x = ![x, c] := by
  funext i
  fin_cases i <;> simp

omit [SeminormedAddCommGroup B] [NormedSpace 𝕜 B] in
private lemma update_vec_one (b y x : B) : Function.update (![b, y] : Fin 2 → B) 1 x = ![b, x] := by
  funext i
  fin_cases i <;> simp

/-- The pure tensor `b ⊗ c` is additive in `b`. -/
lemma tmul_add_left (b b' c : B) :
    (tmul (b + b') c : ⨂̂[𝕜]^2 B) = tmul b c + tmul b' c := by
  have h := (PiTensorProduct.tprod 𝕜).map_update_add (![0, c] : Fin 2 → B) 0 b b'
  rw [update_vec_zero, update_vec_zero, update_vec_zero] at h
  rw [tmul, tmul, tmul, h, Completion.coe_add]

/-- The pure tensor `b ⊗ c` is additive in `c`. -/
lemma tmul_add_right (b c c' : B) :
    (tmul b (c + c') : ⨂̂[𝕜]^2 B) = tmul b c + tmul b c' := by
  have h := (PiTensorProduct.tprod 𝕜).map_update_add (![b, 0] : Fin 2 → B) 1 c c'
  rw [update_vec_one, update_vec_one, update_vec_one] at h
  rw [tmul, tmul, tmul, h, Completion.coe_add]

/-- The pure tensor `b ⊗ c` is homogeneous in `b`. -/
lemma tmul_smul_left (r : 𝕜) (b c : B) :
    (tmul (r • b) c : ⨂̂[𝕜]^2 B) = r • tmul b c := by
  have h := (PiTensorProduct.tprod 𝕜).map_update_smul (![0, c] : Fin 2 → B) 0 r b
  rw [update_vec_zero, update_vec_zero] at h
  rw [tmul, tmul, h, Completion.coe_smul]

/-- The pure tensor `b ⊗ c` is homogeneous in `c`. -/
lemma tmul_smul_right (r : 𝕜) (b c : B) :
    (tmul b (r • c) : ⨂̂[𝕜]^2 B) = r • tmul b c := by
  have h := (PiTensorProduct.tprod 𝕜).map_update_smul (![b, 0] : Fin 2 → B) 1 r c
  rw [update_vec_one, update_vec_one] at h
  rw [tmul, tmul, h, Completion.coe_smul]

/-- Two continuous linear maps out of `B ⊗̂ B` that agree on the pure tensors `b ⊗ c` are equal. -/
lemma ext_tmul {G : Type*} [TopologicalSpace G] [AddCommMonoid G] [Module 𝕜 G] [T2Space G]
    {φ ψ : ⨂̂[𝕜]^2 B →L[𝕜] G}
    (h : ∀ b c : B, φ (tmul b c) = ψ (tmul b c)) : φ = ψ :=
  ext fun m => by
    have hm : m = ![m 0, m 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hm]
    exact h (m 0) (m 1)

/-- The tensor product of two maps sends `b ⊗ c` to `f 0 b ⊗ f 1 c`. -/
lemma map_tmul {B' : Type*} [SeminormedAddCommGroup B'] [NormedSpace 𝕜 B'] (f : Fin 2 → B →L[𝕜] B')
    (b c : B) : map f (tmul b c) = tmul (f 0 b) (f 1 c) := by
  rw [tmul, map_coe, PiTensorProduct.mapL_apply, PiTensorProduct.map_tprod]
  congr 2
  funext i
  fin_cases i <;> rfl

end Two

/-! ### Two copies of a normed algebra -/

section Algebra

variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B] [IsScalarTower 𝕜 B B]
  [SMulCommClass 𝕜 B B]

/-- Pure tensors multiply factorwise: `(b ⊗ c) (b' ⊗ c') = (b b') ⊗ (c c')`. -/
lemma tmul_mul_tmul (b c b' c' : B) :
    (tmul b c : ⨂̂[𝕜]^2 B) * tmul b' c' =
      tmul (b * b') (c * c') := by
  change ((PiTensorProduct.tprod 𝕜 ![b, c] : ⨂[𝕜] _ : Fin 2, B) : Completion (⨂[𝕜] _ : Fin 2, B)) *
    ((PiTensorProduct.tprod 𝕜 ![b', c'] : ⨂[𝕜] _ : Fin 2, B) : Completion (⨂[𝕜] _ : Fin 2, B)) =
      ((PiTensorProduct.tprod 𝕜 ![b * b', c * c'] : ⨂[𝕜] _ : Fin 2, B) :
        Completion (⨂[𝕜] _ : Fin 2, B))
  rw [← Completion.coe_mul', PiTensorProduct.tprod_mul_tprod]
  congr 2
  funext i
  fin_cases i <;> rfl

variable (𝕜 B) in
/-- The **left action** of `B` on `B ⊗̂ B`: `b • (c ⊗ c') = (b c) ⊗ c'`. -/
noncomputable def leftAct :
    B →ₗ[𝕜] ⨂̂[𝕜]^2 B →L[𝕜]
      ⨂̂[𝕜]^2 B where
  toFun b := map ![ContinuousLinearMap.mul 𝕜 B b, ContinuousLinearMap.id 𝕜 B]
  map_add' b b' := ext_tmul fun c c' => by simp [map_tmul, tmul_add_left]
  map_smul' r b := ext_tmul fun c c' => by simp [map_tmul, tmul_smul_left]

variable (𝕜 B) in
/-- The **right action** of `B` on `B ⊗̂ B`: `(c ⊗ c') • b = c ⊗ (c' b)`. -/
noncomputable def rightAct :
    B →ₗ[𝕜] ⨂̂[𝕜]^2 B →L[𝕜]
      ⨂̂[𝕜]^2 B where
  toFun b := map ![ContinuousLinearMap.id 𝕜 B, (ContinuousLinearMap.mul 𝕜 B).flip b]
  map_add' b b' := ext_tmul fun c c' => by simp [map_tmul, tmul_add_right]
  map_smul' r b := ext_tmul fun c c' => by simp [map_tmul, tmul_smul_right]

/-- `b • (c ⊗ c') = (b c) ⊗ c'`. -/
@[simp] lemma leftAct_tmul (b c c' : B) : leftAct 𝕜 B b (tmul c c') = tmul (b * c) c' := by
  simp [leftAct, map_tmul]

/-- `(c ⊗ c') • b = c ⊗ (c' b)`. -/
@[simp] lemma rightAct_tmul (b c c' : B) : rightAct 𝕜 B b (tmul c c') = tmul c (c' * b) := by
  simp [rightAct, map_tmul]

/-- The left action is bounded: `‖b • x‖ ≤ ‖b‖ * ‖x‖`. -/
lemma norm_leftAct_le (b : B) (x : ⨂̂[𝕜]^2 B) :
    ‖leftAct 𝕜 B b x‖ ≤ ‖b‖ * ‖x‖ := by
  refine (norm_map_le _ x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg x))
  rw [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact (mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le 𝕜 B b) ContinuousLinearMap.norm_id_le
    (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)

/-- The right action is bounded: `‖x • b‖ ≤ ‖b‖ * ‖x‖`. -/
lemma norm_rightAct_le (b : B) (x : ⨂̂[𝕜]^2 B) :
    ‖rightAct 𝕜 B b x‖ ≤ ‖b‖ * ‖x‖ := by
  refine (norm_map_le _ x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg x))
  rw [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hb : ‖(ContinuousLinearMap.mul 𝕜 B).flip b‖ ≤ ‖b‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b) fun c => by
      rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_comm ‖b‖]
      exact norm_mul_le c b
  exact (mul_le_mul ContinuousLinearMap.norm_id_le hb (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)

/-- The left action is an action: `(b c) • x = b • (c • x)`. -/
lemma leftAct_mul (b c : B) : leftAct 𝕜 B (b * c) = (leftAct 𝕜 B b).comp (leftAct 𝕜 B c) :=
  ext_tmul fun a a' => by simp [mul_assoc]

/-- The right action is an action: `x • (b c) = (x • b) • c`. -/
lemma rightAct_mul (b c : B) : rightAct 𝕜 B (b * c) = (rightAct 𝕜 B c).comp (rightAct 𝕜 B b) :=
  ext_tmul fun a a' => by simp [mul_assoc]

/-- The two actions commute: `(b • x) • c = b • (x • c)`. -/
lemma leftAct_comp_rightAct (b c : B) :
    (leftAct 𝕜 B b).comp (rightAct 𝕜 B c) = (rightAct 𝕜 B c).comp (leftAct 𝕜 B b) :=
  ext_tmul fun a a' => by simp

variable (𝕜 B) in
/-- The continuous bilinear map `![b, c] ↦ b c`, as a continuous multilinear map on two copies of
`B`, of norm at most one. -/
noncomputable def mulMultilinear : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => B) B :=
  MultilinearMap.mkContinuous
    { toFun m := m 0 * m 1
      map_update_add' m i x y := by fin_cases i <;> simp [add_mul, mul_add]
      map_update_smul' m i r x := by fin_cases i <;> simp [smul_mul_assoc, mul_smul_comm] }
    1 fun m => by simpa [Fin.prod_univ_two] using norm_mul_le (m 0) (m 1)

/-- `mulMultilinear 𝕜 B` sends `m` to `m 0 * m 1`. -/
@[simp] lemma mulMultilinear_apply (m : Fin 2 → B) : mulMultilinear 𝕜 B m = m 0 * m 1 :=
  rfl

/-- The multilinear map `![b, c] ↦ b c` has norm at most one. -/
lemma norm_mulMultilinear_le : ‖mulMultilinear 𝕜 B‖ ≤ 1 :=
  MultilinearMap.mkContinuous_norm_le _ zero_le_one _

section Multiplication

variable [CompleteSpace B]

variable (𝕜 B) in
/-- The **multiplication** `B ⊗̂ B → B`, `b ⊗ c ↦ b c`, for a Banach algebra `B`: the extension to
the completion of the linear map of the multilinear map `![b, c] ↦ b c`, of norm at most one. -/
noncomputable def mul : ⨂̂[𝕜]^2 B →L[𝕜] B :=
  (PiTensorProduct.liftIsometry 𝕜 (fun _ : Fin 2 => B) B (mulMultilinear 𝕜 B)).extend
    (Completion.toComplL : (⨂[𝕜] _ : Fin 2, B) →L[𝕜] Completion (⨂[𝕜] _ : Fin 2, B))

/-- On the algebraic tensor product, the multiplication `B ⊗̂ B → B` is the linear map of the
multilinear map `![b, c] ↦ b c`. -/
lemma mul_coe (y : ⨂[𝕜] _ : Fin 2, B) :
    mul 𝕜 B (y : Completion (⨂[𝕜] _ : Fin 2, B)) =
      PiTensorProduct.lift (mulMultilinear 𝕜 B).toMultilinearMap y :=
  (ContinuousLinearMap.extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _)
    y).trans (PiTensorProduct.liftIsometry_apply_apply _ _)

/-- The multiplication `B ⊗̂ B → B` sends `b ⊗ c` to `b c`. -/
@[simp] lemma mul_tmul (b c : B) : mul 𝕜 B (tmul b c) = b * c := by
  rw [tmul, mul_coe, PiTensorProduct.lift.tprod]
  rfl

/-- The multiplication `B ⊗̂ B → B` is contractive. -/
lemma norm_mul_apply_le (x : ⨂̂[𝕜]^2 B) :
    ‖mul 𝕜 B x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (mul 𝕜 B).continuous.norm continuous_norm
  | ih y =>
    rw [mul_coe, Completion.norm_coe]
    exact (PiTensorProduct.norm_eval_le_projectiveSeminorm (mulMultilinear 𝕜 B) y).trans
      (mul_le_of_le_one_left (norm_nonneg _) norm_mulMultilinear_le)

/-- The multiplication `B ⊗̂ B → B` is a map of left `B`-modules: `m(b • x) = b m(x)`. -/
lemma mul_leftAct (b : B) (x : ⨂̂[𝕜]^2 B) :
    mul 𝕜 B (leftAct 𝕜 B b x) = b * mul 𝕜 B x := by
  have h : (mul 𝕜 B).comp (leftAct 𝕜 B b) = (ContinuousLinearMap.mul 𝕜 B b).comp (mul 𝕜 B) :=
    ext_tmul fun c c' => by simp [mul_assoc]
  exact congr($h x)

/-- The multiplication `B ⊗̂ B → B` is a map of right `B`-modules: `m(x • b) = m(x) b`. -/
lemma mul_rightAct (b : B) (x : ⨂̂[𝕜]^2 B) :
    mul 𝕜 B (rightAct 𝕜 B b x) = mul 𝕜 B x * b := by
  have h : (mul 𝕜 B).comp (rightAct 𝕜 B b) =
      ((ContinuousLinearMap.mul 𝕜 B).flip b).comp (mul 𝕜 B) :=
    ext_tmul fun c c' => by simp [mul_assoc]
  exact congr($h x)

/-! ### Diagonals -/

/-- A **diagonal** of a Banach algebra `B` is an element `d` of `B ⊗̂ B` that commutes with `B`,
`b • d = d • b` for every `b`, and whose image under the multiplication `m : B ⊗̂ B → B` satisfies
`m(d) b = b` for every `b`. Then `m(d)` is a unit of `B` (`ProjectiveTensorProduct.IsDiagonal.mul_mul_apply`),
and for a unital `B` the second condition is `m(d) = 1`. -/
def IsDiagonal (d : ⨂̂[𝕜]^2 B) : Prop :=
  (∀ b : B, leftAct 𝕜 B b d = rightAct 𝕜 B b d) ∧ ∀ b : B, mul 𝕜 B d * b = b

/-- A **bounded approximate diagonal** of a Banach algebra `B` along a nontrivial filter `l` is a
bounded family `d` of elements of `B ⊗̂ B` that commutes with `B` in the limit,
`b • d j - d j • b → 0`, and whose image under the multiplication `m : B ⊗̂ B → B` satisfies
`m(d j) b → b` for every `b`. -/
structure IsBoundedApproximateDiagonal {κ : Type*}
    (d : κ → ⨂̂[𝕜]^2 B) (l : Filter κ) : Prop where
  /-- The family is bounded. -/
  bounded : ∃ C : ℝ, ∀ j, ‖d j‖ ≤ C
  /-- The family commutes with `B` in the limit. -/
  tendsto_commutator (b : B) :
    Tendsto (fun j => leftAct 𝕜 B b (d j) - rightAct 𝕜 B b (d j)) l (𝓝 0)
  /-- Its image under the multiplication satisfies `m(d j) b → b`. -/
  tendsto_mul_apply_mul (b : B) : Tendsto (fun j => mul 𝕜 B (d j) * b) l (𝓝 b)
  /-- The filter is not `⊥`. -/
  neBot : l.NeBot

namespace IsDiagonal

variable {d : ⨂̂[𝕜]^2 B}

/-- A diagonal commutes with `B`: `b • d = d • b`. -/
lemma leftAct_eq_rightAct (hd : IsDiagonal d) (b : B) : leftAct 𝕜 B b d = rightAct 𝕜 B b d :=
  hd.1 b

/-- The image of a diagonal under the multiplication is a left unit: `m(d) b = b`. -/
lemma mul_apply_mul (hd : IsDiagonal d) (b : B) : mul 𝕜 B d * b = b :=
  hd.2 b

/-- The image of a diagonal under the multiplication is a right unit too, hence a unit of `B`:
`b m(d) = m(b • d) = m(d • b) = m(d) b = b`. -/
lemma mul_mul_apply (hd : IsDiagonal d) (b : B) : b * mul 𝕜 B d = b := by
  rw [← mul_leftAct, hd.leftAct_eq_rightAct, mul_rightAct, hd.mul_apply_mul]

/-- **A diagonal is a bounded approximate diagonal**, as a constant family along any nontrivial
filter. -/
lemma isBoundedApproximateDiagonal (hd : IsDiagonal d) {κ : Type*} (l : Filter κ) [l.NeBot] :
    IsBoundedApproximateDiagonal (fun _ : κ => d) l where
  bounded := ⟨‖d‖, fun _ => le_rfl⟩
  tendsto_commutator b := by
    simp only [hd.leftAct_eq_rightAct b, sub_self]
    exact tendsto_const_nhds
  tendsto_mul_apply_mul b := by
    simp only [hd.mul_apply_mul b]
    exact tendsto_const_nhds
  neBot := ‹_›

end IsDiagonal

end Multiplication

end Algebra

/-! ### Two copies of a unital normed algebra -/

section Unital

variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]

/-- For a unital `B`, the left action is the multiplication by `b ⊗ 1`: `(b ⊗ 1) x = b • x`. -/
lemma tmul_one_mul (b : B) (x : ⨂̂[𝕜]^2 B) :
    tmul b 1 * x = leftAct 𝕜 B b x := by
  have h : ContinuousLinearMap.mul 𝕜 (⨂̂[𝕜]^2 B) (tmul b 1) =
      leftAct 𝕜 B b :=
    ext_tmul fun c c' => by simp [tmul_mul_tmul]
  exact congr($h x)

/-- For a unital `B`, the right action is the multiplication by `1 ⊗ b`: `x (1 ⊗ b) = x • b`. -/
lemma mul_tmul_one (b : B) (x : ⨂̂[𝕜]^2 B) :
    x * tmul 1 b = rightAct 𝕜 B b x := by
  have h : (ContinuousLinearMap.mul 𝕜 (⨂̂[𝕜]^2 B)).flip
      (tmul 1 b) = rightAct 𝕜 B b :=
    ext_tmul fun c c' => by simp [tmul_mul_tmul]
  exact congr($h x)

variable [CompleteSpace B] {d : ⨂̂[𝕜]^2 B}

/-- For a unital `B`, the multiplication `B ⊗̂ B → B` sends a diagonal to `1`. -/
lemma IsDiagonal.mul_eq_one (hd : IsDiagonal d) : mul 𝕜 B d = 1 := by
  simpa using hd.mul_mul_apply 1

/-- The norm of a diagonal is at least that of the unit, the multiplication being contractive. -/
lemma IsDiagonal.norm_one_le (hd : IsDiagonal d) : ‖(1 : B)‖ ≤ ‖d‖ :=
  hd.mul_eq_one ▸ norm_mul_apply_le d

end Unital

/-! ### Averages over finite groups of units -/

section GroupAverage

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]
  {G : Type*} [Group G] [Fintype G] (u : G →* Bˣ)

/-- The **average over a finite group of units** `u : G →* Bˣ`: `|G|⁻¹ ∑ g, (u g)⁻¹ ⊗ u g` in
`B ⊗̂ B`. -/
noncomputable def groupAverage : ⨂̂[𝕜]^2 B :=
  (Fintype.card G : 𝕜)⁻¹ • ∑ g, tmul (↑(u g)⁻¹ : B) (u g : B)

variable {𝕜 u}

/-- The average over a finite group of units commutes with the group: `u h • d_G = d_G • u h`, by
the change of variables `g ↦ g h`. -/
lemma leftAct_groupAverage (h : G) :
    leftAct 𝕜 B (u h) (groupAverage 𝕜 u) = rightAct 𝕜 B (u h) (groupAverage 𝕜 u) := by
  rw [groupAverage, map_smul, map_smul, map_sum, map_sum]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulRight h) _ _ fun k => ?_).symm
  rw [leftAct_tmul, rightAct_tmul, Equiv.coe_mulRight, map_mul, mul_inv_rev, Units.val_mul,
    Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]

variable [CompleteSpace B] (hcard : (Fintype.card G : 𝕜) ≠ 0)

include hcard in
/-- The multiplication `B ⊗̂ B → B` sends the average over a finite group of units to `1`, when the
order of the group is invertible in `𝕜`. -/
lemma mul_groupAverage : mul 𝕜 B (groupAverage 𝕜 u) = 1 := by
  simp only [groupAverage, map_smul, map_sum, mul_tmul, Units.inv_mul, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ hcard, one_smul]

include hcard in
/-- **The average over a finite group of units spanning `B` is a diagonal of `B`**, when the order
of the group is invertible in `𝕜`: it commutes with each unit of the group
(`ProjectiveTensorProduct.leftAct_groupAverage`), hence with their span, and the multiplication
sends it to `1`. -/
theorem isDiagonal_groupAverage (hspan : Submodule.span 𝕜 (Set.range fun g => (u g : B)) = ⊤) :
    IsDiagonal (groupAverage 𝕜 u) := by
  refine ⟨fun b => ?_, fun b => by rw [mul_groupAverage hcard, one_mul]⟩
  have hb : b ∈ Submodule.span 𝕜 (Set.range fun g => (u g : B)) := hspan ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact leftAct_groupAverage g
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, add_apply, add_apply, hx, hy]
  | smul r x _ hx =>
    rw [map_smul, map_smul, smul_apply, smul_apply, hx]

end GroupAverage

section GroupAverage

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]
  {G : Type*} [Group G] [Fintype G] {u : G →* Bˣ}

/-- The average over a finite group of contractive units has norm at most one: it is an average of
pure tensors `(u g)⁻¹ ⊗ u g`, each of norm at most `‖u g⁻¹‖ * ‖u g‖ ≤ 1`. -/
lemma norm_groupAverage_le (hu : ∀ g, ‖(u g : B)‖ ≤ 1) : ‖groupAverage 𝕜 u‖ ≤ 1 := by
  have hcard : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
  rw [groupAverage, norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_le_iff₀ hcard, mul_one]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ g, ‖(tmul (↑(u g)⁻¹ : B) (u g : B) : ⨂̂[𝕜]^2 B)‖
      ≤ ∑ _g : G, (1 : ℝ) := Finset.sum_le_sum fun g _ => (norm_tmul_le _ _).trans <| by
        rw [← map_inv]
        exact (mul_le_mul (hu g⁻¹) (hu g) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ = Fintype.card G := by simp

variable [CompleteSpace B]

/-- **The average over a finite group of contractive units of a nontrivial Banach algebra `B` has
norm one**, over `ℝ` or `ℂ`: at most one as an average of pure tensors of norm at most one, and at least `‖1‖ ≥ 1`
as the multiplication, a contraction, sends it to `1`. -/
theorem norm_groupAverage [Nontrivial B] (hu : ∀ g, ‖(u g : B)‖ ≤ 1) : ‖groupAverage 𝕜 u‖ = 1 := by
  refine le_antisymm (norm_groupAverage_le hu) ?_
  have h := norm_mul_apply_le (groupAverage 𝕜 u)
  rw [mul_groupAverage (Nat.cast_ne_zero.2 Fintype.card_ne_zero)] at h
  exact (one_le_norm_one B).trans h

end GroupAverage

/-! ### The sign vectors of `Fin n → 𝕜` -/

section Sign

variable (𝕜 : Type*) [RCLike 𝕜] (n : ℕ)

/-- The sign vectors `ε ∈ {±1}ⁿ`, as a finite group of units of `Fin n → 𝕜`. -/
noncomputable def signUnits : (Fin n → ℤˣ) →* (Fin n → 𝕜)ˣ :=
  (MulEquiv.piUnits (M := fun _ : Fin n => 𝕜)).symm.toMonoidHom.comp
    (MonoidHom.compLeft (Units.map (Int.castRingHom 𝕜).toMonoidHom) (Fin n))

variable {𝕜 n}

/-- The unit `signUnits 𝕜 n ε` is the vector of the signs `ε i`. -/
@[simp] lemma coe_signUnits_apply (ε : Fin n → ℤˣ) (i : Fin n) :
    (signUnits 𝕜 n ε : Fin n → 𝕜) i = ((ε i : ℤ) : 𝕜) :=
  rfl

/-- A sign vector has norm at most one in the supremum norm. -/
lemma norm_signUnits_le (ε : Fin n → ℤˣ) : ‖(signUnits 𝕜 n ε : Fin n → 𝕜)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [coe_signUnits_apply]
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

/-- The sign vectors span `Fin n → 𝕜`: the `i`-th basis vector is `(1 - ε) / 2` for the sign
vector `ε` that is `-1` at `i` and `1` elsewhere. -/
lemma span_signUnits : Submodule.span 𝕜 (Set.range fun ε => (signUnits 𝕜 n ε : Fin n → 𝕜)) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun v => ?_
  rw [pi_eq_sum_univ v]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h : (fun j => if i = j then (1 : 𝕜) else 0) = (2 : 𝕜)⁻¹ •
      ((signUnits 𝕜 n 1 : Fin n → 𝕜) - signUnits 𝕜 n (Function.update 1 i (-1))) := by
    funext j
    by_cases hij : i = j
    · subst hij
      simp
      norm_num
    · simp [hij, Function.update_of_ne (Ne.symm hij)]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨1, rfl⟩)
    (Submodule.subset_span ⟨_, rfl⟩))

/-- **The average over the sign vectors is a diagonal of `Fin n → 𝕜`**, with the supremum norm:
`2⁻ⁿ ∑ ε, ε ⊗ ε`, the sign vectors being their own inverses. -/
lemma isDiagonal_groupAverage_sign : IsDiagonal (groupAverage 𝕜 (signUnits 𝕜 n)) :=
  isDiagonal_groupAverage (Nat.cast_ne_zero.2 Fintype.card_ne_zero) span_signUnits

/-- The diagonal `groupAverage 𝕜 (signUnits 𝕜 n)` of `Fin n → 𝕜`
(`ProjectiveTensorProduct.isDiagonal_groupAverage_sign`) has norm one for `n ≠ 0`. -/
lemma norm_groupAverage_sign [NeZero n] : ‖groupAverage 𝕜 (signUnits 𝕜 n)‖ = 1 :=
  norm_groupAverage norm_signUnits_le

end Sign

/-! ### The sequences vanishing at infinity -/

section ZeroAtInfty

variable (𝕜 : Type*) [RCLike 𝕜] (N : ℕ)

/-- The extension by zero `(Fin N → 𝕜) →L[𝕜] C₀(ℕ, 𝕜)`, `v ↦ (v 0, …, v (N - 1), 0, 0, …)`, of norm
at most one. -/
noncomputable def extendByZero : (Fin N → 𝕜) →L[𝕜] C₀(ℕ, 𝕜) :=
  LinearMap.mkContinuous
    { toFun v :=
        { toFun n := if h : n < N then v ⟨n, h⟩ else 0
          continuous_toFun := continuous_of_discreteTopology
          zero_at_infty' := by
            rw [cocompact_eq_atTop]
            exact tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => by simp [not_lt.2 hn] }
      map_add' v w := by
        ext n
        simp only [ZeroAtInftyContinuousMap.coe_mk, ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
        split_ifs <;> simp
      map_smul' r v := by
        ext n
        simp only [ZeroAtInftyContinuousMap.coe_mk, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
    1 fun v => by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, one_mul]
      refine (BoundedContinuousFunction.norm_le (norm_nonneg v)).2 fun n => ?_
      change ‖if h : n < N then v ⟨n, h⟩ else 0‖ ≤ ‖v‖
      split_ifs with h
      · exact norm_le_pi_norm v _
      · simp

variable {𝕜 N}

/-- `extendByZero 𝕜 N v n` is `v n` for `n < N` and `0` otherwise. -/
lemma extendByZero_apply (v : Fin N → 𝕜) (n : ℕ) :
    extendByZero 𝕜 N v n = if h : n < N then v ⟨n, h⟩ else 0 :=
  rfl

/-- The extension by zero has norm at most one. -/
lemma norm_extendByZero_le : ‖extendByZero 𝕜 N‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The extension by zero is multiplicative. -/
lemma extendByZero_mul (v w : Fin N → 𝕜) :
    extendByZero 𝕜 N (v * w) = extendByZero 𝕜 N v * extendByZero 𝕜 N w := by
  ext n
  simp only [ZeroAtInftyContinuousMap.coe_mul, Pi.mul_apply, extendByZero_apply]
  split_ifs <;> simp

/-- Multiplying an extension by zero on the left by `b` multiplies the vector by the first `N`
values of `b`. -/
lemma mul_extendByZero (b : C₀(ℕ, 𝕜)) (v : Fin N → 𝕜) :
    b * extendByZero 𝕜 N v = extendByZero 𝕜 N ((fun i : Fin N => b i) * v) := by
  ext n
  simp only [ZeroAtInftyContinuousMap.coe_mul, Pi.mul_apply, extendByZero_apply]
  split_ifs <;> simp

/-- Multiplying an extension by zero on the right by `b` multiplies the vector by the first `N`
values of `b`. -/
lemma extendByZero_mul_right (b : C₀(ℕ, 𝕜)) (v : Fin N → 𝕜) :
    extendByZero 𝕜 N v * b = extendByZero 𝕜 N (v * fun i : Fin N => b i) := by
  ext n
  simp only [ZeroAtInftyContinuousMap.coe_mul, Pi.mul_apply, extendByZero_apply]
  split_ifs <;> simp

variable (𝕜 N) in
/-- The **truncated diagonal** `∑_{k < N} e_k ⊗ e_k` of `C₀(ℕ, 𝕜)`, `e_k` the `k`-th coordinate
sequence: the image of the average over the sign vectors of `Fin N → 𝕜` under the extension by
zero. -/
noncomputable def truncDiagonal : ⨂̂[𝕜]^2 C₀(ℕ, 𝕜) :=
  map ![extendByZero 𝕜 N, extendByZero 𝕜 N] (groupAverage 𝕜 (signUnits 𝕜 N))

/-- The truncated diagonal has norm at most one. -/
lemma norm_truncDiagonal_le : ‖truncDiagonal 𝕜 N‖ ≤ 1 := by
  refine (norm_map_le _ _).trans ?_
  rw [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h : ‖extendByZero 𝕜 N‖ * ‖extendByZero 𝕜 N‖ ≤ 1 :=
    (mul_le_mul norm_extendByZero_le norm_extendByZero_le (ContinuousLinearMap.opNorm_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  exact (mul_le_mul h (norm_groupAverage_le norm_signUnits_le) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- The truncated diagonal commutes with `C₀(ℕ, 𝕜)`: `b • d_N = d_N • b`. -/
lemma leftAct_truncDiagonal (b : C₀(ℕ, 𝕜)) :
    leftAct 𝕜 C₀(ℕ, 𝕜) b (truncDiagonal 𝕜 N) = rightAct 𝕜 C₀(ℕ, 𝕜) b (truncDiagonal 𝕜 N) := by
  let E : Fin 2 → (Fin N → 𝕜) →L[𝕜] C₀(ℕ, 𝕜) := ![extendByZero 𝕜 N, extendByZero 𝕜 N]
  have hl : (leftAct 𝕜 C₀(ℕ, 𝕜) b).comp (map E) =
      (map E).comp (leftAct 𝕜 (Fin N → 𝕜) fun i : Fin N => b i) :=
    ext_tmul fun c c' => by simp [E, map_tmul, mul_extendByZero]
  have hr : (rightAct 𝕜 C₀(ℕ, 𝕜) b).comp (map E) =
      (map E).comp (rightAct 𝕜 (Fin N → 𝕜) fun i : Fin N => b i) :=
    ext_tmul fun c c' => by simp [E, map_tmul, extendByZero_mul_right]
  have h := congr($hl (groupAverage 𝕜 (signUnits 𝕜 N)))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    isDiagonal_groupAverage_sign.leftAct_eq_rightAct, ← ContinuousLinearMap.comp_apply (map E),
    ← hr, ContinuousLinearMap.comp_apply] at h
  exact h

/-- The multiplication sends the truncated diagonal to the indicator of `{0, …, N - 1}`. -/
lemma mul_truncDiagonal : mul 𝕜 C₀(ℕ, 𝕜) (truncDiagonal 𝕜 N) = extendByZero 𝕜 N 1 := by
  have h : (mul 𝕜 C₀(ℕ, 𝕜)).comp (map ![extendByZero 𝕜 N, extendByZero 𝕜 N]) =
      (extendByZero 𝕜 N).comp (mul 𝕜 (Fin N → 𝕜)) :=
    ext_tmul fun c c' => by simp [map_tmul, extendByZero_mul]
  have := congr($h (groupAverage 𝕜 (signUnits 𝕜 N)))
  simpa [truncDiagonal, mul_groupAverage] using this

/-- The indicators of `{0, …, N - 1}` form an approximate unit of `C₀(ℕ, 𝕜)`. -/
lemma tendsto_extendByZero_one_mul (b : C₀(ℕ, 𝕜)) :
    Tendsto (fun N => extendByZero 𝕜 N 1 * b) atTop (𝓝 b) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hb : Tendsto b atTop (𝓝 0) := cocompact_eq_atTop (α := ℕ) ▸ b.zero_at_infty'
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hb (ε / 2) (half_pos hε)
  refine ⟨N₀, fun N hN => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (half_pos hε).le).2 fun n => ?_
  change ‖extendByZero 𝕜 N 1 n * b n - b n‖ ≤ ε / 2
  rw [extendByZero_apply]
  split_ifs with h
  · simpa using (half_pos hε).le
  · have := hN₀ n (hN.trans (not_lt.1 h))
    rw [dist_zero_right] at this
    simpa using this.le

/-- **`C₀(ℕ, 𝕜)` has no diagonal**: the image of a diagonal under the multiplication would be a
unit of `C₀(ℕ, 𝕜)`, taking the value `1` at every `n`, while it vanishes at infinity. -/
theorem not_isDiagonal_zeroAtInfty (d : ⨂̂[𝕜]^2 C₀(ℕ, 𝕜)) :
    ¬ IsDiagonal d := by
  intro hd
  have hu : ⇑(mul 𝕜 C₀(ℕ, 𝕜) d) = fun _ => 1 := funext fun n => by
    have := congr($(hd.mul_apply_mul (extendByZero 𝕜 (n + 1) 1)) n)
    simpa [extendByZero_apply] using this
  have ht : Tendsto (mul 𝕜 C₀(ℕ, 𝕜) d) atTop (𝓝 0) :=
    cocompact_eq_atTop (α := ℕ) ▸ (mul 𝕜 C₀(ℕ, 𝕜) d).zero_at_infty'
  rw [hu] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- **The truncated diagonals form a bounded approximate diagonal of `C₀(ℕ, 𝕜)`**, which has no
diagonal (`ProjectiveTensorProduct.not_isDiagonal_zeroAtInfty`): they commute with `C₀(ℕ, 𝕜)`, have norm at
most one, and their images under the multiplication, the indicators of `{0, …, N - 1}`, form an
approximate unit. -/
theorem isBoundedApproximateDiagonal_truncDiagonal :
    IsBoundedApproximateDiagonal (truncDiagonal 𝕜) atTop where
  bounded := ⟨1, fun _ => norm_truncDiagonal_le⟩
  tendsto_commutator b := by
    simp only [leftAct_truncDiagonal, sub_self]
    exact tendsto_const_nhds
  tendsto_mul_apply_mul b := by
    simpa only [mul_truncDiagonal] using tendsto_extendByZero_one_mul b
  neBot := atTop_neBot

end ZeroAtInfty

end ProjectiveTensorProduct
