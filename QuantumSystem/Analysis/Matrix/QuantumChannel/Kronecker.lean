/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.RingTheory.MatrixAlgebra
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Kraus
public import QuantumSystem.Analysis.Matrix.QuantumChannel.PartialTrace

/-!
# Tensor products of quantum channels

The tensor product `Φ ⊗ Ψ` of linear maps `Φ : M_n(ℂ) → M_m(ℂ)` and `Ψ : M_{n'}(ℂ) → M_{m'}(ℂ)` is
the linear map on `M_{n × n'}(ℂ)` determined by `(Φ ⊗ Ψ)(X ⊗ Y) = Φ(X) ⊗ Ψ(Y)`: the map
`TensorProduct.map Φ Ψ` transported along the Kronecker isomorphism
`Matrix.kroneckerLinearEquiv : M_n(ℂ) ⊗ M_{n'}(ℂ) ≃ M_{n × n'}(ℂ)`. Kraus operators `Kₐ` of `Φ` and
`L_b` of `Ψ` give the Kraus operators `Kₐ ⊗ L_b` of `Φ ⊗ Ψ`, so the tensor product of two quantum
channels is a quantum channel.

With the identity channel this is the channel `id_A ⊗ Tr_C` that takes a tripartite state on
`A × (B × C)` to its `A × B` marginal.

## Main definitions

* `Matrix.kroneckerLinearMap`: the tensor product `Φ ⊗ Ψ` of two linear maps on matrices.
* `Matrix.QuantumChannel.kronecker`: the tensor product `Φ ⊗ Ψ` of two quantum channels, with
  notation `Φ ⊗ Ψ` in scope `Kronecker`.

## Main statements

* `Matrix.kroneckerLinearMap_eq_sum_kraus`: `Φ ⊗ Ψ` has the Kraus operators `Kₐ ⊗ L_b`.
* `Matrix.QuantumChannel.kronecker_apply_kronecker`: `(Φ ⊗ Ψ)(X ⊗ Y) = Φ(X) ⊗ Ψ(Y)`.
* `Matrix.QuantumChannel.traceRight_kronecker_apply`,
  `Matrix.QuantumChannel.traceLeft_kronecker_apply`: partial traces intertwine `Φ ⊗ Ψ` with its
  factors, `tr₂ ∘ (Φ ⊗ Ψ) = Φ ∘ tr₂` and `tr₁ ∘ (Φ ⊗ Ψ) = Ψ ∘ tr₁`.

## TODO

The tensor product here is stated only for matrix algebras, through the Kronecker isomorphism.
It should be abstracted in two stages, without transporting along orthonormal bases:

* **Bounded operators on finite-dimensional Hilbert spaces.** For completely positive maps
  `Φ : B(H) → B(K)` and `Ψ : B(H') → B(K')`, define `Φ ⊗ Ψ : B(H ⊗ H') → B(K ⊗ K')` on Mathlib's
  inner product space `H ⊗[ℂ] H'`, determined by `(Φ ⊗ Ψ)(A ⊗ B) = Φ(A) ⊗ Ψ(B)` with the operator
  tensor product `ContinuousLinearMap.tensor`. Complete positivity needs the Kraus or Choi
  representation for maps on `B(H)`, which exists here only for matrices.
* **General C⋆-algebras.** For completely positive maps `φ : A₁ → A₂` and `ψ : B₁ → B₂`, define
  `φ ⊗ ψ : A₁ ⊗_min B₁ → A₂ ⊗_min B₂` on the minimal (spatial) C⋆-tensor product, and prove it
  completely positive through the Stinespring dilation
  (`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/Stinespring.lean`). Mathlib gives
  `A ⊗[ℂ] B` only its star-algebra structure; the C⋆-norm of `A ⊗_min B` is not yet available.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §8.2.3
* Watrous, *The Theory of Quantum Information*, §2.2.2
-/

@[expose] public section

namespace Matrix

open scoped Kronecker TensorProduct

variable {n m n' m' : Type*} [Fintype n] [Fintype m] [Fintype n'] [Fintype m']
  [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m']

/-! ### Tensor product of linear maps on matrices -/

/-- The **tensor product** `Φ ⊗ Ψ` of linear maps on matrices: `TensorProduct.map Φ Ψ` transported
along the Kronecker isomorphism `M_n(ℂ) ⊗ M_{n'}(ℂ) ≃ M_{n × n'}(ℂ)`. -/
noncomputable def kroneckerLinearMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (Ψ : Matrix n' n' ℂ →ₗ[ℂ] Matrix m' m' ℂ) :
    Matrix (n × n') (n × n') ℂ →ₗ[ℂ] Matrix (m × m') (m × m') ℂ :=
  (kroneckerLinearEquiv m m m' m' ℂ).toLinearMap ∘ₗ TensorProduct.map Φ Ψ ∘ₗ
    (kroneckerLinearEquiv n n n' n' ℂ).symm.toLinearMap

/-- `(Φ ⊗ Ψ)(X ⊗ Y) = Φ(X) ⊗ Ψ(Y)`. -/
@[simp] lemma kroneckerLinearMap_kronecker (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (Ψ : Matrix n' n' ℂ →ₗ[ℂ] Matrix m' m' ℂ) (X : Matrix n n ℂ) (Y : Matrix n' n' ℂ) :
    kroneckerLinearMap Φ Ψ (X ⊗ₖ Y) = Φ X ⊗ₖ Ψ Y := by
  simp [kroneckerLinearMap]

omit [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n'] in
/-- Two linear maps out of `M_{n × n'}(ℂ)` that agree on Kronecker products `X ⊗ Y` are equal. -/
lemma linearMap_ext_kronecker [Finite n] [Finite n'] {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {f g : Matrix (n × n') (n × n') ℂ →ₗ[ℂ] M} (h : ∀ X Y, f (X ⊗ₖ Y) = g (X ⊗ₖ Y)) : f = g := by
  classical
  have := Fintype.ofFinite n
  have := Fintype.ofFinite n'
  have : f ∘ₗ (kroneckerLinearEquiv n n n' n' ℂ).toLinearMap =
      g ∘ₗ (kroneckerLinearEquiv n n n' n' ℂ).toLinearMap :=
    TensorProduct.ext' fun X Y => by simpa using h X Y
  ext M
  simpa using LinearMap.congr_fun this ((kroneckerLinearEquiv n n n' n' ℂ).symm M)

/-- **Kraus operators of a tensor product.** If `Φ(A) = Σₐ Kₐ A Kₐᴴ` and `Ψ(B) = Σ_b L_b B L_bᴴ`,
then `(Φ ⊗ Ψ)(M) = Σ_{a,b} (Kₐ ⊗ L_b) M (Kₐ ⊗ L_b)ᴴ`. -/
lemma kroneckerLinearMap_eq_sum_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    {Ψ : Matrix n' n' ℂ →ₗ[ℂ] Matrix m' m' ℂ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K : ι → Matrix m n ℂ} {L : κ → Matrix m' n' ℂ} (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ)
    (hL : ∀ B, Ψ B = ∑ b, L b * B * (L b)ᴴ) (M : Matrix (n × n') (n × n') ℂ) :
    kroneckerLinearMap Φ Ψ M = ∑ p : ι × κ, (K p.1 ⊗ₖ L p.2) * M * (K p.1 ⊗ₖ L p.2)ᴴ := by
  rw [← (kroneckerLinearEquiv n n n' n' ℂ).apply_symm_apply M]
  induction (kroneckerLinearEquiv n n n' n' ℂ).symm M using TensorProduct.inductionOn with
  | tmul X Y =>
    simp only [kroneckerLinearEquiv_tmul, kroneckerLinearMap_kronecker, hK, hL,
      conjTranspose_kronecker, ← mul_kronecker_mul, Fintype.sum_prod_type]
    ext i j
    simp only [kroneckerMap_apply, sum_apply, Finset.sum_mul_sum]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

/-! ### Tensor product of quantum channels -/

namespace QuantumChannel

open scoped Matrix.Norms.L2Operator MatrixOrder

/-- The **tensor product** `Φ ⊗ Ψ` of quantum channels, determined by
`(Φ ⊗ Ψ)(X ⊗ Y) = Φ(X) ⊗ Ψ(Y)` (`Matrix.QuantumChannel.kronecker_apply_kronecker`). It is
completely positive and trace preserving because Kraus operators `Kₐ` of `Φ` and `L_b` of `Ψ` give
the Kraus operators `Kₐ ⊗ L_b` of `Φ ⊗ Ψ` (`Matrix.kroneckerLinearMap_eq_sum_kraus`). -/
noncomputable def kronecker (Φ : QuantumChannel n m) (Ψ : QuantumChannel n' m') :
    QuantumChannel (n × n') (m × m') where
  toLinearMap := kroneckerLinearMap Φ.toLinearMap Ψ.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    obtain ⟨K, hK, -⟩ := Φ.exists_kraus
    obtain ⟨L, hL, -⟩ := Ψ.exists_kraus
    exact (CompletelyPositiveMap.ofKraus _ _
      (kroneckerLinearMap_eq_sum_kraus hK hL)).map_cstarMatrix_nonneg' k M hM
  isTracePreserving' := by
    obtain ⟨K, hK, hKK⟩ := Φ.exists_kraus
    obtain ⟨L, hL, hLL⟩ := Ψ.exists_kraus
    refine isTracePreserving_of_kraus (kroneckerLinearMap_eq_sum_kraus hK hL) ?_
    simp only [conjTranspose_kronecker, ← mul_kronecker_mul, Fintype.sum_prod_type]
    rw [← one_kronecker_one, ← hKK, ← hLL]
    ext i j
    simp only [kroneckerMap_apply, sum_apply, Finset.sum_mul_sum]

@[inherit_doc Matrix.QuantumChannel.kronecker]
scoped[Kronecker] infixl:100 (name := quantumChannelKronecker) " ⊗ " =>
  Matrix.QuantumChannel.kronecker

/-- The tensor product channel `Φ ⊗ Ψ` acts as the tensor product `Matrix.kroneckerLinearMap` of
the underlying linear maps. -/
lemma coe_kronecker (Φ : QuantumChannel n m) (Ψ : QuantumChannel n' m') :
    ⇑(Φ ⊗ Ψ) = kroneckerLinearMap Φ.toLinearMap Ψ.toLinearMap :=
  rfl

/-- `(Φ ⊗ Ψ)(X ⊗ Y) = Φ(X) ⊗ Ψ(Y)`. -/
@[simp] lemma kronecker_apply_kronecker (Φ : QuantumChannel n m) (Ψ : QuantumChannel n' m')
    (X : Matrix n n ℂ) (Y : Matrix n' n' ℂ) : (Φ ⊗ Ψ) (X ⊗ₖ Y) = Φ X ⊗ₖ Ψ Y :=
  kroneckerLinearMap_kronecker _ _ X Y

/-- Tracing out the right factor intertwines `Φ ⊗ Ψ` with `Φ`: `tr₂((Φ ⊗ Ψ)(M)) = Φ(tr₂ M)`. -/
lemma traceRight_kronecker_apply (Φ : QuantumChannel n m) (Ψ : QuantumChannel n' m')
    (M : Matrix (n × n') (n × n') ℂ) : traceRight ((Φ ⊗ Ψ) M) = Φ (traceRight M) := by
  have h : traceRightLinearMap ℂ ∘ₗ kroneckerLinearMap Φ.toLinearMap Ψ.toLinearMap =
      Φ.toLinearMap ∘ₗ traceRightLinearMap ℂ := by
    refine linearMap_ext_kronecker fun X Y => ?_
    simp only [LinearMap.comp_apply, kroneckerLinearMap_kronecker, traceRightLinearMap_apply,
      traceRight_kronecker, map_smul]
    exact congrArg (· • _) (Ψ.trace_map Y)
  exact LinearMap.congr_fun h M

/-- Tracing out the left factor intertwines `Φ ⊗ Ψ` with `Ψ`: `tr₁((Φ ⊗ Ψ)(M)) = Ψ(tr₁ M)`. -/
lemma traceLeft_kronecker_apply (Φ : QuantumChannel n m) (Ψ : QuantumChannel n' m')
    (M : Matrix (n × n') (n × n') ℂ) : traceLeft ((Φ ⊗ Ψ) M) = Ψ (traceLeft M) := by
  have h : traceLeftLinearMap ℂ ∘ₗ kroneckerLinearMap Φ.toLinearMap Ψ.toLinearMap =
      Ψ.toLinearMap ∘ₗ traceLeftLinearMap ℂ := by
    refine linearMap_ext_kronecker fun X Y => ?_
    simp only [LinearMap.comp_apply, kroneckerLinearMap_kronecker, traceLeftLinearMap_apply,
      traceLeft_kronecker, map_smul]
    exact congrArg (· • _) (Φ.trace_map X)
  exact LinearMap.congr_fun h M

end QuantumChannel

end Matrix
