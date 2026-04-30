module

public import QuantumSystem.State

/-!
# Quantum Channels (Completely Positive Trace-Preserving Maps)

This file defines quantum channels on finite-dimensional matrix algebras and establishes
their basic properties. A quantum channel is a linear map Φ: M_n(ℂ) → M_m(ℂ) that is:
1. Completely positive (CP): Has a Kraus representation Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ†
2. Trace-preserving (TP): Tr(Φ(A)) = Tr(A) for all A, equivalently Σᵢ Kᵢ† Kᵢ = I

## Main definitions

* `IsTracePreserving`: A linear map preserves trace.
* `IsCompletelyPositive`: A linear map has a Kraus representation.
* `IsQuantumChannel`: A linear map is both CP and TP.

## Mathematical Background

### Choi-Kraus Theorem
A linear map Φ: M_n(ℂ) → M_m(ℂ) is completely positive if and only if it has a
Kraus representation:
  Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ†
where Kᵢ: ℂⁿ → ℂᵐ are linear maps (Kraus operators).

The map is trace-preserving if and only if:
  Σᵢ Kᵢ† Kᵢ = I

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Chapter 8
* Watrous, *The Theory of Quantum Information*, Chapter 2
-/

@[expose] public section

namespace Matrix

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]

open scoped ComplexOrder

/-! ### Trace-Preserving Maps -/

/-- A linear map is trace-preserving if Tr(Φ(A)) = Tr(A) for all A. -/
def IsTracePreserving (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ A : Matrix n n ℂ, Tr (Φ A) = Tr A

/-! ### Completely Positive Maps -/

/-- A linear map is completely positive if it has a Kraus representation.
This is equivalent to the Choi matrix being positive semi-definite. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix m n ℂ),
    ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ

/-! ### Quantum Channels -/

/-- A quantum channel is a completely positive trace-preserving (CPTP) map.
These are the physically realizable operations on quantum states. -/
structure IsQuantumChannel (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop where
  /-- The map is completely positive -/
  completelyPositive : IsCompletelyPositive Φ
  /-- The map preserves trace -/
  tracePreserving : IsTracePreserving Φ

/-- Quantum channel as a subtype for cleaner API. -/
abbrev QuantumChannel (n : Type*) (m : Type*) [Fintype n] [Fintype m] :=
  { Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ // IsQuantumChannel Φ }

/-- The identity map is a quantum channel. -/
theorem isQuantumChannel_id : IsQuantumChannel (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) where
  completelyPositive := by
    classical
    -- id has Kraus representation with single operator K = I
    use 1, fun _ => 1
    intro A
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    simp [Matrix.conjTranspose_one]
  tracePreserving := fun _ => rfl

/-- Composition of quantum channels is a quantum channel. -/
theorem QuantumChannel.comp
    (Φ : QuantumChannel n m) (Ψ : QuantumChannel m k) :
    IsQuantumChannel (Ψ.val.comp Φ.val) where
  completelyPositive := by
    classical
    -- Composition of CP maps is CP
    -- If Φ(A) = Σᵢ Kᵢ A Kᵢ† and Ψ(B) = Σⱼ Lⱼ B Lⱼ†
    -- Then (Ψ∘Φ)(A) = Σⱼ Lⱼ (Σᵢ Kᵢ A Kᵢ†) Lⱼ† = Σᵢⱼ (Lⱼ Kᵢ) A (Lⱼ Kᵢ)†
    obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
    obtain ⟨s, L, hL⟩ := Ψ.property.completelyPositive
    -- Use product Kraus operators indexed by Fin s × Fin r
    use s * r
    -- Define the combined Kraus operators via equivalence Fin (s * r) ≃ Fin s × Fin r
    let e : Fin (s * r) ≃ Fin s × Fin r := finProdFinEquiv.symm
    use fun p => L (e p).1 * K (e p).2
    intro A
    simp only [LinearMap.comp_apply, hK, hL]
    -- Ψ(Σᵢ Kᵢ A Kᵢ†) = Σⱼ Lⱼ (Σᵢ Kᵢ A Kᵢ†) Lⱼ†
    simp_rw [Matrix.mul_sum, Matrix.sum_mul]
    -- Reindex: ∑_{j,i} = ∑_p via Equiv.sum_comp
    rw [← Fintype.sum_prod_type']
    rw [(Equiv.sum_comp e (fun x => L x.1 * (K x.2 * A * (K x.2)ᴴ) * (L x.1)ᴴ)).symm]
    apply Finset.sum_congr rfl
    intro p _
    -- Need to show: L (e p).1 * (K (e p).2 * A * (K (e p).2)†) * (L (e p).1)†
    --             = L (e p).1 * K (e p).2 * A * (L (e p).1 * K (e p).2)†
    rw [Matrix.conjTranspose_mul]
    -- Now use matrix associativity
    simp only [Matrix.mul_assoc]
  tracePreserving := by
    intro A
    simp only [LinearMap.comp_apply]
    rw [Ψ.property.tracePreserving, Φ.property.tracePreserving]

omit [Fintype m] in
/-- A completely positive map preserves Hermitianity of matrices.
If Φ(A) = Σᵢ Kᵢ A Kᵢ† and A is Hermitian, then Φ(A) is Hermitian. -/
theorem IsCompletelyPositive.map_isHermitian
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hΦ : IsCompletelyPositive Φ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A).IsHermitian := by
  classical
  obtain ⟨r, K, hK⟩ := hΦ
  rw [hK]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]
  congr 1
  rw [hA.eq]

/-- Apply a quantum channel to a density matrix. -/
noncomputable def QuantumChannel.apply [DecidableEq n] [DecidableEq m]
    (Φ : QuantumChannel n m) (ρ : DensityMatrix n) :
    DensityMatrix m where
  toMatrix := Φ.val ↑ρ
  posSemidef := by
    classical
    obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
    rw [hK]
    apply posSemidef_sum
    intro i _
    exact ρ.posSemidef.mul_mul_conjTranspose_same (K i)
  trace_eq_one := by
    rw [Φ.property.tracePreserving]
    exact ρ.trace_eq_one
/-- Quantum channels can be applied as functions from density matrices to density matrices. -/
noncomputable instance [DecidableEq n] [DecidableEq m] : CoeFun (QuantumChannel n m)
    (fun _ => DensityMatrix n → DensityMatrix m) where
  coe := QuantumChannel.apply

/-! ### Kraus Completeness -/

/-- If `Tr(M * A) = Tr(A)` for all `A`, then `M = 1`. -/
private lemma matrix_eq_one_of_trace_mul [DecidableEq n]
    (M : Matrix n n ℂ) (h : ∀ A : Matrix n n ℂ, Tr (M * A) = Tr A) : M = 1 :=
  Matrix.ext_iff_trace_mul_right.mpr fun A => by rw [one_mul]; exact h A

/-- Trace-preserving Kraus channels satisfy the completeness relation: ∑ₖ Kₖ† Kₖ = I. -/
theorem QuantumChannel.kraus_sum_eq_one [DecidableEq n]
    (Φ : QuantumChannel n m)
    {r : ℕ} {K : Fin r → Matrix m n ℂ} (hK : ∀ A, Φ.val A = ∑ i, K i * A * (K i)ᴴ) :
    ∑ i, (K i)ᴴ * K i = 1 := by
  apply matrix_eq_one_of_trace_mul
  intro A
  have key : ∀ i : Fin r, ((K i)ᴴ * K i * A).trace = (K i * A * (K i)ᴴ).trace := fun i => by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (K i)ᴴ]
  rw [Finset.sum_mul]
  simp_rw [Matrix.trace_sum, key, ← Matrix.trace_sum]
  have := Φ.property.tracePreserving A
  rwa [hK] at this

/-! ### Stinespring Isometry -/

/-- Stinespring isometry: stack Kraus operators into a single isometry
V : Matrix (Fin r × m) n ℂ defined by V (i, a) b = Kᵢ a b.
Then V†V = I (from Kraus completeness) and Φ(A) = Σᵢ (i-th block of VAV†). -/
noncomputable def stinespringIsometry {r : ℕ} (K : Fin r → Matrix m n ℂ) :
    Matrix (Fin r × m) n ℂ :=
  Matrix.of fun ⟨i, a⟩ b => K i a b

omit [Fintype n] in
lemma stinespringIsometry_conjTranspose_mul {r : ℕ} [DecidableEq n]
    {K : Fin r → Matrix m n ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (stinespringIsometry K)ᴴ * stinespringIsometry K = 1 := by
  ext a b
  simp only [stinespringIsometry, Matrix.conjTranspose_apply, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
  have heq : ∀ i, ∑ j : m, star (K i j a) * K i j b = ((K i)ᴴ * K i) a b := fun i => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [heq, ← Finset.sum_apply, hK, Matrix.one_apply]

end Matrix
