/-
Copyright (c) 2026 QuantumSystem Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuantumSystem Contributors
-/
module

public import QuantumSystem.Algebra.Linear.Unbounded.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoint of Densely Defined Linear Operators

This file develops the theory of adjoints of densely defined linear operators on Hilbert spaces.

## Main definitions

* `DenselyDefinedLinearMap.adjointDomain`: The domain of the adjoint operator
* `DenselyDefinedLinearMap.adjointValue`: The value of the adjoint at a point in the domain

## Important note

The adjoint of a densely defined linear operator is naturally a **linear** map from
dom(T*) to H. The condition `⟨Tx, y⟩ = ⟨x, T*y⟩` determines T*y uniquely from y.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reed1980]
-/

@[expose] public section

namespace DenselyDefinedLinearMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Helper lemma for uniqueness -/

/-- If inner product with all elements of dense set is zero, then the vector is zero. -/
theorem inner_eq_zero_of_forall_mem_dense [CompleteSpace H] {S : Set H} (hS : Dense S)
    {y : H} (h : ∀ v ∈ S, @inner 𝕜 H _ v y = 0) : y = 0 := by
  rw [← inner_self_eq_zero (𝕜 := 𝕜)]
  have h_closed : IsClosed { v : H | @inner 𝕜 H _ v y = 0 } := by
    apply isClosed_eq
    · exact continuous_inner.comp (Continuous.prodMk continuous_id continuous_const)
    · exact continuous_const
  have h_sub : S ⊆ { v : H | @inner 𝕜 H _ v y = 0 } := fun v hv => h v hv
  have h_all : ∀ v : H, @inner 𝕜 H _ v y = 0 := by
    intro v
    have := h_closed.closure_subset_iff.mpr h_sub
    rw [hS.closure_eq] at this
    exact this (Set.mem_univ v)
  exact h_all y

/-! ### Adjoint Domain -/

section AdjointDomain

variable (T : OnHilbertSpace 𝕜 H)

/-- A vector `y` is in the domain of the adjoint of `T` if there exists a vector `z` such that
for all `x` in the domain of `T`, we have `⟨Tx, y⟩ = ⟨x, z⟩`. -/
def InAdjointDomain (y : H) : Prop :=
  ∃ z : H, ∀ x : T.dom, @inner 𝕜 H _ (T x) y = @inner 𝕜 H _ (x : H) z

/-- The domain of the adjoint of `T` as a set. -/
def adjointDomainSet : Set H :=
  { y : H | InAdjointDomain T y }

variable {T}

/-- Zero is always in the adjoint domain. -/
theorem zero_mem_adjointDomainSet : (0 : H) ∈ adjointDomainSet T := by
  use 0
  intro x
  simp only [inner_zero_right]

/-- The adjoint domain is closed under addition. -/
theorem add_mem_adjointDomainSet {y₁ y₂ : H}
    (hy₁ : y₁ ∈ adjointDomainSet T) (hy₂ : y₂ ∈ adjointDomainSet T) :
    y₁ + y₂ ∈ adjointDomainSet T := by
  obtain ⟨z₁, hz₁⟩ := hy₁
  obtain ⟨z₂, hz₂⟩ := hy₂
  use z₁ + z₂
  intro x
  rw [inner_add_right, inner_add_right, hz₁, hz₂]

/-- The adjoint domain is closed under scalar multiplication. -/
theorem smul_mem_adjointDomainSet {y : H} (c : 𝕜)
    (hy : y ∈ adjointDomainSet T) : c • y ∈ adjointDomainSet T := by
  obtain ⟨z, hz⟩ := hy
  use c • z
  intro x
  -- ⟨Tx, c•y⟩ = conj(c) * ⟨Tx, y⟩ = conj(c) * ⟨x, z⟩
  -- ⟨x, c•z⟩ = conj(c) * ⟨x, z⟩
  simp only [inner_smul_right, hz]

/-- The adjoint domain is closed under negation. -/
theorem neg_mem_adjointDomainSet {y : H}
    (hy : y ∈ adjointDomainSet T) : -y ∈ adjointDomainSet T := by
  obtain ⟨z, hz⟩ := hy
  use -z
  intro x
  rw [inner_neg_right, inner_neg_right, hz]

/-- The domain of the adjoint as a submodule. -/
def adjointDomain (T : OnHilbertSpace 𝕜 H) : Submodule 𝕜 H where
  carrier := adjointDomainSet T
  add_mem' := add_mem_adjointDomainSet
  zero_mem' := zero_mem_adjointDomainSet
  smul_mem' c _ := smul_mem_adjointDomainSet c

@[simp]
theorem mem_adjointDomain (y : H) :
    y ∈ adjointDomain T ↔ InAdjointDomain T y := Iff.rfl

end AdjointDomain

/-! ### Adjoint operator -/

section AdjointValue

/-- The value of `T*y` for `y` in the adjoint domain, chosen via Classical.choose. -/
noncomputable def adjointValue (T : OnHilbertSpace 𝕜 H) (y : adjointDomain T) : H :=
  Classical.choose y.2

theorem adjointValue_spec (T : OnHilbertSpace 𝕜 H) (y : adjointDomain T) :
    ∀ x : T.dom, @inner 𝕜 H _ (T x) y = @inner 𝕜 H _ (x : H) (adjointValue T y) :=
  Classical.choose_spec y.2

end AdjointValue

section Adjoint

variable [CompleteSpace H]

/-- For `y` in the adjoint domain of `T`, the adjoint value `T*y` is uniquely determined
by the density of dom(T). -/
theorem adjoint_value_unique (T : OnHilbertSpace 𝕜 H) {y z₁ z₂ : H}
    (hz₁ : ∀ x : T.dom, @inner 𝕜 H _ (T x) y = @inner 𝕜 H _ (x : H) z₁)
    (hz₂ : ∀ x : T.dom, @inner 𝕜 H _ (T x) y = @inner 𝕜 H _ (x : H) z₂) :
    z₁ = z₂ := by
  have h : ∀ x : T.dom, @inner 𝕜 H _ (x : H) (z₁ - z₂) = 0 := by
    intro x
    rw [inner_sub_right, ← hz₁ x, ← hz₂ x, sub_self]
  rw [← sub_eq_zero]
  apply inner_eq_zero_of_forall_mem_dense (𝕜 := 𝕜) T.dense_dom
  intro v hv
  exact h ⟨v, hv⟩

/-- The adjoint is additive. -/
theorem adjointValue_add (T : OnHilbertSpace 𝕜 H) (y₁ y₂ : adjointDomain T) :
    adjointValue T ⟨(y₁ : H) + y₂, add_mem_adjointDomainSet y₁.2 y₂.2⟩ =
    adjointValue T y₁ + adjointValue T y₂ := by
  apply adjoint_value_unique T (adjointValue_spec T ⟨(y₁ : H) + y₂, _⟩)
  intro x
  rw [inner_add_right, adjointValue_spec T y₁, adjointValue_spec T y₂, inner_add_right]

/-- The adjoint respects scalar multiplication.
The adjoint is a *linear* map: T*(cy) = c · T*y. -/
theorem adjointValue_smul (T : OnHilbertSpace 𝕜 H) (c : 𝕜) (y : adjointDomain T) :
    adjointValue T ⟨c • (y : H), smul_mem_adjointDomainSet c y.2⟩ =
    c • adjointValue T y := by
  apply adjoint_value_unique T (adjointValue_spec T ⟨c • (y : H), _⟩)
  intro x
  -- ⟨T x, c • y⟩ = conj(c) * ⟨T x, y⟩ = conj(c) * ⟨x, T*y⟩
  -- ⟨x, c • T*y⟩ = conj(c) * ⟨x, T*y⟩
  simp only [inner_smul_right, adjointValue_spec T y]

end Adjoint

/-! ### Symmetric and Self-Adjoint Operators -/

/-- The adjoint domain contains T.dom for a symmetric operator. -/
theorem adjointDomain_of_symmetric {T : OnHilbertSpace 𝕜 H} (hT : T.IsSymmetric) :
    T.dom ≤ adjointDomain T := by
  intro y hy
  use T ⟨y, hy⟩
  intro x
  exact hT x ⟨y, hy⟩

/-- An operator is self-adjoint if dom(T) = dom(T*) and T* = T on this domain. -/
def IsSelfAdjoint (T : OnHilbertSpace 𝕜 H) : Prop :=
  (T.dom : Set H) = adjointDomain T ∧
  ∀ (y : H) (hy : y ∈ T.dom) (hy' : y ∈ adjointDomain T),
    adjointValue T ⟨y, hy'⟩ = T ⟨y, hy⟩

/-- Self-adjoint operators are symmetric. -/
theorem IsSelfAdjoint.isSymmetric {T : OnHilbertSpace 𝕜 H} (hT : IsSelfAdjoint T) :
    T.IsSymmetric := by
  intro x y
  have hy_adj : (y : H) ∈ adjointDomain T := by
    have h := hT.1
    simp only [SetLike.coe_set_eq] at h
    exact h ▸ y.2
  calc @inner 𝕜 H _ (T x) y
      = @inner 𝕜 H _ (x : H) (adjointValue T ⟨y, hy_adj⟩) := adjointValue_spec T ⟨y, hy_adj⟩ x
    _ = @inner 𝕜 H _ (x : H) (T y) := by rw [hT.2 y y.2 hy_adj]

section SelfAdjoint

variable [CompleteSpace H]

/-- For a symmetric operator, T* = T on dom(T). -/
theorem adjoint_extends_symmetric {T : OnHilbertSpace 𝕜 H} (hT : T.IsSymmetric) :
    ∀ y : T.dom, adjointValue T ⟨y, adjointDomain_of_symmetric hT y.2⟩ = T y := by
  intro y
  apply adjoint_value_unique T (adjointValue_spec T ⟨y, adjointDomain_of_symmetric hT y.2⟩)
  intro x
  exact hT x y

/-- For symmetric operators, self-adjointness is equivalent to dom(T) = dom(T*). -/
theorem isSelfAdjoint_iff_symmetric_and_domain_eq {T : OnHilbertSpace 𝕜 H} :
    IsSelfAdjoint T ↔ T.IsSymmetric ∧ (T.dom : Set H) = adjointDomain T := by
  constructor
  · intro hT
    exact ⟨hT.isSymmetric, hT.1⟩
  · intro ⟨hT_sym, hT_dom⟩
    constructor
    · exact hT_dom
    · intro y hy hy'
      apply adjoint_value_unique T (adjointValue_spec T ⟨y, hy'⟩)
      intro x
      exact hT_sym x ⟨y, hy⟩

end SelfAdjoint

end DenselyDefinedLinearMap
