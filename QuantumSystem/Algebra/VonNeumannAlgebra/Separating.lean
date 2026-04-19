module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection
public import QuantumSystem.Algebra.VonNeumannAlgebra.NormalState

@[expose] public section

section SeparatingVector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector ξ ∈ H is separating for a von Neumann algebra M ⊆ 𝓑(H) if
x ∈ M and x • ξ = 0 implies x = 0.

This is equivalent to the map M → H given by x ↦ x • ξ being injective. -/
def IsSeparatingVector (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  ∀ x : M, (x : H →L[ℂ] H) ξ = 0 → x = 0

/-- A vector ξ ∈ H is cyclic for a von Neumann algebra M ⊆ 𝓑(H) if
the closure of { x • ξ | x ∈ M } is all of H.

This is equivalent to saying that M ξ spans a dense subspace of H. -/
def IsCyclicVector (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  Dense ({ (x : H →L[ℂ] H) ξ | x : M } : Set H)

/-- Alternative characterization: ξ is separating iff the orbit map is injective. -/
lemma isSeparatingVector_iff_injective (M : VonNeumannAlgebra H) (ξ : H) :
    IsSeparatingVector M ξ ↔ Function.Injective (fun x : M => (x : H →L[ℂ] H) ξ) := by
  constructor
  · intro h x y hxy
    have : (x : H →L[ℂ] H) ξ - (y : H →L[ℂ] H) ξ = 0 := sub_eq_zero.mpr hxy
    rw [← ContinuousLinearMap.sub_apply] at this
    have h_sub : ((x : H →L[ℂ] H) - (y : H →L[ℂ] H)) ξ = 0 := this
    have h_mem : (x : H →L[ℂ] H) - (y : H →L[ℂ] H) ∈ M.toStarSubalgebra :=
      M.toStarSubalgebra.sub_mem x.property y.property
    have h_zero := h ⟨(x : H →L[ℂ] H) - (y : H →L[ℂ] H), h_mem⟩ h_sub
    simp only [Subtype.ext_iff, ZeroMemClass.coe_zero, sub_eq_zero] at h_zero
    exact Subtype.ext h_zero
  · intro h x hx
    have h0 : ((0 : M) : H →L[ℂ] H) ξ = 0 := by simp
    exact h (hx.trans h0.symm)

/-- Nonzero vectors: if ξ is separating, then ξ ≠ 0.

Note: We assume H is nontrivial (has dimension ≥ 1), which holds for any Hilbert space
carrying a von Neumann algebra. -/
lemma IsSeparatingVector.ne_zero [Nontrivial H] {M : VonNeumannAlgebra H} {ξ : H}
    (hξ : IsSeparatingVector M ξ) : ξ ≠ 0 := by
  intro h0
  -- 1 ξ = ξ = 0, so if ξ is separating, 1 = 0 in M
  have h1 : (1 : M) = 0 := hξ 1 (by simp [h0])
  -- But 1 ≠ 0 in a von Neumann algebra on a nontrivial space
  have h_one_ne : ((1 : M) : H →L[ℂ] H) ≠ ((0 : M) : H →L[ℂ] H) := by
    simp only [OneMemClass.coe_one, ZeroMemClass.coe_zero, ne_eq]
    intro heq
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have : x = 0 := by
      calc x = (1 : H →L[ℂ] H) x := by simp
        _ = (0 : H →L[ℂ] H) x := by rw [heq]
        _ = 0 := by simp
    exact hx this
  exact h_one_ne (congr_arg Subtype.val h1)

end SeparatingVector

/-! ## Faithful Normal States -/

section FaithfulState

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace VonNeumannAlgebra

namespace NormalState

variable {S : VonNeumannAlgebra H} [WStarAlgebra (H →L[ℂ] H)]

/-- A normal state ω on a von Neumann algebra S is faithful if ω(x*x) = 0 implies x = 0.

This is the standard definition of faithfulness for states on operator algebras. -/
def IsFaithful (ω : NormalState S) : Prop :=
  ∀ x : S, ω (star x * x) = 0 → x = 0

/-- Alternative characterization: a normal state is faithful iff x*x is not in the kernel
unless x = 0. -/
lemma isFaithful_iff (ω : NormalState S) :
    ω.IsFaithful ↔ ∀ x : S, x ≠ 0 → ω (star x * x) ≠ 0 := by
  constructor
  · intro hf x hx h0
    exact hx (hf x h0)
  · intro h x h0
    by_contra hx
    exact h x hx h0

end NormalState

end VonNeumannAlgebra

end FaithfulState

/-! ## Cyclic-Separating Duality

For a von Neumann algebra M ⊆ B(H), a vector ξ is separating for M if and only if
it is cyclic for the commutant M'.

This fundamental duality is key to the Tomita-Takesaki theory.
-/

section CyclicSeparatingDuality

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H) (ξ : H)

/-- If ξ is separating for M, then M'ξ is dense in H.

This is the "separating implies cyclic for commutant" direction of the duality.
Proof: If M'ξ were not dense, let K be its closure. K is M'-invariant, so the
orthogonal projection P onto K is in M'' = M. Since 1 ∈ M', we have ξ ∈ K,
so (1-P)ξ = 0. But 1-P ≠ 0 (since K ⊊ H), contradicting ξ being separating for M. -/
theorem IsSeparatingVector.isCyclic_commutant
    (hξ : IsSeparatingVector M ξ) : IsCyclicVector M.commutant ξ := by
  rw [IsCyclicVector]
  by_contra h_not_dense
  rw [dense_iff_closure_eq] at h_not_dense
  push_neg at h_not_dense
  -- Let K be the closure of span(M'ξ), a closed submodule
  let S : Set H := { (a' : H →L[ℂ] H) ξ | a' : M.commutant }
  let K : Submodule ℂ H := (Submodule.span ℂ S).topologicalClosure
  -- K is a proper closed subspace (since M'ξ is not dense)
  have hK_closed : IsClosed (K : Set H) := Submodule.isClosed_topologicalClosure _
  -- K has orthogonal projection since it's closed in a complete space
  haveI : CompleteSpace K := hK_closed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  -- The starProjection P is the orthogonal projection onto K
  let P : H →L[ℂ] H := K.starProjection
  -- P is a star projection (self-adjoint idempotent)
  have hP_star : IsStarProjection P := by
    constructor
    · exact Submodule.isIdempotentElem_starProjection K
    · exact (Submodule.starProjection_isSymmetric K).isSelfAdjoint
  -- range(P) = K
  have hP_range : LinearMap.range (P : H →L[ℂ] H) = K := Submodule.range_starProjection K
  -- K is M'-invariant: for all a' ∈ M' and k ∈ K, a'k ∈ K
  have hK_invariant : ∀ a' : M.commutant, ∀ k ∈ K, (a' : H →L[ℂ] H) k ∈ K := by
    intro a' k hk
    -- K = closure(span(M'ξ)), and a' ∈ M', so a' · K ⊆ K
    -- First show a' maps span(S) to span(S)
    have h_span_inv : ∀ s ∈ Submodule.span ℂ S, (a' : H →L[ℂ] H) s ∈ Submodule.span ℂ S := by
      intro s hs
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a'', rfl⟩ := hx
        have ha'a'' : (a' : H →L[ℂ] H) * (a'' : H →L[ℂ] H) ∈ M.commutant :=
          M.commutant.mul_mem a'.property a''.property
        apply Submodule.subset_span
        exact ⟨⟨(a' : H →L[ℂ] H) * (a'' : H →L[ℂ] H), ha'a''⟩, by simp [ContinuousLinearMap.mul_apply]⟩
      | zero => simp
      | add x y _ _ ihx ihy =>
        simp only [map_add]
        exact Submodule.add_mem _ ihx ihy
      | smul c x _ ihx =>
        simp only [map_smul]
        exact Submodule.smul_mem _ c ihx
    -- Then extend to the closure using continuity
    have h_mapsTo : Set.MapsTo (a' : H →L[ℂ] H) (Submodule.span ℂ S : Set H) (Submodule.span ℂ S : Set H) :=
      fun s hs => h_span_inv s hs
    have h_closure := h_mapsTo.closure (a' : H →L[ℂ] H).continuous
    rw [← Submodule.topologicalClosure_coe] at h_closure
    exact h_closure hk
  -- Therefore, range(P) = K is invariant under all a' ∈ M'
  have hK_M'_invariant : ∀ a' ∈ M.commutant, K ∈ Module.End.invtSubmodule (a' : H →L[ℂ] H) := by
    intro a' ha'
    rw [Module.End.mem_invtSubmodule]
    intro k hk
    simp only [Submodule.mem_comap]
    exact hK_invariant ⟨a', ha'⟩ k hk
  -- By IsStarProjection.mem_iff, P ∈ M'' (and M'' = M)
  have hP_in_M'' : P ∈ M.commutant.commutant := by
    rw [VonNeumannAlgebra.IsStarProjection.mem_iff hP_star M.commutant.commutant]
    intro a' ha'
    -- a' ∈ M.commutant.commutant.commutant = M.commutant
    rw [M.commutant_commutant] at ha'
    rw [hP_range]
    exact hK_M'_invariant a' ha'
  have hP_in_M : P ∈ M := by rwa [M.commutant_commutant] at hP_in_M''
  -- Since 1 ∈ M', we have ξ = 1·ξ ∈ M'ξ ⊆ span(M'ξ) ⊆ K
  have hξ_in_K : ξ ∈ K := by
    have h1 : (1 : H →L[ℂ] H) ∈ M.commutant := M.commutant.one_mem
    have hξ_in_S : ξ ∈ S := ⟨⟨1, h1⟩, by simp⟩
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span hξ_in_S)
  -- So Pξ = ξ
  have hPξ : P ξ = ξ := Submodule.starProjection_eq_self_iff.mpr hξ_in_K
  -- And (1-P)ξ = 0
  have h1mP_ξ : (1 - P) ξ = 0 := by simp [hPξ]
  -- Also 1-P ∈ M (M is closed under subtraction)
  have h1mP_in_M : (1 - P) ∈ M := M.sub_mem M.one_mem hP_in_M
  -- K ≠ ⊤ means P ≠ 1, so 1-P ≠ 0
  -- First show that (Submodule.span ℂ S : Set H) = S (since S is already a vector subspace)
  have hS_eq_span : (Submodule.span ℂ S : Set H) = S := by
    ext x
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => exact ⟨⟨0, M.commutant.zero_mem⟩, by simp⟩
      | add x y _ _ ihx ihy =>
        obtain ⟨⟨a', ha'⟩, rfl⟩ := ihx
        obtain ⟨⟨b', hb'⟩, rfl⟩ := ihy
        exact ⟨⟨a' + b', M.commutant.add_mem ha' hb'⟩, by simp [ContinuousLinearMap.add_apply]⟩
      | smul c x _ ihx =>
        obtain ⟨⟨a', ha'⟩, rfl⟩ := ihx
        have hca' : c • a' ∈ M.commutant := by
          have h2 : c • a' = algebraMap ℂ (H →L[ℂ] H) c * a' := by
            simp [Algebra.algebraMap_eq_smul_one]
          rw [h2]
          exact M.commutant.mul_mem (M.commutant.algebraMap_mem c) ha'
        exact ⟨⟨c • a', hca'⟩, by simp [ContinuousLinearMap.smul_apply]⟩
    · intro hx
      exact Submodule.subset_span hx
  have hK_ne_top : K ≠ ⊤ := by
    intro hK_eq_top
    apply h_not_dense
    -- closure S = closure (span S) = K = ⊤ = univ
    calc closure S
        = closure (Submodule.span ℂ S : Set H) := by rw [hS_eq_span]
      _ = (Submodule.span ℂ S).topologicalClosure := rfl
      _ = K := rfl
      _ = (⊤ : Submodule ℂ H) := by rw [hK_eq_top]
      _ = Set.univ := by simp
  have h1mP_ne : (1 - P) ≠ 0 := by
    intro h_eq
    apply hK_ne_top
    have hP_eq_1 : P = 1 := by
      have : P = 1 - (1 - P) := by simp
      rw [this, h_eq, sub_zero]
    rw [← hP_range, hP_eq_1]
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_top, iff_true]
    exact ⟨x, rfl⟩
  -- This contradicts ξ being separating for M
  have h_sep := hξ ⟨(1 - P), h1mP_in_M⟩ h1mP_ξ
  simp only [Subtype.ext_iff, ZeroMemClass.coe_zero] at h_sep
  exact h1mP_ne h_sep

/-- If ξ is cyclic for M', then ξ is separating for M.

This is the "cyclic for commutant implies separating" direction.
Proof: Suppose x ∈ M and xξ = 0. For any a' ∈ M', xa'ξ = a'xξ = a'0 = 0.
Since M'ξ is dense and x is continuous, x = 0 on a dense set, hence x = 0. -/
theorem IsCyclicVector.isSeparating_of_commutant
    (hξ : IsCyclicVector M.commutant ξ) : IsSeparatingVector M ξ := by
  intro x hx
  -- x ∈ M, x ξ = 0
  -- For any a' ∈ M', x (a' ξ) = a' (x ξ) = a' 0 = 0 (since x commutes with M')
  have h_zero_on_orbit : ∀ a' : M.commutant, (x : H →L[ℂ] H) ((a' : H →L[ℂ] H) ξ) = 0 := by
    intro a'
    -- x a' = a' x since x ∈ M and a' ∈ M'
    have h_comm : (x : H →L[ℂ] H) * (a' : H →L[ℂ] H) = (a' : H →L[ℂ] H) * (x : H →L[ℂ] H) := by
      -- x ∈ M, a' ∈ M' = commutant of M
      have hx_mem := x.property
      have ha'_comm := a'.property
      -- By definition of commutant: ∀ y ∈ M, a' y = y a'
      rw [VonNeumannAlgebra.mem_commutant_iff] at ha'_comm
      exact (ha'_comm (x : H →L[ℂ] H) hx_mem)
    calc (x : H →L[ℂ] H) ((a' : H →L[ℂ] H) ξ)
        = ((x : H →L[ℂ] H) * (a' : H →L[ℂ] H)) ξ := rfl
      _ = ((a' : H →L[ℂ] H) * (x : H →L[ℂ] H)) ξ := by rw [h_comm]
      _ = (a' : H →L[ℂ] H) ((x : H →L[ℂ] H) ξ) := rfl
      _ = (a' : H →L[ℂ] H) 0 := by rw [hx]
      _ = 0 := by simp
  -- Since M'ξ is dense and (x : H →L[ℂ] H) is continuous, and it's zero on M'ξ
  have h_zero_on_closure : ∀ y ∈ closure ({ (a' : H →L[ℂ] H) ξ | a' : M.commutant } : Set H),
      (x : H →L[ℂ] H) y = 0 := by
    intro y hy
    have h_closed := ContinuousLinearMap.isClosed_ker (x : H →L[ℂ] H)
    apply h_closed.closure_subset_iff.mpr _ hy
    intro z hz
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    obtain ⟨a', rfl⟩ := hz
    exact h_zero_on_orbit a'
  -- M'ξ is dense, so closure = H
  rw [IsCyclicVector] at hξ
  have h_closure_eq : closure ({ (a' : H →L[ℂ] H) ξ | a' : M.commutant } : Set H) = Set.univ :=
    hξ.closure_eq
  -- So x = 0 on all of H
  have h_x_zero : (x : H →L[ℂ] H) = 0 := by
    ext y
    have hy : y ∈ closure ({ (a' : H →L[ℂ] H) ξ | a' : M.commutant } : Set H) := by
      rw [h_closure_eq]; exact Set.mem_univ y
    exact h_zero_on_closure y hy
  -- Therefore x = 0 as an element of M
  ext
  have := congrFun (congrArg DFunLike.coe h_x_zero)
  simp only [ContinuousLinearMap.zero_apply] at this
  exact this _

/-- Characterization: ξ is separating for M iff ξ is cyclic for M'. -/
theorem isSeparatingVector_iff_isCyclic_commutant :
    IsSeparatingVector M ξ ↔ IsCyclicVector M.commutant ξ :=
  ⟨IsSeparatingVector.isCyclic_commutant M ξ, IsCyclicVector.isSeparating_of_commutant M ξ⟩

end CyclicSeparatingDuality

/-! ## Vector States and Faithful States

A vector ξ ∈ H defines a normal state ωξ on B(H) by ωξ(T) = ⟨ξ, Tξ⟩.
This state is faithful on a von Neumann algebra M iff ξ is separating for M.
-/

section VectorState

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H) (ξ : H)

open scoped InnerProductSpace

/-- A separating vector gives a faithful state when restricted to M.

If ξ is separating for M and ωξ(x*x) = 0 for x ∈ M, then ⟨ξ, x*xξ⟩ = ‖xξ‖² = 0,
so xξ = 0, and by separating property, x = 0. -/
theorem IsSeparatingVector.faithful_vectorState
    (hξ : IsSeparatingVector M ξ) :
    ∀ x : M, ⟪ξ, ((star x * x : M) : H →L[ℂ] H) ξ⟫_ℂ = 0 → x = 0 := by
  intro x h0
  -- ⟨ξ, x*x ξ⟩ = ⟨xξ, xξ⟩ = ‖xξ‖²
  have h_norm_sq : (⟪ξ, ((star x * x : M) : H →L[ℂ] H) ξ⟫_ℂ).re = ‖(x : H →L[ℂ] H) ξ‖^2 := by
    have h_eq : ((star x * x : M) : H →L[ℂ] H) =
        (star (x : H →L[ℂ] H)) * (x : H →L[ℂ] H) := by simp
    rw [h_eq, ContinuousLinearMap.mul_apply]
    -- star x = adjoint x, so we have ⟨ξ, (adjoint x)(x ξ)⟩
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  -- From h0 and h_norm_sq, we get ‖xξ‖ = 0
  have h_re_zero : (⟪ξ, ((star x * x : M) : H →L[ℂ] H) ξ⟫_ℂ).re = 0 := by rw [h0]; simp
  rw [h_norm_sq] at h_re_zero
  have h_norm_zero : ‖(x : H →L[ℂ] H) ξ‖ = 0 := by
    have h_sq_zero : ‖(x : H →L[ℂ] H) ξ‖^2 = 0 := h_re_zero
    exact sq_eq_zero_iff.mp h_sq_zero
  have hxξ : (x : H →L[ℂ] H) ξ = 0 := norm_eq_zero.mp h_norm_zero
  exact hξ x hxξ

/-- Conversely, if the vector state is faithful on M, then ξ is separating for M. -/
theorem isSeparatingVector_of_faithful_vectorState
    (h : ∀ x : M, ⟪ξ, ((star x * x : M) : H →L[ℂ] H) ξ⟫_ℂ = 0 → x = 0) :
    IsSeparatingVector M ξ := by
  intro x hxξ
  -- xξ = 0 implies ⟨ξ, x*xξ⟩ = ⟨xξ, xξ⟩ = 0
  have h0 : ⟪ξ, ((star x * x : M) : H →L[ℂ] H) ξ⟫_ℂ = 0 := by
    have h_eq : ((star x * x : M) : H →L[ℂ] H) =
        (star (x : H →L[ℂ] H)) * (x : H →L[ℂ] H) := by simp
    rw [h_eq, ContinuousLinearMap.mul_apply]
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    simp [hxξ]
  exact h x h0

/-- Characterization: ξ is separating for M iff the vector state ωξ is faithful on M. -/
theorem isSeparatingVector_iff_faithful_vectorState :
    IsSeparatingVector M ξ ↔ ∀ x : M, ⟪ξ, ((star x * x : M) : H →L[ℂ] H) ξ⟫_ℂ = 0 → x = 0 :=
  ⟨IsSeparatingVector.faithful_vectorState M ξ, isSeparatingVector_of_faithful_vectorState M ξ⟩

end VectorState
