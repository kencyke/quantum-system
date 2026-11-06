/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import QuantumSystem.Analysis.CStarAlgebra.GelfandNaimark
import QuantumSystem.Analysis.CStarAlgebra.Representation.Irreducible
import QuantumSystem.ForMathlib.Algebra.Algebra.Unitization
import QuantumSystem.ForMathlib.Algebra.Star.StarAlgHom
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Quotient
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Semisimple
import QuantumSystem.ForMathlib.RepresentationTheory.AlgebraRepresentation.Basic
import QuantumSystem.ForMathlib.RingTheory.Ideal.Pi

/-!
# Finite-dimensional C⋆-algebras are finite direct sums of matrix algebras

A finite-dimensional C⋆-algebra `A`, unital or not, is ⋆-isomorphic to a finite direct sum of full
matrix algebras, the product `Π i, M_[d i](ℂ)` of the `d i × d i` complex matrices
`M_[d i](ℂ) = CStarMatrix (Fin (d i)) (Fin (d i)) ℂ`; in particular it is unital. A simple one is
⋆-isomorphic to a single `M_[n](ℂ)`.

For unital `A`, the algebraic skeleton is Mathlib's Wedderburn–Artin theorem over an algebraically
closed field, `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`, applied through the
semisimplicity of finite-dimensional C⋆-algebras (`CStarAlgebra.isSemisimpleRing`, from
`CStarAlgebra.jacobson_eq_bot`). Its isomorphism is an algebra isomorphism, which need not respect
the involution; the involution is recovered as follows.

* The kernels `J i` of the components of the Wedderburn–Artin isomorphism are two-sided ideals,
  closed by finite-dimensionality, and the quotient maps give `A ≃⋆ₐ[ℂ] Π i, A ⧸ J i`, each quotient
  a simple finite-dimensional C⋆-algebra.
* A simple finite-dimensional unital C⋆-algebra `B` is a matrix algebra: a faithful representation
  (`CStarRep.exists_isometric_unital`) has a finite-dimensional invariant subspace, and one of
  minimal dimension, `K`, is irreducible. The compression of `B` to `K` is a ⋆-homomorphism, injective
  by simplicity and onto `Module.End ℂ K` (`AlgHom.surjective_of_forall_eq_bot_or_eq_top`); an
  orthonormal basis of `K` identifies `Module.End ℂ K` with `M_[finrank ℂ K](ℂ)`.
* A non-unital `A` embeds in its unitization `Unitization ℂ A`, unital and finite-dimensional. Its
  image is the kernel of the scalar projection, a two-sided ideal, so under the decomposition of the
  unitization it is the product of a subfamily of the matrix factors
  (`Ideal.IsTwoSided.exists_set_forall_mem_iff`).
* For a simple `A`, unital or not, the projection of the decomposition onto one factor is onto, and
  injective by simplicity.

## Main results

* **`NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix`**: a finite-dimensional C⋆-algebra,
  unital or not, is ⋆-isomorphic to a finite direct sum of full matrix algebras.
* **`IsSimpleRing.exists_starAlgEquiv_cstarMatrix`**: a simple finite-dimensional C⋆-algebra,
  unital or not, is ⋆-isomorphic to a full matrix algebra.
* `NonUnitalCStarAlgebra.exists_mul_eq_self`: a finite-dimensional C⋆-algebra is unital, that is,
  it has a two-sided multiplicative identity.

The statements use the notation `M_[n](A)` for `CStarMatrix (Fin n) (Fin n) A`, in scope `CStarMatrix`.
-/

@[expose] public section

open Module
open scoped ComplexOrder CStarMatrix

/-! ### The unital case -/

section Unital

/-- The unital case of `IsSimpleRing.exists_starAlgEquiv_cstarMatrix`. -/
private lemma CStarAlgebra.exists_starAlgEquiv_cstarMatrix_of_isSimpleRing (B : Type*)
    [CStarAlgebra B] [FiniteDimensional ℂ B] [IsSimpleRing B] :
    ∃ n : ℕ, NeZero n ∧ Nonempty (B ≃⋆ₐ[ℂ] M_[n](ℂ)) := by
  classical
  obtain ⟨R, -, hinj, -, hone⟩ := CStarRep.exists_isometric_unital B
  have : Nontrivial R.H := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact one_ne_zero (hinj (by rw [hone, map_zero]; exact Subsingleton.elim _ _))
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : R.H)
  -- an invariant subspace of minimal positive dimension
  let P (n : ℕ) : Prop := ∃ K : Submodule ℂ R.H,
    K ≠ ⊥ ∧ FiniteDimensional ℂ K ∧ K ∈ R.invtSubmodule ∧ finrank ℂ K = n
  have hP : ∃ n, P n := by
    refine ⟨_, LinearMap.range (R.orbit ξ : B →ₗ[ℂ] R.H), ?_, inferInstance, ?_, rfl⟩
    · intro h
      have : (R.orbit ξ : B →ₗ[ℂ] R.H) 1 = 0 := by
        rw [← LinearMap.mem_ker, LinearMap.ker_eq_top.mpr ?_]
        · trivial
        · rw [← LinearMap.range_eq_bot]; exact h
      exact hξ (by simpa [hone] using this)
    · rw [CStarRep.mem_invtSubmodule_iff_forall_mem]
      rintro b _ ⟨a, rfl⟩
      exact ⟨b * a, by simp [map_mul]⟩
  obtain ⟨K, hK0, hKfd, hKinv, hKn⟩ := Nat.find_spec hP
  have hmin : ∀ L : Submodule ℂ R.H, L ≠ ⊥ → FiniteDimensional ℂ L →
      L ∈ R.invtSubmodule → finrank ℂ K ≤ finrank ℂ L := fun L h1 h2 h3 ↦
    hKn ▸ Nat.find_min' hP ⟨L, h1, h2, h3, rfl⟩
  have : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK0
  -- the compression to `K`
  let π : B →⋆ₐ[ℂ] Module.End ℂ K :=
    { toFun := fun b ↦ (R.π b : R.H →ₗ[ℂ] R.H).restrict
        fun _ ↦ CStarRep.apply_mem_of_mem_invtSubmodule hKinv b
      map_one' := LinearMap.ext fun x ↦ Subtype.ext <| by
        simp [hone]
      map_mul' := fun a b ↦ LinearMap.ext fun x ↦ Subtype.ext <| by
        simp [map_mul]
      map_zero' := LinearMap.ext fun x ↦ Subtype.ext <| by simp
      map_add' := fun a b ↦ LinearMap.ext fun x ↦ Subtype.ext <| by
        simp [map_add]
      commutes' := fun c ↦ LinearMap.ext fun x ↦ Subtype.ext <| by
        simp [Algebra.algebraMap_eq_smul_one, map_smul, hone]
      map_star' := fun b ↦ by
        rw [LinearMap.star_eq_adjoint, LinearMap.eq_adjoint_iff]
        intro x y
        simp only [LinearMap.coe_restrict_apply, Submodule.coe_inner, ContinuousLinearMap.coe_coe]
        rw [← R.adjoint_π, ContinuousLinearMap.adjoint_inner_left] }
  have hπ (b : B) (x : K) : (π b x : R.H) = R.π b x := rfl
  -- irreducibility, from minimality
  have hirr : ∀ L : Submodule ℂ K, (∀ b, L ∈ Module.End.invtSubmodule (π b)) → L = ⊥ ∨ L = ⊤ := by
    intro L hL
    by_cases hL0 : L = ⊥
    · exact Or.inl hL0
    right
    have hinj' : Function.Injective (Submodule.map K.subtype) :=
      Submodule.map_injective_of_injective K.subtype_injective
    have hL' : L.map K.subtype ≠ ⊥ := fun h ↦ hL0 (hinj' (by rw [h, Submodule.map_bot]))
    have hinv' : L.map K.subtype ∈ R.invtSubmodule := by
      rw [CStarRep.mem_invtSubmodule_iff_forall_mem]
      rintro b _ ⟨y, hy, rfl⟩
      exact ⟨π b y, hL b hy, (hπ b y).symm⟩
    have hle := hmin _ hL' (Submodule.finiteDimensional_of_le (Submodule.map_subtype_le K L)) hinv'
    have := Submodule.eq_of_le_of_finrank_le (Submodule.map_subtype_le K L) hle
    exact hinj' (this.trans (Submodule.map_subtype_top K).symm)
  have hsurj : Function.Surjective π :=
    AlgHom.surjective_of_forall_eq_bot_or_eq_top (π : B →ₐ[ℂ] Module.End ℂ K) hirr
  have hinj : Function.Injective π := RingHom.injective (π : B →+* Module.End ℂ K)
  refine ⟨finrank ℂ K, ⟨(Module.finrank_pos).ne'⟩, ⟨?_⟩⟩
  exact (StarAlgEquiv.ofBijective π ⟨hinj, hsurj⟩).trans <|
    (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ K)).trans
      CStarMatrix.ofMatrixStarAlgEquiv

/-- The unital case of `NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix`. -/
private lemma CStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix (A : Type*) [CStarAlgebra A]
    [FiniteDimensional ℂ A] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧ Nonempty (A ≃⋆ₐ[ℂ] Π i, M_[d i](ℂ)) := by
  classical
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A
  -- the components of `e` and their kernels
  let f (i : Fin n) : A →ₙₐ[ℂ] Matrix (Fin (d i)) (Fin (d i)) ℂ :=
    ((Pi.evalAlgHom ℂ _ i).comp e.toAlgHom :)
  have hf (i : Fin n) (a : A) : f i a = e a i := rfl
  let J (i : Fin n) : Submodule ℂ A := NonUnitalAlgHom.ker ℂ (f i)
  have hJ (i : Fin n) (a : A) : a ∈ J i ↔ e a i = 0 := NonUnitalAlgHom.mem_ker
  have hJclosed (i : Fin n) : IsClosed (J i : Set A) := Submodule.closed_of_finiteDimensional _
  -- the quotients are simple
  have hsimple (i : Fin n) : IsSimpleRing (A ⧸ J i) := by
    let g : A ⧸ J i →+* Matrix (Fin (d i)) (Fin (d i)) ℂ :=
      { toFun := Submodule.Quotient.liftₙₐ (J i) (f i) le_rfl
        map_one' := by
          rw [← Submodule.Quotient.mk_one, Submodule.Quotient.liftₙₐ_mk, hf, map_one]
          rfl
        map_mul' := map_mul _
        map_zero' := map_zero _
        map_add' := map_add _ }
    have hg : Function.Bijective g := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        induction x using Submodule.Quotient.induction_on with | H a => ?_
        rw [Submodule.Quotient.mk_eq_zero]
        exact hx
      · intro M
        refine ⟨Submodule.Quotient.mk (e.symm (Pi.single i M)), ?_⟩
        change f i (e.symm (Pi.single i M)) = M
        rw [hf, e.apply_symm_apply, Pi.single_eq_same]
    have := hd i
    exact IsSimpleRing.of_ringEquiv (RingEquiv.ofBijective g hg).symm inferInstance
  -- the product of the quotient maps
  let Φ : A →⋆ₐ[ℂ] Π i, A ⧸ J i := StarAlgHom.pi fun i ↦ Submodule.Quotient.mkStarₐ (J i)
  have hΦ (a : A) (i : Fin n) : Φ a i = Submodule.Quotient.mk a := rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply e.injective
    funext i
    have : Φ a i = 0 := by rw [ha, Pi.zero_apply]
    rw [hΦ, Submodule.Quotient.mk_eq_zero, hJ] at this
    rw [this, map_zero, Pi.zero_apply]
  have hΦsurj : Function.Surjective Φ := by
    intro y
    choose a ha using fun i ↦ Submodule.Quotient.mk_surjective (J i) (y i)
    refine ⟨e.symm fun i ↦ e (a i) i, funext fun j ↦ ?_⟩
    rw [hΦ, ← ha j, Submodule.Quotient.eq, hJ, map_sub, e.apply_symm_apply, Pi.sub_apply, sub_self]
  choose m hm e' using fun i ↦ CStarAlgebra.exists_starAlgEquiv_cstarMatrix_of_isSimpleRing (A ⧸ J i)
  exact ⟨n, m, hm, ⟨(StarAlgEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).trans
    (StarAlgEquiv.piCongrRight fun i ↦ (e' i).some)⟩⟩

end Unital

/-! ### The structure theorem -/

section NonUnital

variable (A : Type*) [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]

/-- A finite-dimensional C⋆-algebra, unital or not, is ⋆-isomorphic to a finite direct sum of full
matrix algebras `Π i, M_[d i](ℂ)`. -/
theorem NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧ Nonempty (A ≃⋆ₐ[ℂ] Π i, M_[d i](ℂ)) := by
  classical
  obtain ⟨n, d, hd, ⟨e⟩⟩ := CStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix (Unitization ℂ A)
  have : ∀ i, Nonempty (Fin (d i)) := fun i ↦ have := hd i; inferInstance
  -- the image of `A` is the kernel of the scalar projection, a two-sided ideal
  let I : Ideal (Unitization ℂ A) := RingHom.ker (Unitization.fstHom ℂ A)
  let I' : Ideal (Π i, M_[d i](ℂ)) := I.comap e.symm
  have hI' (x) : x ∈ I' ↔ (e.symm x).fst = 0 := Ideal.mem_comap.trans RingHom.mem_ker
  obtain ⟨S, hS⟩ := Ideal.IsTwoSided.exists_set_forall_mem_iff I'
  -- `A` maps onto the factors indexed by `S`
  let Ψ : A →⋆ₙₐ[ℂ] Π i : S, M_[d i](ℂ) :=
    NonUnitalStarAlgHom.pi fun i ↦ (Pi.evalNonUnitalStarAlgHom ℂ _ (i : Fin n)).comp
      (e.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A))
  have hΨ (a : A) (i : S) : Ψ a i = e a i := rfl
  have hmem (a : A) : e (a : Unitization ℂ A) ∈ I' := by
    rw [hI', e.symm_apply_apply, Unitization.fst_inr]
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_zero, ← map_eq_zero_iff e e.injective]
    funext i
    by_cases hi : i ∈ S
    · exact congr_fun ha ⟨i, hi⟩
    · exact (hS _).mp (hmem a) i hi
  have hsurj : Function.Surjective Ψ := by
    intro y
    let x : Π i, M_[d i](ℂ) := fun i ↦ if h : i ∈ S then y ⟨i, h⟩ else 0
    have hx : x ∈ I' := (hS x).mpr fun i hi ↦ dite_eq_right hi
    rw [hI'] at hx
    refine ⟨(e.symm x).snd, funext fun i ↦ ?_⟩
    rw [hΨ]
    have : ((e.symm x).snd : Unitization ℂ A) = e.symm x := by
      conv_rhs => rw [← Unitization.inl_fst_add_inr_snd_eq (e.symm x)]
      rw [hx, Unitization.inl_zero, zero_add]
    rw [this, e.apply_symm_apply]
    exact dite_eq_left i.2
  refine ⟨Fintype.card S, fun j ↦ d ((Fintype.equivFin S).symm j), fun j ↦ hd _, ⟨?_⟩⟩
  exact (StarAlgEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).trans
    (StarAlgEquiv.piCongrLeft' ℂ (fun i : S ↦ M_[d i](ℂ)) (Fintype.equivFin S))

/-- A simple finite-dimensional C⋆-algebra, unital or not, is ⋆-isomorphic to a full matrix
algebra `M_[n](ℂ)`. -/
theorem IsSimpleRing.exists_starAlgEquiv_cstarMatrix [IsSimpleRing A] :
    ∃ n : ℕ, NeZero n ∧ Nonempty (A ≃⋆ₐ[ℂ] M_[n](ℂ)) := by
  obtain ⟨n, d, hd, ⟨Φ⟩⟩ := NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix A
  -- there is a factor, as `A` is nontrivial
  obtain ⟨j⟩ : Nonempty (Fin n) := by
    rw [← not_isEmpty_iff]
    intro _
    obtain ⟨x, y, hxy⟩ := exists_pair_ne A
    exact hxy (Φ.injective (Subsingleton.elim _ _))
  have := hd j
  -- the projection onto it is onto, and injective by simplicity
  let ψ : A →⋆ₙₐ[ℂ] M_[d j](ℂ) := (Pi.evalNonUnitalStarAlgHom ℂ _ j).comp Φ.toNonUnitalStarAlgHom
  have hsurj : Function.Surjective ψ := fun y ↦
    ⟨Φ.symm (Pi.single j y), by simp [ψ]⟩
  have hinj : Function.Injective ψ := by
    rcases eq_bot_or_eq_top (TwoSidedIdeal.ker ψ) with h | h
    · rw [injective_iff_map_eq_zero]
      intro a ha
      have : a ∈ TwoSidedIdeal.ker ψ := (TwoSidedIdeal.mem_ker ψ).mpr ha
      rwa [h, TwoSidedIdeal.mem_bot] at this
    · obtain ⟨a, ha⟩ := hsurj 1
      have : a ∈ TwoSidedIdeal.ker ψ := h ▸ trivial
      rw [TwoSidedIdeal.mem_ker, ha] at this
      exact absurd this one_ne_zero
  exact ⟨d j, hd j, ⟨StarAlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩⟩

/-- A finite-dimensional C⋆-algebra is unital: it has a two-sided multiplicative identity. -/
lemma NonUnitalCStarAlgebra.exists_mul_eq_self : ∃ e : A, ∀ a, e * a = a ∧ a * e = a := by
  obtain ⟨n, d, -, ⟨Φ⟩⟩ := NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix A
  refine ⟨Φ.symm 1, fun a ↦ ⟨?_, ?_⟩⟩
  · conv_lhs => rw [← Φ.symm_apply_apply a, ← map_mul, one_mul]
    exact Φ.symm_apply_apply a
  · conv_lhs => rw [← Φ.symm_apply_apply a, ← map_mul, mul_one]
    exact Φ.symm_apply_apply a

end NonUnital

section Examples

-- A unital algebra is covered through `CStarAlgebra.toNonUnitalCStarAlgebra`.
example : ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
    Nonempty (M_[2](ℂ) ≃⋆ₐ[ℂ] Π i, M_[d i](ℂ)) :=
  NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix _

example : ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
    Nonempty ((Fin 2 → ℂ) ≃⋆ₐ[ℂ] Π i, M_[d i](ℂ)) :=
  NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix _

example : ∃ n : ℕ, NeZero n ∧ Nonempty (M_[3](ℂ) ≃⋆ₐ[ℂ] M_[n](ℂ)) :=
  IsSimpleRing.exists_starAlgEquiv_cstarMatrix _

end Examples
