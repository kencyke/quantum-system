/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import QuantumSystem.Analysis.OperatorSystem.Injective
public import QuantumSystem.ForMathlib.Algebra.Star.StarAlgHom
import QuantumSystem.Analysis.CStarAlgebra.ConditionalExpectation
import QuantumSystem.Analysis.CStarAlgebra.FiniteDimensional
import QuantumSystem.Analysis.CStarAlgebra.PositiveMap

/-!
# Injective C⋆-algebras

A C⋆-algebra with its star order is a space with matrix orders, and injectivity
(`OperatorSystem.Injective`) applies to it. Injectivity of C⋆-algebras is invariant under
`⋆`-isomorphisms and passes to finite products, so a C⋆-algebra `⋆`-isomorphic to `B(K)` is
injective, and so is every finite-dimensional C⋆-algebra, a finite product of matrix algebras
`M_[n](ℂ) ≃ B(ℂⁿ)`.

A unital C⋆-subalgebra `S` of an injective C⋆-algebra `A`, such as `B(H)`, is injective iff it is
the range of a completely positive retraction `E : A → S`, and iff it is the range of a contractive
projection of `A`: such a projection is completely positive by Tomiyama's theorem
(`LinearMap.IsProj.map_cstarMatrix_nonneg_of_norm_apply_le`). That the range of a contractive
projection is injective holds for every closed `⋆`-subalgebra, containing the unit of `A` or not
(`NonUnitalStarSubalgebra.injective_of_isProj`), such as a corner `p A p`. The converse is stated
for unital subalgebras only: injectivity extends completely positive maps along unital complete
order embeddings of operator systems, and the inclusion `S → A` is one only when `S` contains the
unit of `A`.

## Main results

* `OperatorSystem.Injective.of_starAlgEquiv` — injectivity of C⋆-algebras is invariant under
  `⋆`-isomorphisms.
* `OperatorSystem.Injective.pi` — a finite product of injective C⋆-algebras is injective.
* `OperatorSystem.injective_of_starAlgEquiv_continuousLinearMap` — a C⋆-algebra `⋆`-isomorphic to
  `B(K)` is injective.
* `CStarAlgebra.injective_of_finiteDimensional` — a finite-dimensional C⋆-algebra is injective.
* **`StarSubalgebra.injective_iff_exists_retraction`**: a closed unital `⋆`-subalgebra `S` of an
  injective C⋆-algebra `A` is injective iff there is a completely positive `E : A → S` restricting
  to the identity on `S`.
* **`StarSubalgebra.injective_iff_exists_isProj`**: the same iff there is a projection of `A` onto
  `S` of norm at most one.
* `NonUnitalStarSubalgebra.injective_of_isProj`: the range of a contractive projection of an
  injective C⋆-algebra onto a closed `⋆`-subalgebra, unital or not, is injective.
* `LinearMap.IsProj.norm_mkContinuous_eq_one`: a contractive projection of a nonzero C⋆-algebra
  onto a unital `⋆`-subalgebra has norm one.
-/

@[expose] public section

open scoped CStarAlgebra

namespace OperatorSystem

/-- **Injectivity is invariant under `⋆`-isomorphisms of C⋆-algebras**: a `⋆`-isomorphism and its
inverse are completely positive (`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`), so `B` is
a retract of the injective `A` (`OperatorSystem.Injective.of_retract`). -/
lemma Injective.of_starAlgEquiv {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (hA : Injective A) (e : A ≃⋆ₐ[ℂ] B) :
    Injective B :=
  hA.of_retract (CompletelyPositiveMapClass'.toCompletelyPositiveMap' e.symm)
    (CompletelyPositiveMapClass'.toCompletelyPositiveMap' e) fun b => e.apply_symm_apply b

/-- For a finite family of C⋆-algebras, a matrix over the product is positive iff each of its
components is: the componentwise map `Mₖ(Π i, Bᵢ) → Π i, Mₖ(Bᵢ)` is an injective `⋆`-homomorphism,
hence an order embedding (`NonUnitalStarAlgHom.map_le_map_iff`). -/
private lemma cstarMatrix_nonneg_pi_iff {ι : Type*} [Fintype ι] {B : ι → Type*}
    [∀ i, CStarAlgebra (B i)] [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)] {k : ℕ}
    (X : CStarMatrix (Fin k) (Fin k) (Π i, B i)) : 0 ≤ X ↔ ∀ i, 0 ≤ X.map fun x => x i := by
  let e := NonUnitalStarAlgHom.pi (R := ℂ) fun i =>
    CStarMatrix.mapₙₐ (n := Fin k) (Pi.evalStarAlgHom ℂ B i).toNonUnitalStarAlgHom
  have hinj : Function.Injective e := fun X Y h =>
    CStarMatrix.ext fun a b => funext fun i => congr($h i a b)
  have h := NonUnitalStarAlgHom.map_le_map_iff e hinj (x := 0) (y := X)
  rw [map_zero] at h
  rw [← h, Pi.le_def]
  rfl

/-- **A finite product of injective C⋆-algebras is injective.** A completely positive map into the
product has completely positive components (`Pi.evalStarAlgHom` is a `⋆`-homomorphism); each
extends, and the extensions assemble into a completely positive map, a matrix over the product
being positive iff each of its components is. -/
lemma Injective.pi {ι : Type*} [Fintype ι] {B : ι → Type*} [∀ i, CStarAlgebra (B i)]
    [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)] (h : ∀ i, Injective (B i)) :
    Injective (Π i, B i) := by
  intro V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj hj1 φ
  have hψ i := (h i).exists_extension hj hj1
    ((CompletelyPositiveMapClass'.toCompletelyPositiveMap' (Pi.evalStarAlgHom ℂ B i)).comp φ)
  choose ψ hψ using hψ
  refine ⟨⟨LinearMap.pi fun i => (ψ i).toLinearMap, fun k M hM => ?_⟩, ?_⟩
  · refine (cstarMatrix_nonneg_pi_iff _).mpr fun i => ?_
    exact (ψ i).map_cstarMatrix_nonneg' k M hM
  · refine CompletelyPositiveMap'.ext fun v => funext fun i => ?_
    exact DFunLike.congr_fun (hψ i) v

/-- **A C⋆-algebra `⋆`-isomorphic to `B(K)` is injective**, as `B(K)` is
(`OperatorSystem.injective_continuousLinearMap`). -/
lemma injective_of_starAlgEquiv_continuousLinearMap {A K : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : A ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : Injective A :=
  (injective_continuousLinearMap K).of_starAlgEquiv e.symm

end OperatorSystem

namespace CStarAlgebra

/-- **A finite-dimensional C⋆-algebra is injective.** It is `⋆`-isomorphic to a finite product of
matrix algebras (`NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix`), each `⋆`-isomorphic to
`B(ℂⁿ)` (`Matrix.toEuclideanCLM`) and so injective, and a finite product of injective C⋆-algebras is
injective (`OperatorSystem.Injective.pi`). -/
lemma injective_of_finiteDimensional (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [FiniteDimensional ℂ A] : OperatorSystem.Injective A := by
  obtain ⟨n, d, -, ⟨e⟩⟩ := NonUnitalCStarAlgebra.exists_starAlgEquiv_pi_cstarMatrix A
  -- each block `M_[d i](ℂ)` is `B(ℂ^{d i})`
  let f : (Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      Π i, EuclideanSpace ℂ (Fin (d i)) →L[ℂ] EuclideanSpace ℂ (Fin (d i)) :=
    StarAlgEquiv.ofAlgEquiv (AlgEquiv.piCongrRight fun i =>
      (CStarMatrix.ofMatrixStarAlgEquiv.symm.trans Matrix.toEuclideanCLM).toAlgEquiv)
      fun x => funext fun i => map_star (CStarMatrix.ofMatrixStarAlgEquiv.symm.trans
        Matrix.toEuclideanCLM) (x i)
  exact (OperatorSystem.Injective.pi fun i => OperatorSystem.injective_continuousLinearMap _).of_starAlgEquiv
    (e.trans f).symm

end CStarAlgebra

namespace NonUnitalStarSubalgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The range of a contractive projection of an injective C⋆-algebra onto a closed `⋆`-subalgebra
is injective.** The subalgebra `S` need not contain the unit of `A`. The projection is completely
positive (`LinearMap.IsProj.map_cstarMatrix_nonneg_of_norm_apply_le`, from Tomiyama's theorem), and
so is its corestriction to `S`, the inclusion of `S` being a complete order embedding; so `S` is a
retract of the injective `A` (`OperatorSystem.Injective.of_retract`). -/
lemma injective_of_isProj (hA : OperatorSystem.Injective A) {S : NonUnitalStarSubalgebra ℂ A}
    [IsClosed (S : Set A)] {φ : A →ₗ[ℂ] A} (hφ : LinearMap.IsProj S.toSubmodule φ)
    (hn : ∀ x, ‖φ x‖ ≤ ‖x‖) : OperatorSystem.Injective S := by
  have hι := NonUnitalStarAlgHom.isCompleteOrderEmbedding_of_injective
    (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective
  let E : A →CP' S :=
    ⟨LinearMap.codRestrict S.toSubmodule φ hφ.map_mem,
      fun k M hM => (hι k _).mp (hφ.map_cstarMatrix_nonneg_of_norm_apply_le hn hM)⟩
  exact hA.of_retract
    (CompletelyPositiveMapClass'.toCompletelyPositiveMap' (NonUnitalStarSubalgebraClass.subtype S)) E
    fun x => Subtype.ext (hφ.map_id x x.2)

end NonUnitalStarSubalgebra

namespace LinearMap.IsProj

variable {A : Type*} [CStarAlgebra A]

/-- **A contractive projection of a nonzero C⋆-algebra onto a unital `⋆`-subalgebra has norm one**:
it fixes `1`, of norm one. -/
lemma norm_mkContinuous_eq_one [Nontrivial A] {S : StarSubalgebra ℂ A} {φ : A →ₗ[ℂ] A}
    (hφ : LinearMap.IsProj S.toNonUnitalStarSubalgebra.toSubmodule φ) (hn : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    ‖φ.mkContinuous 1 fun x => (hn x).trans_eq (one_mul _).symm‖ = 1 := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) ?_
  have h := (φ.mkContinuous 1 fun x => (hn x).trans_eq (one_mul _).symm).le_opNorm 1
  rwa [LinearMap.mkContinuous_apply, hφ.map_id 1 S.one_mem, norm_one, mul_one] at h

end LinearMap.IsProj

namespace StarSubalgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **A closed unital `⋆`-subalgebra of an injective C⋆-algebra is injective iff it is the range of a
completely positive retraction**, the C⋆-algebra form of
`OperatorSubsystem.injective_iff_exists_retraction`: here `S` carries its own C⋆ matrix order, which
agrees with the one induced from `A`. Forward: the inclusion `S → A` is a unital complete order
embedding (`NonUnitalStarAlgHom.isCompleteOrderEmbedding_of_injective`), along which the identity of
the injective `S` extends. Backward: `S` is a retract of the injective `A`
(`OperatorSystem.Injective.of_retract`). -/
theorem injective_iff_exists_retraction (hA : OperatorSystem.Injective A) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] : OperatorSystem.Injective S ↔ ∃ E : A →CP' S, ∀ x : S, E x = x := by
  constructor
  · intro hS
    obtain ⟨E, hE⟩ := hS.exists_extension
      (NonUnitalStarAlgHom.isCompleteOrderEmbedding_of_injective S.subtype Subtype.val_injective)
      (map_one S.subtype) (CompletelyPositiveMap'.id S)
    exact ⟨E, fun x => DFunLike.congr_fun hE x⟩
  · rintro ⟨E, hE⟩
    exact hA.of_retract (CompletelyPositiveMapClass'.toCompletelyPositiveMap' S.subtype) E hE

/-- **A closed unital `⋆`-subalgebra of an injective C⋆-algebra is injective iff it is the range of a
contractive projection.** Forward: the retraction `E : A → S` of `injective_iff_exists_retraction`
is unital and positive, hence contractive (`OrderHomClass.norm_apply_le_of_map_one_le`). Backward:
`NonUnitalStarSubalgebra.injective_of_isProj`, which does not need the unit of `A` in `S`. For
`A ≠ 0` such a projection has norm one (`LinearMap.IsProj.norm_mkContinuous_eq_one`). -/
theorem injective_iff_exists_isProj (hA : OperatorSystem.Injective A) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] : OperatorSystem.Injective S ↔ ∃ φ : A →ₗ[ℂ] A,
      LinearMap.IsProj S.toNonUnitalStarSubalgebra.toSubmodule φ ∧ ∀ x, ‖φ x‖ ≤ ‖x‖ := by
  constructor
  · intro hS
    obtain ⟨E, hE⟩ := (injective_iff_exists_retraction hA S).mp hS
    refine ⟨(S.subtype : S →ₗ[ℂ] A) ∘ₗ E.toLinearMap,
      ⟨fun x => (E x).2, fun x hx => congrArg Subtype.val (hE ⟨x, hx⟩)⟩, fun x => ?_⟩
    have h1 : CompletelyPositiveMap'.equivCompletelyPositiveMap E 1 ≤ 1 :=
      le_of_eq (hE 1)
    exact OrderHomClass.norm_apply_le_of_map_one_le
      (CompletelyPositiveMap'.equivCompletelyPositiveMap E) h1 x
  · rintro ⟨φ, hφ, hn⟩
    exact NonUnitalStarSubalgebra.injective_of_isProj hA hφ hn

end StarSubalgebra
