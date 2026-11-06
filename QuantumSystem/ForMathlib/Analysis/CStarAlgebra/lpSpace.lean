/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace

/-!
# `ℓ^∞` of unital C⋆-rings and C⋆-algebras

`ℓ^∞(B)` of a family of unital normed rings is a unital ring as soon as the units `1 ∈ B i` are
uniformly bounded. Mathlib builds this ring, `lp.inftyRing`, and the algebra structure over it for
`[∀ i, NormOneClass (B i)]`, which excludes families with a zero ring among them. Here the subring
and subalgebra are built from any bound `Memℓp (1 : ∀ i, B i) ∞` (`lpInftySubring'`,
`lpInftySubalgebra'`), and the ring and algebra structures are installed for families of C⋆-rings,
whose units have norm at most `1` whether they are trivial or not (`CStarRing.norm_one_le`). On a
family of nontrivial C⋆-rings they agree definitionally with Mathlib's.

On these structures, `ℓ^∞` of a family of unital C⋆-algebras is a unital C⋆-algebra, commutative
when every member is. Mathlib provides the non-unital case and, for nontrivial members, the
commutative unital case. Two cases are added here: a family of nontrivial members that are not
commutative, built from Mathlib's own structures (`lp.instCStarAlgebraInftyOfNontrivial`), and a
family with zero members, built on the structures above. Nothing else is new: a nontrivial C⋆-ring
already has `‖1‖ = 1`, and a zero member contributes nothing to `ℓ^∞`.

## Implementation notes

On a family of nontrivial C⋆-rings the structures above agree with Mathlib's by `rfl` but not at
reducible transparency: Mathlib's unit is stated as an element of `lpInftySubring B`, which needs
`[∀ i, NormOneClass (B i)]`. They therefore have priority `100`, and every family of nontrivial
C⋆-algebras gets Mathlib's structures: through `lp.instCStarAlgebraInftyOfNontrivial`, or through
Mathlib's instance in the commutative case. The structures above are found only for a family with a
zero member, where Mathlib has none.

## Main definitions

* `lpInftySubring' B h`, `lpInftySubalgebra' 𝕜 h` — `ℓ^∞(B)` as a subring and a subalgebra of
  `∀ i, B i`, given that `1` is bounded.
* `lp.inftyRing'`, `lp.inftyNormedRing'`, `lp.inftyNormedCommRing'`, `lp.inftyAlgebra'`,
  `lp.inftyNormedAlgebra'` — the unital structures on `ℓ^∞` of a family of unital C⋆-rings.
* `lp.instCStarAlgebraInfty`, `lp.instCommCStarAlgebraInfty` — `ℓ^∞` of a family of unital
  C⋆-algebras is a unital C⋆-algebra.
* `lp.instCStarAlgebraInftyOfNontrivial` — the same for a family of nontrivial unital C⋆-algebras,
  on Mathlib's structures.

## Main results

* `CStarRing.norm_one_le` — the unit of a C⋆-ring has norm at most `1`: it is `1` when the ring is
  nontrivial (`CStarRing.norm_one`) and `0` otherwise.
-/

@[expose] public section

open scoped ENNReal

namespace CStarRing

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]

/-- The unit of a C⋆-ring has norm at most `1`. -/
lemma norm_one_le : ‖(1 : E)‖ ≤ 1 := by
  cases subsingleton_or_nontrivial E
  · simp [Subsingleton.elim (1 : E) 0]
  · exact norm_one.le

end CStarRing

namespace lp

section NormedRing

variable {I : Type*} {B : I → Type*} [∀ i, NormedRing (B i)]

variable (B) in
/-- The subring of elements of `∀ i, B i` whose `lp` norm is finite, given that `1` is bounded. This
is `lp B ∞`, with extra structure; `lpInftySubring B` is the case `h = one_memℓp_infty`. -/
def _root_.lpInftySubring' (h : Memℓp (1 : ∀ i, B i) ∞) : Subring (PreLp B) :=
  { lp B ∞ with
    carrier := { f | Memℓp f ∞ }
    one_mem' := h
    mul_mem' := Memℓp.infty_mul }

variable [∀ i, StarRing (B i)] [∀ i, CStarRing (B i)]

/-- The unit of `∀ i, B i` is bounded for a family of C⋆-rings. -/
lemma _root_.one_memℓp_infty' : Memℓp (1 : ∀ i, B i) ∞ :=
  ⟨1, by rintro i ⟨i, rfl⟩; exact CStarRing.norm_one_le⟩

/-- `ℓ^∞` of a family of unital C⋆-rings is a ring. -/
noncomputable instance (priority := 100) inftyRing' : Ring (lp B ∞) :=
  inferInstanceAs <| Ring (lpInftySubring' B one_memℓp_infty')

/-- Powers of a bounded family of elements of C⋆-rings are bounded. -/
lemma _root_.Memℓp.infty_pow' {f : ∀ i, B i} (hf : Memℓp f ∞) (n : ℕ) : Memℓp (f ^ n) ∞ :=
  (lpInftySubring' B one_memℓp_infty').pow_mem hf n

/-- Natural number casts in `∀ i, B i` are bounded for a family of C⋆-rings. -/
lemma _root_.natCast_memℓp_infty' (n : ℕ) : Memℓp (n : ∀ i, B i) ∞ :=
  natCast_mem (lpInftySubring' B one_memℓp_infty') n

/-- Integer casts in `∀ i, B i` are bounded for a family of C⋆-rings. -/
lemma _root_.intCast_memℓp_infty' (z : ℤ) : Memℓp (z : ∀ i, B i) ∞ :=
  intCast_mem (lpInftySubring' B one_memℓp_infty') z

/-- The unit of `ℓ^∞(B)` is the constant family `1`. -/
@[simp]
lemma infty_coeFn_one' : ⇑(1 : lp B ∞) = 1 :=
  rfl

/-- Powers in `ℓ^∞(B)` are computed componentwise. -/
@[simp]
lemma infty_coeFn_pow' (f : lp B ∞) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

/-- Natural number casts in `ℓ^∞(B)` are the constant families. -/
@[simp]
lemma infty_coeFn_natCast' (n : ℕ) : ⇑(n : lp B ∞) = n :=
  rfl

/-- Integer casts in `ℓ^∞(B)` are the constant families. -/
@[simp]
lemma infty_coeFn_intCast' (z : ℤ) : ⇑(z : lp B ∞) = z :=
  rfl

/-- `ℓ^∞` of a family of unital C⋆-rings is a normed ring. -/
noncomputable instance (priority := 100) inftyNormedRing' : NormedRing (lp B ∞) :=
  { lp.inftyRing', lp.nonUnitalNormedRing with }

end NormedRing

/-- `ℓ^∞` of a family of commutative unital C⋆-rings is a normed commutative ring. -/
noncomputable instance (priority := 100) inftyNormedCommRing' {I : Type*} {B : I → Type*}
    [∀ i, NormedCommRing (B i)] [∀ i, StarRing (B i)] [∀ i, CStarRing (B i)] :
    NormedCommRing (lp B ∞) where
  mul_comm := mul_comm

section Algebra

variable {𝕜 : Type*} {I : Type*} {B : I → Type*}
variable [NormedField 𝕜] [∀ i, NormedRing (B i)] [∀ i, NormedAlgebra 𝕜 (B i)]

/-- Scalars are bounded in `∀ i, B i` as soon as `1` is. -/
lemma _root_.algebraMap_memℓp_infty_of_one (h : Memℓp (1 : ∀ i, B i) ∞) (k : 𝕜) :
    Memℓp (algebraMap 𝕜 (∀ i, B i) k) ∞ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (h.const_smul k : Memℓp (k • (1 : ∀ i, B i)) ∞)

variable (𝕜) in
/-- The `𝕜`-subalgebra of elements of `∀ i, B i` whose `lp` norm is finite, given that `1` is
bounded. This is `lp B ∞`, with extra structure; `lpInftySubalgebra 𝕜 B` is the case
`h = one_memℓp_infty`. -/
def _root_.lpInftySubalgebra' (h : Memℓp (1 : ∀ i, B i) ∞) : Subalgebra 𝕜 (PreLp B) :=
  { lpInftySubring' B h with
    carrier := { f | Memℓp f ∞ }
    algebraMap_mem' := algebraMap_memℓp_infty_of_one h }

variable [∀ i, StarRing (B i)] [∀ i, CStarRing (B i)]

/-- Scalars are bounded in `∀ i, B i` for a family of C⋆-rings. -/
lemma _root_.algebraMap_memℓp_infty' (k : 𝕜) : Memℓp (algebraMap 𝕜 (∀ i, B i) k) ∞ :=
  algebraMap_memℓp_infty_of_one one_memℓp_infty' k

/-- `ℓ^∞` of a family of unital C⋆-rings that are `𝕜`-algebras is a `𝕜`-algebra. -/
noncomputable instance (priority := 100) inftyAlgebra' : Algebra 𝕜 (lp B ∞) :=
  inferInstanceAs <| Algebra 𝕜 (lpInftySubalgebra' 𝕜 (one_memℓp_infty' (B := B)))

/-- `ℓ^∞` of a family of unital C⋆-rings that are normed `𝕜`-algebras is a normed `𝕜`-algebra. -/
noncomputable instance (priority := 100) inftyNormedAlgebra' : NormedAlgebra 𝕜 (lp B ∞) where
  norm_smul_le := norm_smul_le

example : (inftyAlgebra' : Algebra 𝕜 (lp B ∞)).toModule = lp.instModuleSubtypePreLpMemAddSubgroup := by
  with_reducible_and_instances rfl

example : (inftyNormedAlgebra' : NormedAlgebra 𝕜 (lp B ∞)).toNormedSpace = lp.instNormedSpace := by
  with_reducible_and_instances rfl

example [∀ i, Nontrivial (B i)] : (inftyAlgebra' : Algebra 𝕜 (lp B ∞)) =
    lp.instAlgebraSubtypePreLpMemAddSubgroupTopENNReal := by
  rfl

end Algebra

section Examples

variable {I : Type*} {B : I → Type*} [∀ i, NormedRing (B i)] [∀ i, StarRing (B i)]
  [∀ i, CStarRing (B i)]

example : (inftyNormedRing' : NormedRing (lp B ∞)).toNonUnitalNormedRing = lp.nonUnitalNormedRing := by
  with_reducible_and_instances rfl

example [∀ i, Nontrivial (B i)] : (inftyNormedRing' : NormedRing (lp B ∞)) = lp.inftyNormedRing := by
  rfl

end Examples

end lp

section CStarAlgebra

variable {ι : Type*} {A : ι → Type*}

/-- `ℓ^∞` of a family of unital C⋆-algebras is a unital C⋆-algebra. -/
noncomputable instance (priority := 100) lp.instCStarAlgebraInfty [∀ i, CStarAlgebra (A i)] :
    CStarAlgebra (lp A ∞) where

/-- `ℓ^∞` of a family of commutative unital C⋆-algebras is a commutative unital C⋆-algebra. -/
noncomputable instance (priority := 100) lp.instCommCStarAlgebraInfty [∀ i, CommCStarAlgebra (A i)] :
    CommCStarAlgebra (lp A ∞) where
  mul_comm := mul_comm

/-- `ℓ^∞` of a family of nontrivial unital C⋆-algebras is a unital C⋆-algebra, on Mathlib's normed
ring and normed algebra structures. -/
noncomputable instance lp.instCStarAlgebraInftyOfNontrivial [∀ i, CStarAlgebra (A i)]
    [∀ i, Nontrivial (A i)] : CStarAlgebra (lp A ∞) where

-- On nontrivial members the inferred structures are Mathlib's, with no diamond.
example [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] :
    (inferInstance : CStarAlgebra (lp A ∞)).toNormedRing = lp.inftyNormedRing := by
  with_reducible_and_instances rfl

example [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] :
    (inferInstance : CStarAlgebra (lp A ∞)).toNormedAlgebra =
      (lp.inftyNormedAlgebra : NormedAlgebra ℂ (lp A ∞)) := by
  with_reducible_and_instances rfl

example [∀ i, CommCStarAlgebra (A i)] [∀ i, Nontrivial (A i)] :
    (inferInstance : CommCStarAlgebra (lp A ∞)).toCStarAlgebra =
      (inferInstance : CStarAlgebra (lp A ∞)) := by
  with_reducible_and_instances rfl

-- A statement made for arbitrary members and specialised to nontrivial ones differs from the
-- inferred structure only in the unit and the casts, which agree by `rfl`.
example [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] :
    (lp.instCStarAlgebraInfty : CStarAlgebra (lp A ∞)).toNonUnitalCStarAlgebra =
      (lp.instCStarAlgebraInftyOfNontrivial : CStarAlgebra (lp A ∞)).toNonUnitalCStarAlgebra := by
  with_reducible_and_instances rfl

example [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] :
    (lp.instCStarAlgebraInfty : CStarAlgebra (lp A ∞)) = lp.instCStarAlgebraInftyOfNontrivial := by
  rfl

example [∀ i, CStarAlgebra (A i)] :
    (lp.instCStarAlgebraInfty : CStarAlgebra (lp A ∞)).toNonUnitalCStarAlgebra =
      (inferInstance : NonUnitalCStarAlgebra (lp A ∞)) := by
  with_reducible_and_instances rfl

example [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] :
    (lp.instCStarAlgebraInfty : CStarAlgebra (lp A ∞)).toNormedRing = lp.inftyNormedRing := by
  rfl

example [∀ i, CommCStarAlgebra (A i)] :
    (lp.instCommCStarAlgebraInfty : CommCStarAlgebra (lp A ∞)).toCStarAlgebra =
      lp.instCStarAlgebraInfty := by
  with_reducible_and_instances rfl

end CStarAlgebra
