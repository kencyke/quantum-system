module

public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section


/-- A left ideal in a non-unital C*-algebra: a subgroup closed under left multiplication
and scalar multiplication. -/
class CStarAlgebraIdeal (A : Type*) [NonUnitalCStarAlgebra A] extends AddSubgroup A, SubMulAction ℂ A where
  mul_mem' : ∀ (a : A) {x : A}, x ∈ carrier → a * x ∈ carrier

namespace CStarAlgebraIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The equivalence relation on `A` induced by a left ideal. -/
def leftRel (I : CStarAlgebraIdeal A) : Setoid A :=
  QuotientAddGroup.leftRel I.toAddSubgroup

/-- The quotient of a C*-algebra by an ideal. -/
instance instHasQuotient : HasQuotient A (CStarAlgebraIdeal A) where
  quotient' I := Quotient (leftRel I)

instance : SetLike (CStarAlgebraIdeal A) A where
  coe I := I.carrier
  coe_injective' p q h := by
    cases p
    cases q
    congr
    ext x
    simpa [AddSubgroup.mem_carrier] using Set.ext_iff.mp h x

instance (I : CStarAlgebraIdeal A) : AddCommGroup (A ⧸ I) :=
  QuotientAddGroup.Quotient.addCommGroup I.toAddSubgroup

instance (I : CStarAlgebraIdeal A) : Module ℂ (A ⧸ I) where
  smul c := Quotient.map' (c • ·) fun x y h =>
    QuotientAddGroup.leftRel_apply.mpr <| by
      simpa using I.smul_mem' c (QuotientAddGroup.leftRel_apply.mp h)
  one_smul a := Quotient.inductionOn' a fun x => congr_arg Quotient.mk'' (one_smul ℂ x)
  mul_smul c₁ c₂ a := Quotient.inductionOn' a fun x => congr_arg Quotient.mk'' (mul_smul c₁ c₂ x)
  smul_zero c := congr_arg Quotient.mk'' (smul_zero c : c • (0 : A) = 0)
  smul_add c a b := Quotient.inductionOn₂' a b fun x y =>
    congr_arg Quotient.mk'' (smul_add c x y)
  add_smul c₁ c₂ a := Quotient.inductionOn' a fun x =>
    congr_arg Quotient.mk'' (add_smul c₁ c₂ x)
  zero_smul a := Quotient.inductionOn' a fun x => congr_arg Quotient.mk'' (zero_smul ℂ x)

end CStarAlgebraIdeal
