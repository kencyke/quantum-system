module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Comparison
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Type I von Neumann algebras

The general **type I** property, phrased as in the literature (Takesaki V.1, Blackadar III.1.5):
every nonzero central projection dominates a nonzero abelian projection. For a *factor* this is
equivalent to the existence of a minimal projection, i.e. to `IsTypeIFactor`. The equivalence is
proved in full: the easy direction is minimal ⇒ abelian ⇒ type I; the converse first shows that
an abelian projection of a factor is order-minimal (a corner-commutation argument through the
central-support lemma `IsFactor.exists_mul_ne`), then that order-minimality forces the trivial
corner `p N p = ℂ p` — the positive/negative parts of a self-adjoint corner element (non-unital
continuous functional calculus inside the norm-closed corner subalgebra) yield an order
dichotomy, and a Dedekind-cut argument on `{c : ℝ | 0 ≤ x - c • p}` pins each self-adjoint
corner element to a real multiple of `p`.

## Main definitions

* `VonNeumannAlgebra.IsTypeI N` — every nonzero central projection of `N` dominates a nonzero
  abelian projection.
* `VonNeumannAlgebra.cornerNonUnitalStarSubalgebra N hp` — the norm-closed corner `{y ∈ N | p y
  = y = y p}`.

## Main results

* `VonNeumannAlgebra.IsFactor.subprojection_eq_of_isAbelianProjection` — in a factor, an abelian
  projection has no proper nonzero subprojection.
* `VonNeumannAlgebra.isMinimalProjection_of_forall_subprojection` — order-minimality implies the
  trivial corner.
* `VonNeumannAlgebra.IsFactor.isMinimalProjection_of_isAbelianProjection` — in a factor, a
  nonzero abelian projection is minimal.
* `VonNeumannAlgebra.IsFactor.isTypeI_iff_exists_isMinimalProjection` — a factor is type I iff
  it has a minimal projection.
* `VonNeumannAlgebra.isTypeIFactor_iff_isFactor_and_isTypeI` — `IsTypeIFactor N ↔ IsFactor N ∧
  IsTypeI N`.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Type I von Neumann algebra**: every nonzero central projection dominates a nonzero abelian
projection. The subprojection relation `p ≤ z` is written algebraically as `z * p = p`, as
everywhere in this development. -/
def IsTypeI (N : VonNeumannAlgebra H) : Prop :=
  ∀ z : H →L[ℂ] H, IsCentralProjection N z → z ≠ 0 →
    ∃ p : H →L[ℂ] H, IsAbelianProjection N p ∧ p ≠ 0 ∧ z * p = p

/-- A factor with a minimal projection is type I: the only nonzero central projection of a factor
is `1` (`central_projection_eq`), and it dominates the minimal projection, which is abelian and
nonzero. -/
lemma IsFactor.isTypeI_of_exists_isMinimalProjection [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) (h : ∃ e : H →L[ℂ] H, IsMinimalProjection N e) : IsTypeI N := by
  obtain ⟨e, he⟩ := h
  intro z hz hz0
  rcases hN.central_projection_eq hz with h0 | h1
  · exact absurd h0 hz0
  · exact ⟨e, he.isAbelianProjection, he.2.2.1, by rw [h1, one_mul]⟩

/-- **In a factor, an abelian projection is order-minimal**: a projection `q ∈ N` with `q ≤ p`
(written `p * q = q`) is `0` or `p`.

The proof avoids corner-commutant theory and polar decomposition: if `0 ≠ q ≠ p`, then
`r := p - q` is a nonzero projection under `p` orthogonal to `q`, and the central-support lemma
`IsFactor.exists_mul_ne` produces `a ∈ N` with `z := r a q ≠ 0`. Both `z` and `z⋆` are corner
elements of `p`, so they commute by abelianness; but `q z = 0` and `q z⋆ = z⋆` force
`z⋆ z = q (z z⋆) = (q z) z⋆ = 0`, and the C⋆-identity gives `z = 0` — a contradiction. -/
theorem IsFactor.subprojection_eq_of_isAbelianProjection [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {p : H →L[ℂ] H} (hp : IsAbelianProjection N p)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqN : q ∈ N) (hsub : p * q = q) :
    q = 0 ∨ q = p := by
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  by_cases hqp : q = p
  · exact Or.inr hqp
  exfalso
  have hqmul : q * p = q := isStarProjection_subproj_comm hp.1 hq hsub
  set r : H →L[ℂ] H := p - q with hr
  have hpr : p * r = r := by
    rw [hr, mul_sub, hp.1.isIdempotentElem, hsub]
  have hqr : q * r = 0 := by
    rw [hr, mul_sub, hqmul, hq.isIdempotentElem, sub_self]
  have hrsa : star r = r := by
    rw [hr, star_sub, hp.1.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
  have hrN : r ∈ N := sub_mem hp.2.1 hqN
  have hr0 : r ≠ 0 := fun h0 => hqp (by rw [hr, sub_eq_zero] at h0; exact h0.symm)
  obtain ⟨a, haN, hz0⟩ := hN.exists_mul_ne hqN hq0 hr0
  set z : H →L[ℂ] H := r * a * q with hz
  have hzN : z ∈ N := mul_mem (mul_mem hrN haN) hqN
  have hzcorner : p * z * p = z := by
    rw [hz]
    calc p * (r * a * q) * p
        = (p * r) * a * (q * p) := by simp only [mul_assoc]
      _ = r * a * q := by rw [hpr, hqmul]
  have hzstar : star z = q * (star a * r) := by
    rw [hz, star_mul, star_mul, hrsa, hq.isSelfAdjoint.star_eq]
  have hcomm : z * star z = star z * z := by
    have hzc : p * star z * p = star z := by
      have h2 := congrArg star hzcorner
      rw [star_mul, star_mul, hp.1.isSelfAdjoint.star_eq] at h2
      rw [mul_assoc]
      exact h2
    have h1 := hp.2.2 z hzN (star z) (star_mem hzN)
    rwa [hzcorner, hzc] at h1
  have hqz : q * z = 0 := by
    rw [hz, ← mul_assoc, ← mul_assoc, hqr, zero_mul, zero_mul]
  have hqstarz : q * star z = star z := by
    rw [hzstar, ← mul_assoc, hq.isIdempotentElem]
  have hzz0 : star z * z = 0 := by
    have h6 : q * (z * star z) = q * (star z * z) := by rw [hcomm]
    rw [← mul_assoc, hqz, zero_mul] at h6
    rw [← mul_assoc, hqstarz] at h6
    exact h6.symm
  have hznorm : ‖z‖ = 0 := by
    have hmul := CStarRing.norm_star_mul_self (x := z)
    rw [hzz0, norm_zero] at hmul
    exact mul_self_eq_zero.mp hmul.symm
  exact hz0 (norm_eq_zero.mp hznorm)

/-! ### The corner subalgebra

The elements of `N` supported on a star projection `p` on both sides form a norm-closed
non-unital star subalgebra. Norm-closedness is what lets the non-unital continuous functional
calculus (`cfcₙ_mem`) operate inside the corner: the positive and negative parts of a
self-adjoint corner element stay in the corner. -/

/-- The **corner** of `N` at a star projection `p`: the elements of `N` supported on `p` on
both sides, as a non-unital star subalgebra of `B(H)`. -/
def cornerNonUnitalStarSubalgebra (N : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {y | y ∈ N ∧ p * y = y ∧ y * p = y}
  add_mem' := by
    rintro y z ⟨hyN, hpy, hyp⟩ ⟨hzN, hpz, hzp⟩
    exact ⟨add_mem hyN hzN, by rw [mul_add, hpy, hpz], by rw [add_mul, hyp, hzp]⟩
  zero_mem' := ⟨zero_mem _, mul_zero p, zero_mul p⟩
  mul_mem' := by
    rintro y z ⟨hyN, hpy, hyp⟩ ⟨hzN, hpz, hzp⟩
    exact ⟨mul_mem hyN hzN, by rw [← mul_assoc, hpy], by rw [mul_assoc, hzp]⟩
  smul_mem' := by
    rintro c y ⟨hyN, hpy, hyp⟩
    exact ⟨smul_mem c hyN, by rw [mul_smul_comm, hpy], by rw [smul_mul_assoc, hyp]⟩
  star_mem' := by
    rintro y ⟨hyN, hpy, hyp⟩
    refine ⟨star_mem hyN, ?_, ?_⟩
    · have h := congrArg star hyp
      rwa [star_mul, hp.isSelfAdjoint.star_eq] at h
    · have h := congrArg star hpy
      rwa [star_mul, hp.isSelfAdjoint.star_eq] at h

/-- Membership in the corner subalgebra, unfolded. -/
lemma mem_cornerNonUnitalStarSubalgebra_iff {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    {hp : IsStarProjection p} {y : H →L[ℂ] H} :
    y ∈ cornerNonUnitalStarSubalgebra N hp ↔ y ∈ N ∧ p * y = y ∧ y * p = y :=
  Iff.rfl

/-- The corner subalgebra is norm-closed: it is the intersection of the (double-centralizer,
hence closed) carrier of `N` with the closed support conditions `p * y = y` and `y * p = y`. -/
lemma isClosed_cornerNonUnitalStarSubalgebra (N : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) :
    IsClosed ((cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))) := by
  have hset : (cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))
      = (N : Set (H →L[ℂ] H)) ∩ ({y | p * y = y} ∩ {y | y * p = y}) := by
    ext y
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [hset]
  refine N.isClosed_coe.inter (IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_const.mul continuous_id) continuous_id
  · exact isClosed_eq (continuous_id.mul continuous_const) continuous_id

/-- The positive part of a corner element stays in the corner. -/
lemma posPart_mem_cornerNonUnitalStarSubalgebra {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) {d : H →L[ℂ] H}
    (hd : d ∈ cornerNonUnitalStarSubalgebra N hp) :
    d⁺ ∈ cornerNonUnitalStarSubalgebra N hp := by
  haveI : IsClosed ((cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))) :=
    isClosed_cornerNonUnitalStarSubalgebra N hp
  haveI : IsScalarTower ℝ ℂ (H →L[ℂ] H) := IsScalarTower.complexToReal
  rw [CFC.posPart_def]
  exact cfcₙ_mem _ hd

/-- The negative part of a corner element stays in the corner. -/
lemma negPart_mem_cornerNonUnitalStarSubalgebra {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) {d : H →L[ℂ] H}
    (hd : d ∈ cornerNonUnitalStarSubalgebra N hp) :
    d⁻ ∈ cornerNonUnitalStarSubalgebra N hp := by
  haveI : IsClosed ((cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))) :=
    isClosed_cornerNonUnitalStarSubalgebra N hp
  haveI : IsScalarTower ℝ ℂ (H →L[ℂ] H) := IsScalarTower.complexToReal
  rw [CFC.negPart_def]
  exact cfcₙ_mem _ hd

/-! ### Range projections

For `x ∈ N`, the orthogonal projection onto the closure of `range x` lies in `N`; it is nonzero
when `x` is, it is dominated by any projection acting as the identity on the left of `x`, and the
range projections of two operators with `x₁ x₂ = 0`, `x₁` self-adjoint, are orthogonal. -/

/-- The orthogonal projection onto the closure of the range of `x ∈ N` lies in `N`, because that
subspace is invariant under the commutant. -/
lemma starProjection_range_mem {N : VonNeumannAlgebra H} {x : H →L[ℂ] H} (hx : x ∈ N) :
    (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure.starProjection ∈ N := by
  set M : Submodule ℂ H := (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure with hM
  have hpproj : IsStarProjection M.starProjection := isStarProjection_starProjection
  rw [IsStarProjection.mem_iff hpproj N]
  intro y hyN'
  rw [Submodule.range_starProjection]
  have hcl : IsClosed ((M.comap (y : H →ₗ[ℂ] H)) : Set H) := by
    rw [Submodule.comap_coe]
    exact ((LinearMap.range (x : H →ₗ[ℂ] H)).isClosed_topologicalClosure).preimage y.continuous
  have hle : M ≤ M.comap (y : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ hcl
    rintro z ⟨v, rfl⟩
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    have hxy : x * y = y * x := mem_commutant_iff.mp hyN' x hx
    rw [show y (x v) = (y * x) v from rfl, ← hxy]
    exact Submodule.le_topologicalClosure _ ⟨y v, rfl⟩
  exact hle

/-- The range projection of a nonzero operator is nonzero. -/
lemma starProjection_range_ne_zero {x : H →L[ℂ] H} (hx0 : x ≠ 0) :
    (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure.starProjection ≠ 0 := by
  intro h0
  apply hx0
  ext v
  have hmem : x v ∈ (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure :=
    Submodule.le_topologicalClosure _ ⟨v, rfl⟩
  have hfix := Submodule.starProjection_eq_self_iff.mpr hmem
  rw [h0] at hfix
  simpa using hfix.symm

/-- If `p * x = x`, then the range projection of `x` is a subprojection of `p`. -/
lemma starProjection_range_subproj {p x : H →L[ℂ] H} (hpx : p * x = x) :
    p * (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure.starProjection
      = (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure.starProjection := by
  set M : Submodule ℂ H := (LinearMap.range (x : H →ₗ[ℂ] H)).topologicalClosure with hM
  have hle : M ≤ LinearMap.ker ((p - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (p - 1).isClosed_ker
    rintro z ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply]
    rw [show p (x v) = (p * x) v from rfl, hpx]
    exact sub_self _
  ext w
  have hker := hle (M.starProjection_apply_mem w)
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, sub_eq_zero] at hker
  exact hker

/-- The range projections of `x₁` and `x₂` with `x₁` self-adjoint and `x₁ * x₂ = 0` are
orthogonal. -/
lemma starProjection_range_mul_eq_zero {x₁ x₂ : H →L[ℂ] H} (hsa : star x₁ = x₁)
    (h12 : x₁ * x₂ = 0) :
    (LinearMap.range (x₁ : H →ₗ[ℂ] H)).topologicalClosure.starProjection
      * (LinearMap.range (x₂ : H →ₗ[ℂ] H)).topologicalClosure.starProjection = 0 := by
  set M₁ : Submodule ℂ H := (LinearMap.range (x₁ : H →ₗ[ℂ] H)).topologicalClosure with hM₁
  set M₂ : Submodule ℂ H := (LinearMap.range (x₂ : H →ₗ[ℂ] H)).topologicalClosure with hM₂
  have hadj : ContinuousLinearMap.adjoint x₁ = x₁ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hsa]
  have hortho : M₂ ⟂ M₁ := by
    rw [Submodule.isOrtho_iff_le]
    refine Submodule.topologicalClosure_minimal _ ?_ M₁.isClosed_orthogonal
    rintro z ⟨u, rfl⟩
    rw [Submodule.mem_orthogonal]
    intro m hm
    have hker : M₁ ≤ LinearMap.ker ((innerSL ℂ (x₂ u)) : H →ₗ[ℂ] ℂ) := by
      refine Submodule.topologicalClosure_minimal _ ?_ (innerSL ℂ _).isClosed_ker
      rintro w ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left x₁, hadj,
        show x₁ (x₂ u) = (x₁ * x₂) u from rfl, h12]
      simp
    have h0 := hker hm
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at h0
    exact inner_eq_zero_symm.mp h0
  rw [ContinuousLinearMap.mul_def]
  exact Submodule.starProjection_comp_starProjection_eq_zero_iff.mpr hortho.symm

/-! ### Order-minimality implies corner triviality

The dichotomy: a self-adjoint corner element of an order-minimal projection is comparable to `0`
in the Loewner order, because its positive and negative parts would otherwise produce two
orthogonal nonzero subprojections of `p`. A Dedekind-cut argument on
`{c : ℝ | 0 ≤ x - c • p}` then pins every self-adjoint corner element to `x = c₀ • p`. -/

/-- **Dichotomy.** If `p` has no proper nonzero subprojection in `N`, every self-adjoint corner
element `d` satisfies `0 ≤ d` or `d ≤ 0`. -/
lemma nonneg_or_nonpos_of_forall_subprojection {N : VonNeumannAlgebra H}
    {p : H →L[ℂ] H} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hmin : ∀ q, IsStarProjection q → q ∈ N → p * q = q → q = 0 ∨ q = p)
    {d : H →L[ℂ] H} (hdsa : IsSelfAdjoint d)
    (hd : d ∈ cornerNonUnitalStarSubalgebra N hp) :
    0 ≤ d ∨ d ≤ 0 := by
  have hdplus := posPart_mem_cornerNonUnitalStarSubalgebra hp hd
  have hdminus := negPart_mem_cornerNonUnitalStarSubalgebra hp hd
  have hsub : d⁺ - d⁻ = d := CFC.posPart_sub_negPart d hdsa
  by_cases hplus0 : d⁺ = 0
  · right
    rw [← hsub, hplus0, zero_sub]
    exact neg_nonpos.mpr (CFC.negPart_nonneg d)
  by_cases hminus0 : d⁻ = 0
  · left
    rw [← hsub, hminus0, sub_zero]
    exact CFC.posPart_nonneg d
  exfalso
  have hPplus := hmin _ isStarProjection_starProjection (starProjection_range_mem hdplus.1)
    (starProjection_range_subproj hdplus.2.1)
  have hPminus := hmin _ isStarProjection_starProjection (starProjection_range_mem hdminus.1)
    (starProjection_range_subproj hdminus.2.1)
  rcases hPplus with h | hPp
  · exact starProjection_range_ne_zero hplus0 h
  rcases hPminus with h | hPm
  · exact starProjection_range_ne_zero hminus0 h
  have horth := starProjection_range_mul_eq_zero
    (CFC.posPart_nonneg d).isSelfAdjoint.star_eq (CFC.posPart_mul_negPart d)
  rw [hPp, hPm, hp.isIdempotentElem] at horth
  exact hp0 horth

/-- **Cut.** If `p` has no proper nonzero subprojection in `N`, every self-adjoint corner
element is a real multiple of `p`: the supremum `c₀` of `{c : ℝ | 0 ≤ x - c • p}` (nonempty,
bounded, closed) satisfies `x = c₀ • p`, since by the dichotomy `x - c • p ≤ 0` for every
`c > c₀`. -/
lemma exists_real_smul_eq_of_forall_subprojection {N : VonNeumannAlgebra H}
    {p : H →L[ℂ] H} (hp : IsStarProjection p) (hpN : p ∈ N) (hp0 : p ≠ 0)
    (hmin : ∀ q, IsStarProjection q → q ∈ N → p * q = q → q = 0 ∨ q = p)
    {x : H →L[ℂ] H} (hxsa : IsSelfAdjoint x)
    (hx : x ∈ cornerNonUnitalStarSubalgebra N hp) :
    ∃ c : ℝ, x = (c : ℂ) • p := by
  obtain ⟨hxN, hpx, hxp⟩ := hx
  -- positivity of a self-adjoint operator through diagonal inner products
  have hpos_iff : ∀ T : H →L[ℂ] H, IsSelfAdjoint T →
      (0 ≤ T ↔ ∀ v, 0 ≤ RCLike.re (inner ℂ (T v) v)) := by
    intro T hT
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact ⟨fun h => h.2, fun h => ⟨hT, h⟩⟩
  have hsa_c : ∀ c : ℝ, IsSelfAdjoint (x - (c : ℂ) • p) := by
    intro c
    rw [IsSelfAdjoint, star_sub, star_smul, hxsa.star_eq, hp.isSelfAdjoint.star_eq,
      Complex.star_def, Complex.conj_ofReal]
  have hcalc : ∀ (c : ℝ) (v : H), RCLike.re (inner ℂ ((x - (c : ℂ) • p) v) v)
      = RCLike.re (inner ℂ (x v) v) - c * RCLike.re (inner ℂ (p v) v) := by
    intro c v
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
      inner_smul_left, Complex.conj_ofReal, map_sub,
      show RCLike.re ((c : ℂ) * inner ℂ (p v) v) = c * RCLike.re (inner ℂ (p v) v) from
        RCLike.re_ofReal_mul c _]
  have hpvv : ∀ v, RCLike.re (inner ℂ (p v) v) = ‖p v‖ ^ 2 := by
    intro v
    have h1 : inner ℂ (p v) v = inner ℂ (p v) (p v) := by
      calc inner ℂ (p v) v = inner ℂ (p (p v)) v := by
            rw [show p (p v) = (p * p) v from rfl, hp.isIdempotentElem]
        _ = inner ℂ (ContinuousLinearMap.adjoint p (p v)) v := by
            rw [hp.isSelfAdjoint.adjoint_eq]
        _ = inner ℂ (p v) (p v) := ContinuousLinearMap.adjoint_inner_left p v (p v)
    rw [h1, inner_self_eq_norm_sq]
  -- the cut set
  set A : Set ℝ := {c : ℝ | 0 ≤ x - (c : ℂ) • p} with hA
  have hmemA : ∀ c : ℝ, c ∈ A ↔
      ∀ v, c * ‖p v‖ ^ 2 ≤ RCLike.re (inner ℂ (x v) v) := by
    intro c
    rw [hA, Set.mem_setOf_eq, hpos_iff _ (hsa_c c)]
    constructor
    · intro h v
      have := h v
      rw [hcalc, hpvv, sub_nonneg] at this
      exact this
    · intro h v
      rw [hcalc, hpvv, sub_nonneg]
      exact h v
  -- `x` is supported on the corner: `re ⟪x v, v⟫ = re ⟪x (p v), p v⟫`
  have hxvv : ∀ v, RCLike.re (inner ℂ (x v) v) = RCLike.re (inner ℂ (x (p v)) (p v)) := by
    intro v
    have h1 : x v = x (p v) := by rw [← ContinuousLinearMap.mul_apply, hxp]
    have h2 : x (p v) = p (x (p v)) := by
      rw [show p (x (p v)) = (p * x) (p v) from rfl, hpx]
    calc RCLike.re (inner ℂ (x v) v) = RCLike.re (inner ℂ (p (x (p v))) v) := by
          conv_lhs => rw [h1, h2]
      _ = RCLike.re (inner ℂ (x (p v)) (p v)) := by
          have h3 : inner ℂ (p (x (p v))) v = inner ℂ (x (p v)) (p v) := by
            conv_lhs => rw [show p (x (p v)) = ContinuousLinearMap.adjoint p (x (p v)) by
              rw [hp.isSelfAdjoint.adjoint_eq]]
            exact ContinuousLinearMap.adjoint_inner_left p v (x (p v))
          rw [h3]
  -- nonempty: `-‖x‖ ∈ A`
  have hAne : A.Nonempty := by
    refine ⟨-‖x‖, (hmemA _).mpr fun v => ?_⟩
    rw [hxvv]
    have hbound : |RCLike.re (inner ℂ (x (p v)) (p v))| ≤ ‖x‖ * ‖p v‖ ^ 2 := by
      calc |RCLike.re (inner ℂ (x (p v)) (p v))| ≤ ‖inner ℂ (x (p v)) (p v)‖ :=
            RCLike.abs_re_le_norm _
        _ ≤ ‖x (p v)‖ * ‖p v‖ := norm_inner_le_norm _ _
        _ ≤ (‖x‖ * ‖p v‖) * ‖p v‖ :=
            mul_le_mul_of_nonneg_right (x.le_opNorm _) (norm_nonneg _)
        _ = ‖x‖ * ‖p v‖ ^ 2 := by ring
    calc -‖x‖ * ‖p v‖ ^ 2 = -(‖x‖ * ‖p v‖ ^ 2) := by ring
      _ ≤ RCLike.re (inner ℂ (x (p v)) (p v)) := neg_le_of_abs_le hbound
  -- bounded above
  have hAbdd : BddAbove A := by
    obtain ⟨w, hw⟩ : ∃ w, p w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hp0 (ContinuousLinearMap.ext fun w => by simp [hcon w])
    refine ⟨RCLike.re (inner ℂ (x w) w) / ‖p w‖ ^ 2, fun c hc => ?_⟩
    have h1 := (hmemA c).mp hc w
    have h2 : (0 : ℝ) < ‖p w‖ ^ 2 := by positivity
    exact (le_div_iff₀ h2).mpr h1
  -- closed
  have hAclosed : IsClosed A := by
    have hAeq : A = ⋂ v : H,
        {c : ℝ | c * ‖p v‖ ^ 2 ≤ RCLike.re (inner ℂ (x v) v)} := by
      ext c
      simp only [Set.mem_iInter, Set.mem_setOf_eq, ← hmemA c]
    rw [hAeq]
    exact isClosed_iInter fun v =>
      isClosed_le (continuous_id.mul continuous_const) continuous_const
  set c₀ : ℝ := sSup A with hc₀
  have hc₀A : c₀ ∈ A := hAclosed.csSup_mem hAne hAbdd
  refine ⟨c₀, ?_⟩
  -- for every `c > c₀`, the dichotomy forces `x - c • p ≤ 0`
  have hpmem : p ∈ cornerNonUnitalStarSubalgebra N hp :=
    ⟨hpN, hp.isIdempotentElem, hp.isIdempotentElem⟩
  have hupper : ∀ ε : ℝ, 0 < ε → x - ((c₀ + ε : ℝ) : ℂ) • p ≤ 0 := by
    intro ε hε
    have hnotA : (c₀ + ε) ∉ A := fun hmem =>
      absurd (le_csSup hAbdd hmem) (by rw [← hc₀]; linarith)
    have hdmem : x - ((c₀ + ε : ℝ) : ℂ) • p ∈ cornerNonUnitalStarSubalgebra N hp :=
      sub_mem ⟨hxN, hpx, hxp⟩ (SMulMemClass.smul_mem _ hpmem)
    rcases nonneg_or_nonpos_of_forall_subprojection hp hp0 hmin (hsa_c _) hdmem with h | h
    · exact absurd h hnotA
    · exact h
  -- `{c | x - c • p ≤ 0}` is pointwise-characterised, hence closed; it contains `(c₀, ∞)`,
  -- hence its closure point `c₀`
  have hnegpos_iff : ∀ c : ℝ, (x - (c : ℂ) • p ≤ 0) ↔
      ∀ v, RCLike.re (inner ℂ (x v) v) ≤ c * ‖p v‖ ^ 2 := by
    intro c
    have hsa' : IsSelfAdjoint ((c : ℂ) • p - x) := by
      rw [IsSelfAdjoint, star_sub, star_smul, hxsa.star_eq, hp.isSelfAdjoint.star_eq,
        Complex.star_def, Complex.conj_ofReal]
    rw [ContinuousLinearMap.le_def, zero_sub, neg_sub,
      ← ContinuousLinearMap.nonneg_iff_isPositive, hpos_iff _ hsa']
    have hstep : ∀ v, RCLike.re (inner ℂ (((c : ℂ) • p - x) v) v)
        = c * ‖p v‖ ^ 2 - RCLike.re (inner ℂ (x v) v) := by
      intro v
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_sub_left,
        inner_smul_left, Complex.conj_ofReal, map_sub,
        show RCLike.re ((c : ℂ) * inner ℂ (p v) v) = c * RCLike.re (inner ℂ (p v) v) from
          RCLike.re_ofReal_mul c _, hpvv]
    constructor
    · intro h v
      have := h v
      rw [hstep, sub_nonneg] at this
      exact this
    · intro h v
      rw [hstep, sub_nonneg]
      exact h v
  have hBclosed : IsClosed {c : ℝ | x - (c : ℂ) • p ≤ 0} := by
    have hBeq : {c : ℝ | x - (c : ℂ) • p ≤ 0}
        = ⋂ v : H, {c : ℝ | RCLike.re (inner ℂ (x v) v) ≤ c * ‖p v‖ ^ 2} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iInter, hnegpos_iff c]
    rw [hBeq]
    exact isClosed_iInter fun v =>
      isClosed_le continuous_const (continuous_id.mul continuous_const)
  have hIoi : Set.Ioi c₀ ⊆ {c : ℝ | x - (c : ℂ) • p ≤ 0} := by
    intro c hc
    have h := hupper (c - c₀) (sub_pos.mpr hc)
    rw [show c₀ + (c - c₀) = c by ring] at h
    exact h
  have hc₀B : x - (c₀ : ℂ) • p ≤ 0 := by
    have h1 : Set.Ici c₀ ⊆ {c : ℝ | x - (c : ℂ) • p ≤ 0} := by
      rw [← closure_Ioi]
      exact closure_minimal hIoi hBclosed
    exact h1 Set.self_mem_Ici
  have hge : (0 : H →L[ℂ] H) ≤ x - (c₀ : ℂ) • p := hc₀A
  exact sub_eq_zero.mp (le_antisymm hc₀B hge)

/-- **Order-minimality implies corner triviality**: a nonzero star projection `p ∈ N` with no
proper nonzero subprojection in `N` is a minimal projection, i.e. `p N p = ℂ p`. Self-adjoint
corner elements are real multiples of `p` by the cut lemma
(`exists_real_smul_eq_of_forall_subprojection`); a general corner element decomposes into real
and imaginary self-adjoint parts. -/
theorem isMinimalProjection_of_forall_subprojection {N : VonNeumannAlgebra H}
    {p : H →L[ℂ] H} (hp : IsStarProjection p) (hpN : p ∈ N) (hp0 : p ≠ 0)
    (hmin : ∀ q, IsStarProjection q → q ∈ N → p * q = q → q = 0 ∨ q = p) :
    IsMinimalProjection N p := by
  refine ⟨hp, hpN, hp0, fun a haN => ?_⟩
  have hymem : p * a * p ∈ cornerNonUnitalStarSubalgebra N hp := by
    refine ⟨mul_mem (mul_mem hpN haN) hpN, ?_, ?_⟩
    · calc p * (p * a * p) = (p * p) * a * p := by simp only [mul_assoc]
        _ = p * a * p := by rw [hp.isIdempotentElem]
    · rw [mul_assoc (p * a) p p, hp.isIdempotentElem]
  set s : H →L[ℂ] H := star (p * a * p) with hs
  have hsmem : s ∈ cornerNonUnitalStarSubalgebra N hp := star_mem hymem
  have hy₁mem : (2⁻¹ : ℂ) • (p * a * p + s) ∈ cornerNonUnitalStarSubalgebra N hp :=
    SMulMemClass.smul_mem _ (add_mem hymem hsmem)
  have hy₂mem : (-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)
      ∈ cornerNonUnitalStarSubalgebra N hp :=
    SMulMemClass.smul_mem _ (sub_mem hymem hsmem)
  have hy₁sa : IsSelfAdjoint ((2⁻¹ : ℂ) • (p * a * p + s)) := by
    rw [IsSelfAdjoint, star_smul, star_add, hs, star_star,
      show star (2⁻¹ : ℂ) = (2⁻¹ : ℂ) by simp, add_comm]
  have hy₂sa : IsSelfAdjoint ((-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)) := by
    rw [IsSelfAdjoint, star_smul, star_sub, hs, star_star,
      show star (-(Complex.I) * 2⁻¹ : ℂ) = (Complex.I * 2⁻¹ : ℂ) by simp,
      ← neg_sub (p * a * p) (star (p * a * p)), smul_neg, neg_mul, neg_smul]
  obtain ⟨c₁, hc₁⟩ := exists_real_smul_eq_of_forall_subprojection hp hpN hp0 hmin hy₁sa hy₁mem
  obtain ⟨c₂, hc₂⟩ := exists_real_smul_eq_of_forall_subprojection hp hpN hp0 hmin hy₂sa hy₂mem
  refine ⟨(c₁ : ℂ) + Complex.I * (c₂ : ℂ), ?_⟩
  have hrec : (2⁻¹ : ℂ) • (p * a * p + s)
      + Complex.I • ((-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)) = p * a * p := by
    rw [smul_smul, show Complex.I * (-(Complex.I) * 2⁻¹) = (2⁻¹ : ℂ) by
        rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul],
      smul_add, smul_sub]
    calc (2⁻¹ : ℂ) • (p * a * p) + (2⁻¹ : ℂ) • s
          + ((2⁻¹ : ℂ) • (p * a * p) - (2⁻¹ : ℂ) • s)
        = (2⁻¹ : ℂ) • (p * a * p) + (2⁻¹ : ℂ) • (p * a * p) := by abel
      _ = ((2⁻¹ : ℂ) + 2⁻¹) • (p * a * p) := (add_smul _ _ _).symm
      _ = p * a * p := by norm_num
  calc p * a * p
      = (2⁻¹ : ℂ) • (p * a * p + s)
        + Complex.I • ((-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)) := hrec.symm
    _ = (c₁ : ℂ) • p + Complex.I • ((c₂ : ℂ) • p) := by rw [hc₁, hc₂]
    _ = ((c₁ : ℂ) + Complex.I * (c₂ : ℂ)) • p := by rw [smul_smul, ← add_smul]

/-- **In a factor, a nonzero abelian projection is minimal**: it is order-minimal
(`subprojection_eq_of_isAbelianProjection`), and order-minimality forces the trivial corner
(`isMinimalProjection_of_forall_subprojection`). -/
theorem IsFactor.isMinimalProjection_of_isAbelianProjection [Nontrivial H]
    {N : VonNeumannAlgebra H} (hN : IsFactor N) {p : H →L[ℂ] H}
    (hp : IsAbelianProjection N p) (hp0 : p ≠ 0) : IsMinimalProjection N p :=
  isMinimalProjection_of_forall_subprojection hp.1 hp.2.1 hp0 fun _ hq hqN hsub =>
    hN.subprojection_eq_of_isAbelianProjection hp hq hqN hsub

/-- **The abelian-projection characterisation of type I coincides with the minimal-projection one
on factors**: a factor is type I iff it has a minimal projection. Nontriviality of `H` is
essential in both directions (on a subsingleton `H` the type I condition is vacuous while no
nonzero projection exists). -/
theorem IsFactor.isTypeI_iff_exists_isMinimalProjection [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) : IsTypeI N ↔ ∃ e : H →L[ℂ] H, IsMinimalProjection N e := by
  constructor
  · intro h
    have hone : (1 : H →L[ℂ] H) ≠ 0 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : H)
      intro h1
      apply hv
      have h2 := congrArg (fun T : H →L[ℂ] H => T v) h1
      simpa using h2
    obtain ⟨q, hab, hq0, -⟩ := h 1 (isCentralProjection_one N) hone
    exact ⟨q, hN.isMinimalProjection_of_isAbelianProjection hab hq0⟩
  · exact hN.isTypeI_of_exists_isMinimalProjection

/-- The factor-specialised definition `IsTypeIFactor` agrees with the conjunction of the general
abelian-projection type I property and factor-ness. -/
theorem isTypeIFactor_iff_isFactor_and_isTypeI [Nontrivial H] {N : VonNeumannAlgebra H} :
    IsTypeIFactor N ↔ IsFactor N ∧ IsTypeI N := by
  constructor
  · rintro ⟨hf, he⟩
    exact ⟨hf, hf.isTypeI_of_exists_isMinimalProjection he⟩
  · rintro ⟨hf, ht⟩
    exact ⟨hf, hf.isTypeI_iff_exists_isMinimalProjection.mp ht⟩

end VonNeumannAlgebra
