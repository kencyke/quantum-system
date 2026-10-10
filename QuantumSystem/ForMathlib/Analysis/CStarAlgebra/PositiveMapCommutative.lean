/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Topology.PartitionOfUnity

/-!
# Positive maps on commutative unital C⋆-algebras are completely positive

**Stinespring's theorem** (Stinespring 1955, Theorem 4; Paulsen, Theorem 3.11): a positive linear
map `φ` from a commutative unital C⋆-algebra into any C⋆-algebra is completely positive.

By Gelfand duality (`gelfandStarTransform`) the domain may be taken to be `C(X, ℂ)` for a compact
Hausdorff space `X`. Let `M` be a nonnegative `n × n` matrix over `C(X, ℂ)` and `ε > 0`. Cover `X`
by finitely many open sets `Uₗ ∋ xₗ` on which every entry of `M` stays `ε`-close to its value at
`xₗ`, and take a partition of unity `(gₗ)` subordinate to the cover. Then `Σₗ gₗ • M(xₗ)` is
entrywise `ε`-close to `M`, and its image under `φ` is `Σₗ M(xₗ) ⊗ φ(gₗ)`: here `M(xₗ)` is a
nonnegative scalar matrix (evaluation at a point is a ⋆-homomorphism, hence completely positive)
and `φ(gₗ) ≥ 0`, and such a tensor is nonnegative (`CStarMatrix.map_smul_const_nonneg`). Since
`φ` is continuous and the nonnegative cone is closed, `φ(M) ≥ 0`.

## Main results

* `CStarMatrix.map_smul_const_nonneg` — for a nonnegative scalar matrix `S` and `p ≥ 0`, the
  matrix `(S i j • p)ᵢⱼ` is nonnegative.
* `CompletelyPositiveMapClass.of_orderHomClass_of_commCStarAlgebra` — **Stinespring**: a positive
  linear map on a commutative unital C⋆-algebra is completely positive.

## Implementation notes

`CompletelyPositiveMapClass.of_orderHomClass_of_commCStarAlgebra` is a theorem rather than an
instance: Mathlib's instance `CompletelyPositiveMapClass F A₁ A₂ → OrderHomClass F A₁ A₂` would
otherwise form an instance cycle.

## References

* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216, Theorem 4.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Cambridge Stud. Adv. Math. 78
  (2002), Theorem 3.11.
-/

@[expose] public section

open scoped ComplexOrder
open Filter Topology

namespace CStarMatrix

variable {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A nonnegative scalar matrix `S` tensored with a nonnegative element `p` of a C⋆-algebra,
`(S i j • p)ᵢⱼ`, is nonnegative. The nonnegative scalar matrices are the sums of the `C⋆ C`
(`StarOrderedRing.le_iff`), and `((C⋆ C) i j • p)ᵢⱼ = D⋆ D` for `D k j = C k j • √p`. -/
lemma map_smul_const_nonneg {S : CStarMatrix n n ℂ} (hS : 0 ≤ S) {p : A} (hp : 0 ≤ p) :
    0 ≤ S.map (· • p) := by
  obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 S).mp hS
  clear hS
  rw [zero_add]
  induction hP using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨C, rfl⟩ := h
    let D : CStarMatrix n n A := ofMatrix fun k j => C k j • CFC.sqrt p
    convert star_mul_self_nonneg D using 1
    refine ext fun i j => ?_
    simp only [map_apply, mul_apply, star_apply, D, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (star (C k i) * C k j) • p = star (C k i • CFC.sqrt p) * (C k j • CFC.sqrt p)
    rw [star_smul, smul_mul_smul_comm, (CFC.sqrt_nonneg p).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self p hp]
  | zero => exact le_of_eq (ext fun i j => (zero_smul ℂ p).symm)
  | add S T _ _ hS hT =>
    exact (add_nonneg hS hT).trans_eq (ext fun i j => (add_smul (S i j) (T i j) p).symm)

end CStarMatrix

namespace CompletelyPositiveMapClass

section ContinuousMap

variable {X F A : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [FunLike F C(X, ℂ) A]
  [LinearMapClass F ℂ C(X, ℂ) A] [OrderHomClass F C(X, ℂ) A]

/-- The approximation step of Stinespring's theorem: a nonnegative matrix `M` over `C(X, ℂ)` is
entrywise `ε`-close to a matrix `N = Σₗ gₗ • M(xₗ)` whose image under a positive map `φ` is
nonnegative. The `gₗ` form a partition of unity subordinate to a finite open cover by sets
`Uₗ ∋ xₗ` on which every entry of `M` stays `ε`-close to its value at `xₗ`. -/
private lemma exists_approx (φ : F) {n : Type*} [Fintype n] {M : CStarMatrix n n C(X, ℂ)}
    (hM : 0 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : CStarMatrix n n C(X, ℂ), (∀ i j, ‖N i j - M i j‖ ≤ ε) ∧ 0 ≤ N.map φ := by
  let U : X → Set X := fun y => {z | ∀ i j, ‖M i j z - M i j y‖ < ε}
  have hUo (y : X) : IsOpen (U y) := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((M i j).continuous.sub continuous_const).norm continuous_const
  have hUy (y : X) : y ∈ U y := fun i j => by simpa using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hUy y⟩)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun l : t => U l)
    (fun l => hUo l) fun y hy => by
      obtain ⟨l, hl, hyl⟩ := Set.mem_iUnion₂.1 (ht hy)
      exact Set.mem_iUnion.2 ⟨⟨l, hl⟩, hyl⟩
  let g : t → C(X, ℂ) := fun l =>
    ⟨fun z => (ρ l z : ℂ), Complex.continuous_ofReal.comp (ρ l).continuous⟩
  have hg (l : t) : 0 ≤ g l := ContinuousMap.le_def.2 fun z => by
    simpa [g] using ρ.nonneg l z
  let N : CStarMatrix n n C(X, ℂ) := CStarMatrix.ofMatrix fun i j => ∑ l : t, M i j l • g l
  refine ⟨N, fun i j => (ContinuousMap.norm_le _ hε.le).2 fun z => ?_, ?_⟩
  · have hsum : ∑ l, ρ l z = 1 := by
      simpa [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ z)
    have hNz : (N i j - M i j) z = ∑ l, (ρ l z : ℂ) * (M i j l - M i j z) := by
      have : M i j z = ∑ l, (ρ l z : ℂ) * M i j z := by
        rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_mul]
      change (∑ l : t, M i j l • g l) z - M i j z = _
      rw [ContinuousMap.sum_apply]
      simp only [mul_sub, Finset.sum_sub_distrib, ← this]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [g, mul_comm]
    rw [hNz]
    calc ‖∑ l, (ρ l z : ℂ) * (M i j l - M i j z)‖
        ≤ ∑ l, ‖(ρ l z : ℂ) * (M i j l - M i j z)‖ := norm_sum_le _ _
      _ ≤ ∑ l, ρ l z * ε := Finset.sum_le_sum fun l _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ρ.nonneg l z)]
          by_cases h : ρ l z = 0
          · simp [h]
          · have hz : z ∈ U l := hρ l (subset_tsupport _ h)
            gcongr
            · exact ρ.nonneg l z
            · rw [norm_sub_rev]
              exact (hz i j).le
      _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]
  · have hev (l : t) : 0 ≤ M.map fun f => f l :=
      (toCompletelyPositiveLinearMap
        (ContinuousMap.evalStarAlgHom ℂ ℂ (l : X))).map_cstarMatrix_nonneg M hM
    have hN : N.map φ = ∑ l : t, (M.map fun f => f (l : X)).map (· • φ (g l)) := by
      refine CStarMatrix.ext fun i j => ?_
      refine Eq.trans ?_ (map_sum (AddMonoidHom.mk' (fun M : CStarMatrix n n A => M i j)
        (fun _ _ => rfl)) _ _).symm
      change φ (∑ l : t, M i j l • g l) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => map_smul φ _ _
    rw [hN]
    exact Finset.sum_nonneg fun l _ =>
      CStarMatrix.map_smul_const_nonneg (hev l) (map_nonneg φ (hg l))

/-- **Stinespring's theorem** for `C(X, ℂ)`: a positive linear map from `C(X, ℂ)`, `X` compact
Hausdorff, preserves the nonnegativity of matrices. The approximants of
`CompletelyPositiveMapClass.exists_approx` for `ε = 1 / (k + 1)` converge entrywise to `M`; `φ` is
continuous, so their images converge to `φ(M)`, and the nonnegative cone is closed. -/
private lemma map_cstarMatrix_nonneg_of_continuousMap (φ : F) {n : Type*} [Fintype n]
    {M : CStarMatrix n n C(X, ℂ)} (hM : 0 ≤ M) : 0 ≤ M.map φ := by
  choose N hN hNφ using fun k : ℕ => exists_approx φ hM (Nat.one_div_pos_of_nat (n := k))
  have hlim : Tendsto N atTop (𝓝 M) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hN k i j)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : Continuous fun N : CStarMatrix n n C(X, ℂ) => N.map φ :=
    continuous_pi fun i => continuous_pi fun j =>
      (map_continuous φ).comp ((continuous_apply j).comp (continuous_apply i))
  exact CStarAlgebra.isClosed_nonneg.mem_of_tendsto ((hcont.tendsto M).comp hlim)
    (Eventually.of_forall hNφ)

end ContinuousMap

/-- **Stinespring's theorem** (Stinespring 1955, Theorem 4; Paulsen, Theorem 3.11): a positive
linear map from a commutative unital C⋆-algebra into any C⋆-algebra is completely positive.
Gelfand duality identifies `A₁` with `C(X, ℂ)` for the compact Hausdorff character space `X`
(`gelfandStarTransform`); ⋆-isomorphisms are completely positive, and a positive map on `C(X, ℂ)`
is completely positive by uniform approximation with partitions of unity. -/
theorem of_orderHomClass_of_commCStarAlgebra {F A₁ A₂ : Type*} [CommCStarAlgebra A₁]
    [PartialOrder A₁] [StarOrderedRing A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₂]
    [StarOrderedRing A₂]
    [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [OrderHomClass F A₁ A₂] :
    CompletelyPositiveMapClass F A₁ A₂ where
  map_cstarMatrix_nonneg' φ k M hM := by
    let e := gelfandStarTransform A₁
    let ψ : C(WeakDual.characterSpace ℂ A₁, ℂ) →ₚ[ℂ] A₂ :=
      (PositiveLinearMap.ofClass φ).comp (PositiveLinearMap.ofClass e.symm)
    have h := map_cstarMatrix_nonneg_of_continuousMap ψ
      (CompletelyPositiveMapClass.map_cstarMatrix_nonneg' e k M hM)
    convert h using 1
    refine CStarMatrix.ext fun i j => ?_
    change φ (M i j) = φ (e.symm (e (M i j)))
    rw [StarAlgEquiv.symm_apply_apply]

end CompletelyPositiveMapClass
