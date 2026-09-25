/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Basic
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProductCompletion
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Spatial decomposition of a type I factor

This file assembles the proof ingredients of the type I factor structure theorem
`N ≅ B(ℓ²(F)) ⊗̄ 1` up to the spatial decomposition `H ≅ ℓ²(F) ⊗̂ (eH)`:

1. **Covering family.** For a factor `N` with minimal projection `e`, Zorn's lemma and the
   comparison theorem `IsMinimalProjection.mvNSub_of_isFactor` produce a family of mutually
   orthogonal projections, each Murray–von Neumann equivalent to `e`, whose ranges span densely —
   the projection-theoretic backbone `Σ eᵢ = 1` of the structure theorem.
2. **Matrix units.** From the equivalence partial isometries `v_p : e ≅ p` the system of **matrix
   units** `e_{pq} = v_p v_q⋆` is built, with the defining matrix-unit relations, and the
   **multiplicity-one** property: for every `a ∈ N` the matrix entry `v_p⋆ a v_q` is a *scalar*
   multiple of `e` (a direct consequence of the corner condition `e N e = ℂ e` defining a minimal
   projection). Together these say that `N` is, algebraically, the `*`-algebra of `F × F` matrices
   over `ℂ` — the algebraic heart of the structure theorem.
3. **Spatial ℓ² decomposition.** A partial isometry `v` with source projection `p = v⋆v` and range
   projection `q = vv⋆` restricts to a linear isometric equivalence between the closed subspaces
   `range p` and `range q`. These isometries identify every summand `range eᵢ` with the
   multiplicity space `range e`, giving `H ≅ ℓ²(F; eH)` and, through the tensor bridge
   `HilbertTensor.lpTensorEquiv`, the literal tensor form `H ≅ ℓ²(F) ⊗̂ (eH)`.

The remaining steps — the strong-operator reconstruction `a = Σ_{pq} c_{pq}(a) e_{pq}` (in its
double-commutant form: the matrix units generate `N`) and the identification of `N` with
`B(ℓ²(F)) ⊗̄ 1` under the spatial isomorphism — are carried out in
`QuantumSystem.Algebra.VonNeumannAlgebra.TypeI.StructureTheorem`.

## Conventions

The dense span of the ranges is expressed as
`(Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤`, i.e. the closed linear
span of the union of the ranges is the whole space; this is the operator-friendly form of
`⨆ᵢ ranges = 1` and matches the central-support construction `IsFactor.exists_mul_ne`.

`OrthEquivFam` only records that each member is a nonzero star projection in `N` equivalent to
`e`; when `e` is minimal the members are minimal as a consequence
(`OrthEquivFam.isMinimalProjection_of_mem`).

## Main definitions

* `VonNeumannAlgebra.OrthEquivFam N e F` — `F` is a set of pairwise-orthogonal nonzero projections
  in `N`, each Murray–von Neumann equivalent to `e`.
* `VonNeumannAlgebra.OrthEquivFam.pisom` — a choice of equivalence partial isometry `v_p : e ≅ p`.
* `VonNeumannAlgebra.OrthEquivFam.matrixUnit` — the matrix unit `e_{pq} = v_p v_q⋆`.
* `VonNeumannAlgebra.OrthEquivFam.multiplicityEquiv` — the spatial isomorphism `H ≅ ℓ²(F; eH)`.

## Main results

* `VonNeumannAlgebra.IsFactor.exists_orthEquivFam_top` — in a factor, there is a maximal
  orthogonal family of `e`-equivalent projections whose ranges have dense span.
* `VonNeumannAlgebra.OrthEquivFam.matrixUnit_mul_of_eq` / `matrixUnit_mul_of_ne` — the matrix-unit
  multiplication law `e_{pq} e_{rs} = δ_{qr} e_{ps}`.
* `VonNeumannAlgebra.OrthEquivFam.exists_matrixEntry` — multiplicity one:
  `∃ c, v_p⋆ a v_q = c • e` for `a ∈ N`.
* `VonNeumannAlgebra.IsFactor.exists_lp_decomposition` — the `ℓ²`-sum form `H ≅ ℓ²(F; eH)` of
  the spatial decomposition of a type I factor.
* `VonNeumannAlgebra.IsFactor.exists_tmul_decomposition` — the literal tensor form
  `H ≅ ℓ²(F) ⊗̂ (eH)`, obtained by composing with the tensor bridge
  `HilbertTensor.lpTensorEquiv`.

## Notation

`⊗̄` in the prose above is documentation shorthand for the von Neumann (spatial) tensor product of
algebras; that convention is stated in full in `QuantumSystem.Algebra.VonNeumannAlgebra.TensorFactor`,
where the algebras it names (`HilbertTensor.vnTensorLeft` / `vnTensorRight`) are defined.
-/

@[expose] public section

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Covering families of `e`-equivalent projections -/

namespace VonNeumannAlgebra

/-- A family of pairwise-orthogonal nonzero projections in `N`, each Murray–von Neumann equivalent
to `e`. -/
def OrthEquivFam (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) (F : Set (H →L[ℂ] H)) : Prop :=
  (∀ p ∈ F, IsStarProjection p ∧ p ∈ N ∧ p ≠ 0 ∧ e ∼[N] p) ∧
    F.Pairwise (fun p q => p * q = 0)

/-- When `e` is minimal, every member of an `OrthEquivFam` for `e` is itself a minimal
projection, since minimality transports along `∼[N]` (`IsMinimalProjection.of_mvNEquiv`). -/
lemma OrthEquivFam.isMinimalProjection_of_mem {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F) (he : IsMinimalProjection N e)
    {p : H →L[ℂ] H} (hp : p ∈ F) : IsMinimalProjection N p :=
  he.of_mvNEquiv (hF.1 p hp).2.2.2

/-- By Zorn's lemma, there is a maximal orthogonal family of `e`-equivalent projections. -/
lemma exists_maximal_orthEquivFam (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) :
    ∃ F, OrthEquivFam N e F ∧ ∀ G, OrthEquivFam N e G → F ⊆ G → G ⊆ F := by
  obtain ⟨F, hFmax⟩ := zorn_subset {F | OrthEquivFam N e F} (by
    intro c hcsub hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro p ⟨s, hsc, hps⟩; exact (hcsub hsc).1 p hps
    · rintro p ⟨s, hsc, hps⟩ q ⟨t, htc, hqt⟩ hpq
      rcases hchain.total hsc htc with h | h
      · exact (hcsub htc).2 (h hps) hqt hpq
      · exact (hcsub hsc).2 hps (h hqt) hpq)
  exact ⟨F, hFmax.1, fun G hG hFG => hFmax.2 hG hFG⟩

/-- The orthogonal projection onto the closed span of the ranges of an `OrthEquivFam` lies in `N`,
because that subspace is invariant under the commutant `N'`: for `y ∈ N'` and `f ∈ F ⊆ N`,
`y (f x) = (y f) x = (f y) x = f (y x)` lies in the range of `f`. -/
lemma OrthEquivFam.starProjection_mem {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F) :
    (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure.starProjection ∈ N := by
  set S : Set H := {y | ∃ f ∈ F, ∃ x, f x = y} with hS
  set M : Submodule ℂ H := (Submodule.span ℂ S).topologicalClosure with hM
  set p : H →L[ℂ] H := M.starProjection with hp
  have hpproj : IsStarProjection p := isStarProjection_starProjection
  rw [IsStarProjection.mem_iff hpproj N]
  intro y hyN'
  rw [hp, Submodule.range_starProjection]
  have hcl : IsClosed ((M.comap (y : H →ₗ[ℂ] H)) : Set H) := by
    rw [Submodule.comap_coe]
    exact ((Submodule.span ℂ S).isClosed_topologicalClosure).preimage y.continuous
  have hle : M ≤ M.comap (y : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal (Submodule.span ℂ S) ?_ hcl
    rw [Submodule.span_le]
    rintro s ⟨f, hf, x, rfl⟩
    simp only [Submodule.comap_coe, Set.mem_preimage, SetLike.mem_coe, ContinuousLinearMap.coe_coe]
    have hfy : f * y = y * f := mem_commutant_iff.mp hyN' f (hF.1 f hf).2.1
    rw [show y (f x) = (y * f) x from rfl, ← hfy]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, y x, rfl⟩)
  exact hle

/-- **Covering family of minimal projections (factor case).** In a factor, there is a family `F`
of pairwise-orthogonal nonzero projections in `N`, each equivalent to the minimal projection `e`,
whose ranges span densely: the closed linear span of the union of their ranges is `⊤`. This is the
`Σ eᵢ = 1` input of the type I structure theorem.

The proof takes a *maximal* such family `F` (Zorn) and lets `p` be the orthogonal projection onto
the closed span `M` of the ranges; `p ∈ N`. If `M ≠ ⊤` then `r = 1 - p` is a nonzero projection in
`N`, so by the comparison theorem some nonzero `q' ≼ r` is equivalent to `e`; `q'` is orthogonal to
every `f ∈ F`, contradicting maximality. -/
theorem IsFactor.exists_orthEquivFam_top {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e) :
    ∃ F : Set (H →L[ℂ] H), OrthEquivFam N e F ∧
      (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤ := by
  have : Nontrivial H := he.nontrivial
  obtain ⟨F, hF, hFmax⟩ := exists_maximal_orthEquivFam N e
  refine ⟨F, hF, ?_⟩
  set S : Set H := {y | ∃ f ∈ F, ∃ x, f x = y} with hS
  set M : Submodule ℂ H := (Submodule.span ℂ S).topologicalClosure with hM
  set p : H →L[ℂ] H := M.starProjection with hp
  have hpproj : IsStarProjection p := isStarProjection_starProjection
  have hpN : p ∈ N := hF.starProjection_mem
  have hpf : ∀ f ∈ F, p * f = f := by
    intro f hf
    ext x
    simp only [mul_apply_eq_comp, hp]
    rw [Submodule.starProjection_eq_self_iff]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, x, rfl⟩)
  by_contra hMtop
  set r : H →L[ℂ] H := 1 - p with hr
  have hrproj : IsStarProjection r := by
    refine ⟨?_, ?_⟩
    · change (1 - p) * (1 - p) = 1 - p
      rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, mul_one, hpproj.isIdempotentElem,
        sub_self, sub_zero]
    · change star (1 - p) = 1 - p
      rw [star_sub, star_one, hpproj.isSelfAdjoint.star_eq]
  have hrN : r ∈ N := by rw [hr]; exact sub_mem (one_mem _) hpN
  have hr0 : r ≠ 0 := by
    intro h
    apply hMtop
    have hp1 : p = 1 := by rw [hr, sub_eq_zero] at h; exact h.symm
    have hMrange : M = p.range := (Submodule.range_starProjection M).symm
    rw [hMrange, hp1]
    exact Submodule.eq_top_iff'.2 fun y => ⟨y, rfl⟩
  obtain ⟨q', hq'N, hrq', heq'⟩ := he.mvNSub_of_isFactor hN hrproj hrN hr0
  have hq'proj : IsStarProjection q' := heq'.isStarProjection_right
  have hq'0 : q' ≠ 0 := heq'.ne_zero he.2.2.1
  have hpq' : p * q' = 0 := by
    have h := hrq'
    rw [hr, sub_mul, one_mul, sub_eq_self] at h
    exact h
  have horth : ∀ f ∈ F, q' * f = 0 ∧ f * q' = 0 := by
    intro f hf
    have hq'p : q' * p = 0 := by
      have h := congrArg star hpq'
      rwa [star_mul, hq'proj.isSelfAdjoint.star_eq, hpproj.isSelfAdjoint.star_eq, star_zero] at h
    have h1 : q' * f = 0 := by
      calc q' * f = q' * (p * f) := by rw [hpf f hf]
        _ = (q' * p) * f := by rw [mul_assoc]
        _ = 0 := by rw [hq'p, zero_mul]
    refine ⟨h1, ?_⟩
    have h := congrArg star h1
    rwa [star_mul, (hF.1 f hf).1.isSelfAdjoint.star_eq, hq'proj.isSelfAdjoint.star_eq,
      star_zero] at h
  have hq'notF : q' ∉ F := fun hq'F =>
    hq'0 (by have := (horth q' hq'F).1; rwa [hq'proj.isIdempotentElem] at this)
  have hbigger : OrthEquivFam N e (insert q' F) := by
    refine ⟨?_, ?_⟩
    · rintro x (rfl | hx)
      · exact ⟨hq'proj, hq'N, hq'0, heq'⟩
      · exact hF.1 x hx
    · rintro x (rfl | hx) z (rfl | hz) hxz
      · exact absurd rfl hxz
      · exact (horth z hz).1
      · exact (horth x hx).2
      · exact hF.2 hx hz hxz
  have hsub := hFmax (insert q' F) hbigger (Set.subset_insert _ _)
  exact hq'notF (hsub (Set.mem_insert _ _))

/-! ### Matrix units and the multiplicity-one property -/

variable {N : VonNeumannAlgebra H} {e : H →L[ℂ] H} {F : Set (H →L[ℂ] H)}

/-- A choice of partial isometry `v_p` implementing the Murray–von Neumann equivalence `e ∼[N] p`,
oriented with source projection `v_p⋆ v_p = e` (`pisom_source`) and range projection
`v_p v_p⋆ = p` (`pisom_range`). -/
noncomputable def OrthEquivFam.pisom (hF : OrthEquivFam N e F) (p : F) : H →L[ℂ] H :=
  (hF.1 p.1 p.2).2.2.2.choose

/-- The chosen equivalence partial isometry `v_p` lies in `N`. -/
lemma OrthEquivFam.pisom_mem (hF : OrthEquivFam N e F) (p : F) : hF.pisom p ∈ N :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.1

/-- The chosen `v_p` is a partial isometry. -/
lemma OrthEquivFam.pisom_isPI (hF : OrthEquivFam N e F) (p : F) :
    IsPartialIsometry (hF.pisom p) :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.2.1

/-- The source projection of `v_p` is `e`: `v_p⋆ v_p = e`. -/
lemma OrthEquivFam.pisom_source (hF : OrthEquivFam N e F) (p : F) :
    star (hF.pisom p) * hF.pisom p = e :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.2.2.1

/-- The range projection of `v_p` is `p`: `v_p v_p⋆ = p`. -/
lemma OrthEquivFam.pisom_range (hF : OrthEquivFam N e F) (p : F) :
    hF.pisom p * star (hF.pisom p) = (p : H →L[ℂ] H) :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.2.2.2

/-- `v_p e = v_p`: the source projection acts as a right unit on `v_p`. -/
lemma OrthEquivFam.pisom_mul_source (hF : OrthEquivFam N e F) (p : F) :
    hF.pisom p * e = hF.pisom p := by
  have h : hF.pisom p * (star (hF.pisom p) * hF.pisom p) = hF.pisom p := by
    rw [← mul_assoc]; exact hF.pisom_isPI p
  rwa [hF.pisom_source p] at h

/-- `e v_p⋆ = v_p⋆`: the source projection acts as a left unit on `v_p⋆`. -/
lemma OrthEquivFam.e_mul_star_pisom (hF : OrthEquivFam N e F) (p : F) :
    e * star (hF.pisom p) = star (hF.pisom p) := by
  have h : star (hF.pisom p) * hF.pisom p * star (hF.pisom p) = star (hF.pisom p) := by
    have h' : star (hF.pisom p) * star (star (hF.pisom p)) * star (hF.pisom p)
        = star (hF.pisom p) := IsPartialIsometry.star (hF.pisom_isPI p)
    rwa [star_star] at h'
  rwa [hF.pisom_source p] at h

/-- For distinct family members the partial isometries are orthogonal: `v_q⋆ v_r = 0`. -/
lemma OrthEquivFam.star_pisom_mul_pisom_of_ne (hF : OrthEquivFam N e F) {q r : F}
    (hqr : q ≠ r) : star (hF.pisom q) * hF.pisom r = 0 := by
  have hq : (q : H →L[ℂ] H) * hF.pisom q = hF.pisom q := by
    have h : hF.pisom q * star (hF.pisom q) * hF.pisom q = hF.pisom q := hF.pisom_isPI q
    rwa [hF.pisom_range q] at h
  have hr : (r : H →L[ℂ] H) * hF.pisom r = hF.pisom r := by
    have h : hF.pisom r * star (hF.pisom r) * hF.pisom r = hF.pisom r := hF.pisom_isPI r
    rwa [hF.pisom_range r] at h
  have hsq : star (hF.pisom q) * (q : H →L[ℂ] H) = star (hF.pisom q) := by
    have := congrArg star hq
    rwa [star_mul, (hF.1 q.1 q.2).1.isSelfAdjoint.star_eq] at this
  have h0 : (q : H →L[ℂ] H) * r = 0 := hF.2 q.2 r.2 (fun h => hqr (Subtype.ext h))
  calc star (hF.pisom q) * hF.pisom r
      = (star (hF.pisom q) * (q : H →L[ℂ] H)) * ((r : H →L[ℂ] H) * hF.pisom r) := by
        rw [hsq, hr]
    _ = star (hF.pisom q) * ((q : H →L[ℂ] H) * r) * hF.pisom r := by simp only [mul_assoc]
    _ = 0 := by rw [h0, mul_zero, zero_mul]

/-- The **matrix unit** `e_{pq} = v_p v_q⋆`. -/
noncomputable def OrthEquivFam.matrixUnit (hF : OrthEquivFam N e F) (p q : F) : H →L[ℂ] H :=
  hF.pisom p * star (hF.pisom q)

/-- Definitional unfolding of the matrix unit: `e_{pq} = v_p v_q⋆`. -/
lemma OrthEquivFam.matrixUnit_def (hF : OrthEquivFam N e F) (p q : F) :
    hF.matrixUnit p q = hF.pisom p * star (hF.pisom q) := rfl

/-- Matrix units lie in `N`. -/
lemma OrthEquivFam.matrixUnit_mem (hF : OrthEquivFam N e F) (p q : F) :
    hF.matrixUnit p q ∈ N :=
  mul_mem (hF.pisom_mem p) (star_mem (hF.pisom_mem q))

/-- Matrix-unit multiplication law `e_{pq} e_{rs} = δ_{qr} e_{ps}`, diagonal case `q = r`:
`e_{pq} e_{qs} = e_{ps}`. -/
theorem OrthEquivFam.matrixUnit_mul_of_eq (hF : OrthEquivFam N e F) (p q s : F) :
    hF.matrixUnit p q * hF.matrixUnit q s = hF.matrixUnit p s := by
  rw [matrixUnit_def, matrixUnit_def, matrixUnit_def]
  calc hF.pisom p * star (hF.pisom q) * (hF.pisom q * star (hF.pisom s))
      = hF.pisom p * (star (hF.pisom q) * hF.pisom q) * star (hF.pisom s) := by
        simp only [mul_assoc]
    _ = hF.pisom p * e * star (hF.pisom s) := by rw [hF.pisom_source q]
    _ = hF.pisom p * star (hF.pisom s) := by rw [hF.pisom_mul_source p]

/-- Matrix-unit multiplication law `e_{pq} e_{rs} = δ_{qr} e_{ps}`, off-diagonal case `q ≠ r`:
`e_{pq} e_{rs} = 0`. -/
theorem OrthEquivFam.matrixUnit_mul_of_ne (hF : OrthEquivFam N e F) (p s : F) {q r : F}
    (hqr : q ≠ r) : hF.matrixUnit p q * hF.matrixUnit r s = 0 := by
  rw [matrixUnit_def, matrixUnit_def]
  calc hF.pisom p * star (hF.pisom q) * (hF.pisom r * star (hF.pisom s))
      = hF.pisom p * (star (hF.pisom q) * hF.pisom r) * star (hF.pisom s) := by
        simp only [mul_assoc]
    _ = 0 := by rw [hF.star_pisom_mul_pisom_of_ne hqr, mul_zero, zero_mul]

/-- **Multiplicity one.** For a minimal projection `e` and any `a ∈ N`, the matrix entry
`v_p⋆ a v_q` is a scalar multiple of `e`. This is the corner condition `e N e = ℂ e` transported
along the equivalences, and is the algebraic content of `N ≅ B(ℓ²(F)) ⊗̄ 1`. -/
theorem OrthEquivFam.exists_matrixEntry (hF : OrthEquivFam N e F)
    (he : IsMinimalProjection N e) (p q : F) {a : H →L[ℂ] H} (ha : a ∈ N) :
    ∃ c : ℂ, star (hF.pisom p) * a * hF.pisom q = c • e := by
  have hbN : star (hF.pisom p) * a * hF.pisom q ∈ N :=
    mul_mem (mul_mem (star_mem (hF.pisom_mem p)) ha) (hF.pisom_mem q)
  obtain ⟨c, hc⟩ := he.2.2.2 _ hbN
  refine ⟨c, ?_⟩
  have key : e * (star (hF.pisom p) * a * hF.pisom q) * e
      = star (hF.pisom p) * a * hF.pisom q := by
    calc e * (star (hF.pisom p) * a * hF.pisom q) * e
        = (e * star (hF.pisom p)) * a * (hF.pisom q * e) := by simp only [mul_assoc]
      _ = star (hF.pisom p) * a * hF.pisom q := by
          rw [hF.e_mul_star_pisom p, hF.pisom_mul_source q]
  rw [← key, hc]

end VonNeumannAlgebra

/-! ### The spatial ℓ² decomposition

Built from the partial-isometry equivalences `IsPartialIsometry.sourceRangeEquiv`
(`QuantumSystem.ForMathlib.Algebra.Star.PartialIsometry`) and `lpCongr`
(`QuantumSystem.ForMathlib.Analysis.Normed.Lp.lpSpace`). -/

namespace VonNeumannAlgebra

/-- A covering orthogonal family of star projections (each in `OrthEquivFam`) realises `H` as the
internal Hilbert sum of the ranges. -/
lemma OrthEquivFam.isHilbertSum {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤) :
    IsHilbertSum ℂ (fun i : F => LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H))
      (fun i => (LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ) := by
  have : ∀ i : F, CompleteSpace (LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)) :=
    fun i => (hF.1 i.1 i.2).1.completeSpace_range
  refine IsHilbertSum.mkInternal _ ?_ ?_
  · rintro ⟨pi, hpi⟩ ⟨pj, hpj⟩ hij ⟨v, hv⟩ ⟨w, hw⟩
    have hne : pi ≠ pj := fun h => hij (Subtype.ext h)
    have h0 : (pi : H →L[ℂ] H) * pj = 0 := hF.2 hpi hpj hne
    have hvf : (pi : H →L[ℂ] H) v = v := (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap (hF.1 pi hpi).1.isIdempotentElem)).mp hv
    have hwf : (pj : H →L[ℂ] H) w = w := (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap (hF.1 pj hpj).1.isIdempotentElem)).mp hw
    have e1 : (inner ℂ v w : ℂ) = inner ℂ ((pi : H →L[ℂ] H) v) ((pj : H →L[ℂ] H) w) := by
      rw [hvf, hwf]
    change (inner ℂ v w : ℂ) = 0
    rw [e1, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      (hF.1 pi hpi).1.isSelfAdjoint.star_eq,
      show (pi : H →L[ℂ] H) ((pj : H →L[ℂ] H) w) = ((pi : H →L[ℂ] H) * pj) w from rfl, h0]
    simp
  · rw [← htop]
    refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
    rintro y ⟨f, hf, x, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨x, rfl⟩

/-- **Spatial Hilbert-sum isomorphism.** A covering orthogonal family of `e`-equivalent
projections gives a linear isometric equivalence of `H` with the `ℓ²` sum of the ranges. -/
noncomputable def OrthEquivFam.hilbertSumEquiv {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤) :
    H ≃ₗᵢ[ℂ] lp (fun i : F => LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)) 2 :=
  (hF.isHilbertSum htop).linearIsometryEquiv

/-- **Multiplicity decomposition of the Hilbert space.** A covering orthogonal family of
projections each Murray–von Neumann equivalent to `e` identifies `H` isometrically with
`ℓ²(F; eH)` — the `ℓ²` sum, indexed by `F`, of copies of the fibre `range e` (which is the
*multiplicity space* when `e` is minimal, as in `exists_lp_decomposition`; minimality is not
assumed in this lemma). The codomain is that `ℓ²` sum and nothing else: no tensor product occurs
here. Composing with the tensor bridge turns it into the literal `H ≅ ℓ²(F) ⊗̂ (eH)` of the type I
factor structure theorem — that is `OrthEquivFam.spatialEquiv`, and the existence statement is
`exists_tmul_decomposition`. The equivalence
is built from the Hilbert-sum decomposition `H ≅ ⊕ᵢ range eᵢ` and the partial-isometry-induced
isometries `range eᵢ ≅ range e`. -/
noncomputable def OrthEquivFam.multiplicityEquiv {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤) :
    H ≃ₗᵢ[ℂ] lp (fun _ : F => LinearMap.range (e : H →ₗ[ℂ] H)) 2 :=
  (hF.hilbertSumEquiv htop).trans (lpCongr (fun i =>
    (IsPartialIsometry.sourceRangeEquiv
      (hF.1 i.1 i.2).2.2.2.choose_spec.2.1
      (hF.1 i.1 i.2).2.2.2.choose_spec.2.2.1
      (hF.1 i.1 i.2).2.2.2.choose_spec.2.2.2).symm))

/-- The `i`-th Hilbert-sum coordinate of `y`, embedded back into `H`, is the orthogonal projection
`(↑i) y`. This identifies the abstract Hilbert-sum decomposition with the explicit family of range
projections. -/
lemma OrthEquivFam.coe_hilbertSumEquiv_apply {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    (y : H) (i : F) :
    ((hF.hilbertSumEquiv htop y i : LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)) : H)
      = (i : H →L[ℂ] H) y := by
  have hHS := hF.isHilbertSum htop
  have hdecomp : HasSum
      (fun j : F => (LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
        ((hHS.linearIsometryEquiv y) j)) y := by
    have h := hHS.hasSum_linearIsometryEquiv_symm (hHS.linearIsometryEquiv y)
    rwa [LinearIsometryEquiv.symm_apply_apply] at h
  have happ := hdecomp.mapL (i : H →L[ℂ] H)
  have hii : (i : H →L[ℂ] H)
      ((LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) i))
      = (LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) i) :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap (hF.1 i.1 i.2).1.isIdempotentElem)).mp (Submodule.coe_mem _)
  have hsingle : HasSum
      (fun j : F => (i : H →L[ℂ] H)
        ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) j)))
      ((i : H →L[ℂ] H)
        ((LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) i))) :=
    hasSum_single i (fun j hj => by
      have hjfix : (j : H →L[ℂ] H)
          ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) j))
          = (LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
              ((hHS.linearIsometryEquiv y) j) :=
        (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap (hF.1 j.1 j.2).1.isIdempotentElem)).mp (Submodule.coe_mem _)
      have hij0 : (i : H →L[ℂ] H) * (j : H →L[ℂ] H) = 0 :=
        hF.2 i.2 j.2 (fun h => hj (Subtype.ext h).symm)
      calc (i : H →L[ℂ] H)
            ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) j))
          = (i : H →L[ℂ] H) ((j : H →L[ℂ] H)
              ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
                ((hHS.linearIsometryEquiv y) j))) := by rw [hjfix]
        _ = ((i : H →L[ℂ] H) * (j : H →L[ℂ] H))
              ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
                ((hHS.linearIsometryEquiv y) j)) := rfl
        _ = 0 := by rw [hij0]; rfl)
  exact ((happ.unique hsingle).trans hii).symm

/-- The minimal projection `e` of a type I factor is the multiplicity space: a type I factor with
minimal projection `e` acts on a Hilbert space isometric to the `ℓ²` sum `ℓ²(F; eH)` of copies of
`eH = range e`, indexed by a covering orthogonal family `F` (`OrthEquivFam`, with densely
spanning ranges) of minimal projections equivalent to `e`. Composing with the tensor bridge turns
this `ℓ²` sum into the literal tensor product `H ≅ ℓ²(F) ⊗̂ eH`; that is the statement of
`exists_tmul_decomposition`, and it — not this one — is the tensor-product form. -/
theorem IsFactor.exists_lp_decomposition {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e) :
    ∃ F : Set (H →L[ℂ] H), OrthEquivFam N e F ∧
      (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤ ∧
      (∀ p ∈ F, IsMinimalProjection N p) ∧
      Nonempty (H ≃ₗᵢ[ℂ] lp (fun _ : F => LinearMap.range (e : H →ₗ[ℂ] H)) 2) := by
  obtain ⟨F, hF, htop⟩ := hN.exists_orthEquivFam_top he
  exact ⟨F, hF, htop, fun p hp => hF.isMinimalProjection_of_mem he hp,
    ⟨hF.multiplicityEquiv htop⟩⟩

/-- **Tensor-product decomposition (literal form).** A type I factor `N ⊆ B(H)` with minimal
projection `e` acts on a Hilbert space isometric to the completed Hilbert tensor product
`ℓ²(F) ⊗̂ (eH)`, where `F` is a covering orthogonal family (`OrthEquivFam`, with densely spanning
ranges) of minimal projections equivalent to `e` and `eH = range e` is the multiplicity space.
This is the literal `H ≅ ℓ²(F) ⊗̂ eH` form of the type I structure theorem, obtained from
`exists_lp_decomposition` by composing with the tensor bridge `HilbertTensor.lpTensorEquiv`. -/
theorem IsFactor.exists_tmul_decomposition {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e) :
    ∃ F : Set (H →L[ℂ] H), OrthEquivFam N e F ∧
      (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤ ∧
      (∀ p ∈ F, IsMinimalProjection N p) ∧
      Nonempty (H ≃ₗᵢ[ℂ]
        HilbertTensor (lp (fun _ : F => ℂ) 2) (LinearMap.range (e : H →ₗ[ℂ] H))) := by
  obtain ⟨F, hF, htop⟩ := hN.exists_orthEquivFam_top he
  have : CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H)) := he.1.completeSpace_range
  have : DecidableEq (↥F) := Classical.decEq _
  exact ⟨F, hF, htop, fun p hp => hF.isMinimalProjection_of_mem he hp,
    ⟨(hF.multiplicityEquiv htop).trans
      (HilbertTensor.lpTensorEquiv (ι := F) (K := LinearMap.range (e : H →ₗ[ℂ] H)))⟩⟩

end VonNeumannAlgebra
