/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.GNS.Construction
public import QuantumSystem.Algebra.CStarAlgebra.Representation
public import QuantumSystem.Algebra.CStarAlgebra.Representation.Irreducible
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.InvariantSubspace

/-!
# GNS representations of a positive functional

A GNS triplet `(π, H, ξ)` for a positive linear functional `f` on a (possibly non-unital)
C*-algebra `A` is a C*-representation `π` of `A` on a Hilbert space `H` together with a cyclic
vector `ξ` satisfying `f a = ⟪ξ, π a ξ⟫`.  A state `ω` is the case `f = ω.toPositiveLinearMap`,
with `‖f‖ₒₚ = 1`; the only state-specific facts are that `ξ` is then a unit
vector (`norm_ξ_eq_one`) and that `π ≠ 0`, since a state is nonzero
(`π_eq_zero_iff`, `State.toPositiveLinearMap_ne_zero`).

## Main definitions and results

* `GNS.Representation f`: GNS triplets for `f`, extending `CStarRep A`.
* `GNS.Representation.norm_ξ`: `‖ξ‖ = √‖f‖ₒₚ`; for a state, `norm_ξ_eq_one`.
* `GNS.Representation.norm_apply_cyclic`: `‖π a ξ‖ = √‖f (a* a)‖`.
* `GNS.Representation.π_eq_zero_iff`: `π = 0` iff `f = 0`.
* `GNS.Representation.actsNondegenerately`, `GNS.Representation.tendsto_π_approximateUnit`:
  a GNS triplet is non-degenerate, and `π e_α → 1` strongly along an approximate unit.
* `GNS.Representation.UnitaryEquiv`: unitary equivalence of GNS triplets, written `T₁ ≃ᵁ T₂`.
* `GNS.Representation.unique_up_to_unitary_equivalence`: any two GNS triplets for the same
  functional are unitarily equivalent.  The unitary `π₁ a ξ₁ ↦ π₂ a ξ₂` is Mathlib's
  `LinearEquiv.extendOfIsometry` applied to the two dense orbit maps.
* `GNS.Representation.canonical`: the triplet produced by the GNS construction, from Mathlib's
  `PositiveLinearMap.GNS` and `PositiveLinearMap.gnsNonUnitalStarAlgHom` and the cyclic vector
  `PositiveLinearMap.gnsVector`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexHilbertSpace InnerProduct ComplexOrder

namespace GNS

/-- A (non‑unital) GNS triplet `(π, H, ξ)` for a positive linear functional `f : A →ₚ[ℂ] ℂ` on a
(possibly non‑unital) C*-algebra `A`.

This structure extends the bundled C\*-algebra representation `CStarRep A`
(defined in `QuantumSystem.Algebra.CStarAlgebra.Representation`) by the additional data of a
cyclic vector `ξ` and the GNS identity, factoring the conceptual
decomposition "general C\*-representation" + "cyclic vector for a specified
positive functional" at the type level.

Inherited fields (from `CStarRep A`):
* `H` : the underlying type of the Hilbert space.
* `[hilbert]` : evidence that `H` is a complex Hilbert space.
* `π : A →⋆ₙₐ[ℂ] 𝓑(H)` : a non‑unital *-representation of `A` on `H`.

GNS-specific fields:
* `ξ : H` : a cyclic vector; its norm is automatically `√‖f‖ₒₚ` (`norm_ξ`), so it is a unit
  vector exactly when `f` is a state.
* `cyclic` : density of the orbit `{ π a ξ | a : A }` in `H`, i.e. of the range of the orbit map
  `CStarRep.orbit ξ`.  The orbit is already a linear subspace, so no linear span is needed.
* `gns_condition` : the GNS identity `f a = ⟪ξ, π a ξ⟫` for every `a : A`.
-/
structure Representation {A} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →ₚ[ℂ] ℂ) extends CStarRep A where
  /-- The cyclic vector ξ ∈ H -/
  ξ : H
  /-- The cyclic property: the orbit {π(a)ξ : a ∈ A} is dense in H -/
  cyclic : DenseRange (toCStarRep.orbit ξ)
  /-- The GNS condition: f(a) = ⟪ξ, π(a)ξ⟫ for all a ∈ A -/
  gns_condition : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ

namespace Representation

open ComplexConjugate PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {f : A →ₚ[ℂ] ℂ}

/-- A GNS representation acts non-degenerately: the only vector annihilated by every
operator in the image of `π` is `0`.

Cyclicity is what makes this work.  If `π a x = 0` for every `a`, then
`⟪x, π a ξ⟫ = ⟪π (star a) x, ξ⟫ = 0`, so the continuous functional `⟪x, ·⟫` vanishes on the dense
orbit of the cyclic vector, hence everywhere, and in particular `⟪x, x⟫ = 0`. -/
theorem actsNondegenerately (T : Representation f) :
    InnerProductSpace.ActsNondegenerately (Set.range (T.π : A → 𝓑(T.H))) := by
  intro x hx
  have h_orbit : Set.EqOn (fun y => ⟪x, y⟫_ℂ) (fun _ => 0) (Set.range (T.orbit T.ξ)) := by
    rintro _ ⟨a, rfl⟩
    have h : T.π (star a) x = 0 := hx _ ⟨star a, rfl⟩
    rw [← T.adjoint_π] at h
    simp only [CStarRep.orbit_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h, inner_zero_left]
  have h_zero := Continuous.ext_on T.cyclic (by fun_prop) continuous_const h_orbit
  exact inner_self_eq_zero.mp (congrFun h_zero x)

/-! ### Approximate units act as the identity

Along an approximate unit `(e_α)` of `A`, the operators `π e_α` converge strongly to the identity
on the Hilbert space of any GNS triplet — a quantitative form of nondegeneracy.  Only finiteness
of `‖ξ‖` is used, so this yields the normalisation `‖ξ‖² = ‖f‖ₒₚ` (`norm_ξ_sq`) as a theorem:
`f e_α = ⟪ξ, π e_α ξ⟫ → ‖ξ‖²`, while `f e_α → ‖f‖ₒₚ`
(`PositiveContinuousLinearMap.tendsto_nhds_opNorm`). -/

section ApproximateUnit

open Filter Topology

variable (T : Representation f)

/-- Approximate-unit elements act as contractions. -/
lemma eventually_norm_π_le_one :
    ∀ᶠ e in CStarAlgebra.approximateUnit A, ‖T.π e‖ ≤ 1 :=
  (CStarAlgebra.increasingApproximateUnit (A := A)).eventually_norm.mono fun e he =>
    (NonUnitalStarAlgHom.norm_apply_le _ e).trans he

/-- Approximate units act as the identity on the orbit vectors `π a ξ`. -/
lemma tendsto_π_approximateUnit_orbit (a : A) :
    Tendsto (fun e : A => T.π e (T.π a T.ξ)) (CStarAlgebra.approximateUnit A)
      (𝓝 (T.π a T.ξ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h_eq : (fun e : A => ‖T.π e (T.π a T.ξ) - T.π a T.ξ‖) =
      fun e : A => ‖T.π (e * a - a) T.ξ‖ := by
    funext e
    simp [map_sub, map_mul]
  rw [h_eq]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun e => (T.orbit T.ξ).le_of_opNorm_le (T.norm_orbit_le T.ξ) (e * a - a)) ?_
  simpa using (tendsto_iff_norm_sub_tendsto_zero.mp
    ((CStarAlgebra.increasingApproximateUnit (A := A)).tendsto_mul_right a)).const_mul ‖T.ξ‖

/-- Approximate units act as the identity on the whole Hilbert space: `π e_α → 1` strongly. -/
theorem tendsto_π_approximateUnit (x : T.H) :
    Tendsto (fun e : A => T.π e x) (CStarAlgebra.approximateUnit A) (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Approximate `x` within `ε / 4` by an orbit vector `y = π b ξ`.
  obtain ⟨b, hy_dist⟩ := T.cyclic.exists_dist_lt x (by positivity : 0 < ε / 4)
  set y := T.π b T.ξ
  have hy_norm : ‖x - y‖ < ε / 4 := by rwa [dist_eq_norm] at hy_dist
  have hy := (Metric.tendsto_nhds.mp (T.tendsto_π_approximateUnit_orbit b)) (ε / 2) (by positivity)
  filter_upwards [T.eventually_norm_π_le_one, hy] with e he hey
  rw [dist_eq_norm] at hey ⊢
  -- `π e x - x = (π e (x - y) - (x - y)) + (π e y - y)`, with the first term at most `2 ‖x - y‖`.
  have h_decomp : T.π e x - x = (T.π e (x - y) - (x - y)) + (T.π e y - y) := by
    simp only [map_sub]; abel
  have h_first : ‖T.π e (x - y) - (x - y)‖ ≤ 2 * ‖x - y‖ :=
    calc ‖T.π e (x - y) - (x - y)‖
        ≤ ‖T.π e (x - y)‖ + ‖x - y‖ := norm_sub_le _ _
      _ ≤ ‖T.π e‖ * ‖x - y‖ + ‖x - y‖ := by gcongr; exact (T.π e).le_opNorm _
      _ ≤ 1 * ‖x - y‖ + ‖x - y‖ := by gcongr
      _ = 2 * ‖x - y‖ := by ring
  calc ‖T.π e x - x‖
      ≤ ‖T.π e (x - y) - (x - y)‖ + ‖T.π e y - y‖ := by rw [h_decomp]; exact norm_add_le _ _
    _ < 2 * (ε / 4) + ε / 2 := by gcongr; linarith
    _ = ε := by ring

/-- `f e_α → ‖ξ‖²` along an approximate unit. -/
lemma tendsto_apply_approximateUnit_norm_sq :
    Tendsto (fun e : A => f e) (CStarAlgebra.approximateUnit A) (𝓝 ((‖T.ξ‖ ^ 2 : ℝ) : ℂ)) := by
  have h : Tendsto (fun e : A => ⟪T.ξ, T.π e T.ξ⟫_ℂ) (CStarAlgebra.approximateUnit A)
      (𝓝 ⟪T.ξ, T.ξ⟫_ℂ) :=
    (continuous_const.inner continuous_id).tendsto T.ξ |>.comp (T.tendsto_π_approximateUnit T.ξ)
  simpa [← T.gns_condition, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] using h

/-- The squared norm of the cyclic vector is the norm of the functional: `‖ξ‖² = ‖f‖ₒₚ`.  Along
an approximate unit, `f e_α` tends both to `‖ξ‖²` and to `‖f‖ₒₚ`
(`PositiveContinuousLinearMap.tendsto_nhds_opNorm`). -/
theorem norm_ξ_sq : ‖T.ξ‖ ^ 2 = ‖f‖ₒₚ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have : (CStarAlgebra.approximateUnit A).NeBot := hl.toIsApproximateUnit.neBot
  exact_mod_cast tendsto_nhds_unique T.tendsto_apply_approximateUnit_norm_sq
    ((PositiveContinuousLinearMap.ofClass f).tendsto_nhds_opNorm hl)

/-- `‖ξ‖ = √‖f‖ₒₚ`, the same form as `PositiveLinearMap.norm_gnsVector` for the canonical
triplet. -/
theorem norm_ξ : ‖T.ξ‖ = √‖f‖ₒₚ := by
  rw [← T.norm_ξ_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The cyclic vector of a GNS triplet of a state is a unit vector. -/
theorem norm_ξ_eq_one {ω : State A} (T : Representation ω.toPositiveLinearMap) :
    ‖T.ξ‖ = 1 := by
  rw [T.norm_ξ, ω.norm_eq_one, Real.sqrt_one]

end ApproximateUnit

/-- A GNS representation is null exactly for the zero functional.  If `π = 0` then
`f a = ⟪ξ, π a ξ⟫ = 0` for every `a`; conversely, `f = 0` forces `‖ξ‖² = ‖f‖ₒₚ = 0`
(`norm_ξ_sq`), and the orbit of `ξ = 0` is dense only in the zero space. -/
theorem π_eq_zero_iff (T : Representation f) : T.π = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact PositiveLinearMap.ext fun a => by simp [T.gns_condition, h]
  · rintro rfl
    have hξ : T.ξ = 0 := by
      rw [← norm_eq_zero, T.norm_ξ, (opNorm_eq_zero_iff 0).mpr rfl, Real.sqrt_zero]
    have hH : ∀ x : T.H, x = 0 := fun x => congrFun (Continuous.ext_on T.cyclic continuous_id
      continuous_const (by rintro _ ⟨a, rfl⟩; simp [hξ])) x
    ext a x
    simp [hH (T.π a x)]

/-- The GNS representation of a nonzero functional is non-null (`π_eq_zero_iff`). -/
theorem π_ne_zero (T : Representation f) (hf : f ≠ 0) : T.π ≠ 0 :=
  T.π_eq_zero_iff.not.mpr hf

/-- A unitary equivalence between two GNS representations for the **same** functional `f`.

This **extends** the generic unitary equivalence of the underlying `CStarRep`s
(`CStarRep.UnitaryEquiv`, which supplies the intertwining unitary `toLinearIsometryEquiv` and its
`intertwines` property) by the GNS-specific compatibility `map_cyclic_vector`, requiring the
unitary to identify the two cyclic vectors.  This is exactly the extra data of the GNS
uniqueness statement, on top of the bare unitary intertwiner shared with sector theory. -/
structure UnitaryEquiv (T₁ T₂ : Representation f) extends
    CStarRep.UnitaryEquiv T₁.toCStarRep T₂.toCStarRep where
  /-- The unitary sends the cyclic vector of the first triplet to that of the second. -/
  map_cyclic_vector : toUnitaryEquiv.toLinearIsometryEquiv T₁.ξ = T₂.ξ

notation:50 T₁ " ≃ᵁ " T₂ => Representation.UnitaryEquiv (f := _) T₁ T₂

/-- For a GNS triplet, the length of the orbit vector `T.π x T.ξ` is read off from the functional:
`‖π x ξ‖ = √‖f (x* x)‖`, the same form as `PositiveLinearMap.norm_gnsMk` for the canonical
triplet. -/
lemma norm_apply_cyclic (T : Representation f) (x : A) :
    ‖T.π x T.ξ‖ = √‖f (star x * x)‖ := by
  have hval : T.π (star x * x) T.ξ = ((T.π x)†) (T.π x T.ξ) := by
    rw [map_mul, ← T.adjoint_π]
    rfl
  rw [T.gns_condition (star x * x), hval, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- The unitary `π₁ a ξ₁ ↦ π₂ a ξ₂` between two GNS triplets of the same functional.  It extends the
identity of `A` through the two dense orbit maps (`LinearEquiv.extendOfIsometry`); the orbit
vectors have matching norms since both equal `√‖f (a* a)‖` (`norm_apply_cyclic`). -/
private noncomputable def cyclicIsometry (T₁ T₂ : Representation f) : T₁.H ≃ₗᵢ[ℂ] T₂.H :=
  (LinearEquiv.refl ℂ A).extendOfIsometry (T₁.orbit T₁.ξ).toLinearMap
    (T₂.orbit T₂.ξ).toLinearMap T₁.cyclic T₂.cyclic fun a => by
      simp [norm_apply_cyclic]

private lemma cyclicIsometry_apply_orbit (T₁ T₂ : Representation f) (a : A) :
    cyclicIsometry T₁ T₂ (T₁.π a T₁.ξ) = T₂.π a T₂.ξ :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

/-- `cyclicIsometry` intertwines the two representations; by density it suffices to check this on
orbit vectors, where it is `π₁ (a b) ξ₁ ↦ π₂ (a b) ξ₂`. -/
private lemma cyclicIsometry_intertwines (T₁ T₂ : Representation f) (a : A) :
    (cyclicIsometry T₁ T₂ : T₁.H →L[ℂ] T₂.H) ∘L T₁.π a =
      T₂.π a ∘L (cyclicIsometry T₁ T₂ : T₁.H →L[ℂ] T₂.H) := by
  refine DFunLike.coe_injective <|
    Continuous.ext_on T₁.cyclic (map_continuous _) (map_continuous _) ?_
  rintro _ ⟨b, rfl⟩
  have h₁ : T₁.π a (T₁.π b T₁.ξ) = T₁.π (a * b) T₁.ξ := by rw [map_mul]; rfl
  have h₂ : T₂.π a (T₂.π b T₂.ξ) = T₂.π (a * b) T₂.ξ := by rw [map_mul]; rfl
  change cyclicIsometry T₁ T₂ (T₁.π a (T₁.π b T₁.ξ)) =
    T₂.π a (cyclicIsometry T₁ T₂ (T₁.π b T₁.ξ))
  rw [h₁, cyclicIsometry_apply_orbit, cyclicIsometry_apply_orbit, h₂]

/-- `cyclicIsometry` maps `ξ₁` to `ξ₂`: both are the limits of the orbit vectors `π e_α ξ` along
an approximate unit (`tendsto_π_approximateUnit`). -/
private lemma cyclicIsometry_ξ (T₁ T₂ : Representation f) : cyclicIsometry T₁ T₂ T₁.ξ = T₂.ξ := by
  have : (CStarAlgebra.approximateUnit A).NeBot :=
    (CStarAlgebra.increasingApproximateUnit (A := A)).toIsApproximateUnit.neBot
  have h := ((cyclicIsometry T₁ T₂).continuous.tendsto T₁.ξ).comp
    (T₁.tendsto_π_approximateUnit T₁.ξ)
  refine tendsto_nhds_unique h ?_
  simpa [Function.comp_def, cyclicIsometry_apply_orbit] using T₂.tendsto_π_approximateUnit T₂.ξ

/-- GNS representations of a fixed positive functional are unique up to unitary equivalence.

Given two GNS triplets `(π₁, H₁, ξ₁)` and `(π₂, H₂, ξ₂)` for the same functional `f`, there exists a
unitary equivalence `U : T₁ ≃ᵁ T₂` sending the cyclic vector of the first representation to that of
the second and intertwining the two *-representations. In particular, every GNS triplet is
unitarily equivalent to the canonical construction, and any two triplets are unitarily equivalent. -/
theorem unique_up_to_unitary_equivalence :
    ∀ T₁ T₂ : Representation f, Nonempty (T₁ ≃ᵁ T₂) := fun T₁ T₂ =>
  ⟨{ toLinearIsometryEquiv := cyclicIsometry T₁ T₂
     intertwines := cyclicIsometry_intertwines T₁ T₂
     map_cyclic_vector := cyclicIsometry_ξ T₁ T₂ }⟩

variable (f) in
/-- The canonical GNS triplet `(f.GNS, π_f, ξ_f)` produced by the GNS construction: Mathlib's
`PositiveLinearMap.GNS` and `PositiveLinearMap.gnsNonUnitalStarAlgHom`, with the cyclic vector
`PositiveLinearMap.gnsVector`.  For a state `ω` it is `(𝓗[ω], π[ω], ξ[ω])`. -/
noncomputable def canonical : Representation f where
  toCStarRep := f.gnsCStarRep
  ξ := f.gnsVector
  cyclic := f.denseRange_gnsNonUnitalStarAlgHom_apply_gnsVector
  gns_condition := f.apply_eq_inner_gnsNonUnitalStarAlgHom_gnsVector

section Canonical

variable (f)

/-- The representation underlying the canonical triplet is `PositiveLinearMap.gnsCStarRep`. -/
lemma canonical_toCStarRep : (canonical f).toCStarRep = f.gnsCStarRep := rfl

/-- The Hilbert space of the canonical triplet is Mathlib's `PositiveLinearMap.GNS`. -/
lemma canonical_H : (canonical f).H = f.GNS := rfl

/-- The representation of the canonical triplet is `PositiveLinearMap.gnsNonUnitalStarAlgHom`. -/
lemma canonical_π : (canonical f).π = f.gnsNonUnitalStarAlgHom := rfl

/-- The cyclic vector of the canonical triplet is `PositiveLinearMap.gnsVector`. -/
lemma canonical_ξ : (canonical f).ξ = f.gnsVector := rfl

end Canonical

end Representation

end GNS
