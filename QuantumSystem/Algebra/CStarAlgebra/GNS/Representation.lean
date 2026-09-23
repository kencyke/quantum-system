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
# GNS representations of a state

A GNS triplet `(π, H, ξ)` for a state `ω` on a (possibly non-unital) C*-algebra `A` is a
C*-representation `π` of `A` on a Hilbert space `H` together with a cyclic vector `ξ` satisfying
`ω a = ⟪ξ, π a ξ⟫`.

## Main definitions and results

* `GNS.Representation ω`: GNS triplets for `ω`, extending `CStarRep A`.
* `GNS.Representation.norm_ξ`: the cyclic vector is a unit vector.
* `GNS.Representation.norm_apply_cyclic`: `‖π a ξ‖ = √‖ω (a* a)‖`.
* `GNS.Representation.actsNondegenerately`, `GNS.Representation.tendsto_π_approximateUnit`:
  a GNS triplet is non-degenerate, and `π e_α → 1` strongly along an approximate unit.
* `GNS.Representation.UnitaryEquiv`: unitary equivalence of GNS triplets, written `T₁ ≃ᵁ T₂`.
* `GNS.Representation.unique_up_to_unitary_equivalence`: any two GNS triplets for the same state
  are unitarily equivalent.  The unitary `π₁ a ξ₁ ↦ π₂ a ξ₂` is Mathlib's
  `LinearEquiv.extendOfIsometry` applied to the two dense orbit maps.
* `GNS.Representation.canonical`: the triplet produced by the GNS construction.
-/

@[expose] public section

open scoped InnerProductSpace ComplexHilbertSpace InnerProduct

namespace GNS

/-- A (non‑unital) GNS triplet `(π, H, ξ)` for a state `ω : A → ℂ` on a (possibly non‑unital)
C*-algebra `A`.

This structure extends the bundled C\*-algebra representation `CStarRep A`
(defined in `QuantumSystem.Algebra.CStarAlgebra.Representation`) by the additional data of a
cyclic unit vector `ξ` and the GNS identity, factoring the conceptual
decomposition "general C\*-representation" + "cyclic vector for a specified
state" at the type level.

Inherited fields (from `CStarRep A`):
* `H` : the underlying type of the Hilbert space.
* `[hilbert]` : evidence that `H` is a complex Hilbert space.
* `π : A →⋆ₙₐ[ℂ] 𝓑(H)` : a non‑unital *-representation of `A` on `H`.

GNS-specific fields:
* `ξ : H` : a cyclic vector; it is automatically a unit vector (`norm_ξ`).
* `cyclic` : density of the orbit `{ π a ξ | a : A }` in `H`, i.e. of the range of the orbit map
  `CStarRep.orbit ξ`.  The orbit is already a linear subspace, so no linear span is needed.
* `gns_condition` : the GNS identity `ω a = ⟪ξ, π a ξ⟫` for every `a : A`.
-/
structure Representation {A} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (ω : State A)
    extends CStarRep A where
  /-- The cyclic vector ξ ∈ H -/
  ξ : H
  /-- The cyclic property: the orbit {π(a)ξ : a ∈ A} is dense in H -/
  cyclic : DenseRange (toCStarRep.orbit ξ)
  /-- The GNS condition: ω(a) = ⟪ξ, π(a)ξ⟫ for all a ∈ A -/
  gns_condition : ∀ a : A, ω a = ⟪ξ, π a ξ⟫_ℂ

namespace Representation

open ComplexConjugate

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ω : State A}

/-- A GNS representation acts non-degenerately: the only vector annihilated by every
operator in the image of `π` is `0`.

Cyclicity is what makes this work.  If `π a x = 0` for every `a`, then
`⟪x, π a ξ⟫ = ⟪π (star a) x, ξ⟫ = 0`, so the continuous functional `⟪x, ·⟫` vanishes on the dense
orbit of the cyclic vector, hence everywhere, and in particular `⟪x, x⟫ = 0`. -/
theorem actsNondegenerately (T : Representation ω) :
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
of `‖ξ‖` is used, so this yields the normalisation `‖ξ‖ = 1` (`norm_ξ`) as a theorem:
`ω e_α = ⟪ξ, π e_α ξ⟫ → ‖ξ‖²`, while `ω e_α → ‖ω‖ = 1` (`State.tendsto_approximateUnit`). -/

section ApproximateUnit

open Filter Topology

variable (T : Representation ω)

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

/-- `ω e_α → ‖ξ‖²` along an approximate unit. -/
lemma tendsto_apply_approximateUnit_norm_sq :
    Tendsto (fun e : A => ω e) (CStarAlgebra.approximateUnit A) (𝓝 ((‖T.ξ‖ ^ 2 : ℝ) : ℂ)) := by
  have h : Tendsto (fun e : A => ⟪T.ξ, T.π e T.ξ⟫_ℂ) (CStarAlgebra.approximateUnit A)
      (𝓝 ⟪T.ξ, T.ξ⟫_ℂ) :=
    (continuous_const.inner continuous_id).tendsto T.ξ |>.comp (T.tendsto_π_approximateUnit T.ξ)
  simpa [← T.gns_condition, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] using h

/-- The cyclic vector of a GNS triplet is a unit vector: `‖ξ‖ = 1`.  Along an approximate unit,
`ω e_α` tends both to `‖ξ‖²` and to `1` (`State.tendsto_approximateUnit`). -/
theorem norm_ξ : ‖T.ξ‖ = 1 := by
  have : (CStarAlgebra.approximateUnit A).NeBot :=
    (CStarAlgebra.increasingApproximateUnit (A := A)).toIsApproximateUnit.neBot
  have h := tendsto_nhds_unique T.tendsto_apply_approximateUnit_norm_sq
    (ω.tendsto_approximateUnit (CStarAlgebra.increasingApproximateUnit A))
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast h)

end ApproximateUnit

open ComplexOrder in
/-- A GNS representation is non-null: `π = 0` would force `ω a = ⟪ξ, π a ξ⟫ = 0` for every `a`,
contradicting `‖ω‖ = 1`. -/
theorem π_ne_zero (T : Representation ω) : T.π ≠ 0 := by
  intro h
  have h0 : (PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ) = 0 := by
    ext a
    simp [T.gns_condition, h]
  have := ω.norm_ofClass
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- A unitary equivalence between two GNS representations for the **same** state `ω`.

This **extends** the generic unitary equivalence of the underlying `CStarRep`s
(`CStarRep.UnitaryEquiv`, which supplies the intertwining unitary `toLinearIsometryEquiv` and its
`intertwines` property) by the GNS-specific compatibility `map_cyclic_vector`, requiring the
unitary to identify the two cyclic vectors.  This is exactly the extra data of the GNS
uniqueness statement, on top of the bare unitary intertwiner shared with sector theory. -/
structure UnitaryEquiv (T₁ T₂ : Representation ω) extends
    CStarRep.UnitaryEquiv T₁.toCStarRep T₂.toCStarRep where
  /-- The unitary sends the cyclic vector of the first triplet to that of the second. -/
  map_cyclic_vector : toUnitaryEquiv.toLinearIsometryEquiv T₁.ξ = T₂.ξ

notation:50 T₁ " ≃ᵁ " T₂ => Representation.UnitaryEquiv (ω := _) T₁ T₂

/-- For a GNS triplet, the length of the orbit vector `T.π x T.ξ` is read off from the state:
`‖π x ξ‖ = √‖ω (x* x)‖`, the same form as `PositiveLinearMap.norm_gnsMk` for the canonical
triplet. -/
lemma norm_apply_cyclic (T : Representation ω) (x : A) :
    ‖T.π x T.ξ‖ = √‖ω (star x * x)‖ := by
  have hval : T.π (star x * x) T.ξ = ((T.π x)†) (T.π x T.ξ) := by
    rw [map_mul, ← T.adjoint_π]
    rfl
  rw [T.gns_condition (star x * x), hval, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- The unitary `π₁ a ξ₁ ↦ π₂ a ξ₂` between two GNS triplets of the same state.  It extends the
identity of `A` through the two dense orbit maps (`LinearEquiv.extendOfIsometry`); the orbit
vectors have matching norms since both equal `√‖ω (a* a)‖` (`norm_apply_cyclic`). -/
private noncomputable def cyclicIsometry (T₁ T₂ : Representation ω) : T₁.H ≃ₗᵢ[ℂ] T₂.H :=
  (LinearEquiv.refl ℂ A).extendOfIsometry (T₁.orbit T₁.ξ).toLinearMap
    (T₂.orbit T₂.ξ).toLinearMap T₁.cyclic T₂.cyclic fun a => by
      simp [norm_apply_cyclic]

private lemma cyclicIsometry_apply_orbit (T₁ T₂ : Representation ω) (a : A) :
    cyclicIsometry T₁ T₂ (T₁.π a T₁.ξ) = T₂.π a T₂.ξ :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ a

/-- `cyclicIsometry` intertwines the two representations; by density it suffices to check this on
orbit vectors, where it is `π₁ (a b) ξ₁ ↦ π₂ (a b) ξ₂`. -/
private lemma cyclicIsometry_intertwines (T₁ T₂ : Representation ω) (a : A) :
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
private lemma cyclicIsometry_ξ (T₁ T₂ : Representation ω) : cyclicIsometry T₁ T₂ T₁.ξ = T₂.ξ := by
  have : (CStarAlgebra.approximateUnit A).NeBot :=
    (CStarAlgebra.increasingApproximateUnit (A := A)).toIsApproximateUnit.neBot
  have h := ((cyclicIsometry T₁ T₂).continuous.tendsto T₁.ξ).comp
    (T₁.tendsto_π_approximateUnit T₁.ξ)
  refine tendsto_nhds_unique h ?_
  simpa [Function.comp_def, cyclicIsometry_apply_orbit] using T₂.tendsto_π_approximateUnit T₂.ξ

/-- GNS representations of a fixed state are unique up to unitary equivalence.

Given two GNS triplets `(π₁, H₁, ξ₁)` and `(π₂, H₂, ξ₂)` for the same state `ω`, there exists a
unitary equivalence `U : T₁ ≃ᵁ T₂` sending the cyclic vector of the first representation to that of
the second and intertwining the two *-representations. In particular, every GNS triplet is
unitarily equivalent to the canonical construction, and any two triplets are unitarily equivalent. -/
theorem unique_up_to_unitary_equivalence :
    ∀ T₁ T₂ : Representation ω, Nonempty (T₁ ≃ᵁ T₂) := fun T₁ T₂ =>
  ⟨{ toLinearIsometryEquiv := cyclicIsometry T₁ T₂
     intertwines := cyclicIsometry_intertwines T₁ T₂
     map_cyclic_vector := cyclicIsometry_ξ T₁ T₂ }⟩

/-- The canonical GNS triplet `(𝓗[ω], π[ω], ξ[ω])` produced by the GNS construction
(`State.gnsSpace`, `State.gnsRep`, `State.gnsVector`). -/
noncomputable def canonical (ω : State A) : Representation ω where
  toCStarRep := ω.gnsCStarRep
  ξ := ξ[ω]
  cyclic := ω.gnsVector_cyclic
  gns_condition := ω.gns_condition

lemma canonical_toCStarRep : (canonical ω).toCStarRep = ω.gnsCStarRep := rfl
lemma canonical_H : (canonical ω).H = 𝓗[ω] := rfl
lemma canonical_π : (canonical ω).π = π[ω] := rfl
lemma canonical_ξ : (canonical ω).ξ = ξ[ω] := rfl

end Representation

end GNS
