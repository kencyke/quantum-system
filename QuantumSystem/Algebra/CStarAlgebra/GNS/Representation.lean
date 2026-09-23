/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.LinearAlgebra.Span.Def
public import QuantumSystem.ForMathlib.Topology.DenseLinear
public import QuantumSystem.ForMathlib.Topology.MetricSpace.Completion
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
* `GNS.Representation.UnitaryEquiv`: unitary equivalence of GNS triplets, written `T₁ ≃ᵁ T₂`.
* `GNS.Representation.unique_up_to_unitary_equivalence`: any two GNS triplets for the same state
  are unitarily equivalent.
* `GNS.Representation.canonical`: the triplet produced by the GNS construction.
* `State.tendsto_approximateUnit`: a state evaluated along an approximate unit tends to `1`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexHilbertSpace

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
* `cyclic` : density of the linear span `Submodule.span ℂ { π a ξ | a : A }` in `H`.
* `gns_condition` : the GNS identity `ω a = ⟪ξ, π a ξ⟫` for every `a : A`.
-/
structure Representation {A} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (ω : State A)
    extends CStarRep A where
  /-- The cyclic vector ξ ∈ H -/
  ξ : H
  /-- The cyclic property: the span of {π(a)ξ : a ∈ A} is dense in H -/
  cyclic : Dense (↑(Submodule.span ℂ {π a ξ | a : A}) : Set H)
  /-- The GNS condition: ω(a) = ⟪ξ, π(a)ξ⟫ for all a ∈ A -/
  gns_condition : ∀ a : A, ω a = ⟪ξ, π a ξ⟫_ℂ

namespace Representation

open ComplexConjugate

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ω : State A}

/-- A submodule `W` of the Hilbert space of a GNS representation is invariant if it is
stable under the action of `π(a)` for every `a : A`.

This is the generic `CStarRep.IsInvariant` of the underlying representation `T.toCStarRep`;
it is provided here as a thin wrapper so that the GNS-specific lemmas read `T.IsInvariant W`,
while the single source of truth for the notion is `CStarRep.IsInvariant`. -/
def IsInvariant (T : Representation ω) (W : Submodule ℂ T.H) : Prop :=
  T.toCStarRep.IsInvariant W

/-- A GNS representation is (topologically) irreducible if it is non-null and the only
**closed** invariant submodules are `⊥` and `⊤`.

This is the generic `CStarRep.IsIrreducible` of the underlying representation `T.toCStarRep`
(definitionally, since `T.H`/`T.π` are the inherited fields); the GNS wrapper keeps the
`T.IsIrreducible` spelling while delegating the definition to `CStarRep.IsIrreducible`. -/
def IsIrreducible (T : Representation ω) : Prop :=
  T.toCStarRep.IsIrreducible

@[simp] lemma isInvariant_bot (T : Representation ω) : T.IsInvariant (⊥ : Submodule ℂ T.H) := by
  intro a w hw
  rcases (show w = 0 from by simpa using hw) with rfl
  simp

@[simp] lemma isInvariant_top (T : Representation ω) : T.IsInvariant (⊤ : Submodule ℂ T.H) := by
  intro a w hw
  simp

/-- A GNS representation acts non-degenerately: the only vector annihilated by every
operator in the image of `π` is `0`.

Cyclicity is what makes this work.  If `π a x = 0` for every `a`, then
`⟪x, π a ξ⟫ = ⟪π (star a) x, ξ⟫ = 0`, so `x` is orthogonal to the linear span of the orbit of
the cyclic vector; that span is dense, hence its orthogonal complement is trivial. -/
theorem actsNondegenerately (T : Representation ω) :
    InnerProductSpace.ActsNondegenerately (Set.range (T.π : A → 𝓑(T.H))) := by
  intro x hx
  have hx' : ∀ a : A, T.π a x = 0 := fun a => hx _ ⟨a, rfl⟩
  have hstar : ∀ a : A, (T.π a).adjoint = T.π (star a) := by
    intro a
    have h : T.π (star a) = star (T.π a) := T.π.map_star' a
    rw [ContinuousLinearMap.star_eq_adjoint] at h
    exact h.symm
  set S : Submodule ℂ T.H := Submodule.span ℂ {y | ∃ a : A, T.π a T.ξ = y} with hS
  have hmem : x ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [← ContinuousLinearMap.adjoint_inner_left, hstar a, hx' (star a), inner_zero_left]
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
    | smul c y _ hy => simp [inner_smul_right, hy]
  have htop : S.topologicalClosure = ⊤ := by
    ext y
    simp only [Submodule.mem_top, iff_true]
    exact T.cyclic y
  have hbot : Sᗮ = ⊥ := Submodule.topologicalClosure_eq_top_iff.mp htop
  simpa [hbot] using hmem

/-! ### Approximate units act as the identity

Along an approximate unit `(e_α)` of `A`, the operators `π e_α` converge strongly to the identity
on the Hilbert space of any GNS triplet — a quantitative form of nondegeneracy.  Only finiteness
of `‖ξ‖` is used, so this yields the normalisation `‖ξ‖ = 1` (`norm_ξ`) as a theorem:
`‖ξ‖² = lim ω e_α ≤ 1`, while `|ω a| = |⟪ξ, π a ξ⟫| ≤ ‖a‖ ‖ξ‖²` gives `1 = ‖ω‖ ≤ ‖ξ‖²`. -/

section ApproximateUnit

open Filter Topology

variable (T : Representation ω)

/-- The orbit vectors are bounded by the algebra norm: `‖π a ξ‖ ≤ ‖a‖ ‖ξ‖`. -/
lemma norm_π_ξ_le (a : A) : ‖T.π a T.ξ‖ ≤ ‖a‖ * ‖T.ξ‖ :=
  ((T.π a).le_opNorm _).trans (by gcongr; exact NonUnitalStarAlgHom.norm_apply_le _ a)

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
  refine squeeze_zero (fun _ => norm_nonneg _) (fun e => T.norm_π_ξ_le (e * a - a)) ?_
  simpa using (tendsto_iff_norm_sub_tendsto_zero.mp
    ((CStarAlgebra.increasingApproximateUnit (A := A)).tendsto_mul_right a)).mul_const ‖T.ξ‖

/-- Approximate units act as the identity on the linear span of the orbit of `ξ`. -/
lemma tendsto_π_approximateUnit_of_mem_span {x : T.H}
    (hx : x ∈ Submodule.span ℂ {T.π a T.ξ | a : A}) :
    Tendsto (fun e : A => T.π e x) (CStarAlgebra.approximateUnit A) (𝓝 x) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact T.tendsto_π_approximateUnit_orbit a
  | zero => simp
  | add y z _ _ hy hz => simpa [map_add] using hy.add hz
  | smul c y _ hy => simpa [map_smul] using hy.const_smul c

/-- Approximate units act as the identity on the whole Hilbert space: `π e_α → 1` strongly. -/
theorem tendsto_π_approximateUnit (x : T.H) :
    Tendsto (fun e : A => T.π e x) (CStarAlgebra.approximateUnit A) (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Approximate `x` within `ε / 4` by a vector `y` of the cyclic span.
  obtain ⟨y, hy_mem, hy_dist⟩ := T.cyclic.exists_dist_lt x (by positivity : 0 < ε / 4)
  have hy_norm : ‖x - y‖ < ε / 4 := by rwa [dist_eq_norm] at hy_dist
  have hy := (Metric.tendsto_nhds.mp (T.tendsto_π_approximateUnit_of_mem_span hy_mem))
    (ε / 2) (by positivity)
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

/-- The cyclic vector of a GNS triplet is a unit vector: `‖ξ‖ = 1`. -/
theorem norm_ξ : ‖T.ξ‖ = 1 := by
  have : (CStarAlgebra.approximateUnit A).NeBot :=
    (CStarAlgebra.increasingApproximateUnit (A := A)).toIsApproximateUnit.neBot
  -- Upper bound: `‖ξ‖² = lim ω e_α` and `‖ω e‖ ≤ ‖e‖ ≤ 1`.
  have h_le : ‖T.ξ‖ ^ 2 ≤ 1 := by
    have h := (continuous_norm.tendsto _).comp T.tendsto_apply_approximateUnit_norm_sq
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    refine le_of_tendsto h ?_
    filter_upwards [(CStarAlgebra.increasingApproximateUnit (A := A)).eventually_norm] with e he
    exact (ω.norm_apply_le e).trans he
  -- Lower bound: `|ω a| = |⟪ξ, π a ξ⟫| ≤ ‖a‖ ‖ξ‖²`, and `‖ω‖ = 1`.
  have h_ge : 1 ≤ ‖T.ξ‖ ^ 2 := by
    rw [← ω.norm_toContinuousLinearMap]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    rw [State.toContinuousLinearMap_apply, T.gns_condition]
    calc ‖⟪T.ξ, T.π a T.ξ⟫_ℂ‖
        ≤ ‖T.ξ‖ * ‖T.π a T.ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖T.ξ‖ * (‖a‖ * ‖T.ξ‖) := by gcongr; exact T.norm_π_ξ_le a
      _ = ‖T.ξ‖ ^ 2 * ‖a‖ := by ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (le_antisymm h_le h_ge)

/-- Evaluation of the state along an approximate unit converges to `1`: `ω e_α → 1`. -/
theorem tendsto_apply_approximateUnit (T : Representation ω) :
    Tendsto (fun e : A => ω e) (CStarAlgebra.approximateUnit A) (𝓝 1) := by
  simpa [T.norm_ξ] using T.tendsto_apply_approximateUnit_norm_sq

end ApproximateUnit

/-- A GNS representation is non-null: `π = 0` would force `ω a = ⟪ξ, π a ξ⟫ = 0` for every `a`,
contradicting `‖ω‖ = 1`. -/
theorem π_ne_zero (T : Representation ω) : T.π ≠ 0 := by
  intro h
  have h0 : ω.toContinuousLinearMap = 0 := by
    ext a
    simp [State.toContinuousLinearMap_apply, T.gns_condition, h]
  have := ω.norm_toContinuousLinearMap
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

/-- Auxiliary: computes `⟪π a ξ, π b ξ⟫ = ω (star a * b)` for a single GNS triplet. -/
private lemma inner_cyclic_aux (T : Representation ω) (a b : A) :
    ⟪T.π a T.ξ, T.π b T.ξ⟫_ℂ = ω (star a * b) := by
  have h₁ : ⟪T.π a T.ξ, T.π b T.ξ⟫_ℂ =
            ⟪T.ξ, (T.π a).adjoint (T.π b T.ξ)⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hstar : (T.π a).adjoint = T.π (star a) := by
    have : T.π (star a) = star (T.π a) := T.π.map_star' a
    rw [ContinuousLinearMap.star_eq_adjoint] at this
    exact this.symm
  have hmul : (T.π a).adjoint (T.π b T.ξ) = T.π (star a * b) T.ξ := by
    rw [hstar, show T.π (star a * b) = T.π (star a) * T.π b from T.π.map_mul' (star a) b]; rfl
  rw [h₁, hmul, (T.gns_condition (star a * b)).symm]

/-- Inner products on cyclic vectors agree across triplets: both realise `ω (star a * b)`. -/
private lemma inner_cyclic (T₁ T₂ : Representation ω) (a b : A) :
    ⟪T₁.π a T₁.ξ, T₁.π b T₁.ξ⟫_ℂ =
    ⟪T₂.π a T₂.ξ, T₂.π b T₂.ξ⟫_ℂ := by
  calc
    ⟪T₁.π a T₁.ξ, T₁.π b T₁.ξ⟫_ℂ
        = ω (star a * b) := inner_cyclic_aux T₁ a b
    _ = ⟪T₂.π a T₂.ξ, T₂.π b T₂.ξ⟫_ℂ := (inner_cyclic_aux T₂ a b).symm

/-- Equality of norms of corresponding cyclic orbit vectors between two triplets. -/
private lemma norm_cyclic (T₁ T₂ : Representation ω) (a : A) :
    ‖T₁.π a T₁.ξ‖ = ‖T₂.π a T₂.ξ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_sq ℂ]
  exact congr_arg RCLike.re (inner_cyclic T₁ T₂ a a)

/-- The canonical correspondence on cyclic orbit vectors: `π₁(a) ξ₁ ↦ π₂(a) ξ₂`. -/
private noncomputable def cyclicCorrespondence (_T₁ T₂ : Representation ω) (a : A) : T₂.H :=
  T₂.π a T₂.ξ

/-- Well-definedness of the cyclic correspondence: equality in the first triplet forces
equality in the second (uses preservation of inner products). -/
private lemma cyclic_correspondence_well_defined (T₁ T₂ : Representation ω) (a b : A)
    (h : T₁.π a T₁.ξ = T₁.π b T₁.ξ) :
    cyclicCorrespondence T₁ T₂ a = cyclicCorrespondence T₁ T₂ b := by
  unfold cyclicCorrespondence
  -- Show their difference acts trivially on ξ in T₁
  have h_map_sub : T₁.π (a - b) T₁.ξ = 0 := by
    calc T₁.π (a - b) T₁.ξ
        = (T₁.π a - T₁.π b) T₁.ξ := by rw [map_sub]
      _ = T₁.π a T₁.ξ - T₁.π b T₁.ξ := by simp [sub_apply]
      _ = 0 := by rw [h]; simp
  -- Transfer vanishing inner product to T₂ using equality of inner forms on cyclic vectors
  have h_inner_zero_T₂ : ⟪T₂.π (a - b) T₂.ξ, T₂.π (a - b) T₂.ξ⟫_ℂ = 0 := by
    rw [← inner_cyclic T₁ T₂ (a - b) (a - b), h_map_sub]; simp
  -- Norm zero implies vector zero in T₂
  have h_map_sub_T₂ : T₂.π (a - b) T₂.ξ = 0 := by
    have h_norm_sq : ‖T₂.π (a - b) T₂.ξ‖ ^ 2 = 0 := by
      rw [← @inner_self_eq_norm_sq ℂ, h_inner_zero_T₂]; simp
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (h_norm_sq ▸ le_refl _) (sq_nonneg _)))
  -- Rewrite to conclude equality of images (add (π (a-b) ξ) = 0 on the right)
  calc T₂.π a T₂.ξ
      = T₂.π a T₂.ξ - T₂.π (a - b) T₂.ξ := by rw [h_map_sub_T₂]; simp
    _ = T₂.π a T₂.ξ - (T₂.π a - T₂.π b) T₂.ξ := by rw [map_sub]
    _ = T₂.π a T₂.ξ - (T₂.π a T₂.ξ - T₂.π b T₂.ξ) := by simp [sub_apply]
    _ = T₂.π b T₂.ξ := by abel

/-- The cyclic set: `{ π a ξ | a : A }` as a subset of the Hilbert space. -/
private def cyclicSet (T : Representation ω) : Set T.H :=
  ⋃ (a : A), {T.π a T.ξ}

/-- Helper lemma: for a *-homomorphism `π`, density of the union of singletons
`⋃ a, {π a ξ}` is equivalent to density of the span `Submodule.span ℂ {π a ξ | a : A}`. -/
private lemma dense_iUnion_iff_dense_span {A H : Type*} [NonUnitalCStarAlgebra A]
    [ComplexHilbertSpace H] (π : A →⋆ₙₐ[ℂ] 𝓑(H)) (ξ : H) :
    Dense (⋃ (a : A), {π a ξ} : Set H) ↔ Dense (↑(Submodule.span ℂ {π a ξ | a : A}) : Set H) := by
  simp only [dense_iff_closure_eq, Set.iUnion_singleton_eq_range]
  have h_eq : (Set.range fun a => π a ξ) = {π a ξ | a : A} := by ext; simp
  rw [h_eq]
  constructor
  · intro h
    have : closure {π a ξ | a : A} ⊆ closure (↑(Submodule.span ℂ {π a ξ | a : A}) : Set H) :=
      closure_mono Submodule.subset_span
    rw [h] at this
    exact Set.eq_univ_of_univ_subset this
  · intro h
    have hS_add : ∀ {x y}, x ∈ {π a ξ | a : A} → y ∈ {π a ξ | a : A} → x + y ∈ {π a ξ | a : A} := by
      intro x y hx hy
      obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [map_add]⟩
    have hS_smul : ∀ (c : ℂ) {x}, x ∈ {π a ξ | a : A} → c • x ∈ {π a ξ | a : A} := by
      intro c x hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨c • a, by simp [map_smul]⟩
    have : Set.univ ⊆ closure {π a ξ | a : A} := by
      calc Set.univ
        _ = closure (↑(Submodule.span ℂ {π a ξ | a : A}) : Set H) := h.symm
        _ ⊆ closure (closure {π a ξ | a : A}) :=
          closure_mono (Submodule.span_subset_closure ⟨π 0 ξ, 0, rfl⟩ hS_add hS_smul)
        _ = closure {π a ξ | a : A} := closure_closure
    exact Set.eq_univ_of_univ_subset this

/-- Density of the cyclic set (reformulation of the `cyclic` field). -/
private lemma dense_cyclicSet (T : Representation ω) : Dense (cyclicSet T) := by
  unfold cyclicSet
  rw [dense_iUnion_iff_dense_span]
  exact T.cyclic

private lemma mem_cyclicSet (T : Representation ω) (a : A) :
  T.π a T.ξ ∈ cyclicSet T := by
  apply Set.mem_iUnion.mpr
  exact ⟨a, rfl⟩

/-- Characterisation of elements of the cyclic set. -/
private lemma mem_cyclic_set_iff (T : Representation ω) (x : T.H) :
  x ∈ cyclicSet T ↔ ∃ a : A, x = T.π a T.ξ := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    exact ⟨a, (Set.mem_singleton_iff.mp ha)⟩
  · rintro ⟨a, rfl⟩
    exact mem_cyclicSet T a

/-- Distance from the cyclic vector is preserved across corresponding orbit vectors. -/
private lemma dist_cyclic (T₁ T₂ : Representation ω) (a : A) :
    ‖T₁.π a T₁.ξ - T₁.ξ‖ = ‖T₂.π a T₂.ξ - T₂.ξ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [@norm_sub_sq ℂ T₁.H, @norm_sub_sq ℂ T₂.H]
  have h_norm := norm_cyclic T₁ T₂ a
  have h_inner₁ : ⟪T₁.π a T₁.ξ, T₁.ξ⟫_ℂ = conj (ω a) := by
    calc ⟪T₁.π a T₁.ξ, T₁.ξ⟫_ℂ
        = conj ⟪T₁.ξ, T₁.π a T₁.ξ⟫_ℂ := by rw [@inner_conj_symm ℂ T₁.H]
      _ = conj (ω a) := by rw [T₁.gns_condition a]
  have h_inner₂ : ⟪T₂.π a T₂.ξ, T₂.ξ⟫_ℂ = conj (ω a) := by
    calc ⟪T₂.π a T₂.ξ, T₂.ξ⟫_ℂ
        = conj ⟪T₂.ξ, T₂.π a T₂.ξ⟫_ℂ := by rw [@inner_conj_symm ℂ T₂.H]
      _ = conj (ω a) := by rw [T₂.gns_condition a]
  rw [h_inner₁, h_inner₂, h_norm, T₁.norm_ξ, T₂.norm_ξ]

/-- The set-level map on cyclic orbit vectors: every `x : cyclicSet T₁` is represented by
some `π₁(a) ξ₁`, and `cyclicMap` sends it to the matching vector `π₂(a) ξ₂`. -/
private noncomputable def cyclicMap (T₁ T₂ : Representation ω) :
  (cyclicSet T₁) → T₂.H :=
  fun x => T₂.π (Classical.choose (Set.mem_iUnion.mp x.property)) T₂.ξ

/-- Independence of representatives: the value of `cyclicMap` only depends on the point
`x : cyclicSet T₁`, not on the particular `a` used to describe it. -/
private lemma cyclicMap_well_defined (T₁ T₂ : Representation ω)
    (x : cyclicSet T₁) (a : A) (ha : x.val = T₁.π a T₁.ξ) :
    cyclicMap T₁ T₂ x = T₂.π a T₂.ξ := by
  unfold cyclicMap
  let a' := Classical.choose (Set.mem_iUnion.mp x.property)
  have ha' : x.val = T₁.π a' T₁.ξ := by
    have := Classical.choose_spec (Set.mem_iUnion.mp x.property)
    simp only [Set.mem_singleton_iff] at this
    exact this
  have h_eq : T₁.π a T₁.ξ = T₁.π a' T₁.ξ := by rw [← ha, ha']
  have := cyclic_correspondence_well_defined T₁ T₂ a a' h_eq
  unfold cyclicCorrespondence at this
  exact this.symm

/-- The cyclic map preserves inner products. -/
private lemma cyclicMap_inner (T₁ T₂ : Representation ω)
    (x y : cyclicSet T₁) :
    ⟪cyclicMap T₁ T₂ x, cyclicMap T₁ T₂ y⟫_ℂ =
    ⟪x.val, y.val⟫_ℂ := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp x.property
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp y.property
  simp only [Set.mem_singleton_iff] at ha hb
  rw [cyclicMap_well_defined T₁ T₂ x a ha, cyclicMap_well_defined T₁ T₂ y b hb, ha, hb]
  exact (inner_cyclic T₁ T₂ a b).symm

/-- The cyclic map preserves norms. -/
private lemma cyclicMap_norm (T₁ T₂ : Representation ω)
    (x : cyclicSet T₁) :
    ‖cyclicMap T₁ T₂ x‖ = ‖(x : T₁.H)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_sq ℂ]
  have := cyclicMap_inner T₁ T₂ x x
  exact congr_arg RCLike.re this

/-- The cyclic map preserves distances. -/
private lemma cyclicMap_dist (T₁ T₂ : Representation ω)
    (x y : cyclicSet T₁) :
    ‖cyclicMap T₁ T₂ x - cyclicMap T₁ T₂ y‖ = ‖(x : T₁.H) - (y : T₁.H)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), @norm_sub_sq ℂ T₂.H, @norm_sub_sq ℂ T₁.H]
  have h_norm_x := cyclicMap_norm T₁ T₂ x
  have h_norm_y := cyclicMap_norm T₁ T₂ y
  have h_inner := cyclicMap_inner T₁ T₂ x y
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] at h_norm_x h_norm_y
  simp only [h_norm_x, h_norm_y]
  linarith [congr_arg RCLike.re h_inner]

/-- The map on cyclic subsets is an isometry (with respect to the subtype metric). -/
private lemma cyclicMap_isometry (T₁ T₂ : Representation ω) :
    Isometry (cyclicMap T₁ T₂) := by
  intro x y
  have hx : edist (cyclicMap T₁ T₂ x) (cyclicMap T₁ T₂ y) =
            ENNReal.ofReal ‖cyclicMap T₁ T₂ x - cyclicMap T₁ T₂ y‖ := by
    rw [edist_dist, dist_eq_norm]
  have hy : edist x y = ENNReal.ofReal (dist (x : T₁.H) (y : T₁.H)) := by
    have : dist x y = dist (x : T₁.H) (y : T₁.H) := rfl
    rw [edist_dist, this]
  rw [hx, hy, dist_eq_norm, cyclicMap_dist]

/-- A linear isometry equivalence `U : T₁.H ≃ₗᵢ[ℂ] T₂.H` that maps cyclic vectors appropriately also
maps the cyclic vector of the first triplet to that of the second. -/
private lemma linear_isometry_equiv_map_cyclic_vector (T₁ T₂ : Representation ω)
    (U : T₁.H ≃ₗᵢ[ℂ] T₂.H)
    (h_cyclic : ∀ a : A, (U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ) :
    U T₁.ξ = T₂.ξ := by
  suffices ‖(U : T₁.H →L[ℂ] T₂.H) T₁.ξ - T₂.ξ‖ = 0 by exact eq_of_sub_eq_zero (norm_eq_zero.mp this)
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
  obtain ⟨x₁, hx₁_close, hx₁_mem⟩ :=
    Metric.dense_iff.mp (dense_cyclicSet T₁) T₁.ξ (ε / 2) (by linarith : 0 < ε / 2)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx₁_mem
  simp only [Set.mem_singleton_iff] at ha
  subst ha; rw [Metric.mem_ball, dist_eq_norm] at hx₁_close
  have : ‖(U : T₁.H →L[ℂ] T₂.H) T₁.ξ - T₂.ξ‖ < ε := by
    calc ‖(U : T₁.H →L[ℂ] T₂.H) T₁.ξ - T₂.ξ‖
        ≤ ‖(U : T₁.H →L[ℂ] T₂.H) T₁.ξ - (U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ)‖ +
          ‖(U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) - T₂.ξ‖ := by
          convert norm_add_le
                    ((U : T₁.H →L[ℂ] T₂.H) T₁.ξ - (U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ))
                    ((U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) - T₂.ξ) using 2
          abel
      _ = ‖(U : T₁.H →L[ℂ] T₂.H) (T₁.ξ - T₁.π a T₁.ξ)‖ + ‖T₂.π a T₂.ξ - T₂.ξ‖ := by
          rw [map_sub, h_cyclic]
      _ = ‖T₁.ξ - T₁.π a T₁.ξ‖ + ‖T₂.π a T₂.ξ - T₂.ξ‖ := by
          congr 1; exact U.norm_map _
      _ < ε / 2 + ε / 2 := by
          gcongr
          · rw [norm_sub_rev]; exact hx₁_close
          · rw [← dist_cyclic T₁ T₂ a]; exact hx₁_close
      _ = ε := by ring
  linarith

/-- Intertwining property on the cyclic subset: a linear isometry equivalence
`U : T₁.H ≃ₗᵢ[ℂ] T₂.H` respects products on orbit vectors. -/
private lemma linear_isometry_equiv_intertwines_on_cyclic (T₁ T₂ : Representation ω)
    (U : T₁.H ≃ₗᵢ[ℂ] T₂.H)
    (h_cyclic : ∀ a : A, (U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ) :
    ∀ a b : A, (U : T₁.H →L[ℂ] T₂.H) (T₁.π a (T₁.π b T₁.ξ)) =
               T₂.π a ((U : T₁.H →L[ℂ] T₂.H) (T₁.π b T₁.ξ)) := by
  intro a b
  calc (U : T₁.H →L[ℂ] T₂.H) (T₁.π a (T₁.π b T₁.ξ))
      _ = (U : T₁.H →L[ℂ] T₂.H) (T₁.π (a * b) T₁.ξ) := by
        rw [show T₁.π (a * b) = T₁.π a * T₁.π b from T₁.π.map_mul' a b]; rfl
      _ = T₂.π (a * b) T₂.ξ := h_cyclic (a * b)
      _ = T₂.π a (T₂.π b T₂.ξ) := by
        rw [show T₂.π (a * b) = T₂.π a * T₂.π b from T₂.π.map_mul' a b]; rfl
      _ = T₂.π a ((U : T₁.H →L[ℂ] T₂.H) (T₁.π b T₁.ξ)) := by rw [h_cyclic]

/-- Intertwining property extended from the cyclic subset to the whole space by density.
A linear isometry equivalence `U : T₁.H ≃ₗᵢ[ℂ] T₂.H` intertwines the representations. -/
private lemma linear_isometry_equiv_intertwines (T₁ T₂ : Representation ω)
    (U : T₁.H ≃ₗᵢ[ℂ] T₂.H)
    (h_cyclic : ∀ a : A, (U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ) :
    ∀ a : A, (U : T₁.H →L[ℂ] T₂.H) ∘L T₁.π a = T₂.π a ∘L (U : T₁.H →L[ℂ] T₂.H) := by
  intro a
  ext x
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have h_dense := dense_cyclicSet T₁
  unfold cyclicSet at h_dense
  have h_on_cyclic : ∀ b : A, (U : T₁.H →L[ℂ] T₂.H) (T₁.π a (T₁.π b T₁.ξ)) =
      T₂.π a ((U : T₁.H →L[ℂ] T₂.H) (T₁.π b T₁.ξ)) :=
    fun b => linear_isometry_equiv_intertwines_on_cyclic T₁ T₂ U h_cyclic a b
  let f : T₁.H → T₂.H := fun y => (U : T₁.H →L[ℂ] T₂.H) (T₁.π a y)
  let g : T₁.H → T₂.H := fun y => T₂.π a ((U : T₁.H →L[ℂ] T₂.H) y)
  change f x = g x
  have h_eq_on_dense : Set.EqOn f g (⋃ (b : A), {T₁.π b T₁.ξ}) := fun y hy => by
    obtain ⟨b, rfl⟩ := by simpa using hy
    exact h_on_cyclic b
  have hf : Continuous f := ((U : T₁.H →L[ℂ] T₂.H) ∘L T₁.π a).continuous
  have hg : Continuous g := (T₂.π a ∘L (U : T₁.H →L[ℂ] T₂.H)).continuous
  have : f = g := Continuous.ext_on h_dense hf hg h_eq_on_dense
  rw [this]

/-- Extension of the set-level isometry `cyclicMap T₁ T₂` from the dense subset `cyclicSet T₁`
to all of `T₁.H` via metric-space completion. -/
private noncomputable def extendCyclicMap (T₁ T₂ : Representation ω) : T₁.H → T₂.H :=
  MetricSpaceCompletion.extendDense (S := cyclicSet T₁)
    (dense_cyclicSet T₁) (cyclicMap T₁ T₂)

private lemma continuous_extendCyclicMap (T₁ T₂ : Representation ω) :
    Continuous (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) := by
  unfold extendCyclicMap
  exact MetricSpaceCompletion.extended_isometry_is_continuous
    (S := cyclicSet T₁) (dense_cyclicSet T₁) (cyclicMap T₁ T₂) (cyclicMap_isometry T₁ T₂)

private lemma isometry_extendCyclicMap (T₁ T₂ : Representation ω) :
    Isometry (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) := by
  unfold extendCyclicMap
  exact MetricSpaceCompletion.extended_isometry_is_isometry
    (S := cyclicSet T₁) (dense_cyclicSet T₁) (cyclicMap T₁ T₂) (cyclicMap_isometry T₁ T₂)

private lemma extendCyclicMap_eq (T₁ T₂ : Representation ω) (x : cyclicSet T₁) :
    extendCyclicMap (T₁ := T₁) (T₂ := T₂) (x : T₁.H) = cyclicMap T₁ T₂ x := by
  unfold extendCyclicMap
  simpa using
    MetricSpaceCompletion.extended_isometry_is_induced
      (S := cyclicSet T₁) (dense_cyclicSet T₁)
      (cyclicMap T₁ T₂) (cyclicMap_isometry T₁ T₂) x

private lemma extend_cyclic_map_left_inv (T₁ T₂ : Representation ω) :
    ∀ x : T₁.H,
      (extendCyclicMap (T₁ := T₂) (T₂ := T₁)) ((extendCyclicMap (T₁ := T₁) (T₂ := T₂)) x) = x := by
  intro x
  set U_fun := extendCyclicMap (T₁ := T₁) (T₂ := T₂)
  set V_fun := extendCyclicMap (T₁ := T₂) (T₂ := T₁)
  have hx' : x ∈ closure (cyclicSet T₁) :=
    (dense_cyclicSet T₁).closure_eq ▸ (show x ∈ Set.univ from trivial)
  refine (isClosed_eq
    ((continuous_extendCyclicMap (T₁ := T₂) (T₂ := T₁)).comp
      (continuous_extendCyclicMap (T₁ := T₁) (T₂ := T₂)))
    continuous_id).closure_subset_iff.mpr ?_ hx'
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_cyclic_set_iff T₁ z).mp hz
  have hx₁ : T₁.π a T₁.ξ ∈ cyclicSet T₁ := mem_cyclicSet (T := T₁) a
  have hx₂ : T₂.π a T₂.ξ ∈ cyclicSet T₂ := mem_cyclicSet (T := T₂) a
  have hU : U_fun (T₁.π a T₁.ξ) = T₂.π a T₂.ξ := by
    simpa [U_fun] using (extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨T₁.π a T₁.ξ, hx₁⟩).trans
      (cyclicMap_well_defined T₁ T₂ ⟨T₁.π a T₁.ξ, hx₁⟩ a rfl)
  have hV : V_fun (T₂.π a T₂.ξ) = T₁.π a T₁.ξ := by
    simpa [V_fun] using (extendCyclicMap_eq (T₁ := T₂) (T₂ := T₁) ⟨T₂.π a T₂.ξ, hx₂⟩).trans
      (cyclicMap_well_defined T₂ T₁ ⟨T₂.π a T₂.ξ, hx₂⟩ a rfl)
  calc
    V_fun (U_fun (T₁.π a T₁.ξ))
        = V_fun (T₂.π a T₂.ξ) := by simp [hU]
      _ = T₁.π a T₁.ξ := hV

private lemma extend_cyclic_map_right_inv (T₁ T₂ : Representation ω) :
    ∀ y : T₂.H,
      (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) ((extendCyclicMap (T₁ := T₂) (T₂ := T₁)) y) = y := by
  intro y
  set U_fun := extendCyclicMap (T₁ := T₁) (T₂ := T₂)
  set V_fun := extendCyclicMap (T₁ := T₂) (T₂ := T₁)
  have hy' : y ∈ closure (cyclicSet T₂) :=
    (dense_cyclicSet T₂).closure_eq ▸ (show y ∈ Set.univ from trivial)
  refine (isClosed_eq
    ((continuous_extendCyclicMap (T₁ := T₁) (T₂ := T₂)).comp
      (continuous_extendCyclicMap (T₁ := T₂) (T₂ := T₁)))
    continuous_id).closure_subset_iff.mpr ?_ hy'
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_cyclic_set_iff T₂ z).mp hz
  have hx₁ : T₁.π a T₁.ξ ∈ cyclicSet T₁ := mem_cyclicSet (T := T₁) a
  have hx₂ : T₂.π a T₂.ξ ∈ cyclicSet T₂ := mem_cyclicSet (T := T₂) a
  have hV : V_fun (T₂.π a T₂.ξ) = T₁.π a T₁.ξ := by
    simpa [V_fun] using (extendCyclicMap_eq (T₁ := T₂) (T₂ := T₁) ⟨T₂.π a T₂.ξ, hx₂⟩).trans
      (cyclicMap_well_defined T₂ T₁ ⟨T₂.π a T₂.ξ, hx₂⟩ a rfl)
  have hU : U_fun (T₁.π a T₁.ξ) = T₂.π a T₂.ξ := by
    simpa [U_fun] using (extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨T₁.π a T₁.ξ, hx₁⟩).trans
      (cyclicMap_well_defined T₁ T₂ ⟨T₁.π a T₁.ξ, hx₁⟩ a rfl)
  calc
    U_fun (V_fun (T₂.π a T₂.ξ))
        = U_fun (T₁.π a T₁.ξ) := by simp [hV]
      _ = T₂.π a T₂.ξ := hU

private lemma extend_cyclic_map_add (T₁ T₂ : Representation ω) :
    ∀ x y : T₁.H, (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) (x + y) =
      (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) x + (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) y := by
  set U_fun := extendCyclicMap (T₁ := T₁) (T₂ := T₂)
  refine Continuous.add_dense_subset_to_everywhere (dense_cyclicSet T₁) U_fun
    (continuous_extendCyclicMap (T₁ := T₁) (T₂ := T₂)) ?_
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (mem_cyclic_set_iff T₁ x).mp hx
  obtain ⟨b, rfl⟩ := (mem_cyclic_set_iff T₁ y).mp hy
  have hx₁ : T₁.π (a + b) T₁.ξ ∈ cyclicSet T₁ := mem_cyclicSet (T := T₁) (a + b)
  have hUab : U_fun (T₁.π (a + b) T₁.ξ) = T₂.π (a + b) T₂.ξ := by
    simpa [U_fun] using (extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨_, hx₁⟩).trans
      (cyclicMap_well_defined T₁ T₂ ⟨_, hx₁⟩ (a + b) rfl)
  have hUa : U_fun (T₁.π a T₁.ξ) = T₂.π a T₂.ξ := by
    simpa [U_fun] using (extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨_, mem_cyclicSet (T := T₁) a⟩).trans
      (cyclicMap_well_defined T₁ T₂ ⟨_, mem_cyclicSet (T := T₁) a⟩ a rfl)
  have hUb : U_fun (T₁.π b T₁.ξ) = T₂.π b T₂.ξ := by
    simpa [U_fun] using (extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨_, mem_cyclicSet (T := T₁) b⟩).trans
      (cyclicMap_well_defined T₁ T₂ ⟨_, mem_cyclicSet (T := T₁) b⟩ b rfl)
  calc U_fun (T₁.π a T₁.ξ + T₁.π b T₁.ξ)
      = U_fun ((T₁.π a + T₁.π b) T₁.ξ) := by rw [add_apply]
    _ = U_fun (T₁.π (a + b) T₁.ξ) := by
        rw [show T₁.π (a + b) = T₁.π a + T₁.π b from T₁.π.map_add' a b]
    _ = T₂.π (a + b) T₂.ξ := hUab
    _ = (T₂.π a + T₂.π b) T₂.ξ := by
        rw [show T₂.π (a + b) = T₂.π a + T₂.π b from T₂.π.map_add' a b]
    _ = T₂.π a T₂.ξ + T₂.π b T₂.ξ := by rw [add_apply]
    _ = U_fun (T₁.π a T₁.ξ) + U_fun (T₁.π b T₁.ξ) := by rw [← hUa, ← hUb]

private lemma extend_cyclic_map_smul (T₁ T₂ : Representation ω) :
    ∀ (c : ℂ) (x : T₁.H), (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) (c • x) =
      c • (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) x := by
  set U_fun := extendCyclicMap (T₁ := T₁) (T₂ := T₂)
  refine Continuous.smul_dense_subset_to_everywhere (dense_cyclicSet T₁) U_fun
    (continuous_extendCyclicMap (T₁ := T₁) (T₂ := T₂)) ?_
  intro c x hx
  obtain ⟨a, rfl⟩ := (mem_cyclic_set_iff T₁ x).mp hx
  have hx₁ : T₁.π (c • a) T₁.ξ ∈ cyclicSet T₁ := mem_cyclicSet (T := T₁) (c • a)
  have hU1 : U_fun (T₁.π (c • a) T₁.ξ) = T₂.π (c • a) T₂.ξ := by
    simpa [U_fun] using (extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨_, hx₁⟩).trans
      (cyclicMap_well_defined T₁ T₂ ⟨_, hx₁⟩ (c • a) rfl)
  have hUa : U_fun (T₁.π a T₁.ξ) = T₂.π a T₂.ξ := by
    simpa [U_fun] using (extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨_, mem_cyclicSet (T := T₁) a⟩).trans
      (cyclicMap_well_defined T₁ T₂ ⟨_, mem_cyclicSet (T := T₁) a⟩ a rfl)
  change U_fun (c • T₁.π a T₁.ξ) = c • U_fun (T₁.π a T₁.ξ)
  calc U_fun (c • T₁.π a T₁.ξ)
      = U_fun ((c • T₁.π a) T₁.ξ) := rfl
    _ = U_fun ((T₁.π (c • a)) T₁.ξ) := by
        rw [show T₁.π (c • a) = c • T₁.π a from T₁.π.map_smul' c a]
    _ = T₂.π (c • a) T₂.ξ := hU1
    _ = (c • T₂.π a) T₂.ξ := by rw [show T₂.π (c • a) = c • T₂.π a from T₂.π.map_smul' c a]
    _ = c • T₂.π a T₂.ξ := rfl
    _ = c • U_fun (T₁.π a T₁.ξ) := congrArg (c • ·) hUa.symm

/-- The linear isometry equivalence `U : T₁.H ≃ₗᵢ[ℂ] T₂.H` obtained by extending the map
`π₁(a) ξ₁ ↦ π₂(a) ξ₂` from the dense cyclic subset to the whole Hilbert space. -/
private noncomputable def cyclicIsometry (T₁ T₂ : Representation ω) : T₁.H ≃ₗᵢ[ℂ] T₂.H := by
  let U_fun := extendCyclicMap (T₁ := T₁) (T₂ := T₂)
  let V_fun := extendCyclicMap (T₁ := T₂) (T₂ := T₁)
  have h_UV := extend_cyclic_map_left_inv T₁ T₂
  have h_VU := extend_cyclic_map_right_inv T₁ T₂
  have h_add := extend_cyclic_map_add T₁ T₂
  have h_smul := extend_cyclic_map_smul T₁ T₂
  let U_equiv : T₁.H ≃ₗ[ℂ] T₂.H :=
    { toFun := U_fun, invFun := V_fun, left_inv := h_UV, right_inv := h_VU,
      map_add' := h_add, map_smul' := h_smul }
  have h_norm_map : ∀ x : T₁.H, ‖U_fun x‖ = ‖x‖ := by
    intro x
    have h_zero : U_fun 0 = 0 := by
      calc U_fun 0
          = U_fun (0 • (0 : T₁.H)) := by simp
        _ = 0 • U_fun (0 : T₁.H) := h_smul 0 0
        _ = 0 := by simp
    have := (isometry_extendCyclicMap (T₁ := T₁) (T₂ := T₂)).dist_eq x 0
    simpa [U_fun, dist_eq_norm, h_zero] using this
  exact U_equiv.isometryOfInner fun x y ↦
    ({ toLinearMap := U_equiv.toLinearMap, norm_map' := h_norm_map } :
        T₁.H →ₗᵢ[ℂ] T₂.H).inner_map_map x y

/-- On cyclic orbit vectors, `cyclicIsometry` agrees with the expected correspondence. -/
private lemma cyclicIsometry_apply (T₁ T₂ : Representation ω) (a : A) :
  (cyclicIsometry T₁ T₂ : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ := by
  -- The underlying linear map of `cyclicIsometry` is constructed from `extendCyclicMap`.
  have hx : T₁.π a T₁.ξ ∈ cyclicSet T₁ := mem_cyclicSet (T := T₁) a
  conv_lhs =>
    arg 1
    rw [show (cyclicIsometry T₁ T₂ : T₁.H →L[ℂ] T₂.H) =
      (cyclicIsometry T₁ T₂).toLinearIsometry.toContinuousLinearMap from rfl]
  -- The toFun of the `LinearIsometryEquiv` is `extendCyclicMap`.
  change extendCyclicMap (T₁ := T₁) (T₂ := T₂) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ
  rw [extendCyclicMap_eq (T₁ := T₁) (T₂ := T₂) ⟨T₁.π a T₁.ξ, hx⟩]
  exact cyclicMap_well_defined T₁ T₂ ⟨T₁.π a T₁.ξ, hx⟩ a rfl

/-- GNS representations of a fixed state are unique up to unitary equivalence.

Given two GNS triplets `(π₁, H₁, ξ₁)` and `(π₂, H₂, ξ₂)` for the same state `ω`, there exists a
unitary equivalence `U : T₁ ≃ᵁ T₂` sending the cyclic vector of the first representation to that of
the second and intertwining the two *-representations. In particular, every GNS triplet is
unitarily equivalent to the canonical construction, and any two triplets are unitarily equivalent. -/
theorem unique_up_to_unitary_equivalence :
    ∀ T₁ T₂ : Representation ω, Nonempty (T₁ ≃ᵁ T₂) := by
  intro T₁ T₂
  let Uiso := cyclicIsometry T₁ T₂
  have hU_cyclic_iso : ∀ a : A, (Uiso : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ :=
  fun a => cyclicIsometry_apply T₁ T₂ a
  exact ⟨{ toLinearIsometryEquiv := Uiso
           map_cyclic_vector := linear_isometry_equiv_map_cyclic_vector T₁ T₂ Uiso hU_cyclic_iso
           intertwines := linear_isometry_equiv_intertwines T₁ T₂ Uiso hU_cyclic_iso }⟩

/-- The canonical GNS triplet `(𝓗[ω], π[ω], ξ[ω])` produced by the GNS construction
(`State.gnsSpace`, `State.gnsRep`, `State.gnsVector`). -/
noncomputable def canonical : Representation ω where
  H := 𝓗[ω]
  π := π[ω]
  ξ := ξ[ω]
  cyclic := ω.gnsVector_cyclic
  gns_condition := ω.gns_condition

lemma canonical_H : (canonical (ω := ω)).H = 𝓗[ω] := rfl
lemma canonical_π : (canonical (ω := ω)).π = π[ω] := rfl
lemma canonical_ξ : (canonical (ω := ω)).ξ = ξ[ω] := rfl

end Representation

/-- Evaluation of a state along an approximate unit converges to `1`: `ω e_α → 1`. -/
theorem _root_.State.tendsto_approximateUnit {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) :
    Filter.Tendsto (fun e : A => ω e) (CStarAlgebra.approximateUnit A) (nhds 1) :=
  (Representation.canonical (ω := ω)).tendsto_apply_approximateUnit

end GNS
