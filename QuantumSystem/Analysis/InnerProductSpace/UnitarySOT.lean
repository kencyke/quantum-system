/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import QuantumSystem.ForMathlib.Analysis.LocallyConvex.StrongOperatorTopology
public import QuantumSystem.ForMathlib.Topology.MetricSpace.PointwiseIsometry

/-!
# The unitary group with the strong operator topology

The unitary group of a Hilbert space with the strong operator topology is a topological group
(`UnitarySOT.instIsTopologicalGroup`). Mathlib's `unitary (H →L[𝕜] H)` carries the norm topology,
and Mathlib's type copy `H →Lₚₜ[𝕜] H` of the operators with the topology of pointwise convergence
has no multiplication, so this needs a type copy of its own, `UnitarySOT 𝕜 H`, whose topology is
induced by `u ↦ ↑ₚₜ u`. A continuous homomorphism `G →ₜ* UnitarySOT ℂ H` is a strongly continuous
unitary representation of `G`. The unitaries act on `H` by isometries, so the group structure is
continuous by the results of `QuantumSystem.ForMathlib.Topology.MetricSpace.PointwiseIsometry`.

## Main definitions

* `UnitarySOT 𝕜 H`: the unitary group of `H` with the strong operator topology.

## Main results

* `UnitarySOT.tendsto_iff`, `UnitarySOT.continuous_iff`: a family of unitaries converges iff it
  converges at every vector, and a map `f` into `UnitarySOT 𝕜 H` is continuous iff `x ↦ f x y` is
  continuous for every vector `y`.
* **`UnitarySOT.instIsTopologicalGroup`**: the unitary group is a topological group in the strong
  operator topology.
-/

@[expose] public section

/-! ### The unitary group with the strong operator topology -/

noncomputable section UnitarySOT

open Filter Topology
open scoped StrongOperatorTopology

variable (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The **unitary group** `unitary (H →L[𝕜] H)` of a Hilbert space with the **strong operator
topology**: a type copy of Mathlib's `unitary (H →L[𝕜] H)`, which carries the norm topology. A net of
unitaries converges to `u` iff it converges to `u` at every vector (`UnitarySOT.tendsto_iff`). -/
def UnitarySOT : Type _ := unitary (H →L[𝕜] H)

namespace UnitarySOT

variable {𝕜 H}

/-- The group structure of the unitary group. -/
instance instGroup : Group (UnitarySOT 𝕜 H) := inferInstanceAs (Group (unitary (H →L[𝕜] H)))

variable (𝕜 H) in
/-- The identification of the unitary group with its copy carrying the strong operator topology. -/
def ofUnitary : unitary (H →L[𝕜] H) ≃* UnitarySOT 𝕜 H := MulEquiv.refl _

/-- The operator underlying an element of `UnitarySOT 𝕜 H`. -/
@[coe] def toCLM (u : UnitarySOT 𝕜 H) : H →L[𝕜] H :=
  ((ofUnitary 𝕜 H).symm u : unitary (H →L[𝕜] H))

/-- An element of `UnitarySOT 𝕜 H` is coerced to its underlying operator. -/
instance : CoeOut (UnitarySOT 𝕜 H) (H →L[𝕜] H) := ⟨toCLM⟩

/-- A unitary is applied to a vector through its operator: `u y` is notation for
`(u : H →L[𝕜] H) y`, and elaborates to it. -/
instance : CoeFun (UnitarySOT 𝕜 H) fun _ => H → H := ⟨fun u => (u : H →L[𝕜] H)⟩

/-- The strong operator topology on the unitary group, induced by `u ↦ ↑ₚₜ u` into Mathlib's type
copy `H →Lₚₜ[𝕜] H` of the operators with the topology of pointwise convergence. -/
instance instTopologicalSpace : TopologicalSpace (UnitarySOT 𝕜 H) :=
  .induced (fun u : UnitarySOT 𝕜 H => ↑ₚₜ (u : H →L[𝕜] H)) inferInstance

/-- The underlying operator of an element of `UnitarySOT 𝕜 H` is unitary. -/
lemma coe_mem (u : UnitarySOT 𝕜 H) : (u : H →L[𝕜] H) ∈ unitary (H →L[𝕜] H) :=
  ((ofUnitary 𝕜 H).symm u).2

/-- Elements of `UnitarySOT 𝕜 H` with the same underlying operator are equal. -/
@[ext] lemma ext {u v : UnitarySOT 𝕜 H} (h : (u : H →L[𝕜] H) = v) : u = v :=
  Subtype.ext h

/-- The product of unitaries is the product of their operators. -/
@[simp] lemma coe_mul (u v : UnitarySOT 𝕜 H) : ((u * v : UnitarySOT 𝕜 H) : H →L[𝕜] H) = u * v :=
  rfl

/-- The unit of the unitary group is the identity operator. -/
@[simp] lemma coe_one : ((1 : UnitarySOT 𝕜 H) : H →L[𝕜] H) = 1 :=
  rfl

/-- The inverse of a unitary is its adjoint. -/
@[simp] lemma coe_inv (u : UnitarySOT 𝕜 H) :
    ((u⁻¹ : UnitarySOT 𝕜 H) : H →L[𝕜] H) = star (u : H →L[𝕜] H) :=
  rfl

/-- The identification `ofUnitary` does not change the operator. -/
@[simp] lemma coe_ofUnitary (u : unitary (H →L[𝕜] H)) :
    ((ofUnitary 𝕜 H u : UnitarySOT 𝕜 H) : H →L[𝕜] H) = u :=
  rfl

variable (𝕜 H) in
/-- The underlying operators of the unitary group, as a homomorphism into the operators. -/
def coeHom : UnitarySOT 𝕜 H →* (H →L[𝕜] H) :=
  (unitary (H →L[𝕜] H)).subtype.comp (ofUnitary 𝕜 H).symm.toMonoidHom

/-- `coeHom` is the coercion to operators. -/
@[simp] lemma coeHom_apply (u : UnitarySOT 𝕜 H) : coeHom 𝕜 H u = u :=
  rfl

/-- A unitary preserves norms. -/
lemma norm_apply (u : UnitarySOT 𝕜 H) (y : H) : ‖u y‖ = ‖y‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary u.coe_mem y

/-- A family of unitaries converges to `u` in the strong operator topology iff it converges to `u`
at every vector. -/
lemma tendsto_iff {ι : Type*} {l : Filter ι} {f : ι → UnitarySOT 𝕜 H} {u : UnitarySOT 𝕜 H} :
    Tendsto f l (𝓝 u) ↔ ∀ y, Tendsto (fun x => f x y) l (𝓝 (u y)) := by
  rw [nhds_induced, tendsto_comap_iff]
  exact PointwiseConvergenceCLM.tendsto_iff_forall_tendsto

variable {X : Type*} [TopologicalSpace X]

/-- A map into the unitary group is continuous for the strong operator topology iff
`x ↦ f x y` is continuous for every vector `y`. -/
lemma continuous_iff {f : X → UnitarySOT 𝕜 H} :
    Continuous f ↔ ∀ y, Continuous fun x => f x y := by
  refine continuous_induced_rng.trans ⟨fun h y => ?_, fun h =>
    PointwiseConvergenceCLM.continuous_of_continuous_eval fun y => h y⟩
  exact (PointwiseConvergenceCLM.evalCLM (RingHom.id 𝕜) H y).continuous.comp h

/-- Evaluation at a vector is continuous for the strong operator topology. -/
lemma continuous_apply (y : H) : Continuous fun u : UnitarySOT 𝕜 H => u y :=
  continuous_iff.mp continuous_id y

/-- The strong operator topology on the unitary group is induced by `u ↦ (y ↦ u y)` into `H → H`
with the product topology. -/
lemma isInducing_apply : IsInducing fun (u : UnitarySOT 𝕜 H) (y : H) => u y :=
  (PointwiseConvergenceCLM.isEmbedding_coeFn (σ := RingHom.id 𝕜) (E := H) (F := H)).isInducing.comp
    ⟨rfl⟩

/-- A unitary is an isometry. -/
lemma isometry (u : UnitarySOT 𝕜 H) : Isometry fun y => u y :=
  AddMonoidHomClass.isometry_of_norm (u : H →L[𝕜] H) u.norm_apply

/-- **The unitary group is a topological group in the strong operator topology**: it acts on `H` by
isometries (`Topology.IsInducing.isTopologicalGroup_of_isometry`). -/
instance instIsTopologicalGroup : IsTopologicalGroup (UnitarySOT 𝕜 H) :=
  isInducing_apply.isTopologicalGroup_of_isometry isometry (fun _ _ _ => rfl) fun _ => rfl

end UnitarySOT

end UnitarySOT
