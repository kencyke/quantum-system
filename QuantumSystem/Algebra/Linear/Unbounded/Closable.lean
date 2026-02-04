module

public import QuantumSystem.Algebra.Linear.Unbounded.Adjoint
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closability of Densely Defined Linear Operators

This file develops the theory of closability for densely defined linear operators,
with particular focus on symmetric operators which are always closable.

## Main results

* `DenselyDefinedLinearMap.IsSymmetric.isClosable`: Symmetric operators are closable
* `DenselyDefinedLinearMap.closure`: The closure of a densely defined operator

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reed1980]
-/

@[expose] public section

namespace DenselyDefinedLinearMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Closability -/

/-- A densely defined operator is closable if the closure of its graph is a graph
(i.e., if (0, y) is in the closure of the graph, then y = 0). -/
def IsClosable (T : OnHilbertSpace 𝕜 H) : Prop :=
  LinearPMap.IsClosable T.toLinearPMap

/-- A densely defined operator is closed if its graph is closed. -/
def IsClosed (T : OnHilbertSpace 𝕜 H) : Prop :=
  LinearPMap.IsClosed T.toLinearPMap

/-- Closed operators are closable. -/
theorem IsClosed.isClosable {T : OnHilbertSpace 𝕜 H} (hT : IsClosed T) : IsClosable T :=
  LinearPMap.IsClosed.isClosable hT

/-- A closable operator has a unique minimal closed extension. -/
theorem IsClosable.existsUnique (T : OnHilbertSpace 𝕜 H) (hT : IsClosable T) :
    ∃! T' : LinearPMap 𝕜 H H, (graph T).topologicalClosure = T'.graph :=
  LinearPMap.IsClosable.existsUnique hT

/-! ### Closure -/

/-- The closure of a densely defined operator (if closable, otherwise returns the original). -/
noncomputable def closure (T : OnHilbertSpace 𝕜 H) : LinearPMap 𝕜 H H :=
  LinearPMap.closure T.toLinearPMap

/-- For a closable operator, the closure has the same graph closure. -/
theorem IsClosable.graph_closure_eq {T : OnHilbertSpace 𝕜 H} (hT : IsClosable T) :
    T.graph.topologicalClosure = (closure T).graph :=
  LinearPMap.IsClosable.graph_closure_eq_closure_graph hT

/-- The closure of a closable operator is closed. -/
theorem IsClosable.closure_isClosed {T : OnHilbertSpace 𝕜 H} (hT : IsClosable T) :
    LinearPMap.IsClosed (closure T) :=
  LinearPMap.IsClosable.closure_isClosed hT

/-- The original operator is an extension of its closure (T ≤ T̄). -/
theorem le_closure (T : OnHilbertSpace 𝕜 H) :
    T.toLinearPMap ≤ closure T :=
  LinearPMap.le_closure T.toLinearPMap

/-! ### Symmetric operators are closable -/

section SymmetricClosable

variable [CompleteSpace H]

/-- Key lemma: If T is symmetric and (xₙ, Txₙ) → (0, y) in graph topology,
then y = 0. This is proven using the inner product identity. -/
theorem IsSymmetric.graph_closure_zero_implies_zero {T : OnHilbertSpace 𝕜 H}
    (hT : T.IsSymmetric) {y : H}
    (hy : (⟨0, y⟩ : H × H) ∈ (T.graph.topologicalClosure : Set (H × H))) : y = 0 := by
  -- Use mem_closure_iff_seq_limit (available in first countable/metric spaces)
  rw [Submodule.topologicalClosure_coe, mem_closure_iff_seq_limit] at hy
  rcases hy with ⟨s, hs_graph, hs_lim⟩
  have h_inner_zero : ∀ v : T.dom, @inner 𝕜 H _ y v = 0 := by
    intro v
    have h_cont : Continuous fun p : H × H => @inner 𝕜 H _ p.2 (v : H) :=
      continuous_inner.comp (Continuous.prodMk continuous_snd continuous_const)
    have h_lim : Filter.Tendsto (fun n => @inner 𝕜 H _ (s n).2 (v : H)) Filter.atTop
        (nhds (@inner 𝕜 H _ y v)) := h_cont.seqContinuous hs_lim
    -- The sequence s n is in the graph
    have h_eq : ∀ n, @inner 𝕜 H _ (s n).2 (v : H) = @inner 𝕜 H _ ((s n).1 : H) (T v) := by
      intro n
      have hmem := hs_graph n
      -- Extract from graph membership. Note: graph T = T.toLinearPMap.graph
      unfold graph at hmem
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hmem
      obtain ⟨x, hx1, hx2⟩ := hmem
      rw [← hx1, ← hx2]
      exact hT x v
    -- At limit, RHS → ⟨0, Tv⟩ = 0
    have h_rhs : Filter.Tendsto (fun n => @inner 𝕜 H _ ((s n).1 : H) (T v)) Filter.atTop (nhds 0) := by
      have h_fst_lim : Filter.Tendsto (fun n => (s n).1) Filter.atTop (nhds 0) := by
        have := Prod.tendsto_iff _ _ |>.mp hs_lim
        exact this.1
      have h_cont' : Continuous fun x : H => @inner 𝕜 H _ x (T v) :=
        continuous_inner.comp (Continuous.prodMk continuous_id continuous_const)
      have := h_cont'.continuousAt.tendsto.comp h_fst_lim
      simp only [inner_zero_left] at this
      exact this
    -- The sequences are equal, so limits are equal
    have h_eq' : (fun n => @inner 𝕜 H _ (s n).2 (v : H)) = fun n => @inner 𝕜 H _ ((s n).1 : H) (T v) :=
      funext h_eq
    rw [h_eq'] at h_lim
    exact tendsto_nhds_unique h_lim h_rhs
  -- Now use density of dom(T) to conclude y = 0
  apply inner_eq_zero_of_forall_mem_dense (𝕜 := 𝕜) T.dense_dom
  intro v hv
  have h := h_inner_zero ⟨v, hv⟩
  simp only at h
  -- Need ⟨v, y⟩ = 0, we have ⟨y, v⟩ = 0
  rw [inner_eq_zero_symm]
  exact h

/-- Symmetric operators are closable. -/
theorem IsSymmetric.isClosable {T : OnHilbertSpace 𝕜 H} (hT : T.IsSymmetric) : IsClosable T := by
  rw [IsClosable, LinearPMap.IsClosable]
  -- We need to show there exists f' such that T.toLinearPMap.graph.topologicalClosure = f'.graph
  use (graph T).topologicalClosure.toLinearPMap
  -- Use the simp to unfold definitions
  simp only [graph]
  rw [Submodule.toLinearPMap_graph_eq]
  -- Need to prove: if (x, y) ∈ cl(graph T) and x = 0, then y = 0
  intro x hx hx0
  -- Construct the pair (0, x.2) which is in the closure
  have h : (⟨0, x.2⟩ : H × H) ∈ (T.toLinearPMap.graph.topologicalClosure : Set (H × H)) := by
    have hx' : x ∈ T.toLinearPMap.graph.topologicalClosure := hx
    convert hx' using 1
    ext <;> simp [hx0]
  rw [Submodule.topologicalClosure_coe] at h
  exact IsSymmetric.graph_closure_zero_implies_zero hT h

end SymmetricClosable

/-- The closure of a symmetric operator extends the original operator. -/
theorem IsSymmetric.closure_extends {T : OnHilbertSpace 𝕜 H} [CompleteSpace H]
    (_hT : T.IsSymmetric) : T.toLinearPMap ≤ closure T :=
  le_closure T

/-! ### Essentially self-adjoint operators -/

section EssSelfAdjoint

/-- An operator is essentially self-adjoint if its closure is self-adjoint.
This is important because it means there's a unique self-adjoint extension. -/
def IsEssSelfAdjoint (T : OnHilbertSpace 𝕜 H) : Prop :=
  T.IsSymmetric ∧ (closure T).domain = adjointDomain T

/-- Essentially self-adjoint operators are symmetric. -/
theorem IsEssSelfAdjoint.isSymmetric {T : OnHilbertSpace 𝕜 H}
    (hT : IsEssSelfAdjoint T) : T.IsSymmetric :=
  hT.1

/-- Essentially self-adjoint operators are closable. -/
theorem IsEssSelfAdjoint.isClosable {T : OnHilbertSpace 𝕜 H} [CompleteSpace H]
    (hT : IsEssSelfAdjoint T) : IsClosable T :=
  hT.1.isClosable

end EssSelfAdjoint

end DenselyDefinedLinearMap
