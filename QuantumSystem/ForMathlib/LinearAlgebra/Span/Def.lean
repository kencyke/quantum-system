module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs

@[expose] public section

namespace Submodule

lemma span_subset_closure {H : Type*} [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    [ContinuousAdd H] [ContinuousConstSMul ℂ H] {S : Set H} (hS : S.Nonempty)
    (hS_add : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
    (hS_smul : ∀ (c : ℂ) {x}, x ∈ S → c • x ∈ S) :
    ↑(Submodule.span ℂ S) ⊆ closure S := by
  have h0 : (0 : H) ∈ closure S := by
    obtain ⟨s, hs⟩ := hS
    have : (0 : H) = (0 : ℂ) • s := (zero_smul ℂ s).symm
    rw [this]
    have : (0 : ℂ) • s ∈ S := hS_smul 0 hs
    exact subset_closure this
  have hadd : ∀ {x y : H}, x ∈ closure S → y ∈ closure S → x + y ∈ closure S := by
    intro x y hx hy
    have : x + y ∈ closure S := by
      apply map_mem_closure₂ continuous_add hx hy
      exact fun a ha b hb => hS_add ha hb
    exact this
  have hsmul : ∀ (c : ℂ) {x : H}, x ∈ closure S → c • x ∈ closure S := by
    intro c x hx
    have : c • x ∈ closure S := by
      apply map_mem_closure (continuous_const_smul c) hx
      intro y hy
      exact hS_smul c hy
    exact this
  have : CanLift (Set H) (Submodule ℂ H) (↑) (fun s => 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ ∀ (r : ℂ) {x}, x ∈ s → r • x ∈ s) := by infer_instance
  obtain ⟨M, hM⟩ := this.prf (closure S) ⟨h0, hadd, hsmul⟩
  rw [← hM]
  have : S ⊆ ↑M := by rw [hM]; exact subset_closure
  exact SetLike.coe_subset_coe.mpr (Submodule.span_le.mpr this)

end Submodule
