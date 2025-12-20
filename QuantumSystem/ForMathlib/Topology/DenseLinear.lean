module

public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace Continuous

variable {α : Type*} [TopologicalSpace α]
variable {β : Type*} [TopologicalSpace β] [T2Space β]
variable {S : Set α}

section AddSection

variable [AddCommGroup α] [ContinuousAdd α]
variable [AddCommGroup β] [ContinuousAdd β]

/-- A continuous function additive on a dense subset is additive everywhere. -/
lemma add_dense_subset_to_everywhere (hs : Dense S) (f : α → β) (hf : Continuous f)
    (h_add_on : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x + f y) :
    ∀ x y : α, f (x + y) = f x + f y := by
  intros x y
  -- The set where additivity holds is closed
  have h_closed : IsClosed {p : α × α | f (p.1 + p.2) = f p.1 + f p.2} := by
    have h_lhs : Continuous (fun p : α × α => f (p.1 + p.2)) :=
      hf.comp (continuous_fst.add continuous_snd)
    have h_rhs : Continuous (fun p : α × α => f p.1 + f p.2) :=
      (hf.comp continuous_fst).add (hf.comp continuous_snd)
    exact isClosed_eq h_lhs h_rhs
  -- The property holds on the dense product
  have h_dense_prod : Dense (S ×ˢ S) := hs.prod hs
  have h_on_dense : S ×ˢ S ⊆ {p : α × α | f (p.1 + p.2) = f p.1 + f p.2} :=
    fun ⟨a, b⟩ ⟨ha, hb⟩ => h_add_on a ha b hb
  -- Therefore it holds everywhere
  have : (x, y) ∈ {p : α × α | f (p.1 + p.2) = f p.1 + f p.2} :=
    h_closed.closure_subset_iff.mpr h_on_dense (by rw [h_dense_prod.closure_eq]; trivial)
  exact this

end AddSection

section SMulSection

variable [SMul ℂ α] [ContinuousSMul ℂ α]
variable [SMul ℂ β] [ContinuousSMul ℂ β]

/-- A continuous function scalar-multiplicative on a dense subset is scalar-multiplicative everywhere. -/
lemma smul_dense_subset_to_everywhere (hs : Dense S) (f : α → β) (hf : Continuous f)
    (h_smul_on : ∀ c : ℂ, ∀ x ∈ S, f (c • x) = c • f x) :
    ∀ c : ℂ, ∀ x : α, f (c • x) = c • f x := by
  intros c x
  -- For fixed c, use closure on the dense set s
  have h_closed : IsClosed {z : α | f (c • z) = c • f z} := by
    have h_lhs : Continuous (fun z => f (c • z)) := hf.comp (continuous_const.smul continuous_id)
    have h_rhs : Continuous (fun z => c • f z) := continuous_const.smul hf
    exact isClosed_eq h_lhs h_rhs
  have h_on_dense : S ⊆ {z : α | f (c • z) = c • f z} :=
    fun z hz => h_smul_on c z hz
  have : x ∈ {z : α | f (c • z) = c • f z} :=
    h_closed.closure_subset_iff.mpr h_on_dense (hs x)
  exact this

end SMulSection

section LinearSection

variable [AddCommGroup α] [ContinuousAdd α] [SMul ℂ α][ContinuousSMul ℂ α]
variable [AddCommGroup β] [ContinuousAdd β] [SMul ℂ β] [ContinuousSMul ℂ β]

/-- A continuous function linear on a dense subset is linear everywhere. -/
lemma linear_dense_subset_to_everywhere  (hs : Dense S) (f : α → β) (hf : Continuous f)
    (h_add : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x + f y)
    (h_smul : ∀ c : ℂ, ∀ x ∈ S, f (c • x) = c • f x) :
    (∀ x y : α, f (x + y) = f x + f y) ∧ (∀ c : ℂ, ∀ x : α, f (c • x) = c • f x) :=
  ⟨add_dense_subset_to_everywhere hs f hf h_add, smul_dense_subset_to_everywhere hs f hf h_smul⟩

end LinearSection

end Continuous
