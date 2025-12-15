import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace MetricSpaceCompletion

open Set

variable {X : Type*} [PseudoMetricSpace X]
variable {Y : Type*} [PseudoMetricSpace Y]
variable {S : Set X}

/-- Extension of an isometry from a dense subset to the whole space. -/
noncomputable def extend_dense [CompleteSpace Y] (hs : Dense S) (f : S → Y) : X → Y :=
  hs.extend f

/-- The extension of an isometry from a dense subset is continuous. -/
lemma extended_isometry_is_continuous [CompleteSpace Y] [T2Space Y] (hs : Dense S) (f : S → Y) (hf : Isometry f) :
    Continuous (extend_dense hs f) := by
  unfold extend_dense
  apply hs.continuous_extend
  intro a
  exact hs.extend_exists (Isometry.uniformContinuous hf) a

/-- The extension agrees with the original isometry on the dense subset. -/
lemma extended_isometry_is_induced [CompleteSpace Y] [T2Space Y] (hs : Dense S) (f : S → Y) (hf : Isometry f) (x : S) :
    extend_dense hs f x.val = f x := by
  unfold extend_dense
  exact hs.extend_of_ind (Isometry.uniformContinuous hf) x

/-- The extension of an isometry is itself an isometry. -/
lemma extended_isometry_is_isometry [CompleteSpace Y] [T2Space Y] (hs : Dense S) (f : S → Y) (hf : Isometry f) :
    Isometry (extend_dense hs f) := by
  intro x y
  -- The set of pairs where distance is preserved is closed
  have h_closed : IsClosed {p : X × X | edist (extend_dense hs f p.1)
                                              (extend_dense hs f p.2) = edist p.1 p.2} := by
    have h_cont1 : Continuous (fun p : X × X => edist (extend_dense hs f p.1) (extend_dense hs f p.2)) :=
      ((extended_isometry_is_continuous hs f hf).comp continuous_fst).edist
        ((extended_isometry_is_continuous hs f hf).comp continuous_snd)
    have h_cont2 : Continuous (fun p : X × X => edist p.1 p.2) := continuous_edist
    exact isClosed_eq h_cont1 h_cont2
  -- Distance preservation holds on the dense subset s × s
  have h_on_dense : ∀ x₁ x₂ : X, x₁ ∈ S → x₂ ∈ S →
      edist (extend_dense hs f x₁) (extend_dense hs f x₂) = edist x₁ x₂ := by
    intros x₁ x₂ hx₁ hx₂
    rw [extended_isometry_is_induced hs f hf ⟨x₁, hx₁⟩, extended_isometry_is_induced hs f hf ⟨x₂, hx₂⟩]
    exact hf.edist_eq ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  -- s × s is dense in X × X
  have h_prod_dense : Dense (S ×ˢ S) := hs.prod hs
  -- (x, y) is in the closure of s × s
  have h_xy_mem : (x, y) ∈ closure (S ×ˢ S) := by
    rw [h_prod_dense.closure_eq]
    trivial
  -- The property holds on the closure
  have : (x, y) ∈ {p : X × X | edist (extend_dense hs f p.1) (extend_dense hs f p.2) = edist p.1 p.2} := by
    apply h_closed.closure_subset_iff.mpr _ h_xy_mem
    intro ⟨a, b⟩ hab
    simp only [mem_prod] at hab
    exact h_on_dense a b hab.1 hab.2
  exact this

end MetricSpaceCompletion
