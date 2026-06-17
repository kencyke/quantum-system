module

public import QuantumSystem.Algebra.LocalNet.Isotony

/-!
# Locality (Einstein causality) of the local net

Observables localised in **disjoint** regions commute. For finite-dimensional spin systems this
is the concrete realisation of the AQFT locality axiom (Naaijkens 2012 §3.2: spacelike-separated
— here disjoint — regions commute; Verch 2025 §1.2). The proof reduces to the union region
`Λ₁ ∪ Λ₂`, where the two embeddings act on complementary tensor factors, and ultimately to
commutativity of the scalar matrix entries in `ℂ`.
-/

@[expose] public section

namespace LocalNet

variable (L : LocalNet)

/-- The right-region embedding `𝔄(Λ₂) ↪ 𝔄(Λ₁ ∪ Λ₂)` evaluated at indices factored through
    the *left* split `combineIdx (Λ₁ ⊆ Λ₁ ∪ Λ₂)`: since `Λ₁` and `Λ₂` are disjoint, the
    complement `(Λ₁ ∪ Λ₂) \ Λ₁` is exactly `Λ₂`, so the value is `Y` on the complementary
    coordinate, with the diagonal condition now living on the `Λ₁` coordinate. -/
private lemma includeAlgebra_union_right_combineIdx_left
    {Λ₁ Λ₂ : Finset L.sites} (hd : Disjoint Λ₁ Λ₂) (Y : L.localAlgebra Λ₂)
    (a a' : L.regionIdx Λ₁) (b b' : L.regionIdx ((Λ₁ ∪ Λ₂) \ Λ₁)) :
    L.includeAlgebra Finset.subset_union_right Y
        (L.combineIdx Finset.subset_union_left (a, b))
        (L.combineIdx Finset.subset_union_left (a', b'))
      = if a = a' then
          Y (L.regionIdxCongr (Finset.union_sdiff_cancel_left hd) b)
            (L.regionIdxCongr (Finset.union_sdiff_cancel_left hd) b') else 0 := by
  have hcompl : (Λ₁ ∪ Λ₂) \ Λ₁ = Λ₂ := Finset.union_sdiff_cancel_left hd
  -- The `Λ₂`-coordinate (first projection under `combineIdx Λ₂⊆U`) of a left-combined index
  -- is the complement coordinate, transported along `hcompl`.
  have hdR : ∀ (c : L.regionIdx Λ₁) (d : L.regionIdx ((Λ₁ ∪ Λ₂) \ Λ₁)),
      ((L.combineIdx Finset.subset_union_right).symm
          (L.combineIdx Finset.subset_union_left (c, d))).1
        = L.regionIdxCongr hcompl d := by
    intro c d
    funext w
    obtain ⟨wv, wp⟩ := w
    have hw1 : wv ∉ Λ₁ := fun hh => (Finset.disjoint_left.mp hd hh) wp
    change L.combineIdx Finset.subset_union_left (c, d)
          ⟨wv, Finset.subset_union_right wp⟩ = _
    rw [combineIdx_apply_not_mem Finset.subset_union_left c d ⟨wv, _⟩ hw1,
      L.regionIdxCongr_apply hcompl d
        (Finset.mem_sdiff.mpr ⟨Finset.subset_union_right wp, hw1⟩) wp]
  -- The `(U\Λ₂)`-coordinate (second projection under `combineIdx Λ₂⊆U`) only sees `Λ₁`,
  -- transported along `(Λ₁ ∪ Λ₂) \ Λ₂ = Λ₁`.
  have hcR : ∀ (c : L.regionIdx Λ₁) (d : L.regionIdx ((Λ₁ ∪ Λ₂) \ Λ₁)),
      ((L.combineIdx Finset.subset_union_right).symm
          (L.combineIdx Finset.subset_union_left (c, d))).2
        = L.regionIdxCongr (Finset.union_sdiff_cancel_right hd).symm c := by
    intro c d
    funext w
    obtain ⟨wv, wp⟩ := w
    have hwU : wv ∈ Λ₁ ∪ Λ₂ := (Finset.mem_sdiff.mp wp).1
    have hw1 : wv ∈ Λ₁ := by
      rcases Finset.mem_union.mp hwU with h | h
      · exact h
      · exact absurd h (Finset.mem_sdiff.mp wp).2
    change L.combineIdx Finset.subset_union_left (c, d) ⟨wv, hwU⟩ = _
    rw [combineIdx_apply_mem Finset.subset_union_left c d ⟨wv, hwU⟩ hw1,
      L.regionIdxCongr_apply (Finset.union_sdiff_cancel_right hd).symm c hw1 wp]
  have hcond : (((L.combineIdx Finset.subset_union_right).symm
          (L.combineIdx Finset.subset_union_left (a, b))).2
        = ((L.combineIdx Finset.subset_union_right).symm
          (L.combineIdx Finset.subset_union_left (a', b'))).2) ↔ a = a' := by
    rw [hcR a b, hcR a' b']
    exact (L.regionIdxCongr (Finset.union_sdiff_cancel_right hd).symm).apply_eq_iff_eq
  rw [includeAlgebra_apply, hdR a b, hdR a' b']
  simp only [hcond]

/-- **Bipartite locality**: in the union region `Λ₁ ∪ Λ₂` of two disjoint regions, a
    `Λ₁`-observable and a `Λ₂`-observable commute. The two embeddings act on complementary
    tensor factors, so the matrix entries collapse to commuting scalar products in `ℂ`. -/
private lemma includeAlgebra_commute_union {Λ₁ Λ₂ : Finset L.sites} (hd : Disjoint Λ₁ Λ₂)
    (X : L.localAlgebra Λ₁) (Y : L.localAlgebra Λ₂) :
    Commute (L.includeAlgebra Finset.subset_union_left X)
            (L.includeAlgebra Finset.subset_union_right Y) := by
  suffices h : L.includeAlgebra Finset.subset_union_left X *
      L.includeAlgebra Finset.subset_union_right Y =
    L.includeAlgebra Finset.subset_union_right Y *
      L.includeAlgebra Finset.subset_union_left X from h
  ext s s'
  obtain ⟨⟨a, b⟩, rfl⟩ := (L.combineIdx Finset.subset_union_left).surjective s
  obtain ⟨⟨a', b'⟩, rfl⟩ := (L.combineIdx Finset.subset_union_left).surjective s'
  rw [Matrix.mul_apply, Matrix.mul_apply,
    ← (L.combineIdx Finset.subset_union_left).sum_comp
      (fun t => L.includeAlgebra Finset.subset_union_left X
          (L.combineIdx Finset.subset_union_left (a, b)) t *
        L.includeAlgebra Finset.subset_union_right Y t
          (L.combineIdx Finset.subset_union_left (a', b'))),
    ← (L.combineIdx Finset.subset_union_left).sum_comp
      (fun t => L.includeAlgebra Finset.subset_union_right Y
          (L.combineIdx Finset.subset_union_left (a, b)) t *
        L.includeAlgebra Finset.subset_union_left X t
          (L.combineIdx Finset.subset_union_left (a', b'))),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [includeAlgebra_apply_combineIdx,
    L.includeAlgebra_union_right_combineIdx_left hd,
    ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **Locality / Einstein causality (spin systems)**: observables localised in disjoint
    regions commute inside any common total region. The finite-dimensional concrete form of
    the AQFT locality axiom (Naaijkens 2012 §3.2; Verch 2025 §1.2). Reduces to the bipartite
    case via functoriality (`includeAlgebra_trans_apply`) and the ring-hom property of the
    embedding into the union. -/
theorem includeAlgebra_commute_of_disjoint {Λ₁ Λ₂ Λ_total : Finset L.sites}
    (h₁ : Λ₁ ⊆ Λ_total) (h₂ : Λ₂ ⊆ Λ_total) (hd : Disjoint Λ₁ Λ₂)
    (X : L.localAlgebra Λ₁) (Y : L.localAlgebra Λ₂) :
    Commute (L.includeAlgebra h₁ X) (L.includeAlgebra h₂ Y) := by
  have hU : Λ₁ ∪ Λ₂ ⊆ Λ_total := Finset.union_subset h₁ h₂
  have e1 : L.includeAlgebra h₁ X
      = L.includeAlgebra hU (L.includeAlgebra Finset.subset_union_left X) := by
    rw [includeAlgebra_trans_apply]
  have e2 : L.includeAlgebra h₂ Y
      = L.includeAlgebra hU (L.includeAlgebra Finset.subset_union_right Y) := by
    rw [includeAlgebra_trans_apply]
  rw [e1, e2]
  exact (L.includeAlgebra_commute_union hd X Y).map (L.includeAlgebra hU)

end LocalNet
