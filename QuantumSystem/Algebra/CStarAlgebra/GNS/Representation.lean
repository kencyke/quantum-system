import QuantumSystem.ForMathlib.LinearAlgebra.Span.Def
import QuantumSystem.ForMathlib.Topology.DenseLinear
import QuantumSystem.ForMathlib.Topology.MetricSpace.Completion
import QuantumSystem.Algebra.CStarAlgebra.GNS.Construction

namespace GNS

/-- A (non‑unital) GNS triplet `(π, H, ξ)` for a state `ω : A → ℂ` on a (possibly non‑unital)
C*-algebra `A`.

Fields:
* `H` : the underlying type of the Hilbert space.
* `[hilbert]` : evidence that `H` is a complex Hilbert space.
* `π : A →⋆ₙₐ[ℂ] 𝓑(H)` : a non‑unital *-representation of `A` on `H`.
* `ξ : H` : a cyclic unit vector.
* `cyclic` : density of the linear span `Submodule.span ℂ { π a ξ | a : A }` in `H`.
* `unit_norm` : normalisation `‖ξ‖ = 1`.
* `gns_condition` : the GNS identity `ω a = ⟪ξ, π a ξ⟫` for every `a : A`.
-/
structure Representation {A} [NonUnitalCStarAlgebra A] (ω : State ℂ A) where
  /-- The Hilbert space of the GNS representation -/
  H : Type*
  /-- The complex Hilbert space structure on H -/
  [hilbert : ComplexHilbertSpace H]
  /-- The representation π : A → 𝓑(H) -/
  π : A →⋆ₙₐ[ℂ] 𝓑(H)
  /-- The cyclic vector ξ ∈ H -/
  ξ : H
  /-- The cyclic property: the span of {π(a)ξ : a ∈ A} is dense in H -/
  cyclic : Dense (↑(Submodule.span ℂ {π a ξ | a : A}) : Set H)
  /-- The unit norm property: ‖ξ‖ = 1 -/
  unit_norm : ‖ξ‖ = 1
  /-- The GNS condition: ω(a) = ⟪ξ, π(a)ξ⟫ for all a ∈ A -/
  gns_condition : ∀ a : A, ω a = @inner ℂ H hilbert.toInnerProductSpace.toCore.toInner ξ (π a ξ)

attribute [instance] Representation.hilbert

namespace Representation

open ComplexConjugate

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable {ω : State ℂ A}

/-- A submodule `W` of the Hilbert space of a GNS representation is invariant if it is
stable under the action of `π(a)` for every `a : A`. -/
def IsInvariant (T : Representation ω) (W : Submodule ℂ T.H) : Prop :=
  ∀ a : A, W.map (T.π a) ≤ W

/-- A GNS representation is (topologically) irreducible if the only **closed** invariant
submodules are `⊥` and `⊤`. -/
def IsIrreducible (T : Representation ω) : Prop :=
  ∀ W : Submodule ℂ T.H,
    IsClosed (W : Set T.H) →
    T.IsInvariant W →
    (W = ⊥ ∨ W = ⊤)

@[simp] lemma isInvariant_bot (T : Representation ω) : T.IsInvariant (⊥ : Submodule ℂ T.H) := by
  intro a w hw
  rcases (show w = 0 from by simpa using hw) with rfl
  simp

@[simp] lemma isInvariant_top (T : Representation ω) : T.IsInvariant (⊤ : Submodule ℂ T.H) := by
  intro a w hw
  simp

/-- A unitary equivalence between two GNS representations packages the underlying
unitary between the Hilbert spaces together with the expected compatibility data. -/
structure UnitaryEquiv (T₁ T₂ : Representation ω) where
  /-- The underlying unitary between the Hilbert spaces. -/
  unitary_map : UnitaryMap T₁.H T₂.H
  /-- The unitary sends the cyclic vector of the first triplet to that of the second. -/
  map_cyclic_vector :
    (unitary_map.toContinuousLinearMap) T₁.ξ = T₂.ξ
  /-- The unitary intertwines the two representations. -/
  intertwines :
    ∀ a : A,
      (unitary_map.toContinuousLinearMap) ∘L T₁.π a =
        T₂.π a ∘L (unitary_map.toContinuousLinearMap)

notation:50 T₁ " ≃ᵁ " T₂ => Representation.UnitaryEquiv (ω := _) T₁ T₂

/-- Auxiliary: computes `⟪π a ξ, π b ξ⟫ = ω (star a * b)` for a single GNS triplet. -/
private lemma inner_cyclic_aux (T : Representation ω) (a b : A) :
    @inner ℂ T.H _ (T.π a T.ξ) (T.π b T.ξ) = ω (star a * b) := by
  have h₁ : @inner ℂ T.H _ (T.π a T.ξ) (T.π b T.ξ) =
            @inner ℂ T.H _ T.ξ ((T.π a).adjoint (T.π b T.ξ)) := by
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
    @inner ℂ T₁.H _ (T₁.π a T₁.ξ) (T₁.π b T₁.ξ) =
    @inner ℂ T₂.H _ (T₂.π a T₂.ξ) (T₂.π b T₂.ξ) := by
  calc
    @inner ℂ T₁.H _ (T₁.π a T₁.ξ) (T₁.π b T₁.ξ)
        = ω (star a * b) := inner_cyclic_aux T₁ a b
    _ = @inner ℂ T₂.H _ (T₂.π a T₂.ξ) (T₂.π b T₂.ξ) := (inner_cyclic_aux T₂ a b).symm

/-- Equality of norms of corresponding cyclic orbit vectors between two triplets. -/
private lemma norm_cyclic (T₁ T₂ : Representation ω) (a : A) :
    ‖T₁.π a T₁.ξ‖ = ‖T₂.π a T₂.ξ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_sq ℂ]
  exact congr_arg RCLike.re (inner_cyclic T₁ T₂ a a)

/-- The canonical correspondence on cyclic orbit vectors: `π₁(a) ξ₁ ↦ π₂(a) ξ₂`. -/
private def cyclicCorrespondence (_T₁ T₂ : Representation ω) (a : A) : T₂.H :=
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
      _ = T₁.π a T₁.ξ - T₁.π b T₁.ξ := by simp [ContinuousLinearMap.sub_apply]
      _ = 0 := by rw [h]; simp
  -- Transfer vanishing inner product to T₂ using equality of inner forms on cyclic vectors
  have h_inner_zero_T₂ : @inner ℂ T₂.H _ (T₂.π (a - b) T₂.ξ) (T₂.π (a - b) T₂.ξ) = 0 := by
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
    _ = T₂.π a T₂.ξ - (T₂.π a T₂.ξ - T₂.π b T₂.ξ) := by simp [ContinuousLinearMap.sub_apply]
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
  have h_inner₁ : @inner ℂ T₁.H _ (T₁.π a T₁.ξ) T₁.ξ = conj (ω a) := by
    calc @inner ℂ T₁.H _ (T₁.π a T₁.ξ) T₁.ξ
        = conj (@inner ℂ T₁.H _ T₁.ξ (T₁.π a T₁.ξ)) := by rw [@inner_conj_symm ℂ T₁.H]
      _ = conj (ω a) := by rw [T₁.gns_condition a]
  have h_inner₂ : @inner ℂ T₂.H _ (T₂.π a T₂.ξ) T₂.ξ = conj (ω a) := by
    calc @inner ℂ T₂.H _ (T₂.π a T₂.ξ) T₂.ξ
        = conj (@inner ℂ T₂.H _ T₂.ξ (T₂.π a T₂.ξ)) := by rw [@inner_conj_symm ℂ T₂.H]
      _ = conj (ω a) := by rw [T₂.gns_condition a]
  rw [h_inner₁, h_inner₂, h_norm, T₁.unit_norm, T₂.unit_norm]

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
    @inner ℂ T₂.H _ (cyclicMap T₁ T₂ x) (cyclicMap T₁ T₂ y) =
    @inner ℂ T₁.H _ x.val y.val := by
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
  obtain ⟨x₁, hx₁_close, hx₁_mem⟩ := Metric.dense_iff.mp (dense_cyclicSet T₁) T₁.ξ (ε / 2) (by linarith : 0 < ε / 2)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx₁_mem
  simp only [Set.mem_singleton_iff] at ha
  subst ha; rw [Metric.mem_ball, dist_eq_norm] at hx₁_close
  have : ‖(U : T₁.H →L[ℂ] T₂.H) T₁.ξ - T₂.ξ‖ < ε := by
    calc ‖(U : T₁.H →L[ℂ] T₂.H) T₁.ξ - T₂.ξ‖
        ≤ ‖(U : T₁.H →L[ℂ] T₂.H) T₁.ξ - (U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ)‖ +
          ‖(U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) - T₂.ξ‖ := by
          convert norm_add_le ((U : T₁.H →L[ℂ] T₂.H) T₁.ξ - (U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ))
                           ((U : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) - T₂.ξ) using 2; abel
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
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have h_dense := dense_cyclicSet T₁
  unfold cyclicSet at h_dense
  have h_on_cyclic : ∀ b : A, (U : T₁.H →L[ℂ] T₂.H) (T₁.π a (T₁.π b T₁.ξ)) = T₂.π a ((U : T₁.H →L[ℂ] T₂.H) (T₁.π b T₁.ξ)) :=
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
    ∀ x : T₁.H, (extendCyclicMap (T₁ := T₂) (T₂ := T₁)) ((extendCyclicMap (T₁ := T₁) (T₂ := T₂)) x) = x := by
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
    ∀ y : T₂.H, (extendCyclicMap (T₁ := T₁) (T₂ := T₂)) ((extendCyclicMap (T₁ := T₂) (T₂ := T₁)) y) = y := by
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
      = U_fun ((T₁.π a + T₁.π b) T₁.ξ) := by rw [ContinuousLinearMap.add_apply]
    _ = U_fun (T₁.π (a + b) T₁.ξ) := by rw [show T₁.π (a + b) = T₁.π a + T₁.π b from T₁.π.map_add' a b]
    _ = T₂.π (a + b) T₂.ξ := hUab
    _ = (T₂.π a + T₂.π b) T₂.ξ := by rw [show T₂.π (a + b) = T₂.π a + T₂.π b from T₂.π.map_add' a b]
    _ = T₂.π a T₂.ξ + T₂.π b T₂.ξ := by rw [ContinuousLinearMap.add_apply]
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
  show U_fun (c • T₁.π a T₁.ξ) = c • U_fun (T₁.π a T₁.ξ)
  calc U_fun (c • T₁.π a T₁.ξ)
      = U_fun ((c • T₁.π a) T₁.ξ) := rfl
    _ = U_fun ((T₁.π (c • a)) T₁.ξ) := by rw [show T₁.π (c • a) = c • T₁.π a from T₁.π.map_smul' c a]
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

/-- On cyclic orbit vectors, `cyclic_isometry` agrees with the expected correspondence. -/
private lemma cyclicIsometry_apply (T₁ T₂ : Representation ω) (a : A) :
  (cyclicIsometry T₁ T₂ : T₁.H →L[ℂ] T₂.H) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ := by
  -- The underlying linear map of `cyclicIsometry` is constructed from `extendCyclicMap`.
  have hx : T₁.π a T₁.ξ ∈ cyclicSet T₁ := mem_cyclicSet (T := T₁) a
  conv_lhs =>
    arg 1
    rw [show (cyclicIsometry T₁ T₂ : T₁.H →L[ℂ] T₂.H) =
      (cyclicIsometry T₁ T₂).toLinearIsometry.toContinuousLinearMap from rfl]
  -- The toFun of the `LinearIsometryEquiv` is `extendCyclicMap`.
  show extendCyclicMap (T₁ := T₁) (T₂ := T₂) (T₁.π a T₁.ξ) = T₂.π a T₂.ξ
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
  refine ⟨
    { unitary_map := asUnitary Uiso
      map_cyclic_vector := linear_isometry_equiv_map_cyclic_vector T₁ T₂ Uiso hU_cyclic_iso
      intertwines := linear_isometry_equiv_intertwines T₁ T₂ Uiso hU_cyclic_iso
    }
  ⟩

/-- The canonical GNS triplet produced by the quotient and completion construction. -/
noncomputable def canonical : Representation ω where
  H := GNS.Construction.Hω (ω := ω)
  π := GNS.Construction.πωStarHom ω
  ξ := GNS.Construction.ξω ω
  cyclic := GNS.Construction.ξω_is_cyclic ω
  unit_norm := GNS.Construction.ξω_norm ω
  gns_condition := GNS.Construction.state_recovery ω

end Representation

end GNS
