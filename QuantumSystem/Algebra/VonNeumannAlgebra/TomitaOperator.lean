module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Separating
public import QuantumSystem.Algebra.Linear.Unbounded.Antilinear

/-!
# Tomita Operator

This file defines the Tomita operator S₀ for a von Neumann algebra M with a
cyclic and separating vector Ω.

## Main definitions

* `algebraicOrbitSubmodule`: The domain M·Ω = { x·Ω | x ∈ M }
* `tomitaOperator₀`: The pre-closed Tomita operator S₀ : x·Ω ↦ x*·Ω

## Mathematical background

For a von Neumann algebra M ⊆ B(H) with a cyclic and separating vector Ω:

1. **Domain**: dom(S₀) = M·Ω = { x·Ω | x ∈ M }
2. **Definition**: S₀(x·Ω) = x*·Ω for x ∈ M

## References

* [Takesaki, *Theory of Operator Algebras I*][takesaki2002]
-/

@[expose] public section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Domain of Tomita operator -/

section TomitaDomain

variable (M : VonNeumannAlgebra H) (Ω : H)

/-- The algebraic orbit M·Ω as a set: { x·Ω | x ∈ M }. -/
def algebraicOrbit : Set H := { (x : H →L[ℂ] H) Ω | x : M }

/-- The algebraic orbit M·Ω as a submodule of H. -/
def algebraicOrbitSubmodule : Submodule ℂ H where
  carrier := algebraicOrbit M Ω
  add_mem' := fun {a b} ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by simp only [AddMemClass.coe_add,
    ContinuousLinearMap.add_apply, hx, hy]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := fun c {a} ⟨x, hx⟩ => ⟨c • x, by
    change c • (x : H →L[ℂ] H) Ω = c • a; simp [hx]⟩

theorem mem_algebraicOrbitSubmodule {ξ : H} :
    ξ ∈ algebraicOrbitSubmodule M Ω ↔ ∃ x : M, (x : H →L[ℂ] H) Ω = ξ := Iff.rfl

/-- 1·Ω = Ω is in the algebraic orbit. -/
theorem Ω_mem_algebraicOrbit : Ω ∈ algebraicOrbitSubmodule M Ω :=
  ⟨1, by simp⟩

/-- The algebraic orbit is dense when Ω is cyclic. -/
theorem algebraicOrbit_dense (hΩ : IsCyclicVector M Ω) :
    Dense (algebraicOrbitSubmodule M Ω : Set H) := hΩ

end TomitaDomain

/-! ### Tomita operator S₀ -/

section TomitaOperator

variable (M : VonNeumannAlgebra H) (Ω : H)

/-- When Ω is separating for M, the map x ↦ x·Ω is injective on M. -/
theorem algebraicOrbit_injective (hΩsep : IsSeparatingVector M Ω) :
    Function.Injective (fun x : M => (x : H →L[ℂ] H) Ω) :=
  (isSeparatingVector_iff_injective M Ω).mp hΩsep

/-- For any ξ ∈ M·Ω, pick a representative x ∈ M with x·Ω = ξ. -/
noncomputable def algebraicOrbitRep (ξ : algebraicOrbitSubmodule M Ω) : M :=
  Classical.choose ((mem_algebraicOrbitSubmodule M Ω).mp ξ.property)

theorem algebraicOrbitRep_spec (ξ : algebraicOrbitSubmodule M Ω) :
    (algebraicOrbitRep M Ω ξ : H →L[ℂ] H) Ω = ξ :=
  Classical.choose_spec ((mem_algebraicOrbitSubmodule M Ω).mp ξ.property)

theorem algebraicOrbitRep_unique (hΩsep : IsSeparatingVector M Ω)
    (ξ : algebraicOrbitSubmodule M Ω) (x : M) (hx : (x : H →L[ℂ] H) Ω = ξ) :
    x = algebraicOrbitRep M Ω ξ := by
  apply algebraicOrbit_injective M Ω hΩsep
  simp only [hx, algebraicOrbitRep_spec]

/-- The pre-Tomita operator S₀: for ξ = x·Ω, define S₀(ξ) = x*·Ω. -/
noncomputable def tomitaOperator₀Fun :
    algebraicOrbitSubmodule M Ω → H :=
  fun ξ => (star (algebraicOrbitRep M Ω ξ) : H →L[ℂ] H) Ω

/-- S₀(x·Ω) = x*·Ω when we know ξ = x·Ω. -/
theorem tomitaOperator₀Fun_of_eq (hΩsep : IsSeparatingVector M Ω)
    (x : M) (ξ : algebraicOrbitSubmodule M Ω) (hx : (x : H →L[ℂ] H) Ω = ξ) :
    tomitaOperator₀Fun M Ω ξ = (star x : H →L[ℂ] H) Ω := by
  unfold tomitaOperator₀Fun
  congr 2
  have := algebraicOrbitRep_unique M Ω hΩsep ξ x hx
  simp only [this]

/-- S₀ is additive. -/
theorem tomitaOperator₀Fun_add (hΩsep : IsSeparatingVector M Ω)
    (ξ η : algebraicOrbitSubmodule M Ω) :
    tomitaOperator₀Fun M Ω (ξ + η) =
    tomitaOperator₀Fun M Ω ξ + tomitaOperator₀Fun M Ω η := by
  obtain ⟨x, hx⟩ := (mem_algebraicOrbitSubmodule M Ω).mp ξ.property
  obtain ⟨y, hy⟩ := (mem_algebraicOrbitSubmodule M Ω).mp η.property
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep x ξ hx]
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep y η hy]
  have hxy : ((x + y : M) : H →L[ℂ] H) Ω = (ξ : H) + (η : H) := by simp [hx, hy]
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep (x + y) (ξ + η) (by simp [hx, hy])]
  simp only [star_add, AddMemClass.coe_add, ContinuousLinearMap.add_apply]

/-- S₀ is conjugate-homogeneous: S₀(c·ξ) = c̄·S₀(ξ). -/
theorem tomitaOperator₀Fun_smul (hΩsep : IsSeparatingVector M Ω)
    (c : ℂ) (ξ : algebraicOrbitSubmodule M Ω) :
    tomitaOperator₀Fun M Ω (c • ξ) =
    starRingEnd ℂ c • tomitaOperator₀Fun M Ω ξ := by
  obtain ⟨x, hx⟩ := (mem_algebraicOrbitSubmodule M Ω).mp ξ.property
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep x ξ hx]
  have hcx : ((c • x : M) : H →L[ℂ] H) Ω = c • (ξ : H) := by
    change c • (x : H →L[ℂ] H) Ω = c • (ξ : H); simp [hx]
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep (c • x) (c • ξ) hcx]
  have h_smul_coe : ((c • x : M) : H →L[ℂ] H) = c • (x : H →L[ℂ] H) := rfl
  simp only [ContinuousLinearMap.star_eq_adjoint, h_smul_coe, LinearIsometryEquiv.map_smulₛₗ,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]

/-- The Tomita operator S₀ as an antilinear map on its domain. -/
noncomputable def tomitaOperator₀AsAntilinear (hΩsep : IsSeparatingVector M Ω) :
    algebraicOrbitSubmodule M Ω →ₗ⋆[ℂ] H where
  toFun := tomitaOperator₀Fun M Ω
  map_add' := tomitaOperator₀Fun_add M Ω hΩsep
  map_smul' := tomitaOperator₀Fun_smul M Ω hΩsep

/-- The Tomita operator S₀ as a densely defined antilinear map.

For a von Neumann algebra M with cyclic separating vector Ω:
- Domain: dom(S₀) = M·Ω
- Definition: S₀(x·Ω) = x*·Ω -/
noncomputable def tomitaOperator₀ (hΩcyc : IsCyclicVector M Ω) (hΩsep : IsSeparatingVector M Ω) :
    AntilinearOnHilbertSpace ℂ H where
  domain := algebraicOrbitSubmodule M Ω
  toFun := tomitaOperator₀AsAntilinear M Ω hΩsep
  dense_domain := algebraicOrbit_dense M Ω hΩcyc

/-- S₀(Ω) = Ω since 1·Ω = Ω and 1* = 1. -/
theorem tomitaOperator₀_apply_Ω (hΩcyc : IsCyclicVector M Ω) (hΩsep : IsSeparatingVector M Ω) :
    tomitaOperator₀ M Ω hΩcyc hΩsep ⟨Ω, Ω_mem_algebraicOrbit M Ω⟩ = Ω := by
  change tomitaOperator₀Fun M Ω ⟨Ω, Ω_mem_algebraicOrbit M Ω⟩ = Ω
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep 1 ⟨Ω, Ω_mem_algebraicOrbit M Ω⟩ (by simp)]
  simp

/-- S₀(x·Ω) = x*·Ω for any x ∈ M. -/
theorem tomitaOperator₀_apply (hΩcyc : IsCyclicVector M Ω) (hΩsep : IsSeparatingVector M Ω)
    (x : M) :
    tomitaOperator₀ M Ω hΩcyc hΩsep ⟨(x : H →L[ℂ] H) Ω, x, rfl⟩ = (star x : H →L[ℂ] H) Ω := by
  change tomitaOperator₀Fun M Ω ⟨(x : H →L[ℂ] H) Ω, x, rfl⟩ = (star x : H →L[ℂ] H) Ω
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep x ⟨(x : H →L[ℂ] H) Ω, x, rfl⟩ rfl]

/-- S₀² = 1 on M·Ω: S₀(S₀(x·Ω)) = x·Ω.

This follows from (x*)* = x in a C*-algebra. -/
theorem tomitaOperator₀_sq (hΩcyc : IsCyclicVector M Ω) (hΩsep : IsSeparatingVector M Ω)
    (x : M) : ∃ (hη : (star x : H →L[ℂ] H) Ω ∈ algebraicOrbitSubmodule M Ω),
    tomitaOperator₀ M Ω hΩcyc hΩsep ⟨(star x : H →L[ℂ] H) Ω, hη⟩ = (x : H →L[ℂ] H) Ω := by
  refine ⟨⟨star x, rfl⟩, ?_⟩
  change tomitaOperator₀Fun M Ω ⟨(star x : H →L[ℂ] H) Ω, ⟨star x, rfl⟩⟩ = (x : H →L[ℂ] H) Ω
  rw [tomitaOperator₀Fun_of_eq M Ω hΩsep (star x) ⟨(star x : H →L[ℂ] H) Ω, ⟨star x, rfl⟩⟩ rfl]
  simp

end TomitaOperator

/-! ### Closability of Tomita operator -/

section Closability

variable (M : VonNeumannAlgebra H) (Ω : H)

/-- The graph of the Tomita operator S₀ as a set. -/
def tomitaOperator₀_graphSet (hΩcyc : IsCyclicVector M Ω) (hΩsep : IsSeparatingVector M Ω) :
    Set (H × H) :=
  { p | ∃ (x : (tomitaOperator₀ M Ω hΩcyc hΩsep).dom), p = ((x : H), (tomitaOperator₀ M Ω hΩcyc hΩsep) x) }

/-- A key property: ⟨S₀(x·Ω), y·Ω⟩ = conj ⟨y·Ω, S₀(x·Ω)⟩ for x, y ∈ M.

This follows from the conjugate symmetry of the inner product. -/
theorem tomitaOperator₀_inner_conj
    (x y : M) : ⟪(star x : H →L[ℂ] H) Ω, (y : H →L[ℂ] H) Ω⟫_ℂ =
               starRingEnd ℂ ⟪(y : H →L[ℂ] H) Ω, (star x : H →L[ℂ] H) Ω⟫_ℂ := by
  rw [inner_conj_symm]

/-- For the commutant M', we have: ⟨x*·Ω, y'·Ω⟩ = ⟨y'*·Ω, x·Ω⟩.

This follows from commutativity of M and M'. -/
theorem tomitaOperator₀_inner_swap_commutant
    (x : M) (y' : M.commutant) : ⟪(star x : H →L[ℂ] H) Ω, (y' : H →L[ℂ] H) Ω⟫_ℂ =
               ⟪(star y' : H →L[ℂ] H) Ω, (x : H →L[ℂ] H) Ω⟫_ℂ := by
  -- y' commutes with x, so y'·x = x·y'
  have hy'_comm := y'.property
  rw [VonNeumannAlgebra.mem_commutant_iff] at hy'_comm
  have hcomm : (x : H →L[ℂ] H) * (y' : H →L[ℂ] H) = (y' : H →L[ℂ] H) * (x : H →L[ℂ] H) :=
    hy'_comm (x : H →L[ℂ] H) x.property
  -- Use the adjoint property: ⟨x†Ω, y'Ω⟩ = ⟨Ω, xy'Ω⟩ and ⟨y'†Ω, xΩ⟩ = ⟨Ω, y'xΩ⟩
  simp only [ContinuousLinearMap.star_eq_adjoint]
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left]
  -- Goal: ⟨y'†(x†Ω), Ω⟩ = ⟨x†(y'†Ω), Ω⟩
  -- Since x·y' = y'·x, we have (x·y')† = (y'·x)†, i.e., y'†·x† = x†·y'†
  have hadj_comm : (ContinuousLinearMap.adjoint (y' : H →L[ℂ] H))
                   ((ContinuousLinearMap.adjoint (x : H →L[ℂ] H)) Ω) =
                   (ContinuousLinearMap.adjoint (x : H →L[ℂ] H))
                   ((ContinuousLinearMap.adjoint (y' : H →L[ℂ] H)) Ω) := by
    simp only [← ContinuousLinearMap.comp_apply]
    congr 1
    rw [← ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.adjoint_comp]
    -- Need to convert from comp form to mul form to use hcomm
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
    rw [hcomm]
  rw [hadj_comm]

/-- If Ω is separating, the Tomita operator S₀ is closable.

The proof uses the key observation that if (ξₙ, S₀(ξₙ)) converges to (0, η) in graph norm,
then for any y' ∈ M' (the commutant), we have
  ⟨η, y'·Ω⟩ = limₙ ⟨xₙ*·Ω, y'·Ω⟩ = limₙ ⟨y'*·Ω, xₙ·Ω⟩ → ⟨y'*·Ω, 0⟩ = 0.
The swap property holds because M and M' commute.
Since M'·Ω is dense (Ω is cyclic for M' when separating for M), this implies η = 0. -/
theorem tomitaOperator₀_isClosable (hΩcyc : IsCyclicVector M Ω) (hΩsep : IsSeparatingVector M Ω) :
    ∀ η : H, ((0, η) ∈ closure (tomitaOperator₀_graphSet M Ω hΩcyc hΩsep)) → η = 0 := by
  intro η hη
  -- Since Ω is separating for M, it is cyclic for M' (the commutant)
  have hΩcyc' : IsCyclicVector M.commutant Ω := hΩsep.isCyclic_commutant M Ω
  -- We show η is orthogonal to every element of M'·Ω
  have hη_ortho : ∀ y' : M.commutant, ⟪η, (y' : H →L[ℂ] H) Ω⟫_ℂ = 0 := by
    intro y'
    -- η is in the closure of the graph, so there's a sequence (xₙ·Ω, xₙ*·Ω) → (0, η)
    rw [mem_closure_iff_seq_limit] at hη
    obtain ⟨seq, hseq_mem, hseq_lim⟩ := hη
    -- Extract the operators for each sequence element
    have hseq_form : ∀ n, ∃ (xₙ : M), seq n = ((xₙ : H →L[ℂ] H) Ω, (star xₙ : H →L[ℂ] H) Ω) := by
      intro n
      specialize hseq_mem n
      simp only [tomitaOperator₀_graphSet, Set.mem_setOf_eq] at hseq_mem
      obtain ⟨ξ, hξ⟩ := hseq_mem
      obtain ⟨x, hx⟩ := (mem_algebraicOrbitSubmodule M Ω).mp ξ.property
      use x
      rw [hξ]
      congr 1
      · exact hx.symm
      · change tomitaOperator₀Fun M Ω ξ = (star x : H →L[ℂ] H) Ω
        rw [tomitaOperator₀Fun_of_eq M Ω hΩsep x ξ hx]
    -- Use continuity of inner product
    have hlim : Filter.Tendsto (fun n => (seq n).2) Filter.atTop (nhds η) := by
      have : Filter.Tendsto seq Filter.atTop (nhds (0, η)) := hseq_lim
      rw [nhds_prod_eq] at this
      exact Filter.Tendsto.snd this
    have hlim_fst : Filter.Tendsto (fun n => (seq n).1) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto seq Filter.atTop (nhds (0, η)) := hseq_lim
      rw [nhds_prod_eq] at this
      exact Filter.Tendsto.fst this
    -- ⟨η, y'·Ω⟩ = limₙ ⟨(seq n).2, y'·Ω⟩
    have hinner_lim : Filter.Tendsto (fun n => ⟪(seq n).2, (y' : H →L[ℂ] H) Ω⟫_ℂ)
        Filter.atTop (nhds ⟪η, (y' : H →L[ℂ] H) Ω⟫_ℂ) :=
      Filter.Tendsto.inner hlim tendsto_const_nhds
    -- Using the swap property for M and M': ⟨xₙ*·Ω, y'·Ω⟩ = ⟨y'*·Ω, xₙ·Ω⟩
    have hseq_eq : ∀ n, ⟪(seq n).2, (y' : H →L[ℂ] H) Ω⟫_ℂ =
                       ⟪(star y' : H →L[ℂ] H) Ω, (seq n).1⟫_ℂ := by
      intro n
      obtain ⟨xₙ, hxₙ⟩ := hseq_form n
      rw [hxₙ]
      exact tomitaOperator₀_inner_swap_commutant M Ω xₙ y'
    -- limₙ ⟨(seq n).2, y'·Ω⟩ = limₙ ⟨y'*·Ω, (seq n).1⟩ → ⟨y'*·Ω, 0⟩ = 0
    have hlim_inner_rhs : Filter.Tendsto (fun n => ⟪(star y' : H →L[ℂ] H) Ω, (seq n).1⟫_ℂ)
        Filter.atTop (nhds ⟪(star y' : H →L[ℂ] H) Ω, 0⟫_ℂ) :=
      Filter.Tendsto.inner tendsto_const_nhds hlim_fst
    simp only [inner_zero_right] at hlim_inner_rhs
    have hlim_eq : Filter.Tendsto (fun n => ⟪(seq n).2, (y' : H →L[ℂ] H) Ω⟫_ℂ)
        Filter.atTop (nhds 0) := by
      convert hlim_inner_rhs using 1
      ext n
      exact hseq_eq n
    exact tendsto_nhds_unique hinner_lim hlim_eq
  -- Since M'·Ω is dense and η is orthogonal to all of it, η = 0
  have hη_ortho_all : ∀ ξ ∈ algebraicOrbitSubmodule M.commutant Ω, ⟪η, ξ⟫_ℂ = 0 := by
    intro ξ hξ
    obtain ⟨y', hy'⟩ := (mem_algebraicOrbitSubmodule M.commutant Ω).mp hξ
    rw [← hy']
    exact hη_ortho y'
  -- η ⊥ (M'·Ω) and M'·Ω is dense implies η = 0
  have hdense : Dense (algebraicOrbitSubmodule M.commutant Ω : Set H) :=
    algebraicOrbit_dense M.commutant Ω hΩcyc'
  -- Since algebraicOrbitSubmodule is dense, its topological closure is ⊤
  have hclosure_top : (algebraicOrbitSubmodule M.commutant Ω).topologicalClosure = ⊤ := by
    rw [← Submodule.dense_iff_topologicalClosure_eq_top]
    exact hdense
  -- Therefore its orthogonal is ⊥
  have hortho_bot : (algebraicOrbitSubmodule M.commutant Ω)ᗮ = ⊥ := by
    rw [Submodule.topologicalClosure_eq_top_iff] at hclosure_top
    exact hclosure_top
  -- η is in the orthogonal complement
  have hη_in_ortho : η ∈ (algebraicOrbitSubmodule M.commutant Ω)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro ξ hξ
    rw [inner_eq_zero_symm]
    exact hη_ortho_all ξ hξ
  -- Since orthogonal is ⊥, η = 0
  rw [hortho_bot] at hη_in_ortho
  exact Submodule.mem_bot ℂ |>.mp hη_in_ortho

end Closability
