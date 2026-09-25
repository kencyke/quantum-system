/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.RelativeModular

/-!
# Transport of relative modular operators along isometric intertwiners

Let `M` and `N` be von Neumann algebras on Hilbert spaces `H` and `K`, and `V : H → K` a bounded
operator such that every `x ∈ M` is intertwined with some `y ∈ N` (`y V = V x` and `y⋆ V = V x⋆`),
and every `x′ ∈ M′` with some `y′ ∈ N′`. This covers spatial isomorphisms (`V` unitary,
`y = V x V†`), amplifications (`V = e ⊗ (·)`, `y = 1 ⊗ x`) and their composites with partial
isometries. Then `V` intertwines the relative Tomita operators `S^M_{η,ξ}` and `S^N_{Vη,Vξ}` and
the relative modular operators `Δ^M_{η,ξ}` and `Δ^N_{Vη,Vξ}`; if moreover `V† V ξ = ξ`, the
spectral measure of `Δ^N_{Vη,Vξ}` at `Vξ` equals that of `Δ^M_{η,ξ}` at `ξ`.

## Main results

* `VonNeumannAlgebra.adjoint_comp_comp_mem`, `VonNeumannAlgebra.adjoint_comp_comp_mem_commutant` —
  the compressions `V† N V ⊆ M` and `V† N′ V ⊆ M′`.
* `VonNeumannAlgebra.supportProj_comp_eq_comp_supportProj`,
  `VonNeumannAlgebra.adjoint_comp_supportProj` — `s_N(V ξ) V = V s_M(ξ)` and
  `V† s_N(V ξ) = s_M(ξ) V†`.
* `VonNeumannAlgebra.mem_graph_relativeTomita_of_intertwiner`,
  `VonNeumannAlgebra.adjoint_mem_graph_relativeTomita_of_intertwiner` — `V` maps the graph of
  `S^M_{η,ξ}` into that of `S^N_{Vη,Vξ}`, and `V†` maps the latter into the former.
* `VonNeumannAlgebra.mem_graph_relativeModular_of_intertwiner` — `V` maps the graph of
  `Δ^M_{η,ξ}` into that of `Δ^N_{Vη,Vξ}`.
* `VonNeumannAlgebra.spectralMeasure_relativeModular_of_intertwiner` — equality of the spectral
  measures.
-/

@[expose] public section

open Complex ClosedSubmodule
open scoped InnerProductSpace VonNeumannAlgebra LinearPMap
open InnerProductSpace (cyclicSubspace)

namespace VonNeumannAlgebra

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {V : H →L[ℂ] K}

local notation "V†" => ContinuousLinearMap.adjoint V

/-- From `y⋆ V = V x⋆`: `V† y = x V†`. -/
private lemma adjoint_comp_eq_of_star_comp {x : H →L[ℂ] H} {y : K →L[ℂ] K}
    (h : star y ∘L V = V ∘L star x) : V† ∘L y = x ∘L V† := by
  have h' := congrArg ContinuousLinearMap.adjoint h
  rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint (star y), star_star,
    ← ContinuousLinearMap.star_eq_adjoint (star x), star_star] at h'

omit [CompleteSpace H] [CompleteSpace K] in
private lemma apply_apply_of_comp_eq {x : H →L[ℂ] H} {y : K →L[ℂ] K} (h : y ∘L V = V ∘L x)
    (u : H) : y (V u) = V (x u) :=
  congr($h u)

private lemma adjoint_apply_apply_of_star_comp {x : H →L[ℂ] H} {y : K →L[ℂ] K}
    (h : star y ∘L V = V ∘L star x) (z : K) : V† (y z) = x (V† z) :=
  congr($(adjoint_comp_eq_of_star_comp h) z)

/-- **Compression.** `V† y V ∈ M` for `y ∈ N`, when every `x′ ∈ M′` is intertwined by `V` with
some `y′ ∈ N′` (`y′ V = V x′`, `y′⋆ V = V x′⋆`). -/
theorem adjoint_comp_comp_mem
    (hM' : ∀ x ∈ M′, ∃ y ∈ N′, y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x)
    {y : K →L[ℂ] K} (hy : y ∈ N) : V† ∘L y ∘L V ∈ M := by
  rw [← commutant_commutant M, mem_commutant_iff]
  intro x hx
  obtain ⟨y', hy', h₁, h₂⟩ := hM' x hx
  have hc := mem_commutant_iff.mp hy' y hy
  ext u
  simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
  rw [← apply_apply_of_comp_eq h₁ u, ← adjoint_apply_apply_of_star_comp h₂,
    ← mul_apply_eq_comp, ← mul_apply_eq_comp, hc]

/-- **Compression of the commutants.** `V† y V ∈ M′` for `y ∈ N′`, when every `x ∈ M` is
intertwined by `V` with some `y ∈ N`. -/
theorem adjoint_comp_comp_mem_commutant
    (hM : ∀ x ∈ M, ∃ y ∈ N, y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x)
    {y : K →L[ℂ] K} (hy : y ∈ N′) : V† ∘L y ∘L V ∈ M′ := by
  rw [mem_commutant_iff]
  intro x hx
  obtain ⟨y', hy', h₁, h₂⟩ := hM x hx
  have hc := mem_commutant_iff.mp hy y' hy'
  ext u
  simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
  rw [← apply_apply_of_comp_eq h₁ u, ← adjoint_apply_apply_of_star_comp h₂,
    ← mul_apply_eq_comp, ← mul_apply_eq_comp, hc]

variable (hM : ∀ x ∈ M, ∃ y ∈ N, y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x)
  (hM' : ∀ x ∈ M′, ∃ y ∈ N′, y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x)

include hM' in
/-- `V` maps `[M ξ]ᗮ` into `[N (V ξ)]ᗮ`. -/
lemma apply_mem_orthogonal_cyclicSubspace_of_intertwiner {ξ ζ : H}
    (hζ : ζ ∈ (cyclicSubspace (M : Set (H →L[ℂ] H)) ξ).toSubmoduleᗮ) :
    V ζ ∈ (cyclicSubspace (N : Set (K →L[ℂ] K)) (V ξ)).toSubmoduleᗮ := by
  rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_left V]
  exact hζ _ (adjoint_comp_comp_mem hM' hy)

include hM in
/-- `V†` maps `[N (V ξ)]ᗮ` into `[M ξ]ᗮ`. -/
lemma adjoint_apply_mem_orthogonal_cyclicSubspace_of_intertwiner {ξ : H} {ζ : K}
    (hζ : ζ ∈ (cyclicSubspace (N : Set (K →L[ℂ] K)) (V ξ)).toSubmoduleᗮ) :
    V† ζ ∈ (cyclicSubspace (M : Set (H →L[ℂ] H)) ξ).toSubmoduleᗮ := by
  rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
  intro x hx
  obtain ⟨y, hy, h₁, -⟩ := hM x hx
  rw [ContinuousLinearMap.adjoint_inner_right, ← apply_apply_of_comp_eq h₁ ξ]
  exact hζ _ hy

include hM hM' in
/-- **Support projections.** `s_N(V ξ) V = V s_M(ξ)`. -/
theorem supportProj_comp_eq_comp_supportProj (ξ : H) :
    N.supportProj (V ξ) ∘L V = V ∘L M.supportProj ξ := by
  ext u
  change N.supportProj (V ξ) (V u) = V (M.supportProj ξ u)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · -- `V [M′ ξ] ⊆ [N′ (V ξ)]`.
    have hsub := cyclicSubspace_subset (M := M′) (ξ := ξ)
      (s := V ⁻¹' (cyclicSubspace (N′ : Set (K →L[ℂ] K)) (V ξ) : Set K))
      ((cyclicSubspace _ _).isClosed.preimage V.continuous) fun x hx => by
        obtain ⟨y, hy, h₁, -⟩ := hM' x hx
        rw [Set.mem_preimage, ← apply_apply_of_comp_eq h₁ ξ]
        exact InnerProductSpace.apply_mem_cyclicSubspace _ hy
    exact hsub (Submodule.starProjection_apply_mem
      (cyclicSubspace (M′ : Set (H →L[ℂ] H)) ξ).toSubmodule u)
  · -- `V [M′ ξ]ᗮ ⊆ [N′ (V ξ)]ᗮ`.
    rw [← map_sub]
    have hM'' : ∀ x ∈ M′′, ∃ y ∈ N′′, y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x := by
      simpa only [commutant_commutant] using hM
    have h := apply_mem_orthogonal_cyclicSubspace_of_intertwiner (M := M′) (N := N′) hM''
      (Submodule.sub_starProjection_mem_orthogonal
        (K := (cyclicSubspace (M′ : Set (H →L[ℂ] H)) ξ).toSubmodule) u)
    have h' : ⟪w, V (u - M.supportProj ξ u)⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hw h
    rw [← inner_conj_symm, h', map_zero]

include hM hM' in
/-- **Support projections**, adjoint form: `V† s_N(V ξ) = s_M(ξ) V†`. -/
theorem adjoint_comp_supportProj (ξ : H) :
    V† ∘L N.supportProj (V ξ) = M.supportProj ξ ∘L V† := by
  have h := congrArg ContinuousLinearMap.adjoint (supportProj_comp_eq_comp_supportProj hM hM' ξ)
  rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint (N.supportProj _),
    ← ContinuousLinearMap.star_eq_adjoint (M.supportProj _),
    (N.isStarProjection_supportProj _).isSelfAdjoint.star_eq,
    (M.isStarProjection_supportProj _).isSelfAdjoint.star_eq] at h

include hM hM' in
/-- `V` maps the graph of `S^M_{η,ξ}` into that of `S^N_{Vη,Vξ}`. -/
theorem mem_graph_relativeTomita_of_intertwiner {η ξ a b : H}
    (h : (a, b) ∈ (M.relativeTomita η ξ).graph) :
    (V a, V b) ∈ (N.relativeTomita (V η) (V ξ)).graph := by
  obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  obtain ⟨y, hy, h₁, h₂⟩ := hM x hx
  convert mk_mem_graph_relativeTomita (η := V η) hy
    (apply_mem_orthogonal_cyclicSubspace_of_intertwiner hM' hζ) using 2
  · rw [map_add, apply_apply_of_comp_eq h₁ ξ]
  · dsimp only
    rw [apply_apply_of_comp_eq h₂ η]
    exact congr($(supportProj_comp_eq_comp_supportProj hM hM' ξ) (star x η)).symm

include hM hM' in
/-- `V†` maps the graph of `S^N_{Vη,Vξ}` into that of `S^M_{η,ξ}`. -/
theorem adjoint_mem_graph_relativeTomita_of_intertwiner {η ξ : H}
    {a b : K} (h : (a, b) ∈ (N.relativeTomita (V η) (V ξ)).graph) :
    (V† a, V† b) ∈ (M.relativeTomita η ξ).graph := by
  obtain ⟨y, hy, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  have hyM := adjoint_comp_comp_mem hM' hy
  convert mk_mem_graph_relativeTomita (η := η) hyM
    (adjoint_apply_mem_orthogonal_cyclicSubspace_of_intertwiner hM hζ) using 2
  · rw [map_add]
    rfl
  · dsimp only
    rw [ContinuousLinearMap.star_eq_adjoint (V† ∘L y ∘L V), ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint y]
    exact congr($(adjoint_comp_supportProj hM hM' ξ) (star y (V η)))

include hM hM' in
/-- `V` maps the graph of `Δ^M_{η,ξ}` into that of `Δ^N_{Vη,Vξ}`. -/
theorem mem_graph_relativeModular_of_intertwiner {η ξ u z : H}
    (h : (u, z) ∈ (M.relativeModular η ξ).graph) :
    (V u, V z) ∈ (N.relativeModular (V η) (V ξ)).graph := by
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat] at h ⊢
  obtain ⟨w, hw, hwz⟩ := h
  refine ⟨V w, LinearPMap.mem_graph_closure_of_mapsTo (isClosable_relativeTomita N (V η) (V ξ))
    (f := fun p : H × H => (V p.1, V p.2)) (by fun_prop)
    (fun p hp => mem_graph_relativeTomita_of_intertwiner hM hM' hp) hw, ?_⟩
  rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita N (V η) (V ξ)),
    LinearPMap.mem_graph_adjoint_iff (dense_domain_relativeTomita N (V η) (V ξ))]
  rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita M η ξ),
    LinearPMap.mem_graph_adjoint_iff (dense_domain_relativeTomita M η ξ)] at hwz
  intro a b hab
  have := hwz _ _ (adjoint_mem_graph_relativeTomita_of_intertwiner hM hM' hab)
  rwa [inner_real_eq_re_inner, inner_real_eq_re_inner, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left, ← inner_real_eq_re_inner,
    ← inner_real_eq_re_inner] at this

include hM hM' in
/-- **Transport of spectral measures.** If moreover `V† V ξ = ξ`, the spectral measure of
`Δ^N_{Vη,Vξ}` at `V ξ` equals that of `Δ^M_{η,ξ}` at `ξ`. -/
theorem spectralMeasure_relativeModular_of_intertwiner {η ξ : H} (hV : V† (V ξ) = ξ) :
    (isSelfAdjoint_relativeModular N (V η) (V ξ)).spectralMeasure (V ξ) =
      (isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ :=
  (isSelfAdjoint_relativeModular M η ξ).spectralMeasure_intertwiner
    (isSelfAdjoint_relativeModular N (V η) (V ξ))
    (fun _ _ h => mem_graph_relativeModular_of_intertwiner hM hM' h) hV

end VonNeumannAlgebra
