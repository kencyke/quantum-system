/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.Modular.RelativeModular
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Transport of relative modular operators along bounded intertwiners

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
* `VonNeumannAlgebra.compPMap_closure_relativeTomita_le_of_intertwiner`,
  `VonNeumannAlgebra.adjoint_compPMap_closure_relativeTomita_le_of_intertwiner` —
  `V S̄^M_{η,ξ} ⊆ S̄^N_{Vη,Vξ} V` and `V† S̄^N_{Vη,Vξ} ⊆ S̄^M_{η,ξ} V†`.
* `VonNeumannAlgebra.compPMap_relativeModular_le_of_intertwiner` — `V Δ^M_{η,ξ} ⊆ Δ^N_{Vη,Vξ} V`.
* `VonNeumannAlgebra.measure_pvm_relativeModular_of_intertwiner` — equality of the spectral
  measures.
* `VonNeumannAlgebra.star_comp_eq_of_comp_eq` — for a unitary `U`, `y U = U x` implies
  `y⋆ U = U x⋆`.
-/

@[expose] public section

open Complex ClosedSubmodule
open scoped InnerProductSpace InnerProduct VonNeumannAlgebra LinearPMap
open InnerProductSpace (cyclicSubspace)

namespace VonNeumannAlgebra

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {V : H →L[ℂ] K}

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
    (h : star y ∘L V = V ∘L star x) (z : K) : (V†) (y z) = x ((V†) z) :=
  congr($(adjoint_comp_eq_of_star_comp h) z)

/-- **Compression.** `V† y V ∈ M` for `y ∈ N`, when every `x′ ∈ M′` is intertwined by `V` with
some `y′ ∈ N′` (`y′ V = V x′`, `y′⋆ V = V x′⋆`). -/
lemma adjoint_comp_comp_mem
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
lemma adjoint_comp_comp_mem_commutant
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
    (hζ : ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ) :
    V ζ ∈ (cyclicSubspace N (V ξ)).toSubmoduleᗮ := by
  rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_left V]
  exact hζ _ (adjoint_comp_comp_mem hM' hy)

include hM in
/-- `V†` maps `[N (V ξ)]ᗮ` into `[M ξ]ᗮ`. -/
lemma adjoint_apply_mem_orthogonal_cyclicSubspace_of_intertwiner {ξ : H} {ζ : K}
    (hζ : ζ ∈ (cyclicSubspace N (V ξ)).toSubmoduleᗮ) :
    (V†) ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ := by
  rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
  intro x hx
  obtain ⟨y, hy, h₁, -⟩ := hM x hx
  rw [ContinuousLinearMap.adjoint_inner_right, ← apply_apply_of_comp_eq h₁ ξ]
  exact hζ _ hy

include hM hM' in
/-- **Support projections.** `s_N(V ξ) V = V s_M(ξ)`. -/
lemma supportProj_comp_eq_comp_supportProj (ξ : H) :
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
lemma adjoint_comp_supportProj (ξ : H) :
    V† ∘L N.supportProj (V ξ) = M.supportProj ξ ∘L V† := by
  have h := congrArg ContinuousLinearMap.adjoint (supportProj_comp_eq_comp_supportProj hM hM' ξ)
  rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint (N.supportProj _),
    ← ContinuousLinearMap.star_eq_adjoint (M.supportProj _),
    (N.isStarProjection_supportProj _).isSelfAdjoint.star_eq,
    (M.isStarProjection_supportProj _).isSelfAdjoint.star_eq] at h

include hM hM' in
/-- `V S^M_{η,ξ} ⊆ S^N_{Vη,Vξ} V`, pointwise on the generating vectors. -/
private lemma mem_graph_relativeTomita_of_intertwiner {η ξ a b : H}
    (h : (a, b) ∈ (S[M]⟦η, ξ⟧).graphₛₗ) :
    (V a, V b) ∈ (S[N]⟦V η, V ξ⟧).graphₛₗ := by
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
/-- `V† S^N_{Vη,Vξ} ⊆ S^M_{η,ξ} V†`, pointwise on the generating vectors. -/
private lemma adjoint_mem_graph_relativeTomita_of_intertwiner {η ξ : H}
    {a b : K} (h : (a, b) ∈ (S[N]⟦V η, V ξ⟧).graphₛₗ) :
    ((V†) a, (V†) b) ∈ (S[M]⟦η, ξ⟧).graphₛₗ := by
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
/-- **`V S̄^M_{η,ξ} ⊆ S̄^N_{Vη,Vξ} V`**: `V S^M_{η,ξ} ⊆ S^N_{Vη,Vξ} V` on the generating vectors,
hence on the closures (`LinearPMap.compPMap_closureₛₗ_le_closureₛₗ_compNat_toPMap`). -/
lemma compPMap_closure_relativeTomita_le_of_intertwiner {η ξ : H} :
    (V : H →ₗ[ℂ] K).compPMap (S[M]⟦η, ξ⟧).closureₛₗ ≤
      (S[N]⟦V η, V ξ⟧).closureₛₗ.compNat ((V : H →ₗ[ℂ] K).toPMap ⊤) :=
  LinearPMap.compPMap_closureₛₗ_le_closureₛₗ_compNat_toPMap (isClosable_relativeTomita M η ξ)
    (isClosable_relativeTomita N (V η) (V ξ)) V V
    (LinearPMap.compPMap_le_compNat_toPMap_iffₛₗ.mpr fun _ _ h =>
      mem_graph_relativeTomita_of_intertwiner hM hM' h)

include hM hM' in
/-- **`V† S̄^N_{Vη,Vξ} ⊆ S̄^M_{η,ξ} V†`**, as for `V`. -/
lemma adjoint_compPMap_closure_relativeTomita_le_of_intertwiner {η ξ : H} :
    ((V† : K →L[ℂ] H) : K →ₗ[ℂ] H).compPMap (S[N]⟦V η, V ξ⟧).closureₛₗ ≤
      (S[M]⟦η, ξ⟧).closureₛₗ.compNat (((V† : K →L[ℂ] H) : K →ₗ[ℂ] H).toPMap ⊤) :=
  LinearPMap.compPMap_closureₛₗ_le_closureₛₗ_compNat_toPMap
    (isClosable_relativeTomita N (V η) (V ξ)) (isClosable_relativeTomita M η ξ) (V†) (V†)
    (LinearPMap.compPMap_le_compNat_toPMap_iffₛₗ.mpr fun _ _ h =>
      adjoint_mem_graph_relativeTomita_of_intertwiner hM hM' h)

include hM hM' in
/-- **`V Δ^M_{η,ξ} ⊆ Δ^N_{Vη,Vξ} V`**: with `S̄ = S̄^M_{η,ξ}` and `S̄′ = S̄^N_{Vη,Vξ}`,
`V S̄ ⊆ S̄′ V` and `V S̄† ⊆ (S̄ V†)† ⊆ (V† S̄′)† = S̄′† V`, so `V S̄† S̄ ⊆ S̄′† S̄′ V`. -/
lemma compPMap_relativeModular_le_of_intertwiner {η ξ : H} :
    (V : H →ₗ[ℂ] K).compPMap Δ[M]⟦η, ξ⟧ ≤ Δ[N]⟦V η, V ξ⟧.compNat ((V : H →ₗ[ℂ] K).toPMap ⊤) := by
  set S := (S[M]⟦η, ξ⟧).closureₛₗ
  set S' := (S[N]⟦V η, V ξ⟧).closureₛₗ
  have hd := LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita M η ξ)
  have hd' := LinearPMap.dense_domain_closureₛₗ (dense_domain_relativeTomita N (V η) (V ξ))
  have h₁ : (V : H →ₗ[ℂ] K).compPMap S ≤ S'.compNat ((V : H →ₗ[ℂ] K).toPMap ⊤) :=
    compPMap_closure_relativeTomita_le_of_intertwiner hM hM'
  have h₂ : (V : H →ₗ[ℂ] K).compPMap S.adjointₛₗ ≤
      S'.adjointₛₗ.compNat ((V : H →ₗ[ℂ] K).toPMap ⊤) := by
    have hle : ((V† : K →L[ℂ] H) : K →ₗ[ℂ] H).compPMap S' ≤
        S.compNat (((V† : K →L[ℂ] H) : K →ₗ[ℂ] H).toPMap ⊤) :=
      adjoint_compPMap_closure_relativeTomita_le_of_intertwiner hM hM'
    have hadj := LinearPMap.compPMap_adjoint_le_adjointₛₗ_compNat_toPMap hd (V†) (hd'.mono hle.1)
    rw [ContinuousLinearMap.adjoint_adjoint] at hadj
    have hanti : (S.compNat (((V† : K →L[ℂ] H) : K →ₗ[ℂ] H).toPMap ⊤)).adjointₛₗ ≤
        (((V† : K →L[ℂ] H) : K →ₗ[ℂ] H).compPMap S').adjointₛₗ :=
      LinearPMap.adjointₛₗ_anti hd' hle
    have heq : (((V† : K →L[ℂ] H) : K →ₗ[ℂ] H).compPMap S').adjointₛₗ =
        S'.adjointₛₗ.compNat ((V : H →ₗ[ℂ] K).toPMap ⊤) := by
      rw [LinearPMap.adjointₛₗ_compPMap hd' (V†), ContinuousLinearMap.adjointₛₗ_eq_adjoint,
        ContinuousLinearMap.adjoint_adjoint]
    exact hadj.trans (hanti.trans_eq heq)
  rw [relativeModular_def, relativeModular_def]
  calc (V : H →ₗ[ℂ] K).compPMap (S.adjointₛₗ.compNat S)
      = ((V : H →ₗ[ℂ] K).compPMap S.adjointₛₗ).compNat S := (LinearPMap.compPMap_compNat _ _ _).symm
    _ ≤ (S'.adjointₛₗ.compNat ((V : H →ₗ[ℂ] K).toPMap ⊤)).compNat S :=
        LinearPMap.compNat_mono h₂ le_rfl
    _ = S'.adjointₛₗ.compNat ((V : H →ₗ[ℂ] K).compPMap S) := by
        rw [LinearPMap.compNat_assoc, LinearPMap.toPMap_compNat]
    _ ≤ S'.adjointₛₗ.compNat (S'.compNat ((V : H →ₗ[ℂ] K).toPMap ⊤)) :=
        LinearPMap.compNat_mono le_rfl h₁
    _ = (S'.adjointₛₗ.compNat S').compNat ((V : H →ₗ[ℂ] K).toPMap ⊤) :=
        (LinearPMap.compNat_assoc _ _ _).symm

include hM hM' in
/-- **Transport of spectral measures.** If moreover `V† V ξ = ξ`, the spectral measure of
`Δ^N_{Vη,Vξ}` at `V ξ` equals that of `Δ^M_{η,ξ}` at `ξ`. -/
theorem measure_pvm_relativeModular_of_intertwiner {η ξ : H} (hV : (V†) (V ξ) = ξ) :
    μ[N]⟦V η, V ξ⟧ =
      μ[M]⟦η, ξ⟧ :=
  (isSelfAdjoint_relativeModular M η ξ).measure_pvm_intertwiner
    (isSelfAdjoint_relativeModular N (V η) (V ξ))
    (compPMap_relativeModular_le_of_intertwiner hM hM') hV

/-- For a unitary `U`, the intertwining relation `y U = U x` implies `y⋆ U = U x⋆`: the second
half of the hypotheses above is automatic for spatial isomorphisms. -/
lemma star_comp_eq_of_comp_eq (U : H ≃ₗᵢ[ℂ] K) {x : H →L[ℂ] H} {y : K →L[ℂ] K}
    (h : y ∘L (U : H →L[ℂ] K) = U ∘L x) : star y ∘L (U : H →L[ℂ] K) = U ∘L star x := by
  have h' := congrArg ContinuousLinearMap.adjoint h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, U.adjoint_eq_symm,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint] at h'
  ext v
  apply U.symm.injective
  simpa using congr($h' (U v))

end VonNeumannAlgebra
