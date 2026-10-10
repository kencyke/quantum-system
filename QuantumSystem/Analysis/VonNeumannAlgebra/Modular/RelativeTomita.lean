/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.UnboundedOperator.SemilinearAdjoint
public import QuantumSystem.Analysis.VonNeumannAlgebra.SupportProjection
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearPMap.Closure

/-!
# The relative Tomita operator

Let `M` be a von Neumann algebra on `H` and `ξ, η ∈ H`. Araki's **relative Tomita operator**
`S_{η,ξ}` is the conjugate-linear operator
`S_{η,ξ} (x ξ + ζ) = s(ξ) x⋆ η` for `x ∈ M` and `ζ ⊥ [M ξ]`,
where `s(ξ) = VonNeumannAlgebra.supportProj M ξ` is the support of `ξ` in `M`. It is well defined
because `x ξ = 0` forces `s(ξ) x⋆ = 0` (`VonNeumannAlgebra.supportProj_mul_eq_zero_iff`), densely
defined because its domain `M ξ + [M ξ]ᗮ` is dense, and it satisfies
`⟪S_{η,ξ} u, v⟫ = ⟪F_{η,ξ} v, u⟫` against the same construction `F_{η,ξ}` for the commutant `M′`.
Hence `F_{η,ξ} ⊆ S_{η,ξ}†` and `S_{η,ξ}` is closable. Its closure defines the relative modular
operator `Δ_{η,ξ} = S̄†S̄` (downstream), and Araki's relative entropy of the vector functionals
`ω_ξ`, `ω_η` is `S(ω_ξ ‖ ω_η) = -⟪ξ, log Δ_{η,ξ} ξ⟫`. In Araki's notation `S_{Φ,Ψ}` this is
`Φ = η`, `Ψ = ξ`; Ohya–Petz write `S_{η,ξ}` as here.

The equality `S_{η,ξ}† = F̄_{η,ξ}` holds for arbitrary `η, ξ`
(`VonNeumannAlgebra.adjoint_relativeTomita_eq_closure_commutant`, in
`QuantumSystem.Analysis.VonNeumannAlgebra.Modular.TomitaAdjoint`).
Transformation rules along bounded intertwiners between different Hilbert spaces (spatial
isomorphisms, amplifications) are in `QuantumSystem.Analysis.VonNeumannAlgebra.Modular.Intertwiner`
(`VonNeumannAlgebra.compPMap_closure_relativeTomita_le_of_intertwiner` and companions).

The relative Tomita operator is a conjugate-linear partially defined operator
`H →ₛₗ.[starRingEnd ℂ] H`, defined from its graph (`LinearPMap.ofGraphₛₗ`); its adjoint is the
antilinear adjoint `LinearPMap.adjointₛₗ`.

## Main definitions

* `VonNeumannAlgebra.relativeTomitaGraph M η ξ` — the graph `{(x ξ + ζ, s(ξ) x⋆ η)}`.
* `VonNeumannAlgebra.relativeTomita M η ξ` — the operator `S_{η,ξ}` with that graph.

## Main results

* `VonNeumannAlgebra.graph_relativeTomita` — the graph of `S_{η,ξ}` is `relativeTomitaGraph`;
  `VonNeumannAlgebra.mem_domain_relativeTomita_iff` — its domain is `M ξ + [M ξ]ᗮ`, independent
  of `η` (`VonNeumannAlgebra.domain_relativeTomita_eq`).
* `VonNeumannAlgebra.self_mem_graph_relativeTomita` — `S_{η,ξ} ξ = s(ξ) η`.
* `VonNeumannAlgebra.smul_mem_relativeTomitaGraph` — the graph is invariant under
  `(u, v) ↦ (c u, c̄ v)`, so that `S_{η,ξ}` is conjugate-linear.
* `VonNeumannAlgebra.dense_domain_relativeTomita` — `S_{η,ξ}` is densely defined.
* `VonNeumannAlgebra.inner_eq_of_mem_graph_relativeTomita` — `⟪S u, v⟫ = ⟪F v, u⟫` with
  `F = relativeTomita M′ η ξ`; hence `S` and `F` are formal adjoints
  (`VonNeumannAlgebra.isFormalAdjoint_relativeTomita`), `F ≤ S†`
  (`VonNeumannAlgebra.relativeTomita_commutant_le_adjoint`) and `S_{η,ξ}` is closable
  (`VonNeumannAlgebra.isClosable_relativeTomita`).
* Transformation rules, as operator identities:
  `S_{w′ η, ξ} = w′ S_{η,ξ}` for `w′ ∈ M′` (`relativeTomita_apply_left`),
  `S_{a η, ξ} = a S_{η,ξ}` (`relativeTomita_smul_left`),
  `S_{η, c ξ} = c̄⁻¹ S_{η,ξ}` for `c ≠ 0` (`relativeTomita_smul_right`) and
  `S_{η, w′ ξ} = S_{η,ξ} w′⋆` for `w′ ∈ M′` with `w′⋆ w′ ξ = ξ` (`relativeTomita_apply_right`).

## Notation

`S[M]⟦η, ξ⟧` is `VonNeumannAlgebra.relativeTomita M η ξ`; activate it with
`open scoped VonNeumannAlgebra`.

## References

* H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976).
* H. Araki, T. Masuda, *Positive cones and Lp-spaces for von Neumann algebras*, Publ. RIMS 18
  (1982), §2.
* M. Ohya, D. Petz, *Quantum Entropy and Its Use*, Springer (1993), Ch. 2 and 5.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace ComplexConjugate VonNeumannAlgebra LinearPMap
open InnerProductSpace (cyclicSubspace)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (η ξ : H)

/-- The graph `{(x ξ + ζ, s(ξ) x⋆ η) | x ∈ M, ζ ⊥ [M ξ]}` of the relative Tomita operator, a real
subspace of `H × H`. -/
def relativeTomitaGraph : Submodule ℝ (H × H) where
  carrier := {p | ∃ x ∈ M, ∃ ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ,
    p = (x ξ + ζ, M.supportProj ξ (star x η))}
  add_mem' := by
    rintro _ _ ⟨x, hx, ζ, hζ, rfl⟩ ⟨y, hy, ζ', hζ', rfl⟩
    refine ⟨x + y, add_mem hx hy, ζ + ζ', add_mem hζ hζ', ?_⟩
    simp only [Prod.mk_add_mk, add_apply, star_add, map_add]
    abel_nf
  zero_mem' := ⟨0, zero_mem M, 0, zero_mem _, by simp; rfl⟩
  smul_mem' := by
    rintro r _ ⟨x, hx, ζ, hζ, rfl⟩
    refine ⟨(r : ℂ) • x, SMulMemClass.smul_mem _ hx, (r : ℂ) • ζ, Submodule.smul_mem _ _ hζ, ?_⟩
    simp only [Prod.smul_mk, star_smul, smul_apply, smul_add, Complex.coe_smul, star_trivial,
      ContinuousLinearMap.map_smul_of_tower]

variable {M η ξ}

/-- `(x ξ + ζ, s(ξ) x⋆ η)` lies in the graph for `x ∈ M` and `ζ ⊥ [M ξ]`. -/
lemma mk_mem_relativeTomitaGraph {x : H →L[ℂ] H} (hx : x ∈ M) {ζ : H}
    (hζ : ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ) :
    (x ξ + ζ, M.supportProj ξ (star x η)) ∈ M.relativeTomitaGraph η ξ :=
  ⟨x, hx, ζ, hζ, rfl⟩

/-- The graph is that of a function: `x ξ + ζ = 0` forces `x ξ = 0`, hence `s(ξ) x⋆ = 0`. -/
lemma relativeTomitaGraph_snd_eq_zero_of_fst_eq_zero {p : H × H} (hp : p ∈ M.relativeTomitaGraph η ξ)
    (hp0 : p.1 = 0) : p.2 = 0 := by
  obtain ⟨x, hx, ζ, hζ, rfl⟩ := hp
  have hxK : x ξ ∈ (cyclicSubspace M ξ).toSubmodule :=
    InnerProductSpace.apply_mem_cyclicSubspace ξ hx
  have hxξ : x ξ = 0 := by
    have h : ζ = -x ξ := eq_neg_of_add_eq_zero_right hp0
    rw [h, neg_mem_iff] at hζ
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hxK hζ)
  change M.supportProj ξ (star x η) = 0
  rw [← mul_apply_eq_comp, (supportProj_mul_eq_zero_iff (star_mem hx)).mpr (by rwa [star_star]),
    zero_apply]

variable (M η ξ)

/-- The graph of the relative Tomita operator is invariant under `(u, v) ↦ (c u, c̄ v)`:
`S_{η,ξ}` is conjugate-linear. -/
lemma smul_mem_relativeTomitaGraph (c : ℂ) {u v : H} (h : (u, v) ∈ M.relativeTomitaGraph η ξ) :
    (c • u, starRingEnd ℂ c • v) ∈ M.relativeTomitaGraph η ξ := by
  obtain ⟨x, hx, ζ, hζ, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  convert mk_mem_relativeTomitaGraph (η := η) (SMulMemClass.smul_mem c hx)
    (Submodule.smul_mem _ c hζ) using 2
  · simp [smul_add]
  · simp [star_smul]

/-- The **relative Tomita operator** `S_{η,ξ} : x ξ + ζ ↦ s(ξ) x⋆ η` (`x ∈ M`, `ζ ⊥ [M ξ]`), a
conjugate-linear partially defined operator on `H`. -/
noncomputable def relativeTomita : H →ₛₗ.[starRingEnd ℂ] H :=
  LinearPMap.ofGraphₛₗ (M.relativeTomitaGraph η ξ).toAddSubgroup
    (fun c _ _ h => M.smul_mem_relativeTomitaGraph η ξ c h)
    fun _ h => relativeTomitaGraph_snd_eq_zero_of_fst_eq_zero (p := (0, _)) h rfl

/-- `S[M]⟦η, ξ⟧` is the relative Tomita operator `S_{η,ξ}` of the von Neumann algebra `M`. -/
scoped notation "S[" M "]⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeTomita M η ξ

/-- `S⟦η, ξ⟧` is `S[M]⟦η, ξ⟧` for the algebra `M` fixed in this file. -/
local notation "S⟦" η ", " ξ "⟧" => VonNeumannAlgebra.relativeTomita M η ξ

/-- The graph of `S_{η,ξ}` is `relativeTomitaGraph`. -/
@[simp]
lemma graph_relativeTomita : (S⟦η, ξ⟧).graphₛₗ = (M.relativeTomitaGraph η ξ).toAddSubgroup :=
  LinearPMap.graphₛₗ_ofGraphₛₗ _ _ _

variable {M η ξ}

/-- Membership in the graph of `S_{η,ξ}`. -/
lemma mem_graph_relativeTomita {p : H × H} :
    p ∈ (S⟦η, ξ⟧).graphₛₗ ↔ ∃ x ∈ M,
      ∃ ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ,
        p = (x ξ + ζ, M.supportProj ξ (star x η)) := by
  rw [graph_relativeTomita]
  rfl

/-- The domain of `S_{η,ξ}` is `M ξ + [M ξ]ᗮ`. -/
lemma mem_domain_relativeTomita_iff {u : H} :
    u ∈ (S⟦η, ξ⟧).domain ↔ ∃ x ∈ M,
      ∃ ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ, u = x ξ + ζ := by
  rw [LinearPMap.mem_domain_iff_exists_mem_graphₛₗ]
  simp only [mem_graph_relativeTomita, Prod.ext_iff]
  exact ⟨fun ⟨_, x, hx, ζ, hζ, h, _⟩ => ⟨x, hx, ζ, hζ, h⟩,
    fun ⟨x, hx, ζ, hζ, h⟩ => ⟨_, x, hx, ζ, hζ, h, rfl⟩⟩

/-- The domain of `S_{η,ξ}` does not depend on `η`. -/
lemma domain_relativeTomita_eq (η' : H) :
    (S⟦η, ξ⟧).domain = (S⟦η', ξ⟧).domain :=
  Submodule.ext fun _ => mem_domain_relativeTomita_iff.trans mem_domain_relativeTomita_iff.symm

/-- `S_{η,ξ} (x ξ + ζ) = s(ξ) x⋆ η`, in graph form. -/
lemma mk_mem_graph_relativeTomita {x : H →L[ℂ] H} (hx : x ∈ M) {ζ : H}
    (hζ : ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ) :
    (x ξ + ζ, M.supportProj ξ (star x η)) ∈ (S⟦η, ξ⟧).graphₛₗ := by
  rw [graph_relativeTomita]
  exact mk_mem_relativeTomitaGraph hx hζ

/-- `S_{η,ξ} (x ξ) = s(ξ) x⋆ η`, in graph form. -/
lemma apply_mem_graph_relativeTomita {x : H →L[ℂ] H} (hx : x ∈ M) :
    (x ξ, M.supportProj ξ (star x η)) ∈ (S⟦η, ξ⟧).graphₛₗ := by
  simpa using mk_mem_graph_relativeTomita (η := η) hx (zero_mem _)

variable (M η ξ)

/-- `S_{η,ξ} ξ = s(ξ) η`, in graph form. -/
lemma self_mem_graph_relativeTomita : (ξ, M.supportProj ξ η) ∈ (S⟦η, ξ⟧).graphₛₗ := by
  simpa using apply_mem_graph_relativeTomita (η := η) (ξ := ξ) (one_mem M)

/-- `S_{η,ξ}` is densely defined: its domain `M ξ + [M ξ]ᗮ` is dense. -/
lemma dense_domain_relativeTomita : Dense ((S⟦η, ξ⟧).domain : Set H) := by
  set K := (cyclicSubspace M ξ).toSubmodule
  have hdom : ∀ x ∈ M, ∀ ζ ∈ Kᗮ, x ξ + ζ ∈ (S⟦η, ξ⟧).domain := fun x hx ζ hζ =>
    LinearPMap.mem_domain_of_mem_graphₛₗ (mk_mem_graph_relativeTomita (η := η) hx hζ)
  intro w
  -- `w = P w + (w - P w)` with `P w ∈ [M ξ]` and `w - P w ∈ [M ξ]ᗮ`.
  have hPw : K.starProjection w ∈ closure (Set.range fun x : M => (x : H →L[ℂ] H) ξ) := by
    rw [← coe_cyclicSubspace]
    exact K.starProjection_apply_mem w
  have hw : w = K.starProjection w + (w - K.starProjection w) := by abel
  rw [hw]
  refine map_mem_closure (f := fun y => y + (w - K.starProjection w))
    (continuous_id.add continuous_const) hPw ?_
  rintro _ ⟨x, rfl⟩
  exact hdom x x.2 _ (K.sub_starProjection_mem_orthogonal w)

variable {M η ξ} in
/-- **Adjoint relation.** For `(u, S u)` in the graph of `S = S_{η,ξ}` and `(v, F v)` in the graph
of `F = F_{η,ξ}`, the relative Tomita operator of the commutant, `⟪S u, v⟫ = ⟪F v, u⟫`: both are
`⟪η, x x′ ξ⟫` for `u = x ξ + ζ`, `v = x′ ξ + ζ′`. -/
lemma inner_eq_of_mem_graph_relativeTomita {u u' v v' : H}
    (hu : (u, u') ∈ (S⟦η, ξ⟧).graphₛₗ) (hv : (v, v') ∈ (S[M′]⟦η, ξ⟧).graphₛₗ) :
    ⟪u', v⟫_ℂ = ⟪v', u⟫_ℂ := by
  obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp hu
  obtain ⟨y, hy, ζ', hζ', h'⟩ := mem_graph_relativeTomita.mp hv
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h'
  -- `s(ξ) = P_{[M′ ξ]}` fixes `y ξ` and kills `ζ′`; `s′(ξ) = P_{[M ξ]}` fixes `x ξ` and kills `ζ`.
  have hs : M.supportProj ξ (y ξ + ζ') = y ξ := by
    rw [map_add, supportProj, Submodule.starProjection_eq_self_iff.mpr
      (InnerProductSpace.apply_mem_cyclicSubspace ξ hy),
      (Submodule.starProjection_apply_eq_zero_iff (K := _)).mpr hζ', add_zero]
  have hs' : M′.supportProj ξ (x ξ + ζ) = x ξ := by
    rw [map_add, supportProj_commutant, Submodule.starProjection_eq_self_iff.mpr
      (InnerProductSpace.apply_mem_cyclicSubspace ξ hx),
      (Submodule.starProjection_apply_eq_zero_iff (K := _)).mpr hζ, add_zero]
  have hsa : ∀ (N : VonNeumannAlgebra H) (a b : H),
      ⟪N.supportProj ξ a, b⟫_ℂ = ⟪a, N.supportProj ξ b⟫_ℂ := fun N a b => by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      (N.isStarProjection_supportProj ξ).isSelfAdjoint.star_eq]
  rw [hsa, hs, hsa, hs', ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    ← mul_apply_eq_comp, ← mul_apply_eq_comp, mem_commutant_iff.mp hy x hx]

/-- `S_{η,ξ}` and the relative Tomita operator `F_{η,ξ}` of `M′` are formal adjoints:
`⟪S u, v⟫ = conj ⟪u, F v⟫`. -/
lemma isFormalAdjoint_relativeTomita :
    (S⟦η, ξ⟧).IsFormalAdjointₛₗ (S[M′]⟦η, ξ⟧) := fun u v => by
  have h := inner_eq_of_mem_graph_relativeTomita ((S⟦η, ξ⟧).mem_graphₛₗ u)
    ((S[M′]⟦η, ξ⟧).mem_graphₛₗ v)
  rw [h, inner_conj_symm]

/-- The relative Tomita operator of the commutant is contained in the adjoint of `S_{η,ξ}`. -/
lemma relativeTomita_commutant_le_adjoint :
    S[M′]⟦η, ξ⟧ ≤ (S⟦η, ξ⟧).adjointₛₗ :=
  (isFormalAdjoint_relativeTomita M η ξ).le_adjointₛₗ (dense_domain_relativeTomita M η ξ)

/-- `S_{η,ξ}` is closable: its adjoint contains the densely defined `F_{η,ξ}`. -/
theorem isClosable_relativeTomita : (S⟦η, ξ⟧).IsClosableₛₗ :=
  (LinearPMap.isClosableₛₗ_iff_dense_adjointₛₗ_domain (dense_domain_relativeTomita M η ξ)).mpr
    ((dense_domain_relativeTomita M′ η ξ).mono (relativeTomita_commutant_le_adjoint M η ξ).1)

/-! ### Transformation rules -/

variable {M η ξ} {u v : H} {w : H →L[ℂ] H}

/-- `S_{w′ η, ξ} = w′ S_{η,ξ}`, pointwise. -/
private lemma mem_graph_relativeTomita_apply_left_iff (hw : w ∈ M′) :
    (u, v) ∈ (S⟦w η, ξ⟧).graphₛₗ ↔
      ∃ v₀, (u, v₀) ∈ (S⟦η, ξ⟧).graphₛₗ ∧ w v₀ = v := by
  have key : ∀ x ∈ M, M.supportProj ξ (star x (w η)) = w (M.supportProj ξ (star x η)) :=
    fun x hx => by
      rw [← apply_apply_of_mem_commutant hw (star_mem hx),
        ← apply_apply_of_mem_commutant hw (M.supportProj_mem ξ)]
  refine ⟨fun h => ?_, fun ⟨v₀, h, hv⟩ => ?_⟩
  · obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    exact ⟨_, mk_mem_graph_relativeTomita hx hζ, (key x hx).symm⟩
  · obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    rw [← hv, ← key x hx]
    exact mk_mem_graph_relativeTomita hx hζ

/-- Replacing `η` by `w′ η` for `w′ ∈ M′`: `S_{w′ η, ξ} = w′ S_{η,ξ}`. -/
lemma relativeTomita_apply_left (hw : w ∈ M′) :
    S⟦w η, ξ⟧ = (w : H →ₗ[ℂ] H).compPMap S⟦η, ξ⟧ :=
  LinearPMap.eq_of_eq_graphₛₗ <| AddSubgroup.ext fun ⟨_, _⟩ => by
    rw [mem_graph_relativeTomita_apply_left_iff hw, LinearPMap.mem_graphₛₗ_compPMap]
    rfl

/-- `S_{a η, ξ} = a S_{η,ξ}`, pointwise. -/
private lemma mem_graph_relativeTomita_smul_left_iff (a : ℂ) :
    (u, v) ∈ (S⟦a • η, ξ⟧).graphₛₗ ↔
      ∃ v₀, (u, v₀) ∈ (S⟦η, ξ⟧).graphₛₗ ∧ a • v₀ = v := by
  have hw : a • (1 : H →L[ℂ] H) ∈ M′ := SMulMemClass.smul_mem a (one_mem M′)
  simpa using mem_graph_relativeTomita_apply_left_iff (η := η) (u := u) (v := v) hw

/-- Scaling `η`: `S_{a η, ξ} = a S_{η,ξ}`. -/
lemma relativeTomita_smul_left (a : ℂ) :
    S⟦a • η, ξ⟧ = a • S⟦η, ξ⟧ :=
  LinearPMap.eq_of_eq_graphₛₗ <| AddSubgroup.ext fun ⟨_, _⟩ => by
    rw [mem_graph_relativeTomita_smul_left_iff, LinearPMap.mem_graphₛₗ_smul]

/-- `S_{η, c ξ} = c̄⁻¹ S_{η,ξ}`, pointwise. -/
private lemma mem_graph_relativeTomita_smul_right_iff {c : ℂ} (hc : c ≠ 0) :
    (u, v) ∈ (S⟦η, c • ξ⟧).graphₛₗ ↔
      ∃ v₀, (u, v₀) ∈ (S⟦η, ξ⟧).graphₛₗ ∧ (conj c)⁻¹ • v₀ = v := by
  have hK := InnerProductSpace.cyclicSubspace_smul (M : Set (H →L[ℂ] H)) ξ hc
  have hc' : conj c ≠ 0 := (map_ne_zero _).mpr hc
  refine ⟨fun h => ?_, fun ⟨v₀, h, hv⟩ => ?_⟩
  · obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    rw [hK] at hζ
    refine ⟨M.supportProj ξ (star (c • x) η), ?_, ?_⟩
    · convert mk_mem_graph_relativeTomita (η := η) (SMulMemClass.smul_mem c hx) hζ using 2
      rw [smul_apply, map_smul]
    · rw [star_smul, smul_apply, map_smul, Complex.star_def, inv_smul_smul₀ hc', supportProj_smul hc]
  · obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    rw [← hK] at hζ
    convert mk_mem_graph_relativeTomita (η := η) (SMulMemClass.smul_mem c⁻¹ hx) hζ using 2
    · rw [smul_apply, map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
    · rw [← hv, star_smul, smul_apply, map_smul, Complex.star_def, map_inv₀, supportProj_smul hc]

/-- Scaling `ξ` by `c ≠ 0`: `S_{η, c ξ} = c̄⁻¹ S_{η,ξ}`. -/
lemma relativeTomita_smul_right {c : ℂ} (hc : c ≠ 0) :
    S⟦η, c • ξ⟧ = (conj c)⁻¹ • S⟦η, ξ⟧ :=
  LinearPMap.eq_of_eq_graphₛₗ <| AddSubgroup.ext fun ⟨_, _⟩ => by
    rw [mem_graph_relativeTomita_smul_right_iff hc, LinearPMap.mem_graphₛₗ_smul]

/-- `S_{η, w′ ξ} = S_{η,ξ} w′⋆`, pointwise. -/
private lemma mem_graph_relativeTomita_apply_right_iff (hw : w ∈ M′) (hwξ : star w (w ξ) = ξ) :
    (u, v) ∈ (S⟦η, w ξ⟧).graphₛₗ ↔ (star w u, v) ∈ (S⟦η, ξ⟧).graphₛₗ := by
  have hw' : star w ∈ M′ := star_mem hw
  have hs := supportProj_apply_of_mem_commutant (M := M) hw hwξ
  -- `⟪a ξ, w⋆ z⟫ = ⟪a (w ξ), z⟫` for `a ∈ M`.
  have hinner : ∀ a ∈ M, ∀ z, ⟪a ξ, star w z⟫_ℂ = ⟪a (w ξ), z⟫_ℂ := fun a ha z => by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      apply_apply_of_mem_commutant hw ha]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, hy, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
    have hζ' : star w ζ ∈ (cyclicSubspace M ξ).toSubmoduleᗮ := by
      rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
      exact fun a ha => (hinner a ha ζ).trans (hζ a ha)
    convert mk_mem_graph_relativeTomita (η := η) hy hζ' using 2
    · rw [map_add, apply_apply_of_mem_commutant hw' hy, hwξ]
    · rw [hs]
  · obtain ⟨x, hx, ζ, hζ, h⟩ := mem_graph_relativeTomita.mp h
    obtain ⟨h₁, rfl⟩ := Prod.ext_iff.mp h
    dsimp only at h₁
    -- `u = x (w′ ξ) + (u - x (w′ ξ))` with `u - x (w′ ξ) ⊥ [M w′ ξ]`.
    have hζ' : u - x (w ξ) ∈ (cyclicSubspace M (w ξ)).toSubmoduleᗮ := by
      rw [InnerProductSpace.mem_orthogonal_cyclicSubspace_iff] at hζ ⊢
      intro a ha
      have h₂ : ⟪a (w ξ), x (w ξ)⟫_ℂ = ⟪a ξ, x ξ⟫_ℂ := by
        rw [← hinner a ha, apply_apply_of_mem_commutant hw' hx, hwξ]
      rw [inner_sub_right, ← hinner a ha, h₁, inner_add_right, hζ a ha, add_zero, h₂, sub_self]
    convert mk_mem_graph_relativeTomita (η := η) hx hζ' using 2
    · abel
    · rw [hs]

/-- Replacing `ξ` by `w′ ξ` for `w′ ∈ M′` with `w′⋆ w′ ξ = ξ`: `S_{η, w′ ξ} = S_{η,ξ} w′⋆`. -/
lemma relativeTomita_apply_right (hw : w ∈ M′) (hwξ : star w (w ξ) = ξ) :
    S⟦η, w ξ⟧ = S⟦η, ξ⟧.compNat (((star w : H →L[ℂ] H) : H →ₗ[ℂ] H).toPMap ⊤) :=
  LinearPMap.eq_of_eq_graphₛₗ <| AddSubgroup.ext fun ⟨_, _⟩ => by
    rw [mem_graph_relativeTomita_apply_right_iff hw hwξ, LinearPMap.mem_graphₛₗ_compNat_toPMap]
    rfl

end VonNeumannAlgebra
