/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Nuclear
public import QuantumSystem.ForMathlib.Algebra.Star.TensorProductMap

/-!
# Nuclearity of inductive limits

A C⋆-algebra in which the images of a directed family of nuclear C⋆-algebras under injective
`⋆`-homomorphisms have dense union is nuclear: a tensor `∑ aᵢ ⊗ bᵢ` is approximated by one whose
first factors lie in a single image, where nuclearity applies, and both a C⋆-seminorm and the norm
of the minimal tensor product are cross norms, the latter preserved by injective
`⋆`-homomorphisms.

## Main results

* `CStarAlgebra.IsNuclear.of_dense_iUnion` — the permanence of nuclearity under inductive limits along
  injective `⋆`-homomorphisms.

## Not formalized

* The same for `⋆`-homomorphisms that need not be injective. It is equivalent to the permanence of
  nuclearity under quotients: the image of each algebra is a quotient of it, and a quotient map is
  the case of a single algebra.
-/

@[expose] public section

open scoped TensorProduct MinTensorProduct

universe u v w

namespace CStarAlgebra.IsNuclear

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- A `⋆`-homomorphism of `A ⊗[ℂ] B` into a C⋆-algebra changes by at most `δ ∑ ‖bᵢ‖` when the
first factors of `∑ aᵢ ⊗ bᵢ` move by at most `δ`. -/
private lemma norm_apply_sum_sub_tmul_le {B C : Type*} [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (S : Finset (A × B)) (g : A × B → A)
    {δ : ℝ} (hg : ∀ i ∈ S, ‖i.1 - g i‖ ≤ δ) :
    ‖Φ (∑ i ∈ S, (i.1 - g i) ⊗ₜ[ℂ] i.2)‖ ≤ δ * ∑ i ∈ S, ‖i.2‖ := by
  rw [map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  refine (NonUnitalStarAlgHom.norm_apply_tmul_le Φ _ _).trans ?_
  gcongr
  exact hg i hi

/-- Finitely many elements are approximated within `δ` in the image of a single member of a
directed family whose images have dense union. -/
private lemma exists_approx {κ : Type*} {G : κ → Type*} [∀ k, NonUnitalCStarAlgebra (G k)]
    (ι : ∀ k, G k →⋆ₙₐ[ℂ] A) (hdir : Directed (· ≤ ·) fun k => NonUnitalStarAlgHom.range (ι k))
    (hdense : Dense (⋃ k, Set.range (ι k))) (S : Finset A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k, ∀ a ∈ S, ∃ g : G k, ‖a - ι k g‖ < δ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨_, hy⟩ := hdense.nonempty
    obtain ⟨k, -⟩ := Set.mem_iUnion.1 hy
    exact ⟨k, by simp⟩
  | insert a S _ ih =>
    obtain ⟨k₁, hk₁⟩ := ih
    obtain ⟨y, hay, hy⟩ := Metric.dense_iff.1 hdense a δ hδ
    obtain ⟨k₂, g₂, rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨k, h₁, h₂⟩ := hdir k₁ k₂
    refine ⟨k, fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · obtain ⟨g, hg⟩ := h₂ (NonUnitalStarAlgHom.mem_range_self (ι k₂) g₂)
      replace hg : ι k g = ι k₂ g₂ := hg
      refine ⟨g, ?_⟩
      rw [hg, ← dist_eq_norm, dist_comm]
      exact Metric.mem_ball.1 hay
    · obtain ⟨g₁, hg₁⟩ := hk₁ b hb
      obtain ⟨g, hg⟩ := h₁ (NonUnitalStarAlgHom.mem_range_self (ι k₁) g₁)
      replace hg : ι k g = ι k₁ g₁ := hg
      exact ⟨g, by rwa [hg]⟩

/-- **Nuclearity passes to inductive limits along injective `⋆`-homomorphisms**: a C⋆-algebra in
which the images of a directed family of nuclear C⋆-algebras under injective `⋆`-homomorphisms have
dense union is nuclear. -/
theorem of_dense_iUnion {κ : Type*} {G : κ → Type*} [∀ k, NonUnitalCStarAlgebra (G k)]
    [∀ k, IsNuclear.{v, w} (G k)] (ι : ∀ k, G k →⋆ₙₐ[ℂ] A) (hι : ∀ k, Function.Injective (ι k))
    (hdir : Directed (· ≤ ·) fun k => NonUnitalStarAlgHom.range (ι k))
    (hdense : Dense (⋃ k, Set.range (ι k))) : IsNuclear.{v, w} A := by
  classical
  refine ⟨fun B _ C _ Φ z => ?_⟩
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  set L := ∑ i ∈ S, ‖i.2‖
  set z := ∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (2 * (L + 1)) := by positivity
  obtain ⟨k, hk⟩ := exists_approx ι hdir hdense (S.image Prod.fst) hδ
  have hk' (i : A × B) (hi : i ∈ S) : ∃ g : G k, ‖i.1 - ι k g‖ < ε / (2 * (L + 1)) :=
    hk i.1 (Finset.mem_image_of_mem _ hi)
  choose! g hg using hk'
  set w := ∑ i ∈ S, g i ⊗ₜ[ℂ] i.2
  set Ψ := NonUnitalStarAlgebra.TensorProduct.map (ι k) (NonUnitalStarAlgHom.id ℂ B)
  have hΨ : Ψ w = ∑ i ∈ S, ι k (g i) ⊗ₜ[ℂ] i.2 := by simp [Ψ, w, map_sum]
  have hdiff : z - Ψ w = ∑ i ∈ S, (i.1 - ι k (g i)) ⊗ₜ[ℂ] i.2 := by
    rw [hΨ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.sub_tmul _ _ _).symm
  have hle : ∀ i ∈ S, ‖i.1 - ι k (g i)‖ ≤ ε / (2 * (L + 1)) := fun i hi => (hg i hi).le
  have hsmall : ε / (2 * (L + 1)) * L ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [Finset.sum_nonneg fun i (_ : i ∈ S) => norm_nonneg i.2]
  have herrΦ : ‖Φ (z - Ψ w)‖ ≤ ε / 2 := by
    rw [hdiff]
    exact (norm_apply_sum_sub_tmul_le Φ S (fun i => ι k (g i)) hle).trans hsmall
  have herrof : ‖MinTensorProduct.of A B (z - Ψ w)‖ ≤ ε / 2 := by
    rw [hdiff]
    exact (norm_apply_sum_sub_tmul_le (MinTensorProduct.of A B) S (fun i => ι k (g i)) hle).trans
      hsmall
  have hmin : ‖MinTensorProduct.of (G k) B w‖ = ‖MinTensorProduct.of A B (Ψ w)‖ := by
    rw [← MinTensorProduct.norm_map_of_injective (hι k)
      (fun _ _ h => h : Function.Injective (NonUnitalStarAlgHom.id ℂ B))
      (MinTensorProduct.of (G k) B w), MinTensorProduct.map_of]
    rfl
  have hnuc : ‖Φ (Ψ w)‖ ≤ ‖MinTensorProduct.of A B (Ψ w)‖ :=
    (norm_apply_le_norm_of B C (Φ.comp Ψ) w).trans hmin.le
  calc ‖Φ z‖ = ‖Φ (Ψ w) + Φ (z - Ψ w)‖ := by rw [← map_add, add_sub_cancel]
    _ ≤ ‖Φ (Ψ w)‖ + ‖Φ (z - Ψ w)‖ := norm_add_le _ _
    _ ≤ ‖MinTensorProduct.of A B (Ψ w)‖ + ε / 2 := add_le_add hnuc herrΦ
    _ = ‖MinTensorProduct.of A B z - MinTensorProduct.of A B (z - Ψ w)‖ + ε / 2 := by
        rw [← map_sub, sub_sub_cancel]
    _ ≤ ‖MinTensorProduct.of A B z‖ + ‖MinTensorProduct.of A B (z - Ψ w)‖ + ε / 2 := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖MinTensorProduct.of A B z‖ + ε / 2 + ε / 2 := by
        gcongr
    _ = ‖MinTensorProduct.of A B z‖ + ε := by ring

end CStarAlgebra.IsNuclear
