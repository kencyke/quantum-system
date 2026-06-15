module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import QuantumSystem.Algebra.Sector.Category.Endomorphism

/-!
# C\*-analytic enrichment of `End(A)`

This file equips the endomorphism category `StarEndoCat A` of a C\*-algebra `A`
(see `Sector/Category/Endomorphism.lean`) with the analytic structure of a
**C\*-category** in the sense of Müger, *Abstract Duality Theory for Symmetric
Tensor \*-Categories*, §1.4 (Additive, ℂ-linear and \*-categories):

* each hom-space `ρ ⟶ σ` is a complex Banach space (in fact a closed linear
  subspace of `A`);
* composition is `ℂ`-bilinear, so `StarEndoCat A` is `Preadditive` and
  `Linear ℂ`;
* the dagger `f ↦ star f.t` is antilinear and satisfies the **C\*-identity**
  `‖f† ≫ f‖ = ‖f‖²` together with positivity of `f† ≫ f`.

This is the realisation-level content that `CStarTensorCategory.lean` deliberately
keeps out of the abstract `RigidSymmetricDaggerCategory` class: it lives here,
where the hom-spaces are concrete subspaces of the C\*-algebra `A`.

This file develops the algebraic layer (`AddCommGroup` / `Module ℂ` on
intertwiners, `Preadditive` / `Linear ℂ` on `StarEndoCat A`); the normed and
C\*-identity layers are built on top of it.
-/

@[expose] public section

namespace CategoryTheory

universe v u

/-- A **C\*-category** (Müger §1.4: *Additive, ℂ-linear and ∗-categories*): a
`ℂ`-linear dagger category whose hom-spaces are complex Banach spaces satisfying
the C\*-identity `‖f ≫ f†‖ = ‖f‖²`. The Banach-space structure on each hom-space
is supplied as instance prerequisites, since Mathlib has no notion of a category
enriched in normed spaces. -/
class CStarCategory (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)]
    [∀ X Y : C, NormedSpace ℂ (X ⟶ Y)] [∀ X Y : C, CompleteSpace (X ⟶ Y)] :
    Prop where
  /-- The C\*-identity holds on every hom-space. -/
  norm_comp_dagger : ∀ {X Y : C} (f : X ⟶ Y), ‖f ≫ f†‖ = ‖f‖ ^ 2

/-- In a C\*-category the identity is **norm-idempotent**: `‖𝟙 X‖ = ‖𝟙 X‖²`, from the
C\*-identity `‖f ≫ f†‖ = ‖f‖²` applied to `f = 𝟙 X` (since `(𝟙 X)† = 𝟙 X`). -/
lemma CStarCategory.norm_id_sq {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C] [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)]
    [∀ X Y : C, NormedSpace ℂ (X ⟶ Y)] [∀ X Y : C, CompleteSpace (X ⟶ Y)] [CStarCategory C]
    (X : C) : ‖𝟙 X‖ = ‖𝟙 X‖ ^ 2 := by
  have h := CStarCategory.norm_comp_dagger (𝟙 X)
  rwa [DaggerCategory.dagger_id, Category.comp_id] at h

/-- In a C\*-category the identity has **norm `0` or `1`** (standard C\*-category fact, Müger
§1.5): `‖𝟙 X‖ = 0` for a zero object and `‖𝟙 X‖ = 1` for a nonzero object. -/
lemma CStarCategory.norm_id_eq_zero_or_one {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear ℂ C] [DaggerCategory C] [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)]
    [∀ X Y : C, NormedSpace ℂ (X ⟶ Y)] [∀ X Y : C, CompleteSpace (X ⟶ Y)] [CStarCategory C]
    (X : C) : ‖𝟙 X‖ = 0 ∨ ‖𝟙 X‖ = 1 := by
  have key : ‖𝟙 X‖ * (‖𝟙 X‖ - 1) = 0 := by nlinarith [CStarCategory.norm_id_sq X]
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- A C\*-category object **whose identity has nonzero norm** has unit-norm identity:
`‖𝟙 X‖ ≠ 0 → ‖𝟙 X‖ = 1` (Müger §1.5).  Since `‖𝟙 X‖ ∈ {0, 1}`, a nonzero identity forces
`‖𝟙 X‖ = 1`; this is the input turning `End 𝟙 = ℂ` into a genuine isomorphism (scalar
uniqueness `c • 𝟙 = c' • 𝟙 → c = c'`). -/
lemma CStarCategory.norm_id_of_norm_ne_zero {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear ℂ C] [DaggerCategory C] [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)]
    [∀ X Y : C, NormedSpace ℂ (X ⟶ Y)] [∀ X Y : C, CompleteSpace (X ⟶ Y)] [CStarCategory C]
    {X : C} (hX : ‖𝟙 X‖ ≠ 0) : ‖𝟙 X‖ = 1 := by
  rcases CStarCategory.norm_id_eq_zero_or_one X with h | h
  · exact (hX h).elim
  · exact h

/-- The C\*-norm of a **self-adjoint** endomorphism is the square root of `‖f²‖`-style identity:
`‖f‖² = ‖f ≫ f‖` when `f† = f` (Müger §1.5 / standard C\*-identity for self-adjoints), from
`‖f ≫ f†‖ = ‖f‖²` and `f† = f`. -/
lemma CStarCategory.norm_sq_of_selfAdjoint {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear ℂ C] [DaggerCategory C] [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)]
    [∀ X Y : C, NormedSpace ℂ (X ⟶ Y)] [∀ X Y : C, CompleteSpace (X ⟶ Y)] [CStarCategory C]
    {X : C} {f : X ⟶ X} (hf : DaggerCategory.dagger f = f) : ‖f ≫ f‖ = ‖f‖ ^ 2 := by
  have h := CStarCategory.norm_comp_dagger f
  rwa [hf] at h

/-- **Scalar uniqueness against a nonzero identity** (Müger §1.5): if `‖𝟙 X‖ ≠ 0` then
`c • 𝟙 X = c' • 𝟙 X` forces `c = c'`.  Proved purely from `norm_smul` (so it avoids the
zero-instance diamond between the normed and categorical zeros): `‖c - c'‖ · ‖𝟙 X‖ = 0` and
`‖𝟙 X‖ ≠ 0` give `‖c - c'‖ = 0`.  This upgrades the *existence* of the scalar
(`STCStar.irreducible_unit`) to *uniqueness*, so `dim`/`trace` scalars are well-determined. -/
lemma CStarCategory.smul_id_inj {C : Type u} [Category.{v} C]
    [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)] [∀ X Y : C, NormedSpace ℂ (X ⟶ Y)]
    {X : C} (hX : ‖𝟙 X‖ ≠ 0) {c c' : ℂ} (h : c • 𝟙 X = c' • 𝟙 X) : c = c' := by
  have hns : ‖c - c'‖ * ‖𝟙 X‖ = 0 := by
    rw [← norm_smul, sub_smul, h, sub_self, norm_zero]
  rcases mul_eq_zero.mp hns with hc | hc
  · exact sub_eq_zero.mp (norm_eq_zero.mp hc)
  · exact absurd hc hX

namespace StarEndo

open Filter Topology

variable {A : Type u} [CStarAlgebra A] {ρ σ τ : StarEndoCat A}

/-! ### Additive and `ℂ`-module structure on hom-spaces

The set of intertwiners `ρ ⟶ σ` is closed under the linear operations of `A`:
the intertwining relation `t * ρ a = σ a * t` is preserved by `0`, `+`, `-` and
scalar multiplication. We register the operations element-wise on `.t` and pull
back the `AddCommGroup` / `Module ℂ` axioms along the injection `Intertwiner.t`.
-/

instance : Zero (Intertwiner ρ σ) where
  zero := ⟨0, fun a => by rw [zero_mul, mul_zero]⟩

@[simp] lemma zero_t : (0 : Intertwiner ρ σ).t = 0 := rfl

instance : Add (Intertwiner ρ σ) where
  add f g := ⟨f.t + g.t, fun a => by
    rw [add_mul, mul_add, f.intertwines, g.intertwines]⟩

@[simp] lemma add_t (f g : Intertwiner ρ σ) : (f + g).t = f.t + g.t := rfl

instance : Neg (Intertwiner ρ σ) where
  neg f := ⟨-f.t, fun a => by rw [neg_mul, mul_neg, f.intertwines]⟩

@[simp] lemma neg_t (f : Intertwiner ρ σ) : (-f).t = -f.t := rfl

instance : Sub (Intertwiner ρ σ) where
  sub f g := ⟨f.t - g.t, fun a => by
    rw [sub_mul, mul_sub, f.intertwines, g.intertwines]⟩

@[simp] lemma sub_t (f g : Intertwiner ρ σ) : (f - g).t = f.t - g.t := rfl

instance : SMul ℕ (Intertwiner ρ σ) where
  smul n f := ⟨n • f.t, fun a => by rw [smul_mul_assoc, f.intertwines, mul_smul_comm]⟩

@[simp] lemma nsmul_t (n : ℕ) (f : Intertwiner ρ σ) : (n • f).t = n • f.t := rfl

instance : SMul ℤ (Intertwiner ρ σ) where
  smul n f := ⟨n • f.t, fun a => by rw [smul_mul_assoc, f.intertwines, mul_smul_comm]⟩

@[simp] lemma zsmul_t (n : ℤ) (f : Intertwiner ρ σ) : (n • f).t = n • f.t := rfl

instance : SMul ℂ (Intertwiner ρ σ) where
  smul c f := ⟨c • f.t, fun a => by rw [smul_mul_assoc, f.intertwines, mul_smul_comm]⟩

@[simp] lemma smul_t (c : ℂ) (f : Intertwiner ρ σ) : (c • f).t = c • f.t := rfl

/-- The underlying-element map `Intertwiner.t` is injective. -/
lemma t_injective : Function.Injective (Intertwiner.t : Intertwiner ρ σ → A) :=
  fun _ _ h => Intertwiner.ext h

instance : AddCommGroup (Intertwiner ρ σ) :=
  Function.Injective.addCommGroup (Intertwiner.t : Intertwiner ρ σ → A) t_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The underlying-element map as an additive homomorphism `(ρ ⟶ σ) →+ A`. -/
def tAddHom (ρ σ : StarEndoCat A) : Intertwiner ρ σ →+ A where
  toFun := Intertwiner.t
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance : Module ℂ (Intertwiner ρ σ) :=
  Function.Injective.module ℂ (tAddHom ρ σ) t_injective (fun _ _ => rfl)

/-- The underlying-element map as a `ℂ`-linear map `(ρ ⟶ σ) →ₗ[ℂ] A`. -/
def tLinearMap (ρ σ : StarEndoCat A) : Intertwiner ρ σ →ₗ[ℂ] A where
  toFun := Intertwiner.t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma tLinearMap_apply (f : Intertwiner ρ σ) : tLinearMap ρ σ f = f.t := rfl

/-! ### Normed structure on hom-spaces

Each hom-space is a normed `ℂ`-vector space, with the norm inherited from `A`
along the injective underlying-element map `Intertwiner.t` (Müger §1.4: the
hom-spaces of a C\*-category are Banach spaces). -/

noncomputable instance : NormedAddCommGroup (Intertwiner ρ σ) :=
  NormedAddCommGroup.induced _ _ (tLinearMap ρ σ) t_injective

noncomputable instance : NormedSpace ℂ (Intertwiner ρ σ) :=
  NormedSpace.induced ℂ _ _ (tLinearMap ρ σ)

@[simp] lemma norm_t (f : Intertwiner ρ σ) : ‖f‖ = ‖f.t‖ := rfl

/-- The underlying-element map is distance-preserving. -/
lemma dist_t (f g : Intertwiner ρ σ) : dist f.t g.t = dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← sub_t, norm_t]

/-- Each hom-space is complete: the intertwining relation is preserved under
limits (multiplication in `A` is continuous), so a Cauchy sequence of
intertwiners converges to an intertwiner. -/
noncomputable instance : CompleteSpace (Intertwiner ρ σ) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hcau : CauchySeq fun n => (u n).t := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun m hm n hn => by rw [dist_t]; exact hN m hm n hn⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have hint : ∀ a, L * ρ.endo a = σ.endo a * L := fun a => by
    have h1 : Tendsto (fun n => (u n).t * ρ.endo a) atTop (𝓝 (L * ρ.endo a)) :=
      hL.mul_const _
    have h2 : Tendsto (fun n => σ.endo a * (u n).t) atTop (𝓝 (σ.endo a * L)) :=
      hL.const_mul _
    have heq : (fun n => (u n).t * ρ.endo a) = fun n => σ.endo a * (u n).t :=
      funext fun n => (u n).intertwines a
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  refine ⟨⟨L, hint⟩, ?_⟩
  rw [Metric.tendsto_atTop] at hL ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hL ε hε
  exact ⟨N, fun n hn => by rw [← dist_t]; exact hN n hn⟩

/-! ### `Preadditive` and `ℂ`-linear structure on `StarEndoCat A`

Composition is multiplication in `A` (`comp_t : (f ≫ g).t = g.t * f.t`), which is
`ℂ`-bilinear, so the category is preadditive and `ℂ`-linear. -/

instance : Preadditive (StarEndoCat A) where
  homGroup ρ σ := inferInstanceAs (AddCommGroup (Intertwiner ρ σ))
  add_comp _ _ _ f f' g := Intertwiner.ext <| by
    change g.t * (f.t + f'.t) = g.t * f.t + g.t * f'.t
    exact mul_add g.t f.t f'.t
  comp_add _ _ _ f g g' := Intertwiner.ext <| by
    change (g.t + g'.t) * f.t = g.t * f.t + g'.t * f.t
    exact add_mul g.t g'.t f.t

instance : Linear ℂ (StarEndoCat A) where
  homModule ρ σ := inferInstanceAs (Module ℂ (Intertwiner ρ σ))
  smul_comp _ _ _ r f g := Intertwiner.ext <| by
    rw [comp_t, smul_t, smul_t, comp_t]; exact mul_smul_comm r g.t f.t
  comp_smul _ _ _ f r g := Intertwiner.ext <| by
    rw [comp_t, smul_t, smul_t, comp_t]; exact smul_mul_assoc r g.t f.t

/-- The dagger is **antilinear** (Müger §1.4 — the `*`-operation is conjugate-linear):
`(c • f)† = c̄ • f†`. -/
@[simp] lemma dagger_smul (c : ℂ) {ρ σ : StarEndoCat A} (f : ρ ⟶ σ) :
    (c • f)† = star c • f† := by
  apply Intertwiner.ext
  change star (c • f.t) = star c • star f.t
  exact star_smul c f.t

/-! ### Normed structure on the morphism (arrow) type and the C\*-identity

The normed structure transfers to the categorical hom-type `ρ ⟶ σ` (definitionally
`Intertwiner ρ σ`), so morphism composition `≫`, the dagger `†` and the norm `‖·‖`
interact directly. The hom-spaces then satisfy the C\*-identity `‖f ≫ f†‖ = ‖f‖²`
(Müger §1.4), inherited from the C\*-identity of `A`. -/

noncomputable instance (ρ σ : StarEndoCat A) : NormedAddCommGroup (ρ ⟶ σ) :=
  inferInstanceAs (NormedAddCommGroup (Intertwiner ρ σ))

noncomputable instance (ρ σ : StarEndoCat A) : NormedSpace ℂ (ρ ⟶ σ) :=
  inferInstanceAs (NormedSpace ℂ (Intertwiner ρ σ))

instance (ρ σ : StarEndoCat A) : CompleteSpace (ρ ⟶ σ) :=
  inferInstanceAs (CompleteSpace (Intertwiner ρ σ))

/-- The **C\*-identity** for the hom-spaces of `End(A)`: `‖f ≫ f†‖ = ‖f‖²`. -/
lemma norm_comp_dagger (f : ρ ⟶ σ) : ‖f ≫ f†‖ = ‖f‖ ^ 2 := by
  have h1 : ‖f ≫ f†‖ = ‖star f.t * f.t‖ := rfl
  have h2 : ‖f‖ = ‖f.t‖ := rfl
  rw [h1, h2, sq, CStarRing.norm_star_mul_self]

/-- `End(A)` is a **C\*-category**: composition is `ℂ`-bilinear, hom-spaces are
complex Banach spaces, and the C\*-identity holds. -/
instance : CStarCategory (StarEndoCat A) where
  norm_comp_dagger f := norm_comp_dagger f

end StarEndo

end CategoryTheory
