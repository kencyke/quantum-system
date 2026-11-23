/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Physics.LocalNet.Basic

/-!
# Covariances of a net

A **covariance** of a graded-local net over a causal index set `K` is an order automorphism
`σ : K ≃o K` of the regions preserving causal orthogonality, together with, for every region `O`, a
`*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` of local algebras that is natural with respect to the
isotony embeddings and preserves the parity. The naturality field `β_incl` is the AQFT covariance
axiom `β(𝔄(O)) = 𝔄(σO)` compatibly with inclusions (Naaijkens, *Anyons in Infinite Quantum Systems*,
2012, §3.2; Verch, *Lecture Notes on Operator Algebras and Quantum Field Theory*,
arXiv:2507.00900, 2025, §1.2). These
covariances form a `Group` under composition (`Covariance.id`, `Covariance.comp`,
`Covariance.inv`): the automorphism group of the net, with all of its structure.

The parity condition `β_parity` is no condition for a local net, where every map commutes with the
parity (`GradedLocalNet.map_parity`). The parity itself is a covariance leaving every region in
place (`GradedLocalNet.parityCovariance`).

This file isolates the abstract covariance *data* and its group structure; it carries no symmetry
group. A symmetry group `G` acts on the net by supplying a group homomorphism `G →* N.Covariance`
(whose `σ`-component is the geometric action `G → K ≃o K`), and the covariances of a particular
group are in the files importing this one:

* `QuantumSystem.Physics.LocalNet.Covariance.SitePerm` — the permutations of the sites of a
  lattice, which give all the covariances of a lattice net;
* `QuantumSystem.Physics.LocalNet.Covariance.QuasiLocal` — the *action* of the covariances on the
  quasi-local algebra, and the C⋆-dynamical system of a symmetry group acting continuously.

## Notation

`𝔄(O)` in the prose above is documentation shorthand for the local C⋆-algebra `N.algebra O`; the
convention is stated in full in `QuantumSystem.Physics.LocalNet.Isotony`.
-/

@[expose] public section

namespace GradedLocalNet

open scoped CausalOrthogonality

variable {K : Type*} [Preorder K] [CausalOrthogonality K] (N : GradedLocalNet K)

/-! ### Covariances of the net

A covariance of a graded-local net is a causal order automorphism `σ` of the index set together with,
for each region, a `*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` of local algebras that is natural
with respect to the isotony embeddings. This realises the AQFT covariance axiom `β(𝔄(O)) = 𝔄(σO)`
at the abstract net level. Being purely algebraic, the covariance group needs no faithfulness
hypothesis.
-/

/-- A **covariance** of a graded-local net `N`: an order automorphism `σ` of the causal index set
    preserving causal orthogonality (`map_orthogonal_iff`), together with, for every region `O`,
    a `*`-isomorphism `β O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)`, natural with respect to the isotony embeddings
    (`β_incl`). This is the AQFT covariance datum at the abstract net level. -/
structure Covariance where
  /-- The underlying automorphism of the causal index set, carrying the region map `O ↦ σO`. -/
  σ : K ≃o K
  /-- The region automorphism preserves causal orthogonality. Stated as an `iff` so that the
      inverse covariance is again a covariance. -/
  map_orthogonal_iff : ∀ ⦃O₁ O₂ : K⦄, σ O₁ ⟂ σ O₂ ↔ O₁ ⟂ O₂
  /-- The covariance `*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` on each region. -/
  β : ∀ O : K, N.algebra O ≃⋆ₐ[ℂ] N.algebra (σ O)
  /-- **Naturality / covariance**: `β` intertwines the isotony embeddings, so it maps the net to
      itself compatibly with inclusions — the AQFT covariance axiom `β(𝔄(O)) = 𝔄(σO)`. -/
  β_incl : ∀ {O O' : K} (h : O ≤ O') (x : N.algebra O),
      β O' (N.incl h x) = N.incl (σ.monotone h) (β O x)
  /-- The covariance `*`-isomorphisms preserve the parity, so a covariance is a symmetry of the
      graded net. For a local net, whose parity is trivial, this holds for every `β`
      (`GradedLocalNet.map_parity`). -/
  β_parity : ∀ (O : K) (x : N.algebra O), β O (N.parity O x) = N.parity (σ O) (β O x)

namespace Covariance

variable {N} (a : N.Covariance)

/-- **Extensionality** for covariances: two covariances with the same region automorphism and the
    same local `*`-isomorphisms (compared along the induced region equality) are equal. The
    remaining fields are propositions, hence irrelevant. -/
@[ext (iff := false)] lemma ext {s t : N.Covariance} (hσ : s.σ = t.σ)
    (hβ : ∀ (O : K) (x : N.algebra O) (e : s.σ O = t.σ O),
      N.algebraCongr e (s.β O x) = t.β O x) : s = t := by
  revert hσ hβ
  obtain ⟨sσ, -, sβ, -, -⟩ := s
  obtain ⟨tσ, -, tβ, -, -⟩ := t
  rintro rfl hβ
  have hβ' : sβ = tβ := by
    funext O
    ext x
    simpa using hβ O x rfl
  subst hβ'
  rfl

/-- Naturality of the inverse local `*`-isomorphisms with respect to isotony. -/
lemma β_symm_incl {O O' : K} (h : O ≤ O') (y : N.algebra (a.σ O)) :
    (a.β O').symm (N.incl (a.σ.monotone h) y) = N.incl h ((a.β O).symm y) := by
  have key := a.β_incl h ((a.β O).symm y)
  rw [StarAlgEquiv.apply_symm_apply] at key
  rw [← key, StarAlgEquiv.symm_apply_apply]

/-- The inverse local `*`-isomorphisms preserve the parity. -/
lemma β_symm_parity (O : K) (y : N.algebra (a.σ O)) :
    (a.β O).symm (N.parity (a.σ O) y) = N.parity O ((a.β O).symm y) := by
  have key := a.β_parity O ((a.β O).symm y)
  rw [StarAlgEquiv.apply_symm_apply] at key
  rw [← key, StarAlgEquiv.symm_apply_apply]

/-- The local `*`-isomorphisms commute with the region-equality transport. -/
lemma β_algebraCongr {O O' : K} (e : O = O') (x : N.algebra O) :
    a.β O' (N.algebraCongr e x) = N.algebraCongr (by rw [e]) (a.β O x) := by
  subst e; simp

variable (N) in
/-- The **identity covariance**: the identity region automorphism with the identity local
    `*`-isomorphisms. -/
def id : N.Covariance where
  σ := OrderIso.refl K
  map_orthogonal_iff _ _ := Iff.rfl
  β _ := StarAlgEquiv.refl ℂ _
  β_incl _ _ := rfl
  β_parity _ _ := rfl

/-- **Composition of covariances**: apply `b`, then `a`. The region automorphisms compose, and
    the local `*`-isomorphisms compose along them. -/
def comp (a b : N.Covariance) : N.Covariance where
  σ := b.σ.trans a.σ
  map_orthogonal_iff O₁ O₂ :=
    (a.map_orthogonal_iff (O₁ := b.σ O₁) (O₂ := b.σ O₂)).trans
      (b.map_orthogonal_iff (O₁ := O₁) (O₂ := O₂))
  β O := (b.β O).trans (a.β (b.σ O))
  β_incl h x := by
    change a.β (b.σ _) (b.β _ (N.incl h x)) = N.incl _ (a.β (b.σ _) (b.β _ x))
    rw [b.β_incl h]
    exact a.β_incl (b.σ.monotone h) ((b.β _) x)
  β_parity O x := by
    change a.β (b.σ O) (b.β O (N.parity O x)) = N.parity _ (a.β (b.σ O) (b.β O x))
    rw [b.β_parity, a.β_parity]

/-- The **inverse covariance**: the inverse region automorphism with the inverse local
    `*`-isomorphisms, transported along `σ(σ⁻¹O) = O`. -/
def inv (a : N.Covariance) : N.Covariance where
  σ := a.σ.symm
  map_orthogonal_iff O₁ O₂ := by
    rw [← a.map_orthogonal_iff, a.σ.apply_symm_apply, a.σ.apply_symm_apply]
  β O := (N.algebraCongr (a.σ.apply_symm_apply O).symm).trans (a.β (a.σ.symm O)).symm
  β_incl h x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [N.incl_algebraCongr _ _ h (a.σ.monotone (a.σ.symm.monotone h)), a.β_symm_incl]
  β_parity O x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [N.parity_algebraCongr, a.β_symm_parity]

/-- The identity covariance acts as the identity on every local algebra. Not a simp lemma: the
    codomain type of `β O` depends on `σ O`, which `simp` rewrites first (`id_σ_apply`), after which
    this left-hand side no longer matches; use it with `simp only` or `rw`. -/
lemma id_β_apply (O : K) (x : N.algebra O) : (Covariance.id N).β O x = x :=
  rfl

/-- The composite covariance acts by composing the local `*`-isomorphisms along the region maps.
    Not a simp lemma, for the reason given at `id_β_apply`. -/
lemma comp_β_apply (a b : N.Covariance) (O : K) (x : N.algebra O) :
    (a.comp b).β O x = a.β (b.σ O) (b.β O x) :=
  rfl

/-- The inverse covariance acts by the inverse local `*`-isomorphism, after transporting the
    argument along the region equality `σ(σ⁻¹O) = O`. -/
@[simp] lemma inv_β_apply (a : N.Covariance) (O : K) (x : N.algebra O) :
    (Covariance.inv a).β O x = (a.β (a.σ.symm O)).symm
      (N.algebraCongr (a.σ.apply_symm_apply O).symm x) :=
  rfl

/-- The identity covariance fixes every region. -/
@[simp] lemma id_σ_apply (O : K) : (Covariance.id N).σ O = O :=
  rfl

/-- Composing covariances composes their region maps. -/
@[simp] lemma comp_σ_apply (a b : N.Covariance) (O : K) :
    (a.comp b).σ O = a.σ (b.σ O) :=
  rfl

/-- The identity covariance is a left unit for composition. -/
lemma id_comp (a : N.Covariance) : (Covariance.id N).comp a = a := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- The identity covariance is a right unit for composition. -/
lemma comp_id (a : N.Covariance) : a.comp (Covariance.id N) = a := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- Composition of covariances is associative. -/
lemma comp_assoc (a b c : N.Covariance) : (a.comp b).comp c = a.comp (b.comp c) := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- The inverse covariance is a left inverse for composition; together with the three laws above
    this is what makes the covariances a group. -/
lemma inv_comp (a : N.Covariance) : (Covariance.inv a).comp a = Covariance.id N := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext (funext fun O => a.σ.symm_apply_apply O)
  · rw [CStarNet.algebraCongr_eq_iff]
    simp only [comp_β_apply, inv_β_apply, id_β_apply]
    rw [← a.β_algebraCongr, StarAlgEquiv.symm_apply_apply]
    rfl

/-- The covariances of a graded-local net form a **group** under composition, with `Covariance.id` the
    unit and `Covariance.inv` the inverse. -/
noncomputable instance : Group N.Covariance where
  mul a b := a.comp b
  one := Covariance.id N
  inv a := a.inv
  mul_assoc := Covariance.comp_assoc
  one_mul := Covariance.id_comp
  mul_one := Covariance.comp_id
  inv_mul_cancel := Covariance.inv_comp

/-- The group multiplication is composition of covariances. -/
lemma mul_def (a b : N.Covariance) : a * b = a.comp b := rfl

/-- The group unit is the identity covariance. -/
lemma one_def : (1 : N.Covariance) = Covariance.id N := rfl

/-- The group inverse is the inverse covariance. -/
lemma inv_def (a : N.Covariance) : a⁻¹ = a.inv := rfl

end Covariance

/-! ### The parity as a covariance -/

/-- The **parity covariance**: the parity automorphisms of the local algebras, as a covariance
    leaving every region in place. Its action on the quasi-local C⋆-algebra is the parity
    automorphism `GradedLocalNet.quasiLocalParity`. For a local net it is the unit
    (`GradedLocalNet.parityCovariance_eq_one`). -/
def parityCovariance : N.Covariance where
  σ := OrderIso.refl K
  map_orthogonal_iff _ _ := Iff.rfl
  β := N.parity
  β_incl h x := N.parity_incl h x
  β_parity _ _ := rfl

/-- The parity covariance is an involution. -/
lemma parityCovariance_mul_self : parityCovariance N * parityCovariance N = 1 := by
  refine Covariance.ext rfl fun O x e => ?_
  exact (N.algebraCongr_self (O := O) e _).trans (N.parity_parity x)

/-- For a local net the parity covariance is the unit. -/
lemma parityCovariance_eq_one [N.IsLocal] : parityCovariance N = 1 := by
  refine Covariance.ext rfl fun O x e => ?_
  exact (N.algebraCongr_self (O := O) e _).trans (N.parity_apply x)

end GradedLocalNet
