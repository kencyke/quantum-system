/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Physics.LocalNet.Basic

/-!
# Automorphisms of a net

An **automorphism** of a graded-local net over a causal index set `K`
(`GradedLocalNet.Automorphism`) is an automorphism of the net *covering* an automorphism of its
index set: an order automorphism `σ : K ≃o K` of the regions preserving causal orthogonality,
together with, for every region `O`, a `*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` of local algebras
that is natural with respect to the isotony embeddings and preserves the parity. The naturality
field `β_incl` is the AQFT covariance axiom `β(𝔄(O)) = 𝔄(σO)` compatibly with inclusions (Naaijkens,
*Anyons in Infinite Quantum Systems*, 2012, §3.2; Verch, *Lecture Notes on Operator Algebras and
Quantum Field Theory*, arXiv:2507.00900, 2025, §1.2): a symmetry group acts *covariantly* on the
net through a homomorphism into these automorphisms. They form a `Group` under composition
(`Automorphism.id`, `Automorphism.comp`, `Automorphism.inv`).

The automorphisms that leave every region in place, `σ = id`, are the internal symmetries of the
net, the subgroup `GradedLocalNet.Automorphism.internal`. For a Möbius covariant net on `S¹`,
Carpi–Kawahigashi–Longo–Weiner (*From vertex operator algebras to conformal nets and back*,
arXiv:1503.01260, §3.3, (41)) take as the automorphism group of the net the unitaries `g` with
`g 𝒜(I) g⋆ = 𝒜(I)` for every interval `I` and `g Ω = Ω`: region-preserving automorphisms,
implemented by unitaries fixing the vacuum. Neither unitary implementation nor a vacuum is part of
the structure here, and the region-moving automorphisms are kept in the same group.

The parity condition `β_parity` is no condition for a local net, where every map commutes with the
parity (`GradedLocalNet.map_parity`). The parity itself is an automorphism leaving every region in
place (`GradedLocalNet.parityAutomorphism`).

This file isolates the abstract automorphism *data* and its group structure; it carries no symmetry
group. A symmetry group `G` acts on the net by supplying a group homomorphism `G →* N.Automorphism`
(whose `σ`-component is the geometric action `G → K ≃o K`), and the automorphisms of a particular
group are in the files importing this one:

* `QuantumSystem.Physics.LocalNet.Automorphism.SitePerm` — the permutations of the sites of a
  lattice, which give all the automorphisms of a lattice net;
* `QuantumSystem.Physics.LocalNet.Automorphism.QuasiLocal` — the *action* of the automorphisms on the
  quasi-local algebra, and the C⋆-dynamical system of a symmetry group acting continuously.

## Notation

`𝔄(O)` in the prose above is documentation shorthand for the local C⋆-algebra `N.algebra O`; the
convention is stated in full in `QuantumSystem.Physics.LocalNet.Isotony`.
-/

@[expose] public section

namespace GradedLocalNet

open scoped CausalOrthogonality

variable {K : Type*} [Preorder K] [CausalOrthogonality K] (N : GradedLocalNet K)

/-! ### Automorphisms of the net

An automorphism of a graded-local net is a causal order automorphism `σ` of the index set together with,
for each region, a `*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` of local algebras that is natural
with respect to the isotony embeddings. This realises the AQFT covariance axiom `β(𝔄(O)) = 𝔄(σO)`
at the abstract net level. Being purely algebraic, the automorphism group needs no faithfulness
hypothesis.
-/

/-- An **automorphism** of a graded-local net `N`, covering an automorphism of its index set: an
    order automorphism `σ` of the causal index set preserving causal orthogonality
    (`map_orthogonal_iff`), together with, for every region `O`, a `*`-isomorphism
    `β O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)`, natural with respect to the isotony embeddings (`β_incl`) and
    preserving the parity (`β_parity`). This is the datum of the AQFT covariance axiom at the
    abstract net level. -/
structure Automorphism where
  /-- The underlying automorphism of the causal index set, carrying the region map `O ↦ σO`. -/
  σ : K ≃o K
  /-- The region automorphism preserves causal orthogonality. Stated as an `iff` so that the
      inverse automorphism is again an automorphism. -/
  map_orthogonal_iff : ∀ ⦃O₁ O₂ : K⦄, σ O₁ ⟂ σ O₂ ↔ O₁ ⟂ O₂
  /-- The `*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` on each region. -/
  β : ∀ O : K, N.algebra O ≃⋆ₐ[ℂ] N.algebra (σ O)
  /-- **Naturality / covariance**: `β` intertwines the isotony embeddings, so it maps the net to
      itself compatibly with inclusions — the AQFT covariance axiom `β(𝔄(O)) = 𝔄(σO)`. -/
  β_incl : ∀ {O O' : K} (h : O ≤ O') (x : N.algebra O),
      β O' (N.incl h x) = N.incl (σ.monotone h) (β O x)
  /-- The `*`-isomorphisms preserve the parity, so an automorphism is a symmetry of the
      graded net. For a local net, whose parity is trivial, this holds for every `β`
      (`GradedLocalNet.map_parity`). -/
  β_parity : ∀ (O : K) (x : N.algebra O), β O (N.parity O x) = N.parity (σ O) (β O x)

namespace Automorphism

variable {N} (a : N.Automorphism)

/-- **Extensionality** for automorphisms: two automorphisms with the same region automorphism and the
    same local `*`-isomorphisms (compared along the induced region equality) are equal. The
    remaining fields are propositions, hence irrelevant. -/
@[ext (iff := false)] lemma ext {s t : N.Automorphism} (hσ : s.σ = t.σ)
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
/-- The **identity automorphism**: the identity region automorphism with the identity local
    `*`-isomorphisms. -/
def id : N.Automorphism where
  σ := OrderIso.refl K
  map_orthogonal_iff _ _ := Iff.rfl
  β _ := StarAlgEquiv.refl ℂ _
  β_incl _ _ := rfl
  β_parity _ _ := rfl

/-- **Composition of automorphisms**: apply `b`, then `a`. The region automorphisms compose, and
    the local `*`-isomorphisms compose along them. -/
def comp (a b : N.Automorphism) : N.Automorphism where
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

/-- The **inverse automorphism**: the inverse region automorphism with the inverse local
    `*`-isomorphisms, transported along `σ(σ⁻¹O) = O`. -/
def inv (a : N.Automorphism) : N.Automorphism where
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

/-- The identity automorphism acts as the identity on every local algebra. Not a simp lemma: the
    codomain type of `β O` depends on `σ O`, which `simp` rewrites first (`id_σ_apply`), after which
    this left-hand side no longer matches; use it with `simp only` or `rw`. -/
lemma id_β_apply (O : K) (x : N.algebra O) : (Automorphism.id N).β O x = x :=
  rfl

/-- The composite automorphism acts by composing the local `*`-isomorphisms along the region maps.
    Not a simp lemma, for the reason given at `id_β_apply`. -/
lemma comp_β_apply (a b : N.Automorphism) (O : K) (x : N.algebra O) :
    (a.comp b).β O x = a.β (b.σ O) (b.β O x) :=
  rfl

/-- The inverse automorphism acts by the inverse local `*`-isomorphism, after transporting the
    argument along the region equality `σ(σ⁻¹O) = O`. -/
@[simp] lemma inv_β_apply (a : N.Automorphism) (O : K) (x : N.algebra O) :
    (Automorphism.inv a).β O x = (a.β (a.σ.symm O)).symm
      (N.algebraCongr (a.σ.apply_symm_apply O).symm x) :=
  rfl

/-- The identity automorphism fixes every region. -/
@[simp] lemma id_σ_apply (O : K) : (Automorphism.id N).σ O = O :=
  rfl

/-- Composing automorphisms composes their region maps. -/
@[simp] lemma comp_σ_apply (a b : N.Automorphism) (O : K) :
    (a.comp b).σ O = a.σ (b.σ O) :=
  rfl

/-- The identity automorphism is a left unit for composition. -/
lemma id_comp (a : N.Automorphism) : (Automorphism.id N).comp a = a := by
  refine Automorphism.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- The identity automorphism is a right unit for composition. -/
lemma comp_id (a : N.Automorphism) : a.comp (Automorphism.id N) = a := by
  refine Automorphism.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- Composition of automorphisms is associative. -/
lemma comp_assoc (a b c : N.Automorphism) : (a.comp b).comp c = a.comp (b.comp c) := by
  refine Automorphism.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- The inverse automorphism is a left inverse for composition; together with the three laws above
    this is what makes the automorphisms a group. -/
lemma inv_comp (a : N.Automorphism) : (Automorphism.inv a).comp a = Automorphism.id N := by
  refine Automorphism.ext ?_ fun O x e => ?_
  · exact OrderIso.ext (funext fun O => a.σ.symm_apply_apply O)
  · rw [CStarNet.algebraCongr_eq_iff]
    simp only [comp_β_apply, inv_β_apply, id_β_apply]
    rw [← a.β_algebraCongr, StarAlgEquiv.symm_apply_apply]
    rfl

/-- The automorphisms of a graded-local net form a **group** under composition, with `Automorphism.id` the
    unit and `Automorphism.inv` the inverse. -/
noncomputable instance : Group N.Automorphism where
  mul a b := a.comp b
  one := Automorphism.id N
  inv a := a.inv
  mul_assoc := Automorphism.comp_assoc
  one_mul := Automorphism.id_comp
  mul_one := Automorphism.comp_id
  inv_mul_cancel := Automorphism.inv_comp

/-- The group multiplication is composition of automorphisms. -/
lemma mul_def (a b : N.Automorphism) : a * b = a.comp b := rfl

/-- The group unit is the identity automorphism. -/
lemma one_def : (1 : N.Automorphism) = Automorphism.id N := rfl

/-- The group inverse is the inverse automorphism. -/
lemma inv_def (a : N.Automorphism) : a⁻¹ = a.inv := rfl

end Automorphism

/-! ### The parity as an automorphism -/

/-- The **parity automorphism**: the parity automorphisms of the local algebras, as an automorphism
    leaving every region in place. Its action on the quasi-local C⋆-algebra is the parity
    automorphism `GradedLocalNet.quasiLocalParity`. For a local net it is the unit
    (`GradedLocalNet.parityAutomorphism_eq_one`). -/
def parityAutomorphism : N.Automorphism where
  σ := OrderIso.refl K
  map_orthogonal_iff _ _ := Iff.rfl
  β := N.parity
  β_incl h x := N.parity_incl h x
  β_parity _ _ := rfl

/-- The parity automorphism is an involution. -/
lemma parityAutomorphism_mul_self : parityAutomorphism N * parityAutomorphism N = 1 := by
  refine Automorphism.ext rfl fun O x e => ?_
  exact (N.algebraCongr_self (O := O) e _).trans (N.parity_parity x)

/-- For a local net the parity automorphism is the unit. -/
lemma parityAutomorphism_eq_one [N.IsTriviallyGraded] : parityAutomorphism N = 1 := by
  refine Automorphism.ext rfl fun O x e => ?_
  exact (N.algebraCongr_self (O := O) e _).trans (N.parity_apply x)

/-! ### Internal automorphisms -/

namespace Automorphism

/-- The **internal automorphisms**: those leaving every region in place, `σ = id`. They form a
    subgroup, and a group `G` of internal symmetries acts on the net through a homomorphism
    `G →* N.Automorphism.internal`. -/
def internal : Subgroup N.Automorphism where
  carrier := {a | a.σ = OrderIso.refl K}
  one_mem' := rfl
  mul_mem' {a b} ha hb := by
    change b.σ.trans a.σ = OrderIso.refl K
    rw [show a.σ = OrderIso.refl K from ha, show b.σ = OrderIso.refl K from hb]
    rfl
  inv_mem' {a} ha := by
    change a.σ.symm = OrderIso.refl K
    rw [show a.σ = OrderIso.refl K from ha]
    rfl

variable {N}

/-- An internal automorphism fixes every region. -/
lemma internal_σ_apply (a : internal N) (O : K) : a.1.σ O = O :=
  DFunLike.congr_fun a.2 O

variable (N) in
/-- The **action of the internal automorphisms on a local algebra**: `β_O`, transported along
    `σ O = O`. -/
noncomputable def internalAct (O : K) : internal N →* (N.algebra O ≃⋆ₐ[ℂ] N.algebra O) where
  toFun a := (a.1.β O).trans (N.algebraCongr (internal_σ_apply a O))
  map_one' := StarAlgEquiv.ext fun x => N.algebraCongr_self (O := O) rfl x
  map_mul' a b := StarAlgEquiv.ext fun x => by
    obtain ⟨⟨σa, -, βa, -, -⟩, ha⟩ := a
    obtain ⟨⟨σb, -, βb, -, -⟩, hb⟩ := b
    change σa = OrderIso.refl K at ha
    change σb = OrderIso.refl K at hb
    subst ha hb
    rfl

/-- The action of an internal automorphism is `β_O` transported along `σ O = O`. -/
lemma internalAct_apply (a : internal N) (O : K) (x : N.algebra O) :
    internalAct N O a x = N.algebraCongr (internal_σ_apply a O) (a.1.β O x) :=
  rfl

/-- The action of the internal automorphisms is compatible with the isotony embeddings. -/
lemma internalAct_incl (a : internal N) {O O' : K} (h : O ≤ O') (x : N.algebra O) :
    internalAct N O' a (N.incl h x) = N.incl h (internalAct N O a x) := by
  obtain ⟨⟨σ, -, β, hβ, -⟩, ha⟩ := a
  change σ = OrderIso.refl K at ha
  subst ha
  exact hβ h x

/-- The action of the internal automorphisms commutes with the parity. -/
lemma internalAct_parity (a : internal N) (O : K) (x : N.algebra O) :
    internalAct N O a (N.parity O x) = N.parity O (internalAct N O a x) := by
  obtain ⟨⟨σ, -, β, -, hβ⟩, ha⟩ := a
  change σ = OrderIso.refl K at ha
  subst ha
  exact hβ O x

end Automorphism

/-- The parity automorphism is internal. -/
lemma parityAutomorphism_mem_internal : parityAutomorphism N ∈ Automorphism.internal N :=
  rfl

/-- The internal automorphism `parityAutomorphism` acts on every local algebra by the parity. -/
lemma internalAct_parityAutomorphism (O : K) (x : N.algebra O) :
    Automorphism.internalAct N O ⟨_, N.parityAutomorphism_mem_internal⟩ x = N.parity O x :=
  rfl

end GradedLocalNet
