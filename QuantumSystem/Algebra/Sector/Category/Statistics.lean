module

public import QuantumSystem.Algebra.Sector.Category.Endomorphism

/-!
# The statistics operator (braiding intertwiner) of `End(A)`

For two `*`-endomorphisms `ρ`, `σ` of a C\*-algebra `A`, the Doplicher–Haag–Roberts
**statistics operator** is a unitary intertwiner

```
ε(ρ, σ) : ρ ⊗ σ ⟶ σ ⊗ ρ      (here `⊗` is composition of endomorphisms)
```

constructed from a **transporter**: a unitary intertwiner `u : σ ⟶ σ'` moving `σ`
to an endomorphism `σ'` that *commutes* with `ρ`.  Its underlying algebra element
is `u⋆ · ρ(u)`.

This file develops the construction at the abstract level of `StarEndoCat A` (any
C\*-algebra `A`): the commutation `Commutes ρ σ'` and the transporter are taken as
algebraic data.  The geometric input that such transporters *exist* (Haag duality,
spacelike separation) and that the resulting braiding is a *symmetry* (`ε² = 1` in
`d ≥ 3`) is supplied at the net level (`Sector/Net/`).

Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.2.
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

open MonoidalCategory

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ### Unitary intertwiners -/

/-- An intertwiner is **unitary** when its underlying element is a unitary of `A`. -/
def IsUnitary {ρ σ : StarEndoCat A} (f : ρ ⟶ σ) : Prop :=
  f.t ∈ unitary A

/-- The identity intertwiner is unitary. -/
lemma id_isUnitary (ρ : StarEndoCat A) : IsUnitary (𝟙 ρ) := by
  change (𝟙 ρ : ρ ⟶ ρ).t ∈ unitary A
  rw [id_t]; exact Submonoid.one_mem _

/-- A `*`-endomorphism maps unitaries to unitaries. -/
lemma endo_mem_unitary (ρ : StarEndoCat A) {u : A} (hu : u ∈ unitary A) :
    ρ.endo u ∈ unitary A := by
  rw [Unitary.mem_iff] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  refine ⟨?_, ?_⟩
  · rw [← map_star, ← map_mul, h1, map_one]
  · rw [← map_star, ← map_mul, h2, map_one]

/-- A unitary intertwiner `u : σ ⟶ σ'` **star-intertwines** in the opposite
direction: `u⋆ · σ'(c) = σ(c) · u⋆` for every `c`.  This is the relation used to
move `u⋆` across an application of the transported endomorphism (the `hflip`
step inside `statisticsOperator_intertwines`, isolated for reuse). -/
lemma star_intertwines {σ σ' : StarEndoCat A} (u : σ ⟶ σ') (hu : IsUnitary u) (c : A) :
    star u.t * σ'.endo c = σ.endo c * star u.t := by
  obtain ⟨huU, huU2⟩ := Unitary.mem_iff.mp hu
  have e1 : σ.endo c = star u.t * σ'.endo c * u.t := by
    calc σ.endo c = (star u.t * u.t) * σ.endo c := by rw [huU, one_mul]
      _ = star u.t * (u.t * σ.endo c) := mul_assoc _ _ _
      _ = star u.t * (σ'.endo c * u.t) := congrArg (star u.t * ·) (u.intertwines c)
      _ = star u.t * σ'.endo c * u.t := (mul_assoc _ _ _).symm
  calc star u.t * σ'.endo c
      = star u.t * σ'.endo c * (u.t * star u.t) := by rw [huU2, mul_one]
    _ = star u.t * σ'.endo c * u.t * star u.t := (mul_assoc _ _ _).symm
    _ = σ.endo c * star u.t := by rw [← e1]

/-- The monoidal product `f ⊗ₘ g` of two unitary intertwiners is unitary. -/
lemma IsUnitary.tensorHom {ρ ρ' σ σ' : StarEndoCat A} {f : ρ ⟶ ρ'} {g : σ ⟶ σ'}
    (hf : IsUnitary f) (hg : IsUnitary g) : IsUnitary (f ⊗ₘ g) := by
  change (f ⊗ₘ g).t ∈ _root_.unitary A
  rw [tensorHom_t]
  exact mul_mem (endo_mem_unitary ρ' hg) hf

/-- A **unitary intertwiner is an isomorphism**: its inverse is its dagger
`f† = star f.t`.  (`f ≫ f† = 𝟙` and `f† ≫ f = 𝟙` by unitarity.) -/
@[simps] noncomputable def isoOfUnitary {ρ σ : StarEndoCat A} (f : ρ ⟶ σ)
    (hf : IsUnitary f) : ρ ≅ σ where
  hom := f
  inv := homDagger f
  hom_inv_id := by
    apply Intertwiner.ext
    obtain ⟨h1, _⟩ := Unitary.mem_iff.mp hf
    rw [comp_t, homDagger_t, id_t]
    exact h1
  inv_hom_id := by
    apply Intertwiner.ext
    obtain ⟨_, h2⟩ := Unitary.mem_iff.mp hf
    rw [comp_t, homDagger_t, id_t]
    exact h2

/-! ### Commuting endomorphisms -/

/-- Two endomorphisms **commute** when their underlying `*`-endomorphisms commute
as functions.  For DHR endomorphisms localised in spacelike-separated regions this
holds by locality; here it is the algebraic input to the braiding. -/
def Commutes (ρ σ : StarEndoCat A) : Prop :=
  ∀ a : A, ρ.endo (σ.endo a) = σ.endo (ρ.endo a)

namespace Commutes

variable {ρ σ τ : StarEndoCat A}

/-- Commutation of endomorphisms is symmetric. -/
lemma symm (h : Commutes ρ σ) : Commutes σ ρ := fun a => (h a).symm

/-- Every endomorphism commutes with the unit (vacuum) endomorphism. -/
lemma unit_right (ρ : StarEndoCat A) : Commutes ρ (𝟙_ (StarEndoCat A)) := fun _ => rfl

/-- The unit (vacuum) endomorphism commutes with every endomorphism. -/
lemma unit_left (σ : StarEndoCat A) : Commutes (𝟙_ (StarEndoCat A)) σ := fun _ => rfl

/-- If `ρ` commutes with `σ` and with `τ`, it commutes with the fusion `σ ⊗ τ`.
This makes transportability compatible with fusion. -/
lemma tensor_right (hσ : Commutes ρ σ) (hτ : Commutes ρ τ) :
    Commutes ρ (σ ⊗ τ) := fun a => by
  change ρ.endo (σ.endo (τ.endo a)) = σ.endo (τ.endo (ρ.endo a))
  rw [hσ (τ.endo a), hτ a]

/-- If `ρ` and `σ` both commute with `τ`, so does their fusion `ρ ⊗ σ`.  Dual to
`tensor_right`; needed for the first-argument fusion of the statistics operator. -/
lemma tensor_left (hρ : Commutes ρ τ) (hσ : Commutes σ τ) :
    Commutes (ρ ⊗ σ) τ :=
  (tensor_right hρ.symm hσ.symm).symm

end Commutes

/-! ### The statistics operator -/

/-- The intertwining relation of the statistics operator, in *unfolded* form. -/
lemma statisticsOperator_intertwines
    (ρ : StarEndoCat A) {σ σ' : StarEndoCat A}
    (u : σ ⟶ σ') (huU : star u.t * u.t = 1) (huU2 : u.t * star u.t = 1)
    (hcomm : Commutes ρ σ') (a : A) :
    (star u.t * ρ.endo u.t) * ρ.endo (σ.endo a)
      = σ.endo (ρ.endo a) * (star u.t * ρ.endo u.t) := by
  have hflip : ∀ c, star u.t * σ'.endo c = σ.endo c * star u.t := by
    intro c
    have e1 : σ.endo c = star u.t * σ'.endo c * u.t := by
      calc σ.endo c = (star u.t * u.t) * σ.endo c := by rw [huU, one_mul]
        _ = star u.t * (u.t * σ.endo c) := mul_assoc _ _ _
        _ = star u.t * (σ'.endo c * u.t) := congrArg (star u.t * ·) (u.intertwines c)
        _ = star u.t * σ'.endo c * u.t := (mul_assoc _ _ _).symm
    calc star u.t * σ'.endo c
        = star u.t * σ'.endo c * (u.t * star u.t) := by rw [huU2, mul_one]
      _ = star u.t * σ'.endo c * u.t * star u.t := (mul_assoc _ _ _).symm
      _ = σ.endo c * star u.t := by rw [← e1]
  have m1 : ρ.endo u.t * ρ.endo (σ.endo a) = ρ.endo (u.t * σ.endo a) :=
    (map_mul ρ.endo u.t (σ.endo a)).symm
  have m2 : ρ.endo (σ'.endo a * u.t) = ρ.endo (σ'.endo a) * ρ.endo u.t :=
    map_mul ρ.endo (σ'.endo a) u.t
  calc (star u.t * ρ.endo u.t) * ρ.endo (σ.endo a)
      = star u.t * (ρ.endo u.t * ρ.endo (σ.endo a)) := mul_assoc _ _ _
    _ = star u.t * ρ.endo (u.t * σ.endo a) := congrArg (star u.t * ·) m1
    _ = star u.t * ρ.endo (σ'.endo a * u.t) :=
          congrArg (fun z => star u.t * ρ.endo z) (u.intertwines a)
    _ = star u.t * (ρ.endo (σ'.endo a) * ρ.endo u.t) := congrArg (star u.t * ·) m2
    _ = star u.t * (σ'.endo (ρ.endo a) * ρ.endo u.t) :=
          congrArg (fun z => star u.t * (z * ρ.endo u.t)) (hcomm a)
    _ = (star u.t * σ'.endo (ρ.endo a)) * ρ.endo u.t := (mul_assoc _ _ _).symm
    _ = (σ.endo (ρ.endo a) * star u.t) * ρ.endo u.t :=
          congrArg (· * ρ.endo u.t) (hflip (ρ.endo a))
    _ = σ.endo (ρ.endo a) * (star u.t * ρ.endo u.t) := mul_assoc _ _ _

/-- **Statistics operator (braiding intertwiner)** `ρ ⊗ σ ⟶ σ ⊗ ρ`.

Given a unitary transporter `u : σ ⟶ σ'` to an endomorphism `σ'` commuting with
`ρ`, the braiding is the intertwiner with underlying element `u⋆ · ρ(u)`. -/
noncomputable def statisticsOperator
    (ρ : StarEndoCat A) {σ σ' : StarEndoCat A}
    (u : σ ⟶ σ') (hu : IsUnitary u) (hcomm : Commutes ρ σ') :
    (ρ ⊗ σ) ⟶ (σ ⊗ ρ) where
  t := star u.t * ρ.endo u.t
  intertwines a := by
    obtain ⟨huU, huU2⟩ := Unitary.mem_iff.mp hu
    exact statisticsOperator_intertwines ρ u huU huU2 hcomm a

@[simp] lemma statisticsOperator_t
    (ρ : StarEndoCat A) {σ σ' : StarEndoCat A}
    (u : σ ⟶ σ') (hu : IsUnitary u) (hcomm : Commutes ρ σ') :
    (statisticsOperator ρ u hu hcomm).t = star u.t * ρ.endo u.t := rfl

/-- The statistics operator is unitary. -/
lemma statisticsOperator_isUnitary
    (ρ : StarEndoCat A) {σ σ' : StarEndoCat A}
    (u : σ ⟶ σ') (hu : IsUnitary u) (hcomm : Commutes ρ σ') :
    IsUnitary (statisticsOperator ρ u hu hcomm) :=
  mul_mem (Unitary.star_mem hu) (endo_mem_unitary ρ hu)

/-- **Trivial (bosonic) statistics.**  If `ρ` and `σ` already commute, transporting
`σ` by the identity yields the identity braiding `ε(ρ, σ) = 1`. -/
lemma statisticsOperator_id
    (ρ : StarEndoCat A) {σ : StarEndoCat A} (hcomm : Commutes ρ σ) :
    (statisticsOperator ρ (𝟙 σ) (id_isUnitary σ) hcomm).t = 1 := by
  change star (𝟙 σ : σ ⟶ σ).t * ρ.endo (𝟙 σ : σ ⟶ σ).t = 1
  rw [id_t, star_one, one_mul, map_one]

/-! ### Fusion (hexagon) identities of the statistics operator

The statistics operator factors through fusion of either argument — the two
hexagon identities of the braiding.  Both are pure `.t`-algebra identities given
the transport data; the geometric *existence* of transports is supplied at the
net level.  (Müger §1.2; these are the DHR statistics fusion relations.) -/

/-- **Fusion in the second argument.**  Braiding `ρ` against the fused sector
`σ ⊗ τ`, with the monoidal product `uσ ⊗ₘ uτ` of the individual transports,
factors as `ε(ρ, σ⊗τ) = (ε(ρ,σ) ▷ τ) ≫ (σ ◁ ε(ρ,τ))`.  This is the first hexagon
identity (strict associators are trivial). -/
lemma statisticsOperator_tensor_right
    (ρ : StarEndoCat A) {σ σ' τ τ' : StarEndoCat A}
    (uσ : σ ⟶ σ') (huσ : IsUnitary uσ) (hσ : Commutes ρ σ')
    (uτ : τ ⟶ τ') (huτ : IsUnitary uτ) (hτ : Commutes ρ τ') :
    statisticsOperator ρ (uσ ⊗ₘ uτ) (huσ.tensorHom huτ) (hσ.tensor_right hτ)
      = (statisticsOperator ρ uσ huσ hσ ▷ τ) ≫ (σ ◁ statisticsOperator ρ uτ huτ hτ) := by
  apply Intertwiner.ext
  simp only [comp_t, whiskerLeft_t, whiskerRight_t, statisticsOperator_t, tensorHom_t,
    star_mul, map_mul, ← map_star]
  rw [hσ uτ.t]
  simp only [← mul_assoc]
  rw [mul_assoc (star uσ.t) (σ'.endo (star uτ.t)), ← map_mul, star_intertwines uσ huσ, map_mul]

/-- **Fusion in the first argument.**  Braiding the fused sector `ρ ⊗ σ` against
`τ`, with a single transport `u` of `τ` commuting with both `ρ` and `σ`, factors as
`ε(ρ⊗σ, τ) = (ρ ◁ ε(σ,τ)) ≫ (ε(ρ,τ) ▷ σ)`.  This is the second hexagon identity. -/
lemma statisticsOperator_tensor_left
    (ρ σ : StarEndoCat A) {τ τ' : StarEndoCat A}
    (u : τ ⟶ τ') (hu : IsUnitary u) (hρ : Commutes ρ τ') (hσ : Commutes σ τ') :
    statisticsOperator (ρ ⊗ σ) u hu (hρ.tensor_left hσ)
      = (ρ ◁ statisticsOperator σ u hu hσ) ≫ (statisticsOperator ρ u hu hρ ▷ σ) := by
  apply Intertwiner.ext
  obtain ⟨_, huU2⟩ := Unitary.mem_iff.mp hu
  have h1 : ρ.endo u.t * ρ.endo (star u.t) = 1 := by rw [← map_mul, huU2, map_one]
  simp only [comp_t, whiskerLeft_t, whiskerRight_t, statisticsOperator_t,
    monoidalTensorObj_endo_apply, map_mul]
  rw [mul_assoc (star u.t), ← mul_assoc (ρ.endo u.t), h1, one_mul]

/-! ### Naturality of the statistics operator (first argument)

Naturality in the *first* argument holds whenever the transport target `σ'` of the
second sector fixes the intertwiner (`σ'(f) = f`) — the algebraic shadow of
spacelike separation: in a local net the intertwiner is localised in the region of
`ρ, ρ'` while `σ'` is localised in a spacelike cone, so `σ'` acts trivially on it. -/

/-- **Naturality of `ε` in the first argument.**  For an intertwiner `f : ρ ⟶ ρ'`
fixed by the transport target (`σ'.endo f.t = f.t`),
`(f ▷ σ) ≫ ε(ρ', σ) = ε(ρ, σ) ≫ (σ ◁ f)`. -/
lemma statisticsOperator_naturality_left
    {ρ ρ' : StarEndoCat A} (f : ρ ⟶ ρ') {σ σ' : StarEndoCat A}
    (u : σ ⟶ σ') (hu : IsUnitary u) (hρ : Commutes ρ σ') (hρ' : Commutes ρ' σ')
    (htriv : σ'.endo f.t = f.t) :
    (f ▷ σ) ≫ statisticsOperator ρ' u hu hρ'
      = statisticsOperator ρ u hu hρ ≫ (σ ◁ f) := by
  apply Intertwiner.ext
  have hsi : star u.t * f.t = σ.endo f.t * star u.t := by
    have h := star_intertwines u hu f.t
    rwa [htriv] at h
  simp only [comp_t, whiskerLeft_t, whiskerRight_t, statisticsOperator_t]
  rw [mul_assoc, ← f.intertwines u.t, ← mul_assoc, hsi, mul_assoc]

/-! ### Symmetry of the statistics operator

In high dimensions (`d ≥ 3`, connected spacelike complement) the braiding is a
**symmetry**: the monodromy `ε(σ,ρ) ∘ ε(ρ,σ)` is trivial.  The geometric input
enters as a relation between the two transporters — the **reverse braiding equals
the dagger of the forward braiding** — under which the monodromy collapses to `1`
by unitarity.  This is the algebraic keystone of `ε² = 1`; the geometric relation
itself is supplied at the net level (`Net/Symmetry.lean`). -/

/-- **Symmetry keystone.**  If the two transporters `u` (of `σ` across `ρ`) and
`v` (of `ρ` across `σ`) satisfy the opposite-transport relation
`v⋆ · σ(v) = ρ(u⋆) · u` (the reverse statistics operator is the dagger of the
forward one), then the monodromy is trivial:
`ε(ρ,σ).t · ε(σ,ρ).t = 1`.  Pure `.t`-algebra; uses only unitarity of `u`. -/
lemma statisticsOperator_symmetry_t
    (ρ σ : StarEndoCat A) {σ' ρ' : StarEndoCat A}
    (u : σ ⟶ σ') (hu : IsUnitary u) (hρσ' : Commutes ρ σ')
    (v : ρ ⟶ ρ') (hv : IsUnitary v) (hσρ' : Commutes σ ρ')
    (hopp : star v.t * σ.endo v.t = ρ.endo (star u.t) * u.t) :
    (statisticsOperator ρ u hu hρσ').t * (statisticsOperator σ v hv hσρ').t = 1 := by
  obtain ⟨huU, huU2⟩ := Unitary.mem_iff.mp hu
  rw [statisticsOperator_t, statisticsOperator_t, hopp, mul_assoc, ← mul_assoc (ρ.endo u.t),
    ← map_mul, huU2, map_one, one_mul, huU]

/-- **Transport independence.**  Two transports `u₁ : σ ⟶ σ₁'`, `u₂ : σ ⟶ σ₂'` of
`σ` to (possibly different) commuting targets give the *same* statistics operator
(both have codomain `σ ⊗ ρ`, independent of the target), provided `ρ` fixes the
unitary intertwiner `w = u₂ · u₁⋆ : σ₁' → σ₂'` (`ρ(w) = w`).  At the net level `w`
is localised spacelike to `ρ` (Haag duality), so this fixing is automatic — making
the braiding independent of the choice of transport.  Pure `.t`-algebra; uses only
unitarity. -/
lemma statisticsOperator_indep_of_transporter (ρ : StarEndoCat A)
    {σ σ₁' σ₂' : StarEndoCat A}
    (u₁ : σ ⟶ σ₁') (u₂ : σ ⟶ σ₂') (hu₁ : IsUnitary u₁) (hu₂ : IsUnitary u₂)
    (hcomm₁ : Commutes ρ σ₁') (hcomm₂ : Commutes ρ σ₂')
    (hfix : ρ.endo (u₂.t * star u₁.t) = u₂.t * star u₁.t) :
    statisticsOperator ρ u₁ hu₁ hcomm₁ = statisticsOperator ρ u₂ hu₂ hcomm₂ := by
  apply Intertwiner.ext
  obtain ⟨h1U, h1U2⟩ := Unitary.mem_iff.mp hu₁
  obtain ⟨h2U, _⟩ := Unitary.mem_iff.mp hu₂
  simp only [statisticsOperator_t]
  set w := u₂.t * star u₁.t with hw
  have hu₂eq : u₂.t = w * u₁.t := by rw [hw, mul_assoc, h1U, mul_one]
  have hρu₂ : ρ.endo u₂.t = w * ρ.endo u₁.t := by rw [hu₂eq, map_mul, hfix]
  have hstaru₂ : star u₂.t = star u₁.t * star w := by rw [hu₂eq, star_mul]
  have hsww : star w * w = 1 := by
    rw [hw, star_mul, star_star, mul_assoc, ← mul_assoc (star u₂.t), h2U, one_mul, h1U2]
  rw [hstaru₂, hρu₂, mul_assoc (star u₁.t) (star w), ← mul_assoc (star w) w, hsww, one_mul]

/-! ### Transporters

A **transport** of `σ` away from `ρ` is the datum consumed by the statistics
operator: an endomorphism `tgt` commuting with `ρ`, together with a unitary
intertwiner `σ ⟶ tgt`. -/

/-- A **transport** of `σ` into the spacelike complement of `ρ`. -/
structure Transport (ρ σ : StarEndoCat A) where
  /-- The transported endomorphism (spacelike to `ρ`). -/
  tgt : StarEndoCat A
  /-- The unitary intertwiner moving `σ` to `tgt`. -/
  hom : σ ⟶ tgt
  /-- `hom` is unitary. -/
  unitary : IsUnitary hom
  /-- `tgt` commutes with `ρ`. -/
  commutes : Commutes ρ tgt

namespace Transport

variable {ρ σ τ : StarEndoCat A}

/-- The braiding intertwiner `ρ ⊗ σ ⟶ σ ⊗ ρ` of a transportable pair. -/
noncomputable def braiding (tr : Transport ρ σ) : (ρ ⊗ σ) ⟶ (σ ⊗ ρ) :=
  statisticsOperator ρ tr.hom tr.unitary tr.commutes

/-- The braiding is unitary. -/
lemma braiding_isUnitary (tr : Transport ρ σ) : IsUnitary tr.braiding :=
  statisticsOperator_isUnitary ρ tr.hom tr.unitary tr.commutes

/-- A sector commuting with `ρ` is transported trivially (by the identity). -/
noncomputable def ofCommutes (h : Commutes ρ σ) : Transport ρ σ where
  tgt := σ
  hom := 𝟙 σ
  unitary := id_isUnitary σ
  commutes := h

/-- **Bosonic normalisation.**  When `ρ`, `σ` commute, the braiding via the
trivial transport is the identity (`ε(ρ,σ) = 1`) — the statistics is trivial.
In particular the braiding against the vacuum is always trivial. -/
@[simp] lemma braiding_ofCommutes_t (h : Commutes ρ σ) :
    (ofCommutes h).braiding.t = 1 :=
  statisticsOperator_id ρ h

/-- Every sector transports trivially away from the vacuum. -/
noncomputable def ofVacuum (σ : StarEndoCat A) : Transport (𝟙_ (StarEndoCat A)) σ :=
  ofCommutes (Commutes.unit_left σ)

/-- The vacuum transports trivially away from any sector. -/
noncomputable def vacuum (ρ : StarEndoCat A) : Transport ρ (𝟙_ (StarEndoCat A)) :=
  ofCommutes (Commutes.unit_right ρ)

/-- **Transports compose with fusion.**  If both `σ` and `τ` transport away from
`ρ`, so does their fusion `σ ⊗ τ`, the transporter being the monoidal product. -/
noncomputable def tensor (trσ : Transport ρ σ) (trτ : Transport ρ τ) :
    Transport ρ (σ ⊗ τ) where
  tgt := trσ.tgt ⊗ trτ.tgt
  hom := trσ.hom ⊗ₘ trτ.hom
  unitary := by
    change (trσ.hom ⊗ₘ trτ.hom).t ∈ _root_.unitary A
    rw [tensorHom_t]
    exact mul_mem (endo_mem_unitary trσ.tgt trτ.unitary) trσ.unitary
  commutes := Commutes.tensor_right trσ.commutes trτ.commutes

/-- **Hexagon for transports.**  The braiding of the fused transport factors
through the individual braidings: `ε(ρ, σ⊗τ) = (ε(ρ,σ) ▷ τ) ≫ (σ ◁ ε(ρ,τ))`. -/
lemma braiding_tensor (trσ : Transport ρ σ) (trτ : Transport ρ τ) :
    (trσ.tensor trτ).braiding = (trσ.braiding ▷ τ) ≫ (σ ◁ trτ.braiding) :=
  statisticsOperator_tensor_right ρ trσ.hom trσ.unitary trσ.commutes
    trτ.hom trτ.unitary trτ.commutes

/-- **Symmetry of the braiding.**  Given transports `tr` of `σ` across `ρ` and
`tr'` of `ρ` across `σ` whose transporters satisfy the opposite-transport relation
(reverse braiding = dagger of forward braiding), the monodromy is trivial:
`ε(σ,ρ) ≫ ε(ρ,σ) = 𝟙`.  This is the `ε² = 1` content (the relation is the
high-dimensional geometric input, supplied at the net level). -/
lemma symmetry (tr : Transport ρ σ) (tr' : Transport σ ρ)
    (hopp : star tr'.hom.t * σ.endo tr'.hom.t = ρ.endo (star tr.hom.t) * tr.hom.t) :
    tr'.braiding ≫ tr.braiding = 𝟙 (σ ⊗ ρ) := by
  apply Intertwiner.ext
  rw [comp_t, id_t]
  exact statisticsOperator_symmetry_t ρ σ tr.hom tr.unitary tr.commutes
    tr'.hom tr'.unitary tr'.commutes hopp

end Transport

end StarEndo

end CategoryTheory
