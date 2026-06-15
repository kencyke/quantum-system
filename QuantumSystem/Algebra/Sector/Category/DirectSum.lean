module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import QuantumSystem.Algebra.Sector.Category.CStarCategory

/-!
# Binary direct sums (biproducts) of endomorphisms

A C\*-tensor category is **closed under direct sums** (Müger §1.5): for objects
`ρ`, `σ` there is a direct sum `ρ ⊕ σ`.  In the concrete model `StarEndoCat A` an
object is a unital `*`-endomorphism of `A`, and the direct sum is realised
*internally* to `A` by a pair of isometries with orthogonal ranges summing to `1`
(a "Cuntz pair"):

```
v₁⋆ v₁ = 1,  v₂⋆ v₂ = 1,  v₁ v₁⋆ + v₂ v₂⋆ = 1.
```

Given such a pair, `(ρ ⊕ σ)(a) := v₁ ρ(a) v₁⋆ + v₂ σ(a) v₂⋆` is again a unital
`*`-endomorphism, and `v₁, v₂` (resp. `v₁⋆, v₂⋆`) are the biproduct injections
(resp. projections).  The biproduct identities reduce to the Cuntz relations, so
`ρ ⊕ σ` is a genuine `CategoryTheory.Limits.HasBinaryBiproduct`.

The existence of a Cuntz pair is a structural property of `A` (a *properly
infinite* algebra such as the quasi-local algebra of an infinite system); it is
isolated here as the datum `IsometryPair A`, to be supplied by concrete models.
This is the direct-sum half of the C\*-completeness required by the
Doplicher–Roberts reconstruction (Müger Theorem 2.18).

## References

* Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.5.
* Doplicher, Roberts, *A new duality theory for compact groups*, Invent. Math.
  98 (1989).
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

open MonoidalCategory Limits

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ### Cuntz pairs -/

/-- A **Cuntz pair** in `A`: two isometries with orthogonal ranges summing to `1`.
This is exactly the datum realising a binary direct sum of endomorphisms inside
`A`; it exists in any properly infinite C\*-algebra. -/
structure IsometryPair (A : Type u) [CStarAlgebra A] where
  /-- The first isometry. -/
  v₁ : A
  /-- The second isometry. -/
  v₂ : A
  /-- `v₁` is an isometry. -/
  isom₁ : star v₁ * v₁ = 1
  /-- `v₂` is an isometry. -/
  isom₂ : star v₂ * v₂ = 1
  /-- The range projections sum to `1` (completeness). -/
  complete : v₁ * star v₁ + v₂ * star v₂ = 1

namespace IsometryPair

variable (p : IsometryPair A)

/-- The ranges of `v₁` and `v₂` are orthogonal: `v₂⋆ v₁ = 0`.  This follows from the
isometry and completeness relations (the standard `2x = x ⟹ x = 0` argument). -/
lemma orth₂₁ : star p.v₂ * p.v₁ = 0 := by
  have key : star p.v₂ * p.v₁ = star p.v₂ * p.v₁ + star p.v₂ * p.v₁ := by
    calc star p.v₂ * p.v₁
        = star p.v₂ * (1 * p.v₁) := by rw [one_mul]
      _ = star p.v₂ * ((p.v₁ * star p.v₁ + p.v₂ * star p.v₂) * p.v₁) := by rw [p.complete]
      _ = star p.v₂ * (p.v₁ * (star p.v₁ * p.v₁) + p.v₂ * (star p.v₂ * p.v₁)) := by noncomm_ring
      _ = star p.v₂ * (p.v₁ + p.v₂ * (star p.v₂ * p.v₁)) := by rw [p.isom₁, mul_one]
      _ = star p.v₂ * p.v₁ + (star p.v₂ * p.v₂) * (star p.v₂ * p.v₁) := by noncomm_ring
      _ = star p.v₂ * p.v₁ + star p.v₂ * p.v₁ := by rw [p.isom₂, one_mul]
  have h2 : star p.v₂ * p.v₁ + star p.v₂ * p.v₁ = star p.v₂ * p.v₁ + 0 := by
    rw [add_zero]; exact key.symm
  exact add_left_cancel h2

/-- The dual orthogonality `v₁⋆ v₂ = 0`. -/
lemma orth₁₂ : star p.v₁ * p.v₂ = 0 := by
  have h := congrArg star p.orth₂₁
  rwa [star_mul, star_star, star_zero] at h

/-! ### The direct-sum endomorphism -/

/-- The underlying `*`-homomorphism of the direct sum `ρ ⊕ σ`:
`a ↦ v₁ ρ(a) v₁⋆ + v₂ σ(a) v₂⋆`. -/
noncomputable def directSumHom (p : IsometryPair A) (ρ σ : StarEndoCat A) : A →⋆ₐ[ℂ] A where
  toFun a := p.v₁ * ρ.endo a * star p.v₁ + p.v₂ * σ.endo a * star p.v₂
  map_one' := by rw [map_one, map_one, mul_one, mul_one]; exact p.complete
  map_mul' a b := by
    have diag : ∀ {v x y : A}, star v * v = 1 →
        (v * x * star v) * (v * y * star v) = v * (x * y) * star v := by
      intro v x y hv
      have e : (v * x * star v) * (v * y * star v) = v * x * (star v * v) * y * star v := by
        noncomm_ring
      rw [e, hv]; noncomm_ring
    have offdiag : ∀ {v w x y : A}, star v * w = 0 →
        (v * x * star v) * (w * y * star w) = 0 := by
      intro v w x y hvw
      have e : (v * x * star v) * (w * y * star w) = v * x * (star v * w) * y * star w := by
        noncomm_ring
      rw [e, hvw]; noncomm_ring
    rw [map_mul, map_mul, add_mul, mul_add, mul_add, diag p.isom₁, offdiag p.orth₁₂,
      offdiag p.orth₂₁, diag p.isom₂, add_zero, zero_add]
  map_zero' := by rw [map_zero, map_zero, mul_zero, zero_mul, mul_zero, zero_mul, add_zero]
  map_add' a b := by rw [map_add, map_add]; noncomm_ring
  commutes' r := by
    rw [AlgHomClass.commutes ρ.endo r, AlgHomClass.commutes σ.endo r,
      ← Algebra.commutes r p.v₁, ← Algebra.commutes r p.v₂, mul_assoc, mul_assoc,
      ← mul_add, p.complete, mul_one]
  map_star' a := by
    rw [star_add]
    simp only [star_mul, star_star, map_star, mul_assoc]

/-- The **direct sum** `ρ ⊕ σ` of two endomorphisms, realised internally to `A`
via a Cuntz pair. -/
noncomputable def directSum (p : IsometryPair A) (ρ σ : StarEndoCat A) : StarEndoCat A :=
  ⟨p.directSumHom ρ σ⟩

@[simp] lemma directSum_endo_apply (p : IsometryPair A) (ρ σ : StarEndoCat A) (a : A) :
    (p.directSum ρ σ).endo a = p.v₁ * ρ.endo a * star p.v₁ + p.v₂ * σ.endo a * star p.v₂ :=
  rfl

/-! ### The biproduct injections and projections -/

/-- The first injection `ρ ⟶ ρ ⊕ σ`, with underlying element `v₁`. -/
noncomputable def inl (p : IsometryPair A) (ρ σ : StarEndoCat A) : ρ ⟶ p.directSum ρ σ where
  t := p.v₁
  intertwines a := by
    rw [directSum_endo_apply,
      show (p.v₁ * ρ.endo a * star p.v₁ + p.v₂ * σ.endo a * star p.v₂) * p.v₁
        = p.v₁ * ρ.endo a * (star p.v₁ * p.v₁) + p.v₂ * σ.endo a * (star p.v₂ * p.v₁) from by
          noncomm_ring,
      p.isom₁, p.orth₂₁, mul_zero, add_zero, mul_one]

/-- The second injection `σ ⟶ ρ ⊕ σ`, with underlying element `v₂`. -/
noncomputable def inr (p : IsometryPair A) (ρ σ : StarEndoCat A) : σ ⟶ p.directSum ρ σ where
  t := p.v₂
  intertwines a := by
    rw [directSum_endo_apply,
      show (p.v₁ * ρ.endo a * star p.v₁ + p.v₂ * σ.endo a * star p.v₂) * p.v₂
        = p.v₁ * ρ.endo a * (star p.v₁ * p.v₂) + p.v₂ * σ.endo a * (star p.v₂ * p.v₂) from by
          noncomm_ring,
      p.orth₁₂, p.isom₂, mul_zero, zero_add, mul_one]

/-- The first projection `ρ ⊕ σ ⟶ ρ`, with underlying element `v₁⋆`. -/
noncomputable def fst (p : IsometryPair A) (ρ σ : StarEndoCat A) : p.directSum ρ σ ⟶ ρ where
  t := star p.v₁
  intertwines a := by
    rw [directSum_endo_apply,
      show star p.v₁ * (p.v₁ * ρ.endo a * star p.v₁ + p.v₂ * σ.endo a * star p.v₂)
        = (star p.v₁ * p.v₁) * ρ.endo a * star p.v₁
            + (star p.v₁ * p.v₂) * σ.endo a * star p.v₂ from by noncomm_ring,
      p.isom₁, p.orth₁₂, one_mul, zero_mul, zero_mul, add_zero]

/-- The second projection `ρ ⊕ σ ⟶ σ`, with underlying element `v₂⋆`. -/
noncomputable def snd (p : IsometryPair A) (ρ σ : StarEndoCat A) : p.directSum ρ σ ⟶ σ where
  t := star p.v₂
  intertwines a := by
    rw [directSum_endo_apply,
      show star p.v₂ * (p.v₁ * ρ.endo a * star p.v₁ + p.v₂ * σ.endo a * star p.v₂)
        = (star p.v₂ * p.v₁) * ρ.endo a * star p.v₁
            + (star p.v₂ * p.v₂) * σ.endo a * star p.v₂ from by noncomm_ring,
      p.orth₂₁, p.isom₂, zero_mul, zero_mul, zero_add, one_mul]

@[simp] lemma inl_t (p : IsometryPair A) (ρ σ : StarEndoCat A) : (p.inl ρ σ).t = p.v₁ := rfl
@[simp] lemma inr_t (p : IsometryPair A) (ρ σ : StarEndoCat A) : (p.inr ρ σ).t = p.v₂ := rfl
@[simp] lemma fst_t (p : IsometryPair A) (ρ σ : StarEndoCat A) : (p.fst ρ σ).t = star p.v₁ := rfl
@[simp] lemma snd_t (p : IsometryPair A) (ρ σ : StarEndoCat A) : (p.snd ρ σ).t = star p.v₂ := rfl

/-! ### The binary biproduct -/

/-- The binary bicone of `ρ ⊕ σ` from a Cuntz pair: injections `v₁, v₂` and
projections `v₁⋆, v₂⋆`, with the bicone identities given by the Cuntz relations. -/
noncomputable def binaryBicone (p : IsometryPair A) (ρ σ : StarEndoCat A) :
    BinaryBicone ρ σ where
  pt := p.directSum ρ σ
  fst := p.fst ρ σ
  snd := p.snd ρ σ
  inl := p.inl ρ σ
  inr := p.inr ρ σ
  inl_fst := Intertwiner.ext <| by rw [comp_t, fst_t, inl_t, id_t]; exact p.isom₁
  inl_snd := Intertwiner.ext <| by rw [comp_t, snd_t, inl_t, zero_t]; exact p.orth₂₁
  inr_fst := Intertwiner.ext <| by rw [comp_t, fst_t, inr_t, zero_t]; exact p.orth₁₂
  inr_snd := Intertwiner.ext <| by rw [comp_t, snd_t, inr_t, id_t]; exact p.isom₂

/-- The bicone is a biproduct: the total relation `fst ≫ inl + snd ≫ inr = 𝟙`
is the completeness relation of the Cuntz pair. -/
lemma binaryBicone_total (p : IsometryPair A) (ρ σ : StarEndoCat A) :
    (p.binaryBicone ρ σ).fst ≫ (p.binaryBicone ρ σ).inl
      + (p.binaryBicone ρ σ).snd ≫ (p.binaryBicone ρ σ).inr = 𝟙 (p.directSum ρ σ) :=
  Intertwiner.ext <| by
    simp only [binaryBicone]
    exact p.complete

/-- **A Cuntz pair gives binary biproducts.**  Every pair of endomorphisms has a
direct sum `ρ ⊕ σ` realised internally to `A` by the Cuntz pair `p`. -/
lemma hasBinaryBiproduct (p : IsometryPair A) (ρ σ : StarEndoCat A) :
    HasBinaryBiproduct ρ σ :=
  hasBinaryBiproduct_of_total (p.binaryBicone ρ σ) (p.binaryBicone_total ρ σ)

/-! ### Maps between direct sums (functoriality) -/

/-- Collapse a matched pair of blocks: `(b x v⋆)(v y w⋆) = b (x y) w⋆` when `v⋆v = 1`. -/
lemma block_collapse (b x v y w : A) (h : star v * v = 1) :
    (b * x * star v) * (v * y * star w) = b * (x * y) * star w := by
  have e : (b * x * star v) * (v * y * star w) = b * x * (star v * v) * y * star w := by
    noncomm_ring
  rw [e, h]; noncomm_ring

/-- Annihilate a mismatched pair of blocks: `(b x v⋆)(u y w⋆) = 0` when `v⋆u = 0`. -/
lemma block_vanish (b x v u y w : A) (h : star v * u = 0) :
    (b * x * star v) * (u * y * star w) = 0 := by
  have e : (b * x * star v) * (u * y * star w) = b * x * (star v * u) * y * star w := by
    noncomm_ring
  rw [e, h]; noncomm_ring

/-- A pair of intertwiners `f : ρ ⟶ ρ'`, `g : σ ⟶ σ'` induces a **map of direct
sums** `p.directSum ρ σ ⟶ q.directSum ρ' σ'` (source Cuntz pair `p`, target Cuntz
pair `q`), with underlying element `q.v₁ f.t p.v₁⋆ + q.v₂ g.t p.v₂⋆`.  This is the
biproduct functoriality realised internally; with `f`, `g` unitary it is the
unitary transporter moving a direct sum to a direct sum formed by another pair. -/
noncomputable def directSumMap (p q : IsometryPair A) {ρ ρ' σ σ' : StarEndoCat A}
    (f : ρ ⟶ ρ') (g : σ ⟶ σ') : p.directSum ρ σ ⟶ q.directSum ρ' σ' where
  t := q.v₁ * f.t * star p.v₁ + q.v₂ * g.t * star p.v₂
  intertwines a := by
    have hf := f.intertwines a
    have hg := g.intertwines a
    simp only [directSum_endo_apply]
    rw [add_mul, mul_add, mul_add,
      block_collapse q.v₁ f.t p.v₁ (ρ.endo a) p.v₁ p.isom₁,
      block_vanish q.v₁ f.t p.v₁ p.v₂ (σ.endo a) p.v₂ p.orth₁₂,
      block_vanish q.v₂ g.t p.v₂ p.v₁ (ρ.endo a) p.v₁ p.orth₂₁,
      block_collapse q.v₂ g.t p.v₂ (σ.endo a) p.v₂ p.isom₂,
      add_zero, zero_add, hf, hg, add_mul, mul_add, mul_add,
      block_collapse q.v₁ (ρ'.endo a) q.v₁ f.t p.v₁ q.isom₁,
      block_vanish q.v₁ (ρ'.endo a) q.v₁ q.v₂ g.t p.v₂ q.orth₁₂,
      block_vanish q.v₂ (σ'.endo a) q.v₂ q.v₁ f.t p.v₁ q.orth₂₁,
      block_collapse q.v₂ (σ'.endo a) q.v₂ g.t p.v₂ q.isom₂,
      add_zero, zero_add]

@[simp] lemma directSumMap_t (p q : IsometryPair A) {ρ ρ' σ σ' : StarEndoCat A}
    (f : ρ ⟶ ρ') (g : σ ⟶ σ') :
    (directSumMap p q f g).t = q.v₁ * f.t * star p.v₁ + q.v₂ * g.t * star p.v₂ := rfl

/-- The map of direct sums of two **unitary** intertwiners is unitary: it is the
unitary transporter between the two direct sums. -/
lemma directSumMap_isUnitary (p q : IsometryPair A) {ρ ρ' σ σ' : StarEndoCat A}
    {f : ρ ⟶ ρ'} {g : σ ⟶ σ'} (hf : f.t ∈ unitary A) (hg : g.t ∈ unitary A) :
    (directSumMap p q f g).t ∈ unitary A := by
  obtain ⟨hf1, hf2⟩ := Unitary.mem_iff.mp hf
  obtain ⟨hg1, hg2⟩ := Unitary.mem_iff.mp hg
  rw [directSumMap_t, Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [star_add, star_mul, star_mul, star_mul, star_mul, star_star, star_star,
      ← mul_assoc, ← mul_assoc, add_mul, mul_add, mul_add,
      block_collapse p.v₁ (star f.t) q.v₁ f.t p.v₁ q.isom₁,
      block_vanish p.v₁ (star f.t) q.v₁ q.v₂ g.t p.v₂ q.orth₁₂,
      block_vanish p.v₂ (star g.t) q.v₂ q.v₁ f.t p.v₁ q.orth₂₁,
      block_collapse p.v₂ (star g.t) q.v₂ g.t p.v₂ q.isom₂,
      add_zero, zero_add, hf1, hg1, mul_one, mul_one, p.complete]
  · rw [star_add, star_mul, star_mul, star_mul, star_mul, star_star, star_star,
      ← mul_assoc, ← mul_assoc, add_mul, mul_add, mul_add,
      block_collapse q.v₁ f.t p.v₁ (star f.t) q.v₁ p.isom₁,
      block_vanish q.v₁ f.t p.v₁ p.v₂ (star g.t) q.v₂ p.orth₁₂,
      block_vanish q.v₂ g.t p.v₂ p.v₁ (star f.t) q.v₁ p.orth₂₁,
      block_collapse q.v₂ g.t p.v₂ (star g.t) q.v₂ p.isom₂,
      add_zero, zero_add, hf2, hg2, mul_one, mul_one, q.complete]

end IsometryPair

/-! ### Category-wide binary biproducts -/

/-- `A` **has a Cuntz pair** — a *properly infinite* property of `A`: there exist
two isometries with orthogonal ranges summing to `1`.  Under this hypothesis the
endomorphism category has all binary direct sums.  It holds for the quasi-local
algebra of an infinite quantum system (to be discharged for concrete nets, R8). -/
class HasCuntzPair (A : Type u) [CStarAlgebra A] : Prop where
  /-- `A` admits a Cuntz pair. -/
  nonempty_isometryPair : Nonempty (IsometryPair A)

/-- **A category of endomorphisms over a properly infinite algebra has binary
direct sums.**  This connects the internal Cuntz-pair construction to the Mathlib
biproduct API (`⊞`, `biprod.fst`, …) for `StarEndoCat A`. -/
instance [HasCuntzPair A] : HasBinaryBiproducts (StarEndoCat A) where
  has_binary_biproduct ρ σ :=
    (HasCuntzPair.nonempty_isometryPair (A := A)).elim fun p => p.hasBinaryBiproduct ρ σ

end StarEndo

end CategoryTheory
