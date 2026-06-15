module

public import QuantumSystem.Algebra.Sector.Category.Conjugate
public import QuantumSystem.Algebra.Sector.Category.DirectSum

/-!
# Conjugate of a direct sum: `(ρ ⊕ σ)‾ = ρ̄ ⊕ σ̄`

A C\*-tensor category closed under direct sums and conjugates has
`(ρ ⊕ σ)‾ = ρ̄ ⊕ σ̄` (Müger §1.5): the conjugate of a direct sum is the direct sum
of the conjugates.  This is the rigid half of the C\*-completeness of the DHR
category and the source of dimension additivity `d(ρ ⊕ σ) = d(ρ) + d(σ)`.

Given Cuntz pairs `p` (for `ρ ⊕ σ`) and `q` (for `ρ̄ ⊕ σ̄`), the conjugate solutions
are assembled additively from those of `ρ` and `σ` along the biproduct injections:

```
R_{ρ⊕σ}  = R_ρ ≫ (q₁ ⊗ p₁) + R_σ ≫ (q₂ ⊗ p₂),
R̄_{ρ⊕σ} = R̄_ρ ≫ (p₁ ⊗ q₁) + R̄_σ ≫ (p₂ ⊗ q₂),
```

where `pᵢ`/`qᵢ` are the injections of the two direct sums.  The four conjugate
equations then reduce, summand by summand, to those of `ρ` and `σ`: the Cuntz
orthogonality kills the cross terms and the completeness relation reassembles `1`.

## References

* Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.4–1.5.
* Longo, Roberts, *A theory of dimension*, K-Theory 11 (1997).
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

open MonoidalCategory

universe u

variable {A : Type u} [CStarAlgebra A] {ρ σ : StarEndoCat A}

/-- Coevaluation for the conjugate of a direct sum,
`R = R_ρ ≫ (q₁ ⊗ p₁) + R_σ ≫ (q₂ ⊗ p₂)`. -/
noncomputable def Conjugate.directSumR (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    𝟙_ (StarEndoCat A) ⟶ (q.directSum cρ.bar cσ.bar) ⊗ (p.directSum ρ σ) :=
  cρ.R ≫ (q.inl cρ.bar cσ.bar ⊗ₘ p.inl ρ σ) + cσ.R ≫ (q.inr cρ.bar cσ.bar ⊗ₘ p.inr ρ σ)

/-- Coevaluation `R̄ = R̄_ρ ≫ (p₁ ⊗ q₁) + R̄_σ ≫ (p₂ ⊗ q₂)`. -/
noncomputable def Conjugate.directSumRbar (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    𝟙_ (StarEndoCat A) ⟶ (p.directSum ρ σ) ⊗ (q.directSum cρ.bar cσ.bar) :=
  cρ.Rbar ≫ (p.inl ρ σ ⊗ₘ q.inl cρ.bar cσ.bar) + cσ.Rbar ≫ (p.inr ρ σ ⊗ₘ q.inr cρ.bar cσ.bar)

@[simp] lemma Conjugate.directSumR_t (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (cρ.directSumR p q cσ).t =
      q.v₁ * cρ.bar.endo p.v₁ * cρ.R.t + q.v₂ * cσ.bar.endo p.v₂ * cσ.R.t := by
  have h1 := (q.inl cρ.bar cσ.bar).intertwines p.v₁
  have h2 := (q.inr cρ.bar cσ.bar).intertwines p.v₂
  simp only [IsometryPair.inl_t, IsometryPair.inr_t] at h1 h2
  simp only [Conjugate.directSumR]
  rw [add_t, comp_t, comp_t, tensorHom_t, tensorHom_t]
  simp only [IsometryPair.inl_t, IsometryPair.inr_t]
  rw [← h1, ← h2]

@[simp] lemma Conjugate.directSumRbar_t (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (cρ.directSumRbar p q cσ).t =
      p.v₁ * ρ.endo q.v₁ * cρ.Rbar.t + p.v₂ * σ.endo q.v₂ * cσ.Rbar.t := by
  have h1 := (p.inl ρ σ).intertwines q.v₁
  have h2 := (p.inr ρ σ).intertwines q.v₂
  simp only [IsometryPair.inl_t, IsometryPair.inr_t] at h1 h2
  simp only [Conjugate.directSumRbar]
  rw [add_t, comp_t, comp_t, tensorHom_t, tensorHom_t]
  simp only [IsometryPair.inl_t, IsometryPair.inr_t]
  rw [← h1, ← h2]

/-! ### Collapse lemmas for the direct-sum solutions

Pre-composing a solution with the dual injection of its own summand collapses the
Cuntz orthogonality, leaving the summand's solution.  These are the algebraic
heart of the four conjugate equations. -/

/-- `q₁⋆ · R = ρ̄(p₁) · R_ρ`: collapsing `R` along the first conjugate injection. -/
lemma Conjugate.directSumR_qfst (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star q.v₁ * (cρ.directSumR p q cσ).t = cρ.bar.endo p.v₁ * cρ.R.t := by
  rw [directSumR_t,
    show star q.v₁ * (q.v₁ * cρ.bar.endo p.v₁ * cρ.R.t + q.v₂ * cσ.bar.endo p.v₂ * cσ.R.t)
        = (star q.v₁ * q.v₁) * (cρ.bar.endo p.v₁ * cρ.R.t)
          + (star q.v₁ * q.v₂) * (cσ.bar.endo p.v₂ * cσ.R.t) from by noncomm_ring,
    q.isom₁, q.orth₁₂, one_mul, zero_mul, add_zero]

/-- `q₂⋆ · R = σ̄(p₂) · R_σ`: collapsing `R` along the second conjugate injection. -/
lemma Conjugate.directSumR_qsnd (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star q.v₂ * (cρ.directSumR p q cσ).t = cσ.bar.endo p.v₂ * cσ.R.t := by
  rw [directSumR_t,
    show star q.v₂ * (q.v₁ * cρ.bar.endo p.v₁ * cρ.R.t + q.v₂ * cσ.bar.endo p.v₂ * cσ.R.t)
        = (star q.v₂ * q.v₁) * (cρ.bar.endo p.v₁ * cρ.R.t)
          + (star q.v₂ * q.v₂) * (cσ.bar.endo p.v₂ * cσ.R.t) from by noncomm_ring,
    q.orth₂₁, q.isom₂, zero_mul, one_mul, zero_add]

/-- `p₁⋆ · R̄ = ρ(q₁) · R̄_ρ`: collapsing `R̄` along the first injection. -/
lemma Conjugate.directSumRbar_pfst (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star p.v₁ * (cρ.directSumRbar p q cσ).t = ρ.endo q.v₁ * cρ.Rbar.t := by
  rw [directSumRbar_t,
    show star p.v₁ * (p.v₁ * ρ.endo q.v₁ * cρ.Rbar.t + p.v₂ * σ.endo q.v₂ * cσ.Rbar.t)
        = (star p.v₁ * p.v₁) * (ρ.endo q.v₁ * cρ.Rbar.t)
          + (star p.v₁ * p.v₂) * (σ.endo q.v₂ * cσ.Rbar.t) from by noncomm_ring,
    p.isom₁, p.orth₁₂, one_mul, zero_mul, add_zero]

/-- `p₂⋆ · R̄ = σ(q₂) · R̄_σ`: collapsing `R̄` along the second injection. -/
lemma Conjugate.directSumRbar_psnd (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star p.v₂ * (cρ.directSumRbar p q cσ).t = σ.endo q.v₂ * cσ.Rbar.t := by
  rw [directSumRbar_t,
    show star p.v₂ * (p.v₁ * ρ.endo q.v₁ * cρ.Rbar.t + p.v₂ * σ.endo q.v₂ * cσ.Rbar.t)
        = (star p.v₂ * p.v₁) * (ρ.endo q.v₁ * cρ.Rbar.t)
          + (star p.v₂ * p.v₂) * (σ.endo q.v₂ * cσ.Rbar.t) from by noncomm_ring,
    p.orth₂₁, p.isom₂, zero_mul, one_mul, zero_add]

/-- The starred coevaluation `R⋆` in block form. -/
lemma Conjugate.directSumR_star_t (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star (cρ.directSumR p q cσ).t
      = star cρ.R.t * cρ.bar.endo (star p.v₁) * star q.v₁
        + star cσ.R.t * cσ.bar.endo (star p.v₂) * star q.v₂ := by
  rw [directSumR_t]
  simp only [star_add, star_mul, map_star]
  noncomm_ring

/-- The starred coevaluation `R̄⋆` in block form. -/
lemma Conjugate.directSumRbar_star_t (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star (cρ.directSumRbar p q cσ).t
      = star cρ.Rbar.t * ρ.endo (star q.v₁) * star p.v₁
        + star cσ.Rbar.t * σ.endo (star q.v₂) * star p.v₂ := by
  rw [directSumRbar_t]
  simp only [star_add, star_mul, map_star]
  noncomm_ring

/-! ### The four conjugate equations for a direct sum

`eq3` and `eq1` are proved directly by collapsing the Cuntz blocks; `eq2` and
`eq4` then follow by taking adjoints (`star`), since the conjugate equations come
in adjoint pairs (`eq2 = star eq3`, `eq4 = star eq1`). -/

/-- The third conjugate equation (`R`-snake) for the direct sum. -/
lemma Conjugate.directSumEq3 (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star (cρ.directSumRbar p q cσ).t *
      (p.directSum ρ σ).endo (cρ.directSumR p q cσ).t = 1 := by
  rw [IsometryPair.directSum_endo_apply, directSumRbar_star_t, add_mul, mul_add, mul_add,
    IsometryPair.block_collapse (star cρ.Rbar.t) (ρ.endo (star q.v₁)) p.v₁
      (ρ.endo (cρ.directSumR p q cσ).t) p.v₁ p.isom₁,
    IsometryPair.block_vanish (star cρ.Rbar.t) (ρ.endo (star q.v₁)) p.v₁ p.v₂
      (σ.endo (cρ.directSumR p q cσ).t) p.v₂ p.orth₁₂,
    IsometryPair.block_vanish (star cσ.Rbar.t) (σ.endo (star q.v₂)) p.v₂ p.v₁
      (ρ.endo (cρ.directSumR p q cσ).t) p.v₁ p.orth₂₁,
    IsometryPair.block_collapse (star cσ.Rbar.t) (σ.endo (star q.v₂)) p.v₂
      (σ.endo (cρ.directSumR p q cσ).t) p.v₂ p.isom₂,
    add_zero, zero_add,
    ← map_mul ρ.endo, ← map_mul σ.endo, cρ.directSumR_qfst p q cσ, cρ.directSumR_qsnd p q cσ,
    map_mul ρ.endo, map_mul σ.endo,
    show star cρ.Rbar.t * (ρ.endo (cρ.bar.endo p.v₁) * ρ.endo cρ.R.t) * star p.v₁
        = star cρ.Rbar.t * ρ.endo (cρ.bar.endo p.v₁) * ρ.endo cρ.R.t * star p.v₁ from by
          noncomm_ring,
    show star cσ.Rbar.t * (σ.endo (cσ.bar.endo p.v₂) * σ.endo cσ.R.t) * star p.v₂
        = star cσ.Rbar.t * σ.endo (cσ.bar.endo p.v₂) * σ.endo cσ.R.t * star p.v₂ from by
          noncomm_ring,
    cρ.Rbar_intertwine_star, cσ.Rbar_intertwine_star,
    show p.v₁ * star cρ.Rbar.t * ρ.endo cρ.R.t * star p.v₁
        = p.v₁ * (star cρ.Rbar.t * ρ.endo cρ.R.t) * star p.v₁ from by noncomm_ring,
    show p.v₂ * star cσ.Rbar.t * σ.endo cσ.R.t * star p.v₂
        = p.v₂ * (star cσ.Rbar.t * σ.endo cσ.R.t) * star p.v₂ from by noncomm_ring,
    cρ.eq3, cσ.eq3, mul_one, mul_one, p.complete]

/-- The first conjugate equation (`R̄`-snake) for the direct sum. -/
lemma Conjugate.directSumEq1 (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star (cρ.directSumR p q cσ).t *
      (q.directSum cρ.bar cσ.bar).endo (cρ.directSumRbar p q cσ).t = 1 := by
  rw [IsometryPair.directSum_endo_apply, directSumR_star_t, add_mul, mul_add, mul_add,
    IsometryPair.block_collapse (star cρ.R.t) (cρ.bar.endo (star p.v₁)) q.v₁
      (cρ.bar.endo (cρ.directSumRbar p q cσ).t) q.v₁ q.isom₁,
    IsometryPair.block_vanish (star cρ.R.t) (cρ.bar.endo (star p.v₁)) q.v₁ q.v₂
      (cσ.bar.endo (cρ.directSumRbar p q cσ).t) q.v₂ q.orth₁₂,
    IsometryPair.block_vanish (star cσ.R.t) (cσ.bar.endo (star p.v₂)) q.v₂ q.v₁
      (cρ.bar.endo (cρ.directSumRbar p q cσ).t) q.v₁ q.orth₂₁,
    IsometryPair.block_collapse (star cσ.R.t) (cσ.bar.endo (star p.v₂)) q.v₂
      (cσ.bar.endo (cρ.directSumRbar p q cσ).t) q.v₂ q.isom₂,
    add_zero, zero_add,
    ← map_mul cρ.bar.endo, ← map_mul cσ.bar.endo, cρ.directSumRbar_pfst p q cσ,
    cρ.directSumRbar_psnd p q cσ, map_mul cρ.bar.endo, map_mul cσ.bar.endo,
    show star cρ.R.t * (cρ.bar.endo (ρ.endo q.v₁) * cρ.bar.endo cρ.Rbar.t) * star q.v₁
        = star cρ.R.t * cρ.bar.endo (ρ.endo q.v₁) * cρ.bar.endo cρ.Rbar.t * star q.v₁ from by
          noncomm_ring,
    show star cσ.R.t * (cσ.bar.endo (σ.endo q.v₂) * cσ.bar.endo cσ.Rbar.t) * star q.v₂
        = star cσ.R.t * cσ.bar.endo (σ.endo q.v₂) * cσ.bar.endo cσ.Rbar.t * star q.v₂ from by
          noncomm_ring,
    cρ.R_intertwine_star, cσ.R_intertwine_star,
    show q.v₁ * star cρ.R.t * cρ.bar.endo cρ.Rbar.t * star q.v₁
        = q.v₁ * (star cρ.R.t * cρ.bar.endo cρ.Rbar.t) * star q.v₁ from by noncomm_ring,
    show q.v₂ * star cσ.R.t * cσ.bar.endo cσ.Rbar.t * star q.v₂
        = q.v₂ * (star cσ.R.t * cσ.bar.endo cσ.Rbar.t) * star q.v₂ from by noncomm_ring,
    cρ.eq1, cσ.eq1, mul_one, mul_one, q.complete]

/-- The second conjugate equation, the adjoint of `eq3`. -/
lemma Conjugate.directSumEq2 (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (p.directSum ρ σ).endo (star (cρ.directSumR p q cσ).t) *
      (cρ.directSumRbar p q cσ).t = 1 := by
  have h := congrArg star (cρ.directSumEq3 p q cσ)
  rwa [star_mul, star_star, ← map_star, star_one] at h

/-- The fourth conjugate equation, the adjoint of `eq1`. -/
lemma Conjugate.directSumEq4 (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (q.directSum cρ.bar cσ.bar).endo (star (cρ.directSumRbar p q cσ).t) *
      (cρ.directSumR p q cσ).t = 1 := by
  have h := congrArg star (cρ.directSumEq1 p q cσ)
  rwa [star_mul, star_star, ← map_star, star_one] at h

/-- **The conjugate of a direct sum is the direct sum of the conjugates**
(Müger §1.5): given Cuntz pairs `p` for `ρ ⊕ σ` and `q` for `ρ̄ ⊕ σ̄`, the object
`ρ̄ ⊕ σ̄` (built with `q`) is a conjugate of `ρ ⊕ σ` (built with `p`).  This is the
rigid half of C\*-completeness and yields the dimension additivity
`d(ρ ⊕ σ) = d(ρ) + d(σ)`. -/
noncomputable def Conjugate.directSum (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) : Conjugate (p.directSum ρ σ) where
  bar := q.directSum cρ.bar cσ.bar
  R := cρ.directSumR p q cσ
  Rbar := cρ.directSumRbar p q cσ
  eq1 := cρ.directSumEq1 p q cσ
  eq2 := cρ.directSumEq2 p q cσ
  eq3 := cρ.directSumEq3 p q cσ
  eq4 := cρ.directSumEq4 p q cσ

/-- **Dimension additivity** `d(ρ ⊕ σ) = d(ρ) + d(σ)` (Müger §1.5): the left
dimension of the direct-sum conjugate is the sum of the summand dimensions.  This
is the payoff of `Conjugate.directSum`. -/
lemma Conjugate.directSum_dim_t (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (cρ.directSum p q cσ).dim.t = cρ.dim.t + cσ.dim.t := by
  simp only [Conjugate.dim_t]
  change star (cρ.directSumR p q cσ).t * (cρ.directSumR p q cσ).t
      = star cρ.R.t * cρ.R.t + star cσ.R.t * cσ.R.t
  rw [directSumR_star_t, add_mul,
    show star cρ.R.t * cρ.bar.endo (star p.v₁) * star q.v₁ * (cρ.directSumR p q cσ).t
        = star cρ.R.t * cρ.bar.endo (star p.v₁) * (star q.v₁ * (cρ.directSumR p q cσ).t) from by
          noncomm_ring,
    show star cσ.R.t * cσ.bar.endo (star p.v₂) * star q.v₂ * (cρ.directSumR p q cσ).t
        = star cσ.R.t * cσ.bar.endo (star p.v₂) * (star q.v₂ * (cρ.directSumR p q cσ).t) from by
          noncomm_ring,
    cρ.directSumR_qfst p q cσ, cρ.directSumR_qsnd p q cσ,
    show star cρ.R.t * cρ.bar.endo (star p.v₁) * (cρ.bar.endo p.v₁ * cρ.R.t)
        = star cρ.R.t * (cρ.bar.endo (star p.v₁) * cρ.bar.endo p.v₁) * cρ.R.t from by noncomm_ring,
    show star cσ.R.t * cσ.bar.endo (star p.v₂) * (cσ.bar.endo p.v₂ * cσ.R.t)
        = star cσ.R.t * (cσ.bar.endo (star p.v₂) * cσ.bar.endo p.v₂) * cσ.R.t from by noncomm_ring,
    ← map_mul cρ.bar.endo, ← map_mul cσ.bar.endo, p.isom₁, p.isom₂, map_one, map_one,
    mul_one, mul_one]

/-- **Right-dimension additivity** `d̄(ρ ⊕ σ) = d̄(ρ) + d̄(σ)` (Müger §1.5): the mirror of
`directSum_dim_t` for `dim'`, collapsing `R̄` along the injections (`directSumRbar_pfst`,
`directSumRbar_psnd`) and using the isometry relations of `q`. -/
lemma Conjugate.directSum_dim'_t (p q : IsometryPair A)
    (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (cρ.directSum p q cσ).dim'.t = cρ.dim'.t + cσ.dim'.t := by
  simp only [Conjugate.dim'_t]
  change star (cρ.directSumRbar p q cσ).t * (cρ.directSumRbar p q cσ).t
      = star cρ.Rbar.t * cρ.Rbar.t + star cσ.Rbar.t * cσ.Rbar.t
  rw [directSumRbar_star_t, add_mul,
    show star cρ.Rbar.t * ρ.endo (star q.v₁) * star p.v₁ * (cρ.directSumRbar p q cσ).t
        = star cρ.Rbar.t * ρ.endo (star q.v₁) * (star p.v₁ * (cρ.directSumRbar p q cσ).t) from by
          noncomm_ring,
    show star cσ.Rbar.t * σ.endo (star q.v₂) * star p.v₂ * (cρ.directSumRbar p q cσ).t
        = star cσ.Rbar.t * σ.endo (star q.v₂) * (star p.v₂ * (cρ.directSumRbar p q cσ).t) from by
          noncomm_ring,
    cρ.directSumRbar_pfst p q cσ, cρ.directSumRbar_psnd p q cσ,
    show star cρ.Rbar.t * ρ.endo (star q.v₁) * (ρ.endo q.v₁ * cρ.Rbar.t)
        = star cρ.Rbar.t * (ρ.endo (star q.v₁) * ρ.endo q.v₁) * cρ.Rbar.t from by noncomm_ring,
    show star cσ.Rbar.t * σ.endo (star q.v₂) * (σ.endo q.v₂ * cσ.Rbar.t)
        = star cσ.Rbar.t * (σ.endo (star q.v₂) * σ.endo q.v₂) * cσ.Rbar.t from by noncomm_ring,
    ← map_mul ρ.endo, ← map_mul σ.endo, q.isom₁, q.isom₂, map_one, map_one,
    mul_one, mul_one]

end StarEndo

end CategoryTheory
