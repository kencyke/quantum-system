module

public import QuantumSystem.ForMathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Pinching Map via Root-of-Unity Unitary Averaging

The pinching map extracts the block-diagonal part of a matrix by averaging
over root-of-unity diagonal unitaries.

## Main definitions

* `pinchingUnitary r k`: The k-th diagonal unitary on `Fin r × m`, defined by
  `(U_k)_{(i,a)(j,b)} = δ_{ij} δ_{ab} ζ^{ik}` where `ζ = e^{2πi/r}`.

## Main results

* `pinchingUnitary_isUnitary`: Each pinching unitary is unitary.
* `pinching_average_eq_blockDiag`: Averaging `U_k ω U_k†` over `k` extracts
  the block diagonal: `(1/r) ∑_k (U_k ω U_k†)_{(i,a)(j,b)} = δ_{ij} ω_{(i,a)(j,b)}`.
* `splitFinSuccProdEquiv`: Canonical equivalence `Fin (n+1) × m ≃ m ⊕ (Fin n × m)`.

## References

* Lindblad, *Completely positive maps and entropy inequalities*
-/

@[expose] public section

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ### Pinching unitaries -/

/-- **Pinching diagonal unitary**: The k-th diagonal unitary on (Fin r × m) is
defined by (U_k)_{(i,a)(j,b)} = δ_{ij} δ_{ab} ζ^{ik}
where ζ = e^{2πi/r}. -/
noncomputable def pinchingUnitary (r : ℕ) [NeZero r] (k : Fin r) :
    Matrix (Fin r × m) (Fin r × m) ℂ :=
  Matrix.diagonal fun ⟨i, _⟩ => (rootOfUnity r) ^ ((i.val * k.val : ℕ) : ℤ)

omit [Fintype m] in
lemma pinchingUnitary_entry {r : ℕ} [NeZero r] (k : Fin r) (i j : Fin r) (a b : m) :
    pinchingUnitary r k (i, a) (j, b) =
    if i = j ∧ a = b then (rootOfUnity r) ^ ((i.val * k.val : ℕ) : ℤ) else 0 := by
  simp only [pinchingUnitary, Matrix.diagonal_apply, Prod.mk.injEq]

lemma pinchingUnitary_isUnitary {r : ℕ} [NeZero r] (k : Fin r) :
    (pinchingUnitary r k) ∈ Matrix.unitaryGroup (Fin r × m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext ⟨i, a⟩ ⟨j, b⟩
  -- For diagonal D, (Dᴴ * D)_{(i,a)(j,b)} = ∑_x (Dᴴ)_{(i,a)x} * D_{x(j,b)}
  simp only [pinchingUnitary, Matrix.mul_apply, Matrix.one_apply, Prod.mk.injEq]
  -- star (diagonal f) is the conjTranspose, so (star (diagonal f))_{ia,x} = star((diagonal f)_{x,ia})
  simp only [Matrix.star_apply, Matrix.diagonal_apply]
  by_cases h : i = j ∧ a = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [true_and, ↓reduceIte]
    -- Only x = (i, a) contributes to the sum
    have hsum : ∑ x : Fin r × m,
        star (if x = (i, a) then rootOfUnity r ^ ((x.1.val * k.val : ℕ) : ℤ) else 0) *
        (if x = (i, a) then rootOfUnity r ^ ((x.1.val * k.val : ℕ) : ℤ) else 0) =
        star (rootOfUnity r ^ ((i.val * k.val : ℕ) : ℤ)) * rootOfUnity r ^ ((i.val * k.val : ℕ) : ℤ) := by
      convert Finset.sum_eq_single (i, a) ?_ ?_ using 1
      · simp only [↓reduceIte]
      · intro x _ hne
        simp only [if_neg hne, star_zero, zero_mul]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    rw [hsum]
    -- star(z) * z = |z|^2 = 1 for z on unit circle
    have hnorm : ‖rootOfUnity r ^ ((i.val * k.val : ℕ) : ℤ)‖ = 1 := by
      rw [Complex.norm_zpow]
      simp [rootOfUnity_norm]
    -- For z ≠ 0 with |z| = 1, we have star(z) * z = |z|^2 = 1
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.ofReal_eq_one]
    rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
  · simp only [h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro x _
    by_cases h1 : x = (i, a)
    · by_cases h2 : x = (j, b)
      · -- x = (i, a) and x = (j, b) means (i, a) = (j, b), contradiction with h
        have heq : (i, a) = (j, b) := Eq.trans h1.symm h2
        exact absurd ⟨Prod.mk.inj heq |>.1, Prod.mk.inj heq |>.2⟩ h
      · simp only [h2, ↓reduceIte, mul_zero]
    · simp only [h1, ↓reduceIte, star_zero, zero_mul]

omit [Fintype m] in
lemma pinchingUnitary_conjTranspose {r : ℕ} [NeZero r] (k : Fin r) :
    (pinchingUnitary r k)ᴴ = Matrix.diagonal (fun (p : Fin r × m) => (rootOfUnity r) ^ (-((p.1.val * k.val : ℕ) : ℤ))) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [pinchingUnitary, Matrix.diagonal_conjTranspose, Pi.star_apply,
    Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases h : j = i ∧ b = a
  · obtain ⟨rfl, rfl⟩ := h
    simp only [true_and, ↓reduceIte]
    -- star(ζ^n) = (star ζ)^n = (ζ⁻¹)^n = ζ^(-n)
    rw [star_zpow₀, rootOfUnity_star, _root_.inv_zpow']
  · have h' : ¬(i = j ∧ a = b) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
    simp only [h', ↓reduceIte]

/-! ### Pinching average extracts block diagonal -/

/-- Averaging over pinching unitaries extracts block-diagonal:
(1/r) ∑ₖ (Uₖ ω Uₖ†)_(i,a)(j,b) = δᵢⱼ ω_(i,a)(i,b). -/
lemma pinching_average_eq_blockDiag {r : ℕ} [NeZero r]
    (ω : Matrix (Fin r × m) (Fin r × m) ℂ) (i j : Fin r) (a b : m) :
    (1 / r : ℂ) * ∑ k : Fin r, ((pinchingUnitary r k) * ω * (pinchingUnitary r k)ᴴ : Matrix _ _ _) (i, a) (j, b) =
    if i = j then ω (i, a) (j, b) else 0 := by
  -- For diagonal U_k with U_k(p,p) = ζ^(p.1*k), we have:
  -- (U_k ω U_k^†)_{(ia)(jb)} = ζ^(i*k) ω_{(ia)(jb)} ζ^(-j*k)
  have hdiag : ∀ k : Fin r,
      ((pinchingUnitary r k) * ω * (pinchingUnitary r k)ᴴ : Matrix _ _ _) (i, a) (j, b) =
      (rootOfUnity r) ^ ((i.val * k.val : ℕ) : ℤ) * ω (i, a) (j, b) *
      (rootOfUnity r) ^ (-((j.val * k.val : ℕ) : ℤ)) := by
    intro k
    simp only [Matrix.mul_apply]
    -- pinchingUnitary is diagonal, so only x = (i, a) survives in first sum
    -- and only y = (j, b) survives in second sum
    -- The goal is: ∑ x, (∑ t, pinchingUnitary r k (i, a) t * ω t x) * (pinchingUnitary r k)ᴴ x (j, b) = ...
    -- Rewrite using diagonal property of pinchingUnitary
    have hsimplify : ∑ x : Fin r × m, (∑ t : Fin r × m, pinchingUnitary r k (i, a) t * ω t x) *
        (pinchingUnitary r k)ᴴ x (j, b) =
        (rootOfUnity r) ^ ((i.val * k.val : ℕ) : ℤ) * ω (i, a) (j, b) *
        (rootOfUnity r) ^ (-((j.val * k.val : ℕ) : ℤ)) := by
      -- First, simplify the inner sum using diagonal property
      have h_inner : ∀ x : Fin r × m, ∑ t : Fin r × m, pinchingUnitary r k (i, a) t * ω t x =
          pinchingUnitary r k (i, a) (i, a) * ω (i, a) x := by
        intro x
        apply Finset.sum_eq_single (i, a)
        · intro t _ hne
          rw [pinchingUnitary_entry]
          have hne_cond : ¬(i = t.1 ∧ a = t.2) := by
            intro ⟨h1, h2⟩
            have : t = (i, a) := Prod.ext h1.symm h2.symm
            exact hne this
          simp only [hne_cond, ↓reduceIte, zero_mul]
        · intro habs; exact absurd (Finset.mem_univ _) habs
      simp_rw [h_inner]
      -- Now the outer sum simplifies similarly
      rw [Finset.sum_eq_single (j, b)]
      -- Main case: x = (j, b)
      · rw [pinchingUnitary_entry, pinchingUnitary_conjTranspose, Matrix.diagonal_apply]
        simp only [true_and, ↓reduceIte]
      · intro x _ hne
        rw [pinchingUnitary_conjTranspose, Matrix.diagonal_apply]
        simp only [hne, ↓reduceIte, mul_zero]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    exact hsimplify
  simp_rw [hdiag]
  -- Now sum over k: ζ^(i*k) * ω * ζ^(-j*k) = ω * ζ^((i-j)*k)
  have hζne : rootOfUnity r ≠ 0 := rootOfUnity_ne_zero r
  have hcombine : ∀ k : Fin r,
      (rootOfUnity r) ^ ((i.val * k.val : ℕ) : ℤ) * ω (i, a) (j, b) *
      (rootOfUnity r) ^ (-((j.val * k.val : ℕ) : ℤ)) =
      ω (i, a) (j, b) * (rootOfUnity r) ^ (((i.val : ℤ) - (j.val : ℤ)) * (k.val : ℤ)) := by
    intro k
    -- Rewrite ζ^(-n) = (ζ^n)⁻¹ using zpow_neg with explicit arguments
    have h1 : (rootOfUnity r) ^ (-((j.val * k.val : ℕ) : ℤ)) = ((rootOfUnity r) ^ ((j.val * k.val : ℕ) : ℤ))⁻¹ := by
      rw [_root_.zpow_neg (rootOfUnity r) ((j.val * k.val : ℕ) : ℤ)]
    rw [h1]
    -- Now goal: ζ^(ik) * ω * (ζ^(jk))⁻¹ = ω * ζ^((i-j)*k)
    have h2 : (rootOfUnity r) ^ ((i.val * k.val : ℕ) : ℤ) * ω (i, a) (j, b) *
        ((rootOfUnity r) ^ ((j.val * k.val : ℕ) : ℤ))⁻¹ =
        ω (i, a) (j, b) * ((rootOfUnity r) ^ ((i.val * k.val : ℕ) : ℤ) *
        ((rootOfUnity r) ^ ((j.val * k.val : ℕ) : ℤ))⁻¹) := by ring
    rw [h2]
    congr 1
    rw [mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hζne), ← zpow_add₀ hζne]
    congr 1
    push_cast
    ring
  simp_rw [hcombine]
  rw [← Finset.mul_sum, mul_comm (1 / r : ℂ), mul_assoc]
  -- Use root of unity sum
  by_cases hij : i = j
  · subst hij
    simp only [sub_self, zero_mul, zpow_zero, Finset.sum_const, Finset.card_fin, ↓reduceIte]
    rw [nsmul_eq_mul, mul_one]
    -- Goal: ↑r * (1 / ↑r * ω (i, a) (i, b)) = ω (i, a) (i, b)
    have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
    field_simp
  · have hdiff : ((i.val : ℤ) - j.val) % (r : ℤ) ≠ 0 := by
      intro h
      -- i.val, j.val ∈ [0, r), so i.val - j.val ∈ (-r, r)
      -- If (i.val - j.val) % r = 0 and -r < (i.val - j.val) < r, then i.val - j.val = 0
      have hbound_lo : -(r : ℤ) < (i.val : ℤ) - j.val := by
        have : (j.val : ℤ) < r := Int.ofNat_lt.mpr j.isLt
        have : (0 : ℤ) ≤ i.val := Int.natCast_nonneg _
        omega
      have hbound_hi : (i.val : ℤ) - j.val < r := by
        have : (i.val : ℤ) < r := Int.ofNat_lt.mpr i.isLt
        have : (0 : ℤ) ≤ j.val := Int.natCast_nonneg _
        omega
      have hr_pos : (0 : ℤ) < r := Int.natCast_pos.mpr (NeZero.pos r)
      -- The only multiple of r in (-r, r) is 0
      have heq_zero : (i.val : ℤ) - j.val = 0 := by
        have hdvd := Int.dvd_of_emod_eq_zero h
        obtain ⟨k, hk⟩ := hdvd
        -- hk : (i : ℤ) - j = r * k
        -- From -r < r * k < r and r > 0, we get k = 0
        have hk_bound : k = 0 := by
          have hkr : (r : ℤ) * k = (i.val : ℤ) - j.val := hk.symm
          rcases Int.lt_trichotomy k 0 with hk_neg | hk_zero | hk_pos
          · -- k < 0 implies k ≤ -1, so r * k ≤ -r < hbound_lo, contradiction
            have h1 : (r : ℤ) * k ≤ -r := by nlinarith
            have h2 : (r : ℤ) * k > -r := by rw [hkr]; exact hbound_lo
            linarith
          · exact hk_zero
          · -- k > 0 implies k ≥ 1, so r * k ≥ r > hbound_hi, contradiction
            have h1 : (r : ℤ) * k ≥ r := by nlinarith
            have h2 : (r : ℤ) * k < r := by rw [hkr]; exact hbound_hi
            linarith
        simp only [hk_bound, mul_zero] at hk
        exact hk
      have hival : i.val = j.val := by omega
      exact hij (Fin.ext hival)
    have hrsum := rootOfUnity_sum_eq_zero r ((i.val : ℤ) - j.val) hdiff
    rw [hrsum]
    simp only [mul_zero, zero_mul, if_neg hij]

/-! ### Fin product equivalence -/

/-- Canonical equivalence `Fin (n + 1) × m ≃ m ⊕ (Fin n × m)`. -/
def splitFinSuccProdEquiv (n : ℕ) (m : Type*) :
    Fin (n + 1) × m ≃ m ⊕ (Fin n × m) where
  toFun p := if h : (p.1 : ℕ) = 0 then Sum.inl p.2
    else Sum.inr (⟨(p.1 : ℕ) - 1, by omega⟩, p.2)
  invFun x := match x with
    | Sum.inl a => (⟨0, by omega⟩, a)
    | Sum.inr (i, a) => (i.succ, a)
  left_inv := by
    rintro ⟨⟨i, hi⟩, a⟩
    by_cases h : i = 0
    · subst h; rfl
    · have hne : ¬((⟨i, hi⟩ : Fin (n + 1)) : ℕ) = 0 := h
      simp only [hne, dite_false]
      refine Prod.ext (Fin.ext ?_) rfl
      simp only [Fin.val_succ]
      omega
  right_inv := by
    rintro (a | ⟨⟨i, hi⟩, a⟩)
    · rfl
    · have hne : ¬((⟨i, hi⟩ : Fin n).succ : ℕ) = 0 := by
        rw [Fin.val_succ]; exact Nat.succ_ne_zero _
      simp only [hne, dite_false]
      refine congr_arg Sum.inr (Prod.ext (Fin.ext ?_) rfl)
      simp only [Fin.val_succ]
      omega

end Matrix
