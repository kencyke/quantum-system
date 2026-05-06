module

public import QuantumSystem.Algebra.LocalNet
public import QuantumSystem.Channel

/-!
# Partial trace as restriction (matrix-level)

The **restriction** (Schrödinger-picture partial trace) on the matrix algebra of a local
net. Given regions `Λ ⊆ Λ_total` of a `LocalNet`, the restriction of a matrix on
`𝔄(Λ_total)` to `𝔄(Λ)` is defined as the partial trace over the complementary region
`Λ_total \ Λ`. This is the Schrödinger-picture dual of the algebra
inclusion `𝔄(Λ) ↪ 𝔄(Λ_total)`. There is no positional ("left/right") concept — the
operation is parameterised by the region itself.

The matrix-level operation `Matrix.restrict` is defined as a linear map factoring through
`LocalNet.combineIdx` (which factors `regionIdx Λ_total ≃ regionIdx Λ × regionIdx (Λ_total \ Λ)`).
The bundled quantum-channel structure, Kraus operators, trace preservation, and
Heisenberg-picture duality are also provided.

## Main definitions

* `Matrix.restrict` — linear restriction map (matrix-level partial trace)
* `Matrix.restrictKraus` — Kraus operators indexed by the complementary region
* `Matrix.QuantumChannel.restrict` — bundled quantum channel
* `DensityMatrix.restrict` — restriction applied to density matrices
* `ρ ↾ Λ` — paper-style notation for `DensityMatrix.restrict`

## Main results

* `Matrix.restrict_eq_sum_kraus` — Kraus form
* `Matrix.isCompletelyPositive_restrict`, `Matrix.isTracePreserving_restrict`,
  `Matrix.isQuantumChannel_restrict` — channel properties
* `Matrix.restrict_restrict` — iterated marginalisation = direct marginalisation
* `Matrix.trace_mul_includeAlgebra` — Heisenberg-picture trace identity

## References

* Sorce 2024 (`https://arxiv.org/abs/2408.07994`)
* Verch 2025 (`https://arxiv.org/abs/2507.00900`)
* Naaijkens 2012 (`https://repository.ubn.ru.nl/handle/2066/92737`)
-/

@[expose] public section

namespace Matrix

variable {L : LocalNet}

/-! ### Linear restriction map -/

/-- **Restriction of a matrix to a sub-region** (Schrödinger-picture partial trace).
    Sums over indices of the complementary region `Λ_total \ Λ`. -/
noncomputable def restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.localAlgebra Λ_total →ₗ[ℂ] L.localAlgebra Λ where
  toFun M := Matrix.of fun a a' =>
    ∑ b : L.regionIdx (Λ_total \ Λ),
      M (L.combineIdx h (a, b)) (L.combineIdx h (a', b))
  map_add' M N := by
    ext a a'
    simp only [Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c M := by
    ext a a'
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]

@[simp] lemma restrict_apply {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (M : L.localAlgebra Λ_total) (a a' : L.regionIdx Λ) :
    restrict h M a a' =
      ∑ b : L.regionIdx (Λ_total \ Λ),
        M (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) := rfl

/-! ### Trace preservation -/

/-- `Tr(restrict h M) = Tr M`: the restriction preserves the global trace. -/
theorem trace_restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (M : L.localAlgebra Λ_total) :
    Tr (restrict h M) = Tr M := by
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, restrict_apply]
  -- LHS: ∑ a, ∑ b, M (combineIdx (a,b)) (combineIdx (a,b))
  -- RHS: ∑ s : regionIdx Λ_total, M s s
  -- Step 1: combine the double sum into a sum over the product type
  rw [show (∑ a : L.regionIdx Λ, ∑ b : L.regionIdx (Λ_total \ Λ),
        M ((L.combineIdx h) (a, b)) ((L.combineIdx h) (a, b))) =
      ∑ p : L.regionIdx Λ × L.regionIdx (Λ_total \ Λ),
        M ((L.combineIdx h) p) ((L.combineIdx h) p) from
    (Fintype.sum_prod_type
      (fun p : L.regionIdx Λ × L.regionIdx (Λ_total \ Λ) =>
        M ((L.combineIdx h) p) ((L.combineIdx h) p))).symm]
  -- Step 2: reindex via combineIdx
  exact (L.combineIdx h).sum_comp (fun s => M s s)

theorem isTracePreserving_restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    IsTracePreserving (restrict (L := L) h) :=
  trace_restrict h

/-! ### Kraus operators and complete positivity -/

/-- Kraus operator for `restrict h`, indexed by `b : regionIdx (Λ_total \ Λ)`:
    `K_b a a_total = [a_total = combineIdx h (a, b)]`. -/
noncomputable def restrictKraus {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (b : L.regionIdx (Λ_total \ Λ)) :
    Matrix (L.regionIdx Λ) (L.regionIdx Λ_total) ℂ :=
  Matrix.of fun a a_total =>
    if a_total = L.combineIdx h (a, b) then (1 : ℂ) else 0

private lemma restrictKraus_apply {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (b : L.regionIdx (Λ_total \ Λ)) (a : L.regionIdx Λ) (a_total : L.regionIdx Λ_total) :
    restrictKraus h b a a_total =
      if a_total = L.combineIdx h (a, b) then (1 : ℂ) else 0 := rfl

/-- Entry-wise: `(K_b * M * K_bᴴ) a a' = M (combineIdx (a, b)) (combineIdx (a', b))`. -/
private lemma restrictKraus_mul_mul_apply {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (M : L.localAlgebra Λ_total) (b : L.regionIdx (Λ_total \ Λ))
    (a a' : L.regionIdx Λ) :
    ((restrictKraus h b * M : Matrix (L.regionIdx Λ) (L.regionIdx Λ_total) ℂ) *
        (restrictKraus h b)ᴴ : L.localAlgebra Λ) a a' =
      M (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
  -- Outer sum: ∑ p, (K_b * M)(a, p) * star (K_b a' p)
  --          = ∑ p, (∑ q, K_b a q * M q p) * star (K_b a' p)
  -- K_b a' p = 1 iff p = combineIdx (a', b), so outer sum collapses at p = combineIdx (a', b)
  rw [Finset.sum_eq_single (L.combineIdx h (a', b))]
  · -- inner sum collapses at q = combineIdx (a, b)
    rw [Finset.sum_eq_single (L.combineIdx h (a, b))]
    · simp [restrictKraus_apply]
    · intro q _ hq
      simp only [restrictKraus_apply]
      rw [if_neg hq]; ring
    · simp
  · intro p _ hp
    simp only [restrictKraus_apply, apply_ite (star · : ℂ → ℂ),
      star_one, star_zero]
    rw [if_neg hp]
    simp
  · simp

/-- Kraus form of the restriction. -/
theorem restrict_eq_sum_kraus {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (M : L.localAlgebra Λ_total) :
    restrict h M =
      ∑ b : L.regionIdx (Λ_total \ Λ),
        ((restrictKraus h b * M : Matrix (L.regionIdx Λ) (L.regionIdx Λ_total) ℂ) *
            (restrictKraus h b)ᴴ : L.localAlgebra Λ) := by
  ext a a'
  rw [restrict_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (restrictKraus_mul_mul_apply h M b a a').symm

theorem isCompletelyPositive_restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    IsCompletelyPositive (restrict (L := L) h) := by
  classical
  refine ⟨Fintype.card (L.regionIdx (Λ_total \ Λ)),
    fun i => restrictKraus h ((Fintype.equivFin (L.regionIdx (Λ_total \ Λ))).symm i), ?_⟩
  intro M
  rw [restrict_eq_sum_kraus]
  -- Reindex the regionIdx-sum via (equivFin _).symm : Fin r ≃ regionIdx
  exact ((Fintype.equivFin (L.regionIdx (Λ_total \ Λ))).symm.sum_comp
    (fun b : L.regionIdx (Λ_total \ Λ) =>
      ((restrictKraus h b * M : Matrix (L.regionIdx Λ) (L.regionIdx Λ_total) ℂ) *
        (restrictKraus h b)ᴴ : L.localAlgebra Λ))).symm

theorem isQuantumChannel_restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    IsQuantumChannel (restrict (L := L) h) where
  completelyPositive := isCompletelyPositive_restrict h
  tracePreserving := isTracePreserving_restrict h

/-- Restriction as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    Matrix.QuantumChannel (L.regionIdx Λ_total) (L.regionIdx Λ) :=
  ⟨Matrix.restrict h, isQuantumChannel_restrict h⟩

/-! ### Basic algebraic identities for `restrict` -/

/-- `restrict h 1 = card • 1`: restricting the identity matrix scales by the cardinality
    of the traced-out region. AQFT analogue of `partialTraceRight 1 = card • 1`. -/
lemma restrict_one {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    restrict h (1 : L.localAlgebra Λ_total) =
      (Fintype.card (L.regionIdx (Λ_total \ Λ)) : ℂ) • (1 : L.localAlgebra Λ) := by
  ext a a'
  simp only [restrict_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hab : a = a'
  · subst hab
    simp [Finset.card_univ, Finset.sum_const]
  · rw [if_neg hab, mul_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro hcontra
    exact hab ((Prod.mk.injEq _ _ _ _).mp ((L.combineIdx h).injective hcontra) |>.1)

/-- `restrict h (c • M) = c • restrict h M` (linearity over `ℂ`). -/
lemma restrict_smul {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) (c : ℂ)
    (M : L.localAlgebra Λ_total) :
    restrict h (c • M) = c • restrict h M :=
  (Matrix.restrict h).map_smul c M

/-- `restrict h` distributes over addition. -/
private lemma restrict_add {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (M N : L.localAlgebra Λ_total) :
    restrict h (M + N) = restrict h M + restrict h N :=
  (Matrix.restrict h).map_add M N

/-! ### Iterated restriction (transitivity of marginalisation)

Restricting first to an intermediate region and then to a sub-sub-region equals
restricting directly: `restrict h₂ (restrict h₁ M) = restrict (h₂.trans h₁) M`. -/

/-- For `Λ' ⊆ Λ ⊆ Λ_total`, the index combiner factors through the intermediate
    region: starting from `(a', γ', β'') ∈ regionIdx Λ' × regionIdx (Λ \ Λ') ×
    regionIdx (Λ_total \ Λ)`, combining `(a', γ')` to give `regionIdx Λ` and then
    pairing with `β''` agrees with combining `(a', γ' & β'')` directly to give
    `regionIdx Λ_total`. This is the key identity behind `restrict_restrict`. -/
lemma combineIdx_assoc_aux
    {Λ' Λ Λ_total : Finset L.sites} (h₁ : Λ ⊆ Λ_total) (h₂ : Λ' ⊆ Λ)
    (a' : L.regionIdx Λ') (γ : L.regionIdx (Λ \ Λ'))
    (β : L.regionIdx (Λ_total \ Λ))
    (s : ↥Λ_total) :
    L.combineIdx h₁ (L.combineIdx h₂ (a', γ), β) s =
      if hsΛ : s.val ∈ Λ then
        if hsΛ' : s.val ∈ Λ' then a' ⟨s.val, hsΛ'⟩
        else γ ⟨s.val, Finset.mem_sdiff.mpr ⟨hsΛ, hsΛ'⟩⟩
      else β ⟨s.val, Finset.mem_sdiff.mpr ⟨s.property, hsΛ⟩⟩ := by
  by_cases hsΛ : s.val ∈ Λ
  · rw [LocalNet.combineIdx_apply_mem h₁ _ _ s hsΛ, dif_pos hsΛ]
    by_cases hsΛ' : s.val ∈ Λ'
    · rw [LocalNet.combineIdx_apply_mem h₂ _ _ ⟨s.val, hsΛ⟩ hsΛ', dif_pos hsΛ']
    · rw [LocalNet.combineIdx_apply_not_mem h₂ _ _ ⟨s.val, hsΛ⟩ hsΛ', dif_neg hsΛ']
  · rw [LocalNet.combineIdx_apply_not_mem h₁ _ _ s hsΛ, dif_neg hsΛ]

/-- Splitting a `regionIdx (Λ_total \ Λ')` into its `(Λ \ Λ')` and `(Λ_total \ Λ)` parts.
    Used by `restrict_restrict` to convert iterated marginalisation into a single one,
    and by callers (e.g. SSA) that need to commute `combineIdx h₁ ∘ combineIdx h₂` with
    `combineIdx (h₂.trans h₁)` (see `combineIdx_assoc_eq`). -/
def restrictAssocEquiv {Λ' Λ Λ_total : Finset L.sites}
    (h₁ : Λ ⊆ Λ_total) (h₂ : Λ' ⊆ Λ) :
    L.regionIdx (Λ \ Λ') × L.regionIdx (Λ_total \ Λ) ≃ L.regionIdx (Λ_total \ Λ') where
  toFun gb := fun ⟨s, hs⟩ =>
    if hsΛ : s ∈ Λ then
      gb.1 ⟨s, Finset.mem_sdiff.mpr ⟨hsΛ, (Finset.mem_sdiff.mp hs).2⟩⟩
    else
      gb.2 ⟨s, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hs).1, hsΛ⟩⟩
  invFun δ :=
    (fun ⟨s, hs⟩ => δ ⟨s, Finset.mem_sdiff.mpr
        ⟨h₁ (Finset.mem_sdiff.mp hs).1, (Finset.mem_sdiff.mp hs).2⟩⟩,
     fun ⟨s, hs⟩ => δ ⟨s, Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hs).1, fun h_in_Λ' =>
          (Finset.mem_sdiff.mp hs).2 (h₂ h_in_Λ')⟩⟩)
  left_inv := by
    rintro ⟨γ, β⟩
    ext1
    · funext ⟨s, hs⟩
      have h_in_Λ : s ∈ Λ := (Finset.mem_sdiff.mp hs).1
      simp [h_in_Λ]
    · funext ⟨s, hs⟩
      have h_not_Λ : s ∉ Λ := (Finset.mem_sdiff.mp hs).2
      simp [h_not_Λ]
  right_inv := by
    intro δ
    funext ⟨s, hs⟩
    by_cases h_in_Λ : s ∈ Λ <;> simp [h_in_Λ]

/-- **`combineIdx` associativity**: For nested subsets `Λ' ⊆ Λ ⊆ Λ_total`, combining
    `(combineIdx h₂ (a', γ), β)` via the outer subset agrees with combining
    `(a', restrictAssocEquiv (γ, β))` via the composed subset `h₂.trans h₁`.
    AQFT analogue of the tensor-product associativity
    `(ℋ_Λ' ⊗ ℋ_{Λ\Λ'}) ⊗ ℋ_{Λ_total\Λ} ≃ ℋ_Λ' ⊗ (ℋ_{Λ\Λ'} ⊗ ℋ_{Λ_total\Λ})`. -/
lemma combineIdx_assoc_eq {Λ' Λ Λ_total : Finset L.sites}
    (h₁ : Λ ⊆ Λ_total) (h₂ : Λ' ⊆ Λ) (a' : L.regionIdx Λ')
    (γ : L.regionIdx (Λ \ Λ')) (β : L.regionIdx (Λ_total \ Λ)) :
    L.combineIdx h₁ (L.combineIdx h₂ (a', γ), β) =
      L.combineIdx (h₂.trans h₁) (a', restrictAssocEquiv h₁ h₂ (γ, β)) := by
  funext s
  rw [combineIdx_assoc_aux h₁ h₂]
  by_cases hsΛ' : s.val ∈ Λ'
  · have hsΛ : s.val ∈ Λ := h₂ hsΛ'
    rw [LocalNet.combineIdx_apply_mem (h₂.trans h₁) _ _ s hsΛ',
        dif_pos hsΛ, dif_pos hsΛ']
  · rw [LocalNet.combineIdx_apply_not_mem (h₂.trans h₁) _ _ s hsΛ']
    by_cases hsΛ : s.val ∈ Λ
    · rw [dif_pos hsΛ, dif_neg hsΛ']
      simp [restrictAssocEquiv, hsΛ]
    · rw [dif_neg hsΛ]
      simp [restrictAssocEquiv, hsΛ]

/-- **Iterated restriction equals direct restriction**:
    `restrict h₂ (restrict h₁ M) = restrict (h₂.trans h₁) M`.

    Marginalising first to `Λ` then to `Λ' ⊆ Λ` agrees with marginalising directly to `Λ'`.
    AQFT statement of the partial-trace transitivity property. -/
theorem restrict_restrict {Λ' Λ Λ_total : Finset L.sites}
    (h₁ : Λ ⊆ Λ_total) (h₂ : Λ' ⊆ Λ) (M : L.localAlgebra Λ_total) :
    restrict h₂ (restrict h₁ M) = restrict (h₂.trans h₁) M := by
  ext a' a''
  rw [restrict_apply]
  -- Reindex RHS sum via restrictAssocEquiv to a sum over the product type.
  rw [show restrict (h₂.trans h₁) M a' a'' =
        ∑ p : L.regionIdx (Λ \ Λ') × L.regionIdx (Λ_total \ Λ),
          M (L.combineIdx (h₂.trans h₁) (a', restrictAssocEquiv h₁ h₂ p))
            (L.combineIdx (h₂.trans h₁) (a'', restrictAssocEquiv h₁ h₂ p)) from by
    rw [restrict_apply]
    exact ((restrictAssocEquiv h₁ h₂).sum_comp _).symm]
  -- Convert the product sum to nested sums.
  rw [Fintype.sum_prod_type]
  -- Pointwise: rewrite the inner sums via combineIdx_assoc_eq.
  refine Finset.sum_congr rfl fun γ _ => ?_
  refine Finset.sum_congr rfl fun β _ => ?_
  congr 1
  · exact combineIdx_assoc_eq h₁ h₂ a' γ β
  · exact combineIdx_assoc_eq h₁ h₂ a'' γ β

/-! ### Heisenberg-picture duality

The matrix-level dual of the restriction: tracing `ρ` against an embedded observable
`includeAlgebra h X` equals tracing the marginal `restrict h ρ` against `X`. -/

/-- Entry-wise behaviour of `includeAlgebra` at combined indices: the off-diagonal
    components in the complementary region vanish, leaving `X a a'` on the diagonal. -/
@[simp] private lemma includeAlgebra_apply_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) (X : L.localAlgebra Λ)
    (a a' : L.regionIdx Λ) (b b' : L.regionIdx (Λ_total \ Λ)) :
    L.includeAlgebra h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b')) =
      if b = b' then X a a' else 0 := by
  simp [LocalNet.includeAlgebra_apply, Equiv.symm_apply_apply]

/-- **Heisenberg-picture trace identity**:
`Tr(ρ · includeAlgebra h X) = Tr((restrict h ρ) · X)`.
This is the AQFT-natural form of `trace_mul_kronecker_one`. -/
theorem trace_mul_includeAlgebra {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (ρ : L.localAlgebra Λ_total) (X : L.localAlgebra Λ) :
    Tr (ρ * L.includeAlgebra h X) = Tr ((restrict h ρ) * X) := by
  -- RHS expansion: ∑ a, ∑ a', ∑ b, ρ(combine (a,b), combine (a',b)) · X a' a
  have rhs_expand :
      Tr ((restrict h ρ) * X) =
        ∑ a : L.regionIdx Λ, ∑ a' : L.regionIdx Λ, ∑ b : L.regionIdx (Λ_total \ Λ),
          ρ (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) * X a' a := by
    unfold Matrix.trace
    simp_rw [Matrix.diag_apply, Matrix.mul_apply, restrict_apply, Finset.sum_mul]
  -- LHS: reindex outer sum via combineIdx, expand mul
  have lhs_expand :
      Tr (ρ * L.includeAlgebra h X) =
        ∑ a : L.regionIdx Λ, ∑ b : L.regionIdx (Λ_total \ Λ),
          ∑ a' : L.regionIdx Λ,
          ρ (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) * X a' a := by
    unfold Matrix.trace
    -- Reindex Tr over Λ_total via combineIdx⁻¹: ∑ s, M s s = ∑ (a,b), M (combine (a,b)) (combine (a,b))
    rw [show (∑ s : L.regionIdx Λ_total, (ρ * L.includeAlgebra h X).diag s) =
        ∑ p : L.regionIdx Λ × L.regionIdx (Λ_total \ Λ),
          (ρ * L.includeAlgebra h X).diag (L.combineIdx h p) from
      ((L.combineIdx h).sum_comp _).symm]
    rw [Fintype.sum_prod_type]
    -- Goal: ∑ a, ∑ b, (ρ * includeAlgebra h X).diag (combineIdx (a, b)) = ...
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    -- Expand mul, then reindex inner sum (over s' : regionIdx Λ_total) via combineIdx
    rw [Matrix.diag_apply, Matrix.mul_apply,
        show (∑ s' : L.regionIdx Λ_total,
              ρ (L.combineIdx h (a, b)) s' *
              L.includeAlgebra h X s' (L.combineIdx h (a, b))) =
          ∑ p : L.regionIdx Λ × L.regionIdx (Λ_total \ Λ),
            ρ (L.combineIdx h (a, b)) (L.combineIdx h p) *
            L.includeAlgebra h X (L.combineIdx h p) (L.combineIdx h (a, b)) from
      ((L.combineIdx h).sum_comp _).symm]
    rw [Fintype.sum_prod_type]
    -- Now: ∑ a', ∑ b', ρ ... * (includeAlgebra h X) (combineIdx (a', b')) (combineIdx (a, b))
    -- After applying `includeAlgebra_apply_combineIdx`, the b'-sum collapses on b' = b.
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [show (∑ b' : L.regionIdx (Λ_total \ Λ),
              ρ (L.combineIdx h (a, b)) (L.combineIdx h (a', b')) *
              L.includeAlgebra h X (L.combineIdx h (a', b')) (L.combineIdx h (a, b))) =
        ρ (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) * X a' a from by
      rw [Finset.sum_eq_single b]
      · rw [includeAlgebra_apply_combineIdx]; simp
      · intro b' _ hb'
        rw [includeAlgebra_apply_combineIdx, if_neg hb']
        ring
      · simp]
  -- Combine: LHS = ∑ a, ∑ b, ∑ a', ... = ∑ a, ∑ a', ∑ b, ... = RHS
  rw [lhs_expand, rhs_expand]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

end Matrix

namespace DensityMatrix

variable {L : LocalNet}

/-- Restriction of a density matrix to a sub-region (= partial trace over the complement). -/
noncomputable def restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (ρ : L.densityMatrix Λ_total) : L.densityMatrix Λ :=
  (Matrix.QuantumChannel.restrict h : Matrix.QuantumChannel _ _) ρ

@[simp] lemma restrict_toMatrix {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (ρ : L.densityMatrix Λ_total) :
    (restrict h ρ).toMatrix = Matrix.restrict h ρ.toMatrix := rfl

/-- **Iterated restriction equals direct restriction** (density-matrix form).
    Marginalising first to `Λ` then to `Λ' ⊆ Λ` agrees with marginalising directly to `Λ'`. -/
theorem restrict_restrict {Λ' Λ Λ_total : Finset L.sites}
    (h₁ : Λ ⊆ Λ_total) (h₂ : Λ' ⊆ Λ) (ρ : L.densityMatrix Λ_total) :
    restrict h₂ (restrict h₁ ρ) = restrict (h₂.trans h₁) ρ := by
  apply DensityMatrix.ext
  rw [restrict_toMatrix, restrict_toMatrix, restrict_toMatrix,
      Matrix.restrict_restrict]

end DensityMatrix

/-! ## Paper notation: `ρ ↾ Λ`

`ρ ↾ Λ` is the **restriction of a density matrix to a sub-region** — equivalently, the
partial trace over the complementary region. This is the AQFT-natural
form of partial trace: parameterised by the region `Λ` rather than by left/right position.

The subset proof is auto-resolved by trying, in order: `Finset.subset_univ _`
(marginalising from the full system), `Finset.Subset.refl _` (identity), then `decide`
(explicit closed finsets). For complex hypotheses, write `DensityMatrix.restrict h ρ` directly.

For raw `Matrix`-level work, use `Matrix.restrict h M` (no notation provided to keep `↾`
unambiguous on the density-matrix surface). -/

namespace LocalNet
namespace QuantumInfo

scoped syntax:65 term:65 " ↾ " term:66 : term
scoped syntax:65 term:65 " ↾[" term "]" : term

scoped macro_rules
  | `($ρ ↾ $Λ) =>
    `(DensityMatrix.restrict (Λ := $Λ)
        (by first | exact Finset.subset_univ _ | exact Finset.Subset.refl _
                  | decide
                  | assumption) $ρ)
  | `($ρ ↾[$h]) => `(DensityMatrix.restrict $h $ρ)

end QuantumInfo
end LocalNet
