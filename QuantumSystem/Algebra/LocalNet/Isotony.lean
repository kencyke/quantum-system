module

public import QuantumSystem.Algebra.LocalNet.Basic

/-!
# Isotony embedding of the local net

The **isotony** axiom of an AQFT net: for `Λ ⊆ Λ_total` there is a unital `*`-algebra inclusion
`𝔄(Λ) ↪ 𝔄(Λ_total)`, realised concretely as the tensor with identity on the complement
`A ↦ A ⊗ I_{Λ_total \ Λ}` (Naaijkens 2012 §1.3, Verch 2025 §1.2 axiom (i), Bratteli–Robinson
Vol.2 §6.2). This file builds the embedding `includeAlgebra` (as a `StarAlgHom`), proves it is
injective, and establishes its **functoriality** (`includeAlgebra_trans` / `includeAlgebra_refl`),
which makes the net a directed system of `*`-algebras.

Pipeline: entry-wise underlying function `includeAlgebraFun` → algebraic identities
`includeAlgebraFun_{one,mul,star,...}` → bundled `includeAlgebra : _ →⋆ₐ[ℂ] _`.
-/

@[expose] public section

namespace LocalNet

variable (L : LocalNet)

/-! ### Isotony embedding (algebra inclusion) -/

/-- Entry-wise underlying function for `includeAlgebra`, defined separately so the
    structural simp lemmas (`includeAlgebraFun_apply`, `..._apply_combineIdx`) reduce
    by `rfl`/`simp` without going through the `StarAlgHom` coercion. -/
noncomputable def includeAlgebraFun {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) : L.localAlgebra Λ_total :=
  Matrix.of fun s s' =>
    if ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2 then
      X ((L.combineIdx h).symm s).1 ((L.combineIdx h).symm s').1
    else 0

@[simp] lemma includeAlgebraFun_apply {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) (X : L.localAlgebra Λ) (s s' : L.regionIdx Λ_total) :
    L.includeAlgebraFun h X s s' =
      if ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2 then
        X ((L.combineIdx h).symm s).1 ((L.combineIdx h).symm s').1
      else 0 := rfl

/-- Entry-wise behaviour of `includeAlgebraFun` at combined indices: the off-diagonal
    components in the complementary region vanish, leaving `X a a'` on the diagonal. -/
@[simp] lemma includeAlgebraFun_apply_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) (X : L.localAlgebra Λ)
    (a a' : L.regionIdx Λ) (b b' : L.regionIdx (Λ_total \ Λ)) :
    L.includeAlgebraFun h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b')) =
      if b = b' then X a a' else 0 := by
  simp [includeAlgebraFun, Equiv.symm_apply_apply]

lemma includeAlgebraFun_zero {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.includeAlgebraFun h 0 = 0 := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.zero_apply]
  split_ifs <;> rfl

lemma includeAlgebraFun_add {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X Y : L.localAlgebra Λ) :
    L.includeAlgebraFun h (X + Y) =
      L.includeAlgebraFun h X + L.includeAlgebraFun h Y := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.add_apply]
  split_ifs with hbb
  · rfl
  · rw [add_zero]

lemma includeAlgebraFun_smul {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (c : ℂ) (X : L.localAlgebra Λ) :
    L.includeAlgebraFun h (c • X) = c • L.includeAlgebraFun h X := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with hbb
  · rfl
  · rw [mul_zero]

lemma includeAlgebraFun_one {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.includeAlgebraFun h 1 = 1 := by
  ext s s'
  by_cases hss : s = s'
  · subst hss
    rw [includeAlgebraFun_apply, if_pos rfl, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [includeAlgebraFun_apply, Matrix.one_apply_ne hss]
    -- Translate `s ≠ s'` to a disjunction on the two coordinates of `(combineIdx h).symm`.
    have hne : (L.combineIdx h).symm s ≠ (L.combineIdx h).symm s' := fun heq =>
      hss ((L.combineIdx h).symm.injective heq)
    rw [Ne, Prod.ext_iff, not_and_or] at hne
    by_cases h2 : ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2
    · rw [if_pos h2]
      rcases hne with h1 | h2'
      · rw [Matrix.one_apply_ne h1]
      · exact absurd h2 h2'
    · rw [if_neg h2]

lemma includeAlgebraFun_star {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) :
    L.includeAlgebraFun h (star X) = star (L.includeAlgebraFun h X) := by
  ext s s'
  simp only [includeAlgebraFun_apply, Matrix.star_apply]
  by_cases h2 : ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2
  · rw [if_pos h2, if_pos h2.symm]
  · rw [if_neg h2, if_neg (fun hh => h2 hh.symm), star_zero]

lemma includeAlgebraFun_mul {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X Y : L.localAlgebra Λ) :
    L.includeAlgebraFun h (X * Y) =
      L.includeAlgebraFun h X * L.includeAlgebraFun h Y := by
  ext s s'
  -- Express both rows/columns through `combineIdx` so the `_apply_combineIdx` simp lemma fires.
  set sa := ((L.combineIdx h).symm s).1 with hsa
  set sb := ((L.combineIdx h).symm s).2 with hsb
  set s'a := ((L.combineIdx h).symm s').1 with hs'a
  set s'b := ((L.combineIdx h).symm s').2 with hs'b
  have hs : s = L.combineIdx h (sa, sb) := by
    simp [sa, sb, Equiv.apply_symm_apply]
  have hs' : s' = L.combineIdx h (s'a, s'b) := by
    simp [s'a, s'b, Equiv.apply_symm_apply]
  rw [hs, hs', includeAlgebraFun_apply_combineIdx, Matrix.mul_apply]
  -- Reindex the RHS sum (over `regionIdx Λ_total`) via `combineIdx`.
  rw [show ((L.includeAlgebraFun h X * L.includeAlgebraFun h Y)
              (L.combineIdx h (sa, sb)) (L.combineIdx h (s'a, s'b))) =
      ∑ p : L.regionIdx Λ × L.regionIdx (Λ_total \ Λ),
        L.includeAlgebraFun h X (L.combineIdx h (sa, sb)) (L.combineIdx h p) *
          L.includeAlgebraFun h Y (L.combineIdx h p) (L.combineIdx h (s'a, s'b)) from by
    rw [Matrix.mul_apply]
    exact ((L.combineIdx h).sum_comp _).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [includeAlgebraFun_apply_combineIdx]
  -- Goal:
  -- (if sb = s'b then ∑ a'', X sa a'' * Y a'' s'a else 0)
  --   = ∑ a'', ∑ b'', (if sb = b'' then X sa a'' else 0) * (if b'' = s'b then Y a'' s'a else 0)
  by_cases hbb : sb = s'b
  · rw [if_pos hbb]
    refine Finset.sum_congr rfl fun a'' _ => ?_
    rw [Finset.sum_eq_single sb
      (fun b'' _ hb'' => by rw [if_neg fun heq => hb'' heq.symm, zero_mul])
      (fun h_not_mem => absurd (Finset.mem_univ sb) h_not_mem)]
    rw [if_pos rfl, ← hbb, if_pos rfl]
  · rw [if_neg hbb]
    refine (Finset.sum_eq_zero fun a'' _ => ?_).symm
    refine Finset.sum_eq_zero fun b'' _ => ?_
    by_cases hb_sb : sb = b''
    · subst hb_sb
      rw [if_neg hbb, mul_zero]
    · rw [if_neg hb_sb, zero_mul]

lemma includeAlgebraFun_algebraMap {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) (c : ℂ) :
    L.includeAlgebraFun h ((algebraMap ℂ (L.localAlgebra Λ)) c) =
      (algebraMap ℂ (L.localAlgebra Λ_total)) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      includeAlgebraFun_smul, includeAlgebraFun_one]

/-- **Isotony embedding** `𝔄(Λ) ↪ 𝔄(Λ_total)`: tensor a local matrix with the identity on
    the complementary region. Realises the inclusion `A ↦ A ⊗ I_{Λ_total \ Λ}` from
    Naaijkens 2012 §1.3 line 211, Verch 2025 §1.2 axiom (i), Bratteli–Robinson Vol.2 §6.2.
    That this embedding is literally `A ↦ A ⊗ 1` of operators on Hilbert spaces is proved in
    `LocalNet.opEquiv_includeAlgebra` (`TensorDecomposition`); the dual marginal is the partial
    trace `LocalNet.opEquiv_restrict` (`PartialTraceOperator`).
    Bundled as a unital `*`-algebra homomorphism so that `map_one`, `map_mul`, `map_star`
    are available via the `StarAlgHom` API. Entry-wise:
    `(includeAlgebra h X) s s' = X (combineIdx⁻¹ s).1 (combineIdx⁻¹ s').1` when the
    complementary indices match, else `0`. -/
noncomputable def includeAlgebra {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.localAlgebra Λ →⋆ₐ[ℂ] L.localAlgebra Λ_total where
  toFun := L.includeAlgebraFun h
  map_zero' := L.includeAlgebraFun_zero h
  map_add' := L.includeAlgebraFun_add h
  map_one' := L.includeAlgebraFun_one h
  map_mul' := L.includeAlgebraFun_mul h
  commutes' := L.includeAlgebraFun_algebraMap h
  map_star' := L.includeAlgebraFun_star h

/-- Entry-wise unfolding of `includeAlgebra h X`: at indices `(s, s')` of the larger
    region, the embedded matrix equals `X` on the diagonal (in the complementary index)
    and zero off-diagonal. -/
@[simp] lemma includeAlgebra_apply {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) (s s' : L.regionIdx Λ_total) :
    L.includeAlgebra h X s s' =
      if ((L.combineIdx h).symm s).2 = ((L.combineIdx h).symm s').2 then
        X ((L.combineIdx h).symm s).1 ((L.combineIdx h).symm s').1
      else 0 := rfl

/-- Combined-index unfolding of the bundled `includeAlgebra` (the `StarAlgHom` coercion is
    definitionally `includeAlgebraFun`, so this is `includeAlgebraFun_apply_combineIdx`). -/
@[simp] lemma includeAlgebra_apply_combineIdx {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) (a a' : L.regionIdx Λ) (b b' : L.regionIdx (Λ_total \ Λ)) :
    L.includeAlgebra h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b')) =
      if b = b' then X a a' else 0 :=
  L.includeAlgebraFun_apply_combineIdx h X a a' b b'

/-- **Injectivity of the isotony embedding** (the `↪` of `𝔄(Λ) ↪ 𝔄(Λ_total)`): under
    the standing AQFT non-degeneracy assumption that the complementary region has a
    non-empty index type, `includeAlgebra h` is injective as a map of `*`-algebras. -/
theorem includeAlgebra_injective {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    [hne : Nonempty (L.regionIdx (Λ_total \ Λ))] :
    Function.Injective (L.includeAlgebra h) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  ext a a'
  obtain ⟨b⟩ := hne
  have heq : L.includeAlgebra h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) =
      0 := by rw [hX]; rfl
  have key : L.includeAlgebra h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) =
      X a a' := by
    change L.includeAlgebraFun h X (L.combineIdx h (a, b)) (L.combineIdx h (a', b)) = X a a'
    rw [includeAlgebraFun_apply_combineIdx, if_pos rfl]
  rw [key] at heq
  simpa using heq

/-! ### Functoriality (composition of the isotony net)

The isotony embeddings compose: including `Λ₁ ↪ Λ₂ ↪ Λ₃` equals the direct inclusion
`Λ₁ ↪ Λ₃`. This upgrades `includeAlgebra` from a family of embeddings to a genuine functor
on the region poset — a directed system of `*`-algebras — matching the net structure of
Naaijkens 2012 §3.2 and Verch 2025 §1.2. -/

/-- The `Λ₁`-coordinate of a `Λ₃`-index is unchanged by routing through an intermediate
    region `Λ₂`: restricting to `Λ₂` then to `Λ₁` equals restricting directly to `Λ₁`.
    Holds definitionally by proof irrelevance of the `⊆` witnesses. -/
private lemma combineIdx_symm_fst_trans {Λ₁ Λ₂ Λ₃ : Finset L.sites}
    (h₁₂ : Λ₁ ⊆ Λ₂) (h₂₃ : Λ₂ ⊆ Λ₃) (s : L.regionIdx Λ₃) :
    ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm s).1).1
      = ((L.combineIdx (Finset.Subset.trans h₁₂ h₂₃)).symm s).1 := rfl

/-- The complementary index of a `Λ₃`-index over `Λ₁` matches between `s` and `s'` iff it
    matches both over `Λ₂` (the outer complement) and over `Λ₁` inside `Λ₂` (the inner
    complement). This is the factorisation `Λ₃ \ Λ₁ = (Λ₃ \ Λ₂) ⊔ (Λ₂ \ Λ₁)` at the level
    of region indices, and is the bookkeeping core of functoriality. -/
private lemma combineIdx_symm_snd_trans_iff {Λ₁ Λ₂ Λ₃ : Finset L.sites}
    (h₁₂ : Λ₁ ⊆ Λ₂) (h₂₃ : Λ₂ ⊆ Λ₃) (s s' : L.regionIdx Λ₃) :
    (((L.combineIdx (Finset.Subset.trans h₁₂ h₂₃)).symm s).2
        = ((L.combineIdx (Finset.Subset.trans h₁₂ h₂₃)).symm s').2)
      ↔ (((L.combineIdx h₂₃).symm s).2 = ((L.combineIdx h₂₃).symm s').2
          ∧ ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm s).1).2
              = ((L.combineIdx h₁₂).symm ((L.combineIdx h₂₃).symm s').1).2) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext t
      exact congrFun h ⟨t.val, Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp t.property).1,
         fun hh => (Finset.mem_sdiff.mp t.property).2 (h₁₂ hh)⟩⟩
    · funext t
      exact congrFun h ⟨t.val, Finset.mem_sdiff.mpr
        ⟨h₂₃ (Finset.mem_sdiff.mp t.property).1, (Finset.mem_sdiff.mp t.property).2⟩⟩
  · rintro ⟨hA, hB⟩
    funext t
    by_cases ht2 : t.val ∈ Λ₂
    · exact congrFun hB ⟨t.val, Finset.mem_sdiff.mpr ⟨ht2, (Finset.mem_sdiff.mp t.property).2⟩⟩
    · exact congrFun hA ⟨t.val, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp t.property).1, ht2⟩⟩

/-- Pointwise form of functoriality: including `X` from `Λ₁` into `Λ₃` directly equals first
    including into `Λ₂`, then into `Λ₃`. -/
theorem includeAlgebra_trans_apply {Λ₁ Λ₂ Λ₃ : Finset L.sites}
    (h₁₂ : Λ₁ ⊆ Λ₂) (h₂₃ : Λ₂ ⊆ Λ₃) (X : L.localAlgebra Λ₁) :
    L.includeAlgebra h₂₃ (L.includeAlgebra h₁₂ X)
      = L.includeAlgebra (Finset.Subset.trans h₁₂ h₂₃) X := by
  ext s s'
  simp only [includeAlgebra_apply]
  rw [combineIdx_symm_fst_trans, combineIdx_symm_fst_trans, ← ite_and]
  simp only [L.combineIdx_symm_snd_trans_iff h₁₂ h₂₃ s s']

/-- **Functoriality of the isotony net**: the inclusions compose. For `Λ₁ ⊆ Λ₂ ⊆ Λ₃`,
    `includeAlgebra` of the composite subset equals the composition of the two embeddings,
    so the net is a directed system of `*`-algebras (Naaijkens 2012 §3.2). -/
theorem includeAlgebra_trans {Λ₁ Λ₂ Λ₃ : Finset L.sites}
    (h₁₂ : Λ₁ ⊆ Λ₂) (h₂₃ : Λ₂ ⊆ Λ₃) :
    (L.includeAlgebra h₂₃).comp (L.includeAlgebra h₁₂)
      = L.includeAlgebra (Finset.Subset.trans h₁₂ h₂₃) :=
  StarAlgHom.ext fun X => by rw [StarAlgHom.comp_apply, includeAlgebra_trans_apply]

/-- The identity inclusion `Λ ⊆ Λ` acts as the identity: `includeAlgebra (subset_refl Λ)`
    is the identity `*`-algebra map. The complementary region `Λ \ Λ` is empty, so the
    diagonal condition is vacuously satisfied. -/
theorem includeAlgebra_refl_apply {Λ : Finset L.sites} (X : L.localAlgebra Λ) :
    L.includeAlgebra (subset_refl Λ) X = X := by
  ext s s'
  have hc : ((L.combineIdx (subset_refl Λ)).symm s).2
      = ((L.combineIdx (subset_refl Λ)).symm s').2 := by
    funext t
    exact absurd (Finset.mem_sdiff.mp t.property).1 (Finset.mem_sdiff.mp t.property).2
  rw [includeAlgebra_apply, if_pos hc]
  rfl

end LocalNet
