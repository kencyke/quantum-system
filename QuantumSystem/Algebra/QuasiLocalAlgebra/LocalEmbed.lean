module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.Algebra.QuasiLocalAlgebra.GlobalHilbert
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Hilbert

/-!
# Local algebra embedding into the concrete lattice representation

For each finite region `Λ : Finset L` and sector tuple
`Ω : (s : L) → localIdx s` we build the canonical injective unital
`*`-algebra homomorphism

`localEmbed Λ : (regionHilbert Λ →L[ℂ] regionHilbert Λ) →⋆ₐ[ℂ]
                  (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)`

(Naaijkens 2012 §1.3 / Bratteli–Robinson Vol. 2 §2.7.2).  Heuristically this
is `M ⊗ 1_{Λᶜ}`: on basis vectors `e_g = lp.single 2 g 1`,

`localEmbed Λ M (e_g) = ∑_{f : regionIdx Λ} M_{f, g|Λ} e_{(f, g|Λᶜ)}`,

where `g|Λ` is the Λ-restriction of `g` and `(f, g|Λᶜ)` replaces its Λ part
with `f`.

`Ω` enters only through `extendRegionTuple` (filling the complement of `Λ`);
the other helpers consume a generic `globalIdx L Ω` tuple `g`.

## Main definitions

* `LocalNetLike.regionRestrict Λ g` — Λ-restriction `g ↦ g|Λ`.
* `LocalNetLike.globalSwap Λ f g` — replaces the Λ part of `g` with `f`.
* `LocalNetLike.extendRegionTuple Λ f` — extends `f` to a global tuple by
  filling outside-`Λ` coordinates with `Ω`.
* `LocalNetLike.localSubalgebra Λ` / `𝔄(Λ)` — represented image of `B(ℋ(Λ))`
  inside `B(globalHilbert L Ω)`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-! ### Region tuple extensions -/

/-- Equality on `globalIdx L Ω` is classically decidable; registered as a
noncomputable instance so that `lp.single 2 (· : globalIdx L Ω) 1` is well-typed. -/
noncomputable instance instDecidableEqGlobalIdx : DecidableEq (globalIdx L Ω) :=
  Classical.decEq _

/-- Extension of a region tuple `f : regionIdx Λ` to a global tuple in
`globalIdx L Ω` by filling sites outside `Λ` with the sector tuple `Ω`. -/
noncomputable def extendRegionTuple (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    globalIdx L Ω :=
  ⟨fun s => if h : s ∈ Λ then f ⟨s, h⟩ else Ω s,
   ⟨Λ, fun _ hs => dif_neg hs⟩⟩

@[simp]
theorem extendRegionTuple_val_apply_of_mem (Λ : Finset L)
    (f : regionIdx (L := L) Λ) {s : L} (hs : s ∈ Λ) :
    (extendRegionTuple (Ω := Ω) Λ f).val s = f ⟨s, hs⟩ :=
  dif_pos hs

@[simp]
theorem extendRegionTuple_val_apply_of_not_mem (Λ : Finset L)
    (f : regionIdx (L := L) Λ) {s : L} (hs : s ∉ Λ) :
    (extendRegionTuple (Ω := Ω) Λ f).val s = Ω s :=
  dif_neg hs

/-- The extension `extendRegionTuple Λ` is injective. -/
theorem extendRegionTuple_injective (Λ : Finset L) :
    Function.Injective (extendRegionTuple (L := L) (Ω := Ω) Λ) := by
  intro f g h
  ext ⟨s, hs⟩
  have hval : (extendRegionTuple (Ω := Ω) Λ f).val
        = (extendRegionTuple (Ω := Ω) Λ g).val :=
    congrArg Subtype.val h
  have := congrFun hval s
  simpa [extendRegionTuple_val_apply_of_mem, hs] using this

/-! ### Global tuple restriction and swaps -/

/-- Restrict a global tuple to a finite region `Λ`.  The result
`regionRestrict Λ g : regionIdx Λ` lists `g`'s coordinates at the sites
of `Λ`. -/
def regionRestrict (Λ : Finset L) (g : globalIdx L Ω) : regionIdx (L := L) Λ :=
  fun s => g.val s.1

@[simp]
theorem regionRestrict_apply (Λ : Finset L) (g : globalIdx L Ω) (s : ↥Λ) :
    regionRestrict Λ g s = g.val s.1 := rfl

/-- Replace the Λ component of a global tuple `g` with a region tuple `f`.
The Λᶜ component is left unchanged.  Outside `Λ ∪ Γ`, where `Γ` is any
finite witness for `g`'s finite-variation property, the result still
agrees with the sector tuple `Ω`. -/
noncomputable def globalSwap (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L Ω) : globalIdx L Ω :=
  ⟨fun s => if h : s ∈ Λ then f ⟨s, h⟩ else g.val s, by
    obtain ⟨Γ, hΓ⟩ := g.property
    refine ⟨Γ ∪ Λ, fun s hs => ?_⟩
    have hsΛ : s ∉ Λ := fun h => hs (Finset.mem_union_right _ h)
    have hsΓ : s ∉ Γ := fun h => hs (Finset.mem_union_left _ h)
    simp only [dif_neg hsΛ]
    exact hΓ s hsΓ⟩

@[simp]
theorem globalSwap_val_apply_of_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L Ω) {s : L} (hs : s ∈ Λ) :
    (globalSwap Λ f g).val s = f ⟨s, hs⟩ :=
  dif_pos hs

@[simp]
theorem globalSwap_val_apply_of_not_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L Ω) {s : L} (hs : s ∉ Λ) :
    (globalSwap Λ f g).val s = g.val s :=
  dif_neg hs

/-- Restricting `globalSwap Λ f g` to `Λ` recovers `f`. -/
@[simp]
theorem regionRestrict_globalSwap (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L Ω) :
    regionRestrict Λ (globalSwap Λ f g) = f := by
  funext ⟨s, hs⟩
  simp [regionRestrict, globalSwap_val_apply_of_mem _ _ _ hs]

/-- Restoring `g` from `(globalSwap Λ f g, regionRestrict Λ g)`: replacing
the Λ part of `globalSwap Λ f g` with `regionRestrict Λ g` gives back `g`. -/
@[simp]
theorem globalSwap_regionRestrict_globalSwap (Λ : Finset L)
    (f : regionIdx (L := L) Λ) (g : globalIdx L Ω) :
    globalSwap Λ (regionRestrict Λ g) (globalSwap Λ f g) = g := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [globalSwap_val_apply_of_mem _ _ _ hs, regionRestrict]
  · simp [globalSwap_val_apply_of_not_mem _ _ _ hs]

/-- The swap-and-restrict involution
`(g, f) ↔ (globalSwap Λ f g, regionRestrict Λ g)` on
`globalIdx L Ω × regionIdx Λ`: the key reindexing for `(M ⊗ 1)`-style sums. -/
theorem globalSwap_pair_involutive (Λ : Finset L) :
    Function.Involutive
      (fun gf : globalIdx L Ω × regionIdx (L := L) Λ =>
        (globalSwap Λ gf.2 gf.1, regionRestrict Λ gf.1)) := by
  rintro ⟨g, f⟩
  simp [globalSwap_regionRestrict_globalSwap]

/-- The swap-and-restrict bijection on `globalIdx L Ω × regionIdx Λ`. -/
noncomputable def globalSwapEquiv (Λ : Finset L) :
    globalIdx L Ω × regionIdx (L := L) Λ
      ≃ globalIdx L Ω × regionIdx (L := L) Λ :=
  (globalSwap_pair_involutive (Ω := Ω) Λ).toPerm

@[simp]
theorem globalSwapEquiv_apply (Λ : Finset L)
    (gf : globalIdx L Ω × regionIdx (L := L) Λ) :
    globalSwapEquiv (Ω := Ω) Λ gf
      = (globalSwap Λ gf.2 gf.1, regionRestrict Λ gf.1) :=
  rfl

/-! ### Pointwise action of `M ⊗ 1` on global tuples -/

/-- The "Λ-restriction of `w` around `g`" is the vector in
`regionHilbert Λ` whose `f`-th component is `w(globalSwap Λ f g)`.
It packages the data along which `M ⊗ 1_{Λᶜ}` acts as `M`. -/
noncomputable def wRestrict (Λ : Finset L) (w : globalHilbert L Ω)
    (g : globalIdx L Ω) : ℋ(Λ) :=
  WithLp.toLp 2 (fun f : regionIdx (L := L) Λ =>
    (w : lp (fun _ : globalIdx L Ω => ℂ) 2) (globalSwap Λ f g))

@[simp]
theorem wRestrict_apply (Λ : Finset L) (w : globalHilbert L Ω)
    (g : globalIdx L Ω) (f : regionIdx (L := L) Λ) :
    wRestrict Λ w g f =
      (w : lp (fun _ : globalIdx L Ω => ℂ) 2) (globalSwap Λ f g) := rfl

/-- L²-norm of `wRestrict Λ w g`: it is the partial-row sum of `‖w‖²`. -/
theorem norm_sq_wRestrict (Λ : Finset L) (w : globalHilbert L Ω)
    (g : globalIdx L Ω) :
    ‖wRestrict Λ w g‖ ^ 2 = ∑ f : regionIdx (L := L) Λ,
      ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) (globalSwap Λ f g)‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

/-- Pointwise coefficient of `(M ⊗ 1_{Λᶜ}) w` at the global tuple `g`:
the value of `M (wRestrict Λ w g)` at the index `regionRestrict Λ g`. -/
noncomputable def localEmbedCoeff (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (w : globalHilbert L Ω) (g : globalIdx L Ω) : ℂ :=
  (M (wRestrict Λ w g)) (regionRestrict Λ g)

/-- Per-tuple bound: `‖localEmbedCoeff Λ M w g‖² ≤ ‖M‖² · ‖wRestrict Λ w g‖²`. -/
theorem norm_sq_localEmbedCoeff_le (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (w : globalHilbert L Ω) (g : globalIdx L Ω) :
    ‖localEmbedCoeff Λ M w g‖ ^ 2 ≤ ‖M‖ ^ 2 * ‖wRestrict Λ w g‖ ^ 2 := by
  set v := M (wRestrict Λ w g) with hv
  have hcomp : ‖v (regionRestrict Λ g)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  have hop : ‖v‖ ≤ ‖M‖ * ‖wRestrict Λ w g‖ := by
    rw [hv]; exact M.le_opNorm _
  have hop_sq : ‖v‖ ^ 2 ≤ ‖M‖ ^ 2 * ‖wRestrict Λ w g‖ ^ 2 := by
    have hsq : ‖v‖ ^ 2 ≤ (‖M‖ * ‖wRestrict Λ w g‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hop 2
    simpa [mul_pow] using hsq
  exact le_trans hcomp hop_sq

/-! ### Summability of `wRestrict`-norms across global tuples -/

/-- Summability of `‖w h‖²` along `globalIdx L Ω` (i.e. `Memℓp.gen_iff` for `p = 2`). -/
private theorem summable_w_norm_sq (w : globalHilbert L Ω) :
    Summable fun h : globalIdx L Ω =>
      ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 := by
  have hmem :
      Memℓp ((w : lp (fun _ : globalIdx L Ω => ℂ) 2) : globalIdx L Ω → ℂ) 2 :=
    lp.memℓp w
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  rw [memℓp_gen_iff htwo] at hmem
  simpa [ENNReal.toReal_ofNat] using hmem

/-- Partial-sum bound: every Finset sum of `‖w h‖²` over `globalIdx L Ω` is at
most `‖w‖²_lp`. -/
private theorem finsetSum_w_norm_sq_le (w : globalHilbert L Ω)
    (s : Finset (globalIdx L Ω)) :
    ∑ h ∈ s, ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2
      ≤ ∑' h : globalIdx L Ω, ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 :=
  (summable_w_norm_sq w).sum_le_tsum s (fun _ _ => sq_nonneg _)

/-- The total partial-sum bound for `‖wRestrict‖² = Σ_f ‖w(globalSwap Λ f g)‖²`. -/
private theorem finsetSum_wRestrict_norm_sq_le (Λ : Finset L) (w : globalHilbert L Ω)
    (u : Finset (globalIdx L Ω)) :
    ∑ g ∈ u, ‖wRestrict Λ w g‖ ^ 2
      ≤ (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
          ∑' h : globalIdx L Ω, ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 := by
  -- Expand wRestrict to a finite f-sum.
  have hexp : ∀ g, ‖wRestrict Λ w g‖ ^ 2 =
      ∑ f : regionIdx (L := L) Λ,
        ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) (globalSwap Λ f g)‖ ^ 2 :=
    norm_sq_wRestrict Λ w
  calc ∑ g ∈ u, ‖wRestrict Λ w g‖ ^ 2
      = ∑ g ∈ u, ∑ f : regionIdx (L := L) Λ,
          ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) (globalSwap Λ f g)‖ ^ 2 := by
        exact Finset.sum_congr rfl fun g _ => hexp g
    _ = ∑ p ∈ u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ)),
          ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) (globalSwap Λ p.2 p.1)‖ ^ 2 := by
        rw [Finset.sum_product]
    _ = ∑ p ∈ (u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv (Ω := Ω) Λ),
          ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) p.1‖ ^ 2 := by
        rw [Finset.sum_image
          (fun a _ b _ hab => (globalSwapEquiv (Ω := Ω) Λ).injective hab)]
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [globalSwapEquiv_apply]
    _ ≤ ∑ p ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv (Ω := Ω) Λ)).image Prod.fst ×ˢ
              (Finset.univ : Finset (regionIdx (L := L) Λ)),
          ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) p.1‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
        intro p hp
        rw [Finset.mem_product]
        refine ⟨?_, Finset.mem_univ _⟩
        rw [Finset.mem_image]
        exact ⟨p, hp, rfl⟩
    _ = ∑ h ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv (Ω := Ω) Λ)).image Prod.fst,
          ∑ _ : regionIdx (L := L) Λ,
            ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 := by
        rw [Finset.sum_product]
    _ = ∑ h ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv (Ω := Ω) Λ)).image Prod.fst,
          (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
            ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [Finset.sum_const, Finset.card_univ]
        simp [mul_comm]
    _ = (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
          ∑ h ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv (Ω := Ω) Λ)).image Prod.fst,
            ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
          ∑' h : globalIdx L Ω, ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact finsetSum_w_norm_sq_le w _
        · exact Nat.cast_nonneg _

/-- Summability of `‖wRestrict Λ w g‖²` along `globalIdx L Ω`. -/
theorem summable_norm_sq_wRestrict (Λ : Finset L) (w : globalHilbert L Ω) :
    Summable fun g : globalIdx L Ω => ‖wRestrict Λ w g‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) (finsetSum_wRestrict_norm_sq_le Λ w)

/-- Summability of `‖localEmbedCoeff Λ M w g‖²`: the entry point for placing
`localEmbedCoeff Λ M w` in `lp 2`. -/
theorem summable_norm_sq_localEmbedCoeff (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (w : globalHilbert L Ω) :
    Summable fun g : globalIdx L Ω => ‖localEmbedCoeff Λ M w g‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_
    ((summable_norm_sq_wRestrict Λ w).mul_left (‖M‖ ^ 2))
  intro g
  exact norm_sq_localEmbedCoeff_le Λ M w g

/-- The `localEmbedCoeff` data lives in `ℓ²(globalIdx L Ω, ℂ)`. -/
theorem localEmbedCoeff_memℓp (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (w : globalHilbert L Ω) :
    Memℓp (localEmbedCoeff (Ω := Ω) Λ M w) 2 := by
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  rw [memℓp_gen_iff htwo]
  simpa [ENNReal.toReal_ofNat] using summable_norm_sq_localEmbedCoeff Λ M w

/-! ### Linearity of `wRestrict` and `localEmbedCoeff` in `w` -/

theorem wRestrict_add (Λ : Finset L) (w w' : globalHilbert L Ω)
    (g : globalIdx L Ω) :
    wRestrict Λ (w + w') g = wRestrict Λ w g + wRestrict Λ w' g := by
  ext f
  simp only [wRestrict_apply]
  exact congrFun (lp.coeFn_add w w') _

theorem wRestrict_smul (Λ : Finset L) (c : ℂ) (w : globalHilbert L Ω)
    (g : globalIdx L Ω) :
    wRestrict Λ (c • w) g = c • wRestrict Λ w g := by
  ext f
  simp only [wRestrict_apply]
  exact congrFun (lp.coeFn_smul c w) _

theorem localEmbedCoeff_add (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (w w' : globalHilbert L Ω) (g : globalIdx L Ω) :
    localEmbedCoeff Λ M (w + w') g
      = localEmbedCoeff Λ M w g + localEmbedCoeff Λ M w' g := by
  unfold localEmbedCoeff
  rw [wRestrict_add, M.map_add]
  rfl

theorem localEmbedCoeff_smul (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (c : ℂ) (w : globalHilbert L Ω) (g : globalIdx L Ω) :
    localEmbedCoeff Λ M (c • w) g = c • localEmbedCoeff Λ M w g := by
  unfold localEmbedCoeff
  rw [wRestrict_smul, M.map_smul]
  rfl

/-! ### `localEmbed Λ M` as a continuous linear map -/

/-- Coarse uniform bound `Σ' g, ‖wRestrict_g‖² ≤ card · ‖w‖²` (in `tsum` form). -/
private theorem tsum_norm_sq_wRestrict_le (Λ : Finset L) (w : globalHilbert L Ω) :
    ∑' g : globalIdx L Ω, ‖wRestrict Λ w g‖ ^ 2
      ≤ (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
          ∑' h : globalIdx L Ω, ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) (finsetSum_wRestrict_norm_sq_le Λ w)

/-- The linear-map underlying `localEmbed Λ M`, before installing the
operator-norm bound. -/
noncomputable def localEmbedLM (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    globalHilbert L Ω →ₗ[ℂ] globalHilbert L Ω where
  toFun w :=
    (⟨localEmbedCoeff (Ω := Ω) Λ M w, localEmbedCoeff_memℓp Λ M w⟩
      : globalHilbert L Ω)
  map_add' w w' := by
    apply Subtype.ext
    funext g
    exact localEmbedCoeff_add Λ M w w' g
  map_smul' c w := by
    apply Subtype.ext
    funext g
    exact localEmbedCoeff_smul Λ M c w g

@[simp]
theorem localEmbedLM_apply (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) (w : globalHilbert L Ω) (g : globalIdx L Ω) :
    ((localEmbedLM (Ω := Ω) Λ M w : globalHilbert L Ω) : globalIdx L Ω → ℂ) g
      = localEmbedCoeff Λ M w g := rfl

/-- `localEmbed Λ M : globalHilbert L Ω →L[ℂ] globalHilbert L Ω` realising
`M ⊗ 1_{Λᶜ}` on the basis-indexed model.

The boundedness constant `√(card (regionIdx Λ)) · ‖M‖` is loose;
tightening it to `‖M‖` requires an orthogonal-decomposition argument
left for a follow-up. -/
noncomputable def localEmbed (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    globalHilbert L Ω →L[ℂ] globalHilbert L Ω :=
  LinearMap.mkContinuous (localEmbedLM (Ω := Ω) Λ M)
    (Real.sqrt (Fintype.card (regionIdx (L := L) Λ)) * ‖M‖)
    (fun w => by
      change ‖(⟨localEmbedCoeff (Ω := Ω) Λ M w,
            localEmbedCoeff_memℓp Λ M w⟩ : globalHilbert L Ω)‖
          ≤ Real.sqrt (Fintype.card (regionIdx (L := L) Λ)) * ‖M‖ * ‖w‖
      have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
        rw [ENNReal.toReal_ofNat]; norm_num
      have h_lhs_sq : ‖(⟨localEmbedCoeff Λ M w, localEmbedCoeff_memℓp Λ M w⟩
            : globalHilbert L Ω)‖ ^ 2
          = ∑' g : globalIdx L Ω, ‖localEmbedCoeff Λ M w g‖ ^ 2 := by
        have := lp.norm_rpow_eq_tsum (E := fun _ : globalIdx L Ω => ℂ) (p := 2) htwo
          ⟨localEmbedCoeff Λ M w, localEmbedCoeff_memℓp Λ M w⟩
        simpa [ENNReal.toReal_ofNat] using this
      have h_w_sq : ‖w‖ ^ 2
          = ∑' h : globalIdx L Ω,
              ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2 := by
        have := lp.norm_rpow_eq_tsum (E := fun _ : globalIdx L Ω => ℂ) (p := 2) htwo w
        simpa [ENNReal.toReal_ofNat] using this
      have h_bound_sq :
          ‖(⟨localEmbedCoeff Λ M w, localEmbedCoeff_memℓp Λ M w⟩
              : globalHilbert L Ω)‖ ^ 2
            ≤ (Fintype.card (regionIdx (L := L) Λ) : ℝ) * (‖M‖ ^ 2 * ‖w‖ ^ 2) := by
        rw [h_lhs_sq]
        calc ∑' g, ‖localEmbedCoeff Λ M w g‖ ^ 2
            ≤ ∑' g, ‖M‖ ^ 2 * ‖wRestrict Λ w g‖ ^ 2 :=
              Summable.tsum_le_tsum (fun g => norm_sq_localEmbedCoeff_le Λ M w g)
                (summable_norm_sq_localEmbedCoeff Λ M w)
                ((summable_norm_sq_wRestrict Λ w).mul_left _)
          _ = ‖M‖ ^ 2 * ∑' g, ‖wRestrict Λ w g‖ ^ 2 :=
              tsum_mul_left
          _ ≤ ‖M‖ ^ 2 *
                ((Fintype.card (regionIdx (L := L) Λ) : ℝ) *
                  ∑' h, ‖(w : lp (fun _ : globalIdx L Ω => ℂ) 2) h‖ ^ 2) := by
              gcongr
              exact tsum_norm_sq_wRestrict_le Λ w
          _ = (Fintype.card (regionIdx (L := L) Λ) : ℝ) * (‖M‖ ^ 2 * ‖w‖ ^ 2) := by
              rw [← h_w_sq]; ring
      have hC_nn : 0 ≤ Real.sqrt (Fintype.card (regionIdx (L := L) Λ)) * ‖M‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      have hCw_nn : 0 ≤ Real.sqrt (Fintype.card (regionIdx (L := L) Λ)) * ‖M‖ * ‖w‖ :=
        mul_nonneg hC_nn (norm_nonneg _)
      have hbound_sq_form :
          (Real.sqrt (Fintype.card (regionIdx (L := L) Λ)) * ‖M‖ * ‖w‖) ^ 2
            = (Fintype.card (regionIdx (L := L) Λ) : ℝ) * (‖M‖ ^ 2 * ‖w‖ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        ring
      have h_lhs_nn : 0 ≤ ‖(⟨localEmbedCoeff Λ M w, localEmbedCoeff_memℓp Λ M w⟩
              : globalHilbert L Ω)‖ := norm_nonneg _
      have h_sq : ‖(⟨localEmbedCoeff Λ M w, localEmbedCoeff_memℓp Λ M w⟩
              : globalHilbert L Ω)‖ ^ 2
          ≤ (Real.sqrt (Fintype.card (regionIdx (L := L) Λ)) * ‖M‖ * ‖w‖) ^ 2 := by
        rw [hbound_sq_form]; exact h_bound_sq
      exact (abs_le_of_sq_le_sq' h_sq hCw_nn).2)

@[simp]
theorem localEmbed_apply_apply (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (w : globalHilbert L Ω) (g : globalIdx L Ω) :
    ((localEmbed Λ M w : globalHilbert L Ω) : globalIdx L Ω → ℂ) g
      = localEmbedCoeff Λ M w g := rfl

/-! ### Algebraic structure of `M ↦ localEmbed Λ M` -/

/-- A second Λ-swap overrides the first:
`globalSwap Λ f' (globalSwap Λ f g) = globalSwap Λ f' g`. -/
theorem globalSwap_globalSwap (Λ : Finset L) (f f' : regionIdx (L := L) Λ)
    (g : globalIdx L Ω) :
    globalSwap Λ f' (globalSwap Λ f g) = globalSwap Λ f' g := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [globalSwap_val_apply_of_mem _ _ _ hs]
  · simp [globalSwap_val_apply_of_not_mem _ _ _ hs]

/-- `wRestrict` is invariant under swapping the global tuple along `Λ`. -/
theorem wRestrict_globalSwap (Λ : Finset L) (w : globalHilbert L Ω)
    (f : regionIdx (L := L) Λ) (g : globalIdx L Ω) :
    wRestrict Λ w (globalSwap Λ f g) = wRestrict Λ w g := by
  ext f'
  simp only [wRestrict_apply, globalSwap_globalSwap]

/-- Composing `localEmbed Λ N` with the `wRestrict` operation realises
applying `N` first to the local data: `wRestrict Λ (localEmbed Λ N w) g = N (wRestrict Λ w g)`. -/
theorem wRestrict_localEmbed (Λ : Finset L)
    (N : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (w : globalHilbert L Ω) (g : globalIdx L Ω) :
    wRestrict Λ (localEmbed Λ N w) g = N (wRestrict Λ w g) := by
  ext f
  simp only [wRestrict_apply, localEmbed_apply_apply, localEmbedCoeff]
  rw [wRestrict_globalSwap, regionRestrict_globalSwap]

/-- Swapping back the Λ-part with the original `g`'s Λ-part recovers `g`. -/
theorem globalSwap_regionRestrict_self (Λ : Finset L) (g : globalIdx L Ω) :
    globalSwap Λ (regionRestrict Λ g) g = g := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [globalSwap_val_apply_of_mem _ _ _ hs, regionRestrict]
  · simp [globalSwap_val_apply_of_not_mem _ _ _ hs]

/-- The component of `wRestrict Λ w g` at `regionRestrict Λ g` equals `w g`. -/
theorem wRestrict_apply_regionRestrict (Λ : Finset L) (w : globalHilbert L Ω)
    (g : globalIdx L Ω) :
    (wRestrict Λ w g : regionIdx (L := L) Λ → ℂ) (regionRestrict Λ g)
      = ((w : lp (fun _ : globalIdx L Ω => ℂ) 2) : globalIdx L Ω → ℂ) g := by
  rw [wRestrict_apply, globalSwap_regionRestrict_self]

/-- `localEmbed Λ` sends the identity to the identity. -/
theorem localEmbed_one (Λ : Finset L) :
    localEmbed (Ω := Ω) Λ (ContinuousLinearMap.id ℂ (ℋ(Λ)))
      = ContinuousLinearMap.id ℂ (globalHilbert L Ω) := by
  ext w g
  rw [localEmbed_apply_apply]
  unfold localEmbedCoeff
  simp only [ContinuousLinearMap.id_apply]
  exact wRestrict_apply_regionRestrict Λ w g

/-- `localEmbed Λ` is multiplicative: `localEmbed Λ (M ∘ N) = localEmbed Λ M ∘ localEmbed Λ N`. -/
theorem localEmbed_mul (Λ : Finset L)
    (M N : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbed (Ω := Ω) Λ (M.comp N)
      = (localEmbed (Ω := Ω) Λ M).comp (localEmbed (Ω := Ω) Λ N) := by
  ext w g
  rw [localEmbed_apply_apply]
  change localEmbedCoeff Λ (M.comp N) w g
    = ((((localEmbed Λ M).comp (localEmbed Λ N)) w : globalHilbert L Ω)
        : globalIdx L Ω → ℂ) g
  rw [ContinuousLinearMap.comp_apply, localEmbed_apply_apply]
  unfold localEmbedCoeff
  rw [wRestrict_localEmbed]
  rfl

/-- `M ↦ localEmbed Λ M` is additive in `M`. -/
theorem localEmbed_add (Λ : Finset L)
    (M N : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbed (Ω := Ω) Λ (M + N)
      = localEmbed (Ω := Ω) Λ M + localEmbed (Ω := Ω) Λ N := by
  ext w g
  rw [localEmbed_apply_apply]
  change localEmbedCoeff Λ (M + N) w g
    = (((localEmbed (Ω := Ω) Λ M + localEmbed (Ω := Ω) Λ N) w
            : globalHilbert L Ω)
        : globalIdx L Ω → ℂ) g
  rw [ContinuousLinearMap.add_apply]
  unfold localEmbedCoeff
  rw [ContinuousLinearMap.add_apply]
  rfl

/-- `M ↦ localEmbed Λ M` is `ℂ`-linear in `M`. -/
theorem localEmbed_smul (Λ : Finset L) (c : ℂ)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbed (Ω := Ω) Λ (c • M) = c • localEmbed Λ M := by
  ext w g
  rw [localEmbed_apply_apply]
  change localEmbedCoeff Λ (c • M) w g
    = (((c • localEmbed Λ M) w : globalHilbert L Ω) : globalIdx L Ω → ℂ) g
  rw [ContinuousLinearMap.smul_apply]
  unfold localEmbedCoeff
  rw [ContinuousLinearMap.smul_apply]
  rfl

/-- `M ↦ localEmbed Λ M` sends zero to zero. -/
theorem localEmbed_zero (Λ : Finset L) :
    localEmbed (Ω := Ω) Λ (0 : ℋ(Λ) →L[ℂ] ℋ(Λ)) = 0 := by
  ext w g
  rw [localEmbed_apply_apply]
  unfold localEmbedCoeff
  rw [ContinuousLinearMap.zero_apply]
  rfl

/-! ### Matrix-element formulas used to characterise `localEmbed Λ` -/

/-- Finite-sum form of `localEmbedCoeff Λ M v g`: it is the inner product of
the `Λ`-restriction of `v` around `g` with the `(regionRestrict Λ g)`-th column
of `M`. -/
theorem localEmbedCoeff_eq_sum (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (v : globalHilbert L Ω) (g : globalIdx L Ω) :
    localEmbedCoeff Λ M v g
      = ∑ f : regionIdx (L := L) Λ,
          ((M (EuclideanSpace.single f (1 : ℂ)) : regionIdx (L := L) Λ → ℂ)
              (regionRestrict Λ g))
            * ((v : lp (fun _ : globalIdx L Ω => ℂ) 2) : globalIdx L Ω → ℂ)
                (globalSwap Λ f g) := by
  unfold localEmbedCoeff
  have hbasis : (wRestrict Λ v g)
      = ∑ f : regionIdx (L := L) Λ,
          ((wRestrict Λ v g : regionIdx (L := L) Λ → ℂ) f)
            • EuclideanSpace.single f (1 : ℂ) := by
    have := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).sum_repr
      (wRestrict Λ v g)
    simpa [EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using this.symm
  rw [hbasis, map_sum]
  simp only [map_smul]
  rw [WithLp.ofLp_sum]
  change (∑ f : regionIdx (L := L) Λ,
        (((wRestrict Λ v g : regionIdx (L := L) Λ → ℂ) f) •
          (M (EuclideanSpace.single f (1 : ℂ))) : ℋ(Λ)).ofLp)
        (regionRestrict Λ g) = _
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, wRestrict_apply, smul_eq_mul, mul_comm]

/-- Finite-sum form of `localEmbedCoeff Λ (star M) v g` via the adjoint
identity `(M.adjoint y)_a = ⟨M e_a, y⟩` on the finite-dimensional region
Hilbert space.  This rewrites the action of `localEmbed Λ (star M)` in
terms of conjugates of `M`'s matrix elements. -/
private theorem localEmbedCoeff_star_eq_sum (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (v : globalHilbert L Ω) (g : globalIdx L Ω) :
    localEmbedCoeff Λ (star M) v g
      = ∑ f : regionIdx (L := L) Λ,
          star ((M (EuclideanSpace.single (regionRestrict Λ g) (1 : ℂ))
              : regionIdx (L := L) Λ → ℂ) f)
            * ((v : lp (fun _ : globalIdx L Ω => ℂ) 2) : globalIdx L Ω → ℂ)
                (globalSwap Λ f g) := by
  unfold localEmbedCoeff
  have hcoord : ((((star M) (wRestrict Λ v g) : ℋ(Λ))
            : regionIdx (L := L) Λ → ℂ) (regionRestrict Λ g))
        = inner ℂ (EuclideanSpace.single (regionRestrict Λ g) (1 : ℂ))
            ((star M) (wRestrict Λ v g)) := by
    rw [EuclideanSpace.inner_single_left]; simp
  rw [hcoord]
  change inner ℂ _ ((ContinuousLinearMap.adjoint M) (wRestrict Λ v g)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [wRestrict_apply, RCLike.inner_apply, starRingEnd_apply, mul_comm]

/-! ### The basis-vector identity for `map_star` -/

/-- The condition "`g` and `h` agree on `Λᶜ`" is symmetric in the swap form. -/
private theorem globalSwap_agreeOn_symm (Λ : Finset L) (g h : globalIdx L Ω) :
    globalSwap Λ (regionRestrict Λ h) g = h
      ↔ globalSwap Λ (regionRestrict Λ g) h = g := by
  constructor <;> (intro h₁; apply Subtype.ext; funext s; by_cases hs : s ∈ Λ)
  · simp [globalSwap_val_apply_of_mem _ _ _ hs, regionRestrict]
  · simp [globalSwap_val_apply_of_not_mem _ _ _ hs]
    have := congrArg (fun (x : globalIdx L Ω) => x.val s) h₁
    simpa [globalSwap_val_apply_of_not_mem _ _ _ hs] using this.symm
  · simp [globalSwap_val_apply_of_mem _ _ _ hs, regionRestrict]
  · simp [globalSwap_val_apply_of_not_mem _ _ _ hs]
    have := congrArg (fun (x : globalIdx L Ω) => x.val s) h₁
    simpa [globalSwap_val_apply_of_not_mem _ _ _ hs] using this.symm

/-- On a basis vector `lp.single 2 h 1`, the matrix-element identity for the
adjoint reads
`localEmbedCoeff Λ (star M) e_h g = star (localEmbedCoeff Λ M e_g h)`. -/
private theorem localEmbedCoeff_star_lpSingle (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (g h : globalIdx L Ω) :
    localEmbedCoeff Λ (star M) (lp.single 2 h (1 : ℂ)) g
      = star (localEmbedCoeff Λ M (lp.single 2 g (1 : ℂ)) h) := by
  rw [localEmbedCoeff_star_eq_sum, localEmbedCoeff_eq_sum]
  -- Substitute lp.single values.
  have hLHS : ∀ f : regionIdx (L := L) Λ,
      ((lp.single 2 h (1 : ℂ) : lp (fun _ : globalIdx L Ω => ℂ) 2)
          : globalIdx L Ω → ℂ) (globalSwap Λ f g)
        = if globalSwap Λ f g = h then 1 else 0 := by
    intro f
    rw [lp.single_apply]
    exact Pi.single_apply _ _ _
  have hRHS : ∀ f : regionIdx (L := L) Λ,
      ((lp.single 2 g (1 : ℂ) : lp (fun _ : globalIdx L Ω => ℂ) 2)
          : globalIdx L Ω → ℂ) (globalSwap Λ f h)
        = if globalSwap Λ f h = g then 1 else 0 := by
    intro f
    rw [lp.single_apply]
    exact Pi.single_apply _ _ _
  simp_rw [hLHS, hRHS]
  by_cases hagree : globalSwap Λ (regionRestrict Λ h) g = h
  · -- Both sums collapse via `Finset.sum_eq_single`.
    have hLHS_collapse :
        ∑ f : regionIdx (L := L) Λ,
            star ((M (EuclideanSpace.single (regionRestrict Λ g) (1 : ℂ))
                : regionIdx (L := L) Λ → ℂ) f)
              * (if globalSwap Λ f g = h then (1 : ℂ) else 0)
          = star ((M (EuclideanSpace.single (regionRestrict Λ g) (1 : ℂ))
                : regionIdx (L := L) Λ → ℂ) (regionRestrict Λ h)) := by
      rw [Finset.sum_eq_single (regionRestrict Λ h)]
      · simp [hagree]
      · intro f _ hne
        have hgs : globalSwap Λ f g ≠ h := by
          intro hgs
          apply hne
          have := congrArg (regionRestrict Λ) hgs
          simpa using this
        simp [hgs]
      · intro hni
        exact absurd (Finset.mem_univ _) hni
    have hagree' : globalSwap Λ (regionRestrict Λ g) h = g :=
      (globalSwap_agreeOn_symm Λ g h).mp hagree
    have hRHS_collapse :
        ∑ f : regionIdx (L := L) Λ,
            ((M (EuclideanSpace.single f (1 : ℂ)) : regionIdx (L := L) Λ → ℂ)
                (regionRestrict Λ h))
              * (if globalSwap Λ f h = g then (1 : ℂ) else 0)
          = ((M (EuclideanSpace.single (regionRestrict Λ g) (1 : ℂ))
                : regionIdx (L := L) Λ → ℂ) (regionRestrict Λ h)) := by
      rw [Finset.sum_eq_single (regionRestrict Λ g)]
      · simp [hagree']
      · intro f _ hne
        have hgs : globalSwap Λ f h ≠ g := by
          intro hgs
          apply hne
          have := congrArg (regionRestrict Λ) hgs
          simpa using this
        simp [hgs]
      · intro hni
        exact absurd (Finset.mem_univ _) hni
    rw [hLHS_collapse, hRHS_collapse]
  · -- Both sums vanish.
    have hagree' : ¬ globalSwap Λ (regionRestrict Λ g) h = g := by
      intro hagree'; exact hagree ((globalSwap_agreeOn_symm Λ g h).mpr hagree')
    have hLHS_zero :
        ∑ f : regionIdx (L := L) Λ,
            star ((M (EuclideanSpace.single (regionRestrict Λ g) (1 : ℂ))
                : regionIdx (L := L) Λ → ℂ) f)
              * (if globalSwap Λ f g = h then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      have hgs : globalSwap Λ f g ≠ h := by
        intro hgs
        apply hagree
        have := congrArg (regionRestrict Λ) hgs
        rw [regionRestrict_globalSwap] at this
        rw [← this]; exact hgs
      simp [hgs]
    have hRHS_zero :
        ∑ f : regionIdx (L := L) Λ,
            ((M (EuclideanSpace.single f (1 : ℂ)) : regionIdx (L := L) Λ → ℂ)
                (regionRestrict Λ h))
              * (if globalSwap Λ f h = g then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      have hgs : globalSwap Λ f h ≠ g := by
        intro hgs
        apply hagree'
        have := congrArg (regionRestrict Λ) hgs
        rw [regionRestrict_globalSwap] at this
        rw [← this]; exact hgs
      simp [hgs]
    rw [hLHS_zero, hRHS_zero]
    simp

/-! ### Star-preservation of `localEmbed` -/

/-- `localEmbed Λ` preserves the involution: `localEmbed Λ (star M) = star (localEmbed Λ M)`. -/
theorem localEmbed_star (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbed (Ω := Ω) Λ (star M) = star (localEmbed Λ M) := by
  let b : HilbertBasis (globalIdx L Ω) ℂ (globalHilbert L Ω) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (globalHilbert L Ω))
  have hb_apply : ∀ h : globalIdx L Ω, b h = lp.single 2 h (1 : ℂ) := fun h => by
    change (LinearIsometryEquiv.refl ℂ (globalHilbert L Ω)).symm
      (lp.single 2 h (1 : ℂ)) = _
    rfl
  -- Reduce to equality on basis vectors.
  apply ContinuousLinearMap.ext_on
    ((Submodule.dense_iff_topologicalClosure_eq_top).mpr b.dense_span)
  intro v hv
  obtain ⟨h, rfl⟩ := hv
  rw [hb_apply]
  apply Subtype.ext
  funext g
  -- Goal: matrix-element identity `(localEmbed Λ (star M))_{g,h} = star (localEmbed Λ M)_{h,g}`.
  have hLHS :
      ((localEmbed Λ (star M) (lp.single 2 h (1 : ℂ)) : globalHilbert L Ω)
            : globalIdx L Ω → ℂ) g
        = localEmbedCoeff Λ (star M) (lp.single 2 h (1 : ℂ)) g :=
    localEmbed_apply_apply Λ (star M) _ g
  have hRHS :
      ((star (localEmbed Λ M) (lp.single 2 h (1 : ℂ)) : globalHilbert L Ω)
            : globalIdx L Ω → ℂ) g
        = star (localEmbedCoeff Λ M (lp.single 2 g (1 : ℂ)) h) := by
    change ((ContinuousLinearMap.adjoint (localEmbed Λ M) (lp.single 2 h (1 : ℂ))
              : globalHilbert L Ω) : globalIdx L Ω → ℂ) g = _
    have hcoord : (((ContinuousLinearMap.adjoint (localEmbed Λ M)
              (lp.single 2 h (1 : ℂ)) : globalHilbert L Ω)
            : globalIdx L Ω → ℂ) g)
        = inner ℂ
            (lp.single 2 g (1 : ℂ) : lp (fun _ : globalIdx L Ω => ℂ) 2)
            ((ContinuousLinearMap.adjoint (localEmbed Λ M))
              (lp.single 2 h (1 : ℂ))) := by
      rw [lp.inner_single_left]
      simp
    rw [hcoord, ContinuousLinearMap.adjoint_inner_right]
    rw [lp.inner_single_right]
    simp
  rw [hLHS, hRHS]
  exact localEmbedCoeff_star_lpSingle Λ M g h

/-! ### The local subalgebra `𝔄(Λ) ↪ B(globalHilbert L Ω)` (StarSubalgebra) -/

/-- `M ↦ localEmbed Λ M` as a unital `*`-algebra homomorphism. -/
noncomputable def localEmbedHom (Λ : Finset L) :
    (ℋ(Λ) →L[ℂ] ℋ(Λ)) →⋆ₐ[ℂ]
    (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) where
  toFun := localEmbed (Ω := Ω) Λ
  map_one' := localEmbed_one Λ
  map_mul' := localEmbed_mul Λ
  map_zero' := localEmbed_zero Λ
  map_add' := localEmbed_add Λ
  commutes' c := by
    change localEmbed Λ (c • ContinuousLinearMap.id ℂ _) = _
    rw [localEmbed_smul, localEmbed_one]
    rfl
  map_star' := localEmbed_star Λ

@[simp]
theorem localEmbedHom_apply (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedHom (Ω := Ω) Λ M = localEmbed Λ M := rfl

@[simp]
theorem regionRestrict_extendRegionTuple (Λ : Finset L)
    (a : regionIdx (L := L) Λ) :
    regionRestrict Λ (extendRegionTuple (Ω := Ω) Λ a) = a := by
  funext s
  simp [regionRestrict]

/-- Swapping the `Λ`-component of an extended region tuple gives the extension of
the swapped-in region tuple. -/
theorem globalSwap_extendRegionTuple (Λ : Finset L)
    (a b : regionIdx (L := L) Λ) :
    globalSwap (Ω := Ω) Λ b (extendRegionTuple Λ a) = extendRegionTuple Λ b := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [globalSwap_val_apply_of_mem, extendRegionTuple_val_apply_of_mem, hs]
  · simp [globalSwap_val_apply_of_not_mem, extendRegionTuple_val_apply_of_not_mem, hs]

@[simp]
theorem wRestrict_lpSingle_extendRegionTuple (Λ : Finset L)
    (a b : regionIdx (L := L) Λ) :
    wRestrict Λ
        (lp.single 2 (extendRegionTuple (Ω := Ω) Λ b) (1 : ℂ) : globalHilbert L Ω)
        (extendRegionTuple Λ a) = EuclideanSpace.single b (1 : ℂ) := by
  ext f
  rw [wRestrict_apply]
  rw [globalSwap_extendRegionTuple]
  by_cases hfb : f = b
  · subst hfb
    simp [lp.single_apply]
  · have hne : extendRegionTuple (Ω := Ω) Λ f ≠ extendRegionTuple Λ b := by
      intro h
      exact hfb ((extendRegionTuple_injective Λ) h)
    simp [lp.single_apply, hne, hfb]

/-- The represented local algebra map is injective: a local operator is uniquely
recovered from its action on the embedded region basis vectors. -/
theorem localEmbedHom_injective (Λ : Finset L) :
    Function.Injective (localEmbedHom (L := L) (Ω := Ω) Λ) := by
  rw [injective_iff_map_eq_zero]
  intro M hM
  have hbasis_zero : ∀ b : regionIdx (L := L) Λ,
      M (EuclideanSpace.single b (1 : ℂ)) = 0 := by
    intro b
    ext a
    have hzero := congrArg
      (fun T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω =>
        ((T (lp.single 2 (extendRegionTuple (Ω := Ω) Λ b) (1 : ℂ) : globalHilbert L Ω)
            : globalHilbert L Ω) : globalIdx L Ω → ℂ) (extendRegionTuple Λ a)) hM
    rw [localEmbedHom_apply] at hzero
    change ((localEmbed Λ M
        (lp.single 2 (extendRegionTuple (Ω := Ω) Λ b) (1 : ℂ) : globalHilbert L Ω)
          : globalHilbert L Ω) : globalIdx L Ω → ℂ) (extendRegionTuple Λ a) = 0 at hzero
    rw [localEmbed_apply_apply] at hzero
    unfold localEmbedCoeff at hzero
    rw [wRestrict_lpSingle_extendRegionTuple, regionRestrict_extendRegionTuple] at hzero
    simpa using hzero
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ b : regionIdx (L := L) Λ,
      (v : regionIdx (L := L) Λ → ℂ) b • EuclideanSpace.single b (1 : ℂ) := by
    have := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).sum_repr v
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  rw [hv, map_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [map_smul, hbasis_zero b]
  simp

/-- The represented local subalgebra at `Λ`: the image of `M ↦ localEmbed Λ M`
as a unital `*`-subalgebra of `globalHilbert L Ω →L[ℂ] globalHilbert L Ω`. -/
noncomputable def localSubalgebra (Λ : Finset L) :
    StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :=
  (localEmbedHom (Ω := Ω) Λ).range

/-- Paper notation `𝔄(Λ)` for the represented local subalgebra at `Λ`,
in the surrounding sector tuple `Ω` (Naaijkens 2012 §1.3).
Scoped to `LocalNetLike`. -/
scoped notation:max "𝔄(" Λ ")" => LocalNetLike.localSubalgebra Λ

theorem mem_localSubalgebra (Λ : Finset L)
    (T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :
    T ∈ localSubalgebra (Ω := Ω) Λ
      ↔ ∃ M : ℋ(Λ) →L[ℂ] ℋ(Λ),
          localEmbed Λ M = T := by
  change T ∈ ((localEmbedHom Λ).toAlgHom.range : Subalgebra ℂ _) ↔ _
  exact AlgHom.mem_range _

/-! ### Bridge between the abstract local algebra and the represented one

Given `HasLocalRepresentation`, the abstract algebra
`LocalNetLike.localAlgebra Λ` admits a `*`-algebra hom into
`B(globalHilbert L Ω)` with range in `localSubalgebra Λ`. -/

variable [HasLocalRepresentation L]

/-- The composite `*`-algebra hom realising the abstract local algebra inside
`B(globalHilbert L Ω)`. -/
noncomputable def localAlgebraEmbed (Λ : Finset L) :
    LocalNetLike.localAlgebra (L := L) Λ →⋆ₐ[ℂ]
      (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :=
  (localEmbedHom (Ω := Ω) Λ).comp (HasLocalRepresentation.localRep Λ)

theorem localAlgebraEmbed_apply (Λ : Finset L)
    (a : LocalNetLike.localAlgebra (L := L) Λ) :
    localAlgebraEmbed (Ω := Ω) Λ a
      = localEmbed Λ (HasLocalRepresentation.localRep Λ a) := rfl

/-- The range of `localAlgebraEmbed` lies inside `localSubalgebra Λ`. -/
theorem localAlgebraEmbed_range_le_localSubalgebra (Λ : Finset L) :
    (localAlgebraEmbed (Ω := Ω) Λ).range ≤ localSubalgebra Λ := by
  intro T hT
  obtain ⟨a, hT⟩ := hT
  refine ⟨HasLocalRepresentation.localRep Λ a, ?_⟩
  simpa [localAlgebraEmbed_apply] using hT

/-- Membership form of `localAlgebraEmbed_range_le_localSubalgebra`. -/
theorem localAlgebraEmbed_mem_localSubalgebra (Λ : Finset L)
    (a : LocalNetLike.localAlgebra (L := L) Λ) :
    localAlgebraEmbed (Ω := Ω) Λ a ∈ localSubalgebra Λ :=
  localAlgebraEmbed_range_le_localSubalgebra Λ ⟨a, rfl⟩

end LocalNetLike
