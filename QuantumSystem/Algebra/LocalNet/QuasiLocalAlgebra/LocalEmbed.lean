module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Embedding

/-!
# Local algebra embedding into `B(globalHilbert L)` (Phase 5'b)

For each finite region `Λ : Finset L` we build the canonical *unital*
`*`-algebra embedding

`localEmbed Λ : (regionHilbert Λ →L[ℂ] regionHilbert Λ) →⋆ₐ[ℂ]
                  (globalHilbert L →L[ℂ] globalHilbert L)`

following Naaijkens 2012 §1.3 and Bratteli–Robinson Vol. 2 §2.7.2: an
operator `M` on the region Hilbert space is sent to `M ⊗ 1_{Λᶜ}`, the
operator on the infinite-site Hilbert space that acts as `M` on the Λ
factor and as the identity on the complement.  In our basis-indexed model
this is realised on basis vectors `e_g = lp.single 2 g 1` by

`localEmbed Λ M (e_g) = ∑_{f : regionIdx Λ} M_{f, g|Λ} e_{(f, g|Λᶜ)}`

where `g|Λ : regionIdx Λ` is the Λ-restriction of the global tuple `g`,
and `(f, g|Λᶜ) : globalIdx L` is the global tuple obtained by replacing
the Λ component of `g` with `f`.

This file installs the structural helpers that make the formula above
well-defined.  The continuous-linear-map upgrade, the `StarAlgHom`
structure, and the resulting `localSubalgebra Λ : StarSubalgebra ℂ _`
are added in subsequent commits.

## Main definitions

* `LocalNetLike.regionRestrict Λ g` — the Λ-restriction
  `g ↦ g|Λ : regionIdx Λ` of a global tuple.
* `LocalNetLike.globalSwap Λ f g` — the global tuple obtained from `g`
  by replacing its Λ component with `f`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- Restrict a global tuple to a finite region `Λ`.  The result
`regionRestrict Λ g : regionIdx Λ` lists `g`'s coordinates at the sites
of `Λ`. -/
def regionRestrict (Λ : Finset L) (g : globalIdx L) : regionIdx (L := L) Λ :=
  fun s => g.val s.1

@[simp]
theorem regionRestrict_apply (Λ : Finset L) (g : globalIdx L) (s : ↥Λ) :
    regionRestrict Λ g s = g.val s.1 := rfl

/-- Replace the Λ component of a global tuple `g` with a region tuple `f`.
The Λᶜ component is left unchanged.  Outside `Λ ∪ Γ`, where `Γ` is any
finite witness for `g`'s finite-variation property, the result still
agrees with the reference basis. -/
noncomputable def globalSwap (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) : globalIdx L :=
  ⟨fun s => if h : s ∈ Λ then f ⟨s, h⟩ else g.val s, by
    obtain ⟨Γ, hΓ⟩ := g.property
    refine ⟨Γ ∪ Λ, fun s hs => ?_⟩
    have hsΛ : s ∉ Λ := fun h => hs (Finset.mem_union_right _ h)
    have hsΓ : s ∉ Γ := fun h => hs (Finset.mem_union_left _ h)
    simp only [dif_neg hsΛ]
    exact hΓ s hsΓ⟩

@[simp]
theorem globalSwap_val_apply_of_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) {s : L} (hs : s ∈ Λ) :
    (globalSwap Λ f g).val s = f ⟨s, hs⟩ :=
  dif_pos hs

@[simp]
theorem globalSwap_val_apply_of_not_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) {s : L} (hs : s ∉ Λ) :
    (globalSwap Λ f g).val s = g.val s :=
  dif_neg hs

/-- Restricting `globalSwap Λ f g` to `Λ` recovers `f`. -/
@[simp]
theorem regionRestrict_globalSwap (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) :
    regionRestrict Λ (globalSwap Λ f g) = f := by
  funext ⟨s, hs⟩
  simp [regionRestrict, globalSwap_val_apply_of_mem _ _ _ hs]

/-- Outside `Λ`, `globalSwap Λ f g` and `g` carry the same coordinates. -/
theorem globalSwap_eq_of_not_mem (Λ : Finset L) (f : regionIdx (L := L) Λ)
    (g : globalIdx L) {s : L} (hs : s ∉ Λ) :
    (globalSwap Λ f g).val s = g.val s :=
  globalSwap_val_apply_of_not_mem Λ f g hs

/-- `globalSwap Λ f g = globalSwap Λ f' g'` exactly when the Λ parts agree
(`f = f'`) and the Λᶜ parts of the underlying global tuples agree. -/
theorem globalSwap_injective_left (Λ : Finset L) (g : globalIdx L) :
    Function.Injective (fun f : regionIdx (L := L) Λ => globalSwap Λ f g) := by
  intro f f' h
  funext ⟨s, hs⟩
  have hval : (globalSwap Λ f g).val = (globalSwap Λ f' g).val :=
    congrArg Subtype.val h
  have := congrFun hval s
  simpa [globalSwap_val_apply_of_mem, hs] using this

/-- The extension `extendRegionTuple Λ f` is exactly `globalSwap Λ f` applied
to the canonical "vacuum" global tuple obtained by extending a region tuple
of the empty region (i.e. the constant `referenceBasis`-tuple). -/
theorem extendRegionTuple_eq_globalSwap_referenceTuple (Λ : Finset L)
    (f : regionIdx (L := L) Λ) :
    extendRegionTuple Λ f =
      globalSwap Λ f ⟨fun s => referenceBasis L s, ⟨∅, fun _ _ => rfl⟩⟩ := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [extendRegionTuple_val_apply_of_mem _ _ hs,
      globalSwap_val_apply_of_mem _ _ _ hs]
  · simp [extendRegionTuple_val_apply_of_not_mem _ _ hs,
      globalSwap_val_apply_of_not_mem _ _ _ hs]

/-- Restoring `g` from `(globalSwap Λ f g, regionRestrict Λ g)`: replacing
the Λ part of `globalSwap Λ f g` with `regionRestrict Λ g` gives back `g`. -/
@[simp]
theorem globalSwap_regionRestrict_globalSwap (Λ : Finset L)
    (f : regionIdx (L := L) Λ) (g : globalIdx L) :
    globalSwap Λ (regionRestrict Λ g) (globalSwap Λ f g) = g := by
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Λ
  · simp [globalSwap_val_apply_of_mem _ _ _ hs, regionRestrict]
  · simp [globalSwap_val_apply_of_not_mem _ _ _ hs]

/-- The involution on `globalIdx L × regionIdx Λ` that records the
"swap-and-restrict" pairing: `(g, f) ↔ (globalSwap Λ f g, regionRestrict Λ g)`.
This bijection is the key reindexing tool used to count contributions of
`(M ⊗ 1)`-style operators across complement classes. -/
theorem globalSwap_pair_involutive (Λ : Finset L) :
    Function.Involutive
      (fun gf : globalIdx L × regionIdx (L := L) Λ =>
        (globalSwap Λ gf.2 gf.1, regionRestrict Λ gf.1)) := by
  rintro ⟨g, f⟩
  simp [globalSwap_regionRestrict_globalSwap]

/-- The swap-and-restrict bijection on `globalIdx L × regionIdx Λ`. -/
noncomputable def globalSwapEquiv (Λ : Finset L) :
    globalIdx L × regionIdx (L := L) Λ ≃ globalIdx L × regionIdx (L := L) Λ :=
  (globalSwap_pair_involutive Λ).toPerm

@[simp]
theorem globalSwapEquiv_apply (Λ : Finset L)
    (gf : globalIdx L × regionIdx (L := L) Λ) :
    globalSwapEquiv Λ gf = (globalSwap Λ gf.2 gf.1, regionRestrict Λ gf.1) :=
  rfl

/-! ### Pointwise action of `M ⊗ 1` on global tuples -/

/-- The "Λ-restriction of `w` around `g`" is the vector in
`regionHilbert Λ` whose `f`-th component is `w(globalSwap Λ f g)`.
It packages the data along which `M ⊗ 1_{Λᶜ}` acts as `M`. -/
noncomputable def wRestrict (Λ : Finset L) (w : globalHilbert L)
    (g : globalIdx L) : regionHilbert (L := L) Λ :=
  WithLp.toLp 2 (fun f : regionIdx (L := L) Λ =>
    (w : lp (fun _ : globalIdx L => ℂ) 2) (globalSwap Λ f g))

@[simp]
theorem wRestrict_apply (Λ : Finset L) (w : globalHilbert L) (g : globalIdx L)
    (f : regionIdx (L := L) Λ) :
    wRestrict Λ w g f =
      (w : lp (fun _ : globalIdx L => ℂ) 2) (globalSwap Λ f g) := rfl

/-- L²-norm of `wRestrict Λ w g`: it is the partial-row sum of `‖w‖²`. -/
theorem norm_sq_wRestrict (Λ : Finset L) (w : globalHilbert L) (g : globalIdx L) :
    ‖wRestrict Λ w g‖ ^ 2 = ∑ f : regionIdx (L := L) Λ,
      ‖(w : lp (fun _ : globalIdx L => ℂ) 2) (globalSwap Λ f g)‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

/-- Pointwise coefficient of `(M ⊗ 1_{Λᶜ}) w` at the global tuple `g`:
the value of `M (wRestrict Λ w g)` at the index `regionRestrict Λ g`. -/
noncomputable def localEmbedCoeff (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (w : globalHilbert L) (g : globalIdx L) : ℂ :=
  (M (wRestrict Λ w g)) (regionRestrict Λ g)

/-- Per-tuple bound: `‖localEmbedCoeff Λ M w g‖² ≤ ‖M‖² · ‖wRestrict Λ w g‖²`. -/
theorem norm_sq_localEmbedCoeff_le (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (w : globalHilbert L) (g : globalIdx L) :
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

/-- The squared-`lp` norm of `w` is summable along `globalIdx L`.
This is just `Memℓp.gen_iff` rewritten in `‖·‖²` form. -/
private theorem summable_w_norm_sq (w : globalHilbert L) :
    Summable fun h : globalIdx L =>
      ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2 := by
  have hmem : Memℓp ((w : lp (fun _ : globalIdx L => ℂ) 2) : globalIdx L → ℂ) 2 :=
    lp.memℓp w
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  rw [memℓp_gen_iff htwo] at hmem
  simpa [ENNReal.toReal_ofNat] using hmem

/-- Partial-sum bound: every Finset sum of `‖w h‖²` over `globalIdx L` is at
most `‖w‖²_lp`. -/
private theorem finsetSum_w_norm_sq_le (w : globalHilbert L) (s : Finset (globalIdx L)) :
    ∑ h ∈ s, ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2
      ≤ ∑' h : globalIdx L, ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2 :=
  (summable_w_norm_sq w).sum_le_tsum s (fun _ _ => sq_nonneg _)

/-- The total partial-sum bound for `‖wRestrict‖² = Σ_f ‖w(globalSwap Λ f g)‖²`. -/
private theorem finsetSum_wRestrict_norm_sq_le (Λ : Finset L) (w : globalHilbert L)
    (u : Finset (globalIdx L)) :
    ∑ g ∈ u, ‖wRestrict Λ w g‖ ^ 2
      ≤ (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
          ∑' h : globalIdx L, ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2 := by
  -- Expand wRestrict to a finite f-sum.
  have hexp : ∀ g, ‖wRestrict Λ w g‖ ^ 2 =
      ∑ f : regionIdx (L := L) Λ,
        ‖(w : lp (fun _ : globalIdx L => ℂ) 2) (globalSwap Λ f g)‖ ^ 2 :=
    norm_sq_wRestrict Λ w
  calc ∑ g ∈ u, ‖wRestrict Λ w g‖ ^ 2
      = ∑ g ∈ u, ∑ f : regionIdx (L := L) Λ,
          ‖(w : lp (fun _ : globalIdx L => ℂ) 2) (globalSwap Λ f g)‖ ^ 2 := by
        exact Finset.sum_congr rfl fun g _ => hexp g
    _ = ∑ p ∈ u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ)),
          ‖(w : lp (fun _ : globalIdx L => ℂ) 2) (globalSwap Λ p.2 p.1)‖ ^ 2 := by
        rw [Finset.sum_product]
    _ = ∑ p ∈ (u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv Λ),
          ‖(w : lp (fun _ : globalIdx L => ℂ) 2) p.1‖ ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ hab => (globalSwapEquiv Λ).injective hab)]
        refine Finset.sum_congr rfl ?_
        intro p _
        simp [globalSwapEquiv_apply]
    _ ≤ ∑ p ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv Λ)).image Prod.fst ×ˢ
              (Finset.univ : Finset (regionIdx (L := L) Λ)),
          ‖(w : lp (fun _ : globalIdx L => ℂ) 2) p.1‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
        intro p hp
        rw [Finset.mem_product]
        refine ⟨?_, Finset.mem_univ _⟩
        rw [Finset.mem_image]
        exact ⟨p, hp, rfl⟩
    _ = ∑ h ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv Λ)).image Prod.fst,
          ∑ _ : regionIdx (L := L) Λ,
            ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2 := by
        rw [Finset.sum_product]
    _ = ∑ h ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv Λ)).image Prod.fst,
          (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
            ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [Finset.sum_const, Finset.card_univ]
        simp [mul_comm]
    _ = (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
          ∑ h ∈ ((u ×ˢ (Finset.univ : Finset (regionIdx (L := L) Λ))).image
              (globalSwapEquiv Λ)).image Prod.fst,
            ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (Fintype.card (regionIdx (L := L) Λ) : ℝ) *
          ∑' h : globalIdx L, ‖(w : lp (fun _ : globalIdx L => ℂ) 2) h‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact finsetSum_w_norm_sq_le w _
        · exact Nat.cast_nonneg _

/-- Summability of `‖wRestrict Λ w g‖²` along `globalIdx L`. -/
theorem summable_norm_sq_wRestrict (Λ : Finset L) (w : globalHilbert L) :
    Summable fun g : globalIdx L => ‖wRestrict Λ w g‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) (finsetSum_wRestrict_norm_sq_le Λ w)

/-- Summability of `‖localEmbedCoeff Λ M w g‖²` along `globalIdx L`.
This places `localEmbedCoeff Λ M w` in `lp 2` and is the entry point to
upgrading the action `M ⊗ 1` to a continuous linear map. -/
theorem summable_norm_sq_localEmbedCoeff (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (w : globalHilbert L) :
    Summable fun g : globalIdx L => ‖localEmbedCoeff Λ M w g‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_
    ((summable_norm_sq_wRestrict Λ w).mul_left (‖M‖ ^ 2))
  intro g
  exact norm_sq_localEmbedCoeff_le Λ M w g

end LocalNetLike
