module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# ForMathlib: Slope and Derivative Sign Lemmas

## Main Results

* `deriv_nonpos_of_forall_lt_min`: If g has a local minimum from the left at x₀, then g'(x₀) ≤ 0.
-/

@[expose] public section

/-- Derivative sign lemma: if g has a minimum from the left at x₀, then g'(x₀) ≤ 0.
Formally: if g(x₀) ≤ g(y) for all y ∈ (x₀-ε, x₀) and g is differentiable at x₀,
then g'(x₀) ≤ 0.
Proof: the difference quotient (g(y) - g(x₀))/(y - x₀) ≤ 0 for y < x₀ and y near x₀,
and the limit equals the derivative. -/
lemma deriv_nonpos_of_forall_lt_min (g : ℝ → ℝ) (d : ℝ) (x₀ ε : ℝ) (hε : 0 < ε)
    (hd : HasDerivAt g d x₀) (hmin : ∀ y ∈ Set.Ioo (x₀ - ε) x₀, g x₀ ≤ g y) : d ≤ 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  haveI : (nhdsWithin x₀ (Set.Iio x₀)).NeBot :=
    nhdsWithin_Iio_self_neBot' ⟨x₀ - 1, by simp [Set.mem_Iio]⟩
  have hiio_sub : Set.Iio x₀ ⊆ {x₀}ᶜ := fun y hy => by
    simp [(Set.mem_Iio.mp hy).ne]
  have hslope2 := hd.mono_left (nhdsWithin_mono x₀ hiio_sub)
  suffices h : ∀ᶠ y in nhdsWithin x₀ (Set.Iio x₀), slope g x₀ y ≤ 0 from
    le_of_tendsto hslope2 h
  have hIoo : Set.Ioo (x₀ - ε) x₀ ∈ nhdsWithin x₀ (Set.Iio x₀) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (x₀ - ε) (x₀ + ε), isOpen_Ioo, ⟨by linarith, by linarith⟩,
           fun y ⟨hy1, hy2⟩ => ⟨hy1.1, hy2⟩⟩
  filter_upwards [hIoo] with y hy
  simp only [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmin y hy)) (by linarith [hy.2])

end
