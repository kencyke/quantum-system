module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Unitary mapping between unit vectors in a finite-dimensional Hilbert space

For any two unit vectors `u v` in a finite-dimensional inner product space
`H` over `𝕜` (with `RCLike 𝕜`), there exists a linear isometric equivalence
`V : H ≃ₗᵢ[𝕜] H` mapping `u` to `v`.

This is a standard fact in finite-dimensional Hilbert space theory: extend
`{u}` and `{v}` to orthonormal bases of the same cardinality, and pair them
via `OrthonormalBasis.equiv`.  The result is **non-canonical** — it depends
on the choice of basis extension.

## Main result

* `exists_linearIsometryEquiv_of_unit` — the existence statement above.

This is a candidate for upstreaming to Mathlib.
-/

@[expose] public section

open Module Set

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A singleton `{u}` of a unit vector is orthonormal as a subset family. -/
theorem orthonormal_singleton_of_norm_one {u : H} (hu : ‖u‖ = 1) :
    Orthonormal 𝕜 ((↑) : ({u} : Set H) → H) := by
  rw [orthonormal_iff_ite]
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a = u := ha
  have hb' : b = u := hb
  have hab : a = b := ha'.trans hb'.symm
  have hii : (⟨a, ha⟩ : ({u} : Set H)) = ⟨b, hb⟩ := Subtype.ext hab
  have hself : inner 𝕜 a b = ((1 : ℝ) : 𝕜) := by
    rw [ha', hb', inner_self_eq_norm_sq_to_K, hu]
    simp
  rw [if_pos hii]
  simpa using hself

/-- For any pair of unit vectors `u v` in a finite-dimensional inner product
space `H` over `𝕜`, there exists a linear isometric equivalence
`V : H ≃ₗᵢ[𝕜] H` with `V u = v`.

Construction: extend `{u}` and `{v}` to orthonormal bases of the same
finite cardinality, then pair them via `OrthonormalBasis.equiv` along an
equivalence of underlying index sets that maps the distinguished `u`-element
to the distinguished `v`-element.

The result is non-canonical: it depends on the (Classical-choice driven)
basis extension. -/
theorem exists_linearIsometryEquiv_of_unit [FiniteDimensional 𝕜 H] {u v : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ V : H ≃ₗᵢ[𝕜] H, V u = v := by
  classical
  -- Step 1: orthonormal basis extending {u}
  obtain ⟨wu, bu, hu_sub, hbu⟩ :=
    (orthonormal_singleton_of_norm_one (𝕜 := 𝕜) hu).exists_orthonormalBasis_extension
  -- Step 2: orthonormal basis extending {v}
  obtain ⟨wv, bv, hv_sub, hbv⟩ :=
    (orthonormal_singleton_of_norm_one (𝕜 := 𝕜) hv).exists_orthonormalBasis_extension
  -- Step 3: cardinalities match
  have hcard : wu.card = wv.card := by
    have h1 : wu.card = finrank 𝕜 H :=
      (Module.finrank_eq_card_finset_basis bu.toBasis).symm
    have h2 : wv.card = finrank 𝕜 H :=
      (Module.finrank_eq_card_finset_basis bv.toBasis).symm
    exact h1.trans h2.symm
  -- Step 4: build an equivalence wu ≃ wv mapping ⟨u, _⟩ to ⟨v, _⟩
  have huu : u ∈ wu := hu_sub rfl
  have hvv : v ∈ wv := hv_sub rfl
  let pu : (wu : Set H) := ⟨u, huu⟩
  let pv : (wv : Set H) := ⟨v, hvv⟩
  let e₀ : (wu : Set H) ≃ (wv : Set H) := Finset.equivOfCardEq hcard
  let e : (wu : Set H) ≃ (wv : Set H) :=
    e₀.trans (Equiv.swap (e₀ pu) pv)
  have he_pu : e pu = pv := by
    change Equiv.swap (e₀ pu) pv (e₀ pu) = pv
    exact Equiv.swap_apply_left _ _
  -- Step 5: construct V
  refine ⟨bu.equiv bv e, ?_⟩
  -- u = bu pu (as elements of H), v = bv pv
  have hu_eq : (bu pu : H) = u := by
    rw [hbu]
  have hv_eq : (bv pv : H) = v := by
    rw [hbv]
  calc bu.equiv bv e u
      = bu.equiv bv e (bu pu) := by rw [hu_eq]
    _ = bv (e pu) := bu.equiv_apply_basis bv e pu
    _ = bv pv := by rw [he_pu]
    _ = v := hv_eq
