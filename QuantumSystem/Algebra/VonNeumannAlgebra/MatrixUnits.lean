module

public import QuantumSystem.Algebra.VonNeumannAlgebra.CoveringFamily

/-!
# Matrix units of a type I factor and the multiplicity-one property

For a covering orthogonal family `F` of projections each Murray–von Neumann equivalent to the
minimal projection `e` (produced by `IsFactor.exists_orthEquivFam_top`; the members are minimal as
a consequence, though `OrthEquivFam` only records that each is a nonzero star projection in `N`
equivalent to `e`), this file builds the **system of matrix units** `e_{pq} = v_p v_q⋆` from the
equivalence partial isometries `v_p : e ≅ p`, and proves the
defining matrix-unit relations. It then establishes the **multiplicity-one** property: for every
`a ∈ N`, the matrix entry `v_p⋆ a v_q` is a *scalar* multiple of `e` (a direct consequence of the
corner condition `e N e = ℂ e` defining a minimal projection).

Together these say that `N` is, algebraically, the `*`-algebra of `F × F` matrices over `ℂ` — the
algebraic heart of the structure theorem `N ≅ B(ℓ²(F)) ⊗̄ 1`. The remaining (analytic) step is the
strong-operator convergence of `a = Σ_{pq} c_{pq}(a) e_{pq}` and the identification with
`vnTensorLeft`.

## Main definitions

* `VonNeumannAlgebra.OrthEquivFam.pisom` — a choice of equivalence partial isometry `v_p : e ≅ p`.
* `VonNeumannAlgebra.OrthEquivFam.matrixUnit` — the matrix unit `e_{pq} = v_p v_q⋆`.

## Main results

* `matrixUnit_mul_of_eq` / `matrixUnit_mul_of_ne` — the matrix-unit multiplication law
  `e_{pq} e_{rs} = δ_{qr} e_{ps}`.
* `OrthEquivFam.exists_matrixEntry` — multiplicity one: `∃ c, v_p⋆ a v_q = c • e` for `a ∈ N`.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H} {e : H →L[ℂ] H} {F : Set (H →L[ℂ] H)}

/-- A choice of partial isometry `v_p` implementing the Murray–von Neumann equivalence `e ∼[N] p`,
oriented with source projection `v_p⋆ v_p = e` (`pisom_source`) and range projection
`v_p v_p⋆ = p` (`pisom_range`). -/
noncomputable def OrthEquivFam.pisom (hF : OrthEquivFam N e F) (p : F) : H →L[ℂ] H :=
  (hF.1 p.1 p.2).2.2.2.choose

theorem OrthEquivFam.pisom_mem (hF : OrthEquivFam N e F) (p : F) : hF.pisom p ∈ N :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.1

theorem OrthEquivFam.pisom_isPI (hF : OrthEquivFam N e F) (p : F) :
    IsPartialIsometry (hF.pisom p) :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.2.1

theorem OrthEquivFam.pisom_source (hF : OrthEquivFam N e F) (p : F) :
    star (hF.pisom p) * hF.pisom p = e :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.2.2.1

theorem OrthEquivFam.pisom_range (hF : OrthEquivFam N e F) (p : F) :
    hF.pisom p * star (hF.pisom p) = (p : H →L[ℂ] H) :=
  (hF.1 p.1 p.2).2.2.2.choose_spec.2.2.2

/-- `v_p e = v_p`: the source projection acts as a right unit on `v_p`. -/
theorem OrthEquivFam.pisom_mul_source (hF : OrthEquivFam N e F) (p : F) :
    hF.pisom p * e = hF.pisom p := by
  have h : hF.pisom p * (star (hF.pisom p) * hF.pisom p) = hF.pisom p := by
    rw [← mul_assoc]; exact hF.pisom_isPI p
  rwa [hF.pisom_source p] at h

/-- `e v_p⋆ = v_p⋆`: the source projection acts as a left unit on `v_p⋆`. -/
theorem OrthEquivFam.e_mul_star_pisom (hF : OrthEquivFam N e F) (p : F) :
    e * star (hF.pisom p) = star (hF.pisom p) := by
  have h : star (hF.pisom p) * hF.pisom p * star (hF.pisom p) = star (hF.pisom p) := by
    have h' : star (hF.pisom p) * star (star (hF.pisom p)) * star (hF.pisom p)
        = star (hF.pisom p) := IsPartialIsometry.star (hF.pisom_isPI p)
    rwa [star_star] at h'
  rwa [hF.pisom_source p] at h

/-- For distinct family members the partial isometries are orthogonal: `v_q⋆ v_r = 0`. -/
theorem OrthEquivFam.star_pisom_mul_pisom_of_ne (hF : OrthEquivFam N e F) {q r : F}
    (hqr : q ≠ r) : star (hF.pisom q) * hF.pisom r = 0 := by
  have hq : (q : H →L[ℂ] H) * hF.pisom q = hF.pisom q := by
    have h : hF.pisom q * star (hF.pisom q) * hF.pisom q = hF.pisom q := hF.pisom_isPI q
    rwa [hF.pisom_range q] at h
  have hr : (r : H →L[ℂ] H) * hF.pisom r = hF.pisom r := by
    have h : hF.pisom r * star (hF.pisom r) * hF.pisom r = hF.pisom r := hF.pisom_isPI r
    rwa [hF.pisom_range r] at h
  have hsq : star (hF.pisom q) * (q : H →L[ℂ] H) = star (hF.pisom q) := by
    have := congrArg star hq
    rwa [star_mul, (hF.1 q.1 q.2).1.isSelfAdjoint.star_eq] at this
  have h0 : (q : H →L[ℂ] H) * r = 0 := hF.2 q.2 r.2 (fun h => hqr (Subtype.ext h))
  calc star (hF.pisom q) * hF.pisom r
      = (star (hF.pisom q) * (q : H →L[ℂ] H)) * ((r : H →L[ℂ] H) * hF.pisom r) := by
        rw [hsq, hr]
    _ = star (hF.pisom q) * ((q : H →L[ℂ] H) * r) * hF.pisom r := by simp only [mul_assoc]
    _ = 0 := by rw [h0, mul_zero, zero_mul]

/-- The **matrix unit** `e_{pq} = v_p v_q⋆`. -/
noncomputable def OrthEquivFam.matrixUnit (hF : OrthEquivFam N e F) (p q : F) : H →L[ℂ] H :=
  hF.pisom p * star (hF.pisom q)

/-- Definitional unfolding of the matrix unit: `e_{pq} = v_p v_q⋆`. -/
theorem OrthEquivFam.matrixUnit_def (hF : OrthEquivFam N e F) (p q : F) :
    hF.matrixUnit p q = hF.pisom p * star (hF.pisom q) := rfl

/-- Matrix units lie in `N`. -/
theorem OrthEquivFam.matrixUnit_mem (hF : OrthEquivFam N e F) (p q : F) :
    hF.matrixUnit p q ∈ N :=
  mul_mem (hF.pisom_mem p) (star_mem (hF.pisom_mem q))

/-- The diagonal matrix unit is the projection: `e_{pp} = p`. -/
theorem OrthEquivFam.matrixUnit_self (hF : OrthEquivFam N e F) (p : F) :
    hF.matrixUnit p p = (p : H →L[ℂ] H) := hF.pisom_range p

/-- Matrix units are adjoint-symmetric: `e_{pq}⋆ = e_{qp}`. -/
theorem OrthEquivFam.star_matrixUnit (hF : OrthEquivFam N e F) (p q : F) :
    star (hF.matrixUnit p q) = hF.matrixUnit q p := by
  rw [matrixUnit_def, matrixUnit_def, star_mul, star_star]

/-- Matrix-unit multiplication law `e_{pq} e_{rs} = δ_{qr} e_{ps}`, diagonal case `q = r`:
`e_{pq} e_{qs} = e_{ps}`. -/
theorem OrthEquivFam.matrixUnit_mul_of_eq (hF : OrthEquivFam N e F) (p q s : F) :
    hF.matrixUnit p q * hF.matrixUnit q s = hF.matrixUnit p s := by
  rw [matrixUnit_def, matrixUnit_def, matrixUnit_def]
  calc hF.pisom p * star (hF.pisom q) * (hF.pisom q * star (hF.pisom s))
      = hF.pisom p * (star (hF.pisom q) * hF.pisom q) * star (hF.pisom s) := by
        simp only [mul_assoc]
    _ = hF.pisom p * e * star (hF.pisom s) := by rw [hF.pisom_source q]
    _ = hF.pisom p * star (hF.pisom s) := by rw [hF.pisom_mul_source p]

/-- Matrix-unit multiplication law `e_{pq} e_{rs} = δ_{qr} e_{ps}`, off-diagonal case `q ≠ r`:
`e_{pq} e_{rs} = 0`. -/
theorem OrthEquivFam.matrixUnit_mul_of_ne (hF : OrthEquivFam N e F) (p s : F) {q r : F}
    (hqr : q ≠ r) : hF.matrixUnit p q * hF.matrixUnit r s = 0 := by
  rw [matrixUnit_def, matrixUnit_def]
  calc hF.pisom p * star (hF.pisom q) * (hF.pisom r * star (hF.pisom s))
      = hF.pisom p * (star (hF.pisom q) * hF.pisom r) * star (hF.pisom s) := by
        simp only [mul_assoc]
    _ = 0 := by rw [hF.star_pisom_mul_pisom_of_ne hqr, mul_zero, zero_mul]

/-- **Multiplicity one.** For a minimal projection `e` and any `a ∈ N`, the matrix entry
`v_p⋆ a v_q` is a scalar multiple of `e`. This is the corner condition `e N e = ℂ e` transported
along the equivalences, and is the algebraic content of `N ≅ B(ℓ²(F)) ⊗̄ 1`. -/
theorem OrthEquivFam.exists_matrixEntry (hF : OrthEquivFam N e F)
    (he : IsMinimalProjection N e) (p q : F) {a : H →L[ℂ] H} (ha : a ∈ N) :
    ∃ c : ℂ, star (hF.pisom p) * a * hF.pisom q = c • e := by
  have hbN : star (hF.pisom p) * a * hF.pisom q ∈ N :=
    mul_mem (mul_mem (star_mem (hF.pisom_mem p)) ha) (hF.pisom_mem q)
  obtain ⟨c, hc⟩ := he.2.2.2 _ hbN
  refine ⟨c, ?_⟩
  have key : e * (star (hF.pisom p) * a * hF.pisom q) * e
      = star (hF.pisom p) * a * hF.pisom q := by
    calc e * (star (hF.pisom p) * a * hF.pisom q) * e
        = (e * star (hF.pisom p)) * a * (hF.pisom q * e) := by simp only [mul_assoc]
      _ = star (hF.pisom p) * a * hF.pisom q := by
          rw [hF.e_mul_star_pisom p, hF.pisom_mul_source q]
  rw [← key, hc]

end VonNeumannAlgebra
