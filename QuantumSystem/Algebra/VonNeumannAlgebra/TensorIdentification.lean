module

public import QuantumSystem.Algebra.VonNeumannAlgebra.GeneratedByMatrixUnits
public import QuantumSystem.Algebra.VonNeumannAlgebra.TensorFactor

/-!
# Spatial identification of a type I factor with `B(H₁) ⊗̄ 1`

This file completes the spatial structure theorem for a type I factor `N ⊆ B(H)` with minimal
projection `e`: there is a linear isometric equivalence `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` under which `N`
becomes exactly the tensor factor `B(ℓ²(F)) ⊗̄ 1` and `N'` becomes the right factor `1 ⊗̄ B(eH)`.

The identification glues the generation theorem `N = ⟨matrix units⟩''` (`GeneratedByMatrixUnits`)
to the tensor commutation theorem (`Algebra.VonNeumannAlgebra.TensorFactor`) through the spatial isomorphism
`U = multiplicityEquiv ∘ lpTensorEquiv`. The key computation is that `U` carries the matrix unit
`e_{pq}` to the amplified rank-one operator `|δ_p⟩⟨δ_q| ⊗̂ 1`, where `δ_p = lp.single 2 p 1` is the
`p`-th standard basis vector of `ℓ²(F)`.

## Main results

* `VonNeumannAlgebra.OrthEquivFam.coe_multiplicityEquiv_apply` — the explicit `i`-th coordinate of
  `U y`: `(multiplicityEquiv y) i = v_i⋆ y`.
* `VonNeumannAlgebra.OrthEquivFam.hasSum_tmul_spatialEquiv` — the resulting expansion
  `U y = ∑ᵢ δᵢ ⊗̂ (v_i⋆ y)`.
* `VonNeumannAlgebra.OrthEquivFam.conjStarAlgEquiv_matrixUnit` — `U e_{pq} U⋆ = |δ_p⟩⟨δ_q| ⊗̂ 1`.
* `VonNeumannAlgebra.OrthEquivFam.conj_spatialEquiv_eq_vnTensorLeft` — the identification
  `U N U⋆ = B(ℓ²(F)) ⊗̄ 1`, with commutant companion `conj_spatialEquiv_commutant_eq_vnTensorRight`.
* `VonNeumannAlgebra.IsFactor.exists_spatial_tensorDecomposition` — the existence headline.
* `VonNeumannAlgebra.IsFactor.exists_split_tensorDecomposition` — the split tensor decomposition:
  for an intermediate type I factor `A₁ ≤ N ≤ A₂'`, the same `U` sends `A₁` into `B(ℓ²(F)) ⊗̄ 1`
  and `A₂` into `1 ⊗̄ B(eH)`.
-/

@[expose] public section

open scoped TensorProduct

namespace VonNeumannAlgebra

open HilbertTensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H} {e : H →L[ℂ] H} {F : Set (H →L[ℂ] H)}

/-- The `i`-th standard basis vector `δ_i = lp.single 2 i 1` of `ℓ²(F) = lp (fun _ : F => ℂ) 2`.
This is a thin wrapper whose only purpose is to pin the index family `fun _ : F => ℂ`, so that the
basis vectors are unambiguous in scalar positions (such as inner products). -/
noncomputable def lpDelta [DecidableEq F] (i : F) : lp (fun _ : F => ℂ) 2 :=
  lp.single (E := fun _ : F => ℂ) 2 i (1 : ℂ)

/-- `δ i` abbreviates the standard basis vector `lpDelta i` of `ℓ²(F)`, matching the `δ_i` of the
informal text. (A Dirac bra-ket `|x⟩⟨y|` notation for the rank-one operator is deliberately not
introduced here: a leading `|` token collides with the set-builder `{y | … }` used in the `htop`
hypotheses throughout this file.) -/
local notation "δ" => lpDelta

omit [CompleteSpace H] in
lemma lpDelta_apply [DecidableEq F] (i : F) :
    lpDelta i = lp.single (E := fun _ : F => ℂ) 2 i (1 : ℂ) := rfl

omit [CompleteSpace H] in
/-- The basis vectors `δ_i` are unit vectors. -/
lemma lpDelta_norm [DecidableEq F] (i : F) : ‖lpDelta i‖ = 1 := by
  rw [lpDelta_apply, lp.norm_single (by norm_num), norm_one]

omit [CompleteSpace H] in
/-- The standard basis vectors `δ_i` span a dense subspace of `ℓ²(F)`. -/
lemma dense_span_lpDelta [DecidableEq F] :
    Dense (Submodule.span ℂ (Set.range (lpDelta : F → lp (fun _ : F => ℂ) 2)) :
      Set (lp (fun _ : F => ℂ) 2)) := by
  intro g
  have hsum : HasSum (fun i : F => lp.single (E := fun _ : F => ℂ) 2 i (g i)) g :=
    lp.hasSum_single (by norm_num) g
  refine mem_closure_of_tendsto hsum (Filter.Eventually.of_forall (fun s => ?_))
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [show lp.single (E := fun _ : F => ℂ) 2 i (g i) = (g i) • lpDelta i by
    rw [lpDelta_apply, ← lp.single_smul, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Explicit multiplicity coordinate.** Under the spatial decomposition the `i`-th coordinate of
`y` in `ℓ²(F; eH)` is `v_i⋆ y`, where `v_i` is the equivalence partial isometry `e ≅ i`. -/
theorem OrthEquivFam.coe_multiplicityEquiv_apply (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    (y : H) (i : F) :
    ((hF.multiplicityEquiv htop y i : LinearMap.range (e : H →ₗ[ℂ] H)) : H)
      = star (hF.pisom i) y := by
  have hop : star (hF.pisom i) * (i : H →L[ℂ] H) = star (hF.pisom i) := by
    rw [← hF.pisom_range i, ← mul_assoc, hF.pisom_source i, hF.e_mul_star_pisom i]
  have h1 : ((hF.multiplicityEquiv htop y i : LinearMap.range (e : H →ₗ[ℂ] H)) : H)
      = star (hF.pisom i)
          ((hF.hilbertSumEquiv htop y i : LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)) : H) :=
    (hF.pisom_isPI i).coe_sourceRangeEquiv_symm (hF.pisom_source i) (hF.pisom_range i) _
  rw [h1, hF.coe_hilbertSumEquiv_apply htop y i, ← ContinuousLinearMap.mul_apply, hop]

/-- **The spatial isomorphism.** A covering orthogonal family of `e`-equivalent projections gives a
linear isometric equivalence `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` of `H` with the completed Hilbert tensor
product, identifying `H` with `ℓ²(F) ⊗̂ (eH)` via `multiplicityEquiv` and the tensor bridge. This is
the isomorphism implementing the type I structure theorem `N ≅ B(ℓ²(F)) ⊗̄ 1`. -/
noncomputable def OrthEquivFam.spatialEquiv (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] [DecidableEq F] :
    H ≃ₗᵢ[ℂ] HilbertTensor (lp (fun _ : F => ℂ) 2) (LinearMap.range (e : H →ₗ[ℂ] H)) :=
  (hF.multiplicityEquiv htop).trans (lpTensorEquiv (ι := F) (K := LinearMap.range (e : H →ₗ[ℂ] H)))

/-- **Spatial expansion of `U`.** The spatial isomorphism `U = multiplicityEquiv ∘ lpTensorEquiv`
expands a vector as `U y = ∑ᵢ δᵢ ⊗̂ (i-th multiplicity coordinate of y)`. -/
theorem OrthEquivFam.hasSum_tmul_spatialEquiv (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] [DecidableEq F] (y : H) :
    HasSum (fun i : F => tmul (δ i) (hF.multiplicityEquiv htop y i))
      (hF.spatialEquiv htop y) := by
  have h := (lp.hasSum_single (E := fun _ : F => LinearMap.range (e : H →ₗ[ℂ] H)) (p := 2)
      (by norm_num) (hF.multiplicityEquiv htop y)).mapL
      (lpTensorEquiv (ι := F)
        (K := LinearMap.range (e : H →ₗ[ℂ] H))).toLinearIsometry.toContinuousLinearMap
  simpa only [OrthEquivFam.spatialEquiv, lpDelta, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, lpTensorEquiv_single,
    LinearIsometryEquiv.trans_apply] using h

attribute [local irreducible] OrthEquivFam.spatialEquiv OrthEquivFam.multiplicityEquiv

/-- The `p`-th coordinate of `U (e_{pq} y)` collapses to the single term `δ_p ⊗̂ (v_q⋆ y)`: every
other coordinate vanishes because `v_i⋆ e_{pq} = 0` for `i ≠ p`. -/
lemma OrthEquivFam.spatialEquiv_matrixUnit_apply (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] [DecidableEq F] (p q : F) (y : H) :
    hF.spatialEquiv htop (hF.matrixUnit p q y)
      = tmul (δ p) (hF.multiplicityEquiv htop (hF.matrixUnit p q y) p) := by
  refine (hF.hasSum_tmul_spatialEquiv htop (hF.matrixUnit p q y)).unique ?_
  refine hasSum_single p (fun i hi => ?_)
  have hcoe : ((hF.multiplicityEquiv htop (hF.matrixUnit p q y) i :
      LinearMap.range (e : H →ₗ[ℂ] H)) : H) = 0 := by
    rw [hF.coe_multiplicityEquiv_apply htop]
    have h0 : star (hF.pisom i) * hF.matrixUnit p q = 0 := by
      rw [OrthEquivFam.matrixUnit_def, ← mul_assoc,
        hF.star_pisom_mul_pisom_of_ne hi, zero_mul]
    rw [← ContinuousLinearMap.mul_apply, h0, ContinuousLinearMap.zero_apply]
  rw [show hF.multiplicityEquiv htop (hF.matrixUnit p q y) i = 0 from
    Subtype.ext (by rw [hcoe]; rfl), ← tmulRightL_apply, map_zero]

/-- The surviving coordinates agree: `v_p⋆ (e_{pq} y) = v_q⋆ y`. -/
lemma OrthEquivFam.multiplicityEquiv_matrixUnit_coord (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    (p q : F) (y : H) :
    hF.multiplicityEquiv htop (hF.matrixUnit p q y) p = hF.multiplicityEquiv htop y q := by
  apply Subtype.ext
  rw [hF.coe_multiplicityEquiv_apply htop, hF.coe_multiplicityEquiv_apply htop]
  have hpp : star (hF.pisom p) * hF.matrixUnit p q = star (hF.pisom q) := by
    rw [OrthEquivFam.matrixUnit_def, ← mul_assoc, hF.pisom_source p, hF.e_mul_star_pisom q]
  rw [← ContinuousLinearMap.mul_apply, hpp]

/-- The amplified rank-one operator on `U y` collapses to the single term `δ_p ⊗̂ (v_q⋆ y)`: the
rank-one operator picks out the `q`-th coordinate. -/
lemma OrthEquivFam.amplifyLeft_rankOne_spatialEquiv (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] [DecidableEq F] (p q : F) (y : H) :
    amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q)) (hF.spatialEquiv htop y)
      = tmul (δ p) (hF.multiplicityEquiv htop y q) := by
  have key : ∀ i : F, amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q))
      (tmul (δ i) (hF.multiplicityEquiv htop y i))
      = (inner ℂ (δ q) (δ i) : ℂ) • tmul (δ p) (hF.multiplicityEquiv htop y i) :=
    fun i => by rw [amplifyLeft_tmul, InnerProductSpace.rankOne_apply, tmul_smul_left]
  have hqq : (inner ℂ (δ q) (δ q) : ℂ) = 1 := by
    rw [lpDelta_apply, lp.inner_single_left, lp.coeFn_single, Pi.single_eq_same,
      RCLike.inner_apply, map_one, mul_one]
  have hz : ∀ i : F, i ≠ q → amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q))
      (tmul (δ i) (hF.multiplicityEquiv htop y i)) = 0 := by
    intro i hi
    have hzero : (inner ℂ (δ q) (δ i) : ℂ) = 0 := by
      rw [lpDelta_apply, lpDelta_apply, lp.inner_single_left, lp.coeFn_single,
        Pi.single_eq_of_ne (Ne.symm hi), inner_zero_right]
    rw [key i, hzero, zero_smul]
  have hval : amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q))
      (tmul (δ q) (hF.multiplicityEquiv htop y q))
      = tmul (δ p) (hF.multiplicityEquiv htop y q) := by
    rw [key q, hqq, one_smul]
  exact (((hF.hasSum_tmul_spatialEquiv htop y).mapL
    (amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q)))).unique
    (hasSum_single q hz)).trans hval

/-- **Intertwining relation.** The spatial isomorphism intertwines the matrix unit `e_{pq}` with
the amplified rank-one operator: `U (e_{pq} y) = (|δ_p⟩⟨δ_q| ⊗̂ 1) (U y)`. -/
lemma OrthEquivFam.spatialEquiv_intertwine (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] [DecidableEq F] (p q : F) (y : H) :
    hF.spatialEquiv htop (hF.matrixUnit p q y)
      = amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q)) (hF.spatialEquiv htop y) :=
  (hF.spatialEquiv_matrixUnit_apply htop p q y).trans
    ((congrArg (tmul (δ p)) (hF.multiplicityEquiv_matrixUnit_coord htop p q y)).trans
      (hF.amplifyLeft_rankOne_spatialEquiv htop p q y).symm)

/-- **Matrix unit identifies with an amplified rank-one operator.** Under the spatial isomorphism
`U`, the matrix unit `e_{pq}` is carried to the amplification of the rank-one operator
`|δ_p⟩⟨δ_q|` on `ℓ²(F)`: `U e_{pq} U⋆ = |δ_p⟩⟨δ_q| ⊗̂ 1`. This is the algebraic heart of the
identification `N ≅ B(ℓ²(F)) ⊗̄ 1`. -/
theorem OrthEquivFam.conjStarAlgEquiv_matrixUnit (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] [DecidableEq F] (p q : F) :
    (hF.spatialEquiv htop).conjStarAlgEquiv (hF.matrixUnit p q)
      = amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q)) := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  exact (hF.spatialEquiv_intertwine htop p q ((hF.spatialEquiv htop).symm w)).trans
    (congrArg (amplifyLeft (InnerProductSpace.rankOne ℂ (δ p) (δ q)))
      (LinearIsometryEquiv.apply_symm_apply (hF.spatialEquiv htop) w))

omit [CompleteSpace H] in
/-- **The amplified basis rank-one operators generate `B(ℓ²(F)) ⊗̄ 1`.** The von Neumann algebra
generated by `{|δ_p⟩⟨δ_q| ⊗̂ 1 : p q : F}` is the tensor factor `vnTensorLeft = B(ℓ²(F)) ⊗̄ 1`. The
proof computes the commutant: an operator commuting with all the amplified rank-one operators lies
in `1 ⊗̄ B(eH)` (the dense slice lemma, using that `{δ_p}` spans densely), and conversely
`1 ⊗̄ B(eH)` commutes with them; so the commutant is `vnTensorRight`, whose commutant is
`vnTensorLeft`. -/
lemma generated_amplifyLeft_rankOne_eq [Nonempty F] [DecidableEq F]
    [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] :
    VonNeumannAlgebra.generated (Set.range (fun pq : F × F =>
        amplifyLeft (H₂ := LinearMap.range (e : H →ₗ[ℂ] H))
          (InnerProductSpace.rankOne ℂ (δ pq.1) (δ pq.2))))
      = vnTensorLeft := by
  set T := Set.range (fun pq : F × F => amplifyLeft (H₂ := LinearMap.range (e : H →ₗ[ℂ] H))
    (InnerProductSpace.rankOne ℂ (δ pq.1) (δ pq.2))) with hTdef
  have hcomm : VonNeumannAlgebra.commutantSet T = vnTensorRight := by
    refine le_antisymm (fun x hx => ?_) ?_
    · refine mem_vnTensorRight_of_commutes_dense (δ (Classical.arbitrary F))
        (lpDelta_norm _) (Set.range lpDelta) dense_span_lpDelta x (fun f hf => ?_)
      obtain ⟨p, rfl⟩ := hf
      have hg : amplifyLeft (H₂ := LinearMap.range (e : H →ₗ[ℂ] H))
          (InnerProductSpace.rankOne ℂ (δ p) (δ (Classical.arbitrary F))) ∈ T :=
        ⟨(p, Classical.arbitrary F), rfl⟩
      have hcx := (VonNeumannAlgebra.mem_commutantSet_iff.mp hx _ hg).1
      exact hcx.symm
    · refine VonNeumannAlgebra.generated_le ?_
      rintro g ⟨B, rfl⟩
      rw [SetLike.mem_coe, VonNeumannAlgebra.mem_commutantSet_iff]
      rintro h ⟨pq, rfl⟩
      refine ⟨amplifyLeft_comp_amplifyRight
        (InnerProductSpace.rankOne ℂ (δ pq.1) (δ pq.2)) B, ?_⟩
      rw [amplifyLeft_star]
      exact amplifyLeft_comp_amplifyRight
        (star (InnerProductSpace.rankOne ℂ (δ pq.1) (δ pq.2))) B
  haveI : Nontrivial (lp (fun _ : F => ℂ) 2) :=
    ⟨lpDelta (Classical.arbitrary F), 0, by
      rw [← norm_ne_zero_iff, lpDelta_norm]; norm_num⟩
  exact (congrArg VonNeumannAlgebra.commutant hcomm).trans
    (vnTensorRight_commutant (H₁ := lp (fun _ : F => ℂ) 2)
      (H₂ := LinearMap.range (e : H →ₗ[ℂ] H)))

/-- **Type I factor structure theorem (explicit identification).** Under the spatial isomorphism
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)`, the type I factor `N` is carried exactly onto the tensor factor
`B(ℓ²(F)) ⊗̄ 1`: `U N U⋆ = B(ℓ²(F)) ⊗̄ 1`. This glues the matrix-unit generation theorem
`N = ⟨e_{pq}⟩''` to the identification `U e_{pq} U⋆ = |δ_p⟩⟨δ_q| ⊗̂ 1` through the fact that the
spatial conjugation commutes with the generated-algebra construction. -/
theorem OrthEquivFam.conj_spatialEquiv_eq_vnTensorLeft (hF : OrthEquivFam N e F)
    (he : IsMinimalProjection N e)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [Nonempty F] [DecidableEq F] [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] :
    VonNeumannAlgebra.conj (hF.spatialEquiv htop) N = vnTensorLeft := by
  have himg : ⇑(hF.spatialEquiv htop).conjStarAlgEquiv ''
      (Set.range (fun pq : F × F => hF.matrixUnit pq.1 pq.2))
      = Set.range (fun pq : F × F =>
        amplifyLeft (H₂ := LinearMap.range (e : H →ₗ[ℂ] H))
          (InnerProductSpace.rankOne ℂ (δ pq.1) (δ pq.2))) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun pq => hF.conjStarAlgEquiv_matrixUnit htop pq.1 pq.2)
  calc VonNeumannAlgebra.conj (hF.spatialEquiv htop) N
      = VonNeumannAlgebra.conj (hF.spatialEquiv htop)
          (VonNeumannAlgebra.generated (Set.range (fun pq : F × F => hF.matrixUnit pq.1 pq.2))) :=
        congrArg (VonNeumannAlgebra.conj (hF.spatialEquiv htop))
          (hF.generated_matrixUnits_eq he htop).symm
    _ = VonNeumannAlgebra.generated (⇑(hF.spatialEquiv htop).conjStarAlgEquiv ''
          Set.range (fun pq : F × F => hF.matrixUnit pq.1 pq.2)) :=
        VonNeumannAlgebra.conj_generated _ _
    _ = VonNeumannAlgebra.generated (Set.range (fun pq : F × F =>
          amplifyLeft (H₂ := LinearMap.range (e : H →ₗ[ℂ] H))
            (InnerProductSpace.rankOne ℂ (δ pq.1) (δ pq.2)))) :=
        congrArg VonNeumannAlgebra.generated himg
    _ = vnTensorLeft := generated_amplifyLeft_rankOne_eq

/-- **Type I factor structure theorem (commutant).** The same spatial isomorphism carries the
commutant `N'` onto `1 ⊗̄ B(eH)`: `U N' U⋆ = 1 ⊗̄ B(eH)`. This is the companion of
`conj_spatialEquiv_eq_vnTensorLeft`, obtained from it because conjugation commutes with taking
commutants and `(B(ℓ²(F)) ⊗̄ 1)' = 1 ⊗̄ B(eH)`. -/
theorem OrthEquivFam.conj_spatialEquiv_commutant_eq_vnTensorRight (hF : OrthEquivFam N e F)
    (he : IsMinimalProjection N e)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [Nonempty F] [DecidableEq F] [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))] :
    VonNeumannAlgebra.conj (hF.spatialEquiv htop) N′ = vnTensorRight := by
  haveI : Nontrivial (lp (fun _ : F => ℂ) 2) :=
    ⟨lpDelta (Classical.arbitrary F), 0, by
      rw [← norm_ne_zero_iff, lpDelta_norm]; norm_num⟩
  rw [← VonNeumannAlgebra.conj_commutant, hF.conj_spatialEquiv_eq_vnTensorLeft he htop,
    vnTensorLeft_commutant]

/-- **Split inclusion (left factor).** Any von Neumann subalgebra `A₁ ≤ N` of the type I factor `N`
is carried by the spatial isomorphism into the left tensor factor: `U A₁ U⋆ ≤ B(ℓ²(F)) ⊗̄ 1`. This
is monotonicity of spatial conjugation composed with `U N U⋆ = vnTensorLeft`. -/
lemma OrthEquivFam.conj_spatialEquiv_le_vnTensorLeft (hF : OrthEquivFam N e F)
    (he : IsMinimalProjection N e)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [Nonempty F] [DecidableEq F] [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))]
    {A₁ : VonNeumannAlgebra H} (h₁ : A₁ ≤ N) :
    VonNeumannAlgebra.conj (hF.spatialEquiv htop) A₁ ≤ vnTensorLeft :=
  (VonNeumannAlgebra.conj_mono _ h₁).trans_eq (hF.conj_spatialEquiv_eq_vnTensorLeft he htop)

/-- **Split inclusion (right factor).** Any von Neumann algebra `A₂` whose commutant contains `N`
(equivalently `A₂ ⊆ N'`) is carried by the spatial isomorphism into the right tensor factor:
`U A₂ U⋆ ≤ 1 ⊗̄ B(eH)`. The hypothesis `N ≤ A₂'` is the split-property condition; taking commutants
turns it into `A₂ ≤ N'`, and monotonicity composed with `U N' U⋆ = vnTensorRight` finishes. -/
lemma OrthEquivFam.conj_spatialEquiv_le_vnTensorRight (hF : OrthEquivFam N e F)
    (he : IsMinimalProjection N e)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    [Nonempty F] [DecidableEq F] [CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H))]
    {A₂ : VonNeumannAlgebra H} (h₂ : N ≤ A₂′) :
    VonNeumannAlgebra.conj (hF.spatialEquiv htop) A₂ ≤ vnTensorRight := by
  have hA₂ : A₂ ≤ N′ := by
    have h := VonNeumannAlgebra.commutant_le h₂
    rwa [VonNeumannAlgebra.commutant_commutant] at h
  exact (VonNeumannAlgebra.conj_mono _ hA₂).trans_eq
    (hF.conj_spatialEquiv_commutant_eq_vnTensorRight he htop)

omit [CompleteSpace H] in
/-- A covering orthogonal family of a nonzero Hilbert space is nonempty: its ranges span a dense
subspace, which would be `{0}` were the family empty. -/
lemma OrthEquivFam.nonempty_of_top [Nontrivial H] {F : Set (H →L[ℂ] H)}
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤) :
    Nonempty F := by
  rw [← not_isEmpty_iff]
  intro hempty
  have hset : {y : H | ∃ f ∈ F, ∃ x, f x = y} = (∅ : Set H) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨f, hf, x, rfl⟩
    exact hempty.false ⟨f, hf⟩
  obtain ⟨z, hz⟩ := exists_ne (0 : H)
  have hmem : z ∈ (⊤ : Submodule ℂ H) := Submodule.mem_top
  rw [← htop, hset, Submodule.span_empty, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe, Submodule.bot_coe, closure_singleton,
    Set.mem_singleton_iff] at hmem
  exact hz hmem

/-- **Type I factor structure theorem (existence form).** A type I factor `N ⊆ B(H)` with minimal
projection `e` (acting on a nonzero Hilbert space) is, up to a spatial isomorphism
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)`, exactly the tensor factor `B(ℓ²(F)) ⊗̄ 1`, with commutant `1 ⊗̄ B(eH)`:
conjugation by `U` carries `N` onto `vnTensorLeft` and `N'` onto `vnTensorRight`. This is
Yngvason §5.1 (38)→(39) in its model-independent von-Neumann-algebraic form. -/
theorem IsFactor.exists_spatial_tensorDecomposition {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e) :
    ∃ (F : Set (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ]
        HilbertTensor (lp (fun _ : F => ℂ) 2) (LinearMap.range (e : H →ₗ[ℂ] H))),
      VonNeumannAlgebra.conj U N = vnTensorLeft ∧
      VonNeumannAlgebra.conj U N′ = vnTensorRight := by
  haveI := he.nontrivial
  obtain ⟨F, hF, htop⟩ := hN.exists_orthEquivFam_top he
  haveI : CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H)) := he.1.completeSpace_range
  haveI : DecidableEq F := Classical.decEq _
  haveI : Nonempty F := OrthEquivFam.nonempty_of_top htop
  exact ⟨F, hF.spatialEquiv htop, hF.conj_spatialEquiv_eq_vnTensorLeft he htop,
    hF.conj_spatialEquiv_commutant_eq_vnTensorRight he htop⟩

/-- **Split tensor decomposition (Yngvason §5.1 (38)→(39)).** Suppose an intermediate type I factor
`N ⊆ B(H)` with minimal projection `e` is sandwiched between two von Neumann algebras,
`A₁ ≤ N ≤ A₂'` — the *split property* for the pair `(A₁, A₂)`. Then there is a spatial isomorphism
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` simultaneously tensor-splitting both algebras: `A₁` lands in the left
factor `B(ℓ²(F)) ⊗̄ 1` and `A₂` lands in the right factor `1 ⊗̄ B(eH)`, with `N` and its commutant
identified exactly. The existence of such an intermediate type I factor `N` is the
model-dependent split-property input; everything downstream of it is proved here. -/
theorem IsFactor.exists_split_tensorDecomposition {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e)
    {A₁ A₂ : VonNeumannAlgebra H} (h₁ : A₁ ≤ N) (h₂ : N ≤ A₂′) :
    ∃ (F : Set (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ]
        HilbertTensor (lp (fun _ : F => ℂ) 2) (LinearMap.range (e : H →ₗ[ℂ] H))),
      VonNeumannAlgebra.conj U N = vnTensorLeft ∧
      VonNeumannAlgebra.conj U N′ = vnTensorRight ∧
      VonNeumannAlgebra.conj U A₁ ≤ vnTensorLeft ∧
      VonNeumannAlgebra.conj U A₂ ≤ vnTensorRight := by
  haveI := he.nontrivial
  obtain ⟨F, hF, htop⟩ := hN.exists_orthEquivFam_top he
  haveI : CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H)) := he.1.completeSpace_range
  haveI : DecidableEq F := Classical.decEq _
  haveI : Nonempty F := OrthEquivFam.nonempty_of_top htop
  exact ⟨F, hF.spatialEquiv htop, hF.conj_spatialEquiv_eq_vnTensorLeft he htop,
    hF.conj_spatialEquiv_commutant_eq_vnTensorRight he htop,
    hF.conj_spatialEquiv_le_vnTensorLeft he htop h₁,
    hF.conj_spatialEquiv_le_vnTensorRight he htop h₂⟩

universe u

/-- **Type I factor abstract structure theorem.** A type I factor `N` (a factor with a minimal
projection, acting on a nonzero Hilbert space) is `⋆`-isomorphic to the algebra `B(K)` of all
bounded operators on *some* complex Hilbert space `K`. This is the model-independent form of the
classification of type I factors: `B(K)` for `K = ℓ²(F)` is exactly the type `I_{|F|}` factor, and
`K = H` recovers the full algebra `B(H)` as the type `I` factor `⊤`. The spatial content — that the
isomorphism is implemented by a unitary and that `K` is the multiplicity space of the minimal
projection — is `IsFactor.exists_spatial_tensorDecomposition`; here it is packaged as an abstract
`⋆`-isomorphism, hiding the specific model `K = ℓ²(F)` behind an existential. -/
theorem IsTypeIFactor.exists_starAlgEquiv {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {N : VonNeumannAlgebra H}
    (hN : IsTypeIFactor N) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      Nonempty (N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) := by
  obtain ⟨hFactor, e, he⟩ := hN
  obtain ⟨F, U, hU, -⟩ := hFactor.exists_spatial_tensorDecomposition he
  haveI : CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H)) := he.1.completeSpace_range
  haveI : Nontrivial (LinearMap.range (e : H →ₗ[ℂ] H)) := by
    rw [Submodule.nontrivial_iff_ne_bot, ne_eq, LinearMap.range_eq_bot]
    exact fun h => he.2.2.1 (ContinuousLinearMap.coe_injective
      (h.trans ContinuousLinearMap.coe_zero.symm))
  exact ⟨lp (fun _ : F => ℂ) 2, inferInstance, inferInstance, inferInstance,
    ⟨(conjEquiv U N).trans ((equivOfEq hU).trans HilbertTensor.amplifyLeftStarAlgEquiv.symm)⟩⟩

end VonNeumannAlgebra
