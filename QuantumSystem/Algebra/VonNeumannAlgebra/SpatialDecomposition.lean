module

public import QuantumSystem.Algebra.VonNeumannAlgebra.CoveringFamily
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProductCompletion
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Spatial decomposition: partial-isometry-induced isometries between projection ranges

This file begins the spatial half of the type I factor structure theorem. A partial isometry `v`
with source projection `p = v⋆v` and range projection `q = vv⋆` restricts to a linear isometric
equivalence between the closed subspaces `range p` and `range q`. For a family of projections
each Murray–von Neumann equivalent to a fixed minimal projection `e`, these isometries identify
every summand `range eᵢ` with the multiplicity space `range e`, the first step in building the
spatial isomorphism `H ≅ ℓ²(I) ⊗̂ (eH)`.

## Main results

* `IsPartialIsometry.sourceRangeEquiv` — the isometric equivalence `range (v⋆v) ≃ₗᵢ range (vv⋆)`
  induced by a partial isometry `v`.
* `IsFactor.exists_tensor_decomposition` — the `ℓ²`-sum form `H ≅ ℓ²(F; eH)` of the spatial
  decomposition of a type I factor.
* `IsFactor.exists_tmul_decomposition` — the literal tensor form `H ≅ ℓ²(F) ⊗̂ (eH)`, obtained by
  composing with the tensor bridge `HilbertTensor.lpTensorEquiv`.
-/

@[expose] public section

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section LpCongr

variable {α : Type*} {𝕜 : Type*} [RCLike 𝕜] {G G' : α → Type*}
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  [∀ i, NormedAddCommGroup (G' i)] [∀ i, NormedSpace 𝕜 (G' i)]

/-- A family of isometries preserves `Memℓp`: norms are pointwise unchanged. -/
theorem memℓp_congr_linearIsometryEquiv (e : ∀ i, G i ≃ₗᵢ[𝕜] G' i) {f : ∀ i, G i}
    (hf : Memℓp f 2) : Memℓp (fun i => e i (f i)) 2 := by
  apply Memℓp.of_norm
  have hnorm : (fun i => ‖e i (f i)‖) = fun i => ‖f i‖ := funext fun i => (e i).norm_map (f i)
  rw [hnorm]
  exact hf.norm

/-- A family of linear isometric equivalences `G i ≃ₗᵢ G' i` induces a linear isometric
equivalence between the `ℓ²` sums `lp G 2 ≃ₗᵢ lp G' 2`, applied componentwise. -/
noncomputable def lpCongr (e : ∀ i, G i ≃ₗᵢ[𝕜] G' i) : lp G 2 ≃ₗᵢ[𝕜] lp G' 2 where
  toFun f := ⟨fun i => e i (f i), memℓp_congr_linearIsometryEquiv e (lp.memℓp f)⟩
  invFun g := ⟨fun i => (e i).symm (g i), memℓp_congr_linearIsometryEquiv (fun i => (e i).symm)
    (lp.memℓp g)⟩
  left_inv f := by
    refine Subtype.ext (funext fun i => ?_)
    change (e i).symm (e i (f i)) = f i
    rw [LinearIsometryEquiv.symm_apply_apply]
  right_inv g := by
    refine Subtype.ext (funext fun i => ?_)
    change e i ((e i).symm (g i)) = g i
    rw [LinearIsometryEquiv.apply_symm_apply]
  map_add' x y := by
    refine Subtype.ext (funext fun i => ?_)
    change e i ((x + y) i) = e i (x i) + e i (y i)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    refine Subtype.ext (funext fun i => ?_)
    change e i ((c • f) i) = c • e i (f i)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]
  norm_map' f := by
    have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    refine tsum_congr fun i => ?_
    congr 1
    exact (e i).norm_map (f i)

end LpCongr

namespace IsPartialIsometry

/-- For `x` in the source subspace (`p x = x` where `p = v⋆v`), the map preserves the norm:
`‖v x‖ = ‖x‖`. -/
theorem norm_apply {v : H →L[ℂ] H} {p : H →L[ℂ] H}
    (hsource : star v * v = p) {x : H} (hx : (p : H →L[ℂ] H) x = x) : ‖v x‖ = ‖x‖ := by
  have hinner : (inner ℂ (v x) (v x) : ℂ) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_apply, hsource, hx]
  have h2 : ‖v x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact congrArg RCLike.re hinner
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-- The image of any vector under a partial isometry lands in the range subspace: if `q = v v⋆`
then `q (v x) = v x`. -/
theorem apply_mem_range {v : H →L[ℂ] H} (hv : IsPartialIsometry v) {q : H →L[ℂ] H}
    (hrange : v * star v = q) (x : H) : (q : H →L[ℂ] H) (v x) = v x := by
  rw [← ContinuousLinearMap.mul_apply, ← hrange, hv]

/-- A partial isometry `v` with source projection `star v * v = p` and range projection
`v * star v = q` restricts to a linear isometric equivalence from the source subspace
`range p` onto the range subspace `range q`. -/
noncomputable def sourceRangeEquiv {v : H →L[ℂ] H} (hv : IsPartialIsometry v)
    {p q : H →L[ℂ] H} (hsource : star v * v = p) (hrange : v * star v = q) :
    LinearMap.range (p : H →ₗ[ℂ] H) ≃ₗᵢ[ℂ] LinearMap.range (q : H →ₗ[ℂ] H) := by
  have hpidem : (p : H →L[ℂ] H) * p = p := by
    have := hv.isStarProjection_star_mul_self.isIdempotentElem
    rwa [hsource] at this
  have hqidem : (q : H →L[ℂ] H) * q = q := by
    have := hv.isStarProjection_mul_star_self.isIdempotentElem
    rwa [hrange] at this
  have hsvpi : star v * v * star v = star v := by
    have h : star v * star (star v) * star v = star v := IsPartialIsometry.star hv
    rwa [star_star] at h
  have hfix : ∀ {x : H}, x ∈ LinearMap.range (p : H →ₗ[ℂ] H) → (p : H →L[ℂ] H) x = x := by
    rintro x ⟨z, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.mul_apply, hpidem]
  refine LinearIsometryEquiv.ofSurjective
    { toFun := fun ξ => ⟨v ξ.1, ⟨v ξ.1, by
        rw [ContinuousLinearMap.coe_coe]; exact hv.apply_mem_range hrange ξ.1⟩⟩
      map_add' := fun a b => by apply Subtype.ext; simp
      map_smul' := fun c a => by apply Subtype.ext; simp
      norm_map' := fun ξ => norm_apply hsource (hfix ξ.2) } ?_
  rintro ⟨η, hη⟩
  have hqfix : (q : H →L[ℂ] H) η = η := by
    obtain ⟨z, hz⟩ := hη
    rw [← hz, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.mul_apply, hqidem]
  have hmem : star v η ∈ LinearMap.range (p : H →ₗ[ℂ] H) := by
    refine ⟨star v η, ?_⟩
    rw [ContinuousLinearMap.coe_coe, show (p : H →L[ℂ] H) (star v η) = (p * star v) η from rfl,
      ← hsource, hsvpi]
  refine ⟨⟨star v η, hmem⟩, Subtype.ext ?_⟩
  change v (star v η) = η
  rw [← ContinuousLinearMap.mul_apply, hrange, hqfix]

end IsPartialIsometry

/-- A vector in the range of a star projection is fixed by it: `p x = x`. -/
theorem IsStarProjection.apply_eq_self_of_mem_range {p : H →L[ℂ] H} (hp : IsStarProjection p)
    {x : H} (hx : x ∈ LinearMap.range (p : H →ₗ[ℂ] H)) : (p : H →L[ℂ] H) x = x := by
  obtain ⟨z, rfl⟩ := hx
  rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.mul_apply, hp.isIdempotentElem]

/-- The range of a star projection is closed: it equals the kernel of `1 - p`. -/
theorem IsStarProjection.isClosed_range {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    IsClosed (LinearMap.range (p : H →ₗ[ℂ] H) : Set H) := by
  have hker : LinearMap.range (p : H →ₗ[ℂ] H)
      = LinearMap.ker ((1 - p : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
    constructor
    · rintro ⟨z, rfl⟩
      rw [← ContinuousLinearMap.mul_apply, hp.isIdempotentElem]
    · intro hx
      exact ⟨x, hx.symm⟩
  rw [hker]
  exact (1 - p).isClosed_ker

/-- The range of a star projection, as a closed subspace, is complete. -/
theorem IsStarProjection.completeSpace_range {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    CompleteSpace (LinearMap.range (p : H →ₗ[ℂ] H)) :=
  completeSpace_coe_iff_isComplete.mpr hp.isClosed_range.isComplete

/-- The inverse of the partial-isometry-induced equivalence acts as `v⋆`: for `η` in the range
subspace, `(sourceRangeEquiv v).symm η = v⋆ η`. -/
theorem IsPartialIsometry.coe_sourceRangeEquiv_symm {v : H →L[ℂ] H} (hv : IsPartialIsometry v)
    {p q : H →L[ℂ] H} (hsource : star v * v = p) (hrange : v * star v = q)
    (η : LinearMap.range (q : H →ₗ[ℂ] H)) :
    ((hv.sourceRangeEquiv hsource hrange).symm η : H) = star v (η : H) := by
  have hsvpi : star v * v * star v = star v := by
    have h : star v * star (star v) * star v = star v := IsPartialIsometry.star hv
    rwa [star_star] at h
  have hq : IsStarProjection q := by rw [← hrange]; exact hv.isStarProjection_mul_star_self
  have hqfix : (q : H →L[ℂ] H) (η : H) = (η : H) := hq.apply_eq_self_of_mem_range η.2
  have hmem : star v (η : H) ∈ LinearMap.range (p : H →ₗ[ℂ] H) :=
    ⟨star v (η : H), by
      rw [ContinuousLinearMap.coe_coe, ← hsource, ← ContinuousLinearMap.mul_apply, hsvpi]⟩
  have hG : (hv.sourceRangeEquiv hsource hrange) ⟨star v (η : H), hmem⟩ = η := by
    apply Subtype.ext
    change v (star v (η : H)) = (η : H)
    rw [← ContinuousLinearMap.mul_apply, hrange, hqfix]
  have hsymm : (hv.sourceRangeEquiv hsource hrange).symm η = ⟨star v (η : H), hmem⟩ :=
    (hv.sourceRangeEquiv hsource hrange).injective (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact hG.symm)
  rw [hsymm]

namespace VonNeumannAlgebra

/-- A covering orthogonal family of star projections (each in `OrthEquivFam`) realises `H` as the
internal Hilbert sum of the ranges. -/
theorem OrthEquivFam.isHilbertSum {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤) :
    IsHilbertSum ℂ (fun i : F => LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H))
      (fun i => (LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ) := by
  haveI : ∀ i : F, CompleteSpace (LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)) :=
    fun i => (hF.1 i.1 i.2).1.completeSpace_range
  refine IsHilbertSum.mkInternal _ ?_ ?_
  · rintro ⟨pi, hpi⟩ ⟨pj, hpj⟩ hij ⟨v, hv⟩ ⟨w, hw⟩
    have hne : pi ≠ pj := fun h => hij (Subtype.ext h)
    have h0 : (pi : H →L[ℂ] H) * pj = 0 := hF.2 hpi hpj hne
    have hvf : (pi : H →L[ℂ] H) v = v := (hF.1 pi hpi).1.apply_eq_self_of_mem_range hv
    have hwf : (pj : H →L[ℂ] H) w = w := (hF.1 pj hpj).1.apply_eq_self_of_mem_range hw
    have e1 : (inner ℂ v w : ℂ) = inner ℂ ((pi : H →L[ℂ] H) v) ((pj : H →L[ℂ] H) w) := by
      rw [hvf, hwf]
    change (inner ℂ v w : ℂ) = 0
    rw [e1, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      (hF.1 pi hpi).1.isSelfAdjoint.star_eq,
      show (pi : H →L[ℂ] H) ((pj : H →L[ℂ] H) w) = ((pi : H →L[ℂ] H) * pj) w from rfl, h0]
    simp
  · rw [← htop]
    refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
    rintro y ⟨f, hf, x, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨x, rfl⟩

/-- **Spatial Hilbert-sum isomorphism.** A covering orthogonal family of `e`-equivalent
projections gives a linear isometric equivalence of `H` with the `ℓ²` sum of the ranges. -/
noncomputable def OrthEquivFam.hilbertSumEquiv {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤) :
    H ≃ₗᵢ[ℂ] lp (fun i : F => LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)) 2 :=
  (hF.isHilbertSum htop).linearIsometryEquiv

/-- **Tensor-product decomposition of the Hilbert space.** A covering orthogonal family of
projections each Murray–von Neumann equivalent to `e` identifies `H` isometrically with
`ℓ²(F; eH)` — the `ℓ²` sum, indexed by `F`, of copies of the fibre `range e` (which is the
*multiplicity space* when `e` is minimal, as in `exists_tensor_decomposition`; minimality is not
assumed in this lemma). This is the spatial content of the type I factor structure theorem:
`H ≅ ℓ²(F) ⊗̂ (eH)`. The equivalence
is built from the Hilbert-sum decomposition `H ≅ ⊕ᵢ range eᵢ` and the partial-isometry-induced
isometries `range eᵢ ≅ range e`. -/
noncomputable def OrthEquivFam.multiplicityEquiv {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤) :
    H ≃ₗᵢ[ℂ] lp (fun _ : F => LinearMap.range (e : H →ₗ[ℂ] H)) 2 :=
  (hF.hilbertSumEquiv htop).trans (lpCongr (fun i =>
    (IsPartialIsometry.sourceRangeEquiv
      (hF.1 i.1 i.2).2.2.2.choose_spec.2.1
      (hF.1 i.1 i.2).2.2.2.choose_spec.2.2.1
      (hF.1 i.1 i.2).2.2.2.choose_spec.2.2.2).symm))

/-- The `i`-th Hilbert-sum coordinate of `y`, embedded back into `H`, is the orthogonal projection
`(↑i) y`. This identifies the abstract Hilbert-sum decomposition with the explicit family of range
projections. -/
theorem OrthEquivFam.coe_hilbertSumEquiv_apply {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F)
    (htop : (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤)
    (y : H) (i : F) :
    ((hF.hilbertSumEquiv htop y i : LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)) : H)
      = (i : H →L[ℂ] H) y := by
  have hHS := hF.isHilbertSum htop
  have hdecomp : HasSum
      (fun j : F => (LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
        ((hHS.linearIsometryEquiv y) j)) y := by
    have h := hHS.hasSum_linearIsometryEquiv_symm (hHS.linearIsometryEquiv y)
    rwa [LinearIsometryEquiv.symm_apply_apply] at h
  have happ := hdecomp.mapL (i : H →L[ℂ] H)
  have hii : (i : H →L[ℂ] H)
      ((LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) i))
      = (LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) i) :=
    (hF.1 i.1 i.2).1.apply_eq_self_of_mem_range (Submodule.coe_mem _)
  have hsingle : HasSum
      (fun j : F => (i : H →L[ℂ] H)
        ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) j)))
      ((i : H →L[ℂ] H)
        ((LinearMap.range ((i : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) i))) :=
    hasSum_single i (fun j hj => by
      have hjfix : (j : H →L[ℂ] H)
          ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) j))
          = (LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
              ((hHS.linearIsometryEquiv y) j) :=
        (hF.1 j.1 j.2).1.apply_eq_self_of_mem_range (Submodule.coe_mem _)
      have hij0 : (i : H →L[ℂ] H) * (j : H →L[ℂ] H) = 0 :=
        hF.2 i.2 j.2 (fun h => hj (Subtype.ext h).symm)
      calc (i : H →L[ℂ] H)
            ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ ((hHS.linearIsometryEquiv y) j))
          = (i : H →L[ℂ] H) ((j : H →L[ℂ] H)
              ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
                ((hHS.linearIsometryEquiv y) j))) := by rw [hjfix]
        _ = ((i : H →L[ℂ] H) * (j : H →L[ℂ] H))
              ((LinearMap.range ((j : H →L[ℂ] H) : H →ₗ[ℂ] H)).subtypeₗᵢ
                ((hHS.linearIsometryEquiv y) j)) := rfl
        _ = 0 := by rw [hij0]; rfl)
  exact ((happ.unique hsingle).trans hii).symm

/-- The minimal projection `e` of a type I factor is the multiplicity space: a type I factor with
minimal projection `e` acts on a Hilbert space isometric to the `ℓ²` sum `ℓ²(F; eH)` of copies of
`eH = range e`, indexed by a maximal orthogonal family `F` of minimal projections equivalent to
`e`. Composing with the tensor bridge turns this `ℓ²` sum into the literal tensor product
`H ≅ ℓ²(F) ⊗̂ eH`; see `exists_tmul_decomposition`. -/
theorem IsFactor.exists_tensor_decomposition [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e) :
    ∃ (F : Set (H →L[ℂ] H)),
      Nonempty (H ≃ₗᵢ[ℂ] lp (fun _ : F => LinearMap.range (e : H →ₗ[ℂ] H)) 2) := by
  obtain ⟨F, hF, htop⟩ := hN.exists_orthEquivFam_top he
  exact ⟨F, ⟨hF.multiplicityEquiv htop⟩⟩

/-- **Tensor-product decomposition (literal form).** A type I factor `N ⊆ B(H)` with minimal
projection `e` acts on a Hilbert space isometric to the completed Hilbert tensor product
`ℓ²(F) ⊗̂ (eH)`, where `F` is a maximal orthogonal family of minimal projections equivalent to `e`
and `eH = range e` is the multiplicity space. This is the literal `H ≅ ℓ²(F) ⊗̂ eH` form of the
type I structure theorem, obtained from `exists_tensor_decomposition` by composing with the tensor
bridge `HilbertTensor.lpTensorEquiv`. -/
theorem IsFactor.exists_tmul_decomposition [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e) :
    ∃ (F : Set (H →L[ℂ] H)),
      Nonempty (H ≃ₗᵢ[ℂ]
        HilbertTensor (lp (fun _ : F => ℂ) 2) (LinearMap.range (e : H →ₗ[ℂ] H))) := by
  obtain ⟨F, hF, htop⟩ := hN.exists_orthEquivFam_top he
  haveI : CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H)) := he.1.completeSpace_range
  haveI : DecidableEq (↥F) := Classical.decEq _
  exact ⟨F, ⟨(hF.multiplicityEquiv htop).trans
    (HilbertTensor.lpTensorEquiv (ι := F) (K := LinearMap.range (e : H →ₗ[ℂ] H)))⟩⟩

end VonNeumannAlgebra
