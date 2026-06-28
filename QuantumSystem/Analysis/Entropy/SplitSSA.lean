module

public import QuantumSystem.Analysis.Entropy.SplitTransport
public import QuantumSystem.Analysis.Entropy.StrongSubadditivityProduct

/-!
# Strong subadditivity on a split net

The **strong subadditivity** of the von Neumann entropy, stated representation-free on the abstract
operator-algebraic split net `LocalNet.Split`, assembled from:

* the **data-processing inequality** `relativeEntropy_restrict_le` (the analytic engine);
* the **tensor commutant theorem** `LinearMap.exists_map_one_of_commute_map_id`, which makes the
  partial trace depend only on the subsystem traced out (factorisation uniqueness);
* **basis-independence of the von Neumann entropy** `vonNeumannEntropy_toDensityMatrixBasis`,
  which lets us read marginals in a tensor-factorised orthonormal basis;
* the matrix-level `DensityMatrix.vonNeumannEntropy_SSA_product`.

The first brick is the **partial-trace correspondence**: in the orthonormal basis pulled back from a
tensor factorisation, the matrix partial trace `Matrix.traceRight` realises the operator partial
trace `LinearMap.partialTrace`.
-/

@[expose] public section

open scoped TensorProduct ComplexOrder MatrixOrder

namespace LinearMap

variable {ℋ A B : Type*}
  [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

/-- **Partial-trace correspondence.** Read in the orthonormal basis of `ℋ` pulled back from the
tensor product basis `bA ⊗ bB` along a unitary factorisation `e : ℋ ≃ₗᵢ A ⊗ B`, the matrix partial
trace over the `B`-index (`Matrix.traceRight`) realises the operator partial trace
`LinearMap.partialTrace e`. -/
theorem traceRight_toMatrixOrthonormal (e : ℋ ≃ₗᵢ[ℂ] (A ⊗[ℂ] B))
    {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (bA : OrthonormalBasis κ ℂ A) (bB : OrthonormalBasis ν ℂ B) (T : Module.End ℂ ℋ) :
    Matrix.traceRight (LinearMap.toMatrixOrthonormal ((bA.tensorProduct bB).map e.symm) T)
      = LinearMap.toMatrixOrthonormal bA (LinearMap.partialTrace e.toLinearEquiv T) := by
  ext i j
  rw [Matrix.traceRight_apply, LinearMap.toMatrixOrthonormal_apply_apply, partialTrace_apply,
    ← inner_conj_symm (𝕜 := ℂ), TensorProduct.inner_partialTraceRight bB, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.toMatrixOrthonormal_apply_apply, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply, AlgEquiv.apply_symm_apply,
    LinearEquiv.conjAlgEquiv_apply_apply,
    show (e.toLinearEquiv) (T (e.toLinearEquiv.symm (bA j ⊗ₜ[ℂ] bB k)))
        = e (T (e.symm (bA j ⊗ₜ[ℂ] bB k))) from rfl,
    ← e.inner_map_map (e.symm (bA i ⊗ₜ[ℂ] bB k)) (T (e.symm (bA j ⊗ₜ[ℂ] bB k))),
    e.apply_symm_apply]
  exact (inner_conj_symm _ _).symm

/-- **Partial-trace correspondence, left factor.** Tracing out the *first* index (`Matrix.traceLeft`)
of the matrix in the basis pulled back from `bA ⊗ bB` along `e : ℋ ≃ₗᵢ A ⊗ B` realises the operator
partial trace along `e` post-composed with the tensor swap — i.e. tracing out the `A`-factor and
retaining `B`. This reads the `A`-marginal (`ptLeft`) of the tensor-factorised density matrix. -/
theorem traceLeft_toMatrixOrthonormal (e : ℋ ≃ₗᵢ[ℂ] (A ⊗[ℂ] B))
    {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (bA : OrthonormalBasis κ ℂ A) (bB : OrthonormalBasis ν ℂ B) (T : Module.End ℂ ℋ) :
    Matrix.traceLeft (LinearMap.toMatrixOrthonormal ((bA.tensorProduct bB).map e.symm) T)
      = LinearMap.toMatrixOrthonormal bB
          (LinearMap.partialTrace (e.trans (TensorProduct.commIsometry ℂ A B)).toLinearEquiv T) := by
  have hswap : ((bA.tensorProduct bB).map e.symm).reindex (Equiv.prodComm κ ν)
      = (bB.tensorProduct bA).map (e.trans (TensorProduct.commIsometry ℂ A B)).symm := by
    apply DFunLike.ext
    rintro ⟨j, i⟩
    simp only [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
      OrthonormalBasis.tensorProduct_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
      Prod.swap_prod_mk, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
      TensorProduct.commIsometry_symm, TensorProduct.commIsometry_apply,
      TensorProduct.comm_tmul]
  rw [Matrix.traceLeft_eq_traceRight_prodComm, ← LinearMap.toMatrixOrthonormal_reindex, hswap,
    LinearMap.traceRight_toMatrixOrthonormal]

end LinearMap

/-! ### Conjugation under a tensor congruence -/

/-- Conjugating an ampliation `N ⊗ M` by a tensor congruence `congr f g` distributes:
`(congr f g)-conj (N ⊗ M) = (f-conj N) ⊗ (g-conj M)`. -/
theorem TensorProduct.congr_conjAlgEquiv_map {𝕜 E F G K : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    [AddCommGroup G] [Module 𝕜 G] [AddCommGroup K] [Module 𝕜 K]
    (f : E ≃ₗ[𝕜] F) (g : G ≃ₗ[𝕜] K) (N : Module.End 𝕜 E) (M : Module.End 𝕜 G) :
    (TensorProduct.congr f g).conjAlgEquiv 𝕜 (TensorProduct.map N M)
      = TensorProduct.map (f.conjAlgEquiv 𝕜 N) (g.conjAlgEquiv 𝕜 M) := by
  rw [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conjAlgEquiv_apply,
    LinearEquiv.conjAlgEquiv_apply]
  apply TensorProduct.ext'
  intro f' k'
  simp [TensorProduct.map_tmul]

/-- Conjugation by a composite equivalence is the composite of conjugations. -/
theorem LinearEquiv.conjAlgEquiv_trans {𝕜 M₁ M₂ M₃ : Type*} [Field 𝕜]
    [AddCommGroup M₁] [Module 𝕜 M₁] [AddCommGroup M₂] [Module 𝕜 M₂]
    [AddCommGroup M₃] [Module 𝕜 M₃] (e : M₁ ≃ₗ[𝕜] M₂) (f : M₂ ≃ₗ[𝕜] M₃)
    (T : Module.End 𝕜 M₁) :
    (e.trans f).conjAlgEquiv 𝕜 T = f.conjAlgEquiv 𝕜 (e.conjAlgEquiv 𝕜 T) := by
  rw [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conjAlgEquiv_apply,
    LinearEquiv.conjAlgEquiv_apply]
  ext x
  simp [LinearMap.comp_assoc]

/-- Conjugating an ampliation by the tensor commutativity isomorphism swaps the two factors. -/
theorem TensorProduct.comm_conjAlgEquiv_map {𝕜 A B : Type*} [Field 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B] [Module 𝕜 B]
    (f : Module.End 𝕜 A) (g : Module.End 𝕜 B) :
    (TensorProduct.comm 𝕜 A B).conjAlgEquiv 𝕜 (TensorProduct.map f g)
      = TensorProduct.map g f := by
  rw [LinearEquiv.conjAlgEquiv_apply]
  apply TensorProduct.ext'
  intro b a
  simp [TensorProduct.map_tmul]

/-- Conjugating a nested ampliation `(f ⊗ g) ⊗ h` by the tensor associativity isomorphism
reassociates it to `f ⊗ (g ⊗ h)`. -/
theorem TensorProduct.assoc_conjAlgEquiv_map {𝕜 A B C : Type*} [Field 𝕜]
    [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B] [Module 𝕜 B] [AddCommGroup C] [Module 𝕜 C]
    (f : Module.End 𝕜 A) (g : Module.End 𝕜 B) (h : Module.End 𝕜 C) :
    (TensorProduct.assoc 𝕜 A B C).conjAlgEquiv 𝕜
        (TensorProduct.map (TensorProduct.map f g) h)
      = TensorProduct.map f (TensorProduct.map g h) := by
  rw [LinearEquiv.conjAlgEquiv_apply]
  apply TensorProduct.ext'
  intro a bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp [TensorProduct.map_tmul]
  | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]

/-! ### Naturality of the partial trace under relabelling the retained factor -/

section Naturality

variable {R H K K' D : Type*} [Field R]
  [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Free R K]
  [AddCommGroup K'] [Module R K'] [Module.Finite R K'] [Module.Free R K']
  [AddCommGroup D] [Module R D] [Module.Finite R D] [Module.Free R D]

omit [Module.Finite R K] [Module.Free R K] [Module.Finite R K'] [Module.Free R K']
  [Module.Finite R D] [Module.Free R D] in
/-- `partialTraceRight` is natural under relabelling the retained (first) factor by `V`: it carries
the ampliation `V ⊗ 1` (here `LinearEquiv.conj V` on the first factor of the operator tensor) through
to conjugation by `V` of the result. -/
theorem TensorProduct.partialTraceRight_map_conj (V : K ≃ₗ[R] K')
    (S : Module.End R K ⊗[R] Module.End R D) :
    TensorProduct.partialTraceRight
        (TensorProduct.map (LinearEquiv.conj V).toLinearMap LinearMap.id S)
      = (LinearEquiv.conj V) (TensorProduct.partialTraceRight S) := by
  induction S using TensorProduct.induction_on with
  | zero => simp
  | tmul L Rr => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.partialTraceRight_tmul, map_smul, LinearEquiv.coe_coe]
  | add S₁ S₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- Naturality of `endTensorEndAlgEquiv` under conjugation by `congr V 1`: it intertwines the
operator-level conjugation by `V ⊗ 1` with the tensor-level `conj V ⊗ id`. -/
theorem TensorProduct.endTensorEndAlgEquiv_symm_conjAlgEquiv_congr (V : K ≃ₗ[R] K')
    (S : Module.End R K ⊗[R] Module.End R D) :
    (TensorProduct.endTensorEndAlgEquiv).symm
        ((TensorProduct.congr V (LinearEquiv.refl R D)).conjAlgEquiv R
          (TensorProduct.endTensorEndAlgEquiv S))
      = TensorProduct.map (LinearEquiv.conj V).toLinearMap LinearMap.id S := by
  induction S using TensorProduct.induction_on with
  | zero => simp
  | tmul L Rr =>
    rw [TensorProduct.endTensorEndAlgEquiv_tmul, LinearEquiv.conjAlgEquiv_apply,
      show (TensorProduct.congr V (LinearEquiv.refl R D)).toLinearMap
        = TensorProduct.map V.toLinearMap LinearMap.id from by ext; simp,
      show ((TensorProduct.congr V (LinearEquiv.refl R D)).symm.toLinearMap)
        = TensorProduct.map V.symm.toLinearMap LinearMap.id from by
          ext; simp [TensorProduct.congr_symm],
      ← TensorProduct.map_comp, ← TensorProduct.map_comp, TensorProduct.map_tmul, LinearMap.id_apply,
      AlgEquiv.symm_apply_eq, TensorProduct.endTensorEndAlgEquiv_tmul]
    rfl
  | add S₁ S₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **Naturality of the partial trace.** Composing the factorisation `e : H ≃ₗ K ⊗ D` with a
relabelling `V ⊗ 1` of the retained factor conjugates the partial trace by `V`:
`Tr_D ((V ⊗ 1) ∘ e) = V ∘ (Tr_D e) ∘ V⁻¹`. Two factorisations differing by `V ⊗ 1` give unitarily
equivalent marginals — the operator content of factorisation uniqueness. -/
theorem LinearMap.partialTrace_congr_conj (V : K ≃ₗ[R] K') (e : H ≃ₗ[R] K ⊗[R] D)
    (T : Module.End R H) :
    LinearMap.partialTrace (e ≪≫ₗ TensorProduct.congr V (LinearEquiv.refl R D)) T
      = (LinearEquiv.conj V) (LinearMap.partialTrace e T) := by
  rw [LinearMap.partialTrace_apply, LinearMap.partialTrace_apply]
  have hcomp : (e ≪≫ₗ TensorProduct.congr V (LinearEquiv.refl R D)).conjAlgEquiv R T
      = (TensorProduct.congr V (LinearEquiv.refl R D)).conjAlgEquiv R (e.conjAlgEquiv R T) := by
    rw [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conjAlgEquiv_apply,
      LinearEquiv.conjAlgEquiv_apply]
    rfl
  rw [hcomp, ← (TensorProduct.endTensorEndAlgEquiv).apply_symm_apply (e.conjAlgEquiv R T),
    TensorProduct.endTensorEndAlgEquiv_symm_conjAlgEquiv_congr, TensorProduct.partialTraceRight_map_conj,
    AlgEquiv.symm_apply_apply]

/-- **The partial trace is invariant under a unitary relabelling of the traced-out factor.**
Composing `e : H ≃ₗ K ⊗ D` with `congr 1 U` (identity on the retained factor `K`, an isomorphism `U`
on the traced factor `D ≃ D'`) leaves the partial trace unchanged — the trace of the traced factor
is conjugation-invariant. This lets the `castIso`-relabelled factorisation `bcDirect` share its
partial trace with the canonical `BC`-marginal `restrict (decompᵢ (sdiff))`. -/
theorem LinearMap.partialTrace_congr_right_id (e : H ≃ₗ[R] K ⊗[R] D) (U : D ≃ₗ[R] K')
    (T : Module.End R H) :
    LinearMap.partialTrace (e ≪≫ₗ TensorProduct.congr (LinearEquiv.refl R K) U) T
      = LinearMap.partialTrace e T := by
  rw [LinearMap.partialTrace_apply, LinearMap.partialTrace_apply,
    LinearEquiv.conjAlgEquiv_trans e (TensorProduct.congr (LinearEquiv.refl R K) U) T,
    ← (TensorProduct.endTensorEndAlgEquiv (R := R) (M := K) (N := D)).apply_symm_apply
        (e.conjAlgEquiv R T)]
  generalize (TensorProduct.endTensorEndAlgEquiv (R := R) (M := K) (N := D)).symm
      (e.conjAlgEquiv R T) = W
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul Y Z =>
    rw [AlgEquiv.symm_apply_apply, TensorProduct.partialTraceRight_tmul,
      TensorProduct.endTensorEndAlgEquiv_tmul, TensorProduct.congr_conjAlgEquiv_map,
      ← TensorProduct.endTensorEndAlgEquiv_tmul, AlgEquiv.symm_apply_apply,
      TensorProduct.partialTraceRight_tmul,
      show U.conjAlgEquiv R Z = U.conj Z from rfl, LinearMap.trace_conj']
    congr 1
  | add W₁ W₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end Naturality

/-! ### Factorisation uniqueness: extracting the relabelling isometry -/

section FactorizationUniqueness

variable {K K' D : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [FiniteDimensional ℂ K']
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [FiniteDimensional ℂ D]

omit [FiniteDimensional ℂ K] in
/-- A unitary `Φ : K ⊗ D ≃ₗᵢ K' ⊗ D` whose underlying map is an ampliation `V ⊗ 1` of a linear map
`V_lin` upgrades that `V_lin` to a **unitary** `V : K ≃ₗᵢ K'`: it is automatically an
isometric isomorphism. (`Φ = V ⊗ 1` with `Φ` unitary forces `V` unitary.) -/
theorem exists_isometryEquiv_of_toLinearMap_eq_map [Nontrivial D]
    (Φ : (K ⊗[ℂ] D) ≃ₗᵢ[ℂ] (K' ⊗[ℂ] D)) (V_lin : K →ₗ[ℂ] K')
    (hΦ : Φ.toLinearEquiv.toLinearMap = TensorProduct.map V_lin LinearMap.id) :
    ∃ V : K ≃ₗᵢ[ℂ] K', V.toLinearEquiv.toLinearMap = V_lin := by
  obtain ⟨d₀, hd₀⟩ := exists_ne (0 : D)
  have hdd : (inner ℂ d₀ d₀ : ℂ) ≠ 0 := by simp only [ne_eq, inner_self_eq_zero]; exact hd₀
  have hiso : ∀ k₁ k₂ : K, (inner ℂ (V_lin k₁) (V_lin k₂) : ℂ) = inner ℂ k₁ k₂ := by
    intro k₁ k₂
    have h1 : (inner ℂ (Φ (k₁ ⊗ₜ[ℂ] d₀)) (Φ (k₂ ⊗ₜ[ℂ] d₀)) : ℂ)
        = inner ℂ (k₁ ⊗ₜ[ℂ] d₀) (k₂ ⊗ₜ[ℂ] d₀) := Φ.inner_map_map _ _
    rw [show Φ (k₁ ⊗ₜ[ℂ] d₀) = V_lin k₁ ⊗ₜ[ℂ] d₀ by
        rw [show Φ (k₁ ⊗ₜ[ℂ] d₀) = Φ.toLinearEquiv.toLinearMap (k₁ ⊗ₜ[ℂ] d₀) from rfl, hΦ]; simp,
      show Φ (k₂ ⊗ₜ[ℂ] d₀) = V_lin k₂ ⊗ₜ[ℂ] d₀ by
        rw [show Φ (k₂ ⊗ₜ[ℂ] d₀) = Φ.toLinearEquiv.toLinearMap (k₂ ⊗ₜ[ℂ] d₀) from rfl, hΦ]; simp,
      TensorProduct.inner_tmul, TensorProduct.inner_tmul] at h1
    exact mul_right_cancel₀ hdd h1
  have hinj : Function.Injective V_lin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro k hk
    have := hiso k k
    rw [hk] at this; simp only [inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  have hrank : Module.finrank ℂ K = Module.finrank ℂ K' := by
    have := Φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct] at this
    exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos this
  have hsurj : Function.Surjective V_lin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj, hrank]
  let Ve : K ≃ₗ[ℂ] K' := LinearEquiv.ofBijective V_lin ⟨hinj, hsurj⟩
  refine ⟨{ Ve with norm_map' := fun k => ?_ }, rfl⟩
  rw [← Real.sqrt_sq (norm_nonneg (Ve k)), ← Real.sqrt_sq (norm_nonneg k)]
  congr 1
  rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
  exact congrArg Complex.re (hiso k k)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

omit [FiniteDimensional ℂ H] in
/-- **Factorisation uniqueness.** Two unitary factorisations `e₁ : H ≃ₗᵢ K ⊗ D`,
`e₂ : H ≃ₗᵢ K' ⊗ D` that implement the *same* action of `End D` on `H` (`hcomm`: the transition
`e₁.symm.trans e₂` commutes with every `1 ⊗ f`) have partial traces over `D` that agree up to a
unitary `V : K ≃ₗᵢ K'`. The marginal of a state over a subsystem thus depends only on the subsystem,
not on the chosen factorisation of its complement. -/
theorem factorization_uniqueness [Nontrivial D]
    (e₁ : H ≃ₗᵢ[ℂ] (K ⊗[ℂ] D)) (e₂ : H ≃ₗᵢ[ℂ] (K' ⊗[ℂ] D))
    (hcomm : ∀ f : Module.End ℂ D,
      (e₁.symm.trans e₂).toLinearEquiv.toLinearMap ∘ₗ TensorProduct.map LinearMap.id f
        = TensorProduct.map LinearMap.id f ∘ₗ (e₁.symm.trans e₂).toLinearEquiv.toLinearMap)
    (T : Module.End ℂ H) :
    ∃ V : K ≃ₗᵢ[ℂ] K',
      LinearMap.partialTrace e₂.toLinearEquiv T
        = (LinearEquiv.conj V.toLinearEquiv) (LinearMap.partialTrace e₁.toLinearEquiv T) := by
  set Φ : (K ⊗[ℂ] D) ≃ₗᵢ[ℂ] (K' ⊗[ℂ] D) := e₁.symm.trans e₂ with hΦdef
  have hrank : Module.finrank ℂ K' = Module.finrank ℂ K := by
    have := Φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct] at this
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos this).symm
  obtain ⟨W₀⟩ :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ℂ) (M := K') (M' := K) hrank
  have hcomm2 : ∀ f : Module.End ℂ D,
      (TensorProduct.map W₀.toLinearMap LinearMap.id ∘ₗ Φ.toLinearEquiv.toLinearMap)
          ∘ₗ TensorProduct.map LinearMap.id f
        = TensorProduct.map LinearMap.id f
          ∘ₗ (TensorProduct.map W₀.toLinearMap LinearMap.id ∘ₗ Φ.toLinearEquiv.toLinearMap) := by
    intro f
    rw [LinearMap.comp_assoc, hcomm f, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]; simp
  obtain ⟨g, hg⟩ := LinearMap.exists_map_id_of_commute_map_one
    (TensorProduct.map W₀.toLinearMap LinearMap.id ∘ₗ Φ.toLinearEquiv.toLinearMap) hcomm2
  have hVlin : Φ.toLinearEquiv.toLinearMap
      = TensorProduct.map (W₀.symm.toLinearMap ∘ₗ g) LinearMap.id := by
    have h2 : Φ.toLinearEquiv.toLinearMap = TensorProduct.map W₀.symm.toLinearMap LinearMap.id ∘ₗ
        (TensorProduct.map W₀.toLinearMap LinearMap.id ∘ₗ Φ.toLinearEquiv.toLinearMap) := by
      rw [← LinearMap.comp_assoc, ← TensorProduct.map_comp]; simp
    rw [h2, hg, ← TensorProduct.map_comp]; simp
  obtain ⟨V, hV⟩ := exists_isometryEquiv_of_toLinearMap_eq_map Φ _ hVlin
  refine ⟨V, ?_⟩
  have hΦeq : Φ.toLinearEquiv = TensorProduct.congr V.toLinearEquiv (LinearEquiv.refl ℂ D) := by
    apply LinearEquiv.toLinearMap_injective
    rw [hVlin, ← hV]; ext; simp
  have he₂ : e₂.toLinearEquiv = e₁.toLinearEquiv ≪≫ₗ Φ.toLinearEquiv := by
    rw [hΦdef]; ext x; simp
  rw [he₂, hΦeq, LinearMap.partialTrace_congr_conj]

/-- Conjugating an operator by a unitary `V : K ≃ₗᵢ K'` and reading it in the `V`-image of an
orthonormal basis gives the *same matrix* as the original in the original basis. Hence the matrix —
and its von Neumann entropy — is unchanged by `conj V`. -/
theorem toMatrixOrthonormal_conj_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : K ≃ₗᵢ[ℂ] K') (b : OrthonormalBasis ι ℂ K) (X : Module.End ℂ K) :
    LinearMap.toMatrixOrthonormal (b.map V) (LinearEquiv.conj V.toLinearEquiv X)
      = LinearMap.toMatrixOrthonormal b X := by
  ext i j
  rw [LinearMap.toMatrixOrthonormal_apply_apply, LinearMap.toMatrixOrthonormal_apply_apply,
    OrthonormalBasis.map_apply, OrthonormalBasis.map_apply, LinearEquiv.conj_apply_apply]
  simp only [LinearIsometryEquiv.coe_toLinearEquiv]
  rw [LinearIsometryEquiv.inner_map_map]
  simp

end FactorizationUniqueness

/-! ### Reindexing the density matrix of a state -/

namespace LocalNet.Split

variable {sites : Type*} [DecidableEq sites] {N : LocalNet sites} {ℋ : Finset sites → Type*}
  [∀ Λ, NormedAddCommGroup (ℋ Λ)] [∀ Λ, InnerProductSpace ℂ (ℋ Λ)]
  [∀ Λ, FiniteDimensional ℂ (ℋ Λ)]
  (S : Split N ℋ)

/-- Reindexing the orthonormal basis and then transporting the density matrix back along the same
equivalence is the identity: `(toDensityMatrixBasis (b.reindex e) hρ).mapEquiv e =
toDensityMatrixBasis b hρ`. Used to align the tensor-factorised basis with the `A × B × C`
positional index of `vonNeumannEntropy_SSA_product`. -/
theorem toDensityMatrixBasis_reindex_mapEquiv {Λ : Finset sites} {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : OrthonormalBasis ι ℂ (ℋ Λ)) (e : ι ≃ ι') {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    (S.toDensityMatrixBasis (b.reindex e) hρ).mapEquiv e = S.toDensityMatrixBasis b hρ := by
  apply DensityMatrix.ext
  rw [DensityMatrix.mapEquiv_toMatrix, S.toDensityMatrixBasis_toMatrix,
    S.toDensityMatrixBasis_toMatrix, S.toMatrixBasis_apply, S.toMatrixBasis_apply,
    LinearMap.toMatrixOrthonormal_reindex]
  ext a b'
  simp [Matrix.submatrix_apply, Matrix.reindex_apply]

/-- The canonical unitary transport `ℋ s ≃ₗᵢ ℋ t` along a propositional equality of regions
`s = t`. (Both action spaces are literally the same once `s = t` is substituted.) -/
noncomputable def castEquiv {s t : Finset sites} (hst : s = t) : ℋ s ≃ₗᵢ[ℂ] ℋ t := by
  rw [hst]; exact LinearIsometryEquiv.refl ℂ (ℋ t)

/-- **The action is natural under `castEquiv`.** Transporting the operator `act s y` along the
region equality `s = t` (conjugating by `castEquiv`) yields `act t` of the transported operand.
This is the spatial half of the dependent-type coherence between a region and a propositionally
equal one, used to align the `act_incl_compl` action on `ΛABC ∖ (ΛABC ∖ ΛA)` with `act ΛA`. -/
theorem castEquiv_conjAlgEquiv_act {s t : Finset sites} (hst : s = t) (x : N.algebra t) :
    (castEquiv (ℋ := ℋ) hst).conjAlgEquiv ℂ (S.act s (hst.symm ▸ x)) = S.act t x := by
  subst hst
  simp only [castEquiv, eq_mpr_eq_cast, cast_eq]
  rfl

/-- The unitary identification `ℋ (ΛABC ∖ (ΛABC ∖ ΛA)) ≃ₗᵢ ℋ ΛA`, transporting the
complement-of-complement action space to the original sub-region's. Used to match the traced factor
of `decompᵢ` for the `BC` marginal (`ΛABC ∖ ΛA`) with `ΛA` in `factorization_uniqueness`. -/
noncomputable def castIso {ΛA ΛABC : Finset sites} (h : ΛA ⊆ ΛABC) :
    ℋ (ΛABC \ (ΛABC \ ΛA)) ≃ₗᵢ[ℂ] ℋ ΛA :=
  castEquiv (ℋ := ℋ) (by rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr h])

/-- **The `A`-action through the nested factorisation `W`.** Reorganising `ℋ ΛABC` as
`(ℋ ΛA ⊗ ℋ (ΛAB ∖ ΛA)) ⊗ ℋ (ΛABC ∖ ΛAB)` (the unitary `W`), the embedded sub-region operator
`act ΛABC (incl x)` becomes the leftmost ampliation `(x ⊗ 1) ⊗ 1`. This pins the `A`-action in the
`(A ⊗ B) ⊗ C` picture and is the input to factorisation uniqueness for the `BC` marginal. -/
theorem wReorg_conjAlgEquiv_act_incl {ΛA ΛAB ΛABC : Finset sites} (h_A : ΛA ⊆ ΛAB)
    (h_AB : ΛAB ⊆ ΛABC) (x : N.algebra ΛA) :
    ((S.decompᵢ h_AB).trans
        (TensorProduct.congrIsometry (S.decompᵢ h_A)
          (LinearIsometryEquiv.refl ℂ (ℋ (ΛABC \ ΛAB))))).toLinearEquiv.conjAlgEquiv ℂ
        (S.act ΛABC (N.incl (h_A.trans h_AB) x))
      = TensorProduct.map (TensorProduct.map (S.act ΛA x) 1) 1 := by
  rw [← N.incl_trans h_A h_AB, S.act_incl h_AB, S.act_incl h_A]
  rw [show ((S.decompᵢ h_AB).trans
        (TensorProduct.congrIsometry (S.decompᵢ h_A)
          (LinearIsometryEquiv.refl ℂ (ℋ (ΛABC \ ΛAB))))).toLinearEquiv
      = (S.decompᵢ h_AB).toLinearEquiv.trans
          (TensorProduct.congr (S.decompᵢ h_A).toLinearEquiv
            (LinearEquiv.refl ℂ (ℋ (ΛABC \ ΛAB)))) from by
      rw [LinearIsometryEquiv.toLinearEquiv_trans, TensorProduct.toLinearEquiv_congrIsometry]; rfl]
  rw [LinearEquiv.conjAlgEquiv_trans, LinearMap.ampliate, S.decompᵢ_toLinearEquiv h_AB,
    AlgEquiv.apply_symm_apply, TensorProduct.congr_conjAlgEquiv_map, LinearMap.ampliate,
    S.decompᵢ_toLinearEquiv h_A, AlgEquiv.apply_symm_apply]
  congr 1

/-- **Isotony is invariant under a propositional equality of regions.** If `s = t` as finsets, the
embeddings `incl (s ⊆ Λ)` and `incl (t ⊆ Λ)` agree once the operand is transported along `s = t`.
This discharges the dependent-type coherence between the complement-of-complement region
`ΛABC ∖ (ΛABC ∖ ΛA)` and `ΛA` in the `BC`-marginal factorisation uniqueness. -/
theorem _root_.LocalNet.incl_cast {s t Λ : Finset sites} (hst : s = t) (hs : s ⊆ Λ) (ht : t ⊆ Λ)
    (z : N.algebra s) :
    N.incl hs z = N.incl ht (hst ▸ z) := by
  subst hst; rfl

/-- The reorganised unitary factorisation `ℋ ΛABC ≃ᵢ (ℋ B ⊗ ℋ C) ⊗ ℋ A` for the `BC` marginal:
factor out `ΛA` then `ΛAB ∖ ΛA`, reassociate, and move the `ΛA` factor to the end. This is the
factorisation `e₂` that reads the marginal of the `A × (B × C)` density matrix over the `A` factor;
the `ΛA` (traced-out) factor sits last so the partial trace over it lines up with `Matrix.traceRight`
of the reindexed density matrix. -/
noncomputable def bcReorg {ΛA ΛAB ΛABC : Finset sites} (h_A : ΛA ⊆ ΛAB) (h_AB : ΛAB ⊆ ΛABC) :
    ℋ ΛABC ≃ₗᵢ[ℂ] (ℋ (ΛAB \ ΛA) ⊗[ℂ] ℋ (ΛABC \ ΛAB)) ⊗[ℂ] ℋ ΛA :=
  ((S.decompᵢ h_AB).trans
      (TensorProduct.congrIsometry (S.decompᵢ h_A)
        (LinearIsometryEquiv.refl ℂ (ℋ (ΛABC \ ΛAB))))).trans
    ((TensorProduct.assocIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA)) (ℋ (ΛABC \ ΛAB))).trans
      (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA) ⊗[ℂ] ℋ (ΛABC \ ΛAB))))

/-- **The `A`-action through the reorganised factorisation `bcReorg`** is the canonical ampliation
on the last factor: `bcReorg-conj (act ΛABC (incl x)) = 1 ⊗ act ΛA x`. Together with the
complementary `act_incl_compl` action of the `decompᵢ (sdiff)` factorisation, this is the input to
factorisation uniqueness for the `BC` marginal. -/
theorem bcReorg_conjAlgEquiv_act_incl {ΛA ΛAB ΛABC : Finset sites} (h_A : ΛA ⊆ ΛAB)
    (h_AB : ΛAB ⊆ ΛABC) (x : N.algebra ΛA) :
    (S.bcReorg h_A h_AB).toLinearEquiv.conjAlgEquiv ℂ (S.act ΛABC (N.incl (h_A.trans h_AB) x))
      = TensorProduct.map 1 (S.act ΛA x) := by
  rw [bcReorg, LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.conjAlgEquiv_trans,
    S.wReorg_conjAlgEquiv_act_incl h_A h_AB, LinearIsometryEquiv.toLinearEquiv_trans,
    LinearEquiv.conjAlgEquiv_trans, TensorProduct.toLinearEquiv_assocIsometry,
    TensorProduct.assoc_conjAlgEquiv_map, TensorProduct.map_one,
    TensorProduct.toLinearEquiv_commIsometry, TensorProduct.comm_conjAlgEquiv_map]

/-- The direct unitary factorisation `ℋ ΛABC ≃ᵢ ℋ (ΛABC ∖ ΛA) ⊗ ℋ ΛA` for the `BC` marginal: factor
out `ΛA`'s complement directly (`decompᵢ (sdiff)`) and identify the complement-of-complement factor
with `ℋ ΛA` (`castIso`). This is the factorisation `e₁` whose partial trace is, by construction, the
`BC` marginal `restrict`; the traced-out factor is `ℋ ΛA`, matching `bcReorg`. -/
noncomputable def bcDirect {ΛA ΛABC : Finset sites} (h : ΛA ⊆ ΛABC) :
    ℋ ΛABC ≃ₗᵢ[ℂ] ℋ (ΛABC \ ΛA) ⊗[ℂ] ℋ ΛA :=
  (S.decompᵢ (Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC)).trans
    (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (ℋ (ΛABC \ ΛA)))
      (castIso (ℋ := ℋ) h))

/-- **The `A`-action through the direct factorisation `bcDirect`** is the canonical ampliation on
the last factor: `bcDirect-conj (act ΛABC (incl x)) = 1 ⊗ act ΛA x`. Proved via `act_incl_compl`
(the complement acts canonically on its factor), `incl_cast`/`castEquiv_conjAlgEquiv_act` (the
complement-of-complement region is `ΛA`). With `bcReorg_conjAlgEquiv_act_incl` this shows both
factorisations implement the *same* `ΛA`-action, the hypothesis of factorisation uniqueness. -/
theorem bcDirect_conjAlgEquiv_act_incl {ΛA ΛABC : Finset sites} (h : ΛA ⊆ ΛABC) (x : N.algebra ΛA) :
    (S.bcDirect h).toLinearEquiv.conjAlgEquiv ℂ (S.act ΛABC (N.incl h x))
      = TensorProduct.map 1 (S.act ΛA x) := by
  have hΛ : ΛABC \ (ΛABC \ ΛA) = ΛA := by
    rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr h]
  rw [LocalNet.incl_cast hΛ.symm h Finset.sdiff_subset x,
    S.act_incl_compl (Λ := ΛABC \ ΛA) Finset.sdiff_subset (hΛ.symm ▸ x)]
  rw [bcDirect, LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.conjAlgEquiv_trans,
    S.decompᵢ_toLinearEquiv, LinearMap.coampliate, AlgEquiv.apply_symm_apply,
    TensorProduct.toLinearEquiv_congrIsometry, TensorProduct.congr_conjAlgEquiv_map,
    castIso, S.castEquiv_conjAlgEquiv_act, map_one]

/-- **The nested tensor-product basis reassociates to the `bcReorg` factorisation.** The orthonormal
basis of `ℋ ΛABC` built by factoring `ΛA ⊆ ΛAB ⊆ ΛABC` and reindexing `((κA × κB) × κC)` to
`(κA × (κB × κC))` equals the basis pulled back along the `A`-first factorisation
`(decompᵢ h_AB) ≫ congr (decompᵢ h_A) 1 ≫ assoc`. This rewrites the density matrix `ρ_ABC` so that
its `A`-marginal (`ptLeft`) corresponds to the operator partial trace along `bcReorg`. -/
theorem tensorBasis_reindex_prodAssoc {ΛA ΛAB ΛABC : Finset sites} (h_A : ΛA ⊆ ΛAB)
    (h_AB : ΛAB ⊆ ΛABC) {κA κB κC : Type*} [Fintype κA] [Fintype κB] [Fintype κC]
    (bA : OrthonormalBasis κA ℂ (ℋ ΛA)) (bB : OrthonormalBasis κB ℂ (ℋ (ΛAB \ ΛA)))
    (bC : OrthonormalBasis κC ℂ (ℋ (ΛABC \ ΛAB))) :
    ((((bA.tensorProduct bB).map (S.decompᵢ h_A).symm).tensorProduct bC).map
        (S.decompᵢ h_AB).symm).reindex (Equiv.prodAssoc κA κB κC)
      = (bA.tensorProduct (bB.tensorProduct bC)).map
          (((S.decompᵢ h_AB).trans (TensorProduct.congrIsometry (S.decompᵢ h_A)
            (LinearIsometryEquiv.refl ℂ (ℋ (ΛABC \ ΛAB))))).trans
            (TensorProduct.assocIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA)) (ℋ (ΛABC \ ΛAB)))).symm := by
  apply DFunLike.ext
  rintro ⟨a, b, c⟩
  simp only [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply, Equiv.prodAssoc_symm_apply,
    LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    TensorProduct.assocIsometry_symm_apply, TensorProduct.congrIsometry_symm,
    TensorProduct.congrIsometry_apply, TensorProduct.assoc_symm_tmul, TensorProduct.congr_tmul]
  rfl

/-- **The `ΛA`-marginal entropy via the factorised basis equals the representation-free marginal
entropy.** For a state `σ` on `ℋ ΛAB`, tracing out the `ΛA`-index (`ptLeft`) of its density matrix
in the orthonormal basis pulled back from `ℋ ΛA ⊗ ℋ (ΛAB ∖ ΛA)` gives the von Neumann entropy of the
abstract marginal `restrict (sdiff) σ`. Proved by factorisation uniqueness comparing the
complement factorisation `bcDirect h_A` (whose partial trace is `restrict`) with the canonical
`decompᵢ h_A ≫ comm`. This is the building block for the middle-region (`B`) marginal of SSA. -/
theorem vonNeumannEntropy_ptLeft_decompBasis [∀ Λ, Nontrivial (ℋ Λ)]
    {ΛA ΛAB : Finset sites} (h_A : ΛA ⊆ ΛAB) {κA κB : Type*} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (bA : OrthonormalBasis κA ℂ (ℋ ΛA))
    (bB : OrthonormalBasis κB ℂ (ℋ (ΛAB \ ΛA))) {σ : N.algebra ΛAB} (hσ : S.IsDensity σ) :
    Matrix.vonNeumannEntropy
        (S.toDensityMatrixBasis ((bA.tensorProduct bB).map (S.decompᵢ h_A).symm) hσ).ptLeft
      = S.entropy (S.restrict (Finset.sdiff_subset : ΛAB \ ΛA ⊆ ΛAB) σ) := by
  have hcommB : ∀ f : Module.End ℂ (ℋ ΛA),
      ((S.bcDirect h_A).symm.trans
          ((S.decompᵢ h_A).trans
            (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.toLinearMap
          ∘ₗ TensorProduct.map LinearMap.id f
        = TensorProduct.map LinearMap.id f
          ∘ₗ ((S.bcDirect h_A).symm.trans
            ((S.decompᵢ h_A).trans
              (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.toLinearMap := by
    intro f
    obtain ⟨x, rfl⟩ : ∃ x, S.act ΛA x = f := ⟨(S.act ΛA).symm f, by simp⟩
    have h1 := S.bcDirect_conjAlgEquiv_act_incl h_A x
    have h2 : ((S.decompᵢ h_A).trans
          (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA)))).toLinearEquiv.conjAlgEquiv ℂ
          (S.act ΛAB (N.incl h_A x)) = TensorProduct.map 1 (S.act ΛA x) := by
      rw [S.act_incl h_A, LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.conjAlgEquiv_trans,
        LinearMap.ampliate, S.decompᵢ_toLinearEquiv, AlgEquiv.apply_symm_apply,
        TensorProduct.toLinearEquiv_commIsometry, TensorProduct.comm_conjAlgEquiv_map]
    simp only [← Module.End.one_eq_id]
    have hΨM : ((S.bcDirect h_A).symm.trans
          ((S.decompᵢ h_A).trans
            (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.conjAlgEquiv ℂ
          (TensorProduct.map 1 (S.act ΛA x)) = TensorProduct.map 1 (S.act ΛA x) := by
      conv_lhs => rw [← h1]
      rw [show ((S.bcDirect h_A).symm.trans
            ((S.decompᵢ h_A).trans
              (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv
          = (S.bcDirect h_A).toLinearEquiv.symm.trans
            ((S.decompᵢ h_A).trans
              (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA)))).toLinearEquiv from rfl,
        LinearEquiv.conjAlgEquiv_trans, ← LinearEquiv.symm_conjAlgEquiv, AlgEquiv.symm_apply_apply, h2]
    rw [LinearEquiv.conjAlgEquiv_apply] at hΨM
    calc ((S.bcDirect h_A).symm.trans
            ((S.decompᵢ h_A).trans
              (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.toLinearMap
          ∘ₗ TensorProduct.map 1 (S.act ΛA x)
        = (((S.bcDirect h_A).symm.trans
              ((S.decompᵢ h_A).trans
                (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.toLinearMap
            ∘ₗ TensorProduct.map 1 (S.act ΛA x)
            ∘ₗ ((S.bcDirect h_A).symm.trans
              ((S.decompᵢ h_A).trans
                (TensorProduct.commIsometry ℂ (ℋ ΛA)
                  (ℋ (ΛAB \ ΛA))))).toLinearEquiv.symm.toLinearMap)
            ∘ₗ ((S.bcDirect h_A).symm.trans
              ((S.decompᵢ h_A).trans
                (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.toLinearMap := by
          rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _
            ((S.bcDirect h_A).symm.trans
              ((S.decompᵢ h_A).trans
                (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.toLinearMap,
            LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
            LinearMap.comp_id]
      _ = TensorProduct.map 1 (S.act ΛA x)
            ∘ₗ ((S.bcDirect h_A).symm.trans
              ((S.decompᵢ h_A).trans
                (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA))))).toLinearEquiv.toLinearMap := by
          rw [hΨM]
  obtain ⟨W, hW⟩ := factorization_uniqueness (S.bcDirect h_A)
    ((S.decompᵢ h_A).trans (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA)))) hcommB (S.act ΛAB σ)
  have hptdB : LinearMap.partialTrace (S.bcDirect h_A).toLinearEquiv (S.act ΛAB σ)
      = S.act (ΛAB \ ΛA) (S.restrict Finset.sdiff_subset σ) := by
    rw [LocalNet.Split.bcDirect, LinearIsometryEquiv.toLinearEquiv_trans, S.decompᵢ_toLinearEquiv,
      TensorProduct.toLinearEquiv_congrIsometry,
      show (LinearIsometryEquiv.refl ℂ (ℋ (ΛAB \ ΛA))).toLinearEquiv
          = LinearEquiv.refl ℂ (ℋ (ΛAB \ ΛA)) from rfl,
      LinearMap.partialTrace_congr_right_id, S.restrict_apply, AlgEquiv.apply_symm_apply]
  have hbmap : (bB.map W.symm).map W = bB := by
    apply DFunLike.ext; intro i; simp [OrthonormalBasis.map_apply]
  rw [show (S.toDensityMatrixBasis ((bA.tensorProduct bB).map (S.decompᵢ h_A).symm) hσ).ptLeft
        = S.toDensityMatrixBasis (bB.map W.symm) (S.restrict_isDensity Finset.sdiff_subset hσ) from ?_,
    S.vonNeumannEntropy_toDensityMatrixBasis]
  apply DensityMatrix.ext
  rw [DensityMatrix.ptLeft_toMatrix, S.toDensityMatrixBasis_toMatrix, S.toMatrixBasis_apply,
    S.toDensityMatrixBasis_toMatrix, S.toMatrixBasis_apply, LinearMap.traceLeft_toMatrixOrthonormal,
    hW]
  conv_lhs => rw [← hbmap]
  rw [toMatrixOrthonormal_conj_map, hptdB]

/-- **Strong subadditivity of the von Neumann entropy on an abstract split net.** For a faithful
operator-algebraic split net `LocalNet.Split` over finite-dimensional action spaces, and a state
`ρ` on a region `ΛABC` with a nested decomposition `ΛA ⊆ ΛAB ⊆ ΛABC`, the entropies of the marginals
obey
`S(ABC) + S(B) ≤ S(AB) + S(BC)`,
where `B = ΛAB ∖ ΛA`, `BC = ΛABC ∖ ΛA`, and each marginal is the representation-free `restrict`.
This is the AQFT form of strong subadditivity: it is assembled entirely on the abstract net (no
matrix model), by reading each marginal in a tensor-factorised orthonormal basis, using factorisation
uniqueness (the partial trace depends only on the subsystem, not the chosen factorisation of its
complement — the tensor commutant theorem plus the spatial split data `act_incl`/`act_incl_compl`),
and transporting the analytic core `DensityMatrix.vonNeumannEntropy_SSA_product` to the net. -/
theorem vonNeumannEntropy_SSA [∀ Λ, Nontrivial (ℋ Λ)]
    {ΛA ΛAB ΛABC : Finset sites} (h_A : ΛA ⊆ ΛAB) (h_AB : ΛAB ⊆ ΛABC)
    {ρ : N.algebra ΛABC} (hρ : S.IsDensity ρ) :
    S.entropy ρ + S.entropy (S.restrict ((Finset.sdiff_subset : ΛAB \ ΛA ⊆ ΛAB).trans h_AB) ρ)
      ≤ S.entropy (S.restrict h_AB ρ)
        + S.entropy (S.restrict (Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC) ρ) := by
  haveI : Nonempty (Fin (Module.finrank ℂ (ℋ ΛA))) := ⟨⟨0, Module.finrank_pos⟩⟩
  haveI : Nonempty (Fin (Module.finrank ℂ (ℋ (ΛAB \ ΛA)))) := ⟨⟨0, Module.finrank_pos⟩⟩
  haveI : Nonempty (Fin (Module.finrank ℂ (ℋ (ΛABC \ ΛAB)))) := ⟨⟨0, Module.finrank_pos⟩⟩
  set bA := stdOrthonormalBasis ℂ (ℋ ΛA) with hbA
  set bB := stdOrthonormalBasis ℂ (ℋ (ΛAB \ ΛA)) with hbB
  set bC := stdOrthonormalBasis ℂ (ℋ (ΛABC \ ΛAB)) with hbC
  set ρ_ABC := S.toDensityMatrixBasis
      (((((bA.tensorProduct bB).map (S.decompᵢ h_A).symm).tensorProduct bC).map
        (S.decompᵢ h_AB).symm).reindex (Equiv.prodAssoc _ _ _)) hρ with hρ_ABC
  have key := DensityMatrix.vonNeumannEntropy_SSA_product ρ_ABC
    ((ρ_ABC.mapEquiv (Equiv.prodAssoc _ _ _)).ptRight) ρ_ABC.ptLeft ρ_ABC.ptLeft.ptRight rfl rfl rfl
  have hABC : Matrix.vonNeumannEntropy ρ_ABC = S.entropy ρ := by
    rw [hρ_ABC, S.vonNeumannEntropy_toDensityMatrixBasis]
  have hmar : (ρ_ABC.mapEquiv (Equiv.prodAssoc _ _ _)).ptRight
      = S.toDensityMatrixBasis ((bA.tensorProduct bB).map (S.decompᵢ h_A).symm)
        (S.restrict_isDensity h_AB hρ) := by
    rw [hρ_ABC, S.toDensityMatrixBasis_reindex_mapEquiv]
    apply DensityMatrix.ext
    rw [DensityMatrix.ptRight_toMatrix, S.toDensityMatrixBasis_toMatrix, S.toMatrixBasis_apply,
      S.toDensityMatrixBasis_toMatrix, S.toMatrixBasis_apply, LinearMap.traceRight_toMatrixOrthonormal]
    congr 1
    rw [S.restrict_apply, AlgEquiv.apply_symm_apply, S.decompᵢ_toLinearEquiv]
  have hAB : Matrix.vonNeumannEntropy (ρ_ABC.mapEquiv (Equiv.prodAssoc _ _ _)).ptRight
      = S.entropy (S.restrict h_AB ρ) := by rw [hmar, S.vonNeumannEntropy_toDensityMatrixBasis]
  have hcomm : ∀ f : Module.End ℂ (ℋ ΛA),
      ((S.bcDirect (h_A.trans h_AB)).symm.trans (S.bcReorg h_A h_AB)).toLinearEquiv.toLinearMap
          ∘ₗ TensorProduct.map LinearMap.id f
        = TensorProduct.map LinearMap.id f
          ∘ₗ ((S.bcDirect (h_A.trans h_AB)).symm.trans
            (S.bcReorg h_A h_AB)).toLinearEquiv.toLinearMap := by
    intro f
    obtain ⟨x, rfl⟩ : ∃ x, S.act ΛA x = f := ⟨(S.act ΛA).symm f, by simp⟩
    have h1 := S.bcDirect_conjAlgEquiv_act_incl (h_A.trans h_AB) x
    have h2 := S.bcReorg_conjAlgEquiv_act_incl h_A h_AB x
    simp only [← Module.End.one_eq_id]
    have hΨM : ((S.bcDirect (h_A.trans h_AB)).symm.trans
          (S.bcReorg h_A h_AB)).toLinearEquiv.conjAlgEquiv ℂ
          (TensorProduct.map 1 (S.act ΛA x)) = TensorProduct.map 1 (S.act ΛA x) := by
      conv_lhs => rw [← h1]
      rw [show ((S.bcDirect (h_A.trans h_AB)).symm.trans (S.bcReorg h_A h_AB)).toLinearEquiv
          = (S.bcDirect (h_A.trans h_AB)).toLinearEquiv.symm.trans (S.bcReorg h_A h_AB).toLinearEquiv
          from rfl, LinearEquiv.conjAlgEquiv_trans, ← LinearEquiv.symm_conjAlgEquiv,
        AlgEquiv.symm_apply_apply, h2]
    rw [LinearEquiv.conjAlgEquiv_apply] at hΨM
    calc ((S.bcDirect (h_A.trans h_AB)).symm.trans (S.bcReorg h_A h_AB)).toLinearEquiv.toLinearMap
          ∘ₗ TensorProduct.map 1 (S.act ΛA x)
        = (((S.bcDirect (h_A.trans h_AB)).symm.trans (S.bcReorg h_A h_AB)).toLinearEquiv.toLinearMap
            ∘ₗ TensorProduct.map 1 (S.act ΛA x)
            ∘ₗ ((S.bcDirect (h_A.trans h_AB)).symm.trans
              (S.bcReorg h_A h_AB)).toLinearEquiv.symm.toLinearMap)
            ∘ₗ ((S.bcDirect (h_A.trans h_AB)).symm.trans
              (S.bcReorg h_A h_AB)).toLinearEquiv.toLinearMap := by
          rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _
            ((S.bcDirect (h_A.trans h_AB)).symm.trans (S.bcReorg h_A h_AB)).toLinearEquiv.toLinearMap,
            LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
            LinearMap.comp_id]
      _ = TensorProduct.map 1 (S.act ΛA x)
            ∘ₗ ((S.bcDirect (h_A.trans h_AB)).symm.trans
              (S.bcReorg h_A h_AB)).toLinearEquiv.toLinearMap := by
          rw [hΨM]
  have hBC : Matrix.vonNeumannEntropy ρ_ABC.ptLeft
      = S.entropy (S.restrict (Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC) ρ) := by
    rw [hρ_ABC]
    obtain ⟨V, hV⟩ := factorization_uniqueness (S.bcDirect (h_A.trans h_AB)) (S.bcReorg h_A h_AB)
      hcomm (S.act ΛABC ρ)
    have hptd : LinearMap.partialTrace (S.bcDirect (h_A.trans h_AB)).toLinearEquiv (S.act ΛABC ρ)
        = S.act (ΛABC \ ΛA) (S.restrict Finset.sdiff_subset ρ) := by
      rw [LocalNet.Split.bcDirect, LinearIsometryEquiv.toLinearEquiv_trans, S.decompᵢ_toLinearEquiv,
        TensorProduct.toLinearEquiv_congrIsometry,
        show (LinearIsometryEquiv.refl ℂ (ℋ (ΛABC \ ΛA))).toLinearEquiv
            = LinearEquiv.refl ℂ (ℋ (ΛABC \ ΛA)) from rfl,
        LinearMap.partialTrace_congr_right_id, S.restrict_apply, AlgEquiv.apply_symm_apply]
    have hbmap : ((bB.tensorProduct bC).map V.symm).map V = bB.tensorProduct bC := by
      apply DFunLike.ext; intro i; simp [OrthonormalBasis.map_apply]
    rw [show (S.toDensityMatrixBasis _ hρ).ptLeft = S.toDensityMatrixBasis
          ((bB.tensorProduct bC).map V.symm) (S.restrict_isDensity Finset.sdiff_subset hρ) from ?_,
      S.vonNeumannEntropy_toDensityMatrixBasis]
    apply DensityMatrix.ext
    rw [DensityMatrix.ptLeft_toMatrix, S.toDensityMatrixBasis_toMatrix, S.toMatrixBasis_apply,
      S.toDensityMatrixBasis_toMatrix, S.toMatrixBasis_apply,
      S.tensorBasis_reindex_prodAssoc h_A h_AB bA bB bC, LinearMap.traceLeft_toMatrixOrthonormal,
      show (((S.decompᵢ h_AB).trans (TensorProduct.congrIsometry (S.decompᵢ h_A)
          (LinearIsometryEquiv.refl ℂ (ℋ (ΛABC \ ΛAB))))).trans
          (TensorProduct.assocIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA)) (ℋ (ΛABC \ ΛAB)))).trans
          (TensorProduct.commIsometry ℂ (ℋ ΛA) (ℋ (ΛAB \ ΛA) ⊗[ℂ] ℋ (ΛABC \ ΛAB)))
          = S.bcReorg h_A h_AB from by rw [LocalNet.Split.bcReorg, LinearIsometryEquiv.trans_assoc],
      hV]
    conv_lhs => rw [← hbmap]
    rw [toMatrixOrthonormal_conj_map, hptd]
  have hB : Matrix.vonNeumannEntropy ρ_ABC.ptLeft.ptRight
      = S.entropy (S.restrict ((Finset.sdiff_subset : ΛAB \ ΛA ⊆ ΛAB).trans h_AB) ρ) := by
    rw [show ρ_ABC.ptLeft.ptRight = (ρ_ABC.mapEquiv (Equiv.prodAssoc _ _ _)).ptRight.ptLeft from ?_,
      hmar, S.vonNeumannEntropy_ptLeft_decompBasis h_A bA bB (S.restrict_isDensity h_AB hρ),
      S.restrict_restrict]
    apply DensityMatrix.ext
    rw [DensityMatrix.ptRight_toMatrix, DensityMatrix.ptLeft_toMatrix, DensityMatrix.ptLeft_toMatrix,
      DensityMatrix.ptRight_toMatrix, DensityMatrix.mapEquiv_toMatrix]
    exact (Matrix.traceLeft_traceRight_submatrix_prodAssoc _).symm
  rw [hABC, hB, hAB, hBC] at key
  exact key

end LocalNet.Split
