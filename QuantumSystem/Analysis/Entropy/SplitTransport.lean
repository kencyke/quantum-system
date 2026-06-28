module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import QuantumSystem.Analysis.Entropy.SplitEntropy
public import QuantumSystem.Analysis.Entropy.VonNeumannEntropy

/-!
# Matrix transport for a split net

The **transport bridge** that carries the representation-free split-net quantum information back to
the matrix theory: for a region `Λ`, an orthonormal basis of the action space `ℋ Λ` realises the
local algebra as a matrix algebra,

  `Split.toMatrix Λ : N.algebra Λ ≃⋆ₐ[ℂ] Matrix (Fin (finrank ℂ (ℋ Λ))) … ℂ`,

a genuine `*`-isomorphism (`act` is a `*`-iso by `act_star`, and `LinearMap.toMatrixOrthonormal` is
a `*`-iso for an orthonormal basis). Through it, positivity, trace, density and von Neumann entropy
on the split net coincide with their matrix counterparts, so the deep matrix results
(non-negativity, strong subadditivity, …) transport to the abstract net.
-/

@[expose] public section

open scoped Matrix ComplexOrder TensorProduct

namespace TensorProduct

variable {ι A B : Type*} [Fintype ι]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

/-- The diagonal quadratic form of the partial trace over the second factor, expanded over an
orthonormal basis `w` of `B`: `⟪partialTraceRight S a, a⟫ = ∑ₖ ⟪(S as operator) (a ⊗ wₖ), a ⊗ wₖ⟫`.
This is the bridge that makes `partialTraceRight` manifestly positivity-preserving. -/
lemma inner_partialTraceRight (w : OrthonormalBasis ι ℂ B)
    (S : Module.End ℂ A ⊗[ℂ] Module.End ℂ B) (a a' : A) :
    inner ℂ (partialTraceRight S a') a
      = ∑ k, inner ℂ (endTensorEndAlgEquiv S (a' ⊗ₜ[ℂ] w k)) (a ⊗ₜ[ℂ] w k) := by
  induction S using TensorProduct.induction_on with
  | zero => simp
  | tmul Y Z =>
    rw [partialTraceRight_tmul, endTensorEndAlgEquiv_tmul, LinearMap.smul_apply, inner_smul_left]
    simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul, ← Finset.mul_sum]
    rw [mul_comm]
    congr 1
    rw [LinearMap.trace_eq_sum_inner Z w, starRingEnd_apply, star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← starRingEnd_apply, inner_conj_symm]
  | add S₁ S₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, inner_add_left, h₁, h₂, Finset.sum_add_distrib]

end TensorProduct

namespace LinearMap

open scoped ComplexOrder

variable {ℋ A B : Type*}
  [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [FiniteDimensional ℂ ℋ]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

omit [FiniteDimensional ℂ ℋ] in
/-- **The partial trace preserves positivity.** Along a *unitary* tensor factorisation
`e : ℋ ≃ₗᵢ A ⊗ B`, the partial trace of a positive operator is positive — the partial trace is a
quantum channel. The quadratic form expands (`TensorProduct.inner_partialTraceRight`) into a sum of
the quadratic form of `T` at the unit-vectors `e.symm (a ⊗ wₖ)`, each non-negative. -/
theorem isPositive_partialTrace (e : ℋ ≃ₗᵢ[ℂ] (A ⊗[ℂ] B)) {T : Module.End ℂ ℋ}
    (hT : T.IsPositive) : (LinearMap.partialTrace e.toLinearEquiv T).IsPositive := by
  rw [LinearMap.isPositive_iff_complex]
  intro a
  set w := stdOrthonormalBasis ℂ B with hw
  have key : inner ℂ (LinearMap.partialTrace e.toLinearEquiv T a) a =
      ((∑ k, RCLike.re (inner ℂ (T (e.symm (a ⊗ₜ[ℂ] w k))) (e.symm (a ⊗ₜ[ℂ] w k))) : ℝ) : ℂ) := by
    rw [LinearMap.partialTrace_apply, TensorProduct.inner_partialTraceRight w,
      AlgEquiv.apply_symm_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearEquiv.conjAlgEquiv_apply_apply,
      show inner ℂ (e.toLinearEquiv (T (e.toLinearEquiv.symm (a ⊗ₜ[ℂ] w k)))) (a ⊗ₜ[ℂ] w k)
          = inner ℂ (T (e.symm (a ⊗ₜ[ℂ] w k))) (e.symm (a ⊗ₜ[ℂ] w k)) from by
        change inner ℂ (e (T (e.symm (a ⊗ₜ[ℂ] w k)))) (a ⊗ₜ[ℂ] w k)
          = inner ℂ (T (e.symm (a ⊗ₜ[ℂ] w k))) (e.symm (a ⊗ₜ[ℂ] w k))
        rw [← e.inner_map_map (T (e.symm (a ⊗ₜ[ℂ] w k))) (e.symm (a ⊗ₜ[ℂ] w k)),
          e.apply_symm_apply],
      (((LinearMap.isPositive_iff_complex T).mp hT _).1)]
  rw [key]
  have hre : RCLike.re ((∑ k, RCLike.re (inner ℂ (T (e.symm (a ⊗ₜ[ℂ] w k)))
        (e.symm (a ⊗ₜ[ℂ] w k))) : ℝ) : ℂ)
      = ∑ k, RCLike.re (inner ℂ (T (e.symm (a ⊗ₜ[ℂ] w k))) (e.symm (a ⊗ₜ[ℂ] w k))) :=
    RCLike.ofReal_re _
  rw [hre]
  exact ⟨rfl, Finset.sum_nonneg fun k _ => ((LinearMap.isPositive_iff_complex T).mp hT _).2⟩

/-- The **Kraus operators** `Vⱼ : A →ₗ ℋ`, `a ↦ e.symm (a ⊗ wⱼ)`, of the partial trace along a
unitary factorisation `e : ℋ ≃ₗᵢ A ⊗ B`, where `w` is the standard orthonormal basis of `B`. -/
noncomputable def ptKraus (e : ℋ ≃ₗᵢ[ℂ] (A ⊗[ℂ] B)) (j : Fin (Module.finrank ℂ B)) :
    A →ₗ[ℂ] ℋ :=
  e.symm.toLinearEquiv.toLinearMap ∘ₗ (TensorProduct.mk ℂ A B).flip (stdOrthonormalBasis ℂ B j)

omit [FiniteDimensional ℂ ℋ] [FiniteDimensional ℂ A] in
@[simp] theorem ptKraus_apply (e : ℋ ≃ₗᵢ[ℂ] (A ⊗[ℂ] B)) (j : Fin (Module.finrank ℂ B)) (a : A) :
    ptKraus e j a = e.symm (a ⊗ₜ[ℂ] stdOrthonormalBasis ℂ B j) :=
  rfl

/-- **Kraus form of the partial trace**: along a unitary factorisation `e`, the partial trace is a
sum of compressions `Tr_B T = ∑ⱼ Vⱼ⋆ T Vⱼ`. This is the Kraus/Stinespring decomposition exhibiting
the partial trace as a completely positive map. -/
theorem partialTrace_eq_sum_kraus (e : ℋ ≃ₗᵢ[ℂ] (A ⊗[ℂ] B)) (T : Module.End ℂ ℋ) :
    LinearMap.partialTrace e.toLinearEquiv T
      = ∑ j, LinearMap.adjoint (ptKraus e j) ∘ₗ T ∘ₗ ptKraus e j := by
  ext a'
  refine ext_inner_right ℂ fun a => ?_
  rw [LinearMap.partialTrace_apply, TensorProduct.inner_partialTraceRight (stdOrthonormalBasis ℂ B),
    AlgEquiv.apply_symm_apply, LinearMap.sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_left, ptKraus_apply,
    ptKraus_apply, LinearEquiv.conjAlgEquiv_apply_apply]
  rw [show e.toLinearEquiv (T (e.toLinearEquiv.symm (a' ⊗ₜ[ℂ] stdOrthonormalBasis ℂ B j)))
        = e (T (e.symm (a' ⊗ₜ[ℂ] stdOrthonormalBasis ℂ B j))) from rfl,
    ← e.inner_map_map (T (e.symm (a' ⊗ₜ[ℂ] stdOrthonormalBasis ℂ B j)))
      (e.symm (a ⊗ₜ[ℂ] stdOrthonormalBasis ℂ B j)), e.apply_symm_apply]

omit [FiniteDimensional ℂ A] [FiniteDimensional ℂ B] in
/-- The matrix trace of the matrix of `T` in an orthonormal basis `b` is the operator trace of `T`
(independent of the choice of orthonormal basis). -/
theorem trace_toMatrixOrthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ ℋ) (T : Module.End ℂ ℋ) :
    (LinearMap.toMatrixOrthonormal b T).trace = LinearMap.trace ℂ ℋ T := by
  rw [LinearMap.trace_eq_sum_inner T b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrixOrthonormal_apply_apply]

end LinearMap

namespace LocalNet.Split

variable {sites : Type*} [DecidableEq sites] {N : LocalNet sites} {ℋ : Finset sites → Type*}
  [∀ Λ, NormedAddCommGroup (ℋ Λ)] [∀ Λ, InnerProductSpace ℂ (ℋ Λ)]
  [∀ Λ, FiniteDimensional ℂ (ℋ Λ)]
  (S : Split N ℋ)

/-- The type I identification `act Λ` packaged as a `*`-isomorphism, using `act_star`. -/
noncomputable def actₛ (Λ : Finset sites) : N.algebra Λ ≃⋆ₐ[ℂ] Module.End ℂ (ℋ Λ) :=
  { S.act Λ with map_smul' := map_smul (S.act Λ), map_star' := S.act_star }

@[simp] theorem actₛ_apply (Λ : Finset sites) (x : N.algebra Λ) :
    S.actₛ Λ x = S.act Λ x :=
  rfl

/-- The **matrix representation** of the local algebra at `Λ`, a `*`-isomorphism onto the matrix
algebra on the index `Fin (finrank ℂ (ℋ Λ))` obtained from the standard orthonormal basis of the
action space. The composite of the type I identification `actₛ` with the orthonormal matrix
representation `LinearMap.toMatrixOrthonormal`. -/
noncomputable def toMatrix (Λ : Finset sites) :
    N.algebra Λ ≃⋆ₐ[ℂ] Matrix (Fin (Module.finrank ℂ (ℋ Λ))) (Fin (Module.finrank ℂ (ℋ Λ))) ℂ :=
  (S.actₛ Λ).trans (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ (ℋ Λ)))

theorem toMatrix_apply (Λ : Finset sites) (x : N.algebra Λ) :
    S.toMatrix Λ x =
      LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ (ℋ Λ)) (S.act Λ x) :=
  rfl

/-- **Trace transport**: the split trace coincides with the matrix trace of the transported
operator. -/
theorem trace_eq_matrixTrace (Λ : Finset sites) (ρ : N.algebra Λ) :
    S.trace Λ ρ = (S.toMatrix Λ ρ).trace := by
  rw [trace_apply, LinearMap.trace_eq_sum_inner (S.act Λ ρ) (stdOrthonormalBasis ℂ (ℋ Λ)),
    Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, toMatrix_apply, LinearMap.toMatrixOrthonormal_apply_apply]

/-- **Positivity transport**: the transported matrix is positive semidefinite iff the operator
`act Λ ρ` is positive (Loewner). This is `LinearMap.posSemidef_toMatrix_iff` for the orthonormal
basis, through `act`. -/
theorem posSemidef_toMatrix_iff (Λ : Finset sites) (ρ : N.algebra Λ) :
    (S.toMatrix Λ ρ).PosSemidef ↔ 0 ≤ S.act Λ ρ := by
  rw [toMatrix_apply, LinearMap.nonneg_iff_isPositive]
  exact LinearMap.posSemidef_toMatrix_iff (stdOrthonormalBasis ℂ (ℋ Λ))

/-- **Density transport**: a state of the split net (`IsDensity`) maps to a genuine density matrix
under the matrix representation. This is the bridge object through which the matrix quantum
information (von Neumann entropy, strong subadditivity, …) is pulled back to the split net. -/
noncomputable def toDensityMatrix {Λ : Finset sites} {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    DensityMatrix (Fin (Module.finrank ℂ (ℋ Λ))) where
  toMatrix := S.toMatrix Λ ρ
  posSemidef := (S.posSemidef_toMatrix_iff Λ ρ).mpr hρ.nonneg
  trace_eq_one := by rw [← S.trace_eq_matrixTrace]; exact hρ.trace_eq_one

@[simp] theorem toDensityMatrix_toMatrix {Λ : Finset sites} {ρ : N.algebra Λ}
    (hρ : S.IsDensity ρ) : (S.toDensityMatrix hρ).toMatrix = S.toMatrix Λ ρ :=
  rfl

include S in
/-- The local algebra of a split net is finite-dimensional (it is `*`-isomorphic to the operator
algebra on the finite-dimensional action space). -/
theorem finiteDimensional_algebra (Λ : Finset sites) : FiniteDimensional ℂ (N.algebra Λ) :=
  (S.act Λ).symm.toLinearEquiv.finiteDimensional

/-- The matrix representation `Split.toMatrix Λ` is continuous (a linear map of
finite-dimensional spaces). -/
theorem continuous_toMatrix (Λ : Finset sites) : Continuous (S.toMatrix Λ) := by
  haveI := S.finiteDimensional_algebra Λ
  let L : N.algebra Λ →ₗ[ℂ]
      Matrix (Fin (Module.finrank ℂ (ℋ Λ))) (Fin (Module.finrank ℂ (ℋ Λ))) ℂ :=
    { toFun := S.toMatrix Λ, map_add' := map_add _, map_smul' := map_smul _ }
  exact L.continuous_of_finiteDimensional

/-- A state of the split net is self-adjoint (positive operators are self-adjoint, and `act` is a
`*`-isomorphism). -/
theorem isSelfAdjoint_of_isDensity {Λ : Finset sites} {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    IsSelfAdjoint ρ := by
  have h1 : IsSelfAdjoint (S.act Λ ρ) :=
    ((LinearMap.nonneg_iff_isPositive _).mp hρ.nonneg).isSelfAdjoint
  apply (S.act Λ).injective
  rw [S.act_star]
  exact h1

/-- **Entropy transport**: the split-net von Neumann entropy of a state coincides with the matrix
von Neumann entropy of its transported density matrix. The continuous functional calculus commutes
with the `*`-isomorphism `toMatrix` (`StarAlgHomClass.map_cfc`). -/
theorem entropy_eq_vonNeumannEntropy {Λ : Finset sites} {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    S.entropy ρ = Matrix.vonNeumannEntropy (S.toDensityMatrix hρ) := by
  haveI : IsScalarTower ℝ ℂ (N.algebra Λ) := IsScalarTower.complexToReal
  have hsa : IsSelfAdjoint ρ := S.isSelfAdjoint_of_isDensity hρ
  have hsa' : IsSelfAdjoint (S.toMatrix Λ ρ) :=
    show star (S.toMatrix Λ ρ) = S.toMatrix Λ ρ by rw [← map_star, hsa]
  rw [entropy_def, trace_eq_matrixTrace, Matrix.vonNeumannEntropy_eq_cfc_re,
    toDensityMatrix_toMatrix,
    StarAlgHomClass.map_cfc (S.toMatrix Λ) Real.negMulLog ρ
      Real.continuous_negMulLog.continuousOn (S.continuous_toMatrix Λ) hsa hsa']

/-- **Von Neumann entropy of a split-net state is non-negative.** Transported from the matrix
result `Matrix.vonNeumannEntropy_nonneg`. -/
theorem entropy_nonneg {Λ : Finset sites} {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    0 ≤ S.entropy ρ := by
  rw [S.entropy_eq_vonNeumannEntropy hρ]
  exact Matrix.vonNeumannEntropy_nonneg _

/-- The **matrix representation in an arbitrary orthonormal basis** `b` of the action space, a
`*`-isomorphism `N.algebra Λ ≃⋆ₐ Matrix ι`. The von Neumann entropy of the resulting density matrix
is independent of `b` (`vonNeumannEntropy_toDensityMatrixBasis`); this is the freedom of orthonormal
basis used to transport tensor-factorised marginals. -/
noncomputable def toMatrixBasis {Λ : Finset sites} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (ℋ Λ)) : N.algebra Λ ≃⋆ₐ[ℂ] Matrix ι ι ℂ :=
  (S.actₛ Λ).trans (LinearMap.toMatrixOrthonormal b)

theorem toMatrixBasis_apply {Λ : Finset sites} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (ℋ Λ)) (x : N.algebra Λ) :
    S.toMatrixBasis b x = LinearMap.toMatrixOrthonormal b (S.act Λ x) :=
  rfl

theorem trace_eq_matrixTrace_basis {Λ : Finset sites} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (ℋ Λ)) (ρ : N.algebra Λ) :
    S.trace Λ ρ = (S.toMatrixBasis b ρ).trace := by
  rw [toMatrixBasis_apply, LinearMap.trace_toMatrixOrthonormal, trace_apply]

theorem continuous_toMatrixBasis {Λ : Finset sites} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (ℋ Λ)) : Continuous (S.toMatrixBasis b) := by
  haveI := S.finiteDimensional_algebra Λ
  let L : N.algebra Λ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := S.toMatrixBasis b, map_add' := map_add _, map_smul' := map_smul _ }
  exact L.continuous_of_finiteDimensional

/-- The density matrix of a state in an arbitrary orthonormal basis `b` of the action space. -/
noncomputable def toDensityMatrixBasis {Λ : Finset sites} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (ℋ Λ)) {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    DensityMatrix ι where
  toMatrix := S.toMatrixBasis b ρ
  posSemidef := by
    rw [toMatrixBasis_apply]
    exact (LinearMap.posSemidef_toMatrix_iff b).mpr
      ((LinearMap.nonneg_iff_isPositive _).mp hρ.nonneg)
  trace_eq_one := by rw [← S.trace_eq_matrixTrace_basis b]; exact hρ.trace_eq_one

@[simp] theorem toDensityMatrixBasis_toMatrix {Λ : Finset sites} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℂ (ℋ Λ)) {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    (S.toDensityMatrixBasis b hρ).toMatrix = S.toMatrixBasis b ρ :=
  rfl

/-- **Basis-independence of the von Neumann entropy**: the matrix von Neumann entropy of a state's
density matrix is the same in any orthonormal basis of the action space, and equals the
representation-free split-net entropy `S.entropy`. This is the freedom needed to compute marginal
entropies in a *tensor-factorised* orthonormal basis. -/
theorem vonNeumannEntropy_toDensityMatrixBasis {Λ : Finset sites} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℂ (ℋ Λ)) {ρ : N.algebra Λ} (hρ : S.IsDensity ρ) :
    Matrix.vonNeumannEntropy (S.toDensityMatrixBasis b hρ) = S.entropy ρ := by
  haveI : IsScalarTower ℝ ℂ (N.algebra Λ) := IsScalarTower.complexToReal
  have hsa : IsSelfAdjoint ρ := S.isSelfAdjoint_of_isDensity hρ
  have hsa' : IsSelfAdjoint (S.toMatrixBasis b ρ) :=
    show star (S.toMatrixBasis b ρ) = S.toMatrixBasis b ρ by rw [← map_star, hsa]
  rw [entropy_def, S.trace_eq_matrixTrace_basis b, Matrix.vonNeumannEntropy_eq_cfc_re,
    toDensityMatrixBasis_toMatrix,
    StarAlgHomClass.map_cfc (S.toMatrixBasis b) Real.negMulLog ρ
      Real.continuous_negMulLog.continuousOn (S.continuous_toMatrixBasis b) hsa hsa']

/-- **The marginal of a state is a state.** Restricting a density operator to a sub-region yields a
density operator: the marginal preserves positivity (the partial trace along the *unitary*
factorisation `decompᵢ` is positivity-preserving, `LinearMap.isPositive_partialTrace`) and the
trace (`trace_restrict`). This is the representation-free statement that `restrict` is a quantum
channel on states. -/
theorem restrict_isDensity {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') {ρ : N.algebra Λ'}
    (hρ : S.IsDensity ρ) : S.IsDensity (S.restrict h ρ) := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.nonneg_iff_isPositive, restrict_apply, AlgEquiv.apply_symm_apply]
    have hpt := LinearMap.isPositive_partialTrace (S.decompᵢ h)
      ((LinearMap.nonneg_iff_isPositive _).mp hρ.nonneg)
    rwa [S.decompᵢ_toLinearEquiv h] at hpt
  · rw [S.trace_restrict h ρ]
    exact hρ.trace_eq_one

/-- **Non-degeneracy of the trace pairing** on a local algebra: if `trace (A · X) = trace (B · X)`
for every `X`, then `A = B`. The trace form on the type I factor is non-degenerate
(`Matrix.ext_iff_trace_mul_right` through the matrix representation `toMatrix`). -/
theorem trace_nondeg {Λ : Finset sites} {A B : N.algebra Λ}
    (hAB : ∀ X, S.trace Λ (A * X) = S.trace Λ (B * X)) : A = B := by
  apply (S.toMatrix Λ).injective
  rw [Matrix.ext_iff_trace_mul_right]
  intro Y
  have hX := hAB ((S.toMatrix Λ).symm Y)
  simp only [trace_eq_matrixTrace, map_mul, StarAlgEquiv.apply_symm_apply] at hX
  exact hX

/-- **Iterated marginalisation equals direct marginalisation**:
`restrict h₂ (restrict h₁ ρ) = restrict (h₂.trans h₁) ρ`. This is the coherence that strong
subadditivity needs — and it is **free**: it follows from the Heisenberg/trace duality
`trace_mul_incl` together with the net's functoriality `incl_trans`, with no associativity axiom on
the tensor factorisations. (The marginal is the predual of `incl`, and inclusions compose.) -/
theorem restrict_restrict {Λ'' Λ Λ' : Finset sites} (h₁ : Λ ⊆ Λ') (h₂ : Λ'' ⊆ Λ)
    (ρ : N.algebra Λ') :
    S.restrict h₂ (S.restrict h₁ ρ) = S.restrict (h₂.trans h₁) ρ := by
  apply S.trace_nondeg
  intro X
  rw [← S.trace_mul_incl h₂ (S.restrict h₁ ρ) X, ← S.trace_mul_incl (h₂.trans h₁) ρ X,
    ← S.trace_mul_incl h₁ ρ (N.incl h₂ X), N.incl_trans h₂ h₁ X]

/-- The **matrix Kraus operators** of the transported marginal: `Kⱼ = ⟨the matrix of the adjoint of
the partial-trace Kraus operator `Vⱼ` of `decompᵢ h`⟩`, in the standard orthonormal bases. -/
noncomputable def restrictKraus {Λ Λ' : Finset sites} (h : Λ ⊆ Λ')
    (j : Fin (Module.finrank ℂ (ℋ (Λ' \ Λ)))) :
    Matrix (Fin (Module.finrank ℂ (ℋ Λ))) (Fin (Module.finrank ℂ (ℋ Λ'))) ℂ :=
  LinearMap.toMatrix (stdOrthonormalBasis ℂ (ℋ Λ')).toBasis (stdOrthonormalBasis ℂ (ℋ Λ)).toBasis
    (LinearMap.adjoint (LinearMap.ptKraus (S.decompᵢ h) j))

/-- **Matrix Kraus form of the marginal**: under the matrix representation, `restrict h` acts as
`M ↦ ∑ⱼ Kⱼ M Kⱼᴴ`. Transports the operator Kraus form `partialTrace_eq_sum_kraus`; exhibits the
transported marginal as a completely positive map. -/
theorem toMatrix_restrict_eq_sum_kraus {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (ρ : N.algebra Λ') :
    S.toMatrix Λ (S.restrict h ρ)
      = ∑ j, S.restrictKraus h j * S.toMatrix Λ' ρ * (S.restrictKraus h j)ᴴ := by
  have hact : S.act Λ (S.restrict h ρ)
      = LinearMap.partialTrace (S.decompᵢ h).toLinearEquiv (S.act Λ' ρ) := by
    rw [restrict_apply, AlgEquiv.apply_symm_apply, S.decompᵢ_toLinearEquiv h]
  -- `toMatrixOrthonormal` is the matrix in the standard ON basis (clean `LinearMap.toMatrix` form).
  have htmo : ∀ {Λ₀ : Finset sites} (g : Module.End ℂ (ℋ Λ₀)),
      LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ (ℋ Λ₀)) g
        = LinearMap.toMatrix (stdOrthonormalBasis ℂ (ℋ Λ₀)).toBasis
            (stdOrthonormalBasis ℂ (ℋ Λ₀)).toBasis g := fun g => rfl
  -- `(restrictKraus h j)ᴴ` is the matrix of the Kraus operator `Vⱼ` itself.
  have hKt : ∀ j, (S.restrictKraus h j)ᴴ
      = LinearMap.toMatrix (stdOrthonormalBasis ℂ (ℋ Λ)).toBasis
          (stdOrthonormalBasis ℂ (ℋ Λ')).toBasis (LinearMap.ptKraus (S.decompᵢ h) j) := by
    intro j
    rw [restrictKraus, LinearMap.toMatrix_adjoint, Matrix.conjTranspose_conjTranspose]
  rw [toMatrix_apply, hact, LinearMap.partialTrace_eq_sum_kraus, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hKt j, restrictKraus, toMatrix_apply]
  simp only [htmo]
  rw [LinearMap.toMatrix_comp (stdOrthonormalBasis ℂ (ℋ Λ)).toBasis
      (stdOrthonormalBasis ℂ (ℋ Λ')).toBasis (stdOrthonormalBasis ℂ (ℋ Λ)).toBasis,
    LinearMap.toMatrix_comp (stdOrthonormalBasis ℂ (ℋ Λ)).toBasis
      (stdOrthonormalBasis ℂ (ℋ Λ')).toBasis (stdOrthonormalBasis ℂ (ℋ Λ')).toBasis,
    Matrix.mul_assoc]

end LocalNet.Split
