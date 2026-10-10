# QuantumSystem

A Lean 4 formalization of quantum systems from an operator-algebraic perspective.

> [!WARNING]
> This project is a work in progress. Breaking API changes — renamed or
> removed declarations, changed signatures, and reorganized modules — happen
> frequently without deprecation.

> [!NOTE]
> This project is currently not accepting contributors because the following areas still need to be addressed:
>
> * Contributing guidelines (including an AI policy)
> * Repository scope and roadmap, including what should and should not be included
> * Release workflow
> * Documentation (including Lean Blueprint)

## Highlights

Notable results formalized in this repository include:

### C\*-algebras

- **Gelfand–Naimark theorem.** Every (possibly non-unital) C\*-algebra A is isometrically \*-isomorphic onto a norm-closed \*-subalgebra of B(H), realized on the direct sum of the GNS spaces of all pure states; when A is unital, the representation can be taken unital; when A is separable, a countable norming family of pure states gives a separable H.
  - [`Analysis/CStarAlgebra/GelfandNaimark.lean`](QuantumSystem/Analysis/CStarAlgebra/GelfandNaimark.lean) · `CStarRep.exists_starAlgEquiv_range` · `CStarRep.exists_isometric_unital` · `CStarRep.exists_isometric_separable`
- **GNS construction.** For a state ω, the cyclic representation (π_ω, H_ω, Ω_ω) satisfies ω(a) = ⟨Ω_ω, π_ω(a) Ω_ω⟩ with Ω_ω a cyclic unit vector.
  - [`Analysis/CStarAlgebra/GNS/Construction.lean`](QuantumSystem/Analysis/CStarAlgebra/GNS/Construction.lean) · `GNS.Representation.canonical` (`GNS[ω]`)
  - [`Analysis/CStarAlgebra/GNS/Representation.lean`](QuantumSystem/Analysis/CStarAlgebra/GNS/Representation.lean) · `GNS.Representation.gns_condition` · `GNS.Representation.cyclic` · `GNS.Representation.norm_ξ_eq_one`

### Von Neumann algebras

- **Bicommutant theorem.** For a non-degenerate (possibly non-unital) \*-subalgebra A ⊆ B(H): A = A″ ⟺ A is WOT-closed ⟺ A is SOT-closed.
  - [`Analysis/VonNeumannAlgebra/DoubleCommutant/TFAE.lean`](QuantumSystem/Analysis/VonNeumannAlgebra/DoubleCommutant/TFAE.lean) · `DoubleCommutant.bicommutant_tfae` · `DoubleCommutant.bicommutant_tfae_starSubalgebra`
- **Type I factors.** For a factor N ⊆ B(H) and every minimal projection e of N, N is unitarily B(ℓ²(F)) ⊗̄ 1 on ℓ²(F) ⊗̂ eH, with N′ ↦ 1 ⊗̄ B(eH); for a split inclusion A ≤ N ≤ B the same unitary sends A into B(ℓ²(F)) ⊗̄ 1 and B′ into 1 ⊗̄ B(eH). A type I factor has such an e, so both decompositions hold for some e.
  - [`Analysis/VonNeumannAlgebra/TypeI/StructureTheorem.lean`](QuantumSystem/Analysis/VonNeumannAlgebra/TypeI/StructureTheorem.lean) · `VonNeumannAlgebra.IsFactor.exists_spatial_tensor_decomposition` · `VonNeumannAlgebra.IsFactor.exists_split_tensor_decomposition`
  - [`Analysis/VonNeumannAlgebra/TypeI/Basic.lean`](QuantumSystem/Analysis/VonNeumannAlgebra/TypeI/Basic.lean) · `VonNeumannAlgebra.IsTypeIFactor.exists_spatial_tensor_decomposition` · `VonNeumannAlgebra.IsTypeIFactor.exists_split_tensor_decomposition`
- **Relative Tomita operator.** S_{η,ξ} : xξ + ζ ↦ s(ξ) x\* η (x ∈ M, ζ ⊥ [Mξ]) is a closable, densely defined conjugate-linear operator.
  - [`Analysis/VonNeumannAlgebra/Modular/RelativeTomita.lean`](QuantumSystem/Analysis/VonNeumannAlgebra/Modular/RelativeTomita.lean) · `VonNeumannAlgebra.isClosable_relativeTomita`
- **Relative modular operator.** Δ_{η,ξ} = S̄†S̄ is positive self-adjoint (von Neumann's theorem; no Tomita–Takesaki theory needed). Support theorem: μ_ξ{0} = 0 ⟺ s(ξ) ≤ s(η).
  - [`Analysis/VonNeumannAlgebra/Modular/RelativeModular.lean`](QuantumSystem/Analysis/VonNeumannAlgebra/Modular/RelativeModular.lean) · `VonNeumannAlgebra.relativeModular` · `VonNeumannAlgebra.isSelfAdjoint_relativeModular` · `VonNeumannAlgebra.isPositive_relativeModular` · `VonNeumannAlgebra.measure_pvm_relativeModular_singleton_zero_eq_zero_iff`

### Completely positive maps

- **Choi's theorem.** For linear Φ : M_n(ℂ) → M_m(ℂ): Φ is CP ⟺ Φ is k-positive, i.e. id_k ⊗ Φ is positive on kn × kn matrices, for any single k ≥ min(n, m) ⟺ J(Φ) ⪰ 0 ⟺ Φ(A) = Σₐ Kₐ A Kₐ†; a CP map has a Kraus representation with rank J(Φ) operators, the minimum.
  - [`Analysis/Matrix/CompletelyPositiveMap/Choi.lean`](QuantumSystem/Analysis/Matrix/CompletelyPositiveMap/Choi.lean) · `CompletelyPositiveMap.exists_coe_eq_iff_posSemidef_choiMatrix` · `CompletelyPositiveMap.exists_coe_eq_iff_exists_kPositiveMap` · `CompletelyPositiveMap.exists_coe_eq_iff_forall_posSemidef_comp_map` · `CompletelyPositiveMap.exists_coe_eq_iff_exists_kraus` · `CompletelyPositiveMap.exists_kraus_rank`
- **Stinespring's theorem.** A CP map φ : A → B(H) on a (possibly non-unital) C\*-algebra is φ(a) = V† π(a) V for a \*-representation π on a Hilbert space K and V : H → K with the span of the π(a)Vξ dense in K and ‖V‖² = ‖φ‖; for matrices, Φ : M_n(ℂ) → M_m(ℂ) is CP ⟺ Φ(A) = tr₂(V A V†) with an environment of the minimal dimension rank J(Φ); for Φ : B(H) → B(K) with H, K finite-dimensional, Φ is CPTP (a quantum channel) ⟺ Φ(A) = tr₂(V A V†), equivalently Φ\*(B) = V†(B ⊗ 1)V, with V†V = 1 and an environment of dimension rank J(Φ) (the Choi operator in an orthonormal basis of H).
  - [`ForMathlib/Analysis/CStarAlgebra/Stinespring.lean`](QuantumSystem/ForMathlib/Analysis/CStarAlgebra/Stinespring.lean) · `CompletelyPositiveMap.exists_stinespring_dilation`
  - [`Analysis/Matrix/CompletelyPositiveMap/Stinespring.lean`](QuantumSystem/Analysis/Matrix/CompletelyPositiveMap/Stinespring.lean) · `CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespringMatrix` · `Matrix.rank_choiMatrix_le_card_of_stinespring`
  - [`Analysis/CStarAlgebra/CompletelyPositiveMap/Stinespring.lean`](QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Stinespring.lean) · `CPTPMap.exists_coe_eq_iff_exists_stinespring` · `CPTPMap.exists_traceDual_eq_stinespring`
  - [`Analysis/InnerProductSpace/PartialTrace.lean`](QuantumSystem/Analysis/InnerProductSpace/PartialTrace.lean) · `ContinuousLinearMap.traceDual_eq_iff_traceRight`

### Operator analysis

- **Jensen's operator inequality.** For f operator convex on s and Σᵢ aᵢ\*aᵢ = 1 in a unital C\*-algebra, f(Σᵢ aᵢ\* xᵢ aᵢ) ≤ Σᵢ aᵢ\* f(xᵢ) aᵢ for self-adjoint xᵢ with spectrum in s; for Σᵢ aᵢ\*aᵢ ≤ 1 when moreover 0 ∈ s and f(0) ≤ 0 (Hansen–Pedersen). Operator convexity follows Hansen–Pedersen and requires continuity: f is operator convex ⟺ f is continuous and matrix convex, and it does not depend on the universe of the C\*-algebras; the continuity requirement is not redundant, since the indicator of {0} is matrix convex on [0, ∞) although it is discontinuous at 0.
  - [`ForMathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/OperatorConvex.lean`](QuantumSystem/ForMathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/OperatorConvex.lean) · `IsOperatorConvexOn.cfc_sum_le` · `IsOperatorConvexOn.cfc_sum_le_of_le_one` · `isMatrixConvexOn_indicator_zero` · `not_isOperatorConvexOn_indicator_zero`
  - [`Analysis/CStarAlgebra/OperatorConvex.lean`](QuantumSystem/Analysis/CStarAlgebra/OperatorConvex.lean) · `isOperatorConvexOn_iff_continuousOn_and_isMatrixConvexOn` · `isOperatorConvexOn_congr_universe`
- **Lieb concavity.** For finite-dimensional H, K, T : H → K and p, q ≥ 0 with p + q ≤ 1, (A, B) ↦ Tr(Aᵖ T† B^q T) is jointly concave on pairs of positive operators A on H and B on K (Effros' perspective proof for p + q = 1, extended to p + q ≤ 1).
  - [`Analysis/CStarAlgebra/LiebConcavity.lean`](QuantumSystem/Analysis/CStarAlgebra/LiebConcavity.lean) · `ContinuousLinearMap.lieb_concaveOn`
- **Spectral measures.** For self-adjoint unbounded A, the projection-valued measure E_A on ℝ, transported from that of the resolvent (i − A)⁻¹ (itself built via Riesz–Markov–Kakutani and polarization), and its diagonal measures μ_u = ⟨E_A(·) u, u⟩, with ⟨u, (z − A)⁻¹ u⟩ = ∫ (z − λ)⁻¹ dμ_u(λ) for z in the resolvent set.
  - [`Analysis/SpectralTheory/SpectralMeasure.lean`](QuantumSystem/Analysis/SpectralTheory/SpectralMeasure.lean) · `IsSelfAdjoint.pvm` · `IsSelfAdjoint.inner_resolvent_eq_integral`

### Entropy

- **Von Neumann entropy.** For a state ω on B(H), H finite-dimensional, with density ρ: S(ω) = −Tr ρ log ρ satisfies 0 ≤ S(ω) ≤ log dim H, with S(ω) = log dim H ⟺ ω is the maximally mixed state Tr(·)/dim H, and S is concave on the state space.
  - [`InformationTheory/Entropy/VonNeumann/Basic.lean`](QuantumSystem/InformationTheory/Entropy/VonNeumann/Basic.lean) · `State.vonNeumannEntropy_nonneg` · `State.vonNeumannEntropy_le_log_finrank` · `State.vonNeumannEntropy_eq_log_finrank_iff` · `StateSpace.concaveOn_vonNeumannEntropy`
- **Umegaki's formula.** For positive functionals ψ, φ on B(H) (any mass) with densities ρ, σ, D(ψ‖φ) := S(ψ‖φ) (Araki) equals Tr ρ (log ρ − log σ) if the null ideal of φ lies in that of ψ (supp ψ ⊆ supp φ), and +∞ otherwise.
  - [`InformationTheory/Entropy/Umegaki/Basic.lean`](QuantumSystem/InformationTheory/Entropy/Umegaki/Basic.lean) · `umegakiEntropy_eq_ite`
- **Monotonicity and joint convexity.** D(ψ ∘ α‖φ ∘ α) ≤ D(ψ‖φ) for every unital Schwarz map α, in particular every unital 2-positive map and the trace dual of every quantum channel Φ, i.e. D(Φ(ρ)‖Φ(σ)) ≤ D(ρ‖σ); D is jointly convex, D(Σᵢ wᵢ ψᵢ‖Σᵢ wᵢ φᵢ) ≤ Σᵢ wᵢ D(ψᵢ‖φᵢ) for weights wᵢ ≥ 0.
  - [`InformationTheory/Entropy/Umegaki/Monotonicity.lean`](QuantumSystem/InformationTheory/Entropy/Umegaki/Monotonicity.lean) · `umegakiEntropy_comp_le` · `CPTPMap.umegakiEntropy_comp_traceDual_le`
  - [`InformationTheory/Entropy/Umegaki/JointConvexity.lean`](QuantumSystem/InformationTheory/Entropy/Umegaki/JointConvexity.lean) · `umegakiEntropy_jointly_convex`
- **Mutual information.** For a state ω on B(H ⊗ K) with marginals ω_A, ω_B: D(ω‖ω_A ⊗ ω_B) = I(A:B) ≥ 0, i.e. S(ω) ≤ S(ω_A) + S(ω_B).
  - [`InformationTheory/Entropy/VonNeumann/MutualInformation.lean`](QuantumSystem/InformationTheory/Entropy/VonNeumann/MutualInformation.lean) · `State.umegakiEntropy_eq_mutualInformation` · `State.mutualInformation_nonneg`
- **Strong subadditivity.** For every state ω on B((A ⊗ B) ⊗ C): S(ω_AB) + S(ω_BC) ≥ S(ω) + S(ω_B).
  - [`InformationTheory/Entropy/VonNeumann/StrongSubadditivity.lean`](QuantumSystem/InformationTheory/Entropy/VonNeumann/StrongSubadditivity.lean) · `State.vonNeumannEntropy_strong_subadditivity`
- **Araki relative entropy of vectors.** S(ω_ξ‖ω_η) = −⟨ξ, log Δ_{η,ξ} ξ⟩, defined as −∫ log λ dμ_ξ(λ) ∈ EReal.
  - [`InformationTheory/Entropy/Araki/VectorFunctional.lean`](QuantumSystem/InformationTheory/Entropy/Araki/VectorFunctional.lean) · `VonNeumannAlgebra.arakiVec`
- **Araki relative entropy of normal functionals.** S(ψ‖φ) via vector representatives on the amplification ℓ²(ℕ) ⊗̂ H (in place of natural-cone vectors); independent of the representatives.
  - [`InformationTheory/Entropy/Araki/Basic.lean`](QuantumSystem/InformationTheory/Entropy/Araki/Basic.lean) · `VonNeumannAlgebra.arakiEntropy` · `VonNeumannAlgebra.arakiEntropy_eq_arakiVec`
- **Data-processing inequality.** S(ψ ∘ α‖φ ∘ α) ≤ S(ψ‖φ) for unital normal Schwarz maps α (Petz's resolvent argument).
  - [`InformationTheory/Entropy/Araki/Monotonicity.lean`](QuantumSystem/InformationTheory/Entropy/Araki/Monotonicity.lean) · `VonNeumannAlgebra.arakiEntropy_comp_le`
