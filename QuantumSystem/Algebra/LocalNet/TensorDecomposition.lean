module

public import QuantumSystem.Algebra.LocalNet.Net
public import QuantumSystem.ForMathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The split property and the tensor decomposition of a local net

This file implements the **split property** for an abstract local net `LocalNet` and derives,
*without committing to any particular representation*, the **tensor factorisation of the action
space** and the **partial trace** that it induces.

In the operator-algebraic literature the split property of an inclusion `𝔄(Λ) ⊆ 𝔄(Λ')` is the
existence of an intermediate type I factor `𝔄(Λ) ⊆ N ⊆ 𝔄(Λ')`; in its spatial / standard form
(Doplicher–Longo standard split inclusion, Fewster 2016 eqns (12)–(13), Matsui 2011 eqns
(2.1)–(2.2)) this is equivalent to a factorisation of the Hilbert space the algebra acts on,
`ℋ Λ' ≅ ℋ Λ ⊗ ℋ (Λ' ∖ Λ)`, under which `𝔄(Λ)` acts as `B(ℋ Λ) ⊗ 1`. We take this spatial form as
the definition: a `Split` structure assigns to each region a finite-dimensional action space
`ℋ Λ`, identifies `𝔄(Λ)` with the type I factor `End ℂ (ℋ Λ)` (`act`), and presents each isotony
embedding `incl h` as the **ampliation** `X ↦ X ⊗ 1` along a tensor factorisation `decomp h`
(`act_incl`).

From this hypothesis we derive the consequences that the literature uses:

* `Split.decomp` is the tensor factorisation of the action space itself;
* `Split.partialTrace` is the partial trace on the action space (trace out the complementary
  factor), reusing `LinearMap.partialTrace` from `ForMathlib.LinearAlgebra.Trace`;
* `Split.restrict` transports it to a marginal map `𝔄(Λ') →ₗ 𝔄(Λ)` on the algebra;
* `Split.restrict_incl_mul` is the conditional-expectation / partial-trace pull-out
  `restrict (incl x * y) = x * restrict y`, the algebraic heart of statistical independence.

None of this requires von Neumann algebra theory: the partial trace and the ampliation are the
purely linear-algebraic operators of `ForMathlib.LinearAlgebra.Trace`, parameterised by the
explicit decomposition `decomp h`. The split factorisation is carried as spatial data on the
abstract net (`act`/`decomp`/`act_incl`/`act_incl_compl`), not committed to any concrete model.

## References

* Matsui 2011 (`https://arxiv.org/abs/1109.5778`) §2, eqns (2.1)–(2.4).
* Fewster 2016 (`https://arxiv.org/abs/1601.06936`) eqns (12)–(13).
-/

@[expose] public section

open scoped TensorProduct

namespace LocalNet

variable {sites : Type*} [DecidableEq sites]

/-- A **split structure** on a local net `N` over a family of finite-dimensional action spaces
`ℋ`: the spatial form of the split property. Each local algebra is identified with the type I
factor of operators on its action space (`act : 𝔄(Λ) ≃ₐ End ℂ (ℋ Λ)`), and each isotony
embedding is the ampliation `X ↦ X ⊗ 1` along a tensor factorisation of the action space
`decomp h : ℋ Λ' ≃ₗ ℋ Λ ⊗ ℋ (Λ' ∖ Λ)` (`act_incl`). This is the Doplicher–Longo standard split
inclusion (Fewster 2016 eqns (12)–(13)) / Matsui 2011 eqn (2.2) read as a hypothesis: it holds for
some nets and fails for others, and there is no universal proof, so it is carried as data. -/
structure Split (N : LocalNet sites) (ℋ : Finset sites → Type*)
    [∀ Λ, NormedAddCommGroup (ℋ Λ)] [∀ Λ, InnerProductSpace ℂ (ℋ Λ)]
    [∀ Λ, FiniteDimensional ℂ (ℋ Λ)] where
  /-- Each local algebra `𝔄(Λ)` is the type I factor `End ℂ (ℋ Λ)` of operators on its action
      space, `*`-isomorphically (the `*`-structure is recorded by `act_star`). -/
  act : ∀ Λ, N.algebra Λ ≃ₐ[ℂ] Module.End ℂ (ℋ Λ)
  /-- `act` is a `*`-isomorphism: it intertwines the C⋆-involution of `𝔄(Λ)` with the adjoint on
      `End ℂ (ℋ Λ)`. Together with `act` this is the spatial split property's type I identification
      `𝔄(Λ) ≅ B(ℋ Λ)` as C⋆-algebras (not merely as algebras). -/
  act_star : ∀ {Λ : Finset sites} (x : N.algebra Λ), act Λ (star x) = star (act Λ x)
  /-- The **tensor factorisation of the action space** `ℋ Λ' ≅ ℋ Λ ⊗ ℋ (Λ' ∖ Λ)` for an
      inclusion `Λ ⊆ Λ'`. This is the spatial content of the split property. -/
  decomp : ∀ {Λ Λ' : Finset sites}, Λ ⊆ Λ' → (ℋ Λ' ≃ₗ[ℂ] ℋ Λ ⊗[ℂ] ℋ (Λ' \ Λ))
  /-- The factorisation is a **unitary** (norm-preserving): the Hilbert space splits *isometrically*
      as `ℋ Λ' ≅ ℋ Λ ⊗ ℋ (Λ' ∖ Λ)`. This is what makes the induced marginal a quantum channel
      (the partial trace of a positive operator stays positive); see `decompᵢ`. -/
  decomp_norm : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : ℋ Λ'), ‖decomp h x‖ = ‖x‖
  /-- **Isotony is the ampliation**: under the identification `act`, the isotony embedding
      `incl h` acts as `X ↦ X ⊗ 1` along the factorisation `decomp h` (Matsui eqn (2.2)). -/
  act_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
      act Λ' (N.incl h x) = LinearMap.ampliate (decomp h) (act Λ x)
  /-- **The complementary region acts on the complementary factor**: under the identification
      `act`, the isotony embedding of the complement `Λ' ∖ Λ` acts as `Y ↦ 1 ⊗ Y` along the
      factorisation `decomp h`. This is the second half of the spatial split property (Fewster 2016
      eqns (12)–(13)): the standard split inclusion factorises `ℋ Λ'` so that *both* `𝔄(Λ)` and
      `𝔄(Λ' ∖ Λ)` act canonically on their respective tensor factors. It is genuine spatial data:
      the bare net axioms and `act_incl` pin the complement action only up to an inner unitary on
      the complementary factor (Skolem–Noether), and this field fixes that gauge to the canonical
      one, as the standard-form factorisation does. -/
  act_incl_compl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (y : N.algebra (Λ' \ Λ)),
      act Λ' (N.incl Finset.sdiff_subset y) = LinearMap.coampliate (decomp h) (act (Λ' \ Λ) y)

namespace Split

variable {N : LocalNet sites} {ℋ : Finset sites → Type*}
  [∀ Λ, NormedAddCommGroup (ℋ Λ)] [∀ Λ, InnerProductSpace ℂ (ℋ Λ)]
  [∀ Λ, FiniteDimensional ℂ (ℋ Λ)]
  (S : Split N ℋ)

/-- The tensor factorisation `decomp h` as a **unitary** (`LinearIsometryEquiv`), using the
norm-preservation witness `decomp_norm`. This is the Hilbert-space tensor isometry
`U : ℋ Λ' ≃ₗᵢ ℋ Λ ⊗ ℋ (Λ' ∖ Λ)` of the spatial split property (Fewster 2016 eqn (13)). -/
noncomputable def decompᵢ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') :
    ℋ Λ' ≃ₗᵢ[ℂ] ℋ Λ ⊗[ℂ] ℋ (Λ' \ Λ) :=
  { S.decomp h with norm_map' := S.decomp_norm h }

@[simp] theorem decompᵢ_toLinearEquiv {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') :
    (S.decompᵢ h).toLinearEquiv = S.decomp h :=
  rfl

/-- The **partial trace on the action space** induced by the split factorisation: trace out the
complementary factor `ℋ (Λ' ∖ Λ)` and retain `ℋ Λ`. This is `LinearMap.partialTrace` paired with
the tensor decomposition `decomp h`. -/
noncomputable def partialTrace {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') :
    Module.End ℂ (ℋ Λ') →ₗ[ℂ] Module.End ℂ (ℋ Λ) :=
  LinearMap.partialTrace (S.decomp h)

/-- The **marginal map** `𝔄(Λ') →ₗ 𝔄(Λ)` of the net: the partial trace on the action space
transported to the algebra along `act`. This is the abstract, representation-free analogue of
`Matrix.restrict` (partial trace of a density matrix onto the subregion). -/
noncomputable def restrict {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') :
    N.algebra Λ' →ₗ[ℂ] N.algebra Λ :=
  (S.act Λ).symm.toLinearMap ∘ₗ LinearMap.partialTrace (S.decomp h) ∘ₗ (S.act Λ').toLinearMap

theorem restrict_apply {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (y : N.algebra Λ') :
    S.restrict h y = (S.act Λ).symm (LinearMap.partialTrace (S.decomp h) (S.act Λ' y)) :=
  rfl

/-- **Partial-trace pull-out** (conditional-expectation property): tracing the complement out of
`incl h x * y` factors the embedded `x` out of the marginal,
`restrict h (incl h x * y) = x * restrict h y`. This is the algebraic heart of the statistical
independence supplied by the split property (Fewster 2016 eqn (3)); it is the Heisenberg-picture
trace identity `Tr_B((X ⊗ 1) · ρ) = X · Tr_B ρ` (`LinearMap.partialTrace_ampliate_mul`)
transported to the net. -/
theorem restrict_incl_mul {Λ Λ' : Finset sites} (h : Λ ⊆ Λ')
    (x : N.algebra Λ) (y : N.algebra Λ') :
    S.restrict h (N.incl h x * y) = x * S.restrict h y := by
  rw [restrict_apply, restrict_apply, map_mul (S.act Λ'), S.act_incl h x,
    LinearMap.partialTrace_ampliate_mul, map_mul (S.act Λ).symm, AlgEquiv.symm_apply_apply]

end Split

end LocalNet
