/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.InnerProductSpace.StandardSubspace.Tomita
public import QuantumSystem.Analysis.VonNeumannAlgebra.Modular.RelativeModular
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The standard subspace of a cyclic and separating vector

Let `M` be a von Neumann algebra on `H` and `Ω ∈ H` a vector that is **cyclic** (`[M Ω] = H`,
`InnerProductSpace.IsCyclicVector`) and **separating** (`x Ω = 0` forces `x = 0` for `x ∈ M`,
`InnerProductSpace.IsSeparatingVector`). A vector is separating for `M` iff it is cyclic for the
commutant `M′` (`VonNeumannAlgebra.isSeparatingVector_iff_isCyclicVector_commutant`). The closed
real subspace
`H_M = closure {x Ω | x ∈ M, x⋆ = x}`
is then a standard subspace (`VonNeumannAlgebra.standardSubspace`): `H_M + i H_M ⊇ M Ω` is dense,
and `H_M ∩ i H_M = 0` because `H_M` is symplectically orthogonal to `H_{M′}`, which is cyclic in
turn. (In fact `H_{M′} = (H_M)'`; this needs the adjoint of the Tomita operator and is
`VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp`, in
`QuantumSystem.Analysis.VonNeumannAlgebra.Modular.TomitaAdjoint`.)

The Tomita–Takesaki objects of `(M, Ω)` are those of `H_M`. The Tomita operator
`S_{Ω,Ω} : x Ω ↦ x⋆ Ω` (`VonNeumannAlgebra.relativeTomita M Ω Ω`, with `s(Ω) = 1`) has the Tomita
operator `S_{H_M} : a + i b ↦ a - i b` of the standard subspace as its closure
(`VonNeumannAlgebra.closure_relativeTomita_self_eq_tomita`); consequently the modular operator
`Δ_{Ω,Ω} = S̄†S̄` (`VonNeumannAlgebra.relativeModular M Ω Ω`) is the modular operator `Δ_{H_M}`
(`VonNeumannAlgebra.relativeModular_self_eq_modular`), and the modular conjugation and the modular
group of `(M, Ω)` are `J_{H_M}` and `Δ_{H_M}^{it}`.

A bounded `V : H₁ → H₂` with `V† Ω₂ = Ω₁` and `V M₁ V† ⊆ M₂` maps `H_{M₁}` into `H_{M₂}`
(`VonNeumannAlgebra.apply_mem_standardSubspace_of_adjoint_apply`); this is how the standard
subspace results (Borchers' theorems, `QuantumSystem.Analysis.VonNeumannAlgebra.Modular.Borchers`)
apply to von Neumann algebras.

## Main definitions

* `VonNeumannAlgebra.selfAdjointOrbit M Ω` — the real subspace `{x Ω | x ∈ M, x⋆ = x}`.
* `VonNeumannAlgebra.standardSubspace M Ω hc hs`, written `H[M, Ω]` — the standard subspace `H_M`
  of a cyclic and separating vector (Longo's `H_M`, with `Ω` made explicit). The hypotheses are
  default arguments, found in the context by the tactic `cyclic_separating`, also for `M′`.

## Main results

* `VonNeumannAlgebra.isSeparatingVector_iff_isCyclicVector_commutant`,
  `VonNeumannAlgebra.isCyclicVector_iff_isSeparatingVector_commutant` — `Ω` is separating
  (cyclic) for `M` iff it is cyclic (separating) for `M′`.
* `VonNeumannAlgebra.closure_relativeTomita_self_eq_tomita` — `S̄_{Ω,Ω} = S_{H_M}`.
* `VonNeumannAlgebra.relativeModular_self_eq_modular`, `VonNeumannAlgebra.relativeModularGroup_self` —
  `Δ_{Ω,Ω} = Δ_{H_M}` and `Δ_{Ω,Ω}^{it} = Δ_{H_M}^{it}`.
* `VonNeumannAlgebra.apply_mem_standardSubspace_of_adjoint_apply` — a bounded `V` with
  `V† Ω₂ = Ω₁` and `V M₁ V† ⊆ M₂` maps `H_{M₁}` into `H_{M₂}`.

## TODO

* Tomita's theorem `J M J = M′`, `Δ^{it} M Δ^{-it} = M` for von Neumann algebras, the modular
  automorphism group of `M` and the KMS condition of `ω_Ω`.

## Notation

`H[M, Ω]` is `VonNeumannAlgebra.standardSubspace M Ω hc hs`, the standard subspace
`H_M = closure {x Ω | x ∈ M, x⋆ = x}`; the proofs `hc hs` are found in the context by
`cyclic_separating`, also for `M′`. Activate it with `open scoped VonNeumannAlgebra`.

## References

* O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, Springer
  (1987), Proposition 2.5.3 and §2.5.2
* [R. Longo, *Lectures on Conformal Nets, Part I*](https://www.mat.uniroma2.it/longo/Lecture-Notes_files/LN-Part1.pdf),
  §2.1
-/

@[expose] public section

open Set Filter Topology Complex ClosedSubmodule
open scoped InnerProductSpace ComplexConjugate VonNeumannAlgebra LinearPMap StandardSubspace
open scoped InnerProduct
  ComplexStarModule
open InnerProductSpace (cyclicSubspace IsCyclicVector IsSeparatingVector isCyclicVector_iff)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω : H)

/-! ### Cyclic and separating vectors -/

variable {M Ω}

/-- A vector is separating for `M` iff it is cyclic for the commutant `M′` (Bratteli–Robinson,
Proposition 2.5.3): the support `s(Ω) ∈ M` is the projection onto `[M′ Ω]`, and `1 - s(Ω)`
annihilates `Ω`. -/
theorem isSeparatingVector_iff_isCyclicVector_commutant :
    IsSeparatingVector M Ω ↔ IsCyclicVector M′ Ω := by
  refine ⟨fun h => supportProj_eq_one_iff.mp ?_, fun h x hx hxΩ => ?_⟩
  · have h1 := h (1 - M.supportProj Ω) (sub_mem (one_mem M) (M.supportProj_mem Ω))
      (by rw [sub_apply, one_apply_eq_self, supportProj_apply_self, sub_self])
    exact (sub_eq_zero.mp h1).symm
  · have hsub : (cyclicSubspace M′ Ω : Set H) ⊆ {v | x v = 0} :=
      cyclicSubspace_subset (M := M′) (isClosed_eq x.continuous continuous_const) fun y hy => by
        change x (y Ω) = 0
        rw [← apply_apply_of_mem_commutant hy hx, hxΩ, map_zero]
    ext v
    exact hsub (h.mem v)

/-- A vector is cyclic for `M` iff it is separating for the commutant `M′`. -/
lemma isCyclicVector_iff_isSeparatingVector_commutant :
    IsCyclicVector M Ω ↔ IsSeparatingVector M′ Ω := by
  rw [isSeparatingVector_iff_isCyclicVector_commutant, commutant_commutant]

/-- A separating vector for `M` is cyclic for `M′`. -/
lemma _root_.InnerProductSpace.IsSeparatingVector.isCyclicVector_commutant (hs : IsSeparatingVector M Ω) :
    IsCyclicVector M′ Ω :=
  isSeparatingVector_iff_isCyclicVector_commutant.mp hs

/-- A cyclic vector for `M` is separating for `M′`. -/
lemma _root_.InnerProductSpace.IsCyclicVector.isSeparatingVector_commutant (hc : IsCyclicVector M Ω) :
    IsSeparatingVector M′ Ω :=
  isCyclicVector_iff_isSeparatingVector_commutant.mp hc

/-! ### The real subspace of self-adjoint elements applied to `Ω` -/

variable (M Ω) in
/-- The real subspace `{x Ω | x ∈ M, x⋆ = x}`, whose closure is the standard subspace `H_M`. -/
def selfAdjointOrbit : Submodule ℝ H where
  carrier := {v | ∃ x ∈ M, IsSelfAdjoint x ∧ x Ω = v}
  add_mem' := by
    rintro _ _ ⟨x, hx, hxs, rfl⟩ ⟨y, hy, hys, rfl⟩
    exact ⟨x + y, add_mem hx hy, hxs.add hys, by rw [add_apply]⟩
  zero_mem' := ⟨0, zero_mem M, .zero _, zero_apply _⟩
  smul_mem' := by
    rintro r _ ⟨x, hx, hxs, rfl⟩
    refine ⟨(r : ℂ) • x, SMulMemClass.smul_mem _ hx, ?_, by rw [smul_apply, Complex.coe_smul]⟩
    rw [IsSelfAdjoint, star_smul, hxs.star_eq, Complex.star_def, conj_ofReal]

/-- `v ∈ M_sa Ω` iff `v = x Ω` for a self-adjoint `x ∈ M`. -/
lemma mem_selfAdjointOrbit {v : H} :
    v ∈ M.selfAdjointOrbit Ω ↔ ∃ x ∈ M, IsSelfAdjoint x ∧ x Ω = v :=
  Iff.rfl

/-- The real part `(x + x⋆)/2` of an element of `M` lies in `M`. -/
private lemma realPart_mem {x : H →L[ℂ] H} (hx : x ∈ M) : (ℜ x : H →L[ℂ] H) ∈ M := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  exact SMulMemClass.smul_mem _ (add_mem hx (star_mem hx))

/-- The imaginary part `(x - x⋆)/2i` of an element of `M` lies in `M`. -/
private lemma imaginaryPart_mem {x : H →L[ℂ] H} (hx : x ∈ M) : (ℑ x : H →L[ℂ] H) ∈ M := by
  rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
  exact SMulMemClass.smul_mem _ (SMulMemClass.smul_mem _ (sub_mem hx (star_mem hx)))

/-- `x Ω = a + i b` and `x⋆ Ω = a - i b` with `a = (ℜ x) Ω` and `b = (ℑ x) Ω` in
`{y Ω | y ∈ M, y⋆ = y}`. -/
private lemma exists_apply_eq_add {x : H →L[ℂ] H} (hx : x ∈ M) :
    ∃ a ∈ M.selfAdjointOrbit Ω, ∃ b ∈ M.selfAdjointOrbit Ω,
      x Ω = a + I • b ∧ star x Ω = a - I • b := by
  refine ⟨(ℜ x : H →L[ℂ] H) Ω, ⟨_, realPart_mem hx, (ℜ x).2, rfl⟩,
    (ℑ x : H →L[ℂ] H) Ω, ⟨_, imaginaryPart_mem hx, (ℑ x).2, rfl⟩, ?_, ?_⟩
  · conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    rw [add_apply, smul_apply]
  · conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    rw [star_add, star_smul, (ℜ x).2.star_eq, (ℑ x).2.star_eq, Complex.star_def, conj_I,
      add_apply, smul_apply, neg_smul, ← sub_eq_add_neg]

/-- **`H_M` and `H_{M′}` are symplectically orthogonal**: `im ⟪x Ω, y Ω⟫ = 0` for self-adjoint
`x ∈ M` and `y ∈ M′`, since `⟪x Ω, y Ω⟫ = ⟪Ω, x y Ω⟫` and `x y = y x` is self-adjoint. -/
private lemma im_inner_eq_zero {u v : H} (hu : u ∈ M.selfAdjointOrbit Ω)
    (hv : v ∈ M′.selfAdjointOrbit Ω) : (⟪u, v⟫_ℂ).im = 0 := by
  obtain ⟨x, hx, hxs, rfl⟩ := hu
  obtain ⟨y, hy, hys, rfl⟩ := hv
  have hxy : x * y = y * x := mem_commutant_iff.mp hy x hx
  have h : ⟪x Ω, y Ω⟫_ℂ = ⟪Ω, (x * y) Ω⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hxs.star_eq,
      mul_apply_eq_comp]
  have hc : conj ⟪Ω, (x * y) Ω⟫_ℂ = ⟪Ω, (x * y) Ω⟫_ℂ := by
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, star_mul,
      hxs.star_eq, hys.star_eq, ← hxy]
  rw [h]
  exact conj_eq_iff_im.mp hc

/-! ### The standard subspace -/

omit [CompleteSpace H] in
/-- `v ∈ i S` iff `-i v ∈ S`. -/
private lemma mem_mulI_iff {S : ClosedSubmodule ℝ H} {v : H} : v ∈ S.mulI ↔ (-I) • v ∈ S := by
  rw [mem_mapEquiv_iff, scalarSMulCLE_symm_apply, Units.smul_def, Units.val_inv_eq_inv_val,
    val_UnitI, inv_I]

/-- `H_M` is symplectically orthogonal to `H_{M′}`, as closed real subspaces. -/
private lemma closure_le_symplComp :
    (M′.selfAdjointOrbit Ω).closure ≤ (M.selfAdjointOrbit Ω).closure.symplComp := by
  intro v hv
  rw [mem_symplComp_iff]
  intro u hu
  have hcont : Continuous fun p : H × H => (⟪p.1, p.2⟫_ℂ).im :=
    Complex.continuous_im.comp (continuous_fst.inner continuous_snd)
  have hmem := map_mem_closure₂ (f := fun a b : H => (⟪a, b⟫_ℂ).im) (u := {0}) hcont
    ((Submodule.mem_closure_iff.mp hu)) (Submodule.mem_closure_iff.mp hv)
    fun a ha b hb => im_inner_eq_zero ha hb
  simpa using hmem

/-- For `Ω` separating, `H_M ∩ i H_M = 0`: a vector `v` with `v, -i v ∈ H_M` is orthogonal to
`H_{M′}` and `i H_{M′}`, hence to `M′ Ω`, which is dense. -/
private lemma inf_mulI_eq_bot (hs : IsSeparatingVector M Ω) :
    (M.selfAdjointOrbit Ω).closure ⊓ (M.selfAdjointOrbit Ω).closure.mulI = ⊥ := by
  refine eq_bot_iff.mpr fun v ⟨hv, hvi⟩ => ?_
  rw [ClosedSubmodule.mem_bot]
  have hvi' : (-I) • v ∈ (M.selfAdjointOrbit Ω).closure := mem_mulI_iff.mp hvi
  have h0 : ∀ y ∈ M′, IsSelfAdjoint y → ⟪v, y Ω⟫_ℂ = 0 := fun y hy hys => by
    have hyΩ : y Ω ∈ (M′.selfAdjointOrbit Ω).closure :=
      Submodule.mem_closure_iff.mpr (subset_closure ⟨y, hy, hys, rfl⟩)
    have h₁ := mem_symplComp_iff.mp (closure_le_symplComp hyΩ) v hv
    have h₂ := mem_symplComp_iff.mp (closure_le_symplComp hyΩ) _ hvi'
    rw [inner_smul_left, conj_neg_I, I_mul_im] at h₂
    exact Complex.ext h₂ h₁
  have h1 : ∀ y ∈ M′, ⟪v, y Ω⟫_ℂ = 0 := fun y hy => by
    rw [← realPart_add_I_smul_imaginaryPart y, add_apply, smul_apply, inner_add_right,
      inner_smul_right, h0 _ (realPart_mem hy) (ℜ y).2, h0 _ (imaginaryPart_mem hy) (ℑ y).2,
      mul_zero, add_zero]
  have hsub : (cyclicSubspace M′ Ω : Set H) ⊆ {u | ⟪v, u⟫_ℂ = 0} :=
    cyclicSubspace_subset (M := M′) (isClosed_eq (continuous_const.inner continuous_id)
      continuous_const) h1
  exact inner_self_eq_zero.mp (hsub (hs.isCyclicVector_commutant.mem v))

/-- For `Ω` cyclic, `H_M + i H_M` is dense: it contains `x Ω = (ℜ x) Ω + i (ℑ x) Ω`. -/
private lemma sup_mulI_eq_top (hc : IsCyclicVector M Ω) :
    (M.selfAdjointOrbit Ω).closure ⊔ (M.selfAdjointOrbit Ω).closure.mulI = ⊤ := by
  set K := (M.selfAdjointOrbit Ω).closure
  refine eq_top_iff.mpr fun v _ => ?_
  have hsub : (cyclicSubspace M Ω : Set H) ⊆ (↑(K ⊔ K.mulI) : Set H) :=
    cyclicSubspace_subset (K ⊔ K.mulI).isClosed fun x hx => by
      obtain ⟨a, ha, b, hb, hxa, -⟩ := exists_apply_eq_add (Ω := Ω) hx
      rw [hxa]
      refine add_mem (le_sup_left (a := K) (Submodule.mem_closure_iff.mpr (subset_closure ha)))
        (le_sup_right (a := K) ?_)
      rw [mem_mulI_iff, smul_smul, neg_mul, I_mul_I, neg_neg, one_smul]
      exact Submodule.mem_closure_iff.mpr (subset_closure hb)
  exact hsub (hc.mem v)

/-- Proves `IsCyclicVector M Ω` or `IsSeparatingVector M Ω` from the hypotheses in context,
also for the commutant: a separating vector for `M` is cyclic for `M′` and a cyclic vector for `M`
is separating for `M′`. It is the default argument of `VonNeumannAlgebra.standardSubspace`. -/
macro "cyclic_separating" : tactic => `(tactic| first
  | assumption
  | exact InnerProductSpace.IsSeparatingVector.isCyclicVector_commutant ‹_›
  | exact InnerProductSpace.IsCyclicVector.isSeparatingVector_commutant ‹_›)

variable (M Ω) in
/-- The **standard subspace** `H_M = closure {x Ω | x ∈ M, x⋆ = x}` of a cyclic and separating
vector `Ω` for `M`, written `H[M, Ω]`. Its Tomita operator is the closure of `x Ω ↦ x⋆ Ω`
(`VonNeumannAlgebra.closure_relativeTomita_self_eq_tomita`). The hypotheses are found in the
context by `cyclic_separating`. -/
noncomputable def standardSubspace (hc : IsCyclicVector M Ω := by cyclic_separating)
    (hs : IsSeparatingVector M Ω := by cyclic_separating) : StandardSubspace H where
  toClosedSubmodule := (M.selfAdjointOrbit Ω).closure
  IsSeparating := by exact inf_mulI_eq_bot hs
  IsCyclic := by exact sup_mulI_eq_top hc

/-- `H[M, Ω]` is the standard subspace `H_M = closure {x Ω | x ∈ M, x⋆ = x}` of a cyclic and
separating vector `Ω` for `M` (`VonNeumannAlgebra.standardSubspace`). -/
scoped notation "H[" M ", " Ω "]" => VonNeumannAlgebra.standardSubspace M Ω

/-- Displays `VonNeumannAlgebra.standardSubspace M Ω hc hs` as `H[M, Ω]`, hiding the proofs. -/
@[scoped app_unexpander VonNeumannAlgebra.standardSubspace]
meta def standardSubspaceUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $M $Ω $_ $_) => `(H[$M, $Ω])
  | _ => throw ()

variable (hc : IsCyclicVector M Ω) (hs : IsSeparatingVector M Ω)

/-- `H_M` is the closure of `{x Ω | x ∈ M, x⋆ = x}`. -/
lemma coe_standardSubspace :
    (H[M, Ω] : Set H) = closure (M.selfAdjointOrbit Ω : Set H) :=
  Submodule.topologicalClosure_coe _

/-- `x Ω ∈ H_M` for a self-adjoint `x ∈ M`. -/
lemma apply_mem_standardSubspace {x : H →L[ℂ] H} (hx : x ∈ M) (hxs : IsSelfAdjoint x) :
    x Ω ∈ H[M, Ω] :=
  Submodule.mem_closure_iff.mpr (subset_closure ⟨x, hx, hxs, rfl⟩)

/-- `Ω ∈ H_M`. -/
lemma self_mem_standardSubspace : Ω ∈ H[M, Ω] := by
  simpa using apply_mem_standardSubspace hc hs (one_mem M) (.one _)

/-! ### The Tomita operator and the modular operator of `(M, Ω)` -/

include hc hs in
/-- For a cyclic and separating `Ω`, the graph of `S_{η,Ω}` is `{(x Ω, x⋆ η) | x ∈ M}`: the
orthogonal complement of `[M Ω] = H` is `0` and the support is `s(Ω) = 1`. -/
lemma mem_graph_relativeTomita_iff_of_isCyclicVector_of_isSeparatingVector {η u v : H} :
    (u, v) ∈ (S[M]⟦η, Ω⟧).graphₛₗ ↔ ∃ x ∈ M, x Ω = u ∧ star x η = v := by
  have hsupp : M.supportProj Ω = 1 := supportProj_eq_one_iff.mpr hs.isCyclicVector_commutant
  rw [mem_graph_relativeTomita]
  refine ⟨fun ⟨x, hx, ζ, hζ, h⟩ => ⟨x, hx, ?_⟩, fun ⟨x, hx, hu, hv⟩ =>
    ⟨x, hx, 0, zero_mem _, by rw [add_zero, hsupp, one_apply_eq_self, hu, hv]⟩⟩
  have hζ0 : ζ = 0 := by
    rw [isCyclicVector_iff.mp hc] at hζ
    simpa using hζ
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  simp [hζ0, hsupp]

/-- **The Tomita operator of `(M, Ω)`**: the closure of `S_{Ω,Ω} : x Ω ↦ x⋆ Ω` is the Tomita
operator `S_{H_M} : a + i b ↦ a - i b` of the standard subspace `H_M`. Writing `x = ℜ x + i ℑ x`
shows `S_{Ω,Ω} ⊆ S_{H_M}`, and conversely `(a + i b, a - i b)` with `a, b ∈ H_M` is a limit of
`(x Ω, x⋆ Ω)` with `x = c + i d`, `c, d` self-adjoint. -/
theorem closure_relativeTomita_self_eq_tomita :
    (S[M]⟦Ω, Ω⟧).closureₛₗ = S[H[M, Ω]] := by
  set K := H[M, Ω]
  have hle : (S[M]⟦Ω, Ω⟧).graphₛₗ ≤ S[K].graphₛₗ := by
    rintro ⟨u, v⟩ h
    obtain ⟨x, hx, rfl, rfl⟩ :=
      (mem_graph_relativeTomita_iff_of_isCyclicVector_of_isSeparatingVector hc hs).mp h
    obtain ⟨a, ha, b, hb, h₁, h₂⟩ := exists_apply_eq_add (Ω := Ω) hx
    exact K.mem_graph_tomita.mpr ⟨a, Submodule.mem_closure_iff.mpr (subset_closure ha), b,
      Submodule.mem_closure_iff.mpr (subset_closure hb), h₁.symm, h₂.symm⟩
  refine LinearPMap.eq_of_eq_graphₛₗ (SetLike.coe_injective ?_)
  rw [(isClosable_relativeTomita M Ω Ω).coe_graphₛₗ_closureₛₗ]
  refine subset_antisymm (closure_minimal hle K.isClosed_tomita) ?_
  rintro ⟨u, v⟩ h
  obtain ⟨a, ha, b, hb, rfl, rfl⟩ := K.mem_graph_tomita.mp h
  have ha' : a ∈ closure (M.selfAdjointOrbit Ω : Set H) := by
    rw [← coe_standardSubspace hc hs]
    exact ha
  have hb' : b ∈ closure (M.selfAdjointOrbit Ω : Set H) := by
    rw [← coe_standardSubspace hc hs]
    exact hb
  refine map_mem_closure₂ (f := fun p q : H => (p + I • q, p - I • q)) (by fun_prop) ha' hb'
    fun p hp q hq => ?_
  obtain ⟨c, hcM, hcs, rfl⟩ := hp
  obtain ⟨d, hdM, hds, rfl⟩ := hq
  refine (mem_graph_relativeTomita_iff_of_isCyclicVector_of_isSeparatingVector hc hs).mpr
    ⟨c + I • d, add_mem hcM (SMulMemClass.smul_mem _ hdM), by rw [add_apply, smul_apply], ?_⟩
  rw [star_add, star_smul, hcs.star_eq, hds.star_eq, Complex.star_def, conj_I, add_apply,
    smul_apply, neg_smul, ← sub_eq_add_neg]

/-- **The modular operator of `(M, Ω)`**: `Δ_{Ω,Ω} = S̄_{Ω,Ω}† S̄_{Ω,Ω}` is the modular operator
`Δ_{H_M}` of the standard subspace `H_M`. -/
theorem relativeModular_self_eq_modular : Δ[M]⟦Ω, Ω⟧ = Δ[H[M, Ω]] := by
  rw [relativeModular_def, StandardSubspace.modular_def, closure_relativeTomita_self_eq_tomita hc hs]

/-- **The modular group of `(M, Ω)`**: `Δ_{Ω,Ω}^{it}` is the modular group `Δ_{H_M}^{it}` of the
standard subspace `H_M`. -/
lemma relativeModularGroup_self (t : ℝ) : Δ[M]⟦Ω, Ω⟧^{i t} = Δ[H[M, Ω]]^{i t} := by
  have key : ∀ {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B), A = B →
      hA.imaginaryPower t = hB.imaginaryPower t := by
    rintro A B hA hB rfl
    rfl
  rw [relativeModularGroup, key _ _ (relativeModular_self_eq_modular hc hs)]
  rfl

/-! ### Transport between standard subspaces -/

section Transport

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {M₁ : VonNeumannAlgebra H₁} {M₂ : VonNeumannAlgebra H₂} {Ω₁ : H₁} {Ω₂ : H₂}
  {V : H₁ →L[ℂ] H₂}

/-- A bounded `V` with `V† Ω₂ = Ω₁` and `V M₁ V† ⊆ M₂` maps `H_{M₁}` into `H_{M₂}`: for a
self-adjoint `x ∈ M₁`, `V x Ω₁ = (V x V†) Ω₂` with `V x V†` self-adjoint in `M₂`. For a unitary
`u` on one space the conditions read `u Ω = Ω` and `u x u⋆ ∈ M`. As `V` maps between two spaces,
its adjoint is written `V†` (Mathlib's `ContinuousLinearMap.adjoint`), not `V⋆`. -/
lemma apply_mem_standardSubspace_of_adjoint_apply (hc₁ : IsCyclicVector M₁ Ω₁)
    (hs₁ : IsSeparatingVector M₁ Ω₁) (hc₂ : IsCyclicVector M₂ Ω₂) (hs₂ : IsSeparatingVector M₂ Ω₂)
    (hVΩ : (V†) Ω₂ = Ω₁)
    (hVM : ∀ x ∈ M₁, V ∘L x ∘L V† ∈ M₂) {v : H₁}
    (hv : v ∈ H[M₁, Ω₁]) : V v ∈ H[M₂, Ω₂] := by
  rw [← SetLike.mem_coe, coe_standardSubspace] at hv ⊢
  refine map_mem_closure V.continuous hv fun u ⟨x, hx, hxs, hu⟩ => ?_
  refine ⟨V ∘L x ∘L V†, hVM x hx, ?_, ?_⟩
  · rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint, hxs.star_eq, ContinuousLinearMap.comp_assoc]
  · rw [← hu, ← hVΩ]
    rfl

end Transport

end VonNeumannAlgebra
