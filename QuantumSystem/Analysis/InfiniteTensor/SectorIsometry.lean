module

public import Mathlib.Topology.Algebra.LinearMapCompletion
public import QuantumSystem.Analysis.InfiniteTensor.Completion
public import QuantumSystem.Analysis.InfiniteTensor.SectorEquiv
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.UnitaryMapping

/-!
# Phase 3a: sector isometry theorem

The migration plan `infinite-tensor-product.md` calls out a single
mathematical blocker — the **sector isometry theorem**:

```
sectorEquivOfEquivalent :
  c0Rel Ω Ω' → ITPSector H Ω ≃ₗᵢ[ℂ] ITPSector H Ω'
```

promoting Bratteli–Robinson C₀-equivalence of unit families into a unitary
identification of the corresponding incomplete ITP sectors.  Phase 6b's
fiberwise lift, Phase 8's sector-permuting unitary, and Phase 9c's switch
all depend on it.

This file delivers:

* the trivial **`refl`-case** isometry `sectorEquivOfEquivalent_refl`
  (`Ω = Ω'`), establishing the type signature and the consistency of the
  identity case;
* the complete **`referenceRel` case** via the Λ-parameterised
  construction (`forwardFiberFin`, `forwardPreFin`, round-trip identity,
  `preITPSectorEquivOfReferenceRel`, `sectorEquivOfReferenceRel` =
  `sectorEquivOfEquivalent_referenceRel`).  This handles the
  finite-deviation case directly without infinite-product machinery, and
  axiom-free.

## What is left for the general `c0Rel` case

Two viable formalisation routes:

### Route 1: Phase normalisation via infinite product (BR-canonical)

1. **Phase normalisation under C₀-summability.**  Given Ω, Ω' with `c0Rel`,
   define the unit-modulus complex sequence `c_i := ⟨Ω_i, Ω'_i⟩ / ‖⟨Ω_i, Ω'_i⟩‖`
   on indices where `⟨Ω_i, Ω'_i⟩ ≠ 0`.  Prove convergence of the infinite
   product `∏_i c_i` via `Complex.multipliable_of_summable_log`, with
   summable `log` derived from the C₀-summable `1 - ‖⟨Ω_i, Ω'_i⟩‖`.

2. Finite-region phase-aligned tensors compatible with `regionEmbedLe`.

3. Colimit lift through `Module.DirectLimit.lift` + `Completion.extension`.

4. Cocycle / composition consistency for three families.

5. `refl` agreement.

The key Mathlib gap on this route is the bridge from C₀-summability of
`(1 - ‖z_i‖)` to summability of `Complex.log (z_i / ‖z_i‖)`.  The
C₀-condition controls magnitudes but not phase angles, so the bridge
requires either an additional hypothesis or a non-canonical phase choice
at each site.

### Route 2: Non-canonical unitary rotations (Classical-choice based)

For finite-dimensional `H_i`, the unit-vector pair `(Ω_i, Ω'_i)` admits a
unitary `V_i : H_i ≃ₗᵢ[ℂ] H_i` with `V_i Ω_i = Ω'_i` (existence by
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq` extended to a
unitary equivalence on `H_i`).  Choosing such a `V_i` per site via
`Classical.choice`, the colimit-level construction of the present file's
Λ-parameterised section adapts to general unit families: the cocycle
identity `V_T (regionEmbedLe Ω h x) = regionEmbedLe Ω' h (V_S x)` follows
from `V_s Ω_s = Ω'_s`, no `c0Rel` hypothesis needed at the algebraic
colimit.

The completion lift and `LinearIsometryEquiv` bundling proceed as for
the `referenceRel` case (`sectorEquivOfReferenceRel`), giving an
**abstract Hilbert-space equivalence** for *arbitrary* unit families
(canonicity is sacrificed compared to Route 1).

The Mathlib gap on this route is the elementary lemma

```
∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {u v : H}, ‖u‖ = 1 → ‖v‖ = 1 →
    ∃ V : H ≃ₗᵢ[ℂ] H, V u = v
```

which is well-known but not in Mathlib.  Constructing it cleanly takes
substantial Lean work (extend `{u}` and `{v}` to `OrthonormalBasis`es of
`Fin (finrank ℂ H)` via
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, then pair
them via `OrthonormalBasis.equiv`).  The structural framework here
(refl, referenceRel, Λ-parameterised) is ready to consume this lemma
when it lands.

## Status note

The `referenceRel` case (Route's "easy" half) is **complete**;
sufficient for Phase 5 / Phase 9c specialisation to the lattice
reference sector.  The general `c0Rel` case (needed by Phase 8's
sector-permuting unitary) awaits one of Route 1 or Route 2's missing
Mathlib lemma.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical
  Mechanics II*, §2.7.2 (sector unitary equivalences).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped InnerProductSpace

namespace InfiniteTensor

namespace UnitFamily

variable {ι : Type*} [DecidableEq ι] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

/-- The trivial `refl`-case of the sector isometry theorem: when `Ω = Ω'`
the two `ITPSector` spaces are literally equal and the canonical isometry
is the identity.

This is the diagonal special case of the (still pending) general theorem
`sectorEquivOfEquivalent : c0Rel Ω Ω' → ITPSector H Ω ≃ₗᵢ[ℂ] ITPSector H Ω'`.
It establishes the target type signature and the `refl`-agreement
property required by the migration plan. -/
noncomputable def sectorEquivOfEquivalent_refl (Ω : UnitFamily H) :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω :=
  LinearIsometryEquiv.refl ℂ (ITPSector (H := H) Ω)

@[simp]
theorem sectorEquivOfEquivalent_refl_apply (Ω : UnitFamily H)
    (x : ITPSector (H := H) Ω) :
    sectorEquivOfEquivalent_refl Ω x = x := rfl

@[simp]
theorem sectorEquivOfEquivalent_refl_symm (Ω : UnitFamily H) :
    (sectorEquivOfEquivalent_refl Ω).symm = sectorEquivOfEquivalent_refl Ω :=
  rfl

/-! ### Phase 3a (β): the `referenceRel` case (finite difference)

For unit families `Ω, Ω'` agreeing outside a finite set Λ, the sector
isometry can be constructed without infinite-product machinery.  The
construction:

1. For each finite `S ⊆ ι`, build `g_S : regionTensor S →ₗ[ℂ] preITPSector Ω'`
   by lifting `x` to `regionTensor (S ∪ Λ)` via `regionEmbedLe Ω` and then
   passing to `preITPSector Ω'` via `preITPSector.of Ω' (S ∪ Λ)`.
2. Verify cocycle compatibility for `S ⊆ T` using `regionEmbedLe_trans` and
   the fact that `Ω = Ω'` on `ι \ Λ` (so the Ω- and Ω'-extensions of an
   element of `regionTensor (S ∪ Λ)` outside this finset agree).
3. Apply `Module.DirectLimit.lift` to obtain
   `forwardPre : preITPSector Ω →ₗ[ℂ] preITPSector Ω'`.
4. Show inner-product preservation on `preITPSector` (sesquilinear
   reduction to representatives via `inner_of_of` + `regionEmbedLe_inner`).
5. Symmetrise (using `referenceRel.symm`) to get the inverse and bundle
   into `LinearIsometryEquiv`.
6. Lift the preITP isometry to `ITPSector` via `LinearIsometryEquiv` of
   `UniformSpace.Completion`. -/

variable (Ω Ω' : UnitFamily H)

/-- The forward fiber map at finset `S`: lift `x : regionTensor S` into the
`Ω'`-colimit by first extending via `regionEmbedLe Ω` to the larger finset
`S ∪ h.toFinset` (which contains the difference set), then composing with
the canonical embedding into `preITPSector Ω'`. -/
noncomputable def forwardFiber (h : referenceRel Ω Ω') (S : Finset ι) :
    regionTensor S (H := H) →ₗ[ℂ] preITPSector Ω' :=
  (preITPSector.of Ω' (S ∪ h.toFinset)).comp
    (regionEmbedLe Ω (Finset.subset_union_left))

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem forwardFiber_apply (h : referenceRel Ω Ω') (S : Finset ι)
    (x : regionTensor S (H := H)) :
    forwardFiber Ω Ω' h S x =
      preITPSector.of Ω' (S ∪ h.toFinset)
        (regionEmbedLe Ω Finset.subset_union_left x) := rfl

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- **Pointwise agreement of `extendVec` outside the difference set.**

Given `referenceRel Ω Ω'` (Ω = Ω' off a finite set Λ), the Ω-extension of
`x : regionTensor S` to a larger finset `T ∪ Λ` (containing both T and Λ)
agrees pointwise with the two-step extension `Ω-extend to S ∪ Λ` then
`Ω'-extend to T ∪ Λ`.

This is the key identity making the `forwardFiber` cocycle compatible. -/
theorem extendVec_eq_outside_referenceRel (h : referenceRel Ω Ω')
    {S T : Finset ι} (hST : S ⊆ T)
    (x : (s : {x // x ∈ S}) → H s.val) (s' : {x // x ∈ T ∪ h.toFinset}) :
    extendVec Ω (hST.trans Finset.subset_union_left) x s'
      = extendVec Ω'
          (Finset.union_subset_union hST (Finset.Subset.refl _) :
            S ∪ h.toFinset ⊆ T ∪ h.toFinset)
          (extendVec Ω Finset.subset_union_left x) s' := by
  -- Unfold both sides and reduce to a `dite`-by-`dite` case analysis.
  unfold extendVec
  by_cases hs : s'.val ∈ S
  · -- LHS: dif_pos hs gives x ⟨s'.val, hs⟩.
    -- RHS: outer dif_pos (s'.val ∈ S ∪ Λ via hs); inner dif_pos hs.
    have hsLΛ : s'.val ∈ S ∪ h.toFinset := Finset.mem_union_left _ hs
    rw [dif_pos hs, dif_pos hsLΛ]
    change x ⟨s'.val, hs⟩ = (if hs' : s'.val ∈ S then _ else _)
    rw [dif_pos hs]
  · by_cases hsΛ : s'.val ∈ h.toFinset
    · -- LHS: dif_neg hs gives Ω s'.val.
      -- RHS: outer dif_pos (s'.val ∈ S ∪ Λ via hsΛ); inner dif_neg hs gives Ω s'.val.
      have hsLΛ : s'.val ∈ S ∪ h.toFinset := Finset.mem_union_right _ hsΛ
      rw [dif_neg hs, dif_pos hsLΛ]
      change Ω s'.val = (if hs' : s'.val ∈ S then _ else _)
      rw [dif_neg hs]
    · -- LHS: dif_neg hs gives Ω s'.val.
      -- RHS: outer dif_neg (s'.val ∉ S ∪ Λ); gives Ω' s'.val.
      -- Since s'.val ∉ Λ, Ω = Ω' here.
      have hsLΛ : s'.val ∉ S ∪ h.toFinset := by
        intro hin
        rcases Finset.mem_union.mp hin with h₁ | h₂
        · exact hs h₁
        · exact hsΛ h₂
      rw [dif_neg hs, dif_neg hsLΛ]
      by_contra hne
      exact hsΛ (Set.Finite.mem_toFinset h |>.mpr hne)

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Cocycle compatibility for `forwardFiber` on elementary tensors. -/
theorem forwardFiber_cocycle_tprod (h : referenceRel Ω Ω') {S T : Finset ι}
    (hST : S ⊆ T) (ξ : (s : {x // x ∈ S}) → H s.val) :
    forwardFiber Ω Ω' h T (regionEmbedLe Ω hST (PiTensorProduct.tprod ℂ ξ))
      = forwardFiber Ω Ω' h S (PiTensorProduct.tprod ℂ ξ) := by
  rw [forwardFiber_apply, forwardFiber_apply, regionEmbedLe_tprod]
  rw [regionEmbedLe_tprod, regionEmbedLe_tprod, extendVec_trans]
  rw [show preITPSector.of Ω' (S ∪ h.toFinset)
        (PiTensorProduct.tprod ℂ
          (extendVec Ω Finset.subset_union_left ξ))
      = preITPSector.of Ω' (T ∪ h.toFinset)
        (regionEmbedLe Ω' (Finset.union_subset_union hST (Finset.Subset.refl _) :
            S ∪ h.toFinset ⊆ T ∪ h.toFinset)
          (PiTensorProduct.tprod ℂ
            (extendVec Ω Finset.subset_union_left ξ)))
      from (preITPSector.of_extend Ω' _ _).symm]
  rw [regionEmbedLe_tprod]
  -- Now both sides are of Ω' (T∪Λ) (tprod (...)). Reduce to tuple equality.
  congr 2
  funext s'
  exact extendVec_eq_outside_referenceRel Ω Ω' h hST ξ s'

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Cocycle compatibility for `forwardFiber` on all elements (extended from
elementary tensors via `PiTensorProduct.induction_on`). -/
theorem forwardFiber_cocycle (h : referenceRel Ω Ω') {S T : Finset ι}
    (hST : S ⊆ T) (x : regionTensor S (H := H)) :
    forwardFiber Ω Ω' h T (regionEmbedLe Ω hST x)
      = forwardFiber Ω Ω' h S x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    exact forwardFiber_cocycle_tprod Ω Ω' h hST ξ
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, ih₁, ih₂]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Lift `forwardFiber` through the algebraic colimit to obtain a linear map
`preITPSector Ω →ₗ[ℂ] preITPSector Ω'`. -/
noncomputable def forwardPre (h : referenceRel Ω Ω') :
    preITPSector Ω →ₗ[ℂ] preITPSector Ω' :=
  Module.DirectLimit.lift ℂ (Finset ι)
    (fun S : Finset ι => regionTensor S (H := H))
    (regionDirectedLink Ω)
    (forwardFiber Ω Ω' h)
    (fun _ _ _ => forwardFiber_cocycle Ω Ω' h _)

omit [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem forwardPre_of (h : referenceRel Ω Ω') (S : Finset ι)
    (x : regionTensor S (H := H)) :
    forwardPre Ω Ω' h (preITPSector.of Ω S x) = forwardFiber Ω Ω' h S x :=
  Module.DirectLimit.lift_of (R := ℂ) (G := fun S : Finset ι => regionTensor S (H := H))
    (f := regionDirectedLink Ω) _ _ x

/-- Inner product preservation by `forwardPre`. -/
theorem forwardPre_inner (h : referenceRel Ω Ω') (x y : preITPSector Ω) :
    ⟪forwardPre Ω Ω' h x, forwardPre Ω Ω' h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨S, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  rw [← hx, ← hy, forwardPre_of, forwardPre_of, forwardFiber_apply,
    forwardFiber_apply, inner_of_of, inner_of_of]
  exact regionEmbedLe_inner Ω Finset.subset_union_left x' y'

/-- Bundled linear isometry version of `forwardPre`. -/
noncomputable def forwardPreIsom (h : referenceRel Ω Ω') :
    preITPSector Ω →ₗᵢ[ℂ] preITPSector Ω' :=
  { forwardPre Ω Ω' h with
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (forwardPre_inner Ω Ω' h x x) }

omit [DecidableEq ι] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- The difference set of `Ω, Ω'` is symmetric: `h.symm.toFinset = h.toFinset`.

The underlying sets `{i | Ω i ≠ Ω' i}` and `{i | Ω' i ≠ Ω i}` are equal
(by `ne_comm`), hence so are the corresponding `Set.Finite.toFinset`s. -/
theorem referenceRel_symm_toFinset (h : referenceRel Ω Ω') :
    (referenceRel.symm h).toFinset = h.toFinset := by
  ext i
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_comm]

/-! ### Λ-parameterized construction (route (a))

To bypass the `(referenceRel.symm h).toFinset = h.toFinset` issue (which
is propositional but not definitional), we re-cast the construction with
the difference set `Λ` as an *explicit* `Finset ι` parameter and the
agreement hypothesis `hΛ : ∀ i ∉ Λ, Ω i = Ω' i` separately.

The forward and backward fibers then use the *same* `Λ`, so the
round-trip identity holds without any Finset transport.  At the end we
specialise back to `referenceRel` by taking `Λ := h.toFinset` and deriving
`hΛ` from `Set.Finite.mem_toFinset`. -/

omit [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] in
/-- Λ-parameterised analogue of `extendVec_eq_outside_referenceRel`. -/
theorem extendVec_eq_outside_param (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i)
    {S T : Finset ι} (hST : S ⊆ T)
    (x : (s : {x // x ∈ S}) → H s.val) (s' : {x // x ∈ T ∪ Λ}) :
    extendVec Ω (hST.trans Finset.subset_union_left) x s'
      = extendVec Ω'
          (Finset.union_subset_union hST (Finset.Subset.refl _) :
            S ∪ Λ ⊆ T ∪ Λ)
          (extendVec Ω Finset.subset_union_left x) s' := by
  unfold extendVec
  by_cases hs : s'.val ∈ S
  · have hsLΛ : s'.val ∈ S ∪ Λ := Finset.mem_union_left _ hs
    rw [dif_pos hs, dif_pos hsLΛ]
    change x ⟨s'.val, hs⟩ = (if hs' : s'.val ∈ S then _ else _)
    rw [dif_pos hs]
  · by_cases hsΛ : s'.val ∈ Λ
    · have hsLΛ : s'.val ∈ S ∪ Λ := Finset.mem_union_right _ hsΛ
      rw [dif_neg hs, dif_pos hsLΛ]
      change Ω s'.val = (if hs' : s'.val ∈ S then _ else _)
      rw [dif_neg hs]
    · have hsLΛ : s'.val ∉ S ∪ Λ := by
        intro hin
        rcases Finset.mem_union.mp hin with h₁ | h₂
        · exact hs h₁
        · exact hsΛ h₂
      rw [dif_neg hs, dif_neg hsLΛ]
      exact hΛ _ hsΛ

/-- Λ-parameterised forward fiber. -/
noncomputable def forwardFiberFin (Λ : Finset ι)
    (_hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) (S : Finset ι) :
    regionTensor S (H := H) →ₗ[ℂ] preITPSector Ω' :=
  (preITPSector.of Ω' (S ∪ Λ)).comp
    (regionEmbedLe Ω Finset.subset_union_left)

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem forwardFiberFin_apply (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) (S : Finset ι)
    (x : regionTensor S (H := H)) :
    forwardFiberFin Ω Ω' Λ hΛ S x =
      preITPSector.of Ω' (S ∪ Λ)
        (regionEmbedLe Ω Finset.subset_union_left x) := rfl

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Cocycle compatibility for `forwardFiberFin` on tprods. -/
theorem forwardFiberFin_cocycle_tprod (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i)
    {S T : Finset ι} (hST : S ⊆ T) (ξ : (s : {x // x ∈ S}) → H s.val) :
    forwardFiberFin Ω Ω' Λ hΛ T (regionEmbedLe Ω hST (PiTensorProduct.tprod ℂ ξ))
      = forwardFiberFin Ω Ω' Λ hΛ S (PiTensorProduct.tprod ℂ ξ) := by
  rw [forwardFiberFin_apply, forwardFiberFin_apply, regionEmbedLe_tprod]
  rw [regionEmbedLe_tprod, regionEmbedLe_tprod, extendVec_trans]
  rw [show preITPSector.of Ω' (S ∪ Λ)
        (PiTensorProduct.tprod ℂ
          (extendVec Ω Finset.subset_union_left ξ))
      = preITPSector.of Ω' (T ∪ Λ)
        (regionEmbedLe Ω' (Finset.union_subset_union hST (Finset.Subset.refl _) :
            S ∪ Λ ⊆ T ∪ Λ)
          (PiTensorProduct.tprod ℂ
            (extendVec Ω Finset.subset_union_left ξ)))
      from (preITPSector.of_extend Ω' _ _).symm]
  rw [regionEmbedLe_tprod]
  congr 2
  funext s'
  exact extendVec_eq_outside_param Ω Ω' Λ hΛ hST ξ s'

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem forwardFiberFin_cocycle (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i)
    {S T : Finset ι} (hST : S ⊆ T) (x : regionTensor S (H := H)) :
    forwardFiberFin Ω Ω' Λ hΛ T (regionEmbedLe Ω hST x)
      = forwardFiberFin Ω Ω' Λ hΛ S x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    exact forwardFiberFin_cocycle_tprod Ω Ω' Λ hΛ hST ξ
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, ih₁, ih₂]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Λ-parameterised forward map at the colimit level. -/
noncomputable def forwardPreFin (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) :
    preITPSector Ω →ₗ[ℂ] preITPSector Ω' :=
  Module.DirectLimit.lift ℂ (Finset ι)
    (fun S : Finset ι => regionTensor S (H := H))
    (regionDirectedLink Ω)
    (forwardFiberFin Ω Ω' Λ hΛ)
    (fun _ _ _ => forwardFiberFin_cocycle Ω Ω' Λ hΛ _)

omit [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem forwardPreFin_of (Λ : Finset ι) (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i)
    (S : Finset ι) (x : regionTensor S (H := H)) :
    forwardPreFin Ω Ω' Λ hΛ (preITPSector.of Ω S x)
      = forwardFiberFin Ω Ω' Λ hΛ S x :=
  Module.DirectLimit.lift_of (R := ℂ)
    (G := fun S : Finset ι => regionTensor S (H := H))
    (f := regionDirectedLink Ω) _ _ x

theorem forwardPreFin_inner (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) (x y : preITPSector Ω) :
    ⟪forwardPreFin Ω Ω' Λ hΛ x, forwardPreFin Ω Ω' Λ hΛ y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨S, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  rw [← hx, ← hy, forwardPreFin_of, forwardPreFin_of, forwardFiberFin_apply,
    forwardFiberFin_apply, inner_of_of, inner_of_of]
  exact regionEmbedLe_inner Ω Finset.subset_union_left x' y'

/-! ### Round-trip identity for the parameterised construction -/

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Round-trip identity on tprods.  Crucially, both legs use the same `Λ`,
so the outer extension lands in `(S∪Λ)∪Λ = S∪Λ` and every index in the
larger Finset is already inside `S∪Λ`. -/
theorem forwardPreFin_round_trip_tprod (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) (S : Finset ι)
    (ξ : (s : {x // x ∈ S}) → H s.val) :
    forwardPreFin Ω' Ω Λ (fun i hi => (hΛ i hi).symm)
        (forwardPreFin Ω Ω' Λ hΛ
          (preITPSector.of Ω S (PiTensorProduct.tprod ℂ ξ)))
      = preITPSector.of Ω S (PiTensorProduct.tprod ℂ ξ) := by
  rw [forwardPreFin_of, forwardFiberFin_apply, regionEmbedLe_tprod]
  rw [forwardPreFin_of, forwardFiberFin_apply, regionEmbedLe_tprod]
  -- Lift RHS to ((S∪Λ)∪Λ) via two of_extend's.
  conv_rhs => rw [show preITPSector.of Ω S (PiTensorProduct.tprod ℂ ξ)
      = preITPSector.of Ω (S ∪ Λ) (regionEmbedLe Ω
          (Finset.subset_union_left : S ⊆ S ∪ Λ)
          (PiTensorProduct.tprod ℂ ξ)) from
    (preITPSector.of_extend Ω _ _).symm]
  conv_rhs => rw [show preITPSector.of Ω (S ∪ Λ)
        (regionEmbedLe Ω (Finset.subset_union_left : S ⊆ S ∪ Λ)
          (PiTensorProduct.tprod ℂ ξ))
      = preITPSector.of Ω ((S ∪ Λ) ∪ Λ) (regionEmbedLe Ω
          (Finset.subset_union_left : S ∪ Λ ⊆ (S ∪ Λ) ∪ Λ)
          (regionEmbedLe Ω (Finset.subset_union_left : S ⊆ S ∪ Λ)
            (PiTensorProduct.tprod ℂ ξ))) from
    (preITPSector.of_extend Ω _ _).symm]
  rw [regionEmbedLe_tprod, regionEmbedLe_tprod]
  -- Both sides are `of Ω ((S∪Λ)∪Λ) (tprod ...)`.
  congr 2
  funext s'
  -- For every s' : ↥((S∪Λ)∪Λ), the s'.val is in S∪Λ (since Λ ⊆ S∪Λ).
  have hs : s'.val ∈ S ∪ Λ := by
    have h_in : s'.val ∈ (S ∪ Λ) ∪ Λ := s'.prop
    rcases Finset.mem_union.mp h_in with h₁ | h₂
    · exact h₁
    · exact Finset.mem_union_right S h₂
  -- Both extendVec Ω' and extendVec Ω in the outer step give the inner value.
  rw [extendVec_inside _ _ _ _ hs, extendVec_inside _ _ _ _ hs]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Round-trip identity on `preITPSector.of` representatives. -/
theorem forwardPreFin_round_trip_of (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) (S : Finset ι)
    (y : regionTensor S (H := H)) :
    forwardPreFin Ω' Ω Λ (fun i hi => (hΛ i hi).symm)
        (forwardPreFin Ω Ω' Λ hΛ (preITPSector.of Ω S y))
      = preITPSector.of Ω S y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    exact forwardPreFin_round_trip_tprod Ω Ω' Λ hΛ S ξ
  | add y₁ y₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, ih₁, ih₂]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Round-trip identity at the colimit level. -/
theorem forwardPreFin_round_trip (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) (x : preITPSector Ω) :
    forwardPreFin Ω' Ω Λ (fun i hi => (hΛ i hi).symm)
        (forwardPreFin Ω Ω' Λ hΛ x) = x := by
  obtain ⟨S, y, rfl⟩ := preITPSector.exists_of Ω x
  exact forwardPreFin_round_trip_of Ω Ω' Λ hΛ S y

/-- The Λ-parameterised pre-Hilbert linear isometric equivalence between
sectors `preITPSector Ω` and `preITPSector Ω'`. -/
noncomputable def preITPSectorEquivOfFin (Λ : Finset ι)
    (hΛ : ∀ i, i ∉ Λ → Ω i = Ω' i) :
    preITPSector Ω ≃ₗᵢ[ℂ] preITPSector Ω' :=
  { toFun := forwardPreFin Ω Ω' Λ hΛ
    map_add' := (forwardPreFin Ω Ω' Λ hΛ).map_add
    map_smul' := (forwardPreFin Ω Ω' Λ hΛ).map_smul
    invFun := forwardPreFin Ω' Ω Λ (fun i hi => (hΛ i hi).symm)
    left_inv := forwardPreFin_round_trip Ω Ω' Λ hΛ
    right_inv := fun y => by
      have := forwardPreFin_round_trip Ω' Ω Λ (fun i hi => (hΛ i hi).symm) y
      simpa using this
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (forwardPreFin_inner Ω Ω' Λ hΛ x x) }

/-! ### Specialisation to `referenceRel` -/

/-- The pre-Hilbert sector equivalence for `referenceRel Ω Ω'`, using
`Λ := h.toFinset` as the difference set. -/
noncomputable def preITPSectorEquivOfReferenceRel
    (h : referenceRel Ω Ω') :
    preITPSector Ω ≃ₗᵢ[ℂ] preITPSector Ω' :=
  preITPSectorEquivOfFin Ω Ω' h.toFinset (fun i hi => by
    by_contra hne
    exact hi (Set.Finite.mem_toFinset h |>.mpr hne))

/-! ### Completion lift to `ITPSector`

Bundle the pre-Hilbert `LinearIsometryEquiv` into a Hilbert-level
`LinearIsometryEquiv` via two `ContinuousLinearMap.completion`s, with
round-trip identities and norm preservation discharged by the density of
`preITPSector Ω → ITPSector Ω` plus continuity. -/

/-- The full Hilbert-completion isometry: the `referenceRel` case of the
sector isometry theorem. -/
noncomputable def sectorEquivOfReferenceRel
    (h : referenceRel Ω Ω') :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω' :=
  let f := preITPSectorEquivOfReferenceRel Ω Ω' h
  let fc : preITPSector Ω →L[ℂ] preITPSector Ω' :=
    f.toLinearIsometry.toContinuousLinearMap
  let gc : preITPSector Ω' →L[ℂ] preITPSector Ω :=
    f.symm.toLinearIsometry.toContinuousLinearMap
  let fL : ITPSector (H := H) Ω →L[ℂ] ITPSector (H := H) Ω' := fc.completion
  let gL : ITPSector (H := H) Ω' →L[ℂ] ITPSector (H := H) Ω := gc.completion
  { toFun := fL
    map_add' := fL.map_add
    map_smul' := fL.map_smul
    invFun := gL
    left_inv := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (gL.continuous.comp fL.continuous) continuous_id) ?_
      intro a
      change gc.completion (fc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        ContinuousLinearMap.completion_apply_coe gc (fc a)]
      congr 1
      exact f.left_inv a
    right_inv := fun y => by
      refine UniformSpace.Completion.induction_on y
        (isClosed_eq (fL.continuous.comp gL.continuous) continuous_id) ?_
      intro a
      change fc.completion (gc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe gc a,
        ContinuousLinearMap.completion_apply_coe fc (gc a)]
      congr 1
      exact f.right_inv a
    norm_map' := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (continuous_norm.comp fL.continuous) continuous_norm) ?_
      intro a
      change ‖fc.completion ↑a‖ = ‖(↑a : UniformSpace.Completion (preITPSector Ω))‖
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact f.norm_map a }

/-- The `referenceRel` case of `sectorEquivOfEquivalent`, derived through
the `referenceRel ⊆ c0Rel` inclusion. -/
noncomputable def sectorEquivOfEquivalent_referenceRel
    (h : referenceRel Ω Ω') :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω' :=
  sectorEquivOfReferenceRel Ω Ω' h

/-! ### Phase 3a (γ): the general case via per-site unitary rotations

For any pair of unit families `Ω, Ω' : UnitFamily H` (no `c0Rel` hypothesis
needed at this purely algebraic / Hilbert-completion level), choose a
per-site unitary `V_s : H s ≃ₗᵢ[ℂ] H s` with `V_s (Ω s) = Ω' s` (existence
by `exists_linearIsometryEquiv_of_unit` — finite-dimensional Hilbert
spaces admit unitary mappings between any pair of unit vectors).

The pointwise rotation lifts to a colimit-level isometry
`preITPSector Ω ≃ₗᵢ[ℂ] preITPSector Ω'` and to its Hilbert completion
`ITPSector H Ω ≃ₗᵢ[ℂ] ITPSector H Ω'`.  The construction is
non-canonical (depends on the choice of `V_s` per site), but provides the
Hilbert-space identification needed by all downstream phases.

Specialised to `c0Rel`, this gives the migration plan's
`sectorEquivOfEquivalent`. -/

/-- Per-site unitary rotation taking `Ω s` to `Ω' s`. -/
noncomputable def chooseRotation (s : ι) :
    H s ≃ₗᵢ[ℂ] H s :=
  Classical.choose (exists_linearIsometryEquiv_of_unit (Ω.norm_vec s) (Ω'.norm_vec s))

omit [DecidableEq ι] in
theorem chooseRotation_apply (s : ι) :
    chooseRotation Ω Ω' s (Ω s) = Ω' s :=
  Classical.choose_spec (exists_linearIsometryEquiv_of_unit (Ω.norm_vec s) (Ω'.norm_vec s))

omit [DecidableEq ι] in
theorem chooseRotation_symm_apply (s : ι) :
    (chooseRotation Ω Ω' s).symm (Ω' s) = Ω s := by
  have h := chooseRotation_apply Ω Ω' s
  exact h ▸ (chooseRotation Ω Ω' s).symm_apply_apply (Ω s)

/-- Region-level rotation: `regionTensor S ≃ₗᵢ[ℂ] regionTensor S` obtained
from the pointwise rotations. -/
noncomputable def regionRot (S : Finset ι) :
    regionTensor S (H := H) ≃ₗᵢ[ℂ] regionTensor S (H := H) :=
  ForMathlib.PiTensorProduct.piTensorMapIsom (ι := {x // x ∈ S})
    (H := fun s : {x // x ∈ S} => H s.val)
    (fun s : {x // x ∈ S} => chooseRotation Ω Ω' s.val)

@[simp]
theorem regionRot_tprod (S : Finset ι) (ξ : (s : {x // x ∈ S}) → H s.val) :
    regionRot Ω Ω' S (PiTensorProduct.tprod ℂ ξ)
      = PiTensorProduct.tprod ℂ (fun s : {x // x ∈ S} => chooseRotation Ω Ω' s.val (ξ s)) := by
  unfold regionRot
  exact ForMathlib.PiTensorProduct.piTensorMapIsom_tprod (ι := {x // x ∈ S})
    (H := fun s : {x // x ∈ S} => H s.val) _ _

/-- The forward fiber map at finset `S` for the general (V-rotation) case:
apply the per-site rotation to a tuple in `regionTensor S`, then push to
`preITPSector Ω'` via `preITPSector.of Ω' S`. -/
noncomputable def forwardFiberAny (S : Finset ι) :
    regionTensor S (H := H) →ₗ[ℂ] preITPSector Ω' :=
  (preITPSector.of Ω' S).comp (regionRot Ω Ω' S).toLinearMap

theorem forwardFiberAny_apply (S : Finset ι) (x : regionTensor S (H := H)) :
    forwardFiberAny Ω Ω' S x =
      preITPSector.of Ω' S (regionRot Ω Ω' S x) := rfl

/-- Pointwise compatibility for the V-rotation cocycle: applying V then
extending via Ω' equals extending via Ω then applying V, on the level of
tuples. -/
theorem rotateExtendVec_eq (S T : Finset ι) (hST : S ⊆ T)
    (ξ : (s : {x // x ∈ S}) → H s.val) (s' : {x // x ∈ T}) :
    chooseRotation Ω Ω' s'.val (extendVec Ω hST ξ s')
      = extendVec Ω' hST
          (fun s : {x // x ∈ S} => chooseRotation Ω Ω' s.val (ξ s)) s' := by
  by_cases hs : s'.val ∈ S
  · rw [extendVec_inside _ _ _ _ hs, extendVec_inside _ _ _ _ hs]
  · rw [extendVec_outside _ _ _ _ hs, extendVec_outside _ _ _ _ hs]
    exact chooseRotation_apply Ω Ω' s'.val

/-- Cocycle compatibility for `forwardFiberAny` on elementary tensors. -/
theorem forwardFiberAny_cocycle_tprod {S T : Finset ι} (hST : S ⊆ T)
    (ξ : (s : {x // x ∈ S}) → H s.val) :
    forwardFiberAny Ω Ω' T (regionEmbedLe Ω hST (PiTensorProduct.tprod ℂ ξ))
      = forwardFiberAny Ω Ω' S (PiTensorProduct.tprod ℂ ξ) := by
  rw [forwardFiberAny_apply, forwardFiberAny_apply, regionEmbedLe_tprod,
    regionRot_tprod, regionRot_tprod]
  -- LHS: of Ω' T (tprod (V • extendVec Ω hST ξ))
  -- RHS: of Ω' S (tprod (V • ξ))
  -- Lift RHS via of_extend to T:
  conv_rhs => rw [show preITPSector.of Ω' S
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => chooseRotation Ω Ω' s.val (ξ s)))
      = preITPSector.of Ω' T (regionEmbedLe Ω' hST
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => chooseRotation Ω Ω' s.val (ξ s))))
      from (preITPSector.of_extend Ω' _ _).symm]
  rw [regionEmbedLe_tprod]
  -- Now both sides are of Ω' T (tprod ...). Reduce to tuple equality.
  congr 2
  funext s'
  exact rotateExtendVec_eq Ω Ω' S T hST ξ s'

/-- Cocycle compatibility for `forwardFiberAny` on all elements (extended
from elementary tensors via `PiTensorProduct.induction_on`). -/
theorem forwardFiberAny_cocycle {S T : Finset ι} (hST : S ⊆ T)
    (x : regionTensor S (H := H)) :
    forwardFiberAny Ω Ω' T (regionEmbedLe Ω hST x)
      = forwardFiberAny Ω Ω' S x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    exact forwardFiberAny_cocycle_tprod Ω Ω' hST ξ
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, ih₁, ih₂]

/-- Lift `forwardFiberAny` through the algebraic colimit to obtain a linear
map `preITPSector Ω →ₗ[ℂ] preITPSector Ω'`. -/
noncomputable def forwardPreAny :
    preITPSector Ω →ₗ[ℂ] preITPSector Ω' :=
  Module.DirectLimit.lift ℂ (Finset ι)
    (fun S : Finset ι => regionTensor S (H := H))
    (regionDirectedLink Ω)
    (forwardFiberAny Ω Ω')
    (fun _ _ _ => forwardFiberAny_cocycle Ω Ω' _)

@[simp]
theorem forwardPreAny_of (S : Finset ι) (x : regionTensor S (H := H)) :
    forwardPreAny Ω Ω' (preITPSector.of Ω S x) = forwardFiberAny Ω Ω' S x :=
  Module.DirectLimit.lift_of (R := ℂ) (G := fun S : Finset ι => regionTensor S (H := H))
    (f := regionDirectedLink Ω) _ _ x

/-- Inner-product preservation by `forwardPreAny`. -/
theorem forwardPreAny_inner (x y : preITPSector Ω) :
    ⟪forwardPreAny Ω Ω' x, forwardPreAny Ω Ω' y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨S, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  rw [← hx, ← hy, forwardPreAny_of, forwardPreAny_of, forwardFiberAny_apply,
    forwardFiberAny_apply, inner_of_of, inner_of_of]
  exact (regionRot Ω Ω' S).inner_map_map x' y'

/-! ### Backward construction via inverse rotations

The forward map `forwardPreAny Ω Ω'` uses the choice `chooseRotation Ω Ω' s`.
The naive backward `forwardPreAny Ω' Ω` would use `chooseRotation Ω' Ω s`,
which is an *independent* `Classical.choose` and need NOT compose to the
identity with `chooseRotation Ω Ω' s`.

Instead, the bundled inverse uses `(chooseRotation Ω Ω' s).symm` per site,
guaranteeing per-site round-trip identities. -/

/-- Backward region rotation: `(chooseRotation Ω Ω' s).symm` per site. -/
noncomputable def regionRotSymm (S : Finset ι) :
    regionTensor S (H := H) ≃ₗᵢ[ℂ] regionTensor S (H := H) :=
  ForMathlib.PiTensorProduct.piTensorMapIsom (ι := {x // x ∈ S})
    (H := fun s : {x // x ∈ S} => H s.val)
    (fun s : {x // x ∈ S} => (chooseRotation Ω Ω' s.val).symm)

@[simp]
theorem regionRotSymm_tprod (S : Finset ι) (η : (s : {x // x ∈ S}) → H s.val) :
    regionRotSymm Ω Ω' S (PiTensorProduct.tprod ℂ η)
      = PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => (chooseRotation Ω Ω' s.val).symm (η s)) := by
  unfold regionRotSymm
  exact ForMathlib.PiTensorProduct.piTensorMapIsom_tprod (ι := {x // x ∈ S})
    (H := fun s : {x // x ∈ S} => H s.val) _ _

theorem regionRotSymm_regionRot (S : Finset ι) (x : regionTensor S (H := H)) :
    regionRotSymm Ω Ω' S (regionRot Ω Ω' S x) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    rw [map_smul, map_smul, regionRot_tprod, regionRotSymm_tprod]
    congr 1
    refine congrArg (PiTensorProduct.tprod ℂ) ?_
    funext s
    exact (chooseRotation Ω Ω' s.val).symm_apply_apply (ξ s)
  | add x₁ x₂ ih₁ ih₂ =>
    rw [map_add, map_add, ih₁, ih₂]

theorem regionRot_regionRotSymm (S : Finset ι) (y : regionTensor S (H := H)) :
    regionRot Ω Ω' S (regionRotSymm Ω Ω' S y) = y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r η =>
    rw [map_smul, map_smul, regionRotSymm_tprod, regionRot_tprod]
    congr 1
    refine congrArg (PiTensorProduct.tprod ℂ) ?_
    funext s
    exact (chooseRotation Ω Ω' s.val).apply_symm_apply (η s)
  | add y₁ y₂ ih₁ ih₂ =>
    rw [map_add, map_add, ih₁, ih₂]

/-- Backward fiber: `regionTensor S → preITPSector Ω` using inverse rotations. -/
noncomputable def backwardFiberAny (S : Finset ι) :
    regionTensor S (H := H) →ₗ[ℂ] preITPSector Ω :=
  (preITPSector.of Ω S).comp (regionRotSymm Ω Ω' S).toLinearMap

theorem backwardFiberAny_apply (S : Finset ι) (y : regionTensor S (H := H)) :
    backwardFiberAny Ω Ω' S y =
      preITPSector.of Ω S (regionRotSymm Ω Ω' S y) := rfl

/-- Pointwise compatibility for the backward V-rotation cocycle. -/
theorem rotateSymmExtendVec_eq (S T : Finset ι) (hST : S ⊆ T)
    (η : (s : {x // x ∈ S}) → H s.val) (s' : {x // x ∈ T}) :
    (chooseRotation Ω Ω' s'.val).symm (extendVec Ω' hST η s')
      = extendVec Ω hST
          (fun s : {x // x ∈ S} => (chooseRotation Ω Ω' s.val).symm (η s)) s' := by
  by_cases hs : s'.val ∈ S
  · rw [extendVec_inside _ _ _ _ hs, extendVec_inside _ _ _ _ hs]
  · rw [extendVec_outside _ _ _ _ hs, extendVec_outside _ _ _ _ hs]
    exact chooseRotation_symm_apply Ω Ω' s'.val

theorem backwardFiberAny_cocycle_tprod {S T : Finset ι} (hST : S ⊆ T)
    (η : (s : {x // x ∈ S}) → H s.val) :
    backwardFiberAny Ω Ω' T (regionEmbedLe Ω' hST (PiTensorProduct.tprod ℂ η))
      = backwardFiberAny Ω Ω' S (PiTensorProduct.tprod ℂ η) := by
  rw [backwardFiberAny_apply, backwardFiberAny_apply, regionEmbedLe_tprod,
    regionRotSymm_tprod, regionRotSymm_tprod]
  conv_rhs => rw [show preITPSector.of Ω S
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => (chooseRotation Ω Ω' s.val).symm (η s)))
      = preITPSector.of Ω T (regionEmbedLe Ω hST
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => (chooseRotation Ω Ω' s.val).symm (η s))))
      from (preITPSector.of_extend Ω _ _).symm]
  rw [regionEmbedLe_tprod]
  congr 2
  funext s'
  exact rotateSymmExtendVec_eq Ω Ω' S T hST η s'

theorem backwardFiberAny_cocycle {S T : Finset ι} (hST : S ⊆ T)
    (y : regionTensor S (H := H)) :
    backwardFiberAny Ω Ω' T (regionEmbedLe Ω' hST y)
      = backwardFiberAny Ω Ω' S y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r η =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    exact backwardFiberAny_cocycle_tprod Ω Ω' hST η
  | add y₁ y₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, ih₁, ih₂]

/-- Lift `backwardFiberAny` through the algebraic colimit. -/
noncomputable def backwardPreAny :
    preITPSector Ω' →ₗ[ℂ] preITPSector Ω :=
  Module.DirectLimit.lift ℂ (Finset ι)
    (fun S : Finset ι => regionTensor S (H := H))
    (regionDirectedLink Ω')
    (backwardFiberAny Ω Ω')
    (fun _ _ _ => backwardFiberAny_cocycle Ω Ω' _)

@[simp]
theorem backwardPreAny_of (S : Finset ι) (y : regionTensor S (H := H)) :
    backwardPreAny Ω Ω' (preITPSector.of Ω' S y) = backwardFiberAny Ω Ω' S y :=
  Module.DirectLimit.lift_of (R := ℂ) (G := fun S : Finset ι => regionTensor S (H := H))
    (f := regionDirectedLink Ω') _ _ y

/-! ### Round-trip identities at the colimit level -/

theorem forwardPreAny_backwardPreAny_of (S : Finset ι)
    (y : regionTensor S (H := H)) :
    forwardPreAny Ω Ω' (backwardPreAny Ω Ω' (preITPSector.of Ω' S y))
      = preITPSector.of Ω' S y := by
  rw [backwardPreAny_of, backwardFiberAny_apply, forwardPreAny_of,
    forwardFiberAny_apply]
  congr 1
  exact regionRot_regionRotSymm Ω Ω' S y

theorem backwardPreAny_forwardPreAny_of (S : Finset ι)
    (x : regionTensor S (H := H)) :
    backwardPreAny Ω Ω' (forwardPreAny Ω Ω' (preITPSector.of Ω S x))
      = preITPSector.of Ω S x := by
  rw [forwardPreAny_of, forwardFiberAny_apply, backwardPreAny_of,
    backwardFiberAny_apply]
  congr 1
  exact regionRotSymm_regionRot Ω Ω' S x

theorem forwardPreAny_backwardPreAny (y : preITPSector Ω') :
    forwardPreAny Ω Ω' (backwardPreAny Ω Ω' y) = y := by
  obtain ⟨S, y', rfl⟩ := preITPSector.exists_of Ω' y
  exact forwardPreAny_backwardPreAny_of Ω Ω' S y'

theorem backwardPreAny_forwardPreAny (x : preITPSector Ω) :
    backwardPreAny Ω Ω' (forwardPreAny Ω Ω' x) = x := by
  obtain ⟨S, x', rfl⟩ := preITPSector.exists_of Ω x
  exact backwardPreAny_forwardPreAny_of Ω Ω' S x'

/-- The pre-Hilbert sector equivalence for arbitrary pairs of unit families,
via per-site V_s rotations.  No `c0Rel` hypothesis needed. -/
noncomputable def preITPSectorEquivAny :
    preITPSector Ω ≃ₗᵢ[ℂ] preITPSector Ω' :=
  { toFun := forwardPreAny Ω Ω'
    map_add' := (forwardPreAny Ω Ω').map_add
    map_smul' := (forwardPreAny Ω Ω').map_smul
    invFun := backwardPreAny Ω Ω'
    left_inv := backwardPreAny_forwardPreAny Ω Ω'
    right_inv := forwardPreAny_backwardPreAny Ω Ω'
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (forwardPreAny_inner Ω Ω' x x) }

/-! ### Hilbert-completion lift -/

/-- The full Hilbert-completion isometry between `ITPSector` spaces, valid
for **any** pair of unit families `Ω, Ω' : UnitFamily H` (no `c0Rel`
hypothesis needed at this purely Hilbert-level construction).

**Non-canonical**: the underlying per-site rotations come from
`Classical.choice`, so `noncanonicalSectorEquivAny` is *not* functorial
in `Ω, Ω'`.  In particular it does **not** satisfy `_one`, `_mul`, or
`_inv` laws; downstream group-representation arguments must consume a
canonical `SectorEquivData` (via `sectorEquivOfData`) instead.

Use this only where an arbitrary Hilbert-space identification is
explicitly acceptable. -/
noncomputable def noncanonicalSectorEquivAny :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω' :=
  let f := preITPSectorEquivAny Ω Ω'
  let fc : preITPSector Ω →L[ℂ] preITPSector Ω' :=
    f.toLinearIsometry.toContinuousLinearMap
  let gc : preITPSector Ω' →L[ℂ] preITPSector Ω :=
    f.symm.toLinearIsometry.toContinuousLinearMap
  let fL : ITPSector (H := H) Ω →L[ℂ] ITPSector (H := H) Ω' := fc.completion
  let gL : ITPSector (H := H) Ω' →L[ℂ] ITPSector (H := H) Ω := gc.completion
  { toFun := fL
    map_add' := fL.map_add
    map_smul' := fL.map_smul
    invFun := gL
    left_inv := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (gL.continuous.comp fL.continuous) continuous_id) ?_
      intro a
      change gc.completion (fc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        ContinuousLinearMap.completion_apply_coe gc (fc a)]
      congr 1
      exact f.left_inv a
    right_inv := fun y => by
      refine UniformSpace.Completion.induction_on y
        (isClosed_eq (fL.continuous.comp gL.continuous) continuous_id) ?_
      intro a
      change fc.completion (gc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe gc a,
        ContinuousLinearMap.completion_apply_coe fc (gc a)]
      congr 1
      exact f.right_inv a
    norm_map' := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (continuous_norm.comp fL.continuous) continuous_norm) ?_
      intro a
      change ‖fc.completion ↑a‖ = ‖(↑a : UniformSpace.Completion (preITPSector Ω))‖
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact f.norm_map a }

/-- The general `c0Rel` case of the sector isometry theorem, supplied via
Route 2 (`noncanonicalSectorEquivAny`).

The `c0Rel` hypothesis is recorded for API correctness — placing `Ω` and
`Ω'` in the same Bratteli–Robinson sector class is what makes the
identification *meaningful* at the level of physics — but is **not
consumed** by the construction: per-site rotations from `chooseRotation`
are total at the finite-dimensional Hilbert level (no `c0Rel` summability
needed for the algebraic colimit / completion lift to exist).

**Non-canonical**: the resulting isometry depends on `Classical.choice`
via `chooseRotation`.  Consumers requiring functoriality (`refl`, `symm`,
`trans` laws) should instead supply a `SectorEquivData Ω Ω'` and use
`sectorEquivOfData`. -/
noncomputable def sectorEquivOfEquivalent (_h : c0Rel Ω Ω') :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω' :=
  noncanonicalSectorEquivAny Ω Ω'

/-! ### Phase 4: coherent same-index sector transport (`SectorEquivData`)

The wrappers `sectorEquivAny` and `sectorEquivOfEquivalent` above are
**non-canonical**: their underlying per-site rotations are made via
`Classical.choice`.  This section introduces a structured input
`SectorEquivData Ω Ω'` carrying a coherent finite-region transport, and
the corresponding canonical equivalence `sectorEquivOfData`.  Identity,
inverse, and composition laws are then provable at the map level. -/

/-- Coherent transport data between two unit families over the **same**
index family `H : ι → Type*`.

For each finite subset `S : Finset ι` we provide an isometric self-map
of `regionTensor S`; the cocycle compatibility forces these maps to
commute with the Ω/Ω′-extensions `regionEmbedLe`. -/
structure SectorEquivData (Ω Ω' : UnitFamily H) where
  /-- Finite-region isometries on the index-family-only tensor space. -/
  regionMap : (S : Finset ι) →
    regionTensor S (H := H) ≃ₗᵢ[ℂ] regionTensor S (H := H)
  /-- Compatibility with the directed system Ω-extensions on the source
  side and Ω′-extensions on the target side. -/
  regionMap_compat : ∀ {S T : Finset ι} (h : S ⊆ T)
      (x : regionTensor S (H := H)),
    regionMap T (regionEmbedLe Ω h x)
      = regionEmbedLe Ω' h (regionMap S x)

namespace SectorEquivData

/-- Identity transport for a unit family. -/
noncomputable def refl (Ω : UnitFamily H) : SectorEquivData Ω Ω where
  regionMap _ := LinearIsometryEquiv.refl ℂ _
  regionMap_compat _ _ := rfl

/-- Inverse transport: per-region inverses with reversed source/target. -/
noncomputable def symm {Ω Ω' : UnitFamily H} (d : SectorEquivData Ω Ω') :
    SectorEquivData Ω' Ω where
  regionMap S := (d.regionMap S).symm
  regionMap_compat {S T} h y := by
    apply (d.regionMap T).injective
    rw [LinearIsometryEquiv.apply_symm_apply, d.regionMap_compat h,
      LinearIsometryEquiv.apply_symm_apply]

/-- Composition of two transports along a common middle unit family. -/
noncomputable def trans {Ω Ω' Ω'' : UnitFamily H}
    (d₁ : SectorEquivData Ω Ω') (d₂ : SectorEquivData Ω' Ω'') :
    SectorEquivData Ω Ω'' where
  regionMap S := (d₁.regionMap S).trans (d₂.regionMap S)
  regionMap_compat {S T} h x := by
    simp only [LinearIsometryEquiv.trans_apply]
    rw [d₁.regionMap_compat h, d₂.regionMap_compat h]

@[simp]
theorem refl_regionMap_apply (Ω : UnitFamily H) (S : Finset ι)
    (x : regionTensor S (H := H)) :
    (SectorEquivData.refl Ω).regionMap S x = x := rfl

@[simp]
theorem symm_regionMap_apply {Ω Ω' : UnitFamily H} (d : SectorEquivData Ω Ω')
    (S : Finset ι) (y : regionTensor S (H := H)) :
    d.symm.regionMap S y = (d.regionMap S).symm y := rfl

@[simp]
theorem trans_regionMap_apply {Ω Ω' Ω'' : UnitFamily H}
    (d₁ : SectorEquivData Ω Ω') (d₂ : SectorEquivData Ω' Ω'')
    (S : Finset ι) (x : regionTensor S (H := H)) :
    (d₁.trans d₂).regionMap S x = d₂.regionMap S (d₁.regionMap S x) := rfl

end SectorEquivData

/-! ### Forward map at the colimit level (per-data) -/

variable {Ω Ω'}

/-- The forward fiber map at finset `S` for `SectorEquivData`: apply
`regionMap S` and push to `preITPSector Ω'`. -/
noncomputable def forwardFiberOfData (d : SectorEquivData Ω Ω')
    (S : Finset ι) :
    regionTensor S (H := H) →ₗ[ℂ] preITPSector Ω' :=
  (preITPSector.of Ω' S).comp (d.regionMap S).toLinearMap

@[simp]
theorem forwardFiberOfData_apply (d : SectorEquivData Ω Ω')
    (S : Finset ι) (x : regionTensor S (H := H)) :
    forwardFiberOfData d S x = preITPSector.of Ω' S (d.regionMap S x) := rfl

/-- Cocycle compatibility for `forwardFiberOfData`. -/
theorem forwardFiberOfData_cocycle (d : SectorEquivData Ω Ω')
    {S T : Finset ι} (hST : S ⊆ T) (x : regionTensor S (H := H)) :
    forwardFiberOfData d T (regionEmbedLe Ω hST x)
      = forwardFiberOfData d S x := by
  rw [forwardFiberOfData_apply, forwardFiberOfData_apply]
  rw [d.regionMap_compat hST]
  exact preITPSector.of_extend Ω' hST (d.regionMap S x)

/-- Lift `forwardFiberOfData` through the algebraic colimit. -/
noncomputable def forwardPreOfData (d : SectorEquivData Ω Ω') :
    preITPSector Ω →ₗ[ℂ] preITPSector Ω' :=
  Module.DirectLimit.lift ℂ (Finset ι)
    (fun S : Finset ι => regionTensor S (H := H))
    (regionDirectedLink Ω)
    (forwardFiberOfData d)
    (fun _ _ _ => forwardFiberOfData_cocycle d _)

@[simp]
theorem forwardPreOfData_of (d : SectorEquivData Ω Ω') (S : Finset ι)
    (x : regionTensor S (H := H)) :
    forwardPreOfData d (preITPSector.of Ω S x) = forwardFiberOfData d S x :=
  Module.DirectLimit.lift_of (R := ℂ)
    (G := fun S : Finset ι => regionTensor S (H := H))
    (f := regionDirectedLink Ω) _ _ x

/-- Inner-product preservation by `forwardPreOfData`. -/
theorem forwardPreOfData_inner (d : SectorEquivData Ω Ω')
    (x y : preITPSector Ω) :
    ⟪forwardPreOfData d x, forwardPreOfData d y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨S, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  rw [← hx, ← hy, forwardPreOfData_of, forwardPreOfData_of,
    forwardFiberOfData_apply, forwardFiberOfData_apply,
    inner_of_of, inner_of_of]
  exact (d.regionMap S).inner_map_map x' y'

/-- Round-trip on `preITPSector.of` representatives: composing forward
maps for `d` and `d.symm` gives the identity. -/
theorem forwardPreOfData_symm_round_trip_of (d : SectorEquivData Ω Ω')
    (S : Finset ι) (x : regionTensor S (H := H)) :
    forwardPreOfData d.symm (forwardPreOfData d (preITPSector.of Ω S x))
      = preITPSector.of Ω S x := by
  rw [forwardPreOfData_of, forwardFiberOfData_apply,
    forwardPreOfData_of, forwardFiberOfData_apply,
    SectorEquivData.symm_regionMap_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- Round-trip identity on the colimit: `d.symm` is a left inverse to `d`. -/
theorem forwardPreOfData_symm_round_trip (d : SectorEquivData Ω Ω')
    (x : preITPSector Ω) :
    forwardPreOfData d.symm (forwardPreOfData d x) = x := by
  obtain ⟨S, x', rfl⟩ := preITPSector.exists_of Ω x
  exact forwardPreOfData_symm_round_trip_of d S x'

/-- The pre-Hilbert isometric equivalence built from coherent transport
data. -/
noncomputable def preITPSectorEquivOfData (d : SectorEquivData Ω Ω') :
    preITPSector Ω ≃ₗᵢ[ℂ] preITPSector Ω' :=
  { toFun := forwardPreOfData d
    map_add' := (forwardPreOfData d).map_add
    map_smul' := (forwardPreOfData d).map_smul
    invFun := forwardPreOfData d.symm
    left_inv := forwardPreOfData_symm_round_trip d
    right_inv := by
      intro y
      obtain ⟨S, y', rfl⟩ := preITPSector.exists_of Ω' y
      rw [forwardPreOfData_of, forwardFiberOfData_apply,
        forwardPreOfData_of, forwardFiberOfData_apply,
        SectorEquivData.symm_regionMap_apply,
        LinearIsometryEquiv.apply_symm_apply]
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (forwardPreOfData_inner d x x) }

@[simp]
theorem preITPSectorEquivOfData_of (d : SectorEquivData Ω Ω')
    (S : Finset ι) (x : regionTensor S (H := H)) :
    preITPSectorEquivOfData d (preITPSector.of Ω S x)
      = preITPSector.of Ω' S (d.regionMap S x) := by
  change forwardPreOfData d _ = _
  rw [forwardPreOfData_of, forwardFiberOfData_apply]

@[simp]
theorem preITPSectorEquivOfData_symm_of (d : SectorEquivData Ω Ω')
    (S : Finset ι) (y : regionTensor S (H := H)) :
    (preITPSectorEquivOfData d).symm (preITPSector.of Ω' S y)
      = preITPSector.of Ω S ((d.regionMap S).symm y) := by
  change forwardPreOfData d.symm _ = _
  rw [forwardPreOfData_of, forwardFiberOfData_apply,
    SectorEquivData.symm_regionMap_apply]

/-! ### Hilbert-completion lift -/

/-- The full Hilbert-completion isometric equivalence built from
coherent same-index transport data. -/
noncomputable def sectorEquivOfData (d : SectorEquivData Ω Ω') :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω' :=
  let f := preITPSectorEquivOfData d
  let fc : preITPSector Ω →L[ℂ] preITPSector Ω' :=
    f.toLinearIsometry.toContinuousLinearMap
  let gc : preITPSector Ω' →L[ℂ] preITPSector Ω :=
    f.symm.toLinearIsometry.toContinuousLinearMap
  let fL : ITPSector (H := H) Ω →L[ℂ] ITPSector (H := H) Ω' := fc.completion
  let gL : ITPSector (H := H) Ω' →L[ℂ] ITPSector (H := H) Ω := gc.completion
  { toFun := fL
    map_add' := fL.map_add
    map_smul' := fL.map_smul
    invFun := gL
    left_inv := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (gL.continuous.comp fL.continuous) continuous_id) ?_
      intro a
      change gc.completion (fc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        ContinuousLinearMap.completion_apply_coe gc (fc a)]
      congr 1
      change f.symm (f a) = a
      exact f.left_inv a
    right_inv := fun y => by
      refine UniformSpace.Completion.induction_on y
        (isClosed_eq (fL.continuous.comp gL.continuous) continuous_id) ?_
      intro a
      change fc.completion (gc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe gc a,
        ContinuousLinearMap.completion_apply_coe fc (gc a)]
      congr 1
      change f (f.symm a) = a
      exact f.right_inv a
    norm_map' := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (continuous_norm.comp fL.continuous) continuous_norm) ?_
      intro a
      change ‖fc.completion ↑a‖ = ‖(↑a : UniformSpace.Completion (preITPSector Ω))‖
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact f.norm_map a }

variable (Ω Ω')

/-! ### Functorial laws -/

@[simp]
theorem sectorEquivOfData_refl :
    sectorEquivOfData (SectorEquivData.refl Ω)
      = LinearIsometryEquiv.refl ℂ (ITPSector (H := H) Ω) := by
  refine LinearIsometryEquiv.toLinearEquiv_injective ?_
  refine LinearEquiv.toEquiv_injective ?_
  refine Equiv.ext ?_
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (sectorEquivOfData (SectorEquivData.refl Ω)).continuous
      continuous_id
  · intro a
    -- Reduce to the pre-Hilbert level: sectorEquivOfData unfolds to
    -- `(preITPSectorEquivOfData _).toLinearIsometry.toContinuousLinearMap.completion`,
    -- and on `↑a` this returns `↑(preITPSectorEquivOfData ... a)`.
    set fc :
        preITPSector Ω →L[ℂ] preITPSector Ω :=
      ((preITPSectorEquivOfData (SectorEquivData.refl Ω)).toLinearIsometry).toContinuousLinearMap with hfc
    change fc.completion ↑a = ↑a
    rw [ContinuousLinearMap.completion_apply_coe]
    -- Now reduce to: ↑(preITPSectorEquivOfData (.refl Ω) a) = ↑a, i.e.,
    -- the underlying pre-Hilbert map is the identity.
    congr 1
    obtain ⟨S, a', rfl⟩ := preITPSector.exists_of Ω a
    change preITPSectorEquivOfData (.refl Ω) (preITPSector.of Ω S a')
      = preITPSector.of Ω S a'
    rw [preITPSectorEquivOfData_of]
    rfl

variable {Ω Ω'}

theorem sectorEquivOfData_symm (d : SectorEquivData Ω Ω') :
    (sectorEquivOfData d).symm = sectorEquivOfData d.symm := by
  refine LinearIsometryEquiv.toLinearEquiv_injective ?_
  refine LinearEquiv.toEquiv_injective ?_
  refine Equiv.ext ?_
  intro y
  refine UniformSpace.Completion.induction_on y ?_ ?_
  · exact isClosed_eq (sectorEquivOfData d).symm.continuous
      (sectorEquivOfData d.symm).continuous
  · intro a
    -- LHS unfolds to `(preITPSectorEquivOfData d).symm.toLI...completion ↑a`
    -- RHS unfolds to `(preITPSectorEquivOfData d.symm).toLI...completion ↑a`
    set lc :
        preITPSector Ω' →L[ℂ] preITPSector Ω :=
      (preITPSectorEquivOfData d).symm.toLinearIsometry.toContinuousLinearMap
    set rc :
        preITPSector Ω' →L[ℂ] preITPSector Ω :=
      (preITPSectorEquivOfData d.symm).toLinearIsometry.toContinuousLinearMap
    change lc.completion ↑a = rc.completion ↑a
    rw [ContinuousLinearMap.completion_apply_coe,
      ContinuousLinearMap.completion_apply_coe]
    -- After both rewrites, the goal is `↑(lc a) = ↑(rc a)`.
    -- `lc a` and `rc a` reduce to the same pre-Hilbert image
    -- `forwardPreOfData d.symm a` definitionally, so `congr 1` discharges
    -- the goal.
    congr 1

theorem sectorEquivOfData_trans
    {Ω Ω' Ω'' : UnitFamily H}
    (d₁ : SectorEquivData Ω Ω') (d₂ : SectorEquivData Ω' Ω'') :
    (sectorEquivOfData d₁).trans (sectorEquivOfData d₂)
      = sectorEquivOfData (d₁.trans d₂) := by
  refine LinearIsometryEquiv.toLinearEquiv_injective ?_
  refine LinearEquiv.toEquiv_injective ?_
  refine Equiv.ext ?_
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      ((sectorEquivOfData d₂).continuous.comp (sectorEquivOfData d₁).continuous)
      (sectorEquivOfData (d₁.trans d₂)).continuous
  · intro a
    set fc₁ :
        preITPSector Ω →L[ℂ] preITPSector Ω' :=
      (preITPSectorEquivOfData d₁).toLinearIsometry.toContinuousLinearMap
    set fc₂ :
        preITPSector Ω' →L[ℂ] preITPSector Ω'' :=
      (preITPSectorEquivOfData d₂).toLinearIsometry.toContinuousLinearMap
    set fc₁₂ :
        preITPSector Ω →L[ℂ] preITPSector Ω'' :=
      (preITPSectorEquivOfData (d₁.trans d₂)).toLinearIsometry.toContinuousLinearMap
    change fc₂.completion (fc₁.completion ↑a) = fc₁₂.completion ↑a
    rw [ContinuousLinearMap.completion_apply_coe fc₁ a,
      ContinuousLinearMap.completion_apply_coe fc₂ (fc₁ a),
      ContinuousLinearMap.completion_apply_coe fc₁₂ a]
    congr 1
    obtain ⟨S, a', rfl⟩ := preITPSector.exists_of Ω a
    change preITPSectorEquivOfData d₂ (preITPSectorEquivOfData d₁
        (preITPSector.of Ω S a'))
      = preITPSectorEquivOfData (d₁.trans d₂) (preITPSector.of Ω S a')
    rw [preITPSectorEquivOfData_of, preITPSectorEquivOfData_of,
      preITPSectorEquivOfData_of]
    rfl

variable (Ω Ω')

/-! ### Phase 5: Finite-support per-site constructor (`FiniteSiteIsoData`)

Per-site isometries chosen on a finite support, with the off-support
unit vectors required to agree.  The total family is *derived* by
filling the off-support sites with `LinearIsometryEquiv.refl`, which
makes the canonicity boundary explicit: only the finitely many on-support
choices are user-supplied. -/

/-- Finite-support per-site isometry data between two unit families. -/
structure FiniteSiteIsoData (Ω Ω' : UnitFamily H) where
  /-- The finite support carrying the user-chosen per-site rotations. -/
  support : Finset ι
  /-- Per-site isometries, supplied only on the support. -/
  siteIsoOn : (i : {i // i ∈ support}) → H i.val ≃ₗᵢ[ℂ] H i.val
  /-- The supplied rotations move `Ω i` to `Ω' i` on the support. -/
  maps_base_on : ∀ i : {i // i ∈ support},
    siteIsoOn i (Ω i.val) = Ω' i.val
  /-- Off-support, the two unit families coincide. -/
  off_support_eq : ∀ i, i ∉ support → (Ω i : H i) = Ω' i

namespace FiniteSiteIsoData

variable {Ω Ω'}

/-- Total per-site family derived from the support data: the user-chosen
rotation on the support, and `refl` off-support. -/
noncomputable def siteIsoTotal (d : FiniteSiteIsoData Ω Ω')
    (i : ι) : H i ≃ₗᵢ[ℂ] H i :=
  if hi : i ∈ d.support then d.siteIsoOn ⟨i, hi⟩
  else LinearIsometryEquiv.refl ℂ (H i)

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem siteIsoTotal_of_mem (d : FiniteSiteIsoData Ω Ω') {i : ι}
    (hi : i ∈ d.support) :
    d.siteIsoTotal i = d.siteIsoOn ⟨i, hi⟩ := by
  unfold siteIsoTotal; rw [dif_pos hi]

omit [∀ i, FiniteDimensional ℂ (H i)] in
theorem siteIsoTotal_of_not_mem (d : FiniteSiteIsoData Ω Ω') {i : ι}
    (hi : i ∉ d.support) :
    d.siteIsoTotal i = LinearIsometryEquiv.refl ℂ (H i) := by
  unfold siteIsoTotal; rw [dif_neg hi]

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- The total family carries `Ω i` to `Ω' i` at every index. -/
theorem siteIsoTotal_maps_base (d : FiniteSiteIsoData Ω Ω') (i : ι) :
    d.siteIsoTotal i (Ω i) = Ω' i := by
  by_cases hi : i ∈ d.support
  · rw [FiniteSiteIsoData.siteIsoTotal_of_mem _ hi]
    exact d.maps_base_on ⟨i, hi⟩
  · rw [FiniteSiteIsoData.siteIsoTotal_of_not_mem _ hi]
    change (Ω i : H i) = Ω' i
    exact d.off_support_eq i hi

end FiniteSiteIsoData

namespace SectorEquivData

variable {Ω Ω'}

/-- Region-level isometry derived from finite-support per-site data. -/
noncomputable def finiteSiteIso_regionMap (d : FiniteSiteIsoData Ω Ω')
    (S : Finset ι) :
    regionTensor S (H := H) ≃ₗᵢ[ℂ] regionTensor S (H := H) :=
  ForMathlib.PiTensorProduct.piTensorMapIsom (ι := {x // x ∈ S})
    (H := fun s : {x // x ∈ S} => H s.val)
    (fun s : {x // x ∈ S} => d.siteIsoTotal s.val)

@[simp]
theorem finiteSiteIso_regionMap_tprod (d : FiniteSiteIsoData Ω Ω')
    (S : Finset ι) (ξ : (s : {x // x ∈ S}) → H s.val) :
    finiteSiteIso_regionMap d S (PiTensorProduct.tprod ℂ ξ)
      = PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ S} => d.siteIsoTotal s.val (ξ s)) := by
  unfold finiteSiteIso_regionMap
  exact ForMathlib.PiTensorProduct.piTensorMapIsom_tprod
    (ι := {x // x ∈ S})
    (H := fun s : {x // x ∈ S} => H s.val) _ _

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Pointwise compatibility on tuple level: applying the per-site
rotation then extending via Ω' equals extending via Ω then applying the
per-site rotation. -/
theorem siteIsoTotal_extendVec (d : FiniteSiteIsoData Ω Ω')
    {S T : Finset ι} (hST : S ⊆ T)
    (ξ : (s : {x // x ∈ S}) → H s.val) (s' : {x // x ∈ T}) :
    d.siteIsoTotal s'.val (extendVec Ω hST ξ s')
      = extendVec Ω' hST
          (fun s : {x // x ∈ S} => d.siteIsoTotal s.val (ξ s)) s' := by
  by_cases hs : s'.val ∈ S
  · rw [extendVec_inside _ _ _ _ hs, extendVec_inside _ _ _ _ hs]
  · rw [extendVec_outside _ _ _ _ hs, extendVec_outside _ _ _ _ hs]
    exact FiniteSiteIsoData.siteIsoTotal_maps_base d s'.val

/-- Cocycle compatibility for the finite-support region map on tprods. -/
theorem finiteSiteIso_regionMap_compat_tprod
    (d : FiniteSiteIsoData Ω Ω') {S T : Finset ι} (hST : S ⊆ T)
    (ξ : (s : {x // x ∈ S}) → H s.val) :
    finiteSiteIso_regionMap d T (regionEmbedLe Ω hST (PiTensorProduct.tprod ℂ ξ))
      = regionEmbedLe Ω' hST
          (finiteSiteIso_regionMap d S (PiTensorProduct.tprod ℂ ξ)) := by
  rw [regionEmbedLe_tprod, finiteSiteIso_regionMap_tprod,
    finiteSiteIso_regionMap_tprod, regionEmbedLe_tprod]
  congr 1
  funext s'
  exact siteIsoTotal_extendVec d hST ξ s'

theorem finiteSiteIso_regionMap_compat (d : FiniteSiteIsoData Ω Ω')
    {S T : Finset ι} (hST : S ⊆ T) (x : regionTensor S (H := H)) :
    finiteSiteIso_regionMap d T (regionEmbedLe Ω hST x)
      = regionEmbedLe Ω' hST (finiteSiteIso_regionMap d S x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    simp only [map_smul]
    congr 1
    exact finiteSiteIso_regionMap_compat_tprod d hST ξ
  | add x₁ x₂ ih₁ ih₂ =>
    simp only [map_add, ih₁, ih₂]

/-- Build coherent transport data from finite-support per-site rotations. -/
noncomputable def ofFiniteSiteIso (d : FiniteSiteIsoData Ω Ω') :
    SectorEquivData Ω Ω' where
  regionMap := finiteSiteIso_regionMap d
  regionMap_compat _ _ := finiteSiteIso_regionMap_compat d _ _

end SectorEquivData

/-! ### `referenceRel` wrapper

`referenceRel Ω Ω'` provides a finite difference set off which Ω and Ω′
agree.  The constructor below uses
`exists_linearIsometryEquiv_of_unit` to pick a per-site rotation aligning
`Ω i` to `Ω' i` on the difference set — these are still per-site
`Classical.choice`s, but they live only inside the resulting
`FiniteSiteIsoData` and not as ambient `chooseRotation`s. -/

namespace SectorEquivData

variable {Ω Ω'}

/-- Finite-support data derived from a `referenceRel` witness, by
choosing per-site isometries on the (finite) difference set. -/
noncomputable def referenceRelFiniteSiteIso (h : referenceRel Ω Ω') :
    FiniteSiteIsoData Ω Ω' where
  support := h.toFinset
  siteIsoOn i :=
    Classical.choose (exists_linearIsometryEquiv_of_unit
      (Ω.norm_vec i.val) (Ω'.norm_vec i.val))
  maps_base_on i :=
    Classical.choose_spec (exists_linearIsometryEquiv_of_unit
      (Ω.norm_vec i.val) (Ω'.norm_vec i.val))
  off_support_eq i hi := by
    by_contra hne
    exact hi (Set.Finite.mem_toFinset h |>.mpr hne)

/-- Coherent transport data from a `referenceRel` witness. -/
noncomputable def ofReferenceRel (h : referenceRel Ω Ω') :
    SectorEquivData Ω Ω' :=
  ofFiniteSiteIso (referenceRelFiniteSiteIso h)

end SectorEquivData

/-! ### `C0SectorMorphism`: bundling `c0Rel` with coherent data

A `c0Rel` witness alone does not select a coherent map; this wrapper
records both the relation witness and a chosen coherent transport. -/

/-- A morphism inside the same Bratteli–Robinson C₀-sector class: a
relation witness together with chosen coherent transport data. -/
structure C0SectorMorphism (Ω Ω' : UnitFamily H) where
  /-- The Bratteli–Robinson C₀-relation witness placing `Ω` and `Ω'` in
  the same sector. -/
  rel : c0Rel Ω Ω'
  /-- The chosen coherent transport realising the equivalence. -/
  data : SectorEquivData Ω Ω'

/-! ### Phase 6: reindexed (group-action) sector transport (`ReindexedSectorTransportData`)

Group actions translate finite supports `S ↦ target S` for some
bijection-valued `target : Finset ι ≃ Finset ι`, so the natural per-region
isometry has type `regionTensor S ≃ₗᵢ regionTensor (target S)` rather than
`regionTensor S ≃ₗᵢ regionTensor S`.  This section defines the
corresponding transport structure and its colimit-level **forward** lift
to a `LinearIsometry preITPSector Ω → preITPSector Ω'`.

A two-sided `LinearIsometryEquiv` lift is left to consumers who can
supply data for both `g` and `g⁻¹`; this is the natural shape of
group-action covariance constructions. -/

/-- Coherent reindexed transport data between two unit families: a
finset-bijection `target` and per-region isometric equivalences
`regionTensor S ≃ₗᵢ regionTensor (target S)`, compatible with the
directed-system maps `regionEmbedLe`.

Only the **forward** direction is recorded.  The natural pairing for
group-action covariance is two `ReindexedSectorTransportData` instances —
one for `g` and one for `g⁻¹` — that together yield an equiv. -/
structure ReindexedSectorTransportData (Ω Ω' : UnitFamily H) where
  /-- Bijection of finite supports induced by the transport. -/
  target : Finset ι ≃ Finset ι
  /-- Subset-monotonicity of the forward bijection. -/
  target_mono : ∀ {S T : Finset ι}, S ⊆ T → target S ⊆ target T
  /-- Subset-monotonicity of the inverse bijection. -/
  target_symm_mono : ∀ {S T : Finset ι}, S ⊆ T → target.symm S ⊆ target.symm T
  /-- Per-region isometric equivalence to the target finset. -/
  regionMap : (S : Finset ι) →
    regionTensor S (H := H) ≃ₗᵢ[ℂ] regionTensor (target S) (H := H)
  /-- Compatibility with the directed-system Ω/Ω′-extensions. -/
  regionMap_compat : ∀ {S T : Finset ι} (h : S ⊆ T)
      (x : regionTensor S (H := H)),
    regionMap T (regionEmbedLe Ω h x)
      = regionEmbedLe Ω' (target_mono h) (regionMap S x)

variable {Ω Ω'}

/-- Type-level transport of a `regionTensor` element across an equality of
finite supports. -/
def regionTensorCast {S T : Finset ι}
    (h : S = T) (x : regionTensor S (H := H)) : regionTensor T (H := H) :=
  h ▸ x

omit [DecidableEq ι] [∀ i, FiniteDimensional ℂ (H i)] in
@[simp]
theorem regionTensorCast_rfl {S : Finset ι} (x : regionTensor S (H := H)) :
    regionTensorCast (rfl : S = S) x = x := rfl

omit [∀ i, FiniteDimensional ℂ (H i)] in
/-- Transport a `preITPSector.of` across an equality of finite supports. -/
theorem preITPSector.of_finset_cast {Ω : UnitFamily H} {A B : Finset ι}
    (h : A = B) (x : regionTensor B (H := H)) :
    preITPSector.of Ω A (regionTensorCast h.symm x) = preITPSector.of Ω B x := by
  subst h
  rfl

/-- The forward fiber map at finset `S` for reindexed transport. -/
noncomputable def forwardFiberOfReindexed
    (d : ReindexedSectorTransportData Ω Ω') (S : Finset ι) :
    regionTensor S (H := H) →ₗ[ℂ] preITPSector Ω' :=
  (preITPSector.of Ω' (d.target S)).comp (d.regionMap S).toLinearMap

@[simp]
theorem forwardFiberOfReindexed_apply
    (d : ReindexedSectorTransportData Ω Ω') (S : Finset ι)
    (x : regionTensor S (H := H)) :
    forwardFiberOfReindexed d S x
      = preITPSector.of Ω' (d.target S) (d.regionMap S x) := rfl

/-- Cocycle compatibility for `forwardFiberOfReindexed`. -/
theorem forwardFiberOfReindexed_cocycle
    (d : ReindexedSectorTransportData Ω Ω')
    {S T : Finset ι} (hST : S ⊆ T) (x : regionTensor S (H := H)) :
    forwardFiberOfReindexed d T (regionEmbedLe Ω hST x)
      = forwardFiberOfReindexed d S x := by
  rw [forwardFiberOfReindexed_apply, forwardFiberOfReindexed_apply,
    d.regionMap_compat hST]
  exact preITPSector.of_extend Ω' (d.target_mono hST) (d.regionMap S x)

/-- Lift `forwardFiberOfReindexed` through the algebraic colimit. -/
noncomputable def forwardPreOfReindexed
    (d : ReindexedSectorTransportData Ω Ω') :
    preITPSector Ω →ₗ[ℂ] preITPSector Ω' :=
  Module.DirectLimit.lift ℂ (Finset ι)
    (fun S : Finset ι => regionTensor S (H := H))
    (regionDirectedLink Ω)
    (forwardFiberOfReindexed d)
    (fun _ _ _ => forwardFiberOfReindexed_cocycle d _)

@[simp]
theorem forwardPreOfReindexed_of
    (d : ReindexedSectorTransportData Ω Ω') (S : Finset ι)
    (x : regionTensor S (H := H)) :
    forwardPreOfReindexed d (preITPSector.of Ω S x)
      = forwardFiberOfReindexed d S x :=
  Module.DirectLimit.lift_of (R := ℂ)
    (G := fun S : Finset ι => regionTensor S (H := H))
    (f := regionDirectedLink Ω) _ _ x

/-- Inner-product preservation by `forwardPreOfReindexed`. -/
theorem forwardPreOfReindexed_inner
    (d : ReindexedSectorTransportData Ω Ω') (x y : preITPSector Ω) :
    ⟪forwardPreOfReindexed d x, forwardPreOfReindexed d y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨S, x', y', hx, hy⟩ := preITPSector.exists_of₂ Ω x y
  rw [← hx, ← hy, forwardPreOfReindexed_of, forwardPreOfReindexed_of,
    forwardFiberOfReindexed_apply, forwardFiberOfReindexed_apply,
    inner_of_of, inner_of_of]
  exact (d.regionMap S).inner_map_map x' y'

/-- Bundled isometric forward map at the pre-Hilbert level. -/
noncomputable def preITPSectorMapOfReindexed
    (d : ReindexedSectorTransportData Ω Ω') :
    preITPSector Ω →ₗᵢ[ℂ] preITPSector Ω' :=
  { forwardPreOfReindexed d with
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (forwardPreOfReindexed_inner d x x) }

/-- The Hilbert-completion forward isometry built from a reindexed
transport.  Use this in pairs (one for `g`, one for `g⁻¹`) when an
equivalence is needed. -/
noncomputable def sectorMapOfReindexed
    (d : ReindexedSectorTransportData Ω Ω') :
    ITPSector (H := H) Ω →L[ℂ] ITPSector (H := H) Ω' :=
  (preITPSectorMapOfReindexed d).toContinuousLinearMap.completion

theorem sectorMapOfReindexed_apply_coe
    (d : ReindexedSectorTransportData Ω Ω') (a : preITPSector Ω) :
    sectorMapOfReindexed d (↑a : UniformSpace.Completion (preITPSector Ω))
      = (↑(forwardPreOfReindexed d a)
          : UniformSpace.Completion (preITPSector Ω')) := by
  change (preITPSectorMapOfReindexed d).toContinuousLinearMap.completion ↑a
    = ↑(forwardPreOfReindexed d a)
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

/-- Surjectivity of the forward pre-sector map for coherent reindexed data. -/
theorem preITPSectorMapOfReindexed_surjective
    (d : ReindexedSectorTransportData Ω Ω') :
    Function.Surjective (preITPSectorMapOfReindexed d) := by
  intro y
  obtain ⟨S, y', rfl⟩ := preITPSector.exists_of Ω' y
  -- Pull the representative back to `d.target.symm S`, casting through
  -- `d.target.apply_symm_apply S : d.target (d.target.symm S) = S`.
  have hS : d.target (d.target.symm S) = S := d.target.apply_symm_apply S
  refine ⟨preITPSector.of Ω (d.target.symm S)
      ((d.regionMap (d.target.symm S)).symm (regionTensorCast hS.symm y')), ?_⟩
  change forwardPreOfReindexed d
      (preITPSector.of Ω (d.target.symm S)
        ((d.regionMap (d.target.symm S)).symm (regionTensorCast hS.symm y')))
    = preITPSector.of Ω' S y'
  rw [forwardPreOfReindexed_of, forwardFiberOfReindexed_apply,
    LinearIsometryEquiv.apply_symm_apply]
  -- Goal: `of Ω' (d.target (d.target.symm S)) (regionTensorCast hS.symm y')
  --     = of Ω' S y'`, which is exactly `preITPSector.of_finset_cast hS y'`.
  exact preITPSector.of_finset_cast hS y'

/-- The pre-Hilbert isometric equivalence built from coherent reindexed
transport data. -/
noncomputable def preITPSectorEquivOfReindexed
    (d : ReindexedSectorTransportData Ω Ω') :
    preITPSector Ω ≃ₗᵢ[ℂ] preITPSector Ω' :=
  LinearIsometryEquiv.ofSurjective (preITPSectorMapOfReindexed d)
    (preITPSectorMapOfReindexed_surjective d)

/-- The full Hilbert-completion isometric equivalence built from coherent
reindexed transport data. -/
noncomputable def sectorEquivOfReindexedData
    (d : ReindexedSectorTransportData Ω Ω') :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω' :=
  let f := preITPSectorEquivOfReindexed d
  let fc : preITPSector Ω →L[ℂ] preITPSector Ω' :=
    f.toLinearIsometry.toContinuousLinearMap
  let gc : preITPSector Ω' →L[ℂ] preITPSector Ω :=
    f.symm.toLinearIsometry.toContinuousLinearMap
  let fL : ITPSector (H := H) Ω →L[ℂ] ITPSector (H := H) Ω' := fc.completion
  let gL : ITPSector (H := H) Ω' →L[ℂ] ITPSector (H := H) Ω := gc.completion
  { toFun := fL
    map_add' := fL.map_add
    map_smul' := fL.map_smul
    invFun := gL
    left_inv := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (gL.continuous.comp fL.continuous) continuous_id) ?_
      intro a
      change gc.completion (fc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        ContinuousLinearMap.completion_apply_coe gc (fc a)]
      congr 1
      change f.symm (f a) = a
      exact f.left_inv a
    right_inv := fun y => by
      refine UniformSpace.Completion.induction_on y
        (isClosed_eq (fL.continuous.comp gL.continuous) continuous_id) ?_
      intro a
      change fc.completion (gc.completion ↑a) = ↑a
      rw [ContinuousLinearMap.completion_apply_coe gc a,
        ContinuousLinearMap.completion_apply_coe fc (gc a)]
      congr 1
      change f (f.symm a) = a
      exact f.right_inv a
    norm_map' := fun x => by
      refine UniformSpace.Completion.induction_on x
        (isClosed_eq (continuous_norm.comp fL.continuous) continuous_norm) ?_
      intro a
      change ‖fc.completion ↑a‖ = ‖(↑a : UniformSpace.Completion (preITPSector Ω))‖
      rw [ContinuousLinearMap.completion_apply_coe fc a,
        UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact f.norm_map a }

/-! ### Phase 5b: Coherent `c0Rel`-indexed sector transport (`c0Transport`)

Given `h : c0Rel Ω Ω'`, transport between sectors `ITPSector Ω` and
`ITPSector Ω'` via the canonical representative `(⟦Ω⟧ : Quotient c0Equiv).out`.
Since `Ω ≈ Ω'` in `c0Equiv`, the quotient-classes agree (`⟦Ω⟧ = ⟦Ω'⟧`), and
both endpoints share a common representative.

The construction is non-canonical (depends on `chooseRotation` via
`noncanonicalSectorEquivAny`), but the **functorial laws**
`c0Transport_refl/_symm/_trans` hold by the quotient-representative
trick: the transport `Ω → Ω'` factors through the shared representative,
so refl/symm/trans manipulations reduce to algebra in the group
`E ≃ₗᵢ[ℂ] E` (Mathlib's `LinearIsometryEquiv` group structure) and a
single `Quotient.sound` rewrite. -/

section C0Transport

/-! #### `SectorEquivData.ofC0Rel`: non-canonical wrapping into `SectorEquivData` -/

/-- Cocycle compatibility for `regionRot` on elementary tensors at the
`regionTensor` level (a `regionMap`-level analogue of
`forwardFiberAny_cocycle_tprod`). -/
theorem regionRot_regionEmbedLe_compat_tprod (Ω Ω' : UnitFamily H)
    {S T : Finset ι} (hST : S ⊆ T) (ξ : (s : {x // x ∈ S}) → H s.val) :
    regionRot Ω Ω' T (regionEmbedLe Ω hST (PiTensorProduct.tprod ℂ ξ))
      = regionEmbedLe Ω' hST (regionRot Ω Ω' S (PiTensorProduct.tprod ℂ ξ)) := by
  rw [regionEmbedLe_tprod, regionRot_tprod, regionRot_tprod, regionEmbedLe_tprod]
  congr 1
  funext s'
  exact rotateExtendVec_eq Ω Ω' S T hST ξ s'

/-- Cocycle compatibility for `regionRot` on all `regionTensor` elements. -/
theorem regionRot_regionEmbedLe_compat (Ω Ω' : UnitFamily H)
    {S T : Finset ι} (hST : S ⊆ T) (x : regionTensor S (H := H)) :
    regionRot Ω Ω' T (regionEmbedLe Ω hST x)
      = regionEmbedLe Ω' hST (regionRot Ω Ω' S x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
    simp only [map_smul]
    congr 1
    exact regionRot_regionEmbedLe_compat_tprod Ω Ω' hST ξ
  | add x₁ x₂ ih₁ ih₂ =>
    simp only [map_add, ih₁, ih₂]

namespace SectorEquivData

/-- Non-canonical coherent transport data derived from a `c0Rel` witness,
built from per-site rotations `chooseRotation Ω Ω' s`.

**Non-canonical**: the underlying rotations depend on `Classical.choice`,
so this `SectorEquivData` does not satisfy strict refl/symm/trans
identities at the `regionMap` level.  For the canonical functorial
transport at the `ITPSector` level, use `c0Transport` instead — it
factors through a shared `Quotient c0Equiv`-representative and is built
to satisfy `c0Transport_refl/_symm/_trans`. -/
noncomputable def ofC0Rel (_h : c0Rel Ω Ω') : SectorEquivData Ω Ω' where
  regionMap := regionRot Ω Ω'
  regionMap_compat := fun {_ _} hST x => regionRot_regionEmbedLe_compat Ω Ω' hST x

end SectorEquivData

/-! #### `c0Transport`: canonical `ITPSector`-level transport -/

/-- Coherent same-sector transport derived from a `c0Rel` witness.

Defined as the round-trip through the canonical `Quotient c0Equiv`
representative: `ITPSector Ω → ITPSector (⟦Ω⟧).out → ITPSector Ω'`.  The
two legs use `noncanonicalSectorEquivAny` and are non-canonical, but the
**shared representative** makes the construction functorial in `c0Rel`
(see `c0Transport_refl/_symm/_trans`). -/
noncomputable def c0Transport (h : c0Rel Ω Ω') :
    ITPSector (H := H) Ω ≃ₗᵢ[ℂ] ITPSector (H := H) Ω' :=
  let _ := h
  (noncanonicalSectorEquivAny Ω (Quotient.mk c0Equiv Ω).out).trans
    (noncanonicalSectorEquivAny Ω' (Quotient.mk c0Equiv Ω).out).symm

/-- **Identity law** for `c0Transport`: the canonical transport along
`c0Rel.refl Ω` is the identity on `ITPSector Ω`. -/
@[simp]
theorem c0Transport_refl (Ω : UnitFamily H) :
    c0Transport (c0Rel.refl Ω)
      = LinearIsometryEquiv.refl ℂ (ITPSector (H := H) Ω) := by
  unfold c0Transport
  exact LinearIsometryEquiv.self_trans_symm _

/-- **Inverse law** for `c0Transport`: the inverse of the transport along
`h : c0Rel Ω Ω'` agrees with the transport along the symmetric witness
`h.symm : c0Rel Ω' Ω`. -/
theorem c0Transport_symm {Ω Ω' : UnitFamily H} (h : c0Rel Ω Ω') :
    (c0Transport h).symm = c0Transport h.symm := by
  have hQ : (Quotient.mk c0Equiv Ω : Quotient c0Equiv) = Quotient.mk c0Equiv Ω' :=
    Quotient.sound h
  have hout : ((Quotient.mk c0Equiv Ω' : Quotient c0Equiv).out : UnitFamily H)
      = (Quotient.mk c0Equiv Ω : Quotient c0Equiv).out := by rw [hQ]
  unfold c0Transport
  rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_symm, hout]

/-- **Composition law** for `c0Transport`: transporting along the
composed `c0Rel` witness `h₁.trans h₂` agrees with composing the
individual transports. -/
theorem c0Transport_trans {Ω Ω' Ω'' : UnitFamily H}
    (h₁ : c0Rel Ω Ω') (h₂ : c0Rel Ω' Ω'') :
    (c0Transport h₁).trans (c0Transport h₂)
      = c0Transport (h₁.trans h₂) := by
  have hQ : (Quotient.mk c0Equiv Ω : Quotient c0Equiv) = Quotient.mk c0Equiv Ω' :=
    Quotient.sound h₁
  have hout : ((Quotient.mk c0Equiv Ω' : Quotient c0Equiv).out : UnitFamily H)
      = (Quotient.mk c0Equiv Ω : Quotient c0Equiv).out := by rw [hQ]
  unfold c0Transport
  rw [hout]
  -- After `hout`-rewrite, both middle factors `(NSEA Ω' rep).symm` and
  -- `NSEA Ω' rep` share the same representative and cancel pointwise via
  -- `apply_symm_apply`.
  ext x
  simp only [LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

end C0Transport

end UnitFamily

end InfiniteTensor
