module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.QuasiLocal
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Isotony
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Locality
public import QuantumSystem.Algebra.Geometry.Cone
public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionColimit
public import QuantumSystem.Algebra.CStarAlgebra.Representation.DirectSum
public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.LpCongrLeft

/-!
# Direct sum over all concrete lattice sectors

`globalHilbert L Ω` (`GlobalHilbert.lean`) is the concrete ℓ² model of the
incomplete infinite tensor product selected by a single basis tuple
`Ω : (s : L) → localIdx s`.  Tuples agreeing off a finite set of sites select
the *same* sector (`globalIdx L Ω` depends only on the equivalence class), so
the genuine collection of concrete sectors is the quotient

`SectorClass L := ((s : L) → localIdx s) / (agree off a finite set)`.

This file assembles the **Bratteli–Robinson complete infinite tensor product**
(Vol. 2 §2.7.2) as the `ℓ²` direct sum of the per-sector Hilbert spaces,

`globalDirectSum L := ⨁_{c : SectorClass L} globalHilbert L c.out`,

and lifts the single-sector observable-algebra API to it block-diagonally:

* **algebra action core** — `localEmbedDS`, `localSubalgebraDS`,
  `quasiLocalDS` (mirroring `LocalEmbed.lean` / `QuasiLocal.lean`);
* **isotony / locality** — `localSubalgebraDS_le_of_subset`,
  `localEmbedDS_commute_of_disjoint` (mirroring `Isotony.lean` / `Locality.lean`);
* **cone / colimit** — `localConeSubalgDS`, `complementConeSubalgDS`,
  `dense_iUnion_regionEmbedDS_range` (mirroring `Cone.lean` / `RegionColimit.lean`).

The block-diagonal operator is built by reusing the criterion-agnostic
`SectorFamily` machinery of `CStarAlgebra/Representation/DirectSum.lean`: for each region `Λ` the
family `c ↦ (globalHilbert L c.out, localEmbedHom c.out Λ)` is a
`SectorFamily (ℋ(Λ) →L[ℂ] ℋ(Λ))` whose `directSumHilbert` is definitionally
`globalDirectSum L`, so `directSumCLM` supplies the bounded block-diagonal
operator (uniform bound `‖M‖`) and `directSumCLM_adjoint` supplies the
involution.

The vacuum vector and group-covariance API are deliberately **not** lifted
here: a direct sum has one vacuum per sector and a genuine symmetry can
permute sectors, both of which need separate treatment.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace
open ENNReal

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]

/-! ### The sector index: tuples modulo finite variation -/

/-- Two sector tuples are equivalent when they agree off a finite set of
sites.  This is exactly the relation defining membership in `globalIdx`, so
equivalent tuples select the same sector Hilbert space. -/
def SectorRel :
    ((s : L) → localIdx (L := L) s) → ((s : L) → localIdx (L := L) s) → Prop :=
  fun Ω Ω' => ∃ Γ : Finset L, ∀ s ∉ Γ, Ω s = Ω' s

/-- `SectorRel` is an equivalence relation, packaged as a `Setoid`. -/
def sectorSetoid : Setoid ((s : L) → localIdx (L := L) s) where
  r := SectorRel L
  iseqv :=
    { refl := fun _ => ⟨∅, fun _ _ => rfl⟩
      symm := fun ⟨Γ, h⟩ => ⟨Γ, fun s hs => (h s hs).symm⟩
      trans := fun ⟨Γ₁, h₁⟩ ⟨Γ₂, h₂⟩ =>
        ⟨Γ₁ ∪ Γ₂, fun s hs =>
          (h₁ s (fun h => hs (Finset.mem_union_left _ h))).trans
            (h₂ s (fun h => hs (Finset.mem_union_right _ h)))⟩ }

/-- The type of **concrete lattice sectors**: basis tuples modulo finite
variation.  The direct sum `globalDirectSum L` runs over this quotient. -/
abbrev SectorClass : Type _ := Quotient (sectorSetoid L)

/-! ### The complete tensor product as a sector direct sum -/

/-- The **complete infinite tensor product** of the lattice system: the `ℓ²`
direct sum `⨁_{c : SectorClass L} globalHilbert L c.out` of the per-sector
Hilbert spaces (Bratteli–Robinson Vol. 2 §2.7.2). -/
noncomputable abbrev globalDirectSum : Type _ :=
  ↥(lp (fun c : SectorClass L => globalHilbert L c.out) 2)

/-- `globalDirectSum L` is a complex Hilbert space, inherited from `lp`. -/
noncomputable instance instComplexHilbertSpace_globalDirectSum :
    ComplexHilbertSpace (globalDirectSum L) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance

/-! ### Coordinate API

For each sector `c`, the `c`-th coordinate of `globalDirectSum L` is
`globalHilbert L c.out`. -/

/-- Coordinate projection onto the `c`-th sector, as a continuous linear map. -/
noncomputable def sectorComponentDS (c : SectorClass L) :
    globalDirectSum L →L[ℂ] globalHilbert L c.out :=
  lp.evalCLM (𝕜 := ℂ) (fun c' : SectorClass L => globalHilbert L c'.out) 2 c

/-- Coordinate embedding of the `c`-th sector into `globalDirectSum L`, as a
linear isometry (Mathlib's `lp.single` packaged as a `LinearIsometry`). -/
noncomputable def sectorEmbedDS (c : SectorClass L) :
    globalHilbert L c.out →ₗᵢ[ℂ] globalDirectSum L :=
  letI : DecidableEq (SectorClass L) := Classical.decEq _
  { toLinearMap :=
      (lp.singleContinuousLinearMap (𝕜 := ℂ)
        (E := fun c' : SectorClass L => globalHilbert L c'.out) 2 c).toLinearMap
    norm_map' := fun x =>
      lp.norm_single (E := fun c' : SectorClass L => globalHilbert L c'.out)
        (by norm_num : (0 : ℝ≥0∞) < 2) c x }

@[simp] lemma sectorEmbedDS_apply_coord (c : SectorClass L)
    (v : globalHilbert L c.out) :
    (sectorEmbedDS L c v).val c = v := by
  letI : DecidableEq (SectorClass L) := Classical.decEq _
  change (lp.single (E := fun c' : SectorClass L => globalHilbert L c'.out) 2 c v) c = v
  exact lp.single_apply_self
    (E := fun c' : SectorClass L => globalHilbert L c'.out) 2 c v

lemma sectorEmbedDS_apply_coord_ne (c : SectorClass L)
    (v : globalHilbert L c.out) {c' : SectorClass L} (h : c' ≠ c) :
    (sectorEmbedDS L c v).val c' = 0 := by
  letI : DecidableEq (SectorClass L) := Classical.decEq _
  change (lp.single (E := fun c'' : SectorClass L => globalHilbert L c''.out) 2 c v) c' = 0
  exact lp.single_apply_ne
    (E := fun c'' : SectorClass L => globalHilbert L c''.out) 2 c v h

@[simp] theorem sectorComponentDS_sectorEmbedDS (c : SectorClass L)
    (v : globalHilbert L c.out) :
    sectorComponentDS L c (sectorEmbedDS L c v) = v :=
  sectorEmbedDS_apply_coord L c v

/-! ### The per-region sector family -/

/-- For a region `Λ`, the representation of `ℋ(Λ) →L[ℂ] ℋ(Λ)` on the `c`-sector
Hilbert space via `localEmbedHom`. -/
noncomputable def localSectorRep (Λ : Finset L) (c : SectorClass L) :
    CStarRep (ℋ(Λ) →L[ℂ] ℋ(Λ)) where
  H := globalHilbert L c.out
  π := (localEmbedHom (Ω := c.out) Λ).toNonUnitalStarAlgHom

/-- The sector family for region `Λ`: all concrete sectors, each carrying the
`localEmbedHom`-representation of the finite-region operator algebra.  Its
`directSumHilbert` is definitionally `globalDirectSum L`. -/
noncomputable def localSectorFamily (Λ : Finset L) :
    SectorFamily (ℋ(Λ) →L[ℂ] ℋ(Λ)) where
  Index := SectorClass L
  rep := localSectorRep L Λ

/-! ### Block-diagonal local embedding -/

/-- The block-diagonal lift of the finite-region operator `M` to the sector
direct sum: it acts as `localEmbed c.out Λ M` on each sector component.  Bounded
by `‖M‖` uniformly, via `SectorFamily.directSumCLM`. -/
noncomputable def localEmbedDS (Λ : Finset L) (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    globalDirectSum L →L[ℂ] globalDirectSum L :=
  (localSectorFamily L Λ).directSumCLM M

@[simp] theorem localEmbedDS_apply_coord (Λ : Finset L) (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (ψ : globalDirectSum L) (c : SectorClass L) :
    (localEmbedDS L Λ M ψ).val c = localEmbed (Ω := c.out) Λ M (ψ.val c) := rfl

/-- Coordinate-wise extensionality for operators on the sector direct sum. -/
theorem ext_of_coord {S T : globalDirectSum L →L[ℂ] globalDirectSum L}
    (h : ∀ (ψ : globalDirectSum L) (c : SectorClass L), (S ψ).val c = (T ψ).val c) :
    S = T := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  apply Subtype.ext
  funext c
  exact h ψ c

/-! ### Structural lemmas for `localEmbedDS`

Each mirrors the single-sector `localEmbed_*` lemma, reduced coordinate-wise.
The involution `_star` is the only one not coordinate-trivial: it reuses
`SectorFamily.directSumCLM_adjoint`. -/

theorem localEmbedDS_one (Λ : Finset L) :
    localEmbedDS L Λ (1 : ℋ(Λ) →L[ℂ] ℋ(Λ)) = 1 := by
  refine ext_of_coord L fun ψ c => ?_
  rw [localEmbedDS_apply_coord,
      show (1 : ℋ(Λ) →L[ℂ] ℋ(Λ)) = ContinuousLinearMap.id ℂ (ℋ(Λ)) from rfl,
      localEmbed_one]
  rfl

theorem localEmbedDS_zero (Λ : Finset L) :
    localEmbedDS L Λ (0 : ℋ(Λ) →L[ℂ] ℋ(Λ)) = 0 := by
  refine ext_of_coord L fun ψ c => ?_
  simp only [localEmbedDS_apply_coord, localEmbed_zero, ContinuousLinearMap.zero_apply,
    lp.coeFn_zero, Pi.zero_apply]

theorem localEmbedDS_add (Λ : Finset L) (M N : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedDS L Λ (M + N) = localEmbedDS L Λ M + localEmbedDS L Λ N := by
  refine ext_of_coord L fun ψ c => ?_
  simp only [localEmbedDS_apply_coord, localEmbed_add, ContinuousLinearMap.add_apply,
    lp.coeFn_add, Pi.add_apply]

theorem localEmbedDS_smul (Λ : Finset L) (c : ℂ) (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedDS L Λ (c • M) = c • localEmbedDS L Λ M := by
  refine ext_of_coord L fun ψ d => ?_
  simp only [localEmbedDS_apply_coord, localEmbed_smul, ContinuousLinearMap.smul_apply,
    lp.coeFn_smul, Pi.smul_apply]

theorem localEmbedDS_mul (Λ : Finset L) (M N : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedDS L Λ (M.comp N)
      = (localEmbedDS L Λ M).comp (localEmbedDS L Λ N) := by
  refine ext_of_coord L fun ψ c => ?_
  simp only [localEmbedDS_apply_coord, ContinuousLinearMap.comp_apply, localEmbed_mul]

theorem localEmbedDS_star (Λ : Finset L) (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedDS L Λ (star M) = star (localEmbedDS L Λ M) := by
  change (localSectorFamily L Λ).directSumCLM (star M)
      = star ((localSectorFamily L Λ).directSumCLM M)
  rw [ContinuousLinearMap.star_eq_adjoint ((localSectorFamily L Λ).directSumCLM M),
      SectorFamily.directSumCLM_adjoint]

/-! ### The local subalgebra `𝔄_DS(Λ) ↪ B(globalDirectSum L)` -/

/-- `M ↦ localEmbedDS Λ M` as a unital `*`-algebra homomorphism. -/
noncomputable def localEmbedDSHom (Λ : Finset L) :
    (ℋ(Λ) →L[ℂ] ℋ(Λ)) →⋆ₐ[ℂ]
    (globalDirectSum L →L[ℂ] globalDirectSum L) where
  toFun := localEmbedDS L Λ
  map_one' := localEmbedDS_one L Λ
  map_mul' := localEmbedDS_mul L Λ
  map_zero' := localEmbedDS_zero L Λ
  map_add' := localEmbedDS_add L Λ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, localEmbedDS_smul, localEmbedDS_one,
        Algebra.algebraMap_eq_smul_one]
  map_star' := localEmbedDS_star L Λ

@[simp] theorem localEmbedDSHom_apply (Λ : Finset L) (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedDSHom L Λ M = localEmbedDS L Λ M := rfl

/-- The block-diagonal embedding is injective whenever at least one concrete
sector exists: a finite-region operator is determined by its action on any
single sector component (reduces to `localEmbedHom_injective`). -/
theorem localEmbedDSHom_injective [Nonempty (SectorClass L)] (Λ : Finset L) :
    Function.Injective (localEmbedDSHom L Λ) := by
  rw [injective_iff_map_eq_zero]
  intro M hM
  have hM' : localEmbedDS L Λ M = 0 := hM
  obtain ⟨c⟩ := ‹Nonempty (SectorClass L)›
  have hc : localEmbed (Ω := c.out) Λ M = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have h0 : localEmbedDS L Λ M (sectorEmbedDS L c v) = 0 := by
      rw [hM']; simp
    have hval := congrArg (fun w : globalDirectSum L => w.val c) h0
    simp only [localEmbedDS_apply_coord, sectorEmbedDS_apply_coord] at hval
    simpa using hval
  exact (injective_iff_map_eq_zero _).mp (localEmbedHom_injective (Ω := c.out) Λ) M hc

/-- The represented local subalgebra at `Λ` on the sector direct sum. -/
noncomputable def localSubalgebraDS (Λ : Finset L) :
    StarSubalgebra ℂ (globalDirectSum L →L[ℂ] globalDirectSum L) :=
  (localEmbedDSHom L Λ).range

theorem mem_localSubalgebraDS (Λ : Finset L)
    (T : globalDirectSum L →L[ℂ] globalDirectSum L) :
    T ∈ localSubalgebraDS L Λ
      ↔ ∃ M : ℋ(Λ) →L[ℂ] ℋ(Λ), localEmbedDS L Λ M = T := by
  change T ∈ ((localEmbedDSHom L Λ).toAlgHom.range : Subalgebra ℂ _) ↔ _
  exact AlgHom.mem_range _

/-! ### The quasi-local algebra on the sector direct sum -/

/-- Algebraic core `⨆ Λ, localSubalgebraDS Λ` on the sector direct sum. -/
noncomputable def quasiLocalSubalgDS :
    StarSubalgebra ℂ (globalDirectSum L →L[ℂ] globalDirectSum L) :=
  ⨆ Λ : Finset L, localSubalgebraDS L Λ

/-- The **quasi-local algebra on the complete tensor product**: norm closure
of the algebraic core. -/
noncomputable def quasiLocalDS :
    StarSubalgebra ℂ (globalDirectSum L →L[ℂ] globalDirectSum L) :=
  (quasiLocalSubalgDS L).topologicalClosure

theorem localSubalgebraDS_le_quasiLocalSubalgDS (Λ : Finset L) :
    localSubalgebraDS L Λ ≤ quasiLocalSubalgDS L :=
  le_iSup (fun Λ : Finset L => localSubalgebraDS L Λ) Λ

theorem localSubalgebraDS_le_quasiLocalDS (Λ : Finset L) :
    localSubalgebraDS L Λ ≤ quasiLocalDS L :=
  (localSubalgebraDS_le_quasiLocalSubalgDS L Λ).trans
    (StarSubalgebra.le_topologicalClosure _)

theorem quasiLocalSubalgDS_le_quasiLocalDS :
    quasiLocalSubalgDS L ≤ quasiLocalDS L :=
  StarSubalgebra.le_topologicalClosure _

theorem isClosed_quasiLocalDS :
    IsClosed
      (↑(quasiLocalDS L) :
        Set (globalDirectSum L →L[ℂ] globalDirectSum L)) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance instIsClosed_quasiLocalDS :
    IsClosed (SetLike.coe (quasiLocalDS L)) :=
  isClosed_quasiLocalDS L

/-- The **quasi-local algebra on the complete tensor product is a unital
C⋆-algebra**, via the closed-subalgebra instance. -/
noncomputable instance instCStarAlgebra_quasiLocalDS :
    CStarAlgebra ↥(quasiLocalDS L) :=
  inferInstance

/-! ### Isotony

For `Λ ⊆ Λ'`, lifting an operator and embedding via `localEmbedDS Λ'` gives the
same block-diagonal operator as embedding via `localEmbedDS Λ`, so the local
subalgebras are nested. -/

/-- Compatibility of `localEmbedDS` with the isotony lift `regionLift`. -/
theorem localEmbedDS_regionLift_eq {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedDS L Λ' (regionLift h M) = localEmbedDS L Λ M := by
  refine ext_of_coord L fun ψ c => ?_
  simp only [localEmbedDS_apply_coord]
  rw [localEmbed_regionLift_eq]

/-- **Isotony** on the sector direct sum: for `Λ ⊆ Λ'`, the local subalgebra
at `Λ` is contained in the local subalgebra at `Λ'`. -/
theorem localSubalgebraDS_le_of_subset {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    localSubalgebraDS L Λ ≤ localSubalgebraDS L Λ' := by
  intro T hT
  obtain ⟨M, hM⟩ := (mem_localSubalgebraDS L Λ T).mp hT
  exact (mem_localSubalgebraDS L Λ' T).mpr
    ⟨regionLift h M, by rw [localEmbedDS_regionLift_eq, hM]⟩

/-! ### Locality

Operators block-diagonally embedded from disjoint regions commute, because
they commute sector-by-sector (`localEmbed_commute_of_disjoint`). -/

/-- **Locality** at the operator level on the sector direct sum. -/
theorem localEmbedDS_commute_of_disjoint {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (M₁ : ℋ(Λ₁) →L[ℂ] ℋ(Λ₁)) (M₂ : ℋ(Λ₂) →L[ℂ] ℋ(Λ₂)) :
    Commute (localEmbedDS L Λ₁ M₁) (localEmbedDS L Λ₂ M₂) := by
  have key : localEmbedDS L Λ₁ M₁ * localEmbedDS L Λ₂ M₂
           = localEmbedDS L Λ₂ M₂ * localEmbedDS L Λ₁ M₁ := by
    refine ext_of_coord L fun ψ c => ?_
    simp only [ContinuousLinearMap.mul_apply, localEmbedDS_apply_coord]
    have hcomm := congrArg
      (fun T : globalHilbert L c.out →L[ℂ] globalHilbert L c.out => T (ψ.val c))
      (localEmbed_commute_of_disjoint (Ω := c.out) hd M₁ M₂)
    simpa [ContinuousLinearMap.mul_apply] using hcomm
  exact key

/-- **Locality** at the StarSubalgebra level on the sector direct sum. -/
theorem localSubalgebraDS_commute_of_disjoint {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : globalDirectSum L →L[ℂ] globalDirectSum L}
    (h₁ : T₁ ∈ localSubalgebraDS L Λ₁) (h₂ : T₂ ∈ localSubalgebraDS L Λ₂) :
    Commute T₁ T₂ := by
  obtain ⟨M₁, hM₁⟩ := (mem_localSubalgebraDS L Λ₁ T₁).mp h₁
  obtain ⟨M₂, hM₂⟩ := (mem_localSubalgebraDS L Λ₂ T₂).mp h₂
  rw [← hM₁, ← hM₂]
  exact localEmbedDS_commute_of_disjoint L hd M₁ M₂

/-! ### Cone-localised subalgebras on the sector direct sum

Mirror of `Cone.lean`, with `localSubalgebra` replaced by `localSubalgebraDS`. -/

/-- The local C\*-subalgebra supported in a cone `Λ` on the sector direct sum. -/
noncomputable def localConeSubalgDS (Λ : Cone L) :
    StarSubalgebra ℂ (globalDirectSum L →L[ℂ] globalDirectSum L) :=
  (⨆ (Λ' : Finset L) (_ : (↑Λ' : Set L) ⊆ Λ.region),
    localSubalgebraDS L Λ').topologicalClosure

/-- The C\*-subalgebra of operators localised outside the cone `Λ` on the
sector direct sum. -/
noncomputable def complementConeSubalgDS (Λ : Cone L) :
    StarSubalgebra ℂ (globalDirectSum L →L[ℂ] globalDirectSum L) :=
  (⨆ (Λ' : Finset L) (_ : Disjoint (↑Λ' : Set L) Λ.region),
    localSubalgebraDS L Λ').topologicalClosure

lemma localConeSubalgDS_mono {Λ Λ' : Cone L} (h : Λ.region ⊆ Λ'.region) :
    localConeSubalgDS L Λ ≤ localConeSubalgDS L Λ' := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  refine iSup_le fun Λ'' => iSup_le fun hsub => ?_
  exact le_iSup_of_le Λ'' (le_iSup_of_le (hsub.trans h) le_rfl)

lemma complementConeSubalgDS_antimono {Λ Λ' : Cone L} (h : Λ.region ⊆ Λ'.region) :
    complementConeSubalgDS L Λ' ≤ complementConeSubalgDS L Λ := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  refine iSup_le fun Λ'' => iSup_le fun hd => ?_
  have hd' : Disjoint (↑Λ'' : Set L) Λ.region := hd.mono_right h
  exact le_iSup_of_le Λ'' (le_iSup_of_le hd' le_rfl)

lemma localConeSubalgDS_le_quasiLocalDS (Λ : Cone L) :
    localConeSubalgDS L Λ ≤ quasiLocalDS L := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  exact iSup_le fun Λ' => iSup_le fun _ => le_iSup _ Λ'

lemma complementConeSubalgDS_le_quasiLocalDS (Λ : Cone L) :
    complementConeSubalgDS L Λ ≤ quasiLocalDS L := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  exact iSup_le fun Λ' => iSup_le fun _ => le_iSup _ Λ'

lemma complementConeSubalgDS_union_le_left (Λ₁ Λ₂ : Cone L) :
    complementConeSubalgDS L (Λ₁.union Λ₂) ≤ complementConeSubalgDS L Λ₁ :=
  complementConeSubalgDS_antimono L (Cone.subset_union_left Λ₁ Λ₂)

lemma complementConeSubalgDS_union_le_right (Λ₁ Λ₂ : Cone L) :
    complementConeSubalgDS L (Λ₁.union Λ₂) ≤ complementConeSubalgDS L Λ₂ :=
  complementConeSubalgDS_antimono L (Cone.subset_union_right Λ₁ Λ₂)

lemma localConeSubalgDS_le_complementConeSubalgDS {C Λ : Cone L}
    (h : Disjoint C.region Λ.region) :
    localConeSubalgDS L C ≤ complementConeSubalgDS L Λ := by
  refine StarSubalgebra.topologicalClosure_minimal ?_
    (StarSubalgebra.isClosed_topologicalClosure _)
  refine iSup_le fun Λ' => iSup_le fun hsub => ?_
  have hd : Disjoint (↑Λ' : Set L) Λ.region := Set.disjoint_of_subset_left hsub h
  refine le_trans ?_ (StarSubalgebra.le_topologicalClosure _)
  exact le_iSup_of_le Λ' (le_iSup_of_le hd le_rfl)

/-! ### Region-to-direct-sum embedding and density

`regionEmbedDS c Λ` embeds a finite-region Hilbert space into the `c`-sector
component, then into the direct sum. -/

/-- Region-to-direct-sum isometric embedding: `regionEmbed` into the `c`-sector
component, followed by the sector embedding. -/
noncomputable def regionEmbedDS (c : SectorClass L) (Λ : Finset L) :
    regionHilbert Λ →ₗᵢ[ℂ] globalDirectSum L :=
  (sectorEmbedDS L c).comp (regionEmbed c.out Λ)

@[simp] theorem regionEmbedDS_apply (c : SectorClass L) (Λ : Finset L)
    (ξ : regionHilbert Λ) :
    regionEmbedDS L c Λ ξ = sectorEmbedDS L c (regionEmbed c.out Λ ξ) := rfl

/-- The region-to-direct-sum embedding preserves inner products. -/
theorem regionEmbedDS_inner (c : SectorClass L) (Λ : Finset L)
    (ξ η : regionHilbert Λ) :
    ⟪regionEmbedDS L c Λ ξ, regionEmbedDS L c Λ η⟫_ℂ = ⟪ξ, η⟫_ℂ :=
  (regionEmbedDS L c Λ).inner_map_map ξ η

/-- Inner product of a sector embedding with an arbitrary vector picks out the
corresponding sector component. -/
theorem inner_sectorEmbedDS_left (c : SectorClass L)
    (w : globalHilbert L c.out) (y : globalDirectSum L) :
    ⟪sectorEmbedDS L c w, y⟫_ℂ = ⟪w, y.val c⟫_ℂ := by
  letI : DecidableEq (SectorClass L) := Classical.decEq _
  change ⟪(lp.single 2 c w : globalDirectSum L), y⟫_ℂ = ⟪w, y.val c⟫_ℂ
  rw [lp.inner_single_left]

/-- **Density / Hilbert co-limit on the complete tensor product.**  The span of
all region embeddings, ranging over every sector `c` and every finite region
`Λ`, is dense in `globalDirectSum L`.  This exhibits the complete tensor product
as the closed span of the per-sector finite-region embeddings.

Note this is the *span* of the union (a single-sector vector cannot approximate
a genuinely multi-sector vector, so the bare union is not dense). -/
theorem dense_span_iUnion_regionEmbedDS_range :
    Dense (↑(Submodule.span ℂ
      (⋃ (c : SectorClass L) (Λ : Finset L),
        Set.range (⇑(regionEmbedDS L c Λ)))) : Set (globalDirectSum L)) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  have hcomp : ∀ c : SectorClass L, y.val c = 0 := by
    intro c
    refine (dense_iUnion_regionEmbed_range (Ω := c.out)).eq_zero_of_inner_right (𝕜 := ℂ) ?_
    intro w hw
    obtain ⟨Λ, ξ, rfl⟩ := Set.mem_iUnion.mp hw
    have hmem : sectorEmbedDS L c (regionEmbed c.out Λ ξ) ∈
        Submodule.span ℂ (⋃ (c' : SectorClass L) (Λ' : Finset L),
          Set.range (⇑(regionEmbedDS L c' Λ'))) :=
      Submodule.subset_span
        (Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨Λ, ⟨ξ, rfl⟩⟩⟩)
    have h0 := (Submodule.mem_orthogonal _ y).mp hy _ hmem
    rw [inner_sectorEmbedDS_left] at h0
    exact h0
  exact Subtype.ext (funext hcomp)

/-! ### Sector-representative independence

`Ω ≈ Ω'` (`SectorRel`) selects the same sector: `globalIdx L Ω` and
`globalIdx L Ω'` have the same underlying tuples, inducing a canonical linear
isometric equivalence of the sector Hilbert spaces that intertwines the local
algebra action.  This makes the `Quotient.out`-based `globalDirectSum`
representative-independent up to canonical unitary. -/

/-- For `Ω ≈ Ω'`, the index types `globalIdx L Ω` and `globalIdx L Ω'` coincide:
the value-identity bijection. -/
def globalIdxEquiv {Ω Ω' : (s : L) → localIdx (L := L) s}
    (h : SectorRel L Ω Ω') : globalIdx L Ω ≃ globalIdx L Ω' where
  toFun f := ⟨f.val, by
    obtain ⟨Λ, hΛ⟩ := f.property
    obtain ⟨Γ, hΓ⟩ := h
    exact ⟨Λ ∪ Γ, fun s hs =>
      (hΛ s (fun hh => hs (Finset.mem_union_left _ hh))).trans
        (hΓ s (fun hh => hs (Finset.mem_union_right _ hh)))⟩⟩
  invFun g := ⟨g.val, by
    obtain ⟨Λ, hΛ⟩ := g.property
    obtain ⟨Γ, hΓ⟩ := h
    exact ⟨Λ ∪ Γ, fun s hs =>
      (hΛ s (fun hh => hs (Finset.mem_union_left _ hh))).trans
        (hΓ s (fun hh => hs (Finset.mem_union_right _ hh))).symm⟩⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl

@[simp] theorem globalIdxEquiv_val {Ω Ω' : (s : L) → localIdx (L := L) s}
    (h : SectorRel L Ω Ω') (f : globalIdx L Ω) :
    (globalIdxEquiv L h f).val = f.val := rfl

@[simp] theorem globalIdxEquiv_symm_val {Ω Ω' : (s : L) → localIdx (L := L) s}
    (h : SectorRel L Ω Ω') (g : globalIdx L Ω') :
    ((globalIdxEquiv L h).symm g).val = g.val := rfl

/-- The linear isometric equivalence of sector Hilbert spaces induced by
`Ω ≈ Ω'`, reindexing `lp` coordinates along `globalIdxEquiv`. -/
noncomputable def globalHilbertEquiv {Ω Ω' : (s : L) → localIdx (L := L) s}
    (h : SectorRel L Ω Ω') : globalHilbert L Ω ≃ₗᵢ[ℂ] globalHilbert L Ω' :=
  LinearIsometryEquiv.lpCongrLeft ℂ
    (by rw [ENNReal.toReal_ofNat]; norm_num) (globalIdxEquiv L h)

@[simp] theorem globalHilbertEquiv_apply_coord
    {Ω Ω' : (s : L) → localIdx (L := L) s} (h : SectorRel L Ω Ω')
    (ψ : globalHilbert L Ω) (g' : globalIdx L Ω') :
    (globalHilbertEquiv L h ψ).val g' = ψ.val ((globalIdxEquiv L h).symm g') := rfl

/-! ### Local algebra intertwining and `CStarRep.UnitaryEquiv`

The induced sector isometry `globalHilbertEquiv` intertwines the local-algebra
action: `localEmbed Ω Λ M` and `localEmbed Ω' Λ M` are conjugate under it.  All
the ingredients (`globalSwap`, `regionRestrict`, `wRestrict`, `localEmbedCoeff`)
depend only on the underlying tuple values, on which `globalIdxEquiv` is the
identity, so the coordinate equation holds definitionally. -/

/-- `globalHilbertEquiv` conjugates the local embedding (applied form). -/
theorem globalHilbertEquiv_localEmbed_apply
    {Ω Ω' : (s : L) → localIdx (L := L) s} (h : SectorRel L Ω Ω')
    (Λ : Finset L) (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) (ψ : globalHilbert L Ω) :
    globalHilbertEquiv L h (localEmbed (Ω := Ω) Λ M ψ)
      = localEmbed (Ω := Ω') Λ M (globalHilbertEquiv L h ψ) := by
  apply Subtype.ext
  funext g'
  rfl

/-- **Local algebra intertwining**: `globalHilbertEquiv` intertwines
`localEmbed Ω Λ M` and `localEmbed Ω' Λ M`. -/
theorem globalHilbertEquiv_localEmbed
    {Ω Ω' : (s : L) → localIdx (L := L) s} (h : SectorRel L Ω Ω')
    (Λ : Finset L) (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    (↑(globalHilbertEquiv L h) : globalHilbert L Ω →L[ℂ] globalHilbert L Ω')
        ∘L localEmbed (Ω := Ω) Λ M
      = localEmbed (Ω := Ω') Λ M
        ∘L (↑(globalHilbertEquiv L h) : globalHilbert L Ω →L[ℂ] globalHilbert L Ω') := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
  exact globalHilbertEquiv_localEmbed_apply L h Λ M ψ

/-- The local-algebra representation on the `Ω`-sector Hilbert space. -/
noncomputable def localRepAt (Λ : Finset L)
    (Ω : (s : L) → localIdx (L := L) s) : CStarRep (ℋ(Λ) →L[ℂ] ℋ(Λ)) where
  H := globalHilbert L Ω
  π := (localEmbedHom (Ω := Ω) Λ).toNonUnitalStarAlgHom

/-- For `Ω ≈ Ω'`, the local-algebra representations on the two sector Hilbert
spaces are unitarily equivalent, witnessed by `globalHilbertEquiv`. -/
noncomputable def localRepUnitaryEquiv
    {Ω Ω' : (s : L) → localIdx (L := L) s} (h : SectorRel L Ω Ω')
    (Λ : Finset L) :
    CStarRep.UnitaryEquiv (localRepAt L Λ Ω) (localRepAt L Λ Ω') where
  unitary_map := asUnitary (globalHilbertEquiv L h)
  intertwines M := globalHilbertEquiv_localEmbed L h Λ M

/-- Every representative `Ω` of a sector class `c` gives a representation
unitarily equivalent to the `Quotient.out`-based `localSectorRep L Λ c`. -/
theorem localSectorRep_unitaryEquiv
    {Ω : (s : L) → localIdx (L := L) s} {c : SectorClass L}
    (hc : Quotient.mk (sectorSetoid L) Ω = c) (Λ : Finset L) :
    Nonempty (CStarRep.UnitaryEquiv (localRepAt L Λ Ω) (localSectorRep L Λ c)) := by
  have heq : Quotient.mk (sectorSetoid L) Ω
      = Quotient.mk (sectorSetoid L) (Quotient.out c) := by
    rw [hc, Quotient.out_eq]
  have h : SectorRel L Ω (Quotient.out c) := Quotient.exact heq
  exact ⟨localRepUnitaryEquiv L h Λ⟩

end LocalNetLike
