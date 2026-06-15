module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import QuantumSystem.Algebra.Sector.Net.Transport
public import QuantumSystem.Algebra.Sector.Net.Transportable
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Locality
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Isotony

/-!
# DHR transport existence (native re-derivation)

This file proves the **existence half of DHR transportability**, natively in the
`sectorCat`/`StarEndoCat` framework (no auxiliary representation or
`ConeLocalizedEndomorphism` structure): a localized sector `ρ` satisfying the DHR
selection criterion (`IsDHRTransportable`) is transportable (`IsTransportable`,
`isTransportable_of_isDHRTransportable`) — for every cone it is unitarily
equivalent, inside the quasi-local algebra, to a sector localized in that cone.

Given a sector `ρ` (a `*`-endomorphism of `↥(quasiLocal L Ω)`) and a unitary `U`
on `globalHilbert L Ω`, the **conjugated endomorphism**

```
conjEndo ρ U a := U (ρ a) U⋆ ∈ 𝓑(globalHilbert L Ω)
```

is the candidate transported action.  Its `*`-homomorphism properties are
inherited from the conjugation `*`-algebra equivalence
`LinearIsometryEquiv.conjStarAlgEquiv` of `𝓑(globalHilbert L Ω)`.  The central
result is **landing** (`conjEndo_landing`): when `U` intertwines `ρ` with the
vacuum (the inclusion) on the spacelike complement of a cone `Λ`, every
`conjEndo ρ U a` lies in `quasiLocal L Ω`, by a Haag-duality centralizer
argument.

Working directly with `ρ.endo` (a `*`-endomorphism `quasiLocal → quasiLocal`) and
the conjugation equivalence of `𝓑(globalHilbert)` keeps every operation either at
the abstract `𝓑(H)` level or at `quasiLocal → quasiLocal`, avoiding the expensive
`CoeFun`/typeclass synthesis of a `↥(quasiLocal) →⋆ₙₐ 𝓑(…)` homomorphism (which
times out at the concrete coefficient algebra; cf. the project synthesis notes).

The transport theorem assembles `conjEndo` into the sector `transportSector`
localized in `Λ`, together with the charge transporter `U` (which lands in
`quasiLocal` via `intertwiningOp_mem_quasiLocal`, `Net/Transport.lean`), giving the
unitary intertwiner `ρ ⟶ σ`.  Continuity of `conjEndo` (needed for the landing of
every element by density) is obtained from contractivity of `ρ.endo`
(`NonUnitalStarAlgHom.norm_apply_le`) rather than the `ContinuousMapClass`
synthesis, which is unstable at `↥(quasiLocal)`.

## References

* Doplicher, Haag, Roberts, *Local observables and particle statistics I*,
  Comm. Math. Phys. 23 (1971), §3.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*, §5.3.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.2.
-/

@[expose] public section

open scoped LocalNetLike CStarAlgebra

namespace LocalNetLike

open CategoryTheory

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-! ### The conjugated endomorphism `U (ρ a) U⋆` -/

/-- The **conjugated endomorphism** `conjEndo ρ U a := U (ρ a) U⋆`, realised
through the conjugation `*`-algebra equivalence of `𝓑(globalHilbert L Ω)`. -/
noncomputable def conjEndo (ρ : sectorCat L Ω)
    (U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω))
    (a : ↥(quasiLocal L Ω)) : globalHilbert L Ω →L[ℂ] globalHilbert L Ω :=
  U.toLinearIsometryEquiv.conjStarAlgEquiv ((ρ.endo a).val)

variable {ρ : sectorCat L Ω}
  {U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω)}

/-- The explicit operator form `conjEndo ρ U a = U (ρ a) U⋆`. -/
lemma conjEndo_apply (a : ↥(quasiLocal L Ω)) :
    conjEndo ρ U a
      = U.toContinuousLinearMap ∘L (ρ.endo a).val ∘L U.toContinuousLinearMap.adjoint := by
  apply ContinuousLinearMap.ext
  intro y
  rw [conjEndo]
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  rfl

lemma conjEndo_zero : conjEndo ρ U 0 = 0 := by
  rw [conjEndo, map_zero, ZeroMemClass.coe_zero, map_zero]

lemma conjEndo_add (a b : ↥(quasiLocal L Ω)) :
    conjEndo ρ U (a + b) = conjEndo ρ U a + conjEndo ρ U b := by
  rw [conjEndo, conjEndo, conjEndo, map_add, AddMemClass.coe_add, map_add]

lemma conjEndo_smul (c : ℂ) (a : ↥(quasiLocal L Ω)) :
    conjEndo ρ U (c • a) = c • conjEndo ρ U a := by
  rw [conjEndo, conjEndo, map_smul, SetLike.val_smul, map_smul]

lemma conjEndo_mul (a b : ↥(quasiLocal L Ω)) :
    conjEndo ρ U a * conjEndo ρ U b = conjEndo ρ U (a * b) := by
  rw [conjEndo, conjEndo, conjEndo, ← map_mul, map_mul ρ.endo, MulMemClass.coe_mul]

lemma conjEndo_star (a : ↥(quasiLocal L Ω)) :
    star (conjEndo ρ U a) = conjEndo ρ U (star a) := by
  rw [conjEndo, conjEndo, ← map_star, map_star ρ.endo, StarMemClass.coe_star]

/-- `conjEndo` fixes the unit: `U (ρ 1) U⋆ = U U⋆ = 1`. -/
lemma conjEndo_one : conjEndo ρ U 1 = 1 := by
  rw [conjEndo, map_one, OneMemClass.coe_one, map_one]

/-- If `U` intertwines `ρ` with an operator `T` at `a`, then `conjEndo ρ U a = T`. -/
lemma conjEndo_eq_of_intertwined {a : ↥(quasiLocal L Ω)}
    {T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω}
    (h : U.toContinuousLinearMap ∘L (ρ.endo a).val = T ∘L U.toContinuousLinearMap) :
    conjEndo ρ U a = T := by
  rw [conjEndo_apply]
  apply ContinuousLinearMap.ext
  intro y
  have hy := congrArg
    (fun f : globalHilbert L Ω →L[ℂ] globalHilbert L Ω => f (U.toContinuousLinearMap.adjoint y)) h
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hy ⊢
  rw [hy]
  congr 1
  have hUU := congrArg
    (fun f : globalHilbert L Ω →L[ℂ] globalHilbert L Ω => f y) U.comp_adjoint
  simpa using hUU

lemma conjEndo_sub (a b : ↥(quasiLocal L Ω)) :
    conjEndo ρ U (a - b) = conjEndo ρ U a - conjEndo ρ U b := by
  rw [conjEndo, conjEndo, conjEndo, map_sub, AddSubgroupClass.coe_sub, map_sub]

/-- `conjEndo ρ U` is **contractive**: `‖U (ρ a) U⋆‖ ≤ ‖a‖`.  The conjugation
equivalence and the inclusion are isometric, and `ρ.endo` is contractive
(`NonUnitalStarAlgHom.norm_apply_le`). -/
lemma conjEndo_norm_le (a : ↥(quasiLocal L Ω)) : ‖conjEndo ρ U a‖ ≤ ‖a‖ := by
  rw [conjEndo]
  calc ‖U.toLinearIsometryEquiv.conjStarAlgEquiv ((ρ.endo a).val)‖
      ≤ ‖(ρ.endo a).val‖ :=
        NonUnitalStarAlgHom.norm_apply_le U.toLinearIsometryEquiv.conjStarAlgEquiv _
    _ = ‖ρ.endo a‖ := (AddSubgroupClass.coe_norm (quasiLocal L Ω) (ρ.endo a)).symm
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le ρ.endo.toNonUnitalStarAlgHom a

/-- `conjEndo ρ U` is continuous (it is `1`-Lipschitz by `conjEndo_norm_le`). -/
lemma conjEndo_continuous : Continuous (conjEndo ρ U) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun a b => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← conjEndo_sub]
  exact conjEndo_norm_le _

/-! ### Carrier of the algebraic local core -/

/-- The carrier of the algebraic core `quasiLocalSubalg L Ω` is the union of the
local subalgebra carriers (the family is directed under isotony). -/
lemma quasiLocalSubalg_carrier_eq_iUnion :
    (SetLike.coe (quasiLocalSubalg L Ω) :
        Set (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) =
      ⋃ Λ : Finset L,
        (SetLike.coe (localSubalgebra (Ω := Ω) Λ) :
          Set (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) := by
  let M : StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) := {
    carrier := ⋃ Λ : Finset L,
      (SetLike.coe (localSubalgebra (Ω := Ω) Λ) :
        Set (globalHilbert L Ω →L[ℂ] globalHilbert L Ω))
    add_mem' := by
      rintro a b ha hb
      rw [Set.mem_iUnion] at ha hb ⊢
      obtain ⟨Λa, ha⟩ := ha
      obtain ⟨Λb, hb⟩ := hb
      exact ⟨Λa ∪ Λb, add_mem
        (localSubalgebra_le_of_subset Finset.subset_union_left ha)
        (localSubalgebra_le_of_subset Finset.subset_union_right hb)⟩
    mul_mem' := by
      rintro a b ha hb
      rw [Set.mem_iUnion] at ha hb ⊢
      obtain ⟨Λa, ha⟩ := ha
      obtain ⟨Λb, hb⟩ := hb
      exact ⟨Λa ∪ Λb, mul_mem
        (localSubalgebra_le_of_subset Finset.subset_union_left ha)
        (localSubalgebra_le_of_subset Finset.subset_union_right hb)⟩
    algebraMap_mem' := by
      intro c
      rw [Set.mem_iUnion]
      exact ⟨∅, StarSubalgebra.algebraMap_mem (localSubalgebra (Ω := Ω) ∅) c⟩
    star_mem' := by
      rintro a ha
      rw [Set.mem_iUnion] at ha ⊢
      obtain ⟨Λ, ha⟩ := ha
      exact ⟨Λ, star_mem ha⟩
  }
  suffices h_eq : quasiLocalSubalg L Ω = M by rw [h_eq]; rfl
  apply le_antisymm
  · refine iSup_le fun Λ => ?_
    intro x hx
    exact Set.mem_iUnion.mpr ⟨Λ, hx⟩
  · intro x hx
    obtain ⟨Λ, hx⟩ := Set.mem_iUnion.mp hx
    exact (le_iSup (fun Λ : Finset L =>
      (localSubalgebra (Ω := Ω) Λ :
        StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω))) Λ) hx

/-! ### The DHR intertwining datum -/

/-- `ρ` is **intertwined with the vacuum on the complement of `Λ`** by the unitary
`U`: `U (ρ a) = a U` for every `a` localised in the spacelike complement of `Λ`.
This is the transport datum supplied by the DHR selection criterion. -/
def IntertwinedOn (ρ : sectorCat L Ω) (Λ : Cone L)
    (U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω)) : Prop :=
  ∀ a : ↥(quasiLocal L Ω), a.val ∈ complementConeSubalg L Ω Λ →
    U.toContinuousLinearMap ∘L (ρ.endo a).val = a.val ∘L U.toContinuousLinearMap

/-! ### Landing of `conjEndo` in the quasi-local algebra -/

/-- Locality: `a, t` localised in disjoint finite regions commute. -/
lemma quasiLocal_commute_of_disjoint {Λa Λt : Finset L} (hd : Disjoint Λa Λt)
    {a t : ↥(quasiLocal L Ω)}
    (ha : a.val ∈ localSubalgebra (Ω := Ω) Λa)
    (ht : t.val ∈ localSubalgebra (Ω := Ω) Λt) :
    a * t = t * a := by
  apply Subtype.ext
  exact (localSubalgebra_commute_of_disjoint hd ha ht).eq

/-- `conjEndo ρ U a` commutes with a local operator localised away from `a` and
the intertwining region `Λ`. -/
lemma conjEndo_commute_local {Λ : Cone L}
    (hU : IntertwinedOn ρ Λ U)
    {Λa Λt : Finset L} {a : ↥(quasiLocal L Ω)}
    (ha : a.val ∈ localSubalgebra (Ω := Ω) Λa)
    (hd_at : Disjoint Λa Λt) (hd_t : Disjoint (↑Λt : Set L) Λ.region)
    {T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω}
    (hT : T ∈ localSubalgebra (Ω := Ω) Λt) :
    conjEndo ρ U a * T = T * conjEndo ρ U a := by
  have hT_qL : T ∈ quasiLocal L Ω := localSubalgebra_le_quasiLocal L Ω Λt hT
  let t : ↥(quasiLocal L Ω) := ⟨T, hT_qL⟩
  have h_t_in_comp : t.val ∈ complementConeSubalg L Ω Λ :=
    localSubalgebra_mem_complementConeSubalg hd_t hT
  have h_conj_t : conjEndo ρ U t = T := conjEndo_eq_of_intertwined (hU t h_t_in_comp)
  have h_commute : a * t = t * a := quasiLocal_commute_of_disjoint hd_at ha hT
  calc conjEndo ρ U a * T
      = conjEndo ρ U a * conjEndo ρ U t := by rw [h_conj_t]
    _ = conjEndo ρ U (a * t) := conjEndo_mul a t
    _ = conjEndo ρ U (t * a) := by rw [h_commute]
    _ = conjEndo ρ U t * conjEndo ρ U a := (conjEndo_mul t a).symm
    _ = T * conjEndo ρ U a := by rw [h_conj_t]

/-- Landing for a finite-region `a`: `conjEndo ρ U a ∈ quasiLocal L Ω`. -/
lemma conjEndo_landing_localSubalgebra {Λ : Cone L}
    (hU : IntertwinedOn ρ Λ U) (hHaag : HaagDuality L Ω)
    {Λa : Finset L} {a : ↥(quasiLocal L Ω)}
    (ha : a.val ∈ localSubalgebra (Ω := Ω) Λa) :
    conjEndo ρ U a ∈ quasiLocal L Ω := by
  let Λ' : Cone L := { region := (↑Λa : Set L) ∪ Λ.region }
  have h_local_le_centralizer :
      ∀ (Λt : Finset L), Disjoint (↑Λt : Set L) Λ'.region →
        localSubalgebra (Ω := Ω) Λt ≤ StarSubalgebra.centralizer ℂ {conjEndo ρ U a} := by
    intro Λt hd
    have hd_at_set : Disjoint (↑Λt : Set L) (↑Λa : Set L) :=
      hd.mono_right Set.subset_union_left
    have hd_at : Disjoint Λa Λt := (Finset.disjoint_coe.mp hd_at_set).symm
    have hd_t : Disjoint (↑Λt : Set L) Λ.region := hd.mono_right Set.subset_union_right
    intro T hT
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    have hg_eq : g = conjEndo ρ U a := Set.mem_singleton_iff.mp hg
    subst hg_eq
    refine ⟨?_, ?_⟩
    · exact conjEndo_commute_local hU ha hd_at hd_t hT
    · have h_star_a : (star a).val ∈ localSubalgebra (Ω := Ω) Λa := by
        change star a.val ∈ localSubalgebra (Ω := Ω) Λa
        exact star_mem ha
      have h := conjEndo_commute_local hU h_star_a hd_at hd_t hT
      rw [← conjEndo_star] at h
      exact h
  have h_closure_le : complementConeSubalg L Ω Λ' ≤
      StarSubalgebra.centralizer ℂ {conjEndo ρ U a} :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun Λt => iSup_le fun hd => h_local_le_centralizer Λt hd)
      (Set.isClosed_centralizer _)
  have h_central :
      conjEndo ρ U a ∈ Set.centralizer ((complementConeSubalg L Ω Λ' :
        StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) : Set _) := by
    intro m hm
    have hm_in : m ∈ StarSubalgebra.centralizer ℂ {conjEndo ρ U a} := h_closure_le hm
    rw [StarSubalgebra.mem_centralizer_iff] at hm_in
    obtain ⟨h1, _⟩ := hm_in (conjEndo ρ U a) (Set.mem_singleton _)
    exact h1.symm
  rw [hHaag Λ'] at h_central
  exact localConeSubalg_le_quasiLocal L Ω Λ' h_central

/-- **Landing.**  For every `a`, the conjugated operator `conjEndo ρ U a` lies in
the quasi-local algebra (combine the finite-region landing with density of the
algebraic core and the continuity of `conjEndo ρ U`). -/
lemma conjEndo_landing {Λ : Cone L}
    (hU : IntertwinedOn ρ Λ U) (hHaag : HaagDuality L Ω) :
    ∀ a : ↥(quasiLocal L Ω), conjEndo ρ U a ∈ quasiLocal L Ω := by
  intro a
  set landingSet : Set ↥(quasiLocal L Ω) := {a | conjEndo ρ U a ∈ quasiLocal L Ω} with hLS
  have h_closed : IsClosed landingSet :=
    IsClosed.preimage conjEndo_continuous (isClosed_quasiLocal L Ω)
  have h_finite_in : ∀ (b : ↥(quasiLocal L Ω)) (Λb : Finset L),
      b.val ∈ localSubalgebra (Ω := Ω) Λb → b ∈ landingSet :=
    fun b Λb hb => conjEndo_landing_localSubalgebra hU hHaag hb
  have ha_in_closure : a.val ∈ closure ((quasiLocalSubalg L Ω :
      StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) : Set _) := by
    change a.val ∈ ((quasiLocalSubalg L Ω).topologicalClosure :
      StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω))
    exact a.2
  rw [mem_closure_iff_seq_limit] at ha_in_closure
  obtain ⟨xs, hxs_in, hxs_tendsto⟩ := ha_in_closure
  have hxs_mem : ∀ n, ∃ Λn : Finset L, xs n ∈ localSubalgebra (Ω := Ω) Λn := by
    intro n
    have h1 : xs n ∈ ((quasiLocalSubalg L Ω : StarSubalgebra ℂ _) : Set _) := hxs_in n
    rw [quasiLocalSubalg_carrier_eq_iUnion, Set.mem_iUnion] at h1
    exact h1
  set ys : ℕ → ↥(quasiLocal L Ω) := fun n =>
    ⟨xs n, quasiLocalSubalg_le_quasiLocal L Ω (hxs_in n)⟩ with hys
  have hys_in_landing : ∀ n, ys n ∈ landingSet := by
    intro n
    obtain ⟨Λn, hΛn⟩ := hxs_mem n
    exact h_finite_in (ys n) Λn hΛn
  have hys_tendsto : Filter.Tendsto ys Filter.atTop (nhds a) := by
    rw [Metric.tendsto_atTop]
    rw [Metric.tendsto_atTop] at hxs_tendsto
    intro ε hε
    obtain ⟨N, hN⟩ := hxs_tendsto ε hε
    exact ⟨N, fun n hn => hN n hn⟩
  have ha_in_closure_landingSet : a ∈ closure landingSet :=
    mem_closure_of_tendsto hys_tendsto (Filter.Eventually.of_forall hys_in_landing)
  rw [IsClosed.closure_eq h_closed] at ha_in_closure_landingSet
  exact ha_in_closure_landingSet

/-! ### The transported sector -/

/-- The **transported endomorphism**: the unital `*`-endomorphism of
`↥(quasiLocal L Ω)` with underlying action `a ↦ U (ρ a) U⋆`, which lands in the
quasi-local algebra by `conjEndo_landing`.  Its `*`-homomorphism properties are
inherited from `conjEndo`. -/
noncomputable def transportEndo (ρ : sectorCat L Ω) {Λ : Cone L}
    (U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω))
    (hU : IntertwinedOn ρ Λ U) (hHaag : HaagDuality L Ω) :
    ↥(quasiLocal L Ω) →⋆ₐ[ℂ] ↥(quasiLocal L Ω) where
  toFun a := ⟨conjEndo ρ U a, conjEndo_landing hU hHaag a⟩
  map_one' := by
    apply Subtype.ext
    change conjEndo ρ U 1 = (1 : ↥(quasiLocal L Ω)).val
    rw [conjEndo_one, OneMemClass.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    change conjEndo ρ U (a * b) = (⟨conjEndo ρ U a, _⟩ * ⟨conjEndo ρ U b, _⟩ :
      ↥(quasiLocal L Ω)).val
    rw [MulMemClass.coe_mul, conjEndo_mul]
  map_zero' := by
    apply Subtype.ext
    change conjEndo ρ U 0 = (0 : ↥(quasiLocal L Ω)).val
    rw [conjEndo_zero, ZeroMemClass.coe_zero]
  map_add' a b := by
    apply Subtype.ext
    change conjEndo ρ U (a + b) = (⟨conjEndo ρ U a, _⟩ + ⟨conjEndo ρ U b, _⟩ :
      ↥(quasiLocal L Ω)).val
    rw [AddMemClass.coe_add, conjEndo_add]
  commutes' r := by
    apply Subtype.ext
    change conjEndo ρ U (algebraMap ℂ ↥(quasiLocal L Ω) r)
      = (algebraMap ℂ ↥(quasiLocal L Ω) r).val
    rw [Algebra.algebraMap_eq_smul_one, conjEndo_smul, conjEndo_one, SetLike.val_smul,
      OneMemClass.coe_one]
  map_star' a := by
    apply Subtype.ext
    change conjEndo ρ U (star a) = (star ⟨conjEndo ρ U a, _⟩ : ↥(quasiLocal L Ω)).val
    rw [StarMemClass.coe_star, conjEndo_star]

@[simp] lemma transportEndo_apply_val (ρ : sectorCat L Ω) {Λ : Cone L}
    (U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω))
    (hU : IntertwinedOn ρ Λ U) (hHaag : HaagDuality L Ω) (a : ↥(quasiLocal L Ω)) :
    (transportEndo ρ U hU hHaag a).val = conjEndo ρ U a := rfl

/-- The **transported sector**: the `sectorCat` object whose action is `a ↦ U(ρ a)U⋆`. -/
noncomputable def transportSector (ρ : sectorCat L Ω) {Λ : Cone L}
    (U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω))
    (hU : IntertwinedOn ρ Λ U) (hHaag : HaagDuality L Ω) : sectorCat L Ω :=
  ⟨transportEndo ρ U hU hHaag⟩

@[simp] lemma transportSector_endo_apply_val (ρ : sectorCat L Ω) {Λ : Cone L}
    (U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω))
    (hU : IntertwinedOn ρ Λ U) (hHaag : HaagDuality L Ω) (a : ↥(quasiLocal L Ω)) :
    ((transportSector ρ U hU hHaag).endo a).val = conjEndo ρ U a := rfl

/-- The transported sector is **localized in `Λ`**: on the spacelike complement of
`Λ`, `conjEndo` fixes the operator (`conjEndo_eq_of_intertwined` from the datum). -/
lemma transportSector_isLocalizedIn (ρ : sectorCat L Ω) {Λ : Cone L}
    (U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω))
    (hU : IntertwinedOn ρ Λ U) (hHaag : HaagDuality L Ω) :
    IsLocalizedIn Λ (transportSector ρ U hU hHaag) := by
  intro a ha
  apply Subtype.ext
  rw [transportSector_endo_apply_val]
  exact conjEndo_eq_of_intertwined (hU a ha)

/-! ### The DHR selection criterion and transport existence -/

variable [SpacelikeGeometry L]

/-- A sector `ρ` is **DHR-transportable**: for every **proper** cone `Λ` there is a
transport datum — a unitary `U` on `globalHilbert L Ω` intertwining `ρ` with the
vacuum on the spacelike complement of `Λ`.  This is the DHR selection criterion in
the endomorphism picture (restricted to proper cones, as the empty cone forces the
identity). -/
def IsDHRTransportable (ρ : sectorCat L Ω) : Prop :=
  ∀ Λ : Cone L, SpacelikeGeometry.IsProper Λ →
    ∃ U : UnitaryMap (globalHilbert L Ω) (globalHilbert L Ω), IntertwinedOn ρ Λ U

/-- **DHR transport existence.**  Under strong Haag duality, a localized sector
satisfying the DHR selection criterion (`IsDHRTransportable`) is transportable: it
is unitarily equivalent, inside the quasi-local algebra, to a sector localized in
any prescribed cone.

For the target cone `Λ`, the transport datum `U` yields the localized sector
`transportSector` (via `conjEndo`); `U` itself, intertwining `ρ` and the
transported sector, lands in `quasiLocal L Ω` by `intertwiningOp_mem_quasiLocal`,
giving the unitary charge transporter `ρ ⟶ σ`. -/
theorem isTransportable_of_isDHRTransportable (hHaag : HaagDuality L Ω)
    {ρ : sectorCat L Ω} (hρ : IsLocalized L Ω ρ) (hdhr : IsDHRTransportable ρ) :
    IsTransportable ρ := by
  intro Λ hΛ
  obtain ⟨U, hU⟩ := hdhr Λ hΛ
  refine ⟨transportSector ρ U hU hHaag, transportSector_isLocalizedIn ρ U hU hHaag, ?_⟩
  have hσloc : IsLocalized L Ω (transportSector ρ U hU hHaag) :=
    isLocalized_of_isLocalizedIn (transportSector_isLocalizedIn ρ U hU hHaag)
  -- `U` intertwines `ρ` and the transported sector.
  have hWintw : ∀ a : ↥(quasiLocal L Ω),
      U.toContinuousLinearMap * (ρ.endo a).val
        = ((transportSector ρ U hU hHaag).endo a).val * U.toContinuousLinearMap := by
    intro a
    rw [transportSector_endo_apply_val, conjEndo_apply]
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    have hUy : U.toContinuousLinearMap.adjoint (U.toContinuousLinearMap y) = y := by
      have := congrArg (fun f : globalHilbert L Ω →L[ℂ] globalHilbert L Ω => f y) U.adjoint_comp
      simpa using this
    rw [hUy]
  -- Package the charge transporter and verify unitarity.
  refine ⟨intertwinerOfOp hHaag hρ hσloc U.toContinuousLinearMap hWintw, ?_⟩
  change (intertwinerOfOp hHaag hρ hσloc U.toContinuousLinearMap hWintw).t
    ∈ unitary ↥(quasiLocal L Ω)
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [MulMemClass.coe_mul, StarMemClass.coe_star, intertwinerOfOp_t, OneMemClass.coe_one,
      ContinuousLinearMap.star_eq_adjoint]
    exact U.adjoint_comp
  · apply Subtype.ext
    rw [MulMemClass.coe_mul, StarMemClass.coe_star, intertwinerOfOp_t, OneMemClass.coe_one,
      ContinuousLinearMap.star_eq_adjoint]
    exact U.comp_adjoint

end LocalNetLike
