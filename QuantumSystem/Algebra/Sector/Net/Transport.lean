module

public import QuantumSystem.Algebra.Sector.Net.HaagDuality
public import QuantumSystem.Algebra.Sector.Net.Localized

/-!
# Intertwiner landing under Haag duality

The Haag-duality **centralizer core** of the DHR structure theory, re-derived
natively in the `StarEndoCat` framework: an operator `W` on the global Hilbert
space that intertwines two *localized* endomorphisms `ρ`, `σ`
(`W · ρ(a) = σ(a) · W` for every `a`) automatically lies in the quasi-local
algebra.

Indeed, for any `b` localised in the spacelike complement of both localisation
cones, `ρ(b) = b = σ(b)`, so the intertwining relation forces `W` to commute
with `b`.  Hence `W` centralises the complement-cone algebra
`𝔄((Λρ ∪ Λσ)ᶜ)`, which strong Haag duality identifies with the cone algebra
`𝔄(Λρ ∪ Λσ) ⊆ quasiLocal L Ω`.

This is the geometric heart that makes unitary charge transporters and
intertwiners *land* inside the observable algebra; it is the foundation on which
transportability and the existence of conjugates are built.

Müger §1.2 / Naaijkens (2012) §1.3–1.4; Doplicher–Haag–Roberts (1971).
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- A finite-region operator localised in `Λt`, with `↑Λt` disjoint from the
cone `Λ_R`, lies in the spacelike-complement algebra `complementConeSubalg Λ_R`. -/
lemma localSubalgebra_mem_complementConeSubalg
    {Λ_R : Cone L} {Λt : Finset L}
    (hd : Disjoint (↑Λt : Set L) Λ_R.region)
    {T : globalHilbert L Ω →L[ℂ] globalHilbert L Ω}
    (hT : T ∈ localSubalgebra (Ω := Ω) Λt) :
    T ∈ complementConeSubalg L Ω Λ_R := by
  refine StarSubalgebra.le_topologicalClosure _ ?_
  have step1 : localSubalgebra (Ω := Ω) Λt ≤
      ⨆ (_ : Disjoint (↑Λt : Set L) Λ_R.region),
        localSubalgebra (Ω := Ω) Λt :=
    le_iSup (fun _ : Disjoint (↑Λt : Set L) Λ_R.region =>
      localSubalgebra (Ω := Ω) Λt) hd
  have step2 :
      (⨆ (_ : Disjoint (↑Λt : Set L) Λ_R.region),
          localSubalgebra (Ω := Ω) Λt) ≤
        ⨆ Λ' : Finset L, ⨆ (_ : Disjoint (↑Λ' : Set L) Λ_R.region),
          localSubalgebra (Ω := Ω) Λ' :=
    le_iSup (fun Λ' : Finset L =>
      ⨆ (_ : Disjoint (↑Λ' : Set L) Λ_R.region),
        localSubalgebra (Ω := Ω) Λ') Λt
  exact step2 (step1 hT)

/-- **Intertwiner landing (Haag-duality centralizer core).**  An operator `W`
intertwining two localized endomorphisms `ρ`, `σ` lies in the quasi-local
algebra, under strong Haag duality. -/
lemma intertwiningOp_mem_quasiLocal
    (hHaag : HaagDuality L Ω)
    {ρ σ : sectorCat L Ω}
    (hρ : IsLocalized L Ω ρ) (hσ : IsLocalized L Ω σ)
    {W : globalHilbert L Ω →L[ℂ] globalHilbert L Ω}
    (hWintw : ∀ a : ↥(quasiLocal L Ω), W * (ρ.endo a).val = (σ.endo a).val * W) :
    W ∈ quasiLocal L Ω := by
  obtain ⟨Λρ, hρloc⟩ := hρ
  obtain ⟨Λσ, hσloc⟩ := hσ
  -- `W` commutes with operators localised outside both cones.
  have hWcomm : ∀ (b : ↥(quasiLocal L Ω)),
      b.val ∈ complementConeSubalg L Ω Λρ →
      b.val ∈ complementConeSubalg L Ω Λσ →
      W * b.val = b.val * W := by
    intro b hbρ hbσ
    have hρb : ρ.endo b = b := hρloc b hbρ
    have hσb : σ.endo b = b := hσloc b hbσ
    have h := hWintw b
    rw [hρb, hσb] at h
    exact h
  -- The union cone.
  set Λ' : Cone L := Λρ.union Λσ with hΛ'
  -- Each finite local subalgebra disjoint from the union sits in the
  -- centralizer of `{W}`.
  have h_local_le_centralizer :
      ∀ (Λt : Finset L), Disjoint (↑Λt : Set L) Λ'.region →
        localSubalgebra (Ω := Ω) Λt ≤ StarSubalgebra.centralizer ℂ {W} := by
    intro Λt hd
    have hd_ρ : Disjoint (↑Λt : Set L) Λρ.region :=
      hd.mono_right (Cone.subset_union_left Λρ Λσ)
    have hd_σ : Disjoint (↑Λt : Set L) Λσ.region :=
      hd.mono_right (Cone.subset_union_right Λρ Λσ)
    intro T hT
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hT_qL : T ∈ quasiLocal L Ω := localSubalgebra_le_quasiLocal L Ω Λt hT
    have hb_ρ : (⟨T, hT_qL⟩ : ↥(quasiLocal L Ω)).val ∈
        complementConeSubalg L Ω Λρ :=
      localSubalgebra_mem_complementConeSubalg hd_ρ hT
    have hb_σ : (⟨T, hT_qL⟩ : ↥(quasiLocal L Ω)).val ∈
        complementConeSubalg L Ω Λσ :=
      localSubalgebra_mem_complementConeSubalg hd_σ hT
    have hsb_ρ : (star (⟨T, hT_qL⟩ : ↥(quasiLocal L Ω))).val ∈
        complementConeSubalg L Ω Λρ :=
      localSubalgebra_mem_complementConeSubalg hd_ρ (star_mem hT)
    have hsb_σ : (star (⟨T, hT_qL⟩ : ↥(quasiLocal L Ω))).val ∈
        complementConeSubalg L Ω Λσ :=
      localSubalgebra_mem_complementConeSubalg hd_σ (star_mem hT)
    refine ⟨?_, ?_⟩
    · exact hWcomm ⟨T, hT_qL⟩ hb_ρ hb_σ
    · have hstar := hWcomm (star ⟨T, hT_qL⟩) hsb_ρ hsb_σ
      have hval : (star (⟨T, hT_qL⟩ : ↥(quasiLocal L Ω))).val = star T := rfl
      rw [hval] at hstar
      have h2 := congrArg star hstar
      rw [star_mul, star_mul, star_star, ContinuousLinearMap.star_eq_adjoint]
        at h2
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact h2.symm
  -- Extend to the complement-cone algebra via the closed centralizer.
  have h_closure_le : complementConeSubalg L Ω Λ' ≤
      StarSubalgebra.centralizer ℂ {W} :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun Λt => iSup_le fun hd => h_local_le_centralizer Λt hd)
      (Set.isClosed_centralizer _)
  -- `W` centralises the complement-cone algebra as a set.
  have h_central :
      W ∈ Set.centralizer ((complementConeSubalg L Ω Λ' :
        StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) : Set _) := by
    intro m hm
    have hm_in : m ∈ StarSubalgebra.centralizer ℂ {W} := h_closure_le hm
    rw [StarSubalgebra.mem_centralizer_iff] at hm_in
    obtain ⟨h1, _⟩ := hm_in W (Set.mem_singleton _)
    exact h1.symm
  -- Strong Haag duality lands `W` in the quasi-local algebra.
  rw [hHaag Λ'] at h_central
  exact localConeSubalg_le_quasiLocal L Ω Λ' h_central

/-- **Intertwiner landing, packaged.**  An operator `W` on the global Hilbert
space intertwining two localized endomorphisms `ρ`, `σ` defines an honest
morphism `ρ ⟶ σ` in the sector category, with underlying element the
quasi-local operator `W` (it lands there by `intertwiningOp_mem_quasiLocal`). -/
noncomputable def intertwinerOfOp
    (hHaag : HaagDuality L Ω)
    {ρ σ : sectorCat L Ω}
    (hρ : IsLocalized L Ω ρ) (hσ : IsLocalized L Ω σ)
    (W : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
    (hWintw : ∀ a : ↥(quasiLocal L Ω), W * (ρ.endo a).val = (σ.endo a).val * W) :
    ρ ⟶ σ where
  t := ⟨W, intertwiningOp_mem_quasiLocal hHaag hρ hσ hWintw⟩
  intertwines a := by
    apply Subtype.ext
    change W * (ρ.endo a).val = (σ.endo a).val * W
    exact hWintw a

@[simp] lemma intertwinerOfOp_t
    (hHaag : HaagDuality L Ω)
    {ρ σ : sectorCat L Ω}
    (hρ : IsLocalized L Ω ρ) (hσ : IsLocalized L Ω σ)
    (W : globalHilbert L Ω →L[ℂ] globalHilbert L Ω)
    (hWintw : ∀ a : ↥(quasiLocal L Ω), W * (ρ.endo a).val = (σ.endo a).val * W) :
    (intertwinerOfOp hHaag hρ hσ W hWintw).t.val = W := rfl

end LocalNetLike
