module

public import QuantumSystem.Algebra.Geometry.Cone
public import QuantumSystem.Algebra.QuasiLocalAlgebra.QuasiLocal

/-!
# `*`-subalgebras attached to a cone

For each cone `Λ : Cone L` (the pure region geometry, `Geometry/Cone.lean`) this
file forms the two C\*-subalgebras of `B(globalHilbert L Ω)` it determines — the
*algebra-coupled* half of the cone API, depending on the quasi-local algebra:

* `localConeSubalg L Ω Λ` — closure of `⨆ Λ' ⊆ Λ.region, 𝔄(Λ')`, matching `A(Λ)`;
* `complementConeSubalg L Ω Λ` — closure of `⨆ Λ' Disjoint Λ.region, 𝔄(Λ')`,
  matching `A(Λ^c)`.

The finite-region versions (`localSubalgebra Λ` for `Λ : Finset L`) embed as the
special case `Cone.ofFinset Λ`.

## Main results

* `LocalNetLike.complementConeSubalg_antimono` — antimonotonicity in the cone region.
* `LocalNetLike.localConeSubalg_mono` — monotonicity in the cone region.
* `LocalNetLike.localConeSubalg_le_complementConeSubalg` — local-in-a-cone ⊆
  outside-a-separated-cone (the geometric input behind commutation of separated
  sectors).

## References

* Ogata, Pérez-García, Ruiz-de-Alarcón, *Haag Duality for 2D Quantum Spin
  Systems*, arXiv:2509.23734v1, §1.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
-/

@[expose] public section

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
  (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)

/-- The local C\*-subalgebra of `B(globalHilbert L Ω)` supported in a cone `Λ`:
closure of the join of `𝔄(Λ')` over finite subregions `Λ' ⊆ Λ.region`. -/
noncomputable def localConeSubalg (Λ : Cone L) :
    StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :=
  (⨆ (Λ' : Finset L) (_ : (↑Λ' : Set L) ⊆ Λ.region),
    localSubalgebra (Ω := Ω) Λ').topologicalClosure

/-- The C\*-subalgebra of operators localised outside the cone `Λ`: closure of the
join of `𝔄(Λ')` over finite `Λ'` disjoint from `Λ.region`. -/
noncomputable def complementConeSubalg (Λ : Cone L) :
    StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω) :=
  (⨆ (Λ' : Finset L) (_ : Disjoint (↑Λ' : Set L) Λ.region),
    localSubalgebra (Ω := Ω) Λ').topologicalClosure

/-- Monotonicity of `localConeSubalg`: enlarging the cone region enlarges the
local cone algebra. -/
lemma localConeSubalg_mono {Λ Λ' : Cone L} (h : Λ.region ⊆ Λ'.region) :
    localConeSubalg L Ω Λ ≤ localConeSubalg L Ω Λ' := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  refine iSup_le fun Λ'' => iSup_le fun hsub => ?_
  exact le_iSup_of_le Λ'' (le_iSup_of_le (hsub.trans h) le_rfl)

/-- Antimonotonicity of `complementConeSubalg`: enlarging the cone region shrinks
the complement-cone algebra. -/
lemma complementConeSubalg_antimono {Λ Λ' : Cone L} (h : Λ.region ⊆ Λ'.region) :
    complementConeSubalg L Ω Λ' ≤ complementConeSubalg L Ω Λ := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  refine iSup_le fun Λ'' => iSup_le fun hd => ?_
  have hd' : Disjoint (↑Λ'' : Set L) Λ.region := hd.mono_right h
  exact le_iSup_of_le Λ'' (le_iSup_of_le hd' le_rfl)

/-- A cone-localised algebra is contained in the quasi-local algebra. -/
lemma localConeSubalg_le_quasiLocal (Λ : Cone L) :
    localConeSubalg L Ω Λ ≤ quasiLocal L Ω := by
  refine StarSubalgebra.topologicalClosure_mono ?_
  exact iSup_le fun Λ' => iSup_le fun _ => le_iSup _ Λ'

/-- Enlarging to a union cone shrinks the complement-cone algebra below the left
summand's complement-cone algebra. -/
lemma complementConeSubalg_union_le_left (Λ₁ Λ₂ : Cone L) :
    complementConeSubalg L Ω (Λ₁.union Λ₂) ≤ complementConeSubalg L Ω Λ₁ :=
  complementConeSubalg_antimono L Ω (Cone.subset_union_left Λ₁ Λ₂)

/-- Enlarging to a union cone shrinks the complement-cone algebra below the right
summand's complement-cone algebra. -/
lemma complementConeSubalg_union_le_right (Λ₁ Λ₂ : Cone L) :
    complementConeSubalg L Ω (Λ₁.union Λ₂) ≤ complementConeSubalg L Ω Λ₂ :=
  complementConeSubalg_antimono L Ω (Cone.subset_union_right Λ₁ Λ₂)

/-- **Local-in-a-cone ⊆ outside-a-separated-cone.**  If the cone `C` is disjoint
from the cone `Λ`, then every operator localised inside `C` is localised outside
`Λ`: `localConeSubalg C ≤ complementConeSubalg Λ`.

This is the geometric input behind commutation of separated sectors: each finite
generator `𝔄(Λ')` of `localConeSubalg C` has `Λ' ⊆ C.region` disjoint from
`Λ.region`, hence is a generator of `complementConeSubalg Λ`. -/
lemma localConeSubalg_le_complementConeSubalg {C Λ : Cone L}
    (h : Disjoint C.region Λ.region) :
    localConeSubalg L Ω C ≤ complementConeSubalg L Ω Λ := by
  refine StarSubalgebra.topologicalClosure_minimal ?_
    (StarSubalgebra.isClosed_topologicalClosure _)
  refine iSup_le fun Λ' => iSup_le fun hsub => ?_
  have hd : Disjoint (↑Λ' : Set L) Λ.region := Set.disjoint_of_subset_left hsub h
  refine le_trans ?_ (StarSubalgebra.le_topologicalClosure _)
  exact le_iSup_of_le Λ' (le_iSup_of_le hd le_rfl)

end LocalNetLike
