module

public import QuantumSystem.Algebra.Sector.Net.BraidedCategory
public import QuantumSystem.Algebra.Sector.Net.Symmetry

/-!
# The DHR sector category is symmetric (`d ≥ 3`)

In spacetime dimension `d ≥ 3` the DHR braiding is a **symmetry**: the monodromy
`β X Y ≫ β Y X` is the identity.  Categorically this upgrades the
`BraidedCategory` of `Sector/Net/BraidedCategory.lean` to a
`CategoryTheory.SymmetricCategory` on the DHR sector category.

The geometric input is the predicate `SymmetricStatistics` (the connectedness of
the spacelike complement, false in `d = 2`); the algebraic keystone
`Transport.symmetry` collapses the monodromy by unitarity once the
opposite-transport relation is supplied.  Because the braiding `dhrBraiding X Y` is
built by transporting `Y` *clear of* `X` (and `dhrBraiding Y X` by transporting `X`
clear of `Y`), the chosen transports `dhrTransport X Y` / `dhrTransport Y X` carry
exactly the spacelike-target data that `SymmetricStatistics` consumes.

Like the braided structure, this is a structure *parametrized* by the
Haag-duality, net-additivity and symmetric-statistics data, not a global instance.

## References

* Doplicher, Haag, Roberts, *Local observables and particle statistics II*,
  Comm. Math. Phys. 35 (1974).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §6.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L] [SpacelikeGeometry L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- **The DHR braiding is symmetric.**  The monodromy `β X Y ≫ β Y X` is trivial.
The chosen transport of `Y` clear of `X` (`dhrTransport X Y`) and of `X` clear of
`Y` (`dhrTransport Y X`) provide the opposite-transport data; `SymmetricStatistics`
supplies the relation and `Transport.symmetry` closes the monodromy. -/
lemma dhrSymmetry (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (hsym : SymmetricStatistics Ω) (X Y : dhrSectorCat (L := L) (Ω := Ω)) :
    (dhrBraiding hHaag hAdd X Y).hom ≫ (dhrBraiding hHaag hAdd Y X).hom = 𝟙 (X ⊗ Y) := by
  apply ObjectProperty.hom_ext
  change (dhrBraiding hHaag hAdd X Y).hom.hom ≫ (dhrBraiding hHaag hAdd Y X).hom.hom
    = 𝟙 (X.obj ⊗ Y.obj)
  rw [dhrBraiding_hom_hom, dhrBraiding_hom_hom]
  exact Transport.symmetry (dhrTransport hHaag hAdd Y X).tr (dhrTransport hHaag hAdd X Y).tr
    (hsym (dhrTransport hHaag hAdd Y X).tr (dhrTransport hHaag hAdd X Y).tr
      (dhrLocCone_isLocalizedIn Y) (dhrLocCone_isLocalizedIn X)
      (dhrTransport hHaag hAdd Y X).tgt_loc (dhrTransport hHaag hAdd X Y).tgt_loc
      (dhrTransport hHaag hAdd Y X).sep (dhrTransport hHaag hAdd X Y).sep)

/-- **The DHR sector category is symmetric.**  The braided structure
(`dhrBraidedCategory`) together with the symmetry of the statistics
(`SymmetricStatistics`, the `d ≥ 3` input) makes the DHR sector category a
symmetric monoidal category — the symmetric ∗-tensor structure required by the
Doplicher–Roberts reconstruction. -/
@[reducible] noncomputable def dhrSymmetricCategory
    (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω) (hsym : SymmetricStatistics Ω) :
    SymmetricCategory (dhrSectorCat (L := L) (Ω := Ω)) where
  toBraidedCategory := dhrBraidedCategory hHaag hAdd
  symmetry := dhrSymmetry hHaag hAdd hsym

/-! ### The rigid symmetric dagger target (R5)

The assembly step: a monoidal object property of the DHR sector category whose full
subcategory is rigid is a `RigidSymmetricDaggerCategory`.  The symmetric and
dagger-monoidal structures transfer from `dhrSectorCat`, the symmetry is unitary
(`dhrBraiding_isUnitary`), and the rigid structure is the supplied hypothesis — the
content of the existence of conjugates. -/

/-- **The Doplicher–Roberts target on a rigid full subcategory of `dhrSectorCat`.**
Given the symmetric DHR structure (`d ≥ 3`) and a monoidal object property `P` of
the DHR sector category whose full subcategory is `RigidCategory` — the input that
the existence of conjugates supplies — that full subcategory is a
`RigidSymmetricDaggerCategory` (Müger §1.4).  This assembles the abstract target;
the sole remaining ingredient is the rigid structure (i.e. the conjugates). -/
@[reducible] noncomputable def dhrRigidSymmetricDagger
    (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω) (hsym : SymmetricStatistics Ω)
    (P : ObjectProperty (dhrSectorCat (L := L) (Ω := Ω))) [P.IsMonoidal]
    [RigidCategory P.FullSubcategory] :
    RigidSymmetricDaggerCategory P.FullSubcategory :=
  letI := dhrSymmetricCategory hHaag hAdd hsym
  fullSubcategoryRigidSymmetricDagger P (fun X Y => dhrBraiding_isUnitary hHaag hAdd X Y)

end LocalNetLike
