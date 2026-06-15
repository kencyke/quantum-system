module

public import QuantumSystem.Algebra.Geometry.Spacelike
public import QuantumSystem.Algebra.Sector.Net.Transportable

/-!
# ε² = 1: the DHR statistics is a symmetry in high dimensions

In spacetime dimension `d ≥ 3` (more precisely, when the spacelike complement of a
cone is connected) the DHR statistics operator is not merely a *braiding* but a
*symmetry*: the monodromy is trivial,

```
ε(σ, ρ) ≫ ε(ρ, σ) = 𝟙 (σ ⊗ ρ).
```

This is the statement that high-dimensional superselection sectors obey
**permutation (Bose/Fermi) statistics** — the symmetric group acts, not the braid
group.  Categorically it is the `symmetry` axiom of a `SymmetricCategory`.

## The geometric input is irreducible

`ε² = 1` is **not** derivable from the locality and Haag-duality axioms alone: the
same abstract framework holds in `d = 2`, where the braiding is genuinely
non-symmetric (anyons).  The connectivity of the spacelike complement is therefore
a genuine, irreducible geometric hypothesis.  Following the project's pattern for
such selection inputs (Haag duality, `IsDHRTransportable`), it is isolated here as
an explicit predicate `SymmetricStatistics` — to be discharged in concrete `d ≥ 3`
models — rather than smuggled in as an axiom.

`SymmetricStatistics` packages the connectivity as the **opposite-transport
relation**: when `σ` is transported *clear of* `ρ` (to a cone spacelike to `ρ`) and
`ρ` is transported *clear of* `σ`, the reverse statistics operator is the dagger of
the forward one (`v⋆ · σ(v) = ρ(u⋆) · u`).  The algebraic keystone
`Transport.symmetry` (`Category/Statistics.lean`) then collapses the monodromy to
`1` by unitarity.

This is the form needed for the braiding on the whole DHR category, where `ρ`, `σ`
themselves need *not* be spacelike-separated (the statistics operator is defined by
transporting one clear of the other); demanding `ρ ⊥ σ` would only cover the
degenerate case where they already commute.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §6.
* Fredenhagen, Rehren, Schroer, Comm. Math. Phys. 125 (1989).
* Doplicher, Haag, Roberts, *Local observables and particle statistics II*,
  Comm. Math. Phys. 35 (1974).
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L] [SpacelikeGeometry L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- **Symmetric statistics** (the high-dimensional DHR axiom), as a net-level
predicate.  For localized sectors `ρ`, `σ`, a transport `tr` of `σ` to a cone
*spacelike to `ρ`* and a transport `tr'` of `ρ` to a cone *spacelike to `σ`*
satisfy the **opposite-transport relation**

```
tr'.hom⋆ · σ(tr'.hom) = ρ(tr.hom⋆) · tr.hom,
```

equivalently `tr'.braiding = (tr.braiding)†` — the reverse statistics operator is
the dagger of the forward one.  This is the abstract shadow of "the spacelike
complement is connected" (`d ≥ 3`): the two transport choices ("left"/"right" of
`ρ`) are linked through the connected complement.  It is an irreducible geometric
input (false in `d = 2`), to be discharged in concrete models.

`ρ` and `σ` are *not* required to be spacelike-separated themselves — the relation
is between the two transporters, each moving one sector clear of the other.  This is
the form used by the braiding on the whole DHR category. -/
def SymmetricStatistics (Ω : (s : L) → LocalNetLike.localIdx (L := L) s) : Prop :=
  ∀ {ρ σ : sectorCat L Ω} (tr : Transport ρ σ) (tr' : Transport σ ρ)
    {Λρ Λσ Λt Λt' : Cone L},
    IsLocalizedIn Λρ ρ → IsLocalizedIn Λσ σ →
    IsLocalizedIn Λt tr.tgt → IsLocalizedIn Λt' tr'.tgt →
    SpacelikeGeometry.Spacelike Λρ Λt → SpacelikeGeometry.Spacelike Λσ Λt' →
    star tr'.hom.t * σ.endo tr'.hom.t = ρ.endo (star tr.hom.t) * tr.hom.t

/-- **ε² = 1 (DHR statistics is a symmetry).**  Under the symmetric-statistics
axiom, for localized sectors `ρ`, `σ` with a transport `tr` of `σ` spacelike to `ρ`
and a transport `tr'` of `ρ` spacelike to `σ`, the monodromy of the statistics
operator is trivial:

```
ε(σ, ρ) ≫ ε(ρ, σ) = 𝟙 (σ ⊗ ρ).
```

The geometric input (`SymmetricStatistics`) supplies the opposite-transport
relation; the keystone `Transport.symmetry` collapses the monodromy by unitarity. -/
theorem coneSymmetry (hsym : SymmetricStatistics Ω)
    {ρ σ : sectorCat L Ω} {Λρ Λσ Λt Λt' : Cone L}
    (hρ : IsLocalizedIn Λρ ρ) (hσ : IsLocalizedIn Λσ σ)
    (tr : Transport ρ σ) (tr' : Transport σ ρ)
    (ht : IsLocalizedIn Λt tr.tgt) (ht' : IsLocalizedIn Λt' tr'.tgt)
    (hsp : SpacelikeGeometry.Spacelike Λρ Λt) (hsp' : SpacelikeGeometry.Spacelike Λσ Λt') :
    tr'.braiding ≫ tr.braiding = 𝟙 (σ ⊗ ρ) :=
  Transport.symmetry tr tr' (hsym tr tr' hρ hσ ht ht' hsp hsp')

end LocalNetLike
