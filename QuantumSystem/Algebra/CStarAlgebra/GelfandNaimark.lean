module

public import QuantumSystem.Algebra.CStarAlgebra.GNS.DirectSum
public import QuantumSystem.Algebra.CStarAlgebra.GNS.Separable

/-!
# The Gelfand-Naimark theorem

Every C\*-algebra, not necessarily unital and not necessarily commutative, is isometrically
`*`-isomorphic onto a norm closed `*`-subalgebra of the bounded operators on some complex
Hilbert space.  This is the noncommutative Gelfand-Naimark theorem (Gelfand-Naimark 1943;
Murphy, *C\*-algebras and Operator Theory*, Ch. 3 "Ideals and Positive Functionals"; Pedersen,
*C\*-Algebras and Their Automorphism Groups*, Ch. 3 "Functionals and Representations";
Blackadar, *Operator Algebras*, Ch. II "C\*-Algebras"; Takesaki, *Theory of Operator Algebras
I*, Ch. I "Fundamentals of Banach Algebras and C\*-Algebras" — chapter-level locators only,
since none of these four books was independently opened for this file; see the `math-review`
ledger entry for `GelfandNaimark.lean`), and it is not to be confused with the commutative
Gelfand-Naimark theorem — Gelfand duality — which Mathlib carries as
`gelfandTransform_isometry`.

## Main results

* `CStarRep.exists_isometric` — there is a representation `R : CStarRep A` whose `R.π` is
  isometric, injective, and has norm closed range.  The three conjuncts together say that
  `R.π` identifies `A` with a C\*-subalgebra of `𝓑(R.H)`.
* `CStarRep.exists_starAlgEquiv_range` — the same statement in the form the classical
  formulation uses: an explicit `*`-isomorphism of `A` onto a norm closed `*`-subalgebra
  of `𝓑(R.H)` that preserves the norm.
* `CStarRep.exists_isometric_separable` — the **separable refinement**: when `A` is
  separable the Hilbert space may be taken separable as well.

The witness for the first two is `GNS.DirectSum.rep`, the ℓ²-direct sum of the GNS
representations of all pure states of `A`; faithfulness comes from there being enough pure
states (`IsPureState.exists_pos_re_of_ne_zero`), and isometry from faithfulness by
`NonUnitalStarAlgHom.norm_map`. The separable refinement uses a different witness,
`GNS.normingRep`, indexed by a dense sequence of the algebra instead of by the whole pure
state space.

## Conventions and scope

* The Hilbert space is produced in the *same* universe as `A`, which is stronger than the
  usual textbook statement.
* Closedness of the range uses completeness of `A`; `NonUnitalStarAlgHom.range` supplies the
  `*`-subalgebra structure, so "closed `*`-subalgebra" is exactly "C\*-subalgebra" here.
* Nondegeneracy of the representation is not asserted.  It would not strengthen the
  statement: corestricting any isometric `*`-representation to the closure of the span of
  its image is again isometric and is nondegenerate, so the two existentials are equivalent.
  (The witness `GNS.DirectSum.rep` is in fact nondegenerate, being a direct sum of cyclic
  representations.)
* The witness of `CStarRep.exists_isometric` is itself never separable beyond the trivial
  cases: it is indexed by the whole pure state space, and for `A = C₀(ℝ)` the point
  evaluations already form a continuum.  The separable refinement therefore does not
  strengthen that theorem's witness but replaces it — see
  `CStarRep.exists_isometric_separable` and `GNS.normingRep`.
* `CStarRep.exists_isometric_separable` does **not** claim that `H` may be taken to be
  `ℓ²(ℕ)`.  That is true, by the unitary classification of Hilbert spaces by the cardinality
  of an orthonormal basis, but it is extra content and is not stated here.
* There is no unital corollary: nothing here states `R.π 1 = 1` for unital `A`.
-/

@[expose] public section

open scoped ComplexHilbertSpace

universe u


/-- **Gelfand-Naimark theorem** (noncommutative form, `A` not necessarily unital):
every C\*-algebra admits a faithful isometric `*`-representation whose image is norm closed,
that is, `A` is carried onto a C\*-subalgebra of `𝓑(H)` for some complex Hilbert space `H`.

The three conjuncts are what make the conclusion an identification rather than a mere bound:
`Isometry R.π` gives `‖R.π a‖ = ‖a‖`, `Function.Injective R.π` makes `R.π` a bijection onto
its image, and `IsClosed` upgrades the `*`-subalgebra `NonUnitalStarAlgHom.range R.π` to a C\*-subalgebra.  For
the same statement packaged as an explicit `*`-isomorphism, see
`CStarRep.exists_starAlgEquiv_range`.

The Hilbert space is obtained in the same universe as `A`.  The witness is
`GNS.DirectSum.rep A`, the ℓ²-direct sum of the GNS representations of all pure states. -/
theorem CStarRep.exists_isometric (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ R : CStarRep.{u, u} A,
      Isometry R.π ∧ Function.Injective R.π ∧ IsClosed (NonUnitalStarAlgHom.range R.π : Set 𝓑(R.H)) :=
  ⟨GNS.DirectSum.rep A, GNS.DirectSum.rep_isometry, GNS.DirectSum.rep_injective,
    GNS.DirectSum.rep_isClosed_range⟩


/-- **Gelfand-Naimark theorem**, in the form the classical statement uses: every
C\*-algebra `A`, not necessarily unital, is isometrically `*`-isomorphic onto a norm closed
`*`-subalgebra `S` of `𝓑(H)` for some complex Hilbert space `H`.

Isometry is stated as `‖(e a : 𝓑(R.H))‖ = ‖a‖` — the norm `S` inherits from `𝓑(R.H)` —
rather than through a norm structure on `S` itself.  See `CStarRep.exists_isometric` for the
unbundled form. -/
theorem CStarRep.exists_starAlgEquiv_range (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ (R : CStarRep.{u, u} A) (S : NonUnitalStarSubalgebra ℂ 𝓑(R.H)) (e : A ≃⋆ₐ[ℂ] S),
      IsClosed (S : Set 𝓑(R.H)) ∧ ∀ a : A, ‖((e a : S) : 𝓑(R.H))‖ = ‖a‖ :=
  ⟨GNS.DirectSum.rep A, NonUnitalStarAlgHom.range (GNS.DirectSum.rep A).π, GNS.DirectSum.repRangeEquiv A,
    GNS.DirectSum.rep_isClosed_range, GNS.DirectSum.norm_repRangeEquiv⟩


/-- **Gelfand-Naimark theorem, separable refinement**: a *separable* C\*-algebra, not
necessarily unital, admits a faithful isometric `*`-representation with norm closed image on
a **separable** complex Hilbert space.

The refinement is genuine extra content over `CStarRep.exists_isometric`, whose witness is
indexed by the whole pure state space and is nonseparable for, say, `A = C₀(ℝ)`.  The
witness here is `GNS.normingRep A`: the ℓ²-direct sum of the GNS representations of a
*countable* family of pure states, one norming each nonzero member of a dense sequence of
`A`.  Norming rather than merely detecting is what makes a countable family separate the
points of `A` — see `GNS.normingFamily_separatesPoints`.

Separability of `A` is sufficient and never necessary: `𝓑(ℓ²)` is not norm separable, yet
its identity representation on the separable space `ℓ²` is faithful. -/
theorem CStarRep.exists_isometric_separable (A : Type u) [NonUnitalCStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] :
    ∃ R : CStarRep.{u, u} A, TopologicalSpace.SeparableSpace R.H ∧
      Isometry R.π ∧ Function.Injective R.π ∧
      IsClosed (NonUnitalStarAlgHom.range R.π : Set 𝓑(R.H)) :=
  ⟨GNS.normingRep A, inferInstance, GNS.normingRep_isometry A, GNS.normingRep_injective A,
    GNS.normingRep_isClosed_range A⟩
