module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra
public import QuantumSystem.Algebra.CStarAlgebra.Representation
public import QuantumSystem.Algebra.VonNeumannAlgebra.SplitInclusion

/-!
# The split property of a local net

The **split property** of a local net, in the form of Buchholz (*Product states for local
algebras*, Comm. Math. Phys. 36, 1974) and Doplicher–Longo (*Standard and split inclusions of
von Neumann algebras*, Invent. Math. 75, 1984): fix a representation `R` of the quasi-local
C⋆-algebra on a Hilbert space, with representing map `R.π`, and form the **local von Neumann
algebras**

  `𝓡(O) = R.π(𝔄(O))″`  (`LocalNet.localVonNeumannAlgebra`);

the net has the split property when, for every properly contained pair of regions `O₁ ⋐ O₂`, the
inclusion `𝓡(O₁) ≤ 𝓡(O₂)` is a split inclusion — some type I factor interpolates
(`VonNeumannAlgebra.IsSplitInclusion`).

Proper containment `⋐` (`ProperContainment`) is the abstract form of the geometric relation
"the closure of `O₁` lies in the interior of `O₂`" of the QFT literature; on a causal index set
it is model-dependent geometric input, like the causal orthogonality `⟂` itself. Its axioms —
containment, monotonicity, and a nondegenerate causal collar inside the outer region — are
necessary conditions rather than a complete axiomatisation of properness, so the split property is
always relative to the chosen `⋐`. They do force `⋐` to be strict (`ProperlyContained.lt`), which
rules out plain containment `⊆`: a reflexive `⋐` would turn the split property into the demand
that every local algebra be a type I factor. Strict containment `⊂` does satisfy all three axioms on
lattice regions — `Λ₂ \ Λ₁` is a collar for it (`ProperContainment.ofSSubset`) — so, unlike
`CausalOrthogonality (Finset α)`, the absence of a canonical `ProperContainment` instance there is a
choice, not an impossibility: `⊂` admits *touching* pairs such as `{0} ⋐ {0, 1}`, which the
literature's closure separation excludes. Separation is what needs a metric or graph structure on
the sites, and it enters through the thickening operator of `ProperContainment.ofThicken`.

The property is defined at the level of a **net of von Neumann algebras** (`VonNeumannNet`): an
isotone, local assignment `O ↦ 𝓡(O)` over a bare causal index set, with no directedness, no
quasi-local C⋆-algebra and no faithfulness. That is the level at which the index set of the split
property's own literature becomes expressible: the proper intervals of `S¹` are *not* directed
(two intervals covering the circle have no proper upper bound), as Köster's dissertation itself
notes at its definition of a chiral net. Wedges and spacelike cones are further standard
non-directed examples from the wider AQFT literature (not from the sources behind the extraction
note `docs/math/split-inclusion.md`).

The representation-theoretic net above is one instance of that (`LocalNet.vonNeumannNet`), and
`LocalNet.SplitProperty` is `VonNeumannNet.SplitProperty` at it. The hypotheses
`[IsDirectedOrder K]`, `[Nonempty K]` and `[N.Faithful]` belong to *that instance*, not to the
property: the quasi-local algebra's direct limit needs a directed index set with a base point, and
its C⋆-norm needs injective isotony embeddings. The representation
is not assumed nondegenerate: `𝓡(O)` contains `1` regardless, since a von Neumann algebra is
unital, so a degenerate representation on a nonzero space can satisfy the property trivially
(`𝓡(O) = ℂ1` is a type I factor). On the *zero* space it cannot: a type I factor needs a nonzero
minimal projection, so `IsSplitInclusion` is then identically false. Substantive downstream
theorems impose nondegeneracy or cyclicity where they need it.

## Main definitions and results

* `ProperContainment` — the proper-containment relation `O₁ ⋐ O₂` on a causal index set, with
  `ProperlyContained.le` / `.mono` / `.exists_orthogonal`, its strictness
  (`ProperContainment.irrefl`, `ProperlyContained.lt`), the lattice model
  `ProperContainment.ofThicken` built from a strictly enlarging thickening operator, the degenerate
  lattice model `ProperContainment.ofSSubset` the axioms cannot exclude, and
  `ProperContainment.exists_orthogonal_iff_not_subset`, which measures how much the collar axiom
  says on a lattice index set (namely: only strictness).
* `LocalNet.localVonNeumannAlgebra` — the local von Neumann algebra `𝓡(O) = R.π(𝔄(O))″` of a
  region in a representation of the quasi-local algebra, containing the represented local
  observables (`π_ιLocalCStar_mem_localVonNeumannAlgebra`), with isotony
  (`localVonNeumannAlgebra_mono`) and locality
  (`localVonNeumannAlgebra_le_commutant_of_orthogonal`).
* `VonNeumannNet` — an isotone, local net of von Neumann algebras over a causal index set, and
  `VonNeumannNet.SplitProperty` — **the split property**, stated there. Its consequences:
  `SplitProperty.isSplitInclusion` (the split inclusion of a properly contained pair; its tensor
  splitting follows by applying `VonNeumannAlgebra.IsSplitInclusion.exists_tensor_decomposition`
  to it), `SplitProperty.isSplitInclusion_of_le_of_properlyContained_of_le` (stability under
  enlarging the pair), and `SplitProperty.isSplitInclusion_commutant` (the commutant form,
  Borchers/Buchholz, `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O_B)′`, obtained from the nested form via locality).
  Its degenerate side is `VonNeumannNet.splitProperty_of_complex`: on a one-dimensional Hilbert
  space *every* net has the property, so no one-dimensional model is evidence about anything else.
* `LocalNet.vonNeumannNet` — the net of local von Neumann algebras of a representation, as a
  `VonNeumannNet`, and `LocalNet.SplitProperty` — the split property at that instance, with the
  three consequences above specialised to it.

## Notation

`𝔄(O)` and `𝓡(O)` in the prose above are documentation shorthand for the local C⋆-algebra
`N.algebra O` and the local von Neumann algebra `N.localVonNeumannAlgebra R O`; the convention —
and why neither is a Lean notation — is stated in full in `QuantumSystem.Algebra.LocalNet.Net`.

`⊗̄` is documentation shorthand for the von Neumann (spatial) tensor product of algebras; that
convention is stated in full in `QuantumSystem.Algebra.VonNeumannAlgebra.TensorFactor`, where the
algebras it names (`HilbertTensor.vnTensorLeft` / `vnTensorRight`) are defined.
-/

@[expose] public section

open scoped CausalOrthogonality

/-- **Proper containment of regions**: the abstract form of the relation `O₁ ⋐ O₂` ("the closure
    of `O₁` lies in the interior of `O₂`") under which the split property of a local net is
    stated. This is model-dependent geometric input on the causal index set, like `⟂` itself.

    The axioms are containment, monotonicity under shrinking the inner and enlarging the outer
    region, and a **causal collar** (`exists_orthogonal_of_properlyContained`): the outer region
    contains a *nondegenerate* region causally orthogonal to the inner one. Nondegeneracy is
    expressed as `¬ O₃ ≤ O₁`, the only sense a bare order affords — and it is what the
    literature's separation condition actually delivers. Köster's chiral index set defines its own
    `I ⋐ S¹` by "its causal complement `I' := S¹ ∖ Ī` is not the empty set", and `Ī₁ ⊂ I₂` with
    `I₂` open forces a nonempty component of `I₂ ∖ Ī₁` that is a proper interval inside `I₂`,
    disjoint from `I₁` and not contained in it.

    The collar makes `⋐` **irreflexive** (`ProperContainment.irrefl`), indeed strict
    (`ProperlyContained.lt`), which is what the literature's typography `Ī₁ ⊂ I₂` is for: without
    it plain containment `⊆` would satisfy the axioms, and a reflexive `⋐` would make the split
    property demand that every local algebra *be* a type I factor
    (`VonNeumannAlgebra.IsSplitInclusion.isTypeIFactor_of_self`) — the opposite of the type III₁
    structure expected of local algebras. The axioms remain necessary conditions rather than a
    complete axiomatisation, so the split property is still relative to the chosen `⋐`; what they
    now exclude is the degenerate choices. In particular they are *not* enough to exclude
    **touching** regions: on a lattice index set the collar clause is equivalent to plain
    `¬ Λ₂ ⊆ Λ₁` (`exists_orthogonal_iff_not_subset`), so a model that wants the literature's
    separation must build it in — which is what `ofThicken`'s strictly enlarging thickening does.
    Nothing forces `⋐` to be inhabited either: on a finite index set with no room for a collar it
    is empty and the split property holds vacuously, which is correct — a downstream theorem
    needing a genuine pair must say so itself. -/
class ProperContainment (K : Type*) [Preorder K] [CausalOrthogonality K] where
  /-- The proper-containment relation `O₁ ⋐ O₂` on regions. -/
  ProperlyContained : K → K → Prop
  /-- Proper containment implies containment. -/
  le_of_properlyContained : ∀ ⦃O₁ O₂ : K⦄, ProperlyContained O₁ O₂ → O₁ ≤ O₂
  /-- Proper containment survives shrinking the inner region and enlarging the outer one. -/
  properlyContained_mono : ∀ ⦃O₀ O₁ O₂ O₃ : K⦄, O₀ ≤ O₁ → ProperlyContained O₁ O₂ → O₂ ≤ O₃ →
      ProperlyContained O₀ O₃
  /-- **Causal collar**: a properly containing region contains a region causally orthogonal to
      the inner one and not contained in it. The last clause is the nondegeneracy that makes the
      collar a genuine buffer rather than a region orthogonal to everything (such as the empty
      lattice region); it is what forces `⋐` to be irreflexive. -/
  exists_orthogonal_of_properlyContained : ∀ ⦃O₁ O₂ : K⦄, ProperlyContained O₁ O₂ →
      ∃ O₃, O₃ ≤ O₂ ∧ O₁ ⟂ O₃ ∧ ¬ O₃ ≤ O₁

namespace ProperContainment

/-- `O₁ ⋐ O₂` : the region `O₁` is properly contained in `O₂`.

    The glyph is topology's compact-containment symbol, used here for the *binary relation* the
    QFT literature writes `Ī₁ ⊂ I₂`. Köster's dissertation uses the same glyph differently: there
    `I ⋐ S¹` is a membership predicate ("`I` is a proper interval of `S¹`"), not a relation
    between two regions of the index set — a reader coming from that source should not carry the
    predicate reading into this notation (extraction note `docs/math/causal-index-set.md`,
    convention (C7)). -/
scoped infixl:50 " ⋐ " => ProperContainment.ProperlyContained

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [ProperContainment K]

/-- Proper containment implies containment (dot-notation form). -/
theorem ProperlyContained.le {O₁ O₂ : K} (h : O₁ ⋐ O₂) : O₁ ≤ O₂ :=
  le_of_properlyContained h

/-- Proper containment survives shrinking the inner region and enlarging the outer one
    (dot-notation form). -/
theorem ProperlyContained.mono {O₀ O₁ O₂ O₃ : K} (h₀ : O₀ ≤ O₁) (h : O₁ ⋐ O₂) (h₃ : O₂ ≤ O₃) :
    O₀ ⋐ O₃ :=
  properlyContained_mono h₀ h h₃

/-- The causal collar of a proper containment (dot-notation form). -/
theorem ProperlyContained.exists_orthogonal {O₁ O₂ : K} (h : O₁ ⋐ O₂) :
    ∃ O₃, O₃ ≤ O₂ ∧ O₁ ⟂ O₃ ∧ ¬ O₃ ≤ O₁ :=
  exists_orthogonal_of_properlyContained h

/-- **Proper containment is irreflexive**: no region is properly contained in itself. This is the
    content of the collar's nondegeneracy clause — a collar inside `O` that is not contained in
    `O` cannot exist — and it is what the literature's `Ī₁ ⊂ I₂` typography encodes. -/
theorem irrefl (O : K) : ¬ (O ⋐ O) := by
  rintro h
  obtain ⟨_, hle, -, hnle⟩ := h.exists_orthogonal
  exact hnle hle

/-- A properly contained region is not above its container. -/
theorem ProperlyContained.not_ge {O₁ O₂ : K} (h : O₁ ⋐ O₂) : ¬ O₂ ≤ O₁ :=
  fun hge => irrefl O₁ (h.mono le_rfl hge)

/-- **Proper containment is strict**: `O₁ ⋐ O₂` implies `O₁ < O₂`. -/
theorem ProperlyContained.lt {O₁ O₂ : K} (h : O₁ ⋐ O₂) : O₁ < O₂ :=
  lt_of_le_not_ge h.le h.not_ge

/-- A thickening operator that strictly enlarges every nonempty region is enlarging on every
    region: on the empty region `∅ ⊆ thicken ∅` is automatic. -/
lemma subset_thicken_of_ssubset {α : Type*} {thicken : Finset α → Finset α}
    (ssubset_thicken : ∀ Λ : Finset α, Λ.Nonempty → Λ ⊂ thicken Λ) (Λ : Finset α) :
    Λ ⊆ thicken Λ := by
  rcases Λ.eq_empty_or_nonempty with rfl | hne
  · exact Finset.empty_subset _
  · exact (ssubset_thicken Λ hne).subset

/-- **On lattice regions the collar clause says only that `Λ₂` is not contained in `Λ₁`.** With
    `⟂ = Disjoint` on `Finset α` the region `Λ₂ \ Λ₁` is automatically orthogonal to `Λ₁`, so it
    witnesses the collar as soon as it is nonempty; conversely a collar inside `Λ₂` that is not
    inside `Λ₁` forbids `Λ₂ ⊆ Λ₁`.

    This is worth stating because it bounds what the `ProperContainment` axioms can be asked to
    do. On a lattice index set they pin down strictness and nothing more: they do **not** by
    themselves exclude *touching* pairs such as `{0} ⋐ {0, 1}`, which the literature does exclude
    (a pair of local algebras of touching regions is not statistically independent, hence not
    split — Buchholz's *Product states for local algebras* records that postulating normal product
    states for touching regions already yields contradictions for the free field, the corpus's one
    statement that the closure separation is *necessary*).
    Genuine separation is therefore the model's job, not the class's — see `ofThicken`,
    whose thickening operator supplies a buffer layer between `Λ₁` and the collar. -/
lemma exists_orthogonal_iff_not_subset {α : Type*} {Λ₁ Λ₂ : Finset α} :
    (∃ Λ₃ : Finset α, Λ₃ ≤ Λ₂ ∧ Λ₁ ⟂ Λ₃ ∧ ¬ Λ₃ ≤ Λ₁) ↔ ¬ Λ₂ ⊆ Λ₁ := by
  classical
  constructor
  · rintro ⟨Λ₃, hle, -, hnle⟩ hsub
    exact hnle (hle.trans hsub)
  · intro hns
    refine ⟨Λ₂ \ Λ₁, Finset.sdiff_subset, Finset.disjoint_sdiff, ?_⟩
    obtain ⟨x, hx₂, hx₁⟩ := Finset.not_subset.1 hns
    exact fun hsub => hx₁ (hsub (Finset.mem_sdiff.2 ⟨hx₂, hx₁⟩))

/-- **Strict containment already satisfies the axioms**, on any lattice index set and with no
    structure on the sites: containment and monotonicity are immediate, and `Λ₂ \ Λ₁` is a collar
    (`exists_orthogonal_iff_not_subset`). So nothing in the class *prevents* a canonical lattice
    instance — what it fails to deliver is separation, and this model is the witness of that
    failure: it admits the *touching* pair `{0} ⋐ {0, 1}`, whose local algebras the literature
    records as not statistically independent, hence not split.

    Deliberately a `def` rather than an `instance`, and never activated anywhere: it exists to
    exhibit the gap, not to be used. A model that wants separation supplies a thickening operator
    (`ofThicken`). -/
@[reducible] def ofSSubset (α : Type*) : ProperContainment (Finset α) where
  ProperlyContained Λ₁ Λ₂ := Λ₁ ⊂ Λ₂
  le_of_properlyContained _ _ h := le_of_lt h
  properlyContained_mono _ _ _ _ h₀ h h₃ := (h₀.trans_lt h).trans_le h₃
  exists_orthogonal_of_properlyContained _ _ h :=
    exists_orthogonal_iff_not_subset.2 fun hsub => absurd (h.subset.antisymm hsub) (ne_of_lt h)

/-- Proper containment of lattice regions from a **thickening operator** (e.g. the
    `r`-neighbourhood for a metric or graph structure on the sites): `Λ₁ ⋐ Λ₂` iff the thickening
    of `Λ₁` is a *strict* subset of `Λ₂`.

    The thickening is required to be *strictly* enlarging on nonempty regions
    (`ssubset_thicken`). What that buys is the chain `Λ₁ ⊊ thicken Λ₁ ⊆ Λ₂` under `Λ₁ ⋐ Λ₂`, with
    the collar `Λ₂ \ thicken Λ₁` disjoint from the whole of `thicken Λ₁` rather than merely from
    `Λ₁`: the collar is separated from `Λ₁` *by the thickening's own notion of nearness*.

    Whether that is geometric separation is the thickening's business and is **not** a consequence
    of the two hypotheses. The one-sided `thicken Λ = Λ ∪ Λ.image (· + 1)` is monotone and strictly
    enlarging, yet `{0} ⋐ {-1, 0, 1, 2}` has collar `{-1, 2}`, which touches `{0}` from below. A
    thickening that is a genuine neighbourhood operator — enlarging in *every* direction of
    adjacency, as the 1-neighbourhood `ProperContainment.nbhd` of the integer chain is in
    `QuantumSystem.Algebra.LocalNet.Examples` — does exclude *touching* pairs, which is the
    exclusion the literature's `Ī₁ ⊂ I₂` typography performs and one the class axioms alone cannot
    perform on a lattice (`exists_orthogonal_iff_not_subset`). What strictness rules out by itself
    is `thicken := id`, i.e. the degenerate model `ofSSubset`, in which `{0} ⋐ {0, 1}` is admitted.

    On the empty region no strictness is asked, since a neighbourhood operator has
    `thicken ∅ = ∅`; `∅ ⊆ thicken ∅` holds regardless and is all the axioms need there. -/
@[reducible] def ofThicken {α : Type*} [DecidableEq α] (thicken : Finset α → Finset α)
    (ssubset_thicken : ∀ Λ : Finset α, Λ.Nonempty → Λ ⊂ thicken Λ)
    (thicken_mono : Monotone thicken) :
    ProperContainment (Finset α) where
  ProperlyContained Λ₁ Λ₂ := thicken Λ₁ ⊂ Λ₂
  le_of_properlyContained _ _ h := (subset_thicken_of_ssubset ssubset_thicken _).trans h.subset
  properlyContained_mono _ _ _ _ h₀ h h₃ := ((thicken_mono h₀).trans_lt h).trans_le h₃
  exists_orthogonal_of_properlyContained Λ₁ Λ₂ h := by
    refine ⟨Λ₂ \ thicken Λ₁, Finset.sdiff_subset,
      Finset.disjoint_sdiff.mono_left (subset_thicken_of_ssubset ssubset_thicken Λ₁), ?_⟩
    obtain ⟨x, hx₂, hx₁⟩ := Finset.exists_of_ssubset h
    exact fun hsub =>
      hx₁ (subset_thicken_of_ssubset ssubset_thicken Λ₁ (hsub (Finset.mem_sdiff.2 ⟨hx₂, hx₁⟩)))

end ProperContainment

/-! ### Nets of von Neumann algebras

The split property is a statement about a net of *von Neumann* algebras, and it is stated here at
that level. A `VonNeumannNet` is an isotone, local assignment `O ↦ 𝓡(O)` of von Neumann algebras
on a fixed Hilbert space over a bare causal index set: no directedness, no quasi-local C⋆-algebra,
no faithfulness — none of which the property mentions. Non-directed index sets are therefore in
scope — as they must be: the proper intervals of `S¹`, the index set of the chiral split property,
are not directed (two intervals covering the circle have no *proper* upper bound), a point Köster's
dissertation makes explicitly. Wedges and spacelike cones are further standard non-directed
examples from the wider AQFT literature.

The net of local von Neumann algebras of a representation of the quasi-local C⋆-algebra is one
instance (`LocalNet.vonNeumannNet`), and `LocalNet.SplitProperty` is this property at that
instance.
-/

open scoped ProperContainment VonNeumannAlgebra

/-- A **net of von Neumann algebras** over a causal index set `K`, acting on a fixed Hilbert space
    `H`: the assignment `O ↦ 𝓡(O)` together with **isotony** (`algebra_mono`) and **locality**
    (`algebra_le_commutant_of_orthogonal`, Einstein causality `𝓡(O₁) ≤ 𝓡(O₂)′` for `O₁ ⟂ O₂`).

    This is the level at which the split property is stated in the literature — Buchholz's local
    rings `𝓡(O)`, Doplicher–Longo's `W*`-inclusions, Köster's chiral nets assigning a von Neumann
    algebra to each proper interval. The index set carries only a `Preorder` and `⟂`; in
    particular it is not assumed directed, so the index sets those sources use are expressible. -/
structure VonNeumannNet (K : Type*) [Preorder K] [CausalOrthogonality K]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The local von Neumann algebra `𝓡(O)` assigned to a region. -/
  algebra : K → VonNeumannAlgebra H
  /-- **Isotony**: a larger region carries a larger algebra. -/
  algebra_mono : Monotone algebra
  /-- **Locality** (microcausality): causally orthogonal regions carry commuting algebras. -/
  algebra_le_commutant_of_orthogonal : ∀ ⦃O₁ O₂ : K⦄, O₁ ⟂ O₂ → algebra O₁ ≤ (algebra O₂)′

namespace VonNeumannNet

variable {K : Type*} [Preorder K] [CausalOrthogonality K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The split property** of a net of von Neumann algebras (Buchholz; Doplicher–Longo): for every
    properly contained pair of regions `O₁ ⋐ O₂`, some type I factor interpolates between the
    local algebras, `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O₂)`. This is genuinely model-dependent input — it fails for
    nets without the requisite phase-space (nuclearity) behaviour — and it is relative to the
    chosen proper containment `⋐` (see `ProperContainment`).

    This is the *nested* form. The historically original *commutant* form is
    `SplitProperty.isSplitInclusion_commutant`, which follows from this one through locality; the
    converse needs Haag duality and is not available here. -/
def SplitProperty [ProperContainment K] (vnNet : VonNeumannNet K H) : Prop :=
  ∀ ⦃O₁ O₂ : K⦄, O₁ ⋐ O₂ →
    VonNeumannAlgebra.IsSplitInclusion (vnNet.algebra O₁) (vnNet.algebra O₂)

/-- **Every net of von Neumann algebras on `ℂ` has the split property** — whatever the net,
    whatever the proper containment. On the one-dimensional Hilbert space the only von Neumann
    algebra is `𝓑(ℂ)` (`VonNeumannAlgebra.eq_boundedLinearOperators_complex`), a type I factor, so
    every inclusion of the net is the split inclusion `𝓑(ℂ) ≤ 𝓑(ℂ)`.

    Stated here, rather than left implicit inside a witness, because it fixes what a
    one-dimensional model can be evidence *for*: it inhabits `SplitProperty` and distinguishes
    nothing — no net, no representation, no choice of `⋐`. The degeneracy is `dim H = 1` and
    nothing else; it is the escape clause Halvorson–Müger's type III₁ proposition carries
    explicitly ("either `𝓡 = ℂ1` or `𝓡` is a type III₁ factor"). -/
theorem splitProperty_of_complex [ProperContainment K] (vnNet : VonNeumannNet K ℂ) :
    vnNet.SplitProperty := by
  intro O₁ O₂ _
  rw [VonNeumannAlgebra.eq_boundedLinearOperators_complex (vnNet.algebra O₁),
    VonNeumannAlgebra.eq_boundedLinearOperators_complex (vnNet.algebra O₂)]
  exact (VonNeumannAlgebra.isTypeIFactor_boundedLinearOperators (H := ℂ)).isSplitInclusion_self

variable [ProperContainment K] {vnNet : VonNeumannNet K H}

/-- **The split inclusion of a properly contained pair**: under the split property, `O₁ ⋐ O₂`
    yields the split inclusion `𝓡(O₁) ≤ 𝓡(O₂)`. Buchholz's tensor splitting — a unitary
    `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` carrying `𝓡(O₁)` into the tensor factor `𝓑(ℓ²(F)) ⊗̄ 1` and the
    commutant `𝓡(O₂)′` into `1 ⊗̄ 𝓑(eH)`, with the interpolating type I factor and its commutant
    identified exactly — is obtained by applying
    `VonNeumannAlgebra.IsSplitInclusion.exists_tensor_decomposition` to the conclusion. -/
theorem SplitProperty.isSplitInclusion (hs : vnNet.SplitProperty) {O₁ O₂ : K} (h : O₁ ⋐ O₂) :
    VonNeumannAlgebra.IsSplitInclusion (vnNet.algebra O₁) (vnNet.algebra O₂) :=
  hs h

/-- The split property extends to enlarged pairs: if `O₀ ≤ O₁ ⋐ O₂ ≤ O₃` then the inclusion
    `𝓡(O₀) ≤ 𝓡(O₃)` is split as well. -/
lemma SplitProperty.isSplitInclusion_of_le_of_properlyContained_of_le (hs : vnNet.SplitProperty)
    {O₀ O₁ O₂ O₃ : K} (h₀ : O₀ ≤ O₁) (h : O₁ ⋐ O₂) (h₃ : O₂ ≤ O₃) :
    VonNeumannAlgebra.IsSplitInclusion (vnNet.algebra O₀) (vnNet.algebra O₃) :=
  hs (h.mono h₀ h₃)

/-- **The commutant form of the split property** (Borchers' conjecture as displayed in Buchholz,
    *Product states for local algebras*): for a properly contained pair `O₁ ⋐ O₂` and any region
    `O_B` causally orthogonal to `O₂`, a type I factor interpolates between `𝓡(O₁)` and the
    commutant `𝓡(O_B)′`,

      `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O_B)′`.

    This is the historically original shape of the property, for a *disjoint* pair with slack
    rather than a nested one. The nested form implies it through locality
    (`algebra_le_commutant_of_orthogonal`); the converse needs Haag duality, which is not assumed
    anywhere here. Buchholz displays the symmetric four-term chain `𝓡(O₁) ⊂ M₁ ⊂ M₂′ ⊂ 𝓡(O₂)′`
    with two interpolating type I factors; this is its one-sided compression, which is the form
    the adopted definition of a split inclusion carries. -/
theorem SplitProperty.isSplitInclusion_commutant (hs : vnNet.SplitProperty) {O₁ O₂ O_B : K}
    (h : O₁ ⋐ O₂) (hd : O₂ ⟂ O_B) :
    VonNeumannAlgebra.IsSplitInclusion (vnNet.algebra O₁) (vnNet.algebra O_B)′ :=
  (hs h).mono le_rfl (vnNet.algebra_le_commutant_of_orthogonal hd)

end VonNeumannNet

namespace LocalNet

open scoped ProperContainment VonNeumannAlgebra

section LocalAlgebras

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : LocalNet K) [N.Faithful]

/-- The **local von Neumann algebra** `𝓡(O) = R.π(𝔄(O))″` of a region in a representation of the
    quasi-local C⋆-algebra: the von Neumann algebra generated by the image of the local algebra.
    The generating set is star-closed (`star_range_π_ιLocalCStar`), so
    `VonNeumannAlgebra.generated` — which symmetrizes in general — is literally the double
    commutant here (`coe_localVonNeumannAlgebra`). Since `R.π` is a possibly non-unital
    `*`-homomorphism, `𝓡(O)` always contains `1` even when `R.π(𝔄(O))` does not, matching the `″`
    convention. -/
noncomputable def localVonNeumannAlgebra (R : CStarRep N.quasiLocalCStarAlgebra) (O : K) :
    VonNeumannAlgebra R.H :=
  VonNeumannAlgebra.generated (Set.range fun a : N.algebra O => R.π (N.ιLocalCStar O a))

/-- Local observables are represented inside the local von Neumann algebra of their region. -/
lemma π_ιLocalCStar_mem_localVonNeumannAlgebra (R : CStarRep N.quasiLocalCStarAlgebra) (O : K)
    (a : N.algebra O) : R.π (N.ιLocalCStar O a) ∈ N.localVonNeumannAlgebra R O :=
  VonNeumannAlgebra.mem_generated_of_mem ⟨a, rfl⟩

/-- The generating set of `𝓡(O)` is star-closed: `𝔄(O)` is star-closed, and both the embedding
    into the quasi-local algebra and `R.π` are `*`-maps, so `Set.star_range` applies to the
    composite. -/
lemma star_range_π_ιLocalCStar (R : CStarRep N.quasiLocalCStarAlgebra) (O : K) :
    star (Set.range fun a : N.algebra O => R.π (N.ιLocalCStar O a))
      = Set.range fun a : N.algebra O => R.π (N.ιLocalCStar O a) :=
  Set.star_range fun a => by rw [N.ιLocalCStar_star, map_star]

/-- **`𝓡(O)` is literally the double commutant `R.π(𝔄(O))″`.** `VonNeumannAlgebra.generated`
    symmetrizes its generating set in general; here the set is already star-closed
    (`star_range_π_ιLocalCStar`), so no symmetrization happens and the definition agrees with the
    `″` of the operator-algebra literature. -/
lemma coe_localVonNeumannAlgebra (R : CStarRep N.quasiLocalCStarAlgebra) (O : K) :
    (N.localVonNeumannAlgebra R O : Set (R.H →L[ℂ] R.H))
      = (Set.range fun a : N.algebra O => R.π (N.ιLocalCStar O a)).centralizer.centralizer :=
  VonNeumannAlgebra.coe_generated_of_star_eq (N.star_range_π_ιLocalCStar R O)

/-- **Isotony** of the local von Neumann algebras: `O ≤ O'` gives `𝓡(O) ≤ 𝓡(O')`. -/
lemma localVonNeumannAlgebra_mono (R : CStarRep N.quasiLocalCStarAlgebra) {O O' : K}
    (h : O ≤ O') : N.localVonNeumannAlgebra R O ≤ N.localVonNeumannAlgebra R O' := by
  refine VonNeumannAlgebra.generated_mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨N.incl h a, by simp⟩

/-- **Locality** of the local von Neumann algebras: causally orthogonal regions have commuting
    algebras, `𝓡(O₁) ≤ 𝓡(O₂)′`. Einstein causality survives the double commutant. -/
lemma localVonNeumannAlgebra_le_commutant_of_orthogonal (R : CStarRep N.quasiLocalCStarAlgebra)
    {O₁ O₂ : K} (hd : O₁ ⟂ O₂) :
    N.localVonNeumannAlgebra R O₁ ≤ (N.localVonNeumannAlgebra R O₂)′ := by
  have key : VonNeumannAlgebra.generated
      (Set.range fun a : N.algebra O₁ => R.π (N.ιLocalCStar O₁ a))
      ≤ VonNeumannAlgebra.commutantSet
        (Set.range fun b : N.algebra O₂ => R.π (N.ιLocalCStar O₂ b)) := by
    refine VonNeumannAlgebra.generated_le ?_
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, VonNeumannAlgebra.mem_commutantSet_iff]
    rintro _ ⟨b, rfl⟩
    refine ⟨(N.ιLocalCStar_commute_of_orthogonal hd.symm b a).map R.π, ?_⟩
    have hb : star (R.π (N.ιLocalCStar O₂ b)) = R.π (N.ιLocalCStar O₂ (star b)) := by
      rw [← map_star, N.ιLocalCStar_star]
    rw [hb]
    exact (N.ιLocalCStar_commute_of_orthogonal hd.symm (star b) a).map R.π
  exact key.trans_eq (VonNeumannAlgebra.commutant_generated _).symm

/-- **The net of local von Neumann algebras** of a representation, as a `VonNeumannNet`: isotony
    is `localVonNeumannAlgebra_mono` and locality is
    `localVonNeumannAlgebra_le_commutant_of_orthogonal`, both already proved. This is the bridge
    from the C⋆-level net data to the von-Neumann-level object the split property is about. -/
noncomputable def vonNeumannNet (R : CStarRep N.quasiLocalCStarAlgebra) :
    VonNeumannNet K R.H where
  algebra := N.localVonNeumannAlgebra R
  algebra_mono _ _ h := N.localVonNeumannAlgebra_mono R h
  algebra_le_commutant_of_orthogonal _ _ hd :=
    N.localVonNeumannAlgebra_le_commutant_of_orthogonal R hd

/-- The algebras of the net `vonNeumannNet R` are the local von Neumann algebras themselves. -/
@[simp] lemma vonNeumannNet_algebra (R : CStarRep N.quasiLocalCStarAlgebra) (O : K) :
    (N.vonNeumannNet R).algebra O = N.localVonNeumannAlgebra R O := rfl

/-- **The split property** of a local net in a representation `π` of the quasi-local C⋆-algebra
    (Buchholz; Doplicher–Longo): the split property of the associated net of local von Neumann
    algebras (`VonNeumannNet.SplitProperty`) — for every properly contained pair of regions
    `O₁ ⋐ O₂`, some type I factor interpolates, `𝓡(O₁) ≤ M ≤ 𝓡(O₂)`.

    The property itself is defined at the von-Neumann-net level, where it needs neither a
    directed index set nor a quasi-local C⋆-algebra; the hypotheses `[IsDirectedOrder K]`,
    `[Nonempty K]` and `[N.Faithful]` here are the cost of *this instance*, whose local algebras
    are built from a representation of the quasi-local C⋆-algebra. Nets over non-directed index
    sets are stated through `VonNeumannNet.SplitProperty` directly. -/
def SplitProperty [ProperContainment K] (R : CStarRep N.quasiLocalCStarAlgebra) : Prop :=
  (N.vonNeumannNet R).SplitProperty

end LocalAlgebras

section SplitConsequences

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable [ProperContainment K] {N : LocalNet K} [N.Faithful]
variable {R : CStarRep N.quasiLocalCStarAlgebra}

/-- The split property extends to enlarged pairs: if `O₀ ≤ O₁ ⋐ O₂ ≤ O₃` then the inclusion
    `𝓡(O₀) ≤ 𝓡(O₃)` is split as well. Specialisation of
    `VonNeumannNet.SplitProperty.isSplitInclusion_of_le_of_properlyContained_of_le`. -/
lemma SplitProperty.isSplitInclusion_of_le_of_properlyContained_of_le (hs : N.SplitProperty R)
    {O₀ O₁ O₂ O₃ : K} (h₀ : O₀ ≤ O₁) (h : O₁ ⋐ O₂) (h₃ : O₂ ≤ O₃) :
    VonNeumannAlgebra.IsSplitInclusion
      (N.localVonNeumannAlgebra R O₀) (N.localVonNeumannAlgebra R O₃) :=
  VonNeumannNet.SplitProperty.isSplitInclusion_of_le_of_properlyContained_of_le hs h₀ h h₃

/-- **The split inclusion of a properly contained pair**: under the split property, `O₁ ⋐ O₂`
    yields the split inclusion `𝓡(O₁) ≤ 𝓡(O₂)`. Specialisation of
    `VonNeumannNet.SplitProperty.isSplitInclusion`, whose docstring describes the tensor splitting
    that follows. (The instantiated existential is deliberately not restated here: spelling it out
    over `R.H` forces the elaborator to unfold the quasi-local algebra inside `R`'s type, while
    consuming the general statement through this corollary is cheap.) -/
theorem SplitProperty.isSplitInclusion (hs : N.SplitProperty R) {O₁ O₂ : K} (h : O₁ ⋐ O₂) :
    VonNeumannAlgebra.IsSplitInclusion
      (N.localVonNeumannAlgebra R O₁) (N.localVonNeumannAlgebra R O₂) :=
  VonNeumannNet.SplitProperty.isSplitInclusion hs h

/-- **The commutant form of the split property** (Borchers' conjecture as displayed in Buchholz,
    *Product states for local algebras*): for a properly contained pair `O₁ ⋐ O₂` and any region
    `O_B` causally orthogonal to `O₂`, a type I factor interpolates between `𝓡(O₁)` and the
    commutant `𝓡(O_B)′`. Specialisation of
    `VonNeumannNet.SplitProperty.isSplitInclusion_commutant`, whose docstring records what the
    converse would need (Haag duality) and how this one-sided form relates to Buchholz's
    symmetric four-term chain. -/
theorem SplitProperty.isSplitInclusion_commutant (hs : N.SplitProperty R) {O₁ O₂ O_B : K}
    (h : O₁ ⋐ O₂) (hd : O₂ ⟂ O_B) :
    VonNeumannAlgebra.IsSplitInclusion
      (N.localVonNeumannAlgebra R O₁) (N.localVonNeumannAlgebra R O_B)′ :=
  VonNeumannNet.SplitProperty.isSplitInclusion_commutant hs h hd

end SplitConsequences

end LocalNet
