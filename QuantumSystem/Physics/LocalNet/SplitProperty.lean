/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.SplitInclusion
public import QuantumSystem.Physics.LocalNet.VonNeumannNet

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
lattice regions — `O₂ \ O₁` is a collar for it (`ProperContainment.ofLT`) — so, unlike
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
non-directed examples from the wider AQFT literature (Buchholz 1974, Doplicher–Longo 1984 treat
the split property itself; the non-directed index sets come from the surrounding literature).

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
  (`ProperContainment.irrefl`, `ProperlyContained.lt`), the model `ProperContainment.ofThicken`
  on lattice regions built from a monotone enlarging thickening operator, the degenerate model
  `ProperContainment.ofLT` (strict containment) the axioms cannot exclude, and
  `ProperContainment.exists_disjoint_iff_not_le`, which measures how much the collar axiom says on
  a lattice index set (namely: only strictness). The metric model on infinite lattice regions,
  `ProperContainment.ofCThickening`, and the extension of a finite-region net to infinite regions
  live in `QuantumSystem.Physics.LocalNet.InfiniteRegion`.
* `VonNeumannNet.SplitProperty` — **the split property** of a net of von Neumann algebras
  (`VonNeumannNet`, `LocalNet.localVonNeumannAlgebra` and `LocalNet.vonNeumannNet` are in
  `QuantumSystem.Physics.LocalNet.VonNeumannNet`). Its consequences:
  `SplitProperty.isSplitInclusion` (the split inclusion of a properly contained pair; its tensor
  splitting follows by applying `VonNeumannAlgebra.IsSplitInclusion.exists_tensor_decomposition`
  to it), `SplitProperty.isSplitInclusion_of_le_of_properlyContained_of_le` (stability under
  enlarging the pair), and `SplitProperty.isSplitPair` (the commutant form,
  Borchers/Buchholz, `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O_B)′`, obtained from the nested form via locality).
  The commutant form on its own, with no gap between the regions, is `VonNeumannNet.IsSplitPair`,
  a symmetric relation (`VonNeumannNet.IsSplitPair.symm`); Matsui's half-chain split property is
  of that form.
  Its degenerate side is `VonNeumannNet.splitProperty_of_complex`: on a one-dimensional Hilbert
  space *every* net has the property, so no one-dimensional model is evidence about anything else.
* `LocalNet.SplitProperty` — the split property at the net `LocalNet.vonNeumannNet` of a
  representation, an `abbrev` to which the three consequences above apply directly.

## Notation

`O₁ ⋐ O₂` is `ProperContainment.ProperlyContained O₁ O₂`; activate it with
`open scoped ProperContainment`.

`𝔄(O)` and `𝓡(O)` in the prose above are documentation shorthand for the local C⋆-algebra
`N.algebra O` and the local von Neumann algebra `N.localVonNeumannAlgebra R O`; the convention —
and why neither is a Lean notation — is stated in full in `QuantumSystem.Physics.LocalNet.Basic`.

`⊗̄` is documentation shorthand for the von Neumann (spatial) tensor product of algebras; that
convention is stated in full in `QuantumSystem.Analysis.VonNeumannAlgebra.TensorFactor`, where the
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
    disjoint from `I₁` and not contained in it. On such an index set, where the difference of two
    regions need not be a region, the collar is a genuine constraint on `⋐`: with no causally
    orthogonal regions at all it forces `⋐` to be empty.

    The collar makes `⋐` **irreflexive** (`ProperContainment.irrefl`), indeed strict
    (`ProperlyContained.lt`), which is what the literature's typography `Ī₁ ⊂ I₂` is for: without
    it plain containment `⊆` would satisfy the axioms, and a reflexive `⋐` would make the split
    property demand that every local algebra *be* a type I factor
    (`VonNeumannAlgebra.IsSplitInclusion.isTypeIFactor_of_self`) — the opposite of the type III₁
    structure expected of local algebras.

    The axioms are necessary conditions rather than a complete axiomatisation, so the split
    property is relative to the chosen `⋐`. In particular they do **not** exclude *touching*
    regions, which the literature's separation does exclude: on lattice regions, where `⟂` is
    `Disjoint` and differences are regions, the collar clause is equivalent to plain `¬ O₂ ≤ O₁`
    (`exists_disjoint_iff_not_le`), so strict containment satisfies the axioms (`ofLT`) and admits
    `{0} ⋐ {0, 1}`. A model that wants genuine separation must build it in, which is what
    `ofThicken` with a two-sided neighbourhood operator does: the integer-chain model of
    `QuantumSystem.Physics.LocalNet.Examples` on finite regions, and the metric model
    `ofCThickening` of `QuantumSystem.Physics.LocalNet.InfiniteRegion` on infinite ones. Nor do
    the axioms force `⋐` to relate any genuine pair; see `VonNeumannNet.SplitProperty` for what
    that means for the property. -/
class ProperContainment (K : Type*) [Preorder K] [CausalOrthogonality K] where
  /-- The proper-containment relation `O₁ ⋐ O₂` on regions. -/
  ProperlyContained : K → K → Prop
  /-- Proper containment implies containment. -/
  le_of_properlyContained : ∀ ⦃O₁ O₂ : K⦄, ProperlyContained O₁ O₂ → O₁ ≤ O₂
  /-- Proper containment survives shrinking the inner region and enlarging the outer one. -/
  properlyContained_mono : ∀ ⦃O₀ O₁ O₂ O₃ : K⦄, O₀ ≤ O₁ → ProperlyContained O₁ O₂ →
      O₂ ≤ O₃ → ProperlyContained O₀ O₃
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
    predicate reading into this notation (Köster, *Structure of Coset Models*, arXiv
    math-ph/0308031, writes the separation itself as `Ī₁ ⊂ I₂`). -/
scoped infixl:50 " ⋐ " => ProperContainment.ProperlyContained

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [ProperContainment K]

/-- Proper containment implies containment (dot-notation form). -/
lemma ProperlyContained.le {O₁ O₂ : K} (h : O₁ ⋐ O₂) : O₁ ≤ O₂ :=
  le_of_properlyContained h

/-- Proper containment survives shrinking the inner region and enlarging the outer one
    (dot-notation form). -/
lemma ProperlyContained.mono {O₀ O₁ O₂ O₃ : K} (h₀ : O₀ ≤ O₁) (h : O₁ ⋐ O₂)
    (h₃ : O₂ ≤ O₃) : O₀ ⋐ O₃ :=
  properlyContained_mono h₀ h h₃

/-- The causal collar of a proper containment (dot-notation form). -/
lemma ProperlyContained.exists_orthogonal {O₁ O₂ : K} (h : O₁ ⋐ O₂) :
    ∃ O₃, O₃ ≤ O₂ ∧ O₁ ⟂ O₃ ∧ ¬ O₃ ≤ O₁ :=
  exists_orthogonal_of_properlyContained h

/-- **Proper containment is irreflexive**: no region is properly contained in itself. This is the
    content of the collar's nondegeneracy clause — a collar inside `O` that is not contained in
    `O` cannot exist — and it is what the literature's `Ī₁ ⊂ I₂` typography encodes. -/
lemma irrefl (O : K) : ¬ (O ⋐ O) := by
  rintro h
  obtain ⟨_, hle, -, hnle⟩ := h.exists_orthogonal
  exact hnle hle

/-- A properly contained region is not above its container. -/
lemma ProperlyContained.not_ge {O₁ O₂ : K} (h : O₁ ⋐ O₂) : ¬ O₂ ≤ O₁ :=
  fun hge => irrefl O₁ (h.mono le_rfl hge)

/-- **Proper containment is strict**: `O₁ ⋐ O₂` implies `O₁ < O₂`. -/
lemma ProperlyContained.lt {O₁ O₂ : K} (h : O₁ ⋐ O₂) : O₁ < O₂ :=
  lt_of_le_not_ge h.le h.not_ge

/-- **On lattice regions the collar clause says only that `O₂` is not below `O₁`.** In a
    generalized Boolean algebra of regions — `Finset α` or `Set α` — the difference `O₂ \ O₁` is a
    region disjoint from `O₁`, so it witnesses the collar (with `⟂ = Disjoint`) as soon as it is
    not below `O₁`; conversely a collar inside `O₂` that is not inside `O₁` forbids `O₂ ≤ O₁`.

    This is worth stating because it bounds what the `ProperContainment` axioms can be asked to
    do. On a lattice index set they pin down strictness and nothing more: they do **not** by
    themselves exclude *touching* pairs such as `{0} ⋐ {0, 1}`, which the literature does exclude
    (a pair of local algebras of touching regions is not statistically independent, hence not
    split — Buchholz's *Product states for local algebras* records that postulating normal product
    states for touching regions already yields contradictions for the free field, the corpus's one
    statement that the closure separation is *necessary*).
    Genuine separation is therefore the model's job, not the class's — see `ofThicken`,
    whose thickening operator supplies a buffer layer between `O₁` and the collar. -/
lemma exists_disjoint_iff_not_le {I : Type*} [GeneralizedBooleanAlgebra I] {O₁ O₂ : I} :
    (∃ O₃, O₃ ≤ O₂ ∧ Disjoint O₁ O₃ ∧ ¬ O₃ ≤ O₁) ↔ ¬ O₂ ≤ O₁ := by
  constructor
  · rintro ⟨O₃, hle, -, hnle⟩ hsub
    exact hnle (hle.trans hsub)
  · refine fun hns => ⟨O₂ \ O₁, sdiff_le, disjoint_sdiff_self_right, fun hsub => hns ?_⟩
    simpa using sdiff_le_iff.1 hsub

/-- Proper containment of lattice regions from a **thickening operator** (e.g. the
    `r`-neighbourhood for a metric or graph structure on the sites): `O₁ ⋐ O₂` iff the thickening
    of `O₁` lies strictly below `O₂`. The regions form a generalized Boolean algebra — `Finset α`
    or `Set α` — whose disjoint regions are causally orthogonal (`orthogonal_of_disjoint`). The
    thickening need only be monotone and enlarging (`O ≤ thicken O`); strict enlargement is not
    asked, since it fails at a top region such as `Set.univ`.

    What the construction buys is the chain `O₁ ≤ thicken O₁ < O₂` under `O₁ ⋐ O₂`, with the
    collar `O₂ \ thicken O₁` disjoint from the whole of `thicken O₁` rather than merely from `O₁`:
    the collar is separated from `O₁` *by the thickening's own notion of nearness*.

    Whether that is geometric separation is the thickening's business and is **not** a consequence
    of the two hypotheses. The one-sided `thicken Λ = Λ ∪ Λ.image (· + 1)` on `Finset ℤ` is monotone
    and enlarging, yet `{0} ⋐ {-1, 0, 1, 2}` has collar `{-1, 2}`, which touches `{0}` from below. A
    thickening that is a genuine neighbourhood operator — enlarging in *every* direction of
    adjacency, as the 1-neighbourhood `ProperContainment.nbhd` of the integer chain is in
    `QuantumSystem.Physics.LocalNet.Examples`, or the metric `Metric.cthickening` of
    `ProperContainment.ofCThickening` in `QuantumSystem.Physics.LocalNet.InfiniteRegion` — does
    exclude *touching* pairs, which is the exclusion the literature's `Ī₁ ⊂ I₂` typography performs
    and one the class axioms alone cannot perform on a lattice (`exists_disjoint_iff_not_le`). The
    identity thickening gives back exactly the degenerate model `ofLT`. -/
@[reducible] def ofThicken {I : Type*} [GeneralizedBooleanAlgebra I] [CausalOrthogonality I]
    (orthogonal_of_disjoint : ∀ ⦃O₁ O₂ : I⦄, Disjoint O₁ O₂ → O₁ ⟂ O₂) (thicken : I → I)
    (le_thicken : ∀ O, O ≤ thicken O) (thicken_mono : Monotone thicken) :
    ProperContainment I where
  ProperlyContained O₁ O₂ := thicken O₁ < O₂
  le_of_properlyContained O₁ _ h := (le_thicken O₁).trans h.le
  properlyContained_mono _ _ _ _ h₀ h h₃ := ((thicken_mono h₀).trans_lt h).trans_le h₃
  exists_orthogonal_of_properlyContained O₁ _ h := by
    obtain ⟨O₃, hle, hd, hnle⟩ := exists_disjoint_iff_not_le.2 h.not_ge
    exact ⟨O₃, hle, orthogonal_of_disjoint (hd.mono_left (le_thicken O₁)),
      fun h₃ => hnle (h₃.trans (le_thicken O₁))⟩

/-- **Strict containment already satisfies the axioms**, on any lattice index set and with no
    structure on the sites: containment and monotonicity are immediate, and `O₂ \ O₁` is a collar
    (`exists_disjoint_iff_not_le`). So nothing in the class *prevents* a canonical lattice
    instance — what it fails to deliver is separation, and this model is the witness of that
    failure: on `Finset ℤ` it admits the *touching* pair `{0} ⋐ {0, 1}`, whose local algebras the
    literature records as not statistically independent, hence not split. It is `ofThicken` at the
    identity thickening.

    The type is explicit (`I`, not the section's `K`) so that the section's `[ProperContainment K]`
    is not captured. Deliberately a `def` rather than an `instance`, and never activated anywhere:
    it exists to exhibit the gap, not to be used. A model that wants separation supplies a
    thickening operator (`ofThicken`). -/
@[reducible] def ofLT (I : Type*) [GeneralizedBooleanAlgebra I] [CausalOrthogonality I]
    (orthogonal_of_disjoint : ∀ ⦃O₁ O₂ : I⦄, Disjoint O₁ O₂ → O₁ ⟂ O₂) :
    ProperContainment I where
  ProperlyContained O₁ O₂ := O₁ < O₂
  le_of_properlyContained _ _ h := le_of_lt h
  properlyContained_mono _ _ _ _ h₀ h h₃ := (h₀.trans_lt h).trans_le h₃
  exists_orthogonal_of_properlyContained _ _ h := by
    obtain ⟨O₃, hle, hd, hnle⟩ := exists_disjoint_iff_not_le.2 h.not_ge
    exact ⟨O₃, hle, orthogonal_of_disjoint hd, hnle⟩

end ProperContainment

/-! ### Nets of von Neumann algebras

The split property is a statement about a net of *von Neumann* algebras, and it is stated here at
that level, for a `VonNeumannNet` over a bare causal index set (the definition, and why
non-directed index sets such as the proper intervals of `S¹` must be in scope, are in
`QuantumSystem.Physics.LocalNet.VonNeumannNet`). The net of local von Neumann algebras of a
representation of the quasi-local C⋆-algebra is one instance (`LocalNet.vonNeumannNet`), and
`LocalNet.SplitProperty` is this property at that instance.
-/

open scoped ProperContainment VonNeumannAlgebra

namespace VonNeumannNet

variable {K : Type*} [Preorder K] [CausalOrthogonality K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The split property** of a net of von Neumann algebras (Buchholz; Doplicher–Longo): for every
    properly contained pair of regions `O₁ ⋐ O₂`, some type I factor interpolates between the
    local algebras, `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O₂)`. This is genuinely model-dependent input — it fails for
    nets without the requisite phase-space (nuclearity) behaviour — and it is relative to the
    chosen proper containment `⋐` (see `ProperContainment`).

    That relativity is strong: neither an empty `⋐` nor a merely inhabited one gives the property
    content. On lattice regions `Λ₁ ⋐ Λ₂ :↔ Λ₁ = ∅ ∧ Λ₂.Nonempty` satisfies every axiom of
    `ProperContainment` and relates the pair `∅ ⋐ {0}`, yet under it the property only ever asks
    `𝓡(∅) ≤ 𝓡(Λ)` to split. The property says something about a net only through the genuine
    pairs the model's `⋐` relates. On the integer chain these include
    `ProperContainment.properlyContained_singleton`, and there the property is not automatic:
    `LocalNet.Examples.not_splitProperty_diagonalNet` refutes it for a constant net.

    This is the *nested* form. The historically original *commutant* form is
    `SplitProperty.isSplitPair`, which follows from this one through locality; the converse needs
    Haag duality and is not available here. The gap-free pair form `IsSplitPair` is stated
    separately, since no properly contained pair can produce it. -/
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

/-- **A split pair of regions**: a type I factor interpolates between the algebra of `O₁` and the
    commutant of the algebra of `O₂`,

      `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O₂)′`.

    No proper containment and no gap between the regions is involved. This is the form in which
    Matsui states the half-chain split property of a spin chain, for the adjacent half-chains
    `(-∞, 0]` and `[1, ∞)`, and the disjoint-pair form of Buchholz's *Product states for local
    algebras*. For causally orthogonal regions the inclusion `𝓡(O₁) ≤ 𝓡(O₂)′` itself holds by
    locality (`algebra_le_commutant_of_orthogonal`), so the content is the interpolating factor.

    The relation is symmetric (`IsSplitPair.symm`): taking commutants turns the chain into
    `𝓡(O₂) ≤ 𝔑′ ≤ 𝓡(O₁)′`, and the commutant of a type I factor is a type I factor
    (`VonNeumannAlgebra.IsTypeIFactor.commutant`). -/
def IsSplitPair (vnNet : VonNeumannNet K H) (O₁ O₂ : K) : Prop :=
  VonNeumannAlgebra.IsSplitInclusion (vnNet.algebra O₁) (vnNet.algebra O₂)′

/-- A split pair is in particular a commuting pair: `𝓡(O₁) ≤ 𝓡(O₂)′`. -/
lemma IsSplitPair.le {vnNet : VonNeumannNet K H} {O₁ O₂ : K} (h : vnNet.IsSplitPair O₁ O₂) :
    vnNet.algebra O₁ ≤ (vnNet.algebra O₂)′ :=
  VonNeumannAlgebra.IsSplitInclusion.le h

/-- **Split pairs are symmetric.** If `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O₂)′` for a type I factor `𝔑`, then
    `𝓡(O₂) ≤ 𝔑′ ≤ 𝓡(O₁)′`, and `𝔑′` is a type I factor
    (`VonNeumannAlgebra.IsSplitInclusion.commutant`). -/
lemma IsSplitPair.symm {vnNet : VonNeumannNet K H} {O₁ O₂ : K} (h : vnNet.IsSplitPair O₁ O₂) :
    vnNet.IsSplitPair O₂ O₁ := by
  have := VonNeumannAlgebra.IsSplitInclusion.commutant h
  rwa [VonNeumannAlgebra.commutant_commutant] at this

/-- The split-pair relation is symmetric. -/
lemma isSplitPair_comm {vnNet : VonNeumannNet K H} {O₁ O₂ : K} :
    vnNet.IsSplitPair O₁ O₂ ↔ vnNet.IsSplitPair O₂ O₁ :=
  ⟨IsSplitPair.symm, IsSplitPair.symm⟩

/-- Splitness of a pair survives shrinking either region. -/
lemma IsSplitPair.mono {vnNet : VonNeumannNet K H} {O₁ O₂ O₁' O₂' : K} (h₁ : O₁' ≤ O₁)
    (h₂ : O₂' ≤ O₂) (h : vnNet.IsSplitPair O₁ O₂) : vnNet.IsSplitPair O₁' O₂' :=
  VonNeumannAlgebra.IsSplitInclusion.mono (vnNet.algebra_mono h₁)
    (VonNeumannAlgebra.commutant_le (vnNet.algebra_mono h₂)) h

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
    `O_B` causally orthogonal to `O₂`, the pair `(O₁, O_B)` is split (`IsSplitPair`),

      `𝓡(O₁) ≤ 𝔑 ≤ 𝓡(O_B)′`.

    This is the historically original shape of the property, for a *disjoint* pair with slack
    rather than a nested one. The nested form implies it through locality
    (`algebra_le_commutant_of_orthogonal`); the converse needs Haag duality, which is not assumed
    anywhere here. Buchholz displays the symmetric four-term chain `𝓡(O₁) ⊂ M₁ ⊂ M₂′ ⊂ 𝓡(O₂)′`
    with two interpolating type I factors; this is its one-sided compression, which is the form
    the adopted definition of a split inclusion carries.

    The pair obtained this way always has the gap `O₂` between `O₁` and `O_B`. Since `⋐` is
    irreflexive, adjacent pairs such as Matsui's half-chains are out of its reach; for them
    `IsSplitPair` is the property itself, not a consequence. -/
theorem SplitProperty.isSplitPair (hs : vnNet.SplitProperty) {O₁ O₂ O_B : K}
    (h : O₁ ⋐ O₂) (hd : O₂ ⟂ O_B) : vnNet.IsSplitPair O₁ O_B :=
  (hs h).mono le_rfl (vnNet.algebra_le_commutant_of_orthogonal hd)

end VonNeumannNet

namespace LocalNet

open scoped ProperContainment VonNeumannAlgebra

section LocalAlgebras

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : LocalNet K) [N.Faithful]

/-- **The split property** of a local net in a representation `π` of the quasi-local C⋆-algebra
    (Buchholz; Doplicher–Longo): the split property of the associated net of local von Neumann
    algebras (`VonNeumannNet.SplitProperty`) — for every properly contained pair of regions
    `O₁ ⋐ O₂`, some type I factor interpolates, `𝓡(O₁) ≤ M ≤ 𝓡(O₂)`. It is relative to the chosen
    `⋐` exactly as the von-Neumann-net property is; an inhabited `⋐` alone does not give it
    content (see `VonNeumannNet.SplitProperty`).

    The property itself is defined at the von-Neumann-net level, where it needs neither a
    directed index set nor a quasi-local C⋆-algebra; the hypotheses `[IsDirectedOrder K]`,
    `[Nonempty K]` and `[N.Faithful]` here are the cost of *this instance*, whose local algebras
    are built from a representation of the quasi-local C⋆-algebra. Nets over non-directed index
    sets are stated through `VonNeumannNet.SplitProperty` directly.

    This is an `abbrev`, so the consequences `VonNeumannNet.SplitProperty.isSplitInclusion`,
    `VonNeumannNet.SplitProperty.isSplitInclusion_of_le_of_properlyContained_of_le` and
    `VonNeumannNet.SplitProperty.isSplitPair` apply to `hs : N.SplitProperty R` directly (also by
    dot notation), and are not restated here. -/
abbrev SplitProperty [ProperContainment K] (R : CStarRep N.quasiLocalCStarAlgebra) : Prop :=
  (N.vonNeumannNet R).SplitProperty

end LocalAlgebras

end LocalNet
