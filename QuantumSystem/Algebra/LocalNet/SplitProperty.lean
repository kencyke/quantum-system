module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra
public import QuantumSystem.Algebra.CStarAlgebra.Representation
public import QuantumSystem.Algebra.VonNeumannAlgebra.SplitInclusion

/-!
# The split property of a local net

The **split property** of a local net, in the form of Buchholz (*Product states for local
algebras*, Comm. Math. Phys. 36, 1974) and Doplicher–Longo (*Standard and split inclusions of
von Neumann algebras*, Invent. Math. 75, 1984): fix a representation `π` of the quasi-local
C⋆-algebra on a Hilbert space and form the **local von Neumann algebras**

  `𝓡(O) = π(𝔄(O))″`  (`LocalNet.localVonNeumannAlgebra`);

the net has the split property when, for every properly contained pair of regions `O₁ ⋐ O₂`, the
inclusion `𝓡(O₁) ≤ 𝓡(O₂)` is a split inclusion — some type I factor interpolates
(`VonNeumannAlgebra.IsSplitInclusion`).

Proper containment `⋐` (`ProperContainment`) is the abstract form of the geometric relation
"the closure of `O₁` lies in the interior of `O₂`" of the QFT literature; on a causal index set
it is model-dependent geometric input, like the causal orthogonality `⟂` itself. The class only
axiomatises necessary conditions (containment, monotonicity, and a causal collar inside the outer
region); it is *not* a complete axiomatisation of properness — e.g. on lattice regions, where the
empty region is orthogonal to everything, plain containment `⊆` also satisfies the axioms — so
the split property is always relative to the chosen `⋐`. Unlike `CausalOrthogonality (Finset α)`,
there is no canonical `ProperContainment` instance on lattice regions: a genuine collar needs a
metric or graph structure on the sites, supplied e.g. through `ProperContainment.ofThicken`.

Because the quasi-local algebra requires a directed index set, this formulation states the split
property for directed `K` only (Buchholz's double-cone setting); split inclusions of local
algebras over non-directed families (e.g. wedges) can still be stated pointwise through
`VonNeumannAlgebra.IsSplitInclusion`. The representation is not assumed nondegenerate — for
degenerate representations the property can hold trivially, as in the literature, and substantive
downstream theorems impose nondegeneracy or cyclicity where they need it.

## Main definitions and results

* `ProperContainment` — the proper-containment relation `O₁ ⋐ O₂` on a causal index set.
* `LocalNet.localVonNeumannAlgebra` — the local von Neumann algebra `𝓡(O) = π(𝔄(O))″` of a
  region in a representation of the quasi-local algebra, with isotony
  (`localVonNeumannAlgebra_mono`) and locality
  (`localVonNeumannAlgebra_le_commutant_of_orthogonal`).
* `LocalNet.SplitProperty` — the split property of the net in the representation.
* `LocalNet.SplitProperty.isSplitInclusion` — the split inclusion of a properly contained pair;
  Buchholz's tensor splitting between properly separated regions follows by applying
  `VonNeumannAlgebra.IsSplitInclusion.exists_tensorDecomposition` to it.
-/

@[expose] public section

open scoped CausalOrthogonality

/-- **Proper containment of regions**: the abstract form of the relation `O₁ ⋐ O₂` ("the closure
    of `O₁` lies in the interior of `O₂`") under which the split property of a local net is
    stated. This is model-dependent geometric input on the causal index set, like `⟂` itself.

    The axioms are necessary conditions, not a complete axiomatisation of properness: containment,
    monotonicity under shrinking the inner and enlarging the outer region, and a **causal collar**
    — the outer region contains a region causally orthogonal to the inner one
    (`exists_orthogonal_of_properlyContained`). On the Haag–Kastler index set of nonempty double
    cones the collar axiom expresses genuine properness; on index sets with a region orthogonal
    to everything (such as the empty lattice region) it is weaker, and plain containment also
    satisfies the axioms — the split property is therefore always relative to the chosen `⋐`. -/
class ProperContainment (K : Type*) [Preorder K] [CausalOrthogonality K] where
  /-- The proper-containment relation `O₁ ⋐ O₂` on regions. -/
  ProperlyContained : K → K → Prop
  /-- Proper containment implies containment. -/
  le_of_properlyContained : ∀ ⦃O₁ O₂ : K⦄, ProperlyContained O₁ O₂ → O₁ ≤ O₂
  /-- Proper containment survives shrinking the inner region and enlarging the outer one. -/
  properlyContained_mono : ∀ ⦃O₀ O₁ O₂ O₃ : K⦄, O₀ ≤ O₁ → ProperlyContained O₁ O₂ → O₂ ≤ O₃ →
      ProperlyContained O₀ O₃
  /-- **Causal collar**: a properly containing region contains a region causally orthogonal to
      the inner one. -/
  exists_orthogonal_of_properlyContained : ∀ ⦃O₁ O₂ : K⦄, ProperlyContained O₁ O₂ →
      ∃ O₃, O₃ ≤ O₂ ∧ O₁ ⟂ O₃

namespace ProperContainment

/-- `O₁ ⋐ O₂` : the region `O₁` is properly contained in `O₂`. -/
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
    ∃ O₃, O₃ ≤ O₂ ∧ O₁ ⟂ O₃ :=
  exists_orthogonal_of_properlyContained h

/-- Proper containment of lattice regions from a **thickening operator** (e.g. the
    `r`-neighbourhood for a metric or graph structure on the sites): `Λ₁ ⋐ Λ₂` iff the
    thickening of `Λ₁` still lies in `Λ₂`. The causal collar is the genuine one,
    `Λ₂ \ thicken Λ₁`. -/
@[reducible] def ofThicken {α : Type*} [DecidableEq α] (thicken : Finset α → Finset α)
    (subset_thicken : ∀ Λ, Λ ⊆ thicken Λ) (thicken_mono : Monotone thicken) :
    ProperContainment (Finset α) where
  ProperlyContained Λ₁ Λ₂ := thicken Λ₁ ⊆ Λ₂
  le_of_properlyContained _ _ h := (subset_thicken _).trans h
  properlyContained_mono _ _ _ _ h₀ h h₃ := ((thicken_mono h₀).trans h).trans h₃
  exists_orthogonal_of_properlyContained Λ₁ Λ₂ _ :=
    ⟨Λ₂ \ thicken Λ₁, Finset.sdiff_subset,
      Finset.disjoint_sdiff.mono_left (subset_thicken Λ₁)⟩

end ProperContainment

namespace LocalNet

open scoped ProperContainment VonNeumannAlgebra

section LocalAlgebras

variable {K : Type*} [PartialOrder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : LocalNet K) [N.Faithful]

/-- The **local von Neumann algebra** `𝓡(O) = π(𝔄(O))″` of a region in a representation of the
    quasi-local C⋆-algebra: the von Neumann algebra generated by the image of the local algebra.
    The generating set is star-closed (`𝔄(O)` is star-closed, and the embedding and `π` are
    `*`-maps), so `VonNeumannAlgebra.generated` — which symmetrizes in general — is literally the
    double commutant `π(𝔄(O))″` here. Since `π` is a possibly non-unital `*`-homomorphism,
    `𝓡(O)` always contains `1` even when `π(𝔄(O))` does not, matching the `″` convention. -/
noncomputable def localVonNeumannAlgebra (R : CStarRep N.quasiLocalCStarAlgebra) (O : K) :
    VonNeumannAlgebra R.H :=
  VonNeumannAlgebra.generated (Set.range fun a : N.algebra O => R.π (N.ιLocalCStar O a))

/-- Local observables are represented inside the local von Neumann algebra of their region. -/
lemma π_ιLocalCStar_mem_localVonNeumannAlgebra (R : CStarRep N.quasiLocalCStarAlgebra) (O : K)
    (a : N.algebra O) : R.π (N.ιLocalCStar O a) ∈ N.localVonNeumannAlgebra R O :=
  VonNeumannAlgebra.mem_generated_of_mem ⟨a, rfl⟩

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

/-- **The split property** of a local net in a representation `π` of the quasi-local C⋆-algebra
    (Buchholz; Doplicher–Longo): for every properly contained pair of regions `O₁ ⋐ O₂`, some
    type I factor interpolates between the local von Neumann algebras,
    `𝓡(O₁) ≤ M ≤ 𝓡(O₂)`. This is genuinely model-dependent input — it fails for nets without
    the requisite phase-space (nuclearity) behaviour — and it is relative to the chosen proper
    containment `⋐` (see `ProperContainment`). -/
def SplitProperty [ProperContainment K] (R : CStarRep N.quasiLocalCStarAlgebra) : Prop :=
  ∀ ⦃O₁ O₂ : K⦄, O₁ ⋐ O₂ →
    VonNeumannAlgebra.IsSplitInclusion
      (N.localVonNeumannAlgebra R O₁) (N.localVonNeumannAlgebra R O₂)

end LocalAlgebras

section SplitConsequences

variable {K : Type*} [PartialOrder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable [ProperContainment K] {N : LocalNet K} [N.Faithful]
variable {R : CStarRep N.quasiLocalCStarAlgebra}

/-- The split property extends to enlarged pairs: if `O₀ ≤ O₁ ⋐ O₂ ≤ O₃` then the inclusion
    `𝓡(O₀) ≤ 𝓡(O₃)` is split as well. -/
lemma SplitProperty.isSplitInclusion_of_le_of_le (hs : N.SplitProperty R)
    {O₀ O₁ O₂ O₃ : K} (h₀ : O₀ ≤ O₁) (h : O₁ ⋐ O₂) (h₃ : O₂ ≤ O₃) :
    VonNeumannAlgebra.IsSplitInclusion
      (N.localVonNeumannAlgebra R O₀) (N.localVonNeumannAlgebra R O₃) :=
  hs (h.mono h₀ h₃)

/-- **Buchholz's tensor splitting between properly separated regions**, in split-inclusion form:
    under the split property, every properly contained pair `O₁ ⋐ O₂` yields the split inclusion
    `𝓡(O₁) ≤ 𝓡(O₂)`, whose full tensor splitting — a unitary `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` carrying
    `𝓡(O₁)` into the tensor factor `B(ℓ²(F)) ⊗̄ 1` and the dual algebra `𝓡(O₂)′` into
    `1 ⊗̄ B(eH)`, with the interpolating type I factor and its commutant identified exactly — is
    obtained by applying `VonNeumannAlgebra.IsSplitInclusion.exists_tensorDecomposition` to the
    conclusion. (The instantiated existential is deliberately not restated here: spelling it out
    over `R.H` forces the elaborator to unfold the quasi-local algebra inside `R`'s type, while
    consuming the general statement through this corollary is cheap.) -/
theorem SplitProperty.isSplitInclusion (hs : N.SplitProperty R) {O₁ O₂ : K} (h : O₁ ⋐ O₂) :
    VonNeumannAlgebra.IsSplitInclusion
      (N.localVonNeumannAlgebra R O₁) (N.localVonNeumannAlgebra R O₂) :=
  hs h

end SplitConsequences

end LocalNet
