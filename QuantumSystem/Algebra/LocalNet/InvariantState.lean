module

public import QuantumSystem.Algebra.LocalNet.GroupAction

/-!
# `G`-invariant density matrices on a `LocalNet`

Defines the `G`-invariance predicate for density matrices on a region `Λ` (when
`g · Λ = Λ`) and a vacuum-style specialisation for the global region
`Finset.univ`. The maximally-mixed state `π = I / d` is shown to be
`G`-invariant for any group action — a sample inhabitant verifying that the
invariance predicate is non-empty (Verch 2025 §1.2 axiom (iv) precondition).

## Main definitions

* `LocalNet.IsGroupInvariantStateAt` — invariance Prop for a `densityMatrix Λ`
  under `α_g` (conditional on `g · Λ = Λ`).
* `LocalNet.IsGroupInvariantVacuum` — specialisation to global `Λ = Finset.univ`.
* `LocalNet.maximallyMixed_isGroupInvariantVacuum` — sample: `π` is invariant.

## References

* Verch 2025 (`https://arxiv.org/abs/2507.00900`) §1.2 axiom (iv)
-/

@[expose] public section

namespace LocalNet

variable (L : LocalNet)

/-- **`g`-invariance condition** for a state on region `Λ`. The state `ρ` is
    `G`-invariant if for every `g : G` whose action fixes `Λ` (`g · Λ = Λ`),
    transporting `ρ.toMatrix` along `α_g` and then back via `regionIdxCongr`
    leaves `ρ` unchanged. -/
def IsGroupInvariantStateAt {G : Type*} [Group G]
    (act : L.HasGroupAction G) {Λ : Finset L.sites}
    (ρ : L.densityMatrix Λ) : Prop :=
  ∀ (g : G) (hg : act.regionImage g Λ = Λ),
    (L.algebraAut act g Λ ρ.toMatrix).submatrix
        (L.regionIdxCongr hg).symm (L.regionIdxCongr hg).symm = ρ.toMatrix

/-- **`G`-invariant vacuum**: a global density matrix that is `α_g`-invariant
    for every `g`. The condition `g · Λ = Λ` is automatic for `Λ = Finset.univ`
    since `act.siteAction g` is a bijection.
    Requires `[Fintype L.sites]` for `Finset.univ` to be available. -/
def IsGroupInvariantVacuum [Fintype L.sites] {G : Type*} [Group G]
    (act : L.HasGroupAction G) (ρ : L.densityMatrix (Finset.univ : Finset L.sites)) :
    Prop :=
  ∀ g : G,
    have hg : act.regionImage g (Finset.univ : Finset L.sites) = Finset.univ :=
      Finset.image_univ_of_surjective (act.siteAction g).surjective
    (L.algebraAut act g Finset.univ ρ.toMatrix).submatrix
        (L.regionIdxCongr hg).symm (L.regionIdxCongr hg).symm = ρ.toMatrix

/-- **Sample `G`-invariant vacuum**: the maximally-mixed state `π = I / d` is
    `α_g`-invariant on every `LocalNet` for any group action. The proof relies
    on `algebraAut` being a `*`-algebra equivalence (so it preserves `1` and the
    `ℂ`-action) and on `Matrix.submatrix_one_equiv` (the identity matrix is
    invariant under reindexing along an `Equiv`). Verifies that
    `IsGroupInvariantVacuum` is non-empty on every `LocalNet` with non-empty
    local Hilbert spaces. -/
theorem maximallyMixed_isGroupInvariantVacuum
    [Fintype L.sites] {G : Type*} [Group G] (act : L.HasGroupAction G)
    [∀ s, Nonempty (L.localIdx s)] :
    L.IsGroupInvariantVacuum act
      (DensityMatrix.maximallyMixed
        (n := L.regionIdx (Finset.univ : Finset L.sites))) := by
  intro g
  rw [DensityMatrix.maximallyMixed_toMatrix, map_smul, map_one]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply]

end LocalNet
