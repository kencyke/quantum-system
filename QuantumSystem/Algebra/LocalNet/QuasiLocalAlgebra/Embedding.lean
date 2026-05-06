module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.GlobalHilbert
public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Hilbert

/-!
# Region tuple extensions for the global Hilbert space (Phase 5'a step 4)

Following Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2 §2.7.2, we extend
each region tuple `f : (s : Λ) → localIdx s` to a global tuple by filling
outside-`Λ` coordinates with the chosen reference basis index.  The
resulting `extendRegionTuple` and its companion lemmas are consumed by
`LocalEmbed.lean` to characterise the matrix elements of `localEmbed Λ`.

## Main definitions

* `LocalNetLike.extendRegionTuple Λ f` — extension of a region tuple to a
  global tuple by filling outside-`Λ` coordinates with `referenceBasis L`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- Equality on `globalIdx L` is classically decidable; we register this as a
noncomputable instance so that `lp.single 2 (· : globalIdx L) 1` is well-typed
downstream. -/
noncomputable instance instDecidableEqGlobalIdx : DecidableEq (globalIdx L) :=
  Classical.decEq _

/-- Extension of a region tuple `f : regionIdx Λ` to a global tuple in
`globalIdx L` by filling sites outside `Λ` with the reference basis index. -/
noncomputable def extendRegionTuple (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    globalIdx L :=
  ⟨fun s => if h : s ∈ Λ then f ⟨s, h⟩ else referenceBasis L s,
   ⟨Λ, fun _ hs => dif_neg hs⟩⟩

@[simp]
theorem extendRegionTuple_val_apply_of_mem (Λ : Finset L)
    (f : regionIdx (L := L) Λ) {s : L} (hs : s ∈ Λ) :
    (extendRegionTuple Λ f).val s = f ⟨s, hs⟩ :=
  dif_pos hs

theorem extendRegionTuple_val_apply_of_not_mem (Λ : Finset L)
    (f : regionIdx (L := L) Λ) {s : L} (hs : s ∉ Λ) :
    (extendRegionTuple Λ f).val s = referenceBasis L s :=
  dif_neg hs

/-- The extension `extendRegionTuple Λ` is injective. -/
theorem extendRegionTuple_injective (Λ : Finset L) :
    Function.Injective (extendRegionTuple (L := L) Λ) := by
  intro f g h
  ext ⟨s, hs⟩
  have hval : (extendRegionTuple Λ f).val = (extendRegionTuple Λ g).val :=
    congrArg Subtype.val h
  have := congrFun hval s
  simpa [extendRegionTuple_val_apply_of_mem, hs] using this

end LocalNetLike
