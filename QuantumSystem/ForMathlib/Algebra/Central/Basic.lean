/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Central.Basic

/-!
# Central algebras across universes

Mathlib's `Algebra.IsCentral.of_algEquiv` transfers centrality along an algebra isomorphism
`D ≃ₐ[K] D'` between algebras in one universe. The proof does not use that restriction; this file
states it for algebras in any universes, as needed for operator algebras on Hilbert spaces in
different universes.

## Main results

* `Algebra.IsCentral.of_algEquiv'` — a central algebra is carried to a central algebra by an
  algebra isomorphism, in any universes.
* `Algebra.IsCentral.iff_of_algEquiv` — two isomorphic algebras are central together.

## TODO

Upstream both lemmas: generalise `Algebra.IsCentral.of_algEquiv` in Mathlib to algebras in
different universes, which retires `of_algEquiv'`, and add the iff form, which Mathlib lacks.
-/

@[expose] public section

namespace Algebra.IsCentral

variable {K D D' : Type*} [CommSemiring K] [Semiring D] [Algebra K D] [Semiring D'] [Algebra K D']

/-- **A central algebra is carried to a central algebra by an algebra isomorphism**, between
algebras in any universes. -/
lemma of_algEquiv' [h : IsCentral K D] (e : D ≃ₐ[K] D') : IsCentral K D' where
  out x hx :=
    have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

/-- Two algebras isomorphic over `K` are central together. -/
lemma iff_of_algEquiv (e : D ≃ₐ[K] D') : IsCentral K D ↔ IsCentral K D' :=
  ⟨fun _ => of_algEquiv' e, fun _ => of_algEquiv' e.symm⟩

end Algebra.IsCentral
