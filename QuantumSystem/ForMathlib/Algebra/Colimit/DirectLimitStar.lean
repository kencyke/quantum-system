module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Star.Basic

/-!
# Star and algebra structure on a direct limit

The direct limit of a directed system of `*`-rings (resp. `𝕜`-algebras) with `*`-homomorphism
(resp. algebra-homomorphism) connecting maps is again a `*`-ring (resp. `𝕜`-algebra), with the
operations acting componentwise. Mathlib already provides the `Ring`/`Module` structure on
`DirectLimit`; this file adds the `Star`, `StarRing`, `Algebra` and `StarModule` instances.

These are general facts about direct limits and are candidates for upstreaming to Mathlib.
-/

@[expose] public section

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {F : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (F i) (F j)] [DirectedSystem F (f · · ·)]
variable [IsDirectedOrder ι]

section Star

variable [∀ i, Star (F i)] [∀ i j (h : i ≤ j), StarHomClass (T h) (F i) (F j)]

/-- Componentwise involution on a direct limit of `*`-magmas. -/
noncomputable instance : Star (DirectLimit F f) where
  star := DirectLimit.map (F₁ := F) (F₂ := F) f f (fun _ => star)
    (fun _ _ h x => map_star (f _ _ h) x)

@[simp] lemma star_mk (i) (x : F i) :
    star (⟦⟨i, x⟩⟧ : DirectLimit F f) = ⟦⟨i, star x⟩⟧ := rfl

end Star

section StarRing

variable [Nonempty ι] [∀ i, Ring (F i)] [∀ i, StarRing (F i)]
  [∀ i j (h : i ≤ j), RingHomClass (T h) (F i) (F j)]
  [∀ i j (h : i ≤ j), StarHomClass (T h) (F i) (F j)]

/-- The direct limit of a directed system of `*`-rings is a `*`-ring. -/
noncomputable instance : StarRing (DirectLimit F f) where
  star_involutive z := by
    induction z using DirectLimit.induction with
    | _ i x => simp only [star_mk, star_star]
  star_mul a b := by
    induction a, b using DirectLimit.induction₂ with
    | _ i x y => simp only [DirectLimit.mul_def, star_mk, star_mul]
  star_add a b := by
    induction a, b using DirectLimit.induction₂ with
    | _ i x y => simp only [DirectLimit.add_def, star_mk, star_add]

end StarRing

section Algebra

variable {𝕜 : Type*} [Nonempty ι] [CommSemiring 𝕜] [∀ i, Semiring (F i)] [∀ i, Algebra 𝕜 (F i)]
  [∀ i j (h : i ≤ j), RingHomClass (T h) (F i) (F j)]
  [∀ i j (h : i ≤ j), LinearMapClass (T h) 𝕜 (F i) (F j)]

/-- The direct limit of a directed system of `𝕜`-algebras is a `𝕜`-algebra. -/
noncomputable instance : Algebra 𝕜 (DirectLimit F f) :=
  Algebra.ofModule
    (fun _ a b => by
      induction a, b using DirectLimit.induction₂ with
      | _ i x y => simp only [DirectLimit.smul_def, DirectLimit.mul_def, smul_mul_assoc])
    (fun _ a b => by
      induction a, b using DirectLimit.induction₂ with
      | _ i x y => simp only [DirectLimit.smul_def, DirectLimit.mul_def, mul_smul_comm])

end Algebra

section StarModule

variable {𝕜 : Type*} [Nonempty ι] [CommSemiring 𝕜] [Star 𝕜] [∀ i, Semiring (F i)]
  [∀ i, Algebra 𝕜 (F i)] [∀ i, Star (F i)] [∀ i, StarModule 𝕜 (F i)]
  [∀ i j (h : i ≤ j), LinearMapClass (T h) 𝕜 (F i) (F j)]
  [∀ i j (h : i ≤ j), StarHomClass (T h) (F i) (F j)]

/-- The involution on a direct limit of `𝕜`-`*`-algebras is conjugate-linear. -/
instance : StarModule 𝕜 (DirectLimit F f) where
  star_smul c z := by
    induction z using DirectLimit.induction with
    | _ i x => simp only [DirectLimit.smul_def, star_mk, star_smul]

end StarModule

end DirectLimit
