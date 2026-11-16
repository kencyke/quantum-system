/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Extending tensor products over finite sets by reference vectors

Fix a family of modules `A i` over `R`, indexed by `ι`, and a reference vector `ξ i` in each. For
finite sets `s ⊆ t` of indices, the tensor product over `s` maps into the tensor product over `t` by
filling the indices of `t \ s` with the reference vectors:
`⨂_{i ∈ s} m i ↦ (⨂_{i ∈ s} m i) ⊗ (⨂_{j ∈ t \ s} ξ j)`. These maps form a directed system over the
finite sets of indices, whose direct limit is the tensor product of the whole family along `ξ`.
For algebras and `ξ = 1` they are algebra homomorphisms, `x ↦ x ⊗ 1`.

## Main definitions

* `PiTensorProduct.extendFun ξ m` — the family on `t` that is `m` on `s` and `ξ` elsewhere.
* `PiTensorProduct.extend R ξ h` — for `h : s ⊆ t`, the linear map
  `(⨂[R] i : s, A i) →ₗ[R] ⨂[R] i : t, A i` filling `t \ s` with `ξ`.
* `PiTensorProduct.extendAlgHom R h` — for algebras, `PiTensorProduct.extend R 1 h` as an algebra
  homomorphism.

## Main results

* `PiTensorProduct.directedSystem`, `PiTensorProduct.directedSystemAlgHom` — the maps form a
  directed system over `Finset ι`.
-/

@[expose] public section

open scoped TensorProduct

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- A product over `s ⊆ t`, as a product over `t` that is `1` off `s`. -/
lemma prod_subtype_eq_prod_ite {M : Type*} [CommMonoid M] {s t : Finset ι} (hst : s ⊆ t)
    (g : t → M) : ∏ i : s, g ⟨i, hst i.2⟩ = ∏ j : t, if (j : ι) ∈ s then g j else 1 :=
  Fintype.prod_of_injective (fun i : s => (⟨i, hst i.2⟩ : t))
    (fun _ _ h => Subtype.ext (congrArg Subtype.val h :)) _ _
    (fun j hj => by
      rw [ite_eq_right_iff]
      exact fun h => absurd ⟨⟨j, h⟩, rfl⟩ hj)
    (fun i => by simp [i.2])

end Finset

namespace PiTensorProduct

variable {ι R : Type*} [CommSemiring R] [DecidableEq ι] {A : ι → Type*}

section Fun

variable (ξ : Π i, A i)

/-- The family on `t` that is `m` on `s` and the reference vector `ξ` on the other indices. -/
def extendFun {s t : Finset ι} (m : Π i : s, A i) : Π i : t, A i :=
  fun j => if h : (j : ι) ∈ s then m ⟨j, h⟩ else ξ j

/-- On the indices of `s`, the extension is `m`. -/
lemma extendFun_apply_of_mem {s t : Finset ι} (m : Π i : s, A i) (j : t) (h : (j : ι) ∈ s) :
    extendFun ξ m j = m ⟨j, h⟩ := by
  simp [extendFun, h]

/-- Off the indices of `s`, the extension is the reference vector. -/
lemma extendFun_apply_of_notMem {s t : Finset ι} (m : Π i : s, A i) (j : t) (h : (j : ι) ∉ s) :
    extendFun ξ m j = ξ j := by
  simp [extendFun, h]

/-- Changing one coordinate of `m` changes the same coordinate of its extension. -/
lemma extendFun_update {s t : Finset ι} (hst : s ⊆ t) [DecidableEq s] [DecidableEq t]
    (m : Π i : s, A i) (i : s) (x : A i) :
    extendFun (t := t) ξ (Function.update m i x) =
      Function.update (extendFun ξ m) ⟨i, hst i.2⟩ x := by
  funext j
  by_cases hj : (j : ι) ∈ s
  · rw [extendFun_apply_of_mem _ _ _ hj]
    by_cases hji : (j : ι) = i
    · obtain ⟨j, hj'⟩ := j
      obtain ⟨i, hi⟩ := i
      simp only at hji
      subst hji
      simp
    · rw [Function.update_of_ne (fun h => hji (congrArg Subtype.val h)),
        Function.update_of_ne (fun h => hji (congrArg Subtype.val h)),
        extendFun_apply_of_mem _ _ _ hj]
  · have hji : j ≠ ⟨i, hst i.2⟩ := fun h => hj (h ▸ i.2)
    rw [extendFun_apply_of_notMem _ _ _ hj, Function.update_of_ne hji,
      extendFun_apply_of_notMem _ _ _ hj]

/-- Extending from `s` to `s` does nothing. -/
lemma extendFun_refl {s : Finset ι} (m : Π i : s, A i) : extendFun (t := s) ξ m = m := by
  funext j
  exact extendFun_apply_of_mem _ _ _ j.2

/-- Extending from `s` to `t` and then to `u` is extending from `s` to `u`. -/
lemma extendFun_extendFun {s t u : Finset ι} (hst : s ⊆ t) (m : Π i : s, A i) :
    extendFun (t := u) ξ (extendFun (t := t) ξ m) = extendFun ξ m := by
  funext j
  by_cases hj : (j : ι) ∈ s
  · simp [extendFun, hj, hst hj]
  · by_cases hj' : (j : ι) ∈ t <;> simp [extendFun, hj, hj']

/-- A product of factors depending on the coordinates of two extensions, each factor being `1` at
the reference vectors, is the product over the smaller set. -/
lemma prod_extendFun₂ {B : ι → Type*} {M : Type*} [CommMonoid M] (ζ : Π i, B i) {s t : Finset ι}
    (hst : s ⊆ t) (g : ∀ j, A j → B j → M) (hg : ∀ j, g j (ξ j) (ζ j) = 1) (m : Π i : s, A i)
    (n : Π i : s, B i) :
    ∏ j : t, g j (extendFun ξ m j) (extendFun ζ n j) = ∏ i : s, g i (m i) (n i) := by
  calc ∏ j : t, g j (extendFun ξ m j) (extendFun ζ n j)
      = ∏ j : t, if (j : ι) ∈ s then g j (extendFun ξ m j) (extendFun ζ n j) else 1 :=
        Finset.prod_congr rfl fun j _ => by
          split_ifs with h
          · rfl
          · rw [extendFun_apply_of_notMem _ _ _ h, extendFun_apply_of_notMem _ _ _ h, hg]
    _ = ∏ i : s, g i (extendFun ξ m ⟨i, hst i.2⟩) (extendFun ζ n ⟨i, hst i.2⟩) :=
        (Finset.prod_subtype_eq_prod_ite hst fun j => g j (extendFun ξ m j) (extendFun ζ n j)).symm
    _ = ∏ i : s, g i (m i) (n i) := Finset.prod_congr rfl fun i _ => by
        rw [extendFun_apply_of_mem ξ m (⟨i, hst i.2⟩ : t) i.2,
          extendFun_apply_of_mem ζ n (⟨i, hst i.2⟩ : t) i.2]

end Fun

section Module

variable [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)] (ξ : Π i, A i)

/-- The multilinear map `m ↦ ⨂ extendFun ξ m`, multilinear since each coordinate of `m` appears
once. -/
def extendMultilinear {s t : Finset ι} (hst : s ⊆ t) :
    MultilinearMap R (fun i : s => A i) (⨂[R] i : t, A i) where
  toFun m := tprod R (extendFun ξ m)
  map_update_add' m i x y := by
    classical
    simp only [extendFun_update ξ hst, MultilinearMap.map_update_add]
  map_update_smul' m i r x := by
    classical
    simp only [extendFun_update ξ hst, MultilinearMap.map_update_smul]

variable (R) in
/-- The **extension by the reference vectors** `ξ` from the tensor product over `s` to the tensor
product over `t ⊇ s`: `⨂_{i ∈ s} m i ↦ (⨂_{i ∈ s} m i) ⊗ (⨂_{j ∈ t \ s} ξ j)`. -/
def extend {s t : Finset ι} (hst : s ⊆ t) : (⨂[R] i : s, A i) →ₗ[R] ⨂[R] i : t, A i :=
  lift (extendMultilinear ξ hst)

/-- The extension sends `⨂ m` to `⨂ extendFun ξ m`. -/
@[simp] lemma extend_tprod {s t : Finset ι} (hst : s ⊆ t) (m : Π i : s, A i) :
    extend R ξ hst (tprod R m) = tprod R (extendFun ξ m) :=
  lift.tprod _

/-- Extending from `s` to `s` is the identity. -/
lemma extend_refl (s : Finset ι) : extend R ξ (subset_refl s) = LinearMap.id :=
  PiTensorProduct.ext (MultilinearMap.ext fun m => by simp [extendFun_refl])

/-- Extending from `s` to `t` and then to `u` is extending from `s` to `u`. -/
lemma extend_extend {s t u : Finset ι} (hst : s ⊆ t) (htu : t ⊆ u) (x : ⨂[R] i : s, A i) :
    extend R ξ htu (extend R ξ hst x) = extend R ξ (hst.trans htu) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m => simp [extendFun_extendFun ξ hst]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The extensions by the reference vectors form a directed system over the finite sets of
indices. -/
instance directedSystem :
    DirectedSystem (fun s : Finset ι => ⨂[R] i : s, A i) (fun _ _ h => extend R ξ h) where
  map_self s x := by rw [extend_refl]; rfl
  map_map _ _ _ hst htu x := extend_extend ξ hst htu x

end Module

section Algebra

variable [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- The extension of `1` by `1` is `1`. -/
lemma extendFun_one {s t : Finset ι} :
    extendFun (t := t) (1 : Π i, A i) (1 : Π i : s, A i) = 1 := by
  funext j
  by_cases hj : (j : ι) ∈ s <;> simp [extendFun, hj]

/-- The extension by `1` is multiplicative. -/
lemma extendFun_mul {s t : Finset ι} (m n : Π i : s, A i) :
    extendFun (t := t) (1 : Π i, A i) (m * n) = extendFun 1 m * extendFun 1 n := by
  funext j
  by_cases hj : (j : ι) ∈ s <;> simp [extendFun, hj]

variable (R) in
/-- For algebras, the extension by `1`, `x ↦ x ⊗ 1`, as an algebra homomorphism. -/
def extendAlgHom {s t : Finset ι} (hst : s ⊆ t) : (⨂[R] i : s, A i) →ₐ[R] ⨂[R] i : t, A i :=
  AlgHom.ofLinearMap (extend R (1 : Π i, A i) hst)
    (by rw [one_def, extend_tprod, extendFun_one, one_def])
    (fun x y => by
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' n =>
          rw [smul_mul_smul_comm, tprod_mul_tprod, map_smul, map_smul, map_smul, extend_tprod,
            extend_tprod, extend_tprod, extendFun_mul, smul_mul_smul_comm, tprod_mul_tprod]
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul])

/-- `PiTensorProduct.extendAlgHom h` is the extension by `1`. -/
lemma toLinearMap_extendAlgHom {s t : Finset ι} (hst : s ⊆ t) :
    (extendAlgHom R (A := A) hst).toLinearMap = extend R (1 : Π i, A i) hst :=
  rfl

/-- `PiTensorProduct.extendAlgHom h` sends `⨂ m` to `⨂ m ⊗ 1`. -/
@[simp] lemma extendAlgHom_tprod {s t : Finset ι} (hst : s ⊆ t) (m : Π i : s, A i) :
    extendAlgHom R hst (tprod R m) = tprod R (extendFun (t := t) 1 m) :=
  extend_tprod (R := R) 1 hst m

/-- The extensions by `1` form a directed system of algebra homomorphisms. -/
instance directedSystemAlgHom :
    DirectedSystem (fun s : Finset ι => ⨂[R] i : s, A i) (fun _ _ h => extendAlgHom R h) where
  map_self _ x := (directedSystem (R := R) (A := A) 1).map_self x
  map_map _ _ _ hst htu x := extend_extend (R := R) (1 : Π i, A i) hst htu x

end Algebra

end PiTensorProduct
