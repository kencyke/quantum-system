module

public import QuantumSystem.Algebra.Linear.Unbounded.Basic
public import Mathlib.Algebra.Module.LinearMap.Star

/-!
# Antilinear (Conjugate-Linear) Maps

This file develops the theory of antilinear (conjugate-linear) maps on inner product spaces.
Antilinear maps are essential in quantum mechanics, particularly for the modular conjugation
operator J in Tomita-Takesaki theory.

## Main definitions

* `Antilinear`: Type alias for semilinear maps with conjugate scalar action
* `DenselyDefinedAntilinearMap`: Densely defined antilinear operators

## Antilinear maps

An antilinear map (or conjugate-linear map) is a map f : V → W satisfying:
- f(x + y) = f(x) + f(y)  (additive)
- f(c • x) = c̄ • f(x)    (conjugate-homogeneous)

where c̄ denotes the complex conjugate.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reed1980]
* [Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics*][bratteli1987]
-/

@[expose] public section

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']

/-! ### Antilinear maps -/

/-- Antilinear maps are semilinear maps with the star ring endomorphism as the ring homomorphism.
In the complex case, this means f(cz) = c̄·f(z). -/
abbrev Antilinear (𝕜 : Type*) [CommSemiring 𝕜] [StarRing 𝕜]
    (M M' : Type*) [AddCommMonoid M] [AddCommMonoid M'] [Module 𝕜 M] [Module 𝕜 M'] :=
  M →ₗ⋆[𝕜] M'

namespace Antilinear

variable {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [Module 𝕜 M] [Module 𝕜 M']

/-- An antilinear map satisfies f(c • x) = starRingEnd 𝕜 c • f(x). -/
theorem map_smul_eq_star_smul (f : Antilinear 𝕜 M M') (c : 𝕜) (x : M) :
    f (c • x) = starRingEnd 𝕜 c • f x := LinearMap.map_smulₛₗ f c x

/-- The zero antilinear map. -/
def zero : Antilinear 𝕜 M M' := 0

/-- Addition of antilinear maps. -/
instance : Add (Antilinear 𝕜 M M') := inferInstance

end Antilinear

/-! ### Antilinear isometries -/

/-- An antilinear isometry is an antilinear map that preserves norms. -/
structure AntilinearIsometry (𝕜 : Type*) [CommSemiring 𝕜] [StarRing 𝕜]
    (M M' : Type*) [SeminormedAddCommGroup M] [SeminormedAddCommGroup M']
    [Module 𝕜 M] [Module 𝕜 M'] extends Antilinear 𝕜 M M' where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖

namespace AntilinearIsometry

variable {M M' : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup M']
  [Module 𝕜 M] [Module 𝕜 M']

/-- An antilinear isometry preserves norms. -/
theorem norm_map (f : AntilinearIsometry 𝕜 M M') (x : M) : ‖f.toLinearMap x‖ = ‖x‖ :=
  f.norm_map' x

/-- The underlying function of an antilinear isometry. -/
def toFunAux (f : AntilinearIsometry 𝕜 M M') : M → M' := f.toLinearMap

instance : FunLike (AntilinearIsometry 𝕜 M M') M M' where
  coe f := f.toFunAux
  coe_injective' f g h := by
    cases f; cases g
    simp only [AntilinearIsometry.mk.injEq]
    ext x
    exact congrFun h x

@[simp]
theorem coe_toLinearMap (f : AntilinearIsometry 𝕜 M M') : ⇑f.toLinearMap = f := rfl

end AntilinearIsometry

/-! ### Conjugation operator -/

section Conjugation

variable [CompleteSpace H]

/-- A conjugation operator on a Hilbert space is an antilinear isometric involution.
This is the abstract model for the modular conjugation J in Tomita-Takesaki theory. -/
structure Conjugation (𝕜 : Type*) [RCLike 𝕜] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] extends AntilinearIsometry 𝕜 H H where
  involutive' : ∀ x, toLinearMap (toLinearMap x) = x

namespace Conjugation

variable (J : Conjugation 𝕜 H)

omit [CompleteSpace H] in
/-- A conjugation is involutive: J(Jx) = x. -/
theorem involutive : Function.Involutive J.toLinearMap := J.involutive'

omit [CompleteSpace H] in
/-- A conjugation is its own inverse. -/
theorem self_comp_self : J.toLinearMap.comp J.toLinearMap = LinearMap.id := by
  ext x
  exact J.involutive x

omit [CompleteSpace H] in
instance : FunLike (Conjugation 𝕜 H) H H where
  coe J := J.toAntilinearIsometry
  coe_injective' J K h := by
    obtain ⟨⟨f₁, hf₁⟩, hi₁⟩ := J
    obtain ⟨⟨f₂, hf₂⟩, hi₂⟩ := K
    simp only [Conjugation.mk.injEq, AntilinearIsometry.mk.injEq]
    exact LinearMap.ext (fun x => congrFun h x)

omit [CompleteSpace H] in
/-- A conjugation preserves inner products in a specific way:
⟨Jx, Jy⟩ = ⟨y, x⟩ = conj ⟨x, y⟩.

This follows from polarization identity and the fact that J preserves norms.
The proof uses `inner_eq_sum_norm_sq_div_four` and properties of antilinear maps.

**Proof outline**: For an antilinear isometry J on a complex Hilbert space:
1. By polarization: `⟨u, v⟩ = (‖u+v‖² - ‖u-v‖² + I(‖u-Iv‖² - ‖u+Iv‖²))/4`
2. J preserves norms: `‖Jw‖ = ‖w‖` for all w
3. J is antilinear: `J(u + v) = Ju + Jv` and `J(c·u) = c̄·Ju`
4. Thus `‖Ju + Jv‖ = ‖J(u+v)‖ = ‖u+v‖`, similarly for other terms
5. For the imaginary part: `‖Ju - I·Jv‖ = ‖Jx + J(I·y)‖ = ‖J(x + I·y)‖ = ‖x + I·y‖`
6. Similarly: `‖Ju + I·Jv‖ = ‖x - I·y‖`
7. Substituting: `⟨Jx, Jy⟩ = (‖x+y‖² - ‖x-y‖² - I(‖x+Iy‖² - ‖x-Iy‖²))/4 = conj ⟨x, y⟩`
-/
theorem inner_map_map (x y : H) : @inner 𝕜 H _ (J x) (J y) = starRingEnd 𝕜 (@inner 𝕜 H _ x y) := by
  -- Identify J x with J.toLinearMap x
  have coe_eq : ∀ z, J z = J.toLinearMap z := fun _ => rfl
  simp only [coe_eq]
  -- Setup: J is additive and satisfies J(c•v) = conj(c)•Jv
  have hJadd : ∀ a b, J.toLinearMap (a + b) = J.toLinearMap a + J.toLinearMap b :=
    fun a b => J.toLinearMap.map_add a b
  have hJsub : ∀ a b, J.toLinearMap (a - b) = J.toLinearMap a - J.toLinearMap b :=
    fun a b => J.toLinearMap.map_sub a b
  -- Norm preservation for sums/differences
  have norm_add : ‖J.toLinearMap x + J.toLinearMap y‖ = ‖x + y‖ := by
    rw [← hJadd, J.toAntilinearIsometry.norm_map]
  have norm_sub : ‖J.toLinearMap x - J.toLinearMap y‖ = ‖x - y‖ := by
    rw [← hJsub, J.toAntilinearIsometry.norm_map]
  -- Key fact: J(I•y) = -I•Jy (since conj(I) = -I)
  have hI : J.toLinearMap ((@RCLike.I 𝕜 _) • y) = ((-1 : 𝕜) * @RCLike.I 𝕜 _) • J.toLinearMap y := by
    rw [J.toLinearMap.map_smulₛₗ, RCLike.conj_I, neg_one_mul]
  -- Norm with imaginary component: ‖Jx - I•Jy‖ = ‖x + I•y‖
  have norm1 : ‖J.toLinearMap x - (@RCLike.I 𝕜 _) • J.toLinearMap y‖ =
               ‖x + (@RCLike.I 𝕜 _) • y‖ := by
    have h1 : J.toLinearMap x - (@RCLike.I 𝕜 _) • J.toLinearMap y =
              J.toLinearMap x + J.toLinearMap ((@RCLike.I 𝕜 _) • y) := by
      rw [hI]
      simp only [neg_one_mul, neg_smul]
      rw [sub_eq_add_neg]
    rw [h1, ← hJadd, J.toAntilinearIsometry.norm_map]
  -- ‖Jx + I•Jy‖ = ‖x - I•y‖
  have norm2 : ‖J.toLinearMap x + (@RCLike.I 𝕜 _) • J.toLinearMap y‖ =
               ‖x - (@RCLike.I 𝕜 _) • y‖ := by
    have h1 : J.toLinearMap x + (@RCLike.I 𝕜 _) • J.toLinearMap y =
              J.toLinearMap x - J.toLinearMap ((@RCLike.I 𝕜 _) • y) := by
      rw [hI]
      simp only [neg_one_mul, neg_smul]
      rw [sub_eq_add_neg, neg_neg]
    rw [h1, ← hJsub, J.toAntilinearIsometry.norm_map]
  -- Apply polarization identity on both sides
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  rw [norm_add, norm_sub, norm1, norm2]
  -- Simplify conjugates: real numbers are fixed, conj(I) = -I
  simp only [map_div₀, map_sub, map_add, map_mul, RCLike.conj_I,
             RCLike.conj_ofReal, map_pow]
  -- Handle the fact that 4 is coerced from naturals
  have h4 : (4 : 𝕜) = ((4 : ℝ) : 𝕜) := by norm_cast
  simp only [h4, RCLike.conj_ofReal]
  ring

end Conjugation

end Conjugation

/-! ### Densely defined antilinear maps -/

/-- A densely defined antilinear map is an antilinear map defined on a dense subspace. -/
structure DenselyDefinedAntilinearMap (𝕜 : Type*) [RCLike 𝕜]
    (E F : Type*) [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜 F] where
  /-- The domain of the map as a submodule. -/
  domain : Submodule 𝕜 E
  /-- The underlying antilinear map on the domain. -/
  toFun : domain →ₗ⋆[𝕜] F
  /-- The domain is dense in E. -/
  dense_domain : Dense (domain : Set E)

namespace DenselyDefinedAntilinearMap

variable {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F]

/-- The domain of a densely defined antilinear map. -/
def dom (T : DenselyDefinedAntilinearMap 𝕜 E F) : Submodule 𝕜 E := T.domain

/-- Coercion to function on the domain. -/
instance : CoeFun (DenselyDefinedAntilinearMap 𝕜 E F) (fun T => T.dom → F) where
  coe T := T.toFun

/-- Apply the map to an element of the domain. -/
theorem apply_eq (T : DenselyDefinedAntilinearMap 𝕜 E F) (x : T.dom) :
    T x = T.toFun x := rfl

/-- Scalar multiplication property (with conjugate). -/
theorem map_smul (T : DenselyDefinedAntilinearMap 𝕜 E F) (c : 𝕜) (x : T.dom) :
    T (c • x) = starRingEnd 𝕜 c • T x := LinearMap.map_smulₛₗ T.toFun c x

/-- Additivity. -/
theorem map_add (T : DenselyDefinedAntilinearMap 𝕜 E F) (x y : T.dom) :
    T (x + y) = T x + T y := T.toFun.map_add x y

end DenselyDefinedAntilinearMap

/-! ### On Hilbert spaces -/

/-- Densely defined antilinear operator on a Hilbert space. -/
abbrev AntilinearOnHilbertSpace (𝕜 : Type*) [RCLike 𝕜] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :=
  DenselyDefinedAntilinearMap 𝕜 H H

/-! ### Graph and closability for antilinear maps -/

namespace AntilinearOnHilbertSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The graph of a densely defined antilinear map as a set in H × H. -/
def graphSet (T : AntilinearOnHilbertSpace 𝕜 H) : Set (H × H) :=
  { p | ∃ (x : T.dom), p = ((x : H), T x) }

/-- An antilinear map is closable if the closure of its graph doesn't contain (0, y) with y ≠ 0.
This is analogous to the definition for linear maps. -/
def IsClosable (T : AntilinearOnHilbertSpace 𝕜 H) : Prop :=
  ∀ y : H, ((0, y) ∈ closure (T.graphSet)) → y = 0

/-- An antilinear map is closed if its graph is closed. -/
def IsGraphClosed (T : AntilinearOnHilbertSpace 𝕜 H) : Prop :=
  _root_.IsClosed (T.graphSet)

omit [CompleteSpace H] in
/-- Closed antilinear maps are closable. -/
theorem IsGraphClosed.isClosable {T : AntilinearOnHilbertSpace 𝕜 H} (hT : IsGraphClosed T) :
    IsClosable T := by
  intro y hy
  rw [_root_.IsClosed.closure_eq hT] at hy
  obtain ⟨x, hx⟩ := hy
  simp only [Prod.mk.injEq] at hx
  have hx0 : (x : H) = 0 := hx.1.symm
  have hxy : y = T x := hx.2
  rw [hxy]
  have : x = 0 := Subtype.ext hx0
  simp only [this, map_zero]

end AntilinearOnHilbertSpace
