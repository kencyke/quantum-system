/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# The multiplication of a topological ring is a continuous perfect pairing

For a commutative ring `R` with continuous multiplication, the multiplication
`LinearMap.mul R R : R →ₗ[R] R →ₗ[R] R` is a continuous perfect pairing of `R` with itself: every
continuous linear map `f : R →L[R] R` is multiplication by `f 1`. For `R = ℝ` this realises `ℝ` as
its own dual, the pairing along which the Fourier transform of a measure on `ℝ` is
`t ↦ ∫ exp (i t λ) dμ(λ)`.

## Main results

* `LinearMap.mul_isContPerfPair` — `(LinearMap.mul R R).IsContPerfPair`.
-/

@[expose] public section

namespace LinearMap

variable {R : Type*} [CommRing R] [TopologicalSpace R] [ContinuousMul R]

/-- The multiplication of a commutative ring with continuous multiplication is a continuous
perfect pairing: a continuous linear map `f : R →L[R] R` is multiplication by `f 1`. -/
instance mul_isContPerfPair : (LinearMap.mul R R).IsContPerfPair where
  continuous_uncurry := continuous_mul
  bijective_left := by
    refine ⟨fun x y h => by simpa using congr($h 1), fun f => ⟨f 1, ?_⟩⟩
    ext
    simp
  bijective_right := by
    refine ⟨fun x y h => by simpa using congr($h 1), fun f => ⟨f 1, ?_⟩⟩
    ext
    simp

end LinearMap
