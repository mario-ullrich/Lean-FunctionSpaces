/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Sequences.Lq
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The normalising factor `2^(j/2)` of dyadic dilations

Haar functions, multiwavelets and Daubechies wavelets of level `j` carry the factor `2^(j/2)`,
which makes the dilation `g ↦ 2^(j/2) g(2^j ·)` an isometry of `L_2`. As a complex number its
square is `2^j` (`ofReal_two_rpow_half_mul_self`), and its extended norm is the dyadic weight
`2^(j/2)` (`enorm_two_rpow_half`). Dilations on `ℝ^d` carry the factor `(2^(j/2))^d`, whose
square is `2^(jd)` (`ofReal_two_rpow_half_pow_mul_self`) and whose extended norm is `2^(jd/2)`
(`enorm_two_rpow_half_pow`).
-/

@[expose] public section

open scoped ENNReal

/-- **The square of the normalising factor**: `2^(j/2) · 2^(j/2) = 2^j` for every `j ∈ ℕ`, as
complex numbers (Mathlib's `Real.rpow_add` and `add_halves`). -/
theorem ofReal_two_rpow_half_mul_self (j : ℕ) :
    (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) = (2 : ℂ) ^ j := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add two_pos, add_halves, Real.rpow_natCast]
  push_cast
  rfl

/-- **The normalising factor in extended norm**: `‖2^(j/2)‖ = 2^(j/2)` for every `j ∈ ℕ`, written
as the dyadic weight `ENNReal.dyadicWeight (1/2) j`. -/
theorem enorm_two_rpow_half (j : ℕ) :
    ‖(((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ)‖ₑ = ENNReal.dyadicWeight (1 / 2) j := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    ← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat, ENNReal.dyadicWeight, mul_one_div]

/-- **The square of the normalising factor on `ℝ^d`**: `(2^(j/2))^d (2^(j/2))^d = 2^(jd)` for all
`j, d ∈ ℕ`, as complex numbers (`ofReal_two_rpow_half_mul_self`). -/
theorem ofReal_two_rpow_half_pow_mul_self {d : ℕ} (j : ℕ) :
    (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) ^ d * (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) ^ d =
      (2 : ℂ) ^ (j * d) := by
  rw [← mul_pow, ofReal_two_rpow_half_mul_self, pow_mul]

/-- **The normalising factor on `ℝ^d` in extended norm**: `‖(2^(j/2))^d‖ = 2^(jd/2)` for all
`j, d ∈ ℕ`, written as the dyadic weight `ENNReal.dyadicWeight (d/2) j`
(`enorm_two_rpow_half`). -/
theorem enorm_two_rpow_half_pow {d : ℕ} (j : ℕ) :
    ‖(((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) ^ d‖ₑ = ENNReal.dyadicWeight (d / 2) j := by
  rw [eNorm_pow, enorm_two_rpow_half, ← ENNReal.rpow_natCast, ENNReal.dyadicWeight_rpow]
  congr 1
  ring
