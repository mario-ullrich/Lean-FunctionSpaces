/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Differences of higher order

The **difference of order `r` with step `h`** of `f : ℝ → ℂ` is

`Δ_h^r f(x) = ∑_{k=0}^r (-1)^(r-k) C(r,k) f(x + k h)`   (`Interval.iterDiff`),

the `r`-fold iterate of Mathlib's forward difference `fwdDiff h` (`Δ_h f(x) = f(x + h) - f(x)`).
It is linear in `f`, commutes with translations and is invariant up to sign and shift under the
reflection `x ↦ c - x`.  Differences of order `r` annihilate the **polynomials of degree `< r`**
(`Interval.iterDiff_polynomial`), which is why they measure smoothness of order `r`; this
comes from Mathlib's `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` (step `1`) after the change
of variable `x + k h`.  Polynomials are elements of Mathlib's `Polynomial.degreeLT ℂ r`,
evaluated at real points.
-/

@[expose] public section

open Finset Polynomial

namespace Interval

/-- The **difference of order `r`** with step `h`, `Δ_h^r f = (fwdDiff h)^[r] f`. -/
noncomputable def iterDiff (r : ℕ) (h : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := (fwdDiff h)^[r] f

/-- `Δ_h^r f(x) = ∑_{k=0}^r (-1)^(r-k) C(r,k) f(x + k h)`. -/
theorem iterDiff_apply (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    iterDiff r h f x =
      ∑ k ∈ range (r + 1), ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (x + k * h) := by
  rw [iterDiff, fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- `Δ_h^0 f = f`. -/
@[simp] theorem iterDiff_zero (h : ℝ) (f : ℝ → ℂ) : iterDiff 0 h f = f := rfl

/-- `Δ_h^(r+1) f(x) = Δ_h^r f(x + h) - Δ_h^r f(x)`. -/
theorem iterDiff_succ (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    iterDiff (r + 1) h f x = iterDiff r h f (x + h) - iterDiff r h f x := by
  rw [iterDiff, Function.iterate_succ_apply']
  rfl

/-- `Δ_h^(r+1) f = Δ_h^r (Δ_h f)`. -/
theorem iterDiff_succ' (r : ℕ) (h : ℝ) (f : ℝ → ℂ) :
    iterDiff (r + 1) h f = iterDiff r h (fwdDiff h f) := by
  rw [iterDiff, Function.iterate_succ_apply]
  rfl

/-- Differences are additive. -/
theorem iterDiff_add (r : ℕ) (h : ℝ) (f g : ℝ → ℂ) :
    iterDiff r h (f + g) = iterDiff r h f + iterDiff r h g := by
  funext x
  simp only [iterDiff_apply, Pi.add_apply, mul_add, sum_add_distrib]

/-- Differences commute with subtraction. -/
theorem iterDiff_sub (r : ℕ) (h : ℝ) (f g : ℝ → ℂ) :
    iterDiff r h (f - g) = iterDiff r h f - iterDiff r h g := by
  funext x
  simp only [iterDiff_apply, Pi.sub_apply, mul_sub, sum_sub_distrib]

/-- Differences are homogeneous. -/
theorem iterDiff_const_mul (r : ℕ) (h : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    iterDiff r h (fun x => c * f x) = fun x => c * iterDiff r h f x := by
  funext x
  simp only [iterDiff_apply, mul_sum]
  exact sum_congr rfl fun k _ => by ring

/-- Differences commute with translations: `Δ_h^r (f(· + c))(x) = Δ_h^r f(x + c)`. -/
theorem iterDiff_comp_add (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (c x : ℝ) :
    iterDiff r h (fun y => f (y + c)) x = iterDiff r h f (x + c) := by
  simp only [iterDiff_apply]
  exact sum_congr rfl fun k _ => by rw [add_right_comm]

/-- **Reflection**: for `g(x) = f(c - x)`, `Δ_h^r g(x) = (-1)^r Δ_h^r f(c - x - r h)`. -/
theorem iterDiff_reflect (r : ℕ) (h : ℝ) (f : ℝ → ℂ) (c x : ℝ) :
    iterDiff r h (fun y => f (c - y)) x = (-1 : ℂ) ^ r * iterDiff r h f (c - x - r * h) := by
  simp only [iterDiff_apply, mul_sum]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [show r + 1 - 1 - k = r - k by omega, Nat.choose_symm hk', show r - (r - k) = k by omega]
  have hx : c - (x + ((r - k : ℕ) : ℝ) * h) = c - x - r * h + k * h := by
    rw [Nat.cast_sub hk']; ring
  rw [hx]
  have hsign : (-1 : ℂ) ^ k = (-1) ^ r * (-1) ^ (r - k) := by
    rw [← pow_add, show r + (r - k) = k + 2 * (r - k) by omega, pow_add, pow_mul]
    simp
  rw [hsign]
  ring

/-- **Differences of order `r` annihilate polynomials of degree `< r`**:
`Δ_h^r P = 0` for `P ∈ degreeLT ℂ r`. -/
theorem iterDiff_polynomial {r : ℕ} {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (h : ℝ) :
    iterDiff r h (fun x => P.eval (x : ℂ)) = 0 := by
  funext x
  rcases eq_or_ne P 0 with rfl | hP0
  · simp [iterDiff_apply]
  set Q : ℂ[X] := P.comp (C (x : ℂ) + C (h : ℂ) * X)
  have hdeg : Q.natDegree < r := by
    have h1 : (C (x : ℂ) + C (h : ℂ) * X).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    have h2 : P.natDegree < r := (natDegree_lt_iff_degree_lt hP0).2 (mem_degreeLT.1 hP)
    calc Q.natDegree ≤ P.natDegree * (C (x : ℂ) + C (h : ℂ) * X).natDegree := natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ h1
      _ < r := by rw [mul_one]; exact h2
  have hzero := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  rw [iterDiff_apply, Pi.zero_apply]
  rw [Pi.zero_apply] at hzero
  rw [← hzero]
  refine sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul, mul_one, zero_add, eval_comp]
  simp only [eval_add, eval_C, eval_mul, eval_X]
  push_cast
  ring_nf

end Interval
