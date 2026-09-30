/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Sequences.Lq
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Log

/-!
# Cauchy condensation with power weights

For a **decreasing** sequence `b : ℕ → ℝ≥0∞` and a real exponent `γ`, the weighted series
`∑ₙ (n + 1) ^ γ b n` and its dyadic version `∑ₖ 2 ^ (k (γ + 1)) b (2 ^ k)` are comparable:

* `tsum_pow_mul_le_dyadic`:
  `∑ₙ (n+1)^γ b n ≤ b 0 + 2^(max γ 0) ∑ₖ 2^(k(γ+1)) b (2^k)`;
* `dyadic_le_tsum_pow_mul`:
  `∑ₖ 2^(k(γ+1)) b (2^(k+1)) ≤ 2^(max (-γ) 0) ∑ₙ (n+1)^γ b n`;

and the analogous statements for suprema, `iSup_pow_mul_le_dyadic` and
`dyadic_le_iSup_pow_mul`.  The proof splits `ℕ \ {0}` into the dyadic blocks
`[2^k, 2^(k+1))`, which have `2^k` elements, on which `b` is at most `b (2^k)` and at least
`b (2^(k+1))`, and on which `(n+1)^γ` is within a factor `2^|γ|` of `2^(kγ)`.

For `γ = 0` this is Cauchy's condensation test (Mathlib: `ENNReal.le_tsum_condensed`,
`ENNReal.tsum_condensed_le`).  The weight `(n + 1) ^ γ` is in general increasing, so the
weighted sequence is not decreasing and Mathlib's version does not apply to it directly.
These estimates are what makes Pietsch's quasi-norm `‖(n^(s - 1/q) E_{n-1})ₙ‖_q` equivalent to
the dyadic one `‖(2^(ks) E_{2^k})ₖ‖_q`.
-/

@[expose] public section

open Finset Filter
open scoped ENNReal

namespace ENNReal

/-- For a nonpositive exponent, `x ↦ x ^ z` is decreasing on `ℝ≥0∞`. -/
theorem rpow_le_rpow_of_nonpos {x y : ℝ≥0∞} {z : ℝ} (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have hy : y ^ z = (y ^ (-z))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
  have hx : x ^ z = (x ^ (-z))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
  rw [hy, hx]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hxy (neg_nonneg.2 hz))

/-- The initial segment `[0, 2^K)` of `ℕ` is `{0}` together with the dyadic blocks
`[2^k, 2^(k+1))`, `k < K`. -/
theorem sum_range_two_pow_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) (K : ℕ) :
    ∑ n ∈ range (2 ^ K), g n = g 0 + ∑ k ∈ range K, ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), g n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [← Finset.sum_range_add_sum_Ico g (Nat.pow_le_pow_right two_pos (Nat.le_succ K)), ih,
      Finset.sum_range_succ, add_assoc]

/-- `2^k = 2^(k · 1)`, the dyadic weight of exponent `1`. -/
theorem natCast_two_pow_eq (k : ℕ) : ((2 ^ k : ℕ) : ℝ≥0∞) = dyadicWeight 1 k := by
  rw [← natCast_two_pow_rpow, ENNReal.rpow_one]

/-- A dyadic block `[2^k, 2^(k+1))` has `2^k` elements. -/
theorem card_Ico_two_pow (k : ℕ) : (Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
  rw [Nat.card_Ico, pow_succ]; omega

/-- On the dyadic block `[2^k, 2^(k+1))`, `(n + 1)^γ ≤ 2^(max γ 0) 2^(kγ)`. -/
theorem natCast_succ_rpow_le {k n : ℕ} (hn : n ∈ Ico (2 ^ k) (2 ^ (k + 1))) (γ : ℝ) :
    ((n + 1 : ℕ) : ℝ≥0∞) ^ γ ≤ 2 ^ max γ 0 * dyadicWeight γ k := by
  rw [Finset.mem_Ico] at hn
  rcases le_or_gt 0 γ with hγ | hγ
  · rw [max_eq_left hγ]
    calc ((n + 1 : ℕ) : ℝ≥0∞) ^ γ ≤ ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) ^ γ := by
          gcongr; exact_mod_cast hn.2
      _ = 2 ^ γ * dyadicWeight γ k := by rw [natCast_two_pow_rpow, dyadicWeight_succ]
  · rw [max_eq_right hγ.le, ENNReal.rpow_zero, one_mul, ← natCast_two_pow_rpow]
    exact rpow_le_rpow_of_nonpos (by exact_mod_cast hn.1.trans (Nat.le_succ n)) hγ.le

/-- On the dyadic block `[2^k, 2^(k+1))`, `2^(kγ) ≤ 2^(max (-γ) 0) (n + 1)^γ`. -/
theorem dyadicWeight_le_natCast_succ_rpow {k n : ℕ} (hn : n ∈ Ico (2 ^ k) (2 ^ (k + 1)))
    (γ : ℝ) : dyadicWeight γ k ≤ 2 ^ max (-γ) 0 * ((n + 1 : ℕ) : ℝ≥0∞) ^ γ := by
  rw [Finset.mem_Ico] at hn
  rcases le_or_gt 0 γ with hγ | hγ
  · rw [max_eq_right (neg_nonpos.2 hγ), ENNReal.rpow_zero, one_mul, ← natCast_two_pow_rpow]
    gcongr; exact_mod_cast hn.1.trans (Nat.le_succ n)
  · rw [max_eq_left (neg_nonneg.2 hγ.le)]
    have h1 : ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) ^ γ ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ γ :=
      rpow_le_rpow_of_nonpos (by exact_mod_cast hn.2) hγ.le
    rw [natCast_two_pow_rpow, dyadicWeight_succ] at h1
    calc dyadicWeight γ k = 2 ^ (-γ) * (2 ^ γ * dyadicWeight γ k) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
            neg_add_cancel, ENNReal.rpow_zero, one_mul]
      _ ≤ _ := by gcongr

variable {b : ℕ → ℝ≥0∞}

/-- The weighted sum over a dyadic block is at most `2^(max γ 0) 2^(k(γ+1)) b (2^k)`. -/
theorem sum_Ico_pow_mul_le (hb : Antitone b) (γ : ℝ) (k : ℕ) :
    ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n ≤
      2 ^ max γ 0 * dyadicWeight (γ + 1) k * b (2 ^ k) := by
  calc ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n
      ≤ ∑ _n ∈ Ico (2 ^ k) (2 ^ (k + 1)), 2 ^ max γ 0 * dyadicWeight γ k * b (2 ^ k) := by
        gcongr with n hn
        · exact natCast_succ_rpow_le hn γ
        · exact hb (Finset.mem_Ico.1 hn).1
    _ = 2 ^ max γ 0 * dyadicWeight (γ + 1) k * b (2 ^ k) := by
        rw [Finset.sum_const, card_Ico_two_pow, nsmul_eq_mul, dyadicWeight_add,
          natCast_two_pow_eq]
        ring

/-- The weighted sum over a dyadic block is at least `2^(-max (-γ) 0) 2^(k(γ+1)) b (2^(k+1))`. -/
theorem le_sum_Ico_pow_mul (hb : Antitone b) (γ : ℝ) (k : ℕ) :
    dyadicWeight (γ + 1) k * b (2 ^ (k + 1)) ≤
      2 ^ max (-γ) 0 * ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
  calc dyadicWeight (γ + 1) k * b (2 ^ (k + 1))
      = ∑ _n ∈ Ico (2 ^ k) (2 ^ (k + 1)), dyadicWeight γ k * b (2 ^ (k + 1)) := by
        rw [Finset.sum_const, card_Ico_two_pow, nsmul_eq_mul, dyadicWeight_add,
          natCast_two_pow_eq]
        ring
    _ ≤ ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), 2 ^ max (-γ) 0 * (((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [← mul_assoc]
        exact mul_le_mul' (dyadicWeight_le_natCast_succ_rpow hn γ)
          (hb (Finset.mem_Ico.1 hn).2.le)
    _ = _ := by rw [Finset.mul_sum]

/-- **Weighted condensation, upper bound**:
`∑ₙ (n+1)^γ b n ≤ b 0 + 2^(max γ 0) ∑ₖ 2^(k(γ+1)) b (2^k)` for decreasing `b`. -/
theorem tsum_pow_mul_le_dyadic (hb : Antitone b) (γ : ℝ) :
    ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n ≤
      b 0 + 2 ^ max γ 0 * ∑' k, dyadicWeight (γ + 1) k * b (2 ^ k) := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two)]
  refine iSup_le fun K => ?_
  rw [sum_range_two_pow_eq]
  simp only [Nat.cast_one, Nat.zero_add, ENNReal.one_rpow, one_mul]
  gcongr
  calc ∑ k ∈ range K, ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n
      ≤ ∑ k ∈ range K, 2 ^ max γ 0 * (dyadicWeight (γ + 1) k * b (2 ^ k)) := by
        gcongr with k
        rw [← mul_assoc]; exact sum_Ico_pow_mul_le hb γ k
    _ ≤ ∑' k, 2 ^ max γ 0 * (dyadicWeight (γ + 1) k * b (2 ^ k)) := ENNReal.sum_le_tsum _
    _ = _ := ENNReal.tsum_mul_left

/-- **Weighted condensation, lower bound**:
`∑ₖ 2^(k(γ+1)) b (2^(k+1)) ≤ 2^(max (-γ) 0) ∑ₙ (n+1)^γ b n` for decreasing `b`. -/
theorem dyadic_le_tsum_pow_mul (hb : Antitone b) (γ : ℝ) :
    ∑' k, dyadicWeight (γ + 1) k * b (2 ^ (k + 1)) ≤
      2 ^ max (-γ) 0 * ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun K => ?_
  calc ∑ k ∈ range K, dyadicWeight (γ + 1) k * b (2 ^ (k + 1))
      ≤ ∑ k ∈ range K, 2 ^ max (-γ) 0 *
          ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
        exact Finset.sum_le_sum fun k _ => le_sum_Ico_pow_mul hb γ k
    _ = 2 ^ max (-γ) 0 * ∑ k ∈ range K,
          ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ max (-γ) 0 * ∑ n ∈ range (2 ^ K), ((n + 1 : ℕ) : ℝ≥0∞) ^ γ * b n := by
        rw [sum_range_two_pow_eq]; gcongr; exact le_add_self
    _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum _

/-- **Condensation for suprema**, upper bound: for decreasing `b` and `s ≥ 0`,
`supₙ (n+1)^s b n ≤ b 0 + 2^s supₖ 2^(ks) b (2^k)`. -/
theorem iSup_pow_mul_le_dyadic (hb : Antitone b) {s : ℝ} (hs : 0 ≤ s) :
    ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n ≤ b 0 + 2 ^ s * ⨆ k, dyadicWeight s k * b (2 ^ k) := by
  refine iSup_le fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set k := Nat.log 2 n
  have hmem : n ∈ Ico (2 ^ k) (2 ^ (k + 1)) :=
    Finset.mem_Ico.2 ⟨Nat.pow_log_le_self 2 hn.ne', Nat.lt_pow_succ_log_self Nat.one_lt_two n⟩
  calc ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n ≤ 2 ^ s * dyadicWeight s k * b (2 ^ k) := by
        gcongr
        · simpa [max_eq_left hs] using natCast_succ_rpow_le hmem s
        · exact hb (Finset.mem_Ico.1 hmem).1
    _ ≤ 2 ^ s * ⨆ k, dyadicWeight s k * b (2 ^ k) := by
        rw [mul_assoc]; gcongr; exact le_iSup (fun k => dyadicWeight s k * b (2 ^ k)) k
    _ ≤ _ := le_add_self

/-- **Condensation for suprema**, lower bound: for `s ≥ 0`,
`supₖ 2^(ks) b (2^k) ≤ supₙ (n+1)^s b n`. -/
theorem dyadic_le_iSup_pow_mul {s : ℝ} (hs : 0 ≤ s) :
    ⨆ k, dyadicWeight s k * b (2 ^ k) ≤ ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n := by
  refine iSup_le fun k => ?_
  calc dyadicWeight s k * b (2 ^ k) ≤ ((2 ^ k + 1 : ℕ) : ℝ≥0∞) ^ s * b (2 ^ k) := by
        rw [← natCast_two_pow_rpow]; gcongr; exact_mod_cast Nat.le_succ _
    _ ≤ _ := le_iSup (fun n => ((n + 1 : ℕ) : ℝ≥0∞) ^ s * b n) (2 ^ k)

end ENNReal
