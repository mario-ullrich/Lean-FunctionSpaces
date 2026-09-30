/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `ℓ_q` norms of sequences in `ℝ≥0∞`

For a sequence `a : ℕ → ℝ≥0∞` and `q ∈ [1, ∞]`,

`lqNorm q a = (∑ₙ a n ^ q) ^ (1/q)`   for `q < ∞`,   `lqNorm ∞ a = supₙ a n`.

**Why `ℝ≥0∞` and why `eLpNorm`.** All quasi-norms of approximation spaces are `ℓ_q` norms of
nonnegative sequences.  In `ℝ≥0∞` every series has a value, possibly `∞`, so no summability
side conditions appear, and membership in a space becomes the statement `lqNorm q a < ∞`.
This is Mathlib's own design for `L_p` (`MeasureTheory.eLpNorm`, `MeasureTheory.MemLp`).  The
definition is literally `eLpNorm a q Measure.count`, the `L_q` norm for the counting measure
on `ℕ`, so Minkowski's inequality (`MeasureTheory.eLpNorm_add_le`) and monotonicity come for
free from Mathlib.  The alternative, Mathlib's normed space `lp`, would require summability
proofs for every sequence that enters.

The file adds what Mathlib lacks: the explicit formulas, homogeneity for `ℝ≥0∞` scalars,
**monotonicity in `q`** (`lqNorm r a ≤ lqNorm q a` for `1 ≤ q ≤ r`; Mathlib has only the
inclusion `lp.monotone`, without the norm bound), the splitting off of the first term, the
geometric sequence, and the **dyadic weights** `dyadicWeight s k = 2 ^ (k s)` that every
approximation space uses.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ENNReal

/-- The **`ℓ_q` norm** of a sequence in `ℝ≥0∞`: `(∑ₙ a n ^ q) ^ (1/q)` for `q < ∞` and
`supₙ a n` for `q = ∞`, defined as the `L_q` norm for the counting measure. -/
noncomputable def lqNorm (q : ℝ≥0∞) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ := eLpNorm a q Measure.count

variable {q r : ℝ≥0∞} {a b : ℕ → ℝ≥0∞}

/-- Every sequence is measurable for the counting measure; this is the side condition of the
Mathlib lemmas on `eLpNorm`. -/
theorem aestronglyMeasurable_count (a : ℕ → ℝ≥0∞) : AEStronglyMeasurable a Measure.count :=
  measurable_from_nat.aestronglyMeasurable

theorem lqNorm_top (a : ℕ → ℝ≥0∞) : lqNorm ∞ a = ⨆ n, a n := by
  simp [lqNorm, eLpNorm_exponent_top (aestronglyMeasurable_count a)]

theorem lqNorm_eq_tsum (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ℕ → ℝ≥0∞) :
    lqNorm q a = (∑' n, a n ^ q.toReal) ^ (1 / q.toReal) := by
  rw [lqNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq (aestronglyMeasurable_count a),
    lintegral_count]
  rfl

theorem lqNorm_one (a : ℕ → ℝ≥0∞) : lqNorm 1 a = ∑' n, a n := by
  simp [lqNorm_eq_tsum one_ne_zero one_ne_top]

/-- For `1 ≤ q < ∞` the exponent `q.toReal` is at least `1`. -/
theorem one_le_toReal_of_one_le (hq : 1 ≤ q) (hq' : q ≠ ∞) : 1 ≤ q.toReal := by
  simpa using ENNReal.toReal_mono hq' hq

/-- The `q`-th power of the norm is the sum of the `q`-th powers. -/
theorem lqNorm_rpow (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ℕ → ℝ≥0∞) :
    lqNorm q a ^ q.toReal = ∑' n, a n ^ q.toReal := by
  have hp : q.toReal ≠ 0 := (ENNReal.toReal_pos hq0 hq).ne'
  rw [lqNorm_eq_tsum hq0 hq, one_div, ENNReal.rpow_inv_rpow hp]

@[simp]
theorem lqNorm_zero_right (q : ℝ≥0∞) : lqNorm q (fun _ => 0) = 0 := eLpNorm_fun_zero

/-- The exponent `0` is degenerate: `eLpNorm` assigns it the value `0`.  All statements below
assume `1 ≤ q`. -/
@[simp]
theorem lqNorm_zero_left (a : ℕ → ℝ≥0∞) : lqNorm 0 a = 0 :=
  eLpNorm_exponent_zero (aestronglyMeasurable_count a)

/-- Every term is bounded by the norm. -/
theorem le_lqNorm (hq : q ≠ 0) (a : ℕ → ℝ≥0∞) (n : ℕ) : a n ≤ lqNorm q a :=
  enorm_le_eLpNorm_count a n hq

theorem lqNorm_mono (h : ∀ n, a n ≤ b n) : lqNorm q a ≤ lqNorm q b :=
  eLpNorm_mono_enorm (aestronglyMeasurable_count a) h

/-- **Minkowski's inequality** for `ℓ_q`, `1 ≤ q ≤ ∞`. -/
theorem lqNorm_add_le (hq : 1 ≤ q) (a b : ℕ → ℝ≥0∞) :
    lqNorm q (fun n => a n + b n) ≤ lqNorm q a + lqNorm q b :=
  eLpNorm_add_le (f := a) (g := b) hq

/-- **Homogeneity**: `‖c a‖_q = c ‖a‖_q` for every `c ∈ ℝ≥0∞`. -/
theorem lqNorm_const_mul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun n => c * a n) = c * lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top, ENNReal.mul_iSup]
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- **Monotonicity in the exponent**: for `1 ≤ q ≤ r`, `‖a‖_r ≤ ‖a‖_q`.  Proof: with
`M = ‖a‖_q`, each term satisfies `a n ^ r ≤ M ^ (r - q) a n ^ q`; sum over `n`. -/
theorem lqNorm_le_lqNorm_of_le (hq : 1 ≤ q) (hqr : q ≤ r) (a : ℕ → ℝ≥0∞) :
    lqNorm r a ≤ lqNorm q a := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  rcases eq_or_ne r ∞ with rfl | hr
  · rw [lqNorm_top]; exact iSup_le (le_lqNorm hq0 a)
  have hq' : q ≠ ∞ := ne_top_of_le_ne_top hr hqr
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le (hq.trans hqr)).ne'
  set M := lqNorm q a
  set p := q.toReal
  set p' := r.toReal
  have hp : 0 < p := ENNReal.toReal_pos hq0 hq'
  have hp' : 0 < p' := ENNReal.toReal_pos hr0 hr
  have hpp' : p ≤ p' := ENNReal.toReal_mono hr hqr
  have key : ∑' n, a n ^ p' ≤ M ^ p' := by
    calc ∑' n, a n ^ p' = ∑' n, a n ^ (p' - p) * a n ^ p := by
          congr 1; funext n
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) hp.le, sub_add_cancel]
      _ ≤ ∑' n, M ^ (p' - p) * a n ^ p := by
          gcongr with n
          exact le_lqNorm hq0 a n
      _ = M ^ (p' - p) * M ^ p := by rw [ENNReal.tsum_mul_left, lqNorm_rpow hq0 hq' a]
      _ = M ^ p' := by rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) hp.le, sub_add_cancel]
  rw [lqNorm_eq_tsum hr0 hr, one_div, ENNReal.rpow_inv_le_iff hp']
  exact key

/-- Dropping the first term does not increase the norm. -/
theorem lqNorm_shift_le (a : ℕ → ℝ≥0∞) : lqNorm q (fun n => a (n + 1)) ≤ lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top]; exact iSup_le fun n => le_iSup a (n + 1)
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  exact ENNReal.rpow_le_rpow
    (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 1) (fun n => a n ^ q.toReal))
    (by positivity)

/-- **Splitting off the first term**: `‖a‖_q ≤ a 0 + ‖(a (n + 1))ₙ‖_q`. -/
theorem lqNorm_le_head_add_shift (hq : 1 ≤ q) (a : ℕ → ℝ≥0∞) :
    lqNorm q a ≤ a 0 + lqNorm q (fun n => a (n + 1)) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  set e : ℕ → ℝ≥0∞ := fun n => if n = 0 then a 0 else 0
  set b : ℕ → ℝ≥0∞ := fun n => if n = 0 then 0 else a n
  have hab : a = fun n => e n + b n := by
    funext n; rcases n with _ | n <;> simp [e, b]
  have he : lqNorm q e ≤ a 0 := by
    rcases eq_or_ne q ∞ with rfl | hq'
    · rw [lqNorm_top]; exact iSup_le fun n => by simp only [e]; split_ifs <;> simp
    have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq'
    rw [lqNorm_eq_tsum hq0 hq']
    have : ∑' n, e n ^ q.toReal = a 0 ^ q.toReal := by
      rw [tsum_eq_single 0 fun n hn => by simp [e, hn, ENNReal.zero_rpow_of_pos hp]]
      simp [e]
    rw [this, one_div, ENNReal.rpow_rpow_inv hp.ne']
  have hb : lqNorm q b = lqNorm q (fun n => a (n + 1)) := by
    rcases eq_or_ne q ∞ with rfl | hq'
    · rw [lqNorm_top, lqNorm_top]
      apply le_antisymm
      · exact iSup_le fun n => by
          rcases n with _ | n
          · simp [b]
          · simpa [b] using le_iSup (fun n => a (n + 1)) n
      · exact iSup_le fun n => by simpa [b] using le_iSup b (n + 1)
    have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq'
    rw [lqNorm_eq_tsum hq0 hq', lqNorm_eq_tsum hq0 hq',
      tsum_eq_zero_add' ENNReal.summable]
    simp [b, ENNReal.zero_rpow_of_pos hp]
  calc lqNorm q a = lqNorm q (fun n => e n + b n) := by rw [← hab]
    _ ≤ lqNorm q e + lqNorm q b := lqNorm_add_le hq e b
    _ ≤ a 0 + lqNorm q (fun n => a (n + 1)) := by rw [hb]; gcongr

/-- The norm of a geometric sequence: `‖(r ^ k)ₖ‖_q ≤ (1 - r)⁻¹`, the value of the series
for `q = 1`. -/
theorem lqNorm_geometric_le (hq : 1 ≤ q) (r : ℝ≥0∞) :
    lqNorm q (fun k => r ^ k) ≤ (1 - r)⁻¹ := by
  calc lqNorm q (fun k => r ^ k) ≤ lqNorm 1 (fun k => r ^ k) := lqNorm_le_lqNorm_of_le le_rfl hq _
    _ = (1 - r)⁻¹ := by rw [lqNorm_one, ENNReal.tsum_geometric]

theorem lqNorm_le_lqNorm_one (hq : 1 ≤ q) (a : ℕ → ℝ≥0∞) : lqNorm q a ≤ ∑' n, a n := by
  simpa [lqNorm_one] using lqNorm_le_lqNorm_of_le le_rfl hq a

/-! ### Dyadic weights -/

/-- The **dyadic weight** `2 ^ (k s)`: the factor by which the error `E_{2^k}` is multiplied
in the dyadic form of an approximation space of smoothness `s`. -/
noncomputable def dyadicWeight (s : ℝ) (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((k : ℝ) * s)

variable {s t : ℝ}

@[simp]
theorem dyadicWeight_zero_right (s : ℝ) : dyadicWeight s 0 = 1 := by simp [dyadicWeight]

@[simp]
theorem dyadicWeight_zero_left (k : ℕ) : dyadicWeight 0 k = 1 := by simp [dyadicWeight]

theorem dyadicWeight_ne_top (s : ℝ) (k : ℕ) : dyadicWeight s k ≠ ∞ :=
  ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top

theorem dyadicWeight_lt_top (s : ℝ) (k : ℕ) : dyadicWeight s k < ∞ :=
  (dyadicWeight_ne_top s k).lt_top

theorem dyadicWeight_pos (s : ℝ) (k : ℕ) : 0 < dyadicWeight s k :=
  ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top

theorem dyadicWeight_ne_zero (s : ℝ) (k : ℕ) : dyadicWeight s k ≠ 0 := (dyadicWeight_pos s k).ne'

theorem dyadicWeight_add (s t : ℝ) (k : ℕ) :
    dyadicWeight (s + t) k = dyadicWeight s k * dyadicWeight t k := by
  rw [dyadicWeight, mul_add, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]; rfl

theorem dyadicWeight_add_nat (s : ℝ) (k j : ℕ) :
    dyadicWeight s (k + j) = dyadicWeight s k * dyadicWeight s j := by
  rw [dyadicWeight, Nat.cast_add, add_mul, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  rfl

theorem dyadicWeight_succ (s : ℝ) (k : ℕ) :
    dyadicWeight s (k + 1) = 2 ^ s * dyadicWeight s k := by
  rw [dyadicWeight_add_nat, mul_comm]; simp [dyadicWeight]

theorem dyadicWeight_neg (s : ℝ) (k : ℕ) : dyadicWeight (-s) k = (dyadicWeight s k)⁻¹ := by
  rw [dyadicWeight, mul_neg, ENNReal.rpow_neg]; rfl

theorem dyadicWeight_neg_mul_self (s : ℝ) (k : ℕ) : dyadicWeight (-s) k * dyadicWeight s k = 1 := by
  rw [dyadicWeight_neg, ENNReal.inv_mul_cancel (dyadicWeight_ne_zero s k) (dyadicWeight_ne_top s k)]

theorem dyadicWeight_mul_neg_self (s : ℝ) (k : ℕ) : dyadicWeight s k * dyadicWeight (-s) k = 1 := by
  rw [mul_comm, dyadicWeight_neg_mul_self]

theorem dyadicWeight_rpow (s p : ℝ) (k : ℕ) : dyadicWeight s k ^ p = dyadicWeight (s * p) k := by
  rw [dyadicWeight, dyadicWeight, ← ENNReal.rpow_mul, mul_assoc]

/-- The dyadic weights are a geometric sequence with ratio `2 ^ s`. -/
theorem dyadicWeight_eq_pow (s : ℝ) (k : ℕ) : dyadicWeight s k = ((2 : ℝ≥0∞) ^ s) ^ k := by
  rw [dyadicWeight, mul_comm, ENNReal.rpow_mul_natCast]

theorem dyadicWeight_mono (hs : 0 ≤ s) : Monotone (dyadicWeight s) := fun _ _ hkj =>
  ENNReal.rpow_le_rpow_of_exponent_le one_le_two
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hkj) hs)

/-- `(2 ^ k) ^ s = 2 ^ (k s)`: the dyadic weight is the power weight at the dyadic point. -/
theorem natCast_two_pow_rpow (s : ℝ) (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ≥0∞) ^ s = dyadicWeight s k := by
  rw [dyadicWeight, ENNReal.rpow_natCast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- For `α > 0` the ratio `2 ^ (-α)` of the decaying weights is `< 1`. -/
theorem two_rpow_neg_lt_one {α : ℝ} (hα : 0 < α) : (2 : ℝ≥0∞) ^ (-α) < 1 :=
  ENNReal.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_iff_pos.2 hα)

/-- The constant `(1 - 2 ^ (-α))⁻¹` of geometric sums is finite for `α > 0`. -/
theorem one_sub_two_rpow_neg_inv_ne_top {α : ℝ} (hα : 0 < α) : (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ ≠ ∞ := by
  rw [ENNReal.inv_ne_top]
  exact (tsub_pos_of_lt (two_rpow_neg_lt_one hα)).ne'

/-- The constant `(1 - 2 ^ (-α))⁻¹` is at least `1`. -/
theorem one_le_one_sub_two_rpow_neg_inv (α : ℝ) : 1 ≤ (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ :=
  ENNReal.one_le_inv.2 tsub_le_self

/-- `‖(2 ^ (-k α))ₖ‖_q ≤ (1 - 2 ^ (-α))⁻¹`. -/
theorem lqNorm_dyadicWeight_neg_le (hq : 1 ≤ q) (α : ℝ) :
    lqNorm q (dyadicWeight (-α)) ≤ (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ := by
  have : dyadicWeight (-α) = fun k => ((2 : ℝ≥0∞) ^ (-α)) ^ k := funext (dyadicWeight_eq_pow _)
  rw [this]
  exact lqNorm_geometric_le hq _

end ENNReal
