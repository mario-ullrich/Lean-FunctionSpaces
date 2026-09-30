/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Sequences.Lq
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Discrete Hardy inequalities

For `α > 0`, `1 ≤ q ≤ ∞` and a sequence `b : ℕ → ℝ≥0∞`, with `C_α = (1 - 2^(-α))⁻¹`:

* `hardy_sum_le`:
  `‖(2^(-kα) ∑_{j ≤ k} b j)ₖ‖_q ≤ C_α ‖(2^(-kα) b k)ₖ‖_q`;
* `hardy_tail_le`:
  `‖(2^(kα) ∑_{i ≥ 0} b (k + i))ₖ‖_q ≤ C_α ‖(2^(kα) b k)ₖ‖_q`.

These are the two estimates behind every telescoping argument in approximation theory: the
first controls partial sums of dyadic blocks (Bernstein side), the second controls tails
(Jackson and Nikolskii side).  Both are Young's inequality `‖w * c‖_q ≤ ‖w‖_1 ‖c‖_q` for the
geometric kernel `w i = 2^(-iα)`.  The proof writes the convolution as a series of shifted
copies of `c` and uses the **countable Minkowski inequality** `lqNorm_tsum_le`, which follows
from Mathlib's finite version (`MeasureTheory.eLpNorm_sum_le`) by monotone convergence
(`lqNorm_iSup`).
-/

@[expose] public section

open Finset Filter MeasureTheory
open scoped ENNReal

namespace ENNReal

variable {q : ℝ≥0∞}

/-- **Monotone convergence** for the `ℓ_q` norm: for an increasing sequence of sequences,
the norm of the pointwise supremum is the supremum of the norms. -/
theorem lqNorm_iSup {F : ℕ → ℕ → ℝ≥0∞} (hF : Monotone F) :
    lqNorm q (fun k => ⨆ N, F N k) = ⨆ N, lqNorm q (F N) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne q ∞ with rfl | hq
  · simp_rw [lqNorm_top]; exact iSup_comm
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  simp_rw [lqNorm_eq_tsum hq0 hq]
  have h1 : ∀ k, (⨆ N, F N k) ^ q.toReal = ⨆ N, F N k ^ q.toReal := fun k =>
    (ENNReal.orderIsoRpow q.toReal hp).map_iSup (fun N => F N k)
  have hmono : Monotone fun N k => F N k ^ q.toReal := fun N M h k =>
    ENNReal.rpow_le_rpow (hF h k) hp.le
  have h2 : ∑' k, ⨆ N, F N k ^ q.toReal = ⨆ N, ∑' k, F N k ^ q.toReal := by
    rw [← lintegral_count, lintegral_iSup (fun _ => measurable_from_nat) hmono]
    simp_rw [lintegral_count]
  simp_rw [h1, h2]
  exact (ENNReal.orderIsoRpow (1 / q.toReal) (by positivity)).map_iSup _

/-- **Minkowski's inequality for finite sums** of sequences. -/
theorem lqNorm_sum_le (hq : 1 ≤ q) {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ≥0∞) :
    lqNorm q (fun k => ∑ i ∈ s, f i k) ≤ ∑ i ∈ s, lqNorm q (f i) := by
  have : (fun k => ∑ i ∈ s, f i k) = ∑ i ∈ s, f i := by funext k; simp
  rw [this]
  exact eLpNorm_sum_le hq

/-- **Minkowski's inequality for series** of sequences: the norm of a pointwise sum is at most
the sum of the norms. -/
theorem lqNorm_tsum_le (hq : 1 ≤ q) (f : ℕ → ℕ → ℝ≥0∞) :
    lqNorm q (fun k => ∑' i, f i k) ≤ ∑' i, lqNorm q (f i) := by
  simp_rw [ENNReal.tsum_eq_iSup_nat]
  have hmono : Monotone fun N k => ∑ i ∈ range N, f i k := fun N M h k =>
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  rw [lqNorm_iSup hmono]
  exact iSup_mono fun N => lqNorm_sum_le hq _ f

/-- Dropping the first `i` terms does not increase the norm. -/
theorem lqNorm_shift_le' (i : ℕ) (a : ℕ → ℝ≥0∞) : lqNorm q (fun n => a (n + i)) ≤ lqNorm q a := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc lqNorm q (fun n => a (n + (i + 1))) = lqNorm q (fun n => (fun m => a (m + i)) (n + 1)) := by
          simp only [add_assoc, add_comm 1 i]
      _ ≤ lqNorm q (fun m => a (m + i)) := lqNorm_shift_le (q := q) (fun m => a (m + i))
      _ ≤ lqNorm q a := ih

/-- Shifting a sequence to the right by `i` places, filling with zeros, does not increase the
norm. -/
theorem lqNorm_shiftRight_le (i : ℕ) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => if i ≤ k then a (k - i) else 0) ≤ lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top]
    exact iSup_le fun k => by split_ifs <;> simp [le_iSup a (k - i)]
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  refine ENNReal.rpow_le_rpow (le_of_eq ?_) (by positivity)
  set F : ℕ → ℝ≥0∞ := fun k => (if i ≤ k then a (k - i) else 0) ^ q.toReal
  have hsplit := Summable.sum_add_tsum_nat_add' (f := F) (k := i) ENNReal.summable
  have h0 : ∑ k ∈ range i, F k = 0 :=
    Finset.sum_eq_zero fun k hk => by
      simp [F, not_le.2 (Finset.mem_range.1 hk), ENNReal.zero_rpow_of_pos hp]
  rw [← hsplit, h0, zero_add]
  simp [F]

/-- **Hardy's inequality for tails**: for `α > 0` and `1 ≤ q ≤ ∞`,
`‖(2^(kα) ∑_{i ≥ 0} b (k + i))ₖ‖_q ≤ (1 - 2^(-α))⁻¹ ‖(2^(kα) b k)ₖ‖_q`. -/
theorem hardy_tail_le (hq : 1 ≤ q) (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight α k * ∑' i, b (k + i)) ≤
      (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q (fun k => dyadicWeight α k * b k) := by
  set c : ℕ → ℝ≥0∞ := fun k => dyadicWeight α k * b k
  have hterm : ∀ k, dyadicWeight α k * ∑' i, b (k + i) =
      ∑' i, dyadicWeight (-α) i * c (k + i) := fun k => by
    rw [← ENNReal.tsum_mul_left]
    congr 1; funext i
    simp only [c, dyadicWeight_add_nat, ← mul_assoc]
    rw [mul_comm (dyadicWeight (-α) i), mul_assoc (dyadicWeight α k), dyadicWeight_neg_mul_self,
      mul_one]
  simp_rw [hterm]
  calc lqNorm q (fun k => ∑' i, dyadicWeight (-α) i * c (k + i))
      ≤ ∑' i, lqNorm q (fun k => dyadicWeight (-α) i * c (k + i)) :=
        lqNorm_tsum_le hq (fun i k => dyadicWeight (-α) i * c (k + i))
    _ = ∑' i, dyadicWeight (-α) i * lqNorm q (fun k => c (k + i)) := by
        simp_rw [lqNorm_const_mul]
    _ ≤ ∑' i, dyadicWeight (-α) i * lqNorm q c := by
        gcongr with i; exact lqNorm_shift_le' i c
    _ = (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q c := by
        rw [ENNReal.tsum_mul_right]
        simp_rw [dyadicWeight_eq_pow]
        rw [ENNReal.tsum_geometric]

/-- **Hardy's inequality for partial sums**: for `α > 0` and `1 ≤ q ≤ ∞`,
`‖(2^(-kα) ∑_{j ≤ k} b j)ₖ‖_q ≤ (1 - 2^(-α))⁻¹ ‖(2^(-kα) b k)ₖ‖_q`. -/
theorem hardy_sum_le (hq : 1 ≤ q) (α : ℝ) (b : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight (-α) k * ∑ j ∈ range (k + 1), b j) ≤
      (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q (fun k => dyadicWeight (-α) k * b k) := by
  set c : ℕ → ℝ≥0∞ := fun k => dyadicWeight (-α) k * b k
  set g : ℕ → ℕ → ℝ≥0∞ := fun i k => dyadicWeight (-α) i * (if i ≤ k then c (k - i) else 0)
  have hterm : ∀ k, dyadicWeight (-α) k * ∑ j ∈ range (k + 1), b j = ∑' i, g i k := fun k => by
    rw [tsum_eq_sum (s := range (k + 1)) fun i hi => by
      simp [g, not_le.2 (by simpa using hi : k < i)]]
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hk : k = (k - i) + i := (Nat.sub_add_cancel hik).symm
    simp only [g, c, hik, ↓reduceIte, add_tsub_cancel_right]
    rw [← mul_assoc, ← dyadicWeight_add_nat, add_comm i, ← hk]
  simp_rw [hterm]
  calc lqNorm q (fun k => ∑' i, g i k) ≤ ∑' i, lqNorm q (g i) := lqNorm_tsum_le hq g
    _ = ∑' i, dyadicWeight (-α) i * lqNorm q (fun k => if i ≤ k then c (k - i) else 0) := by
        simp_rw [g, lqNorm_const_mul]
    _ ≤ ∑' i, dyadicWeight (-α) i * lqNorm q c := by
        gcongr with i; exact lqNorm_shiftRight_le i c
    _ = (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm q c := by
        rw [ENNReal.tsum_mul_right]
        simp_rw [dyadicWeight_eq_pow]
        rw [ENNReal.tsum_geometric]

end ENNReal
