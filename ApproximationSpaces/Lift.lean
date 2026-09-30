/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Embedding
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Lifting approximants: the telescoping argument

Let `ι : Y → X` be a bounded linear map and `A` a scheme in `X`.  A **lifting bound** of
exponent `β` says that every approximant is the image of an element of `Y` of controlled size:

`a ∈ A n, n ≥ 1  ⟹  a = ι y  with  ‖y‖_Y ≤ C n^β ‖a‖_X`   (`ApproximationScheme.LiftBound`).

For `Y` a space of smooth functions this is **Bernstein's inequality** (`β` the smoothness);
for `Y = L_r ⊆ X = L_p` it is **Nikolskii's inequality** (`β = d (1/p - 1/r)`).

Given `f ∈ X`, choose near-best approximants `a_k ∈ A (2^k)` (`DyadicApprox`), so that
`f = a_0 + ∑_k (a_{k+1} - a_k)` with blocks `a_{k+1} - a_k ∈ A (2^(k+2))` of size
`≲ E_{2^k}(f)`.  Lift every block to `Y`: the lifted blocks have size `≲ 2^(kβ) E_{2^k}(f)`, so
if `∑_k 2^(kβ) E_{2^k}(f) < ∞` their series converges in the Banach space `Y` to some `y` with
`ι y = f` (`DyadicApprox.exists_preimage`).  The partial sums of that series lift the
approximants `a_k`, and the tails bound how well `y` is approximated in `Y`.

This single construction yields three theorems: Bernstein implies `A^β_1 ↪ Y`
(`exists_preimage_of_liftBound`, this file), the Nikolskii transfer theorem
(`ApproximationSpaces.Nikolskii`), and one half of the representation theorem.

**Tolerances.** Best approximants need not exist, so `a_k` is only near-best:
`‖f - a_k‖ ≤ E_{2^k}(f) + t_k`.  The tolerances `t_k = ‖f‖ 2^(-k(σ+1))` are chosen so small
that every weighted sum of them that occurs is at most `2 ‖f‖`, which is absorbed into the
final constant; this avoids a limit `ε → 0`.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A **lifting bound** of exponent `β` and constant `C` for `ι : Y → X`: every approximant
`a ∈ A n`, `n ≥ 1`, is `ι y` for some `y` with `‖y‖ ≤ C n^β ‖a‖`.  This is Bernstein's
inequality when `Y` is a smoothness space and Nikolskii's inequality when `Y ⊆ X` is a
smaller Lebesgue space. -/
def LiftBound (ι : Y →L[ℝ] X) (A : ApproximationScheme X) (β C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a ∈ A n, ∃ y : Y, ι y = a ∧ ‖y‖ ≤ C * (n : ℝ) ^ β * ‖a‖

variable {ι : Y →L[ℝ] X} {A : ApproximationScheme X} {β C : ℝ}

/-- The lifting bound in `ℝ≥0∞`. -/
theorem LiftBound.exists_enorm_le (hB : LiftBound ι A β C) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    {a : X} (ha : a ∈ A n) :
    ∃ y : Y, ι y = a ∧ ‖y‖ₑ ≤ ENNReal.ofReal C * (n : ℝ≥0∞) ^ β * ‖a‖ₑ := by
  obtain ⟨y, hy, hle⟩ := hB n hn a ha
  refine ⟨y, hy, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos hn0,
    ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hle

/-- The constant `2 C 4^β` by which a lifted dyadic block exceeds `2^(kβ)` times its error. -/
noncomputable def liftConst (C β : ℝ) : ℝ≥0∞ := 2 * ENNReal.ofReal C * dyadicWeight β 2

theorem liftConst_ne_top (C β : ℝ) : liftConst C β ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (ENNReal.dyadicWeight_ne_top β 2)

/-- A **dyadic sequence of near-best approximants** of `f` with tolerances `t`:
`a k ∈ A (2^k)` and `‖f - a k‖ ≤ E_{2^k}(f) + t k`. -/
structure DyadicApprox (A : ApproximationScheme X) (f : X) (t : ℕ → ℝ≥0∞) where
  /-- The approximant of complexity `2^k`. -/
  a : ℕ → X
  mem : ∀ k, a k ∈ A (2 ^ k)
  enorm_sub_le : ∀ k, ‖f - a k‖ₑ ≤ A.approxSeq f (2 ^ k) + t k

/-- Near-best approximants exist for every choice of positive finite tolerances. -/
theorem exists_dyadicApprox (A : ApproximationScheme X) (f : X) {t : ℕ → ℝ≥0∞}
    (ht0 : ∀ k, t k ≠ 0) (htop : ∀ k, t k ≠ ∞) : Nonempty (A.DyadicApprox f t) := by
  have : ∀ k, ∃ a ∈ A (2 ^ k), ‖f - a‖ₑ ≤ A.approxSeq f (2 ^ k) + t k := fun k => by
    obtain ⟨a, ha, h⟩ :=
      exists_mem_norm_sub_le_add (A := A) (2 ^ k) f (ENNReal.toReal_pos (ht0 k) (htop k))
    refine ⟨a, ha, ?_⟩
    rw [← ofReal_norm, approxSeq, ← ENNReal.ofReal_toReal (htop k),
      ← ENNReal.ofReal_add (approxError_nonneg _ _) ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal h
  choose a ha h using this
  exact ⟨⟨a, ha, h⟩⟩

namespace DyadicApprox

variable {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t)

/-- Consecutive approximants differ by an approximant of complexity `2^(k+2)`. -/
theorem sub_mem (k : ℕ) : D.a (k + 1) - D.a k ∈ A (2 ^ (k + 2)) :=
  sub_mem_pow_add_two (D.mem (k + 1)) (D.mem k)

/-- The blocks are controlled by the errors: `‖a_{k+1} - a_k‖ ≤ 2 (E_{2^k}(f) + t_k)`. -/
theorem enorm_sub_succ_le (ht : Antitone t) (k : ℕ) :
    ‖D.a (k + 1) - D.a k‖ₑ ≤ 2 * (A.approxSeq f (2 ^ k) + t k) := by
  calc ‖D.a (k + 1) - D.a k‖ₑ = ‖(f - D.a k) - (f - D.a (k + 1))‖ₑ := by congr 1; abel
    _ ≤ ‖f - D.a k‖ₑ + ‖f - D.a (k + 1)‖ₑ := _root_.enorm_sub_le
    _ ≤ (A.approxSeq f (2 ^ k) + t k) + (A.approxSeq f (2 ^ (k + 1)) + t (k + 1)) :=
        add_le_add (D.enorm_sub_le k) (D.enorm_sub_le (k + 1))
    _ ≤ (A.approxSeq f (2 ^ k) + t k) + (A.approxSeq f (2 ^ k) + t k) := by
        gcongr
        · exact approxSeq_anti f (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
        · exact ht (Nat.le_succ k)
    _ = 2 * (A.approxSeq f (2 ^ k) + t k) := by ring

theorem enorm_zero_le : ‖D.a 0‖ₑ ≤ 2 * ‖f‖ₑ + t 0 := by
  calc ‖D.a 0‖ₑ = ‖f - (f - D.a 0)‖ₑ := by rw [sub_sub_cancel]
    _ ≤ ‖f‖ₑ + ‖f - D.a 0‖ₑ := _root_.enorm_sub_le
    _ ≤ ‖f‖ₑ + (A.approxSeq f (2 ^ 0) + t 0) := by gcongr; exact D.enorm_sub_le 0
    _ ≤ ‖f‖ₑ + (‖f‖ₑ + t 0) := by gcongr; exact approxSeq_le_enorm f _
    _ = 2 * ‖f‖ₑ + t 0 := by ring

/-- The approximants converge to `f` when the dyadic errors and the tolerances tend to `0`. -/
theorem tendsto (he : Tendsto (fun k => A.approxSeq f (2 ^ k)) atTop (𝓝 0))
    (ht : Tendsto t atTop (𝓝 0)) : Tendsto D.a atTop (𝓝 f) := by
  have h : Tendsto (fun k => ‖f - D.a k‖ₑ) atTop (𝓝 0) := by
    have := he.add ht
    rw [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
      D.enorm_sub_le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def, norm_sub_rev] using this

/-- **Lifting the blocks**: `a_0 = ι y_0` and `a_{k+1} - a_k = ι d_k` with
`‖y_0‖ ≤ C ‖a_0‖` and `‖d_k‖ ≤ C 2^((k+2)β) ‖a_{k+1} - a_k‖`. -/
theorem exists_lift (hB : LiftBound ι A β C) (hC : 0 ≤ C) :
    ∃ y0 : Y, ∃ d : ℕ → Y, ι y0 = D.a 0 ∧ (∀ k, ι (d k) = D.a (k + 1) - D.a k) ∧
      ‖y0‖ₑ ≤ ENNReal.ofReal C * ‖D.a 0‖ₑ ∧
      ∀ k, ‖d k‖ₑ ≤ ENNReal.ofReal C * dyadicWeight β (k + 2) * ‖D.a (k + 1) - D.a k‖ₑ := by
  obtain ⟨y0, hy0, hy0le⟩ := hB.exists_enorm_le hC (n := 2 ^ 0) le_rfl (D.mem 0)
  have : ∀ k, ∃ z : Y, ι z = D.a (k + 1) - D.a k ∧
      ‖z‖ₑ ≤ ENNReal.ofReal C * ((2 ^ (k + 2) : ℕ) : ℝ≥0∞) ^ β * ‖D.a (k + 1) - D.a k‖ₑ :=
    fun k => hB.exists_enorm_le hC Nat.one_le_two_pow (D.sub_mem k)
  choose d hd hdle using this
  refine ⟨y0, d, hy0, hd, by simpa using hy0le, fun k => ?_⟩
  rw [← ENNReal.natCast_two_pow_rpow]
  exact hdle k

include D in
/-- **The telescoping lift.**  If `∑_k 2^(kβ) (E_{2^k}(f) + t_k) < ∞`, then `f = ι y` for some
`y ∈ Y` with

* `‖y‖ ≤ C (2 ‖f‖ + t_0) + K ∑_k 2^(kβ) (E_{2^k}(f) + t_k)`, and
* for every `k` some `z` with `ι z ∈ A (2^k)` and
  `‖y - z‖ ≤ K ∑_{i ≥ 0} 2^((k+i)β) (E_{2^(k+i)}(f) + t_{k+i})`,

where `K = liftConst C β`. -/
theorem exists_preimage [CompleteSpace Y] (ht : Antitone t) (hB : LiftBound ι A β C)
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hsum : ∑' k, dyadicWeight β k * (A.approxSeq f (2 ^ k) + t k) ≠ ∞) :
    ∃ y : Y, ι y = f ∧
      ‖y‖ₑ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + t 0) +
        liftConst C β * ∑' k, dyadicWeight β k * (A.approxSeq f (2 ^ k) + t k) ∧
      ∀ k, ∃ z : Y, ι z ∈ A (2 ^ k) ∧
        ‖y - z‖ₑ ≤ liftConst C β *
          ∑' i, dyadicWeight β (k + i) * (A.approxSeq f (2 ^ (k + i)) + t (k + i)) := by
  obtain ⟨y0, d, hy0, hd, hy0le, hdle⟩ := D.exists_lift hB hC
  set g : ℕ → ℝ≥0∞ := fun k => dyadicWeight β k * (A.approxSeq f (2 ^ k) + t k)
  have hdk : ∀ k, ‖d k‖ₑ ≤ liftConst C β * g k := fun k => by
    calc ‖d k‖ₑ ≤ ENNReal.ofReal C * dyadicWeight β (k + 2) * ‖D.a (k + 1) - D.a k‖ₑ := hdle k
      _ ≤ ENNReal.ofReal C * dyadicWeight β (k + 2) * (2 * (A.approxSeq f (2 ^ k) + t k)) := by
          gcongr; exact D.enorm_sub_succ_le ht k
      _ = liftConst C β * g k := by
          simp only [g, liftConst, ENNReal.dyadicWeight_add_nat]; ring
  have hsumd : ∑' k, ‖d k‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (liftConst_ne_top C β) hsum) ?_
    calc ∑' k, ‖d k‖ₑ ≤ ∑' k, liftConst C β * g k := ENNReal.tsum_le_tsum hdk
      _ = liftConst C β * ∑' k, g k := ENNReal.tsum_mul_left
  have hsd : Summable d := Summable.of_norm (by simpa using ENNReal.summable_toReal hsumd)
  -- the partial sums lift the approximants
  have hpart : ∀ n, ι (y0 + ∑ j ∈ range n, d j) = D.a n := fun n => by
    rw [map_add, map_sum, hy0]
    simp_rw [hd]
    rw [Finset.sum_range_sub (fun k => D.a k) n]
    abel
  -- the errors and the tolerances tend to zero
  have hg : Tendsto g atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hle1 : ∀ k, A.approxSeq f (2 ^ k) + t k ≤ g k := fun k =>
    le_mul_of_one_le_left' (ENNReal.one_le_dyadicWeight hβ k)
  have he : Tendsto (fun k => A.approxSeq f (2 ^ k)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun _ => bot_le)
      fun k => le_self_add.trans (hle1 k)
  have ht0 : Tendsto t atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun _ => bot_le)
      fun k => le_add_self.trans (hle1 k)
  set y := y0 + ∑' k, d k
  have hlim : Tendsto (fun n => ι (y0 + ∑ j ∈ range n, d j)) atTop (𝓝 (ι y)) :=
    (ι.continuous.tendsto y).comp (tendsto_const_nhds.add hsd.hasSum.tendsto_sum_nat)
  simp_rw [hpart] at hlim
  have hy : ι y = f := tendsto_nhds_unique hlim (D.tendsto he ht0)
  refine ⟨y, hy, ?_, fun k => ⟨y0 + ∑ j ∈ range k, d j, by rw [hpart]; exact D.mem k, ?_⟩⟩
  · calc ‖y‖ₑ ≤ ‖y0‖ₑ + ‖∑' k, d k‖ₑ := enorm_add_le _ _
      _ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + t 0) + ∑' k, ‖d k‖ₑ := by
          gcongr
          · exact hy0le.trans (by gcongr; exact D.enorm_zero_le)
          · exact enorm_tsum_le_tsum_enorm
      _ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + t 0) + ∑' k, liftConst C β * g k := by
          gcongr with k; exact hdk k
      _ = _ := by rw [ENNReal.tsum_mul_left]
  · have htail : y - (y0 + ∑ j ∈ range k, d j) = ∑' i, d (i + k) := by
      rw [show y = y0 + ∑' k, d k from rfl,
        ← ((summable_nat_add_iff k).2 hsd).sum_add_tsum_nat_add']
      abel
    rw [htail]
    calc ‖∑' i, d (i + k)‖ₑ ≤ ∑' i, ‖d (i + k)‖ₑ := enorm_tsum_le_tsum_enorm
      _ ≤ ∑' i, liftConst C β * g (k + i) := ENNReal.tsum_le_tsum fun i => by
          rw [add_comm k i]; exact hdk (i + k)
      _ = _ := ENNReal.tsum_mul_left

end DyadicApprox

section Tolerance

variable {E : Type*} [NormedAddCommGroup E]

/-- The tolerances `t_k = ‖f‖ 2^(-k(σ+1))`: positive and finite for `f ≠ 0`, decreasing for
`σ ≥ -1`, and small against every weight `2^(kτ)` with `τ ≤ σ`. -/
noncomputable def tolerance (f : E) (σ : ℝ) (k : ℕ) : ℝ≥0∞ := ‖f‖ₑ * dyadicWeight (-(σ + 1)) k

theorem tolerance_ne_zero {f : E} (hf : f ≠ 0) (σ : ℝ) (k : ℕ) : tolerance f σ k ≠ 0 :=
  mul_ne_zero (enorm_ne_zero.2 hf) (ENNReal.dyadicWeight_ne_zero _ k)

theorem tolerance_ne_top (f : E) (σ : ℝ) (k : ℕ) : tolerance f σ k ≠ ∞ :=
  ENNReal.mul_ne_top enorm_ne_top (ENNReal.dyadicWeight_ne_top _ k)

theorem tolerance_anti (f : E) {σ : ℝ} (hσ : 0 ≤ σ) : Antitone (tolerance f σ) := fun _ _ h => by
  unfold tolerance
  gcongr
  exact ENNReal.dyadicWeight_anti (by linarith) h

@[simp]
theorem tolerance_zero (f : E) (σ : ℝ) : tolerance f σ 0 = ‖f‖ₑ := by simp [tolerance]

/-- `2^(kτ) t_k ≤ ‖f‖ 2^(-k)` for `τ ≤ σ`. -/
theorem dyadicWeight_mul_tolerance_le (f : E) {σ τ : ℝ} (h : τ ≤ σ) (k : ℕ) :
    dyadicWeight τ k * tolerance f σ k ≤ ‖f‖ₑ * dyadicWeight (-1) k := by
  rw [tolerance, mul_left_comm, ← ENNReal.dyadicWeight_add]
  gcongr
  exact ENNReal.dyadicWeight_le_of_le (by linarith) k

theorem tsum_dyadicWeight_mul_tolerance_le (f : E) {σ τ : ℝ} (h : τ ≤ σ) :
    ∑' k, dyadicWeight τ k * tolerance f σ k ≤ 2 * ‖f‖ₑ := by
  calc ∑' k, dyadicWeight τ k * tolerance f σ k ≤ ∑' k, ‖f‖ₑ * dyadicWeight (-1) k :=
        ENNReal.tsum_le_tsum fun k => dyadicWeight_mul_tolerance_le f h k
    _ = 2 * ‖f‖ₑ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg_one, mul_comm]

theorem lqNorm_dyadicWeight_mul_tolerance_le {q : ℝ≥0∞} (hq : 1 ≤ q) (f : E) {σ τ : ℝ}
    (h : τ ≤ σ) : lqNorm q (fun k => dyadicWeight τ k * tolerance f σ k) ≤ 2 * ‖f‖ₑ := by
  calc lqNorm q (fun k => dyadicWeight τ k * tolerance f σ k)
      ≤ lqNorm q (fun k => ‖f‖ₑ * dyadicWeight (-1) k) :=
        ENNReal.lqNorm_mono fun k => dyadicWeight_mul_tolerance_le f h k
    _ = ‖f‖ₑ * lqNorm q (dyadicWeight (-1)) := ENNReal.lqNorm_const_mul _ _
    _ ≤ ‖f‖ₑ * 2 := by gcongr; exact ENNReal.lqNorm_dyadicWeight_neg_one_le hq
    _ = 2 * ‖f‖ₑ := mul_comm _ _

end Tolerance

/-- **A lifting bound of exponent `β` gives `A^β_1 ↪ Y`**: if
`∑_k 2^(kβ) E_{2^k}(f) < ∞`, then `f = ι y` with
`‖y‖ ≤ (3 C + 3 K) (‖f‖ + ∑_k 2^(kβ) E_{2^k}(f))`, `K = liftConst C β`.  For a Bernstein
inequality this is the embedding of the approximation space into the smoothness space. -/
theorem exists_preimage_of_liftBound [CompleteSpace Y] (hB : LiftBound ι A β C) (hC : 0 ≤ C)
    (hβ : 0 ≤ β) {f : X} (hf : lqNorm 1 (A.approxSeqDyadic β f) < ∞) :
    ∃ y : Y, ι y = f ∧
      ‖y‖ₑ ≤ (3 * ENNReal.ofReal C + 3 * liftConst C β) * A.approxNormDyadic β 1 f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero ι, by simp⟩
  set t := tolerance f β
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 β) (tolerance_ne_top f β)
  set L := lqNorm 1 (A.approxSeqDyadic β f)
  have hsplit : ∑' k, dyadicWeight β k * (A.approxSeq f (2 ^ k) + t k) ≤ L + 2 * ‖f‖ₑ := by
    simp_rw [mul_add]
    rw [ENNReal.tsum_add, ← ENNReal.lqNorm_one]
    exact add_le_add le_rfl (tsum_dyadicWeight_mul_tolerance_le f le_rfl)
  have hsum : ∑' k, dyadicWeight β k * (A.approxSeq f (2 ^ k) + t k) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf.ne, ENNReal.mul_ne_top (by norm_num)
      enorm_ne_top⟩) hsplit
  obtain ⟨y, hy, hyle, -⟩ := D.exists_preimage (tolerance_anti f hβ) hB hC hβ hsum
  refine ⟨y, hy, hyle.trans ?_⟩
  rw [tolerance_zero]
  calc ENNReal.ofReal C * (2 * ‖f‖ₑ + ‖f‖ₑ) +
        liftConst C β * ∑' k, dyadicWeight β k * (A.approxSeq f (2 ^ k) + t k)
      ≤ ENNReal.ofReal C * (3 * (‖f‖ₑ + L)) + liftConst C β * (3 * (‖f‖ₑ + L)) := by
        gcongr
        · calc 2 * ‖f‖ₑ + ‖f‖ₑ = 3 * ‖f‖ₑ := by ring
            _ ≤ 3 * (‖f‖ₑ + L) := by gcongr; exact le_self_add
        · calc _ ≤ L + 2 * ‖f‖ₑ := hsplit
            _ ≤ 3 * (‖f‖ₑ + L) := by
                calc L + 2 * ‖f‖ₑ ≤ (‖f‖ₑ + L) + 2 * (‖f‖ₑ + L) := by
                      gcongr
                      · exact le_add_self
                      · exact le_self_add
                  _ = 3 * (‖f‖ₑ + L) := by ring
    _ = (3 * ENNReal.ofReal C + 3 * liftConst C β) * A.approxNormDyadic β 1 f := by
        rw [approxNormDyadic]; ring

end ApproximationScheme
