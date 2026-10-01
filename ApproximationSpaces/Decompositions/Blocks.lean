/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Lift
public import ApproximationSpaces.Sequences.Hardy

/-!
# Block decompositions

For `s > 0`, `1 ≤ q ≤ ∞` and a Banach space `X`, an element `f` lies in `A^s_q` if and only if
it has a **block decomposition**

`f = ∑_{k ≥ 0} g_k`,   `g_k ∈ A (2^k)`,   `(2^(ks) ‖g_k‖)_k ∈ ℓ_q`

(`memApprox_iff_blockDecompNorm_lt_top`), and the infimum of `‖(2^(ks) ‖g_k‖)_k‖_q` over all
block decompositions (`blockDecompNorm`) is an equivalent quasi-norm
(`approxNormDyadic_le_blockDecompNorm`, `blockDecompNorm_le_approxNormDyadic`).  Each block
`g_k` is a whole level, an approximant of complexity `2^k`.  Atomic decompositions refine every
block into localised atoms with coefficients; wavelet decompositions expand it in a basis.

* Given a decomposition, `∑_{j < k} g_j ∈ A (2^k)`, so `E_{2^k}(f) ≤ ∑_{i ≥ 0} ‖g_{k+i}‖`, and
  Hardy's inequality for tails gives the bound on `‖f‖_{A^s_q}`.
* Conversely, the differences of near-best approximants form a decomposition
  (`g_{k+2} = a_{k+1} - a_k ∈ A (2^(k+2))`), whose norms are controlled by the errors.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

/-- `1 + 2 + ⋯ + 2^(k-1) < 2^k`. -/
theorem sum_range_two_pow_lt (k : ℕ) : ∑ j ∈ range k, 2 ^ j < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

variable (A) in
/-- The **block decomposition quasi-norm**: the infimum of `‖(2^(ks) ‖g_k‖)_k‖_q` over all
block decompositions `f = ∑ g_k` with `g_k ∈ A (2^k)`. -/
noncomputable def blockDecompNorm (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ⨅ (g : ℕ → X) (_ : ∀ k, g k ∈ A (2 ^ k)) (_ : HasSum g f),
    lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ)

/-- Every block decomposition `f = ∑ g_k` with `g_k ∈ A_{2^k}` bounds the block decomposition
quasi-norm. -/
theorem blockDecompNorm_le {f : X} {g : ℕ → X} (hg : ∀ k, g k ∈ A (2 ^ k)) (hf : HasSum g f) :
    A.blockDecompNorm s q f ≤ lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ) :=
  iInf₂_le_of_le g hg (iInf_le_of_le hf le_rfl)

/-- The partial sums of a block decomposition are approximants: `∑_{j<k} g_j ∈ A (2^k)`. -/
theorem sum_range_mem {g : ℕ → X} (hg : ∀ k, g k ∈ A (2 ^ k)) (k : ℕ) :
    ∑ j ∈ range k, g j ∈ A (2 ^ k) :=
  A.mem_of_le (sum_range_two_pow_lt k).le (sum_mem (range k) fun j _ => hg j)

/-- **A block decomposition controls the approximation norm**: for `s > 0`,
`‖f‖^dyadic ≤ 2 (1 - 2^(-s))⁻¹ ‖(2^(ks) ‖g_k‖)_k‖_q`. -/
theorem approxNormDyadic_le_of_hasSum (hq : 1 ≤ q) {f : X} {g : ℕ → X}
    (hg : ∀ k, g k ∈ A (2 ^ k)) (hf : HasSum g f) :
    A.approxNormDyadic s q f ≤
      2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ) := by
  set Cs := (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹
  set L := lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ)
  have htail : ∀ k, ‖f - ∑ j ∈ range k, g j‖ₑ ≤ ∑' i, ‖g (k + i)‖ₑ := fun k => by
    rw [← hf.tsum_eq, ← ((summable_nat_add_iff k).2 hf.summable).sum_add_tsum_nat_add',
      add_sub_cancel_left]
    calc ‖∑' i, g (i + k)‖ₑ ≤ ∑' i, ‖g (i + k)‖ₑ := enorm_tsum_le_tsum_enorm
      _ = ∑' i, ‖g (k + i)‖ₑ := by simp_rw [add_comm]
  have hD : lqNorm q (A.approxSeqDyadic s f) ≤ Cs * L := by
    calc lqNorm q (A.approxSeqDyadic s f)
        ≤ lqNorm q (fun k => dyadicWeight s k * ∑' i, ‖g (k + i)‖ₑ) :=
          ENNReal.lqNorm_mono fun k => by
            rw [approxSeqDyadic]; gcongr
            exact (approxSeq_le_of_mem (sum_range_mem hg k) f).trans (htail k)
      _ ≤ Cs * L := ENNReal.hardy_tail_le hq s (fun m => ‖g m‖ₑ)
  have hf' : ‖f‖ₑ ≤ Cs * L := by
    have hsup : ∀ i, dyadicWeight s i * ‖g i‖ₑ ≤ L := fun i =>
      ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne' (fun k => dyadicWeight s k * ‖g k‖ₑ) i
    calc ‖f‖ₑ = ‖f - ∑ j ∈ range 0, g j‖ₑ := by simp
      _ ≤ ∑' i, ‖g (0 + i)‖ₑ := htail 0
      _ = ∑' i, dyadicWeight (-s) i * (dyadicWeight s i * ‖g i‖ₑ) := by
          congr 1; funext i
          rw [zero_add, ← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
      _ ≤ ∑' i, dyadicWeight (-s) i * L := ENNReal.tsum_le_tsum fun i => by gcongr; exact hsup i
      _ = Cs * L := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_dyadicWeight_neg]
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ Cs * L + Cs * L := add_le_add hf' hD
    _ = 2 * Cs * L := by ring

/-- **The block decomposition quasi-norm controls the approximation norm**, `s > 0`. -/
theorem approxNormDyadic_le_blockDecompNorm (hs : 0 < s) (hq : 1 ≤ q) (f : X) :
    A.approxNormDyadic s q f ≤ 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * A.blockDecompNorm s q f := by
  have h : 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)
  have h0 : 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ ≠ 0 :=
    mul_ne_zero two_ne_zero (zero_lt_one.trans_le (ENNReal.one_le_one_sub_two_rpow_neg_inv s)).ne'
  rw [blockDecompNorm, ENNReal.mul_iInf_of_ne h0 h]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne h0 h]
  refine le_iInf fun hg => ?_
  rw [ENNReal.mul_iInf_of_ne h0 h]
  exact le_iInf fun hf => approxNormDyadic_le_of_hasSum hq hg hf

/-- The block decomposition built from near-best approximants: `g 0 = 0`, `g 1 = a 0` and
`g (k + 2) = a (k + 1) - a k`. -/
noncomputable def DyadicApprox.blocks {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) : ℕ → X
  | 0 => 0
  | 1 => D.a 0
  | k + 2 => D.a (k + 1) - D.a k

/-- The blocks of a dyadic approximation lie in the right sets: `g_k ∈ A_{2^k}`. -/
theorem DyadicApprox.blocks_mem {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (k : ℕ) :
    D.blocks k ∈ A (2 ^ k) := by
  match k with
  | 0 => exact A.zero_mem _
  | 1 => exact A.mem_of_le (by norm_num) (D.mem 0)
  | k + 2 => exact D.sub_mem k

/-- The partial sums of the blocks are the approximants: `∑_{j < K+2} g_j = a_K`. -/
theorem DyadicApprox.sum_range_blocks {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (K : ℕ) :
    ∑ j ∈ range (K + 2), D.blocks j = D.a K := by
  induction K with
  | zero => simp [Finset.sum_range_succ, DyadicApprox.blocks]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [DyadicApprox.blocks]
    abel

/-- **The block decomposition of near-best approximants**: for tolerances `t` that decrease, tend to
`0`, start at most at `‖f‖` and satisfy `∑ t_k ≤ 2 ‖f‖` and `‖(2^(ks) t_k)_k‖_q ≤ 2 ‖f‖`, the
blocks of a dyadic approximation of `f ∈ A^s_q` form a block decomposition of `f` with
`‖(2^(ks) ‖g_k‖)_k‖_q ≤ 3·2^s ‖f‖ + 2·4^s (‖(2^(ks) E_{2^k}(f))_k‖_q + 2 ‖f‖)`. -/
theorem DyadicApprox.blockDecompNorm_le [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (ht : Antitone t)
    (ht0 : t 0 ≤ ‖f‖ₑ) (htend : Tendsto t atTop (𝓝 0)) (htsum : ∑' k, t k ≤ 2 * ‖f‖ₑ)
    (htq : lqNorm q (fun k => dyadicWeight s k * t k) ≤ 2 * ‖f‖ₑ) :
    A.blockDecompNorm s q f ≤ 2 ^ s * (3 * ‖f‖ₑ) +
      2 * dyadicWeight s 2 * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ) := by
  have hg : ∀ k, ‖D.blocks (k + 2)‖ₑ ≤ 2 * (A.approxSeq f (2 ^ k) + t k) := fun k =>
    D.enorm_sub_succ_le ht k
  have hg1 : ‖D.blocks 1‖ₑ ≤ 3 * ‖f‖ₑ :=
    calc ‖D.blocks 1‖ₑ = ‖D.a 0‖ₑ := rfl
      _ ≤ 2 * ‖f‖ₑ + t 0 := D.enorm_zero_le
      _ ≤ 2 * ‖f‖ₑ + ‖f‖ₑ := by gcongr
      _ = 3 * ‖f‖ₑ := by ring
  -- summability of the blocks
  have hE1 : lqNorm 1 (A.approxSeqDyadic 0 f) < ∞ := hf.lqNorm_one_lt_top hq le_rfl hs
  have htail : ∑' k, ‖D.blocks (k + 2)‖ₑ ≠ ∞ := by
    have hfin : 2 * (lqNorm 1 (A.approxSeqDyadic 0 f) + 2 * ‖f‖ₑ) ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.2
        ⟨hE1.ne, ENNReal.mul_ne_top (by norm_num) enorm_ne_top⟩)
    refine ne_top_of_le_ne_top hfin ?_
    calc ∑' k, ‖D.blocks (k + 2)‖ₑ ≤ ∑' k, 2 * (A.approxSeq f (2 ^ k) + t k) :=
          ENNReal.tsum_le_tsum hg
      _ = 2 * (∑' k, A.approxSeqDyadic 0 f k + ∑' k, t k) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]; simp [approxSeqDyadic]
      _ ≤ 2 * (lqNorm 1 (A.approxSeqDyadic 0 f) + 2 * ‖f‖ₑ) := by
          rw [ENNReal.lqNorm_one]; gcongr
  have hsum : Summable D.blocks :=
    (summable_nat_add_iff 2).1 (Summable.of_norm (by simpa using ENNReal.summable_toReal htail))
  -- the blocks add up to `f`
  have he : Tendsto (fun k => A.approxSeq f (2 ^ k)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_approxError_pow_zero_of_memApprox hq hs hf)
    simpa [approxSeq] using this
  have hlim : HasSum D.blocks f := by
    have h2 : Tendsto (fun K => ∑ j ∈ range (K + 2), D.blocks j) atTop (𝓝 (∑' k, D.blocks k)) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
    simp_rw [D.sum_range_blocks] at h2
    have hfeq : f = ∑' k, D.blocks k := tendsto_nhds_unique (D.tendsto he htend) h2
    exact (congrArg (HasSum D.blocks) hfeq).mpr hsum.hasSum
  -- the norm of the decomposition
  refine (ApproximationScheme.blockDecompNorm_le D.blocks_mem hlim).trans ?_
  refine ((ENNReal.lqNorm_le_head_add_shift hq _).trans (add_le_add le_rfl
    (ENNReal.lqNorm_le_head_add_shift hq _))).trans ?_
  have h0 : dyadicWeight s 0 * ‖D.blocks 0‖ₑ = 0 := by simp [DyadicApprox.blocks]
  have h1 : dyadicWeight s (0 + 1) * ‖D.blocks (0 + 1)‖ₑ ≤ 2 ^ s * (3 * ‖f‖ₑ) := by
    rw [zero_add, ENNReal.dyadicWeight_succ, ENNReal.dyadicWeight_zero_right, mul_one]
    gcongr
  have h2 : lqNorm q (fun k => dyadicWeight s (k + 1 + 1) * ‖D.blocks (k + 1 + 1)‖ₑ) ≤
      2 * dyadicWeight s 2 * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ) := by
    calc lqNorm q (fun k => dyadicWeight s (k + 1 + 1) * ‖D.blocks (k + 1 + 1)‖ₑ)
        ≤ lqNorm q (fun k => 2 * dyadicWeight s 2 *
            (A.approxSeqDyadic s f k + dyadicWeight s k * t k)) :=
          ENNReal.lqNorm_mono fun k => by
            calc dyadicWeight s (k + 1 + 1) * ‖D.blocks (k + 2)‖ₑ
                ≤ dyadicWeight s (k + 2) * (2 * (A.approxSeq f (2 ^ k) + t k)) := by
                  gcongr; exact hg k
              _ = _ := by rw [ENNReal.dyadicWeight_add_nat, approxSeqDyadic]; ring
      _ = 2 * dyadicWeight s 2 *
            lqNorm q (fun k => A.approxSeqDyadic s f k + dyadicWeight s k * t k) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ _ := by
          gcongr
          exact (ENNReal.lqNorm_add_le hq _ _).trans (add_le_add le_rfl htq)
  rw [h0, zero_add]
  exact add_le_add h1 h2

/-- **The approximation norm controls the block decomposition quasi-norm**: in a Banach space and for
`s > 0`, `inf ‖(2^(ks) ‖g_k‖)_k‖_q ≤ (3·2^s + 4·4^s) ‖f‖^dyadic`. -/
theorem blockDecompNorm_le_approxNormDyadic [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) (f : X) :
    A.blockDecompNorm s q f ≤ (3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f := by
  by_cases hf : A.MemApprox s q f
  swap
  · rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le, not_lt, top_le_iff] at hf
    rw [hf, ENNReal.mul_top (by positivity)]; exact le_top
  rcases eq_or_ne f 0 with rfl | hf0
  · refine (blockDecompNorm_le (g := fun _ => 0) (fun k => A.zero_mem _) hasSum_zero).trans ?_
    simp
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 s) (tolerance_ne_top f s)
  have htend : Tendsto (tolerance f s) atTop (𝓝 0) := by
    have hr : (2 : ℝ≥0∞) ^ (-(s + 1)) < 1 := ENNReal.two_rpow_neg_lt_one (by linarith)
    have hgeo := ENNReal.Tendsto.const_mul (a := ‖f‖ₑ)
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr enorm_ne_top)
    rw [mul_zero] at hgeo
    refine hgeo.congr fun k => ?_
    rw [tolerance, ENNReal.dyadicWeight_eq_pow]
  have htsum : ∑' k, tolerance f s k ≤ 2 * ‖f‖ₑ := by
    have := tsum_dyadicWeight_mul_tolerance_le (σ := s) (τ := 0) f hs.le
    simp only [ENNReal.dyadicWeight_zero_left, one_mul] at this
    exact this
  have h := D.blockDecompNorm_le hs hq hf (tolerance_anti f hs.le) (tolerance_zero f s).le htend htsum
    (lqNorm_dyadicWeight_mul_tolerance_le hq f le_rfl)
  refine h.trans ?_
  have hfN : ‖f‖ₑ ≤ A.approxNormDyadic s q f := enorm_le_approxNormDyadic f
  have hDN : lqNorm q (A.approxSeqDyadic s f) + ‖f‖ₑ = A.approxNormDyadic s q f := by
    rw [approxNormDyadic, add_comm]
  calc 2 ^ s * (3 * ‖f‖ₑ) + 2 * dyadicWeight s 2 * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ)
      = 2 ^ s * (3 * ‖f‖ₑ) + 2 * dyadicWeight s 2 *
          ((lqNorm q (A.approxSeqDyadic s f) + ‖f‖ₑ) + ‖f‖ₑ) := by ring
    _ ≤ 2 ^ s * (3 * A.approxNormDyadic s q f) + 2 * dyadicWeight s 2 *
          (A.approxNormDyadic s q f + A.approxNormDyadic s q f) := by
        rw [hDN]; gcongr
    _ = (3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f := by ring

/-- **The characterisation of `A^s_q` by block decompositions**: in a Banach space, for
`s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `f = ∑ g_k` with `g_k ∈ A (2^k)` and
`(2^(ks) ‖g_k‖)_k ∈ ℓ_q`. -/
theorem memApprox_iff_blockDecompNorm_lt_top [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) {f : X} :
    A.MemApprox s q f ↔ A.blockDecompNorm s q f < ∞ := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le]
  constructor
  · intro h
    exact (blockDecompNorm_le_approxNormDyadic hs hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
        (ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top).lt_top,
        ENNReal.mul_lt_top (by norm_num) (ENNReal.dyadicWeight_lt_top s 2)⟩) h)
  · intro h
    exact (approxNormDyadic_le_blockDecompNorm hs hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs).lt_top) h)

end ApproximationScheme
