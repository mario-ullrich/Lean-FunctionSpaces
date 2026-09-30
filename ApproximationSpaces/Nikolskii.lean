/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Lift
public import ApproximationSpaces.Sequences.Hardy

/-!
# The Nikolskii transfer theorem

Let `ι : Y → X` be an injective bounded linear map between Banach spaces, `A` a scheme in
`X` whose approximants lie in `ι(Y)`, and suppose the **Nikolskii inequality**

`a ∈ A n, n ≥ 1  ⟹  a = ι y  with  ‖y‖_Y ≤ C n^α ‖a‖_X`

(`LiftBound ι A α C`).  Pull the scheme back to `Y`, `B n = ι⁻¹(A n)`.  Then for `0 ≤ α < s`
and `1 ≤ q ≤ ∞`, every `f ∈ A^s_q(X)` is `f = ι y` for some `y ∈ B^{s-α}_q(Y)`, with

`‖y‖_{B^{s-α}_q} ≤ K ‖f‖_{A^s_q}`,   `K = nikolskiiConst C α s`

in the dyadic quasi-norms (`exists_preimage_of_nikolskii`).  The typical case is
`X = L_p ⊇ Y = L_r` with `p < r` and `α = d (1/p - 1/r)`: a function in the Besov space
`B^s_{p,q}` with `s > d(1/p - 1/r)` is in `L_r` and belongs to `B^{s - d(1/p-1/r)}_{r,q}`.
`ι` is the inclusion `L_r → L_p`, which is not surjective, so `f` is *a priori* only an
element of `L_p`; the theorem constructs its `L_r` version.

**Proof.** The telescoping lift of `ApproximationSpaces.Lift` gives `y = y_0 + ∑_k d_k` in `Y`
whose partial sums `z_k` lie in `B (2^k)`.  So `E^B_{2^k}(y) ≤ ‖y - z_k‖ ≤ ∑_{i ≥ k} ‖d_i‖` and
`‖d_i‖ ≲ 2^(iα) E_{2^i}(f)`; Hardy's inequality for tails with exponent `s - α > 0`
(`ENNReal.hardy_tail_le`) converts this into the bound on `‖(2^(k(s-α)) E^B_{2^k}(y))_k‖_q`.
The strict inequality `α < s` is needed for Hardy's inequality and for the convergence of the
series; the limiting case `α = s` is false in general.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {ι : Y →L[ℝ] X} {A : ApproximationScheme X} {α C s : ℝ} {q : ℝ≥0∞}

/-- The constant of the Nikolskii transfer theorem,
`3 C + 3 K (1 - 2^(-(s-α)))⁻¹ + 2 K` with `K = liftConst C α`. -/
noncomputable def nikolskiiConst (C α s : ℝ) : ℝ≥0∞ :=
  3 * ENNReal.ofReal C + 3 * liftConst C α * (1 - (2 : ℝ≥0∞) ^ (-(s - α)))⁻¹ + 2 * liftConst C α

theorem nikolskiiConst_ne_top (C : ℝ) (h : α < s) : nikolskiiConst C α s ≠ ∞ := by
  have h1 : liftConst C α ≠ ∞ := liftConst_ne_top C α
  have h2 := ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 h)
  unfold nikolskiiConst
  exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h1) h2⟩,
    ENNReal.mul_ne_top (by norm_num) h1⟩

/-- **The Nikolskii transfer theorem.**  For an injective `ι : Y → X` with a Nikolskii
inequality of exponent `α` for `A`, `0 ≤ α < s` and `1 ≤ q ≤ ∞`, every `f ∈ A^s_q(X)` is
`ι y` for some `y ∈ Y` with `‖y‖_{B^{s-α}_q} ≤ K ‖f‖_{A^s_q}` (dyadic quasi-norms), where `B`
is the scheme `ι⁻¹(A n)` in `Y`. -/
theorem exists_preimage_of_nikolskii [CompleteSpace Y] (hι : Function.Injective ι)
    (hN : LiftBound ι A α C) (hC : 0 ≤ C) (hα : 0 ≤ α) (hαs : α < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) :
    ∃ y : Y, ι y = f ∧ (A.comap ι.toLinearMap hι).approxNormDyadic (s - α) q y ≤
      nikolskiiConst C α s * A.approxNormDyadic s q f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero ι, by simp⟩
  have hs : 0 ≤ s := hα.trans hαs.le
  set B := A.comap ι.toLinearMap hι
  set t := tolerance f s
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 s) (tolerance_ne_top f s)
  set N := A.approxNormDyadic s q f
  set Cs := (1 - (2 : ℝ≥0∞) ^ (-(s - α)))⁻¹
  set K := liftConst C α
  set g : ℕ → ℝ≥0∞ := fun m => dyadicWeight α m * (A.approxSeq f (2 ^ m) + t m)
  have hfN : ‖f‖ₑ ≤ N := enorm_le_approxNormDyadic f
  have hL : lqNorm 1 (A.approxSeqDyadic α f) ≤ Cs * N :=
    (lqNorm_le_approxNormDyadic f).trans (approxNormDyadic_le_of_lt hq le_rfl f)
  have hsplit : ∑' k, g k ≤ lqNorm 1 (A.approxSeqDyadic α f) + 2 * ‖f‖ₑ := by
    simp_rw [g, mul_add]
    rw [ENNReal.tsum_add, ← ENNReal.lqNorm_one]
    exact add_le_add le_rfl (tsum_dyadicWeight_mul_tolerance_le f hαs.le)
  have hsum : ∑' k, g k ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨(hf.lqNorm_one_lt_top hq hα hαs).ne,
      ENNReal.mul_ne_top (by norm_num) enorm_ne_top⟩) hsplit
  obtain ⟨y, hy, hyle, htail⟩ := D.exists_preimage (tolerance_anti f hs) hN hC hα hsum
  refine ⟨y, hy, ?_⟩
  -- the dyadic errors of `y` for the pulled-back scheme
  have herr : ∀ k, B.approxSeqDyadic (s - α) y k ≤
      K * (dyadicWeight (s - α) k * ∑' i, g (k + i)) := fun k => by
    obtain ⟨z, hz, hzle⟩ := htail k
    calc B.approxSeqDyadic (s - α) y k = dyadicWeight (s - α) k * B.approxSeq y (2 ^ k) := rfl
      _ ≤ dyadicWeight (s - α) k * ‖y - z‖ₑ := by
          gcongr; exact approxSeq_le_of_mem (A.mem_comap.2 hz) y
      _ ≤ dyadicWeight (s - α) k * (K * ∑' i, g (k + i)) := by gcongr
      _ = K * (dyadicWeight (s - α) k * ∑' i, g (k + i)) := by ring
  have hg : ∀ k, dyadicWeight (s - α) k * g k =
      A.approxSeqDyadic s f k + dyadicWeight s k * t k := fun k => by
    simp only [g, approxSeqDyadic, ← mul_assoc, ← ENNReal.dyadicWeight_add, sub_add_cancel,
      mul_add]
  have hlq : lqNorm q (B.approxSeqDyadic (s - α) y) ≤ K * (Cs * (2 * N)) := by
    calc lqNorm q (B.approxSeqDyadic (s - α) y)
        ≤ lqNorm q (fun k => K * (dyadicWeight (s - α) k * ∑' i, g (k + i))) :=
          ENNReal.lqNorm_mono herr
      _ = K * lqNorm q (fun k => dyadicWeight (s - α) k * ∑' i, g (k + i)) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ K * (Cs * lqNorm q (fun k => dyadicWeight (s - α) k * g k)) := by
          gcongr; exact ENNReal.hardy_tail_le hq (s - α) g
      _ ≤ K * (Cs * (2 * N)) := by
          gcongr
          simp_rw [hg]
          calc lqNorm q (fun k => A.approxSeqDyadic s f k + dyadicWeight s k * t k)
              ≤ lqNorm q (A.approxSeqDyadic s f) + lqNorm q (fun k => dyadicWeight s k * t k) :=
                ENNReal.lqNorm_add_le hq _ _
            _ ≤ lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ := by
                gcongr; exact lqNorm_dyadicWeight_mul_tolerance_le hq f le_rfl
            _ ≤ 2 * N := by
                calc lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ
                    ≤ 2 * lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ := by
                      gcongr; exact le_mul_of_one_le_left' one_le_two
                  _ = 2 * N := by
                      rw [show N = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) from rfl]; ring
  have hnorm : ‖y‖ₑ ≤ (3 * ENNReal.ofReal C + K * Cs + 2 * K) * N := by
    calc ‖y‖ₑ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + t 0) + K * ∑' k, g k := hyle
      _ ≤ ENNReal.ofReal C * (3 * N) + K * (Cs * N + 2 * N) := by
          rw [show t 0 = ‖f‖ₑ from tolerance_zero f s]
          gcongr
          · calc 2 * ‖f‖ₑ + ‖f‖ₑ = 3 * ‖f‖ₑ := by ring
              _ ≤ 3 * N := by gcongr
          · exact hsplit.trans (add_le_add hL (by gcongr))
      _ = (3 * ENNReal.ofReal C + K * Cs + 2 * K) * N := by ring
  calc B.approxNormDyadic (s - α) q y = ‖y‖ₑ + lqNorm q (B.approxSeqDyadic (s - α) y) := rfl
    _ ≤ (3 * ENNReal.ofReal C + K * Cs + 2 * K) * N + K * (Cs * (2 * N)) := add_le_add hnorm hlq
    _ = nikolskiiConst C α s * N := by simp only [nikolskiiConst, K, Cs]; ring

/-- **The Nikolskii transfer theorem**, membership form: `f ∈ A^s_q(X)` gives `f = ι y` with
`y ∈ B^{s-α}_q(Y)`. -/
theorem MemApprox.exists_preimage_of_nikolskii [CompleteSpace Y] (hι : Function.Injective ι)
    (hN : LiftBound ι A α C) (hC : 0 ≤ C) (hα : 0 ≤ α) (hαs : α < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) :
    ∃ y : Y, ι y = f ∧ (A.comap ι.toLinearMap hι).MemApprox (s - α) q y := by
  obtain ⟨y, hy, hle⟩ := ApproximationScheme.exists_preimage_of_nikolskii hι hN hC hα hαs hq hf
  refine ⟨y, hy, (memApprox_iff_approxNormDyadic_lt_top hq (sub_nonneg.2 hαs.le)).2 ?_⟩
  exact hle.trans_lt (ENNReal.mul_lt_top (nikolskiiConst_ne_top C hαs).lt_top
    ((memApprox_iff_approxNormDyadic_lt_top hq (hα.trans hαs.le)).1 hf))

end ApproximationScheme
