/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Classical.Modulus

/-!
# Besov spaces through moduli of smoothness: the coincidence theorem in `L_2(𝕋^d)`

The classical definition of the Besov space `B^s_{2,q}(𝕋^d)`, `0 < s < 1`, uses the modulus of
smoothness `ω(f, t)_2 = sup_{‖h‖ ≤ t} ‖f(· + h) - f‖_2`:

`‖f‖ = ‖f‖_2 + ‖(2^(js) ω(f, 2^(-j))_2)_{j ≥ 0}‖_{ℓ_q}`   (`Torus.modulusNorm`).

**Coincidence theorem** (`Torus.memBesov_iff_modulusNorm_lt_top`): for `0 < s < 1` and
`1 ≤ q ≤ ∞` this space is the approximation space `B^s_{2,q}(𝕋^d)` of trigonometric polynomials,
with equivalent norms:

* `‖f‖_{B^s_{2,q}} ≤ (d + 1) ‖f‖_{mod}` by Jackson's theorem
  (`approxNormDyadic_le_modulusNorm`);
* `‖f‖_{mod} ≤ C(d, s) ‖f‖_{B^s_{2,q}}` (`modulusNorm_le_approxNormDyadic`): the modulus at
  `2^(-j)` is bounded by the dyadic Fourier blocks, `ω(f, 2^(-j)) ≲ ∑_K min(1, 2^(K-j)) ‖Δ_K f‖`,
  because a translation by `h` multiplies the block `Δ_K f` by at most `min(2, 4πd 2^K ‖h‖)`;
  the two halves of the sum are Hardy's inequalities with exponents `s` and `1 - s`, and the
  blocks are controlled by the approximation norm.

The restriction `s < 1` is that of first-order differences; higher smoothness needs
differences of higher order.  For `p ≠ 2` the same theorem needs Jackson's and Bernstein's
inequalities in `L_p`, proved with the de la Vallée Poussin kernel, which is not formalised.
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set ApproximationScheme
open scoped ENNReal TorusHaar lp Real

namespace Torus

open ENNReal (lqNorm dyadicWeight)

variable {d : Type*} [Fintype d]

/-- The **classical Besov norm** through the modulus of smoothness,
`‖f‖_2 + ‖(2^(js) ω(f, 2^(-j))_2)_j‖_{ℓ_q}`. -/
noncomputable def modulusNorm (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ℝ≥0∞ :=
  ‖f‖ₑ + lqNorm q (fun j : ℕ => dyadicWeight s j * modulus f (1 / 2 ^ j))

variable {s : ℝ} {q : ℝ≥0∞}

/-- Jackson's theorem in the form `E_n(f) ≤ (d + 1) ω(f, 1/n)`. -/
theorem approxSeq_le_modulus {n : ℕ} (hn : 1 ≤ n) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume 2).approxSeq f n ≤
      ((Fintype.card d : ℝ≥0∞) + 1) * modulus f (1 / n) := by
  have h := approxSeq_sq_le_card_mul_modulus_sq hn f
  have hd : (Fintype.card d : ℝ≥0∞) ≤ ((Fintype.card d : ℝ≥0∞) + 1) ^ 2 := by
    calc (Fintype.card d : ℝ≥0∞) ≤ (Fintype.card d : ℝ≥0∞) + 1 := le_self_add
      _ ≤ ((Fintype.card d : ℝ≥0∞) + 1) ^ 2 := by
          rw [sq]; exact le_mul_of_one_le_left' le_add_self
  have h2 : ((trigScheme d).toLp volume 2).approxSeq f n ^ 2 ≤
      (((Fintype.card d : ℝ≥0∞) + 1) * modulus f (1 / n)) ^ 2 := by
    rw [mul_pow]; exact h.trans (by gcongr)
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_two] at h2
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 h2

/-- **Jackson's half of the coincidence theorem**: `‖f‖_{B^s_{2,q}} ≤ (d + 1) ‖f‖_{mod}` in the
dyadic quasi-norm. -/
theorem approxNormDyadic_le_modulusNorm (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume 2).approxNormDyadic s q f ≤
      ((Fintype.card d : ℝ≥0∞) + 1) * modulusNorm s q f := by
  set M := (Fintype.card d : ℝ≥0∞) + 1
  have hseq : ∀ j, ((trigScheme d).toLp volume 2).approxSeqDyadic s f j ≤
      M * (dyadicWeight s j * modulus f (1 / 2 ^ j)) := fun j => by
    rw [approxSeqDyadic, mul_left_comm]
    gcongr
    have := approxSeq_le_modulus (Nat.one_le_two_pow (n := j)) f
    simpa using this
  calc ((trigScheme d).toLp volume 2).approxNormDyadic s q f
      = ‖f‖ₑ + lqNorm q (((trigScheme d).toLp volume 2).approxSeqDyadic s f) := rfl
    _ ≤ M * ‖f‖ₑ + M * lqNorm q (fun j : ℕ => dyadicWeight s j * modulus f (1 / 2 ^ j)) := by
        gcongr
        · exact le_mul_of_one_le_left' le_add_self
        · rw [← ENNReal.lqNorm_const_mul]; exact ENNReal.lqNorm_mono hseq
    _ = M * modulusNorm s q f := by rw [modulusNorm, mul_add]

/-- The multiplier bound of a translation by `‖h‖ ≤ t` on the dyadic block `K`:
`min(2, 2πd 2^(K+1) t)`. -/
noncomputable def blockMult (d : Type*) [Fintype d] (K : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min 2 (2 * π * Fintype.card d * 2 ^ (K + 1) * t))

/-- On the block `K`, `|e_k(h) - 1| ≤ min(2, 2πd 2^(K+1) ‖h‖)`. -/
theorem enorm_mFourier_sub_one_le_blockMult {k : d → ℤ} {K : ℕ} (hk : deg k < 2 ^ (K + 1))
    {h : UnitAddTorus d} {t : ℝ} (hh : ‖h‖ ≤ t) :
    ‖mFourier k h - 1‖ₑ ≤ blockMult d K t := by
  rw [blockMult, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (le_min ?_ ?_)
  · calc ‖mFourier k h - 1‖ ≤ ‖mFourier k h‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
          rw [norm_one, show ‖mFourier k h‖ = 1 by
            simpa [trigMonomial_apply] using norm_trigMonomial_apply k h]; norm_num
  · calc ‖mFourier k h - 1‖ ≤ 2 * π * Fintype.card d * deg k * ‖h‖ :=
          norm_mFourier_sub_one_le k h
      _ ≤ 2 * π * Fintype.card d * 2 ^ (K + 1) * t := by
          gcongr
          exact_mod_cast hk.le

/-- **A translation acts on the dyadic blocks with bounded multipliers**: for `‖h‖ ≤ t`,
`‖f(· + h) - f‖² ≤ ∑_K min(2, 2πd 2^(K+1) t)² ‖Δ_K f‖²`. -/
theorem enorm_translate_sub_sq_le {h : UnitAddTorus d} {t : ℝ} (hh : ‖h‖ ≤ t)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖translate h f - f‖ₑ ^ 2 ≤ ∑' K, blockMult d K t ^ 2 * ‖fourierBlock K f‖ₑ ^ 2 := by
  rw [enorm_translate_sub_sq]
  simp_rw [enorm_fourierBlock_sq, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rcases Nat.eq_zero_or_pos (deg k) with h0 | hpos
  · have hk : k = 0 := by
      funext i; have := natAbs_le_deg k i; rw [h0] at this; simpa using this
    subst hk
    simp [mFourier_zero]
  set K0 := Nat.log 2 (deg k)
  have hK0 : 2 ^ K0 ≤ deg k ∧ deg k < 2 ^ (K0 + 1) :=
    ⟨Nat.pow_log_le_self 2 hpos.ne', Nat.lt_pow_succ_log_self Nat.one_lt_two _⟩
  calc ‖mFourier k h - 1‖ₑ ^ 2 * ‖mFourierCoeff f k‖ₑ ^ 2
      ≤ blockMult d K0 t ^ 2 * ‖mFourierCoeff f k‖ₑ ^ 2 := by
        gcongr; exact enorm_mFourier_sub_one_le_blockMult hK0.2 hh
    _ = blockMult d K0 t ^ 2 * (if 2 ^ K0 ≤ deg k ∧ deg k < 2 ^ (K0 + 1) then
          ‖mFourierCoeff f k‖ₑ ^ 2 else 0) := by simp only [hK0, and_self, ↓reduceIte]
    _ ≤ ∑' K, blockMult d K t ^ 2 * (if 2 ^ K ≤ deg k ∧ deg k < 2 ^ (K + 1) then
          ‖mFourierCoeff f k‖ₑ ^ 2 else 0) :=
        ENNReal.le_tsum (f := fun K => blockMult d K t ^ 2 * (if 2 ^ K ≤ deg k ∧
          deg k < 2 ^ (K + 1) then ‖mFourierCoeff f k‖ₑ ^ 2 else 0)) K0

/-- `(∑ a_K²)^(1/2) ≤ ∑ a_K` in `ℝ≥0∞`. -/
theorem le_tsum_of_sq_le_tsum_sq {x : ℝ≥0∞} {a : ℕ → ℝ≥0∞} (h : x ^ 2 ≤ ∑' K, a K ^ 2) :
    x ≤ ∑' K, a K := by
  have h2 : lqNorm 2 a ^ (2 : ℝ≥0∞).toReal = ∑' K, a K ^ (2 : ℝ≥0∞).toReal :=
    ENNReal.lqNorm_rpow (by norm_num) (by norm_num) a
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h2
  have hx : x ≤ lqNorm 2 a := by
    rw [← h2] at h
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_two] at h
    exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 h
  exact hx.trans (ENNReal.lqNorm_le_lqNorm_one (by norm_num) a)

/-- **The modulus is controlled by the dyadic blocks**:
`ω(f, t) ≤ ∑_K min(2, 2πd 2^(K+1) t) ‖Δ_K f‖`. -/
theorem modulus_le_tsum_block (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (t : ℝ) :
    modulus f t ≤ ∑' K, blockMult d K t * ‖fourierBlock K f‖ₑ := by
  refine iSup₂_le fun h hh => le_tsum_of_sq_le_tsum_sq ?_
  simp_rw [mul_pow]
  exact enorm_translate_sub_sq_le hh f

/-- `∑_K [j ≤ K] g K = ∑_i g (j + i)`. -/
theorem tsum_ite_le_eq (j : ℕ) (g : ℕ → ℝ≥0∞) :
    ∑' K, (if j ≤ K then g K else 0) = ∑' i, g (j + i) := by
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := j)]
  have h0 : ∑ K ∈ Finset.range j, (if j ≤ K then g K else 0) = 0 :=
    Finset.sum_eq_zero fun K hK => by simp [not_le.2 (Finset.mem_range.1 hK)]
  rw [h0, zero_add]
  congr 1; funext i
  simp only [Nat.le_add_left j i, ↓reduceIte]
  rw [add_comm]

/-- `∑_K [K ≤ j] g K = ∑_{K ≤ j} g K`. -/
theorem tsum_ite_ge_eq (j : ℕ) (g : ℕ → ℝ≥0∞) :
    ∑' K, (if K ≤ j then g K else 0) = ∑ K ∈ Finset.range (j + 1), g K := by
  rw [tsum_eq_sum (s := Finset.range (j + 1)) fun K hK => by
    simp [not_le.2 (by simpa using hK : j < K)]]
  exact Finset.sum_congr rfl fun K hK => by
    simp [Nat.lt_succ_iff.1 (Finset.mem_range.1 hK)]

/-- At `t = 2^(-j)` the block multipliers are `≤ 2` for `K ≥ j` and `≤ 4πd 2^(K-j)` for
`K ≤ j`. -/
theorem blockMult_le (K j : ℕ) :
    blockMult d K (1 / 2 ^ j) ≤ (if j ≤ K then 2 else 0) +
      (if K ≤ j then ENNReal.ofReal (4 * π * Fintype.card d) *
        (dyadicWeight (-1) j * dyadicWeight 1 K) else 0) := by
  by_cases hjK : j ≤ K
  · simp only [hjK, ↓reduceIte]
    refine le_trans ?_ le_self_add
    rw [blockMult, ← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · simp only [hjK, show K ≤ j by omega, ↓reduceIte, zero_add]
    have h1 : ENNReal.ofReal ((2 : ℝ) ^ K * (1 / 2 ^ j)) =
        dyadicWeight (-1) j * dyadicWeight 1 K := by
      rw [ENNReal.ofReal_mul (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
        show ((2 : ℝ) ^ K) = ((2 ^ K : ℕ) : ℝ) by push_cast; rfl,
        show ((2 : ℝ) ^ j) = ((2 ^ j : ℕ) : ℝ) by push_cast; rfl, ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast, ENNReal.natCast_two_pow_eq, ENNReal.natCast_two_pow_eq,
        ← ENNReal.dyadicWeight_neg, mul_comm]
    calc blockMult d K (1 / 2 ^ j)
        ≤ ENNReal.ofReal (4 * π * Fintype.card d * ((2 : ℝ) ^ K * (1 / 2 ^ j))) := by
          rw [blockMult]
          refine ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans_eq ?_)
          ring
      _ = ENNReal.ofReal (4 * π * Fintype.card d) * (dyadicWeight (-1) j * dyadicWeight 1 K) := by
          rw [ENNReal.ofReal_mul (by positivity), h1]

/-- The weighted modulus at `2^(-j)`, split into the tail and the partial sums of the
weighted blocks. -/
theorem dyadicWeight_mul_modulus_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ) :
    dyadicWeight s j * modulus f (1 / 2 ^ j) ≤
      2 * (dyadicWeight s j * ∑' i, ‖fourierBlock (j + i) f‖ₑ) +
        ENNReal.ofReal (4 * π * Fintype.card d) * (dyadicWeight (-(1 - s)) j *
          ∑ K ∈ Finset.range (j + 1), dyadicWeight 1 K * ‖fourierBlock K f‖ₑ) := by
  set C1 := ENNReal.ofReal (4 * π * Fintype.card d)
  have hsplit : ∑' K, blockMult d K (1 / 2 ^ j) * ‖fourierBlock K f‖ₑ ≤
      2 * ∑' i, ‖fourierBlock (j + i) f‖ₑ +
        C1 * (dyadicWeight (-1) j * ∑ K ∈ Finset.range (j + 1),
          dyadicWeight 1 K * ‖fourierBlock K f‖ₑ) := by
    calc ∑' K, blockMult d K (1 / 2 ^ j) * ‖fourierBlock K f‖ₑ
        ≤ ∑' K, ((if j ≤ K then 2 * ‖fourierBlock K f‖ₑ else 0) +
            (if K ≤ j then C1 * dyadicWeight (-1) j *
              (dyadicWeight 1 K * ‖fourierBlock K f‖ₑ) else 0)) :=
          ENNReal.tsum_le_tsum fun K =>
            (mul_le_mul' (blockMult_le K j) le_rfl).trans (le_of_eq (by split_ifs <;> ring))
      _ = 2 * ∑' i, ‖fourierBlock (j + i) f‖ₑ + C1 * (dyadicWeight (-1) j *
            ∑ K ∈ Finset.range (j + 1), dyadicWeight 1 K * ‖fourierBlock K f‖ₑ) := by
          rw [ENNReal.tsum_add, tsum_ite_le_eq, tsum_ite_ge_eq, ENNReal.tsum_mul_left,
            ← Finset.mul_sum, mul_assoc]
  have hw : dyadicWeight s j * dyadicWeight (-1) j = dyadicWeight (-(1 - s)) j := by
    rw [← ENNReal.dyadicWeight_add]; congr 1; ring
  calc dyadicWeight s j * modulus f (1 / 2 ^ j)
      ≤ dyadicWeight s j * ∑' K, blockMult d K (1 / 2 ^ j) * ‖fourierBlock K f‖ₑ := by
        gcongr; exact modulus_le_tsum_block f _
    _ ≤ dyadicWeight s j * (2 * ∑' i, ‖fourierBlock (j + i) f‖ₑ + C1 * (dyadicWeight (-1) j *
          ∑ K ∈ Finset.range (j + 1), dyadicWeight 1 K * ‖fourierBlock K f‖ₑ)) := by gcongr
    _ = _ := by rw [mul_add, ← hw]; ring

/-- The constant of the second half of the coincidence theorem,
`1 + 5 (2 (1 - 2^(-s))⁻¹ + 4πd (1 - 2^(-(1-s)))⁻¹)`. -/
noncomputable def coincidenceConst (d : Type*) [Fintype d] (s : ℝ) : ℝ≥0∞ :=
  1 + 5 * (2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ +
    ENNReal.ofReal (4 * π * Fintype.card d) * (1 - (2 : ℝ≥0∞) ^ (-(1 - s)))⁻¹)

theorem coincidenceConst_ne_top (hs : 0 < s) (hs1 : s < 1) : coincidenceConst d s ≠ ∞ := by
  unfold coincidenceConst
  have h1 := ENNReal.one_sub_two_rpow_neg_inv_ne_top hs
  have h2 := ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 hs1)
  refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) h1,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2⟩)⟩

/-- **The second half of the coincidence theorem**: for `0 < s < 1`,
`‖f‖_{mod} ≤ C(d, s) ‖f‖_{B^s_{2,q}}` in the dyadic quasi-norm. -/
theorem modulusNorm_le_approxNormDyadic (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    modulusNorm s q f ≤
      coincidenceConst d s * ((trigScheme d).toLp volume 2).approxNormDyadic s q f := by
  set C1 := ENNReal.ofReal (4 * π * Fintype.card d)
  set Cs := (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹
  set Cs1 := (1 - (2 : ℝ≥0∞) ^ (-(1 - s)))⁻¹
  set N := ((trigScheme d).toLp volume 2).approxNormDyadic s q f
  set L := lqNorm q (fun K => dyadicWeight s K * ‖fourierBlock K f‖ₑ)
  have hL : L ≤ 5 * N := by
    have h := (fourierScheme d).projectionScheme.blockNorm_le_approxNormDyadic (s := s) (q := q) f
    have hb : ENNReal.ofReal (fourierScheme d).projectionScheme.bound +
        2 * (1 + ENNReal.ofReal (fourierScheme d).projectionScheme.bound) = 5 := by
      change ENNReal.ofReal 1 + 2 * (1 + ENNReal.ofReal 1) = 5
      rw [ENNReal.ofReal_one]; norm_num
    rw [hb] at h
    have hN : N = (fourierScheme d).toScheme.approxNormDyadic s q f :=
      congrArg (fun A : ApproximationScheme (Lp ℂ 2 (volume : Measure (UnitAddTorus d))) =>
        A.approxNormDyadic s q f) (toLp_trigScheme_eq d)
    rw [hN]
    exact le_add_self.trans h
  have hmod : lqNorm q (fun j : ℕ => dyadicWeight s j * modulus f (1 / 2 ^ j)) ≤
      2 * (Cs * L) + C1 * (Cs1 * L) := by
    have hsplit : ∀ K, dyadicWeight (-(1 - s)) K * (dyadicWeight 1 K * ‖fourierBlock K f‖ₑ) =
        dyadicWeight s K * ‖fourierBlock K f‖ₑ := fun K => by
      rw [← mul_assoc, ← ENNReal.dyadicWeight_add]; congr 2; ring
    calc lqNorm q (fun j : ℕ => dyadicWeight s j * modulus f (1 / 2 ^ j))
        ≤ lqNorm q (fun j => 2 * (dyadicWeight s j * ∑' i, ‖fourierBlock (j + i) f‖ₑ) +
            C1 * (dyadicWeight (-(1 - s)) j *
              ∑ K ∈ Finset.range (j + 1), dyadicWeight 1 K * ‖fourierBlock K f‖ₑ)) :=
          ENNReal.lqNorm_mono (dyadicWeight_mul_modulus_le f)
      _ ≤ 2 * lqNorm q (fun j => dyadicWeight s j * ∑' i, ‖fourierBlock (j + i) f‖ₑ) +
            C1 * lqNorm q (fun j => dyadicWeight (-(1 - s)) j *
              ∑ K ∈ Finset.range (j + 1), dyadicWeight 1 K * ‖fourierBlock K f‖ₑ) := by
          refine (ENNReal.lqNorm_add_le hq _ _).trans (le_of_eq ?_)
          rw [ENNReal.lqNorm_const_mul, ENNReal.lqNorm_const_mul]
      _ ≤ 2 * (Cs * L) + C1 * (Cs1 * L) := by
          gcongr
          · exact ENNReal.hardy_tail_le hq s (fun m => ‖fourierBlock m f‖ₑ)
          · have := ENNReal.hardy_sum_le hq (1 - s)
              (fun K => dyadicWeight 1 K * ‖fourierBlock K f‖ₑ)
            simp_rw [hsplit] at this
            exact this
  have hfN : ‖f‖ₑ ≤ N := enorm_le_approxNormDyadic f
  calc modulusNorm s q f = ‖f‖ₑ + lqNorm q (fun j : ℕ => dyadicWeight s j * modulus f (1 / 2 ^ j)) :=
        rfl
    _ ≤ N + (2 * (Cs * (5 * N)) + C1 * (Cs1 * (5 * N))) :=
        add_le_add hfN (hmod.trans (by gcongr))
    _ = coincidenceConst d s * N := by simp only [coincidenceConst, C1, Cs, Cs1]; ring

/-- **The coincidence theorem in `L_2(𝕋^d)`**: for `0 < s < 1` and `1 ≤ q ≤ ∞`, the Besov space
`B^s_{2,q}(𝕋^d)` defined by approximation with trigonometric polynomials is the Besov space
defined by the modulus of smoothness: `f ∈ B^s_{2,q}` iff
`‖f‖_2 + ‖(2^(js) ω(f, 2^(-j))_2)_j‖_{ℓ_q} < ∞`. -/
theorem memBesov_iff_modulusNorm_lt_top (hs : 0 < s) (hs1 : s < 1) (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (trigScheme d).MemBesov volume 2 s q f ↔ modulusNorm s q f < ∞ := by
  change ((trigScheme d).toLp volume 2).MemApprox s q f ↔ _
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le]
  constructor
  · intro h
    exact (modulusNorm_le_approxNormDyadic hq f).trans_lt
      (ENNReal.mul_lt_top (coincidenceConst_ne_top hs hs1).lt_top h)
  · intro h
    exact (approxNormDyadic_le_modulusNorm f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.natCast_lt_top _, ENNReal.one_lt_top⟩) h)

end Torus
