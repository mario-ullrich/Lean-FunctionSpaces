/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Norm
public import ApproximationSpaces.Sequences.Dyadic
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The dyadic quasi-norm of `A^s_q`

Since `E_n(f)` decreases in `n`, only the errors at the dyadic points `n = 2^k` matter:
for `s ≥ 0` and `1 ≤ q ≤ ∞`,

`‖f‖_{A^s_q} ≍ ‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}`,

with the explicit constants `approxNorm ≤ 2^s · approxNormDyadic` and
`approxNormDyadic ≤ 4 · 2^s · approxNorm` (`approxNorm_le_approxNormDyadic`,
`approxNormDyadic_le_approxNorm`).  The term `‖f‖` is needed because the dyadic sequence
starts with `E_1(f)`, which vanishes on `A 1`, while Pietsch's sequence starts with
`E_0(f) = ‖f‖`.

**Why the dyadic form is the working norm.** Its weights `2^(ks)` do not depend on `q`, so
comparing different `q` is monotonicity of `ℓ_q` norms, and a shift `k ↦ k + 1` multiplies the
weights by the constant `2^s`.  Every later theorem is proved for `approxNormDyadic` and
transported through this equivalence; no later proof unfolds Pietsch's weights `n^(s - 1/q)`.

The file ends with the consequence that the errors of an element of `A^s_q`, `s > 0`, tend to
zero, so that `A^s_q` lies in the closure of `⋃ A n`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (A : ApproximationScheme X)

/-- The **dyadic sequence** `(2^(ks) E_{2^k}(f))_k`. -/
noncomputable def approxSeqDyadic (s : ℝ) (f : X) (k : ℕ) : ℝ≥0∞ :=
  dyadicWeight s k * A.approxSeq f (2 ^ k)

/-- The **dyadic quasi-norm** `‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}`, equivalent to Pietsch's
quasi-norm for `s ≥ 0`. -/
noncomputable def approxNormDyadic (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f)

variable {A} {s : ℝ} {q : ℝ≥0∞}

/-- Each term `2^(ks) E_{2^k}(f)` is at most the `ℓ_q` norm of the dyadic sequence. -/
theorem approxSeqDyadic_le_lqNorm (hq : 1 ≤ q) (f : X) (k : ℕ) :
    A.approxSeqDyadic s f k ≤ lqNorm q (A.approxSeqDyadic s f) :=
  ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne' _ k

/-- `‖f‖ ≤ ‖f‖^dyadic_{A^s_q}`. -/
theorem enorm_le_approxNormDyadic (f : X) : ‖f‖ₑ ≤ A.approxNormDyadic s q f := le_self_add

/-- The `ℓ_q` part of the dyadic quasi-norm is at most the quasi-norm. -/
theorem lqNorm_le_approxNormDyadic (f : X) :
    lqNorm q (A.approxSeqDyadic s f) ≤ A.approxNormDyadic s q f := le_add_self

/-- Powers of the dyadic terms: `(2^(ks) E_{2^k}(f))^p = 2^(ksp) E_{2^k}(f)^p` for `p ≥ 0`. -/
theorem approxSeqDyadic_rpow {p : ℝ} (hp : 0 ≤ p) (f : X) (k : ℕ) :
    A.approxSeqDyadic s f k ^ p = dyadicWeight (s * p) k * A.approxSeq f (2 ^ k) ^ p := by
  rw [approxSeqDyadic, ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.dyadicWeight_rpow]

/-- The first dyadic term is `E_1(f)`. -/
theorem approxSeqDyadic_zero (f : X) : A.approxSeqDyadic s f 0 = A.approxSeq f 1 := by
  simp [approxSeqDyadic]

/-- The dyadic quasi-norm of `0` is `0`. -/
@[simp]
theorem approxNormDyadic_zero (s : ℝ) (q : ℝ≥0∞) : A.approxNormDyadic s q 0 = 0 := by
  have : A.approxSeqDyadic s 0 = fun _ => 0 := by funext k; simp [approxSeqDyadic]
  simp [approxNormDyadic, this]

/-- The dyadic terms are homogeneous: `2^(ks) E_{2^k}(c f) = |c| 2^(ks) E_{2^k}(f)`. -/
theorem approxSeqDyadic_smul (c : ℝ) (f : X) :
    A.approxSeqDyadic s (c • f) = fun k => ‖c‖ₑ * A.approxSeqDyadic s f k := by
  funext k; rw [approxSeqDyadic, approxSeqDyadic, approxSeq_smul, mul_left_comm]

/-- The dyadic quasi-norm is homogeneous: `‖c f‖^dyadic = |c| ‖f‖^dyadic`. -/
theorem approxNormDyadic_smul (c : ℝ) (f : X) :
    A.approxNormDyadic s q (c • f) = ‖c‖ₑ * A.approxNormDyadic s q f := by
  rw [approxNormDyadic, approxNormDyadic, approxSeqDyadic_smul, ENNReal.lqNorm_const_mul,
    enorm_smul, mul_add]

/-- `1 ≤ 2^s` for `s ≥ 0`. -/
theorem one_le_two_rpow (hs : 0 ≤ s) : 1 ≤ (2 : ℝ≥0∞) ^ s := by
  simpa using ENNReal.rpow_le_rpow_of_exponent_le one_le_two hs

/-- `2^s` is finite in `ℝ≥0∞`. -/
theorem two_rpow_ne_top (s : ℝ) : (2 : ℝ≥0∞) ^ s ≠ ∞ :=
  ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top

/-- **Pietsch's quasi-norm is dominated by the dyadic one**: for `s ≥ 0` and `1 ≤ q ≤ ∞`,
`‖f‖_{A^s_q} ≤ 2^s (‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_q)`. -/
theorem approxNorm_le_approxNormDyadic (hq : 1 ≤ q) (hs : 0 ≤ s) (f : X) :
    A.approxNorm s q f ≤ 2 ^ s * A.approxNormDyadic s q f := by
  have h2s := one_le_two_rpow hs
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [approxNorm_top, approxNormDyadic, ENNReal.lqNorm_top]
    calc ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * A.approxSeq f n
        ≤ A.approxSeq f 0 + 2 ^ s * ⨆ k, dyadicWeight s k * A.approxSeq f (2 ^ k) :=
          ENNReal.iSup_pow_mul_le_dyadic (approxSeq_anti f) hs
      _ ≤ 2 ^ s * ‖f‖ₑ + 2 ^ s * ⨆ k, A.approxSeqDyadic s f k := by
          rw [approxSeq_zero_left]
          exact add_le_add (le_mul_of_one_le_left' h2s) le_rfl
      _ = 2 ^ s * (‖f‖ₑ + ⨆ k, A.approxSeqDyadic s f k) := by rw [mul_add]
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hp1 : 1 ≤ q.toReal := ENNReal.one_le_toReal_of_one_le hq hq'
  have hp : 0 < q.toReal := zero_lt_one.trans_le hp1
  have hD : lqNorm q (A.approxSeqDyadic s f) ^ q.toReal =
      ∑' k, dyadicWeight (s * q.toReal) k * A.approxSeq f (2 ^ k) ^ q.toReal := by
    rw [ENNReal.lqNorm_rpow hq0 hq']
    simp_rw [approxSeqDyadic_rpow hp.le]
  set p := q.toReal
  have hb : Antitone fun n => A.approxSeq f n ^ p := fun m n h =>
    ENNReal.rpow_le_rpow (approxSeq_anti f h) hp.le
  set D := lqNorm q (A.approxSeqDyadic s f)
  rw [← ENNReal.rpow_le_rpow_iff hp, approxNorm_rpow hq0 hq']
  calc ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * p - 1) * A.approxSeq f n ^ p
      ≤ A.approxSeq f 0 ^ p + 2 ^ max (s * p - 1) 0 *
          ∑' k, dyadicWeight (s * p - 1 + 1) k * A.approxSeq f (2 ^ k) ^ p :=
        ENNReal.tsum_pow_mul_le_dyadic hb (s * p - 1)
    _ = ‖f‖ₑ ^ p + 2 ^ max (s * p - 1) 0 * D ^ p := by
        rw [sub_add_cancel, hD, approxSeq_zero_left]
    _ ≤ (2 ^ s) ^ p * ‖f‖ₑ ^ p + (2 ^ s) ^ p * D ^ p := by
        gcongr
        · exact le_mul_of_one_le_left' (ENNReal.one_le_rpow h2s hp |>.trans_eq' rfl)
        · rw [← ENNReal.rpow_mul]
          exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two
            (max_le (by linarith) (by positivity))
    _ = (2 ^ s) ^ p * (‖f‖ₑ ^ p + D ^ p) := by rw [mul_add]
    _ ≤ (2 ^ s) ^ p * (‖f‖ₑ + D) ^ p := by gcongr; exact ENNReal.add_rpow_le_rpow_add _ _ hp1
    _ = (2 ^ s * A.approxNormDyadic s q f) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]; rfl

/-- The shifted dyadic sequence `(2^(ks) E_{2^(k+1)}(f))_k` is dominated by twice Pietsch's
quasi-norm. -/
theorem lqNorm_dyadic_succ_le (hq : 1 ≤ q) (hs : 0 ≤ s) (f : X) :
    lqNorm q (fun k => dyadicWeight s k * A.approxSeq f (2 ^ (k + 1))) ≤
      2 * A.approxNorm s q f := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [ENNReal.lqNorm_top]
    calc ⨆ k, dyadicWeight s k * A.approxSeq f (2 ^ (k + 1))
        ≤ ⨆ k, dyadicWeight s k * A.approxSeq f (2 ^ k) := iSup_mono fun k => by
          gcongr
          exact approxSeq_anti f (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
      _ ≤ ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * A.approxSeq f n := ENNReal.dyadic_le_iSup_pow_mul hs
      _ = A.approxNorm s ∞ f := (approxNorm_top s f).symm
      _ ≤ 2 * A.approxNorm s ∞ f := le_mul_of_one_le_left' one_le_two
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hp1 : 1 ≤ q.toReal := ENNReal.one_le_toReal_of_one_le hq hq'
  have hp : 0 < q.toReal := zero_lt_one.trans_le hp1
  set p := q.toReal
  have hb : Antitone fun n => A.approxSeq f n ^ p := fun m n h =>
    ENNReal.rpow_le_rpow (approxSeq_anti f h) hp.le
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.lqNorm_rpow hq0 hq']
  calc ∑' k, (dyadicWeight s k * A.approxSeq f (2 ^ (k + 1))) ^ p
      = ∑' k, dyadicWeight (s * p - 1 + 1) k * A.approxSeq f (2 ^ (k + 1)) ^ p := by
        congr 1; funext k
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.dyadicWeight_rpow, sub_add_cancel]
    _ ≤ 2 ^ max (-(s * p - 1)) 0 * ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * p - 1) *
          A.approxSeq f n ^ p := ENNReal.dyadic_le_tsum_pow_mul hb _
    _ = 2 ^ max (-(s * p - 1)) 0 * A.approxNorm s q f ^ p := by rw [approxNorm_rpow hq0 hq']
    _ ≤ 2 ^ p * A.approxNorm s q f ^ p := by
        have hsp : 0 ≤ s * p := mul_nonneg hs hp.le
        gcongr ?_ * _
        exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two
          (max_le (by linarith) (by linarith))
    _ = (2 * A.approxNorm s q f) ^ p := (ENNReal.mul_rpow_of_nonneg _ _ hp.le).symm

/-- **The dyadic quasi-norm is dominated by Pietsch's**: for `s ≥ 0` and `1 ≤ q ≤ ∞`,
`‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_q ≤ 4 · 2^s ‖f‖_{A^s_q}`. -/
theorem approxNormDyadic_le_approxNorm (hq : 1 ≤ q) (hs : 0 ≤ s) (f : X) :
    A.approxNormDyadic s q f ≤ 4 * 2 ^ s * A.approxNorm s q f := by
  set P := A.approxNorm s q f
  have h2s := one_le_two_rpow hs
  have hfP : ‖f‖ₑ ≤ P := enorm_le_approxNorm hq f
  have hhead : A.approxSeqDyadic s f 0 ≤ P := by
    rw [approxSeqDyadic_zero]; exact (approxSeq_le_enorm f 1).trans hfP
  have hshift : lqNorm q (fun k => A.approxSeqDyadic s f (k + 1)) ≤ 2 ^ s * (2 * P) := by
    have : (fun k => A.approxSeqDyadic s f (k + 1)) =
        fun k => 2 ^ s * (dyadicWeight s k * A.approxSeq f (2 ^ (k + 1))) := by
      funext k; rw [approxSeqDyadic, ENNReal.dyadicWeight_succ, mul_assoc]
    rw [this, ENNReal.lqNorm_const_mul]
    gcongr
    exact lqNorm_dyadic_succ_le hq hs f
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ P + (P + 2 ^ s * (2 * P)) := by
        gcongr
        exact (ENNReal.lqNorm_le_head_add_shift hq _).trans (add_le_add hhead hshift)
    _ = (2 + 2 * 2 ^ s) * P := by ring
    _ ≤ (2 * 2 ^ s + 2 * 2 ^ s) * P := by
        gcongr; exact le_mul_of_one_le_right' h2s
    _ = 4 * 2 ^ s * P := by ring

/-- For `s ≥ 0`, `f ∈ A^s_q` iff its dyadic quasi-norm is finite. -/
theorem memApprox_iff_approxNormDyadic_lt_top (hq : 1 ≤ q) (hs : 0 ≤ s) {f : X} :
    A.MemApprox s q f ↔ A.approxNormDyadic s q f < ∞ := by
  constructor
  · intro hf
    exact (approxNormDyadic_le_approxNorm hq hs f).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (two_rpow_ne_top s).lt_top) hf)
  · intro hf
    exact (approxNorm_le_approxNormDyadic hq hs f).trans_lt
      (ENNReal.mul_lt_top (two_rpow_ne_top s).lt_top hf)

/-- For `s ≥ 0`, `f ∈ A^s_q` iff `(2^(ks) E_{2^k}(f))_k ∈ ℓ_q`. -/
theorem memApprox_iff_lqNorm_dyadic_lt_top (hq : 1 ≤ q) (hs : 0 ≤ s) {f : X} :
    A.MemApprox s q f ↔ lqNorm q (A.approxSeqDyadic s f) < ∞ := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs, approxNormDyadic, ENNReal.add_lt_top]
  exact and_iff_right enorm_lt_top

/-- A bound on the dyadic quasi-norm gives the decay `E_{2^k}(f) ≤ 2^(-ks) ‖f‖^dyadic`. -/
theorem approxSeq_pow_le (hq : 1 ≤ q) (f : X) (k : ℕ) :
    A.approxSeq f (2 ^ k) ≤ dyadicWeight (-s) k * lqNorm q (A.approxSeqDyadic s f) := by
  calc A.approxSeq f (2 ^ k) = dyadicWeight (-s) k * A.approxSeqDyadic s f k := by
        rw [approxSeqDyadic, ← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
    _ ≤ _ := by gcongr; exact approxSeqDyadic_le_lqNorm hq f k

/-- For `f ∈ A^s_q` with `s > 0`, the dyadic errors `E_{2^k}(f)` tend to zero. -/
theorem tendsto_approxError_pow_zero_of_memApprox (hq : 1 ≤ q) (hs : 0 < s) {f : X}
    (hf : A.MemApprox s q f) : Tendsto (fun k => A.approxError (2 ^ k) f) atTop (𝓝 0) := by
  have hD := (memApprox_iff_lqNorm_dyadic_lt_top hq hs.le).1 hf
  set D := lqNorm q (A.approxSeqDyadic s f)
  have hgeom : Tendsto (fun k => D * ((2 : ℝ≥0∞) ^ (-s)) ^ k) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.two_rpow_neg_lt_one hs))
      (Or.inr hD.ne)
  have hseq : Tendsto (fun k => A.approxSeq f (2 ^ k)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom (fun _ => bot_le)
      fun k => by
        rw [mul_comm, ← ENNReal.dyadicWeight_eq_pow]; exact approxSeq_pow_le hq f k
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hseq
  simpa [Function.comp_def, approxSeq, ENNReal.toReal_ofReal (approxError_nonneg _ _)] using this

/-- **`A^s_q` lies in the closure of `⋃ A n`** for `s > 0`. -/
theorem mem_closure_iUnion_of_memApprox (hq : 1 ≤ q) (hs : 0 < s) {f : X}
    (hf : A.MemApprox s q f) : f ∈ closure (⋃ n, A n) :=
  (tendsto_approxError_zero_iff f).1
    (tendsto_approxError_zero_of_pow (tendsto_approxError_pow_zero_of_memApprox hq hs hf))

end ApproximationScheme
