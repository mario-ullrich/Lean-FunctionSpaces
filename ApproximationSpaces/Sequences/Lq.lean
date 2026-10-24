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

The file adds what Mathlib lacks: the explicit formulas, homogeneity for `ℝ≥0∞` scalars
(also of `L_p` norms of `[0, ∞]`-valued functions, `MeasureTheory.eLpNorm_const_mul_ennreal`),
**monotonicity in `q`** (`lqNorm r a ≤ lqNorm q a` for `1 ≤ q ≤ r`; Mathlib has only the
inclusion `lp.monotone`, without the norm bound), the Cauchy–Schwarz inequality
`∑_k a_k b_k ≤ ‖a‖_{ℓ_2} ‖b‖_{ℓ_2}` for series and for finite sums
(`ENNReal.lqNorm_one_mul_le`, `ENNReal.sum_mul_le_lqNorm_two_mul`), the splitting off of the
first term, tails of sequences (`ENNReal.lqNorm_ite_le_eq`), sequences with one nonzero term
(`Rd.lqNorm_ite_eq`), reindexing along bijections and injections
(`ENNReal.lqNorm_comp_equiv`, `ENNReal.lqNorm_extend_zero`), the `ℓ_q` norm of the geometric
sequence for every `q` (`ENNReal.dyadicGeomConst`), and the **dyadic weights**
`dyadicWeight s k = 2 ^ (k s)` that every approximation space uses.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ENNReal

/-- The **`ℓ_q` norm** of a family `a : ι → [0, ∞]`: `(∑_i a_i ^ q) ^ (1/q)` for `q < ∞` and
`sup_i a_i` for `q = ∞`, defined as the `L_q` norm for the counting measure.  The index set is `ℕ`
for sequences, `ℕ^d` for the spaces of dominating mixed smoothness and a finite set for the
coefficients of one level of atoms or wavelets; the general lemmas hold for every countable `ι`
with measurable singletons. -/
noncomputable def lqNorm {ι : Type*} [MeasurableSpace ι] (q : ℝ≥0∞) (a : ι → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm a q Measure.count

section Generic

variable {ι : Type*} [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
  {q r : ℝ≥0∞} {a b : ι → ℝ≥0∞}

/-- Every sequence is measurable for the counting measure; this is the side condition of the
Mathlib lemmas on `eLpNorm`. -/
theorem aestronglyMeasurable_count (a : ι → ℝ≥0∞) : AEStronglyMeasurable a Measure.count :=
  (measurable_of_countable a).aestronglyMeasurable

/-- `‖a‖_{ℓ_∞} = sup_n a_n`. -/
theorem lqNorm_top (a : ι → ℝ≥0∞) : lqNorm ∞ a = ⨆ n, a n := by
  simp [lqNorm, eLpNorm_exponent_top (aestronglyMeasurable_count a)]

/-- `‖a‖_{ℓ_q} = (∑_n a_n^q)^(1/q)` for `0 < q < ∞`. -/
theorem lqNorm_eq_tsum (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ι → ℝ≥0∞) :
    lqNorm q a = (∑' n, a n ^ q.toReal) ^ (1 / q.toReal) := by
  rw [lqNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq (aestronglyMeasurable_count a),
    lintegral_count]
  rfl

/-- `‖a‖_{ℓ_1} = ∑_n a_n`. -/
theorem lqNorm_one (a : ι → ℝ≥0∞) : lqNorm 1 a = ∑' n, a n := by
  simp [lqNorm_eq_tsum one_ne_zero one_ne_top]

/-- For `1 ≤ q < ∞` the exponent `q.toReal` is at least `1`. -/
theorem one_le_toReal_of_one_le (hq : 1 ≤ q) (hq' : q ≠ ∞) : 1 ≤ q.toReal := by
  simpa using ENNReal.toReal_mono hq' hq

/-- The `q`-th power of the norm is the sum of the `q`-th powers. -/
theorem lqNorm_rpow (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ι → ℝ≥0∞) :
    lqNorm q a ^ q.toReal = ∑' n, a n ^ q.toReal := by
  have hp : q.toReal ≠ 0 := (ENNReal.toReal_pos hq0 hq).ne'
  rw [lqNorm_eq_tsum hq0 hq, one_div, ENNReal.rpow_inv_rpow hp]

/-- **The square of the `ℓ_2` norm** is the sum of the squares:
`‖a‖_{ℓ_2}² = ∑_i a_i²` (`ENNReal.lqNorm_rpow` with `q = 2`, natural exponent). -/
theorem lqNorm_two_sq (a : ι → ℝ≥0∞) : lqNorm 2 a ^ 2 = ∑' i, a i ^ 2 := by
  have h := lqNorm_rpow two_ne_zero ofNat_ne_top a
  simpa only [toReal_ofNat, rpow_two] using h

/-- **The Cauchy–Schwarz inequality for nonnegative sequences**:
`∑_k a_k b_k ≤ ‖a‖_{ℓ_2} ‖b‖_{ℓ_2}` for families `a, b` in `[0, ∞]` indexed by a countable set
(Mathlib's `ENNReal.lintegral_mul_le_Lp_mul_Lq` for the counting measure). -/
theorem lqNorm_one_mul_le (a b : ι → ℝ≥0∞) :
    lqNorm 1 (fun k => a k * b k) ≤ lqNorm 2 a * lqNorm 2 b := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ι)
    Real.HolderConjugate.two_two (measurable_of_countable a).aemeasurable
    (measurable_of_countable b).aemeasurable
  rw [lqNorm_one, lqNorm_eq_tsum two_ne_zero ofNat_ne_top, lqNorm_eq_tsum two_ne_zero ofNat_ne_top]
  simpa [lintegral_count] using h

/-- **The Cauchy–Schwarz inequality for finite sums against `ℓ_2` norms**:
`∑_{j ∈ s} a_j b_j ≤ ‖a‖_{ℓ_2} ‖b‖_{ℓ_2}` for every finite set `s` and all families `a, b` in
`[0, ∞]` indexed by a countable set: a finite sum is at most the series
(`ENNReal.sum_le_tsum`), which is the `ℓ_1` norm of the products (`ENNReal.lqNorm_one`), and
`ENNReal.lqNorm_one_mul_le` bounds that. -/
theorem sum_mul_le_lqNorm_two_mul (s : Finset ι) (a b : ι → ℝ≥0∞) :
    ∑ j ∈ s, a j * b j ≤ lqNorm 2 a * lqNorm 2 b :=
  (ENNReal.sum_le_tsum s).trans ((lqNorm_one _).symm.trans_le (lqNorm_one_mul_le a b))

omit [Countable ι] [MeasurableSingletonClass ι] in
/-- The zero family has norm `0`. -/
@[simp]
theorem lqNorm_zero_right (q : ℝ≥0∞) : lqNorm q (fun _ : ι => (0 : ℝ≥0∞)) = 0 := eLpNorm_fun_zero

/-- The exponent `0` is degenerate: `eLpNorm` assigns it the value `0`.  The statements below
with a hypothesis `1 ≤ q` need it; the others hold for every `q`. -/
@[simp]
theorem lqNorm_zero_left (a : ι → ℝ≥0∞) : lqNorm 0 a = 0 :=
  eLpNorm_exponent_zero (aestronglyMeasurable_count a)

omit [Countable ι] in
/-- Every term is bounded by the norm. -/
theorem le_lqNorm (hq : q ≠ 0) (a : ι → ℝ≥0∞) (n : ι) : a n ≤ lqNorm q a :=
  enorm_le_eLpNorm_count a n hq

/-- The `ℓ_q` norm is monotone in the sequence. -/
theorem lqNorm_mono (h : ∀ n, a n ≤ b n) : lqNorm q a ≤ lqNorm q b :=
  eLpNorm_mono_enorm (aestronglyMeasurable_count a) h

omit [Countable ι] [MeasurableSingletonClass ι] in
/-- **Minkowski's inequality** for `ℓ_q`, `1 ≤ q ≤ ∞`. -/
theorem lqNorm_add_le (hq : 1 ≤ q) (a b : ι → ℝ≥0∞) :
    lqNorm q (fun n => a n + b n) ≤ lqNorm q a + lqNorm q b :=
  eLpNorm_add_le (f := a) (g := b) hq

/-- **Homogeneity**: `‖c a‖_q = c ‖a‖_q` for every `c ∈ ℝ≥0∞`. -/
theorem lqNorm_const_mul (c : ℝ≥0∞) (a : ι → ℝ≥0∞) :
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

/-- **Comparable sequences have finite `ℓ_q` norms together**: if `a ≤ M b` and `b ≤ K a` with
finite `K, M`, then `‖a‖_q < ∞ ↔ ‖b‖_q < ∞`. -/
theorem lqNorm_lt_top_iff_of_le_mul {a b : ι → ℝ≥0∞} {K M : ℝ≥0∞} (hK : K ≠ ∞) (hM : M ≠ ∞)
    (hab : ∀ n, a n ≤ M * b n) (hba : ∀ n, b n ≤ K * a n) :
    lqNorm q a < ∞ ↔ lqNorm q b < ∞ := by
  constructor
  · intro h
    calc lqNorm q b ≤ lqNorm q (fun n => K * a n) := lqNorm_mono hba
      _ = K * lqNorm q a := lqNorm_const_mul K a
      _ < ∞ := ENNReal.mul_lt_top hK.lt_top h
  · intro h
    calc lqNorm q a ≤ lqNorm q (fun n => M * b n) := lqNorm_mono hab
      _ = M * lqNorm q b := lqNorm_const_mul M b
      _ < ∞ := ENNReal.mul_lt_top hM.lt_top h

/-- **Monotonicity in the exponent**: for `1 ≤ q ≤ r`, `‖a‖_r ≤ ‖a‖_q`.  Proof: with
`M = ‖a‖_q`, each term satisfies `a n ^ r ≤ M ^ (r - q) a n ^ q`; sum over `n`. -/
theorem lqNorm_le_lqNorm_of_le (hq : 1 ≤ q) (hqr : q ≤ r) (a : ι → ℝ≥0∞) :
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

/-- `‖a‖_{ℓ_q} ≤ ‖a‖_{ℓ_1} = ∑_i a_i` for `q ≥ 1`. -/
theorem lqNorm_le_lqNorm_one (hq : 1 ≤ q) (a : ι → ℝ≥0∞) : lqNorm q a ≤ ∑' n, a n := by
  simpa [lqNorm_one] using lqNorm_le_lqNorm_of_le le_rfl hq a

/-- A family that vanishes outside a finite set `s` has `‖a‖_{ℓ_q} ≤ ∑_{i ∈ s} a_i` for
`q ≥ 1` (`ENNReal.lqNorm_le_lqNorm_one`). -/
theorem lqNorm_le_sum_of_eq_zero (hq : 1 ≤ q) (s : Finset ι) (ha : ∀ i ∉ s, a i = 0) :
    lqNorm q a ≤ ∑ i ∈ s, a i :=
  (lqNorm_le_lqNorm_one hq a).trans_eq (tsum_eq_sum ha)

/-- For a finite index set, `‖a‖_{ℓ_q} = (∑_i a_i^q)^(1/q)` for `0 < q < ∞`. -/
theorem lqNorm_eq_sum [Fintype ι] (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ι → ℝ≥0∞) :
    lqNorm q a = (∑ i, a i ^ q.toReal) ^ (1 / q.toReal) := by
  rw [lqNorm_eq_tsum hq0 hq, tsum_fintype]

/-- For a finite index set, a family bounded by `B` has `‖a‖_{ℓ_q} ≤ (#ι)^(1/q) B`, `q ≠ 0`. -/
theorem lqNorm_le_card_rpow_mul [Fintype ι] (hq0 : q ≠ 0) {B : ℝ≥0∞} (h : ∀ i, a i ≤ B) :
    lqNorm q a ≤ (Fintype.card ι : ℝ≥0∞) ^ (1 / q.toReal) * B := by
  rcases eq_or_ne q ∞ with rfl | hq
  · have h0 : (1 : ℝ) / (∞ : ℝ≥0∞).toReal = 0 := by simp
    rw [lqNorm_top, h0, ENNReal.rpow_zero, one_mul]
    exact iSup_le h
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_sum hq0 hq]
  calc (∑ i, a i ^ q.toReal) ^ (1 / q.toReal)
      ≤ (∑ _i : ι, B ^ q.toReal) ^ (1 / q.toReal) := by
        gcongr with i
        exact h i
    _ = ((Fintype.card ι : ℝ≥0∞) * B ^ q.toReal) ^ (1 / q.toReal) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ≥0∞) ^ (1 / q.toReal) * B := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq'.ne', ENNReal.rpow_one]

/-- **The `ℓ_q` norm on a finite product**: `‖a‖_{ℓ_q(M × N)}^q = ∑_m ‖a_{m,·}‖_{ℓ_q(N)}^q` for
`0 < q < ∞`. -/
theorem lqNorm_prod_rpow {M N : Type*} [Fintype M] [Fintype N] [MeasurableSpace M]
    [MeasurableSpace N] [MeasurableSingletonClass M] [MeasurableSingletonClass N] (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (a : M × N → ℝ≥0∞) :
    lqNorm q a ^ q.toReal = ∑ m, lqNorm q (fun n => a (m, n)) ^ q.toReal := by
  rw [lqNorm_rpow hq0 hq, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lqNorm_rpow hq0 hq, tsum_fintype]

/-! ### Reindexing -/

variable {ι' : Type*} [MeasurableSpace ι'] [Countable ι'] [MeasurableSingletonClass ι']

/-- **Reindexing by a bijection** does not change the `ℓ_q` norm: `‖a ∘ e‖_q = ‖a‖_q`. -/
theorem lqNorm_comp_equiv (e : ι ≃ ι') (a : ι' → ℝ≥0∞) : lqNorm q (a ∘ e) = lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [lqNorm_zero_left]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top]
    exact e.iSup_comp
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  congr 1
  exact e.tsum_eq fun n => a n ^ q.toReal

/-- **Extension by zero along an injective map** does not change the `ℓ_q` norm: if
`g : ι → ι'` is injective, the family on `ι'` equal to `a i` at `g i` and to `0` off the range
of `g` has the norm of `a`. -/
theorem lqNorm_extend_zero {g : ι → ι'} (hg : Function.Injective g) (a : ι → ℝ≥0∞) :
    lqNorm q (Function.extend g a 0) = lqNorm q a := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [lqNorm_zero_left]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, lqNorm_top]
    exact iSup_extend_bot hg a
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq]
  congr 1
  have hext : ∀ n, Function.extend g a 0 n ^ q.toReal =
      Function.extend g (fun i => a i ^ q.toReal) 0 n :=
    fun n => by
      rw [Function.apply_extend (· ^ q.toReal) g 0 n]
      congr 1
      funext m
      simp [ENNReal.zero_rpow_of_pos hp]
  simp_rw [hext]
  exact tsum_extend_zero hg _

/-- **Restriction to the range of an injective map** does not increase the `ℓ_q` norm:
`‖a ∘ g‖_q ≤ ‖a‖_q`. -/
theorem lqNorm_comp_le_of_injective {g : ι → ι'} (hg : Function.Injective g) (a : ι' → ℝ≥0∞) :
    lqNorm q (a ∘ g) ≤ lqNorm q a := by
  rw [← lqNorm_extend_zero hg]
  refine lqNorm_mono fun n => ?_
  by_cases hn : ∃ i, g i = n
  · obtain ⟨i, rfl⟩ := hn
    rw [hg.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hn]
    exact zero_le

end Generic

variable {q r : ℝ≥0∞} {a b : ℕ → ℝ≥0∞}

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

/-- **Splitting off the first `m` terms**: `‖a‖_q ≤ a 0 + ⋯ + a (m - 1) + ‖(a (n + m))ₙ‖_q`. -/
theorem lqNorm_le_sum_range_add_shift (hq : 1 ≤ q) (a : ℕ → ℝ≥0∞) (m : ℕ) :
    lqNorm q a ≤ ∑ j ∈ Finset.range m, a j + lqNorm q (fun n => a (n + m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hshift : (fun n => a (n + 1 + m)) = fun n => a (n + (m + 1)) := by
      funext n
      congr 1
      omega
    calc lqNorm q a ≤ ∑ j ∈ Finset.range m, a j + lqNorm q (fun n => a (n + m)) := ih
      _ ≤ ∑ j ∈ Finset.range m, a j + (a (0 + m) + lqNorm q (fun n => a (n + 1 + m))) := by
          gcongr
          exact lqNorm_le_head_add_shift hq (fun n => a (n + m))
      _ = ∑ j ∈ Finset.range (m + 1), a j + lqNorm q (fun n => a (n + (m + 1))) := by
          rw [hshift, Finset.sum_range_succ, zero_add, add_assoc]

/-- The norm of a geometric sequence: `‖(r ^ k)ₖ‖_q ≤ (1 - r)⁻¹`, the value of the series
for `q = 1`. -/
theorem lqNorm_geometric_le (hq : 1 ≤ q) (r : ℝ≥0∞) :
    lqNorm q (fun k => r ^ k) ≤ (1 - r)⁻¹ := by
  calc lqNorm q (fun k => r ^ k) ≤ lqNorm 1 (fun k => r ^ k) := lqNorm_le_lqNorm_of_le le_rfl hq _
    _ = (1 - r)⁻¹ := by rw [lqNorm_one, ENNReal.tsum_geometric]

/-! ### Dyadic weights -/

/-- The **dyadic weight** `2 ^ (k s)`: the factor by which the error `E_{2^k}` is multiplied
in the dyadic form of an approximation space of smoothness `s`. -/
noncomputable def dyadicWeight (s : ℝ) (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((k : ℝ) * s)

variable {s t : ℝ}

/-- `2^(0·s) = 1`. -/
@[simp]
theorem dyadicWeight_zero_right (s : ℝ) : dyadicWeight s 0 = 1 := by simp [dyadicWeight]

/-- `2^(k·0) = 1`. -/
@[simp]
theorem dyadicWeight_zero_left (k : ℕ) : dyadicWeight 0 k = 1 := by simp [dyadicWeight]

/-- The dyadic weights are finite. -/
theorem dyadicWeight_ne_top (s : ℝ) (k : ℕ) : dyadicWeight s k ≠ ∞ :=
  ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top

/-- The dyadic weights are finite. -/
theorem dyadicWeight_lt_top (s : ℝ) (k : ℕ) : dyadicWeight s k < ∞ :=
  (dyadicWeight_ne_top s k).lt_top

/-- The dyadic weights are positive. -/
theorem dyadicWeight_pos (s : ℝ) (k : ℕ) : 0 < dyadicWeight s k :=
  ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top

/-- The dyadic weights are nonzero. -/
theorem dyadicWeight_ne_zero (s : ℝ) (k : ℕ) : dyadicWeight s k ≠ 0 := (dyadicWeight_pos s k).ne'

/-- `2^(k(s+t)) = 2^(ks) 2^(kt)`. -/
theorem dyadicWeight_add (s t : ℝ) (k : ℕ) :
    dyadicWeight (s + t) k = dyadicWeight s k * dyadicWeight t k := by
  rw [dyadicWeight, mul_add, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]; rfl

/-- `2^((k+j)s) = 2^(ks) 2^(js)`. -/
theorem dyadicWeight_add_nat (s : ℝ) (k j : ℕ) :
    dyadicWeight s (k + j) = dyadicWeight s k * dyadicWeight s j := by
  rw [dyadicWeight, Nat.cast_add, add_mul, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  rfl

/-- `2^((k+1)s) = 2^s 2^(ks)`. -/
theorem dyadicWeight_succ (s : ℝ) (k : ℕ) :
    dyadicWeight s (k + 1) = 2 ^ s * dyadicWeight s k := by
  rw [dyadicWeight_add_nat, mul_comm]; simp [dyadicWeight]

/-- `2^(-ks) = (2^(ks))⁻¹`. -/
theorem dyadicWeight_neg (s : ℝ) (k : ℕ) : dyadicWeight (-s) k = (dyadicWeight s k)⁻¹ := by
  rw [dyadicWeight, mul_neg, ENNReal.rpow_neg]; rfl

/-- `2^(-ks) 2^(ks) = 1`. -/
theorem dyadicWeight_neg_mul_self (s : ℝ) (k : ℕ) : dyadicWeight (-s) k * dyadicWeight s k = 1 := by
  rw [dyadicWeight_neg, ENNReal.inv_mul_cancel (dyadicWeight_ne_zero s k) (dyadicWeight_ne_top s k)]

/-- `2^(ks) 2^(-ks) = 1`. -/
theorem dyadicWeight_mul_neg_self (s : ℝ) (k : ℕ) : dyadicWeight s k * dyadicWeight (-s) k = 1 := by
  rw [mul_comm, dyadicWeight_neg_mul_self]

/-- `(2^(ks))^p = 2^(k s p)`. -/
theorem dyadicWeight_rpow (s p : ℝ) (k : ℕ) : dyadicWeight s k ^ p = dyadicWeight (s * p) k := by
  rw [dyadicWeight, dyadicWeight, ← ENNReal.rpow_mul, mul_assoc]

/-- The dyadic weights are a geometric sequence with ratio `2 ^ s`. -/
theorem dyadicWeight_eq_pow (s : ℝ) (k : ℕ) : dyadicWeight s k = ((2 : ℝ≥0∞) ^ s) ^ k := by
  rw [dyadicWeight, mul_comm, ENNReal.rpow_mul_natCast]

/-- The squared dyadic weight: `(2^(ks))² = (4^k)^s`. -/
theorem dyadicWeight_sq (s : ℝ) (k : ℕ) : dyadicWeight s k ^ 2 = ((4 : ℝ≥0∞) ^ k) ^ s := by
  rw [dyadicWeight, ← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_natCast (4 : ℝ≥0∞) k,
    ← ENNReal.rpow_mul, show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- For `s ≥ 0` the dyadic weights increase in `k`. -/
theorem dyadicWeight_mono (hs : 0 ≤ s) : Monotone (dyadicWeight s) := fun _ _ hkj =>
  ENNReal.rpow_le_rpow_of_exponent_le one_le_two
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hkj) hs)

/-- For a fixed `k`, the weight `2 ^ (k s)` increases with `s`. -/
theorem dyadicWeight_le_of_le {s t : ℝ} (h : s ≤ t) (k : ℕ) : dyadicWeight s k ≤ dyadicWeight t k :=
  ENNReal.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k))

/-- For `s ≤ 0` the weights decrease. -/
theorem dyadicWeight_anti (hs : s ≤ 0) : Antitone (dyadicWeight s) := fun _ _ hkj =>
  ENNReal.rpow_le_rpow_of_exponent_le one_le_two
    (mul_le_mul_of_nonpos_right (Nat.cast_le.2 hkj) hs)

/-- For `s ≥ 0`, `1 ≤ 2^(ks)`. -/
theorem one_le_dyadicWeight (hs : 0 ≤ s) (k : ℕ) : 1 ≤ dyadicWeight s k := by
  simpa using dyadicWeight_mono hs (Nat.zero_le k)

/-- `(2 ^ k) ^ s = 2 ^ (k s)`: the dyadic weight is the power weight at the dyadic point. -/
theorem natCast_two_pow_rpow (s : ℝ) (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ≥0∞) ^ s = dyadicWeight s k := by
  rw [dyadicWeight, ENNReal.rpow_natCast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- `(2^(jn))^t = 2^(j n t)`: a power of the volume factor `2^(jn)` is a dyadic weight. -/
theorem two_pow_rpow_eq_dyadicWeight (j n : ℕ) (t : ℝ) :
    ((2 : ℝ≥0∞) ^ (j * n)) ^ t = dyadicWeight (n * t) j := by
  rw [dyadicWeight, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- The product rule for powers of `2` in `[0, ∞]`: `2^x 2^y = 2^(x+y)` for all real `x, y`
(Mathlib's `ENNReal.rpow_add` with the side conditions `2 ≠ 0` and `2 ≠ ∞` discharged). -/
theorem two_rpow_mul_two_rpow (x y : ℝ) : (2 : ℝ≥0∞) ^ x * 2 ^ y = 2 ^ (x + y) :=
  (ENNReal.rpow_add x y two_ne_zero ENNReal.ofNat_ne_top).symm

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

/-- `∑ₖ 2^(-kα) = (1 - 2^(-α))⁻¹`. -/
theorem tsum_dyadicWeight_neg (α : ℝ) :
    ∑' k, dyadicWeight (-α) k = (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ := by
  simp_rw [dyadicWeight_eq_pow]
  exact ENNReal.tsum_geometric _

/-- The constant `(1 - 2^(-α q))^(-1/q)` of the dyadic geometric sequence `(2^(-kα))_k`, with
the value `1` for `q = ∞` (where `q.toReal = 0`).  For `α ≥ 0` and `q ≠ 0` it is the `ℓ_q` norm
of that sequence (`ENNReal.lqNorm_dyadicWeight_neg_eq_dyadicGeomConst`). -/
noncomputable def dyadicGeomConst (α : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  ((1 - (2 : ℝ≥0∞) ^ (-(α * q.toReal)))⁻¹) ^ (1 / q.toReal)

/-- **The geometric sequence in `ℓ_q`** for every `q ≠ 0`:
`‖(2^(-kα))_k‖_{ℓ_q} = dyadicGeomConst α q` for `α ≥ 0`. -/
theorem lqNorm_dyadicWeight_neg_eq_dyadicGeomConst {α : ℝ} (hα : 0 ≤ α) (hq0 : q ≠ 0) :
    lqNorm q (dyadicWeight (-α)) = dyadicGeomConst α q := by
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [lqNorm_top, dyadicGeomConst, toReal_top, _root_.div_zero, rpow_zero]
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0 (dyadicWeight_zero_right _).ge)
    exact (dyadicWeight_anti (neg_nonpos.2 hα) (Nat.zero_le k)).trans_eq
      (dyadicWeight_zero_right _)
  rw [lqNorm_eq_tsum hq0 hq, dyadicGeomConst]
  simp_rw [dyadicWeight_rpow, neg_mul]
  rw [tsum_dyadicWeight_neg]

/-- The geometric sequence for every `q`: `‖(2^(-kα))_k‖_{ℓ_q} ≤ dyadicGeomConst α q` for
`α ≥ 0`; for `q = 0` the left side is `0`. -/
theorem lqNorm_dyadicWeight_neg_le_dyadicGeomConst {α : ℝ} (hα : 0 ≤ α) :
    lqNorm q (dyadicWeight (-α)) ≤ dyadicGeomConst α q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [lqNorm_zero_left]
  exact (lqNorm_dyadicWeight_neg_eq_dyadicGeomConst hα hq0).le

/-- The constant `dyadicGeomConst α q` is at least `1`, for every `α` and `q`. -/
theorem one_le_dyadicGeomConst (α : ℝ) (q : ℝ≥0∞) : 1 ≤ dyadicGeomConst α q :=
  (one_rpow _).symm.trans_le
    (rpow_le_rpow (one_le_one_sub_two_rpow_neg_inv _) (by positivity))

/-- The constant `dyadicGeomConst α q` is finite for `α > 0`. -/
theorem dyadicGeomConst_ne_top {α : ℝ} (hα : 0 < α) (q : ℝ≥0∞) : dyadicGeomConst α q ≠ ∞ := by
  rcases (ENNReal.toReal_nonneg (a := q)).eq_or_lt with h | h
  · rw [dyadicGeomConst, ← h, _root_.div_zero, rpow_zero]
    exact one_ne_top
  exact rpow_ne_top_of_nonneg (by positivity)
    (one_sub_two_rpow_neg_inv_ne_top (_root_.mul_pos hα h))

/-- `∑ₖ 2^(-k) = 2`. -/
theorem tsum_dyadicWeight_neg_one : ∑' k, dyadicWeight (-1) k = 2 := by
  simp_rw [dyadicWeight_eq_pow, ENNReal.rpow_neg_one]
  exact ENNReal.tsum_geometric_two

/-- `‖(2^(-k))ₖ‖_q ≤ 2`. -/
theorem lqNorm_dyadicWeight_neg_one_le (hq : 1 ≤ q) : lqNorm q (dyadicWeight (-1)) ≤ 2 := by
  calc lqNorm q (dyadicWeight (-1)) ≤ ∑' k, dyadicWeight (-1) k := lqNorm_le_lqNorm_one hq _
    _ = 2 := tsum_dyadicWeight_neg_one

/-! ### Powers of two as dyadic weights -/

/-- `ofReal (2^x) = 2^x`: the real power of two as an element of `[0, ∞]`. -/
theorem ofReal_two_rpow (x : ℝ) : ENNReal.ofReal ((2 : ℝ) ^ x) = (2 : ℝ≥0∞) ^ x := by
  rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- `2^k` as a dyadic weight. -/
theorem ofReal_two_pow_eq (k : ℕ) : ENNReal.ofReal (2 ^ k) = dyadicWeight 1 k := by
  rw [← ENNReal.natCast_two_pow_rpow, ENNReal.rpow_one, ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]
  push_cast
  rfl

/-- `(2^i)^n = 2^(in)` as a dyadic weight. -/
theorem ofReal_two_pow_pow (i n : ℕ) :
    ENNReal.ofReal (((2 : ℝ) ^ i) ^ n) = dyadicWeight n i := by
  rw [ENNReal.dyadicWeight_eq_pow, ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← pow_mul, ← pow_mul, mul_comm]

/-- `(2^(-k))^l = 2^(-kl)` as a dyadic weight. -/
theorem ofReal_one_div_two_pow_pow (k l : ℕ) :
    ENNReal.ofReal ((1 / 2 ^ k) ^ l) = dyadicWeight (-(l : ℝ)) k := by
  have h : (1 / 2 ^ k : ℝ) ^ l = ((2 : ℝ) ^ (-(l : ℝ))) ^ k := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow, inv_pow, ← pow_mul,
      ← pow_mul, mul_comm]
  rw [ENNReal.dyadicWeight_eq_pow, h, ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- `(2^j h)^θ ≤ 2^(-(k-j)θ)` for `0 ≤ h ≤ 2^(-k)`, `j ≤ k` and `θ ≥ 0`. -/
theorem ofReal_two_pow_mul_rpow_le {j k : ℕ} (hjk : j ≤ k) {h : ℝ} (hh : h ≤ 1 / 2 ^ k) {θ : ℝ}
    (hθ : 0 ≤ θ) : ENNReal.ofReal (2 ^ j * h) ^ θ ≤ dyadicWeight (-θ) (k - j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left]
  have h1 : (2 : ℝ) ^ j * h ≤ ((2 : ℝ) ^ m)⁻¹ := by
    rw [pow_add] at hh
    calc (2 : ℝ) ^ j * h ≤ 2 ^ j * (1 / (2 ^ j * 2 ^ m)) := by gcongr
      _ = ((2 : ℝ) ^ m)⁻¹ := by field_simp
  calc ENNReal.ofReal (2 ^ j * h) ^ θ ≤ ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) ^ θ :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) hθ
    _ = dyadicWeight (-θ) m := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.inv_rpow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          dyadicWeight, mul_neg, ENNReal.rpow_neg]

/-! ### Subadditive functionals and series -/

/-- **Subadditive functionals and multiple series**: if `Q` is subadditive, `Q a ≤ C ‖a‖` with
`C < ∞`, and the partial sums of `∑ u_k` over finite sets `S_J` converge to `F`, then
`Q F ≤ ∑_k Q(u_k)`. -/
theorem le_tsum_of_tendsto_finsetSum {E ι : Type*} [NormedAddCommGroup E] {Q : E → ℝ≥0∞}
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hadd : ∀ a b, Q (a + b) ≤ Q a + Q b) (hle : ∀ a, Q a ≤ C * ‖a‖ₑ)
    {S : ℕ → Finset ι} {u : ι → E} {F : E}
    (hu : Tendsto (fun J => ∑ k ∈ S J, u k) atTop (nhds F)) :
    Q F ≤ ∑' k, Q (u k) := by
  have hsum : ∀ s : Finset ι, Q (∑ k ∈ s, u k) ≤ ∑ k ∈ s, Q (u k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hle 0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (hadd _ _).trans (add_le_add le_rfl ih)
  have hJ : ∀ J, Q F ≤ ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ := fun J => by
    calc Q F = Q (∑ k ∈ S J, u k + (F - ∑ k ∈ S J, u k)) := by rw [add_sub_cancel]
      _ ≤ Q (∑ k ∈ S J, u k) + Q (F - ∑ k ∈ S J, u k) := hadd _ _
      _ ≤ ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ :=
          add_le_add ((hsum _).trans (ENNReal.sum_le_tsum _)) (hle _)
  have h1 : Tendsto (fun J => F - ∑ k ∈ S J, u k) atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := F)).sub hu
    rwa [sub_self] at this
  have h2 : Tendsto (fun J => ‖F - ∑ k ∈ S J, u k‖ₑ) atTop (nhds 0) := by
    have h3 := (continuous_enorm.tendsto (0 : E)).comp h1
    rw [enorm_zero] at h3
    exact h3
  have hlim : Tendsto (fun J => ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ) atTop
      (nhds (∑' k, Q (u k) + C * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul h2 (Or.inr hC))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hJ)

/-- **Subadditive functionals and series**: if `Q` is subadditive, `Q a ≤ C ‖a‖` with `C < ∞`, and
the partial sums of `∑ u_j` converge to `f`, then `Q f ≤ ∑_j Q(u_j)`. -/
theorem le_tsum_of_tendsto_sum {E : Type*} [NormedAddCommGroup E] {Q : E → ℝ≥0∞} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hadd : ∀ a b, Q (a + b) ≤ Q a + Q b) (hle : ∀ a, Q a ≤ C * ‖a‖ₑ)
    {u : ℕ → E} {f : E}
    (hu : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), u j) atTop (nhds f)) :
    Q f ≤ ∑' j, Q (u j) :=
  le_tsum_of_tendsto_finsetSum (S := fun J => Finset.range (J + 1)) hC hadd hle hu

/-- **Weighted sequences are summable**: `∑_j a_j ≤ (1 - 2^(-s))⁻¹ ‖(2^(js) a_j)_j‖_{ℓ_q}`,
since `a_j ≤ 2^(-js) ‖(2^(js) a_j)_j‖_{ℓ_q}`. -/
theorem tsum_le_lqNorm_dyadicWeight {q : ℝ≥0∞} (hq : 1 ≤ q) (s : ℝ) (a : ℕ → ℝ≥0∞) :
    ∑' j, a j ≤ (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun j => dyadicWeight s j * a j) := by
  set X := lqNorm q (fun j => dyadicWeight s j * a j)
  calc ∑' j, a j ≤ ∑' j, dyadicWeight (-s) j * X := ENNReal.tsum_le_tsum fun j => by
        calc a j = dyadicWeight (-s) j * (dyadicWeight s j * a j) := by
              rw [← mul_assoc, dyadicWeight_neg_mul_self, one_mul]
          _ ≤ dyadicWeight (-s) j * X := mul_le_mul' le_rfl
              (le_lqNorm (zero_lt_one.trans_le hq).ne' (fun j => dyadicWeight s j * a j) j)
    _ = (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
        rw [ENNReal.tsum_mul_right, tsum_dyadicWeight_neg]

/-- **A series with weighted bounds**: if the partial sums of `∑ u_j` converge to `F` and
`‖u_j‖ ≤ K b_j`, then `‖F‖ ≤ K (1 - 2^(-s))⁻¹ ‖(2^(js) b_j)_j‖_{ℓ_q}`
(`ENNReal.tsum_le_lqNorm_dyadicWeight`). -/
theorem enorm_le_of_tendsto_sum {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {F : E}
    (hu : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), u j) atTop (nhds F)) {K : ℝ≥0∞}
    {b : ℕ → ℝ≥0∞} (hb : ∀ j, ‖u j‖ₑ ≤ K * b j) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ‖F‖ₑ ≤ K * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun j => dyadicWeight s j * b j) := by
  have h1 : ‖F‖ₑ ≤ ∑' j, ‖u j‖ₑ :=
    le_tsum_of_tendsto_sum (C := 1) ENNReal.one_ne_top (fun x y => enorm_add_le x y)
      (fun x => by rw [one_mul]) hu
  calc ‖F‖ₑ ≤ ∑' j, K * b j := h1.trans (ENNReal.tsum_le_tsum hb)
    _ = K * ∑' j, b j := ENNReal.tsum_mul_left
    _ ≤ K * ((1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun j => dyadicWeight s j * b j)) :=
        mul_le_mul' le_rfl (tsum_le_lqNorm_dyadicWeight hq s b)
    _ = _ := (mul_assoc _ _ _).symm

/-! ### Tails and partial sums -/

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

/-- **The `ℓ_q` norm of a tail is the norm of the shifted sequence**: for `0 < q < ∞`,
`‖(0, …, 0, a_N, a_{N+1}, …)‖_{ℓ_q} = ‖(a_{N+k})_k‖_{ℓ_q}` (`ENNReal.tsum_ite_le_eq`). -/
theorem lqNorm_ite_le_eq {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) (a : ℕ → ℝ≥0∞) (N : ℕ) :
    lqNorm q (fun j => if N ≤ j then a j else 0) = lqNorm q (fun k => a (N + k)) := by
  have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [lqNorm_eq_tsum hq0 hq, lqNorm_eq_tsum hq0 hq, ← tsum_ite_le_eq N (fun n => a n ^ q.toReal)]
  congr 1
  refine tsum_congr fun j => ?_
  split_ifs <;> simp [ENNReal.zero_rpow_of_pos hpos]

end ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### `L_p` norms of functions with values in `[0, ∞]` -/

/-- **Homogeneity** for a scalar `c ∈ [0, ∞]`: `‖c h‖_p = c ‖h‖_p` for measurable
`h : α → [0, ∞]` (Mathlib's `eLpNorm_const_smul` covers scalars in a normed division ring).
Measurability matters for `p = 0`: a non-measurable `h > 0` has `‖h‖_0 = ∞`, while `∞ · h = ∞`
is measurable with `‖∞ · h‖_0 = 0`. -/
theorem eLpNorm_const_mul_ennreal (c : ℝ≥0∞) {h : α → ℝ≥0∞} (hh : AEMeasurable h μ)
    (p : ℝ≥0∞) : eLpNorm (fun x => c * h x) p μ = c * eLpNorm h p μ := by
  have hch : AEStronglyMeasurable (fun x => c * h x) μ := (hh.const_mul c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hch, eLpNorm_exponent_zero hh.aestronglyMeasurable, mul_zero]
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hch, eLpNorm_exponent_top hh.aestronglyMeasurable]
    simp only [eLpNormEssSup, enorm_eq_self]
    exact ENNReal.essSup_const_mul
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hch,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hh.aestronglyMeasurable]
  simp only [enorm_eq_self]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  rw [lintegral_const_mul'' _ (hh.pow_const _), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

end MeasureTheory

/-- `(1 + t)^N ≤ 2^N (1 + t^N)` for `t ≥ 0`, from Mathlib's `add_pow_le`. -/
theorem one_add_pow_le_two_pow_mul {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  calc (1 + t) ^ N ≤ 2 ^ (N - 1) * (1 ^ N + t ^ N) := add_pow_le zero_le_one ht N
    _ ≤ 2 ^ N * (1 + t ^ N) := by
      rw [one_pow]
      gcongr
      · exact one_le_two
      · exact Nat.sub_le N 1

namespace Rd

open ENNReal (lqNorm)

/-- `‖(…, 0, x, 0, …)‖_{ℓ_q} = x` for a sequence with one nonzero term. -/
theorem lqNorm_ite_eq {q : ℝ≥0∞} (hq : 1 ≤ q) (j : ℕ) (x : ℝ≥0∞) :
    lqNorm q (fun i => if i = j then x else 0) = x := by
  rcases eq_or_ne q ∞ with rfl | hqt
  · rw [ENNReal.lqNorm_top]
    refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le j (by simp))
    split_ifs <;> simp
  · have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
    have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
    rw [ENNReal.lqNorm_eq_tsum hq0 hqt]
    have h : (fun i => (if i = j then x else 0) ^ q.toReal) =
        fun i => if i = j then x ^ q.toReal else 0 := funext fun i => by
      split_ifs <;> simp [ENNReal.zero_rpow_of_pos hpos]
    rw [h, tsum_ite_eq, one_div, ENNReal.rpow_rpow_inv hpos.ne']

end Rd
