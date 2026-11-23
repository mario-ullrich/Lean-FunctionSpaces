/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Sequences.Hardy
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.SuccPred.IntervalSucc

/-!
# A fractional Hardy inequality on `(0, 1]`

For `s > 1/2`, a measurable `u : ℝ → ℂ` that vanishes almost everywhere on an interval `(0, ε)`
satisfies (`Rd.lintegral_div_rpow_le_halfLineForm`)

`∫_0^1 |u(t)|² / t^(2s) dt ≤ K_s ∫_0^1 ∫_0^1 |u(t) - u(τ)|² / |t - τ|^(1+2s) dτ dt`,

with `K_s = 2^(2s+2) (1 - 2^(-(s-1/2)))^(-2)` (`Rd.halfLineHardyConst`), independent of `ε`. The
right side is the Gagliardo form of `u` on `(0, 1]` (`Rd.halfLineForm`). The proof is dyadic and
follows no single source:

* **Scaled dyadic intervals.** For `c > 0` the intervals `(c 2^(-k-1), c 2^(-k)]` are pairwise
  disjoint and cover `(0, c]` (`Real.pairwise_disjoint_Ioc_div_two_pow`,
  `Real.iUnion_Ioc_div_two_pow`). For `c = 1` they are the blocks `I_k` (`Rd.halfLineBlock`).
* **Two Minkowski steps** (`MeasureTheory.rpow_mul_lintegral_rpow_le`): for sets `A`, `B` of an
  s-finite measure space,
  `|B|^(1/2) ‖u‖_{L_2(A)} ≤ (∫_A ∫_B |u(t) - u(τ)|²)^(1/2) + |A|^(1/2) ‖u‖_{L_2(B)}`, from
  Minkowski's inequality in `L_2(B)` for `u(t) = (u(t) - u(τ)) + u(τ)` at each `t ∈ A` and then in
  `L_2(A)` (Mathlib's `ENNReal.lintegral_Lp_add_le`).
* **Weighted layers.** For a measurable `η : α → ℝ` on a measure space, `c > 0` and `s > 0`,
  `∑_k 2^(2ks) ∫_{0 < η ≤ c 2^(-k)} g ≤ (1 - 2^(-2s))⁻¹ c^(2s) ∫_{η > 0} g / min(η, 1)^(2s)`
  (`MeasureTheory.setLIntegral_preimage_Ioc_le_tsum`,
  `MeasureTheory.tsum_dyadicWeight_mul_setLIntegral_le`), by the layers of `η` between scaled
  dyadic heights and Hardy's inequality for tails.
* **Telescoping and Hardy's inequality.** A sequence in `[0, ∞]` with `m_k ≤ m_{k+1} + b_k` that
  vanishes from some index on is at most the tail sums of `b`
  (`ENNReal.le_tsum_of_le_add_of_eq_zero`), so Hardy's inequality for tails
  (`ENNReal.hardy_tail_le`) bounds `∑_k 2^(2αk) m_k²` by `(1 - 2^(-α))^(-2) ∑_k 2^(2αk) b_k²` for
  `α = s - 1/2` (`ENNReal.tsum_sq_le_of_le_add_of_eq_zero`). This is the only place where
  `s > 1/2` enters.
* **The blocks and the form.** The normalised block norms `m_k = |I_k|^(-1/2) ‖u‖_{L_2(I_k)}`
  satisfy `m_k ≤ m_{k+1} + b_k`, with `b_k` the normalised double integral over `I_k × I_{k+1}`
  (`Rd.dyadicWeight_mul_lintegral_halfLineBlock_le_add`). The integral `∫_0^1 |u|² t^(-2s)` is at
  most the weighted block sums (`Rd.lintegral_Ioc_div_rpow_le_tsum_halfLineBlock`), and the double
  integrals over the neighbouring blocks, where `|t - τ| ≤ 2^(-k)`, sum to at most the form
  (`Rd.tsum_dyadicWeight_mul_lintegral_le_halfLineForm`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Real

/-! ### Scaled dyadic intervals -/

/-- **Scaled dyadic intervals are disjoint**: for `c ≥ 0` the intervals
`(c 2^(-k-1), c 2^(-k)]`, `k ∈ ℕ`, are pairwise disjoint, as the intervals between the consecutive
terms of the decreasing sequence `c 2^(-k)` (Mathlib's `Antitone.pairwise_disjoint_on_Ioc_succ`). -/
theorem pairwise_disjoint_Ioc_div_two_pow {c : ℝ} (hc : 0 ≤ c) :
    Pairwise (Function.onFun Disjoint fun k : ℕ => Ioc (c / 2 ^ (k + 1)) (c / 2 ^ k)) := by
  have h : Antitone fun k : ℕ => c / 2 ^ k := fun i j hij =>
    div_le_div_of_nonneg_left hc (by positivity) (pow_le_pow_right₀ one_le_two hij)
  exact h.pairwise_disjoint_on_Ioc_succ

/-- **Scaled dyadic intervals cover `(0, c]`**: for `c > 0` every `0 < t ≤ c` has
`c 2^(-k-1) < t ≤ c 2^(-k)` for some `k ∈ ℕ` (Mathlib's `exists_nat_pow_near_of_lt_one` for `t/c`
with base `1/2`). -/
theorem iUnion_Ioc_div_two_pow {c : ℝ} (hc : 0 < c) :
    ⋃ k : ℕ, Ioc (c / 2 ^ (k + 1)) (c / 2 ^ k) = Ioc 0 c := by
  refine Subset.antisymm (iUnion_subset fun k t ht => ⟨lt_trans (by positivity) ht.1,
    ht.2.trans (div_le_self hc.le (one_le_pow₀ one_le_two))⟩) fun t ht => ?_
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near_of_lt_one (div_pos ht.1 hc)
    ((div_le_one hc).2 ht.2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [one_div_pow, lt_div_iff₀ hc, one_div_mul_eq_div] at h1
  rw [one_div_pow, div_le_iff₀ hc, one_div_mul_eq_div] at h2
  exact mem_iUnion.2 ⟨n, h1, h2⟩

end Real

namespace MeasureTheory

/-! ### Two Minkowski steps -/

/-- **Two Minkowski steps between two sets**: for a measurable `u : α → ℂ` on an s-finite measure
space and sets `A`, `B`,
`|B|^(1/2) ‖u‖_{L_2(A)} ≤ (∫_A ∫_B |u(t) - u(τ)|² dτ dt)^(1/2) + |A|^(1/2) ‖u‖_{L_2(B)}`.
At every `t ∈ A` the constant `u(t)` is `(u(t) - u(τ)) + u(τ)` as a function of `τ ∈ B`, so
Minkowski's inequality in `L_2(B)` (Mathlib's `ENNReal.lintegral_Lp_add_le`) gives
`|B|^(1/2) |u(t)| ≤ e(t) + ‖u‖_{L_2(B)}` with `e(t) = (∫_B |u(t) - u(τ)|² dτ)^(1/2)`, measurable
by Tonelli's theorem (Mathlib's `Measurable.lintegral_prod_right'`); Minkowski's inequality in
`L_2(A)` finishes the proof. -/
theorem rpow_mul_lintegral_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {u : α → ℂ} (hu : Measurable u) (A B : Set α) :
    μ B ^ (2⁻¹ : ℝ) * (∫⁻ t in A, ‖u t‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ) ≤
      (∫⁻ t in A, ∫⁻ τ in B, ‖u t - u τ‖ₑ ^ 2 ∂μ ∂μ) ^ (2⁻¹ : ℝ) +
        μ A ^ (2⁻¹ : ℝ) * (∫⁻ τ in B, ‖u τ‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ) := by
  set c := (∫⁻ τ in B, ‖u τ‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)
  set e : α → ℝ≥0∞ := fun t => (∫⁻ τ in B, ‖u t - u τ‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)
  have hF : Measurable fun p : α × α => ‖u p.1 - u p.2‖ₑ ^ 2 :=
    ((hu.comp measurable_fst).sub (hu.comp measurable_snd)).enorm.pow_const 2
  have he : Measurable e := (hF.lintegral_prod_right' (ν := μ.restrict B)).pow_const _
  have h2 : (0 : ℝ) ≤ 2⁻¹ := by norm_num
  have hpt : ∀ t, μ B ^ (2⁻¹ : ℝ) * ‖u t‖ₑ ≤ e t + c := fun t => by
    have hmink := ENNReal.lintegral_Lp_add_le (μ := μ.restrict B) (f := fun τ => ‖u t - u τ‖ₑ)
      (g := fun τ => ‖u τ‖ₑ) (hu.const_sub (u t)).enorm.aemeasurable hu.enorm.aemeasurable
      one_le_two
    simp only [Pi.add_apply, ENNReal.rpow_two, one_div] at hmink
    calc μ B ^ (2⁻¹ : ℝ) * ‖u t‖ₑ = (∫⁻ _ in B, ‖u t‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ) := by
          rw [setLIntegral_const, ENNReal.mul_rpow_of_nonneg _ _ h2, ← ENNReal.rpow_two,
            ENNReal.rpow_rpow_inv two_ne_zero, mul_comm]
      _ ≤ (∫⁻ τ in B, (‖u t - u τ‖ₑ + ‖u τ‖ₑ) ^ 2 ∂μ) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.rpow_le_rpow (lintegral_mono fun τ => ?_) h2
          refine pow_le_pow_left₀ zero_le ?_ 2
          calc ‖u t‖ₑ = ‖u t - u τ + u τ‖ₑ := by rw [sub_add_cancel]
            _ ≤ ‖u t - u τ‖ₑ + ‖u τ‖ₑ := enorm_add_le _ _
      _ ≤ e t + c := hmink
  have hmink := ENNReal.lintegral_Lp_add_le (μ := μ.restrict A) (f := e) (g := fun _ => c)
    he.aemeasurable aemeasurable_const one_le_two
  simp only [Pi.add_apply, ENNReal.rpow_two, one_div] at hmink
  calc μ B ^ (2⁻¹ : ℝ) * (∫⁻ t in A, ‖u t‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)
      = (∫⁻ t in A, (μ B ^ (2⁻¹ : ℝ) * ‖u t‖ₑ) ^ 2 ∂μ) ^ (2⁻¹ : ℝ) := by
        have hB : (μ B ^ (2⁻¹ : ℝ)) ^ 2 = μ B := by
          rw [← ENNReal.rpow_two, ENNReal.rpow_inv_rpow two_ne_zero]
        simp_rw [mul_pow, hB]
        rw [lintegral_const_mul _ (hu.enorm.pow_const 2), ENNReal.mul_rpow_of_nonneg _ _ h2]
    _ ≤ (∫⁻ t in A, (e t + c) ^ 2 ∂μ) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun t => pow_le_pow_left₀ zero_le (hpt t) 2) h2
    _ ≤ (∫⁻ t in A, e t ^ 2 ∂μ) ^ (2⁻¹ : ℝ) + (∫⁻ _ in A, c ^ 2 ∂μ) ^ (2⁻¹ : ℝ) := hmink
    _ = _ := by
        have he2 : ∀ t, e t ^ 2 = ∫⁻ τ in B, ‖u t - u τ‖ₑ ^ 2 ∂μ := fun t => by
          rw [← ENNReal.rpow_two, ENNReal.rpow_inv_rpow two_ne_zero]
        simp_rw [he2]
        rw [setLIntegral_const, ENNReal.mul_rpow_of_nonneg _ _ h2, ← ENNReal.rpow_two,
          ENNReal.rpow_rpow_inv two_ne_zero, mul_comm c]

/-! ### Weighted layers -/

/-- **Layers by dyadic heights**: for `η : α → ℝ`, `c > 0` and `k ∈ ℕ`,
`∫_{0 < η ≤ c 2^(-k)} g ≤ ∑_{i ≥ 0} ∫_{c 2^(-(k+i+1)) < η ≤ c 2^(-(k+i))} g`, since the intervals
`(c 2^(-(k+i+1)), c 2^(-(k+i))]` cover `(0, c 2^(-k)]` (`Real.iUnion_Ioc_div_two_pow` for
`c 2^(-k)`, Mathlib's `lintegral_iUnion_le`). -/
theorem setLIntegral_preimage_Ioc_le_tsum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (η : α → ℝ) {c : ℝ} (hc : 0 < c) (g : α → ℝ≥0∞) (k : ℕ) :
    ∫⁻ x in η ⁻¹' Ioc 0 (c / 2 ^ k), g x ∂μ ≤
      ∑' i, ∫⁻ x in η ⁻¹' Ioc (c / 2 ^ (k + i + 1)) (c / 2 ^ (k + i)), g x ∂μ := by
  have h : η ⁻¹' Ioc 0 (c / 2 ^ k) =
      ⋃ i, η ⁻¹' Ioc (c / 2 ^ (k + i + 1)) (c / 2 ^ (k + i)) := by
    rw [← Real.iUnion_Ioc_div_two_pow (by positivity : 0 < c / 2 ^ k), preimage_iUnion]
    simp only [div_div, ← pow_add, add_assoc]
  rw [h]
  exact lintegral_iUnion_le _ _

/-- **Weighted layers and the Hardy integral**: for a measurable `η : α → ℝ`, `c > 0`, `s > 0`
and `g : α → [0, ∞]`,
`∑_k 2^(2ks) ∫_{0 < η ≤ c 2^(-k)} g ≤ (1 - 2^(-2s))⁻¹ c^(2s) ∫_{η > 0} g / min(η, 1)^(2s)`.
The layer `k` is the union of the height intervals `A_j = {c 2^(-j-1) < η ≤ c 2^(-j)}`, `j ≥ k`
(`MeasureTheory.setLIntegral_preimage_Ioc_le_tsum`), Hardy's inequality for tails
(`ENNReal.hardy_tail_le` with `q = 1`) moves the weight to the intervals, and on `A_j` the weight
`2^(2js)` is at most `(c/η)^(2s) ≤ c^(2s) min(η, 1)^(-2s)`; the `A_j` are disjoint
(`Real.pairwise_disjoint_Ioc_div_two_pow`, Mathlib's `lintegral_iUnion`). -/
theorem tsum_dyadicWeight_mul_setLIntegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {η : α → ℝ} (hη : Measurable η) {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 < s) (g : α → ℝ≥0∞) :
    ∑' k, dyadicWeight (2 * s) k * ∫⁻ x in η ⁻¹' Ioc 0 (c / 2 ^ k), g x ∂μ ≤
      (1 - (2 : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * ENNReal.ofReal c ^ (2 * s) *
        ∫⁻ x in η ⁻¹' Ioi 0, g x / ENNReal.ofReal (min (η x) 1) ^ (2 * s) ∂μ := by
  set A : ℕ → Set α := fun j => η ⁻¹' Ioc (c / 2 ^ (j + 1)) (c / 2 ^ j)
  have hA : ∀ j, MeasurableSet (A j) := fun j => hη measurableSet_Ioc
  have hdisj : Pairwise (Function.onFun Disjoint A) := fun i j hij =>
    (Real.pairwise_disjoint_Ioc_div_two_pow hc.le hij).preimage η
  set b : ℕ → ℝ≥0∞ := fun j => ∫⁻ x in A j, g x ∂μ
  have h1 : ∑' k, dyadicWeight (2 * s) k * ∫⁻ x in η ⁻¹' Ioc 0 (c / 2 ^ k), g x ∂μ ≤
      (1 - (2 : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * ∑' k, dyadicWeight (2 * s) k * b k := by
    have hH := ENNReal.hardy_tail_le (q := 1) le_rfl (2 * s) b
    rw [ENNReal.lqNorm_one, ENNReal.lqNorm_one] at hH
    exact le_trans (ENNReal.tsum_le_tsum fun k =>
      mul_le_mul' le_rfl (setLIntegral_preimage_Ioc_le_tsum η hc g k)) hH
  have h2 : ∀ j, dyadicWeight (2 * s) j * b j ≤
      ∫⁻ x in A j, ENNReal.ofReal c ^ (2 * s) *
        (g x / ENNReal.ofReal (min (η x) 1) ^ (2 * s)) ∂μ := fun j => by
    rw [← lintegral_const_mul' _ _ (ENNReal.dyadicWeight_ne_top _ _)]
    refine setLIntegral_mono' (hA j) fun x hx => ?_
    have hx0 : 0 < η x := lt_trans (by positivity) hx.1
    have hm : 0 < min (η x) 1 := lt_min hx0 one_pos
    have hpow : dyadicWeight (2 * s) j * ENNReal.ofReal (min (η x) 1) ^ (2 * s) ≤
        ENNReal.ofReal c ^ (2 * s) := by
      rw [mul_comm, ← ENNReal.ofReal_two_pow_mul_rpow hm]
      refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by positivity)
      have := hx.2
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith [min_le_left (η x) 1, pow_pos (two_pos : (0 : ℝ) < 2) j]
    calc dyadicWeight (2 * s) j * g x ≤ ENNReal.ofReal c ^ (2 * s) /
          ENNReal.ofReal (min (η x) 1) ^ (2 * s) * g x := by
          refine mul_le_mul' ((ENNReal.le_div_iff_mul_le ?_ ?_).2 hpow) le_rfl
          · exact Or.inl (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hm) ENNReal.ofReal_ne_top).ne'
          · exact Or.inl (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal c ^ (2 * s) * (g x / ENNReal.ofReal (min (η x) 1) ^ (2 * s)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
  calc _ ≤ _ := h1
    _ ≤ (1 - (2 : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * ∑' j, ∫⁻ x in A j, ENNReal.ofReal c ^ (2 * s) *
          (g x / ENNReal.ofReal (min (η x) 1) ^ (2 * s)) ∂μ :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum h2)
    _ ≤ _ := by
        rw [← lintegral_iUnion hA hdisj, mul_assoc,
          ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity)
            ENNReal.ofReal_ne_top)]
        refine mul_le_mul' le_rfl (lintegral_mono_set (iUnion_subset fun j x hx => ?_))
        exact lt_trans (by positivity) hx.1

end MeasureTheory

namespace ENNReal

/-! ### Telescoping and Hardy's inequality -/

/-- **Telescoping in `[0, ∞]`**: if `m_k ≤ m_{k+1} + b_k` for all `k` and `m_k = 0` for `k ≥ K`,
then `m_k ≤ ∑_{i ≥ 0} b_{k+i}`, since `m_k ≤ m_{k+j} + ∑_{i < j} b_{k+i}` for every `j` by
induction, and `m_{k+K} = 0`. -/
theorem le_tsum_of_le_add_of_eq_zero {m b : ℕ → ℝ≥0∞} (h : ∀ k, m k ≤ m (k + 1) + b k)
    {K : ℕ} (hK : ∀ k, K ≤ k → m k = 0) (k : ℕ) : m k ≤ ∑' i, b (k + i) := by
  have hj : ∀ j, m k ≤ m (k + j) + ∑ i ∈ Finset.range j, b (k + i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc m k ≤ m (k + j) + ∑ i ∈ Finset.range j, b (k + i) := ih
        _ ≤ m (k + j + 1) + b (k + j) + ∑ i ∈ Finset.range j, b (k + i) := by
            gcongr
            exact h _
        _ = m (k + (j + 1)) + ∑ i ∈ Finset.range (j + 1), b (k + i) := by
            rw [Finset.sum_range_succ, ← add_assoc k j 1]
            ring
  calc m k ≤ m (k + K) + ∑ i ∈ Finset.range K, b (k + i) := hj K
    _ = ∑ i ∈ Finset.range K, b (k + i) := by rw [hK _ (Nat.le_add_left K k), zero_add]
    _ ≤ ∑' i, b (k + i) := ENNReal.sum_le_tsum _

/-- **Hardy's inequality for telescoping sequences**: if `m_k ≤ m_{k+1} + b_k` for all `k` and
`m` vanishes from some index on, then for every real `α`
`∑_k (2^(kα) m_k)² ≤ ((1 - 2^(-α))⁻¹)² ∑_k (2^(kα) b_k)²`, the constant being finite for
`α > 0`. By telescoping `m_k ≤ ∑_{i ≥ 0} b_{k+i}` (`ENNReal.le_tsum_of_le_add_of_eq_zero`), and
Hardy's inequality for tails (`ENNReal.hardy_tail_le` with `q = 2`) bounds the weighted tails. -/
theorem tsum_sq_le_of_le_add_of_eq_zero {m b : ℕ → ℝ≥0∞} (h : ∀ k, m k ≤ m (k + 1) + b k)
    {K : ℕ} (hK : ∀ k, K ≤ k → m k = 0) (α : ℝ) :
    ∑' k, (dyadicWeight α k * m k) ^ 2 ≤
      ((1 - (2 : ℝ≥0∞) ^ (-α))⁻¹) ^ 2 * ∑' k, (dyadicWeight α k * b k) ^ 2 := by
  have h1 : lqNorm 2 (fun k => dyadicWeight α k * m k) ≤
      (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * lqNorm 2 (fun k => dyadicWeight α k * b k) :=
    (ENNReal.lqNorm_mono fun k => mul_le_mul' le_rfl (le_tsum_of_le_add_of_eq_zero h hK k)).trans
      (ENNReal.hardy_tail_le one_le_two α b)
  rw [← ENNReal.lqNorm_two_sq, ← ENNReal.lqNorm_two_sq, ← mul_pow]
  exact pow_le_pow_left₀ zero_le h1 2

end ENNReal

namespace Rd

/-! ### Dyadic blocks of `(0, 1]` -/

/-- The **dyadic block** `I_k = (2^(-k-1), 2^(-k)]` of `(0, 1]`, a dyadic interval. -/
def halfLineBlock (k : ℕ) : Set ℝ := Ioc (1 / 2 ^ (k + 1)) (1 / 2 ^ k)

/-- The dyadic blocks are measurable. -/
theorem measurableSet_halfLineBlock (k : ℕ) : MeasurableSet (halfLineBlock k) :=
  measurableSet_Ioc

/-- The dyadic blocks are pairwise disjoint: `Real.pairwise_disjoint_Ioc_div_two_pow` for
`c = 1`. -/
theorem pairwise_disjoint_halfLineBlock : Pairwise (Function.onFun Disjoint halfLineBlock) :=
  Real.pairwise_disjoint_Ioc_div_two_pow zero_le_one

/-- The dyadic blocks lie in `(0, 1]`. -/
theorem halfLineBlock_subset_Ioc (k : ℕ) : halfLineBlock k ⊆ Ioc 0 1 := fun _ ht =>
  ⟨lt_trans (by positivity) ht.1,
    ht.2.trans (by rw [div_le_one (by positivity)]; exact one_le_pow₀ one_le_two)⟩

/-- **The dyadic blocks cover `(0, 1]`**: `Real.iUnion_Ioc_div_two_pow` for `c = 1`. -/
theorem iUnion_halfLineBlock : ⋃ k, halfLineBlock k = Ioc 0 1 :=
  Real.iUnion_Ioc_div_two_pow one_pos

/-- `|I_k| = 2^(-(k+1))`. -/
theorem volume_halfLineBlock (k : ℕ) :
    volume (halfLineBlock k) = dyadicWeight (-1) (k + 1) := by
  rw [halfLineBlock, Real.volume_Ioc, ← ENNReal.ofReal_one_div_two_pow_rpow, Real.rpow_one,
    pow_succ]
  congr 1
  ring

/-! ### The form and the blocks -/

/-- The **Gagliardo form on `(0, 1]`**:
`∫_0^1 ∫_0^1 |u(t) - u(τ)|² / |t - τ|^(1+2s) dτ dt` for `u : ℝ → ℂ`. -/
noncomputable def halfLineForm (s : ℝ) (u : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ τ in Ioc (0 : ℝ) 1, ‖u t - u τ‖ₑ ^ 2 / ‖t - τ‖ₑ ^ (1 + 2 * s)

/-- The constant `K_s = 2^(2s+2) ((1 - 2^(-(s-1/2)))⁻¹)²` of the Hardy inequality on `(0, 1]`,
`Rd.lintegral_div_rpow_le_halfLineForm`. -/
noncomputable def halfLineHardyConst (s : ℝ) : ℝ≥0∞ :=
  2 ^ (2 * s + 2) * ((1 - (2 : ℝ≥0∞) ^ (-(s - 1 / 2)))⁻¹) ^ 2

/-- The constant `K_s` is finite for `s > 1/2`. -/
theorem halfLineHardyConst_ne_top {s : ℝ} (hs : 1 / 2 < s) : halfLineHardyConst s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _)
    (ENNReal.pow_ne_top (ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith)))

/-- **The weighted integral by blocks**: for `s ≥ 0`,
`∫_0^1 |u(t)|² t^(-2s) dt ≤ ∑_k 2^(2s(k+1)) ∫_{I_k} |u|²`, since `t > 2^(-k-1)` on `I_k` and
the `I_k` cover `(0, 1]` (`Rd.iUnion_halfLineBlock`, Mathlib's `lintegral_iUnion_le`). -/
theorem lintegral_Ioc_div_rpow_le_tsum_halfLineBlock {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 / ENNReal.ofReal t ^ (2 * s) ≤
      ∑' k, dyadicWeight (2 * s) (k + 1) * ∫⁻ t in halfLineBlock k, ‖u t‖ₑ ^ 2 := by
  rw [← iUnion_halfLineBlock]
  refine (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum fun k => ?_)
  rw [← lintegral_const_mul' _ _ (ENNReal.dyadicWeight_ne_top _ _)]
  refine setLIntegral_mono' (measurableSet_halfLineBlock k) fun t ht => ?_
  rw [div_eq_mul_inv, mul_comm]
  refine mul_le_mul' ?_ le_rfl
  rw [← inv_inv (dyadicWeight _ (k + 1)), ← ENNReal.dyadicWeight_neg, ENNReal.inv_le_inv]
  calc dyadicWeight (-(2 * s)) (k + 1) = ENNReal.ofReal (1 / 2 ^ (k + 1)) ^ (2 * s) := by
        rw [ENNReal.ofReal_div_two_pow_rpow one_pos, ENNReal.ofReal_one, ENNReal.one_rpow,
          one_mul]
    _ ≤ ENNReal.ofReal t ^ (2 * s) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ht.1.le) (by positivity)

/-- **Neighbouring blocks and the form**: for `s ≥ -1/2`,
`∑_k 2^(k(1+2s)) ∫_{I_k} ∫_{I_{k+1}} |u(t) - u(τ)|² dτ dt ≤ ∫_0^1 ∫_0^1 |u(t) - u(τ)|² /
|t - τ|^(1+2s) dτ dt`. For `t ∈ I_k`, `τ ∈ I_{k+1}`, `0 < t - τ ≤ 2^(-k)`, so the weight is at
most `|t - τ|^(-(1+2s))`; the `I_{k+1}` lie in `(0, 1]` and the `I_k` are disjoint
(`Rd.pairwise_disjoint_halfLineBlock`, Mathlib's `lintegral_iUnion`). -/
theorem tsum_dyadicWeight_mul_lintegral_le_halfLineForm {s : ℝ} (hs : -(1 / 2) ≤ s)
    (u : ℝ → ℂ) :
    ∑' k, dyadicWeight (1 + 2 * s) k * ∫⁻ t in halfLineBlock k,
      ∫⁻ τ in halfLineBlock (k + 1), ‖u t - u τ‖ₑ ^ 2 ≤ halfLineForm s u := by
  have hb : (0 : ℝ) ≤ 1 + 2 * s := by linarith
  have hk : ∀ k, dyadicWeight (1 + 2 * s) k * ∫⁻ t in halfLineBlock k,
      ∫⁻ τ in halfLineBlock (k + 1), ‖u t - u τ‖ₑ ^ 2 ≤ ∫⁻ t in halfLineBlock k,
        ∫⁻ τ in Ioc (0 : ℝ) 1, ‖u t - u τ‖ₑ ^ 2 / ‖t - τ‖ₑ ^ (1 + 2 * s) := fun k => by
    rw [← lintegral_const_mul' _ _ (ENNReal.dyadicWeight_ne_top _ _)]
    refine setLIntegral_mono' (measurableSet_halfLineBlock k) fun t ht => ?_
    rw [← lintegral_const_mul' _ _ (ENNReal.dyadicWeight_ne_top _ _)]
    refine (setLIntegral_mono' (measurableSet_halfLineBlock (k + 1)) fun τ hτ => ?_).trans
      (lintegral_mono_set (halfLineBlock_subset_Ioc (k + 1)))
    have hτt : τ < t := hτ.2.trans_lt ht.1
    have hle : ‖t - τ‖ₑ ^ (1 + 2 * s) ≤ dyadicWeight (-(1 + 2 * s)) k := by
      rw [← ENNReal.ofReal_one_div_two_pow_rpow, ← ENNReal.ofReal_rpow_of_nonneg
        (by positivity) hb, Real.enorm_eq_ofReal_abs, abs_of_pos (sub_pos.2 hτt)]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (by linarith [ht.2, (lt_trans (by positivity) hτ.1 : (0 : ℝ) < τ)])) hb
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul' le_rfl ?_
    rw [← inv_inv (dyadicWeight _ k), ← ENNReal.dyadicWeight_neg, ENNReal.inv_le_inv]
    exact hle
  calc _ ≤ ∑' k, ∫⁻ t in halfLineBlock k,
        ∫⁻ τ in Ioc (0 : ℝ) 1, ‖u t - u τ‖ₑ ^ 2 / ‖t - τ‖ₑ ^ (1 + 2 * s) :=
        ENNReal.tsum_le_tsum hk
    _ = halfLineForm s u := by
        rw [← lintegral_iUnion measurableSet_halfLineBlock pairwise_disjoint_halfLineBlock,
          iUnion_halfLineBlock, halfLineForm]

/-- **One step between neighbouring blocks**: with `a_k = ‖u‖_{L_2(I_k)}` and
`d_k = (∫_{I_k} ∫_{I_{k+1}} |u(t) - u(τ)|²)^(1/2)`,
`2^((k+1)/2) a_k ≤ 2^((k+2)/2) a_{k+1} + 2^((k+2)/2) 2^((k+1)/2) d_k`: the two Minkowski steps
(`MeasureTheory.rpow_mul_lintegral_rpow_le`) for `A = I_k`, `B = I_{k+1}` with
`|I_k| = 2^(-(k+1))` (`Rd.volume_halfLineBlock`), multiplied by `2^((k+2)/2) 2^((k+1)/2)`. -/
theorem dyadicWeight_mul_lintegral_halfLineBlock_le_add {u : ℝ → ℂ} (hu : Measurable u) (k : ℕ) :
    dyadicWeight 2⁻¹ (k + 1) * (∫⁻ t in halfLineBlock k, ‖u t‖ₑ ^ 2) ^ (2⁻¹ : ℝ) ≤
      dyadicWeight 2⁻¹ (k + 1 + 1) *
          (∫⁻ t in halfLineBlock (k + 1), ‖u t‖ₑ ^ 2) ^ (2⁻¹ : ℝ) +
        dyadicWeight 2⁻¹ (k + 1 + 1) * dyadicWeight 2⁻¹ (k + 1) *
          (∫⁻ t in halfLineBlock k, ∫⁻ τ in halfLineBlock (k + 1), ‖u t - u τ‖ₑ ^ 2) ^
            (2⁻¹ : ℝ) := by
  have h := rpow_mul_lintegral_rpow_le (μ := volume) hu (halfLineBlock k)
    (halfLineBlock (k + 1))
  rw [volume_halfLineBlock, volume_halfLineBlock, ENNReal.dyadicWeight_rpow,
    ENNReal.dyadicWeight_rpow, show (-1 : ℝ) * 2⁻¹ = -2⁻¹ by norm_num] at h
  have e1 := ENNReal.dyadicWeight_mul_neg_self (2⁻¹ : ℝ) (k + 1)
  have e2 := ENNReal.dyadicWeight_mul_neg_self (2⁻¹ : ℝ) (k + 1 + 1)
  set a := (∫⁻ t in halfLineBlock k, ‖u t‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  set a' := (∫⁻ t in halfLineBlock (k + 1), ‖u t‖ₑ ^ 2) ^ (2⁻¹ : ℝ)
  set d := (∫⁻ t in halfLineBlock k, ∫⁻ τ in halfLineBlock (k + 1), ‖u t - u τ‖ₑ ^ 2) ^
    (2⁻¹ : ℝ)
  calc dyadicWeight 2⁻¹ (k + 1) * a
      = dyadicWeight 2⁻¹ (k + 1) * (dyadicWeight 2⁻¹ (k + 1 + 1) *
          dyadicWeight (-2⁻¹) (k + 1 + 1)) * a := by rw [e2, mul_one]
    _ = dyadicWeight 2⁻¹ (k + 1 + 1) * dyadicWeight 2⁻¹ (k + 1) *
          (dyadicWeight (-2⁻¹) (k + 1 + 1) * a) := by ring
    _ ≤ dyadicWeight 2⁻¹ (k + 1 + 1) * dyadicWeight 2⁻¹ (k + 1) *
          (d + dyadicWeight (-2⁻¹) (k + 1) * a') := mul_le_mul' le_rfl h
    _ = dyadicWeight 2⁻¹ (k + 1 + 1) * (dyadicWeight 2⁻¹ (k + 1) *
          dyadicWeight (-2⁻¹) (k + 1)) * a' +
          dyadicWeight 2⁻¹ (k + 1 + 1) * dyadicWeight 2⁻¹ (k + 1) * d := by ring
    _ = _ := by rw [e1, mul_one]

/-! ### The Hardy inequality on `(0, 1]` -/

/-- **A fractional Hardy inequality on `(0, 1]`**: for `s > 1/2`, a measurable `u : ℝ → ℂ` and
`ε > 0` with `u = 0` almost everywhere on `(0, ε)`,
`∫_0^1 |u(t)|² / t^(2s) dt ≤ K_s ∫_0^1 ∫_0^1 |u(t) - u(τ)|² / |t - τ|^(1+2s) dτ dt` with
`K_s = 2^(2s+2) (1 - 2^(-(s-1/2)))^(-2)` (`Rd.halfLineHardyConst`), independent of `ε`. With
`m_k = 2^((k+1)/2) ‖u‖_{L_2(I_k)}` and `b_k` the normalised double integrals over `I_k × I_{k+1}`,
`m_k ≤ m_{k+1} + b_k` (`Rd.dyadicWeight_mul_lintegral_halfLineBlock_le_add`) and `m_k = 0` once
`I_k ⊆ (0, ε)`; Hardy's inequality (`ENNReal.tsum_sq_le_of_le_add_of_eq_zero`,
`α = s - 1/2 > 0`) compares the left side (`Rd.lintegral_Ioc_div_rpow_le_tsum_halfLineBlock`) with
the form (`Rd.tsum_dyadicWeight_mul_lintegral_le_halfLineForm`). -/
theorem lintegral_div_rpow_le_halfLineForm {s : ℝ} (hs : 1 / 2 < s) {u : ℝ → ℂ}
    (hu : Measurable u) {ε : ℝ} (hε : 0 < ε) (hu0 : ∀ᵐ t ∂volume, t ∈ Ioo 0 ε → u t = 0) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 / ENNReal.ofReal t ^ (2 * s) ≤
      halfLineHardyConst s * halfLineForm s u := by
  set I : ℕ → ℝ≥0∞ := fun k => ∫⁻ t in halfLineBlock k, ‖u t‖ₑ ^ 2
  set D : ℕ → ℝ≥0∞ := fun k =>
    ∫⁻ t in halfLineBlock k, ∫⁻ τ in halfLineBlock (k + 1), ‖u t - u τ‖ₑ ^ 2
  set m : ℕ → ℝ≥0∞ := fun k => dyadicWeight 2⁻¹ (k + 1) * I k ^ (2⁻¹ : ℝ)
  set b : ℕ → ℝ≥0∞ := fun k =>
    dyadicWeight 2⁻¹ (k + 1 + 1) * dyadicWeight 2⁻¹ (k + 1) * D k ^ (2⁻¹ : ℝ)
  have hsq : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_two, ENNReal.rpow_inv_rpow two_ne_zero]
  have hw : ∀ (c : ℝ) (j : ℕ), dyadicWeight c j ^ 2 = (2 : ℝ≥0∞) ^ ((j : ℝ) * c * 2) := by
    intro c j
    rw [← ENNReal.rpow_two, ENNReal.dyadicWeight_rpow, ENNReal.dyadicWeight, mul_assoc]
  have hadd : ∀ x y : ℝ, (2 : ℝ≥0∞) ^ x * 2 ^ y = 2 ^ (x + y) := fun x y =>
    (ENNReal.rpow_add x y two_ne_zero ENNReal.ofNat_ne_top).symm
  -- `m` vanishes from some index on
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hm0 : ∀ k, K ≤ k → m k = 0 := fun k hk => by
    have hI : I k = 0 := by
      refine (setLIntegral_congr_fun_ae (measurableSet_halfLineBlock k) ?_).trans lintegral_zero
      filter_upwards [hu0] with t ht htk
      have hkK : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ K := pow_le_pow_of_le_one (by norm_num)
        (by norm_num) hk
      rw [ht ⟨lt_trans (by positivity) htk.1, htk.2.trans_lt (by
        rw [← one_div_pow]; exact hkK.trans_lt hK)⟩, enorm_zero, zero_pow two_ne_zero]
    simp only [m, hI, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), mul_zero]
  have hH := ENNReal.tsum_sq_le_of_le_add_of_eq_zero
    (fun k => dyadicWeight_mul_lintegral_halfLineBlock_le_add hu k) hm0 (s - 1 / 2)
  -- the left side by the blocks
  have e1 : ∀ k, dyadicWeight (2 * s) (k + 1) * I k =
      2 ^ (2 * (s - 1 / 2)) * (dyadicWeight (s - 1 / 2) k * m k) ^ 2 := fun k => by
    simp only [m]
    rw [mul_pow, mul_pow, hsq, hw, hw, ← mul_assoc, ← mul_assoc, hadd, hadd,
      ENNReal.dyadicWeight]
    congr 2
    push_cast
    ring
  -- the right side by the form
  have e2 : ∀ k, (dyadicWeight (s - 1 / 2) k * b k) ^ 2 =
      8 * (dyadicWeight (1 + 2 * s) k * D k) := fun k => by
    simp only [b]
    rw [mul_pow, mul_pow, mul_pow, hsq, hw, hw, hw, ← mul_assoc, ← mul_assoc, hadd, hadd,
      ENNReal.dyadicWeight, ← mul_assoc, show (8 : ℝ≥0∞) = 2 ^ (3 : ℝ) by norm_num, hadd]
    congr 2
    push_cast
    ring
  have h5 := tsum_dyadicWeight_mul_lintegral_le_halfLineForm (by linarith : -(1 / 2) ≤ s) u
  calc ∫⁻ t in Ioc (0 : ℝ) 1, ‖u t‖ₑ ^ 2 / ENNReal.ofReal t ^ (2 * s)
      ≤ ∑' k, dyadicWeight (2 * s) (k + 1) * I k :=
        lintegral_Ioc_div_rpow_le_tsum_halfLineBlock (by linarith) u
    _ = 2 ^ (2 * (s - 1 / 2)) * ∑' k, (dyadicWeight (s - 1 / 2) k * m k) ^ 2 := by
        simp_rw [e1]
        exact ENNReal.tsum_mul_left
    _ ≤ 2 ^ (2 * (s - 1 / 2)) * (((1 - (2 : ℝ≥0∞) ^ (-(s - 1 / 2)))⁻¹) ^ 2 *
          (8 * ∑' k, dyadicWeight (1 + 2 * s) k * D k)) := by
        have h8 : ∑' k, (dyadicWeight (s - 1 / 2) k * b k) ^ 2 =
            8 * ∑' k, dyadicWeight (1 + 2 * s) k * D k := by
          simp_rw [e2]
          exact ENNReal.tsum_mul_left
        rw [← h8]
        exact mul_le_mul' le_rfl hH
    _ ≤ 2 ^ (2 * (s - 1 / 2)) * (((1 - (2 : ℝ≥0∞) ^ (-(s - 1 / 2)))⁻¹) ^ 2 *
          (8 * halfLineForm s u)) := by gcongr
    _ = halfLineHardyConst s * halfLineForm s u := by
        rw [halfLineHardyConst, show (8 : ℝ≥0∞) = 2 ^ (3 : ℝ) by norm_num,
          show (2 * s + 2 : ℝ) = 2 * (s - 1 / 2) + 3 by ring, ← hadd]
        ring

end Rd
