/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Lp.MixedNorms
public import FunctionSpaces.Analysis.Lp.Interpolation
public import FunctionSpaces.Analysis.Lp.Inclusion

/-!
# `L_p` for every `0 < p ≤ ∞`

For `0 < p < 1` the quantity `‖f‖_p = (∫ ‖f‖^p)^(1/p)` is a quasi-norm, whose `p`-th power is
subadditive, and Mathlib makes `Lp E p μ` a normed group only for `1 ≤ p`. This file collects
the facts on `L_p` that hold for every exponent, stated for functions through `eLpNorm` on an
arbitrary measure space.

* **The `ρ`-triangle inequality.** With `ρ = min(1, p)`, written `(min 1 p).toReal`, one inequality
  covers every `p ≠ 0`: `‖f + g‖_p^ρ ≤ ‖f‖_p^ρ + ‖g‖_p^ρ`
  (`MeasureTheory.eLpNorm_add_rpow_min_le`). It is Mathlib's triangle inequality for
  `inhmgELpNorm`, which equals `‖f‖_p^ρ` (`MeasureTheory.inhmgELpNorm_eq_eLpNorm_rpow_min`). The
  exponent `ρ` lies in `(0, 1]`, is `p` for `p ≤ 1` and `1` for `p ≥ 1`, also at `p = ∞`
  (`ENNReal.toReal_min_one_pos`, `ENNReal.toReal_min_one_le_one`,
  `ENNReal.toReal_min_one_of_le_one`, `ENNReal.toReal_min_one_of_one_le`).
* **The quasi-norm of `Lp`.** `‖0‖ₑ = 0` and `‖-f‖ₑ = ‖f‖ₑ` on `Lp E p μ` for every `p`
  (`MeasureTheory.Lp.enorm_zero`, `MeasureTheory.Lp.enorm_neg`), `‖f + g‖ₑ^p ≤ ‖f‖ₑ^p + ‖g‖ₑ^p`
  for `p ≤ 1` (`MeasureTheory.Lp.enorm_add_rpow_le_of_le_one`), and two approximants of one
  element are close (`MeasureTheory.Lp.enorm_sub_rpow_le_two_mul`).
* **Limits in measure.** If `u_n → g` in measure, then
  `‖g - u_k‖_r^ρ ≤ ∑_{i ≥ 0} ‖u_{k+i+1} - u_{k+i}‖_r^ρ` with `ρ = min(1, r)`, for every
  `0 < r ≤ ∞` (`MeasureTheory.eLpNorm_sub_rpow_min_le_tsum`; for `1 ≤ r` the triangle inequality
  of a series, `MeasureTheory.eLpNorm_sub_le_tsum`). Fatou's lemma along an almost everywhere
  convergent subsequence identifies the limit.
* **Series.** `‖∑_i g_i‖_p^ρ ≤ ∑_i ‖g_i‖_p^ρ` for countably many `g_i : α → [0, ∞]`
  (`MeasureTheory.eLpNorm_tsum_rpow_le_of_le_one`, `MeasureTheory.eLpNorm_tsum_rpow_min_le`); a
  function with finite `L_p` quasi-norm is finite almost everywhere
  (`MeasureTheory.ae_lt_top_of_eLpNorm_ne_top`); and `∑_i ‖g_i‖_p^ρ < ∞` makes `∑_i |g_i(x)|`
  finite for almost every `x` (`MeasureTheory.summable_norm_of_tsum_eLpNorm_rpow_min_ne_top`).
* **The sup-norm bootstrap.** A bound `N ≤ M ‖f‖_{p₀}` of an almost everywhere bound `N` of `|f|`
  gives `N ≤ M^(p₀/p) ‖f‖_p` for every `0 < p ≤ p₀`
  (`MeasureTheory.le_rpow_mul_eLpNorm_of_ae_enorm_le`), and `‖f‖_∞ ≤ M ‖f‖_p` gives
  `‖f‖_r ≤ M^(1 - p/r) ‖f‖_p` for every `p ≤ r ≤ ∞` (`MeasureTheory.eLpNorm_le_of_eLpNorm_top_le`)
  (Z. Ditzian, A. Prymak, *On Nikol'skii inequalities for domains in `ℝ^d`*, Constr. Approx. 44
  (2016), Theorem 2.1). So a Nikolskii inequality at one exponent gives it at every smaller one.
* **The first moment method.** Some value `F(y)` approximates `F` on a set at least as well as
  the mean of all values (`MeasureTheory.exists_setLIntegral_enorm_sub_rpow_le`).

On `[0, 1]` with Lebesgue measure and for `p < 1`, the only continuous linear functional on
`L_p` is `0` (M. M. Day, *The spaces `L^p` with `0 < p < 1`*, Bull. Amer. Math. Soc. 46 (1940)),
so `L_p` has no bounded linear projections onto nonzero finite-dimensional subspaces; near-best
approximants take their place in the files that use this one.
-/

@[expose] public section

open Filter
open scoped ENNReal

/-! ### The exponent `ρ = min(1, p)` -/

namespace ENNReal

/-- The exponent `ρ = min(1, p)` is positive for `p ≠ 0`, also at `p = ∞`, where `ρ = 1`. -/
theorem toReal_min_one_pos {p : ℝ≥0∞} (hp0 : p ≠ 0) : 0 < (min 1 p).toReal :=
  ENNReal.toReal_pos (lt_min zero_lt_one (pos_iff_ne_zero.2 hp0)).ne'
    (ne_top_of_le_ne_top one_ne_top (min_le_left 1 p))

/-- The exponent `ρ = min(1, p)` is at most `1`. -/
theorem toReal_min_one_le_one (p : ℝ≥0∞) : (min 1 p).toReal ≤ 1 :=
  (ENNReal.toReal_mono one_ne_top (min_le_left 1 p)).trans_eq toReal_one

/-- For `p ≤ 1` the exponent `ρ = min(1, p)` is `p`. -/
theorem toReal_min_one_of_le_one {p : ℝ≥0∞} (hp1 : p ≤ 1) : (min 1 p).toReal = p.toReal := by
  rw [min_eq_right hp1]

/-- For `p ≥ 1`, including `p = ∞`, the exponent `ρ = min(1, p)` is `1`. -/
theorem toReal_min_one_of_one_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) : (min 1 p).toReal = 1 := by
  rw [min_eq_left hp1, toReal_one]

end ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p r : ℝ≥0∞}

/-! ### The `ρ`-triangle inequality -/

/-- **Mathlib's inhomogeneous `L_p` quasi-norm is the `ρ`-th power of the `L_p` quasi-norm**:
`inhmgELpNorm f p μ = ‖f‖_p^ρ` with `ρ = min(1, p)`, for every `p ≠ 0` and every function with
values in an additive monoid with an extended seminorm. For `p ≤ 1` this is Mathlib's
`inhmgELpNorm_eq_eLpNorm_pow`, for `p ≥ 1` Mathlib's `inhmgELpNorm_eq_eLpNorm`; at `p = 0`
Mathlib's value is the measure of the support of an almost everywhere strongly measurable `f`. -/
theorem inhmgELpNorm_eq_eLpNorm_rpow_min {ε : Type*} [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] (hp0 : p ≠ 0) (f : α → ε) :
    inhmgELpNorm f p μ = eLpNorm f p μ ^ (min 1 p).toReal := by
  rcases le_total p 1 with hp1 | hp1
  · rw [ENNReal.toReal_min_one_of_le_one hp1, inhmgELpNorm_eq_eLpNorm_pow hp1 hp0]
  · rw [ENNReal.toReal_min_one_of_one_le hp1, ENNReal.rpow_one, inhmgELpNorm_eq_eLpNorm hp1]

/-- **The `ρ`-triangle inequality of `L_p` for every `0 < p ≤ ∞`**: with `ρ = min(1, p)`,
`‖f + g‖_p^ρ ≤ ‖f‖_p^ρ + ‖g‖_p^ρ` on any measure space, for all functions with values in an
additive monoid with an extended seminorm and continuous addition, such as a normed group or
`[0, ∞]`. For `p ≤ 1` this is `MeasureTheory.eLpNorm_add_rpow_le_of_le_one`, for `p ≥ 1` the
triangle inequality `eLpNorm_add_le`. Both are Mathlib's triangle inequality
`inhmgELpNorm_add_le`, since `inhmgELpNorm f p μ = ‖f‖_p^ρ` for `p ≠ 0`
(`MeasureTheory.inhmgELpNorm_eq_eLpNorm_rpow_min`). -/
theorem eLpNorm_add_rpow_min_le {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    [ContinuousAdd ε] (hp0 : p ≠ 0) (f g : α → ε) :
    eLpNorm (f + g) p μ ^ (min 1 p).toReal ≤
      eLpNorm f p μ ^ (min 1 p).toReal + eLpNorm g p μ ^ (min 1 p).toReal := by
  rw [← inhmgELpNorm_eq_eLpNorm_rpow_min hp0, ← inhmgELpNorm_eq_eLpNorm_rpow_min hp0,
    ← inhmgELpNorm_eq_eLpNorm_rpow_min hp0]
  exact inhmgELpNorm_add_le

/-! ### The quasi-norm of `Lp` -/

/-- The quasi-norm of `L_p(μ)` vanishes at `0`, for every `p`. -/
protected theorem Lp.enorm_zero {E : Type*} [NormedAddCommGroup E] :
    ‖(0 : Lp E p μ)‖ₑ = 0 := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (Lp.coeFn_zero E p μ), eLpNorm_zero]

/-- The quasi-norm of `L_p(μ)` is even, `‖-f‖_p = ‖f‖_p`, for every `p`. -/
protected theorem Lp.enorm_neg {E : Type*} [NormedAddCommGroup E] (f : Lp E p μ) :
    ‖-f‖ₑ = ‖f‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (Lp.coeFn_neg f), eLpNorm_neg]

/-- **The `p`-th power of the quasi-norm of `L_p` is subadditive for `p ≤ 1`**:
`‖f + g‖_p^p ≤ ‖f‖_p^p + ‖g‖_p^p` for `f, g ∈ L_p(μ)`, from the same inequality for functions
(`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`). At `p = 0` both sides are powers `x^0 = 1`. -/
theorem Lp.enorm_add_rpow_le_of_le_one {E : Type*} [NormedAddCommGroup E] (hp1 : p ≤ 1)
    (f g : Lp E p μ) :
    ‖f + g‖ₑ ^ p.toReal ≤ ‖f‖ₑ ^ p.toReal + ‖g‖ₑ ^ p.toReal := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [ENNReal.toReal_zero, ENNReal.rpow_zero]
    exact le_self_add
  rw [Lp.enorm_def, Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (Lp.coeFn_add f g)]
  exact eLpNorm_add_rpow_le_of_le_one hp0 hp1 _ _

/-- **Two approximants of one element are close**, `p ≤ 1`: if `‖f - g‖_p ≤ e` and
`‖f - h‖_p ≤ e` in `L_p(μ)`, then `‖g - h‖_p^p ≤ 2 e^p`, since `g - h = (f - h) - (f - g)`
(`MeasureTheory.Lp.enorm_add_rpow_le_of_le_one`, `MeasureTheory.Lp.enorm_neg`). -/
theorem Lp.enorm_sub_rpow_le_two_mul {E : Type*} [NormedAddCommGroup E] (hp1 : p ≤ 1)
    {f g h : Lp E p μ} {e : ℝ≥0∞} (hg : ‖f - g‖ₑ ≤ e) (hh : ‖f - h‖ₑ ≤ e) :
    ‖g - h‖ₑ ^ p.toReal ≤ 2 * e ^ p.toReal :=
  calc ‖g - h‖ₑ ^ p.toReal = ‖(f - h) + -(f - g)‖ₑ ^ p.toReal := by
        rw [show (f - h) + -(f - g) = g - h by abel]
    _ ≤ ‖f - h‖ₑ ^ p.toReal + ‖-(f - g)‖ₑ ^ p.toReal := Lp.enorm_add_rpow_le_of_le_one hp1 _ _
    _ ≤ e ^ p.toReal + e ^ p.toReal := by
        rw [Lp.enorm_neg]
        exact add_le_add (ENNReal.rpow_le_rpow hh ENNReal.toReal_nonneg)
          (ENNReal.rpow_le_rpow hg ENNReal.toReal_nonneg)
    _ = 2 * e ^ p.toReal := (two_mul _).symm

/-! ### Fatou's lemma for telescoping sums in every `L_r` -/

/-- **Telescoping in `L_r`, `0 < r ≤ ∞`**: with `ρ = min(1, r)`,
`‖u_{k+n} - u_k‖_r^ρ ≤ ∑_{i<n} ‖u_{k+i+1} - u_{k+i}‖_r^ρ` for functions with values in a
seminormed group, by the `ρ`-triangle inequality (`MeasureTheory.eLpNorm_add_rpow_min_le`). -/
theorem eLpNorm_sub_rpow_min_le_sum {E : Type*} [SeminormedAddCommGroup E] (hr0 : r ≠ 0)
    (u : ℕ → α → E) (k n : ℕ) :
    eLpNorm (u (k + n) - u k) r μ ^ (min 1 r).toReal ≤
      ∑ i ∈ Finset.range n, eLpNorm (u (k + i + 1) - u (k + i)) r μ ^ (min 1 r).toReal := by
  have hρ : 0 < (min 1 r).toReal := ENNReal.toReal_min_one_pos hr0
  induction n with
  | zero => simp [ENNReal.zero_rpow_of_pos hρ]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc eLpNorm (u (k + (n + 1)) - u k) r μ ^ (min 1 r).toReal
        = eLpNorm ((u (k + n + 1) - u (k + n)) + (u (k + n) - u k)) r μ ^ (min 1 r).toReal := by
          rw [sub_add_sub_cancel]; rfl
      _ ≤ eLpNorm (u (k + n + 1) - u (k + n)) r μ ^ (min 1 r).toReal +
            eLpNorm (u (k + n) - u k) r μ ^ (min 1 r).toReal := eLpNorm_add_rpow_min_le hr0 _ _
      _ ≤ _ := by rw [add_comm]; gcongr

/-- **Fatou's lemma for telescoping sums in `L_r`, `0 < r ≤ ∞`**: if `u_n → g` in measure, with
almost everywhere strongly measurable `u_n`, then, with `ρ = min(1, r)`,
`‖g - u_k‖_r^ρ ≤ ∑_{i ≥ 0} ‖u_{k+i+1} - u_{k+i}‖_r^ρ`. The finite telescoping sums bound
`‖u_{k+n} - u_k‖_r^ρ` (`MeasureTheory.eLpNorm_sub_rpow_min_le_sum`), and Mathlib's
`eLpNorm_le_of_tendstoInMeasure`, valid for every exponent, passes the bound to the limit. For
`r ≤ 1` this is `MeasureTheory.eLpNorm_sub_rpow_le_tsum`. -/
theorem eLpNorm_sub_rpow_min_le_tsum {E : Type*} [SeminormedAddCommGroup E] (hr0 : r ≠ 0)
    {u : ℕ → α → E} {g : α → E} (hu : TendstoInMeasure μ u atTop g)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (k : ℕ) :
    eLpNorm (g - u k) r μ ^ (min 1 r).toReal ≤
      ∑' i, eLpNorm (u (k + i + 1) - u (k + i)) r μ ^ (min 1 r).toReal := by
  have hρ : 0 < (min 1 r).toReal := ENNReal.toReal_min_one_pos hr0
  set S := ∑' i, eLpNorm (u (k + i + 1) - u (k + i)) r μ ^ (min 1 r).toReal
  have hk : Tendsto (fun n => k + n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_left n k) tendsto_id
  have hlim : TendstoInMeasure μ (fun n => u (k + n) - u k) atTop (g - u k) :=
    (hu.comp hk).sub_right (u k)
  have hbound : ∀ n, eLpNorm (u (k + n) - u k) r μ ≤ S ^ (min 1 r).toReal⁻¹ := fun n =>
    (ENNReal.le_rpow_inv_iff hρ).2 ((eLpNorm_sub_rpow_min_le_sum hr0 u k n).trans
      (ENNReal.sum_le_tsum _))
  have h := eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hbound) hlim
    fun n => (hum _).sub (hum k)
  exact (ENNReal.le_rpow_inv_iff hρ).1 h

/-- **The triangle inequality for limits in measure, `1 ≤ r ≤ ∞`**: if `u_n → g` in measure, with
almost everywhere strongly measurable `u_n`, then
`‖g - u_k‖_r ≤ ∑_{i ≥ 0} ‖u_{k+i+1} - u_{k+i}‖_r`, for every limit in measure `g`, of finite or
infinite quasi-norm. This is the case `ρ = 1` of `MeasureTheory.eLpNorm_sub_rpow_min_le_tsum`. -/
theorem eLpNorm_sub_le_tsum {E : Type*} [SeminormedAddCommGroup E] (hr1 : 1 ≤ r)
    {u : ℕ → α → E} {g : α → E} (hu : TendstoInMeasure μ u atTop g)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (k : ℕ) :
    eLpNorm (g - u k) r μ ≤ ∑' i, eLpNorm (u (k + i + 1) - u (k + i)) r μ := by
  have h := eLpNorm_sub_rpow_min_le_tsum (zero_lt_one.trans_le hr1).ne' hu hum k
  simpa only [ENNReal.toReal_min_one_of_one_le hr1, ENNReal.rpow_one] using h

/-! ### Series in `L_p` -/

/-- **Series in `L_p`, `0 < p ≤ 1`**: `‖∑_i g_i‖_p^p ≤ ∑_i ‖g_i‖_p^p` for countably many
`g_i : α → [0, ∞]` on any measure space. Pointwise `(∑_i g_i)^p ≤ ∑_i g_i^p`
(`ENNReal.rpow_tsum_le_tsum_rpow`), and the integral of a series of measurable functions is the
series of the integrals (Mathlib's `lintegral_tsum`). If some `g_i` is not measurable, then
`‖g_i‖_p = ∞` and so is the right side. -/
theorem eLpNorm_tsum_rpow_le_of_le_one {ι : Type*} [Countable ι] {g : ι → α → ℝ≥0∞}
    (hp0 : p ≠ 0) (hp1 : p ≤ 1) :
    eLpNorm (fun x => ∑' i, g i x) p μ ^ p.toReal ≤ ∑' i, eLpNorm (g i) p μ ^ p.toReal := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  by_cases hg : ∀ i, AEMeasurable (g i) μ
  swap
  · obtain ⟨i, hi⟩ := not_forall.1 hg
    have h : eLpNorm (g i) p μ ^ p.toReal = ∞ := by
      rw [eLpNorm_of_not_aestronglyMeasurable fun h => hi h.aemeasurable,
        ENNReal.top_rpow_of_pos hρ]
    rw [ENNReal.tsum_eq_top_of_eq_top ⟨i, h⟩]
    exact le_top
  have hρ1 : p.toReal ≤ 1 := by
    simpa only [ENNReal.toReal_min_one_of_le_one hp1] using ENNReal.toReal_min_one_le_one p
  rw [eLpNorm_rpow_eq_lintegral hp0 hp (AEMeasurable.tsum hg)]
  calc ∫⁻ x, (∑' i, g i x) ^ p.toReal ∂μ ≤ ∫⁻ x, ∑' i, g i x ^ p.toReal ∂μ :=
        lintegral_mono fun x => ENNReal.rpow_tsum_le_tsum_rpow _ hρ hρ1
    _ = ∑' i, ∫⁻ x, g i x ^ p.toReal ∂μ := lintegral_tsum fun i => (hg i).pow_const _
    _ = ∑' i, eLpNorm (g i) p μ ^ p.toReal := by
        congr 1
        funext i
        rw [eLpNorm_rpow_eq_lintegral hp0 hp (hg i)]

/-- **Series in `L_p`, `0 < p ≤ ∞`**: with `ρ = min(1, p)`, `‖∑_i g_i‖_p^ρ ≤ ∑_i ‖g_i‖_p^ρ` for
countably many `g_i : α → [0, ∞]` on any measure space: for `p ≤ 1`
`MeasureTheory.eLpNorm_tsum_rpow_le_of_le_one`, for `p ≥ 1` Minkowski's inequality for series
`MeasureTheory.eLpNorm_tsum_le`. -/
theorem eLpNorm_tsum_rpow_min_le {ι : Type*} [Countable ι] {g : ι → α → ℝ≥0∞} (hp0 : p ≠ 0) :
    eLpNorm (fun x => ∑' i, g i x) p μ ^ (min 1 p).toReal ≤
      ∑' i, eLpNorm (g i) p μ ^ (min 1 p).toReal := by
  rcases le_total p 1 with hp1 | hp1
  · rw [ENNReal.toReal_min_one_of_le_one hp1]
    exact eLpNorm_tsum_rpow_le_of_le_one hp0 hp1
  · simp only [ENNReal.toReal_min_one_of_one_le hp1, ENNReal.rpow_one]
    exact eLpNorm_tsum_le hp1

/-- **A function with finite `L_p` quasi-norm is finite almost everywhere**, for every
`0 < p ≤ ∞` and every `F : α → [0, ∞]`: for `p < ∞` the integral of `F^p` is finite (Mathlib's
`ae_lt_top'`), for `p = ∞` the essential supremum bounds `F` (Mathlib's `ae_le_eLpNormEssSup`). A
function that is not almost everywhere measurable has infinite quasi-norm. -/
theorem ae_lt_top_of_eLpNorm_ne_top {F : α → ℝ≥0∞} (hp0 : p ≠ 0) (h : eLpNorm F p μ ≠ ∞) :
    ∀ᵐ x ∂μ, F x < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · filter_upwards [ae_le_eLpNormEssSup (f := F) (μ := μ)] with x hx
    rw [enorm_eq_self] at hx
    exact (hx.trans eLpNormEssSup_le_eLpNorm_top).trans_lt h.lt_top
  have hF : AEMeasurable F μ := by
    by_contra hF
    exact h (eLpNorm_of_not_aestronglyMeasurable fun h' => hF h'.aemeasurable)
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hint : ∫⁻ x, F x ^ p.toReal ∂μ ≠ ∞ := by
    rw [← eLpNorm_rpow_eq_lintegral hp0 hp hF]
    exact ENNReal.rpow_ne_top_of_nonneg hρ.le h
  filter_upwards [ae_lt_top' (hF.pow_const _) hint] with x hx
  exact lt_top_iff_ne_top.2 ((ENNReal.rpow_eq_top_iff_of_pos hρ).not.1 hx.ne)

/-- **Series with summable `ρ`-th powers of quasi-norms converge absolutely almost everywhere**:
for `0 < p ≤ ∞`, `ρ = min(1, p)` and countably many functions `g_i` with values in a normed group,
`∑_i ‖g_i‖_p^ρ < ∞` gives `∑_i |g_i(x)| < ∞` for almost every `x`. For `p ≥ 1` this is Mathlib's
`summable_norm_of_tsum_eLpNorm_ne_top`; for every `p` the series `∑_i |g_i|` has finite `L_p`
quasi-norm (`MeasureTheory.eLpNorm_tsum_rpow_min_le`), so it is finite almost everywhere
(`MeasureTheory.ae_lt_top_of_eLpNorm_ne_top`). -/
theorem summable_norm_of_tsum_eLpNorm_rpow_min_ne_top {ι : Type*} [Countable ι] {E : Type*}
    [NormedAddCommGroup E] {g : ι → α → E} (hp0 : p ≠ 0)
    (h : ∑' i, eLpNorm (g i) p μ ^ (min 1 p).toReal ≠ ∞) :
    ∀ᵐ x ∂μ, Summable fun i => ‖g i x‖ := by
  have hρ : 0 < (min 1 p).toReal := ENNReal.toReal_min_one_pos hp0
  have hg : ∀ i, AEStronglyMeasurable (g i) μ := fun i => by
    by_contra hgi
    refine h (ENNReal.tsum_eq_top_of_eq_top ⟨i, ?_⟩)
    rw [eLpNorm_of_not_aestronglyMeasurable hgi, ENNReal.top_rpow_of_pos hρ]
  have he : ∀ i, eLpNorm (fun x => ‖g i x‖ₑ) p μ = eLpNorm (g i) p μ := fun i =>
    eLpNorm_enorm _ (hg i)
  have h1 := eLpNorm_tsum_rpow_min_le (μ := μ) (g := fun i x => ‖g i x‖ₑ) hp0
  simp only [he] at h1
  have hS : eLpNorm (fun x => ∑' i, ‖g i x‖ₑ) p μ ≠ ∞ :=
    (ENNReal.rpow_eq_top_iff_of_pos hρ).not.1 (ne_top_of_le_ne_top h h1)
  filter_upwards [ae_lt_top_of_eLpNorm_ne_top hp0 hS] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.1 hx.ne

/-! ### The sup-norm bootstrap -/

/-- **A bound of the supremum by one `L_{p₀}` quasi-norm gives it by every smaller one**
(Ditzian–Prymak 2016, Theorem 2.1, (2.2)): let `N < ∞` bound `|f|` almost everywhere, for example
the essential supremum of `f` or the supremum norm of a bounded continuous `f`. If
`N ≤ M ‖f‖_{p₀}` with `p₀ < ∞`, then `N ≤ M^(p₀/p) ‖f‖_p` for every `0 < p ≤ p₀`. By
interpolation, `‖f‖_{p₀} ≤ N^(1-θ) ‖f‖_p^θ` with `θ = p/p₀`
(`MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow`); cancelling `N^(1-θ)` leaves
`N^θ ≤ M ‖f‖_p^θ`, and the `1/θ`-th power gives the claim. A function that is not almost
everywhere strongly measurable has `‖f‖_q = ∞` for every `q`, so the claim holds for it too. -/
theorem le_rpow_mul_eLpNorm_of_ae_enorm_le {E : Type*} [NormedAddCommGroup E] {f : α → E}
    {N M p₀ : ℝ≥0∞} (hN : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ N) (hNtop : N ≠ ∞) (hp0 : p ≠ 0) (hpp₀ : p ≤ p₀)
    (hp₀ : p₀ ≠ ∞) (h : N ≤ M * eLpNorm f p₀ μ) :
    N ≤ M ^ (p₀.toReal / p.toReal) * eLpNorm f p μ := by
  rcases eq_or_ne N 0 with rfl | hN0
  · exact zero_le
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top hp₀ hpp₀)
  have hp₀r : 0 < p₀.toReal := hpr.trans_le (ENNReal.toReal_mono hp₀ hpp₀)
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · have hM : M ≠ 0 := by
      rintro rfl
      exact hN0 (le_zero_iff.1 (h.trans_eq (zero_mul _)))
    rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hM) (by positivity)).ne']
    exact le_top
  have hθ0 : 0 < p.toReal / p₀.toReal := div_pos hpr hp₀r
  have h1θ : 0 ≤ 1 - p.toReal / p₀.toReal := ENNReal.one_sub_toReal_div_nonneg hpp₀
  have hint := eLpNorm_le_rpow_mul_eLpNorm_rpow hf hN hp0 hpp₀ hp₀
  set θ := p.toReal / p₀.toReal with hθ
  have hc0 : N ^ (1 - θ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hN0) hNtop).ne'
  have hctop : N ^ (1 - θ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg h1θ hNtop
  have hkey : N ^ θ ≤ M * eLpNorm f p μ ^ θ := by
    refine (ENNReal.mul_le_mul_iff_right hc0 hctop).1 ?_
    rw [← ENNReal.rpow_add_of_nonneg _ _ h1θ hθ0.le, sub_add_cancel, ENNReal.rpow_one]
    calc N ≤ M * eLpNorm f p₀ μ := h
      _ ≤ M * (N ^ (1 - θ) * eLpNorm f p μ ^ θ) := by gcongr
      _ = N ^ (1 - θ) * (M * eLpNorm f p μ ^ θ) := by ring
  calc N = (N ^ θ) ^ θ⁻¹ := (ENNReal.rpow_rpow_inv hθ0.ne' N).symm
    _ ≤ (M * eLpNorm f p μ ^ θ) ^ θ⁻¹ := ENNReal.rpow_le_rpow hkey (inv_nonneg.2 hθ0.le)
    _ = M ^ (p₀.toReal / p.toReal) * eLpNorm f p μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hθ0.le), ← ENNReal.rpow_mul,
          mul_inv_cancel₀ hθ0.ne', ENNReal.rpow_one, hθ, inv_div]

/-- **A bound of `‖f‖_∞` by `‖f‖_p` gives a bound of every `‖f‖_r`, `p ≤ r ≤ ∞`, by `‖f‖_p`**
(Ditzian–Prymak 2016, Theorem 2.1, (2.3) with `q = p`): if `‖f‖_∞ ≤ M ‖f‖_p` with `p ≠ 0`, then
`‖f‖_r ≤ M^(1 - p/r) ‖f‖_p` for every `p ≤ r ≤ ∞`. For `r = ∞` this is the hypothesis; for
`r < ∞` interpolation gives `‖f‖_r ≤ ‖f‖_∞^(1-θ) ‖f‖_p^θ` with `θ = p/r`
(`MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow`), and
`(M ‖f‖_p)^(1-θ) ‖f‖_p^θ = M^(1-θ) ‖f‖_p`. A function that is not almost everywhere strongly
measurable has `‖f‖_q = ∞` for every `q`, so the hypothesis forces `M ≠ 0` and the right side is
`∞`. -/
theorem eLpNorm_le_of_eLpNorm_top_le {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hp0 : p ≠ 0) (hpr : p ≤ r) {M : ℝ≥0∞} (h : eLpNorm f ∞ μ ≤ M * eLpNorm f p μ) :
    eLpNorm f r μ ≤ M ^ (1 - p.toReal / r.toReal) * eLpNorm f p μ := by
  rcases eq_or_ne r ∞ with rfl | hr
  · simpa using h
  have hθ : 0 ≤ p.toReal / r.toReal := by positivity
  have h1θ : 0 ≤ 1 - p.toReal / r.toReal := ENNReal.one_sub_toReal_div_nonneg hpr
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · have hM : M ≠ 0 := by
      rintro rfl
      rw [zero_mul, eLpNorm_of_not_aestronglyMeasurable hf] at h
      exact ENNReal.top_ne_zero (le_zero_iff.1 h)
    simp only [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hM) h1θ).ne', le_refl]
  have hN : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ eLpNorm f ∞ μ := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
    exact hx.trans eLpNormEssSup_le_eLpNorm_top
  calc eLpNorm f r μ
      ≤ eLpNorm f ∞ μ ^ (1 - p.toReal / r.toReal) * eLpNorm f p μ ^ (p.toReal / r.toReal) :=
        eLpNorm_le_rpow_mul_eLpNorm_rpow hf hN hp0 hpr hr
    _ ≤ (M * eLpNorm f p μ) ^ (1 - p.toReal / r.toReal) *
          eLpNorm f p μ ^ (p.toReal / r.toReal) := by gcongr
    _ = M ^ (1 - p.toReal / r.toReal) * eLpNorm f p μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ, mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ h1θ hθ, sub_add_cancel, ENNReal.rpow_one]

/-! ### The first moment method -/

/-- **A value of `F` approximates `F` on `s` at least as well as the mean of all values** (the
first moment method, Mathlib's `exists_le_setLAverage`): for measurable `F`, a set `s` of finite
positive measure and every exponent `r`, some `y ∈ s` has
`∫_s |F(x) - F(y)|^r dx ≤ μ(s)⁻¹ ∫_s ∫_s |F(x) - F(z)|^r dx dz`. -/
theorem exists_setLIntegral_enorm_sub_rpow_le [SFinite μ] {F : α → ℂ} (hF : Measurable F)
    {s : Set α} (hμ0 : μ s ≠ 0) (hμ : μ s ≠ ∞) (r : ℝ) :
    ∃ y ∈ s, ∫⁻ x in s, ‖F x - F y‖ₑ ^ r ∂μ ≤
      (μ s)⁻¹ * ∫⁻ y in s, ∫⁻ x in s, ‖F x - F y‖ₑ ^ r ∂μ ∂μ := by
  have hG : Measurable fun y => ∫⁻ x in s, ‖F x - F y‖ₑ ^ r ∂μ :=
    Measurable.lintegral_prod_left' (f := fun z : α × α => ‖F z.1 - F z.2‖ₑ ^ r)
      (((hF.comp measurable_fst).sub (hF.comp measurable_snd)).enorm.pow_const r)
  obtain ⟨y, hy, hle⟩ := exists_le_setLAverage hμ0 hμ hG.aemeasurable
  exact ⟨y, hy, hle.trans_eq (by rw [setLAverage_eq, ENNReal.div_eq_inv_mul])⟩

end MeasureTheory
