/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Interpolation between `L_p` and `L_∞`

For a function bounded by `M` and `0 < p ≤ r < ∞`,

`‖f‖_r ≤ M^(1 - p/r) ‖f‖_p^(p/r)`

(`eLpNorm_le_rpow_mul_eLpNorm_rpow`), because `|f|^r ≤ M^(r-p) |f|^p` pointwise.  This is the
elementary case of log-convexity of `p ↦ ‖f‖_p`; Mathlib has Hölder's inequality but not this
form.  It reduces every Nikolskii inequality `‖a‖_r ≲ n^(D(1/p-1/r)) ‖a‖_p` to the case
`r = ∞`.  The real-valued form `toReal_eLpNorm_le_rpow_mul` is the one used in estimates.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p r : ℝ≥0∞} {f : α → E}

/-- **Interpolation between `L_p` and `L_∞`**: for `‖f‖ ≤ M` a.e. and `0 < p ≤ r < ∞`,
`‖f‖_r ≤ M^(1 - p/r) ‖f‖_p^(p/r)`. -/
theorem eLpNorm_le_rpow_mul_eLpNorm_rpow (hf : AEStronglyMeasurable f μ) {M : ℝ≥0∞}
    (hM : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M) (hp0 : p ≠ 0) (hpr : p ≤ r) (hr : r ≠ ∞) :
    eLpNorm f r μ ≤ M ^ (1 - p.toReal / r.toReal) * eLpNorm f p μ ^ (p.toReal / r.toReal) := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  have hr0 : r ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hp0) hpr).ne'
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr0 hr
  have hpr' : p.toReal ≤ r.toReal := ENNReal.toReal_mono hr hpr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf]
  have hpt : ∀ᵐ x ∂μ, ‖f x‖ₑ ^ r.toReal ≤ M ^ (r.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
    filter_upwards [hM] with x hx
    rw [← sub_add_cancel r.toReal p.toReal,
      ENNReal.rpow_add_of_nonneg _ _ (by linarith) hpp.le, sub_add_cancel]
    gcongr
  calc (∫⁻ x, ‖f x‖ₑ ^ r.toReal ∂μ) ^ (1 / r.toReal)
      ≤ (∫⁻ x, M ^ (r.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / r.toReal) := by
        gcongr ?_ ^ _
        exact lintegral_mono_ae hpt
    _ = (M ^ (r.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / r.toReal) := by
        rw [lintegral_const_mul'' _ (hf.enorm.pow_const _)]
    _ = M ^ (1 - p.toReal / r.toReal) *
          ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) ^ (p.toReal / r.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        congr 2 <;> field_simp

/-- The interpolation inequality in real numbers, for a bounded function on a finite measure
space: `‖f‖_r ≤ M^(1 - p/r) ‖f‖_p^(p/r)` for `0 < p ≤ r < ∞`. -/
theorem toReal_eLpNorm_le_rpow_mul [IsFiniteMeasure μ] (hf : AEStronglyMeasurable f μ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) (hp0 : p ≠ 0) (hpr : p ≤ r) (hr : r ≠ ∞) :
    (eLpNorm f r μ).toReal ≤
      M ^ (1 - p.toReal / r.toReal) * (eLpNorm f p μ).toReal ^ (p.toReal / r.toReal) := by
  have hM' : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ENNReal.ofReal M := by
    filter_upwards [hM] with x hx
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hx
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  have hfp : eLpNorm f p μ ≠ ∞ :=
    ((memLp_const (p := p) (μ := μ) M).mono' hf hM).eLpNorm_ne_top
  have hexp : 0 ≤ 1 - p.toReal / r.toReal := by
    rw [sub_nonneg]
    rcases eq_or_ne r.toReal 0 with h | h
    · simp [h]
    · exact div_le_one_of_le₀ (ENNReal.toReal_mono hr hpr) ENNReal.toReal_nonneg
  have h := eLpNorm_le_rpow_mul_eLpNorm_rpow hf hM' hp0 hpr hr
  calc (eLpNorm f r μ).toReal
      ≤ (ENNReal.ofReal M ^ (1 - p.toReal / r.toReal) *
          eLpNorm f p μ ^ (p.toReal / r.toReal)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hexp
          ENNReal.ofReal_ne_top) (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfp)) h
    _ = M ^ (1 - p.toReal / r.toReal) * (eLpNorm f p μ).toReal ^ (p.toReal / r.toReal) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
          ENNReal.toReal_ofReal hM0]

end MeasureTheory
