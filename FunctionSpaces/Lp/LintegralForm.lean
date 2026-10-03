/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `L_p` norms through integrals of powers

For `0 < p < ∞` the `L_p` norm of `g` is `(∫ ‖g‖^p)^(1/p)`.  The function-space files use it in
two forms: as the identity `‖g‖_p^p = ∫ ‖g‖^p` (`MeasureTheory.eLpNorm_rpow_eq`), and as the bound
`‖g‖_p ≤ B` whenever `∫ ‖g‖^p ≤ B^p` (`MeasureTheory.eLpNorm_le_of_lintegral_le`).  Both are short
consequences of Mathlib's `eLpNorm_eq_lintegral_rpow_enorm_toReal`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- `L_p` norms through `L_p` integrals, for `0 < p < ∞`. -/
theorem eLpNorm_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) : eLpNorm g p μ ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg, one_div,
    ENNReal.rpow_inv_rpow (ENNReal.toReal_pos hp0 hp).ne']

/-- The `L_p` norm through the integral of the `p`-th power, as an inequality. -/
theorem eLpNorm_le_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {B : ℝ≥0∞}
    (h : ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ ≤ B ^ p.toReal) : eLpNorm g p μ ≤ B := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg]
  calc (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤ (B ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = B := by rw [one_div, ENNReal.rpow_rpow_inv hq.ne']

end MeasureTheory
