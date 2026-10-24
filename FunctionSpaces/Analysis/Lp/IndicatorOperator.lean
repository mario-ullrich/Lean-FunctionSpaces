/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Multiplication by an indicator on `L_p`

For a measurable set `s` of a measure space, multiplication by the indicator `1_s` is a bounded
linear operator on `L_p(μ)` of norm at most `1` (`Rd.indicatorLp`); it is multiplication by
`1_s` almost everywhere (`Rd.indicatorLp_apply_ae`) and `‖1_s g‖_p ≤ ‖g‖_p`
(`Rd.enorm_indicatorLp_le`). Two classes have the same image iff they agree almost everywhere
on `s` (`Rd.indicatorLp_eq_iff_ae_eq_restrict`), and `∫_s a b = ⟨1_s a, b⟩` for `a, b ∈ L_2`
with Mathlib's pairing of `L_2` with `L_2` (`Rd.setIntegral_mul_eq_lpPairing`). For a measurable
`T ⊆ O`, the extension by zero `g ↦ 1_T g` from `L_p(μ|_O)` to `L_p(μ)` is a bounded linear
operator of norm at most `1` (`Rd.indicatorExtendLp`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Rd

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- `1_s g ∈ L_p` for `g ∈ L_p`. -/
theorem memLp_indicator_coe {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    MemLp (s.indicator (g : α → ℂ)) p μ :=
  (Lp.memLp g).indicator hs

omit [Fact (1 ≤ p)] in
/-- `‖1_s g‖_p ≤ ‖g‖_p` for the class of `1_s g`. -/
theorem norm_toLp_indicator_le {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    ‖(memLp_indicator_coe hs g).toLp _‖ ≤ ‖g‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_indicator_le _ hs)

/-- **Multiplication by the indicator of a measurable set** as an operator on `L_p` of norm at
most `1`. -/
noncomputable def indicatorLp {s : Set α} (hs : MeasurableSet s) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_indicator_coe hs g).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_coe hs (f + g))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_coe hs f)
        have e3 := MemLp.coeFn_toLp (memLp_indicator_coe hs g)
        have e4 := Lp.coeFn_add f g
        have e5 := Lp.coeFn_add ((memLp_indicator_coe hs f).toLp _)
          ((memLp_indicator_coe hs g).toLp _)
        filter_upwards [e1, e2, e3, e4, e5] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, h4, Pi.add_apply]
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_coe hs (c • f))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_coe hs f)
        have e3 := Lp.coeFn_smul c f
        have e4 := Lp.coeFn_smul c ((memLp_indicator_coe hs f).toLp _)
        filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, h3, Pi.smul_apply]
        · simp only [Set.indicator_of_notMem hx, smul_zero] }
    1 (fun g => by
      rw [one_mul]
      exact norm_toLp_indicator_le hs g)

/-- Multiplication by an indicator is multiplication by the indicator, almost everywhere. -/
theorem indicatorLp_apply_ae {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    indicatorLp hs g =ᵐ[μ] s.indicator g :=
  MemLp.coeFn_toLp (memLp_indicator_coe hs g)

/-- **Integrals over a set as a pairing**: `∫_s a b = ⟨1_s a, b⟩` for `a, b ∈ L_2(μ)` and a
measurable set `s`, with Mathlib's bounded bilinear pairing of `L_2` with `L_2`
(`ContinuousLinearMap.lpPairing`). -/
theorem setIntegral_mul_eq_lpPairing {s : Set α} (hs : MeasurableSet s) (a b : Lp ℂ 2 μ) :
    ∫ x in s, a x * b x ∂μ =
      (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2 (indicatorLp hs a) b := by
  rw [ContinuousLinearMap.lpPairing_eq_integral, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorLp_apply_ae hs a] with x hx
  rw [ContinuousLinearMap.mul_apply', hx]
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- `‖1_s g‖_p ≤ ‖g‖_p`. -/
theorem enorm_indicatorLp_le {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    ‖indicatorLp hs g‖ₑ ≤ ‖g‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hs g)]
  exact eLpNorm_indicator_le _ hs

/-- Two elements of `L_p` have the same restriction `1_s F = 1_s f` to a measurable set `s` iff
they agree almost everywhere on `s`: Mathlib's `MeasureTheory.ae_eq_restrict_iff_indicator_ae_eq`
for the classes in `L_p`. -/
theorem indicatorLp_eq_iff_ae_eq_restrict {s : Set α} (hs : MeasurableSet s) {F f : Lp ℂ p μ} :
    indicatorLp hs F = indicatorLp hs f ↔ (F : α → ℂ) =ᵐ[μ.restrict s] f := by
  rw [ae_eq_restrict_iff_indicator_ae_eq hs, Lp.ext_iff]
  exact ⟨fun h => (indicatorLp_apply_ae hs F).symm.trans (h.trans (indicatorLp_apply_ae hs f)),
    fun h => (indicatorLp_apply_ae hs F).trans (h.trans (indicatorLp_apply_ae hs f).symm)⟩

/-! ### Extension by zero -/

omit [Fact (1 ≤ p)] in
/-- For `g ∈ L_p(μ|_O)` and a measurable `T ⊆ O`, the extension by zero `1_T g` lies in `L_p(μ)`
(Mathlib's `MeasureTheory.memLp_indicator_iff_restrict`). -/
theorem memLp_indicator_restrict {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) : MemLp (T.indicator (g : α → ℂ)) p μ :=
  (memLp_indicator_iff_restrict hT).2 ((Lp.memLp g).mono_measure (Measure.restrict_mono hTO le_rfl))

omit [Fact (1 ≤ p)] in
/-- `‖1_T g‖_{L_p(μ)} ≤ ‖g‖_{L_p(μ|_O)}` for `T ⊆ O` (Mathlib's
`MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`). -/
theorem eLpNorm_indicator_restrict_le {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) :
    eLpNorm (T.indicator (g : α → ℂ)) p μ ≤ eLpNorm g p (μ.restrict O) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hT]
  exact eLpNorm_mono_measure _ (Measure.restrict_mono hTO le_rfl)

/-- **Extension by zero** from `L_p(μ|_O)` to `L_p(μ)` on a measurable `T ⊆ O`: the operator
`g ↦ 1_T g` of norm at most `1`. -/
noncomputable def indicatorExtendLp {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O) :
    Lp ℂ p (μ.restrict O) →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_indicator_restrict hT hTO g).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO (f + g))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO f)
        have e3 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO g)
        have e4 := ae_restrict_of_ae_restrict_of_subset hTO (Lp.coeFn_add f g)
        have e5 := Lp.coeFn_add ((memLp_indicator_restrict hT hTO f).toLp _)
          ((memLp_indicator_restrict hT hTO g).toLp _)
        filter_upwards [e1, e2, e3, e5, (ae_restrict_iff' hT).1 e4] with x h1 h2 h3 h5 h4
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ T
        · simp only [Set.indicator_of_mem hx, h4 hx, Pi.add_apply]
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO (c • f))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO f)
        have e3 := ae_restrict_of_ae_restrict_of_subset hTO (Lp.coeFn_smul c f)
        have e4 := Lp.coeFn_smul c ((memLp_indicator_restrict hT hTO f).toLp _)
        filter_upwards [e1, e2, e4, (ae_restrict_iff' hT).1 e3] with x h1 h2 h4 h3
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ T
        · simp only [Set.indicator_of_mem hx, h3 hx, Pi.smul_apply]
        · simp only [Set.indicator_of_notMem hx, smul_zero] }
    1 (fun g => by
      change ‖(memLp_indicator_restrict hT hTO g).toLp _‖ ≤ 1 * ‖g‖
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_indicator_restrict_le hT hTO g))

/-- The extension by zero is `1_T g` almost everywhere. -/
theorem indicatorExtendLp_apply_ae {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) : indicatorExtendLp hT hTO g =ᵐ[μ] T.indicator g :=
  MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO g)

/-- `‖1_T g‖_{L_p(μ)} ≤ ‖g‖_{L_p(μ|_O)}` for the extension by zero. -/
theorem enorm_indicatorExtendLp_le {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) : ‖indicatorExtendLp hT hTO g‖ₑ ≤ ‖g‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def g, eLpNorm_congr_ae (indicatorExtendLp_apply_ae hT hTO g)]
  exact eLpNorm_indicator_restrict_le hT hTO g

end Rd
