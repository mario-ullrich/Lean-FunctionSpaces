/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Lp.LintegralForm
public import ApproximationSpaces.Sequences.Lq
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Convolution with integrable kernels in `L_p`

On a finite-dimensional real vector space `V` with a Haar measure `μ`, the **convolution** of an
integrable kernel `K` with `f ∈ L_p` is `(K ⋆ f)(x) = ∫ K(y) f(x - y) dy` (`Rd.conv`, Mathlib's
`MeasureTheory.convolution` with the multiplication of `ℂ`).

**Young's inequality** `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`, `1 ≤ p < ∞` (`Rd.eLpNorm_conv_le`), comes from
the weighted Jensen inequality

`(∫ |K(y)| |g(y)| dy)^p ≤ (∫ |K|)^(p-1) ∫ |K(y)| |g(y)|^p dy`

(`Rd.lintegral_mul_rpow_le`, Hölder's inequality for the measure `|K(y)| dy`), applied to
`g(y) = f(x - y)` and integrated over `x` by Tonelli's theorem and the translation invariance of
`μ` (`Rd.lintegral_rpow_lintegral_le`). The same bound shows that the integral of the convolution
converges absolutely at almost every point (`Rd.ae_convolutionExistsAt`), so convolution is linear
in `f` almost everywhere and defines a bounded operator on `L_p` of norm at most `‖K‖_1`
(`Rd.convLp`). These operators compose like their kernels, `K ⋆ (L ⋆ f) = (K ⋆ L) ⋆ f`
(`Rd.convLp_convLp`, from the associativity `Rd.conv_conv_ae`), and are linear in the kernel
(`Rd.convLp_sub_kernel`). Mathlib has the pointwise Hölder bounds of convolutions, not Young's
inequality.

Uniformly bounded families average to bounded functions: `‖∫ Φ(z) G(·, z) dz‖_p ≤ ‖Φ‖_1 M` if
`‖G(·, z)‖_p ≤ M` whenever `Φ(z) ≠ 0` (`Rd.eLpNorm_integral_kernel_le_of_bound`). **Pointwise
bounds**: if `|K| ≤ A` and `K = 0` outside `B̄(0, ρ)`, Hölder's inequality on balls gives
`|(K ⋆ g)(x)| ≤ A |B̄(0,ρ)|^(1-1/p) ‖g‖_p` (`Rd.lintegral_closedBall_le`,
`Rd.enorm_conv_le_of_bound`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Convolution

namespace Rd

/-! ### The weighted Jensen inequality -/

/-- **Weighted Jensen inequality**: for `1 ≤ p` and nonnegative `a`, `g`,
`(∫ a g)^p ≤ (∫ a)^(p-1) ∫ a g^p`. This is Hölder's inequality for the measure `a dμ`: split
`a g = a^(1/q) (a^(1/p) g)` with the conjugate exponent `q` (Mathlib's
`ENNReal.lintegral_mul_le_Lp_mul_Lq`). -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 1 ≤ p) {a g : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hg : AEMeasurable g μ) :
    (∫⁻ y, a y * g y ∂μ) ^ p ≤ (∫⁻ y, a y ∂μ) ^ (p - 1) * ∫⁻ y, a y * g y ^ p ∂μ := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp
  set q := p.conjExponent
  have hpq : p.HolderConjugate q := .conjExponent hp1
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hpq.symm.pos
  have hsum : 1 / q + 1 / p = 1 := by
    have := hpq.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  have hsplit : ∀ y, a y * g y = a y ^ (1 / q) * (a y ^ (1 / p) * g y) := fun y => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
      ENNReal.rpow_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm (ha.pow_const (1 / q))
    ((ha.pow_const (1 / p)).mul hg)
  have h1 : ∀ y, (a y ^ (1 / q)) ^ q = a y := fun y => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have h2 : ∀ y, (a y ^ (1 / p) * g y) ^ p = a y * g y ^ p := fun y => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
  simp only [Pi.mul_apply, h1, h2] at hH
  have hexp : 1 / q * p = p - 1 := by
    have h : 1 / q = 1 - 1 / p := by linarith
    rw [h]
    field_simp
  calc (∫⁻ y, a y * g y ∂μ) ^ p
      = (∫⁻ y, a y ^ (1 / q) * (a y ^ (1 / p) * g y) ∂μ) ^ p := by
        rw [lintegral_congr fun y => hsplit y]
    _ ≤ ((∫⁻ y, a y ∂μ) ^ (1 / q) * (∫⁻ y, a y * g y ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow hH hp0.le
    _ = (∫⁻ y, a y ∂μ) ^ (p - 1) * ∫⁻ y, a y * g y ^ p ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one, hexp]

/-! ### Convolution and Young's inequality -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-- The **convolution** of complex functions, `(K ⋆ f)(x) = ∫ K(y) f(x - y) dy` (Mathlib's
`MeasureTheory.convolution` with the multiplication of `ℂ`). -/
noncomputable def conv (K f : V → ℂ) (μ : Measure V) : V → ℂ :=
  K ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] f

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `(K ⋆ f)(x) = ∫ K(y) f(x - y) dy`. -/
theorem conv_apply (K f : V → ℂ) (μ : Measure V) (x : V) :
    conv K f μ x = ∫ y, K y * f (x - y) ∂μ := by
  rw [conv, convolution_def]
  rfl

/-- Convolutions of a.e. strongly measurable functions are a.e. strongly measurable (Mathlib's
`AEStronglyMeasurable.convolution_integrand` and `AEStronglyMeasurable.integral_prod_right'`). -/
theorem aestronglyMeasurable_conv {K f : V → ℂ} (hK : AEStronglyMeasurable K μ)
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (conv K f μ) μ :=
  (hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf).integral_prod_right'

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The pointwise bound `|(K ⋆ f)(x)| ≤ ∫ |K(y)| |f(x - y)| dy`. -/
theorem enorm_conv_le_lintegral (K f : V → ℂ) (x : V) :
    ‖conv K f μ x‖ₑ ≤ ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ := by
  rw [conv_apply]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun y => enorm_mul _ _

/-- **The integral form of Young's inequality** for nonnegative functions: for `1 ≤ q`,
`∫ (∫ a(y) b(x - y) dy)^q dx ≤ (∫ a)^q ∫ b^q`. By the weighted Jensen inequality the inner power is
at most `(∫ a)^(q-1) ∫ a(y) b(x - y)^q dy`; Tonelli's theorem and the translation invariance of `μ`
give `(∫ a)^(q-1) (∫ a) ∫ b^q`. -/
theorem lintegral_rpow_lintegral_mul_le {q : ℝ} (hq1 : 1 ≤ q) {a b : V → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    ∫⁻ x, (∫⁻ y, a y * b (x - y) ∂μ) ^ q ∂μ ≤ (∫⁻ y, a y ∂μ) ^ q * ∫⁻ x, b x ^ q ∂μ := by
  have hbx : ∀ x, AEMeasurable (fun y => b (x - y)) μ := fun x =>
    hb.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant μ x)
  have hby : ∀ y, AEMeasurable (fun x => b (x - y) ^ q) μ := fun y =>
    (hb.pow_const q).comp_quasiMeasurePreserving
      (measurePreserving_sub_right μ y).quasiMeasurePreserving
  have hprod : AEMeasurable (Function.uncurry fun x y => a y * b (x - y) ^ q) (μ.prod μ) :=
    ha.comp_snd.mul ((hb.pow_const q).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant μ μ))
  calc ∫⁻ x, (∫⁻ y, a y * b (x - y) ∂μ) ^ q ∂μ
      ≤ ∫⁻ x, (∫⁻ y, a y ∂μ) ^ (q - 1) * ∫⁻ y, a y * b (x - y) ^ q ∂μ ∂μ :=
        lintegral_mono fun x => lintegral_mul_rpow_le hq1 ha (hbx x)
    _ = (∫⁻ y, a y ∂μ) ^ (q - 1) * ∫⁻ x, ∫⁻ y, a y * b (x - y) ^ q ∂μ ∂μ :=
        lintegral_const_mul'' _ hprod.lintegral_prod_right'
    _ = (∫⁻ y, a y ∂μ) ^ (q - 1) * ∫⁻ y, ∫⁻ x, a y * b (x - y) ^ q ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hprod]
    _ = (∫⁻ y, a y ∂μ) ^ (q - 1) * ∫⁻ y, a y * ∫⁻ x, b x ^ q ∂μ ∂μ := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul'' _ (hby y), lintegral_sub_right_eq_self (fun x => b x ^ q) y]
    _ = (∫⁻ y, a y ∂μ) ^ (q - 1) * ((∫⁻ y, a y ∂μ) * ∫⁻ x, b x ^ q ∂μ) := by
        rw [lintegral_mul_const'' _ ha]
    _ = (∫⁻ y, a y ∂μ) ^ q * ∫⁻ x, b x ^ q ∂μ := by
        rw [← mul_assoc]
        congr 1
        conv_rhs => rw [show q = (q - 1) + 1 by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]

/-- The integrand of `x ↦ ∫ |K(y)| |f(x - y)|^q dy` is measurable on the product. -/
theorem aemeasurable_kernel_rpow {K f : V → ℂ} (hK : AEStronglyMeasurable K μ)
    (hf : AEStronglyMeasurable f μ) (q : ℝ) :
    AEMeasurable (Function.uncurry fun x y => ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ q) (μ.prod μ) :=
  hK.enorm.comp_snd.mul ((hf.enorm.pow_const q).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_of_right_invariant μ μ))

/-- The function `x ↦ ∫ |K(y)| |f(x - y)| dy` is measurable. -/
theorem aemeasurable_lintegral_kernel {K f : V → ℂ} (hK : AEStronglyMeasurable K μ)
    (hf : AEStronglyMeasurable f μ) :
    AEMeasurable (fun x => ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) μ := by
  have h := (aemeasurable_kernel_rpow hK hf 1).lintegral_prod_right'
  simpa only [ENNReal.rpow_one, Function.uncurry_apply_pair] using h

/-- **The integral form of Young's inequality**: for `1 ≤ p < ∞`,
`∫ (∫ |K(y)| |f(x - y)| dy)^p dx ≤ (‖K‖_1 ‖f‖_p)^p`. -/
theorem lintegral_rpow_lintegral_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : V → ℂ}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) ^ p.toReal ∂μ ≤
      (eLpNorm K 1 μ * eLpNorm f p μ) ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp hp1
    rwa [ENNReal.toReal_one] at h
  refine (lintegral_rpow_lintegral_mul_le hq1 hK.enorm hf.enorm).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), eLpNorm_one_eq_lintegral_enorm hK,
    eLpNorm_rpow_eq hf hp0 hp]

/-- **Young's inequality** for an integrable kernel: `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`, `1 ≤ p < ∞`. -/
theorem eLpNorm_conv_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : V → ℂ}
    (hK : AEStronglyMeasurable K μ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (conv K f μ) p μ ≤ eLpNorm K 1 μ * eLpNorm f p μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine eLpNorm_le_of_lintegral_le (aestronglyMeasurable_conv hK hf) hp0 hp ?_
  exact (lintegral_mono fun x => ENNReal.rpow_le_rpow (enorm_conv_le_lintegral K f x)
    hq.le).trans (lintegral_rpow_lintegral_le hp1 hp hK hf)

omit [BorelSpace V] in
/-- **Weighted averages in `L_p`** (Minkowski's integral inequality, in the form of the weighted
Jensen inequality): for `1 ≤ p < ∞`, a weight `Φ` and a jointly measurable `G`,
`‖∫ Φ(z) G(·, z) dz‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖G(·, z)‖_p^p dz`. -/
theorem eLpNorm_integral_kernel_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ : V → ℂ}
    (hΦ : AEStronglyMeasurable Φ μ) {G : V → V → ℂ} (hG : Measurable (Function.uncurry G)) :
    eLpNorm (fun x => ∫ z, Φ z * G x z ∂μ) p μ ^ p.toReal ≤
      (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) *
        ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => G x z) p μ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp hp1
    rwa [ENNReal.toReal_one] at h
  have hprod : AEMeasurable (Function.uncurry fun x z => ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal)
      (μ.prod μ) :=
    hΦ.enorm.comp_snd.mul (hG.enorm.pow_const _).aemeasurable
  have hint : AEStronglyMeasurable (fun x => ∫ z, Φ z * G x z ∂μ) μ :=
    (hΦ.comp_snd.mul hG.aestronglyMeasurable).integral_prod_right'
  rw [eLpNorm_rpow_eq hint hp0 hp]
  calc ∫⁻ x, ‖∫ z, Φ z * G x z ∂μ‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ * ‖G x z‖ₑ ∂μ) ^ p.toReal ∂μ := lintegral_mono fun x => by
        refine ENNReal.rpow_le_rpow ((enorm_integral_le_lintegral_enorm _).trans_eq ?_) hq.le
        simp_rw [enorm_mul]
    _ ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) *
          ∫⁻ z, ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal ∂μ ∂μ :=
        lintegral_mono fun x => lintegral_mul_rpow_le hq1 hΦ.enorm
          (hG.comp measurable_prodMk_left).enorm.aemeasurable
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) *
          ∫⁻ x, ∫⁻ z, ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal ∂μ ∂μ :=
        lintegral_const_mul'' _ hprod.lintegral_prod_right'
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) *
          ∫⁻ z, ∫⁻ x, ‖Φ z‖ₑ * ‖G x z‖ₑ ^ p.toReal ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hprod]
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) *
          ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => G x z) p μ ^ p.toReal ∂μ := by
        congr 1
        refine lintegral_congr fun z => ?_
        have hGz : AEStronglyMeasurable (fun x => G x z) μ :=
          (hG.comp measurable_prodMk_right).aestronglyMeasurable
        rw [lintegral_const_mul' _ _ enorm_ne_top, eLpNorm_rpow_eq hGz hp0 hp]

omit [BorelSpace V] in
/-- **Weighted averages of uniformly bounded functions**: if `‖G(·, z)‖_p ≤ M` for every `z` with
`Φ(z) ≠ 0` and `0 < ‖Φ‖_1 < ∞`, then `‖∫ Φ(z) G(·, z) dz‖_p ≤ ‖Φ‖_1 M`
(`Rd.eLpNorm_integral_kernel_le`). -/
theorem eLpNorm_integral_kernel_le_of_bound {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ : V → ℂ}
    (hΦ : AEStronglyMeasurable Φ μ) (hΦ0 : ∫⁻ z, ‖Φ z‖ₑ ∂μ ≠ 0) (hΦt : ∫⁻ z, ‖Φ z‖ₑ ∂μ ≠ ∞)
    {G : V → V → ℂ} (hG : Measurable (Function.uncurry G)) {M : ℝ≥0∞}
    (hM : ∀ z, Φ z ≠ 0 → eLpNorm (fun x => G x z) p μ ≤ M) :
    eLpNorm (fun x => ∫ z, Φ z * G x z ∂μ) p μ ≤ (∫⁻ z, ‖Φ z‖ₑ ∂μ) * M := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← ENNReal.rpow_le_rpow_iff hq]
  refine (eLpNorm_integral_kernel_le hp1 hp hΦ hG).trans ?_
  calc (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) *
        ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => G x z) p μ ^ p.toReal ∂μ
      ≤ (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) * ∫⁻ z, ‖Φ z‖ₑ * M ^ p.toReal ∂μ :=
        mul_le_mul' le_rfl (lintegral_mono fun z => by
          by_cases hz : Φ z = 0
          · simp [hz]
          · exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hM z hz) hq.le))
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) * (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (1 : ℝ) * M ^ p.toReal := by
        rw [lintegral_mul_const'' _ hΦ.enorm, ENNReal.rpow_one, mul_assoc]
    _ = ((∫⁻ z, ‖Φ z‖ₑ ∂μ) * M) ^ p.toReal := by
        rw [← ENNReal.rpow_add _ _ hΦ0 hΦt, sub_add_cancel, ENNReal.mul_rpow_of_nonneg _ _ hq.le]

/-- Convolution of an integrable kernel with an `L_p` function is in `L_p`. -/
theorem memLp_conv {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : V → ℂ} (hK : Integrable K μ)
    (hf : MemLp f p μ) : MemLp (conv K f μ) p μ :=
  lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (ENNReal.mul_ne_top
    (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top hf.eLpNorm_ne_top)
    (eLpNorm_conv_le hp1 hp hK.aestronglyMeasurable hf.aestronglyMeasurable))

/-- **The convolution integral converges absolutely almost everywhere** for an integrable
kernel and `f ∈ L_p`, `1 ≤ p < ∞`: the integral form of Young's inequality is finite. -/
theorem ae_convolutionExistsAt {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : V → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt K f x (ContinuousLinearMap.mul ℂ ℂ) μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hK1 : eLpNorm K 1 μ ≠ ∞ := (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top
  have hfin : ∫⁻ x, (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) ^ p.toReal ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le (ENNReal.mul_ne_top hK1
      hf.eLpNorm_ne_top))
      (lintegral_rpow_lintegral_le hp1 hp hK.aestronglyMeasurable hf.aestronglyMeasurable)
  have hmeas : AEMeasurable (fun x => (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ) ^ p.toReal) μ :=
    (aemeasurable_lintegral_kernel hK.aestronglyMeasurable hf.aestronglyMeasurable).pow_const _
  filter_upwards [ae_lt_top' hmeas hfin] with x hx
  have hx' : ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ∂μ < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_rpow_of_pos hq] at hx
    exact lt_irrefl _ hx
  refine ⟨hK.aestronglyMeasurable.convolution_integrand_snd (ContinuousLinearMap.mul ℂ ℂ)
    hf.aestronglyMeasurable x, ?_⟩
  simpa [HasFiniteIntegral, enorm_mul] using hx'

/-- **Convolution is additive** in `f ∈ L_p` almost everywhere. -/
theorem conv_add_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f g : V → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    conv K (f + g) μ =ᵐ[μ] conv K f μ + conv K g μ := by
  filter_upwards [ae_convolutionExistsAt hp1 hp hK hf, ae_convolutionExistsAt hp1 hp hK hg]
    with x hfx hgx
  exact hfx.distrib_add hgx

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- Convolution is homogeneous in `f`. -/
theorem conv_smul (K f : V → ℂ) (c : ℂ) : conv K (c • f) μ = c • conv K f μ :=
  convolution_smul

/-- **The double convolution integral converges absolutely almost everywhere**: for integrable
`K`, `L` and `f ∈ L_p`, `1 ≤ p < ∞`, for almost every `x₀`,
`∫∫ |K(y)| |L(x - y)| |f(x₀ - x)| dx dy < ∞`. The double integral is
`∫ |K(y)| F(x₀ - y) dy` with `F(z) = ∫ |L(w)| |f(z - w)| dw`, and the integral form of Young's
inequality, applied twice, bounds the integral of its `p`-th power. -/
theorem ae_integrable_conv_conv {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K L f : V → ℂ}
    (hK : Integrable K μ) (hL : Integrable L μ) (hf : MemLp f p μ) :
    ∀ᵐ x₀ ∂μ, Integrable (Function.uncurry fun x y => K y * (L (x - y) * f (x₀ - x)))
      (μ.prod μ) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp hp1
    rwa [ENNReal.toReal_one] at h
  have hfm := hf.aestronglyMeasurable
  set F : V → ℝ≥0∞ := fun z => ∫⁻ w, ‖L w‖ₑ * ‖f (z - w)‖ₑ ∂μ with hFdef
  have hF : AEMeasurable F μ := aemeasurable_lintegral_kernel hL.aestronglyMeasurable hfm
  set G : V → ℝ≥0∞ := fun x₀ => ∫⁻ y, ‖K y‖ₑ * F (x₀ - y) ∂μ with hGdef
  have hGm : AEMeasurable G μ :=
    (hK.aestronglyMeasurable.enorm.comp_snd.mul (hF.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant μ μ))).lintegral_prod_right'
  -- the double integral of the norms is `G x₀`
  have hdouble : ∀ x₀, ∫⁻ z, ‖Function.uncurry (fun x y => K y * (L (x - y) * f (x₀ - x))) z‖ₑ
      ∂(μ.prod μ) = G x₀ := fun x₀ => by
    have hmeas : AEMeasurable (Function.uncurry fun x y =>
        ‖K y‖ₑ * (‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ)) (μ.prod μ) :=
      hK.aestronglyMeasurable.enorm.comp_snd.mul
        ((hL.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul
          (hfm.enorm.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀)).comp_fst)
    have hrw : (fun z : V × V =>
        ‖Function.uncurry (fun x y => K y * (L (x - y) * f (x₀ - x))) z‖ₑ) =
        Function.uncurry fun x y => ‖K y‖ₑ * (‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ) := by
      funext z
      obtain ⟨x, y⟩ := z
      simp only [Function.uncurry_apply_pair, enorm_mul]
    have hinner : ∀ y, AEMeasurable (fun x => ‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ) μ := fun y =>
      (hL.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
        (measurePreserving_sub_right μ y).quasiMeasurePreserving).mul
        (hfm.enorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀))
    rw [hrw, lintegral_prod _ hmeas]
    simp only [Function.uncurry_apply_pair]
    rw [lintegral_lintegral_swap hmeas]
    refine lintegral_congr fun y => ?_
    rw [lintegral_const_mul'' _ (hinner y),
      ← lintegral_add_right_eq_self (fun x => ‖L (x - y)‖ₑ * ‖f (x₀ - x)‖ₑ) y]
    congr 1
    refine lintegral_congr fun w => ?_
    simp only [add_sub_cancel_right]
    rw [show x₀ - (w + y) = x₀ - y - w by abel]
  -- the `p`-th power of `G` has finite integral
  have hK1 : ∫⁻ y, ‖K y‖ₑ ∂μ ≠ ∞ := hK.2.ne
  have hL1 : ∫⁻ y, ‖L y‖ₑ ∂μ ≠ ∞ := hL.2.ne
  have hfq : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ ≠ ∞ := by
    rw [← eLpNorm_rpow_eq hfm hp0 hp]
    exact ENNReal.rpow_ne_top_of_nonneg hq.le hf.eLpNorm_ne_top
  have hGfin : ∫⁻ x₀, G x₀ ^ p.toReal ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ ((lintegral_rpow_lintegral_mul_le hq1
      hK.aestronglyMeasurable.enorm hF).trans (mul_le_mul' le_rfl
        (lintegral_rpow_lintegral_mul_le hq1 hL.aestronglyMeasurable.enorm hfm.enorm)))
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le hK1)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le hL1) hfq)
  filter_upwards [ae_lt_top' (hGm.pow_const _) hGfin] with x₀ hx₀
  have hG : G x₀ < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_rpow_of_pos hq] at hx₀
    exact lt_irrefl _ hx₀
  refine ⟨hK.aestronglyMeasurable.comp_snd.mul
    ((hL.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant μ μ)).mul
      ((hfm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀)).comp_fst)), ?_⟩
  rw [HasFiniteIntegral, hdouble x₀]
  exact hG

/-- **Convolution is associative**: `(K ⋆ L) ⋆ f = K ⋆ (L ⋆ f)` almost everywhere for integrable
`K`, `L` and `f ∈ L_p`, `1 ≤ p < ∞` (Mathlib's `convolution_assoc'`, with the absolute convergence
of `Rd.ae_integrable_conv_conv`). -/
theorem conv_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K L f : V → ℂ}
    (hK : Integrable K μ) (hL : Integrable L μ) (hf : MemLp f p μ) :
    conv (conv K L μ) f μ =ᵐ[μ] conv K (conv L f μ) μ := by
  filter_upwards [ae_integrable_conv_conv hp1 hp hK hL hf] with x₀ hx₀
  exact convolution_assoc' (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (fun x y z => by simp only [ContinuousLinearMap.mul_apply']; ring)
    (hK.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hL)
    (ae_convolutionExistsAt hp1 hp hL hf) hx₀

/-- **Convolution is additive in the kernel** almost everywhere, for integrable kernels and
`f ∈ L_p`. -/
theorem add_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K K' f : V → ℂ}
    (hK : Integrable K μ) (hK' : Integrable K' μ) (hf : MemLp f p μ) :
    conv (K + K') f μ =ᵐ[μ] conv K f μ + conv K' f μ := by
  filter_upwards [ae_convolutionExistsAt hp1 hp hK hf, ae_convolutionExistsAt hp1 hp hK' hf]
    with x hx hx'
  exact hx.add_distrib hx'

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- Convolution is homogeneous in the kernel. -/
theorem smul_conv (K f : V → ℂ) (c : ℂ) : conv (c • K) f μ = c • conv K f μ :=
  smul_convolution

/-- **Convolution is subtractive in the kernel** almost everywhere. -/
theorem sub_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K K' f : V → ℂ}
    (hK : Integrable K μ) (hK' : Integrable K' μ) (hf : MemLp f p μ) :
    conv (K - K') f μ =ᵐ[μ] conv K f μ - conv K' f μ := by
  have hneg : conv (-K') f μ = -conv K' f μ := by
    rw [show -K' = (-1 : ℂ) • K' by simp, smul_conv]
    simp
  filter_upwards [add_conv_ae hp1 hp hK hK'.neg hf] with x hx
  rw [sub_eq_add_neg K K', hx, Pi.add_apply, hneg, Pi.neg_apply, Pi.sub_apply, sub_eq_add_neg]

/-- Convolutions of functions that agree almost everywhere agree everywhere (Mathlib's
`convolution_congr`). -/
theorem conv_congr_ae {K f g : V → ℂ} (hfg : f =ᵐ[μ] g) : conv K f μ = conv K g μ :=
  convolution_congr (ContinuousLinearMap.mul ℂ ℂ) (Filter.EventuallyEq.refl _ K) hfg

/-- **Convolution is commutative**: `K ⋆ L = L ⋆ K` (Mathlib's `convolution_flip`). -/
theorem conv_comm (K L : V → ℂ) : conv K L μ = conv L K μ := by
  rw [conv, conv, ← convolution_flip, ContinuousLinearMap.flip_mul]

/-- Convolutions of integrable functions are integrable (Mathlib's
`Integrable.integrable_convolution`). -/
theorem integrable_conv {K L : V → ℂ} (hK : Integrable K μ) (hL : Integrable L μ) :
    Integrable (conv K L μ) μ :=
  hK.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hL

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Young's inequality for the classes in `L_p`**:
`‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p` for `f ∈ L_p`. -/
theorem norm_toLp_conv_le (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    ‖(memLp_conv Fact.out hp hK (Lp.memLp f)).toLp (conv K f μ)‖ ≤
      (eLpNorm K 1 μ).toReal * ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top
    (Lp.eLpNorm_ne_top f)) (eLpNorm_conv_le Fact.out hp hK.aestronglyMeasurable
      (Lp.aestronglyMeasurable f))

/-- **Convolution with an integrable kernel as a bounded operator on `L_p`**, `1 ≤ p < ∞`, of
norm at most `‖K‖_1` (Young's inequality). -/
noncomputable def convLp (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) :
    Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_conv Fact.out hp hK (Lp.memLp f)).toLp (conv K f μ)
      map_add' := fun f g => by
        refine Lp.ext ?_
        have hc : conv K (⇑(f + g)) μ = conv K (⇑f + ⇑g) μ := conv_congr_ae (Lp.coeFn_add f g)
        filter_upwards [MemLp.coeFn_toLp (memLp_conv Fact.out hp hK (Lp.memLp (f + g))),
          MemLp.coeFn_toLp (memLp_conv Fact.out hp hK (Lp.memLp f)),
          MemLp.coeFn_toLp (memLp_conv Fact.out hp hK (Lp.memLp g)),
          Lp.coeFn_add ((memLp_conv Fact.out hp hK (Lp.memLp f)).toLp (conv K f μ))
            ((memLp_conv Fact.out hp hK (Lp.memLp g)).toLp (conv K g μ)),
          conv_add_ae Fact.out hp hK (Lp.memLp f) (Lp.memLp g)] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, hc, h5, Pi.add_apply]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have hc : conv K (⇑(c • f)) μ = conv K (c • ⇑f) μ := conv_congr_ae (Lp.coeFn_smul c f)
        filter_upwards [MemLp.coeFn_toLp (memLp_conv Fact.out hp hK (Lp.memLp (c • f))),
          MemLp.coeFn_toLp (memLp_conv Fact.out hp hK (Lp.memLp f)),
          Lp.coeFn_smul c ((memLp_conv Fact.out hp hK (Lp.memLp f)).toLp (conv K f μ))]
          with x h1 h2 h3
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, hc, conv_smul, Pi.smul_apply] }
    (eLpNorm K 1 μ).toReal (norm_toLp_conv_le hp hK)

/-- The operator `convLp` is convolution, almost everywhere. -/
theorem convLp_apply_ae (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    convLp hp hK f =ᵐ[μ] conv K f μ :=
  MemLp.coeFn_toLp (memLp_conv Fact.out hp hK (Lp.memLp f))

/-- **Young's inequality on `L_p`**: `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`. -/
theorem norm_convLp_le (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    ‖convLp hp hK f‖ ≤ (eLpNorm K 1 μ).toReal * ‖f‖ :=
  norm_toLp_conv_le hp hK f

/-- **Young's inequality on `L_p`** in extended norms: `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`. -/
theorem enorm_convLp_le (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (f : Lp ℂ p μ) :
    ‖convLp hp hK f‖ₑ ≤ eLpNorm K 1 μ * ‖f‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (convLp_apply_ae hp hK f)]
  exact eLpNorm_conv_le Fact.out hp hK.aestronglyMeasurable (Lp.aestronglyMeasurable f)

/-- **Convolution operators compose like their kernels**: `K ⋆ (L ⋆ f) = (K ⋆ L) ⋆ f` in `L_p`
(`Rd.conv_conv_ae`). -/
theorem convLp_convLp (hp : p ≠ ∞) {K L : V → ℂ} (hK : Integrable K μ) (hL : Integrable L μ)
    (f : Lp ℂ p μ) : convLp hp hK (convLp hp hL f) = convLp hp (integrable_conv hK hL) f := by
  refine Lp.ext ?_
  have h1 : conv K (⇑(convLp hp hL f)) μ = conv K (conv L f μ) μ :=
    conv_congr_ae (convLp_apply_ae hp hL f)
  filter_upwards [convLp_apply_ae hp hK (convLp hp hL f),
    convLp_apply_ae hp (integrable_conv hK hL) f, conv_conv_ae Fact.out hp hK hL (Lp.memLp f)]
    with x hx1 hx2 hx3
  rw [hx1, h1, hx2, hx3]

/-- If `K ⋆ L = M`, then `K ⋆ (L ⋆ f) = M ⋆ f` in `L_p`. -/
theorem convLp_convLp_of_eq (hp : p ≠ ∞) {K L M : V → ℂ} (hK : Integrable K μ)
    (hL : Integrable L μ) (hM : Integrable M μ) (h : conv K L μ = M) (f : Lp ℂ p μ) :
    convLp hp hK (convLp hp hL f) = convLp hp hM f := by
  rw [convLp_convLp hp hK hL]
  subst h
  rfl

/-- Convolution with the zero kernel is zero. -/
theorem convLp_of_eq_zero (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (h : K = 0)
    (f : Lp ℂ p μ) : convLp hp hK f = 0 := by
  subst h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [convLp_apply_ae hp hK f] with x hx
  rw [hx, conv_apply]
  simp

/-- **Convolution operators commute**: `K ⋆ (L ⋆ f) = L ⋆ (K ⋆ f)` in `L_p`. -/
theorem convLp_comm (hp : p ≠ ∞) {K L : V → ℂ} (hK : Integrable K μ) (hL : Integrable L μ)
    (f : Lp ℂ p μ) : convLp hp hK (convLp hp hL f) = convLp hp hL (convLp hp hK f) := by
  rw [convLp_convLp_of_eq hp hK hL (integrable_conv hL hK) (conv_comm K L), convLp_convLp]

/-- **Convolution operators are additive in the kernel**: `(K + K') ⋆ f = K ⋆ f + K' ⋆ f` in
`L_p`. -/
theorem convLp_add_kernel (hp : p ≠ ∞) {K K' : V → ℂ} (hK : Integrable K μ)
    (hK' : Integrable K' μ) (f : Lp ℂ p μ) :
    convLp hp (hK.add hK') f = convLp hp hK f + convLp hp hK' f := by
  refine Lp.ext ?_
  filter_upwards [convLp_apply_ae hp (hK.add hK') f, convLp_apply_ae hp hK f,
    convLp_apply_ae hp hK' f, Lp.coeFn_add (convLp hp hK f) (convLp hp hK' f),
    add_conv_ae Fact.out hp hK hK' (Lp.memLp f)] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]

/-- **Convolution operators are subtractive in the kernel**: `(K - K') ⋆ f = K ⋆ f - K' ⋆ f`
in `L_p`. -/
theorem convLp_sub_kernel (hp : p ≠ ∞) {K K' : V → ℂ} (hK : Integrable K μ)
    (hK' : Integrable K' μ) (f : Lp ℂ p μ) :
    convLp hp (hK.sub hK') f = convLp hp hK f - convLp hp hK' f := by
  refine Lp.ext ?_
  filter_upwards [convLp_apply_ae hp (hK.sub hK') f, convLp_apply_ae hp hK f,
    convLp_apply_ae hp hK' f, Lp.coeFn_sub (convLp hp hK f) (convLp hp hK' f),
    sub_conv_ae Fact.out hp hK hK' (Lp.memLp f)] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sub_apply, h2, h3, h5, Pi.sub_apply]

end Rd

/-! ### Pointwise bounds with Lebesgue measure -/

namespace Rd

open Metric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Hölder's inequality on a ball**: `∫_{B̄(x,ρ)} |g| ≤ |B̄(x,ρ)|^(1-1/p) ‖g‖_p`. -/
theorem lintegral_closedBall_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) (x : V) (ρ : ℝ) :
    ∫⁻ z in closedBall x ρ, ‖g z‖ₑ ≤
      volume (closedBall x ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume := by
  have hgr : AEStronglyMeasurable g (volume.restrict (closedBall x ρ)) := hg.restrict
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 hgr
  rw [eLpNorm_one_eq_lintegral_enorm hgr, Measure.restrict_apply_univ, ENNReal.toReal_one,
    div_one] at h
  refine h.trans ?_
  rw [mul_comm]
  exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- `∫ |K(y)| |g(x - y)| dy ≤ A |B̄(0,ρ)|^(1-1/p) ‖g‖_p` if `|K| ≤ A` and `K = 0` outside
`B̄(0, ρ)`. -/
theorem lintegral_kernel_mul_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) {A : ℝ≥0∞} (hK : ∀ y, ‖K y‖ₑ ≤ A) {ρ : ℝ}
    (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) (x : V) :
    ∫⁻ y, ‖K y‖ₑ * ‖g (x - y)‖ₑ ≤
      A * volume (closedBall (0 : V) ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume := by
  set G : V → ℝ≥0∞ := (closedBall x ρ).indicator fun z => ‖g z‖ₑ
  have h1 : ∀ y, ‖K y‖ₑ * ‖g (x - y)‖ₑ ≤ A * G (x - y) := fun y => by
    by_cases hy : ‖y‖ ≤ ρ
    · have hmem : x - y ∈ closedBall x ρ := by
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact hy
      simp only [G, Set.indicator_of_mem hmem]
      exact mul_le_mul' (hK y) le_rfl
    · rw [hKρ y (not_le.1 hy), enorm_zero, zero_mul]
      exact zero_le
  calc ∫⁻ y, ‖K y‖ₑ * ‖g (x - y)‖ₑ ≤ ∫⁻ y, A * G (x - y) := lintegral_mono h1
    _ = ∫⁻ z, A * G z := lintegral_sub_left_eq_self (fun z => A * G z) x
    _ = A * ∫⁻ z in closedBall x ρ, ‖g z‖ₑ := by
        rw [lintegral_const_mul'' A (hg.enorm.indicator measurableSet_closedBall),
          lintegral_indicator measurableSet_closedBall]
    _ ≤ A * (volume (closedBall x ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume) :=
        mul_le_mul' le_rfl (lintegral_closedBall_le hp1 hg x ρ)
    _ = _ := by rw [Measure.addHaar_closedBall_center, mul_assoc]

/-- **Pointwise bound of a convolution**: if `|K| ≤ A` and `K = 0` outside `B̄(0, ρ)`, then
`|(K ⋆ g)(x)| ≤ A |B̄(0,ρ)|^(1-1/p) ‖g‖_p`, by Hölder's inequality on the ball `B̄(x, ρ)`. -/
theorem enorm_conv_le_of_bound {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ}
    (hg : AEStronglyMeasurable g volume) {A : ℝ≥0∞} (hK : ∀ y, ‖K y‖ₑ ≤ A) {ρ : ℝ}
    (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) (x : V) :
    ‖conv K g volume x‖ₑ ≤
      A * volume (closedBall (0 : V) ρ) ^ (1 - 1 / p.toReal) * eLpNorm g p volume :=
  (enorm_conv_le_lintegral K g x).trans (lintegral_kernel_mul_le hp1 hg hK hKρ x)

/-- The convolution integrals of a continuous kernel with compact support and a locally integrable
function converge absolutely. -/
theorem integrable_translate_mul_of_locallyIntegrable {K g : V → ℂ} (hKc : Continuous K)
    (hKs : HasCompactSupport K) (hg : LocallyIntegrable g volume) (v x : V) :
    Integrable (fun y => K (y + v) * g (x - y)) volume := by
  have hc : HasCompactSupport fun y => K (y + v) :=
    hKs.comp_homeomorph (Homeomorph.addRight v)
  exact (hc.convolutionExists_left (ContinuousLinearMap.mul ℂ ℂ)
    (hKc.comp (continuous_id.add continuous_const)) hg) x

/-- `(K ⋆ g)(x + v) = ∫ K(y + v) g(x - y) dy`, by translation invariance. -/
theorem conv_add_apply (K g : V → ℂ) (x v : V) :
    conv K g volume (x + v) = ∫ y, K (y + v) * g (x - y) := by
  rw [conv_apply, ← integral_add_right_eq_self (fun y => K y * g (x + v - y)) v]
  congr 1
  funext y
  congr 2
  abel

end Rd
