/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Approximate identities in `L_p`

The **dilation** `Φ_c(x) = c^n Φ(c x)`, `n = dim V`, keeps the integral and the `L_1` norm of `Φ`
(`Rd.integral_dilate`, `Rd.eLpNorm_dilate_one`), and the convolution with `Φ_c` averages `f` over
the shifts `c^(-1) z` weighted by `Φ(z)`: `(Φ_c ⋆ f)(x) = ∫ Φ(z) f(x - c^(-1) z) dz`
(`Rd.conv_dilate_apply`, Mathlib's `Measure.integral_comp_smul`).

**Approximate identities** (`Rd.tendsto_eLpNorm_conv_dilate_sub`): for an integrable `Φ` with
`∫ Φ = 1` and `f ∈ L_p`, `1 ≤ p < ∞`, `‖Φ_c ⋆ f - f‖_p → 0` as `c → ∞`. With `∫ Φ = 1`,
`(Φ_c ⋆ f)(x) - f(x) = ∫ Φ(z) (f(x - c^(-1) z) - f(x)) dz`, and the weighted Jensen inequality
gives `‖Φ_c ⋆ f - f‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖f(· - c^(-1) z) - f‖_p^p dz`. Translation is
continuous in `L_p` (`Rd.continuous_eLpNorm_comp_sub_sub`, from Mathlib's continuity of the
action of `V` on `L_p` by translation of the domain), so the integrand tends to `0`, and dominated
convergence applies with the bound `|Φ(z)| (2 ‖f‖_p)^p`. For the operators of `Rd.convLp` this
reads `Φ_{c_i} ⋆ f → f` in `L_p` along any dilation factors `c_i → ∞`
(`Rd.tendsto_convLp_dilate`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-! ### Continuity of translation -/

/-- **Continuity of translation in `L_p`**, `1 ≤ p < ∞`: `w ↦ ‖f(· - w) - f‖_p` is continuous,
from Mathlib's continuity of the action of `V` on `L_p` by translation of the domain
(`Lp.instContinuousVAddDomAddAct`). -/
theorem continuous_eLpNorm_comp_sub_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {f : V → ℂ}
    (hf : MemLp f p μ) : Continuous fun w : V => eLpNorm (fun x => f (x - w) - f x) p μ := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  set G : V → Lp ℂ p μ := fun w =>
    (hf.comp_measurePreserving (measurePreserving_vadd (-w) μ)).toLp (fun x => f (-w +ᵥ x))
  have hc : Continuous fun w : V => DomAddAct.mk (-w) +ᵥ hf.toLp f :=
    (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const
  have hG : Continuous G := hc.congr fun w => DomAddAct.mk_vadd_toLp (-w) hf
  have hT : Continuous fun w : V => ‖G w - hf.toLp f‖ₑ := (hG.sub continuous_const).enorm
  refine hT.congr fun w => ?_
  simp only [G]
  rw [← MemLp.toLp_sub, Lp.enorm_toLp]
  congr 1
  funext x
  simp only [Pi.sub_apply, vadd_eq_add, neg_add_eq_sub]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `‖f(· - w)‖_p = ‖f‖_p`: translation preserves `L_p` norms. -/
theorem eLpNorm_comp_sub_right {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) (w : V) :
    eLpNorm (fun x => f (x - w)) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_sub_right μ w)

/-! ### Dilations -/

/-- The **dilation** `Φ_c(x) = c^n Φ(c x)`, `n = dim V`, which keeps the integral of `Φ`. -/
noncomputable def dilate (c : ℝ) (Φ : V → ℂ) (x : V) : ℂ :=
  (((c ^ finrank ℝ V : ℝ)) : ℂ) * Φ (c • x)

/-- Dilations of integrable functions are integrable. -/
theorem integrable_dilate {Φ : V → ℂ} (hΦ : Integrable Φ μ) {c : ℝ} (hc : c ≠ 0) :
    Integrable (dilate c Φ) μ :=
  (hΦ.comp_smul hc).const_mul _

/-- **The dilation keeps the integral**: `∫ Φ_c = ∫ Φ` for `c > 0` (Mathlib's
`Measure.integral_comp_smul`). -/
theorem integral_dilate (Φ : V → ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ x, dilate c Φ x ∂μ = ∫ x, Φ x ∂μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  simp only [dilate]
  rw [integral_const_mul, Measure.integral_comp_smul μ Φ c, abs_of_pos (inv_pos.2 hpow),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpow.ne',
    Complex.ofReal_one, one_mul]

/-- **The dilation keeps the `L_1` norm**: `‖Φ_c‖_1 = ‖Φ‖_1` for `c > 0`. -/
theorem eLpNorm_dilate_one {Φ : V → ℂ} (hΦ : Integrable Φ μ) {c : ℝ} (hc : 0 < c) :
    eLpNorm (dilate c Φ) 1 μ = eLpNorm Φ 1 μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  have hd := integrable_dilate hΦ hc.ne'
  rw [eLpNorm_one_eq_lintegral_enorm hd.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hΦ.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hd, ← ofReal_integral_norm_eq_lintegral_enorm hΦ]
  congr 1
  have hnorm : ∀ x, ‖dilate c Φ x‖ = c ^ finrank ℝ V * ‖Φ (c • x)‖ := fun x => by
    rw [dilate, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow]
  simp_rw [hnorm]
  rw [integral_const_mul, Measure.integral_comp_smul μ (fun y => ‖Φ y‖) c,
    abs_of_pos (inv_pos.2 hpow), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul]

/-- **Convolution with a dilation**: `(Φ_c ⋆ f)(x) = ∫ Φ(z) f(x - c^(-1) z) dz` for `c > 0`
(substitute `y = c^(-1) z`, Mathlib's `Measure.integral_comp_smul`). -/
theorem conv_dilate_apply (Φ f : V → ℂ) {c : ℝ} (hc : 0 < c) (x : V) :
    conv (dilate c Φ) f μ x = ∫ z, Φ z * f (x - c⁻¹ • z) ∂μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  rw [conv_apply]
  have h : ∀ y, dilate c Φ y * f (x - y) =
      (((c ^ finrank ℝ V : ℝ)) : ℂ) * (fun z => Φ z * f (x - c⁻¹ • z)) (c • y) := fun y => by
    simp only [dilate, inv_smul_smul₀ hc.ne']
    ring
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_smul μ (fun z => Φ z * f (x - c⁻¹ • z)) c,
    abs_of_pos (inv_pos.2 hpow), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hpow.ne', Complex.ofReal_one, one_mul]

/-! ### Approximate identities -/

/-- **The averaged translates are integrable**: for integrable `Φ`, `f ∈ L_p`, `c > 0` and almost
every `x`, `z ↦ Φ(z) f(x - c^(-1) z)` is integrable; its integral is `(Φ_c ⋆ f)(x)`. -/
theorem ae_integrable_dilate_mul {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ f : V → ℂ}
    (hΦ : Integrable Φ μ) (hf : MemLp f p μ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ x ∂μ, Integrable (fun z => Φ z * f (x - c⁻¹ • z)) μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  filter_upwards [ae_convolutionExistsAt hp1 hp (integrable_dilate hΦ hc.ne') hf] with x hx
  have hx' : Integrable (fun y => dilate c Φ y * f (x - y)) μ := hx
  have h2 := (hx'.comp_smul (inv_ne_zero hc.ne')).const_mul ((((c ^ finrank ℝ V)⁻¹ : ℝ)) : ℂ)
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only [dilate, smul_inv_smul₀ hc.ne']
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpow.ne',
    Complex.ofReal_one, one_mul]

/-- **The local bound of an approximate identity**: for `∫ Φ = 1`, `c > 0` and almost every
`x`, `|(Φ_c ⋆ f)(x) - f(x)| ≤ ∫ |Φ(z)| |f(x - c^(-1) z) - f(x)| dz`. -/
theorem ae_enorm_conv_dilate_sub_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ f : V → ℂ}
    (hΦ : Integrable Φ μ) (h1 : ∫ x, Φ x ∂μ = 1) (hf : MemLp f p μ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ x ∂μ, ‖conv (dilate c Φ) f μ x - f x‖ₑ ≤
      ∫⁻ z, ‖Φ z‖ₑ * ‖f (x - c⁻¹ • z) - f x‖ₑ ∂μ := by
  filter_upwards [ae_integrable_dilate_mul hp1 hp hΦ hf hc] with x hint
  have hconst : Integrable (fun z => Φ z * f x) μ := hΦ.mul_const (f x)
  calc ‖conv (dilate c Φ) f μ x - f x‖ₑ
      = ‖∫ z, (Φ z * f (x - c⁻¹ • z) - Φ z * f x) ∂μ‖ₑ := by
        rw [integral_sub hint hconst, integral_mul_const, h1, one_mul, conv_dilate_apply Φ f hc x]
    _ ≤ ∫⁻ z, ‖Φ z * f (x - c⁻¹ • z) - Φ z * f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ z, ‖Φ z‖ₑ * ‖f (x - c⁻¹ • z) - f x‖ₑ ∂μ := by
        congr 1
        funext z
        rw [← mul_sub, enorm_mul]

/-- **Approximate identities in `L_p`**: for an integrable `Φ` with `∫ Φ = 1` and `f ∈ L_p`,
`1 ≤ p < ∞`, `‖Φ_c ⋆ f - f‖_p → 0` as `c → ∞`. -/
theorem tendsto_eLpNorm_conv_dilate_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {Φ f : V → ℂ}
    (hΦ : Integrable Φ μ) (h1 : ∫ x, Φ x ∂μ = 1) (hf : MemLp f p μ) :
    Tendsto (fun c : ℝ => eLpNorm (conv (dilate c Φ) f μ - f) p μ) atTop (𝓝 0) := by
  -- reduce to a strongly measurable representative of `f`
  obtain ⟨g, hgm, hfg⟩ := hf.aestronglyMeasurable
  have hg : MemLp g p μ := hf.ae_eq hfg
  have hcong : ∀ c : ℝ, eLpNorm (conv (dilate c Φ) f μ - f) p μ =
      eLpNorm (conv (dilate c Φ) g μ - g) p μ := fun c => by
    rw [conv_congr_ae hfg]
    exact eLpNorm_congr_ae ((Filter.EventuallyEq.refl _ _).sub hfg)
  simp_rw [hcong]
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp hp1
    rwa [ENNReal.toReal_one] at h
  set q := p.toReal
  set T : V → ℝ≥0∞ := fun w => eLpNorm (fun x => g (x - w) - g x) p μ
  have hT : Continuous T := continuous_eLpNorm_comp_sub_sub hp hg
  have hT0 : T 0 = 0 := by simp [T]
  have hgmeas : Measurable g := hgm.measurable
  have hΦ1 : ∫⁻ z, ‖Φ z‖ₑ ∂μ ≠ ∞ := hΦ.2.ne
  -- the bound for `c > 0`
  set I : ℝ → ℝ≥0∞ := fun c => ∫⁻ z, ‖Φ z‖ₑ * T (c⁻¹ • z) ^ q ∂μ
  have hbound : ∀ c : ℝ, 0 < c → eLpNorm (conv (dilate c Φ) g μ - g) p μ ≤
      ((∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) * I c) ^ (1 / q) := fun c hc => by
    have hconvm : AEStronglyMeasurable (conv (dilate c Φ) g μ - g) μ :=
      (aestronglyMeasurable_conv (integrable_dilate hΦ hc.ne').aestronglyMeasurable
        hg.aestronglyMeasurable).sub hgm.aestronglyMeasurable
    refine eLpNorm_le_of_lintegral_le hconvm hp0 hp ?_
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
    have hprod : AEMeasurable (Function.uncurry fun x z =>
        ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q) (μ.prod μ) :=
      hΦ.aestronglyMeasurable.enorm.comp_snd.mul
        (((hgmeas.comp (measurable_fst.sub (measurable_snd.const_smul c⁻¹))).sub
          (hgmeas.comp measurable_fst)).enorm.pow_const q).aemeasurable
    calc ∫⁻ x, ‖(conv (dilate c Φ) g μ - g) x‖ₑ ^ q ∂μ
        ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ∂μ) ^ q ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_enorm_conv_dilate_sub_le hp1 hp hΦ h1 hg hc] with x hx
          exact ENNReal.rpow_le_rpow hx hq.le
      _ ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) *
            ∫⁻ z, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q ∂μ ∂μ :=
          lintegral_mono fun x => lintegral_mul_rpow_le hq1 hΦ.aestronglyMeasurable.enorm
            ((hgmeas.comp (measurable_const.sub (measurable_id.const_smul c⁻¹))).sub
              measurable_const).enorm.aemeasurable
      _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) *
            ∫⁻ x, ∫⁻ z, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q ∂μ ∂μ :=
          lintegral_const_mul'' _ hprod.lintegral_prod_right'
      _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) *
            ∫⁻ z, ∫⁻ x, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q ∂μ ∂μ := by
          rw [lintegral_lintegral_swap hprod]
      _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) * I c := by
          congr 1
          refine lintegral_congr fun z => ?_
          have hm : Measurable fun x => ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q :=
            ((hgmeas.comp (measurable_id.sub_const _)).sub hgmeas).enorm.pow_const q
          have hsm : AEStronglyMeasurable (fun x => g (x - c⁻¹ • z) - g x) μ :=
            ((hgm.comp_measurable (measurable_id.sub_const _)).sub hgm).aestronglyMeasurable
          rw [lintegral_const_mul _ hm]
          congr 1
          exact (eLpNorm_rpow_eq hsm hp0 hp).symm
  -- dominated convergence for `I`
  have hI : Tendsto I atTop (𝓝 0) := by
    have hlim := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := μ) (l := atTop) (F := fun (c : ℝ) z => ‖Φ z‖ₑ * T (c⁻¹ • z) ^ q)
      (f := fun _ => 0) (fun z => ‖Φ z‖ₑ * (2 * eLpNorm g p μ) ^ q)
      (Eventually.of_forall fun c => hΦ.aestronglyMeasurable.enorm.mul
        ((hT.measurable.comp (measurable_const_smul c⁻¹)).pow_const q).aemeasurable)
      (Eventually.of_forall fun c => Eventually.of_forall fun z => by
        gcongr
        calc T (c⁻¹ • z) ≤ eLpNorm (fun x => g (x - c⁻¹ • z)) p μ + eLpNorm g p μ :=
              eLpNorm_sub_le hp1
          _ = 2 * eLpNorm g p μ := by
              rw [eLpNorm_comp_sub_right hgm.aestronglyMeasurable, two_mul])
      (by
        rw [lintegral_mul_const'' _ hΦ.aestronglyMeasurable.enorm]
        exact ENNReal.mul_ne_top hΦ1 (ENNReal.rpow_ne_top_of_nonneg hq.le
          (ENNReal.mul_ne_top (by simp) hg.eLpNorm_ne_top)))
      (Eventually.of_forall fun z => by
        have h0 : Tendsto (fun c : ℝ => c⁻¹ • z) atTop (𝓝 0) := by
          have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const z
          rwa [zero_smul ℝ z] at this
        have h2 : Tendsto (fun c : ℝ => T (c⁻¹ • z)) atTop (𝓝 0) := by
          have := (hT.tendsto 0).comp h0
          rwa [hT0] at this
        have h1' : Tendsto (fun c : ℝ => T (c⁻¹ • z) ^ q) atTop (𝓝 0) := by
          have := ((ENNReal.continuous_rpow_const (y := q)).tendsto 0).comp h2
          rwa [ENNReal.zero_rpow_of_pos hq] at this
        have := ENNReal.Tendsto.const_mul (a := ‖Φ z‖ₑ) h1' (Or.inr enorm_ne_top)
        rwa [mul_zero] at this)
    rwa [lintegral_zero] at hlim
  -- conclusion
  have hlim2 : Tendsto (fun c => ((∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) * I c) ^ (1 / q)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun c => (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) * I c) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1)) hI
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by linarith) hΦ1))
      rwa [mul_zero] at this
    have := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto 0).comp h3
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.2 hq)] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim2
    (Eventually.of_forall fun _ => zero_le)
    ((eventually_gt_atTop 0).mono fun c hc => hbound c hc)

/-- **Approximate identities as operators on `L_p`**: for an integrable `Φ` with `∫ Φ = 1`,
dilation factors `c_i ≠ 0` with `c_i → ∞` and `f ∈ L_p`, `1 ≤ p < ∞`, `Φ_{c_i} ⋆ f → f` in `L_p`
(Mathlib's `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`). -/
theorem tendsto_convLp_dilate {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {Φ : V → ℂ}
    (hΦ : Integrable Φ μ) (h1 : ∫ x, Φ x ∂μ = 1) {ι : Type*} {l : Filter ι} {c : ι → ℝ}
    (hc : ∀ i, c i ≠ 0) (hcl : Tendsto c l atTop) (f : Lp ℂ p μ) :
    Tendsto (fun i => convLp hp (integrable_dilate hΦ (hc i)) f) l (𝓝 f) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine ((tendsto_eLpNorm_conv_dilate_sub hp hΦ h1 (Lp.memLp f)).comp hcl).congr fun i => ?_
  exact eLpNorm_congr_ae ((convLp_apply_ae hp _ f).sub (Filter.EventuallyEq.refl _ _)).symm

end Rd
