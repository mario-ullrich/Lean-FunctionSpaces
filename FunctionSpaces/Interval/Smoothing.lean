/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.Steklov
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smoothing by Steklov averages

For continuous `f`, `r ≥ 1` and `δ > 0` the **Steklov smoothing**

`S_δ f = ∑_{k=1}^r (-1)^(k+1) C(r,k) M_{kδ}^r f`   (`Interval.smooth`)

is `r` times continuously differentiable, and it is close to `f` in terms of differences:

* `f - S_δ f = (-1)^r avg_{v ∈ [0, δ]^r} Δ^r_{v_1 + ⋯ + v_r} f`, so
  `‖f - S_δ f‖_{L_p(J)} ≤ sup_{0 ≤ h ≤ rδ} ‖Δ_h^r f‖_{L_p(J)}` (`Interval.eLpNorm_sub_smooth_le`);
* `(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r,k) (kδ)^(-r) Δ_{kδ}^r f`, so
  `‖(S_δ f)^(r)‖_{L_p(J)} ≤ 2^r δ^(-r) sup_{0 ≤ h ≤ rδ} ‖Δ_h^r f‖_{L_p(J)}`
  (`Interval.eLpNorm_iteratedDeriv_smooth_le`).

The average over the cube `[0, δ]^r` is built as the `r`-fold average in the step,
`Interval.avgStepIter`, and the `L_p` bound for averages is Minkowski's inequality in the form
`‖δ^(-1) ∫_0^δ K(t, ·) dt‖_p ≤ sup_t ‖K(t, ·)‖_p` (`Interval.eLpNorm_avg_le`), from Hölder's
inequality pointwise and Tonelli's theorem.  Here `1 ≤ p < ∞`.

With `δ = L / r²` the smoothing at `x` looks at `[x, x + L]`. On a left part `[0, w]` of `[0, b]`
with `w + L ≤ b` this gives `‖f - S_δ f‖_p ≤ ω_r(f, L, [0, b])_p` and
`‖(S_δ f)^(r)‖_p ≤ L^(-r) 2^r r^(2r) ω_r(f, L, [0, b])_p`, and with Taylor's theorem polynomial
approximations of `S_δ f` on all subintervals (`Interval.exists_left_smoothing`); the reflection
`x ↦ b - x` gives the same on a right part `[b - w, b]` (`Interval.exists_right_smoothing`).
These are the local estimates behind Jackson's and Whitney's inequalities.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

/-- Averaging a function of `(h, x)` in the step: `δ^(-1) ∫_0^δ G(σ + t, x) dt`. -/
noncomputable def avgStep (δ : ℝ) (G : ℝ → ℝ → ℂ) (σ x : ℝ) : ℂ :=
  ((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, G (σ + t) x

/-- The `m`-fold average in the step. -/
noncomputable def avgStepIter (m : ℕ) (δ : ℝ) (G : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := (avgStep δ)^[m] G

/-- `avgStepIter (m+1) = avgStep ∘ avgStepIter m`. -/
theorem avgStepIter_succ (m : ℕ) (δ : ℝ) (G : ℝ → ℝ → ℂ) :
    avgStepIter (m + 1) δ G = avgStep δ (avgStepIter m δ G) := by
  rw [avgStepIter, Function.iterate_succ_apply']
  rfl

/-- Averages of jointly continuous functions are jointly continuous. -/
theorem continuous_avgStep {G : ℝ → ℝ → ℂ} (hG : Continuous (Function.uncurry G)) (δ : ℝ) :
    Continuous (Function.uncurry (avgStep δ G)) := by
  have hc : Continuous (Function.uncurry fun (q : ℝ × ℝ) (t : ℝ) => G (q.1 + t) q.2) :=
    hG.comp (by fun_prop : Continuous fun p : (ℝ × ℝ) × ℝ => (p.1.1 + p.2, p.1.2))
  have h : Continuous fun q : ℝ × ℝ => ∫ t in (0 : ℝ)..δ, G (q.1 + t) q.2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 δ
  exact continuous_const.mul h

/-- Iterated averages of jointly continuous functions are jointly continuous. -/
theorem continuous_avgStepIter {G : ℝ → ℝ → ℂ} (hG : Continuous (Function.uncurry G))
    (m : ℕ) (δ : ℝ) : Continuous (Function.uncurry (avgStepIter m δ G)) := by
  induction m with
  | zero => exact hG
  | succ m ih => rw [avgStepIter_succ]; exact continuous_avgStep ih δ

/-- `L_p` norms through `L_p` integrals, for `0 < p < ∞`. -/
theorem eLpNorm_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ} (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) : eLpNorm g p μ ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg, one_div,
    ENNReal.rpow_inv_rpow (ENNReal.toReal_pos hp0 hp).ne']

/-- **Hölder's inequality for averages**: `|δ^(-1) ∫_0^δ k|^p ≤ δ^(-1) ∫_0^δ |k|^p`. -/
theorem enorm_avg_rpow_le {k : ℝ → ℂ} (hk : Continuous k) {δ : ℝ} (hδ : 0 < δ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ‖((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, k t‖ₑ ^ p.toReal ≤
      (ENNReal.ofReal δ)⁻¹ * ∫⁻ t in Ioc 0 δ, ‖k t‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  set q := p.toReal
  set D := ENNReal.ofReal δ
  have hD0 : D ≠ 0 := by simpa [D] using hδ
  have hDt : D ≠ ∞ := ENNReal.ofReal_ne_top
  set ν := volume.restrict (Ioc (0 : ℝ) δ)
  have hνu : ν univ = D := by simp [ν, D]
  have hkm : AEStronglyMeasurable k ν := hk.aestronglyMeasurable
  have hinv : ‖((δ : ℂ))⁻¹‖ₑ = D⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
      ENNReal.ofReal_inv_of_pos hδ]
  have h1 : ‖∫ t in (0 : ℝ)..δ, k t‖ₑ ≤ eLpNorm k p ν * D ^ (1 - 1 / q) := by
    rw [intervalIntegral.integral_of_le hδ.le]
    calc ‖∫ t in Ioc 0 δ, k t‖ₑ ≤ ∫⁻ t in Ioc 0 δ, ‖k t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm k 1 ν := (eLpNorm_one_eq_lintegral_enorm hkm).symm
      _ ≤ eLpNorm k p ν * ν univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / q) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hkm
      _ = eLpNorm k p ν * D ^ (1 - 1 / q) := by rw [hνu, ENNReal.toReal_one, div_one]
  rw [enorm_mul, hinv]
  calc (D⁻¹ * ‖∫ t in (0 : ℝ)..δ, k t‖ₑ) ^ q
      ≤ (D⁻¹ * (eLpNorm k p ν * D ^ (1 - 1 / q))) ^ q := by gcongr
    _ = D⁻¹ ^ q * D ^ ((1 - 1 / q) * q) * eLpNorm k p ν ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          ← ENNReal.rpow_mul]
        ring
    _ = D⁻¹ * ∫⁻ t in Ioc 0 δ, ‖k t‖ₑ ^ q := by
        rw [eLpNorm_rpow_eq hkm hp0 hp', ENNReal.inv_rpow, ← ENNReal.rpow_neg,
          ← ENNReal.rpow_add _ _ hD0 hDt, show -q + (1 - 1 / q) * q = -1 by field_simp; ring,
          ENNReal.rpow_neg_one]

/-- **Minkowski's inequality for averages**: for jointly continuous `K`, `δ > 0` and
`1 ≤ p < ∞`, `‖δ^(-1) ∫_0^δ K(t, ·) dt‖_{L_p(μ)} ≤ sup_{0 ≤ t ≤ δ} ‖K(t, ·)‖_{L_p(μ)}`. -/
theorem eLpNorm_avg_le {K : ℝ → ℝ → ℂ} (hK : Continuous (Function.uncurry K)) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (s : Set ℝ) :
    eLpNorm (fun x => ((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, K t x) p (volume.restrict s) ≤
      ⨆ t ∈ Icc 0 δ, eLpNorm (K t) p (volume.restrict s) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hD0 : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
  have hDt : ENNReal.ofReal δ ≠ ∞ := ENNReal.ofReal_ne_top
  have hKx : ∀ x, Continuous fun t => K t x := fun x =>
    hK.comp (continuous_id.prodMk continuous_const)
  have hKt : ∀ t, Continuous (K t) := fun t => hK.comp (continuous_const.prodMk continuous_id)
  have hswap : Continuous (Function.uncurry fun (x t : ℝ) => K t x) :=
    hK.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2, p.1))
  have havg : Continuous fun x => ((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, K t x :=
    continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hswap 0 δ)
  have hmeas : Measurable (Function.uncurry fun (x t : ℝ) => ‖K t x‖ₑ ^ p.toReal) :=
    hswap.measurable.enorm.pow_const p.toReal
  have hB : ∀ t ∈ Icc 0 δ, ∫⁻ x, ‖K t x‖ₑ ^ p.toReal ∂volume.restrict s ≤
      (⨆ t ∈ Icc 0 δ, eLpNorm (K t) p (volume.restrict s)) ^ p.toReal := fun t ht => by
    rw [← eLpNorm_rpow_eq (hKt t).aestronglyMeasurable hp0 hp']
    exact ENNReal.rpow_le_rpow
      (le_iSup₂ (f := fun t (_ : t ∈ Icc 0 δ) => eLpNorm (K t) p (volume.restrict s)) t ht) hq.le
  have hint : ∫⁻ x, ‖((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, K t x‖ₑ ^ p.toReal ∂volume.restrict s ≤
      (⨆ t ∈ Icc 0 δ, eLpNorm (K t) p (volume.restrict s)) ^ p.toReal := by
    calc ∫⁻ x, ‖((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, K t x‖ₑ ^ p.toReal ∂volume.restrict s
        ≤ ∫⁻ x, (ENNReal.ofReal δ)⁻¹ * (∫⁻ t in Ioc 0 δ, ‖K t x‖ₑ ^ p.toReal)
            ∂volume.restrict s :=
          lintegral_mono fun x => enorm_avg_rpow_le (hKx x) hδ hp hp'
      _ = (ENNReal.ofReal δ)⁻¹ * ∫⁻ t in Ioc 0 δ, ∫⁻ x, ‖K t x‖ₑ ^ p.toReal ∂volume.restrict s := by
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hD0)]
          congr 1
          exact lintegral_lintegral_swap
            (hmeas.aemeasurable (μ := (volume.restrict s).prod (volume.restrict (Ioc 0 δ))))
      _ ≤ (ENNReal.ofReal δ)⁻¹ *
            ∫⁻ _ in Ioc 0 δ, (⨆ t ∈ Icc 0 δ, eLpNorm (K t) p (volume.restrict s)) ^ p.toReal :=
          mul_le_mul_right (setLIntegral_mono measurable_const
            fun t ht => hB t (Ioc_subset_Icc_self ht)) _
      _ = (⨆ t ∈ Icc 0 δ, eLpNorm (K t) p (volume.restrict s)) ^ p.toReal := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm _ (ENNReal.ofReal δ),
            ← mul_assoc, ENNReal.inv_mul_cancel hD0 hDt, one_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' havg.aestronglyMeasurable]
  calc (∫⁻ x, ‖((δ : ℂ))⁻¹ * ∫ t in (0 : ℝ)..δ, K t x‖ₑ ^ p.toReal ∂volume.restrict s) ^ (1 / p.toReal)
      ≤ ((⨆ t ∈ Icc 0 δ, eLpNorm (K t) p (volume.restrict s)) ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = ⨆ t ∈ Icc 0 δ, eLpNorm (K t) p (volume.restrict s) := by rw [one_div, ENNReal.rpow_rpow_inv hq.ne']

/-- **Iterated averages are bounded by the sup over the steps**:
`‖avg^m G(σ, ·)‖_{L_p(μ)} ≤ sup_{σ ≤ h ≤ σ + mδ} ‖G(h, ·)‖_{L_p(μ)}`. -/
theorem eLpNorm_avgStepIter_le {G : ℝ → ℝ → ℂ} (hG : Continuous (Function.uncurry G)) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (s : Set ℝ) (m : ℕ) (σ : ℝ) :
    eLpNorm (avgStepIter m δ G σ) p (volume.restrict s) ≤
      ⨆ h ∈ Icc σ (σ + m * δ), eLpNorm (G h) p (volume.restrict s) := by
  induction m generalizing σ with
  | zero =>
    exact le_iSup₂ (f := fun h (_ : h ∈ Icc σ (σ + (0 : ℕ) * δ)) =>
      eLpNorm (G h) p (volume.restrict s)) σ
      ⟨le_rfl, by simp⟩
  | succ m ih =>
    rw [avgStepIter_succ]
    have hK : Continuous (Function.uncurry fun t x => avgStepIter m δ G (σ + t) x) :=
      (continuous_avgStepIter hG m δ).comp
        (by fun_prop : Continuous fun p : ℝ × ℝ => (σ + p.1, p.2))
    refine (eLpNorm_avg_le hK hδ hp hp' s).trans (iSup₂_le fun t ht => (ih (σ + t)).trans ?_)
    refine iSup₂_le fun h hh => le_iSup₂_of_le h ⟨?_, ?_⟩ le_rfl
    · linarith [ht.1, hh.1]
    · have := hh.2; push_cast at this ⊢; nlinarith [ht.2]

/-- Averaging a function of `x` alone changes nothing. -/
theorem avgStepIter_const (g : ℝ → ℂ) {δ : ℝ} (hδ : δ ≠ 0) (m : ℕ) :
    avgStepIter m δ (fun _ x => g x) = fun _ x => g x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [avgStepIter_succ, ih]
    funext σ x
    have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
    simp only [avgStep, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    field_simp

/-- **Averaged translates are Steklov averages**: averaging `g(x + k h)` `m` times in the step
gives `M_{kδ}^m g(x + kσ)`, for `k ≥ 1`. -/
theorem avgStepIter_shift (g : ℝ → ℂ) {k : ℕ} (hk : 1 ≤ k) (δ : ℝ) (m : ℕ) :
    avgStepIter m δ (fun h x => g (x + k * h)) =
      fun σ x => steklovIter m (k * δ) g (x + k * σ) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [avgStepIter_succ, ih]
    funext σ x
    rw [steklovIter_succ, steklov]
    simp only [avgStep]
    have hsub : ∫ t in (0 : ℝ)..δ, steklovIter m (k * δ) g (x + k * (σ + t)) =
        (k : ℝ)⁻¹ • ∫ τ in (0 : ℝ)..k * δ, steklovIter m (k * δ) g (x + k * σ + τ) := by
      calc ∫ t in (0 : ℝ)..δ, steklovIter m (k * δ) g (x + k * (σ + t))
          = ∫ t in (0 : ℝ)..δ, (fun τ => steklovIter m (k * δ) g (x + k * σ + τ)) (k * t) := by
            congr 1
            funext t
            simp only
            congr 1
            ring
        _ = (k : ℝ)⁻¹ • ∫ τ in (k : ℝ) * 0..(k : ℝ) * δ,
              steklovIter m (k * δ) g (x + k * σ + τ) :=
            intervalIntegral.integral_comp_mul_left
              (fun τ => steklovIter m (k * δ) g (x + k * σ + τ)) hk0
        _ = _ := by rw [mul_zero]
    rw [hsub, Complex.real_smul]
    push_cast
    field_simp

/-- Averages of finite linear combinations. -/
theorem avgStepIter_sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℝ → ℂ}
    (hG : ∀ i ∈ s, Continuous (Function.uncurry (G i))) (c : ι → ℂ) (δ : ℝ) (m : ℕ) :
    avgStepIter m δ (fun h x => ∑ i ∈ s, c i * G i h x) =
      fun σ x => ∑ i ∈ s, c i * avgStepIter m δ (G i) σ x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [avgStepIter_succ, ih]
    funext σ x
    simp only [avgStep, avgStepIter_succ]
    have hint : ∀ i ∈ s, IntervalIntegrable (fun t => c i * avgStepIter m δ (G i) (σ + t) x)
        volume 0 δ := fun i hi => by
      have hcI : Continuous fun t => avgStepIter m δ (G i) (σ + t) x :=
        (continuous_avgStepIter (hG i hi) m δ).comp
          (by fun_prop : Continuous fun t : ℝ => (σ + t, x))
      exact (hcI.const_mul (c i)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hint]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [intervalIntegral.integral_const_mul]
    ring

/-- The **Steklov smoothing** `S_δ f = ∑_{k=1}^r (-1)^(k+1) C(r,k) M_{kδ}^r f`. -/
noncomputable def smooth (r : ℕ) (δ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range r, ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
    steklovIter r ((k + 1 : ℕ) * δ) f x

/-- **`f - S_δ f` is an averaged difference**:
`f - S_δ f = (-1)^r avg^r_{h} Δ_h^r f` at step `0`. -/
theorem sub_smooth_eq {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (x : ℝ) :
    f x - smooth r δ f x =
      (-1 : ℂ) ^ r * avgStepIter r δ (fun h y => iterDiff r h f y) 0 x := by
  have hrepr : (fun h y => iterDiff r h f y) = fun h y => ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (y + k * h) :=
    funext fun h => funext fun y => iterDiff_apply r h f y
  have hcont : ∀ k ∈ Finset.range (r + 1),
      Continuous (Function.uncurry fun (h y : ℝ) => f (y + k * h)) := fun k _ =>
    hf.comp (by fun_prop)
  rw [hrepr, avgStepIter_sum _ hcont]
  simp only
  rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
  have h0 : avgStepIter r δ (fun (h y : ℝ) => f (y + ((0 : ℕ) : ℝ) * h)) 0 x = f x := by
    have : (fun (h y : ℝ) => f (y + ((0 : ℕ) : ℝ) * h)) = fun _ y => f y := by
      funext h y; simp
    rw [this, avgStepIter_const f hδ]
  rw [h0]
  have hk : ∀ k ∈ Finset.range r, avgStepIter r δ (fun (h y : ℝ) => f (y + ((k + 1 : ℕ) : ℝ) * h))
      0 x = steklovIter r ((k + 1 : ℕ) * δ) f x := fun k _ => by
    rw [avgStepIter_shift f (by omega) δ]
    simp
  rw [Finset.sum_congr rfl fun k hk' => by rw [hk k hk'], smooth]
  have hsign : ∀ k ∈ Finset.range r, (-1 : ℂ) ^ r * (((-1 : ℂ) ^ (r - (k + 1)) *
      (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x) =
      -(((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x) :=
    fun k hk' => by
      have hkr : k + 1 ≤ r := Finset.mem_range.1 hk'
      have : (-1 : ℂ) ^ r = (-1) ^ (r - (k + 1)) * (-1) ^ (k + 1) := by
        rw [← pow_add, Nat.sub_add_cancel hkr]
      rw [this]
      have h2 : ((-1 : ℂ) ^ (r - (k + 1))) * (-1) ^ (r - (k + 1)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      calc (-1 : ℂ) ^ (r - (k + 1)) * (-1) ^ (k + 1) * ((-1) ^ (r - (k + 1)) *
            ↑(r.choose (k + 1)) * steklovIter r (↑(k + 1) * δ) f x)
          = ((-1 : ℂ) ^ (r - (k + 1)) * (-1) ^ (r - (k + 1))) * (-1) ^ (k + 1) *
              (↑(r.choose (k + 1)) * steklovIter r (↑(k + 1) * δ) f x) := by ring
        _ = _ := by rw [h2, pow_succ (-1 : ℂ) (k + 1)]; ring
  rw [Finset.sum_congr rfl hsign, Finset.sum_neg_distrib]
  have hr0 : (-1 : ℂ) ^ r * ((-1 : ℂ) ^ (r - 0) * (r.choose 0 : ℂ) * f x) = f x := by
    rw [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul]
    simp
  rw [hr0]
  ring

/-- The Steklov smoothing of a continuous function lies in `C^r`. -/
theorem contDiff_smooth {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ) :
    ContDiff ℝ r (smooth r δ f) := by
  show ContDiff ℝ r fun x => ∑ k ∈ Finset.range r,
    ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x
  exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_steklovIter hf r _)

/-- **The derivative of order `r` of the smoothing is a combination of differences**:
`(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r,k) (kδ)^(-r) Δ_{kδ}^r f`. -/
theorem iteratedDeriv_smooth {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ) :
    iteratedDeriv r (smooth r δ f) = fun x => ∑ k ∈ Finset.range r,
      ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        ((((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r * iterDiff r ((k + 1 : ℕ) * δ) f x) := by
  have : smooth r δ f = ∑ k ∈ Finset.range r, fun x =>
      ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) * steklovIter r ((k + 1 : ℕ) * δ) f x := by
    funext x; simp [smooth, Finset.sum_apply]
  rw [this]
  funext x
  rw [iteratedDeriv_sum fun k _ =>
    (contDiff_const.mul (contDiff_steklovIter hf r _)).contDiffAt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_steklovIter hf]

/-- Differences of a continuous function are jointly continuous in the step and the point. -/
theorem continuous_iterDiff_uncurry {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) :
    Continuous (Function.uncurry fun (h y : ℝ) => iterDiff r h f y) := by
  have : (Function.uncurry fun (h y : ℝ) => iterDiff r h f y) = fun q : ℝ × ℝ =>
      ∑ k ∈ Finset.range (r + 1), ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (q.2 + k * q.1) :=
    funext fun q => iterDiff_apply r q.1 f q.2
  rw [this]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hf.comp (by fun_prop))

/-- **The smoothing is close to `f`**: for `[u, w]` with `a ≤ u` and `w + r² δ ≤ b`,
`‖f - S_δ f‖_{L_p[u, w]} ≤ ω_r(f, rδ, [a, b])_p`. -/
theorem eLpNorm_sub_smooth_le {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {a b u w : ℝ} (hau : a ≤ u)
    (hwb : w + r * (r * δ) ≤ b) :
    eLpNorm (fun x => f x - smooth r δ f x) p (volume.restrict (Icc u w)) ≤
      modulus r p a b f (r * δ) := by
  have heq : (fun x => f x - smooth r δ f x) = ((-1 : ℂ) ^ r) •
      avgStepIter r δ (fun h y => iterDiff r h f y) 0 := by
    funext x
    rw [sub_smooth_eq hf r hδ.ne' x]
    rfl
  rw [heq, eLpNorm_const_smul, enorm_pow, enorm_neg, enorm_one, one_pow, one_mul]
  refine (eLpNorm_avgStepIter_le (continuous_iterDiff_uncurry hf r) hδ hp hp' _ r 0).trans ?_
  refine iSup₂_le fun h hh => ?_
  rw [zero_add] at hh
  refine (eLpNorm_Icc_mono _ p hau ?_).trans (eLpNorm_iterDiff_le_modulus ⟨hh.1, hh.2⟩)
  have : (r : ℝ) * h ≤ r * (r * δ) := mul_le_mul_of_nonneg_left hh.2 (Nat.cast_nonneg r)
  linarith

/-- **The derivative of order `r` of the smoothing**: for `[u, w]` with `a ≤ u` and
`w + r² δ ≤ b`, `‖(S_δ f)^(r)‖_{L_p[u, w]} ≤ 2^r δ^(-r) ω_r(f, rδ, [a, b])_p`. -/
theorem eLpNorm_iteratedDeriv_smooth_le {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) {a b u w : ℝ} (hau : a ≤ u)
    (hwb : w + r * (r * δ) ≤ b) :
    eLpNorm (iteratedDeriv r (smooth r δ f)) p (volume.restrict (Icc u w)) ≤
      2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * modulus r p a b f (r * δ) := by
  rw [iteratedDeriv_smooth hf r δ]
  have hsum : (fun x => ∑ k ∈ Finset.range r, ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
      ((((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r * iterDiff r ((k + 1 : ℕ) * δ) f x)) =
      ∑ k ∈ Finset.range r, (((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • iterDiff r ((k + 1 : ℕ) * δ) f := by
    funext x
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum]
  refine (eLpNorm_sum_le hp).trans ?_
  have hk : ∀ k ∈ Finset.range r, eLpNorm ((((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
      (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • iterDiff r ((k + 1 : ℕ) * δ) f) p
        (volume.restrict (Icc u w)) ≤
      (r.choose (k + 1) : ℝ≥0∞) * ((ENNReal.ofReal δ)⁻¹ ^ r * modulus r p a b f (r * δ)) :=
    fun k hk => by
      have hkr : ((k + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Finset.mem_range.1 hk
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      rw [eLpNorm_const_smul, enorm_mul, enorm_mul, enorm_pow, enorm_neg, enorm_one, one_pow,
        one_mul, mul_assoc]
      gcongr
      · rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
      · rw [enorm_pow, ← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
        gcongr
        exact le_mul_of_one_le_left hδ.le hk1
      · refine (eLpNorm_Icc_mono _ p hau ?_).trans
          (eLpNorm_iterDiff_le_modulus ⟨by positivity, ?_⟩)
        · have : (r : ℝ) * ((k + 1 : ℕ) * δ) ≤ r * (r * δ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkr hδ.le) (Nat.cast_nonneg r)
          linarith
        · exact mul_le_mul_of_nonneg_right hkr hδ.le
  refine (Finset.sum_le_sum hk).trans ?_
  rw [← Finset.sum_mul, mul_assoc]
  gcongr
  have h2 : ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ≥0∞) ≤ 2 ^ r := by
    have := Nat.sum_range_choose r
    rw [Finset.sum_range_succ'] at this
    have h' : ∑ k ∈ Finset.range r, r.choose (k + 1) ≤ 2 ^ r := by omega
    exact_mod_cast h'
  exact h2

/-- **Smoothing on a left part**: for continuous `F`, `r ≥ 1`, a scale `L > 0` and `w + L ≤ b`,
the Steklov smoothing `g = S_δ F`, `δ = L/r²`, and its derivative `D = g^(r)` satisfy
`‖F - g‖_{L_p[0,w]} ≤ ω_r(F, L, [0, b])_p` and
`‖D‖_{L_p[0,w]} ≤ L^(-r) 2^r r^(2r) ω_r(F, L, [0, b])_p`, and for every `u ≤ v` there is `T` of
degree `< r` with `‖g - T‖_{L_p[u,v]} ≤ (v - u)^r ‖D‖_{L_p[u,v]}` (Taylor). -/
theorem exists_left_smoothing {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {b L w : ℝ} (hL : 0 < L) (hwL : w + L ≤ b) :
    ∃ g D : ℝ → ℂ, Measurable g ∧ Measurable D ∧
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc 0 w)) ≤ modulus r p 0 b F L ∧
      eLpNorm D p (volume.restrict (Icc 0 w)) ≤
        ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * modulus r p 0 b F L ∧
      ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc u v)) ≤
          ENNReal.ofReal (v - u) ^ r * eLpNorm D p (volume.restrict (Icc u v)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set δ : ℝ := L / r ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hrδ : (r : ℝ) * δ ≤ L := by
    rw [hδdef, show (r : ℝ) * (L / r ^ 2) = L / r by field_simp]
    exact div_le_self hL.le (by exact_mod_cast hr)
  have hrrδ : (r : ℝ) * (r * δ) = L := by rw [hδdef]; field_simp
  have hwb : w + r * (r * δ) ≤ b := by rw [hrrδ]; exact hwL
  have hg := contDiff_smooth hF r δ
  refine ⟨smooth r δ F, iteratedDeriv r (smooth r δ F), hg.continuous.measurable,
    (hg.continuous_iteratedDeriv r le_rfl).measurable, ?_, ?_, fun u v huv =>
      exists_eLpNorm_sub_polyFun_le hp r hg huv⟩
  · exact (eLpNorm_sub_smooth_le hF r hδ hp hp' le_rfl hwb).trans (modulus_mono r p 0 b F hrδ)
  · refine (eLpNorm_iteratedDeriv_smooth_le hF r hδ hp le_rfl hwb).trans ?_
    have hinv : (ENNReal.ofReal δ)⁻¹ = (r : ℝ≥0∞) ^ 2 * ENNReal.ofReal L⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos hδ, hδdef, show (L / (r : ℝ) ^ 2)⁻¹ = (r : ℝ) ^ 2 * L⁻¹ by
        field_simp, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg r),
        ENNReal.ofReal_natCast]
    rw [hinv, mul_pow, ← pow_mul]
    calc 2 ^ r * ((r : ℝ≥0∞) ^ (2 * r) * ENNReal.ofReal L⁻¹ ^ r) * modulus r p 0 b F (r * δ)
        ≤ 2 ^ r * ((r : ℝ≥0∞) ^ (2 * r) * ENNReal.ofReal L⁻¹ ^ r) * modulus r p 0 b F L := by
          gcongr
          exact modulus_mono r p 0 b F hrδ
      _ = _ := by ring

/-- **Smoothing on a right part**: the same on `[b - w, b]`, by the reflection `x ↦ b - x`, which
preserves the modulus on `[0, b]` (`Interval.modulus_reflect`). -/
theorem exists_right_smoothing {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {b L w : ℝ} (hL : 0 < L) (hwL : w + L ≤ b) :
    ∃ g D : ℝ → ℂ, Measurable g ∧ Measurable D ∧
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc (b - w) b)) ≤ modulus r p 0 b F L ∧
      eLpNorm D p (volume.restrict (Icc (b - w) b)) ≤
        ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * modulus r p 0 b F L ∧
      ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc u v)) ≤
          ENNReal.ofReal (v - u) ^ r * eLpNorm D p (volume.restrict (Icc u v)) := by
  have hF' : Continuous fun x => F (b - x) := hF.comp (continuous_const.sub continuous_id)
  obtain ⟨G, DG, hGm, hDm, h1, h2, h3⟩ := exists_left_smoothing hF' hr hp hp' hL hwL
  have hmod : modulus r p 0 b (fun x => F (b - x)) L = modulus r p 0 b F L := by
    simpa using modulus_reflect hF.measurable r p 0 b L
  rw [hmod] at h1 h2
  refine ⟨fun x => G (b - x), fun x => DG (b - x), hGm.comp (measurable_const.sub measurable_id),
    hDm.comp (measurable_const.sub measurable_id), ?_, ?_, fun u v huv => ?_⟩
  · have h := eLpNorm_comp_sub_Icc (f := fun y => F (b - y) - G y)
      ((hF'.measurable).sub hGm) p b (b - w) b
    simp only [sub_sub_cancel, sub_self] at h
    rw [h]
    exact h1
  · have h := eLpNorm_comp_sub_Icc hDm p b (b - w) b
    simp only [sub_sub_cancel, sub_self] at h
    rw [h]
    exact h2
  · obtain ⟨T, hT, hTb⟩ := h3 (b - v) (b - u) (by linarith)
    refine ⟨T.comp (C ((b : ℝ) : ℂ) + C (((-1 : ℝ) : ℝ) : ℂ) * X),
      comp_affine_mem_degreeLT hT _ _, ?_⟩
    have hfun : (fun x => G (b - x) - polyFun (T.comp (C ((b : ℝ) : ℂ) +
        C (((-1 : ℝ) : ℝ) : ℂ) * X)) x) = fun x => (fun y => G y - polyFun T y) (b - x) := by
      funext x
      rw [polyFun_comp_affine]
      congr 2
      ring
    rw [hfun, eLpNorm_comp_sub_Icc (f := fun y => G y - polyFun T y)
      (hGm.sub (measurable_polyFun T)) p b u v, eLpNorm_comp_sub_Icc hDm p b u v]
    rw [show (b - u) - (b - v) = v - u by ring] at hTb
    exact hTb

end Interval
