/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Lp.MixedNorms
public import FunctionSpaces.Wavelets.Examples.DyadicStepsQuasiBanach
public import FunctionSpaces.Wavelets.Examples.HaarBasis

/-!
# The Haar system in `L_p[0, 1]`, `0 < p ≤ 1`

For `0 < p ≤ 1` the approximation spaces `E_{s,q}` of the step couple `Haar.stepCouple p`
(approximation by dyadic step functions in the quasi-Banach space `L_p[0, 1]`) are described by
Haar coefficients when `s > 1/p - 1`. The step couple is the couple in `L_p` of the Haar scheme
of essentially bounded functions on `[0, 1]` (`Haar.stepCouple_eq_lpCouple`).

* **The Nikolskii inequality of steps**: for every `0 < p ≤ ∞`, a step function `a` of level `j`
  has `‖a‖_∞ ≤ 2^(j/p) ‖a‖_p` (`Haar.eLpNorm_top_le_of_mem_lpMeas`), and hence
  `‖a‖_r ≤ 2^(j(1/p - 1/r)) ‖a‖_p` for every `p ≤ r ≤ ∞` (`Haar.eLpNorm_le_of_mem_lpMeas`).
* **Steps lie in `L_1`**: for `p ≤ 1` the case `r = 1` is
  `‖a‖_1 ≤ 2^(j(1/p - 1)) ‖a‖_p` (`Haar.eLpNorm_one_le_of_mem_lpMeas`); the bound holds also
  locally on every union of dyadic intervals of level `j`
  (`Haar.setLIntegral_enorm_le_of_dyadicIndex`).
* **The approximation spaces embed into `L_1` for `s > 1/p - 1`**: near-best steps `b_j` converge
  in measure to `f` (`Haar.tendstoInMeasure_of_nearBest`), and Fatou's lemma for telescoping sums
  (`MeasureTheory.eLpNorm_sub_rpow_le_tsum`) adds their differences in `L_1`, so
  `‖f‖_1 ≤ C (‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q})` (`Haar.eLpNorm_one_le_eNormDyadic`).
* **The level norms** `H_k(f) = 2^(k(1/2 - 1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p}`
  (`Haar.haarLevelNorm`), the quasi-norms of the martingale differences
  (`Haar.haarLevelNorm_eq_eLpNorm`), are `p`-subadditive, at most `2^k ‖f‖_1`, and for a step of
  level `j ≥ k` at most `2^((j-k)(1/p - 1)) ‖a‖_p` (`Haar.haarLevelNorm_le_of_mem_lpMeas`).
* **Martingale convergence in `L_1`**: `E[f | ℱ_N] → f` for integrable `f`
  (`Haar.tendsto_eLpNorm_condExp_sub`), so an integrable function is determined by its Haar
  coefficients (`Haar.ae_eq_zero_of_haarCoeff_eq_zero`) and
  `‖f - E[f | ℱ_k]‖_p^p ≤ ∑_{j ≥ k} H_j(f)^p` (`Haar.eLpNorm_sub_condExp_rpow_le_tsum`).

Hardy's inequality for tails in `ℓ_{q/p}` (`ENNReal.lqNorm_rpow_le_of_rpow_le_tsum`) turns these
bounds into the **coefficient characterisation** (`Haar.memEMethod_stepCouple_iff_haarCoeff`): for
`0 < p ≤ 1`, `s > 1/p - 1` and `q ≠ 0`,

`f ∈ E_{s,q}  ⟺  f ∈ L_1, |∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_m‖_{ℓ_p})_k‖_{ℓ_q} < ∞`,

and with the first modulus for `1/p - 1 < s < 1/p` (`Haar.memEMethod_stepCouple_iff_modulus`) the
description of `B^s_{p,q,1}[0, 1]` by Haar coefficients
(`Haar.lqNorm_modulus_lt_top_iff_haarCoeff_of_le_one`). This is the description by Haar
coefficients behind the Schauder basis property of the Haar system in these spaces for `d = 1`
(`Haar.tendsto_eNormDyadic_sub_haarPartialSum`), which is due to P. Oswald, *On inequalities for
spline approximation and spline systems in the space `L_p` (`0 < p < 1`)*, Approximation and
Function Spaces (Gdańsk 1979), 1981; see Oswald, *Haar system as Schauder basis in Besov spaces:
The limiting cases for `0 < p ≤ 1`*, arXiv:1808.08156, §1 and Theorem 1. The condition
`s > 1/p - 1` cannot be dropped: for `0 < s < 1/p - 1` and `q < ∞`, `B^s_{p,q,1}[0, 1]` has a
trivial dual (Oswald 2018, §1 and Theorem 1 (i)); the limiting case `s = 1/p - 1` is the subject
of Oswald 2018.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open ENNReal (dyadicWeight lqNorm)

namespace Haar

variable {p : ℝ≥0∞}

/-! ### Functions of the dyadic σ-algebras -/

/-- A function measurable for the dyadic σ-algebra `ℱ_j` is constant on the dyadic intervals of
level `j`. -/
theorem eq_of_dyadicIndex_eq {j : ℕ} {g : ℝ → ℂ} (hg : StronglyMeasurable[dyadicFiltration j] g)
    {x y : ℝ} (h : dyadicIndex j x = dyadicIndex j y) : g x = g y := by
  have hg' : StronglyMeasurable[MeasurableSpace.comap (dyadicIndex j) ⊤] g := hg
  exact hg'.eq_of_comap_top h

/-- A function measurable for `ℱ_j` lies in `L_r[0, 1]` for every `r`: on `[0, 1]` it is a step
function with `2^j` values (`Haar.ae_eq_ppFun_of_stronglyMeasurable`). -/
theorem memLp_of_stronglyMeasurable_dyadicFiltration {j : ℕ} {g : ℝ → ℂ}
    (hg : StronglyMeasurable[dyadicFiltration j] g) (r : ℝ≥0∞) : MemLp g r vol :=
  (Interval.memLp_ppFun j _ r).ae_eq (ae_eq_ppFun_of_stronglyMeasurable hg).symm

/-- An `ℱ_j`-measurable element of `L_p[0, 1]` lies in `L_r[0, 1]` for every `r`. -/
theorem memLp_of_mem_lpMeas {j : ℕ} {a : Lp ℂ p vol}
    (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) (r : ℝ≥0∞) : MemLp a r vol := by
  obtain ⟨g, hg, hag⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 ha
  exact (memLp_of_stronglyMeasurable_dyadicFiltration hg r).ae_eq hag.symm

/-- The `ℱ_j`-measurable elements of `L_p[0, 1]` are `ℱ_k`-measurable for `j ≤ k`. -/
theorem mem_lpMeas_of_le {j k : ℕ} (hjk : j ≤ k) {a : Lp ℂ p vol}
    (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) :
    a ∈ lpMeas ℂ ℝ (dyadicFiltration k) p vol := by
  obtain ⟨g, hg, hag⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 ha
  exact mem_lpMeas_iff_aestronglyMeasurable.2 ⟨g, hg.mono (dyadicFiltration.mono hjk), hag⟩

/-- Over the dyadic intervals of level `k` in `[0, 1)` the integrals of `F ≥ 0` add up to the
integral over `[0, 1]`. -/
theorem sum_setLIntegral_haarDyadicInterval (F : ℝ → ℝ≥0∞) (k : ℕ) :
    ∑ m : Fin (2 ^ k), ∫⁻ x in haarDyadicInterval k ((m : ℕ) : ℤ), F x ∂vol = ∫⁻ x, F x ∂vol := by
  rw [show (∫⁻ x, F x ∂vol) = ∫⁻ x in Icc (0 : ℝ) 1, F x from rfl,
    Interval.lintegral_unit_eq_sum_dyadicIco F k, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [haarDyadicInterval_natCast, Measure.restrict_restrict (Interval.measurableSet_dyadicIco _ _),
    inter_eq_left.2 ((Interval.dyadicIco_subset m.isLt).trans Ico_subset_Icc_self)]

/-! ### Steps of level `j` in `L_1` and `L_∞` -/

/-- **A step by its integral around a point**: let `x ∈ [0, 1)`, let `F ≥ 0` be constant on the
dyadic interval of level `j` containing `x`, and let `S` contain that interval. Then
`F(x) ≤ 2^j ∫_S F`, since the integral of `F` over that interval is `F(x) 2^(-j)`. -/
theorem le_dyadicWeight_mul_setLIntegral_of_dyadicIndex {j : ℕ} {F : ℝ → ℝ≥0∞} {S : Set ℝ}
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hF : ∀ y ∈ haarDyadicInterval j (dyadicIndex j x), F y = F x)
    (hS : haarDyadicInterval j (dyadicIndex j x) ⊆ S) :
    F x ≤ dyadicWeight 1 j * ∫⁻ y in S, F y ∂vol := by
  have hI : ∫⁻ y in haarDyadicInterval j (dyadicIndex j x), F y ∂vol =
      F x * dyadicWeight (-1) j := by
    rw [setLIntegral_congr_fun (measurableSet_haarDyadicInterval _ _) hF,
      setLIntegral_const, vol_haarDyadicInterval (dyadicIndex_nonneg hx) (dyadicIndex_lt hx)]
  calc F x = dyadicWeight 1 j * (F x * dyadicWeight (-1) j) := by
        rw [mul_left_comm, ENNReal.dyadicWeight_mul_neg_self, mul_one]
    _ ≤ dyadicWeight 1 j * ∫⁻ y in S, F y ∂vol := by
        gcongr
        exact hI ▸ lintegral_mono_set hS

/-- **Steps in `L_1`, locally**: let `0 < p ≤ 1` and let `G` be constant on the dyadic intervals
of level `j`. On a measurable set `S` that is a union of such intervals,
`∫_S |G| ≤ 2^(j(1/p - 1)) (∫_S |G|^p)^(1/p)`. On `[0, 1)`, `|G(x)|^p 2^(-j)` is the integral of
`|G|^p` over the interval of `x`, so `|G|^p ≤ 2^j ∫_S |G|^p` on `S`
(`Haar.le_dyadicWeight_mul_setLIntegral_of_dyadicIndex`), and `|G| = |G|^p |G|^(1-p)`. -/
theorem setLIntegral_enorm_le_of_dyadicIndex (hp0 : p ≠ 0) (hp1 : p ≤ 1) {j : ℕ} {G : ℝ → ℂ}
    (hG : ∀ x y, dyadicIndex j x = dyadicIndex j y → G x = G y) {S : Set ℝ}
    (hSm : MeasurableSet S) (hS : ∀ x ∈ S, haarDyadicInterval j (dyadicIndex j x) ⊆ S) :
    ∫⁻ x in S, ‖G x‖ₑ ∂vol ≤
      dyadicWeight (1 / p.toReal - 1) j * (∫⁻ x in S, ‖G x‖ₑ ^ p.toReal ∂vol) ^ (1 / p.toReal) := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  set ρ := p.toReal with hρdef
  have hρ : 0 < ρ := ENNReal.toReal_pos hp0 hp
  have hρ1 : ρ ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1)
  set J := ∫⁻ x in S, ‖G x‖ₑ ^ ρ ∂vol
  rcases eq_or_ne J ∞ with hJ | hJ
  · rw [hJ, ENNReal.top_rpow_of_pos (by positivity),
      ENNReal.mul_top (ENNReal.dyadicWeight_ne_zero _ _)]
    exact le_top
  have hpt : ∀ x ∈ S, x ∈ Ico (0 : ℝ) 1 → ‖G x‖ₑ ^ ρ ≤ dyadicWeight 1 j * J := fun x hxS hx =>
    le_dyadicWeight_mul_setLIntegral_of_dyadicIndex (F := fun y => ‖G y‖ₑ ^ ρ) hx
      (fun y hy => by simp only [hG y x (mem_haarDyadicInterval.1 hy)]) (hS x hxS)
  set K := (dyadicWeight 1 j * J) ^ ((1 - ρ) / ρ) with hKdef
  have ha0 : 0 ≤ (1 - ρ) / ρ := div_nonneg (by linarith) hρ.le
  have hK : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) hρ.le)
    (ENNReal.mul_ne_top (ENNReal.dyadicWeight_ne_top _ _) hJ)
  have hae : ∀ᵐ x ∂vol.restrict S, ‖G x‖ₑ ≤ ‖G x‖ₑ ^ ρ * K := by
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae Interval.ae_mem_Ico_unitVol]
      with x hxS hx
    calc ‖G x‖ₑ = ‖G x‖ₑ ^ ρ * (‖G x‖ₑ ^ ρ) ^ ((1 - ρ) / ρ) := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ hρ.le (mul_nonneg hρ.le ha0),
            mul_div_cancel₀ _ hρ.ne', add_sub_cancel, ENNReal.rpow_one]
      _ ≤ ‖G x‖ₑ ^ ρ * K :=
          mul_le_mul_right (ENNReal.rpow_le_rpow (hpt x hxS hx) ha0) _
  calc ∫⁻ x in S, ‖G x‖ₑ ∂vol ≤ ∫⁻ x in S, ‖G x‖ₑ ^ ρ * K ∂vol := lintegral_mono_ae hae
    _ = J * K := lintegral_mul_const' _ _ hK
    _ = dyadicWeight (1 * ((1 - ρ) / ρ)) j * (J ^ (1 : ℝ) * J ^ ((1 - ρ) / ρ)) := by
        rw [hKdef, ENNReal.mul_rpow_of_nonneg _ _ ha0, ENNReal.dyadicWeight_rpow, ENNReal.rpow_one]
        ring
    _ = dyadicWeight (1 / ρ - 1) j * J ^ (1 / ρ) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one ha0]
        congr 2 <;> field_simp
        ring

/-- **The sup norm of a step of level `j`**: for `0 < p ≤ ∞` and an `ℱ_j`-measurable
`a ∈ L_t[0, 1]`, `‖a‖_∞ ≤ 2^(j/p) ‖a‖_p`, with `1/∞ = 0`. For `p < ∞`, the representative of `a`
that is constant on the dyadic intervals of level `j` has `|a(x)|^p ≤ 2^j ∫_0^1 |a|^p` for
`x ∈ [0, 1)` (`Haar.le_dyadicWeight_mul_setLIntegral_of_dyadicIndex`), and with the values `c_n`
of `a` the bound reads `max_n |c_n| ≤ (∑_n |c_n|^p)^(1/p)`. -/
theorem eLpNorm_top_le_of_mem_lpMeas (hp0 : p ≠ 0) {t : ℝ≥0∞} {j : ℕ} {a : Lp ℂ t vol}
    (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) t vol) :
    eLpNorm a ∞ vol ≤ dyadicWeight (1 / p.toReal) j * eLpNorm a p vol := by
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [ENNReal.toReal_top, div_zero, ENNReal.dyadicWeight_zero_left, one_mul]
  obtain ⟨g, hg, hag⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 ha
  have hgm : AEStronglyMeasurable g vol := (hg.mono (dyadicFiltration.le j)).aestronglyMeasurable
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_congr_ae hag, eLpNorm_congr_ae hag, eLpNorm_exponent_top hgm,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hgm]
  refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
  filter_upwards [Interval.ae_mem_Ico_unitVol] with x hx
  have h : ‖g x‖ₑ ^ p.toReal ≤ dyadicWeight 1 j * ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂vol := by
    simpa only [Measure.restrict_univ] using
      le_dyadicWeight_mul_setLIntegral_of_dyadicIndex (j := j) (S := univ)
        (F := fun y => ‖g y‖ₑ ^ p.toReal) hx
        (fun y hy => by simp only [eq_of_dyadicIndex_eq hg (mem_haarDyadicInterval.1 hy)])
        (subset_univ _)
  calc ‖g x‖ₑ = (‖g x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hρ.ne', ENNReal.rpow_one]
    _ ≤ (dyadicWeight 1 j * ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂vol) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = dyadicWeight (1 / p.toReal) j * (∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂vol) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.dyadicWeight_rpow, one_mul]

/-- **The Nikolskii inequality of steps**: for `0 < p ≤ r ≤ ∞` and an `ℱ_j`-measurable
`a ∈ L_t[0, 1]`, `‖a‖_r ≤ 2^(j(1/p - 1/r)) ‖a‖_p`, with `1/∞ = 0`. The sup bound
`‖a‖_∞ ≤ 2^(j/p) ‖a‖_p` (`Haar.eLpNorm_top_le_of_mem_lpMeas`) passes to `L_r` by
`MeasureTheory.eLpNorm_le_of_eLpNorm_top_le`, since `(j/p)(1 - p/r) = j(1/p - 1/r)`. -/
theorem eLpNorm_le_of_mem_lpMeas (hp0 : p ≠ 0) {r t : ℝ≥0∞} (hpr : p ≤ r) {j : ℕ}
    {a : Lp ℂ t vol} (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) t vol) :
    eLpNorm a r vol ≤ dyadicWeight (1 / p.toReal - 1 / r.toReal) j * eLpNorm a p vol := by
  refine (eLpNorm_le_of_eLpNorm_top_le hp0 hpr
    (eLpNorm_top_le_of_mem_lpMeas hp0 ha)).trans_eq ?_
  rw [ENNReal.dyadicWeight_rpow]
  congr 2
  rcases eq_or_ne r ∞ with rfl | hr
  · simp
  have hp : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top hr hpr)).ne'
  have hr0 : r.toReal ≠ 0 :=
    (ENNReal.toReal_pos ((pos_iff_ne_zero.2 hp0).trans_le hpr).ne' hr).ne'
  field_simp

/-- **Steps of level `j` lie in `L_1`**: for `0 < p ≤ 1` and an `ℱ_j`-measurable `a ∈ L_p[0, 1]`,
`‖a‖_1 ≤ 2^(j(1/p - 1)) ‖a‖_p`, the case `r = 1` of `Haar.eLpNorm_le_of_mem_lpMeas`. With the
values `c_n` of `a`, this is `2^(-j) ∑ |c_n| ≤ 2^(-j) (∑ |c_n|^p)^(1/p)`. -/
theorem eLpNorm_one_le_of_mem_lpMeas (hp0 : p ≠ 0) (hp1 : p ≤ 1) {j : ℕ} {a : Lp ℂ p vol}
    (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) :
    eLpNorm a 1 vol ≤ dyadicWeight (1 / p.toReal - 1) j * ‖a‖ₑ := by
  simpa only [ENNReal.toReal_one, div_one, ← Lp.eNorm_def] using
    eLpNorm_le_of_mem_lpMeas hp0 hp1 ha

/-! ### Haar coefficients -/

/-- A Haar function times an integrable function is integrable, since `|h_{k,m}| ≤ 2^(k/2)`. -/
theorem integrable_haarFunction_mul {f : ℝ → ℂ} (hf : Integrable f vol) (k : ℕ) (m : ℤ) :
    Integrable (fun x => (haarFunction k m x : ℂ) * f x) vol :=
  hf.bdd_mul (Complex.measurable_ofReal.comp (measurable_haarFunction k m)).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_haarFunction_le k m x)

/-- Haar coefficients are additive on integrable functions. -/
theorem haarCoeff_add {f g : ℝ → ℂ} (hf : Integrable f vol) (hg : Integrable g vol) (k : ℕ)
    (m : ℤ) : haarCoeff (f + g) k m = haarCoeff f k m + haarCoeff g k m := by
  simp only [haarCoeff, Pi.add_apply, mul_add]
  exact integral_add (integrable_haarFunction_mul hf k m) (integrable_haarFunction_mul hg k m)

/-- Haar coefficients are subtractive on integrable functions. -/
theorem haarCoeff_sub {f g : ℝ → ℂ} (hf : Integrable f vol) (hg : Integrable g vol) (k : ℕ)
    (m : ℤ) : haarCoeff (f - g) k m = haarCoeff f k m - haarCoeff g k m := by
  simp only [haarCoeff, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_haarFunction_mul hf k m) (integrable_haarFunction_mul hg k m)

/-- **A Haar coefficient by the local `L_1` norm**:
`|⟨f, h_{k,m}⟩| ≤ 2^(k/2) ∫_{I_{k,m}} |f|`, since `h_{k,m}` vanishes off `I_{k,m}` and has modulus
`2^(k/2)` on it. For non-integrable `f` the coefficient is `0`. -/
theorem enorm_haarCoeff_le (f : ℝ → ℂ) (k : ℕ) (m : ℤ) :
    ‖haarCoeff f k m‖ₑ ≤ dyadicWeight (1 / 2) k * ∫⁻ x in haarDyadicInterval k m, ‖f x‖ₑ ∂vol := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  rw [← lintegral_const_mul' _ _ (ENNReal.dyadicWeight_ne_top _ _),
    ← lintegral_indicator (measurableSet_haarDyadicInterval k m)]
  refine lintegral_mono fun x => ?_
  by_cases hx : dyadicIndex k x = m
  · rw [indicator_of_mem (mem_haarDyadicInterval.2 hx), eNorm_mul, enorm_haarFunction hx]
  · rw [haarFunction_eq_zero hx]
    simp

/-- **Steps of level `j ≤ k` have no Haar coefficients of level `k`**: if `G` is constant on the
dyadic intervals of level `k`, then `⟨G, h_{k,m}⟩ = 0`, since `h_{k,m}` has mean zero
(`Haar.integral_haarFunction`). -/
theorem haarCoeff_eq_zero_of_dyadicIndex {k : ℕ} {G : ℝ → ℂ}
    (hG : ∀ x y, dyadicIndex k x = dyadicIndex k y → G x = G y) (m : ℤ) : haarCoeff G k m = 0 := by
  have hpt : (fun x => (haarFunction k m x : ℂ) * G x) =
      fun x => (haarFunction k m x : ℂ) * G ((m : ℝ) / 2 ^ k) := by
    funext x
    by_cases hx : dyadicIndex k x = m
    · rw [hG x _ (hx.trans (dyadicIndex_intCast_div k m).symm)]
    · rw [haarFunction_eq_zero hx]
      simp
  rw [haarCoeff, hpt, integral_mul_const, integral_complex_ofReal, integral_haarFunction,
    Complex.ofReal_zero, zero_mul]

/-- An `ℱ_j`-measurable element of `L_p[0, 1]` has no Haar coefficients of level `k ≥ j`. -/
theorem haarCoeff_eq_zero_of_mem_lpMeas {j k : ℕ} (hjk : j ≤ k) {a : Lp ℂ p vol}
    (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) (m : ℤ) : haarCoeff a k m = 0 := by
  obtain ⟨g, hg, hag⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 ha
  rw [haarCoeff_congr_ae hag]
  exact haarCoeff_eq_zero_of_dyadicIndex (fun x y h =>
    eq_of_dyadicIndex_eq hg (dyadicIndex_eq_of_le hjk h)) m

/-! ### The level norms of the Haar expansion -/

variable (p) in
/-- The **quasi-norm of level `k` of the Haar expansion** of `f` in `L_p`,
`2^(k(1/2 - 1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p}`, that is `‖∑_m ⟨f, h_{k,m}⟩ h_{k,m}‖_p`
(`Haar.eLpNorm_sum_haar`). -/
noncomputable def haarLevelNorm (f : ℝ → ℂ) (k : ℕ) : ℝ≥0∞ :=
  dyadicWeight (1 / 2 - 1 / p.toReal) k *
    lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)

/-- Functions that agree almost everywhere on `[0, 1]` have the same level norms. -/
theorem haarLevelNorm_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[vol] g) (k : ℕ) :
    haarLevelNorm p f k = haarLevelNorm p g k := by
  simp only [haarLevelNorm, haarCoeff_congr_ae h]

/-- The `p`-th power of the level norm:
`2^(k(p/2 - 1)) ∑_{m<2^k} |⟨f, h_{k,m}⟩|^p`, for `0 < p < ∞`. -/
theorem haarLevelNorm_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : ℝ → ℂ) (k : ℕ) :
    haarLevelNorm p f k ^ p.toReal = dyadicWeight (p.toReal / 2 - 1) k *
      ∑ m : Fin (2 ^ k), ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ ^ p.toReal := by
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [haarLevelNorm, ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.dyadicWeight_rpow,
    ENNReal.lqNorm_rpow hp0 hp, tsum_fintype]
  congr 2
  field_simp

/-- **The level norm is the norm of the martingale difference**: for integrable `f` and
`0 < p < ∞`, `‖E[f | ℱ_{k+1}] - E[f | ℱ_k]‖_p` is the level norm of `f`
(`Haar.condExp_succ_sub_ae_eq`, `Haar.eLpNorm_sum_haar`). -/
theorem haarLevelNorm_eq_eLpNorm (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : ℝ → ℂ} (hf : Integrable f vol)
    (k : ℕ) : haarLevelNorm p f k =
      eLpNorm (vol[f | dyadicFiltration (k + 1)] - vol[f | dyadicFiltration k]) p vol := by
  rw [eLpNorm_congr_ae (condExp_succ_sub_ae_eq k hf), eLpNorm_sum_haar hp0 hp]
  rfl

/-- **The level norm by the `L_1` norm**: `H_k(f) ≤ 2^k ∫_0^1 |f|`, since every coefficient is
at most `2^(k/2) ∫_0^1 |f|` (`Haar.enorm_haarCoeff_le`) and there are `2^k` of them. -/
theorem haarLevelNorm_le_lintegral (f : ℝ → ℂ) (k : ℕ) :
    haarLevelNorm p f k ≤ dyadicWeight 1 k * ∫⁻ x, ‖f x‖ₑ ∂vol := by
  have hc : ∀ m : Fin (2 ^ k), ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ ≤
      dyadicWeight (1 / 2) k * ∫⁻ x, ‖f x‖ₑ ∂vol := fun m =>
    (enorm_haarCoeff_le f k _).trans (mul_le_mul_right (setLIntegral_le_lintegral _ _) _)
  calc haarLevelNorm p f k ≤ dyadicWeight (1 / 2 - 1 / p.toReal) k *
        ((Fintype.card (Fin (2 ^ k)) : ℝ≥0∞) ^ (1 / p.toReal) *
          (dyadicWeight (1 / 2) k * ∫⁻ x, ‖f x‖ₑ ∂vol)) := by
        rw [haarLevelNorm]
        gcongr
        exact ENNReal.lqNorm_le_card_rpow_mul hc
    _ = dyadicWeight 1 k * ∫⁻ x, ‖f x‖ₑ ∂vol := by
        rw [Fintype.card_fin, ENNReal.natCast_two_pow_rpow, ← mul_assoc, ← mul_assoc,
          ← ENNReal.dyadicWeight_add, ← ENNReal.dyadicWeight_add]
        congr 2
        ring

/-- **`p`-subadditivity of the level norm**, `0 < p ≤ 1`: for integrable `f` and `g`,
`H_k(f + g)^p ≤ H_k(f)^p + H_k(g)^p`, from `|a + b|^p ≤ |a|^p + |b|^p` for the coefficients. -/
theorem haarLevelNorm_add_rpow_le (hp0 : p ≠ 0) (hp1 : p ≤ 1) {f g : ℝ → ℂ}
    (hf : Integrable f vol) (hg : Integrable g vol) (k : ℕ) :
    haarLevelNorm p (f + g) k ^ p.toReal ≤
      haarLevelNorm p f k ^ p.toReal + haarLevelNorm p g k ^ p.toReal := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hρ1 : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1)
  rw [haarLevelNorm_rpow hp0 hp, haarLevelNorm_rpow hp0 hp, haarLevelNorm_rpow hp0 hp, ← mul_add,
    ← Finset.sum_add_distrib]
  gcongr with m
  rw [haarCoeff_add hf hg]
  exact (ENNReal.rpow_le_rpow (eNorm_add_le _ _) hρ.le).trans
    (ENNReal.rpow_add_le_add_rpow _ _ hρ.le hρ1)

/-- **The level norm of a step**: for `0 < p ≤ 1`, `k ≤ j` and an `ℱ_j`-measurable
`a ∈ L_p[0, 1]`, `H_k(a) ≤ 2^((j-k)(1/p - 1)) ‖a‖_p`. Each coefficient is at most
`2^(k/2) ∫_{I_{k,m}} |a|` (`Haar.enorm_haarCoeff_le`), and on `I_{k,m}` the step `a` satisfies
`∫ |a| ≤ 2^(j(1/p - 1)) (∫ |a|^p)^(1/p)` (`Haar.setLIntegral_enorm_le_of_dyadicIndex`). -/
theorem haarLevelNorm_le_of_mem_lpMeas (hp0 : p ≠ 0) (hp1 : p ≤ 1) {j k : ℕ} (hkj : k ≤ j)
    {a : Lp ℂ p vol} (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) :
    haarLevelNorm p a k ≤ dyadicWeight (1 / p.toReal - 1) (j - k) * ‖a‖ₑ := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  set ρ := p.toReal
  have hρ : 0 < ρ := ENNReal.toReal_pos hp0 hp
  obtain ⟨g, hg, hag⟩ := mem_lpMeas_iff_aestronglyMeasurable.1 ha
  have hgm : AEStronglyMeasurable g vol := (hg.mono (dyadicFiltration.le j)).aestronglyMeasurable
  have hm : ∀ m : Fin (2 ^ k), ‖haarCoeff g k ((m : ℕ) : ℤ)‖ₑ ^ ρ ≤ dyadicWeight (ρ / 2) k *
      (dyadicWeight (1 - ρ) j * ∫⁻ x in haarDyadicInterval k ((m : ℕ) : ℤ), ‖g x‖ₑ ^ ρ ∂vol) := by
    intro m
    have hS : ∀ x ∈ haarDyadicInterval k ((m : ℕ) : ℤ),
        haarDyadicInterval j (dyadicIndex j x) ⊆ haarDyadicInterval k ((m : ℕ) : ℤ) :=
      fun x hx y hy => (dyadicIndex_eq_of_le hkj hy).trans hx
    calc ‖haarCoeff g k ((m : ℕ) : ℤ)‖ₑ ^ ρ
        ≤ (dyadicWeight (1 / 2) k * (dyadicWeight (1 / ρ - 1) j *
            (∫⁻ x in haarDyadicInterval k ((m : ℕ) : ℤ), ‖g x‖ₑ ^ ρ ∂vol) ^ (1 / ρ))) ^ ρ := by
          refine ENNReal.rpow_le_rpow ((enorm_haarCoeff_le g k _).trans ?_) hρ.le
          gcongr
          exact setLIntegral_enorm_le_of_dyadicIndex hp0 hp1
            (fun x y h => eq_of_dyadicIndex_eq hg h) (measurableSet_haarDyadicInterval _ _) hS
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.mul_rpow_of_nonneg _ _ hρ.le,
            ENNReal.dyadicWeight_rpow, ENNReal.dyadicWeight_rpow, ← ENNReal.rpow_mul,
            one_div_mul_cancel hρ.ne', ENNReal.rpow_one, show (1 / 2 : ℝ) * ρ = ρ / 2 by ring,
            show (1 / ρ - 1) * ρ = 1 - ρ by field_simp]
  rw [← ENNReal.rpow_le_rpow_iff hρ, haarLevelNorm_congr_ae hag, haarLevelNorm_rpow hp0 hp,
    ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.dyadicWeight_rpow, Lp.eNorm_def,
    eLpNorm_congr_ae hag, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hgm, ← ENNReal.rpow_mul,
    one_div_mul_cancel hρ.ne', ENNReal.rpow_one]
  calc dyadicWeight (ρ / 2 - 1) k * ∑ m : Fin (2 ^ k), ‖haarCoeff g k ((m : ℕ) : ℤ)‖ₑ ^ ρ
      ≤ dyadicWeight (ρ / 2 - 1) k * ∑ m : Fin (2 ^ k), dyadicWeight (ρ / 2) k *
          (dyadicWeight (1 - ρ) j * ∫⁻ x in haarDyadicInterval k ((m : ℕ) : ℤ),
              ‖g x‖ₑ ^ ρ ∂vol) := by
        gcongr with m
        exact hm m
    _ = dyadicWeight (ρ / 2 - 1) k * dyadicWeight (ρ / 2) k * dyadicWeight (1 - ρ) j *
          ∫⁻ x, ‖g x‖ₑ ^ ρ ∂vol := by
        rw [← sum_setLIntegral_haarDyadicInterval _ k, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = dyadicWeight ((1 / ρ - 1) * ρ) (j - k) * ∫⁻ x, ‖g x‖ₑ ^ ρ ∂vol := by
        congr 1
        simp only [dyadicWeight]
        rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
          ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, Nat.cast_sub hkj]
        congr 1
        field_simp
        ring

/-- The level norm of an `ℱ_j`-measurable element of `L_p[0, 1]` vanishes at every level
`k ≥ j`. -/
theorem haarLevelNorm_eq_zero_of_mem_lpMeas {j k : ℕ} (hjk : j ≤ k) {a : Lp ℂ p vol}
    (ha : a ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) : haarLevelNorm p a k = 0 := by
  simp [haarLevelNorm, haarCoeff_eq_zero_of_mem_lpMeas hjk ha, ENNReal.lqNorm_zero_right]

/-! ### Near-best steps -/

section NearBest

variable {f : Lp ℂ p vol} {b : ℕ → Lp ℂ p vol} {e : ℕ → ℝ≥0∞}

/-- **Two near-best steps are close**: for `0 < p ≤ 1`, if `‖f - b_j‖_p ≤ e_j` for every `j` and
`e` decreases, then `‖b_{j+1} - b_j‖_p^p ≤ 2 e_j^p` (`MeasureTheory.Lp.enorm_sub_rpow_le_two_mul`
with `‖f - b_{j+1}‖_p ≤ e_{j+1} ≤ e_j`). For a general couple this is
`InterpCouple.norm0_sub_succ_rpow_le_of_nearBest`. -/
theorem enorm_sub_rpow_le_of_nearBest (hp1 : p ≤ 1) (hbe : ∀ j, ‖f - b j‖ₑ ≤ e j)
    (he : Antitone e) (j : ℕ) : ‖b (j + 1) - b j‖ₑ ^ p.toReal ≤ 2 * e j ^ p.toReal :=
  Lp.enorm_sub_rpow_le_two_mul hp1 ((hbe (j + 1)).trans (he j.le_succ)) (hbe j)

/-- **Two near-best steps in `L_1`**: under the hypotheses of `Haar.enorm_sub_rpow_le_of_nearBest`,
with `b_j` measurable for `ℱ_j`,
`‖b_{j+1} - b_j‖_1 ≤ 2^((j+1)(1/p - 1)) 2^(1/p) e_j` (`Haar.eLpNorm_one_le_of_mem_lpMeas`). -/
theorem eLpNorm_one_sub_le_of_nearBest (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hb : ∀ j, b j ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) (hbe : ∀ j, ‖f - b j‖ₑ ≤ e j)
    (he : Antitone e) (j : ℕ) :
    eLpNorm (⇑(b (j + 1)) - ⇑(b j)) 1 vol ≤
      dyadicWeight (1 / p.toReal - 1) (j + 1) * (2 ^ (1 / p.toReal) * e j) := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  rw [← eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
  refine (eLpNorm_one_le_of_mem_lpMeas hp0 hp1
    (sub_mem (hb (j + 1)) (mem_lpMeas_of_le j.le_succ (hb j)))).trans ?_
  gcongr
  exact ENNReal.le_two_rpow_mul_of_rpow_le hp0 hp (enorm_sub_rpow_le_of_nearBest hp1 hbe he j)

/-- **Near-best steps converge in measure**: if `‖f - b_j‖_p ≤ e_j → 0`, then `b_j → f` in
measure, the case of elements of `L_p` of `MeasureTheory.tendstoInMeasure_of_eLpNorm_sub_le`. -/
theorem tendstoInMeasure_of_nearBest (hp0 : p ≠ 0) (hbe : ∀ j, ‖f - b j‖ₑ ≤ e j)
    (he0 : Tendsto e atTop (𝓝 0)) : TendstoInMeasure vol (fun n => ⇑(b n)) atTop ⇑f := by
  have hbe' : ∀ᶠ n in atTop, eLpNorm (⇑f - ⇑(b n)) p vol ≤ e n := Eventually.of_forall fun n => by
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub _ _), ← Lp.eNorm_def]
    exact hbe n
  exact tendstoInMeasure_of_eLpNorm_sub_le hp0 hbe' he0

/-- **The `L_1` distance to a near-best step**: if `b_j` are `ℱ_j`-measurable with
`‖f - b_j‖_p ≤ e_j`, `e` decreasing to `0`, then
`‖f - b_k‖_1 ≤ ∑_{i ≥ 0} 2^((k+i+1)(1/p - 1)) 2^(1/p) e_{k+i}`. It is the case `r = 1`,
`C = 2^(1/p - 1)`, `β = 1/p - 1` of `MeasureTheory.eLpNorm_sub_rpow_min_le_tsum_of_nearBest`,
proved here by Fatou's lemma for telescoping sums in `L_1`
(`MeasureTheory.eLpNorm_sub_rpow_le_tsum`) and the bound of each difference `b_{j+1} - b_j`
(`Haar.eLpNorm_one_sub_le_of_nearBest`). -/
theorem eLpNorm_one_sub_le_tsum_of_nearBest (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hb : ∀ j, b j ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) (hbe : ∀ j, ‖f - b j‖ₑ ≤ e j)
    (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0)) (k : ℕ) :
    eLpNorm (⇑f - ⇑(b k)) 1 vol ≤ ∑' i, dyadicWeight (1 / p.toReal - 1) (k + i + 1) *
      (2 ^ (1 / p.toReal) * e (k + i)) := by
  have h := MeasureTheory.eLpNorm_sub_rpow_le_tsum one_ne_zero le_rfl
    (tendstoInMeasure_of_nearBest hp0 hbe he0) (fun n => Lp.aestronglyMeasurable (b n)) k
  simp only [ENNReal.toReal_one, ENNReal.rpow_one] at h
  exact h.trans (tsum_le_tsum fun i =>
    eLpNorm_one_sub_le_of_nearBest hp0 hp1 hb hbe he (k + i))

/-- **The `L_1` norm by near-best steps**: under the hypotheses of
`Haar.eLpNorm_one_sub_le_tsum_of_nearBest` and `‖f‖_p ≤ e_0`,
`‖f‖_1 ≤ 2^(1/p) e_0 + ∑_{i ≥ 0} 2^((i+1)(1/p - 1)) 2^(1/p) e_i`: the step `b_0` is a constant with
`‖b_0‖_1 = ‖b_0‖_p ≤ 2^(1/p) e_0`. -/
theorem eLpNorm_one_le_of_nearBest (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hb : ∀ j, b j ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) (hbe : ∀ j, ‖f - b j‖ₑ ≤ e j)
    (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0)) (hfe : ‖f‖ₑ ≤ e 0) :
    eLpNorm f 1 vol ≤ 2 ^ (1 / p.toReal) * e 0 +
      ∑' i, dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * e i) := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hb0 : ‖b 0‖ₑ ≤ 2 ^ (1 / p.toReal) * e 0 := by
    refine ENNReal.le_two_rpow_mul_of_rpow_le hp0 hp ?_
    have h := Lp.enorm_sub_rpow_le_two_mul (g := b 0) (h := 0) hp1 (hbe 0) (by rwa [sub_zero])
    rwa [sub_zero] at h
  have h1 : eLpNorm (b 0) 1 vol ≤ 2 ^ (1 / p.toReal) * e 0 := by
    refine (eLpNorm_one_le_of_mem_lpMeas hp0 hp1 (hb 0)).trans ?_
    rw [ENNReal.dyadicWeight_zero_right, one_mul]
    exact hb0
  have h2 := eLpNorm_one_sub_le_tsum_of_nearBest hp0 hp1 hb hbe he he0 0
  simp only [zero_add] at h2
  calc eLpNorm f 1 vol = eLpNorm ((⇑f - ⇑(b 0)) + ⇑(b 0)) 1 vol := by rw [sub_add_cancel]
    _ ≤ eLpNorm (⇑f - ⇑(b 0)) 1 vol + eLpNorm (b 0) 1 vol := eLpNorm_add_le le_rfl
    _ ≤ _ := by rw [add_comm]; gcongr

/-- **Near-best steps with a summable `L_1` bound**: under the hypotheses of
`Haar.eLpNorm_one_sub_le_tsum_of_nearBest`, if `∑_i 2^((i+1)(1/p - 1)) 2^(1/p) e_i < ∞`, then
`f ∈ L_1[0, 1]`, since `‖f - b_0‖_1` is at most this series and the step `b_0` lies in `L_1`. -/
theorem integrable_of_nearBest (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hb : ∀ j, b j ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) (hbe : ∀ j, ‖f - b j‖ₑ ≤ e j)
    (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0))
    (hsum : ∑' i, dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * e i) ≠ ∞) :
    Integrable f vol := by
  have h0 := eLpNorm_one_sub_le_tsum_of_nearBest hp0 hp1 hb hbe he he0 0
  simp only [zero_add] at h0
  have hm : MemLp (⇑f - ⇑(b 0)) 1 vol := h0.trans_lt hsum.lt_top
  refine ((memLp_one_iff_integrable.1 hm).add
    (memLp_one_iff_integrable.1 (memLp_of_mem_lpMeas (hb 0) 1))).congr
      (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]

/-- **The level norms by near-best steps**: under the hypotheses of
`Haar.eLpNorm_one_sub_le_tsum_of_nearBest`, if `∑_i 2^((i+1)(1/p - 1)) 2^(1/p) e_i < ∞`, then
`H_k(f)^p ≤ ∑_{i ≥ 0} (2^((i+1)(1/p - 1)) 2^(1/p) e_{k+i})^p`. Then `f` is integrable
(`Haar.integrable_of_nearBest`), and the telescoping
`b_{k+n} = b_k + ∑_{i<n} (b_{k+i+1} - b_{k+i})`, where `H_k(b_k) = 0`, the bound of the level norm
of a step (`Haar.haarLevelNorm_le_of_mem_lpMeas`) and `H_k(f - b_{k+n}) ≤ 2^k ‖f - b_{k+n}‖_1 → 0`
(`Haar.haarLevelNorm_le_lintegral`) give it. -/
theorem haarLevelNorm_rpow_le_tsum_of_nearBest (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hb : ∀ j, b j ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) (hbe : ∀ j, ‖f - b j‖ₑ ≤ e j)
    (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0))
    (hsum : ∑' i, dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * e i) ≠ ∞)
    (k : ℕ) : haarLevelNorm p f k ^ p.toReal ≤
      ∑' i, (dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * e (k + i))) ^
        p.toReal := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hf := integrable_of_nearBest hp0 hp1 hb hbe he he0 hsum
  set ρ := p.toReal
  have hρ : 0 < ρ := ENNReal.toReal_pos hp0 hp
  set S := ∑' i, (dyadicWeight (1 / ρ - 1) (i + 1) * (2 ^ (1 / ρ) * e (k + i))) ^ ρ
  set T : ℕ → ℝ≥0∞ := fun n =>
    ∑' i, dyadicWeight (1 / ρ - 1) (n + i + 1) * (2 ^ (1 / ρ) * e (n + i))
  have hI : ∀ j, Integrable (b j) vol := fun j =>
    memLp_one_iff_integrable.1 (memLp_of_mem_lpMeas (hb j) 1)
  have htel : ∀ n, haarLevelNorm p (b (k + n)) k ^ ρ ≤ S := fun n => by
    have hstep : ∀ i, haarLevelNorm p (⇑(b (k + i + 1)) - ⇑(b (k + i))) k ^ ρ ≤
        (dyadicWeight (1 / ρ - 1) (i + 1) * (2 ^ (1 / ρ) * e (k + i))) ^ ρ := fun i => by
      rw [haarLevelNorm_congr_ae (Lp.coeFn_sub _ _).symm]
      refine ENNReal.rpow_le_rpow ((haarLevelNorm_le_of_mem_lpMeas hp0 hp1 (by omega)
        (sub_mem (hb _) (mem_lpMeas_of_le (Nat.le_succ _) (hb _)))).trans ?_) hρ.le
      rw [show k + i + 1 - k = i + 1 by omega]
      gcongr
      exact ENNReal.le_two_rpow_mul_of_rpow_le hp0 hp (enorm_sub_rpow_le_of_nearBest hp1 hbe he _)
    refine le_trans ?_ ((Finset.sum_le_sum (s := Finset.range n) fun i _ => hstep i).trans
      (sum_le_tsum _))
    induction n with
    | zero => simp [haarLevelNorm_eq_zero_of_mem_lpMeas le_rfl (hb k), ENNReal.zero_rpow_of_pos hρ]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      calc haarLevelNorm p (b (k + (n + 1))) k ^ ρ
          = haarLevelNorm p ((⇑(b (k + n + 1)) - ⇑(b (k + n))) + ⇑(b (k + n))) k ^ ρ := by
            rw [sub_add_cancel]
            rfl
        _ ≤ haarLevelNorm p (⇑(b (k + n + 1)) - ⇑(b (k + n))) k ^ ρ +
              haarLevelNorm p (b (k + n)) k ^ ρ :=
            haarLevelNorm_add_rpow_le hp0 hp1 ((hI _).sub (hI _)) (hI _) k
        _ ≤ _ := by rw [add_comm]; gcongr
  have hT : Tendsto (fun n => T (k + n)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_sum_nat_add
      (fun j => dyadicWeight (1 / ρ - 1) (j + 1) * (2 ^ (1 / ρ) * e j)) hsum
    refine (h.comp (tendsto_atTop_mono (fun n => Nat.le_add_left n k) tendsto_id)).congr
      fun n => tsum_congr fun i => ?_
    rw [add_comm i (k + n)]
  have hbound : ∀ n, haarLevelNorm p f k ^ ρ ≤ (dyadicWeight 1 k * T (k + n)) ^ ρ + S := fun n => by
    have hfb : haarLevelNorm p (⇑f - ⇑(b (k + n))) k ≤ dyadicWeight 1 k * T (k + n) := by
      refine (haarLevelNorm_le_lintegral _ k).trans ?_
      gcongr
      rw [← eLpNorm_one_eq_lintegral_eNorm
        ((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable _))]
      exact eLpNorm_one_sub_le_tsum_of_nearBest hp0 hp1 hb hbe he he0 (k + n)
    calc haarLevelNorm p f k ^ ρ
        = haarLevelNorm p ((⇑f - ⇑(b (k + n))) + ⇑(b (k + n))) k ^ ρ := by rw [sub_add_cancel]
      _ ≤ haarLevelNorm p (⇑f - ⇑(b (k + n))) k ^ ρ + haarLevelNorm p (b (k + n)) k ^ ρ :=
          haarLevelNorm_add_rpow_le hp0 hp1 (hf.sub (hI _)) (hI _) k
      _ ≤ _ := add_le_add (ENNReal.rpow_le_rpow hfb hρ.le) (htel n)
  have hlim : Tendsto (fun n => (dyadicWeight 1 k * T (k + n)) ^ ρ + S) atTop (𝓝 (0 + S)) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    have h0 := ENNReal.Tendsto.const_mul hT (Or.inr (ENNReal.dyadicWeight_ne_top 1 k))
    rw [mul_zero] at h0
    have h1 := (ENNReal.continuous_rpow_const (y := ρ)).continuousAt.tendsto.comp h0
    rw [ENNReal.zero_rpow_of_pos hρ] at h1
    exact h1
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim hbound

end NearBest

/-! ### The embedding into `L_1` -/

variable {s : ℝ} {q : ℝ≥0∞}

/-- **Near-best steps exist**: for every `f ∈ L_p[0, 1]` and `s` there are `ℱ_j`-measurable
`b_j ∈ L_p` with `‖f - b_j‖_p ≤ E(2^j, f) + ‖f‖_p 2^(-j(s+1))` in the step couple. This is
`InterpCouple.exists_nearBest_eFunctional` for the step couple, with the complexity bound
`N₁(b_j) ≤ 2^j` read as `ℱ_j`-measurability (`Haar.mem_lpMeas_of_stepCouple_norm1_le`). -/
theorem exists_nearBest_stepCouple (f : Lp ℂ p vol) (s : ℝ) :
    ∃ b : ℕ → Lp ℂ p vol, (∀ j, b j ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) ∧
      ∀ j, ‖f - b j‖ₑ ≤
        (stepCouple p).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) f + ‖f‖ₑ * dyadicWeight (-(s + 1)) j := by
  obtain ⟨b, hb1, hb0⟩ := InterpCouple.exists_nearBest_eFunctional (A := stepCouple p)
    InterpCouple.ofMonotoneSubgroups_norm1_zero f s
  exact ⟨b, fun j => mem_lpMeas_of_stepCouple_norm1_le (hb1 j), hb0⟩

/-- The tolerances `e_j = E(2^j, f) + ‖f‖_p 2^(-j(s+1))` decrease for `s ≥ -1`, the step couple's
case of `InterpCouple.antitone_eFunctional_add_dyadicWeight`. -/
theorem antitone_eFunctional_stepCouple_add (hs : -1 ≤ s) (f : Lp ℂ p vol) :
    Antitone fun j : ℕ =>
      (stepCouple p).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) f + ‖f‖ₑ * dyadicWeight (-(s + 1)) j :=
  (stepCouple p).antitone_eFunctional_add_dyadicWeight hs f

/-- **The sum of the `L_1` bounds**: for `q ≠ 0`, with `δ = s - (1/p - 1)`,
`∑_i 2^((i+1)(1/p - 1)) 2^(1/p) e_i ≤ 2^(1/p) 2^(1/p - 1) (1 - 2^(-δ))⁻¹ ‖(2^(ks) e_k)_k‖_{ℓ_q}`,
since `e_i ≤ 2^(-is) ‖(2^(ks) e_k)_k‖_{ℓ_q}`. -/
theorem tsum_dyadicWeight_succ_mul_le_lqNorm (hq0 : q ≠ 0) (e : ℕ → ℝ≥0∞) :
    ∑' i, dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * e i) ≤
      2 ^ (1 / p.toReal) * 2 ^ (1 / p.toReal - 1) * (1 - 2 ^ (-(s - (1 / p.toReal - 1))))⁻¹ *
        lqNorm q (fun k => dyadicWeight s k * e k) := by
  set L := lqNorm q (fun k => dyadicWeight s k * e k)
  calc ∑' i, dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * e i)
      ≤ ∑' i, dyadicWeight (1 / p.toReal - 1) (i + 1) *
          (2 ^ (1 / p.toReal) * (dyadicWeight (-s) i * L)) := by
        gcongr with i
        exact ENNReal.le_dyadicWeight_neg_mul_lqNorm hq0 s e i
    _ = ∑' i, 2 ^ (1 / p.toReal) * 2 ^ (1 / p.toReal - 1) * L *
          dyadicWeight (-(s - (1 / p.toReal - 1))) i := by
        refine tsum_congr fun i => ?_
        rw [ENNReal.dyadicWeight_succ, show -(s - (1 / p.toReal - 1)) = (1 / p.toReal - 1) + -s by
          ring, ENNReal.dyadicWeight_add]
        ring
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
        ring

/-- The constant `2^(1/p) (1 + 2^(1/p - 1) (1 - 2^(-δ))⁻¹) C_q (1 + γ_{1,q})`, `δ = s - (1/p - 1)`,
of the embedding of the approximation spaces of the step couple into `L_1`, with Mathlib's
`C_q = LpAddConst q` and `γ_{1,q} = dyadicGeomConst 1 q`. -/
noncomputable def stepCoupleEmbedConst (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  2 ^ (1 / p.toReal) * (1 + 2 ^ (1 / p.toReal - 1) * (1 - 2 ^ (-(s - (1 / p.toReal - 1))))⁻¹) *
    (ENNReal.LpAddConst q * (1 + ENNReal.dyadicGeomConst 1 q))

/-- The embedding constant is finite for `s > 1/p - 1`. -/
theorem stepCoupleEmbedConst_ne_top (hs : 1 / p.toReal - 1 < s) (q : ℝ≥0∞) :
    stepCoupleEmbedConst p s q ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _) (ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith))⟩))
    (ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q).ne
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.dyadicGeomConst_ne_top one_pos q⟩))

/-- `0 < s` when `s > 1/p - 1` and `0 < p ≤ 1`, since then `1/p ≥ 1`. -/
theorem pos_of_one_div_sub_one_lt (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 1 / p.toReal - 1 < s) :
    0 < s := by
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
  have hρ1 : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1)
  have : 1 ≤ 1 / p.toReal := one_le_one_div hρ hρ1
  linarith

/-- **The step couple embeds into `L_1` for `s > 1/p - 1`**: for `0 < p ≤ 1` and `q ≠ 0`,
`‖f‖_1 ≤ stepCoupleEmbedConst p s q · (‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q})`. The near-best
steps `b_j` of `Haar.exists_nearBest_stepCouple` converge in measure to `f`, and their differences
add up in `L_1` (`Haar.eLpNorm_one_le_of_nearBest`), with
`‖(2^(ks) e_k)_k‖_{ℓ_q} ≤ C_q (1 + γ_{1,q})` times the dyadic norm
(`InterpCouple.lqNorm_dyadicWeight_mul_eFunctional_add_le`). -/
theorem eLpNorm_one_le_eNormDyadic (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 1 / p.toReal - 1 < s)
    (hq0 : q ≠ 0) (f : Lp ℂ p vol) :
    eLpNorm f 1 vol ≤ stepCoupleEmbedConst p s q * (stepCouple p).eNormDyadic s q f := by
  set N := (stepCouple p).eNormDyadic s q f
  have hs0 := pos_of_one_div_sub_one_lt hp0 hp1 hs
  have hC0 : stepCoupleEmbedConst p s q ≠ 0 := mul_ne_zero (mul_ne_zero
    (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
      (ne_of_gt (lt_of_lt_of_le one_pos le_self_add)))
    (mul_ne_zero (ne_of_gt (lt_of_lt_of_le one_pos (ENNReal.one_le_LpAddConst q)))
      (ne_of_gt (lt_of_lt_of_le one_pos le_self_add)))
  rcases eq_or_ne N ∞ with hN | hN
  · rw [hN, ENNReal.mul_top hC0]
    exact le_top
  obtain ⟨b, hb, hbe⟩ := exists_nearBest_stepCouple f s
  set e : ℕ → ℝ≥0∞ := fun j =>
    (stepCouple p).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) f + ‖f‖ₑ * dyadicWeight (-(s + 1)) j
  set L := lqNorm q (fun k => dyadicWeight s k * e k)
  have hL : L ≤ ENNReal.LpAddConst q * (1 + ENNReal.dyadicGeomConst 1 q) * N :=
    InterpCouple.lqNorm_dyadicWeight_mul_eFunctional_add_le (stepCouple p) s q f
  have hLt : L ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.LpAddConst_lt_top q).ne (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.dyadicGeomConst_ne_top one_pos q⟩)) hN) hL
  have he0 : Tendsto e atTop (𝓝 0) := ENNReal.tendsto_zero_of_lqNorm_dyadicWeight_ne_top hq0 hs0 hLt
  have hfe : ‖f‖ₑ ≤ e 0 := le_add_left (by rw [ENNReal.dyadicWeight_zero_right, mul_one])
  have he00 : e 0 ≤ L := by
    simpa using ENNReal.le_lqNorm hq0 (fun k => dyadicWeight s k * e k) 0
  refine (eLpNorm_one_le_of_nearBest hp0 hp1 hb hbe
    (antitone_eFunctional_stepCouple_add (by linarith) f) he0 hfe).trans ?_
  calc 2 ^ (1 / p.toReal) * e 0 +
        ∑' i, dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * e i)
      ≤ 2 ^ (1 / p.toReal) * L + 2 ^ (1 / p.toReal) * 2 ^ (1 / p.toReal - 1) *
          (1 - 2 ^ (-(s - (1 / p.toReal - 1))))⁻¹ * L :=
        add_le_add (by gcongr) (tsum_dyadicWeight_succ_mul_le_lqNorm hq0 e)
    _ = 2 ^ (1 / p.toReal) * (1 + 2 ^ (1 / p.toReal - 1) *
          (1 - 2 ^ (-(s - (1 / p.toReal - 1))))⁻¹) * L := by ring
    _ ≤ _ := by
        rw [stepCoupleEmbedConst, mul_assoc _ (ENNReal.LpAddConst q * _)]
        gcongr

/-- **Elements of the approximation spaces of the step couple are integrable** for
`s > 1/p - 1`: for `0 < p ≤ 1`, `q ≠ 0` and a finite dyadic norm, `f ∈ L_1[0, 1]`
(`Haar.eLpNorm_one_le_eNormDyadic`). -/
theorem integrable_of_eNormDyadic_lt_top (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 1 / p.toReal - 1 < s)
    (hq0 : q ≠ 0) {f : Lp ℂ p vol} (hf : (stepCouple p).eNormDyadic s q f < ∞) :
    Integrable f vol := by
  have h := (eLpNorm_one_le_eNormDyadic hp0 hp1 hs hq0 f).trans_lt
    (ENNReal.mul_lt_top (stepCoupleEmbedConst_ne_top hs q).lt_top hf)
  exact memLp_one_iff_integrable.1 h

/-! ### Martingale convergence in `L_1` -/

/-- **Martingale convergence in `L_1[0, 1]`**: for integrable `F`, `E[F | ℱ_N] → F` in `L_1`. The
conditional expectations form a projection scheme of bound `1` in `L_1`
(`MeasureTheory.Filtration.filtrationProjectionScheme`) whose approximants are dense
(`Haar.closure_iUnion_haarScheme`), so the projections converge
(`ApproximationScheme.ProjectionScheme.tendsto_of_dense`). -/
theorem tendsto_eLpNorm_condExp_sub {F : ℝ → ℂ} (hF : Integrable F vol) :
    Tendsto (fun N => eLpNorm (vol[F | dyadicFiltration N] - F) 1 vol) atTop (𝓝 0) := by
  have hm : MemLp F 1 vol := memLp_one_iff_integrable.2 hF
  have hP2 : ∀ N, (dyadicFiltration.filtrationProjectionScheme (p := 1) (μ := vol)).P (2 ^ N) =
      Lp.condExpLp (dyadicFiltration N) := fun N =>
    ApproximationScheme.ProjectionScheme.ofMonotone_two_pow N
  have hP := (dyadicFiltration.filtrationProjectionScheme (p := 1) (μ := vol)).tendsto_of_dense
    (closure_iUnion_haarScheme (p := 1) ENNReal.one_ne_top) (hm.toLp F)
  have h2 : Tendsto (fun N => Lp.condExpLp (dyadicFiltration N) (hm.toLp F)) atTop
      (𝓝 (hm.toLp F)) :=
    (hP.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).congr fun N => by
      rw [Function.comp_apply, hP2]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h2
  refine h2.congr fun N => eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_condExpLp (m := dyadicFiltration N) (hm.toLp F),
    condExp_congr_ae (m := dyadicFiltration N) (MemLp.coeFn_toLp hm), MemLp.coeFn_toLp hm]
    with x h1 h2 h3
  simp only [Pi.sub_apply, h1, h2, h3]

/-- **An integrable function is determined by its Haar coefficients**: if `F ∈ L_1[0, 1]` has
`∫_0^1 F = 0` and `⟨F, h_{k,m}⟩ = 0` for all `k` and `0 ≤ m < 2^k`, then `F = 0` almost everywhere
on `[0, 1]`. Every conditional expectation `E[F | ℱ_N]` vanishes, by `E[F | ℱ_0] = ∫_0^1 F` and the
Haar sums of the martingale differences (`Haar.condExp_zero_ae_eq`,
`Haar.condExp_succ_sub_ae_eq`), and they converge to `F` in `L_1`
(`Haar.tendsto_eLpNorm_condExp_sub`). -/
theorem ae_eq_zero_of_haarCoeff_eq_zero {F : ℝ → ℂ} (hF : Integrable F vol)
    (h0 : ∫ x, F x ∂vol = 0) (h : ∀ k (m : Fin (2 ^ k)), haarCoeff F k ((m : ℕ) : ℤ) = 0) :
    F =ᵐ[vol] 0 := by
  have hE : ∀ N, vol[F | dyadicFiltration N] =ᵐ[vol] 0 := by
    intro N
    induction N with
    | zero =>
      filter_upwards [condExp_zero_ae_eq hF] with x hx
      rw [hx, h0, Pi.zero_apply]
    | succ N ih =>
      filter_upwards [condExp_succ_sub_ae_eq N hF, ih] with x h1 h2
      simp only [h, zero_mul, Finset.sum_const_zero, Pi.sub_apply, h2, Pi.zero_apply,
        sub_zero] at h1 ⊢
      exact h1
  have hconst : ∀ N, eLpNorm (vol[F | dyadicFiltration N] - F) 1 vol = eLpNorm F 1 vol :=
    fun N => by
      rw [eLpNorm_congr_ae ((hE N).sub EventuallyEq.rfl), zero_sub, eLpNorm_neg]
  have h1 : eLpNorm F 1 vol = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun N => (hconst N).symm)
      (tendsto_eLpNorm_condExp_sub hF)
  exact (eLpNorm_eq_zero_iff one_ne_zero).1 h1

/-- **The distance to the conditional expectation by the level norms**: for `0 < p ≤ 1` and
integrable `F`, `‖F - E[F | ℱ_k]‖_p^p ≤ ∑_{i ≥ 0} H_{k+i}(F)^p`. The conditional expectations
converge to `F` in `L_1` (`Haar.tendsto_eLpNorm_condExp_sub`), hence in measure, and their
differences are the Haar sums of one level (`Haar.haarLevelNorm_eq_eLpNorm`), so Fatou's lemma
for telescoping sums applies (`MeasureTheory.eLpNorm_sub_rpow_le_tsum`). -/
theorem eLpNorm_sub_condExp_rpow_le_tsum (hp0 : p ≠ 0) (hp1 : p ≤ 1) {F : ℝ → ℂ}
    (hF : Integrable F vol) (k : ℕ) :
    eLpNorm (F - vol[F | dyadicFiltration k]) p vol ^ p.toReal ≤
      ∑' i, haarLevelNorm p F (k + i) ^ p.toReal := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hu : TendstoInMeasure vol (fun n => vol[F | dyadicFiltration n]) atTop F :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (tendsto_eLpNorm_condExp_sub hF)
  refine (MeasureTheory.eLpNorm_sub_rpow_le_tsum hp0 hp1 hu
    (fun _ => integrable_condExp.aestronglyMeasurable) k).trans_eq (tsum_congr fun i => ?_)
  rw [haarLevelNorm_eq_eLpNorm hp0 hp hF]

/-- **The conditional expectation is a step of level `k`**: `E(2^k, f) ≤ ‖f - E[f | ℱ_k]‖_p` in
the step couple, for every `f ∈ L_p[0, 1]`, since `E[f | ℱ_k]` is `ℱ_k`-measurable and lies in
`L_p` (`Haar.memLp_of_stronglyMeasurable_dyadicFiltration`). -/
theorem eFunctional_stepCouple_le_eLpNorm_sub_condExp (f : Lp ℂ p vol) (k : ℕ) :
    (stepCouple p).eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f ≤
      eLpNorm (⇑f - vol[⇑f | dyadicFiltration k]) p vol := by
  have hm : MemLp (vol[⇑f | dyadicFiltration k]) p vol :=
    memLp_of_stronglyMeasurable_dyadicFiltration stronglyMeasurable_condExp p
  have hb : hm.toLp _ ∈ lpMeasSubgroup ℂ (dyadicFiltration k) p vol :=
    mem_lpMeasSubgroup_iff_aestronglyMeasurable.2
      ⟨_, stronglyMeasurable_condExp, MemLp.coeFn_toLp hm⟩
  rw [eFunctional_stepCouple_two_pow]
  refine (iInf₂_le _ hb).trans_eq ?_
  rw [Lp.eNorm_def]
  exact eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (EventuallyEq.rfl.sub (MemLp.coeFn_toLp hm)))

/-! ### The coefficient characterisation -/

/-- The `p`-th power of the bound of `Haar.haarLevelNorm_rpow_le_tsum_of_nearBest`:
`(2^((i+1)(1/p - 1)) 2^(1/p) x)^p = 2 · 2^(1 - p) · 2^(i(1 - p)) x^p` for `0 < p < ∞`. -/
theorem dyadicWeight_succ_mul_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : ℕ) (x : ℝ≥0∞) :
    (dyadicWeight (1 / p.toReal - 1) (i + 1) * (2 ^ (1 / p.toReal) * x)) ^ p.toReal =
      2 * 2 ^ (1 - p.toReal) * (dyadicWeight (1 - p.toReal) i * x ^ p.toReal) := by
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.mul_rpow_of_nonneg _ _ hρ.le,
    ENNReal.dyadicWeight_rpow, ← ENNReal.rpow_mul, one_div_mul_cancel hρ.ne', ENNReal.rpow_one,
    show (1 / p.toReal - 1) * p.toReal = 1 - p.toReal by field_simp, ENNReal.dyadicWeight_succ]
  ring

/-- **Approximation by steps bounds the Haar coefficients**: for `0 < p ≤ 1`, `s > 1/p - 1`,
`q ≠ 0` and a finite dyadic norm `‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q}`,
`‖(2^(ks) H_k(f))_k‖_{ℓ_q} < ∞`. The near-best steps give
`H_k(f)^p ≤ 2 · 2^(1-p) ∑_{i ≥ 0} 2^(i(1-p)) e_{k+i}^p`
(`Haar.haarLevelNorm_rpow_le_tsum_of_nearBest`), and Hardy's inequality for tails in `ℓ_{q/p}`
with the exponent `sp - (1 - p) > 0` (`ENNReal.lqNorm_rpow_le_of_rpow_le_tsum`) bounds the
`ℓ_q` norm by that of `(2^(ks) e_k)_k`. -/
theorem lqNorm_haarLevelNorm_lt_top (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 1 / p.toReal - 1 < s)
    (hq0 : q ≠ 0) {f : Lp ℂ p vol} (hN : (stepCouple p).eNormDyadic s q f < ∞) :
    lqNorm q (fun k => dyadicWeight s k * haarLevelNorm p f k) < ∞ := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  set ρ := p.toReal with hρdef
  have hρ : 0 < ρ := ENNReal.toReal_pos hp0 hp
  have hs0 := pos_of_one_div_sub_one_lt hp0 hp1 hs
  obtain ⟨b, hb, hbe⟩ := exists_nearBest_stepCouple f s
  set e : ℕ → ℝ≥0∞ := fun j =>
    (stepCouple p).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) f + ‖f‖ₑ * dyadicWeight (-(s + 1)) j
  set L := lqNorm q (fun k => dyadicWeight s k * e k)
  have hLt : L ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.LpAddConst_lt_top q).ne (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.dyadicGeomConst_ne_top one_pos q⟩)) hN.ne)
    (InterpCouple.lqNorm_dyadicWeight_mul_eFunctional_add_le (stepCouple p) s q f)
  have hsum : ∑' i, dyadicWeight (1 / ρ - 1) (i + 1) * (2 ^ (1 / ρ) * e i) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.two_rpow_ne_top _) (ENNReal.two_rpow_ne_top _))
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith))) hLt)
      (tsum_dyadicWeight_succ_mul_le_lqNorm hq0 e)
  have hk : ∀ k, haarLevelNorm p f k ^ ρ ≤
      2 * 2 ^ (1 - ρ) * ∑' i, dyadicWeight (1 - ρ) i * e (k + i) ^ ρ := fun k =>
    (haarLevelNorm_rpow_le_tsum_of_nearBest hp0 hp1 hb hbe
      (antitone_eFunctional_stepCouple_add (by linarith) f)
      (ENNReal.tendsto_zero_of_lqNorm_dyadicWeight_ne_top hq0 hs0 hLt) hsum k).trans_eq (by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun i => dyadicWeight_succ_mul_rpow hp0 hp i _)
  have hα : 0 < s * ρ - (1 - ρ) := by
    have h := mul_lt_mul_of_pos_right hs hρ
    rw [sub_mul, one_div_mul_cancel hρ.ne', one_mul] at h
    linarith
  rw [← ENNReal.rpow_lt_top_iff_of_pos hρ]
  refine (ENNReal.lqNorm_rpow_le_of_rpow_le_tsum hρ hk s q).trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofNat_lt_top
      (ENNReal.two_rpow_ne_top _).lt_top) (ENNReal.hardyConst_ne_top hα _).lt_top)
    (ENNReal.rpow_lt_top_of_nonneg hρ.le hLt))

/-- **The Haar coefficients bound the approximation by steps**: for `0 < p ≤ 1`, `s > 0`,
integrable `f ∈ L_p[0, 1]` and `‖(2^(ks) H_k(f))_k‖_{ℓ_q} < ∞`, the dyadic norm
`‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q}` is finite. With `E(2^k, f)^p ≤ ‖f - E[f | ℱ_k]‖_p^p ≤
∑_{i ≥ 0} H_{k+i}(f)^p` (`Haar.eFunctional_stepCouple_le_eLpNorm_sub_condExp`,
`Haar.eLpNorm_sub_condExp_rpow_le_tsum`), Hardy's inequality for tails in `ℓ_{q/p}` with the
exponent `sp` (`ENNReal.lqNorm_rpow_le_of_rpow_le_tsum`) applies. -/
theorem eNormDyadic_lt_top_of_lqNorm_haarLevelNorm (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 0 < s)
    {f : Lp ℂ p vol} (hf : Integrable f vol)
    (hH : lqNorm q (fun k => dyadicWeight s k * haarLevelNorm p f k) < ∞) :
    (stepCouple p).eNormDyadic s q f < ∞ := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hk : ∀ k, (stepCouple p).eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f ^ p.toReal ≤
      1 * ∑' i, dyadicWeight 0 i * haarLevelNorm p f (k + i) ^ p.toReal := fun k => by
    simp only [ENNReal.dyadicWeight_zero_left, one_mul]
    exact (ENNReal.rpow_le_rpow (eFunctional_stepCouple_le_eLpNorm_sub_condExp f k) hρ.le).trans
      (eLpNorm_sub_condExp_rpow_le_tsum hp0 hp1 hf k)
  have hE := (ENNReal.lqNorm_rpow_le_of_rpow_le_tsum hρ hk s q).trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.one_lt_top (ENNReal.hardyConst_ne_top (by
      rw [sub_zero]; positivity) _).lt_top) (ENNReal.rpow_lt_top_of_nonneg hρ.le hH.ne))
  rw [ENNReal.rpow_lt_top_iff_of_pos hρ] at hE
  exact ENNReal.add_lt_top.2 ⟨(Lp.eLpNorm_lt_top f).trans_eq' (Lp.eNorm_def f).symm, hE⟩

variable (p) in
/-- The weight of the Haar coefficient condition is the level norm:
`2^(k(s + 1/2 - 1/p)) ‖(⟨f, h_{k,m}⟩)_m‖_{ℓ_p} = 2^(ks) H_k(f)`. -/
theorem dyadicWeight_mul_lqNorm_haarCoeff (s : ℝ) (f : ℝ → ℂ) (k : ℕ) :
    dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
      lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ) =
        dyadicWeight s k * haarLevelNorm p f k := by
  rw [ENNReal.dyadicWeight_add, mul_assoc]
  rfl

/-- **Besov spaces for `0 < p ≤ 1` through Haar coefficients.** For `0 < p ≤ 1`, `s > 1/p - 1`
and `q ≠ 0`, `f ∈ L_p[0, 1]` lies in the approximation space `E_{s,q}` of the step couple
(`A^s_q(L_p, steps)`) iff `f ∈ L_1[0, 1]` and
`|∫_0^1 f| + ‖(2^(k(s + 1/2 - 1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`. The
integrability comes from `s > 1/p - 1` (`Haar.integrable_of_eNormDyadic_lt_top`), and Haar
coefficients are defined through `L_1`; the two directions are
`Haar.lqNorm_haarLevelNorm_lt_top` and `Haar.eNormDyadic_lt_top_of_lqNorm_haarLevelNorm`. For
`1/p - 1 < s < 1/p` the space is `B^s_{p,q,1}[0, 1]` of the first modulus
(`Haar.lqNorm_modulus_lt_top_iff_haarCoeff_of_le_one`). -/
theorem memEMethod_stepCouple_iff_haarCoeff (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hs : 1 / p.toReal - 1 < s) (hq0 : q ≠ 0) (f : Lp ℂ p vol) :
    (stepCouple p).MemEMethod s q f ↔ Integrable f vol ∧ ‖∫ x, f x ∂vol‖ₑ +
      lqNorm q (fun k => dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
        lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)) < ∞ := by
  have hs0 := pos_of_one_div_sub_one_lt hp0 hp1 hs
  simp only [dyadicWeight_mul_lqNorm_haarCoeff p s, ENNReal.add_lt_top, eNorm_lt_top, true_and]
  rw [InterpCouple.memEMethod_iff_eNormDyadic_lt_top (A := stepCouple p)
    InterpCouple.ofMonotoneSubgroups_norm1_zero
    (fun _ hb => InterpCouple.eq_zero_of_ofMonotoneSubgroups_norm1_lt_one hb) hs0.le
    (Or.inl hs0) hq0]
  exact ⟨fun hN => ⟨integrable_of_eNormDyadic_lt_top hp0 hp1 hs hq0 hN,
    lqNorm_haarLevelNorm_lt_top hp0 hp1 hs hq0 hN⟩,
    fun ⟨hf, hH⟩ => eNormDyadic_lt_top_of_lqNorm_haarLevelNorm hp0 hp1 hs0 hf hH⟩

/-- **Besov spaces of the first modulus for `0 < p ≤ 1` through Haar coefficients.** For
`0 < p ≤ 1`, `q ≠ 0` and `1/p - 1 < s < 1/p`, `f ∈ L_p[0, 1]` has
`‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞` iff `f ∈ L_1[0, 1]` and
`|∫_0^1 f| + ‖(2^(k(s + 1/2 - 1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`: both say that
`f` lies in `E_{s,q}` of the step couple (`Haar.memEMethod_stepCouple_iff_modulus`,
`Haar.memEMethod_stepCouple_iff_haarCoeff`). -/
theorem lqNorm_modulus_lt_top_iff_haarCoeff_of_le_one (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hs : 1 / p.toReal - 1 < s) (hsp : s < 1 / p.toReal) (hq0 : q ≠ 0) (f : Lp ℂ p vol) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Interval.intervalLpModulus p 1 f k) < ∞ ↔
      Integrable f vol ∧ ‖∫ x, f x ∂vol‖ₑ +
        lqNorm q (fun k => dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
          lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)) < ∞ :=
  (memEMethod_stepCouple_iff_modulus hp0 hp1 hq0 (pos_of_one_div_sub_one_lt hp0 hp1 hs) hsp
    f).symm.trans (memEMethod_stepCouple_iff_haarCoeff hp0 hp1 hs hq0 f)

end Haar
