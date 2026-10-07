/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.Smoothing
public import FunctionSpaces.Rd.Differences

/-!
# Steklov smoothing on the whole line

For a continuous `f : ℝ → ℂ`, an order `r ∈ ℕ` and a step `δ > 0`, the **Steklov smoothing**
`S_δ f = ∑_{k=1}^r (-1)^(k+1) C(r, k) M_{kδ}^r f` (`Interval.smooth`, defined pointwise on all of
`ℝ` from the Steklov averages `M_η g(x) = η^(-1) ∫_0^η g(x + τ) dτ`) is `r` times continuously
differentiable (`Interval.contDiff_smooth`). On all of `ℝ` it is controlled by the modulus of
smoothness of the line, `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_{L_p(ℝ)}` (`Rd.modulus volume`):

* `‖f - S_δ f‖_{L_p(ℝ)} ≤ ω_r(f, rδ)_p` for `1 ≤ p < ∞`
  (`Daubechies.eLpNorm_sub_smooth_le_modulus`);
* `‖(S_δ f)^(r)‖_{L_p(ℝ)} ≤ 2^r δ^(-r) ω_r(f, rδ)_p` for `1 ≤ p ≤ ∞`
  (`Daubechies.eLpNorm_iteratedDeriv_smooth_le_modulus`).

The proofs are those of the interval versions `Interval.eLpNorm_sub_smooth_le` and
`Interval.eLpNorm_iteratedDeriv_smooth_le`, with Lebesgue measure on `ℝ` in place of its
restriction to an interval. The difference `f - S_δ f` is `(-1)^r` times the average of
`Δ^r_{v_1 + ⋯ + v_r} f` over `v ∈ [0, δ]^r` (`Interval.sub_smooth_eq`), so Minkowski's inequality
for averages (`Interval.eLpNorm_avgStepIter_le`) bounds it by the differences with steps
`0 ≤ h ≤ rδ`. The derivative is the combination
`(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r, k) (kδ)^(-r) Δ_{kδ}^r f`
(`Daubechies.iteratedDeriv_smooth_eq_sum_smul`), bounded term by term
(`Daubechies.eLpNorm_smul_higherDiff_le_modulus`) with `∑_{k=1}^r C(r, k) ≤ 2^r`.

At the dyadic step `δ = 1/(N 2^j)`, where `Nδ = 2^(-j)` and `δ^(-N) = N^N 2^(jN)`, the two
bounds read `‖f - S_δ f‖_p ≤ ω_N(f, 2^(-j))_p` and
`‖(S_δ f)^(N)‖_p ≤ 2^N N^N 2^(jN) ω_N(f, 2^(-j))_p` (`Daubechies.eLpNorm_sub_smooth_le_dyadic`,
`Daubechies.eLpNorm_iteratedDeriv_smooth_le_dyadic`), and for `f ∈ L_p` both `S_δ f` and
`(S_δ f)^(r)` lie in `L_p` (`Daubechies.memLp_smooth`, `Daubechies.memLp_iteratedDeriv_smooth`).
These are the smoothing steps of Jackson's inequality for the Daubechies projections.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Daubechies

/-! ### The two smoothing estimates on the line -/

/-- **Differences with a nonnegative step are bounded by the modulus**: for `0 ≤ h ≤ t`,
`‖Δ_h^r f‖_{L_p(ℝ)} ≤ ω_r(f, t)_p`, where `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_{L_p(ℝ)}` is the
modulus of smoothness of the line (`Rd.modulus volume`). -/
theorem eLpNorm_higherDiff_le_modulus_of_nonneg {r : ℕ} {p : ℝ≥0∞} {f : ℝ → ℂ} {h t : ℝ}
    (h0 : 0 ≤ h) (ht : h ≤ t) :
    eLpNorm (Rd.higherDiff r h f) p volume ≤ Rd.modulus volume r p f t :=
  Rd.eLpNorm_higherDiff_le_modulus (by rwa [Real.norm_of_nonneg h0])

/-- **The smoothing is close to `f` on the whole line**: for continuous `f : ℝ → ℂ`, `r ∈ ℕ`,
`δ > 0` and `1 ≤ p < ∞`,
`‖f - S_δ f‖_{L_p(ℝ)} ≤ ω_r(f, rδ)_p`.
Indeed `f - S_δ f = (-1)^r avg_{v ∈ [0, δ]^r} Δ^r_{v_1 + ⋯ + v_r} f` (`Interval.sub_smooth_eq`),
and Minkowski's inequality for averages (`Interval.eLpNorm_avgStepIter_le`, stated for
`p < ∞`) bounds its norm by the supremum of `‖Δ_h^r f‖_{L_p(ℝ)}` over `0 ≤ h ≤ rδ`. -/
theorem eLpNorm_sub_smooth_le_modulus {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => f x - Interval.smooth r δ f x) p volume ≤
      Rd.modulus volume r p f (r * δ) := by
  have heq : (fun x => f x - Interval.smooth r δ f x) = ((-1 : ℂ) ^ r) •
      Interval.avgStepIter r δ (fun h y => Rd.higherDiff r h f y) 0 := by
    funext x
    rw [Interval.sub_smooth_eq hf r hδ.ne' x]
    rfl
  rw [heq, eLpNorm_const_smul, enorm_pow, enorm_neg, enorm_one, one_pow, one_mul]
  refine (Interval.eLpNorm_avgStepIter_le (Interval.continuous_higherDiff_uncurry hf r) hδ hp
    hp' volume r 0).trans (iSup₂_le fun h hh => ?_)
  rw [zero_add] at hh
  exact eLpNorm_higherDiff_le_modulus_of_nonneg hh.1 hh.2

/-- `∑_{k=1}^r C(r, k) ≤ 2^r`, written with the index `k + 1` for `k < r`: the full sum
`∑_{k=0}^r C(r, k)` is `2^r` (Mathlib's `Nat.sum_range_choose`). -/
theorem sum_range_choose_succ_le (r : ℕ) :
    ∑ k ∈ Finset.range r, (r.choose (k + 1) : ℝ≥0∞) ≤ 2 ^ r := by
  have h := Nat.sum_range_choose r
  rw [Finset.sum_range_succ'] at h
  have h' : ∑ k ∈ Finset.range r, r.choose (k + 1) ≤ 2 ^ r := by omega
  exact_mod_cast h'

/-- **The derivative of the smoothing as a sum of functions**: for continuous `f : ℝ → ℂ`,
`(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r, k) (kδ)^(-r) Δ_{kδ}^r f`
as an identity of functions `ℝ → ℂ` (`Interval.iteratedDeriv_smooth` at every point), written
with the index `k + 1` for `k < r` and as a sum `∑_k c_k • g_k`, the form to which the triangle
inequality in `L_p` applies. -/
theorem iteratedDeriv_smooth_eq_sum_smul {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ) :
    iteratedDeriv r (Interval.smooth r δ f) = ∑ k ∈ Finset.range r,
      (((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • Rd.higherDiff r ((k + 1 : ℕ) * δ) f := by
  rw [Interval.iteratedDeriv_smooth hf r δ]
  funext x
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

/-- **One term of the derivative of the smoothing**: for `1 ≤ k ≤ r` (written `k + 1` with
`k < r`) and `δ > 0`,
`‖(-1)^(k+1) C(r, k) (kδ)^(-r) Δ_{kδ}^r f‖_{L_p(ℝ)} ≤ C(r, k) δ^(-r) ω_r(f, rδ)_p`,
since `(kδ)^(-r) ≤ δ^(-r)` and `0 ≤ kδ ≤ rδ`. -/
theorem eLpNorm_smul_higherDiff_le_modulus {f : ℝ → ℂ} {r k : ℕ} (hk : k < r) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} :
    eLpNorm ((((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
      (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • Rd.higherDiff r ((k + 1 : ℕ) * δ) f) p volume ≤
      (r.choose (k + 1) : ℝ≥0∞) *
        ((ENNReal.ofReal δ)⁻¹ ^ r * Rd.modulus volume r p f (r * δ)) := by
  have hkr : ((k + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  rw [eLpNorm_const_smul, enorm_mul, enorm_mul, enorm_pow, enorm_neg, enorm_one, one_pow,
    one_mul, mul_assoc]
  gcongr
  · rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
  · rw [enorm_pow, ← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
    gcongr
    exact le_mul_of_one_le_left hδ.le hk1
  · exact eLpNorm_higherDiff_le_modulus_of_nonneg (by positivity)
      (mul_le_mul_of_nonneg_right hkr hδ.le)

/-- **The derivative of order `r` of the smoothing on the whole line**: for continuous
`f : ℝ → ℂ`, `r ∈ ℕ`, `δ > 0` and `1 ≤ p ≤ ∞`,
`‖(S_δ f)^(r)‖_{L_p(ℝ)} ≤ 2^r δ^(-r) ω_r(f, rδ)_p`,
by the triangle inequality for `(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r, k) (kδ)^(-r) Δ_{kδ}^r f`
and `∑_{k=1}^r C(r, k) ≤ 2^r`. -/
theorem eLpNorm_iteratedDeriv_smooth_le_modulus {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (iteratedDeriv r (Interval.smooth r δ f)) p volume ≤
      2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * Rd.modulus volume r p f (r * δ) := by
  rw [iteratedDeriv_smooth_eq_sum_smul hf r δ]
  refine ((eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun k hk =>
    eLpNorm_smul_higherDiff_le_modulus (Finset.mem_range.1 hk) hδ)).trans ?_
  rw [← Finset.sum_mul, mul_assoc]
  gcongr
  exact sum_range_choose_succ_le r

/-! ### The dyadic step `δ = 1/(N 2^j)` -/

/-- **The smoothing at a dyadic scale is close to `f`**: for continuous `f : ℝ → ℂ`, `N ≥ 1`,
`j ∈ ℕ`, `1 ≤ p < ∞` and the step `δ = 1/(N 2^j)`,
`‖f - S_δ f‖_{L_p(ℝ)} ≤ ω_N(f, 2^(-j))_p`.
This is `eLpNorm_sub_smooth_le_modulus` with `r = N`, since `Nδ = 2^(-j)`. -/
theorem eLpNorm_sub_smooth_le_dyadic {f : ℝ → ℂ} (hf : Continuous f) {N : ℕ} (hN : 0 < N)
    (j : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => f x - Interval.smooth N (1 / (N * 2 ^ j)) f x) p volume ≤
      Rd.modulus volume N p f (1 / 2 ^ j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < 1 / (N * 2 ^ j) := div_pos one_pos (mul_pos hN' (pow_pos two_pos j))
  have hNδ : (N : ℝ) * (1 / (N * 2 ^ j)) = 1 / 2 ^ j := by field_simp
  have h := eLpNorm_sub_smooth_le_modulus hf N hδ hp hp'
  rwa [hNδ] at h

/-- **The derivative of the smoothing at a dyadic scale**: for continuous `f : ℝ → ℂ`, `N ≥ 1`,
`j ∈ ℕ`, `1 ≤ p ≤ ∞` and the step `δ = 1/(N 2^j)`,
`‖(S_δ f)^(N)‖_{L_p(ℝ)} ≤ 2^N N^N 2^(jN) ω_N(f, 2^(-j))_p`.
This is `eLpNorm_iteratedDeriv_smooth_le_modulus` with `r = N`, since `δ^(-N) = N^N 2^(jN)`
and `Nδ = 2^(-j)`. -/
theorem eLpNorm_iteratedDeriv_smooth_le_dyadic {f : ℝ → ℂ} (hf : Continuous f) {N : ℕ}
    (hN : 0 < N) (j : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (iteratedDeriv N (Interval.smooth N (1 / (N * 2 ^ j)) f)) p volume ≤
      2 ^ N * (N : ℝ≥0∞) ^ N * 2 ^ (j * N) * Rd.modulus volume N p f (1 / 2 ^ j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < 1 / (N * 2 ^ j) := div_pos one_pos (mul_pos hN' (pow_pos two_pos j))
  have hNδ : (N : ℝ) * (1 / (N * 2 ^ j)) = 1 / 2 ^ j := by field_simp
  have hinv : (ENNReal.ofReal (1 / (N * 2 ^ j)))⁻¹ ^ N = (N : ℝ≥0∞) ^ N * 2 ^ (j * N) := by
    rw [← ENNReal.ofReal_inv_of_pos hδ, one_div, inv_inv, ENNReal.ofReal_mul hN'.le,
      ENNReal.ofReal_natCast, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, mul_pow,
      ← pow_mul]
  have h := eLpNorm_iteratedDeriv_smooth_le_modulus hf N hδ hp
  rwa [hinv, hNδ, ← mul_assoc] at h

/-! ### `L_p` membership -/

/-- **The smoothing of an `L_p` function lies in `L_p`**: for continuous `f ∈ L_p(ℝ)`, `r ∈ ℕ`,
`δ > 0` and `1 ≤ p < ∞`, also `S_δ f ∈ L_p(ℝ)`, because
`‖f - S_δ f‖_p ≤ ω_r(f, rδ)_p ≤ 2^r ‖f‖_p` (`Rd.modulus_le`). -/
theorem memLp_smooth {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : Continuous f) (hfp : MemLp f p volume)
    (r : ℕ) {δ : ℝ} (hδ : 0 < δ) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    MemLp (Interval.smooth r δ f) p volume := by
  have hsub : MemLp (fun x => f x - Interval.smooth r δ f x) p volume := memLp_iff.2 <|
    calc eLpNorm (fun x => f x - Interval.smooth r δ f x) p volume
        ≤ Rd.modulus volume r p f (r * δ) := eLpNorm_sub_smooth_le_modulus hf r hδ hp hp'
      _ ≤ 2 ^ r * eLpNorm f p volume := Rd.modulus_le hf.aestronglyMeasurable hp r _
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfp.eLpNorm_lt_top
  have heq : Interval.smooth r δ f = f - fun x => f x - Interval.smooth r δ f x := by
    funext x
    simp
  rw [heq]
  exact hfp.sub hsub

/-- **The derivative of the smoothing of an `L_p` function lies in `L_p`**: for continuous
`f ∈ L_p(ℝ)`, `r ∈ ℕ`, `δ > 0` and `1 ≤ p ≤ ∞`, also `(S_δ f)^(r) ∈ L_p(ℝ)`, because
`‖(S_δ f)^(r)‖_p ≤ 2^r δ^(-r) ω_r(f, rδ)_p ≤ 4^r δ^(-r) ‖f‖_p`. -/
theorem memLp_iteratedDeriv_smooth {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : Continuous f)
    (hfp : MemLp f p volume) (r : ℕ) {δ : ℝ} (hδ : 0 < δ) (hp : 1 ≤ p) :
    MemLp (iteratedDeriv r (Interval.smooth r δ f)) p volume := by
  have h2 : (2 : ℝ≥0∞) ^ r < ∞ := ENNReal.pow_lt_top ENNReal.ofNat_lt_top
  have hinv : (ENNReal.ofReal δ)⁻¹ < ∞ := ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hδ)
  refine memLp_iff.2 ?_
  calc eLpNorm (iteratedDeriv r (Interval.smooth r δ f)) p volume
      ≤ 2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * Rd.modulus volume r p f (r * δ) :=
        eLpNorm_iteratedDeriv_smooth_le_modulus hf r hδ hp
    _ ≤ 2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * (2 ^ r * eLpNorm f p volume) := by
        gcongr
        exact Rd.modulus_le hf.aestronglyMeasurable hp r _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top h2 (ENNReal.pow_lt_top hinv))
        (ENNReal.mul_lt_top h2 hfp.eLpNorm_lt_top)

end Daubechies
