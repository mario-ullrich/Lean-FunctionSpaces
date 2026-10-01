/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.PiecewisePoly
public import FunctionSpaces.Interval.Smoothing
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Jackson's inequality for dyadic piecewise polynomials

For `1 ≤ p < ∞`, `r ≥ 1` and `k ≥ 1`, the error of best approximation in `L_p[0, 1]` by
piecewise polynomials of level `k` and degree `< r` is bounded by the modulus of smoothness,
`E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p`
(`Interval.approxSeq_ppScheme_le`).

The proof uses no Whitney theorem. For continuous `f`, the Steklov smoothing `S_δ f` with
`δ = 2^(-k) / r²` is close to `f` and its `r`-th derivative is bounded by `δ^(-r)` times the
modulus (`Interval.eLpNorm_sub_smooth_le`, `Interval.eLpNorm_iteratedDeriv_smooth_le`); on each
dyadic interval it is approximated by a polynomial (`Interval.exists_eLpNorm_sub_polyFun_le`).
The smoothing looks to the right of `x`, so this argument covers `[0, 1/2]`
(`Interval.exists_left_approx`); the reflection `x ↦ 1 - x` preserves the modulus and gives
`[1/2, 1]` (`Interval.exists_right_approx`). The point `1/2` is a knot of every level `k ≥ 1`,
which is why `k ≥ 1`. General `f ∈ L_p` follow by density of bounded continuous functions.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The constant of the local Jackson estimate, `1 + 2^r r^(2r)`. -/
noncomputable def jacksonConst (r : ℕ) : ℝ≥0∞ := 1 + 2 ^ r * (r : ℝ≥0∞) ^ (2 * r)

/-- The local Jackson constant is finite. -/
theorem jacksonConst_ne_top (r : ℕ) : jacksonConst r ≠ ∞ := by
  unfold jacksonConst
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (by simp)
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))⟩

/-- **Local Jackson estimate on the left half**: for continuous `F` there are polynomials `Q_n`
of degree `< r` such that every function `S` equal to `Q_n` on the open dyadic intervals of level
`k + 1` in `[0, 1/2]` satisfies
`‖F - S‖_{L_p[0, 1/2]} ≤ (1 + 2^r r^(2r)) ω_r(F, 2^(-(k+1)), [0, 1])_p`.
The proof smooths `F` by `S_δ`, `δ = 2^(-(k+1)) / r²`, and approximates `S_δ F` by Taylor
polynomials on each dyadic interval. -/
theorem exists_left_approx {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (k : ℕ) :
    ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ ∀ S : ℝ → ℂ, Measurable S →
      (∀ n : ℕ, n < 2 ^ k → ∀ x ∈ Ioo ((n : ℝ) / 2 ^ (k + 1)) ((n + 1) / 2 ^ (k + 1)),
        S x = polyFun (Q n) x) →
      eLpNorm (fun x => F x - S x) p (volume.restrict (Icc 0 (1 / 2))) ≤
        jacksonConst r * modulus r p 0 1 F (1 / 2 ^ (k + 1)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  set L : ℝ := 1 / 2 ^ (k + 1) with hLdef
  have hL : 0 < L := by positivity
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set δ : ℝ := L / r ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hrδ : (r : ℝ) * δ ≤ L := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hrr : (r : ℝ) ≤ r ^ 2 := by nlinarith
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hL2 : (2 ^ k : ℕ) * L = 1 / 2 := by
    rw [hLdef]; push_cast; field_simp; ring
  set g := smooth r δ F
  have hg : ContDiff ℝ r g := contDiff_smooth hF r δ
  choose Q hQ hQb using fun n : ℕ => exists_eLpNorm_sub_polyFun_le hp r hg
    (u := n * L) (v := (n + 1) * L) (by nlinarith)
  refine ⟨Q, hQ, fun S hS hSQ => ?_⟩
  set ω := modulus r p 0 1 F L
  have hdom : (1 / 2 : ℝ) + r * (r * δ) ≤ 1 := by
    have : (r : ℝ) * (r * δ) = L := by rw [hδdef]; field_simp
    rw [this, hLdef]
    have : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ≤ 2 ^ (k + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  have hmod : modulus r p 0 1 F (r * δ) ≤ ω := modulus_mono r p 0 1 F hrδ
  -- the smoothing error
  have h1 : eLpNorm (fun x => F x - g x) p (volume.restrict (Icc 0 (1 / 2))) ≤ ω :=
    (eLpNorm_sub_smooth_le hF r hδ hp hp' le_rfl hdom).trans hmod
  -- the derivative of the smoothing
  have h2 : eLpNorm (iteratedDeriv r g) p (volume.restrict (Icc 0 (1 / 2))) ≤
      2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * ω :=
    (eLpNorm_iteratedDeriv_smooth_le hF r hδ hp le_rfl hdom).trans (by gcongr)
  have hgm : Measurable g := hg.continuous.measurable
  have hderm : Measurable (iteratedDeriv r g) :=
    (hg.continuous_iteratedDeriv r le_rfl).measurable
  -- the Taylor error, summed over the dyadic intervals
  have h3 : eLpNorm (fun x => g x - S x) p (volume.restrict (Icc 0 (1 / 2))) ≤
      ENNReal.ofReal L ^ r * eLpNorm (iteratedDeriv r g) p (volume.restrict (Icc 0 (1 / 2))) := by
    refine eLpNorm_le_of_lintegral_le (hgm.sub hS).aestronglyMeasurable hp0 hp' ?_
    have hsplit := lintegral_Icc_le_sum (fun x => ‖g x - S x‖ₑ ^ p.toReal) 0 hL.le (2 ^ k)
    rw [zero_add, hL2] at hsplit
    refine hsplit.trans ?_
    have hpiece : ∀ n ∈ Finset.range (2 ^ k),
        ∫⁻ x in Icc (0 + n * L) (0 + (n + 1) * L), ‖g x - S x‖ₑ ^ p.toReal ≤
          (ENNReal.ofReal L ^ r) ^ p.toReal *
            ∫⁻ x in Icc (0 + n * L) (0 + (n + 1) * L), ‖iteratedDeriv r g x‖ₑ ^ p.toReal :=
      fun n hn => by
        simp only [zero_add]
        have hae : ∀ᵐ x ∂volume.restrict (Icc (n * L) ((n + 1) * L)),
            ‖g x - S x‖ₑ ^ p.toReal = ‖g x - polyFun (Q n) x‖ₑ ^ p.toReal := by
          rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
          rw [hSQ n (Finset.mem_range.1 hn) x (by
            constructor
            · rw [hLdef] at hx; have := hx.1; field_simp at this ⊢; linarith
            · rw [hLdef] at hx; have := hx.2; field_simp at this ⊢; linarith)]
        rw [lintegral_congr_ae hae, ← eLpNorm_rpow_eq (g := fun x => g x - polyFun (Q n) x)
          ((hgm.sub (measurable_polyFun _)).aestronglyMeasurable) hp0 hp',
          ← eLpNorm_rpow_eq hderm.aestronglyMeasurable hp0 hp',
          ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
        have hlen : ((n : ℝ) + 1) * L - n * L = L := by ring
        have hb := hQb n
        rw [hlen] at hb
        exact ENNReal.rpow_le_rpow hb hq.le
    refine (Finset.sum_le_sum hpiece).trans ?_
    rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      eLpNorm_rpow_eq hderm.aestronglyMeasurable hp0 hp']
    gcongr
    have := sum_le_lintegral_Icc (G := fun x => ‖iteratedDeriv r g x‖ₑ ^ p.toReal) 0 hL.le (2 ^ k)
    rw [zero_add, hL2] at this
    exact this
  have hLδ : ENNReal.ofReal L ^ r * (2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * ω) =
      2 ^ r * (r : ℝ≥0∞) ^ (2 * r) * ω := by
    have : ENNReal.ofReal L * (ENNReal.ofReal δ)⁻¹ = (r : ℝ≥0∞) ^ 2 := by
      rw [← ENNReal.ofReal_inv_of_pos hδ, ← ENNReal.ofReal_mul hL.le, hδdef]
      rw [show L * (L / (r : ℝ) ^ 2)⁻¹ = (r : ℝ) ^ 2 by field_simp]
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
    calc ENNReal.ofReal L ^ r * (2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * ω)
        = 2 ^ r * (ENNReal.ofReal L * (ENNReal.ofReal δ)⁻¹) ^ r * ω := by rw [mul_pow]; ring
      _ = _ := by rw [this, ← pow_mul]
  calc eLpNorm (fun x => F x - S x) p (volume.restrict (Icc 0 (1 / 2)))
      = eLpNorm ((fun x => F x - g x) + fun x => g x - S x) p
          (volume.restrict (Icc 0 (1 / 2))) := by congr 1; funext x; simp
    _ ≤ eLpNorm (fun x => F x - g x) p (volume.restrict (Icc 0 (1 / 2))) +
          eLpNorm (fun x => g x - S x) p (volume.restrict (Icc 0 (1 / 2))) :=
        eLpNorm_add_le hp
    _ ≤ ω + ENNReal.ofReal L ^ r * (2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * ω) :=
        add_le_add h1 (h3.trans (by gcongr))
    _ = jacksonConst r * ω := by rw [hLδ, jacksonConst]; ring

/-- **Local Jackson estimate on the right half**, by reflection: for continuous `F` there are
polynomials `Q_n` of degree `< r` such that every `S` with `S(1 - x) = Q_n(x)` on the open
dyadic intervals of level `k + 1` in `[0, 1/2]` satisfies
`‖F - S‖_{L_p[1/2, 1]} ≤ (1 + 2^r r^(2r)) ω_r(F, 2^(-(k+1)), [0, 1])_p`. -/
theorem exists_right_approx {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (k : ℕ) :
    ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ ∀ S : ℝ → ℂ, Measurable S →
      (∀ n : ℕ, n < 2 ^ k → ∀ x ∈ Ioo ((n : ℝ) / 2 ^ (k + 1)) ((n + 1) / 2 ^ (k + 1)),
        S (1 - x) = polyFun (Q n) x) →
      eLpNorm (fun x => F x - S x) p (volume.restrict (Icc (1 / 2) 1)) ≤
        jacksonConst r * modulus r p 0 1 F (1 / 2 ^ (k + 1)) := by
  have hF' : Continuous fun x => F (1 - x) := hF.comp (continuous_const.sub continuous_id)
  obtain ⟨Q, hQ, hQS⟩ := exists_left_approx hF' hr hp hp' k
  refine ⟨Q, hQ, fun S hS hSQ => ?_⟩
  have hS' : Measurable fun x => S (1 - x) := hS.comp (measurable_const.sub measurable_id)
  have h := hQS (fun x => S (1 - x)) hS' hSQ
  have hrefl : eLpNorm (fun x => F x - S x) p (volume.restrict (Icc (1 / 2) 1)) =
      eLpNorm (fun x => F (1 - x) - S (1 - x)) p (volume.restrict (Icc 0 (1 / 2))) := by
    rw [eLpNorm_comp_sub_Icc (f := fun x => F x - S x) (hF.measurable.sub hS) p 1 0 (1 / 2)]
    norm_num
  have hmod : modulus r p 0 1 (fun x => F (1 - x)) (1 / 2 ^ (k + 1)) =
      modulus r p 0 1 F (1 / 2 ^ (k + 1)) := by
    have := modulus_reflect hF.measurable r p 0 1 (1 / 2 ^ (k + 1))
    simpa using this
  rw [hrefl, ← hmod]
  exact h

/-- Splitting `[a, c]` at `b`: `‖G‖_{L_p[a,c]} ≤ ‖G‖_{L_p[a,b]} + ‖G‖_{L_p[b,c]}`. -/
theorem eLpNorm_Icc_split {G : ℝ → ℂ} (hG : Measurable G) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    eLpNorm G p (volume.restrict (Icc a c)) ≤
      eLpNorm G p (volume.restrict (Icc a b)) + eLpNorm G p (volume.restrict (Icc b c)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp' hp; rwa [ENNReal.toReal_one] at this
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hG.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hG.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hG.aestronglyMeasurable,
    ← Icc_union_Icc_eq_Icc hab hbc]
  refine le_trans (ENNReal.rpow_le_rpow (lintegral_union_le _ _ _) (by positivity)) ?_
  have := ENNReal.rpow_add_rpow_le_add
    ((∫⁻ x in Icc a b, ‖G x‖ₑ ^ p.toReal) ^ (1 / p.toReal))
    ((∫⁻ x in Icc b c, ‖G x‖ₑ ^ p.toReal) ^ (1 / p.toReal)) hq1
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel (by linarith),
    ENNReal.rpow_one, ENNReal.rpow_one] at this

/-- **Jackson's estimate for continuous functions**: for continuous `F` and `k ≥ 0` there is a
piecewise polynomial `S` of level `k + 1` and degree `< r` with
`‖F - S‖_{L_p[0,1]} ≤ 2 (1 + 2^r r^(2r)) ω_r(F, 2^(-(k+1)), [0, 1])_p`. -/
theorem exists_ppFun_approx {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (k : ℕ) :
    ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧
      eLpNorm (fun x => F x - ppFun (k + 1) Q x) p unitVol ≤
        2 * jacksonConst r * modulus r p 0 1 F (1 / 2 ^ (k + 1)) := by
  obtain ⟨Ql, hQl, hl⟩ := exists_left_approx hF hr hp hp' k
  obtain ⟨Qr, hQr, hrt⟩ := exists_right_approx hF hr hp hp' k
  set Q : ℕ → ℂ[X] := fun m => if m < 2 ^ k then Ql m else
    (Qr (2 ^ (k + 1) - 1 - m)).comp (C ((1 : ℝ) : ℂ) + C ((-1 : ℝ) : ℂ) * X)
  have hQ : ∀ m, Q m ∈ degreeLT ℂ r := fun m => by
    simp only [Q]
    split_ifs
    · exact hQl m
    · exact comp_affine_mem_degreeLT (hQr _) _ _
  refine ⟨Q, hQ, ?_⟩
  have hSm : Measurable (ppFun (k + 1) Q) := measurable_ppFun _ _
  have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
  have hleft : ∀ n : ℕ, n < 2 ^ k → ∀ x ∈ Ioo ((n : ℝ) / 2 ^ (k + 1)) ((n + 1) / 2 ^ (k + 1)),
      ppFun (k + 1) Q x = polyFun (Ql n) x := fun n hn x hx => by
    have hn' : n < 2 ^ (k + 1) := lt_of_lt_of_le hn (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
    rw [ppFun_eq_of_mem Q hn' (Ioo_subset_Ico_self hx)]
    simp [Q, hn]
  have hright : ∀ n : ℕ, n < 2 ^ k → ∀ x ∈ Ioo ((n : ℝ) / 2 ^ (k + 1)) ((n + 1) / 2 ^ (k + 1)),
      ppFun (k + 1) Q (1 - x) = polyFun (Qr n) x := fun n hn x hx => by
    have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hm : 2 ^ (k + 1) - 1 - n < 2 ^ (k + 1) := by omega
    have hm' : ¬ (2 ^ (k + 1) - 1 - n < 2 ^ k) := by omega
    have hmn : 2 ^ (k + 1) - 1 - (2 ^ (k + 1) - 1 - n) = n := by omega
    have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    have hmem : 1 - x ∈ dyadicIco (k + 1) (2 ^ (k + 1) - 1 - n) := by
      rw [mem_dyadicIco]
      have hcast : ((2 ^ (k + 1) - 1 - n : ℕ) : ℝ) = 2 ^ (k + 1) - 1 - n := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]
      have h1 := hx.1
      have h2' := hx.2
      rw [div_lt_iff₀ hpos] at h1
      rw [lt_div_iff₀ hpos] at h2'
      constructor <;> nlinarith
    rw [ppFun_eq_of_mem Q hm hmem]
    simp only [Q, hm', ↓reduceIte, hmn]
    rw [polyFun_comp_affine]
    congr 1
    ring
  have hL := hl _ hSm hleft
  have hR := hrt _ hSm hright
  calc eLpNorm (fun x => F x - ppFun (k + 1) Q x) p unitVol
      ≤ eLpNorm (fun x => F x - ppFun (k + 1) Q x) p (volume.restrict (Icc 0 (1 / 2))) +
          eLpNorm (fun x => F x - ppFun (k + 1) Q x) p (volume.restrict (Icc (1 / 2) 1)) :=
        eLpNorm_Icc_split (hF.measurable.sub hSm) hp hp' (by norm_num) (by norm_num)
    _ ≤ jacksonConst r * modulus r p 0 1 F (1 / 2 ^ (k + 1)) +
          jacksonConst r * modulus r p 0 1 F (1 / 2 ^ (k + 1)) := add_le_add hL hR
    _ = 2 * jacksonConst r * modulus r p 0 1 F (1 / 2 ^ (k + 1)) := by ring

variable (p) in
/-- The modulus of an element of `L_p[0, 1]` at the dyadic scale `2^(-k)`,
`ω_r(f, 2^(-k), [0, 1])_p`. -/
noncomputable def lpModulus (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) : ℝ≥0∞ :=
  modulus r p 0 1 (f : ℝ → ℂ) (1 / 2 ^ k)

/-- The modulus of elements of `L_p[0, 1]` is subadditive. -/
theorem lpModulus_add_le (r : ℕ) (f g : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r (f + g) k ≤ lpModulus p r f k + lpModulus p r g k := by
  rw [lpModulus, modulus_congr_ae (Lp.coeFn_add f g)]
  exact modulus_add_le Fact.out r 0 1 _ _ _

/-- `ω_r(f, t) ≤ 2^r ‖f‖_p` in `L_p[0, 1]`. -/
theorem lpModulus_le (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.enorm_def]
  exact modulus_le (Lp.stronglyMeasurable f).measurable Fact.out r 0 1 _

/-- **Jackson's inequality for dyadic piecewise polynomials**: for `1 ≤ p < ∞`, `r ≥ 1` and
`k ≥ 1`, `E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p`; first for continuous
functions, then by density. -/
theorem approxSeq_ppScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) (f : Lp ℂ p unitVol) {k : ℕ}
    (hk : 1 ≤ k) :
    (ppScheme p r).approxSeq f (2 ^ k) ≤ 2 * jacksonConst r * lpModulus p r f k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hp1 : 1 ≤ p := Fact.out
  set C := 2 * jacksonConst r
  have hC : C ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (jacksonConst_ne_top r)
  -- continuous functions
  have hcont : ∀ g : ℝ →ᵇ ℂ, (ppScheme p r).approxSeq
      (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g) (2 ^ (k + 1)) ≤
        C * lpModulus p r (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g) (k + 1) := by
    intro g
    obtain ⟨Q, hQ, hbound⟩ := exists_ppFun_approx g.continuous hr hp1 hp k
    set a := (memLp_ppFun (k + 1) Q p).toLp (ppFun (k + 1) Q)
    have ha : a ∈ ppScheme p r (2 ^ (k + 1)) :=
      mem_ppScheme_two_pow.2 ⟨Q, hQ, MemLp.coeFn_toLp _⟩
    have hg := BoundedContinuousFunction.coeFn_toLp (E := ℂ) p unitVol ℝ g
    refine ((ppScheme p r).approxSeq_le_of_mem ha _).trans ?_
    rw [Lp.enorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hg.sub (MemLp.coeFn_toLp _))),
      lpModulus, modulus_congr_ae hg]
    exact hbound
  set b := C * lpModulus p r f (k + 1)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set K : ℝ≥0∞ := C * 2 ^ r + 1
  have hK : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC (by simp), ENNReal.one_ne_top⟩
  have hK0 : K ≠ 0 := by simp [K]
  have hη : 0 < (ε / K).toReal := ENNReal.toReal_pos (by
    simpa using ⟨ne_of_gt (by exact_mod_cast hε), hK⟩) (ENNReal.div_ne_top ENNReal.coe_ne_top hK0)
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.1
    (BoundedContinuousFunction.toLp_denseRange ℂ unitVol ℝ hp) f _ hη
  set fg := BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g
  have hdist : ‖f - fg‖ₑ ≤ ε / K := by
    rw [← edist_eq_enorm_sub, edist_dist, ← ENNReal.ofReal_toReal
      (ENNReal.div_ne_top ENNReal.coe_ne_top hK0)]
    exact ENNReal.ofReal_le_ofReal hg.le
  have hmod : lpModulus p r fg (k + 1) ≤ lpModulus p r f (k + 1) + 2 ^ r * ‖f - fg‖ₑ := by
    have h := lpModulus_add_le r f (fg - f) (k + 1)
    rw [add_sub_cancel] at h
    refine h.trans (add_le_add le_rfl ((lpModulus_le r _ _).trans ?_))
    rw [← enorm_neg, neg_sub]
  calc (ppScheme p r).approxSeq f (2 ^ (k + 1))
      ≤ (ppScheme p r).approxSeq fg (2 ^ (k + 1)) + ‖f - fg‖ₑ :=
        ApproximationScheme.approxSeq_le_approxSeq_add_enorm _ f fg
    _ ≤ C * (lpModulus p r f (k + 1) + 2 ^ r * ‖f - fg‖ₑ) + ‖f - fg‖ₑ :=
        add_le_add ((hcont g).trans (by gcongr)) le_rfl
    _ = b + K * ‖f - fg‖ₑ := by simp only [b, K]; ring
    _ ≤ b + K * (ε / K) := by gcongr
    _ = b + ε := by rw [ENNReal.mul_div_cancel hK0 hK]

end Interval
