/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.PiecewisePoly
public import FunctionSpaces.Interval.Whitney
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Jackson's inequality for dyadic piecewise polynomials

For `1 ≤ p < ∞`, `r ≥ 1` and `k ≥ 1`, the error of best approximation in `L_p[0, 1]` by
piecewise polynomials of level `k` and degree `< r` is bounded by the modulus of smoothness,
`E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p`
(`Interval.approxSeq_ppScheme_le`). At level `0` the approximants are the polynomials of degree
`< r`, and Whitney's inequality of `FunctionSpaces.Interval.Whitney` gives the bound there
(`Interval.exists_approxSeq_ppScheme_one_le`), so Jackson's inequality holds at every level
(`Interval.exists_approxSeq_ppScheme_le`).

For `k ≥ 1` the proof needs no Whitney theorem. For continuous `f`, the Steklov smoothing of
`Interval.exists_left_smoothing` is close to `f`, its `r`-th derivative is bounded by `2^(kr)`
times the modulus, and on each dyadic interval it is approximated by a Taylor polynomial. The
smoothing looks to the right of `x`, so this argument covers `[0, 1/2]`
(`Interval.exists_left_approx`); the reflection `x ↦ 1 - x` preserves the modulus and gives
`[1/2, 1]` (`Interval.exists_right_approx`). The point `1/2` is a knot of every level `k ≥ 1`,
which is why `k ≥ 1` in this part of the argument. General `f ∈ L_p` follow by density of
bounded continuous functions (`Interval.approxSeq_le_of_continuous`, which serves every scheme in
`L_p[0, 1]`).
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
The proof smooths `F` (`Interval.exists_left_smoothing` with `L = 2^(-(k+1))`) and approximates
the smoothing by Taylor polynomials on each dyadic interval. -/
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
  have hL2 : (2 ^ k : ℕ) * L = 1 / 2 := by
    rw [hLdef]; push_cast; field_simp; ring
  have hwL : (1 / 2 : ℝ) + L ≤ 1 := by
    have : L ≤ 1 / 2 := by
      rw [hLdef, div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨g, D, hgm, hDm, h1, h2, hT⟩ := exists_left_smoothing hF hr hp hp' hL hwL
  choose Q hQ hQb using fun n : ℕ => hT (n * L) ((n + 1) * L) (by nlinarith)
  refine ⟨Q, hQ, fun S hS hSQ => ?_⟩
  set ω := modulus r p 0 1 F L
  -- the Taylor error, summed over the dyadic intervals
  have h3 : eLpNorm (fun x => g x - S x) p (volume.restrict (Icc 0 (1 / 2))) ≤
      ENNReal.ofReal L ^ r * eLpNorm D p (volume.restrict (Icc 0 (1 / 2))) := by
    refine eLpNorm_le_of_lintegral_le (hgm.sub hS).aestronglyMeasurable hp0 hp' ?_
    have hsplit := lintegral_Icc_le_sum (fun x => ‖g x - S x‖ₑ ^ p.toReal) 0 hL.le (2 ^ k)
    rw [zero_add, hL2] at hsplit
    refine hsplit.trans ?_
    have hpiece : ∀ n ∈ Finset.range (2 ^ k),
        ∫⁻ x in Icc (0 + n * L) (0 + (n + 1) * L), ‖g x - S x‖ₑ ^ p.toReal ≤
          (ENNReal.ofReal L ^ r) ^ p.toReal *
            ∫⁻ x in Icc (0 + n * L) (0 + (n + 1) * L), ‖D x‖ₑ ^ p.toReal :=
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
          ← eLpNorm_rpow_eq hDm.aestronglyMeasurable hp0 hp',
          ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
        have hlen : ((n : ℝ) + 1) * L - n * L = L := by ring
        have hb := hQb n
        rw [hlen] at hb
        exact ENNReal.rpow_le_rpow hb hq.le
    refine (Finset.sum_le_sum hpiece).trans ?_
    rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      eLpNorm_rpow_eq hDm.aestronglyMeasurable hp0 hp']
    gcongr
    have := sum_le_lintegral_Icc (G := fun x => ‖D x‖ₑ ^ p.toReal) 0 hL.le (2 ^ k)
    rw [zero_add, hL2] at this
    exact this
  have hLL : ENNReal.ofReal L * ENNReal.ofReal L⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hL.le, mul_inv_cancel₀ hL.ne', ENNReal.ofReal_one]
  calc eLpNorm (fun x => F x - S x) p (volume.restrict (Icc 0 (1 / 2)))
      = eLpNorm ((fun x => F x - g x) + fun x => g x - S x) p
          (volume.restrict (Icc 0 (1 / 2))) := by congr 1; funext x; simp
    _ ≤ eLpNorm (fun x => F x - g x) p (volume.restrict (Icc 0 (1 / 2))) +
          eLpNorm (fun x => g x - S x) p (volume.restrict (Icc 0 (1 / 2))) :=
        eLpNorm_add_le hp
    _ ≤ ω + ENNReal.ofReal L ^ r * (ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω) :=
        add_le_add h1 (h3.trans (by gcongr))
    _ = ω + (ENNReal.ofReal L * ENNReal.ofReal L⁻¹) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω := by
        rw [mul_pow]; ring
    _ = jacksonConst r * ω := by rw [hLL, one_pow, one_mul, jacksonConst]; ring

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

omit [Fact (1 ≤ p)] in
/-- The modulus at the dyadic scales decreases with the level. -/
theorem lpModulus_anti (r : ℕ) (f : Lp ℂ p unitVol) : Antitone (lpModulus p r f) := fun _ _ hjk =>
  modulus_mono r p 0 1 _ (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hjk))

/-- **From continuous functions to `L_p` by density**: a bound `E_n(g) ≤ C ω_r(g, 2^(-k))_p`
for every bounded continuous `g`, given by an approximant `u ∈ A_n` of `g`, holds for every
`f ∈ L_p[0, 1]`, `p < ∞`. The bounded continuous functions are dense in `L_p` (Mathlib's
`BoundedContinuousFunction.toLp_denseRange`), and both sides move by at most a multiple of
`‖f - g‖_p`. -/
theorem approxSeq_le_of_continuous {A : ApproximationScheme (Lp ℂ p unitVol)} (hp : p ≠ ∞)
    {r n k : ℕ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ g : ℝ →ᵇ ℂ, ∃ u : ℝ → ℂ, (∃ a ∈ A n, (a : ℝ → ℂ) =ᵐ[unitVol] u) ∧
      eLpNorm (fun x => g x - u x) p unitVol ≤ C * modulus r p 0 1 g (1 / 2 ^ k))
    (f : Lp ℂ p unitVol) : A.approxSeq f n ≤ C * lpModulus p r f k := by
  -- continuous functions
  have hcont : ∀ g : ℝ →ᵇ ℂ, A.approxSeq
      (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g) n ≤
        C * lpModulus p r (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g) k := by
    intro g
    obtain ⟨u, ⟨a, ha, hau⟩, hbound⟩ := h g
    have hg := BoundedContinuousFunction.coeFn_toLp (E := ℂ) p unitVol ℝ g
    refine (A.approxSeq_le_of_mem ha _).trans ?_
    rw [Lp.enorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hg.sub hau)), lpModulus,
      modulus_congr_ae hg]
    exact hbound
  -- density
  set b := C * lpModulus p r f k
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
  have hmod : lpModulus p r fg k ≤ lpModulus p r f k + 2 ^ r * ‖f - fg‖ₑ := by
    have h := lpModulus_add_le r f (fg - f) k
    rw [add_sub_cancel] at h
    refine h.trans (add_le_add le_rfl ((lpModulus_le r _ _).trans ?_))
    rw [← enorm_neg, neg_sub]
  calc A.approxSeq f n
      ≤ A.approxSeq fg n + ‖f - fg‖ₑ := ApproximationScheme.approxSeq_le_approxSeq_add_enorm _ f fg
    _ ≤ C * (lpModulus p r f k + 2 ^ r * ‖f - fg‖ₑ) + ‖f - fg‖ₑ :=
        add_le_add ((hcont g).trans (by gcongr)) le_rfl
    _ = b + K * ‖f - fg‖ₑ := by simp only [b, K]; ring
    _ ≤ b + K * (ε / K) := by gcongr
    _ = b + ε := by rw [ENNReal.mul_div_cancel hK0 hK]

/-- **Jackson's inequality for dyadic piecewise polynomials**: for `1 ≤ p < ∞`, `r ≥ 1` and
`k ≥ 1`, `E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p`; first for continuous
functions (`Interval.exists_ppFun_approx`), then by density
(`Interval.approxSeq_le_of_continuous`). -/
theorem approxSeq_ppScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) (f : Lp ℂ p unitVol) {k : ℕ}
    (hk : 1 ≤ k) :
    (ppScheme p r).approxSeq f (2 ^ k) ≤ 2 * jacksonConst r * lpModulus p r f k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  refine approxSeq_le_of_continuous hp (ENNReal.mul_ne_top (by norm_num) (jacksonConst_ne_top r))
    (fun g => ?_) f
  obtain ⟨Q, hQ, hbound⟩ := exists_ppFun_approx g.continuous hr Fact.out hp k
  exact ⟨ppFun (k + 1) Q, ⟨(memLp_ppFun (k + 1) Q p).toLp _,
    mem_ppScheme_two_pow.2 ⟨Q, hQ, MemLp.coeFn_toLp _⟩, MemLp.coeFn_toLp _⟩, hbound⟩

/-- **Whitney's inequality in `L_p[0, 1]`**: for `1 ≤ p < ∞`, `r ≥ 1` and `m ≥ 2` there is
`W < ∞` with `E_1(f)_p ≤ W ω_r(f, 2^(-m), [0, 1])_p` for every `f ∈ L_p[0, 1]`, where `E_1` is the
error of best approximation by the polynomials of degree `< r` (the approximants of
complexity `1`). -/
theorem exists_approxSeq_ppScheme_one_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {m : ℕ} (hm : 2 ≤ m) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ f : Lp ℂ p unitVol,
      (ppScheme p r).approxSeq f 1 ≤ W * lpModulus p r f m := by
  have ht : (0 : ℝ) < 1 / 2 ^ m := by positivity
  have ht3 : (1 : ℝ) / 2 ^ m ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  obtain ⟨W, hW, hWb⟩ := exists_eLpNorm_sub_polyFun_le_modulus hr hp ht ht3
  refine ⟨W, hW, fun f => approxSeq_le_of_continuous hp hW (fun g => ?_) f⟩
  obtain ⟨P, hP, hbound⟩ := hWb g g.continuous
  have hae : (fun x => g x - ppFun 0 (fun _ => P) x) =ᵐ[unitVol] fun x => g x - polyFun P x := by
    filter_upwards [ae_mem_Ico_unitVol] with x hx
    obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := 0) hx
    rw [ppFun_eq_of_mem _ hlt hmem]
  refine ⟨ppFun 0 (fun _ => P), ⟨(memLp_ppFun 0 (fun _ => P) p).toLp _, ?_, MemLp.coeFn_toLp _⟩,
    (eLpNorm_congr_ae hae).trans_le hbound⟩
  rw [mem_ppScheme one_ne_zero, Nat.log_one_right]
  exact ⟨fun _ => P, fun _ => hP, MemLp.coeFn_toLp _⟩

/-- **Jackson's inequality for dyadic piecewise polynomials at every level**: for `1 ≤ p < ∞` and
`r ≥ 1` there is `C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k), [0, 1])_p` for every
`f ∈ L_p[0, 1]` and every `k ≥ 0`; level `0` is Whitney's inequality. -/
theorem exists_approxSeq_ppScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p unitVol) (k : ℕ),
      (ppScheme p r).approxSeq f (2 ^ k) ≤ CJ * lpModulus p r f k := by
  obtain ⟨W, hW, hWb⟩ := exists_approxSeq_ppScheme_one_le (p := p) hr hp (le_refl 2)
  refine ⟨W + 2 * jacksonConst r, ENNReal.add_ne_top.2 ⟨hW, ENNReal.mul_ne_top (by norm_num)
    (jacksonConst_ne_top r)⟩, fun f k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    exact (hWb f).trans (mul_le_mul' le_self_add (lpModulus_anti r f (Nat.zero_le 2)))
  · exact (approxSeq_ppScheme_le hr hp f hk).trans (mul_le_mul' le_add_self le_rfl)

end Interval
