/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.Smoothing

/-!
# Whitney's inequality on `[0, 1]`

**Whitney's inequality**: for `1 ≤ p < ∞`, `r ≥ 1` and `0 < t ≤ 1/3` there is `W < ∞` such
that every continuous `F` has a polynomial `P` of degree `< r` with

`‖F - P‖_{L_p[0, 1]} ≤ W ω_r(F, t, [0, 1])_p`

(`Interval.exists_eLpNorm_sub_polyFun_le_modulus`). The best approximation by polynomials on
the whole interval is controlled by the modulus at a single scale `t`.

The proof uses two one-sided smoothings with `L = t` (`Interval.exists_left_smoothing`,
`Interval.exists_right_smoothing`). Together with Taylor's theorem they give polynomials `T₁`
and `T₂` with `‖F - T₁‖ ≤ A ω` on `[0, 1 - t]` and `‖F - T₂‖ ≤ A ω` on `[t, 1]`,
`A = 1 + t^(-r) 2^r r^(2r)` (`Interval.eLpNorm_sub_polyFun_le_of_smoothing`). Both parts contain
`[1/3, 2/3]`, where `T₁` and `T₂` differ by at most `2A ω`; since all norms on the polynomials of
degree `< r` are equivalent, they differ by at most `2K'A ω` on `[0, 1]`
(`Interval.exists_eLpNorm_le_middle`). Splitting `[0, 1]` at `1/2` gives `W = (2 + 2K') A`.

For the dyadic piecewise polynomials and splines of level `0`, the approximants are exactly the
polynomials of degree `< r`, so Whitney's inequality is their Jackson inequality at level `0`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Polynomials are controlled by their middle third**: there is `K'` with
`‖P‖_{L_p[0, 1]} ≤ K' ‖P‖_{L_p[1/3, 2/3]}` for every polynomial `P` of degree `< r`, by the
equivalence of norms on the polynomials of degree `< r`. -/
theorem exists_eLpNorm_le_middle (r : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ P ∈ degreeLT ℂ r,
      eLpNorm (polyFun P) p (volume.restrict (Icc 0 1)) ≤
        K * eLpNorm (polyFun P) p (volume.restrict (Icc (1 / 3) (2 / 3))) := by
  obtain ⟨K, hK, hKb⟩ := exists_enorm_le_eLpNorm (p := p) r (by norm_num : (1 / 3 : ℝ) < 2 / 3)
  refine ⟨K, hK, fun P hP => ?_⟩
  refine (eLpNorm_le_of_ae_enorm_bound (measurable_polyFun P).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun x hx => hKb P hP x hx))).trans_eq ?_
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.one_rpow,
    smul_eq_mul, mul_one]

/-- **Smoothing and Taylor on one part**: if `‖F - g‖_{L_p[a,b]} ≤ ω`, `‖D‖_{L_p[a,b]} ≤ c ω`,
`‖g - T‖_{L_p[a,b]} ≤ (b - a)^r ‖D‖_{L_p[a,b]}` and `b - a ≤ 1`, then
`‖F - T‖_{L_p[a,b]} ≤ (1 + c) ω`. -/
theorem eLpNorm_sub_polyFun_le_of_smoothing {F g D : ℝ → ℂ} {r : ℕ} {a b : ℝ} (hab : b - a ≤ 1)
    {T : ℂ[X]} {ω c : ℝ≥0∞}
    (h1 : eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) ≤ ω)
    (h2 : eLpNorm D p (volume.restrict (Icc a b)) ≤ c * ω)
    (h3 : eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      ENNReal.ofReal (b - a) ^ r * eLpNorm D p (volume.restrict (Icc a b))) :
    eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ≤ (1 + c) * ω := by
  have hp1 : 1 ≤ p := Fact.out
  have hle : ENNReal.ofReal (b - a) ^ r ≤ 1 := pow_le_one₀ zero_le (ENNReal.ofReal_le_one.2 hab)
  calc eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b))
      = eLpNorm ((fun x => F x - g x) + fun x => g x - polyFun T x) p
          (volume.restrict (Icc a b)) := by congr 1; funext x; simp
    _ ≤ eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
          eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) := eLpNorm_add_le hp1
    _ ≤ ω + 1 * (c * ω) := add_le_add h1 (h3.trans (mul_le_mul' hle h2))
    _ = (1 + c) * ω := by ring

/-- **Whitney's inequality for continuous functions**: for `1 ≤ p < ∞`, `r ≥ 1` and
`0 < t ≤ 1/3` there is `W < ∞` such that every continuous `F` has a polynomial `P` of degree
`< r` with `‖F - P‖_{L_p[0, 1]} ≤ W ω_r(F, t, [0, 1])_p`. -/
theorem exists_eLpNorm_sub_polyFun_le_modulus {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {t : ℝ}
    (ht : 0 < t) (ht3 : t ≤ 1 / 3) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ F : ℝ → ℂ, Continuous F → ∃ P ∈ degreeLT ℂ r,
      eLpNorm (fun x => F x - polyFun P x) p (volume.restrict (Icc 0 1)) ≤
        W * modulus r p 0 1 F t := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨K', hK', hK'b⟩ := exists_eLpNorm_le_middle (p := p) r
  set c : ℝ≥0∞ := ENNReal.ofReal t⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))
  have hc : c ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))
  refine ⟨(2 + 2 * K') * (1 + c), ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨by simp,
    ENNReal.mul_ne_top (by simp) hK'⟩) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hc⟩),
    fun F hF => ?_⟩
  set ω := modulus r p 0 1 F t
  have hwL : (1 - t) + t ≤ 1 := by linarith
  -- the left polynomial, on `[0, 1 - t]`
  obtain ⟨gl, Dl, -, -, hl1, hl2, hl3⟩ := exists_left_smoothing hF hr hp1 hp ht hwL
  obtain ⟨T₁, hT₁, hT₁b⟩ := hl3 0 (1 - t) (by linarith)
  have hE₁ : eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc 0 (1 - t))) ≤
      (1 + c) * ω := eLpNorm_sub_polyFun_le_of_smoothing (by linarith) hl1 hl2 hT₁b
  -- the right polynomial, on `[t, 1]`
  obtain ⟨gr, Dr, -, -, hr1, hr2, hr3⟩ := exists_right_smoothing hF hr hp1 hp ht hwL
  rw [sub_sub_cancel] at hr1 hr2
  obtain ⟨T₂, hT₂, hT₂b⟩ := hr3 t 1 (by linarith)
  have hE₂ : eLpNorm (fun x => F x - polyFun T₂ x) p (volume.restrict (Icc t 1)) ≤
      (1 + c) * ω := eLpNorm_sub_polyFun_le_of_smoothing (by linarith) hr1 hr2 hT₂b
  -- the two polynomials are close on `[1/3, 2/3]`, hence on `[0, 1]`
  have hmid : eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc (1 / 3) (2 / 3))) ≤
      2 * ((1 + c) * ω) := by
    calc eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc (1 / 3) (2 / 3)))
        = eLpNorm ((fun x => F x - polyFun T₂ x) - fun x => F x - polyFun T₁ x) p
            (volume.restrict (Icc (1 / 3) (2 / 3))) := by
          congr 1; funext x; simp only [Pi.sub_apply, polyFun, eval_sub]; ring
      _ ≤ eLpNorm (fun x => F x - polyFun T₂ x) p (volume.restrict (Icc (1 / 3) (2 / 3))) +
            eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc (1 / 3) (2 / 3))) :=
          eLpNorm_sub_le hp1
      _ ≤ (1 + c) * ω + (1 + c) * ω := add_le_add
          ((eLpNorm_Icc_mono _ p (by linarith) (by norm_num)).trans hE₂)
          ((eLpNorm_Icc_mono _ p (by norm_num) (by linarith)).trans hE₁)
      _ = 2 * ((1 + c) * ω) := by ring
  have hdiff : eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc 0 1)) ≤
      K' * (2 * ((1 + c) * ω)) :=
    (hK'b _ (Submodule.sub_mem _ hT₁ hT₂)).trans (mul_le_mul' le_rfl hmid)
  -- `T₁` on the two halves of `[0, 1]`
  have hL : eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc 0 (1 / 2))) ≤
      (1 + c) * ω := (eLpNorm_Icc_mono _ p le_rfl (by linarith)).trans hE₁
  have hR : eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc (1 / 2) 1)) ≤
      (1 + c) * ω + K' * (2 * ((1 + c) * ω)) := by
    calc eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc (1 / 2) 1))
        = eLpNorm ((fun x => F x - polyFun T₂ x) - polyFun (T₁ - T₂)) p
            (volume.restrict (Icc (1 / 2) 1)) := by
          congr 1; funext x; simp only [Pi.sub_apply, polyFun, eval_sub]; ring
      _ ≤ eLpNorm (fun x => F x - polyFun T₂ x) p (volume.restrict (Icc (1 / 2) 1)) +
            eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc (1 / 2) 1)) := eLpNorm_sub_le hp1
      _ ≤ (1 + c) * ω + K' * (2 * ((1 + c) * ω)) := add_le_add
          ((eLpNorm_Icc_mono _ p (by linarith) le_rfl).trans hE₂)
          ((eLpNorm_Icc_mono _ p (by norm_num) le_rfl).trans hdiff)
  refine ⟨T₁, hT₁, ?_⟩
  calc eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc 0 1))
      ≤ eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc 0 (1 / 2))) +
          eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc (1 / 2) 1)) :=
        eLpNorm_Icc_split (hF.measurable.sub (measurable_polyFun _)) hp1 hp (by norm_num)
          (by norm_num)
    _ ≤ (1 + c) * ω + ((1 + c) * ω + K' * (2 * ((1 + c) * ω))) := add_le_add hL hR
    _ = (2 + 2 * K') * (1 + c) * ω := by ring

end Interval
