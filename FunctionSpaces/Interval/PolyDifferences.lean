/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.Taylor
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differences of polynomials of every order

For a polynomial `P` of degree `< r` the difference of order `m ≥ r` vanishes
(`Interval.iterDiff_polynomial`); differences of lower order are small instead. If
`|P^(m)| ≤ M` on `[y, y + mσ]`, `σ ≥ 0`, then `|Δ_σ^m P(y)| ≤ σ^m M`
(`Interval.norm_iterDiff_polyFun_le`), by induction on `m` with the mean value theorem, since the
derivative of `Δ_σ^m P` is `Δ_σ^m P'` (`Interval.hasDerivAt_iterDiff_polyFun`).

On the finite-dimensional space of polynomials of degree `< r` every linear map is bounded by
the `L_p` norm on an interval (`Interval.exists_enorm_linearMap_le_eLpNorm`); for the `m`-th
derivative this is a form of Markov's inequality. After rescaling, the polynomials satisfy a
**difference bound** of order `m` (`Interval.DiffBound`, `Interval.exists_diffBound`):
`|Δ_t^m P(x)| ≤ K (t/L)^m L^(-1/p) ‖P‖_{L_p[u, u + L]}` for `x, x + mt ∈ [u, u + 2L]`. For `m = 0`
this is Nikolskii's bound (`Interval.NikolskiiBound`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

/-- The derivatives of polynomials of degree `< r` have degree `< r`. -/
theorem iterate_derivative_mem_degreeLT {r : ℕ} {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (m : ℕ) :
    derivative^[m] P ∈ degreeLT ℂ r := by
  induction m with
  | zero => exact hP
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [mem_degreeLT] at ih ⊢
    exact degree_derivative_le.trans_lt ih

/-- The value of a polynomial with coefficients `c` at `x ∈ [0, 1]` is at most `r ‖c‖`. -/
theorem norm_polyFun_degreeLTEquiv_symm_le (r : ℕ) (c : Fin r → ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) x‖ ≤ r * ‖c‖ := by
  have hx1 : ‖(x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
  rw [polyFun_degreeLTEquiv_symm]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin r, ‖c i * (x : ℂ) ^ (i : ℕ)‖ ≤ ∑ _i : Fin r, ‖c‖ :=
        Finset.sum_le_sum fun i _ => by
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx1)
            |>.trans (norm_le_pi_norm c i)
    _ = r * ‖c‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Linear maps of polynomials are bounded by the norm**: let `Φ` be a linear map of the
polynomials that preserves the degree bound `< r`, and `[α, β]` an interval of positive length.
There is `K` with `|Φ P(x)| ≤ K ‖P‖_{L_p[α, β]}` for all `x ∈ [0, 1]` and `P` of degree `< r`. In
coordinates `Φ` is a linear map of `ℂ^r`, hence bounded, and the coordinates are bounded by the
`L_p` norm, since `coeffToLp` is injective on a space of finite dimension. -/
theorem exists_enorm_linearMap_le_eLpNorm (r : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ[X])
    (hΦ : ∀ P ∈ degreeLT ℂ r, Φ P ∈ degreeLT ℂ r) {α β : ℝ} (hαβ : α < β) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ P ∈ degreeLT ℂ r, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖polyFun (Φ P) x‖ₑ ≤ K * eLpNorm (polyFun P) p (volume.restrict (Icc α β)) := by
  obtain ⟨K, -, hK⟩ := (coeffToLp p r α β).injective_iff_antilipschitz.1
    (coeffToLp_injective r hαβ)
  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) := (degreeLTEquiv ℂ r).toLinearMap ∘ₗ
    (Φ.restrict hΦ) ∘ₗ (degreeLTEquiv ℂ r).symm.toLinearMap
  let T' := LinearMap.toContinuousLinearMap T
  refine ⟨r * (‖T'‖ₑ * K), ENNReal.mul_ne_top (ENNReal.natCast_ne_top r)
    (ENNReal.mul_ne_top enorm_ne_top ENNReal.coe_ne_top), fun P hP x hx => ?_⟩
  set c := degreeLTEquiv ℂ r ⟨P, hP⟩
  have hPc : ((degreeLTEquiv ℂ r).symm c : ℂ[X]) = P := by simp [c]
  have hΦc : ((degreeLTEquiv ℂ r).symm (T c) : ℂ[X]) = Φ P := by
    simp [T, c, LinearMap.restrict_apply]
  have hbound : ‖c‖ ≤ K * ‖coeffToLp p r α β c‖ :=
    ZeroHomClass.bound_of_antilipschitz (coeffToLp p r α β) hK c
  have hT : ‖T c‖ ≤ ‖T'‖ * ‖c‖ := T'.le_opNorm c
  have hval : ‖polyFun (Φ P) x‖ ≤ r * (‖T'‖ * (K * ‖coeffToLp p r α β c‖)) := by
    rw [← hΦc]
    refine (norm_polyFun_degreeLTEquiv_symm_le r (T c) hx).trans ?_
    gcongr
    exact hT.trans (by gcongr)
  have hval' : ‖polyFun (Φ P) x‖ₑ ≤ r * (‖T'‖ₑ * (K * ‖coeffToLp p r α β c‖ₑ)) := by
    rw [← ofReal_norm, ← ofReal_norm]
    calc ENNReal.ofReal ‖polyFun (Φ P) x‖
        ≤ ENNReal.ofReal (r * (‖T'‖ * (K * ‖coeffToLp p r α β c‖))) := ENNReal.ofReal_le_ofReal hval
      _ = _ := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (norm_nonneg _),
          ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_coe_nnreal, ofReal_norm, ofReal_norm]
  rw [enorm_coeffToLp, hPc] at hval'
  calc ‖polyFun (Φ P) x‖ₑ ≤ r * (‖T'‖ₑ * (K * eLpNorm (polyFun P) p
        (volume.restrict (Icc α β)))) := hval'
    _ = _ := by ring

/-! ### Differences of polynomials and derivatives -/

/-- The derivative of a difference of a polynomial is the difference of its derivative:
`(Δ_σ^m P)' = Δ_σ^m P'`. -/
theorem hasDerivAt_iterDiff_polyFun (m : ℕ) (σ : ℝ) (P : ℂ[X]) (z : ℝ) :
    HasDerivAt (iterDiff m σ (polyFun P)) (iterDiff m σ (polyFun (derivative P)) z) z := by
  have h : iterDiff m σ (polyFun P) = fun z => ∑ k ∈ Finset.range (m + 1),
      ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * polyFun P (z + k * σ) :=
    funext fun z => iterDiff_apply m σ _ z
  rw [h, iterDiff_apply]
  exact HasDerivAt.fun_sum fun k _ =>
    ((hasDerivAt_polyFun P (z + k * σ)).comp_add_const z (k * σ)).const_mul _

/-- **Differences of polynomials by derivatives**: if `|P^(m)| ≤ M` on `[y, y + mσ]` with
`σ ≥ 0`, then `|Δ_σ^m P(y)| ≤ σ^m M`. Induction on `m`: `Δ_σ^(m+1) P(y) = Δ_σ^m P(y + σ) -
Δ_σ^m P(y)`, and the mean value theorem (Mathlib's
`norm_image_sub_le_of_norm_deriv_le_segment'`) applies to `Δ_σ^m P` with derivative
`Δ_σ^m P'`. -/
theorem norm_iterDiff_polyFun_le (m : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {M : ℝ} :
    ∀ (P : ℂ[X]) (y : ℝ), (∀ z ∈ Icc y (y + m * σ), ‖polyFun (derivative^[m] P) z‖ ≤ M) →
      ‖iterDiff m σ (polyFun P) y‖ ≤ σ ^ m * M := by
  induction m with
  | zero =>
    intro P y h
    simpa using h y ⟨le_rfl, by simp⟩
  | succ m ih =>
    intro P y h
    rw [iterDiff_succ]
    have hd : ∀ z ∈ Icc y (y + σ), HasDerivWithinAt (iterDiff m σ (polyFun P))
        (iterDiff m σ (polyFun (derivative P)) z) (Icc y (y + σ)) z :=
      fun z _ => (hasDerivAt_iterDiff_polyFun m σ P z).hasDerivWithinAt
    have hb : ∀ z ∈ Ico y (y + σ), ‖iterDiff m σ (polyFun (derivative P)) z‖ ≤ σ ^ m * M :=
      fun z hz => ih (derivative P) z fun w hw => by
        have hw' : w ∈ Icc y (y + ((m + 1 : ℕ) : ℝ) * σ) := by
          push_cast
          constructor <;> nlinarith [hz.1, hz.2, hw.1, hw.2]
        have := h w hw'
        rwa [Function.iterate_succ_apply] at this
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (y + σ)
      ⟨by linarith, le_rfl⟩
    calc ‖iterDiff m σ (polyFun P) (y + σ) - iterDiff m σ (polyFun P) y‖
        ≤ σ ^ m * M * (y + σ - y) := hmvt
      _ = σ ^ (m + 1) * M := by ring

/-! ### The difference bound -/

variable (p) in
/-- The **difference bound** of order `m` with constant `K` for the polynomials of degree `< r`:
`|Δ_t^m P(x)| ≤ K (t/L)^m L^(-1/p) ‖P‖_{L_p[u, u + L]}` for `t ≥ 0` and `u ≤ x`,
`x + mt ≤ u + 2L`. For `m = 0` this is Nikolskii's bound `Interval.NikolskiiBound`. -/
def DiffBound (r m : ℕ) (K : ℝ≥0∞) : Prop :=
  ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ {t : ℝ}, 0 ≤ t → ∀ x, u ≤ x →
    x + m * t ≤ u + 2 * L →
      ‖iterDiff m t (polyFun P) x‖ₑ ≤ K * ENNReal.ofReal (t / L) ^ m *
        ENNReal.ofReal L⁻¹ ^ (1 / p.toReal) * eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L)))

/-- The `m`-th derivative as a linear map preserves the degree bound `< r`. -/
theorem pow_derivative_mem_degreeLT {r : ℕ} (m : ℕ) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) :
    ((derivative : ℂ[X] →ₗ[ℂ] ℂ[X]) ^ m) P ∈ degreeLT ℂ r := by
  rw [Module.End.pow_apply]
  exact iterate_derivative_mem_degreeLT hP m

/-- **Differences of polynomials are small**: for `1 ≤ p < ∞` and every order `m` there is a
difference bound for the polynomials of degree `< r`. On `[0, 1]` the derivative `P^(m)` is
bounded by `K ‖P‖_{L_p[0, 1/2]}` (`Interval.exists_enorm_linearMap_le_eLpNorm`), so
`|Δ_σ^m P(y)| ≤ σ^m K ‖P‖_{L_p[0, 1/2]}` (`Interval.norm_iterDiff_polyFun_le`); the substitution
`x = u + 2L y` rescales. -/
theorem exists_diffBound (r m : ℕ) (hp : p ≠ ∞) : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ DiffBound p r m K := by
  obtain ⟨K, hK, hKb⟩ := exists_enorm_linearMap_le_eLpNorm (p := p) r
    ((derivative : ℂ[X] →ₗ[ℂ] ℂ[X]) ^ m) (fun P hP => pow_derivative_mem_degreeLT m hP)
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨K, hK, fun P hPr u L hL t ht x hux hxu => ?_⟩
  have h2L : 0 < 2 * L := by positivity
  set Q := P.comp (C (u : ℂ) + C ((2 * L : ℝ) : ℂ) * X)
  have hQ : Q ∈ degreeLT ℂ r := comp_affine_mem_degreeLT hPr _ _
  set σ := t / (2 * L)
  set y := (x - u) / (2 * L)
  have hσ : 0 ≤ σ := div_nonneg ht h2L.le
  -- the difference in the new variable
  have hdiff : iterDiff m t (polyFun P) x = iterDiff m σ (polyFun Q) y := by
    rw [iterDiff_apply, iterDiff_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [polyFun_comp_affine]
    congr 2
    simp only [σ, y]
    field_simp
    ring
  -- the bound of the derivative on `[0, 1]`
  have hfin : eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2))) ≠ ∞ :=
    (memLp_polyFun Q p 0 (1 / 2)).eLpNorm_ne_top
  have hKQ : K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2))) ≠ ∞ :=
    ENNReal.mul_ne_top hK hfin
  have hder : ∀ z ∈ Icc y (y + m * σ), ‖polyFun (derivative^[m] Q) z‖ ≤
      (K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2)))).toReal := fun z hz => by
    have hz01 : z ∈ Icc (0 : ℝ) 1 := by
      have hy0 : 0 ≤ y := div_nonneg (by linarith) h2L.le
      have hy1 : y + m * σ ≤ 1 := by
        rw [show y + m * σ = (x - u + m * t) / (2 * L) by simp only [y, σ]; ring,
          div_le_one h2L]
        linarith
      exact ⟨hy0.trans hz.1, hz.2.trans hy1⟩
    have h := hKb Q hQ z hz01
    rw [Module.End.pow_apply] at h
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hKQ).1 h
  have hval := norm_iterDiff_polyFun_le m hσ Q y hder
  -- the norm of `Q` on `[0, 1/2]`
  have hnorm := eLpNorm_comp_affine (measurable_polyFun P) hp u h2L 0 (1 / 2)
  rw [mul_zero, add_zero, show 2 * L * (1 / 2) = L by ring] at hnorm
  have hQfun : (fun y => polyFun P (u + 2 * L * y)) = polyFun Q :=
    funext fun y => (polyFun_comp_affine P u (2 * L) y).symm
  rw [hQfun] at hnorm
  have hσL : σ ≤ t / L := div_le_div_of_nonneg_left ht hL (by linarith)
  rw [hdiff, ← ofReal_norm]
  calc ENNReal.ofReal ‖iterDiff m σ (polyFun Q) y‖
      ≤ ENNReal.ofReal (σ ^ m * (K * eLpNorm (polyFun Q) p
          (volume.restrict (Icc 0 (1 / 2)))).toReal) := ENNReal.ofReal_le_ofReal hval
    _ = ENNReal.ofReal σ ^ m * (K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2)))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hσ, ENNReal.ofReal_toReal hKQ]
    _ = K * ENNReal.ofReal σ ^ m * ENNReal.ofReal (2 * L)⁻¹ ^ (1 / p.toReal) *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        rw [hnorm]; ring
    _ ≤ K * ENNReal.ofReal (t / L) ^ m * ENNReal.ofReal L⁻¹ ^ (1 / p.toReal) *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        gcongr
        linarith

end Interval
