/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Interpolation.EFunctionalModuli
public import ApproximationSpaces.Dyadic

/-!
# The calculus of the E-functional: homogeneity, embeddings, maps, near-best sequences

For a couple `A = (N₀, N₁)` on an abelian group (`InterpCouple`) with the E-functional
`E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}` (`InterpCouple.eFunctional`) and the dyadic norm
`‖u‖^dy_{s,q} = N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}` (`InterpCouple.eNormDyadic`), this file
collects the facts that the Besov spaces of a scheme of functions in `L_p`, `0 < p ≤ ∞`, need.
They hold for the quasi-norm `‖·‖_p` with `p < 1`: the hypotheses on `N₀` are homogeneity and,
for the blocks of near-best sequences, evenness and a `ρ`-triangle inequality.

* **Homogeneity**: `E(t, c u) ≤ |c| E(t, u)` and `‖c u‖^dy_{s,q} ≤ |c| ‖u‖^dy_{s,q}` if
  `N₀(c a) ≤ |c| N₀(a)`, multiplication by `c ≠ 0` does not increase the complexity and
  `N₁(0) = 0` (`InterpCouple.eFunctional_smul_le`, `InterpCouple.eNormDyadic_smul_le`).
* **Embeddings**: the dyadic norm decreases in the fine index, `‖u‖^dy_{s,r} ≤ ‖u‖^dy_{s,q}` for
  `0 < q ≤ r`, and in the smoothness, `‖u‖^dy_{t,r} ≤ γ_{s-t,r} ‖u‖^dy_{s,q}` for `t < s`,
  `q ≠ 0` and every `r` (`InterpCouple.eNormDyadic_mono_exponent`,
  `InterpCouple.eNormDyadic_le_of_lt`).
* **Maps**: if `N₁(0) = 0`, an additive map `T` with `N₀'(T a) ≤ M N₀(a)`, `M < ∞`, and
  `N₁'(T a) ≤ N₁(a)` gives `E'(t, T u) ≤ M E(t, u)` (`InterpCouple.eFunctional_map_le`); a map
  that sends every set `S_n` of a complexity couple into the set `S'_n` of another does not
  increase the complexity (`InterpCouple.complexity_norm1_map_le`).
* **Near-best sequences**: if `N₁(0) = 0`, there are `b_k` with `N₁(b_k) ≤ 2^k` and
  `N₀(u - b_k) ≤ E(2^k, u) + N₀(u) 2^(-k(s+1))` (`InterpCouple.exists_nearBest_eFunctional`);
  for `s ≥ -1` their tolerances decrease (`InterpCouple.antitone_eFunctional_add_dyadicWeight`),
  and if `N₀` is even and `N₀^ρ` subadditive, their blocks satisfy
  `N₀(b_{k+1} - b_k)^ρ ≤ 2 e_k^ρ` (`InterpCouple.norm0_sub_succ_rpow_le_of_nearBest`). Near-best
  sequences take the role of bounded linear projections onto the approximants: for a non-atomic
  measure and `0 < p < 1` the dual space of `L_p` is `{0}`, and every bounded linear projection
  of `L_p` with finite-dimensional range is `0`.
* **Pietsch's form** `‖((n + 1)^(s - 1/q) E(n, u))_n‖_{ℓ_q}` (`InterpCouple.eNormPietsch`): for
  `s ≥ 0` and `q ∈ (0, ∞]` it is at most `C_q 2^s` times the dyadic norm if `N₁(0) = 0`, and the
  dyadic norm is at most `4 C_q² 2^s` times it if only `0` has complexity below `1`, with the
  constants of the dyadic form of `A^s_q`, `C_q = LpAddConst q`
  (`InterpCouple.eNormPietsch_le_eNormDyadic`, `InterpCouple.eNormDyadic_le_eNormPietsch`); for
  the complexity couple of an approximation scheme it is Pietsch's quasi-norm `‖f‖_{A^s_q}`
  (`ApproximationScheme.eNormPietsch_complexityCouple`).

The comparison of the two forms is Cauchy condensation for a decreasing sequence `e` in `[0, ∞]`,
with `e_0` in the role of `‖f‖ = E_0(f)` (`ENNReal.lqNorm_pow_mul_le_dyadic`,
`ENNReal.dyadic_le_lqNorm_pow_mul`); the steps are those of
`ApproximationScheme.approxNorm_le_approxNormDyadic'` and
`ApproximationScheme.approxNormDyadic_le_approxNorm'`.
-/

@[expose] public section

open scoped ENNReal

/-! ### Pietsch's weights against the dyadic ones, for a decreasing sequence -/

namespace ENNReal

variable {q : ℝ≥0∞}

/-- **The `q`-th power of Pietsch's weighted `ℓ_q` norm**: for `0 < q < ∞`,
`‖((n + 1)^(s - 1/q) e_n)_n‖_{ℓ_q}^q = ∑_n (n + 1)^(sq - 1) e_n^q`. -/
theorem lqNorm_pow_mul_rpow (hq0 : q ≠ 0) (hq : q ≠ ∞) (s : ℝ) (e : ℕ → ℝ≥0∞) :
    lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * e n) ^ q.toReal =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * q.toReal - 1) * e n ^ q.toReal := by
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [ENNReal.lqNorm_rpow hq0 hq]
  congr 1
  funext n
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul]
  congr 2
  field_simp

variable {s : ℝ} {e : ℕ → ℝ≥0∞}

/-- **Pietsch's weighted `ℓ_q` norm by the dyadic one, for a decreasing sequence**: for
`e_0 ≥ e_1 ≥ ⋯` in `[0, ∞]`, `s ≥ 0` and `q ∈ (0, ∞]`,
`‖((n + 1)^(s - 1/q) e_n)_n‖_{ℓ_q} ≤ C_q 2^s (e_0 + ‖(2^(ks) e_{2^k})_k‖_{ℓ_q})` with Mathlib's
constant `C_q = LpAddConst q` (`1` for `q ≥ 1`); for `q = 0` the left side is `lqNorm 0 = 0`.
Cauchy condensation (`ENNReal.tsum_pow_mul_le_dyadic`, `ENNReal.iSup_pow_mul_le_dyadic`)
compares the `q`-th powers, and `(x^q + y^q)^(1/q) ≤ C_q (x + y)`. For `e_n = E_n(f)` this is
`ApproximationScheme.approxNorm_le_approxNormDyadic'`. -/
theorem lqNorm_pow_mul_le_dyadic (he : Antitone e) (hs : 0 ≤ s) :
    lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * e n) ≤
      LpAddConst q * 2 ^ s * (e 0 + lqNorm q fun k => dyadicWeight s k * e (2 ^ k)) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [lqNorm_zero_left]
    exact zero_le
  have h2s := ENNReal.one_le_two_rpow hs
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [LpAddConst_of_one_le le_top, one_mul, lqNorm_top, lqNorm_top, toReal_top,
      _root_.div_zero, sub_zero]
    calc ⨆ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * e n
        ≤ e 0 + 2 ^ s * ⨆ k, dyadicWeight s k * e (2 ^ k) := iSup_pow_mul_le_dyadic he hs
      _ ≤ 2 ^ s * e 0 + 2 ^ s * ⨆ k, dyadicWeight s k * e (2 ^ k) :=
          add_le_add (le_mul_of_one_le_left' h2s) le_rfl
      _ = 2 ^ s * (e 0 + ⨆ k, dyadicWeight s k * e (2 ^ k)) := by rw [mul_add]
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq'
  have hpow := lqNorm_pow_mul_rpow hq0 hq' s e
  set p := q.toReal
  set D := lqNorm q fun k => dyadicWeight s k * e (2 ^ k)
  set P := lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / p) * e n)
  have hD : D ^ p = ∑' k, dyadicWeight (s * p) k * e (2 ^ k) ^ p := by
    rw [ENNReal.lqNorm_rpow hq0 hq']
    congr 1
    funext k
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.dyadicWeight_rpow]
  have hb : Antitone fun n => e n ^ p := fun m n h => ENNReal.rpow_le_rpow (he h) hp.le
  have hPp : P ^ p ≤ (2 ^ s) ^ p * (e 0 ^ p + D ^ p) := by
    rw [hpow]
    calc ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * p - 1) * e n ^ p
        ≤ e 0 ^ p + 2 ^ max (s * p - 1) 0 *
            ∑' k, dyadicWeight (s * p - 1 + 1) k * e (2 ^ k) ^ p :=
          ENNReal.tsum_pow_mul_le_dyadic hb (s * p - 1)
      _ = e 0 ^ p + 2 ^ max (s * p - 1) 0 * D ^ p := by rw [sub_add_cancel, hD]
      _ ≤ (2 ^ s) ^ p * e 0 ^ p + (2 ^ s) ^ p * D ^ p := by
          gcongr
          · exact le_mul_of_one_le_left' (ENNReal.one_le_rpow h2s hp |>.trans_eq' rfl)
          · rw [← ENNReal.rpow_mul]
            exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two
              (max_le (by linarith) (by positivity))
      _ = (2 ^ s) ^ p * (e 0 ^ p + D ^ p) := by rw [mul_add]
  calc P = (P ^ p) ^ (1 / p) := by rw [one_div, ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ ((2 ^ s) ^ p * (e 0 ^ p + D ^ p)) ^ (1 / p) := by gcongr
    _ = 2 ^ s * (e 0 ^ p + D ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div, ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ 2 ^ s * (LpAddConst q * (e 0 + D)) := by
        gcongr
        exact ENNReal.rpow_add_rpow_le_LpAddConst_mul hq0 hq' _ _
    _ = LpAddConst q * 2 ^ s * (e 0 + D) := by ring

/-- **The shifted dyadic sequence by Pietsch's weighted norm, for a decreasing sequence**: for
`e_0 ≥ e_1 ≥ ⋯` in `[0, ∞]`, `s ≥ 0` and `q ∈ (0, ∞]`,
`‖(2^(ks) e_{2^(k+1)})_k‖_{ℓ_q} ≤ 2 C_q P` with `P = ‖((n + 1)^(s - 1/q) e_n)_n‖_{ℓ_q}` Pietsch's
weighted norm; for `q = 0` the left side is `lqNorm 0 = 0`. Cauchy condensation
(`ENNReal.dyadic_le_tsum_pow_mul`) bounds the `q`-th power of the left side by
`2^(max(1 - sq, 0)) P^q`, and `2^(max(1 - sq, 0)) ≤ 2 ≤ (2 C_q)^q`. For `e_n = E_n(f)` this is
`ApproximationScheme.lqNorm_dyadic_succ_le'`. -/
theorem lqNorm_dyadic_succ_le_lqNorm_pow_mul (he : Antitone e) (hs : 0 ≤ s) :
    lqNorm q (fun k => dyadicWeight s k * e (2 ^ (k + 1))) ≤
      2 * LpAddConst q *
        lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * e n) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [lqNorm_zero_left]
    exact zero_le
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [lqNorm_top, LpAddConst_of_one_le le_top, mul_one, lqNorm_top, toReal_top,
      _root_.div_zero, sub_zero]
    calc ⨆ k, dyadicWeight s k * e (2 ^ (k + 1))
        ≤ ⨆ k, dyadicWeight s k * e (2 ^ k) := iSup_mono fun k => by
          gcongr
          exact he (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
      _ ≤ ⨆ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * e n := dyadic_le_iSup_pow_mul hs
      _ ≤ 2 * ⨆ n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * e n := le_mul_of_one_le_left' one_le_two
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq'
  have hpow := lqNorm_pow_mul_rpow hq0 hq' s e
  set p := q.toReal
  set P := lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / p) * e n)
  have hb : Antitone fun n => e n ^ p := fun m n h => ENNReal.rpow_le_rpow (he h) hp.le
  have h2 : (2 : ℝ≥0∞) ≤ (2 * LpAddConst q) ^ p := by
    calc (2 : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
      _ ≤ (2 * LpAddConst q) ^ p :=
          ENNReal.rpow_le_rpow (ENNReal.two_rpow_one_div_le_two_mul_LpAddConst q) hp.le
  have hsp : 0 ≤ s * p := mul_nonneg hs hp.le
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.lqNorm_rpow hq0 hq']
  calc ∑' k, (dyadicWeight s k * e (2 ^ (k + 1))) ^ p
      = ∑' k, dyadicWeight (s * p - 1 + 1) k * e (2 ^ (k + 1)) ^ p := by
        congr 1
        funext k
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.dyadicWeight_rpow, sub_add_cancel]
    _ ≤ 2 ^ max (-(s * p - 1)) 0 * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * p - 1) * e n ^ p :=
        ENNReal.dyadic_le_tsum_pow_mul hb _
    _ = 2 ^ max (-(s * p - 1)) 0 * P ^ p := by rw [hpow]
    _ ≤ (2 * LpAddConst q) ^ p * P ^ p := by
        gcongr ?_ * _
        refine le_trans ?_ h2
        calc (2 : ℝ≥0∞) ^ max (-(s * p - 1)) 0 ≤ 2 ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le one_le_two (max_le (by linarith) zero_le_one)
          _ = 2 := ENNReal.rpow_one 2
    _ = (2 * LpAddConst q * P) ^ p := (ENNReal.mul_rpow_of_nonneg _ _ hp.le).symm

/-- **The dyadic norm by Pietsch's weighted norm, for a decreasing sequence**: for
`e_0 ≥ e_1 ≥ ⋯` in `[0, ∞]`, `s ≥ 0` and `q ∈ (0, ∞]`,
`e_0 + ‖(2^(ks) e_{2^k})_k‖_{ℓ_q} ≤ 4 C_q² 2^s ‖((n + 1)^(s - 1/q) e_n)_n‖_{ℓ_q}` with Mathlib's
constant `C_q = LpAddConst q`. The term `n = 0` gives `e_0`; the first dyadic term is `e_1 ≤ e_0`,
and splitting it off costs `C_q` (`ENNReal.lqNorm_le_head_add_shift'`); the others are bounded by
`ENNReal.lqNorm_dyadic_succ_le_lqNorm_pow_mul`. For `e_n = E_n(f)` this is
`ApproximationScheme.approxNormDyadic_le_approxNorm'`. -/
theorem dyadic_le_lqNorm_pow_mul (he : Antitone e) (hq0 : q ≠ 0) (hs : 0 ≤ s) :
    e 0 + lqNorm q (fun k => dyadicWeight s k * e (2 ^ k)) ≤
      LpAddConst q ^ 2 * 4 * 2 ^ s *
        lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * e n) := by
  have he0 : e 0 ≤ lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * e n) := by
    have h := ENNReal.le_lqNorm hq0
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * e n) 0
    simp only [zero_add, Nat.cast_one, ENNReal.one_rpow, one_mul] at h
    exact h
  set P := lqNorm q (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * e n)
  set C := LpAddConst q
  have h2s := ENNReal.one_le_two_rpow hs
  have hC : 1 ≤ C := ENNReal.one_le_LpAddConst q
  have h1 : 1 ≤ C ^ 2 * 2 ^ s :=
    (one_mul (1 : ℝ≥0∞)).symm.le.trans (mul_le_mul' (one_le_pow₀ hC) h2s)
  have hC2 : C ≤ C ^ 2 * 2 ^ s :=
    calc C = C * 1 * 1 := by ring
      _ ≤ C * C * 2 ^ s := by gcongr
      _ = C ^ 2 * 2 ^ s := by ring
  have hhead : dyadicWeight s 0 * e (2 ^ 0) ≤ P := by
    rw [ENNReal.dyadicWeight_zero_right, one_mul, pow_zero]
    exact (he zero_le_one).trans he0
  have hshift : lqNorm q (fun k => dyadicWeight s (k + 1) * e (2 ^ (k + 1))) ≤
      2 ^ s * (2 * C * P) := by
    have h : (fun k => dyadicWeight s (k + 1) * e (2 ^ (k + 1))) =
        fun k => 2 ^ s * (dyadicWeight s k * e (2 ^ (k + 1))) := by
      funext k
      rw [ENNReal.dyadicWeight_succ, mul_assoc]
    rw [h, ENNReal.lqNorm_const_mul]
    gcongr
    exact lqNorm_dyadic_succ_le_lqNorm_pow_mul he hs
  calc e 0 + lqNorm q (fun k => dyadicWeight s k * e (2 ^ k))
      ≤ P + C * (P + 2 ^ s * (2 * C * P)) := by
        gcongr
        exact (ENNReal.lqNorm_le_head_add_shift' q _).trans (by gcongr)
    _ = (1 + C + 2 * C ^ 2 * 2 ^ s) * P := by ring
    _ ≤ (C ^ 2 * 2 ^ s + C ^ 2 * 2 ^ s + 2 * C ^ 2 * 2 ^ s) * P := by gcongr
    _ = C ^ 2 * 4 * 2 ^ s * P := by ring

end ENNReal

open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst)

namespace InterpCouple

variable {U : Type*} [AddCommGroup U] {A : InterpCouple U}

/-! ### Homogeneity -/

section Smul

variable [Module ℝ U]

/-- **Homogeneity of the E-functional**: if `N₀(c a) ≤ |c| N₀(a)` for all real `c` and all `a`,
multiplication by a real `c ≠ 0` does not increase the complexity, and `N₁(0) = 0`, then
`E(t, c u) ≤ |c| E(t, u)`. For `c ≠ 0` the substitution `b ↦ c b` keeps admissible elements
admissible; for `c = 0` the element `b = 0` is admissible, and `N₀(0) = 0` by the first
hypothesis with `c = 0`. -/
theorem eFunctional_smul_le (h10 : A.norm1 0 = 0)
    (h0 : ∀ (c : ℝ) (a : U), A.norm0 (c • a) ≤ ‖c‖ₑ * A.norm0 a)
    (h1 : ∀ c : ℝ, c ≠ 0 → ∀ a : U, A.norm1 (c • a) ≤ A.norm1 a) (c : ℝ) (t : ℝ≥0∞) (u : U) :
    A.eFunctional t (c • u) ≤ ‖c‖ₑ * A.eFunctional t u := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h00 : A.norm0 0 = 0 := by simpa using h0 0 0
    rw [zero_smul, eFunctional_zero_right h00 h10]
    exact zero_le
  rw [show ‖c‖ₑ * A.eFunctional t u = ⨅ b : {b : U // A.norm1 b ≤ t}, ‖c‖ₑ * A.norm0 (u - b) from
    ENNReal.mul_iInf_of_ne (enorm_ne_zero.2 hc) enorm_ne_top]
  refine le_iInf fun b => (eFunctional_le ((h1 c hc b).trans b.2)).trans ?_
  rw [← smul_sub]
  exact h0 c (u - b)

/-- **Homogeneity of the dyadic norm**: under the hypotheses of
`InterpCouple.eFunctional_smul_le`, `‖c u‖^dy_{s,q} ≤ |c| ‖u‖^dy_{s,q}` for the dyadic norm
`N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}`, termwise and by the homogeneity of the `ℓ_q` norm. -/
theorem eNormDyadic_smul_le (h10 : A.norm1 0 = 0)
    (h0 : ∀ (c : ℝ) (a : U), A.norm0 (c • a) ≤ ‖c‖ₑ * A.norm0 a)
    (h1 : ∀ c : ℝ, c ≠ 0 → ∀ a : U, A.norm1 (c • a) ≤ A.norm1 a) (c s : ℝ) (q : ℝ≥0∞)
    (u : U) : A.eNormDyadic s q (c • u) ≤ ‖c‖ₑ * A.eNormDyadic s q u := by
  have hL : lqNorm q (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (c • u))
      ≤ ‖c‖ₑ * lqNorm q (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun k => ?_
    calc dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (c • u)
        ≤ dyadicWeight s k * (‖c‖ₑ * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := by
          gcongr
          exact eFunctional_smul_le h10 h0 h1 c _ u
      _ = ‖c‖ₑ * (dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := mul_left_comm _ _ _
  rw [eNormDyadic, eNormDyadic, mul_add]
  exact add_le_add (h0 c u) hL

end Smul

/-- **The dyadic norm of `0`** is `0` if both norms vanish at `0`, since then `E(t, 0) = 0`. -/
theorem eNormDyadic_zero (h00 : A.norm0 0 = 0) (h10 : A.norm1 0 = 0) (s : ℝ) (q : ℝ≥0∞) :
    A.eNormDyadic s q 0 = 0 := by
  simp [eNormDyadic, h00, eFunctional_zero_right h00 h10, ENNReal.lqNorm_zero_right]

/-! ### Embeddings of the dyadic norms -/

/-- **The dyadic norm decreases in the fine index**: `‖u‖^dy_{s,r} ≤ ‖u‖^dy_{s,q}` for
`0 < q ≤ r ≤ ∞`, also below `1`, by the monotonicity of the `ℓ_q` norms
(`ENNReal.lqNorm_le_lqNorm_of_le`). -/
theorem eNormDyadic_mono_exponent {q r : ℝ≥0∞} (hq0 : q ≠ 0) (hqr : q ≤ r) (s : ℝ) (u : U) :
    A.eNormDyadic s r u ≤ A.eNormDyadic s q u :=
  add_le_add le_rfl (ENNReal.lqNorm_le_lqNorm_of_le hq0 hqr _)

/-- **Lower smoothness with any fine index**: for `t < s`, `q ≠ 0` and every `r`,
`‖u‖^dy_{t,r} ≤ γ_{s-t,r} ‖u‖^dy_{s,q}` with `γ_{s-t,r} = dyadicGeomConst (s - t) r`, finite
since `s - t > 0`. Every term satisfies `2^(kt) E(2^k, u) ≤ 2^(-k(s-t)) L` with `L` the `ℓ_q`
part of `‖u‖^dy_{s,q}`, the geometric sequence has `ℓ_r` norm at most `γ_{s-t,r}`, and
`N₀(u) ≤ γ_{s-t,r} N₀(u)` since `γ_{s-t,r} ≥ 1` (`ENNReal.one_le_dyadicGeomConst`). -/
theorem eNormDyadic_le_of_lt {s t : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hts : t < s) (r : ℝ≥0∞)
    (u : U) :
    A.eNormDyadic t r u ≤ dyadicGeomConst (s - t) r * A.eNormDyadic s q u := by
  set L := lqNorm q fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u
  set γ := dyadicGeomConst (s - t) r
  have hterm : ∀ k : ℕ, dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u ≤
      L * dyadicWeight (-(s - t)) k := fun k => by
    calc dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u
        = dyadicWeight (-(s - t)) k *
            (dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := by
          rw [← mul_assoc, ← ENNReal.dyadicWeight_add, show -(s - t) + s = t by ring]
      _ ≤ dyadicWeight (-(s - t)) k * L := by
          gcongr
          exact ENNReal.le_lqNorm hq0
            (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) k
      _ = L * dyadicWeight (-(s - t)) k := mul_comm _ _
  have hL : lqNorm r (fun k : ℕ => dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) ≤
      γ * L := by
    calc lqNorm r (fun k : ℕ => dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u)
        ≤ lqNorm r (fun k : ℕ => L * dyadicWeight (-(s - t)) k) := ENNReal.lqNorm_mono hterm
      _ = L * lqNorm r (dyadicWeight (-(s - t))) := ENNReal.lqNorm_const_mul _ _
      _ ≤ L * γ := by
          gcongr
          exact ENNReal.lqNorm_dyadicWeight_neg_le_dyadicGeomConst (sub_nonneg.2 hts.le)
      _ = γ * L := mul_comm _ _
  calc A.eNormDyadic t r u
      = A.norm0 u + lqNorm r (fun k : ℕ => dyadicWeight t k *
          A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := rfl
    _ ≤ γ * A.norm0 u + γ * L :=
        add_le_add (le_mul_of_one_le_left' (ENNReal.one_le_dyadicGeomConst _ _)) hL
    _ = γ * A.eNormDyadic s q u := by rw [eNormDyadic, mul_add]

/-! ### Maps -/

/-- **The complexity of an image**: for any first norms `N` on `U` and `N'` on `V`, if a map
`T : U → V` sends every set `S n` into `S' n`, the complexity in the complexity couple of the
sets `S'` of `T b` is at most the complexity of `b` in that of the sets `S`. -/
theorem complexity_norm1_map_le {V : Type*} [AddCommGroup V] {N : U → ℝ≥0∞} {N' : V → ℝ≥0∞}
    {S : ℕ → Set U} {S' : ℕ → Set V} (T : U → V) (hT : ∀ n, ∀ b ∈ S n, T b ∈ S' n) (b : U) :
    (complexity N' S').norm1 (T b) ≤ (complexity N S).norm1 b :=
  le_iInf fun n => complexity_norm1_le_of_mem (hT n b n.2)

/-- **The E-functional under an additive map**: if `N₁(0) = 0`, `T : U → V` is additive,
`N₀'(T a) ≤ M N₀(a)` and `N₁'(T a) ≤ N₁(a)` for every `a`, and `M < ∞`, then
`E'(t, T u) ≤ M E(t, u)`: the image `T b` of an admissible `b` is admissible, and
`T u - T b = T (u - b)`. For `M = 0` the admissible element `b = 0` gives
`E'(t, T u) ≤ N₀'(T u) = 0`. The analogue for the K-functional is
`InterpCouple.kFunctional_map_le`. -/
theorem eFunctional_map_le {V : Type*} [AddCommGroup V] {B : InterpCouple V} (T : U →+ V)
    (h10 : A.norm1 0 = 0) {M : ℝ≥0∞} (hM : M ≠ ∞) (h0 : ∀ a, B.norm0 (T a) ≤ M * A.norm0 a)
    (h1 : ∀ a, B.norm1 (T a) ≤ A.norm1 a) (t : ℝ≥0∞) (u : U) :
    B.eFunctional t (T u) ≤ M * A.eFunctional t u := by
  rcases eq_or_ne M 0 with rfl | hM0
  · refine (eFunctional_le ((h1 0).trans (h10.trans_le zero_le))).trans ?_
    rw [map_zero, sub_zero, zero_mul]
    exact (h0 u).trans_eq (zero_mul _)
  rw [show M * A.eFunctional t u = ⨅ b : {b : U // A.norm1 b ≤ t}, M * A.norm0 (u - b) from
    ENNReal.mul_iInf_of_ne hM0 hM]
  refine le_iInf fun b => (eFunctional_le ((h1 b).trans b.2)).trans ?_
  rw [← map_sub]
  exact h0 _

/-! ### Near-best sequences -/

/-- **Near-best sequences**: if `N₁(0) = 0`, then for every `u` and `s` there are `b_k` with
`N₁(b_k) ≤ 2^k` and `N₀(u - b_k) ≤ E(2^k, u) + N₀(u) 2^(-k(s+1))`. For `N₀(u) ∈ (0, ∞)` the
tolerance is positive and `E(2^k, u) ≤ N₀(u)` is finite
(`InterpCouple.exists_norm0_sub_le_eFunctional_add`); for `N₀(u) = 0` and for `N₀(u) = ∞` the
element `b_k = 0` is admissible and near-best. Near-best sequences take the role of bounded
linear projections onto the approximants (for a non-atomic measure and `0 < p < 1`, the dual
space of `L_p` is `{0}`). -/
theorem exists_nearBest_eFunctional (h10 : A.norm1 0 = 0) (u : U) (s : ℝ) :
    ∃ b : ℕ → U, (∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞)) ∧ ∀ k,
      A.norm0 (u - b k) ≤
        A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u + A.norm0 u * dyadicWeight (-(s + 1)) k := by
  have hzero : ∀ k : ℕ, A.norm1 0 ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := fun k => h10.trans_le zero_le
  rcases eq_or_ne (A.norm0 u) 0 with hu0 | hu0
  · exact ⟨fun _ => 0, hzero, fun k => by rw [sub_zero, hu0]; exact zero_le⟩
  rcases eq_or_ne (A.norm0 u) ∞ with hut | hut
  · refine ⟨fun _ => 0, hzero, fun k => ?_⟩
    rw [hut, ENNReal.top_mul (ENNReal.dyadicWeight_ne_zero _ k), add_top]
    exact le_top
  have hE : ∀ k, A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u ≠ ∞ := fun k =>
    ne_top_of_le_ne_top hut (eFunctional_le_norm0 h10 u)
  choose b hb1 hb0 using fun k => exists_norm0_sub_le_eFunctional_add (hE k)
    (mul_ne_zero hu0 (ENNReal.dyadicWeight_ne_zero (-(s + 1)) k))
  exact ⟨b, hb1, hb0⟩

/-- **The tolerances decrease**: `e_k = E(2^k, u) + N₀(u) 2^(-k(s+1))` decreases in `k` for
`s ≥ -1`, since `E(t, u)` decreases in `t` and `2^(-k(s+1))` in `k`. -/
theorem antitone_eFunctional_add_dyadicWeight {s : ℝ} (hs : -1 ≤ s) (u : U) :
    Antitone fun k : ℕ =>
      A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u + A.norm0 u * dyadicWeight (-(s + 1)) k :=
  fun _ _ hij => add_le_add
    (eFunctional_anti u (Nat.cast_le.2 (Nat.pow_le_pow_right two_pos hij)))
    (mul_le_mul_right (ENNReal.dyadicWeight_anti (by linarith) hij) _)

/-- **Two near-best elements are close**: if `N₀` is even, `N₀^ρ` is subadditive for some
`ρ ≥ 0`, `N₀(u - b_k) ≤ e_k` for every `k` and `e` decreases, then
`N₀(b_{k+1} - b_k)^ρ ≤ 2 e_k^ρ`, from `b_{k+1} - b_k = (u - b_k) - (u - b_{k+1})` and
`e_{k+1} ≤ e_k`. -/
theorem norm0_sub_succ_rpow_le_of_nearBest {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hneg : ∀ a, A.norm0 (-a) = A.norm0 a)
    (hadd : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) {u : U} {b : ℕ → U}
    {e : ℕ → ℝ≥0∞} (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (he : Antitone e) (k : ℕ) :
    A.norm0 (b (k + 1) - b k) ^ ρ ≤ 2 * e k ^ ρ := by
  rw [show b (k + 1) - b k = (u - b k) - (u - b (k + 1)) by abel]
  calc A.norm0 ((u - b k) - (u - b (k + 1))) ^ ρ
      ≤ A.norm0 (u - b k) ^ ρ + A.norm0 (u - b (k + 1)) ^ ρ := norm0_sub_rpow_le hneg hadd _ _
    _ ≤ e k ^ ρ + e k ^ ρ := add_le_add (ENNReal.rpow_le_rpow (hbe k) hρ)
        (ENNReal.rpow_le_rpow ((hbe (k + 1)).trans (he k.le_succ)) hρ)
    _ = 2 * e k ^ ρ := (two_mul _).symm

/-! ### Pietsch's form -/

/-- **Pietsch's form** of the norm of the approximation space of a couple:
`‖((n + 1)^(s - 1/q) E(n, u))_{n ∈ ℕ}‖_{ℓ_q}`, the weights of Pietsch's quasi-norm of `A^s_q`
(`ApproximationScheme.approxNorm`) with the E-functional at the integers in place of the errors
`E_n(f)`. -/
noncomputable def eNormPietsch (A : InterpCouple U) (s : ℝ) (q : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  lqNorm q fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * A.eFunctional n u

/-- The E-functional at the integers decreases: `E(n, u) ≥ E(m, u)` for `n ≤ m`. -/
theorem antitone_eFunctional_natCast (u : U) : Antitone fun n : ℕ => A.eFunctional n u :=
  fun _ _ h => eFunctional_anti u (Nat.cast_le.2 h)

/-- **`E(0, u) = N₀(u)`** if `N₁(0) = 0` and every `b` with `N₁(b) < 1` is `0`: then `b = 0` is
the only admissible element at `t = 0`. -/
theorem eFunctional_zero_left (h10 : A.norm1 0 = 0) (hdisc : ∀ b, A.norm1 b < 1 → b = 0) (u : U) :
    A.eFunctional 0 u = A.norm0 u :=
  le_antisymm (eFunctional_le_norm0 h10 u) (norm0_le_eFunctional_of_lt_one hdisc zero_lt_one u)

/-- **Pietsch's form of `0`** is `0` if both norms vanish at `0`. -/
theorem eNormPietsch_zero (h00 : A.norm0 0 = 0) (h10 : A.norm1 0 = 0) (s : ℝ) (q : ℝ≥0∞) :
    A.eNormPietsch s q 0 = 0 := by
  simp [eNormPietsch, eFunctional_zero_right h00 h10, ENNReal.lqNorm_zero_right]

/-- **Pietsch's form under an additive map**: under the hypotheses of
`InterpCouple.eFunctional_map_le`, `‖T u‖^P_{s,q} ≤ M ‖u‖^P_{s,q}` for every `s` and `q`,
termwise. -/
theorem eNormPietsch_map_le {V : Type*} [AddCommGroup V] {B : InterpCouple V} (T : U →+ V)
    (h10 : A.norm1 0 = 0) {M : ℝ≥0∞} (hM : M ≠ ∞) (h0 : ∀ a, B.norm0 (T a) ≤ M * A.norm0 a)
    (h1 : ∀ a, B.norm1 (T a) ≤ A.norm1 a) (s : ℝ) (q : ℝ≥0∞) (u : U) :
    B.eNormPietsch s q (T u) ≤ M * A.eNormPietsch s q u := by
  rw [eNormPietsch, eNormPietsch, ← ENNReal.lqNorm_const_mul]
  refine ENNReal.lqNorm_mono fun n => ?_
  calc ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * B.eFunctional n (T u)
      ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * (M * A.eFunctional n u) := by
        gcongr
        exact eFunctional_map_le T h10 hM h0 h1 _ u
    _ = M * (((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * A.eFunctional n u) :=
        mul_left_comm _ _ _

variable {s : ℝ} {q : ℝ≥0∞}

/-- **Pietsch's form by the dyadic norm**: if `N₁(0) = 0`, then for `s ≥ 0` and every `q`,
`‖u‖^P_{s,q} ≤ C_q 2^s ‖u‖^dy_{s,q}` with `C_q = LpAddConst q`, by Cauchy condensation for the
decreasing sequence `E(n, u)` (`ENNReal.lqNorm_pow_mul_le_dyadic`), whose first term is
`E(0, u) ≤ N₀(u)`. -/
theorem eNormPietsch_le_eNormDyadic (h10 : A.norm1 0 = 0) (hs : 0 ≤ s) (u : U) :
    A.eNormPietsch s q u ≤ LpAddConst q * 2 ^ s * A.eNormDyadic s q u := by
  refine (ENNReal.lqNorm_pow_mul_le_dyadic (antitone_eFunctional_natCast (A := A) u) hs).trans ?_
  rw [Nat.cast_zero, eNormDyadic]
  gcongr
  exact eFunctional_le_norm0 h10 u

/-- **The dyadic norm by Pietsch's form**: if only `0` has complexity below `1`, then for `s ≥ 0`
and `q ∈ (0, ∞]`, `‖u‖^dy_{s,q} ≤ 4 C_q² 2^s ‖u‖^P_{s,q}` with `C_q = LpAddConst q`
(`ENNReal.dyadic_le_lqNorm_pow_mul`), since the first term of the decreasing sequence `E(n, u)`
is `E(0, u) ≥ N₀(u)`. -/
theorem eNormDyadic_le_eNormPietsch (hdisc : ∀ b, A.norm1 b < 1 → b = 0) (hq0 : q ≠ 0)
    (hs : 0 ≤ s) (u : U) :
    A.eNormDyadic s q u ≤ LpAddConst q ^ 2 * 4 * 2 ^ s * A.eNormPietsch s q u := by
  refine le_trans ?_
    (ENNReal.dyadic_le_lqNorm_pow_mul (antitone_eFunctional_natCast (A := A) u) hq0 hs)
  rw [Nat.cast_zero, eNormDyadic]
  gcongr
  exact norm0_le_eFunctional_of_lt_one hdisc zero_lt_one u

/-- **Pietsch's form and the dyadic norm are finite together**: if `N₁(0) = 0` and only `0` has
complexity below `1`, then for `s ≥ 0` and `q ∈ (0, ∞]`, `‖u‖^P_{s,q} < ∞` iff
`‖u‖^dy_{s,q} < ∞`. -/
theorem eNormPietsch_lt_top_iff (h10 : A.norm1 0 = 0) (hdisc : ∀ b, A.norm1 b < 1 → b = 0)
    (hq0 : q ≠ 0) (hs : 0 ≤ s) {u : U} :
    A.eNormPietsch s q u < ∞ ↔ A.eNormDyadic s q u < ∞ := by
  have hC := ENNReal.LpAddConst_lt_top q
  constructor
  · intro h
    refine (eNormDyadic_le_eNormPietsch hdisc hq0 hs u).trans_lt (ENNReal.mul_lt_top ?_ h)
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_ne_top hC.ne).lt_top (by norm_num))
      (ENNReal.two_rpow_ne_top s).lt_top
  · intro h
    exact (eNormPietsch_le_eNormDyadic h10 hs u).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC (ENNReal.two_rpow_ne_top s).lt_top) h)

end InterpCouple

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : ℝ} {q : ℝ≥0∞}

/-- **Pietsch's form of the complexity couple is Pietsch's quasi-norm**: for an approximation
scheme `A`, `‖f‖^P_{s,q}` of its complexity couple is `‖f‖_{A^s_q}`, termwise since
`E(n, f) = E_n(f)` (`ApproximationScheme.eFunctional_complexityCouple`). -/
theorem eNormPietsch_complexityCouple (A : ApproximationScheme X) (f : X) :
    A.complexityCouple.eNormPietsch s q f = A.approxNorm s q f := by
  simp only [InterpCouple.eNormPietsch, eFunctional_complexityCouple, approxNorm]

end ApproximationScheme
