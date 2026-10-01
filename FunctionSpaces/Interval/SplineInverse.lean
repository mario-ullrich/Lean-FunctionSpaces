/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.PiecewiseInverse
public import FunctionSpaces.Interval.Splines

/-!
# The inverse inequality for dyadic splines

For a spline `a` of order `r` and level `j` and every `k`,
`ω_r(a, 2^(-k), [0, 1])_p ≤ C_B 2^(-(k-j)(r-1+1/p)) ‖a‖_p` (`k - j` truncated at `0`). The
order `r - 1 + 1/p` comes from the jumps of the `(r-1)`-th derivative at the knots.

For `0 ≤ h ≤ 2^(-k)` the difference `Δ_h^r a(x)` vanishes when `x, …, x + rh` lie in one
interval. Otherwise, on `[x, x + rh]` the spline is `Q(y) + ∑_m c_m (y - ξ_m)_+^(r-1)`, with `Q` the
piece at `x` and `ξ_m` the knots in reach (`Interval.polyFun_eq_add_sum_jumps`). The polynomial
part has `Δ_h^r Q = 0`, and `|Δ_h^r (· - ξ)_+^(r-1)(x)| ≤ 2^r (rh)^(r-1)` for `x < ξ`
(`Interval.enorm_iterDiff_truncPow_le`). The jump `c_m L^(r-1) = Q_m(ξ_m + L) - Q_{m-1}(ξ_m + L)`,
`L = 2^(-j)`, is bounded by Nikolskii's inequality on the two neighbouring pieces
(`Interval.enorm_polyFun_le_two`). The rest is the strip integral of D1.7.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Nikolskii's inequality on the doubled interval**: there is `K` with
`|P(x)| ≤ K L^(-1/p) ‖P‖_{L_p[u, u + L]}` for `x ∈ [u, u + 2L]` and `P` of degree `< r`. -/
theorem enorm_polyFun_le_two (r : ℕ) (hp : p ≠ ∞) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L →
      ∀ x ∈ Icc u (u + 2 * L), ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
  obtain ⟨K, hK, hP⟩ := exists_enorm_le_eLpNorm (p := p) r (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨K, hK, fun P hPr u L hL x hx => ?_⟩
  have h2L : 0 < 2 * L := by positivity
  set Q := P.comp (C (u : ℂ) + C ((2 * L : ℝ) : ℂ) * X)
  have hQ : Q ∈ degreeLT ℂ r := comp_affine_mem_degreeLT hPr _ _
  have hy : (x - u) / (2 * L) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hx.1]) h2L.le
    · rw [div_le_one h2L]; linarith [hx.2]
  have hQx : polyFun Q ((x - u) / (2 * L)) = polyFun P x := by
    rw [polyFun_comp_affine]; congr 1; field_simp; ring
  have hnorm := eLpNorm_comp_affine (measurable_polyFun P) hp u h2L 0 (1 / 2)
  rw [mul_zero, add_zero, show 2 * L * (1 / 2) = L by ring] at hnorm
  have hQfun : (fun y => polyFun P (u + 2 * L * y)) = polyFun Q :=
    funext fun y => (polyFun_comp_affine P u (2 * L) y).symm
  rw [hQfun] at hnorm
  calc ‖polyFun P x‖ₑ = ‖polyFun Q ((x - u) / (2 * L))‖ₑ := by rw [hQx]
    _ ≤ K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2))) := hP Q hQ _ hy
    _ = K * ENNReal.ofReal (2 * L)⁻¹ ^ (1 / p).toReal *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        rw [hnorm, mul_assoc]
    _ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        gcongr
        linarith

/-- The **truncated power** `(y - ξ)_+^(r-1)`. -/
noncomputable def truncPow (r : ℕ) (ξ : ℝ) (y : ℝ) : ℂ :=
  if ξ ≤ y then (((y - ξ) ^ (r - 1) : ℝ) : ℂ) else 0

/-- **Differences of a truncated power left of its knot**: for `x < ξ` and `h ≥ 0`,
`|Δ_h^r (· - ξ)_+^(r-1)(x)| ≤ 2^r (rh)^(r-1)`, since `0 ≤ (x + ih - ξ)_+ ≤ rh`. -/
theorem enorm_iterDiff_truncPow_le (r : ℕ) {ξ h x : ℝ} (hh : 0 ≤ h) (hx : x < ξ) :
    ‖iterDiff r h (truncPow r ξ) x‖ₑ ≤ 2 ^ r * ENNReal.ofReal (r * h) ^ (r - 1) := by
  have hT : ∀ i ∈ Finset.range (r + 1),
      ‖truncPow r ξ (x + i * h)‖ₑ ≤ ENNReal.ofReal (r * h) ^ (r - 1) := fun i hi => by
    have hi' : (i : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    unfold truncPow
    split_ifs with hξ
    · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_pow,
        abs_of_nonneg (by linarith), ← ENNReal.ofReal_pow (by positivity)]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) ?_ _)
      nlinarith [mul_le_mul_of_nonneg_right hi' hh]
    · simp
  have hc : ∀ i : ℕ, ‖(-1 : ℂ) ^ (r - i) * (r.choose i : ℂ)‖ₑ = (r.choose i : ℝ≥0∞) := fun i => by
    rw [enorm_mul, enorm_pow, enorm_neg, enorm_one, one_pow, one_mul, ← ofReal_norm,
      Complex.norm_natCast, ENNReal.ofReal_natCast]
  rw [iterDiff_apply]
  refine (enorm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (r + 1),
        ‖(-1 : ℂ) ^ (r - i) * (r.choose i : ℂ) * truncPow r ξ (x + i * h)‖ₑ
      ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ≥0∞) * ENNReal.ofReal (r * h) ^ (r - 1) :=
        Finset.sum_le_sum fun i hi => by
          rw [enorm_mul, hc]
          exact mul_le_mul_right (hT i hi) _
    _ = _ := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        rfl

/-- **The strip integral**: if `|F|^p` is bounded by `G^p M_n` on the strip of width `rh` left of
the right end of every dyadic interval `I_{j,n}` and vanishes elsewhere on `S ⊆ [0, 1]`, and
`∑_{n < 2^j} M_n ≤ (r + 1) B^p`, then `‖F‖_{L_p(S)} ≤ G (rh (r + 1))^(1/p) B`. -/
theorem eLpNorm_le_of_strip (hp : p ≠ ∞) {F : ℝ → ℂ} {S : Set ℝ} (hS : S ⊆ Icc 0 1)
    (hF : AEStronglyMeasurable F (volume.restrict S)) {j r : ℕ} {h : ℝ} {G : ℝ≥0∞}
    {M : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hpt : ∀ᵐ x ∂volume.restrict S, ‖F x‖ₑ ^ p.toReal ≤ stripBound j r h (G ^ p.toReal) M x)
    (hB : ∑ n ∈ Finset.range (2 ^ j), M n ≤ (r + 1) * B ^ p.toReal) :
    eLpNorm F p (volume.restrict S) ≤
      G * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) * B := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine eLpNorm_le_of_lintegral_le hF hp0 hp ?_
  calc ∫⁻ x in S, ‖F x‖ₑ ^ p.toReal
      ≤ ∫⁻ x in S, stripBound j r h (G ^ p.toReal) M x := lintegral_mono_ae hpt
    _ ≤ ∫⁻ x in Icc (0 : ℝ) 1, stripBound j r h (G ^ p.toReal) M x := lintegral_mono_set hS
    _ ≤ G ^ p.toReal * ENNReal.ofReal (r * h) * ∑ n ∈ Finset.range (2 ^ j), M n :=
        lintegral_stripBound_le j r h _ _
    _ ≤ G ^ p.toReal * ENNReal.ofReal (r * h) * ((r + 1) * B ^ p.toReal) := by gcongr
    _ = (G * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) * B) ^ p.toReal := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
        ring

/-! ### Splines across the knots -/

/-- **Telescoping**: `f b = f a + ∑_{a < m ≤ b} (f m - f (m - 1))` for `a ≤ b`. -/
theorem eq_add_sum_Ioc_sub {G : Type*} [AddCommGroup G] (f : ℕ → G) {a b : ℕ} (hab : a ≤ b) :
    f b = f a + ∑ m ∈ Finset.Ioc a b, (f m - f (m - 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, Nat.add_sub_cancel, ← add_assoc, ← ih]
    abel

open Classical in
/-- The **jump coefficients** of spline pieces: `Q_m - Q_{m-1} = c_m (x - ξ_m)^(r-1)` at the
interior knots, and `0` elsewhere. -/
noncomputable def jumpCoeff {r j : ℕ} {Q : ℕ → ℂ[X]} (hJ : SplineJoins r j Q) (m : ℕ) : ℂ :=
  if h : 0 < m ∧ m < 2 ^ j then (hJ m h.1 h.2).choose else 0

/-- The jump at an interior knot. -/
theorem sub_eq_jumpCoeff {r j : ℕ} {Q : ℕ → ℂ[X]} (hJ : SplineJoins r j Q) {m : ℕ} (h0 : 0 < m)
    (hm : m < 2 ^ j) :
    Q m - Q (m - 1) = C (jumpCoeff hJ m) * (X - C ((((m : ℝ) / 2 ^ j : ℝ)) : ℂ)) ^ (r - 1) := by
  have h : 0 < m ∧ m < 2 ^ j := ⟨h0, hm⟩
  simp only [jumpCoeff, h, and_self, ↓reduceDIte]
  exact (hJ m h0 hm).choose_spec

/-- **A spline across the knots**: for `0 ≤ x ≤ y < 1` with `⌊2^j y⌋ ≤ ⌊2^j x⌋ + r`,
`u(y) = Q_{n₀}(y) + ∑_{n₀ < m ≤ n₀ + r} c_m (y - ξ_m)_+^(r-1)`, `n₀ = ⌊2^j x⌋`. -/
theorem polyFun_eq_add_sum_jumps {r j : ℕ} {Q : ℕ → ℂ[X]} (hJ : SplineJoins r j Q) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) (hyr : ⌊2 ^ j * y⌋₊ ≤ ⌊2 ^ j * x⌋₊ + r) :
    ppFun j Q y = polyFun (Q ⌊2 ^ j * x⌋₊) y + ∑ m ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r),
      jumpCoeff hJ m * truncPow r ((m : ℝ) / 2 ^ j) y := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hy0 : 0 ≤ y := hx.trans hxy
  obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := j) ⟨hy0, hy1⟩
  have hnn : ⌊2 ^ j * x⌋₊ ≤ ⌊2 ^ j * y⌋₊ := Nat.floor_mono (by nlinarith)
  rw [ppFun_eq_of_mem Q hlt hmem, eq_add_sum_Ioc_sub Q hnn, polyFun_add,
    ← Finset.sum_Ioc_consecutive _ hnn hyr]
  have hzero : ∑ m ∈ Finset.Ioc ⌊2 ^ j * y⌋₊ (⌊2 ^ j * x⌋₊ + r),
      jumpCoeff hJ m * truncPow r ((m : ℝ) / 2 ^ j) y = 0 :=
    Finset.sum_eq_zero fun m hm => by
      have hm' := (Finset.mem_Ioc.1 hm).1
      have : y < (m : ℝ) / 2 ^ j := by
        rw [lt_div_iff₀ hpos]
        have h1 : (⌊2 ^ j * y⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm'
        linarith [Nat.lt_floor_add_one (2 ^ j * y)]
      simp [truncPow, not_le.2 this]
  rw [hzero, add_zero]
  congr 1
  rw [polyFun, eval_finsetSum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.1 hm
  rw [sub_eq_jumpCoeff hJ (by omega) (by omega), eval_mul, eval_C, eval_pow, eval_sub, eval_X,
    eval_C]
  have hξ : (m : ℝ) / 2 ^ j ≤ y := by
    rw [div_le_iff₀ hpos]
    have : (m : ℝ) ≤ ⌊2 ^ j * y⌋₊ := by exact_mod_cast hm2
    nlinarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 ^ j * y)]
  simp only [truncPow, hξ, ↓reduceIte]
  push_cast
  ring

/-- **Differences of a spline are differences of its jumps**: on `[x, x + rh] ⊆ [0, 1)` with
`h ≤ 2^(-j)`, `Δ_h^r u(x) = ∑_{n₀ < m ≤ n₀ + r} c_m Δ_h^r (· - ξ_m)_+^(r-1)(x)`. -/
theorem iterDiff_ppFun_eq_sum_jumps {r j : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r)
    (hJ : SplineJoins r j Q) {h x : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) (hx : 0 ≤ x)
    (hxr : x + r * h < 1) :
    iterDiff r h (ppFun j Q) x = ∑ m ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r),
      jumpCoeff hJ m * iterDiff r h (truncPow r ((m : ℝ) / 2 ^ j)) x := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hkh : (2 : ℝ) ^ j * h ≤ 1 := by
    rw [le_div_iff₀ hpos] at hh
    linarith
  have hdec : ∀ i ∈ Finset.range (r + 1), ppFun j Q (x + i * h) =
      polyFun (Q ⌊2 ^ j * x⌋₊) (x + i * h) + ∑ m ∈ Finset.Ioc ⌊2 ^ j * x⌋₊ (⌊2 ^ j * x⌋₊ + r),
        jumpCoeff hJ m * truncPow r ((m : ℝ) / 2 ^ j) (x + i * h) := fun i hi => by
    have hi' : (i : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hih : (i : ℝ) * h ≤ r * h := mul_le_mul_of_nonneg_right hi' hh0
    refine polyFun_eq_add_sum_jumps hJ hx (by nlinarith [mul_nonneg (Nat.cast_nonneg i) hh0])
      (by linarith) ?_
    have : 2 ^ j * (x + i * h) ≤ 2 ^ j * x + r := by
      have : (2 : ℝ) ^ j * (i * h) ≤ r :=
        calc (2 : ℝ) ^ j * (i * h) = i * (2 ^ j * h) := by ring
          _ ≤ r * 1 := mul_le_mul hi' hkh (by positivity) (Nat.cast_nonneg r)
          _ = r := mul_one _
      linarith
    calc ⌊2 ^ j * (x + i * h)⌋₊ ≤ ⌊2 ^ j * x + (r : ℝ)⌋₊ := Nat.floor_mono this
      _ = ⌊2 ^ j * x⌋₊ + r := Nat.floor_add_natCast (by positivity) r
  rw [iterDiff_apply, Finset.sum_congr rfl fun i hi => by rw [hdec i hi] ]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hpoly : ∑ i ∈ Finset.range (r + 1), ((-1 : ℂ) ^ (r - i) * (r.choose i : ℂ)) *
      polyFun (Q ⌊2 ^ j * x⌋₊) (x + i * h) = 0 := by
    rw [← iterDiff_apply]
    exact congrFun (iterDiff_polynomial (hQ _) h) x
  rw [hpoly, zero_add, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iterDiff_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The local estimate -/

/-- The `L_p` norm of a piece on the closure of its interval is the local mass. -/
theorem eLpNorm_piece_eq_localMass (hp : p ≠ ∞) {j m : ℕ} (Q : ℕ → ℂ[X]) (hm : m < 2 ^ j) :
    eLpNorm (polyFun (Q m)) p (volume.restrict (Icc ((m : ℝ) / 2 ^ j) (m / 2 ^ j + 1 / 2 ^ j))) =
      localMass p j (ppFun j Q) m ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hIco : dyadicIco j m = Ico ((m : ℝ) / 2 ^ j) (m / 2 ^ j + 1 / 2 ^ j) := by
    rw [dyadicIco, add_div]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (measurable_polyFun _).aestronglyMeasurable,
    localMass, hIco, ← setLIntegral_congr Ico_ae_eq_Icc]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_Ico :
    MeasurableSet (Ico ((m : ℝ) / 2 ^ j) (m / 2 ^ j + 1 / 2 ^ j))) fun x hx => ?_
  have hx' : x ∈ dyadicIco j m := by rw [hIco]; exact hx
  rw [ppFun_eq_of_mem Q hm hx']

/-- **The jumps are bounded by the neighbouring pieces**: for `0 < m < 2^j` and `L = 2^(-j)`,
`|c_m| L^(r-1) ≤ K 2^(j/p) (m_m^(1/p) + m_{m-1}^(1/p))`, from
`c_m L^(r-1) = Q_m(ξ_m + L) - Q_{m-1}(ξ_m + L)` and Nikolskii's inequality. -/
theorem enorm_jumpCoeff_le {r j : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r)
    (hJ : SplineJoins r j Q) {K : ℝ≥0∞}
    (hK1 : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + L),
      ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))))
    (hK2 : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + 2 * L),
      ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))))
    (hp : p ≠ ∞) {m : ℕ} (h0 : 0 < m) (hm : m < 2 ^ j) :
    ‖jumpCoeff hJ m‖ₑ * ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1) ≤
      K * ENNReal.ofReal (2 ^ j) ^ (1 / p).toReal * (localMass p j (ppFun j Q) m ^ (1 / p.toReal) +
        localMass p j (ppFun j Q) (m - 1) ^ (1 / p.toReal)) := by
  have hL : (0 : ℝ) < 1 / 2 ^ j := by positivity
  have hinv : (1 / (2 : ℝ) ^ j)⁻¹ = 2 ^ j := by rw [one_div, inv_inv]
  have hval : polyFun (Q m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j) -
      polyFun (Q (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j) =
      jumpCoeff hJ m * (((1 / 2 ^ j : ℝ) ^ (r - 1) : ℝ) : ℂ) := by
    have h := congrArg (fun P => polyFun P ((m : ℝ) / 2 ^ j + 1 / 2 ^ j))
      (sub_eq_jumpCoeff hJ h0 hm)
    simp only [polyFun, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at h ⊢
    rw [h]
    congr 1
    push_cast
    ring
  have h1 : ‖polyFun (Q m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ ≤ K * ENNReal.ofReal (2 ^ j) ^ (1 / p).toReal *
      localMass p j (ppFun j Q) m ^ (1 / p.toReal) := by
    have := hK1 _ (hQ m) ((m : ℝ) / 2 ^ j) hL ((m : ℝ) / 2 ^ j + 1 / 2 ^ j) ⟨by linarith, le_rfl⟩
    rwa [hinv, eLpNorm_piece_eq_localMass hp Q hm] at this
  have h2 : ‖polyFun (Q (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ ≤ K * ENNReal.ofReal (2 ^ j) ^ (1 / p).toReal *
      localMass p j (ppFun j Q) (m - 1) ^ (1 / p.toReal) := by
    have hξ : (m : ℝ) / 2 ^ j - 1 / 2 ^ j = ((m - 1 : ℕ) : ℝ) / 2 ^ j := by
      rw [Nat.cast_sub h0, Nat.cast_one, sub_div]
    have := hK2 _ (hQ (m - 1)) ((m : ℝ) / 2 ^ j - 1 / 2 ^ j) hL ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)
      ⟨by linarith, by linarith⟩
    rwa [hinv, hξ, eLpNorm_piece_eq_localMass hp Q (by omega)] at this
  calc ‖jumpCoeff hJ m‖ₑ * ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1)
      = ‖polyFun (Q m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j) - polyFun (Q (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ := by
        rw [hval, enorm_mul, ← ofReal_norm (((1 / 2 ^ j : ℝ) ^ (r - 1) : ℝ) : ℂ),
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          ENNReal.ofReal_pow hL.le]
    _ ≤ ‖polyFun (Q m) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ + ‖polyFun (Q (m - 1)) ((m : ℝ) / 2 ^ j + 1 / 2 ^ j)‖ₑ :=
        enorm_sub_le
    _ ≤ _ := by rw [mul_add]; exact add_le_add h1 h2

/-- The constant of the pointwise bound,
`G = 2 r 2^r K (r 2^j h)^(r-1) 2^(j/p)`. -/
noncomputable def splineStripConst (r j : ℕ) (K : ℝ≥0∞) (h : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  2 * r * 2 ^ r * K * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) *
    ENNReal.ofReal (2 ^ j) ^ (1 / p).toReal

/-- **Pointwise bound for differences of splines**: on the strips left of the knots,
`|Δ_h^r u(x)| ≤ G (∑_{l ≤ r} m_{n₀+l})^(1/p)`. -/
theorem enorm_iterDiff_spline_le {r j : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r)
    (hJ : SplineJoins r j Q) {K : ℝ≥0∞}
    (hK1 : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + L),
      ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))))
    (hK2 : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + 2 * L),
      ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))))
    (hp : p ≠ ∞) {h x : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) (hx : 0 ≤ x)
    (hxr : x + r * h < 1) :
    ‖iterDiff r h (ppFun j Q) x‖ₑ ≤ splineStripConst r j K h p *
      (∑ l ∈ Finset.range (r + 1), localMass p j (ppFun j Q) (⌊2 ^ j * x⌋₊ + l)) ^
        (1 / p.toReal) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  set n₀ := ⌊2 ^ j * x⌋₊
  set S := ∑ l ∈ Finset.range (r + 1), localMass p j (ppFun j Q) (n₀ + l)
  have hmass : ∀ l ≤ r, localMass p j (ppFun j Q) (n₀ + l) ^ (1 / p.toReal) ≤
      S ^ (1 / p.toReal) := fun l hl => by
    gcongr
    exact Finset.single_le_sum (f := fun l => localMass p j (ppFun j Q) (n₀ + l))
      (fun _ _ => zero_le) (Finset.mem_range.2 (by omega))
  have hscale : ENNReal.ofReal (r * h) ^ (r - 1) =
      ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1) * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) := by
    rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  -- each jump contributes at most `2 · 2^r K (r 2^j h)^(r-1) 2^(j/p) S^(1/p)`
  have hterm : ∀ m ∈ Finset.Ioc n₀ (n₀ + r), ‖jumpCoeff hJ m *
      iterDiff r h (truncPow r ((m : ℝ) / 2 ^ j)) x‖ₑ ≤
        2 * 2 ^ r * K * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) *
          ENNReal.ofReal (2 ^ j) ^ (1 / p).toReal * S ^ (1 / p.toReal) := fun m hm => by
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.1 hm
    have hxm : x < (m : ℝ) / 2 ^ j := by
      rw [lt_div_iff₀ hpos]
      have : (n₀ : ℝ) + 1 ≤ m := by exact_mod_cast hm1
      linarith [Nat.lt_floor_add_one (2 ^ j * x)]
    rw [enorm_mul]
    refine (mul_le_mul_right (enorm_iterDiff_truncPow_le r hh0 hxm) _).trans ?_
    rcases lt_or_ge m (2 ^ j) with hmj | hmj
    · have hc := enorm_jumpCoeff_le hQ hJ hK1 hK2 hp (by omega) hmj
      have hS : localMass p j (ppFun j Q) m ^ (1 / p.toReal) +
          localMass p j (ppFun j Q) (m - 1) ^ (1 / p.toReal) ≤ 2 * S ^ (1 / p.toReal) := by
        rw [two_mul]
        refine add_le_add ?_ ?_
        · rw [show m = n₀ + (m - n₀) by omega]; exact hmass _ (by omega)
        · rw [show m - 1 = n₀ + (m - 1 - n₀) by omega]; exact hmass _ (by omega)
      calc ‖jumpCoeff hJ m‖ₑ * (2 ^ r * ENNReal.ofReal (r * h) ^ (r - 1))
          = 2 ^ r * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) *
              (‖jumpCoeff hJ m‖ₑ * ENNReal.ofReal (1 / 2 ^ j) ^ (r - 1)) := by
            rw [hscale]; ring
        _ ≤ 2 ^ r * ENNReal.ofReal (r * (2 ^ j * h)) ^ (r - 1) *
              (K * ENNReal.ofReal (2 ^ j) ^ (1 / p).toReal * (2 * S ^ (1 / p.toReal))) := by
            exact mul_le_mul' le_rfl (hc.trans (mul_le_mul' le_rfl hS))
        _ = _ := by ring
    · have h0 : jumpCoeff hJ m = 0 := by
        simp only [jumpCoeff, show ¬ (0 < m ∧ m < 2 ^ j) by omega, ↓reduceDIte]
      rw [h0, enorm_zero, zero_mul]
      exact zero_le
  rw [iterDiff_ppFun_eq_sum_jumps hQ hJ hh0 hh hx hxr]
  refine (enorm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Nat.card_Ioc, show n₀ + r - n₀ = r by omega, nsmul_eq_mul,
    splineStripConst]
  ring_nf
  exact le_rfl

/-! ### The inverse inequality -/

/-- **The local inverse estimate for splines**: for a spline `u` of level `j` and
`0 ≤ h ≤ 2^(-j)`, `‖Δ_h^r u‖_{L_p[0, 1 - rh]} ≤ G (rh (r + 1))^(1/p) ‖u‖_{L_p[0, 1]}`. -/
theorem eLpNorm_iterDiff_spline_le {r j : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r)
    (hJ : SplineJoins r j Q) {K : ℝ≥0∞}
    (hK1 : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + L),
      ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))))
    (hK2 : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + 2 * L),
      ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))))
    (hp : p ≠ ∞) {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) :
    eLpNorm (iterDiff r h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - r * h))) ≤
      splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) *
        eLpNorm (ppFun j Q) p unitVol := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hrh : (0 : ℝ) ≤ r * h := by positivity
  refine eLpNorm_le_of_strip hp (Icc_subset_Icc le_rfl (by linarith))
    (measurable_iterDiff (measurable_ppFun j Q) r h).aestronglyMeasurable ?_
    (sum_sum_localMass_le hp j r Q)
  rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  rw [stripBound]
  split_ifs with hbad
  · calc ‖iterDiff r h (ppFun j Q) x‖ₑ ^ p.toReal
        ≤ (splineStripConst r j K h p * (∑ l ∈ Finset.range (r + 1),
            localMass p j (ppFun j Q) (⌊2 ^ j * x⌋₊ + l)) ^ (1 / p.toReal)) ^ p.toReal :=
          ENNReal.rpow_le_rpow (enorm_iterDiff_spline_le hQ hJ hK1 hK2 hp hh0 hh hx.1
            (by linarith [hx.2])) hq.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
            ENNReal.rpow_one]
  · push Not at hbad
    rw [iterDiff_eq_zero_of_isPiecewisePoly (isPiecewisePoly_ppFun hQ j) hh0 hx.1 hbad, enorm_zero,
      ENNReal.zero_rpow_of_pos hq]

/-- The constant of the inverse inequality for splines,
`2 r 2^r K r^(r-1) (r (r + 1))^(1/p)`. -/
noncomputable def splineInverseConst (r : ℕ) (K p : ℝ≥0∞) : ℝ≥0∞ :=
  2 * r * 2 ^ r * K * (r : ℝ≥0∞) ^ (r - 1) * ((r * (r + 1) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal)

/-- The bound of the local estimate in terms of `2^j h`:
`G (rh (r + 1))^(1/p) = C (2^j h)^(r-1) (2^j h)^(1/p)`. -/
theorem splineStripConst_mul_eq (hp : p ≠ ∞) (r j : ℕ) (K : ℝ≥0∞) (h : ℝ) :
    splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) =
      splineInverseConst r K p * ENNReal.ofReal (2 ^ j * h) ^ (r - 1) *
        ENNReal.ofReal (2 ^ j * h) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hθ : (1 / p).toReal = 1 / p.toReal := by rw [ENNReal.toReal_div, ENNReal.toReal_one]
  have h1 : ENNReal.ofReal (r * (2 ^ j * h)) = (r : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
  have h2 : ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
      (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) =
      ((r * (r + 1) : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) *
        ENNReal.ofReal (2 ^ j * h) ^ (1 / p.toReal) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    congr 1
    have h3 : ENNReal.ofReal (2 ^ j) * ENNReal.ofReal (r * h) =
        (r : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h) := by
      rw [← ENNReal.ofReal_mul (by positivity), show (2 : ℝ) ^ j * (r * h) = r * (2 ^ j * h) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
    calc ENNReal.ofReal (2 ^ j) * (ENNReal.ofReal (r * h) * (r + 1))
        = (ENNReal.ofReal (2 ^ j) * ENNReal.ofReal (r * h)) * (r + 1) := by ring
      _ = ((r : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) * (r + 1) := by rw [h3]
      _ = _ := by push_cast; ring
  rw [splineStripConst, splineInverseConst, hθ, h1, mul_pow]
  calc 2 * r * 2 ^ r * K * ((r : ℝ≥0∞) ^ (r - 1) * ENNReal.ofReal (2 ^ j * h) ^ (r - 1)) *
        ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
        (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal)
      = 2 * r * 2 ^ r * K * (r : ℝ≥0∞) ^ (r - 1) * ENNReal.ofReal (2 ^ j * h) ^ (r - 1) *
          (ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
            (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal)) := by ring
    _ = _ := by rw [h2]; ring

/-- `(2^j h)^n ≤ 2^(-(k-j)n)` for `0 ≤ h ≤ 2^(-k)` and `j ≤ k`. -/
theorem ofReal_two_pow_mul_pow_le {j k : ℕ} (hjk : j ≤ k) {h : ℝ} (hh : h ≤ 1 / 2 ^ k) (n : ℕ) :
    ENNReal.ofReal (2 ^ j * h) ^ n ≤ dyadicWeight (-(n : ℝ)) (k - j) := by
  rw [← ENNReal.rpow_natCast]
  exact ofReal_two_pow_mul_rpow_le hjk hh (Nat.cast_nonneg n)

/-- **The inverse inequality for dyadic splines**, of order `θ = r - 1 + 1/p`: there is
`C_B < ∞` with `ω_r(a, 2^(-k), [0, 1])_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for every spline `a` of order `r`
and level `j` (and `k - j` truncated at `0`). -/
theorem exists_inverse_splineScheme {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ splineScheme p r (2 ^ j),
      lpModulus p r a k ≤
        CB * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K1, hK1, hb1⟩ := enorm_polyFun_le (p := p) r hp
  obtain ⟨K2, hK2, hb2⟩ := enorm_polyFun_le_two (p := p) r hp
  have hb1' : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + L),
      ‖polyFun P x‖ₑ ≤ (K1 + K2) * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) :=
    fun P hP u L hL x hx => (hb1 P hP u hL x hx).trans (by gcongr; exact le_self_add)
  have hb2' : ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + 2 * L),
      ‖polyFun P x‖ₑ ≤ (K1 + K2) * ENNReal.ofReal L⁻¹ ^ (1 / p).toReal *
        eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) :=
    fun P hP u L hL x hx => (hb2 P hP u hL x hx).trans (by gcongr; exact le_add_self)
  have hKt : K1 + K2 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hK1, hK2⟩
  have hCt : splineInverseConst r (K1 + K2) p ≠ ∞ := by
    unfold splineInverseConst
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top r)) (by simp)) hKt)
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))) ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _)
  refine ⟨2 ^ r * (1 + splineInverseConst r (K1 + K2) p),
    ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hCt⟩),
    fun j k a ha => ?_⟩
  obtain ⟨Q, hQ, hJ, hae⟩ := mem_splineScheme_two_pow.1 ha
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpModulus_le r a k).trans
      (by gcongr; exact le_mul_of_one_le_right zero_le le_self_add)
  · have hnorm : ‖a‖ₑ = eLpNorm (ppFun j Q) p unitVol := by
      rw [Lp.enorm_def]
      exact eLpNorm_congr_ae hae
    rw [lpModulus, modulus_congr_ae hae, hnorm]
    refine iSup₂_le fun h hh => ?_
    have hhj : h ≤ 1 / 2 ^ j := hh.2.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hjk))
    have hw : ENNReal.ofReal (2 ^ j * h) ^ (r - 1) * ENNReal.ofReal (2 ^ j * h) ^ (1 / p.toReal) ≤
        dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) := by
      rw [show -(((r - 1 : ℕ) : ℝ) + 1 / p.toReal) = -((r - 1 : ℕ) : ℝ) + -(1 / p.toReal) by ring,
        ENNReal.dyadicWeight_add]
      exact mul_le_mul' (ofReal_two_pow_mul_pow_le hjk hh.2 _)
        (ofReal_two_pow_mul_rpow_le hjk hh.2 (by positivity))
    calc eLpNorm (iterDiff r h (ppFun j Q)) p (volume.restrict (Icc 0 (1 - r * h)))
        ≤ splineStripConst r j (K1 + K2) h p * (ENNReal.ofReal (r * h) * (r + 1)) ^
            (1 / p.toReal) * eLpNorm (ppFun j Q) p unitVol :=
          eLpNorm_iterDiff_spline_le hQ hJ hb1' hb2' hp hh.1 hhj
      _ = splineInverseConst r (K1 + K2) p * (ENNReal.ofReal (2 ^ j * h) ^ (r - 1) *
            ENNReal.ofReal (2 ^ j * h) ^ (1 / p.toReal)) * eLpNorm (ppFun j Q) p unitVol := by
          rw [splineStripConst_mul_eq hp r j _ h, mul_assoc (splineInverseConst _ _ _)]
      _ ≤ splineInverseConst r (K1 + K2) p *
            dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) *
            eLpNorm (ppFun j Q) p unitVol := mul_le_mul' (mul_le_mul' le_rfl hw) le_rfl
      _ ≤ 2 ^ r * (1 + splineInverseConst r (K1 + K2) p) *
            dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) *
            eLpNorm (ppFun j Q) p unitVol := by
          gcongr
          calc splineInverseConst r (K1 + K2) p ≤ 1 + splineInverseConst r (K1 + K2) p :=
                le_add_self
            _ ≤ 2 ^ r * (1 + splineInverseConst r (K1 + K2) p) :=
                le_mul_of_one_le_left zero_le (one_le_pow₀ one_le_two)

end Interval
