/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Lipschitz.BoundaryLayers
public import FunctionSpaces.Rd.Atoms.SmoothAtoms
public import FunctionSpaces.Rd.Atoms.AtomAnalysis

/-!
# The indicator of a bounded Lipschitz domain as a pointwise multiplier

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`n = dim V`, `Ω ⊆ V` a bounded Lipschitz domain, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `0 < s < 1/p`.
Multiplication by `1_Ω` is bounded on `B^s_{p,q}(V)`, normed by first differences
(`Rd.BoundedLipschitzDomain.exists_modNorm_indicatorLp_le`):

`‖1_Ω F‖_p + ‖(2^(ks) ω_1(1_Ω F, 2^(-k))_p)_k‖_{ℓ_q}`
`≤ C (‖F‖_p + ‖(2^(ks) ω_1(F, 2^(-k))_p)_k‖_{ℓ_q})`,

with `C` independent of `q` and `F`. This is the case of `B`-spaces of Triebel's multiplier theorem
for characteristic functions (Triebel 2002, Proposition 5.3 and Remark 5.4), proved by the
mechanism of Schneider and Vybíral (Theorem 5.4(i), Remark 5.10): the products of smooth atoms
with a multiplier are non-smooth atoms.

* **Indicators of smooth atoms.** If `a` is a smooth atom of order `1` (`Rd.IsSmoothAtom`) with
  radius factor `d ≥ 1` and constant `A`, then `1_Ω a` is a regular atom (`Rd.IsRegularAtom`) of
  exponent `1/p` and order `1` with the constant `K A d^n`
  (`Rd.BoundedLipschitzDomain.exists_isRegularAtom_indicator`). Pointwise,
  `|Δ_h(1_U a)(x)| ≤ |Δ_h a(x)| + 1_{S_h(U)}(x) |a(x)|` (`Rd.enorm_indicator_add_sub_le`); the
  first term is at most `2A min(1, 2^j ‖h‖)` near the support of `a`
  (`Rd.IsSmoothAtom.enorm_sub_le_indicator`), the second at most `A` on the switch set inside the
  ball of `a` (`Rd.IsSmoothAtom.indicator_switchSet_le`), whose volume is at most
  `C d^n 2^(-jn) min(1, 2^j ‖h‖)`
  (`Rd.BoundedLipschitzDomain.exists_volume_switchSet_inter_closedBall_div_two_pow_le`).
  An `L_p` bound by two indicators (`Rd.eLpNorm_le_of_enorm_le_indicator_add`) gives the
  difference bound with the exponent `1/p` (`Rd.IsSmoothAtom.eLpNorm_fwdDiff_indicator_le`); the
  norm bound is `Rd.IsSmoothAtom.eLpNorm_indicator_le`.
* **The multiplier theorem.** The smooth atomic decomposition of `F`
  (`Rd.LocalMeansBump.atomic_decomposition_smooth`, with the standard bump) passes through
  `1_Ω`: `1_Ω F = ∑_j ∑_m λ_{j,m} 1_Ω a_{j,m}` with the same coefficients, the atomic synthesis
  (`Rd.modNorm_le_coeffNorm`, `0 < s < σ = 1/p`) bounds the left side by the coefficient norm,
  which is the local means norm of `F`, bounded by the right side
  (`Rd.LocalMeansBump.localMeansNorm_le`). Every step holds for `1 ≤ q ≤ ∞`.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

/-- **`x^z ≤ x` for `x ≥ 1` and `z ≤ 1`** in `[0, ∞]`, the companion of Mathlib's
`ENNReal.rpow_le_self_of_le_one` (`x ≤ 1`, `z ≥ 1`), from Mathlib's
`ENNReal.rpow_le_rpow_of_exponent_le` and `ENNReal.rpow_one`. -/
theorem ENNReal.rpow_le_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 1) :
    x ^ z ≤ x :=
  (ENNReal.rpow_le_rpow_of_exponent_le hx hz).trans_eq (ENNReal.rpow_one x)

namespace Rd

/-! ### Bounds by two indicators -/

/-- **An `L_p` bound by two indicators**: for `1 ≤ p` and `f` with values in a normed group, if
`|f| ≤ B₁ 1_{S₁} + B₂ 1_{S₂}` pointwise with measurable `S₁`, `S₂`, then
`‖f‖_p ≤ B₁ μ(S₁)^(1/p) + B₂ μ(S₂)^(1/p)` (Mathlib's `eLpNorm_add_le` and
`eLpNorm_indicator_const_le`). -/
theorem eLpNorm_le_of_enorm_le_indicator_add {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : α → E}
    (hf : AEStronglyMeasurable f μ) {S₁ S₂ : Set α}
    (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂) {B₁ B₂ : ℝ≥0∞}
    (hB : ∀ x, ‖f x‖ₑ ≤ S₁.indicator (fun _ => B₁) x + S₂.indicator (fun _ => B₂) x) :
    eLpNorm f p μ ≤ B₁ * μ S₁ ^ (1 / p.toReal) + B₂ * μ S₂ ^ (1 / p.toReal) := by
  calc eLpNorm f p μ ≤ eLpNorm (S₁.indicator (fun _ => B₁) + S₂.indicator (fun _ => B₂)) p μ :=
        eLpNorm_mono_enorm hf fun x => (hB x).trans_eq (enorm_eq_self _).symm
    _ ≤ eLpNorm (S₁.indicator fun _ => B₁) p μ + eLpNorm (S₂.indicator fun _ => B₂) p μ :=
        eLpNorm_add_le hp1
    _ ≤ _ := by
        refine add_le_add ((eLpNorm_indicator_const_le B₁ p h₁.nullMeasurableSet).trans_eq ?_)
          ((eLpNorm_indicator_const_le B₂ p h₂.nullMeasurableSet).trans_eq ?_) <;>
        rw [enorm_eq_self]

/-- **Differences of a cut-off function**: for a set `X` with an addition, `U ⊆ X` and
`a : X → E` with values in a normed group,
`|1_U a(x + h) - 1_U a(x)| ≤ |a(x + h) - a(x)| + 1_{S_h(U)}(x) |a(x)|`. Off the switch set both
points lie on the same side of `U`; on it the difference is `-a(x)` or
`a(x + h) = (a(x + h) - a(x)) + a(x)`. -/
theorem enorm_indicator_add_sub_le {X E : Type*} [Add X] [NormedAddCommGroup E] (U : Set X)
    (a : X → E) (h x : X) :
    ‖U.indicator a (x + h) - U.indicator a x‖ₑ ≤
      ‖a (x + h) - a x‖ₑ + (switchSet U h).indicator (fun y => ‖a y‖ₑ) x := by
  by_cases hx : x ∈ U <;> by_cases hxh : x + h ∈ U
  · rw [indicator_of_mem hx, indicator_of_mem hxh]
    exact le_self_add
  · have hs : x ∈ switchSet U h := fun hiff => hxh (hiff.1 hx)
    rw [indicator_of_mem hx, indicator_of_notMem hxh, indicator_of_mem hs, zero_sub, enorm_neg]
    exact le_add_self
  · have hs : x ∈ switchSet U h := fun hiff => hx (hiff.2 hxh)
    rw [indicator_of_notMem hx, indicator_of_mem hxh, indicator_of_mem hs, sub_zero]
    calc ‖a (x + h)‖ₑ = ‖(a (x + h) - a x) + a x‖ₑ := by rw [sub_add_cancel]
      _ ≤ _ := enorm_add_le _ _
  · rw [indicator_of_notMem hx, indicator_of_notMem hxh, sub_self, enorm_zero]
    exact zero_le

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Indicators of smooth atoms -/

/-- **Differences of smooth atoms of order one**: for a smooth atom `a` on `V` of order `1`, level
`j`, centre `c`, radius factor `d` and constant `A`,
`|a(x + h) - a(x)| ≤ 2A min(1, 2^j ‖h‖)` (`Rd.IsSmoothAtom.enorm_higherDiff_le`, with `A ≥ 0` from
`Rd.IsSmoothAtom.const_nonneg`), and the difference vanishes unless `x` lies in
`B̄(c, d 2^(-j)) ∪ B̄(c - h, d 2^(-j))`. -/
theorem IsSmoothAtom.enorm_sub_le_indicator {d A : ℝ} {j : ℕ} {c : V}
    {a : V → ℂ} (ha : IsSmoothAtom univ 1 d A j c a) (h x : V) :
    ‖a (x + h) - a x‖ₑ ≤ (closedBall c (d / 2 ^ j) ∪ closedBall (c - h) (d / 2 ^ j)).indicator
      (fun _ => ENNReal.ofReal (2 * A) * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖))) x := by
  by_cases hx : x ∈ closedBall c (d / 2 ^ j) ∪ closedBall (c - h) (d / 2 ^ j)
  · rw [indicator_of_mem hx]
    have h1 := ha.enorm_higherDiff_le convex_univ (by simp) ha.const_nonneg le_rfl le_rfl
      (show x ∈ stepSet univ 1 h by rw [stepSet_univ]; trivial)
    refine h1.trans_eq ?_
    rw [Nat.cast_one, ENNReal.rpow_one]
    norm_num
  · rw [indicator_of_notMem hx]
    simp only [mem_union, mem_closedBall, dist_eq_norm, not_or, not_le] at hx
    rw [show x - (c - h) = x + h - c by abel] at hx
    rw [ha.eq_zero x hx.1, ha.eq_zero (x + h) hx.2, sub_zero, enorm_zero]

/-- **The switch term of a smooth atom**: `1_{S_h(U)}(x) |a(x)| ≤ A 1_{S_h(U) ∩ B̄(c, d 2^(-j))}(x)`
for a smooth atom `a` on `V` with level `j`, centre `c`, radius factor `d` and constant `A`, since
`|a| ≤ A` (`Rd.IsSmoothAtom.norm_le`) and `a` vanishes outside `B̄(c, d 2^(-j))`. -/
theorem IsSmoothAtom.indicator_switchSet_le {K : ℕ} {d A : ℝ} {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom univ K d A j c a) (U : Set V) (h x : V) :
    (switchSet U h).indicator (fun y => ‖a y‖ₑ) x ≤
      (switchSet U h ∩ closedBall c (d / 2 ^ j)).indicator (fun _ => ENNReal.ofReal A) x := by
  by_cases hs : x ∈ switchSet U h
  · by_cases hb : x ∈ closedBall c (d / 2 ^ j)
    · rw [indicator_of_mem hs, indicator_of_mem (mem_inter hs hb), ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (ha.norm_le (mem_univ x))
    · rw [mem_closedBall, dist_eq_norm, not_le] at hb
      rw [indicator_of_mem hs, ha.eq_zero x hb, enorm_zero]
      exact zero_le
  · rw [indicator_of_notMem hs]
    exact zero_le

/-- **The norm of `1_U a` for a smooth atom `a`**: for `1 ≤ p`, a measurable `U`, `d ≥ 1` and a
smooth atom `a` on `V` of order `1` with level `j`, radius factor `d` and constant `A`,
`‖1_U a‖_p ≤ |B_1|^(1/p) A d^n 2^(-jn/p)`, since `|1_U a| ≤ A` (`Rd.IsSmoothAtom.norm_le`)
vanishes outside `B̄(c, d 2^(-j))` (`Rd.eLpNorm_le_of_bound_of_support`) and `(d^n)^(1/p) ≤ d^n`
(`ENNReal.rpow_le_self_of_one_le`). -/
theorem IsSmoothAtom.eLpNorm_indicator_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {U : Set V}
    (hU : MeasurableSet U) {d A : ℝ} (hd : 1 ≤ d) {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom univ 1 d A j c a) :
    eLpNorm (U.indicator a) p volume ≤ volume (ball (0 : V) 1) ^ (1 / p.toReal) *
      ENNReal.ofReal (A * d ^ finrank ℝ V) * dyadicWeight (-(finrank ℝ V / p.toReal)) j := by
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hτ0 : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hτ1 : 1 / p.toReal ≤ 1 := by linarith [one_sub_one_div_toReal_nonneg hp1]
  have hD : ENNReal.ofReal (d ^ finrank ℝ V) ^ (1 / p.toReal) ≤ ENNReal.ofReal (d ^ finrank ℝ V) :=
    ENNReal.rpow_le_self_of_one_le (ENNReal.one_le_ofReal.2 (one_le_pow₀ hd)) hτ1
  refine (eLpNorm_le_of_bound_of_support (ha.aestronglyMeasurable.indicator hU)
    (S := closedBall c (d / 2 ^ j)) (B := ENNReal.ofReal A) (fun x hx => ?_) (fun x => ?_)).trans ?_
  · rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact indicator_apply_eq_zero.2 fun _ => ha.eq_zero x hx
  · refine (enorm_indicator_le_enorm_self a x).trans ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ha.norm_le (mem_univ x))
  · rw [volume_closedBall_div_two_pow hd0 j c, ENNReal.rpow_mul_dyadicWeight_neg,
      ENNReal.mul_rpow_of_nonneg _ _ hτ0, ENNReal.ofReal_mul ha.const_nonneg]
    calc ENNReal.ofReal A * (ENNReal.ofReal (d ^ finrank ℝ V) ^ (1 / p.toReal) *
          volume (ball (0 : V) 1) ^ (1 / p.toReal) * dyadicWeight (-(finrank ℝ V / p.toReal)) j)
        ≤ ENNReal.ofReal A * (ENNReal.ofReal (d ^ finrank ℝ V) *
          volume (ball (0 : V) 1) ^ (1 / p.toReal) *
            dyadicWeight (-(finrank ℝ V / p.toReal)) j) := by
          gcongr
      _ = _ := by ring

/-- **Differences of `1_U a` for a smooth atom `a`**: let `1 ≤ p`, `U` measurable, `d ≥ 1`,
`a` a smooth atom on `V` of order `1` with level `j`, centre `c`, radius factor `d` and
constant `A`, and let the switch set of `U` for the step `h` satisfy
`|S_h(U) ∩ B̄(c, d 2^(-j))| ≤ C d^n 2^(-jn) min(1, 2^j ‖h‖)`. Then
`‖Δ_h(1_U a)‖_p ≤ (4 |B_1|^(1/p) + C^(1/p)) A d^n 2^(-jn/p) min(1, (2^j ‖h‖)^(1/p))`. The pointwise
bound `Rd.enorm_indicator_add_sub_le` with `Rd.IsSmoothAtom.enorm_sub_le_indicator` and
`Rd.IsSmoothAtom.indicator_switchSet_le` gives two indicators
(`Rd.eLpNorm_le_of_enorm_le_indicator_add`); for `1/p ≤ 1`, `m = min(1, 2^j ‖h‖) ≤ m^(1/p)`,
`(d^n)^(1/p) ≤ d^n` and `2^(1/p) ≤ 2` (`ENNReal.rpow_le_self_of_one_le`). -/
theorem IsSmoothAtom.eLpNorm_fwdDiff_indicator_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {U : Set V}
    (hU : MeasurableSet U) {d A : ℝ} (hd : 1 ≤ d) {j : ℕ} {c : V} {a : V → ℂ}
    (ha : IsSmoothAtom univ 1 d A j c a) {h : V} {C : ℝ≥0∞}
    (hC : volume (switchSet U h ∩ closedBall c (d / 2 ^ j)) ≤ C *
      ENNReal.ofReal (d ^ finrank ℝ V) * dyadicWeight (-(finrank ℝ V : ℝ)) j *
        min 1 (ENNReal.ofReal (2 ^ j * ‖h‖))) :
    eLpNorm (fwdDiff h (U.indicator a)) p volume ≤
      (4 * volume (ball (0 : V) 1) ^ (1 / p.toReal) + C ^ (1 / p.toReal)) *
        ENNReal.ofReal (A * d ^ finrank ℝ V) * dyadicWeight (-(finrank ℝ V / p.toReal)) j *
          min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (1 / p.toReal)) := by
  set τ := 1 / p.toReal
  set D := ENNReal.ofReal (d ^ finrank ℝ V)
  set β := volume (ball (0 : V) 1)
  set w := dyadicWeight (-(finrank ℝ V : ℝ)) j
  set W := dyadicWeight (-(finrank ℝ V / p.toReal)) j
  set m := min 1 (ENNReal.ofReal (2 ^ j * ‖h‖))
  set M := min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ τ)
  set S₁ := closedBall c (d / 2 ^ j) ∪ closedBall (c - h) (d / 2 ^ j)
  set S₂ := switchSet U h ∩ closedBall c (d / 2 ^ j)
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hτ0 : 0 ≤ τ := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hτ1 : τ ≤ 1 := by linarith [one_sub_one_div_toReal_nonneg hp1]
  have hD : D ^ τ ≤ D :=
    ENNReal.rpow_le_self_of_one_le (ENNReal.one_le_ofReal.2 (one_le_pow₀ hd)) hτ1
  have hm : m ^ τ ≤ M := le_min (ENNReal.rpow_le_one (min_le_left _ _) hτ0)
    (ENNReal.rpow_le_rpow (min_le_right _ _) hτ0)
  have hmM : m ≤ M := ((ENNReal.rpow_one m).symm.le.trans
    (ENNReal.rpow_le_rpow_of_exponent_ge (min_le_left _ _) hτ1)).trans hm
  have h2 : (2 : ℝ≥0∞) ^ τ ≤ 2 := ENNReal.rpow_le_self_of_one_le one_le_two hτ1
  have hW : ∀ X : ℝ≥0∞, (X * w) ^ τ = X ^ τ * W := fun X =>
    ENNReal.rpow_mul_dyadicWeight_neg X (finrank ℝ V) p j
  have hS₁ : volume S₁ ≤ 2 * (D * β * w) :=
    (measure_union_le _ _).trans_eq (by
      rw [volume_closedBall_div_two_pow hd0 j, volume_closedBall_div_two_pow hd0 j, two_mul])
  have hpt : ∀ x, ‖fwdDiff h (U.indicator a) x‖ₑ ≤
      S₁.indicator (fun _ => ENNReal.ofReal (2 * A) * m) x +
        S₂.indicator (fun _ => ENNReal.ofReal A) x := fun x =>
    (enorm_indicator_add_sub_le U a h x).trans
      (add_le_add (ha.enorm_sub_le_indicator h x) (ha.indicator_switchSet_le U h x))
  refine (eLpNorm_le_of_enorm_le_indicator_add hp1
    (aestronglyMeasurable_higherDiff (ha.aestronglyMeasurable.indicator hU) 1 h)
    (measurableSet_closedBall.union measurableSet_closedBall)
    ((measurableSet_switchSet hU h).inter measurableSet_closedBall) hpt).trans ?_
  have e1 : (2 * (D * β * w)) ^ τ = 2 ^ τ * (D ^ τ * β ^ τ * W) := by
    rw [ENNReal.mul_rpow_of_nonneg 2 (D * β * w) hτ0, hW (D * β),
      ENNReal.mul_rpow_of_nonneg D β hτ0]
  have e2 : (C * D * m * w) ^ τ = C ^ τ * D ^ τ * m ^ τ * W := by
    rw [hW (C * D * m), ENNReal.mul_rpow_of_nonneg (C * D) m hτ0,
      ENNReal.mul_rpow_of_nonneg C D hτ0]
  calc ENNReal.ofReal (2 * A) * m * volume S₁ ^ τ + ENNReal.ofReal A * volume S₂ ^ τ
      ≤ ENNReal.ofReal (2 * A) * m * (2 * (D * β * w)) ^ τ +
          ENNReal.ofReal A * (C * D * m * w) ^ τ := by
        gcongr
        exact hC.trans_eq (by ring)
    _ = 2 * ENNReal.ofReal A * m * (2 ^ τ * (D ^ τ * β ^ τ * W)) +
          ENNReal.ofReal A * (C ^ τ * D ^ τ * m ^ τ * W) := by
        rw [e1, e2, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    _ ≤ 2 * ENNReal.ofReal A * M * (2 * (D * β ^ τ * W)) +
          ENNReal.ofReal A * (C ^ τ * D * M * W) := by
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul ha.const_nonneg]
        ring

/-! ### The multiplier theorem -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **Indicators of smooth atoms are regular atoms** (the mechanism of Schneider–Vybíral,
Theorem 5.4(i)): for `1 ≤ p` (`p = ∞` included, with exponent `1/∞ = 0`) there is `K < ∞` such
that for every smooth atom `a` on `V` of order `1`, level `j`, centre `c`, radius factor `d ≥ 1`
and constant `A`, the function `1_Ω a` is a regular atom of exponent `1/p` and order `1` with the
constant `K A d^n` (`Rd.IsSmoothAtom.eLpNorm_indicator_le`,
`Rd.IsSmoothAtom.eLpNorm_fwdDiff_indicator_le`, with the boundary layer
`Rd.BoundedLipschitzDomain.exists_volume_switchSet_inter_closedBall_div_two_pow_le`). The
exponent `1/p` is the volume of the layer, `≈ ‖h‖ ρ^(n-1)`, raised to `1/p`. -/
theorem exists_isRegularAtom_indicator {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ {d A : ℝ} {j : ℕ} {c : V} {a : V → ℂ}, 1 ≤ d →
      IsSmoothAtom univ 1 d A j c a →
        IsRegularAtom p (1 / p.toReal) 1 d (K * ENNReal.ofReal (A * d ^ finrank ℝ V)) j c
          (Ω.carrier.indicator a) := by
  obtain ⟨C, hC, hlayer⟩ := Ω.exists_volume_switchSet_inter_closedBall_div_two_pow_le
  have hτ0 : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  refine ⟨4 * volume (ball (0 : V) 1) ^ (1 / p.toReal) + C ^ (1 / p.toReal),
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_ne_top_of_nonneg hτ0 measure_ball_lt_top.ne),
      ENNReal.rpow_ne_top_of_nonneg hτ0 hC⟩, fun {d A j c a} hd ha => ?_⟩
  refine ⟨ha.aestronglyMeasurable.indicator Ω.measurableSet,
    fun x hx => indicator_apply_eq_zero.2 fun _ => ha.eq_zero x hx, ?_, fun h => ?_⟩
  · rw [indicator_univ]
    refine (ha.eLpNorm_indicator_le hp1 Ω.measurableSet hd).trans ?_
    gcongr
    calc volume (ball (0 : V) 1) ^ (1 / p.toReal)
        ≤ 4 * volume (ball (0 : V) 1) ^ (1 / p.toReal) := le_mul_of_one_le_left' (by norm_num)
      _ ≤ _ := le_self_add
  · rw [stepSet_univ, indicator_univ, Function.iterate_one]
    exact ha.eLpNorm_fwdDiff_indicator_le hp1 Ω.measurableSet hd (hlayer c h hd j)

/-- **The indicator of a bounded Lipschitz domain is a pointwise multiplier of `B^s_{p,q}(V)` for
`0 < s < 1/p`** (Triebel 2002, Proposition 5.3 and Remark 5.4; Schneider–Vybíral, Theorem 5.4(i)
and Remark 5.10): for `1 ≤ p < ∞` there is `C < ∞` with
`‖1_Ω F‖_p + ‖(2^(ks) ω_1(1_Ω F, 2^(-k))_p)_k‖_{ℓ_q}`
`≤ C (‖F‖_p + ‖(2^(ks) ω_1(F, 2^(-k))_p)_k‖_{ℓ_q})` for every `1 ≤ q ≤ ∞` and every
`F ∈ L_p(V)`. The smooth cell atoms of `F`
(`Rd.LocalMeansBump.atomic_decomposition_smooth` with the standard bump, radius factor `2 + n`)
become regular atoms of exponent `1/p` after multiplication by `1_Ω`
(`Rd.BoundedLipschitzDomain.exists_isRegularAtom_indicator`), with the same coefficients; the
reproducing formula (`Rd.LocalMeansBump.tendsto_sum_dual_localMean`) passes through the bounded
operator `1_Ω`; the atomic synthesis (`Rd.modNorm_le_coeffNorm`) and the bound of the local means
by differences (`Rd.LocalMeansBump.localMeansNorm_le`) finish the proof. -/
theorem exists_modNorm_indicatorLp_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {q : ℝ≥0∞}, 1 ≤ q → ∀ F : Lp ℂ p (volume : Measure V),
      ‖indicatorLp Ω.measurableSet F‖ₑ + lqNorm q (fun k =>
          dyadicWeight s k * lpModulus p 1 (indicatorLp Ω.measurableSet F) k) ≤
        C * (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 F k)) := by
  have hp1 : 1 ≤ p := Fact.out
  set b : LocalMeansBump V := LocalMeansBump.std
  have hb : b.radius = 1 := LocalMeansBump.centered_radius one_pos
  set d : ℝ := 2 * ((1 : ℕ) : ℝ) * b.radius + finrank ℝ V
  have hd : 1 ≤ d := by
    simp only [d, hb, Nat.cast_one]
    linarith [(Nat.cast_nonneg (finrank ℝ V) : (0 : ℝ) ≤ finrank ℝ V)]
  obtain ⟨A, -, hdec⟩ := b.atomic_decomposition_smooth hp 1 1
  obtain ⟨K, hK, hind⟩ := Ω.exists_isRegularAtom_indicator hp1
  set N := ⌈(2 * (d + ((1 : ℕ) : ℝ)) + 2) ^ finrank ℝ V⌉₊
  set C' := K * ENNReal.ofReal (A * d ^ finrank ℝ V)
  have hC' : C' ≠ ∞ := ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top
  refine ⟨atomSynthConst p N C' 1 s (1 / p.toReal) * b.upperConst 1 s,
    ENNReal.mul_ne_top (atomSynthConst_ne_top hp1 N hC' 1 hs hsp) (b.upperConst_ne_top 1 s),
    fun {q} hq F => ?_⟩
  obtain ⟨hatom, hsum, hcoef⟩ := hdec F
  set G : ℕ → Lp ℂ p (volume : Measure V) := fun j => b.localMean hp 1 j F
  have hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1),
      indicatorLp Ω.measurableSet (convLp hp (b.integrable_dual 1 j) (G j))) atTop
      (𝓝 (indicatorLp Ω.measurableSet F)) :=
    (((indicatorLp Ω.measurableSet).continuous.tendsto F).comp
      (b.tendsto_sum_dual_localMean hp le_rfl F)).congr fun J => by
        simp only [Function.comp_apply, map_sum]
        rfl
  have hf : ∀ j, ∀ᵐ x ∂volume,
      indicatorLp Ω.measurableSet (convLp hp (b.integrable_dual 1 j) (G j)) x =
        ∑' m, cellCoef p j (G j) m * Ω.carrier.indicator (cellAtom p (b.dual 1 j) j (G j) m) x :=
    fun j => by
      filter_upwards [indicatorLp_apply_ae Ω.measurableSet
        (convLp hp (b.integrable_dual 1 j) (G j)), hsum j] with x hx hxs
      rw [hx]
      by_cases hxΩ : x ∈ Ω.carrier
      · simp only [indicator_of_mem hxΩ]
        exact hxs
      · simp only [indicator_of_notMem hxΩ, mul_zero, tsum_zero]
  have hN : ∀ j x (S : Finset (Fin (finrank ℝ V) → ℤ)),
      (∀ m ∈ S, cellCoef p j (G j) m ≠ 0 ∧ ‖x - cellCenter j m‖ ≤ (d + ((1 : ℕ) : ℝ)) / 2 ^ j) →
        S.card ≤ N := fun j x S hS =>
    card_le_of_norm_sub_cellCenter_le j (by linarith) x S fun m hm => (hS m hm).2
  have hsyn := modNorm_le_coeffNorm hp (fun j m => cellCenter j m)
    (fun j m => Ω.carrier.indicator (cellAtom p (b.dual 1 j) j (G j) m))
    (fun j => cellCoef p j (G j)) hN (fun j m => hind hd (hatom j m)) hf hF hs hsp hq
  rw [hcoef s q] at hsyn
  refine hsyn.trans ?_
  rw [mul_assoc]
  gcongr
  exact b.localMeansNorm_le hp 1 s hq F

end BoundedLipschitzDomain

end Rd
