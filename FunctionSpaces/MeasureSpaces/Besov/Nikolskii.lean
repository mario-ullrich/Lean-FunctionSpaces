/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.Besov.ElementaryEmbeddings
public import FunctionSpaces.Analysis.Lp.QuasiNorm
public import ApproximationSpaces.Lift

/-!
# The Nikolskii inequality of a scheme

A scheme of functions `S` on a measure space `(Ω, μ)` has the **Nikolskii property of
dimension `D`** if for every `1 ≤ p ≤ ∞` there is `C` with

`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p`   for all `a ∈ S n`, `n ≥ 1`

(`FunctionScheme.HasNikolskii`), a hypothesis on the scheme; here `‖a‖_∞` is the norm of the
class `a` in `L_∞(μ)`. The constants are real numbers, which fits a finite measure, where all
these quasi-norms are finite. At `p = ∞` the bound holds with `C = 1` for every scheme. On a
finite measure space the bound in `[0, ∞]` with `C < ∞` for every `1 ≤ p < ∞` gives the property
(`FunctionScheme.HasNikolskii.of_eLpNorm_top_le`), and for the scheme of an approximation scheme
`T` of bounded continuous functions the same bound with the sup norm of the elements of `T` for
every `1 ≤ p < ∞` suffices (`FunctionScheme.hasNikolskii_ofContinuous`), since the `L_∞` norm of
a bounded continuous function is at most its sup norm
(`BoundedContinuousFunction.toReal_eLpNorm_top_le_norm`). The property holds with `D = d` for
the trigonometric polynomials of degree `< n` on `𝕋^d` (`Torus.trigScheme_hasNikolskii`,
`Torus.hasNikolskii_fourierEigenbasis`) and with `D = 1` for the dyadic step functions on
`[0, 1)` (`Haar.hasNikolskii_haarScheme`).

The property asks `p ≥ 1` only, and yet it controls every `0 < p ≤ ∞`: for `0 < p < 1` the
bound `‖a‖_∞ ≤ C₁ n^D ‖a‖_1` at `p = 1` gives `‖a‖_∞ ≤ C₁^(1/p) n^(D/p) ‖a‖_p`
(Ditzian–Prymak 2016, Theorem 2.1; `HasNikolskii.exists_eLpNorm_top_le`). The property is
stated against `L_∞` only; the general **Nikolskii inequality**

`‖a‖_r ≤ C' n^(D (1/p - 1/r)) ‖a‖_p`,   `0 < p ≤ r ≤ ∞`

follows by interpolation, `‖a‖_r ≤ ‖a‖_∞^(1 - p/r) ‖a‖_p^(p/r)`
(`HasNikolskii.exists_eLpNorm_le_of_le`), an inequality in `[0, ∞]` whose proof uses no
finiteness of `μ`; the real form `HasNikolskii.eLpNorm_le` and the lifting bound below take `μ`
finite. The interpolation uses only the bound at the source exponent `p`, the **Nikolskii bound
at `p`** (`FunctionScheme.HasNikolskiiAt`), which alone gives the inequality from `L_p` to every
`L_r`, `p ≤ r ≤ ∞` (`HasNikolskiiAt.exists_eLpNorm_le_mul`). The property gives this bound at
every `0 < p ≤ ∞` (`HasNikolskii.hasNikolskiiAt`), and for the scheme of `T` the sup-norm bound
of the elements of `T` at one `p` gives it at that `p`
(`FunctionScheme.hasNikolskiiAt_ofContinuous`). On the blocks
`b_{k+1} - b_k ∈ S_{2^(k+2)}` of a sequence `b_k ∈ S_{2^k}` the inequality reads
`‖b_{k+1} - b_k‖_r ≤ C 2^(2α) 2^(kα) ‖b_{k+1} - b_k‖_p` with `α = D (1/p - 1/r)`
(`FunctionScheme.eLpNorm_sub_succ_le_of_nikolskii`). The
exponent `D (1/p - 1/r)` is `nikolskiiExponent D p r`, equal to `(D/p)(1 - p/r)` for
`0 < p ≤ r` (`nikolskiiExponent_eq_mul_one_sub_div`); for `D > 0`, `0 < p < ∞` and `r > 0` it is
positive iff `p < r` and nonnegative iff `p ≤ r`
(`nikolskiiExponent_pos`, `lt_of_nikolskiiExponent_pos`, `le_of_nikolskiiExponent_nonneg`).
With `θ = p₀/p₁` and `s₀ - s₁ = D(1/p₀ - 1/p₁)`, `θ s₀ + (1 - θ)(s₀ - D/p₀) = s₁`
(`nikolskiiExponent_interp_eq`). For the Gagliardo–Nirenberg–Sobolev inequality,
`D(1/p - 1/r) = 1` with `D ≥ 0` means `p < ∞` and `1/r = 1/p - 1/D`
(`toReal_inv_eq_of_nikolskiiExponent_eq_one`), which follows from `1/r + 1/n = 1/p` for `D = n`
(`nikolskiiExponent_eq_one_of_inv_add_inv`), and `n(1 - 1/r) = m ≥ 2` passes through the
conjugate exponent `n/(n - 1)` (`nikolskiiExponent_conjExponent_of_eq`).

In the language of `ApproximationSpaces.Lift` this is, for `1 ≤ p ≤ r`, a lifting bound for the
inclusion `L_r ↪ L_p` and the scheme in `L_p` (`HasNikolskii.liftBound`): the approximant `a` in
`L_p` is the inclusion of the same function in `L_r`, of norm at most
`C' n^(D(1/p - 1/r)) ‖a‖_p`.

The norms are written with `eLpNorm`, a function of representatives, so one statement
quantifies over all exponents `1 ≤ p ≤ ∞`, without an instance `Fact (1 ≤ p)` for each.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

/-- The **Nikolskii exponent** `D (1/p - 1/r)`.  With `1/∞ = 0` (in Lean `∞.toReal = 0` and
`0⁻¹ = 0`) it is `D/p` for `r = ∞`. -/
noncomputable def nikolskiiExponent (D : ℝ) (p r : ℝ≥0∞) : ℝ := D * (p.toReal⁻¹ - r.toReal⁻¹)

/-- `D(1/p - 1/r) ≥ 0` for `D ≥ 0` and `0 < p ≤ r ≤ ∞`, since then `1/r ≤ 1/p`
(`ENNReal.one_div_toReal_sub_one_div_toReal_nonneg`). -/
theorem nikolskiiExponent_nonneg {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp0 : p ≠ 0) (hpr : p ≤ r) :
    0 ≤ nikolskiiExponent D p r :=
  mul_nonneg hD (by
    simpa only [one_div] using ENNReal.one_div_toReal_sub_one_div_toReal_nonneg hp0 hpr)

/-- A natural number `m` above the Nikolskii exponent is at least `1`: for `D ≥ 0`,
`0 < p ≤ r ≤ ∞` and `m ∈ ℕ` with `m > D(1/p - 1/r)`, `m ≥ 1`, since the exponent is
nonnegative (`nikolskiiExponent_nonneg`). -/
theorem one_le_of_nikolskiiExponent_lt {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpr : p ≤ r) {m : ℕ} (hm : nikolskiiExponent D p r < m) : 1 ≤ m :=
  Nat.one_le_iff_ne_zero.2
    (Nat.cast_pos.1 ((nikolskiiExponent_nonneg hD hp0 hpr).trans_lt hm)).ne'

/-- **The Nikolskii exponent is positive** for `D > 0` and `0 < p < r ≤ ∞`, since then
`1/r < 1/p`. -/
theorem nikolskiiExponent_pos {D : ℝ} (hD : 0 < D) {p r : ℝ≥0∞} (hp0 : p ≠ 0) (hpr : p < r) :
    0 < nikolskiiExponent D p r := by
  unfold nikolskiiExponent
  refine mul_pos hD (sub_pos.2 ?_)
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 (hpr.trans_le le_top).ne
  rcases eq_or_ne r ∞ with rfl | hr
  · simpa using hpp
  exact inv_strictAnti₀ hpp (ENNReal.toReal_strict_mono hr hpr)

/-- **A positive Nikolskii exponent forces `p < r`**: for `D ≥ 0`, `p < ∞` and `r > 0`, if
`D(1/p - 1/r) > 0`, then `p < r`; for `r ≤ p` the exponent is `≤ 0`. -/
theorem lt_of_nikolskiiExponent_pos {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp : p ≠ ∞) (hr : 0 < r)
    (h : 0 < nikolskiiExponent D p r) : p < r := by
  by_contra hrp
  rw [not_lt] at hrp
  have hr' : r ≠ ∞ := ne_top_of_le_ne_top hp hrp
  have hle : p.toReal⁻¹ ≤ r.toReal⁻¹ :=
    inv_anti₀ (ENNReal.toReal_pos hr.ne' hr') (ENNReal.toReal_mono hp hrp)
  unfold nikolskiiExponent at h
  nlinarith

/-- **A nonnegative Nikolskii exponent forces `p ≤ r`**: for `D > 0`, `p < ∞` and `r > 0`, if
`D(1/p - 1/r) ≥ 0`, then `p ≤ r`; for `r < p` the exponent is `< 0`. -/
theorem le_of_nikolskiiExponent_nonneg {D : ℝ} (hD : 0 < D) {p r : ℝ≥0∞} (hp : p ≠ ∞)
    (hr : 0 < r) (h : 0 ≤ nikolskiiExponent D p r) : p ≤ r := by
  by_contra hrp
  rw [not_le] at hrp
  have hr' : r ≠ ∞ := ne_top_of_lt hrp
  have hlt : p.toReal⁻¹ < r.toReal⁻¹ :=
    inv_strictAnti₀ (ENNReal.toReal_pos hr.ne' hr') (ENNReal.toReal_strict_mono hp hrp)
  unfold nikolskiiExponent at h
  nlinarith

/-- **The interpolation identity of the Nikolskii exponent**: for `0 < p₀ < ∞`, `θ = p₀/p₁` and
`s₀ - s₁ = D(1/p₀ - 1/p₁)`, `θ s₀ + (1 - θ)(s₀ - D/p₀) = s₁`, since `θ/p₀ = 1/p₁`. -/
theorem nikolskiiExponent_interp_eq {D s₀ s₁ : ℝ} {p₀ p₁ : ℝ≥0∞} (hp₀0 : p₀ ≠ 0) (hp₀ : p₀ ≠ ∞)
    (hs : s₀ - s₁ = nikolskiiExponent D p₀ p₁) :
    p₀.toReal / p₁.toReal * s₀ + (1 - p₀.toReal / p₁.toReal) * (s₀ - D / p₀.toReal) = s₁ := by
  have h0 : p₀.toReal ≠ 0 := (ENNReal.toReal_pos hp₀0 hp₀).ne'
  unfold nikolskiiExponent at hs
  rw [show s₁ = s₀ - D * (p₀.toReal⁻¹ - p₁.toReal⁻¹) by linarith]
  field_simp
  ring

/-- `α(D, p, ∞) = D/p`. -/
@[simp]
theorem nikolskiiExponent_top (D : ℝ) (p : ℝ≥0∞) : nikolskiiExponent D p ∞ = D * p.toReal⁻¹ := by
  simp [nikolskiiExponent]

/-- `α(D, p, p) = 0`. -/
@[simp]
theorem nikolskiiExponent_self (D : ℝ) (p : ℝ≥0∞) : nikolskiiExponent D p p = 0 := by
  simp [nikolskiiExponent]

/-- **The Nikolskii exponent as an interpolated exponent**: for `0 < p ≤ r ≤ ∞`,
`D(1/p - 1/r) = (D/p)(1 - p/r)`, with `1/∞ = 0` and `p/∞ = 0`. This is the exponent of `n` that
interpolation between `L_p` and `L_∞` produces from a bound `‖a‖_∞ ≤ C n^(D/p) ‖a‖_p`. -/
theorem nikolskiiExponent_eq_mul_one_sub_div (D : ℝ) {p r : ℝ≥0∞} (hp0 : p ≠ 0) (hpr : p ≤ r) :
    nikolskiiExponent D p r = D * p.toReal⁻¹ * (1 - p.toReal / r.toReal) := by
  unfold nikolskiiExponent
  rcases eq_or_ne r ∞ with rfl | hr
  · simp
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top hr hpr)
  have hrr : 0 < r.toReal := hpp.trans_le (ENNReal.toReal_mono hr hpr)
  field_simp

/-- **The Nikolskii exponent `1`**: for `D ≥ 0`, `D(1/p - 1/r) = 1` forces `D > 0`, `p < ∞` and
`1/r = 1/p - 1/D`; for `p = ∞` the exponent is `-D/r ≤ 0`. -/
theorem toReal_inv_eq_of_nikolskiiExponent_eq_one {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞}
    (hs : nikolskiiExponent D p r = 1) : 0 < D ∧ p ≠ ∞ ∧ r.toReal⁻¹ = p.toReal⁻¹ - D⁻¹ := by
  unfold nikolskiiExponent at hs
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs
    exact zero_ne_one hs
  refine ⟨lt_of_le_of_ne hD (Ne.symm hD0), fun hp => ?_, ?_⟩
  · rw [hp, ENNReal.toReal_top, inv_zero, zero_sub] at hs
    have : 0 ≤ r.toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
    nlinarith
  · have h : p.toReal⁻¹ - r.toReal⁻¹ = D⁻¹ := eq_inv_of_mul_eq_one_right hs
    linarith

/-- **The exponents in the form `1/r + 1/n = 1/p`**: for `n ∈ ℕ`, `0 < p` and
`r⁻¹ + n⁻¹ = p⁻¹` in `[0, ∞]` (where `1/0 = ∞`), `p < ∞` and `n(1/p - 1/r) = 1`. The inverses
`r⁻¹` and `n⁻¹` are at most `p⁻¹ < ∞`, so the identity holds between real numbers. -/
theorem nikolskiiExponent_eq_one_of_inv_add_inv {n : ℕ} {p r : ℝ≥0∞} (hp0 : p ≠ 0)
    (hexp : r⁻¹ + (n : ℝ≥0∞)⁻¹ = p⁻¹) : p ≠ ∞ ∧ nikolskiiExponent n p r = 1 := by
  have hpinv : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hp0
  have hr0 : r⁻¹ ≠ ∞ := ne_top_of_le_ne_top hpinv (le_self_add.trans hexp.le)
  have hn0 : (n : ℝ≥0∞)⁻¹ ≠ ∞ := ne_top_of_le_ne_top hpinv (le_add_self.trans hexp.le)
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hn0
  refine ⟨fun hpt => ?_, ?_⟩
  · rw [hpt, ENNReal.inv_top, add_eq_zero] at hexp
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n) hexp.2
  have h := congrArg ENNReal.toReal hexp
  rw [ENNReal.toReal_add hr0 hn0, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at h
  unfold nikolskiiExponent
  rw [← h, add_sub_cancel_left, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)]

/-- For `m ≥ 2`, `n(1 - 1/r) = m` forces `n > 1`, since `1/r ≥ 0`. -/
theorem one_lt_of_nikolskiiExponent_one_eq {n m : ℕ} (hm : 2 ≤ m) {r : ℝ≥0∞}
    (hs : nikolskiiExponent n 1 r = m) : 1 < n := by
  unfold nikolskiiExponent at hs
  rw [ENNReal.toReal_one, inv_one] at hs
  have ha : 0 ≤ r.toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : (1 : ℝ) < n := by nlinarith
  exact_mod_cast h

/-- **The intermediate exponent `q = n/(n - 1)`**: for `m ≥ 2`, every `r ∈ [0, ∞]` with
`n(1 - 1/r) = m` and the conjugate exponent `q = n/(n - 1)` of `n` (Mathlib's
`ENNReal.conjExponent`), `1 < q < ∞`, `n(1 - 1/q) = 1` and `n(1/q - 1/r) = m - 1`: Hölder
conjugacy gives `1/q + 1/n = 1` (`nikolskiiExponent_eq_one_of_inv_add_inv`), and
`n > 1` (`one_lt_of_nikolskiiExponent_one_eq`). -/
theorem nikolskiiExponent_conjExponent_of_eq {n m : ℕ} (hm : 2 ≤ m) {r : ℝ≥0∞}
    (hs : nikolskiiExponent n 1 r = m) :
    1 < ENNReal.conjExponent n ∧ ENNReal.conjExponent n ≠ ∞ ∧
      nikolskiiExponent n 1 (ENNReal.conjExponent n) = 1 ∧
      nikolskiiExponent n (ENNReal.conjExponent n) r = ((m - 1 : ℕ) : ℝ) := by
  have hn : (1 : ℝ≥0∞) < n := by exact_mod_cast one_lt_of_nikolskiiExponent_one_eq hm hs
  have : (n : ℝ≥0∞).HolderConjugate (ENNReal.conjExponent n) := .conjExponent hn.le
  have h1 : nikolskiiExponent n 1 (ENNReal.conjExponent n) = 1 :=
    (nikolskiiExponent_eq_one_of_inv_add_inv one_ne_zero (by
      rw [inv_one, add_comm]
      exact ENNReal.HolderConjugate.inv_add_inv_eq_one _ _)).2
  refine ⟨(ENNReal.HolderConjugate.lt_top_iff_one_lt _ _).1 (ENNReal.natCast_lt_top n),
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt _ _).2 hn).ne, h1, ?_⟩
  obtain ⟨-, -, hq⟩ := toReal_inv_eq_of_nikolskiiExponent_eq_one (Nat.cast_nonneg n) h1
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (one_lt_of_nikolskiiExponent_one_eq hm hs).ne_bot
  unfold nikolskiiExponent at hs ⊢
  rw [ENNReal.toReal_one, inv_one] at hs hq
  rw [hq, Nat.cast_sub (by omega), Nat.cast_one, ← hs]
  field_simp
  ring

namespace FunctionScheme

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **Nikolskii property of dimension `D`**: for every `1 ≤ p ≤ ∞`,
`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all approximants `a ∈ S n`, `n ≥ 1`, with the norm `‖a‖_∞` of the
class `a` in `L_∞(μ)`. A hypothesis on the scheme; the trigonometric polynomials on the torus
(`Torus.trigScheme_hasNikolskii`) and the dyadic step functions on `[0, 1)`
(`Haar.hasNikolskii_haarScheme`) have it. The property asks `p ≥ 1` only, since the bound at
`p = 1` gives the bound for every `0 < p < 1`
(`FunctionScheme.HasNikolskii.exists_eLpNorm_top_le`). It is meant for a finite measure, where
all the quasi-norms are finite; on an infinite measure the real form forces every approximant to
lie in every `L_p`, `1 ≤ p < ∞`: if `‖a‖_p = ∞`, then `(‖a‖_p).toReal = 0`, so `‖a‖_∞ = 0`, and
then `a = 0` and `‖a‖_p = 0`. -/
structure HasNikolskii (S : FunctionScheme μ) (D : ℝ) : Prop where
  exists_const : ∀ p : ℝ≥0∞, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
    (eLpNorm a ∞ μ).toReal ≤ C * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal

variable {S : FunctionScheme μ} {D : ℝ}

/-- **The Nikolskii property of the scheme of a scheme of bounded continuous functions**: if an
approximation scheme `T` of bounded continuous functions satisfies, for every `1 ≤ p < ∞`,
`sup |a| ≤ C n^(D/p) ‖a‖_p` for all `a ∈ T n`, `n ≥ 1`, then its scheme of functions has the
Nikolskii property of dimension `D`, since `‖a‖_∞ ≤ sup |a|`. At `p = ∞` the bound of the
Nikolskii property reads `‖a‖_∞ ≤ C ‖a‖_∞` and holds with `C = 1` for every scheme. -/
theorem hasNikolskii_ofContinuous [IsFiniteMeasure μ] [TopologicalSpace Ω] [BorelSpace Ω]
    {T : ApproximationScheme (Ω →ᵇ ℂ)}
    (h : ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ T n,
      ‖a‖ ≤ C * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal) :
    (ofContinuous T μ).HasNikolskii D := by
  refine ⟨fun p hp => ?_⟩
  rcases eq_or_ne p ∞ with rfl | hp'
  · exact ⟨1, zero_le_one, fun n _ b _ => by simp⟩
  obtain ⟨C, hC, hCa⟩ := h p hp hp'
  refine ⟨C, hC, fun n hn _ hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := mem_ofContinuous.1 hb
  have hae := BoundedContinuousFunction.coeFn_toLp (E := ℂ) ∞ μ ℝ a
  rw [eLpNorm_congr_ae hae, eLpNorm_congr_ae hae]
  exact (BoundedContinuousFunction.toReal_eLpNorm_top_le_norm a).trans (hCa n hn a ha)

/-- **The Nikolskii bound for one exponent `1 ≤ p ≤ ∞`, in `[0, ∞]`**: under the Nikolskii
property of dimension `D` there is `C < ∞` with `‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all `a ∈ S n`,
`n ≥ 1`, as an inequality of extended nonnegative reals. The real bound of the property passes
to `[0, ∞]` because `‖a‖_∞ < ∞` for the class `a ∈ L_∞`. -/
theorem HasNikolskii.exists_eLpNorm_top_le_of_one_le (h : S.HasNikolskii D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      eLpNorm a ∞ μ ≤ C * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ := by
  obtain ⟨C, hC, hCa⟩ := h.exists_const p hp
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n hn a ha => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  calc eLpNorm a ∞ μ
      ≤ ENNReal.ofReal (C * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal) :=
        (ENNReal.le_ofReal_iff_toReal_le (Lp.eLpNorm_ne_top a) (by positivity)).2
          (hCa n hn a ha)
    _ ≤ ENNReal.ofReal C * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC,
          ← ENNReal.ofReal_rpow_of_pos hn0, ENNReal.ofReal_natCast]
        gcongr
        exact ENNReal.ofReal_toReal_le

/-- **The Nikolskii property from bounds in `[0, ∞]`**: on a finite measure space, if for every
`1 ≤ p < ∞` there is `C < ∞` with `‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all `a ∈ S n`, `n ≥ 1`, as an
inequality of extended nonnegative reals, then `S` has the Nikolskii property of dimension `D`.
This is the converse of `FunctionScheme.HasNikolskii.exists_eLpNorm_top_le_of_one_le`, for
`p < ∞`: on a finite measure space `‖a‖_p < ∞` for every class `a ∈ L_∞`, so the bound passes to
real numbers. At `p = ∞` the property holds with `C = 1` for every scheme. The hypothesis says
that `S` satisfies the Nikolskii bound of dimension `D` at every `1 ≤ p < ∞`
(`FunctionScheme.HasNikolskiiAt`). -/
theorem HasNikolskii.of_eLpNorm_top_le [IsFiniteMeasure μ]
    (h : ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      eLpNorm a ∞ μ ≤ C * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ) :
    S.HasNikolskii D := by
  refine ⟨fun p hp => ?_⟩
  rcases eq_or_ne p ∞ with rfl | hp'
  · exact ⟨1, zero_le_one, fun n _ b _ => by simp⟩
  obtain ⟨C, hC, hCa⟩ := h p hp hp'
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun n hn a ha => ?_⟩
  have hap : eLpNorm a p μ ≠ ∞ := ((Lp.memLp a).mono_exponent le_top).eLpNorm_ne_top
  have hN : (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn)) (ENNReal.natCast_ne_top n)
  calc (eLpNorm a ∞ μ).toReal
      ≤ (C * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hN) hap) (hCa n hn a ha)
    _ = C.toReal * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

/-- **The Nikolskii bound for every `0 < p ≤ ∞`** (Ditzian–Prymak 2016, Theorem 2.1, (2.2)):
under the Nikolskii property of dimension `D`, for every `0 < p ≤ ∞` there is `C < ∞` with
`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all `a ∈ S n`, `n ≥ 1`. For `p ≥ 1` this is the property itself
(`FunctionScheme.HasNikolskii.exists_eLpNorm_top_le_of_one_le`). For `p < 1` the property at
`p₀ = 1` gives `‖a‖_∞ ≤ C₁ n^D ‖a‖_1`, and the bootstrap
`MeasureTheory.le_rpow_mul_eLpNorm_of_ae_enorm_le` with the almost everywhere bound
`N = ‖a‖_∞ < ∞` of `|a|` turns it into `‖a‖_∞ ≤ (C₁ n^D)^(1/p) ‖a‖_p = C₁^(1/p) n^(D/p) ‖a‖_p`.
The conclusion is the Nikolskii bound at `p` (`FunctionScheme.HasNikolskiiAt`) written out;
`FunctionScheme.HasNikolskii.hasNikolskiiAt` states it in that form. -/
theorem HasNikolskii.exists_eLpNorm_top_le (h : S.HasNikolskii D) {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      eLpNorm a ∞ μ ≤ C * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ := by
  rcases le_or_gt 1 p with hp1 | hp1
  · exact h.exists_eLpNorm_top_le_of_one_le hp1
  obtain ⟨C, hC, hCa⟩ := h.exists_eLpNorm_top_le_of_one_le le_rfl
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 (hp1.trans ENNReal.one_lt_top).ne
  refine ⟨C ^ p.toReal⁻¹, ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hpp.le) hC,
    fun n hn a ha => ?_⟩
  have h1 := hCa n hn a ha
  rw [ENNReal.toReal_one, inv_one, mul_one] at h1
  have hN := ae_enorm_le_eLpNorm_top (a : Ω → ℂ) μ
  calc eLpNorm a ∞ μ
      ≤ (C * (n : ℝ≥0∞) ^ D) ^ ((1 : ℝ≥0∞).toReal / p.toReal) * eLpNorm a p μ :=
        le_rpow_mul_eLpNorm_of_ae_enorm_le hN (Lp.eLpNorm_ne_top a) hp0 hp1.le
          ENNReal.one_ne_top h1
    _ = C ^ p.toReal⁻¹ * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ := by
        rw [ENNReal.toReal_one, one_div, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hpp.le),
          ← ENNReal.rpow_mul]

variable (S D) in
/-- The **Nikolskii bound of dimension `D` at the exponent `p`**: there is `C < ∞` with
`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all approximants `a ∈ S n`, `n ≥ 1`, as an inequality of extended
nonnegative reals, with the norm `‖a‖_∞` of the class `a` in `L_∞(μ)` and `1/∞ = 0`. A
hypothesis on the scheme at one exponent: the Nikolskii property gives it at every `0 < p ≤ ∞`
(`FunctionScheme.HasNikolskii.hasNikolskiiAt`), and the local Weyl bound of a continuous spectral
basis gives it at every `0 < p ≤ 2` (`ContinuousSpectralBasis.hasNikolskiiAt_basisScheme`). It
yields the Nikolskii inequality from `L_p` to every `L_r`, `p ≤ r ≤ ∞`
(`FunctionScheme.HasNikolskiiAt.exists_eLpNorm_le_mul`), which is all that the Besov embeddings
of `FunctionSpaces.MeasureSpaces.Besov.Embeddings` use. It is meant for `0 < p ≤ ∞`: at `p = 0`
Lean reads `1/0 = 0` and `‖a‖_0 = 0`, so the bound would say that every approximant of
complexity `n ≥ 1` vanishes almost everywhere; every theorem that uses it assumes `p ≠ 0`. -/
def HasNikolskiiAt (p : ℝ≥0∞) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
    eLpNorm a ∞ μ ≤ C * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ

/-- **The Nikolskii property gives the Nikolskii bound at every exponent `0 < p ≤ ∞`**: under
the Nikolskii property of dimension `D`, `S` satisfies the Nikolskii bound of dimension `D` at
every `p ≠ 0` (`FunctionScheme.HasNikolskii.exists_eLpNorm_top_le`). -/
theorem HasNikolskii.hasNikolskiiAt (h : S.HasNikolskii D) {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    S.HasNikolskiiAt D p :=
  h.exists_eLpNorm_top_le hp0

/-- **The Nikolskii bound at `p` from the supremum norm**: if an approximation scheme `T` of
bounded continuous functions satisfies `sup |a| ≤ C n^(D/p) ‖a‖_p` for all `a ∈ T n`, `n ≥ 1`,
with a real constant `C ≥ 0`, then its scheme of functions satisfies the Nikolskii bound of
dimension `D` at `p` with the constant `C`, since the `L_∞` norm of the class of `a` is at most
`sup |a|` (`BoundedContinuousFunction.eLpNorm_top_le_enorm`). -/
theorem hasNikolskiiAt_ofContinuous [IsFiniteMeasure μ] [TopologicalSpace Ω] [BorelSpace Ω]
    {T : ApproximationScheme (Ω →ᵇ ℂ)} {p : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ a ∈ T n,
      ‖a‖ ≤ C * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal) :
    (ofContinuous T μ).HasNikolskiiAt D p := by
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n hn _ hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := mem_ofContinuous.1 hb
  have hae := BoundedContinuousFunction.coeFn_toLp (E := ℂ) ∞ μ ℝ a
  rw [eLpNorm_congr_ae hae, eLpNorm_congr_ae hae]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  calc eLpNorm a ∞ μ ≤ ENNReal.ofReal ‖a‖ :=
        (BoundedContinuousFunction.eLpNorm_top_le_enorm a).trans_eq (ofReal_norm a).symm
    _ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal) :=
        ENNReal.ofReal_le_ofReal (h n hn a ha)
    _ ≤ ENNReal.ofReal C * (n : ℝ≥0∞) ^ (D * p.toReal⁻¹) * eLpNorm a p μ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC,
          ← ENNReal.ofReal_rpow_of_pos hn0, ENNReal.ofReal_natCast]
        gcongr
        exact ENNReal.ofReal_toReal_le

/-- **The Nikolskii inequality from the bound at the source exponent**, for
`0 < p ≤ r ≤ ∞`, in `[0, ∞]` (Ditzian–Prymak 2016, Theorem 2.1, (2.3) with `q = p`): if `S`
satisfies the Nikolskii bound `‖a‖_∞ ≤ C₀ n^(D/p) ‖a‖_p` of dimension `D` at `p`, there is
`C < ∞` with `‖a‖_r ≤ C n^(D(1/p - 1/r)) ‖a‖_p` for all `a ∈ S n`, `n ≥ 1`. Interpolation
between `L_p` and `L_∞` gives `‖a‖_r ≤ (C₀ n^(D/p))^(1 - p/r) ‖a‖_p`
(`MeasureTheory.eLpNorm_le_of_eLpNorm_top_le`), and `(D/p)(1 - p/r) = D(1/p - 1/r)`
(`nikolskiiExponent_eq_mul_one_sub_div`), so `C = C₀^(1 - p/r)`. -/
theorem HasNikolskiiAt.exists_eLpNorm_le_mul {p r : ℝ≥0∞} (h : S.HasNikolskiiAt D p)
    (hp0 : p ≠ 0) (hpr : p ≤ r) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      eLpNorm a r μ ≤ C * (n : ℝ≥0∞) ^ nikolskiiExponent D p r * eLpNorm a p μ := by
  obtain ⟨C, hC, hCa⟩ := h
  have h1 : 0 ≤ 1 - p.toReal / r.toReal := ENNReal.one_sub_toReal_div_nonneg hpr
  refine ⟨C ^ (1 - p.toReal / r.toReal), ENNReal.rpow_ne_top_of_nonneg h1 hC,
    fun n hn a ha => (eLpNorm_le_of_eLpNorm_top_le hp0 hpr (hCa n hn a ha)).trans_eq ?_⟩
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1, ← ENNReal.rpow_mul,
    ← nikolskiiExponent_eq_mul_one_sub_div D hp0 hpr]

/-- **The Nikolskii inequality for `0 < p ≤ r ≤ ∞`, in `[0, ∞]`** (Ditzian–Prymak 2016,
Theorem 2.1, (2.2) and (2.3)): under the Nikolskii property of dimension `D` there is `C < ∞` with
`‖a‖_r ≤ C n^(D(1/p - 1/r)) ‖a‖_p` for all `a ∈ S n`, `n ≥ 1`. The property gives the bound
`‖a‖_∞ ≤ C₀ n^(D/p) ‖a‖_p` at `p` (`FunctionScheme.HasNikolskii.hasNikolskiiAt`), and
interpolation between `L_p` and `L_∞` passes it to `L_r`
(`FunctionScheme.HasNikolskiiAt.exists_eLpNorm_le_mul`). -/
theorem HasNikolskii.exists_eLpNorm_le_of_le (h : S.HasNikolskii D) {p r : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpr : p ≤ r) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      eLpNorm a r μ ≤ C * (n : ℝ≥0∞) ^ nikolskiiExponent D p r * eLpNorm a p μ :=
  (h.hasNikolskiiAt hp0).exists_eLpNorm_le_mul hp0 hpr

/-- **The Nikolskii inequality on the blocks of a dyadic sequence**: if
`‖a‖_r ≤ C n^α ‖a‖_p` for all `a ∈ S_n`, `n ≥ 1`, and `b_k ∈ S_{2^k}` for every `k`, then
`‖b_{k+1} - b_k‖_r ≤ C 2^(2α) 2^(kα) ‖b_{k+1} - b_k‖_p`, since
`b_{k+1} - b_k ∈ S_{2^(k+2)}` (`ApproximationScheme.sub_mem_pow_add_two`) and
`(2^(k+2))^α = 2^(2α) 2^(kα)`. -/
theorem eLpNorm_sub_succ_le_of_nikolskii {p r : ℝ≥0∞} {C : ℝ≥0∞} {α : ℝ}
    (hC : ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n, eLpNorm a r μ ≤ C * (n : ℝ≥0∞) ^ α * eLpNorm a p μ)
    {b : ℕ → Lp ℂ ∞ μ} (hb : ∀ k, b k ∈ S (2 ^ k)) (k : ℕ) :
    eLpNorm (⇑(b (k + 1)) - ⇑(b k)) r μ ≤
      C * 2 ^ (2 * α) * ENNReal.dyadicWeight α k * eLpNorm (⇑(b (k + 1)) - ⇑(b k)) p μ := by
  have h := hC (2 ^ (k + 2)) Nat.one_le_two_pow _
    (ApproximationScheme.sub_mem_pow_add_two (hb (k + 1)) (hb k))
  have hae := Lp.coeFn_sub (b (k + 1)) (b k)
  rw [eLpNorm_congr_ae hae, eLpNorm_congr_ae hae, ENNReal.natCast_two_pow_rpow,
    ENNReal.dyadicWeight_add_nat] at h
  refine h.trans_eq ?_
  rw [show ENNReal.dyadicWeight α 2 = 2 ^ (2 * α) by simp [ENNReal.dyadicWeight]]
  ring

variable [IsFiniteMeasure μ]

/-- **The Nikolskii inequality** in real numbers: on a finite measure space, under the Nikolskii
property of dimension `D`, for `0 < p ≤ r ≤ ∞` there is `C ≥ 0` with
`‖a‖_r ≤ C n^(D(1/p - 1/r)) ‖a‖_p` for all `a ∈ S n`, `n ≥ 1`. This is
`FunctionScheme.HasNikolskii.exists_eLpNorm_le_of_le` in real numbers, since on a finite measure
space every class `a ∈ L_∞` has `‖a‖_p < ∞`. -/
theorem HasNikolskii.eLpNorm_le (h : S.HasNikolskii D) {p r : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpr : p ≤ r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      (eLpNorm a r μ).toReal ≤ C * (n : ℝ) ^ nikolskiiExponent D p r * (eLpNorm a p μ).toReal := by
  obtain ⟨C, hC, hCa⟩ := h.exists_eLpNorm_le_of_le hp0 hpr
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun n hn a ha => ?_⟩
  have hfin : C * (n : ℝ≥0∞) ^ nikolskiiExponent D p r * eLpNorm a p μ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC (ENNReal.rpow_ne_top_of_ne_zero
      (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn)) (ENNReal.natCast_ne_top n)))
      ((Lp.memLp a).mono_exponent le_top).eLpNorm_ne_top
  calc (eLpNorm a r μ).toReal
      ≤ (C * (n : ℝ≥0∞) ^ nikolskiiExponent D p r * eLpNorm a p μ).toReal :=
        ENNReal.toReal_mono hfin (hCa n hn a ha)
    _ = C.toReal * (n : ℝ) ^ nikolskiiExponent D p r * (eLpNorm a p μ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

/-- **The Nikolskii inequality as a lifting bound** for the inclusion `L_r ↪ L_p` of a finite
measure space, `1 ≤ p ≤ r ≤ ∞`: every approximant of the scheme in `L_p` is the inclusion of an
approximant in `L_r` whose norm is at most `C n^(D(1/p - 1/r))` times its `L_p` norm. -/
theorem HasNikolskii.liftBound (h : S.HasNikolskii D) {p r : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ r)] (hpr : p ≤ r) : ∃ C : ℝ, 0 ≤ C ∧
      ApproximationScheme.LiftBound (Lp.inclusionOfExponentLe (E := ℂ) (𝕜 := ℝ) μ hpr)
        (S.toLp p) (nikolskiiExponent D p r) C := by
  obtain ⟨C, hC, hCa⟩ := h.eLpNorm_le (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpr
  refine ⟨C, hC, fun n hn g hg => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hg
  refine ⟨Lp.topInclusion (𝕜 := ℝ) μ r a, Lp.inclusionOfExponentLeLinear_topInclusion hpr a, ?_⟩
  rw [Lp.norm_def, Lp.norm_def, Lp.eLpNorm_inclusionOfExponentLeLinear,
    Lp.eLpNorm_inclusionOfExponentLeLinear]
  exact hCa n hn a ha

end FunctionScheme
