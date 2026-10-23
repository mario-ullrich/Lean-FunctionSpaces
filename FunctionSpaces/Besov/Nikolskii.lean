/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Besov.Trivial
public import FunctionSpaces.Lp.Interpolation

/-!
# The Nikolskii inequality of a scheme

A scheme of functions `S` has the **Nikolskii property of dimension `D`** for the measure `μ`
if for every `1 ≤ p ≤ ∞` there is `C` with

`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p`   for all `a ∈ S n`, `n ≥ 1`

(`FunctionScheme.HasNikolskii`), a hypothesis on the scheme.  For trigonometric polynomials of
degree `< n` on `𝕋^d` it holds with `D = d` (`Torus.trigScheme_hasNikolskii`,
`Torus.hasNikolskii_fourierEigenbasis`); these torus instances are the ones proved in this
library.  The property is stated against the sup norm only; the general
**Nikolskii inequality**

`‖a‖_r ≤ C' n^(D (1/p - 1/r)) ‖a‖_p`,   `p ≤ r`

follows by interpolation, `‖a‖_r ≤ ‖a‖_∞^(1 - p/r) ‖a‖_p^(p/r)`
(`HasNikolskii.eLpNorm_le`).  The exponent `D (1/p - 1/r)` is `nikolskiiExponent D p r`.

In the language of `ApproximationSpaces.Lift` this is a lifting bound for the inclusion
`L_r ↪ L_p` and the scheme in `L_p` (`HasNikolskii.liftBound`): the approximant `a` in `L_p` is
the inclusion of the same function in `L_r`, of norm at most `C' n^(D(1/p - 1/r)) ‖a‖_p`.

The norms are written with `eLpNorm`, so that the hypothesis does not need an `L_p` space, and
hence no instance `Fact (1 ≤ p)`, for every `p` at once.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

/-- The **Nikolskii exponent** `D (1/p - 1/r)`.  With `1/∞ = 0` (in Lean `∞.toReal = 0` and
`0⁻¹ = 0`) it is `D/p` for `r = ∞`. -/
noncomputable def nikolskiiExponent (D : ℝ) (p r : ℝ≥0∞) : ℝ := D * (p.toReal⁻¹ - r.toReal⁻¹)

/-- `D(1/p - 1/r) ≥ 0` for `D ≥ 0` and `1 ≤ p ≤ r`. -/
theorem nikolskiiExponent_nonneg {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp : 1 ≤ p) (hpr : p ≤ r) :
    0 ≤ nikolskiiExponent D p r := by
  unfold nikolskiiExponent
  refine mul_nonneg hD (sub_nonneg.2 ?_)
  rcases eq_or_ne r ∞ with rfl | hr
  · simp
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  exact inv_anti₀ (ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp')
    (ENNReal.toReal_mono hr hpr)

/-- A natural number `m` above the Nikolskii exponent is at least `1`: for `D ≥ 0`,
`1 ≤ p ≤ r` and `m ∈ ℕ` with `m > D(1/p - 1/r)`, `m ≥ 1`, since the exponent is nonnegative
(`nikolskiiExponent_nonneg`). -/
theorem one_le_of_nikolskiiExponent_lt {D : ℝ} (hD : 0 ≤ D) {p r : ℝ≥0∞} (hp : 1 ≤ p)
    (hpr : p ≤ r) {m : ℕ} (hm : nikolskiiExponent D p r < m) : 1 ≤ m :=
  Nat.one_le_iff_ne_zero.2 (Nat.cast_pos.1 ((nikolskiiExponent_nonneg hD hp hpr).trans_lt hm)).ne'

/-- `α(D, p, ∞) = D/p`. -/
@[simp]
theorem nikolskiiExponent_top (D : ℝ) (p : ℝ≥0∞) : nikolskiiExponent D p ∞ = D * p.toReal⁻¹ := by
  simp [nikolskiiExponent]

/-- `α(D, p, p) = 0`. -/
@[simp]
theorem nikolskiiExponent_self (D : ℝ) (p : ℝ≥0∞) : nikolskiiExponent D p p = 0 := by
  simp [nikolskiiExponent]

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

/-- The **Nikolskii property of dimension `D`**: for every `1 ≤ p ≤ ∞`,
`‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all approximants `a ∈ S n`, `n ≥ 1`. A hypothesis on the scheme;
the torus has it (`Torus.trigScheme_hasNikolskii`). -/
structure HasNikolskii (S : FunctionScheme Ω) (μ : Measure Ω) (D : ℝ) : Prop where
  exists_const : ∀ p : ℝ≥0∞, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
    ‖a‖ ≤ C * (n : ℝ) ^ (D * p.toReal⁻¹) * (eLpNorm a p μ).toReal

variable {S : FunctionScheme Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {D : ℝ}

omit [IsFiniteMeasure μ] in
/-- The `L_∞` norm of a bounded continuous function is at most its sup norm. -/
theorem toReal_eLpNorm_top_le_norm (a : Ω →ᵇ ℂ) :
    (eLpNorm a ∞ μ).toReal ≤ ‖a‖ := by
  have : eLpNorm a ∞ μ ≤ ‖a‖ₑ := by
    rw [eLpNorm_exponent_top a.continuous.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x => by
      rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (a.norm_coe_le_norm x))
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono enorm_ne_top this

/-- **The Nikolskii inequality**: under the Nikolskii property of dimension `D ≥ 0`, for
`1 ≤ p ≤ r ≤ ∞` there is `C` with `‖a‖_r ≤ C n^(D(1/p - 1/r)) ‖a‖_p` for all `a ∈ S n`,
`n ≥ 1`. -/
theorem HasNikolskii.eLpNorm_le (h : S.HasNikolskii μ D) {p r : ℝ≥0∞} (hp : 1 ≤ p)
    (hpr : p ≤ r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n,
      (eLpNorm a r μ).toReal ≤ C * (n : ℝ) ^ nikolskiiExponent D p r * (eLpNorm a p μ).toReal := by
  obtain ⟨C, hC, hCa⟩ := h.exists_const p hp
  rcases eq_or_ne r ∞ with rfl | hr
  · refine ⟨C, hC, fun n hn a ha => ?_⟩
    rw [nikolskiiExponent_top]
    exact (toReal_eLpNorm_top_le_norm a).trans (hCa n hn a ha)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le (hp.trans hpr)).ne'
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr0 hr
  set θ := p.toReal / r.toReal
  have hθ1 : 0 ≤ 1 - θ := ENNReal.one_sub_toReal_div_nonneg hpr
  refine ⟨C ^ (1 - θ), Real.rpow_nonneg hC _, fun n hn a ha => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Np := (eLpNorm a p μ).toReal
  have hNp : 0 ≤ Np := ENNReal.toReal_nonneg
  have hint := toReal_eLpNorm_le_rpow_mul (μ := μ) a.continuous.aestronglyMeasurable
    (norm_nonneg a) (Filter.Eventually.of_forall a.norm_coe_le_norm) hp0 hpr hr
  calc (eLpNorm a r μ).toReal ≤ ‖a‖ ^ (1 - θ) * Np ^ θ := hint
    _ ≤ (C * (n : ℝ) ^ (D * p.toReal⁻¹) * Np) ^ (1 - θ) * Np ^ θ := by
        gcongr; exact hCa n hn a ha
    _ = C ^ (1 - θ) * (n : ℝ) ^ nikolskiiExponent D p r * (Np ^ (1 - θ) * Np ^ θ) := by
        rw [Real.mul_rpow (by positivity) hNp, Real.mul_rpow hC (by positivity),
          ← Real.rpow_mul hn0]
        have : D * p.toReal⁻¹ * (1 - θ) = nikolskiiExponent D p r := by
          simp only [nikolskiiExponent, θ]; field_simp
        rw [this]; ring
    _ = C ^ (1 - θ) * (n : ℝ) ^ nikolskiiExponent D p r * Np := by
        rw [← Real.rpow_add' hNp (by norm_num), sub_add_cancel, Real.rpow_one]

/-- **The Nikolskii inequality as a lifting bound** for the inclusion `L_r ↪ L_p`: every
approximant of the scheme in `L_p` is the inclusion of an approximant in `L_r` whose norm is at
most `C n^(D(1/p - 1/r))` times its `L_p` norm. -/
theorem HasNikolskii.liftBound (h : S.HasNikolskii μ D) {p r : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ r)] (hpr : p ≤ r) : ∃ C : ℝ, 0 ≤ C ∧
      ApproximationScheme.LiftBound (Lp.inclusionOfExponentLe (E := ℂ) (𝕜 := ℝ) μ hpr)
        (S.toLp μ p) (nikolskiiExponent D p r) C := by
  obtain ⟨C, hC, hCa⟩ := h.eLpNorm_le (Fact.out : 1 ≤ p) hpr
  refine ⟨C, hC, fun n hn g hg => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hg
  refine ⟨BoundedContinuousFunction.toLp (E := ℂ) r μ ℝ a,
    BoundedContinuousFunction.inclusionOfExponentLe_toLp hpr a, ?_⟩
  change ‖BoundedContinuousFunction.toLp (E := ℂ) r μ ℝ a‖ ≤
    C * (n : ℝ) ^ nikolskiiExponent D p r * ‖BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ a‖
  rw [BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm,
    BoundedContinuousFunction.norm_toLp_eq_toReal_eLpNorm]
  exact hCa n hn a ha

end FunctionScheme
