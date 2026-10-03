/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.PiecewisePoly
public import FunctionSpaces.Interval.Smoothing
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The unit cube and slices

The unit cube `Q = [0, 1]^d` carries the product of Lebesgue measure on `[0, 1]`
(`Cube.cubeVol`), a probability measure on `Fin d → ℝ`. Functions on the cube are
functions `(Fin d → ℝ) → ℂ`, and `L_p(Q) = Lp ℂ p (cubeVol d)`.

The theory on the cube is built from the theory on the interval through **slices**: the slice of
`f` through `x` in coordinate `i` is the function `t ↦ f(x₁, …, x_{i-1}, t, x_{i+1}, …, x_d)`
(`Cube.slice`). Tonelli's theorem in one coordinate, in Mathlib's form of marginals
(`MeasureTheory.lmarginal_singleton`, `MeasureTheory.lintegral_eq_of_lmarginal_eq`), integrates
out the coordinate `i`: `∫_Q G = ∫_Q (∫_0^1 G(x with t in place i) dt) dx`
(`Cube.lintegral_cubeVol_eq_slice`); the inner integral does not depend on `x_i`. So `L_p` norms
on the cube, also over the regions `{x ∈ Q : x_i ∈ S}`, are `L_p` norms over `x` of the
`L_p[0, 1]` norms of the slices (`Cube.eLpNorm_rpow_region_eq_slice`), and functions equal
almost everywhere on the cube have almost everywhere equal slices for almost every `x`
(`Cube.ae_slice_ae_eq`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Cube

open Interval

/-- Lebesgue measure on `[0, 1]` is a probability measure. -/
instance isProbabilityMeasure_unitVol : IsProbabilityMeasure unitVol :=
  ⟨by simp [unitVol, Real.volume_Icc]⟩

/-- On `[a, b] ⊆ [0, 1]`, Lebesgue measure on `[0, 1]` restricted to `[a, b]` is Lebesgue measure
on `[a, b]`. -/
theorem unitVol_restrict_Icc_of_subset {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitVol.restrict (Icc a b) = volume.restrict (Icc a b) := by
  rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.2 (Icc_subset_Icc ha hb)]

/-- **Lebesgue measure on the unit cube** `[0, 1]^d`, the product of Lebesgue measure on
`[0, 1]`. -/
noncomputable abbrev cubeVol (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => unitVol

variable {d : ℕ}

/-- The **slice** of `f` through `x` in coordinate `i`: `t ↦ f(x₁, …, t, …, x_d)`, with `t` in
place `i`. -/
def slice (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) (i : Fin d) (t : ℝ) : ℂ :=
  f (Function.update x i t)

/-- The slices of a measurable function are measurable. -/
theorem measurable_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (x : Fin d → ℝ)
    (i : Fin d) : Measurable (slice f x i) :=
  hf.comp (measurable_update x)

/-- The slices of a measurable function are jointly measurable in the point and the variable. -/
theorem measurable_slice_uncurry {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (i : Fin d) :
    Measurable (fun q : (Fin d → ℝ) × ℝ => slice f q.1 i q.2) :=
  hf.comp measurable_update'

/-- A slice does not depend on the coordinate `i` of the point. -/
theorem slice_update (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    slice f (Function.update x i s) i = slice f x i := by
  funext t
  simp only [slice, Function.update_idem]

/-- **Integrating out one coordinate**: for measurable `G ≥ 0` on the cube and every
coordinate `i`, `∫_Q G = ∫_Q (∫_0^1 G(update x i t) dt) dx`; the inner integral does not depend
on `x_i`. -/
theorem lintegral_cubeVol_eq_slice {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) (i : Fin d) :
    ∫⁻ x, G x ∂cubeVol d = ∫⁻ x, (∫⁻ t, G (Function.update x i t) ∂unitVol) ∂cubeVol d := by
  set F : (Fin d → ℝ) → ℝ≥0∞ := fun x => ∫⁻ t, G (Function.update x i t) ∂unitVol
  have hmarg : (∫⋯∫⁻_{i}, G ∂fun _ => unitVol) = F := lmarginal_singleton G i
  have hF : Measurable F := hmarg ▸ hG.lmarginal (fun _ => unitVol)
  refine lintegral_eq_of_lmarginal_eq {i} hG hF ?_
  rw [hmarg, lmarginal_singleton]
  funext x
  simp only [F, Function.update_idem]
  rw [lintegral_const, measure_univ, mul_one]

/-- **Integrating out one coordinate over a region** `{x ∈ Q : x_i ∈ S}`:
`∫_{x_i ∈ S} G = ∫_Q (∫_S G(update x i t) dt) dx`. -/
theorem lintegral_region_eq_slice {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) (i : Fin d)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ∫⁻ x in {x | x i ∈ S}, G x ∂cubeVol d =
      ∫⁻ x, (∫⁻ t in S, G (Function.update x i t) ∂unitVol) ∂cubeVol d := by
  have hR : MeasurableSet {x : Fin d → ℝ | x i ∈ S} := measurable_pi_apply i hS
  rw [← lintegral_indicator hR, lintegral_cubeVol_eq_slice (hG.indicator hR) i]
  refine lintegral_congr fun x => ?_
  rw [← lintegral_indicator hS]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ S
  · rw [indicator_of_mem ht, indicator_of_mem (show Function.update x i t ∈ {x | x i ∈ S} by
      simpa using ht)]
  · rw [indicator_of_notMem ht, indicator_of_notMem (show Function.update x i t ∉ {x | x i ∈ S} by
      simpa using ht)]

/-- **`L_p` norms over a region through slices**: for measurable `f`, `0 < p < ∞`,
`‖f‖_{L_p({x_i ∈ S})}^p = ∫_Q ‖slice f x i‖_{L_p(S)}^p dx`. -/
theorem eLpNorm_rpow_region_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) {S : Set ℝ} (hS : MeasurableSet S) :
    eLpNorm f p ((cubeVol d).restrict {x | x i ∈ S}) ^ p.toReal =
      ∫⁻ x, eLpNorm (slice f x i) p (unitVol.restrict S) ^ p.toReal ∂cubeVol d := by
  rw [eLpNorm_rpow_eq hf.aestronglyMeasurable hp0 hp,
    lintegral_region_eq_slice (hf.enorm.pow_const _) i hS]
  refine lintegral_congr fun x => ?_
  rw [eLpNorm_rpow_eq (measurable_slice hf x i).aestronglyMeasurable hp0 hp]
  rfl

/-- **`L_p` norms on the cube through slices**: for measurable `f`, `0 < p < ∞`,
`‖f‖_{L_p(Q)}^p = ∫_Q ‖slice f x i‖_{L_p[0,1]}^p dx`. -/
theorem eLpNorm_rpow_cubeVol_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) :
    eLpNorm f p (cubeVol d) ^ p.toReal =
      ∫⁻ x, eLpNorm (slice f x i) p unitVol ^ p.toReal ∂cubeVol d := by
  have h := eLpNorm_rpow_region_eq_slice hf hp0 hp i MeasurableSet.univ
  simpa using h

/-- The `L_p` norms of the slices of a measurable function are measurable in the point. -/
theorem measurable_eLpNorm_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) (μ : Measure ℝ) [SFinite μ] :
    Measurable fun x => eLpNorm (slice f x i) p μ := by
  have h : Measurable fun x => ∫⁻ t, ‖slice f x i t‖ₑ ^ p.toReal ∂μ :=
    ((measurable_slice_uncurry hf i).enorm.pow_const p.toReal).lintegral_prod_right'
  have heq : (fun x => eLpNorm (slice f x i) p μ) =
      fun x => (∫⁻ t, ‖slice f x i t‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := funext fun x =>
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (measurable_slice hf x i).aestronglyMeasurable
  rw [heq]
  exact h.pow_const _

/-- **Minkowski's inequality in the form of bounds**: for `q ≥ 1`, `∫ φ^q ≤ a^q` and
`∫ ψ^q ≤ b^q` give `∫ (φ + ψ)^q ≤ (a + b)^q` (Mathlib's `ENNReal.lintegral_Lp_add_le`). It
combines bounds of norms of slices, which are functions of the point with values in `ℝ≥0∞`. -/
theorem lintegral_add_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ}
    (hq : 1 ≤ q) {φ ψ : α → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hψ : AEMeasurable ψ μ)
    {a b : ℝ≥0∞} (ha : ∫⁻ x, φ x ^ q ∂μ ≤ a ^ q) (hb : ∫⁻ x, ψ x ^ q ∂μ ≤ b ^ q) :
    ∫⁻ x, (φ x + ψ x) ^ q ∂μ ≤ (a + b) ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hroot : ∀ {c : ℝ≥0∞} {F : α → ℝ≥0∞}, ∫⁻ x, F x ^ q ∂μ ≤ c ^ q →
      (∫⁻ x, F x ^ q ∂μ) ^ (1 / q) ≤ c := fun {c F} h =>
    (ENNReal.rpow_le_rpow h (by positivity)).trans_eq (by
      rw [one_div, ENNReal.rpow_rpow_inv hq0.ne'])
  have h := ENNReal.lintegral_Lp_add_le hφ hψ hq
  simp only [Pi.add_apply] at h
  calc ∫⁻ x, (φ x + ψ x) ^ q ∂μ = ((∫⁻ x, (φ x + ψ x) ^ q ∂μ) ^ (1 / q)) ^ q := by
        rw [one_div, ENNReal.rpow_inv_rpow hq0.ne']
    _ ≤ (a + b) ^ q := ENNReal.rpow_le_rpow (h.trans (add_le_add (hroot ha) (hroot hb))) hq0.le

/-- Constant multiples in bounds of `∫ φ^q`: `∫ φ^q ≤ a^q` gives `∫ (c φ)^q ≤ (c a)^q`. -/
theorem lintegral_const_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ}
    (hq : 0 ≤ q) {c : ℝ≥0∞} (hc : c ≠ ∞) {φ : α → ℝ≥0∞} {a : ℝ≥0∞}
    (ha : ∫⁻ x, φ x ^ q ∂μ ≤ a ^ q) : ∫⁻ x, (c * φ x) ^ q ∂μ ≤ (c * a) ^ q := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq hc)]
  exact mul_le_mul' le_rfl ha

/-- **Slices of almost equal functions**: if `f = g` almost everywhere on the cube, then for
almost every `x` the slices of `f` and `g` through `x` in coordinate `i` agree almost
everywhere on `[0, 1]`. -/
theorem ae_slice_ae_eq {f g : (Fin d → ℝ) → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[cubeVol d] g) (i : Fin d) :
    ∀ᵐ x ∂cubeVol d, slice f x i =ᵐ[unitVol] slice g x i := by
  have hset : MeasurableSet {x : Fin d → ℝ | f x ≠ g x} :=
    (measurableSet_eq_fun hf hg).compl
  have h0 : ∫⁻ x, {x | f x ≠ g x}.indicator 1 x ∂cubeVol d = 0 := by
    rw [lintegral_indicator_one hset]
    exact ae_iff.1 hfg
  rw [lintegral_cubeVol_eq_slice ((measurable_one.indicator hset)) i,
    lintegral_eq_zero_iff (by
      have : Measurable ((∫⋯∫⁻_{i}, {x | f x ≠ g x}.indicator 1 ∂fun _ => unitVol)) :=
        (measurable_one.indicator hset).lmarginal (fun _ => unitVol)
      rwa [lmarginal_singleton] at this)] at h0
  filter_upwards [h0] with x hx
  have hx' : ∫⁻ t, {t | slice f x i t ≠ slice g x i t}.indicator 1 t ∂unitVol = 0 := hx
  rw [lintegral_indicator_one (s := {t | slice f x i t ≠ slice g x i t})
    (measurableSet_eq_fun (measurable_slice hf x i) (measurable_slice hg x i)).compl] at hx'
  exact ae_iff.2 hx'

end Cube
