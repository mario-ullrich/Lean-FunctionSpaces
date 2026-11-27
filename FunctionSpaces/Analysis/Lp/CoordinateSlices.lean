/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Lp.LintegralForm
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `L_p` norms on `ℝ^d` through coordinate slices

On `ℝ^d = Fin d → ℝ` with Lebesgue measure, the slice of `f` through `x` in coordinate `i` is the
function `t ↦ f(x₁, …, x_{i-1}, t, x_{i+1}, …, x_d)` of one variable, written
`fun t => f (Function.update x i t)` (on the cube this is `Cube.slice f x i`). Integrating out the
coordinate `i` writes integrals and `L_p` norms on `ℝ^(n+1)` as integrals over the other `n`
coordinates of one-dimensional integrals and `L_p` norms of the slices. For `y ∈ ℝ^n` let
`insertNth i t y ∈ ℝ^(n+1)` be the point with `t` in place `i` and the coordinates of `y` in the
other places (Mathlib's `Fin.insertNth`); the slice through `insertNth i s y` in coordinate `i`
is `t ↦ f(insertNth i t y)` for every `s` (Mathlib's `Fin.update_insertNth`).

* **Integrating out one coordinate.** `∫ G = ∫_{ℝ^n} ∫_ℝ G(insertNth i t y) dt dy` for every
  a.e. measurable `G ≥ 0` (`Rd.lintegral_eq_lintegral_slices`), since `x ↦ (x_i, (x_l)_{l ≠ i})`
  preserves Lebesgue measure (Mathlib's `volume_preserving_piFinSuccAbove`) and Tonelli's theorem
  applies on `ℝ × ℝ^n`.
* **`L_p` norms as mixed norms.** For measurable `f` and `0 < p < ∞`,
  `‖f‖_p = ‖y ↦ ‖t ↦ f(insertNth i t y)‖_{L_p(ℝ)}‖_{L_p(ℝ^n)}` (`Rd.eLpNorm_eq_eLpNorm_slices`).
* **Bounds through slices.** If `‖A(x with t in place i)‖_p ≤ a ‖B(…)‖_p + b ‖D(…)‖_p` for the
  slices through every point `x`, then `‖A‖_p ≤ a ‖B‖_p + b ‖D‖_p` for `1 ≤ p < ∞`
  (`Rd.eLpNorm_le_add_of_slice_le`), by Minkowski's inequality for the outer `L_p` norm; with one
  term on the right the same holds for `0 < p < ∞` (`Rd.eLpNorm_le_of_slice_le`).

On the unit cube with its probability measure the same tools are `Cube.lintegral_cubeVol_eq_slice`
and `Cube.eLpNorm_cubeVol_le_of_slice_le`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Rd

variable {n : ℕ}

/-- **Integrating out one coordinate**: on `ℝ^(n+1)` with Lebesgue measure, for every a.e.
measurable `G : ℝ^(n+1) → [0, ∞]` and every coordinate `i`,
`∫ G(x) dx = ∫_{ℝ^n} (∫_ℝ G(insertNth i t y) dt) dy`, where `insertNth i t y` has `t` in place `i`
and the coordinates of `y` in the other places. The map `x ↦ (x_i, (x_l)_{l ≠ i})` preserves
Lebesgue measure (Mathlib's `volume_preserving_piFinSuccAbove`), and Tonelli's theorem on
`ℝ × ℝ^n` (Mathlib's `MeasureTheory.lintegral_prod_symm`) integrates first over `t`. -/
theorem lintegral_eq_lintegral_slices (i : Fin (n + 1)) {G : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hG : AEMeasurable G) :
    ∫⁻ x, G x = ∫⁻ y : Fin n → ℝ, ∫⁻ t, G (i.insertNth t y) := by
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  rw [← he.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
    Measure.volume_eq_prod]
  exact lintegral_prod_symm (fun z => G ((MeasurableEquiv.piFinSuccAbove _ i).symm z))
    (hG.comp_quasiMeasurePreserving he.symm.quasiMeasurePreserving)

/-- **The point with an inserted coordinate is measurable in both arguments**: `(y, t) ↦
insertNth i t y` is measurable on `ℝ^n × ℝ`, as the inverse of the measurable equivalence
`x ↦ (x_i, (x_l)_{l ≠ i})` (Mathlib's `MeasurableEquiv.piFinSuccAbove`) after swapping the
factors. -/
theorem measurable_insertNth (i : Fin (n + 1)) :
    Measurable fun q : (Fin n → ℝ) × ℝ => (i.insertNth q.2 q.1 : Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurable.comp
    measurable_swap

/-- The `L_p` norms of the slices `t ↦ f(insertNth i t y)` of a measurable `f` depend measurably
on `y ∈ ℝ^n`, for `0 < p < ∞`: the `p`-th powers are the integrals over `t` of a measurable
function of `(y, t)` (`Rd.measurable_insertNth`, Mathlib's
`Measurable.lintegral_prod_right'`). -/
theorem measurable_eLpNorm_slices {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin (n + 1)) :
    Measurable fun y : Fin n → ℝ => eLpNorm (fun t : ℝ => f (i.insertNth t y)) p volume := by
  have hj := hf.comp (measurable_insertNth i)
  have h : Measurable fun y : Fin n → ℝ => ∫⁻ t, ‖f (i.insertNth t y)‖ₑ ^ p.toReal :=
    (hj.eNorm.pow_const p.toReal).lintegral_prod_right'
  have heq : (fun y : Fin n → ℝ => eLpNorm (fun t : ℝ => f (i.insertNth t y)) p volume) =
      fun y => (∫⁻ t, ‖f (i.insertNth t y)‖ₑ ^ p.toReal) ^ (1 / p.toReal) := funext fun y =>
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
      (hj.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [heq]
  exact h.pow_const _

/-- **`L_p` norms as mixed norms of slices**: for measurable `f` on `ℝ^(n+1)`, `0 < p < ∞` and
every coordinate `i`, `‖f‖_p = ‖y ↦ ‖t ↦ f(insertNth i t y)‖_{L_p(ℝ)}‖_{L_p(ℝ^n)}`. The `p`-th
powers agree by integrating out the coordinate `i` in `|f|^p`
(`Rd.lintegral_eq_lintegral_slices`). -/
theorem eLpNorm_eq_eLpNorm_slices {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin (n + 1)) :
    eLpNorm f p volume =
      eLpNorm (fun y : Fin n → ℝ => eLpNorm (fun t : ℝ => f (i.insertNth t y)) p volume) p
        volume := by
  refine (ENNReal.rpow_left_injective (ENNReal.toReal_pos hp0 hp).ne').eq_iff.1 ?_
  simp only [eLpNorm_rpow_eq hf.aestronglyMeasurable hp0 hp,
    eLpNorm_rpow_eq (measurable_eLpNorm_slices hf hp0 hp i).aestronglyMeasurable hp0 hp,
    eNorm_eq_self]
  rw [lintegral_eq_lintegral_slices i (hf.eNorm.pow_const _).aemeasurable]
  refine lintegral_congr fun y => ?_
  have hmt : Measurable fun t : ℝ => f (i.insertNth t y) :=
    (hf.comp (measurable_insertNth i)).comp (measurable_const.prodMk measurable_id)
  rw [eLpNorm_rpow_eq hmt.aestronglyMeasurable hp0 hp]

/-- **Bounds through slices, two terms**: let `1 ≤ p < ∞`, let `A, B, D` be measurable on `ℝ^d`,
`i` a coordinate and `a, b ∈ [0, ∞]`. If the slices through every point `x` in coordinate `i`
satisfy `‖A(x with t in place i)‖_p ≤ a ‖B(…)‖_p + b ‖D(…)‖_p` (norms in `t ∈ ℝ`), then
`‖A‖_p ≤ a ‖B‖_p + b ‖D‖_p`. The three norms are the `L_p` norms over the other coordinates of
the norms of the slices (`Rd.eLpNorm_eq_eLpNorm_slices`), and Minkowski's inequality for the
outer norm (Mathlib's `MeasureTheory.eLpNorm_add_le`) splits the right-hand side. -/
theorem eLpNorm_le_add_of_slice_le {d : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {A B D : (Fin d → ℝ) → ℂ} (hA : Measurable A) (hB : Measurable B) (hD : Measurable D)
    (i : Fin d) {a b : ℝ≥0∞}
    (h : ∀ x, eLpNorm (fun t => A (Function.update x i t)) p volume ≤
      a * eLpNorm (fun t => B (Function.update x i t)) p volume +
        b * eLpNorm (fun t => D (Function.update x i t)) p volume) :
    eLpNorm A p volume ≤ a * eLpNorm B p volume + b * eLpNorm D p volume := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := i.pos; omega⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  rw [eLpNorm_eq_eLpNorm_slices hA hp0 hp i, eLpNorm_eq_eLpNorm_slices hB hp0 hp i,
    eLpNorm_eq_eLpNorm_slices hD hp0 hp i,
    ← eLpNorm_const_mul_ennreal (measurable_eLpNorm_slices hB hp0 hp i).aestronglyMeasurable,
    ← eLpNorm_const_mul_ennreal (measurable_eLpNorm_slices hD hp0 hp i).aestronglyMeasurable]
  refine (eLpNorm_mono_eNorm (measurable_eLpNorm_slices hA hp0 hp i).aestronglyMeasurable
    fun y => ?_).trans (eLpNorm_add_le hp1)
  simpa only [eNorm_eq_self, Fin.update_insertNth, Pi.add_apply] using h (i.insertNth 0 y)

/-- **Bounds through slices, one term**: let `0 < p < ∞`, let `A, B` be measurable on `ℝ^d`, `i` a
coordinate and `a ∈ [0, ∞]`. If the slices through every point `x` in coordinate `i` satisfy
`‖A(x with t in place i)‖_p ≤ a ‖B(x with t in place i)‖_p` (norms in `t ∈ ℝ`), then
`‖A‖_p ≤ a ‖B‖_p`, since both norms are the `L_p` norms over the other coordinates of the norms
of the slices (`Rd.eLpNorm_eq_eLpNorm_slices`). -/
theorem eLpNorm_le_of_slice_le {d : ℕ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {A B : (Fin d → ℝ) → ℂ} (hA : Measurable A) (hB : Measurable B) (i : Fin d) {a : ℝ≥0∞}
    (h : ∀ x, eLpNorm (fun t => A (Function.update x i t)) p volume ≤
      a * eLpNorm (fun t => B (Function.update x i t)) p volume) :
    eLpNorm A p volume ≤ a * eLpNorm B p volume := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := i.pos; omega⟩
  rw [eLpNorm_eq_eLpNorm_slices hA hp0 hp i, eLpNorm_eq_eLpNorm_slices hB hp0 hp i,
    ← eLpNorm_const_mul_ennreal (measurable_eLpNorm_slices hB hp0 hp i).aestronglyMeasurable]
  refine eLpNorm_mono_eNorm (measurable_eLpNorm_slices hA hp0 hp i).aestronglyMeasurable
    fun y => ?_
  simpa only [eNorm_eq_self, Fin.update_insertNth] using h (i.insertNth 0 y)

end Rd
