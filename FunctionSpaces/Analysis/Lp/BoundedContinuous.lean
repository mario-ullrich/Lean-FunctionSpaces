/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Lp.Inclusion
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Bounded continuous functions in `L_p`

Mathlib's `BoundedContinuousFunction.toLp p μ 𝕜` regards a bounded continuous function on a
finite measure space as an element of `L_p(μ)`.  This file adds:

* bounds by the sup norm, for every exponent: `‖a‖_{L_∞} ≤ sup |a|` for every measure, in
  `[0, ∞]` and between real numbers (`BoundedContinuousFunction.eLpNorm_top_le_enorm`,
  `BoundedContinuousFunction.toReal_eLpNorm_top_le_norm`), and the class `ι_{∞,p}(a)` of `a` in
  `L_p`, taken through `L_∞`, has `‖ι_{∞,p}(a)‖_p ≤ μ(Ω)^(1/p) sup |a|` for a finite measure and
  every `p`, also `p < 1` (`BoundedContinuousFunction.eLpNorm_topInclusion_toLp_le`);
* compatibility with the inclusion `L_r ↪ L_p`: including the `L_r` class of `a` gives its
  `L_p` class (`BoundedContinuousFunction.inclusionOfExponentLe_toLp`, and for the linear map
  `BoundedContinuousFunction.inclusionOfExponentLeLinear_toLp`);
* `‖toLp p μ 𝕜 a‖ = ‖a‖_{L_p}` written with `eLpNorm` (`norm_toLp_eq_toReal_eLpNorm`);
* for a measure giving positive mass to nonempty open sets, the sup norm equals the `L_∞`
  norm (`norm_toLp_top`), so `toLp ∞` is an isometry and its range is closed
  (`isClosed_range_toLp_top`).

The last point is what lets a limit of continuous functions in `L_∞` be continuous: it is the
step from "`f ∈ L_∞`" to "`f` has a continuous representative" in the embeddings into `C(Ω)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BoundedContinuousFunction

/-! ### Bounds by the sup norm -/

/-- **The `L_∞` norm of a bounded continuous function is at most its sup norm**:
`‖a‖_{L_∞(μ)} ≤ sup |a|` in `[0, ∞]` for every measure `μ`, since `|a(x)| ≤ ‖a‖` for every
`x`. -/
theorem eLpNorm_top_le_enorm {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup E]
    [SecondCountableTopologyEither α E] (a : α →ᵇ E) : eLpNorm a ∞ μ ≤ ‖a‖ₑ := by
  rw [eLpNorm_exponent_top a.continuous.aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_enorm_bound
    (Filter.Eventually.of_forall fun x => enorm_le_iff_norm_le.2 (a.norm_coe_le_norm x))

/-- **The real form of the sup-norm bound in `L_∞`**: `(‖a‖_{L_∞(μ)}).toReal ≤ sup |a|` for every
measure `μ` (`BoundedContinuousFunction.eLpNorm_top_le_enorm`, with `‖a‖ₑ < ∞`). -/
theorem toReal_eLpNorm_top_le_norm {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [TopologicalSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup E]
    [SecondCountableTopologyEither α E] (a : α →ᵇ E) :
    (eLpNorm a ∞ μ).toReal ≤ ‖a‖ := by
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono enorm_ne_top (eLpNorm_top_le_enorm a)

/-- **The `L_p` quasi-norm of a bounded continuous function**: for a finite measure `μ` on `Ω`,
every exponent `p` and every bounded continuous `b`, the class `ι_{∞,p}(b)` of `b` in `L_p(μ)`,
taken through `L_∞(μ)`, satisfies `‖ι_{∞,p}(b)‖_p ≤ μ(Ω)^(1/p) ‖b‖_∞`, since `b` is bounded by
its sup norm everywhere (`MeasureTheory.eLpNorm_le_of_ae_enorm_bound`). This is the `[0, ∞]`
form, along `L_∞ ↪ L_p`, of Mathlib's `BoundedContinuousFunction.Lp_nnnorm_le`, which holds for
every exponent. -/
theorem eLpNorm_topInclusion_toLp_le {α E 𝕜 : Type*}
    [MeasurableSpace α] {μ : Measure α} [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup E]
    [SecondCountableTopologyEither α E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [IsFiniteMeasure μ] (p : ℝ≥0∞) (b : α →ᵇ E) :
    eLpNorm (Lp.topInclusion (𝕜 := 𝕜) μ p
        (BoundedContinuousFunction.toLp (E := E) ∞ μ 𝕜 b)) p μ ≤
      μ Set.univ ^ p.toReal⁻¹ * ‖b‖ₑ := by
  rw [mul_comm, ← smul_eq_mul]
  refine eLpNorm_le_of_ae_enorm_bound (Lp.aestronglyMeasurable _) ?_
  filter_upwards [Lp.coeFn_topInclusion (𝕜 := 𝕜) (p := p)
      (BoundedContinuousFunction.toLp (E := E) ∞ μ 𝕜 b),
    BoundedContinuousFunction.coeFn_toLp (E := E) (p := ∞) (μ := μ) (𝕜 := 𝕜) b] with x h1 h2
  rw [h1, h2, enorm_le_iff_norm_le]
  exact b.norm_coe_le_norm x

variable {α E 𝕜 : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup E] [SecondCountableTopologyEither α E]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [IsFiniteMeasure μ] {p r : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- The `L_p` class of `a` is the inclusion of its `L_r` class. -/
@[simp]
theorem inclusionOfExponentLe_toLp (hpr : p ≤ r) (a : α →ᵇ E) :
    Lp.inclusionOfExponentLe (𝕜 := 𝕜) μ hpr (toLp (E := E) r μ 𝕜 a) = toLp (E := E) p μ 𝕜 a := by
  ext1
  filter_upwards [Lp.coeFn_inclusionOfExponentLe (𝕜 := 𝕜) hpr (toLp (E := E) r μ 𝕜 a),
    coeFn_toLp (E := E) r μ 𝕜 a, coeFn_toLp (E := E) p μ 𝕜 a] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The `L_p` class of `a` is the image of its `L_r` class under the linear inclusion
`MeasureTheory.Lp.inclusionOfExponentLeLinear`, which agrees with the bounded inclusion for
`1 ≤ p` (`MeasureTheory.Lp.inclusionOfExponentLe_apply`). -/
@[simp]
theorem inclusionOfExponentLeLinear_toLp (hpr : p ≤ r) (a : α →ᵇ E) :
    Lp.inclusionOfExponentLeLinear (𝕜 := 𝕜) μ hpr (toLp (E := E) r μ 𝕜 a) =
      toLp (E := E) p μ 𝕜 a :=
  inclusionOfExponentLe_toLp hpr a

/-- The `L_p` norm of the class of a bounded continuous function is its `eLpNorm`: the bounded
continuous analogue of Mathlib's `MeasureTheory.Lp.norm_toLp`, proved from
`MeasureTheory.Lp.norm_def` with the class `toLp p μ 𝕜 a` equal to `a` almost everywhere
(`BoundedContinuousFunction.coeFn_toLp`). -/
theorem norm_toLp_eq_toReal_eLpNorm (a : α →ᵇ E) :
    ‖toLp (E := E) p μ 𝕜 a‖ = (eLpNorm a p μ).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_toLp (E := E) p μ 𝕜 a)]

/-- For a measure that charges every nonempty open set, the `L_∞` norm of a bounded
continuous function is its sup norm. -/
theorem norm_toLp_top [μ.IsOpenPosMeasure] (a : α →ᵇ E) : ‖toLp (E := E) ∞ μ 𝕜 a‖ = ‖a‖ := by
  apply le_antisymm
  · have := Lp.norm_le_of_ae_bound (f := toLp (E := E) ∞ μ 𝕜 a) (norm_nonneg a)
      ((coeFn_toLp (E := E) ∞ μ 𝕜 a).mono fun x hx => by rw [hx]; exact a.norm_coe_le_norm x)
    simpa using this
  · -- the open set where `‖a x‖` exceeds the `L_∞` norm is null, hence empty
    set F := toLp (E := E) ∞ μ 𝕜 a
    have hae : ∀ᵐ x ∂μ, ‖a x‖ₑ ≤ ‖F‖ₑ := by
      filter_upwards [coeFn_toLp (E := E) ∞ μ 𝕜 a,
        ae_le_eLpNormEssSup (f := (F : α → E)) (μ := μ)] with x h1 h2
      rw [← h1, Lp.enorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable F)]
      exact h2
    have hU : IsOpen {x | ‖F‖ₑ < ‖a x‖ₑ} :=
      isOpen_lt continuous_const (continuous_enorm.comp a.continuous)
    have hU0 : μ {x | ‖F‖ₑ < ‖a x‖ₑ} = 0 := by
      simpa [not_le] using ae_iff.1 hae
    rw [hU.measure_eq_zero_iff μ] at hU0
    refine (norm_le (norm_nonneg _)).2 fun x => ?_
    have hx : ‖a x‖ₑ ≤ ‖F‖ₑ := by
      by_contra h
      exact (Set.eq_empty_iff_forall_notMem.1 hU0 x) (not_le.1 h)
    rw [← toReal_enorm, ← toReal_enorm]
    exact ENNReal.toReal_mono enorm_ne_top hx

/-- For a measure that charges every nonempty open set, `toLp ∞` is an isometry. -/
theorem isometry_toLp_top [μ.IsOpenPosMeasure] :
    Isometry (toLp (E := E) ∞ μ 𝕜 : (α →ᵇ E) → Lp E ∞ μ) :=
  (AddMonoidHomClass.isometry_iff_norm _).2 (norm_toLp_top (μ := μ) (𝕜 := 𝕜))

/-- For a measure that charges every nonempty open set, the bounded continuous functions form
a closed subspace of `L_∞`. -/
theorem isClosed_range_toLp_top [μ.IsOpenPosMeasure] [CompleteSpace E] :
    IsClosed (Set.range (toLp (E := E) ∞ μ 𝕜 : (α →ᵇ E) → Lp E ∞ μ)) :=
  ((isometry_toLp_top (μ := μ) (𝕜 := 𝕜)).isUniformInducing.isComplete_range).isClosed

end BoundedContinuousFunction
