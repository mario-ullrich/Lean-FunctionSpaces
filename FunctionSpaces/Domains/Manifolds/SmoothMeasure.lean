/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Smooth measures on manifolds

A measure `μ` on a manifold `M` modelled on `E` with corners `I` is **smooth**
(`Manifold.IsSmoothMeasure`) if in every chart `e` of the atlas the image of `μ` on the source of
`e` under the extended chart `κ = e.extend I` has a continuous density `ρ_e` with `0 < ρ_e < ∞`
with respect to the Lebesgue measure on the target `κ(e.source) ⊆ range I`:

`κ_* (μ|_{e.source}) = ρ_e · vol|_{κ(e.source)}`.

The Riemannian volume and the Lebesgue measure of a smooth domain are smooth measures.

**Integrals in a chart** (`Manifold.IsSmoothMeasure.lintegral_source_eq`):
`∫_{e.source} F dμ = ∫_{κ(e.source)} ρ_e(y) F(κ⁻¹ y) dy`. For functions that vanish outside a
compact subset `K` of the source, the density is bounded above and below on `κ(K)`, so the
integrals over `M` and over the chart are comparable
(`Manifold.IsSmoothMeasure.exists_lintegral_chart_le`): the `L_p` norms on `M` and in the chart
are equivalent for such functions.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M]

/-- A **smooth measure** on `M`: in every chart `e` of the atlas, the image of `μ` on the source of
`e` under the extended chart is a measure with a continuous density `ρ_e` with `0 < ρ_e < ∞` on the
target, with respect to the Lebesgue measure on the target. -/
class IsSmoothMeasure (μ : Measure M) : Prop where
  exists_density : ∀ e ∈ atlas H M, ∃ ρ : E → ℝ≥0∞, ContinuousOn ρ (e.extend I).target ∧
    (∀ y ∈ (e.extend I).target, 0 < ρ y ∧ ρ y < ∞) ∧
    Measure.map (e.extend I) (μ.restrict e.source) =
      (volume.restrict (e.extend I).target).withDensity ρ

omit [FiniteDimensional ℝ E] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M] in
/-- The target of an extended chart is measurable: it is the intersection of an open set with the
closed range of `I`. -/
theorem measurableSet_extend_target (e : OpenPartialHomeomorph M H) :
    MeasurableSet (e.extend I).target := by
  rw [e.extend_target]
  exact (I.continuous_symm.isOpen_preimage _ e.open_target).measurableSet.inter
    I.isClosed_range.measurableSet

namespace IsSmoothMeasure

variable {I} {μ : Measure M} [IsSmoothMeasure I μ]

omit [ChartedSpace H M] [IsSmoothMeasure I μ] in
/-- **Integrals in a chart**: for a chart `e` of the atlas with density `ρ` and a measurable
`F ≥ 0`, `∫_{e.source} F dμ = ∫_{κ(e.source)} ρ(y) F(κ⁻¹ y) dy`. -/
theorem lintegral_source_eq {e : OpenPartialHomeomorph M H} {ρ : E → ℝ≥0∞}
    (hρc : ContinuousOn ρ (e.extend I).target)
    (hmap : Measure.map (e.extend I) (μ.restrict e.source) =
      (volume.restrict (e.extend I).target).withDensity ρ)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in e.source, F x ∂μ =
      ∫⁻ y in (e.extend I).target, ρ y * F ((e.extend I).symm y) := by
  have hT := measurableSet_extend_target I e
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have hκ : AEMeasurable (e.extend I) (μ.restrict e.source) := by
    have h := (e.continuousOn_extend (I := I)).aemeasurable (μ := μ)
      (by rw [e.extend_source]; exact hsrc)
    rwa [e.extend_source] at h
  have hFs : AEMeasurable (fun y => F ((e.extend I).symm y))
      (volume.restrict (e.extend I).target) :=
    hF.comp_aemeasurable ((e.continuousOn_extend_symm (I := I)).aemeasurable hT)
  have hFs' : AEMeasurable (fun y => F ((e.extend I).symm y))
      (Measure.map (e.extend I) (μ.restrict e.source)) := by
    rw [hmap]
    exact hFs.mono_ac (withDensity_absolutelyContinuous _ _)
  calc ∫⁻ x in e.source, F x ∂μ
      = ∫⁻ x in e.source, F ((e.extend I).symm (e.extend I x)) ∂μ :=
        setLIntegral_congr_fun hsrc fun x hx => by rw [e.extend_left_inv hx]
    _ = ∫⁻ y, F ((e.extend I).symm y) ∂(Measure.map (e.extend I) (μ.restrict e.source)) :=
        (lintegral_map' hFs' hκ).symm
    _ = ∫⁻ y, F ((e.extend I).symm y) ∂((volume.restrict (e.extend I).target).withDensity ρ) := by
        rw [hmap]
    _ = ∫⁻ y in (e.extend I).target, ρ y * F ((e.extend I).symm y) :=
        lintegral_withDensity_eq_lintegral_mul₀ (hρc.aemeasurable hT) hFs

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The density is bounded above and below on compact sets**: on a compact `K'` inside the
target, `c ≤ ρ ≤ C` with `0 < c` and `C < ∞`, since `ρ` is continuous with values in `(0, ∞)`. -/
theorem exists_density_bounds {T : Set E} {ρ : E → ℝ≥0∞} (hρc : ContinuousOn ρ T)
    (hρ : ∀ y ∈ T, 0 < ρ y ∧ ρ y < ∞) {K' : Set E} (hK' : IsCompact K') (hK'T : K' ⊆ T) :
    ∃ c C : ℝ≥0∞, c ≠ 0 ∧ C ≠ ∞ ∧ ∀ y ∈ K', c ≤ ρ y ∧ ρ y ≤ C := by
  rcases K'.eq_empty_or_nonempty with h | hne
  · exact ⟨1, 1, one_ne_zero, ENNReal.one_ne_top, by simp [h]⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hK'.exists_isMinOn hne (hρc.mono hK'T)
  obtain ⟨y₁, hy₁, hmax⟩ := hK'.exists_isMaxOn hne (hρc.mono hK'T)
  exact ⟨ρ y₀, ρ y₁, (hρ y₀ (hK'T hy₀)).1.ne', (hρ y₁ (hK'T hy₁)).2.ne,
    fun y hy => ⟨hmin hy, hmax hy⟩⟩

variable (μ) in
/-- **Integrals on `M` and in a chart are comparable** for functions that vanish outside a compact
subset `K` of the source of a chart `e` of the atlas: there are `c > 0` and `C < ∞` with
`∫_{κ(e.source)} F ∘ κ⁻¹ ≤ c⁻¹ ∫_M F dμ` and `∫_M F dμ ≤ C ∫_{κ(e.source)} F ∘ κ⁻¹`. -/
theorem exists_lintegral_chart_le {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ c C : ℝ≥0∞, c ≠ 0 ∧ C ≠ ∞ ∧ ∀ F : M → ℝ≥0∞, Measurable F → (∀ x ∉ K, F x = 0) →
      (∫⁻ y in (e.extend I).target, F ((e.extend I).symm y) ≤ c⁻¹ * ∫⁻ x, F x ∂μ) ∧
      ∫⁻ x, F x ∂μ ≤ C * ∫⁻ y in (e.extend I).target, F ((e.extend I).symm y) := by
  obtain ⟨ρ, hρc, hρ, hmap⟩ := IsSmoothMeasure.exists_density (I := I) (μ := μ) e he
  set T := (e.extend I).target
  have hK' : IsCompact (e.extend I '' K) :=
    hK.image_of_continuousOn ((e.continuousOn_extend (I := I)).mono (by rwa [e.extend_source]))
  have hK'T : e.extend I '' K ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (e.extend I).map_source (by rw [e.extend_source]; exact hKs hx)
  obtain ⟨c, C, hc, hC, hbd⟩ := exists_density_bounds hρc hρ hK' hK'T
  refine ⟨c, C, hc, hC, fun F hF hFK => ⟨?_, ?_⟩⟩
  · -- where `F ∘ κ⁻¹ ≠ 0`, the density is at least `c`
    have hsupp : ∀ y ∈ T, F ((e.extend I).symm y) ≠ 0 → c ≤ ρ y := fun y hy hne => by
      have hx : (e.extend I).symm y ∈ K := by
        by_contra h
        exact hne (hFK _ h)
      have hyK : y ∈ e.extend I '' K := ⟨_, hx, (e.extend I).right_inv hy⟩
      exact (hbd y hyK).1
    calc ∫⁻ y in T, F ((e.extend I).symm y)
        ≤ ∫⁻ y in T, c⁻¹ * (ρ y * F ((e.extend I).symm y)) := by
          refine setLIntegral_mono' (measurableSet_extend_target I e) fun y hy => ?_
          by_cases hne : F ((e.extend I).symm y) = 0
          · rw [hne]
            exact zero_le
          · rw [← mul_assoc]
            calc F ((e.extend I).symm y) = 1 * F ((e.extend I).symm y) := (one_mul _).symm
              _ ≤ c⁻¹ * ρ y * F ((e.extend I).symm y) := by
                  gcongr
                  calc (1 : ℝ≥0∞) = c⁻¹ * c := (ENNReal.inv_mul_cancel hc (ne_top_of_le_ne_top
                        (hρ y hy).2.ne (hsupp y hy hne))).symm
                    _ ≤ c⁻¹ * ρ y := mul_le_mul' le_rfl (hsupp y hy hne)
      _ = c⁻¹ * ∫⁻ y in T, ρ y * F ((e.extend I).symm y) := lintegral_const_mul' _ _
          (ENNReal.inv_ne_top.2 hc)
      _ = c⁻¹ * ∫⁻ x in e.source, F x ∂μ := by rw [lintegral_source_eq hρc hmap hF]
      _ ≤ c⁻¹ * ∫⁻ x, F x ∂μ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
  · -- `F` lives in the source, where the density is at most `C`
    have hsupp : Function.support F ⊆ e.source := fun x hx => hKs (by
      by_contra h
      exact hx (hFK x h))
    calc ∫⁻ x, F x ∂μ = ∫⁻ x in e.source, F x ∂μ := (setLIntegral_eq_of_support_subset hsupp).symm
      _ = ∫⁻ y in T, ρ y * F ((e.extend I).symm y) := lintegral_source_eq hρc hmap hF
      _ ≤ ∫⁻ y in T, C * F ((e.extend I).symm y) := by
          refine setLIntegral_mono' (measurableSet_extend_target I e) fun y hy => ?_
          by_cases hne : F ((e.extend I).symm y) = 0
          · rw [hne, mul_zero, mul_zero]
          · have hx : (e.extend I).symm y ∈ K := by
              by_contra h
              exact hne (hFK _ h)
            exact mul_le_mul' (hbd y ⟨_, hx, (e.extend I).right_inv hy⟩).2 le_rfl
      _ = C * ∫⁻ y in T, F ((e.extend I).symm y) := lintegral_const_mul' _ _ hC

end IsSmoothMeasure

end Manifold
