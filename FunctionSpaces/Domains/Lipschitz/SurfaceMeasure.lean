/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Traces.BoundaryTraceSpace
public import FunctionSpaces.Domains.Lipschitz.LipschitzGraphArea

/-!
# The surface measure of a bounded Lipschitz domain

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner
product space `V`, `dim V = n`, such as `ℝ^d`, with the boundary balls `B_j` and the Lipschitz
graphs `γ_j(x') = x' + φ_j(x') e_j` over the hyperplanes `H_j`.

* **The surface measure** `σ` (`Rd.BoundedLipschitzDomain.surfaceMeasure`) is Mathlib's
  `(n-1)`-dimensional Euclidean Hausdorff measure `μHE[n-1]` restricted to `Γ`, defined without
  charts. By the area formula for Lipschitz graphs, in each chart it is the measure with density
  `√(1 + ‖∇φ_j‖²)` on `H_j` (`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support`,
  `Rd.BoundedLipschitzDomain.integral_surfaceMeasure_of_support`), so two charts give the same
  integrals (`Rd.BoundedLipschitzDomain.lintegral_chart_eq`), the density between `1` and
  `√(1 + M_j²)` compares the integrals in a chart with those over `Γ`
  (`Rd.BoundedLipschitzDomain.lintegral_chart_le`, `Rd.BoundedLipschitzDomain.lintegral_le_chart`),
  and a resolution of unity splits every integral over `Γ` into chart integrals, since
  `g = ∑_j ψ_j g` on `Γ` (`Rd.BoundedLipschitzDomain.ae_eq_sum_mul`,
  `Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure`,
  `Rd.BoundedLipschitzDomain.integral_surfaceMeasure`). It is finite, its null sets are those of
  the charts (`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_iff_aeBoundary`), and `Γ` is a null
  set of the volume (`Rd.BoundedLipschitzDomain.volume_frontier`).
* **The traces in `L_2(Γ)`**: the boundary trace of the trace theorem lies in `L_p(σ)`
  (`Rd.BoundedLipschitzDomain.memLp_boundaryTrace`); for `p = 2` and `1/2 < s < 3/2` it gives
  bounded operators `T^s_Γ : H^s(V) → L_2(Γ)` (`Rd.BoundedLipschitzDomain.ambientTraceL2`) with
  values in `B^{s-1/2}_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.memBoundaryBesov_ambientTraceL2`), the
  injective trace of the trace space of `H^s(Ω)` in `L_2(Γ)` (`Rd.BoundedLipschitzDomain.traceL2`)
  and `γ^s_{L_2} : H^s(Ω) → L_2(Γ)` (`Rd.BoundedLipschitzDomain.boundaryTraceL2`), which is
  `T^s_Γ` on `H^s(Ω)` (`Rd.BoundedLipschitzDomain.boundaryTraceL2_eq_ambientTraceL2`) and whose
  kernel is the trace kernel (`Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`), so `T^s_Γ`
  vanishes on the trace kernel (`Rd.BoundedLipschitzDomain.ambientTraceL2_eq_zero_of_mem_traceKer`);
  `B^{s-1/2}_{2,2}(Γ) ⊆ L_2(Γ)` (`Rd.BoundedLipschitzDomain.memLp_of_memBoundaryBesov`). For
  `s = 1` the statements with the `L_2` function `Rd.toL2` are
  `Rd.BoundedLipschitzDomain.ambientTraceL2_one_apply_ae`,
  `Rd.BoundedLipschitzDomain.traceL2_one_apply_ae` and
  `Rd.BoundedLipschitzDomain.boundaryTraceL2_one_apply_ae`. The statements about `U ∈ H^s(V)`
  alone (`Rd.BoundedLipschitzDomain.memLp_boundaryTrace_sobolevToL2`,
  `Rd.BoundedLipschitzDomain.exists_eLpNorm_boundaryTrace_sobolevToL2_le`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_add`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_smul`, `T^s_Γ`) hold for `1/2 < s < 2`,
  the range of `Rd.modNorm_sobolevToL2_lt_top`; they take the hypotheses `1/2 < s < 3/2` of the
  family, for one calling convention.
* **The outward unit normal** `ν(y) = ∑_j ψ_j(y) ν_j(P_j y)`
  (`Rd.BoundedLipschitzDomain.outwardNormal`) is pasted from the chart normals `ν_j` with the fixed
  resolution of unity `ψ = Rd.BoundedLipschitzDomain.boundaryPartition`, which is nonnegative; it is
  measurable with `‖ν‖ ≤ 1`.
-/

@[expose] public section

open MeasureTheory Module Metric Filter Topology Set
open scoped ENNReal NNReal BesselPotentialSpace Manifold
open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : BoundedLipschitzDomain V)

/-! ### The boundary in a ball is the graph -/

/-- **In a boundary ball the boundary is the graph**: `Γ ∩ B_j = γ_j(H_j) ∩ B_j`
(`Rd.BoundedLipschitzDomain.mem_frontier_iff`). -/
theorem frontier_inter_ball_eq (j : Fin Ω.N) :
    frontier Ω.carrier ∩ ball (Ω.center j) (Ω.radius j) =
      range (Ω.graph j).graphMap ∩ ball (Ω.center j) (Ω.radius j) := by
  ext y
  refine ⟨fun ⟨hy, hb⟩ => ⟨⟨_, (Ω.mem_frontier_iff j hb).1 hy⟩, hb⟩, ?_⟩
  rintro ⟨⟨x', rfl⟩, hb⟩
  exact ⟨Ω.graphMap_mem_frontier j hb, hb⟩

variable [MeasurableSpace V] [BorelSpace V]

/-! ### The surface measure -/

/-- **The surface measure** `σ` of the boundary `Γ` of a bounded Lipschitz domain in `V`,
`dim V = n`: the `(n-1)`-dimensional Hausdorff measure restricted to `Γ`, normalised as Mathlib's
`μHE[n-1]`, so that it is the volume on hyperplanes. In each chart it is the measure with density
`√(1 + ‖∇φ_j‖²)` on the hyperplane
(`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support`). -/
noncomputable def surfaceMeasure : Measure V :=
  (μHE[finrank ℝ V - 1] : Measure V).restrict (frontier Ω.carrier)

/-- The surface measure is carried by the boundary: almost every point lies on `Γ`. -/
theorem ae_mem_frontier : ∀ᵐ y ∂Ω.surfaceMeasure, y ∈ frontier Ω.carrier :=
  ae_restrict_mem isClosed_frontier.measurableSet

/-- The complement of the boundary is a null set of the surface measure. -/
theorem surfaceMeasure_compl_frontier : Ω.surfaceMeasure (frontier Ω.carrier)ᶜ = 0 :=
  ae_iff.1 Ω.ae_mem_frontier

/-- **The surface measure in a boundary ball**: on `B_j` the surface measure is `μHE[n-1]` on the
graph `γ_j(H_j)` (`Rd.BoundedLipschitzDomain.frontier_inter_ball_eq`). -/
theorem surfaceMeasure_restrict_ball (j : Fin Ω.N) :
    Ω.surfaceMeasure.restrict (ball (Ω.center j) (Ω.radius j)) =
      ((μHE[finrank ℝ V - 1] : Measure V).restrict (range (Ω.graph j).graphMap)).restrict
        (ball (Ω.center j) (Ω.radius j)) := by
  rw [surfaceMeasure, Measure.restrict_restrict measurableSet_ball,
    Measure.restrict_restrict measurableSet_ball, inter_comm, Ω.frontier_inter_ball_eq,
    inter_comm]

variable [FiniteDimensional ℝ V]

/-- **Integrals over a boundary ball in the chart**: for every `F : V → [0, ∞]` vanishing outside
`B_j`, `∫_Γ F dσ = ∫_{H_j} F(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'`, by the area formula for the graph
of `φ_j` (`Rd.LipschitzGraph.lintegral_graphMap`). -/
theorem lintegral_surfaceMeasure_of_support (j : Fin Ω.N) (F : V → ℝ≥0∞)
    (hF : ∀ y, F y ≠ 0 → y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫⁻ y, F y ∂Ω.surfaceMeasure =
      ∫⁻ x', F ((Ω.graph j).graphMap x') * ENNReal.ofReal ((Ω.graph j).gramDensity x') := by
  have hs : Function.support F ⊆ ball (Ω.center j) (Ω.radius j) := fun y hy => hF y hy
  rw [← setLIntegral_eq_of_support_subset hs, surfaceMeasure_restrict_ball,
    setLIntegral_eq_of_support_subset hs, LipschitzGraph.lintegral_graphMap]

/-- **Integrals in the chart are at most those over `Γ`**: for every `F : V → [0, ∞]` vanishing
outside `B_j`, `∫_{H_j} F(γ_j x') dx' ≤ ∫_Γ F dσ`, since the density `√(1 + ‖∇φ_j‖²)` is at least
`1` (`Rd.LipschitzGraph.one_le_ofReal_gramDensity`). -/
theorem lintegral_chart_le (j : Fin Ω.N) (F : V → ℝ≥0∞)
    (hF : ∀ y, F y ≠ 0 → y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫⁻ x', F ((Ω.graph j).graphMap x') ≤ ∫⁻ y, F y ∂Ω.surfaceMeasure := by
  rw [Ω.lintegral_surfaceMeasure_of_support j F hF]
  exact lintegral_mono fun x' => le_mul_of_one_le_right' ((Ω.graph j).one_le_ofReal_gramDensity x')

/-- **Integrals over `Γ` by the chart**: for every `F : V → [0, ∞]` vanishing outside `B_j`,
`∫_Γ F dσ ≤ √(1 + M_j²) ∫_{H_j} F(γ_j x') dx'` (`Rd.LipschitzGraph.gramDensity_le`). -/
theorem lintegral_le_chart (j : Fin Ω.N) (F : V → ℝ≥0∞)
    (hF : ∀ y, F y ≠ 0 → y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫⁻ y, F y ∂Ω.surfaceMeasure ≤
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * ∫⁻ x', F ((Ω.graph j).graphMap x') := by
  rw [Ω.lintegral_surfaceMeasure_of_support j F hF,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x' => ?_
  rw [mul_comm]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal ((Ω.graph j).gramDensity_le x')) le_rfl

/-- **Complex integrals over a boundary ball in the chart**: for every `F : V → ℂ` vanishing outside
`B_j`, `∫_Γ F dσ = ∫_{H_j} F(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'`, by the area formula for the graph of
`φ_j` (`Rd.LipschitzGraph.integral_graphMap`). -/
theorem integral_surfaceMeasure_of_support (j : Fin Ω.N) (F : V → ℂ)
    (hF : ∀ y, F y ≠ 0 → y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫ y, F y ∂Ω.surfaceMeasure =
      ∫ x', F ((Ω.graph j).graphMap x') * ((Ω.graph j).gramDensity x' : ℂ) := by
  have h : ∀ y, y ∉ ball (Ω.center j) (Ω.radius j) → F y = 0 := fun y hy =>
    by_contra fun h => hy (hF y h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h, surfaceMeasure_restrict_ball,
    setIntegral_eq_integral_of_forall_compl_eq_zero h, LipschitzGraph.integral_graphMap]

/-- **Two charts give the same integral**: for every `F : V → [0, ∞]` vanishing outside
`B_j ∩ B_k`, `∫_{H_j} F(γ_j x') √(1 + ‖∇φ_j‖²) dx' = ∫_{H_k} F(γ_k y') √(1 + ‖∇φ_k‖²) dy'`; both
are `∫_Γ F dσ`. -/
theorem lintegral_chart_eq (j k : Fin Ω.N) (F : V → ℝ≥0∞)
    (hF : ∀ y, F y ≠ 0 →
      y ∈ ball (Ω.center j) (Ω.radius j) ∩ ball (Ω.center k) (Ω.radius k)) :
    ∫⁻ x', F ((Ω.graph j).graphMap x') * ENNReal.ofReal ((Ω.graph j).gramDensity x') =
      ∫⁻ y', F ((Ω.graph k).graphMap y') * ENNReal.ofReal ((Ω.graph k).gramDensity y') := by
  rw [← Ω.lintegral_surfaceMeasure_of_support j F fun y hy => (hF y hy).1,
    Ω.lintegral_surfaceMeasure_of_support k F fun y hy => (hF y hy).2]

omit [FiniteDimensional ℝ V] in
/-- **The surface measure as a sum over the charts**: for every resolution of unity `ψ` with
`ψ_j ≥ 0` on `Γ`, `σ = ∑_j ψ_j σ`, the sum of the measures with the densities `ψ_j`, since
`∑_j ψ_j = 1` on `Γ` and `σ` is carried by `Γ`. -/
theorem surfaceMeasure_eq_sum_withDensity (ψ : Ω.BoundaryPartition)
    (hψ : ∀ j, ∀ y ∈ frontier Ω.carrier, 0 ≤ ψ.toFun j y) :
    Ω.surfaceMeasure =
      Measure.sum fun j => Ω.surfaceMeasure.withDensity fun y => ENNReal.ofReal (ψ.toFun j y) := by
  rw [← withDensity_tsum fun j => (ψ.contDiff j).continuous.measurable.ennreal_ofReal]
  conv_lhs => rw [← withDensity_one (μ := Ω.surfaceMeasure)]
  refine withDensity_congr_ae (Ω.ae_mem_frontier.mono fun y hy => ?_)
  rw [ENNReal.tsum_apply, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun j _ => hψ j y hy,
    ψ.sum_eq_one y hy, ENNReal.ofReal_one, Pi.one_apply]

/-- **The surface measure in the charts**: for every resolution of unity `ψ` on the boundary with
`ψ_j ≥ 0` on `Γ` and every `F : V → [0, ∞]`,
`∫_Γ F dσ = ∑_j ∫_{H_j} ψ_j(γ_j x') F(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'`. By
`Rd.BoundedLipschitzDomain.surfaceMeasure_eq_sum_withDensity`, `∫_Γ F dσ = ∑_j ∫_Γ ψ_j F dσ`, and
`ψ_j F` vanishes outside `B_j` (`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support`).
It holds for every `F`, measurable or not. -/
theorem lintegral_surfaceMeasure (ψ : Ω.BoundaryPartition)
    (hψ : ∀ j, ∀ y ∈ frontier Ω.carrier, 0 ≤ ψ.toFun j y) (F : V → ℝ≥0∞) :
    ∫⁻ y, F y ∂Ω.surfaceMeasure = ∑ j, ∫⁻ x', ENNReal.ofReal (ψ.toFun j ((Ω.graph j).graphMap x')) *
      F ((Ω.graph j).graphMap x') * ENNReal.ofReal ((Ω.graph j).gramDensity x') := by
  conv_lhs => rw [Ω.surfaceMeasure_eq_sum_withDensity ψ hψ]
  rw [lintegral_sum_measure, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (ψ.contDiff j).continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine Ω.lintegral_surfaceMeasure_of_support j _ fun y hy => ψ.mem_ball_of_ne_zero fun h => hy ?_
  rw [Pi.mul_apply, h, ENNReal.ofReal_zero, zero_mul]

omit [FiniteDimensional ℝ V] in
/-- On `Γ`, `g = ∑_j ψ_j g` almost everywhere for the surface measure, since `∑_j ψ_j = 1` on `Γ`
and `σ` is carried by `Γ`. -/
theorem ae_eq_sum_mul (ψ : Ω.BoundaryPartition) (g : V → ℂ) :
    g =ᵐ[Ω.surfaceMeasure] fun y => ∑ j, ψ.toComplex j y * g y :=
  Ω.ae_mem_frontier.mono fun y hy => by
    dsimp only
    rw [← Finset.sum_mul, ψ.sum_toComplex_eq_one hy, one_mul]

/-- **The surface measure in the charts, for complex integrals**: for every resolution of unity `ψ`
on the boundary, of any sign, and every `σ`-integrable `f : V → ℂ`,
`∫_Γ f dσ = ∑_j ∫_{H_j} ψ_j(γ_j x') f(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'`. On `Γ`, `f = ∑_j ψ_j f`;
each `ψ_j f` is integrable since `ψ_j` is bounded, and vanishes outside `B_j`
(`Rd.BoundedLipschitzDomain.integral_surfaceMeasure_of_support`). -/
theorem integral_surfaceMeasure (ψ : Ω.BoundaryPartition) {f : V → ℂ}
    (hf : Integrable f Ω.surfaceMeasure) :
    ∫ y, f y ∂Ω.surfaceMeasure = ∑ j, ∫ x', ψ.toComplex j ((Ω.graph j).graphMap x') *
      f ((Ω.graph j).graphMap x') * ((Ω.graph j).gramDensity x' : ℂ) := by
  have hsum : ∫ y, f y ∂Ω.surfaceMeasure =
      ∫ y, ∑ j, ψ.toComplex j y * f y ∂Ω.surfaceMeasure :=
    integral_congr_ae (Ω.ae_eq_sum_mul ψ f)
  rw [hsum, integral_finsetSum _ fun j _ => hf.bdd_mul
    (ψ.contDiff_toComplex j).continuous.aestronglyMeasurable
    (ae_of_all _ (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Ω.integral_surfaceMeasure_of_support j (fun y => ψ.toComplex j y * f y) fun y hy =>
    ψ.mem_ball_of_ne_zero fun h => hy (by simp [BoundaryPartition.toComplex, h])

/-- **Integrals over the boundary are at most the sum of the chart integrals**: for every
`F : V → [0, ∞]`, `∫_Γ F dσ ≤ ∑_j ∫_{H_j} (1_{B_j} F)(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'`, since the
balls `B_j` cover `Γ`. It holds for every `F`, measurable or not. -/
theorem lintegral_surfaceMeasure_le_sum (F : V → ℝ≥0∞) :
    ∫⁻ y, F y ∂Ω.surfaceMeasure ≤ ∑ j, ∫⁻ x', (ball (Ω.center j) (Ω.radius j)).indicator F
      ((Ω.graph j).graphMap x') * ENNReal.ofReal ((Ω.graph j).gramDensity x') := by
  have hcov : Ω.surfaceMeasure.restrict (⋃ j, ball (Ω.center j) (Ω.radius j)) =
      Ω.surfaceMeasure :=
    Measure.restrict_eq_self_of_ae_mem (Ω.ae_mem_frontier.mono fun _ hy => Ω.frontier_subset hy)
  calc ∫⁻ y, F y ∂Ω.surfaceMeasure
      = ∫⁻ y in ⋃ j, ball (Ω.center j) (Ω.radius j), F y ∂Ω.surfaceMeasure := by rw [hcov]
    _ ≤ ∑' j, ∫⁻ y in ball (Ω.center j) (Ω.radius j), F y ∂Ω.surfaceMeasure :=
        lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ y, (ball (Ω.center j) (Ω.radius j)).indicator F y ∂Ω.surfaceMeasure := by
        rw [tsum_fintype]
        exact Finset.sum_congr rfl fun j _ => (lintegral_indicator measurableSet_ball F).symm
    _ = _ := Finset.sum_congr rfl fun j _ =>
        Ω.lintegral_surfaceMeasure_of_support j _ fun _ hy => mem_of_indicator_ne_zero hy

/-- **The surface measure is finite**: `σ(Γ) ≤ ∑_j √(1 + M_j²) |γ_j⁻¹(B_j)|`, and the sets
`γ_j⁻¹(B_j) ⊆ H_j` are bounded since the graph maps are antilipschitz. -/
instance isFiniteMeasure_surfaceMeasure : IsFiniteMeasure Ω.surfaceMeasure := by
  refine ⟨(lintegral_one.symm.trans_le (Ω.lintegral_surfaceMeasure_le_sum 1)).trans_lt
    (ENNReal.sum_lt_top.2 fun j _ => ?_)⟩
  set A := (Ω.graph j).graphMap ⁻¹' ball (Ω.center j) (Ω.radius j)
  have hA : MeasurableSet A :=
    (Ω.graph j).measurableEmbedding_graphMap.measurable measurableSet_ball
  calc ∫⁻ x', (ball (Ω.center j) (Ω.radius j)).indicator 1 ((Ω.graph j).graphMap x') *
        ENNReal.ofReal ((Ω.graph j).gramDensity x')
      ≤ ∫⁻ x', A.indicator (fun _ => ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2)) x' := by
        refine lintegral_mono fun x' => ?_
        by_cases hx : x' ∈ A
        · rw [indicator_of_mem hx, indicator_of_mem (show (Ω.graph j).graphMap x' ∈ _ from hx),
            Pi.one_apply, one_mul]
          exact ENNReal.ofReal_le_ofReal ((Ω.graph j).gramDensity_le x')
        · rw [indicator_of_notMem (show (Ω.graph j).graphMap x' ∉ _ from hx), zero_mul]
          exact zero_le
    _ = ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * volume A := lintegral_indicator_const hA _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Ω.graph j).antilipschitzWith_graphMap.isBounded_preimage isBounded_ball).measure_lt_top

/-- **Almost everywhere on a boundary ball, in the chart**: a property holds for `σ`-almost every
`y ∈ B_j` iff it holds at `γ_j(x')` for almost every `x' ∈ H_j` with `γ_j(x') ∈ B_j`. The image of
the measure with the density `√(1 + ‖∇φ_j‖²) ≥ 1` under `γ_j` is `μHE[n-1]` on the graph
(`Rd.LipschitzGraph.map_graphMap_withDensity`), and this density has the null sets of the volume. -/
theorem ae_surfaceMeasure_ball_iff (j : Fin Ω.N) {P : V → Prop} :
    (∀ᵐ y ∂Ω.surfaceMeasure, y ∈ ball (Ω.center j) (Ω.radius j) → P y) ↔
      ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
        (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j) → P ((Ω.graph j).graphMap x') := by
  rw [← ae_restrict_iff' measurableSet_ball, surfaceMeasure_restrict_ball,
    ae_restrict_iff' measurableSet_ball, ← LipschitzGraph.map_graphMap_withDensity,
    (Ω.graph j).measurableEmbedding_graphMap.ae_map_iff]
  have hac := withDensity_absolutelyContinuous' (μ := (volume : Measure (Ω.graph j).hyperplane))
    (Ω.graph j).measurable_gramDensity.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x' => (ENNReal.ofReal_pos.2 ((Ω.graph j).gramDensity_pos x')).ne')
  exact ⟨fun h => hac.ae_le h, fun h => (withDensity_absolutelyContinuous _ _).ae_le h⟩

/-- **`σ`-almost everywhere statements in a chart**: if `P` holds `σ`-almost everywhere, then
`P(γ_j x')` holds for almost every `x' ∈ H_j` with `γ_j(x') ∈ B_j`
(`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_ball_iff`). -/
theorem ae_graphMap_of_ae_surfaceMeasure (j : Fin Ω.N) {P : V → Prop}
    (h : ∀ᵐ y ∂Ω.surfaceMeasure, P y) :
    ∀ᵐ x' ∂(volume : Measure (Ω.graph j).hyperplane),
      (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j) → P ((Ω.graph j).graphMap x') :=
  (Ω.ae_surfaceMeasure_ball_iff j).1 (h.mono fun _ hy _ => hy)

/-- **The null sets of the surface measure are those of the charts**: a property holds
`σ`-almost everywhere iff it holds almost everywhere on the boundary in the sense of the charts
(`Rd.BoundedLipschitzDomain.aeBoundary`), since the balls `B_j` cover `Γ`. -/
theorem ae_surfaceMeasure_iff_aeBoundary {P : V → Prop} :
    (∀ᵐ y ∂Ω.surfaceMeasure, P y) ↔ ∀ᶠ y in Ω.aeBoundary, P y := by
  rw [eventually_aeBoundary_iff]
  simp_rw [← ae_surfaceMeasure_ball_iff]
  refine ⟨fun h j => h.mono fun y hy _ => hy, fun h => ?_⟩
  filter_upwards [ae_all_iff.2 h, Ω.ae_mem_frontier] with y hy hΓ
  obtain ⟨j, hj⟩ := mem_iUnion.1 (Ω.frontier_subset hΓ)
  exact hy j hj

/-- **The boundary of a bounded Lipschitz domain is a null set**: `|Γ| = 0`. The set `Γ` has
finite `μHE[n-1]`-measure, hence `μHE[n]`-measure zero (Mathlib's
`MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top`), and `μHE[n]` is the volume. -/
theorem volume_frontier : volume (frontier Ω.carrier) = 0 := by
  rcases (frontier Ω.carrier).eq_empty_or_nonempty with h | ⟨y, hy⟩
  · rw [h, measure_empty]
  · obtain ⟨j, -⟩ := mem_iUnion.1 (Ω.frontier_subset hy)
    have : Nontrivial V := nontrivial_of_ne _ 0 (Ω.graph j).e_ne_zero
    have hfin : (μHE[finrank ℝ V - 1] : Measure V) (frontier Ω.carrier) ≠ ∞ := by
      have h := measure_ne_top Ω.surfaceMeasure (frontier Ω.carrier)
      rwa [surfaceMeasure, Measure.restrict_apply_self] at h
    have hlt : finrank ℝ V - 1 < finrank ℝ V := Nat.sub_lt finrank_pos one_pos
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact ((Measure.euclideanHausdorffMeasure_zero_or_top hlt _).resolve_right hfin)

/-! ### The boundary trace in `L_p(Γ)` -/

section BoundaryLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The boundary trace is measurable**: `Tr_Γ F = ∑_k ψ_k (Tr_k F ∘ P_k)` is a finite sum of
products of continuous functions with measurable representatives composed with the continuous
projections `P_k`. -/
theorem stronglyMeasurable_boundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) (L : ℕ)
    (F : Lp ℂ p (volume : Measure V)) : StronglyMeasurable (Ω.boundaryTrace ψ hp L F) :=
  Finset.stronglyMeasurable_fun_sum _ fun k _ =>
    (ψ.contDiff_toComplex k).continuous.stronglyMeasurable.mul
      ((Lp.stronglyMeasurable _).comp_measurable (Ω.graph k).graphProj.continuous.measurable)

/-- **The `L_p(Γ)` bound of the boundary trace**: under the hypotheses of the trace theorem,
`∫_Γ |Tr_Γ F|^p dσ ≤ ∑_j √(1 + M_j²) ‖Tr_j F‖_{L_p(H_j)}^p`, with the Lipschitz constants `M_j`
of the charts. In the chart `j`, `Tr_Γ F ∘ γ_j = Tr_j F` almost everywhere on `γ_j⁻¹(B_j)`
(`Rd.BoundedLipschitzDomain.boundaryTrace_graphMap`) and the Gram density is at most
`√(1 + M_j²)` (`Rd.LipschitzGraph.gramDensity_le`). -/
theorem lintegral_enorm_boundaryTrace_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ}
    (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) :
    ∫⁻ y, ‖Ω.boundaryTrace ψ hp L F y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure ≤
      ∑ j, ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) *
        ∫⁻ x', ‖(Ω.graph j).graphTrace hp L F x'‖ₑ ^ p.toReal := by
  refine (Ω.lintegral_surfaceMeasure_le_sum _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ((Ω.boundaryTrace_graphMap ψ hp hL hs hsL hq hF j).mono
    fun x' hx => ?_)
  by_cases hb : (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j)
  · rw [indicator_of_mem hb, hx hb, mul_comm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal ((Ω.graph j).gramDensity_le x')) le_rfl
  · rw [indicator_of_notMem hb, zero_mul]
    exact zero_le

/-- **The boundary trace lies in `L_p(Γ)`**: under the hypotheses of the trace theorem,
`Tr_Γ F ∈ L_p(σ)` (`Rd.BoundedLipschitzDomain.lintegral_enorm_boundaryTrace_le`, and
`Tr_j F ∈ L_p(H_j)`). -/
theorem memLp_boundaryTrace (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ}
    (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) :
    MemLp (Ω.boundaryTrace ψ hp L F) p Ω.surfaceMeasure := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine memLp_iff.2 ((eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 hp
    (Ω.stronglyMeasurable_boundaryTrace ψ hp L F).aestronglyMeasurable).2
    ((Ω.lintegral_enorm_boundaryTrace_le ψ hp hL hs hsL hq hF).trans_lt
      (ENNReal.sum_lt_top.2 fun j _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)))
  exact lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp (Lp.memLp _).eLpNorm_lt_top

end BoundaryLp

/-! ### `L_2(Γ)` and the traces of `H^s`, `1/2 < s < 3/2` -/

/-- **The space `L_2(Γ)`** of square integrable functions on the boundary with respect to the
surface measure. -/
noncomputable abbrev BoundaryL2 := Lp ℂ 2 Ω.surfaceMeasure

/-- **The boundary trace of `H^s(V)` lies in `L_2(Γ)`**, `1/2 < s < 3/2`: for every resolution
of unity `ψ` and `U ∈ H^s(V)`, `Tr_Γ ι_s U ∈ L_2(σ)`
(`Rd.BoundedLipschitzDomain.memLp_boundaryTrace` at smoothness `s - 1/2`, `p = q = 2`,
`L = 2`). -/
theorem memLp_boundaryTrace_sobolevToL2 (ψ : Ω.BoundaryPartition) (s : ℝ) (U : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    MemLp (Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)) 2
      Ω.surfaceMeasure :=
  Ω.memLp_boundaryTrace ψ two_ne_top one_le_two (sub_pos.2 hs) (by norm_num; linarith)
    one_le_two (modNorm_sobolevToL2_lt_top hs (by linarith) U)

/-- **The `L_2(Γ)` bound of the trace of `H^s(V)`**, `1/2 < s < 3/2`:
`‖Tr_Γ ι_s U‖_{L_2(Γ)} ≤ C ‖U‖` for every resolution of unity and every `U ∈ H^s(V)`, with
`C = (∑_j √(1 + M_j²) K_j²)^(1/2)` for the constants `K_j` of the traces of the graph domains
`Ω_j` (`Rd.LipschitzGraph.exists_enorm_graphTrace_sobolevToL2_le`,
`Rd.BoundedLipschitzDomain.lintegral_enorm_boundaryTrace_le`). -/
theorem exists_eLpNorm_boundaryTrace_sobolevToL2_le (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ψ : Ω.BoundaryPartition) (U : H^{s}(V)),
      eLpNorm (Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)) 2
        Ω.surfaceMeasure ≤ C * ‖U‖ₑ := by
  have hs0 : 0 ≤ s := (one_half_pos.trans hs).le
  choose K hK hle using fun j => (Ω.graph j).exists_enorm_graphTrace_sobolevToL2_le hs (by linarith)
  refine ⟨(∑ j, ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * K j ^ (2 : ℝ)) ^ (1 / 2 : ℝ),
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hK j))), fun ψ U => ?_⟩
  have hj : ∀ j, ∫⁻ x', ‖(Ω.graph j).graphTrace two_ne_top 2 (sobolevToL2 hs0 U) x'‖ₑ ^
      (2 : ℝ≥0∞).toReal ≤ K j ^ (2 : ℝ) * ‖U‖ₑ ^ (2 : ℝ) := fun j => by
    rw [ENNReal.toReal_ofNat, lintegral_rpow_eNorm_eq_rpow_eLpNorm' two_pos,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    refine ENNReal.rpow_le_rpow ((le_of_eq ?_).trans (hle j U)) (by norm_num)
    rw [Lp.eNorm_def, eLpNorm_eq_eLpNorm' two_ne_zero two_ne_top (Lp.aestronglyMeasurable _),
      ENNReal.toReal_ofNat]
  have hsum := (Ω.lintegral_enorm_boundaryTrace_le ψ two_ne_top one_le_two (sub_pos.2 hs)
    (by norm_num; linarith) one_le_two (modNorm_sobolevToL2_lt_top hs (by linarith) U)).trans
    (Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hj j))
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero two_ne_top
    (Ω.stronglyMeasurable_boundaryTrace ψ two_ne_top 2 _).aestronglyMeasurable]
  calc (∫⁻ y, ‖Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 hs0 U) y‖ₑ ^ (2 : ℝ≥0∞).toReal
        ∂Ω.surfaceMeasure) ^ (1 / (2 : ℝ≥0∞).toReal)
      ≤ (∑ j, ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * (K j ^ (2 : ℝ) * ‖U‖ₑ ^ (2 : ℝ))) ^
          (1 / 2 : ℝ) := by
        rw [ENNReal.toReal_ofNat]
        exact ENNReal.rpow_le_rpow hsum (by norm_num)
    _ = _ := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul]
        norm_num

/-- `Tr_Γ ι_s (U + W) = Tr_Γ ι_s U + Tr_Γ ι_s W` almost everywhere on `Γ`, for every resolution of
unity and `1/2 < s < 3/2` (`Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_sub`). -/
theorem boundaryTrace_sobolevToL2_add (ψ : Ω.BoundaryPartition) (s : ℝ) (U W : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le (U + W))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U) +
        Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le W) := by
  have h := Ω.boundaryTrace_sobolevToL2_sub ψ s (U + W) W hs hs'
  rw [add_sub_cancel_right] at h
  filter_upwards [h] with y hy
  rw [Pi.add_apply, hy, Pi.sub_apply, sub_add_cancel]

/-- `Tr_Γ ι_s (c U) = c Tr_Γ ι_s U` almost everywhere on `Γ`, for every resolution of unity and
`1/2 < s < 3/2`, since `ι_s (c U) = c ι_s U` and the boundary trace is homogeneous
(`Rd.BoundedLipschitzDomain.boundaryTrace_smul`, `Rd.modNorm_sobolevToL2_lt_top`). -/
theorem boundaryTrace_sobolevToL2_smul (ψ : Ω.BoundaryPartition) (s : ℝ) (c : ℂ) (U : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le (c • U))
      =ᶠ[Ω.aeBoundary] c • Ω.boundaryTrace ψ two_ne_top 2
        (sobolevToL2 (one_half_pos.trans hs).le U) := by
  rw [map_smul]
  exact Ω.boundaryTrace_smul ψ two_ne_top (sub_pos.2 hs) (by norm_num; linarith) one_le_two c
    (modNorm_sobolevToL2_lt_top hs (by linarith) U)

/-- **The trace of `H^s(V)` in `L_2(Γ)` as a linear map**, `1/2 < s < 3/2`: `U ↦ Tr_Γ ι_s U`,
with the canonical resolution of unity. -/
noncomputable def ambientTraceLinear (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : H^{s}(V) →ₗ[ℂ] Ω.BoundaryL2 where
  toFun U := (Ω.memLp_boundaryTrace_sobolevToL2 Ω.boundaryPartition s U hs hs').toLp _
  map_add' U W := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    exact Ω.ae_surfaceMeasure_iff_aeBoundary.2 (Ω.boundaryTrace_sobolevToL2_add _ s U W hs hs')
  map_smul' c U := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    exact Ω.ae_surfaceMeasure_iff_aeBoundary.2 (Ω.boundaryTrace_sobolevToL2_smul _ s c U hs hs')

/-- **The trace `T^s_Γ` of `H^s(V)` on `Γ`**, `1/2 < s < 3/2`, as a bounded operator
`H^s(V) → L_2(Γ)`, `U ↦ Tr_Γ ι_s U`; `T_Γ = T^1_Γ`
(`Rd.BoundedLipschitzDomain.exists_eLpNorm_boundaryTrace_sobolevToL2_le`). -/
noncomputable def ambientTraceL2 (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : H^{s}(V) →L[ℂ] Ω.BoundaryL2 :=
  (Ω.ambientTraceLinear s hs hs').mkContinuousOfExistsBound (by
    obtain ⟨C, hC, hle⟩ := Ω.exists_eLpNorm_boundaryTrace_sobolevToL2_le s hs hs'
    refine ⟨C.toReal, fun U => ?_⟩
    change ‖(Ω.memLp_boundaryTrace_sobolevToL2 Ω.boundaryPartition s U hs hs').toLp _‖ ≤ _
    rw [Lp.norm_toLp, ← toReal_eNorm U, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC eNorm_ne_top) (hle _ U))

/-- The trace of `U ∈ H^s(V)` in `L_2(Γ)` is the boundary trace `Tr_Γ ι_s U` almost everywhere on
`Γ`, for every resolution of unity (`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`). -/
theorem ambientTraceL2_apply_ae (ψ : Ω.BoundaryPartition) (s : ℝ) (U : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.ambientTraceL2 s hs hs' U : V → ℂ) =ᵐ[Ω.surfaceMeasure]
      Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U) :=
  (MemLp.coeFn_toLp (Ω.memLp_boundaryTrace_sobolevToL2 Ω.boundaryPartition s U hs hs')).trans
    (Ω.ae_surfaceMeasure_iff_aeBoundary.2
    (Ω.boundaryTrace_eventuallyEq Ω.boundaryPartition ψ two_ne_top one_le_two (sub_pos.2 hs)
      (by norm_num; linarith) one_le_two (modNorm_sobolevToL2_lt_top hs (by linarith) U)))

/-- The trace of `U ∈ H^1(V)` in `L_2(Γ)` is the boundary trace `Tr_Γ ι U` of its `L_2` function
`Rd.toL2 U`, the case `s = 1` of `Rd.BoundedLipschitzDomain.ambientTraceL2_apply_ae`
(`Rd.sobolevToL2_one`). -/
theorem ambientTraceL2_one_apply_ae (ψ : Ω.BoundaryPartition) (U : H^{1}(V)) :
    ((Ω.ambientTraceL2 1) U : V → ℂ) =ᵐ[Ω.surfaceMeasure]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) := by
  have h := Ω.ambientTraceL2_apply_ae ψ 1 U
  rwa [sobolevToL2_one] at h

/-- **The trace of `H^s(V)` in `L_2(Γ)` lies in `B^{s-1/2}_{2,2}(Γ)`**, `1/2 < s < 3/2`: for every
resolution of unity `ψ` and `U ∈ H^s(V)`, `T^s_Γ U` is the boundary trace `Tr_Γ ι_s U` almost
everywhere on `Γ` (`Rd.BoundedLipschitzDomain.ambientTraceL2_apply_ae`), which lies in
`B^{s-1/2}_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.memBoundaryBesov_sobolevToL2`). -/
theorem memBoundaryBesov_ambientTraceL2 (ψ : Ω.BoundaryPartition) (s : ℝ) (U : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 (Ω.ambientTraceL2 s hs hs' U) :=
  (Ω.memBoundaryBesov_sobolevToL2 ψ s U hs hs').congr (EventuallyEq.symm
    (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Ω.ambientTraceL2_apply_ae ψ s U hs hs')))

/-- **The trace of the trace space in `L_2(Γ)`**, `1/2 < s < 3/2`: an element `t` of the trace
space of `H^s(Ω)` goes to the boundary trace of its extension `E_s t ∈ H^s(Ω)`. It is injective
(`Rd.BoundedLipschitzDomain.traceL2_injective`). -/
noncomputable def traceL2 (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : Ω.TraceSpace s hs hs' →L[ℂ] Ω.BoundaryL2 :=
  Ω.ambientTraceL2 s hs hs' ∘L (vanishOn s Ω.toOpens)ᗮ.subtypeL ∘L Ω.domainExtend s hs hs'

/-- `traceL2 s t = Tr_Γ ι_s (E_s t)` almost everywhere on `Γ`, for every resolution of unity. -/
theorem traceL2_apply_ae (ψ : Ω.BoundaryPartition) {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (t : Ω.TraceSpace s hs hs') :
    (Ω.traceL2 s hs hs' t : V → ℂ) =ᵐ[Ω.surfaceMeasure] Ω.boundaryTrace ψ two_ne_top 2
      (sobolevToL2 (one_half_pos.trans hs).le
        ((Ω.domainExtend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V))) :=
  Ω.ambientTraceL2_apply_ae ψ s _ hs hs'

/-- `traceL2 1 t = Tr_Γ ι (E_1 t)` almost everywhere on `Γ` with the `L_2` function `Rd.toL2`, the
case `s = 1` of `Rd.BoundedLipschitzDomain.traceL2_apply_ae` (`Rd.sobolevToL2_one`). -/
theorem traceL2_one_apply_ae (ψ : Ω.BoundaryPartition) (t : Ω.TraceSpace 1) :
    ((Ω.traceL2 1) t : V → ℂ) =ᵐ[Ω.surfaceMeasure] Ω.boundaryTrace ψ two_ne_top 2
      (toL2 (((Ω.domainExtend 1) t : Ω.SobolevOne) : H^{1}(V))) := by
  have h := Ω.traceL2_apply_ae ψ t
  rwa [sobolevToL2_one] at h

/-- **The trace of the trace space in `L_2(Γ)` is injective**: elements of the trace space with
the same boundary trace almost everywhere on `Γ` are equal
(`Rd.BoundedLipschitzDomain.boundaryTrace_domainExtend_eventuallyEq_iff`), and `σ`-null sets are the
null sets of the charts (`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_iff_aeBoundary`). -/
theorem traceL2_injective (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : Function.Injective (Ω.traceL2 s hs hs') := by
  intro t t' h
  have h1 := Ω.traceL2_apply_ae Ω.boundaryPartition t
  rw [h] at h1
  exact (Ω.boundaryTrace_domainExtend_eventuallyEq_iff Ω.boundaryPartition t t').1
    (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (h1.symm.trans (Ω.traceL2_apply_ae _ t')))

/-- **The trace `γ^s_{L_2} : H^s(Ω) → L_2(Γ)`**, `1/2 < s < 3/2`: the trace `γ_s` onto the trace
space followed by the trace of the trace space in `L_2(Γ)`; `γ_{L_2} = γ^1_{L_2}`. Its kernel is
the trace kernel (`Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`). -/
noncomputable def boundaryTraceL2 (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : RestrictionSpace s Ω.toOpens →L[ℂ] Ω.BoundaryL2 :=
  Ω.traceL2 s hs hs' ∘L Ω.domainTrace s hs hs'

/-- **`γ^s_{L_2} u` is the boundary trace of `u`**: `γ^s_{L_2} u = Tr_Γ ι_s u` almost everywhere
on `Γ`, for every resolution of unity
(`Rd.BoundedLipschitzDomain.boundaryTrace_domainExtend_domainTrace`). -/
theorem boundaryTraceL2_apply_ae (ψ : Ω.BoundaryPartition) (s : ℝ)
    (u : RestrictionSpace s Ω.toOpens) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.boundaryTraceL2 s hs hs' u : V → ℂ) =ᵐ[Ω.surfaceMeasure]
      Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V))) :=
  (Ω.traceL2_apply_ae ψ (Ω.domainTrace s hs hs' u)).trans
    (Ω.ae_surfaceMeasure_iff_aeBoundary.2 (Ω.boundaryTrace_domainExtend_domainTrace ψ s u hs hs'))

/-- **`γ_{L_2} u` is the boundary trace of `u ∈ H^1(Ω)`** with the `L_2` function `Rd.toL2`, the
case `s = 1` of `Rd.BoundedLipschitzDomain.boundaryTraceL2_apply_ae` (`Rd.sobolevToL2_one`). -/
theorem boundaryTraceL2_one_apply_ae (ψ : Ω.BoundaryPartition) (u : Ω.SobolevOne) :
    ((Ω.boundaryTraceL2 1) u : V → ℂ) =ᵐ[Ω.surfaceMeasure]
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u : H^{1}(V))) := by
  have h := Ω.boundaryTraceL2_apply_ae ψ 1 u
  rwa [sobolevToL2_one] at h

/-- **`γ^s_{L_2} u` is the trace of `u` read in `H^s(V)`**: `γ^s_{L_2} u = T^s_Γ u`, that is
`boundaryTraceL2 s u = ambientTraceL2 s u`, for every `u ∈ H^s(Ω)`; both are the boundary trace
`Tr_Γ ι_s u` almost everywhere on `Γ` (`Rd.BoundedLipschitzDomain.boundaryTraceL2_apply_ae`,
`Rd.BoundedLipschitzDomain.ambientTraceL2_apply_ae`). -/
theorem boundaryTraceL2_eq_ambientTraceL2 (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.boundaryTraceL2 s hs hs' u = Ω.ambientTraceL2 s hs hs' (u : H^{s}(V)) :=
  Lp.ext ((Ω.boundaryTraceL2_apply_ae Ω.boundaryPartition s u hs hs').trans
    (Ω.ambientTraceL2_apply_ae Ω.boundaryPartition s _ hs hs').symm)

/-- **The kernel of `γ^s_{L_2} : H^s(Ω) → L_2(Γ)` is the trace kernel**: `γ^s_{L_2} u = 0` in
`L_2(Γ)` iff the boundary trace of `u` vanishes almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff`). -/
theorem ker_boundaryTraceL2 (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.boundaryTraceL2 s hs hs').ker = Ω.traceKer s hs hs' := by
  ext u
  rw [LinearMap.mem_ker, Lp.eq_zero_iff_ae_eq_zero,
    Ω.mem_traceKer_iff Ω.boundaryPartition s u hs hs']
  have h := Ω.boundaryTraceL2_apply_ae Ω.boundaryPartition s u hs hs'
  exact ⟨fun h0 => Ω.ae_surfaceMeasure_iff_aeBoundary.1 (h.symm.trans h0),
    fun h0 => h.trans (Ω.ae_surfaceMeasure_iff_aeBoundary.2 h0)⟩

/-- **Elements of the trace kernel have zero trace in `L_2(Γ)`**, `1/2 < s < 3/2`: for
`u ∈ ker γ_s`, read in `H^s(V)`, `T^s_Γ u = 0`
(`Rd.BoundedLipschitzDomain.boundaryTraceL2_eq_ambientTraceL2`,
`Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`). -/
theorem ambientTraceL2_eq_zero_of_mem_traceKer (s : ℝ) (hs : 1 / 2 < s) (hs' : s < 3 / 2)
    {u : RestrictionSpace s Ω.toOpens} (hu : u ∈ Ω.traceKer s hs hs') :
    Ω.ambientTraceL2 s hs hs' (u : H^{s}(V)) = 0 := by
  have h : u ∈ (Ω.boundaryTraceL2 s hs hs').ker := by
    rw [Ω.ker_boundaryTraceL2 s hs hs']
    exact hu
  rw [← Ω.boundaryTraceL2_eq_ambientTraceL2 s u hs hs']
  exact LinearMap.mem_ker.1 h

/-- **The functions of `B^{s-1/2}_{2,2}(Γ)` are traces in `L_2(Γ)`**, `1/2 < s < 3/2`: for every
resolution of unity `ψ` and `g ∈ B^{s-1/2}_{2,2}(Γ)` there is `t` in the trace space of `H^s(Ω)`
with `traceL2 s t = g` `σ`-almost everywhere
(`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`). -/
theorem exists_traceL2_ae_eq (ψ : Ω.BoundaryPartition) (s : ℝ) {g : V → ℂ}
    (hg : Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 g) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    ∃ t : Ω.TraceSpace s hs hs', (Ω.traceL2 s hs hs' t : V → ℂ) =ᵐ[Ω.surfaceMeasure] g := by
  obtain ⟨t, ht⟩ := Ω.exists_traceSpace_of_memBoundaryBesov ψ s hg hs hs'
  exact ⟨t, (Ω.traceL2_apply_ae ψ t).trans (Ω.ae_surfaceMeasure_iff_aeBoundary.2 ht)⟩

/-- **`B^{s-1/2}_{2,2}(Γ) ⊆ L_2(Γ)`**, `1/2 < s < 3/2`: every `g ∈ B^{s-1/2}_{2,2}(Γ)` is square
integrable with respect to the surface measure
(`Rd.BoundedLipschitzDomain.exists_traceL2_ae_eq`). -/
theorem memLp_of_memBoundaryBesov (ψ : Ω.BoundaryPartition) (s : ℝ) {g : V → ℂ}
    (hg : Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 g) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : MemLp g 2 Ω.surfaceMeasure := by
  obtain ⟨t, ht⟩ := Ω.exists_traceL2_ae_eq ψ s hg hs hs'
  exact (Lp.memLp _).ae_eq ht

/-! ### The unit normal -/

/-- **The outward unit normal field** `ν(y) = ∑_j ψ_j(y) ν_j(P_j y)` of `Ω`, pasted from the
outward unit normals `ν_j` of the charts (`Rd.LipschitzGraph.normalAt`) with the canonical
resolution of unity `ψ = Rd.BoundedLipschitzDomain.boundaryPartition`, which is nonnegative. It
is defined on all of `V`, measurable and of norm at most `1`; for `y ∈ Γ` it is a convex
combination of the chart normals `ν_j(P_j y)` with `ψ_j(y) > 0`. On each boundary ball `B_j` it
is the chart normal `ν_j(P_j y)` for `σ`-almost every `y`, by the Gauss–Green theorem in two
charts (`Rd.BoundedLipschitzDomain.outwardNormal_ae_eq_normalAt`). -/
noncomputable def outwardNormal (y : V) : V :=
  ∑ j, Ω.boundaryPartition.toFun j y • (Ω.graph j).normalAt ((Ω.graph j).graphProj y)

/-- The unit normal field is measurable. -/
theorem measurable_outwardNormal : Measurable Ω.outwardNormal :=
  Finset.measurable_fun_sum _ fun j _ =>
    (Ω.boundaryPartition.contDiff j).continuous.measurable.smul
      ((Ω.graph j).measurable_normalAt.comp (Ω.graph j).graphProj.continuous.measurable)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The unit normal field has norm at most `1`: `‖ν(y)‖ ≤ ∑_j ψ_j(y) ≤ 1`. -/
theorem norm_outwardNormal_le (y : V) : ‖Ω.outwardNormal y‖ ≤ 1 := by
  calc ‖Ω.outwardNormal y‖ ≤ ∑ j, ‖Ω.boundaryPartition.toFun j y • (Ω.graph j).normalAt
        ((Ω.graph j).graphProj y)‖ := norm_sum_le _ _
    _ = ∑ j, Ω.boundaryPartition.toFun j y := Finset.sum_congr rfl fun j _ => by
        rw [norm_smul, (Ω.graph j).norm_normalAt, mul_one]
        exact Real.norm_of_nonneg (Ω.boundaryPartition_nonneg j y)
    _ ≤ 1 := Ω.sum_boundaryPartition_le_one y

end BoundedLipschitzDomain

end Rd
