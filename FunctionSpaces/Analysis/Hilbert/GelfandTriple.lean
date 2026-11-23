/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gelfand triples

Let `V` and `H` be Hilbert spaces over `𝕜 = ℝ` or `ℂ` and `ι : V → H` a bounded linear map.

* **The pivot dual** `J : H → V*`, `J g = ⟪g, ι ·⟫_H` (`ContinuousLinearMap.pivotDual`,
  `ContinuousLinearMap.pivotDual_apply_apply`), is the adjoint `ι* : H → V` followed by Riesz's
  isometry `V → V*` (Mathlib's `ContinuousLinearMap.adjoint`, `InnerProductSpace.toDual`). It is
  conjugate-linear and bounded, `‖J g‖ = ‖ι* g‖ ≤ ‖ι‖ ‖g‖` and `‖J‖ = ‖ι‖`
  (`ContinuousLinearMap.norm_pivotDual_apply`, `ContinuousLinearMap.norm_pivotDual_apply_le`,
  `ContinuousLinearMap.norm_pivotDual`).
* **Injectivity**: the kernel of `J` is `(range ι)^⊥` (`ContinuousLinearMap.ker_pivotDual`), and
  a continuous linear map into a Hilbert space has dense range iff the orthogonal complement of
  its range is `{0}` (`ContinuousLinearMap.denseRange_iff_orthogonal_range_eq_bot`), so `J` is
  injective iff `ι` has dense range (`ContinuousLinearMap.pivotDual_injective_iff`); and
  `J (ι v) w = ⟪ι v, ι w⟫_H`, so `J ∘ ι : V → V*` is injective iff `ι` is
  (`ContinuousLinearMap.pivotDual_comp_injective_iff`).

If `ι` is injective with dense range, `V ⊂ H ⊂ V*` is a **Gelfand triple** (often called a rigged
Hilbert space; for separable `V` an evolution triple in Zeidler's sense) with **pivot space** `H`
(Brezis): `H` is identified with its dual by Riesz, and the duality of `V*` and `V` extends the
inner product of `H`.

* **Pivot space `L_2(μ)`**: for `ι : V → L_2(μ)`, `J g v = ∫ conj (g) ι v dμ`
  (`MeasureTheory.L2.pivotDual_apply_apply_eq_integral`).
* **Dense range in `L_2`**: let `μ` be a locally finite measure on a finite-dimensional real
  space that is carried by an open set `U`. A function of `L_p(μ)`, `p ≥ 1`, that integrates to
  zero against every smooth real function with compact support in `U` is zero
  (`MeasureTheory.Lp.eq_zero_of_forall_integral_contDiff_smul_eq_zero`, from Mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`), so a continuous linear map into
  `L_2(μ)` whose range contains these functions has dense range
  (`MeasureTheory.L2.denseRange_of_forall_contDiff`).

The Sobolev spaces on `ℝ^d`, on open sets and on the boundary of a bounded Lipschitz domain give
their Gelfand triples with pivot space `L_2` through `ContinuousLinearMap.pivotDual_injective_iff`:
each contributes its embedding into `L_2`, the dense range of that embedding (on open sets and on
the boundary by `MeasureTheory.L2.denseRange_of_forall_contDiff`, on `ℝ^d` by the density of the
Schwartz functions) and the identification of the pivot dual with the pairing of the space of
negative order.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **Dense range by orthogonal complements**: a continuous linear map `T` from a topological
module `X` into a Hilbert space `H` has dense range iff the orthogonal complement of its range is
`{0}` (Mathlib's `Submodule.topologicalClosure_eq_top_iff`,
`Submodule.dense_iff_topologicalClosure_eq_top`). -/
theorem denseRange_iff_orthogonal_range_eq_bot {X : Type*} [TopologicalSpace X]
    [AddCommMonoid X] [Module 𝕜 X] (T : X →L[𝕜] H) : DenseRange T ↔ T.rangeᗮ = ⊥ := by
  rw [← Submodule.topologicalClosure_eq_top_iff, ← Submodule.dense_iff_topologicalClosure_eq_top,
    LinearMap.coe_range]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  (ι : V →L[𝕜] H)

/-- **The pivot dual** `J : H → V*` of a bounded linear map `ι : V → H` of Hilbert spaces:
`J g = ⟪g, ι ·⟫_H` (`ContinuousLinearMap.pivotDual_apply_apply`), the functional on `V` given by
the inner product of `H`. It is the adjoint `ι* : H → V` (Mathlib's
`ContinuousLinearMap.adjoint`) followed by Riesz's conjugate-linear isometry `V → V*` (Mathlib's
`InnerProductSpace.toDual`), hence conjugate-linear and bounded. If `ι` is injective with dense
range, `V ⊂ H ⊂ V*` is a Gelfand triple with pivot space `H`, and `J` is the inclusion of `H`
into `V*`. -/
noncomputable def pivotDual : H →L⋆[𝕜] StrongDual 𝕜 V :=
  (InnerProductSpace.toDual 𝕜 V).toLinearIsometry.toContinuousLinearMap.comp (adjoint ι)

/-- **The pivot dual is the inner product of `H`**: `J g v = ⟪g, ι v⟫_H` for `g ∈ H` and `v ∈ V`
(Mathlib's `InnerProductSpace.toDual_apply_apply`, `ContinuousLinearMap.adjoint_inner_left`). -/
theorem pivotDual_apply_apply (g : H) (v : V) : ι.pivotDual g v = ⟪g, ι v⟫_𝕜 := by
  change InnerProductSpace.toDual 𝕜 V (adjoint ι g) v = _
  rw [InnerProductSpace.toDual_apply_apply, adjoint_inner_left]

/-- **The duality of `V*` and `V` extends the inner product of `H`**: for `v, w ∈ V`,
`J (ι v) w = ⟪ι v, ι w⟫_H`. -/
theorem pivotDual_apply_apply_self (v w : V) : ι.pivotDual (ι v) w = ⟪ι v, ι w⟫_𝕜 :=
  ι.pivotDual_apply_apply (ι v) w

/-- **The norm of `J g`** is the norm of `ι* g`, since Riesz's map `V → V*` is an isometry
(Mathlib's `LinearIsometryEquiv.norm_map`). -/
theorem norm_pivotDual_apply (g : H) : ‖ι.pivotDual g‖ = ‖adjoint ι g‖ :=
  (InnerProductSpace.toDual 𝕜 V).norm_map (adjoint ι g)

/-- **The norm of the pivot dual** is that of `ι`: `‖J‖ = ‖ι*‖ = ‖ι‖` (Mathlib's
`LinearIsometry.norm_toContinuousLinearMap_comp`, and `ContinuousLinearMap.adjoint` is an
isometry). -/
theorem norm_pivotDual : ‖ι.pivotDual‖ = ‖ι‖ := by
  rw [pivotDual, LinearIsometry.norm_toContinuousLinearMap_comp, LinearIsometryEquiv.norm_map]

/-- **The pivot dual is bounded**: `‖J g‖ ≤ ‖ι‖ ‖g‖` for every `g ∈ H`
(`ContinuousLinearMap.norm_pivotDual`). -/
theorem norm_pivotDual_apply_le (g : H) : ‖ι.pivotDual g‖ ≤ ‖ι‖ * ‖g‖ := by
  rw [← ι.norm_pivotDual]
  exact ι.pivotDual.le_opNorm g

/-- **The kernel of the pivot dual** is the orthogonal complement of the range of `ι`: `J g = 0`
iff `ι* g = 0`, since Riesz's map is injective, and `ker ι* = (range ι)^⊥` (Mathlib's
`ContinuousLinearMap.orthogonal_range`). -/
theorem ker_pivotDual : ι.pivotDual.ker = ι.rangeᗮ := by
  ext g
  rw [LinearMap.mem_ker, orthogonal_range, LinearMap.mem_ker]
  exact (InnerProductSpace.toDual 𝕜 V).map_eq_zero_iff

/-- **The pivot dual is injective iff `ι` has dense range**: the kernel of `J` is
`(range ι)^⊥` (`ContinuousLinearMap.ker_pivotDual`), which is `{0}` iff the range is dense
(`ContinuousLinearMap.denseRange_iff_orthogonal_range_eq_bot`). Then `H` embeds into `V*`. -/
theorem pivotDual_injective_iff : Function.Injective ι.pivotDual ↔ DenseRange ι := by
  rw [denseRange_iff_orthogonal_range_eq_bot, ← ker_pivotDual, Submodule.eq_bot_iff,
    injective_iff_map_eq_zero]
  simp only [LinearMap.mem_ker, coe_coe]

/-- **The embedding `V → V*` of the triple**: `v ↦ J (ι v) = ⟪ι v, ι ·⟫_H` is injective iff `ι` is.
`J ∘ ι` is Riesz's injective map `V → V*` after `ι* ∘ ι`, and `ι* ∘ ι` is injective iff `ι` is
(Mathlib's `ContinuousLinearMap.adjoint_comp_self_injective_iff`, from
`⟪ι* ι v, v⟫ = ‖ι v‖²`). -/
theorem pivotDual_comp_injective_iff :
    Function.Injective (ι.pivotDual.comp ι) ↔ Function.Injective ι := by
  change Function.Injective (InnerProductSpace.toDual 𝕜 V ∘ (adjoint ι ∘ ι)) ↔ _
  rw [(InnerProductSpace.toDual 𝕜 V).injective.of_comp_iff, ι.adjoint_comp_self_injective_iff]

end ContinuousLinearMap

namespace MeasureTheory

section Separation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]

/-- **Smooth functions separate `L_p(μ)`**, `1 ≤ p ≤ ∞`: let `μ` be a locally finite measure on a
finite-dimensional real space, carried by an open set `U` (`μ`-almost every point lies in `U`),
and `F` a real Banach space. If `f ∈ L_p(μ; F)` has `∫ ψ f dμ = 0` for every smooth real `ψ`
with compact support in `U`, then `f = 0`. `L_p(μ)` functions are locally integrable for
`p ≥ 1` (Mathlib's `MemLp.locallyIntegrable`), and the fundamental lemma of the calculus of
variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `f = 0` almost
everywhere on `U`. -/
theorem Lp.eq_zero_of_forall_integral_contDiff_smul_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set E} (hU : IsOpen U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (f : Lp F p μ)
    (h : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ψ x • f x ∂μ = 0) : f = 0 := by
  have hf : LocallyIntegrableOn (f : E → F) U μ :=
    ((Lp.memLp f).locallyIntegrable hp).locallyIntegrableOn U
  have h0 : ∀ᵐ x ∂μ, x ∈ U → (f : E → F) x = 0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [h0, hμ] with x hx hxU
  exact hx hxU

end Separation

namespace L2

section PivotDual

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]

/-- **The pivot dual into `L_2(μ)`**: for a bounded linear map `ι` from a Hilbert space `X` into
`L_2(μ)` with values in `𝕜 = ℝ` or `ℂ`, the pivot dual of `g ∈ L_2(μ)` is
`J g v = ∫ conj (g) ι v dμ` for `v ∈ X` (`ContinuousLinearMap.pivotDual_apply_apply`, Mathlib's
`MeasureTheory.L2.inner_def`, `RCLike.inner_apply'`). -/
theorem pivotDual_apply_apply_eq_integral (ι : X →L[𝕜] Lp 𝕜 2 μ) (g : Lp 𝕜 2 μ) (v : X) :
    ι.pivotDual g v = ∫ x, conj (g x) * ι v x ∂μ := by
  rw [ContinuousLinearMap.pivotDual_apply_apply, inner_def]
  simp only [RCLike.inner_apply']

end PivotDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]

/-- **Dense range in `L_2(μ)`**: for `μ` and `U` as in
`MeasureTheory.Lp.eq_zero_of_forall_integral_contDiff_smul_eq_zero`, a continuous linear map `T`
from a topological module `X` into the complex `L_2(μ)` whose range contains every smooth real
function with compact support in `U` (up to `μ`-null sets) has dense range. A function `f`
orthogonal to the range has `∫ ψ f dμ = ⟪ψ, f⟫ = 0` for all these `ψ`, since `ψ` is real, hence
vanishes (`ContinuousLinearMap.denseRange_iff_orthogonal_range_eq_bot`). -/
theorem denseRange_of_forall_contDiff {X : Type*} [TopologicalSpace X] [AddCommMonoid X]
    [Module ℂ X] (T : X →L[ℂ] Lp ℂ 2 μ) {U : Set E} (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hT : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∃ x, (T x : E → ℂ) =ᵐ[μ] fun y => (ψ y : ℂ)) : DenseRange T := by
  rw [ContinuousLinearMap.denseRange_iff_orthogonal_range_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  refine Lp.eq_zero_of_forall_integral_contDiff_smul_eq_zero one_le_two hU hμ f
    fun ψ hψ hc hsupp => ?_
  obtain ⟨x, hx⟩ := hT ψ hψ hc hsupp
  have h : ⟪T x, f⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self (T : X →ₗ[ℂ] Lp ℂ 2 μ) x) hf
  rw [inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [hx] with y hy
  rw [hy, RCLike.inner_apply', Complex.conj_ofReal, Complex.real_smul]

end L2

end MeasureTheory
