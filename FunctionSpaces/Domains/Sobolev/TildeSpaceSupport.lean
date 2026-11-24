/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Sobolev.LipschitzDomainGreen
public import FunctionSpaces.Domains.Sobolev.ZeroExtensionBound
public import FunctionSpaces.Rd.SingularIntegrals.ConvolutionAdjoint
public import FunctionSpaces.Rd.Atoms.SmoothAtoms
public import FunctionSpaces.Rd.Sobolev.SobolevTwoDifferences

/-!
# `H̃^s(Ω)` by supports, `s ≥ 0`

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`s ≥ 0`, `ι_s U` the `L_2` function of `U ∈ H^s(V)` (`Rd.sobolevToL2`) and `H̃^s(Ω)` the closure
of the test functions of an open set `Ω` in `H^s(V)` (`Rd.tildeSpace`). On a bounded Lipschitz
domain `Ω`, `H̃^s(Ω)` consists of the `U ∈ H^s(V)` with `ι_s U = 0` almost everywhere outside
`Ω`: `H̃^s(Ω) = Ĥ^s(Ω)` in the notation of Chandler-Wilde, Hewett and Moiola (Lemma 3.15). Since
the boundary `Γ` is a null set, this is McLean's `H̃^s(Ω) = H^s_{Ω̄}` (Theorem 3.29) for
`s ≥ 0`; the case `s = 1` is `Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`. The proof uses
mollification in `H^s(V)` (`Rd.tendsto_sobolevConv_dilate`) and smooth cut-offs
(`Rd.exists_sobolevToL2_eq_mulLp`).

* **Localised functions**: for a resolution of unity `ψ` of a bounded Lipschitz domain, every
  `ψ_j ι_s U` is `ι_s W` for some `W ∈ H^s(V)`
  (`Rd.BoundedLipschitzDomain.BoundaryPartition.exists_sobolevToL2_eq_localizeL2`).
* **Mollified functions**: smoothing a function that vanishes outside a compact set `S` with a
  smooth kernel of compact support gives a Schwartz function supported in `supp K + S`
  (`Rd.exists_schwartz_eq_conv`). Let `η` be smooth with compact support and `∫ η = 1`, and
  `η_c(x) = c^d η(c x)` its dilates (`Rd.dilate`, `d = dim V`). If `ι_s U` vanishes almost
  everywhere outside a compact set `S` and `supp η_{2^n} + S ⊆ Ω` for large `n`, then
  `U ∈ H̃^s(Ω)` (`Rd.mem_tildeSpace_of_dilate_of_nonneg`); in particular, every `U` with
  `ι_s U = 0` almost everywhere outside a compact subset of `Ω` lies in `H̃^s(Ω)`
  (`Rd.mem_tildeSpace_of_isCompact_of_nonneg`).
* **Cone mollifiers**: for a Lipschitz graph domain, a normalised bump function supported in the
  open cone of the graph and in `B̄(0, 1/2)` (`Rd.LipschitzGraph.coneMollifier`,
  `Rd.LipschitzGraph.tsupport_coneMollifier_subset`); convolution with its dilates moves the
  closure of the graph domain into the domain.
* **`H̃^s(Ω)` by supports**: on a bounded Lipschitz domain, every `U` with `ι_s U = 0` almost
  everywhere outside `Ω` is `U = ∑_j ψ_j U + χ U`, for a resolution of unity `ψ` equal to one
  near `Γ` and an interior cut-off `χ` with `χ + ∑_j ψ_j = 1` on `Ω`
  (`Rd.BoundedLipschitzDomain.eq_sum_add_of_ae_eq_zero_of_nonneg`); the chart pieces lie in
  `H̃^s(Ω)` by the cone mollifiers of the charts
  (`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart_of_nonneg`), and so
  `U ∈ H̃^s(Ω)` iff `ι_s U = 0` almost everywhere outside `Ω`
  (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff_of_nonneg`).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal SchwartzMap FourierTransform BesselPotentialSpace Pointwise

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {s : ℝ}

/-! ### Localised functions -/

/-- **Localised `H^s(V)` functions, `s ≥ 0`**: for every resolution of unity `ψ` of a bounded
Lipschitz domain, every chart `j` and `U ∈ H^s(V)` there is `W ∈ H^s(V)` with `ι_s W = ψ_j ι_s U`,
since `ψ_j` is smooth with closed support in the bounded ball `B_j`
(`Rd.BoundedLipschitzDomain.BoundaryPartition.hasCompactSupport`,
`Rd.exists_sobolevToL2_eq_mulLp`). At `s = 1` this is
`Rd.BoundedLipschitzDomain.BoundaryPartition.exists_toL2_eq_localizeL2`. -/
theorem BoundedLipschitzDomain.BoundaryPartition.exists_sobolevToL2_eq_localizeL2
    {Ω : BoundedLipschitzDomain V} (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (hs : 0 ≤ s)
    (U : H^{s}(V)) : ∃ W : H^{s}(V), sobolevToL2 hs W = ψ.localizeL2 j (sobolevToL2 hs U) :=
  exists_sobolevToL2_eq_mulLp hs (ψ.contDiff j) (ψ.hasCompactSupport j) _ _ U

/-! ### Smooth functions supported in `Ω` -/

/-- **Smoothing a function that vanishes outside a compact set**: for a smooth kernel `K` with
compact support and a locally integrable `f` vanishing outside a compact set `S`, `K ⋆ f` is a
Schwartz function with compact support in `supp K + S` (Mathlib's
`HasCompactSupport.contDiff_convolution_left`, `HasCompactSupport.convolution`,
`support_convolution_subset`). -/
theorem exists_schwartz_eq_conv {K f : V → ℂ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K)
    (hKc : HasCompactSupport K)
    (hf : LocallyIntegrable f volume) {S : Set V} (hS : IsCompact S) (hfS : ∀ x ∉ S, f x = 0) :
    ∃ w : 𝓢(V, ℂ), (w : V → ℂ) = conv K f volume ∧ HasCompactSupport w ∧
      tsupport w ⊆ tsupport K + S := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro hS hfS
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (conv K f volume) := contDiff_conv hK hKc hf
  have hcs : HasCompactSupport (conv K f volume) :=
    hKc.convolution (ContinuousLinearMap.mul ℂ ℂ) hfc
  exact ⟨hcs.toSchwartzMap hsm, rfl, hcs, closure_minimal ((support_convolution_subset _).trans
    (add_subset_add (subset_tsupport K) (Function.support_subset_iff'.2 hfS)))
    (hKc.isCompact.add hS).isClosed⟩

/-- **Mollified functions in `H̃^s(Ω)`, `s ≥ 0`**: let `Ω` be open, `U ∈ H^s(V)` with `ι_s U = 0`
almost everywhere outside a compact set `S`, and `η` a smooth function with compact support and
`∫ η = 1`. If `supp η_{2^n} + S ⊆ Ω` for all large `n`, then `U ∈ H̃^s(Ω)`: `η_{2^n} ⋆ U` has the
`L_2` function `η_{2^n} ⋆ ι_s U` (`Rd.sobolevToL2_sobolevConv`), a Schwartz function with compact
support in `supp η_{2^n} + S` (`Rd.exists_schwartz_eq_conv`), hence, for large `n`, in the span
of the test functions of `Ω` (`Rd.ofSchwartz_mem_testSpan`), and `η_{2^n} ⋆ U → U` in `H^s(V)`
(`Rd.tendsto_sobolevConv_dilate`). At `s = 1` this is `Rd.mem_tildeSpace_of_dilate`. -/
theorem mem_tildeSpace_of_dilate_of_nonneg (hs : 0 ≤ s) {Ω : Opens V} {U : H^{s}(V)} {S : Set V}
    (hS : IsCompact S) (hUS : ∀ᵐ x ∂volume, x ∉ S → sobolevToL2 hs U x = 0) {η : V → ℂ}
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hηc : HasCompactSupport η)
    (hη1 : ∫ x, η x = 1)
    (hΩ : ∀ᶠ n : ℕ in atTop, tsupport (dilate ((2 : ℝ) ^ n) η) + S ⊆ Ω) :
    U ∈ tildeSpace s Ω := by
  have hGae : S.indicator (sobolevToL2 hs U : V → ℂ) =ᵐ[volume] sobolevToL2 hs U := by
    filter_upwards [hUS] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS, hx hxS]
  have hloc : LocallyIntegrable (S.indicator (sobolevToL2 hs U : V → ℂ)) volume :=
    ((Lp.memLp (sobolevToL2 hs U)).locallyIntegrable (by norm_num)).indicator
      hS.isClosed.measurableSet
  have hc : ∀ n : ℕ, (2 : ℝ) ^ n ≠ 0 := fun n => by positivity
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  choose w hw hwc hws using fun n : ℕ => exists_schwartz_eq_conv (contDiff_dilate hη _)
    (hasCompactSupport_dilate hηc (hc n)) hloc hS fun x hx => indicator_of_notMem hx _
  have hW : ∀ n, sobolevConv (integrable_dilate hηi (hc n)) s U = ofSchwartz s (w n) :=
    fun n => by
      refine sobolevToL2_injective hs ?_
      rw [sobolevToL2_sobolevConv, sobolevToL2_ofSchwartz]
      refine Lp.ext ?_
      filter_upwards [(w n).coeFn_toLp 2 volume, convLp_apply_ae two_ne_top
        (integrable_dilate hηi (hc n)) (sobolevToL2 hs U)] with x h1 h2
      rw [h1, h2, hw n, conv_congr_ae hGae]
  have ht := tendsto_sobolevConv_dilate hηi hη1 hc
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) U
  rw [tildeSpace, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto ht (hΩ.mono fun n hn => ?_)
  rw [SetLike.mem_coe, hW n]
  exact ofSchwartz_mem_testSpan s (hwc n) ((hws n).trans hn)

/-- **Functions with compact support in `Ω` lie in `H̃^s(Ω)`, `s ≥ 0`**: for an open set `Ω`,
every `U ∈ H^s(V)` with `ι_s U = 0` almost everywhere outside a compact subset `S` of `Ω` lies in
`H̃^s(Ω)`. Some thickening `S_δ` lies in `Ω` (Mathlib's `IsCompact.exists_thickening_subset_open`),
and for the mollifier of the standard bump `Rd.stdBumpBase`, supported in `B̄(0, 1)`, eventually
`supp η_{2^n} + S ⊆ S_δ` (`Rd.eventually_tsupport_dilate_add_subset_thickening`,
`Rd.mem_tildeSpace_of_dilate_of_nonneg`). At `s = 1` this is `Rd.mem_tildeSpace_of_isCompact`. -/
theorem mem_tildeSpace_of_isCompact_of_nonneg (hs : 0 ≤ s) {Ω : Opens V} {U : H^{s}(V)}
    {S : Set V} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (hUS : ∀ᵐ x ∂volume, x ∉ S → sobolevToL2 hs U x = 0) : U ∈ tildeSpace s Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hS.exists_thickening_subset_open Ω.isOpen hSΩ
  refine mem_tildeSpace_of_dilate_of_nonneg hs hS hUS
    (contDiff_bumpMollifier (stdBumpBase (V := V))) (hasCompactSupport_bumpMollifier _)
    (integral_bumpMollifier _) ?_
  exact (eventually_tsupport_dilate_add_subset_thickening (tsupport_bumpMollifier_subset _) hδ
    S).mono fun n hn => hn.trans hδΩ

/-! ### Mollifiers supported in the cone of a Lipschitz graph -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The bump function of the cone mollifier: centre `e/4`, radii `ρ/4` and `ρ/2` for the cone
radius `ρ = 1/(8(M + 1))`. -/
noncomputable def coneMollifierBase : ContDiffBump ((1 / 4 : ℝ) • Ω.e) :=
  ⟨Ω.coneRadius / 4, Ω.coneRadius / 2, by have := Ω.coneRadius_pos; positivity,
    by have := Ω.coneRadius_pos; linarith⟩

/-- **The cone mollifier**: a smooth function with integral `1` and compact support in the open
cone `K` of the graph and in `B̄(0, 1/2)` (`Rd.LipschitzGraph.tsupport_coneMollifier_subset`), the
mollifier of the bump `Rd.LipschitzGraph.coneMollifierBase`. Convolution with its dilates moves
the closure of the graph domain into the domain (`Rd.LipschitzGraph.add_mem_of_mem_closure`). -/
noncomputable def coneMollifier : V → ℂ := bumpMollifier Ω.coneMollifierBase

/-- The cone mollifier is supported in the open cone and in `B̄(0, 1/2)`: its closed support is
`B̄(e/4, ρ/2) ⊆ B(e/4, ρ) ⊆ K` (`Rd.LipschitzGraph.ball_subset_graphCone`), and
`‖e/4‖ + ρ/2 ≤ 1/2`. -/
theorem tsupport_coneMollifier_subset :
    tsupport Ω.coneMollifier ⊆ Ω.graphCone ∩ closedBall 0 (1 / 2) := by
  intro z hz
  have h := tsupport_bumpMollifier_subset Ω.coneMollifierBase hz
  have hρ := Ω.coneRadius_pos
  have hρ8 := Ω.coneRadius_le
  have hr : Ω.coneMollifierBase.rOut = Ω.coneRadius / 2 := rfl
  rw [hr] at h
  refine ⟨Ω.ball_subset_graphCone (closedBall_subset_ball (by linarith) h), ?_⟩
  rw [mem_closedBall, dist_eq_norm] at h
  have he : ‖(1 / 4 : ℝ) • Ω.e‖ = 1 / 4 := by
    rw [norm_smul, Ω.norm_e, mul_one, Real.norm_of_nonneg (by norm_num)]
  have hz' : ‖z‖ ≤ ‖z - (1 / 4 : ℝ) • Ω.e‖ + ‖(1 / 4 : ℝ) • Ω.e‖ := by
    have := norm_add_le (z - (1 / 4 : ℝ) • Ω.e) ((1 / 4 : ℝ) • Ω.e)
    rwa [sub_add_cancel] at this
  rw [mem_closedBall_zero_iff]
  linarith

end LipschitzGraph

/-! ### `H̃^s(Ω)` by supports -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The local lemma: chart pieces of functions vanishing outside `Ω` lie in `H̃^s(Ω)`**, for
`s ≥ 0`: let `U ∈ H^s(V)` with `ι_s U = 0` almost everywhere outside `Ω`, and let `ζ` be a
continuous bounded real function with closed support in the boundary ball `B_j`. Every
`W ∈ H^s(V)` with `ι_s W = ζ ι_s U` lies in `H̃^s(Ω)`. `ι_s W` vanishes outside the compact set
`S = Ω̄_j ∩ supp ζ`, since `Ω ∩ B_j` is the graph domain `Ω_j` inside `B_j`; the cone mollifier of
the chart moves `S` into `Ω_j` (`Rd.LipschitzGraph.add_mem_of_mem_closure`,
`Rd.LipschitzGraph.mem_graphCone_of_mem_tsupport_dilate`), and its small dilates keep it inside
`B_j` (`Rd.eventually_tsupport_dilate_add_subset_thickening`,
`Rd.mem_tildeSpace_of_dilate_of_nonneg`). At `s = 1` this is
`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart`. -/
theorem mem_tildeSpace_of_mulLp_chart_of_nonneg (hs : 0 ≤ s) (j : Fin Ω.N) {U : H^{s}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → sobolevToL2 hs U x = 0) {ζ : V → ℝ}
    (hζ : tsupport ζ ⊆ ball (Ω.center j) (Ω.radius j)) {C : ℝ}
    (hc : Continuous fun x => (ζ x : ℂ)) (hC : ∀ x, ‖(ζ x : ℂ)‖ ≤ C) {W : H^{s}(V)}
    (hW : sobolevToL2 hs W = mulLp hc hC (sobolevToL2 hs U)) : W ∈ tildeSpace s Ω.toOpens := by
  have hB := Ω.inter_ball_eq j le_rfl
  have hK : IsCompact (tsupport ζ) :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (isBounded_ball.subset hζ)
  have hS : IsCompact (closure (Ω.graph j).domain ∩ tsupport ζ) := hK.inter_left isClosed_closure
  have hWS : ∀ᵐ x ∂volume, x ∉ closure (Ω.graph j).domain ∩ tsupport ζ →
      sobolevToL2 hs W x = 0 := by
    rw [hW]
    filter_upwards [mulLp_apply_ae hc hC (sobolevToL2 hs U), hU] with x h1 h2 hxS
    rw [h1]
    by_cases hxK : x ∈ tsupport ζ
    · have hxΩ : x ∉ Ω.carrier := fun hxΩ =>
        hxS ⟨subset_closure ((Set.ext_iff.1 hB x).1 ⟨hxΩ, hζ hxK⟩).1, hxK⟩
      rw [h2 hxΩ, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hxK, Complex.ofReal_zero, zero_mul]
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_thickening_subset_open isOpen_ball hζ
  have hη := (Ω.graph j).tsupport_coneMollifier_subset
  refine mem_tildeSpace_of_dilate_of_nonneg hs (η := (Ω.graph j).coneMollifier) hS hWS
    (contDiff_bumpMollifier _) (hasCompactSupport_bumpMollifier _) (integral_bumpMollifier _) ?_
  filter_upwards [eventually_tsupport_dilate_add_subset_thickening (hη.trans inter_subset_right)
    hδ (closure (Ω.graph j).domain ∩ tsupport ζ)] with n hn
  rintro _ ⟨z, hz, y, hy, rfl⟩
  have hzK := (Ω.graph j).mem_graphCone_of_mem_tsupport_dilate (hη.trans inter_subset_left)
    (by positivity) hz
  have hzyB : z + y ∈ ball (Ω.center j) (Ω.radius j) :=
    hδB (thickening_subset_of_subset δ inter_subset_right (hn ⟨z, hz, y, hy, rfl⟩))
  have hzyD : z + y ∈ (Ω.graph j).domain := by
    rw [add_comm]
    exact (Ω.graph j).add_mem_of_mem_closure hy.1 hzK
  rw [Ω.coe_toOpens]
  exact ((Set.ext_iff.1 hB (z + y)).2 ⟨hzyD, hzyB⟩).1

/-- **The decomposition in `L_2(V)` of a function vanishing outside `Ω`**: if
`χ + ∑_j ψ_j = 1` on `Ω` for a resolution of unity `ψ` and a continuous bounded real `χ`, then
`F = ∑_j ψ_j F + χ F` for every `F ∈ L_2(V)` vanishing almost everywhere outside `Ω`: on `Ω` the
factors add up to `1`, outside `Ω` both sides vanish. -/
theorem eq_sum_localizeL2_add_mulLp (ψ : Ω.BoundaryPartition) {χ : V → ℝ}
    (hχ1 : ∀ x ∈ Ω.carrier, χ x + ∑ j, ψ.toFun j x = 1) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C)
    {F : Lp ℂ 2 (volume : Measure V)} (hF : ∀ᵐ x ∂volume, x ∉ Ω.carrier → F x = 0) :
    F = ∑ j, ψ.localizeL2 j F + mulLp hc hC F := by
  refine Lp.ext ?_
  have hloc : ∀ᵐ x ∂(volume : Measure V), ∀ j,
      (ψ.localizeL2 j F : V → ℂ) x = ψ.toComplex j x * F x :=
    ae_all_iff.2 fun j => mulLp_apply_ae _ _ _
  filter_upwards [hF, hloc, mulLp_apply_ae hc hC F,
    Lp.coeFn_add (∑ j, ψ.localizeL2 j F) (mulLp hc hC F),
    Lp.coeFn_fun_finsetSum Finset.univ fun j => ψ.localizeL2 j F] with x h1 h2 h3 h4 h5
  rw [h4, Pi.add_apply, h5, h3]
  simp only [h2]
  rw [← Finset.sum_mul, ← add_mul]
  by_cases hx : x ∈ Ω.carrier
  · have h6 : ∑ j, ψ.toComplex j x + (χ x : ℂ) = 1 := by
      simp only [BoundaryPartition.toComplex]
      rw [← Complex.ofReal_sum, ← Complex.ofReal_add, add_comm, hχ1 x hx, Complex.ofReal_one]
    rw [h6, one_mul]
  · rw [h1 hx, mul_zero]

/-- **The decomposition of a function vanishing outside `Ω`**, for `s ≥ 0`: if `χ + ∑_j ψ_j = 1`
on `Ω`, `U ∈ H^s(V)` has `ι_s U = 0` almost everywhere outside `Ω`, `ι_s W_j = ψ_j ι_s U` and
`ι_s W_0 = χ ι_s U`, then `U = ∑_j W_j + W_0` in `H^s(V)`: the `L_2` functions agree
(`Rd.BoundedLipschitzDomain.eq_sum_localizeL2_add_mulLp`), and `ι_s` is injective
(`Rd.sobolevToL2_injective`). At `s = 1` this is
`Rd.BoundedLipschitzDomain.eq_sum_add_of_ae_eq_zero`. -/
theorem eq_sum_add_of_ae_eq_zero_of_nonneg (hs : 0 ≤ s) (ψ : Ω.BoundaryPartition)
    {χ : V → ℝ} (hχ1 : ∀ x ∈ Ω.carrier, χ x + ∑ j, ψ.toFun j x = 1) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) {U : H^{s}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → sobolevToL2 hs U x = 0) {Wj : Fin Ω.N → H^{s}(V)}
    (hWj : ∀ j, sobolevToL2 hs (Wj j) = ψ.localizeL2 j (sobolevToL2 hs U))
    {W0 : H^{s}(V)} (hW0 : sobolevToL2 hs W0 = mulLp hc hC (sobolevToL2 hs U)) :
    U = ∑ j, Wj j + W0 := by
  refine sobolevToL2_injective hs ?_
  rw [map_add, map_sum, hW0]
  simp only [hWj]
  exact Ω.eq_sum_localizeL2_add_mulLp ψ hχ1 hc hC hU

/-- **Functions vanishing outside `Ω` lie in `H̃^s(Ω)`, `s ≥ 0`**: on a bounded Lipschitz
domain, every `U ∈ H^s(V)` with `ι_s U = 0` almost everywhere outside `Ω` lies in the closure of
the test functions of `Ω`. With a resolution of unity `ψ` equal to one near `Γ`
(`Rd.BoundedLipschitzDomain.exists_boundaryPartition_nhds`) and the interior cut-off `χ`
(`Rd.BoundedLipschitzDomain.exists_interior_cutoff`), `U = ∑_j ψ_j U + χ U`
(`Rd.exists_sobolevToL2_eq_mulLp`,
`Rd.BoundedLipschitzDomain.eq_sum_add_of_ae_eq_zero_of_nonneg`); the chart pieces lie in
`H̃^s(Ω)` by the cone mollifiers
(`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart_of_nonneg`), the interior piece since
it vanishes outside a compact subset of `Ω` (`Rd.mem_tildeSpace_of_isCompact_of_nonneg`). -/
theorem mem_tildeSpace_of_ae_eq_zero_of_nonneg (hs : 0 ≤ s) {U : H^{s}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → sobolevToL2 hs U x = 0) :
    U ∈ tildeSpace s Ω.toOpens := by
  obtain ⟨ψ, -, -, hψ⟩ := Ω.exists_boundaryPartition_nhds
  obtain ⟨χ, hχ, hcs, hχΩ, hχ1⟩ := exists_interior_cutoff ψ hψ
  have hc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hcs.comp_left Complex.ofReal_zero)
  choose Wj hWj using fun j => ψ.exists_sobolevToL2_eq_localizeL2 j hs U
  obtain ⟨W0, hW0⟩ := exists_sobolevToL2_eq_mulLp hs hχ hcs hc hC U
  rw [Ω.eq_sum_add_of_ae_eq_zero_of_nonneg hs ψ hχ1 hc hC hU hWj hW0]
  refine add_mem (Submodule.sum_mem _ fun j _ =>
    Ω.mem_tildeSpace_of_mulLp_chart_of_nonneg hs j hU (ψ.tsupport_subset j) _ _ (hWj j)) ?_
  refine mem_tildeSpace_of_isCompact_of_nonneg hs hcs.isCompact
    (by rw [Ω.coe_toOpens]; exact hχΩ) ?_
  rw [hW0]
  filter_upwards [mulLp_apply_ae hc hC (sobolevToL2 hs U)] with x hx hxS
  rw [hx, image_eq_zero_of_notMem_tsupport hxS, Complex.ofReal_zero, zero_mul]

/-- **`H̃^s(Ω)` is the space of `H^s(V)` functions vanishing outside `Ω`, `s ≥ 0`**: on a bounded
Lipschitz domain, `U ∈ H^s(V)` lies in `H̃^s(Ω)` iff `ι_s U = 0` almost everywhere outside `Ω`
(`Rd.sobolevToL2_ae_eq_zero_of_mem_tildeSpace`,
`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_ae_eq_zero_of_nonneg`). In the notation of
Chandler-Wilde, Hewett and Moiola this is `H̃^s(Ω) = Ĥ^s(Ω)` (Lemma 3.15). Since `Γ` is a null
set (`Rd.BoundedLipschitzDomain.volume_frontier`), it is McLean's `H̃^s(Ω) = H^s_{Ω̄}`
(Theorem 3.29) for `s ≥ 0`. At `s = 1` it is `Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`. -/
theorem mem_tildeSpace_iff_of_nonneg (hs : 0 ≤ s) (U : H^{s}(V)) :
    U ∈ tildeSpace s Ω.toOpens ↔ ∀ᵐ x ∂volume, x ∉ Ω.carrier → sobolevToL2 hs U x = 0 :=
  ⟨sobolevToL2_ae_eq_zero_of_mem_tildeSpace hs, Ω.mem_tildeSpace_of_ae_eq_zero_of_nonneg hs⟩

end BoundedLipschitzDomain

end Rd
