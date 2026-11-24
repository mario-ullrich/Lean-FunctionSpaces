/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Sobolev.TildeSpaceSupport
public import FunctionSpaces.Domains.Traces.BoundarySobolev
public import FunctionSpaces.Domains.Sobolev.SobolevDuality

/-!
# The kernel of the trace

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner product
space `V`, such as `ℝ^d`, with Lebesgue measure, `H^s(Ω)` the Hilbert space of restrictions of
`H^s(V)`, `H̃^s(Ω)` the closure of the test functions of `Ω` in `H^s(V)`, `H^s_0(Ω)` the
closure of their restrictions in `H^s(Ω)`, and `ker γ_s = Ω.traceKer s` the trace kernel of
`H^s(Ω)`, `1/2 < s < 3/2`, with `ker γ = ker γ_1`.

* **Mollification in `H^1(V)`**: convergence of the `L_2` functions and of their weak
  derivatives gives convergence in `H^1(V)` (`Rd.tendsto_of_tendsto_toL2`), so the mollified
  `η_c ⋆ U` converge to `U` in `H^1(V)` as `c → ∞` (`Rd.tendsto_of_toL2_eq_convLp`).
* **`H̃^1(Ω)` by supports**: the cases `s = 1` of `FunctionSpaces.Domains.Sobolev.TildeSpaceSupport`
  with the `L_2` function `Rd.toL2` (`Rd.sobolevToL2_one`). Mollified functions supported in `Ω`
  lie in `H̃^1(Ω)` (`Rd.mem_tildeSpace_of_dilate`, `Rd.mem_tildeSpace_of_isCompact`), and on a
  bounded Lipschitz domain `U ∈ H^1(V)` lies in `H̃^1(Ω)` iff it vanishes outside `Ω`
  (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`). For `U ∈ H^1(V)` vanishing outside an open set
  `Ω`, the zero extension of `U|_Ω` is `U` (`Rd.indicatorLp_toL2_restrictProj`).
* **`ker γ = H^1_0(Ω)`** (`Rd.BoundedLipschitzDomain.traceKer_one_eq_zeroBoundarySpace`, McLean,
  Theorem 3.40): `H^s_0(Ω) ⊆ ker γ_s` for every `1/2 < s < 3/2`
  (`Rd.BoundedLipschitzDomain.zeroBoundarySpace_le_traceKer`), since the test functions, read in
  `H^s(V)` for any `s ≥ 0`, are continuous and have zero boundary trace
  (`Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_ofTest`); conversely, `u ∈ H^1(Ω)` with zero
  trace has its zero extension in `H^1(V)`
  (`Rd.BoundedLipschitzDomain.memWSobolev_indicatorLp_iff_mem_traceKer`), the zero extension lies
  in `H̃^1(Ω)`, and so `u ∈ H^1_0(Ω)`.
* **`H̃^1(Ω) ≅ ker γ` and the dual**: restriction is an isometry of `H̃^1(Ω)` onto `ker γ`
  (`Rd.BoundedLipschitzDomain.tildeEquivTraceKer`), and `(ker γ)^* ≅ H^{-1}(Ω)`
  (`Rd.BoundedLipschitzDomain.dualTraceKerEquiv`).
* **`ker γ_s = H^s_0(Ω)` for `1/2 < s ≤ 1`**
  (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace_of_le_one`; McLean, Theorem 3.40,
  applied in this range by Hewett–Moiola, Remark 2.6). The trace `T^s_Γ : H^s(V) → L_2(Γ)`
  commutes with the inclusions (`Rd.BoundedLipschitzDomain.ambientTraceL2_sobolevInclusion`).
  The extension from the boundary `E_Γ` (`Rd.BoundedLipschitzDomain.besovExtendLp`), one
  operator for every smoothness, maps
  `B^{s-1/2}_{2,2}(Γ)` into `H^s(V)` with a bound
  (`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_besovExtendLp`,
  `Rd.BoundedLipschitzDomain.exists_enorm_le_of_sobolevToL2_eq_besovExtendLp`), and `U` minus the
  extension of its trace restricts to `ker γ_s`
  (`Rd.BoundedLipschitzDomain.restrictProj_sub_mem_traceKer`). For `u ∈ ker γ_s` and
  `W' ∈ H^1(V)` this correction of `W'` at the level `1` lies in `H^1_0(Ω) ⊆ H^s_0(Ω)` and within
  `K ‖ι_{s,1} W' - u‖` of `u`
  (`Rd.BoundedLipschitzDomain.exists_mem_zeroBoundarySpace_enorm_sub_le`), and `H^1(V)` is dense
  in `H^s(V)`.

`FunctionSpaces.Domains.Traces.TraceKernelGeneral` proves `ker γ_s = H^s_0(Ω)` for
`1 ≤ s < 3/2` by zero extension, and holds the quotient `H^s(Ω) ⧸ H^s_0(Ω)` for every
`1/2 < s < 3/2`.
-/

@[expose] public section

open MeasureTheory Module Metric Filter Topology Set TopologicalSpace
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace Distributions LineDeriv Pointwise

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Mollification in `H^1(V)` -/

/-- **Convergence in `H^1(V)`** from the convergence of the `L_2` functions and of all their weak
derivatives in `L_2(V)`: `‖W - U‖ ≤ ‖ι W - ι U‖_2 + ∑_i ‖∂_{e_i} W - ∂_{e_i} U‖_2` for an
orthonormal basis `(e_i)` (`Rd.norm_le_norm_toL2_add_sum`). -/
theorem tendsto_of_tendsto_toL2 {ι : Type*} {l : Filter ι} {W : ι → H^{1}(V)} {U : H^{1}(V)}
    (h0 : Tendsto (fun i => toL2 (W i)) l (𝓝 (toL2 U)))
    (h1 : ∀ v : V, Tendsto (fun i => weakDerivL2 v (W i)) l (𝓝 (weakDerivL2 v U))) :
    Tendsto W l (𝓝 U) := by
  let b := stdOrthonormalBasis ℝ V
  rw [tendsto_iff_norm_sub_tendsto_zero] at h0 ⊢
  have h2 := h0.add (tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_iff_norm_sub_tendsto_zero.1 (h1 (b i)))
  simp only [Finset.sum_const_zero, add_zero] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) h2
  refine (norm_le_norm_toL2_add_sum b (W i - U)
    (G := fun k => weakDerivL2 (b k) (W i) - weakDerivL2 (b k) U) fun k => ?_).trans_eq (by
      rw [map_sub])
  rw [← map_sub]
  exact hasWeakLineDeriv_weakDerivL2 _ _

/-- **Mollification converges in `H^1(V)`**: let `η` be a Schwartz function with `∫ η = 1`,
`c_i ≠ 0` dilation factors with `c_i → ∞`, `η_c(x) = c^n η(c x)`, and `U ∈ H^1(V)`. If
`W_i ∈ H^1(V)` has the `L_2` function `η_{c_i} ⋆ ι U`, then `W_i → U` in `H^1(V)`. The weak
derivatives of `η_{c_i} ⋆ ι U` are `η_{c_i} ⋆ ∂_v U` (`Rd.hasWeakLineDeriv_convLp`), and
approximate identities converge in `L_2(V)` (`Rd.tendsto_convLp_dilate`). -/
theorem tendsto_of_toL2_eq_convLp {η : 𝓢(V, ℂ)} (h1 : ∫ x, η x = 1) {ι : Type*} {l : Filter ι}
    {c : ι → ℝ} (hc : ∀ i, c i ≠ 0) (hcl : Tendsto c l atTop) (U : H^{1}(V))
    {W : ι → H^{1}(V)}
    (hW : ∀ i, toL2 (W i) = convLp two_ne_top (integrable_dilate η.integrable (hc i)) (toL2 U)) :
    Tendsto W l (𝓝 U) := by
  refine tendsto_of_tendsto_toL2 ?_ fun v => ?_
  · simp_rw [hW]
    exact tendsto_convLp_dilate two_ne_top η.integrable h1 hc hcl _
  · have hd : ∀ i, weakDerivL2 v (W i) =
        convLp two_ne_top (integrable_dilate η.integrable (hc i)) (weakDerivL2 v U) := fun i =>
      weakDerivL2_eq (by
        rw [hW i]
        exact hasWeakLineDeriv_convLp two_ne_top two_ne_top (schwartzDilate (c i) (hc i) η) _
          (coe_schwartzDilate _ _ _) (hasWeakLineDeriv_weakDerivL2 v U))
    simp_rw [hd]
    exact tendsto_convLp_dilate two_ne_top η.integrable h1 hc hcl _

/-! ### `H̃^1(Ω)` by supports -/

/-- **Mollified functions in `H̃^1(Ω)`**: let `Ω` be open, `U ∈ H^1(V)` vanishing almost everywhere
outside a compact set `S`, and `η` a smooth function with compact support and `∫ η = 1`. If
`supp η_{2^n} + S ⊆ Ω` for all large `n`, then `U ∈ H̃^1(Ω)`. This is the case `s = 1` of
`Rd.mem_tildeSpace_of_dilate_of_nonneg`, with the `L_2` function `ι_1 = Rd.toL2`
(`Rd.sobolevToL2_one`). -/
theorem mem_tildeSpace_of_dilate {Ω : Opens V} {U : H^{1}(V)} {S : Set V} (hS : IsCompact S)
    (hUS : ∀ᵐ x ∂volume, x ∉ S → toL2 U x = 0) {η : V → ℂ}
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hηc : HasCompactSupport η) (hη1 : ∫ x, η x = 1)
    (hΩ : ∀ᶠ n : ℕ in atTop, tsupport (dilate ((2 : ℝ) ^ n) η) + S ⊆ Ω) :
    U ∈ tildeSpace 1 Ω :=
  mem_tildeSpace_of_dilate_of_nonneg zero_le_one hS (by rwa [sobolevToL2_one]) hη hηc hη1 hΩ

/-- **Mollified functions with compact support in `Ω`**: for an open set `Ω`, every `U ∈ H^1(V)`
vanishing almost everywhere outside a compact subset `S` of `Ω` lies in `H̃^1(Ω)`, the case
`s = 1` of `Rd.mem_tildeSpace_of_isCompact_of_nonneg` (`Rd.sobolevToL2_one`). -/
theorem mem_tildeSpace_of_isCompact {Ω : Opens V} {U : H^{1}(V)} {S : Set V} (hS : IsCompact S)
    (hSΩ : S ⊆ Ω) (hUS : ∀ᵐ x ∂volume, x ∉ S → toL2 U x = 0) : U ∈ tildeSpace 1 Ω :=
  mem_tildeSpace_of_isCompact_of_nonneg zero_le_one hS hSΩ (by rwa [sobolevToL2_one])

/-- **The zero extension of the restriction**: for an open `Ω` and `U ∈ H^1(V)` vanishing almost
everywhere outside `Ω`, the zero extension of the `L_2` function of `U|_Ω ∈ H^1(Ω)` is `ι U`, since
`U|_Ω = U` almost everywhere on `Ω` (`Rd.sub_restrictProj_mem`, `Rd.mem_vanishOn_one_iff`). -/
theorem indicatorLp_toL2_restrictProj {Ω : Opens V} {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ (Ω : Set V) → toL2 U x = 0) :
    indicatorLp Ω.isOpen.measurableSet (toL2 (restrictProj 1 Ω U : H^{1}(V))) = toL2 U := by
  have h := (mem_vanishOn_one_iff _).1 (sub_restrictProj_mem (s := 1) (Ω := Ω) U)
  rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet] at h
  refine Lp.ext ?_
  filter_upwards [indicatorLp_apply_ae Ω.isOpen.measurableSet
    (toL2 (restrictProj 1 Ω U : H^{1}(V))), h, hU,
    Lp.coeFn_sub (toL2 U) (toL2 (restrictProj 1 Ω U : H^{1}(V)))] with x h1 h2 h3 h4
  rw [h1]
  by_cases hx : x ∈ (Ω : Set V)
  · have h5 := h2 hx
    rw [map_sub, h4, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h5
    rw [indicator_of_mem hx, h5]
  · rw [indicator_of_notMem hx, h3 hx]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The local lemma: chart pieces of functions vanishing outside `Ω` lie in `H̃^1(Ω)`**: let
`U ∈ H^1(V)` vanish almost everywhere outside `Ω`, and let `ζ` be a continuous bounded real
function with closed support in the boundary ball `B_j`. Every `W ∈ H^1(V)` with `ι W = ζ ι U`
lies in `H̃^1(Ω)`. This is the case `s = 1` of
`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart_of_nonneg` (`Rd.sobolevToL2_one`). -/
theorem mem_tildeSpace_of_mulLp_chart (j : Fin Ω.N) {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0) {ζ : V → ℝ}
    (hζ : tsupport ζ ⊆ ball (Ω.center j) (Ω.radius j)) {C : ℝ}
    (hc : Continuous fun x => (ζ x : ℂ)) (hC : ∀ x, ‖(ζ x : ℂ)‖ ≤ C) {W : H^{1}(V)}
    (hW : toL2 W = mulLp hc hC (toL2 U)) : W ∈ tildeSpace 1 Ω.toOpens :=
  Ω.mem_tildeSpace_of_mulLp_chart_of_nonneg zero_le_one j (by rwa [sobolevToL2_one]) hζ hc hC
    (by rwa [sobolevToL2_one])

/-- **The decomposition of a function vanishing outside `Ω`**: if `χ + ∑_j ψ_j = 1` on `Ω`,
`U ∈ H^1(V)` vanishes almost everywhere outside `Ω`, the `L_2` functions of `W_j` are `ψ_j ι U`
and that of `W_0` is `χ ι U`, then `U = ∑_j W_j + W_0` in `H^1(V)`. This is the case `s = 1` of
`Rd.BoundedLipschitzDomain.eq_sum_add_of_ae_eq_zero_of_nonneg` (`Rd.sobolevToL2_one`). -/
theorem eq_sum_add_of_ae_eq_zero (ψ : Ω.BoundaryPartition) {χ : V → ℝ}
    (hχ1 : ∀ x ∈ Ω.carrier, χ x + ∑ j, ψ.toFun j x = 1) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0)
    {Wj : Fin Ω.N → H^{1}(V)} (hWj : ∀ j, toL2 (Wj j) = ψ.localizeL2 j (toL2 U))
    {W0 : H^{1}(V)} (hW0 : toL2 W0 = mulLp hc hC (toL2 U)) : U = ∑ j, Wj j + W0 :=
  Ω.eq_sum_add_of_ae_eq_zero_of_nonneg zero_le_one ψ hχ1 hc hC (by rwa [sobolevToL2_one])
    (by rwa [sobolevToL2_one]) (by rwa [sobolevToL2_one])

/-- **Functions vanishing outside `Ω` lie in `H̃^1(Ω)`**: on a bounded Lipschitz domain, every
`U ∈ H^1(V)` whose `L_2` function vanishes almost everywhere outside `Ω` lies in the closure of the
test functions of `Ω`, the case `s = 1` of
`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_ae_eq_zero_of_nonneg` (`Rd.sobolevToL2_one`). -/
theorem mem_tildeSpace_of_ae_eq_zero {U : H^{1}(V)}
    (hU : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0) : U ∈ tildeSpace 1 Ω.toOpens :=
  Ω.mem_tildeSpace_of_ae_eq_zero_of_nonneg zero_le_one (by rwa [sobolevToL2_one])

/-- **`H̃^1(Ω)` is the space of `H^1(V)` functions vanishing outside `Ω`**: on a bounded Lipschitz
domain, `U ∈ H^1(V)` lies in `H̃^1(Ω)` iff its `L_2` function vanishes almost everywhere outside
`Ω`, the case `s = 1` of `Rd.BoundedLipschitzDomain.mem_tildeSpace_iff_of_nonneg`
(`Rd.sobolevToL2_one`). Since `Γ` is a null set (`Rd.BoundedLipschitzDomain.volume_frontier`),
this is `H̃^s(Ω) = H^s_{Ω̄}` of McLean (Theorem 3.29) for `s = 1`. -/
theorem mem_tildeSpace_iff (U : H^{1}(V)) :
    U ∈ tildeSpace 1 Ω.toOpens ↔ ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0 := by
  rw [Ω.mem_tildeSpace_iff_of_nonneg zero_le_one, sobolevToL2_one]

/-! ### `H^s_0(Ω) ⊆ ker γ_s` and `ker γ = H^1_0(Ω)` -/

/-- **Test functions have zero boundary trace**: on a bounded Lipschitz domain, for every
`s ≥ 0` and every test function `φ` of `Ω`, the boundary trace of `ι_s φ` vanishes almost
everywhere on `Γ`. For every `s ≥ 0`, `ι_s φ` is the continuous function `φ`
(`Rd.ofTest_eq_ofSchwartz`, `Rd.sobolevToL2_ofSchwartz`), the same `L_2` function as at the level
`1`, where its differences of order `2` have a finite quasi-norm with weight `1`
(`Rd.modNorm_sobolevToL2_lt_top`). So its boundary trace is its restriction to `Γ`
(`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq_of_continuous`), which vanishes: `φ` has
closed support in the open set `Ω`, and `Γ` does not meet `Ω`. -/
theorem boundaryTrace_sobolevToL2_ofTest (ψ : Ω.BoundaryPartition) {s : ℝ} (hs : 0 ≤ s)
    (φ : 𝓓(Ω.toOpens, ℝ)) :
    Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 hs (ofTest s φ)) =ᶠ[Ω.aeBoundary] 0 := by
  have h1 : sobolevToL2 hs (ofTest s φ) = sobolevToL2 zero_le_one (ofTest 1 φ) := by
    rw [ofTest_eq_ofSchwartz, ofTest_eq_ofSchwartz, sobolevToL2_ofSchwartz,
      sobolevToL2_ofSchwartz]
  have hFG : (sobolevToL2 zero_le_one (ofTest 1 φ) : V → ℂ) =ᵐ[volume] testSchwartz φ := by
    rw [ofTest_eq_ofSchwartz, sobolevToL2_ofSchwartz]
    exact (testSchwartz φ).coeFn_toLp 2 volume
  rw [h1]
  refine (Ω.boundaryTrace_eventuallyEq_of_continuous ψ two_ne_top one_le_two
    (sub_pos.2 one_half_lt_one) (by norm_num) one_le_two
    (modNorm_sobolevToL2_lt_top one_half_lt_one (by norm_num) _)
    (testSchwartz φ).continuous hFG).trans ?_
  filter_upwards [Ω.ae_surfaceMeasure_iff_aeBoundary.1 Ω.ae_mem_frontier] with y hy
  rw [Ω.isOpen.frontier_eq] at hy
  rw [testSchwartz_apply, image_eq_zero_of_notMem_tsupport fun h => hy.2 (φ.tsupport_subset h),
    Complex.ofReal_zero, Pi.zero_apply]

/-- **`H^s_0(Ω) ⊆ ker γ_s`**, `1/2 < s < 3/2`: the trace kernel is closed
(`Rd.BoundedLipschitzDomain.isClosed_traceKer`, Mathlib's
`Submodule.topologicalClosure_minimal`), so it suffices that it contains the restrictions of the
test functions of `Ω`, whose closure is `H^s_0(Ω)`. The restriction keeps the boundary trace
(`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`), and the boundary trace of a test
function vanishes (`Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_ofTest`). -/
theorem zeroBoundarySpace_le_traceKer (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : zeroBoundarySpace s Ω.toOpens ≤ Ω.traceKer s hs hs' := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Ω.isClosed_traceKer s hs hs')
  rw [Submodule.map_le_iff_le_comap, testSpan, Submodule.span_le]
  rintro _ ⟨φ, rfl⟩
  change restrictProj s Ω.toOpens (ofTest s φ) ∈ Ω.traceKer s hs hs'
  rw [Ω.mem_traceKer_iff Ω.boundaryPartition s _ hs hs']
  exact (Ω.boundaryTrace_restrictProj Ω.boundaryPartition s _ hs hs').trans
    (Ω.boundaryTrace_sobolevToL2_ofTest Ω.boundaryPartition (one_half_pos.trans hs).le φ)

/-- **`ker γ ⊆ H^1_0(Ω)`**: for `u` in the trace kernel, the zero extension `1_Ω ι u` is the `L_2`
function of some `U ∈ H^1(V)` (`Rd.BoundedLipschitzDomain.memWSobolev_indicatorLp_of_mem_traceKer`,
`Rd.exists_toL2_eq_of_memWSobolev`). `U` vanishes outside `Ω`, so `U ∈ H̃^1(Ω)`
(`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_ae_eq_zero`), and `u = U|_Ω`
(`Rd.restrictProj_eq_of_ae_eq`) lies in `H^1_0(Ω)` (`Rd.range_tildeToRestriction`). -/
theorem traceKer_one_le_zeroBoundarySpace : Ω.traceKer 1 ≤ zeroBoundarySpace 1 Ω.toOpens := by
  intro u hu
  obtain ⟨U, hU⟩ := exists_toL2_eq_of_memWSobolev (Ω.memWSobolev_indicatorLp_of_mem_traceKer hu)
  have hUae : (toL2 U : V → ℂ) =ᵐ[volume] Ω.carrier.indicator (toL2 (u : H^{1}(V))) := by
    rw [hU]
    exact indicatorLp_apply_ae _ _
  have hU0 : ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0 := by
    filter_upwards [hUae] with x hx hxΩ
    rw [hx, indicator_of_notMem hxΩ]
  have hUu : (toL2 U : V → ℂ) =ᵐ[volume.restrict (Ω.toOpens : Set V)] toL2 (u : H^{1}(V)) := by
    rw [Ω.coe_toOpens]
    filter_upwards [ae_restrict_of_ae hUae, ae_restrict_mem Ω.measurableSet] with x hx hxΩ
    rw [hx, indicator_of_mem hxΩ]
  rw [← restrictProj_eq_of_ae_eq hUu, ← range_tildeToRestriction]
  exact ⟨⟨U, Ω.mem_tildeSpace_of_ae_eq_zero hU0⟩, rfl⟩

/-- **`ker γ = H^1_0(Ω)`** on a bounded Lipschitz domain (McLean, Theorem 3.40; Hiptmair, Pauly
and Schulz cite it for `ker γ = H^1_0(Ω)`), for the trace kernel `Ω.traceKer 1` of `H^1(Ω)`: the
elements of `H^1(Ω)` whose chart traces all vanish, equivalently whose boundary trace vanishes
almost everywhere on `Γ` (`Rd.BoundedLipschitzDomain.mem_traceKer_one_iff`), are exactly the
limits in `H^1(Ω)` of test functions of `Ω`
(`Rd.BoundedLipschitzDomain.zeroBoundarySpace_le_traceKer`,
`Rd.BoundedLipschitzDomain.traceKer_one_le_zeroBoundarySpace`). -/
theorem traceKer_one_eq_zeroBoundarySpace : Ω.traceKer 1 = zeroBoundarySpace 1 Ω.toOpens :=
  le_antisymm Ω.traceKer_one_le_zeroBoundarySpace (Ω.zeroBoundarySpace_le_traceKer 1)

/-! ### `H̃^1(Ω) ≅ ker γ` and the dual of `ker γ` -/

/-- **`H̃^1(Ω) ≅ ker γ` isometrically**: restriction is an isometry of `H̃^1(Ω)` onto
`H^1_0(Ω) = ker γ` (`Rd.tildeEquivZeroBoundary`,
`Rd.BoundedLipschitzDomain.traceKer_one_eq_zeroBoundarySpace`). -/
noncomputable def tildeEquivTraceKer : tildeSpace 1 Ω.toOpens ≃ₗᵢ[ℂ] Ω.traceKer 1 :=
  (tildeEquivZeroBoundary Ω.toOpens).trans
    (LinearIsometryEquiv.ofEq _ _ Ω.traceKer_one_eq_zeroBoundarySpace.symm)

/-- `tildeEquivTraceKer Ω U` is the restriction of `U` to `Ω`. -/
theorem coe_tildeEquivTraceKer_apply (U : tildeSpace 1 Ω.toOpens) :
    (Ω.tildeEquivTraceKer U : Ω.SobolevOne) = restrictProj 1 Ω.toOpens U :=
  rfl

/-- **The element of `H̃^1(Ω)` with restriction `u ∈ ker γ` is `u` itself**, read in `H^1(V)`
(`Rd.coe_tildeEquivZeroBoundary_symm_apply`). -/
theorem coe_tildeEquivTraceKer_symm_apply (u : Ω.traceKer 1) :
    ((Ω.tildeEquivTraceKer.symm u : tildeSpace 1 Ω.toOpens) : H^{1}(V)) =
      ((u : Ω.SobolevOne) : H^{1}(V)) := by
  rw [tildeEquivTraceKer, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.ofEq_symm,
    coe_tildeEquivZeroBoundary_symm_apply, LinearIsometryEquiv.coe_ofEq_apply]

/-- **The dual of `ker γ` is `H^{-1}(Ω)`**: every bounded functional `ℓ` on the trace kernel is
`u ↦ [W, u]` for exactly one `W ∈ H^{-1}(Ω)`, with `‖W‖ = ‖ℓ‖`
(`Rd.BoundedLipschitzDomain.dualTraceKerEquiv_apply`,
`Rd.BoundedLipschitzDomain.dualTraceKerEquiv_eq_iff`); Riesz on `ker γ`, the isometry
`Rd.BoundedLipschitzDomain.tildeEquivTraceKer` and the duality `H̃^1(Ω) ≅ H^{-1}(Ω)`
(`Rd.tildeEquivRestriction`), as for `Rd.dualZeroBoundaryEquiv`. -/
noncomputable def dualTraceKerEquiv :
    StrongDual ℂ (Ω.traceKer 1) ≃ₗᵢ⋆[ℂ] RestrictionSpace (-1) Ω.toOpens :=
  (InnerProductSpace.toDual ℂ (Ω.traceKer 1)).symm.trans
    (Ω.tildeEquivTraceKer.symm.trans (tildeEquivRestriction 1 Ω.toOpens))

/-- **`ℓ` is the pairing with `dualTraceKerEquiv Ω ℓ`**: `ℓ(u) = [W, u]` for
`W = dualTraceKerEquiv Ω ℓ` and every `u ∈ ker γ`, read as an element of `H^1(V)`. -/
theorem dualTraceKerEquiv_apply (ℓ : StrongDual ℂ (Ω.traceKer 1)) (u : Ω.traceKer 1) :
    ℓ u = sobolevPairing 1 (Ω.dualTraceKerEquiv ℓ : H^{-1}(V)) ((u : Ω.SobolevOne) : H^{1}(V)) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := Ω.traceKer 1) (x := u) (y := ℓ)
  rw [← h, ← LinearIsometryEquiv.inner_map_map Ω.tildeEquivTraceKer.symm,
    Submodule.coe_inner, dualTraceKerEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, coe_tildeEquivRestriction_apply, sobolevPairing_besselShift,
    Ω.coe_tildeEquivTraceKer_symm_apply u]

/-- The functional of `W ∈ H^{-1}(Ω)` on `ker γ` is `u ↦ [W, u]`. -/
theorem dualTraceKerEquiv_symm_apply (W : RestrictionSpace (-1) Ω.toOpens) (u : Ω.traceKer 1) :
    Ω.dualTraceKerEquiv.symm W u =
      sobolevPairing 1 (W : H^{-1}(V)) ((u : Ω.SobolevOne) : H^{1}(V)) := by
  rw [dualTraceKerEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualTraceKerEquiv Ω ℓ = W` iff
`ℓ(u) = [W, u]` for every `u ∈ ker γ`. -/
theorem dualTraceKerEquiv_eq_iff (ℓ : StrongDual ℂ (Ω.traceKer 1))
    (W : RestrictionSpace (-1) Ω.toOpens) :
    Ω.dualTraceKerEquiv ℓ = W ↔ ∀ u : Ω.traceKer 1,
      ℓ u = sobolevPairing 1 (W : H^{-1}(V)) ((u : Ω.SobolevOne) : H^{1}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualTraceKerEquiv_symm_apply]

/-! ### `ker γ_s = H^s_0(Ω)` for `1/2 < s ≤ 1` -/

/-- **The trace of `H^s(V)` in `L_2(Γ)` commutes with the inclusions**, `1/2 < t ≤ s < 3/2`:
`T^t_Γ(ι_{t,s} U) = T^s_Γ U` for every `U ∈ H^s(V)`, since `ι_t(ι_{t,s} U) = ι_s U`
(`Rd.sobolevToL2_sobolevInclusion`) and both traces are the boundary trace of this `L_2` function
(`Rd.BoundedLipschitzDomain.ambientTraceL2_apply_ae`). -/
theorem ambientTraceL2_sobolevInclusion {s t : ℝ} (ht : 1 / 2 < t) (hts : t ≤ s)
    (hs' : s < 3 / 2) (U : H^{s}(V)) :
    Ω.ambientTraceL2 t ht (hts.trans_lt hs') (sobolevInclusion hts U) =
      Ω.ambientTraceL2 s (ht.trans_le hts) hs' U := by
  refine Lp.ext ((Ω.ambientTraceL2_apply_ae Ω.boundaryPartition t _ ht _).trans ?_)
  rw [sobolevToL2_sobolevInclusion]
  exact (Ω.ambientTraceL2_apply_ae Ω.boundaryPartition s U _ hs').symm

/-- **The inclusions keep the trace kernel**, `1/2 < t ≤ s < 3/2`: if `u ∈ ker γ_s`, then
`ι^Ω_{t,s} u = (ι_{t,s} u)|_Ω ∈ ker γ_t`. The restriction keeps the boundary trace
(`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`), and `ι_t(ι_{t,s} u) = ι_s u`
(`Rd.sobolevToL2_sobolevInclusion`). -/
theorem restrictionInclusion_mem_traceKer {s t : ℝ} (ht : 1 / 2 < t) (hts : t ≤ s)
    (hs' : s < 3 / 2) {u : RestrictionSpace s Ω.toOpens}
    (hu : u ∈ Ω.traceKer s (ht.trans_le hts) hs') :
    restrictionInclusion hts Ω.toOpens u ∈ Ω.traceKer t ht (hts.trans_lt hs') := by
  rw [Ω.mem_traceKer_iff Ω.boundaryPartition s u _ hs'] at hu
  rw [Ω.mem_traceKer_iff Ω.boundaryPartition t _ ht (hts.trans_lt hs'),
    restrictionInclusion_apply]
  refine (Ω.boundaryTrace_restrictProj Ω.boundaryPartition t _ ht (hts.trans_lt hs')).trans ?_
  rw [sobolevToL2_sobolevInclusion]
  exact hu

/-- **The extension from the boundary maps `B^{s-1/2}_{2,2}(Γ)` into `H^s(V)`**, `1/2 < s < 3/2`:
for every `g ∈ L_2(Γ)` in `B^{s-1/2}_{2,2}(Γ)`, the extension `E_Γ g`
(`Rd.BoundedLipschitzDomain.besovExtendLp`) is `ι_s W` for some `W ∈ H^s(V)`. Its quasi-norm with
differences of order `2` and weight `(s - 1/2) + 1/2 = s` is finite
(`Rd.BoundedLipschitzDomain.modNorm_besovExtendLp_lt_top`), and such functions come from
`H^s(V)` (`Rd.exists_sobolevToL2_eq_of_modNorm_lt_top`). -/
theorem exists_sobolevToL2_eq_besovExtendLp (s : ℝ) {g : Ω.BoundaryL2}
    (hg : Ω.MemBoundaryBesov 2 Ω.boundaryPartition (s - 1 / 2) 2 g)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ W : H^{s}(V), sobolevToL2 (one_half_pos.trans hs).le W = Ω.besovExtendLp two_ne_top g := by
  have hF := Ω.modNorm_besovExtendLp_lt_top two_ne_top (sub_pos.2 hs) (by linarith) one_le_two
    hg
  have hσ : s - 1 / 2 + 1 / (2 : ℝ≥0∞).toReal = s := by norm_num
  rw [hσ] at hF
  exact exists_sobolevToL2_eq_of_modNorm_lt_top (one_half_pos.trans hs) (r := 2)
    (by norm_num; linarith) hF

/-- **The extension from the boundary is bounded into `H^s(V)`**, `1/2 < s < 3/2`: there is
`C < ∞` with `‖W‖ ≤ C ‖g‖_{B^{s-1/2}_{2,2}(Γ)}` for every `g ∈ L_2(Γ)` in `B^{s-1/2}_{2,2}(Γ)`
and every `W ∈ H^s(V)` with `ι_s W = E_Γ g`: the bound of the extension
(`Rd.BoundedLipschitzDomain.exists_modNorm_besovExtendLp_le`) and the bound of `H^s(V)` by
differences of order `2` (`Rd.enorm_le_modNorm_sobolevToL2`). -/
theorem exists_enorm_le_of_sobolevToL2_eq_besovExtendLp (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundaryL2,
      Ω.MemBoundaryBesov 2 Ω.boundaryPartition (s - 1 / 2) 2 g → ∀ W : H^{s}(V),
        sobolevToL2 (one_half_pos.trans hs).le W = Ω.besovExtendLp two_ne_top g →
          ‖W‖ₑ ≤ C * Ω.boundaryBesovNorm 2 Ω.boundaryPartition (s - 1 / 2) 2 g := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_modNorm_besovExtendLp_le two_ne_top (sub_pos.2 hs)
    (by linarith) one_le_two
  refine ⟨sobolevBesovInvConst V s 2 * C,
    ENNReal.mul_ne_top (sobolevBesovInvConst_ne_top s 2) hC, fun g hg W hW => ?_⟩
  have h := hle g hg
  have hσ : s - 1 / 2 + 1 / (2 : ℝ≥0∞).toReal = s := by norm_num
  rw [hσ, ← hW] at h
  rw [mul_assoc]
  exact (enorm_le_modNorm_sobolevToL2 (one_half_pos.trans hs).le 2 W).trans
    (mul_le_mul' le_rfl h)

/-- **A function minus the extension of its trace has zero trace**, `1/2 < s < 3/2`: for
`U ∈ H^s(V)` and every `W ∈ H^s(V)` with `ι_s W = E_Γ(T^s_Γ U)`, `(U - W)|_Ω ∈ ker γ_s`. Almost
everywhere on `Γ`, `Tr_Γ ι_s(U - W) = Tr_Γ ι_s U - Tr_Γ E_Γ(T^s_Γ U) = T^s_Γ U - T^s_Γ U = 0`
(`Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_sub`,
`Rd.BoundedLipschitzDomain.boundaryTrace_besovExtendLp`,
`Rd.BoundedLipschitzDomain.memBoundaryBesov_ambientTraceL2`), and the restriction keeps the
boundary trace (`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`). -/
theorem restrictProj_sub_mem_traceKer (s : ℝ) (hs : 1 / 2 < s) (hs' : s < 3 / 2)
    {U W : H^{s}(V)} (hW : sobolevToL2 (one_half_pos.trans hs).le W =
      Ω.besovExtendLp two_ne_top (Ω.ambientTraceL2 s hs hs' U)) :
    restrictProj s Ω.toOpens (U - W) ∈ Ω.traceKer s hs hs' := by
  have hg := Ω.memBoundaryBesov_ambientTraceL2 Ω.boundaryPartition s U hs hs'
  have hE := Ω.boundaryTrace_besovExtendLp two_ne_top (sub_pos.2 hs) (by linarith) one_le_two hg
  rw [← hW] at hE
  have hU := Ω.ae_surfaceMeasure_iff_aeBoundary.1
    (Ω.ambientTraceL2_apply_ae Ω.boundaryPartition s U hs hs')
  rw [Ω.mem_traceKer_iff Ω.boundaryPartition s _ hs hs']
  filter_upwards [Ω.boundaryTrace_restrictProj Ω.boundaryPartition s (U - W) hs hs',
    Ω.boundaryTrace_sobolevToL2_sub Ω.boundaryPartition s U W hs hs', hU, hE] with y h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, ← h3, h4, sub_self, Pi.zero_apply]

/-- **Approximation of `ker γ_s` by `H^s_0(Ω)` with a bound**, `1/2 < s ≤ 1`: there is `K < ∞`
such that for every `u ∈ ker γ_s` and every `W' ∈ H^1(V)` some `y ∈ H^s_0(Ω)` has
`‖y - u‖ ≤ K ‖ι_{s,1} W' - u‖`. Let `g = T^1_Γ W'` and `W ∈ H^1(V)` with `ι_1 W = E_Γ g`
(`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_besovExtendLp` at `s = 1`). The correction
`(W' - W)|_Ω` lies in `ker γ_1 = H^1_0(Ω)`
(`Rd.BoundedLipschitzDomain.restrictProj_sub_mem_traceKer`,
`Rd.BoundedLipschitzDomain.traceKer_one_eq_zeroBoundarySpace`), so `y = ι^Ω_{s,1}((W' - W)|_Ω)`
lies in `H^s_0(Ω)` (`Rd.restrictionInclusion_mem_zeroBoundarySpace`), and
`y - u = (ι_{s,1} W' - u - ι_{s,1} W)|_Ω`. Since `T^s_Γ u = 0`, `g = T^s_Γ(ι_{s,1} W' - u)`
(`Rd.BoundedLipschitzDomain.ambientTraceL2_sobolevInclusion`), so
`‖g‖_{B^{s-1/2}_{2,2}(Γ)} ≤ C_tr ‖ι_{s,1} W' - u‖`
(`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_sobolevToL2_le`); `ι_{s,1} W` has the
`L_2` function `E_Γ g` as well, so `‖ι_{s,1} W‖ ≤ C_E ‖g‖_{B^{s-1/2}_{2,2}(Γ)}`
(`Rd.BoundedLipschitzDomain.exists_enorm_le_of_sobolevToL2_eq_besovExtendLp`). The one function
`E_Γ g` serves the levels `1` and `s`; `K = 1 + C_E C_tr`. -/
theorem exists_mem_zeroBoundarySpace_enorm_sub_le (s : ℝ) (hs : 1 / 2 < s) (hs1 : s ≤ 1) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ u ∈ Ω.traceKer s hs (by linarith), ∀ W' : H^{1}(V),
      ∃ y ∈ zeroBoundarySpace s Ω.toOpens,
        ‖y - u‖ₑ ≤ K * ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ₑ := by
  have hs' : s < 3 / 2 := by linarith
  obtain ⟨Ct, hCt, htr⟩ := Ω.exists_boundaryBesovNorm_sobolevToL2_le Ω.boundaryPartition s hs hs'
  obtain ⟨CE, hCE, hext⟩ := Ω.exists_enorm_le_of_sobolevToL2_eq_besovExtendLp s hs hs'
  refine ⟨1 + CE * Ct, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hCE hCt⟩,
    fun u hu W' => ?_⟩
  obtain ⟨W, hW⟩ := Ω.exists_sobolevToL2_eq_besovExtendLp 1
    (Ω.memBoundaryBesov_ambientTraceL2 Ω.boundaryPartition 1 W')
  have hy := Ω.restrictProj_sub_mem_traceKer 1 (by norm_num) (by norm_num) hW
  rw [Ω.traceKer_one_eq_zeroBoundarySpace] at hy
  refine ⟨restrictionInclusion hs1 Ω.toOpens (restrictProj 1 Ω.toOpens (W' - W)),
    restrictionInclusion_mem_zeroBoundarySpace hs1 hy, ?_⟩
  have hTD : Ω.ambientTraceL2 s hs hs' (sobolevInclusion hs1 W' - (u : H^{s}(V))) =
      Ω.ambientTraceL2 1 (by norm_num) (by norm_num) W' := by
    rw [map_sub, Ω.ambientTraceL2_eq_zero_of_mem_traceKer s hs hs' hu, sub_zero]
    exact Ω.ambientTraceL2_sobolevInclusion hs hs1 (by norm_num) W'
  have hgB : Ω.MemBoundaryBesov 2 Ω.boundaryPartition (s - 1 / 2) 2
      (Ω.ambientTraceL2 1 (by norm_num) (by norm_num) W') := by
    rw [← hTD]
    exact Ω.memBoundaryBesov_ambientTraceL2 Ω.boundaryPartition s _ hs hs'
  have hgN : Ω.boundaryBesovNorm 2 Ω.boundaryPartition (s - 1 / 2) 2
      (Ω.ambientTraceL2 1 (by norm_num) (by norm_num) W') ≤
        Ct * ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ₑ := by
    rw [← hTD, Ω.boundaryBesovNorm_congr _ (Ω.ae_surfaceMeasure_iff_aeBoundary.1
      (Ω.ambientTraceL2_apply_ae Ω.boundaryPartition s _ hs hs'))]
    exact htr _
  have hWs : ‖sobolevInclusion hs1 W‖ₑ ≤
      CE * (Ct * ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ₑ) := by
    refine (hext _ hgB (sobolevInclusion hs1 W) ?_).trans (mul_le_mul' le_rfl hgN)
    rw [sobolevToL2_sobolevInclusion]
    exact hW
  have hyu : restrictionInclusion hs1 Ω.toOpens (restrictProj 1 Ω.toOpens (W' - W)) - u =
      restrictProj s Ω.toOpens
        (sobolevInclusion hs1 W' - (u : H^{s}(V)) - sobolevInclusion hs1 W) := by
    have h1 : sobolevInclusion hs1 W' - (u : H^{s}(V)) - sobolevInclusion hs1 W =
        sobolevInclusion hs1 (W' - W) - (u : H^{s}(V)) := by
      rw [map_sub (sobolevInclusion hs1) W' W]
      abel
    rw [restrictionInclusion_restrictProj, h1,
      map_sub (restrictProj s Ω.toOpens) (sobolevInclusion hs1 (W' - W)), restrictProj_coe]
  rw [hyu]
  calc _ ≤ ‖sobolevInclusion hs1 W' - (u : H^{s}(V)) - sobolevInclusion hs1 W‖ₑ :=
        enorm_le_iff_norm_le.2 (norm_restrictProj_apply_le _)
    _ ≤ ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ₑ + ‖sobolevInclusion hs1 W‖ₑ := enorm_sub_le
    _ ≤ ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ₑ +
        CE * (Ct * ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ₑ) := add_le_add le_rfl hWs
    _ = (1 + CE * Ct) * ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ₑ := by ring

/-- **`ker γ_s ⊆ H^s_0(Ω)`** for `1/2 < s ≤ 1` (McLean, Theorem 3.40): every `u ∈ ker γ_s` lies in
the closure of `H^s_0(Ω)`, which is closed. For `ε > 0` the inclusion `H^1(V) ⊆ H^s(V)` has
dense range (`Rd.denseRange_sobolevInclusion`), so some `W' ∈ H^1(V)` has
`K ‖ι_{s,1} W' - u‖ < ε`, and
`Rd.BoundedLipschitzDomain.exists_mem_zeroBoundarySpace_enorm_sub_le` gives `y ∈ H^s_0(Ω)`
within `ε` of `u`. -/
theorem traceKer_le_zeroBoundarySpace_of_le_one (s : ℝ) (hs : 1 / 2 < s) (hs1 : s ≤ 1) :
    Ω.traceKer s hs (by linarith) ≤ zeroBoundarySpace s Ω.toOpens := by
  obtain ⟨K, hK, hle⟩ := Ω.exists_mem_zeroBoundarySpace_enorm_sub_le s hs hs1
  intro u hu
  rw [← SetLike.mem_coe, ← (isClosed_zeroBoundarySpace s Ω.toOpens).closure_eq,
    Metric.mem_closure_iff]
  intro ε hε
  have hK1 : (0 : ℝ) < K.toReal + 1 := by positivity
  obtain ⟨W', hW'⟩ := (denseRange_sobolevInclusion (V := V) hs1).exists_dist_lt
    (u : H^{s}(V)) (div_pos hε hK1)
  obtain ⟨y, hy, hyle⟩ := hle u hu W'
  refine ⟨y, hy, ?_⟩
  have h1 : ‖y - u‖ ≤ K.toReal * ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hK enorm_ne_top) hyle
    rwa [ENNReal.toReal_mul, toReal_enorm, toReal_enorm] at h
  have h2 : ‖sobolevInclusion hs1 W' - (u : H^{s}(V))‖ < ε / (K.toReal + 1) := by
    rw [← dist_eq_norm, dist_comm]
    exact hW'
  rw [dist_eq_norm, norm_sub_rev]
  calc ‖y - u‖ ≤ K.toReal * (ε / (K.toReal + 1)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2.le ENNReal.toReal_nonneg)
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hK1]
      nlinarith [ENNReal.toReal_nonneg (a := K)]

/-- **`ker γ_s = H^s_0(Ω)`** for `1/2 < s ≤ 1` on a bounded Lipschitz domain (McLean,
Theorem 3.40, applied in this range by Hewett–Moiola, Remark 2.6): the elements of `H^s(Ω)`
whose boundary trace vanishes almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff`) are exactly the limits in `H^s(Ω)` of restricted
test functions of `Ω` (`Rd.BoundedLipschitzDomain.zeroBoundarySpace_le_traceKer`,
`Rd.BoundedLipschitzDomain.traceKer_le_zeroBoundarySpace_of_le_one`). At `s = 1` this is
`Rd.BoundedLipschitzDomain.traceKer_one_eq_zeroBoundarySpace`. -/
theorem traceKer_eq_zeroBoundarySpace_of_le_one (s : ℝ) (hs : 1 / 2 < s) (hs1 : s ≤ 1) :
    Ω.traceKer s hs (by linarith) = zeroBoundarySpace s Ω.toOpens :=
  le_antisymm (Ω.traceKer_le_zeroBoundarySpace_of_le_one s hs hs1)
    (Ω.zeroBoundarySpace_le_traceKer s hs _)

end BoundedLipschitzDomain

end Rd
