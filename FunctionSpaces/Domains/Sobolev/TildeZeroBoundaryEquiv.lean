/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Lipschitz.GraphHardy
public import FunctionSpaces.Domains.Sobolev.SobolevZeroExtension

/-!
# `H̃^s(Ω) ≅ H^s_0(Ω)` for `s ≥ 0`, `s ∉ 1/2 + ℕ_0`

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
and `Ω ⊆ V` a bounded Lipschitz domain. The first part treats `1/2 < s < 1`. Write `ι_s U` for
the `L_2` function of `U ∈ H^s(V)` (`Rd.sobolevToL2`) and
`N_s(F) = ‖F‖_2 + ‖(2^(ks) ω_1(F, 2^(-k))_2)_k‖_{ℓ_2}` for the `B^s_{2,2}` quantity of first
differences, equivalent to the norm of `H^s(V)` on the `L_2` functions
(`Rd.modNorm_sobolevToL2_le`, `Rd.enorm_le_modNorm_sobolevToL2`).

* **The zero extension bound**
  (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_half_lt`): there is `C` with
  `‖U‖ ≤ C ‖U + W‖` for every `U` in the span `T^s(Ω)` of the test functions and every `W`
  vanishing on `Ω`, so restriction is an isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)`
  (`Rd.HasZeroExtensionBound.tildeEquivZeroBoundaryOfBound`; McLean, Theorem 3.33; Hewett–Moiola,
  Lemma 2.1). With `Φ = ι_s(U + W)`, `ι_s U = 1_Ω Φ` (`Rd.sobolevToL2_eq_indicatorLp_add`).
* **The decomposition** (`Rd.BoundedLipschitzDomain.indicatorLp_eq_sum_add`): for a resolution of
  unity `ψ` and an interior cut-off `χ` with `χ + ∑_j ψ_j = 1` on `Ω`,
  `1_Ω Φ = ∑_j 1_{Ω_j}(ψ_j Φ) + χ Φ`, with the graph domains `Ω_j` of the charts, since `Ω` and
  `Ω_j` agree on the chart ball that carries `ψ_j`.
* **Vanishing near the graphs.** The `L_2` function of `U + W` vanishes on `Ω` outside a compact
  subset of `Ω` (`Rd.BoundedLipschitzDomain.exists_isCompact_sobolevToL2_add_eq_zero`, from the
  Schwartz function of `U`), so each `ψ_j Φ` vanishes on the points of `Ω_j` of small height above
  the graph (`Rd.BoundedLipschitzDomain.exists_mul_eq_zero_of_graphHeight_lt`): the point straight
  below such a point on the graph is close to it, inside the chart ball and outside `Ω`.

The extension by zero from each graph domain
(`Rd.LipschitzGraph.exists_modNorm_indicatorLp_le_of_vanish`, which rests on the Hardy inequality
and needs `s > 1/2`) and the smooth multipliers `ψ_j` and `χ` (`Rd.exists_mul_modNorm_le`, which
needs `s < 1` for first differences) bound `N_s(ι_s U)` by a multiple of `N_s(Φ)`.

**All admissible `s`.** Let `s ≥ 0` with `s - 1/2 ∉ ℕ_0`. The zero extension bound at
`s - ⌊s⌋ ∈ [0, 1/2) ∪ (1/2, 1)` (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_lt_one`,
from `Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_lt_half` and the bound above),
lifted `⌊s⌋` times with the same constant (`Rd.HasZeroExtensionBound.add_natCast`), gives the bound
at `s` (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound`), so restriction is an
isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)`
(`Rd.BoundedLipschitzDomain.tildeEquivZeroBoundaryOfNeHalf`; McLean, Theorem 3.33; the case of
bounded `Ω` and `s ≥ 0` of Hewett–Moiola, Lemma 2.1).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology TopologicalSpace Set
open scoped ENNReal BesselPotentialSpace SchwartzMap

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {s : ℝ}

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The cut-off by the charts**: for a resolution of unity `ψ` and a real function `χ` with
`χ = 0` outside `Ω` and `χ + ∑_j ψ_j = 1` on `Ω`, every `Φ ∈ L_2(V)` satisfies
`1_Ω Φ = ∑_j 1_{Ω_j} G_j + G_0` whenever `G_j = ψ_j Φ` and `G_0 = χ Φ` almost everywhere, with the
graph domains `Ω_j` of the charts. Where `ψ_j ≠ 0` the point lies in the chart ball `B_j`, on which
membership in `Ω` is membership in `Ω_j` (`Rd.BoundedLipschitzDomain.mem_carrier_iff_of_mem_ball`);
outside `Ω` the cut-off `χ` vanishes. -/
theorem indicatorLp_eq_sum_add (ψ : Ω.BoundaryPartition) {χ : V → ℝ}
    (hχΩ : Function.support χ ⊆ Ω.carrier) (hχ1 : ∀ x ∈ Ω.carrier, χ x + ∑ j, ψ.toFun j x = 1)
    {Φ : Lp ℂ 2 (volume : Measure V)} {G : Fin Ω.N → Lp ℂ 2 (volume : Measure V)}
    (hG : ∀ j, (G j : V → ℂ) =ᵐ[volume] fun x => ψ.toComplex j x * Φ x)
    {G₀ : Lp ℂ 2 (volume : Measure V)} (hG₀ : (G₀ : V → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) * Φ x) :
    indicatorLp Ω.measurableSet Φ =
      ∑ j, indicatorLp (Ω.graph j).measurableSet_domain (G j) + G₀ := by
  have hB : ∀ j x, ψ.toFun j x ≠ 0 → (x ∈ Ω.carrier ↔ x ∈ (Ω.graph j).domain) := fun j x hψ =>
    Ω.mem_carrier_iff_of_mem_ball (ψ.mem_ball_of_ne_zero hψ)
  have hj : ∀ᵐ x ∂(volume : Measure V), ∀ j,
      (indicatorLp (Ω.graph j).measurableSet_domain (G j) : V → ℂ) x =
        (Ω.graph j).domain.indicator (fun x => ψ.toComplex j x * Φ x) x :=
    ae_all_iff.2 fun j => by
      filter_upwards [indicatorLp_apply_ae (Ω.graph j).measurableSet_domain (G j), hG j]
        with x h1 h2
      rw [h1]
      by_cases hx : x ∈ (Ω.graph j).domain
      · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  refine Lp.ext ?_
  filter_upwards [indicatorLp_apply_ae Ω.measurableSet Φ, hj, hG₀,
    Lp.coeFn_add (∑ j, indicatorLp (Ω.graph j).measurableSet_domain (G j)) G₀,
    Lp.coeFn_fun_finsetSum Finset.univ fun j => indicatorLp (Ω.graph j).measurableSet_domain (G j)]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h5, h3]
  simp only [h2]
  by_cases hx : x ∈ Ω.carrier
  · have hterm : ∀ j, (Ω.graph j).domain.indicator (fun x => ψ.toComplex j x * Φ x) x =
        ψ.toComplex j x * Φ x := fun j => by
      by_cases hψ : ψ.toFun j x = 0
      · rw [ψ.toComplex_of_eq_zero hψ, zero_mul, indicator_apply_eq_zero]
        exact fun _ => by rw [ψ.toComplex_of_eq_zero hψ, zero_mul]
      · exact indicator_of_mem ((hB j x hψ).1 hx) _
    rw [indicator_of_mem hx]
    simp only [hterm]
    rw [← Finset.sum_mul, ← add_mul]
    have h6 : ∑ j, ψ.toComplex j x + (χ x : ℂ) = 1 := by
      simp only [BoundaryPartition.toComplex]
      rw [← Complex.ofReal_sum, ← Complex.ofReal_add, add_comm, hχ1 x hx, Complex.ofReal_one]
    rw [h6, one_mul]
  · rw [indicator_of_notMem hx, Function.notMem_support.1 (fun h => hx (hχΩ h)),
      Complex.ofReal_zero, zero_mul, add_zero]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    by_cases hψ : ψ.toFun j x = 0
    · rw [indicator_apply_eq_zero]
      exact fun _ => by rw [ψ.toComplex_of_eq_zero hψ, zero_mul]
    · exact indicator_of_notMem (fun h => hx ((hB j x hψ).2 h)) _

/-- **Extensions of test functions vanish on `Ω` outside a compact set**: for `s ≥ 0`, `U` in the
span `T^s(Ω)` of the test functions and `W` vanishing on `Ω`, there is a compact `K ⊆ Ω` with
`ι_s(U + W) = 0` almost everywhere on `Ω \ K`. On `Ω`, `ι_s(U + W) = ι_s U`
(`Rd.sobolevToL2_eq_indicatorLp_add`), the Schwartz function of `U`
(`Rd.exists_schwartz_of_mem_testSpan`, `Rd.sobolevToL2_eq_of_toDistr_eq`), whose closed support
`K` lies in the bounded `Ω`. -/
theorem exists_isCompact_sobolevToL2_add_eq_zero (hs0 : 0 ≤ s) {U W : H^{s}(V)}
    (hU : U ∈ testSpan s Ω.toOpens) (hW : W ∈ vanishOn s Ω.toOpens) :
    ∃ K : Set V, IsCompact K ∧ K ⊆ Ω.carrier ∧
      ∀ᵐ x ∂volume, x ∈ Ω.carrier → x ∉ K → sobolevToL2 hs0 (U + W) x = 0 := by
  obtain ⟨w, hw, hUw⟩ := exists_schwartz_of_mem_testSpan hU
  have hUw' : sobolevToL2 hs0 U = w.toLp 2 (volume : Measure V) :=
    sobolevToL2_eq_of_toDistr_eq hs0 U (by rw [Lp.toTemperedDistribution_toLp_eq]; exact hUw.symm)
  have hid := sobolevToL2_eq_indicatorLp_add hs0 (Submodule.le_topologicalClosure _ hU) hW
  rw [hUw'] at hid
  refine ⟨tsupport w, isCompact_of_isClosed_isBounded (isClosed_tsupport w)
    (Ω.isBounded.subset hw), hw, ?_⟩
  filter_upwards [w.coeFn_toLp 2 volume, hid ▸ indicatorLp_apply_ae Ω.toOpens.isOpen.measurableSet
    (sobolevToL2 hs0 (U + W))] with x hwx hix hxΩ hxK
  rw [indicator_of_mem (show x ∈ (Ω.toOpens : Set V) from hxΩ)] at hix
  rw [← hix, hwx, image_eq_zero_of_notMem_tsupport hxK]

/-- **Localised functions vanish near the graph**: let `K ⊆ Ω` be compact and `Φ = 0` almost
everywhere on `Ω \ K`. For every resolution of unity `ψ` and chart `j` there is `ε > 0` with
`ψ_j Φ = 0` almost everywhere on the points of the graph domain `Ω_j` of height less than `ε`.
Take `ε` below the distance of `K` to `V \ Ω` and of `supp ψ_j` to `V \ B_j`
(Mathlib's `IsCompact.exists_thickening_subset_open`). If `ψ_j(x) ≠ 0`, `x ∈ Ω_j` and
`η_j(x) < ε`, then `x ∈ Ω` (`Rd.BoundedLipschitzDomain.mem_carrier_iff_of_mem_ball`), and the
point `z = x - η_j(x) e_j` on the graph is at distance `η_j(x) < ε` from `x`; it lies in `B_j`
but not in `Ω_j` (`Rd.LipschitzGraph.graphHeight_add_smul`), hence not in `Ω`, so `x ∉ K`. -/
theorem exists_mul_eq_zero_of_graphHeight_lt (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {K : Set V}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω.carrier) {Φ : V → ℂ}
    (hΦ : ∀ᵐ x ∂volume, x ∈ Ω.carrier → x ∉ K → Φ x = 0) :
    ∃ ε > 0, ∀ᵐ x ∂volume, x ∈ (Ω.graph j).domain → (Ω.graph j).graphHeight x < ε →
      ψ.toComplex j x * Φ x = 0 := by
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open Ω.isOpen hKΩ
  obtain ⟨δ', hδ', hδψ⟩ := (ψ.hasCompactSupport j).isCompact.exists_thickening_subset_open
    isOpen_ball (ψ.tsupport_subset j)
  refine ⟨min δ δ', lt_min hδ hδ', ?_⟩
  filter_upwards [hΦ] with x hx hxd hxη
  by_cases hψ : ψ.toFun j x = 0
  · rw [ψ.toComplex_of_eq_zero hψ, zero_mul]
  have hxΩ : x ∈ Ω.carrier := (Ω.mem_carrier_iff_of_mem_ball (ψ.mem_ball_of_ne_zero hψ)).2 hxd
  have hη0 : 0 < (Ω.graph j).graphHeight x := ((Ω.graph j).mem_domain_iff_graphHeight_pos x).1 hxd
  have hxK : x ∉ K := fun hxK => by
    set z := x + (-(Ω.graph j).graphHeight x) • (Ω.graph j).e
    have hdist : dist z x < min δ δ' := by
      rw [dist_eq_norm, show z - x = (-(Ω.graph j).graphHeight x) • (Ω.graph j).e by simp [z],
        norm_smul, (Ω.graph j).norm_e, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hη0]
      exact hxη
    have hzΩ : z ∈ Ω.carrier :=
      hδK (mem_thickening_iff.2 ⟨x, hxK, hdist.trans_le (min_le_left _ _)⟩)
    have hzB : z ∈ ball (Ω.center j) (Ω.radius j) := hδψ (mem_thickening_iff.2
      ⟨x, subset_tsupport _ hψ, hdist.trans_le (min_le_right _ _)⟩)
    have hzd := ((Ω.graph j).mem_domain_iff_graphHeight_pos z).1
      ((Ω.mem_carrier_iff_of_mem_ball hzB).1 hzΩ)
    rw [(Ω.graph j).graphHeight_add_smul, add_neg_cancel] at hzd
    exact lt_irrefl _ hzd
  rw [hx hxΩ hxK, mul_zero]

/-- **The zero extension bound for `1/2 < s < 1`** (McLean, Theorem 3.33; Hewett–Moiola,
Lemma 2.1): a bounded Lipschitz domain has the zero extension bound at `s` with some constant
`C`, so restriction is an isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)`
(`Rd.HasZeroExtensionBound.tildeEquivZeroBoundaryOfBound`). For `U ∈ T^s(Ω)` and `W` vanishing on
`Ω` let `Φ = ι_s(U + W)`; then `ι_s U = 1_Ω Φ = ∑_j 1_{Ω_j}(ψ_j Φ) + χ Φ`
(`Rd.sobolevToL2_eq_indicatorLp_add`, `Rd.BoundedLipschitzDomain.indicatorLp_eq_sum_add`), each
`ψ_j Φ` vanishes near the graph of `Ω_j`
(`Rd.BoundedLipschitzDomain.exists_isCompact_sobolevToL2_add_eq_zero`,
`Rd.BoundedLipschitzDomain.exists_mul_eq_zero_of_graphHeight_lt`), so the extension by zero from
`Ω_j` (`Rd.LipschitzGraph.exists_modNorm_indicatorLp_le_of_vanish`, `s > 1/2`) and the smooth
multipliers (`Rd.exists_mul_modNorm_le`, `s < 1`) give `N_s(ι_s U) ≤ C' N_s(Φ)`; the norm of
`H^s(V)` and `N_s` are equivalent (`Rd.enorm_le_modNorm_sobolevToL2`,
`Rd.modNorm_sobolevToL2_le`). -/
theorem exists_hasZeroExtensionBound_of_half_lt (hs : 1 / 2 < s) (hs1 : s < 1) :
    ∃ C : ℝ, HasZeroExtensionBound s Ω.toOpens C := by
  have hs0 : 0 ≤ s := by linarith
  have hs1' : s < ((1 : ℕ) : ℝ) := by rw [Nat.cast_one]; exact hs1
  obtain ⟨ψ, -, -, hψ⟩ := Ω.exists_boundaryPartition_nhds
  obtain ⟨χ, hχ, hcs, hχΩ, hχ1⟩ := exists_interior_cutoff ψ hψ
  obtain ⟨Cχ, hCχ, hχmul⟩ := exists_mul_modNorm_le two_ne_top
    (Complex.ofRealCLM.contDiff.comp hχ) (hcs.comp_left Complex.ofReal_zero) hs1' one_le_two
  choose Cψ hCψ hψmul using fun j => exists_mul_modNorm_le two_ne_top (ψ.contDiff_toComplex j)
    (ψ.hasCompactSupport_toComplex j) hs1' one_le_two
  choose C₂ hC₂ hext using fun j => (Ω.graph j).exists_modNorm_indicatorLp_le_of_vanish hs
  set N : Lp ℂ 2 (volume : Measure V) → ℝ≥0∞ := fun F =>
    ‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight s k * lpModulus 2 1 F k)
  set K := sobolevBesovInvConst V s 1 * (∑ j, C₂ j * Cψ j + Cχ) * sobolevBesovConst V s 1
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (sobolevBesovInvConst_ne_top s 1)
    (ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (hC₂ j) (hCψ j),
      hCχ⟩)) (sobolevBesovConst_ne_top (by linarith) hs1')
  refine ⟨K.toReal, fun U hU W hW => ?_⟩
  set Φ := sobolevToL2 hs0 (U + W)
  obtain ⟨G₀, hG₀ae, hG₀⟩ := hχmul Φ
  choose G hGae hG using fun j => hψmul j Φ
  obtain ⟨Kc, hKc, hKcΩ, hΦK⟩ := Ω.exists_isCompact_sobolevToL2_add_eq_zero hs0 hU hW
  have hvan : ∀ j, ∃ ε > 0, ∀ᵐ x ∂volume, x ∈ (Ω.graph j).domain →
      (Ω.graph j).graphHeight x < ε → G j x = 0 := fun j => by
    obtain ⟨ε, hε, h⟩ := Ω.exists_mul_eq_zero_of_graphHeight_lt ψ j hKc hKcΩ hΦK
    refine ⟨ε, hε, ?_⟩
    filter_upwards [h, hGae j] with x hx hGx hxd hxη
    rw [hGx]
    exact hx hxd hxη
  have hdec : sobolevToL2 hs0 U =
      ∑ j, indicatorLp (Ω.graph j).measurableSet_domain (G j) + G₀ :=
    (sobolevToL2_eq_indicatorLp_add hs0 (Submodule.le_topologicalClosure _ hU) hW).trans
      (Ω.indicatorLp_eq_sum_add ψ ((subset_tsupport χ).trans hχΩ) hχ1 hGae hG₀ae)
  have hN : N (sobolevToL2 hs0 U) ≤ (∑ j, C₂ j * Cψ j + Cχ) * N Φ := by
    rw [hdec, add_mul, Finset.sum_mul]
    refine (modNorm_add_le _ _ 1 s one_le_two).trans (add_le_add ?_ hG₀)
    refine (modNorm_finsetSum_le _ _ 1 s one_le_two).trans (Finset.sum_le_sum fun j _ => ?_)
    calc _ ≤ C₂ j * modNormOn (Ω.graph j).measurableSet_domain 1 s 2 (G j) := hext j (G j) (hvan j)
      _ ≤ C₂ j * N (G j) :=
          mul_le_mul' le_rfl (modNormOn_le_modNorm_of_indicatorLp _ 1 s 2 rfl)
      _ ≤ C₂ j * (Cψ j * N Φ) := mul_le_mul' le_rfl (hG j)
      _ = C₂ j * Cψ j * N Φ := by ring
  have h : ‖U‖ₑ ≤ K * ‖U + W‖ₑ :=
    calc ‖U‖ₑ ≤ sobolevBesovInvConst V s 1 * N (sobolevToL2 hs0 U) :=
          enorm_le_modNorm_sobolevToL2 hs0 1 U
      _ ≤ sobolevBesovInvConst V s 1 * ((∑ j, C₂ j * Cψ j + Cχ) *
            (sobolevBesovConst V s 1 * ‖U + W‖ₑ)) :=
          mul_le_mul' le_rfl (hN.trans (mul_le_mul' le_rfl
            (modNorm_sobolevToL2_le (by linarith) hs1' (U + W))))
      _ = K * ‖U + W‖ₑ := by ring
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top hK eNorm_ne_top) h
  rwa [toReal_eNorm, ENNReal.toReal_mul, toReal_eNorm] at h'

/-! ### `H̃^s(Ω) ≅ H^s_0(Ω)` for `s ≥ 0`, `s ∉ 1/2 + ℕ_0` -/

/-- **The zero extension bound for `0 ≤ s < 1`, `s ≠ 1/2`**: a bounded Lipschitz domain has the
zero extension bound at `s` with some constant, for `s < 1/2` by the indicator of `Ω` as a
multiplier (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_lt_half`) and for
`1/2 < s < 1` by the Hardy inequality
(`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_half_lt`). -/
theorem exists_hasZeroExtensionBound_of_lt_one (hs0 : 0 ≤ s) (hs1 : s < 1) (hs : s ≠ 1 / 2) :
    ∃ C : ℝ, HasZeroExtensionBound s Ω.toOpens C := by
  rcases lt_or_gt_of_ne hs with h | h
  · exact Ω.exists_hasZeroExtensionBound_of_lt_half hs0 h
  · exact Ω.exists_hasZeroExtensionBound_of_half_lt h hs1

/-- **The zero extension bound for every `s ≥ 0` with `s - 1/2 ∉ ℕ_0`** (McLean, Theorem 3.33;
the case of bounded `Ω` and `s ≥ 0` of Hewett–Moiola, Lemma 2.1): a bounded Lipschitz domain has
the zero extension bound at `s` with some constant `C`. With `m = ⌊s⌋`, the fractional part
`s - m ∈ [0, 1)` differs from `1/2`, so the bound holds at `s - m`
(`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_lt_one`), and lifting it `m` times
keeps the constant (`Rd.HasZeroExtensionBound.add_natCast`). On a smooth bounded domain,
restriction does not map `H̃^s(Ω)` onto `H^s_0(Ω)` for the excluded `s ∈ 1/2 + ℕ_0`
(Hewett–Moiola, Remark 2.5). -/
theorem exists_hasZeroExtensionBound (hs0 : 0 ≤ s) (hs : ∀ k : ℕ, s ≠ k + 1 / 2) :
    ∃ C : ℝ, HasZeroExtensionBound s Ω.toOpens C := by
  have hm : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs0
  have hm1 : s < ⌊s⌋₊ + 1 := Nat.lt_floor_add_one s
  obtain ⟨C, hC⟩ := Ω.exists_hasZeroExtensionBound_of_lt_one (sub_nonneg.2 hm) (by linarith)
    (fun h => hs ⌊s⌋₊ (by linarith))
  refine ⟨C, ?_⟩
  have h := hC.add_natCast ⌊s⌋₊
  rwa [sub_add_cancel] at h

/-- **`H̃^s(Ω) ≅ H^s_0(Ω)` for `s ≥ 0`, `s - 1/2 ∉ ℕ_0`** (McLean, Theorem 3.33; the case of
bounded `Ω` and `s ≥ 0` of Hewett–Moiola, Lemma 2.1): on a bounded Lipschitz domain, restriction
is an isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)`, the isomorphism of the zero extension bound
(`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound`,
`Rd.HasZeroExtensionBound.tildeEquivZeroBoundaryOfBound`), with `‖U|_Ω‖ ≤ ‖U‖ ≤ C ‖U|_Ω‖`. With the
Gelfand triple `H̃^s(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)`
(`Rd.sobolevPairing_tildeDualEquiv_pivotDual_tildeToL2`) it gives the triple
`H^s_0(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)` up to equivalent norms.

The two spaces sit in different ambient spaces: `H̃^s(Ω)` (`Rd.tildeSpace`) is the closure of the
test functions of `Ω` in `H^s(V)`, and `H^s_0(Ω)` (`Rd.zeroBoundarySpace`) is the closure of their
restrictions in `H^s(Ω)`. For `s ≥ 0` and every open `Ω`, restriction maps `H̃^s(Ω)` into
`H^s_0(Ω)` injectively, with dense range and norm at most `1`
(`Rd.tildeToRestrictionL_injective_of_nonneg`, `Rd.closure_range_tildeToRestrictionL`,
`Rd.norm_restrictProj_apply_le`; Hewett–Moiola, Lemma 2.2(iii)). It is onto exactly when extending
by zero is bounded, `‖U‖ ≤ C ‖U|_Ω‖` on `H̃^s(Ω)` (Hewett–Moiola, the list after Lemma 2.9). At
`s ∈ 1/2 + ℕ_0` this fails on smooth bounded domains (Hewett–Moiola, Remark 2.5). At `s = 1/2` the
constant `1` lies in `H^{1/2}_0(Ω) = H^{1/2}(Ω)`, but its zero extension `1_Ω` does not lie in
`H^{1/2}(V)`, so `1` is the restriction of no element of `H̃^{1/2}(Ω)`; this holds for every bounded
Lipschitz domain (Chandler-Wilde–Hewett–Moiola, Remark 3.32). -/
noncomputable def tildeEquivZeroBoundaryOfNeHalf (hs0 : 0 ≤ s) (hs : ∀ k : ℕ, s ≠ k + 1 / 2) :
    tildeSpace s Ω.toOpens ≃L[ℂ] zeroBoundarySpace s Ω.toOpens :=
  (Ω.exists_hasZeroExtensionBound hs0 hs).choose_spec.tildeEquivZeroBoundaryOfBound

/-- `Ω.tildeEquivZeroBoundaryOfNeHalf hs0 hs U` is the restriction of `U` to `Ω`. -/
theorem coe_tildeEquivZeroBoundaryOfNeHalf_apply (hs0 : 0 ≤ s) (hs : ∀ k : ℕ, s ≠ k + 1 / 2)
    (U : tildeSpace s Ω.toOpens) :
    (Ω.tildeEquivZeroBoundaryOfNeHalf hs0 hs U : RestrictionSpace s Ω.toOpens) =
      restrictProj s Ω.toOpens U :=
  rfl

end BoundedLipschitzDomain

end Rd
