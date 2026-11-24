/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Sobolev.TildeZeroBoundaryEquiv
public import FunctionSpaces.Domains.Sobolev.LipschitzDomainGreen
public import FunctionSpaces.Domains.Traces.TraceKernel
public import FunctionSpaces.Rd.FourierMultipliers.BesselPotentialMultipliers

/-!
# The kernel of the trace of `H^s(Ω)`, `1/2 < s < 3/2`

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner product
space `V`, such as `ℝ^d`, with Lebesgue measure, `H^s(Ω)` the Hilbert space of restrictions of
`H^s(V)`, `H̃^s(Ω)` the closure of the test functions of `Ω` in `H^s(V)`, `H^s_0(Ω)` the closure
of their restrictions in `H^s(Ω)`, `ι_s U` the `L_2` function of `U ∈ H^s(V)`, `s ≥ 0`
(`Rd.sobolevToL2`), `ι_{t,s} : H^s(V) → H^t(V)` and `ι^Ω_{t,s} : H^s(Ω) → H^t(Ω)` the inclusions,
`t ≤ s` (`Rd.sobolevInclusion`, `Rd.restrictionInclusion`), and `ker γ_s = Ω.traceKer s` the
trace kernel of `H^s(Ω)`, `1/2 < s < 3/2`.

* **Zero extensions of `ker γ_s`, `1 ≤ s < 3/2`**: for `u ∈ ker γ_s`, `ι^Ω_{1,s} u ∈ ker γ_1`, so
  `∂_v(1_Ω ι_s u) = 1_Ω ∂_v(ι_{1,s} u)`
  (`Rd.BoundedLipschitzDomain.lineDerivOp_indicatorLp_of_mem_traceKer`, from Green's formula
  `Rd.BoundedLipschitzDomain.hasWeakLineDeriv_indicatorLp_of_mem_traceKer`, since on `Ω` a
  restriction has the same `L_2` function and weak derivatives, `Rd.sobolevToL2_restrictProj_ae_eq`,
  `Rd.weakDerivL2_restrictProj_ae_eq`).
  As `s - 1 < 1/2`, the indicator of `Ω` keeps `H^{s-1}(V)`
  (`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_indicatorLp`), so `1_Ω ι_s u` and its first
  derivatives lie in `H^{s-1}(V)` (`Rd.memSobolev_bessel_iff_exists_sobolevToL2_eq`,
  `Rd.memSobolev_bessel_weakDerivL2_sobolevInclusion`), and `1_Ω ι_s u` lies in `H^s(V)`
  (`TemperedDistribution.memSobolev_add_one_iff`,
  `Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_indicatorLp_of_mem_traceKer`).
* **`ker γ_s = H^s_0(Ω)` for `1/2 < s < 3/2`**
  (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`; McLean, Theorem 3.40): for
  `1/2 < s ≤ 1` by approximation from the level `1`
  (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace_of_le_one`), for `1 ≤ s < 3/2` by
  zero extension (`Rd.BoundedLipschitzDomain.traceKer_le_zeroBoundarySpace_of_one_le`), since a
  function of `H^s(Ω)` whose zero extension lies in `H^s(V)` lies in `H^s_0(Ω)`
  (`Rd.BoundedLipschitzDomain.mem_zeroBoundarySpace_of_sobolevToL2_eq_indicatorLp`). So the
  kernel of the trace `H^s(Ω) → H^{s-1/2}(Γ)` is `H^s_0(Ω)`
  (`Rd.BoundedLipschitzDomain.ker_sobolevTrace_eq_zeroBoundarySpace`), and `u ∈ ker γ_s` iff
  `1_Ω ι_s u = ι_s U'` for some `U' ∈ H^s(V)`
  (`Rd.BoundedLipschitzDomain.mem_traceKer_iff_exists_sobolevToL2_eq_indicatorLp`).
* **The quotient**: `H^s(Ω) ⧸ H^s_0(Ω)` is isometrically isomorphic to the trace space of `H^s(Ω)`
  (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`), the class of `u` going to
  `γ_s u`, and isomorphic to `H^{s-1/2}(Γ)`
  (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivBoundarySobolev`). The quotient norm is
  equivalent to the Sobolev–Slobodeckij norm of `H^{s-1/2}(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`). For `s = 1` this is the
  trace space of Hiptmair, Pauly and Schulz for `k = 0`.
-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal SchwartzMap BesselPotentialSpace Distributions LineDeriv

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-! ### Zero extensions of `ker γ_s`, `1 ≤ s < 3/2` -/

/-- **The derivatives of the zero extension of `u ∈ ker γ_s`**, `1 ≤ s < 3/2`: for every direction
`v`, `∂_v(1_Ω ι_s u) = 1_Ω ∂_v(ι_{1,s} u)` as tempered distributions, with `u` read in `H^s(V)`.
`u₁ = ι^Ω_{1,s} u = (ι_{1,s} u)|_Ω` lies in `ker γ_1`
(`Rd.BoundedLipschitzDomain.restrictionInclusion_mem_traceKer`), so `1_Ω ∂_v u₁` is the weak
derivative of `1_Ω ι_1 u₁` on `V`
(`Rd.BoundedLipschitzDomain.hasWeakLineDeriv_indicatorLp_of_mem_traceKer`); on `Ω`, `u₁` and
`ι_{1,s} u` have the same `L_2` function and weak derivatives
(`Rd.sobolevToL2_restrictProj_ae_eq`, `Rd.weakDerivL2_restrictProj_ae_eq`), and weak
derivatives on `V` are derivatives of tempered distributions (`Rd.hasWeakLineDeriv_top_iff`). -/
theorem lineDerivOp_indicatorLp_of_mem_traceKer (s : ℝ) (hs1 : 1 ≤ s) (hs' : s < 3 / 2)
    {u : RestrictionSpace s Ω.toOpens} (hu : u ∈ Ω.traceKer s (by linarith) hs') (v : V) :
    ∂_{v} ((indicatorLp Ω.measurableSet (sobolevToL2 (zero_le_one.trans hs1) (u : H^{s}(V))) :
        Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      ((indicatorLp Ω.measurableSet (weakDerivL2 v (sobolevInclusion hs1 (u : H^{s}(V)))) :
        Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) := by
  have hu₁ := Ω.restrictionInclusion_mem_traceKer (by norm_num) hs1 hs' hu
  have h := Ω.hasWeakLineDeriv_indicatorLp_of_mem_traceKer hu₁ v
  have e1 : indicatorLp Ω.measurableSet
      (toL2 (restrictionInclusion hs1 Ω.toOpens u : H^{1}(V))) =
      indicatorLp Ω.measurableSet (sobolevToL2 (zero_le_one.trans hs1) (u : H^{s}(V))) := by
    refine (indicatorLp_eq_iff_ae_eq_restrict _).2 ?_
    have h1 := sobolevToL2_restrictProj_ae_eq (Ω := Ω.toOpens) zero_le_one
      (sobolevInclusion hs1 (u : H^{s}(V)))
    rw [sobolevToL2_sobolevInclusion, sobolevToL2_one] at h1
    exact h1
  have e2 : indicatorLp Ω.measurableSet
      (weakDerivL2 v (restrictionInclusion hs1 Ω.toOpens u : H^{1}(V))) =
      indicatorLp Ω.measurableSet (weakDerivL2 v (sobolevInclusion hs1 (u : H^{s}(V)))) :=
    (indicatorLp_eq_iff_ae_eq_restrict _).2
      (weakDerivL2_restrictProj_ae_eq (Ω := Ω.toOpens) v _)
  rw [e1, e2] at h
  have h' := hasWeakLineDeriv_top_iff.1 h
  rwa [LineDeriv.iteratedLineDerivOp_one] at h'

/-- **The zero extension of `u ∈ ker γ_s` lies in `H^s(V)`**, `1 ≤ s < 3/2`: there is
`U' ∈ H^s(V)` with `ι_s U' = 1_Ω ι_s u`. As `0 ≤ s - 1 < 1/2`, multiplication by `1_Ω` keeps
`H^{s-1}(V)` (`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_indicatorLp`), so `1_Ω ι_s u` lies
in `H^{s-1}(V)`, and so do its derivatives `1_Ω ∂_v(ι_{1,s} u)`
(`Rd.BoundedLipschitzDomain.lineDerivOp_indicatorLp_of_mem_traceKer`,
`Rd.memSobolev_bessel_weakDerivL2_sobolevInclusion`); a tempered distribution in `H^{s-1}(V)` with
all first derivatives in `H^{s-1}(V)` lies in `H^s(V)`
(`TemperedDistribution.memSobolev_add_one_iff`). -/
theorem exists_sobolevToL2_eq_indicatorLp_of_mem_traceKer (s : ℝ) (hs1 : 1 ≤ s)
    (hs' : s < 3 / 2) {u : RestrictionSpace s Ω.toOpens}
    (hu : u ∈ Ω.traceKer s (by linarith) hs') :
    ∃ U' : H^{s}(V), sobolevToL2 (zero_le_one.trans hs1) U' =
      indicatorLp Ω.measurableSet (sobolevToL2 (zero_le_one.trans hs1) (u : H^{s}(V))) := by
  have hσ0 : 0 ≤ s - 1 := sub_nonneg.2 hs1
  have hσ : s - 1 < 1 / 2 := by linarith
  have hsub : s - 1 ≤ s := by linarith
  have h0 : TemperedDistribution.MemSobolev (s - 1) 2 ((indicatorLp Ω.measurableSet
      (sobolevToL2 (zero_le_one.trans hs1) (u : H^{s}(V))) : Lp ℂ 2 (volume : Measure V)) :
        𝓢'(V, ℂ)) := by
    obtain ⟨F₀, hF₀⟩ := Ω.exists_sobolevToL2_eq_indicatorLp hσ0 hσ
      (sobolevInclusion hsub (u : H^{s}(V)))
    rw [sobolevToL2_sobolevInclusion] at hF₀
    exact (memSobolev_bessel_iff_exists_sobolevToL2_eq hσ0 _).2 ⟨F₀, hF₀⟩
  have h1 : ∀ v : V, TemperedDistribution.MemSobolev (s - 1) 2 (∂_{v} ((indicatorLp
      Ω.measurableSet (sobolevToL2 (zero_le_one.trans hs1) (u : H^{s}(V))) :
        Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ))) := fun v => by
    rw [Ω.lineDerivOp_indicatorLp_of_mem_traceKer s hs1 hs' hu v]
    obtain ⟨D, hD⟩ := (memSobolev_bessel_iff_exists_sobolevToL2_eq hσ0 _).1
      (memSobolev_bessel_weakDerivL2_sobolevInclusion hs1 (u : H^{s}(V)) v)
    obtain ⟨G, hG⟩ := Ω.exists_sobolevToL2_eq_indicatorLp hσ0 hσ D
    rw [hD] at hG
    exact (memSobolev_bessel_iff_exists_sobolevToL2_eq hσ0 _).2 ⟨G, hG⟩
  have h := (TemperedDistribution.memSobolev_add_one_iff ENNReal.one_lt_two two_ne_top).2 ⟨h0, h1⟩
  rw [sub_add_cancel] at h
  exact (memSobolev_bessel_iff_exists_sobolevToL2_eq _ _).1 h

/-! ### `ker γ_s = H^s_0(Ω)` -/

/-- **`ker γ_s ⊆ H^s_0(Ω)` for `1 ≤ s < 3/2`** (McLean, Theorem 3.40): the zero extension of
`u ∈ ker γ_s` lies in `H^s(V)`
(`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_indicatorLp_of_mem_traceKer`), so `u` lies in
`H^s_0(Ω)` (`Rd.BoundedLipschitzDomain.mem_zeroBoundarySpace_of_sobolevToL2_eq_indicatorLp`). -/
theorem traceKer_le_zeroBoundarySpace_of_one_le (s : ℝ) (hs1 : 1 ≤ s) (hs' : s < 3 / 2) :
    Ω.traceKer s (by linarith) hs' ≤ zeroBoundarySpace s Ω.toOpens := fun u hu => by
  obtain ⟨U', hU'⟩ := Ω.exists_sobolevToL2_eq_indicatorLp_of_mem_traceKer s hs1 hs' hu
  exact Ω.mem_zeroBoundarySpace_of_sobolevToL2_eq_indicatorLp _ hU'

/-- **`ker γ_s = H^s_0(Ω)` for `1/2 < s < 3/2`** on a bounded Lipschitz domain (McLean,
Theorem 3.40): the elements of `H^s(Ω)` whose boundary trace vanishes almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff`) are exactly the limits in `H^s(Ω)` of restricted
test functions of `Ω`. `H^s_0(Ω) ⊆ ker γ_s` is
`Rd.BoundedLipschitzDomain.zeroBoundarySpace_le_traceKer`; the converse is
`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace_of_le_one` for `s ≤ 1` and
`Rd.BoundedLipschitzDomain.traceKer_le_zeroBoundarySpace_of_one_le` for `s ≥ 1`. At `s = 1` this
is `Rd.BoundedLipschitzDomain.traceKer_one_eq_zeroBoundarySpace`. -/
theorem traceKer_eq_zeroBoundarySpace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : Ω.traceKer s hs hs' = zeroBoundarySpace s Ω.toOpens := by
  rcases le_or_gt s 1 with hs1 | hs1
  · exact Ω.traceKer_eq_zeroBoundarySpace_of_le_one s hs hs1
  · exact le_antisymm (Ω.traceKer_le_zeroBoundarySpace_of_one_le s hs1.le hs')
      (Ω.zeroBoundarySpace_le_traceKer s hs hs')

/-- **The kernel of the trace `H^s(Ω) → H^{s-1/2}(Γ)` is `H^s_0(Ω)`**, `1/2 < s < 3/2` (McLean,
Theorem 3.40): `Rd.BoundedLipschitzDomain.ker_sobolevTrace` and
`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`. -/
theorem ker_sobolevTrace_eq_zeroBoundarySpace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.sobolevTrace s hs hs').ker = zeroBoundarySpace s Ω.toOpens := by
  rw [Ω.ker_sobolevTrace s hs hs', Ω.traceKer_eq_zeroBoundarySpace s hs hs']

/-- **Vanishing trace by zero extension**, `1/2 < s < 3/2`: `u ∈ H^s(Ω)` lies in `ker γ_s` iff
its zero extension `1_Ω ι_s u` is `ι_s U'` for some `U' ∈ H^s(V)`. At `s = 1`, with `W^1_2(V)` in
place of `H^1(V)`, this is `Rd.BoundedLipschitzDomain.memSobolevW_indicatorLp_iff_mem_traceKer`.
If `ι_s U' = 1_Ω ι_s u`, then `u ∈ H^s_0(Ω) ⊆ ker γ_s`
(`Rd.BoundedLipschitzDomain.mem_zeroBoundarySpace_of_sobolevToL2_eq_indicatorLp`,
`Rd.BoundedLipschitzDomain.zeroBoundarySpace_le_traceKer`). Conversely, `ker γ_s = H^s_0(Ω)`
(`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`) is the image of `H̃^s(Ω)` under
restriction, since `s ∉ 1/2 + ℕ_0` (`Rd.BoundedLipschitzDomain.tildeEquivZeroBoundaryOfNeHalf`),
and `U ∈ H̃^s(Ω)` with `U|_Ω = u` has `ι_s U = 1_Ω ι_s u`, as `U|_Ω - U` vanishes on `Ω`
(`Rd.sub_restrictProj_mem`, `Rd.sobolevToL2_eq_indicatorLp_add`). -/
theorem mem_traceKer_iff_exists_sobolevToL2_eq_indicatorLp (s : ℝ)
    (u : RestrictionSpace s Ω.toOpens) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    u ∈ Ω.traceKer s hs hs' ↔ ∃ U' : H^{s}(V), sobolevToL2 (one_half_pos.trans hs).le U' =
      indicatorLp Ω.measurableSet (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V))) := by
  have h0 : 0 ≤ s := (one_half_pos.trans hs).le
  refine ⟨fun hu => ?_, fun ⟨U', hU'⟩ => Ω.zeroBoundarySpace_le_traceKer s hs hs'
    (Ω.mem_zeroBoundarySpace_of_sobolevToL2_eq_indicatorLp h0 hU')⟩
  have hne : ∀ k : ℕ, s ≠ k + 1 / 2 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [Nat.cast_zero, zero_add] at hk
      exact hs.ne' hk
    · have h1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk1
      linarith
  have hz : u ∈ zeroBoundarySpace s Ω.toOpens := by
    rwa [← Ω.traceKer_eq_zeroBoundarySpace s hs hs']
  set U := (Ω.tildeEquivZeroBoundaryOfNeHalf h0 hne).symm ⟨u, hz⟩ with hUdef
  have hU : restrictProj s Ω.toOpens (U : H^{s}(V)) = u := by
    rw [← Ω.coe_tildeEquivZeroBoundaryOfNeHalf_apply h0 hne, hUdef,
      ContinuousLinearEquiv.apply_symm_apply]
  have hW : (restrictProj s Ω.toOpens (U : H^{s}(V)) : H^{s}(V)) - U ∈
      vanishOn s Ω.toOpens := by
    rw [← neg_sub]
    exact neg_mem (sub_restrictProj_mem _)
  have h := sobolevToL2_eq_indicatorLp_add h0 U.2 hW
  rw [add_sub_cancel, hU] at h
  exact ⟨U, h⟩

/-! ### The quotient `H^s(Ω) ⧸ H^s_0(Ω)` -/

/-- **`H^s(Ω) ⧸ H^s_0(Ω)` is the trace space of `H^s(Ω)`, isometrically**, `1/2 < s < 3/2`: the
quotient of `H^s(Ω)` by `H^s_0(Ω)`, with the quotient norm, is isometrically isomorphic to the
trace space `Ω.TraceSpace s`, the orthogonal complement of `ker γ_s`: the isometry
`H^s(Ω) ⧸ ker γ_s ≅ Ω.TraceSpace s` (`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`) after
the change of subspace `H^s_0(Ω) = ker γ_s` (Mathlib's `Submodule.quotLIEOfEq`,
`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`). The class of `u` corresponds to
`γ_s u` (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace_mk`). The content is
`ker γ_s = H^s_0(Ω)`; the isometry holds by the definition of the trace space as the orthogonal
complement of `ker γ_s`. The norm of the trace space, and so the quotient norm, is equivalent to
the Sobolev–Slobodeckij norm of `H^{s-1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`). For `s = 1` this is the
trace space of Hiptmair, Pauly and Schulz for `k = 0`, and `H^{s-1/2}(Γ)` is the classical
`H^{1/2}(Γ)`. -/
noncomputable def quotientZeroBoundaryEquivTraceSpace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (RestrictionSpace s Ω.toOpens ⧸ zeroBoundarySpace s Ω.toOpens) ≃ₗᵢ[ℂ]
      Ω.TraceSpace s hs hs' :=
  (Submodule.quotLIEOfEq _ _ (Ω.traceKer_eq_zeroBoundarySpace s hs hs').symm).trans
    (Ω.quotientEquivTraceSpace s hs hs')

/-- The class of `u` modulo `H^s_0(Ω)` corresponds to the trace `γ_s u`: the change of subspace
keeps the class of `u` (Mathlib's `Submodule.quotEquivOfEq_mk`), and
`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace_mk`. -/
theorem quotientZeroBoundaryEquivTraceSpace_mk (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.quotientZeroBoundaryEquivTraceSpace s hs hs' (Submodule.Quotient.mk u) =
      Ω.domainTrace s hs hs' u := by
  rw [quotientZeroBoundaryEquivTraceSpace, LinearIsometryEquiv.trans_apply]
  exact Ω.quotientEquivTraceSpace_mk s u hs hs'

/-- **`H^s(Ω) ⧸ H^s_0(Ω) ≅ H^{s-1/2}(Γ)`**, `1/2 < s < 3/2` (McLean, Theorems 3.38 and 3.40): the
isometry onto the trace space (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`)
followed by the isomorphism of the trace space with `H^{s-1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev`). The class of `u` goes to its trace
in `H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivBoundarySobolev_mk`). -/
noncomputable def quotientZeroBoundaryEquivBoundarySobolev (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (RestrictionSpace s Ω.toOpens ⧸ zeroBoundarySpace s Ω.toOpens) ≃L[ℂ]
      Ω.BoundarySobolev (s - 1 / 2) :=
  (Ω.quotientZeroBoundaryEquivTraceSpace s hs hs').toContinuousLinearEquiv.trans
    (Ω.traceSpaceEquivBoundarySobolev s hs hs')

/-- The class of `u` modulo `H^s_0(Ω)` goes to the trace of `u` in `H^{s-1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.sobolevTrace`). -/
theorem quotientZeroBoundaryEquivBoundarySobolev_mk (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.quotientZeroBoundaryEquivBoundarySobolev s hs hs' (Submodule.Quotient.mk u) =
      Ω.sobolevTrace s hs hs' u := by
  rw [quotientZeroBoundaryEquivBoundarySobolev, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    Ω.quotientZeroBoundaryEquivTraceSpace_mk s u hs hs']
  rfl

end BoundedLipschitzDomain

end Rd
