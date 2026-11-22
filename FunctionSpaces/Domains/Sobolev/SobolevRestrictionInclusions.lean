/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Sobolev.SobolevRestrictionSpaces

/-!
# Inclusions of Sobolev spaces on open sets

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω ⊆ V` open and `t ≤ s` real. The inclusion `ι_{t,s} : H^s(V) → H^t(V)` (`Rd.sobolevInclusion`)
keeps the tempered distribution; this file carries it to the spaces built inside `H^s(V)`
(`Rd.vanishOn`, `Rd.RestrictionSpace`, `Rd.testSpan`, `Rd.zeroBoundarySpace`), and shows that
derivatives map test functions to test functions and keep vanishing on `Ω`.

* **Schwartz and test functions**: `ι_{t,s}` maps a Schwartz function and a test function of `Ω`
  in `H^s(V)` to the same function in `H^t(V)` (`Rd.sobolevInclusion_ofSchwartz`,
  `Rd.sobolevInclusion_ofTest`), so it has dense range (`Rd.denseRange_sobolevInclusion`);
  at `t = s` it is the identity (`Rd.sobolevInclusion_self`), and the `L_2` function of a
  Schwartz function is the function itself (`Rd.sobolevToL2_ofSchwartz`).
* **Vanishing and test functions**: `ι_{t,s} W` vanishes on `Ω` iff `W` does
  (`Rd.sobolevInclusion_mem_vanishOn_iff`), and `ι_{t,s}` maps the span of the test functions
  into the span of the test functions (`Rd.sobolevInclusion_mem_testSpan`).
* **The inclusion `H^s(Ω) ⊆ H^t(Ω)`**: `u ↦ (ι_{t,s} u)|_Ω` (`Rd.restrictionInclusion`), an
  injective bounded operator of norm at most `1` (`Rd.restrictionInclusion_injective`) with
  dense range that commutes with restriction,
  `ι_{t,s}(U|_Ω) = (ι_{t,s} U)|_Ω` (`Rd.restrictionInclusion_restrictProj`), and maps
  `H^s_0(Ω)` into `H^t_0(Ω)` (`Rd.restrictionInclusion_mem_zeroBoundarySpace`).
* **Derivatives**: `∂_v : H^{s+1}(V) → H^s(V)` maps a test function `φ` of `Ω` to the test
  function `∂_v φ` (`Rd.sobolevLineDeriv_ofTest`), the span of the test functions into the span
  of the test functions (`Rd.sobolevLineDeriv_mem_testSpan`), and the elements vanishing on `Ω` to
  elements vanishing on `Ω` (`Rd.sobolevLineDeriv_mem_vanishOn`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal SchwartzMap BesselPotentialSpace Distributions LineDeriv

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {s t : ℝ}

/-! ### The inclusions on Schwartz and test functions -/

/-- **The inclusion `ι_{s,s}` is the identity** of `H^s(V)`: it keeps the tempered distribution
(`Rd.toDistr_sobolevInclusion`), which determines an element of `H^s(V)` (Mathlib's
`BesselPotentialSpace.ext`). -/
theorem sobolevInclusion_self (U : H^{s}(V)) : sobolevInclusion le_rfl U = U :=
  BesselPotentialSpace.ext (toDistr_sobolevInclusion le_rfl U)

/-- **The `L_2` function of `H^0(V)` has the same norm**: `‖ι_0 U‖_2 = ‖U‖_{H^0}`, since
`ι_0 U = J_0 (ι_{0,0} U)` (`Rd.sobolevToL2_apply`), `‖J_0 U‖_2 = ‖U‖_{H^0}` (Mathlib's
`BesselPotentialSpace.norm_toLp_eq`) and `ι_{0,0}` is the identity (`Rd.sobolevInclusion_self`). -/
theorem norm_sobolevToL2_zero (U : H^{0}(V)) : ‖sobolevToL2 le_rfl U‖ = ‖U‖ := by
  rw [sobolevToL2_apply, BesselPotentialSpace.norm_toLp_eq, sobolevInclusion_self]

/-- **Schwartz functions under the inclusions**: for `t ≤ s` and a Schwartz function `w`,
`ι_{t,s} w = w`, since both sides have the tempered distribution `w`
(`Rd.toDistr_sobolevInclusion`, `Rd.toDistr_ofSchwartz`). -/
theorem sobolevInclusion_ofSchwartz (hts : t ≤ s) (w : 𝓢(V, ℂ)) :
    sobolevInclusion hts (ofSchwartz s w) = ofSchwartz t w :=
  BesselPotentialSpace.ext (by
    rw [toDistr_sobolevInclusion, toDistr_ofSchwartz, toDistr_ofSchwartz])

/-- **Test functions under the inclusions**: for `t ≤ s` and a real test function `φ` of an open
set `Ω`, `ι_{t,s} φ = φ` (`Rd.toDistr_sobolevInclusion`, `Rd.toDistr_ofTest`). -/
theorem sobolevInclusion_ofTest {Ω : Opens V} (hts : t ≤ s) (φ : 𝓓(Ω, ℝ)) :
    sobolevInclusion hts (ofTest s φ) = ofTest t φ :=
  BesselPotentialSpace.ext (by rw [toDistr_sobolevInclusion, toDistr_ofTest, toDistr_ofTest])

/-- **The inclusion `H^s(V) ⊆ H^t(V)` has dense range**: its range contains the Schwartz
functions (`Rd.sobolevInclusion_ofSchwartz`), which are dense in `H^t(V)`
(`Rd.denseRange_ofSchwartz`). -/
theorem denseRange_sobolevInclusion (hts : t ≤ s) : DenseRange (sobolevInclusion (V := V) hts) :=
  (denseRange_ofSchwartz t).mono (by
    rintro _ ⟨w, rfl⟩
    exact ⟨ofSchwartz s w, sobolevInclusion_ofSchwartz hts w⟩)

/-- **The `L_2` function of a Schwartz function** in `H^s(V)`, `s ≥ 0`, is the function itself:
`ι_s w = w` in `L_2(V)`, since both have the tempered distribution `w`
(`Rd.sobolevToL2_eq_of_toDistr_eq`; at `s = 1` this is `Rd.toL2_ofSchwartz`). -/
theorem sobolevToL2_ofSchwartz (hs : 0 ≤ s) (w : 𝓢(V, ℂ)) :
    sobolevToL2 hs (ofSchwartz s w) = w.toLp 2 :=
  sobolevToL2_eq_of_toDistr_eq hs _ (by
    rw [Lp.toTemperedDistribution_toLp_eq, toDistr_ofSchwartz])

/-! ### Vanishing on `Ω` and the span of the test functions -/

variable {Ω : Opens V}

/-- **The inclusions detect vanishing on `Ω`**: for `t ≤ s` and `W ∈ H^s(V)`, `ι_{t,s} W ∈ H^t(V)`
vanishes on `Ω` iff `W` does, since both have the same tempered distribution
(`Rd.toDistr_sobolevInclusion`, `Rd.mem_vanishOn_iff`). -/
theorem sobolevInclusion_mem_vanishOn_iff (hts : t ≤ s) (W : H^{s}(V)) :
    sobolevInclusion hts W ∈ vanishOn t Ω ↔ W ∈ vanishOn s Ω := by
  rw [mem_vanishOn_iff, mem_vanishOn_iff, toDistr_sobolevInclusion]

/-- **The inclusions keep vanishing on `Ω`**: for `t ≤ s`, if `W ∈ H^s(V)` vanishes on `Ω`, so
does `ι_{t,s} W ∈ H^t(V)` (`Rd.sobolevInclusion_mem_vanishOn_iff`). -/
theorem sobolevInclusion_mem_vanishOn (hts : t ≤ s) {W : H^{s}(V)} (hW : W ∈ vanishOn s Ω) :
    sobolevInclusion hts W ∈ vanishOn t Ω :=
  (sobolevInclusion_mem_vanishOn_iff hts W).2 hW

/-- **Linear maps that keep the test functions keep their span**: for all real `s` and `t`, if a
linear map `f : H^s(V) → H^t(V)` maps every test function of `Ω` into the span `T^t(Ω)` of the
test functions, then it maps `T^s(Ω)` into `T^t(Ω)` (Mathlib's `Submodule.map_span_le`). -/
theorem apply_mem_testSpan_of_forall (f : H^{s}(V) →ₗ[ℂ] H^{t}(V))
    (hf : ∀ φ : 𝓓(Ω, ℝ), f (ofTest s φ) ∈ testSpan t Ω) {U : H^{s}(V)}
    (hU : U ∈ testSpan s Ω) : f U ∈ testSpan t Ω := by
  have h : (testSpan s Ω).map f ≤ testSpan t Ω :=
    (Submodule.map_span_le _ _ _).2 (by
      rintro _ ⟨φ, rfl⟩
      exact hf φ)
  exact h (Submodule.mem_map_of_mem hU)

/-- **The inclusions keep the span of the test functions**: for `t ≤ s`,
`ι_{t,s}(T^s(Ω)) ⊆ T^t(Ω)`, since `ι_{t,s} φ = φ` for every test function `φ` of `Ω`
(`Rd.sobolevInclusion_ofTest`). -/
theorem sobolevInclusion_mem_testSpan (hts : t ≤ s) {U : H^{s}(V)} (hU : U ∈ testSpan s Ω) :
    sobolevInclusion hts U ∈ testSpan t Ω := by
  refine apply_mem_testSpan_of_forall (sobolevInclusion hts).toLinearMap (fun φ => ?_) hU
  rw [ContinuousLinearMap.coe_coe, sobolevInclusion_ofTest]
  exact Submodule.subset_span ⟨φ, rfl⟩

/-! ### The inclusion `H^s(Ω) ⊆ H^t(Ω)` -/

/-- **The inclusion `H^s(Ω) ⊆ H^t(Ω)`** for `t ≤ s` and an open set `Ω`: `u ↦ (ι_{t,s} u)|_Ω`,
the inclusion `ι_{t,s}` of `u ∈ H^s(Ω) ⊆ H^s(V)` followed by the restriction to `Ω`. It is an
injective bounded operator of norm at most `1` (`Rd.restrictionInclusion_injective`,
`Rd.norm_restrictionInclusion_apply_le`) and commutes with restriction
(`Rd.restrictionInclusion_restrictProj`). -/
noncomputable def restrictionInclusion (hts : t ≤ s) (Ω : Opens V) :
    RestrictionSpace s Ω →L[ℂ] RestrictionSpace t Ω :=
  restrictProj t Ω ∘L sobolevInclusion hts ∘L (vanishOn s Ω)ᗮ.subtypeL

/-- `restrictionInclusion hts Ω u = (ι_{t,s} u)|_Ω`. -/
theorem restrictionInclusion_apply (hts : t ≤ s) (u : RestrictionSpace s Ω) :
    restrictionInclusion hts Ω u = restrictProj t Ω (sobolevInclusion hts (u : H^{s}(V))) :=
  rfl

/-- **The inclusion has norm at most `1`**: `‖(ι_{t,s} u)|_Ω‖ ≤ ‖u‖`
(`Rd.norm_restrictProj_apply_le`, `Rd.norm_sobolevInclusion_apply_le`). -/
theorem norm_restrictionInclusion_apply_le (hts : t ≤ s) (u : RestrictionSpace s Ω) :
    ‖restrictionInclusion hts Ω u‖ ≤ ‖u‖ :=
  (norm_restrictProj_apply_le _).trans (norm_sobolevInclusion_apply_le hts _)

/-- **The inclusion `H^s(Ω) ⊆ H^t(Ω)` is injective**: if `(ι_{t,s} u)|_Ω = 0`, then
`ι_{t,s} u` vanishes on `Ω` (`Rd.restrictProj_eq_zero_iff`), hence so does `u`
(`Rd.sobolevInclusion_mem_vanishOn_iff`); `u` also lies in `H^s(Ω)`, the orthogonal complement
of the elements vanishing on `Ω`, so `u = 0` (Mathlib's `Submodule.inf_orthogonal_eq_bot`). -/
theorem restrictionInclusion_injective (hts : t ≤ s) :
    Function.Injective (restrictionInclusion hts Ω) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  rw [restrictionInclusion_apply, restrictProj_eq_zero_iff,
    sobolevInclusion_mem_vanishOn_iff] at hu
  have h : (u : H^{s}(V)) ∈ vanishOn s Ω ⊓ (vanishOn s Ω)ᗮ := ⟨hu, u.2⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h
  exact Subtype.ext h

/-- **The inclusion commutes with restriction**: for `t ≤ s` and `U ∈ H^s(V)`,
`ι_{t,s}(U|_Ω) = (ι_{t,s} U)|_Ω` in `H^t(Ω)`. `U|_Ω - U` vanishes on `Ω`
(`Rd.sub_restrictProj_mem`), hence so does its inclusion (`Rd.sobolevInclusion_mem_vanishOn`),
which the restriction maps to `0` (`Rd.restrictProj_eq_zero_iff`). -/
theorem restrictionInclusion_restrictProj (hts : t ≤ s) (U : H^{s}(V)) :
    restrictionInclusion hts Ω (restrictProj s Ω U) =
      restrictProj t Ω (sobolevInclusion hts U) := by
  have h : (restrictProj s Ω U : H^{s}(V)) - U ∈ vanishOn s Ω := by
    simpa using neg_mem (sub_restrictProj_mem (Ω := Ω) U)
  have h' := (restrictProj_eq_zero_iff (Ω := Ω) _).2 (sobolevInclusion_mem_vanishOn hts h)
  rw [map_sub, map_sub, sub_eq_zero] at h'
  exact h'

/-- **The inclusion `H^s(Ω) ⊆ H^t(Ω)` has dense range**: its range contains the restrictions
`(ι_{t,s} U)|_Ω` (`Rd.restrictionInclusion_restrictProj`), which are dense, since `ι_{t,s}` has
dense range (`Rd.denseRange_sobolevInclusion`) and the restriction is continuous and onto
(`Rd.restrictProj_surjective`). -/
theorem denseRange_restrictionInclusion (hts : t ≤ s) :
    DenseRange (restrictionInclusion hts Ω) := by
  have h : DenseRange (restrictProj t Ω ∘ sobolevInclusion (V := V) hts) :=
    (restrictProj_surjective (s := t) (Ω := Ω)).denseRange.comp
      (denseRange_sobolevInclusion hts) (restrictProj t Ω).continuous
  refine h.mono ?_
  rintro _ ⟨U, rfl⟩
  exact ⟨restrictProj s Ω U, restrictionInclusion_restrictProj hts U⟩

/-- **The inclusion maps `H^s_0(Ω)` into `H^t_0(Ω)`**: for `t ≤ s`, the restriction of a test
span element `U ∈ T^s(Ω)` goes to `(ι_{t,s} U)|_Ω` (`Rd.restrictionInclusion_restrictProj`),
the restriction of an element of `T^t(Ω)` (`Rd.sobolevInclusion_mem_testSpan`); `H^s_0(Ω)` is the
closure of these restrictions, and the preimage of the closed `H^t_0(Ω)` is closed. -/
theorem restrictionInclusion_mem_zeroBoundarySpace (hts : t ≤ s) {u : RestrictionSpace s Ω}
    (hu : u ∈ zeroBoundarySpace s Ω) : restrictionInclusion hts Ω u ∈ zeroBoundarySpace t Ω := by
  have hc : zeroBoundarySpace s Ω ≤
      (zeroBoundarySpace t Ω).comap (restrictionInclusion hts Ω : _ →ₗ[ℂ] _) := by
    refine Submodule.topologicalClosure_minimal _ ?_
      ((isClosed_zeroBoundarySpace t Ω).preimage (restrictionInclusion hts Ω).continuous)
    rintro _ ⟨U, hU, rfl⟩
    change restrictionInclusion hts Ω (restrictProj s Ω U) ∈ zeroBoundarySpace t Ω
    rw [restrictionInclusion_restrictProj]
    exact Submodule.le_topologicalClosure _
      (Submodule.mem_map_of_mem (sobolevInclusion_mem_testSpan hts hU))
  exact hc hu

/-! ### Derivatives of test functions and of vanishing elements -/

/-- **The derivative of a test function**: for a real test function `φ` of `Ω`, every real `s`
and every `v`, `∂_v φ` computed in `H^{s+1}(V) → H^s(V)` is the test function `∂_v φ` in
`H^s(V)`. Both have the tempered distribution `∂_v φ` (`Rd.toDistr_sobolevLineDeriv`, Mathlib's
`TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq`, `Rd.lineDerivOp_testSchwartz`). -/
theorem sobolevLineDeriv_ofTest (s : ℝ) (v : V) (φ : 𝓓(Ω, ℝ)) :
    sobolevLineDeriv s v (ofTest (s + 1) φ) = ofTest s (∂_{v} φ) :=
  BesselPotentialSpace.ext (by
    rw [toDistr_sobolevLineDeriv, toDistr_ofTest, toDistr_ofTest, ← lineDerivOp_testSchwartz]
    exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq _ _)

/-- **Derivatives keep the span of the test functions**: `∂_v(T^{s+1}(Ω)) ⊆ T^s(Ω)`, since
`∂_v φ` is a test function of `Ω` for every test function `φ` of `Ω`
(`Rd.sobolevLineDeriv_ofTest`). -/
theorem sobolevLineDeriv_mem_testSpan (s : ℝ) (v : V) {U : H^{s + 1}(V)}
    (hU : U ∈ testSpan (s + 1) Ω) : sobolevLineDeriv s v U ∈ testSpan s Ω := by
  refine apply_mem_testSpan_of_forall (sobolevLineDeriv s v).toLinearMap (fun φ => ?_) hU
  rw [ContinuousLinearMap.coe_coe, sobolevLineDeriv_ofTest]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- **Derivatives keep vanishing on `Ω`**: if `W ∈ H^{s+1}(V)` vanishes on `Ω`, so does
`∂_v W ∈ H^s(V)`, since `(∂_v W)(φ) = -W(∂_v φ)` (Mathlib's
`TemperedDistribution.lineDerivOp_apply_apply`) and `∂_v φ` is a test function of `Ω` for every
test function `φ` of `Ω` (`Rd.lineDerivOp_testSchwartz`). -/
theorem sobolevLineDeriv_mem_vanishOn (s : ℝ) (v : V) {W : H^{s + 1}(V)}
    (hW : W ∈ vanishOn (s + 1) Ω) : sobolevLineDeriv s v W ∈ vanishOn s Ω := by
  rw [mem_vanishOn_iff] at hW ⊢
  intro φ
  rw [toDistr_sobolevLineDeriv, TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    lineDerivOp_testSchwartz, hW, neg_zero]

end Rd
