/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Lipschitz.IndicatorMultiplier
public import FunctionSpaces.Domains.Traces.TildeSpaceSupport
public import FunctionSpaces.Domains.Sobolev.ZeroExtensionBound

/-!
# Zero extensions in `H^s`, `0 ≤ s < 1/2`

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω ⊆ V` a bounded Lipschitz domain and `0 ≤ s < 1/2`. Write `ι_s U` for the `L_2` function of
`U ∈ H^s(V)` (`Rd.sobolevToL2`). Multiplication by `1_Ω` keeps `H^s(V)`: `1_Ω` is a multiplier
of `B^s_{2,2}` (`Rd.BoundedLipschitzDomain.exists_modNorm_indicatorLp_le`), and
`H^s(V) = B^s_{2,2}(V)` with constants (`Rd.modNorm_sobolevToL2_le`,
`Rd.enorm_le_modNorm_sobolevToL2`). Consequently:

* **The zero extension bound** holds at every `0 ≤ s < 1/2`
  (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_lt_half`): for `U ∈ T^s(Ω)` and `W`
  vanishing on `Ω`, `ι_s U = 1_Ω ι_s(U + W)` (`Rd.sobolevToL2_eq_indicatorLp_add`), so
  `‖U‖ ≤ C ‖U + W‖`. Restriction is an isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)`.
* **Zero extensions**: for every `U ∈ H^s(V)` there is `U' ∈ H^s(V)` with `ι_s U' = 1_Ω ι_s U`
  (`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_indicatorLp`); it lies in `H̃^s(Ω)` and has the
  same restriction to `Ω` (`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_sobolevToL2_eq_indicatorLp`,
  `Rd.BoundedLipschitzDomain.restrictProj_eq_of_sobolevToL2_eq_indicatorLp`). Restrictions are
  determined by the `L_2` functions on `Ω` (`Rd.restrictProj_eq_restrictProj_of_ae_eq`,
  `Rd.restrictProj_eq_of_sobolevToL2_ae_eq`).
* **`H̃^s(Ω) = H^s_0(Ω) = H^s(Ω)`**: `H^s_0(Ω)` is all of `H^s(Ω)`
  (`Rd.BoundedLipschitzDomain.zeroBoundarySpace_eq_top_of_lt_half`; Grisvard, Theorem 1.4.2.4;
  McLean, Theorem 3.40), and restriction is an isomorphism of `H̃^s(Ω)` onto `H^s(Ω)`
  (`Rd.BoundedLipschitzDomain.tildeEquivRestrictionSpaceOfLtHalf`; Hewett–Moiola, Lemma 2.1 with
  `H^s_0(Ω) = H^s(Ω)` for `s ≤ 1/2`, p. 3, cf. Remark 2.6; McLean, Theorem 3.33).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Set
open scoped ENNReal BesselPotentialSpace

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {s : ℝ}

/-! ### Restrictions through the `L_2` functions -/

/-- **Restrictions are determined by the `L_2` functions on `Ω`**: for `s ≥ 0`, an open `Ω` and
`U, U' ∈ H^s(V)` with `ι_s U = ι_s U'` almost everywhere on `Ω`, `U|_Ω = U'|_Ω`, since `U - U'`
vanishes on `Ω` (`Rd.mem_vanishOn_iff_sobolevToL2`), the kernel of the restriction
(`Rd.restrictProj_eq_zero_iff`). -/
theorem restrictProj_eq_restrictProj_of_ae_eq (hs : 0 ≤ s) {Ω : Opens V} {U U' : H^{s}(V)}
    (h : (sobolevToL2 hs U : V → ℂ) =ᵐ[volume.restrict (Ω : Set V)] sobolevToL2 hs U') :
    restrictProj s Ω U = restrictProj s Ω U' := by
  have hmem : U - U' ∈ vanishOn s Ω := by
    rw [mem_vanishOn_iff_sobolevToL2 hs, map_sub]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (sobolevToL2 hs U) (sobolevToL2 hs U')), h]
      with x h1 h2
    rw [h1, Pi.sub_apply, h2, sub_self, Pi.zero_apply]
  have h0 := (restrictProj_eq_zero_iff (Ω := Ω) (U - U')).2 hmem
  rwa [map_sub, sub_eq_zero] at h0

/-- **An element of `H^s(Ω)` is the restriction of every element with the same `L_2` function on
`Ω`**: for `s ≥ 0`, `U ∈ H^s(V)` and `u ∈ H^s(Ω)` with `ι_s U = ι_s u` almost everywhere on `Ω`,
`U|_Ω = u` (`Rd.restrictProj_eq_restrictProj_of_ae_eq`, `Rd.restrictProj_coe`). At `s = 1` this is
`Rd.restrictProj_eq_of_ae_eq`. -/
theorem restrictProj_eq_of_sobolevToL2_ae_eq (hs : 0 ≤ s) {Ω : Opens V} {U : H^{s}(V)}
    {u : RestrictionSpace s Ω}
    (h : (sobolevToL2 hs U : V → ℂ) =ᵐ[volume.restrict (Ω : Set V)]
      sobolevToL2 hs (u : H^{s}(V))) :
    restrictProj s Ω U = u :=
  (restrictProj_eq_restrictProj_of_ae_eq hs h).trans (restrictProj_coe u)

/-- **Test functions as cut-offs of their extensions**: for `s ≥ 0`, an open `Ω`, `U ∈ H̃^s(Ω)`
and `W` vanishing on `Ω`, `ι_s U = 1_Ω ι_s(U + W)`, since `ι_s U = 0` almost everywhere outside `Ω`
(`Rd.sobolevToL2_ae_eq_zero_of_mem_tildeSpace`) and `ι_s W = 0` almost everywhere on `Ω`
(`Rd.mem_vanishOn_iff_sobolevToL2`). -/
theorem sobolevToL2_eq_indicatorLp_add (hs : 0 ≤ s) {Ω : Opens V} {U W : H^{s}(V)}
    (hU : U ∈ tildeSpace s Ω) (hW : W ∈ vanishOn s Ω) :
    sobolevToL2 hs U = indicatorLp Ω.isOpen.measurableSet (sobolevToL2 hs (U + W)) := by
  refine Lp.ext ?_
  have hU0 := sobolevToL2_ae_eq_zero_of_mem_tildeSpace hs hU
  have hW0 := (ae_restrict_iff' Ω.isOpen.measurableSet).1
    ((mem_vanishOn_iff_sobolevToL2 hs W).1 hW)
  filter_upwards [indicatorLp_apply_ae Ω.isOpen.measurableSet (sobolevToL2 hs (U + W)),
    Lp.coeFn_add (sobolevToL2 hs U) (sobolevToL2 hs W), hU0, hW0] with x h1 h2 h3 h4
  rw [h1]
  by_cases hx : x ∈ (Ω : Set V)
  · rw [indicator_of_mem hx, map_add, h2, Pi.add_apply, h4 hx, Pi.zero_apply, add_zero]
  · rw [indicator_of_notMem hx, h3 hx]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-! ### The zero extension bound for `0 ≤ s < 1/2` -/

/-- **The zero extension bound for `0 ≤ s < 1/2`**: a bounded Lipschitz domain has the zero
extension bound at `s` with some constant `C`. At `s = 0` this is
`Rd.hasZeroExtensionBound_zero` (`C = 1`). For `0 < s < 1/2`, `U ∈ T^s(Ω)` and `W` vanishing on
`Ω`, `ι_s U = 1_Ω ι_s(U + W)` (`Rd.sobolevToL2_eq_indicatorLp_add`), so
`‖U‖ ≤ c_I N(1_Ω ι_s(U + W)) ≤ c_I C_Ω N(ι_s(U + W)) ≤ c_I C_Ω c_B ‖U + W‖`, where `N` is the
`B^s_{2,2}` quantity of first differences: `Rd.enorm_le_modNorm_sobolevToL2`, the multiplier
theorem `Rd.BoundedLipschitzDomain.exists_modNorm_indicatorLp_le` at `p = q = 2`, `s < 1/2`, and
`Rd.modNorm_sobolevToL2_le`. -/
theorem exists_hasZeroExtensionBound_of_lt_half (hs0 : 0 ≤ s) (hs : s < 1 / 2) :
    ∃ C : ℝ, HasZeroExtensionBound s Ω.toOpens C := by
  rcases hs0.eq_or_lt with rfl | hpos
  · exact ⟨1, hasZeroExtensionBound_zero _⟩
  obtain ⟨CΩ, hCΩ, hmult⟩ := Ω.exists_modNorm_indicatorLp_le (p := 2) two_ne_top hpos
    (by simpa using hs)
  have hs1 : s < ((1 : ℕ) : ℝ) := by
    rw [Nat.cast_one]
    linarith
  set K := sobolevBesovInvConst V s 1 * CΩ * sobolevBesovConst V s 1
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (sobolevBesovInvConst_ne_top s 1) hCΩ)
    (sobolevBesovConst_ne_top hpos hs1)
  refine ⟨K.toReal, fun U hU W hW => ?_⟩
  have hid := sobolevToL2_eq_indicatorLp_add hs0 (Submodule.le_topologicalClosure _ hU) hW
  have h1 := enorm_le_modNorm_sobolevToL2 hs0 1 U
  rw [hid] at h1
  have h : ‖U‖ₑ ≤ K * ‖U + W‖ₑ :=
    calc ‖U‖ₑ ≤ _ := h1
      _ ≤ sobolevBesovInvConst V s 1 * (CΩ * (‖sobolevToL2 hs0 (U + W)‖ₑ + lqNorm 2 (fun k =>
            dyadicWeight s k * lpModulus 2 1 (sobolevToL2 hs0 (U + W)) k))) := by
          gcongr
          exact hmult one_le_two _
      _ ≤ sobolevBesovInvConst V s 1 * (CΩ * (sobolevBesovConst V s 1 * ‖U + W‖ₑ)) := by
          gcongr
          exact modNorm_sobolevToL2_le hpos hs1 (U + W)
      _ = K * ‖U + W‖ₑ := by ring
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top hK enorm_ne_top) h
  rwa [toReal_enorm, ENNReal.toReal_mul, toReal_enorm] at h'

/-! ### Zero extensions and `H̃^s(Ω) = H^s_0(Ω) = H^s(Ω)` -/

/-- **Zero extensions in `H^s(V)` for `0 ≤ s < 1/2`**: for every `U ∈ H^s(V)` there is
`U' ∈ H^s(V)` with `ι_s U' = 1_Ω ι_s U`. At `s = 0` every `L_2` function is `ι_0 U'`
(`Rd.sobolevToL2_zero_surjective`); for `0 < s < 1/2` the multiplier theorem
(`Rd.BoundedLipschitzDomain.exists_modNorm_indicatorLp_le`) and `Rd.modNorm_sobolevToL2_le` give
`1_Ω ι_s U` a finite `B^s_{2,2}` quantity, so it is `ι_s U'`
(`Rd.exists_sobolevToL2_eq_of_modNorm_lt_top`). -/
theorem exists_sobolevToL2_eq_indicatorLp (hs0 : 0 ≤ s) (hs : s < 1 / 2) (U : H^{s}(V)) :
    ∃ U' : H^{s}(V), sobolevToL2 hs0 U' = indicatorLp Ω.measurableSet (sobolevToL2 hs0 U) := by
  rcases hs0.eq_or_lt with rfl | hpos
  · exact sobolevToL2_zero_surjective _
  obtain ⟨CΩ, hCΩ, hmult⟩ := Ω.exists_modNorm_indicatorLp_le (p := 2) two_ne_top hpos
    (by simpa using hs)
  have hs1 : s < ((1 : ℕ) : ℝ) := by
    rw [Nat.cast_one]
    linarith
  have hfin := (hmult one_le_two (sobolevToL2 hpos.le U)).trans_lt (ENNReal.mul_lt_top hCΩ.lt_top
    ((modNorm_sobolevToL2_le hpos hs1 U).trans_lt
      (ENNReal.mul_lt_top (sobolevBesovConst_ne_top hpos hs1).lt_top enorm_lt_top)))
  exact exists_sobolevToL2_eq_of_modNorm_lt_top hpos hs1 hfin

/-- **Zero extensions lie in `H̃^s(Ω)`**: for `s ≥ 0` and `U, U' ∈ H^s(V)` with
`ι_s U' = 1_Ω ι_s U`, `ι_s U'` vanishes outside `Ω`, so `U' ∈ H̃^s(Ω)`
(`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff_of_nonneg`). -/
theorem mem_tildeSpace_of_sobolevToL2_eq_indicatorLp (hs0 : 0 ≤ s) {U U' : H^{s}(V)}
    (h : sobolevToL2 hs0 U' = indicatorLp Ω.measurableSet (sobolevToL2 hs0 U)) :
    U' ∈ tildeSpace s Ω.toOpens := by
  rw [Ω.mem_tildeSpace_iff_of_nonneg hs0, h]
  filter_upwards [indicatorLp_apply_ae Ω.measurableSet (sobolevToL2 hs0 U)] with x hx hxΩ
  rw [hx, indicator_of_notMem hxΩ]

/-- **Zero extensions have the same restriction**: for `s ≥ 0` and `U, U' ∈ H^s(V)` with
`ι_s U' = 1_Ω ι_s U`, `U'|_Ω = U|_Ω`, since `ι_s U' = ι_s U` almost everywhere on `Ω`
(`Rd.restrictProj_eq_restrictProj_of_ae_eq`). -/
theorem restrictProj_eq_of_sobolevToL2_eq_indicatorLp (hs0 : 0 ≤ s) {U U' : H^{s}(V)}
    (h : sobolevToL2 hs0 U' = indicatorLp Ω.measurableSet (sobolevToL2 hs0 U)) :
    restrictProj s Ω.toOpens U' = restrictProj s Ω.toOpens U := by
  refine restrictProj_eq_restrictProj_of_ae_eq hs0 ?_
  rw [h]
  filter_upwards [ae_restrict_of_ae (indicatorLp_apply_ae Ω.measurableSet (sobolevToL2 hs0 U)),
    ae_restrict_mem Ω.measurableSet] with x hx hxΩ
  rw [hx, indicator_of_mem (show x ∈ Ω.carrier from hxΩ)]

/-- **`H^s_0(Ω) = H^s(Ω)` for `0 ≤ s < 1/2`** (Grisvard, Theorem 1.4.2.4; McLean, Theorem 3.40;
Chandler-Wilde, Hewett and Moiola, Corollary 3.29(ix)): every `u ∈ H^s(Ω)` is the restriction of
the zero extension `U'` of `u` (`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_indicatorLp`),
an element of `H̃^s(Ω)`, and restrictions of `H̃^s(Ω)` lie in `H^s_0(Ω)`
(`Rd.range_tildeToRestrictionL_le`). -/
theorem zeroBoundarySpace_eq_top_of_lt_half (hs0 : 0 ≤ s) (hs : s < 1 / 2) :
    zeroBoundarySpace s Ω.toOpens = ⊤ := by
  refine eq_top_iff.2 fun u _ => ?_
  obtain ⟨U', hU'⟩ := Ω.exists_sobolevToL2_eq_indicatorLp hs0 hs (u : H^{s}(V))
  have hmem := Ω.mem_tildeSpace_of_sobolevToL2_eq_indicatorLp hs0 hU'
  have hres := Ω.restrictProj_eq_of_sobolevToL2_eq_indicatorLp hs0 hU'
  rw [restrictProj_coe] at hres
  exact range_tildeToRestrictionL_le (LinearMap.mem_range.2 ⟨⟨U', hmem⟩, hres⟩)

/-- **`H̃^s(Ω) ≅ H^s(Ω)` for `0 ≤ s < 1/2`** (Hewett–Moiola, Lemma 2.1 with `H^s_0(Ω) = H^s(Ω)`
for `s ≤ 1/2`, p. 3, cf. Remark 2.6; McLean, Theorem 3.33):
restriction is an isomorphism of `H̃^s(Ω)` onto `H^s(Ω)`, the isomorphism onto `H^s_0(Ω)` of the
zero extension bound (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_lt_half`,
`Rd.HasZeroExtensionBound.tildeEquivZeroBoundary`) followed by `H^s_0(Ω) = H^s(Ω)`
(`Rd.BoundedLipschitzDomain.zeroBoundarySpace_eq_top_of_lt_half`). -/
noncomputable def tildeEquivRestrictionSpaceOfLtHalf (hs0 : 0 ≤ s) (hs : s < 1 / 2) :
    tildeSpace s Ω.toOpens ≃L[ℂ] RestrictionSpace s Ω.toOpens :=
  (Ω.exists_hasZeroExtensionBound_of_lt_half hs0 hs).choose_spec.tildeEquivZeroBoundary.trans
    (LinearIsometryEquiv.ofTop _ _
      (Ω.zeroBoundarySpace_eq_top_of_lt_half hs0 hs)).toContinuousLinearEquiv

/-- `Ω.tildeEquivRestrictionSpaceOfLtHalf hs0 hs U` is the restriction of `U` to `Ω`. -/
theorem tildeEquivRestrictionSpaceOfLtHalf_apply (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    (U : tildeSpace s Ω.toOpens) :
    Ω.tildeEquivRestrictionSpaceOfLtHalf hs0 hs U = restrictProj s Ω.toOpens U :=
  rfl

end BoundedLipschitzDomain

end Rd
