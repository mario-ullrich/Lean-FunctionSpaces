/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Sobolev.SobolevRestrictionInclusions

/-!
# The zero extension bound and `H̃^s(Ω) = H^s_0(Ω)`

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω ⊆ V` open and `s` real. Restriction maps `H̃^s(Ω)`, the closure of the test functions of `Ω`
in `H^s(V)`, into `H^s_0(Ω)`, the closure of their restrictions in `H^s(Ω)`
(`Rd.tildeToRestrictionL`). Following Hewett and Moiola (the list after Lemma 2.9 of their note
on the restriction operator), this file reduces the question whether it is an isomorphism to one
inequality on test functions, and proves that inequality for every integer `s ≥ 0`.

* **The zero extension bound**: `Rd.HasZeroExtensionBound s Ω C` says
  `‖U‖ ≤ C ‖U + W‖` for every `U` in the span `T^s(Ω)` of the test functions and every `W`
  vanishing on `Ω`, Hewett and Moiola's condition (iv). It gives `‖U‖ ≤ C ‖U|_Ω‖` on
  `H̃^s(Ω)` (`Rd.HasZeroExtensionBound.norm_le_norm_restrictProj`), so the range of the
  restriction is closed and equals `H^s_0(Ω)`
  (`Rd.HasZeroExtensionBound.range_tildeToRestrictionL`), and restriction is an isomorphism
  `H̃^s(Ω) ≅ H^s_0(Ω)` with bounds `1` and `C`
  (`Rd.HasZeroExtensionBound.tildeEquivZeroBoundaryOfBound`).
* **Injectivity for `s ≥ 0`**: for every open `Ω`, the `L_2` function of an element of
  `H̃^s(Ω)` vanishes outside `Ω` (`Rd.sobolevToL2_ae_eq_zero_of_mem_tildeSpace`), so restriction
  is injective on `H̃^s(Ω)` (`Rd.eq_zero_of_mem_tildeSpace_of_restrictProj_eq_zero`; Hewett and
  Moiola, Lemma 2.2(iii)).
* **Lifting from `s` to `s + 1`**: the norm recursion
  `(2π)² ‖U‖²_{s+1} = (2π)² ‖ι_{s,s+1} U‖²_s + ∑_i ‖∂_{e_i} U‖²_s`
  (`Rd.sq_norm_eq_add_sum_sobolevLineDeriv`) and derivatives that keep test functions and
  vanishing (`Rd.sobolevLineDeriv_mem_testSpan`, `Rd.sobolevLineDeriv_mem_vanishOn`) carry the
  bound from `s` to `s + 1` with the same constant (`Rd.HasZeroExtensionBound.add_one`), and so
  from `s` to `s + m` for every `m ∈ ℕ` (`Rd.HasZeroExtensionBound.add_natCast`).
* **Integer `s`**: at `s = 0` the bound holds with `C = 1` on every open set, since the `L_2`
  functions of `U` and `W` have disjoint supports (`Rd.hasZeroExtensionBound_zero`); by lifting,
  for every `m ∈ ℕ` (`Rd.hasZeroExtensionBound_natCast`), so restriction is an isometry of
  `H̃^m(Ω)` onto `H^m_0(Ω)` for every open `Ω` (`Rd.tildeEquivZeroBoundaryNat`; Hewett and
  Moiola, Lemma 2.2(iii); Chandler-Wilde, Hewett and Moiola, Lemma 3.31(vi)).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal SchwartzMap Real BesselPotentialSpace Distributions LineDeriv

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {s : ℝ} {Ω : Opens V}

/-! ### Restriction is injective on `H̃^s(Ω)` for `s ≥ 0` -/

/-- **Restriction is injective on `H̃^s(Ω)` for `s ≥ 0`**, for every open `Ω` (Hewett and Moiola,
Lemma 2.2(iii)): if `U ∈ H̃^s(Ω)` and `U|_Ω = 0`, then `U = 0`. Indeed `U` vanishes on `Ω`
(`Rd.restrictProj_eq_zero_iff`), so `ι_s U = 0` almost everywhere on `Ω`
(`Rd.mem_vanishOn_iff_sobolevToL2`), and almost everywhere outside `Ω`
(`Rd.sobolevToL2_ae_eq_zero_of_mem_tildeSpace`); `ι_s` is injective
(`Rd.sobolevToL2_injective`). -/
theorem eq_zero_of_mem_tildeSpace_of_restrictProj_eq_zero (hs : 0 ≤ s) {U : H^{s}(V)}
    (hU : U ∈ tildeSpace s Ω) (h0 : restrictProj s Ω U = 0) : U = 0 := by
  have hΩ := (mem_vanishOn_iff_sobolevToL2 hs U).1 ((restrictProj_eq_zero_iff U).1 h0)
  have hc := sobolevToL2_ae_eq_zero_of_mem_tildeSpace hs hU
  have h2 : sobolevToL2 hs U = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hΩ, hc] with x h1 h2
    by_cases hx : x ∈ (Ω : Set V)
    · exact h1 hx
    · exact h2 hx
  exact sobolevToL2_injective hs (h2.trans (map_zero _).symm)

/-- **Restriction `H̃^s(Ω) → H^s(Ω)` is injective for `s ≥ 0`**, for every open `Ω`
(`Rd.eq_zero_of_mem_tildeSpace_of_restrictProj_eq_zero`). -/
theorem tildeToRestrictionL_injective_of_nonneg (hs : 0 ≤ s) :
    Function.Injective (tildeToRestrictionL s Ω) :=
  (injective_iff_map_eq_zero _).2 fun U hU =>
    Subtype.ext (eq_zero_of_mem_tildeSpace_of_restrictProj_eq_zero hs U.2 hU)

/-! ### The zero extension bound -/

variable (s Ω) in
/-- **The zero extension bound** (Hewett and Moiola's condition (iv), in the list after their
Lemma 2.9): `‖U‖ ≤ C ‖U + W‖` in `H^s(V)` for every `U` in the span `T^s(Ω)` of the test
functions of `Ω` and every `W` vanishing on `Ω`. Since `U + W` runs through all extensions of
`U|_Ω`, it says `‖U‖ ≤ C ‖U|_Ω‖`: extending `U|_Ω` by zero outside `Ω` costs at most the
factor `C`. -/
def HasZeroExtensionBound (C : ℝ) : Prop :=
  ∀ U ∈ testSpan s Ω, ∀ W ∈ vanishOn s Ω, ‖U‖ ≤ C * ‖U + W‖

variable {C : ℝ}

/-- **The bound on test functions**: under the zero extension bound, `‖U‖ ≤ C ‖U|_Ω‖` for
`U ∈ T^s(Ω)`, since `‖U|_Ω‖ = ‖U + W‖` for some `W` vanishing on `Ω`
(`Rd.exists_norm_restrictProj_eq`). -/
theorem HasZeroExtensionBound.norm_le_of_mem_testSpan (h : HasZeroExtensionBound s Ω C)
    {U : H^{s}(V)} (hU : U ∈ testSpan s Ω) : ‖U‖ ≤ C * ‖restrictProj s Ω U‖ := by
  obtain ⟨W, hW, hUW⟩ := exists_norm_restrictProj_eq (Ω := Ω) U
  rw [hUW]
  exact h U hU W hW

/-- **The bound on `H̃^s(Ω)`**: under the zero extension bound, `‖U‖ ≤ C ‖U|_Ω‖` for every
`U ∈ H̃^s(Ω)`, by continuity from the test functions
(`Rd.HasZeroExtensionBound.norm_le_of_mem_testSpan`). -/
theorem HasZeroExtensionBound.norm_le_norm_restrictProj (h : HasZeroExtensionBound s Ω C)
    {U : H^{s}(V)} (hU : U ∈ tildeSpace s Ω) : ‖U‖ ≤ C * ‖restrictProj s Ω U‖ := by
  have hc : IsClosed {U : H^{s}(V) | ‖U‖ ≤ C * ‖restrictProj s Ω U‖} :=
    isClosed_le continuous_norm
      (continuous_const.mul (continuous_norm.comp (restrictProj s Ω).continuous))
  refine closure_minimal (fun U hU => h.norm_le_of_mem_testSpan hU) hc ?_
  rw [← Submodule.topologicalClosure_coe]
  exact hU

/-- **Under the zero extension bound, restriction is injective on `H̃^s(Ω)`**, for every real
`s`: `U|_Ω = 0` gives `‖U‖ ≤ C ‖U|_Ω‖ = 0`
(`Rd.HasZeroExtensionBound.norm_le_norm_restrictProj`). -/
theorem HasZeroExtensionBound.tildeToRestrictionL_injective (h : HasZeroExtensionBound s Ω C) :
    Function.Injective (tildeToRestrictionL s Ω) := by
  refine (injective_iff_map_eq_zero _).2 fun U hU => ?_
  have hb := h.norm_le_norm_restrictProj U.2
  change ‖(U : H^{s}(V))‖ ≤ C * ‖tildeToRestrictionL s Ω U‖ at hb
  rw [hU, norm_zero, mul_zero] at hb
  exact Subtype.ext (norm_le_zero_iff.1 hb)

/-- **Under the zero extension bound, the restrictions of `H̃^s(Ω)` form `H^s_0(Ω)`**: by
`‖U‖ ≤ C ‖U|_Ω‖` (`Rd.HasZeroExtensionBound.norm_le_norm_restrictProj`) the restriction is
antilipschitz on the complete space `H̃^s(Ω)`, so its range is closed (Mathlib's
`AntilipschitzWith.isClosed_range`), and its closure is `H^s_0(Ω)`
(`Rd.closure_range_tildeToRestrictionL`). -/
theorem HasZeroExtensionBound.range_tildeToRestrictionL (h : HasZeroExtensionBound s Ω C) :
    (tildeToRestrictionL s Ω).range = zeroBoundarySpace s Ω := by
  have hK : ∀ U : tildeSpace s Ω,
      ‖U‖ ≤ (C.toNNReal : ℝ) * ‖tildeToRestrictionL s Ω U‖ := fun U =>
    (h.norm_le_norm_restrictProj U.2).trans
      (mul_le_mul_of_nonneg_right C.le_coe_toNNReal (norm_nonneg _))
  have hc : IsClosed ((tildeToRestrictionL s Ω).range : Set (RestrictionSpace s Ω)) :=
    ((tildeToRestrictionL s Ω).antilipschitz_of_bound hK).isClosed_range
      (tildeToRestrictionL s Ω).uniformContinuous
  rw [← closure_range_tildeToRestrictionL]
  exact (IsClosed.submodule_topologicalClosure_eq hc).symm

/-- **Restriction as a linear equivalence `H̃^s(Ω) ≃ H^s_0(Ω)`** under the zero extension bound:
injective (`Rd.HasZeroExtensionBound.tildeToRestrictionL_injective`) with range `H^s_0(Ω)`
(`Rd.HasZeroExtensionBound.range_tildeToRestrictionL`). -/
noncomputable def HasZeroExtensionBound.tildeLinearEquivZeroBoundary
    (h : HasZeroExtensionBound s Ω C) : tildeSpace s Ω ≃ₗ[ℂ] zeroBoundarySpace s Ω :=
  (LinearEquiv.ofInjective (tildeToRestrictionL s Ω : tildeSpace s Ω →ₗ[ℂ] RestrictionSpace s Ω)
    h.tildeToRestrictionL_injective).trans
    (LinearEquiv.ofEq _ _ h.range_tildeToRestrictionL)

/-- The linear equivalence `H̃^s(Ω) ≃ H^s_0(Ω)` is the restriction to `Ω`. -/
theorem HasZeroExtensionBound.coe_tildeLinearEquivZeroBoundary_apply
    (h : HasZeroExtensionBound s Ω C) (U : tildeSpace s Ω) :
    (h.tildeLinearEquivZeroBoundary U : RestrictionSpace s Ω) = restrictProj s Ω U :=
  rfl

/-- **`H̃^s(Ω) ≅ H^s_0(Ω)` under the zero extension bound** (Hewett and Moiola, the list after
Lemma 2.9: (iv) implies (i)): restriction is an isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)`, with
`‖U|_Ω‖ ≤ ‖U‖` (`Rd.norm_restrictProj_apply_le`) and `‖U‖ ≤ C ‖U|_Ω‖`
(`Rd.HasZeroExtensionBound.norm_le_norm_restrictProj`); Mathlib's
`LinearEquiv.toContinuousLinearEquivOfBounds` with the bounds `1` and `C`, no open mapping
theorem. -/
noncomputable def HasZeroExtensionBound.tildeEquivZeroBoundaryOfBound
    (h : HasZeroExtensionBound s Ω C) : tildeSpace s Ω ≃L[ℂ] zeroBoundarySpace s Ω :=
  h.tildeLinearEquivZeroBoundary.toContinuousLinearEquivOfBounds 1 C
    (fun U => by
      rw [one_mul]
      exact norm_restrictProj_apply_le (U : H^{s}(V)))
    (fun u => by
      have hb := h.norm_le_norm_restrictProj (h.tildeLinearEquivZeroBoundary.symm u).2
      rw [← h.coe_tildeLinearEquivZeroBoundary_apply, LinearEquiv.apply_symm_apply] at hb
      exact hb)

/-- `h.tildeEquivZeroBoundaryOfBound U` is the restriction of `U` to `Ω`. -/
theorem HasZeroExtensionBound.coe_tildeEquivZeroBoundaryOfBound_apply
    (h : HasZeroExtensionBound s Ω C) (U : tildeSpace s Ω) :
    (h.tildeEquivZeroBoundaryOfBound U : RestrictionSpace s Ω) = restrictProj s Ω U :=
  rfl

/-- **Under the zero extension bound with `C = 1`, restriction is isometric on `H̃^s(Ω)`**:
`‖U|_Ω‖ ≤ ‖U‖` (`Rd.norm_restrictProj_apply_le`) and
`‖U‖ ≤ ‖U|_Ω‖` (`Rd.HasZeroExtensionBound.norm_le_norm_restrictProj`). -/
theorem HasZeroExtensionBound.norm_restrictProj_eq (h : HasZeroExtensionBound s Ω 1)
    {U : H^{s}(V)} (hU : U ∈ tildeSpace s Ω) : ‖restrictProj s Ω U‖ = ‖U‖ :=
  le_antisymm (norm_restrictProj_apply_le U)
    ((h.norm_le_norm_restrictProj hU).trans_eq (one_mul _))

/-! ### Lifting the bound and integer smoothness -/

variable (Ω) in
/-- **The zero extension bound at `s = 0`, with `C = 1`, on every open set**: for `U ∈ T^0(Ω)`
and `W` vanishing on `Ω`, `‖U‖ = ‖ι_0 U‖_2` (`Rd.norm_sobolevToL2_zero`), `ι_0 U` vanishes
outside `Ω` (`Rd.exists_opens_sobolevToL2_ae_eq_zero`) and `ι_0 W` on `Ω`
(`Rd.mem_vanishOn_iff_sobolevToL2`), so `‖ι_0 U‖_2 ≤ ‖ι_0 U + ι_0 W‖_2`
(`Rd.norm_le_norm_add_of_ae_eq_zero`). -/
theorem hasZeroExtensionBound_zero : HasZeroExtensionBound 0 Ω 1 := by
  intro U hU W hW
  obtain ⟨O, hO, hUO⟩ := exists_opens_sobolevToL2_ae_eq_zero le_rfl hU
  rw [one_mul, ← norm_sobolevToL2_zero U, ← norm_sobolevToL2_zero (U + W), map_add]
  exact norm_le_norm_add_of_ae_eq_zero Ω.isOpen.measurableSet
    (ae_restrict_of_ae_restrict_of_subset hO hUO) ((mem_vanishOn_iff_sobolevToL2 le_rfl W).1 hW)

/-- **Lifting the zero extension bound from `s` to `s + 1`, with the same constant**, for every
real `C`: for `U ∈ T^{s+1}(Ω)` and `W` vanishing on `Ω`, the norm recursion
`(2π)² ‖U‖²_{s+1} = (2π)² ‖ι U‖²_s + ∑_i ‖∂_{e_i} U‖²_s` (`Rd.sq_norm_eq_add_sum_sobolevLineDeriv`)
holds for `U` and for `U + W`. The inclusion and the derivatives map `U` into `T^s(Ω)` and `W`
to elements vanishing on `Ω` (`Rd.sobolevInclusion_mem_testSpan`,
`Rd.sobolevInclusion_mem_vanishOn`, `Rd.sobolevLineDeriv_mem_testSpan`,
`Rd.sobolevLineDeriv_mem_vanishOn`), so the bound at `s` applies to every term. For `C < 0`
the bound at `s` gives `‖ι U‖ ≤ C ‖ι (U + W)‖ ≤ 0`, so `ι U = 0` and `ι (U + W) = 0`, hence
`U = 0` and `U + W = 0` (`Rd.sobolevInclusion_injective`). -/
theorem HasZeroExtensionBound.add_one (h : HasZeroExtensionBound s Ω C) :
    HasZeroExtensionBound (s + 1) Ω C := by
  intro U hU W hW
  have hι : ‖sobolevInclusion (lt_add_one s).le U‖ ≤
      C * ‖sobolevInclusion (lt_add_one s).le (U + W)‖ := by
    rw [map_add]
    exact h _ (sobolevInclusion_mem_testSpan _ hU) _ (sobolevInclusion_mem_vanishOn _ hW)
  rcases lt_or_ge C 0 with hC | hC
  · have h1 := norm_nonneg (sobolevInclusion (lt_add_one s).le U)
    have h2 := norm_nonneg (sobolevInclusion (lt_add_one s).le (U + W))
    have hUW : U + W = 0 := sobolevInclusion_injective (lt_add_one s).le
      (by rw [map_zero, ← norm_eq_zero]; nlinarith)
    have hU0 : U = 0 := sobolevInclusion_injective (lt_add_one s).le
      (by rw [map_zero, ← norm_eq_zero]; nlinarith)
    rw [hUW, hU0]
    simp
  let b := stdOrthonormalBasis ℝ V
  have hsq : ∀ x y : ℝ, 0 ≤ x → x ≤ C * y → x ^ 2 ≤ C ^ 2 * y ^ 2 := fun x y hx hxy => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx hxy 2
  have hd : ∀ i, ‖sobolevLineDeriv s (b i) U‖ ≤ C * ‖sobolevLineDeriv s (b i) (U + W)‖ :=
    fun i => by
      rw [map_add]
      exact h _ (sobolevLineDeriv_mem_testSpan s (b i) hU) _
        (sobolevLineDeriv_mem_vanishOn s (b i) hW)
  have h2 : (2 * π) ^ 2 * ‖U‖ ^ 2 ≤ C ^ 2 * ((2 * π) ^ 2 * ‖U + W‖ ^ 2) := by
    rw [sq_norm_eq_add_sum_sobolevLineDeriv b s U,
      sq_norm_eq_add_sum_sobolevLineDeriv b s (U + W), mul_add, Finset.mul_sum]
    refine add_le_add ?_ (Finset.sum_le_sum fun i _ => hsq _ _ (norm_nonneg _) (hd i))
    calc (2 * π) ^ 2 * ‖sobolevInclusion (lt_add_one s).le U‖ ^ 2
        ≤ (2 * π) ^ 2 * (C ^ 2 * ‖sobolevInclusion (lt_add_one s).le (U + W)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hsq _ _ (norm_nonneg _) hι) (by positivity)
      _ = C ^ 2 * ((2 * π) ^ 2 * ‖sobolevInclusion (lt_add_one s).le (U + W)‖ ^ 2) := by ring
  have h3 : (2 * π) ^ 2 * ‖U‖ ^ 2 ≤ (2 * π) ^ 2 * (C * ‖U + W‖) ^ 2 := h2.trans_eq (by ring)
  have h4 : ‖U‖ ^ 2 ≤ (C * ‖U + W‖) ^ 2 := le_of_mul_le_mul_left h3 (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

/-- **Lifting the zero extension bound by `m ∈ ℕ`, with the same constant**: for every open `Ω`
and every real `C`, the zero extension bound at `s` gives the bound at `s + m`
(`Rd.HasZeroExtensionBound.add_one`, applied `m` times). -/
theorem HasZeroExtensionBound.add_natCast (h : HasZeroExtensionBound s Ω C) (m : ℕ) :
    HasZeroExtensionBound (s + m) Ω C := by
  induction m with
  | zero => rwa [Nat.cast_zero, add_zero]
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc]
    exact ih.add_one

variable (Ω) in
/-- **The zero extension bound for integer smoothness, with `C = 1`, on every open set**: the
bound at `s = 0` (`Rd.hasZeroExtensionBound_zero`) lifted by `m`
(`Rd.HasZeroExtensionBound.add_natCast`). -/
theorem hasZeroExtensionBound_natCast (m : ℕ) : HasZeroExtensionBound m Ω 1 := by
  simpa using (hasZeroExtensionBound_zero Ω).add_natCast m

/-- **`H̃^m(Ω) ≅ H^m_0(Ω)` isometrically, for every open `Ω` and `m ∈ ℕ`** (Hewett and Moiola,
Lemma 2.2(iii); Chandler-Wilde, Hewett and Moiola, Lemma 3.31(vi)): restriction is an isometric
isomorphism of `H̃^m(Ω)` onto `H^m_0(Ω)`, by the zero extension bound with `C = 1`
(`Rd.hasZeroExtensionBound_natCast`, `Rd.HasZeroExtensionBound.tildeLinearEquivZeroBoundary`,
`Rd.HasZeroExtensionBound.norm_restrictProj_eq`). -/
noncomputable def tildeEquivZeroBoundaryNat (m : ℕ) (Ω : Opens V) :
    tildeSpace m Ω ≃ₗᵢ[ℂ] zeroBoundarySpace m Ω where
  toLinearEquiv := (hasZeroExtensionBound_natCast Ω m).tildeLinearEquivZeroBoundary
  norm_map' U := (hasZeroExtensionBound_natCast Ω m).norm_restrictProj_eq U.2

/-- `tildeEquivZeroBoundaryNat m Ω U` is the restriction of `U` to `Ω`. -/
theorem coe_tildeEquivZeroBoundaryNat_apply (m : ℕ) (U : tildeSpace m Ω) :
    (tildeEquivZeroBoundaryNat m Ω U : RestrictionSpace m Ω) = restrictProj m Ω U :=
  rfl

end Rd
