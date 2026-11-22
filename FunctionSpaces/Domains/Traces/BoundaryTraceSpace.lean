/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Sobolev.LipschitzDomainH1
public import FunctionSpaces.Rd.Sobolev.SobolevTwoDifferences
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The trace spaces of a bounded Lipschitz domain

Let `Ω` be a bounded Lipschitz domain with boundary `Γ` in a finite-dimensional real inner
product space `V`, such as `ℝ^d`, with Lebesgue measure, `1/2 < s < 3/2`, and `H^s(Ω)` the
Hilbert space `Rd.RestrictionSpace s Ω`; `H^1(Ω)` is `Rd.BoundedLipschitzDomain.SobolevOne`. For
`U ∈ H^s(V)`, `ι_s U` is its `L_2` function (`Rd.sobolevToL2`). The trace space of `H^s(Ω)` is
defined as the orthogonal complement of the trace kernel `ker γ_s` in `H^s(Ω)`, a Hilbert space;
the trace, the extension and the quotient isometry below hold by this definition. The family is
indexed by `s` with the hypotheses `1/2 < s` and `s < 3/2` as explicit arguments, filled in by
`norm_num` for numerals: `Ω.TraceSpace 1` is the trace space of `H^1(Ω)`, whose norm is
equivalent to the norm of `B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`).

* **`H^1(V)` in Besov spaces, with constants**: for `U ∈ H^1(V)` with `L_2` function `ι U`
  (`Rd.toL2`), `‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with an explicit `C`
  (`Rd.modNorm_two_le_norm`), and the `B^{1/2}_{2,1}` quantity is at most `√2` times the
  `B^1_{2,2}` quantity (`Rd.modNorm_half_one_le`, by the Cauchy–Schwarz inequality
  `ENNReal.lqNorm_one_mul_le` and `‖(2^(-k/2))_k‖_{ℓ_2} = √2`,
  `ENNReal.lqNorm_two_dyadicWeight_neg_half`); together `H^1(V) ⊆ B^{1/2}_{2,1}(V)` with
  constant `√2 C` (`Rd.modNorm_half_one_le_norm`). Conversely
  `‖U‖ ≤ C' (‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2})` with an explicit `C'`
  (`Rd.enorm_le_modNorm_two`). The trace of `H^1(V)` on one Lipschitz
  graph is bounded (`Rd.LipschitzGraph.exists_enorm_trace_toL2_le`): a bounded operator
  `H^1(V) → L_2(H)` (`Rd.LipschitzGraph.traceH1`), equal to `w ∘ γ` for Schwartz functions `w`
  (`Rd.LipschitzGraph.traceH1_ofSchwartz_ae`).
* **`H^s(V)` in `B^{1/2}_{2,1}(V)`, `1/2 < s < 2`**: for `U ∈ H^s(V)` with `L_2` function `ι_s U`
  (`Rd.sobolevToL2`), `‖ι_s U‖_2 + ∑_k 2^(k/2) ω_2(ι_s U, 2^(-k))_2 ≤ c C ‖U‖` with explicit
  `c` and `C` (`Rd.modNorm_half_one_le_norm_of_lt`), so the trace of `H^s(V)` on one Lipschitz
  graph is bounded (`Rd.LipschitzGraph.exists_enorm_trace_sobolevToL2_le`).
* **Chart traces**: `u ↦ Tr_j(ψ_j ι_s u)` is a bounded operator from `H^s(Ω)` to `L_2` of the
  hyperplane of the chart `j` (`Rd.BoundedLipschitzDomain.chartTrace`), for the canonical
  resolution of unity `Rd.BoundedLipschitzDomain.boundaryPartition`.
* **The trace kernel**: `Rd.BoundedLipschitzDomain.traceKer` is the closed subspace of the
  `u ∈ H^s(Ω)` whose boundary trace vanishes almost everywhere on `Γ`, for every resolution of
  unity (`Rd.BoundedLipschitzDomain.mem_traceKer_iff`). The restriction to `Ω` keeps the boundary
  trace (`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`).
* **The trace space of `H^s(Ω)`** is its orthogonal complement
  (`Rd.BoundedLipschitzDomain.TraceSpace`), with the trace `Rd.BoundedLipschitzDomain.trace`, the
  orthogonal projection, and the extension `Rd.BoundedLipschitzDomain.extend`, the inclusion:
  `trace ∘ extend = id`, both have norm at most `1`, the kernel of the trace is the trace kernel,
  and `H^s(Ω) ⧸ traceKer` is isometrically isomorphic to the trace space
  (`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`). Two elements of `H^s(Ω)` have the same
  trace iff their boundary traces agree almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.trace_eq_iff`), and the boundary traces of the elements of the trace
  space are the functions of `B^{s-1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
  `Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`).
* **The dual of the trace space** (`Rd.BoundedLipschitzDomain.DualTraceSpace`) is
  conjugate-linearly isometric to it by Riesz (`Rd.BoundedLipschitzDomain.dualTraceEquiv`), and
  the adjoint of the trace is the extension (`Rd.BoundedLipschitzDomain.adjoint_trace`).
* **The case `s = 1` with `Rd.toL2`**: the statements for `H^1(Ω)` with the `L_2` function
  `Rd.toL2` (`Rd.BoundedLipschitzDomain.mem_traceKer_one_iff`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj_one`,
  `Rd.BoundedLipschitzDomain.trace_one_eq_iff`).

The statements about `U ∈ H^s(V)` (`Rd.BoundedLipschitzDomain.exists_enorm_trace_localize_le`,
`Rd.BoundedLipschitzDomain.BoundaryPartition.intrinsicNorm_localize_lt_top`,
`Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_sub`,
`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`) hold for `1/2 < s < 2`, the range of
`Rd.modNorm_sobolevToL2_lt_top`; they take the hypotheses `1/2 < s < 3/2` of the family, for one
calling convention.
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal SchwartzMap BesselPotentialSpace InnerProductSpace
open TemperedDistribution (besselPotential)
open ENNReal (lqNorm dyadicWeight)

/-! ### A sum of dyadic weights -/

namespace ENNReal

/-- `‖(2^(-k/2))_k‖_{ℓ_2} = √2`, since `∑_k 2^(-k) = 2`. -/
theorem lqNorm_two_dyadicWeight_neg_half :
    lqNorm 2 (dyadicWeight (-(1 / 2))) = 2 ^ (1 / 2 : ℝ) := by
  rw [ENNReal.lqNorm_eq_tsum two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  simp_rw [ENNReal.dyadicWeight_rpow]
  norm_num [ENNReal.tsum_dyadicWeight_neg_one]

end ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### `H^1(V)` in Besov spaces, with constants -/

/-- **`B^1_{2,2}(V) ⊆ B^{1/2}_{2,1}(V)` with constant `√2`**: for every `F ∈ L_2(V)`,
`‖F‖_2 + ∑_k 2^(k/2) ω_2(F, 2^(-k))_2 ≤ √2 (‖F‖_2 + ‖(2^k ω_2(F, 2^(-k))_2)_k‖_{ℓ_2})`, by the
Cauchy–Schwarz inequality `∑_k 2^(-k/2) (2^k ω_k) ≤ ‖(2^(-k/2))_k‖_{ℓ_2} ‖(2^k ω_k)_k‖_{ℓ_2}`. The
left side is the norm in which the trace on a Lipschitz graph domain is bounded
(`Rd.LipschitzGraph.enorm_trace_le`). -/
theorem modNorm_half_one_le (F : Lp ℂ 2 (volume : Measure V)) :
    ‖F‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus 2 2 F k) ≤
      2 ^ (1 / 2 : ℝ) * (‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 F k)) := by
  have hw : ∀ k, dyadicWeight (1 / 2) k * lpModulus 2 2 F k =
      dyadicWeight (-(1 / 2)) k * (dyadicWeight 1 k * lpModulus 2 2 F k) := fun k => by
    rw [← mul_assoc, ← ENNReal.dyadicWeight_add]
    norm_num
  have hcs : lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus 2 2 F k) ≤
      2 ^ (1 / 2 : ℝ) * lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 F k) := by
    simp_rw [hw]
    exact (ENNReal.lqNorm_one_mul_le _ _).trans_eq
      (by rw [ENNReal.lqNorm_two_dyadicWeight_neg_half])
  have h1 : (1 : ℝ≥0∞) ≤ 2 ^ (1 / 2 : ℝ) := ENNReal.one_le_rpow (by norm_num) (by norm_num)
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left bot_le h1) hcs

variable (V) in
/-- **The constant of `H^1(V) ⊆ B^1_{2,2}(V)`**: `C_inv · 2 (1 - 2^(-1))⁻¹ · (2 · 4)^{1/2}`, the
product of the constants of the three inclusions behind `Rd.modNorm_two_le_norm`: the inverse
inequality for the moduli of order `2` (`ApproximationScheme.ModulusData.inverseConst` of
`Rd.bandModulusData`), `F^1_{2,2} ⊆ B^1_{2,2}` (`Rd.approxNormDyadic_le_triebelLizorkinNorm`) and
`H^1 ⊆ F^1_{2,2}` (`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`). -/
noncomputable def sobolevOneBesovConst : ℝ≥0∞ :=
  (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
    (2 * (1 - (2 : ℝ≥0∞) ^ (-1 : ℝ))⁻¹) * (2 * 4 ^ (1 : ℝ)) ^ (1 / 2 : ℝ)

/-- The constant of `H^1(V) ⊆ B^1_{2,2}(V)` is finite. -/
theorem sobolevOneBesovConst_ne_top : sobolevOneBesovConst V ≠ ∞ := by
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ((bandModulusData two_ne_top 2).inverseConst_ne_top (by norm_num))
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top one_pos)))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg zero_le_one (by norm_num))))

/-- **`H^1(V) ⊆ B^1_{2,2}(V)` with an explicit constant**: for every `U ∈ H^1(V)` with `L_2`
function `ι U`, `‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with
`C = Rd.sobolevOneBesovConst V`: the moduli are bounded by the band-limited approximation norm
(`ApproximationScheme.ModulusData.modNorm_le_approxNormDyadic`), which is bounded by the norm of
`F^1_{2,2}` (`Rd.approxNormDyadic_le_triebelLizorkinNorm`), which is at most
`(2 · 4)^{1/2} ‖J_1 ι U‖_2` (`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`), and
`‖J_1 ι U‖_2 = ‖U‖` (`BesselPotentialSpace.enorm_toLp_eq`). -/
theorem modNorm_two_le_norm (U : H^{1}(V)) :
    ‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k) ≤
      sobolevOneBesovConst V * ‖U‖ₑ := by
  have hfh : besselPotential V ℂ 1 ((toL2 U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (U.toLp : 𝓢'(V, ℂ)) := by
    rw [toTemperedDistribution_toL2]
    exact U.bessel_toDistr_eq_toLp
  have h1 := (bandModulusData (V := V) two_ne_top 2).modNorm_le_approxNormDyadic one_le_two
    zero_le_one (by norm_num) (toL2 U)
  have h2 := approxNormDyadic_le_triebelLizorkinNorm two_ne_top one_pos one_le_two (toL2 U)
  rw [max_self] at h2
  have h3 := triebelLizorkinNorm_le_of_besselPotential_eq zero_le_one hfh
  rw [U.enorm_toLp_eq] at h3
  calc ‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k)
      ≤ (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
          (bandScheme two_ne_top).approxNormDyadic 1 2 (toL2 U) := h1
    _ ≤ (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
          (2 * (1 - (2 : ℝ≥0∞) ^ (-1 : ℝ))⁻¹ * triebelLizorkinNorm 1 2 (toL2 U)) := by gcongr
    _ ≤ (bandModulusData (V := V) two_ne_top 2).inverseConst 1 *
          (2 * (1 - (2 : ℝ≥0∞) ^ (-1 : ℝ))⁻¹ * ((2 * 4 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) * ‖U‖ₑ)) := by
        gcongr
    _ = sobolevOneBesovConst V * ‖U‖ₑ := by
        rw [sobolevOneBesovConst]
        ring

variable (V) in
/-- **The constant of the bound of `H^1(V)` by `B^1_{2,2}(V)`**:
`(2 · 5)^{1/2} · 8 · 8 ‖Φ‖_1 · D`, the product of the constants of the three inclusions behind
`Rd.enorm_le_modNorm_two`: `F^1_{2,2} ⊆ H^1` (`Rd.enorm_besselPotential_le_triebelLizorkinNorm`),
`A^1_2 ⊆ F^1_{2,2}` for the band-limited approximation spaces, with the Littlewood–Paley kernel
`Φ = Rd.lpKernel` (`Rd.triebelLizorkinNorm_le_approxNormDyadic`), and Jackson's direction for the
moduli of order `2` (`ApproximationScheme.ModulusData.directConst` of `Rd.bandModulusData`). -/
noncomputable def sobolevOneInvConst : ℝ≥0∞ :=
  (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) *
    (8 * dyadicWeight 1 3 * eLpNorm (lpKernel (V := V)) 1 volume) *
      (bandModulusData (V := V) two_ne_top 2).directConst 1

/-- The constant of the bound of `H^1(V)` by `B^1_{2,2}(V)` is finite. -/
theorem sobolevOneInvConst_ne_top : sobolevOneInvConst V ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg zero_le_one (by norm_num))))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.dyadicWeight_ne_top 1 3))
      eLpNorm_lpKernel_ne_top))
    ((bandModulusData two_ne_top 2).directConst_ne_top 1)

/-- **The norm of `H^1(V)` by the `B^1_{2,2}(V)` quantity, with an explicit constant**, the
converse of `Rd.modNorm_two_le_norm`: for every `U ∈ H^1(V)` with `L_2` function `ι U`,
`‖U‖ ≤ C (‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2})` with `C = Rd.sobolevOneInvConst V`:
`‖U‖ = ‖J_1 ι U‖_2` (`BesselPotentialSpace.enorm_toLp_eq`) is at most `(2 · 5)^{1/2}` times the
norm of `F^1_{2,2}` (`Rd.enorm_besselPotential_le_triebelLizorkinNorm`), which is bounded by the
band-limited approximation norm (`Rd.triebelLizorkinNorm_le_approxNormDyadic`), which is bounded by
the moduli (`ApproximationScheme.ModulusData.approxNormDyadic_le_modNorm`). -/
theorem enorm_le_modNorm_two (U : H^{1}(V)) :
    ‖U‖ₑ ≤ sobolevOneInvConst V *
      (‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k)) := by
  have hfh : besselPotential V ℂ 1 ((toL2 U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (U.toLp : 𝓢'(V, ℂ)) := by
    rw [toTemperedDistribution_toL2]
    exact U.bessel_toDistr_eq_toLp
  have h1 := enorm_besselPotential_le_triebelLizorkinNorm zero_le_one hfh
  rw [U.enorm_toLp_eq] at h1
  have h2 := triebelLizorkinNorm_le_approxNormDyadic two_ne_top zero_le_one one_le_two (toL2 U)
  rw [min_self] at h2
  have h3 := (bandModulusData (V := V) two_ne_top 2).approxNormDyadic_le_modNorm (s := 1)
    one_le_two (toL2 U)
  calc ‖U‖ₑ ≤ (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) * triebelLizorkinNorm 1 2 (toL2 U) := h1
    _ ≤ (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) *
        (8 * dyadicWeight 1 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          (bandScheme two_ne_top).approxNormDyadic 1 2 (toL2 U)) := by gcongr
    _ ≤ (2 * 5 ^ (1 : ℝ)) ^ (1 / 2 : ℝ) *
        (8 * dyadicWeight 1 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          ((bandModulusData (V := V) two_ne_top 2).directConst 1 *
            (‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight 1 k * lpModulus 2 2 (toL2 U) k)))) := by
        gcongr
        exact h3
    _ = _ := by
        rw [sobolevOneInvConst]
        ring

/-- **`H^1(V) ⊆ B^{1/2}_{2,1}(V)` with an explicit constant**: for every `U ∈ H^1(V)` with `L_2`
function `ι U`, `‖ι U‖_2 + ∑_k 2^(k/2) ω_2(ι U, 2^(-k))_2 ≤ √2 C ‖U‖` with
`C = Rd.sobolevOneBesovConst V` (`Rd.modNorm_half_one_le`, `Rd.modNorm_two_le_norm`). The left
side bounds the traces on Lipschitz graph domains (`Rd.LipschitzGraph.enorm_trace_le`). -/
theorem modNorm_half_one_le_norm (U : H^{1}(V)) :
    ‖toL2 U‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus 2 2 (toL2 U) k) ≤
      2 ^ (1 / 2 : ℝ) * sobolevOneBesovConst V * ‖U‖ₑ := by
  rw [mul_assoc]
  exact (modNorm_half_one_le _).trans (mul_le_mul' le_rfl (modNorm_two_le_norm U))

/-- **The hypothesis of the trace theorems for `H^1(V)`**: for every `U ∈ H^1(V)`,
`‖ι U‖_2 + ‖(2^(k(1/2 + 1/2)) ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} < ∞`, the finiteness that the boundary
traces at `s = 1/2`, `p = q = 2` and order `L = 2` ask for (`Rd.modNorm_two_le_norm`). -/
theorem modNorm_toL2_lt_top (U : H^{1}(V)) :
    ‖toL2 U‖ₑ + lqNorm 2 (fun k => dyadicWeight (1 / 2 + 1 / (2 : ℝ≥0∞).toReal) k *
      lpModulus 2 2 (toL2 U) k) < ∞ := by
  have hσ : (1 / 2 : ℝ) + 1 / (2 : ℝ≥0∞).toReal = 1 := by norm_num
  rw [hσ]
  exact (modNorm_two_le_norm U).trans_lt
    (ENNReal.mul_lt_top sobolevOneBesovConst_ne_top.lt_top enorm_lt_top)

/-- **The trace of `H^1(V)` on a Lipschitz graph is bounded**: `‖Tr ι U‖_{L_2(H)} ≤ C ‖U‖` for every
`U ∈ H^1(V)` with `L_2` function `ι U` (`Rd.toL2`), with `C = K √2 Rd.sobolevOneBesovConst V` for
the constant `K` of the trace bound in the `B^{1/2}_{2,1}` quantity
(`Rd.LipschitzGraph.enorm_trace_le`, `Rd.modNorm_half_one_le_norm`). -/
theorem LipschitzGraph.exists_enorm_trace_toL2_le (Ω : LipschitzGraph V) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : H^{1}(V), ‖Ω.trace two_ne_top 2 (toL2 U)‖ₑ ≤ C * ‖U‖ₑ := by
  obtain ⟨K, hK, hle⟩ := Ω.enorm_trace_le two_ne_top 2
  refine ⟨K * (2 ^ (1 / 2 : ℝ) * sobolevOneBesovConst V), ENNReal.mul_ne_top hK
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num))
      sobolevOneBesovConst_ne_top), fun U => ?_⟩
  have hw : 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  have h1 := hle (toL2 U)
  rw [hw] at h1
  rw [mul_assoc]
  exact h1.trans (mul_le_mul' le_rfl (modNorm_half_one_le_norm U))

/-! ### The trace of `H^1(V)` on a Lipschitz graph as an operator -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The `L_2` functions of `H^1(V)` satisfy the hypothesis of the trace theorem on `Ω` at
`s = 1/2`, `p = q = 2` and order `2` (`Rd.modNorm_toL2_lt_top`). -/
theorem intrinsicNorm_toL2_lt_top (U : H^{1}(V)) :
    Ω.intrinsicNorm two_ne_top 2 (1 / 2 + 1 / (2 : ℝ≥0∞).toReal) 2 (toL2 U) < ∞ :=
  (Ω.intrinsicNorm_lt_top_of_modNorm two_ne_top 2 one_le_two (modNorm_toL2_lt_top U)).2

/-- The trace of `H^1(V)` on the graph as a linear map, `U ↦ Tr(ι U)` for the `L_2` function
`ι U` (`Rd.LipschitzGraph.trace_sub`, `Rd.LipschitzGraph.trace_smul`). -/
noncomputable def traceH1Linear : H^{1}(V) →ₗ[ℂ] Lp ℂ 2 (volume : Measure Ω.hyperplane) where
  toFun U := Ω.trace two_ne_top 2 (toL2 U)
  map_add' U W := by
    have h := Ω.trace_sub two_ne_top 2 (s := 1 / 2) (by norm_num) one_le_two
      (Ω.intrinsicNorm_toL2_lt_top (U + W)) (Ω.intrinsicNorm_toL2_lt_top W)
    rw [map_add, add_sub_cancel_right] at h
    rw [map_add, h, sub_add_cancel]
  map_smul' c U := by
    simp only [map_smul, RingHom.id_apply, LipschitzGraph.trace_smul]

/-- **The trace of `H^1(V)` on a Lipschitz graph** as a bounded operator `H^1(V) → L_2(H)`,
`U ↦ Tr(ι U)` (`Rd.LipschitzGraph.exists_enorm_trace_toL2_le`). -/
noncomputable def traceH1 : H^{1}(V) →L[ℂ] Lp ℂ 2 (volume : Measure Ω.hyperplane) :=
  (Ω.traceH1Linear).mkContinuousOfExistsBound (by
    obtain ⟨C, hC, hle⟩ := Ω.exists_enorm_trace_toL2_le
    refine ⟨C.toReal, fun U => ?_⟩
    rw [← toReal_enorm, ← toReal_enorm U, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC enorm_ne_top) (hle U))

/-- `traceH1 U = Tr(ι U)`. -/
theorem traceH1_apply (U : H^{1}(V)) : Ω.traceH1 U = Ω.trace two_ne_top 2 (toL2 U) :=
  rfl

/-- **The trace of a Schwartz function** is its restriction to the graph: `Tr w = w ∘ γ` almost
everywhere on `H` (`Rd.LipschitzGraph.trace_ae_eq_comp_graphMap`). -/
theorem traceH1_ofSchwartz_ae (w : 𝓢(V, ℂ)) :
    (Ω.traceH1 (ofSchwartz 1 w) : Ω.hyperplane → ℂ) =ᵐ[volume] fun x' => w (Ω.graphMap x') := by
  rw [traceH1_apply]
  refine Ω.trace_ae_eq_comp_graphMap two_ne_top (L := 2) one_le_two (s := 1 / 2) (by norm_num)
    one_le_two (Ω.intrinsicNorm_lt_top_of_modNorm two_ne_top 2 one_le_two
      (modNorm_toL2_lt_top (ofSchwartz 1 w))).1 w.continuous ?_
  rw [toL2_ofSchwartz]
  exact w.coeFn_toLp 2 volume

end LipschitzGraph

/-! ### `H^s(V)` in `B^{1/2}_{2,1}(V)` and the trace of `H^s(V)` on a Lipschitz graph -/

/-- **`H^s(V) ⊆ B^{1/2}_{2,1}(V)` with an explicit constant**, `1/2 < s < 2`: for every
`U ∈ H^s(V)` with `L_2` function `ι_s U` (`Rd.sobolevToL2`),
`‖ι_s U‖_2 + ∑_k 2^(k/2) ω_2(ι_s U, 2^(-k))_2 ≤ c C ‖U‖` with
`c = ‖(2^{-k(s-1/2)})_k‖_{ℓ_2}` (`Rd.modNorm_half_one_le_of_lt`) and
`C = Rd.sobolevBesovConst V s 2` (`Rd.modNorm_sobolevToL2_le`, differences of order `2 > s`). The
left side bounds the traces on Lipschitz graph domains (`Rd.LipschitzGraph.enorm_trace_le`). At
`s = 1` the corresponding bound with `√2 Rd.sobolevOneBesovConst V` is
`Rd.modNorm_half_one_le_norm`. -/
theorem modNorm_half_one_le_norm_of_lt {s : ℝ} (hs : 1 / 2 < s) (hs2 : s < 2) (U : H^{s}(V)) :
    ‖sobolevToL2 (one_half_pos.trans hs).le U‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k *
      lpModulus 2 2 (sobolevToL2 (one_half_pos.trans hs).le U) k) ≤
        ENNReal.dyadicGeomConst (s - 1 / 2) 2 * sobolevBesovConst V s 2 * ‖U‖ₑ := by
  rw [mul_assoc]
  exact (modNorm_half_one_le_of_lt hs 2 _).trans (mul_le_mul' le_rfl
    (modNorm_sobolevToL2_le (one_half_pos.trans hs) (by exact_mod_cast hs2) U))

/-- **The trace of `H^s(V)` on a Lipschitz graph is bounded**, `1/2 < s < 2`:
`‖Tr ι_s U‖_{L_2(H)} ≤ C ‖U‖` for every `U ∈ H^s(V)` with `L_2` function `ι_s U`
(`Rd.sobolevToL2`), with `C = K c Rd.sobolevBesovConst V s 2` for the constant `K` of the trace
bound in the `B^{1/2}_{2,1}` quantity (`Rd.LipschitzGraph.enorm_trace_le`) and
`c = ‖(2^{-k(s-1/2)})_k‖_{ℓ_2}` (`Rd.modNorm_half_one_le_norm_of_lt`). -/
theorem LipschitzGraph.exists_enorm_trace_sobolevToL2_le (Ω : LipschitzGraph V) {s : ℝ}
    (hs : 1 / 2 < s) (hs2 : s < 2) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : H^{s}(V),
      ‖Ω.trace two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)‖ₑ ≤ C * ‖U‖ₑ := by
  obtain ⟨K, hK, hle⟩ := Ω.enorm_trace_le two_ne_top 2
  have hs0 : 0 < s := one_half_pos.trans hs
  have hsr : s < ((2 : ℕ) : ℝ) := by exact_mod_cast hs2
  refine ⟨K * (ENNReal.dyadicGeomConst (s - 1 / 2) 2 * sobolevBesovConst V s 2),
    ENNReal.mul_ne_top hK (ENNReal.mul_ne_top (ENNReal.dyadicGeomConst_ne_top (sub_pos.2 hs) 2)
      (sobolevBesovConst_ne_top hs0 hsr)), fun U => ?_⟩
  have hw : 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  have h1 := hle (sobolevToL2 hs0.le U)
  rw [hw] at h1
  rw [mul_assoc K]
  exact h1.trans (mul_le_mul' le_rfl (modNorm_half_one_le_norm_of_lt hs hs2 U))

/-! ### The chart traces of `H^s(Ω)`, `1/2 < s < 3/2` -/

namespace BoundedLipschitzDomain

/-- **The Sobolev space `H^1(Ω)`** of a bounded Lipschitz domain, as a Hilbert space: the
restriction space `Rd.RestrictionSpace 1 Ω` of the open set `Ω`. `Rd.restrictL2` identifies its
elements with the restrictions to `Ω` of the functions of `Rd.BoundedLipschitzDomain.MemSobolevOn`
(`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`). -/
abbrev SobolevOne (Ω : BoundedLipschitzDomain V) := RestrictionSpace 1 Ω.toOpens

/-- **The canonical resolution of unity** on the boundary of `Ω`, a fixed choice among the
nonnegative resolutions of `Rd.BoundedLipschitzDomain.exists_boundaryPartition_nonneg`: `ψ_j ≥ 0`
and `∑_j ψ_j ≤ 1` everywhere. The trace kernel uses it and does not depend on it
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff`); the surface measure and the unit normal use its
nonnegativity. -/
noncomputable def boundaryPartition (Ω : BoundedLipschitzDomain V) : Ω.BoundaryPartition :=
  Ω.exists_boundaryPartition_nonneg.choose

omit [MeasurableSpace V] [BorelSpace V] in
/-- The functions of the canonical resolution of unity are nonnegative. -/
theorem boundaryPartition_nonneg (Ω : BoundedLipschitzDomain V) (j : Fin Ω.N) (y : V) :
    0 ≤ Ω.boundaryPartition.toFun j y :=
  Ω.exists_boundaryPartition_nonneg.choose_spec.1 j y

omit [MeasurableSpace V] [BorelSpace V] in
/-- The functions of the canonical resolution of unity sum to at most `1` everywhere. -/
theorem sum_boundaryPartition_le_one (Ω : BoundedLipschitzDomain V) (y : V) :
    ∑ j, Ω.boundaryPartition.toFun j y ≤ 1 :=
  Ω.exists_boundaryPartition_nonneg.choose_spec.2 y

namespace BoundaryPartition

variable {Ω : BoundedLipschitzDomain V} (ψ : Ω.BoundaryPartition)

/-- **A bound of the derivatives of `ψ_j`** up to order `2`, a choice among the bounds of
`Rd.exists_iteratedFDeriv_bound` (smooth functions with compact support). -/
noncomputable def derivBound (j : Fin Ω.N) : ℝ :=
  (exists_iteratedFDeriv_bound (ψ.contDiff_toComplex j) (ψ.hasCompactSupport_toComplex j) 2).choose

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivatives of `ψ_j` of order at most `2` are bounded by `ψ.derivBound j`. -/
theorem derivBound_spec (j : Fin Ω.N) :
    ∀ l ≤ 2, ∀ x, ‖iteratedFDeriv ℝ l (ψ.toComplex j) x‖ ≤ ψ.derivBound j :=
  (exists_iteratedFDeriv_bound (ψ.contDiff_toComplex j) (ψ.hasCompactSupport_toComplex j)
    2).choose_spec

omit [MeasurableSpace V] [BorelSpace V] in
/-- `|ψ_j| ≤ D_j` for the derivative bound `D_j = ψ.derivBound j`. -/
theorem enorm_toComplex_le (j : Fin Ω.N) (y : V) :
    ‖ψ.toComplex j y‖ₑ ≤ ENNReal.ofReal (ψ.derivBound j) := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j) y)

omit [MeasurableSpace V] [BorelSpace V] in
/-- `ψ_j` is Lipschitz: `|ψ_j(x) - ψ_j(y)| ≤ D_j |x - y|` for the derivative bound
`D_j = ψ.derivBound j` (`Rd.norm_higherDiff_le_of_iteratedFDeriv` with differences of order
`1`). -/
theorem enorm_toComplex_sub_le (j : Fin Ω.N) (x y : V) :
    ‖ψ.toComplex j x - ψ.toComplex j y‖ₑ ≤ ENNReal.ofReal (ψ.derivBound j) * ‖x - y‖ₑ := by
  have h := norm_higherDiff_le_of_iteratedFDeriv (ψ.contDiff_toComplex j) (l := 1)
    (fun z => ψ.derivBound_spec j 1 (by norm_num) z) (x - y) y
  simp only [Function.iterate_one, fwdDiff, add_sub_cancel, pow_one] at h
  have hD : 0 ≤ ψ.derivBound j :=
    (norm_nonneg _).trans (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j) y)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal h

/-- **Localisation to the chart `j`**: `F ↦ ψ_j F` on `L_2(V)` (`Rd.mulLp`). -/
noncomputable def localize (j : Fin Ω.N) (F : Lp ℂ 2 (volume : Measure V)) :
    Lp ℂ 2 (volume : Measure V) :=
  mulLp (ψ.contDiff_toComplex j).continuous
    (norm_le_of_iteratedFDeriv_le (ψ.derivBound_spec j)) F

/-- **Localisations of `H^s(V)` functions satisfy the trace hypothesis**, `1/2 < s < 3/2`: for
every resolution of unity `ψ` and `U ∈ H^s(V)` with `L_2` function `ι_s U`, the intrinsic norm of
`ψ_j ι_s U` of smoothness `(s - 1/2) + 1/2` on the graph domain of every chart `k` is finite
(`Rd.modNorm_mulLp_lt_top`, `Rd.modNorm_sobolevToL2_lt_top`). -/
theorem intrinsicNorm_localize_lt_top (j k : Fin Ω.N) (s : ℝ) (U : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.graph k).intrinsicNorm two_ne_top 2 (s - 1 / 2 + 1 / (2 : ℝ≥0∞).toReal) 2
      (ψ.localize j (sobolevToL2 (one_half_pos.trans hs).le U)) < ∞ :=
  ((Ω.graph k).intrinsicNorm_lt_top_of_modNorm two_ne_top 2 one_le_two
    (modNorm_mulLp_lt_top two_ne_top (ψ.contDiff_toComplex j)
      (ψ.derivBound_spec j) (by norm_num; linarith) one_le_two
      (modNorm_sobolevToL2_lt_top hs (by linarith) U))).2

end BoundaryPartition

variable (Ω : BoundedLipschitzDomain V)

/-- **The chart trace as a linear map**, `1/2 < s < 3/2`: `u ↦ Tr_j(ψ_j ι_s u)` from `H^s(Ω)` to
`L_2(H_j)`, with the trace of the graph domain of the chart `j`, the canonical resolution of unity
and the `L_2` function `ι_s u` (`Rd.sobolevToL2`). It is additive by `Rd.LipschitzGraph.trace_sub`
on the localised `H^s(V)` functions and homogeneous by `Rd.LipschitzGraph.trace_smul` and
`Rd.mulLp_smul`. -/
noncomputable def chartTraceLinear (j : Fin Ω.N) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    RestrictionSpace s Ω.toOpens →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Ω.graph j).hyperplane) where
  toFun u := (Ω.graph j).trace two_ne_top 2
    (Ω.boundaryPartition.localize j (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V))))
  map_add' u w := by
    have hs0 : 0 ≤ s := (one_half_pos.trans hs).le
    have h := (Ω.graph j).trace_sub two_ne_top 2 (s := s - 1 / 2) (sub_pos.2 hs) one_le_two
      (Ω.boundaryPartition.intrinsicNorm_localize_lt_top j j s ((u : H^{s}(V)) + w) hs hs')
      (Ω.boundaryPartition.intrinsicNorm_localize_lt_top j j s w hs hs')
    have he : Ω.boundaryPartition.localize j (sobolevToL2 hs0 ((u : H^{s}(V)) + w)) -
        Ω.boundaryPartition.localize j (sobolevToL2 hs0 (w : H^{s}(V))) =
          Ω.boundaryPartition.localize j (sobolevToL2 hs0 (u : H^{s}(V))) := by
      rw [BoundaryPartition.localize, BoundaryPartition.localize, ← mulLp_sub, map_add,
        add_sub_cancel_right]
      rfl
    rw [he] at h
    rw [Submodule.coe_add, h, sub_add_cancel]
  map_smul' c u := by
    simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, BoundaryPartition.localize,
      mulLp_smul, LipschitzGraph.trace_smul]

/-- `chartTraceLinear Ω j s u = Tr_j(ψ_j ι_s u)`. -/
theorem chartTraceLinear_apply (j : Fin Ω.N) (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.chartTraceLinear j s hs hs' u = (Ω.graph j).trace two_ne_top 2
      (Ω.boundaryPartition.localize j (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V)))) :=
  rfl

/-- **The chart traces are bounded**, `1/2 < s < 3/2`: `‖Tr_j(ψ_j ι_s U)‖_{L_2(H_j)} ≤ C ‖U‖` for
every `U ∈ H^s(V)`, for every resolution of unity `ψ`, with
`C = K M c Rd.sobolevBesovConst V s 2`. The trace is at most `K` times the `B^{1/2}_{2,1}`
quantity of `ψ_j ι_s U` (`Rd.LipschitzGraph.enorm_trace_le`), which is at most `M` times that of
`ι_s U` (`Rd.modNorm_mulLp_le`, with the multiplier constant `M = Rd.multiplierTotal` of `ψ_j` for
differences of order `2` and smoothness `1/2`), which is at most
`c Rd.sobolevBesovConst V s 2 ‖U‖` with `c = ‖(2^{-k(s-1/2)})_k‖_{ℓ_2}`
(`Rd.modNorm_half_one_le_norm_of_lt`). -/
theorem exists_enorm_trace_localize_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : H^{s}(V),
      ‖(Ω.graph j).trace two_ne_top 2 (ψ.localize j (sobolevToL2 (one_half_pos.trans hs).le U))‖ₑ ≤
        C * ‖U‖ₑ := by
  obtain ⟨K, hK, hle⟩ := (Ω.graph j).enorm_trace_le two_ne_top 2
  have hs0 : 0 < s := one_half_pos.trans hs
  have hs2 : s < ((2 : ℕ) : ℝ) := by norm_num; linarith
  refine ⟨K * multiplierTotal (V := V) two_ne_top 2 (1 / 2) (ψ.derivBound j) *
      ENNReal.dyadicGeomConst (s - 1 / 2) 2 * sobolevBesovConst V s 2,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK
      (multiplierTotal_ne_top two_ne_top (by norm_num) _))
      (ENNReal.dyadicGeomConst_ne_top (sub_pos.2 hs) 2)) (sobolevBesovConst_ne_top hs0 hs2),
    fun U => ?_⟩
  have hw : 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  have h1 := hle (ψ.localize j (sobolevToL2 hs0.le U))
  rw [hw] at h1
  have h2 : ‖ψ.localize j (sobolevToL2 hs0.le U)‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k *
      lpModulus 2 2 (ψ.localize j (sobolevToL2 hs0.le U)) k) ≤
        multiplierTotal (V := V) two_ne_top 2 (1 / 2) (ψ.derivBound j) *
          (‖sobolevToL2 hs0.le U‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k *
            lpModulus 2 2 (sobolevToL2 hs0.le U) k)) :=
    modNorm_mulLp_le two_ne_top (ψ.contDiff_toComplex j) (ψ.derivBound_spec j) (s := 1 / 2)
      (by norm_num) le_rfl _
  have h3 := modNorm_half_one_le_norm_of_lt hs (by linarith) U
  calc _ ≤ _ := h1
    _ ≤ K * (multiplierTotal (V := V) two_ne_top 2 (1 / 2) (ψ.derivBound j) *
          (ENNReal.dyadicGeomConst (s - 1 / 2) 2 * sobolevBesovConst V s 2 * ‖U‖ₑ)) :=
        mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl h3))
    _ = _ := by ring

/-- **The chart traces are bounded operators**, `1/2 < s < 3/2`: `u ↦ Tr_j(ψ_j ι_s u)` from
`H^s(Ω)` to `L_2(H_j)`, with the canonical resolution of unity
(`Rd.BoundedLipschitzDomain.exists_enorm_trace_localize_le`). -/
noncomputable def chartTrace (j : Fin Ω.N) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    RestrictionSpace s Ω.toOpens →L[ℂ] Lp ℂ 2 (volume : Measure (Ω.graph j).hyperplane) :=
  (Ω.chartTraceLinear j s hs hs').mkContinuousOfExistsBound (by
    obtain ⟨C, hC, hle⟩ := Ω.exists_enorm_trace_localize_le Ω.boundaryPartition j s hs hs'
    refine ⟨C.toReal, fun u => ?_⟩
    rw [← toReal_enorm, ← toReal_enorm u, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC enorm_ne_top) (hle (u : H^{s}(V))))

/-- `chartTrace Ω j s u = Tr_j(ψ_j ι_s u)`. -/
theorem chartTrace_apply (j : Fin Ω.N) (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.chartTrace j s hs hs' u = (Ω.graph j).trace two_ne_top 2
      (Ω.boundaryPartition.localize j (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V)))) :=
  rfl

/-- **The chart trace is the localised boundary trace**:
`Tr_j(ψ_j ι_s u) = (ψ_j Tr_Γ ι_s u) ∘ γ_j` almost everywhere on `H_j`, with the canonical
resolution of unity
(`Rd.BoundedLipschitzDomain.trace_mulLp_ae_boundaryTrace`). -/
theorem chartTrace_ae_eq (j : Fin Ω.N) (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.chartTrace j s hs hs' u : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume] fun x' =>
      Ω.boundaryPartition.toComplex j ((Ω.graph j).graphMap x') *
        Ω.boundaryTrace Ω.boundaryPartition two_ne_top 2
          (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V))) ((Ω.graph j).graphMap x') :=
  Ω.trace_mulLp_ae_boundaryTrace Ω.boundaryPartition two_ne_top one_le_two (sub_pos.2 hs)
    (by norm_num; linarith) one_le_two
    (modNorm_sobolevToL2_lt_top hs (by linarith) _) j
    (Ω.boundaryPartition.derivBound_spec j)

/-! ### The trace kernel -/

/-- **Vanishing on the boundary, chart by chart**: for every resolution of unity `ψ`, a function
`T` vanishes almost everywhere on `Γ` iff `(ψ_j T) ∘ γ_j = 0` almost everywhere on `H_j` for every
`j`. `⇐`: the localised statements hold almost everywhere on `Γ ∩ B_j`
(`Rd.BoundedLipschitzDomain.eventually_aeBoundary_of_chart`), and `T = ∑_j ψ_j T` on `Γ`. -/
theorem eventuallyEq_zero_iff_forall_chart (ψ : Ω.BoundaryPartition) (T : V → ℂ) :
    T =ᶠ[Ω.aeBoundary] 0 ↔ ∀ j, (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      T ((Ω.graph j).graphMap x')) =ᵐ[(volume : Measure (Ω.graph j).hyperplane)] 0 := by
  constructor
  · intro h j
    filter_upwards [Ω.eventually_aeBoundary_iff.1 h j] with x' hx
    by_cases hψ : ψ.toFun j ((Ω.graph j).graphMap x') = 0
    · simp [ψ.toComplex_of_eq_zero hψ]
    · simp [hx (ψ.mem_ball_of_ne_zero hψ)]
  · intro h
    have hk : ∀ k, ∀ᶠ y in Ω.aeBoundary,
        y ∈ ball (Ω.center k) (Ω.radius k) → ψ.toComplex k y * T y = 0 := fun k =>
      Ω.eventually_aeBoundary_of_chart k ((h k).mono fun x' hx _ => hx)
    have hΓ : ∀ᶠ y in Ω.aeBoundary, y ∈ frontier Ω.carrier :=
      Ω.eventually_aeBoundary_iff.2 fun j =>
        Eventually.of_forall fun x' hx => Ω.graphMap_mem_frontier j hx
    filter_upwards [eventually_all.2 hk, hΓ] with y hy hyΓ
    calc T y = ∑ k, ψ.toComplex k y * T y := by
          rw [← Finset.sum_mul, ψ.sum_toComplex_eq_one hyΓ, one_mul]
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          by_cases hψ : ψ.toFun k y = 0
          · rw [ψ.toComplex_of_eq_zero hψ, zero_mul]
          · exact hy k (ψ.mem_ball_of_ne_zero hψ)

/-- **The trace kernel** `ker γ_s ⊆ H^s(Ω)`, `1/2 < s < 3/2`: the `u` whose chart traces
`Tr_j(ψ_j u)` all vanish, for the canonical resolution of unity; equivalently, the `u` whose
boundary trace vanishes almost everywhere on `Γ`, for every resolution of unity
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff`). -/
noncomputable def traceKer (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : Submodule ℂ (RestrictionSpace s Ω.toOpens) :=
  ⨅ j, (Ω.chartTrace j s hs hs').ker

/-- The trace kernel is closed, an intersection of kernels of bounded operators. -/
theorem isClosed_traceKer (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    IsClosed (Ω.traceKer s hs hs' : Set (RestrictionSpace s Ω.toOpens)) := by
  rw [traceKer, Submodule.coe_iInf]
  exact isClosed_iInter fun j => ContinuousLinearMap.isClosed_ker _

/-- The trace kernel is complete, as a closed subspace of the Hilbert space `H^s(Ω)`; hence it
has an orthogonal projection. -/
instance completeSpace_traceKer {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2} :
    CompleteSpace (Ω.traceKer s hs hs') :=
  (Ω.isClosed_traceKer s hs hs').completeSpace_coe

/-- **The trace kernel by the boundary trace**: for every resolution of unity `ψ`, `u ∈ H^s(Ω)`
lies in the trace kernel iff its boundary trace `Tr_Γ ι_s u` vanishes almost everywhere on `Γ`. In
particular the trace kernel does not depend on the resolution of unity in its definition. The
chart traces are the localised boundary traces (`Rd.BoundedLipschitzDomain.chartTrace_ae_eq`),
`Rd.BoundedLipschitzDomain.eventuallyEq_zero_iff_forall_chart` collects them, and the boundary
traces of two resolutions agree almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`). -/
theorem mem_traceKer_iff (ψ : Ω.BoundaryPartition) (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    u ∈ Ω.traceKer s hs hs' ↔ Ω.boundaryTrace ψ two_ne_top 2
      (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V))) =ᶠ[Ω.aeBoundary] 0 := by
  have hψ := Ω.boundaryTrace_eventuallyEq Ω.boundaryPartition ψ two_ne_top one_le_two
    (sub_pos.2 hs) (by norm_num; linarith) one_le_two
    (modNorm_sobolevToL2_lt_top hs (by linarith) (u : H^{s}(V)))
  rw [traceKer, Submodule.mem_iInf, ← (Filter.EventuallyEq.congr_left hψ),
    eventuallyEq_zero_iff_forall_chart Ω Ω.boundaryPartition]
  refine forall_congr' fun j => ?_
  rw [LinearMap.mem_ker, Lp.eq_zero_iff_ae_eq_zero]
  exact ⟨fun h => (Ω.chartTrace_ae_eq j s u hs hs').symm.trans h,
    fun h => (Ω.chartTrace_ae_eq j s u hs hs').trans h⟩

/-- **The trace kernel of `H^1(Ω)` by the boundary trace**, the case `s = 1` of
`Rd.BoundedLipschitzDomain.mem_traceKer_iff` with the `L_2` function `Rd.toL2`
(`Rd.sobolevToL2_one`). -/
theorem mem_traceKer_one_iff (ψ : Ω.BoundaryPartition) (u : Ω.SobolevOne) :
    u ∈ Ω.traceKer 1 ↔
      Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u : H^{1}(V))) =ᶠ[Ω.aeBoundary] 0 := by
  rw [Ω.mem_traceKer_iff ψ 1 u, sobolevToL2_one]

/-- **The boundary trace of `H^s(V)` functions is linear**, `1/2 < s < 3/2`: for every resolution
of unity `ψ` and `U, W ∈ H^s(V)`, `Tr_Γ ι_s(U - W) = Tr_Γ ι_s U - Tr_Γ ι_s W` almost everywhere on
`Γ`, since `ι_s(U - W) + ι_s W = ι_s U` and the boundary trace is additive
(`Rd.BoundedLipschitzDomain.boundaryTrace_add`, `Rd.modNorm_sobolevToL2_lt_top`). -/
theorem boundaryTrace_sobolevToL2_sub (ψ : Ω.BoundaryPartition) (s : ℝ) (U W : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le (U - W))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U) -
        Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le W) := by
  have hs0 : 0 ≤ s := (one_half_pos.trans hs).le
  have h := Ω.boundaryTrace_add ψ two_ne_top (sub_pos.2 hs) (by norm_num; linarith) one_le_two
    (modNorm_sobolevToL2_lt_top hs (by linarith) (U - W))
    (modNorm_sobolevToL2_lt_top hs (by linarith) W)
  have hUW : sobolevToL2 hs0 (U - W) + sobolevToL2 hs0 W = sobolevToL2 hs0 U := by
    rw [← map_add, sub_add_cancel]
  rw [hUW] at h
  filter_upwards [h] with y hy
  rw [Pi.sub_apply, hy, Pi.add_apply, add_sub_cancel_right]

/-- **The restriction to `Ω` keeps the boundary trace**, `1/2 < s < 3/2`: for every resolution of
unity `ψ` and `U ∈ H^s(V)`, `Tr_Γ ι_s(U|_Ω) = Tr_Γ ι_s U` almost everywhere on `Γ`, since
`U - U|_Ω` vanishes on `Ω` (`Rd.sub_restrictProj_mem`, `Rd.mem_vanishOn_iff_sobolevToL2`) and the
boundary trace depends only on the function on `Ω`
(`Rd.BoundedLipschitzDomain.boundaryTrace_congr`). -/
theorem boundaryTrace_restrictProj (ψ : Ω.BoundaryPartition) (s : ℝ) (U : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le
        ((restrictProj s Ω.toOpens U : RestrictionSpace s Ω.toOpens) : H^{s}(V)))
      =ᶠ[Ω.aeBoundary]
        Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U) := by
  have hs0 : 0 ≤ s := (one_half_pos.trans hs).le
  have h := (mem_vanishOn_iff_sobolevToL2 hs0 _).1
    (sub_restrictProj_mem (s := s) (Ω := Ω.toOpens) U)
  rw [Ω.coe_toOpens] at h
  replace h := (ae_restrict_iff' Ω.measurableSet).1 h
  have hF := fun G : H^{s}(V) => modNorm_sobolevToL2_lt_top hs (by linarith) G
  refine Ω.boundaryTrace_congr ψ two_ne_top one_le_two (sub_pos.2 hs)
    (by norm_num; linarith) one_le_two (hF _) (hF U) ?_
  filter_upwards [h, Lp.coeFn_sub (sobolevToL2 hs0 U)
    (sobolevToL2 hs0 ((restrictProj s Ω.toOpens U : RestrictionSpace s Ω.toOpens) : H^{s}(V)))]
    with x hx hsub hxΩ
  have hx' := hx hxΩ
  rw [map_sub, hsub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx'
  exact hx'.symm

/-- **The restriction to `Ω` keeps the boundary trace of `H^1(V)`**: `Tr_Γ ι(U|_Ω) = Tr_Γ ι U`
almost everywhere on `Γ` for the `L_2` function `Rd.toL2`, the case `s = 1` of
`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj` (`Rd.sobolevToL2_one`). -/
theorem boundaryTrace_restrictProj_one (ψ : Ω.BoundaryPartition) (U : H^{1}(V)) :
    Ω.boundaryTrace ψ two_ne_top 2 (toL2 ((restrictProj 1 Ω.toOpens U : Ω.SobolevOne) : H^{1}(V)))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (toL2 U) := by
  have h := Ω.boundaryTrace_restrictProj ψ 1 U
  rwa [sobolevToL2_one] at h

/-! ### The trace space of `H^s(Ω)` -/

/-- **The trace space of `H^s(Ω)`**, `1/2 < s < 3/2`, of a bounded Lipschitz domain, as a Hilbert
space: the orthogonal complement of the trace kernel in `H^s(Ω)`. The boundary traces of its
elements are the functions of `B^{s-1/2}_{2,2}(Γ)`, up to null sets of `Γ`
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`,
`Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`). For `s = 1` its norm is
equivalent to the norm of `B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`). -/
abbrev TraceSpace (s : ℝ) (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :=
  ↥(Ω.traceKer s hs hs')ᗮ

/-- **The trace** `γ_s : H^s(Ω) → Ω.TraceSpace s`, `1/2 < s < 3/2`, the orthogonal projection onto
the trace space. Two elements of `H^s(Ω)` have the same trace iff their boundary traces agree
almost everywhere on `Γ` (`Rd.BoundedLipschitzDomain.trace_eq_iff`). -/
noncomputable def trace (s : ℝ) (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    RestrictionSpace s Ω.toOpens →L[ℂ] Ω.TraceSpace s hs hs' :=
  (Ω.traceKer s hs hs')ᗮ.orthogonalProjectionOnto

/-- **The extension** `Ω.TraceSpace s → H^s(Ω)`, `1/2 < s < 3/2`, the inclusion of the trace space:
a right inverse of the trace (`Rd.BoundedLipschitzDomain.trace_extend`) and an isometry
(`Rd.BoundedLipschitzDomain.norm_extend_apply`). -/
noncomputable def extend (s : ℝ) (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.TraceSpace s hs hs' →L[ℂ] RestrictionSpace s Ω.toOpens :=
  (Ω.traceKer s hs hs')ᗮ.subtypeL

/-- **The extension is a right inverse of the trace**: `γ_s (E_s t) = t`. -/
@[simp]
theorem trace_extend {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2} (t : Ω.TraceSpace s hs hs') :
    Ω.trace s hs hs' (Ω.extend s hs hs' t) = t :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self t

/-- The trace has norm at most `1`: `‖γ_s u‖ ≤ ‖u‖`. -/
theorem norm_trace_apply_le (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ‖Ω.trace s hs hs' u‖ ≤ ‖u‖ :=
  Submodule.norm_orthogonalProjectionOnto_apply_le _ u

/-- The extension is an isometry: `‖E_s t‖ = ‖t‖`. -/
theorem norm_extend_apply {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2} (t : Ω.TraceSpace s hs hs') :
    ‖Ω.extend s hs hs' t‖ = ‖t‖ :=
  rfl

/-- `γ_s u = 0` iff `u` lies in the trace kernel (Mathlib's
`Submodule.orthogonalProjectionOnto_eq_zero_iff`, `Submodule.orthogonal_orthogonal`). -/
theorem trace_eq_zero_iff (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.trace s hs hs' u = 0 ↔ u ∈ Ω.traceKer s hs hs' := by
  rw [trace, Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]

/-- **The kernel of the trace is the trace kernel**: the kernel of the orthogonal projection onto
`Kᗮ` is `Kᗮᗮ = K` (Mathlib's `Submodule.ker_orthogonalProjectionOnto`,
`Submodule.orthogonal_orthogonal`). -/
theorem ker_trace (s : ℝ) (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.trace s hs hs').ker = Ω.traceKer s hs hs' := by
  rw [trace, Submodule.ker_orthogonalProjectionOnto, Submodule.orthogonal_orthogonal]

/-- `u` and the extension of its trace differ by an element of the trace kernel. -/
theorem sub_extend_trace_mem (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    u - Ω.extend s hs hs' (Ω.trace s hs hs' u) ∈ Ω.traceKer s hs hs' := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (Ω.traceKer s hs hs')ᗮ) u
  rwa [Submodule.orthogonal_orthogonal] at h

/-- **The trace space as a quotient**: `H^s(Ω) ⧸ ker γ_s` is isometrically isomorphic to the trace
space, by the definition of the trace space as an orthogonal complement (Mathlib's
`Submodule.quotientEquivOrthogonal`); the class of `u` corresponds to `γ_s u`
(`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace_mk`). -/
noncomputable def quotientEquivTraceSpace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (RestrictionSpace s Ω.toOpens ⧸ Ω.traceKer s hs hs') ≃ₗᵢ[ℂ] Ω.TraceSpace s hs hs' :=
  Submodule.quotientEquivOrthogonal _

/-- The class of `u` corresponds to its trace. -/
theorem quotientEquivTraceSpace_mk (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.quotientEquivTraceSpace s hs hs' (Submodule.Quotient.mk u) = Ω.trace s hs hs' u := by
  have h : (Submodule.Quotient.mk u : RestrictionSpace s Ω.toOpens ⧸ Ω.traceKer s hs hs') =
      Submodule.Quotient.mk (Ω.extend s hs hs' (Ω.trace s hs hs' u)) :=
    (Submodule.Quotient.eq _).2 (Ω.sub_extend_trace_mem s u hs hs')
  rw [quotientEquivTraceSpace, h]
  exact Submodule.quotientEquivOrthogonal_mk _ _ (Ω.trace s hs hs' u).2

/-! ### The boundary traces of the trace space -/

/-- **Equal traces are equal boundary traces**: for every resolution of unity `ψ`,
`γ_s u = γ_s u'` iff `Tr_Γ ι_s u = Tr_Γ ι_s u'` almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.mem_traceKer_iff` for `u - u'`,
`Rd.BoundedLipschitzDomain.boundaryTrace_sobolevToL2_sub`). -/
theorem trace_eq_iff (ψ : Ω.BoundaryPartition) (s : ℝ) (u u' : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.trace s hs hs' u = Ω.trace s hs hs' u' ↔
      Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V)))
        =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2
          (sobolevToL2 (one_half_pos.trans hs).le (u' : H^{s}(V))) := by
  rw [← sub_eq_zero, ← map_sub, Ω.trace_eq_zero_iff s _ hs hs', Ω.mem_traceKer_iff ψ s _ hs hs',
    Submodule.coe_sub]
  have h := Ω.boundaryTrace_sobolevToL2_sub ψ s (u : H^{s}(V)) u' hs hs'
  exact ⟨fun h' => Filter.eventuallyEq_iff_sub.2 (h.symm.trans h'),
    fun h' => h.trans (Filter.eventuallyEq_iff_sub.1 h')⟩

/-- **Equal traces of `H^1(Ω)` are equal boundary traces**, the case `s = 1` of
`Rd.BoundedLipschitzDomain.trace_eq_iff` with the `L_2` function `Rd.toL2`
(`Rd.sobolevToL2_one`). -/
theorem trace_one_eq_iff (ψ : Ω.BoundaryPartition) (u u' : Ω.SobolevOne) :
    (Ω.trace 1) u = (Ω.trace 1) u' ↔ Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u : H^{1}(V)))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (toL2 (u' : H^{1}(V))) := by
  rw [Ω.trace_eq_iff ψ 1 u u', sobolevToL2_one]

/-- **The extension of the trace has the same boundary trace**: `Tr_Γ ι_s (E_s γ_s u) = Tr_Γ ι_s u`
almost everywhere on `Γ`, for every resolution of unity. -/
theorem boundaryTrace_extend_trace (ψ : Ω.BoundaryPartition) (s : ℝ)
    (u : RestrictionSpace s Ω.toOpens) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le
      ((Ω.extend s hs hs' (Ω.trace s hs hs' u) : RestrictionSpace s Ω.toOpens) : H^{s}(V)))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2
        (sobolevToL2 (one_half_pos.trans hs).le (u : H^{s}(V))) :=
  (Ω.trace_eq_iff ψ s _ _ hs hs').1 (Ω.trace_extend _)

/-- **Elements of the trace space are determined by their boundary traces**: `Tr_Γ ι_s (E_s t)`
and `Tr_Γ ι_s (E_s t')` agree almost everywhere on `Γ` iff `t = t'`. -/
theorem boundaryTrace_extend_eventuallyEq_iff (ψ : Ω.BoundaryPartition) {s : ℝ} {hs : 1 / 2 < s}
    {hs' : s < 3 / 2} (t t' : Ω.TraceSpace s hs hs') :
    Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le
      ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le
        ((Ω.extend s hs hs' t' : RestrictionSpace s Ω.toOpens) : H^{s}(V))) ↔ t = t' := by
  rw [← Ω.trace_eq_iff ψ s _ _ hs hs', trace_extend, trace_extend]

/-- **The boundary trace of `H^s(V)` functions lies in `B^{s-1/2}_{2,2}(Γ)`**, `1/2 < s < 3/2`:
for every resolution of unity `ψ` and `U ∈ H^s(V)`
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_boundaryTrace` at smoothness `s - 1/2`, `p = q = 2`,
`L = 2`). -/
theorem memBoundaryBesov_sobolevToL2 (ψ : Ω.BoundaryPartition) (s : ℝ) (U : H^{s}(V))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2
      (Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)) :=
  Ω.memBoundaryBesov_boundaryTrace ψ two_ne_top one_le_two (sub_pos.2 hs)
    (by linarith) (by norm_num; linarith) one_le_two
    (modNorm_sobolevToL2_lt_top hs (by linarith) U)

/-- **The boundary traces of the trace space lie in `B^{s-1/2}_{2,2}(Γ)`**: for every resolution
of unity `ψ` and `t ∈ Ω.TraceSpace s`, `Tr_Γ ι_s (E_s t) ∈ B^{s-1/2}_{2,2}(Γ)`. -/
theorem memBoundaryBesov_extend (ψ : Ω.BoundaryPartition) {s : ℝ} {hs : 1 / 2 < s}
    {hs' : s < 3 / 2} (t : Ω.TraceSpace s hs hs') :
    Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 (Ω.boundaryTrace ψ two_ne_top 2
      (sobolevToL2 (one_half_pos.trans hs).le
        ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))) :=
  Ω.memBoundaryBesov_sobolevToL2 ψ s _ hs hs'

/-- **Every function of `B^{s-1/2}_{2,2}(Γ)` is the boundary trace of an element of the trace
space**, `1/2 < s < 3/2`: for every resolution of unity `ψ` and `g ∈ B^{s-1/2}_{2,2}(Γ)` there is
`t ∈ Ω.TraceSpace s` with `Tr_Γ ι_s (E_s t) = g` almost everywhere on `Γ`. The bounded extension
(`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq`) gives `F ∈ B^s_{2,2}(V)` with boundary
trace `g`, which is `ι_s U` for some `U ∈ H^s(V)` (`Rd.exists_sobolevToL2_eq_of_modNorm_lt_top`),
and `t = γ_s(U|_Ω)` (`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`). -/
theorem exists_traceSpace_of_memBoundaryBesov (ψ : Ω.BoundaryPartition) (s : ℝ) {g : V → ℂ}
    (hg : Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 g) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    ∃ t : Ω.TraceSpace s hs hs', Ω.boundaryTrace ψ two_ne_top 2
      (sobolevToL2 (one_half_pos.trans hs).le
        ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V))) =ᶠ[Ω.aeBoundary] g := by
  obtain ⟨F, hF, hFg⟩ := Ω.exists_boundaryTrace_eq ψ two_ne_top (L := 2) le_rfl (sub_pos.2 hs)
    (by linarith) one_le_two hg
  have hσ : s - 1 / 2 + 1 / (2 : ℝ≥0∞).toReal = s := by norm_num
  rw [hσ] at hF
  obtain ⟨U, rfl⟩ := exists_sobolevToL2_eq_of_modNorm_lt_top (one_half_pos.trans hs) (r := 2)
    (by norm_num; linarith) hF
  exact ⟨Ω.trace s hs hs' (restrictProj s Ω.toOpens U), ((Ω.boundaryTrace_extend_trace ψ s _ hs
    hs').trans (Ω.boundaryTrace_restrictProj ψ s U hs hs')).trans hFg⟩

/-! ### The dual of the trace space -/

/-- **The dual of the trace space**, `1/2 < s < 3/2`: the bounded linear functionals on
`Ω.TraceSpace s`. Normal traces of vector fields on `Ω` pair with the trace space of `H^1(Ω)`
through this space at `s = 1`. -/
abbrev DualTraceSpace (s : ℝ) (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :=
  StrongDual ℂ (Ω.TraceSpace s hs hs')

/-- **Riesz for the dual of the trace space**: the conjugate-linear isometric isomorphism of the
dual onto the trace space that represents a functional by an element (Mathlib's
`InnerProductSpace.toDual`): `ℓ t = ⟪dualTraceEquiv Ω s ℓ, t⟫`
(`Rd.BoundedLipschitzDomain.dualTraceEquiv_apply`), and this element is the only one with this
property (`Rd.BoundedLipschitzDomain.eq_dualTraceEquiv_of_forall`). -/
noncomputable def dualTraceEquiv (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.DualTraceSpace s hs hs' ≃ₗᵢ⋆[ℂ] Ω.TraceSpace s hs hs' :=
  (InnerProductSpace.toDual ℂ (Ω.TraceSpace s hs hs')).symm

/-- Every functional on the trace space is the inner product with its representing element. -/
theorem dualTraceEquiv_apply {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (ℓ : Ω.DualTraceSpace s hs hs') (t : Ω.TraceSpace s hs hs') :
    ℓ t = ⟪Ω.dualTraceEquiv s hs hs' ℓ, t⟫_ℂ := by
  rw [dualTraceEquiv, InnerProductSpace.toDual_symm_apply]

/-- **The representing element is unique**: if `ℓ t = ⟪t₀, t⟫` for every `t ∈ Ω.TraceSpace s`,
then `t₀ = dualTraceEquiv Ω s ℓ` (Mathlib's `ext_inner_right`). -/
theorem eq_dualTraceEquiv_of_forall {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (ℓ : Ω.DualTraceSpace s hs hs') {t₀ : Ω.TraceSpace s hs hs'} (h : ∀ t, ℓ t = ⟪t₀, t⟫_ℂ) :
    t₀ = Ω.dualTraceEquiv s hs hs' ℓ :=
  ext_inner_right ℂ fun t => by rw [← h, dualTraceEquiv_apply]

/-- **The adjoint of the trace is the extension**: `γ_s* = E_s`, the adjoint of an orthogonal
projection onto a closed subspace is its inclusion (Mathlib's
`Submodule.adjoint_orthogonalProjectionOnto`). -/
theorem adjoint_trace (s : ℝ) (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ContinuousLinearMap.adjoint (Ω.trace s hs hs') = Ω.extend s hs hs' :=
  Submodule.adjoint_orthogonalProjectionOnto _

end BoundedLipschitzDomain

end Rd
