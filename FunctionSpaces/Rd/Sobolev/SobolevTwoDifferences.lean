/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Sobolev.SobolevScale
public import FunctionSpaces.Rd.Differences.BesovDifferences
public import FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkin

/-!
# `H^s(V)` by differences, with constants

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`s > 0` and `r > s` an integer. Mathlib's Sobolev space `H^s(V)` is the Besov space
`B^s_{2,2}(V)` (`Rd.memSobolev_two_iff_exists_memApprox`); this file gives both directions with
explicit constants, for the `L_2` functions `ι_s U` of `U ∈ H^s(V)` (`Rd.sobolevToL2`) and the
moduli of smoothness of order `r`.

* **`H^s(V) ⊆ B^s_{2,2}(V)`**: `‖ι_s U‖_2 + ‖(2^{ks} ω_r(ι_s U, 2^{-k})_2)_k‖_{ℓ_2} ≤ C ‖U‖`
  with `C = Rd.sobolevBesovConst V s r` (`Rd.modNorm_sobolevToL2_le`).
* **The converse**: `‖U‖ ≤ C' (‖ι_s U‖_2 + ‖(2^{ks} ω_r(ι_s U, 2^{-k})_2)_k‖_{ℓ_2})` with
  `C' = Rd.sobolevBesovInvConst V s r`, for every `s ≥ 0` and every order `r`, informative for
  `s < r` (`Rd.enorm_le_modNorm_sobolevToL2`); for `0 < s < r`, every `F ∈ L_2(V)` with finite
  right side is `ι_s U` for some `U ∈ H^s(V)` (`Rd.exists_sobolevToL2_eq_of_modNorm_lt_top`).
* **Smooth cut-offs**: for `s ≥ 0`, a smooth real `χ` with compact support and `U ∈ H^s(V)`,
  the product `χ ι_s U` is `ι_s W` for some `W ∈ H^s(V)` (`Rd.exists_sobolevToL2_eq_mulLp`): at
  `s = 0` since `ι_0` maps onto `L_2(V)`, for `s > 0` by the moduli of order `⌊s⌋ + 1` and the
  pointwise multiplier theorem.
* **`B^s_{p,2} ⊆ B^{1/2}_{p,1}` for `s > 1/2`**: the `ℓ_1` quantity of smoothness `1/2` is at most
  `‖(2^{-k(s-1/2)})_k‖_{ℓ_2}` times the `ℓ_2` quantity of smoothness `s`
  (`Rd.modNorm_half_one_le_of_lt`), and for `1/2 < s < 2` the `L_2` functions of `H^s(V)` satisfy
  the hypothesis of the trace theorems at smoothness `s - 1/2`, `p = q = 2` and order `2`
  (`Rd.modNorm_sobolevToL2_lt_top`).

At `s = 1` and order `2` the constants are those of `Rd.modNorm_two_le_norm` and
`Rd.enorm_le_modNorm_two`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap BesselPotentialSpace
open ENNReal (lqNorm dyadicWeight dyadicGeomConst)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### `H^s(V) ⊆ B^s_{2,2}(V)` with a constant -/

variable (V) in
/-- **The constant of `H^s(V) ⊆ B^s_{2,2}(V)` for the moduli of order `r`**:
`C_inv · 2 (1 - 2^{-s})⁻¹ · (2 · 4^s)^{1/2}`, the product of the constants of the three inclusions
behind `Rd.modNorm_sobolevToL2_le`: the inverse inequality for the moduli of order `r`
(`ApproximationScheme.ModulusData.inverseConst` of `Rd.bandModulusData`), `F^s_{2,2} ⊆ B^s_{2,2}`
(`Rd.approxNormDyadic_le_triebelLizorkinNorm`) and `H^s ⊆ F^s_{2,2}`
(`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`). At `s = 1`, `r = 2` it is
`Rd.sobolevOneBesovConst V`. -/
noncomputable def sobolevBesovConst (s : ℝ) (r : ℕ) : ℝ≥0∞ :=
  (bandModulusData (V := V) two_ne_top r).inverseConst s *
    (2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * (2 * 4 ^ s) ^ (1 / 2 : ℝ)

/-- The constant of `H^s(V) ⊆ B^s_{2,2}(V)` is finite for `0 < s < r`. -/
theorem sobolevBesovConst_ne_top {s : ℝ} {r : ℕ} (hs : 0 < s) (hsr : s < r) :
    sobolevBesovConst V s r ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top ((bandModulusData two_ne_top r).inverseConst_ne_top hsr)
    (ENNReal.two_mul_one_sub_two_rpow_neg_inv_ne_top hs))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))))

/-- **`H^s(V) ⊆ B^s_{2,2}(V)` with an explicit constant**: for `0 < s < r` and every
`U ∈ H^s(V)` with `L_2` function `ι_s U`,
`‖ι_s U‖_2 + ‖(2^{ks} ω_r(ι_s U, 2^{-k})_2)_k‖_{ℓ_2} ≤ C ‖U‖` with
`C = Rd.sobolevBesovConst V s r`: the moduli are bounded by the band-limited approximation norm
(`ApproximationScheme.ModulusData.modNorm_le_approxNormDyadic`), which is bounded by the norm of
`F^s_{2,2}` (`Rd.approxNormDyadic_le_triebelLizorkinNorm`), which is at most
`(2 · 4^s)^{1/2} ‖J_s ι_s U‖_2` (`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`), and
`J_s ι_s U` is the `L_2` function of `U` (`Rd.besselPotential_sobolevToL2`). -/
theorem modNorm_sobolevToL2_le {s : ℝ} {r : ℕ} (hs : 0 < s) (hsr : s < r) (U : H^{s}(V)) :
    ‖sobolevToL2 hs.le U‖ₑ + lqNorm 2 (fun k => dyadicWeight s k *
      lpModulus 2 r (sobolevToL2 hs.le U) k) ≤ sobolevBesovConst V s r * ‖U‖ₑ := by
  set f := sobolevToL2 hs.le U
  have h1 := (bandModulusData (V := V) two_ne_top r).modNorm_le_approxNormDyadic one_le_two
    hs.le hsr f
  have h2 := approxNormDyadic_le_triebelLizorkinNorm two_ne_top hs one_le_two f
  rw [max_self] at h2
  have h3 := triebelLizorkinNorm_le_of_besselPotential_eq hs.le
    (besselPotential_sobolevToL2 hs.le U)
  rw [U.enorm_toLp_eq] at h3
  calc ‖f‖ₑ + lqNorm 2 (fun k => dyadicWeight s k * lpModulus 2 r f k)
      ≤ (bandModulusData (V := V) two_ne_top r).inverseConst s *
          (bandScheme two_ne_top).approxNormDyadic s 2 f := h1
    _ ≤ (bandModulusData (V := V) two_ne_top r).inverseConst s *
          (2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * triebelLizorkinNorm s 2 f) := by gcongr
    _ ≤ (bandModulusData (V := V) two_ne_top r).inverseConst s *
          (2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * ((2 * 4 ^ s) ^ (1 / 2 : ℝ) * ‖U‖ₑ)) := by
        gcongr
    _ = sobolevBesovConst V s r * ‖U‖ₑ := by
        rw [sobolevBesovConst]
        ring

/-! ### The norm of `H^s(V)` by differences -/

variable (V) in
/-- **The constant of the bound of `H^s(V)` by `B^s_{2,2}(V)` for the moduli of order `r`**:
`(2 · 5^s)^{1/2} · 8 · 2^{3s} ‖Φ‖_1 · D`, the product of the constants of the three inclusions
behind `Rd.enorm_le_modNorm_sobolevToL2`: `F^s_{2,2} ⊆ H^s`
(`Rd.enorm_besselPotential_le_triebelLizorkinNorm`), `A^s_2 ⊆ F^s_{2,2}` for the band-limited
approximation spaces, with the Littlewood–Paley kernel `Φ = Rd.lpKernel`
(`Rd.triebelLizorkinNorm_le_approxNormDyadic`), and Jackson's direction for the moduli of order
`r` (`ApproximationScheme.ModulusData.directConst` of `Rd.bandModulusData`). At `s = 1`, `r = 2`
it is `Rd.sobolevOneInvConst V`. -/
noncomputable def sobolevBesovInvConst (s : ℝ) (r : ℕ) : ℝ≥0∞ :=
  (2 * 5 ^ s) ^ (1 / 2 : ℝ) * (8 * dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume) *
    (bandModulusData (V := V) two_ne_top r).directConst s

/-- The constant of the bound of `H^s(V)` by `B^s_{2,2}(V)` is finite. -/
theorem sobolevBesovInvConst_ne_top (s : ℝ) (r : ℕ) : sobolevBesovInvConst V s r ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))))
    (eight_mul_dyadicWeight_mul_eLpNorm_lpKernel_ne_top s))
    ((bandModulusData two_ne_top r).directConst_ne_top s)

/-- **The norm of `H^s(V)` by the `B^s_{2,2}(V)` quantity, with an explicit constant**, the
converse of `Rd.modNorm_sobolevToL2_le`: for `s ≥ 0`, every order `r` and every `U ∈ H^s(V)` with
`L_2` function `ι_s U`, `‖U‖ ≤ C (‖ι_s U‖_2 + ‖(2^{ks} ω_r(ι_s U, 2^{-k})_2)_k‖_{ℓ_2})` with
`C = Rd.sobolevBesovInvConst V s r`: `‖U‖ = ‖J_s ι_s U‖_2` is at most `(2 · 5^s)^{1/2}` times the
norm of `F^s_{2,2}` (`Rd.enorm_besselPotential_le_triebelLizorkinNorm`), which is bounded by the
band-limited approximation norm (`Rd.triebelLizorkinNorm_le_approxNormDyadic`), which is bounded by
the moduli (`ApproximationScheme.ModulusData.approxNormDyadic_le_modNorm`). The bound is
informative for `s < r`; for `r ≤ s` the right side is infinite unless `U = 0`. -/
theorem enorm_le_modNorm_sobolevToL2 {s : ℝ} (hs : 0 ≤ s) (r : ℕ) (U : H^{s}(V)) :
    ‖U‖ₑ ≤ sobolevBesovInvConst V s r * (‖sobolevToL2 hs U‖ₑ +
      lqNorm 2 (fun k => dyadicWeight s k * lpModulus 2 r (sobolevToL2 hs U) k)) := by
  set f := sobolevToL2 hs U
  have h1 := enorm_besselPotential_le_triebelLizorkinNorm hs (besselPotential_sobolevToL2 hs U)
  rw [U.enorm_toLp_eq] at h1
  have h2 := triebelLizorkinNorm_le_approxNormDyadic two_ne_top hs one_le_two f
  rw [min_self] at h2
  have h3 := (bandModulusData (V := V) two_ne_top r).approxNormDyadic_le_modNorm (s := s)
    one_le_two f
  calc ‖U‖ₑ ≤ (2 * 5 ^ s) ^ (1 / 2 : ℝ) * triebelLizorkinNorm s 2 f := h1
    _ ≤ (2 * 5 ^ s) ^ (1 / 2 : ℝ) *
        (8 * dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          (bandScheme two_ne_top).approxNormDyadic s 2 f) := by gcongr
    _ ≤ (2 * 5 ^ s) ^ (1 / 2 : ℝ) *
        (8 * dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume *
          ((bandModulusData (V := V) two_ne_top r).directConst s *
            (‖f‖ₑ + lqNorm 2 (fun k => dyadicWeight s k * lpModulus 2 r f k)))) := by
        gcongr
        exact h3
    _ = _ := by
        rw [sobolevBesovInvConst]
        ring

/-- **`L_2` functions of finite `B^s_{2,2}` quantity come from `H^s(V)`**: for `0 < s < r` and
`F ∈ L_2(V)` with `‖F‖_2 + ‖(2^{ks} ω_r(F, 2^{-k})_2)_k‖_{ℓ_2} < ∞`, there is `U ∈ H^s(V)` with
`ι_s U = F`: `F` lies in the band-limited approximation space `A^s_2`
(`Rd.memApprox_bandScheme_iff_modulus`), hence in `H^s(V)`
(`Rd.memSobolev_two_iff_exists_memApprox`, Mathlib's
`TemperedDistribution.MemSobolev.toBesselPotentialSpace`). -/
theorem exists_sobolevToL2_eq_of_modNorm_lt_top {s : ℝ} {r : ℕ} (hs : 0 < s) (hsr : s < r)
    {F : Lp ℂ 2 (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight s k * lpModulus 2 r F k) < ∞) :
    ∃ U : H^{s}(V), sobolevToL2 hs.le U = F := by
  have hA := (memApprox_bandScheme_iff_modulus two_ne_top hs.le hsr one_le_two F).2 hF
  have hU := (memSobolev_two_iff_exists_memApprox hs (F : 𝓢'(V, ℂ))).2 ⟨F, rfl, hA⟩
  exact ⟨hU.toBesselPotentialSpace, sobolevToL2_eq_of_toDistr_eq hs.le _
    (TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr hU).symm⟩

/-! ### Smooth cut-offs -/

/-- **Smooth multipliers keep `H^s(V)`, `s ≥ 0`**: for a smooth real `χ` with compact support and
`U ∈ H^s(V)` there is `W ∈ H^s(V)` with `ι_s W = χ ι_s U`. At `s = 0` every `L_2` function is
`ι_0 W` for some `W` (`Rd.sobolevToL2_zero_surjective`). For `s > 0` let `r = ⌊s⌋ + 1 > s`:
`ι_s U` has a finite `B^s_{2,2}` quantity with the moduli of order `r`
(`Rd.modNorm_sobolevToL2_le`), so has `χ ι_s U`, the derivatives of `χ` being bounded
(`Rd.exists_iteratedFDeriv_bound`, `Rd.modNorm_mulLp_lt_top`), and such functions are `ι_s W`
(`Rd.exists_sobolevToL2_eq_of_modNorm_lt_top`). At `s = 1` this is `Rd.exists_toL2_eq_mulLp`. -/
theorem exists_sobolevToL2_eq_mulLp {s : ℝ} (hs : 0 ≤ s) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hcs : HasCompactSupport χ) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) (U : H^{s}(V)) :
    ∃ W : H^{s}(V), sobolevToL2 hs W = mulLp hc hC (sobolevToL2 hs U) := by
  rcases hs.eq_or_lt with rfl | hpos
  · exact sobolevToL2_zero_surjective _
  have hχc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => (χ x : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hsr : s < ((⌊s⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one s
  obtain ⟨D, hD⟩ := exists_iteratedFDeriv_bound hχc (hcs.comp_left Complex.ofReal_zero)
    (⌊s⌋₊ + 1)
  have hF := (modNorm_sobolevToL2_le hpos hsr U).trans_lt
    (ENNReal.mul_lt_top (sobolevBesovConst_ne_top hpos hsr).lt_top enorm_lt_top)
  exact exists_sobolevToL2_eq_of_modNorm_lt_top hpos hsr
    (modNorm_mulLp_lt_top two_ne_top hχc hD hsr one_le_two hF)

/-! ### The quantity of `B^{1/2}_{2,1}` and the trace hypothesis -/

/-- **`B^s_{p,2} ⊆ B^{1/2}_{p,1}` for `s > 1/2`, with the constant of the geometric sequence**:
for `1 ≤ p ≤ ∞`, every order `r` and every `F ∈ L_p(V)`,
`‖F‖_p + ∑_k 2^{k/2} ω_r(F, 2^{-k})_p ≤ c (‖F‖_p + ‖(2^{ks} ω_r(F, 2^{-k})_p)_k‖_{ℓ_2})` with
`c = ‖(2^{-k(s-1/2)})_k‖_{ℓ_2} = ENNReal.dyadicGeomConst (s - 1/2) 2`, by the Cauchy–Schwarz
inequality `∑_k 2^{-k(s-1/2)} (2^{ks} ω_k) ≤ ‖(2^{-k(s-1/2)})_k‖_{ℓ_2} ‖(2^{ks} ω_k)_k‖_{ℓ_2}`
(`ENNReal.lqNorm_one_mul_le`) and `c ≥ 1`. At `s = 1`, `r = 2`, `p = 2` this is
`Rd.modNorm_half_one_le` with `c = √2`. -/
theorem modNorm_half_one_le_of_lt {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : ℝ} (hs : 1 / 2 < s) (r : ℕ)
    (F : Lp ℂ p (volume : Measure V)) :
    ‖F‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus p r F k) ≤
      dyadicGeomConst (s - 1 / 2) 2 *
        (‖F‖ₑ + lqNorm 2 (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  have hw : ∀ k, dyadicWeight (1 / 2) k * lpModulus p r F k =
      dyadicWeight (-(s - 1 / 2)) k * (dyadicWeight s k * lpModulus p r F k) := fun k => by
    rw [← mul_assoc, ← ENNReal.dyadicWeight_add]
    congr 2
    ring
  have hcs : lqNorm 1 (fun k => dyadicWeight (1 / 2) k * lpModulus p r F k) ≤
      dyadicGeomConst (s - 1 / 2) 2 *
        lqNorm 2 (fun k => dyadicWeight s k * lpModulus p r F k) := by
    simp_rw [hw]
    refine (ENNReal.lqNorm_one_mul_le _ _).trans_eq ?_
    rw [ENNReal.lqNorm_dyadicWeight_neg_eq_dyadicGeomConst (by linarith) two_ne_zero]
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left bot_le (ENNReal.one_le_dyadicGeomConst _ _)) hcs

/-- **The hypothesis of the trace theorems for `H^s(V)`, `1/2 < s < 2`**: for every
`U ∈ H^s(V)`, `‖ι_s U‖_2 + ‖(2^{k((s - 1/2) + 1/2)} ω_2(ι_s U, 2^{-k})_2)_k‖_{ℓ_2} < ∞`, the
finiteness that the boundary traces at smoothness `s - 1/2`, `p = q = 2` and order `L = 2` ask
for (`Rd.modNorm_sobolevToL2_le`). The finiteness holds for `0 < s < 2`; `s > 1/2` is the range of
the trace theorems. At `s = 1` this is `Rd.modNorm_toL2_lt_top`. -/
theorem modNorm_sobolevToL2_lt_top {s : ℝ} (hs : 1 / 2 < s) (hs2 : s < 2) (U : H^{s}(V)) :
    ‖sobolevToL2 (one_half_pos.trans hs).le U‖ₑ + lqNorm 2 (fun k =>
      dyadicWeight ((s - 1 / 2) + 1 / (2 : ℝ≥0∞).toReal) k *
        lpModulus 2 2 (sobolevToL2 (one_half_pos.trans hs).le U) k) < ∞ := by
  have hσ : (s - 1 / 2) + 1 / (2 : ℝ≥0∞).toReal = s := by norm_num
  rw [hσ]
  exact (modNorm_sobolevToL2_le (one_half_pos.trans hs) (by exact_mod_cast hs2) U).trans_lt
    (ENNReal.mul_lt_top
      (sobolevBesovConst_ne_top (one_half_pos.trans hs) (by exact_mod_cast hs2)).lt_top
      enorm_lt_top)

end Rd
