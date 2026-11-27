/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Sobolev.RellichCompactness
public import FunctionSpaces.Rd.Differences.PointwiseMultipliers

/-!
# The scale of Sobolev spaces `H^s(V)`

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure.
Mathlib's Sobolev space `H^s(V) = H^{s,2}(V, ℂ)` (`BesselPotentialSpace`) consists of the
tempered distributions `u` whose Bessel potential `J_s u = 𝓕⁻(⟨ξ⟩^s 𝓕u)` is an `L_2` function,
and `‖u‖_{H^s} = ‖J_s u‖_2`. This file builds the maps between these spaces, for every real `s`.

* **Fourier multipliers of `L_2` functions**: if `𝓕h = w 𝓕g` almost everywhere for
  `g, h ∈ L_2(V)` and a weight `w` of temperate growth, then `h` is the Fourier multiplier
  `w(D) g` of tempered distributions (`Rd.fourierMultiplierCLM_toTemperedDistribution_eq`) and
  `‖h‖_2² = ∫ |w|² |𝓕g|²` (`Rd.enorm_sq_eq_lintegral_of_fourier_ae_eq`, for every `w`). Bessel
  potentials commute with derivatives (`Rd.lineDerivOp_besselPotential`).
* **Bessel weights as multipliers**: for `t ≤ 0`, `⟨ξ⟩^t ≤ 1` (`Rd.besselWeight_le_one`), and
  `g ↦ ⟨·⟩^t g` is a bounded operator on `L_2(V)` of norm at most `1` (`Rd.besselWeightMul`,
  `Rd.norm_besselWeightMul_le_one`).
* **Inclusions**: for `t ≤ s`, `H^s(V) ⊆ H^t(V)` as a bounded operator `ι_{t,s}` of norm at most
  `1`, `U ↦ J_{-t} 𝓕⁻(⟨ξ⟩^{t-s} 𝓕(J_s U))` (`Rd.sobolevInclusion`), which keeps the distribution
  (`Rd.toDistr_sobolevInclusion`), is injective and composes (`Rd.sobolevInclusion_injective`,
  `Rd.sobolevInclusion_sobolevInclusion`), with `ι_{s,s}` the identity
  (`Rd.sobolevInclusion_self`). The inclusion is an explicit Fourier multiplier.
* **`L_2` functions**: for `s ≥ 0`, every `U ∈ H^s(V)` is the `L_2` function
  `ι_s U = Rd.sobolevToL2 hs U`, whose distribution is `U`
  (`Rd.toTemperedDistribution_sobolevToL2`), with `‖ι_s U‖_2 ≤ ‖U‖`
  (`Rd.norm_sobolevToL2_apply_le`); at `s = 1` this is `Rd.toL2` (`Rd.sobolevToL2_one`), and at
  `s = 0` it is an isometry onto `L_2(V)` (`Rd.norm_sobolevToL2_zero`,
  `Rd.sobolevToL2_zero_surjective`). An `L_2` function lies in Mathlib's `H^s(V)` as a tempered
  distribution iff it is `ι_s U` for some `U ∈ H^s(V)`
  (`Rd.memSobolev_bessel_iff_exists_sobolevToL2_eq`).
* **Derivatives**: `∂_v : H^{s+1}(V) → H^s(V)` as a bounded operator of norm at most `2π ‖v‖`
  (`Rd.sobolevLineDeriv`, `Rd.toDistr_sobolevLineDeriv`, `Rd.norm_sobolevLineDeriv_apply_le`),
  the Fourier multiplier with the symbol `2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1}` of `J_{-1} ∂_v` after `J_{s+1}`
  (`Rd.besselLineDerivSymbol`).
* **The norm recursion**: for every orthonormal basis `(e_i)` of `V` and `U ∈ H^{s+1}(V)`,
  `(2π)² ‖U‖²_{H^{s+1}} = (2π)² ‖ι_{s,s+1} U‖²_{H^s} + ∑_i ‖∂_{e_i} U‖²_{H^s}`
  (`Rd.sq_norm_eq_add_sum_sobolevLineDeriv`), from `⟨ξ⟩² = 1 + ∑_i ⟪ξ, e_i⟫²` on the Fourier side.
* **Convolution and mollification**: for an integrable `K`, convolution `U ↦ K ⋆ U` is a bounded
  operator on `H^s(V)`, acting on the `L_2` function `J_s U` (`Rd.sobolevConv`,
  `Rd.toLp_sobolevConv`), the Fourier multiplier with the symbol `𝓕K`
  (`Rd.fourier_toLp_sobolevConv_ae`); for `s ≥ 0` it acts on `ι_s U` as well
  (`Rd.sobolevToL2_sobolevConv`), and for an integrable `η` with `∫ η = 1` the dilates `η_c ⋆ U`
  converge to `U` in `H^s(V)` as `c → ∞` (`Rd.tendsto_sobolevConv_dilate`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform LineDeriv Real BesselPotentialSpace
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Fourier multipliers of `L_2` functions -/

/-- **Fourier multipliers of `L_2` functions**: if `w` has temperate growth, `g, h ∈ L_2(V)` and
`𝓕h = w 𝓕g` almost everywhere, then Mathlib's Fourier multiplier `w(D) = 𝓕⁻ w 𝓕` of tempered
distributions maps `g` to `h`. The product of `w` with the distribution of `𝓕g` is the
distribution of the `L_2` function `w 𝓕g` (`Rd.smulLeftCLM_toTemperedDistribution_eq`), and the
Fourier transforms of `L_2` and of `𝓢'` agree (Mathlib's `Lp.fourier_toTemperedDistribution_eq`,
`Lp.fourierInv_toTemperedDistribution_eq`). -/
theorem fourierMultiplierCLM_toTemperedDistribution_eq {w : V → ℂ} (hw : w.HasTemperateGrowth)
    {g h : Lp ℂ 2 (volume : Measure V)}
    (hgh : (𝓕 h : Lp ℂ 2 (volume : Measure V)) =ᵐ[volume]
      fun ξ => w ξ * (𝓕 g : Lp ℂ 2 (volume : Measure V)) ξ) :
    TemperedDistribution.fourierMultiplierCLM ℂ w (g : 𝓢'(V, ℂ)) = (h : 𝓢'(V, ℂ)) := by
  have hm : MemLp (fun ξ => w ξ * (𝓕 g : Lp ℂ 2 (volume : Measure V)) ξ) 2 volume :=
    (Lp.memLp (𝓕 h)).ae_eq hgh
  have h1 : hm.toLp _ = 𝓕 h := Lp.ext (hm.coeFn_toLp.trans hgh.symm)
  rw [TemperedDistribution.fourierMultiplierCLM_apply, Lp.fourier_toTemperedDistribution_eq,
    smulLeftCLM_toTemperedDistribution_eq hw _ hm, h1, Lp.fourierInv_toTemperedDistribution_eq,
    FourierTransform.fourierInv_fourier_eq]

/-- **Plancherel for a Fourier multiplier**: if `𝓕h = w 𝓕g` almost everywhere for
`g, h ∈ L_2(V)` and any function `w`, then `‖h‖_2² = ∫ |w(ξ)|² |𝓕g(ξ)|² dξ`
(`Rd.enorm_fourier_Lp_two`). -/
theorem enorm_sq_eq_lintegral_of_fourier_ae_eq {w : V → ℂ} {g h : Lp ℂ 2 (volume : Measure V)}
    (hgh : (𝓕 h : Lp ℂ 2 (volume : Measure V)) =ᵐ[volume]
      fun ξ => w ξ * (𝓕 g : Lp ℂ 2 (volume : Measure V)) ξ) :
    ‖h‖ₑ ^ 2 = ∫⁻ ξ, ENNReal.ofReal (‖w ξ‖ ^ 2) *
      ‖(𝓕 g : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
  rw [← enorm_fourier_Lp_two, enorm_sq_eq_lintegral]
  refine lintegral_congr_ae ?_
  filter_upwards [hgh] with ξ hξ
  rw [hξ, eNorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- **Bessel potentials commute with derivatives**: `∂_v (J_t u) = J_t (∂_v u)` for every
tempered distribution `u`, since both `∂_v` and `J_t` are Fourier multipliers (Mathlib's
`TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`,
`TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`). -/
theorem lineDerivOp_besselPotential (t : ℝ) (v : V) (u : 𝓢'(V, ℂ)) :
    ∂_{v} (besselPotential V ℂ t u) = besselPotential V ℂ t (∂_{v} u) := by
  rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM,
    TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM, map_smul,
    TemperedDistribution.besselPotential,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop)
      (by fun_prop),
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop)
      (by fun_prop), mul_comm (fun x : V => ((inner ℝ x v : ℝ) : ℂ))]

/-! ### Bessel weights as multipliers -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `⟨ξ⟩^t ≤ 1` for `t ≤ 0`, since `1 + ‖ξ‖² ≥ 1`. -/
theorem besselWeight_le_one {t : ℝ} (ht : t ≤ 0) (ξ : V) : besselWeight t ξ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|⟨ξ⟩^t| ≤ 1` for `t ≤ 0`, for the Bessel weight as a complex number. -/
theorem norm_besselWeight_le_one {t : ℝ} (ht : t ≤ 0) (ξ : V) :
    ‖(besselWeight t ξ : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (besselWeight_nonneg _ _)]
  exact besselWeight_le_one ht ξ

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Bessel weight `⟨ξ⟩^t`, as a complex function, is continuous. -/
theorem continuous_ofReal_besselWeight (t : ℝ) :
    Continuous fun ξ : V => (besselWeight t ξ : ℂ) :=
  (hasTemperateGrowth_besselWeight t).1.continuous

/-- **Multiplication by `⟨ξ⟩^t`, `t ≤ 0`, on `L_2(V)`**: the operator `g ↦ ⟨·⟩^t g` of
multiplication by a continuous function bounded by `1` (`Rd.mulLpL`). At `t = -1` it is
`Rd.besselInvMul` (`Rd.besselWeightMul_neg_one`). -/
noncomputable def besselWeightMul (t : ℝ) (ht : t ≤ 0) :
    Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  mulLpL (continuous_ofReal_besselWeight t) (norm_besselWeight_le_one ht)

/-- Multiplication by `⟨ξ⟩^t` is pointwise multiplication, almost everywhere. -/
theorem besselWeightMul_apply_ae {t : ℝ} (ht : t ≤ 0) (g : Lp ℂ 2 (volume : Measure V)) :
    (besselWeightMul t ht g : V → ℂ) =ᵐ[volume] fun ξ => (besselWeight t ξ : ℂ) * g ξ :=
  mulLp_apply_ae (continuous_ofReal_besselWeight t) (norm_besselWeight_le_one ht) g

/-- **Multiplication by `⟨ξ⟩^t`, `t ≤ 0`, has operator norm at most `1`** on `L_2(V)`: the
operator `Rd.mulLpL` is built with the bound `1` of `|⟨ξ⟩^t|` (Mathlib's
`LinearMap.mkContinuous_norm_le`). -/
theorem norm_besselWeightMul_le_one {t : ℝ} (ht : t ≤ 0) :
    ‖besselWeightMul (V := V) t ht‖ ≤ 1 := by
  unfold besselWeightMul mulLpL
  exact (LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _).trans_eq
    (ENNReal.toReal_ofReal zero_le_one)

/-- **At `t = -1` the multiplier is `Rd.besselInvMul`**: both operators multiply by `⟨ξ⟩^{-1}`
almost everywhere (`Rd.besselWeightMul_apply_ae`, `Rd.besselInvMul_apply_ae`). -/
theorem besselWeightMul_neg_one : besselWeightMul (V := V) (-1) (by norm_num) = besselInvMul :=
  ContinuousLinearMap.ext fun g =>
    Lp.ext ((besselWeightMul_apply_ae _ g).trans (besselInvMul_apply_ae g).symm)

/-! ### Inclusions -/

/-- **The inclusion `H^s(V) ⊆ H^t(V)` for `t ≤ s`**: `U ↦ J_{-t} 𝓕⁻(⟨ξ⟩^{t-s} 𝓕(J_s U))`,
built from Mathlib's isometry `U ↦ J_s U` of `H^s(V)` onto `L_2(V)`
(`BesselPotentialSpace.toLpₗᵢ`), the Fourier transform of `L_2(V)` and the multiplier
`Rd.besselWeightMul (t - s)`. It keeps the distribution (`Rd.toDistr_sobolevInclusion`). -/
noncomputable def sobolevInclusion {s t : ℝ} (hts : t ≤ s) : H^{s}(V) →L[ℂ] H^{t}(V) :=
  (BesselPotentialSpace.toLpₗᵢ V ℂ t 2).symm.toLinearIsometry.toContinuousLinearMap ∘L
    FourierTransform.fourierInvCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L
    besselWeightMul (t - s) (sub_nonpos.2 hts) ∘L
    FourierTransform.fourierCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L
    (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).toLinearIsometry.toContinuousLinearMap

variable {s t : ℝ}

/-- The `L_2` function `J_t (ι_{t,s} U)` of the inclusion is `𝓕⁻(⟨ξ⟩^{t-s} 𝓕(J_s U))`. -/
theorem toLp_sobolevInclusion (hts : t ≤ s) (U : H^{s}(V)) :
    (sobolevInclusion hts U).toLp =
      𝓕⁻ (besselWeightMul (t - s) (sub_nonpos.2 hts) (𝓕 U.toLp)) := by
  rw [← BesselPotentialSpace.toLpₗᵢ_apply (sobolevInclusion hts U), sobolevInclusion]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply, FourierTransform.fourierCLM_apply,
    FourierTransform.fourierInvCLM_apply]
  rw [BesselPotentialSpace.toLpₗᵢ_apply]

/-- The Fourier transform of `J_t (ι_{t,s} U)` is `⟨ξ⟩^{t-s} 𝓕(J_s U)` almost everywhere. -/
theorem fourier_toLp_sobolevInclusion_ae (hts : t ≤ s) (U : H^{s}(V)) :
    (𝓕 (sobolevInclusion hts U).toLp : Lp ℂ 2 (volume : Measure V)) =ᵐ[volume]
      fun ξ => (besselWeight (t - s) ξ : ℂ) * (𝓕 U.toLp : Lp ℂ 2 (volume : Measure V)) ξ := by
  rw [toLp_sobolevInclusion, FourierTransform.fourier_fourierInv_eq]
  exact besselWeightMul_apply_ae _ _

/-- **The inclusion keeps the distribution**: `ι_{t,s} U = U` as tempered distributions. The
`L_2` function of `ι_{t,s} U` is `J_{t-s}(J_s U)`
(`Rd.fourierMultiplierCLM_toTemperedDistribution_eq`), so the distribution of `ι_{t,s} U` is
`J_{-t} J_{t-s} J_s U = J_0 U = U` (Mathlib's
`TemperedDistribution.besselPotential_besselPotential_apply`,
`TemperedDistribution.besselPotential_zero`). -/
theorem toDistr_sobolevInclusion (hts : t ≤ s) (U : H^{s}(V)) :
    (sobolevInclusion hts U).toDistr = U.toDistr := by
  have h : besselPotential V ℂ (t - s) (U.toLp : 𝓢'(V, ℂ)) =
      ((sobolevInclusion hts U).toLp : 𝓢'(V, ℂ)) :=
    fourierMultiplierCLM_toTemperedDistribution_eq (hasTemperateGrowth_besselWeight (t - s))
      (fourier_toLp_sobolevInclusion_ae hts U)
  rw [← BesselPotentialSpace.besselPotential_neg_toLp_eq (f := sobolevInclusion hts U), ← h,
    ← U.bessel_toDistr_eq_toLp, TemperedDistribution.besselPotential_besselPotential_apply,
    TemperedDistribution.besselPotential_besselPotential_apply,
    show s + (t - s + -t) = 0 by ring, TemperedDistribution.besselPotential_zero,
    ContinuousLinearMap.id_apply]

/-- **The inclusion has norm at most `1`**: `‖ι_{t,s} U‖_{H^t} ≤ ‖U‖_{H^s}`, by Plancherel
(`BesselPotentialSpace.norm_fourier_toLp_eq`) and `Rd.norm_besselWeightMul_le_one`. -/
theorem norm_sobolevInclusion_apply_le (hts : t ≤ s) (U : H^{s}(V)) :
    ‖sobolevInclusion hts U‖ ≤ ‖U‖ := by
  rw [← BesselPotentialSpace.norm_toLp_eq, toLp_sobolevInclusion, ← Lp.norm_fourier_eq,
    FourierTransform.fourier_fourierInv_eq, ← BesselPotentialSpace.norm_fourier_toLp_eq]
  exact ((besselWeightMul _ _).le_of_opNorm_le (norm_besselWeightMul_le_one _) _).trans_eq
    (one_mul _)

/-- **The inclusion is injective**: an element of `H^t(V)` is determined by its distribution
(Mathlib's `BesselPotentialSpace.ext`), and `ι_{t,s} U = U` as distributions. -/
theorem sobolevInclusion_injective (hts : t ≤ s) :
    Function.Injective (sobolevInclusion (V := V) hts) :=
  fun U W h => BesselPotentialSpace.ext (by
    rw [← toDistr_sobolevInclusion hts U, h, toDistr_sobolevInclusion])

/-- **Inclusions compose**: for `u ≤ t ≤ s`, `ι_{u,t} ∘ ι_{t,s} = ι_{u,s}`. -/
theorem sobolevInclusion_sobolevInclusion {u : ℝ} (hut : u ≤ t) (hts : t ≤ s) (U : H^{s}(V)) :
    sobolevInclusion hut (sobolevInclusion hts U) = sobolevInclusion (hut.trans hts) U :=
  BesselPotentialSpace.ext (by simp only [toDistr_sobolevInclusion])

/-- **The inclusion `ι_{s,s}` is the identity** of `H^s(V)`: it keeps the tempered distribution
(`Rd.toDistr_sobolevInclusion`), which determines an element of `H^s(V)` (Mathlib's
`BesselPotentialSpace.ext`). -/
theorem sobolevInclusion_self (U : H^{s}(V)) : sobolevInclusion le_rfl U = U :=
  BesselPotentialSpace.ext (toDistr_sobolevInclusion le_rfl U)

/-! ### `L_2` functions -/

/-- **The `L_2` function `ι_s U` of an element `U` of `H^s(V)`, `s ≥ 0`**: the inclusion
`ι_{0,s}` into `H^0(V)`, followed by Mathlib's isometry `H^0(V) → L_2(V)`, `U ↦ J_0 U = U`. Its
distribution is `U` (`Rd.toTemperedDistribution_sobolevToL2`); at `s = 1` it is `Rd.toL2`
(`Rd.sobolevToL2_one`). -/
noncomputable def sobolevToL2 {s : ℝ} (hs : 0 ≤ s) : H^{s}(V) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  (BesselPotentialSpace.toLpₗᵢ V ℂ 0 2).toLinearIsometry.toContinuousLinearMap ∘L
    sobolevInclusion hs

/-- `ι_s U` is the `L_2` function `J_0 (ι_{0,s} U)` of the inclusion of `U` into `H^0(V)`. -/
theorem sobolevToL2_apply (hs : 0 ≤ s) (U : H^{s}(V)) :
    sobolevToL2 hs U = (sobolevInclusion hs U).toLp := by
  simp only [sobolevToL2, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    BesselPotentialSpace.toLpₗᵢ_apply]

/-- **`ι_s U` represents `U`**: the tempered distribution of the `L_2` function `ι_s U` is `U`,
since `J_0` is the identity (Mathlib's `TemperedDistribution.besselPotential_zero`) and the
inclusion `ι_{0,s}` keeps the distribution (`Rd.toDistr_sobolevInclusion`). -/
theorem toTemperedDistribution_sobolevToL2 (hs : 0 ≤ s) (U : H^{s}(V)) :
    ((sobolevToL2 hs U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) = U.toDistr := by
  have h := (sobolevInclusion hs U).bessel_toDistr_eq_toLp
  rw [TemperedDistribution.besselPotential_zero, ContinuousLinearMap.id_apply,
    toDistr_sobolevInclusion] at h
  rw [sobolevToL2_apply, ← h]

/-- `J_s (ι_s U) = J_s U`: the Bessel potential of the `L_2` function `ι_s U` is the `L_2`
function of `U`. -/
theorem besselPotential_sobolevToL2 (hs : 0 ≤ s) (U : H^{s}(V)) :
    besselPotential V ℂ s ((sobolevToL2 hs U : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (U.toLp : 𝓢'(V, ℂ)) := by
  rw [toTemperedDistribution_sobolevToL2]
  exact U.bessel_toDistr_eq_toLp

/-- An `L_2` function `f` is `ι_s U` as soon as its tempered distribution is `U`: `L_2` functions
are determined by their distributions (`Rd.eq_of_toTemperedDistribution_eq`). -/
theorem sobolevToL2_eq_of_toDistr_eq (hs : 0 ≤ s) (U : H^{s}(V))
    {f : Lp ℂ 2 (volume : Measure V)} (hf : (f : 𝓢'(V, ℂ)) = U.toDistr) :
    sobolevToL2 hs U = f :=
  eq_of_toTemperedDistribution_eq ((toTemperedDistribution_sobolevToL2 hs U).trans hf.symm)

/-- **`L_2` functions in `H^s(V)`**: for `s ≥ 0`, the tempered distribution of `f ∈ L_2(V)` lies in
Mathlib's `H^s(V)` iff `f = ι_s U` for some `U ∈ H^s(V)`. Mathlib's
`TemperedDistribution.MemSobolev.toBesselPotentialSpace` bundles the distribution, whose `L_2`
function is `f` (`Rd.sobolevToL2_eq_of_toDistr_eq`); conversely the distribution of `ι_s U` is `U`
(`Rd.toTemperedDistribution_sobolevToL2`). -/
theorem memSobolev_bessel_iff_exists_sobolevToL2_eq (hs : 0 ≤ s)
    (f : Lp ℂ 2 (volume : Measure V)) :
    TemperedDistribution.MemSobolev s 2 (f : 𝓢'(V, ℂ)) ↔ ∃ U : H^{s}(V), sobolevToL2 hs U = f := by
  refine ⟨fun hf => ⟨hf.toBesselPotentialSpace, sobolevToL2_eq_of_toDistr_eq hs _
    hf.toBesselPotentialSpace_toDistr.symm⟩, ?_⟩
  rintro ⟨U, rfl⟩
  rw [toTemperedDistribution_sobolevToL2]
  exact U.memSobolev_toDistr

/-- **`H^s(V)`, `s ≥ 0`, is determined by its `L_2` functions**: `U ↦ ι_s U` is injective
(`Rd.toTemperedDistribution_sobolevToL2`, Mathlib's `BesselPotentialSpace.ext`). -/
theorem sobolevToL2_injective (hs : 0 ≤ s) : Function.Injective (sobolevToL2 (V := V) hs) :=
  fun U W h => BesselPotentialSpace.ext (by
    rw [← toTemperedDistribution_sobolevToL2 hs U, h, toTemperedDistribution_sobolevToL2])

/-- **`‖ι_s U‖_2 ≤ ‖U‖_{H^s}`** for `s ≥ 0` (`Rd.norm_sobolevInclusion_apply_le`). -/
theorem norm_sobolevToL2_apply_le (hs : 0 ≤ s) (U : H^{s}(V)) : ‖sobolevToL2 hs U‖ ≤ ‖U‖ := by
  rw [sobolevToL2_apply, BesselPotentialSpace.norm_toLp_eq]
  exact norm_sobolevInclusion_apply_le hs U

/-- **At `s = 1` the `L_2` function is `Rd.toL2`**: both represent the same distribution
(`Rd.toL2_eq_of_toDistr_eq`). -/
theorem sobolevToL2_one : sobolevToL2 (V := V) zero_le_one = toL2 := by
  refine ContinuousLinearMap.ext fun U => ?_
  exact (toL2_eq_of_toDistr_eq U (toTemperedDistribution_sobolevToL2 zero_le_one U)).symm

/-- **The `L_2` function does not depend on the space**: for `0 ≤ t ≤ s` and `U ∈ H^s(V)`,
`ι_t (ι_{t,s} U) = ι_s U`. -/
theorem sobolevToL2_sobolevInclusion (ht : 0 ≤ t) (hts : t ≤ s) (U : H^{s}(V)) :
    sobolevToL2 ht (sobolevInclusion hts U) = sobolevToL2 (ht.trans hts) U :=
  sobolevToL2_eq_of_toDistr_eq ht _ (by
    rw [toTemperedDistribution_sobolevToL2, toDistr_sobolevInclusion])

/-- **The `L_2` function of `H^0(V)` has the same norm**: `‖ι_0 U‖_2 = ‖U‖_{H^0}`, since
`ι_0 U = J_0 (ι_{0,0} U)` (`Rd.sobolevToL2_apply`), `‖J_0 U‖_2 = ‖U‖_{H^0}` (Mathlib's
`BesselPotentialSpace.norm_toLp_eq`) and `ι_{0,0}` is the identity (`Rd.sobolevInclusion_self`). -/
theorem norm_sobolevToL2_zero (U : H^{0}(V)) : ‖sobolevToL2 le_rfl U‖ = ‖U‖ := by
  rw [sobolevToL2_apply, BesselPotentialSpace.norm_toLp_eq, sobolevInclusion_self]

/-- **Every `L_2` function is the `L_2` function of an element of `H^0(V)`**: for `F ∈ L_2(V)`,
the element `U = J_0⁻¹ F` of `H^0(V)` (Mathlib's isometry `BesselPotentialSpace.toLpₗᵢ` onto
`L_2(V)`) has `ι_0 U = J_0 (ι_{0,0} U) = J_0 U = F` (`Rd.sobolevInclusion_self`). -/
theorem sobolevToL2_zero_surjective : Function.Surjective (sobolevToL2 (V := V) le_rfl) := by
  intro F
  refine ⟨(BesselPotentialSpace.toLpₗᵢ V ℂ 0 2).symm F, ?_⟩
  rw [sobolevToL2_apply, sobolevInclusion_self, ← BesselPotentialSpace.toLpₗᵢ_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-! ### Derivatives -/

/-- **The symbol of `J_{-1} ∂_v`**: `2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1}`, the symbol `2πi ⟪ξ, v⟫` of `∂_v`
times the Bessel weight `⟨ξ⟩^{-1}`, bounded by `2π ‖v‖` (`Rd.norm_besselLineDerivSymbol_le`). -/
noncomputable def besselLineDerivSymbol (v ξ : V) : ℂ :=
  2 * π * Complex.I * ((inner ℝ ξ v * besselWeight (-1) ξ : ℝ) : ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The symbol of `J_{-1} ∂_v` is smooth with polynomially bounded derivatives. -/
theorem hasTemperateGrowth_besselLineDerivSymbol (v : V) :
    (besselLineDerivSymbol v).HasTemperateGrowth := by
  unfold besselLineDerivSymbol besselWeight
  fun_prop

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The symbol of `J_{-1} ∂_v` is continuous. -/
theorem continuous_besselLineDerivSymbol (v : V) : Continuous (besselLineDerivSymbol v) :=
  (hasTemperateGrowth_besselLineDerivSymbol v).1.continuous

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1}| = 2π |⟪ξ, v⟫| ⟨ξ⟩^{-1}`. -/
theorem norm_besselLineDerivSymbol (v ξ : V) :
    ‖besselLineDerivSymbol v ξ‖ = 2 * π * (|inner ℝ ξ v| * besselWeight (-1) ξ) := by
  rw [besselLineDerivSymbol, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (besselWeight_nonneg _ _), mul_one]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **`|2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1}| ≤ 2π ‖v‖`**, by Cauchy–Schwarz and `‖ξ‖ ≤ ⟨ξ⟩`
(`Rd.norm_le_besselWeight_one`). -/
theorem norm_besselLineDerivSymbol_le (v ξ : V) :
    ‖besselLineDerivSymbol v ξ‖ ≤ 2 * π * ‖v‖ := by
  have hb : 0 < besselWeight 1 ξ := Real.rpow_pos_of_pos (by positivity) _
  rw [norm_besselLineDerivSymbol, besselWeight_neg_one_eq_inv, ← div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ((div_le_iff₀ hb).2 ?_) (by positivity)
  calc |inner ℝ ξ v| ≤ ‖ξ‖ * ‖v‖ := abs_real_inner_le_norm ξ v
    _ ≤ besselWeight 1 ξ * ‖v‖ :=
        mul_le_mul_of_nonneg_right (norm_le_besselWeight_one ξ) (norm_nonneg v)
    _ = ‖v‖ * besselWeight 1 ξ := mul_comm _ _

/-- **`J_{-1} ∂_v` is the Fourier multiplier with the symbol `2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1}`**, for every
tempered distribution (Mathlib's `TemperedDistribution.besselPotential_neg_one_lineDerivOp_eq`). -/
theorem besselPotential_neg_one_lineDerivOp (v : V) (u : 𝓢'(V, ℂ)) :
    besselPotential V ℂ (-1) (∂_{v} u) =
      TemperedDistribution.fourierMultiplierCLM ℂ (besselLineDerivSymbol v) u := by
  have h : besselLineDerivSymbol v = (2 * π * Complex.I) • fun x : V =>
      ((inner ℝ x v * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := rfl
  rw [TemperedDistribution.besselPotential_neg_one_lineDerivOp_eq, h,
    TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop)]
  rfl

/-- **The derivative `∂_v : H^{s+1}(V) → H^s(V)`**: `U ↦ J_{-s} 𝓕⁻(m_v 𝓕(J_{s+1} U))` with the
symbol `m_v(ξ) = 2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1}` (`Rd.besselLineDerivSymbol`), a bounded operator; it is
the derivative of tempered distributions (`Rd.toDistr_sobolevLineDeriv`). -/
noncomputable def sobolevLineDeriv (s : ℝ) (v : V) : H^{s + 1}(V) →L[ℂ] H^{s}(V) :=
  (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).symm.toLinearIsometry.toContinuousLinearMap ∘L
    FourierTransform.fourierInvCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L
    mulLpL (continuous_besselLineDerivSymbol v) (norm_besselLineDerivSymbol_le v) ∘L
    FourierTransform.fourierCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L
    (BesselPotentialSpace.toLpₗᵢ V ℂ (s + 1) 2).toLinearIsometry.toContinuousLinearMap

/-- The `L_2` function `J_s (∂_v U)` is `𝓕⁻(m_v 𝓕(J_{s+1} U))`. -/
theorem toLp_sobolevLineDeriv (s : ℝ) (v : V) (U : H^{s + 1}(V)) :
    (sobolevLineDeriv s v U).toLp =
      𝓕⁻ (mulLp (continuous_besselLineDerivSymbol v) (norm_besselLineDerivSymbol_le v)
        (𝓕 U.toLp)) := by
  rw [← BesselPotentialSpace.toLpₗᵢ_apply (sobolevLineDeriv s v U), sobolevLineDeriv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply, FourierTransform.fourierCLM_apply,
    FourierTransform.fourierInvCLM_apply, mulLpL_apply]
  rw [BesselPotentialSpace.toLpₗᵢ_apply]

/-- The Fourier transform of `J_s (∂_v U)` is `2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1} 𝓕(J_{s+1} U)` almost
everywhere. -/
theorem fourier_toLp_sobolevLineDeriv_ae (s : ℝ) (v : V) (U : H^{s + 1}(V)) :
    (𝓕 (sobolevLineDeriv s v U).toLp : Lp ℂ 2 (volume : Measure V)) =ᵐ[volume]
      fun ξ => besselLineDerivSymbol v ξ * (𝓕 U.toLp : Lp ℂ 2 (volume : Measure V)) ξ := by
  rw [toLp_sobolevLineDeriv, FourierTransform.fourier_fourierInv_eq]
  exact mulLp_apply_ae _ _ _

/-- **`∂_v U` is the derivative of the distribution `U`**. The `L_2` function of `∂_v U` is
`J_{-1} ∂_v (J_{s+1} U)` (`Rd.fourierMultiplierCLM_toTemperedDistribution_eq`,
`Rd.besselPotential_neg_one_lineDerivOp`), so its distribution is
`J_{-s} J_{-1} ∂_v J_{s+1} U = ∂_v U` (`Rd.lineDerivOp_besselPotential`). -/
theorem toDistr_sobolevLineDeriv (s : ℝ) (v : V) (U : H^{s + 1}(V)) :
    (sobolevLineDeriv s v U).toDistr = ∂_{v} U.toDistr := by
  have h : besselPotential V ℂ (-1) (∂_{v} (U.toLp : 𝓢'(V, ℂ))) =
      ((sobolevLineDeriv s v U).toLp : 𝓢'(V, ℂ)) := by
    rw [besselPotential_neg_one_lineDerivOp]
    exact fourierMultiplierCLM_toTemperedDistribution_eq
      (hasTemperateGrowth_besselLineDerivSymbol v) (fourier_toLp_sobolevLineDeriv_ae s v U)
  rw [← BesselPotentialSpace.besselPotential_neg_toLp_eq (f := sobolevLineDeriv s v U), ← h,
    ← U.bessel_toDistr_eq_toLp, lineDerivOp_besselPotential,
    TemperedDistribution.besselPotential_besselPotential_apply,
    TemperedDistribution.besselPotential_besselPotential_apply,
    show s + 1 + (-1 + -s) = 0 by ring, TemperedDistribution.besselPotential_zero,
    ContinuousLinearMap.id_apply]

/-- **`‖∂_v U‖_{H^s} ≤ 2π ‖v‖ ‖U‖_{H^{s+1}}`**, by Plancherel and the bound `2π ‖v‖` of the
symbol (`Rd.norm_besselLineDerivSymbol_le`), with which the multiplication operator `Rd.mulLpL`
is built (Mathlib's `LinearMap.mkContinuous_norm_le`). -/
theorem norm_sobolevLineDeriv_apply_le (s : ℝ) (v : V) (U : H^{s + 1}(V)) :
    ‖sobolevLineDeriv s v U‖ ≤ 2 * π * ‖v‖ * ‖U‖ := by
  rw [← BesselPotentialSpace.norm_toLp_eq, toLp_sobolevLineDeriv, ← Lp.norm_fourier_eq,
    FourierTransform.fourier_fourierInv_eq, ← BesselPotentialSpace.norm_fourier_toLp_eq]
  have hC : ‖mulLpL (p := 2) (V := V) (continuous_besselLineDerivSymbol v)
      (norm_besselLineDerivSymbol_le v)‖ ≤ 2 * π * ‖v‖ := by
    unfold mulLpL
    exact (LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  exact (mulLpL _ _).le_of_opNorm_le hC _

/-! ### The norm recursion -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `(⟨ξ⟩^{-1})² (1 + ‖ξ‖²) = 1`. -/
theorem besselWeight_neg_one_sq_mul (ξ : V) : besselWeight (-1) ξ ^ 2 * (1 + ‖ξ‖ ^ 2) = 1 := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [besselWeight, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
    show (-1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one,
    inv_mul_cancel₀ hpos.ne']

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The symbols of the norm recursion add up**: for every orthonormal basis `(e_i)` of `V` and
every `ξ`, `(2π)² (⟨ξ⟩^{-1})² + ∑_i |2πi ⟪ξ, e_i⟫ ⟨ξ⟩^{-1}|² = (2π)²`, since
`∑_i ⟪ξ, e_i⟫² = ‖ξ‖²` (Mathlib's `OrthonormalBasis.sum_sq_inner_left`) and
`(⟨ξ⟩^{-1})² (1 + ‖ξ‖²) = 1`. -/
theorem sq_besselWeight_add_sum_sq_norm_besselLineDerivSymbol {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (ξ : V) :
    (2 * π) ^ 2 * ‖(besselWeight (-1) ξ : ℂ)‖ ^ 2 + ∑ i, ‖besselLineDerivSymbol (b i) ξ‖ ^ 2 =
      (2 * π) ^ 2 := by
  have hs : ∑ i, ‖besselLineDerivSymbol (b i) ξ‖ ^ 2 =
      (2 * π) ^ 2 * besselWeight (-1) ξ ^ 2 * ‖ξ‖ ^ 2 := by
    simp_rw [norm_besselLineDerivSymbol, mul_pow, sq_abs, ← b.sum_sq_inner_left ξ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs, Complex.norm_real, Real.norm_of_nonneg (besselWeight_nonneg _ _)]
  linear_combination (2 * π) ^ 2 * besselWeight_neg_one_sq_mul ξ

/-- `‖ι_{s,s+1} U‖²_{H^s} = ∫ (⟨ξ⟩^{-1})² |𝓕(J_{s+1} U)(ξ)|² dξ` for `U ∈ H^{s+1}(V)`
(`Rd.enorm_sq_eq_lintegral_of_fourier_ae_eq`). -/
theorem enorm_sq_sobolevInclusion_add_one (s : ℝ) (U : H^{s + 1}(V)) :
    ‖sobolevInclusion (lt_add_one s).le U‖ₑ ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal (‖(besselWeight (-1) ξ : ℂ)‖ ^ 2) *
        ‖(𝓕 U.toLp : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
  rw [← BesselPotentialSpace.enorm_toLp_eq,
    enorm_sq_eq_lintegral_of_fourier_ae_eq (fourier_toLp_sobolevInclusion_ae _ U),
    show s - (s + 1) = -1 by ring]

/-- `‖∂_v U‖²_{H^s} = ∫ |2πi ⟪ξ, v⟫ ⟨ξ⟩^{-1}|² |𝓕(J_{s+1} U)(ξ)|² dξ` for `U ∈ H^{s+1}(V)`
(`Rd.enorm_sq_eq_lintegral_of_fourier_ae_eq`). -/
theorem enorm_sq_sobolevLineDeriv (s : ℝ) (v : V) (U : H^{s + 1}(V)) :
    ‖sobolevLineDeriv s v U‖ₑ ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal (‖besselLineDerivSymbol v ξ‖ ^ 2) *
        ‖(𝓕 U.toLp : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2 := by
  rw [← BesselPotentialSpace.enorm_toLp_eq,
    enorm_sq_eq_lintegral_of_fourier_ae_eq (fourier_toLp_sobolevLineDeriv_ae s v U)]

/-- **The norm recursion in `ℝ≥0∞`**: for every orthonormal basis `(e_i)` of `V` and every
`U ∈ H^{s+1}(V)`,
`(2π)² ‖U‖²_{H^{s+1}} = (2π)² ‖ι_{s,s+1} U‖²_{H^s} + ∑_i ‖∂_{e_i} U‖²_{H^s}`. On the Fourier side
of `J_{s+1} U` the three terms carry the weights `(2π)²`, `(2π)² (⟨ξ⟩^{-1})²` and
`|2πi ⟪ξ, e_i⟫ ⟨ξ⟩^{-1}|²` (`Rd.enorm_sq_sobolevInclusion_add_one`,
`Rd.enorm_sq_sobolevLineDeriv`), which add up
(`Rd.sq_besselWeight_add_sum_sq_norm_besselLineDerivSymbol`). -/
theorem enorm_sq_eq_add_sum_sobolevLineDeriv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (s : ℝ) (U : H^{s + 1}(V)) :
    ENNReal.ofReal (2 * π) ^ 2 * ‖U‖ₑ ^ 2 =
      ENNReal.ofReal (2 * π) ^ 2 * ‖sobolevInclusion (lt_add_one s).le U‖ₑ ^ 2 +
        ∑ i, ‖sobolevLineDeriv s (b i) U‖ₑ ^ 2 := by
  set G : V → ℝ≥0∞ := fun ξ => ‖(𝓕 U.toLp : Lp ℂ 2 (volume : Measure V)) ξ‖ₑ ^ 2
  have hG : AEMeasurable G volume := (Lp.aestronglyMeasurable _).eNorm.pow_const 2
  have hw : ∀ (f : V → ℂ), Continuous f →
      AEMeasurable (fun ξ => ENNReal.ofReal (‖f ξ‖ ^ 2) * G ξ) volume := fun f hf =>
    ((hf.norm.pow 2).measurable.ennreal_ofReal.aemeasurable).mul hG
  have hpt : ∀ ξ, ENNReal.ofReal (2 * π) ^ 2 * G ξ =
      ENNReal.ofReal (2 * π) ^ 2 * (ENNReal.ofReal (‖(besselWeight (-1) ξ : ℂ)‖ ^ 2) * G ξ) +
        ∑ i, ENNReal.ofReal (‖besselLineDerivSymbol (b i) ξ‖ ^ 2) * G ξ := fun ξ => by
    rw [← Finset.sum_mul, ← mul_assoc, ← add_mul, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      sq_besselWeight_add_sum_sq_norm_besselLineDerivSymbol b ξ]
  rw [enorm_sq_sobolevInclusion_add_one]
  simp_rw [enorm_sq_sobolevLineDeriv]
  rw [← BesselPotentialSpace.enorm_toLp_eq, ← enorm_fourier_Lp_two, enorm_sq_eq_lintegral,
    ← lintegral_const_mul' _ _ (by finiteness), ← lintegral_const_mul' _ _ (by finiteness),
    ← lintegral_finsetSum' _ fun i _ => hw _ (continuous_besselLineDerivSymbol (b i)),
    ← lintegral_add_left' ((hw _ (continuous_ofReal_besselWeight (-1))).const_mul _)]
  exact lintegral_congr fun ξ => hpt ξ

/-- **The norm recursion**: for every orthonormal basis `(e_i)` of `V`, every real `s` and every
`U ∈ H^{s+1}(V)`,
`(2π)² ‖U‖²_{H^{s+1}} = (2π)² ‖ι_{s,s+1} U‖²_{H^s} + ∑_i ‖∂_{e_i} U‖²_{H^s}`, with the inclusion
`ι_{s,s+1}` (`Rd.sobolevInclusion`) and the derivatives `Rd.sobolevLineDeriv`
(`Rd.enorm_sq_eq_add_sum_sobolevLineDeriv`). At `s = 0` it is the identity
`(2π)² ‖J_1 f‖_2² = (2π)² ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²` of `Rd.sq_norm_besselPotential_one_eq`. -/
theorem sq_norm_eq_add_sum_sobolevLineDeriv {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (s : ℝ) (U : H^{s + 1}(V)) :
    (2 * π) ^ 2 * ‖U‖ ^ 2 = (2 * π) ^ 2 * ‖sobolevInclusion (lt_add_one s).le U‖ ^ 2 +
      ∑ i, ‖sobolevLineDeriv s (b i) U‖ ^ 2 := by
  have he := enorm_sq_eq_add_sum_sobolevLineDeriv b s U
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * π)] at he
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 he

/-! ### Convolution and mollification -/

/-- **Convolution in `H^s(V)`**: for an integrable `K` and every real `s`, `U ↦ K ⋆ U`, the
element of `H^s(V)` whose `L_2` function `J_s (K ⋆ U)` is `K ⋆ J_s U`
(`Rd.toLp_sobolevConv`). It is a bounded operator, built from Mathlib's isometry
`U ↦ J_s U` of `H^s(V)` onto `L_2(V)` (`BesselPotentialSpace.toLpₗᵢ`) and Young's inequality
`‖K ⋆ g‖_2 ≤ ‖K‖_1 ‖g‖_2` (`Rd.convLp`). -/
noncomputable def sobolevConv {K : V → ℂ} (hK : Integrable K) (s : ℝ) :
    H^{s}(V) →L[ℂ] H^{s}(V) :=
  (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).symm.toLinearIsometry.toContinuousLinearMap ∘L
    convLp two_ne_top hK ∘L
    (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).toLinearIsometry.toContinuousLinearMap

/-- The `L_2` function `J_s (K ⋆ U)` of the convolution is `K ⋆ J_s U`. -/
theorem toLp_sobolevConv {K : V → ℂ} (hK : Integrable K) (U : H^{s}(V)) :
    (sobolevConv hK s U).toLp = convLp two_ne_top hK U.toLp := by
  rw [← BesselPotentialSpace.toLpₗᵢ_apply (sobolevConv hK s U), sobolevConv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]
  rw [BesselPotentialSpace.toLpₗᵢ_apply]

/-- The Fourier transform of `J_s (K ⋆ U)` is `𝓕K · 𝓕(J_s U)` almost everywhere, by the
convolution theorem on `L_2` (`Rd.fourier_convLp`). -/
theorem fourier_toLp_sobolevConv_ae {K : V → ℂ} (hK : Integrable K) (U : H^{s}(V)) :
    (𝓕 (sobolevConv hK s U).toLp : Lp ℂ 2 (volume : Measure V)) =ᵐ[volume]
      fun ξ => 𝓕 K ξ * (𝓕 U.toLp : Lp ℂ 2 (volume : Measure V)) ξ := by
  rw [toLp_sobolevConv]
  exact fourier_convLp hK U.toLp

/-- **Convolution acts on the `L_2` functions**: for `s ≥ 0`, an integrable `K` and
`U ∈ H^s(V)`, `ι_s (K ⋆ U) = K ⋆ ι_s U`. Both sides have the Fourier transform
`𝓕K ⟨ξ⟩^{-s} 𝓕(J_s U)` almost everywhere (`Rd.fourier_toLp_sobolevInclusion_ae`,
`Rd.fourier_toLp_sobolevConv_ae`, `Rd.fourier_convLp`), and the Fourier transform of `L_2(V)` is
injective (Mathlib's `FourierTransform.fourierInv_fourier_eq`). -/
theorem sobolevToL2_sobolevConv (hs : 0 ≤ s) {K : V → ℂ} (hK : Integrable K) (U : H^{s}(V)) :
    sobolevToL2 hs (sobolevConv hK s U) = convLp two_ne_top hK (sobolevToL2 hs U) := by
  have h : (𝓕 (sobolevToL2 hs (sobolevConv hK s U)) : Lp ℂ 2 (volume : Measure V)) =
      𝓕 (convLp two_ne_top hK (sobolevToL2 hs U)) := by
    refine Lp.ext ?_
    rw [sobolevToL2_apply, sobolevToL2_apply]
    filter_upwards [fourier_toLp_sobolevInclusion_ae hs (sobolevConv hK s U),
      fourier_convLp hK (sobolevInclusion hs U).toLp, fourier_toLp_sobolevInclusion_ae hs U,
      fourier_toLp_sobolevConv_ae hK U] with ξ h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    ring
  calc sobolevToL2 hs (sobolevConv hK s U)
      = (𝓕⁻ (𝓕 (sobolevToL2 hs (sobolevConv hK s U)) : Lp ℂ 2 (volume : Measure V)) :
          Lp ℂ 2 (volume : Measure V)) := (FourierTransform.fourierInv_fourier_eq _).symm
    _ = convLp two_ne_top hK (sobolevToL2 hs U) := by
        rw [h, FourierTransform.fourierInv_fourier_eq]

open Filter Topology in
/-- **Mollification converges in `H^s(V)`**, for every real `s`: let `η` be integrable with
`∫ η = 1`, `c_i ≠ 0` dilation factors with `c_i → ∞` and `η_c(x) = c^n η(c x)`. Then
`η_{c_i} ⋆ U → U` in `H^s(V)` for every `U ∈ H^s(V)`, since `‖η_c ⋆ U - U‖_{H^s}` is the `L_2`
norm of `η_c ⋆ J_s U - J_s U` (`Rd.toLp_sobolevConv`, Mathlib's
`BesselPotentialSpace.norm_toLp_eq`) and approximate identities converge in `L_2(V)`
(`Rd.tendsto_convLp_dilate`). -/
theorem tendsto_sobolevConv_dilate {η : V → ℂ} (hη : Integrable η) (h1 : ∫ x, η x = 1)
    {ι : Type*} {l : Filter ι} {c : ι → ℝ} (hc : ∀ i, c i ≠ 0) (hcl : Tendsto c l atTop)
    (U : H^{s}(V)) : Tendsto (fun i => sobolevConv (integrable_dilate hη (hc i)) s U) l (𝓝 U) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine (tendsto_iff_norm_sub_tendsto_zero.1
    (tendsto_convLp_dilate two_ne_top hη h1 hc hcl U.toLp)).congr fun i => ?_
  rw [← BesselPotentialSpace.norm_toLp_eq (sobolevConv (integrable_dilate hη (hc i)) s U - U),
    BesselPotentialSpace.toLp_sub, toLp_sobolevConv]

end Rd
