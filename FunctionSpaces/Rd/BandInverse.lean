/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.DilatedDifferences
public import FunctionSpaces.Rd.BandLimited
public import ApproximationSpaces.Sequences.Lq

/-!
# The inverse inequality for band-limited functions

For a band-limited `a ∈ E_j`, `a = Θ_j ⋆ a`, so every difference of `a` is the convolution of `a`
with a difference of the kernel: `Δ_h^r a = (Δ_h^r Θ_j) ⋆ a` (`Rd.higherDiff_conv_ae`). By Young's
inequality and the dilation `Δ_h^r Θ_j = (Δ_{2^j h}^r Θ)_{2^j}` (`Rd.higherDiff_dilate`),

`‖Δ_h^r a‖_p ≤ ‖Δ_{2^j h}^r Θ‖_1 ‖a‖_p`.

**Differences of Schwartz functions in `L_1`** (`Rd.lintegral_enorm_higherDiff_schwartz_le`):
`‖Δ_v^r G‖_1 ≤ ‖v‖^r ‖D^r G‖_1`. The fundamental theorem of calculus along the segment from `x`
to `x + v` gives `G(x + v) - G(x) = ∫_0^1 ∂_v G(x + t v) dt`, hence `‖Δ_v G‖_1 ≤ ‖∂_v G‖_1`
(`Rd.lintegral_enorm_fwdDiff_le`); differences commute with line derivatives
(`Rd.lineDerivOp_fwdDiffSchwartz`), so induction gives `‖Δ_v^r G‖_1 ≤ ‖∂_v^r G‖_1`, and
`|∂_v^r G(x)| ≤ ‖v‖^r ‖D^r G(x)‖`. Mathlib's Schwartz space provides the translations, the line
derivatives `∂_v` and the integrability of all derivatives.

**The inverse inequality** (`Rd.lpModulus_le_of_mem_bandSpace`): for `a ∈ E_j`,
`ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` with `C = 2^r + ‖D^r Θ‖_1` (for `k < j` the bound
`ω_r ≤ 2^r ‖a‖_p` is used).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal SchwartzMap LineDeriv

namespace Rd

open ENNReal (dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Differences of Schwartz functions -/

/-- The forward difference `G ↦ G(· + v) - G` as an operator on Schwartz functions. -/
noncomputable def fwdDiffSchwartz (v : V) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.compSubConstCLM ℝ (-v) - ContinuousLinearMap.id ℝ _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Schwartz forward difference is the forward difference. -/
theorem coe_fwdDiffSchwartz (v : V) (G : 𝓢(V, ℂ)) :
    (fwdDiffSchwartz v G : V → ℂ) = fwdDiff v G := by
  funext x
  simp [fwdDiffSchwartz, fwdDiff, sub_neg_eq_add]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences commute with line derivatives**: `∂_u (Δ_v G) = Δ_v (∂_u G)`. -/
theorem lineDerivOp_fwdDiffSchwartz (u v : V) (G : 𝓢(V, ℂ)) :
    ∂_{u} (fwdDiffSchwartz v G) = fwdDiffSchwartz v (∂_{u} G) := by
  ext x
  have hcoe : ((fwdDiffSchwartz v G : 𝓢(V, ℂ)) : V → ℂ) = fun y => G (y + v) - G y :=
    coe_fwdDiffSchwartz v G
  have hd : DifferentiableAt ℝ (fun y => G (y + v)) x :=
    G.differentiableAt.comp x (differentiableAt_id.add_const v)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe, fderiv_fun_sub hd G.differentiableAt,
    fderiv_comp_add_right, coe_fwdDiffSchwartz, fwdDiff, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Iterated line derivatives commute with differences. -/
theorem iteratedLineDerivOp_fwdDiffSchwartz (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∂^{fun _ : Fin r => v} (fwdDiffSchwartz v G) =
      fwdDiffSchwartz v (∂^{fun _ : Fin r => v} G) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left]
    exact (congrArg _ ih).trans (lineDerivOp_fwdDiffSchwartz v v _)

/-- **A difference is bounded by the line derivative in `L_1`**: `‖Δ_v G‖_1 ≤ ‖∂_v G‖_1`, from
`G(x + v) - G(x) = ∫_0^1 ∂_v G(x + t v) dt` and the translation invariance of `∫ |∂_v G|`. -/
theorem lintegral_enorm_fwdDiff_le (v : V) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖fwdDiff v (G : V → ℂ) x‖ₑ ≤ ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ := by
  have hftc : ∀ x, fwdDiff v (G : V → ℂ) x =
      ∫ t in (0 : ℝ)..1, (∂_{v} G : 𝓢(V, ℂ)) (x + t • v) := fun x => by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => G (x + t • v))
        ((∂_{v} G : 𝓢(V, ℂ)) (x + t • v)) t := fun t _ => by
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      exact (G.hasFDerivAt (x + t • v)).comp_hasDerivAt t h1
    have hcont : Continuous fun t : ℝ => (∂_{v} G : 𝓢(V, ℂ)) (x + t • v) :=
      (SchwartzMap.continuous _).comp (continuous_const.add (continuous_id.smul continuous_const))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
    simp [fwdDiff]
  have hle : ∀ x, ‖fwdDiff v (G : V → ℂ) x‖ₑ ≤
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖(∂_{v} G : 𝓢(V, ℂ)) (x + t • v)‖ₑ := fun x => by
    rw [hftc x, intervalIntegral.integral_of_le zero_le_one]
    exact enorm_integral_le_lintegral_enorm _
  have hmeas : Measurable (Function.uncurry fun (x : V) (t : ℝ) =>
      ‖(∂_{v} G : 𝓢(V, ℂ)) (x + t • v)‖ₑ) :=
    ((SchwartzMap.continuous _).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).enorm.measurable
  calc ∫⁻ x, ‖fwdDiff v (G : V → ℂ) x‖ₑ
      ≤ ∫⁻ x, ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖(∂_{v} G : 𝓢(V, ℂ)) (x + t • v)‖ₑ :=
        lintegral_mono hle
    _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) (x + t • v)‖ₑ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ _t in Set.Ioc (0 : ℝ) 1, ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ :=
        lintegral_congr fun t =>
          lintegral_add_right_eq_self (fun x => ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ) (t • v)
    _ = ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
          ENNReal.ofReal_one, mul_one]

/-- **Differences of order `r` are bounded by line derivatives of order `r` in `L_1`**:
`‖Δ_v^r G‖_1 ≤ ‖∂_v^r G‖_1`. -/
theorem lintegral_enorm_higherDiff_le (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖(fwdDiff v)^[r] (G : V → ℂ) x‖ₑ ≤
      ∫⁻ x, ‖(∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) x‖ₑ := by
  induction r generalizing G with
  | zero => exact le_rfl
  | succ r ih =>
    calc ∫⁻ x, ‖(fwdDiff v)^[r + 1] (G : V → ℂ) x‖ₑ
        = ∫⁻ x, ‖(fwdDiff v)^[r] (fwdDiffSchwartz v G : V → ℂ) x‖ₑ := by
          rw [Function.iterate_succ_apply, ← coe_fwdDiffSchwartz]
      _ ≤ ∫⁻ x, ‖(∂^{fun _ : Fin r => v} (fwdDiffSchwartz v G) : 𝓢(V, ℂ)) x‖ₑ := ih _
      _ = ∫⁻ x, ‖fwdDiff v ((∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) : V → ℂ) x‖ₑ := by
          rw [iteratedLineDerivOp_fwdDiffSchwartz, coe_fwdDiffSchwartz]
      _ ≤ ∫⁻ x, ‖(∂_{v} (∂^{fun _ : Fin r => v} G) : 𝓢(V, ℂ)) x‖ₑ :=
          lintegral_enorm_fwdDiff_le v _
      _ = ∫⁻ x, ‖(∂^{fun _ : Fin (r + 1) => v} G : 𝓢(V, ℂ)) x‖ₑ := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|∂_v^r G(x)| ≤ ‖v‖^r ‖D^r G(x)‖`. -/
theorem enorm_iteratedLineDerivOp_le (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) (x : V) :
    ‖(∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) x‖ₑ ≤
      ‖v‖ₑ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ := by
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  have h := (iteratedFDeriv ℝ r (G : V → ℂ) x).le_opNorm (fun _ => v)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  calc ‖iteratedFDeriv ℝ r (G : V → ℂ) x (fun _ => v)‖ₑ
      = ENNReal.ofReal ‖iteratedFDeriv ℝ r (G : V → ℂ) x (fun _ => v)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖v‖ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖) :=
        ENNReal.ofReal_le_ofReal (h.trans_eq (mul_comm _ _))
    _ = ‖v‖ₑ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
          ofReal_norm]

/-- **`L_1` norms of differences of Schwartz functions**: `‖Δ_v^r G‖_1 ≤ ‖v‖^r ‖D^r G‖_1`. -/
theorem lintegral_enorm_higherDiff_schwartz_le (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖(fwdDiff v)^[r] (G : V → ℂ) x‖ₑ ≤
      ‖v‖ₑ ^ r * ∫⁻ x, ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ := by
  calc ∫⁻ x, ‖(fwdDiff v)^[r] (G : V → ℂ) x‖ₑ
      ≤ ∫⁻ x, ‖(∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) x‖ₑ := lintegral_enorm_higherDiff_le v r G
    _ ≤ ∫⁻ x, ‖v‖ₑ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ :=
        lintegral_mono fun x => enorm_iteratedLineDerivOp_le v r G x
    _ = ‖v‖ₑ ^ r * ∫⁻ x, ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)

/-- The derivatives of a Schwartz function are integrable: `‖D^r G‖_1 < ∞`. -/
theorem lintegral_enorm_iteratedFDeriv_ne_top (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ ≠ ∞ := by
  have h := (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume G 0 r).2
  simp only [pow_zero, one_mul, HasFiniteIntegral, enorm_norm] at h
  exact h.ne

/-! ### The inverse inequality -/

variable (V) in
/-- The constant of the inverse inequality, `2^r + ‖D^r Θ‖_1`. -/
noncomputable def bandInverseConst (r : ℕ) : ℝ≥0∞ :=
  2 ^ r + ∫⁻ x, ‖iteratedFDeriv ℝ r (bandKernelS (V := V) : V → ℂ) x‖ₑ

/-- The constant of the inverse inequality is finite. -/
theorem bandInverseConst_ne_top (r : ℕ) : bandInverseConst V r ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨by simp, lintegral_enorm_iteratedFDeriv_ne_top r _⟩

/-- **Differences of the band-limiting kernels in `L_1`**: `‖Δ_h^r Θ_j‖_1 ≤ (2^j ‖h‖)^r ‖D^r Θ‖_1`,
by the dilation `Δ_h^r Θ_j = (Δ_{2^j h}^r Θ)_{2^j}`. -/
theorem eLpNorm_higherDiff_Theta_le (r j : ℕ) (h : V) :
    eLpNorm ((fwdDiff h)^[r] (Theta (V := V) j)) 1 volume ≤
      ENNReal.ofReal (2 ^ j * ‖h‖) ^ r *
        ∫⁻ x, ‖iteratedFDeriv ℝ r (bandKernelS (V := V) : V → ℂ) x‖ₑ := by
  have hint : Integrable ((fwdDiff ((2 : ℝ) ^ j • h))^[r] (bandKernel (V := V))) :=
    integrable_higherDiff integrable_bandKernel r _
  rw [Theta, higherDiff_dilate, eLpNorm_dilate_one hint (by positivity),
    eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
  refine (lintegral_enorm_higherDiff_schwartz_le _ r bandKernelS).trans_eq ?_
  rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (by positivity)]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The inverse inequality for band-limited functions**: for `a ∈ E_j`,
`ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` with `C = 2^r + ‖D^r Θ‖_1` (and `k - j` truncated at
`0`). For `k ≥ j` and `‖h‖ ≤ 2^(-k)`, `Δ_h^r a = (Δ_h^r Θ_j) ⋆ a` and Young's inequality give
`‖Δ_h^r a‖_p ≤ (2^j ‖h‖)^r ‖D^r Θ‖_1 ‖a‖_p`. -/
theorem lpModulus_le_of_mem_bandSpace (hp : p ≠ ∞) (r : ℕ) {j k : ℕ}
    {a : Lp ℂ p (volume : Measure V)} (ha : a ∈ bandSpace hp j) :
    lpModulus p r a k ≤ bandInverseConst V r * dyadicWeight (-(r : ℝ)) (k - j) * ‖a‖ₑ := by
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpModulus_le r a k).trans (by gcongr; exact le_self_add)
  · rw [mem_bandSpace] at ha
    have hae : (a : V → ℂ) =ᵐ[volume] conv (Theta j) (a : V → ℂ) volume := by
      have h1 := convLp_apply_ae hp (integrable_Theta (V := V) j) a
      rw [ha] at h1
      exact h1
    set D := ∫⁻ x, ‖iteratedFDeriv ℝ r (bandKernelS (V := V) : V → ℂ) x‖ₑ
    rw [lpModulus, modulus_congr_ae hae]
    refine iSup₂_le fun h hh => ?_
    have h1 : eLpNorm ((fwdDiff h)^[r] (conv (Theta j) (a : V → ℂ) volume)) p volume ≤
        eLpNorm ((fwdDiff h)^[r] (Theta (V := V) j)) 1 volume * ‖a‖ₑ := by
      rw [eLpNorm_congr_ae (higherDiff_conv_ae Fact.out hp (integrable_Theta j) (Lp.memLp a) r h),
        Lp.enorm_def]
      exact eLpNorm_conv_le Fact.out hp
        (integrable_higherDiff (integrable_Theta j) r h).aestronglyMeasurable
        (Lp.aestronglyMeasurable a)
    have h2 : ENNReal.ofReal (2 ^ j * ‖h‖) ^ r ≤ dyadicWeight (-(r : ℝ)) (k - j) := by
      rw [← ENNReal.rpow_natCast]
      exact ENNReal.ofReal_two_pow_mul_rpow_le hjk hh (Nat.cast_nonneg r)
    calc eLpNorm ((fwdDiff h)^[r] (conv (Theta j) (a : V → ℂ) volume)) p volume
        ≤ ENNReal.ofReal (2 ^ j * ‖h‖) ^ r * D * ‖a‖ₑ :=
          h1.trans (by gcongr; exact eLpNorm_higherDiff_Theta_le r j h)
      _ ≤ dyadicWeight (-(r : ℝ)) (k - j) * D * ‖a‖ₑ := by gcongr
      _ ≤ bandInverseConst V r * dyadicWeight (-(r : ℝ)) (k - j) * ‖a‖ₑ := by
          rw [mul_comm (dyadicWeight _ _) D]
          gcongr
          exact le_add_self

end Rd
