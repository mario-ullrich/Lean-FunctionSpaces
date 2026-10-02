/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.MomentKernels
public import FunctionSpaces.Rd.BesovDifferences

/-!
# Local means

A **bump for local means** is a smooth `g : V → ℂ` with `∫ g = 1` that vanishes outside the ball
of radius `R` (`Rd.LocalMeansBump`). With the moment kernel `m` of order `L`
(`Rd.momentKernel`) and its dilations `m_{2^j}` (`Rd.LocalMeansBump.scaled`), the **local means**
of `f ∈ L_p(V)` are `k_j ⋆ f` (`Rd.LocalMeansBump.localMean`) with the kernels

`k_0 = m`,  `k_j = m_{2^j} - m_{2^(j-1)}`   (`Rd.LocalMeansBump.kernel`),

and the **local means quasi-norm** is `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q}`
(`Rd.LocalMeansBump.localMeansNorm`). With the dual kernels `η_0 = m`,
`η_j = m_{2^j} + m_{2^(j-1)}` (`Rd.LocalMeansBump.dual`), the identity `a² - b² = (a - b)(a + b)`
in the commutative convolution algebra gives the **reproducing formula**
`∑_{j ≤ J} η_j ⋆ k_j ⋆ f = m_{2^J} ⋆ m_{2^J} ⋆ f → f` in `L_p`
(`Rd.LocalMeansBump.sum_dual_localMean`, `Rd.LocalMeansBump.tendsto_sum_dual_localMean`).

**Local means and differences** (`Rd.LocalMeansBump.besov_iff_localMeans`): for `1 ≤ p < ∞`,
`0 < s < L` and `1 ≤ q ≤ ∞`, `‖f‖_p + ‖(2^(ks) ω_L(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff the local means
quasi-norm is finite, with equivalent quasi-norms:

* `‖k_j ⋆ f‖_p ≤ 2 ‖g‖_1 (1 + R)^L ω_L(f, 2^(1-j))_p`, since `f - m_c ⋆ f` averages differences
  of order `L` (`Rd.LocalMeansBump.localMeansNorm_le`);
* `ω_L(η_j ⋆ h, 2^(-i))_p ≤ C min(1, 2^((j-i)L)) ‖h‖_p` by the differences of the smooth kernels
  in `L_1`; the reproducing formula and Hardy's inequalities in both directions
  (`ENNReal.lqNorm_almostDiagonal_le`) bound the moduli by the local means
  (`Rd.LocalMeansBump.modNorm_le_localMeansNorm`).

Local means therefore describe the same spaces as band-limited approximation, Littlewood–Paley
blocks and differences (`Rd.LocalMeansBump.memApprox_bandScheme_iff_localMeans`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal SchwartzMap

open ENNReal (lqNorm dyadicWeight)

/-! ### Two lemmas on series -/

/-- **An almost diagonal sum in weighted `ℓ_q`**:
`‖(2^(is) ∑_j c_{ij} a_j)_i‖_{ℓ_q} ≤ ((1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹) ‖(2^(js) a_j)_j‖_{ℓ_q}`
with `c_{ij} = 2^(-(i-j)L)` for `j ≤ i` and `c_{ij} = 1` for `j > i`, by Hardy's inequalities for
the sum below and the tail above the diagonal (finite for `0 < s < L`). -/
theorem ENNReal.lqNorm_almostDiagonal_le {q : ℝ≥0∞} (hq : 1 ≤ q) (s L : ℝ) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun i => dyadicWeight s i *
      ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j) ≤
      ((1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) *
        lqNorm q (fun j => dyadicWeight s j * a j) := by
  set X := lqNorm q (fun j => dyadicWeight s j * a j)
  have hsplit : ∀ i, ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j =
      ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j + ∑' t, a (t + (i + 1)) :=
    fun i => by
      rw [← Summable.sum_add_tsum_nat_add' (k := i + 1) ENNReal.summable]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hji : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        simp only [hji, ↓reduceIte]
      · refine tsum_congr fun t => ?_
        have hti : ¬(t + (i + 1) ≤ i) := by omega
        simp only [hti, ↓reduceIte, one_mul]
  have hw : ∀ i j, j ≤ i → dyadicWeight s i * dyadicWeight (-L) (i - j) =
      dyadicWeight (-(L - s)) i * (dyadicWeight (L - s) j * dyadicWeight s j) := by
    intro i j hji
    simp only [dyadicWeight]
    rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
      ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
      ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, Nat.cast_sub hji]
    congr 1
    ring
  have hP : lqNorm q (fun i => dyadicWeight s i *
      ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j) ≤
      (1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ * X := by
    have h := ENNReal.hardy_sum_le hq (L - s)
      (fun j => dyadicWeight (L - s) j * (dyadicWeight s j * a j))
    have h1 : (fun i => dyadicWeight s i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j) =
        fun i => dyadicWeight (-(L - s)) i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (L - s) j * (dyadicWeight s j * a j) := by
      funext i
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← mul_assoc, hw i j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
      ring
    have h2 : (fun k => dyadicWeight (-(L - s)) k *
        (dyadicWeight (L - s) k * (dyadicWeight s k * a k))) = fun k => dyadicWeight s k * a k := by
      funext k
      rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
    rw [h1]
    rw [h2] at h
    exact h
  have hT : lqNorm q (fun i => dyadicWeight s i * ∑' t, a (t + (i + 1))) ≤
      (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
    refine (ENNReal.lqNorm_mono fun i => ?_).trans (ENNReal.hardy_tail_le hq s a)
    have hinj : Function.Injective fun t : ℕ => t + 1 := add_left_injective 1
    have htail : ∑' t, a (t + (i + 1)) ≤ ∑' n, a (i + n) :=
      calc ∑' t, a (t + (i + 1)) = ∑' t, (fun n => a (i + n)) (t + 1) := by
            congr 1
            funext t
            congr 1
            omega
        _ ≤ ∑' n, a (i + n) := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun n => a (i + n))
    exact mul_le_mul' le_rfl htail
  calc lqNorm q (fun i => dyadicWeight s i *
        ∑' j, (if j ≤ i then dyadicWeight (-L) (i - j) else 1) * a j)
      = lqNorm q (fun i => dyadicWeight s i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j +
          dyadicWeight s i * ∑' t, a (t + (i + 1))) := by
        congr 1
        funext i
        rw [hsplit i, mul_add]
    _ ≤ lqNorm q (fun i => dyadicWeight s i *
          ∑ j ∈ Finset.range (i + 1), dyadicWeight (-L) (i - j) * a j) +
        lqNorm q (fun i => dyadicWeight s i * ∑' t, a (t + (i + 1))) :=
        ENNReal.lqNorm_add_le hq _ _
    _ ≤ (1 - (2 : ℝ≥0∞) ^ (-(L - s)))⁻¹ * X + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := add_le_add hP hT
    _ = _ := by ring

namespace Rd

/-- **Subadditive functionals and series**: if `Q` is subadditive, `Q a ≤ C ‖a‖` with `C < ∞`, and
the partial sums of `∑ u_j` converge to `f`, then `Q f ≤ ∑_j Q(u_j)`. -/
theorem le_tsum_of_tendsto_sum {E : Type*} [NormedAddCommGroup E] {Q : E → ℝ≥0∞} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hadd : ∀ a b, Q (a + b) ≤ Q a + Q b) (hle : ∀ a, Q a ≤ C * ‖a‖ₑ)
    {u : ℕ → E} {f : E}
    (hu : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), u j) atTop (𝓝 f)) :
    Q f ≤ ∑' j, Q (u j) := by
  have hsum : ∀ s : Finset ℕ, Q (∑ j ∈ s, u j) ≤ ∑ j ∈ s, Q (u j) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hle 0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (hadd _ _).trans (add_le_add le_rfl ih)
  have hJ : ∀ J, Q f ≤ ∑' j, Q (u j) + C * ‖f - ∑ j ∈ Finset.range (J + 1), u j‖ₑ := fun J => by
    calc Q f = Q (∑ j ∈ Finset.range (J + 1), u j + (f - ∑ j ∈ Finset.range (J + 1), u j)) := by
          rw [add_sub_cancel]
      _ ≤ Q (∑ j ∈ Finset.range (J + 1), u j) + Q (f - ∑ j ∈ Finset.range (J + 1), u j) :=
          hadd _ _
      _ ≤ ∑' j, Q (u j) + C * ‖f - ∑ j ∈ Finset.range (J + 1), u j‖ₑ :=
          add_le_add ((hsum _).trans (ENNReal.sum_le_tsum _)) (hle _)
  have h1 : Tendsto (fun J => f - ∑ j ∈ Finset.range (J + 1), u j) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := f)).sub hu
    rwa [sub_self] at this
  have h2 : Tendsto (fun J => ‖f - ∑ j ∈ Finset.range (J + 1), u j‖ₑ) atTop (𝓝 0) := by
    have h3 := (continuous_enorm.tendsto (0 : E)).comp h1
    rw [enorm_zero] at h3
    exact h3
  have hlim : Tendsto (fun J => ∑' j, Q (u j) + C * ‖f - ∑ j ∈ Finset.range (J + 1), u j‖ₑ)
      atTop (𝓝 (∑' j, Q (u j) + C * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul h2 (Or.inr hC))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hJ)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Bumps and their kernels -/

variable (V) in
/-- A **bump for local means**: a smooth function with integral `1` that vanishes outside the
ball of radius `radius`. -/
structure LocalMeansBump where
  /-- The function. -/
  toFun : V → ℂ
  /-- The radius of the ball outside of which the bump vanishes. -/
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toFun
  eq_zero : ∀ z, radius < ‖z‖ → toFun z = 0
  integral_eq_one : ∫ z, toFun z = 1

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- A bump has compact support. -/
theorem hasCompactSupport : HasCompactSupport b.toFun :=
  HasCompactSupport.intro (isCompact_closedBall 0 b.radius) fun x hx =>
    b.eq_zero x (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

/-- A bump is integrable. -/
theorem integrable : Integrable b.toFun :=
  b.contDiff.continuous.integrable_of_hasCompactSupport b.hasCompactSupport

/-- The moment kernel of a bump is smooth. -/
theorem contDiff_momentKernel (L : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (momentKernel b.toFun L) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (contDiff_const.mul (b.contDiff.comp (contDiff_const_smul _)))

/-- The moment kernel of a bump vanishes outside the ball of radius `L R`. -/
theorem momentKernel_eq_zero (L : ℕ) {x : V} (hx : L * b.radius < ‖x‖) :
    momentKernel b.toFun L x = 0 := by
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl' : (l : ℝ) + 1 ≤ L := by exact_mod_cast Finset.mem_range.1 hl
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  rw [dilate, b.eq_zero _ ?_, mul_zero, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (by positivity), one_div, inv_mul_eq_div, lt_div_iff₀ hpos]
  calc b.radius * ((l : ℝ) + 1) ≤ b.radius * L := mul_le_mul_of_nonneg_left hl' b.radius_nonneg
    _ = L * b.radius := mul_comm _ _
    _ < ‖x‖ := hx

/-- The moment kernel of a bump has compact support. -/
theorem hasCompactSupport_momentKernel (L : ℕ) : HasCompactSupport (momentKernel b.toFun L) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (L * b.radius)) fun x hx =>
    b.momentKernel_eq_zero L (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

/-- The moment kernel of a bump as a Schwartz function. -/
noncomputable def momentSchwartz (L : ℕ) : 𝓢(V, ℂ) :=
  (b.hasCompactSupport_momentKernel L).toSchwartzMap (b.contDiff_momentKernel L)

/-- The `L_1` norm of the derivatives of order `L` of the moment kernel. -/
noncomputable def derivNorm (L : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ‖iteratedFDeriv ℝ L (b.momentSchwartz L : V → ℂ) x‖ₑ

/-- The moment kernel at the dyadic scale `2^j`, `m_{2^j} = 2^(jn) m(2^j ·)`. -/
noncomputable def scaled (L j : ℕ) : V → ℂ := dilate (2 ^ j) (momentKernel b.toFun L)

/-- The **local means kernels** `k_0 = m`, `k_j = m_{2^j} - m_{2^(j-1)}`. -/
noncomputable def kernel (L : ℕ) : ℕ → V → ℂ
  | 0 => b.scaled L 0
  | j + 1 => b.scaled L (j + 1) - b.scaled L j

/-- The **dual kernels** `η_0 = m`, `η_j = m_{2^j} + m_{2^(j-1)}`. -/
noncomputable def dual (L : ℕ) : ℕ → V → ℂ
  | 0 => b.scaled L 0
  | j + 1 => b.scaled L (j + 1) + b.scaled L j

/-- The dilated moment kernels are integrable. -/
theorem integrable_scaled (L j : ℕ) : Integrable (b.scaled L j) :=
  integrable_dilate (integrable_momentKernel b.integrable L) (by positivity)

/-- The local means kernels are integrable. -/
theorem integrable_kernel (L j : ℕ) : Integrable (b.kernel L j) := by
  cases j with
  | zero => exact b.integrable_scaled L 0
  | succ j => exact (b.integrable_scaled L (j + 1)).sub (b.integrable_scaled L j)

/-- The dual kernels are integrable. -/
theorem integrable_dual (L j : ℕ) : Integrable (b.dual L j) := by
  cases j with
  | zero => exact b.integrable_scaled L 0
  | succ j => exact (b.integrable_scaled L (j + 1)).add (b.integrable_scaled L j)

/-- `‖m_{2^j}‖_1 = ‖m‖_1`. -/
theorem eLpNorm_scaled_one (L j : ℕ) :
    eLpNorm (b.scaled L j) 1 volume = eLpNorm (momentKernel b.toFun L) 1 volume :=
  eLpNorm_dilate_one (integrable_momentKernel b.integrable L) (by positivity)

/-- `‖η_j‖_1 ≤ 2 ‖m‖_1`. -/
theorem eLpNorm_dual_one_le (L j : ℕ) :
    eLpNorm (b.dual L j) 1 volume ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume := by
  cases j with
  | zero =>
    rw [two_mul]
    exact (b.eLpNorm_scaled_one L 0).le.trans le_self_add
  | succ j =>
    show eLpNorm (b.scaled L (j + 1) + b.scaled L j) 1 volume ≤ _
    calc eLpNorm (b.scaled L (j + 1) + b.scaled L j) 1 volume
        ≤ eLpNorm (b.scaled L (j + 1)) 1 volume + eLpNorm (b.scaled L j) 1 volume :=
          eLpNorm_add_le le_rfl
      _ = 2 * eLpNorm (momentKernel b.toFun L) 1 volume := by
          rw [b.eLpNorm_scaled_one, b.eLpNorm_scaled_one, two_mul]

/-- **Differences of the dilated moment kernels in `L_1`**:
`‖Δ_v^L m_{2^j}‖_1 ≤ (2^j ‖v‖)^L ‖D^L m‖_1`. -/
theorem eLpNorm_iterDiff_scaled_le (L j : ℕ) (v : V) :
    eLpNorm ((fwdDiff v)^[L] (b.scaled L j)) 1 volume ≤
      ENNReal.ofReal (2 ^ j * ‖v‖) ^ L * b.derivNorm L := by
  have hint : Integrable ((fwdDiff ((2 : ℝ) ^ j • v))^[L] (momentKernel b.toFun L)) :=
    integrable_iterDiff (integrable_momentKernel b.integrable L) L _
  rw [scaled, iterDiff_dilate, eLpNorm_dilate_one hint (by positivity),
    eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
  refine (lintegral_enorm_iterDiff_schwartz_le _ L (b.momentSchwartz L)).trans_eq ?_
  rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (by positivity)]
  rfl

/-- `‖Δ_v^L m_{2^j}‖_1 ≤ 2^L ‖m‖_1`. -/
theorem eLpNorm_iterDiff_scaled_le' (L j : ℕ) (v : V) :
    eLpNorm ((fwdDiff v)^[L] (b.scaled L j)) 1 volume ≤
      2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume := by
  rw [← b.eLpNorm_scaled_one L j]
  exact eLpNorm_iterDiff_le (b.integrable_scaled L j).aestronglyMeasurable le_rfl L v

/-- The constant `2 (‖D^L m‖_1 + 2^L ‖m‖_1)` of the differences of the dual kernels. -/
noncomputable def dualConst (L : ℕ) : ℝ≥0∞ :=
  2 * (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume)

/-- The constant of the differences of the dual kernels is finite. -/
theorem dualConst_ne_top (L : ℕ) : b.dualConst L ≠ ∞ :=
  ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.2
    ⟨lintegral_enorm_iteratedFDeriv_ne_top L _, ENNReal.mul_ne_top (by simp)
      (memLp_one_iff_integrable.2 (integrable_momentKernel b.integrable L)).eLpNorm_ne_top⟩)

/-- One dilated kernel at a scale at most `2^j`: `‖Δ_v^L m_{2^l}‖_1 ≤ C 2^(-(i-j)L)` for
`l ≤ j ≤ i` and `‖v‖ ≤ 2^(-i)`, and `≤ C` always. -/
theorem eLpNorm_iterDiff_scaled_le_dyadic (L : ℕ) {i j l : ℕ} (hlj : l ≤ j) {v : V}
    (hv : ‖v‖ ≤ 1 / 2 ^ i) :
    eLpNorm ((fwdDiff v)^[L] (b.scaled L l)) 1 volume ≤
      (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume) *
        (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) := by
  split_ifs with hji
  · have hw : ENNReal.ofReal (2 ^ l * ‖v‖) ^ L ≤ dyadicWeight (-(L : ℝ)) (i - j) := by
      rw [← ENNReal.rpow_natCast]
      exact (Interval.ofReal_two_pow_mul_rpow_le (hlj.trans hji) hv (Nat.cast_nonneg L)).trans
        (ENNReal.dyadicWeight_anti (by simp) (by omega))
    calc eLpNorm ((fwdDiff v)^[L] (b.scaled L l)) 1 volume
        ≤ ENNReal.ofReal (2 ^ l * ‖v‖) ^ L * b.derivNorm L := b.eLpNorm_iterDiff_scaled_le L l v
      _ ≤ dyadicWeight (-(L : ℝ)) (i - j) * b.derivNorm L := by gcongr
      _ ≤ (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume) *
            dyadicWeight (-(L : ℝ)) (i - j) := by
          rw [mul_comm]
          gcongr
          exact le_self_add
  · rw [mul_one]
    exact (b.eLpNorm_iterDiff_scaled_le' L l v).trans le_add_self

/-- **Differences of the dual kernels in `L_1`**: for `‖v‖ ≤ 2^(-i)`,
`‖Δ_v^L η_j‖_1 ≤ C 2^(-(i-j)L)` if `j ≤ i`, and `‖Δ_v^L η_j‖_1 ≤ C` if `j > i`. -/
theorem eLpNorm_iterDiff_dual_le (L : ℕ) {i j : ℕ} {v : V} (hv : ‖v‖ ≤ 1 / 2 ^ i) :
    eLpNorm ((fwdDiff v)^[L] (b.dual L j)) 1 volume ≤
      b.dualConst L * (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) := by
  set B := (b.derivNorm L + 2 ^ L * eLpNorm (momentKernel b.toFun L) 1 volume) *
    (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1)
  have h2 : b.dualConst L * (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) = B + B := by
    rw [dualConst, ← two_mul, mul_assoc]
  rw [h2]
  cases j with
  | zero =>
    exact (b.eLpNorm_iterDiff_scaled_le_dyadic L le_rfl hv).trans le_self_add
  | succ j =>
    show eLpNorm ((fwdDiff v)^[L] (b.scaled L (j + 1) + b.scaled L j)) 1 volume ≤ B + B
    rw [fwdDiff_iter_add]
    exact (eLpNorm_add_le le_rfl).trans (add_le_add
      (b.eLpNorm_iterDiff_scaled_le_dyadic L le_rfl hv)
      (b.eLpNorm_iterDiff_scaled_le_dyadic L (Nat.le_succ j) hv))

/-! ### Local means and the reproducing formula -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **local means** `f ↦ k_j ⋆ f` on `L_p`. -/
noncomputable def localMean (hp : p ≠ ∞) (L j : ℕ) :
    Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  convLp hp (b.integrable_kernel L j)

/-- **The reproducing formula, partial sums**: `∑_{j ≤ J} η_j ⋆ k_j ⋆ f = m_{2^J} ⋆ m_{2^J} ⋆ f`,
from `a² - b² = (a - b)(a + b)` for the commuting operators `a = m_{2^(J+1)} ⋆`,
`b = m_{2^J} ⋆`. -/
theorem sum_dual_localMean (hp : p ≠ ∞) (L J : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ∑ j ∈ Finset.range (J + 1), convLp hp (b.integrable_dual L j) (b.localMean hp L j f) =
      convLp hp (b.integrable_scaled L J) (convLp hp (b.integrable_scaled L J) f) := by
  induction J with
  | zero =>
    rw [Finset.sum_range_one]
    rfl
  | succ J ih =>
    have hk : b.localMean hp L (J + 1) f = convLp hp (b.integrable_scaled L (J + 1)) f -
        convLp hp (b.integrable_scaled L J) f :=
      convLp_sub_kernel hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J) f
    have hd : convLp hp (b.integrable_dual L (J + 1)) (b.localMean hp L (J + 1) f) =
        convLp hp (b.integrable_scaled L (J + 1)) (b.localMean hp L (J + 1) f) +
          convLp hp (b.integrable_scaled L J) (b.localMean hp L (J + 1) f) :=
      convLp_add_kernel hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J) _
    rw [Finset.sum_range_succ, ih, hd, hk, map_sub, map_sub,
      convLp_comm hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J)]
    abel

/-- **The reproducing formula**: `∑_j η_j ⋆ k_j ⋆ f = f` in `L_p`, since
`m_{2^J} ⋆ m_{2^J} ⋆ f → f` (`m` is an approximate identity, `Rd.tendsto_convLp_dilate`). -/
theorem tendsto_sum_dual_localMean (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    (f : Lp ℂ p (volume : Measure V)) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L j) (b.localMean hp L j f)) atTop (𝓝 f) := by
  simp_rw [b.sum_dual_localMean hp L]
  have h : Tendsto (fun J => convLp hp (b.integrable_scaled L J) f) atTop (𝓝 f) :=
    tendsto_convLp_dilate hp (integrable_momentKernel b.integrable L)
      (integral_momentKernel b.integrable b.integral_eq_one hL) (c := fun J : ℕ => (2 : ℝ) ^ J)
      (fun J => pow_ne_zero J two_ne_zero) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) f
  set C := (eLpNorm (momentKernel b.toFun L) 1 volume).toReal
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun J => norm_nonneg _) (fun J => ?_) (by simpa using h.const_mul (C + 1))
  have hA : ∀ g : Lp ℂ p (volume : Measure V),
      ‖convLp hp (b.integrable_scaled L J) g‖ ≤ C * ‖g‖ := fun g => by
    have h1 := norm_convLp_le hp (b.integrable_scaled L J) g
    rwa [b.eLpNorm_scaled_one] at h1
  calc ‖convLp hp (b.integrable_scaled L J) (convLp hp (b.integrable_scaled L J) f) - f‖
      = ‖convLp hp (b.integrable_scaled L J) (convLp hp (b.integrable_scaled L J) f - f) +
          (convLp hp (b.integrable_scaled L J) f - f)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ C * ‖convLp hp (b.integrable_scaled L J) f - f‖ +
          ‖convLp hp (b.integrable_scaled L J) f - f‖ :=
        (norm_add_le _ _).trans (add_le_add (hA _) le_rfl)
    _ = (C + 1) * ‖convLp hp (b.integrable_scaled L J) f - f‖ := by ring

/-- The **local means quasi-norm** `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q}`. -/
noncomputable def localMeansNorm (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight s j * ‖b.localMean hp L j f‖ₑ)

/-! ### Local means are bounded by the modulus -/

/-- `‖k_0 ⋆ f‖_p ≤ ‖m‖_1 ‖f‖_p`. -/
theorem enorm_localMean_zero_le (hp : p ≠ ∞) (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖b.localMean hp L 0 f‖ₑ ≤ eLpNorm (momentKernel b.toFun L) 1 volume * ‖f‖ₑ :=
  (enorm_convLp_le hp (b.integrable_kernel L 0) f).trans_eq
    (congrArg (· * ‖f‖ₑ) (b.eLpNorm_scaled_one L 0))

/-- **Local means are bounded by the modulus**:
`‖k_{j+1} ⋆ f‖_p ≤ 2 ‖g‖_1 (1 + R)^L ω_L(f, 2^(-j))_p`, since
`k_{j+1} ⋆ f = (f - m_{2^j} ⋆ f) - (f - m_{2^(j+1)} ⋆ f)` and `f - m_c ⋆ f` averages differences
with steps of length at most `R/c`. -/
theorem enorm_localMean_succ_le (hp : p ≠ ∞) (L j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖b.localMean hp L (j + 1) f‖ₑ ≤
      2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j := by
  set A := ∫⁻ z, ‖b.toFun z‖ₑ
  have hk : b.localMean hp L (j + 1) f = (f - convLp hp (b.integrable_scaled L j) f) -
      (f - convLp hp (b.integrable_scaled L (j + 1)) f) := by
    rw [show b.localMean hp L (j + 1) f = convLp hp (b.integrable_scaled L (j + 1)) f -
        convLp hp (b.integrable_scaled L j) f from
      convLp_sub_kernel hp (b.integrable_scaled L (j + 1)) (b.integrable_scaled L j) f]
    abel
  have hω : ∀ i, ‖f - convLp hp (b.integrable_scaled L i) f‖ₑ ≤
      A * modulus volume L p (f : V → ℂ) (b.radius / 2 ^ i) := fun i =>
    enorm_sub_convLp_momentKernel_le hp b.integrable b.integral_eq_one b.eq_zero L
      (by positivity) f
  have hmono : modulus volume L p (f : V → ℂ) (b.radius / 2 ^ (j + 1)) ≤
      modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) :=
    modulus_mono L p _ (div_le_div_of_nonneg_left b.radius_nonneg (by positivity)
      (pow_le_pow_right₀ one_le_two (Nat.le_succ j)))
  have hdil : modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) ≤
      ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j := by
    rw [lpModulus, show b.radius / 2 ^ j = b.radius * (1 / 2 ^ j) by ring]
    exact modulus_mul_le (Lp.aestronglyMeasurable f) Fact.out L b.radius_nonneg (by positivity)
  calc ‖b.localMean hp L (j + 1) f‖ₑ
      ≤ ‖f - convLp hp (b.integrable_scaled L j) f‖ₑ +
          ‖f - convLp hp (b.integrable_scaled L (j + 1)) f‖ₑ := by
        rw [hk]
        exact enorm_sub_le
    _ ≤ A * modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) +
          A * modulus volume L p (f : V → ℂ) (b.radius / 2 ^ j) :=
        add_le_add (hω j) ((hω (j + 1)).trans (by gcongr))
    _ ≤ A * (ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j) +
          A * (ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j) := by gcongr
    _ = 2 * A * ENNReal.ofReal (1 + b.radius) ^ L * lpModulus p L f j := by ring

/-- The constant of the upper bound, `‖m‖_1 + 2^s · 2 ‖g‖_1 (1 + R)^L`. -/
noncomputable def upperConst (L : ℕ) (s : ℝ) : ℝ≥0∞ :=
  eLpNorm (momentKernel b.toFun L) 1 volume +
    2 ^ s * (2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L)

/-- The constant of the upper bound is finite. -/
theorem upperConst_ne_top (L : ℕ) (s : ℝ) : b.upperConst L s ≠ ∞ :=
  ENNReal.add_ne_top.2
    ⟨(memLp_one_iff_integrable.2 (integrable_momentKernel b.integrable L)).eLpNorm_ne_top,
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg' (by norm_num) (by simp))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) b.integrable.2.ne)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))⟩

/-- **The local means quasi-norm is bounded by the modulus**:
`‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q} ≤ C (‖f‖_p + ‖(2^(js) ω_L(f, 2^(-j))_p)_j‖_{ℓ_q})`. -/
theorem localMeansNorm_le (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure V)) :
    b.localMeansNorm hp L s q f ≤
      b.upperConst L s * (‖f‖ₑ + lqNorm q (fun j => dyadicWeight s j * lpModulus p L f j)) := by
  set C' := 2 * (∫⁻ z, ‖b.toFun z‖ₑ) * ENNReal.ofReal (1 + b.radius) ^ L
  set M := eLpNorm (momentKernel b.toFun L) 1 volume
  set Λ := lqNorm q (fun j => dyadicWeight s j * lpModulus p L f j)
  have htail : lqNorm q (fun j => dyadicWeight s (j + 1) * ‖b.localMean hp L (j + 1) f‖ₑ) ≤
      2 ^ s * C' * Λ := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun j => ?_
    rw [ENNReal.dyadicWeight_succ]
    calc 2 ^ s * dyadicWeight s j * ‖b.localMean hp L (j + 1) f‖ₑ
        ≤ 2 ^ s * dyadicWeight s j * (C' * lpModulus p L f j) :=
          mul_le_mul' le_rfl (b.enorm_localMean_succ_le hp L j f)
      _ = 2 ^ s * C' * (dyadicWeight s j * lpModulus p L f j) := by ring
  calc b.localMeansNorm hp L s q f
      ≤ dyadicWeight s 0 * ‖b.localMean hp L 0 f‖ₑ +
          lqNorm q (fun j => dyadicWeight s (j + 1) * ‖b.localMean hp L (j + 1) f‖ₑ) :=
        ENNReal.lqNorm_le_head_add_shift hq _
    _ ≤ M * ‖f‖ₑ + 2 ^ s * C' * Λ := by
        rw [ENNReal.dyadicWeight_zero_right, one_mul]
        exact add_le_add (b.enorm_localMean_zero_le hp L f) htail
    _ ≤ b.upperConst L s * ‖f‖ₑ + b.upperConst L s * Λ := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = b.upperConst L s * (‖f‖ₑ + Λ) := by ring

/-! ### The modulus is bounded by the local means -/

/-- **The moduli of the reproducing terms**: for `η_j ⋆ h`,
`ω_L(η_j ⋆ h, 2^(-i))_p ≤ C c_{ij} ‖h‖_p` with `c_{ij} = 2^(-(i-j)L)` for `j ≤ i` and `1` for
`j > i`. -/
theorem lpModulus_dual_le (hp : p ≠ ∞) (L i j : ℕ) (h : Lp ℂ p (volume : Measure V)) :
    lpModulus p L (convLp hp (b.integrable_dual L j) h) i ≤
      b.dualConst L * (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * ‖h‖ₑ :=
  lpModulus_convLp_le hp (b.integrable_dual L j) L i (fun _ hv => b.eLpNorm_iterDiff_dual_le L hv) h

/-- The constant of the synthesis estimate,
`2 ‖m‖_1 (1 - 2^(-s))⁻¹ + C_η ((1 - 2^(-(L-s)))⁻¹ + (1 - 2^(-s))⁻¹)`. -/
noncomputable def synthConst (L : ℕ) (s : ℝ) : ℝ≥0∞ :=
  2 * eLpNorm (momentKernel b.toFun L) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ +
    b.dualConst L * ((1 - (2 : ℝ≥0∞) ^ (-((L : ℝ) - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹)

/-- The constant of the synthesis estimate is finite for `0 < s < L`. -/
theorem synthConst_ne_top {L : ℕ} {s : ℝ} (hs : 0 < s) (hsL : s < L) : b.synthConst L s ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (memLp_one_iff_integrable.2 (integrable_momentKernel b.integrable L)).eLpNorm_ne_top)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs),
    ENNReal.mul_ne_top (b.dualConst_ne_top L) (ENNReal.add_ne_top.2
      ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith),
        ENNReal.one_sub_two_rpow_neg_inv_ne_top hs⟩)⟩

/-- **Synthesis with the dual kernels**: if `F = ∑_j η_j ⋆ h_j` in `L_p` (as the limit of the
partial sums), then for `0 < s < L`,
`‖F‖_p + ‖(2^(is) ω_L(F, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖h_j‖_p)_j‖_{ℓ_q}`, by the moduli of
the terms (`Rd.LocalMeansBump.lpModulus_dual_le`) and Hardy's inequalities. -/
theorem modNorm_le_of_tendsto (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)} {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hrep : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L j) (h j)) atTop (𝓝 F)) :
    ‖F‖ₑ + lqNorm q (fun i => dyadicWeight s i * lpModulus p L F i) ≤
      b.synthConst L s * lqNorm q (fun j => dyadicWeight s j * ‖h j‖ₑ) := by
  set a : ℕ → ℝ≥0∞ := fun j => ‖h j‖ₑ
  set X := lqNorm q (fun j => dyadicWeight s j * a j)
  set M := eLpNorm (momentKernel b.toFun L) 1 volume
  -- the norm of `f`
  have hnorm : ‖F‖ₑ ≤ 2 * M * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
    have h1 : ‖F‖ₑ ≤ ∑' j, ‖convLp hp (b.integrable_dual L j) (h j)‖ₑ :=
      le_tsum_of_tendsto_sum (C := 1) ENNReal.one_ne_top (fun x y => enorm_add_le x y)
        (fun x => by rw [one_mul]) hrep
    have h2 : ∀ j, ‖convLp hp (b.integrable_dual L j) (h j)‖ₑ ≤
        2 * M * (dyadicWeight (-s) j * X) := fun j => by
      have hX : dyadicWeight s j * a j ≤ X :=
        ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne' (fun j => dyadicWeight s j * a j) j
      calc ‖convLp hp (b.integrable_dual L j) (h j)‖ₑ
          ≤ eLpNorm (b.dual L j) 1 volume * a j := enorm_convLp_le hp _ _
        _ ≤ 2 * M * (dyadicWeight (-s) j * (dyadicWeight s j * a j)) := by
            rw [← mul_assoc (dyadicWeight (-s) j), ENNReal.dyadicWeight_neg_mul_self, one_mul]
            gcongr
            exact b.eLpNorm_dual_one_le L j
        _ ≤ 2 * M * (dyadicWeight (-s) j * X) := by gcongr
    calc ‖F‖ₑ ≤ ∑' j, 2 * M * (dyadicWeight (-s) j * X) := h1.trans (ENNReal.tsum_le_tsum h2)
      _ = 2 * M * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_dyadicWeight_neg]
          ring
  -- the moduli
  have hmod : ∀ i, lpModulus p L F i ≤ b.dualConst L *
      ∑' j, (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * a j := fun i => by
    have h1 : lpModulus p L F i ≤
        ∑' j, lpModulus p L (convLp hp (b.integrable_dual L j) (h j)) i :=
      le_tsum_of_tendsto_sum (C := 2 ^ L) (by simp) (fun x y => lpModulus_add_le L x y i)
        (fun x => lpModulus_le L x i) hrep
    refine h1.trans ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← mul_assoc]
    exact b.lpModulus_dual_le hp L i j _
  have hlq : lqNorm q (fun i => dyadicWeight s i * lpModulus p L F i) ≤
      b.dualConst L *
        (((1 - (2 : ℝ≥0∞) ^ (-((L : ℝ) - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * X) := by
    calc lqNorm q (fun i => dyadicWeight s i * lpModulus p L F i)
        ≤ lqNorm q (fun i => b.dualConst L * (dyadicWeight s i *
            ∑' j, (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * a j)) :=
          ENNReal.lqNorm_mono fun i => by
            calc dyadicWeight s i * lpModulus p L F i
                ≤ dyadicWeight s i * (b.dualConst L *
                    ∑' j, (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * a j) :=
                  mul_le_mul' le_rfl (hmod i)
              _ = b.dualConst L * (dyadicWeight s i *
                    ∑' j, (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * a j) := by
                  ring
      _ = b.dualConst L * lqNorm q (fun i => dyadicWeight s i *
            ∑' j, (if j ≤ i then dyadicWeight (-(L : ℝ)) (i - j) else 1) * a j) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ b.dualConst L *
            (((1 - (2 : ℝ≥0∞) ^ (-((L : ℝ) - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * X) :=
          mul_le_mul' le_rfl (ENNReal.lqNorm_almostDiagonal_le hq s L a)
  calc ‖F‖ₑ + lqNorm q (fun i => dyadicWeight s i * lpModulus p L F i)
      ≤ 2 * M * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X + b.dualConst L *
          (((1 - (2 : ℝ≥0∞) ^ (-((L : ℝ) - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * X) :=
        add_le_add hnorm hlq
    _ = _ := by rw [synthConst]; ring

/-- **The modulus is bounded by the local means**: for `0 < s < L`,
`‖f‖_p + ‖(2^(is) ω_L(f, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q}`, by the
reproducing formula and the synthesis estimate. -/
theorem modNorm_le_localMeansNorm (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) (s : ℝ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    ‖f‖ₑ + lqNorm q (fun i => dyadicWeight s i * lpModulus p L f i) ≤
      b.synthConst L s * b.localMeansNorm hp L s q f :=
  b.modNorm_le_of_tendsto hp L s hq (b.tendsto_sum_dual_localMean hp hL f)

/-! ### Local means and Besov spaces -/

/-- **Local means and differences**: for `1 ≤ p < ∞`, `0 < s < L` and `1 ≤ q ≤ ∞`,
`‖f‖_p + ‖(2^(ks) ω_L(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`. -/
theorem besov_iff_localMeans (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L f k) < ∞ ↔
      b.localMeansNorm hp L s q f < ∞ := by
  constructor
  · intro h
    exact (b.localMeansNorm_le hp L s hq f).trans_lt
      (ENNReal.mul_lt_top (b.upperConst_ne_top L s).lt_top h)
  · intro h
    exact (b.modNorm_le_localMeansNorm hp hL s hq f).trans_lt
      (ENNReal.mul_lt_top (b.synthConst_ne_top hs hsL).lt_top h)

/-- **Local means and band-limited approximation**: for `1 ≤ p < ∞`, `0 < s < L` and
`1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p, (E_k))` iff `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`. -/
theorem memApprox_bandScheme_iff_localMeans (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ}
    (hs : 0 < s) (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).MemApprox s q f ↔ b.localMeansNorm hp L s q f < ∞ := by
  rw [memApprox_bandScheme_iff_modulus hp hs.le hsL hq f, b.besov_iff_localMeans hp hL hs hsL hq f]

end LocalMeansBump

end Rd
