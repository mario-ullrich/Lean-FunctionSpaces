/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Cube.Splines
public import FunctionSpaces.Cube.PiecewiseJackson

/-!
# Jackson's inequality for tensor splines on the cube

For `1 ≤ p < ∞` and `r ≥ 1` there is `C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k))_p` for every
`f ∈ L_p(Q)`, `Q = [0, 1]^d`, and every level `k`, where `E` is the error of best approximation
by splines of order `r` in each variable (`Cube.exists_approxSeq_cubeSplineScheme_le`).

For `k ≥ r + 2` the approximant of a bounded continuous `f` is the tensor quasi-interpolant. In
coordinate `i`, every slice of `f - Q_k^{(i)} f` is the error of the quasi-interpolant in one
variable, and `Interval.exists_eLpNorm_sub_qi_le_of_taylor` bounds it by the smoothings of `f` in
coordinate `i` on `{x_i ≤ 3/4}` and `{x_i ≥ 1/4}` (`Cube.exists_left_cubeSmoothing`,
`Cube.exists_right_cubeSmoothing` with `L = 2^(-k)`); the windows of the quasi-interpolant have
length at most `1/4`. The transfer lemma `Cube.eLpNorm_le_of_slice_le` passes the bound to the
cube (`Cube.exists_eLpNorm_sub_slicewise_qiKernel_le`), and the errors telescope over the
coordinates (`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le_of_coord`). The coarse levels
`k ≤ r + 1` use Whitney's inequality on the cube at the scale `2^(-(r+1))`: the splines of level
`0` contain the polynomials of degree `< r` in each variable.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction

namespace Cube

open Interval

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Jackson's estimate for splines in one coordinate**: there is `B < ∞` with
`‖f - Q_k^{(i)} f‖_{L_p(Q)} ≤ B ω_r^{(i)}(f, 2^(-k))_p` for every continuous `f`, every
coordinate `i` and every `k ≥ r + 2`. -/
theorem exists_eLpNorm_sub_slicewise_qiKernel_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ {f : (Fin d → ℝ) → ℂ}, Continuous f → ∀ (i : Fin d) {k : ℕ},
      r + 2 ≤ k → eLpNorm (fun x => f x - (qiKernel hr k).slicewise i f x) p (cubeVol d) ≤
        B * coordModulus r p i f (1 / 2 ^ k) := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨A, hA, hAb⟩ := exists_eLpNorm_sub_qi_le_of_taylor (p := p) hr hp
  have hJ : 1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))⟩
  refine ⟨A * (2 * (1 + (r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)))),
    ENNReal.mul_ne_top hA (ENNReal.mul_ne_top (by simp) hJ), fun {f} hf i {k} hk => ?_⟩
  have hfm := hf.measurable
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  have hwL : (3 / 4 : ℝ) + 1 / 2 ^ k ≤ 1 := by
    have : (1 : ℝ) / 2 ^ k ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨G₁, D₁, hG₁, hD₁, h1L, h2L, hTL⟩ := exists_left_cubeSmoothing hf hr hp1 hp i hL hwL
  obtain ⟨G₂, D₂, hG₂, hD₂, h1R, h2R, hTR⟩ := exists_right_cubeSmoothing hf hr hp1 hp i hL hwL
  rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num] at h1R h2R
  have hslice : ∀ x, eLpNorm (slice (fun y => f y - (qiKernel hr k).slicewise i f y) x i) p
      unitVol ≤
      A * ((eLpNorm (slice (fun y => f y - G₁ y) x i) p (volume.restrict (Icc 0 (3 / 4))) +
            ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r *
              eLpNorm (slice D₁ x i) p (volume.restrict (Icc 0 (3 / 4)))) +
          (eLpNorm (slice (fun y => f y - G₂ y) x i) p (volume.restrict (Icc (1 / 4) 1)) +
            ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r *
              eLpNorm (slice D₂ x i) p (volume.restrict (Icc (1 / 4) 1)))) := fun x => by
    have hint : IntegrableOn (slice f x i) (Icc (0 : ℝ) 1) :=
      (continuous_slice hf x i).integrableOn_Icc
    rw [slice_sub_slicewise, qiKernel_apply hr k hint]
    exact hAb hk (measurable_slice hfm x i)
      (fun m _ => integrableOn_dyadicIco_of_continuous (continuous_slice hf x i) k m)
      (measurable_slice hG₁ x i) (measurable_slice hD₁ x i) (measurable_slice hG₂ x i)
      (measurable_slice hD₂ x i) (hTL x) (hTR x)
  refine (eLpNorm_le_of_slice_le (hfm.sub ((qiKernel hr k).measurable_slicewise hfm i))
    (hfm.sub hG₁) hD₁ (hfm.sub hG₂) hD₂ hp1 hp i le_rfl (by norm_num) (by norm_num) le_rfl hA
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hslice).trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [two_mul, add_mul]
  exact add_le_add (add_ofReal_div_pow_mul_le r k h1L h2L) (add_ofReal_div_pow_mul_le r k h1R h2R)

/-- **Jackson's inequality for tensor splines on the cube**: for `1 ≤ p < ∞` and `r ≥ 1` there is
`C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k))_p` for every `f ∈ L_p(Q)` and every `k ≥ 0`:
the tensor quasi-interpolant for `k ≥ r + 2`, Whitney's inequality for `k ≤ r + 1`. -/
theorem exists_approxSeq_cubeSplineScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p (cubeVol d)) (k : ℕ),
      (cubeSplineScheme p d r).approxSeq f (2 ^ k) ≤ CJ * lpCubeModulus p r f k := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨B, hB, hBb⟩ := exists_eLpNorm_sub_slicewise_qiKernel_le (d := d) (p := p) hr hp
  obtain ⟨Cq, hCq, hCqb⟩ := exists_eLpNorm_qiKernel_apply_le (p := p) hr hp
  obtain ⟨W, hW, hWb⟩ :=
    exists_approxSeq_cubePPScheme_one_le (d := d) (p := p) hr hp (m := r + 1) (by omega)
  have hF : (1 + Cq) ^ d * B ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hCq⟩)) hB
  refine ⟨W + (1 + Cq) ^ d * B, ENNReal.add_ne_top.2 ⟨hW, hF⟩, fun f k => ?_⟩
  rcases lt_or_ge k (r + 2) with hk | hk
  · -- the coarse levels: Whitney's inequality
    calc (cubeSplineScheme p d r).approxSeq f (2 ^ k)
        ≤ (cubeSplineScheme p d r).approxSeq f 1 :=
          ApproximationScheme.approxSeq_anti f Nat.one_le_two_pow
      _ ≤ (cubePPScheme p d r).approxSeq f 1 := approxSeq_cubeSplineScheme_one_le r f
      _ ≤ W * lpCubeModulus p r f (r + 1) := hWb f
      _ ≤ (W + (1 + Cq) ^ d * B) * lpCubeModulus p r f k :=
          mul_le_mul' le_self_add (lpCubeModulus_anti r f (by omega))
  · -- the fine levels: the tensor quasi-interpolant
    refine (approxSeq_le_of_continuous hp hF (fun g => ?_) f).trans
      (mul_le_mul' le_add_self le_rfl)
    have hgb : BddMeas (g : (Fin d → ℝ) → ℂ) :=
      ⟨g.continuous.measurable, ‖g‖, g.norm_coe_le_norm⟩
    have hS := isCubeSpline_cubeQI hr k hgb
    exact ⟨cubeQI hr k g, ⟨(hS.1.memLp p (cubeVol d)).toLp _,
      mem_cubeSplineScheme_two_pow.2 ⟨_, hS, MemLp.coeFn_toLp _⟩, MemLp.coeFn_toLp _⟩,
      (qiKernel hr k).eLpNorm_sub_foldSlicewise_le_of_coord hp1 hp hCq (hCqb k) hgb
        fun i => hBb g.continuous i hk⟩

end Cube
