/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Cube.PiecewisePoly
public import FunctionSpaces.Cube.Smoothing
public import FunctionSpaces.Interval.PiecewiseJackson

/-!
# Jackson's inequality for piecewise polynomials on the cube

For `1 ≤ p < ∞`, `r ≥ 1` and `k ≥ 1`, the error of best approximation in `L_p(Q)`,
`Q = [0, 1]^d`, by piecewise polynomials of level `k` and degree `< r` in each variable is bounded
by the modulus on the cube,
`E_{2^k}(f)_p ≤ (1 + C_r)^(d+1) 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k))_p`
(`Cube.approxSeq_cubePPScheme_le`), with the bound `C_r` of the local projections.

The approximant of a bounded continuous `f` is the tensor projection
`P_k^d f = P_k^{(0)} ⋯ P_k^{(d-1)} f`. Its error telescopes into the errors of the projections in
single coordinates (`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le`). In coordinate `i`, every slice
of `f - P_k^{(i)} f` is the error of the local projection in one variable, and Lebesgue's
inequality (`Cube.eLpNorm_sub_ppKernel_apply_le`) bounds it by the error of any piecewise
polynomial. That piecewise polynomial is built slice by slice from Taylor polynomials of the
smoothings in coordinate `i` on the halves `{x_i ≤ 1/2}` and `{x_i ≥ 1/2}`
(`Cube.exists_left_cubeSmoothing`, `Cube.exists_right_cubeSmoothing`,
`Interval.exists_ppFun_approx_of_taylor`), so it need not depend measurably on the slice.
Minkowski's inequality in the point (`Cube.lintegral_add_rpow_le`) turns the bounds of the slices
into bounds on the two halves of the cube (`Cube.eLpNorm_sub_slicewise_ppKernel_le`). General
`f ∈ L_p(Q)` follow by density of the bounded continuous functions
(`Cube.approxSeq_le_of_continuous`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction

namespace Cube

open Interval

variable {d : ℕ}

/-- **Jackson's estimate in one coordinate**: for continuous `f`, `r ≥ 1` and `k ≥ 0`,
`‖f - P_{k+1}^{(i)} f‖_{L_p(Q)} ≤ (1 + C_r) 2 (1 + 2^r r^(2r)) ω_r^{(i)}(f, 2^(-(k+1)))_p`. -/
theorem eLpNorm_sub_slicewise_ppKernel_le {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) {r : ℕ}
    (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) (k : ℕ) :
    eLpNorm (fun x => f x - (ppKernel r (k + 1)).slicewise i f x) p (cubeVol d) ≤
      (1 + ppProjConst r) * (2 * jacksonConst r) * coordModulus r p i f (1 / 2 ^ (k + 1)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hq1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp' hp; rwa [ENNReal.toReal_one] at this
  have hL : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  have hfm := hf.measurable
  obtain ⟨G₁, D₁, hG₁, hD₁, h1L, h2L, hTL⟩ :=
    exists_left_cubeSmoothing hf hr hp hp' i hL (one_half_add_le_one k)
  obtain ⟨G₂, D₂, hG₂, hD₂, h1R, h2R, hTR⟩ :=
    exists_right_cubeSmoothing hf hr hp hp' i hL (one_half_add_le_one k)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h1R h2R
  set T := ppKernel r (k + 1)
  set M := ENNReal.ofReal (1 / 2 ^ (k + 1)) ^ r
  set νL : Measure ℝ := volume.restrict (Icc 0 (1 / 2))
  set νR : Measure ℝ := volume.restrict (Icc (1 / 2) 1)
  -- the bounds of the slices, as functions of the point
  set φ₁ : (Fin d → ℝ) → ℝ≥0∞ := fun x => eLpNorm (slice (fun y => f y - G₁ y) x i) p νL
  set φ₂ : (Fin d → ℝ) → ℝ≥0∞ := fun x => M * eLpNorm (slice D₁ x i) p νL
  set φ₃ : (Fin d → ℝ) → ℝ≥0∞ := fun x => eLpNorm (slice (fun y => f y - G₂ y) x i) p νR
  set φ₄ : (Fin d → ℝ) → ℝ≥0∞ := fun x => M * eLpNorm (slice D₂ x i) p νR
  have hslice : ∀ x, eLpNorm (slice (fun y => f y - T.slicewise i f y) x i) p unitVol ≤
      (1 + ppProjConst r) * ((φ₁ x + φ₂ x) + (φ₃ x + φ₄ x)) := fun x => by
    obtain ⟨Q, hQ, hb⟩ := exists_ppFun_approx_of_taylor (measurable_slice hfm x i)
      (measurable_slice hG₁ x i) (measurable_slice hD₁ x i) (measurable_slice hG₂ x i)
      (measurable_slice hD₂ x i) hp hp' (hTL x) (hTR x) k
    have hs : slice (fun y => f y - T.slicewise i f y) x i =
        fun t => slice f x i t - T.apply (slice f x i) t := by
      funext t
      rw [← KernelOp.slice_slicewise]
      rfl
    rw [hs]
    exact (eLpNorm_sub_ppKernel_apply_le hp hp' (measurable_slice hfm x i)
      (continuous_slice hf x i).integrableOn_Icc hQ).trans (mul_le_mul' le_rfl hb)
  -- Minkowski's inequality in the point
  have hM : M ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hm₁ : Measurable φ₁ := measurable_eLpNorm_slice (hfm.sub hG₁) hp0 hp' i νL
  have hm₂ : Measurable φ₂ := (measurable_eLpNorm_slice hD₁ hp0 hp' i νL).const_mul M
  have hm₃ : Measurable φ₃ := measurable_eLpNorm_slice (hfm.sub hG₂) hp0 hp' i νR
  have hm₄ : Measurable φ₄ := (measurable_eLpNorm_slice hD₂ hp0 hp' i νR).const_mul M
  have hi₁ : ∫⁻ x, φ₁ x ^ p.toReal ∂cubeVol d ≤
      eLpNorm (fun y => f y - G₁ y) p (regionVol d i 0 (1 / 2)) ^ p.toReal :=
    (eLpNorm_rpow_regionVol_eq_slice (hfm.sub hG₁) hp0 hp' i le_rfl (by norm_num)).ge
  have hi₂ : ∫⁻ x, φ₂ x ^ p.toReal ∂cubeVol d ≤
      (M * eLpNorm D₁ p (regionVol d i 0 (1 / 2))) ^ p.toReal :=
    lintegral_const_mul_rpow_le hq.le hM
      (eLpNorm_rpow_regionVol_eq_slice hD₁ hp0 hp' i le_rfl (by norm_num)).ge
  have hi₃ : ∫⁻ x, φ₃ x ^ p.toReal ∂cubeVol d ≤
      eLpNorm (fun y => f y - G₂ y) p (regionVol d i (1 / 2) 1) ^ p.toReal :=
    (eLpNorm_rpow_regionVol_eq_slice (hfm.sub hG₂) hp0 hp' i (by norm_num) le_rfl).ge
  have hi₄ : ∫⁻ x, φ₄ x ^ p.toReal ∂cubeVol d ≤
      (M * eLpNorm D₂ p (regionVol d i (1 / 2) 1)) ^ p.toReal :=
    lintegral_const_mul_rpow_le hq.le hM
      (eLpNorm_rpow_regionVol_eq_slice hD₂ hp0 hp' i (by norm_num) le_rfl).ge
  have hall := lintegral_add_rpow_le hq1 (hm₁.add hm₂).aemeasurable (hm₃.add hm₄).aemeasurable
    (lintegral_add_rpow_le hq1 hm₁.aemeasurable hm₂.aemeasurable hi₁ hi₂)
    (lintegral_add_rpow_le hq1 hm₃.aemeasurable hm₄.aemeasurable hi₃ hi₄)
  have hFm : Measurable fun x => f x - T.slicewise i f x := hfm.sub (T.measurable_slicewise hfm i)
  have hmain : eLpNorm (fun x => f x - T.slicewise i f x) p (cubeVol d) ≤
      (1 + ppProjConst r) *
        ((eLpNorm (fun y => f y - G₁ y) p (regionVol d i 0 (1 / 2)) +
            M * eLpNorm D₁ p (regionVol d i 0 (1 / 2))) +
          (eLpNorm (fun y => f y - G₂ y) p (regionVol d i (1 / 2) 1) +
            M * eLpNorm D₂ p (regionVol d i (1 / 2) 1))) := by
    refine (ENNReal.rpow_le_rpow_iff hq).1 ?_
    rw [eLpNorm_rpow_cubeVol_eq_slice hFm hp0 hp' i]
    calc ∫⁻ x, eLpNorm (slice (fun y => f y - T.slicewise i f y) x i) p unitVol ^ p.toReal
          ∂cubeVol d
        ≤ ∫⁻ x, ((1 + ppProjConst r) * ((φ₁ x + φ₂ x) + (φ₃ x + φ₄ x))) ^ p.toReal ∂cubeVol d :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hslice x) hq.le
      _ ≤ _ := lintegral_const_mul_rpow_le hq.le
          (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩) hall
  refine hmain.trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [two_mul, add_mul]
  exact add_le_add (add_ofReal_pow_mul_le_jacksonConst hL r h1L h2L)
    (add_ofReal_pow_mul_le_jacksonConst hL r h1R h2R)

/-- The constant of Jackson's inequality on the cube, `(1 + C_r)^(d+1) 2 (1 + 2^r r^(2r))`, with
the bound `C_r` of the local projections. -/
noncomputable def cubeJacksonConst (d r : ℕ) : ℝ≥0∞ :=
  (1 + ppProjConst r) ^ (d + 1) * (2 * jacksonConst r)

/-- The Jackson constant on the cube is finite. -/
theorem cubeJacksonConst_ne_top (d r : ℕ) : cubeJacksonConst d r ≠ ∞ :=
  ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩))
    (ENNReal.mul_ne_top (by norm_num) (jacksonConst_ne_top r))

/-- **Jackson's estimate for continuous functions on the cube**: for bounded continuous `f`,
`r ≥ 1` and `k ≥ 0`, the tensor projection satisfies
`‖f - P_{k+1}^d f‖_{L_p(Q)} ≤ (1 + C_r)^(d+1) 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-(k+1)))_p`. -/
theorem eLpNorm_sub_cubeProj_le {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (hfb : BddMeas f)
    {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (k : ℕ) :
    eLpNorm (fun x => f x - cubeProj r (k + 1) f x) p (cubeVol d) ≤
      cubeJacksonConst d r * cubeModulus r p f (1 / 2 ^ (k + 1)) := by
  refine ((ppKernel r (k + 1)).eLpNorm_sub_foldSlicewise_le hp hp' (ppProjConst_ne_top r)
    (fun u hu => eLpNorm_ppKernel_apply_le hp hp' r (k + 1) hu) (List.finRange d) hfb).trans ?_
  rw [List.length_finRange, ← Fin.sum_univ_def]
  calc (1 + ppProjConst r) ^ d *
        ∑ i, eLpNorm (fun x => f x - (ppKernel r (k + 1)).slicewise i f x) p (cubeVol d)
      ≤ (1 + ppProjConst r) ^ d * ∑ i, (1 + ppProjConst r) * (2 * jacksonConst r) *
          coordModulus r p i f (1 / 2 ^ (k + 1)) := by
        gcongr with i
        exact eLpNorm_sub_slicewise_ppKernel_le hf hr hp hp' i k
    _ = cubeJacksonConst d r * cubeModulus r p f (1 / 2 ^ (k + 1)) := by
        rw [← Finset.mul_sum, cubeJacksonConst, cubeModulus, pow_succ]
        ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **From continuous functions to `L_p(Q)` by density**: a bound
`E_n(g) ≤ C ω_r(g, 2^(-k))_p` for every bounded continuous `g`, given by an approximant
`u ∈ A_n` of `g`, holds for every `f ∈ L_p(Q)`, `p < ∞`, as in one variable
(`Interval.approxSeq_le_of_continuous`). -/
theorem approxSeq_le_of_continuous {A : ApproximationScheme (Lp ℂ p (cubeVol d))} (hp : p ≠ ∞)
    {r n k : ℕ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ g : (Fin d → ℝ) →ᵇ ℂ, ∃ u : (Fin d → ℝ) → ℂ,
      (∃ a ∈ A n, (a : (Fin d → ℝ) → ℂ) =ᵐ[cubeVol d] u) ∧
        eLpNorm (fun x => g x - u x) p (cubeVol d) ≤ C * cubeModulus r p g (1 / 2 ^ k))
    (f : Lp ℂ p (cubeVol d)) : A.approxSeq f n ≤ C * lpCubeModulus p r f k := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  refine ApproximationScheme.approxSeq_le_of_dense
    (BoundedContinuousFunction.toLp_denseRange ℂ (cubeVol d) ℝ hp)
    (fun f g => lpCubeModulus_add_le hp r f g k) (C0 := d * 2 ^ r)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (fun f => lpCubeModulus_le hp r f k) hC ?_ f
  rintro _ ⟨g, rfl⟩
  obtain ⟨u, ⟨a, ha, hau⟩, hbound⟩ := h g
  have hg := BoundedContinuousFunction.coeFn_toLp (E := ℂ) p (cubeVol d) ℝ g
  refine (A.approxSeq_le_of_mem ha _).trans ?_
  rw [Lp.enorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hg.sub hau)), lpCubeModulus,
    cubeModulus_congr_ae (Lp.stronglyMeasurable _).measurable g.continuous.measurable hg hp0 hp]
  exact hbound

/-- **Jackson's inequality for piecewise polynomials on the cube**: for `1 ≤ p < ∞`, `r ≥ 1` and
`k ≥ 1`, `E_{2^k}(f)_p ≤ (1 + C_r)^(d+1) 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k))_p` for every
`f ∈ L_p(Q)`; first for bounded continuous functions with the tensor projection
(`Cube.eLpNorm_sub_cubeProj_le`), then by density. -/
theorem approxSeq_cubePPScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) (f : Lp ℂ p (cubeVol d))
    {k : ℕ} (hk : 1 ≤ k) :
    (cubePPScheme p d r).approxSeq f (2 ^ k) ≤ cubeJacksonConst d r * lpCubeModulus p r f k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  refine approxSeq_le_of_continuous hp (cubeJacksonConst_ne_top d r) (fun g => ?_) f
  have hgb : BddMeas (g : (Fin d → ℝ) → ℂ) := ⟨g.continuous.measurable, ‖g‖, g.norm_coe_le_norm⟩
  have hP := isCubePP_cubeProj r (k + 1) hgb
  exact ⟨cubeProj r (k + 1) g, ⟨(hP.1.memLp p (cubeVol d)).toLp _,
    mem_cubePPScheme_two_pow.2 ⟨_, hP, MemLp.coeFn_toLp _⟩, MemLp.coeFn_toLp _⟩,
    eLpNorm_sub_cubeProj_le g.continuous hgb hr Fact.out hp k⟩

end Cube
