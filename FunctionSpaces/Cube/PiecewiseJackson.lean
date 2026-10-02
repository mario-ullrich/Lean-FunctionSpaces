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
Minkowski's inequality in the point turns the bounds of the slices into bounds on two regions of
the cube (`Cube.eLpNorm_le_of_slice_le`, used in `Cube.eLpNorm_sub_slicewise_ppKernel_le`).
General `f ∈ L_p(Q)` follow by density of the bounded continuous functions
(`Cube.approxSeq_le_of_continuous`).

At level `0` the approximants are the polynomials of degree `< r` in each variable, and
**Whitney's inequality on the cube** `E_1(f)_p ≤ W ω_r(f, 1)_p`
(`Cube.exists_approxSeq_cubePPScheme_one_le`) follows in the same way: on every slice, the Taylor
polynomials of the smoothings on `{x_i ≤ 3/4}` and `{x_i ≥ 1/4}` are glued as in one variable
(`Interval.exists_eLpNorm_sub_polyFun_le_glue`). So Jackson's inequality holds at every level
(`Cube.exists_approxSeq_cubePPScheme_le`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction

namespace Cube

open Interval

variable {d : ℕ}

/-! ### From slices to the cube -/

/-- **From slices to the cube, on two regions**: if every slice of `F` in coordinate `i` satisfies
`‖F_{x,i}‖_{L_p[0,1]} ≤ c ((‖(G₁)_{x,i}‖_{L_p[a₁,b₁]} + M ‖(D₁)_{x,i}‖_{L_p[a₁,b₁]}) + (‖(G₂)_{x,i}‖_{L_p[a₂,b₂]} + M ‖(D₂)_{x,i}‖_{L_p[a₂,b₂]}))`,
then the same bound holds for the norms on the cube and on the regions `{x_i ∈ [a_ν, b_ν]}`, by
Minkowski's inequality in the point (`Cube.lintegral_add_rpow_le`). -/
theorem eLpNorm_le_of_slice_le {F G₁ D₁ G₂ D₂ : (Fin d → ℝ) → ℂ} (hF : Measurable F)
    (hG₁ : Measurable G₁) (hD₁ : Measurable D₁) (hG₂ : Measurable G₂) (hD₂ : Measurable D₂)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁)
    (hb₁ : b₁ ≤ 1) (ha₂ : 0 ≤ a₂) (hb₂ : b₂ ≤ 1) {c M : ℝ≥0∞} (hc : c ≠ ∞) (hM : M ≠ ∞)
    (h : ∀ x, eLpNorm (slice F x i) p unitVol ≤
      c * ((eLpNorm (slice G₁ x i) p (volume.restrict (Icc a₁ b₁)) +
          M * eLpNorm (slice D₁ x i) p (volume.restrict (Icc a₁ b₁))) +
        (eLpNorm (slice G₂ x i) p (volume.restrict (Icc a₂ b₂)) +
          M * eLpNorm (slice D₂ x i) p (volume.restrict (Icc a₂ b₂))))) :
    eLpNorm F p (cubeVol d) ≤
      c * ((eLpNorm G₁ p (regionVol d i a₁ b₁) + M * eLpNorm D₁ p (regionVol d i a₁ b₁)) +
        (eLpNorm G₂ p (regionVol d i a₂ b₂) + M * eLpNorm D₂ p (regionVol d i a₂ b₂))) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hq1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp' hp; rwa [ENNReal.toReal_one] at this
  have hm₁ := measurable_eLpNorm_slice hG₁ hp0 hp' i (volume.restrict (Icc a₁ b₁))
  have hm₂ := (measurable_eLpNorm_slice hD₁ hp0 hp' i (volume.restrict (Icc a₁ b₁))).const_mul M
  have hm₃ := measurable_eLpNorm_slice hG₂ hp0 hp' i (volume.restrict (Icc a₂ b₂))
  have hm₄ := (measurable_eLpNorm_slice hD₂ hp0 hp' i (volume.restrict (Icc a₂ b₂))).const_mul M
  have hall := lintegral_add_rpow_le hq1 (hm₁.add hm₂).aemeasurable (hm₃.add hm₄).aemeasurable
    (lintegral_add_rpow_le hq1 hm₁.aemeasurable hm₂.aemeasurable
      (eLpNorm_rpow_regionVol_eq_slice hG₁ hp0 hp' i ha₁ hb₁).ge
      (lintegral_const_mul_rpow_le hq.le hM
        (eLpNorm_rpow_regionVol_eq_slice hD₁ hp0 hp' i ha₁ hb₁).ge))
    (lintegral_add_rpow_le hq1 hm₃.aemeasurable hm₄.aemeasurable
      (eLpNorm_rpow_regionVol_eq_slice hG₂ hp0 hp' i ha₂ hb₂).ge
      (lintegral_const_mul_rpow_le hq.le hM
        (eLpNorm_rpow_regionVol_eq_slice hD₂ hp0 hp' i ha₂ hb₂).ge))
  refine (ENNReal.rpow_le_rpow_iff hq).1 ?_
  rw [eLpNorm_rpow_cubeVol_eq_slice hF hp0 hp' i]
  exact (lintegral_mono fun x => ENNReal.rpow_le_rpow (h x) hq.le).trans
    (lintegral_const_mul_rpow_le hq.le hc hall)

/-- The slices of `f - P^{(i)} f` in coordinate `i` are the errors of `P` on the slices of `f`. -/
theorem slice_sub_slicewise {ι : Type*} [Fintype ι] (T : KernelOp ι) (f : (Fin d → ℝ) → ℂ)
    (i : Fin d) (x : Fin d → ℝ) :
    slice (fun y => f y - T.slicewise i f y) x i =
      fun t => slice f x i t - T.apply (slice f x i) t := by
  funext t
  rw [← KernelOp.slice_slicewise]
  rfl

/-- **From one coordinate to all**: if `‖f - P_k^{(i)} f‖_{L_p(Q)} ≤ B ω_r^{(i)}(f, t)_p` in every
coordinate, then `‖f - P_k^d f‖_{L_p(Q)} ≤ (1 + C_r)^d B ω_r(f, t)_p`, by telescoping
(`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le`). -/
theorem eLpNorm_sub_cubeProj_le_of_coord {f : (Fin d → ℝ) → ℂ} (hfb : BddMeas f) {r k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {B : ℝ≥0∞} {t : ℝ}
    (h : ∀ i, eLpNorm (fun x => f x - (ppKernel r k).slicewise i f x) p (cubeVol d) ≤
      B * coordModulus r p i f t) :
    eLpNorm (fun x => f x - cubeProj r k f x) p (cubeVol d) ≤
      (1 + ppProjConst r) ^ d * B * cubeModulus r p f t := by
  refine ((ppKernel r k).eLpNorm_sub_foldSlicewise_le hp hp' (ppProjConst_ne_top r)
    (fun u hu => eLpNorm_ppKernel_apply_le hp hp' r k hu) (List.finRange d) hfb).trans ?_
  rw [List.length_finRange, ← Fin.sum_univ_def]
  calc (1 + ppProjConst r) ^ d *
        ∑ i, eLpNorm (fun x => f x - (ppKernel r k).slicewise i f x) p (cubeVol d)
      ≤ (1 + ppProjConst r) ^ d * ∑ i, B * coordModulus r p i f t :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => h i)
    _ = (1 + ppProjConst r) ^ d * B * cubeModulus r p f t := by
        rw [cubeModulus, ← Finset.mul_sum, mul_assoc]

/-! ### Jackson's inequality from level `1` on -/

/-- **Jackson's estimate in one coordinate**: for continuous `f`, `r ≥ 1` and `k ≥ 0`,
`‖f - P_{k+1}^{(i)} f‖_{L_p(Q)} ≤ (1 + C_r) 2 (1 + 2^r r^(2r)) ω_r^{(i)}(f, 2^(-(k+1)))_p`. -/
theorem eLpNorm_sub_slicewise_ppKernel_le {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) {r : ℕ}
    (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) (k : ℕ) :
    eLpNorm (fun x => f x - (ppKernel r (k + 1)).slicewise i f x) p (cubeVol d) ≤
      (1 + ppProjConst r) * (2 * jacksonConst r) * coordModulus r p i f (1 / 2 ^ (k + 1)) := by
  have hL : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  have hfm := hf.measurable
  obtain ⟨G₁, D₁, hG₁, hD₁, h1L, h2L, hTL⟩ :=
    exists_left_cubeSmoothing hf hr hp hp' i hL (one_half_add_le_one k)
  obtain ⟨G₂, D₂, hG₂, hD₂, h1R, h2R, hTR⟩ :=
    exists_right_cubeSmoothing hf hr hp hp' i hL (one_half_add_le_one k)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h1R h2R
  set T := ppKernel r (k + 1)
  have hslice : ∀ x, eLpNorm (slice (fun y => f y - T.slicewise i f y) x i) p unitVol ≤
      (1 + ppProjConst r) *
        ((eLpNorm (slice (fun y => f y - G₁ y) x i) p (volume.restrict (Icc 0 (1 / 2))) +
            ENNReal.ofReal (1 / 2 ^ (k + 1)) ^ r *
              eLpNorm (slice D₁ x i) p (volume.restrict (Icc 0 (1 / 2)))) +
          (eLpNorm (slice (fun y => f y - G₂ y) x i) p (volume.restrict (Icc (1 / 2) 1)) +
            ENNReal.ofReal (1 / 2 ^ (k + 1)) ^ r *
              eLpNorm (slice D₂ x i) p (volume.restrict (Icc (1 / 2) 1)))) := fun x => by
    obtain ⟨Q, hQ, hb⟩ := exists_ppFun_approx_of_taylor (measurable_slice hfm x i)
      (measurable_slice hG₁ x i) (measurable_slice hD₁ x i) (measurable_slice hG₂ x i)
      (measurable_slice hD₂ x i) hp hp' (hTL x) (hTR x) k
    rw [slice_sub_slicewise]
    exact (eLpNorm_sub_ppKernel_apply_le hp hp' (measurable_slice hfm x i)
      (continuous_slice hf x i).integrableOn_Icc hQ).trans (mul_le_mul' le_rfl hb)
  refine (eLpNorm_le_of_slice_le (hfm.sub (T.measurable_slicewise hfm i)) (hfm.sub hG₁) hD₁
    (hfm.sub hG₂) hD₂ hp hp' i le_rfl (by norm_num) (by norm_num) le_rfl
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hslice).trans ?_
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
  refine (eLpNorm_sub_cubeProj_le_of_coord hfb hp hp'
    fun i => eLpNorm_sub_slicewise_ppKernel_le hf hr hp hp' i k).trans_eq ?_
  rw [cubeJacksonConst, pow_succ]
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

/-! ### Whitney's inequality: level `0` -/

/-- **Whitney's estimate in one coordinate**: there is `W < ∞` with
`‖f - P_0^{(i)} f‖_{L_p(Q)} ≤ W ω_r^{(i)}(f, 1/4)_p` for every continuous `f` and every
coordinate `i`, where `P_0` is the projection onto the polynomials of degree `< r` in one
variable. On every slice, the Taylor polynomials of the smoothings on `{x_i ≤ 3/4}` and on
`{x_i ≥ 1/4}` are glued as in Whitney's inequality on `[0, 1]`
(`Interval.exists_eLpNorm_sub_polyFun_le_glue`). -/
theorem exists_eLpNorm_sub_slicewise_ppKernel_zero_le {r : ℕ} (hr : 1 ≤ r) (hp' : p ≠ ∞) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ {f : (Fin d → ℝ) → ℂ}, Continuous f → ∀ i : Fin d,
      eLpNorm (fun x => f x - (ppKernel r 0).slicewise i f x) p (cubeVol d) ≤
        W * coordModulus r p i f (1 / 4) := by
  have hp : 1 ≤ p := Fact.out
  obtain ⟨K, hK, hKb⟩ := exists_eLpNorm_sub_polyFun_le_glue (p := p) r hp'
  obtain ⟨c, hc_eq⟩ : ∃ c : ℝ≥0∞,
      c = ENNReal.ofReal (1 / 4 : ℝ)⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) := ⟨_, rfl⟩
  have hc : c ≠ ∞ := hc_eq ▸ ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))
  have hCK : (1 + ppProjConst r) * (1 + K) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK⟩)
  refine ⟨(1 + ppProjConst r) * (1 + K) * (2 * (1 + c)), ENNReal.mul_ne_top hCK
    (ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hc⟩)),
    fun {f} hf i => ?_⟩
  have hfm := hf.measurable
  have hL : (0 : ℝ) < 1 / 4 := by norm_num
  have hwL : (3 / 4 : ℝ) + 1 / 4 ≤ 1 := by norm_num
  obtain ⟨G₁, D₁, hG₁, hD₁, h1L, h2L, hTL⟩ := exists_left_cubeSmoothing hf hr hp hp' i hL hwL
  obtain ⟨G₂, D₂, hG₂, hD₂, h1R, h2R, hTR⟩ := exists_right_cubeSmoothing hf hr hp hp' i hL hwL
  rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num] at h1R h2R
  rw [← hc_eq] at h2L h2R
  set T := ppKernel r 0
  have hslice : ∀ x, eLpNorm (slice (fun y => f y - T.slicewise i f y) x i) p unitVol ≤
      (1 + ppProjConst r) * (1 + K) *
        ((eLpNorm (slice (fun y => f y - G₁ y) x i) p (volume.restrict (Icc 0 (3 / 4))) +
            1 * eLpNorm (slice D₁ x i) p (volume.restrict (Icc 0 (3 / 4)))) +
          (eLpNorm (slice (fun y => f y - G₂ y) x i) p (volume.restrict (Icc (1 / 4) 1)) +
            1 * eLpNorm (slice D₂ x i) p (volume.restrict (Icc (1 / 4) 1)))) := fun x => by
    have hu := measurable_slice hfm x i
    obtain ⟨T₁, hT₁, hT₁b⟩ := hTL x 0 (3 / 4) (by norm_num)
    obtain ⟨T₂, hT₂, hT₂b⟩ := hTR x (1 / 4) 1 (by norm_num)
    have hE₁ : eLpNorm (fun t => slice f x i t - polyFun T₁ t) p
        (volume.restrict (Icc 0 (2 / 3))) ≤
        eLpNorm (slice (fun y => f y - G₁ y) x i) p (volume.restrict (Icc 0 (3 / 4))) +
          1 * eLpNorm (slice D₁ x i) p (volume.restrict (Icc 0 (3 / 4))) := by
      rw [one_mul]
      exact (eLpNorm_Icc_mono _ p le_rfl (by norm_num)).trans
        (eLpNorm_sub_polyFun_le_add (by norm_num) hT₁b)
    have hE₂ : eLpNorm (fun t => slice f x i t - polyFun T₂ t) p
        (volume.restrict (Icc (1 / 3) 1)) ≤
        eLpNorm (slice (fun y => f y - G₂ y) x i) p (volume.restrict (Icc (1 / 4) 1)) +
          1 * eLpNorm (slice D₂ x i) p (volume.restrict (Icc (1 / 4) 1)) := by
      rw [one_mul]
      exact (eLpNorm_Icc_mono _ p (by norm_num) le_rfl).trans
        (eLpNorm_sub_polyFun_le_add (by norm_num) hT₂b)
    have hae : (fun t => slice f x i t - ppFun 0 (fun _ => T₁) t) =ᵐ[unitVol]
        fun t => slice f x i t - polyFun T₁ t := by
      filter_upwards [ae_mem_Ico_unitVol] with t ht
      obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := 0) ht
      rw [ppFun_eq_of_mem _ hlt hmem]
    rw [slice_sub_slicewise]
    calc eLpNorm (fun t => slice f x i t - T.apply (slice f x i) t) p unitVol
        ≤ (1 + ppProjConst r) *
            eLpNorm (fun t => slice f x i t - ppFun 0 (fun _ => T₁) t) p unitVol :=
          eLpNorm_sub_ppKernel_apply_le hp hp' hu (continuous_slice hf x i).integrableOn_Icc
            fun _ => hT₁
      _ = (1 + ppProjConst r) *
            eLpNorm (fun t => slice f x i t - polyFun T₁ t) p (volume.restrict (Icc 0 1)) := by
          rw [eLpNorm_congr_ae hae]
      _ ≤ (1 + ppProjConst r) * ((1 + K) *
            (eLpNorm (fun t => slice f x i t - polyFun T₁ t) p (volume.restrict (Icc 0 (2 / 3))) +
              eLpNorm (fun t => slice f x i t - polyFun T₂ t) p
                (volume.restrict (Icc (1 / 3) 1)))) :=
          mul_le_mul' le_rfl (hKb hu hT₁ hT₂)
      _ ≤ (1 + ppProjConst r) * ((1 + K) *
            ((eLpNorm (slice (fun y => f y - G₁ y) x i) p (volume.restrict (Icc 0 (3 / 4))) +
                1 * eLpNorm (slice D₁ x i) p (volume.restrict (Icc 0 (3 / 4)))) +
              (eLpNorm (slice (fun y => f y - G₂ y) x i) p (volume.restrict (Icc (1 / 4) 1)) +
                1 * eLpNorm (slice D₂ x i) p (volume.restrict (Icc (1 / 4) 1))))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add hE₁ hE₂))
      _ = _ := by ring
  refine (eLpNorm_le_of_slice_le (hfm.sub (T.measurable_slicewise hfm i)) (hfm.sub hG₁) hD₁
    (hfm.sub hG₂) hD₂ hp hp' i le_rfl (by norm_num) (by norm_num) le_rfl hCK
    ENNReal.one_ne_top hslice).trans ?_
  refine (mul_le_mul' le_rfl ?_).trans_eq (mul_assoc _ _ _).symm
  calc (eLpNorm (fun y => f y - G₁ y) p (regionVol d i 0 (3 / 4)) +
        1 * eLpNorm D₁ p (regionVol d i 0 (3 / 4))) +
      (eLpNorm (fun y => f y - G₂ y) p (regionVol d i (1 / 4) 1) +
        1 * eLpNorm D₂ p (regionVol d i (1 / 4) 1))
      ≤ (coordModulus r p i f (1 / 4) + 1 * (c * coordModulus r p i f (1 / 4))) +
          (coordModulus r p i f (1 / 4) + 1 * (c * coordModulus r p i f (1 / 4))) :=
        add_le_add (add_le_add h1L (mul_le_mul' le_rfl h2L))
          (add_le_add h1R (mul_le_mul' le_rfl h2R))
    _ = 2 * (1 + c) * coordModulus r p i f (1 / 4) := by ring

/-- **Whitney's inequality on the cube**: there is `W < ∞` with `E_1(f)_p ≤ W ω_r(f, 1)_p` for
every `f ∈ L_p(Q)`; the approximants of complexity `1` are the polynomials of degree `< r` in
each variable. -/
theorem exists_approxSeq_cubePPScheme_one_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ f : Lp ℂ p (cubeVol d),
      (cubePPScheme p d r).approxSeq f 1 ≤ W * lpCubeModulus p r f 0 := by
  obtain ⟨W, hW, hWb⟩ := exists_eLpNorm_sub_slicewise_ppKernel_zero_le (d := d) (p := p) hr hp
  have hW' : (1 + ppProjConst r) ^ d * W ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩)) hW
  refine ⟨(1 + ppProjConst r) ^ d * W, hW',
    fun f => approxSeq_le_of_continuous hp hW' (fun g => ?_) f⟩
  have hgb : BddMeas (g : (Fin d → ℝ) → ℂ) := ⟨g.continuous.measurable, ‖g‖, g.norm_coe_le_norm⟩
  have hP := isCubePP_cubeProj r 0 hgb
  refine ⟨cubeProj r 0 g, ⟨(hP.1.memLp p (cubeVol d)).toLp _, ?_, MemLp.coeFn_toLp _⟩, ?_⟩
  · show _ ∈ cubePPScheme p d r (2 ^ 0)
    exact mem_cubePPScheme_two_pow.2 ⟨_, hP, MemLp.coeFn_toLp _⟩
  · exact (eLpNorm_sub_cubeProj_le_of_coord hgb Fact.out hp fun i => hWb g.continuous i).trans
      (mul_le_mul' le_rfl (cubeModulus_mono r p _ (by norm_num)))

/-- **Jackson's inequality for piecewise polynomials on the cube at every level**: for
`1 ≤ p < ∞` and `r ≥ 1` there is `C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k))_p` for every
`f ∈ L_p(Q)` and every `k ≥ 0`; level `0` is Whitney's inequality. -/
theorem exists_approxSeq_cubePPScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p (cubeVol d)) (k : ℕ),
      (cubePPScheme p d r).approxSeq f (2 ^ k) ≤ CJ * lpCubeModulus p r f k := by
  obtain ⟨W, hW, hWb⟩ := exists_approxSeq_cubePPScheme_one_le (d := d) (p := p) hr hp
  refine ⟨W + cubeJacksonConst d r,
    ENNReal.add_ne_top.2 ⟨hW, cubeJacksonConst_ne_top d r⟩, fun f k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    exact (hWb f).trans (mul_le_mul' le_self_add le_rfl)
  · exact (approxSeq_cubePPScheme_le hr hp f hk).trans (mul_le_mul' le_add_self le_rfl)

end Cube
