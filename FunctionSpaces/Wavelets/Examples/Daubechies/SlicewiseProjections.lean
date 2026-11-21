/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Lp.CoordinateSlices
public import FunctionSpaces.Domains.Cube.Smoothing
public import FunctionSpaces.Wavelets.Examples.Daubechies.Jackson

/-!
# The Daubechies projections in one coordinate on `ℝ^d`

For a Daubechies mask of order `N ≥ 2`, a level `j` and a coordinate `i`, the **slicewise
projection** applies the projection `P_j` of one variable (`Daubechies.projFun`) to every slice
of `f : ℝ^d → ℂ` in coordinate `i`,

`P_j^{(i)} f(x) = P_j (f_{x,i})(x_i)` with the slice `f_{x,i}(t) = f(x with t in place i)`
(`Daubechies.sliceProj`, `Cube.slice`).

Its slices are the projections of the slices (`Daubechies.slice_sliceProj`), and it is additive on
differences of continuous functions (`Daubechies.sliceProj_sub`). The expansions of
one variable are jointly continuous in the coefficients and the point
(`Daubechies.continuous_expand_uncurry`), and for a continuous generator `g` the coefficients
`⟨f_{x,i}, g_{j,k}⟩` of the slices depend continuously (measurably) on the point for continuous
(measurable) `f` (`Daubechies.continuous_coeffFun_slice`, `Daubechies.measurable_coeffFun_slice`),
so `P_j^{(i)} f` is continuous (measurable) as well (`Daubechies.continuous_sliceProj`,
`Daubechies.measurable_sliceProj`).

* **The bound.** `‖P_j^{(i)} f‖_p ≤ C ‖f‖_p` for measurable `f` and `1 ≤ p < ∞`, with the bound
  `C = projConst m p` of one variable (`Daubechies.eLpNorm_sliceProj_le`): slice by slice
  (`Daubechies.eLpNorm_projFun_le`) and through the slices (`Rd.eLpNorm_le_of_slice_le`).
* **Jackson's inequality in one coordinate.** For continuous `f`,
  `‖f - P_j^{(i)} f‖_p ≤ C_J ω_N(f, 2^(-j))_p` with the isotropic modulus of smoothness of `ℝ^d`
  and the Jackson constant `C_J = jacksonConst m p` of one variable
  (`Daubechies.eLpNorm_sub_sliceProj_le`). The proof of one variable runs slice by slice with the
  Steklov smoothing in coordinate `i` (`Cube.cubeSmooth`): on each slice
  `‖g - P_j g‖ ≤ (1 + C) ‖g - S g‖ + C_S 2^(-jN) ‖(S g)^(N)‖`
  (`Daubechies.eLpNorm_slice_sub_sliceProj_le`), the slices pass the bound to `ℝ^d`
  (`Rd.eLpNorm_le_add_of_slice_le`), and on `ℝ^d` the smoothing satisfies
  `‖f - S^{(i)}_δ f‖_p ≤ ω_r(f, rδ)_p` and `‖∂_i^r S^{(i)}_δ f‖_p ≤ 2^r δ^(-r) ω_r(f, rδ)_p`
  (`Cube.eLpNorm_sub_cubeSmooth_le_modulus`, `Cube.eLpNorm_cubeSmoothDeriv_le_modulus`).

The norm on `ℝ^d` is the sup norm.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal ComplexConjugate

namespace Daubechies

/-! ### The coefficients of the slices -/

section Generic

variable {g : ℝ → ℂ} {a b : ℝ} {d : ℕ}

/-- **The coefficients of the slices of a continuous function are continuous**: let `g` be
continuous and vanish outside `[a, b]`, and let `f : ℝ^d → ℂ` be continuous. For a coordinate
`i`, a level `j` and a position `k`, the coefficient
`x ↦ ⟨f_{x,i}, g_{j,k}⟩ = ∫ f(x with t in place i) conj g_{j,k}(t) dt` is continuous. The
integrand vanishes outside the compact support window of `g_{j,k}` and is jointly continuous, so
Mathlib's `continuous_parametric_integral_of_continuous` applies. -/
theorem continuous_coeffFun_slice (hg : Continuous g) (hsupp : ∀ x ∉ Set.Icc a b, g x = 0)
    {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (i : Fin d) (j : ℕ) (k : ℤ) :
    Continuous fun x => coeffFun g j (Cube.slice f x i) k := by
  have hW : (fun x => coeffFun g j (Cube.slice f x i) k) = fun x =>
      ∫ t in supportWindow a b j k, f (Function.update x i t) * conj (scaledFun g j k t) := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [scaledFun_eq_zero hsupp ht, map_zero, mul_zero]
  rw [hW]
  exact continuous_parametric_integral_of_continuous
    ((hf.comp (continuous_fst.update i continuous_snd)).mul (Complex.continuous_conj.comp
      ((continuous_scaledFun hg j k).comp continuous_snd)))
    (isCompact_supportWindow a b j k)

/-- **The coefficients of the slices of a measurable function are measurable**: let `g` be
continuous and `f : ℝ^d → ℂ` measurable. For a coordinate `i`, a level `j` and a position `k`,
the coefficient `x ↦ ⟨f_{x,i}, g_{j,k}⟩` is measurable, as a partial integral of a jointly
measurable function (Mathlib's `MeasureTheory.StronglyMeasurable.integral_prod_right'`). -/
theorem measurable_coeffFun_slice (hg : Continuous g) {f : (Fin d → ℝ) → ℂ} (hf : Measurable f)
    (i : Fin d) (j : ℕ) (k : ℤ) :
    Measurable fun x => coeffFun g j (Cube.slice f x i) k :=
  (StronglyMeasurable.integral_prod_right' (ν := volume)
    (f := fun q : (Fin d → ℝ) × ℝ => Cube.slice f q.1 i q.2 * conj (scaledFun g j k q.2))
    ((Cube.measurable_slice_uncurry hf i).mul ((Complex.continuous_conj.comp
      (continuous_scaledFun hg j k)).measurable.comp measurable_snd)).stronglyMeasurable).measurable

end Generic

variable {N : ℕ} (m : Mask N) {d : ℕ}

/-! ### The slicewise projection -/

/-- **The projection of level `j` in coordinate `i`**: `P_j^{(i)} f(x) = P_j (f_{x,i})(x_i)`, the
projection of one variable (`Daubechies.projFun`) applied to the slice of `f` through `x` in
coordinate `i` (`Cube.slice`) and evaluated at `x_i`. -/
noncomputable def sliceProj (j : ℕ) (i : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  projFun m j (Cube.slice f x i) (x i)

/-- **The slices of the slicewise projection are the projections of the slices**:
`(P_j^{(i)} f)_{x,i} = P_j (f_{x,i})`, since the slice through `x` does not depend on `x_i`
(`Cube.slice_update`). -/
theorem slice_sliceProj (j : ℕ) (i : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    Cube.slice (sliceProj m j i f) x i = projFun m j (Cube.slice f x i) := by
  funext t
  simp only [Cube.slice, sliceProj]
  rw [Cube.slice_update, Function.update_self]

/-- **The projection in one coordinate is additive on differences of continuous functions**:
`P_j^{(i)} (f - g) = P_j^{(i)} f - P_j^{(i)} g` for continuous `f, g` and `N ≥ 2`, slice by slice
(`Daubechies.projFun_sub`). -/
theorem sliceProj_sub (hN : 2 ≤ N) {f g : (Fin d → ℝ) → ℂ} (hf : Continuous f)
    (hg : Continuous g) (j : ℕ) (i : Fin d) (x : Fin d → ℝ) :
    sliceProj m j i (fun y => f y - g y) x = sliceProj m j i f x - sliceProj m j i g x :=
  congrFun (projFun_sub m hN (Cube.continuous_slice hf x i).locallyIntegrable
    (Cube.continuous_slice hg x i).locallyIntegrable j) (x i)

/-- **The slicewise projection of a continuous function is continuous**, for `N ≥ 2`: it is the
expansion of one variable, jointly continuous in its coefficients and its point
(`Daubechies.continuous_expand_uncurry`), at the continuous coefficients of the slices
(`Daubechies.continuous_coeffFun_slice`) and the point `x_i`. -/
theorem continuous_sliceProj (hN : 2 ≤ N) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (j : ℕ)
    (i : Fin d) : Continuous (sliceProj m j i f) :=
  (continuous_expand_uncurry (continuous_scalingFun m hN)
    (fun _ hx => scalingFun_eq_zero m hN hx) j).comp
    ((continuous_pi fun k => continuous_coeffFun_slice (continuous_scalingFun m hN)
      (fun _ hx => scalingFun_eq_zero m hN hx) hf i j k).prodMk (continuous_apply i))

/-- **The slicewise projection of a measurable function is measurable**, for `N ≥ 2`: the
continuous expansion map (`Daubechies.continuous_expand_uncurry`) composed with the measurable
coefficients of the slices (`Daubechies.measurable_coeffFun_slice`) and the coordinate `x_i`. -/
theorem measurable_sliceProj (hN : 2 ≤ N) {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (j : ℕ)
    (i : Fin d) : Measurable (sliceProj m j i f) :=
  (continuous_expand_uncurry (continuous_scalingFun m hN)
    (fun _ hx => scalingFun_eq_zero m hN hx) j).measurable.comp
    ((measurable_pi_iff.2 fun k => measurable_coeffFun_slice (continuous_scalingFun m hN) hf i
      j k).prodMk (measurable_pi_apply i))

/-- **The slicewise projection is bounded on `L_p(ℝ^d)`**: for `N ≥ 2`, `1 ≤ p < ∞`, measurable
`f`, every level `j` and every coordinate `i`, `‖P_j^{(i)} f‖_p ≤ C ‖f‖_p` with the bound
`C = projConst m p` of the projections of one variable. Every slice satisfies the bound
(`Daubechies.slice_sliceProj`, `Daubechies.eLpNorm_projFun_le`), and the slices pass it to
`ℝ^d` (`Rd.eLpNorm_le_of_slice_le`). -/
theorem eLpNorm_sliceProj_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (j : ℕ) (i : Fin d) :
    eLpNorm (sliceProj m j i f) p volume ≤ ENNReal.ofReal (projConst m p) * eLpNorm f p volume :=
  Rd.eLpNorm_le_of_slice_le (zero_lt_one.trans_le hp1).ne' hp (measurable_sliceProj m hN hf j i)
    hf i fun x => by
      rw [show (fun t => sliceProj m j i f (Function.update x i t)) =
        projFun m j (Cube.slice f x i) from slice_sliceProj m j i f x]
      exact eLpNorm_projFun_le m hN hp1 hp (Cube.measurable_slice hf x i).aestronglyMeasurable j

/-! ### Jackson's inequality in one coordinate -/

/-- **Jackson's inequality on one slice**: for `N ≥ 2`, `1 ≤ p < ∞`, continuous `f`, every level
`j`, coordinate `i`, step `δ` and point `x`, the slices through `x` in coordinate `i` satisfy
`‖f_{x,i} - (P_j^{(i)} f)_{x,i}‖_p ≤ (1 + C) ‖f_{x,i} - (S^{(i)}_δ f)_{x,i}‖_p +
C_S 2^(-jN) ‖(∂_i^N S^{(i)}_δ f)_{x,i}‖_p` with `C = projConst m p` and
`C_S = smoothJacksonConst m p`. The slices are `g - P_j g`, `g - S_δ g` and `(S_δ g)^(N)` for the
slice `g = f_{x,i}` (`Daubechies.slice_sliceProj`, `Cube.slice_cubeSmooth`,
`Cube.slice_cubeSmoothDeriv`), and the bound is `Daubechies.eLpNorm_sub_projFun_le_add` with
Jackson's inequality for the smooth function `S_δ g`
(`Daubechies.eLpNorm_sub_projFun_le_of_contDiff`). -/
theorem eLpNorm_slice_sub_sliceProj_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (j : ℕ) (i : Fin d) (δ : ℝ) (x : Fin d → ℝ) :
    eLpNorm (fun t => Cube.slice f x i t - Cube.slice (sliceProj m j i f) x i t) p volume ≤
      (1 + ENNReal.ofReal (projConst m p)) *
          eLpNorm (fun t => Cube.slice f x i t - Cube.slice (Cube.cubeSmooth N δ i f) x i t) p
            volume +
        smoothJacksonConst m p * (2 ^ (j * N))⁻¹ *
          eLpNorm (Cube.slice (Cube.cubeSmoothDeriv N δ i f) x i) p volume := by
  have hg := Cube.continuous_slice hf x i
  have hS := Interval.contDiff_smooth hg N δ
  rw [slice_sliceProj, Cube.slice_cubeSmooth, Cube.slice_cubeSmoothDeriv]
  refine (eLpNorm_sub_projFun_le_add m hN hp1 hp hg.locallyIntegrable
    hS.continuous.locallyIntegrable j).trans ?_
  gcongr
  exact eLpNorm_sub_projFun_le_of_contDiff m hN hp1 hp hS j

/-- **Jackson's inequality in one coordinate**: for `N ≥ 2`, `1 ≤ p < ∞`, every continuous
`f : ℝ^d → ℂ`, every level `j` and every coordinate `i`,
`‖f - P_j^{(i)} f‖_p ≤ C_J ω_N(f, 2^(-j))_p` with the Jackson constant `C_J = jacksonConst m p`
of one variable and the isotropic modulus of smoothness of `ℝ^d` (sup norm). With the smoothing
`S^{(i)}_δ f` in coordinate `i` at the step `δ = 1/(N 2^j)`, the slices satisfy the bound of
`Daubechies.eLpNorm_slice_sub_sliceProj_le`, which passes to `ℝ^d`
(`Rd.eLpNorm_le_add_of_slice_le`); there `‖f - S^{(i)}_δ f‖_p ≤ ω_N(f, 2^(-j))_p` and
`‖∂_i^N S^{(i)}_δ f‖_p ≤ 2^N N^N 2^(jN) ω_N(f, 2^(-j))_p`
(`Cube.eLpNorm_sub_cubeSmooth_le_modulus`, `Cube.eLpNorm_cubeSmoothDeriv_le_modulus`,
`Daubechies.ofReal_one_div_mul_two_pow_inv_pow`), and the two bounds combine as in one variable
(`Daubechies.add_le_jacksonConst_mul`). The inequality holds in `[0, ∞]`. -/
theorem eLpNorm_sub_sliceProj_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (j : ℕ) (i : Fin d) :
    eLpNorm (fun x => f x - sliceProj m j i f x) p volume ≤
      jacksonConst m p * Rd.modulus volume N p f (1 / 2 ^ j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ : (0 : ℝ) < 1 / (N * 2 ^ j) := by positivity
  have hNδ : (N : ℝ) * (1 / (N * 2 ^ j)) = 1 / 2 ^ j := by field_simp
  have hB := Cube.eLpNorm_sub_cubeSmooth_le_modulus hf N hδ hp1 hp i
  have hD := Cube.eLpNorm_cubeSmoothDeriv_le_modulus hf N hδ hp1 i
  rw [hNδ] at hB hD
  rw [ofReal_one_div_mul_two_pow_inv_pow (by omega) j, ← mul_assoc] at hD
  refine (Rd.eLpNorm_le_add_of_slice_le hp1 hp
    (hf.sub (continuous_sliceProj m hN hf j i)).measurable
    (hf.sub (Cube.continuous_cubeSmooth hf N hδ.ne' i)).measurable
    (Cube.continuous_cubeSmoothDeriv hf N _ i).measurable i
    (eLpNorm_slice_sub_sliceProj_le m hN hp1 hp hf j i _)).trans ?_
  exact add_le_jacksonConst_mul m j hB hD

end Daubechies
