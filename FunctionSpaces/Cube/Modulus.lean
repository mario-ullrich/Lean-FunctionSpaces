/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Cube.Basic

/-!
# Moduli of smoothness on the cube

The difference of order `r` and step `h` in coordinate `i`,
`Δ^r_{h e_i} f(x) = ∑_k (-1)^(r-k) C(r,k) f(x + k h e_i)` (`Cube.cubeDiff`), is the difference
`Δ_h^r` of the slice of `f` through `x` in coordinate `i`, evaluated at `x_i`. The **modulus of
smoothness in coordinate `i`** on the cube `Q = [0, 1]^d` is

`ω_r^{(i)}(f, t)_p = sup_{0 ≤ h ≤ t} ‖Δ^r_{h e_i} f‖_{L_p({x ∈ Q : x_i ≤ 1 - rh})}`

(`Cube.coordModulus`), and the **modulus on the cube** is their sum
`ω_r(f, t)_p = ∑_i ω_r^{(i)}(f, t)_p` (`Cube.cubeModulus`).

**Design.** These are the coordinatewise moduli of Nikol'skii's definition of Besov spaces. The
isotropic modulus `sup_{|h| ≤ t} ‖Δ_h^r f‖_p` is in `FunctionSpaces.Cube.IsoModulus`, and for
`0 < s < r - 1 + 1/p` both give the same Besov spaces on the cube
(`Cube.lqNorm_cubeModulus_lt_top_iff_iso`).
The supremum over `h` stays outside the integral over the other coordinates. Through the slices
(`Cube.eLpNorm_rpow_cubeDiff_eq_slice`), every bound of `Δ_h^r` in one variable for a fixed step
`h` carries over to the cube.

As in one variable, the modulus increases in `t`, is subadditive, is bounded by `2^r ‖f‖_p` in
every coordinate, and depends only on the class of `f` in `L_p(Q)`, `1 ≤ p < ∞`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Cube

open Interval

variable {d : ℕ}

/-- The **difference of order `r` and step `h` in coordinate `i`**,
`Δ^r_{h e_i} f(x) = Δ_h^r (slice f x i)(x_i)`. -/
noncomputable def cubeDiff (r : ℕ) (h : ℝ) (i : Fin d) (f : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℝ) : ℂ :=
  iterDiff r h (slice f x i) (x i)

/-- The coordinate difference as a sum: `Δ^r_{h e_i} f(x) = ∑_k (-1)^(r-k) C(r,k) f(x + k h e_i)`. -/
theorem cubeDiff_eq (r : ℕ) (h : ℝ) (i : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    cubeDiff r h i f x = ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (Function.update x i (x i + k * h)) := by
  rw [cubeDiff, iterDiff_apply]
  rfl

/-- Coordinate differences of measurable functions are measurable. -/
theorem measurable_cubeDiff {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (r : ℕ) (h : ℝ)
    (i : Fin d) : Measurable (cubeDiff r h i f) := by
  have : cubeDiff r h i f = fun x => ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (Function.update x i (x i + k * h)) :=
    funext (cubeDiff_eq r h i f)
  rw [this]
  refine Finset.measurable_sum _ fun k _ => measurable_const.mul (hf.comp ?_)
  exact measurable_update'.comp (measurable_id.prodMk ((measurable_pi_apply i).add_const _))

/-- The slice of a coordinate difference in its own coordinate is the difference of the slice. -/
theorem slice_cubeDiff (r : ℕ) (h : ℝ) (i : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    slice (cubeDiff r h i f) x i = iterDiff r h (slice f x i) := by
  funext t
  simp only [slice, cubeDiff]
  rw [slice_update, Function.update_self]

/-- Coordinate differences are additive. -/
theorem cubeDiff_add (r : ℕ) (h : ℝ) (i : Fin d) (f g : (Fin d → ℝ) → ℂ) :
    cubeDiff r h i (f + g) = cubeDiff r h i f + cubeDiff r h i g := by
  funext x
  simp only [cubeDiff, Pi.add_apply]
  rw [show slice (f + g) x i = slice f x i + slice g x i from rfl, iterDiff_add]
  rfl

/-- The region `{x ∈ Q : x_i ≤ 1 - r h}` of the differences of step `h` in coordinate `i`, as a
restriction of the cube measure. -/
noncomputable abbrev diffRegion (d : ℕ) (r : ℕ) (h : ℝ) (i : Fin d) : Measure (Fin d → ℝ) :=
  (cubeVol d).restrict {x | x i ∈ Icc 0 (1 - r * h)}

/-- **Coordinate differences through slices**: for measurable `f`, `h ≥ 0` and `0 < p < ∞`,
`‖Δ^r_{h e_i} f‖_{L_p({x_i ≤ 1 - rh})}^p = ∫_Q ‖Δ_h^r (slice f x i)‖_{L_p[0, 1-rh]}^p dx`. -/
theorem eLpNorm_rpow_cubeDiff_eq_slice {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (r : ℕ) {h : ℝ} (hh : 0 ≤ h) (i : Fin d) :
    eLpNorm (cubeDiff r h i f) p (diffRegion d r h i) ^ p.toReal =
      ∫⁻ x, eLpNorm (iterDiff r h (slice f x i)) p (volume.restrict (Icc 0 (1 - r * h))) ^
        p.toReal ∂cubeVol d := by
  rw [diffRegion, eLpNorm_rpow_region_eq_slice (measurable_cubeDiff hf r h i) hp0 hp i
    measurableSet_Icc]
  refine lintegral_congr fun x => ?_
  rw [slice_cubeDiff, unitVol_restrict_Icc_of_subset le_rfl
    (sub_le_self _ (mul_nonneg (Nat.cast_nonneg r) hh))]

/-- The **modulus of smoothness in coordinate `i`** on the cube:
`ω_r^{(i)}(f, t)_p = sup_{0 ≤ h ≤ t} ‖Δ^r_{h e_i} f‖_{L_p({x ∈ Q : x_i ≤ 1 - rh})}`. -/
noncomputable def coordModulus (r : ℕ) (p : ℝ≥0∞) (i : Fin d) (f : (Fin d → ℝ) → ℂ) (t : ℝ) :
    ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : h ∈ Icc 0 t), eLpNorm (cubeDiff r h i f) p (diffRegion d r h i)

/-- `‖Δ^r_{h e_i} f‖_{L_p({x_i ≤ 1 - rh})} ≤ ω_r^{(i)}(f, t)` for `0 ≤ h ≤ t`. -/
theorem eLpNorm_cubeDiff_le_coordModulus {r : ℕ} {p : ℝ≥0∞} {i : Fin d}
    {f : (Fin d → ℝ) → ℂ} {t h : ℝ} (hh : h ∈ Icc 0 t) :
    eLpNorm (cubeDiff r h i f) p (diffRegion d r h i) ≤ coordModulus r p i f t :=
  le_iSup₂ (f := fun (h : ℝ) (_ : h ∈ Icc 0 t) =>
    eLpNorm (cubeDiff r h i f) p (diffRegion d r h i)) h hh

/-- The coordinate modulus increases in `t`. -/
theorem coordModulus_mono (r : ℕ) (p : ℝ≥0∞) (i : Fin d) (f : (Fin d → ℝ) → ℂ) :
    Monotone (coordModulus r p i f) :=
  fun _ _ hst => iSup₂_le fun _ hh => eLpNorm_cubeDiff_le_coordModulus ⟨hh.1, hh.2.trans hst⟩

/-- The coordinate modulus is subadditive. -/
theorem coordModulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (i : Fin d)
    (f g : (Fin d → ℝ) → ℂ) (t : ℝ) :
    coordModulus r p i (f + g) t ≤ coordModulus r p i f t + coordModulus r p i g t := by
  refine iSup₂_le fun h hh => ?_
  rw [cubeDiff_add]
  exact (eLpNorm_add_le hp).trans
    (add_le_add (eLpNorm_cubeDiff_le_coordModulus hh) (eLpNorm_cubeDiff_le_coordModulus hh))

/-- **`‖Δ^r_{h e_i} f‖_{L_p({x_i ≤ 1 - rh})} ≤ 2^r ‖f‖_{L_p(Q)}`** for `h ≥ 0`, from the bound in
one variable on every slice. -/
theorem eLpNorm_cubeDiff_le {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (r : ℕ) {h : ℝ} (hh : 0 ≤ h) (i : Fin d) :
    eLpNorm (cubeDiff r h i f) p (diffRegion d r h i) ≤ 2 ^ r * eLpNorm f p (cubeVol d) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  refine (ENNReal.rpow_le_rpow_iff hq).1 ?_
  rw [eLpNorm_rpow_cubeDiff_eq_slice hf hp0 hp' r hh i, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    eLpNorm_rpow_cubeVol_eq_slice hf hp0 hp' i, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hq.le (by simp))]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  exact ENNReal.rpow_le_rpow (eLpNorm_iterDiff_le (measurable_slice hf x i) hp r hh 0 1) hq.le

/-- `ω_r^{(i)}(f, t)_p ≤ 2^r ‖f‖_{L_p(Q)}`. -/
theorem coordModulus_le {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (r : ℕ) (i : Fin d) (t : ℝ) :
    coordModulus r p i f t ≤ 2 ^ r * eLpNorm f p (cubeVol d) :=
  iSup₂_le fun _ hh => eLpNorm_cubeDiff_le hf hp hp' r hh.1 i

/-- **The coordinate modulus depends only on the class in `L_p(Q)`**: measurable functions that
agree almost everywhere on the cube have almost everywhere equal slices, hence equal
differences. -/
theorem coordModulus_congr_ae {f g : (Fin d → ℝ) → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[cubeVol d] g) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (r : ℕ) (i : Fin d)
    (t : ℝ) : coordModulus r p i f t = coordModulus r p i g t := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp only [coordModulus]
  congr 1
  funext h
  congr 1
  funext hh
  refine (ENNReal.rpow_left_injective hq.ne').eq_iff.1 ?_
  rw [eLpNorm_rpow_cubeDiff_eq_slice hf hp0 hp r hh.1 i,
    eLpNorm_rpow_cubeDiff_eq_slice hg hp0 hp r hh.1 i]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_slice_ae_eq hf hg hfg i] with x hx
  rw [eLpNorm_iterDiff_congr_ae (a := 0) (b := 1) hx r p hh.1]

/-- The **modulus of smoothness on the cube**, `ω_r(f, t)_p = ∑_i ω_r^{(i)}(f, t)_p`. -/
noncomputable def cubeModulus (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∑ i, coordModulus r p i f t

/-- The modulus on the cube increases in `t`. -/
theorem cubeModulus_mono (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) :
    Monotone (cubeModulus r p f) :=
  fun _ _ hst => Finset.sum_le_sum fun i _ => coordModulus_mono r p i f hst

/-- The modulus on the cube is subadditive. -/
theorem cubeModulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (f g : (Fin d → ℝ) → ℂ) (t : ℝ) :
    cubeModulus r p (f + g) t ≤ cubeModulus r p f t + cubeModulus r p g t := by
  rw [cubeModulus, cubeModulus, cubeModulus, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => coordModulus_add_le hp r i f g t

/-- `ω_r(f, t)_p ≤ d 2^r ‖f‖_{L_p(Q)}`. -/
theorem cubeModulus_le {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (r : ℕ) (t : ℝ) :
    cubeModulus r p f t ≤ d * 2 ^ r * eLpNorm f p (cubeVol d) := by
  calc cubeModulus r p f t ≤ ∑ _i : Fin d, 2 ^ r * eLpNorm f p (cubeVol d) :=
        Finset.sum_le_sum fun i _ => coordModulus_le hf hp hp' r i t
    _ = d * 2 ^ r * eLpNorm f p (cubeVol d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- The modulus on the cube depends only on the class in `L_p(Q)`. -/
theorem cubeModulus_congr_ae {f g : (Fin d → ℝ) → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[cubeVol d] g) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (r : ℕ) (t : ℝ) :
    cubeModulus r p f t = cubeModulus r p g t :=
  Finset.sum_congr rfl fun i _ => coordModulus_congr_ae hf hg hfg hp0 hp r i t

/-! ### The modulus on `L_p(Q)` at dyadic scales -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The modulus of an element of `L_p(Q)` at the dyadic scale `2^(-k)`,
`ω_r(f, 2^(-k))_p` on the cube. -/
noncomputable def lpCubeModulus (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) : ℝ≥0∞ :=
  cubeModulus r p (f : (Fin d → ℝ) → ℂ) (1 / 2 ^ k)

/-- The modulus on `L_p(Q)` is subadditive. -/
theorem lpCubeModulus_add_le (hp : p ≠ ∞) (r : ℕ) (f g : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpCubeModulus p r (f + g) k ≤ lpCubeModulus p r f k + lpCubeModulus p r g k := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  rw [lpCubeModulus, cubeModulus_congr_ae (Lp.stronglyMeasurable (f + g)).measurable
    ((Lp.stronglyMeasurable f).measurable.add (Lp.stronglyMeasurable g).measurable)
    (Lp.coeFn_add f g) hp0 hp]
  exact cubeModulus_add_le Fact.out r _ _ _

/-- `ω_r(f, t)_p ≤ d 2^r ‖f‖_p` in `L_p(Q)`. -/
theorem lpCubeModulus_le (hp : p ≠ ∞) (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpCubeModulus p r f k ≤ d * 2 ^ r * ‖f‖ₑ := by
  rw [Lp.enorm_def]
  exact cubeModulus_le (Lp.stronglyMeasurable f).measurable Fact.out hp r _

omit [Fact (1 ≤ p)] in
/-- The modulus at the dyadic scales decreases with the level. -/
theorem lpCubeModulus_anti (r : ℕ) (f : Lp ℂ p (cubeVol d)) : Antitone (lpCubeModulus p r f) :=
  fun _ _ hjk => cubeModulus_mono r p _ (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hjk))

end Cube
