/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.Differences
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The modulus of smoothness on an interval

For `f : ℝ → ℂ`, `1 ≤ p ≤ ∞` and an interval `[a, b]`, the **modulus of smoothness of order `r`**
is

`ω_r(f, t, [a, b])_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r f‖_{L_p[a, b - r h]}`   (`Interval.modulus`):

the differences are taken only where all points `x, x + h, …, x + r h` lie in `[a, b]`.  It
increases in `t`, is subadditive and homogeneous in `f`, satisfies
`ω_r(f, t) ≤ 2^r ‖f‖_{L_p[a,b]}`, vanishes on polynomials of degree `< r`, depends only on the
class of `f` in `L_p[a, b]` (`Interval.modulus_congr_ae`) and is invariant under the reflection
`x ↦ a + b - x` (`Interval.modulus_reflect`).

All norms are `eLpNorm` on the restriction of Lebesgue measure; the functions are measurable
functions on `ℝ`, as the representatives of elements of `L_p` are.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Interval

/-- Translation: `‖f(· + c)‖_{L_p[u,v]} = ‖f‖_{L_p[u+c, v+c]}`. -/
theorem eLpNorm_comp_add_Icc {f : ℝ → ℂ} (hf : Measurable f) (p : ℝ≥0∞) (c u v : ℝ) :
    eLpNorm (fun x => f (x + c)) p (volume.restrict (Icc u v)) =
      eLpNorm f p (volume.restrict (Icc (u + c) (v + c))) := by
  have hpre : (fun x => x + c) ⁻¹' Icc (u + c) (v + c) = Icc u v := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmp : MeasurePreserving (· + c) (volume.restrict (Icc u v))
      (volume.restrict (Icc (u + c) (v + c))) := by
    have := (measurePreserving_add_right volume c).restrict_preimage
      (measurableSet_Icc (a := u + c) (b := v + c))
    rwa [hpre] at this
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp

/-- Reflection: `‖f(c - ·)‖_{L_p[u,v]} = ‖f‖_{L_p[c-v, c-u]}`. -/
theorem eLpNorm_comp_sub_Icc {f : ℝ → ℂ} (hf : Measurable f) (p : ℝ≥0∞) (c u v : ℝ) :
    eLpNorm (fun x => f (c - x)) p (volume.restrict (Icc u v)) =
      eLpNorm f p (volume.restrict (Icc (c - v) (c - u))) := by
  have hpre : (fun x => c - x) ⁻¹' Icc (c - v) (c - u) = Icc u v := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmp : MeasurePreserving (fun x => c - x) (volume.restrict (Icc u v))
      (volume.restrict (Icc (c - v) (c - u))) := by
    have := (volume.measurePreserving_sub_left c).restrict_preimage
      (measurableSet_Icc (a := c - v) (b := c - u))
    rwa [hpre] at this
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp

/-- `L_p` norms increase with the interval. -/
theorem eLpNorm_Icc_mono (f : ℝ → ℂ) (p : ℝ≥0∞) {u v u' v' : ℝ} (hu : u' ≤ u) (hv : v ≤ v') :
    eLpNorm f p (volume.restrict (Icc u v)) ≤ eLpNorm f p (volume.restrict (Icc u' v')) :=
  eLpNorm_mono_measure _ (Measure.restrict_mono (Icc_subset_Icc hu hv) le_rfl)

/-- Differences of a measurable function are measurable. -/
theorem measurable_iterDiff {f : ℝ → ℂ} (hf : Measurable f) (r : ℕ) (h : ℝ) :
    Measurable (iterDiff r h f) := by
  have : iterDiff r h f = fun x => ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (x + k * h) := funext (iterDiff_apply r h f)
  rw [this]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (hf.comp (measurable_add_const _))

/-- **Differences in `L_p`**: if `‖f(· + k h)‖_{L_p(μ)} ≤ B` for `k ≤ r`, then
`‖Δ_h^r f‖_{L_p(μ)} ≤ 2^r B`, by the triangle inequality and `∑_k C(r, k) = 2^r`. -/
theorem eLpNorm_iterDiff_le_of_forall {f : ℝ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure ℝ}
    {r : ℕ} {h : ℝ} {B : ℝ≥0∞}
    (hB : ∀ k ∈ Finset.range (r + 1), eLpNorm (fun x => f (x + k * h)) p μ ≤ B) :
    eLpNorm (iterDiff r h f) p μ ≤ 2 ^ r * B := by
  have hsum : iterDiff r h f = ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) • fun x => f (x + k * h) := by
    funext x
    rw [iterDiff_apply, Finset.sum_apply]
    rfl
  rw [hsum]
  refine (eLpNorm_sum_le hp).trans ?_
  calc ∑ k ∈ Finset.range (r + 1),
        eLpNorm (((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) • fun x => f (x + k * h)) p μ
      ≤ ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ≥0∞) * B :=
        Finset.sum_le_sum fun k hk => by
          rw [eLpNorm_const_smul, enorm_iterDiff_coeff]
          exact mul_le_mul_right (hB k hk) _
    _ = 2 ^ r * B := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        rfl

/-- **`‖Δ_h^r f‖_{L_p[a, b - rh]} ≤ 2^r ‖f‖_{L_p[a,b]}`** for `h ≥ 0`. -/
theorem eLpNorm_iterDiff_le {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (a b : ℝ) :
    eLpNorm (iterDiff r h f) p (volume.restrict (Icc a (b - r * h))) ≤
      2 ^ r * eLpNorm f p (volume.restrict (Icc a b)) := by
  refine eLpNorm_iterDiff_le_of_forall hp fun k hk => ?_
  have hkr : (k : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [eLpNorm_comp_add_Icc hf]
  exact eLpNorm_Icc_mono f p (by nlinarith) (by nlinarith [mul_le_mul_of_nonneg_right hkr hh])

/-- The **modulus of smoothness of order `r`** on `[a, b]` in `L_p`:
`ω_r(f, t, [a, b])_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r f‖_{L_p[a, b - r h]}`. -/
noncomputable def modulus (r : ℕ) (p : ℝ≥0∞) (a b : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : h ∈ Icc 0 t), eLpNorm (iterDiff r h f) p (volume.restrict (Icc a (b - r * h)))

/-- `‖Δ_h^r f‖_{L_p[a, b - rh]} ≤ ω_r(f, t)` for `0 ≤ h ≤ t`. -/
theorem eLpNorm_iterDiff_le_modulus {r : ℕ} {p : ℝ≥0∞} {a b : ℝ} {f : ℝ → ℂ} {t h : ℝ}
    (hh : h ∈ Icc 0 t) :
    eLpNorm (iterDiff r h f) p (volume.restrict (Icc a (b - r * h))) ≤ modulus r p a b f t :=
  le_iSup₂ (f := fun (h : ℝ) (_ : h ∈ Icc 0 t) =>
    eLpNorm (iterDiff r h f) p (volume.restrict (Icc a (b - r * h)))) h hh

/-- The modulus increases in `t`. -/
theorem modulus_mono (r : ℕ) (p : ℝ≥0∞) (a b : ℝ) (f : ℝ → ℂ) : Monotone (modulus r p a b f) :=
  fun _ _ hst => iSup₂_le fun _ hh => eLpNorm_iterDiff_le_modulus ⟨hh.1, hh.2.trans hst⟩

/-- `ω_r(f, t) ≤ 2^r ‖f‖_{L_p[a,b]}`. -/
theorem modulus_le {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (a b t : ℝ) :
    modulus r p a b f t ≤ 2 ^ r * eLpNorm f p (volume.restrict (Icc a b)) :=
  iSup₂_le fun _ hh => eLpNorm_iterDiff_le hf hp r hh.1 a b

/-- The modulus is subadditive. -/
theorem modulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (a b : ℝ) (f g : ℝ → ℂ) (t : ℝ) :
    modulus r p a b (f + g) t ≤ modulus r p a b f t + modulus r p a b g t := by
  refine iSup₂_le fun h hh => ?_
  rw [iterDiff_add]
  exact (eLpNorm_add_le hp).trans
    (add_le_add (eLpNorm_iterDiff_le_modulus hh) (eLpNorm_iterDiff_le_modulus hh))

/-- The modulus is homogeneous. -/
theorem modulus_const_mul (r : ℕ) (p : ℝ≥0∞) (a b : ℝ) (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    modulus r p a b (fun x => c * f x) t = ‖c‖ₑ * modulus r p a b f t := by
  simp only [modulus, iterDiff_const_mul, ENNReal.mul_iSup]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_const_smul c (iterDiff r h f) p _

/-- The modulus vanishes on polynomials of degree `< r`. -/
theorem modulus_polynomial {r : ℕ} {P : Polynomial ℂ} (hP : P ∈ Polynomial.degreeLT ℂ r)
    (p : ℝ≥0∞) (a b t : ℝ) : modulus r p a b (fun x => P.eval (x : ℂ)) t = 0 := by
  simp [modulus, iterDiff_polynomial hP]

/-- **The modulus depends only on the class in `L_p[a, b]`**: functions that agree almost
everywhere on `[a, b]` have the same modulus. -/
theorem modulus_congr_ae {f g : ℝ → ℂ} {a b : ℝ} (hfg : f =ᵐ[volume.restrict (Icc a b)] g) (r : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    modulus r p a b f t = modulus r p a b g t := by
  simp only [modulus]
  congr 1
  funext h
  congr 1
  funext hh
  refine eLpNorm_congr_ae ?_
  have hk : ∀ k ∈ Finset.range (r + 1), (fun x => f (x + k * h)) =ᵐ[volume.restrict
      (Icc a (b - r * h))] fun x => g (x + k * h) := fun k hk => by
    have hkr : (k : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hpre : (fun x => x + k * h) ⁻¹' Icc (a + k * h) (b - r * h + k * h) =
        Icc a (b - r * h) := by
      ext x
      simp only [mem_preimage, mem_Icc]
      constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]
    have hmp : MeasurePreserving (· + k * h) (volume.restrict (Icc a (b - r * h)))
        (volume.restrict (Icc (a + k * h) (b - r * h + k * h))) := by
      have := (measurePreserving_add_right volume (k * h)).restrict_preimage
        (measurableSet_Icc (a := a + k * h) (b := b - r * h + k * h))
      rwa [hpre] at this
    have hsub : Icc (a + k * h) (b - r * h + k * h) ⊆ Icc a b :=
      Icc_subset_Icc (by nlinarith [hh.1]) (by nlinarith [hh.1])
    exact hmp.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae_restrict_of_subset hsub hfg)
  filter_upwards [(Filter.eventually_all_finset _).2 hk] with x hx
  rw [iterDiff_apply, iterDiff_apply]
  exact Finset.sum_congr rfl fun k hk' => by rw [hx k hk']

/-- **Reflection**: `ω_r(f(a + b - ·), t, [a, b]) = ω_r(f, t, [a, b])`. -/
theorem modulus_reflect {f : ℝ → ℂ} (hf : Measurable f) (r : ℕ) (p : ℝ≥0∞) (a b t : ℝ) :
    modulus r p a b (fun x => f (a + b - x)) t = modulus r p a b f t := by
  simp only [modulus]
  congr 1
  funext h
  congr 1
  funext _
  have hfun : iterDiff r h (fun x => f (a + b - x)) =
      fun x => (-1 : ℂ) ^ r * iterDiff r h f (a + b - r * h - x) := by
    funext x
    rw [iterDiff_reflect]
    congr 2
    ring
  rw [hfun, show (fun x => (-1 : ℂ) ^ r * iterDiff r h f (a + b - r * h - x)) =
      ((-1 : ℂ) ^ r) • fun x => iterDiff r h f (a + b - r * h - x) from rfl, eLpNorm_const_smul,
    eLpNorm_comp_sub_Icc (measurable_iterDiff hf r h)]
  simp only [enorm_pow, enorm_neg, enorm_one, one_pow, one_mul]
  congr 3 <;> ring

end Interval
