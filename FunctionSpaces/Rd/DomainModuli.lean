/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Differences

/-!
# Moduli of smoothness on subsets of `V`

For `U ⊆ V`, a step `h ∈ V` and `r ∈ ℕ`, the points `x` with `x, x + h, …, x + r h ∈ U` form the
set `U_{rh}` (`Rd.stepSet`, a subset of `U`). The **restricted difference** is
`Δ_h^r(f, x, U) = Δ_h^r f(x)` for `x ∈ U_{rh}` and `0` otherwise, and the **modulus of
smoothness on `U`** is

`ω_r(f, t, U)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r(f, ·, U)‖_{L_p(U)}`

(DeVore–Sharpley, (2.1); `Rd.modulusOn`). It uses only the values of `f` on `U`
(`Rd.modulusOn_indicator`, `Rd.modulusOn_congr_ae`), increases in `t`, is subadditive, is bounded
by `2^r ‖f‖_{L_p(U)}` (`Rd.modulusOn_le`) and by the modulus on `V` (`Rd.modulusOn_le_modulus`),
and on `U = V` it is the modulus on `V` (`Rd.modulusOn_univ`). `Rd.lpModulusOn` samples it for
`f ∈ L_p` at the dyadic scales `2^(-k)`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Points whose steps stay in a set -/

/-- The set `U_{rh}` of the points `x` with `x, x + h, …, x + r h ∈ U`. -/
def stepSet (U : Set V) (r : ℕ) (h : V) : Set V := {x | ∀ l ≤ r, x + (l : ℝ) • h ∈ U}

/-- `U_{rh} ⊆ U` (the case `l = 0`). -/
theorem stepSet_subset (U : Set V) (r : ℕ) (h : V) : stepSet U r h ⊆ U := fun x hx => by
  simpa using hx 0 (Nat.zero_le r)

/-- `U_{rh} ⊆ O_{rh}` for `U ⊆ O`. -/
theorem stepSet_mono {U O : Set V} (hUO : U ⊆ O) (r : ℕ) (h : V) : stepSet U r h ⊆ stepSet O r h :=
  fun _ hx l hl => hUO (hx l hl)

/-- `V_{rh} = V`. -/
@[simp]
theorem stepSet_univ (r : ℕ) (h : V) : stepSet (Set.univ : Set V) r h = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ => Set.mem_univ _

/-- **Restricted differences use only the values on `U`**:
`1_{U_{rh}} Δ_h^r (1_U f) = 1_{U_{rh}} Δ_h^r f`. -/
theorem indicator_stepSet_higherDiff_indicator (U : Set V) (r : ℕ) (h : V) (f : V → ℂ) :
    (stepSet U r h).indicator ((fwdDiff h)^[r] (U.indicator f)) =
      (stepSet U r h).indicator ((fwdDiff h)^[r] f) := by
  funext x
  by_cases hx : x ∈ stepSet U r h
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, higherDiff_apply, higherDiff_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Set.indicator_of_mem (hx l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)))]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-! ### The modulus of smoothness on a set -/

variable [MeasurableSpace V] {μ : Measure V}

variable (μ) in
/-- The **modulus of smoothness on `U`**, `ω_r(f, t, U)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r(f, ·, U)‖_p`,
with the restricted difference `Δ_h^r(f, ·, U) = 1_{U_{rh}} Δ_h^r f`. -/
noncomputable def modulusOn (U : Set V) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (h : V) (_ : ‖h‖ ≤ t), eLpNorm ((stepSet U r h).indicator ((fwdDiff h)^[r] f)) p μ

/-- `‖Δ_h^r(f, ·, U)‖_p ≤ ω_r(f, t, U)_p` for `‖h‖ ≤ t`. -/
theorem eLpNorm_indicator_higherDiff_le_modulusOn {U : Set V} {r : ℕ} {p : ℝ≥0∞} {f : V → ℂ}
    {t : ℝ} {h : V} (hh : ‖h‖ ≤ t) :
    eLpNorm ((stepSet U r h).indicator ((fwdDiff h)^[r] f)) p μ ≤ modulusOn μ U r p f t :=
  le_iSup₂ (f := fun (h : V) (_ : ‖h‖ ≤ t) =>
    eLpNorm ((stepSet U r h).indicator ((fwdDiff h)^[r] f)) p μ) h hh

/-- The modulus on `U` increases in `t`. -/
theorem modulusOn_mono (U : Set V) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) :
    Monotone (modulusOn μ U r p f) :=
  fun _ _ hst => iSup₂_le fun _ hh => eLpNorm_indicator_higherDiff_le_modulusOn (hh.trans hst)

/-- The modulus on `V` is the modulus. -/
@[simp]
theorem modulusOn_univ (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) :
    modulusOn μ Set.univ r p f t = modulus μ r p f t := by
  simp [modulusOn, modulus]

/-- **The modulus on `U` uses only the values on `U`**: `ω_r(1_U f, t, U)_p = ω_r(f, t, U)_p`. -/
theorem modulusOn_indicator (U : Set V) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) :
    modulusOn μ U r p (U.indicator f) t = modulusOn μ U r p f t := by
  simp only [modulusOn, indicator_stepSet_higherDiff_indicator]

/-- The modulus on `U` is subadditive. -/
theorem modulusOn_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (U : Set V) (r : ℕ) (f g : V → ℂ) (t : ℝ) :
    modulusOn μ U r p (f + g) t ≤ modulusOn μ U r p f t + modulusOn μ U r p g t := by
  refine iSup₂_le fun h hh => ?_
  rw [fwdDiff_iter_add, Set.indicator_add']
  exact (eLpNorm_add_le hp).trans (add_le_add (eLpNorm_indicator_higherDiff_le_modulusOn hh)
    (eLpNorm_indicator_higherDiff_le_modulusOn hh))

variable [BorelSpace V]

/-- `U_{rh}` is measurable for measurable `U`. -/
theorem measurableSet_stepSet {U : Set V} (hU : MeasurableSet U) (r : ℕ) (h : V) :
    MeasurableSet (stepSet U r h) := by
  simp only [stepSet, Set.ofPred_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => measurable_add_const _ hU

/-- **The modulus on `U` is at most the modulus on `V`**, `ω_r(f, t, U)_p ≤ ω_r(f, t)_p`. -/
theorem modulusOn_le_modulus {U : Set V} (hU : MeasurableSet U) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ)
    (t : ℝ) : modulusOn μ U r p f t ≤ modulus μ r p f t :=
  iSup₂_mono fun h _ => eLpNorm_indicator_le _ (measurableSet_stepSet hU r h)

variable [μ.IsAddHaarMeasure]

/-- **The modulus on a set grows with the set**: `ω_r(f, t, U)_p ≤ ω_r(f, t, O)_p` for `U ⊆ O`. -/
theorem modulusOn_mono_set {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {U O : Set V}
    (hU : MeasurableSet U) (hUO : U ⊆ O) (r : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    modulusOn μ U r p f t ≤ modulusOn μ O r p f t :=
  iSup₂_mono fun h _ => eLpNorm_mono
    ((aestronglyMeasurable_higherDiff hf r h).indicator (measurableSet_stepSet hU r h))
    fun x => norm_indicator_le_of_subset (stepSet_mono hUO r h) _ x

/-- `ω_r(f, t, U)_p ≤ 2^r ‖f‖_{L_p(U)}`. -/
theorem modulusOn_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {U : Set V}
    (hU : MeasurableSet U) {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (t : ℝ) :
    modulusOn μ U r p f t ≤ 2 ^ r * eLpNorm (U.indicator f) p μ := by
  rw [← modulusOn_indicator]
  exact (modulusOn_le_modulus hU r p _ t).trans (modulus_le (hf.indicator hU) hp r t)

/-- **The modulus on `U` depends only on the class of `f` on `U`**: if `1_U f = 1_U g` almost
everywhere, then `ω_r(f, t, U)_p = ω_r(g, t, U)_p`. -/
theorem modulusOn_congr_ae {U : Set V} {f g : V → ℂ} (hfg : U.indicator f =ᵐ[μ] U.indicator g)
    (r : ℕ) (p : ℝ≥0∞) (t : ℝ) : modulusOn μ U r p f t = modulusOn μ U r p g t := by
  rw [← modulusOn_indicator U r p f, ← modulusOn_indicator U r p g]
  simp only [modulusOn]
  congr 1
  funext h
  congr 1
  funext _
  refine eLpNorm_congr_ae ?_
  filter_upwards [higherDiff_congr_ae hfg r h] with x hx
  by_cases hxU : x ∈ stepSet U r h
  · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, hx]
  · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]

/-! ### The modulus on a set at dyadic scales -/

variable {p : ℝ≥0∞}

variable (p) in
/-- The modulus on `U` of an element of `L_p` at the dyadic scale `2^(-k)`. -/
noncomputable def lpModulusOn (U : Set V) (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) : ℝ≥0∞ :=
  modulusOn μ U r p (f : V → ℂ) (1 / 2 ^ k)

omit [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The modulus on `U` decreases along the dyadic scales. -/
theorem lpModulusOn_succ_le (U : Set V) (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) :
    lpModulusOn p U r f (k + 1) ≤ lpModulusOn p U r f k :=
  modulusOn_mono U r p _ (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ one_le_two (Nat.le_succ k)))

omit [μ.IsAddHaarMeasure] in
/-- `ω_r(f, 2^(-k), U)_p ≤ ω_r(f, 2^(-k))_p` on `L_p`. -/
theorem lpModulusOn_le_lpModulus [Fact (1 ≤ p)] {U : Set V} (hU : MeasurableSet U) (r : ℕ)
    (f : Lp ℂ p μ) (k : ℕ) : lpModulusOn p U r f k ≤ lpModulus p r f k :=
  modulusOn_le_modulus hU r p _ _

/-- The modulus on a set at the dyadic scales grows with the set. -/
theorem lpModulusOn_mono_set {U O : Set V} (hU : MeasurableSet U) (hUO : U ⊆ O) (r : ℕ)
    (f : Lp ℂ p μ) (k : ℕ) : lpModulusOn p U r f k ≤ lpModulusOn p O r f k :=
  modulusOn_mono_set (Lp.aestronglyMeasurable f) hU hUO r p _

/-- Elements of `L_p` that agree on `U` have the same moduli on `U`. -/
theorem lpModulusOn_congr {U : Set V} {f g : Lp ℂ p μ}
    (hfg : U.indicator f =ᵐ[μ] U.indicator g) (r k : ℕ) :
    lpModulusOn p U r f k = lpModulusOn p U r g k :=
  modulusOn_congr_ae hfg r p _

end Rd
