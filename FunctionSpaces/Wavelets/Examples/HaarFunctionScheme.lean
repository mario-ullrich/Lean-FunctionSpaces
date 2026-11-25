/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.HaarQuasiBanach
public import FunctionSpaces.MeasureSpaces.SchemeLpCouple

/-!
# Dyadic step functions as a scheme of essentially bounded functions

The Haar scheme in `L_∞[0, 1]`, `Haar.haarScheme ∞`, is a scheme of essentially bounded functions
on the probability space `[0, 1]`: its approximants of complexity `n ≥ 1` are the step functions
on the dyadic intervals of level `⌊log₂ n⌋`, the `ℱ_⌊log₂ n⌋`-measurable elements of
`L_∞[0, 1]`. Sent into `L_p[0, 1]` by the inclusion `ι_{∞,p}`, it gives the step couple of
`L_p[0, 1]` for every exponent `p`, also for `0 < p < 1`.

* **Steps are bounded.** An `ℱ_j`-measurable element of `L_p[0, 1]` is the class of an
  `ℱ_j`-measurable element of `L_∞[0, 1]`, since a step function of level `j` takes only `2^j`
  values almost everywhere on `[0, 1]` (`Haar.exists_topInclusion_eq_of_mem_lpMeas`).
* **The approximants in `L_p`.** The approximants of `Haar.haarScheme ∞` in `L_p`
  (`FunctionScheme.lpSets`) are the dyadic levels of the subgroups `V_j` of `ℱ_j`-measurable
  elements of `L_p[0, 1]`: `{0}` at complexity `0` and `V_⌊log₂ n⌋` at complexity `n ≥ 1`
  (`Haar.lpSets_haarScheme`).
* **The couple.** The step couple of `L_p[0, 1]` (`Haar.stepCouple`) is the couple of
  `Haar.haarScheme ∞` in `L_p` (`Haar.stepCouple_eq_lpCouple`), for every exponent `p`. So the
  results on the couple of a scheme of essentially bounded functions in `L_p`
  (`FunctionScheme.lpCouple`) apply to the step couple, and the dyadic steps are a test case of
  the Besov spaces of such a scheme for `0 < p ≤ ∞`.

The declared type of `Haar.haarScheme ∞` is `ApproximationScheme (Lp ℂ ∞ vol)`, so the
declarations of the namespace `FunctionScheme` are applied to it with their full names, as in
`FunctionScheme.lpCouple (Haar.haarScheme ∞) p`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Haar

variable {p : ℝ≥0∞}

/-- **Steps are essentially bounded**: every `ℱ_j`-measurable element `f` of `L_p[0, 1]` is
the class in `L_p` of an `ℱ_j`-measurable element `a` of `L_∞[0, 1]`, `f = ι_{∞,p} a`, since a
step function of level `j` takes only `2^j` values almost everywhere on `[0, 1]`
(`Haar.memLp_of_mem_lpMeas`). -/
theorem exists_topInclusion_eq_of_mem_lpMeas {j : ℕ} {f : Lp ℂ p vol}
    (hf : f ∈ lpMeas ℂ ℝ (dyadicFiltration j) p vol) :
    ∃ a ∈ lpMeas ℂ ℝ (dyadicFiltration j) ∞ vol, Lp.topInclusion (𝕜 := ℝ) vol p a = f := by
  refine ⟨(memLp_of_mem_lpMeas hf ∞).toLp f, ?_, ?_⟩
  · rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
    exact hf.congr (MemLp.coeFn_toLp _).symm
  · ext1
    exact (Lp.coeFn_topInclusion (𝕜 := ℝ) _).trans (MemLp.coeFn_toLp _)

variable (p) in
/-- **The approximants of the Haar scheme in `L_p`**: for every exponent `p` and `n ∈ ℕ`, the
classes in `L_p[0, 1]` of the approximants of complexity `n` of the Haar scheme in `L_∞[0, 1]`
form the dyadic level `n` of the subgroups `V_j` of `ℱ_j`-measurable elements of `L_p[0, 1]`:
`{0}` for `n = 0` and `V_⌊log₂ n⌋` for `n ≥ 1`. -/
theorem lpSets_haarScheme (n : ℕ) :
    FunctionScheme.lpSets (haarScheme ∞) p n =
      InterpCouple.dyadicLevels (fun j => lpMeasSubgroup ℂ (dyadicFiltration j) p vol) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [FunctionScheme.lpSets_zero, InterpCouple.dyadicLevels_zero]
  ext f
  simp only [InterpCouple.dyadicLevels, hn, ↓reduceIte, SetLike.mem_coe]
  rw [FunctionScheme.mem_lpSets, mem_lpMeasSubgroup_iff_aestronglyMeasurable,
    ← mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := mem_lpMeas_iff_aestronglyMeasurable.1
      ((dyadicFiltration.mem_filtrationScheme hn).1 ha)
    exact mem_lpMeas_iff_aestronglyMeasurable.2
      (ha'.congr (Lp.coeFn_topInclusion (𝕜 := ℝ) a).symm)
  · intro hf
    obtain ⟨a, ha, rfl⟩ := exists_topInclusion_eq_of_mem_lpMeas hf
    exact ⟨a, (dyadicFiltration.mem_filtrationScheme hn).2 ha, rfl⟩

variable (p) in
/-- **The step couple is the couple of the Haar scheme in `L_p`**: for every exponent `p`, the
couple of dyadic step functions in `L_p[0, 1]` (`Haar.stepCouple`) is the couple in `L_p` of the
Haar scheme in `L_∞[0, 1]` (`FunctionScheme.lpCouple`). Both are complexity couples of the
quasi-norm `‖·‖_p`, which is Mathlib's `‖f‖ₑ` on `Lp` (`MeasureTheory.Lp.enorm_def`), and of the
same sets (`Haar.lpSets_haarScheme`). -/
theorem stepCouple_eq_lpCouple : stepCouple p = FunctionScheme.lpCouple (haarScheme ∞) p := by
  have hN : (fun f : Lp ℂ p vol => ‖f‖ₑ) = fun f : Lp ℂ p vol => eLpNorm f p vol :=
    funext fun f => Lp.enorm_def f
  have hS : InterpCouple.dyadicLevels (fun j => lpMeasSubgroup ℂ (dyadicFiltration j) p vol) =
      FunctionScheme.lpSets (haarScheme ∞) p :=
    funext fun n => (lpSets_haarScheme p n).symm
  show InterpCouple.complexity _ _ = InterpCouple.complexity _ _
  rw [hN, hS]

end Haar
