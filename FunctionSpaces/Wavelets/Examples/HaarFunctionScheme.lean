/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.HaarQuasiBanach
public import FunctionSpaces.MeasureSpaces.Besov.Embeddings

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
* **The Haar scheme in `L_p`.** For `1 ≤ p ≤ ∞` the scheme `S^(p)` of `Haar.haarScheme ∞` in
  `L_p` is the Haar scheme `Haar.haarScheme p` (`Haar.toLp_haarScheme`), so for these `p` the
  Besov spaces of the steps are the approximation spaces of the Haar scheme in `L_p`
  (`FunctionScheme.memBesov_iff_memApprox`).
* **The Besov spaces of the steps.** For `0 < p ≤ 1`, `0 < q ≤ ∞` and `0 ≤ s < 1/p`, the Besov
  space `B^s_{p,q}` of `Haar.haarScheme ∞` is the space `B^s_{p,q,1}[0, 1]` of the first modulus:
  `f` lies in it iff `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
  (`Haar.memBesov_haarScheme_iff_modulus`).
* **The Nikolskii property.** An approximant `a` of complexity `n ≥ 1` has
  `‖a‖_∞ ≤ n^(1/p) ‖a‖_p` for every `0 < p ≤ ∞` (`Haar.eLpNorm_top_le_of_mem_haarScheme`), so
  the Haar scheme in `L_∞[0, 1]` has the Nikolskii property of dimension `1`
  (`Haar.hasNikolskii_haarScheme`).
* **The Besov embeddings of the steps.** For `0 < p ≤ r ≤ ∞`, `0 < q ≤ ∞` and
  `s > 1/p - 1/r` there is `K < ∞` such that every `f ∈ L_p[0, 1]` with finite dyadic norm
  `‖f‖^dy_{s,q}` in the step couple of `L_p[0, 1]` is the inclusion of some `g ∈ L_r[0, 1]` with
  `‖g‖^dy_{s - (1/p - 1/r), q} ≤ K ‖f‖^dy_{s,q}` in the step couple of `L_r[0, 1]`
  (`Haar.exists_uniform_inclusion_eq_stepCouple`), and there is `K' < ∞` with
  `‖f‖_r ≤ K' ‖f‖^dy_{s,q}` for every `f ∈ L_p[0, 1]`
  (`Haar.exists_eLpNorm_le_eNormDyadic_stepCouple`). Both are the Besov embedding of a scheme of
  functions with the Nikolskii property (`FunctionScheme.exists_uniform_inclusion_eq_of_nikolskii`,
  `FunctionScheme.exists_eLpNorm_le_eNormDyadic_of_nikolskii`). The case `r = 1`, `0 < p ≤ 1` of
  the second holds with an explicit constant (`Haar.eLpNorm_one_le_eNormDyadic`, proved
  directly); the agreement of the two proofs checks the Besov embedding of a scheme of functions
  for `p < 1`. With the first modulus (`Haar.eNormDyadic_stepCouple_lt_top_iff_modulus`), for
  `0 < p ≤ 1` and `1/p - 1/r < s < 1/p` the second bound is the embedding
  `B^s_{p,q,1}[0, 1] ⊆ L_r[0, 1]`.

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
  rw [InterpCouple.dyadicLevels_of_ne_zero hn, SetLike.mem_coe, FunctionScheme.mem_lpSets,
    mem_lpMeasSubgroup_iff_aestronglyMeasurable, ← mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)]
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

/-- **For `1 ≤ p` the Haar scheme in `L_p` is the image of the Haar scheme in `L_∞`**: the
scheme `S^(p)` of `Haar.haarScheme ∞` is `Haar.haarScheme p`, since both have the sets `{0}` and
`V_⌊log₂ n⌋` (`Haar.lpSets_haarScheme`, `Haar.sets_haarScheme`). -/
theorem toLp_haarScheme [Fact (1 ≤ p)] :
    FunctionScheme.toLp (haarScheme ∞) p = haarScheme p :=
  ApproximationScheme.ext fun n =>
    (lpSets_haarScheme p n).trans (congrFun sets_haarScheme n).symm

/-- **The Besov spaces of the dyadic steps are `B^s_{p,q,1}[0, 1]`**: for `0 < p ≤ 1`,
`0 < q ≤ ∞` and `0 ≤ s < 1/p`, `f ∈ L_p[0, 1]` lies in the Besov space of the Haar scheme in
`L_∞[0, 1]` iff `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`. Both conditions say
that the dyadic norm of `f` in the step couple is finite
(`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`, `Haar.stepCouple_eq_lpCouple`,
`Haar.eNormDyadic_stepCouple_lt_top_iff_modulus`). -/
theorem memBesov_haarScheme_iff_modulus (hp0 : p ≠ 0) (hp1 : p ≤ 1) {s : ℝ} {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p vol) :
    FunctionScheme.MemBesov (haarScheme ∞) p s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => ENNReal.dyadicWeight s k *
        Interval.intervalLpModulus p 1 f k) < ∞ := by
  rw [FunctionScheme.memBesov_iff_eNormDyadic_lt_top hq0 hs, ← stepCouple_eq_lpCouple p]
  exact eNormDyadic_stepCouple_lt_top_iff_modulus hp0 hp1 hs hsp f

/-! ### The Nikolskii property and the Besov embeddings of the steps -/

/-- **The Nikolskii bound of the Haar scheme**: for every `0 < p ≤ ∞`, `n ∈ ℕ` and every
approximant `a` of complexity `n` of the Haar scheme in `L_∞[0, 1]`,
`‖a‖_∞ ≤ n^(1/p) ‖a‖_p`, with `1/∞ = 0`. For `n = 0` the approximant is `0`. For `n ≥ 1` it is a
step of level `j = ⌊log₂ n⌋` (`MeasureTheory.Filtration.mem_filtrationScheme`), so
`‖a‖_∞ ≤ 2^(j/p) ‖a‖_p` (`Haar.eLpNorm_top_le_of_mem_lpMeas`), and `2^(j/p) ≤ n^(1/p)` since
`2^j ≤ n`. -/
theorem eLpNorm_top_le_of_mem_haarScheme (hp0 : p ≠ 0) {n : ℕ} {a : Lp ℂ ∞ vol}
    (ha : a ∈ haarScheme ∞ n) :
    eLpNorm a ∞ vol ≤ (n : ℝ≥0∞) ^ p.toReal⁻¹ * eLpNorm a p vol := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [(haarScheme ∞).coe_zero, Set.mem_singleton_iff] at ha
    subst ha
    rw [eLpNorm_congr_ae (Lp.coeFn_zero ℂ ∞ vol), eLpNorm_zero]
    exact zero_le
  refine (eLpNorm_top_le_of_mem_lpMeas hp0
    ((dyadicFiltration.mem_filtrationScheme hn).1 ha)).trans ?_
  rw [one_div, ← ENNReal.natCast_two_pow_rpow]
  gcongr
  exact_mod_cast Nat.pow_log_le_self 2 hn

/-- **The Haar scheme has the Nikolskii property of dimension `1`**: the Haar scheme in
`L_∞[0, 1]`, as a scheme of essentially bounded functions on `[0, 1]`, satisfies
`‖a‖_∞ ≤ n^(1/p) ‖a‖_p` for every `1 ≤ p ≤ ∞`, `n ≥ 1` and `a` of complexity `n`, with the
constant `1` (`Haar.eLpNorm_top_le_of_mem_haarScheme`). On the probability space `[0, 1]` this
bound in `[0, ∞]` gives the Nikolskii property
(`FunctionScheme.HasNikolskii.of_eLpNorm_top_le`). -/
theorem hasNikolskii_haarScheme : FunctionScheme.HasNikolskii (haarScheme ∞) 1 :=
  FunctionScheme.HasNikolskii.of_eLpNorm_top_le fun p hp _ => ⟨1, ENNReal.one_ne_top,
    fun _ _ _ ha => by
      simpa only [one_mul] using
        eLpNorm_top_le_of_mem_haarScheme (zero_lt_one.trans_le hp).ne' ha⟩

variable {r : ℝ≥0∞} {s : ℝ} {q : ℝ≥0∞}

/-- **The Besov embedding of the dyadic steps**, for `0 < p ≤ r ≤ ∞` and `0 < q ≤ ∞`: for
`s > 1/p - 1/r` there is `K < ∞` such that every `f ∈ L_p[0, 1]` with finite dyadic norm
`‖f‖^dy_{s,q} = ‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q}` in the step couple of `L_p[0, 1]` is the
inclusion of some `g ∈ L_r[0, 1]` with `‖g‖^dy_{s - (1/p - 1/r), q} ≤ K ‖f‖^dy_{s,q}` in the step
couple of `L_r[0, 1]`. This is the Besov embedding of a scheme of functions with the Nikolskii
property (`FunctionScheme.exists_uniform_inclusion_eq_of_nikolskii`) for the Haar scheme in
`L_∞[0, 1]` and `D = 1` (`Haar.hasNikolskii_haarScheme`), whose couples in `L_p` and `L_r` are
the step couples (`Haar.stepCouple_eq_lpCouple`). -/
theorem exists_uniform_inclusion_eq_stepCouple (hp0 : p ≠ 0) (hpr : p ≤ r)
    (hs : p.toReal⁻¹ - r.toReal⁻¹ < s) (hq0 : q ≠ 0) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p vol, (stepCouple p).eNormDyadic s q f ≠ ∞ →
      ∃ g : Lp ℂ r vol, Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) vol hpr g = f ∧
        (stepCouple r).eNormDyadic (s - (p.toReal⁻¹ - r.toReal⁻¹)) q g ≤
          K * (stepCouple p).eNormDyadic s q f := by
  have hα : nikolskiiExponent 1 p r = p.toReal⁻¹ - r.toReal⁻¹ := one_mul _
  rw [stepCouple_eq_lpCouple p, stepCouple_eq_lpCouple r, ← hα]
  exact FunctionScheme.exists_uniform_inclusion_eq_of_nikolskii hasNikolskii_haarScheme
    zero_le_one hp0 hpr (hα ▸ hs) hq0

/-- **The dyadic steps embed into `L_r`**: for `0 < p ≤ r ≤ ∞`, `0 < q ≤ ∞` and
`s > 1/p - 1/r` there is `K < ∞` with
`‖f‖_r ≤ K (‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q})` for every `f ∈ L_p[0, 1]`, with the
`E`-functional `E` of the step couple of `L_p[0, 1]`. This is the bound of `‖f‖_r` of the
Besov embedding of a scheme of functions with the Nikolskii property
(`FunctionScheme.exists_eLpNorm_le_eNormDyadic_of_nikolskii`) for the Haar scheme in
`L_∞[0, 1]` and `D = 1` (`Haar.hasNikolskii_haarScheme`), whose couple in `L_p` is the step
couple (`Haar.stepCouple_eq_lpCouple`). Its case `r = 1`, `0 < p ≤ 1` holds with an explicit
constant (`Haar.eLpNorm_one_le_eNormDyadic`). -/
theorem exists_eLpNorm_le_eNormDyadic_stepCouple (hp0 : p ≠ 0) (hpr : p ≤ r)
    (hs : p.toReal⁻¹ - r.toReal⁻¹ < s) (hq0 : q ≠ 0) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p vol,
      eLpNorm f r vol ≤ K * (stepCouple p).eNormDyadic s q f := by
  have hα : nikolskiiExponent 1 p r = p.toReal⁻¹ - r.toReal⁻¹ := one_mul _
  rw [stepCouple_eq_lpCouple p]
  exact FunctionScheme.exists_eLpNorm_le_eNormDyadic_of_nikolskii hasNikolskii_haarScheme
    zero_le_one hp0 hpr (hα ▸ hs) hq0

end Haar
