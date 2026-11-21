/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Sequences.Lq
public import FunctionSpaces.Analysis.Differences.Differences

/-!
# Moduli of smoothness under linear changes of variables

Let `V` and `W` be finite-dimensional real normed spaces with additive Haar measures `μ` and
`ν`, and let `e : V → W` be a continuous linear map that carries `μ` to `ν`
(`MeasurePreserving e μ ν`), such as the coordinates of an orthonormal basis.

* **Moduli.** Differences commute with additive maps, `Δ_h^r (f ∘ e) = (Δ_{e h}^r f) ∘ e`
  (`Rd.higherDiff_comp_addHom`). Since `‖e h‖ ≤ ‖e‖ ‖h‖` and `e` preserves the measures,
  `ω_r(f ∘ e, t)_{L_p(μ)} ≤ ω_r(f, ‖e‖ t)_{L_p(ν)}` for every `p` (`Rd.modulus_comp_le`), and with
  the dilation of the scale `ω_r(f ∘ e, 2^(-k))_p ≤ (1 + ‖e‖)^r ω_r(f, 2^(-k))_p` on `L_p`,
  `1 ≤ p ≤ ∞` (`Rd.lpModulus_compMeasurePreserving_le`).
* **Besov quasi-norms.** Composition with a measure preserving map keeps the `L_p` norm
  (`MeasureTheory.Lp.enorm_compMeasurePreserving`), so the quasi-norm
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}` of `f ∘ e` is at most `(1 + ‖e‖)^r` times that of
  `f` (`Rd.modNorm_compMeasurePreserving_le`). For a continuous linear equivalence the two
  quasi-norms are finite together (`Rd.modNorm_compMeasurePreserving_lt_top_iff`): the Besov
  spaces defined by differences do not depend on the choice of linear coordinates and norm.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- **Composition with a measure preserving map keeps the `L_p` norm**: for a measure preserving
`f : (α, μ) → (β, μb)`, every exponent `p` and `g ∈ L_p(μb)`,
`‖g ∘ f‖_{L_p(μ)} = ‖g‖_{L_p(μb)}` in `[0, ∞]`, the extended-norm form of Mathlib's
`MeasureTheory.Lp.norm_compMeasurePreserving` (from
`MeasureTheory.eLpNorm_comp_measurePreserving`). -/
theorem MeasureTheory.Lp.enorm_compMeasurePreserving {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup E] {p : ℝ≥0∞} {μ : Measure α} {μb : Measure β}
    {f : α → β} (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    ‖Lp.compMeasurePreserving f hf g‖ₑ = ‖g‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (Lp.coeFn_compMeasurePreserving g hf),
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable g) hf]

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] {ν : Measure W} [ν.IsAddHaarMeasure]

omit [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- **The modulus under a linear change of variables**: let `e : V → W` be continuous, linear
and measure preserving from `μ` to `ν`. Then for every a.e. strongly measurable `f` on `W`, every
order `r`, exponent `p` and scale `t`, `ω_r(f ∘ e, t)_{L_p(μ)} ≤ ω_r(f, ‖e‖ t)_{L_p(ν)}`: for
`‖h‖ ≤ t`, `‖Δ_h^r (f ∘ e)‖_{L_p(μ)} = ‖Δ_{e h}^r f‖_{L_p(ν)}` (`Rd.higherDiff_comp_addHom`,
Mathlib's `MeasureTheory.eLpNorm_comp_measurePreserving`) and `‖e h‖ ≤ ‖e‖ t`. -/
theorem modulus_comp_le (e : V →L[ℝ] W) (he : MeasurePreserving e μ ν) {f : W → ℂ}
    (hf : AEStronglyMeasurable f ν) (r : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    modulus μ r p (f ∘ e) t ≤ modulus ν r p f (‖e‖ * t) := by
  refine iSup₂_le fun h hh => ?_
  rw [higherDiff_comp_addHom,
    eLpNorm_comp_measurePreserving (aestronglyMeasurable_higherDiff hf r (e h)) he]
  exact eLpNorm_higherDiff_le_modulus
    ((e.le_opNorm h).trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _)))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The dyadic moduli under a linear change of variables**: let `e : V → W` be continuous,
linear and measure preserving from `μ` to `ν`, and `1 ≤ p`. Then for every `F ∈ L_p(ν)`, every
order `r` and every `k`, the composition `F ∘ e ∈ L_p(μ)` (Mathlib's
`MeasureTheory.Lp.compMeasurePreserving`) satisfies
`ω_r(F ∘ e, 2^(-k))_p ≤ (1 + ‖e‖)^r ω_r(F, 2^(-k))_p`: `Rd.modulus_comp_le` and the dilation of
the scale by `‖e‖` (`Rd.modulus_mul_le`). -/
theorem lpModulus_compMeasurePreserving_le (e : V →L[ℝ] W) (he : MeasurePreserving e μ ν)
    (r : ℕ) (F : Lp ℂ p ν) (k : ℕ) :
    lpModulus p r (Lp.compMeasurePreserving e he F) k ≤
      ENNReal.ofReal (1 + ‖e‖) ^ r * lpModulus p r F k := by
  rw [lpModulus, modulus_congr_ae (Lp.coeFn_compMeasurePreserving F he)]
  exact (modulus_comp_le e he (Lp.aestronglyMeasurable F) r p _).trans
    (modulus_mul_le (Lp.aestronglyMeasurable F) Fact.out r (norm_nonneg _) (by positivity))

/-- **Besov quasi-norms under a linear change of variables**: let `e : V → W` be continuous,
linear and measure preserving from `μ` to `ν`, and `1 ≤ p`. Then for every `F ∈ L_p(ν)`, every
order `r`, smoothness `s` and `q`,
`‖F ∘ e‖_p + ‖(2^(ks) ω_r(F ∘ e, 2^(-k))_p)_k‖_{ℓ_q} ≤
(1 + ‖e‖)^r (‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q})`
(`MeasureTheory.Lp.enorm_compMeasurePreserving`, `Rd.lpModulus_compMeasurePreserving_le`; the
factor is at least `1`). -/
theorem modNorm_compMeasurePreserving_le (e : V →L[ℝ] W) (he : MeasurePreserving e μ ν) (r : ℕ)
    (s : ℝ) (q : ℝ≥0∞) (F : Lp ℂ p ν) :
    ‖Lp.compMeasurePreserving e he F‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpModulus p r (Lp.compMeasurePreserving e he F) k) ≤
      ENNReal.ofReal (1 + ‖e‖) ^ r *
        (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  have h1 : 1 ≤ ENNReal.ofReal (1 + ‖e‖) ^ r := one_le_pow₀ (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (norm_nonneg e)))
  rw [mul_add, ← ENNReal.lqNorm_const_mul, Lp.enorm_compMeasurePreserving]
  refine add_le_add (le_mul_of_one_le_left' h1) (ENNReal.lqNorm_mono fun k => ?_)
  calc dyadicWeight s k * lpModulus p r (Lp.compMeasurePreserving e he F) k
      ≤ dyadicWeight s k * (ENNReal.ofReal (1 + ‖e‖) ^ r * lpModulus p r F k) := by
        gcongr
        exact lpModulus_compMeasurePreserving_le e he r F k
    _ = ENNReal.ofReal (1 + ‖e‖) ^ r * (dyadicWeight s k * lpModulus p r F k) := by ring

/-- **Besov spaces do not depend on linear coordinates**: let `e : V → W` be a continuous linear
equivalence that is measure preserving from `μ` to `ν`, and `1 ≤ p`. Then for every
`F ∈ L_p(ν)`, every order `r`, smoothness `s` and `q`,
`‖F ∘ e‖_p + ‖(2^(ks) ω_r(F ∘ e, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. One direction is
`Rd.modNorm_compMeasurePreserving_le` for `e`, the other the same for `e⁻¹`, which is measure
preserving from `ν` to `μ` (Mathlib's `MeasureTheory.MeasurePreserving.symm`), since
`(F ∘ e) ∘ e⁻¹ = F`. -/
theorem modNorm_compMeasurePreserving_lt_top_iff (e : V ≃L[ℝ] W) (he : MeasurePreserving e μ ν)
    (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (F : Lp ℂ p ν) :
    ‖Lp.compMeasurePreserving e he F‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpModulus p r (Lp.compMeasurePreserving e he F) k)
          < ∞ ↔
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞ := by
  have he' : MeasurePreserving e.symm ν μ :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv he
  have hFF : Lp.compMeasurePreserving e.symm he' (Lp.compMeasurePreserving e he F) = F := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e he F) he',
      he'.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving F he)] with x h1 h2
    rw [h1, h2]
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  constructor
  · intro h
    rw [← hFF]
    exact (modNorm_compMeasurePreserving_le (e.symm : W →L[ℝ] V) he' r s q _).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) h)
  · intro h
    exact (modNorm_compMeasurePreserving_le (e : V →L[ℝ] W) he r s q F).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) h)

end Rd
