/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.Besov.Basic
public import ApproximationSpaces.Transfer

/-!
# Elementary embeddings of Besov spaces

Three embeddings of the Besov spaces of a scheme of functions hold for every `0 < p ≤ ∞` and
`0 < q ≤ ∞` without any property of the scheme. They follow from the E-method calculus for the
couple of the scheme in `L_p`:

* **in the smoothness and fine indices**: `B^s_{p,q} ⊆ B^t_{p,q'}` for `0 ≤ t < s`, or `t = s`
  and `q ≤ q'` (`FunctionScheme.MemBesov.mono`), through the dyadic norms of the couple
  (`InterpCouple.eNormDyadic_le_of_lt`, `InterpCouple.eNormDyadic_mono_exponent`);
* **in the integrability**: for `0 < p ≤ r ≤ ∞`, `B^s_{r,q} ⊆ B^s_{p,q}` through the inclusion
  `ι_{r,p} : L_r ↪ L_p` (`FunctionScheme.MemBesov.inclusion`), with
  `‖ι_{r,p} f‖_{B^s_{p,q}} ≤ μ(Ω)^(1/p - 1/r) ‖f‖_{B^s_{r,q}}`
  (`FunctionScheme.besovNorm_inclusion_le`): by Hölder's inequality the inclusion multiplies the
  quasi-norm by at most `μ(Ω)^(1/p - 1/r)`, a finite constant
  (`ENNReal.one_div_toReal_sub_one_div_toReal_nonneg`), and it maps approximants to
  approximants;
* **from the sup norm**: for an approximation scheme `T` of bounded continuous functions, the
  uniform Besov space of `T` embeds into every `B^s_{p,q}` of the scheme of functions of `T`
  (`FunctionScheme.MemBesov.of_sup`), along the map `a ↦ ι_{∞,p}(a)` from bounded continuous
  functions to `L_p`, which multiplies the quasi-norm by at most `μ(Ω)^(1/p)`
  (`BoundedContinuousFunction.eLpNorm_topInclusion_toLp_le`).

The second and the third are instances of the bound of Pietsch's form under an additive map
(`InterpCouple.eNormPietsch_map_le`). The embeddings in the opposite direction, from
`B^s_{p,q}` into `B^{s'}_{r,q}` with `r > p`, cost smoothness and need a Nikolskii inequality for
the scheme (`FunctionSpaces.MeasureSpaces.Besov.Embeddings`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

/-- **The exponent of Hölder's inequality between `L_r` and `L_p` is nonnegative**:
`0 ≤ 1/p - 1/r` for `0 < p ≤ r ≤ ∞`, with `1/∞ = 0`. So the constant `μ(Ω)^(1/p - 1/r)` of
Hölder's inequality `‖f‖_p ≤ μ(Ω)^(1/p - 1/r) ‖f‖_r` is finite for a finite measure `μ`. -/
theorem ENNReal.one_div_toReal_sub_one_div_toReal_nonneg {p r : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpr : p ≤ r) : 0 ≤ 1 / p.toReal - 1 / r.toReal := by
  rcases eq_or_ne r ∞ with rfl | hr
  · simp
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top hr hpr))
    (ENNReal.toReal_mono hr hpr)

/-- **The `L_p` quasi-norm of a bounded continuous function**: for a finite measure `μ` on `Ω`,
every exponent `p` and every bounded continuous `b`, the class `ι_{∞,p}(b)` of `b` in `L_p(μ)`,
taken through `L_∞(μ)`, satisfies `‖ι_{∞,p}(b)‖_p ≤ μ(Ω)^(1/p) ‖b‖_∞`, since `b` is bounded by
its sup norm everywhere (`MeasureTheory.eLpNorm_le_of_ae_enorm_bound`). For `1 ≤ p` this is
Mathlib's `BoundedContinuousFunction.Lp_nnnorm_le`. -/
theorem BoundedContinuousFunction.eLpNorm_topInclusion_toLp_le {α E 𝕜 : Type*}
    [MeasurableSpace α] {μ : Measure α} [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup E]
    [SecondCountableTopologyEither α E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [IsFiniteMeasure μ] (p : ℝ≥0∞) (b : α →ᵇ E) :
    eLpNorm (Lp.topInclusion (𝕜 := 𝕜) μ p
        (BoundedContinuousFunction.toLp (E := E) ∞ μ 𝕜 b)) p μ ≤
      μ Set.univ ^ p.toReal⁻¹ * ‖b‖ₑ := by
  rw [mul_comm, ← smul_eq_mul]
  refine eLpNorm_le_of_ae_enorm_bound (Lp.aestronglyMeasurable _) ?_
  filter_upwards [Lp.coeFn_topInclusion (𝕜 := 𝕜) (p := p)
      (BoundedContinuousFunction.toLp (E := E) ∞ μ 𝕜 b),
    BoundedContinuousFunction.coeFn_toLp (E := E) (p := ∞) (μ := μ) (𝕜 := 𝕜) b] with x h1 h2
  rw [h1, h2, enorm_le_iff_norm_le]
  exact b.norm_coe_le_norm x

namespace FunctionScheme

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {S : FunctionScheme μ} {p r : ℝ≥0∞} {s t : ℝ} {q q' : ℝ≥0∞}

/-- **Embeddings in the smoothness and fine indices**: for every exponent `p` and
`0 < q ≤ ∞`, if `0 ≤ t` and `t < s`, or `t = s` and `q ≤ q'`, then `B^s_{p,q} ⊆ B^t_{p,q'}`.
The dyadic norms of the couple of `S` in `L_p` compare (`InterpCouple.eNormDyadic_le_of_lt`,
`InterpCouple.eNormDyadic_mono_exponent`), and a finite dyadic norm gives membership for every
fine index (`FunctionScheme.MemBesov.of_eNormDyadic_lt_top`). -/
theorem MemBesov.mono (hq0 : q ≠ 0) (ht : 0 ≤ t) (h : t < s ∨ (t = s ∧ q ≤ q'))
    {f : Lp ℂ p μ} (hf : S.MemBesov p s q f) : S.MemBesov p t q' f := by
  have hs : 0 ≤ s := by rcases h with h | ⟨rfl, -⟩ <;> linarith
  rw [memBesov_iff_eNormDyadic_lt_top hq0 hs] at hf
  refine MemBesov.of_eNormDyadic_lt_top ht ?_
  rcases h with h | ⟨rfl, hqq'⟩
  · exact (InterpCouple.eNormDyadic_le_of_lt hq0 h q' f).trans_lt
      (ENNReal.mul_lt_top (ENNReal.dyadicGeomConst_ne_top (sub_pos.2 h) q').lt_top hf)
  · exact (InterpCouple.eNormDyadic_mono_exponent hq0 hqq' _ f).trans_lt hf

/-- **Embedding in the integrability**, norm form: for `0 < p ≤ r ≤ ∞` and `f ∈ L_r(μ)`,
`‖ι_{r,p} f‖_{B^s_{p,q}} ≤ μ(Ω)^(1/p - 1/r) ‖f‖_{B^s_{r,q}}` with the inclusion
`ι_{r,p} : L_r ↪ L_p`. By Hölder's inequality `‖ι_{r,p} a‖_p ≤ μ(Ω)^(1/p - 1/r) ‖a‖_r`, and
`ι_{r,p}` does not increase the complexity (`FunctionScheme.lpCouple_norm1_inclusion_le`). -/
theorem besovNorm_inclusion_le (hp0 : p ≠ 0) (hpr : p ≤ r) (f : Lp ℂ r μ) :
    S.besovNorm p s q (Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr f) ≤
      μ Set.univ ^ (1 / p.toReal - 1 / r.toReal) * S.besovNorm r s q f := by
  refine InterpCouple.eNormPietsch_map_le
    (Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr).toAddMonoidHom (lpCouple_norm1_zero S r)
    (ENNReal.rpow_ne_top_of_nonneg (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg hp0 hpr)
      (measure_ne_top μ _)) (fun a => ?_) (fun a => lpCouple_norm1_inclusion_le hpr a) s q f
  rw [lpCouple_norm0, lpCouple_norm0, mul_comm]
  exact (Lp.eLpNorm_inclusionOfExponentLeLinear (𝕜 := ℝ) hpr a p).trans_le
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpr (Lp.aestronglyMeasurable a))

/-- **Embedding in the integrability**: for `0 < p ≤ r ≤ ∞`, `B^s_{r,q} ⊆ B^s_{p,q}` through
the inclusion `ι_{r,p} : L_r ↪ L_p`. -/
theorem MemBesov.inclusion (hp0 : p ≠ 0) (hpr : p ≤ r) {f : Lp ℂ r μ}
    (hf : S.MemBesov r s q f) :
    S.MemBesov p s q (Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr f) :=
  (besovNorm_inclusion_le hp0 hpr f).trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg hp0 hpr)
      (measure_ne_top μ _)) hf)

/-- **Embedding of the uniform Besov space**: for an approximation scheme `T` of bounded
continuous functions, every exponent `p` and every `q`, the class in `L_p` of a bounded
continuous function `a` in the approximation space `A^s_q` of `T` in the sup norm lies in
`B^s_{p,q}` of the scheme of functions of `T`. The map `a ↦ ι_{∞,p}(a)` satisfies
`‖ι_{∞,p}(a)‖_p ≤ μ(Ω)^(1/p) ‖a‖_∞` (`BoundedContinuousFunction.eLpNorm_topInclusion_toLp_le`)
and maps `T_n` into the approximants of the scheme of `T` in `L_p`. -/
theorem MemBesov.of_sup [TopologicalSpace Ω] [BorelSpace Ω] {T : ApproximationScheme (Ω →ᵇ ℂ)}
    {a : Ω →ᵇ ℂ} (ha : T.MemApprox s q a) :
    (ofContinuous T μ).MemBesov p s q
      (Lp.topInclusion (𝕜 := ℝ) μ p (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ a)) := by
  have hM : μ Set.univ ^ p.toReal⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (measure_ne_top μ _)
  have h1 : ∀ n, ∀ b ∈ T.sets n, Lp.topInclusion (𝕜 := ℝ) μ p
      (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ b) ∈ lpSets (ofContinuous T μ) p n :=
    fun _ b hb => topInclusion_mem_lpSets (mem_ofContinuous.2 ⟨b, hb, rfl⟩)
  have hle := InterpCouple.eNormPietsch_map_le (A := T.complexityCouple)
    (B := (ofContinuous T μ).lpCouple p) ((Lp.topInclusion (𝕜 := ℝ) μ p).comp
      (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ).toLinearMap).toAddMonoidHom
    (InterpCouple.complexity_norm1_zero (T.zero_mem 0)) hM
    (fun b => BoundedContinuousFunction.eLpNorm_topInclusion_toLp_le (𝕜 := ℝ) p b)
    (InterpCouple.complexity_norm1_map_le _ h1) s q a
  rw [ApproximationScheme.eNormPietsch_complexityCouple] at hle
  exact hle.trans_lt (ENNReal.mul_lt_top hM.lt_top ha)

end FunctionScheme
