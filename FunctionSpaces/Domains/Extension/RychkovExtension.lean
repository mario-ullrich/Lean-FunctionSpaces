/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Lipschitz.LipschitzGraph

/-!
# Rychkov's extension for Lipschitz graph domains

Let `Ω` be a Lipschitz graph domain with cone `K`, `L ≥ 1`, and `k_j`, `η_j` the local means
kernels and the dual kernels of the cone bump of `Ω`, all supported in `-K`. For `f ∈ L_p(V)`,
`1 ≤ p < ∞`, only the values of `f` on `Ω` matter below. The **intrinsic local means
quasi-norm** is `‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}` (`Rd.LipschitzGraph.intrinsicNorm`); it
depends only on `f` on `Ω` (`Rd.LipschitzGraph.intrinsicNorm_congr`).

**Rychkov's extension** (`Rd.LipschitzGraph.extension`) is

`Ext f = ∑_j η_j ⋆ (1_Ω (k_j ⋆ f))`,

an absolutely convergent series in `L_p` for `s > 0` and a finite intrinsic quasi-norm
(`Rd.LipschitzGraph.summable_extTerm`):

* `Ext f = f` on `Ω` (`Rd.LipschitzGraph.cutoff_extension`): by the support principle,
  `1_Ω (η_j ⋆ (1_Ω h)) = 1_Ω (η_j ⋆ h)`, so on `Ω` the partial sums are those of the reproducing
  formula `∑_{j ≤ J} η_j ⋆ k_j ⋆ f → f`;
* for `0 < s < L`,
  `‖Ext f‖_p + ‖(2^(is) ω_L(Ext f, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`
  (`Rd.LipschitzGraph.modNorm_extension_le`), by the synthesis estimate of local means.

**Restrictions** (`Rd.LipschitzGraph.exists_besov_extension_iff`): for `0 < s < L`, `f` agrees on
`Ω` with some `F ∈ L_p(V)` satisfying the Besov condition by differences iff the intrinsic
quasi-norm of `f` is finite, and `Ext f` is such an `F`. The construction does not depend on `s`:
one operator serves all `0 < s < L`.
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The terms `η_j ⋆ (1_Ω (k_j ⋆ f))` of the extension. -/
noncomputable def extTerm (hp : p ≠ ∞) (L j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure V) :=
  convLp hp (Ω.coneBump.integrable_dual L j) (Ω.cutoff (Ω.coneBump.localMean hp L j f))

/-- The **intrinsic local means quasi-norm** `‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
noncomputable def intrinsicNorm (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight s j * ‖Ω.cutoff (Ω.coneBump.localMean hp L j f)‖ₑ)

/-- **The intrinsic quasi-norm depends only on `f` on `Ω`**: the kernels `k_j` are supported in
`-K` (the support principle). -/
theorem intrinsicNorm_congr (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    {F f : Lp ℂ p (volume : Measure V)} (hFf : Ω.cutoff F = Ω.cutoff f) :
    Ω.intrinsicNorm hp L s q F = Ω.intrinsicNorm hp L s q f := by
  unfold intrinsicNorm
  congr 1
  funext j
  exact congrArg (fun g => dyadicWeight s j * ‖g‖ₑ)
    (Ω.cutoff_convLp_eq hp (Ω.coneBump.integrable_kernel L j) (Ω.coneSupported_kernel L j) hFf)

/-- The intrinsic quasi-norm is at most the local means quasi-norm. -/
theorem intrinsicNorm_le_localMeansNorm (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    Ω.intrinsicNorm hp L s q f ≤ Ω.coneBump.localMeansNorm hp L s q f :=
  ENNReal.lqNorm_mono fun _ => mul_le_mul' le_rfl (enorm_indicatorLp_le _ _)

/-- **The extension converges absolutely** for `s > 0` and a finite intrinsic quasi-norm:
`‖η_j ⋆ (1_Ω (k_j ⋆ f))‖_p ≤ 2 ‖m‖_1 2^(-js) ‖f‖_intr`. -/
theorem summable_extTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    Summable fun j => Ω.extTerm hp L j f := by
  set X := Ω.intrinsicNorm hp L s q f
  set M := eLpNorm (momentKernel Ω.coneBump.toFun L) 1 volume
  have hle : ∀ j, ‖Ω.extTerm hp L j f‖ₑ ≤ 2 * M * (dyadicWeight (-s) j * X) := fun j => by
    have hX : dyadicWeight s j * ‖Ω.cutoff (Ω.coneBump.localMean hp L j f)‖ₑ ≤ X :=
      ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
        (fun j => dyadicWeight s j * ‖Ω.cutoff (Ω.coneBump.localMean hp L j f)‖ₑ) j
    calc ‖Ω.extTerm hp L j f‖ₑ
        ≤ eLpNorm (Ω.coneBump.dual L j) 1 volume *
            ‖Ω.cutoff (Ω.coneBump.localMean hp L j f)‖ₑ := enorm_convLp_le hp _ _
      _ ≤ 2 * M * (dyadicWeight (-s) j *
            (dyadicWeight s j * ‖Ω.cutoff (Ω.coneBump.localMean hp L j f)‖ₑ)) := by
          rw [← mul_assoc (dyadicWeight (-s) j), ENNReal.dyadicWeight_neg_mul_self, one_mul]
          exact mul_le_mul' (Ω.coneBump.eLpNorm_dual_one_le L j) le_rfl
      _ ≤ 2 * M * (dyadicWeight (-s) j * X) := by gcongr
  have htsum : ∑' j, ‖Ω.extTerm hp L j f‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_dyadicWeight_neg]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (memLp_one_iff_integrable.2 (integrable_momentKernel Ω.coneBump.integrable L)).eLpNorm_ne_top)
      (ENNReal.mul_ne_top (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs) hf.ne)
  exact Summable.of_norm (by simpa using ENNReal.summable_toReal htsum)

/-- **Rychkov's extension** `Ext f = ∑_j η_j ⋆ (1_Ω (k_j ⋆ f))`. -/
noncomputable def extension (hp : p ≠ ∞) (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure V) :=
  ∑' j, Ω.extTerm hp L j f

/-- The partial sums of the extension converge to it. -/
theorem tendsto_sum_extTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), Ω.extTerm hp L j f) atTop
      (𝓝 (Ω.extension hp L f)) :=
  ((Ω.summable_extTerm hp L hs hq hf).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-- **The extension agrees with `f` on `Ω`**: `1_Ω Ext f = 1_Ω f`. On `Ω` the terms are those of
the reproducing formula, by the support principle. -/
theorem cutoff_extension (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    Ω.cutoff (Ω.extension hp L f) = Ω.cutoff f := by
  have hsum : ∀ J, Ω.cutoff (∑ j ∈ Finset.range (J + 1), Ω.extTerm hp L j f) =
      Ω.cutoff (∑ j ∈ Finset.range (J + 1),
        convLp hp (Ω.coneBump.integrable_dual L j) (Ω.coneBump.localMean hp L j f)) := fun J => by
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      Ω.cutoff_convLp_cutoff hp _ (Ω.coneSupported_dual L j) _
  have h1 : Tendsto (fun J => Ω.cutoff (∑ j ∈ Finset.range (J + 1), Ω.extTerm hp L j f)) atTop
      (𝓝 (Ω.cutoff (Ω.extension hp L f))) :=
    (Ω.cutoff.continuous.tendsto _).comp (Ω.tendsto_sum_extTerm hp L hs hq hf)
  have h2 : Tendsto (fun J => Ω.cutoff (∑ j ∈ Finset.range (J + 1),
      convLp hp (Ω.coneBump.integrable_dual L j) (Ω.coneBump.localMean hp L j f))) atTop
      (𝓝 (Ω.cutoff f)) :=
    (Ω.cutoff.continuous.tendsto _).comp (Ω.coneBump.tendsto_sum_dual_localMean hp hL f)
  simp_rw [hsum] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The extension satisfies the Besov condition by differences**: for `0 < s < L`,
`‖Ext f‖_p + ‖(2^(is) ω_L(Ext f, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
theorem modNorm_extension_le (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    ‖Ω.extension hp L f‖ₑ +
        lqNorm q (fun i => dyadicWeight s i * lpModulus p L (Ω.extension hp L f) i) ≤
      Ω.coneBump.synthConst L s * Ω.intrinsicNorm hp L s q f :=
  Ω.coneBump.modNorm_le_of_tendsto hp L s hq (Ω.tendsto_sum_extTerm hp L hs hq hf)

/-- **Restrictions of Besov spaces to Lipschitz graph domains**: for `1 ≤ p < ∞`, `0 < s < L` and
`1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F ∈ L_p(V)` with
`‖F‖_p + ‖(2^(ks) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff the intrinsic local means quasi-norm of `f`
is finite; `F = Ext f` is such a function. -/
theorem exists_besov_extension_iff (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (∃ F : Lp ℂ p (volume : Measure V), Ω.cutoff F = Ω.cutoff f ∧
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L F k) < ∞) ↔
      Ω.intrinsicNorm hp L s q f < ∞ := by
  constructor
  · rintro ⟨F, hFf, hF⟩
    rw [← Ω.intrinsicNorm_congr hp L s q hFf]
    exact (Ω.intrinsicNorm_le_localMeansNorm hp L s q F).trans_lt
      ((Ω.coneBump.localMeansNorm_le hp L s hq F).trans_lt
        (ENNReal.mul_lt_top (Ω.coneBump.upperConst_ne_top L s).lt_top hF))
  · intro hf
    exact ⟨Ω.extension hp L f, Ω.cutoff_extension hp hL hs hq hf,
      (Ω.modNorm_extension_le hp L hs hq hf).trans_lt
        (ENNReal.mul_lt_top (Ω.coneBump.synthConst_ne_top hs hsL).lt_top hf)⟩

end LipschitzGraph

end Rd
