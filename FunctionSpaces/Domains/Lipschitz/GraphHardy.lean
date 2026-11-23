/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Lp.HalfLineHardy
public import FunctionSpaces.Analysis.Lp.LintegralForm
public import FunctionSpaces.Domains.Lipschitz.BoundaryLayers
public import FunctionSpaces.Rd.Differences.SobolevSlobodeckij

/-!
# A Hardy inequality on Lipschitz graph domains

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω = {x : φ(x) < ⟪x, e⟫}` a Lipschitz graph domain with Lipschitz constant `M`, and
`η(x) = ⟪x, e⟫ - φ(x)` the height above the graph (`Rd.LipschitzGraph.height`). For `s > 1/2` and
`G ∈ L_2(V)` with `G = 0` almost everywhere on `{x ∈ Ω : η(x) < ε}` for some `ε > 0`, write
`N_{s,Ω}(G) = ‖1_Ω G‖_2 + ‖(2^(ks) ω_1(G, 2^(-k), Ω)_2)_k‖_{ℓ_2}` for the intrinsic `B^s_{2,2}`
quantity of first differences on `Ω` (`Rd.modNormOn`).

* **The Hardy inequality** (`Rd.LipschitzGraph.lintegral_div_min_height_le`,
  `Rd.LipschitzGraph.lintegral_div_min_height_le_modNormOn`,
  `Rd.LipschitzGraph.exists_lintegral_div_height_le`):
  `∫_Ω |G|² / min(η, 1)^(2s) ≤ ∫_Ω |G|² + K_s 2^(2s+2) ∑_k 2^(2ks) ω_1(G, 2^(-k), Ω)_2²
  ≤ (1 + K_s 2^(2s+2)) N_{s,Ω}(G)²`, with `K_s` the constant of the Hardy inequality on `(0, 1]`
  (`Rd.halfLineHardyConst`); the constants depend only on `s`. In the graph coordinates
  `(x', t) ↦ γ(x') + t e`, which preserve the Lebesgue measure
  (`Rd.LipschitzGraph.lintegral_eq_lintegral_graphEquiv`, `Rd.LipschitzGraph.ae_ae_graphEquiv`),
  the left side on `{0 < η ≤ 1}` is an integral over the vertical lines of the Hardy integrals on
  `(0, 1]` (`Rd.lintegral_div_rpow_le_halfLineForm`), whose forms are the integrals of the vertical
  form (`Rd.LipschitzGraph.verticalForm`, `Rd.LipschitzGraph.halfLineForm_graphEquiv`,
  `Rd.LipschitzGraph.lintegral_Ioc_height_le`).
  The substitution `τ = η(x) + r` turns the vertical forms into the vertical difference quotients
  `|G(x + r e) - G(x)|² / |r|^(1+2s)` on the pairs of heights `η(x), η(x) + r ∈ (0, 1]`
  (`Rd.LipschitzGraph.verticalQuotient`, `Rd.LipschitzGraph.lintegral_verticalForm_eq`); these
  pairs lie in the step sets of `Ω`, so Tonelli's theorem and the dyadic shells
  `2^(-k-1) < |r| ≤ 2^(-k)` (`Rd.lintegral_real_le_tsum_dyadicAnnulus`,
  `Rd.LipschitzGraph.lintegral_verticalQuotient_le`) give the moduli on `Ω`
  (`Rd.LipschitzGraph.lintegral_verticalForm_le`). For `1/2 < s < 1` this is a weaker,
  directional form of Dyda's inequality on domains above Lipschitz graphs (Dyda 2004,
  Theorem 1.1, as recorded by Edmunds, Hurri-Syrjänen and Vähäkangas), whose case `p = 2` needs
  `0 < s < 1`.
* **Extension by zero** (`Rd.LipschitzGraph.exists_modNorm_indicatorLp_le_of_vanish`):
  `‖1_Ω G‖_2 + ‖(2^(ks) ω_1(1_Ω G, 2^(-k))_2)_k‖_{ℓ_2} ≤ C N_{s,Ω}(G)`. Pointwise,
  `|Δ_y(1_Ω G)| ≤ 1_{Ω_y} |Δ_y G| + 1_L |G| + (1_L |G|)(· + y)` with the layer
  `L = {0 < η ≤ (1 + M) ‖y‖}` (`Rd.LipschitzGraph.enorm_fwdDiff_indicator_le`,
  `Rd.LipschitzGraph.eLpNorm_fwdDiff_indicator_le`), so the modulus of `1_Ω G` is at most the
  modulus on `Ω` plus twice the `L_2` norm of `G` on a layer
  (`Rd.LipschitzGraph.lpModulus_indicatorLp_le`). The weighted layer norms are bounded by the
  Hardy integral (`Rd.LipschitzGraph.tsum_sq_eLpNorm_layer_le`), through the dyadic decomposition
  of the heights (`MeasureTheory.setLIntegral_preimage_Ioc_le_tsum`) and Hardy's inequality for
  tails (`MeasureTheory.tsum_dyadicWeight_mul_setLIntegral_le`).

The vertical form and the vertical difference quotient of a measurable function are measurable
(`Rd.LipschitzGraph.measurable_verticalForm`, `Rd.LipschitzGraph.measurable_verticalQuotient`),
since the height is continuous (`Rd.LipschitzGraph.continuous_height`).
-/

@[expose] public section

open MeasureTheory Metric Module Set
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V)

/-! ### Graph coordinates -/

/-- **Integrals in graph coordinates**: for measurable `F : V → [0, ∞]`,
`∫_V F = ∫_H ∫_ℝ F(γ(x') + t e) dt dx'`, since the graph coordinates preserve the Lebesgue
measure (`Rd.LipschitzGraph.measurePreserving_graphEquiv`, Mathlib's
`MeasurePreserving.lintegral_comp_emb`) and by Tonelli's theorem (Mathlib's `lintegral_prod`). -/
theorem lintegral_eq_lintegral_graphEquiv {F : V → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ x', ∫⁻ t, F (Ω.graphEquiv (x', t)) := by
  rw [← Ω.measurePreserving_graphEquiv.lintegral_comp_emb Ω.graphEquiv.measurableEmbedding,
    lintegral_prod (fun p => F (Ω.graphEquiv p)) (hF.comp Ω.graphEquiv.measurable).aemeasurable]

/-- **Almost everywhere on the vertical lines**: a property that holds almost everywhere on `V`
holds, for almost every `x' ∈ H`, at `γ(x') + t e` for almost every `t`, since the graph
coordinates preserve the Lebesgue measure (Mathlib's `Measure.ae_ae_of_ae_prod`). -/
theorem ae_ae_graphEquiv {P : V → Prop} (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), ∀ᵐ t ∂(volume : Measure ℝ),
      P (Ω.graphEquiv (x', t)) :=
  Measure.ae_ae_of_ae_prod (Ω.measurePreserving_graphEquiv.quasiMeasurePreserving.ae h)

/-! ### The vertical form -/

/-- The **vertical form** at `x`:
`∫_0^1 |G(x) - G(x + (τ - η(x)) e)|² / |η(x) - τ|^(1+2s) dτ`. In graph coordinates
`x = γ(x') + t e` the points `x + (τ - η(x)) e = γ(x') + τ e` run through the vertical line of
`x'`, so its integral over the heights `t ∈ (0, 1]` is the Gagliardo form on `(0, 1]` of the
Hardy inequality on that line (`Rd.LipschitzGraph.halfLineForm_graphEquiv`). -/
noncomputable def verticalForm (s : ℝ) (G : V → ℂ) (x : V) : ℝ≥0∞ :=
  ∫⁻ τ in Ioc (0 : ℝ) 1,
    ‖G x - G (x + (τ - Ω.height x) • Ω.e)‖ₑ ^ 2 / ‖Ω.height x - τ‖ₑ ^ (1 + 2 * s)

/-- The vertical form of a measurable `G` is measurable (Mathlib's
`Measurable.lintegral_prod_right'`). -/
theorem measurable_verticalForm (s : ℝ) {G : V → ℂ} (hG : Measurable G) :
    Measurable (Ω.verticalForm s G) := by
  have hη := Ω.continuous_height.measurable
  refine Measurable.lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun p : V × ℝ => ‖G p.1 - G (p.1 + (p.2 - Ω.height p.1) • Ω.e)‖ₑ ^ 2 /
      ‖Ω.height p.1 - p.2‖ₑ ^ (1 + 2 * s)) ?_
  refine Measurable.div ?_ ?_
  · refine ((hG.comp measurable_fst).sub (hG.comp ?_)).enorm.pow_const 2
    exact measurable_fst.add (((measurable_snd.sub (hη.comp measurable_fst))).smul_const _)
  · exact ((hη.comp measurable_fst).sub measurable_snd).enorm.pow_const _

/-- **Vertical forms on a line**: on the vertical line of `x' ∈ H`, the Gagliardo form on `(0, 1]`
of `t ↦ G(γ(x') + t e)` is the integral of the vertical form over the heights `t ∈ (0, 1]`, since
`η(γ(x') + t e) = t` (`Rd.LipschitzGraph.height_graphEquiv`). -/
theorem halfLineForm_graphEquiv (s : ℝ) (G : V → ℂ) (x' : Ω.hyperplane) :
    halfLineForm s (fun t => G (Ω.graphEquiv (x', t))) =
      ∫⁻ t in Ioc (0 : ℝ) 1, Ω.verticalForm s G (Ω.graphEquiv (x', t)) := by
  simp only [halfLineForm, verticalForm, Ω.height_graphEquiv]
  refine lintegral_congr fun t => lintegral_congr fun τ => ?_
  rw [Ω.graphEquiv_apply (x', t), Ω.graphEquiv_apply (x', τ), add_assoc, ← add_smul,
    add_sub_cancel]

/-- **The Hardy inequality on `(0, 1]` along the vertical lines**: for `s > 1/2`, a measurable
`G` and `ε > 0` with `G = 0` almost everywhere on `{x ∈ Ω : η(x) < ε}`,
`∫_{0 < η ≤ 1} |G|² η^(-2s) ≤ K_s ∫_{0 < η ≤ 1} (vertical form of G)`. In graph coordinates
(`Rd.LipschitzGraph.lintegral_eq_lintegral_graphEquiv`) the left side is an integral over `x' ∈ H`
of Hardy integrals on `(0, 1]`, `G` vanishes near `0` on almost every line
(`Rd.LipschitzGraph.ae_ae_graphEquiv`), and `Rd.lintegral_div_rpow_le_halfLineForm` with
`Rd.LipschitzGraph.halfLineForm_graphEquiv` applies on each. -/
theorem lintegral_Ioc_height_le {s : ℝ} (hs : 1 / 2 < s) {G : V → ℂ} (hG : Measurable G)
    {ε : ℝ} (hε : 0 < ε) (hG0 : ∀ᵐ x ∂volume, x ∈ Ω.domain → Ω.height x < ε → G x = 0) :
    ∫⁻ x in Ω.height ⁻¹' Ioc 0 1, ‖G x‖ₑ ^ 2 / ENNReal.ofReal (Ω.height x) ^ (2 * s) ≤
      halfLineHardyConst s * ∫⁻ x in Ω.height ⁻¹' Ioc 0 1, Ω.verticalForm s G x := by
  have hη := Ω.continuous_height.measurable
  have hS : MeasurableSet (Ω.height ⁻¹' Ioc (0 : ℝ) 1) := hη measurableSet_Ioc
  have key : ∀ F : V → ℝ≥0∞, Measurable F → ∫⁻ x in Ω.height ⁻¹' Ioc 0 1, F x =
      ∫⁻ x', ∫⁻ t in Ioc (0 : ℝ) 1, F (Ω.graphEquiv (x', t)) := fun F hF => by
    rw [← lintegral_indicator hS, Ω.lintegral_eq_lintegral_graphEquiv (hF.indicator hS)]
    refine lintegral_congr fun x' => ?_
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun t => ?_
    simp only [indicator, mem_preimage, Ω.height_graphEquiv]
  rw [key (fun x => ‖G x‖ₑ ^ 2 / ENNReal.ofReal (Ω.height x) ^ (2 * s))
      ((hG.enorm.pow_const 2).div (hη.ennreal_ofReal.pow_const _)),
    key _ (Ω.measurable_verticalForm s hG),
    ← lintegral_const_mul' _ _ (halfLineHardyConst_ne_top hs)]
  refine lintegral_mono_ae ?_
  filter_upwards [Ω.ae_ae_graphEquiv hG0] with x' hx'
  simp only [Ω.height_graphEquiv]
  rw [← Ω.halfLineForm_graphEquiv]
  refine lintegral_div_rpow_le_halfLineForm hs
    (hG.comp (Ω.graphEquiv.measurable.comp measurable_prodMk_left)) hε ?_
  filter_upwards [hx'] with t ht hti
  have h2 : Ω.height (Ω.graphEquiv (x', t)) = t := Ω.height_graphEquiv (x', t)
  exact ht ((Ω.mem_domain_iff_height_pos _).2 (by rw [h2]; exact hti.1)) (by rw [h2]; exact hti.2)

/-- The **pairs of heights** `{(x, r) : η(x) ∈ (0, 1], η(x) + r ∈ (0, 1]}`: the points `x` of `Ω`
of height at most `1` whose vertical translate `x + r e` is again such a point
(`Rd.LipschitzGraph.height_add_smul`). -/
def heightPairs : Set (V × ℝ) :=
  {p | Ω.height p.1 ∈ Ioc (0 : ℝ) 1 ∧ Ω.height p.1 + p.2 ∈ Ioc (0 : ℝ) 1}

/-- The **vertical difference quotient** `|G(x + r e) - G(x)|² / |r|^(1+2s)` on the pairs of
heights (`Rd.LipschitzGraph.heightPairs`), and `0` elsewhere. -/
noncomputable def verticalQuotient (s : ℝ) (G : V → ℂ) : V × ℝ → ℝ≥0∞ :=
  Ω.heightPairs.indicator fun p => ‖G (p.1 + p.2 • Ω.e) - G p.1‖ₑ ^ 2 / ‖p.2‖ₑ ^ (1 + 2 * s)

/-- The vertical difference quotient of a measurable `G` is measurable. -/
theorem measurable_verticalQuotient (s : ℝ) {G : V → ℂ} (hG : Measurable G) :
    Measurable (Ω.verticalQuotient s G) := by
  have hη := Ω.continuous_height.measurable
  refine Measurable.indicator (Measurable.div ?_ (measurable_snd.enorm.pow_const _))
    ((hη.comp measurable_fst measurableSet_Ioc).inter
      ((hη.comp measurable_fst).add measurable_snd measurableSet_Ioc))
  exact ((hG.comp (measurable_fst.add (measurable_snd.smul_const _))).sub
    (hG.comp measurable_fst)).enorm.pow_const 2

/-- **The vertical forms by vertical differences**: the integral of the vertical form over
`{0 < η ≤ 1}` is `∫_V ∫_ℝ q(x, r) dr dx` with the vertical difference quotient `q`
(`Rd.LipschitzGraph.verticalQuotient`), by the substitution `τ = η(x) + r` in the vertical form
(Mathlib's `lintegral_add_left_eq_self`). -/
theorem lintegral_verticalForm_eq (s : ℝ) (G : V → ℂ) :
    ∫⁻ x in Ω.height ⁻¹' Ioc 0 1, Ω.verticalForm s G x =
      ∫⁻ x, ∫⁻ r, Ω.verticalQuotient s G (x, r) := by
  rw [← lintegral_indicator (Ω.continuous_height.measurable measurableSet_Ioc)]
  refine lintegral_congr fun x => ?_
  by_cases hx : Ω.height x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem (show x ∈ Ω.height ⁻¹' Ioc 0 1 from hx), verticalForm,
      ← lintegral_indicator measurableSet_Ioc, ← lintegral_add_left_eq_self _ (Ω.height x)]
    refine lintegral_congr fun r => ?_
    by_cases hr : Ω.height x + r ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hr]
      simp only [verticalQuotient, indicator_of_mem (show (x, r) ∈ Ω.heightPairs from ⟨hx, hr⟩),
        add_sub_cancel_left, sub_add_cancel_left, enorm_neg]
      rw [enorm_sub_rev]
    · rw [indicator_of_notMem hr]
      exact (indicator_of_notMem (fun h : (x, r) ∈ Ω.heightPairs => hr h.2) _).symm
  · rw [indicator_of_notMem (show x ∉ Ω.height ⁻¹' Ioc 0 1 from hx)]
    refine ((lintegral_congr fun r => ?_).trans lintegral_zero).symm
    exact indicator_of_notMem (fun h : (x, r) ∈ Ω.heightPairs => hx h.1) _

/-- **The vertical differences on a dyadic shell**: for `s ≥ -1/2`, `G ∈ L_2(V)` and
`2^(-k-1) < |r| ≤ 2^(-k)`, `∫_V q(x, r) dx ≤ 2^((k+1)(1+2s)) ω_1(G, 2^(-k), Ω)_2²` for the
vertical difference quotient `q` (`Rd.LipschitzGraph.verticalQuotient`). The pairs of heights lie
in the step set `Ω_{re}` (`Rd.LipschitzGraph.height_add_smul`), `|r|^(-1-2s) ≤ 2^((k+1)(1+2s))`,
and `‖1_{Ω_{re}} Δ_{re} G‖_2 ≤ ω_1(G, 2^(-k), Ω)_2` since `‖r e‖ = |r| ≤ 2^(-k)`
(`Rd.eLpNorm_indicator_higherDiff_le_modulusOn`). -/
theorem lintegral_verticalQuotient_le {s : ℝ} (hs : -(1 / 2) ≤ s)
    (G : Lp ℂ 2 (volume : Measure V)) {k : ℕ} {r : ℝ} (hr : r ∈ dyadicAnnulus (1 : ℝ) k) :
    ∫⁻ x, Ω.verticalQuotient s G (x, r) ≤
      dyadicWeight (1 + 2 * s) (k + 1) * lpModulusOn 2 Ω.domain 1 G k ^ 2 := by
  have hG := (Lp.stronglyMeasurable G).measurable
  have hb : (0 : ℝ) ≤ 1 + 2 * s := by linarith
  have hinv : (‖r‖ₑ ^ (1 + 2 * s))⁻¹ ≤ dyadicWeight (1 + 2 * s) (k + 1) := by
    rw [← inv_inv (dyadicWeight _ (k + 1)), ← ENNReal.dyadicWeight_neg, ENNReal.inv_le_inv,
      ← ENNReal.ofReal_one_div_two_pow_rpow, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hb,
      ← ofReal_norm]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hr.1.le) hb
  have hpt : ∀ x, Ω.verticalQuotient s G (x, r) ≤ ‖(diffStepSet Ω.domain 1 (r • Ω.e)).indicator
      (fwdDiff (r • Ω.e) (G : V → ℂ)) x‖ₑ ^ 2 * dyadicWeight (1 + 2 * s) (k + 1) := fun x => by
    simp only [verticalQuotient]
    by_cases hx : (x, r) ∈ Ω.heightPairs
    · have hst : x ∈ diffStepSet Ω.domain 1 (r • Ω.e) := fun l hl => by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with rfl | rfl
        · simpa [Ω.mem_domain_iff_height_pos] using hx.1.1
        · simpa [Ω.mem_domain_iff_height_pos, Ω.height_add_smul] using hx.2.1
      rw [indicator_of_mem hx, indicator_of_mem hst, div_eq_mul_inv]
      exact mul_le_mul' le_rfl hinv
    · rw [indicator_of_notMem hx]
      exact zero_le
  calc ∫⁻ x, Ω.verticalQuotient s G (x, r) ≤ ∫⁻ x, ‖(diffStepSet Ω.domain 1 (r • Ω.e)).indicator
        (fwdDiff (r • Ω.e) (G : V → ℂ)) x‖ₑ ^ 2 * dyadicWeight (1 + 2 * s) (k + 1) :=
        lintegral_mono hpt
    _ = eLpNorm ((diffStepSet Ω.domain 1 (r • Ω.e)).indicator (fwdDiff (r • Ω.e) (G : V → ℂ)))
          2 volume ^ 2 * dyadicWeight (1 + 2 * s) (k + 1) := by
        rw [lintegral_mul_const' _ _ (ENNReal.dyadicWeight_ne_top _ _),
          lintegral_enorm_sq_eq_eLpNorm_sq]
        exact ((hG.comp (measurable_add_const _)).sub hG).aestronglyMeasurable.indicator
          (measurableSet_diffStepSet Ω.measurableSet_domain 1 _)
    _ ≤ _ := by
        rw [mul_comm]
        refine mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le ?_ 2)
        refine eLpNorm_indicator_higherDiff_le_modulusOn (r := 1) ?_
        rw [norm_smul, Ω.norm_e, mul_one]
        exact hr.2

/-- **The vertical forms by the moduli on `Ω`**: for `s ≥ -1/2` and `G ∈ L_2(V)`,
`∫_{0 < η ≤ 1} (vertical form of G) ≤ 2^(2s+2) ∑_k (2^(ks) ω_1(G, 2^(-k), Ω)_2)²`. The left side
is `∫_V ∫_ℝ q(x, r) dr dx` (`Rd.LipschitzGraph.lintegral_verticalForm_eq`); by Tonelli's theorem
(Mathlib's `lintegral_lintegral_swap`) it is `∫ Q(r) dr` with `Q(r) = ∫_V q(x, r) dx`, which
vanishes at `0` and for `|r| > 1` and is bounded on the dyadic shells
(`Rd.LipschitzGraph.lintegral_verticalQuotient_le`, `Rd.lintegral_real_le_tsum_dyadicAnnulus`).
-/
theorem lintegral_verticalForm_le {s : ℝ} (hs : -(1 / 2) ≤ s) (G : Lp ℂ 2 (volume : Measure V)) :
    ∫⁻ x in Ω.height ⁻¹' Ioc 0 1, Ω.verticalForm s G x ≤
      2 ^ (2 * s + 2) * ∑' k, (dyadicWeight s k * lpModulusOn 2 Ω.domain 1 G k) ^ 2 := by
  have hHm := Ω.measurable_verticalQuotient s (Lp.stronglyMeasurable G).measurable
  rw [Ω.lintegral_verticalForm_eq, lintegral_lintegral_swap
    (f := fun x r => Ω.verticalQuotient s G (x, r)) hHm.aemeasurable]
  refine (lintegral_real_le_tsum_dyadicAnnulus
    (F := fun r => ∫⁻ x, Ω.verticalQuotient s G (x, r))
    (c := fun k => dyadicWeight (1 + 2 * s) (k + 1) * lpModulusOn 2 Ω.domain 1 G k ^ 2) ?_ ?_
    fun k r hr => Ω.lintegral_verticalQuotient_le hs G hr).trans_eq ?_
  · refine (lintegral_congr fun x => ?_).trans lintegral_zero
    simp [verticalQuotient]
  · intro r hr
    refine (lintegral_congr fun x => ?_).trans lintegral_zero
    refine indicator_of_notMem (fun h => ?_) _
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    rcases lt_abs.1 hr with hr | hr <;> linarith
  · rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    have h2 : ∀ x : ℝ, (2 : ℝ≥0∞) * 2 ^ x = 2 ^ (1 + x) := fun x => by
      rw [ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, ENNReal.rpow_one]
    have hw : (2 : ℝ≥0∞) * (dyadicWeight (-1) k * dyadicWeight (1 + 2 * s) (k + 1)) =
        2 ^ (2 * s + 2) * dyadicWeight s k ^ 2 := by
      rw [← ENNReal.rpow_two (dyadicWeight s k), ENNReal.dyadicWeight_rpow]
      simp only [ENNReal.dyadicWeight]
      rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, h2,
        ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      congr 1
      push_cast
      ring
    rw [mul_pow, ← mul_assoc (2 ^ (2 * s + 2) : ℝ≥0∞), ← hw]
    ring

/-! ### The Hardy inequality -/

/-- **The Hardy inequality on a Lipschitz graph domain** (for `1/2 < s < 1` a weaker, directional
form of Dyda 2004, Theorem 1.1, for `p = 2`): for `s > 1/2`, `G ∈ L_2(V)` and `ε > 0` with `G = 0`
almost everywhere on `{x ∈ Ω : η(x) < ε}`,
`∫_Ω |G|² / min(η, 1)^(2s) ≤ ∫_Ω |G|² + K_s 2^(2s+2) ∑_k (2^(ks) ω_1(G, 2^(-k), Ω)_2)²`,
with `K_s` of `Rd.halfLineHardyConst`; the constant depends neither on `ε` nor on `Ω`. On
`{0 < η ≤ 1}` this is `Rd.LipschitzGraph.lintegral_Ioc_height_le` with
`Rd.LipschitzGraph.lintegral_verticalForm_le`; on `{η > 1}` the integrand is `|G|²`. -/
theorem lintegral_div_min_height_le {s : ℝ} (hs : 1 / 2 < s) (G : Lp ℂ 2 (volume : Measure V))
    {ε : ℝ} (hε : 0 < ε) (hG0 : ∀ᵐ x ∂volume, x ∈ Ω.domain → Ω.height x < ε → G x = 0) :
    ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 / ENNReal.ofReal (min (Ω.height x) 1) ^ (2 * s) ≤
      (∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2) + halfLineHardyConst s * 2 ^ (2 * s + 2) *
        ∑' k, (dyadicWeight s k * lpModulusOn 2 Ω.domain 1 G k) ^ 2 := by
  have hG := (Lp.stronglyMeasurable G).measurable
  have hη := Ω.continuous_height.measurable
  set F : V → ℝ≥0∞ := fun x => ‖G x‖ₑ ^ 2 / ENNReal.ofReal (min (Ω.height x) 1) ^ (2 * s)
  have hsub : Ω.domain ⊆ Ω.height ⁻¹' Ioc 0 1 ∪ (Ω.domain ∩ Ω.height ⁻¹' Ioi 1) := fun x hx => by
    by_cases h1 : Ω.height x ≤ 1
    · exact Or.inl ⟨(Ω.mem_domain_iff_height_pos x).1 hx, h1⟩
    · exact Or.inr ⟨hx, not_le.1 h1⟩
  have h1 : ∫⁻ x in Ω.height ⁻¹' Ioc 0 1, F x ≤ halfLineHardyConst s * (2 ^ (2 * s + 2) *
      ∑' k, (dyadicWeight s k * lpModulusOn 2 Ω.domain 1 G k) ^ 2) := by
    rw [setLIntegral_congr_fun (g := fun x => ‖G x‖ₑ ^ 2 / ENNReal.ofReal (Ω.height x) ^ (2 * s))
      (hη measurableSet_Ioc) fun x hx => by
        simp only [F, min_eq_left (show Ω.height x ≤ 1 from hx.2)]]
    exact (Ω.lintegral_Ioc_height_le hs hG hε hG0).trans
      (mul_le_mul' le_rfl (Ω.lintegral_verticalForm_le (by linarith) G))
  have h2 : ∫⁻ x in Ω.domain ∩ Ω.height ⁻¹' Ioi 1, F x ≤ ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 := by
    rw [setLIntegral_congr_fun (g := fun x => ‖G x‖ₑ ^ 2)
      (Ω.measurableSet_domain.inter (hη measurableSet_Ioi)) fun x hx => by
        simp only [F, min_eq_right (show 1 ≤ Ω.height x from (mem_Ioi.1 hx.2).le),
          ENNReal.ofReal_one, ENNReal.one_rpow, div_one]]
    exact lintegral_mono_set inter_subset_left
  calc ∫⁻ x in Ω.domain, F x
      ≤ ∫⁻ x in Ω.height ⁻¹' Ioc 0 1 ∪ (Ω.domain ∩ Ω.height ⁻¹' Ioi 1), F x :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ x in Ω.height ⁻¹' Ioc 0 1, F x) + ∫⁻ x in Ω.domain ∩ Ω.height ⁻¹' Ioi 1, F x :=
        lintegral_union_le F _ _
    _ ≤ halfLineHardyConst s * (2 ^ (2 * s + 2) *
          ∑' k, (dyadicWeight s k * lpModulusOn 2 Ω.domain 1 G k) ^ 2) +
          ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 := add_le_add h1 h2
    _ = _ := by ring

/-- **The Hardy inequality on a Lipschitz graph domain by the intrinsic quasi-norm**: for
`s > 1/2`, `G ∈ L_2(V)` and `ε > 0` with `G = 0` almost everywhere on `{x ∈ Ω : η(x) < ε}`,
`∫_Ω |G|² / min(η, 1)^(2s) ≤ (1 + K_s 2^(2s+2)) N_{s,Ω}(G)²` with `K_s` of
`Rd.halfLineHardyConst` and the intrinsic quasi-norm
`N_{s,Ω}(G) = ‖1_Ω G‖_2 + ‖(2^(ks) ω_1(G, 2^(-k), Ω)_2)_k‖_{ℓ_2}` (`Rd.modNormOn`); the constant
depends neither on `ε` nor on `Ω`. From `Rd.LipschitzGraph.lintegral_div_min_height_le`, since
`∫_Ω |G|² = ‖1_Ω G‖_2²` and the sum is the square of the `ℓ_2` norm in `N_{s,Ω}(G)`. -/
theorem lintegral_div_min_height_le_modNormOn {s : ℝ} (hs : 1 / 2 < s)
    (G : Lp ℂ 2 (volume : Measure V)) {ε : ℝ} (hε : 0 < ε)
    (hG0 : ∀ᵐ x ∂volume, x ∈ Ω.domain → Ω.height x < ε → G x = 0) :
    ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 / ENNReal.ofReal (min (Ω.height x) 1) ^ (2 * s) ≤
      (1 + halfLineHardyConst s * 2 ^ (2 * s + 2)) *
        modNormOn Ω.measurableSet_domain 1 s 2 G ^ 2 := by
  set N := modNormOn Ω.measurableSet_domain 1 s 2 G
  have hI : ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 ≤ N ^ 2 := by
    rw [lintegral_enorm_sq_eq_eLpNorm_sq (Lp.aestronglyMeasurable G).restrict,
      ← eLpNorm_indicator_eq_eLpNorm_restrict Ω.measurableSet_domain.nullMeasurableSet,
      ← eLpNorm_congr_ae (indicatorLp_apply_ae Ω.measurableSet_domain G), ← Lp.enorm_def]
    exact pow_le_pow_left₀ zero_le le_self_add 2
  have hM : ∑' k, (dyadicWeight s k * lpModulusOn 2 Ω.domain 1 G k) ^ 2 ≤ N ^ 2 := by
    rw [← ENNReal.lqNorm_two_sq]
    exact pow_le_pow_left₀ zero_le le_add_self 2
  calc _ ≤ _ := Ω.lintegral_div_min_height_le hs G hε hG0
    _ ≤ N ^ 2 + halfLineHardyConst s * 2 ^ (2 * s + 2) * N ^ 2 :=
        add_le_add hI (mul_le_mul' le_rfl hM)
    _ = (1 + halfLineHardyConst s * 2 ^ (2 * s + 2)) * N ^ 2 := by ring

/-- **The Hardy inequality on a Lipschitz graph domain with a finite constant**: for `s > 1/2`
there is `C < ∞` such that `∫_Ω |G|² / min(η, 1)^(2s) ≤ C N_{s,Ω}(G)²` for every `G ∈ L_2(V)`
that vanishes almost everywhere on `{x ∈ Ω : η(x) < ε}` for some `ε > 0`; the constant
`C = 1 + K_s 2^(2s+2)` of `Rd.LipschitzGraph.lintegral_div_min_height_le_modNormOn` is finite
(`Rd.halfLineHardyConst_ne_top`). -/
theorem exists_lintegral_div_height_le {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ G : Lp ℂ 2 (volume : Measure V),
      (∃ ε > 0, ∀ᵐ x ∂volume, x ∈ Ω.domain → Ω.height x < ε → G x = 0) →
      ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 / ENNReal.ofReal (min (Ω.height x) 1) ^ (2 * s) ≤
        C * modNormOn Ω.measurableSet_domain 1 s 2 G ^ 2 :=
  ⟨1 + halfLineHardyConst s * 2 ^ (2 * s + 2), ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (halfLineHardyConst_ne_top hs) (ENNReal.two_rpow_ne_top _)⟩,
    fun G ⟨_, hε, hG0⟩ => Ω.lintegral_div_min_height_le_modNormOn hs G hε hG0⟩

/-! ### Extension by zero -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences of the extension by zero, pointwise**: for `G : V → ℂ` and steps `y`,
`|Δ_y(1_Ω G)(x)| ≤ |1_{Ω_y} Δ_y G(x)| + |1_L G(x)| + |1_L G(x + y)|` with the layer
`L = {0 < η ≤ (1 + M) ‖y‖}`. If exactly one of `x` and `x + y` lies in `Ω`, that point lies in
`L`, since the height changes sign between them and is `(1 + M)`-Lipschitz
(`Rd.LipschitzGraph.abs_height_le_of_mem_switchSet`). -/
theorem enorm_fwdDiff_indicator_le (G : V → ℂ) (y x : V) :
    ‖fwdDiff y (Ω.domain.indicator G) x‖ₑ ≤
      ‖(diffStepSet Ω.domain 1 y).indicator (fwdDiff y G) x‖ₑ +
        ‖(Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) * ‖y‖)).indicator G x‖ₑ +
        ‖(Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) * ‖y‖)).indicator G (x + y)‖ₑ := by
  simp only [fwdDiff]
  by_cases hx : x ∈ Ω.domain <;> by_cases hxy : x + y ∈ Ω.domain
  · have hst : x ∈ diffStepSet Ω.domain 1 y := fun l hl => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with rfl | rfl
      · simpa using hx
      · simpa using hxy
    rw [indicator_of_mem hx, indicator_of_mem hxy, indicator_of_mem hst]
    exact le_add_right (le_add_right le_rfl)
  · have hL : x ∈ Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) * ‖y‖) :=
      ⟨(Ω.mem_domain_iff_height_pos x).1 hx, (le_abs_self _).trans
        (Ω.abs_height_le_of_mem_switchSet
          (show ¬(x ∈ Ω.domain ↔ x + y ∈ Ω.domain) from fun h => hxy (h.1 hx)))⟩
    rw [indicator_of_mem hx, indicator_of_notMem hxy, indicator_of_mem hL, zero_sub, enorm_neg]
    exact le_add_right le_add_self
  · have hL : x + y ∈ Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) * ‖y‖) := by
      refine ⟨(Ω.mem_domain_iff_height_pos _).1 hxy, (le_abs_self _).trans ?_⟩
      have h := Ω.abs_height_le_of_mem_switchSet (h := -y) (x := x + y)
        (show ¬(x + y ∈ Ω.domain ↔ x + y + -y ∈ Ω.domain) by
          rw [add_neg_cancel_right]
          exact fun h => hx (h.1 hxy))
      rwa [norm_neg] at h
    rw [indicator_of_notMem hx, indicator_of_mem hxy, indicator_of_mem hL, sub_zero]
    exact le_add_left le_rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem hxy, sub_zero, enorm_zero]
    exact zero_le

/-- **Differences of the extension by zero in `L_2`**: for an almost everywhere strongly
measurable `G` and every step `y`,
`‖Δ_y(1_Ω G)‖_2 ≤ ‖1_{Ω_y} Δ_y G‖_2 + 2 ‖1_L G‖_2` with `L = {0 < η ≤ (1 + M) ‖y‖}`, from the
pointwise bound `Rd.LipschitzGraph.enorm_fwdDiff_indicator_le`, Minkowski's inequality and the
translation invariance of the `L_2` norm (Mathlib's `eLpNorm_comp_measurePreserving`). -/
theorem eLpNorm_fwdDiff_indicator_le {G : V → ℂ} (hG : AEStronglyMeasurable G volume) (y : V) :
    eLpNorm (fwdDiff y (Ω.domain.indicator G)) 2 volume ≤
      eLpNorm ((diffStepSet Ω.domain 1 y).indicator (fwdDiff y G)) 2 volume +
        2 * eLpNorm ((Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) * ‖y‖)).indicator G) 2 volume := by
  have hτ := measurePreserving_add_right (volume : Measure V) y
  have hL : MeasurableSet (Ω.height ⁻¹' Ioc (0 : ℝ) ((1 + Ω.M) * ‖y‖)) :=
    Ω.continuous_height.measurable measurableSet_Ioc
  have hGΩ := hG.indicator Ω.measurableSet_domain
  have hfd : AEStronglyMeasurable (fwdDiff y (Ω.domain.indicator G)) volume := by
    unfold fwdDiff
    exact (hGΩ.comp_measurePreserving hτ).sub hGΩ
  have hst : AEStronglyMeasurable ((diffStepSet Ω.domain 1 y).indicator (fwdDiff y G)) volume := by
    unfold fwdDiff
    exact ((hG.comp_measurePreserving hτ).sub hG).indicator
      (measurableSet_diffStepSet Ω.measurableSet_domain 1 y)
  have hLG := hG.indicator hL
  have hpt : ∀ x, ‖fwdDiff y (Ω.domain.indicator G) x‖ₑ ≤
      ‖((fun x => ‖(diffStepSet Ω.domain 1 y).indicator (fwdDiff y G) x‖ₑ) +
        (fun x => ‖(Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) * ‖y‖)).indicator G x‖ₑ) +
        (fun x => ‖(Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) * ‖y‖)).indicator G x‖ₑ) ∘ (· + y)) x‖ₑ :=
    fun x => by
      simp only [Pi.add_apply, Function.comp_apply, enorm_eq_self]
      exact Ω.enorm_fwdDiff_indicator_le G y x
  refine ((eLpNorm_mono_enorm (p := 2) hfd hpt).trans ((eLpNorm_add_le one_le_two).trans
    (add_le_add (eLpNorm_add_le one_le_two) le_rfl))).trans_eq ?_
  rw [eLpNorm_comp_measurePreserving hLG.enorm.aestronglyMeasurable hτ, eLpNorm_enorm _ hst,
    eLpNorm_enorm _ hLG]
  ring

/-- **The modulus of the extension by zero**: for `G ∈ L_2(V)` and `k ∈ ℕ`,
`ω_1(1_Ω G, 2^(-k))_2 ≤ ω_1(G, 2^(-k), Ω)_2 + 2 ‖1_{L_k} G‖_2` with the layer
`L_k = {0 < η ≤ (1 + M) 2^(-k)}`, from `Rd.LipschitzGraph.eLpNorm_fwdDiff_indicator_le` for the
steps `‖y‖ ≤ 2^(-k)`. -/
theorem lpModulus_indicatorLp_le (G : Lp ℂ 2 (volume : Measure V)) (k : ℕ) :
    lpModulus 2 1 (indicatorLp Ω.measurableSet_domain G) k ≤
      lpModulusOn 2 Ω.domain 1 G k +
        2 * eLpNorm ((Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) / 2 ^ k)).indicator G) 2 volume := by
  rw [lpModulus, smoothnessModulus_congr_ae (indicatorLp_apply_ae Ω.measurableSet_domain G)]
  refine iSup₂_le fun y hy => ?_
  refine (Ω.eLpNorm_fwdDiff_indicator_le (Lp.aestronglyMeasurable G) y).trans
    (add_le_add (eLpNorm_indicator_higherDiff_le_modulusOn (r := 1) hy) ?_)
  refine mul_le_mul' le_rfl (eLpNorm_mono ((Lp.aestronglyMeasurable G).indicator
    (Ω.continuous_height.measurable measurableSet_Ioc)) fun x => norm_indicator_le_of_subset
      (preimage_mono (Ioc_subset_Ioc_right ?_)) _ x)
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hy (by linarith [Ω.M_nonneg])

/-- **The weighted layer norms by the Hardy integral**: for `s > 0` and `G ∈ L_2(V)`,
`∑_k (2^(ks) ‖1_{L_k} G‖_2)² ≤ (1 - 2^(-2s))⁻¹ (1 + M)^(2s) ∫_Ω |G|² / min(η, 1)^(2s)` with
`L_k = {0 < η ≤ (1 + M) 2^(-k)}`: `MeasureTheory.tsum_dyadicWeight_mul_setLIntegral_le` for the
height. -/
theorem tsum_sq_eLpNorm_layer_le {s : ℝ} (hs : 0 < s) (G : Lp ℂ 2 (volume : Measure V)) :
    ∑' k, (dyadicWeight s k *
        eLpNorm ((Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) / 2 ^ k)).indicator G) 2 volume) ^ 2 ≤
      (1 - (2 : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * ENNReal.ofReal (1 + Ω.M) ^ (2 * s) *
        ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 / ENNReal.ofReal (min (Ω.height x) 1) ^ (2 * s) := by
  have hη := Ω.continuous_height.measurable
  have hdom : Ω.height ⁻¹' Ioi 0 = Ω.domain := by
    ext x
    exact (Ω.mem_domain_iff_height_pos x).symm
  have h := tsum_dyadicWeight_mul_setLIntegral_le (μ := volume) hη
    (by linarith [Ω.M_nonneg] : (0 : ℝ) < 1 + Ω.M) hs (fun x => ‖G x‖ₑ ^ 2)
  rw [hdom] at h
  refine le_trans (le_of_eq (tsum_congr fun k => ?_)) h
  rw [mul_pow, ← ENNReal.rpow_two (dyadicWeight s k), ENNReal.dyadicWeight_rpow, mul_comm s 2,
    eLpNorm_indicator_eq_eLpNorm_restrict (hη measurableSet_Ioc).nullMeasurableSet,
    ← lintegral_enorm_sq_eq_eLpNorm_sq (Lp.aestronglyMeasurable G).restrict]

/-- **Extension by zero from a Lipschitz graph domain**: for `s > 1/2` there is `C < ∞` such that
for every `G ∈ L_2(V)` that vanishes almost everywhere on `{x ∈ Ω : η(x) < ε}` for some `ε > 0`,
`‖1_Ω G‖_2 + ‖(2^(ks) ω_1(1_Ω G, 2^(-k))_2)_k‖_{ℓ_2} ≤ C N_{s,Ω}(G)` with the intrinsic
quasi-norm `N_{s,Ω}` (`Rd.modNormOn`). The modulus of `1_Ω G` is at most the modulus on `Ω`
plus twice the layer norms (`Rd.LipschitzGraph.lpModulus_indicatorLp_le`), and the weighted layer
norms are at most a multiple of `N_{s,Ω}(G)` by the Hardy inequality
(`Rd.LipschitzGraph.tsum_sq_eLpNorm_layer_le`,
`Rd.LipschitzGraph.exists_lintegral_div_height_le`). -/
theorem exists_modNorm_indicatorLp_le_of_vanish {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ G : Lp ℂ 2 (volume : Measure V),
      (∃ ε > 0, ∀ᵐ x ∂volume, x ∈ Ω.domain → Ω.height x < ε → G x = 0) →
      ‖indicatorLp Ω.measurableSet_domain G‖ₑ + lqNorm 2 (fun k => dyadicWeight s k *
          lpModulus 2 1 (indicatorLp Ω.measurableSet_domain G) k) ≤
        C * modNormOn Ω.measurableSet_domain 1 s 2 G := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_lintegral_div_height_le hs
  set K := (1 - (2 : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * ENNReal.ofReal (1 + Ω.M) ^ (2 * s) * C₁
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith))
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)) hC₁
  refine ⟨1 + 2 * max K 1, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (max_lt hK.lt_top ENNReal.one_lt_top).ne⟩,
    fun G hG => ?_⟩
  set N := modNormOn Ω.measurableSet_domain 1 s 2 G
  set lam : ℕ → ℝ≥0∞ := fun k =>
    eLpNorm ((Ω.height ⁻¹' Ioc 0 ((1 + Ω.M) / 2 ^ k)).indicator G) 2 volume
  have hlam : lqNorm 2 (fun k => dyadicWeight s k * lam k) ≤ max K 1 * N := by
    refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
    rw [ENNReal.lqNorm_two_sq]
    calc ∑' k, (dyadicWeight s k * lam k) ^ 2
        ≤ (1 - (2 : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * ENNReal.ofReal (1 + Ω.M) ^ (2 * s) *
          ∫⁻ x in Ω.domain, ‖G x‖ₑ ^ 2 / ENNReal.ofReal (min (Ω.height x) 1) ^ (2 * s) :=
          Ω.tsum_sq_eLpNorm_layer_le (by linarith) G
      _ ≤ (1 - (2 : ℝ≥0∞) ^ (-(2 * s)))⁻¹ * ENNReal.ofReal (1 + Ω.M) ^ (2 * s) *
          (C₁ * N ^ 2) := mul_le_mul' le_rfl (h₁ G hG)
      _ = K * N ^ 2 := by ring
      _ ≤ (max K 1 * N) ^ 2 := by
          rw [mul_pow, sq (max K 1)]
          exact mul_le_mul' ((le_max_left K 1).trans
            (le_mul_of_one_le_left' (le_max_right K 1))) le_rfl
  calc ‖indicatorLp Ω.measurableSet_domain G‖ₑ + lqNorm 2 (fun k => dyadicWeight s k *
        lpModulus 2 1 (indicatorLp Ω.measurableSet_domain G) k)
      ≤ ‖indicatorLp Ω.measurableSet_domain G‖ₑ + (lqNorm 2 (fun k => dyadicWeight s k *
          lpModulusOn 2 Ω.domain 1 G k) + 2 * lqNorm 2 (fun k => dyadicWeight s k * lam k)) := by
        refine add_le_add le_rfl ?_
        rw [← ENNReal.lqNorm_const_mul]
        refine (ENNReal.lqNorm_mono fun k => ?_).trans (ENNReal.lqNorm_add_le one_le_two _ _)
        refine (mul_le_mul' le_rfl (Ω.lpModulus_indicatorLp_le G k)).trans_eq ?_
        ring
    _ = N + 2 * lqNorm 2 (fun k => dyadicWeight s k * lam k) := by
        simp only [N, modNormOn]
        ring
    _ ≤ N + 2 * (max K 1 * N) := by gcongr
    _ = (1 + 2 * max K 1) * N := by ring

end LipschitzGraph

end Rd
