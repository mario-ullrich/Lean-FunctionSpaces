/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Differences.DomainModuli
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Moduli of smoothness under linear and affine changes of variables

Let `V` and `W` be finite-dimensional real normed spaces with additive Haar measures `μ` and
`ν`, and let `e : V → W` be a continuous linear map that carries `μ` to `ν`
(`MeasurePreserving e μ ν`), such as the coordinates of an orthonormal basis.

* **Moduli.** Differences commute with additive maps, `Δ_h^r (f ∘ e) = (Δ_{e h}^r f) ∘ e`
  (`Rd.higherDiff_comp_addHom`). Since `‖e h‖ ≤ ‖e‖ ‖h‖` and `e` preserves the measures,
  `ω_r(f ∘ e, t)_{L_p(μ)} ≤ ω_r(f, ‖e‖ t)_{L_p(ν)}` for every `p` (`Rd.modulus_comp_le`), and with
  the dilation of the scale `ω_r(f ∘ e, 2^(-k))_p ≤ (1 + ‖e‖)^r ω_r(f, 2^(-k))_p` on `L_p`,
  `1 ≤ p ≤ ∞` (`Rd.lpModulus_compMeasurePreserving_le`).
* **Moduli on subsets.** The step sets of a preimage are preimages of step sets,
  `(e⁻¹(U))_{rh} = e⁻¹(U_{r(eh)})` (`Rd.stepSet_preimage`), so the same argument gives
  `ω_r(f ∘ e, t, e⁻¹(U))_{L_p(μ)} ≤ ω_r(f, ‖e‖ t, U)_{L_p(ν)}` for the modulus on a measurable
  set `U` (`Rd.modulusOn_comp_le`). For the coordinates `ofLp : ℓ_p^ι → ∏_i β_i` of Mathlib's
  `PiLp`, `‖ofLp‖ ≤ 1` and `‖ofLp⁻¹‖ ≤ (#ι)^(1/p)` (`PiLp.norm_continuousLinearEquiv_le`,
  `PiLp.norm_continuousLinearEquiv_symm_le`); on `ℝ^d` this compares the Euclidean norm with the
  maximum norm.
* **Besov quasi-norms.** Composition with a measure preserving map keeps the `L_p` norm
  (`MeasureTheory.Lp.enorm_compMeasurePreserving`), so the quasi-norm
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}` of `f ∘ e` is at most `(1 + ‖e‖)^r` times that of
  `f` (`Rd.modNorm_compMeasurePreserving_le`). For a continuous linear equivalence the two
  quasi-norms are finite together (`Rd.modNorm_compMeasurePreserving_lt_top_iff`): the Besov
  spaces defined by differences do not depend on the choice of linear coordinates and norm.
* **Affine maps.** Let `n = dim V`, `a ∈ V`, `L > 0` and `A x = a + L x`. Then `A` carries `μ` to
  `L^(-n) μ` (`Rd.measurePreserving_affine`, from Mathlib's `Measure.map_addHaar_smul`), so
  `‖G ∘ A‖_p = L^(-n/p) ‖G‖_p` for every `p`, with `L^(-n/p) = 1` for `p = ∞`
  (`Rd.eLpNorm_comp_affine`). Differences and step sets move along `A` with the step `L h`
  (`Rd.higherDiff_comp_affine`, `Rd.stepSet_preimage_affine`), so
  `ω_r(f ∘ A, t, A⁻¹(U))_p ≤ L^(-n/p) ω_r(f, L t, U)_p` (`Rd.modulusOn_comp_affine_le`).
  Composition with `A` is a bounded operator on `L_p`, `1 ≤ p ≤ ∞` (`Rd.compAffineLp`), with
  two-sided inverse the composition with `A⁻¹ y = -(L⁻¹ a) + L⁻¹ y`
  (`Rd.compAffineLp_inv_compAffineLp`, `Rd.compAffineLp_compAffineLp_inv`).
  The intrinsic quasi-norms of `Rd.modNormOn` satisfy `N_{A⁻¹(U)}(G ∘ A) ≤ C N_U(G)` with `C`
  depending on `L`, `n`, `p`, `r` and `s` (`Rd.exists_modNormOn_compAffineLp_le`): the scale
  `L 2^(-k)` lies below `2^(-(k-m))` for `L < 2^m`, and the shift of `m` levels costs `2^(ms)`
  (`ENNReal.lqNorm_dyadicWeight_le_of_shift`).
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

/-- **The identification of `PiLp p β` with the product has norm at most `1`**: for
`1 ≤ p ≤ ∞` and finitely many normed spaces `β_i`, the coordinates `ofLp : ℓ_p^ι(β) → ∏_i β_i`,
with the maximum norm on the product, satisfy `max_i ‖x_i‖ ≤ ‖x‖_p` (Mathlib's
`PiLp.lipschitzWith_ofLp` and `ContinuousLinearMap.opNorm_le_of_lipschitzWith`). -/
theorem PiLp.norm_continuousLinearEquiv_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] (β : ι → Type*)
    [∀ i, SeminormedAddCommGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] :
    ‖(PiLp.continuousLinearEquiv p 𝕜 β : PiLp p β →L[𝕜] ∀ i, β i)‖ ≤ 1 := by
  have h := ContinuousLinearMap.opNorm_le_of_lipschitzWith
    (f := (PiLp.continuousLinearEquiv p 𝕜 β : PiLp p β →L[𝕜] ∀ i, β i))
    (PiLp.lipschitzWith_ofLp p β)
  simpa using h

/-- **The inverse identification has norm at most `(#ι)^(1/p)`**: for `1 ≤ p ≤ ∞`,
`‖x‖_p ≤ (#ι)^(1/p) max_i ‖x_i‖` for `x` in the product of finitely many normed spaces (Mathlib's
`PiLp.lipschitzWith_toLp`); for the Euclidean space `ℝ^d` this is `‖x‖_2 ≤ √d ‖x‖_∞`. -/
theorem PiLp.norm_continuousLinearEquiv_symm_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] (β : ι → Type*)
    [∀ i, SeminormedAddCommGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] :
    ‖((PiLp.continuousLinearEquiv p 𝕜 β).symm : (∀ i, β i) →L[𝕜] PiLp p β)‖ ≤
      (Fintype.card ι : ℝ) ^ (1 / p).toReal := by
  have h := ContinuousLinearMap.opNorm_le_of_lipschitzWith
    (f := ((PiLp.continuousLinearEquiv p 𝕜 β).symm : (∀ i, β i) →L[𝕜] PiLp p β))
    (PiLp.lipschitzWith_toLp p β)
  simpa using h

namespace Rd

open ENNReal (lqNorm dyadicWeight)
open Module (finrank)

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

omit [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] in
/-- **Step sets under linear maps**: `(e⁻¹(U))_{rh} = e⁻¹(U_{r(eh)})` for every continuous
linear `e : V → W`, every set `U ⊆ W`, order `r` and step `h ∈ V`, since
`e (x + l h) = e x + l (e h)`. -/
theorem stepSet_preimage (e : V →L[ℝ] W) (U : Set W) (r : ℕ) (h : V) :
    stepSet (e ⁻¹' U) r h = e ⁻¹' stepSet U r (e h) := by
  ext x
  simp only [stepSet, Set.mem_preimage, Set.mem_ofPred_eq, map_add, map_smul]

omit [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- **The modulus on a set under a linear change of variables**: let `e : V → W` be continuous,
linear and measure preserving from `μ` to `ν`, and `U ⊆ W` measurable. Then for every
a.e. strongly measurable `f` on `W`, every order `r`, exponent `p` and scale `t`,
`ω_r(f ∘ e, t, e⁻¹(U))_{L_p(μ)} ≤ ω_r(f, ‖e‖ t, U)_{L_p(ν)}`: for `‖h‖ ≤ t` the restricted
difference of `f ∘ e` with step `h` is that of `f` with step `e h`, composed with `e`
(`Rd.stepSet_preimage`, `Rd.higherDiff_comp_addHom`), and `‖e h‖ ≤ ‖e‖ t`. -/
theorem modulusOn_comp_le (e : V →L[ℝ] W) (he : MeasurePreserving e μ ν) {U : Set W}
    (hU : MeasurableSet U) {f : W → ℂ} (hf : AEStronglyMeasurable f ν) (r : ℕ) (p : ℝ≥0∞)
    (t : ℝ) : modulusOn μ (e ⁻¹' U) r p (f ∘ e) t ≤ modulusOn ν U r p f (‖e‖ * t) := by
  refine iSup₂_le fun h hh => ?_
  have hfun : (stepSet (e ⁻¹' U) r h).indicator ((fwdDiff h)^[r] (f ∘ e)) =
      (stepSet U r (e h)).indicator ((fwdDiff (e h))^[r] f) ∘ e := by
    funext x
    rw [stepSet_preimage, higherDiff_comp_addHom, Function.comp_apply, Set.indicator_comp_right]
  rw [hfun, eLpNorm_comp_measurePreserving ((aestronglyMeasurable_higherDiff hf r (e h)).indicator
    (measurableSet_stepSet hU r (e h))) he]
  exact eLpNorm_indicator_higherDiff_le_modulusOn
    ((e.le_opNorm h).trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _)))

/-! ### Affine maps -/

section Affine

variable [FiniteDimensional ℝ V]

/-- **Affine maps carry a Haar measure to a multiple of it**: for `a ∈ V` and `L > 0`, the map
`x ↦ a + L x` carries `μ` to `L^(-n) μ`, `n = dim V`: the dilation by Mathlib's
`MeasureTheory.Measure.map_addHaar_smul`, the translation by the invariance of `L^(-n) μ`
(Mathlib's `MeasureTheory.measurePreserving_add_left`). -/
theorem measurePreserving_affine (a : V) {L : ℝ} (hL : 0 < L) :
    MeasurePreserving (fun x => a + L • x) μ (ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ • μ) := by
  have hsmul : MeasurePreserving (fun x : V => L • x) μ
      (ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ • μ) := by
    refine ⟨measurable_const_smul L, ?_⟩
    rw [Measure.map_addHaar_smul μ hL.ne', abs_of_pos (by positivity)]
  exact (measurePreserving_add_left _ a).comp hsmul

/-- **`L_p` norms under affine maps**: for every exponent `p`, `a ∈ V`, `L > 0` and every
a.e. strongly measurable `G`, `‖G(a + L ·)‖_p = L^(-n/p) ‖G‖_p`, `n = dim V`, where
`L^(-n/p) = 1` for `p = ∞` (`Rd.measurePreserving_affine` and Mathlib's
`MeasureTheory.eLpNorm_smul_measure_of_ne_zero`). -/
theorem eLpNorm_comp_affine {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (a : V) {L : ℝ}
    (hL : 0 < L) {G : V → E} (hG : AEStronglyMeasurable G μ) :
    eLpNorm (fun x => G (a + L • x)) p μ =
      ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ ^ (1 / p).toReal * eLpNorm G p μ := by
  have h := eLpNorm_comp_measurePreserving (p := p) (hG.smul_measure _)
    (measurePreserving_affine (μ := μ) a hL)
  rw [eLpNorm_smul_measure_of_ne_zero
    (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos hL _))).ne' _ _ _, smul_eq_mul] at h
  exact h

/-- **Affine maps keep almost everywhere equality**: if `f = g` almost everywhere, then
`f(a + L ·) = g(a + L ·)` almost everywhere, since `x ↦ a + L x` carries `μ` to a multiple of
`μ` (`Rd.measurePreserving_affine`). -/
theorem ae_eq_comp_affine {E : Type*} (a : V) {L : ℝ} (hL : 0 < L) {f g : V → E}
    (hfg : f =ᵐ[μ] g) : (fun x => f (a + L • x)) =ᵐ[μ] fun x => g (a + L • x) :=
  (measurePreserving_affine a hL).quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure hfg _)

/-- **Affine maps keep `L_p`**: for every exponent `p`, `a ∈ V` and `L > 0`, `G ∈ L_p` implies
`G(a + L ·) ∈ L_p` (`Rd.eLpNorm_comp_affine`). -/
theorem memLp_comp_affine {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (a : V) {L : ℝ}
    (hL : 0 < L) {G : V → E} (hG : MemLp G p μ) :
    MemLp (fun x => G (a + L • x)) p μ := by
  rw [memLp_iff, eLpNorm_comp_affine a hL hG.aestronglyMeasurable]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
    ENNReal.ofReal_ne_top) (memLp_iff.1 hG)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Step sets under affine maps**: for `A x = a + L x`,
`(A⁻¹(U))_{rh} = A⁻¹(U_{r(Lh)})`, since `A (x + l h) = A x + l (L h)`. -/
theorem stepSet_preimage_affine (a : V) (L : ℝ) (U : Set V) (r : ℕ) (h : V) :
    stepSet ((fun x => a + L • x) ⁻¹' U) r h = (fun x => a + L • x) ⁻¹' stepSet U r (L • h) := by
  ext x
  simp only [stepSet, Set.mem_preimage, Set.mem_ofPred_eq, smul_add, smul_comm L, add_assoc]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences under affine maps**: `Δ_h^r (f ∘ A) = (Δ_{Lh}^r f) ∘ A` for `A x = a + L x`,
from the expansion `Δ_h^r f(x) = ∑_{l ≤ r} (-1)^(r-l) C(r, l) f(x + l h)`
(`Rd.higherDiff_apply`) and `A (x + l h) = A x + l (L h)`. -/
theorem higherDiff_comp_affine (a : V) (L : ℝ) (r : ℕ) (h : V) (f : V → ℂ) :
    (fwdDiff h)^[r] (fun x => f (a + L • x)) = fun x => (fwdDiff (L • h))^[r] f (a + L • x) := by
  funext x
  rw [higherDiff_apply, higherDiff_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_add, smul_comm L (l : ℝ) h, add_assoc]

/-- **The modulus on a set under affine maps**: for every exponent `p`, `a ∈ V`, `L > 0`,
`A x = a + L x`, a measurable `U`, an a.e. strongly measurable `f`, every order `r` and scale
`t`, `ω_r(f ∘ A, t, A⁻¹(U))_p ≤ L^(-n/p) ω_r(f, L t, U)_p`, `n = dim V`: the restricted difference
of `f ∘ A` with step `h` is that of `f` with step `L h`, composed with `A`
(`Rd.stepSet_preimage_affine`, `Rd.higherDiff_comp_affine`, `Rd.eLpNorm_comp_affine`), and
`‖L h‖ ≤ L t`. -/
theorem modulusOn_comp_affine_le {p : ℝ≥0∞} (a : V) {L : ℝ} (hL : 0 < L) {U : Set V}
    (hU : MeasurableSet U) {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (r : ℕ) (t : ℝ) :
    modulusOn μ ((fun x => a + L • x) ⁻¹' U) r p (fun x => f (a + L • x)) t ≤
      ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ ^ (1 / p).toReal * modulusOn μ U r p f (L * t) := by
  refine iSup₂_le fun h hh => ?_
  have hfun : (stepSet ((fun x => a + L • x) ⁻¹' U) r h).indicator
      ((fwdDiff h)^[r] (fun x => f (a + L • x))) =
      fun x => (stepSet U r (L • h)).indicator ((fwdDiff (L • h))^[r] f) (a + L • x) := by
    funext x
    rw [stepSet_preimage_affine, higherDiff_comp_affine]
    exact Set.indicator_comp_right (fun x => a + L • x)
  rw [hfun, eLpNorm_comp_affine a hL ((aestronglyMeasurable_higherDiff hf r (L • h)).indicator
    (measurableSet_stepSet hU r (L • h)))]
  refine mul_le_mul' le_rfl (eLpNorm_indicator_higherDiff_le_modulusOn ?_)
  rw [norm_smul, Real.norm_of_nonneg hL.le]
  exact mul_le_mul_of_nonneg_left hh hL.le

end Affine

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

/-! ### Composition with an affine map on `L_p` -/

section AffineLp

variable [FiniteDimensional ℝ V]

/-- **Composition with an affine map on `L_p`**: for `1 ≤ p ≤ ∞`, `a ∈ V` and `L > 0`, the
operator `G ↦ G(a + L ·)` on `L_p(μ)`, of norm at most `L^(-n/p)`, `n = dim V`
(`Rd.eLpNorm_comp_affine`). The map `x ↦ a + L x` carries `μ` to `L^(-n) μ`, so the operator is
built from `MeasureTheory.MemLp.toLp` with an explicit bound; its linearity is Mathlib's
`MeasureTheory.MemLp.toLp_add` and `MeasureTheory.MemLp.toLp_const_smul`. -/
noncomputable def compAffineLp (a : V) {L : ℝ} (hL : 0 < L) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun G => (memLp_comp_affine a hL (Lp.memLp G)).toLp _
      map_add' := fun F G => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (ae_eq_comp_affine a hL (Lp.coeFn_add F G))
      map_smul' := fun c G => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (ae_eq_comp_affine a hL (Lp.coeFn_smul c G)) }
    (ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ ^ (1 / p).toReal).toReal (fun G => by
      change ‖(memLp_comp_affine a hL (Lp.memLp G)).toLp _‖ ≤ _
      rw [Lp.norm_toLp, eLpNorm_comp_affine a hL (Lp.aestronglyMeasurable G),
        ENNReal.toReal_mul, Lp.norm_def])

/-- The composition with an affine map is `G(a + L ·)` almost everywhere. -/
theorem compAffineLp_ae (a : V) {L : ℝ} (hL : 0 < L) (G : Lp ℂ p μ) :
    compAffineLp a hL G =ᵐ[μ] fun x => G (a + L • x) :=
  MemLp.coeFn_toLp (memLp_comp_affine a hL (Lp.memLp G))

/-- **The norm of the composition with an affine map**: `‖G(a + L ·)‖_p = L^(-n/p) ‖G‖_p` in
`[0, ∞]`, `n = dim V` (`Rd.eLpNorm_comp_affine`). -/
theorem enorm_compAffineLp (a : V) {L : ℝ} (hL : 0 < L) (G : Lp ℂ p μ) :
    ‖compAffineLp a hL G‖ₑ = ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ ^ (1 / p).toReal * ‖G‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (compAffineLp_ae a hL G),
    eLpNorm_comp_affine a hL (Lp.aestronglyMeasurable G)]

/-- **The inverse affine map undoes the composition**: the inverse of `A x = a + L x` is
`A⁻¹ y = L⁻¹ (y - a) = -(L⁻¹ a) + L⁻¹ y`, and `(G ∘ A) ∘ A⁻¹ = G` in `L_p`, since
`A (A⁻¹ y) = y`. -/
theorem compAffineLp_inv_compAffineLp (a : V) {L : ℝ} (hL : 0 < L) (G : Lp ℂ p μ) :
    compAffineLp (-(L⁻¹ • a)) (inv_pos.2 hL) (compAffineLp a hL G) = G := by
  refine Lp.ext ?_
  filter_upwards [compAffineLp_ae (-(L⁻¹ • a)) (inv_pos.2 hL) (compAffineLp a hL G),
    ae_eq_comp_affine (-(L⁻¹ • a)) (inv_pos.2 hL) (compAffineLp_ae a hL G)] with x h1 h2
  rw [h1]
  refine h2.trans ?_
  simp only [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hL.ne', one_smul, add_neg_cancel_left]

/-- **The composition undoes the inverse affine map**: for `A x = a + L x` and
`A⁻¹ y = -(L⁻¹ a) + L⁻¹ y`, `(G ∘ A⁻¹) ∘ A = G` in `L_p`, since `A⁻¹ (A x) = x`. -/
theorem compAffineLp_compAffineLp_inv (a : V) {L : ℝ} (hL : 0 < L) (G : Lp ℂ p μ) :
    compAffineLp a hL (compAffineLp (-(L⁻¹ • a)) (inv_pos.2 hL) G) = G := by
  refine Lp.ext ?_
  filter_upwards [compAffineLp_ae a hL (compAffineLp (-(L⁻¹ • a)) (inv_pos.2 hL) G),
    ae_eq_comp_affine a hL (compAffineLp_ae (-(L⁻¹ • a)) (inv_pos.2 hL) G)] with x h1 h2
  rw [h1]
  refine h2.trans ?_
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hL.ne', one_smul, neg_add_cancel_left]

/-- **Dyadic moduli on a set under affine maps**: for `A x = a + L x`, a measurable `U`, every
order `r`, `G ∈ L_p` and `k ∈ ℕ`,
`ω_r(G ∘ A, 2^(-k), A⁻¹(U))_p ≤ L^(-n/p) ω_r(G, L 2^(-k), U)_p` (`Rd.modulusOn_comp_affine_le`
and `Rd.compAffineLp_ae`). -/
theorem lpModulusOn_compAffineLp_le (a : V) {L : ℝ} (hL : 0 < L) {U : Set V}
    (hU : MeasurableSet U) (r : ℕ) (G : Lp ℂ p μ) (k : ℕ) :
    lpModulusOn p ((fun x => a + L • x) ⁻¹' U) r (compAffineLp a hL G) k ≤
      ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ ^ (1 / p).toReal *
        modulusOn μ U r p G (L * (1 / 2 ^ k)) := by
  rw [lpModulusOn, modulusOn_congr_ae (g := fun x => G (a + L • x)) ?_]
  · exact modulusOn_comp_affine_le a hL hU (Lp.aestronglyMeasurable G) r _
  · filter_upwards [compAffineLp_ae a hL G] with x hx
    by_cases h : x ∈ (fun x => a + L • x) ⁻¹' U
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hx]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

/-- **Cut-off norms under affine maps**: for `A x = a + L x` and a measurable `U`,
`‖1_{A⁻¹(U)} (G ∘ A)‖_p = L^(-n/p) ‖1_U G‖_p`, since `1_{A⁻¹(U)} (G ∘ A) = (1_U G) ∘ A`
(`Rd.eLpNorm_comp_affine`). -/
theorem enorm_indicatorLp_compAffineLp (a : V) {L : ℝ} (hL : 0 < L) {U : Set V}
    (hU : MeasurableSet U) (hAU : MeasurableSet ((fun x => a + L • x) ⁻¹' U)) (G : Lp ℂ p μ) :
    ‖indicatorLp hAU (compAffineLp a hL G)‖ₑ =
      ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ ^ (1 / p).toReal * ‖indicatorLp hU G‖ₑ := by
  have h : ((fun x => a + L • x) ⁻¹' U).indicator (compAffineLp a hL G) =ᵐ[μ]
      fun x => U.indicator G (a + L • x) := by
    filter_upwards [compAffineLp_ae a hL G] with x hx
    by_cases h : a + L • x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ (fun x => a + L • x) ⁻¹' U from h),
        Set.indicator_of_mem h, hx]
    · rw [Set.indicator_of_notMem (show x ∉ (fun x => a + L • x) ⁻¹' U from h),
        Set.indicator_of_notMem h]
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hAU _),
    eLpNorm_congr_ae (indicatorLp_apply_ae hU G), eLpNorm_congr_ae h,
    eLpNorm_comp_affine a hL ((Lp.aestronglyMeasurable G).indicator hU)]

/-- **Intrinsic quasi-norms under affine maps**: let `1 ≤ p ≤ ∞`, `a ∈ V`, `L > 0`,
`A x = a + L x`, `U` measurable, `s ≥ 0` and `1 ≤ q ≤ ∞`. Then there is `C < ∞` with
`N_{A⁻¹(U)}(G ∘ A) ≤ C N_U(G)` for every `G ∈ L_p(μ)`, where
`N_U(G) = ‖1_U G‖_p + ‖(2^(ks) ω_r(G, 2^(-k), U)_p)_k‖_{ℓ_q}` (`Rd.modNormOn`). With `n = dim V`
and `L < 2^m`, `C = L^(-n/p) (1 + 2^(ms) (m 2^r + 1))`: the cut-off norms scale by `L^(-n/p)`
(`Rd.enorm_indicatorLp_compAffineLp`), the modulus of `G ∘ A` at level `k + m` is at most
`L^(-n/p)` times that of `G` at level `k` (`Rd.lpModulusOn_compAffineLp_le`), and the first `m`
levels are at most `2^r L^(-n/p) ‖1_U G‖_p` (`Rd.modulusOn_le`); the shift of `m` levels costs
`2^(ms)` (`ENNReal.lqNorm_dyadicWeight_le_of_shift`). The converse bound is this one for the
inverse map (`Rd.compAffineLp_inv_compAffineLp`, `Rd.compAffineLp_compAffineLp_inv`). -/
theorem exists_modNormOn_compAffineLp_le (a : V) {L : ℝ} (hL : 0 < L) {U : Set V}
    (hU : MeasurableSet U) (hAU : MeasurableSet ((fun x => a + L • x) ⁻¹' U)) (r : ℕ) {s : ℝ}
    (hs : 0 ≤ s) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ G : Lp ℂ p μ,
      modNormOn hAU r s q (compAffineLp a hL G) ≤ C * modNormOn hU r s q G := by
  set c := ENNReal.ofReal (L ^ finrank ℝ V)⁻¹ ^ (1 / p).toReal
  have hc : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt L one_lt_two
  refine ⟨c * (1 + dyadicWeight s m * (m * 2 ^ r + 1)),
    ENNReal.mul_ne_top hc (ENNReal.one_add_dyadicWeight_mul_ne_top s m r), fun G => ?_⟩
  set N := modNormOn hU r s q G
  have hIe : eLpNorm (U.indicator G) p μ = ‖indicatorLp hU G‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hU G)]
  have hI : ‖indicatorLp hU G‖ₑ ≤ N := le_self_add
  have hΛ : lqNorm q (fun k => dyadicWeight s k * lpModulusOn p U r G k) ≤ N := le_add_self
  have hlev : ∀ k, L * (1 / 2 ^ (k + m)) ≤ 1 / 2 ^ k := fun k => by
    rw [pow_add, show L * (1 / (2 ^ k * 2 ^ m)) = L / 2 ^ m * (1 / 2 ^ k) by ring]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).2 hm.le)
  have hshift := ENNReal.lqNorm_dyadicWeight_le_of_shift hq hs m
    (a := fun k => lpModulusOn p ((fun x => a + L • x) ⁻¹' U) r (compAffineLp a hL G) k)
    (b := fun k => c * lpModulusOn p U r G k) (B := c * (2 ^ r * ‖indicatorLp hU G‖ₑ))
    (fun k _ => (lpModulusOn_compAffineLp_le a hL hU r G k).trans (mul_le_mul' le_rfl
      ((modulusOn_le (Lp.aestronglyMeasurable G) hU Fact.out r _).trans_eq (by rw [hIe]))))
    (fun k => (lpModulusOn_compAffineLp_le a hL hU r G (k + m)).trans
      (mul_le_mul' le_rfl (modulusOn_mono U r p _ (hlev k))))
  have hcΛ : lqNorm q (fun k => dyadicWeight s k * (c * lpModulusOn p U r G k)) =
      c * lqNorm q (fun k => dyadicWeight s k * lpModulusOn p U r G k) := by
    rw [← ENNReal.lqNorm_const_mul]
    congr 1
    funext k
    ring
  rw [modNormOn, enorm_indicatorLp_compAffineLp a hL hU hAU]
  calc c * ‖indicatorLp hU G‖ₑ + lqNorm q (fun k => dyadicWeight s k *
        lpModulusOn p ((fun x => a + L • x) ⁻¹' U) r (compAffineLp a hL G) k)
      ≤ c * ‖indicatorLp hU G‖ₑ + dyadicWeight s m * (m * (c * (2 ^ r * ‖indicatorLp hU G‖ₑ)) +
          lqNorm q (fun k => dyadicWeight s k * (c * lpModulusOn p U r G k))) :=
        add_le_add le_rfl hshift
    _ = c * ‖indicatorLp hU G‖ₑ + dyadicWeight s m * (m * (c * (2 ^ r * ‖indicatorLp hU G‖ₑ)) +
          c * lqNorm q (fun k => dyadicWeight s k * lpModulusOn p U r G k)) := by
        rw [hcΛ]
    _ ≤ c * N + dyadicWeight s m * (m * (c * (2 ^ r * N)) + c * N) := by gcongr
    _ = c * (1 + dyadicWeight s m * (m * 2 ^ r + 1)) * N := by ring

end AffineLp

end Rd
