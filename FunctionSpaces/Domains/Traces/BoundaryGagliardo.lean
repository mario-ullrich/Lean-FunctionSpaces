/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Traces.TraceSpaceNorm
public import FunctionSpaces.Rd.Differences.SobolevSlobodeckij

/-!
# The Sobolev–Slobodeckij norm on the boundary and the Hilbert space `H^t(Γ)`

Let `Ω` be a bounded Lipschitz domain in `V`, `dim V = n`, with boundary `Γ`, surface measure `σ`,
charts `γ_j : H_j → V` and a resolution of unity `(ψ_j)` on `Γ`.

* **The Gagliardo form on `Γ`** (`Rd.BoundedLipschitzDomain.boundarySlobodeckijForm`; Gagliardo
  1957): `∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ(y) dσ(x)`, chart-free. Double integrals
  over a boundary ball are double integrals in the chart
  (`Rd.BoundedLipschitzDomain.lintegral_lintegral_surfaceMeasure_of_support`).
* **The upper bound** (`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`): for
  `1 ≤ p < ∞` and `s > 0` the form is at most `C ‖g‖_{B^s_{p,p}(Γ)}^p` for the chart-wise norm
  (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`). The pieces `ψ_j g` are localised in the balls
  `B_j`, and in the chart the Gagliardo form of `H_j` is bounded by the first-difference norm
  (`Rd.slobodeckijForm_le`).
* **The lower bound** (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`): for
  `0 < s < 1`, `‖g‖_{B^s_{p,p}(Γ)}^p ≤ C (‖g‖_{L_p(Γ)}^p + ∫_Γ ∫_Γ …)`. The Gagliardo form on
  `H_j` of each chart piece `(ψ_j g) ∘ γ_j` is split into a part inside `B_j`, a part with the
  Lipschitz differences of `ψ_j` and a tail
  (`Rd.BoundedLipschitzDomain.slobodeckijForm_chartPiece_le`), and it bounds the first-difference
  norm (`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`).
* **Gagliardo's description of the boundary spaces**: for `g ∈ L_p(Γ)`, `g ∈ B^s_{p,p}(Γ)` iff
  the form is finite
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top`), so
  `W^{s,p}(Γ) = B^s_{p,p}(Γ)`. For `p = 2` and `1/2 < s < 3/2`, the norm of the trace space
  `Ω.TraceSpace s` of `H^s(Ω)` is equivalent to
  `(‖τ_s w‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |τ_s w(y) - τ_s w(x)|² / |y - x|^(n+2s-2) dσ dσ)^(1/2)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`), and the range of
  `τ_s : Ω.TraceSpace s → L_2(Γ)` is the set where the form is finite
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff_slobodeckij`).
* **The Hilbert space `H^t(Γ)`** (`Rd.BoundedLipschitzDomain.BoundarySobolev`), `0 < t < 1`:
  `B^t_{2,2}(Γ)` with the chart-wise Gagliardo norm
  `‖g‖²_{L_2(Γ)} + ∑_j ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t) dy' dx'` of the
  chart pieces `G_j = (ψ_j g) ∘ γ_j`, the norm of the injective linear map
  `g ↦ (g, (G_j(y') - G_j(x'))_j)` into a Hilbert space built from the Gagliardo measures
  `Rd.gagliardoMeasure` on `H_j × H_j` (`Rd.BoundedLipschitzDomain.gagliardoEmbedding`), which
  gives the inner product. It is isomorphic to `B^t_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`), complete, its dual
  `H^{-t}(Γ)` is identified with it by Riesz
  (`Rd.BoundedLipschitzDomain.dualBoundarySobolevEquiv`), and its norm is equivalent to
  Gagliardo's norm with the surface measure
  (`Rd.BoundedLipschitzDomain.exists_boundarySobolev_norm_equiv_slobodeckij`).
* **The trace onto `H^{s-1/2}(Γ)`**, `1/2 < s < 3/2` (McLean, Theorem 3.38): the trace space of
  `H^s(Ω)` is isomorphic to `H^{s-1/2}(Γ)`
  (`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev`; for `s = 1` with values in
  `H^{1/2}(Γ)`, `Rd.BoundedLipschitzDomain.traceSpaceOneEquivBoundarySobolevHalf`); the trace
  `H^s(Ω) → H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.sobolevTrace`) is bounded with kernel
  `ker γ_s` and the bounded linear right inverse `Rd.BoundedLipschitzDomain.sobolevExtend`, and it
  is the Besov trace of `B^s_{2,2}(Ω)` at `p = q = 2`
  (`Rd.BoundedLipschitzDomain.toLp_sobolevTrace_eq_besovTrace`).

The constants depend on `Ω`, `ψ`, `p` and `s` and are fixed before the functions. The results
hold in every dimension `n ≥ 1`; for `n = 1` the hyperplanes are points and `Γ` is finite.
-/

@[expose] public section

open MeasureTheory Filter Metric Module Set
open scoped ENNReal InnerProductSpace BesselPotentialSpace

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Gagliardo integrands and double integrals -/

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

/-- **Points inside and outside two concentric balls are far apart**: for `y ∈ B(c, r)` and
`x ∉ B(c, R)`, `R - r ≤ |y - x|`, by the triangle inequality. -/
theorem sub_le_norm_sub_of_mem_ball {c x y : E} {r R : ℝ} (hy : y ∈ ball c r)
    (hx : x ∉ ball c R) : R - r ≤ ‖y - x‖ := by
  rw [mem_ball] at hy hx
  have h := dist_triangle x y c
  rw [dist_eq_norm x y, norm_sub_rev] at h
  linarith

/-- **The Gagliardo integrand of a function supported in a ball**: if `f` vanishes outside
`B(c, r)` and `r ≤ R`, then for all `x, y`, `P > 0` and `a ≥ 0`,
`|f(y) - f(x)|^P / |y - x|^a ≤ 1_{B(c,R)²}(x, y) |f(y) - f(x)|^P / |y - x|^a +
|f(x)|^P / (R - r)^a + |f(y)|^P / (R - r)^a`. If one point lies outside `B(c, R)`, then `f`
vanishes there, and the other point is at distance at least `R - r` where `f` does not vanish
(`Rd.sub_le_norm_sub_of_mem_ball`). -/
theorem slobodeckijIntegrand_le_of_support {c : E} {r R : ℝ} (hr : r ≤ R) {f : E → ℂ}
    (hf0 : ∀ y, f y ≠ 0 → y ∈ ball c r) {P : ℝ} (hP : 0 < P) {a : ℝ} (ha : 0 ≤ a) (x y : E) :
    ‖f y - f x‖ₑ ^ P / ‖y - x‖ₑ ^ a ≤
      (ball c R ×ˢ ball c R).indicator (fun z : E × E => ‖f z.2 - f z.1‖ₑ ^ P / ‖z.2 - z.1‖ₑ ^ a)
          (x, y) + ‖f x‖ₑ ^ P / ENNReal.ofReal (R - r) ^ a +
        ‖f y‖ₑ ^ P / ENNReal.ofReal (R - r) ^ a := by
  have hfar : ∀ {u v : E}, f u ≠ 0 → v ∉ ball c R →
      ‖f u‖ₑ ^ P / ‖u - v‖ₑ ^ a ≤ ‖f u‖ₑ ^ P / ENNReal.ofReal (R - r) ^ a := fun hu hv => by
    refine ENNReal.div_le_div_left (ENNReal.rpow_le_rpow ?_ ha) _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (sub_le_norm_sub_of_mem_ball (hf0 _ hu) hv)
  have hzero : ∀ {u : E}, u ∉ ball c R → f u = 0 := fun hu =>
    by_contra fun h => hu (ball_subset_ball hr (hf0 _ h))
  by_cases hxy : (x, y) ∈ ball c R ×ˢ ball c R
  · rw [indicator_of_mem hxy, add_assoc]
    exact le_self_add
  rw [indicator_of_notMem hxy, zero_add]
  rcases not_and_or.1 (mem_prod.not.1 hxy) with hx | hy
  · rw [hzero hx, sub_zero]
    by_cases hfy : f y = 0
    · rw [hfy, enorm_zero, ENNReal.zero_rpow_of_pos hP, ENNReal.zero_div]
      exact zero_le
    · exact (hfar hfy hx).trans le_add_self
  · rw [hzero hy, zero_sub, enorm_neg, enorm_sub_rev]
    by_cases hfx : f x = 0
    · rw [hfx, enorm_zero, ENNReal.zero_rpow_of_pos hP, ENNReal.zero_div]
      exact zero_le
    · exact (hfar hfx hy).trans le_self_add

end NormedGroup

/-- **The difference of two products**: `|a b - c d| ≤ |a| |b - d| + |a - c| |d|` for complex
numbers, from `a b - c d = a (b - d) + (a - c) d`. -/
theorem enorm_mul_sub_mul_le (a b c d : ℂ) :
    ‖a * b - c * d‖ₑ ≤ ‖a‖ₑ * ‖b - d‖ₑ + ‖a - c‖ₑ * ‖d‖ₑ := by
  rw [show a * b - c * d = a * (b - d) + (a - c) * d by ring, ← enorm_mul, ← enorm_mul]
  exact enorm_add_le _ _

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : BoundedLipschitzDomain V)

/-! ### The Gagliardo form on the boundary -/

/-- **The Gagliardo form on the boundary** `Γ` of a bounded Lipschitz domain in `V`, `dim V = n`:
`∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n - 1 + sp) dσ(y) dσ(x)` with the surface measure `σ`, for
`0 < p < ∞` the `p`-th power of the Gagliardo seminorm of the Sobolev–Slobodeckij space
`W^{s,p}(Γ)` of the `(n-1)`-dimensional surface `Γ` (Gagliardo 1957). For `p = 2`, `s = 1/2` the
exponent is `n`. -/
noncomputable def boundarySlobodeckijForm (p : ℝ≥0∞) (s : ℝ) (g : V → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ‖g y - g x‖ₑ ^ p.toReal /
    ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure

omit [FiniteDimensional ℝ V] in
/-- The Gagliardo form on the boundary depends only on the class of `g` modulo null sets of the
surface measure. -/
theorem boundarySlobodeckijForm_congr_ae {g h : V → ℂ} (hgh : g =ᵐ[Ω.surfaceMeasure] h)
    (p : ℝ≥0∞) (s : ℝ) : Ω.boundarySlobodeckijForm p s g = Ω.boundarySlobodeckijForm p s h :=
  lintegral_congr_ae (hgh.mono fun x hx => lintegral_congr_ae (hgh.mono fun y hy => by
    simp only [hx, hy]))

/-- **Double integrals over a boundary ball in the chart**: for every `F : V → V → [0, ∞]` that
vanishes unless both points lie in `B_j`,
`∫_Γ ∫_Γ F(x, y) dσ(y) dσ(x) = ∫_{H_j} ∫_{H_j} F(γ_j x', γ_j y') w(y') w(x') dy' dx'` with the
density `w = √(1 + ‖∇φ_j‖²)`, by the chart formula
`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support` twice. It holds for every `F`,
measurable or not. -/
theorem lintegral_lintegral_surfaceMeasure_of_support (j : Fin Ω.N) (F : V → V → ℝ≥0∞)
    (hF : ∀ x y, F x y ≠ 0 →
      x ∈ ball (Ω.center j) (Ω.radius j) ∧ y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫⁻ x, ∫⁻ y, F x y ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure =
      ∫⁻ x', ∫⁻ y', F ((Ω.graph j).graphMap x') ((Ω.graph j).graphMap y') *
        ENNReal.ofReal ((Ω.graph j).gram y') * ENNReal.ofReal ((Ω.graph j).gram x') := by
  have hin : ∀ x, ∫⁻ y, F x y ∂Ω.surfaceMeasure =
      ∫⁻ y', F x ((Ω.graph j).graphMap y') * ENNReal.ofReal ((Ω.graph j).gram y') := fun x =>
    Ω.lintegral_surfaceMeasure_of_support j (F x) fun y hy => (hF x y hy).2
  simp_rw [hin]
  rw [Ω.lintegral_surfaceMeasure_of_support j _ fun x hx => by_contra fun hxB => hx (by
    have h0 : ∀ y, F x y = 0 := fun y => by_contra fun h => hxB (hF x y h).1
    simp only [h0, zero_mul, lintegral_zero])]
  exact lintegral_congr fun x' => (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm

/-- **Double integrals in the chart are at most those over `Γ`**: for every `F : V → V → [0, ∞]`
that vanishes unless both points lie in `B_j`,
`∫_{H_j} ∫_{H_j} F(γ_j x', γ_j y') dy' dx' ≤ ∫_Γ ∫_Γ F dσ dσ`, since the density
`√(1 + ‖∇φ_j‖²)` is at least `1` (`Rd.LipschitzGraph.one_le_ofReal_gram`). -/
theorem lintegral_lintegral_chart_le (j : Fin Ω.N) (F : V → V → ℝ≥0∞)
    (hF : ∀ x y, F x y ≠ 0 →
      x ∈ ball (Ω.center j) (Ω.radius j) ∧ y ∈ ball (Ω.center j) (Ω.radius j)) :
    ∫⁻ x', ∫⁻ y', F ((Ω.graph j).graphMap x') ((Ω.graph j).graphMap y') ≤
      ∫⁻ x, ∫⁻ y, F x y ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure := by
  rw [Ω.lintegral_lintegral_surfaceMeasure_of_support j F hF]
  exact lintegral_mono fun x' => lintegral_mono fun y' =>
    le_mul_of_one_le_right' ((Ω.graph j).one_le_ofReal_gram x') |>.trans'
      (le_mul_of_one_le_right' ((Ω.graph j).one_le_ofReal_gram y'))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The functions of `B^s_{p,q}(Γ)` are measurable on `Γ`**: every `g ∈ B^s_{p,q}(Γ)` is
almost everywhere strongly measurable for the surface measure. On `B_j`, `ψ_j g` is
`σ`-almost everywhere the chart piece `G_j ∈ L_p(H_j)` composed with the projection `P_j`
(`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_ball_iff`), it vanishes outside `B_j`, and
`g = ∑_j ψ_j g` on `Γ`. -/
theorem aestronglyMeasurable_of_memBoundaryBesov (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    {g : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) :
    AEStronglyMeasurable g Ω.surfaceMeasure := by
  choose G hG _ using hg
  have hj : ∀ j, (fun y => ψ.toComplex j y * g y) =ᵐ[Ω.surfaceMeasure]
      (ball (Ω.center j) (Ω.radius j)).indicator fun y => G j ((Ω.graph j).proj y) := by
    intro j
    have h1 := (Ω.ae_surfaceMeasure_ball_iff j (P := fun y => ψ.toComplex j y * g y =
      (ball (Ω.center j) (Ω.radius j)).indicator (fun y => G j ((Ω.graph j).proj y)) y)).2
      ((hG j).mono fun x' hx' hB => by
        rw [indicator_of_mem hB, (Ω.graph j).proj_graphMap, hx'])
    filter_upwards [h1] with y hy
    by_cases hyB : y ∈ ball (Ω.center j) (Ω.radius j)
    · exact hy hyB
    · have hψ : ψ.toFun j y = 0 := by_contra fun h => hyB (ψ.mem_ball_of_ne_zero h)
      rw [ψ.toComplex_of_eq_zero hψ, zero_mul, indicator_of_notMem hyB]
  refine AEStronglyMeasurable.congr (f := fun y => ∑ j, (ball (Ω.center j) (Ω.radius j)).indicator
    (fun y => G j ((Ω.graph j).proj y)) y) (Finset.stronglyMeasurable_fun_sum Finset.univ fun j _ =>
    ((Lp.stronglyMeasurable (G j)).comp_measurable
      (Ω.graph j).proj.continuous.measurable).indicator measurableSet_ball).aestronglyMeasurable ?_
  filter_upwards [ae_all_iff.2 hj, Ω.ae_eq_sum_mul ψ g] with y h1 h2
  rw [h2]
  exact Finset.sum_congr rfl fun j _ => (h1 j).symm

/-- **The Gagliardo form of a finite sum**: for `1 ≤ p < ∞` and measurable `f_i`, the Gagliardo
form on `Γ` of `∑_{i ∈ t} f_i` is at most `(#t)^(p-1)` times the sum of the forms of the `f_i`, by
the triangle inequality and Hölder's inequality for finite sums (Mathlib's
`ENNReal.rpow_sum_le_const_mul_sum_rpow`). -/
theorem boundarySlobodeckijForm_finsetSum_le (hp : p ≠ ∞) (s : ℝ) {ι : Type*} (t : Finset ι)
    {f : ι → V → ℂ} (hf : ∀ i, Measurable (f i)) :
    Ω.boundarySlobodeckijForm p s (fun y => ∑ i ∈ t, f i y) ≤
      (t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, Ω.boundarySlobodeckijForm p s (f i) := by
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  have hc : (t.card : ℝ≥0∞) ^ (p.toReal - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _)
  have hpt : ∀ x y : V, ‖(∑ i ∈ t, f i y) - ∑ i ∈ t, f i x‖ₑ ^ p.toReal /
      ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≤
      (t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, ‖f i y - f i x‖ₑ ^ p.toReal /
        ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) := fun x y => by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i ∈ t, (f i y - f i x)‖ₑ ^ p.toReal /
          ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)
        ≤ ((t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, ‖f i y - f i x‖ₑ ^ p.toReal) /
          ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) :=
          ENNReal.div_le_div_right ((ENNReal.rpow_le_rpow (enorm_sum_le _ _) (by linarith)).trans
            (ENNReal.rpow_sum_le_const_mul_sum_rpow (s := t)
              (f := fun i => ‖f i y - f i x‖ₑ) hP1)) _
      _ = _ := by simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
  have hm := fun i => measurable_slobodeckijIntegrand (hf i) p.toReal
    (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)
  have hy : ∀ i (x : V), Measurable fun y : V => ‖f i y - f i x‖ₑ ^ p.toReal /
      ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) := fun i x =>
    (hm i).comp measurable_prodMk_left
  have hx : ∀ i, Measurable fun x : V => ∫⁻ y, ‖f i y - f i x‖ₑ ^ p.toReal /
      ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ∂Ω.surfaceMeasure := fun i =>
    (hm i).lintegral_prod_right'
  calc Ω.boundarySlobodeckijForm p s (fun y => ∑ i ∈ t, f i y)
      ≤ ∫⁻ x, ∫⁻ y, (t.card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ i ∈ t, ‖f i y - f i x‖ₑ ^ p.toReal /
          ‖y - x‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ∂Ω.surfaceMeasure
            ∂Ω.surfaceMeasure := lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = _ := by
        rw [lintegral_congr fun x => (lintegral_const_mul' _ _ hc).trans (congrArg _
          (lintegral_finsetSum t fun i _ => hy i x)), lintegral_const_mul' _ _ hc,
          lintegral_finsetSum t fun i _ => hx i]
        rfl

/-! ### The upper bound by the chart-wise Besov norm -/

/-- **The part of the Gagliardo form inside one boundary ball**: for every `f : V → ℂ` and
`s ≥ 0`, `∫_Γ ∫_Γ 1_{B_j²}(x, y) |f(y) - f(x)|^p / |y - x|^(n-1+sp) dσ(y) dσ(x)` is at most
`(1 + M_j²)` times the Gagliardo form on `H_j` of `f ∘ γ_j`: the chart formula
(`Rd.BoundedLipschitzDomain.lintegral_lintegral_surfaceMeasure_of_support`), the bound
`√(1 + M_j²)` of the density, and `|y' - x'| ≤ |γ_j y' - γ_j x'|`. -/
theorem lintegral_lintegral_indicator_le_slobodeckijForm (j : Fin Ω.N) (f : V → ℂ) (p : ℝ≥0∞)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ x, ∫⁻ y, (ball (Ω.center j) (Ω.radius j) ×ˢ ball (Ω.center j) (Ω.radius j)).indicator
        (fun z : V × V => ‖f z.2 - f z.1‖ₑ ^ p.toReal /
          ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) (x, y)
        ∂Ω.surfaceMeasure ∂Ω.surfaceMeasure ≤
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ 2 *
        slobodeckijForm p s (fun x' => f ((Ω.graph j).graphMap x')) := by
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hc : ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [Ω.lintegral_lintegral_surfaceMeasure_of_support j _ fun x y h =>
      mem_prod.1 (mem_of_indicator_ne_zero h),
    slobodeckijForm, (Ω.graph j).finrank_hyperplane_eq_sub_one, sq,
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hc hc)]
  refine lintegral_mono fun x' => ?_
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hc hc)]
  refine lintegral_mono fun y' => ?_
  have h1 := (Set.indicator_le_self (ball (Ω.center j) (Ω.radius j) ×ˢ
    ball (Ω.center j) (Ω.radius j)) (fun z : V × V => ‖f z.2 - f z.1‖ₑ ^ p.toReal /
      ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)))
    ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y')
  have h2 := ENNReal.div_le_div_left (ENNReal.rpow_le_rpow
    ((Ω.graph j).enorm_sub_le_enorm_graphMap_sub y' x') ha)
    (‖f ((Ω.graph j).graphMap y') - f ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal)
  calc _ ≤ (‖f ((Ω.graph j).graphMap y') - f ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal /
        ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) *
          ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) :=
        mul_le_mul' (mul_le_mul' (h1.trans h2)
          (ENNReal.ofReal_le_ofReal ((Ω.graph j).gram_le y')))
          (ENNReal.ofReal_le_ofReal ((Ω.graph j).gram_le x'))
    _ = _ := by ring

omit [Fact (1 ≤ p)] in
/-- **The Gagliardo form of a function supported in a boundary ball**: let `f : V → ℂ` be
measurable and vanish outside `B(c_j, r)` with `r < r_j`, the radius of `B_j`. For `0 < p < ∞`
and `s ≥ 0`, `∫_Γ ∫_Γ |f(y) - f(x)|^p / |y - x|^(n-1+sp) dσ dσ` is at most
`(1 + M_j²) [f ∘ γ_j]_{W^{s,p}(H_j)}^p + 2 σ(Γ) (r_j - r)^(-(n-1+sp)) ∫_Γ |f|^p dσ`: the pairs in
`B_j²` go to the chart
(`Rd.BoundedLipschitzDomain.lintegral_lintegral_indicator_le_slobodeckijForm`), the other pairs
are at distance at least `r_j - r` (`Rd.slobodeckijIntegrand_le_of_support`). -/
theorem boundarySlobodeckijForm_le_of_support (j : Fin Ω.N) {r : ℝ} (hr : r < Ω.radius j)
    {f : V → ℂ} (hf : Measurable f) (hf0 : ∀ y, f y ≠ 0 → y ∈ ball (Ω.center j) r)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) {s : ℝ} (hs : 0 ≤ s) :
    Ω.boundarySlobodeckijForm p s f ≤ ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ 2 *
        slobodeckijForm p s (fun x' => f ((Ω.graph j).graphMap x')) +
      2 * Ω.surfaceMeasure univ /
          ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
        ∫⁻ y, ‖f y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure := by
  have hP := ENNReal.toReal_pos hp0 hp
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hm : Measurable fun x : V => ‖f x‖ₑ ^ p.toReal /
      ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) :=
    (hf.enorm.pow_const _).div_const _
  refine (lintegral_lintegral_le_add_two_mul hm fun x y =>
    slobodeckijIntegrand_le_of_support hr.le hf0 hP ha x y).trans
    (add_le_add (Ω.lintegral_lintegral_indicator_le_slobodeckijForm j f p hs) (le_of_eq ?_))
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ (hf.enorm.pow_const _)]
  ring

/-- **The Gagliardo form of one localised piece, by its chart piece**: for `1 ≤ p < ∞`, `s > 0`,
a resolution of unity `ψ` and a chart `j` there is `C < ∞` such that for every measurable `g` and
every `G ∈ L_p(H_j)` with `G = (ψ_j g) ∘ γ_j` almost everywhere,
`[ψ_j g]_{W^{s,p}(Γ)}^p ≤ C (‖G‖_p + ‖(2^(ks) ω_1(G, 2^(-k))_p)_k‖_{ℓ_p})^p`, by
`Rd.BoundedLipschitzDomain.boundarySlobodeckijForm_le_of_support` and the bound of the Gagliardo
form on `H_j` (`Rd.slobodeckijForm_le`). -/
theorem exists_boundarySlobodeckijForm_mul_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Measurable g →
      ∀ G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane),
        (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
          (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) →
        Ω.boundarySlobodeckijForm p s (fun y => ψ.toComplex j y * g y) ≤
          C * (‖G‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport _) (ψ.tsupport_subset j)
  have hf0 : ∀ g : V → ℂ, ∀ y, ψ.toComplex j y * g y ≠ 0 → y ∈ ball (Ω.center j) r :=
    fun g y hy => hsub (subset_tsupport _ fun h =>
      left_ne_zero_of_mul hy (ψ.toComplex_of_eq_zero h))
  have hδ : ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (sub_pos.2 hr)) ENNReal.ofReal_ne_top).ne'
  refine ⟨ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ 2 *
      slobodeckijConstLower (Ω.graph j).hyperplane p s +
    2 * Ω.surfaceMeasure univ /
      ENNReal.ofReal (Ω.radius j - r) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2), ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (slobodeckijConstLower_ne_top hp0 hp hs),
      ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (measure_ne_top _ _)) hδ) ENNReal.ofReal_ne_top⟩, fun g hg G hG => ?_⟩
  have hGP : ‖G‖ₑ ^ p.toReal = ∫⁻ x', ‖ψ.toComplex j ((Ω.graph j).graphMap x') *
      g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal := by
    rw [Lp.enorm_def, eLpNorm_rpow_eq (Lp.aestronglyMeasurable G) hp0 hp]
    exact lintegral_congr_ae (hG.mono fun x' hx' => by dsimp only; rw [hx'])
  have hL : ∫⁻ y, ‖ψ.toComplex j y * g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure ≤
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) * ‖G‖ₑ ^ p.toReal := by
    rw [hGP]
    refine Ω.lintegral_le_chart j _ fun y hy => ball_subset_ball hr.le (hf0 g y fun h => hy ?_)
    rw [h, enorm_zero, ENNReal.zero_rpow_of_pos hP]
  have hS : slobodeckijForm p s (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      g ((Ω.graph j).graphMap x')) ≤ slobodeckijConstLower (Ω.graph j).hyperplane p s *
        (‖G‖ₑ ^ p.toReal +
          lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k) ^ p.toReal) := by
    rw [← slobodeckijForm_congr_ae hG]
    exact slobodeckijForm_le hp hs G
  have hsum := ENNReal.add_rpow_le_rpow_add ‖G‖ₑ
    (lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) hP1
  have hone : ‖G‖ₑ ^ p.toReal ≤
      (‖G‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) ^ p.toReal :=
    ENNReal.rpow_le_rpow le_self_add hP.le
  calc Ω.boundarySlobodeckijForm p s (fun y => ψ.toComplex j y * g y)
      ≤ _ := Ω.boundarySlobodeckijForm_le_of_support j hr
        ((ψ.contDiff_toComplex j).continuous.measurable.mul hg) (hf0 g) hp0 hp hs.le
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (hS.trans (mul_le_mul' le_rfl hsum)))
        (mul_le_mul' le_rfl (hL.trans (mul_le_mul' le_rfl hone)))
    _ = _ := by ring

/-- **The Gagliardo form by the chart-wise Besov norm** (the upper half of Gagliardo's description
of `B^s_{p,p}(Γ)`): for `1 ≤ p < ∞`, `s > 0` and a resolution of unity `ψ` there is `C < ∞` with
`∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ dσ ≤ C ‖g‖_{B^s_{p,p}(Γ)}^p` for every `g`. For
`g ∈ B^s_{p,p}(Γ)`, `g` is measurable on `Γ`
(`Rd.BoundedLipschitzDomain.aestronglyMeasurable_of_memBoundaryBesov`), `g = ∑_j ψ_j g` on `Γ`,
the form of the sum is at most `N^(p-1)` times the sum of the forms
(`Rd.BoundedLipschitzDomain.boundarySlobodeckijForm_finsetSum_le`), and each piece is bounded by
its chart piece (`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_mul_le`); otherwise the
right side is `∞`. -/
theorem exists_boundarySlobodeckijForm_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 < s) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ,
      Ω.boundarySlobodeckijForm p s g ≤ C * Ω.boundaryBesovNorm p ψ s p g ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  choose C hC hle using fun j => Ω.exists_boundarySlobodeckijForm_mul_le ψ j hp hs
  refine ⟨((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ j, C j + 1,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.natCast_ne_top _)) (ENNReal.sum_ne_top.2 fun j _ => hC j), ENNReal.one_ne_top⟩,
    fun g => ?_⟩
  by_cases hg : Ω.MemBoundaryBesov p ψ s p g
  swap
  · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg, ENNReal.top_rpow_of_pos hP,
      ENNReal.mul_top (by positivity)]
    exact le_top
  have hm := Ω.aestronglyMeasurable_of_memBoundaryBesov ψ hg
  have hae := Ω.ae_surfaceMeasure_iff_aeBoundary.1 hm.ae_eq_mk
  have hmk : Measurable (hm.mk g) := hm.stronglyMeasurable_mk.measurable
  rw [Ω.boundarySlobodeckijForm_congr_ae hm.ae_eq_mk, Ω.boundaryBesovNorm_congr ψ hae]
  choose G hG _ using hg.congr hae
  have hpiece : ∀ j, (‖G j‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 (G j) k)) ^
      p.toReal ≤ Ω.boundaryBesovNorm p ψ s p (hm.mk g) ^ p.toReal := fun j => by
    rw [Ω.boundaryBesovNorm_eq_sum ψ G hG]
    exact ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun j =>
      ‖G j‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 (G j) k))
      (fun _ _ => zero_le) (Finset.mem_univ j)) hP.le
  calc Ω.boundarySlobodeckijForm p s (hm.mk g)
      = Ω.boundarySlobodeckijForm p s (fun y => ∑ j, ψ.toComplex j y * hm.mk g y) :=
        Ω.boundarySlobodeckijForm_congr_ae (Ω.ae_eq_sum_mul ψ _) p s
    _ ≤ ((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
          ∑ j, Ω.boundarySlobodeckijForm p s (fun y => ψ.toComplex j y * hm.mk g y) :=
        Ω.boundarySlobodeckijForm_finsetSum_le hp s _ fun j =>
          (ψ.contDiff_toComplex j).continuous.measurable.mul hmk
    _ ≤ ((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
          ∑ j, C j * Ω.boundaryBesovNorm p ψ s p (hm.mk g) ^ p.toReal :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ =>
          (hle j _ hmk (G j) (hG j)).trans (mul_le_mul' le_rfl (hpiece j)))
    _ ≤ _ := by
        rw [← Finset.sum_mul, ← mul_assoc]
        exact mul_le_mul' le_self_add le_rfl

/-! ### The lower bound by the Gagliardo form -/

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The integrand of a chart piece, by the product rule for differences**: for `P ≥ 1`,
`a ≥ 0`, the chart piece `G = (ψ_j g) ∘ γ_j` and all `x', y' ∈ H_j`,
`|G(y') - G(x')|^P / |y' - x'|^a ≤ 2^(P-1) (D_j^P (1 + M_j)^a |g(γ y') - g(γ x')|^P /
|γ y' - γ x'|^a + |g(γ x')|^P |ψ_j(γ y') - ψ_j(γ x')|^P / |y' - x'|^a)`, from
`G(y') - G(x') = ψ_j(γ y') (g(γ y') - g(γ x')) + (ψ_j(γ y') - ψ_j(γ x')) g(γ x')` and
`|γ y' - γ x'| ≤ (1 + M_j) |y' - x'|`. -/
theorem chartPiece_integrand_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {P : ℝ} (hP1 : 1 ≤ P)
    {a : ℝ} (ha : 0 ≤ a) (g : V → ℂ) (x' y' : (Ω.graph j).hyperplane) :
    ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y') -
        ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P /
        ‖y' - x'‖ₑ ^ a ≤
      2 ^ (P - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ P * ENNReal.ofReal (1 + (Ω.graph j).M) ^ a *
          (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P /
            ‖(Ω.graph j).graphMap y' - (Ω.graph j).graphMap x'‖ₑ ^ a) +
        ‖g ((Ω.graph j).graphMap x')‖ₑ ^ P *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') -
            ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a)) := by
  have hP : 0 ≤ P := by linarith
  have hM : 0 < 1 + (Ω.graph j).M := by linarith [(Ω.graph j).M_nonneg]
  have h2 : ‖ψ.toComplex j ((Ω.graph j).graphMap y')‖ₑ ^ P *
      (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a) ≤
      ENNReal.ofReal (ψ.derivBound j) ^ P * ENNReal.ofReal (1 + (Ω.graph j).M) ^ a *
        (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P /
          ‖(Ω.graph j).graphMap y' - (Ω.graph j).graphMap x'‖ₑ ^ a) := by
    rw [mul_assoc]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (ψ.enorm_toComplex_le j _) hP)
      (ENNReal.div_rpow_le_rpow_mul_div_rpow (ENNReal.ofReal_pos.2 hM).ne' ENNReal.ofReal_ne_top
        ((Ω.graph j).enorm_graphMap_sub_le y' x') ha)
  calc _ ≤ 2 ^ (P - 1) * ((‖ψ.toComplex j ((Ω.graph j).graphMap y')‖ₑ *
          ‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ) ^ P +
        (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ *
          ‖g ((Ω.graph j).graphMap x')‖ₑ) ^ P) / ‖y' - x'‖ₑ ^ a :=
        ENNReal.div_le_div_right ((ENNReal.rpow_le_rpow (enorm_mul_sub_mul_le _ _ _ _) hP).trans
          (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hP1)) _
    _ = 2 ^ (P - 1) * (‖ψ.toComplex j ((Ω.graph j).graphMap y')‖ₑ ^ P *
          (‖g ((Ω.graph j).graphMap y') - g ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a) +
        ‖g ((Ω.graph j).graphMap x')‖ₑ ^ P *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
            P / ‖y' - x'‖ₑ ^ a)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hP, ENNReal.mul_rpow_of_nonneg _ _ hP, mul_div_assoc,
          ENNReal.add_div, mul_comm (‖ψ.toComplex j ((Ω.graph j).graphMap y') -
            ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ P), mul_div_assoc, mul_div_assoc]
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add h2 le_rfl)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The integrand of a chart piece, with one point outside the chart ball**: if `ψ_j` vanishes
outside `B(c_j, r)`, `r ≤ r_j`, and `γ_j x' ∉ B_j`, then for the chart piece
`G = (ψ_j g) ∘ γ_j`, `|G(y') - G(x')|^P / |y' - x'|^a ≤ |G(y')|^P 1_{|x' - y'| ≥ η} |x' - y'|^(-a)`
with `η = (r_j - r) / (1 + M_j)`: `G(x') = 0`, and `G(y') ≠ 0` puts `γ_j y'` in `B(c_j, r)`, at
distance at least `r_j - r` from `γ_j x'`. -/
theorem chartPiece_integrand_le_of_notMem (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {r : ℝ}
    (hr : r ≤ Ω.radius j) (hsub : ∀ y, ψ.toFun j y ≠ 0 → y ∈ ball (Ω.center j) r) {P : ℝ}
    (hP : 0 < P) (a : ℝ) (g : V → ℂ) {x' y' : (Ω.graph j).hyperplane}
    (hx : (Ω.graph j).graphMap x' ∉ ball (Ω.center j) (Ω.radius j)) :
    ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y') -
        ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P /
        ‖y' - x'‖ₑ ^ a ≤
      ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y')‖ₑ ^ P *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-a)) (x' - y') := by
  have hφx : ψ.toComplex j ((Ω.graph j).graphMap x') = 0 :=
    ψ.toComplex_of_eq_zero (by_contra fun h => hx (ball_subset_ball hr (hsub _ h)))
  rw [hφx, zero_mul, sub_zero]
  by_cases hφy : ψ.toFun j ((Ω.graph j).graphMap y') = 0
  · rw [ψ.toComplex_of_eq_zero hφy, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hP,
      ENNReal.zero_div, zero_mul]
  have hfar := sub_le_norm_sub_of_mem_ball (hsub _ hφy) hx
  have hlip := (Ω.graph j).norm_graphMap_sub_le y' x'
  have hM : 0 < 1 + (Ω.graph j).M := by linarith [(Ω.graph j).M_nonneg]
  have hη : (Ω.radius j - r) / (1 + (Ω.graph j).M) ≤ ‖x' - y'‖ := by
    rw [div_le_iff₀ hM, norm_sub_rev]
    linarith
  rw [indicator_of_mem (by simpa [mem_ball_zero_iff] using hη), ENNReal.rpow_neg,
    ← div_eq_mul_inv, enorm_sub_rev x' y']

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The integrand of a chart piece, bounded by four parts**: if `ψ_j` vanishes outside
`B(c_j, r)` with `r ≤ r_j`, then for `P ≥ 1`, `a ≥ 0`, the chart piece `G = (ψ_j g) ∘ γ_j` and all
`x', y' ∈ H_j`, `|G(y') - G(x')|^P / |y' - x'|^a` is at most
`2^(P-1) (A(x', y') + B(x', y')) + |G(x')|^P k(y' - x') + |G(y')|^P k(x' - y')` with the kernel
`k(z) = 1_{|z| ≥ η} |z|^(-a)`, `η = (r_j - r) / (1 + M_j)`, the part
`A = D_j^P (1 + M_j)^a 1_{B_j²}(γ x', γ y') |g(γ y') - g(γ x')|^P / |γ y' - γ x'|^a` and the part
`B = 1_{B_j}(γ x') |g(γ x')|^P |ψ_j(γ y') - ψ_j(γ x')|^P / |y' - x'|^a`
(`Rd.BoundedLipschitzDomain.chartPiece_integrand_le`,
`Rd.BoundedLipschitzDomain.chartPiece_integrand_le_of_notMem`). -/
theorem chartPiece_integrand_le_add (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {r : ℝ}
    (hr : r ≤ Ω.radius j) (hsub : ∀ y, ψ.toFun j y ≠ 0 → y ∈ ball (Ω.center j) r) {P : ℝ}
    (hP1 : 1 ≤ P) {a : ℝ} (ha : 0 ≤ a) (g : V → ℂ) (x' y' : (Ω.graph j).hyperplane) :
    ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y') -
        ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P /
        ‖y' - x'‖ₑ ^ a ≤
      2 ^ (P - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ P * ENNReal.ofReal (1 + (Ω.graph j).M) ^ a *
          (ball (Ω.center j) (Ω.radius j) ×ˢ ball (Ω.center j) (Ω.radius j)).indicator
            (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ P / ‖z.2 - z.1‖ₑ ^ a)
            ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y') +
        (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ P) ((Ω.graph j).graphMap x') *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') -
            ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ P / ‖y' - x'‖ₑ ^ a)) +
      ‖ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-a)) (y' - x') +
      ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y')‖ₑ ^ P *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-a)) (x' - y') := by
  have hP : 0 < P := by linarith
  by_cases hx : (Ω.graph j).graphMap x' ∈ ball (Ω.center j) (Ω.radius j)
  · by_cases hy : (Ω.graph j).graphMap y' ∈ ball (Ω.center j) (Ω.radius j)
    · rw [indicator_of_mem (mk_mem_prod hx hy), indicator_of_mem hx]
      exact (Ω.chartPiece_integrand_le ψ j hP1 ha g x' y').trans (le_self_add.trans le_self_add)
    · have h := Ω.chartPiece_integrand_le_of_notMem ψ j hr hsub hP a g (x' := y') (y' := x') hy
      rw [enorm_sub_rev, enorm_sub_rev x' y'] at h
      exact h.trans (le_add_right le_add_self)
  · exact (Ω.chartPiece_integrand_le_of_notMem ψ j hr hsub hP a g hx).trans le_add_self

/-- **The inside part of a chart piece**: for every `g`,
`∫_{H_j} ∫_{H_j} 1_{B_j²}(γ x', γ y') |g(γ y') - g(γ x')|^p / |γ y' - γ x'|^(n-1+sp) dy' dx'` is at
most the Gagliardo form of `g` on `Γ` (`Rd.BoundedLipschitzDomain.lintegral_lintegral_chart_le`). -/
theorem lintegral_lintegral_inside_le (j : Fin Ω.N) (g : V → ℂ) (p : ℝ≥0∞) (s : ℝ) :
    ∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j) ×ˢ ball (Ω.center j) (Ω.radius j)).indicator
        (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ p.toReal /
          ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))
        ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y') ≤
      Ω.boundarySlobodeckijForm p s g :=
  (Ω.lintegral_lintegral_chart_le j (fun x y => (ball (Ω.center j) (Ω.radius j) ×ˢ
    ball (Ω.center j) (Ω.radius j)).indicator (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ p.toReal /
      ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) (x, y))
    fun _ _ h => mem_prod.1 (mem_of_indicator_ne_zero h)).trans
    (lintegral_mono fun x => lintegral_mono fun y => Set.indicator_le_self _ _ (x, y))

/-- The constant `(D_j (1 + M_j))^p c_1 + (2 D_j)^p c_2` of the Lipschitz part of a chart piece,
with `c_1 = Rd.ballRpowConst H_j (n - 1 + sp - p)`, `c_2 = Rd.complBallRpowConst H_j (n - 1 + sp)`
and the derivative bound `D_j = ψ.derivBound j`. -/
noncomputable def chartLipschitzConst (p : ℝ≥0∞) (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (s : ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (ψ.derivBound j * (1 + (Ω.graph j).M)) ^ p.toReal *
      ballRpowConst (Ω.graph j).hyperplane
        (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal - p.toReal) +
    ENNReal.ofReal (2 * ψ.derivBound j) ^ p.toReal *
      complBallRpowConst (Ω.graph j).hyperplane (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.BoundedLipschitzDomain.chartLipschitzConst` is finite for `0 < p < ∞` and
`0 < s < 1`. -/
theorem chartLipschitzConst_ne_top (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) : Ω.chartLipschitzConst p ψ j s ≠ ∞ := by
  have hP := ENNReal.toReal_pos hp0 hp
  have hm := (Ω.graph j).finrank_hyperplane_eq_sub_one
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hP.le
    ENNReal.ofReal_ne_top) (ballRpowConst_ne_top ?_), ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top) (complBallRpowConst_ne_top ?_)⟩
  · rw [hm]
    nlinarith
  · rw [hm]
    nlinarith

omit [Fact (1 ≤ p)] in
/-- **The Lipschitz part of a chart piece**: for `0 < p < ∞` and `0 < s < 1`,
`∫_{H_j} ∫_{H_j} 1_{B_j}(γ x') |g(γ x')|^p |ψ_j(γ y') - ψ_j(γ x')|^p / |y' - x'|^(n-1+sp) dy' dx'`
is at most `K ∫_Γ |g|^p dσ` with `K = Rd.BoundedLipschitzDomain.chartLipschitzConst p ψ j s`: the
inner integral is at most `K` (`Rd.lintegral_rpow_div_norm_rpow_le`, with
`|ψ_j(γ y') - ψ_j(γ x')| ≤ min(D_j (1 + M_j) |y' - x'|, 2 D_j)`). -/
theorem lintegral_lintegral_lipschitz_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (g : V → ℂ) :
    ∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') *
        (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
          p.toReal / ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) ≤
      Ω.chartLipschitzConst p ψ j s * ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure := by
  have hP := ENNReal.toReal_pos hp0 hp
  have hm := (Ω.graph j).finrank_hyperplane_eq_sub_one
  have hφγ : Continuous fun y' => ψ.toComplex j ((Ω.graph j).graphMap y') :=
    (ψ.contDiff_toComplex j).continuous.comp (Ω.graph j).continuous_graphMap
  have hin : ∀ x', ∫⁻ y', ‖ψ.toComplex j ((Ω.graph j).graphMap y') -
      ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal /
        ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≤
      Ω.chartLipschitzConst p ψ j s := fun x' => by
    rw [← lintegral_add_right_eq_self _ x']
    simp only [add_sub_cancel_right]
    refine lintegral_rpow_div_norm_rpow_le (fun z => ?_) (fun z => ?_) hP ?_ ?_
    · refine (ψ.enorm_toComplex_sub_le j _ _).trans ?_
      rw [ENNReal.ofReal_mul (norm_nonneg _ |>.trans (norm_le_of_iteratedFDeriv_le
        (ψ.derivBound_spec j) 0)), mul_assoc]
      refine mul_le_mul' le_rfl ((Ω.graph j).enorm_graphMap_sub_le (z + x') x' |>.trans ?_)
      rw [add_sub_cancel_right]
    · refine enorm_sub_le.trans ?_
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, two_mul]
      exact add_le_add (ψ.enorm_toComplex_le j _) (ψ.enorm_toComplex_le j _)
    · rw [hm]
      nlinarith
    · rw [hm]
      nlinarith
  have hK : Ω.chartLipschitzConst p ψ j s ≠ ∞ := Ω.chartLipschitzConst_ne_top ψ j hp0 hp hs hs1
  calc _ = ∫⁻ x', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') * ∫⁻ y', ‖ψ.toComplex j ((Ω.graph j).graphMap y') -
          ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal /
            ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) :=
        lintegral_congr fun x' => lintegral_const_mul _ (((hφγ.measurable.sub
          measurable_const).enorm.pow_const _).div
            ((measurable_id.sub measurable_const).enorm.pow_const _))
    _ ≤ ∫⁻ x', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') * Ω.chartLipschitzConst p ψ j s :=
        lintegral_mono fun x' => mul_le_mul' le_rfl (hin x')
    _ ≤ (∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure) * Ω.chartLipschitzConst p ψ j s := by
        rw [lintegral_mul_const' _ _ hK]
        exact mul_le_mul' ((Ω.lintegral_chart_le j _ fun _ h => mem_of_indicator_ne_zero h).trans
          (lintegral_mono (Set.indicator_le_self _ _))) le_rfl
    _ = _ := mul_comm _ _

/-- **The Gagliardo form of a chart piece, split into its parts**: if `ψ_j` vanishes outside
`B(c_j, r)` with `r ≤ r_j` and `g` is measurable, then for `1 ≤ p < ∞` and `s ≥ 0` the Gagliardo
form on `H_j` of `G = (ψ_j g) ∘ γ_j` is at most `2^(p-1) (∫∫ A + ∫∫ B) + 2 ∫∫ |G(x')|^p k(y' - x')`
for the parts of `Rd.BoundedLipschitzDomain.chartPiece_integrand_le_add`; the last part appears
twice by Tonelli's theorem. -/
theorem slobodeckijForm_chartPiece_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {r : ℝ}
    (hr : r ≤ Ω.radius j) (hsub : ∀ y, ψ.toFun j y ≠ 0 → y ∈ ball (Ω.center j) r) (hp : p ≠ ∞)
    {s : ℝ} (hs : 0 ≤ s) {g : V → ℂ} (hg : Measurable g) :
    slobodeckijForm p s (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
        g ((Ω.graph j).graphMap x')) ≤
      2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
          ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
          (∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j) ×ˢ
              ball (Ω.center j) (Ω.radius j)).indicator
            (fun z : V × V => ‖g z.2 - g z.1‖ₑ ^ p.toReal /
              ‖z.2 - z.1‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))
            ((Ω.graph j).graphMap x', (Ω.graph j).graphMap y')) +
        ∫⁻ x', ∫⁻ y', (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
            ((Ω.graph j).graphMap x') *
          (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
            p.toReal / ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) +
      2 * ∫⁻ x', ∫⁻ y', ‖ψ.toComplex j ((Ω.graph j).graphMap x') *
          g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) (y' - x') := by
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hγ := (Ω.graph j).continuous_graphMap.measurable
  have hφγ : Measurable fun y' => ψ.toComplex j ((Ω.graph j).graphMap y') :=
    (ψ.contDiff_toComplex j).continuous.measurable.comp hγ
  have hG : Measurable fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      g ((Ω.graph j).graphMap x') := hφγ.mul (hg.comp hγ)
  have hk : Measurable ((ball (0 : (Ω.graph j).hyperplane)
      ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
        fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) :=
    (measurable_enorm.pow_const _).indicator measurableSet_ball.compl
  have hT : Measurable (Function.uncurry fun x' y' : (Ω.graph j).hyperplane =>
      ‖ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) (y' - x')) :=
    ((hG.comp measurable_fst).enorm.pow_const p.toReal).mul
      (hk.comp (measurable_snd.sub measurable_fst))
  have hT' : Measurable (Function.uncurry fun x' y' : (Ω.graph j).hyperplane =>
      ‖ψ.toComplex j ((Ω.graph j).graphMap y') * g ((Ω.graph j).graphMap y')‖ₑ ^ p.toReal *
        (ball (0 : (Ω.graph j).hyperplane) ((Ω.radius j - r) / (1 + (Ω.graph j).M)))ᶜ.indicator
          (fun z => ‖z‖ₑ ^ (-(((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) (x' - y')) :=
    ((hG.comp measurable_snd).enorm.pow_const p.toReal).mul
      (hk.comp (measurable_fst.sub measurable_snd))
  have hB : Measurable (Function.uncurry fun x' y' : (Ω.graph j).hyperplane =>
      (ball (Ω.center j) (Ω.radius j)).indicator (fun y => ‖g y‖ₑ ^ p.toReal)
        ((Ω.graph j).graphMap x') *
        (‖ψ.toComplex j ((Ω.graph j).graphMap y') - ψ.toComplex j ((Ω.graph j).graphMap x')‖ₑ ^
          p.toReal / ‖y' - x'‖ₑ ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) :=
    ((((hg.enorm.pow_const p.toReal).indicator measurableSet_ball).comp hγ).comp
      measurable_fst).mul ((((hφγ.comp measurable_snd).sub
        (hφγ.comp measurable_fst)).enorm.pow_const p.toReal).div
          ((measurable_snd.sub measurable_fst).enorm.pow_const _))
  rw [slobodeckijForm, (Ω.graph j).finrank_hyperplane_eq_sub_one]
  refine (lintegral_mono fun x' => lintegral_mono fun y' =>
    Ω.chartPiece_integrand_le_add ψ j hr hsub hP1 ha g x' y').trans (le_of_eq ?_)
  rw [lintegral_lintegral_add_right _ hT', lintegral_lintegral_add_right _ hT,
    lintegral_lintegral_swap hT'.aemeasurable,
    lintegral_lintegral_const_mul' (ENNReal.two_rpow_ne_top _), lintegral_lintegral_add_right _ hB,
    lintegral_lintegral_const_mul' (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg ha ENNReal.ofReal_ne_top)), add_assoc, ← two_mul]

/-- **The Gagliardo form of a chart piece by the form on `Γ`**: for `1 ≤ p < ∞`, `0 < s < 1`, a
resolution of unity `ψ` and a chart `j` there is `K < ∞` such that for every measurable `g` the
Gagliardo form on `H_j` of `G = (ψ_j g) ∘ γ_j` is at most
`K (∫_Γ |g|^p dσ + ∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ dσ)`. The parts of
`Rd.BoundedLipschitzDomain.slobodeckijForm_chartPiece_le` are bounded by
`Rd.BoundedLipschitzDomain.lintegral_lintegral_inside_le`,
`Rd.BoundedLipschitzDomain.lintegral_lintegral_lipschitz_le`,
`Rd.lintegral_lintegral_mul_indicator_le` and
`Rd.BoundedLipschitzDomain.lintegral_chartPiece_le`. -/
theorem exists_slobodeckijForm_chartPiece_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : V → ℂ, Measurable g →
      slobodeckijForm p s (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
          g ((Ω.graph j).graphMap x')) ≤
        K * (∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure + Ω.boundarySlobodeckijForm p s g) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  have ha : 0 ≤ ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by positivity
  have hM : 0 < 1 + (Ω.graph j).M := by linarith [(Ω.graph j).M_nonneg]
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball (isClosed_tsupport _) (ψ.tsupport_subset j)
  have hη : 0 < (Ω.radius j - r) / (1 + (Ω.graph j).M) := div_pos (sub_pos.2 hr) hM
  have hma : (finrank ℝ (Ω.graph j).hyperplane : ℝ) <
      ((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal := by
    rw [(Ω.graph j).finrank_hyperplane_eq_sub_one]
    exact lt_add_of_pos_right _ (mul_pos hs hP)
  have h2 : (2 : ℝ≥0∞) ^ (p.toReal - 1) ≠ ∞ :=
    ENNReal.two_rpow_ne_top _
  have hD : ENNReal.ofReal (ψ.derivBound j) ^ p.toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg ha ENNReal.ofReal_ne_top
  have hI : complBallRpowConst (Ω.graph j).hyperplane
      (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
      ENNReal.ofReal ((Ω.radius j - r) / (1 + (Ω.graph j).M)) ^
        ((finrank ℝ (Ω.graph j).hyperplane : ℝ) -
          (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) ≠ ∞ :=
    ENNReal.mul_ne_top (complBallRpowConst_ne_top hma)
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.2 hη).ne' ENNReal.ofReal_ne_top)
  refine ⟨2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
      ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) +
    2 ^ (p.toReal - 1) * Ω.chartLipschitzConst p ψ j s +
    2 * (complBallRpowConst (Ω.graph j).hyperplane (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
      ENNReal.ofReal ((Ω.radius j - r) / (1 + (Ω.graph j).M)) ^
        ((finrank ℝ (Ω.graph j).hyperplane : ℝ) - (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal))) *
      ENNReal.ofReal (ψ.derivBound j) ^ p.toReal,
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top h2 (ENNReal.mul_ne_top hD hc),
      ENNReal.mul_ne_top h2 (Ω.chartLipschitzConst_ne_top ψ j hp0 hp hs hs1)⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hI) hD⟩, fun g hg => ?_⟩
  have hT := (lintegral_lintegral_mul_indicator_le (fun x' => ‖ψ.toComplex j
    ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal) hη hma).trans
    (mul_le_mul' le_rfl (Ω.lintegral_chartPiece_le ψ j hP g))
  refine (Ω.slobodeckijForm_chartPiece_le ψ j hr.le (fun y hy => hsub (subset_tsupport _ hy)) hp
    hs.le hg).trans ?_
  calc _ ≤ 2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
          ENNReal.ofReal (1 + (Ω.graph j).M) ^ (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
          Ω.boundarySlobodeckijForm p s g +
        Ω.chartLipschitzConst p ψ j s * ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure) +
      2 * (complBallRpowConst (Ω.graph j).hyperplane
          (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal) *
        ENNReal.ofReal ((Ω.radius j - r) / (1 + (Ω.graph j).M)) ^
          ((finrank ℝ (Ω.graph j).hyperplane : ℝ) -
            (((finrank ℝ V - 1 : ℕ) : ℝ) + s * p.toReal)) *
        (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
          ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure)) :=
        add_le_add (mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (Ω.lintegral_lintegral_inside_le j g p s))
          (Ω.lintegral_lintegral_lipschitz_le ψ j hp0 hp hs hs1 g))) (mul_le_mul' le_rfl hT)
    _ ≤ _ := (le_of_eq (by ring)).trans (ENNReal.mul_add_mul_add_mul_le _ _ _ _ _)

/-- **The chart-wise Besov norm by the Gagliardo form** (the lower half of Gagliardo's description
of `B^s_{p,p}(Γ)`): for `1 ≤ p < ∞`, `0 < s < 1` and a resolution of unity `ψ` there is `C < ∞`
with `‖g‖_{B^s_{p,p}(Γ)}^p ≤ C (‖g‖_{L_p(Γ)}^p + ∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ dσ)`
for every `g` measurable on `Γ`. If `g ∈ L_p(Γ)`, every chart piece `G_j = (ψ_j g) ∘ γ_j` lies in
`L_p(H_j)` (`Rd.BoundedLipschitzDomain.lintegral_chartPiece_le`), its first-difference norm is
bounded by its Gagliardo form on `H_j` (`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`), and that by
the form on `Γ` (`Rd.BoundedLipschitzDomain.exists_slobodeckijForm_chartPiece_le`). -/
theorem exists_boundaryBesovNorm_rpow_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, AEStronglyMeasurable g Ω.surfaceMeasure →
      Ω.boundaryBesovNorm p ψ s p g ^ p.toReal ≤
        C * (eLpNorm g p Ω.surfaceMeasure ^ p.toReal + Ω.boundarySlobodeckijForm p s g) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  choose K hK hle using fun j => Ω.exists_slobodeckijForm_chartPiece_le ψ j hp hs hs1
  refine ⟨((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
      ∑ j, 2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal +
        slobodeckijConstUpper (Ω.graph j).hyperplane p s * K j) + 1,
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.natCast_ne_top _)) (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top
        (ENNReal.two_rpow_ne_top _)
        (ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top,
          ENNReal.mul_ne_top (slobodeckijConstUpper_ne_top hp0 hp hs) (hK j)⟩)),
      ENNReal.one_ne_top⟩, fun g hg => ?_⟩
  have hgm : Measurable (hg.mk g) := hg.stronglyMeasurable_mk.measurable
  rw [Ω.boundaryBesovNorm_congr ψ (Ω.ae_surfaceMeasure_iff_aeBoundary.1 hg.ae_eq_mk),
    eLpNorm_congr_ae hg.ae_eq_mk, Ω.boundarySlobodeckijForm_congr_ae hg.ae_eq_mk,
    eLpNorm_rpow_eq hgm.aestronglyMeasurable hp0 hp]
  by_cases hX : ∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure = ∞
  · rw [hX, top_add, ENNReal.mul_top (by positivity)]
    exact le_top
  have hmem : ∀ j, MemLp (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') *
      hg.mk g ((Ω.graph j).graphMap x')) p volume := fun j =>
    memLp_iff.2 ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp
      ((((ψ.contDiff_toComplex j).continuous.comp (Ω.graph j).continuous_graphMap).measurable.mul
        (hgm.comp (Ω.graph j).continuous_graphMap.measurable)).aestronglyMeasurable)).2
      ((Ω.lintegral_chartPiece_le ψ j hP _).trans_lt (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg hP.le ENNReal.ofReal_ne_top) (lt_top_iff_ne_top.2 hX))))
  have hj : ∀ j (G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane)),
      (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume] (fun x' => ψ.toComplex j
        ((Ω.graph j).graphMap x') * hg.mk g ((Ω.graph j).graphMap x')) →
      (‖G‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k)) ^ p.toReal ≤
        2 ^ (p.toReal - 1) * ((ENNReal.ofReal (ψ.derivBound j) ^ p.toReal +
          slobodeckijConstUpper (Ω.graph j).hyperplane p s * K j) *
          (∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure +
            Ω.boundarySlobodeckijForm p s (hg.mk g))) := by
    intro j G hG
    have hGP : ‖G‖ₑ ^ p.toReal ≤ ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
        ∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure := by
      have hGP' : ∫⁻ x', ‖G x'‖ₑ ^ p.toReal = ∫⁻ x', ‖ψ.toComplex j ((Ω.graph j).graphMap x') *
          hg.mk g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal :=
        lintegral_congr_ae (hG.mono fun x' hx' => by dsimp only; rw [hx'])
      rw [Lp.enorm_def, eLpNorm_rpow_eq (Lp.aestronglyMeasurable G) hp0 hp, hGP']
      exact Ω.lintegral_chartPiece_le ψ j hP _
    have hL := (lqNorm_modulus_rpow_le_slobodeckijForm hp hs G).trans (mul_le_mul' le_rfl
      ((slobodeckijForm_congr_ae hG p s).trans_le (hle j _ hgm)))
    calc _ ≤ 2 ^ (p.toReal - 1) * (‖G‖ₑ ^ p.toReal +
          lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 G k) ^ p.toReal) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hP1
      _ ≤ _ := mul_le_mul' le_rfl ((add_le_add hGP hL).trans (by
          rw [add_mul, mul_assoc]
          exact add_le_add (mul_le_mul' le_rfl le_self_add) le_rfl))
  rw [Ω.boundaryBesovNorm_eq_sum ψ (fun j => (hmem j).toLp _) fun j => (hmem j).coeFn_toLp]
  calc _ ≤ ((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) * ∑ j,
        (‖(hmem j).toLp _‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1
          ((hmem j).toLp _) k)) ^ p.toReal :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ) (f := fun j =>
          ‖(hmem j).toLp _‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1
            ((hmem j).toLp _) k)) hP1
    _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => hj j _ (hmem j).coeFn_toLp)
    _ = (((Finset.univ : Finset (Fin Ω.N)).card : ℝ≥0∞) ^ (p.toReal - 1) *
        ∑ j, 2 ^ (p.toReal - 1) * (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal +
          slobodeckijConstUpper (Ω.graph j).hyperplane p s * K j)) *
        (∫⁻ y, ‖hg.mk g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure +
          Ω.boundarySlobodeckijForm p s (hg.mk g)) := by
        simp only [← mul_assoc, ← Finset.sum_mul]
    _ ≤ _ := mul_le_mul' le_self_add le_rfl

/-! ### Gagliardo's description of `B^s_{p,p}(Γ)` and of the trace space -/

/-- **Gagliardo's description of `B^s_{p,p}(Γ)`** (Gagliardo 1957): for `1 ≤ p < ∞`, `0 < s < 1`,
a resolution of unity `ψ` and `g ∈ L_p(Γ)`, `g ∈ B^s_{p,p}(Γ)` iff
`∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ(y) dσ(x) < ∞`, that is, the chart-wise space
`B^s_{p,p}(Γ)` is the Sobolev–Slobodeckij space `W^{s,p}(Γ)` defined by the surface measure
(`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`). -/
theorem memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top (ψ : Ω.BoundaryPartition)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {g : V → ℂ}
    (hg : MemLp g p Ω.surfaceMeasure) :
    Ω.MemBoundaryBesov p ψ s p g ↔ Ω.boundarySlobodeckijForm p s g < ∞ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP := ENNReal.toReal_pos hp0 hp
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_boundarySlobodeckijForm_le ψ hp hs
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundaryBesovNorm_rpow_le ψ hp hs hs1
  rw [Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ]
  refine ⟨fun h => (h₁ g).trans_lt (ENNReal.mul_lt_top hC₁.lt_top
    (ENNReal.rpow_lt_top_of_nonneg hP.le h.ne)), fun h => ?_⟩
  rw [← ENNReal.rpow_lt_top_iff_of_pos hP]
  exact (h₂ g hg.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top hC₂.lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg hP.le hg.eLpNorm_lt_top.ne, h⟩))

/-- **The norm of the trace space of `H^s(Ω)` by the Sobolev–Slobodeckij norm**, `1/2 < s < 3/2`:
there is `C < ∞` with
`‖w‖² ≤ C (‖τ_s w‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |τ_s w(y) - τ_s w(x)|² / |y - x|^(n+2s-2) dσ(y) dσ(x))` and
the reverse bound `‖τ_s w‖²_{L_2(Γ)} + ∫_Γ ∫_Γ … ≤ C ‖w‖²` for every `w ∈ Ω.TraceSpace s` and its
trace `τ_s w ∈ L_2(Γ)`, `n = dim V`: the norm of the trace space is equivalent to Gagliardo's norm
of `W^{s-1/2,2}(Γ)`. It combines the equivalence with the chart-wise norm of
`B^{s-1/2}_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`) with
`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le` and the boundedness of `τ_s`. -/
theorem exists_traceL2_norm_equiv_slobodeckij (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ w : Ω.TraceSpace s hs hs',
      ‖w‖ₑ ^ 2 ≤ C * (‖Ω.traceL2 s hs hs' w‖ₑ ^ 2 +
          Ω.boundarySlobodeckijForm 2 (s - 1 / 2) (Ω.traceL2 s hs hs' w)) ∧
        ‖Ω.traceL2 s hs hs' w‖ₑ ^ 2 +
            Ω.boundarySlobodeckijForm 2 (s - 1 / 2) (Ω.traceL2 s hs hs' w) ≤
          C * ‖w‖ₑ ^ 2 := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_traceL2_norm_equiv Ω.boundaryPartition s hs hs'
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundarySlobodeckijForm_le (p := 2) Ω.boundaryPartition
    two_ne_top (s := s - 1 / 2) (sub_pos.2 hs)
  obtain ⟨C₃, hC₃, h₃⟩ := Ω.exists_boundaryBesovNorm_rpow_le (p := 2) Ω.boundaryPartition
    two_ne_top (s := s - 1 / 2) (sub_pos.2 hs) (by linarith)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h₂ h₃
  refine ⟨C₁ ^ 2 * C₃ + (‖Ω.traceL2 s hs hs'‖ₑ ^ 2 + C₂ * C₁ ^ 2), ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.pow_ne_top hC₁) hC₃, ENNReal.add_ne_top.2
      ⟨ENNReal.pow_ne_top enorm_ne_top, ENNReal.mul_ne_top hC₂ (ENNReal.pow_ne_top hC₁)⟩⟩,
    fun w => ⟨?_, ?_⟩⟩
  · calc ‖w‖ₑ ^ 2
        ≤ (C₁ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition (s - 1 / 2) 2
            (Ω.traceL2 s hs hs' w)) ^ 2 :=
          pow_le_pow_left₀ zero_le (h₁ w).1 2
      _ ≤ C₁ ^ 2 * (C₃ * (‖Ω.traceL2 s hs hs' w‖ₑ ^ 2 +
            Ω.boundarySlobodeckijForm 2 (s - 1 / 2) (Ω.traceL2 s hs hs' w))) := by
          rw [mul_pow, Lp.enorm_def]
          exact mul_le_mul' le_rfl (h₃ _ (Lp.aestronglyMeasurable _))
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · calc _ ≤ (‖Ω.traceL2 s hs hs'‖ₑ * ‖w‖ₑ) ^ 2 + C₂ * (C₁ * ‖w‖ₑ) ^ 2 :=
          add_le_add (pow_le_pow_left₀ zero_le ((Ω.traceL2 s hs hs').le_opENorm w) 2)
            ((h₂ _).trans (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le (h₁ w).2 2)))
      _ = (‖Ω.traceL2 s hs hs'‖ₑ ^ 2 + C₂ * C₁ ^ 2) * ‖w‖ₑ ^ 2 := by ring
      _ ≤ _ := mul_le_mul' le_add_self le_rfl

/-- **The range of the trace `Ω.TraceSpace s → L_2(Γ)` by the Gagliardo form**, `1/2 < s < 3/2`:
`g ∈ L_2(Γ)` is the trace `τ_s w` of some `w ∈ Ω.TraceSpace s` iff
`∫_Γ ∫_Γ |g(y) - g(x)|² / |y - x|^(n+2s-2) dσ(y) dσ(x) < ∞`
(`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`,
`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top`). -/
theorem mem_range_traceL2_iff_slobodeckij (s : ℝ) (g : Ω.BoundaryL2)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    g ∈ LinearMap.range (Ω.traceL2 s hs hs' : Ω.TraceSpace s hs hs' →ₗ[ℂ] Ω.BoundaryL2) ↔
      Ω.boundarySlobodeckijForm 2 (s - 1 / 2) g < ∞ := by
  rw [Ω.mem_range_traceL2_iff Ω.boundaryPartition s g hs hs']
  exact Ω.memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top _ two_ne_top (sub_pos.2 hs)
    (by linarith) (Lp.memLp g)

/-! ### The Hilbert space `H^t(Γ)` -/

/-- **The pair differences of a chart piece lie in `L_2` of the Gagliardo measure**: for `t > 0`,
`g ∈ B^t_{2,2}(Γ)` and its chart piece `G_j = (ψ_j g) ∘ γ_j` on `H_j` for the canonical
resolution of unity, `(x', y') ↦ G_j(y') - G_j(x')` lies in `L_2(H_j × H_j)` for
`Rd.gagliardoMeasure`: its square norm is the Gagliardo form of `G_j`
(`Rd.eLpNorm_sub_sq_gagliardoMeasure`), finite by the bound by the first-difference norm
(`Rd.slobodeckijForm_le`) and `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_chartPieceLp`. -/
theorem memLp_chartPiece_sub (j : Fin Ω.N) {t : ℝ} (ht : 0 < t) (g : Ω.BoundaryBesov 2 t 2) :
    MemLp (fun z : (Ω.graph j).hyperplane × (Ω.graph j).hyperplane =>
      (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ) z.2 -
        (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ) z.1) 2
      (gagliardoMeasure (Ω.graph j).hyperplane t) := by
  set G := Ω.chartPieceLp Ω.boundaryPartition j g.toLp
  have hG : Measurable (G : (Ω.graph j).hyperplane → ℂ) := (Lp.stronglyMeasurable G).measurable
  refine memLp_iff.2 ?_
  have hfin := (Ω.memBoundaryBesov_iff_chartPieceLp _ t 2 g.toLp).1 g.mem j
  have hS := slobodeckijForm_le two_ne_top ht G
  rw [ENNReal.toReal_ofNat] at hS
  have hlt : slobodeckijForm 2 t (G : (Ω.graph j).hyperplane → ℂ) < ∞ := by
    refine hS.trans_lt (ENNReal.mul_lt_top (slobodeckijConstLower_ne_top two_ne_zero
      ENNReal.ofNat_ne_top ht).lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.1 hfin).2.ne
  rw [← eLpNorm_sub_sq_gagliardoMeasure t hG] at hlt
  exact (ENNReal.pow_lt_top_iff.1 hlt).resolve_right two_ne_zero

/-- **The pair differences of the chart piece `j`** as a linear map
`δ_j : B^t_{2,2}(Γ) → L_2(H_j × H_j, |y' - x'|^(-(n-1+2t)) dx' dy')`,
`δ_j g = ((x', y') ↦ G_j(y') - G_j(x'))`
with the chart piece `G_j = (ψ_j g) ∘ γ_j` of the canonical resolution of unity
(`Rd.BoundedLipschitzDomain.memLp_chartPiece_sub`), for `t > 0`. Its square norm is the
Gagliardo form of `G_j` on `H_j` (`Rd.BoundedLipschitzDomain.enorm_chartGagliardoDiff_sq`). For
`t ≤ 0` the map is `0`, and the norm of `Rd.BoundedLipschitzDomain.BoundarySobolev t` is then the
norm of `L_2(Γ)`; that space is `H^t(Γ)` for `0 < t < 1`. -/
noncomputable def chartGagliardoDiff (j : Fin Ω.N) (t : ℝ) :
    Ω.BoundaryBesov 2 t 2 →ₗ[ℂ] Lp ℂ 2 (gagliardoMeasure (Ω.graph j).hyperplane t) :=
  if ht : 0 < t then
    { toFun g := (Ω.memLp_chartPiece_sub j ht g).toLp _
      map_add' g h := by
        rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
        have hadd : Ω.chartPieceLp Ω.boundaryPartition j (g + h).toLp =
            Ω.chartPieceLp Ω.boundaryPartition j g.toLp +
              Ω.chartPieceLp Ω.boundaryPartition j h.toLp := map_add _ _ _
        filter_upwards [ae_gagliardoMeasure t (hadd ▸ Lp.coeFn_add
          (Ω.chartPieceLp Ω.boundaryPartition j g.toLp)
          (Ω.chartPieceLp Ω.boundaryPartition j h.toLp))] with z hz
        simp only [Pi.add_apply, hz.1, hz.2]
        ring
      map_smul' c g := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
        have hsmul : Ω.chartPieceLp Ω.boundaryPartition j (c • g).toLp =
            c • Ω.chartPieceLp Ω.boundaryPartition j g.toLp := map_smul _ _ _
        filter_upwards [ae_gagliardoMeasure t (hsmul ▸ Lp.coeFn_smul c
          (Ω.chartPieceLp Ω.boundaryPartition j g.toLp))] with z hz
        simp only [Pi.smul_apply, smul_eq_mul, hz.1, hz.2]
        ring }
  else 0

/-- **The square norm of the pair differences is the Gagliardo form of the chart piece**: for
`t > 0` and `g ∈ B^t_{2,2}(Γ)`,
`‖δ_j g‖² = ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t) dy' dx'`, the Gagliardo form
`Rd.slobodeckijForm 2 t G_j` on the hyperplane `H_j` of dimension `n - 1`
(`Rd.eLpNorm_sub_sq_gagliardoMeasure`). -/
theorem enorm_chartGagliardoDiff_sq (j : Fin Ω.N) {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) :
    ‖Ω.chartGagliardoDiff j t g‖ₑ ^ 2 =
      slobodeckijForm 2 t (Ω.chartPieceLp Ω.boundaryPartition j g.toLp :
        (Ω.graph j).hyperplane → ℂ) := by
  rw [chartGagliardoDiff, dite_eq_left ht, LinearMap.coe_mk, AddHom.coe_mk, Lp.enorm_def,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  exact eLpNorm_sub_sq_gagliardoMeasure t (Lp.stronglyMeasurable _).measurable

/-- **The Gagliardo embedding** `g ↦ (g, (δ_j g)_j)` of `B^t_{2,2}(Γ)` into the Hilbert space
`L_2(Γ) × ∏_j L_2(H_j × H_j, |y' - x'|^(-(n-1+2t)) dx' dy')`, with the `L_2` norm on the product
(Mathlib's `WithLp 2`) and the pair differences `δ_j g` of the chart pieces
(`Rd.BoundedLipschitzDomain.chartGagliardoDiff`): a linear map, injective by its first component
(`Rd.BoundedLipschitzDomain.gagliardoEmbedding_injective`), whose square norm is
`‖g‖²_{L_2(Γ)}` plus the Gagliardo forms of the chart pieces
(`Rd.BoundedLipschitzDomain.enorm_sq_gagliardoEmbedding`). It defines the norm and the inner
product of `H^t(Γ)` (`Rd.BoundedLipschitzDomain.BoundarySobolev`). -/
noncomputable def gagliardoEmbedding (t : ℝ) : Ω.BoundaryBesov 2 t 2 →ₗ[ℂ]
    WithLp 2 (Ω.BoundaryL2 ×
      PiLp 2 fun j : Fin Ω.N => Lp ℂ 2 (gagliardoMeasure (Ω.graph j).hyperplane t)) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ
    (BoundaryBesov.toLpL : Ω.BoundaryBesov 2 t 2 →L[ℂ] Ω.BoundaryL2).toLinearMap.prod
      ((WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ
        LinearMap.pi fun j => Ω.chartGagliardoDiff j t)

/-- The Gagliardo embedding sends `g` to `(g, (δ_j g)_j)`. -/
theorem gagliardoEmbedding_apply (t : ℝ) (g : Ω.BoundaryBesov 2 t 2) :
    Ω.gagliardoEmbedding t g =
      WithLp.toLp 2 (g.toLp, WithLp.toLp 2 fun j => Ω.chartGagliardoDiff j t g) :=
  rfl

/-- The Gagliardo embedding is injective: its first component is `g ∈ L_2(Γ)`. -/
theorem gagliardoEmbedding_injective (t : ℝ) : Function.Injective (Ω.gagliardoEmbedding t) :=
  fun _ _ hgh => BoundaryBesov.ext (congrArg WithLp.fst hgh)

/-- **The square norm of the Gagliardo embedding**:
`‖(g, (δ_j g)_j)‖² = ‖g‖²_{L_2(Γ)} + ∑_j ‖δ_j g‖²` (Mathlib's `WithLp.prod_norm_sq_eq_of_L2`,
`PiLp.norm_sq_eq_of_L2`). -/
theorem sq_norm_gagliardoEmbedding (t : ℝ) (g : Ω.BoundaryBesov 2 t 2) :
    ‖Ω.gagliardoEmbedding t g‖ ^ 2 = ‖g.toLp‖ ^ 2 + ∑ j, ‖Ω.chartGagliardoDiff j t g‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, gagliardoEmbedding_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    PiLp.norm_sq_eq_of_L2]

/-- **The chart-wise Gagliardo norm**: for `t > 0` and `g ∈ B^t_{2,2}(Γ)`,
`‖(g, (δ_j g)_j)‖² = ‖g‖²_{L_2(Γ)} + ∑_j ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t)`
with the chart pieces `G_j = (ψ_j g) ∘ γ_j`
(`Rd.BoundedLipschitzDomain.sq_norm_gagliardoEmbedding`,
`Rd.BoundedLipschitzDomain.enorm_chartGagliardoDiff_sq`). -/
theorem enorm_sq_gagliardoEmbedding {t : ℝ} (ht : 0 < t) (g : Ω.BoundaryBesov 2 t 2) :
    ‖Ω.gagliardoEmbedding t g‖ₑ ^ 2 = ‖g.toLp‖ₑ ^ 2 + ∑ j, slobodeckijForm 2 t
      (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ) := by
  have h := congrArg ENNReal.ofReal (Ω.sq_norm_gagliardoEmbedding t g)
  rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun _ _ => by positivity),
    ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity] at h
  simp only [ENNReal.ofReal_pow, norm_nonneg, ofReal_norm] at h
  rw [h]
  simp only [Ω.enorm_chartGagliardoDiff_sq _ ht]

/-- **`L_2(Γ)` is bounded by the Gagliardo embedding**: `‖g‖_{L_2(Γ)} ≤ ‖Φ g‖` for
`Φ g = (g, (δ_j g)_j)`, `t > 0` (`Rd.BoundedLipschitzDomain.enorm_sq_gagliardoEmbedding`). -/
theorem enorm_toLp_le_enorm_gagliardoEmbedding {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) :
    ‖g.toLp‖ₑ ≤ ‖Ω.gagliardoEmbedding t g‖ₑ := by
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, Ω.enorm_sq_gagliardoEmbedding ht]
  exact le_self_add

/-- **The Gagliardo form of a chart piece is bounded by the Gagliardo embedding**: the Gagliardo
form of `G_j = (ψ_j g) ∘ γ_j` on `H_j` is at most `‖Φ g‖²` for `Φ g = (g, (δ_j g)_j)`, `t > 0`
(`Rd.BoundedLipschitzDomain.enorm_sq_gagliardoEmbedding`). -/
theorem slobodeckijForm_chartPieceLp_le_enorm_gagliardoEmbedding_sq {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) (j : Fin Ω.N) :
    slobodeckijForm 2 t (Ω.chartPieceLp Ω.boundaryPartition j g.toLp :
      (Ω.graph j).hyperplane → ℂ) ≤ ‖Ω.gagliardoEmbedding t g‖ₑ ^ 2 := by
  rw [Ω.enorm_sq_gagliardoEmbedding ht]
  exact (Finset.single_le_sum (f := fun j => slobodeckijForm 2 t
    (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ))
    (fun _ _ => zero_le) (Finset.mem_univ j)).trans le_add_self

/-- **The Gagliardo embedding is bounded on `B^t_{2,2}(Γ)`**, `t > 0`: there is `C < ∞` with
`‖(g, (δ_j g)_j)‖ ≤ C ‖g‖_{B^t_{2,2}(Γ)}`, by `‖g‖_{L_2(Γ)} ≤ C₀ ‖g‖_{B^t_{2,2}(Γ)}`
(`Rd.BoundedLipschitzDomain.exists_eLpNorm_le_boundaryBesovNorm`) and the bound of the Gagliardo
form of each chart piece by its first-difference norm (`Rd.slobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.modNorm_chartPieceLp_le`). -/
theorem exists_enorm_gagliardoEmbedding_le {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundaryBesov 2 t 2,
      ‖Ω.gagliardoEmbedding t g‖ₑ ≤ C * ‖g‖ₑ := by
  obtain ⟨C₀, hC₀, h₀⟩ := Ω.exists_eLpNorm_le_boundaryBesovNorm (p := 2) Ω.boundaryPartition t 2
  set K := C₀ ^ 2 + ∑ j : Fin Ω.N, slobodeckijConstLower (Ω.graph j).hyperplane 2 t with hKdef
  have hK : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hC₀, ENNReal.sum_ne_top.2
    fun j _ => slobodeckijConstLower_ne_top two_ne_zero ENNReal.ofNat_ne_top ht⟩
  have hK2 : (K ^ (1 / 2 : ℝ)) ^ 2 = K := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  refine ⟨K ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK, fun g => ?_⟩
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, hK2, Ω.enorm_sq_gagliardoEmbedding ht,
    BoundaryBesov.enorm_eq, hKdef, add_mul, Finset.sum_mul]
  refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
  · rw [← mul_pow, Lp.enorm_def]
    exact pow_le_pow_left₀ zero_le (h₀ _ (Lp.aestronglyMeasurable _)) 2
  · have hS := slobodeckijForm_le two_ne_top ht (Ω.chartPieceLp Ω.boundaryPartition j g.toLp)
    have hsum := ENNReal.add_rpow_le_rpow_add
      ‖Ω.chartPieceLp Ω.boundaryPartition j g.toLp‖ₑ (lqNorm 2 fun k => dyadicWeight t k *
        lpModulus 2 1 (Ω.chartPieceLp Ω.boundaryPartition j g.toLp) k)
      (by norm_num : (1 : ℝ) ≤ (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hsum hS
    exact hS.trans (mul_le_mul' le_rfl (hsum.trans (pow_le_pow_left₀ zero_le
      (Ω.modNorm_chartPieceLp_le _ t 2 g.toLp j) 2)))

/-- **`B^t_{2,2}(Γ)` is bounded by the Gagliardo embedding**, `t > 0`: there is `C < ∞` with
`‖g‖_{B^t_{2,2}(Γ)} ≤ C ‖Φ g‖` for `Φ g = (g, (δ_j g)_j)`. Chart by chart,
`‖G_j‖_{L_2(H_j)} ≤ D_j ‖g‖_{L_2(Γ)} ≤ D_j ‖Φ g‖` with the bound
`D_j = Ω.boundaryPartition.derivBound j` of `ψ⁰_j`
(`Rd.BoundedLipschitzDomain.eLpNorm_chartPiece_le`,
`Rd.BoundedLipschitzDomain.enorm_toLp_le_enorm_gagliardoEmbedding`), and the square of the
first-difference norm of `G_j` is at most a constant times its Gagliardo form
(`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`), which is at most `‖Φ g‖²`
(`Rd.BoundedLipschitzDomain.slobodeckijForm_chartPieceLp_le_enorm_gagliardoEmbedding_sq`). -/
theorem exists_enorm_le_enorm_gagliardoEmbedding {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundaryBesov 2 t 2,
      ‖g‖ₑ ≤ C * ‖Ω.gagliardoEmbedding t g‖ₑ := by
  refine ⟨∑ j, (ENNReal.ofReal (Ω.boundaryPartition.derivBound j) +
      slobodeckijConstUpper (Ω.graph j).hyperplane 2 t ^ (1 / 2 : ℝ)),
    ENNReal.sum_ne_top.2 fun j _ => ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (slobodeckijConstUpper_ne_top two_ne_zero ENNReal.ofNat_ne_top ht)⟩, fun g => ?_⟩
  rw [BoundaryBesov.enorm_eq, Ω.boundaryBesovNorm_eq_sum_chartPieceLp, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [add_mul]
  refine add_le_add ?_ ?_
  · rw [Lp.enorm_def, eLpNorm_congr_ae (Ω.chartPieceLp_ae _ j g.toLp)]
    refine (Ω.eLpNorm_chartPiece_le _ j (Lp.stronglyMeasurable g.toLp)).trans
      (mul_le_mul' le_rfl ?_)
    rw [← Lp.enorm_def]
    exact Ω.enorm_toLp_le_enorm_gagliardoEmbedding ht g
  · have hL := lqNorm_modulus_rpow_le_slobodeckijForm two_ne_top ht
      (Ω.chartPieceLp Ω.boundaryPartition j g.toLp)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hL
    have hC2 : (slobodeckijConstUpper (Ω.graph j).hyperplane 2 t ^ (1 / 2 : ℝ)) ^ 2 =
        slobodeckijConstUpper (Ω.graph j).hyperplane 2 t := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, hC2]
    exact hL.trans (mul_le_mul' le_rfl
      (Ω.slobodeckijForm_chartPieceLp_le_enorm_gagliardoEmbedding_sq ht g j))

/-- **The Gagliardo embedding and `B^t_{2,2}(Γ)` have equivalent norms**, `t > 0`: there is
`C < ∞` with `‖g‖_{B^t_{2,2}(Γ)} ≤ C ‖(g, (δ_j g)_j)‖` and `‖(g, (δ_j g)_j)‖ ≤ C ‖g‖_{B^t_{2,2}(Γ)}`
(`Rd.BoundedLipschitzDomain.exists_enorm_le_enorm_gagliardoEmbedding`,
`Rd.BoundedLipschitzDomain.exists_enorm_gagliardoEmbedding_le`). -/
theorem exists_gagliardoEmbedding_norm_equiv {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundaryBesov 2 t 2,
      ‖g‖ₑ ≤ C * ‖Ω.gagliardoEmbedding t g‖ₑ ∧ ‖Ω.gagliardoEmbedding t g‖ₑ ≤ C * ‖g‖ₑ := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_enorm_le_enorm_gagliardoEmbedding ht
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_enorm_gagliardoEmbedding_le ht
  exact ⟨max C₁ C₂, (max_lt hC₁.lt_top hC₂.lt_top).ne, fun g =>
    ⟨(h₁ g).trans (mul_le_mul' (le_max_left _ _) le_rfl),
      (h₂ g).trans (mul_le_mul' (le_max_right _ _) le_rfl)⟩⟩

/-- **The Sobolev space `H^t(Γ)`** on the boundary of a bounded Lipschitz domain, `0 < t < 1`:
the space `B^t_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.BoundaryBesov`) with the chart-wise
Gagliardo norm
`‖g‖²_{H^t(Γ)} = ‖g‖²_{L_2(Γ)} + ∑_j ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t)`
for the chart pieces `G_j = (ψ_j g) ∘ γ_j` of the canonical resolution of unity, the norm of the
Gagliardo embedding (`Rd.BoundedLipschitzDomain.gagliardoEmbedding`). This norm satisfies the
parallelogram law and comes from an inner product, so `H^t(Γ)` is a Hilbert space; it is
equivalent to the norm of `B^t_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`) and to Gagliardo's norm with the
surface measure
(`Rd.BoundedLipschitzDomain.exists_boundarySobolev_norm_equiv_slobodeckij`). The definition is a
type synonym of `B^t_{2,2}(Γ)` with its own norm, for every `t`. For `0 < t < 1` it is `H^t(Γ)`.
For `t < 0` it is `L_2(Γ)` with its norm, and for `t ≥ 1` and `n ≥ 2` it is `{0}`, since
`ω_1(G, h) = o(h)` forces `G = 0` in `L_2(H_j)`. The space `H^{-t}(Γ)` is
`Rd.BoundedLipschitzDomain.DualBoundarySobolev t`. -/
def BoundarySobolev (t : ℝ) : Type _ := Ω.BoundaryBesov 2 t 2

namespace BoundarySobolev

variable {Ω} {t : ℝ}

/-- `H^t(Γ)` is an additive group, that of `B^t_{2,2}(Γ)`. -/
noncomputable instance instAddCommGroup : AddCommGroup (Ω.BoundarySobolev t) :=
  inferInstanceAs (AddCommGroup (Ω.BoundaryBesov 2 t 2))

/-- `H^t(Γ)` is a complex vector space, that of `B^t_{2,2}(Γ)`. -/
noncomputable instance instModule : Module ℂ (Ω.BoundarySobolev t) :=
  inferInstanceAs (Module ℂ (Ω.BoundaryBesov 2 t 2))

/-- **The norm of `H^t(Γ)`**: the norm of the Gagliardo embedding (Mathlib's
`NormedAddCommGroup.induced`, the embedding being injective). -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Ω.BoundarySobolev t) :=
  NormedAddCommGroup.induced (Ω.BoundarySobolev t) _
    (Ω.gagliardoEmbedding t : Ω.BoundarySobolev t →ₗ[ℂ] _) (Ω.gagliardoEmbedding_injective t)

/-- `H^t(Γ)` is a complex normed space: the Gagliardo embedding is linear (Mathlib's
`NormedSpace.induced`). -/
noncomputable instance instNormedSpace : NormedSpace ℂ (Ω.BoundarySobolev t) :=
  NormedSpace.induced ℂ (Ω.BoundarySobolev t) _
    (Ω.gagliardoEmbedding t : Ω.BoundarySobolev t →ₗ[ℂ] _)

/-- **The inner product of `H^t(Γ)`**: `⟪g, h⟫ = ⟪(g, (δ_j g)_j), (h, (δ_j h)_j)⟫` in the
Hilbert space of the Gagliardo embedding, so that `‖g‖² = ⟪g, g⟫`; by polarisation it is the
only inner product with the chart-wise Gagliardo norm. The fields are those of Mathlib's
`InnerProductSpace.induced`, written out over the norm `instNormedAddCommGroup`, so that instance
search finds the norm of the dual space `H^{-t}(Γ)`. -/
noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (Ω.BoundarySobolev t) where
  inner g h := ⟪Ω.gagliardoEmbedding t g, Ω.gagliardoEmbedding t h⟫_ℂ
  norm_sq_eq_re_inner g := norm_sq_eq_re_inner (Ω.gagliardoEmbedding t g)
  conj_inner_symm _ _ := inner_conj_symm _ _
  add_left g g' h :=
    (congrArg (⟪·, Ω.gagliardoEmbedding t h⟫_ℂ) ((Ω.gagliardoEmbedding t).map_add g g')).trans
      (inner_add_left _ _ _)
  smul_left g h c :=
    (congrArg (⟪·, Ω.gagliardoEmbedding t h⟫_ℂ) ((Ω.gagliardoEmbedding t).map_smul c g)).trans
      (inner_smul_left _ _ _)

end BoundarySobolev

/-- The norm of `g ∈ H^t(Γ)` is the norm of its Gagliardo embedding. -/
theorem norm_boundarySobolev {t : ℝ} (g : Ω.BoundarySobolev t) :
    ‖g‖ = ‖Ω.gagliardoEmbedding t g‖ :=
  rfl

/-- The extended norm of `g ∈ H^t(Γ)` is that of its Gagliardo embedding. -/
theorem enorm_boundarySobolev {t : ℝ} (g : Ω.BoundarySobolev t) :
    ‖g‖ₑ = ‖Ω.gagliardoEmbedding t g‖ₑ :=
  rfl

/-- **The inner product of `H^t(Γ)`** is the inner product of the Gagliardo embeddings:
`⟪g, h⟫_{H^t(Γ)} = ⟪g, h⟫_{L_2(Γ)} + ∑_j ⟪δ_j g, δ_j h⟫`. -/
theorem inner_boundarySobolev {t : ℝ} (g h : Ω.BoundarySobolev t) :
    ⟪g, h⟫_ℂ = ⟪Ω.gagliardoEmbedding t g, Ω.gagliardoEmbedding t h⟫_ℂ :=
  rfl

/-- **Equal smoothness gives the same space**: for `t = t'`, the identity `H^t(Γ) → H^{t'}(Γ)` as
a linear isometric isomorphism, as Mathlib's `LinearEquiv.cast` does for linear isomorphisms. It
identifies, for example, `H^{1 - 1/2}(Γ)` with `H^{1/2}(Γ)`, two types that Lean does not identify
by computation. -/
noncomputable def boundarySobolevCongr {t t' : ℝ} (h : t = t') :
    Ω.BoundarySobolev t ≃ₗᵢ[ℂ] Ω.BoundarySobolev t' :=
  h ▸ LinearIsometryEquiv.refl ℂ _

/-- The identification `H^t(Γ) = H^{t'}(Γ)` keeps the function in `L_2(Γ)`. -/
theorem toLp_boundarySobolevCongr {t t' : ℝ} (h : t = t') (g : Ω.BoundarySobolev t) :
    (Ω.boundarySobolevCongr h g).toLp = g.toLp := by
  subst h
  rfl

/-- **`H^t(Γ)` and `B^t_{2,2}(Γ)` are isomorphic**, `t > 0`: the identity is an isomorphism of
normed spaces from `B^t_{2,2}(Γ)` with the chart-wise Gagliardo norm onto `B^t_{2,2}(Γ)` with the
norm by chart pieces (`Rd.BoundedLipschitzDomain.exists_gagliardoEmbedding_norm_equiv`). -/
noncomputable def boundarySobolevEquivBoundaryBesov (t : ℝ) (ht : 0 < t) :
    Ω.BoundarySobolev t ≃L[ℂ] Ω.BoundaryBesov 2 t 2 :=
  { (LinearEquiv.refl ℂ (Ω.BoundaryBesov 2 t 2) :
      Ω.BoundarySobolev t ≃ₗ[ℂ] Ω.BoundaryBesov 2 t 2) with
    continuous_toFun := by
      obtain ⟨C, hC, h⟩ := Ω.exists_gagliardoEmbedding_norm_equiv ht
      have hb : ∀ g : Ω.BoundaryBesov 2 t 2, ‖g‖ ≤ C.toReal * ‖Ω.gagliardoEmbedding t g‖ :=
        fun g => norm_le_toReal_mul_of_enorm_le hC (h g).1
      let e : Ω.BoundarySobolev t ≃ₗ[ℂ] Ω.BoundaryBesov 2 t 2 := LinearEquiv.refl ℂ _
      exact AddMonoidHomClass.continuous_of_bound e C.toReal hb
    continuous_invFun := by
      obtain ⟨C, hC, h⟩ := Ω.exists_gagliardoEmbedding_norm_equiv ht
      have hb : ∀ g : Ω.BoundaryBesov 2 t 2, ‖Ω.gagliardoEmbedding t g‖ ≤ C.toReal * ‖g‖ :=
        fun g => norm_le_toReal_mul_of_enorm_le hC (h g).2
      let e : Ω.BoundaryBesov 2 t 2 ≃ₗ[ℂ] Ω.BoundarySobolev t := LinearEquiv.refl ℂ _
      exact AddMonoidHomClass.continuous_of_bound e C.toReal hb }

/-- The isomorphism `H^t(Γ) ≅ B^t_{2,2}(Γ)` keeps the function in `L_2(Γ)`. -/
theorem toLp_boundarySobolevEquivBoundaryBesov {t : ℝ} (ht : 0 < t) (g : Ω.BoundarySobolev t) :
    (Ω.boundarySobolevEquivBoundaryBesov t ht g).toLp = g.toLp :=
  rfl

/-- The inverse isomorphism `B^t_{2,2}(Γ) ≅ H^t(Γ)` keeps the function in `L_2(Γ)`. -/
theorem toLp_boundarySobolevEquivBoundaryBesov_symm {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) :
    BoundaryBesov.toLp ((Ω.boundarySobolevEquivBoundaryBesov t ht).symm g) = g.toLp :=
  rfl

/-- **`H^t(Γ)` is a Hilbert space**, `t > 0`: it is isomorphic to the Banach space
`B^t_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`,
`Rd.BoundedLipschitzDomain.completeSpace_boundaryBesov`; Mathlib's `completeSpace_congr`). -/
instance completeSpace_boundarySobolev {t : ℝ} [Fact (0 < t)] :
    CompleteSpace (Ω.BoundarySobolev t) :=
  (completeSpace_congr (e := (Ω.boundarySobolevEquivBoundaryBesov t Fact.out).toEquiv)
    (Ω.boundarySobolevEquivBoundaryBesov t Fact.out).isUniformEmbedding).2 inferInstance

/-- **The dual space `H^{-t}(Γ)`**: the bounded linear functionals on `H^t(Γ)`. -/
abbrev DualBoundarySobolev (t : ℝ) := StrongDual ℂ (Ω.BoundarySobolev t)

/-- **Riesz for `H^{-t}(Γ)`**, `t > 0`: the conjugate-linear isometric isomorphism of the dual
onto `H^t(Γ)` that represents a functional by an element (Mathlib's `InnerProductSpace.toDual`):
`ℓ g = ⟪dualBoundarySobolevEquiv t ht ℓ, g⟫`
(`Rd.BoundedLipschitzDomain.dualBoundarySobolevEquiv_apply`). The identification depends on the
chosen Hilbert norm, that is, on the charts and on the resolution of unity `ψ⁰`. -/
noncomputable def dualBoundarySobolevEquiv (t : ℝ) (ht : 0 < t) :
    Ω.DualBoundarySobolev t ≃ₗᵢ⋆[ℂ] Ω.BoundarySobolev t :=
  haveI : Fact (0 < t) := ⟨ht⟩
  (InnerProductSpace.toDual ℂ (Ω.BoundarySobolev t)).symm

/-- Every functional on `H^t(Γ)` is the inner product with its representing element. -/
theorem dualBoundarySobolevEquiv_apply {t : ℝ} (ht : 0 < t) (ℓ : Ω.DualBoundarySobolev t)
    (g : Ω.BoundarySobolev t) :
    ℓ g = ⟪Ω.dualBoundarySobolevEquiv t ht ℓ, g⟫_ℂ := by
  have : Fact (0 < t) := ⟨ht⟩
  rw [dualBoundarySobolevEquiv, InnerProductSpace.toDual_symm_apply]

/-- **The norm of `H^t(Γ)` by the Sobolev–Slobodeckij norm on `Γ`**, `0 < t < 1`: there is
`C < ∞` with `‖g‖²_{H^t(Γ)} ≤ C (‖g‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |g(y) - g(x)|² / |y - x|^(n-1+2t) dσ dσ)`
and the reverse bound, for every `g ∈ H^t(Γ)`: the norm equivalence with `B^t_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_gagliardoEmbedding_norm_equiv`), the bounds of Gagliardo's form
on `Γ` by the chart-wise norm (`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`) and of `L_2(Γ)` by
`B^t_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.exists_eLpNorm_le_boundaryBesovNorm`). -/
theorem exists_boundarySobolev_norm_equiv_slobodeckij {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundarySobolev t,
      ‖g‖ₑ ^ 2 ≤ C * (‖g.toLp‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 t g.toLp) ∧
        ‖g.toLp‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 t g.toLp ≤ C * ‖g‖ₑ ^ 2 := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_gagliardoEmbedding_norm_equiv ht
  obtain ⟨C₀, hC₀, h₀⟩ := Ω.exists_eLpNorm_le_boundaryBesovNorm (p := 2) Ω.boundaryPartition t 2
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundarySlobodeckijForm_le (p := 2) Ω.boundaryPartition
    two_ne_top ht
  obtain ⟨C₃, hC₃, h₃⟩ := Ω.exists_boundaryBesovNorm_rpow_le (p := 2) Ω.boundaryPartition
    two_ne_top ht ht1
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h₂ h₃
  refine ⟨C₁ ^ 2 * C₃ + (C₀ ^ 2 + C₂) * C₁ ^ 2, ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.pow_ne_top hC₁) hC₃, ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.pow_ne_top hC₀, hC₂⟩) (ENNReal.pow_ne_top hC₁)⟩, fun g => ⟨?_, ?_⟩⟩
  · have hB := (h₁ g).2.trans_eq (congrArg (C₁ * ·) (BoundaryBesov.enorm_eq g))
    rw [enorm_boundarySobolev]
    calc _ ≤ (C₁ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp) ^ 2 :=
          pow_le_pow_left₀ zero_le hB 2
      _ ≤ C₁ ^ 2 * (C₃ * (‖g.toLp‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 t g.toLp)) := by
          rw [mul_pow, Lp.enorm_def]
          exact mul_le_mul' le_rfl (h₃ _ (Lp.aestronglyMeasurable _))
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · have hB := (BoundaryBesov.enorm_eq g).symm.trans_le (h₁ g).1
    rw [enorm_boundarySobolev]
    calc _ ≤ (C₀ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp) ^ 2 +
          C₂ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp ^ 2 := by
          rw [Lp.enorm_def]
          exact add_le_add (pow_le_pow_left₀ zero_le (h₀ _ (Lp.aestronglyMeasurable _)) 2)
            (h₂ _)
      _ = (C₀ ^ 2 + C₂) * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp ^ 2 := by ring
      _ ≤ (C₀ ^ 2 + C₂) * (C₁ * ‖Ω.gagliardoEmbedding t g‖ₑ) ^ 2 :=
          mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hB 2)
      _ = (C₀ ^ 2 + C₂) * C₁ ^ 2 * ‖Ω.gagliardoEmbedding t g‖ₑ ^ 2 := by ring
      _ ≤ _ := mul_le_mul' le_add_self le_rfl

/-! ### The trace onto `H^{s-1/2}(Γ)` -/

/-- **The trace space of `H^s(Ω)` is isomorphic to `H^{s-1/2}(Γ)`**, `1/2 < s < 3/2` (McLean,
Theorem 3.38): `w ↦ τ_s w`, the isomorphism with `B^{s-1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesov`) followed by the identity onto
`H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`). For `s = 1`,
`Rd.BoundedLipschitzDomain.traceSpaceOneEquivBoundarySobolevHalf` has values in `H^{1/2}(Γ)`. -/
noncomputable def traceSpaceEquivBoundarySobolev (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.TraceSpace s hs hs' ≃L[ℂ] Ω.BoundarySobolev (s - 1 / 2) :=
  (Ω.traceSpaceEquivBoundaryBesov s hs hs').trans
    (Ω.boundarySobolevEquivBoundaryBesov (s - 1 / 2) (sub_pos.2 hs)).symm

/-- The isomorphism `Ω.TraceSpace s ≅ H^{s-1/2}(Γ)` sends `w` to `τ_s w ∈ L_2(Γ)`. -/
theorem toLp_traceSpaceEquivBoundarySobolev {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (w : Ω.TraceSpace s hs hs') :
    (Ω.traceSpaceEquivBoundarySobolev s hs hs' w).toLp = Ω.traceL2 s hs hs' w :=
  rfl

/-- **The trace space of `H^1(Ω)` is isomorphic to `H^{1/2}(Γ)`**: the isomorphism
`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev` at `s = 1`, followed by the
identification of `H^{1 - 1/2}(Γ)` with `H^{1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.boundarySobolevCongr`). -/
noncomputable def traceSpaceOneEquivBoundarySobolevHalf :
    Ω.TraceSpace 1 ≃L[ℂ] Ω.BoundarySobolev (1 / 2) :=
  (Ω.traceSpaceEquivBoundarySobolev 1).trans
    (Ω.boundarySobolevCongr (by norm_num)).toContinuousLinearEquiv

/-- The isomorphism `Ω.TraceSpace 1 ≅ H^{1/2}(Γ)` sends `w` to `τ_1 w ∈ L_2(Γ)`. -/
theorem toLp_traceSpaceOneEquivBoundarySobolevHalf (w : Ω.TraceSpace 1) :
    (Ω.traceSpaceOneEquivBoundarySobolevHalf w).toLp = (Ω.traceL2 1) w :=
  Ω.toLp_boundarySobolevCongr _ _

/-- **The trace `H^s(Ω) → H^{s-1/2}(Γ)`**, `1/2 < s < 3/2` (McLean, Theorem 3.38): the trace
`γ_s` onto the trace space followed by the isomorphism with `H^{s-1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev`). It is onto, with the bounded linear
right inverse `Rd.BoundedLipschitzDomain.sobolevExtend`, its kernel is the trace kernel, and its
function in `L_2(Γ)` is the Besov trace of `1_Ω ι_s u`
(`Rd.BoundedLipschitzDomain.toLp_sobolevTrace_eq_besovTrace`). -/
noncomputable def sobolevTrace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    RestrictionSpace s Ω.toOpens →L[ℂ] Ω.BoundarySobolev (s - 1 / 2) :=
  (Ω.traceSpaceEquivBoundarySobolev s hs hs' :
    Ω.TraceSpace s hs hs' →L[ℂ] Ω.BoundarySobolev (s - 1 / 2)) ∘L Ω.trace s hs hs'

/-- **The extension `H^{s-1/2}(Γ) → H^s(Ω)`**, `1/2 < s < 3/2`: the inverse of the isomorphism
`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev` followed by the extension `E_s`, a
bounded linear right inverse of the trace
(`Rd.BoundedLipschitzDomain.sobolevTrace_sobolevExtend`). -/
noncomputable def sobolevExtend (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.BoundarySobolev (s - 1 / 2) →L[ℂ] RestrictionSpace s Ω.toOpens :=
  Ω.extend s hs hs' ∘L ((Ω.traceSpaceEquivBoundarySobolev s hs hs').symm :
    Ω.BoundarySobolev (s - 1 / 2) →L[ℂ] Ω.TraceSpace s hs hs')

/-- The trace into `H^{s-1/2}(Γ)` has the function `γ^s_{L_2} u ∈ L_2(Γ)`
(`Rd.BoundedLipschitzDomain.boundaryTraceL2`). -/
theorem toLp_sobolevTrace (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.sobolevTrace s hs hs' u).toLp = Ω.boundaryTraceL2 s hs hs' u :=
  rfl

/-- **The extension is a right inverse of the trace**: `γ(E g) = g` for every
`g ∈ H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.trace_extend`). -/
theorem sobolevTrace_sobolevExtend (s : ℝ) (g : Ω.BoundarySobolev (s - 1 / 2))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.sobolevTrace s hs hs' (Ω.sobolevExtend s hs hs' g) = g := by
  change Ω.traceSpaceEquivBoundarySobolev s hs hs' (Ω.trace s hs hs'
    (Ω.extend s hs hs' ((Ω.traceSpaceEquivBoundarySobolev s hs hs').symm g))) = g
  rw [trace_extend, ContinuousLinearEquiv.apply_symm_apply]

/-- **The kernel of the trace `H^s(Ω) → H^{s-1/2}(Γ)` is the trace kernel**: the isomorphism with
`H^{s-1/2}(Γ)` is injective (`Rd.BoundedLipschitzDomain.ker_trace`). -/
theorem ker_sobolevTrace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.sobolevTrace s hs hs').ker = Ω.traceKer s hs hs' := by
  rw [← Ω.ker_trace s hs hs']
  ext u
  change Ω.traceSpaceEquivBoundarySobolev s hs hs' (Ω.trace s hs hs' u) = 0 ↔
    Ω.trace s hs hs' u = 0
  exact (Ω.traceSpaceEquivBoundarySobolev s hs hs').map_eq_zero_iff

/-- **Restrictions of `H^s(V)` lie in `B^s_{2,2}(Ω)`**, `0 < s < 2`: for `U ∈ H^s(V)`,
`N_Ω(1_Ω ι_s U) ≤ ‖ι_s U‖_2 + ‖(2^(ks) ω_2(ι_s U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with
`C = Rd.sobolevBesovConst V s 2` (`Rd.modNormOn_le_modNorm_of_indicatorLp`,
`Rd.modNorm_sobolevToL2_le`). -/
theorem modNormOn_indicatorLp_sobolevToL2_le {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (U : H^{s}(V)) :
    modNormOn Ω.measurableSet 2 s 2 (indicatorLp Ω.measurableSet (sobolevToL2 hs.le U)) ≤
      sobolevBesovConst V s 2 * ‖U‖ₑ :=
  (modNormOn_le_modNorm_of_indicatorLp Ω.measurableSet 2 s 2
    (indicatorLp_indicatorLp _ _).symm).trans
    (modNorm_sobolevToL2_le hs (r := 2) (by exact_mod_cast hs2) U)

/-- **The restriction `H^s(Ω) → B^s_{2,2}(Ω)`**, `0 < s < 2`: `u ↦ 1_Ω ι_s u`, the `L_2` function
of `u` cut off outside `Ω`, in the Banach space `B^s_{2,2}(Ω)` of
`Rd.BoundedLipschitzDomain.DomainBesov` with differences of order `2`, bounded by
`Rd.BoundedLipschitzDomain.modNormOn_indicatorLp_sobolevToL2_le`. -/
noncomputable def restrictionToDomainBesov (s : ℝ) (hs : 0 < s) (hs2 : s < 2) :
    RestrictionSpace s Ω.toOpens →L[ℂ] Ω.DomainBesov 2 2 s 2 :=
  LinearMap.mkContinuous
    { toFun u := ⟨indicatorLp Ω.measurableSet (sobolevToL2 hs.le (u : H^{s}(V))),
        indicatorLp_indicatorLp _ _,
        (Ω.modNormOn_indicatorLp_sobolevToL2_le hs hs2 _).trans_lt (ENNReal.mul_lt_top
          (sobolevBesovConst_ne_top hs (r := 2) (by exact_mod_cast hs2)).lt_top enorm_lt_top)⟩
      map_add' u w := DomainBesov.ext (by
        change indicatorLp Ω.measurableSet (sobolevToL2 hs.le ((u : H^{s}(V)) + w)) = _
        rw [map_add, map_add]
        rfl)
      map_smul' c u := DomainBesov.ext (by
        change indicatorLp Ω.measurableSet (sobolevToL2 hs.le (c • (u : H^{s}(V)))) = _
        rw [map_smul, map_smul]
        rfl) }
    (sobolevBesovConst V s 2).toReal fun u => by
      refine norm_le_toReal_mul_of_enorm_le
        (sobolevBesovConst_ne_top hs (r := 2) (by exact_mod_cast hs2)) ?_
      rw [DomainBesov.enorm_eq]
      exact Ω.modNormOn_indicatorLp_sobolevToL2_le hs hs2 _

/-- The restriction sends `u` to `1_Ω ι_s u`. -/
theorem toLp_restrictionToDomainBesov (s : ℝ) (hs : 0 < s) (hs2 : s < 2)
    (u : RestrictionSpace s Ω.toOpens) :
    (Ω.restrictionToDomainBesov s hs hs2 u).toLp =
      indicatorLp Ω.measurableSet (sobolevToL2 hs.le (u : H^{s}(V))) :=
  rfl

/-- **The trace into `H^{s-1/2}(Γ)` is the Besov trace at `p = q = 2`**, `1/2 < s < 3/2`: the
function in `L_2(Γ)` of the trace of `u ∈ H^s(Ω)` is the Besov trace
(`Rd.BoundedLipschitzDomain.besovTrace`) of `1_Ω ι_s u ∈ B^s_{2,2}(Ω)`; both are the boundary
trace `Tr_Γ ι_s u` (`Rd.BoundedLipschitzDomain.besovTrace_ae` with the extension `ι_s u`,
`Rd.BoundedLipschitzDomain.boundaryTraceL2_apply_ae`). -/
theorem toLp_sobolevTrace_eq_besovTrace (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.sobolevTrace s hs hs' u).toLp = (Ω.besovTrace two_ne_top s 2 (by norm_num; linarith)
      (by norm_num; linarith) (Ω.restrictionToDomainBesov s (one_half_pos.trans hs)
        (by linarith) u)).toLp := by
  have hs0 : 0 < s := one_half_pos.trans hs
  rw [Ω.toLp_sobolevTrace s u hs hs']
  refine Lp.ext ((Ω.boundaryTraceL2_apply_ae Ω.boundaryPartition s u hs hs').trans ?_)
  exact (Ω.besovTrace_ae two_ne_top _ _ _ (F := sobolevToL2 hs0.le (u : H^{s}(V))) rfl
    ((modNorm_sobolevToL2_le hs0 (r := 2) (by norm_num; linarith) _).trans_lt
      (ENNReal.mul_lt_top (sobolevBesovConst_ne_top hs0 (r := 2)
        (by norm_num; linarith)).lt_top enorm_lt_top))).symm

end BoundedLipschitzDomain

end Rd
