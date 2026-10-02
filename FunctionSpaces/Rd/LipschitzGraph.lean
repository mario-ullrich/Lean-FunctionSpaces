/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.LocalMeans
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Lipschitz graph domains

A **Lipschitz graph domain** in `V` is `Ω = {x : φ(x) < ⟪x, e⟫}` for a unit vector `e` and an
`M`-Lipschitz function `φ` that is constant along `e` (`Rd.LipschitzGraph`); for `V = ℝ^d` and
`e = e_d` this is `{x_d > φ(x_1, …, x_(d-1))}`. With the cone
`K = {y : M ‖y - ⟪y, e⟫ e‖ < ⟪y, e⟫}` (`Rd.LipschitzGraph.cone`), `Ω + K ⊆ Ω`
(`Rd.LipschitzGraph.add_mem`): a step into the cone raises `⟪·, e⟫` faster than `φ`. The cone is
closed under positive scaling and contains a ball around `e/4` (`Rd.LipschitzGraph.ball_subset_cone`).

The **cone bump** (`Rd.LipschitzGraph.coneBump`) is a bump for local means supported in
`-K ∩ B(0, 1/2)`. A kernel `k` is **supported in `-K`** if `k(y) ≠ 0` implies `-y ∈ K`
(`Rd.LipschitzGraph.ConeSupported`); this passes to sums, differences and dilations, so the moment
kernels, the local means kernels and the dual kernels of the cone bump are supported in `-K`.

**Support principle** (`Rd.LipschitzGraph.conv_indicator_eq`): for a kernel supported in `-K` and
`x ∈ Ω`, `(k ⋆ f)(x)` depends only on `f` on `Ω`, since `x - y ∈ x + K ⊆ Ω` whenever
`k(y) ≠ 0`. On `L_p`, with the cut-off `f ↦ 1_Ω f` (`Rd.LipschitzGraph.cutoff`, from
`Rd.indicatorLp`): `1_Ω (k ⋆ (1_Ω h)) = 1_Ω (k ⋆ h)` (`Rd.LipschitzGraph.cutoff_convLp_cutoff`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

namespace Rd

/-! ### Multiplication by an indicator on `L_p` -/

section Indicator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- `1_s g ∈ L_p` for `g ∈ L_p`. -/
theorem memLp_indicator_coe {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    MemLp (s.indicator (g : α → ℂ)) p μ :=
  (Lp.memLp g).indicator hs

omit [Fact (1 ≤ p)] in
/-- `‖1_s g‖_p ≤ ‖g‖_p` for the class of `1_s g`. -/
theorem norm_toLp_indicator_le {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    ‖(memLp_indicator_coe hs g).toLp _‖ ≤ ‖g‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_indicator_le _ hs)

/-- **Multiplication by the indicator of a measurable set** as an operator on `L_p` of norm at
most `1`. -/
noncomputable def indicatorLp {s : Set α} (hs : MeasurableSet s) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_indicator_coe hs g).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_coe hs (f + g))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_coe hs f)
        have e3 := MemLp.coeFn_toLp (memLp_indicator_coe hs g)
        have e4 := Lp.coeFn_add f g
        have e5 := Lp.coeFn_add ((memLp_indicator_coe hs f).toLp _)
          ((memLp_indicator_coe hs g).toLp _)
        filter_upwards [e1, e2, e3, e4, e5] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, h4, Pi.add_apply]
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_coe hs (c • f))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_coe hs f)
        have e3 := Lp.coeFn_smul c f
        have e4 := Lp.coeFn_smul c ((memLp_indicator_coe hs f).toLp _)
        filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, h3, Pi.smul_apply]
        · simp only [Set.indicator_of_notMem hx, smul_zero] }
    1 (fun g => by
      rw [one_mul]
      exact norm_toLp_indicator_le hs g)

/-- Multiplication by an indicator is multiplication by the indicator, almost everywhere. -/
theorem indicatorLp_apply_ae {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    indicatorLp hs g =ᵐ[μ] s.indicator g :=
  MemLp.coeFn_toLp (memLp_indicator_coe hs g)

/-- `‖1_s g‖_p ≤ ‖g‖_p`. -/
theorem enorm_indicatorLp_le {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    ‖indicatorLp hs g‖ₑ ≤ ‖g‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hs g)]
  exact eLpNorm_indicator_le _ hs

end Indicator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Lipschitz graph domains and their cones -/

variable (V) in
/-- A **Lipschitz graph domain** `{x : φ(x) < ⟪x, e⟫}`, given by a unit vector `e` and a function
`φ` that is `M`-Lipschitz and constant along `e`. -/
structure LipschitzGraph where
  /-- The upward direction. -/
  e : V
  norm_e : ‖e‖ = 1
  /-- The Lipschitz constant. -/
  M : ℝ
  M_nonneg : 0 ≤ M
  /-- The graph function. -/
  phi : V → ℝ
  lipschitz : ∀ x y, |phi x - phi y| ≤ M * ‖x - y‖
  const : ∀ (x : V) (t : ℝ), phi (x + t • e) = phi x

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The domain `{x : φ(x) < ⟪x, e⟫}`. -/
def domain : Set V := {x | Ω.phi x < inner ℝ x Ω.e}

/-- The cone `K = {y : M ‖y - ⟪y, e⟫ e‖ < ⟪y, e⟫}`. -/
def cone : Set V := {y | Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e}

/-- **Steps into the cone stay in the domain**: `Ω + K ⊆ Ω`. -/
theorem add_mem {x y : V} (hx : x ∈ Ω.domain) (hy : y ∈ Ω.cone) : x + y ∈ Ω.domain := by
  set d := y - inner ℝ y Ω.e • Ω.e
  have h1 : Ω.phi (x + y) = Ω.phi (x + d) := by
    rw [← Ω.const (x + d) (inner ℝ y Ω.e)]
    congr 1
    simp only [d]
    abel
  have h2 : Ω.phi (x + d) ≤ Ω.phi x + Ω.M * ‖d‖ := by
    have h := Ω.lipschitz (x + d) x
    rw [add_sub_cancel_left] at h
    linarith [le_abs_self (Ω.phi (x + d) - Ω.phi x)]
  have hx' : Ω.phi x < inner ℝ x Ω.e := hx
  have hy' : Ω.M * ‖d‖ < inner ℝ y Ω.e := hy
  show Ω.phi (x + y) < inner ℝ (x + y) Ω.e
  rw [inner_add_left, h1]
  linarith

/-- The cone is closed under positive scaling. -/
theorem smul_mem_cone {c : ℝ} (hc : 0 < c) {y : V} (hy : y ∈ Ω.cone) : c • y ∈ Ω.cone := by
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e := hy
  show Ω.M * ‖c • y - inner ℝ (c • y) Ω.e • Ω.e‖ < inner ℝ (c • y) Ω.e
  rw [real_inner_smul_left, ← smul_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hc.le]
  nlinarith

/-- Multiples of a step in the cone stay in the domain: `x + l h ∈ Ω`. -/
theorem add_nsmul_mem {x h : V} (hx : x ∈ Ω.domain) (hh : h ∈ Ω.cone) (l : ℕ) :
    x + (l : ℝ) • h ∈ Ω.domain := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simpa using hx
  · exact Ω.add_mem hx (Ω.smul_mem_cone (by exact_mod_cast hl) hh)

/-- The graph function is continuous. -/
theorem continuous_phi : Continuous Ω.phi :=
  (LipschitzWith.of_dist_le_mul (K := ⟨Ω.M, Ω.M_nonneg⟩) fun x y => by
    rw [Real.dist_eq, dist_eq_norm]
    exact Ω.lipschitz x y).continuous

/-- The domain is open. -/
theorem isOpen_domain : IsOpen Ω.domain :=
  isOpen_lt Ω.continuous_phi (continuous_id.inner continuous_const)

/-- The radius `1/(8(M + 1))` of a ball around `e/4` inside the cone. -/
noncomputable def coneRadius : ℝ := 1 / (8 * (Ω.M + 1))

/-- The radius is positive. -/
theorem coneRadius_pos : 0 < Ω.coneRadius := by
  have := Ω.M_nonneg
  unfold coneRadius
  positivity

/-- `ρ ≤ 1/8`. -/
theorem coneRadius_le : Ω.coneRadius ≤ 1 / 8 := by
  have := Ω.M_nonneg
  unfold coneRadius
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `(2M + 1) ρ ≤ 1/4`. -/
theorem two_mul_add_one_mul_coneRadius_le : (2 * Ω.M + 1) * Ω.coneRadius ≤ 1 / 4 := by
  have := Ω.M_nonneg
  unfold coneRadius
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **A ball inside the cone**: `B(e/4, ρ) ⊆ K`, since the component orthogonal to `e` of a point
of the ball is at most `2ρ` and its component along `e` at least `1/4 - ρ`. -/
theorem ball_subset_cone : Metric.ball ((1 / 4 : ℝ) • Ω.e) Ω.coneRadius ⊆ Ω.cone := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  set d := w - (1 / 4 : ℝ) • Ω.e with hd
  have hwd : w = (1 / 4 : ℝ) • Ω.e + d := by rw [hd]; abel
  have hee : inner ℝ Ω.e Ω.e = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, Ω.norm_e, one_pow]
  have hde : |inner ℝ d Ω.e| ≤ ‖d‖ := by
    have h := abs_real_inner_le_norm d Ω.e
    rwa [Ω.norm_e, mul_one] at h
  have hinner : inner ℝ w Ω.e = 1 / 4 + inner ℝ d Ω.e := by
    rw [hwd, inner_add_left, real_inner_smul_left, hee, mul_one]
  have hperp : w - inner ℝ w Ω.e • Ω.e = d - inner ℝ d Ω.e • Ω.e := by
    rw [hinner, add_smul]
    rw [hwd]
    abel
  have hnorm : ‖d - inner ℝ d Ω.e • Ω.e‖ ≤ 2 * ‖d‖ := by
    calc ‖d - inner ℝ d Ω.e • Ω.e‖ ≤ ‖d‖ + ‖inner ℝ d Ω.e • Ω.e‖ := norm_sub_le _ _
      _ = ‖d‖ + |inner ℝ d Ω.e| := by rw [norm_smul, Real.norm_eq_abs, Ω.norm_e, mul_one]
      _ ≤ 2 * ‖d‖ := by linarith
  have hM := Ω.M_nonneg
  have h1 : Ω.M * ‖d - inner ℝ d Ω.e • Ω.e‖ ≤ Ω.M * (2 * ‖d‖) :=
    mul_le_mul_of_nonneg_left hnorm hM
  have h2 : (2 * Ω.M + 1) * ‖d‖ < (2 * Ω.M + 1) * Ω.coneRadius :=
    mul_lt_mul_of_pos_left hw (by positivity)
  have h3 := Ω.two_mul_add_one_mul_coneRadius_le
  have h4 : -‖d‖ ≤ inner ℝ d Ω.e := (abs_le.1 hde).1
  show Ω.M * ‖w - inner ℝ w Ω.e • Ω.e‖ < inner ℝ w Ω.e
  rw [hperp, hinner]
  nlinarith

/-! ### Kernels supported in `-K` -/

/-- A kernel `k` is **supported in `-K`** if `k(y) ≠ 0` implies `-y ∈ K`. -/
def ConeSupported (k : V → ℂ) : Prop := ∀ y, k y ≠ 0 → -y ∈ Ω.cone

variable {Ω}

/-- Sums of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.add {k k' : V → ℂ} (hk : Ω.ConeSupported k) (hk' : Ω.ConeSupported k') :
    Ω.ConeSupported (k + k') := fun y hy => by
  by_cases h : k y = 0
  · exact hk' y fun h' => hy (by simp [h, h'])
  · exact hk y h

/-- Differences of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.sub {k k' : V → ℂ} (hk : Ω.ConeSupported k) (hk' : Ω.ConeSupported k') :
    Ω.ConeSupported (k - k') := fun y hy => by
  by_cases h : k y = 0
  · exact hk' y fun h' => hy (by simp [h, h'])
  · exact hk y h

/-- Dilations of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.dilate {k : V → ℂ} (hk : Ω.ConeSupported k) {c : ℝ} (hc : 0 < c) :
    Ω.ConeSupported (Rd.dilate c k) := fun y hy => by
  have hky : k (c • y) ≠ 0 := fun h => hy (by simp [Rd.dilate, h])
  have h := Ω.smul_mem_cone (inv_pos.2 hc) (hk (c • y) hky)
  rwa [smul_neg, inv_smul_smul₀ hc.ne'] at h

/-- Finite combinations of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.finsetSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) {k : ι → V → ℂ}
    (hk : ∀ i ∈ s, Ω.ConeSupported (k i)) :
    Ω.ConeSupported (fun x => ∑ i ∈ s, a i * k i x) := fun y hy => by
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  exact hk i hi y (right_ne_zero_of_mul hne)

variable (Ω)

/-! ### The cone bump -/

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The smooth bump around `-e/4` with outer radius `ρ`. -/
noncomputable def coneBumpBase : ContDiffBump (-((1 / 4 : ℝ) • Ω.e)) :=
  ⟨Ω.coneRadius / 2, Ω.coneRadius, by have := Ω.coneRadius_pos; positivity,
    by have := Ω.coneRadius_pos; linarith⟩

/-- The **cone bump**: a bump for local means supported in `-K ∩ B(0, 1/2)` (the normalised
`ContDiffBump` around `-e/4` of radius `ρ`). -/
noncomputable def coneBump : LocalMeansBump V where
  toFun z := ((Ω.coneBumpBase.normed volume z : ℝ) : ℂ)
  radius := 1 / 2
  radius_nonneg := by norm_num
  contDiff := Complex.ofRealCLM.contDiff.comp (Ω.coneBumpBase.contDiff_normed (n := ⊤))
  eq_zero z hz := by
    have hz' : z ∉ Function.support (Ω.coneBumpBase.normed volume) := by
      rw [Ω.coneBumpBase.support_normed_eq, Metric.mem_ball, dist_eq_norm, sub_neg_eq_add]
      intro h
      have h1 : ‖z‖ ≤ ‖z + (1 / 4 : ℝ) • Ω.e‖ + ‖(1 / 4 : ℝ) • Ω.e‖ := by
        have := norm_sub_le (z + (1 / 4 : ℝ) • Ω.e) ((1 / 4 : ℝ) • Ω.e)
        rwa [add_sub_cancel_right] at this
      rw [norm_smul, Ω.norm_e, mul_one, Real.norm_of_nonneg (by norm_num)] at h1
      have h2 : Ω.coneBumpBase.rOut = Ω.coneRadius := rfl
      rw [h2] at h
      linarith [Ω.coneRadius_le]
    rw [Function.notMem_support.1 hz', Complex.ofReal_zero]
  integral_eq_one := by
    rw [integral_complex_ofReal, Ω.coneBumpBase.integral_normed, Complex.ofReal_one]

/-- The cone bump vanishes outside the ball of radius `1/2`. -/
theorem coneBump_radius : Ω.coneBump.radius = 1 / 2 := rfl

/-- The cone bump is supported in `-K`. -/
theorem coneSupported_coneBump : Ω.ConeSupported Ω.coneBump.toFun := fun y hy => by
  have hy' : y ∈ Function.support (Ω.coneBumpBase.normed volume) := fun h =>
    hy (by simp [coneBump, h])
  rw [Ω.coneBumpBase.support_normed_eq, Metric.mem_ball, dist_eq_norm] at hy'
  refine Ω.ball_subset_cone ?_
  rw [Metric.mem_ball, dist_eq_norm, show -y - (1 / 4 : ℝ) • Ω.e = -(y - -((1 / 4 : ℝ) • Ω.e))
    by abel, norm_neg]
  exact hy'

/-- The moment kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_momentKernel (L : ℕ) :
    Ω.ConeSupported (momentKernel Ω.coneBump.toFun L) :=
  ConeSupported.finsetSum _ _ fun _ _ => (Ω.coneSupported_coneBump).dilate (by positivity)

/-- The dilated moment kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_scaled (L j : ℕ) : Ω.ConeSupported (Ω.coneBump.scaled L j) :=
  (Ω.coneSupported_momentKernel L).dilate (by positivity)

/-- The local means kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_kernel (L j : ℕ) : Ω.ConeSupported (Ω.coneBump.kernel L j) := by
  cases j with
  | zero => exact Ω.coneSupported_scaled L 0
  | succ j => exact (Ω.coneSupported_scaled L (j + 1)).sub (Ω.coneSupported_scaled L j)

/-- The dual kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_dual (L j : ℕ) : Ω.ConeSupported (Ω.coneBump.dual L j) := by
  cases j with
  | zero => exact Ω.coneSupported_scaled L 0
  | succ j => exact (Ω.coneSupported_scaled L (j + 1)).add (Ω.coneSupported_scaled L j)

/-! ### The support principle -/

omit [FiniteDimensional ℝ V] in
/-- The domain is measurable. -/
theorem measurableSet_domain : MeasurableSet Ω.domain := Ω.isOpen_domain.measurableSet

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **The support principle**: for a kernel supported in `-K` and `x ∈ Ω`,
`(k ⋆ (1_Ω f))(x) = (k ⋆ f)(x)`. -/
theorem conv_indicator_eq {k : V → ℂ} (hk : Ω.ConeSupported k) (f : V → ℂ) {x : V}
    (hx : x ∈ Ω.domain) (μ : Measure V) :
    conv k (Ω.domain.indicator f) μ x = conv k f μ x := by
  rw [conv_apply, conv_apply]
  congr 1
  funext y
  by_cases hy : k y = 0
  · simp [hy]
  · have hmem : x - y ∈ Ω.domain := by
      have h := Ω.add_mem hx (hk y hy)
      rwa [← sub_eq_add_neg] at h
    rw [Set.indicator_of_mem hmem]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **cut-off** `f ↦ 1_Ω f` on `L_p`. -/
noncomputable def cutoff : Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  indicatorLp Ω.measurableSet_domain

/-- The cut-off is `1_Ω f` almost everywhere. -/
theorem cutoff_apply_ae (f : Lp ℂ p (volume : Measure V)) :
    Ω.cutoff f =ᵐ[volume] Ω.domain.indicator f :=
  indicatorLp_apply_ae Ω.measurableSet_domain f

/-- `‖1_Ω f‖_p = ‖f‖_{L_p(Ω)}`. -/
theorem enorm_cutoff (f : Lp ℂ p (volume : Measure V)) :
    ‖Ω.cutoff f‖ₑ = eLpNorm (Ω.domain.indicator f) p volume := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (Ω.cutoff_apply_ae f)]

/-- `‖1_Ω f‖_p ≤ ‖f‖_p`. -/
theorem enorm_cutoff_le (f : Lp ℂ p (volume : Measure V)) : ‖Ω.cutoff f‖ₑ ≤ ‖f‖ₑ :=
  enorm_indicatorLp_le _ f

/-- Elements of `L_p` with the same cut-off agree almost everywhere on `Ω`. -/
theorem indicator_ae_eq_of_cutoff_eq {F f : Lp ℂ p (volume : Measure V)}
    (hFf : Ω.cutoff F = Ω.cutoff f) : Ω.domain.indicator F =ᵐ[volume] Ω.domain.indicator f := by
  filter_upwards [Ω.cutoff_apply_ae F, Ω.cutoff_apply_ae f] with x h1 h2
  rw [← h1, ← h2, hFf]

/-- **The support principle on `L_p`**: `1_Ω (k ⋆ (1_Ω h)) = 1_Ω (k ⋆ h)` for an integrable
kernel supported in `-K`. -/
theorem cutoff_convLp_cutoff (hp : p ≠ ∞) {k : V → ℂ} (hk : Integrable k)
    (hks : Ω.ConeSupported k) (h : Lp ℂ p (volume : Measure V)) :
    Ω.cutoff (convLp hp hk (Ω.cutoff h)) = Ω.cutoff (convLp hp hk h) := by
  refine Lp.ext ?_
  have h3 : conv k (Ω.cutoff h : V → ℂ) volume = conv k (Ω.domain.indicator h) volume :=
    conv_congr_ae (indicatorLp_apply_ae Ω.measurableSet_domain h)
  filter_upwards [indicatorLp_apply_ae Ω.measurableSet_domain (convLp hp hk (Ω.cutoff h)),
    convLp_apply_ae hp hk (Ω.cutoff h),
    indicatorLp_apply_ae Ω.measurableSet_domain (convLp hp hk h), convLp_apply_ae hp hk h]
    with x hx1 hx2 hx4 hx5
  change (indicatorLp Ω.measurableSet_domain (convLp hp hk (Ω.cutoff h)) : V → ℂ) x =
    (indicatorLp Ω.measurableSet_domain (convLp hp hk h) : V → ℂ) x
  rw [hx1, hx4]
  by_cases hx : x ∈ Ω.domain
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hx2, hx5, h3,
      Ω.conv_indicator_eq hks _ hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- **Convolutions of functions that agree on `Ω` agree on `Ω`**: if `1_Ω F = 1_Ω f`, then
`1_Ω (k ⋆ F) = 1_Ω (k ⋆ f)` for an integrable kernel supported in `-K`. -/
theorem cutoff_convLp_eq (hp : p ≠ ∞) {k : V → ℂ} (hk : Integrable k)
    (hks : Ω.ConeSupported k) {F f : Lp ℂ p (volume : Measure V)}
    (hFf : Ω.cutoff F = Ω.cutoff f) :
    Ω.cutoff (convLp hp hk F) = Ω.cutoff (convLp hp hk f) := by
  rw [← Ω.cutoff_convLp_cutoff hp hk hks F, hFf, Ω.cutoff_convLp_cutoff hp hk hks f]

end LipschitzGraph

end Rd
