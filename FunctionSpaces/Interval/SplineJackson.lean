/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.QuasiInterp
public import FunctionSpaces.Interval.SplineInverse
public import FunctionSpaces.Interval.PiecewiseJackson

/-!
# Jackson's inequality for dyadic splines and the coincidence theorem

For `1 ≤ p < ∞`, `r ≥ 1` and `k ≥ r + 2`, the error of best approximation in `L_p[0, 1]` by splines
of order `r` and level `k` is bounded by the modulus of smoothness,
`E_{2^k}(f)_p ≤ C ω_r(f, 2^(-k), [0, 1])_p`.

The approximant is the quasi-interpolant `Q_k f` of `FunctionSpaces.Interval.QuasiInterp`. On
`I_{k,i}` it reproduces every polynomial `T_i` of degree `< r` and is bounded by the `L_p` norm on
the window `W_i = [(i + 1 - r) 2^(-k), (i + 1) 2^(-k)]` of `r` intervals, so
`‖f - Q_k f‖_{L_p(I_{k,i})} ≤ C ‖f - T_i‖_{L_p(W_i)}`. For continuous `f`, `T_i` is a Taylor
polynomial of the Steklov smoothing of `f`, forward on `[0, 3/4]` and backward on `[1/4, 1]`
(`Interval.exists_left_smoothing`, `Interval.exists_right_smoothing`); every window lies in one of
the two parts, and the windows overlap at most `r` times (`Interval.sum_lintegral_window_le`).
General `f ∈ L_p` follow by density (`Interval.exists_approxSeq_splineScheme_le`).

With the inverse inequality of order `r - 1 + 1/p` (`Interval.exists_inverse_splineScheme`) this
is a modulus compatible with the spline scheme (`Interval.splineModulusData`), and for
`1 ≤ q ≤ ∞` and `0 ≤ s < r - 1 + 1/p`,
`f ∈ A^s_q ↔ ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
(`Interval.memApprox_splineScheme_iff`): the approximation space of splines of order `r` is
`B^s_{p,q}[0, 1]` for `0 < s < r - 1 + 1/p`, beyond smoothness `1` for `r ≥ 2`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction
open ENNReal (dyadicWeight)

namespace Interval

/-- **Smoothing on the left part**: for continuous `F`, `r ≥ 1` and `k ≥ 2`, the Steklov smoothing
`g = S_δ F`, `δ = 2^(-k)/r²`, and its derivative `D = g^(r)` satisfy on `[0, 3/4]`
`‖F - g‖_p ≤ ω_r(F, 2^(-k))_p` and `‖D‖_p ≤ 2^(kr) 2^r r^(2r) ω_r(F, 2^(-k))_p`, and on every
`[a, b] ⊆ [0, 3/4]` there is `T` of degree `< r` with `‖g - T‖_{L_p[a,b]} ≤ (b - a)^r ‖D‖_{L_p[a,b]}`. -/
theorem exists_left_smoothing {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {k : ℕ} (hk : 2 ≤ k) :
    ∃ g D : ℝ → ℂ, Measurable g ∧ Measurable D ∧
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc 0 (3 / 4))) ≤
        modulus r p 0 1 F (1 / 2 ^ k) ∧
      eLpNorm D p (volume.restrict (Icc 0 (3 / 4))) ≤
        ENNReal.ofReal (2 ^ k) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * modulus r p 0 1 F (1 / 2 ^ k) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 3 / 4 → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (b - a) ^ r * eLpNorm D p (volume.restrict (Icc a b)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  set δ : ℝ := (1 / 2 ^ k) / r ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hrδ : (r : ℝ) * δ ≤ 1 / 2 ^ k := by
    rw [hδdef, show (r : ℝ) * (1 / 2 ^ k / r ^ 2) = (1 / 2 ^ k) / r by field_simp]
    exact div_le_self hL.le (by exact_mod_cast hr)
  have hrrδ : (r : ℝ) * (r * δ) = 1 / 2 ^ k := by rw [hδdef]; field_simp
  have hk4 : (1 : ℝ) / 2 ^ k ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hwb : (3 / 4 : ℝ) + r * (r * δ) ≤ 1 := by rw [hrrδ]; linarith
  have hg := contDiff_smooth hF r δ
  refine ⟨smooth r δ F, iteratedDeriv r (smooth r δ F), hg.continuous.measurable,
    (hg.continuous_iteratedDeriv r le_rfl).measurable, ?_, ?_, fun a b ha hab hb =>
      exists_eLpNorm_sub_polyFun_le hp r hg hab⟩
  · exact (eLpNorm_sub_smooth_le hF r hδ hp hp' le_rfl hwb).trans
      (modulus_mono r p 0 1 F hrδ)
  · refine (eLpNorm_iteratedDeriv_smooth_le hF r hδ hp le_rfl hwb).trans ?_
    have hinv : (ENNReal.ofReal δ)⁻¹ = (r : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 ^ k) := by
      rw [← ENNReal.ofReal_inv_of_pos hδ, hδdef, show ((1 / 2 ^ k) / (r : ℝ) ^ 2)⁻¹ =
        (r : ℝ) ^ 2 * 2 ^ k by field_simp, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
    rw [hinv, mul_pow, ← pow_mul]
    calc 2 ^ r * ((r : ℝ≥0∞) ^ (2 * r) * ENNReal.ofReal (2 ^ k) ^ r) *
          modulus r p 0 1 F (r * δ)
        ≤ 2 ^ r * ((r : ℝ≥0∞) ^ (2 * r) * ENNReal.ofReal (2 ^ k) ^ r) *
            modulus r p 0 1 F (1 / 2 ^ k) := by
          gcongr
          exact modulus_mono r p 0 1 F hrδ
      _ = _ := by ring

/-- **Smoothing on the right part**: the same on `[1/4, 1]`, by the reflection `x ↦ 1 - x`, which
preserves the modulus. -/
theorem exists_right_smoothing {F : ℝ → ℂ} (hF : Continuous F) {r : ℕ} (hr : 1 ≤ r)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {k : ℕ} (hk : 2 ≤ k) :
    ∃ g D : ℝ → ℂ, Measurable g ∧ Measurable D ∧
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc (1 / 4) 1)) ≤
        modulus r p 0 1 F (1 / 2 ^ k) ∧
      eLpNorm D p (volume.restrict (Icc (1 / 4) 1)) ≤
        ENNReal.ofReal (2 ^ k) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * modulus r p 0 1 F (1 / 2 ^ k) ∧
      ∀ a b : ℝ, 1 / 4 ≤ a → a ≤ b → b ≤ 1 → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (b - a) ^ r * eLpNorm D p (volume.restrict (Icc a b)) := by
  have hF' : Continuous fun x => F (1 - x) := hF.comp (continuous_const.sub continuous_id)
  obtain ⟨G, DG, hGm, hDm, h1, h2, h3⟩ := exists_left_smoothing hF' hr hp hp' hk
  have hmod : modulus r p 0 1 (fun x => F (1 - x)) (1 / 2 ^ k) = modulus r p 0 1 F (1 / 2 ^ k) := by
    have := modulus_reflect hF.measurable r p 0 1 (1 / 2 ^ k)
    simpa using this
  rw [hmod] at h1 h2
  refine ⟨fun x => G (1 - x), fun x => DG (1 - x), hGm.comp (measurable_const.sub measurable_id),
    hDm.comp (measurable_const.sub measurable_id), ?_, ?_, fun a b ha hab hb => ?_⟩
  · have h := eLpNorm_comp_sub_Icc (f := fun y => F (1 - y) - G y)
      ((hF'.measurable).sub hGm) p 1 (1 / 4) 1
    simp only [sub_sub_cancel] at h
    rw [h, show (1 : ℝ) - 1 = 0 by ring, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
    exact h1
  · rw [eLpNorm_comp_sub_Icc hDm p 1 (1 / 4) 1, show (1 : ℝ) - 1 = 0 by ring,
      show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num]
    exact h2
  · obtain ⟨T, hT, hTb⟩ := h3 (1 - b) (1 - a) (by linarith) (by linarith) (by linarith)
    refine ⟨T.comp (C (((1 : ℝ) : ℝ) : ℂ) + C (((-1 : ℝ) : ℝ) : ℂ) * X),
      comp_affine_mem_degreeLT hT _ _, ?_⟩
    have hfun : (fun x => G (1 - x) - polyFun (T.comp (C (((1 : ℝ) : ℝ) : ℂ) +
        C (((-1 : ℝ) : ℝ) : ℂ) * X)) x) = fun x => (fun y => G y - polyFun T y) (1 - x) := by
      funext x
      rw [polyFun_comp_affine]
      congr 2
      ring
    rw [hfun, eLpNorm_comp_sub_Icc (f := fun y => G y - polyFun T y)
      (hGm.sub (measurable_polyFun T)) p 1 a b,
      eLpNorm_comp_sub_Icc hDm p 1 a b]
    rw [show (1 - a) - (1 - b) = b - a by ring] at hTb
    exact hTb

/-- **Bounded overlap of the windows**: the windows `[(i + 1 - r) 2^(-k), (i + 1) 2^(-k)]`,
`i < 2^k`, cover every point at most `r` times: `∑_i ∫_{W_i} G ≤ r ∫ G`. -/
theorem sum_lintegral_window_le (r k : ℕ) (G : ℝ → ℝ≥0∞) :
    ∑ i ∈ Finset.range (2 ^ k), ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k),
      G x ≤ r * ∫⁻ x, G x := by
  have hL : (0 : ℝ) ≤ 1 / 2 ^ k := by positivity
  have hwin : ∀ i : ℕ, ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), G x ≤
      ∑ n ∈ Finset.range r, ∫⁻ x in Icc ((1 - (r : ℝ) + n) / 2 ^ k + i * (1 / 2 ^ k))
        ((1 - (r : ℝ) + n) / 2 ^ k + (i + 1) * (1 / 2 ^ k)), G x := fun i => by
    have h := lintegral_Icc_le_sum G (((i : ℝ) + 1 - r) / 2 ^ k) hL r
    rw [show ((i : ℝ) + 1 - r) / 2 ^ k + r * (1 / 2 ^ k) = ((i : ℝ) + 1) / 2 ^ k by
      field_simp; ring] at h
    refine h.trans_eq (Finset.sum_congr rfl fun n _ => ?_)
    congr 2
    field_simp
    ring_nf
  calc ∑ i ∈ Finset.range (2 ^ k), ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k)
        (((i : ℝ) + 1) / 2 ^ k), G x
      ≤ ∑ i ∈ Finset.range (2 ^ k), ∑ n ∈ Finset.range r,
          ∫⁻ x in Icc ((1 - (r : ℝ) + n) / 2 ^ k + i * (1 / 2 ^ k))
            ((1 - (r : ℝ) + n) / 2 ^ k + (i + 1) * (1 / 2 ^ k)), G x :=
        Finset.sum_le_sum fun i _ => hwin i
    _ = ∑ n ∈ Finset.range r, ∑ i ∈ Finset.range (2 ^ k),
          ∫⁻ x in Icc ((1 - (r : ℝ) + n) / 2 ^ k + i * (1 / 2 ^ k))
            ((1 - (r : ℝ) + n) / 2 ^ k + (i + 1) * (1 / 2 ^ k)), G x := Finset.sum_comm
    _ ≤ ∑ _n ∈ Finset.range r, ∫⁻ x, G x :=
        Finset.sum_le_sum fun n _ =>
          (sum_le_lintegral_Icc _ hL (2 ^ k)).trans (setLIntegral_le_lintegral _ _)
    _ = r * ∫⁻ x, G x := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Linearity of the quasi-interpolant -/

/-- The B-spline coordinates are additive. -/
theorem bcoord_add {r : ℕ} (hr : 1 ≤ r) {P Q : ℂ[X]} (hP : P ∈ degreeLT ℂ r)
    (hQ : Q ∈ degreeLT ℂ r) (j : ℕ) : bcoord hr (P + Q) j = bcoord hr P j + bcoord hr Q j := by
  by_cases hj : j < r
  · have h1 : P + Q ∈ degreeLT ℂ r ∧ j < r := ⟨Submodule.add_mem _ hP hQ, hj⟩
    have h2 : P ∈ degreeLT ℂ r ∧ j < r := ⟨hP, hj⟩
    have h3 : Q ∈ degreeLT ℂ r ∧ j < r := ⟨hQ, hj⟩
    simp only [bcoord, h1, h2, h3, and_self, ↓reduceDIte]
    rw [show (⟨P + Q, h1.1⟩ : degreeLT ℂ r) = ⟨P, hP⟩ + ⟨Q, hQ⟩ from rfl, map_add,
      Finsupp.add_apply]
  · have h : ∀ R : ℂ[X], ¬ (R ∈ degreeLT ℂ r ∧ j < r) := fun R h => hj h.2
    simp only [bcoord, h, ↓reduceDIte, add_zero]

/-- The B-spline coordinates are homogeneous. -/
theorem bcoord_C_mul {r : ℕ} (hr : 1 ≤ r) (c : ℂ) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (j : ℕ) :
    bcoord hr (C c * P) j = c * bcoord hr P j := by
  by_cases hj : j < r
  · have hcP : C c * P ∈ degreeLT ℂ r := by
      rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ hP
    have h1 : C c * P ∈ degreeLT ℂ r ∧ j < r := ⟨hcP, hj⟩
    have h2 : P ∈ degreeLT ℂ r ∧ j < r := ⟨hP, hj⟩
    simp only [bcoord, h1, h2, and_self, ↓reduceDIte]
    rw [show (⟨C c * P, h1.1⟩ : degreeLT ℂ r) = c • ⟨P, hP⟩ from
      Subtype.ext (by simp [smul_eq_C_mul]), map_smul, Finsupp.smul_apply, smul_eq_mul]
  · have h : ∀ R : ℂ[X], ¬ (R ∈ degreeLT ℂ r ∧ j < r) := fun R h => hj h.2
    simp only [bcoord, h, ↓reduceDIte, mul_zero]

/-- The B-spline coefficients are additive. -/
theorem bsplineCoef_add {r : ℕ} (hr : 1 ≤ r) {P Q : ℂ[X]} (hP : P ∈ degreeLT ℂ r)
    (hQ : Q ∈ degreeLT ℂ r) (n : ℤ) :
    bsplineCoef hr (P + Q) n = bsplineCoef hr P n + bsplineCoef hr Q n := by
  rw [bsplineCoef, add_comp, bcoord_add hr (comp_X_add_C_mem hP _) (comp_X_add_C_mem hQ _)]
  rfl

/-- The B-spline coefficients are homogeneous. -/
theorem bsplineCoef_C_mul {r : ℕ} (hr : 1 ≤ r) (c : ℂ) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r)
    (n : ℤ) : bsplineCoef hr (C c * P) n = c * bsplineCoef hr P n := by
  rw [bsplineCoef, mul_comp, C_comp, bcoord_C_mul hr c (comp_X_add_C_mem hP _)]
  rfl

/-- The rescaled local projections have degree `< r`. -/
theorem locProjScaled_mem (r k : ℕ) (g : ℝ → ℂ) (m : ℕ) : locProjScaled r k g m ∈ degreeLT ℂ r :=
  comp_affine_mem_degreeLT (locProj_mem r k g m) _ _

/-- **The quasi-interpolant coefficients are linear** on functions integrable on `J(n)`. -/
theorem qiCoeff_add_const_mul {r : ℕ} (hr : 1 ≤ r) (k : ℕ) {g₁ g₂ : ℝ → ℂ} (c : ℂ) {n : ℤ}
    (h₁ : IntegrableOn g₁ (dyadicIco k n.toNat)) (h₂ : IntegrableOn g₂ (dyadicIco k n.toNat)) :
    qiCoeff hr k (fun y => g₁ y + c * g₂ y) n = qiCoeff hr k g₁ n + c * qiCoeff hr k g₂ n := by
  have h₂' : IntegrableOn (fun y => c * g₂ y) (dyadicIco k n.toNat) := h₂.const_mul c
  have hloc : locProjScaled r k (fun y => g₁ y + c * g₂ y) n.toNat =
      locProjScaled r k g₁ n.toNat + C c * locProjScaled r k g₂ n.toNat := by
    rw [locProjScaled, show (fun y => g₁ y + c * g₂ y) = g₁ + fun y => c * g₂ y from rfl,
      locProj_add h₁ h₂', locProj_const_mul, add_comp, mul_comp, C_comp]
    rfl
  rw [qiCoeff, hloc, bsplineCoef_add hr (locProjScaled_mem r k _ _)
    (by rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (locProjScaled_mem r k _ _)),
    bsplineCoef_C_mul hr c (locProjScaled_mem r k _ _)]
  rfl

/-- **The error of the quasi-interpolant through a polynomial**: on `I_{k,i}`,
`g - Q_k g = (g - T) - Q_k(g - T)` for every polynomial `T` of degree `< r`. -/
theorem polyFun_qiPieces_sub {r : ℕ} (hr : 1 ≤ r) {k i : ℕ} (hi : i < 2 ^ k) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Icc 0 1)) {T : ℂ[X]} (hT : T ∈ degreeLT ℂ r) {x : ℝ}
    (hx : x ∈ dyadicIco k i) :
    polyFun (qiPieces hr k (fun y => g y - polyFun T y) i) x =
      polyFun (qiPieces hr k g i) x - polyFun T x := by
  have hT' := polyFun_qiPieces_of_eq hr (g := polyFun T) hT hi (fun _ _ _ _ _ => rfl) hx
  rw [← hT', polyFun_qiPieces_eq_sum_Ioc hr hi _ hx, polyFun_qiPieces_eq_sum_Ioc hr hi _ hx,
    polyFun_qiPieces_eq_sum_Ioc hr hi _ hx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hnk : n.toNat < 2 ^ k := by omega
  have hJ : dyadicIco k n.toNat ⊆ Icc 0 1 :=
    (dyadicIco_subset hnk).trans Ico_subset_Icc_self
  have h := qiCoeff_add_const_mul hr k (-1) (n := n) (hg.mono_set hJ)
    ((continuous_polyFun T).integrableOn_Icc.mono_set (hJ.trans le_rfl))
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  rw [h, sub_mul]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The window `W_i = [(i + 1 - r) 2^(-k), (i + 1) 2^(-k)]` (truncated at `0`) of the
quasi-interpolant on `I_{k,i}`. -/
def qiWindow (r k i : ℕ) : Set ℝ := Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k)

/-- The intervals `J(n)`, `i - r < n ≤ i`, lie in the window of `I_{k,i}`. -/
theorem dyadicIco_subset_qiWindow {r k i : ℕ} {n : ℤ} (hn : (i : ℤ) - r < n ∧ n ≤ i) :
    dyadicIco k n.toNat ⊆ qiWindow r k i := by
  intro x hx
  rw [dyadicIco, mem_Ico] at hx
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : ((i + 1 - r : ℕ) : ℝ) ≤ (n.toNat : ℝ) := by exact_mod_cast (by omega : i + 1 - r ≤ n.toNat)
  have h2 : (n.toNat : ℝ) + 1 ≤ (i : ℝ) + 1 := by exact_mod_cast (by omega : n.toNat + 1 ≤ i + 1)
  constructor
  · exact (div_le_div_of_nonneg_right h1 hpos.le).trans hx.1
  · exact hx.2.le.trans (div_le_div_of_nonneg_right h2 hpos.le)

/-- `I_{k,i}` lies in its window. -/
theorem dyadicIco_subset_qiWindow_self {r : ℕ} (hr : 1 ≤ r) (k i : ℕ) :
    dyadicIco k i ⊆ qiWindow r k i := by
  intro x hx
  rw [dyadicIco, mem_Ico] at hx
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : ((i + 1 - r : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (by omega : i + 1 - r ≤ i)
  exact ⟨(div_le_div_of_nonneg_right h1 hpos.le).trans hx.1, hx.2.le⟩

/-- **The local error of the quasi-interpolant**: for every polynomial `T` of degree `< r`,
`‖g - Q_k g‖_{L_p(I_{k,i})} ≤ (1 + r M_N C_b r M²) ‖g - T‖_{L_p(W_i)}`. -/
theorem eLpNorm_sub_qiPieces_le {r : ℕ} (hr : 1 ≤ r) {Cb : ℝ≥0∞}
    (hCb : ∀ R ∈ degreeLT ℂ r, ∀ j : ℕ,
      ‖bcoord hr R j‖ₑ ≤ Cb * eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)))
    {MN : ℝ≥0∞} (hMN : ∀ y, ‖bspline r y‖ₑ ≤ MN) (hp : p ≠ ∞) {k i : ℕ} (hi : i < 2 ^ k)
    {g : ℝ → ℂ} (hgm : Measurable g) (hg : IntegrableOn g (Icc 0 1)) {T : ℂ[X]}
    (hT : T ∈ degreeLT ℂ r) :
    eLpNorm (fun x => g x - polyFun (qiPieces hr k g i) x) p (volume.restrict (dyadicIco k i)) ≤
      (1 + r * (MN * (Cb * ppProjConst r))) *
        eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (qiWindow r k i)) := by
  have hp1 : 1 ≤ p := Fact.out
  set h : ℝ → ℂ := fun y => g y - polyFun T y
  have hhm : Measurable h := hgm.sub (measurable_polyFun T)
  have hfun : (fun x => g x - polyFun (qiPieces hr k g i) x) =ᵐ[volume.restrict (dyadicIco k i)]
      fun x => h x - polyFun (qiPieces hr k h i) x := by
    filter_upwards [ae_restrict_mem (measurableSet_dyadicIco k i)] with x hx
    simp only [h]
    rw [polyFun_qiPieces_sub hr hi hg hT hx]
    ring
  have hloc := eLpNorm_qiPieces_le hr hCb hMN hp hi (g := h) hhm.aestronglyMeasurable
  have hcard : (Finset.Ioc ((i : ℤ) - r) i).card = r := by
    rw [Int.card_Ioc]; omega
  rw [eLpNorm_congr_ae hfun]
  calc eLpNorm (fun x => h x - polyFun (qiPieces hr k h i) x) p (volume.restrict (dyadicIco k i))
      ≤ eLpNorm h p (volume.restrict (dyadicIco k i)) +
          eLpNorm (polyFun (qiPieces hr k h i)) p (volume.restrict (dyadicIco k i)) :=
        eLpNorm_sub_le hp1
    _ ≤ eLpNorm h p (volume.restrict (qiWindow r k i)) + MN * (Cb * ppProjConst r) *
          ∑ _n ∈ Finset.Ioc ((i : ℤ) - r) i, eLpNorm h p (volume.restrict (qiWindow r k i)) := by
        gcongr
        · exact dyadicIco_subset_qiWindow_self hr k i
        · exact hloc.trans (by
            gcongr with n hn
            exact dyadicIco_subset_qiWindow (Finset.mem_Ioc.1 hn))
    _ = _ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        ring

/-! ### Jackson's inequality for continuous functions -/

/-- **Approximation on a window**: if `‖g - T₀‖_{L_p[a,b]} ≤ (b - a)^r ‖D‖_{L_p[a,b]}` for some
polynomial `T₀` and `(b - a)^r ≤ c`, then
`‖F - T₀‖^p ≤ 2^(p-1) ∫_{[a,b]} (|F - g|^p + c^p |D|^p)`. -/
theorem exists_window_poly {F g D : ℝ → ℂ} (hFm : Measurable F) (hgm : Measurable g)
    (hDm : Measurable D) (hp : p ≠ ∞) {r : ℕ} {a b : ℝ} {c : ℝ≥0∞}
    (hT : ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      ENNReal.ofReal (b - a) ^ r * eLpNorm D p (volume.restrict (Icc a b)))
    (hc : ENNReal.ofReal (b - a) ^ r ≤ c) :
    ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ^
      p.toReal ≤ 2 ^ (p.toReal - 1) * ∫⁻ x in Icc a b,
        (‖F x - g x‖ₑ ^ p.toReal + c ^ p.toReal * ‖D x‖ₑ ^ p.toReal) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp hp1; rwa [ENNReal.toReal_one] at this
  obtain ⟨T, hTm, hTb⟩ := hT
  refine ⟨T, hTm, ?_⟩
  have htri : eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
        c * eLpNorm D p (volume.restrict (Icc a b)) := by
    calc eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b))
        = eLpNorm ((fun x => F x - g x) + fun x => g x - polyFun T x) p
            (volume.restrict (Icc a b)) := by congr 1; funext x; simp
      _ ≤ eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
            eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) :=
          eLpNorm_add_le hp1
      _ ≤ _ := add_le_add le_rfl (hTb.trans (by gcongr))
  calc eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ^ p.toReal
      ≤ (eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
          c * eLpNorm D p (volume.restrict (Icc a b))) ^ p.toReal :=
        ENNReal.rpow_le_rpow htri hq.le
    _ ≤ 2 ^ (p.toReal - 1) * (eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) ^
          p.toReal + (c * eLpNorm D p (volume.restrict (Icc a b))) ^ p.toReal) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq1
    _ = _ := by
        have hm1 : Measurable fun x => ‖F x - g x‖ₑ ^ p.toReal :=
          ((hFm.sub hgm).enorm).pow_const _
        have hm2 : Measurable fun x => ‖D x‖ₑ ^ p.toReal := hDm.enorm.pow_const _
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          eLpNorm_rpow_eq (g := fun x => F x - g x) ((hFm.sub hgm).aestronglyMeasurable) hp0 hp,
          eLpNorm_rpow_eq hDm.aestronglyMeasurable hp0 hp, lintegral_add_left hm1,
          lintegral_const_mul _ hm2]

/-- The constant of Jackson's inequality for splines,
`C_q (2^p r (1 + (r^r 2^r r^(2r))^p))^(1/p)` with `C_q = 1 + r M_N C_b r M²`. -/
noncomputable def splineJacksonConst (r : ℕ) (Cq p : ℝ≥0∞) : ℝ≥0∞ :=
  Cq * (2 ^ p.toReal * r * (1 + ((r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))) ^ p.toReal)) ^
    (1 / p.toReal)

/-- The `p`-th power of the error over `[0, 1]` is the sum over the dyadic intervals. -/
theorem lintegral_sub_ppFun_le_sum (hp : p ≠ ∞) {F : ℝ → ℂ} (hFm : Measurable F) (k : ℕ)
    (Q : ℕ → ℂ[X]) :
    ∫⁻ x in Icc (0 : ℝ) 1, ‖F x - ppFun k Q x‖ₑ ^ p.toReal ≤
      ∑ i ∈ Finset.range (2 ^ k), eLpNorm (fun x => F x - polyFun (Q i) x) p
        (volume.restrict (dyadicIco k i)) ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hL : (0 : ℝ) ≤ 1 / 2 ^ k := by positivity
  have h1 : (0 : ℝ) + ((2 ^ k : ℕ) : ℝ) * (1 / 2 ^ k) = 1 := by
    rw [zero_add]; push_cast; field_simp
  have hsplit := lintegral_Icc_le_sum (fun x => ‖F x - ppFun k Q x‖ₑ ^ p.toReal) 0 hL (2 ^ k)
  rw [h1] at hsplit
  refine hsplit.trans (Finset.sum_le_sum fun i hi => le_of_eq ?_)
  have hIco : Ico ((0 : ℝ) + i * (1 / 2 ^ k)) ((0 : ℝ) + (i + 1) * (1 / 2 ^ k)) = dyadicIco k i := by
    rw [dyadicIco]
    congr 1 <;> ring
  rw [eLpNorm_rpow_eq (g := fun x => F x - polyFun (Q i) x)
    ((hFm.sub (measurable_polyFun _)).aestronglyMeasurable) hp0 hp,
    ← setLIntegral_congr Ico_ae_eq_Icc, hIco]
  exact setLIntegral_congr_fun (measurableSet_dyadicIco k i) fun x hx => by
    rw [ppFun_eq_of_mem Q (Finset.mem_range.1 hi) hx]

/-- **Jackson's inequality for splines, continuous functions**: there is `C` with
`‖F - Q_k F‖_{L_p[0,1]} ≤ C ω_r(F, 2^(-k), [0, 1])_p` for every continuous `F` and `k ≥ r + 2`. -/
theorem exists_eLpNorm_sub_qi_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : ℝ → ℂ, Continuous F → ∀ k : ℕ, r + 2 ≤ k →
      eLpNorm (fun x => F x - ppFun k (qiPieces hr k F) x) p unitVol ≤
        C * modulus r p 0 1 F (1 / 2 ^ k) := by
  obtain ⟨Cb, hCb, hCbb⟩ := exists_enorm_bcoord_le p hr
  obtain ⟨MN, hMN, hMNb⟩ := exists_enorm_bspline_le r
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hCq : 1 + r * (MN * (Cb * ppProjConst r)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.natCast_ne_top r)
      (ENNReal.mul_ne_top hMN (ENNReal.mul_ne_top hCb (ppProjConst_ne_top r)))⟩
  refine ⟨splineJacksonConst r (1 + r * (MN * (Cb * ppProjConst r))) p, ?_, fun F hF k hk => ?_⟩
  · unfold splineJacksonConst
    refine ENNReal.mul_ne_top hCq (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_)
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le
      ENNReal.ofNat_ne_top) (ENNReal.natCast_ne_top r)) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ENNReal.rpow_ne_top_of_nonneg hq.le ?_⟩)
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))
  set Cq := 1 + r * (MN * (Cb * ppProjConst r))
  set ω := modulus r p 0 1 F (1 / 2 ^ k)
  have hk2 : 2 ≤ k := by omega
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hrk : (r : ℝ) / 2 ^ k ≤ 1 / 4 := by
    have h1 : (r : ℝ) < 2 ^ r := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ (r + 2) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    rw [div_le_div_iff₀ hpos (by norm_num), pow_add] at *
    nlinarith
  obtain ⟨gl, Dl, hglm, hDlm, hl1, hl2, hl3⟩ := exists_left_smoothing hF hr hp1 hp hk2
  obtain ⟨gr, Dr, hgrm, hDrm, hr1, hr2, hr3⟩ := exists_right_smoothing hF hr hp1 hp hk2
  set c : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) / 2 ^ k) ^ r
  set Hl : ℝ → ℝ≥0∞ := fun x => ‖F x - gl x‖ₑ ^ p.toReal + c ^ p.toReal * ‖Dl x‖ₑ ^ p.toReal
  set Hr : ℝ → ℝ≥0∞ := fun x => ‖F x - gr x‖ₑ ^ p.toReal + c ^ p.toReal * ‖Dr x‖ₑ ^ p.toReal
  set Hbar : ℝ → ℝ≥0∞ := fun x => (Icc (0 : ℝ) (3 / 4)).indicator Hl x +
    (Icc (1 / 4 : ℝ) 1).indicator Hr x
  -- the error on one interval
  have hint : ∀ i ∈ Finset.range (2 ^ k),
      eLpNorm (fun x => F x - polyFun (qiPieces hr k F i) x) p
        (volume.restrict (dyadicIco k i)) ^ p.toReal ≤
      Cq ^ p.toReal * (2 ^ (p.toReal - 1) *
        ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), Hbar x) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hcast : (i : ℝ) + 1 - r ≤ ((i + 1 - r : ℕ) : ℝ) := by
      rcases le_or_gt r (i + 1) with h | h
      · rw [Nat.cast_sub h]; push_cast; rfl
      · have : (i : ℝ) + 1 - r < 0 := by
          have : ((i + 1 : ℕ) : ℝ) < r := by exact_mod_cast h
          push_cast at this; linarith
        exact this.le.trans (Nat.cast_nonneg _)
    have hab : ((i + 1 - r : ℕ) : ℝ) / 2 ^ k ≤ ((i : ℝ) + 1) / 2 ^ k := by
      have : ((i + 1 - r : ℕ) : ℝ) ≤ (i : ℝ) + 1 := by
        exact_mod_cast (by omega : i + 1 - r ≤ i + 1)
      exact div_le_div_of_nonneg_right this hpos.le
    have hlen : ((i : ℝ) + 1) / 2 ^ k - ((i + 1 - r : ℕ) : ℝ) / 2 ^ k ≤ (r : ℝ) / 2 ^ k := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hpos.le
    have hc' : ENNReal.ofReal (((i : ℝ) + 1) / 2 ^ k - ((i + 1 - r : ℕ) : ℝ) / 2 ^ k) ^ r ≤ c :=
      pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hlen) r
    have ha0 : 0 ≤ ((i + 1 - r : ℕ) : ℝ) / 2 ^ k := by positivity
    have hwin : qiWindow r k i ⊆ Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k) :=
      Icc_subset_Icc (div_le_div_of_nonneg_right hcast hpos.le) le_rfl
    have hW : qiWindow r k i =
        Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k) := rfl
    obtain ⟨T, hT, hTb⟩ : ∃ T ∈ degreeLT ℂ r, eLpNorm (fun x => F x - polyFun T x) p
        (volume.restrict (Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k))) ^
          p.toReal ≤ 2 ^ (p.toReal - 1) *
        ∫⁻ x in Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), Hbar x := by
      by_cases hleft : ((i : ℝ) + 1) / 2 ^ k ≤ 3 / 4
      · obtain ⟨T, hT, h⟩ := exists_window_poly hF.measurable hglm hDlm hp
          (hl3 _ _ ha0 hab hleft) hc'
        refine ⟨T, hT, h.trans (mul_le_mul' le_rfl ?_)⟩
        refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
        have hx' : x ∈ Icc (0 : ℝ) (3 / 4) := ⟨ha0.trans hx.1, hx.2.trans hleft⟩
        have hb : Hbar x = Hl x + (Icc (1 / 4 : ℝ) 1).indicator Hr x := by
          simp only [Hbar, indicator_of_mem hx']
        rw [hb]
        exact le_self_add
      · push Not at hleft
        have ha : 1 / 4 ≤ ((i + 1 - r : ℕ) : ℝ) / 2 ^ k := by
          have : ((i : ℝ) + 1 - r) / 2 ^ k = ((i : ℝ) + 1) / 2 ^ k - (r : ℝ) / 2 ^ k := by ring
          linarith [div_le_div_of_nonneg_right hcast hpos.le]
        have hb : ((i : ℝ) + 1) / 2 ^ k ≤ 1 := by
          rw [div_le_one hpos]
          have : ((i + 1 : ℕ) : ℝ) ≤ 2 ^ k := by exact_mod_cast hi'
          push_cast at this; linarith
        obtain ⟨T, hT, h⟩ := exists_window_poly hF.measurable hgrm hDrm hp
          (hr3 _ _ ha hab hb) hc'
        refine ⟨T, hT, h.trans (mul_le_mul' le_rfl ?_)⟩
        refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
        have hx' : x ∈ Icc (1 / 4 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans hb⟩
        have hb' : Hbar x = (Icc (0 : ℝ) (3 / 4)).indicator Hl x + Hr x := by
          simp only [Hbar, indicator_of_mem hx']
        rw [hb']
        exact le_add_self
    calc eLpNorm (fun x => F x - polyFun (qiPieces hr k F i) x) p
          (volume.restrict (dyadicIco k i)) ^ p.toReal
        ≤ (Cq * eLpNorm (fun x => F x - polyFun T x) p
            (volume.restrict (Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k)))) ^
              p.toReal :=
          ENNReal.rpow_le_rpow ((eLpNorm_sub_qiPieces_le hr hCbb hMNb hp hi' hF.measurable
            hF.integrableOn_Icc hT).trans_eq (by rw [hW])) hq.le
      _ = Cq ^ p.toReal * eLpNorm (fun x => F x - polyFun T x) p
            (volume.restrict (Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k))) ^
              p.toReal := ENNReal.mul_rpow_of_nonneg _ _ hq.le
      _ ≤ Cq ^ p.toReal * (2 ^ (p.toReal - 1) *
            ∫⁻ x in Icc (((i + 1 - r : ℕ) : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), Hbar x) :=
          mul_le_mul' le_rfl hTb
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono_set (hW ▸ hwin)))
  -- the integral of the dominating function
  have hHl : Measurable Hl := ((hF.measurable.sub hglm).enorm.pow_const _).add
    (measurable_const.mul (hDlm.enorm.pow_const _))
  have hHr : Measurable Hr := ((hF.measurable.sub hgrm).enorm.pow_const _).add
    (measurable_const.mul (hDrm.enorm.pow_const _))
  have hside : ∀ {G D : ℝ → ℂ} {s : Set ℝ}, Measurable G → Measurable D →
      eLpNorm (fun x => F x - G x) p (volume.restrict s) ≤ ω →
      eLpNorm D p (volume.restrict s) ≤ ENNReal.ofReal (2 ^ k) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω →
      ∫⁻ x in s, (‖F x - G x‖ₑ ^ p.toReal + c ^ p.toReal * ‖D x‖ₑ ^ p.toReal) ≤
        (1 + ((r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))) ^ p.toReal) * ω ^ p.toReal := by
    intro G D s hGm hDm h1 h2
    rw [lintegral_add_left (f := fun x => ‖F x - G x‖ₑ ^ p.toReal)
      ((hF.measurable.sub hGm).enorm.pow_const _),
      lintegral_const_mul _ (hDm.enorm.pow_const _),
      ← eLpNorm_rpow_eq (g := fun x => F x - G x) ((hF.measurable.sub hGm).aestronglyMeasurable)
        hp0 hp, ← eLpNorm_rpow_eq hDm.aestronglyMeasurable hp0 hp]
    have hcc : c * ENNReal.ofReal (2 ^ k) ^ r = (r : ℝ≥0∞) ^ r := by
      rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hpos.ne',
        ENNReal.ofReal_natCast]
    calc eLpNorm (fun x => F x - G x) p (volume.restrict s) ^ p.toReal +
          c ^ p.toReal * eLpNorm D p (volume.restrict s) ^ p.toReal
        ≤ ω ^ p.toReal + c ^ p.toReal * (ENNReal.ofReal (2 ^ k) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω) ^ p.toReal := by
          gcongr
      _ = (1 + ((r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))) ^ p.toReal) * ω ^ p.toReal := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← mul_assoc, ← mul_assoc, hcc,
            ENNReal.mul_rpow_of_nonneg _ _ hq.le]
          ring
  have hHbar : ∫⁻ x, Hbar x ≤ 2 * ((1 + ((r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))) ^ p.toReal) * ω ^ p.toReal) := by
    rw [lintegral_add_left ((hHl.indicator measurableSet_Icc)),
      lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Icc, two_mul]
    exact add_le_add (hside hglm hDlm hl1 hl2) (hside hgrm hDrm hr1 hr2)
  -- assembling
  refine eLpNorm_le_of_lintegral_le ((hF.measurable.sub
    (measurable_ppFun _ _)).aestronglyMeasurable) hp0 hp ?_
  calc ∫⁻ x, ‖F x - ppFun k (qiPieces hr k F) x‖ₑ ^ p.toReal ∂unitVol
      ≤ ∑ i ∈ Finset.range (2 ^ k), eLpNorm (fun x => F x - polyFun (qiPieces hr k F i) x) p
          (volume.restrict (dyadicIco k i)) ^ p.toReal :=
        lintegral_sub_ppFun_le_sum hp hF.measurable k _
    _ ≤ ∑ i ∈ Finset.range (2 ^ k), Cq ^ p.toReal * (2 ^ (p.toReal - 1) *
          ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), Hbar x) :=
        Finset.sum_le_sum hint
    _ = Cq ^ p.toReal * 2 ^ (p.toReal - 1) * ∑ i ∈ Finset.range (2 ^ k),
          ∫⁻ x in Icc (((i : ℝ) + 1 - r) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k), Hbar x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ Cq ^ p.toReal * 2 ^ (p.toReal - 1) * (r * ∫⁻ x, Hbar x) := by
        gcongr
        exact sum_lintegral_window_le r k Hbar
    _ ≤ Cq ^ p.toReal * 2 ^ (p.toReal - 1) *
          (r * (2 * ((1 + ((r : ℝ≥0∞) ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))) ^ p.toReal) * ω ^ p.toReal))) := by gcongr
    _ = (splineJacksonConst r Cq p * ω) ^ p.toReal := by
        have h2 : (2 : ℝ≥0∞) ^ (p.toReal - 1) * 2 = 2 ^ p.toReal := by
          calc (2 : ℝ≥0∞) ^ (p.toReal - 1) * 2 = 2 ^ (p.toReal - 1) * 2 ^ (1 : ℝ) := by
                rw [ENNReal.rpow_one]
            _ = 2 ^ (p.toReal - 1 + 1) :=
                (ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top).symm
            _ = 2 ^ p.toReal := by rw [sub_add_cancel]
        unfold splineJacksonConst
        rw [ENNReal.mul_rpow_of_nonneg (Cq * _) ω hq.le, ENNReal.mul_rpow_of_nonneg Cq _ hq.le,
          ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one, ← h2]
        ring

/-! ### Jackson's inequality in `L_p` and the coincidence theorem -/

/-- **Jackson's inequality for dyadic splines**: for `1 ≤ p < ∞` and `r ≥ 1` there is `C_J` with
`E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k), [0, 1])_p` for all `f ∈ L_p[0, 1]` and `k ≥ r + 2`. -/
theorem exists_approxSeq_splineScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p unitVol) (k : ℕ), r + 2 ≤ k →
      (splineScheme p r).approxSeq f (2 ^ k) ≤ CJ * lpModulus p r f k := by
  obtain ⟨C, hC, hCb⟩ := exists_eLpNorm_sub_qi_le hr hp
  refine ⟨C, hC, fun f k hk => ?_⟩
  -- continuous functions
  have hcont : ∀ g : ℝ →ᵇ ℂ, (splineScheme p r).approxSeq
      (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g) (2 ^ k) ≤
        C * lpModulus p r (BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g) k := by
    intro g
    set a := (memLp_ppFun k (qiPieces hr k g) p).toLp (ppFun k (qiPieces hr k g))
    have ha : a ∈ splineScheme p r (2 ^ k) :=
      mem_splineScheme_two_pow.2 ⟨qiPieces hr k g, qiPieces_mem hr k g,
        splineJoins_qiPieces hr k g, MemLp.coeFn_toLp _⟩
    have hg := BoundedContinuousFunction.coeFn_toLp (E := ℂ) p unitVol ℝ g
    refine ((splineScheme p r).approxSeq_le_of_mem ha _).trans ?_
    rw [Lp.enorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hg.sub (MemLp.coeFn_toLp _))),
      lpModulus, modulus_congr_ae hg]
    exact hCb g g.continuous k hk
  set b := C * lpModulus p r f k
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set K : ℝ≥0∞ := C * 2 ^ r + 1
  have hK : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC (by simp), ENNReal.one_ne_top⟩
  have hK0 : K ≠ 0 := by simp [K]
  have hη : 0 < (ε / K).toReal := ENNReal.toReal_pos (by
    simpa using ⟨ne_of_gt (by exact_mod_cast hε), hK⟩) (ENNReal.div_ne_top ENNReal.coe_ne_top hK0)
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.1
    (BoundedContinuousFunction.toLp_denseRange ℂ unitVol ℝ hp) f _ hη
  set fg := BoundedContinuousFunction.toLp (E := ℂ) p unitVol ℝ g
  have hdist : ‖f - fg‖ₑ ≤ ε / K := by
    rw [← edist_eq_enorm_sub, edist_dist, ← ENNReal.ofReal_toReal
      (ENNReal.div_ne_top ENNReal.coe_ne_top hK0)]
    exact ENNReal.ofReal_le_ofReal hg.le
  have hmod : lpModulus p r fg k ≤ lpModulus p r f k + 2 ^ r * ‖f - fg‖ₑ := by
    have h := lpModulus_add_le r f (fg - f) k
    rw [add_sub_cancel] at h
    refine h.trans (add_le_add le_rfl ((lpModulus_le r _ _).trans ?_))
    rw [← enorm_neg, neg_sub]
  calc (splineScheme p r).approxSeq f (2 ^ k)
      ≤ (splineScheme p r).approxSeq fg (2 ^ k) + ‖f - fg‖ₑ :=
        ApproximationScheme.approxSeq_le_approxSeq_add_enorm _ f fg
    _ ≤ C * (lpModulus p r f k + 2 ^ r * ‖f - fg‖ₑ) + ‖f - fg‖ₑ :=
        add_le_add ((hcont g).trans (by gcongr)) le_rfl
    _ = b + K * ‖f - fg‖ₑ := by simp only [b, K]; ring
    _ ≤ b + K * (ε / K) := by gcongr
    _ = b + ε := by rw [ENNReal.mul_div_cancel hK0 hK]

/-- The modulus `ω_r(f, 2^(-k), [0, 1])_p` is compatible with the scheme of dyadic splines of
order `r`, with inverse order `θ = r - 1 + 1/p` and Jackson's inequality from level `r + 2` on. -/
noncomputable def splineModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (splineScheme p r) (((r - 1 : ℕ) : ℝ) + 1 / p.toReal) where
  modulus := lpModulus p r
  add_le := lpModulus_add_le r
  C0 := 2 ^ r
  C0_ne_top := by simp
  le_enorm := lpModulus_le r
  jacksonStart := r + 2
  CJ := (exists_approxSeq_splineScheme_le hr hp).choose
  CJ_ne_top := (exists_approxSeq_splineScheme_le hr hp).choose_spec.1
  jackson f k hk := (exists_approxSeq_splineScheme_le hr hp).choose_spec.2 f k hk
  CB := (exists_inverse_splineScheme (r := r) hp).choose
  CB_ne_top := (exists_inverse_splineScheme hp).choose_spec.1
  inverse := (exists_inverse_splineScheme hp).choose_spec.2

/-- **Approximation by dyadic splines.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 ≤ s < r - 1 + 1/p`, an `f ∈ L_p[0, 1]` lies in the approximation space `A^s_q` of the splines
of order `r` (degree `< r`, `C^(r-2)`) on dyadic partitions iff its Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}` is finite. -/
theorem memApprox_splineScheme_iff {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) (f : Lp ℂ p unitVol) :
    (splineScheme p r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ := by
  have hθ : (r : ℝ) - 1 + 1 / p.toReal = ((r - 1 : ℕ) : ℝ) + 1 / p.toReal := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  exact (splineModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs (hθ ▸ hsr) f

end Interval
