/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Cube.IsoInverse
public import FunctionSpaces.Rd.MixedSmoothness.MixedDifferences
public import FunctionSpaces.Wavelets.Examples.Daubechies.Besov

/-!
# Tensor Daubechies generators on `ℝ^d` and their moduli of smoothness

For a Daubechies mask of order `N ≥ 2` with scaling function `φ` (`Daubechies.scalingFun`) and
wavelet `ψ` (`Daubechies.wavelet`), and a set `e ⊆ {0, …, d-1}` of coordinates, the **tensor
generator** on `ℝ^d = Fin d → ℝ` is

`Ψ^e(x) = ∏_{i ∈ e} ψ(x_i) ∏_{i ∉ e} φ(x_i)`

(`Daubechies.tensorGen`); `Φ = Ψ^∅` is the tensor scaling function, and the `2^d - 1` generators
with `e ≠ ∅` are the tensor wavelets of DeVore's *Nonlinear approximation*, (7.18). This file
proves the properties of the generators that a multiresolution analysis on `ℝ^d` built from them
uses:

* **Support, continuity, `L_p`.** `Ψ^e` vanishes outside the cube `[1 - N, 2N - 1]^d`, is
  continuous and lies in every `L_p` (`Daubechies.tensorGen_eq_zero`,
  `Daubechies.continuous_tensorGen`, `Daubechies.memLp_tensorGen`).
* **Orthonormality.** `∫ Ψ^e(x - k) conj Ψ^{e'}(x - l) dx = δ_{ee'} δ_{kl}` for `k, l ∈ ℤ^d`
  (`Daubechies.integral_tensorGen_translate_mul_conj_translate`): by Fubini the integral is the
  product of the one-dimensional inner products of `φ` and `ψ` and their translates, and if
  `e ≠ e'` one factor pairs `φ` with `ψ`.
* **Isotropic differences of tensor products.** The isotropic difference `Δ_h^r` on `ℝ^d` is a sum
  of `d^r` translated mixed coordinate differences (`Cube.higherDiff_eq_sum`), and a mixed
  coordinate difference of a tensor product is the tensor product of the one-dimensional
  differences (`Cube.cubeMixedDiff_tensorKernel`). With `‖⊗K‖_p = ∏_i ‖K_i‖_p`
  (`Rd.eLpNorm_tensorKernel`), bounds `‖Δ_t^n K_i‖_p ≤ A |t|^{θ_n}` for all orders `n ≤ r` give
  `‖Δ_h^r (⊗K)‖_p ≤ d^r A^d ‖h‖^Θ` whenever `Θ ≤ ∑_i θ_{n_i}` for all `n` with `∑_i n_i = r`
  (`Rd.eLpNorm_higherDiff_tensorKernel_le`).
* **Lower orders.** A modulus bound `ω_r(g, t)_p ≤ K t^θ` for `0 < t ≤ 1`
  (`Daubechies.ModulusBound`; a Bernstein bound is the case `g = φ`) gives one of every order
  `r'` and every exponent `0 ≤ θ' ≤ θ` with `θ' < r'` (`Daubechies.ModulusBound.of_order`), since
  for `q = ∞` and smoothness `θ' < r'` the Besov norm by differences of order `r'` is bounded by
  the one of order `r` (`Rd.modNorm_le_modNorm_of_lt`). The wavelet lies in the scaling space of
  level one, so the Bernstein inequality transfers a Bernstein bound of `φ` to `ψ`
  (`Daubechies.modulusBound_wavelet`).
* **The moduli of the generators.** If `φ` has a Bernstein bound of order `θ` with differences of
  order `N`, then for `0 ≤ θ' ≤ θ`, `θ' < N` there is a constant `K < ∞` with
  `‖Δ_h^N Ψ^e‖_p ≤ K ‖h‖^{θ'}` for all `e` and `‖h‖ ≤ 1`
  (`Daubechies.eLpNorm_higherDiff_tensorGen_le`): the exponents `θ' n / N` of the orders `n ≤ N`
  add up to `θ'` over every word of the expansion of `Δ_h^N`.

The norm on `ℝ^d` is the sup norm, and `‖h‖ ≤ 1` bounds every coordinate `|h_i|`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ComplexConjugate
open ENNReal (dyadicWeight lqNorm)

/-! ### Isotropic differences of tensor products -/

namespace Cube

variable {d : ℕ}

/-- **Mixed coordinate differences of tensor products** act on the factors: along a list `l` of
distinct coordinates, the mixed difference `M_m (⊗K)` with orders `m_i` and steps `h_i` is the
tensor product `⊗K'` with `K'_i = Δ^{m_i}_{h_i} K_i` for `i ∈ l` and `K'_i = K_i` otherwise
(`Rd.higherDiff_single_tensorKernel`, one coordinate at a time). -/
theorem cubeMixedDiff_tensorKernel (m : Fin d → ℕ) (h : Fin d → ℝ) {l : List (Fin d)}
    (hl : l.Nodup) (K : Fin d → ℝ → ℂ) :
    cubeMixedDiff m h l (Rd.tensorKernel K) =
      Rd.tensorKernel fun i => if i ∈ l then (fwdDiff (h i))^[m i] (K i) else K i := by
  induction l with
  | nil => simp [cubeMixedDiff_nil]
  | cons c l ih =>
    rw [List.nodup_cons] at hl
    rw [cubeMixedDiff_cons, ih hl.2, ← higherDiff_single, Rd.higherDiff_def,
      Rd.higherDiff_single_tensorKernel]
    congr 1
    funext i
    by_cases hic : i = c
    · subst hic
      simp [hl.1]
    · simp [hic]

end Cube

namespace Rd

open TranslationAlgebra (letterCount shiftVec sum_letterCount)

variable {d : ℕ}

/-- **Products of one-dimensional differences**: let `‖h‖ ≤ 1`, `θ_n ≥ 0`, and let
`‖Δ_t^n K_i‖_p ≤ A |t|^{θ_n}` for every coordinate `i`, every order `n ≤ r` and every `|t| ≤ 1`.
Then for all orders `n_i ≤ r`, `∏_i ‖Δ^{n_i}_{h_i} K_i‖_p ≤ A^d ‖h‖^{∑_i θ_{n_i}}`, since
`|h_i| ≤ ‖h‖ ≤ 1`. -/
theorem prod_eLpNorm_higherDiff_le {p : ℝ≥0∞} {r : ℕ} {K : Fin d → ℝ → ℂ} {A : ℝ≥0∞}
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n)
    (hb : ∀ i, ∀ n ≤ r, ∀ t : ℝ, |t| ≤ 1 →
      eLpNorm ((fwdDiff t)^[n] (K i)) p volume ≤ A * ENNReal.ofReal (|t| ^ θ n))
    {h : Fin d → ℝ} (hh : ‖h‖ ≤ 1) {n : Fin d → ℕ} (hn : ∀ i, n i ≤ r) :
    ∏ i, eLpNorm ((fwdDiff (h i))^[n i] (K i)) p volume ≤
      A ^ d * ENNReal.ofReal ‖h‖ ^ ∑ i, θ (n i) := by
  have hhi : ∀ i, |h i| ≤ ‖h‖ := fun i => by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm h i
  calc ∏ i, eLpNorm ((fwdDiff (h i))^[n i] (K i)) p volume
      ≤ ∏ i, (A * ENNReal.ofReal ‖h‖ ^ θ (n i)) := by
        refine Finset.prod_le_prod fun i _ =>
          (hb i _ (hn i) (h i) ((hhi i).trans hh)).trans ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg h) (hθ _)]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (abs_nonneg _) (hhi i) (hθ _))) A
    _ = A ^ d * ENNReal.ofReal ‖h‖ ^ ∑ i, θ (n i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Cube.prod_rpow_eq_rpow_sum _ _ fun i _ => hθ _]

/-- **Isotropic differences of tensor products**: let `1 ≤ p < ∞`, let the one-dimensional
kernels `K_i` be almost everywhere strongly measurable, let `θ_n ≥ 0` and `0 ≤ Θ ≤ ∑_i θ_{n_i}`
for every `n ∈ ℕ^d` with `∑_i n_i = r`, and let `‖Δ_t^n K_i‖_p ≤ A |t|^{θ_n}` for every
coordinate `i`, every order `n ≤ r` and every `|t| ≤ 1`. Then for every `h ∈ ℝ^d` with
`‖h‖ ≤ 1`, `‖Δ_h^r (⊗K)‖_p ≤ d^r A^d ‖h‖^Θ`. The isotropic difference is the sum of the `d^r`
translated mixed coordinate differences of its words (`Cube.higherDiff_eq_sum`), each the tensor
product of one-dimensional differences (`Cube.cubeMixedDiff_tensorKernel`) with the norm
`∏_i ‖Δ^{n_i}_{h_i} K_i‖_p` (`Rd.eLpNorm_tensorKernel`, translation invariance) for the
multiplicities `n_i ≤ r` of the word, and each word contributes at most `A^d ‖h‖^Θ`
(`Rd.prod_eLpNorm_higherDiff_le`). -/
theorem eLpNorm_higherDiff_tensorKernel_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (r : ℕ)
    {K : Fin d → ℝ → ℂ} (hK : ∀ i, AEStronglyMeasurable (K i)) {A : ℝ≥0∞} {θ : ℕ → ℝ}
    (hθ : ∀ n, 0 ≤ θ n) {Θ : ℝ} (hΘ0 : 0 ≤ Θ)
    (hΘ : ∀ n : Fin d → ℕ, ∑ i, n i = r → Θ ≤ ∑ i, θ (n i))
    (hb : ∀ i, ∀ n ≤ r, ∀ t : ℝ, |t| ≤ 1 →
      eLpNorm ((fwdDiff t)^[n] (K i)) p volume ≤ A * ENNReal.ofReal (|t| ^ θ n))
    {h : Fin d → ℝ} (hh : ‖h‖ ≤ 1) :
    eLpNorm ((fwdDiff h)^[r] (tensorKernel K)) p volume ≤
      (d : ℝ≥0∞) ^ r * A ^ d * ENNReal.ofReal (‖h‖ ^ Θ) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  set G : (Fin r → Fin d) → Fin d → ℝ → ℂ := fun α i => (fwdDiff (h i))^[letterCount α i] (K i)
  have hG : ∀ α, AEStronglyMeasurable (tensorKernel (G α)) := fun α =>
    aestronglyMeasurable_tensorKernel fun i => aestronglyMeasurable_higherDiff (hK i) _ _
  have hsum : (fwdDiff h)^[r] (tensorKernel K) =
      ∑ α : Fin r → Fin d, fun x => tensorKernel (G α) (x + shiftVec h α) := by
    funext x
    rw [Finset.sum_apply, ← higherDiff_def, Cube.higherDiff_eq_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Cube.cubeMixedDiff_tensorKernel _ _ (List.nodup_finRange d)]
    simp [G]
  have hA1 : ENNReal.ofReal ‖h‖ ≤ 1 := ENNReal.ofReal_le_one.2 hh
  have hword : ∀ α : Fin r → Fin d,
      eLpNorm (fun x => tensorKernel (G α) (x + shiftVec h α)) p volume ≤
        A ^ d * ENNReal.ofReal (‖h‖ ^ Θ) := fun α => by
    rw [eLpNorm_comp_add_right (hG α), eLpNorm_tensorKernel hp0 hp fun i =>
      aestronglyMeasurable_higherDiff (hK i) _ _,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg h) hΘ0]
    exact (prod_eLpNorm_higherDiff_le hθ hb hh (Cube.letterCount_le α)).trans (mul_le_mul_right
      (ENNReal.rpow_le_rpow_of_exponent_ge hA1 (hΘ _ (sum_letterCount α))) _)
  rw [hsum]
  refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun α _ => hword α).trans_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

end Rd

namespace Daubechies

variable {N : ℕ} (m : Mask N) {d : ℕ}

/-! ### The tensor generators -/

/-- **The tensor generator** `Ψ^e(x) = ∏_{i ∈ e} ψ(x_i) ∏_{i ∉ e} φ(x_i)` on `ℝ^d`, for a set
`e` of coordinates, with the wavelet `ψ` (`Daubechies.wavelet`) in the coordinates of `e` and the
scaling function `φ` (`Daubechies.scalingFun`) in the others. `Φ = Ψ^∅` is the tensor scaling
function, and the `Ψ^e` with `e ≠ ∅` are the tensor wavelets. -/
noncomputable def tensorGen (e : Finset (Fin d)) : (Fin d → ℝ) → ℂ :=
  Rd.tensorKernel fun i => if i ∈ e then wavelet m else scalingFun m

/-- `Ψ^e(x) = ∏_i γ_i(x_i)` with `γ_i = ψ` for `i ∈ e` and `γ_i = φ` otherwise. -/
theorem tensorGen_apply (e : Finset (Fin d)) (x : Fin d → ℝ) :
    tensorGen m e x = ∏ i, (if i ∈ e then wavelet m else scalingFun m) (x i) := rfl

/-- **The factors vanish outside `[1 - N, 2N - 1]`**, for `N ≥ 2`: `φ` vanishes outside
`[0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`) and `ψ` outside `[1 - N, N]`
(`Daubechies.wavelet_eq_zero`), and both intervals lie in `[1 - N, 2N - 1]`. -/
theorem ite_wavelet_scalingFun_eq_zero (hN : 2 ≤ N) (P : Prop) [Decidable P] {t : ℝ}
    (ht : t ∉ Set.Icc (1 - N : ℝ) (2 * N - 1)) :
    (if P then wavelet m else scalingFun m) t = 0 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  split_ifs
  · exact wavelet_eq_zero m hN fun h => ht ⟨h.1, by linarith [h.2]⟩
  · exact scalingFun_eq_zero m hN fun h => ht ⟨by linarith [h.1], h.2⟩

/-- **Support of the tensor generators**: for `N ≥ 2`, `Ψ^e(x) = 0` whenever some coordinate
`x_i` lies outside `[1 - N, 2N - 1]`, since the factor of coordinate `i` vanishes there
(`Daubechies.ite_wavelet_scalingFun_eq_zero`). -/
theorem tensorGen_eq_zero (hN : 2 ≤ N) (e : Finset (Fin d)) {x : Fin d → ℝ}
    (hx : ∃ i, x i ∉ Set.Icc (1 - N : ℝ) (2 * N - 1)) : tensorGen m e x = 0 := by
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_wavelet_scalingFun_eq_zero m hN _ hi)

/-- **The tensor generators are continuous**, for `N ≥ 2`: tensor products of the continuous
functions `φ` and `ψ` (`Daubechies.continuous_scalingFun`, `Daubechies.continuous_wavelet`). -/
theorem continuous_tensorGen (hN : 2 ≤ N) (e : Finset (Fin d)) : Continuous (tensorGen m e) :=
  Rd.continuous_tensorKernel fun i => by
    split_ifs
    exacts [continuous_wavelet m hN, continuous_scalingFun m hN]

/-- **The tensor generators have compact support**, for `N ≥ 2`: they vanish outside the cube
`[1 - N, 2N - 1]^d` (`Daubechies.tensorGen_eq_zero`). -/
theorem hasCompactSupport_tensorGen (hN : 2 ≤ N) (e : Finset (Fin d)) :
    HasCompactSupport (tensorGen m e) :=
  HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc (a := (1 - N : ℝ))
    (b := 2 * N - 1)) fun x hx => tensorGen_eq_zero m hN e (by
      simpa only [Set.mem_univ_pi, not_forall] using hx)

/-- **The tensor generators lie in every `L_p`**, `p ∈ [0, ∞]`, for `N ≥ 2`: they are continuous
with compact support (Mathlib's `Continuous.memLp_of_hasCompactSupport`). -/
theorem memLp_tensorGen (hN : 2 ≤ N) (e : Finset (Fin d)) (p : ℝ≥0∞) :
    MemLp (tensorGen m e) p :=
  (continuous_tensorGen m hN e).memLp_of_hasCompactSupport (hasCompactSupport_tensorGen m hN e)

/-! ### Orthonormality -/

/-- **The one-dimensional factors are orthonormal**: for `N ≥ 2`, two propositions `P, P'`
choosing `γ = ψ` if `P` holds and `γ = φ` otherwise (and `γ'` likewise by `P'`), and `k, l ∈ ℤ`,
`∫ γ(t - k) conj γ'(t - l) dt` is `1` if `γ = γ'` and `k = l`, and `0` otherwise
(`Daubechies.integral_scalingFun_translate_mul_conj_translate`,
`Daubechies.integral_wavelet_translate_mul_conj_translate`,
`Daubechies.integral_wavelet_translate_mul_conj_scalingFun_translate` and its conjugate). -/
theorem integral_ite_translate_mul_conj_translate (hN : 2 ≤ N) (P P' : Prop) [Decidable P]
    [Decidable P'] (k l : ℤ) :
    ∫ t, (if P then wavelet m else scalingFun m) (t - k) *
        conj ((if P' then wavelet m else scalingFun m) (t - l)) =
      if (P ↔ P') ∧ k = l then 1 else 0 := by
  by_cases hP : P <;> by_cases hP' : P' <;> simp only [hP, hP', ↓reduceIte, iff_self,
    true_and, iff_false, false_iff, not_true, false_and]
  · exact integral_wavelet_translate_mul_conj_translate m hN k l
  · exact integral_wavelet_translate_mul_conj_scalingFun_translate m hN k l
  · have h : ∀ t : ℝ, scalingFun m (t - k) * conj (wavelet m (t - l)) =
        conj (wavelet m (t - l) * conj (scalingFun m (t - k))) := fun t => by
      rw [map_mul, Complex.conj_conj, mul_comm]
    simp_rw [h, integral_conj, integral_wavelet_translate_mul_conj_scalingFun_translate m hN l k,
      map_zero]
  · exact integral_scalingFun_translate_mul_conj_translate m hN k l

/-- **Orthonormality of the tensor generators and their integer translates**: for `N ≥ 2`, sets
`e, e'` of coordinates and `k, l ∈ ℤ^d`, `∫ Ψ^e(x - k) conj Ψ^{e'}(x - l) dx` is `1` if `e = e'`
and `k = l`, and `0` otherwise. By Fubini (Mathlib's `integral_fintype_prod_volume_eq_prod`) the
integral is the product over the coordinates of the one-dimensional inner products
(`Daubechies.integral_ite_translate_mul_conj_translate`), which are `0` or `1`; their product is
`1` iff every coordinate lies in both or neither of `e, e'` and `k_i = l_i` for every `i`. -/
theorem integral_tensorGen_translate_mul_conj_translate (hN : 2 ≤ N) (e e' : Finset (Fin d))
    (k l : Fin d → ℤ) :
    ∫ x, tensorGen m e (x - fun i => (k i : ℝ)) * conj (tensorGen m e' (x - fun i => (l i : ℝ))) =
      if e = e' ∧ k = l then 1 else 0 := by
  have h : ∀ x : Fin d → ℝ, tensorGen m e (x - fun i => (k i : ℝ)) *
      conj (tensorGen m e' (x - fun i => (l i : ℝ))) =
      ∏ i, (if i ∈ e then wavelet m else scalingFun m) (x i - k i) *
        conj ((if i ∈ e' then wavelet m else scalingFun m) (x i - l i)) := fun x => by
    simp only [tensorGen_apply, Pi.sub_apply, map_prod, Finset.prod_mul_distrib]
  simp_rw [h]
  rw [integral_fintype_prod_volume_eq_prod (E := fun _ => ℝ) (fun i t =>
    (if i ∈ e then wavelet m else scalingFun m) (t - k i) *
      conj ((if i ∈ e' then wavelet m else scalingFun m) (t - l i)))]
  simp_rw [integral_ite_translate_mul_conj_translate m hN]
  rw [Fintype.prod_boole]
  by_cases hee : e = e' ∧ k = l
  · obtain ⟨rfl, rfl⟩ := hee
    simp
  · have hi : ¬ ∀ i, (i ∈ e ↔ i ∈ e') ∧ k i = l i := fun hi =>
      hee ⟨Finset.ext fun i => (hi i).1, funext fun i => (hi i).2⟩
    simp only [hee, hi, ↓reduceIte]

/-! ### Modulus bounds of lower orders -/

/-- **A modulus bound of order `θ` in `L_p`** with differences of order `r` for a function
`g : ℝ → ℂ`: there is a finite constant `K` with `ω_r(g, t)_p ≤ K t^θ` for all `0 < t ≤ 1`. For
the scaling function this is a Bernstein bound (`Daubechies.bernsteinBound_iff_modulusBound`). -/
def ModulusBound (g : ℝ → ℂ) (p : ℝ≥0∞) (θ : ℝ) (r : ℕ) : Prop :=
  ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    Rd.smoothnessModulus volume r p g t ≤ K * ENNReal.ofReal (t ^ θ)

/-- A Bernstein bound (`Daubechies.BernsteinBound`) is a modulus bound for the scaling
function. -/
theorem bernsteinBound_iff_modulusBound {p : ℝ≥0∞} {θ : ℝ} {r : ℕ} :
    BernsteinBound m p θ r ↔ ModulusBound (scalingFun m) p θ r := Iff.rfl

/-- **From dyadic scales to all scales**: if `θ ≥ 0` and `ω_r(g, 2^(-k))_p ≤ B 2^(-kθ)` for every
`k ∈ ℕ` with `B < ∞`, then `g` has a modulus bound of order `θ` with differences of order `r`:
for `2^(-k-1) < t ≤ 2^(-k)` the modulus increases in `t` (`Rd.smoothnessModulus_mono`) and
`2^(-kθ) ≤ 2^θ t^θ`. -/
theorem modulusBound_of_dyadic {g : ℝ → ℂ} {p : ℝ≥0∞} {θ : ℝ} (hθ : 0 ≤ θ) {r : ℕ}
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (h : ∀ k : ℕ, Rd.smoothnessModulus volume r p g (1 / 2 ^ k) ≤ B * dyadicWeight (-θ) k) :
    ModulusBound g p θ r := by
  refine ⟨ENNReal.ofReal (2 ^ θ) * B, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB,
    fun t ht => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (one_le_one_div ht.1 ht.2) one_lt_two
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have htk : t ≤ 1 / 2 ^ k := by
    rw [le_div_iff₀ h2k, mul_comm]
    rwa [le_div_iff₀ ht.1] at hk1
  have hkt : 1 / 2 ^ k ≤ 2 * t := by
    rw [div_lt_iff₀ ht.1, pow_succ] at hk2
    rw [div_le_iff₀ h2k]
    linarith
  calc Rd.smoothnessModulus volume r p g t ≤ Rd.smoothnessModulus volume r p g (1 / 2 ^ k) :=
        Rd.smoothnessModulus_mono r p g htk
    _ ≤ B * ENNReal.ofReal ((1 / 2 ^ k) ^ θ) := by
        rw [ENNReal.ofReal_one_div_two_pow_rpow]
        exact h k
    _ ≤ B * ENNReal.ofReal ((2 * t) ^ θ) := by gcongr
    _ = ENNReal.ofReal (2 ^ θ) * B * ENNReal.ofReal (t ^ θ) := by
        rw [Real.mul_rpow zero_le_two ht.1.le, ENNReal.ofReal_mul (by positivity)]
        ring

/-- **Modulus bounds of other orders**: let `1 ≤ p < ∞`, `g ∈ L_p(ℝ)`, and let `g` have a modulus
bound of order `θ` with differences of order `r`. Then for every order `r'` and every exponent
`θ'` with `0 ≤ θ' ≤ θ` and `θ' < r'`, `g` has a modulus bound of order `θ'` with differences of
order `r'`. The sequence `2^(kθ') ω_r(g, 2^(-k))_p` is bounded by the constant of the bound, so
the norm `‖g‖_p + sup_k 2^(kθ') ω_r(g, 2^(-k))_p` is finite, and it bounds
`sup_k 2^(kθ') ω_{r'}(g, 2^(-k))_p` up to a constant (`Rd.modNorm_le_modNorm_of_lt` with
`q = ∞`); `Daubechies.modulusBound_of_dyadic` passes to all scales. -/
theorem ModulusBound.of_order {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {g : ℝ → ℂ}
    (hg : MemLp g p) {θ θ' : ℝ} {r r' : ℕ} (hB : ModulusBound g p θ r) (hθ'0 : 0 ≤ θ')
    (hθ' : θ' ≤ θ) (hθ'r : θ' < r') : ModulusBound g p θ' r' := by
  obtain ⟨K, hK, hmod⟩ := hB
  obtain ⟨C, hC, hle⟩ := Rd.modNorm_le_modNorm_of_lt (V := ℝ) hp r hθ'0 hθ'r (q := ∞) le_top
  set F := hg.toLp g
  have hF : ∀ n k, Rd.lpModulus p n F k = Rd.smoothnessModulus volume n p g (1 / 2 ^ k) :=
    fun n k => Rd.smoothnessModulus_congr_ae hg.coeFn_toLp n p _
  have hsup : lqNorm ∞ (fun k => dyadicWeight θ' k * Rd.lpModulus p r F k) ≤ K := by
    rw [ENNReal.lqNorm_top]
    refine iSup_le fun k => ?_
    have hk : (1 / 2 ^ k : ℝ) ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity)).2 (one_le_pow₀ one_le_two)⟩
    calc dyadicWeight θ' k * Rd.lpModulus p r F k
        ≤ dyadicWeight θ' k * (K * dyadicWeight (-θ') k) := by
          rw [hF]
          gcongr
          refine (hmod _ hk).trans ?_
          rw [ENNReal.ofReal_one_div_two_pow_rpow]
          gcongr
          exact ENNReal.dyadicWeight_le_of_le (neg_le_neg hθ') k
      _ = K := by
          rw [mul_left_comm, ENNReal.dyadicWeight_mul_neg_self, mul_one]
  refine modulusBound_of_dyadic hθ'0 (B := C * (‖F‖ₑ + K))
    (ENNReal.mul_ne_top hC (ENNReal.add_ne_top.2 ⟨enorm_ne_top, hK⟩)) fun k => ?_
  have h1 : dyadicWeight θ' k * Rd.lpModulus p r' F k ≤ C * (‖F‖ₑ + K) :=
    ((ENNReal.le_lqNorm ENNReal.top_ne_zero _ k).trans le_add_self).trans
      ((hle F).trans (by gcongr))
  calc Rd.smoothnessModulus volume r' p g (1 / 2 ^ k)
      = dyadicWeight (-θ') k * (dyadicWeight θ' k * Rd.lpModulus p r' F k) := by
        rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul, hF]
    _ ≤ dyadicWeight (-θ') k * (C * (‖F‖ₑ + K)) := by gcongr
    _ = C * (‖F‖ₑ + K) * dyadicWeight (-θ') k := mul_comm _ _

/-- **Steps from a modulus bound**: if `g` has a modulus bound of order `θ` with differences of
order `r ≥ 1`, there is a constant `K < ∞` with `‖Δ_t^r g‖_p ≤ K |t|^θ` for every `|t| ≤ 1`:
for `t ≠ 0` the step `t` is admissible for the modulus at `|t| ∈ (0, 1]`
(`Rd.eLpNorm_higherDiff_le_smoothnessModulus`), and `Δ_0^r g = 0`. -/
theorem ModulusBound.exists_eLpNorm_le {g : ℝ → ℂ} {p : ℝ≥0∞} {θ : ℝ} {r : ℕ}
    (hB : ModulusBound g p θ r) (hr : r ≠ 0) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t : ℝ, |t| ≤ 1 →
      eLpNorm ((fwdDiff t)^[r] g) p volume ≤ K * ENNReal.ofReal (|t| ^ θ) := by
  obtain ⟨K, hK, hmod⟩ := hB
  refine ⟨K, hK, fun t ht => ?_⟩
  rcases eq_or_ne t 0 with rfl | ht0
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    rw [Function.iterate_succ_apply', show fwdDiff (0 : ℝ) ((fwdDiff 0)^[n] g) = 0 from
      funext fun x => by simp [fwdDiff], eLpNorm_zero]
    exact zero_le
  · exact (Rd.eLpNorm_higherDiff_le_smoothnessModulus (by rw [Real.norm_eq_abs])).trans
      (hmod |t| ⟨abs_pos.2 ht0, ht⟩)

/-- **Steps of every order from a modulus bound**: let `1 ≤ p < ∞`, `g ∈ L_p(ℝ)` with a modulus
bound of order `θ` with differences of order `r`, and `0 ≤ θ' ≤ θ` with `θ' < r`. Then there is
a constant `A < ∞` with `‖Δ_t^n g‖_p ≤ A |t|^(θ' n / r)` for every order `n ≤ r` and every
`|t| ≤ 1`: for `n ≥ 1` by `Daubechies.ModulusBound.of_order` with the exponent
`θ' n / r < n`, and for `n = 0` with `A ≥ ‖g‖_p`. -/
theorem ModulusBound.exists_eLpNorm_le_orders {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {g : ℝ → ℂ} (hg : MemLp g p) {θ θ' : ℝ} {r : ℕ} (hB : ModulusBound g p θ r)
    (hθ'0 : 0 ≤ θ') (hθ' : θ' ≤ θ) (hθ'r : θ' < r) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ n ≤ r, ∀ t : ℝ, |t| ≤ 1 →
      eLpNorm ((fwdDiff t)^[n] g) p volume ≤ A * ENNReal.ofReal (|t| ^ (θ' * n / r)) := by
  have hr : (0 : ℝ) < r := hθ'0.trans_lt hθ'r
  have hn : ∀ n : Fin (r + 1), ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t : ℝ, |t| ≤ 1 →
      eLpNorm ((fwdDiff t)^[n] g) p volume ≤ K * ENNReal.ofReal (|t| ^ (θ' * n / r)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · refine ⟨eLpNorm g p volume, hg.eLpNorm_ne_top, fun t _ => ?_⟩
      simp [h0]
    · have hnr : (n : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 n.2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
      refine (hB.of_order hp hg (by positivity) ?_ ?_).exists_eLpNorm_le hpos.ne'
      · rw [div_le_iff₀ hr]
        nlinarith
      · rw [div_lt_iff₀ hr]
        nlinarith
  choose K hK hbound using hn
  refine ⟨∑ n, K n, ENNReal.sum_ne_top.2 fun n _ => hK n, fun n hn t ht => ?_⟩
  refine (hbound ⟨n, Nat.lt_succ_of_le hn⟩ t ht).trans ?_
  gcongr
  exact Finset.single_le_sum (f := K) (fun _ _ => zero_le) (Finset.mem_univ _)

/-- **The wavelet lies in the scaling space of level one**: for `N ≥ 2` and `1 ≤ p < ∞`, the class
of `ψ` in `L_p(ℝ)` lies in `V_1` (`Daubechies.scalingSpace`), since
`ψ = ∑_n (g_n/√2) φ_{1,n}` is an expansion of level one
(`Daubechies.waveletScaled_eq_daubechiesExpand` at level and position `0`) and the projection `P_1`
reproduces it (`Daubechies.projFun_daubechiesExpand`). -/
theorem toLp_wavelet_mem_scalingSpace (hN : 2 ≤ N) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (memLp_wavelet m hN p).toLp _ ∈ scalingSpace m p hN hp 1 := by
  have hψ : wavelet m =
      daubechiesExpand (scalingFun m) 1 (fun n => ((dualCoeff m n / √2 : ℝ) : ℂ)) := by
    funext x
    simpa [waveletScaled, scaledFun_zero] using waveletScaled_eq_daubechiesExpand m 0 0 x
  have h1 : projFun m 1 (wavelet m) = wavelet m := by
    rw [hψ, projFun_daubechiesExpand m hN]
  refine (mem_scalingSpace m).2 ⟨(memLp_wavelet m hN p).toLp _, Lp.ext ?_⟩
  refine (daubechiesProj_apply_ae m hN hp 1 _).trans ?_
  rw [projFun_congr_ae m (MemLp.coeFn_toLp _) 1, h1]
  exact (MemLp.coeFn_toLp _).symm

/-- **Modulus bounds for the wavelet**: let `N ≥ 2`, `1 ≤ p < ∞`, `θ ≥ 0`, and let `φ` have a
Bernstein bound of order `θ` with differences of order `r` (`Daubechies.BernsteinBound`). Then
the wavelet `ψ` has a modulus bound of order `θ` with differences of order `r`. Since `ψ ∈ V_1`
(`Daubechies.toLp_wavelet_mem_scalingSpace`), Bernstein's inequality
(`Daubechies.smoothnessModulus_mem_scalingSpace_le` with `j = 1`) gives
`ω_r(ψ, t)_p ≤ C ω_r(φ, 2t)_p ‖ψ‖_p ≤ C K (2t)^θ ‖ψ‖_p` for `t ≤ 1/2`, and
`ω_r(ψ, t)_p ≤ 2^r ‖ψ‖_p ≤ 2^r (2t)^θ ‖ψ‖_p` for `1/2 < t ≤ 1` (`Rd.smoothnessModulus_le`). -/
theorem modulusBound_wavelet (hN : 2 ≤ N) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {θ : ℝ}
    {r : ℕ} (hθ : 0 ≤ θ) (hB : BernsteinBound m p θ r) : ModulusBound (wavelet m) p θ r := by
  obtain ⟨K, hK, hmod⟩ := hB
  set a := (memLp_wavelet m hN p).toLp _
  refine ⟨ENNReal.ofReal (2 ^ θ) * (daubechiesBernsteinConst m p r * K + 2 ^ r) * ‖a‖ₑ,
    by finiteness [daubechiesBernsteinConst_ne_top m hN p r], fun t ht => ?_⟩
  rw [← Rd.smoothnessModulus_congr_ae (MemLp.coeFn_toLp (memLp_wavelet m hN p)) r p t]
  have h2t : ENNReal.ofReal ((2 * t) ^ θ) = ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (t ^ θ) := by
    rw [Real.mul_rpow zero_le_two ht.1.le, ENNReal.ofReal_mul (by positivity)]
  suffices h : Rd.smoothnessModulus volume r p (a : ℝ → ℂ) t ≤
      (daubechiesBernsteinConst m p r * K + 2 ^ r) * ENNReal.ofReal ((2 * t) ^ θ) * ‖a‖ₑ by
    refine h.trans_eq ?_
    rw [h2t]
    ring
  rcases le_or_gt (2 * t) 1 with h2 | h2
  · refine (smoothnessModulus_mem_scalingSpace_le m hN hp r (toLp_wavelet_mem_scalingSpace m hN hp)
      (by rwa [pow_one])).trans ?_
    rw [pow_one]
    calc daubechiesBernsteinConst m p r * Rd.smoothnessModulus volume r p (scalingFun m) (2 * t) *
            ‖a‖ₑ
        ≤ daubechiesBernsteinConst m p r * (K * ENNReal.ofReal ((2 * t) ^ θ)) * ‖a‖ₑ := by
          gcongr
          exact hmod _ ⟨by linarith [ht.1], h2⟩
      _ ≤ (daubechiesBernsteinConst m p r * K + 2 ^ r) * ENNReal.ofReal ((2 * t) ^ θ) * ‖a‖ₑ := by
          rw [← mul_assoc]
          gcongr
          exact le_self_add
  · have h1 : 1 ≤ ENNReal.ofReal ((2 * t) ^ θ) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow h2.le hθ)
    calc Rd.smoothnessModulus volume r p (a : ℝ → ℂ) t ≤ 2 ^ r * ‖a‖ₑ := by
          rw [Lp.enorm_def]
          exact Rd.smoothnessModulus_le (Lp.aestronglyMeasurable a) Fact.out r t
      _ ≤ (daubechiesBernsteinConst m p r * K + 2 ^ r) * ENNReal.ofReal ((2 * t) ^ θ) * ‖a‖ₑ := by
          gcongr
          calc (2 : ℝ≥0∞) ^ r ≤ daubechiesBernsteinConst m p r * K + 2 ^ r := le_add_self
            _ ≤ (daubechiesBernsteinConst m p r * K + 2 ^ r) * ENNReal.ofReal ((2 * t) ^ θ) :=
              le_mul_of_one_le_right' h1

/-! ### The moduli of the tensor generators -/

/-- **The moduli of smoothness of the tensor generators**: let `N ≥ 2`, `1 ≤ p < ∞`, let `φ` have
a Bernstein bound of order `θ` in `L_p` with differences of order `N`, and let `0 ≤ θ' ≤ θ` with
`θ' < N`. Then there is a constant `K < ∞` with `‖Δ_h^N Ψ^e‖_p ≤ K ‖h‖^{θ'}` for every set `e`
of coordinates and every `h ∈ ℝ^d` with `‖h‖ ≤ 1`. Both `φ` and `ψ`
(`Daubechies.modulusBound_wavelet`) satisfy `‖Δ_t^n γ‖_p ≤ A |t|^(θ' n / N)` for all orders
`n ≤ N` (`Daubechies.ModulusBound.exists_eLpNorm_le_orders`), the exponents add up to
`θ' ∑_i n_i / N = θ'` over every word, and `Rd.eLpNorm_higherDiff_tensorKernel_le` applies with
`K = d^N (A_φ + A_ψ)^d`. -/
theorem eLpNorm_higherDiff_tensorGen_le (hN : 2 ≤ N) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {θ θ' : ℝ} (hB : BernsteinBound m p θ N) (hθ'0 : 0 ≤ θ') (hθ' : θ' ≤ θ) (hθ'N : θ' < N) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ (e : Finset (Fin d)) (h : Fin d → ℝ), ‖h‖ ≤ 1 →
      eLpNorm ((fwdDiff h)^[N] (tensorGen m e)) p volume ≤ K * ENNReal.ofReal (‖h‖ ^ θ') := by
  obtain ⟨Aφ, hAφ, hφ⟩ := ModulusBound.exists_eLpNorm_le_orders hp (memLp_scalingFun m hN p)
    ((bernsteinBound_iff_modulusBound m).1 hB) hθ'0 hθ' hθ'N
  obtain ⟨Aψ, hAψ, hψ⟩ := ModulusBound.exists_eLpNorm_le_orders hp (memLp_wavelet m hN p)
    (modulusBound_wavelet m hN hp (hθ'0.trans hθ') hB) hθ'0 hθ' hθ'N
  have hN0 : (0 : ℝ) < N := by positivity
  refine ⟨(d : ℝ≥0∞) ^ N * (Aφ + Aψ) ^ d, by finiteness, fun e h hh => ?_⟩
  refine Rd.eLpNorm_higherDiff_tensorKernel_le Fact.out hp N (fun i => ?_)
    (θ := fun n => θ' * n / N) (fun n => by positivity) hθ'0 (fun n hn => ?_)
    (fun i n hn t ht => ?_) hh
  · split_ifs
    exacts [(continuous_wavelet m hN).aestronglyMeasurable,
      (continuous_scalingFun m hN).aestronglyMeasurable]
  · rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum, hn, mul_div_cancel_right₀ _ hN0.ne']
  · split_ifs
    · exact (hψ n hn t ht).trans (by gcongr; exact le_add_self)
    · exact (hφ n hn t ht).trans (by gcongr; exact le_self_add)

end Daubechies
