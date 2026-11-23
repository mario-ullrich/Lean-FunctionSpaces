/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.HaarSchauderBasis

/-!
# `n`-term Haar approximation and Besov spaces for every `0 < τ < 2`

Let `0 < τ < 2` and `θ = 1/τ - 1/2`. Best `n`-term approximation from the Haar basis in
`L_2[0, 1]` is described by the Haar coefficients in `ℓ_τ` (`Haar.memApprox_nTerm_iff_haarCoeff`).
For `τ ≤ 1` the Haar coefficient characterisation of the step couple in the quasi-Banach space
`L_τ[0, 1]` (`Haar.memEMethod_stepCouple_iff_haarCoeff` with `p = q = τ` and `s = θ`, where the
weight `2^(k(s + 1/2 - 1/p))` is `1` and `θ > 1/τ - 1` holds always) gives

* `f ∈ A^θ_τ(L_2, n-term)` iff the class of `f` in `L_τ` lies in the approximation space
  `E_{θ,τ}` of dyadic steps in `L_τ` (`Haar.memApprox_nTerm_iff_memEMethod`);
* every element of `E_{θ,τ}` is the class of a function in `L_2`
  (`Haar.exists_inclusion_eq_of_memEMethod`): its Haar coefficients lie in `ℓ_τ ⊆ ℓ_2`, the Haar
  basis gives a function `F ∈ L_2` with the same coefficients, and an integrable function is
  determined by its Haar coefficients (`Haar.ae_eq_zero_of_haarCoeff_eq_zero`). So the two
  approximation spaces are equal as sets.

With the step-couple characterisation by the first modulus
(`Haar.memEMethod_stepCouple_iff_modulus`) for `τ ≤ 1`, and the case `1 ≤ τ < 2`
(`Haar.memApprox_nTerm_iff_modulus`), this gives for every `0 < τ < 2`
(`Haar.memApprox_nTerm_iff_intervalModulus_of_lt_two`)

`f ∈ A^θ_τ(L_2, n-term Haar)  ⟺  ‖f‖_τ + ‖(2^(kθ) ω_1(f, 2^(-k), [0, 1])_τ)_k‖_{ℓ_τ} < ∞`.

For `2/3 < τ < 2`, that is `θ < 1`, the right side is the classical Besov space
`B^θ_{τ,τ}[0, 1]` (DeVore, *Nonlinear approximation*, Acta Numer. 7, 1998, §3.6), and the
equivalence is the Haar case of the theorem of DeVore–Jawerth–Popov (*Compression of wavelet
decompositions*, Amer. J. Math. 114, 1992); for `τ ≤ 2/3` the right side is the space
`B^θ_{τ,τ,1}[0, 1]` of the first modulus.
-/

@[expose] public section

open MeasureTheory Set Filter ApproximationScheme Interval
open scoped ENNReal
open ENNReal (dyadicWeight lqNorm)

namespace Haar

/-- `τ ≤ 2` gives the exponent bound `ofReal τ ≤ 2` of the inclusion `L_2 ⊆ L_τ`. -/
theorem ofReal_le_two {τ : ℝ} (hτ2 : τ ≤ 2) : ENNReal.ofReal τ ≤ 2 :=
  (ENNReal.ofReal_le_ofReal hτ2).trans_eq (ENNReal.ofReal_ofNat 2)

/-- **A sequence in `ℓ_τ`, `0 < τ ≤ 2`, is square summable**: if `∑ |a_n|^τ < ∞` then
`a ∈ ℓ_2` (Mathlib's `Memℓp.of_exponent_ge`). -/
theorem mem_l2_of_tsum_enorm_rpow_ne_top {a : ℕ → ℂ} {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ ≤ 2)
    (ha : ∑' n, ‖a n‖ₑ ^ τ ≠ ∞) : Memℓp a 2 := by
  have hτ : (ENNReal.ofReal τ).toReal = τ := ENNReal.toReal_ofReal hτ0.le
  have h1 : Memℓp a (ENNReal.ofReal τ) := by
    rw [memℓp_gen_iff (by rw [hτ]; exact hτ0), hτ]
    have hpt : ∀ n, ‖a n‖ₑ ^ τ = ENNReal.ofReal (‖a n‖ ^ τ) := fun n => by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hτ0.le]
    simp_rw [hpt] at ha
    exact (ENNReal.summable_toReal ha).congr fun n => ENNReal.toReal_ofReal (by positivity)
  exact h1.of_exponent_ge (ofReal_le_two hτ2)

/-- **Nonlinear approximation in `L_2` is approximation by steps in `L_τ`, `0 < τ ≤ 1`**: with
`θ = 1/τ - 1/2`, `f ∈ L_2[0, 1]` lies in the approximation space `A^θ_τ` of `n`-term approximation
from the Haar basis iff its class in `L_τ[0, 1]` lies in the approximation space `E_{θ,τ}` of the
step couple. Both conditions are `∑_k ∑_{i<2^k} |⟨f, h_{k,i}⟩|^τ < ∞`
(`Haar.memApprox_nTerm_iff_haarCoeff`, `Haar.memEMethod_stepCouple_iff_haarCoeff` with `p = q = τ`
and `s = θ`, where the weight `2^(k(s + 1/2 - 1/τ))` is `1`); for `f ∈ L_2` the integrability
is free. -/
theorem memApprox_nTerm_iff_memEMethod {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (f : Lp ℂ 2 vol) :
    (nTerm haarBasis.coeffDictionary).MemApprox (1 / τ - 1 / 2) (ENNReal.ofReal τ) f ↔
      (stepCouple (ENNReal.ofReal τ)).MemEMethod (1 / τ - 1 / 2) (ENNReal.ofReal τ)
        (Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) vol (ofReal_le_two (by linarith)) f) := by
  set p := ENNReal.ofReal τ
  have hp0 : p ≠ 0 := (ENNReal.ofReal_pos.2 hτ0).ne'
  have hp1 : p ≤ 1 := ENNReal.ofReal_le_one.2 hτ1
  have hpτ : p.toReal = τ := ENNReal.toReal_ofReal hτ0.le
  have hs : 1 / p.toReal - 1 < 1 / τ - 1 / 2 := by rw [hpτ]; linarith
  set g := Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) vol
    (ofReal_le_two (τ := τ) (by linarith)) f
  have hg : (g : ℝ → ℂ) =ᵐ[vol] f := Lp.coeFn_inclusionOfExponentLeLinear _ f
  have hgi : Integrable g vol := ((Lp.memLp f).integrable (by norm_num)).congr hg.symm
  rw [memApprox_nTerm_iff_haarCoeff hτ0 (by linarith) f,
    memEMethod_stepCouple_iff_haarCoeff hp0 hp1 hs hp0 g, hpτ,
    show 1 / τ - 1 / 2 + (1 / 2 - 1 / τ) = 0 by ring, integral_congr_ae hg]
  simp only [ENNReal.dyadicWeight_zero_left, one_mul, haarCoeff_congr_ae hg, hgi, true_and]
  rw [ENNReal.add_lt_top, ENNReal.add_lt_top, ENNReal.rpow_lt_top_iff_of_pos hτ0, ← hpτ,
    ← ENNReal.rpow_lt_top_iff_of_pos (hpτ ▸ hτ0) (x := lqNorm p _),
    ENNReal.lqNorm_lqNorm_rpow hp0 ENNReal.ofReal_ne_top]
  simp only [tsum_fintype]

/-- **Every element of the approximation space of steps in `L_τ`, `0 < τ ≤ 1`, with
`θ = 1/τ - 1/2`, is a function in `L_2`**: if `g ∈ L_τ[0, 1]` lies in `E_{θ,τ}` of the step
couple, then `g` is the class of some `f ∈ L_2[0, 1]`. The Haar coefficients of `g` lie in
`ℓ_τ ⊆ ℓ_2` (`Haar.memEMethod_stepCouple_iff_haarCoeff`), so the Haar basis gives `F ∈ L_2` with
the same coefficients, and `F - g ∈ L_1` has no Haar coefficients, so `F = g` almost everywhere
(`Haar.ae_eq_zero_of_haarCoeff_eq_zero`). -/
theorem exists_inclusion_eq_of_memEMethod {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {g : Lp ℂ (ENNReal.ofReal τ) vol}
    (hg : (stepCouple (ENNReal.ofReal τ)).MemEMethod (1 / τ - 1 / 2) (ENNReal.ofReal τ) g) :
    ∃ f : Lp ℂ 2 vol,
      Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) vol (ofReal_le_two (by linarith)) f = g := by
  have hp0 : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.2 hτ0).ne'
  have hp1 : ENNReal.ofReal τ ≤ 1 := ENNReal.ofReal_le_one.2 hτ1
  have hpτ : (ENNReal.ofReal τ).toReal = τ := ENNReal.toReal_ofReal hτ0.le
  have hs : 1 / (ENNReal.ofReal τ).toReal - 1 < 1 / τ - 1 / 2 := by rw [hpτ]; linarith
  obtain ⟨hgi, hfin⟩ := (memEMethod_stepCouple_iff_haarCoeff hp0 hp1 hs hp0 g).1 hg
  rw [hpτ, show 1 / τ - 1 / 2 + (1 / 2 - 1 / τ) = 0 by ring] at hfin
  simp only [ENNReal.dyadicWeight_zero_left, one_mul] at hfin
  have hcoef : ∑' k, ∑ m : Fin (2 ^ k), ‖haarCoeff g k ((m : ℕ) : ℤ)‖ₑ ^ τ ≠ ∞ := by
    have h := (ENNReal.add_lt_top.1 hfin).2
    rw [← ENNReal.rpow_lt_top_iff_of_pos (by rw [hpτ]; exact hτ0 : 0 < (ENNReal.ofReal τ).toReal),
      ENNReal.lqNorm_lqNorm_rpow hp0 ENNReal.ofReal_ne_top] at h
    simpa only [tsum_fintype, hpτ] using h.ne
  have hsys : ∀ k (m : Fin (2 ^ k)), haarSystemCoeff g (2 ^ k + m) = haarCoeff g k m :=
    fun k m => haarSystemCoeff_two_pow_add g m.isLt
  have ha : ∑' n, ‖haarSystemCoeff g n‖ₑ ^ τ ≠ ∞ := by
    rw [ENNReal.tsum_eq_add_tsum_two_pow_add, haarSystemCoeff_zero]
    simp only [hsys]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg hτ0.le enorm_ne_top, hcoef⟩
  set F : Lp ℂ 2 vol := haarBasis.repr.symm
    ⟨haarSystemCoeff g, mem_l2_of_tsum_enorm_rpow_ne_top hτ0 (by linarith) ha⟩
  have hF : ∀ n, haarSystemCoeff F n = haarSystemCoeff g n := fun n => by
    rw [haarSystemCoeff, ← haarBasis_repr_apply, LinearIsometryEquiv.apply_symm_apply]
  have hFi : Integrable F vol := (Lp.memLp F).integrable (by norm_num)
  have h0 : ∫ x, F x - g x ∂vol = 0 := by
    rw [integral_sub hFi hgi, ← haarSystemCoeff_zero, ← haarSystemCoeff_zero, hF, sub_self]
  have hc : ∀ k (m : Fin (2 ^ k)), haarCoeff (⇑F - ⇑g) k ((m : ℕ) : ℤ) = 0 := fun k m => by
    rw [haarCoeff_sub hFi hgi, ← haarSystemCoeff_two_pow_add _ m.isLt,
      ← haarSystemCoeff_two_pow_add _ m.isLt, hF, sub_self]
  have hdiff := ae_eq_zero_of_haarCoeff_eq_zero (hFi.sub hgi) h0 hc
  refine ⟨F, Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_inclusionOfExponentLeLinear (𝕜 := ℝ)
    (ofReal_le_two (τ := τ) (by linarith)) F, hdiff] with x h1 h2
  rw [h1]
  simpa [sub_eq_zero] using h2

/-- **Best `n`-term Haar approximation in `L_2` and Besov spaces of the first modulus, every
`0 < τ < 2`** (for `2/3 < τ < 2` the Haar case of DeVore–Jawerth–Popov): with
`θ = 1/τ - 1/2`, `f ∈ L_2[0, 1]` lies in the approximation space `A^θ_τ` of `n`-term
approximation from the Haar basis iff `‖f‖_τ + ‖(2^(kθ) ω_1(f, 2^(-k), [0, 1])_τ)_k‖_{ℓ_τ} < ∞`.
For `τ ≤ 1` by the step couple in the quasi-Banach space `L_τ`
(`Haar.memApprox_nTerm_iff_memEMethod`, `Haar.memEMethod_stepCouple_iff_modulus`), for
`1 < τ < 2` by `Haar.memApprox_nTerm_iff_modulus`. For `2/3 < τ < 2` the right side is the
classical Besov space `B^θ_{τ,τ}[0, 1]` (DeVore 1998, §3.6); for `τ ≤ 2/3`, where `θ ≥ 1`, it is
the space of the first modulus. -/
theorem memApprox_nTerm_iff_intervalModulus_of_lt_two {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2)
    (f : Lp ℂ 2 vol) :
    (nTerm haarBasis.coeffDictionary).MemApprox (1 / τ - 1 / 2) (ENNReal.ofReal τ) f ↔
      eLpNorm f (ENNReal.ofReal τ) vol + lqNorm (ENNReal.ofReal τ) (fun k =>
        dyadicWeight (1 / τ - 1 / 2) k *
          Interval.intervalModulus 1 (ENNReal.ofReal τ) 0 1 f (1 / 2 ^ k)) < ∞ := by
  have hpτ : (ENNReal.ofReal τ).toReal = τ := ENNReal.toReal_ofReal hτ0.le
  rcases le_or_gt τ 1 with hτ1 | hτ1
  · have hp0 : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.2 hτ0).ne'
    have hθ0 : 0 < 1 / τ - 1 / 2 := by
      have := one_div_lt_one_div_of_lt hτ0 hτ2
      linarith
    have hθp : 1 / τ - 1 / 2 < 1 / (ENNReal.ofReal τ).toReal := by
      rw [hpτ]
      linarith
    have hg := Lp.coeFn_inclusionOfExponentLeLinear (𝕜 := ℝ)
      (ofReal_le_two (τ := τ) (by linarith)) f
    rw [memApprox_nTerm_iff_memEMethod hτ0 hτ1 f, memEMethod_stepCouple_iff_modulus hp0
      (ENNReal.ofReal_le_one.2 hτ1) hp0 hθ0 hθp, Lp.enorm_def, eLpNorm_congr_ae hg]
    simp only [Interval.intervalLpModulus, intervalModulus_congr_ae hg]
  · have : Fact (1 ≤ ENNReal.ofReal τ) := ⟨ENNReal.one_le_ofReal.2 hτ1.le⟩
    have hp2 : ENNReal.ofReal τ < 2 := by
      rw [← ENNReal.ofReal_ofNat 2]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hτ2
    have hg := Lp.coeFn_inclusionOfExponentLe (𝕜 := ℝ) hp2.le f
    have h := memApprox_nTerm_iff_modulus hp2 f
    rw [hpτ] at h
    rw [h, Lp.enorm_def, eLpNorm_congr_ae hg]
    simp only [Interval.intervalLpModulus, intervalModulus_congr_ae hg]

end Haar
