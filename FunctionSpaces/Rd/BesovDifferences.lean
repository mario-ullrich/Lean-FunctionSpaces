/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.BandJackson
public import FunctionSpaces.Rd.BandInverse
public import FunctionSpaces.Rd.LittlewoodPaley
public import ApproximationSpaces.Moduli

/-!
# Besov spaces on `V` by differences

For `1 ≤ p < ∞` and `r ≥ 1`, the modulus of smoothness `ω_r(f, t)_p` of `f ∈ L_p(V)` is
compatible with the band-limited scheme with inverse order `r` (`Rd.bandModulusData`):
Jackson's inequality `E(f, E_k)_p ≤ C_J ω_r(f, 2^(-k))_p` (`Rd.approxSeq_bandScheme_le`) and the
inverse inequality `ω_r(a, 2^(-k))_p ≤ C_B 2^(-(k-j) r) ‖a‖_p` for `a ∈ E_j`
(`Rd.lpModulus_le_of_mem_bandSpace`). The coincidence theorem for moduli
(`ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top`) gives, for `0 ≤ s < r`:

`f ∈ A^s_q(L_p, (E_k))  ⟺  ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`

(`Rd.memApprox_bandScheme_iff_modulus`). With the Littlewood–Paley characterisation
(`Rd.memApprox_bandScheme_iff`), the three descriptions of `B^s_{p,q}(V)` coincide for `0 < s < r`:
by approximation with band-limited functions, by Littlewood–Paley blocks, and by differences
(`Rd.littlewoodPaleyNorm_lt_top_iff_modulus`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The modulus of smoothness is compatible with the band-limited scheme**, with inverse order
`r`: Jackson's inequality from level `0` on, and the inverse inequality for band-limited
functions. -/
noncomputable def bandModulusData (hp : p ≠ ∞) (r : ℕ) :
    ApproximationScheme.ModulusData (bandScheme (V := V) hp) r where
  modulus f k := lpModulus p r f k
  add_le f g k := lpModulus_add_le r f g k
  C0 := 2 ^ r
  C0_ne_top := by simp
  le_enorm f k := lpModulus_le r f k
  jacksonStart := 0
  CJ := jacksonConst V r p
  CJ_ne_top := jacksonConst_ne_top Fact.out hp r
  jackson f k _ := approxSeq_bandScheme_le hp r k f
  CB := bandInverseConst V r
  CB_ne_top := bandInverseConst_ne_top r
  inverse _ _ _ ha := lpModulus_le_of_mem_bandSpace hp r (mem_bandScheme_two_pow.1 ha)

/-- **Band-limited approximation and moduli of smoothness**: for `1 ≤ p < ∞`, `0 ≤ s < r` and
`1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p, (E_k))` iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem memApprox_bandScheme_iff_modulus (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).MemApprox s q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ :=
  (bandModulusData hp r).memApprox_iff_modNorm_lt_top hq hs hsr f

/-- **Littlewood–Paley blocks and moduli of smoothness**: for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞`, `(2^(js) ‖ψ_j ⋆ f‖_p)_j ∈ ℓ_q` iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem littlewoodPaleyNorm_lt_top_iff_modulus (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    littlewoodPaleyNorm hp s q f < ∞ ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ := by
  rw [← memApprox_bandScheme_iff hp hs hq, memApprox_bandScheme_iff_modulus hp hs.le hsr hq f]

end Rd
