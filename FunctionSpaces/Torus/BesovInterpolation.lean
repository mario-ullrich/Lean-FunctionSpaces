/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.LpBesovModuli

/-!
# Besov spaces on the torus as interpolation spaces

For `1 ≤ p < ∞` and Besov spaces by differences of order `r` on `𝕋^d`, with the quasi-norms
`‖f‖_p + ‖(2^(ks_i) ω_r(f, 2^(-k))_p)_k‖_{ℓ_{q_i}}` (the couple
`ApproximationScheme.ModulusData.modCouple` of `Torus.trigLpModulusData`), `0 < s₀ < s₁ < r`,
`0 < η < 1`, `1 ≤ q₀, q₁, q ≤ ∞` and `s = (1-η)s₀ + ηs₁`,

`f ∈ (B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q} ⟺ ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`

(`Torus.periodic_memKMethod_modCouple_iff`), and `(L_p, B^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}` by
differences (`Torus.periodic_memKMethod_leftModCouple_iff`). The Besov spaces of the
trigonometric scheme, defined by best approximation, interpolate in the same way for every
`0 < p ≤ ∞` (`FunctionScheme.memKMethod_besovCouple_iff`,
`FunctionScheme.memKMethod_lpBesovCouple_iff`), and for `0 < s < t` and every fine index
`B^s_{p,q} = (L_p, B^t_{p,q₁})_{s/t,q}` (`FunctionScheme.memBesov_iff_memKMethod_lpBesovCouple`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal TorusHaar

open ENNReal (lqNorm dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ η : ℝ} {q₀ q₁ q : ℝ≥0∞}

/-- **Besov spaces on the torus by differences interpolate**: for `1 ≤ p < ∞`, an order `r`,
`0 < s₀ < s₁ < r`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, `f ∈ L_p(𝕋^d)` lies in the real
interpolation space of the couple of the quasi-norms
`‖f‖_p + ‖(2^(ks_i) ω_r(f, 2^(-k))_p)_k‖_{ℓ_{q_i}}` iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` with `s = (1-η)s₀ + ηs₁`. -/
theorem periodic_memKMethod_modCouple_iff (hp : p ≠ ∞) {r : ℕ} (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (hs₁ : s₁ < r) (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    ((trigLpModulusData d hp r).modCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight ((1 - η) * s₀ + η * s₁) k * Rd.lpModulus p r f k) <
        ∞ :=
  (trigLpModulusData d hp r).memKMethod_modCouple_iff hs₀ hs hs₁ hη hη' hq₀ hq₁ hq

/-- **`L_p` and a Besov space by differences on the torus interpolate**: for `1 ≤ p < ∞`, an
order `r`, `0 < s₁ < r`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, `f ∈ L_p(𝕋^d)` lies in the real
interpolation space of the couple of `‖f‖_p` and
`‖f‖_p + ‖(2^(ks₁) ω_r(f, 2^(-k))_p)_k‖_{ℓ_{q₁}}` iff
`‖f‖_p + ‖(2^(kηs₁) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem periodic_memKMethod_leftModCouple_iff (hp : p ≠ ∞) {r : ℕ} (hs₁ : 0 < s₁) (hs₁r : s₁ < r)
    (hη : 0 < η) (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    ((trigLpModulusData d hp r).leftModCouple s₁ q₁).MemKMethod η q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight (η * s₁) k * Rd.lpModulus p r f k) < ∞ :=
  (trigLpModulusData d hp r).memKMethod_leftModCouple_iff hs₁ hs₁r hη hη' hq₁ hq

end Torus
