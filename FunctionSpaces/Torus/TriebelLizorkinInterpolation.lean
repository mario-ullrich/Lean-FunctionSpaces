/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.TriebelLizorkin
public import ApproximationSpaces.Interpolation.ApproxSpaces

/-!
# Triebel–Lizorkin spaces on the torus and real interpolation

Let `1 ≤ p < ∞`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`.  On `𝕋^d` the Triebel–Lizorkin quasi-norm
of `F^s_{p,q}` lies between the dyadic quasi-norms of `B^s_{p,max(p,q)}` and `B^s_{p,min(p,q)}`
of the trigonometric polynomials (`Torus.approxNormDyadic_le_periodicTriebelLizorkinNorm`,
`Torus.periodicTriebelLizorkinNorm_le_approxNormDyadic`), with the constants
`Torus.periodicTriebelLizorkinBesovConst` and `Torus.periodicBesovTriebelLizorkinConst`, so the
sandwich principle gives, for `0 < s₀ < s₁`,

`(F^{s₀}_{p,q₀}(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}(𝕋^d)` and
`(L_p(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))_{η,q} = B^{ηs₁}_{p,q}(𝕋^d)`

(`Torus.memKMethod_periodicTriebelLizorkinCouple_iff`,
`Torus.memKMethod_periodicLpTriebelLizorkinCouple_iff`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal TorusHaar
open ENNReal (dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ η : ℝ} {q₀ q₁ q : ℝ≥0∞}

variable (d) in
/-- The constant `2 (#d + 1) 2^((#d + 1) s) ‖Φ‖_1` of the bound of the Triebel–Lizorkin
quasi-norm on `𝕋^d` by the Besov quasi-norm
(`Torus.periodicTriebelLizorkinNorm_le_approxNormDyadic`). -/
noncomputable def periodicTriebelLizorkinBesovConst (s : ℝ) : ℝ≥0∞ :=
  2 * ((Fintype.card d : ℝ≥0∞) + 1) * dyadicWeight s (Fintype.card d + 1) *
    eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume

variable (d) in
/-- The constant `Torus.periodicTriebelLizorkinBesovConst d s` is finite. -/
theorem periodicTriebelLizorkinBesovConst_ne_top (s : ℝ) :
    periodicTriebelLizorkinBesovConst d s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩))
    (ENNReal.dyadicWeight_ne_top _ _)) Rd.eLpNorm_lpKernel_ne_top

/-- The constant `2 · 2^s (1 - 2^(-s))⁻¹` of the bound of the Besov quasi-norm on `𝕋^d` by the
Triebel–Lizorkin quasi-norm (`Torus.approxNormDyadic_le_periodicTriebelLizorkinNorm`). -/
noncomputable def periodicBesovTriebelLizorkinConst (s : ℝ) : ℝ≥0∞ :=
  2 * dyadicWeight s 1 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹

/-- The constant `Torus.periodicBesovTriebelLizorkinConst s` is finite for `s > 0`. -/
theorem periodicBesovTriebelLizorkinConst_ne_top {s : ℝ} (hs : 0 < s) :
    periodicBesovTriebelLizorkinConst s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.dyadicWeight_ne_top _ _))
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)

/-- The **couple `(F^{s₀}_{p,q₀}(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))`** on `L_p(𝕋^d)`: the two
Triebel–Lizorkin quasi-norms. -/
noncomputable def periodicTriebelLizorkinCouple (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) :
    InterpCouple (Lp ℂ p (volume : Measure (UnitAddTorus d))) :=
  ⟨periodicTriebelLizorkinNorm s₀ q₀, periodicTriebelLizorkinNorm s₁ q₁⟩

omit [Fact (1 ≤ p)] in
/-- The first norm of `(F^{s₀}_{p,q₀}(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))` is the quasi-norm of
`F^{s₀}_{p,q₀}(𝕋^d)`. -/
@[simp]
theorem periodicTriebelLizorkinCouple_norm0 (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (periodicTriebelLizorkinCouple s₀ q₀ s₁ q₁).norm0 f = periodicTriebelLizorkinNorm s₀ q₀ f := rfl

omit [Fact (1 ≤ p)] in
/-- The second norm of `(F^{s₀}_{p,q₀}(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))` is the quasi-norm of
`F^{s₁}_{p,q₁}(𝕋^d)`. -/
@[simp]
theorem periodicTriebelLizorkinCouple_norm1 (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (periodicTriebelLizorkinCouple s₀ q₀ s₁ q₁).norm1 f = periodicTriebelLizorkinNorm s₁ q₁ f := rfl

/-- The **couple `(L_p(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))`** on `L_p(𝕋^d)`: the `L_p` norm and the
Triebel–Lizorkin quasi-norm. -/
noncomputable def periodicLpTriebelLizorkinCouple (s₁ : ℝ) (q₁ : ℝ≥0∞) :
    InterpCouple (Lp ℂ p (volume : Measure (UnitAddTorus d))) :=
  ⟨fun f => ‖f‖ₑ, periodicTriebelLizorkinNorm s₁ q₁⟩

/-- The first norm of `(L_p(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))` is the `L_p` norm. -/
@[simp]
theorem periodicLpTriebelLizorkinCouple_norm0 (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (periodicLpTriebelLizorkinCouple s₁ q₁).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of `(L_p(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))` is the quasi-norm of
`F^{s₁}_{p,q₁}(𝕋^d)`. -/
@[simp]
theorem periodicLpTriebelLizorkinCouple_norm1 (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (periodicLpTriebelLizorkinCouple s₁ q₁).norm1 f = periodicTriebelLizorkinNorm s₁ q₁ f := rfl

/-- **Triebel–Lizorkin spaces on the torus interpolate to Besov spaces**: for `1 ≤ p < ∞`,
`0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, `f ∈ L_p(𝕋^d)` lies in the real
interpolation space `(F^{s₀}_{p,q₀}(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))_{η,q}` iff
`f ∈ B^{(1-η)s₀+ηs₁}_{p,q}(𝕋^d)`
(`ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches`). -/
theorem memKMethod_periodicTriebelLizorkinCouple_iff (hp : p ≠ ∞) (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    (periodicTriebelLizorkinCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      (trigScheme d).MemBesov p ((1 - η) * s₀ + η * s₁) q f := by
  rw [FunctionScheme.memBesov_iff_memApprox]
  exact ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches
    (N₀ := periodicTriebelLizorkinNorm s₀ q₀) (N₁ := periodicTriebelLizorkinNorm s₁ q₁)
    (periodicTriebelLizorkinBesovConst_ne_top d s₀) (periodicBesovTriebelLizorkinConst_ne_top hs₀)
    (periodicTriebelLizorkinBesovConst_ne_top d s₁)
      (periodicBesovTriebelLizorkinConst_ne_top (hs₀.trans hs))
    (le_min Fact.out hq₀) (le_max_of_le_right hq₀) (le_min Fact.out hq₁)
    (le_max_of_le_right hq₁) hs₀ hs hη hη' hq
    (periodicTriebelLizorkinNorm_le_approxNormDyadic hp hs₀.le hq₀)
    (approxNormDyadic_le_periodicTriebelLizorkinNorm hp hs₀ hq₀)
    (periodicTriebelLizorkinNorm_le_approxNormDyadic hp (hs₀.trans hs).le hq₁)
    (approxNormDyadic_le_periodicTriebelLizorkinNorm hp (hs₀.trans hs) hq₁)

/-- **`L_p` and a Triebel–Lizorkin space on the torus interpolate to Besov spaces**: for
`1 ≤ p < ∞`, `s₁ > 0`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, `f ∈ L_p(𝕋^d)` lies in the real
interpolation space `(L_p(𝕋^d), F^{s₁}_{p,q₁}(𝕋^d))_{η,q}` iff `f ∈ B^{ηs₁}_{p,q}(𝕋^d)`
(`ApproximationScheme.memKMethod_iff_memApprox_of_sandwich`). -/
theorem memKMethod_periodicLpTriebelLizorkinCouple_iff (hp : p ≠ ∞) (hs₁ : 0 < s₁) (hη : 0 < η)
    (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    (periodicLpTriebelLizorkinCouple s₁ q₁).MemKMethod η q f ↔
      (trigScheme d).MemBesov p (η * s₁) q f := by
  rw [FunctionScheme.memBesov_iff_memApprox]
  exact ApproximationScheme.memKMethod_iff_memApprox_of_sandwich
    (N₁ := periodicTriebelLizorkinNorm s₁ q₁)
    (periodicTriebelLizorkinBesovConst_ne_top d s₁) (periodicBesovTriebelLizorkinConst_ne_top hs₁)
    (le_min Fact.out hq₁) (le_max_of_le_right hq₁) hs₁ hη hη' hq
    (periodicTriebelLizorkinNorm_le_approxNormDyadic hp hs₁.le hq₁)
    (approxNormDyadic_le_periodicTriebelLizorkinNorm hp hs₁ hq₁)

end Torus
