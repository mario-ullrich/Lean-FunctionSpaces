/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.Besov.Basic
public import ApproximationSpaces.Interpolation.EFunctionalRepresentation

/-!
# Besov spaces as interpolation spaces

Let `μ` be a finite measure on `Ω`, `S` a scheme of functions on `(Ω, μ)` and `0 < p ≤ ∞`. For
`s ≥ 0` and `0 < q ≤ ∞` the Besov space `B^s_{p,q}` consists of the `f ∈ L_p(μ)` of finite
dyadic norm `‖f‖_p + ‖(2^(ks) E_{2^k}(f)_p)_k‖_{ℓ_q}` of the couple of `S` in `L_p`
(`FunctionScheme.lpCouple`, `FunctionScheme.memBesov_iff_eNormDyadic_lt_top`), so the couples of
Besov spaces are couples of E-spaces of that couple:

* `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` (`FunctionScheme.besovCouple`), with the dyadic quasi-norms of
  the two Besov spaces, and
* `(L_p, B^{s₁}_{p,q₁})` (`FunctionScheme.lpBesovCouple`), with the quasi-norm of `L_p` and the
  dyadic quasi-norm of `B^{s₁}_{p,q₁}`.

The real interpolation spaces of the continuous K-method are

`(L_p, B^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}` for `s₁ > 0`, `0 < η < 1` and `0 < q₁, q ≤ ∞`,
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}` for `0 < s₀ < s₁`, `0 < η < 1` and
`1 ≤ q₀, q₁, q ≤ ∞`

(`FunctionScheme.memKMethod_lpBesovCouple_iff`, `FunctionScheme.memKMethod_besovCouple_iff`):
the representation and the reiteration theorem for the E-spaces of a quasi-normed couple
(`InterpCouple.memKMethod_leftECouple_iff`, `InterpCouple.memKMethod_eCouple_iff`), since the
couple of `S` in `L_p` is quasi-normed and its complexity is subadditive. In particular
`B^s_{p,q} = (L_p, B^r_{p,q₁})_{s/r,q}` for `0 < s < r` and all fine indices
(`FunctionScheme.memBesov_iff_memKMethod_lpBesovCouple`). For the classical Besov spaces this is
DeVore, Acta Numer. 7 (1998), (4.32); for approximation spaces it is DeVore, Acta Numer. 7
(1998), §4.3, Theorem 2, due to DeVore–Popov, LNM 1302 (1988). Both
interpolation theorems are also equalities of subspaces of `L_p(μ)`
(`FunctionScheme.kMethodSpace_lpBesovCouple`, `FunctionScheme.kMethodSpace_besovCouple`), and
the couples of Pietsch's quasi-norms `FunctionScheme.besovNorm` have the same interpolation
spaces (`FunctionScheme.memKMethod_lpBesovNormCouple_iff`,
`FunctionScheme.memKMethod_besovNormCouple_iff`), since Pietsch's form and the dyadic norm bound
each other (`InterpCouple.eNormPietsch_le_eNormDyadic`, `InterpCouple.eNormDyadic_le_eNormPietsch`).

The fine indices `≥ 1` of the couple of two Besov spaces are those of the reiteration theorem
`InterpCouple.memKMethod_kCouple_iff`; DeVore–Popov, Trans. Amer. Math. Soc. 305 (1988),
Corollary 6.2, interpolate two classical Besov spaces of positive smoothness for every fine
index. The statements hold for every exponent `p`; at `p = 0` all quasi-norms vanish.

For `1 ≤ p ≤ ∞` the couple of `S` in `L_p` is the complexity couple of the scheme
`S^(p) = S.toLp p` in the normed space `L_p(μ)`, and the two couples are the couples
`(A^{s₀}_{q₀}, A^{s₁}_{q₁})` and `(L_p, A^{s₁}_{q₁})` of approximation spaces of `S^(p)`
(`FunctionScheme.besovCouple_eq_approxCouple`, `FunctionScheme.lpBesovCouple_eq_leftApproxCouple`),
whose interpolation spaces for fine indices `≥ 1` are also given by the reiteration theorem for
approximation spaces (`ApproximationScheme.memKMethod_approxCouple_iff`,
`ApproximationScheme.memKMethod_approxCouple_zero_iff`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FunctionScheme

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (S : FunctionScheme μ) (p : ℝ≥0∞)

/-- The **couple `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})`** of two Besov spaces of the scheme, on
`L_p(μ)`, for every exponent `p`: the couple `(E_{s₀,q₀}, E_{s₁,q₁})` of the couple of `S` in
`L_p`, with the dyadic quasi-norms `‖f‖_p + ‖(2^(ks_i) E_{2^k}(f)_p)_k‖_{ℓ_{q_i}}` of the two
Besov spaces. -/
noncomputable abbrev besovCouple (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) :
    InterpCouple (Lp ℂ p μ) :=
  (S.lpCouple p).eCouple s₀ q₀ s₁ q₁

/-- The **couple `(L_p, B^{s₁}_{p,q₁})`** of the scheme, for every exponent `p`: the couple
`(N₀, E_{s₁,q₁})` of the couple of `S` in `L_p`, with the quasi-norm `‖f‖_p` of `L_p(μ)` and the
dyadic quasi-norm `‖f‖_p + ‖(2^(ks₁) E_{2^k}(f)_p)_k‖_{ℓ_{q₁}}` of the Besov space
`B^{s₁}_{p,q₁}`. -/
noncomputable abbrev lpBesovCouple (s₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple (Lp ℂ p μ) :=
  (S.lpCouple p).leftECouple s₁ q₁

variable {S p} {s s₀ s₁ r η : ℝ} {q q₀ q₁ : ℝ≥0∞}

/-! ### The couples for `p ≥ 1` -/

/-- **For `p ≥ 1` the couple of two Besov spaces is a couple of approximation spaces**: for
`1 ≤ p ≤ ∞` the couple `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})` is the couple `(A^{s₀}_{q₀}, A^{s₁}_{q₁})`
of the scheme `S^(p) = S.toLp p` in `L_p(μ)`, since the couple of `S` in `L_p` is the complexity
couple of `S^(p)` (`FunctionScheme.lpCouple_eq_complexityCouple`), whose dyadic norms are those of
the approximation spaces (`ApproximationScheme.eNormDyadic_complexityCouple`). -/
theorem besovCouple_eq_approxCouple [Fact (1 ≤ p)] :
    S.besovCouple p s₀ q₀ s₁ q₁ = (S.toLp p).approxCouple s₀ q₀ s₁ q₁ := by
  show (⟨(S.lpCouple p).eNormDyadic s₀ q₀, (S.lpCouple p).eNormDyadic s₁ q₁⟩ :
      InterpCouple (Lp ℂ p μ)) =
    ⟨(S.toLp p).approxNormDyadic s₀ q₀, (S.toLp p).approxNormDyadic s₁ q₁⟩
  rw [lpCouple_eq_complexityCouple]
  congr 1 <;> exact funext ApproximationScheme.eNormDyadic_complexityCouple

/-- **For `p ≥ 1` the couple `(L_p, B^{s₁}_{p,q₁})` is a couple of approximation spaces**: for
`1 ≤ p ≤ ∞` it is the couple `(L_p, A^{s₁}_{q₁})` of the scheme `S^(p) = S.toLp p` in `L_p(μ)`,
with the norm `‖f‖ₑ = ‖f‖_p` of `L_p(μ)` (`FunctionScheme.lpCouple_eq_complexityCouple`,
`ApproximationScheme.eNormDyadic_complexityCouple`). -/
theorem lpBesovCouple_eq_leftApproxCouple [Fact (1 ≤ p)] :
    S.lpBesovCouple p s₁ q₁ = (S.toLp p).leftApproxCouple s₁ q₁ := by
  show (⟨(S.lpCouple p).norm0, (S.lpCouple p).eNormDyadic s₁ q₁⟩ : InterpCouple (Lp ℂ p μ)) =
    ⟨fun f => ‖f‖ₑ, (S.toLp p).approxNormDyadic s₁ q₁⟩
  rw [lpCouple_eq_complexityCouple]
  congr 1
  exact funext ApproximationScheme.eNormDyadic_complexityCouple

/-! ### Interpolation of Besov spaces -/

/-- **Besov spaces interpolate**: for every scheme of functions, every exponent `p`,
`0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`,
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}`: the reiteration theorem for
E-spaces (`InterpCouple.memKMethod_eCouple_iff`) for the couple of `S` in `L_p`, which is
quasi-normed with subadditive complexity (`FunctionScheme.isQuasiNormed_lpCouple`,
`FunctionScheme.lpCouple_norm1_add_le`), and the description of the Besov space by the dyadic
norm (`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`). For the classical Besov spaces this is
DeVore–Popov, Trans. Amer. Math. Soc. 305 (1988), Corollary 6.2, which holds for every fine
index. -/
theorem memKMethod_besovCouple_iff (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p μ} :
    (S.besovCouple p s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      S.MemBesov p ((1 - η) * s₀ + η * s₁) q f :=
  (InterpCouple.memKMethod_eCouple_iff (isQuasiNormed_lpCouple S p) lpCouple_norm1_add_le hs₀ hs
    hη hη' hq₀ hq₁ hq).trans
      (memBesov_iff_eNormDyadic_lt_top (zero_lt_one.trans_le hq).ne'
        (ApproximationScheme.reiterationExponent_pos hs₀ hs hη hη').le).symm

/-- **`L_p` and a Besov space interpolate**: for every scheme of functions, every exponent `p`,
`s₁ > 0`, `0 < η < 1` and `0 < q₁, q ≤ ∞`, `(L_p, B^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}`: the
representation of E-spaces as interpolation spaces (`InterpCouple.memKMethod_leftECouple_iff`)
for the couple of `S` in `L_p`, and the description of the Besov space by the dyadic norm
(`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`). -/
theorem memKMethod_lpBesovCouple_iff (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1) (hq₁ : q₁ ≠ 0)
    (hq : q ≠ 0) {f : Lp ℂ p μ} :
    (S.lpBesovCouple p s₁ q₁).MemKMethod η q f ↔ S.MemBesov p (η * s₁) q f :=
  (InterpCouple.memKMethod_leftECouple_iff (isQuasiNormed_lpCouple S p) lpCouple_norm1_add_le hs₁
    hη hη' hq₁ hq).trans (memBesov_iff_eNormDyadic_lt_top hq (mul_pos hη hs₁).le).symm

/-- **Besov spaces by the representation**: for every scheme of functions, every exponent `p`,
`0 < s < r` and `0 < q, q₁ ≤ ∞`, `B^s_{p,q} = (L_p, B^r_{p,q₁})_{s/r,q}`, the case
`η = s/r` of `FunctionScheme.memKMethod_lpBesovCouple_iff`. For the classical Besov spaces this
is DeVore, Acta Numer. 7 (1998), (4.32); for approximation spaces it is DeVore, Acta Numer. 7
(1998), §4.3, Theorem 2, due to DeVore–Popov, LNM 1302 (1988). -/
theorem memBesov_iff_memKMethod_lpBesovCouple (hs : 0 < s) (hsr : s < r) (hq₁ : q₁ ≠ 0)
    (hq : q ≠ 0) {f : Lp ℂ p μ} :
    S.MemBesov p s q f ↔ (S.lpBesovCouple p r q₁).MemKMethod (s / r) q f := by
  have hr : 0 < r := hs.trans hsr
  rw [memKMethod_lpBesovCouple_iff hr (div_pos hs hr) ((div_lt_one hr).2 hsr) hq₁ hq,
    div_mul_cancel₀ s hr.ne']

/-- **Besov spaces interpolate**, as an equality of subspaces of `L_p(μ)`: for `0 < s₀ < s₁`,
`0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, the real interpolation space
`(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q}` of the quasi-normed homogeneous couple
(`InterpCouple.isQuasiNormed_eCouple`, `InterpCouple.isHomogeneousCouple_eCouple`) is
`B^{(1-η)s₀+ηs₁}_{p,q}`. -/
theorem kMethodSpace_besovCouple (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) :
    InterpCouple.kMethodSpace (A := S.besovCouple p s₀ q₀ s₁ q₁)
        (InterpCouple.isQuasiNormed_eCouple (isQuasiNormed_lpCouple S p) lpCouple_norm1_add_le
          s₀ q₀ s₁ q₁)
        (InterpCouple.isHomogeneousCouple_eCouple (lpCouple_norm1_zero S p)
          (fun c g => (lpCouple_norm0_smul c g).le) (fun c _ g => lpCouple_norm1_smul_le c g)
          s₀ q₀ s₁ q₁) η q =
      S.besovSpace p ((1 - η) * s₀ + η * s₁) q
        (ApproximationScheme.reiterationExponent_pos hs₀ hs hη hη').le
        (zero_lt_one.trans_le hq).ne' :=
  Submodule.ext fun _ =>
    (memKMethod_besovCouple_iff hs₀ hs hη hη' hq₀ hq₁ hq).trans mem_besovSpace.symm

/-- **`L_p` and a Besov space interpolate**, as an equality of subspaces of `L_p(μ)`: for
`s₁ > 0`, `0 < η < 1` and `0 < q₁, q ≤ ∞`, the real interpolation space
`(L_p, B^{s₁}_{p,q₁})_{η,q}` of the quasi-normed homogeneous couple
(`InterpCouple.isQuasiNormed_leftECouple`, `InterpCouple.isHomogeneousCouple_leftECouple`) is
`B^{ηs₁}_{p,q}`. -/
theorem kMethodSpace_lpBesovCouple (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1) (hq₁ : q₁ ≠ 0)
    (hq : q ≠ 0) :
    InterpCouple.kMethodSpace (A := S.lpBesovCouple p s₁ q₁)
        (InterpCouple.isQuasiNormed_leftECouple (isQuasiNormed_lpCouple S p) lpCouple_norm1_add_le
          s₁ q₁)
        (InterpCouple.isHomogeneousCouple_leftECouple (lpCouple_norm1_zero S p)
          (fun c g => (lpCouple_norm0_smul c g).le) (fun c _ g => lpCouple_norm1_smul_le c g)
          s₁ q₁) η q =
      S.besovSpace p (η * s₁) q (mul_pos hη hs₁).le hq :=
  Submodule.ext fun _ => (memKMethod_lpBesovCouple_iff hs₁ hη hη' hq₁ hq).trans mem_besovSpace.symm

/-! ### The couples of Pietsch's quasi-norms -/

/-- **Besov spaces interpolate, with Pietsch's quasi-norms**: for every exponent `p`,
`0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, the real interpolation space of the couple
of the Besov quasi-norms `FunctionScheme.besovNorm` of `B^{s₀}_{p,q₀}` and `B^{s₁}_{p,q₁}` is
`B^{(1-η)s₀+ηs₁}_{p,q}`. Pietsch's form of smoothness `s ≥ 0` is at most `C_q 2^s` times the
dyadic norm, and the dyadic norm at most `4 C_q² 2^s` times Pietsch's form
(`InterpCouple.eNormPietsch_le_eNormDyadic`, `InterpCouple.eNormDyadic_le_eNormPietsch`), so the
couple has the interpolation spaces of the couple of dyadic quasi-norms
(`InterpCouple.memKMethod_congr`). -/
theorem memKMethod_besovNormCouple_iff (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : Lp ℂ p μ} :
    (⟨S.besovNorm p s₀ q₀, S.besovNorm p s₁ q₁⟩ : InterpCouple (Lp ℂ p μ)).MemKMethod η q f ↔
      S.MemBesov p ((1 - η) * s₀ + η * s₁) q f :=
  (InterpCouple.memKMethod_congr (B := S.besovCouple p s₀ q₀ s₁ q₁)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.LpAddConst_lt_top q₀).ne) (by norm_num))
      (ENNReal.two_rpow_ne_top s₀))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.LpAddConst_lt_top q₁).ne) (by norm_num))
      (ENNReal.two_rpow_ne_top s₁))
    (ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q₀).ne (ENNReal.two_rpow_ne_top s₀))
    (ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q₁).ne (ENNReal.two_rpow_ne_top s₁))
    (InterpCouple.eNormDyadic_le_eNormPietsch (fun _ hb => eq_zero_of_lpCouple_norm1_lt_one hb)
      (zero_lt_one.trans_le hq₀).ne' hs₀.le)
    (InterpCouple.eNormDyadic_le_eNormPietsch (fun _ hb => eq_zero_of_lpCouple_norm1_lt_one hb)
      (zero_lt_one.trans_le hq₁).ne' (hs₀.trans hs).le)
    (InterpCouple.eNormPietsch_le_eNormDyadic (lpCouple_norm1_zero S p) hs₀.le)
    (InterpCouple.eNormPietsch_le_eNormDyadic (lpCouple_norm1_zero S p) (hs₀.trans hs).le)).trans
    (memKMethod_besovCouple_iff hs₀ hs hη hη' hq₀ hq₁ hq)

/-- **`L_p` and a Besov space interpolate, with Pietsch's quasi-norm**: for every exponent `p`,
`s₁ > 0`, `0 < η < 1` and `0 < q₁, q ≤ ∞`, the real interpolation space of the couple of the
quasi-norm `‖f‖_p` of `L_p(μ)` and the Besov quasi-norm `FunctionScheme.besovNorm` of
`B^{s₁}_{p,q₁}` is `B^{ηs₁}_{p,q}`, by the equivalence of Pietsch's form and the dyadic norm
(`InterpCouple.eNormPietsch_le_eNormDyadic`, `InterpCouple.eNormDyadic_le_eNormPietsch`,
`InterpCouple.memKMethod_congr`). -/
theorem memKMethod_lpBesovNormCouple_iff (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1)
    (hq₁ : q₁ ≠ 0) (hq : q ≠ 0) {f : Lp ℂ p μ} :
    (⟨fun g => eLpNorm g p μ, S.besovNorm p s₁ q₁⟩ : InterpCouple (Lp ℂ p μ)).MemKMethod η q f ↔
      S.MemBesov p (η * s₁) q f :=
  (InterpCouple.memKMethod_congr
    (A := (⟨fun g => eLpNorm g p μ, S.besovNorm p s₁ q₁⟩ : InterpCouple (Lp ℂ p μ)))
    (B := S.lpBesovCouple p s₁ q₁)
    ENNReal.one_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.LpAddConst_lt_top q₁).ne) (by norm_num))
      (ENNReal.two_rpow_ne_top s₁))
    ENNReal.one_ne_top
    (ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q₁).ne (ENNReal.two_rpow_ne_top s₁))
    (fun g => (one_mul (eLpNorm g p μ)).ge)
    (InterpCouple.eNormDyadic_le_eNormPietsch (fun _ hb => eq_zero_of_lpCouple_norm1_lt_one hb)
      hq₁ hs₁.le)
    (fun g => (one_mul (eLpNorm g p μ)).ge)
    (InterpCouple.eNormPietsch_le_eNormDyadic (lpCouple_norm1_zero S p) hs₁.le)).trans
    (memKMethod_lpBesovCouple_iff hs₁ hη hη' hq₁ hq)

end FunctionScheme
