/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.Haar
public import FunctionSpaces.Interval.PiecewisePeriodic
public import ApproximationSpaces.Transfer

/-!
# Haar coefficients and Besov spaces on the interval and on the circle

The Haar scheme of `FunctionSpaces.Wavelets.Examples.Haar` (step functions on the dyadic
intervals, in `L_p[0, 1)`) is the scheme of dyadic piecewise polynomials of degree `< 1`
(`Interval.ppScheme p 1`, in `L_p[0, 1]`). Lebesgue measure on `[0, 1)` and on `[0, 1]` is the
same measure (`Haar.vol_eq_unitVol`), so the identity of functions is an isometry between the
two `L_p` spaces (`Haar.toHaar`, `Haar.ofHaar`), and it maps the approximants onto each other:
a function measurable for the dyadic `σ`-algebra of level `j` is a step function on the dyadic
intervals of level `j`. Hence the two schemes have the same approximation spaces
(`Haar.memApprox_ppScheme_one_iff`).

Together with the characterisations through moduli of smoothness this gives, for `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞` and `0 < s < 1/p`, three equivalent descriptions of one space:

* `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞` (Besov space on the interval),
* `‖f‖_p + ‖(2^(ks) ω_1^per(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (Besov space on the circle),
* `|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞` (Haar coefficients)

(`Haar.lqNorm_modulus_lt_top_iff_haarCoeff`, `Haar.lqNorm_perModulus_lt_top_iff_haarCoeff`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Haar

open Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lebesgue measure restricted to `[0, 1)` and to `[0, 1]` is the same measure. -/
theorem vol_eq_unitVol : vol = unitVol := Measure.restrict_congr_set Ico_ae_eq_Icc

/-- The identity is measure preserving from `[0, 1)` to `[0, 1]`. -/
theorem measurePreserving_id_vol : MeasurePreserving id vol unitVol := by
  rw [vol_eq_unitVol]
  exact MeasurePreserving.id _

/-- The identity is measure preserving from `[0, 1]` to `[0, 1)`. -/
theorem measurePreserving_id_unitVol : MeasurePreserving id unitVol vol := by
  rw [vol_eq_unitVol]
  exact MeasurePreserving.id _

/-- Almost everywhere on `[0, 1)` is almost everywhere on `[0, 1]`. -/
theorem ae_eq_unitVol_of_vol {F G : ℝ → ℂ} (h : F =ᵐ[vol] G) : F =ᵐ[unitVol] G := by
  rwa [vol_eq_unitVol] at h

/-- Almost everywhere on `[0, 1]` is almost everywhere on `[0, 1)`. -/
theorem ae_eq_vol_of_unitVol {F G : ℝ → ℂ} (h : F =ᵐ[unitVol] G) : F =ᵐ[vol] G := by
  rwa [vol_eq_unitVol]

variable (p) in
/-- The identity of functions as an isometry `L_p[0, 1] → L_p[0, 1)`. -/
noncomputable def toHaar : Lp ℂ p unitVol →L[ℝ] Lp ℂ p vol :=
  (Lp.compMeasurePreservingₗᵢ ℝ id measurePreserving_id_vol).toContinuousLinearMap

variable (p) in
/-- The identity of functions as an isometry `L_p[0, 1) → L_p[0, 1]`. -/
noncomputable def ofHaar : Lp ℂ p vol →L[ℝ] Lp ℂ p unitVol :=
  (Lp.compMeasurePreservingₗᵢ ℝ id measurePreserving_id_unitVol).toContinuousLinearMap

/-- `toHaar` does not change the function. -/
theorem coeFn_toHaar (f : Lp ℂ p unitVol) : toHaar p f =ᵐ[vol] f :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_id_vol

/-- `ofHaar` does not change the function. -/
theorem coeFn_ofHaar (f : Lp ℂ p vol) : ofHaar p f =ᵐ[unitVol] f :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_id_unitVol

/-- `ofHaar` inverts `toHaar`. -/
theorem ofHaar_toHaar (f : Lp ℂ p unitVol) : ofHaar p (toHaar p f) = f := by
  exact Lp.ext ((coeFn_ofHaar _).trans (ae_eq_unitVol_of_vol (coeFn_toHaar f)))

/-- A polynomial of degree `< 1` is constant. -/
theorem polyFun_of_mem_degreeLT_one {P : ℂ[X]} (hP : P ∈ degreeLT ℂ 1) (x : ℝ) :
    polyFun P x = P.coeff 0 := by
  rw [polyFun, eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.1 (mem_degreeLT.1 hP)),
    eval_C, coeff_C_zero]

/-- On `[0, 1)` the dyadic index is the floor of `2^j x`. -/
theorem dyadicIndex_eq_floor {j : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    dyadicIndex j x = (⌊2 ^ j * x⌋₊ : ℤ) :=
  (Int.natCast_floor_eq_floor (mul_nonneg (by positivity) hx.1)).symm

/-- The dyadic index of a left endpoint `n 2^(-j)` is `n`. -/
theorem dyadicIndex_natCast_div (j n : ℕ) : dyadicIndex j ((n : ℝ) / 2 ^ j) = n := by
  rw [dyadicIndex, mul_div_cancel₀ _ (by positivity), Int.floor_natCast]

/-- A piecewise constant function agrees on `[0, 1)` with its step function. -/
theorem ppFun_ae_eq_stepFun {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ 1) (j : ℕ) :
    ppFun j Q =ᵐ[vol] stepFun (ppFun j Q) j := by
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := j) hx
  have hend : ((⌊2 ^ j * x⌋₊ : ℕ) : ℝ) / 2 ^ j ∈ dyadicIco j ⌊2 ^ j * x⌋₊ := by
    rw [mem_dyadicIco, mul_div_cancel₀ _ (by positivity)]
    exact ⟨le_rfl, lt_add_one _⟩
  rw [stepFun, dyadicIndex_eq_floor hx, Int.cast_natCast, ppFun_eq_of_mem Q hlt hmem,
    ppFun_eq_of_mem Q hlt hend, polyFun_of_mem_degreeLT_one (hQ _),
    polyFun_of_mem_degreeLT_one (hQ _)]

/-- A function measurable for the dyadic `σ`-algebra of level `j` is a piecewise constant
function on `[0, 1)`. -/
theorem ae_eq_ppFun_of_stronglyMeasurable {j : ℕ} {g : ℝ → ℂ}
    (hg : StronglyMeasurable[dyadicFiltration j] g) :
    g =ᵐ[vol] ppFun j (fun m => C (g ((m : ℝ) / 2 ^ j))) := by
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := j) hx
  rw [ppFun_eq_of_mem _ hlt hmem, polyFun, eval_C]
  have hg' : StronglyMeasurable[MeasurableSpace.comap (dyadicIndex j) ⊤] g := hg
  refine (hg'.eq_of_comap_top ?_).symm
  rw [dyadicIndex_natCast_div, dyadicIndex_eq_floor hx]

/-- `toHaar` maps the piecewise constant approximants into the Haar approximants. -/
theorem toHaar_mem_scheme {n : ℕ} {a : Lp ℂ p unitVol} (ha : a ∈ ppScheme p 1 n) :
    toHaar p a ∈ scheme p n := by
  show toHaar p a ∈ dyadicFiltration.approximants p vol n
  unfold Filtration.approximants
  split_ifs with hn
  · subst hn
    rw [Submodule.mem_bot, mem_ppScheme_zero.1 ha, map_zero]
  · obtain ⟨Q, hQ, hae⟩ := (mem_ppScheme hn).1 ha
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact ⟨stepFun (ppFun (Nat.log 2 n) Q) (Nat.log 2 n), stronglyMeasurable_stepFun _ _,
      (coeFn_toHaar a).trans ((ae_eq_vol_of_unitVol hae).trans (ppFun_ae_eq_stepFun hQ _))⟩

/-- `ofHaar` maps the Haar approximants into the piecewise constant approximants. -/
theorem ofHaar_mem_ppScheme {n : ℕ} {a : Lp ℂ p vol} (ha : a ∈ scheme p n) :
    ofHaar p a ∈ ppScheme p 1 n := by
  change a ∈ dyadicFiltration.approximants p vol n at ha
  unfold Filtration.approximants at ha
  split_ifs at ha with hn
  · subst hn
    rw [Submodule.mem_bot] at ha
    rw [mem_ppScheme_zero, ha, map_zero]
  · rw [mem_ppScheme hn]
    rw [mem_lpMeas_iff_aestronglyMeasurable] at ha
    obtain ⟨g, hg, hag⟩ := ha
    refine ⟨fun m => C (g ((m : ℝ) / 2 ^ Nat.log 2 n)), fun m =>
      mem_degreeLT.2 (degree_C_le.trans_lt (by norm_num)), ?_⟩
    exact (coeFn_ofHaar a).trans
      (ae_eq_unitVol_of_vol (hag.trans (ae_eq_ppFun_of_stronglyMeasurable hg)))

/-- **The Haar scheme is the piecewise constant scheme**: `f ∈ A^s_q` for the piecewise
constants in `L_p[0, 1]` iff `f ∈ A^s_q` for the Haar scheme in `L_p[0, 1)`. -/
theorem memApprox_ppScheme_one_iff {s : ℝ} {q : ℝ≥0∞} (f : Lp ℂ p unitVol) :
    (ppScheme p 1).MemApprox s q f ↔ (scheme p).MemApprox s q (toHaar p f) := by
  constructor
  · exact ApproximationScheme.MemApprox.map (toHaar p) fun _ _ ha => toHaar_mem_scheme ha
  · intro h
    have h' := ApproximationScheme.MemApprox.map (ofHaar p)
      (fun _ _ ha => ofHaar_mem_ppScheme ha) h
    rwa [ofHaar_toHaar] at h'

/-- `toHaar` does not change Haar coefficients. -/
theorem haarCoeff_toHaar (f : Lp ℂ p unitVol) (k : ℕ) (m : ℤ) :
    haarCoeff (toHaar p f) k m = haarCoeff f k m :=
  integral_congr_ae ((coeFn_toHaar f).mono fun x hx => by simp only [hx])

/-- `toHaar` does not change the integral. -/
theorem integral_toHaar (f : Lp ℂ p unitVol) : ∫ x, toHaar p f x ∂vol = ∫ x, f x ∂vol :=
  integral_congr_ae (coeFn_toHaar f)

/-- **Besov spaces on the interval through Haar coefficients.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < 1/p`, the Besov quasi-norm `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}` of
`f ∈ L_p[0, 1]` is finite iff
`|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`. -/
theorem lqNorm_modulus_lt_top_iff_haarCoeff (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 f k) < ∞ ↔
      ‖∫ x, f x ∂vol‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
          ENNReal.lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)) < ∞ := by
  rw [← memApprox_ppScheme_iff le_rfl hp hq hs.le hsp f, memApprox_ppScheme_one_iff,
    memApprox_iff_haarCoeff hp hs hq, integral_toHaar]
  simp only [haarCoeff_toHaar]

/-- **Besov spaces on the circle through Haar coefficients.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < 1/p`, the periodic Besov quasi-norm `‖f‖_p + ‖(2^(ks) ω_1^per(f, 2^(-k))_p)_k‖_{ℓ_q}`
of `f ∈ L_p(𝕋) = L_p[0, 1]` is finite iff
`|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`. -/
theorem lqNorm_perModulus_lt_top_iff_haarCoeff (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p 1 f k) < ∞ ↔
      ‖∫ x, f x ∂vol‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k *
          ENNReal.lqNorm p (fun m : Fin (2 ^ k) => ‖haarCoeff f k ((m : ℕ) : ℤ)‖ₑ)) < ∞ := by
  rw [← memApprox_ppScheme_iff_per le_rfl hp hq hs.le hsp f, memApprox_ppScheme_one_iff,
    memApprox_iff_haarCoeff hp hs hq, integral_toHaar]
  simp only [haarCoeff_toHaar]

end Haar
