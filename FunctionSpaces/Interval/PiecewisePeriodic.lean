/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.PiecewiseInverse
public import FunctionSpaces.Interval.Periodic

/-!
# Piecewise polynomials on the circle

On the circle `𝕋 = ℝ/ℤ`, identified with `[0, 1)` through the periodic extension
`f̃(x) = f(x - ⌊x⌋)`, the dyadic piecewise polynomials are the same functions as on `[0, 1)`,
so their scheme is `Interval.ppScheme` in `L_p[0, 1] = L_p(𝕋)`. Only the modulus changes: the
periodic modulus `ω_r^per(f, t)_p` of `FunctionSpaces.Interval.Periodic` also sees the knot
`0 = 1` of the circle.

* **Jackson's inequality** `E_{2^k}(f)_p ≤ C ω_r^per(f, 2^(-k))_p` follows from the one on
  `[0, 1]`, since the periodic modulus is the larger one (`Interval.approxSeq_ppScheme_le_per`).
* **The inverse inequality** `ω_r^per(a, 2^(-k))_p ≤ C_B 2^(-(k-j)/p) ‖a‖_p` for `a ∈ V_j`
  (`Interval.exists_inverse_ppScheme_per`) is the local inverse estimate for the periodic
  extension, which is a piecewise polynomial on `[0, ∞)` (`Interval.isPiecewisePoly_perExt_ppFun`)
  whose `2^j` consecutive pieces always make up one period
  (`Interval.sum_localMass_perExt_le`).

Hence for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < 1/p`,
`f ∈ A^s_q ↔ ‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
(`Interval.memApprox_ppScheme_iff_per`): the approximation space is the Besov space
`B^s_{p,q}(𝕋)` for `0 < s < 1/p`. Comparing with `Interval.memApprox_ppScheme_iff`, the Besov
spaces `B^s_{p,q}[0, 1]` and `B^s_{p,q}(𝕋)` contain the same functions for `0 < s < 1/p`
(`Interval.lqNorm_modulus_lt_top_iff_perModulus`): below smoothness `1/p` a jump between the
ends of the interval does not count.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The periodic extension of a piecewise polynomial** of level `k` is a piecewise polynomial
of level `k` on `[0, ∞)`: on `I_{k,m}` with `m = m' + 2^k c`, `m' < 2^k`, it is `Q_{m'}` shifted
by `c`. -/
theorem isPiecewisePoly_perExt_ppFun {r : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r)
    (k : ℕ) : IsPiecewisePoly r k (perExt (ppFun k Q)) := by
  intro m
  obtain ⟨c, m', hm', hdecomp⟩ : ∃ c m' : ℕ, m' < 2 ^ k ∧ m = m' + 2 ^ k * c :=
    ⟨m / 2 ^ k, m % 2 ^ k, Nat.mod_lt _ (by positivity), (Nat.mod_add_div m (2 ^ k)).symm⟩
  refine ⟨(Q m').comp (C ((-(c : ℝ) : ℝ) : ℂ) + C ((1 : ℝ) : ℂ) * X),
    comp_affine_mem_degreeLT (hQ m') _ _, fun x hx => ?_⟩
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hdiv : (m : ℝ) = m' + 2 ^ k * c := by rw [hdecomp]; push_cast; ring
  have hm'R : (m' : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hm'
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
  rw [mem_dyadicIco] at hx
  have hfl : ⌊x⌋ = (c : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · nlinarith
    · nlinarith
  have hfract : Int.fract x = x - c := by
    rw [← Int.self_sub_floor, hfl]
    push_cast
    ring
  have hmem : x - c ∈ dyadicIco k m' := by
    rw [mem_dyadicIco]
    constructor <;> nlinarith
  rw [perExt, hfract, ppFun_eq_of_mem Q hm' hmem, polyFun_comp_affine]
  congr 1
  ring

/-- **The local masses of a periodic extension**: `2^k` consecutive pieces of the periodic
extension `ũ` make up one period, so `∑_{n < 2^k} ∫_{I_{k,n+l}} |ũ|^p ≤ ‖u‖_p^p`. -/
theorem sum_localMass_perExt_le {u : ℝ → ℂ} (hu : Measurable u) (hp : p ≠ ∞) (k l : ℕ) :
    ∑ n ∈ Finset.range (2 ^ k), localMass p k (perExt u) (n + l) ≤
      eLpNorm u p unitVol ^ p.toReal := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hsum := sum_le_lintegral_Icc (G := fun x => ‖perExt u x‖ₑ ^ p.toReal) ((l : ℝ) / 2 ^ k)
    (by positivity : (0 : ℝ) ≤ 1 / 2 ^ k) (2 ^ k)
  have h1 : (l : ℝ) / 2 ^ k + ((2 ^ k : ℕ) : ℝ) * (1 / 2 ^ k) = l / 2 ^ k + 1 := by
    push_cast
    field_simp
  rw [h1, lintegral_Icc_periodic (G := fun x => ‖perExt u x‖ₑ ^ p.toReal)
    (fun x => by simp only [perExt_periodic u x])] at hsum
  have hpieces : ∀ n : ℕ, localMass p k (perExt u) (n + l) =
      ∫⁻ x in Icc ((l : ℝ) / 2 ^ k + n * (1 / 2 ^ k)) ((l : ℝ) / 2 ^ k + (n + 1) * (1 / 2 ^ k)),
        ‖perExt u x‖ₑ ^ p.toReal := fun n => by
    rw [localMass, ← setLIntegral_congr Ico_ae_eq_Icc, dyadicIco]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun n _ => hpieces n]
  refine hsum.trans (le_of_eq ?_)
  rw [eLpNorm_rpow_eq hu.aestronglyMeasurable hp0 hp, ← setLIntegral_congr Ico_ae_eq_Icc]
  rw [show (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂unitVol) = ∫⁻ x in Icc (0 : ℝ) 1, ‖u x‖ₑ ^ p.toReal from rfl,
    ← setLIntegral_congr Ico_ae_eq_Icc]
  exact setLIntegral_congr_fun measurableSet_Ico fun x hx => by rw [perExt_of_mem u hx]

/-- **Bounded overlap on the circle**: `∑_{n < 2^k} ∑_{l ≤ r} ∫_{I_{k,n+l}} |ũ|^p ≤ (r + 1) ‖u‖_p^p`
for the periodic extension `ũ`. -/
theorem sum_sum_localMass_perExt_le {u : ℝ → ℂ} (hu : Measurable u) (hp : p ≠ ∞) (k r : ℕ) :
    ∑ n ∈ Finset.range (2 ^ k), ∑ l ∈ Finset.range (r + 1), localMass p k (perExt u) (n + l) ≤
      (r + 1) * eLpNorm u p unitVol ^ p.toReal := by
  rw [Finset.sum_comm]
  calc ∑ l ∈ Finset.range (r + 1), ∑ n ∈ Finset.range (2 ^ k), localMass p k (perExt u) (n + l)
      ≤ ∑ _l ∈ Finset.range (r + 1), eLpNorm u p unitVol ^ p.toReal :=
        Finset.sum_le_sum fun l _ => sum_localMass_perExt_le hu hp k l
    _ = (r + 1) * eLpNorm u p unitVol ^ p.toReal := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

variable (p) in
/-- The periodic modulus of an element of `L_p[0, 1] = L_p(𝕋)` at the dyadic scale `2^(-k)`,
`ω_r^per(f, 2^(-k))_p`. -/
noncomputable def lpPerModulus (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) : ℝ≥0∞ :=
  perModulus r p (f : ℝ → ℂ) (1 / 2 ^ k)

/-- The periodic modulus of elements of `L_p[0, 1]` is subadditive. -/
theorem lpPerModulus_add_le (r : ℕ) (f g : Lp ℂ p unitVol) (k : ℕ) :
    lpPerModulus p r (f + g) k ≤ lpPerModulus p r f k + lpPerModulus p r g k := by
  rw [lpPerModulus, perModulus_congr_ae (Lp.coeFn_add f g)]
  exact perModulus_add_le Fact.out r _ _ _

/-- `ω_r^per(f, t)_p ≤ 2^r ‖f‖_p` in `L_p[0, 1]`. -/
theorem lpPerModulus_le (hp : p ≠ ∞) (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) :
    lpPerModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.enorm_def]
  exact perModulus_le (Lp.stronglyMeasurable f).measurable Fact.out hp r _

omit [Fact (1 ≤ p)] in
/-- The modulus on `[0, 1]` is at most the periodic modulus. -/
theorem lpModulus_le_lpPerModulus (r : ℕ) (f : Lp ℂ p unitVol) (k : ℕ) :
    lpModulus p r f k ≤ lpPerModulus p r f k :=
  modulus_le_perModulus r p _ _

/-- **Jackson's inequality on the circle**: for `1 ≤ p < ∞`, `r ≥ 1` and `k ≥ 1`,
`E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r^per(f, 2^(-k))_p`. -/
theorem approxSeq_ppScheme_le_per {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) (f : Lp ℂ p unitVol)
    {k : ℕ} (hk : 1 ≤ k) :
    (ppScheme p r).approxSeq f (2 ^ k) ≤ 2 * jacksonConst r * lpPerModulus p r f k :=
  (approxSeq_ppScheme_le hr hp f hk).trans (mul_le_mul' le_rfl (lpModulus_le_lpPerModulus r f k))

/-- **The inverse inequality on the circle**, of order `1/p`: there is `C_B < ∞` with
`ω_r^per(a, 2^(-k))_p ≤ C_B 2^(-(k-j)/p) ‖a‖_p` for every piecewise polynomial `a` of level `j`
(and `k - j` truncated at `0`). -/
theorem exists_inverse_ppScheme_per {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ ppScheme p r (2 ^ j),
      lpPerModulus p r a k ≤ CB * dyadicWeight (-(1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  refine ⟨ppInverseConst p r K, ppInverseConst_ne_top r hK, fun j k a ha => ?_⟩
  obtain ⟨Q, hQ, hae⟩ := mem_ppScheme_two_pow.1 ha
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpPerModulus_le hp r a k).trans (by gcongr; exact two_pow_le_ppInverseConst r K)
  · have hnorm : ‖a‖ₑ = eLpNorm (ppFun j Q) p unitVol := by
      rw [Lp.enorm_def]
      exact eLpNorm_congr_ae hae
    rw [lpPerModulus, perModulus_congr_ae hae, hnorm]
    refine iSup₂_le fun h hh => ?_
    have hhj : h ≤ 1 / 2 ^ j := hh.2.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hjk))
    exact (eLpNorm_iterDiff_le_of_isPiecewisePoly (isPiecewisePoly_perExt_ppFun hQ j)
      (measurable_perExt (measurable_ppFun j Q)) hKb hp hh.1 hhj
      (sum_sum_localMass_perExt_le (measurable_ppFun j Q) hp j r)).trans
      (le_ppInverseConst_mul hjk K hh.2 _)

/-- The periodic modulus `ω_r^per(f, 2^(-k))_p` is compatible with the scheme of dyadic piecewise
polynomials of degree `< r`, with inverse order `θ = 1/p`. -/
noncomputable def ppPerModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (ppScheme p r) (1 / p.toReal) where
  modulus := lpPerModulus p r
  add_le := lpPerModulus_add_le r
  C0 := 2 ^ r
  C0_ne_top := by simp
  le_enorm := lpPerModulus_le hp r
  jacksonStart := 1
  CJ := 2 * jacksonConst r
  CJ_ne_top := ENNReal.mul_ne_top (by norm_num) (jacksonConst_ne_top r)
  jackson f _ hk := approxSeq_ppScheme_le_per hr hp f hk
  CB := (exists_inverse_ppScheme_per (r := r) hp).choose
  CB_ne_top := (exists_inverse_ppScheme_per hp).choose_spec.1
  inverse := (exists_inverse_ppScheme_per hp).choose_spec.2

/-- **Approximation by piecewise polynomials on the circle.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`r ≥ 1` and `0 ≤ s < 1/p`, an `f ∈ L_p(𝕋) = L_p[0, 1]` lies in the approximation space `A^s_q`
of the dyadic piecewise polynomials of degree `< r` iff its periodic Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q}` is finite. -/
theorem memApprox_ppScheme_iff_per {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p unitVol) :
    (ppScheme p r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p r f k) < ∞ :=
  (ppPerModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs hsp f

/-- **Besov spaces on the interval and on the circle agree below smoothness `1/p`**: for
`1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < 1/p`, the Besov quasi-norm of `f ∈ L_p[0, 1]`
defined by the modulus on `[0, 1]` is finite iff the one defined by the periodic modulus is.
Both conditions describe the same approximation space. -/
theorem lqNorm_modulus_lt_top_iff_perModulus {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p r f k) < ∞ :=
  (memApprox_ppScheme_iff hr hp hq hs hsp f).symm.trans
    (memApprox_ppScheme_iff_per hr hp hq hs hsp f)

end Interval
