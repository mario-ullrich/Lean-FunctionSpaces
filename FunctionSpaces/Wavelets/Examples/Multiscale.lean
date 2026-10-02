/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.HaarBesov
public import FunctionSpaces.Interval.LocalProjection

/-!
# Multiscale decompositions by local polynomial projections

Let `P_k` be the projection of `L_p[0, 1]` onto the piecewise polynomials of degree `< r` on the
dyadic intervals of level `k`, the local `L_2`-orthogonal projection on every interval
(`Interval.ppProj`). These projections are uniformly bounded in `L_p`, so they form a projection
scheme (`Interval.ppProjectionScheme`), and the abstract block characterisation gives, for
`1 ≤ p < ∞`, `r ≥ 1`, `s > 0` and `1 ≤ q ≤ ∞`,
`f ∈ A^s_q ↔ ‖P_0 f‖_p + ‖(2^(ks) ‖P_{k+1} f - P_k f‖_p)_k‖_{ℓ_q} < ∞`
(`Interval.memApprox_ppScheme_iff_block`). The density of the piecewise polynomials needed
there comes from the Haar system (`Interval.closure_iUnion_ppScheme`).

The detail `P_{k+1} f - P_k f` is the part of `f` that multiwavelets of degree `< r` expand at
level `k`. With the characterisations through moduli of smoothness, for `0 < s < 1/p` the
Besov spaces `B^s_{p,q}[0, 1]` and `B^s_{p,q}(𝕋)` are described by these details
(`Interval.lqNorm_modulus_lt_top_iff_block`, `Interval.lqNorm_perModulus_lt_top_iff_block`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The approximants of the piecewise polynomial scheme increase with the degree. -/
theorem ppScheme_mono_degree {r r' : ℕ} (hrr' : r ≤ r') (n : ℕ) :
    ppScheme p r n ⊆ ppScheme p r' n := by
  intro a ha
  rcases eq_or_ne n 0 with rfl | hn
  · exact mem_ppScheme_zero.2 (mem_ppScheme_zero.1 ha)
  · obtain ⟨Q, hQ, hae⟩ := (mem_ppScheme hn).1 ha
    exact (mem_ppScheme hn).2 ⟨Q, fun m => degreeLT_mono hrr' (hQ m), hae⟩

/-- **The piecewise polynomials are dense** in `L_p[0, 1]` for `1 ≤ p < ∞` and `r ≥ 1`: they
contain the step functions of the Haar system. -/
theorem closure_iUnion_ppScheme (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) :
    closure (⋃ n, ppScheme p r n) = univ := by
  have hd : Dense (⋃ n, Haar.scheme p n) := dense_iff_closure_eq.2 (Haar.closure_iUnion_scheme hp)
  have hsurj : Function.Surjective (Haar.ofHaar p) := fun f => ⟨Haar.toHaar p f, Haar.ofHaar_toHaar f⟩
  have himg : Dense (Haar.ofHaar p '' ⋃ n, Haar.scheme p n) :=
    hsurj.denseRange.dense_image (Haar.ofHaar p).continuous hd
  refine dense_iff_closure_eq.1 (himg.mono ?_)
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨n, hn⟩ := mem_iUnion.1 ha
  exact mem_iUnion.2 ⟨n, ppScheme_mono_degree hr n (Haar.ofHaar_mem_ppScheme hn)⟩

/-- **Approximation by piecewise polynomials through multiscale details**: for `1 ≤ p < ∞`,
`r ≥ 1`, `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff
`‖P_0 f‖_p + ‖(2^(ks) ‖P_{k+1} f - P_k f‖_p)_k‖_{ℓ_q} < ∞`, with `P_k` the local projections
onto the piecewise polynomials of level `k`. -/
theorem memApprox_ppScheme_iff_block (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    (ppScheme p r).MemApprox s q f ↔ ‖ppProj p hp r 0 f‖ₑ + ENNReal.lqNorm q (fun k =>
      dyadicWeight s k * ‖ppProj p hp r (k + 1) f - ppProj p hp r k f‖ₑ) < ∞ := by
  rw [(ppProjectionScheme hp r).memApprox_iff_blockNorm_lt_top (closure_iUnion_ppScheme hp hr) hs
    hq]
  have h1 : (ppProjectionScheme hp r).P 1 = ppProj p hp r 0 := by
    simpa using ppProjectionScheme_two_pow hp r 0
  simp only [ApproximationScheme.ProjectionScheme.blockNorm,
    ApproximationScheme.ProjectionScheme.block, ppProjectionScheme_two_pow, h1]

/-- **Besov spaces on the interval through multiscale details**: for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`r ≥ 1` and `0 < s < 1/p`, the Besov quasi-norm `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}`
is finite iff `‖P_0 f‖_p + ‖(2^(ks) ‖P_{k+1} f - P_k f‖_p)_k‖_{ℓ_q} < ∞`. -/
theorem lqNorm_modulus_lt_top_iff_block (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ ↔
      ‖ppProj p hp r 0 f‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight s k * ‖ppProj p hp r (k + 1) f - ppProj p hp r k f‖ₑ) < ∞ := by
  rw [← memApprox_ppScheme_iff hr hp hq hs.le hsp f, memApprox_ppScheme_iff_block hp hr hs hq]

/-- **Besov spaces on the circle through multiscale details**: for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`r ≥ 1` and `0 < s < 1/p`, the periodic Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q}` is finite iff
`‖P_0 f‖_p + ‖(2^(ks) ‖P_{k+1} f - P_k f‖_p)_k‖_{ℓ_q} < ∞`. -/
theorem lqNorm_perModulus_lt_top_iff_block (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ}
    (hs : 0 < s) (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p r f k) < ∞ ↔
      ‖ppProj p hp r 0 f‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight s k * ‖ppProj p hp r (k + 1) f - ppProj p hp r k f‖ₑ) < ∞ := by
  rw [← memApprox_ppScheme_iff_per hr hp hq hs.le hsp f, memApprox_ppScheme_iff_block hp hr hs hq]

end Interval
