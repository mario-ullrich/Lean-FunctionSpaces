/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.Besov.Basic
public import ApproximationSpaces.Decompositions.EFunctionalBlocks

/-!
# Block decompositions of Besov spaces, `0 < p ≤ ∞`

Let `μ` be a finite measure on `Ω`, `S` a scheme of functions on `(Ω, μ)` (an approximation
scheme of essentially bounded functions), `0 < p ≤ ∞`, `ρ = min(1, p)`, `s > 0` and
`0 < q ≤ ∞`. A function `f ∈ L_p(μ)` lies in the Besov space `B^s_{p,q}` if and only if
`f = ∑_k g_k` almost everywhere with approximants `g_k ∈ S_{2^k}` and
`(2^(ks) ‖g_k‖_p)_k ∈ ℓ_q` (`FunctionScheme.memBesov_iff_exists_blocks`), with equivalent
quasi-norms (DeVore–Popov, Trans. Amer. Math. Soc. 305 (1988), Theorem 5.1 and Corollary 5.3,
for dyadic splines). This is the block decomposition of the E-spaces of a `ρ`-normed couple
(`InterpCouple.eNormDyadic_lt_top_iff_eBlockDecompNorm_lt_top`) for the couple of `S` in `L_p`,
with the convergence of the partial sums in `L_p` replaced by convergence almost everywhere.

* **Series of essentially bounded functions.** The partial sums of every series `∑_k g_k` of
  essentially bounded functions with almost everywhere sum `f` and
  `‖(2^(ks) ‖g_k‖_p)_k‖_{ℓ_q} < ∞` converge to `f` in `L_p` and in measure
  (`FunctionScheme.tendsto_eLpNorm_sub_sum_of_blocks`): the weighted `ℓ_q` bound gives
  `∑_k ‖g_k‖_p^ρ < ∞` (`ENNReal.tsum_rpow_ne_top_of_lqNorm_dyadicWeight_ne_top`), and the series
  lemmas of `FunctionSpaces.Analysis.Lp.QuasiNorm` apply
  (`MeasureTheory.tendsto_eLpNorm_sub_sum_of_ae_hasSum`).
* **The two bounds.** For `g_k ∈ S_{2^k}` with almost everywhere sum `f`,
  `‖f‖^dy_{s,q} ≤ 2 H^(1/ρ) ‖(2^(ks) ‖g_k‖_p)_k‖_{ℓ_q}` with Hardy's constant
  `H = hardyConst (sρ) (q/ρ)` (`FunctionScheme.eNormDyadic_le_of_blocks`); conversely, the
  blocks `g_0 = 0`, `g_1 = b_0`, `g_{k+2} = b_{k+1} - b_k` of near-best approximants
  `b_k ∈ S_{2^k}` (`InterpCouple.nearBestBlocks`, `ApproximationScheme.nearBestBlocks_mem`) have
  the almost everywhere sum `f` and size at most `eBlockConst ρ s q ‖f‖^dy_{s,q}`
  (`FunctionScheme.exists_blocks_of_memBesov`). Here `‖f‖^dy_{s,q}` is the dyadic norm of the
  couple of `S` in `L_p`, finite exactly on `B^s_{p,q}`
  (`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`).

The blocks are essentially bounded functions, so they lie in every `L_r` and are the
approximants themselves; Haar and wavelet expansions with `p < 1` expand them further.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight hardyConst)

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : ApproximationScheme X}

/-- **The blocks of dyadic approximants are approximants of their level**: if `b_k ∈ A_{2^k}`
for every `k`, then the blocks `g_0 = 0`, `g_1 = b_0` and `g_{k+2} = b_{k+1} - b_k` of `b`
(`InterpCouple.nearBestBlocks`) satisfy `g_k ∈ A_{2^k}` for every `k`, since
`b_{k+1} - b_k ∈ A_{2^(k+2)}` (`ApproximationScheme.sub_mem_pow_add_two`). -/
theorem nearBestBlocks_mem {b : ℕ → X} (hb : ∀ k, b k ∈ A (2 ^ k)) (k : ℕ) :
    InterpCouple.nearBestBlocks b k ∈ A (2 ^ k) := by
  rcases k with _ | _ | k
  · exact A.zero_mem _
  · exact A.mem_of_le (by norm_num) (hb 0)
  · exact sub_mem_pow_add_two (hb (k + 1)) (hb k)

end ApproximationScheme

namespace FunctionScheme

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞} {s : ℝ} {q : ℝ≥0∞}

/-- **Series of essentially bounded functions of finite size converge in `L_p` and in
measure**: let `0 < p ≤ ∞`, `s > 0`, `0 < q ≤ ∞`, `f ∈ L_p(μ)` and `g_k ∈ L_∞(μ)` with
`∑_k g_k(x) = f(x)` for almost every `x` and `‖(2^(ks) ‖g_k‖_p)_k‖_{ℓ_q} < ∞`. Then
`‖f - ∑_{k<n} g_k‖_p → 0` and `∑_{k<n} g_k → f` in measure. With `ρ = min(1, p)`, the weighted
`ℓ_q` bound gives `∑_k ‖g_k‖_p^ρ < ∞` (`ENNReal.tsum_rpow_ne_top_of_lqNorm_dyadicWeight_ne_top`),
the partial sums converge in `L_p` (`MeasureTheory.tendsto_eLpNorm_sub_sum_of_ae_hasSum`), and
convergence in `L_p` implies convergence in measure (Mathlib's
`tendstoInMeasure_of_tendsto_eLpNorm`). The statement holds on every measure space. -/
theorem tendsto_eLpNorm_sub_sum_of_blocks (hp0 : p ≠ 0) (hs : 0 < s) (hq : q ≠ 0)
    {f : Lp ℂ p μ} {g : ℕ → Lp ℂ ∞ μ} (hfg : ∀ᵐ x ∂μ, HasSum (fun k => g k x) (f x))
    (hL : lqNorm q (fun k => dyadicWeight s k * eLpNorm (g k) p μ) ≠ ∞) :
    Tendsto (fun n => eLpNorm (⇑f - ∑ k ∈ Finset.range n, ⇑(g k)) p μ) atTop (𝓝 0) ∧
      TendstoInMeasure μ (fun n => ∑ k ∈ Finset.range n, ⇑(g k)) atTop f := by
  have hsum : ∑' k, eLpNorm (g k) p μ ^ (min 1 p).toReal ≠ ∞ :=
    ENNReal.tsum_rpow_ne_top_of_lqNorm_dyadicWeight_ne_top hq hs
      (ENNReal.toReal_min_one_pos hp0) hL
  have hlim := tendsto_eLpNorm_sub_sum_of_ae_hasSum hp0 hfg hsum
  exact ⟨hlim, tendstoInMeasure_of_tendsto_eLpNorm hp0
    (hlim.congr fun n => eLpNorm_sub_comm _ _ _ _)⟩

variable [IsFiniteMeasure μ] {S : FunctionScheme μ}

/-- **Essentially bounded functions in the couple of `S` in `L_p`**: for `a ∈ L_∞(μ)`, the
quasi-norm `N₀ = ‖·‖_p` of the couple of `S` in `L_p` gives `N₀(ι_{∞,p} a) = ‖a‖_p`, since the
inclusion `ι_{∞,p}` keeps the function almost everywhere
(`MeasureTheory.Lp.eLpNorm_inclusionOfExponentLeLinear`). -/
theorem lpCouple_norm0_topInclusion (a : Lp ℂ ∞ μ) :
    (S.lpCouple p).norm0 (Lp.topInclusion (𝕜 := ℝ) μ p a) = eLpNorm a p μ := by
  rw [lpCouple_norm0]
  exact Lp.eLpNorm_inclusionOfExponentLeLinear le_top a p

/-- **Partial sums of essentially bounded functions in the couple of `S` in `L_p`**: for
`f ∈ L_p(μ)` and `g_k ∈ L_∞(μ)`, the quasi-norm `N₀ = ‖·‖_p` of the couple of `S` in `L_p` gives
`N₀(f - ∑_{k<n} ι_{∞,p} g_k) = ‖f - ∑_{k<n} g_k‖_p`, since the inclusion `ι_{∞,p}` is linear and
keeps the functions almost everywhere (`MeasureTheory.Lp.eLpNorm_sub_topInclusion`). -/
theorem lpCouple_norm0_sub_sum_topInclusion (f : Lp ℂ p μ) (g : ℕ → Lp ℂ ∞ μ) (n : ℕ) :
    (S.lpCouple p).norm0 (f - ∑ k ∈ Finset.range n, Lp.topInclusion (𝕜 := ℝ) μ p (g k)) =
      eLpNorm (⇑f - ∑ k ∈ Finset.range n, ⇑(g k)) p μ := by
  rw [lpCouple_norm0, ← map_sum (Lp.topInclusion (𝕜 := ℝ) μ p), Lp.eLpNorm_sub_topInclusion]
  exact eLpNorm_congr_ae ((EventuallyEq.refl _ _).sub (Lp.coeFn_finsetSum _ _))

/-- **A block decomposition bounds the dyadic norm**: let `0 < p ≤ ∞`, `ρ = min(1, p)`, `s > 0`
and `0 < q ≤ ∞`. If `g_k ∈ S_{2^k}` and `∑_k g_k(x) = f(x)` for almost every `x`, then
`‖f‖^dy_{s,q} ≤ 2 H^(1/ρ) ‖(2^(ks) ‖g_k‖_p)_k‖_{ℓ_q}` for the dyadic norm of the couple of `S` in
`L_p`, with Hardy's constant `H = hardyConst (sρ) (q/ρ)`. If the right side is finite, the
partial sums converge to `f` in `L_p` (`FunctionScheme.tendsto_eLpNorm_sub_sum_of_blocks`), so
the classes `ι_{∞,p} g_k` form a block decomposition of `f` in the couple, and
`InterpCouple.eNormDyadic_le_of_tendsto_sum` applies. -/
theorem eNormDyadic_le_of_blocks (hp0 : p ≠ 0) (hs : 0 < s) (hq : q ≠ 0) {f : Lp ℂ p μ}
    {g : ℕ → Lp ℂ ∞ μ} (hg : ∀ k, g k ∈ S (2 ^ k))
    (hfg : ∀ᵐ x ∂μ, HasSum (fun k => g k x) (f x)) :
    (S.lpCouple p).eNormDyadic s q f ≤
      2 * hardyConst (s * (min 1 p).toReal) (q / ENNReal.ofReal (min 1 p).toReal) ^
        (1 / (min 1 p).toReal) * lqNorm q (fun k => dyadicWeight s k * eLpNorm (g k) p μ) := by
  have hρ : 0 < (min 1 p).toReal := ENNReal.toReal_min_one_pos hp0
  rcases eq_or_ne (lqNorm q (fun k => dyadicWeight s k * eLpNorm (g k) p μ)) ∞ with hL | hL
  · have hH : hardyConst (s * (min 1 p).toReal) (q / ENNReal.ofReal (min 1 p).toReal) ^
        (1 / (min 1 p).toReal) ≠ 0 :=
      (ENNReal.rpow_pos (zero_lt_one.trans_le (ENNReal.one_le_hardyConst _ _))
        (ENNReal.hardyConst_ne_top (mul_pos hs hρ) _)).ne'
    rw [hL, ENNReal.mul_top (mul_ne_zero two_ne_zero hH)]
    exact le_top
  have hlim := (tendsto_eLpNorm_sub_sum_of_blocks hp0 hs hq hfg hL).1
  have h := InterpCouple.eNormDyadic_le_of_tendsto_sum (isQuasiNormed_lpCouple S p)
    lpCouple_norm1_add_le hρ (lpCouple_norm0_add_rpow_min_le hp0) hq (s := s) (u := f)
    (g := fun k => Lp.topInclusion (𝕜 := ℝ) μ p (g k))
    (fun k => lpCouple_norm1_le_of_mem (topInclusion_mem_lpSets (hg k)))
    (by simpa only [lpCouple_norm0_sub_sum_topInclusion] using hlim)
  simpa only [lpCouple_norm0_topInclusion] using h

/-- **Besov functions have block decompositions converging almost everywhere**: let
`0 < p ≤ ∞`, `ρ = min(1, p)`, `s > 0` and `0 < q ≤ ∞`. Every `f ∈ B^s_{p,q}` is
`f = ∑_k g_k` almost everywhere with `g_k ∈ S_{2^k}`, the partial sums converge to `f` in `L_p`
and in measure, and `‖(2^(ks) ‖g_k‖_p)_k‖_{ℓ_q} ≤ eBlockConst ρ s q ‖f‖^dy_{s,q}`. The near-best
approximants `b_k` of the couple of `S` in `L_p` with their tolerances
(`InterpCouple.exists_nearBest_tolerances`) are classes `b_k = ι_{∞,p} a_k` of
`a_k ∈ S_{2^k}`. Let `g_k` be the blocks of `(a_k)` (`InterpCouple.nearBestBlocks`). The blocks
of `(b_k)` are the classes `ι_{∞,p} g_k` (`InterpCouple.nearBestBlocks_map`), which
`InterpCouple.lqNorm_nearBestBlocks_le` bounds. Their partial sums of index `k + 2` are the
`b_k`, which converge to `f` in `L_p`, and `MeasureTheory.ae_hasSum_of_tendsto_eLpNorm` gives the
almost everywhere sum. -/
theorem exists_blocks_of_memBesov (hp0 : p ≠ 0) (hs : 0 < s) (hq : q ≠ 0) {f : Lp ℂ p μ}
    (hf : S.MemBesov p s q f) :
    ∃ g : ℕ → Lp ℂ ∞ μ, (∀ k, g k ∈ S (2 ^ k)) ∧ (∀ᵐ x ∂μ, HasSum (fun k => g k x) (f x)) ∧
      Tendsto (fun n => eLpNorm (⇑f - ∑ k ∈ Finset.range n, ⇑(g k)) p μ) atTop (𝓝 0) ∧
      TendstoInMeasure μ (fun n => ∑ k ∈ Finset.range n, ⇑(g k)) atTop f ∧
      lqNorm q (fun k => dyadicWeight s k * eLpNorm (g k) p μ) ≤
        InterpCouple.eBlockConst (min 1 p).toReal s q * (S.lpCouple p).eNormDyadic s q f := by
  have hρ : 0 < (min 1 p).toReal := ENNReal.toReal_min_one_pos hp0
  have hu : (S.lpCouple p).eNormDyadic s q f ≠ ∞ :=
    ((memBesov_iff_eNormDyadic_lt_top hq hs.le).1 hf).ne
  obtain ⟨b, e, hb1, hbe, he, he0, hLq⟩ :=
    InterpCouple.exists_nearBest_tolerances (lpCouple_norm1_zero S p) f s (by linarith)
  choose a ha hab using fun k => mem_lpSets.1 (mem_lpSets_of_lpCouple_norm1_le (hb1 k))
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Lp ℂ ∞ μ, g = InterpCouple.nearBestBlocks a := ⟨_, rfl⟩
  have hgb : ∀ k, InterpCouple.nearBestBlocks b k = Lp.topInclusion (𝕜 := ℝ) μ p (g k) :=
    fun k => by
      rw [show b = fun j => Lp.topInclusion (𝕜 := ℝ) μ p (a j) from funext fun j => (hab j).symm,
        hg]
      exact InterpCouple.nearBestBlocks_map (Lp.topInclusion (𝕜 := ℝ) μ p).toAddMonoidHom a k
  have hLe' := hLq q
  have hLe : lqNorm q (fun k => dyadicWeight s k * e k) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.LpAddConst_lt_top q).ne (ENNReal.add_ne_top.2
        ⟨ENNReal.one_ne_top, ENNReal.dyadicGeomConst_ne_top one_pos q⟩)) hu) hLe'
  have hbound : lqNorm q (fun k => dyadicWeight s k * eLpNorm (g k) p μ) ≤
      InterpCouple.eBlockConst (min 1 p).toReal s q * (S.lpCouple p).eNormDyadic s q f := by
    have h1 := InterpCouple.lqNorm_nearBestBlocks_le (q := q) (isQuasiNormed_lpCouple S p) hρ
      (lpCouple_norm0_add_rpow_min_le hp0) hbe he he0 s
    simp only [hgb, lpCouple_norm0_topInclusion] at h1
    refine h1.trans ?_
    calc _ ≤ ENNReal.LpAddConst q ^ 2 * 2 ^ (1 / (min 1 p).toReal) * (2 ^ s * (1 + 2 ^ s)) *
          (ENNReal.LpAddConst q * (1 + ENNReal.dyadicGeomConst 1 q) *
            (S.lpCouple p).eNormDyadic s q f) := by gcongr
      _ = _ := by unfold InterpCouple.eBlockConst; ring
  have hL : lqNorm q (fun k => dyadicWeight s k * eLpNorm (g k) p μ) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (InterpCouple.eBlockConst_ne_top _ _ _) hu) hbound
  have hbf : Tendsto (fun k => (S.lpCouple p).norm0 (f - b k)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_zero_of_lqNorm_dyadicWeight_ne_top hq hs hLe) (fun _ => zero_le) hbe
  have hlim : Tendsto (fun n => eLpNorm (⇑f - ∑ k ∈ Finset.range n, ⇑(g k)) p μ) atTop (𝓝 0) := by
    have h := InterpCouple.tendsto_norm0_sub_sum_nearBestBlocks hbf
    simpa only [hgb, lpCouple_norm0_sub_sum_topInclusion] using h
  have hae := ae_hasSum_of_tendsto_eLpNorm hp0
    (ENNReal.tsum_rpow_ne_top_of_lqNorm_dyadicWeight_ne_top hq hs hρ hL) hlim
  have hconv := tendsto_eLpNorm_sub_sum_of_blocks hp0 hs hq hae hL
  refine ⟨g, fun k => ?_, hae, hconv.1, hconv.2, hbound⟩
  rw [hg]
  exact ApproximationScheme.nearBestBlocks_mem ha k

/-- **Block decompositions characterise the Besov spaces, `0 < p ≤ ∞`** (DeVore–Popov, Trans.
Amer. Math. Soc. 305 (1988), Theorem 5.1 and Corollary 5.3, for dyadic splines): for `s > 0` and
`0 < q ≤ ∞`, `f ∈ B^s_{p,q}` if and only if `f = ∑_k g_k` almost everywhere for some
`g_k ∈ S_{2^k}` with `‖(2^(ks) ‖g_k‖_p)_k‖_{ℓ_q} < ∞`
(`FunctionScheme.exists_blocks_of_memBesov`, `FunctionScheme.eNormDyadic_le_of_blocks`). -/
theorem memBesov_iff_exists_blocks (hp0 : p ≠ 0) (hs : 0 < s) (hq : q ≠ 0) {f : Lp ℂ p μ} :
    S.MemBesov p s q f ↔ ∃ g : ℕ → Lp ℂ ∞ μ, (∀ k, g k ∈ S (2 ^ k)) ∧
      (∀ᵐ x ∂μ, HasSum (fun k => g k x) (f x)) ∧
      lqNorm q (fun k => dyadicWeight s k * eLpNorm (g k) p μ) < ∞ := by
  have hρ : 0 < (min 1 p).toReal := ENNReal.toReal_min_one_pos hp0
  constructor
  · intro hf
    obtain ⟨g, hg, hfg, -, -, hL⟩ := exists_blocks_of_memBesov hp0 hs hq hf
    exact ⟨g, hg, hfg, hL.trans_lt (ENNReal.mul_lt_top
      (InterpCouple.eBlockConst_ne_top _ _ _).lt_top
      ((memBesov_iff_eNormDyadic_lt_top hq hs.le).1 hf))⟩
  · rintro ⟨g, hg, hfg, hL⟩
    refine MemBesov.of_eNormDyadic_lt_top hs.le
      ((eNormDyadic_le_of_blocks hp0 hs hq hg hfg).trans_lt
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ?_) hL))
    exact (ENNReal.hardyConst_rpow_ne_top (mul_pos hs hρ) _ (one_div_nonneg.2 hρ.le)).lt_top

end FunctionScheme
