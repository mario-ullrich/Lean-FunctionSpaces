/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.Besov.Nikolskii
public import FunctionSpaces.MeasureSpaces.SchemeLpCouple
public import ApproximationSpaces.Nikolskii

/-!
# Embedding theorems for Besov spaces

Let `μ` be a finite measure on `Ω`, let `S` be a scheme of functions on `(Ω, μ)` with the
Nikolskii property of dimension `D ≥ 0`, and write `α = D (1/p - 1/r)` for `0 < p ≤ r ≤ ∞`.
Then:

* **the Besov embedding with a norm bound** (`exists_uniform_inclusion_eq_of_nikolskii`): for
  `0 < p ≤ r ≤ ∞`, `0 < q ≤ ∞` and `s > α` there is `K < ∞` such that every `f ∈ L_p` whose dyadic
  norm `‖f‖^dy_{s,q}` in the couple of `S` in `L_p` (`FunctionScheme.lpCouple`) is finite lies
  in `L_r`, with `‖f‖^dy_{s-α,q} ≤ K ‖f‖^dy_{s,q}` for the dyadic norm in the couple of `S` in
  `L_r`;
* **the Besov embedding** (`MemBesov.exists_inclusion_eq_of_nikolskii`): for `1 ≤ p ≤ r ≤ ∞`,
  `1 ≤ q ≤ ∞` and `s > α`, every `f ∈ B^s_{p,q}` lies in `L_r` and belongs to `B^{s - α}_{r,q}`;
* **into `L_∞`** (`MemBesov.exists_inclusion_eq_top`, the case `r = ∞`, `α = D/p`): for
  `1 ≤ p ≤ ∞`, `1 ≤ q ≤ ∞` and `s > D/p`, every `f ∈ B^s_{p,q}` lies in `L_∞` and belongs to
  `B^{s - D/p}_{∞,q}`;
* **into bounded continuous functions** (`MemBesov.exists_boundedContinuous_of_nikolskii`): for
  `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`, if moreover `Ω` is a topological space with its Borel
  `σ`-algebra, `μ` charges every nonempty open set and the scheme has continuous approximants,
  every `f ∈ B^s_{p,q}` with `s > D/p` has a bounded continuous representative.

**The norm bound for every `0 < p ≤ r ≤ ∞`.** Mathlib makes `Lp` a normed group for `p ≥ 1`
only; for `p < 1` the function `‖·‖_p` is a quasi-norm, and for a non-atomic `μ` the only
bounded linear functional on `L_p(μ)` is `0` (Day 1940), so the only bounded linear projection
with finite-dimensional range is `0`. The proof therefore sums the blocks of near-best
approximants with the `ρ`-triangle inequality and a Nikolskii inequality, as in the proof of
DeVore–Popov 1988, Theorem 7.1, and identifies the limit through convergence in measure.
Near-best approximants `b_k ∈ S_{2^k}` with `‖f - b_k‖_p ≤ e_k = E(2^k, f) + ‖f‖_p 2^(-k(s+1))`
(`FunctionScheme.exists_nearBest_lpCouple`) have blocks `b_{k+1} - b_k ∈ S_{2^(k+2)}`, on which
the Nikolskii inequality gives `‖b_{k+1} - b_k‖_r ≤ C 2^(2α) 2^(kα) ‖b_{k+1} - b_k‖_p`
(`eLpNorm_sub_succ_le_of_nikolskii`). The transfer of near-best sequences and Hardy's inequality
for tails bound `‖(2^(k(s-α)) ‖f - b_k‖_r)_k‖_{ℓ_q}` by `‖(2^(ks) e_k)_k‖_{ℓ_q}`, for functions
on any measure space (`MeasureTheory.lqNorm_eLpNorm_sub_le_of_nearBest`). Since `b_k ∈ S_{2^k}`,
the error of best approximation of `f` in `L_r` at `2^k` is at most `‖f - b_k‖_r`, which gives
`f ∈ L_r` and the bound (`exists_inclusion_eq_eNormDyadic_le`,
`exists_inclusion_eq_eNormDyadic_le_of_nearBest`, with the constant `nikolskiiTransferConst`).

**For `p ≥ 1`.** The other three theorems are the abstract Nikolskii transfer theorem
(`ApproximationScheme.MemApprox.exists_preimage_of_nikolskii`, the membership form of
`ApproximationScheme.exists_preimage_approxNormDyadic_le_of_nikolskii`) for `X = L_p`,
`Y = L_r` and the inclusion `L_r ↪ L_p`; the pulled-back scheme is again `S` in `L_r`
(`FunctionScheme.comap_toLp_of_le`).  For the last one, `f` in `L_∞` with positive smoothness
is a limit of approximants, which are classes of bounded continuous functions, and these classes
form a closed subspace of `L_∞`.

The limiting case `s = α` is not covered: the proof of the norm bound needs Hardy's constant
`hardyConst ((s - α) ρ_r) (q/ρ_r)` with `ρ_r = min(1, r)`, which is finite for `s > α`, and the
Nikolskii transfer theorem needs `α < s`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst hardyConst)

/-! ### Near-best sequences in weighted `ℓ_q` -/

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] {p r : ℝ≥0∞}

/-- **Near-best sequences in weighted `ℓ_q`, `0 < p, r ≤ ∞`**: let `ρ_p = min(1, p)`,
`ρ_r = min(1, r)`, and let `b_k` be almost everywhere strongly measurable functions with
`‖f - b_k‖_p ≤ e_k`, where `e` decreases to `0`, and blocks with
`‖b_{k+1} - b_k‖_r ≤ C 2^(kβ) ‖b_{k+1} - b_k‖_p`. Then for every `s ∈ ℝ` and every `q`,
`‖(2^(k(s-β)) ‖f - b_k‖_r)_k‖_{ℓ_q} ≤ C 2^(1/ρ_p) H^(1/ρ_r) ‖(2^(ks) e_k)_k‖_{ℓ_q}` with Hardy's
constant `H = hardyConst ((s - β) ρ_r) (q/ρ_r)`, finite for `s > β`. The transfer of near-best
sequences (`MeasureTheory.eLpNorm_sub_rpow_min_le_tsum_of_nearBest`) bounds
`‖f - b_k‖_r^(ρ_r)` by a tail of `(2^(jβ) e_j)^(ρ_r)`, the tail inequality in `ρ_r`-th powers
(`ENNReal.lqNorm_rpow_le_of_rpow_le_tsum`) turns this into a bound of the `ρ_r`-th power of the
left side, and `2^(k(s-β)) 2^(kβ) = 2^(ks)`. -/
theorem lqNorm_eLpNorm_sub_le_of_nearBest (hp0 : p ≠ 0) (hr0 : r ≠ 0) {f : α → E}
    {b : ℕ → α → E} {e : ℕ → ℝ≥0∞} {β : ℝ} {C : ℝ≥0∞}
    (hb : ∀ k, AEStronglyMeasurable (b k) μ) (hbe : ∀ k, eLpNorm (f - b k) p μ ≤ e k)
    (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0))
    (hN : ∀ k, eLpNorm (b (k + 1) - b k) r μ ≤
      C * dyadicWeight β k * eLpNorm (b (k + 1) - b k) p μ) (s : ℝ) (q : ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight (s - β) k * eLpNorm (f - b k) r μ) ≤
      C * 2 ^ (1 / (min 1 p).toReal) *
        hardyConst ((s - β) * (min 1 r).toReal) (q / ENNReal.ofReal (min 1 r).toReal) ^
          (1 / (min 1 r).toReal) * lqNorm q (fun k => dyadicWeight s k * e k) := by
  have hρ : 0 < (min 1 r).toReal := ENNReal.toReal_min_one_pos hr0
  have htail : ∀ k, eLpNorm (f - b k) r μ ^ (min 1 r).toReal ≤
      (C * 2 ^ (1 / (min 1 p).toReal)) ^ (min 1 r).toReal *
        ∑' i, dyadicWeight 0 i * (dyadicWeight β (k + i) * e (k + i)) ^ (min 1 r).toReal :=
    fun k => by
      simpa only [ENNReal.dyadicWeight_zero_left, one_mul] using
        eLpNorm_sub_rpow_min_le_tsum_of_nearBest hp0 hr0 hb hbe he he0 hN k
  have hw : ∀ k, dyadicWeight (s - β) k * (dyadicWeight β k * e k) = dyadicWeight s k * e k :=
    fun k => by rw [← mul_assoc, ← ENNReal.dyadicWeight_add, sub_add_cancel]
  have h := ENNReal.lqNorm_rpow_le_of_rpow_le_tsum (y := fun j => dyadicWeight β j * e j) hρ
    htail (s - β) q
  simp only [sub_zero, hw] at h
  rw [← ENNReal.rpow_le_rpow_iff hρ, ENNReal.mul_rpow_of_nonneg _ _ hρ.le,
    ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ← ENNReal.rpow_mul, one_div_mul_cancel hρ.ne',
    ENNReal.rpow_one]
  exact h

end MeasureTheory

namespace FunctionScheme

/-! ### The norm bound for every `0 < p ≤ r ≤ ∞` -/

/-- The **constant of the Besov embedding along a near-best sequence**: with `ρ_p = min(1, p)`,
`ρ_r = min(1, r)`, Mathlib's constant `C_r = LpAddConst r` of the quasi-triangle inequality in
`L_r` and Hardy's constant `H = hardyConst ((s - α) ρ_r) (q/ρ_r)`, it is
`((1 + C_r) C 2^(2α) H^(1/ρ_r) + C_r C) 2^(1/ρ_p)`, where `C` is the constant of a Nikolskii
inequality `‖a‖_r ≤ C n^α ‖a‖_p`. -/
noncomputable def nikolskiiTransferConst (C : ℝ≥0∞) (α s : ℝ) (p r q : ℝ≥0∞) : ℝ≥0∞ :=
  ((1 + LpAddConst r) * (C * 2 ^ (2 * α)) *
      hardyConst ((s - α) * (min 1 r).toReal) (q / ENNReal.ofReal (min 1 r).toReal) ^
        (1 / (min 1 r).toReal) + LpAddConst r * C) * 2 ^ (1 / (min 1 p).toReal)

/-- **The Hardy factor of `nikolskiiTransferConst` is finite**: with `ρ_r = min(1, r)`, the
factor `hardyConst ((s - α) ρ_r) (q/ρ_r) ^ (1/ρ_r)` is finite for `α < s` and `r ≠ 0`, since
`(s - α) ρ_r > 0` (`ENNReal.hardyConst_ne_top`). -/
theorem nikolskiiTransferConst_hardy_ne_top {α s : ℝ} {r : ℝ≥0∞} (hαs : α < s) (hr0 : r ≠ 0)
    (q : ℝ≥0∞) :
    hardyConst ((s - α) * (min 1 r).toReal) (q / ENNReal.ofReal (min 1 r).toReal) ^
      (1 / (min 1 r).toReal) ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 ENNReal.toReal_nonneg)
    (ENNReal.hardyConst_ne_top (mul_pos (sub_pos.2 hαs) (ENNReal.toReal_min_one_pos hr0)) _)

/-- The constant `nikolskiiTransferConst C α s p r q` is finite for `C < ∞`, `α < s` and
`r ≠ 0`: Hardy's constant `hardyConst ((s - α) ρ_r) (q/ρ_r)` is finite since
`(s - α) ρ_r > 0` (`FunctionScheme.nikolskiiTransferConst_hardy_ne_top`). -/
theorem nikolskiiTransferConst_ne_top {C : ℝ≥0∞} {α s : ℝ} {r : ℝ≥0∞} (hC : C ≠ ∞)
    (hαs : α < s) (hr0 : r ≠ 0) (p q : ℝ≥0∞) : nikolskiiTransferConst C α s p r q ≠ ∞ := by
  have hr : LpAddConst r ≠ ∞ := (ENNReal.LpAddConst_lt_top r).ne
  have hH := nikolskiiTransferConst_hardy_ne_top hαs hr0 q
  unfold nikolskiiTransferConst
  exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hr⟩) (ENNReal.mul_ne_top hC
      (ENNReal.two_rpow_ne_top _))) hH, ENNReal.mul_ne_top hr hC⟩) (ENNReal.two_rpow_ne_top _)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {S : FunctionScheme μ} {D : ℝ} {p r : ℝ≥0∞} {s : ℝ} {q : ℝ≥0∞}

omit [IsFiniteMeasure μ] in
/-- **The Nikolskii inequality on the blocks of a dyadic sequence**: if
`‖a‖_r ≤ C n^α ‖a‖_p` for all `a ∈ S_n`, `n ≥ 1`, and `b_k ∈ S_{2^k}` for every `k`, then
`‖b_{k+1} - b_k‖_r ≤ C 2^(2α) 2^(kα) ‖b_{k+1} - b_k‖_p`, since
`b_{k+1} - b_k ∈ S_{2^(k+2)}` (`ApproximationScheme.sub_mem_pow_add_two`) and
`(2^(k+2))^α = 2^(2α) 2^(kα)`. -/
theorem eLpNorm_sub_succ_le_of_nikolskii {C : ℝ≥0∞} {α : ℝ}
    (hC : ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n, eLpNorm a r μ ≤ C * (n : ℝ≥0∞) ^ α * eLpNorm a p μ)
    {b : ℕ → Lp ℂ ∞ μ} (hb : ∀ k, b k ∈ S (2 ^ k)) (k : ℕ) :
    eLpNorm (⇑(b (k + 1)) - ⇑(b k)) r μ ≤
      C * 2 ^ (2 * α) * dyadicWeight α k * eLpNorm (⇑(b (k + 1)) - ⇑(b k)) p μ := by
  have h := hC (2 ^ (k + 2)) Nat.one_le_two_pow _
    (ApproximationScheme.sub_mem_pow_add_two (hb (k + 1)) (hb k))
  have hae := Lp.coeFn_sub (b (k + 1)) (b k)
  rw [eLpNorm_congr_ae hae, eLpNorm_congr_ae hae, ENNReal.natCast_two_pow_rpow,
    ENNReal.dyadicWeight_add_nat] at h
  refine h.trans_eq ?_
  rw [show dyadicWeight α 2 = 2 ^ (2 * α) by simp [dyadicWeight]]
  ring

/-- **Membership in `L_r` along approximants**: let `p ≤ r`, `q ≠ 0`, `t ∈ ℝ`, let
`b_k ∈ S_{2^k}`, and let `X = ‖(2^(kt) ‖f - b_k‖_r)_k‖_{ℓ_q}` be finite for some `f ∈ L_p`. Then
`f` is the inclusion of some `g ∈ L_r`, and the dyadic norm of `g` in the couple of `S` in `L_r`
satisfies `‖g‖^dy_{t,q} ≤ C_r (X + ‖b_0‖_r) + X` with Mathlib's constant `C_r = LpAddConst r`.
The error of best approximation of `g` at `2^k` is at most `‖g - b_k‖_r = ‖f - b_k‖_r`
(`FunctionScheme.eFunctional_lpCouple_natCast`), and
`‖g‖_r ≤ C_r (‖f - b_0‖_r + ‖b_0‖_r)` with `‖f - b_0‖_r ≤ X`. -/
theorem exists_inclusion_eq_eNormDyadic_le (hpr : p ≤ r) (hq0 : q ≠ 0) {f : Lp ℂ p μ}
    {b : ℕ → Lp ℂ ∞ μ} (hb : ∀ k, b k ∈ S (2 ^ k)) (t : ℝ)
    (hX : lqNorm q (fun k => dyadicWeight t k * eLpNorm (⇑f - ⇑(b k)) r μ) ≠ ∞) :
    ∃ g : Lp ℂ r μ, Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr g = f ∧
      (lpCouple S r).eNormDyadic t q g ≤
        LpAddConst r * (lqNorm q (fun k => dyadicWeight t k * eLpNorm (⇑f - ⇑(b k)) r μ) +
          eLpNorm (b 0) r μ) +
            lqNorm q (fun k => dyadicWeight t k * eLpNorm (⇑f - ⇑(b k)) r μ) := by
  have hx0 : eLpNorm (⇑f - ⇑(b 0)) r μ ≤
      lqNorm q (fun k => dyadicWeight t k * eLpNorm (⇑f - ⇑(b k)) r μ) := by
    simpa only [ENNReal.dyadicWeight_zero_right, one_mul] using
      ENNReal.le_lqNorm hq0 (fun k => dyadicWeight t k * eLpNorm (⇑f - ⇑(b k)) r μ) 0
  have hfr : MemLp f r μ := by
    have hfb : MemLp (⇑f - ⇑(b 0)) r μ := hx0.trans_lt hX.lt_top
    simpa only [sub_add_cancel] using hfb.add ((Lp.memLp (b 0)).mono_exponent le_top)
  have hg : ⇑(hfr.toLp f) =ᵐ[μ] f := hfr.coeFn_toLp
  refine ⟨hfr.toLp f, ?_, ?_⟩
  · ext1
    filter_upwards [Lp.coeFn_inclusionOfExponentLeLinear (𝕜 := ℝ) hpr (hfr.toLp f), hg]
      with x h1 h2
    rw [h1, h2]
  rw [InterpCouple.eNormDyadic, lpCouple_norm0, eLpNorm_congr_ae hg]
  refine add_le_add ?_ (ENNReal.lqNorm_mono fun k => ?_)
  · calc eLpNorm f r μ = eLpNorm ((⇑f - ⇑(b 0)) + ⇑(b 0)) r μ := by rw [sub_add_cancel]
      _ ≤ LpAddConst r * (eLpNorm (⇑f - ⇑(b 0)) r μ + eLpNorm (b 0) r μ) := eLpNorm_add_le' r
      _ ≤ _ := by gcongr
  gcongr
  calc (lpCouple S r).eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (hfr.toLp f)
      ≤ eLpNorm (⇑(hfr.toLp f) - ⇑(b k)) r μ :=
        (eFunctional_lpCouple_natCast (2 ^ k) _).trans_le (iInf₂_le (b k) (hb k))
    _ = eLpNorm (⇑f - ⇑(b k)) r μ := eLpNorm_congr_ae (hg.sub (EventuallyEq.refl _ _))

/-- **The Besov embedding along a near-best sequence**, for `0 < p ≤ r ≤ ∞` and `q ≠ 0`: let
`‖a‖_r ≤ C n^α ‖a‖_p` for all `a ∈ S_n`, `n ≥ 1`, with `C < ∞`, `α < s` and `s > 0`. Let
`f ∈ L_p`, `b_k ∈ S_{2^k}` and a decreasing sequence `e` with `‖f - b_k‖_p ≤ e_k`,
`‖f‖_p ≤ e_0` and `Y = ‖(2^(ks) e_k)_k‖_{ℓ_q} < ∞`. Then `f` is the inclusion of some
`g ∈ L_r` whose dyadic norm in the couple of `S` in `L_r` satisfies
`‖g‖^dy_{s-α,q} ≤ K₀ Y` with `K₀ = nikolskiiTransferConst C α s p r q`. The terms `e_k` tend to
`0` (`ENNReal.tendsto_zero_of_lqNorm_dyadicWeight_ne_top`, since `s > 0`), the blocks satisfy
the Nikolskii inequality (`FunctionScheme.eLpNorm_sub_succ_le_of_nikolskii`), so
`MeasureTheory.lqNorm_eLpNorm_sub_le_of_nearBest` bounds `X = ‖(2^(k(s-α)) ‖f - b_k‖_r)_k‖_{ℓ_q}`
by `C 2^(2α) 2^(1/ρ_p) H^(1/ρ_r) Y`; `FunctionScheme.exists_inclusion_eq_eNormDyadic_le` gives
`g`, and `‖b_0‖_r ≤ C ‖b_0‖_p ≤ C 2^(1/ρ_p) e_0 ≤ C 2^(1/ρ_p) Y`
(`MeasureTheory.eLpNorm_sub_le_two_rpow_mul` with `‖f - 0‖_p ≤ e_0`). -/
theorem exists_inclusion_eq_eNormDyadic_le_of_nearBest {C : ℝ≥0∞} {α : ℝ} (hC : C ≠ ∞)
    (hCa : ∀ n : ℕ, 1 ≤ n → ∀ a ∈ S n, eLpNorm a r μ ≤ C * (n : ℝ≥0∞) ^ α * eLpNorm a p μ)
    (hp0 : p ≠ 0) (hpr : p ≤ r) (hαs : α < s) (hs0 : 0 < s) (hq0 : q ≠ 0) {f : Lp ℂ p μ}
    {b : ℕ → Lp ℂ ∞ μ} {e : ℕ → ℝ≥0∞} (hb : ∀ k, b k ∈ S (2 ^ k))
    (hbe : ∀ k, eLpNorm (⇑f - ⇑(b k)) p μ ≤ e k) (hf : eLpNorm f p μ ≤ e 0) (he : Antitone e)
    (hY : lqNorm q (fun k => dyadicWeight s k * e k) ≠ ∞) :
    ∃ g : Lp ℂ r μ, Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr g = f ∧
      (lpCouple S r).eNormDyadic (s - α) q g ≤
        nikolskiiTransferConst C α s p r q * lqNorm q (fun k => dyadicWeight s k * e k) := by
  have hr0 : r ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hp0) hpr).ne'
  have hH := nikolskiiTransferConst_hardy_ne_top hαs hr0 q
  have hB := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hC
    (ENNReal.two_rpow_ne_top (2 * α))) (ENNReal.two_rpow_ne_top (1 / (min 1 p).toReal))) hH
  have hX := lqNorm_eLpNorm_sub_le_of_nearBest hp0 hr0 (fun k => Lp.aestronglyMeasurable (b k))
    hbe he (ENNReal.tendsto_zero_of_lqNorm_dyadicWeight_ne_top hq0 hs0 hY)
    (eLpNorm_sub_succ_le_of_nikolskii hCa hb) s q
  obtain ⟨g, hg, hgN⟩ := exists_inclusion_eq_eNormDyadic_le hpr hq0 hb (s - α)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top hB hY) hX)
  refine ⟨g, hg, hgN.trans ?_⟩
  have he0 : e 0 ≤ lqNorm q (fun k => dyadicWeight s k * e k) := by
    simpa only [ENNReal.dyadicWeight_zero_right, one_mul] using
      ENNReal.le_lqNorm hq0 (fun k => dyadicWeight s k * e k) 0
  have hb0 : eLpNorm (b 0) r μ ≤
      C * (2 ^ (1 / (min 1 p).toReal) * lqNorm q (fun k => dyadicWeight s k * e k)) := by
    have h1 : eLpNorm (b 0) p μ ≤ 2 ^ (1 / (min 1 p).toReal) * e 0 := by
      simpa only [zero_sub, eLpNorm_neg] using
        eLpNorm_sub_le_two_rpow_mul hp0 (g := 0) (by rwa [sub_zero]) (hbe 0)
    calc eLpNorm (b 0) r μ ≤ C * ((1 : ℕ) : ℝ≥0∞) ^ α * eLpNorm (b 0) p μ :=
          hCa 1 le_rfl _ (by simpa using hb 0)
      _ ≤ _ := by
          rw [Nat.cast_one, ENNReal.one_rpow, mul_one]
          gcongr
          exact h1.trans (by gcongr)
  unfold nikolskiiTransferConst
  set X := lqNorm q (fun k => dyadicWeight (s - α) k * eLpNorm (⇑f - ⇑(b k)) r μ)
  set Y := lqNorm q (fun k => dyadicWeight s k * e k)
  set c : ℝ≥0∞ := 2 ^ (1 / (min 1 p).toReal)
  set H := hardyConst ((s - α) * (min 1 r).toReal) (q / ENNReal.ofReal (min 1 r).toReal) ^
    (1 / (min 1 r).toReal)
  calc LpAddConst r * (X + eLpNorm (b 0) r μ) + X
      ≤ LpAddConst r * (C * 2 ^ (2 * α) * c * H * Y + C * (c * Y)) +
          C * 2 ^ (2 * α) * c * H * Y := by gcongr
    _ = ((1 + LpAddConst r) * (C * 2 ^ (2 * α)) * H + LpAddConst r * C) * c * Y := by ring

/-- **The Besov embedding** in the dyadic norms of the couples, for `0 < p ≤ r ≤ ∞` and
`0 < q ≤ ∞` (the method of the proof of DeVore–Popov 1988, Theorem 7.1; Kerkyacharian–Petrushev
2015, Proposition 6.14, for Besov spaces on Dirichlet spaces): let `S` have the Nikolskii
property of dimension `D ≥ 0` and `α = D(1/p - 1/r) < s`. There is `K < ∞` such that every
`f ∈ L_p` whose dyadic norm `‖f‖^dy_{s,q}` in the couple of `S` in `L_p` is finite is the
inclusion of some `g ∈ L_r` with `‖g‖^dy_{s-α,q} ≤ K ‖f‖^dy_{s,q}`, the dyadic norm of `g` in
the couple of `S` in `L_r`. The Nikolskii inequality for `0 < p ≤ r`
(`FunctionScheme.HasNikolskii.exists_eLpNorm_le_of_le`) and near-best approximants
(`FunctionScheme.exists_nearBest_lpCouple`) with the tolerances
`e_k = E(2^k, f) + ‖f‖_p 2^(-k(s+1))`, which decrease
(`InterpCouple.antitone_eFunctional_add_dyadicWeight`) and satisfy
`‖(2^(ks) e_k)_k‖_{ℓ_q} ≤ C_q (1 + γ_{1,q}) ‖f‖^dy_{s,q}`
(`InterpCouple.lqNorm_dyadicWeight_mul_eFunctional_add_le`), give the bound along the near-best
sequence (`FunctionScheme.exists_inclusion_eq_eNormDyadic_le_of_nearBest`), so
`K = nikolskiiTransferConst C α s p r q · C_q (1 + γ_{1,q})` with `C_q = LpAddConst q` and
`γ_{1,q} = dyadicGeomConst 1 q`. For the dyadic steps on `[0, 1)` (`D = 1`), `r = 1` and
`0 < p ≤ 1`, the resulting bound of `‖f‖_1` is `Haar.eLpNorm_one_le_eNormDyadic`. -/
theorem exists_uniform_inclusion_eq_of_nikolskii (h : S.HasNikolskii D) (hD : 0 ≤ D)
    (hp0 : p ≠ 0) (hpr : p ≤ r) (hs : nikolskiiExponent D p r < s) (hq0 : q ≠ 0) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p μ, (lpCouple S p).eNormDyadic s q f ≠ ∞ →
      ∃ g : Lp ℂ r μ, Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr g = f ∧
        (lpCouple S r).eNormDyadic (s - nikolskiiExponent D p r) q g ≤
          K * (lpCouple S p).eNormDyadic s q f := by
  have hα := nikolskiiExponent_nonneg hD hp0 hpr
  have hM : LpAddConst q * (1 + dyadicGeomConst 1 q) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q).ne
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.dyadicGeomConst_ne_top one_pos q⟩)
  obtain ⟨C, hC, hCa⟩ := h.exists_eLpNorm_le_of_le hp0 hpr
  refine ⟨nikolskiiTransferConst C (nikolskiiExponent D p r) s p r q *
      (LpAddConst q * (1 + dyadicGeomConst 1 q)),
    ENNReal.mul_ne_top (nikolskiiTransferConst_ne_top hC hs
      (lt_of_lt_of_le (pos_iff_ne_zero.2 hp0) hpr).ne' p q) hM, fun f hf => ?_⟩
  obtain ⟨b, hb, hbe⟩ := exists_nearBest_lpCouple (S := S) f s
  have hY := InterpCouple.lqNorm_dyadicWeight_mul_eFunctional_add_le (lpCouple S p) s q f
  have hf0 : eLpNorm f p μ ≤ (lpCouple S p).eFunctional ((2 ^ 0 : ℕ) : ℝ≥0∞) f +
      eLpNorm f p μ * dyadicWeight (-(s + 1)) 0 := by
    rw [ENNReal.dyadicWeight_zero_right, mul_one]
    exact le_add_self
  obtain ⟨g, hg, hgN⟩ := exists_inclusion_eq_eNormDyadic_le_of_nearBest hC hCa hp0 hpr hs
    (hα.trans_lt hs) hq0 hb hbe hf0
    ((lpCouple S p).antitone_eFunctional_add_dyadicWeight (by linarith) f)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top hM hf) hY)
  refine ⟨g, hg, hgN.trans ?_⟩
  rw [mul_assoc]
  gcongr
  exact hY

/-! ### The Besov embeddings for `1 ≤ p ≤ r ≤ ∞` -/

variable [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- **The Besov embedding** `B^s_{p,q} ↪ B^{s - D(1/p - 1/r)}_{r,q}` for `p ≤ r` and
`s > D(1/p - 1/r)`: every `f ∈ B^s_{p,q}` is the inclusion of some `g ∈ L_r` lying in
`B^{s - D(1/p-1/r)}_{r,q}`. -/
theorem MemBesov.exists_inclusion_eq_of_nikolskii (h : S.HasNikolskii D) (hD : 0 ≤ D)
    (hpr : p ≤ r) (hs : nikolskiiExponent D p r < s) (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : S.MemBesov p s q f) :
    ∃ g : Lp ℂ r μ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g = f ∧
      S.MemBesov r (s - nikolskiiExponent D p r) q g := by
  obtain ⟨C, hC, hN⟩ := h.liftBound hpr
  have hα := nikolskiiExponent_nonneg hD (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpr
  obtain ⟨g, hg, hmem⟩ := ApproximationScheme.MemApprox.exists_preimage_of_nikolskii
    (Lp.inclusionOfExponentLe_injective hpr) hN hC hα hs hq (memBesov_iff_memApprox.1 hf)
  refine ⟨g, hg, ?_⟩
  rw [memBesov_iff_memApprox]
  rwa [comap_toLp_of_le hpr] at hmem

/-- **Embedding into `L_∞`**: for `s > D/p`, every `f ∈ B^s_{p,q}` is the inclusion of some
`g ∈ L_∞` lying in `B^{s - D/p}_{∞,q}`. -/
theorem MemBesov.exists_inclusion_eq_top (h : S.HasNikolskii D) (hD : 0 ≤ D)
    (hs : D * p.toReal⁻¹ < s) (hq : 1 ≤ q) {f : Lp ℂ p μ} (hf : S.MemBesov p s q f) :
    ∃ g : Lp ℂ ∞ μ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ le_top g = f ∧
      S.MemBesov ∞ (s - D * p.toReal⁻¹) q g := by
  have := hf.exists_inclusion_eq_of_nikolskii h hD (le_top : p ≤ ∞)
    (by rwa [nikolskiiExponent_top]) hq
  rwa [nikolskiiExponent_top] at this

/-- **Embedding into bounded continuous functions**: if `Ω` is a topological space with its Borel
`σ`-algebra, `μ` charges every nonempty open set, the scheme has continuous approximants and
`s > D/p`, every `f ∈ B^s_{p,q}` has a bounded continuous representative. -/
theorem MemBesov.exists_boundedContinuous_of_nikolskii [TopologicalSpace Ω] [BorelSpace Ω]
    [μ.IsOpenPosMeasure] (hS : S.HasContinuousApproximants) (h : S.HasNikolskii D)
    (hD : 0 ≤ D) (hs : D * p.toReal⁻¹ < s) (hq : 1 ≤ q) {f : Lp ℂ p μ}
    (hf : S.MemBesov p s q f) :
    ∃ a : Ω →ᵇ ℂ, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ le_top
      (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ a) = f := by
  obtain ⟨g, hg, hmem⟩ := hf.exists_inclusion_eq_top h hD hs hq
  have hcl : g ∈ closure (⋃ n, S.toLp ∞ n) :=
    ApproximationScheme.mem_closure_iUnion_of_memApprox hq (sub_pos.2 hs)
      (memBesov_iff_memApprox.1 hmem)
  have hsub : (⋃ n, S.toLp ∞ n) ⊆
      Set.range (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ : (Ω →ᵇ ℂ) → Lp ℂ ∞ μ) := by
    rintro _ ⟨_, ⟨n, rfl⟩, a, ha, rfl⟩
    obtain ⟨b, hb⟩ := hS n ha
    exact ⟨b, hb.trans (Lp.inclusionOfExponentLeLinear_self (𝕜 := ℝ) a).symm⟩
  obtain ⟨a, ha⟩ := (BoundedContinuousFunction.isClosed_range_toLp_top (μ := μ) (𝕜 := ℝ)
    (E := ℂ)).closure_subset_iff.2 hsub hcl
  exact ⟨a, by rw [ha, hg]⟩

end FunctionScheme
