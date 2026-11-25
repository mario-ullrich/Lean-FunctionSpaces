/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.Besov.Nikolskii
public import FunctionSpaces.MeasureSpaces.SchemeLpCouple

/-!
# Embedding theorems for Besov spaces

Let `μ` be a finite measure on `Ω`, let `S` be a scheme of functions on `(Ω, μ)` with the
Nikolskii property of dimension `D ≥ 0`, and write `α = D (1/p - 1/r)` for `0 < p ≤ r ≤ ∞`.
Then, for every `0 < q ≤ ∞`:

* **the Besov embedding with a norm bound** (`exists_uniform_inclusion_eq_of_nikolskii`): for
  `s > α` there is `K < ∞` such that every `f ∈ L_p` whose dyadic norm `‖f‖^dy_{s,q}` in the
  couple of `S` in `L_p` (`FunctionScheme.lpCouple`) is finite is the inclusion of some
  `g ∈ L_r`, with `‖g‖^dy_{s-α,q} ≤ K ‖f‖^dy_{s,q}` for the dyadic norm in the couple of `S` in
  `L_r`, and so `‖f‖_r ≤ K' ‖f‖^dy_{s,q}` for every `f ∈ L_p`
  (`exists_eLpNorm_le_eNormDyadic_of_nikolskii`);
* **the Besov embedding** (`MemBesov.exists_inclusion_eq_of_nikolskii`): for `s > α`, every
  `f ∈ B^s_{p,q}` lies in `L_r` and belongs to `B^{s - α}_{r,q}`;
* **into `L_∞`** (`MemBesov.exists_inclusion_eq_top`, the case `r = ∞`, `α = D/p`): for
  `s > D/p`, every `f ∈ B^s_{p,q}` lies in `L_∞` and belongs to `B^{s - D/p}_{∞,q}`;
* **into bounded continuous functions** (`MemBesov.exists_boundedContinuous_of_nikolskii`): if
  moreover `Ω` is a topological space with its Borel `σ`-algebra, `μ` charges every nonempty
  open set and the scheme has continuous approximants, every `f ∈ B^s_{p,q}` with `s > D/p` has a
  bounded continuous representative.

**The norm bound for every `0 < p ≤ r ≤ ∞`.** Mathlib makes `Lp` a normed group for `p ≥ 1`
only; for `p < 1` the function `‖·‖_p` is a quasi-norm, and `L_p[0, 1]` has no nonzero
continuous linear functional (Day 1940, see `FunctionSpaces.Analysis.Lp.QuasiNorm`), so near-best
approximants take the role of bounded linear projections onto the approximants. The proof
therefore sums the blocks of near-best approximants with the `ρ`-triangle inequality and a
Nikolskii inequality, as in the proof of DeVore–Popov 1988, Theorem 7.1, and identifies the limit
through convergence in measure. Near-best approximants `b_k ∈ S_{2^k}` with
`‖f - b_k‖_p ≤ e_k = E(2^k, f) + ‖f‖_p 2^(-k(s+1))` (`FunctionScheme.exists_nearBest_lpCouple`)
have blocks `b_{k+1} - b_k ∈ S_{2^(k+2)}`, on which the Nikolskii inequality gives
`‖b_{k+1} - b_k‖_r ≤ C 2^(2α) 2^(kα) ‖b_{k+1} - b_k‖_p`
(`FunctionScheme.eLpNorm_sub_succ_le_of_nikolskii`). The transfer of near-best sequences and
Hardy's inequality for tails bound `‖(2^(k(s-α)) ‖f - b_k‖_r)_k‖_{ℓ_q}` by
`‖(2^(ks) e_k)_k‖_{ℓ_q}`, for functions on any measure space
(`MeasureTheory.lqNorm_eLpNorm_sub_le_of_nearBest`). Since `b_k ∈ S_{2^k}`, the error of best
approximation of `f` in `L_r` at `2^k` is at most `‖f - b_k‖_r`, which gives `f ∈ L_r` and the
bound (`FunctionScheme.exists_inclusion_eq_eNormDyadic_le`,
`exists_inclusion_eq_eNormDyadic_le_of_nearBest`, with the constant `nikolskiiTransferConst`).

**The Besov spaces.** For smoothness `s ≥ 0` the Besov space `B^s_{p,q}` consists of the `f`
with finite dyadic norm (`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`), and `s > α ≥ 0`, so
the norm bound gives the second theorem, and the case `r = ∞` the third. For the last one, the
class `g ∈ L_∞` of the third theorem lies in `B^{s - D/p}_{∞,∞}`
(`FunctionScheme.MemBesov.mono`), which is the approximation space of `S` in the normed space
`L_∞` (`FunctionScheme.memBesov_iff_memApprox`). With positive smoothness `g` is a limit of
approximants, which are classes of bounded continuous functions, and these classes form a closed
subspace of `L_∞`.

The limiting case `s = α` is not covered: the proof of the norm bound needs Hardy's constant
`hardyConst ((s - α) ρ_r) (q/ρ_r)` with `ρ_r = min(1, r)`, which is finite for `s > α`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst hardyConst)

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
`γ_{1,q} = dyadicGeomConst 1 q`. For the dyadic steps on `[0, 1)` (`D = 1`) this is
`Haar.exists_uniform_inclusion_eq_stepCouple`, and the bound of `‖f‖_r` that follows
(`FunctionScheme.exists_eLpNorm_le_eNormDyadic_of_nikolskii`) is
`Haar.exists_eLpNorm_le_eNormDyadic_stepCouple`; for `r = 1` and `0 < p ≤ 1` it is
`Haar.eLpNorm_one_le_eNormDyadic`, proved directly with an explicit constant. -/
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

/-- **The Besov embedding into `L_r`** in the dyadic norm, for `0 < p ≤ r ≤ ∞` and
`0 < q ≤ ∞`: let `S` have the Nikolskii property of dimension `D ≥ 0` and
`α = D(1/p - 1/r) < s`. There is `K < ∞` with `‖f‖_r ≤ K ‖f‖^dy_{s,q}` for every `f ∈ L_p`, with
the dyadic norm `‖f‖^dy_{s,q} = ‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q}` of `f` in the couple of `S`
in `L_p`. For a finite right side this is the bound `‖g‖_r ≤ ‖g‖^dy_{s-α,q}` of the dyadic norm
in `L_r` together with `FunctionScheme.exists_uniform_inclusion_eq_of_nikolskii`; `K` is taken at
least `1`, so that the bound also holds when the right side is infinite. -/
theorem exists_eLpNorm_le_eNormDyadic_of_nikolskii (h : S.HasNikolskii D) (hD : 0 ≤ D)
    (hp0 : p ≠ 0) (hpr : p ≤ r) (hs : nikolskiiExponent D p r < s) (hq0 : q ≠ 0) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p μ,
      eLpNorm f r μ ≤ K * (lpCouple S p).eNormDyadic s q f := by
  obtain ⟨K, hK, hKf⟩ := exists_uniform_inclusion_eq_of_nikolskii h hD hp0 hpr hs hq0
  refine ⟨max K 1, max_ne_top hK ENNReal.one_ne_top, fun f => ?_⟩
  rcases eq_or_ne ((lpCouple S p).eNormDyadic s q f) ∞ with hf | hf
  · rw [hf, ENNReal.mul_top (zero_lt_one.trans_le (le_max_right K 1)).ne']
    exact le_top
  obtain ⟨g, rfl, hg⟩ := hKf f hf
  calc eLpNorm (Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr g) r μ = eLpNorm g r μ :=
        Lp.eLpNorm_inclusionOfExponentLeLinear hpr g r
    _ = (lpCouple S r).norm0 g := (lpCouple_norm0 g).symm
    _ ≤ (lpCouple S r).eNormDyadic (s - nikolskiiExponent D p r) q g := le_self_add
    _ ≤ K * (lpCouple S p).eNormDyadic s q _ := hg
    _ ≤ max K 1 * (lpCouple S p).eNormDyadic s q _ := by gcongr; exact le_max_left K 1

/-! ### The embeddings of the Besov spaces, `0 < p ≤ r ≤ ∞` -/

/-- **The Besov embedding** `B^s_{p,q} ↪ B^{s - α}_{r,q}`, `α = D(1/p - 1/r)`, for
`0 < p ≤ r ≤ ∞`, `0 < q ≤ ∞` and `s > α`, for a scheme with the Nikolskii property of
dimension `D ≥ 0`: every `f ∈ B^s_{p,q}` is the inclusion of some `g ∈ L_r` lying in
`B^{s - α}_{r,q}`. Since `s > α ≥ 0`, membership in both Besov spaces is the finiteness of the
dyadic norms of the couples (`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`), which the norm
bound `FunctionScheme.exists_uniform_inclusion_eq_of_nikolskii` compares. -/
theorem MemBesov.exists_inclusion_eq_of_nikolskii (h : S.HasNikolskii D) (hD : 0 ≤ D)
    (hp0 : p ≠ 0) (hpr : p ≤ r) (hs : nikolskiiExponent D p r < s) (hq0 : q ≠ 0)
    {f : Lp ℂ p μ} (hf : S.MemBesov p s q f) :
    ∃ g : Lp ℂ r μ, Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr g = f ∧
      S.MemBesov r (s - nikolskiiExponent D p r) q g := by
  have hα := nikolskiiExponent_nonneg hD hp0 hpr
  rw [memBesov_iff_eNormDyadic_lt_top hq0 (hα.trans hs.le)] at hf
  obtain ⟨K, hK, hKf⟩ := exists_uniform_inclusion_eq_of_nikolskii h hD hp0 hpr hs hq0
  obtain ⟨g, hg, hgN⟩ := hKf f hf.ne
  exact ⟨g, hg, MemBesov.of_eNormDyadic_lt_top (sub_nonneg.2 hs.le)
    (hgN.trans_lt (ENNReal.mul_lt_top hK.lt_top hf))⟩

/-- **Embedding into `L_∞`**, for `0 < p ≤ ∞` and `0 < q ≤ ∞`: for a scheme with the Nikolskii
property of dimension `D ≥ 0` and `s > D/p`, every `f ∈ B^s_{p,q}` is the inclusion of some
`g ∈ L_∞` lying in `B^{s - D/p}_{∞,q}`. This is the case `r = ∞` of
`FunctionScheme.MemBesov.exists_inclusion_eq_of_nikolskii`, where `D(1/p - 1/∞) = D/p`
(`nikolskiiExponent_top`). -/
theorem MemBesov.exists_inclusion_eq_top (h : S.HasNikolskii D) (hD : 0 ≤ D) (hp0 : p ≠ 0)
    (hs : D * p.toReal⁻¹ < s) (hq0 : q ≠ 0) {f : Lp ℂ p μ} (hf : S.MemBesov p s q f) :
    ∃ g : Lp ℂ ∞ μ, Lp.topInclusion (𝕜 := ℝ) μ p g = f ∧
      S.MemBesov ∞ (s - D * p.toReal⁻¹) q g := by
  have := hf.exists_inclusion_eq_of_nikolskii h hD hp0 (le_top : p ≤ ∞)
    (by rwa [nikolskiiExponent_top]) hq0
  rwa [nikolskiiExponent_top] at this

/-- **Embedding into bounded continuous functions**, for `0 < p ≤ ∞` and `0 < q ≤ ∞`: if `Ω` is
a topological space with its Borel `σ`-algebra, `μ` charges every nonempty open set, the scheme
has continuous approximants and the Nikolskii property of dimension `D ≥ 0`, and `s > D/p`, every
`f ∈ B^s_{p,q}` has a bounded continuous representative. The class `g ∈ L_∞` of
`FunctionScheme.MemBesov.exists_inclusion_eq_top` lies in `B^{s - D/p}_{∞,∞}`
(`FunctionScheme.MemBesov.mono`), the approximation space of `S` in `L_∞`
(`FunctionScheme.memBesov_iff_memApprox`), so it is a limit of approximants
(`ApproximationScheme.mem_closure_iUnion_of_memApprox`); these are classes of bounded continuous
functions, which form a closed subset of `L_∞`
(`BoundedContinuousFunction.isClosed_range_toLp_top`). -/
theorem MemBesov.exists_boundedContinuous_of_nikolskii [TopologicalSpace Ω] [BorelSpace Ω]
    [μ.IsOpenPosMeasure] (hS : S.HasContinuousApproximants) (h : S.HasNikolskii D)
    (hD : 0 ≤ D) (hp0 : p ≠ 0) (hs : D * p.toReal⁻¹ < s) (hq0 : q ≠ 0) {f : Lp ℂ p μ}
    (hf : S.MemBesov p s q f) :
    ∃ a : Ω →ᵇ ℂ, Lp.topInclusion (𝕜 := ℝ) μ p
      (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ a) = f := by
  obtain ⟨g, hg, hmem⟩ := hf.exists_inclusion_eq_top h hD hp0 hs hq0
  have htop : S.MemBesov ∞ (s - D * p.toReal⁻¹) ∞ g :=
    hmem.mono hq0 (sub_pos.2 hs).le (Or.inr ⟨rfl, le_top⟩)
  have hcl : g ∈ closure (⋃ n, S.toLp ∞ n) :=
    ApproximationScheme.mem_closure_iUnion_of_memApprox le_top (sub_pos.2 hs)
      (memBesov_iff_memApprox.1 htop)
  have hsub : (⋃ n, S.toLp ∞ n) ⊆
      Set.range (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ : (Ω →ᵇ ℂ) → Lp ℂ ∞ μ) := by
    rintro _ ⟨_, ⟨n, rfl⟩, a, ha, rfl⟩
    obtain ⟨b, hb⟩ := hS n ha
    exact ⟨b, hb.trans (Lp.inclusionOfExponentLeLinear_self (𝕜 := ℝ) a).symm⟩
  obtain ⟨a, ha⟩ := (BoundedContinuousFunction.isClosed_range_toLp_top (μ := μ) (𝕜 := ℝ)
    (E := ℂ)).closure_subset_iff.2 hsub hcl
  exact ⟨a, by rw [ha, hg]⟩

end FunctionScheme
