/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Interpolation.EFunctionalSpaces
public import ApproximationSpaces.Sequences.Hardy

/-!
# Block decompositions of the E-spaces of a `ρ`-normed couple

Let `A = (N₀, N₁)` be a couple on an abelian group (`InterpCouple`) whose first norm has a
subadditive `ρ`-th power, `N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for some `ρ > 0`, as the quasi-norm
`‖·‖_p` with `ρ = min(1, p)`. This file characterises the approximation spaces `E_{s,q}` of the
couple by block decompositions (DeVore–Popov, Trans. Amer. Math. Soc. 305 (1988), Theorem 5.1).
A **block decomposition** of `u` is a sequence `g_k` with `N₁(g_k) ≤ 2^k` whose partial sums
`∑_{k<n} g_k` converge to `u` in `N₀`; its size is `‖(2^(ks) N₀(g_k))_k‖_{ℓ_q}`, and the
infimum of the sizes is `InterpCouple.eBlockDecompNorm`. The norm `N₃` of DeVore–Popov is the
size of one block decomposition, the blocks `T_k - T_{k-1}` of their spline approximants `T_k`.
Here the dyadic norm, which is their `N₁` for dyadic splines, is bounded by the size of every
block decomposition (`InterpCouple.eNormDyadic_le_of_tendsto_sum`) and bounds the size of the
blocks of near-best approximants (`InterpCouple.exists_blocks_eNormDyadic`).

* **Partial sums**: `N₁(∑_{k<n} g_k) ≤ 2^n` if `N₁(0) = 0` and `N₁` is subadditive
  (`InterpCouple.norm1_sum_range_le`), and `N₀(u - ∑_{k<n} g_k)^ρ ≤ ∑_{i ≥ 0} N₀(g_{n+i})^ρ`
  (`InterpCouple.norm0_sub_sum_rpow_le_tsum`): the `ρ`-triangle inequality bounds the finite
  pieces of the tail, and the partial sums converge, so no completeness is used.
* **Blocks of a sequence**: `g_0 = 0`, `g_1 = b_0`, `g_{k+2} = b_{k+1} - b_k`
  (`InterpCouple.nearBestBlocks`), with the partial sums `∑_{j<k+2} g_j = b_k`
  (`InterpCouple.sum_range_nearBestBlocks`); additive maps commute with the blocks
  (`InterpCouple.nearBestBlocks_map`). For `b_k` with `N₀(u - b_k) ≤ e_k`, `e` decreasing and
  `N₀(u) ≤ e_0`, `‖(2^(ks) N₀(g_k))_k‖_{ℓ_q} ≤ C_q² 2^(1/ρ) 2^s (1 + 2^s) ‖(2^(ks) e_k)_k‖_{ℓ_q}`
  with `C_q = LpAddConst q` (`InterpCouple.lqNorm_nearBestBlocks_le`).
* **The two bounds**: for a quasi-normed couple with subadditive complexity and `0 < q ≤ ∞`,
  every block decomposition gives `‖u‖^dy_{s,q} ≤ 2 H^(1/ρ) ‖(2^(ks) N₀(g_k))_k‖_{ℓ_q}` with
  Hardy's constant `H = hardyConst (sρ) (q/ρ)` (`InterpCouple.eNormDyadic_le_of_tendsto_sum`);
  near-best sequences give block decompositions of size at most `eBlockConst ρ s q ‖u‖^dy_{s,q}`
  for `s > 0` (`InterpCouple.exists_blocks_eNormDyadic`). So for `s > 0`,
  `‖u‖^dy_{s,q} < ∞` if and only if `u` has a block decomposition of finite size
  (`InterpCouple.eNormDyadic_lt_top_iff_eBlockDecompNorm_lt_top`).

For a scheme in a Banach space and `q ≥ 1` this is
`ApproximationScheme.memApprox_iff_blockDecompNorm_lt_top`, where the series of blocks converges
by completeness; here the convergence of the partial sums is part of the definition.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst hardyConst)

namespace InterpCouple

variable {U : Type*} [AddCommGroup U] {A : InterpCouple U} {C : ℝ≥0∞} {ρ s : ℝ} {q : ℝ≥0∞}

/-! ### Blocks of a sequence -/

/-- The **blocks of a sequence** `b`: `g 0 = 0`, `g 1 = b 0` and `g (k + 2) = b (k + 1) - b k`, so
that the partial sums `∑_{j < k+2} g_j` are the `b_k`. Applied to approximants `b_k = T_k`, these
are the blocks `t_k = T_k - T_{k-1}` (`T_{-1} = 0`) of DeVore–Popov moved up by one level,
`g_{k+1} = t_k`, since a subadditive complexity gives only `N₁(b_{k+1} - b_k) ≤ 2^(k+2)`. -/
def nearBestBlocks (b : ℕ → U) : ℕ → U
  | 0 => 0
  | 1 => b 0
  | k + 2 => b (k + 1) - b k

/-- The partial sums of the blocks are the elements of the sequence:
`∑_{j < k+2} g_j = b_k`. -/
theorem sum_range_nearBestBlocks (b : ℕ → U) (k : ℕ) :
    ∑ j ∈ range (k + 2), nearBestBlocks b j = b k := by
  induction k with
  | zero => simp [Finset.sum_range_succ, nearBestBlocks]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [nearBestBlocks]
    abel

/-- **Additive maps commute with the blocks**: the blocks `g'` of the image sequence `(T b_j)_j`
are `g'_k = T(g_k)`. -/
theorem nearBestBlocks_map {V : Type*} [AddCommGroup V] (T : U →+ V) (b : ℕ → U) (k : ℕ) :
    nearBestBlocks (fun j => T (b j)) k = T (nearBestBlocks b k) := by
  rcases k with _ | _ | k
  · exact (map_zero T).symm
  · rfl
  · exact (map_sub T _ _).symm

/-- **The blocks have the complexity of their level**: if the couple is quasi-normed, `N₁` is
subadditive and `N₁(b_k) ≤ 2^k` for every `k`, then the blocks `g_k` of `b`
(`InterpCouple.nearBestBlocks`) satisfy `N₁(g_k) ≤ 2^k`, since
`N₁(b_{k+1} - b_k) ≤ 2^(k+1) + 2^k ≤ 2^(k+2)`. -/
theorem norm1_nearBestBlocks_le (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {b : ℕ → U}
    (hb : ∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞)) (k : ℕ) :
    A.norm1 (nearBestBlocks b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := by
  rcases k with _ | _ | k
  · exact hA.norm1_zero.trans_le zero_le
  · exact (hb 0).trans (Nat.cast_le.2 (by norm_num))
  · calc A.norm1 (b (k + 1) - b k) ≤ A.norm1 (b (k + 1)) + A.norm1 (b k) :=
          norm1_sub_le hA.norm1_neg h1 _ _
      _ ≤ ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) + ((2 ^ k : ℕ) : ℝ≥0∞) := add_le_add (hb _) (hb _)
      _ ≤ ((2 ^ (k + 2) : ℕ) : ℝ≥0∞) := by
          rw [← Nat.cast_add, Nat.cast_le]
          rw [pow_succ, pow_succ, pow_succ]
          omega

/-- **The partial sums of the blocks converge with the sequence**: if `N₀(u - b_k) → 0`, then
the blocks `g_j` of `b` satisfy `N₀(u - ∑_{j<n} g_j) → 0`, since the partial sum of index `k + 2`
is `b_k`. -/
theorem tendsto_norm0_sub_sum_nearBestBlocks {u : U} {b : ℕ → U}
    (hb : Tendsto (fun k => A.norm0 (u - b k)) atTop (𝓝 0)) :
    Tendsto (fun n => A.norm0 (u - ∑ j ∈ range n, nearBestBlocks b j)) atTop (𝓝 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 2]
  simpa only [sum_range_nearBestBlocks] using hb

/-- **The blocks of near-best approximants**: let the couple be quasi-normed and let
`N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for some `ρ > 0`. If `N₀(u - b_k) ≤ e_k` for every `k`, `e`
decreases and `N₀(u) ≤ e_0`, then the blocks `g_k` of `b` satisfy
`‖(2^(ks) N₀(g_k))_k‖_{ℓ_q} ≤ C_q² 2^(1/ρ) 2^s (1 + 2^s) ‖(2^(ks) e_k)_k‖_{ℓ_q}` for every `s`
and `q`, with `C_q = LpAddConst q`: `N₀(b_{k+1} - b_k) ≤ 2^(1/ρ) e_k`, `N₀(b_0) ≤ 2^(1/ρ) e_0`,
and the shift by two levels costs `C_q` twice. For `q = 0` the left side is `0`. -/
theorem lqNorm_nearBestBlocks_le (hA : A.IsQuasiNormed C) (hρ : 0 < ρ)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) {u : U}
    {b : ℕ → U} {e : ℕ → ℝ≥0∞} (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (he : Antitone e)
    (he0 : A.norm0 u ≤ e 0) (s : ℝ) :
    lqNorm q (fun k => dyadicWeight s k * A.norm0 (nearBestBlocks b k)) ≤
      LpAddConst q ^ 2 * 2 ^ (1 / ρ) * (2 ^ s * (1 + 2 ^ s)) *
        lqNorm q (fun k => dyadicWeight s k * e k) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [ENNReal.lqNorm_zero_left]
  set L := lqNorm q (fun k => dyadicWeight s k * e k)
  set a : ℕ → ℝ≥0∞ := fun k => dyadicWeight s k * A.norm0 (nearBestBlocks b k) with ha
  have hroot : ∀ x y : ℝ≥0∞, x ^ ρ ≤ 2 * y ^ ρ → x ≤ 2 ^ (1 / ρ) * y := fun x y h => by
    have h' := ENNReal.le_two_rpow_mul_of_rpow_le (p := ENNReal.ofReal ρ)
      (ENNReal.ofReal_pos.2 hρ).ne' ENNReal.ofReal_ne_top
      (by rwa [ENNReal.toReal_ofReal hρ.le])
    rwa [ENNReal.toReal_ofReal hρ.le] at h'
  have hb0 : A.norm0 (b 0) ≤ 2 ^ (1 / ρ) * e 0 := by
    refine hroot _ _ ?_
    calc A.norm0 (b 0) ^ ρ = A.norm0 (u - (u - b 0)) ^ ρ := by rw [sub_sub_cancel]
      _ ≤ A.norm0 u ^ ρ + A.norm0 (u - b 0) ^ ρ := norm0_sub_rpow_le hA.norm0_neg h0 _ _
      _ ≤ e 0 ^ ρ + e 0 ^ ρ :=
          add_le_add (ENNReal.rpow_le_rpow he0 hρ.le) (ENNReal.rpow_le_rpow (hbe 0) hρ.le)
      _ = 2 * e 0 ^ ρ := (two_mul _).symm
  have he0L : e 0 ≤ L := by
    simpa using ENNReal.le_lqNorm hq (fun k => dyadicWeight s k * e k) 0
  have ha0 : a 0 = 0 := by simp [ha, nearBestBlocks, hA.norm0_zero]
  have ha1 : a 1 ≤ 2 ^ s * 2 ^ (1 / ρ) * L := by
    calc a 1 = 2 ^ s * A.norm0 (b 0) := by simp [ha, nearBestBlocks, ENNReal.dyadicWeight]
      _ ≤ 2 ^ s * (2 ^ (1 / ρ) * L) := by gcongr; exact hb0.trans (by gcongr)
      _ = 2 ^ s * 2 ^ (1 / ρ) * L := by ring
  have hshift : lqNorm q (fun k => a (k + 1 + 1)) ≤ 2 ^ s * 2 ^ s * 2 ^ (1 / ρ) * L := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun k => ?_
    calc a (k + 1 + 1) = 2 ^ s * (2 ^ s * dyadicWeight s k) * A.norm0 (b (k + 1) - b k) := by
          rw [ha]; dsimp only; rw [ENNReal.dyadicWeight_succ, ENNReal.dyadicWeight_succ]; rfl
      _ ≤ 2 ^ s * (2 ^ s * dyadicWeight s k) * (2 ^ (1 / ρ) * e k) := by
          gcongr
          exact hroot _ _ (norm0_sub_succ_rpow_le_of_nearBest hρ.le hA.norm0_neg h0 hbe he k)
      _ = 2 ^ s * 2 ^ s * 2 ^ (1 / ρ) * (dyadicWeight s k * e k) := by ring
  calc lqNorm q a ≤ LpAddConst q * (a 0 + lqNorm q (fun k => a (k + 1))) :=
        ENNReal.lqNorm_le_head_add_shift' q a
    _ ≤ LpAddConst q * (0 + LpAddConst q * (a 1 + lqNorm q (fun k => a (k + 1 + 1)))) := by
        rw [ha0]
        gcongr
        exact ENNReal.lqNorm_le_head_add_shift' q (fun k => a (k + 1))
    _ ≤ LpAddConst q * (0 + LpAddConst q *
          (2 ^ s * 2 ^ (1 / ρ) * L + 2 ^ s * 2 ^ s * 2 ^ (1 / ρ) * L)) := by
        gcongr
    _ = LpAddConst q ^ 2 * 2 ^ (1 / ρ) * (2 ^ s * (1 + 2 ^ s)) * L := by ring

/-! ### Partial sums of a block decomposition -/

/-- **The partial sums of blocks are approximants**: if `N₁(0) = 0`, `N₁` is subadditive and
`N₁(g_k) ≤ 2^k` for every `k`, then `N₁(∑_{k<n} g_k) ≤ 2^n`, since `∑_{k<n} 2^k < 2^n`
(Mathlib's `Finset.le_sum_of_subadditive` and `Nat.geomSum_lt`). -/
theorem norm1_sum_range_le (h10 : A.norm1 0 = 0)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {g : ℕ → U}
    (hg : ∀ k, A.norm1 (g k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞)) (n : ℕ) :
    A.norm1 (∑ k ∈ range n, g k) ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by
  calc A.norm1 (∑ k ∈ range n, g k) ≤ ∑ k ∈ range n, A.norm1 (g k) :=
        Finset.le_sum_of_subadditive A.norm1 h10.le h1 _ _
    _ ≤ ∑ k ∈ range n, ((2 ^ k : ℕ) : ℝ≥0∞) := Finset.sum_le_sum fun k _ => hg k
    _ ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_sum, Nat.cast_le]
        exact (Nat.geomSum_lt le_rfl fun _ hk => mem_range.1 hk).le

/-- **The tail of a block decomposition in `ρ`-th powers**: let `N₀(0) = 0` and
`N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for some `ρ > 0`. If the partial sums `S_n = ∑_{k<n} g_k`
satisfy `N₀(u - S_n) → 0`, then `N₀(u - S_n)^ρ ≤ ∑_{i ≥ 0} N₀(g_{n+i})^ρ` for every `n`. For
`m ≥ 0`, `u - S_n = (u - S_{n+m}) + ∑_{i<m} g_{n+i}`, the `ρ`-triangle inequality bounds the
finite sum, and `N₀(u - S_{n+m})^ρ → 0`; no completeness is used. -/
theorem norm0_sub_sum_rpow_le_tsum (hρ : 0 < ρ) (h00 : A.norm0 0 = 0)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) {u : U} {g : ℕ → U}
    (hlim : Tendsto (fun n => A.norm0 (u - ∑ k ∈ range n, g k)) atTop (𝓝 0)) (n : ℕ) :
    A.norm0 (u - ∑ k ∈ range n, g k) ^ ρ ≤ ∑' i, A.norm0 (g (n + i)) ^ ρ := by
  set T := ∑' i, A.norm0 (g (n + i)) ^ ρ
  have hsub : ∀ m, A.norm0 (u - ∑ k ∈ range n, g k) ^ ρ ≤
      A.norm0 (u - ∑ k ∈ range (m + n), g k) ^ ρ + T := fun m => by
    have hfin : A.norm0 (∑ i ∈ range m, g (n + i)) ^ ρ ≤
        ∑ i ∈ range m, A.norm0 (g (n + i)) ^ ρ :=
      Finset.le_sum_of_subadditive (fun a => A.norm0 a ^ ρ)
        (by simp [h00, ENNReal.zero_rpow_of_pos hρ]) h0 _ _
    calc A.norm0 (u - ∑ k ∈ range n, g k) ^ ρ
        = A.norm0 ((u - ∑ k ∈ range (m + n), g k) + ∑ i ∈ range m, g (n + i)) ^ ρ := by
          rw [add_comm m n, Finset.sum_range_add]
          congr 2
          abel
      _ ≤ A.norm0 (u - ∑ k ∈ range (m + n), g k) ^ ρ +
          A.norm0 (∑ i ∈ range m, g (n + i)) ^ ρ := h0 _ _
      _ ≤ A.norm0 (u - ∑ k ∈ range (m + n), g k) ^ ρ + T := by
          gcongr
          exact hfin.trans (ENNReal.sum_le_tsum _)
  have hlim' : Tendsto (fun m => A.norm0 (u - ∑ k ∈ range (m + n), g k) ^ ρ + T) atTop
      (𝓝 (0 + T)) := by
    have h := ((ENNReal.continuous_rpow_const (y := ρ)).tendsto (0 : ℝ≥0∞)).comp
      ((Filter.tendsto_add_atTop_iff_nat n).2 hlim)
    rw [ENNReal.zero_rpow_of_pos hρ] at h
    exact h.add_const T
  rw [← zero_add T]
  exact ge_of_tendsto' hlim' hsub

/-! ### The block decomposition quasi-norm -/

variable (A) in
/-- The **block decomposition quasi-norm** of a couple: the infimum of
`‖(2^(ks) N₀(g_k))_k‖_{ℓ_q}` over all sequences `g_k` with `N₁(g_k) ≤ 2^k` whose partial sums
`∑_{k<n} g_k` converge to `u` in `N₀`, written `‖u‖^dec_{s,q}`. The norm `N₃` of DeVore–Popov
(Trans. Amer. Math. Soc. 305 (1988), Theorem 5.1) is the size of the blocks of near-best spline
approximants; the infimum over all block decompositions is equivalent to it
(`InterpCouple.eNormDyadic_le_of_tendsto_sum`, `InterpCouple.exists_blocks_eNormDyadic`). -/
noncomputable def eBlockDecompNorm (s : ℝ) (q : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  ⨅ (g : ℕ → U) (_ : ∀ k, A.norm1 (g k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (_ : Tendsto (fun n => A.norm0 (u - ∑ k ∈ range n, g k)) atTop (𝓝 0)),
    lqNorm q (fun k => dyadicWeight s k * A.norm0 (g k))

/-- Every block decomposition bounds the block decomposition quasi-norm. -/
theorem eBlockDecompNorm_le_of_tendsto {u : U} {g : ℕ → U}
    (hg : ∀ k, A.norm1 (g k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (hlim : Tendsto (fun n => A.norm0 (u - ∑ k ∈ range n, g k)) atTop (𝓝 0)) :
    A.eBlockDecompNorm s q u ≤ lqNorm q (fun k => dyadicWeight s k * A.norm0 (g k)) :=
  iInf₂_le_of_le g hg (iInf_le_of_le hlim le_rfl)

/-- **A block decomposition bounds the dyadic norm**: let the couple be quasi-normed with
subadditive complexity, let `N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for some `ρ > 0`, and let
`q ≠ 0`. For every `s` and every block decomposition `u = lim ∑_{k<n} g_k`,
`‖u‖^dy_{s,q} ≤ 2 H^(1/ρ) ‖(2^(ks) N₀(g_k))_k‖_{ℓ_q}` with `H = hardyConst (sρ) (q/ρ)`: for
`S_n = ∑_{k<n} g_k`, `E(2^n, u) ≤ N₀(u - S_n)`, the tails in `ρ`-th powers, Hardy's inequality
for tails, and `N₀(u) = N₀(u - S_0)`. -/
theorem eNormDyadic_le_of_tendsto_sum (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hρ : 0 < ρ)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) (hq : q ≠ 0) {u : U}
    {g : ℕ → U} (hg : ∀ k, A.norm1 (g k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (hlim : Tendsto (fun n => A.norm0 (u - ∑ k ∈ range n, g k)) atTop (𝓝 0)) :
    A.eNormDyadic s q u ≤ 2 * hardyConst (s * ρ) (q / ENNReal.ofReal ρ) ^ (1 / ρ) *
      lqNorm q (fun k => dyadicWeight s k * A.norm0 (g k)) := by
  set x : ℕ → ℝ≥0∞ := fun n => A.norm0 (u - ∑ k ∈ range n, g k)
  set H := hardyConst (s * ρ) (q / ENNReal.ofReal ρ)
  set M := lqNorm q (fun k => dyadicWeight s k * A.norm0 (g k))
  have htail : ∀ n, x n ^ ρ ≤ 1 * ∑' i, dyadicWeight 0 i * A.norm0 (g (n + i)) ^ ρ :=
    fun n => by
      simpa only [one_mul, ENNReal.dyadicWeight_zero_left] using
        norm0_sub_sum_rpow_le_tsum hρ hA.norm0_zero h0 hlim n
  have hX : lqNorm q (fun n => dyadicWeight s n * x n) ≤ H ^ (1 / ρ) * M := by
    have h := ENNReal.lqNorm_rpow_le_of_rpow_le_tsum (y := fun j => A.norm0 (g j)) hρ htail s q
    rw [one_mul, sub_zero] at h
    have h' := ENNReal.rpow_le_rpow h (one_div_nonneg.2 hρ.le)
    rwa [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hρ.le), one_div,
      ENNReal.rpow_rpow_inv hρ.ne', ENNReal.rpow_rpow_inv hρ.ne', ← one_div] at h'
  have hE : ∀ n, A.eFunctional ((2 ^ n : ℕ) : ℝ≥0∞) u ≤ x n := fun n =>
    eFunctional_le (norm1_sum_range_le hA.norm1_zero h1 hg n)
  have hx0 : A.norm0 u ≤ lqNorm q (fun n => dyadicWeight s n * x n) := by
    simpa [x] using ENNReal.le_lqNorm hq (fun n => dyadicWeight s n * x n) 0
  calc A.eNormDyadic s q u
      = A.norm0 u + lqNorm q (fun k : ℕ => dyadicWeight s k *
          A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := rfl
    _ ≤ lqNorm q (fun n => dyadicWeight s n * x n) + lqNorm q (fun n => dyadicWeight s n * x n) :=
        add_le_add hx0 (ENNReal.lqNorm_mono fun k => by gcongr; exact hE k)
    _ ≤ H ^ (1 / ρ) * M + H ^ (1 / ρ) * M := add_le_add hX hX
    _ = 2 * H ^ (1 / ρ) * M := by ring

/-- **The block decomposition quasi-norm bounds the dyadic norm**: under the hypotheses of
`InterpCouple.eNormDyadic_le_of_tendsto_sum` and `s > 0`,
`‖u‖^dy_{s,q} ≤ 2 H^(1/ρ) ‖u‖^dec_{s,q}` with `H = hardyConst (sρ) (q/ρ)`. The hypothesis
`s > 0` makes `H` finite; for `s ≤ 0` the infimum can vanish while the dyadic norm does not: on
`U = ℝ` with `N₀ = |·|`, `N₁(0) = 0` and `N₁ = 1` off `0`, the blocks `g_k = u/M` for `k < M`
and `g_k = 0` for `k ≥ M` have size `|u|/M` for `s = 0` and `q = ∞`, while
`‖u‖^dy_{s,q} = |u|`. -/
theorem eNormDyadic_le_eBlockDecompNorm (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hρ : 0 < ρ)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) (hs : 0 < s) (hq : q ≠ 0)
    (u : U) :
    A.eNormDyadic s q u ≤
      2 * hardyConst (s * ρ) (q / ENNReal.ofReal ρ) ^ (1 / ρ) * A.eBlockDecompNorm s q u := by
  set K := 2 * hardyConst (s * ρ) (q / ENNReal.ofReal ρ) ^ (1 / ρ)
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg
    (one_div_nonneg.2 hρ.le) (ENNReal.hardyConst_ne_top (mul_pos hs hρ) _))
  have hH : 1 ≤ hardyConst (s * ρ) (q / ENNReal.ofReal ρ) := by
    unfold hardyConst
    split_ifs
    exacts [ENNReal.one_le_one_sub_two_rpow_neg_inv _, ENNReal.one_le_dyadicGeomConst _ _]
  have hK0 : K ≠ 0 := mul_ne_zero two_ne_zero (ENNReal.rpow_pos (zero_lt_one.trans_le hH)
    (ENNReal.hardyConst_ne_top (mul_pos hs hρ) _)).ne'
  rw [eBlockDecompNorm, ENNReal.mul_iInf_of_ne hK0 hK]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne hK0 hK]
  refine le_iInf fun hg => ?_
  rw [ENNReal.mul_iInf_of_ne hK0 hK]
  exact le_iInf fun hlim => eNormDyadic_le_of_tendsto_sum hA h1 hρ h0 hq hg hlim

/-- The constant `C_q² 2^(1/ρ) 2^s (1 + 2^s) · C_q (1 + γ_{1,q})` of the block decompositions
of near-best sequences, with `C_q = LpAddConst q` and `γ_{1,q} = dyadicGeomConst 1 q`: the first
factor is that of `InterpCouple.lqNorm_nearBestBlocks_le`, the second that of the tolerances
(`InterpCouple.lqNorm_dyadicWeight_mul_eFunctional_add_le`). -/
noncomputable def eBlockConst (ρ s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  LpAddConst q ^ 2 * 2 ^ (1 / ρ) * (2 ^ s * (1 + 2 ^ s)) *
    (LpAddConst q * (1 + dyadicGeomConst 1 q))

/-- The constant `eBlockConst ρ s q` is finite. -/
theorem eBlockConst_ne_top (ρ s : ℝ) (q : ℝ≥0∞) : eBlockConst ρ s q ≠ ∞ := by
  have hC : LpAddConst q ≠ ∞ := (ENNReal.LpAddConst_lt_top q).ne
  unfold eBlockConst
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hC)
    (ENNReal.two_rpow_ne_top _)) (ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.two_rpow_ne_top _⟩)))
    (ENNReal.mul_ne_top hC (ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.dyadicGeomConst_ne_top one_pos q⟩))

/-- The constant `eBlockConst ρ s q` is positive: every factor is at least `1` or a power of `2`,
which is positive. -/
theorem eBlockConst_ne_zero (ρ s : ℝ) (q : ℝ≥0∞) : eBlockConst ρ s q ≠ 0 := by
  have hC : LpAddConst q ≠ 0 := (zero_lt_one.trans_le (ENNReal.one_le_LpAddConst q)).ne'
  have h2 : ∀ t : ℝ, (2 : ℝ≥0∞) ^ t ≠ 0 := fun t =>
    (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
  unfold eBlockConst
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hC) (h2 _))
    (mul_ne_zero (h2 _) (add_ne_zero.2 (Or.inl one_ne_zero))))
    (mul_ne_zero hC (add_ne_zero.2 (Or.inl one_ne_zero)))

/-- **Near-best sequences give block decompositions**: let the couple be quasi-normed, let
`N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for some `ρ > 0`, let `s > 0` and `q ≠ 0`. If
`‖u‖^dy_{s,q} < ∞`, there are `b_k` with `N₁(b_k) ≤ 2^k` and `N₀(u - b_k) → 0` whose blocks
satisfy `‖(2^(ks) N₀(g_k))_k‖_{ℓ_q} ≤ eBlockConst ρ s q ‖u‖^dy_{s,q}`: near-best approximants
with the tolerances `e_k = E(2^k, u) + N₀(u) 2^(-k(s+1))`, which tend to `0` for `s > 0`. -/
theorem exists_blocks_eNormDyadic (hA : A.IsQuasiNormed C) (hρ : 0 < ρ)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) (hs : 0 < s) (hq : q ≠ 0)
    {u : U} (hu : A.eNormDyadic s q u ≠ ∞) :
    ∃ b : ℕ → U, (∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞)) ∧
      Tendsto (fun k => A.norm0 (u - b k)) atTop (𝓝 0) ∧
      lqNorm q (fun k => dyadicWeight s k * A.norm0 (nearBestBlocks b k)) ≤
        eBlockConst ρ s q * A.eNormDyadic s q u := by
  obtain ⟨b, hb1, hb0⟩ := exists_nearBest_eFunctional hA.norm1_zero u s
  set e : ℕ → ℝ≥0∞ := fun k =>
    A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u + A.norm0 u * dyadicWeight (-(s + 1)) k
  have he : Antitone e := antitone_eFunctional_add_dyadicWeight (by linarith) u
  have he0 : A.norm0 u ≤ e 0 := by simp [e]
  have hL : lqNorm q (fun k => dyadicWeight s k * e k) ≤
      LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q u :=
    lqNorm_dyadicWeight_mul_eFunctional_add_le A s q u
  have hLfin : lqNorm q (fun k => dyadicWeight s k * e k) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.LpAddConst_lt_top q).ne (ENNReal.add_ne_top.2
        ⟨ENNReal.one_ne_top, ENNReal.dyadicGeomConst_ne_top one_pos q⟩)) hu) hL
  refine ⟨b, hb1, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_zero_of_lqNorm_dyadicWeight_ne_top hq hs hLfin) (fun _ => zero_le) hb0
  · calc lqNorm q (fun k => dyadicWeight s k * A.norm0 (nearBestBlocks b k))
        ≤ LpAddConst q ^ 2 * 2 ^ (1 / ρ) * (2 ^ s * (1 + 2 ^ s)) *
            lqNorm q (fun k => dyadicWeight s k * e k) :=
          lqNorm_nearBestBlocks_le hA hρ h0 hb0 he he0 s
      _ ≤ LpAddConst q ^ 2 * 2 ^ (1 / ρ) * (2 ^ s * (1 + 2 ^ s)) *
            (LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q u) := by gcongr
      _ = eBlockConst ρ s q * A.eNormDyadic s q u := by unfold eBlockConst; ring

/-- **The dyadic norm bounds the block decomposition quasi-norm**: for a quasi-normed couple
with subadditive complexity, `N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for some `ρ > 0`, `s > 0` and
`q ≠ 0`, `‖u‖^dec_{s,q} ≤ eBlockConst ρ s q ‖u‖^dy_{s,q}`, from the blocks of near-best
approximants (`InterpCouple.exists_blocks_eNormDyadic`). -/
theorem eBlockDecompNorm_le_eNormDyadic (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hρ : 0 < ρ)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) (hs : 0 < s) (hq : q ≠ 0)
    (u : U) :
    A.eBlockDecompNorm s q u ≤ eBlockConst ρ s q * A.eNormDyadic s q u := by
  rcases eq_or_ne (A.eNormDyadic s q u) ∞ with hu | hu
  · rw [hu, ENNReal.mul_top (eBlockConst_ne_zero ρ s q)]
    exact le_top
  obtain ⟨b, hb1, hblim, hbound⟩ := exists_blocks_eNormDyadic hA hρ h0 hs hq hu
  exact (eBlockDecompNorm_le_of_tendsto (norm1_nearBestBlocks_le hA h1 hb1)
    (tendsto_norm0_sub_sum_nearBestBlocks hblim)).trans hbound

/-- **Block decompositions characterise `E_{s,q}`** (DeVore–Popov, Trans. Amer. Math. Soc. 305
(1988), Theorem 5.1): for a quasi-normed couple with subadditive complexity,
`N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for some `ρ > 0`, `s > 0` and `q ≠ 0`,
`‖u‖^dy_{s,q} < ∞` if and only if `u` has a block decomposition of finite size. -/
theorem eNormDyadic_lt_top_iff_eBlockDecompNorm_lt_top (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hρ : 0 < ρ)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ) (hs : 0 < s) (hq : q ≠ 0)
    (u : U) :
    A.eNormDyadic s q u < ∞ ↔ A.eBlockDecompNorm s q u < ∞ := by
  constructor
  · exact fun hu => (eBlockDecompNorm_le_eNormDyadic hA h1 hρ h0 hs hq u).trans_lt
      (ENNReal.mul_lt_top (eBlockConst_ne_top ρ s q).lt_top hu)
  · refine fun hu => (eNormDyadic_le_eBlockDecompNorm hA h1 hρ h0 hs hq u).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ?_) hu)
    exact (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 hρ.le)
      (ENNReal.hardyConst_ne_top (mul_pos hs hρ) _)).lt_top

end InterpCouple
