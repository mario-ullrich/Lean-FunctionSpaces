/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Dyadic

/-!
# The linear structure of `A^s_q`

For `s ≥ 0` and `0 < q ≤ ∞` the approximation space `A^s_q` is a linear subspace of `X`, and
its dyadic quasi-norm satisfies the **quasi-triangle inequality**

`‖f + g‖^dy_{A^s_q} ≤ C (‖f‖^dy_{A^s_q} + ‖g‖^dy_{A^s_q})`;

for `1 ≤ q ≤ ∞` so does Pietsch's quasi-norm `‖·‖_{A^s_q}`.

The reason is `E_{2n}(f + g) ≤ E_n(f) + E_n(g)`: in the dyadic form, the errors of `f + g` at
`2^(k+1)` are controlled by those of `f` and `g` at `2^k`, at the cost of the factor `2^s`. For
the dyadic quasi-norm the constant is `C_q (2 + 2^s C_q)` for every `q` and `s`
(`approxNormDyadic_add_le'`), where `C_q = LpAddConst q` is Mathlib's constant of the
quasi-triangle inequality in `ℓ_q`, `2^(1/q - 1)` for `0 < q < 1` and `1` otherwise. For
`1 ≤ q ≤ ∞` and `s ≥ 0` the constants are `2 · 2^s` for the dyadic quasi-norm
(`approxNormDyadic_add_le`) and `8 · (2^s)^3` for Pietsch's (`approxNorm_add_le`); these
constants are not optimised.

`ApproximationScheme.approxSpace A s q hs hq0` is `A^s_q` as a `Submodule ℝ X`.  A `Submodule`
must carry the proof that it is closed under addition, which is proved here for `s ≥ 0` and
`q ≠ 0`; hence the two hypotheses are arguments of the definition.  The approximants themselves
lie in every `A^s_q` (`memApprox_of_mem`), and for `s > 0` the space lies in the closure of
`⋃ A n`.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight LpAddConst)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

/-- The dyadic sequence of `f + g` at `k + 1` is controlled by those of `f` and `g` at `k`. -/
theorem approxSeqDyadic_add_le_succ (f g : X) (k : ℕ) :
    A.approxSeqDyadic s (f + g) (k + 1) ≤
      2 ^ s * (A.approxSeqDyadic s f k + A.approxSeqDyadic s g k) := by
  rw [approxSeqDyadic, ENNReal.dyadicWeight_succ, mul_assoc, approxSeqDyadic, approxSeqDyadic,
    ← mul_add]
  gcongr
  exact approxError_add_le_pow_succ k f g

/-- **Quasi-triangle inequality** for the dyadic quasi-norm, for every fine index `q` and every
`s`: `‖f + g‖^dy_{A^s_q} ≤ C_q (2 + 2^s C_q) (‖f‖^dy_{A^s_q} + ‖g‖^dy_{A^s_q})`, with Mathlib's
constant `C_q = LpAddConst q` of the quasi-triangle inequality in `ℓ_q` (`2^(1/q - 1)` for
`0 < q < 1`, `1` otherwise). The dyadic sequence of `f + g` shifted by one level is controlled by
those of `f` and `g` (`approxSeqDyadic_add_le_succ`); splitting off its first term
(`ENNReal.lqNorm_le_head_add_shift'`) and adding the two sequences
(`ENNReal.lqNorm_add_le'`) cost a factor `C_q` each. -/
theorem approxNormDyadic_add_le' (f g : X) :
    A.approxNormDyadic s q (f + g) ≤ LpAddConst q * (2 + 2 ^ s * LpAddConst q) *
      (A.approxNormDyadic s q f + A.approxNormDyadic s q g) := by
  set Cq := LpAddConst q
  set D := lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g) with hD
  have hCq : 1 ≤ Cq := ENNReal.one_le_LpAddConst q
  have hfg : ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ := eNorm_add_le f g
  have hx0 : A.approxSeqDyadic s (f + g) 0 ≤ ‖f‖ₑ + ‖g‖ₑ := by
    rw [approxSeqDyadic_zero]
    exact (approxError_le_enorm _ 1).trans hfg
  have hshift : lqNorm q (fun k => A.approxSeqDyadic s (f + g) (k + 1)) ≤ 2 ^ s * (Cq * D) := by
    calc lqNorm q (fun k => A.approxSeqDyadic s (f + g) (k + 1))
        ≤ lqNorm q (fun k => 2 ^ s * (A.approxSeqDyadic s f k + A.approxSeqDyadic s g k)) :=
          ENNReal.lqNorm_mono fun k => approxSeqDyadic_add_le_succ f g k
      _ ≤ 2 ^ s * (Cq * D) := by
          rw [ENNReal.lqNorm_const_mul]
          gcongr
          exact ENNReal.lqNorm_add_le' q _ _
  calc A.approxNormDyadic s q (f + g) = ‖f + g‖ₑ + lqNorm q (A.approxSeqDyadic s (f + g)) := rfl
    _ ≤ Cq * (‖f‖ₑ + ‖g‖ₑ) + Cq * ((‖f‖ₑ + ‖g‖ₑ) + 2 ^ s * (Cq * D)) := by
        gcongr
        · exact hfg.trans (le_mul_of_one_le_left' hCq)
        · exact (ENNReal.lqNorm_le_head_add_shift' q _).trans (by gcongr)
    _ = Cq * (2 * (‖f‖ₑ + ‖g‖ₑ) + 2 ^ s * Cq * D) := by ring
    _ ≤ Cq * ((2 + 2 ^ s * Cq) * (‖f‖ₑ + ‖g‖ₑ) + (2 + 2 ^ s * Cq) * D) := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = Cq * (2 + 2 ^ s * Cq) * (A.approxNormDyadic s q f + A.approxNormDyadic s q g) := by
        simp only [hD, approxNormDyadic]; ring

/-- **Quasi-triangle inequality** for the dyadic quasi-norm, with constant `2 · 2^s`, for
`1 ≤ q ≤ ∞` and `s ≥ 0`; for `s < 1` this constant is smaller than the constant `2 + 2^s` of
`ApproximationScheme.approxNormDyadic_add_le'` at `q ≥ 1`. -/
theorem approxNormDyadic_add_le (hq : 1 ≤ q) (hs : 0 ≤ s) (f g : X) :
    A.approxNormDyadic s q (f + g) ≤
      2 * 2 ^ s * (A.approxNormDyadic s q f + A.approxNormDyadic s q g) := by
  have h2s := ENNReal.one_le_two_rpow hs
  have hfg : ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ := eNorm_add_le f g
  have hD : lqNorm q (A.approxSeqDyadic s (f + g)) ≤ (‖f‖ₑ + ‖g‖ₑ) +
      2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g)) := by
    refine (ENNReal.lqNorm_le_head_add_shift hq _).trans (add_le_add ?_ ?_)
    · rw [approxSeqDyadic_zero]; exact (approxError_le_enorm _ 1).trans hfg
    · calc lqNorm q (fun k => A.approxSeqDyadic s (f + g) (k + 1))
          ≤ lqNorm q (fun k => 2 ^ s * (A.approxSeqDyadic s f k + A.approxSeqDyadic s g k)) :=
            ENNReal.lqNorm_mono fun k => approxSeqDyadic_add_le_succ f g k
        _ = 2 ^ s * lqNorm q (fun k => A.approxSeqDyadic s f k + A.approxSeqDyadic s g k) :=
            ENNReal.lqNorm_const_mul _ _
        _ ≤ _ := by gcongr; exact ENNReal.lqNorm_add_le hq _ _
  calc A.approxNormDyadic s q (f + g) = ‖f + g‖ₑ + lqNorm q (A.approxSeqDyadic s (f + g)) := rfl
    _ ≤ (‖f‖ₑ + ‖g‖ₑ) + ((‖f‖ₑ + ‖g‖ₑ) +
          2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g))) :=
        add_le_add hfg hD
    _ = 2 * (‖f‖ₑ + ‖g‖ₑ) +
          2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g)) := by ring
    _ ≤ 2 * 2 ^ s * (‖f‖ₑ + ‖g‖ₑ) +
          2 * 2 ^ s * (lqNorm q (A.approxSeqDyadic s f) + lqNorm q (A.approxSeqDyadic s g)) := by
        gcongr
        · exact le_mul_of_one_le_right' h2s
        · exact le_mul_of_one_le_left' one_le_two
    _ = 2 * 2 ^ s * (A.approxNormDyadic s q f + A.approxNormDyadic s q g) := by
        simp only [approxNormDyadic]; ring

/-- **Quasi-triangle inequality** for Pietsch's quasi-norm, with the (not optimised) constant
`8 · (2^s)^3`, obtained through the dyadic quasi-norm. -/
theorem approxNorm_add_le (hq : 1 ≤ q) (hs : 0 ≤ s) (f g : X) :
    A.approxNorm s q (f + g) ≤ 8 * (2 ^ s) ^ 3 * (A.approxNorm s q f + A.approxNorm s q g) := by
  calc A.approxNorm s q (f + g) ≤ 2 ^ s * A.approxNormDyadic s q (f + g) :=
        approxNorm_le_approxNormDyadic hq hs _
    _ ≤ 2 ^ s * (2 * 2 ^ s * (A.approxNormDyadic s q f + A.approxNormDyadic s q g)) := by
        gcongr; exact approxNormDyadic_add_le hq hs f g
    _ ≤ 2 ^ s * (2 * 2 ^ s * (4 * 2 ^ s * A.approxNorm s q f + 4 * 2 ^ s * A.approxNorm s q g)) := by
        gcongr <;> exact approxNormDyadic_le_approxNorm hq hs _
    _ = 8 * (2 ^ s) ^ 3 * (A.approxNorm s q f + A.approxNorm s q g) := by ring

/-- For `s ≥ 0` and `0 < q ≤ ∞`, `A^s_q` is closed under addition: the dyadic quasi-norm of `f + g`
is finite by its quasi-triangle inequality (`approxNormDyadic_add_le'`), and the dyadic
quasi-norm is finite exactly on `A^s_q` (`memApprox_iff_approxNormDyadic_lt_top'`). -/
theorem MemApprox.add (hq0 : q ≠ 0) (hs : 0 ≤ s) {f g : X} (hf : A.MemApprox s q f)
    (hg : A.MemApprox s q g) : A.MemApprox s q (f + g) := by
  rw [memApprox_iff_approxNormDyadic_lt_top' hq0 hs] at hf hg ⊢
  have hC : LpAddConst q < ∞ := ENNReal.LpAddConst_lt_top q
  exact (approxNormDyadic_add_le' f g).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC
    (ENNReal.add_lt_top.2 ⟨by norm_num, ENNReal.mul_lt_top (ENNReal.two_rpow_ne_top s).lt_top hC⟩))
    (ENNReal.add_lt_top.2 ⟨hf, hg⟩))

/-- For `s ≥ 0` and `0 < q ≤ ∞`, `A^s_q` is closed under subtraction. -/
theorem MemApprox.sub (hq0 : q ≠ 0) (hs : 0 ≤ s) {f g : X} (hf : A.MemApprox s q f)
    (hg : A.MemApprox s q g) : A.MemApprox s q (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hq0 hs hg.neg

/-- For `s ≥ 0` and `0 < q ≤ ∞`, `A^s_q` is closed under finite sums. -/
theorem MemApprox.sum (hq0 : q ≠ 0) (hs : 0 ≤ s) {ι : Type*} (t : Finset ι) {f : ι → X}
    (hf : ∀ i ∈ t, A.MemApprox s q (f i)) : A.MemApprox s q (∑ i ∈ t, f i) :=
  Finset.sum_induction f (A.MemApprox s q) (fun _ _ ha hb => ha.add hq0 hs hb)
    (memApprox_zero s q) hf

/-- **Approximants lie in every approximation space**, for `s ≥ 0` and `0 < q ≤ ∞`: an element
`a` of `A m` has `E_{2^k}(a) = 0` for `2^k ≥ m`, so its dyadic sequence has only finitely many
nonzero terms, each finite, and lies in every `ℓ_q` (`ENNReal.lqNorm_lt_top_of_eq_zero`). -/
theorem memApprox_of_mem (hq0 : q ≠ 0) (hs : 0 ≤ s) {m : ℕ} {a : X} (ha : a ∈ A m) :
    A.MemApprox s q a := by
  rw [memApprox_iff_lqNorm_dyadic_lt_top' hq0 hs]
  refine ENNReal.lqNorm_lt_top_of_eq_zero (Finset.range m) (fun k hk => ?_) fun k _ =>
    ENNReal.mul_ne_top (ENNReal.dyadicWeight_ne_top s k) (approxError_ne_top a _)
  have hmk : m ≤ 2 ^ k :=
    (not_lt.1 (Finset.mem_range.not.1 hk)).trans (Nat.lt_two_pow_self).le
  rw [approxSeqDyadic, approxError_eq_zero_of_mem (A.mono hmk ha), mul_zero]

variable (A)

/-- The **approximation space** `A^s_q` as a real subspace of `X`, for `s ≥ 0` and
`0 < q ≤ ∞`. -/
def approxSpace (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq0 : q ≠ 0) : Submodule ℝ X where
  carrier := {f | A.MemApprox s q f}
  zero_mem' := memApprox_zero s q
  add_mem' hf hg := MemApprox.add hq0 hs hf hg
  smul_mem' c _ hf := MemApprox.smul hf c

variable {A}

/-- Membership in the approximation space as a submodule. -/
@[simp]
theorem mem_approxSpace {hs : 0 ≤ s} {hq0 : q ≠ 0} {f : X} :
    f ∈ A.approxSpace s q hs hq0 ↔ A.MemApprox s q f := Iff.rfl

/-- `⋃ A n ⊆ A^s_q`, for `s ≥ 0` and `0 < q ≤ ∞`. -/
theorem iUnion_subset_approxSpace (hs : 0 ≤ s) (hq0 : q ≠ 0) :
    (⋃ n, A n) ⊆ A.approxSpace s q hs hq0 := fun _ hf =>
  let ⟨_, hn⟩ := Set.mem_iUnion.1 hf
  memApprox_of_mem hq0 hs hn

/-- For `s > 0` and `0 < q ≤ ∞`, `A^s_q` lies in the closure of `⋃ A n`. -/
theorem approxSpace_subset_closure (hs : 0 < s) (hq0 : q ≠ 0) :
    (A.approxSpace s q hs.le hq0 : Set X) ⊆ closure (⋃ n, A n) := fun _ hf =>
  mem_closure_iUnion_of_memApprox hq0 hs hf

end ApproximationScheme
