/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Error
public import ApproximationSpaces.Sequences.Lq

/-!
# The approximation spaces `A^s_q`

For an approximation scheme `A` in `X`, a smoothness `s` and a fine index `1 ≤ q ≤ ∞`,
Pietsch's **approximation space** `A^s_q` consists of the `f ∈ X` with

`‖f‖_{A^s_q} = ‖ (n^(s - 1/q) E_{n-1}(f))_{n ≥ 1} ‖_{ℓ_q} < ∞`.

In Lean the sequence is indexed from `0` as `((n + 1)^(s - 1/q) E_n(f))_{n ≥ 0}`, the
quasi-norm is `A.approxNorm s q f`, and membership is `A.MemApprox s q f`.  For `q = ∞` the
exponent is `s` (in Lean `1 / ∞.toReal = 1 / 0 = 0`), so `‖f‖_{A^s_∞} = sup (n+1)^s E_n(f)`.

**Design.** The quasi-norm takes values in `ℝ≥0∞` and is defined for every `f`; membership is
finiteness, as for `MeasureTheory.eLpNorm` and `MeasureTheory.MemLp`.  The spaces are only
quasi-normed (the triangle inequality holds up to a constant), and Mathlib has no class for
quasi-normed spaces, so no new normed type is introduced.  The linear structure is recorded
separately as a `Submodule` (`ApproximationScheme.approxSpace`).

The errors enter through `approxSeq f n = E_n(f)` as an element of `ℝ≥0∞`.  This file holds
the definition and the facts that follow directly from the calculus of `E_n`: homogeneity,
`‖f‖ ≤ ‖f‖_{A^s_q}` (because `E_0(f) = ‖f‖`), definiteness, and comparison of schemes.
Everything else is proved for the equivalent dyadic quasi-norm of
`ApproximationSpaces.Dyadic`.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (A : ApproximationScheme X)

/-- The errors `E_n(f)` as a sequence in `ℝ≥0∞`. -/
noncomputable def approxSeq (f : X) (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (A.approxError n f)

variable {A}

/-- The errors decrease: `E_n(f) ≤ E_m(f)` for `m ≤ n`. -/
theorem approxSeq_anti (f : X) : Antitone (A.approxSeq f) := fun _ _ h =>
  ENNReal.ofReal_le_ofReal (approxError_anti f h)

/-- `E_0(f) = ‖f‖`. -/
@[simp]
theorem approxSeq_zero_left (f : X) : A.approxSeq f 0 = ‖f‖ₑ := by
  simp [approxSeq]

/-- `E_n(0) = 0`. -/
@[simp]
theorem approxSeq_zero_right (n : ℕ) : A.approxSeq 0 n = 0 := by simp [approxSeq]

/-- `E_n(f) ≤ ‖f‖`. -/
theorem approxSeq_le_enorm (f : X) (n : ℕ) : A.approxSeq f n ≤ ‖f‖ₑ := by
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (approxError_le_norm n f)

/-- The errors are finite. -/
theorem approxSeq_ne_top (f : X) (n : ℕ) : A.approxSeq f n ≠ ∞ := ENNReal.ofReal_ne_top

/-- `E_n(f) ≤ ‖f - a‖` for `a ∈ A_n`. -/
theorem approxSeq_le_of_mem {n : ℕ} {a : X} (ha : a ∈ A n) (f : X) :
    A.approxSeq f n ≤ ‖f - a‖ₑ := by
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (approxError_le_norm_sub ha f)

/-- `E_n(f) = 0` for `f ∈ A_n`. -/
theorem approxSeq_eq_zero_of_mem {n : ℕ} {f : X} (hf : f ∈ A n) : A.approxSeq f n = 0 := by
  simp [approxSeq, approxError_eq_zero_of_mem hf]

/-- `E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`. -/
theorem approxSeq_add_le (m n : ℕ) (f g : X) :
    A.approxSeq (f + g) (m + n) ≤ A.approxSeq f m + A.approxSeq g n := by
  rw [approxSeq, approxSeq, approxSeq, ← ENNReal.ofReal_add (approxError_nonneg _ _)
    (approxError_nonneg _ _)]
  exact ENNReal.ofReal_le_ofReal (approxError_add_le m n f g)

/-- `E_{2^(k+1)}(f + g) ≤ E_{2^k}(f) + E_{2^k}(g)`. -/
theorem approxSeq_add_le_pow_succ (k : ℕ) (f g : X) :
    A.approxSeq (f + g) (2 ^ (k + 1)) ≤ A.approxSeq f (2 ^ k) + A.approxSeq g (2 ^ k) := by
  have := approxSeq_add_le (A := A) (2 ^ k) (2 ^ k) f g
  rwa [← two_mul, ← pow_succ'] at this

/-- `E_n(c f) = |c| E_n(f)`. -/
theorem approxSeq_smul (c : ℝ) (f : X) (n : ℕ) :
    A.approxSeq (c • f) n = ‖c‖ₑ * A.approxSeq f n := by
  rw [approxSeq, approxSeq, approxError_smul, ENNReal.ofReal_mul (abs_nonneg c),
    Real.enorm_eq_ofReal_abs]

/-- `E_n(-f) = E_n(f)`. -/
@[simp]
theorem approxSeq_neg (f : X) (n : ℕ) : A.approxSeq (-f) n = A.approxSeq f n := by
  simp [approxSeq]

/-- Larger approximating sets give smaller errors. -/
theorem approxSeq_anti_scheme {A' : ApproximationScheme X} (h : ∀ n, A n ⊆ A' n) (f : X)
    (n : ℕ) : A'.approxSeq f n ≤ A.approxSeq f n :=
  ENNReal.ofReal_le_ofReal (approxError_anti_scheme h n f)

variable (A)

/-- **Pietsch's quasi-norm** of `A^s_q`: the `ℓ_q` norm of `((n + 1)^(s - 1/q) E_n(f))_n`. -/
noncomputable def approxNorm (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ENNReal.lqNorm q (fun n => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * A.approxSeq f n)

/-- `f` belongs to the **approximation space** `A^s_q`: its quasi-norm is finite. -/
def MemApprox (s : ℝ) (q : ℝ≥0∞) (f : X) : Prop := A.approxNorm s q f < ∞

variable {A} {s : ℝ} {q : ℝ≥0∞}

/-- `f ∈ A^s_q` iff its quasi-norm is finite. -/
theorem memApprox_iff {f : X} : A.MemApprox s q f ↔ A.approxNorm s q f < ∞ := Iff.rfl

/-- The quasi-norm of an element of `A^s_q` is finite. -/
theorem MemApprox.approxNorm_ne_top {f : X} (hf : A.MemApprox s q f) : A.approxNorm s q f ≠ ∞ :=
  hf.ne

/-- For `q = ∞` the quasi-norm is `sup_n (n + 1)^s E_n(f)`. -/
theorem approxNorm_top (s : ℝ) (f : X) :
    A.approxNorm s ∞ f = ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * A.approxSeq f n := by
  simp [approxNorm, ENNReal.lqNorm_top]

/-- For `q < ∞` the `q`-th power of the quasi-norm is `∑ₙ (n + 1)^(sq - 1) E_n(f)^q`. -/
theorem approxNorm_rpow (hq0 : q ≠ 0) (hq : q ≠ ∞) (s : ℝ) (f : X) :
    A.approxNorm s q f ^ q.toReal =
      ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * q.toReal - 1) * A.approxSeq f n ^ q.toReal := by
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [approxNorm, ENNReal.lqNorm_rpow hq0 hq]
  congr 1; funext n
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul]
  congr 2
  field_simp

/-- `‖0‖_{A^s_q} = 0`. -/
@[simp]
theorem approxNorm_zero (s : ℝ) (q : ℝ≥0∞) : A.approxNorm s q 0 = 0 := by
  simp [approxNorm]

/-- `0 ∈ A^s_q`. -/
theorem memApprox_zero (s : ℝ) (q : ℝ≥0∞) : A.MemApprox s q 0 := by
  simp [MemApprox]

/-- **Homogeneity**: `‖c f‖_{A^s_q} = |c| ‖f‖_{A^s_q}`. -/
theorem approxNorm_smul (c : ℝ) (f : X) :
    A.approxNorm s q (c • f) = ‖c‖ₑ * A.approxNorm s q f := by
  simp_rw [approxNorm, approxSeq_smul, mul_left_comm _ ‖c‖ₑ]
  exact ENNReal.lqNorm_const_mul _ _

/-- `A^s_q` is closed under real multiples. -/
theorem MemApprox.smul {f : X} (hf : A.MemApprox s q f) (c : ℝ) : A.MemApprox s q (c • f) := by
  rw [MemApprox, approxNorm_smul]
  exact ENNReal.mul_lt_top enorm_lt_top hf

/-- `A^s_q` is closed under negation. -/
theorem MemApprox.neg {f : X} (hf : A.MemApprox s q f) : A.MemApprox s q (-f) := by
  simpa using hf.smul (-1)

/-- **The embedding `A^s_q ↪ X`**: `‖f‖ ≤ ‖f‖_{A^s_q}`, from the term `E_0(f) = ‖f‖`. -/
theorem enorm_le_approxNorm (hq : 1 ≤ q) (f : X) : ‖f‖ₑ ≤ A.approxNorm s q f := by
  have := ENNReal.le_lqNorm (a := fun n => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) *
    A.approxSeq f n) (zero_lt_one.trans_le hq).ne' 0
  simp only [zero_add, Nat.cast_one, ENNReal.one_rpow, one_mul, approxSeq_zero_left] at this
  exact this

/-- For `q ≥ 1`, `‖f‖_{A^s_q} = 0` only for `f = 0`. -/
theorem approxNorm_eq_zero_iff (hq : 1 ≤ q) {f : X} : A.approxNorm s q f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ approxNorm_zero s q⟩
  have := enorm_le_approxNorm (A := A) (s := s) hq f
  rw [h, nonpos_iff_eq_zero, enorm_eq_zero] at this
  exact this

/-- A scheme with larger sets has smaller quasi-norms, hence larger approximation spaces. -/
theorem approxNorm_anti_scheme {A' : ApproximationScheme X} (h : ∀ n, A n ⊆ A' n) (f : X) :
    A'.approxNorm s q f ≤ A.approxNorm s q f :=
  ENNReal.lqNorm_mono fun n => by gcongr; exact approxSeq_anti_scheme h f n

/-- A scheme with larger sets has larger approximation spaces. -/
theorem MemApprox.of_subset_scheme {A' : ApproximationScheme X} (h : ∀ n, A n ⊆ A' n) {f : X}
    (hf : A.MemApprox s q f) : A'.MemApprox s q f :=
  (approxNorm_anti_scheme h f).trans_lt hf

end ApproximationScheme
