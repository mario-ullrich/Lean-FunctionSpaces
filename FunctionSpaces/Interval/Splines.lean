/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.PiecewisePoly
public import FunctionSpaces.Interval.BSpline
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Dyadic splines on `[0, 1]`

A **spline of order `r`** on the dyadic grid of level `k` is a piecewise polynomial of degree
`< r` on the intervals `I_{k,n}` whose consecutive pieces differ by a multiple of `(x - ξ)^(r-1)`
at every interior knot `ξ = n 2^(-k)` (`Interval.SplineJoins`). For polynomials of degree `< r`
this is the same as agreeing to order `r - 2` at `ξ` (`Interval.exists_eq_C_mul_pow_iff`), so the
splines of order `r` are the `C^(r-2)` piecewise polynomials; for `r = 1` they are the step
functions, for `r = 2` the continuous piecewise linear functions. The jump form is what the inverse
inequality uses: across a knot a spline is a polynomial plus `c (x - ξ)_+^(r-1)`.

The classes of splines in `L_p[0, 1]` form subspaces `S_k` increasing in `k`
(`Interval.splineSpace`), and the scheme `Interval.splineScheme` has them as approximants of
complexity `2^k`. The B-splines `N_r(2^k x - n)` (`Interval.bsplinePieces`) have spline joins
(`Interval.splineJoins_bsplinePieces`), so their combinations are splines.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

/-- **Splines in jump form are `C^(r-2)`**: a polynomial `P` of degree `< r` is a multiple of
`(X - ξ)^(r-1)` iff `P` and its derivatives up to order `r - 2` vanish at `ξ`. -/
theorem exists_eq_C_mul_pow_iff {r : ℕ} (hr : 1 ≤ r) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r)
    (ξ : ℂ) :
    (∃ c, P = C c * (X - C ξ) ^ (r - 1)) ↔ ∀ i < r - 1, (derivative^[i] P).eval ξ = 0 := by
  constructor
  · rintro ⟨c, rfl⟩ i hi
    rw [iterate_derivative_C_mul, iterate_derivative_X_sub_pow]
    simp [Nat.sub_ne_zero_of_lt hi]
  · intro h
    rcases eq_or_ne P 0 with rfl | hP0
    · exact ⟨0, by simp⟩
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · -- `r = 1`: polynomials of degree `< 1` are constants
      have h1 : r = 1 := by omega
      subst h1
      refine ⟨P.coeff 0, ?_⟩
      rw [Nat.sub_self, pow_zero, mul_one]
      exact eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.1 (mem_degreeLT.1 hP))
    · have hroot : r - 2 < P.rootMultiplicity ξ :=
        lt_rootMultiplicity_of_isRoot_iterate_derivative hP0 fun m hm => h m (by omega)
      obtain ⟨Q, hQ⟩ := (pow_dvd_pow (X - C ξ) (by omega : r - 1 ≤ P.rootMultiplicity ξ)).trans
        (pow_rootMultiplicity_dvd P ξ)
      have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ; exact hP0 hQ
      have hdeg : P.natDegree < r :=
        (natDegree_lt_iff_degree_lt hP0).2 (mem_degreeLT.1 hP)
      rw [hQ, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero ξ)) hQ0, natDegree_pow,
        natDegree_X_sub_C, mul_one] at hdeg
      refine ⟨Q.coeff 0, ?_⟩
      rw [hQ, eq_C_of_natDegree_eq_zero (by omega : Q.natDegree = 0), mul_comm, coeff_C_zero]

/-- The pieces `Q` have **spline joins of order `r`** at the interior knots of level `k`: at
`ξ = n 2^(-k)`, `0 < n < 2^k`, consecutive pieces differ by a multiple of `(x - ξ)^(r-1)`. -/
def SplineJoins (r k : ℕ) (Q : ℕ → ℂ[X]) : Prop :=
  ∀ n, 0 < n → n < 2 ^ k → ∃ c : ℂ,
    Q n - Q (n - 1) = C c * (X - C ((((n : ℝ) / 2 ^ k : ℝ)) : ℂ)) ^ (r - 1)

/-- The zero pieces have spline joins. -/
theorem splineJoins_zero (r k : ℕ) : SplineJoins r k 0 := fun _ _ _ => ⟨0, by simp⟩

/-- Spline joins are preserved by sums. -/
theorem SplineJoins.add {r k : ℕ} {Q Q' : ℕ → ℂ[X]} (h : SplineJoins r k Q)
    (h' : SplineJoins r k Q') : SplineJoins r k (Q + Q') := fun n hn hnk => by
  obtain ⟨c, hc⟩ := h n hn hnk
  obtain ⟨c', hc'⟩ := h' n hn hnk
  refine ⟨c + c', ?_⟩
  simp only [Pi.add_apply]
  rw [show Q n + Q' n - (Q (n - 1) + Q' (n - 1)) = (Q n - Q (n - 1)) + (Q' n - Q' (n - 1)) by
    ring, hc, hc', C_add]
  ring

/-- Spline joins are preserved by constant multiples. -/
theorem SplineJoins.const_mul {r k : ℕ} {Q : ℕ → ℂ[X]} (h : SplineJoins r k Q) (a : ℂ) :
    SplineJoins r k (fun n => C a * Q n) := fun n hn hnk => by
  obtain ⟨c, hc⟩ := h n hn hnk
  refine ⟨a * c, ?_⟩
  rw [← mul_sub, hc, C_mul]
  ring

/-- Spline joins are preserved by finite sums. -/
theorem SplineJoins.sum {r k : ℕ} {ι : Type*} (s : Finset ι) {Q : ι → ℕ → ℂ[X]}
    (h : ∀ i ∈ s, SplineJoins r k (Q i)) : SplineJoins r k (∑ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using splineJoins_zero r k
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Spline joins of level `k` are spline joins of level `k + 1`: the new knots lie inside the
pieces, where the jump is `0`. -/
theorem SplineJoins.refine {r k : ℕ} {Q : ℕ → ℂ[X]} (h : SplineJoins r k Q) :
    SplineJoins r (k + 1) (fun m => Q (m / 2)) := fun m hm hmk => by
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · have hn : 0 < n := by omega
    have hnk : n < 2 ^ k := by rw [pow_succ] at hmk; omega
    obtain ⟨c, hc⟩ := h n hn hnk
    refine ⟨c, ?_⟩
    simp only
    rw [show 2 * n / 2 = n by omega, show (2 * n - 1) / 2 = n - 1 by omega, hc]
    congr 4
    push_cast
    rw [pow_succ]
    field_simp
  · refine ⟨0, ?_⟩
    simp only
    rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1 - 1) / 2 = n by omega]
    simp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The space `S_k` of **splines of order `r`** on the dyadic grid of level `k` in `L_p[0, 1]`:
the classes of piecewise polynomials of level `k` and degree `< r` with spline joins. -/
noncomputable def splineSpace (r k : ℕ) : Submodule ℝ (Lp ℂ p unitVol) where
  carrier := {g | ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ SplineJoins r k Q ∧
    (g : ℝ → ℂ) =ᵐ[unitVol] ppFun k Q}
  add_mem' := by
    rintro g g' ⟨Q, hQ, hj, hg⟩ ⟨Q', hQ', hj', hg'⟩
    refine ⟨Q + Q', fun n => Submodule.add_mem _ (hQ n) (hQ' n), hj.add hj', ?_⟩
    filter_upwards [Lp.coeFn_add g g', hg, hg'] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ppFun_add, Pi.add_apply]
  zero_mem' := ⟨0, fun n => Submodule.zero_mem _, splineJoins_zero r k, by
    filter_upwards [Lp.coeFn_zero ℂ p unitVol] with x hx
    rw [hx, ppFun_zero]⟩
  smul_mem' := by
    rintro c g ⟨Q, hQ, hj, hg⟩
    refine ⟨fun n => C (c : ℂ) * Q n, fun n => ?_, hj.const_mul _, ?_⟩
    · show C (c : ℂ) * Q n ∈ degreeLT ℂ r
      rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (hQ n)
    · filter_upwards [Lp.coeFn_smul c g, hg] with x h1 h2
      rw [h1, Pi.smul_apply, h2, ppFun_const_mul, Complex.real_smul]

omit [Fact (1 ≤ p)] in
/-- Splines are piecewise polynomials. -/
theorem splineSpace_le_ppSpace (r k : ℕ) : splineSpace p r k ≤ ppSpace p r k :=
  fun _ ⟨Q, hQ, _, hg⟩ => ⟨Q, hQ, hg⟩

omit [Fact (1 ≤ p)] in
/-- The spline spaces increase with the level. -/
theorem splineSpace_mono (r : ℕ) : Monotone (splineSpace p r) := by
  refine monotone_nat_of_le_succ fun k g hg => ?_
  obtain ⟨Q, hQ, hj, hgQ⟩ := hg
  exact ⟨fun n => Q (n / 2), fun n => hQ _, hj.refine, hgQ.trans (ppFun_refine k Q).symm⟩

variable (p) in
/-- The approximants of complexity `n`: `{0}` for `n = 0`, `S_{⌊log₂ n⌋}` for `n ≥ 1`. -/
noncomputable def splineApproximants (r n : ℕ) : Submodule ℝ (Lp ℂ p unitVol) :=
  if n = 0 then ⊥ else splineSpace p r (Nat.log 2 n)

omit [Fact (1 ≤ p)] in
/-- The approximants of the spline scheme increase. -/
theorem splineApproximants_mono (r : ℕ) : Monotone (splineApproximants p r) := by
  intro a b hab f hf
  by_cases ha : a = 0
  · simp only [splineApproximants, ha, ↓reduceIte, Submodule.mem_bot] at hf
    rw [hf]; exact Submodule.zero_mem _
  · have hb : b ≠ 0 := by omega
    simp only [splineApproximants, ha, hb, ↓reduceIte] at hf ⊢
    exact splineSpace_mono r (Nat.log_mono_right hab) hf

variable (p) in
/-- The **scheme of dyadic splines** of order `r` in `L_p[0, 1]`. -/
noncomputable def splineScheme (r : ℕ) : ApproximationScheme (Lp ℂ p unitVol) :=
  ApproximationScheme.ofSubmodules (splineApproximants p r) (by simp [splineApproximants])
    (splineApproximants_mono r)

/-- The approximants of complexity `2^k` are the splines of level `k`. -/
theorem mem_splineScheme_two_pow {r k : ℕ} {g : Lp ℂ p unitVol} :
    g ∈ splineScheme p r (2 ^ k) ↔ g ∈ splineSpace p r k := by
  show g ∈ splineApproximants p r (2 ^ k) ↔ _
  simp [splineApproximants, Nat.log_pow Nat.one_lt_two]

/-- The spline scheme is linear. -/
theorem splineScheme_isLinear (r : ℕ) : (splineScheme p r).IsLinear :=
  ApproximationScheme.isLinear_ofSubmodules _ _ _

/-! ### B-splines on the dyadic grid -/

/-- The pieces of the B-spline `N_r(2^k x - n)` on the dyadic intervals `I_{k,m}`:
`B_{m-n}(2^k x - n)` for `0 ≤ m - n ≤ r`, and `0` otherwise. -/
noncomputable def bsplinePieces (r k : ℕ) (n : ℤ) (m : ℕ) : ℂ[X] :=
  if 0 ≤ (m : ℤ) - n ∧ (m : ℤ) - n ≤ r then
    (bsplinePiece r ((m : ℤ) - n).toNat).comp
      (C ((-(n : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X)
  else 0

/-- The B-spline pieces have degree `< r`. -/
theorem bsplinePieces_mem {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (n : ℤ) (m : ℕ) :
    bsplinePieces r k n m ∈ degreeLT ℂ r := by
  unfold bsplinePieces
  split_ifs
  · exact comp_affine_mem_degreeLT (bsplinePiece_mem hr _) _ _
  · exact Submodule.zero_mem _

/-- The affine change of variables of the powers:
`(2^k x - n - d)^(r-1) = 2^(k(r-1)) (x - (n + d) 2^(-k))^(r-1)`. -/
theorem X_sub_C_pow_comp_affine (r k : ℕ) (n : ℝ) (d : ℂ) :
    ((X - C d) ^ (r - 1)).comp (C ((-n : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X) =
      C ((((2 : ℝ) ^ k : ℝ) : ℂ) ^ (r - 1)) *
        (X - C (((n : ℂ) + d) / (((2 : ℝ) ^ k : ℝ) : ℂ))) ^ (r - 1) := by
  have h2 : ((((2 : ℝ) ^ k : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  rw [pow_comp, sub_comp, X_comp, C_comp, C_pow, ← mul_pow]
  congr 1
  rw [mul_sub, ← C_mul, mul_div_cancel₀ _ h2, C_add, Complex.ofReal_neg, C_neg]
  ring

/-- The first piece `B_0 = X^(r-1)/(r-1)!`. -/
theorem bsplinePiece_zero (r : ℕ) : bsplinePiece r 0 = C (bsplineCoeff r 0) * (X - C 0) ^ (r - 1) := by
  simp [bsplinePiece]

/-- **The B-splines have spline joins**: at the knot `m 2^(-k)` the pieces of `N_r(2^k x - n)`
jump by `(-1)^d C(r, d)/(r-1)! 2^(k(r-1)) (x - m 2^(-k))^(r-1)`, `d = m - n`. -/
theorem splineJoins_bsplinePieces {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (n : ℤ) :
    SplineJoins r k (bsplinePieces r k n) := by
  intro m hm _
  have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by rw [Nat.cast_sub hm]; rfl
  have hknot : ∀ e : ℕ, (m : ℤ) - n = e →
      ((n : ℝ) : ℂ) + (e : ℂ) = (((m : ℝ)) : ℂ) := fun e he => by
    have : ((n : ℤ) : ℝ) + (e : ℝ) = (m : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) he
      push_cast at this
      linarith
    exact_mod_cast this
  have hcast : (((m : ℝ)) : ℂ) / (((2 : ℝ) ^ k : ℝ) : ℂ) = (((m : ℝ) / 2 ^ k : ℝ) : ℂ) := by
    push_cast; ring
  rcases lt_or_ge ((m : ℤ) - n) 0 with hd | hd
  · -- both pieces vanish
    refine ⟨0, ?_⟩
    simp only [bsplinePieces, hm1, not_le.2 hd, false_and, ↓reduceIte,
      show ¬ (0 ≤ (m : ℤ) - 1 - n) by omega, sub_zero, C_0, zero_mul]
  rcases lt_or_ge (r : ℤ) ((m : ℤ) - n) with hdr | hdr
  · -- right of the support: both pieces vanish (the second one is `B_r = 0`)
    refine ⟨0, ?_⟩
    have h1 : bsplinePieces r k n m = 0 := by
      simp only [bsplinePieces, not_le.2 hdr, and_false, ↓reduceIte]
    have h2 : bsplinePieces r k n (m - 1) = 0 := by
      unfold bsplinePieces
      rw [hm1]
      split_ifs with h
      · rw [show ((m : ℤ) - 1 - n).toNat = r by omega, bsplinePiece_top hr, zero_comp]
      · rfl
    rw [h1, h2, sub_zero, C_0, zero_mul]
  obtain ⟨e, he⟩ : ∃ e : ℕ, (m : ℤ) - n = e := ⟨((m : ℤ) - n).toNat, (Int.toNat_of_nonneg hd).symm⟩
  have hpm : bsplinePieces r k n m = (bsplinePiece r e).comp
      (C ((-(n : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X) := by
    unfold bsplinePieces
    simp only [show 0 ≤ (m : ℤ) - n ∧ (m : ℤ) - n ≤ r from ⟨hd, hdr⟩, and_self, ↓reduceIte]
    rw [he, Int.toNat_natCast]
  rcases Nat.eq_zero_or_pos e with he0 | he0
  · -- `m = n`: the first piece starts
    subst he0
    refine ⟨bsplineCoeff r 0 * ((((2 : ℝ) ^ k : ℝ) : ℂ)) ^ (r - 1), ?_⟩
    have h2 : bsplinePieces r k n (m - 1) = 0 := by
      simp only [bsplinePieces, hm1, show ¬ (0 ≤ (m : ℤ) - 1 - n) by omega, false_and,
        ↓reduceIte]
    have hnm : (((n : ℤ) : ℝ) : ℂ) = (((m : ℝ)) : ℂ) := by
      have := hknot 0 (by simpa using he)
      simpa using this
    rw [h2, sub_zero, hpm, bsplinePiece_zero, mul_comp, C_comp, X_sub_C_pow_comp_affine,
      add_zero, hnm, hcast, C_mul]
    ring
  · -- inside the support: consecutive pieces differ by the new term
    refine ⟨bsplineCoeff r e * ((((2 : ℝ) ^ k : ℝ) : ℂ)) ^ (r - 1), ?_⟩
    have h2 : bsplinePieces r k n (m - 1) = (bsplinePiece r (e - 1)).comp
        (C ((-(n : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X) := by
      unfold bsplinePieces
      rw [hm1]
      simp only [show 0 ≤ (m : ℤ) - 1 - n ∧ (m : ℤ) - 1 - n ≤ r from ⟨by omega, by omega⟩, and_self,
        ↓reduceIte]
      rw [show ((m : ℤ) - 1 - n).toNat = e - 1 by omega]
    have hsucc := bsplinePiece_succ r (e - 1)
    rw [Nat.sub_add_cancel he0] at hsucc
    rw [hpm, h2, hsucc, add_comp, add_sub_cancel_left, mul_comp, C_comp,
      X_sub_C_pow_comp_affine, hknot e he, hcast, C_mul]
    ring

/-- On `I_{k,m}` the pieces are the B-spline: `Q_m(x) = N_r(2^k x - n)`. -/
theorem polyFun_bsplinePieces {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (n : ℤ) {m : ℕ} {x : ℝ}
    (hx : x ∈ dyadicIco k m) : polyFun (bsplinePieces r k n m) x = bspline r (2 ^ k * x - n) := by
  rw [mem_dyadicIco] at hx
  have hy : 2 ^ k * x - n ∈ Ico (((m : ℤ) - n : ℤ) : ℝ) ((((m : ℤ) - n : ℤ) : ℝ) + 1) := by
    push_cast
    constructor <;> linarith [hx.1, hx.2]
  unfold bsplinePieces
  split_ifs with h
  · rw [polyFun_comp_affine]
    obtain ⟨e, he⟩ : ∃ e : ℕ, (m : ℤ) - n = e := ⟨((m : ℤ) - n).toNat, (Int.toNat_of_nonneg h.1).symm⟩
    rw [he, Int.toNat_natCast]
    rw [he] at hy
    push_cast at hy
    rcases lt_or_eq_of_le (show e ≤ r by omega) with her | her
    · rw [bspline_eq_piece her hy]
      congr 1
      ring
    · subst her
      rw [bsplinePiece_top hr, bspline_eq_zero_of_ge hy.1]
      simp [polyFun]
  · push Not at h
    by_cases h0 : 0 ≤ (m : ℤ) - n
    · have h1 := h h0
      have : (r : ℝ) ≤ 2 ^ k * x - n := by
        have : ((r : ℤ) : ℝ) < (((m : ℤ) - n : ℤ) : ℝ) := by exact_mod_cast h1
        push_cast at this hy
        linarith [hy.1]
      rw [bspline_eq_zero_of_ge this]
      simp [polyFun]
    · have : 2 ^ k * x - n < 0 := by
        have : (((m : ℤ) - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : (m : ℤ) - n ≤ -1)
        push_cast at this hy
        linarith [hy.2]
      rw [bspline_eq_zero_of_lt r this]
      simp [polyFun]

end Interval
