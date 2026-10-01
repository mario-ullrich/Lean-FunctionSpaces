/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.KFunctional
public import ApproximationSpaces.Sequences.Hardy

/-!
# The representation theorem: approximation spaces are interpolation spaces

Let `ι : Y → X` satisfy Jackson's and Bernstein's inequalities of order `r > 0` for the scheme
`A`.  Then for `0 < s < r` and `1 ≤ q ≤ ∞`

`A^s_q = (X, Y)_{s/r, q}`   with equivalent norms

(DeVore–Lorentz, Chapter 7, Theorem 9.1; Pietsch).  The two halves:

* **Jackson** (`approxNormDyadic_le_interpNorm_of_jackson`):
  `E_n(f) ≤ max(1, C) K(n^(-r), f)` (`approxSeq_le_kFunctional_of_jackson`), so at the
  dyadic points `2^(ks) E_{2^k}(f) ≤ max(1, C) 2^(kr·s/r) K(2^(-kr), f)`;
* **Bernstein** (`interpNorm_le_approxNormDyadic_of_bernstein`): with near-best approximants
  `a_k = ι z_k` lifted by Bernstein's inequality (`DyadicApprox.exists_lift_partial`),
  `K(2^(-kr), f) ≤ ‖f - a_k‖ + 2^(-kr) ‖z_k‖` and `‖z_k‖ ≲ ∑_{j ≤ k} 2^(jr) E_{2^j}(f)`; Hardy's
  inequality for partial sums with exponent `r - s > 0` (`ENNReal.hardy_sum_le`) finishes.

Neither half needs `Y` to be complete.  The theorem identifies Besov spaces defined by
different schemes with the same Jackson and Bernstein inequalities
(`approxSpace_eq_of_jackson_bernstein`): approximation spaces depend only on the smoothness
space `Y`, not on the particular approximants.
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {ι : Y →L[ℝ] X} {A : ApproximationScheme X} {r s C : ℝ} {q : ℝ≥0∞}

/-- **Jackson's half of the representation theorem**:
`‖f‖_{A^s_q} ≤ max(1, C) ‖f‖_{(X,Y)_{s/r,q}}` (dyadic quasi-norm), for `r ≠ 0`. -/
theorem approxNormDyadic_le_interpNorm_of_jackson (hJ : JacksonBound ι A r C) (hC : 0 ≤ C)
    (hr : r ≠ 0) (f : X) :
    A.approxNormDyadic s q f ≤ max 1 (ENNReal.ofReal C) * interpNorm ι (s / r) r q f := by
  set M := max 1 (ENNReal.ofReal C)
  have hseq : ∀ k, A.approxSeqDyadic s f k ≤ M * interpSeq ι (s / r) r f k := fun k => by
    rw [approxSeqDyadic, interpSeq, mul_div_cancel₀ s hr, mul_left_comm]
    gcongr
    have := approxSeq_le_kFunctional_of_jackson hJ hC (Nat.one_le_two_pow (n := k)) f
    rwa [ENNReal.natCast_two_pow_rpow] at this
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ M * ‖f‖ₑ + M * lqNorm q (interpSeq ι (s / r) r f) := by
        gcongr
        · exact le_mul_of_one_le_left' (le_max_left _ _)
        · rw [← ENNReal.lqNorm_const_mul]; exact ENNReal.lqNorm_mono hseq
    _ = M * interpNorm ι (s / r) r q f := by rw [interpNorm, mul_add]

/-- The constant of Bernstein's half of the representation theorem,
`3 + (3 C + 2 K) (1 - 2^(-(r-s)))⁻¹` with `K = liftConst C r`. -/
noncomputable def reprConst (C r s : ℝ) : ℝ≥0∞ :=
  3 + (3 * ENNReal.ofReal C + 2 * liftConst C r) * (1 - (2 : ℝ≥0∞) ^ (-(r - s)))⁻¹

/-- The constant of the representation theorem is finite for `s < r`. -/
theorem reprConst_ne_top (C : ℝ) (h : s < r) : reprConst C r s ≠ ∞ := by
  unfold reprConst
  refine ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (by norm_num) (liftConst_ne_top C r)⟩)
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 h))⟩

/-- **Bernstein's half of the representation theorem**: for `0 < s < r`,
`‖f‖_{(X,Y)_{s/r,q}} ≤ reprConst C r s · ‖f‖_{A^s_q}` (dyadic quasi-norm). -/
theorem interpNorm_le_approxNormDyadic_of_bernstein (hB : LiftBound ι A r C) (hC : 0 ≤ C)
    (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q) (f : X) :
    interpNorm ι (s / r) r q f ≤ reprConst C r s * A.approxNormDyadic s q f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have : interpSeq ι (s / r) r (0 : X) = fun _ => 0 := by funext k; simp [interpSeq]
    simp [interpNorm, this]
  have hr : r ≠ 0 := (hs.trans hsr).ne'
  set t := tolerance f s
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 s) (tolerance_ne_top f s)
  obtain ⟨y0, d, hpart, hy0, hd⟩ := D.exists_lift_partial (tolerance_anti f hs.le) hB hC
  set K := liftConst C r
  set Cr := (1 - (2 : ℝ≥0∞) ^ (-(r - s)))⁻¹
  set N := A.approxNormDyadic s q f
  set Ds := lqNorm q (A.approxSeqDyadic s f)
  set b : ℕ → ℝ≥0∞ := fun j => dyadicWeight r j * (A.approxSeq f (2 ^ j) + t j)
  have hy0' : ‖y0‖ₑ ≤ 3 * ENNReal.ofReal C * ‖f‖ₑ := by
    rw [tolerance_zero] at hy0
    calc ‖y0‖ₑ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + ‖f‖ₑ) := hy0
      _ = 3 * ENNReal.ofReal C * ‖f‖ₑ := by ring
  -- the K-functional at `2^(-kr)`, through the lifted partial sums
  have hK : ∀ k, interpSeq ι (s / r) r f k ≤
      (A.approxSeqDyadic s f k + dyadicWeight s k * t k) +
        (3 * ENNReal.ofReal C * ‖f‖ₑ * dyadicWeight (-(r - s)) k +
          K * (dyadicWeight (-(r - s)) k * ∑ j ∈ range (k + 1), b j)) := fun k => by
    have hz : ‖y0 + ∑ j ∈ range k, d j‖ₑ ≤ 3 * ENNReal.ofReal C * ‖f‖ₑ +
        K * ∑ j ∈ range (k + 1), b j := by
      calc ‖y0 + ∑ j ∈ range k, d j‖ₑ ≤ ‖y0‖ₑ + ∑ j ∈ range k, ‖d j‖ₑ :=
            (enorm_add_le _ _).trans (by gcongr; exact enorm_sum_le _ _)
        _ ≤ 3 * ENNReal.ofReal C * ‖f‖ₑ + ∑ j ∈ range k, K * b j := by
            gcongr with j; exact hd j
        _ ≤ 3 * ENNReal.ofReal C * ‖f‖ₑ + ∑ j ∈ range (k + 1), K * b j := by
            gcongr; exact Nat.le_succ k
        _ = _ := by rw [Finset.mul_sum]
    have hkf : kFunctional ι (dyadicWeight (-r) k) f ≤
        (A.approxSeq f (2 ^ k) + t k) + dyadicWeight (-r) k *
          (3 * ENNReal.ofReal C * ‖f‖ₑ + K * ∑ j ∈ range (k + 1), b j) := by
      refine (kFunctional_le (y0 + ∑ j ∈ range k, d j) f).trans ?_
      rw [hpart k]
      gcongr
      exact D.enorm_sub_le k
    rw [interpSeq, mul_div_cancel₀ s hr]
    calc dyadicWeight s k * kFunctional ι (dyadicWeight (-r) k) f
        ≤ dyadicWeight s k * ((A.approxSeq f (2 ^ k) + t k) + dyadicWeight (-r) k *
          (3 * ENNReal.ofReal C * ‖f‖ₑ + K * ∑ j ∈ range (k + 1), b j)) := by gcongr
      _ = _ := by
          have hw : dyadicWeight s k * dyadicWeight (-r) k = dyadicWeight (-(r - s)) k := by
            rw [← ENNReal.dyadicWeight_add]; congr 1; ring
          simp only [approxSeqDyadic, mul_add, ← mul_assoc, hw]
          ring
  -- the four sequences
  have hsplit : ∀ k, dyadicWeight (-(r - s)) k * b k =
      A.approxSeqDyadic s f k + dyadicWeight s k * t k := fun k => by
    simp only [b, approxSeqDyadic, ← mul_assoc, ← ENNReal.dyadicWeight_add, mul_add]
    congr 2 <;> congr 1 <;> ring
  have hL12 : lqNorm q (fun k => A.approxSeqDyadic s f k + dyadicWeight s k * t k) ≤
      Ds + 2 * ‖f‖ₑ :=
    (ENNReal.lqNorm_add_le hq _ _).trans
      (add_le_add le_rfl (lqNorm_dyadicWeight_mul_tolerance_le hq f le_rfl))
  have hL3 : lqNorm q (fun k => 3 * ENNReal.ofReal C * ‖f‖ₑ * dyadicWeight (-(r - s)) k) ≤
      3 * ENNReal.ofReal C * ‖f‖ₑ * Cr := by
    rw [ENNReal.lqNorm_const_mul]
    gcongr
    exact ENNReal.lqNorm_dyadicWeight_neg_le hq _
  have hL4 : lqNorm q (fun k => K * (dyadicWeight (-(r - s)) k * ∑ j ∈ range (k + 1), b j)) ≤
      K * (Cr * (Ds + 2 * ‖f‖ₑ)) := by
    rw [ENNReal.lqNorm_const_mul]
    gcongr
    calc lqNorm q (fun k => dyadicWeight (-(r - s)) k * ∑ j ∈ range (k + 1), b j)
        ≤ Cr * lqNorm q (fun k => dyadicWeight (-(r - s)) k * b k) :=
          ENNReal.hardy_sum_le hq (r - s) b
      _ ≤ Cr * (Ds + 2 * ‖f‖ₑ) := by simp_rw [hsplit]; gcongr
  have hfN : ‖f‖ₑ ≤ N := enorm_le_approxNormDyadic f
  have hDN : Ds ≤ N := lqNorm_le_approxNormDyadic f
  calc interpNorm ι (s / r) r q f = ‖f‖ₑ + lqNorm q (interpSeq ι (s / r) r f) := rfl
    _ ≤ ‖f‖ₑ + ((Ds + 2 * ‖f‖ₑ) + (3 * ENNReal.ofReal C * ‖f‖ₑ * Cr +
          K * (Cr * (Ds + 2 * ‖f‖ₑ)))) := by
        gcongr
        calc lqNorm q (interpSeq ι (s / r) r f)
            ≤ lqNorm q (fun k => (A.approxSeqDyadic s f k + dyadicWeight s k * t k) +
                (3 * ENNReal.ofReal C * ‖f‖ₑ * dyadicWeight (-(r - s)) k +
                  K * (dyadicWeight (-(r - s)) k * ∑ j ∈ range (k + 1), b j))) :=
              ENNReal.lqNorm_mono hK
          _ ≤ _ := (ENNReal.lqNorm_add_le hq _ _).trans (add_le_add hL12
              ((ENNReal.lqNorm_add_le hq _ _).trans (add_le_add hL3 hL4)))
    _ = (‖f‖ₑ + (Ds + 2 * ‖f‖ₑ)) + 3 * ENNReal.ofReal C * ‖f‖ₑ * Cr +
          K * (Cr * (Ds + 2 * ‖f‖ₑ)) := by ring
    _ ≤ 3 * N + 3 * ENNReal.ofReal C * N * Cr + K * (Cr * (2 * N)) := by
        have hN : N = ‖f‖ₑ + Ds := rfl
        have h1 : ‖f‖ₑ + (Ds + 2 * ‖f‖ₑ) ≤ 3 * N :=
          calc ‖f‖ₑ + (Ds + 2 * ‖f‖ₑ) = N + 2 * ‖f‖ₑ := by rw [hN]; ring
            _ ≤ N + 2 * N := by gcongr
            _ = 3 * N := by ring
        have h2 : Ds + 2 * ‖f‖ₑ ≤ 2 * N :=
          calc Ds + 2 * ‖f‖ₑ = N + ‖f‖ₑ := by rw [hN]; ring
            _ ≤ N + N := by gcongr
            _ = 2 * N := by ring
        gcongr
    _ = reprConst C r s * N := by simp only [reprConst, K, Cr]; ring

/-- **The representation theorem**: under Jackson's and Bernstein's inequalities of order `r`
and for `0 < s < r`, `f ∈ A^s_q` if and only if `f ∈ (X, Y)_{s/r,q}`. -/
theorem memApprox_iff_memInterp {C₁ C₂ : ℝ} (hJ : JacksonBound ι A r C₁) (hC₁ : 0 ≤ C₁)
    (hB : LiftBound ι A r C₂) (hC₂ : 0 ≤ C₂) (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q) {f : X} :
    A.MemApprox s q f ↔ MemInterp ι (s / r) r q f := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le]
  constructor
  · intro h
    exact (interpNorm_le_approxNormDyadic_of_bernstein hB hC₂ hs hsr hq f).trans_lt
      (ENNReal.mul_lt_top (reprConst_ne_top C₂ hsr).lt_top h)
  · intro h
    exact (approxNormDyadic_le_interpNorm_of_jackson hJ hC₁ (hs.trans hsr).ne' f).trans_lt
      (ENNReal.mul_lt_top (max_lt ENNReal.one_lt_top ENNReal.ofReal_lt_top) h)

/-- **The representation theorem** as an equality of subspaces: `A^s_q = (X, Y)_{s/r,q}`. -/
theorem approxSpace_eq_interpSpace {C₁ C₂ : ℝ} (hJ : JacksonBound ι A r C₁) (hC₁ : 0 ≤ C₁)
    (hB : LiftBound ι A r C₂) (hC₂ : 0 ≤ C₂) (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q) :
    A.approxSpace s q hs.le hq = interpSpace ι (s / r) r q hq :=
  Submodule.ext fun _ => memApprox_iff_memInterp hJ hC₁ hB hC₂ hs hsr hq

/-- **Approximation spaces depend only on the smoothness space**: two schemes satisfying
Jackson's and Bernstein's inequalities of the same order `r` for the same `ι : Y → X` have the
same approximation spaces `A^s_q`, `0 < s < r`. -/
theorem approxSpace_eq_of_jackson_bernstein {B : ApproximationScheme X} {C₁ C₂ C₃ C₄ : ℝ}
    (hJA : JacksonBound ι A r C₁) (hC₁ : 0 ≤ C₁) (hBA : LiftBound ι A r C₂) (hC₂ : 0 ≤ C₂)
    (hJB : JacksonBound ι B r C₃) (hC₃ : 0 ≤ C₃) (hBB : LiftBound ι B r C₄) (hC₄ : 0 ≤ C₄)
    (hs : 0 < s) (hsr : s < r) (hq : 1 ≤ q) :
    A.approxSpace s q hs.le hq = B.approxSpace s q hs.le hq := by
  rw [approxSpace_eq_interpSpace hJA hC₁ hBA hC₂ hs hsr hq,
    approxSpace_eq_interpSpace hJB hC₃ hBB hC₄ hs hsr hq]

/-- **The representation theorem for a smoothness space** `W` of order `r`: for `0 < s < r`,
`A^s_q = (X, W)_{s/r,q}`. -/
theorem SmoothnessSpace.memApprox_iff_memInterp (W : SmoothnessSpace A Y) (hs : 0 < s)
    (hsr : s < W.order) (hq : 1 ≤ q) {f : X} :
    A.MemApprox s q f ↔ MemInterp W.ι (s / W.order) W.order q f :=
  ApproximationScheme.memApprox_iff_memInterp W.jackson W.jacksonConst_nonneg W.bernstein
    W.bernsteinConst_nonneg hs hsr hq

end ApproximationScheme
