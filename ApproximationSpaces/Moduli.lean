/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Lift
public import ApproximationSpaces.Sequences.Hardy

/-!
# Moduli of smoothness and approximation: the coincidence theorem

Classical function spaces are defined by a **modulus of smoothness** `ω(f, 2^(-k))`, approximation
spaces by the errors `E_{2^k}(f)`.  They coincide when the scheme and the modulus are linked by

* a **Jackson inequality** `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for `k ≥ 1`, and
* an **inverse inequality** of order `θ`: `ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`
  (with `k - j` truncated at `0`, so for `k < j` this is a bound by `‖a‖`).

A `ModulusData A θ` bundles the modulus (sampled at dyadic scales, `modulus f k = ω(f, 2^(-k))`), its
subadditivity and bound `ω(f) ≤ C₀ ‖f‖`, and the two inequalities.  With the classical
quasi-norm `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q}` (`ModulusData.modNorm`):

* `‖f‖_{A^s_q} ≤ (2 + C_J) ‖f‖^ω_{s,q}` for all `s ≥ 0` (`ModulusData.approxNormDyadic_le_modNorm`);
* `‖f‖^ω_{s,q} ≤ K ‖f‖_{A^s_q}` for `0 ≤ s < θ` (`ModulusData.modNorm_le_approxNormDyadic`),
  by writing `f` as `(f - a_k) + a_0 + ∑_{j<k} (a_{j+1} - a_j)` with near-best approximants and
  applying the inverse inequality to each block and Hardy's inequality to the sum.

So `A^s_q` is the classical space for `0 < s < θ` (`ModulusData.memApprox_iff_modNorm_lt_top`).
The same theorem serves trigonometric polynomials (`θ = r` for `ω_r`), piecewise polynomials
(`θ = 1/p`), splines and wavelets.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

/-- A **modulus of smoothness compatible with the scheme `A`**, with inverse order `θ`: the
modulus at the dyadic scales `modulus f k = ω(f, 2^(-k))`, subadditive and bounded by `C₀ ‖f‖`, with a
Jackson inequality `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for `k ≥ 1` and an inverse inequality
`ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`. -/
structure ModulusData (A : ApproximationScheme X) (θ : ℝ) where
  /-- The modulus at the dyadic scales. -/
  modulus : X → ℕ → ℝ≥0∞
  add_le : ∀ f g k, modulus (f + g) k ≤ modulus f k + modulus g k
  /-- The constant of `ω(f) ≤ C₀ ‖f‖`. -/
  C0 : ℝ≥0∞
  C0_ne_top : C0 ≠ ∞
  le_enorm : ∀ f k, modulus f k ≤ C0 * ‖f‖ₑ
  /-- The Jackson constant. -/
  CJ : ℝ≥0∞
  CJ_ne_top : CJ ≠ ∞
  jackson : ∀ f k, 1 ≤ k → A.approxSeq f (2 ^ k) ≤ CJ * modulus f k
  /-- The constant of the inverse inequality. -/
  CB : ℝ≥0∞
  CB_ne_top : CB ≠ ∞
  inverse : ∀ j k, ∀ a ∈ A (2 ^ j), modulus a k ≤ CB * dyadicWeight (-θ) (k - j) * ‖a‖ₑ

namespace ModulusData

variable {θ : ℝ} (M : ModulusData A θ)

/-- The **classical quasi-norm** `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q}`. -/
noncomputable def modNorm (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * M.modulus f k)

/-- The modulus of `0` vanishes. -/
theorem modulus_zero (k : ℕ) : M.modulus 0 k = 0 :=
  le_antisymm ((M.le_enorm 0 k).trans (by simp)) bot_le

/-- The modulus is subadditive on finite sums. -/
theorem modulus_sum_le {ι : Type*} (t : Finset ι) (g : ι → X) (k : ℕ) :
    M.modulus (∑ i ∈ t, g i) k ≤ ∑ i ∈ t, M.modulus (g i) k := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [M.modulus_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (M.add_le _ _ k).trans (add_le_add le_rfl ih)

/-- **Jackson's direction**: `‖f‖_{A^s_q} ≤ (2 + C_J) ‖f‖^ω_{s,q}`. -/
theorem approxNormDyadic_le_modNorm (hq : 1 ≤ q) (f : X) :
    A.approxNormDyadic s q f ≤ (2 + M.CJ) * M.modNorm s q f := by
  set L := lqNorm q (fun k => dyadicWeight s k * M.modulus f k)
  have hshift : lqNorm q (fun k => A.approxSeqDyadic s f (k + 1)) ≤ M.CJ * L := by
    rw [← ENNReal.lqNorm_const_mul]
    refine (ENNReal.lqNorm_mono fun k => ?_).trans (ENNReal.lqNorm_shift_le _)
    rw [approxSeqDyadic, mul_left_comm]
    gcongr
    exact M.jackson f (k + 1) (Nat.succ_pos k)
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ ‖f‖ₑ + (A.approxSeqDyadic s f 0 + lqNorm q fun k => A.approxSeqDyadic s f (k + 1)) := by
        gcongr; exact ENNReal.lqNorm_le_head_add_shift hq _
    _ ≤ ‖f‖ₑ + (‖f‖ₑ + M.CJ * L) := by
        gcongr
        rw [approxSeqDyadic_zero]
        exact approxSeq_le_enorm f 1
    _ ≤ (2 + M.CJ) * (‖f‖ₑ + L) := by
        calc ‖f‖ₑ + (‖f‖ₑ + M.CJ * L) = 2 * ‖f‖ₑ + M.CJ * L := by ring
          _ ≤ (2 * ‖f‖ₑ + M.CJ * ‖f‖ₑ) + (2 * L + M.CJ * L) := by
              gcongr
              · exact le_self_add
              · exact le_add_self
          _ = (2 + M.CJ) * (‖f‖ₑ + L) := by ring

/-- `2^(-(n-2)θ) ≤ 2^(2θ) 2^(-nθ)` for truncated subtraction and `θ ≥ 0`. -/
theorem dyadicWeight_neg_sub_two_le {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    dyadicWeight (-θ) (n - 2) ≤ dyadicWeight θ 2 * dyadicWeight (-θ) n := by
  rcases le_or_gt 2 n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, ENNReal.dyadicWeight_add_nat, ← mul_assoc,
      ENNReal.dyadicWeight_mul_neg_self, one_mul]
  · calc dyadicWeight (-θ) (n - 2) = 1 := by rw [show n - 2 = 0 by omega]; simp
      _ ≤ dyadicWeight θ 2 * dyadicWeight (-θ) n := by
          rw [← ENNReal.dyadicWeight_mul_neg_self θ n]
          gcongr
          · exact ENNReal.dyadicWeight_mono hθ (by omega)

/-- The constant of the inverse direction,
`1 + 3 C₀ + C_B (3 + 6 · 4^θ) (1 - 2^(-(θ-s)))⁻¹`. -/
noncomputable def inverseConst (s : ℝ) : ℝ≥0∞ :=
  1 + 3 * M.C0 + M.CB * (3 + 6 * dyadicWeight θ 2) * (1 - (2 : ℝ≥0∞) ^ (-(θ - s)))⁻¹

/-- The constant of the inverse direction is finite for `s < θ`. -/
theorem inverseConst_ne_top (hsθ : s < θ) : M.inverseConst s ≠ ∞ := by
  have hr : (2 : ℝ≥0∞) ^ (-(θ - s)) < 1 := ENNReal.two_rpow_neg_lt_one (by linarith)
  unfold inverseConst
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (by norm_num) M.C0_ne_top⟩, ENNReal.mul_ne_top (ENNReal.mul_ne_top
      M.CB_ne_top (ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (by norm_num)
        (ENNReal.dyadicWeight_ne_top _ _)⟩)) (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne')⟩

/-- **The inverse direction**: for `0 ≤ s < θ`, `‖f‖^ω_{s,q} ≤ K ‖f‖_{A^s_q}` with
`K = M.inverseConst s`. -/
theorem modNorm_le_approxNormDyadic (hq : 1 ≤ q) (hs : 0 ≤ s) (hsθ : s < θ) (f : X) :
    M.modNorm s q f ≤ M.inverseConst s * A.approxNormDyadic s q f := by
  have hθ : 0 ≤ θ := hs.trans hsθ.le
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [modNorm, M.modulus_zero]
  set t := tolerance f s
  obtain ⟨D⟩ := A.exists_dyadicApprox f (fun k => tolerance_ne_zero hf0 s k)
    (tolerance_ne_top f s)
  have ht : Antitone t := tolerance_anti f hs
  set N := A.approxNormDyadic s q f
  set E : ℕ → ℝ≥0∞ := fun k => dyadicWeight s k * (A.approxSeq f (2 ^ k) + t k)
  have hE : lqNorm q E ≤ N + 2 * ‖f‖ₑ := by
    calc lqNorm q E = lqNorm q (fun k => A.approxSeqDyadic s f k + dyadicWeight s k * t k) := by
          congr 1; funext k; simp only [E, approxSeqDyadic]; ring
      _ ≤ lqNorm q (A.approxSeqDyadic s f) + lqNorm q (fun k => dyadicWeight s k * t k) :=
          ENNReal.lqNorm_add_le hq _ _
      _ ≤ N + 2 * ‖f‖ₑ := add_le_add le_add_self
          (lqNorm_dyadicWeight_mul_tolerance_le hq f le_rfl)
  -- pointwise bound for one scale
  set α := θ - s
  have hpt : ∀ k, dyadicWeight s k * M.modulus f k ≤
      M.C0 * E k + M.CB * 3 * ‖f‖ₑ * dyadicWeight (-α) k +
        M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-α) k *
          ∑ j ∈ range (k + 1), dyadicWeight α j * E j) := fun k => by
    have htel : f = (f - D.a k) + (D.a 0 + ∑ j ∈ range k, (D.a (j + 1) - D.a j)) := by
      rw [sum_range_sub (fun j => D.a j) k]; abel
    have h1 : M.modulus (f - D.a k) k ≤ M.C0 * (A.approxSeq f (2 ^ k) + t k) :=
      (M.le_enorm _ k).trans (by gcongr; exact D.enorm_sub_le k)
    have h2 : M.modulus (D.a 0) k ≤ M.CB * dyadicWeight (-θ) k * (3 * ‖f‖ₑ) := by
      refine (M.inverse 0 k _ (by simpa using D.mem 0)).trans ?_
      rw [Nat.sub_zero]
      gcongr
      calc ‖D.a 0‖ₑ ≤ 2 * ‖f‖ₑ + t 0 := D.enorm_zero_le
        _ = 3 * ‖f‖ₑ := by rw [show t 0 = ‖f‖ₑ from tolerance_zero f s]; ring
    have h3 : ∀ j ∈ range k, M.modulus (D.a (j + 1) - D.a j) k ≤
        M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-θ) (k - j) *
          (A.approxSeq f (2 ^ j) + t j)) := fun j _ => by
      refine (M.inverse (j + 2) k _ (D.sub_mem j)).trans ?_
      calc M.CB * dyadicWeight (-θ) (k - (j + 2)) * ‖D.a (j + 1) - D.a j‖ₑ
          ≤ M.CB * (dyadicWeight θ 2 * dyadicWeight (-θ) (k - j)) *
              (2 * (A.approxSeq f (2 ^ j) + t j)) := by
            gcongr
            · rw [show k - (j + 2) = k - j - 2 by omega]
              exact dyadicWeight_neg_sub_two_le hθ (k - j)
            · exact D.enorm_sub_succ_le ht j
        _ = _ := by ring
    have hω : M.modulus f k ≤ M.C0 * (A.approxSeq f (2 ^ k) + t k) +
        M.CB * dyadicWeight (-θ) k * (3 * ‖f‖ₑ) + ∑ j ∈ range k,
          M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-θ) (k - j) *
            (A.approxSeq f (2 ^ j) + t j)) := by
      calc M.modulus f k = M.modulus ((f - D.a k) + (D.a 0 + ∑ j ∈ range k, (D.a (j + 1) - D.a j))) k := by
            rw [← htel]
        _ ≤ M.modulus (f - D.a k) k + (M.modulus (D.a 0) k + ∑ j ∈ range k, M.modulus (D.a (j + 1) - D.a j) k) :=
            (M.add_le _ _ k).trans (add_le_add le_rfl ((M.add_le _ _ k).trans
              (add_le_add le_rfl (M.modulus_sum_le _ _ k))))
        _ ≤ _ := by
            rw [← add_assoc]
            exact add_le_add (add_le_add h1 h2) (Finset.sum_le_sum h3)
    -- multiply by the weight
    have hw : ∀ j ∈ range k, dyadicWeight s k * dyadicWeight (-θ) (k - j) =
        dyadicWeight (-α) k * dyadicWeight α j * dyadicWeight s j := fun j hj => by
      have hjk : j ≤ k := (Finset.mem_range.1 hj).le
      simp only [ENNReal.dyadicWeight]
      rw [← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
        ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
        ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, Nat.cast_sub hjk]
      congr 1
      simp only [α]
      ring
    have hw0 : dyadicWeight s k * dyadicWeight (-θ) k = dyadicWeight (-α) k := by
      rw [← ENNReal.dyadicWeight_add]; congr 1; simp only [α]; ring
    calc dyadicWeight s k * M.modulus f k
        ≤ dyadicWeight s k * (M.C0 * (A.approxSeq f (2 ^ k) + t k) +
            M.CB * dyadicWeight (-θ) k * (3 * ‖f‖ₑ) + ∑ j ∈ range k,
              M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-θ) (k - j) *
                (A.approxSeq f (2 ^ j) + t j))) := by gcongr
      _ = M.C0 * E k + M.CB * 3 * ‖f‖ₑ * (dyadicWeight s k * dyadicWeight (-θ) k) +
            M.CB * (2 * dyadicWeight θ 2) * ∑ j ∈ range k,
              (dyadicWeight s k * dyadicWeight (-θ) (k - j)) *
                (A.approxSeq f (2 ^ j) + t j) := by
          simp only [E, mul_add, Finset.mul_sum]; ring_nf
      _ ≤ M.C0 * E k + M.CB * 3 * ‖f‖ₑ * dyadicWeight (-α) k +
            M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-α) k *
              ∑ j ∈ range (k + 1), dyadicWeight α j * E j) := by
          rw [hw0, Finset.sum_congr rfl fun j hj => by rw [hw j hj]]
          have hsum : ∑ j ∈ range k, dyadicWeight (-α) k * dyadicWeight α j * dyadicWeight s j *
              (A.approxSeq f (2 ^ j) + t j) =
                dyadicWeight (-α) k * ∑ j ∈ range k, dyadicWeight α j * E j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [E]
            ring
          rw [hsum]
          exact add_le_add le_rfl (mul_le_mul_right (mul_le_mul_right
            (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ k))) _) _)
  -- the ℓ_q norm
  have hr : (2 : ℝ≥0∞) ^ (-α) < 1 := ENNReal.two_rpow_neg_lt_one (by simp only [α]; linarith)
  have hgeo : lqNorm q (dyadicWeight (-α)) ≤ (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ :=
    ENNReal.lqNorm_dyadicWeight_neg_le hq α
  have hhardy := ENNReal.hardy_sum_le hq α (fun j => dyadicWeight α j * E j)
  have hcancel : (fun k => dyadicWeight (-α) k * (dyadicWeight α k * E k)) = E := by
    funext k; rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
  rw [hcancel] at hhardy
  have hfN : ‖f‖ₑ ≤ N := enorm_le_approxNormDyadic f
  calc M.modNorm s q f = ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * M.modulus f k) := rfl
    _ ≤ ‖f‖ₑ + (M.C0 * lqNorm q E + M.CB * 3 * ‖f‖ₑ * lqNorm q (dyadicWeight (-α)) +
          M.CB * (2 * dyadicWeight θ 2) * lqNorm q (fun k => dyadicWeight (-α) k *
            ∑ j ∈ range (k + 1), dyadicWeight α j * E j)) := by
        gcongr
        refine (ENNReal.lqNorm_mono hpt).trans ?_
        refine (ENNReal.lqNorm_add_le hq _ _).trans ?_
        gcongr
        · refine (ENNReal.lqNorm_add_le hq _ _).trans ?_
          rw [ENNReal.lqNorm_const_mul, ENNReal.lqNorm_const_mul]
        · rw [ENNReal.lqNorm_const_mul]
    _ ≤ N + (M.C0 * (N + 2 * N) + M.CB * 3 * N * (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ +
          M.CB * (2 * dyadicWeight θ 2) * ((1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * (N + 2 * N))) := by
        gcongr
        · exact hE.trans (by gcongr)
        · exact hhardy.trans (by gcongr; exact hE.trans (by gcongr))
    _ = (1 + 3 * M.C0 + M.CB * (3 + 6 * dyadicWeight θ 2) * (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹) * N := by
        ring
    _ = M.inverseConst s * N := rfl

/-- **The coincidence theorem**: for `0 ≤ s < θ` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff the classical
quasi-norm `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q}` is finite. -/
theorem memApprox_iff_modNorm_lt_top (hq : 1 ≤ q) (hs : 0 ≤ s) (hsθ : s < θ) (f : X) :
    A.MemApprox s q f ↔ M.modNorm s q f < ∞ := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs]
  constructor
  · intro h
    exact (M.modNorm_le_approxNormDyadic hq hs hsθ f).trans_lt
      (ENNReal.mul_lt_top (M.inverseConst_ne_top hsθ).lt_top h)
  · intro h
    exact (M.approxNormDyadic_le_modNorm hq f).trans_lt
      (ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨by norm_num, M.CJ_ne_top.lt_top⟩) h)

end ModulusData

end ApproximationScheme
