/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Interval.Polynomials
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Cardinal B-splines

The **cardinal B-spline** of order `r ≥ 1` is the function `N_r` that vanishes outside `[0, r)`
and on `[j, j + 1)`, `0 ≤ j < r`, is the polynomial
`B_j(X) = ∑_{l ≤ j} (-1)^l C(r, l) (X - l)^(r-1) / (r-1)!` (`Interval.bsplinePiece`), so that
`N_r(x) = ∑_l (-1)^l C(r, l) (x - l)_+^(r-1) / (r-1)!`. Everything here is algebra of the pieces.

* Consecutive pieces differ by a multiple of `(X - j)^(r-1)` (`Interval.bsplinePiece_succ`),
  and `B_r = 0` (`Interval.bsplinePiece_top`), the `r`-th difference of a polynomial of degree
  `< r` (Mathlib's `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`). So `N_r` is a spline: its
  pieces agree to order `r - 2` at the knots.
* On `[0, 1)` the `r` B-splines `N_r(· + j)`, `j < r`, are the polynomials
  `β_j(X) = B_j(X + j)` (`Interval.bsplineLocal`), and these form a basis of the polynomials of
  degree `< r` (`Interval.bsplineBasis`): in terms of the shifted powers `(X + m)^(r-1)`, which
  are linearly independent by a Vandermonde argument, the change of basis is triangular.
* `β_j(X + 1) = β_{j+1} - (const) X^(r-1)` (`Interval.bsplineLocal_comp_add_one`). Hence the
  coordinates of a polynomial in these bases on neighbouring unit intervals agree
  (`Interval.bcoord_comp_add_one`, `Interval.bcoord_comp_eq_bsplineCoef`): **every polynomial `P`
  of degree `< r` is `∑_n c_n(P) N_r(x - n)` on all of `ℝ`**, with one coefficient `c_n(P)` per
  B-spline (`Interval.polyFun_eq_sum_bsplineCoef`).
-/

@[expose] public section

open Polynomial Finset

namespace Interval

/-- The coefficients `(-1)^l C(r, l) / (r-1)!` of the pieces of the B-spline of order `r`. -/
noncomputable def bsplineCoeff (r l : ℕ) : ℂ :=
  (-1 : ℂ) ^ l * (r.choose l : ℂ) / ((r - 1).factorial : ℂ)

/-- The `j`-th piece of the cardinal B-spline of order `r`,
`B_j(X) = ∑_{l ≤ j} (-1)^l C(r, l) (X - l)^(r-1) / (r-1)!`, the B-spline on `[j, j + 1)`. -/
noncomputable def bsplinePiece (r j : ℕ) : ℂ[X] :=
  ∑ l ∈ range (j + 1), C (bsplineCoeff r l) * (X - C (l : ℂ)) ^ (r - 1)

/-- Consecutive pieces differ by a multiple of `(X - (j + 1))^(r-1)`. -/
theorem bsplinePiece_succ (r j : ℕ) :
    bsplinePiece r (j + 1) =
      bsplinePiece r j + C (bsplineCoeff r (j + 1)) * (X - C ((j + 1 : ℕ) : ℂ)) ^ (r - 1) := by
  rw [bsplinePiece, sum_range_succ, ← bsplinePiece]

/-- The first piece `B_0 = X^(r-1)/(r-1)!`. -/
theorem bsplinePiece_zero (r : ℕ) :
    bsplinePiece r 0 = C (bsplineCoeff r 0) * (X - C 0) ^ (r - 1) := by
  simp [bsplinePiece]

/-- The power of a polynomial of degree `≤ 1` to the `r - 1` has degree `< r` (Mathlib's
`Polynomial.natDegree_pow_le_of_le`). -/
theorem pow_mem_degreeLT {r : ℕ} (hr : 1 ≤ r) {P : ℂ[X]} (hP : P.natDegree ≤ 1) :
    P ^ (r - 1) ∈ degreeLT ℂ r := by
  rw [mem_degreeLT]
  have h : (P ^ (r - 1)).natDegree < r := (natDegree_pow_le_of_le (r - 1) hP).trans_lt (by omega)
  exact (degree_le_natDegree).trans_lt (by exact_mod_cast h)

/-- The pieces have degree `< r`. -/
theorem bsplinePiece_mem {r : ℕ} (hr : 1 ≤ r) (j : ℕ) : bsplinePiece r j ∈ degreeLT ℂ r :=
  Submodule.sum_mem _ fun l _ => by
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (pow_mem_degreeLT hr (natDegree_X_sub_C_le _))

/-- **The last piece vanishes**, `B_r = 0`: `∑_{l ≤ r} (-1)^l C(r, l) (z - l)^(r-1) = 0` is the
`r`-th difference of the polynomial `(z - X)^(r-1)` of degree `< r` at `0` (Mathlib's
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` and `fwdDiff_iter_eq_sum_shift`). -/
theorem bsplinePiece_top {r : ℕ} (hr : 1 ≤ r) : bsplinePiece r r = 0 := by
  refine Polynomial.funext fun z => ?_
  have hdeg : ((C z - X) ^ (r - 1)).natDegree < r :=
    (natDegree_pow_le_of_le (m := 1) (r - 1) ((natDegree_sub_le _ _).trans (by simp))).trans_lt
      (by omega)
  have hsum : ∑ k ∈ range (r + 1),
      (-1 : ℂ) ^ (r - k) * (r.choose k : ℂ) * (z - k) ^ (r - 1) = 0 := by
    have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
    rw [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at h
    refine (sum_congr rfl fun k _ => ?_).trans h
    simp only [eval_pow, eval_sub, eval_C, eval_X, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul]
    push_cast
    ring
  rw [eval_zero, bsplinePiece, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  calc ∑ l ∈ range (r + 1), bsplineCoeff r l * (z - l) ^ (r - 1)
      = ((-1 : ℂ) ^ r / ((r - 1).factorial : ℂ)) * ∑ k ∈ range (r + 1),
          (-1 : ℂ) ^ (r - k) * (r.choose k : ℂ) * (z - k) ^ (r - 1) := by
        rw [mul_sum]
        refine sum_congr rfl fun l hl => ?_
        rw [bsplineCoeff, neg_one_pow_eq_of_le (Nat.lt_succ_iff.1 (mem_range.1 hl))]
        ring
    _ = 0 := by rw [hsum, mul_zero]

/-! ### The B-spline basis on a unit interval -/

/-- The **B-splines on `[0, 1)`**: `β_j(X) = B_j(X + j)` is `N_r(· + j)` on `[0, 1)`. -/
noncomputable def bsplineLocal (r j : ℕ) : ℂ[X] := (bsplinePiece r j).comp (X + C (j : ℂ))

/-- `β_j = ∑_{l ≤ j} (-1)^l C(r, l) (X + (j - l))^(r-1) / (r-1)!`. -/
theorem bsplineLocal_eq (r j : ℕ) :
    bsplineLocal r j =
      ∑ l ∈ range (j + 1), C (bsplineCoeff r l) * (X + C ((j - l : ℕ) : ℂ)) ^ (r - 1) := by
  rw [bsplineLocal, bsplinePiece, Polynomial.sum_comp]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hl)
  rw [mul_comp, C_comp, pow_comp, sub_comp, X_comp, C_comp, Nat.cast_sub hl', C_sub]
  ring

/-- The B-splines on `[0, 1)` have degree `< r`. -/
theorem bsplineLocal_mem {r : ℕ} (hr : 1 ≤ r) (j : ℕ) : bsplineLocal r j ∈ degreeLT ℂ r := by
  rw [bsplineLocal_eq]
  exact Submodule.sum_mem _ fun l _ => by
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (pow_mem_degreeLT hr (natDegree_X_add_C _).le)

/-- **The shifted powers `(X + m)^(r-1)`, `m < r`, are linearly independent**: their
coefficients give the system `∑_m g_m m^e = 0`, `e < r`, with a Vandermonde matrix. -/
theorem linearIndependent_X_add_C_pow (r : ℕ) :
    LinearIndependent ℂ (fun m : Fin r => (X + C ((m : ℕ) : ℂ)) ^ (r - 1)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcoeff : ∀ d : ℕ,
      ∑ m : Fin r, g m * (((m : ℕ) : ℂ) ^ (r - 1 - d) * ((r - 1).choose d : ℂ)) = 0 := fun d => by
    have h := congrArg (fun P => P.coeff d) hg
    simpa only [finsetSum_coeff, coeff_smul, coeff_X_add_C_pow, smul_eq_mul, coeff_zero]
      using h
  have hv : Matrix.vecMul g (Matrix.vandermonde (fun m : Fin r => ((m : ℕ) : ℂ))) = 0 := by
    funext e
    have h := hcoeff (r - 1 - e)
    rw [show r - 1 - (r - 1 - e) = e by omega] at h
    have hc : ((r - 1).choose (r - 1 - e) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
    simp only [← mul_assoc] at h
    rw [← sum_mul] at h
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    exact (mul_eq_zero.1 h).resolve_right hc
  have hdet : (Matrix.vandermonde (fun m : Fin r => ((m : ℕ) : ℂ))).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.2 fun a b hab => Fin.ext (by exact_mod_cast hab)
  exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv) i

/-- The shifted powers as elements of the polynomials of degree `< r`. -/
noncomputable def shiftedPow {r : ℕ} (hr : 1 ≤ r) (m : Fin r) : degreeLT ℂ r :=
  ⟨(X + C ((m : ℕ) : ℂ)) ^ (r - 1), pow_mem_degreeLT hr (natDegree_X_add_C _).le⟩

/-- The shifted powers span the polynomials of degree `< r`. -/
theorem top_le_span_shiftedPow {r : ℕ} (hr : 1 ≤ r) :
    ⊤ ≤ Submodule.span ℂ (Set.range (shiftedPow hr)) := by
  have hli : LinearIndependent ℂ (shiftedPow hr) := by
    have h := linearIndependent_X_add_C_pow r
    exact LinearIndependent.of_comp (degreeLT ℂ r).subtype h
  have := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_degreeLT])
  exact this.ge

/-- The B-splines on `[0, 1)` as elements of the polynomials of degree `< r`. -/
noncomputable def bsplineVec {r : ℕ} (hr : 1 ≤ r) (j : Fin r) : degreeLT ℂ r :=
  ⟨bsplineLocal r j, bsplineLocal_mem hr j⟩

/-- `β_j = (1/(r-1)!) (X + j)^(r-1) + ∑_{1 ≤ l ≤ j} (…) (X + (j - l))^(r-1)`, the triangular
form in the shifted powers. -/
theorem bsplineVec_eq {r : ℕ} (hr : 1 ≤ r) (j : Fin r) :
    bsplineVec hr j = bsplineCoeff r 0 • shiftedPow hr j + ∑ l ∈ range j,
      bsplineCoeff r (l + 1) • shiftedPow hr ⟨j - (l + 1), by omega⟩ := by
  apply Subtype.ext
  simp only [bsplineVec, shiftedPow, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum,
    smul_eq_C_mul]
  rw [bsplineLocal_eq, sum_range_succ', Nat.sub_zero, add_comm]

/-- **The B-splines on `[0, 1)` span the polynomials of degree `< r`**: every shifted power is a
combination of them, by induction along the triangular form. -/
theorem top_le_span_bsplineVec {r : ℕ} (hr : 1 ≤ r) :
    ⊤ ≤ Submodule.span ℂ (Set.range (bsplineVec hr)) := by
  refine (top_le_span_shiftedPow hr).trans (Submodule.span_le.2 ?_)
  rintro _ ⟨⟨m, hm⟩, rfl⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hc : bsplineCoeff r 0 ≠ 0 := by
      simp [bsplineCoeff, Nat.factorial_ne_zero]
    have h := bsplineVec_eq hr ⟨m, hm⟩
    have hsum : ∑ l ∈ range m, bsplineCoeff r (l + 1) • shiftedPow hr ⟨m - (l + 1), by omega⟩ ∈
        Submodule.span ℂ (Set.range (bsplineVec hr)) :=
      Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (ih (m - (l + 1))
        (by have := mem_range.1 hl; omega) (by omega))
    have hβ : bsplineVec hr ⟨m, hm⟩ ∈ Submodule.span ℂ (Set.range (bsplineVec hr)) :=
      Submodule.subset_span ⟨_, rfl⟩
    have hrepr : shiftedPow hr ⟨m, hm⟩ = (bsplineCoeff r 0)⁻¹ •
        (bsplineVec hr ⟨m, hm⟩ - ∑ l ∈ range m,
          bsplineCoeff r (l + 1) • shiftedPow hr ⟨m - (l + 1), by omega⟩) := by
      rw [h, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hrepr]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hβ hsum)

/-- **The B-spline basis** of the polynomials of degree `< r` on `[0, 1)`. -/
noncomputable def bsplineBasis {r : ℕ} (hr : 1 ≤ r) : Module.Basis (Fin r) ℂ (degreeLT ℂ r) :=
  basisOfTopLeSpanOfCardEqFinrank (bsplineVec hr) (top_le_span_bsplineVec hr)
    (by rw [Fintype.card_fin, finrank_degreeLT])

/-- The elements of the B-spline basis. -/
theorem bsplineBasis_apply {r : ℕ} (hr : 1 ≤ r) (j : Fin r) :
    bsplineBasis hr j = bsplineVec hr j := by
  rw [bsplineBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

/-! ### Coordinates in the B-spline basis -/

/-- Splitting off the last term of a sum over `range r`, `r ≥ 1`. -/
theorem sum_range_eq_add_last {M : Type*} [AddCommMonoid M] {r : ℕ} (hr : 1 ≤ r) (f : ℕ → M) :
    ∑ k ∈ range r, f k = ∑ k ∈ range (r - 1), f k + f (r - 1) := by
  conv_lhs => rw [show r = r - 1 + 1 by omega]
  rw [sum_range_succ]

/-- Splitting off the first term of a sum over `range r`, `r ≥ 1`. -/
theorem sum_range_eq_first_add {M : Type*} [AddCommMonoid M] {r : ℕ} (hr : 1 ≤ r)
    (f : ℕ → M) : ∑ k ∈ range r, f k = f 0 + ∑ k ∈ range (r - 1), f (k + 1) := by
  conv_lhs => rw [show r = r - 1 + 1 by omega]
  rw [sum_range_succ', add_comm]

open Classical in
/-- The **coordinates** of a polynomial `P` of degree `< r` in the B-spline basis on `[0, 1)`:
`P = ∑_{j < r} a_j β_j` (`0` for `j ≥ r` or `P` of higher degree). -/
noncomputable def bcoord {r : ℕ} (hr : 1 ≤ r) (P : ℂ[X]) (j : ℕ) : ℂ :=
  if h : P ∈ degreeLT ℂ r ∧ j < r then (bsplineBasis hr).repr ⟨P, h.1⟩ ⟨j, h.2⟩ else 0

/-- **Expansion in the B-spline basis**: `P = ∑_{j < r} a_j β_j`. -/
theorem sum_bcoord {r : ℕ} (hr : 1 ≤ r) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) :
    ∑ j ∈ range r, bcoord hr P j • bsplineLocal r j = P := by
  have h := congrArg Subtype.val ((bsplineBasis hr).sum_repr ⟨P, hP⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, bsplineBasis_apply, bsplineVec] at h
  rw [← Fin.sum_univ_eq_sum_range (fun j => bcoord hr P j • bsplineLocal r j)]
  refine (sum_congr rfl fun j _ => ?_).trans h
  rw [bcoord, dite_eq_left ⟨hP, j.2⟩]

/-- **The coordinates are unique**: if `P = ∑_{j < r} c_j β_j`, then the `c_j` are the
coordinates. -/
theorem bcoord_eq_of_sum {r : ℕ} (hr : 1 ≤ r) {P : ℂ[X]} (c : ℕ → ℂ)
    (h : ∑ j ∈ range r, c j • bsplineLocal r j = P) {j : ℕ} (hj : j < r) :
    bcoord hr P j = c j := by
  have hP : P ∈ degreeLT ℂ r := h ▸ Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (bsplineLocal_mem hr j)
  have hli := (bsplineBasis hr).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (fun k => bcoord hr P k - c k) (by
    apply Subtype.ext
    simp only [sub_smul, sum_sub_distrib, Submodule.coe_sub, Submodule.coe_sum,
      Submodule.coe_smul, bsplineBasis_apply, bsplineVec, Submodule.coe_zero]
    rw [Fin.sum_univ_eq_sum_range (fun k => bcoord hr P k • bsplineLocal r k),
      Fin.sum_univ_eq_sum_range (fun k => c k • bsplineLocal r k), sum_bcoord hr hP, h, sub_self])
    ⟨j, hj⟩
  exact sub_eq_zero.1 h0

/-- `β_j(X + 1) = β_{j+1} - (-1)^(j+1) C(r, j+1)/(r-1)! X^(r-1)`. -/
theorem bsplineLocal_comp_add_one (r j : ℕ) :
    (bsplineLocal r j).comp (X + C 1) =
      bsplineLocal r (j + 1) - C (bsplineCoeff r (j + 1)) * X ^ (r - 1) := by
  have hL : (bsplineLocal r j).comp (X + C 1) =
      (bsplinePiece r j).comp (X + C ((j + 1 : ℕ) : ℂ)) := by
    rw [bsplineLocal, comp_assoc]
    congr 1
    simp only [add_comp, X_comp, C_comp, Nat.cast_succ, C_add, C_1]
    ring
  have hR : bsplineLocal r (j + 1) = (bsplinePiece r j).comp (X + C ((j + 1 : ℕ) : ℂ)) +
      C (bsplineCoeff r (j + 1)) * X ^ (r - 1) := by
    rw [bsplineLocal, bsplinePiece_succ, add_comp, mul_comp, C_comp, pow_comp, sub_comp, X_comp,
      C_comp, add_sub_cancel_right]
  rw [hL, hR, add_sub_cancel_right]

/-- `β_0 = X^(r-1)/(r-1)!`. -/
theorem bsplineLocal_zero (r : ℕ) : bsplineLocal r 0 = C (bsplineCoeff r 0) * X ^ (r - 1) := by
  simp [bsplineLocal, bsplinePiece]

/-- `β_r = 0`. -/
theorem bsplineLocal_top {r : ℕ} (hr : 1 ≤ r) : bsplineLocal r r = 0 := by
  rw [bsplineLocal, bsplinePiece_top hr, zero_comp]

/-- **The coordinates move by one under a shift by `1`**: the coordinate `j + 1` of `P(X + 1)` is
the coordinate `j` of `P`. -/
theorem bcoord_comp_add_one {r : ℕ} (hr : 1 ≤ r) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) {j : ℕ}
    (hj : j + 1 < r) : bcoord hr (P.comp (X + C 1)) (j + 1) = bcoord hr P j := by
  have hc0 : bsplineCoeff r 0 ≠ 0 := by simp [bsplineCoeff, Nat.factorial_ne_zero]
  -- the coordinates of `P(X + 1)`
  have h1 : P.comp (X + C 1) = ∑ k ∈ range r, bcoord hr P k • bsplineLocal r (k + 1) -
      C (∑ k ∈ range r, bcoord hr P k * bsplineCoeff r (k + 1)) * X ^ (r - 1) := by
    conv_lhs => rw [← sum_bcoord hr hP]
    rw [Polynomial.sum_comp]
    simp only [smul_eq_C_mul, mul_comp, C_comp, bsplineLocal_comp_add_one, mul_sub,
      sum_sub_distrib, map_sum, sum_mul, C_mul, mul_assoc]
  have h2 : ∑ k ∈ range r, bcoord hr P k • bsplineLocal r (k + 1) =
      ∑ k ∈ range (r - 1), bcoord hr P k • bsplineLocal r (k + 1) := by
    rw [sum_range_eq_add_last hr, Nat.sub_add_cancel hr, bsplineLocal_top hr, smul_zero, add_zero]
  have hexp : ∑ k ∈ range r, (if k = 0 then
      -(∑ k ∈ range r, bcoord hr P k * bsplineCoeff r (k + 1)) / bsplineCoeff r 0
      else bcoord hr P (k - 1)) • bsplineLocal r k = P.comp (X + C 1) := by
    rw [h1, h2, sum_range_eq_first_add hr]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, bsplineLocal_zero,
      smul_eq_C_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hc0, C_neg, neg_mul]
    ring
  rw [bcoord_eq_of_sum hr _ hexp hj]
  simp

/-! ### B-spline coefficients of polynomials -/

/-- Translates of polynomials of degree `< r` have degree `< r`: Mathlib's
`Polynomial.taylor_mem_degreeLT`, since `taylor a P = P.comp (X + C a)` (`Polynomial.taylor_apply`),
stated in the `comp` form that the rewrites below need. -/
theorem comp_X_add_C_mem {r : ℕ} {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (a : ℂ) :
    P.comp (X + C a) ∈ degreeLT ℂ r :=
  (taylor_mem_degreeLT (r := a)).2 hP

/-- The **B-spline coefficient** `c_n(P)` of a polynomial `P`: the coordinate of `N_r(· - n)` in
the expansion of `P` on `[n, n + 1)`. -/
noncomputable def bsplineCoef {r : ℕ} (hr : 1 ≤ r) (P : ℂ[X]) (n : ℤ) : ℂ :=
  bcoord hr (P.comp (X + C (n : ℂ))) 0

/-- **Consistency of the coefficients**: on `[i, i + 1)` the coordinate `j` of `P(X + i)` is the
coefficient `c_{i-j}(P)` of the B-spline `N_r(· - (i - j))`, whatever the interval. -/
theorem bcoord_comp_eq_bsplineCoef {r : ℕ} (hr : 1 ≤ r) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r)
    (i : ℤ) {j : ℕ} (hj : j < r) :
    bcoord hr (P.comp (X + C (i : ℂ))) j = bsplineCoef hr P (i - j) := by
  induction j generalizing i with
  | zero => simp [bsplineCoef]
  | succ j ih =>
    have h : P.comp (X + C (i : ℂ)) = (P.comp (X + C ((i - 1 : ℤ) : ℂ))).comp (X + C 1) := by
      rw [comp_assoc]
      congr 1
      rw [add_comp, X_comp, C_comp]
      push_cast
      simp only [C_sub, C_1]
      ring
    rw [h, bcoord_comp_add_one hr (comp_X_add_C_mem hP _) hj, ih (i - 1) (by omega)]
    congr 1
    push_cast
    ring

/-- The **cardinal B-spline** `N_r` of order `r`: the piece `B_j` on `[j, j + 1)`, `0 ≤ j < r`,
and `0` outside `[0, r)`. -/
noncomputable def bspline (r : ℕ) (x : ℝ) : ℂ :=
  if 0 ≤ x ∧ x < r then polyFun (bsplinePiece r ⌊x⌋₊) x else 0

/-- On `[j, j + 1)`, `j < r`, the B-spline is its piece `B_j`. -/
theorem bspline_eq_piece {r j : ℕ} (hj : j < r) {x : ℝ} (hx : x ∈ Set.Ico (j : ℝ) (j + 1)) :
    bspline r x = polyFun (bsplinePiece r j) x := by
  have h0 : 0 ≤ x := (Nat.cast_nonneg j).trans hx.1
  have hfl : ⌊x⌋₊ = j := (Nat.floor_eq_iff h0).2 hx
  have hxr : x < r := hx.2.trans_le (by exact_mod_cast hj)
  simp only [bspline, h0, hxr, and_self, ↓reduceIte, hfl]

/-- The B-spline vanishes left of `0`. -/
theorem bspline_eq_zero_of_lt (r : ℕ) {x : ℝ} (hx : x < 0) : bspline r x = 0 := by
  simp only [bspline, not_le.2 hx, false_and, ↓reduceIte]

/-- The B-spline vanishes right of `r`. -/
theorem bspline_eq_zero_of_ge {r : ℕ} {x : ℝ} (hx : (r : ℝ) ≤ x) : bspline r x = 0 := by
  simp only [bspline, not_lt.2 hx, and_false, ↓reduceIte]

/-- `N_r(x - (i - j)) = β_j(x - i)` for `x ∈ [i, i + 1)` and `j < r`. -/
theorem bspline_sub_eq {r : ℕ} {i : ℤ} {j : ℕ} (hj : j < r) {x : ℝ}
    (hx : x ∈ Set.Ico (i : ℝ) (i + 1)) :
    bspline r (x - ((i - j : ℤ) : ℝ)) = polyFun (bsplineLocal r j) (x - i) := by
  have hmem : x - ((i - j : ℤ) : ℝ) ∈ Set.Ico (j : ℝ) (j + 1) := by
    push_cast
    constructor <;> linarith [hx.1, hx.2]
  rw [bspline_eq_piece hj hmem]
  simp only [polyFun, bsplineLocal, eval_comp, eval_add, eval_X, eval_C]
  congr 1
  push_cast
  ring

/-- **Polynomials are combinations of B-splines** (Marsden's identity): for `P` of degree `< r`
and `x ∈ [i, i + 1)`, `P(x) = ∑_{j < r} c_{i-j}(P) N_r(x - (i - j))`, with the coefficients
`c_n(P)` independent of the interval. -/
theorem polyFun_eq_sum_bsplineCoef {r : ℕ} (hr : 1 ≤ r) {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r)
    {i : ℤ} {x : ℝ} (hx : x ∈ Set.Ico (i : ℝ) (i + 1)) :
    polyFun P x =
      ∑ j ∈ range r, bsplineCoef hr P (i - j) * bspline r (x - ((i - j : ℤ) : ℝ)) := by
  have hexp := sum_bcoord hr (comp_X_add_C_mem hP (i : ℂ))
  have hval : polyFun P x = polyFun (P.comp (X + C (i : ℂ))) (x - i) := by
    simp only [polyFun, eval_comp, eval_add, eval_X, eval_C]
    congr 1
    push_cast
    ring
  rw [hval, ← hexp]
  simp only [polyFun, eval_finsetSum, eval_smul, smul_eq_mul]
  refine sum_congr rfl fun j hj => ?_
  rw [bcoord_comp_eq_bsplineCoef hr hP i (mem_range.1 hj), bspline_sub_eq (mem_range.1 hj) hx,
    polyFun]

end Interval
