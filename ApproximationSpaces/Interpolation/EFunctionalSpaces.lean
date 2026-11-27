/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Interpolation.EFunctionalModuli
public import ApproximationSpaces.Dyadic

/-!
# The calculus of the E-functional: homogeneity, embeddings, maps and Pietsch's form

For a couple `A = (N₀, N₁)` on an abelian group (`InterpCouple`) with the E-functional
`E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}` (`InterpCouple.eFunctional`) and the dyadic norm
`‖u‖^dy_{s,q} = N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}` (`InterpCouple.eNormDyadic`), this file
collects the facts that the Besov spaces of a scheme of functions in `L_p`, `0 < p ≤ ∞`, need.
They hold for the quasi-norm `‖·‖_p` with `p < 1`: the hypothesis on `N₀` is homogeneity. The
Besov proofs also use the complexity of an image (`InterpCouple.complexity_norm1_map_le`) and
near-best sequences with decreasing tolerances (`InterpCouple.exists_nearBest_eFunctional`,
`InterpCouple.antitone_eFunctional_add_dyadicWeight`), all three in
`ApproximationSpaces.Interpolation.EFunctional`; the blocks of a near-best sequence satisfy
`N₀(b_{k+1} - b_k)^ρ ≤ 2 e_k^ρ` for an even `N₀` with subadditive `N₀^ρ`
(`InterpCouple.norm0_sub_succ_rpow_le_of_nearBest`, in
`ApproximationSpaces.Interpolation.EFunctionalModuli`).

* **Homogeneity**: `E(t, c u) ≤ |c| E(t, u)` and `‖c u‖^dy_{s,q} ≤ |c| ‖u‖^dy_{s,q}` if
  `N₀(c a) ≤ |c| N₀(a)`, multiplication by `c ≠ 0` does not increase the complexity and
  `N₁(0) = 0` (`InterpCouple.eFunctional_smul_le`, `InterpCouple.eNormDyadic_smul_le`).
* **Embeddings**: the dyadic norm decreases in the fine index, `‖u‖^dy_{s,r} ≤ ‖u‖^dy_{s,q}` for
  `0 < q ≤ r`, and in the smoothness, `‖u‖^dy_{t,r} ≤ γ_{s-t,r} ‖u‖^dy_{s,q}` for `t < s`,
  `q ≠ 0` and every `r` (`InterpCouple.eNormDyadic_mono_exponent`,
  `InterpCouple.eNormDyadic_le_of_lt`).
* **Maps**: if `N₁(0) = 0`, an additive map `T` with `N₀'(T a) ≤ M N₀(a)`, `M < ∞`, and
  `N₁'(T a) ≤ N₁(a)` gives `E'(t, T u) ≤ M E(t, u)` (`InterpCouple.eFunctional_map_le`), and
  then `‖T u‖^P_{s,q} ≤ M ‖u‖^P_{s,q}` for Pietsch's form (`InterpCouple.eNormPietsch_map_le`).
* **Pietsch's form** `‖((n + 1)^(s - 1/q) E(n, u))_n‖_{ℓ_q}` (`InterpCouple.eNormPietsch`): for
  `s ≥ 0` it is at most `C_q 2^s` times the dyadic norm if `N₁(0) = 0`, and for `q ∈ (0, ∞]` the
  dyadic norm is at most `4 C_q² 2^s` times it if only `0` has complexity below `1`, with the
  constants of the dyadic form of `A^s_q`, `C_q = LpAddConst q`
  (`InterpCouple.eNormPietsch_le_eNormDyadic`, `InterpCouple.eNormDyadic_le_eNormPietsch`); for
  the complexity couple of an approximation scheme it is Pietsch's quasi-norm `‖f‖_{A^s_q}`
  (`ApproximationScheme.eNormPietsch_complexityCouple`).

The comparison of the two forms is Cauchy condensation for the decreasing sequence `E(n, u)`,
with `E(0, u)` in the role of `‖f‖ = E_0(f)` (`ENNReal.lqNorm_pow_mul_le_dyadic`,
`ENNReal.dyadic_le_lqNorm_pow_mul`), as for `A^s_q`
(`ApproximationScheme.approxNorm_le_approxNormDyadic'`,
`ApproximationScheme.approxNormDyadic_le_approxNorm'`).
-/

@[expose] public section

open scoped ENNReal

open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst)

namespace InterpCouple

variable {U : Type*} [AddCommGroup U] {A : InterpCouple U}

/-! ### Homogeneity -/

section Smul

variable [Module ℝ U]

/-- **Homogeneity of the E-functional**: if `N₀(c a) ≤ |c| N₀(a)` for all real `c` and all `a`,
multiplication by a real `c ≠ 0` does not increase the complexity, and `N₁(0) = 0`, then
`E(t, c u) ≤ |c| E(t, u)`. For `c ≠ 0` the substitution `b ↦ c b` keeps admissible elements
admissible; for `c = 0` the element `b = 0` is admissible, and `N₀(0) = 0` by the first
hypothesis with `c = 0`. -/
theorem eFunctional_smul_le (h10 : A.norm1 0 = 0)
    (h0 : ∀ (c : ℝ) (a : U), A.norm0 (c • a) ≤ ‖c‖ₑ * A.norm0 a)
    (h1 : ∀ c : ℝ, c ≠ 0 → ∀ a : U, A.norm1 (c • a) ≤ A.norm1 a) (c : ℝ) (t : ℝ≥0∞) (u : U) :
    A.eFunctional t (c • u) ≤ ‖c‖ₑ * A.eFunctional t u := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h00 : A.norm0 0 = 0 := by simpa using h0 0 0
    rw [zero_smul, eFunctional_zero_right h00 h10]
    exact zero_le
  rw [show ‖c‖ₑ * A.eFunctional t u = ⨅ b : {b : U // A.norm1 b ≤ t}, ‖c‖ₑ * A.norm0 (u - b) from
    ENNReal.mul_iInf_of_ne (eNorm_ne_zero.2 hc) eNorm_ne_top]
  refine le_iInf fun b => (eFunctional_le ((h1 c hc b).trans b.2)).trans ?_
  rw [← smul_sub]
  exact h0 c (u - b)

/-- **Homogeneity of the dyadic norm**: under the hypotheses of
`InterpCouple.eFunctional_smul_le`, `‖c u‖^dy_{s,q} ≤ |c| ‖u‖^dy_{s,q}` for the dyadic norm
`N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}`, termwise and by the homogeneity of the `ℓ_q` norm. -/
theorem eNormDyadic_smul_le (h10 : A.norm1 0 = 0)
    (h0 : ∀ (c : ℝ) (a : U), A.norm0 (c • a) ≤ ‖c‖ₑ * A.norm0 a)
    (h1 : ∀ c : ℝ, c ≠ 0 → ∀ a : U, A.norm1 (c • a) ≤ A.norm1 a) (c s : ℝ) (q : ℝ≥0∞)
    (u : U) : A.eNormDyadic s q (c • u) ≤ ‖c‖ₑ * A.eNormDyadic s q u := by
  have hL : lqNorm q (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (c • u))
      ≤ ‖c‖ₑ * lqNorm q (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun k => ?_
    calc dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (c • u)
        ≤ dyadicWeight s k * (‖c‖ₑ * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := by
          gcongr
          exact eFunctional_smul_le h10 h0 h1 c _ u
      _ = ‖c‖ₑ * (dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := mul_left_comm _ _ _
  rw [eNormDyadic, eNormDyadic, mul_add]
  exact add_le_add (h0 c u) hL

end Smul

/-! ### Embeddings of the dyadic norms -/

/-- **The dyadic norm decreases in the fine index**: `‖u‖^dy_{s,r} ≤ ‖u‖^dy_{s,q}` for
`0 < q ≤ r ≤ ∞`, also below `1`, by the monotonicity of the `ℓ_q` norms
(`ENNReal.lqNorm_le_lqNorm_of_le`). -/
theorem eNormDyadic_mono_exponent {q r : ℝ≥0∞} (hq0 : q ≠ 0) (hqr : q ≤ r) (s : ℝ) (u : U) :
    A.eNormDyadic s r u ≤ A.eNormDyadic s q u :=
  add_le_add le_rfl (ENNReal.lqNorm_le_lqNorm_of_le hq0 hqr _)

/-- **Lower smoothness with any fine index**: for `t < s`, `q ≠ 0` and every `r`,
`‖u‖^dy_{t,r} ≤ γ_{s-t,r} ‖u‖^dy_{s,q}` with `γ_{s-t,r} = dyadicGeomConst (s - t) r`, finite
since `s - t > 0`. Every term satisfies `2^(kt) E(2^k, u) ≤ 2^(-k(s-t)) L` with `L` the `ℓ_q`
part of `‖u‖^dy_{s,q}`, the geometric sequence has `ℓ_r` norm at most `γ_{s-t,r}`, and
`N₀(u) ≤ γ_{s-t,r} N₀(u)` since `γ_{s-t,r} ≥ 1` (`ENNReal.one_le_dyadicGeomConst`). -/
theorem eNormDyadic_le_of_lt {s t : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hts : t < s) (r : ℝ≥0∞)
    (u : U) :
    A.eNormDyadic t r u ≤ dyadicGeomConst (s - t) r * A.eNormDyadic s q u := by
  set L := lqNorm q fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u
  set γ := dyadicGeomConst (s - t) r
  have hterm : ∀ k : ℕ, dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u ≤
      L * dyadicWeight (-(s - t)) k := fun k => by
    calc dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u
        = dyadicWeight (-(s - t)) k *
            (dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := by
          rw [← mul_assoc, ← ENNReal.dyadicWeight_add, show -(s - t) + s = t by ring]
      _ ≤ dyadicWeight (-(s - t)) k * L := by
          gcongr
          exact ENNReal.le_lqNorm hq0
            (fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) k
      _ = L * dyadicWeight (-(s - t)) k := mul_comm _ _
  have hL : lqNorm r (fun k : ℕ => dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) ≤
      γ * L := by
    calc lqNorm r (fun k : ℕ => dyadicWeight t k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u)
        ≤ lqNorm r (fun k : ℕ => L * dyadicWeight (-(s - t)) k) := ENNReal.lqNorm_mono hterm
      _ = L * lqNorm r (dyadicWeight (-(s - t))) := ENNReal.lqNorm_const_mul _ _
      _ ≤ L * γ := by
          gcongr
          exact ENNReal.lqNorm_dyadicWeight_neg_le_dyadicGeomConst (sub_nonneg.2 hts.le)
      _ = γ * L := mul_comm _ _
  calc A.eNormDyadic t r u
      = A.norm0 u + lqNorm r (fun k : ℕ => dyadicWeight t k *
          A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := rfl
    _ ≤ γ * A.norm0 u + γ * L :=
        add_le_add (le_mul_of_one_le_left' (ENNReal.one_le_dyadicGeomConst _ _)) hL
    _ = γ * A.eNormDyadic s q u := by rw [eNormDyadic, mul_add]

/-! ### Maps -/

/-- **The E-functional under an additive map**: if `N₁(0) = 0`, `T : U → V` is additive,
`N₀'(T a) ≤ M N₀(a)` and `N₁'(T a) ≤ N₁(a)` for every `a`, and `M < ∞`, then
`E'(t, T u) ≤ M E(t, u)`: the image `T b` of an admissible `b` is admissible, and
`T u - T b = T (u - b)`. For `M = 0` the admissible element `b = 0` gives
`E'(t, T u) ≤ N₀'(T u) = 0`. The analogue for the K-functional is
`InterpCouple.kFunctional_map_le`. -/
theorem eFunctional_map_le {V : Type*} [AddCommGroup V] {B : InterpCouple V} (T : U →+ V)
    (h10 : A.norm1 0 = 0) {M : ℝ≥0∞} (hM : M ≠ ∞) (h0 : ∀ a, B.norm0 (T a) ≤ M * A.norm0 a)
    (h1 : ∀ a, B.norm1 (T a) ≤ A.norm1 a) (t : ℝ≥0∞) (u : U) :
    B.eFunctional t (T u) ≤ M * A.eFunctional t u := by
  rcases eq_or_ne M 0 with rfl | hM0
  · refine (eFunctional_le ((h1 0).trans (h10.trans_le zero_le))).trans ?_
    rw [map_zero, sub_zero, zero_mul]
    exact (h0 u).trans_eq (zero_mul _)
  rw [show M * A.eFunctional t u = ⨅ b : {b : U // A.norm1 b ≤ t}, M * A.norm0 (u - b) from
    ENNReal.mul_iInf_of_ne hM0 hM]
  refine le_iInf fun b => (eFunctional_le ((h1 b).trans b.2)).trans ?_
  rw [← map_sub]
  exact h0 _

/-! ### Pietsch's form -/

/-- **Pietsch's form** of the norm of the approximation space of a couple:
`‖((n + 1)^(s - 1/q) E(n, u))_{n ∈ ℕ}‖_{ℓ_q}`, the weights of Pietsch's quasi-norm of `A^s_q`
(`ApproximationScheme.approxNorm`) with the E-functional at the integers in place of the errors
`E_n(f)`. -/
noncomputable def eNormPietsch (A : InterpCouple U) (s : ℝ) (q : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  lqNorm q fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * A.eFunctional n u

/-- **Pietsch's form of `0`** is `0` if both norms vanish at `0`. -/
theorem eNormPietsch_zero (h00 : A.norm0 0 = 0) (h10 : A.norm1 0 = 0) (s : ℝ) (q : ℝ≥0∞) :
    A.eNormPietsch s q 0 = 0 := by
  simp [eNormPietsch, eFunctional_zero_right h00 h10, ENNReal.lqNorm_zero_right]

/-- **Pietsch's form under an additive map**: under the hypotheses of
`InterpCouple.eFunctional_map_le`, `‖T u‖^P_{s,q} ≤ M ‖u‖^P_{s,q}` for every `s` and `q`,
termwise. -/
theorem eNormPietsch_map_le {V : Type*} [AddCommGroup V] {B : InterpCouple V} (T : U →+ V)
    (h10 : A.norm1 0 = 0) {M : ℝ≥0∞} (hM : M ≠ ∞) (h0 : ∀ a, B.norm0 (T a) ≤ M * A.norm0 a)
    (h1 : ∀ a, B.norm1 (T a) ≤ A.norm1 a) (s : ℝ) (q : ℝ≥0∞) (u : U) :
    B.eNormPietsch s q (T u) ≤ M * A.eNormPietsch s q u := by
  rw [eNormPietsch, eNormPietsch, ← ENNReal.lqNorm_const_mul]
  refine ENNReal.lqNorm_mono fun n => ?_
  calc ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * B.eFunctional n (T u)
      ≤ ((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * (M * A.eFunctional n u) := by
        gcongr
        exact eFunctional_map_le T h10 hM h0 h1 _ u
    _ = M * (((n + 1 : ℕ) : ℝ≥0∞) ^ (s - 1 / q.toReal) * A.eFunctional n u) :=
        mul_left_comm _ _ _

variable {s : ℝ} {q : ℝ≥0∞}

/-- **Pietsch's form by the dyadic norm**: if `N₁(0) = 0`, then for `s ≥ 0` and every `q`,
`‖u‖^P_{s,q} ≤ C_q 2^s ‖u‖^dy_{s,q}` with `C_q = LpAddConst q`, by Cauchy condensation for the
decreasing sequence `E(n, u)` (`ENNReal.lqNorm_pow_mul_le_dyadic`), whose first term is
`E(0, u) ≤ N₀(u)`. -/
theorem eNormPietsch_le_eNormDyadic (h10 : A.norm1 0 = 0) (hs : 0 ≤ s) (u : U) :
    A.eNormPietsch s q u ≤ LpAddConst q * 2 ^ s * A.eNormDyadic s q u := by
  refine (ENNReal.lqNorm_pow_mul_le_dyadic (antitone_eFunctional_natCast (A := A) u) hs).trans ?_
  rw [Nat.cast_zero, eNormDyadic]
  gcongr
  exact eFunctional_le_norm0 h10 u

/-- **The dyadic norm by Pietsch's form**: if only `0` has complexity below `1`, then for `s ≥ 0`
and `q ∈ (0, ∞]`, `‖u‖^dy_{s,q} ≤ 4 C_q² 2^s ‖u‖^P_{s,q}` with `C_q = LpAddConst q`
(`ENNReal.dyadic_le_lqNorm_pow_mul`), since the first term of the decreasing sequence `E(n, u)`
is `E(0, u) ≥ N₀(u)`. -/
theorem eNormDyadic_le_eNormPietsch (hdisc : ∀ b, A.norm1 b < 1 → b = 0) (hq0 : q ≠ 0)
    (hs : 0 ≤ s) (u : U) :
    A.eNormDyadic s q u ≤ LpAddConst q ^ 2 * 4 * 2 ^ s * A.eNormPietsch s q u := by
  refine le_trans ?_
    (ENNReal.dyadic_le_lqNorm_pow_mul (antitone_eFunctional_natCast (A := A) u) hq0 hs)
  rw [Nat.cast_zero, eNormDyadic]
  gcongr
  exact norm0_le_eFunctional_of_lt_one hdisc zero_lt_one u

/-- **Pietsch's form and the dyadic norm are finite together**: if `N₁(0) = 0` and only `0` has
complexity below `1`, then for `s ≥ 0` and `q ∈ (0, ∞]`, `‖u‖^P_{s,q} < ∞` iff
`‖u‖^dy_{s,q} < ∞`. -/
theorem eNormPietsch_lt_top_iff (h10 : A.norm1 0 = 0) (hdisc : ∀ b, A.norm1 b < 1 → b = 0)
    (hq0 : q ≠ 0) (hs : 0 ≤ s) {u : U} :
    A.eNormPietsch s q u < ∞ ↔ A.eNormDyadic s q u < ∞ := by
  have hC := ENNReal.LpAddConst_lt_top q
  constructor
  · intro h
    refine (eNormDyadic_le_eNormPietsch hdisc hq0 hs u).trans_lt (ENNReal.mul_lt_top ?_ h)
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_ne_top hC.ne).lt_top (by norm_num))
      (ENNReal.two_rpow_ne_top s).lt_top
  · intro h
    exact (eNormPietsch_le_eNormDyadic h10 hs u).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC (ENNReal.two_rpow_ne_top s).lt_top) h)

end InterpCouple

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : ℝ} {q : ℝ≥0∞}

/-- **Pietsch's form of the complexity couple is Pietsch's quasi-norm**: for an approximation
scheme `A`, `‖f‖^P_{s,q}` of its complexity couple is `‖f‖_{A^s_q}`, termwise since
`E(n, f) = E_n(f)` (`ApproximationScheme.eFunctional_complexityCouple`). -/
theorem eNormPietsch_complexityCouple (A : ApproximationScheme X) (f : X) :
    A.complexityCouple.eNormPietsch s q f = A.approxNorm s q f := by
  simp only [InterpCouple.eNormPietsch, eFunctional_complexityCouple, approxNorm]

end ApproximationScheme
