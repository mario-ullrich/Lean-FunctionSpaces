/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Interpolation.EFunctionalSpaces
public import ApproximationSpaces.Interpolation.ApproxSpaces

/-!
# Couples of E-spaces and Jackson's half of their representation

Let `A = (N₀, N₁)` be a couple on an abelian group (`InterpCouple`), with the E-functional
`E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}` and the dyadic norm
`‖u‖^dy_{s,q} = N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}` of its approximation space `E_{s,q}`
(`InterpCouple.eNormDyadic`). This file builds the two couples of E-spaces

* `(N₀, E_{r,q₁})` (`InterpCouple.leftECouple`), with the norms `N₀` and `‖·‖^dy_{r,q₁}`, and
* `(E_{s₀,q₀}, E_{s₁,q₁})` (`InterpCouple.eCouple`), with the norms `‖·‖^dy_{s₀,q₀}` and
  `‖·‖^dy_{s₁,q₁}`,

the analogues of `ApproximationScheme.leftApproxCouple` and `ApproximationScheme.approxCouple`
for a quasi-norm `N₀`, and proves Jackson's half of the representation
`E_{s,q} = (N₀, E_{r,q₁})_{s/r,q}` (Pietsch, J. Approx. Theory 32 (1981); DeVore–Popov,
LNM 1302 (1988); DeVore, Acta Numer. 7 (1998), §4.3, Theorem 2).

* **The couples**: for a couple quasi-normed with constant `C` whose complexity is subadditive,
  both couples are quasi-normed for every smoothness and every fine index, with the constants of
  the quasi-triangle inequality of the dyadic norm (`InterpCouple.isQuasiNormed_leftECouple`,
  `InterpCouple.isQuasiNormed_eCouple`, from `InterpCouple.eNormDyadic_add_le`,
  `InterpCouple.eNormDyadic_zero`, `InterpCouple.eNormDyadic_neg` and
  `InterpCouple.le_eAddConst`). On a real vector space they are homogeneous if `N₁(0) = 0`, `N₀`
  is homogeneous and multiplication by `c ≠ 0` does not increase the complexity
  (`InterpCouple.isHomogeneousCouple_leftECouple`, `InterpCouple.isHomogeneousCouple_eCouple`),
  and `(N₀, E_{r,q₁})` is ordered, `N₀ ≤ ‖·‖^dy_{r,q₁}`
  (`InterpCouple.norm0_le_leftECouple_norm1`).
* **Jackson's half**: let `N : U → [0, ∞]` satisfy Jackson's inequality
  `E(2^k, g) ≤ C_J 2^(-kr) N(g)` with `C_J < ∞`, as the dyadic norm of `E_{r,q₁}`, `q₁ ≠ 0`, does
  with `C_J = 1` (`InterpCouple.eFunctional_two_pow_le_dyadicWeight_mul`). Then
  `E(2^(k+1), u) ≤ C max(1, C_J) K(2^(-kr), u)` for the K-functional of the couple `(N₀, N)`
  (`InterpCouple.eFunctional_succ_le_kFunctional`), and for `r ≠ 0`, every `s` and every `q`,
  `‖u‖^dy_{s,q} ≤ eJacksonConst C C_J s q · (N₀(u) + ‖(2^(ks) K(2^(-kr), u))_k‖_{ℓ_q})`, the
  norm of `(N₀, N)` on the grid `t = 2^(-kr)` (`InterpCouple.eNormDyadic_le_interpNorm_of_jackson`).
  The quasi-triangle inequality of `N₀` enters once, at each level.
-/

@[expose] public section

open scoped ENNReal
open ENNReal (lqNorm dyadicWeight LpAddConst)

namespace InterpCouple

variable {U : Type*} [AddCommGroup U] {A : InterpCouple U} {C : ℝ≥0∞}

/-! ### The couples `(N₀, E_{r,q₁})` and `(E_{s₀,q₀}, E_{s₁,q₁})` -/

variable (A) in
/-- The **couple `(N₀, E_{r,q₁})`** of a couple `A = (N₀, N₁)`: the first norm `N₀` of `A` and the
dyadic norm `‖u‖^dy_{r,q₁} = N₀(u) + ‖(2^(kr) E(2^k, u))_k‖_{ℓ_{q₁}}` of its approximation space
`E_{r,q₁}`. It is the couple of the representation of `E_{s,q}`, `0 < s < r`, as an
interpolation space, the analogue of `ApproximationScheme.leftApproxCouple` (whose case `q₁ = ∞`
is `ApproximationScheme.reprCouple`). -/
noncomputable def leftECouple (r : ℝ) (q₁ : ℝ≥0∞) : InterpCouple U :=
  ⟨A.norm0, A.eNormDyadic r q₁⟩

variable (A) in
/-- The **couple `(E_{s₀,q₀}, E_{s₁,q₁})`** of a couple `A`: the dyadic norms `‖·‖^dy_{s₀,q₀}` and
`‖·‖^dy_{s₁,q₁}` of two of its approximation spaces, the analogue of
`ApproximationScheme.approxCouple`. -/
noncomputable def eCouple (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple U :=
  ⟨A.eNormDyadic s₀ q₀, A.eNormDyadic s₁ q₁⟩

/-- The first norm of `(N₀, E_{r,q₁})` is `N₀`. -/
@[simp]
theorem leftECouple_norm0 (r : ℝ) (q₁ : ℝ≥0∞) (u : U) :
    (A.leftECouple r q₁).norm0 u = A.norm0 u := rfl

/-- The second norm of `(N₀, E_{r,q₁})` is the dyadic norm of `E_{r,q₁}`. -/
@[simp]
theorem leftECouple_norm1 (r : ℝ) (q₁ : ℝ≥0∞) (u : U) :
    (A.leftECouple r q₁).norm1 u = A.eNormDyadic r q₁ u := rfl

/-- The first norm of `(E_{s₀,q₀}, E_{s₁,q₁})` is the dyadic norm of `E_{s₀,q₀}`. -/
@[simp]
theorem eCouple_norm0 (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) (u : U) :
    (A.eCouple s₀ q₀ s₁ q₁).norm0 u = A.eNormDyadic s₀ q₀ u := rfl

/-- The second norm of `(E_{s₀,q₀}, E_{s₁,q₁})` is the dyadic norm of `E_{s₁,q₁}`. -/
@[simp]
theorem eCouple_norm1 (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) (u : U) :
    (A.eCouple s₀ q₀ s₁ q₁).norm1 u = A.eNormDyadic s₁ q₁ u := rfl

/-- **`(N₀, E_{r,q₁})` is ordered**: `N₀(u) ≤ 1 · ‖u‖^dy_{r,q₁}` for every `u`, since `N₀(u)` is the
first term of the dyadic norm. -/
theorem norm0_le_leftECouple_norm1 (r : ℝ) (q₁ : ℝ≥0∞) (u : U) :
    (A.leftECouple r q₁).norm0 u ≤ 1 * (A.leftECouple r q₁).norm1 u := by
  rw [one_mul]
  exact le_self_add

/-- **`(N₀, E_{r,q₁})` is quasi-normed**: if `A` is quasi-normed with constant `C` and its
complexity is subadditive, then for every `r` and every `q₁` the couple `(N₀, E_{r,q₁})` is
quasi-normed with constant `eAddConst C r q₁`: the dyadic norm vanishes at `0`, is even and
satisfies the quasi-triangle inequality with this constant (`InterpCouple.eNormDyadic_zero`,
`InterpCouple.eNormDyadic_neg`, `InterpCouple.eNormDyadic_add_le`), and `N₀` satisfies it since
`C ≤ eAddConst C r q₁` (`InterpCouple.le_eAddConst`). -/
theorem isQuasiNormed_leftECouple (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (r : ℝ) (q₁ : ℝ≥0∞) :
    (A.leftECouple r q₁).IsQuasiNormed (eAddConst C r q₁) where
  ne_top := eAddConst_ne_top hA.ne_top r q₁
  norm0_zero := hA.norm0_zero
  norm1_zero := eNormDyadic_zero hA.norm0_zero hA.norm1_zero r q₁
  norm0_neg := hA.norm0_neg
  norm1_neg := eNormDyadic_neg hA.norm0_neg hA.norm1_neg r q₁
  norm0_add_le a b := (hA.norm0_add_le a b).trans (mul_le_mul_left (le_eAddConst C r q₁) _)
  norm1_add_le := eNormDyadic_add_le hA h1 r q₁

/-- **`(E_{s₀,q₀}, E_{s₁,q₁})` is quasi-normed**: if `A` is quasi-normed with constant `C` and its
complexity is subadditive, then for all smoothness indices and fine indices the couple of the two
dyadic norms is quasi-normed with constant `max(eAddConst C s₀ q₀, eAddConst C s₁ q₁)`
(`InterpCouple.eNormDyadic_add_le`). -/
theorem isQuasiNormed_eCouple (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ)
    (q₁ : ℝ≥0∞) :
    (A.eCouple s₀ q₀ s₁ q₁).IsQuasiNormed (max (eAddConst C s₀ q₀) (eAddConst C s₁ q₁)) where
  ne_top := max_ne_top (eAddConst_ne_top hA.ne_top s₀ q₀) (eAddConst_ne_top hA.ne_top s₁ q₁)
  norm0_zero := eNormDyadic_zero hA.norm0_zero hA.norm1_zero s₀ q₀
  norm1_zero := eNormDyadic_zero hA.norm0_zero hA.norm1_zero s₁ q₁
  norm0_neg := eNormDyadic_neg hA.norm0_neg hA.norm1_neg s₀ q₀
  norm1_neg := eNormDyadic_neg hA.norm0_neg hA.norm1_neg s₁ q₁
  norm0_add_le a b := (eNormDyadic_add_le hA h1 s₀ q₀ a b).trans
    (mul_le_mul_left (le_max_left _ _) _)
  norm1_add_le a b := (eNormDyadic_add_le hA h1 s₁ q₁ a b).trans
    (mul_le_mul_left (le_max_right _ _) _)

section Smul

variable [Module ℝ U]

/-- **`(N₀, E_{r,q₁})` is homogeneous** on a real vector space if `N₁(0) = 0`,
`N₀(c a) ≤ |c| N₀(a)` for all real `c`, and multiplication by `c ≠ 0` does not increase the
complexity (`InterpCouple.eNormDyadic_smul_le`). -/
theorem isHomogeneousCouple_leftECouple (h10 : A.norm1 0 = 0)
    (h0 : ∀ (c : ℝ) (a : U), A.norm0 (c • a) ≤ ‖c‖ₑ * A.norm0 a)
    (h1 : ∀ c : ℝ, c ≠ 0 → ∀ a : U, A.norm1 (c • a) ≤ A.norm1 a) (r : ℝ) (q₁ : ℝ≥0∞) :
    (A.leftECouple r q₁).IsHomogeneousCouple where
  norm0_smul_le := h0
  norm1_smul_le c a := eNormDyadic_smul_le h10 h0 h1 c r q₁ a

/-- **`(E_{s₀,q₀}, E_{s₁,q₁})` is homogeneous** on a real vector space under the hypotheses of
`InterpCouple.isHomogeneousCouple_leftECouple` (`InterpCouple.eNormDyadic_smul_le`). -/
theorem isHomogeneousCouple_eCouple (h10 : A.norm1 0 = 0)
    (h0 : ∀ (c : ℝ) (a : U), A.norm0 (c • a) ≤ ‖c‖ₑ * A.norm0 a)
    (h1 : ∀ c : ℝ, c ≠ 0 → ∀ a : U, A.norm1 (c • a) ≤ A.norm1 a) (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ)
    (q₁ : ℝ≥0∞) :
    (A.eCouple s₀ q₀ s₁ q₁).IsHomogeneousCouple where
  norm0_smul_le c a := eNormDyadic_smul_le h10 h0 h1 c s₀ q₀ a
  norm1_smul_le c a := eNormDyadic_smul_le h10 h0 h1 c s₁ q₁ a

end Smul

/-! ### Jackson's half -/

/-- **Jackson's inequality for `E_{r,q₁}`**: for `q₁ ≠ 0`, every `b` and every `k`,
`E(2^k, b) ≤ 1 · 2^(-kr) ‖b‖^dy_{r,q₁}`, since `2^(kr) E(2^k, b)` is one term of the `ℓ_{q₁}` part
of the dyadic norm (`ENNReal.le_dyadicWeight_neg_mul_lqNorm`). -/
theorem eFunctional_two_pow_le_dyadicWeight_mul {r : ℝ} {q₁ : ℝ≥0∞} (hq₁ : q₁ ≠ 0) (k : ℕ)
    (b : U) :
    A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) b ≤ 1 * dyadicWeight (-r) k * A.eNormDyadic r q₁ b := by
  rw [one_mul]
  exact (ENNReal.le_dyadicWeight_neg_mul_lqNorm hq₁ r
    (fun j : ℕ => A.eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) b) k).trans
    (mul_le_mul_right le_add_self _)

/-- **Jackson's half at one level**: let `A` be quasi-normed with constant `C` and subadditive
complexity, and let `N : U → [0, ∞]` satisfy Jackson's inequality
`E(2^k, g) ≤ C_J 2^(-kr) N(g)` for all `k` and `g`, with `C_J < ∞`. Then
`E(2^(k+1), u) ≤ C max(1, C_J) K(2^(-kr), u)` for the K-functional of the couple `(N₀, N)`:
for every `g`, `E(2^(k+1), u) ≤ C (E(2^k, u - g) + E(2^k, g)) ≤ C (N₀(u - g) + C_J 2^(-kr) N(g))`
(`InterpCouple.eFunctional_add_le`), and the infimum over `g` passes to the K-functional
(`InterpCouple.le_add_mul_kFunctional`). The hypothesis `C_J < ∞` is needed: on `U = ℝ²` with
`N₀(x, y) = |x| + |y|`, only `0` as approximant, `N(x, 0) = |x|` and `N(x, y) = |y|` for `y ≠ 0`,
Jackson's inequality holds with `C_J = ∞` and `K(t, (1, 0)) = 0` along `g = (1, 1/n)`, while
`E(2^(k+1), (1, 0)) = 1`. -/
theorem eFunctional_succ_le_kFunctional (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {N : U → ℝ≥0∞} {CJ : ℝ≥0∞}
    (hCJ : CJ ≠ ∞) {r : ℝ}
    (hJ : ∀ k g, A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) g ≤ CJ * dyadicWeight (-r) k * N g)
    (k : ℕ) (u : U) :
    A.eFunctional ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) u ≤
      C * max 1 CJ * (⟨A.norm0, N⟩ : InterpCouple U).kFunctional (dyadicWeight (-r) k) u := by
  have hc : C * max 1 CJ ≠ ∞ := ENNReal.mul_ne_top hA.ne_top (max_ne_top ENNReal.one_ne_top hCJ)
  have h2 : ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) = ((2 ^ k : ℕ) : ℝ≥0∞) + ((2 ^ k : ℕ) : ℝ≥0∞) := by
    push_cast
    ring
  have hM : ∀ g, A.norm0 (u - g) + CJ * dyadicWeight (-r) k * N g ≤
      max 1 CJ * (A.norm0 (u - g) + dyadicWeight (-r) k * N g) := fun g => by
    rw [mul_add, mul_assoc CJ]
    gcongr
    · exact le_mul_of_one_le_left' (le_max_left _ _)
    · exact le_max_right _ _
  refine (le_add_mul_kFunctional (A := ⟨A.norm0, N⟩) (X := 0) (t := dyadicWeight (-r) k) hc
    fun g => ?_).trans_eq (zero_add _)
  calc A.eFunctional ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) u
      = A.eFunctional (((2 ^ k : ℕ) : ℝ≥0∞) + ((2 ^ k : ℕ) : ℝ≥0∞)) ((u - g) + g) := by
        rw [h2, sub_add_cancel]
    _ ≤ C * (A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (u - g) +
          A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) g) :=
        eFunctional_add_le hA.ne_top hA.norm1_zero hA.norm0_add_le h1 _ _ _ _
    _ ≤ C * (A.norm0 (u - g) + CJ * dyadicWeight (-r) k * N g) := by
        gcongr
        · exact eFunctional_le_norm0 hA.norm1_zero _
        · exact hJ k g
    _ ≤ C * (max 1 CJ * (A.norm0 (u - g) + dyadicWeight (-r) k * N g)) :=
        mul_le_mul_right (hM g) C
    _ = 0 + C * max 1 CJ * (A.norm0 (u - g) + dyadicWeight (-r) k * N g) := by ring

/-- The constant `1 + C_q (1 + 2^s C max(1, C_J))` of Jackson's half of the representation of
`E_{s,q}`, with Mathlib's constant `C_q = LpAddConst q`, for a couple quasi-normed with constant
`C` and Jackson's inequality with constant `C_J`. -/
noncomputable def eJacksonConst (C CJ : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  1 + LpAddConst q * (1 + 2 ^ s * C * max 1 CJ)

/-- The constant `eJacksonConst C C_J s q` is finite for `C, C_J < ∞`. -/
theorem eJacksonConst_ne_top (hC : C ≠ ∞) {CJ : ℝ≥0∞} (hCJ : CJ ≠ ∞) (s : ℝ) (q : ℝ≥0∞) :
    eJacksonConst C CJ s q ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top q).ne
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.two_rpow_ne_top s) hC) (max_ne_top ENNReal.one_ne_top hCJ)⟩)⟩

/-- **Jackson's half of the representation of `E_{s,q}`**: under the hypotheses of
`InterpCouple.eFunctional_succ_le_kFunctional` and `r ≠ 0`, for every `s`, every `q` and every
`u`, `‖u‖^dy_{s,q} ≤ eJacksonConst C C_J s q · ‖u‖_{s/r,r,q}`, where
`‖u‖_{s/r,r,q} = N₀(u) + ‖(2^(ks) K(2^(-kr), u))_k‖_{ℓ_q}` is the norm of the couple `(N₀, N)` on
the grid `t = 2^(-kr)` (`InterpCouple.interpNorm`). The first term `E(1, u) ≤ N₀(u)` of the `ℓ_q`
norm is split off at the cost `C_q = LpAddConst q` (`ENNReal.lqNorm_le_head_add_shift'`), and
every other term is bounded one level down. -/
theorem eNormDyadic_le_interpNorm_of_jackson (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {N : U → ℝ≥0∞} {CJ : ℝ≥0∞}
    (hCJ : CJ ≠ ∞) {r : ℝ}
    (hJ : ∀ k g, A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) g ≤ CJ * dyadicWeight (-r) k * N g)
    (hr : r ≠ 0) (s : ℝ) (q : ℝ≥0∞) (u : U) :
    A.eNormDyadic s q u ≤
      eJacksonConst C CJ s q * (⟨A.norm0, N⟩ : InterpCouple U).interpNorm (s / r) r q u := by
  obtain ⟨L, hL⟩ : ∃ L, L = lqNorm q (fun k : ℕ => dyadicWeight s k *
      (⟨A.norm0, N⟩ : InterpCouple U).kFunctional (dyadicWeight (-r) k) u) := ⟨_, rfl⟩
  have hx0 : dyadicWeight s 0 * A.eFunctional ((2 ^ 0 : ℕ) : ℝ≥0∞) u ≤ A.norm0 u := by
    rw [ENNReal.dyadicWeight_zero_right, one_mul]
    exact eFunctional_le_norm0 hA.norm1_zero u
  have hshift : lqNorm q (fun k : ℕ => dyadicWeight s (k + 1) *
      A.eFunctional ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) u) ≤ 2 ^ s * C * max 1 CJ * L := by
    rw [hL, ← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun k => ?_
    rw [ENNReal.dyadicWeight_succ]
    calc 2 ^ s * dyadicWeight s k * A.eFunctional ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) u
        ≤ 2 ^ s * dyadicWeight s k * (C * max 1 CJ *
            (⟨A.norm0, N⟩ : InterpCouple U).kFunctional (dyadicWeight (-r) k) u) := by
          gcongr
          exact eFunctional_succ_le_kFunctional hA h1 hCJ hJ k u
      _ = 2 ^ s * C * max 1 CJ * (dyadicWeight s k *
            (⟨A.norm0, N⟩ : InterpCouple U).kFunctional (dyadicWeight (-r) k) u) := by ring
  have hc1 : 1 + LpAddConst q ≤ eJacksonConst C CJ s q := by
    unfold eJacksonConst
    exact add_le_add le_rfl (le_mul_of_one_le_right' le_self_add)
  have hc2 : LpAddConst q * (2 ^ s * C * max 1 CJ) ≤ eJacksonConst C CJ s q := by
    unfold eJacksonConst
    exact (mul_le_mul_right le_add_self _).trans le_add_self
  calc A.eNormDyadic s q u
      = A.norm0 u + lqNorm q (fun k : ℕ => dyadicWeight s k *
          A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) := rfl
    _ ≤ A.norm0 u + LpAddConst q * (A.norm0 u + 2 ^ s * C * max 1 CJ * L) :=
        add_le_add le_rfl ((ENNReal.lqNorm_le_head_add_shift' q _).trans
          (mul_le_mul_right (add_le_add hx0 hshift) _))
    _ = (1 + LpAddConst q) * A.norm0 u + LpAddConst q * (2 ^ s * C * max 1 CJ) * L := by ring
    _ ≤ eJacksonConst C CJ s q * A.norm0 u + eJacksonConst C CJ s q * L :=
        add_le_add (mul_le_mul_left hc1 _) (mul_le_mul_left hc2 _)
    _ = eJacksonConst C CJ s q * (⟨A.norm0, N⟩ : InterpCouple U).interpNorm (s / r) r q u := by
        rw [← mul_add, hL, interpNorm, mul_div_cancel₀ s hr]

end InterpCouple
