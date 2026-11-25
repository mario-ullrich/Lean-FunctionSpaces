/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Interpolation.EFunctionalSpaces
public import ApproximationSpaces.Interpolation.ApproxSpaces

/-!
# E-spaces as interpolation spaces

Let `A = (N₀, N₁)` be a couple on an abelian group (`InterpCouple`), with the E-functional
`E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}` and the dyadic norm
`‖u‖^dy_{s,q} = N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}` of its approximation space `E_{s,q}`
(`InterpCouple.eNormDyadic`). This file builds the two couples of E-spaces

* `(N₀, E_{r,q₁})` (`InterpCouple.leftECouple`), with the norms `N₀` and `‖·‖^dy_{r,q₁}`, and
* `(E_{s₀,q₀}, E_{s₁,q₁})` (`InterpCouple.eCouple`), with the norms `‖·‖^dy_{s₀,q₀}` and
  `‖·‖^dy_{s₁,q₁}`,

the analogues of `ApproximationScheme.leftApproxCouple` and `ApproximationScheme.approxCouple`
for a quasi-norm `N₀`, and proves the representation `E_{s,q} = (N₀, E_{r,q₁})_{s/r,q}` for
`0 < s < r` and all fine indices `0 < q, q₁ ≤ ∞` (Pietsch, J. Approx. Theory 32 (1981);
DeVore–Popov, LNM 1302 (1988); DeVore, Acta Numer. 7 (1998), §4.3, Theorem 2), and the
reiteration `(E_{s₀,q₀}, E_{s₁,q₁})_{η,q} = E_{(1-η)s₀+ηs₁,q}` for `1 ≤ q₀, q₁, q ≤ ∞`.

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
* **Bernstein's half**: near-best approximants `b_k`, `N₁(b_k) ≤ 2^k`, with decreasing tolerances
  `N₀(u - b_k) ≤ e_k` have `E(2^j, b_k) = 0` for `j ≥ k` and `E(2^j, b_k) ≤ 2C e_j` for `j < k`
  (`InterpCouple.eFunctional_two_pow_le_of_nearBest`), so, with `ρ₁ = min(1, q₁)`,
  `‖b_k‖^dy_{r,q₁} ≤ C (e_k + N₀(u)) + 2C (∑_{j<k} (2^(jr) e_j)^ρ₁)^(1/ρ₁)`
  (`InterpCouple.eNormDyadic_le_of_nearBest`). With
  `K(2^(-kr), u) ≤ N₀(u - b_k) + 2^(-kr) ‖b_k‖^dy_{r,q₁}`
  (`InterpCouple.kFunctional_leftECouple_le_of_nearBest`), Hardy's inequality for partial sums in
  `ρ₁`-th powers and the quasi-triangle inequality of `ℓ_q`
  (`InterpCouple.lqNorm_kFunctional_le_of_le`,
  `InterpCouple.lqNorm_kFunctional_leftECouple_le_of_nearBest`) give, for `0 ≤ s < r` and every
  `q`, `N₀(u) + ‖(2^(ks) K(2^(-kr), u))_k‖_{ℓ_q} ≤ eReprConst C r s q₁ q · ‖u‖^dy_{s,q}`
  (`InterpCouple.interpNorm_leftECouple_le_eNormDyadic`). Only the quasi-triangle inequality of
  `N₀` is used.
* **The representation**: for `r > 0`, `0 < η < 1` and `0 < q, q₁ ≤ ∞`,
  `u ∈ (N₀, E_{r,q₁})_{η,q}` iff `‖u‖^dy_{ηr,q} < ∞` (`InterpCouple.memKMethod_leftECouple_iff`).
* **Reiteration**: the discrete K-norms of `(N₀, E_{r,∞})` on the grid `t = 2^n` and the dyadic
  norms bound each other with the constants `eReprLowerConst` and `eReprUpperConst`
  (`InterpCouple.eNormDyadic_le_discreteKMethodNorm_leftECouple`,
  `InterpCouple.discreteKMethodNorm_leftECouple_le_eNormDyadic`), and the reiteration theorem of
  `ApproximationSpaces.Interpolation.Reiteration` gives, for `0 < s₀ < s₁`, `0 < η < 1` and
  `1 ≤ q₀, q₁, q ≤ ∞`, `(E_{s₀,q₀}, E_{s₁,q₁})_{η,q} = E_{(1-η)s₀+ηs₁,q}`
  (`InterpCouple.memKMethod_eCouple_iff`). The fine indices `≥ 1` are those of that theorem;
  fine indices below `1` need Holmstedt's formula with `ℓ_q` sums. The reiteration for every
  fine index is Bergh–Löfström, Theorem 3.11.5, for quasi-normed couples, and DeVore–Popov,
  Trans. Amer. Math. Soc. 305 (1988), Corollary 6.2, for Besov spaces.
-/

@[expose] public section

open scoped ENNReal
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst hardyConst)

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

/-! ### Bernstein's half -/

/-- **The E-functionals of near-best approximants**: let `A` be quasi-normed with constant `C`,
and let `N₁(b_k) ≤ 2^k` and `N₀(u - b_k) ≤ e_k` for every `k`, with `e` decreasing. Then
`E(2^j, b_k) = 0` for `j ≥ k`, since `b_k` itself is admissible, and
`E(2^j, b_k) ≤ N₀(b_k - b_j) ≤ C (e_j + e_k) ≤ 2C e_j` for `j < k`, from
`b_k - b_j = (u - b_j) - (u - b_k)`. -/
theorem eFunctional_two_pow_le_of_nearBest (hA : A.IsQuasiNormed C) {u : U} {b : ℕ → U}
    {e : ℕ → ℝ≥0∞} (hb1 : ∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (he : Antitone e) (j k : ℕ) :
    A.eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) (b k) ≤ if j < k then 2 * C * e j else 0 := by
  split_ifs with hjk
  · calc A.eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) (b k) ≤ A.norm0 (b k - b j) := eFunctional_le (hb1 j)
      _ = A.norm0 ((u - b j) + -(u - b k)) := by congr 1; abel
      _ ≤ C * (A.norm0 (u - b j) + A.norm0 (-(u - b k))) := hA.norm0_add_le _ _
      _ ≤ C * (e j + e j) := by
          rw [hA.norm0_neg]
          gcongr
          exacts [hbe j, (hbe k).trans (he hjk.le)]
      _ = 2 * C * e j := by ring
  · have hk : A.norm1 (b k) ≤ ((2 ^ j : ℕ) : ℝ≥0∞) :=
      (hb1 k).trans (by exact_mod_cast Nat.pow_le_pow_right two_pos (not_lt.1 hjk))
    exact (eFunctional_le hk).trans_eq (by rw [sub_self, hA.norm0_zero])

/-- **The dyadic norm of a near-best approximant**: under the hypotheses of
`InterpCouple.eFunctional_two_pow_le_of_nearBest`, for every `r`, every `q₁ ≠ 0` and every `k`,
with `ρ₁ = min(1, q₁)`,
`‖b_k‖^dy_{r,q₁} ≤ C (e_k + N₀(u)) + 2C (∑_{j<k} (2^(jr) e_j)^ρ₁)^(1/ρ₁)`. The first term bounds
`N₀(b_k) ≤ C (N₀(u - b_k) + N₀(u))`. The sequence `(2^(jr) E(2^j, b_k))_j` vanishes from `j = k`
on, so its `ℓ_{q₁}` norm is at most its `ℓ_{ρ₁}` norm (`ENNReal.lqNorm_le_lqNorm_of_le`), a finite
sum. -/
theorem eNormDyadic_le_of_nearBest (hA : A.IsQuasiNormed C) {r : ℝ} {q₁ : ℝ≥0∞} (hq₁ : q₁ ≠ 0)
    {u : U} {b : ℕ → U} {e : ℕ → ℝ≥0∞} (hb1 : ∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (he : Antitone e) (k : ℕ) :
    A.eNormDyadic r q₁ (b k) ≤ C * (e k + A.norm0 u) +
      2 * C * (∑ j ∈ Finset.range k, (dyadicWeight r j * e j) ^ (min 1 q₁).toReal) ^
        (1 / (min 1 q₁).toReal) := by
  have hρ0 : min 1 q₁ ≠ 0 := (lt_min one_pos (pos_iff_ne_zero.2 hq₁)).ne'
  have hρt : min 1 q₁ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  have hρ : 0 < (min 1 q₁).toReal := ENNReal.toReal_pos hρ0 hρt
  have h0 : A.norm0 (b k) ≤ C * (e k + A.norm0 u) :=
    calc A.norm0 (b k) = A.norm0 (-(u - b k) + u) := by congr 1; abel
      _ ≤ C * (A.norm0 (-(u - b k)) + A.norm0 u) := hA.norm0_add_le _ _
      _ ≤ C * (e k + A.norm0 u) := by rw [hA.norm0_neg]; gcongr; exact hbe k
  have hz : lqNorm (min 1 q₁) (fun j => if j < k then dyadicWeight r j * e j else 0) =
      (∑ j ∈ Finset.range k, (dyadicWeight r j * e j) ^ (min 1 q₁).toReal) ^
        (1 / (min 1 q₁).toReal) := by
    rw [ENNReal.lqNorm_eq_tsum hρ0 hρt]
    congr 1
    rw [tsum_eq_sum (s := Finset.range k) fun j hj => ?_]
    · exact Finset.sum_congr rfl fun j hj => by simp only [ite_eq_left (Finset.mem_range.1 hj)]
    · simp only [ite_eq_right (by simpa using hj : ¬j < k), ENNReal.zero_rpow_of_pos hρ]
  have h1 : lqNorm q₁ (fun j : ℕ => dyadicWeight r j * A.eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) (b k)) ≤
      2 * C * lqNorm (min 1 q₁) (fun j => if j < k then dyadicWeight r j * e j else 0) := by
    rw [← ENNReal.lqNorm_const_mul]
    refine (ENNReal.lqNorm_mono fun j => ?_).trans
      (ENNReal.lqNorm_le_lqNorm_of_le hρ0 (min_le_right _ _) _)
    refine (mul_le_mul_right (eFunctional_two_pow_le_of_nearBest hA hb1 hbe he j k) _).trans ?_
    split_ifs
    · exact (mul_left_comm _ _ _).le
    · rw [mul_zero]
      exact zero_le
  calc A.eNormDyadic r q₁ (b k) = A.norm0 (b k) + lqNorm q₁ (fun j : ℕ => dyadicWeight r j *
        A.eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) (b k)) := rfl
    _ ≤ _ := add_le_add h0 (h1.trans_eq (by rw [hz]))

/-- **The `ℓ_q` bookkeeping of Bernstein's halves**: for a couple `B`, `s ≤ r` and sequences
`e`, `x` and numbers `a, b ∈ [0, ∞]`, if `K(2^(-kr), u) ≤ a e_k + b 2^(-kr) + x_k` for every `k`,
then `‖(2^(ks) K(2^(-kr), u))_k‖_{ℓ_q} ≤ C_q (C_q (a ‖(2^(ks) e_k)_k‖_{ℓ_q} + b γ_{r-s,q}) +
‖(2^(ks) x_k)_k‖_{ℓ_q})`, with Mathlib's constant `C_q = LpAddConst q` of the quasi-triangle
inequality (`ENNReal.lqNorm_add_le'`, used twice) and `γ_{r-s,q} = dyadicGeomConst (r - s) q`,
which bounds `‖(2^(-k(r-s)))_k‖_{ℓ_q}`. -/
theorem lqNorm_kFunctional_le_of_le {B : InterpCouple U} {r s : ℝ} {q : ℝ≥0∞} {u : U}
    {e x : ℕ → ℝ≥0∞} {a b : ℝ≥0∞} (hsr : s ≤ r)
    (hK : ∀ k, B.kFunctional (dyadicWeight (-r) k) u ≤
      a * e k + b * dyadicWeight (-r) k + x k) :
    lqNorm q (fun k => dyadicWeight s k * B.kFunctional (dyadicWeight (-r) k) u) ≤
      LpAddConst q * (LpAddConst q * (a * lqNorm q (fun k => dyadicWeight s k * e k) +
        b * dyadicGeomConst (r - s) q) + lqNorm q (fun k => dyadicWeight s k * x k)) := by
  have hw : ∀ k, dyadicWeight s k * dyadicWeight (-r) k = dyadicWeight (-(r - s)) k := fun k => by
    rw [← ENNReal.dyadicWeight_add]
    congr 1
    ring
  have hpt : ∀ k, dyadicWeight s k * B.kFunctional (dyadicWeight (-r) k) u ≤
      (a * (dyadicWeight s k * e k) + b * dyadicWeight (-(r - s)) k) + dyadicWeight s k * x k :=
    fun k => (mul_le_mul_right (hK k) _).trans_eq (by rw [← hw k]; ring)
  calc lqNorm q (fun k => dyadicWeight s k * B.kFunctional (dyadicWeight (-r) k) u)
      ≤ lqNorm q (fun k => (a * (dyadicWeight s k * e k) + b * dyadicWeight (-(r - s)) k) +
          dyadicWeight s k * x k) := ENNReal.lqNorm_mono hpt
    _ ≤ LpAddConst q * (lqNorm q (fun k => a * (dyadicWeight s k * e k) +
          b * dyadicWeight (-(r - s)) k) + lqNorm q (fun k => dyadicWeight s k * x k)) :=
        ENNReal.lqNorm_add_le' q _ _
    _ ≤ LpAddConst q * (LpAddConst q * (lqNorm q (fun k => a * (dyadicWeight s k * e k)) +
          lqNorm q (fun k => b * dyadicWeight (-(r - s)) k)) +
          lqNorm q (fun k => dyadicWeight s k * x k)) := by
        gcongr
        exact ENNReal.lqNorm_add_le' q _ _
    _ ≤ _ := by
        rw [ENNReal.lqNorm_const_mul, ENNReal.lqNorm_const_mul]
        gcongr
        exact ENNReal.lqNorm_dyadicWeight_neg_le_dyadicGeomConst (sub_nonneg.2 hsr)

/-- **Bernstein's half at one level**: under the hypotheses of
`InterpCouple.eNormDyadic_le_of_nearBest` and `r ≥ 0`, with `ρ₁ = min(1, q₁)`, the K-functional of
`(N₀, E_{r,q₁})` satisfies
`K(2^(-kr), u) ≤ (1 + C) e_k + C N₀(u) 2^(-kr) + 2^(-kr) · 2C (∑_{j<k} (2^(jr) e_j)^ρ₁)^(1/ρ₁)`,
from `K(2^(-kr), u) ≤ N₀(u - b_k) + 2^(-kr) ‖b_k‖^dy_{r,q₁}` and `2^(-kr) ≤ 1`. -/
theorem kFunctional_leftECouple_le_of_nearBest (hA : A.IsQuasiNormed C) {r : ℝ} (hr : 0 ≤ r)
    {q₁ : ℝ≥0∞} (hq₁ : q₁ ≠ 0) {u : U} {b : ℕ → U} {e : ℕ → ℝ≥0∞}
    (hb1 : ∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (he : Antitone e) (k : ℕ) :
    (A.leftECouple r q₁).kFunctional (dyadicWeight (-r) k) u ≤
      (1 + C) * e k + C * A.norm0 u * dyadicWeight (-r) k +
        dyadicWeight (-r) k * (2 * C * (∑ j ∈ Finset.range k,
          (dyadicWeight r j * e j) ^ (min 1 q₁).toReal) ^ (1 / (min 1 q₁).toReal)) := by
  set S := (∑ j ∈ Finset.range k, (dyadicWeight r j * e j) ^ (min 1 q₁).toReal) ^
    (1 / (min 1 q₁).toReal)
  have hw : dyadicWeight (-r) k ≤ 1 :=
    (ENNReal.dyadicWeight_anti (neg_nonpos.2 hr) (Nat.zero_le k)).trans_eq
      (ENNReal.dyadicWeight_zero_right _)
  calc (A.leftECouple r q₁).kFunctional (dyadicWeight (-r) k) u
      ≤ A.norm0 (u - b k) + dyadicWeight (-r) k * A.eNormDyadic r q₁ (b k) :=
        kFunctional_le (b k) u
    _ ≤ e k + dyadicWeight (-r) k * (C * (e k + A.norm0 u) + 2 * C * S) := by
        gcongr
        exacts [hbe k, eNormDyadic_le_of_nearBest hA hq₁ hb1 hbe he k]
    _ = e k + dyadicWeight (-r) k * (C * e k) + C * A.norm0 u * dyadicWeight (-r) k +
          dyadicWeight (-r) k * (2 * C * S) := by ring
    _ ≤ e k + 1 * (C * e k) + C * A.norm0 u * dyadicWeight (-r) k +
          dyadicWeight (-r) k * (2 * C * S) := by gcongr
    _ = (1 + C) * e k + C * A.norm0 u * dyadicWeight (-r) k + dyadicWeight (-r) k * (2 * C * S) :=
        by ring

/-- **Bernstein's half in `ℓ_q`**: under the hypotheses of
`InterpCouple.kFunctional_leftECouple_le_of_nearBest`, for `s ≤ r` and every `q`, with
`ρ₁ = min(1, q₁)` and `L = ‖(2^(ks) e_k)_k‖_{ℓ_q}`,
`‖(2^(ks) K(2^(-kr), u))_k‖_{ℓ_q} ≤
C_q (C_q ((1 + C) L + C N₀(u) γ_{r-s,q}) + ((2C)^ρ₁ H)^(1/ρ₁) L)` for the K-functional of
`(N₀, E_{r,q₁})`, with `H = hardyConst ((r - s)ρ₁) (q/ρ₁)`
(`InterpCouple.lqNorm_kFunctional_le_of_le`). The last term of the bound at one level satisfies
`x_k^ρ₁ = (2C)^ρ₁ ∑_{j<k} 2^(-(k-j)rρ₁) e_j^ρ₁`, so Hardy's inequality for partial sums in
`ρ₁`-th powers (`ENNReal.lqNorm_le_of_rpow_le_sum`) bounds `‖(2^(ks) x_k)_k‖_{ℓ_q}`. -/
theorem lqNorm_kFunctional_leftECouple_le_of_nearBest (hA : A.IsQuasiNormed C) {r s : ℝ}
    (hr : 0 ≤ r) (hsr : s ≤ r) {q₁ : ℝ≥0∞} (hq₁ : q₁ ≠ 0) {u : U} {b : ℕ → U} {e : ℕ → ℝ≥0∞}
    (hb1 : ∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (he : Antitone e) (q : ℝ≥0∞) :
    lqNorm q (fun k => dyadicWeight s k *
        (A.leftECouple r q₁).kFunctional (dyadicWeight (-r) k) u) ≤
      LpAddConst q * (LpAddConst q * ((1 + C) * lqNorm q (fun k => dyadicWeight s k * e k) +
        C * A.norm0 u * dyadicGeomConst (r - s) q) +
        ((2 * C) ^ (min 1 q₁).toReal * hardyConst (r * (min 1 q₁).toReal - s * (min 1 q₁).toReal)
          (q / ENNReal.ofReal (min 1 q₁).toReal)) ^ (1 / (min 1 q₁).toReal) *
          lqNorm q (fun k => dyadicWeight s k * e k)) := by
  set ρ := (min 1 q₁).toReal
  have hρ : 0 < ρ := ENNReal.toReal_pos (lt_min one_pos (pos_iff_ne_zero.2 hq₁)).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
  have hx : ∀ k, (dyadicWeight (-r) k * (2 * C *
      (∑ j ∈ Finset.range k, (dyadicWeight r j * e j) ^ ρ) ^ (1 / ρ))) ^ ρ ≤
      (2 * C) ^ ρ * ∑ j ∈ Finset.range (k + 1), dyadicWeight (-(r * ρ)) (k - j) * e j ^ ρ :=
    fun k => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.mul_rpow_of_nonneg _ _ hρ.le,
        ← ENNReal.rpow_mul, one_div_mul_cancel hρ.ne', ENNReal.rpow_one,
        ENNReal.dyadicWeight_rpow, mul_left_comm, Finset.mul_sum]
      gcongr
      refine (Finset.sum_congr rfl fun j hj => ?_).trans_le
        (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 k.le_succ))
      have hjk : j ≤ k := (Finset.mem_range.1 hj).le
      have h := ENNReal.dyadicWeight_mul_dyadicWeight_neg_sub 0 (r * ρ) hjk
      rw [ENNReal.dyadicWeight_zero_left, one_mul, sub_zero] at h
      rw [ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.dyadicWeight_rpow, h, neg_mul, mul_assoc]
  refine (lqNorm_kFunctional_le_of_le hsr
    (kFunctional_leftECouple_le_of_nearBest hA hr hq₁ hb1 hbe he)).trans ?_
  gcongr
  exact ENNReal.lqNorm_le_of_rpow_le_sum hρ hx s q

/-- The constant of Bernstein's half of the representation `E_{s,q} = (N₀, E_{r,q₁})_{s/r,q}`:
with Mathlib's constant `C_q = LpAddConst q`, `M = C_q (1 + γ_{1,q})`, `ρ₁ = min(1, q₁)` and
`H = hardyConst ((r - s)ρ₁) (q/ρ₁)`, it is
`1 + C_q (C_q ((1 + C) M + C γ_{r-s,q}) + ((2C)^ρ₁ H)^(1/ρ₁) M)`. -/
noncomputable def eReprConst (C : ℝ≥0∞) (r s : ℝ) (q₁ q : ℝ≥0∞) : ℝ≥0∞ :=
  1 + LpAddConst q * (LpAddConst q * ((1 + C) * (LpAddConst q * (1 + dyadicGeomConst 1 q)) +
    C * dyadicGeomConst (r - s) q) +
    ((2 * C) ^ (min 1 q₁).toReal * hardyConst (r * (min 1 q₁).toReal - s * (min 1 q₁).toReal)
      (q / ENNReal.ofReal (min 1 q₁).toReal)) ^ (1 / (min 1 q₁).toReal) *
      (LpAddConst q * (1 + dyadicGeomConst 1 q)))

/-- The constant `eReprConst C r s q₁ q` is finite for `C < ∞`, `s < r` and `q₁ ≠ 0`. -/
theorem eReprConst_ne_top (hC : C ≠ ∞) {r s : ℝ} (hsr : s < r) {q₁ : ℝ≥0∞} (hq₁ : q₁ ≠ 0)
    (q : ℝ≥0∞) : eReprConst C r s q₁ q ≠ ∞ := by
  have hρ : 0 < (min 1 q₁).toReal := ENNReal.toReal_pos
    (lt_min one_pos (pos_iff_ne_zero.2 hq₁)).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
  have hα : 0 < r * (min 1 q₁).toReal - s * (min 1 q₁).toReal := by
    rw [← sub_mul]
    exact mul_pos (sub_pos.2 hsr) hρ
  have hq : LpAddConst q ≠ ∞ := (ENNReal.LpAddConst_lt_top q).ne
  have hM : LpAddConst q * (1 + dyadicGeomConst 1 q) ≠ ∞ :=
    ENNReal.mul_ne_top hq (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.dyadicGeomConst_ne_top one_pos q⟩)
  have hH : ((2 * C) ^ (min 1 q₁).toReal * hardyConst (r * (min 1 q₁).toReal -
      s * (min 1 q₁).toReal) (q / ENNReal.ofReal (min 1 q₁).toReal)) ^
        (1 / (min 1 q₁).toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hρ.le (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC))
      (ENNReal.hardyConst_ne_top hα _))
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hq (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top hq (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, hC⟩) hM, ENNReal.mul_ne_top hC
        (ENNReal.dyadicGeomConst_ne_top (sub_pos.2 hsr) q)⟩), ENNReal.mul_ne_top hH hM⟩)⟩

/-- **Bernstein's half of `E_{s,q} = (N₀, E_{r,q₁})_{s/r,q}`**: if `A` is quasi-normed with
constant `C`, `0 ≤ s < r` and `q₁ ≠ 0`, then for every `q` and every `u`,
`‖u‖_{s/r,r,q} ≤ eReprConst C r s q₁ q · ‖u‖^dy_{s,q}`, where
`‖u‖_{s/r,r,q} = N₀(u) + ‖(2^(ks) K(2^(-kr), u))_k‖_{ℓ_q}` is the norm of `(N₀, E_{r,q₁})` on the
grid `t = 2^(-kr)` (`InterpCouple.interpNorm`). The near-best approximants of `u` with their
tolerances (`InterpCouple.exists_nearBest_tolerances`) lie in `E_{r,q₁}` and take the place of
the lifts (`InterpCouple.lqNorm_kFunctional_leftECouple_le_of_nearBest`). Only the quasi-triangle
inequality of `N₀` is used. -/
theorem interpNorm_leftECouple_le_eNormDyadic (hA : A.IsQuasiNormed C) {r s : ℝ} (hs : 0 ≤ s)
    (hsr : s < r) {q₁ : ℝ≥0∞} (hq₁ : q₁ ≠ 0) (q : ℝ≥0∞) (u : U) :
    (A.leftECouple r q₁).interpNorm (s / r) r q u ≤
      eReprConst C r s q₁ q * A.eNormDyadic s q u := by
  have hr : 0 < r := hs.trans_lt hsr
  obtain ⟨b, e, hb1, hbe, he, -, hL⟩ :=
    exists_nearBest_tolerances hA.norm1_zero u s (by linarith)
  have hK := lqNorm_kFunctional_leftECouple_le_of_nearBest hA hr.le hsr.le hq₁ hb1 hbe he q
  have hN : A.norm0 u ≤ A.eNormDyadic s q u := le_self_add
  calc (A.leftECouple r q₁).interpNorm (s / r) r q u
      = A.norm0 u + lqNorm q (fun k => dyadicWeight s k *
          (A.leftECouple r q₁).kFunctional (dyadicWeight (-r) k) u) := by
        rw [interpNorm, mul_div_cancel₀ s hr.ne']
        rfl
    _ ≤ A.eNormDyadic s q u + LpAddConst q * (LpAddConst q *
          ((1 + C) * (LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q u) +
            C * A.eNormDyadic s q u * dyadicGeomConst (r - s) q) +
          ((2 * C) ^ (min 1 q₁).toReal * hardyConst (r * (min 1 q₁).toReal -
            s * (min 1 q₁).toReal) (q / ENNReal.ofReal (min 1 q₁).toReal)) ^
              (1 / (min 1 q₁).toReal) *
            (LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q u)) := by
        refine add_le_add hN (hK.trans ?_)
        gcongr
        all_goals exact hL q
    _ = eReprConst C r s q₁ q * A.eNormDyadic s q u := by
        rw [eReprConst]
        ring

/-! ### E-spaces are interpolation spaces -/

/-- **E-spaces are interpolation spaces** (Pietsch, J. Approx. Theory 32 (1981); DeVore–Popov,
LNM 1302 (1988); DeVore, Acta Numer. 7 (1998), §4.3, Theorem 2): if `A` is quasi-normed with
constant `C` and its complexity is subadditive, then for `r > 0`, `0 < η < 1` and
`0 < q, q₁ ≤ ∞`, `u` lies in the real interpolation space `(N₀, E_{r,q₁})_{η,q}` iff
`‖u‖^dy_{ηr,q} < ∞`. The two halves are `InterpCouple.eNormDyadic_le_interpNorm_of_jackson`
(with Jackson's inequality `InterpCouple.eFunctional_two_pow_le_dyadicWeight_mul`) and
`InterpCouple.interpNorm_leftECouple_le_eNormDyadic`, on the grid `t = 2^(-kr)` of the ordered
quasi-normed couple `(N₀, E_{r,q₁})` (`InterpCouple.memKMethod_iff_interpNorm_lt_top`). -/
theorem memKMethod_leftECouple_iff (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hη' : η < 1) {q₁ q : ℝ≥0∞} (hq₁ : q₁ ≠ 0) (hq : q ≠ 0) {u : U} :
    (A.leftECouple r q₁).MemKMethod η q u ↔ A.eNormDyadic (η * r) q u < ∞ := by
  have hsr : η * r < r := mul_lt_of_lt_one_left hr hη'
  have hB := interpNorm_leftECouple_le_eNormDyadic hA (mul_pos hη hr).le hsr hq₁ q u
  have hJ := eNormDyadic_le_interpNorm_of_jackson hA h1 ENNReal.one_ne_top
    (fun k g => eFunctional_two_pow_le_dyadicWeight_mul hq₁ k g) hr.ne' (η * r) q u
  rw [mul_div_cancel_right₀ η hr.ne'] at hB hJ
  rw [memKMethod_iff_interpNorm_lt_top (isQuasiNormed_leftECouple hA h1 r q₁)
    ENNReal.one_ne_top (norm0_le_leftECouple_norm1 r q₁) hη hr hq]
  exact ⟨fun h => hJ.trans_lt (ENNReal.mul_lt_top
      (eJacksonConst_ne_top hA.ne_top ENNReal.one_ne_top _ _).lt_top h),
    fun h => hB.trans_lt (ENNReal.mul_lt_top (eReprConst_ne_top hA.ne_top hsr hq₁ q).lt_top h)⟩

/-! ### Reiteration of E-spaces -/

/-- The constant of the bound of `‖·‖^dy_{s,q}` by the discrete K-norm of `(N₀, E_{r,∞})` on the
grid `t = 2^n`: `eJacksonConst C 1 s q · (1 + K_r) 2^s (r log 2)^(-1/q) · (log 2)^(1/q) 2^(s/r)`
with `K_r = eAddConst C r ∞`. -/
noncomputable def eReprLowerConst (C : ℝ≥0∞) (r s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  eJacksonConst C 1 s q * ((1 + eAddConst C r ∞) *
    (2 ^ s * (ENNReal.ofReal (r * Real.log 2) ^ (1 / q.toReal))⁻¹)) *
      (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (s / r))

/-- The constant `eReprLowerConst C r s q` is finite for `C < ∞` and `r > 0`. -/
theorem eReprLowerConst_ne_top (hC : C ≠ ∞) {r : ℝ} (hr : 0 < r) (s : ℝ) (q : ℝ≥0∞) :
    eReprLowerConst C r s q ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (eJacksonConst_ne_top hC ENNReal.one_ne_top s q)
    (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, eAddConst_ne_top hC r ∞⟩)
      (ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top s)
        (ENNReal.inv_ne_top.2 (ApproximationScheme.ofReal_mul_log_two_rpow_ne_zero hr q)))))
    (ApproximationScheme.log_two_rpow_mul_two_rpow_ne_top (s / r) q)

/-- **The dyadic norm by the discrete K-norm of `(N₀, E_{r,∞})`**: if `A` is quasi-normed with
constant `C` and its complexity is subadditive, `s ≥ 0`, `r > 0` and `q ≠ 0`, then
`‖u‖^dy_{s,q} ≤ eReprLowerConst C r s q · ‖(2^(-ns/r) K(2^n, u))_{n ∈ ℤ}‖_{ℓ_q}` for the
K-functional of `(N₀, E_{r,∞})`: Jackson's half
(`InterpCouple.eNormDyadic_le_interpNorm_of_jackson`), then the comparisons of the norm on the
grid `ℕ` with the continuous and the discrete K-norm (`InterpCouple.interpNorm_le_kMethodNorm`,
`InterpCouple.kMethodNorm_le_mul_discreteKMethodNorm`). -/
theorem eNormDyadic_le_discreteKMethodNorm_leftECouple (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {r s : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    {q : ℝ≥0∞} (hq : q ≠ 0) (u : U) :
    A.eNormDyadic s q u ≤
      eReprLowerConst C r s q * (A.leftECouple r ∞).discreteKMethodNorm (s / r) 1 q u := by
  have hJ := eNormDyadic_le_interpNorm_of_jackson hA h1 ENNReal.one_ne_top
    (fun k g => eFunctional_two_pow_le_dyadicWeight_mul (q₁ := ∞) ENNReal.top_ne_zero k g)
    hr.ne' s q u
  have hK := interpNorm_le_kMethodNorm (isQuasiNormed_leftECouple hA h1 r ∞) ENNReal.one_ne_top
    (norm0_le_leftECouple_norm1 r ∞) (div_nonneg hs hr.le) hr hq u
  rw [mul_div_cancel₀ s hr.ne', max_self, mul_one] at hK
  calc A.eNormDyadic s q u
      ≤ eJacksonConst C 1 s q * (A.leftECouple r ∞).interpNorm (s / r) r q u := hJ
    _ ≤ eJacksonConst C 1 s q * ((1 + eAddConst C r ∞) *
          (2 ^ s * (ENNReal.ofReal (r * Real.log 2) ^ (1 / q.toReal))⁻¹) *
            (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (s / r) *
              (A.leftECouple r ∞).discreteKMethodNorm (s / r) 1 q u)) := by
        gcongr
        refine hK.trans ?_
        gcongr
        exact kMethodNorm_le_mul_discreteKMethodNorm (div_nonneg hs hr.le) u
    _ = eReprLowerConst C r s q * (A.leftECouple r ∞).discreteKMethodNorm (s / r) 1 q u := by
        rw [eReprLowerConst]
        ring

/-- The constant of the bound of the discrete K-norm of `(N₀, E_{r,∞})` on the grid `t = 2^n` by
`‖·‖^dy_{s,q}`: `((log 2)^(1/q) 2^(-s/r))⁻¹ · kMethodUpperConst (s/r) r q · eReprConst C r s ∞ q`.
-/
noncomputable def eReprUpperConst (C : ℝ≥0∞) (r s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(s / r)))⁻¹ *
    (ApproximationScheme.kMethodUpperConst (s / r) r q * eReprConst C r s ∞ q)

/-- The constant `eReprUpperConst C r s q` is finite for `C < ∞` and `0 < s < r`. -/
theorem eReprUpperConst_ne_top (hC : C ≠ ∞) {r s : ℝ} (hs : 0 < s) (hsr : s < r) (q : ℝ≥0∞) :
    eReprUpperConst C r s q ≠ ∞ :=
  ENNReal.mul_ne_top (ApproximationScheme.inv_log_two_rpow_mul_two_rpow_ne_top _ q)
    (ENNReal.mul_ne_top (ApproximationScheme.kMethodUpperConst_ne_top
      (div_pos hs (hs.trans hsr)) (hs.trans hsr) q)
      (eReprConst_ne_top hC hsr ENNReal.top_ne_zero q))

/-- **The discrete K-norm of `(N₀, E_{r,∞})` by the dyadic norm**: if `A` is quasi-normed with
constant `C` and `0 < s < r`, then for every `q`,
`‖(2^(-ns/r) K(2^n, u))_{n ∈ ℤ}‖_{ℓ_q} ≤ eReprUpperConst C r s q · ‖u‖^dy_{s,q}`: Bernstein's half
(`InterpCouple.interpNorm_leftECouple_le_eNormDyadic`), then the comparisons of the norm on the
grid `ℕ` with the continuous and the discrete K-norm (`InterpCouple.kMethodNorm_le_interpNorm`,
`InterpCouple.discreteKMethodNorm_le_mul_kMethodNorm`). -/
theorem discreteKMethodNorm_leftECouple_le_eNormDyadic (hA : A.IsQuasiNormed C) {r s : ℝ}
    (hs : 0 < s) (hsr : s < r) (q : ℝ≥0∞) (u : U) :
    (A.leftECouple r ∞).discreteKMethodNorm (s / r) 1 q u ≤
      eReprUpperConst C r s q * A.eNormDyadic s q u :=
  calc (A.leftECouple r ∞).discreteKMethodNorm (s / r) 1 q u
      ≤ (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(s / r)))⁻¹ *
          (A.leftECouple r ∞).kMethodNorm (s / r) q u :=
        discreteKMethodNorm_le_mul_kMethodNorm (div_pos hs (hs.trans hsr)).le u
    _ ≤ (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(s / r)))⁻¹ *
          (ApproximationScheme.kMethodUpperConst (s / r) r q *
            (eReprConst C r s ∞ q * A.eNormDyadic s q u)) := by
        gcongr
        refine (kMethodNorm_le_interpNorm (eNormDyadic_zero hA.norm0_zero hA.norm1_zero r ∞)
          (div_pos hs (hs.trans hsr)).le (hs.trans hsr) u).trans ?_
        gcongr
        exact interpNorm_leftECouple_le_eNormDyadic hA hs.le hsr ENNReal.top_ne_zero q u
    _ = eReprUpperConst C r s q * A.eNormDyadic s q u := by
        rw [eReprUpperConst]
        ring

/-- **The reiteration theorem for E-spaces** (for approximation spaces: Pietsch, J. Approx.
Theory 32 (1981); DeVore–Lorentz, Chapter 7): if `A` is quasi-normed with constant `C`
and its complexity is subadditive, then for `0 < s₀ < s₁`, `0 < η < 1` and
`1 ≤ q₀, q₁, q ≤ ∞`, `(E_{s₀,q₀}, E_{s₁,q₁})_{η,q} = E_{(1-η)s₀+ηs₁,q}`: `u` lies in the real
interpolation space of the couple `(E_{s₀,q₀}, E_{s₁,q₁})` iff
`‖u‖^dy_{(1-η)s₀+ηs₁,q} < ∞`. Both spaces are represented in the couple `(N₀, E_{r,∞})` with
`r = s₁ + 1`, whose discrete K-norms are comparable with the dyadic norms
(`InterpCouple.eNormDyadic_le_discreteKMethodNorm_leftECouple`,
`InterpCouple.discreteKMethodNorm_leftECouple_le_eNormDyadic`), and the reiteration theorem
`InterpCouple.memKMethod_kCouple_iff` with `InterpCouple.memKMethod_leftECouple_iff` gives the
result. The fine indices `≥ 1` are those of the reiteration theorem. -/
theorem memKMethod_eCouple_iff (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {s₀ s₁ η : ℝ} (hs₀ : 0 < s₀)
    (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1) {q₀ q₁ q : ℝ≥0∞} (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) {u : U} :
    (A.eCouple s₀ q₀ s₁ q₁).MemKMethod η q u ↔
      A.eNormDyadic ((1 - η) * s₀ + η * s₁) q u < ∞ := by
  have hs₁ : 0 < s₁ := hs₀.trans hs
  have hr : 0 < s₁ + 1 := by linarith
  have hsr₀ : s₀ < s₁ + 1 := by linarith
  have hsr₁ : s₁ < s₁ + 1 := by linarith
  have hθ : 0 < (1 - η) * s₀ + η * s₁ :=
    ApproximationScheme.reiterationExponent_pos hs₀ hs hη hη'
  have hθr : (1 - η) * s₀ + η * s₁ < s₁ + 1 :=
    ApproximationScheme.reiterationExponent_lt hs hsr₁ hη'
  rw [← div_mul_cancel₀ ((1 - η) * s₀ + η * s₁) hr.ne',
    ← memKMethod_leftECouple_iff hA h1 hr (div_pos hθ hr) ((div_lt_one hr).2 hθr)
      ENNReal.top_ne_zero (one_pos.trans_le hq).ne',
    show ((1 - η) * s₀ + η * s₁) / (s₁ + 1) =
      (1 - η) * (s₀ / (s₁ + 1)) + η * (s₁ / (s₁ + 1)) by ring,
    ← memKMethod_kCouple_iff (isQuasiNormed_leftECouple hA h1 (s₁ + 1) ∞) (div_pos hs₀ hr)
      (div_lt_div_of_pos_right hs hr) ((div_lt_one hr).2 hsr₁) hη hη' hq₀ hq₁ hq]
  exact memKMethod_congr (A := A.eCouple s₀ q₀ s₁ q₁)
    (B := (A.leftECouple (s₁ + 1) ∞).kCouple (s₀ / (s₁ + 1)) q₀ (s₁ / (s₁ + 1)) q₁)
    (eReprUpperConst_ne_top hA.ne_top hs₀ hsr₀ q₀) (eReprUpperConst_ne_top hA.ne_top hs₁ hsr₁ q₁)
    (eReprLowerConst_ne_top hA.ne_top hr s₀ q₀) (eReprLowerConst_ne_top hA.ne_top hr s₁ q₁)
    (discreteKMethodNorm_leftECouple_le_eNormDyadic hA hs₀ hsr₀ q₀)
    (discreteKMethodNorm_leftECouple_le_eNormDyadic hA hs₁ hsr₁ q₁)
    (eNormDyadic_le_discreteKMethodNorm_leftECouple hA h1 hs₀.le hr (one_pos.trans_le hq₀).ne')
    (eNormDyadic_le_discreteKMethodNorm_leftECouple hA h1 hs₁.le hr (one_pos.trans_le hq₁).ne')

end InterpCouple
