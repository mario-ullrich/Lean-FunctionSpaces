/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Interpolation.EFunctionalRepresentation
public import Mathlib.Order.CompleteLattice.Group

/-!
# The Jackson–Bernstein theorem for quasi-normed couples

Let `A = (N₀, N₁)` be a couple on an abelian group (`InterpCouple`), quasi-normed with constant
`C` and with subadditive complexity `N₁`, with the E-functional
`E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}` and the dyadic norm
`‖u‖^dy_{s,q} = N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}` of its approximation space `E_{s,q}`
(`InterpCouple.eNormDyadic`). Jackson's and Bernstein's inequalities of order `r`
(`InterpCouple.JacksonBernsteinData A ρ r`) concern a function `Y : U → [0, ∞]` with

* `Y(-a) = Y(a)` and `Y(a + b)^ρ ≤ Y(a)^ρ + Y(b)^ρ` for an exponent `ρ > 0`,
* **Jackson's inequality** `E(2^k, u) ≤ C_J 2^(-kr) Y(u)` with `C_J < ∞`, and
* **Bernstein's inequality** `Y(a) ≤ C_B 2^(kr) N₀(a)` for `N₁(a) ≤ 2^k`, with `C_B < ∞`.

The couple `(N₀, N₀ + Y)` (`InterpCouple.JacksonBernsteinData.smoothnessCouple`) is quasi-normed
with constant `max(C, C_ρ)`, `C_ρ = LpAddConst ρ`, since the `ρ`-triangle inequality of `Y` gives
`Y(a + b) ≤ C_ρ (Y(a) + Y(b))` for every `ρ > 0`
(`InterpCouple.JacksonBernsteinData.isQuasiNormed_smoothnessCouple`). The **Jackson–Bernstein
theorem** states `E_{s,q} = (N₀, N₀ + Y)_{s/r,q}` for `0 < s < r` and `0 < q ≤ ∞`
(`InterpCouple.JacksonBernsteinData.memKMethod_smoothnessCouple_iff`); for a normed space `X` in
place of `N₀` it is DeVore, Acta Numer. 7 (1998), §4.3, Theorem 1.

* **Jackson's half** is the one of the representation theorem for every Jackson inequality
  (`InterpCouple.eNormDyadic_le_interpNorm_of_jackson`), applied to `N = N₀ + Y`
  (`InterpCouple.JacksonBernsteinData.eNormDyadic_le_interpNorm_smoothnessCouple`).
* **Bernstein's half**: near-best approximants `b_k`, `N₁(b_k) ≤ 2^k`, with decreasing tolerances
  `N₀(u - b_k) ≤ e_k` and `N₀(u) ≤ e_0` (`InterpCouple.exists_nearBest_tolerances`) telescope as
  `b_k = b_0 + ∑_{j<k} (b_{j+1} - b_j)`, a finite sum, so the bound holds in every abelian
  group `U`. The quasi-triangle inequality of `N₀` gives `N₀(b_0) ≤ 2C e_0` and
  `N₀(b_{j+1} - b_j) ≤ 2C e_j` (`InterpCouple.norm0_sub_le_two_mul`); Bernstein's inequality at
  the levels `0` and `j + 2` and the `ρ`-triangle inequality of `Y` give
  `(2^(-kr) Y(b_k))^ρ ≤ 2 (2C C_B)^ρ 4^(rρ) ∑_{j ≤ k} 2^(-(k-j)rρ) e_j^ρ`
  (`InterpCouple.JacksonBernsteinData.dyadicWeight_mul_smoothNorm_rpow_le_of_nearBest`). Hardy's
  inequality for partial sums in `ρ`-th powers and the `ℓ_q` bookkeeping of
  `InterpCouple.lqNorm_kFunctional_le_of_le` then bound the norm of `(N₀, N₀ + Y)` on the grid
  `t = 2^(-kr)` by `jacksonBernsteinConst C C_B ρ r s q · ‖u‖^dy_{s,q}` for `0 ≤ s < r`
  (`InterpCouple.jacksonBernsteinConst`,
  `InterpCouple.JacksonBernsteinData.interpNorm_smoothnessCouple_le_eNormDyadic`).

The normed counterpart for approximation schemes is `ApproximationScheme.SmoothnessSpace` with
`ApproximationScheme.SmoothnessSpace.memApprox_iff_memInterp`. For `L_p`, `0 < p < 1`, the space
`Y` is a classical or an approximation space: the K-functional of `L_p` and the Sobolev space
`W^r_p` on the circle vanishes identically (Ditzian–Hristov–Ivanov, Constr. Approx. 11 (1995)).

**Classical spaces of a modulus.** Let `ω` be a modulus compatible with a `ρ`-normed couple of
inverse order `θ` (`InterpCouple.CoupleModulusData`), with the classical quasi-norm
`‖f‖^ω_{s,q} = N₀(f) + ‖(2^(ks) ω(f, k))_k‖_{ℓ_q}`. If `ω` is even and `0 ≤ r ≤ θ`, then
`Y(f) = sup_k 2^(kr) ω(f, k)` satisfies Jackson's and Bernstein's inequalities of order `r`
(`InterpCouple.CoupleModulusData.jacksonBernsteinData`), and `(N₀, N₀ + Y)` is the couple
`(N₀, ‖·‖^ω_{r,∞})` (`InterpCouple.CoupleModulusData.leftCoupleModCouple`). With the
coincidence theorem this gives, for `0 < s < r ≤ θ` and `0 < q ≤ ∞`,
`(N₀, ‖·‖^ω_{r,∞})_{s/r,q} = {f : ‖f‖^ω_{s,q} < ∞}`
(`InterpCouple.CoupleModulusData.memKMethod_leftCoupleModCouple_top_iff`).

For every compatible modulus, the representation theorem and the coincidence theorem give
`(N₀, ‖·‖^ω_{s₁,q₁})_{η,q} = {f : ‖f‖^ω_{ηs₁,q} < ∞}` for `0 < s₁ < θ`, `0 < η < 1` and
`0 < q₁, q ≤ ∞` (`InterpCouple.CoupleModulusData.memKMethod_leftCoupleModCouple_iff`).
-/

@[expose] public section

open Finset
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst hardyConst)

namespace InterpCouple

variable {U : Type*} [AddCommGroup U]

/-! ### Two elements close to a third -/

section NearBest

variable {A : InterpCouple U} {C : ℝ≥0∞}

/-- **An element close to a second one is bounded by it**: if `A` is quasi-normed with constant
`C` and `N₀(u - a) ≤ x`, then `N₀(a) ≤ C (x + N₀(u))`, from `a = -(u - a) + u`. -/
theorem norm0_le_of_sub_le (hA : A.IsQuasiNormed C) {u a : U} {x : ℝ≥0∞}
    (h : A.norm0 (u - a) ≤ x) : A.norm0 a ≤ C * (x + A.norm0 u) :=
  calc A.norm0 a = A.norm0 (-(u - a) + u) := by congr 1; abel
    _ ≤ C * (A.norm0 (-(u - a)) + A.norm0 u) := hA.norm0_add_le _ _
    _ ≤ C * (x + A.norm0 u) := by
        rw [hA.norm0_neg]
        exact mul_le_mul_right (add_le_add h le_rfl) C

/-- **Two elements close to a third are close to each other**: if `A` is quasi-normed with
constant `C`, `N₀(u - a) ≤ x` and `N₀(u - a') ≤ x`, then `N₀(a - a') ≤ 2C x`, from
`a - a' = (u - a') - (u - a)`. For near-best approximants `b_k` of `u` with decreasing tolerances
`e_k` it gives `N₀(b_{j+1} - b_j) ≤ 2C e_j`, and `N₀(b_0) ≤ 2C e_0` if `N₀(u) ≤ e_0`. -/
theorem norm0_sub_le_two_mul (hA : A.IsQuasiNormed C) {u a a' : U} {x : ℝ≥0∞}
    (ha : A.norm0 (u - a) ≤ x) (ha' : A.norm0 (u - a') ≤ x) : A.norm0 (a - a') ≤ 2 * C * x :=
  calc A.norm0 (a - a') = A.norm0 ((u - a') + -(u - a)) := by congr 1; abel
    _ ≤ C * (A.norm0 (u - a') + A.norm0 (-(u - a))) := hA.norm0_add_le _ _
    _ ≤ C * (x + x) := by
        rw [hA.norm0_neg]
        exact mul_le_mul_right (add_le_add ha' ha) C
    _ = 2 * C * x := by ring

end NearBest

/-! ### Jackson's and Bernstein's inequalities -/

/-- **Jackson's and Bernstein's inequalities of order `r`** for a couple `A = (N₀, N₁)`: a
smoothness quasi-seminorm `Y = smoothNorm : U → [0, ∞]` that is even and whose `ρ`-th power is
subadditive for an exponent `ρ > 0`, with Jackson's inequality `E(2^k, u) ≤ C_J 2^(-kr) Y(u)` for
all `k` and `u` and Bernstein's inequality `Y(a) ≤ C_B 2^(kr) N₀(a)` for `N₁(a) ≤ 2^k`, both
constants finite. If `A` is quasi-normed, evenness, the `ρ`-triangle inequality and `Y(0) = 0`
(from Bernstein's inequality at level `0`) make `(N₀, N₀ + Y)` a quasi-normed couple; the
`ρ`-triangle inequality also telescopes Bernstein's inequality over any number of levels with a
constant independent of that number. The normed counterpart for approximation schemes is
`ApproximationScheme.SmoothnessSpace`. -/
structure JacksonBernsteinData (A : InterpCouple U) (ρ r : ℝ) where
  /-- The exponent `ρ` is positive. -/
  rho_pos : 0 < ρ
  /-- The smoothness quasi-seminorm `Y`. -/
  smoothNorm : U → ℝ≥0∞
  /-- `Y` is even. -/
  smoothNorm_neg : ∀ a, smoothNorm (-a) = smoothNorm a
  /-- `Y^ρ` is subadditive. -/
  smoothNorm_add_rpow_le : ∀ a b, smoothNorm (a + b) ^ ρ ≤ smoothNorm a ^ ρ + smoothNorm b ^ ρ
  /-- The Jackson constant. -/
  CJ : ℝ≥0∞
  /-- The Jackson constant is finite. -/
  CJ_ne_top : CJ ≠ ∞
  /-- Jackson's inequality `E(2^k, u) ≤ C_J 2^(-kr) Y(u)`. -/
  jackson : ∀ k u,
    A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u ≤ CJ * dyadicWeight (-r) k * smoothNorm u
  /-- The Bernstein constant. -/
  CB : ℝ≥0∞
  /-- The Bernstein constant is finite. -/
  CB_ne_top : CB ≠ ∞
  /-- Bernstein's inequality `Y(a) ≤ C_B 2^(kr) N₀(a)` for `N₁(a) ≤ 2^k`. -/
  bernstein : ∀ k a, A.norm1 a ≤ ((2 ^ k : ℕ) : ℝ≥0∞) →
    smoothNorm a ≤ CB * dyadicWeight r k * A.norm0 a

namespace JacksonBernsteinData

variable {A : InterpCouple U} {C : ℝ≥0∞} {ρ r s : ℝ} {q : ℝ≥0∞} (J : A.JacksonBernsteinData ρ r)

/-- The **couple `(N₀, N₀ + Y)`** of Jackson's and Bernstein's inequalities: the first norm `N₀`
of `A` and `N₀ + Y` for the smoothness quasi-seminorm `Y`, the analogue of the couple
`(X, Y)` of a smoothness space `Y ↪ X`. -/
noncomputable def smoothnessCouple : InterpCouple U :=
  ⟨A.norm0, fun u => A.norm0 u + J.smoothNorm u⟩

/-- The first norm of `(N₀, N₀ + Y)` is `N₀`. -/
@[simp]
theorem smoothnessCouple_norm0 (u : U) : J.smoothnessCouple.norm0 u = A.norm0 u := rfl

/-- The second norm of `(N₀, N₀ + Y)` is `N₀ + Y`. -/
@[simp]
theorem smoothnessCouple_norm1 (u : U) :
    J.smoothnessCouple.norm1 u = A.norm0 u + J.smoothNorm u := rfl

/-- `Y(0) = 0` if `N₀(0) = 0` and `N₁(0) = 0`, by Bernstein's inequality at level `0`. -/
theorem smoothNorm_zero (h00 : A.norm0 0 = 0) (h10 : A.norm1 0 = 0) : J.smoothNorm 0 = 0 := by
  refine le_antisymm ((J.bernstein 0 0 ?_).trans_eq ?_) bot_le
  · rw [h10]
    exact zero_le
  · rw [h00, mul_zero]

/-- **The quasi-triangle inequality of `Y`**: `Y(a + b) ≤ C_ρ (Y(a) + Y(b))` with Mathlib's
constant `C_ρ = LpAddConst ρ`, from the `ρ`-triangle inequality, for every `ρ > 0`
(`ENNReal.le_mul_add_of_rpow_le_add_rpow`). -/
theorem smoothNorm_add_le (a b : U) :
    J.smoothNorm (a + b) ≤ LpAddConst (ENNReal.ofReal ρ) * (J.smoothNorm a + J.smoothNorm b) :=
  ENNReal.le_mul_add_of_rpow_le_add_rpow J.rho_pos (J.smoothNorm_add_rpow_le a b)

/-- **`(N₀, N₀ + Y)` is quasi-normed**: if `A` is quasi-normed with constant `C`, the couple
`(N₀, N₀ + Y)` is quasi-normed with constant `max(C, C_ρ)`, `C_ρ = LpAddConst ρ`: `Y` vanishes
at `0`, is even and satisfies the quasi-triangle inequality with the constant `C_ρ`
(`InterpCouple.JacksonBernsteinData.smoothNorm_zero`,
`InterpCouple.JacksonBernsteinData.smoothNorm_add_le`). -/
theorem isQuasiNormed_smoothnessCouple (hA : A.IsQuasiNormed C) :
    J.smoothnessCouple.IsQuasiNormed (max C (LpAddConst (ENNReal.ofReal ρ))) where
  ne_top := max_ne_top hA.ne_top (ENNReal.LpAddConst_lt_top _).ne
  norm0_zero := hA.norm0_zero
  norm1_zero := by
    rw [smoothnessCouple_norm1, hA.norm0_zero, J.smoothNorm_zero hA.norm0_zero hA.norm1_zero,
      add_zero]
  norm0_neg := hA.norm0_neg
  norm1_neg a := by
    rw [smoothnessCouple_norm1, smoothnessCouple_norm1, hA.norm0_neg, J.smoothNorm_neg]
  norm0_add_le a b := (hA.norm0_add_le a b).trans (mul_le_mul_left (le_max_left _ _) _)
  norm1_add_le a b := by
    simp only [smoothnessCouple_norm1]
    calc A.norm0 (a + b) + J.smoothNorm (a + b)
        ≤ C * (A.norm0 a + A.norm0 b) +
            LpAddConst (ENNReal.ofReal ρ) * (J.smoothNorm a + J.smoothNorm b) :=
          add_le_add (hA.norm0_add_le a b) (J.smoothNorm_add_le a b)
      _ ≤ max C (LpAddConst (ENNReal.ofReal ρ)) * (A.norm0 a + A.norm0 b) +
            max C (LpAddConst (ENNReal.ofReal ρ)) * (J.smoothNorm a + J.smoothNorm b) :=
          add_le_add (mul_le_mul_left (le_max_left _ _) _) (mul_le_mul_left (le_max_right _ _) _)
      _ = max C (LpAddConst (ENNReal.ofReal ρ)) *
            (A.norm0 a + J.smoothNorm a + (A.norm0 b + J.smoothNorm b)) := by ring

/-- **`(N₀, N₀ + Y)` is ordered**: `N₀(u) ≤ 1 · (N₀(u) + Y(u))` for every `u`. -/
theorem norm0_le_smoothnessCouple_norm1 (u : U) :
    J.smoothnessCouple.norm0 u ≤ 1 * J.smoothnessCouple.norm1 u := by
  rw [one_mul]
  exact le_self_add

/-- **The `ρ`-triangle inequality on finite sums**: if `N₀(0) = 0` and `N₁(0) = 0`, then
`Y(∑_{i ∈ t} g_i)^ρ ≤ ∑_{i ∈ t} Y(g_i)^ρ` for every finite family (Mathlib's
`Finset.le_sum_of_subadditive`). -/
theorem smoothNorm_sum_rpow_le (h00 : A.norm0 0 = 0) (h10 : A.norm1 0 = 0) {ι : Type*}
    (t : Finset ι) (g : ι → U) :
    J.smoothNorm (∑ i ∈ t, g i) ^ ρ ≤ ∑ i ∈ t, J.smoothNorm (g i) ^ ρ := by
  have h0 : J.smoothNorm 0 ^ ρ = 0 := by
    rw [J.smoothNorm_zero h00 h10, ENNReal.zero_rpow_of_pos J.rho_pos]
  exact Finset.le_sum_of_subadditive (fun a => J.smoothNorm a ^ ρ) h0.le
    J.smoothNorm_add_rpow_le t g

/-- **Bernstein's inequality in `ρ`-th powers**: if `N₁(a) ≤ 2^j` and `N₀(a) ≤ c x`, then
`Y(a)^ρ ≤ (c C_B)^ρ 2^(jrρ) x^ρ`. -/
theorem smoothNorm_rpow_le_of_norm1_le {a : U} {j : ℕ} {c x : ℝ≥0∞}
    (ha1 : A.norm1 a ≤ ((2 ^ j : ℕ) : ℝ≥0∞)) (ha0 : A.norm0 a ≤ c * x) :
    J.smoothNorm a ^ ρ ≤ (c * J.CB) ^ ρ * dyadicWeight (r * ρ) j * x ^ ρ := by
  have hρ := J.rho_pos.le
  calc J.smoothNorm a ^ ρ ≤ (c * J.CB * dyadicWeight r j * x) ^ ρ := by
        refine ENNReal.rpow_le_rpow ((J.bernstein j a ha1).trans ?_) hρ
        calc J.CB * dyadicWeight r j * A.norm0 a ≤ J.CB * dyadicWeight r j * (c * x) := by
              gcongr
          _ = c * J.CB * dyadicWeight r j * x := by ring
    _ = (c * J.CB) ^ ρ * dyadicWeight (r * ρ) j * x ^ ρ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hρ, ENNReal.mul_rpow_of_nonneg _ _ hρ,
          ENNReal.dyadicWeight_rpow]

/-- **Bernstein's inequality for near-best approximants**: let `A` be quasi-normed with constant
`C` and subadditive complexity, `r ≥ 0`, and let
`N₁(b_k) ≤ 2^k` and `N₀(u - b_k) ≤ e_k` for every `k`, with `e` decreasing and `N₀(u) ≤ e_0`. Then
`(2^(-kr) Y(b_k))^ρ ≤ 2 (2C C_B)^ρ 4^(rρ) ∑_{j ≤ k} 2^(-(k-j)rρ) e_j^ρ`. The telescoping
`b_k = b_0 + ∑_{j<k} (b_{j+1} - b_j)` is a finite sum, estimated with the `ρ`-triangle
inequality of `Y`; Bernstein's inequality applies to `b_0` at level `0` and to
`b_{j+1} - b_j` at level `j + 2` (`InterpCouple.norm1_sub_le_pow_add_two`), with
`N₀(b_0) ≤ 2C e_0` and `N₀(b_{j+1} - b_j) ≤ 2C e_j` (`InterpCouple.norm0_sub_le_two_mul`). The
terms of `b_0` and of the first block both sit at `j = 0`, hence the factor `2`
(`ENNReal.add_sum_range_le_two_mul_sum`). -/
theorem dyadicWeight_mul_smoothNorm_rpow_le_of_nearBest (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hr : 0 ≤ r) {u : U} {b : ℕ → U}
    {e : ℕ → ℝ≥0∞} (hb1 : ∀ k, A.norm1 (b k) ≤ ((2 ^ k : ℕ) : ℝ≥0∞))
    (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (he : Antitone e) (he0 : A.norm0 u ≤ e 0) (k : ℕ) :
    (dyadicWeight (-r) k * J.smoothNorm (b k)) ^ ρ ≤
      2 * (2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 2 *
        ∑ j ∈ range (k + 1), dyadicWeight (-(r * ρ)) (k - j) * e j ^ ρ := by
  have hρ := J.rho_pos
  have htel : b k = b 0 + ∑ j ∈ range k, (b (j + 1) - b j) := by
    rw [sum_range_sub (fun j => b j) k]
    abel
  have hw : ∀ j ≤ k, dyadicWeight (-(r * ρ)) (k - j) =
      dyadicWeight (-(r * ρ)) k * dyadicWeight (r * ρ) j := fun j hjk => by
    have h := ENNReal.dyadicWeight_mul_dyadicWeight_neg_sub 0 (r * ρ) hjk
    rwa [ENNReal.dyadicWeight_zero_left, one_mul, sub_zero] at h
  have h0 : dyadicWeight (-(r * ρ)) k * J.smoothNorm (b 0) ^ ρ ≤
      (2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 2 *
        (dyadicWeight (-(r * ρ)) (k - 0) * e 0 ^ ρ) := by
    have hn : A.norm0 (b 0) ≤ 2 * C * e 0 := by
      have h := norm0_sub_le_two_mul hA (hbe 0) (a' := 0) (by rwa [sub_zero])
      rwa [sub_zero] at h
    calc dyadicWeight (-(r * ρ)) k * J.smoothNorm (b 0) ^ ρ
        ≤ dyadicWeight (-(r * ρ)) k *
            ((2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 0 * e 0 ^ ρ) := by
          gcongr
          exact J.smoothNorm_rpow_le_of_norm1_le (hb1 0) hn
      _ = (2 * C * J.CB) ^ ρ * 1 * (dyadicWeight (-(r * ρ)) (k - 0) * e 0 ^ ρ) := by
          rw [ENNReal.dyadicWeight_zero_right, Nat.sub_zero]
          ring
      _ ≤ _ := by
          gcongr
          exact ENNReal.one_le_dyadicWeight (mul_nonneg hr hρ.le) 2
  have hj : ∀ j ∈ range k, dyadicWeight (-(r * ρ)) k * J.smoothNorm (b (j + 1) - b j) ^ ρ ≤
      (2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 2 *
        (dyadicWeight (-(r * ρ)) (k - j) * e j ^ ρ) := fun j hj => by
    have hn : A.norm0 (b (j + 1) - b j) ≤ 2 * C * e j :=
      norm0_sub_le_two_mul hA ((hbe (j + 1)).trans (he (Nat.le_succ j))) (hbe j)
    calc dyadicWeight (-(r * ρ)) k * J.smoothNorm (b (j + 1) - b j) ^ ρ
        ≤ dyadicWeight (-(r * ρ)) k *
            ((2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) (j + 2) * e j ^ ρ) := by
          gcongr
          exact J.smoothNorm_rpow_le_of_norm1_le
            (norm1_sub_le_pow_add_two hA.norm1_neg h1 (hb1 j) (hb1 (j + 1))) hn
      _ = _ := by
          rw [ENNReal.dyadicWeight_add_nat (r * ρ) j 2, hw j (mem_range.1 hj).le]
          ring
  calc (dyadicWeight (-r) k * J.smoothNorm (b k)) ^ ρ
      = dyadicWeight (-(r * ρ)) k * J.smoothNorm (b 0 + ∑ j ∈ range k, (b (j + 1) - b j)) ^ ρ := by
        rw [← htel, ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.dyadicWeight_rpow, neg_mul]
    _ ≤ dyadicWeight (-(r * ρ)) k * (J.smoothNorm (b 0) ^ ρ +
          ∑ j ∈ range k, J.smoothNorm (b (j + 1) - b j) ^ ρ) := by
        gcongr
        exact (J.smoothNorm_add_rpow_le _ _).trans
          (add_le_add le_rfl (J.smoothNorm_sum_rpow_le hA.norm0_zero hA.norm1_zero _ _))
    _ ≤ (2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 2 *
          (dyadicWeight (-(r * ρ)) (k - 0) * e 0 ^ ρ) + ∑ j ∈ range k,
            (2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 2 *
              (dyadicWeight (-(r * ρ)) (k - j) * e j ^ ρ) := by
        rw [mul_add, mul_sum]
        exact add_le_add h0 (sum_le_sum hj)
    _ ≤ 2 * ∑ j ∈ range (k + 1), (2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 2 *
          (dyadicWeight (-(r * ρ)) (k - j) * e j ^ ρ) :=
        ENNReal.add_sum_range_le_two_mul_sum (fun j => (2 * C * J.CB) ^ ρ *
          dyadicWeight (r * ρ) 2 * (dyadicWeight (-(r * ρ)) (k - j) * e j ^ ρ)) k
    _ = _ := by
        rw [← mul_sum]
        ring

end JacksonBernsteinData

/-! ### The Jackson–Bernstein theorem -/

/-- The constant of Bernstein's half of the Jackson–Bernstein theorem: with Mathlib's constant
`C_q = LpAddConst q`, `M = C_q (1 + γ_{1,q})` and `H = hardyConst ((r - s)ρ) (q/ρ)`, it is
`1 + C_q (C_q ((1 + C) M + C γ_{r-s,q}) + (2 (2C C_B)^ρ 4^(rρ) H)^(1/ρ) M)`. -/
noncomputable def jacksonBernsteinConst (C CB : ℝ≥0∞) (ρ r s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  1 + LpAddConst q * (LpAddConst q * ((1 + C) * (LpAddConst q * (1 + dyadicGeomConst 1 q)) +
    C * dyadicGeomConst (r - s) q) +
    (2 * (2 * C * CB) ^ ρ * dyadicWeight (r * ρ) 2 *
      hardyConst (r * ρ - s * ρ) (q / ENNReal.ofReal ρ)) ^ (1 / ρ) *
      (LpAddConst q * (1 + dyadicGeomConst 1 q)))

/-- The constant `jacksonBernsteinConst C C_B ρ r s q` is finite for `C, C_B < ∞`, `ρ > 0` and
`s < r`. -/
theorem jacksonBernsteinConst_ne_top {C CB : ℝ≥0∞} (hC : C ≠ ∞) (hCB : CB ≠ ∞) {ρ r s : ℝ}
    (hρ : 0 < ρ) (hsr : s < r) (q : ℝ≥0∞) : jacksonBernsteinConst C CB ρ r s q ≠ ∞ := by
  have hα : 0 < r * ρ - s * ρ := by
    rw [← sub_mul]
    exact mul_pos (sub_pos.2 hsr) hρ
  have hq : LpAddConst q ≠ ∞ := (ENNReal.LpAddConst_lt_top q).ne
  have hM : LpAddConst q * (1 + dyadicGeomConst 1 q) ≠ ∞ :=
    ENNReal.mul_ne_top hq (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.dyadicGeomConst_ne_top one_pos q⟩)
  have hT : (2 * (2 * C * CB) ^ ρ * dyadicWeight (r * ρ) 2 *
      hardyConst (r * ρ - s * ρ) (q / ENNReal.ofReal ρ)) ^ (1 / ρ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_pos.2 hρ).le (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hρ.le
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC) hCB)))
        (ENNReal.dyadicWeight_ne_top _ _)) (ENNReal.hardyConst_ne_top hα _))
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hq (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top hq (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, hC⟩) hM, ENNReal.mul_ne_top hC
        (ENNReal.dyadicGeomConst_ne_top (sub_pos.2 hsr) q)⟩), ENNReal.mul_ne_top hT hM⟩)⟩

namespace JacksonBernsteinData

variable {A : InterpCouple U} {C : ℝ≥0∞} {ρ r s : ℝ} {q : ℝ≥0∞} (J : A.JacksonBernsteinData ρ r)

/-- **Bernstein's half at one level**: if `A` is quasi-normed with constant `C`, `r ≥ 0` and
`N₀(u - b_k) ≤ e_k` for every `k`, then the K-functional of `(N₀, N₀ + Y)` satisfies
`K(2^(-kr), u) ≤ (1 + C) e_k + C N₀(u) 2^(-kr) + 2^(-kr) Y(b_k)`, from
`K(2^(-kr), u) ≤ N₀(u - b_k) + 2^(-kr) (N₀(b_k) + Y(b_k))`,
`N₀(b_k) ≤ C (e_k + N₀(u))` (`InterpCouple.norm0_le_of_sub_le`) and `2^(-kr) ≤ 1`. -/
theorem kFunctional_smoothnessCouple_le_of_nearBest (hA : A.IsQuasiNormed C) (hr : 0 ≤ r)
    {u : U} {b : ℕ → U} {e : ℕ → ℝ≥0∞} (hbe : ∀ k, A.norm0 (u - b k) ≤ e k) (k : ℕ) :
    J.smoothnessCouple.kFunctional (dyadicWeight (-r) k) u ≤
      (1 + C) * e k + C * A.norm0 u * dyadicWeight (-r) k +
        dyadicWeight (-r) k * J.smoothNorm (b k) := by
  have hw : dyadicWeight (-r) k ≤ 1 :=
    (ENNReal.dyadicWeight_anti (neg_nonpos.2 hr) (Nat.zero_le k)).trans_eq
      (ENNReal.dyadicWeight_zero_right _)
  calc J.smoothnessCouple.kFunctional (dyadicWeight (-r) k) u
      ≤ A.norm0 (u - b k) + dyadicWeight (-r) k * (A.norm0 (b k) + J.smoothNorm (b k)) :=
        kFunctional_le (b k) u
    _ ≤ e k + dyadicWeight (-r) k * (C * (e k + A.norm0 u) + J.smoothNorm (b k)) := by
        gcongr
        exacts [hbe k, norm0_le_of_sub_le hA (hbe k)]
    _ = e k + dyadicWeight (-r) k * (C * e k) + C * A.norm0 u * dyadicWeight (-r) k +
          dyadicWeight (-r) k * J.smoothNorm (b k) := by ring
    _ ≤ e k + 1 * (C * e k) + C * A.norm0 u * dyadicWeight (-r) k +
          dyadicWeight (-r) k * J.smoothNorm (b k) := by gcongr
    _ = (1 + C) * e k + C * A.norm0 u * dyadicWeight (-r) k +
          dyadicWeight (-r) k * J.smoothNorm (b k) := by ring

/-- **Bernstein's half of the Jackson–Bernstein theorem**: if `A` is quasi-normed with constant
`C` and its complexity is subadditive, and `0 ≤ s < r`, then for every `q` and every `u`,
`‖u‖_{s/r,r,q} ≤ jacksonBernsteinConst C C_B ρ r s q · ‖u‖^dy_{s,q}`
(`InterpCouple.jacksonBernsteinConst`), where
`‖u‖_{s/r,r,q} = N₀(u) + ‖(2^(ks) K(2^(-kr), u))_k‖_{ℓ_q}` is the norm of `(N₀, N₀ + Y)` on the
grid `t = 2^(-kr)` (`InterpCouple.interpNorm`). The near-best approximants of `u` with their
tolerances (`InterpCouple.exists_nearBest_tolerances`) take the place of the elements of `Y`;
the terms `2^(-kr) Y(b_k)` are summed with Hardy's inequality for partial sums in `ρ`-th powers
(`ENNReal.lqNorm_le_of_rpow_le_sum`,
`InterpCouple.JacksonBernsteinData.dyadicWeight_mul_smoothNorm_rpow_le_of_nearBest`) and the
three terms of the bound at one level with `InterpCouple.lqNorm_kFunctional_le_of_le`. -/
theorem interpNorm_smoothnessCouple_le_eNormDyadic (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hs : 0 ≤ s) (hsr : s < r) (u : U) :
    J.smoothnessCouple.interpNorm (s / r) r q u ≤
      jacksonBernsteinConst C J.CB ρ r s q * A.eNormDyadic s q u := by
  have hr : 0 < r := hs.trans_lt hsr
  obtain ⟨b, e, hb1, hbe, he, he0, hL⟩ :=
    exists_nearBest_tolerances hA.norm1_zero u s (by linarith)
  have hx := ENNReal.lqNorm_le_of_rpow_le_sum J.rho_pos
    (J.dyadicWeight_mul_smoothNorm_rpow_le_of_nearBest hA h1 hr.le hb1 hbe he he0) s q
  have hK := lqNorm_kFunctional_le_of_le (q := q) hsr.le
    (J.kFunctional_smoothnessCouple_le_of_nearBest hA hr.le hbe)
  have hN : A.norm0 u ≤ A.eNormDyadic s q u := le_self_add
  calc J.smoothnessCouple.interpNorm (s / r) r q u
      = A.norm0 u + lqNorm q (fun k => dyadicWeight s k *
          J.smoothnessCouple.kFunctional (dyadicWeight (-r) k) u) := by
        rw [interpNorm, mul_div_cancel₀ s hr.ne']
        rfl
    _ ≤ A.eNormDyadic s q u + LpAddConst q * (LpAddConst q *
          ((1 + C) * (LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q u) +
            C * A.eNormDyadic s q u * dyadicGeomConst (r - s) q) +
          (2 * (2 * C * J.CB) ^ ρ * dyadicWeight (r * ρ) 2 *
            hardyConst (r * ρ - s * ρ) (q / ENNReal.ofReal ρ)) ^ (1 / ρ) *
            (LpAddConst q * (1 + dyadicGeomConst 1 q) * A.eNormDyadic s q u)) := by
        refine add_le_add hN (hK.trans ?_)
        gcongr
        all_goals first
          | exact hL q
          | exact hx.trans (mul_le_mul_right (hL q) _)
    _ = jacksonBernsteinConst C J.CB ρ r s q * A.eNormDyadic s q u := by
        rw [jacksonBernsteinConst]
        ring

/-- **Jackson's half of the Jackson–Bernstein theorem**: if `A` is quasi-normed with constant
`C` and its complexity is subadditive, and `r ≠ 0`, then for every `s`, every `q` and every `u`,
`‖u‖^dy_{s,q} ≤ eJacksonConst C C_J s q · ‖u‖_{s/r,r,q}` for the norm of `(N₀, N₀ + Y)` on the
grid `t = 2^(-kr)`: Jackson's inequality for `Y` gives it for `N₀ + Y ≥ Y`
(`InterpCouple.eNormDyadic_le_interpNorm_of_jackson`). -/
theorem eNormDyadic_le_interpNorm_smoothnessCouple (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hr : r ≠ 0) (u : U) :
    A.eNormDyadic s q u ≤
      eJacksonConst C J.CJ s q * J.smoothnessCouple.interpNorm (s / r) r q u :=
  eNormDyadic_le_interpNorm_of_jackson (N := fun g => A.norm0 g + J.smoothNorm g) hA h1
    J.CJ_ne_top (fun k g => (J.jackson k g).trans (mul_le_mul_right le_add_self _)) hr s q u

/-- **The Jackson–Bernstein theorem for quasi-normed couples** (for a normed space `X` in place
of `N₀`: DeVore, Acta Numer. 7 (1998), §4.3, Theorem 1): if `A` is quasi-normed with constant
`C` and its complexity is subadditive, and `Y` satisfies Jackson's and Bernstein's inequalities
of order `r`, then for `0 < s < r` and `0 < q ≤ ∞`, `u` lies in the real interpolation space
`(N₀, N₀ + Y)_{s/r,q}` iff `‖u‖^dy_{s,q} < ∞`, that is, `E_{s,q} = (N₀, N₀ + Y)_{s/r,q}`. The
two halves are
`InterpCouple.JacksonBernsteinData.eNormDyadic_le_interpNorm_smoothnessCouple` and
`InterpCouple.JacksonBernsteinData.interpNorm_smoothnessCouple_le_eNormDyadic`, on the grid
`t = 2^(-kr)` of the ordered quasi-normed couple `(N₀, N₀ + Y)`
(`InterpCouple.memKMethod_iff_interpNorm_lt_top`). -/
theorem memKMethod_smoothnessCouple_iff (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (hs : 0 < s) (hsr : s < r)
    (hq : q ≠ 0) {u : U} :
    J.smoothnessCouple.MemKMethod (s / r) q u ↔ A.eNormDyadic s q u < ∞ := by
  have hr : 0 < r := hs.trans hsr
  rw [memKMethod_iff_interpNorm_lt_top (J.isQuasiNormed_smoothnessCouple hA) ENNReal.one_ne_top
    J.norm0_le_smoothnessCouple_norm1 (div_pos hs hr) hr hq]
  exact ⟨fun h => (J.eNormDyadic_le_interpNorm_smoothnessCouple hA h1 hr.ne' u).trans_lt
      (ENNReal.mul_lt_top (eJacksonConst_ne_top hA.ne_top J.CJ_ne_top s q).lt_top h),
    fun h => (J.interpNorm_smoothnessCouple_le_eNormDyadic hA h1 hs.le hsr u).trans_lt
      (ENNReal.mul_lt_top
        (jacksonBernsteinConst_ne_top hA.ne_top J.CB_ne_top J.rho_pos hsr q).lt_top h)⟩

end JacksonBernsteinData

/-! ### Classical spaces of a modulus as interpolation spaces -/

namespace CoupleModulusData

variable {A : InterpCouple U} {ρ θ : ℝ} (M : A.CoupleModulusData ρ θ)

/-- The **couple `(N₀, ‖·‖^ω_{s₁,q₁})`** of a modulus `ω` compatible with a `ρ`-normed couple
`A`: the first norm `N₀` of `A` and the classical quasi-norm
`‖f‖^ω_{s₁,q₁} = N₀(f) + ‖(2^(ks₁) ω(f, k))_k‖_{ℓ_{q₁}}`, the analogue of
`ApproximationScheme.ModulusData.leftModCouple`. -/
noncomputable def leftCoupleModCouple (s₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple U :=
  ⟨A.norm0, M.coupleModNorm s₁ q₁⟩

/-- The first norm of `(N₀, ‖·‖^ω_{s₁,q₁})` is `N₀`. -/
@[simp]
theorem leftCoupleModCouple_norm0 (s₁ : ℝ) (q₁ : ℝ≥0∞) (f : U) :
    (M.leftCoupleModCouple s₁ q₁).norm0 f = A.norm0 f := rfl

/-- The second norm of `(N₀, ‖·‖^ω_{s₁,q₁})` is the classical quasi-norm. -/
@[simp]
theorem leftCoupleModCouple_norm1 (s₁ : ℝ) (q₁ : ℝ≥0∞) (f : U) :
    (M.leftCoupleModCouple s₁ q₁).norm1 f = M.coupleModNorm s₁ q₁ f := rfl

/-- **The inverse inequality gives Bernstein's inequality at each scale**: for `0 ≤ r ≤ θ`, an
element `a` with `N₁(a) ≤ 2^j` satisfies `2^(kr) ω(a, k) ≤ C_B 2^(jr) N₀(a)` for every `k`. For
`k ≤ j` this is `2^(kr) ≤ 2^(jr)`; for `k > j`, `2^(kr) 2^(-(k-j)θ) = 2^(jr) 2^((k-j)(r-θ))` and
`r - θ ≤ 0`. -/
theorem dyadicWeight_mul_modulus_le_of_norm1_le {r : ℝ} (hr : 0 ≤ r) (hrθ : r ≤ θ) {a : U}
    {j : ℕ} (ha : A.norm1 a ≤ ((2 ^ j : ℕ) : ℝ≥0∞)) (k : ℕ) :
    dyadicWeight r k * M.modulus a k ≤ M.CB * dyadicWeight r j * A.norm0 a := by
  have hw : dyadicWeight r k * dyadicWeight (-θ) (k - j) ≤ dyadicWeight r j := by
    rcases le_total k j with hkj | hjk
    · rw [Nat.sub_eq_zero_of_le hkj, ENNReal.dyadicWeight_zero_right, mul_one]
      exact ENNReal.dyadicWeight_mono hr hkj
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
      rw [Nat.add_sub_cancel_left, ENNReal.dyadicWeight_add_nat, mul_assoc,
        ← ENNReal.dyadicWeight_add]
      calc dyadicWeight r j * dyadicWeight (r + -θ) m ≤ dyadicWeight r j * 1 := by
            gcongr
            exact (ENNReal.dyadicWeight_anti (by linarith) (Nat.zero_le m)).trans_eq
              (ENNReal.dyadicWeight_zero_right _)
        _ = dyadicWeight r j := mul_one _
  calc dyadicWeight r k * M.modulus a k
      ≤ dyadicWeight r k * (M.CB * dyadicWeight (-θ) (k - j) * A.norm0 a) := by
        gcongr
        exact M.inverse j k a ha
    _ = M.CB * (dyadicWeight r k * dyadicWeight (-θ) (k - j)) * A.norm0 a := by ring
    _ ≤ M.CB * dyadicWeight r j * A.norm0 a := by gcongr

/-- **The `ρ`-triangle inequality of the weighted supremum of the modulus**: for every `r`,
`(sup_k 2^(kr) ω(f + g, k))^ρ ≤ (sup_k 2^(kr) ω(f, k))^ρ + (sup_k 2^(kr) ω(g, k))^ρ`, from the
`ρ`-triangle inequality of `ω(·, k)` at each scale; the `ρ`-th power of a supremum is the
supremum of the `ρ`-th powers (Mathlib's `ENNReal.orderIsoRpow`), and the supremum of a sum is at
most the sum of the suprema (Mathlib's `iSup_add_le`). -/
theorem lqNorm_top_add_rpow_le (r : ℝ) (f g : U) :
    lqNorm ∞ (fun k => dyadicWeight r k * M.modulus (f + g) k) ^ ρ ≤
      lqNorm ∞ (fun k => dyadicWeight r k * M.modulus f k) ^ ρ +
        lqNorm ∞ (fun k => dyadicWeight r k * M.modulus g k) ^ ρ := by
  have hρ := M.rho_pos
  have hsup : ∀ h : U, lqNorm ∞ (fun k => dyadicWeight r k * M.modulus h k) ^ ρ =
      ⨆ k, (dyadicWeight r k * M.modulus h k) ^ ρ := fun h => by
    rw [ENNReal.lqNorm_top]
    exact (ENNReal.orderIsoRpow ρ hρ).map_iSup _
  have hpow : ∀ (h : U) (k : ℕ),
      (dyadicWeight r k * M.modulus h k) ^ ρ = dyadicWeight (r * ρ) k * M.modulus h k ^ ρ :=
    fun h k => by rw [ENNReal.mul_rpow_of_nonneg _ _ hρ.le, ENNReal.dyadicWeight_rpow]
  rw [hsup, hsup, hsup]
  calc ⨆ k, (dyadicWeight r k * M.modulus (f + g) k) ^ ρ
      ≤ ⨆ k, ((dyadicWeight r k * M.modulus f k) ^ ρ +
          (dyadicWeight r k * M.modulus g k) ^ ρ) := iSup_mono fun k => by
        rw [hpow, hpow, hpow, ← mul_add]
        gcongr
        exact M.add_rpow_le f g k
    _ ≤ _ := iSup_add_le _ _

/-- **Jackson's and Bernstein's inequalities for the classical space of a modulus**: for an even
modulus `ω` compatible with `A` of exponent `ρ` and inverse order `θ`, and `0 ≤ r ≤ θ`, the
smoothness quasi-seminorm `Y(f) = sup_k 2^(kr) ω(f, k)` satisfies Jackson's inequality
`E(2^k, f) ≤ C_J 2^(-kr) Y(f)`, from `E(2^k, f) ≤ C_J ω(f, k)` and `ω(f, k) ≤ 2^(-kr) Y(f)`, and
Bernstein's inequality `Y(a) ≤ C_B 2^(kr) N₀(a)` for `N₁(a) ≤ 2^k`
(`InterpCouple.CoupleModulusData.dyadicWeight_mul_modulus_le_of_norm1_le`); `Y^ρ` is subadditive
(`InterpCouple.CoupleModulusData.lqNorm_top_add_rpow_le`). The evenness of `ω` gives the evenness
of `Y`. -/
noncomputable def jacksonBernsteinData (hωneg : ∀ f k, M.modulus (-f) k = M.modulus f k)
    {r : ℝ} (hr : 0 ≤ r) (hrθ : r ≤ θ) : A.JacksonBernsteinData ρ r where
  rho_pos := M.rho_pos
  smoothNorm f := lqNorm ∞ (fun k => dyadicWeight r k * M.modulus f k)
  smoothNorm_neg f := by simp only [hωneg]
  smoothNorm_add_rpow_le := M.lqNorm_top_add_rpow_le r
  CJ := M.CJ
  CJ_ne_top := M.CJ_ne_top
  jackson k u := (M.jackson u k).trans (by
    rw [mul_assoc]
    gcongr
    exact ENNReal.le_dyadicWeight_neg_mul_lqNorm ENNReal.top_ne_zero r (M.modulus u) k)
  CB := M.CB
  CB_ne_top := M.CB_ne_top
  bernstein k a ha := by
    rw [ENNReal.lqNorm_top]
    exact iSup_le fun i => M.dyadicWeight_mul_modulus_le_of_norm1_le hr hrθ ha i

/-- **The couple of Jackson's and Bernstein's inequalities of a modulus** is the couple
`(N₀, ‖·‖^ω_{r,∞})`: `N₀ + Y` with `Y(f) = sup_k 2^(kr) ω(f, k)` is the classical quasi-norm
`‖·‖^ω_{r,∞}`. -/
theorem smoothnessCouple_jacksonBernsteinData
    (hωneg : ∀ f k, M.modulus (-f) k = M.modulus f k) {r : ℝ} (hr : 0 ≤ r) (hrθ : r ≤ θ) :
    (M.jacksonBernsteinData hωneg hr hrθ).smoothnessCouple = M.leftCoupleModCouple r ∞ := rfl

/-- **Classical spaces of a modulus as interpolation spaces of `(N₀, ‖·‖^ω_{r,∞})`**: for an even
modulus `ω` compatible with `A` of exponent `ρ` and inverse order `θ`, `0 < s < r ≤ θ` and
`0 < q ≤ ∞`, `f` lies in the real interpolation space `(N₀, ‖·‖^ω_{r,∞})_{s/r,q}` iff
`‖f‖^ω_{s,q} = N₀(f) + ‖(2^(ks) ω(f, k))_k‖_{ℓ_q} < ∞`. The Jackson–Bernstein theorem
(`InterpCouple.JacksonBernsteinData.memKMethod_smoothnessCouple_iff`) applies to
`InterpCouple.CoupleModulusData.jacksonBernsteinData`, and the coincidence theorem
(`InterpCouple.CoupleModulusData.eNormDyadic_lt_top_iff`) shows that the dyadic norm
`‖f‖^dy_{s,q}` is finite iff the classical quasi-norm `‖f‖^ω_{s,q}` is, for `0 ≤ s < θ`. For
`r < θ`, `InterpCouple.CoupleModulusData.memKMethod_leftCoupleModCouple_iff` with `s₁ = r`,
`q₁ = ∞` and `η = s/r` gives the same equivalence for every compatible modulus; the evenness of
`ω` serves the endpoint `r = θ`. -/
theorem memKMethod_leftCoupleModCouple_top_iff
    (hωneg : ∀ f k, M.modulus (-f) k = M.modulus f k) {r s : ℝ} (hs : 0 < s) (hsr : s < r)
    (hrθ : r ≤ θ) {q : ℝ≥0∞} (hq : q ≠ 0) {f : U} :
    (M.leftCoupleModCouple r ∞).MemKMethod (s / r) q f ↔ M.coupleModNorm s q f < ∞ := by
  have h := (M.jacksonBernsteinData hωneg (hs.le.trans hsr.le) hrθ).memKMethod_smoothnessCouple_iff
    M.isQuasiNormed M.norm1_add_le hs hsr hq (u := f)
  rw [M.smoothnessCouple_jacksonBernsteinData] at h
  rw [h]
  exact M.eNormDyadic_lt_top_iff hs.le (hsr.trans_le hrθ) f

/-- **Interpolation of `N₀` and a classical space of a modulus**: for a modulus `ω` compatible with
`A` of exponent `ρ` and inverse order `θ`, `0 < s₁ < θ`, `0 < η < 1` and `0 < q₁, q ≤ ∞`, `f`
lies in the real interpolation space `(N₀, ‖·‖^ω_{s₁,q₁})_{η,q}` iff `‖f‖^ω_{ηs₁,q} < ∞`. The
classical quasi-norm `‖·‖^ω_{s₁,q₁}` and the dyadic norm of `E_{s₁,q₁}` bound each other
(`InterpCouple.CoupleModulusData.eNormDyadic_le_coupleModNorm`,
`InterpCouple.CoupleModulusData.coupleModNorm_le_eNormDyadic`), so the couple has the
interpolation spaces of `(N₀, E_{s₁,q₁})` (`InterpCouple.memKMethod_congr`), and
`(N₀, E_{s₁,q₁})_{η,q}` is the space of finite dyadic norm `‖·‖^dy_{ηs₁,q}`
(`InterpCouple.memKMethod_leftECouple_iff`); the
coincidence theorem (`InterpCouple.CoupleModulusData.eNormDyadic_lt_top_iff`) turns this into
`‖f‖^ω_{ηs₁,q} < ∞`. The theorem holds for every compatible modulus. -/
theorem memKMethod_leftCoupleModCouple_iff {s₁ η : ℝ} (hs₁ : 0 < s₁) (hs₁θ : s₁ < θ)
    (hη : 0 < η) (hη' : η < 1) {q₁ q : ℝ≥0∞} (hq₁ : q₁ ≠ 0) (hq : q ≠ 0) {f : U} :
    (M.leftCoupleModCouple s₁ q₁).MemKMethod η q f ↔ M.coupleModNorm (η * s₁) q f < ∞ := by
  have hlt : η * s₁ < θ := (mul_lt_of_lt_one_left hs₁ hη').trans hs₁θ
  have hcongr : (M.leftCoupleModCouple s₁ q₁).MemKMethod η q f ↔
      (A.leftECouple s₁ q₁).MemKMethod η q f :=
    memKMethod_congr (A := M.leftCoupleModCouple s₁ q₁) (B := A.leftECouple s₁ q₁)
      ENNReal.one_ne_top (max_lt ENNReal.one_lt_top M.CJ_ne_top.lt_top).ne
      ENNReal.one_ne_top (M.coupleInverseConst_ne_top hs₁θ q₁) (fun a => (one_mul _).ge)
      (fun a => M.eNormDyadic_le_coupleModNorm a) (fun a => (one_mul _).ge)
      (fun a => M.coupleModNorm_le_eNormDyadic hs₁.le hs₁θ a)
  rw [hcongr, memKMethod_leftECouple_iff M.isQuasiNormed M.norm1_add_le hs₁ hη hη' hq₁ hq]
  exact M.eNormDyadic_lt_top_iff (mul_pos hη hs₁).le hlt f

end CoupleModulusData

end InterpCouple
