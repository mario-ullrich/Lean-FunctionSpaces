/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.BesovModuli
public import ApproximationSpaces.Decompositions.Atomic
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Lipschitz atoms on the torus

A **Lipschitz atom** of level `j` at the grid point `2^(-j) m ∈ 𝕋^d` (`Torus.gridPoint`) is a
continuous function `a` with

`|a| ≤ 1`,   `|a(x) - a(y)| ≤ 2^j ‖x - y‖`,   `a = 0` outside the ball of radius `D 2^(-j)`

around the grid point (`Torus.IsLipAtom`), as in Schneider–Vybíral, *Non-smooth atomic
decompositions*, with balls of the sup norm in place of dilated cubes.  The atoms of one level
overlap at most `(2D + 1)^d` times (`Torus.card_filter_norm_sub_gridPoint_le`), so in `L_2`

* **size**: `‖∑_m c_m a_m‖_2 ≲ 2^(-jd/2) ‖c‖_{ℓ_2}`,
* **decay**: `E_{2^k}(∑_m c_m a_m)_2 ≲ 2^(-(k-j)) 2^(-jd/2) ‖c‖_{ℓ_2}` for `k ≥ j`, from Jackson's
  theorem `E_n(f)_2 ≤ (d + 1) ω(f, 1/n)_2` and the Lipschitz bound on translates.

So Lipschitz atoms form an atomic system of smoothness `σ = 1` and size exponent `δ = d/2` for
the trigonometric scheme in `L_2(𝕋^d)` (`Torus.lipAtomicSystem`), and for `0 < s < 1` every
Lipschitz-atomic sum with coefficients in `b^s_{2,q}` lies in `B^s_{2,q}(𝕋^d)`
(`Torus.memBesov_of_lipAtoms`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal BoundedContinuousFunction TorusHaar

namespace Torus

variable {d : Type*} [Fintype d]

/-- The dyadic grid point `2^(-j) m` of `𝕋^d`, the centre of the atoms at position `m`. -/
noncomputable def gridPoint (j : ℕ) (m : d → Fin (2 ^ j)) : UnitAddTorus d :=
  fun i => (((m i : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) : ℝ)

/-- **One-dimensional overlap count**: at most `2R + 1` of the points `l/N` of the circle lie
within `R/N` of a given point. -/
theorem card_filter_norm_sub_le {N : ℕ} (hN : 0 < N) (R : ℕ) (u : UnitAddCircle) :
    (Finset.univ.filter fun l : Fin N =>
      ‖u - ((((l : ℕ) : ℝ) / N : ℝ) : UnitAddCircle)‖ ≤ R / N).card ≤ 2 * R + 1 := by
  induction u using QuotientAddGroup.induction_on with
  | H y =>
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set z₀ : ℤ := ⌈(N : ℝ) * y⌉
  set φ : Fin N → ℤ := fun l => (l : ℤ) + N * round (y - ((l : ℕ) : ℝ) / N)
  have hclose : ∀ l : Fin N, ‖((y : ℝ) : UnitAddCircle) - ((((l : ℕ) : ℝ) / N : ℝ) :
      UnitAddCircle)‖ ≤ R / N → |(N : ℝ) * y - φ l| ≤ R := fun l hl => by
    rw [← AddCircle.coe_sub, AddCircle.norm_eq] at hl
    simp only [inv_one, one_mul, mul_one] at hl
    have h1 : (N : ℝ) * y - φ l = N * (y - ((l : ℕ) : ℝ) / N - round (y - ((l : ℕ) : ℝ) / N)) := by
      simp only [φ]; push_cast; field_simp; ring
    rw [h1, abs_mul, abs_of_pos hN']
    calc (N : ℝ) * |y - ((l : ℕ) : ℝ) / N - round (y - ((l : ℕ) : ℝ) / N)| ≤ N * (R / N) := by
          gcongr
      _ = R := by field_simp
  have hmaps : ∀ l ∈ Finset.univ.filter (fun l : Fin N => ‖((y : ℝ) : UnitAddCircle) -
      ((((l : ℕ) : ℝ) / N : ℝ) : UnitAddCircle)‖ ≤ R / N),
      φ l ∈ Finset.Icc (z₀ - R) (z₀ + R) := fun l hl => by
    rw [Finset.mem_filter] at hl
    have h := abs_le.1 (hclose l hl.2)
    have hc1 : (N : ℝ) * y ≤ z₀ := Int.le_ceil _
    have hc2 : (z₀ : ℝ) < N * y + 1 := Int.ceil_lt_add_one _
    have hlow : ((z₀ - R - 1 : ℤ) : ℝ) < φ l := by push_cast; linarith
    have hup : (φ l : ℝ) ≤ ((z₀ + R : ℤ) : ℝ) := by push_cast; linarith
    rw [Finset.mem_Icc]
    constructor
    · have := Int.cast_lt.1 hlow; omega
    · exact Int.cast_le.1 hup
  have hinj : Set.InjOn φ (Finset.univ.filter (fun l : Fin N => ‖((y : ℝ) : UnitAddCircle) -
      ((((l : ℕ) : ℝ) / N : ℝ) : UnitAddCircle)‖ ≤ R / N) : Set (Fin N)) := fun l _ l' _ h => by
    simp only [φ] at h
    have hdvd : (N : ℤ) ∣ ((l : ℕ) : ℤ) - ((l' : ℕ) : ℤ) :=
      ⟨round (y - ((l' : ℕ) : ℝ) / N) - round (y - ((l : ℕ) : ℝ) / N), by linarith⟩
    have habs : |((l : ℕ) : ℤ) - ((l' : ℕ) : ℤ)| < N := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact Fin.ext (by omega)
  calc _ ≤ (Finset.Icc (z₀ - R) (z₀ + R)).card := Finset.card_le_card_of_injOn φ hmaps hinj
    _ = 2 * R + 1 := by
        rw [Int.card_Icc, show z₀ + R + 1 - (z₀ - R) = ((2 * R + 1 : ℕ) : ℤ) by push_cast; ring,
          Int.toNat_natCast]

/-- **Overlap count on `𝕋^d`**: at most `(2R + 1)^d` grid points of level `j` lie within
`R 2^(-j)` of a given point. -/
theorem card_filter_norm_sub_gridPoint_le [DecidableEq d] (j R : ℕ) (x : UnitAddTorus d) :
    (Finset.univ.filter fun m : d → Fin (2 ^ j) =>
      ‖x - gridPoint j m‖ ≤ R / ((2 ^ j : ℕ) : ℝ)).card ≤ (2 * R + 1) ^ Fintype.card d := by
  classical
  have hsub : (Finset.univ.filter fun m : d → Fin (2 ^ j) =>
      ‖x - gridPoint j m‖ ≤ R / ((2 ^ j : ℕ) : ℝ)) ⊆ Fintype.piFinset fun i =>
        Finset.univ.filter fun l : Fin (2 ^ j) =>
          ‖x i - ((((l : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) : ℝ) : UnitAddCircle)‖ ≤
            R / ((2 ^ j : ℕ) : ℝ) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    rw [Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (norm_le_pi_norm (x - gridPoint j m) i).trans hm
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ i, (Finset.univ.filter fun l : Fin (2 ^ j) =>
          ‖x i - ((((l : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) : ℝ) : UnitAddCircle)‖ ≤
            R / ((2 ^ j : ℕ) : ℝ)).card
      ≤ (2 * R + 1) ^ (Finset.univ : Finset d).card :=
        Finset.prod_le_pow_card _ _ _ fun i _ =>
          card_filter_norm_sub_le (Nat.pos_of_ne_zero (by positivity)) R (x i)
    _ = _ := by rw [Finset.card_univ]

/-- The volume of a ball of the circle: `|B(u, ρ)| ≤ 2ρ`. -/
theorem volume_closedBall_circle_le (u : UnitAddCircle) {ρ : ℝ} :
    volume (Metric.closedBall u ρ) ≤ ENNReal.ofReal (2 * ρ) := by
  rw [TorusHaar.volume_eq_haarAddCircle]
  have h := AddCircle.volume_closedBall (T := 1) (x := u) ρ
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] at h
  rw [h]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- The volume of a ball of `𝕋^d` for the sup norm: `|B(c, ρ)| ≤ (2ρ)^d`. -/
theorem volume_closedBall_le (c : UnitAddTorus d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.closedBall c ρ) ≤ ENNReal.ofReal (2 * ρ) ^ Fintype.card d := by
  rw [closedBall_pi c hρ, volume_pi, Measure.pi_pi]
  calc ∏ i, volume (Metric.closedBall (c i) ρ) ≤ ENNReal.ofReal (2 * ρ) ^
        (Finset.univ : Finset d).card :=
        Finset.prod_le_pow_card _ _ _ fun i _ => volume_closedBall_circle_le (c i)
    _ = _ := by rw [Finset.card_univ]

open Classical in
/-- **`L_2` bound for sums with bounded overlap**: if `F_m` vanishes outside `S_m`,
`|F_m| ≤ b_m`, and every point lies in at most `N` of the sets `S_m`, then
`∫ |∑_m F_m|² ≤ N ∑_m b_m² |S_m|`. -/
theorem lintegral_enorm_sum_sq_le {M : Type*} [Fintype M] (F : M → UnitAddTorus d → ℂ)
    (S : M → Set (UnitAddTorus d)) (hS : ∀ m, MeasurableSet (S m)) (b : M → ℝ)
    (hF : ∀ m x, x ∉ S m → F m x = 0) (hb : ∀ m x, ‖F m x‖ ≤ b m) (N : ℕ)
    (hN : ∀ x, (Finset.univ.filter fun m => x ∈ S m).card ≤ N) :
    ∫⁻ x, ‖∑ m, F m x‖ₑ ^ (2 : ℝ) ≤ N * ∑ m, ENNReal.ofReal (b m ^ 2) * volume (S m) := by
  classical
  have hpt : ∀ x, ‖∑ m, F m x‖ₑ ^ (2 : ℝ) ≤
      N * ∑ m, (S m).indicator (fun _ => ENNReal.ofReal (b m ^ 2)) x := fun x => by
    set T := Finset.univ.filter fun m => x ∈ S m
    have hsum : ∑ m, F m x = ∑ m ∈ T, F m x :=
      (Finset.sum_subset (Finset.filter_subset _ _) fun m _ hm => hF m x (by
        simpa [T] using hm)).symm
    have hreal : ‖∑ m, F m x‖ ^ 2 ≤ N * ∑ m ∈ T, b m ^ 2 := by
      rw [hsum]
      calc ‖∑ m ∈ T, F m x‖ ^ 2 ≤ (∑ m ∈ T, b m) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans
              (Finset.sum_le_sum fun m _ => hb m x)) 2
        _ ≤ T.card * ∑ m ∈ T, b m ^ 2 := sq_sum_le_card_mul_sum_sq
        _ ≤ N * ∑ m ∈ T, b m ^ 2 := by
            gcongr
            exact_mod_cast hN x
    have hind : ∑ m ∈ T, ENNReal.ofReal (b m ^ 2) =
        ∑ m, (S m).indicator (fun _ => ENNReal.ofReal (b m ^ 2)) x := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => x ∈ S m)]
      rw [Finset.sum_congr rfl (fun m hm => Set.indicator_of_mem (by simpa using hm) _),
        Finset.sum_eq_zero (fun m hm => Set.indicator_of_notMem (by simpa using hm) _), add_zero]
    calc ‖∑ m, F m x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖∑ m, F m x‖ ^ 2) := by
          rw [← ofReal_norm, ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (N * ∑ m ∈ T, b m ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = N * ∑ m ∈ T, ENNReal.ofReal (b m ^ 2) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg fun m _ => sq_nonneg _]
      _ = _ := by rw [hind]
  calc ∫⁻ x, ‖∑ m, F m x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x, N * ∑ m, (S m).indicator (fun _ => ENNReal.ofReal (b m ^ 2)) x :=
        lintegral_mono hpt
    _ = N * ∑ m, ENNReal.ofReal (b m ^ 2) * volume (S m) := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N),
          lintegral_finsetSum _ fun m _ => (measurable_const.indicator (hS m))]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [lintegral_indicator_const (hS m)]

open ENNReal (dyadicWeight finLqNorm) in
/-- The ball of radius `R 2^(-j)` has volume `≤ (2R)^d 2^(-jd)`. -/
theorem volume_closedBall_gridPoint_le (j R : ℕ) (c : UnitAddTorus d) :
    volume (Metric.closedBall c (R / ((2 ^ j : ℕ) : ℝ))) ≤
      ENNReal.ofReal (2 * R) ^ Fintype.card d * dyadicWeight (-(Fintype.card d : ℝ)) j := by
  refine (volume_closedBall_le c (by positivity)).trans_eq ?_
  have h2 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  rw [mul_div_assoc', ENNReal.ofReal_div_of_pos h2, ENNReal.ofReal_natCast, div_eq_mul_inv,
    mul_pow, ← ENNReal.natCast_two_pow_rpow, ENNReal.rpow_neg, ENNReal.rpow_natCast,
    ENNReal.inv_pow]

open ENNReal (dyadicWeight finLqNorm) in
/-- `(∑_m ‖c_m‖²)^(1/2)` is the `ℓ_2` norm of the coefficients. -/
theorem finLqNorm_two_eq {M : Type*} [Fintype M] (c : M → ℝ) :
    finLqNorm 2 (fun m => ‖c m‖ₑ) = (∑ m, ENNReal.ofReal (c m ^ 2)) ^ (1 / 2 : ℝ) := by
  simp only [finLqNorm, ENNReal.ofNat_ne_top, ↓reduceIte, ENNReal.toReal_ofNat]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
    sq_abs]

open ENNReal (dyadicWeight finLqNorm) in
/-- **The `L_2` norm of a sum of functions near the grid**: if `G = ∑_m F_m`, `F_m` vanishes
outside the ball of radius `R 2^(-j)` around the grid point and `|F_m| ≤ |c_m| τ`, then
`‖G‖_2 ≤ ((2R + 1)^d (2R)^d)^(1/2) τ 2^(-jd/2) ‖c‖_{ℓ_2}`. -/
theorem eLpNorm_le_of_overlap [DecidableEq d] {j : ℕ} (R : ℕ) {G : UnitAddTorus d → ℂ}
    (hG : AEStronglyMeasurable G volume) (F : (d → Fin (2 ^ j)) → UnitAddTorus d → ℂ)
    (hGF : ∀ x, G x = ∑ m, F m x) (c : (d → Fin (2 ^ j)) → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hF : ∀ m x, R / ((2 ^ j : ℕ) : ℝ) < ‖x - gridPoint j m‖ → F m x = 0)
    (hb : ∀ m x, ‖F m x‖ ≤ |c m| * τ) :
    eLpNorm G 2 volume ≤ ((((2 * R + 1) ^ Fintype.card d : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (2 * R) ^ Fintype.card d) ^ (1 / 2 : ℝ) * ENNReal.ofReal τ *
        (dyadicWeight (-(Fintype.card d / 2 : ℝ)) j * finLqNorm 2 (fun m => ‖c m‖ₑ)) := by
  set r : ℝ := R / ((2 ^ j : ℕ) : ℝ)
  set S : (d → Fin (2 ^ j)) → Set (UnitAddTorus d) := fun m => Metric.closedBall (gridPoint j m) r
  set N : ℕ := (2 * R + 1) ^ Fintype.card d
  set V : ℝ≥0∞ := ENNReal.ofReal (2 * R) ^ Fintype.card d
  set w := dyadicWeight (-(Fintype.card d : ℝ)) j
  have hS : ∀ m, MeasurableSet (S m) := fun m => Metric.isClosed_closedBall.measurableSet
  have hint := lintegral_enorm_sum_sq_le F S hS (fun m => |c m| * τ)
    (fun m x hx => hF m x (by simpa [S, Metric.mem_closedBall, dist_eq_norm] using hx)) hb N
    (fun x => by
      convert card_filter_norm_sub_gridPoint_le j R x using 2
      ext m; simp [S, Metric.mem_closedBall, dist_eq_norm, r])
  have hvol : ∀ m, volume (S m) ≤ V * w := fun m => volume_closedBall_gridPoint_le j R _
  have hsum : ∑ m, ENNReal.ofReal ((|c m| * τ) ^ 2) * volume (S m) ≤
      ENNReal.ofReal (τ ^ 2) * V * w * ∑ m, ENNReal.ofReal (c m ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [mul_pow, sq_abs, ENNReal.ofReal_mul (sq_nonneg _)]
    calc ENNReal.ofReal (c m ^ 2) * ENNReal.ofReal (τ ^ 2) * volume (S m)
        ≤ ENNReal.ofReal (c m ^ 2) * ENNReal.ofReal (τ ^ 2) * (V * w) := by gcongr; exact hvol m
      _ = _ := by ring
  have hG2 : eLpNorm G 2 volume = (∫⁻ x, ‖∑ m, F m x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hG]
    simp only [ENNReal.toReal_ofNat, hGF]
  rw [hG2, finLqNorm_two_eq]
  calc (∫⁻ x, ‖∑ m, F m x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * (ENNReal.ofReal (τ ^ 2) * V * w * ∑ m, ENNReal.ofReal (c m ^ 2))) ^
          (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hint.trans (by gcongr)) (by norm_num)
    _ = ((N : ℝ≥0∞) * V) ^ (1 / 2 : ℝ) * ENNReal.ofReal (τ ^ 2) ^ (1 / 2 : ℝ) *
          (w ^ (1 / 2 : ℝ) * (∑ m, ENNReal.ofReal (c m ^ 2)) ^ (1 / 2 : ℝ)) := by
        rw [show (N : ℝ≥0∞) * (ENNReal.ofReal (τ ^ 2) * V * w * ∑ m, ENNReal.ofReal (c m ^ 2)) =
            ((N : ℝ≥0∞) * V) * ENNReal.ofReal (τ ^ 2) * (w * ∑ m, ENNReal.ofReal (c m ^ 2)) by
              ring]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _
          (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ = _ := by
        have hτ2 : ENNReal.ofReal (τ ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal τ := by
          rw [ENNReal.ofReal_pow hτ, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
        have hw : w ^ (1 / 2 : ℝ) = dyadicWeight (-(Fintype.card d / 2 : ℝ)) j := by
          rw [ENNReal.dyadicWeight_rpow]; congr 1; ring
        rw [hτ2, hw]

/-- A **Lipschitz atom** of level `j` at position `m` with support radius `D`: `|a| ≤ 1`,
`|a(x) - a(y)| ≤ 2^j ‖x - y‖`, and `a = 0` outside the ball of radius `D 2^(-j)` around the grid
point `2^(-j) m`. -/
structure IsLipAtom (D j : ℕ) (m : d → Fin (2 ^ j)) (a : UnitAddTorus d →ᵇ ℂ) : Prop where
  norm_le : ∀ x, ‖a x‖ ≤ 1
  lipschitz : ∀ x y, ‖a x - a y‖ ≤ 2 ^ j * ‖x - y‖
  eq_zero : ∀ x, D / ((2 ^ j : ℕ) : ℝ) < ‖x - gridPoint j m‖ → a x = 0

/-- `0` is a Lipschitz atom. -/
theorem isLipAtom_zero (D j : ℕ) (m : d → Fin (2 ^ j)) : IsLipAtom D j m 0 where
  norm_le x := by simp
  lipschitz x y := by simp
  eq_zero x _ := rfl

/-- The `L_2` norm of the difference of a translate: `‖τ_h g - g‖_2 = ‖g(· + h) - g‖_2` for a
bounded continuous `g`. -/
theorem enorm_translate_toLp_sub (h : UnitAddTorus d) (g : UnitAddTorus d →ᵇ ℂ) :
    ‖translate h (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ g) -
      BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ g‖ₑ =
        eLpNorm (fun x => g (x + h) - g x) 2 volume := by
  rw [Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  have hg := BoundedContinuousFunction.coeFn_toLp 2 volume ℝ g
  have hgh : (fun x => (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ g) (x + h)) =ᵐ[volume]
      fun x => g (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [Lp.coeFn_sub (translate h (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ g))
    (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ g),
    coeFn_translate h (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ g), hg, hgh]
    with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4]

open ENNReal (dyadicWeight finLqNorm) in
/-- **Size of Lipschitz atoms**: `‖∑_m c_m a_m‖_2 ≤ ((2D + 1)^d (2D)^d)^(1/2) 2^(-jd/2) ‖c‖_{ℓ_2}`
for atoms of one level. -/
theorem eLpNorm_sum_lipAtoms_le [DecidableEq d] {D j : ℕ}
    {a : (d → Fin (2 ^ j)) → UnitAddTorus d →ᵇ ℂ} (ha : ∀ m, IsLipAtom D j m (a m))
    (c : (d → Fin (2 ^ j)) → ℝ) :
    eLpNorm (⇑(∑ m, c m • a m : UnitAddTorus d →ᵇ ℂ)) 2 volume ≤
      ((((2 * D + 1) ^ Fintype.card d : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (2 * D) ^ Fintype.card d) ^ (1 / 2 : ℝ) *
        (dyadicWeight (-(Fintype.card d / 2 : ℝ)) j * finLqNorm 2 (fun m => ‖c m‖ₑ)) := by
  have h := eLpNorm_le_of_overlap (j := j) D (G := ⇑(∑ m, c m • a m))
    (∑ m, c m • a m).continuous.aestronglyMeasurable (fun m x => c m • a m x)
    (fun x => by simp) c zero_le_one
    (fun m x hx => by simp only [(ha m).eq_zero x hx, smul_zero])
    (fun m x => by
      rw [norm_smul, Real.norm_eq_abs, mul_one]
      exact mul_le_of_le_one_right (abs_nonneg _) ((ha m).norm_le x))
  rwa [ENNReal.ofReal_one, mul_one] at h

open ENNReal (dyadicWeight finLqNorm) in
/-- **Decay of Lipschitz atoms under translation**: for `k ≥ j` and `‖h‖ ≤ 2^(-k)`,
`‖τ_h g - g‖_2 ≤ ((2D + 3)^d (2D + 2)^d)^(1/2) 2^(-(k-j)) 2^(-jd/2) ‖c‖_{ℓ_2}`, where
`g = ∑_m c_m a_m`. -/
theorem enorm_translate_sum_lipAtoms_sub_le [DecidableEq d] {D j k : ℕ} (hjk : j ≤ k)
    {a : (d → Fin (2 ^ j)) → UnitAddTorus d →ᵇ ℂ} (ha : ∀ m, IsLipAtom D j m (a m))
    (c : (d → Fin (2 ^ j)) → ℝ) {h : UnitAddTorus d} (hh : ‖h‖ ≤ 1 / ((2 ^ k : ℕ) : ℝ)) :
    ‖translate h (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (∑ m, c m • a m)) -
        BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (∑ m, c m • a m)‖ₑ ≤
      ((((2 * (D + 1) + 1) ^ Fintype.card d : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (2 * ((D + 1 : ℕ) : ℝ)) ^ Fintype.card d) ^ (1 / 2 : ℝ) *
        dyadicWeight (-1) (k - j) *
          (dyadicWeight (-(Fintype.card d / 2 : ℝ)) j * finLqNorm 2 (fun m => ‖c m‖ₑ)) := by
  rw [enorm_translate_toLp_sub]
  set g := ∑ m, c m • a m
  have h2j : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have h2k : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hjk' : 1 / ((2 ^ k : ℕ) : ℝ) ≤ 1 / ((2 ^ j : ℕ) : ℝ) :=
    one_div_le_one_div_of_le h2j (by exact_mod_cast Nat.pow_le_pow_right two_pos hjk)
  set τ : ℝ := ((2 ^ j : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ)
  have hτ : 0 ≤ τ := by positivity
  have hmeas : AEStronglyMeasurable (fun x => g (x + h) - g x) volume :=
    ((g.continuous.comp (continuous_id.add continuous_const)).sub g.continuous).aestronglyMeasurable
  have hbound := eLpNorm_le_of_overlap (j := j) (D + 1) hmeas
    (fun m x => c m • (a m (x + h) - a m x)) (fun x => by
      simp [g, Finset.sum_sub_distrib, smul_sub]) c hτ
    (fun m x hx => by
      have hx' : (D : ℝ) / ((2 ^ j : ℕ) : ℝ) < ‖x - gridPoint j m‖ := by
        refine lt_of_le_of_lt ?_ hx
        gcongr; linarith
      have hxh : (D : ℝ) / ((2 ^ j : ℕ) : ℝ) < ‖x + h - gridPoint j m‖ := by
        have h1 : ‖x - gridPoint j m‖ ≤ ‖x + h - gridPoint j m‖ + ‖h‖ := by
          calc ‖x - gridPoint j m‖ = ‖(x + h - gridPoint j m) - h‖ := by congr 1; abel
            _ ≤ ‖x + h - gridPoint j m‖ + ‖h‖ := norm_sub_le _ _
        have h2 : ((D + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) =
            (D : ℝ) / ((2 ^ j : ℕ) : ℝ) + 1 / ((2 ^ j : ℕ) : ℝ) := by push_cast; ring
        linarith
      simp only [(ha m).eq_zero x hx', (ha m).eq_zero (x + h) hxh, sub_zero, smul_zero])
    (fun m x => by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      calc ‖a m (x + h) - a m x‖ ≤ 2 ^ j * ‖x + h - x‖ := (ha m).lipschitz _ _
        _ = ((2 ^ j : ℕ) : ℝ) * ‖h‖ := by push_cast; rw [add_sub_cancel_left]
        _ ≤ ((2 ^ j : ℕ) : ℝ) * (1 / ((2 ^ k : ℕ) : ℝ)) := by gcongr
        _ = τ := by rw [mul_one_div])
  refine hbound.trans_eq ?_
  have hτw : ENNReal.ofReal τ = dyadicWeight (-1) (k - j) := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [Nat.add_sub_cancel_left, ENNReal.dyadicWeight_eq_pow]
    have : τ = ((2 : ℝ) ^ e)⁻¹ := by
      simp only [τ]; push_cast; rw [pow_add]; field_simp
    rw [this, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.rpow_neg_one, ENNReal.inv_pow]
  rw [hτw]

/-- The constant of the Lipschitz atomic system. -/
noncomputable def lipConst (d : Type*) [Fintype d] (D : ℕ) : ℝ≥0∞ :=
  ((((2 * D + 1) ^ Fintype.card d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * D) ^ Fintype.card d) ^
      (1 / 2 : ℝ) +
    ((Fintype.card d : ℝ≥0∞) + 1) * ((((2 * (D + 1) + 1) ^ Fintype.card d : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (2 * ((D + 1 : ℕ) : ℝ)) ^ Fintype.card d) ^ (1 / 2 : ℝ)

/-- The constant of the Lipschitz atomic system is finite. -/
theorem lipConst_ne_top (D : ℕ) : lipConst d D ≠ ∞ := by
  unfold lipConst
  refine ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)),
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)))⟩

/-- The trigonometric scheme in `L_p` is linear. -/
theorem trigScheme_toLp_isLinear (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ((trigScheme d).toLp volume p).IsLinear := by
  unfold FunctionScheme.toLp trigScheme
  exact (ApproximationScheme.isLinear_ofSubmodules _ _ _).map _

/-- **Lipschitz atoms form an atomic system** of smoothness `σ = 1` and size exponent
`δ = d/2` for the trigonometric scheme in `L_2(𝕋^d)`: the admissible atoms at `(j, m)` are the
classes of the Lipschitz atoms of level `j` at the grid point `2^(-j) m`. -/
noncomputable def lipAtomicSystem [DecidableEq d] (D : ℕ) :
    ((trigScheme d).toLp volume 2).AtomicSystem (fun j => d → Fin (2 ^ j)) 2
      (Fintype.card d / 2) 1 where
  adm j m := (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ) '' {a | IsLipAtom D j m a}
  zero_mem j m := ⟨0, isLipAtom_zero D j m, map_zero _⟩
  C := lipConst d D
  C_ne_top := lipConst_ne_top D
  size j a ha c := by
    choose A hA hAa using ha
    have hsum : ∑ m, c m • a m =
        BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (∑ m, c m • A m) := by
      simp only [map_sum, map_smul, hAa]
    rw [hsum, Lp.enorm_def, eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 volume ℝ _)]
    refine (eLpNorm_sum_lipAtoms_le hA c).trans ?_
    gcongr
    exact le_self_add
  decay j a ha c k hjk := by
    choose A hA hAa using ha
    have hsum : ∑ m, c m • a m =
        BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (∑ m, c m • A m) := by
      simp only [map_sum, map_smul, hAa]
    rw [hsum]
    refine (approxSeq_le_modulus (Nat.one_le_two_pow (n := k)) _).trans ?_
    have hmod := iSup₂_le (f := fun (h : UnitAddTorus d) (_ : ‖h‖ ≤ 1 / ((2 ^ k : ℕ) : ℝ)) =>
      ‖translate h (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (∑ m, c m • A m)) -
        BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (∑ m, c m • A m)‖ₑ)
      fun h hh => enorm_translate_sum_lipAtoms_sub_le hjk hA c hh
    refine (mul_le_mul' le_rfl hmod).trans ?_
    rw [lipConst]
    set W := ENNReal.dyadicWeight (-1) (k - j)
    set X := ENNReal.dyadicWeight (-(Fintype.card d / 2 : ℝ)) j *
      ENNReal.finLqNorm 2 (fun m => ‖c m‖ₑ)
    calc ((Fintype.card d : ℝ≥0∞) + 1) * (((((2 * (D + 1) + 1) ^ Fintype.card d : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (2 * ((D + 1 : ℕ) : ℝ)) ^ Fintype.card d) ^ (1 / 2 : ℝ) * W * X)
        = W * ((((Fintype.card d : ℝ≥0∞) + 1) *
            ((((2 * (D + 1) + 1) ^ Fintype.card d : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (2 * ((D + 1 : ℕ) : ℝ)) ^ Fintype.card d) ^ (1 / 2 : ℝ)) * X) := by
          ring
      _ ≤ _ := by gcongr; exact le_add_self

open ENNReal (dyadicWeight finLqNorm) in
/-- **Synthesis with Lipschitz atoms on the torus**: every sum
`f = ∑_j ∑_m λ_{j,m} a_{j,m}` of Lipschitz atoms (the series over `j` converging in `L_2`)
satisfies `‖f‖_{B^s_{2,q}(𝕋^d)} ≤ K ‖λ‖_{b^s_{2,q}}` in the dyadic quasi-norm, with `δ = d/2`
and `K = (lipAtomicSystem D).synthConst s`, finite for `0 < s < 1`. -/
theorem approxNormDyadic_le_of_lipAtoms [DecidableEq d] (D : ℕ) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) {A : ∀ j, (d → Fin (2 ^ j)) → UnitAddTorus d →ᵇ ℂ}
    (hA : ∀ j m, IsLipAtom D j m (A j m)) {c : ∀ j, (d → Fin (2 ^ j)) → ℝ}
    {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hf : HasSum (fun j => ∑ m, c j m • BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (A j m))
      f) :
    ((trigScheme d).toLp volume 2).approxNormDyadic s q f ≤
      (lipAtomicSystem (d := d) D).synthConst s *
        ApproximationScheme.bNorm (fun j => d → Fin (2 ^ j)) s (Fintype.card d / 2) 2 q c :=
  (lipAtomicSystem (d := d) D).approxNormDyadic_le_bNorm (trigScheme_toLp_isLinear 2) hq
    (fun j m => ⟨A j m, hA j m, rfl⟩) hf

/-- **Lipschitz-atomic sums are Besov functions**: for `0 < s < 1` and `1 ≤ q ≤ ∞`, every sum
of Lipschitz atoms with coefficients in `b^s_{2,q}` lies in `B^s_{2,q}(𝕋^d)`; this is the
synthesis half of the Lipschitz-atomic characterisation of Schneider–Vybíral on `𝕋^d`,
`p = 2`. -/
theorem memBesov_of_lipAtoms [DecidableEq d] (D : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {A : ∀ j, (d → Fin (2 ^ j)) → UnitAddTorus d →ᵇ ℂ}
    (hA : ∀ j m, IsLipAtom D j m (A j m)) {c : ∀ j, (d → Fin (2 ^ j)) → ℝ}
    {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hf : HasSum (fun j => ∑ m, c j m • BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (A j m))
      f)
    (hc : ApproximationScheme.bNorm (fun j => d → Fin (2 ^ j)) s (Fintype.card d / 2) 2 q c < ∞) :
    (trigScheme d).MemBesov volume 2 s q f :=
  (lipAtomicSystem (d := d) D).memApprox_of_bNorm_lt_top (trigScheme_toLp_isLinear 2) hs hs1 hq
    (fun j m => ⟨A j m, hA j m, rfl⟩) hf hc

end Torus
