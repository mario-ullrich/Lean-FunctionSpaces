/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Atoms.Examples.Torus

/-!
# Hat functions on the torus

The **hat function** of the circle at `l/N` is `max(0, 1 - N ‖u - l/N‖)` (`Torus.circleHat`);
the hat function of `𝕋^d` at the grid point `2^(-j) m` is the product of the hats of the
coordinates (`Torus.torusHat`), and the constant `1` for `j = 0`.  For `N ≥ 2` the hats at the
`N` points `l/N` form a **partition of unity** of the circle (`Torus.sum_circleHat`), and so the
torus hats of every level form one of `𝕋^d` (`Torus.sum_torusHat`).  A torus hat of level `j`
takes values in `[0, 1]`, vanishes outside the ball of radius `2^(-j)` around its grid point and
is Lipschitz with constant `#d 2^j`, so up to the factor `#d` it is a Lipschitz atom.
-/

@[expose] public section

open UnitAddTorus

namespace Torus

/-- The **hat function** of the circle at the point `l/N`: `max(0, 1 - N ‖u - l/N‖)`. -/
noncomputable def circleHat (N l : ℕ) (u : UnitAddCircle) : ℝ :=
  max 0 (1 - N * ‖u - ((((l : ℝ) / N : ℝ)) : UnitAddCircle)‖)

/-- Hat functions are nonnegative. -/
theorem circleHat_nonneg (N l : ℕ) (u : UnitAddCircle) : 0 ≤ circleHat N l u := le_max_left _ _

/-- Hat functions are at most `1`. -/
theorem circleHat_le_one (N l : ℕ) (u : UnitAddCircle) : circleHat N l u ≤ 1 :=
  max_le zero_le_one (sub_le_self _ (by positivity))

/-- The hat at `l/N` vanishes at distance `≥ 1/N` from `l/N`. -/
theorem circleHat_eq_zero {N l : ℕ} {u : UnitAddCircle}
    (h : 1 ≤ N * ‖u - ((((l : ℝ) / N : ℝ)) : UnitAddCircle)‖) : circleHat N l u = 0 :=
  max_eq_left (by linarith)

/-- **Hat functions are Lipschitz** with constant `N`. -/
theorem abs_circleHat_sub_le (N l : ℕ) (u v : UnitAddCircle) :
    |circleHat N l u - circleHat N l v| ≤ N * ‖u - v‖ := by
  unfold circleHat
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [sub_sub_sub_cancel_left, ← mul_sub, abs_mul, Nat.abs_cast]
  gcongr
  calc |‖v - ((((l : ℝ) / N : ℝ)) : UnitAddCircle)‖ - ‖u - ((((l : ℝ) / N : ℝ)) : UnitAddCircle)‖|
      ≤ ‖(v - ((((l : ℝ) / N : ℝ)) : UnitAddCircle)) -
          (u - ((((l : ℝ) / N : ℝ)) : UnitAddCircle))‖ := abs_norm_sub_norm_le _ _
    _ = ‖u - v‖ := by rw [sub_sub_sub_cancel_right, norm_sub_rev]

/-- Hat functions are continuous. -/
theorem continuous_circleHat (N l : ℕ) : Continuous (circleHat N l) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul
    (continuous_id.sub continuous_const).norm))

/-- Shifting the representative by a multiple of `N`: if `l + N z = n`, then
`y - l/N = (N y - n)/N` on the circle. -/
theorem coe_sub_div_eq {N : ℕ} (hN : 0 < N) (y : ℝ) {l : ℕ} {z n : ℤ}
    (h : (l : ℤ) + N * z = n) :
    ((y : ℝ) : UnitAddCircle) - ((((l : ℝ) / N : ℝ)) : UnitAddCircle) =
      ((((N : ℝ) * y - n) / N : ℝ) : UnitAddCircle) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨z, ?_⟩
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have h' : (l : ℝ) + N * z = n := by exact_mod_cast h
  rw [zsmul_eq_mul, mul_one,
    show y - (l : ℝ) / N - ((N : ℝ) * y - n) / N = ((n : ℝ) - l) / N by field_simp; ring, ← h',
    add_sub_cancel_left, mul_div_cancel_left₀ _ hN']

/-- `N ‖y - l/N‖ = |N y - n|` for the integer `n = l + N round(y - l/N)` in the class of `l`
modulo `N`. -/
theorem natCast_mul_norm_coe_sub_div {N : ℕ} (hN : 0 < N) (y : ℝ) (l : ℕ) :
    (N : ℝ) * ‖((y : ℝ) : UnitAddCircle) - ((((l : ℝ) / N : ℝ)) : UnitAddCircle)‖ =
      |N * y - ((l : ℤ) + N * round (y - l / N) : ℤ)| := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← AddCircle.coe_sub, UnitAddCircle.norm_eq, ← abs_of_pos hN', ← abs_mul, abs_of_pos hN']
  congr 1
  push_cast
  field_simp
  ring

/-- If `l ≡ n (mod N)` with `0 ≤ l < N`, then `l = n mod N`. -/
theorem natCast_eq_emod {N l : ℕ} (hl : l < N) {z n : ℤ} (h : (l : ℤ) + N * z = n) :
    (l : ℤ) = n % N := by
  rw [← h, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (Int.natCast_nonneg _)
    (by exact_mod_cast hl)]

/-- **Partition of unity on the circle**: for `N ≥ 2`, `∑_{l < N} hat_{N,l} = 1`.  With
`t = N y` and `k = ⌊t⌋`, only the hats at `k` and `k + 1` (modulo `N`) are nonzero at `y`, with
values `1 - (t - k)` and `t - k`. -/
theorem sum_circleHat {N : ℕ} (hN : 2 ≤ N) (u : UnitAddCircle) :
    ∑ l ∈ Finset.range N, circleHat N l u = 1 := by
  induction u using QuotientAddGroup.induction_on with
  | H y =>
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN0
  set t : ℝ := N * y with ht
  set k : ℤ := ⌊t⌋
  have hk0 : (k : ℝ) ≤ t := Int.floor_le t
  have hk1 : t < k + 1 := Int.lt_floor_add_one t
  have hr0 : (((k % N).toNat : ℕ) : ℤ) = k % N := Int.toNat_of_nonneg (Int.emod_nonneg _ hNz.ne')
  have hr1 : ((((k + 1) % N).toNat : ℕ) : ℤ) = (k + 1) % N :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hNz.ne')
  have hr0N : (k % N).toNat < N := by have := Int.emod_lt_of_pos k hNz; omega
  have hr1N : ((k + 1) % N).toNat < N := by have := Int.emod_lt_of_pos (k + 1) hNz; omega
  have hne : (k % N).toNat ≠ ((k + 1) % N).toNat := by
    intro h
    have h' : (k + 1) % N = k % N := by rw [← hr0, ← hr1, h]
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, add_sub_cancel_left,
      Int.emod_eq_of_lt zero_le_one (by omega)] at h'
    exact one_ne_zero h'
  -- the value of a hat through the shifted representative
  have hval : ∀ l : ℕ, ∀ z n : ℤ, (l : ℤ) + N * z = n → |t - n| ≤ 1 →
      circleHat N l ((y : ℝ) : UnitAddCircle) = 1 - |t - n| := by
    intro l z n h hn
    rw [circleHat, coe_sub_div_eq hN0 y h, (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < N), mul_div_cancel₀ _ (by positivity)]
    · exact max_eq_right (by linarith)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N), abs_one, div_le_iff₀ (by positivity)]
      linarith
  have h0 : circleHat N (k % N).toNat ((y : ℝ) : UnitAddCircle) = 1 - (t - k) := by
    rw [hval _ (k / N) k (by rw [hr0]; exact Int.emod_add_mul_ediv k N)
      (by rw [abs_of_nonneg (by linarith)]; linarith), abs_of_nonneg (by linarith)]
  have h1 : circleHat N ((k + 1) % N).toNat ((y : ℝ) : UnitAddCircle) = t - k := by
    rw [hval _ ((k + 1) / N) (k + 1) (by rw [hr1]; exact Int.emod_add_mul_ediv (k + 1) N)
      (by push_cast; rw [abs_of_nonpos (by linarith)]; linarith)]
    push_cast
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [Finset.sum_eq_add_of_mem _ _ (Finset.mem_range.2 hr0N) (Finset.mem_range.2 hr1N) hne, h0, h1]
  · ring
  · intro l hl hl'
    apply circleHat_eq_zero
    rw [natCast_mul_norm_coe_sub_div hN0]
    set n : ℤ := (l : ℤ) + N * round (y - l / N)
    have hlN : l < N := Finset.mem_range.1 hl
    have hn0 : n ≠ k := fun h => hl'.1 (by
      have := natCast_eq_emod hlN (z := round (y - l / N)) h
      omega)
    have hn1 : n ≠ k + 1 := fun h => hl'.2 (by
      have := natCast_eq_emod hlN (z := round (y - l / N)) h
      omega)
    rcases (by omega : n ≤ k - 1 ∨ k + 2 ≤ n) with h | h
    · have : (n : ℝ) ≤ k - 1 := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (k : ℝ) + 2 ≤ n := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith

/-- `|∏ aᵢ - ∏ bᵢ| ≤ ∑ |aᵢ - bᵢ|` for numbers in `[0, 1]`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hB0 : 0 ≤ ∏ j ∈ s, b j := Finset.prod_nonneg fun j _ => hb0 j
    have hB1 : ∏ j ∈ s, b j ≤ 1 := Finset.prod_le_one₀ (fun j _ => hb0 j) fun j _ => hb1 j
    calc |a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j|
        = |a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j| := by ring_nf
      _ ≤ |a i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| + |a i - b i| * |∏ j ∈ s, b j| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ j ∈ s, |a j - b j| + |a i - b i| * 1 := by
          rw [abs_of_nonneg (ha0 i), abs_of_nonneg hB0]
          gcongr
          · exact ha1 i
      _ = |a i - b i| + ∑ j ∈ s, |a j - b j| := by ring

variable {d : Type*} [Fintype d]

/-- The **hat function of `𝕋^d`** at the grid point `2^(-j) m`: for `j ≥ 1` the product of the
circle hats of the coordinates, and the constant `1` for `j = 0`, where the grid has the single
point `0` and the partition of unity is the constant `1`. -/
noncomputable def torusHat (j : ℕ) (m : d → Fin (2 ^ j)) (x : UnitAddTorus d) : ℝ :=
  if j = 0 then 1 else ∏ i, circleHat (2 ^ j) (m i) (x i)

/-- Torus hats are nonnegative. -/
theorem torusHat_nonneg (j : ℕ) (m : d → Fin (2 ^ j)) (x : UnitAddTorus d) :
    0 ≤ torusHat j m x := by
  unfold torusHat
  split_ifs
  · exact zero_le_one
  · exact Finset.prod_nonneg fun _ _ => circleHat_nonneg _ _ _

/-- Torus hats are at most `1`. -/
theorem torusHat_le_one (j : ℕ) (m : d → Fin (2 ^ j)) (x : UnitAddTorus d) :
    torusHat j m x ≤ 1 := by
  unfold torusHat
  split_ifs
  · exact le_rfl
  · exact Finset.prod_le_one₀ (fun _ _ => circleHat_nonneg _ _ _)
      fun _ _ => circleHat_le_one _ _ _

/-- **Partition of unity on `𝕋^d`**: the torus hats of every level sum to `1`. -/
theorem sum_torusHat [DecidableEq d] (j : ℕ) (x : UnitAddTorus d) :
    ∑ m : d → Fin (2 ^ j), torusHat j m x = 1 := by
  unfold torusHat
  split_ifs with hj
  · subst hj
    simp
  · have h2 : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (Nat.one_le_iff_ne_zero.2 hj)
    rw [← Fintype.prod_sum (fun i (l : Fin (2 ^ j)) => circleHat (2 ^ j) l (x i))]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun l => circleHat (2 ^ j) l (x i)), sum_circleHat h2]

/-- **Torus hats are Lipschitz** with constant `#d 2^j`. -/
theorem abs_torusHat_sub_le (j : ℕ) (m : d → Fin (2 ^ j)) (x y : UnitAddTorus d) :
    |torusHat j m x - torusHat j m y| ≤ Fintype.card d * 2 ^ j * ‖x - y‖ := by
  unfold torusHat
  split_ifs
  · rw [sub_self, abs_zero]
    positivity
  refine (abs_prod_sub_prod_le _ (fun _ => circleHat_nonneg _ _ _)
    (fun _ => circleHat_le_one _ _ _) (fun _ => circleHat_nonneg _ _ _)
    (fun _ => circleHat_le_one _ _ _)).trans ?_
  calc ∑ i, |circleHat (2 ^ j) (m i) (x i) - circleHat (2 ^ j) (m i) (y i)|
      ≤ ∑ _i : d, (2 ^ j : ℝ) * ‖x - y‖ := Finset.sum_le_sum fun i _ =>
        (abs_circleHat_sub_le _ _ _ _).trans (by
          push_cast
          gcongr
          exact norm_le_pi_norm (x - y) i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Points of `𝕋^d` have norm at most `1/2`. -/
theorem norm_le_half (x : UnitAddTorus d) : ‖x‖ ≤ 1 / 2 :=
  (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i =>
    (AddCircle.norm_le_half_period 1 one_ne_zero).trans_eq (by norm_num)

/-- A torus hat of level `j` vanishes outside the open ball of radius `2^(-j)` around its grid
point. -/
theorem torusHat_eq_zero {j : ℕ} {m : d → Fin (2 ^ j)} {x : UnitAddTorus d}
    (hx : ¬ ‖x - gridPoint j m‖ < 1 / ((2 ^ j : ℕ) : ℝ)) : torusHat j m x = 0 := by
  unfold torusHat
  split_ifs with hj
  · subst hj
    exact absurd ((norm_le_half _).trans_lt (by norm_num)) hx
  rw [pi_norm_lt_iff (by positivity)] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  refine Finset.prod_eq_zero (Finset.mem_univ i) (circleHat_eq_zero ?_)
  have h2 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ h2] at hi
  simpa [gridPoint, mul_comm] using hi

/-- Torus hats are continuous. -/
theorem continuous_torusHat (j : ℕ) (m : d → Fin (2 ^ j)) : Continuous (torusHat j m) := by
  unfold torusHat
  split_ifs
  · exact continuous_const
  · exact continuous_finsetProd _ fun i _ => (continuous_circleHat _ _).comp (continuous_apply i)

end Torus
