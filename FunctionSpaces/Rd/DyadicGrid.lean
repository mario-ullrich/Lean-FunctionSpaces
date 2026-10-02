/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Convolution
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The dyadic grid of a finite-dimensional inner product space

In the coordinates `x_i = ⟪b_i, x⟫` of the orthonormal basis `b = stdOrthonormalBasis ℝ V`
(`Rd.gridBasis`), the **dyadic cells** of level `j ∈ ℕ` are
`P_{j,m} = {x : ⌊2^j x_i⌋ = m_i for all i}`, `m ∈ ℤ^n` (`Rd.cell`, `Rd.cellIndex`); they partition
`V`. The centre `c_{j,m}` has the coordinates `(m_i + 1/2) 2^(-j)` (`Rd.cellCenter`), and
`‖x - c_{j,m}‖ ≤ n 2^(-j)` on `P_{j,m}` (`Rd.norm_sub_cellCenter_le`). **Counting**: at most
`(2ρ + 2)^n` centres of level `j` lie in a ball of radius `ρ 2^(-j)`
(`Rd.card_le_of_norm_cellCenter_sub_le`), since each coordinate of such a centre lies in an
interval of length `2ρ 2^(-j)`.
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal

namespace Rd

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The orthonormal basis of the dyadic grid. -/
noncomputable abbrev gridBasis : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V :=
  stdOrthonormalBasis ℝ V

variable {V}

/-- The index `(⌊2^j x_i⌋)_i` of the dyadic cell of level `j` containing `x`. -/
noncomputable def cellIndex (j : ℕ) (x : V) : Fin (finrank ℝ V) → ℤ :=
  fun i => ⌊(2 : ℝ) ^ j * (gridBasis V).repr x i⌋

/-- The **dyadic cell** `P_{j,m}` of level `j` and index `m`. -/
def cell (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) : Set V := {x | cellIndex j x = m}

/-- The **centre** of the dyadic cell `P_{j,m}`, with the coordinates `(m_i + 1/2) 2^(-j)`. -/
noncomputable def cellCenter (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) : V :=
  (gridBasis V).repr.symm (WithLp.toLp 2 fun i => ((m i : ℝ) + 1 / 2) / 2 ^ j)

/-- Every point lies in the cell of its index. -/
theorem mem_cell_cellIndex (j : ℕ) (x : V) : x ∈ cell j (cellIndex j x) := rfl

/-- The coordinates of a centre. -/
theorem repr_cellCenter (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) (i : Fin (finrank ℝ V)) :
    (gridBasis V).repr (cellCenter j m) i = ((m i : ℝ) + 1 / 2) / 2 ^ j := by
  simp [cellCenter]

/-- A coordinate is at most the norm. -/
theorem abs_repr_le_norm (y : V) (i : Fin (finrank ℝ V)) : |(gridBasis V).repr y i| ≤ ‖y‖ := by
  rw [OrthonormalBasis.repr_apply_apply]
  calc |inner ℝ ((gridBasis V) i) y| ≤ ‖(gridBasis V) i‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ = ‖y‖ := by rw [(gridBasis V).orthonormal.1 i, one_mul]

/-- On a cell, every coordinate differs from that of the centre by at most `2^(-j)/2`. -/
theorem abs_repr_sub_cellCenter_le {j : ℕ} {m : Fin (finrank ℝ V) → ℤ} {x : V}
    (hx : x ∈ cell j m) (i : Fin (finrank ℝ V)) :
    |(gridBasis V).repr (x - cellCenter j m) i| ≤ 1 / 2 / 2 ^ j := by
  have hm : ⌊(2 : ℝ) ^ j * (gridBasis V).repr x i⌋ = m i := congrFun hx i
  have h1 := Int.floor_le ((2 : ℝ) ^ j * (gridBasis V).repr x i)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ j * (gridBasis V).repr x i)
  rw [hm] at h1 h2
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  rw [map_sub, PiLp.sub_apply, repr_cellCenter]
  set t := (gridBasis V).repr x i
  have key : t - ((m i : ℝ) + 1 / 2) / 2 ^ j = (2 ^ j * t - m i - 1 / 2) / 2 ^ j := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos, abs_le]
  constructor <;> linarith

/-- **Cells are small**: `‖x - c_{j,m}‖ ≤ n 2^(-j)` on `P_{j,m}`. -/
theorem norm_sub_cellCenter_le {j : ℕ} {m : Fin (finrank ℝ V) → ℤ} {x : V} (hx : x ∈ cell j m) :
    ‖x - cellCenter j m‖ ≤ finrank ℝ V / 2 ^ j := by
  set y := x - cellCenter j m
  have hy : y = ∑ i, (gridBasis V).repr y i • (gridBasis V) i := ((gridBasis V).sum_repr y).symm
  calc ‖y‖ = ‖∑ i, (gridBasis V).repr y i • (gridBasis V) i‖ := by rw [← hy]
    _ ≤ ∑ i, ‖(gridBasis V).repr y i • (gridBasis V) i‖ := norm_sum_le _ _
    _ = ∑ i, |(gridBasis V).repr y i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, (gridBasis V).orthonormal.1 i, mul_one, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin (finrank ℝ V), 1 / 2 ^ j :=
        Finset.sum_le_sum fun i _ => (abs_repr_sub_cellCenter_le hx i).trans
          (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    _ = finrank ℝ V / 2 ^ j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

/-- The cell index is measurable. -/
theorem measurable_cellIndex [MeasurableSpace V] [BorelSpace V] (j : ℕ) :
    Measurable (cellIndex (V := V) j) := by
  refine Measurable.of_eval fun i => ?_
  simp only [cellIndex, OrthonormalBasis.repr_apply_apply]
  exact Int.measurable_floor.comp
    (measurable_const.mul (continuous_const.inner continuous_id).measurable)

/-- Cells are measurable. -/
theorem measurableSet_cell [MeasurableSpace V] [BorelSpace V] (j : ℕ)
    (m : Fin (finrank ℝ V) → ℤ) : MeasurableSet (cell (V := V) j m) :=
  measurable_cellIndex j (measurableSet_singleton m)

/-- **Counting centres**: at most `(2ρ + 2)^n` centres of level `j` lie in the ball of radius
`ρ 2^(-j)` around `x`. -/
theorem card_le_of_norm_cellCenter_sub_le (j : ℕ) (x : V) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (S : Finset (Fin (finrank ℝ V) → ℤ)) (hS : ∀ m ∈ S, ‖cellCenter j m - x‖ ≤ ρ / 2 ^ j) :
    (S.card : ℝ) ≤ (2 * ρ + 2) ^ finrank ℝ V := by
  set a : Fin (finrank ℝ V) → ℝ := fun i => (2 : ℝ) ^ j * (gridBasis V).repr x i
  set T := Fintype.piFinset fun i => Finset.Icc ⌈a i - ρ - 1 / 2⌉ ⌊a i + ρ - 1 / 2⌋
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hST : S ⊆ T := fun m hm => by
    rw [Fintype.mem_piFinset]
    intro i
    have h := (abs_repr_le_norm (cellCenter j m - x) i).trans (hS m hm)
    rw [map_sub, PiLp.sub_apply, repr_cellCenter] at h
    have key : ((m i : ℝ) + 1 / 2) / 2 ^ j - (gridBasis V).repr x i =
        ((m i : ℝ) + 1 / 2 - a i) / 2 ^ j := by
      simp only [a]
      field_simp
    rw [key, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos, abs_le] at h
    have h1 := h.1
    have h2 := h.2
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩
  calc (S.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hST
    _ = ∏ i, ((Finset.Icc ⌈a i - ρ - 1 / 2⌉ ⌊a i + ρ - 1 / 2⌋).card : ℝ) := by
        rw [Fintype.card_piFinset]
        push_cast
        rfl
    _ ≤ ∏ _i : Fin (finrank ℝ V), (2 * ρ + 2) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        rw [Int.card_Icc]
        have hc := Int.le_ceil (a i - ρ - 1 / 2)
        have hf := Int.floor_le (a i + ρ - 1 / 2)
        rcases le_or_gt 0 (⌊a i + ρ - 1 / 2⌋ + 1 - ⌈a i - ρ - 1 / 2⌉) with h | h
        · have hcast : (((⌊a i + ρ - 1 / 2⌋ + 1 - ⌈a i - ρ - 1 / 2⌉).toNat : ℕ) : ℝ) =
              ((⌊a i + ρ - 1 / 2⌋ + 1 - ⌈a i - ρ - 1 / 2⌉ : ℤ) : ℝ) := by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
          rw [hcast]
          push_cast
          linarith
        · rw [Int.toNat_of_nonpos h.le]
          push_cast
          linarith
    _ = (2 * ρ + 2) ^ finrank ℝ V := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Rd
