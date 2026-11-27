/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Differences.DilatedDifferences
public import FunctionSpaces.Wavelets.Examples.Daubechies.SlicewiseProjections
public import FunctionSpaces.Wavelets.Examples.Daubechies.TensorProjections

/-!
# Jackson's inequality for the tensor Daubechies scheme

For a Daubechies mask of order `N ≥ 2`, `1 ≤ p < ∞` and a level `j`, the projections of one
variable applied in one coordinate after the other,

`R_j f = P_j^{(i_1)} ⋯ P_j^{(i_n)} f` for a list `l = [i_1, …, i_n]` of coordinates
(`Daubechies.foldSliceProj`, with `Daubechies.sliceProj`),

give Jackson's inequality for the tensor scaling spaces `V_j` of
`FunctionSpaces.Wavelets.Examples.Daubechies.TensorProjections`.

* **Telescoping.** For continuous `f`,
  `f - P^{(i)} R f = (f - P^{(i)} f) + P^{(i)} (f - R f)`, so with the bound `C` of the projections
  of one variable and the length `|l|` of the list,
  `‖f - R f‖_p ≤ (1 + C)^{|l|} ∑_{i ∈ l} ‖f - P_j^{(i)} f‖_p`
  (`Daubechies.eLpNorm_sub_foldSliceProj_le`). With Jackson's inequality in one coordinate
  (`Daubechies.eLpNorm_sub_sliceProj_le`) and all `d` coordinates,
  `‖f - R_j f‖_p ≤ C_{J,d} ω_N(f, 2^(-j))_p`
  (`Daubechies.eLpNorm_sub_foldSliceProj_le_smoothnessModulus`, `Daubechies.tensorJacksonConst`).
* **The range.** `R_j f` lies in `V_j`. Applying the projection in coordinate `i` to a finite sum
  `∑_k c_k(x) ∏_{i' ∈ S} φ_{j,k_{i'}}(x_{i'})` whose coefficients do not depend on the coordinates
  in `S ∌ i` expands each coefficient in the coordinate `i`
  (`Daubechies.sliceProj_eq_sum_of_eq_sum`), and the positions of the new sum are those of the
  old one with one more coordinate (`Daubechies.sum_foldBox_cons`). By induction on the list,
  `R_j f(x) = ∑_k c_k(x) ∏_{i ∈ l} φ_{j,k_i}(x_i)` with iterated coefficients
  (`Daubechies.foldCoeff`, `Daubechies.foldSliceProj_eq_sum`), which for all coordinates are
  constants: `R_j f = ∑_k c_k Φ_{j,k}` (`Daubechies.foldSliceProj_eq_tensorExpand`). Hence
  `R_j f` lies in `V_j` (`Daubechies.toLp_foldSliceProj_mem_tensorScalingSpace`). No identity
  between `R_j f` and the projection `P_j f` is needed.
* **Jackson's inequality.** `E_{2^j}(f)_p ≤ C_{J,d} ω_N(f, 2^(-j))_p` for every `f ∈ L_p(ℝ^d)`
  (`Daubechies.approxError_tensorScheme_le`): for bounded continuous representatives by the two
  steps above, and in general by density (Mathlib's
  `MeasureTheory.Lp.boundedContinuousFunction_dense`,
  `ApproximationScheme.approxError_le_of_dense`).
  The Lebesgue inequality turns it into `‖f - P_j f‖_p ≤ (1 + C_P) C_{J,d} ω_N(f, 2^(-j))_p`
  (`Daubechies.enorm_sub_tensorProj_le`).
* **Density.** `ω_N(f, 2^(-j))_p → 0` (`Rd.tendsto_lpModulus`), so the errors tend to zero
  (`Daubechies.tendsto_approxError_tensorScheme`), the scaling spaces are dense in `L_p(ℝ^d)`
  (`Daubechies.closure_iUnion_tensorScheme`) and `P_j f → f` (`Daubechies.tendsto_tensorProj`).

The norm on `ℝ^d` is the sup norm.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal ComplexConjugate

namespace Daubechies

variable {N : ℕ} (m : Mask N) {d : ℕ}

/-! ### The projections of one variable in several coordinates -/

/-- **The projections of one variable in the coordinates of a list**:
`R f = P_j^{(i_1)} ⋯ P_j^{(i_n)} f` for the list `l = [i_1, …, i_n]`, the last coordinate first
(`Daubechies.sliceProj`). -/
noncomputable def foldSliceProj (j : ℕ) (l : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    (Fin d → ℝ) → ℂ :=
  l.foldr (fun i g => sliceProj m j i g) f

/-- For the empty list `R f = f`. -/
theorem foldSliceProj_nil (j : ℕ) (f : (Fin d → ℝ) → ℂ) : foldSliceProj m j [] f = f := rfl

/-- For the list `i :: l`, `R f = P_j^{(i)}` applied to `R f` for `l`. -/
theorem foldSliceProj_cons (j : ℕ) (i : Fin d) (l : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    foldSliceProj m j (i :: l) f = sliceProj m j i (foldSliceProj m j l f) := rfl

/-- **`R f` is continuous** for continuous `f` and `N ≥ 2` (`Daubechies.continuous_sliceProj`). -/
theorem continuous_foldSliceProj (hN : 2 ≤ N) (j : ℕ) (l : List (Fin d))
    {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) : Continuous (foldSliceProj m j l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact continuous_sliceProj m hN ih j i

/-- **The bound of `R`**: for `N ≥ 2`, `1 ≤ p < ∞` and continuous `f`,
`‖R f‖_p ≤ C^{|l|} ‖f‖_p` with the bound `C = projConst m p` of one variable and the length `|l|`
of the list `l` (`Daubechies.eLpNorm_sliceProj_le`). -/
theorem eLpNorm_foldSliceProj_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (j : ℕ)
    (l : List (Fin d)) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) :
    eLpNorm (foldSliceProj m j l f) p volume ≤
      ENNReal.ofReal (projConst m p) ^ l.length * eLpNorm f p volume := by
  induction l with
  | nil => simp [foldSliceProj_nil]
  | cons i l ih =>
    rw [foldSliceProj_cons, List.length_cons, pow_succ', mul_assoc]
    exact (eLpNorm_sliceProj_le m hN hp1 hp (continuous_foldSliceProj m hN j l hf).measurable j
      i).trans (by gcongr)

/-- **`R f ∈ L_p`** for continuous `f ∈ L_p`, `N ≥ 2` and `1 ≤ p < ∞`
(`Daubechies.eLpNorm_foldSliceProj_le`). -/
theorem memLp_foldSliceProj (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (j : ℕ)
    (l : List (Fin d)) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (hfp : MemLp f p volume) :
    MemLp (foldSliceProj m j l f) p volume :=
  (eLpNorm_foldSliceProj_le m hN hp1 hp j l hf).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hfp.eLpNorm_lt_top)

/-- **Telescoping over the coordinates of a list**: for `N ≥ 2`, `1 ≤ p < ∞` and continuous `f`,
`‖f - R f‖_p ≤ (1 + C)^{|l|} ∑_{i ∈ l} ‖f - P_j^{(i)} f‖_p` with `C = projConst m p` and the
length `|l|` of the list `l`. The step is `f - P^{(i)} R f = (f - P^{(i)} f) + P^{(i)} (f - R f)`
(`Daubechies.sliceProj_sub`, `Daubechies.eLpNorm_sliceProj_le`); this is the argument of
`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le` on the cube. -/
theorem eLpNorm_sub_foldSliceProj_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (j : ℕ) (l : List (Fin d)) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) :
    eLpNorm (fun x => f x - foldSliceProj m j l f x) p volume ≤
      (1 + ENNReal.ofReal (projConst m p)) ^ l.length *
        (l.map fun i => eLpNorm (fun x => f x - sliceProj m j i f x) p volume).sum := by
  induction l with
  | nil => simp [foldSliceProj_nil]
  | cons i l ih =>
    have hF := continuous_foldSliceProj m hN j l hf
    have heq : (fun x => f x - foldSliceProj m j (i :: l) f x) =
        (fun x => f x - sliceProj m j i f x) +
          sliceProj m j i (fun y => f y - foldSliceProj m j l f y) := by
      funext x
      rw [Pi.add_apply, foldSliceProj_cons, sliceProj_sub m hN hf hF j i x]
      ring
    have h2 : eLpNorm (sliceProj m j i fun y => f y - foldSliceProj m j l f y) p volume ≤
        ENNReal.ofReal (projConst m p) *
          eLpNorm (fun y => f y - foldSliceProj m j l f y) p volume :=
      eLpNorm_sliceProj_le m hN hp1 hp (hf.sub hF).measurable j i
    set C := ENNReal.ofReal (projConst m p)
    set e := eLpNorm (fun x => f x - sliceProj m j i f x) p volume
    set S := (l.map fun i => eLpNorm (fun x => f x - sliceProj m j i f x) p volume).sum
    have h1 : 1 ≤ (1 + C) ^ (l.length + 1) := one_le_pow₀ le_self_add
    rw [heq, List.length_cons, List.map_cons, List.sum_cons]
    calc eLpNorm ((fun x => f x - sliceProj m j i f x) +
          sliceProj m j i (fun y => f y - foldSliceProj m j l f y)) p volume
        ≤ e + C * ((1 + C) ^ l.length * S) :=
          (eLpNorm_add_le hp1).trans (add_le_add le_rfl (h2.trans (mul_le_mul' le_rfl ih)))
      _ = e + (1 + C) ^ l.length * C * S := by ring
      _ ≤ (1 + C) ^ (l.length + 1) * e + (1 + C) ^ l.length * (1 + C) * S := by
          gcongr
          · exact le_mul_of_one_le_left' h1
          · exact le_add_self
      _ = (1 + C) ^ (l.length + 1) * (e + S) := by ring

/-- **The Jackson constant on `ℝ^d`**: `C_{J,d} = (1 + C)^d d C_J` with the bound
`C = projConst m p` of the projections of one variable and the Jackson constant
`C_J = daubechiesJacksonConst m p` of one variable. -/
noncomputable def tensorJacksonConst (p : ℝ≥0∞) (d : ℕ) : ℝ≥0∞ :=
  (1 + ENNReal.ofReal (projConst m p)) ^ d * (d * daubechiesJacksonConst m p)

/-- The constant `tensorJacksonConst m p d` is finite for `N ≥ 2`
(`Daubechies.daubechiesJacksonConst_ne_top`). -/
theorem tensorJacksonConst_ne_top (hN : 2 ≤ N) (p : ℝ≥0∞) (d : ℕ) :
    tensorJacksonConst m p d ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩))
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (daubechiesJacksonConst_ne_top m hN p))

/-- **Jackson's inequality for `R_j` in all coordinates**: for `N ≥ 2`, `1 ≤ p < ∞`, every
continuous `f : ℝ^d → ℂ` and every level `j`, with `R_j f` the projections of one variable in all
`d` coordinates, `‖f - R_j f‖_p ≤ C_{J,d} ω_N(f, 2^(-j))_p` with
`C_{J,d} = tensorJacksonConst m p d` and the isotropic modulus of `ℝ^d`: the telescoping bound
(`Daubechies.eLpNorm_sub_foldSliceProj_le`) and Jackson's inequality in each coordinate
(`Daubechies.eLpNorm_sub_sliceProj_le`). -/
theorem eLpNorm_sub_foldSliceProj_le_smoothnessModulus (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (j : ℕ) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) :
    eLpNorm (fun x => f x - foldSliceProj m j (List.finRange d) f x) p volume ≤
      tensorJacksonConst m p d * Rd.smoothnessModulus volume N p f (1 / 2 ^ j) := by
  refine (eLpNorm_sub_foldSliceProj_le m hN hp1 hp j _ hf).trans ?_
  rw [List.length_finRange, tensorJacksonConst, mul_assoc]
  gcongr
  refine (List.sum_le_length_nsmul _
    (daubechiesJacksonConst m p * Rd.smoothnessModulus volume N p f (1 / 2 ^ j))
    fun x hx => ?_).trans_eq ?_
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact eLpNorm_sub_sliceProj_le m hN hp1 hp hf j i
  · rw [List.length_map, List.length_finRange, nsmul_eq_mul, mul_assoc]

/-! ### The positions in the coordinates of a list -/

/-- **The positions in the coordinates of a list**: the `k ∈ ℤ^d` with
`⌈2^j x_i - b⌉ ≤ k_i ≤ ⌊2^j x_i - a⌋` for the coordinates `i` of the list `l` and `k_i = 0` for
the others. For `a = 0`, `b = 2N - 1` these are the positions of the products
`∏_{i ∈ l} φ_{j,k_i}(x_i)` that can be nonzero at `x`. -/
noncomputable def foldBox (a b : ℝ) (j : ℕ) (l : List (Fin d)) (x : Fin d → ℝ) :
    Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i =>
    if i ∈ l then Finset.Icc ⌈(2 : ℝ) ^ j * x i - b⌉ ⌊(2 : ℝ) ^ j * x i - a⌋ else {0}

/-- `k` lies in the box iff every coordinate lies in its interval, or is `0` off the list. -/
theorem mem_foldBox {a b : ℝ} {j : ℕ} {l : List (Fin d)} {x : Fin d → ℝ} {k : Fin d → ℤ} :
    k ∈ foldBox a b j l x ↔ ∀ i, k i ∈
      if i ∈ l then Finset.Icc ⌈(2 : ℝ) ^ j * x i - b⌉ ⌊(2 : ℝ) ^ j * x i - a⌋ else {0} :=
  Fintype.mem_piFinset

/-- For the empty list the box is `{0}`. -/
theorem foldBox_nil (a b : ℝ) (j : ℕ) (x : Fin d → ℝ) : foldBox a b j [] x = {0} := by
  simp only [foldBox, List.not_mem_nil, ↓reduceIte]
  exact Fintype.piFinset_singleton 0

/-- **The box of all coordinates**: for the list of all coordinates no coordinate is fixed to
`0`, and the box is the box of positions at `x` (`Daubechies.tensorBox`). -/
theorem foldBox_finRange (a b : ℝ) (j : ℕ) (x : Fin d → ℝ) :
    foldBox a b j (List.finRange d) x = tensorBox a b j x := by
  simp only [foldBox, tensorBox, List.mem_finRange, ↓reduceIte]

/-- The box does not depend on the coordinates off the list. -/
theorem foldBox_update {a b : ℝ} {j : ℕ} {l : List (Fin d)} {i : Fin d} (hi : i ∉ l)
    (x : Fin d → ℝ) (t : ℝ) : foldBox a b j l (Function.update x i t) = foldBox a b j l x := by
  unfold foldBox
  congr 1
  funext i'
  split_ifs with h
  · rw [Function.update_of_ne fun h' : i' = i => hi (h' ▸ h)]
  · rfl

/-- **One more coordinate**: for `i ∉ l` the box of `i :: l` consists of the `k` with `n` in place
`i`, for `n` in the interval of coordinate `i` and `k` in the box of `l` (where `k_i = 0`), so
`∑_{k ∈ box(i :: l)} H(k) = ∑_n ∑_{k ∈ box(l)} H(k with n in place i)`. -/
theorem sum_foldBox_cons {a b : ℝ} {j : ℕ} {l : List (Fin d)} {i : Fin d} (hi : i ∉ l)
    (x : Fin d → ℝ) (H : (Fin d → ℤ) → ℂ) :
    ∑ k ∈ foldBox a b j (i :: l) x, H k = ∑ n ∈ Finset.Icc ⌈(2 : ℝ) ^ j * x i - b⌉
      ⌊(2 : ℝ) ^ j * x i - a⌋, ∑ k ∈ foldBox a b j l x, H (Function.update k i n) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun q => Function.update q.2 i q.1)
    (fun k => (k i, Function.update k i 0)) (fun q hq => ?_) (fun k hk => ?_) (fun q hq => ?_)
    (fun k _ => ?_) (fun _ _ => rfl)
  · obtain ⟨hn, hk⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    refine Finset.mem_coe.2 (mem_foldBox.2 fun i' => ?_)
    rcases eq_or_ne i' i with rfl | hne
    · simpa using hn
    · simpa [Function.update_of_ne hne, List.mem_cons, hne] using mem_foldBox.1 hk i'
  · have hk' := mem_foldBox.1 (Finset.mem_coe.1 hk)
    refine Finset.mem_coe.2
      (Finset.mem_product.2 ⟨by simpa using hk' i, mem_foldBox.2 fun i' => ?_⟩)
    rcases eq_or_ne i' i with rfl | hne
    · simp [hi]
    · simpa [Function.update_of_ne hne, List.mem_cons, hne] using hk' i'
  · obtain ⟨-, hk⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    have h0 : q.2 i = 0 := by simpa [hi] using mem_foldBox.1 hk i
    ext1
    · simp
    · simp [h0]
  · simp

/-! ### The iterated coefficients -/

/-- **The iterated coefficients** of `f` in the coordinates of a list `l`, at the positions
`k ∈ ℤ^d`: for the empty list `f` itself, and for `i :: l` the coefficient
`x ↦ ⟨(c_l)_{x,i}, φ_{j,k_i}⟩` of the slices in coordinate `i` of the iterated coefficient `c_l`
for `l`. They do not depend on the coordinates of `l`
(`Daubechies.foldCoeff_eq_of_forall_notMem`). -/
noncomputable def foldCoeff (j : ℕ) :
    List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℤ) → (Fin d → ℝ) → ℂ
  | [], f, _ => f
  | i :: l, f, k => fun x => coeffFun (scalingFun m) j (Cube.slice (foldCoeff j l f k) x i) (k i)

/-- The iterated coefficient for `i :: l` is the coefficient in coordinate `i` of that for `l`. -/
theorem foldCoeff_cons (j : ℕ) (i : Fin d) (l : List (Fin d)) (f : (Fin d → ℝ) → ℂ)
    (k : Fin d → ℤ) (x : Fin d → ℝ) :
    foldCoeff m j (i :: l) f k x =
      coeffFun (scalingFun m) j (Cube.slice (foldCoeff m j l f k) x i) (k i) := rfl

/-- **The iterated coefficients of a continuous function are continuous**, for `N ≥ 2`
(`Daubechies.continuous_coeffFun_slice`). -/
theorem continuous_foldCoeff (hN : 2 ≤ N) (j : ℕ) (l : List (Fin d)) {f : (Fin d → ℝ) → ℂ}
    (hf : Continuous f) (k : Fin d → ℤ) : Continuous (foldCoeff m j l f k) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    exact continuous_coeffFun_slice (continuous_scalingFun m hN)
      (fun _ hx => scalingFun_eq_zero m hN hx) ih i j (k i)

/-- **The iterated coefficients do not depend on the coordinates of the list**: if `x` and `y`
agree off `l`, then `c_l(k)(x) = c_l(k)(y)`. -/
theorem foldCoeff_eq_of_forall_notMem (j : ℕ) (l : List (Fin d)) (f : (Fin d → ℝ) → ℂ)
    (k : Fin d → ℤ) {x y : Fin d → ℝ} (hxy : ∀ i ∉ l, x i = y i) :
    foldCoeff m j l f k x = foldCoeff m j l f k y := by
  induction l generalizing x y with
  | nil => exact congrArg f (funext fun i => hxy i List.not_mem_nil)
  | cons i l ih =>
    rw [foldCoeff_cons, foldCoeff_cons]
    congr 1
    funext t
    refine ih fun i' hi' => ?_
    rcases eq_or_ne i' i with rfl | hne
    · simp
    · rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact hxy i' (by simp [hne, hi'])

/-- **The iterated coefficients read only the positions of the list**: for `i ∉ l`,
`c_l(k with n in place i) = c_l(k)`. -/
theorem foldCoeff_update_index (j : ℕ) {l : List (Fin d)} {i : Fin d} (hi : i ∉ l)
    (f : (Fin d → ℝ) → ℂ) (k : Fin d → ℤ) (n : ℤ) :
    foldCoeff m j l f (Function.update k i n) = foldCoeff m j l f k := by
  induction l with
  | nil => rfl
  | cons i' l ih =>
    obtain ⟨hne, hil⟩ : i ≠ i' ∧ i ∉ l := by simpa [List.mem_cons, not_or] using hi
    funext x
    rw [foldCoeff_cons, foldCoeff_cons, ih hil, Function.update_of_ne (Ne.symm hne)]

/-! ### The range of the projections in all coordinates -/

/-- **One more coordinate for a finite sum**: let `N ≥ 2`, `i ∉ l`, let the `c_k` be continuous,
and let `g(y) = ∑_{k ∈ box_l(y)} c_k(y) ∏_{i' ∈ l} φ_{j,k_{i'}}(y_{i'})` for every `y`, with the
box of `Daubechies.foldBox` for `[0, 2N - 1]`. Then `P_j^{(i)} g(x)` is the double sum over the
positions `n` of coordinate `i` and the `k ∈ box_l(x)` of
`⟨(c_k)_{x,i}, φ_{j,n}⟩ ∏_{i' ∈ l} φ_{j,k_{i'}}(x_{i'}) φ_{j,n}(x_i)`: the slice of `g` in
coordinate `i` is a finite combination of the slices of the `c_k` with fixed weights
(`Daubechies.foldBox_update`), the coefficients are linear (`Daubechies.coeffFun_sum_mul`), and
the expansion of one variable is a finite sum (`Daubechies.daubechiesExpand_eq_sum`). -/
theorem sliceProj_eq_sum_of_eq_sum (hN : 2 ≤ N) (j : ℕ) {i : Fin d} {l : List (Fin d)}
    (hi : i ∉ l) {g : (Fin d → ℝ) → ℂ} {c : (Fin d → ℤ) → (Fin d → ℝ) → ℂ}
    (hc : ∀ k, Continuous (c k))
    (hg : ∀ y, g y = ∑ k ∈ foldBox 0 (2 * N - 1) j l y,
      c k y * ∏ i' ∈ l.toFinset, daubechiesScaled m j (k i') (y i')) (x : Fin d → ℝ) :
    sliceProj m j i g x = ∑ n ∈ Finset.Icc ⌈(2 : ℝ) ^ j * x i - (2 * N - 1)⌉
        ⌊(2 : ℝ) ^ j * x i - 0⌋, ∑ k ∈ foldBox 0 (2 * N - 1) j l x,
      coeffFun (scalingFun m) j (Cube.slice (c k) x i) n *
        (∏ i' ∈ l.toFinset, daubechiesScaled m j (k i') (x i')) * daubechiesScaled m j n (x i) := by
  have hslice : Cube.slice g x i = fun t => ∑ k ∈ foldBox 0 (2 * N - 1) j l x,
      Cube.slice (c k) x i t * ∏ i' ∈ l.toFinset, daubechiesScaled m j (k i') (x i') := by
    funext t
    rw [Cube.slice, hg, foldBox_update hi]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Cube.slice]
    congr 1
    refine Finset.prod_congr rfl fun i' hi' => ?_
    rw [Function.update_of_ne fun h : i' = i => hi (h ▸ List.mem_toFinset.1 hi')]
  rw [sliceProj, hslice, projFun, daubechiesExpand_eq_sum (fun _ hx => scalingFun_eq_zero m hN hx)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeffFun_sum_mul (F := fun k => Cube.slice (c k) x i) _ _ fun k _ =>
    integrable_mul_conj_daubechiesScaled m hN
      (Cube.continuous_slice (hc k) x i).locallyIntegrable j n,
    Finset.sum_mul]

/-- **`R f` as a finite sum**: for `N ≥ 2`, continuous `f`, a list `l` without repetitions and
every `x`, `R f(x) = ∑_{k ∈ box_l(x)} c_l(k)(x) ∏_{i ∈ l} φ_{j,k_i}(x_i)` with the iterated
coefficients (`Daubechies.foldCoeff`) and the box of `Daubechies.foldBox` for `[0, 2N - 1]`. By
induction on `l`: `Daubechies.sliceProj_eq_sum_of_eq_sum` and the positions with one more
coordinate (`Daubechies.sum_foldBox_cons`, `Daubechies.foldCoeff_update_index`). -/
theorem foldSliceProj_eq_sum (hN : 2 ≤ N) (j : ℕ) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f)
    {l : List (Fin d)} (hl : l.Nodup) (x : Fin d → ℝ) :
    foldSliceProj m j l f x = ∑ k ∈ foldBox 0 (2 * N - 1) j l x,
      foldCoeff m j l f k x * ∏ i ∈ l.toFinset, daubechiesScaled m j (k i) (x i) := by
  induction l generalizing x with
  | nil =>
    rw [foldBox_nil, Finset.sum_singleton]
    simp [foldSliceProj_nil, foldCoeff]
  | cons i l ih =>
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    rw [foldSliceProj_cons, sliceProj_eq_sum_of_eq_sum m hN j hi
      (fun k => continuous_foldCoeff m hN j l hf k) (ih hl') x, sum_foldBox_cons hi]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    have hi' : i ∉ l.toFinset := fun h => hi (List.mem_toFinset.1 h)
    have hprod : ∏ i' ∈ l.toFinset, daubechiesScaled m j (Function.update k i n i') (x i') =
        ∏ i' ∈ l.toFinset, daubechiesScaled m j (k i') (x i') :=
      Finset.prod_congr rfl fun i' hi'' => by
        rw [Function.update_of_ne fun h : i' = i => hi' (h ▸ hi'')]
    rw [foldCoeff_cons, foldCoeff_update_index m j hi, Function.update_self, List.toFinset_cons,
      Finset.prod_insert hi', Function.update_self, hprod]
    ring

/-- **`R f` in all coordinates is an expansion in `Φ`**: for `N ≥ 2`, continuous `f` and every
level `j`, the projections of one variable in all `d` coordinates give
`R_j f = ∑_{k ∈ ℤ^d} c_k Φ_{j,k}` with the constants `c_k = c(k)(0)` of the iterated coefficients
(`Daubechies.foldSliceProj_eq_sum`, `Daubechies.foldCoeff_eq_of_forall_notMem`): for the list of
all coordinates the box is the box of positions at `x` (`Daubechies.foldBox_finRange`),
`Φ_{j,k}(x) = ∏_i φ_{j,k_i}(x_i)` (`Daubechies.tensorScaled_tensorGen_empty`), and the terms off
the box vanish. -/
theorem foldSliceProj_eq_tensorExpand (hN : 2 ≤ N) (j : ℕ) {f : (Fin d → ℝ) → ℂ}
    (hf : Continuous f) :
    foldSliceProj m j (List.finRange d) f = tensorExpand (tensorScalingFamily m d) j
      (fun νk => foldCoeff m j (List.finRange d) f νk.2 0) := by
  funext x
  rw [foldSliceProj_eq_sum m hN j hf (List.nodup_finRange d) x, List.toFinset_finRange,
    foldBox_finRange, tensorExpand, ← (Equiv.punitProd (Fin d → ℤ)).symm.tsum_eq]
  refine Eq.trans ?_
    (tsum_eq_sum (s := tensorBox 0 (2 * N - 1) j x) fun k hk => ?_).symm
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Equiv.punitProd_symm_apply, tensorScaled_tensorGen_empty]
    rw [foldCoeff_eq_of_forall_notMem m j _ f k fun i hi => absurd (List.mem_finRange i) hi]
  · simp only [Equiv.punitProd_symm_apply, tensorScaled_tensorGen_empty]
    obtain ⟨i, hki⟩ : ∃ i, k i ∉ Finset.Icc ⌈(2 : ℝ) ^ j * x i - (2 * N - 1)⌉
        ⌊(2 : ℝ) ^ j * x i - 0⌋ := by
      by_contra h
      push Not at h
      exact hk (Fintype.mem_piFinset.2 h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (scaledFun_eq_zero
      (fun _ ht => scalingFun_eq_zero m hN ht) fun hx => hki (mem_Icc_ceil_floor hx)), mul_zero]

/-- **`R f` lies in the scaling space**: for `N ≥ 2`, `1 ≤ p < ∞`, every level `j` and every
continuous `f ∈ L_p(ℝ^d)`, the class of `R_j f` lies in `V_j`, since `R_j f` is an expansion in
the `Φ_{j,k}` (`Daubechies.foldSliceProj_eq_tensorExpand`) and the projection `P_j` reproduces
these (`Daubechies.tensorProjFun_tensorExpand`). -/
theorem toLp_foldSliceProj_mem_tensorScalingSpace {p : ℝ≥0∞} [Fact (1 ≤ p)] (hN : 2 ≤ N)
    (hp : p ≠ ∞) (j : ℕ) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (hfp : MemLp f p volume) :
    (memLp_foldSliceProj m hN Fact.out hp j (List.finRange d) hf hfp).toLp _ ∈
      tensorScalingSpace m p d hN hp j := by
  set a := (memLp_foldSliceProj m hN Fact.out hp j (List.finRange d) hf hfp).toLp _
  refine (mem_tensorScalingSpace m).2 ⟨a, Lp.ext ((tensorProj_apply_ae m hN hp j a).trans ?_)⟩
  rw [tensorProjFun_congr_ae m (MemLp.coeFn_toLp _) j, foldSliceProj_eq_tensorExpand m hN j hf,
    tensorProjFun_tensorExpand m hN j, ← foldSliceProj_eq_tensorExpand m hN j hf]
  exact (MemLp.coeFn_toLp _).symm

/-! ### Jackson's inequality on `L_p` -/

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Jackson's inequality for the tensor Daubechies scheme**: for `N ≥ 2`, `1 ≤ p < ∞`, every
`f ∈ L_p(ℝ^d)` and every level `j`, the error of best approximation from the scaling space `V_j`
(the approximants of complexity `2^j`) satisfies
`E_{2^j}(f)_p ≤ C_{J,d} ω_N(f, 2^(-j))_p` with `C_{J,d} = tensorJacksonConst m p d` and the
isotropic modulus of `ℝ^d`. For `f` with a bounded continuous representative `g`,
`R_j g ∈ V_j` (`Daubechies.toLp_foldSliceProj_mem_tensorScalingSpace`) and
`‖g - R_j g‖_p ≤ C_{J,d} ω_N(g, 2^(-j))_p`
(`Daubechies.eLpNorm_sub_foldSliceProj_le_smoothnessModulus`); these `f` are dense (Mathlib's
`MeasureTheory.Lp.boundedContinuousFunction_dense`), and both sides are controlled by `‖f‖_p`, so
the bound extends to all of `L_p` (`ApproximationScheme.approxError_le_of_dense`). -/
theorem approxError_tensorScheme_le (hN : 2 ≤ N) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) (j : ℕ) :
    (tensorScheme m p d hN hp).approxError f (2 ^ j) ≤
      tensorJacksonConst m p d * Rd.lpModulus p N f j := by
  refine ApproximationScheme.approxError_le_of_dense
    (Lp.boundedContinuousFunction_dense ℂ volume hp) (fun f g => Rd.lpModulus_add_le N f g j)
    (C0 := 2 ^ N) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (fun f => Rd.lpModulus_le N f j)
    (tensorJacksonConst_ne_top m hN p d) (fun g hg => ?_) f
  obtain ⟨g₀, hg₀⟩ := Lp.mem_boundedContinuousFunction_iff.1 hg
  have hae : ⇑g =ᵐ[volume] g₀ := by
    have h := g₀.toContinuousMap.coeFn_toAEEqFun volume
    rw [hg₀] at h
    exact h
  have hgp : MemLp (g₀ : (Fin d → ℝ) → ℂ) p volume := MemLp.ae_eq hae (Lp.memLp g)
  refine ((tensorScheme m p d hN hp).approxError_le_of_mem ((mem_tensorScheme_two_pow m).2
    (toLp_foldSliceProj_mem_tensorScalingSpace m hN hp j g₀.continuous hgp)) g).trans ?_
  rw [Lp.eNorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
    (hae.sub (MemLp.coeFn_toLp _))), Rd.lpModulus, Rd.smoothnessModulus_congr_ae hae]
  exact eLpNorm_sub_foldSliceProj_le_smoothnessModulus m hN Fact.out hp j g₀.continuous

/-- **Jackson's inequality for the tensor projections**: for `N ≥ 2`, `1 ≤ p < ∞`, every
`f ∈ L_p(ℝ^d)` and every level `j`, `‖f - P_j f‖_p ≤ (1 + C_P) C_{J,d} ω_N(f, 2^(-j))_p` with the
bound `C_P = tensorProjConst m p d` of the projections: the Lebesgue inequality
(`ApproximationScheme.ProjectionScheme.enorm_sub_le_approxError` for
`Daubechies.tensorProjectionScheme`) and `Daubechies.approxError_tensorScheme_le`. -/
theorem enorm_sub_tensorProj_le (hN : 2 ≤ N) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) (j : ℕ) :
    ‖f - tensorProj m p d hN hp j f‖ₑ ≤
      (1 + ENNReal.ofReal (tensorProjConst m p d)) * tensorJacksonConst m p d *
        Rd.lpModulus p N f j := by
  have h := (tensorProjectionScheme m p d hN hp).enorm_sub_le_approxError (2 ^ j) f
  rw [tensorProjectionScheme_two_pow] at h
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_right (approxError_tensorScheme_le m hN hp f j) _

/-- **The errors tend to zero**: for `N ≥ 2`, `1 ≤ p < ∞` and every `f ∈ L_p(ℝ^d)`,
`E_{2^j}(f)_p → 0` as `j → ∞`, since `E_{2^j}(f)_p ≤ C_{J,d} ω_N(f, 2^(-j))_p`
(`Daubechies.approxError_tensorScheme_le`) and the modulus tends to zero
(`Rd.tendsto_lpModulus`). -/
theorem tendsto_approxError_tensorScheme (hN : 2 ≤ N) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    Tendsto (fun j => (tensorScheme m p d hN hp).approxError f (2 ^ j)) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (Rd.tendsto_lpModulus hp (by omega : 1 ≤ N) f)
    (Or.inr (tensorJacksonConst_ne_top m hN p d))
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    fun j => approxError_tensorScheme_le m hN hp f j

/-- **The tensor Daubechies scheme is dense** in `L_p(ℝ^d)`, for `N ≥ 2` and `1 ≤ p < ∞`: the
closure of the union of its approximants is all of `L_p`, since the errors of every `f` tend to
zero (`Daubechies.tendsto_approxError_tensorScheme`,
`ApproximationScheme.tendsto_approxError_zero_iff`). -/
theorem closure_iUnion_tensorScheme (hN : 2 ≤ N) (hp : p ≠ ∞) :
    closure (⋃ n, tensorScheme m p d hN hp n) = Set.univ :=
  Set.eq_univ_of_forall fun f => ((tensorScheme m p d hN hp).tendsto_approxError_zero_iff f).1
    ((tensorScheme m p d hN hp).tendsto_approxError_zero_of_pow
      (tendsto_approxError_tensorScheme m hN hp f))

/-- **The tensor projections converge**: `P_j f → f` in `L_p(ℝ^d)` as `j → ∞`, for every
`f ∈ L_p(ℝ^d)`, `N ≥ 2` and `1 ≤ p < ∞`. The projections are uniformly bounded and the scheme is
dense (`Daubechies.closure_iUnion_tensorScheme`), so the projection scheme converges
(`ApproximationScheme.ProjectionScheme.tendsto_of_dense`) along the complexities `2^j`
(`Daubechies.tensorProjectionScheme_two_pow`). -/
theorem tendsto_tensorProj (hN : 2 ≤ N) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    Tendsto (fun j => tensorProj m p d hN hp j f) atTop (𝓝 f) := by
  have h := ((tensorProjectionScheme m p d hN hp).tendsto_of_dense
    (closure_iUnion_tensorScheme m hN hp) f).comp
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  simpa only [Function.comp_def, tensorProjectionScheme_two_pow] using h

end Lp

end Daubechies
