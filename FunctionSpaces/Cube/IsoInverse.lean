/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Cube.IsoModulus
public import FunctionSpaces.Interval.LowerDifferences

/-!
# Isotropic differences of functions with slices in a class

Let `V` be a subspace of functions of one variable (for instance the piecewise polynomials or
the splines of level `j`) whose differences of every order `m ≤ r` satisfy
`‖Δ_t^m u‖_{L_p(J(m,t))} ≤ β(m, t) ‖u‖_{L_p[0,1]}` on the step regions
`J(m,t) = {x ∈ [0, 1] : x + mt ∈ [0, 1]}` (`Interval.stepRegion`). For a function `f` on the cube
all of whose slices lie in `V`,

`‖Δ_h^r f‖_{L_p(Q_{rh})} ≤ (∑_{α : Fin r → Fin d} ∏_i β(m_i(α), h_i)) ‖f‖_{L_p(Q)}`

(`Cube.eLpNorm_higherDiff_le_sum`). The isotropic difference is a sum of `d^r` translated mixed
coordinate differences (`Cube.higherDiff_eq_sum`). A translate stays in the cube on `Q_{rh}`, so its
norm is at most the norm of the mixed difference on a box (`Cube.eLpNorm_shift_mixedDiff_le`),
and the mixed difference is bounded one coordinate at a time by Tonelli's theorem
(`Cube.eLpNorm_cubeDiff_inter_le`, `Cube.eLpNorm_mixedDiff_le`): the box constraint in the other
coordinates does not depend on the coordinate of the step (`Cube.lintegral_inter_eq_slice`), and
the slices of the intermediate functions stay in `V` (`Cube.slice_mixedDiff_mem`).

If `β(m, t) = C (2^j |t|)^{θ_m}` for `|t| ≤ 2^(-j)` and `Θ ≤ ∑_i θ_{m_i}` whenever `∑_i m_i = r`,
this gives `‖Δ_h^r f‖ ≤ d^r C^d (2^j ‖h‖_∞)^Θ ‖f‖` for `‖h‖_∞ ≤ 2^(-j)`
(`Cube.eLpNorm_higherDiff_le_of_exponents`): every word `α` carries the total order `r`, and the
gains in the single coordinates multiply.
-/

@[expose] public section

open MeasureTheory Set
open Rd (higherDiff measurable_higherDiff)
open scoped ENNReal

namespace Cube

open Interval TranslationAlgebra

variable {d : ℕ}

/-! ### One coordinate at a time -/

/-- **Integrating out one coordinate under a constraint that does not depend on it**: if
`R` does not depend on the coordinate `i`, then
`∫_{R ∩ {x_i ∈ S}} G = ∫_R (∫_S G(x with t in place i) dt) dx`. -/
theorem lintegral_inter_eq_slice {G : (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) (i : Fin d)
    {R : Set (Fin d → ℝ)} (hR : MeasurableSet R)
    (hRi : ∀ x t, Function.update x i t ∈ R ↔ x ∈ R) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫⁻ x in R ∩ {x | x i ∈ S}, G x ∂cubeVol d =
      ∫⁻ x in R, (∫⁻ t in S, G (Function.update x i t) ∂unitVol) ∂cubeVol d := by
  have hRS : MeasurableSet (R ∩ {x : Fin d → ℝ | x i ∈ S}) :=
    hR.inter (measurable_pi_apply i hS)
  rw [← lintegral_indicator hRS, lintegral_cubeVol_eq_slice (hG.indicator hRS) i,
    ← lintegral_indicator hR]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ R
  · rw [indicator_of_mem hx, ← lintegral_indicator hS]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht, indicator_of_mem (show Function.update x i t ∈
        R ∩ {x | x i ∈ S} from ⟨(hRi x t).2 hx, by simpa using ht⟩)]
    · rw [indicator_of_notMem ht, indicator_of_notMem fun h => ht (by simpa using h.2)]
  · rw [indicator_of_notMem hx]
    have h0 : ∀ t, (R ∩ {x | x i ∈ S}).indicator G (Function.update x i t) = 0 := fun t =>
      indicator_of_notMem (fun h => hx ((hRi x t).1 h.1)) _
    simp only [h0, lintegral_zero]

/-- **One coordinate step**: let `R` not depend on the coordinate `i`, and let every slice of `F`
in coordinate `i` satisfy `‖Δ_t^m u‖_{L_p(J(m,t))} ≤ β ‖u‖_{L_p[0,1]}`. Then
`‖Δ^m_{t e_i} F‖_{L_p(R ∩ {x_i + mt ∈ [0,1]})} ≤ β ‖F‖_{L_p(R)}`, by Tonelli in coordinate `i`. -/
theorem eLpNorm_cubeDiff_inter_le {F : (Fin d → ℝ) → ℂ} (hF : Measurable F) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (m : ℕ) (t : ℝ) (i : Fin d) {R : Set (Fin d → ℝ)}
    (hR : MeasurableSet R) (hRi : ∀ x s, Function.update x i s ∈ R ↔ x ∈ R) {β : ℝ≥0∞}
    (hβfin : β ≠ ∞)
    (hβ : ∀ x, eLpNorm (higherDiff m t (slice F x i)) p (volume.restrict (stepRegion m t)) ≤
      β * eLpNorm (slice F x i) p unitVol) :
    eLpNorm (cubeDiff m t i F) p
        ((cubeVol d).restrict (R ∩ {x | x i + m * t ∈ Icc (0 : ℝ) 1})) ≤
      β * eLpNorm F p ((cubeVol d).restrict R) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set S : Set ℝ := {s | s + m * t ∈ Icc (0 : ℝ) 1}
  have hS : MeasurableSet S := (measurable_add_const _) measurableSet_Icc
  have hstep : unitVol.restrict S = volume.restrict (stepRegion m t) := by
    rw [unitVol, Measure.restrict_restrict hS]
    congr 1
    ext s
    rw [mem_stepRegion]
    simp only [S, mem_inter_iff, mem_ofPred_eq]
    exact and_comm
  have hRu : R ∩ {x : Fin d → ℝ | x i ∈ (univ : Set ℝ)} = R := by simp
  have hGm : Measurable fun x => ‖cubeDiff m t i F x‖ₑ ^ p.toReal :=
    (measurable_cubeDiff hF m t i).enorm.pow_const _
  have hFm : Measurable fun x => ‖F x‖ₑ ^ p.toReal := hF.enorm.pow_const _
  have hRHS : ∫⁻ x in R, ‖F x‖ₑ ^ p.toReal ∂cubeVol d =
      ∫⁻ x in R, eLpNorm (slice F x i) p unitVol ^ p.toReal ∂cubeVol d := by
    have h := lintegral_inter_eq_slice hFm i hR hRi MeasurableSet.univ
    rw [hRu] at h
    rw [h]
    refine lintegral_congr fun x => ?_
    rw [Measure.restrict_univ, eLpNorm_rpow_eq (measurable_slice hF x i).aestronglyMeasurable
      hp0 hp]
    rfl
  refine (ENNReal.rpow_le_rpow_iff hq).1 ?_
  rw [eLpNorm_rpow_eq (measurable_cubeDiff hF m t i).aestronglyMeasurable hp0 hp,
    ENNReal.mul_rpow_of_nonneg _ _ hq.le, eLpNorm_rpow_eq hF.aestronglyMeasurable hp0 hp,
    show R ∩ {x : Fin d → ℝ | x i + m * t ∈ Icc (0 : ℝ) 1} = R ∩ {x | x i ∈ S} from rfl,
    lintegral_inter_eq_slice hGm i hR hRi hS, hRHS,
    ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le hβfin)]
  refine setLIntegral_mono' hR fun x _ => ?_
  have h1 : ∫⁻ s in S, ‖cubeDiff m t i F (Function.update x i s)‖ₑ ^ p.toReal ∂unitVol =
      eLpNorm (higherDiff m t (slice F x i)) p (volume.restrict (stepRegion m t)) ^ p.toReal := by
    rw [← hstep, eLpNorm_rpow_eq
      (measurable_higherDiff (measurable_slice hF x i) m t).aestronglyMeasurable hp0 hp]
    refine lintegral_congr fun s => ?_
    rw [← slice_cubeDiff]
    rfl
  rw [h1, ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  exact ENNReal.rpow_le_rpow (hβ x) hq.le

/-! ### Mixed differences on boxes -/

/-- The **box region** of a mixed difference along a list: the points `x` with
`x_i + m_i h_i ∈ [0, 1]` for the coordinates `i` of the list. -/
def listRegion (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d)) : Set (Fin d → ℝ) :=
  {x | ∀ i ∈ l, x i + m i * h i ∈ Icc (0 : ℝ) 1}

/-- The box region of the empty list is everything. -/
theorem listRegion_nil (m : Fin d → ℕ) (h : Fin d → ℝ) : listRegion m h [] = univ := by
  ext x
  simp [listRegion]

/-- The box region of `i :: l`. -/
theorem listRegion_cons (m : Fin d → ℕ) (h : Fin d → ℝ) (i : Fin d) (l : List (Fin d)) :
    listRegion m h (i :: l) = listRegion m h l ∩ {x | x i + m i * h i ∈ Icc (0 : ℝ) 1} := by
  ext x
  simp only [listRegion, List.mem_cons, forall_eq_or_imp, mem_inter_iff, mem_ofPred_eq]
  exact and_comm

/-- Box regions are measurable. -/
theorem measurableSet_listRegion (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d)) :
    MeasurableSet (listRegion m h l) := by
  induction l with
  | nil => rw [listRegion_nil]; exact MeasurableSet.univ
  | cons i l ih =>
    rw [listRegion_cons]
    exact ih.inter (((measurable_pi_apply i).add_const _) measurableSet_Icc)

/-- The box region of a list does not depend on the coordinates outside the list. -/
theorem update_mem_listRegion_iff (m : Fin d → ℕ) (h : Fin d → ℝ) {l : List (Fin d)}
    {i : Fin d} (hi : i ∉ l) (x : Fin d → ℝ) (s : ℝ) :
    Function.update x i s ∈ listRegion m h l ↔ x ∈ listRegion m h l := by
  simp only [listRegion, mem_ofPred_eq]
  refine forall₂_congr fun c hc => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hi hc)]

/-- **Mixed differences on boxes**: if every slice of `f` in every coordinate lies in `V`, and
the differences of order `m_i` and step `h_i` of the functions in `V` are bounded by `β_i` on the
step regions, then the mixed difference along a list of distinct coordinates satisfies
`‖M f‖_{L_p(box)} ≤ (∏_{i ∈ l} β_i) ‖f‖_{L_p(Q)}`. -/
theorem eLpNorm_mixedDiff_le (V : Submodule ℂ (ℝ → ℂ)) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (m : Fin d → ℕ) (h : Fin d → ℝ) (β : Fin d → ℝ≥0∞) (hβfin : ∀ i, β i ≠ ∞)
    (hβ : ∀ u ∈ V, ∀ i, eLpNorm (higherDiff (m i) (h i) u) p
      (volume.restrict (stepRegion (m i) (h i))) ≤ β i * eLpNorm u p unitVol)
    {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (hfV : ∀ i x, slice f x i ∈ V) :
    ∀ l : List (Fin d), l.Nodup →
      eLpNorm (mixedDiff m h l f) p ((cubeVol d).restrict (listRegion m h l)) ≤
        (l.map β).prod * eLpNorm f p (cubeVol d)
  | [], _ => by
    rw [mixedDiff_nil, listRegion_nil, Measure.restrict_univ, List.map_nil, List.prod_nil,
      one_mul]
  | i :: l, hl => by
    obtain ⟨hil, hl'⟩ := List.nodup_cons.1 hl
    rw [mixedDiff_cons, listRegion_cons, List.map_cons, List.prod_cons, mul_assoc]
    refine (eLpNorm_cubeDiff_inter_le (measurable_mixedDiff m h l hf) hp0 hp (m i) (h i) i
      (measurableSet_listRegion m h l) (update_mem_listRegion_iff m h hil) (hβfin i)
      fun x => hβ _ (slice_mixedDiff_mem V m h hil (hfV i) x) i).trans ?_
    exact mul_le_mul' le_rfl (eLpNorm_mixedDiff_le V hp0 hp m h β hβfin hβ hf hfV l hl')

/-- **The translated terms**: on the isotropic region the translate of the mixed difference of
a word `α` by its shift `s_α` stays in the cube, and lands in the box of the mixed difference, so
`‖M f(· + s_α)‖_{L_p(Q_{rh})} ≤ ‖M f‖_{L_p(box)}`. -/
theorem eLpNorm_shift_mixedDiff_le {r : ℕ} (h : Fin d → ℝ) (α : Fin r → Fin d)
    {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (fun x => mixedDiff (count α) h (List.finRange d) f (x + shiftVec h α)) p
        ((cubeVol d).restrict (isoRegion r h)) ≤
      eLpNorm (mixedDiff (count α) h (List.finRange d) f) p
        ((cubeVol d).restrict (listRegion (count α) h (List.finRange d))) := by
  refine eLpNorm_comp_add_le (measurable_mixedDiff _ h _ hf) p (measurableSet_isoRegion r h)
    (measurableSet_listRegion _ h _) _ fun x hx => ?_
  have hle := card_lt_add_count_le α
  have hcoord : ∀ c, x c + ((Finset.univ.filter fun l => c < α l).card : ℝ) * h c ∈
      Icc (0 : ℝ) 1 := fun c =>
    add_mul_mem_Icc (hx.2 c (mem_univ c)) (hx.1 c) (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.le_add_right _ _).trans (hle c))
  refine ⟨fun c _ => ?_, fun c _ => ?_⟩
  · simp only [Pi.add_apply, shiftVec_apply]
    rw [add_assoc, ← add_mul]
    exact add_mul_mem_Icc (hx.2 c (mem_univ c)) (hx.1 c) (by positivity)
      (by exact_mod_cast hle c)
  · simp only [Pi.add_apply, shiftVec_apply]
    exact hcoord c

/-! ### The isotropic difference -/

/-- The multiplicities of a word are at most its length. -/
theorem count_le {r : ℕ} (α : Fin r → Fin d) (i : Fin d) : count α i ≤ r := by
  rw [count]
  exact (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])

/-- **Isotropic differences of functions with slices in a class**: if the differences of order
`m ≤ r` of the functions in `V` with the steps `h_i` are bounded by `β(m, h_i)` on the step regions,
and every slice of `f` lies in `V`, then
`‖Δ_h^r f‖_{L_p(Q_{rh})} ≤ (∑_α ∏_i β(m_i(α), h_i)) ‖f‖_{L_p(Q)}`, summed over the words
`α : Fin r → Fin d`. -/
theorem eLpNorm_higherDiff_le_sum (V : Submodule ℂ (ℝ → ℂ)) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (r : ℕ) (h : Fin d → ℝ) (β : ℕ → ℝ → ℝ≥0∞) (hβfin : ∀ m t, β m t ≠ ∞)
    (hβ : ∀ u ∈ V, ∀ m ≤ r, ∀ i : Fin d, eLpNorm (higherDiff m (h i) u) p
      (volume.restrict (stepRegion m (h i))) ≤ β m (h i) * eLpNorm u p unitVol)
    {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (hfV : ∀ i x, slice f x i ∈ V) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) ≤
      (∑ α : Fin r → Fin d, ∏ i, β (count α i) (h i)) * eLpNorm f p (cubeVol d) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hsum : higherDiff r h f = ∑ α : Fin r → Fin d,
      fun x => mixedDiff (count α) h (List.finRange d) f (x + shiftVec h α) := by
    funext x
    rw [higherDiff_eq_sum, Finset.sum_apply]
  rw [hsum, Finset.sum_mul]
  refine (eLpNorm_sum_le hp1).trans (Finset.sum_le_sum fun α _ => ?_)
  refine (eLpNorm_shift_mixedDiff_le h α hf p).trans ?_
  have hmix := eLpNorm_mixedDiff_le V hp0 hp (count α) h (fun i => β (count α i) (h i))
    (fun i => hβfin _ _) (fun u hu i => hβ u hu _ (count_le α i) i) hf hfV
    (List.finRange d) (List.nodup_finRange d)
  rwa [← Fin.prod_univ_def] at hmix

/-- `∏_i A^{θ_i} = A^{∑_i θ_i}` for exponents `θ_i ≥ 0`. -/
theorem prod_rpow_eq_rpow_sum {ι : Type*} (s : Finset ι) (A : ℝ≥0∞) {θ : ι → ℝ}
    (hθ : ∀ i ∈ s, 0 ≤ θ i) : ∏ i ∈ s, A ^ θ i = A ^ ∑ i ∈ s, θ i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih fun i hi => hθ i
      (Finset.mem_insert_of_mem hi), ENNReal.rpow_add_of_nonneg _ _ (hθ a
        (Finset.mem_insert_self a s)) (Finset.sum_nonneg fun i hi => hθ i
          (Finset.mem_insert_of_mem hi))]

/-- **Isotropic differences with gains in the coordinates**: let the differences of order
`m ≤ r` of the functions in `V` satisfy `‖Δ_t^m u‖_{L_p(J(m,t))} ≤ C (2^j |t|)^{θ_m} ‖u‖_p` for
`|t| ≤ 2^(-j)`, with `θ_m ≥ 0`, and let `Θ ≤ ∑_i θ_{m_i}` whenever `∑_i m_i = r`. Then for every
`f` with slices in `V` and `‖h‖_∞ ≤ 2^(-j)`,
`‖Δ_h^r f‖_{L_p(Q_{rh})} ≤ d^r C^d (2^j ‖h‖_∞)^Θ ‖f‖_{L_p(Q)}`. -/
theorem eLpNorm_higherDiff_le_of_exponents (V : Submodule ℂ (ℝ → ℂ)) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (r j : ℕ) {C : ℝ≥0∞} (hC : C ≠ ∞) (θ : ℕ → ℝ) (hθ : ∀ m, 0 ≤ θ m) {Θ : ℝ}
    (hΘ : ∀ m : Fin d → ℕ, ∑ i, m i = r → Θ ≤ ∑ i, θ (m i))
    (hV : ∀ u ∈ V, ∀ m ≤ r, ∀ t : ℝ, |t| ≤ 1 / 2 ^ j →
      eLpNorm (higherDiff m t u) p (volume.restrict (stepRegion m t)) ≤
        C * ENNReal.ofReal (2 ^ j * |t|) ^ θ m * eLpNorm u p unitVol)
    {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (hfV : ∀ i x, slice f x i ∈ V)
    {h : Fin d → ℝ} (hh : ‖h‖ ≤ 1 / 2 ^ j) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) ≤
      (d : ℝ≥0∞) ^ r * C ^ d * ENNReal.ofReal (2 ^ j * ‖h‖) ^ Θ * eLpNorm f p (cubeVol d) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hhi : ∀ i, |h i| ≤ ‖h‖ := fun i => by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm h i
  set A := ENNReal.ofReal (2 ^ j * ‖h‖)
  have hA1 : A ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hpos] at hh
    linarith
  set β : ℕ → ℝ → ℝ≥0∞ := fun m t => C * ENNReal.ofReal (2 ^ j * |t|) ^ θ m
  have hβfin : ∀ m t, β m t ≠ ∞ := fun m t =>
    ENNReal.mul_ne_top hC (ENNReal.rpow_ne_top_of_nonneg (hθ m) ENNReal.ofReal_ne_top)
  refine (eLpNorm_higherDiff_le_sum V hp1 hp r h β hβfin
    (fun u hu m hm i => hV u hu m hm (h i) ((hhi i).trans hh)) hf hfV).trans ?_
  -- each word contributes at most `C^d A^Θ`
  have hword : ∀ α : Fin r → Fin d, ∏ i, β (count α i) (h i) ≤ C ^ d * A ^ Θ := fun α => by
    simp only [β]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul' le_rfl ?_
    calc ∏ i, ENNReal.ofReal (2 ^ j * |h i|) ^ θ (count α i)
        ≤ ∏ i, A ^ θ (count α i) := Finset.prod_le_prod fun i _ =>
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by
            have := hhi i; nlinarith)) (hθ _)
      _ = A ^ ∑ i, θ (count α i) := prod_rpow_eq_rpow_sum _ A fun i _ => hθ _
      _ ≤ A ^ Θ := ENNReal.rpow_le_rpow_of_exponent_ge hA1 (hΘ _ (sum_count α))
  calc (∑ α : Fin r → Fin d, ∏ i, β (count α i) (h i)) * eLpNorm f p (cubeVol d)
      ≤ (∑ _α : Fin r → Fin d, C ^ d * A ^ Θ) * eLpNorm f p (cubeVol d) :=
        mul_le_mul' (Finset.sum_le_sum fun α _ => hword α) le_rfl
    _ = (d : ℝ≥0∞) ^ r * C ^ d * A ^ Θ * eLpNorm f p (cubeVol d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Cube
