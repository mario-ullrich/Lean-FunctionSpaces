/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.MollifiedGraph
public import FunctionSpaces.Rd.BoundedLipschitz

/-!
# Extension from the boundary of a Lipschitz graph domain

Every `g ∈ B^s_{p,q}(H)`, `0 < s < 1`, `1 ≤ p < ∞`, is a trace (Schneider–Vybíral, Theorems 4.10
and 4.11, for `p ≥ 1`). The atoms `a` of `g` on the hyperplane `H` (the cell atoms of the terms
`g_j = η_j ⋆ (k_j ⋆ g)` of the reproducing formula on `H`) are extended by

`A(x) = a(Px) v_j(x)`  (`Rd.LipschitzGraph.extendAtom`)

with the vertical cut-off `v_j` of the mollified graph (`Rd.LipschitzGraph.vertCutoff`): `A ∘ γ = a`,
and by Leibniz's rule for differences `|Δ_h^2 A| ≤ 4 A_0 B min(1, (2^j ‖h‖)^2)`
(`Rd.LipschitzGraph.enorm_higherDiff_two_extendAtom_le`), so the extended atoms are regular atoms of
order and exponent `2` on `V` (`Rd.LipschitzGraph.isRegularAtom_extendAtom`). The levels of the
extension are `F_j(x) = g_j(Px) v_j(x)` (`Rd.LipschitzGraph.extLevel`), and
`E g = ∑_j F_j` (`Rd.LipschitzGraph.graphExtension`) has a finite `B^{s+1/p}_{p,q}`-norm on `V`
(`Rd.LipschitzGraph.modNorm_graphExtension_le`), since the coefficient quasi-norm with smoothness
`s + 1/p` on `V` is the one with smoothness `s` on `H`: `(s + 1/p) - n/p = s - (n-1)/p`.

**The trace of the extension is `g`** (`Rd.LipschitzGraph.trace_graphExtension`): the partial sums
`∑_{j ≤ J} F_j` are continuous with traces `∑_{j ≤ J} g_j → g`
(`Rd.LipschitzGraph.trace_sum_traceExtTerm`), and they converge to `E g` in `B^{1/p}_{p,1}`,
where the trace is linear and continuous (`Rd.LipschitzGraph.trace_sub`,
`Rd.LipschitzGraph.enorm_trace_le`). Together with the boundedness of the trace this describes the
trace space (`Rd.LipschitzGraph.exists_trace_eq_iff`; Schneider–Vybíral, Theorem 4.11 for graph
domains and `p ≥ 1`): `g` is the trace of a function with finite intrinsic
`B^{s+1/p}_{p,q}`-norm on `Ω` iff `g ∈ B^s_{p,q}(H)`.

Schneider–Vybíral extend Lip atoms by Whitney's extension and interpolate through `p < 1`
(their Lemma 4.9); for `p ≥ 1` the mollified graph replaces this.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-- `min(1, s^a) min(1, s^b) ≤ min(1, s^(a+b))` for `a, b ≥ 0`. -/
theorem min_one_rpow_mul_le (s : ℝ≥0∞) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (s ^ a) * min 1 (s ^ b) ≤ min 1 (s ^ (a + b)) := by
  rcases le_total s 1 with hs | hs
  · have hsa : s ^ a ≤ 1 := ENNReal.rpow_le_one hs ha
    have hsb : s ^ b ≤ 1 := ENNReal.rpow_le_one hs hb
    have hsab : s ^ (a + b) ≤ 1 := ENNReal.rpow_le_one hs (add_nonneg ha hb)
    rw [min_eq_right hsa, min_eq_right hsb, min_eq_right hsab,
      ENNReal.rpow_add_of_nonneg a b ha hb]
  · have hsab : 1 ≤ s ^ (a + b) :=
      (ENNReal.one_rpow _).symm.le.trans (ENNReal.rpow_le_rpow hs (add_nonneg ha hb))
    rw [min_eq_left hsab]
    exact (mul_le_mul' (min_le_left _ _) (min_le_left _ _)).trans_eq (one_mul 1)

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V)

/-! ### Extended atoms -/

/-- The **extension of a function on `H`** at level `j`: `A(x) = a(Px) v_j(x)`. -/
noncomputable def extendAtom (j : ℕ) (a : Ω.hyperplane → ℂ) (x : V) : ℂ :=
  a (Ω.proj x) * Ω.vertCutoff j x

/-- `A(γ x') = a(x')`. -/
theorem extendAtom_graphMap (j : ℕ) (a : Ω.hyperplane → ℂ) (x' : Ω.hyperplane) :
    Ω.extendAtom j a (Ω.graphMap x') = a x' := by
  rw [extendAtom, Ω.proj_graphMap, Ω.vertCutoff_graphMap, mul_one]

/-- The extension of a continuous function is continuous. -/
theorem continuous_extendAtom (j : ℕ) {a : Ω.hyperplane → ℂ} (hac : Continuous a) :
    Continuous (Ω.extendAtom j a) :=
  (hac.comp Ω.proj.continuous).mul (Ω.continuous_vertCutoff j)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `Δ_h^l (a ∘ P)(x) = Δ_{Ph}^l a(Px)`. -/
theorem higherDiff_comp_proj (l : ℕ) (h : V) (a : Ω.hyperplane → ℂ) (x : V) :
    (fwdDiff h)^[l] (fun y => a (Ω.proj y)) x = (fwdDiff (Ω.proj h))^[l] a (Ω.proj x) := by
  rw [higherDiff_apply, higherDiff_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_smul]

/-- `||A| ≤ A_0` for `|a| ≤ A_0`. -/
theorem enorm_extendAtom_le (j : ℕ) {a : Ω.hyperplane → ℂ} {A : ℝ≥0∞}
    (ha : ∀ y, ‖a y‖ₑ ≤ A) (x : V) : ‖Ω.extendAtom j a x‖ₑ ≤ A := by
  rw [extendAtom, enorm_mul]
  refine (mul_le_mul' (ha _) ?_).trans_eq (mul_one A)
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Ω.norm_vertCutoff_le j x)

/-- **Second differences of extended atoms**: if `|Δ_h^l a| ≤ A_0 min(1, (2^j ‖h‖)^l)` for
`l ≤ 2`, then `|Δ_h^2 A| ≤ 4 A_0 B min(1, (2^j ‖h‖)^2)`, by Leibniz's rule for differences
(`Rd.higherDiff_mul`) and the bounds of the vertical cut-off. -/
theorem enorm_higherDiff_two_extendAtom_le (j : ℕ) {a : Ω.hyperplane → ℂ} {A : ℝ≥0∞}
    (ha : ∀ l ≤ 2, ∀ h y, ‖(fwdDiff h)^[l] a y‖ₑ ≤
      A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (l : ℝ))) (h x : V) :
    ‖(fwdDiff h)^[2] (Ω.extendAtom j a) x‖ₑ ≤
      4 * A * ENNReal.ofReal Ω.vertCutoffConst *
        min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (2 : ℝ)) := by
  set t := ENNReal.ofReal (2 ^ j * ‖h‖)
  set B := ENNReal.ofReal Ω.vertCutoffConst
  have hu : ∀ l ≤ 2, ‖(fwdDiff h)^[l] (fun y => a (Ω.proj y)) x‖ₑ ≤
      A * min 1 (t ^ (l : ℝ)) := fun l hl => by
    rw [Ω.higherDiff_comp_proj]
    refine (ha l hl _ _).trans (mul_le_mul' le_rfl (min_le_min le_rfl
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (Nat.cast_nonneg l))))
    exact mul_le_mul_of_nonneg_left (Ω.norm_proj_le h) (by positivity)
  have hv : ∀ m ≤ 2, ∀ y, ‖(fwdDiff h)^[m] (Ω.vertCutoff j) y‖ₑ ≤ B * min 1 (t ^ (m : ℝ)) :=
    fun m hm y => Ω.enorm_higherDiff_vertCutoff_le j hm h y
  have hterm : ∀ l ∈ Finset.range (2 + 1), ‖(Nat.choose 2 l : ℂ) *
      ((fwdDiff h)^[l] (fun y => a (Ω.proj y)) x *
        (fwdDiff h)^[2 - l] (Ω.vertCutoff j) (x + (l : ℝ) • h))‖ₑ ≤
      (Nat.choose 2 l : ℝ≥0∞) * (A * B * min 1 (t ^ (2 : ℝ))) := fun l hl => by
    have hl2 : l ≤ 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    rw [enorm_mul, enorm_mul, ← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
    refine mul_le_mul' le_rfl ?_
    calc ‖(fwdDiff h)^[l] (fun y => a (Ω.proj y)) x‖ₑ *
          ‖(fwdDiff h)^[2 - l] (Ω.vertCutoff j) (x + (l : ℝ) • h)‖ₑ
        ≤ (A * min 1 (t ^ (l : ℝ))) * (B * min 1 (t ^ ((2 - l : ℕ) : ℝ))) :=
          mul_le_mul' (hu l hl2) (hv (2 - l) (Nat.sub_le 2 l) _)
      _ = A * B * (min 1 (t ^ (l : ℝ)) * min 1 (t ^ ((2 - l : ℕ) : ℝ))) := by ring
      _ ≤ A * B * min 1 (t ^ (2 : ℝ)) := by
          refine mul_le_mul' le_rfl ((min_one_rpow_mul_le t (Nat.cast_nonneg _)
            (Nat.cast_nonneg _)).trans_eq ?_)
          congr 2
          rw [Nat.cast_sub hl2]
          ring
  have hsum : ∑ l ∈ Finset.range (2 + 1), (Nat.choose 2 l : ℝ≥0∞) = 4 := by
    simp [Finset.sum_range_succ]
    norm_num
  rw [show Ω.extendAtom j a = fun y => a (Ω.proj y) * Ω.vertCutoff j y from rfl, higherDiff_mul]
  calc ‖∑ l ∈ Finset.range (2 + 1), (Nat.choose 2 l : ℂ) *
        ((fwdDiff h)^[l] (fun y => a (Ω.proj y)) x *
          (fwdDiff h)^[2 - l] (Ω.vertCutoff j) (x + (l : ℝ) • h))‖ₑ
      ≤ ∑ l ∈ Finset.range (2 + 1), (Nat.choose 2 l : ℝ≥0∞) * (A * B * min 1 (t ^ (2 : ℝ))) :=
        (enorm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = 4 * A * B * min 1 (t ^ (2 : ℝ)) := by
        rw [← Finset.sum_mul, hsum]
        ring

/-- The radius factor `d (1 + M ‖ρ‖_1) + c + 1` of the extended atoms. -/
noncomputable def extendRadius (d : ℝ) : ℝ :=
  d * (1 + Ω.M * Ω.graphBumpNorm) + Ω.cutoffLevel + 1

/-- The centre `c' + φ_j(c') e` in `V` of the extension of an atom centred at `c' ∈ H`. -/
noncomputable def extendCenter (j : ℕ) (c' : Ω.hyperplane) : V :=
  (c' : V) + Ω.smoothGraph j c' • Ω.e

/-- The projection of the extended centre is the centre. -/
theorem proj_extendCenter (j : ℕ) (c' : Ω.hyperplane) : Ω.proj (Ω.extendCenter j c') = c' := by
  rw [extendCenter, map_add, map_smul, Ω.proj_e, smul_zero, add_zero, Ω.proj_coe]

/-- **The support of extended atoms**: if `a = 0` outside `B̄(c', d 2^(-j))`, then `A = 0` outside
`B̄(c' + φ_j(c') e, (d (1 + M ‖ρ‖_1) + c + 1) 2^(-j))`. -/
theorem extendAtom_eq_zero (j : ℕ) {a : Ω.hyperplane → ℂ} {d : ℝ} {c' : Ω.hyperplane} (h0 : ∀ y, d / 2 ^ j < ‖y - c'‖ → a y = 0) {x : V}
    (hx : Ω.extendRadius d / 2 ^ j < ‖x - Ω.extendCenter j c'‖) : Ω.extendAtom j a x = 0 := by
  by_contra hne
  have ha : a (Ω.proj x) ≠ 0 := left_ne_zero_of_mul hne
  have hv : Ω.vertCutoff j x ≠ 0 := right_ne_zero_of_mul hne
  have h1 : ‖Ω.proj x - c'‖ ≤ d / 2 ^ j := not_lt.1 fun h => ha (h0 _ h)
  have h2 : |inner ℝ x Ω.e - Ω.smoothGraph j (Ω.proj x)| ≤ (Ω.cutoffLevel + 1) / 2 ^ j :=
    le_of_lt (not_le.1 fun h => hv (Ω.vertCutoff_eq_zero j h))
  have h3 : |Ω.smoothGraph j (Ω.proj x) - Ω.smoothGraph j c'| ≤
      Ω.M * Ω.graphBumpNorm * (d / 2 ^ j) :=
    (Ω.abs_smoothGraph_sub_le j _ _).trans (mul_le_mul_of_nonneg_left h1
      (mul_nonneg Ω.M_nonneg Ω.graphBumpNorm_nonneg))
  have hdecomp : x - Ω.extendCenter j c' = ((Ω.proj x - c' : Ω.hyperplane) : V) +
      (inner ℝ x Ω.e - Ω.smoothGraph j c') • Ω.e := by
    have hx' : x = (Ω.proj x : V) + inner ℝ x Ω.e • Ω.e := by rw [coe_proj, sub_add_cancel]
    conv_lhs => rw [hx']
    rw [extendCenter, Submodule.coe_sub, sub_smul]
    abel
  have hle : ‖x - Ω.extendCenter j c'‖ ≤ Ω.extendRadius d / 2 ^ j := by
    rw [hdecomp]
    calc ‖((Ω.proj x - c' : Ω.hyperplane) : V) + (inner ℝ x Ω.e - Ω.smoothGraph j c') • Ω.e‖
        ≤ ‖Ω.proj x - c'‖ + |inner ℝ x Ω.e - Ω.smoothGraph j c'| := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs, Submodule.norm_coe]
      _ ≤ ‖Ω.proj x - c'‖ + (|inner ℝ x Ω.e - Ω.smoothGraph j (Ω.proj x)| +
            |Ω.smoothGraph j (Ω.proj x) - Ω.smoothGraph j c'|) := by
          gcongr
          exact abs_sub_le _ _ _
      _ ≤ d / 2 ^ j + ((Ω.cutoffLevel + 1) / 2 ^ j + Ω.M * Ω.graphBumpNorm * (d / 2 ^ j)) :=
          add_le_add h1 (add_le_add h2 h3)
      _ = Ω.extendRadius d / 2 ^ j := by
          rw [extendRadius]
          ring
  exact absurd hle (not_le.2 hx)

/-- **Extended atoms are regular atoms** of order and exponent `2` on `V`: if `a` is continuous,
vanishes outside `B̄(c', d 2^(-j))` and `|Δ_h^l a| ≤ A_0 min(1, (2^j ‖h‖)^l)` for `l ≤ 2`, then
`A = (a ∘ P) v_j` is a regular atom of level `j` with centre `c' + φ_j(c') e`. -/
theorem isRegularAtom_extendAtom {p : ℝ≥0∞} (j : ℕ) {a : Ω.hyperplane → ℂ} (hac : Continuous a)
    {d : ℝ} (hd : 0 ≤ d) {c' : Ω.hyperplane} (h0 : ∀ y, d / 2 ^ j < ‖y - c'‖ → a y = 0)
    {A : ℝ≥0∞}
    (ha : ∀ l ≤ 2, ∀ h y, ‖(fwdDiff h)^[l] a y‖ₑ ≤
      A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (l : ℝ))) :
    IsRegularAtom p 2 2 (Ω.extendRadius d)
      (4 * A * ENNReal.ofReal Ω.vertCutoffConst * (((2 + 1 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Ω.extendRadius d ^ finrank ℝ V) * volume (ball (0 : V) 1))) ^
          (1 / p.toReal)) j (Ω.extendCenter j c') (Ω.extendAtom j a) := by
  have hR : 0 ≤ Ω.extendRadius d := by
    have := Ω.cutoffLevel_pos
    have := mul_nonneg hd (add_nonneg zero_le_one (mul_nonneg Ω.M_nonneg Ω.graphBumpNorm_nonneg))
    rw [extendRadius]
    linarith
  have hB : 1 ≤ 4 * ENNReal.ofReal Ω.vertCutoffConst := by
    have h4 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Ω.vertCutoffConst := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [Ω.four_le_vertCutoffConst])
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ 4 * ENNReal.ofReal Ω.vertCutoffConst := mul_le_mul' (by norm_num) h4
  refine isRegularAtom_of_pointwise hR (Ω.continuous_extendAtom j hac).aestronglyMeasurable
    (fun x hx => Ω.extendAtom_eq_zero j h0 hx) (fun x => ?_) (fun h x => ?_)
  · refine (Ω.enorm_extendAtom_le j (fun y => by simpa using ha 0 (Nat.zero_le 2) 0 y) x).trans ?_
    calc A = 1 * A := (one_mul A).symm
      _ ≤ 4 * ENNReal.ofReal Ω.vertCutoffConst * A := mul_le_mul' hB le_rfl
      _ = 4 * A * ENNReal.ofReal Ω.vertCutoffConst := by ring
  · have h2 := Ω.enorm_higherDiff_two_extendAtom_le j ha h x
    simpa using h2

/-! ### The extension operator -/

section Extension

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The terms of the reproducing formula on `H`: `g_j = η_j ⋆ (k_j ⋆ g)`, with the mollifier bump of
`H` and moment order `1`. -/
noncomputable def extLevelH (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane))
    (x' : Ω.hyperplane) : ℂ :=
  conv (Ω.graphBump.dual 1 j) (Ω.graphBump.localMean hp 1 j g) volume x'

/-- The terms on `H` are continuous. -/
theorem continuous_extLevelH (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    Continuous (Ω.extLevelH hp j g) :=
  (Ω.graphBump.hasCompactSupport_dual 1 j).continuous_convolution_left
    (ContinuousLinearMap.mul ℂ ℂ) (Ω.graphBump.continuous_dual 1 j)
    ((Lp.memLp _).locallyIntegrable Fact.out)

/-- The radius factor of the cell atoms on `H`. -/
noncomputable def extRadiusH : ℝ := 2 * ((1 : ℕ) : ℝ) * Ω.graphBump.radius + finrank ℝ Ω.hyperplane

/-- The radius factor of the cell atoms on `H` is nonnegative. -/
theorem extRadiusH_nonneg : 0 ≤ Ω.extRadiusH :=
  add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
    Ω.graphBump.radius_nonneg) (Nat.cast_nonneg _)

/-- **The extended atoms**: there are `C < ∞` and an overlap bound `N` such that for every level
`j` and `h ∈ L_p(H)` the extensions of the cell atoms of `η_j ⋆ h` are regular atoms on `V` of order
and exponent `2`, centred at `c_{j,m} + φ_j(c_{j,m}) e`, whose centres have overlap at most `N`: they
project to the cell centres of `H`. -/
theorem exists_extension_atoms :
    ∃ (C : ℝ≥0∞) (N : ℕ), C ≠ ∞ ∧ ∀ (j : ℕ) {h : Ω.hyperplane → ℂ}, MemLp h p volume →
      (∀ m, IsRegularAtom p 2 2 (Ω.extendRadius Ω.extRadiusH) C j
        (Ω.extendCenter j (cellCenter j m))
        (Ω.extendAtom j (cellAtom p (Ω.graphBump.dual 1 j) j h m))) ∧
      ∀ x (S : Finset (Fin (finrank ℝ Ω.hyperplane) → ℤ)),
        (∀ m ∈ S, cellCoef p j h m ≠ 0 ∧
          ‖x - Ω.extendCenter j (cellCenter j m)‖ ≤ (Ω.extendRadius Ω.extRadiusH + 2) / 2 ^ j) →
          S.card ≤ N := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨A, hA, hb⟩ := Ω.graphBump.exists_cellAtom_pointwise_bound hp1 1 2
  have hd : 0 ≤ Ω.extendRadius Ω.extRadiusH := by
    have := Ω.cutoffLevel_pos
    have := mul_nonneg Ω.extRadiusH_nonneg
      (add_nonneg zero_le_one (mul_nonneg Ω.M_nonneg Ω.graphBumpNorm_nonneg))
    rw [extendRadius]
    linarith
  refine ⟨4 * A * ENNReal.ofReal Ω.vertCutoffConst * (((2 + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (Ω.extendRadius Ω.extRadiusH ^ finrank ℝ V) * volume (ball (0 : V) 1))) ^
        (1 / p.toReal), ⌈(2 * (Ω.extendRadius Ω.extRadiusH + 2) + 2) ^
          finrank ℝ Ω.hyperplane⌉₊, ?_, fun j h hh => ⟨fun m => ?_, fun x S hS => ?_⟩⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA)
      ENNReal.ofReal_ne_top) (ENNReal.rpow_ne_top_of_nonneg
        (div_nonneg zero_le_one ENNReal.toReal_nonneg) (ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            measure_ball_lt_top.ne)))
  · exact Ω.isRegularAtom_extendAtom j (continuous_cellAtom hp1 (Ω.graphBump.continuous_dual 1 j)
      (Ω.graphBump.hasCompactSupport_dual 1 j) hh j m) Ω.extRadiusH_nonneg
      (fun y hy => cellAtom_eq_zero (fun z hz => Ω.graphBump.dual_eq_zero_of_lt 1 j hz) m hy)
      (fun l hl h' y => hb j hh m l hl h' y)
  · refine card_le_of_norm_sub_cellCenter_le j (by linarith) (Ω.proj x) S fun m hm => ?_
    calc ‖Ω.proj x - cellCenter j m‖ = ‖Ω.proj (x - Ω.extendCenter j (cellCenter j m))‖ := by
          rw [map_sub, Ω.proj_extendCenter]
      _ ≤ ‖x - Ω.extendCenter j (cellCenter j m)‖ := Ω.norm_proj_le _
      _ ≤ (Ω.extendRadius Ω.extRadiusH + 2) / 2 ^ j := (hS m hm).2

/-- The levels of the extension: `F_j(x) = g_j(Px) v_j(x)`. -/
noncomputable def extLevel (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    V → ℂ :=
  Ω.extendAtom j (Ω.extLevelH hp j g)

/-- **The levels are sums of extended atoms**: `F_j = ∑_m λ_{j,m} A_{j,m}` at every point. -/
theorem extLevel_eq_tsum (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane))
    (x : V) :
    Ω.extLevel hp j g x = ∑' m, cellCoef p j (Ω.graphBump.localMean hp 1 j g) m *
      Ω.extendAtom j (cellAtom p (Ω.graphBump.dual 1 j) j (Ω.graphBump.localMean hp 1 j g) m) x := by
  have hρ : 0 ≤ 2 * ((1 : ℕ) : ℝ) * Ω.graphBump.radius / 2 ^ j :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
      Ω.graphBump.radius_nonneg) (by positivity)
  rw [extLevel, extendAtom, extLevelH, conv_eq_tsum_cellAtom Fact.out
    (Ω.graphBump.continuous_dual 1 j) hρ (fun y hy => Ω.graphBump.dual_eq_zero_of_lt 1 j hy)
    (Lp.memLp _) j, ← tsum_mul_right]
  refine tsum_congr fun m => ?_
  rw [extendAtom, mul_assoc]

/-- The levels of the extension are continuous. -/
theorem continuous_extLevel (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    Continuous (Ω.extLevel hp j g) :=
  Ω.continuous_extendAtom j (Ω.continuous_extLevelH hp j g)

/-- **The levels of the extension in `L_p`**: `‖F_j‖_p ≤ K 2^(-j/p) ‖k_j ⋆ g‖_p`. -/
theorem eLpNorm_extLevel_le (hp : p ≠ ∞) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ j (g : Lp ℂ p (volume : Measure Ω.hyperplane)),
      eLpNorm (Ω.extLevel hp j g) p volume ≤
        K * dyadicWeight (-(1 / p.toReal)) j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨C, N, hC, hatoms⟩ := Ω.exists_extension_atoms (p := p)
  have hexp : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  refine ⟨(N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (ENNReal.natCast_ne_top N)) hC, fun j g => ?_⟩
  obtain ⟨hat, hN⟩ := hatoms j (Lp.memLp (Ω.graphBump.localMean hp 1 j g))
  have hlev := eLpNorm_levelSum_le hp1 hp (fun m => Ω.extendCenter j (cellCenter j m))
    (fun m => Ω.extendAtom j (cellAtom p (Ω.graphBump.dual 1 j) j
      (Ω.graphBump.localMean hp 1 j g) m))
    (cellCoef p j (Ω.graphBump.localMean hp 1 j g))
    (fun x S hS => hN x S fun m hm => ⟨(hS m hm).1, by simpa using (hS m hm).2⟩) hat
    (Ω.continuous_extLevel hp j g).aestronglyMeasurable
    (Eventually.of_forall (Ω.extLevel_eq_tsum hp j g))
  refine hlev.trans_eq ?_
  rw [levelNorm_cellCoef hp0 hp (Lp.memLp _) j, ← Lp.enorm_def]
  have hw : dyadicWeight (-(finrank ℝ V / p.toReal)) j *
      dyadicWeight (finrank ℝ Ω.hyperplane / p.toReal) j = dyadicWeight (-(1 / p.toReal)) j := by
    rw [← ENNReal.dyadicWeight_add, Ω.finrank_hyperplane_eq]
    congr 1
    ring
  calc (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) *
        (dyadicWeight (finrank ℝ Ω.hyperplane / p.toReal) j *
          ‖Ω.graphBump.localMean hp 1 j g‖ₑ)
      = (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C * (dyadicWeight (-(finrank ℝ V / p.toReal)) j *
          dyadicWeight (finrank ℝ Ω.hyperplane / p.toReal) j) *
            ‖Ω.graphBump.localMean hp 1 j g‖ₑ := by ring
    _ = _ := by rw [hw]

/-- The levels of the extension are in `L_p`. -/
theorem memLp_extLevel (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    MemLp (Ω.extLevel hp j g) p volume := by
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_extLevel_le hp
  exact memLp_iff.2 ((hle j g).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK.lt_top
    (ENNReal.dyadicWeight_lt_top _ _)) enorm_lt_top))

/-- The level `F_j` of the extension in `L_p(V)`. -/
noncomputable def traceExtTerm (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    Lp ℂ p (volume : Measure V) :=
  (Ω.memLp_extLevel hp j g).toLp _

/-- The level in `L_p` agrees with `F_j` almost everywhere. -/
theorem traceExtTerm_ae (hp : p ≠ ∞) (j : ℕ) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    Ω.traceExtTerm hp j g =ᵐ[volume] Ω.extLevel hp j g :=
  MemLp.coeFn_toLp _

/-- The **extension** `E g = ∑_j F_j` of `g` from the boundary. -/
noncomputable def graphExtension (hp : p ≠ ∞) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    Lp ℂ p (volume : Measure V) :=
  ∑' j, Ω.traceExtTerm hp j g

/-- **The extension converges absolutely** for `s > 0` and a finite local means quasi-norm
`X = ‖(2^(js) ‖k_j ⋆ g‖_p)_j‖_{ℓ_q}`: `‖F_j‖_p ≤ K X 2^(-js)`. -/
theorem summable_traceExtTerm (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {g : Lp ℂ p (volume : Measure Ω.hyperplane)}
    (hX : Ω.graphBump.localMeansNorm hp 1 s q g < ∞) :
    Summable fun j => Ω.traceExtTerm hp j g := by
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_extLevel_le hp
  set X := Ω.graphBump.localMeansNorm hp 1 s q g
  have hterm : ∀ j, ‖Ω.traceExtTerm hp j g‖ₑ ≤ K * X * dyadicWeight (-s) j := fun j => by
    have hXj : dyadicWeight s j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ ≤ X :=
      ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
        (fun j => dyadicWeight s j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ) j
    rw [Lp.enorm_def, eLpNorm_congr_ae (Ω.traceExtTerm_ae hp j g)]
    refine (hle j g).trans ?_
    have hw : dyadicWeight (-(1 / p.toReal)) j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ ≤
        dyadicWeight (-s) j * (dyadicWeight s j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ) := by
      rw [← mul_assoc, ← ENNReal.dyadicWeight_add, neg_add_cancel, ENNReal.dyadicWeight_zero_left,
        one_mul]
      calc dyadicWeight (-(1 / p.toReal)) j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ
          ≤ 1 * ‖Ω.graphBump.localMean hp 1 j g‖ₑ := by
            refine mul_le_mul' ?_ le_rfl
            have := ENNReal.dyadicWeight_anti (s := -(1 / p.toReal))
              (by have := ENNReal.toReal_nonneg (a := p); simp only [neg_nonpos]; positivity)
              (Nat.zero_le j)
            simpa using this
        _ = ‖Ω.graphBump.localMean hp 1 j g‖ₑ := one_mul _
    calc K * dyadicWeight (-(1 / p.toReal)) j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ
        = K * (dyadicWeight (-(1 / p.toReal)) j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ) := by ring
      _ ≤ K * (dyadicWeight (-s) j * X) :=
          mul_le_mul' le_rfl (hw.trans (mul_le_mul' le_rfl hXj))
      _ = K * X * dyadicWeight (-s) j := by ring
  refine Summable.of_norm ?_
  have hfin : ∑' j, ‖Ω.traceExtTerm hp j g‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hK hX.ne)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)
  simpa only [toReal_enorm] using ENNReal.summable_toReal hfin

/-- **The extension is bounded** (Schneider–Vybíral, Theorem 4.10, for `p ≥ 1`): for `0 < s < 1`
there is `K < ∞` with
`‖E g‖_p + ‖(2^(k(s+1/p)) ω_2(E g, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖g‖_{L_p(H)} + ‖(2^(ks) ω_1(g, 2^(-k))_p)_k‖_{ℓ_q})`, by the atomic synthesis on `V` with the
extended atoms. -/
theorem modNorm_graphExtension_le (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : Lp ℂ p (volume : Measure Ω.hyperplane),
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k) < ∞ →
      ‖Ω.graphExtension hp g‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p 2 (Ω.graphExtension hp g) k) ≤
        K * (‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k)) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  have hσ2 : s + 1 / p.toReal < 2 := by
    have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hpr
    linarith
  obtain ⟨C, N, hC, hatoms⟩ := Ω.exists_extension_atoms (p := p)
  refine ⟨atomSynthConst p N C 2 (s + 1 / p.toReal) 2 * Ω.graphBump.upperConst 1 s,
    ENNReal.mul_ne_top (atomSynthConst_ne_top hp1 N hC 2 hσ0 hσ2)
      (Ω.graphBump.upperConst_ne_top 1 s), fun g hg => ?_⟩
  have hLM := Ω.graphBump.localMeansNorm_le hp 1 s hq g
  have hX : Ω.graphBump.localMeansNorm hp 1 s q g < ∞ :=
    hLM.trans_lt (ENNReal.mul_lt_top (Ω.graphBump.upperConst_ne_top 1 s).lt_top hg)
  have hsyn := modNorm_le_coeffNorm hp (fun j m => Ω.extendCenter j (cellCenter j m))
    (fun j m => Ω.extendAtom j (cellAtom p (Ω.graphBump.dual 1 j) j
      (Ω.graphBump.localMean hp 1 j g) m))
    (fun j => cellCoef p j (Ω.graphBump.localMean hp 1 j g))
    (fun j x S hS => (hatoms j (Lp.memLp _)).2 x S fun m hm =>
      ⟨(hS m hm).1, by simpa using (hS m hm).2⟩)
    (fun j m => (hatoms j (Lp.memLp _)).1 m)
    (fun j => (Ω.traceExtTerm_ae hp j g).mono fun x hx => hx.trans (Ω.extLevel_eq_tsum hp j g x))
    (((Ω.summable_traceExtTerm hp hs hq hX).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))
    hσ0 hσ2 hq
  refine hsyn.trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl (le_trans (le_of_eq ?_) hLM)
  rw [coeffNorm, LocalMeansBump.localMeansNorm]
  congr 1
  funext j
  rw [levelNorm_cellCoef hp0 hp (Lp.memLp _) j, ← Lp.enorm_def, ← mul_assoc,
    ← ENNReal.dyadicWeight_add, Ω.finrank_hyperplane_eq]
  congr 2
  ring

end Extension

/-! ### The trace of the extension -/

section TraceExtension

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A finite norm with moduli of order `2` and smoothness `σ` on `V` gives a finite intrinsic norm
of order `L ≥ 2` on `Ω`. -/
theorem intrinsicNorm_lt_top_of_modNorm (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {σ : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) {G : Lp ℂ p (volume : Measure V)}
    (hG : ‖G‖ₑ + lqNorm q (fun k => dyadicWeight σ k * lpModulus p 2 G k) < ∞) :
    ‖Ω.cutoff G‖ₑ + lqNorm q (fun k => dyadicWeight σ k * lpModulusOn p Ω.domain L G k) < ∞ ∧
      Ω.intrinsicNorm hp L σ q G < ∞ := by
  have h1 : ‖Ω.cutoff G‖ₑ + lqNorm q (fun k => dyadicWeight σ k * lpModulusOn p Ω.domain L G k) <
      ∞ :=
    ((Ω.modNormOn_le_modNorm L σ q rfl).trans (modNorm_order_le hL σ q G)).trans_lt
      (ENNReal.mul_lt_top (by simp) hG)
  exact ⟨h1, Ω.intrinsicNorm_lt_top hp L σ hq h1⟩

/-- **One level of the extension**: there are `C < ∞` and `N` such that for `0 < σ < 2`,
`1 ≤ q ≤ ∞`, `g ∈ L_p(H)` and every level `j`,
`‖F_j‖_p + ‖(2^(kσ) ω_2(F_j, 2^(-k))_p)_k‖_{ℓ_q} ≤ K_σ 2^(j(σ - 1/p)) ‖k_j ⋆ g‖_p` with
`K_σ = Rd.atomSynthConst p N C 2 σ 2`: the level is a sum of the extended atoms
(`Rd.LipschitzGraph.exists_extension_atoms`, `Rd.modNorm_level_le`). -/
theorem exists_modNorm_traceExtTerm_le (hp : p ≠ ∞) :
    ∃ (C : ℝ≥0∞) (N : ℕ), C ≠ ∞ ∧ ∀ {σ : ℝ}, 0 < σ → σ < 2 → ∀ {q : ℝ≥0∞}, 1 ≤ q →
      ∀ (g : Lp ℂ p (volume : Measure Ω.hyperplane)) (j : ℕ),
        ‖Ω.traceExtTerm hp j g‖ₑ + lqNorm q (fun k =>
            dyadicWeight σ k * lpModulus p 2 (Ω.traceExtTerm hp j g) k) ≤
          atomSynthConst p N C 2 σ 2 *
            (dyadicWeight (σ - 1 / p.toReal) j * ‖Ω.graphBump.localMean hp 1 j g‖ₑ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨C, N, hC, hatoms⟩ := Ω.exists_extension_atoms (p := p)
  refine ⟨C, N, hC, fun {σ'} hσ' hσ'2 {q'} hq' g j => ?_⟩
  obtain ⟨hat, hN⟩ := hatoms j (Lp.memLp (Ω.graphBump.localMean hp 1 j g))
  refine (modNorm_level_le hp j (fun m => Ω.extendCenter j (cellCenter j m))
    (fun m => Ω.extendAtom j (cellAtom p (Ω.graphBump.dual 1 j) j
      (Ω.graphBump.localMean hp 1 j g) m)) (cellCoef p j (Ω.graphBump.localMean hp 1 j g))
    (fun x S hS => hN x S fun m hm => ⟨(hS m hm).1, by simpa using (hS m hm).2⟩) hat
    ((Ω.traceExtTerm_ae hp j g).mono fun x hx => hx.trans (Ω.extLevel_eq_tsum hp j g x))
    hσ' hσ'2 hq').trans_eq ?_
  rw [levelNorm_cellCoef hp0 hp (Lp.memLp _) j, ← Lp.enorm_def]
  congr 1
  rw [← mul_assoc, ← ENNReal.dyadicWeight_add, Ω.finrank_hyperplane_eq]
  congr 2
  ring

/-- **The traces of the partial sums of the extension** are the partial sums of the reproducing
formula on `H`: `Tr (∑_{j ≤ J} F_j) = ∑_{j ≤ J} η_j ⋆ (k_j ⋆ g)`, since the partial sums are
continuous with the values `∑_{j ≤ J} (η_j ⋆ (k_j ⋆ g))(x')` on the graph
(`Rd.LipschitzGraph.trace_ae_eq_comp_graphMap`). -/
theorem trace_sum_traceExtTerm (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) (J : ℕ)
    (hFJ : ‖∑ j ∈ Finset.range (J + 1), Ω.traceExtTerm hp j g‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k *
        lpModulus p 2 (∑ j ∈ Finset.range (J + 1), Ω.traceExtTerm hp j g) k) < ∞) :
    Ω.trace hp L (∑ j ∈ Finset.range (J + 1), Ω.traceExtTerm hp j g) =
      ∑ j ∈ Finset.range (J + 1),
        convLp hp (Ω.graphBump.integrable_dual 1 j) (Ω.graphBump.localMean hp 1 j g) := by
  have hcont : Continuous fun x => ∑ j ∈ Finset.range (J + 1), Ω.extLevel hp j g x :=
    continuous_finsetSum _ fun j _ => Ω.continuous_extLevel hp j g
  have hae : ((∑ j ∈ Finset.range (J + 1), Ω.traceExtTerm hp j g :
      Lp ℂ p (volume : Measure V)) : V → ℂ) =ᵐ[volume]
        fun x => ∑ j ∈ Finset.range (J + 1), Ω.extLevel hp j g x := by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
      (fun j => Ω.traceExtTerm hp j g), ae_all_iff.2 fun j => Ω.traceExtTerm_ae hp j g]
      with x hx1 hx2
    rw [hx1]
    exact Finset.sum_congr rfl fun j _ => hx2 j
  have htr := Ω.trace_ae_eq_comp_graphMap hp (by omega) hs hq
    (Ω.intrinsicNorm_lt_top_of_modNorm hp hL hq hFJ).1 hcont hae
  refine Lp.ext ?_
  filter_upwards [htr, Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
    (fun j => convLp hp (Ω.graphBump.integrable_dual 1 j) (Ω.graphBump.localMean hp 1 j g)),
    ae_all_iff.2 fun j => convLp_apply_ae hp (Ω.graphBump.integrable_dual 1 j)
      (Ω.graphBump.localMean hp 1 j g)] with x' h1 h2 h3
  rw [h1, h2, Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3 j, extLevel, Ω.extendAtom_graphMap]
  rfl

/-- **The trace of the extension** (Schneider–Vybíral, Theorem 4.11, for `p ≥ 1`): for
`0 < s < 1`, `L ≥ 2` and `g ∈ L_p(H)` with `‖g‖_p + ‖(2^(ks) ω_1(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞`,
`Tr (E g) = g`. The partial sums `∑_{j ≤ J} F_j` are continuous with traces
`∑_{j ≤ J} η_j ⋆ (k_j ⋆ g) → g` (`Rd.LipschitzGraph.trace_ae_eq_comp_graphMap`), and they converge
to `E g` in `B^{1/p}_{p,1}`, where the trace is continuous
(`Rd.LipschitzGraph.tendsto_trace_of_modNorm_sub_le`). -/
theorem trace_graphExtension (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {g : Lp ℂ p (volume : Measure Ω.hyperplane)}
    (hg : ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k) < ∞) :
    Ω.trace hp L (Ω.graphExtension hp g) = g := by
  have hp1 : 1 ≤ p := Fact.out
  have hpr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hpinv0 : 0 < 1 / p.toReal := by positivity
  have hpinv1 : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hpr
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  have hσ2 : s + 1 / p.toReal < 2 := by linarith
  set X := Ω.graphBump.localMeansNorm hp 1 s q g
  have hX : X < ∞ := (Ω.graphBump.localMeansNorm_le hp 1 s hq g).trans_lt
    (ENNReal.mul_lt_top (Ω.graphBump.upperConst_ne_top 1 s).lt_top hg)
  set T : ℕ → Lp ℂ p (volume : Measure V) := fun j => Ω.traceExtTerm hp j g
  have hsum : Summable T := Ω.summable_traceExtTerm hp hs hq hX
  obtain ⟨C, N, hC, hlevel⟩ := Ω.exists_modNorm_traceExtTerm_le hp
  have hfinT : ∀ j, ‖T j‖ₑ + lqNorm q
      (fun k => dyadicWeight (s + 1 / p.toReal) k * lpModulus p 2 (T j) k) < ∞ := fun j =>
    (hlevel hσ0 hσ2 hq g j).trans_lt (ENNReal.mul_lt_top
      (atomSynthConst_ne_top hp1 N hC 2 hσ0 hσ2).lt_top (ENNReal.mul_lt_top
        (ENNReal.dyadicWeight_lt_top _ _) enorm_lt_top))
  -- the finite norms of the extension and of its partial sums
  have hEfin := (Ω.modNorm_graphExtension_le hp hs hs1 hq)
  obtain ⟨KE, hKE, hEle⟩ := hEfin
  have hF : ‖Ω.graphExtension hp g‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p 2 (Ω.graphExtension hp g) k) < ∞ :=
    (hEle g hg).trans_lt (ENNReal.mul_lt_top hKE.lt_top hg)
  have hFJ : ∀ J, ‖∑ j ∈ Finset.range (J + 1), T j‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p 2 (∑ j ∈ Finset.range (J + 1), T j) k) <
        ∞ := fun J => modNorm_finsetSum_lt_top _ T hq fun j _ => hfinT j
  -- the tail in the norm of `B^{1/p}_{p,1}` with order `L`
  set K1 := atomSynthConst p N C 2 (1 / p.toReal) 2
  have hK1 : K1 ≠ ∞ := atomSynthConst_ne_top hp1 N hC 2 hpinv0 (by linarith)
  set Q : Lp ℂ p (volume : Measure V) → ℝ≥0∞ := fun G =>
    ‖G‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / p.toReal) k * lpModulus p L G k)
  have hQT : ∀ j, Q (T j) ≤ 2 ^ (L - 2) * K1 * ‖Ω.graphBump.localMean hp 1 j g‖ₑ := fun j => by
    refine (modNorm_order_le hL _ 1 (T j)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul' le_rfl ((hlevel hpinv0 (by linarith) le_rfl g j).trans_eq ?_)
    rw [sub_self, ENNReal.dyadicWeight_zero_left, one_mul]
  have hQtail : ∀ J, Q (∑' i, T (i + (J + 1))) ≤
      ∑' i, 2 ^ (L - 2) * K1 * ‖Ω.graphBump.localMean hp 1 (i + (J + 1)) g‖ₑ := fun J =>
    (modNorm_one_tsum_le L (1 / p.toReal) ((summable_nat_add_iff (J + 1)).2 hsum)).trans
      (ENNReal.tsum_le_tsum fun i => hQT (i + (J + 1)))
  -- the tails tend to `0`
  have hhsum : ∑' j, 2 ^ (L - 2) * K1 * ‖Ω.graphBump.localMean hp 1 j g‖ₑ ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hK1) (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs) hX.ne)
      (ENNReal.tsum_le_lqNorm_dyadicWeight hq s _))
  have htail : Tendsto (fun J => ∑' i, 2 ^ (L - 2) * K1 *
      ‖Ω.graphBump.localMean hp 1 (i + (J + 1)) g‖ₑ) atTop (𝓝 0) :=
    (ENNReal.tendsto_sum_nat_add _ hhsum).comp (tendsto_add_atTop_nat 1)
  -- the traces of the partial sums converge to the trace of the extension
  have hsplit : ∀ J, Ω.graphExtension hp g - ∑ j ∈ Finset.range (J + 1), T j =
      ∑' i, T (i + (J + 1)) := fun J => by
    rw [graphExtension, ← hsum.sum_add_tsum_nat_add (J + 1)]
    abel
  have hconv := Ω.tendsto_trace_of_modNorm_sub_le hp L hs hq
    (Ω.intrinsicNorm_lt_top_of_modNorm hp hL hq hF).2
    (fun J => (Ω.intrinsicNorm_lt_top_of_modNorm hp hL hq (hFJ J)).2) htail
    (fun J => ne_top_of_le_ne_top hhsum (ENNReal.tsum_comp_le_tsum_of_injective
      (add_left_injective (J + 1)) fun j => 2 ^ (L - 2) * K1 * ‖Ω.graphBump.localMean hp 1 j g‖ₑ))
    fun J => by rw [hsplit J]; exact hQtail J
  -- the traces of the partial sums are the partial sums of the reproducing formula on `H`
  have hpart : ∀ J, Ω.trace hp L (∑ j ∈ Finset.range (J + 1), T j) =
      ∑ j ∈ Finset.range (J + 1),
        convLp hp (Ω.graphBump.integrable_dual 1 j) (Ω.graphBump.localMean hp 1 j g) := fun J =>
    Ω.trace_sum_traceExtTerm hp hL hs hq g J (hFJ J)
  have hlim := Ω.graphBump.tendsto_sum_dual_localMean hp le_rfl g
  simp_rw [← hpart] at hlim
  exact tendsto_nhds_unique hconv hlim

/-- **The trace space of a Lipschitz graph domain** (Schneider–Vybíral, Theorem 4.11, for
`p ≥ 1`): for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, `g ∈ L_p(H)` is the trace of some
`f` with `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff
`‖g‖_p + ‖(2^(ks) ω_1(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. The trace is bounded
(`Rd.LipschitzGraph.modNorm_trace_le`), and `E g` is such an `f`
(`Rd.LipschitzGraph.trace_graphExtension`). -/
theorem exists_trace_eq_iff (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (g : Lp ℂ p (volume : Measure Ω.hyperplane)) :
    (∃ f : Lp ℂ p (volume : Measure V), ‖Ω.cutoff f‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * lpModulusOn p Ω.domain L f k) < ∞ ∧
        Ω.trace hp L f = g) ↔
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k) < ∞ := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨K, hK, hle⟩ := Ω.modNorm_trace_le hp L hs hs1 hq
    exact (hle f hf).trans_lt (ENNReal.mul_lt_top hK.lt_top hf)
  · intro hg
    obtain ⟨K, hK, hle⟩ := Ω.modNorm_graphExtension_le hp hs hs1 hq
    exact ⟨Ω.graphExtension hp g, (Ω.intrinsicNorm_lt_top_of_modNorm hp hL hq
      ((hle g hg).trans_lt (ENNReal.mul_lt_top hK.lt_top hg))).1,
      Ω.trace_graphExtension hp hL hs hs1 hq hg⟩

end TraceExtension

end LipschitzGraph

end Rd
