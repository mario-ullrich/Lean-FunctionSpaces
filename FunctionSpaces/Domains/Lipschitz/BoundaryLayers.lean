/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Lipschitz.BoundedLipschitz
public import FunctionSpaces.Domains.Lipschitz.GraphStraightening
public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Boundary layers of Lipschitz domains

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure and
`n = dim V`. For a set `U ⊆ V` and a step `h ∈ V`, the **switch set** `S_h(U)` (`Rd.switchSet`)
consists of the points `x` for which exactly one of `x` and `x + h` lies in `U`; it is the set where
`1_U(x + h) - 1_U(x) ≠ 0`, the symmetric difference `U ∆ (U - h)` (`Rd.switchSet_eq_symmDiff`),
and empty for `h = 0` (`Rd.switchSet_zero`). This file shows that the switch set of a bounded
Lipschitz domain is a layer of width `≲ ‖h‖` along the boundary.

* **Crossing.** A preconnected set that meets `U` and its complement meets the frontier of `U`
  (`Rd.inter_frontier_nonempty_of_isPreconnected`); so the segment from a switch point `x` to
  `x + h` contains a boundary point of `U` (`Rd.exists_mem_frontier_of_mem_switchSet`). The switch
  set of a measurable set is measurable and has volume at most `2 |U|`
  (`Rd.measurableSet_switchSet`, `Rd.volume_switchSet_le`), from Mathlib's
  `MeasurableSet.symmDiff` and `Set.symmDiff_subset_union`.
* **The height above a graph.** For a Lipschitz graph domain `{x : φ(x) < ⟪x, e⟫}` the height
  `η(x) = ⟪x, e⟫ - φ(x)` (`Rd.LipschitzGraph.height`) is positive exactly on the domain
  (`Rd.LipschitzGraph.mem_domain_iff_height_pos`), grows by `r` along `r e`
  (`Rd.LipschitzGraph.height_add_smul`), is the last coordinate of the graph coordinates
  `(x', t) ↦ γ(x') + t e` (`Rd.LipschitzGraph.height_graphEquiv`), and is `(1 + M)`-Lipschitz
  (`Rd.LipschitzGraph.abs_height_add_sub_le`). A switch point of the graph domain for the step
  `h` has `|η(x)| ≤ (1 + M) ‖h‖` (`Rd.LipschitzGraph.abs_height_le_of_mem_switchSet`), and the
  slab `{|η| ≤ δ}` meets a closed ball of radius `ρ` in a set of volume at most
  `2 δ ρ^(n-1) |B^{n-1}_1|` (`Rd.LipschitzGraph.volume_abs_height_le_inter_closedBall`), since the
  graph coordinates preserve the Lebesgue measure.
* **The layer of a bounded Lipschitz domain**
  (`Rd.BoundedLipschitzDomain.exists_volume_switchSet_inter_closedBall_le`): there is `C < ∞` with
  `|S_h(Ω) ∩ B̄(c, ρ)| ≤ C ‖h‖ ρ^(n-1)` for all `c`, `h` and `ρ ≥ ‖h‖`. For short steps every
  switch point lies, together with its step, in a chart ball, where `Ω` is a graph domain
  (`Rd.BoundedLipschitzDomain.switchSet_subset_iUnion`); for long steps `|S_h(Ω)| ≤ 2 |Ω|`. At the
  scales of atoms, `|S_h(Ω) ∩ B̄(c, d 2^(-j))| ≤ C d^n 2^(-jn) min(1, 2^j ‖h‖)` for `d ≥ 1`
  (`Rd.BoundedLipschitzDomain.exists_volume_switchSet_inter_closedBall_div_two_pow_le`).
-/

@[expose] public section

open MeasureTheory Metric Module Set
open scoped ENNReal symmDiff

open ENNReal (dyadicWeight)

namespace Rd

/-! ### Switch sets and crossing -/

/-- **A preconnected set that meets `U` and its complement meets the frontier of `U`**: otherwise
it would lie in the union of the disjoint open sets `int U` and `X \ cl U`, hence in one of them
(Mathlib's `IsPreconnected.subset_or_subset`), but it has points in `U` and outside `U`. -/
theorem inter_frontier_nonempty_of_isPreconnected {X : Type*} [TopologicalSpace X] {S U : Set X}
    (hS : IsPreconnected S) (h₁ : (S ∩ U).Nonempty) (h₂ : (S \ U).Nonempty) :
    (S ∩ frontier U).Nonempty := by
  by_contra hne
  have hsub : S ⊆ interior U ∪ (closure U)ᶜ := fun z hz => by
    by_cases hi : z ∈ interior U
    · exact Or.inl hi
    · exact Or.inr fun hc => hne ⟨z, hz, hc, hi⟩
  rcases hS.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset_closure) hsub with h | h
  · obtain ⟨z, hzS, hzU⟩ := h₂
    exact hzU (interior_subset (h hzS))
  · obtain ⟨z, hzS, hzU⟩ := h₁
    exact h hzS (subset_closure hzU)

/-- The **switch set** of `U` for the step `h`: the points `x` for which exactly one of `x` and
`x + h` lies in `U`. It is the set where `1_U(x + h) - 1_U(x) ≠ 0`. -/
def switchSet {X : Type*} [Add X] (U : Set X) (h : X) : Set X := {x | ¬(x ∈ U ↔ x + h ∈ U)}

/-- **The switch set is a symmetric difference**: `S_h(U) = U ∆ (U - h)`, where
`U - h = {x | x + h ∈ U}` (Mathlib's `symmDiff`, with `Set.mem_symmDiff`). -/
theorem switchSet_eq_symmDiff {X : Type*} [Add X] (U : Set X) (h : X) :
    switchSet U h = U ∆ ((· + h) ⁻¹' U) := by
  ext x
  simp only [switchSet, mem_ofPred_eq, Set.mem_symmDiff, mem_preimage]
  tauto

/-- There are no switch points for the zero step: `S_0(U) = ∅`. -/
@[simp]
theorem switchSet_zero {X : Type*} [AddZeroClass X] (U : Set X) : switchSet U 0 = ∅ := by
  ext x
  simp [switchSet]

/-- The switch set of a measurable set `U` is measurable, as the symmetric difference of `U` and
the measurable set `U - h` (`Rd.switchSet_eq_symmDiff`, Mathlib's `MeasurableSet.symmDiff`). -/
theorem measurableSet_switchSet {X : Type*} [MeasurableSpace X] [Add X] [MeasurableAdd X]
    {U : Set X} (hU : MeasurableSet U) (h : X) : MeasurableSet (switchSet U h) := by
  rw [switchSet_eq_symmDiff]
  exact hU.symmDiff (measurable_add_const h hU)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **A switch point sees the frontier on its step**: if exactly one of `x` and `x + h` lies in
`U` (`Rd.switchSet_eq_symmDiff`, Mathlib's `Set.mem_symmDiff`), the segment `[x, x + h]` contains
a point of the frontier of `U`, since the segment is convex, hence preconnected (Mathlib's
`Convex.isPreconnected`), and `Rd.inter_frontier_nonempty_of_isPreconnected` applies. -/
theorem exists_mem_frontier_of_mem_switchSet {U : Set V} {h x : V} (hx : x ∈ switchSet U h) :
    ∃ z ∈ segment ℝ x (x + h), z ∈ frontier U := by
  have hS := (convex_segment x (x + h)).isPreconnected
  simp only [switchSet_eq_symmDiff, Set.mem_symmDiff, mem_preimage] at hx
  rcases hx with ⟨hxU, hxh⟩ | ⟨hxh, hxU⟩
  · exact inter_frontier_nonempty_of_isPreconnected hS ⟨x, left_mem_segment ℝ _ _, hxU⟩
      ⟨x + h, right_mem_segment ℝ _ _, hxh⟩
  · exact inter_frontier_nonempty_of_isPreconnected hS ⟨x + h, right_mem_segment ℝ _ _, hxh⟩
      ⟨x, left_mem_segment ℝ _ _, hxU⟩

section Measure

variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- **The switch set has volume at most `2 |U|`**: it lies in `U ∪ (U - h)`
(`Rd.switchSet_eq_symmDiff`, Mathlib's `Set.symmDiff_subset_union`), and translations preserve
the Lebesgue measure (Mathlib's `measure_preimage_add_right`). -/
theorem volume_switchSet_le (U : Set V) (h : V) : volume (switchSet U h) ≤ 2 * volume U := by
  calc volume (switchSet U h) ≤ volume (U ∪ (· + h) ⁻¹' U) := by
        rw [switchSet_eq_symmDiff]
        exact measure_mono Set.symmDiff_subset_union
    _ ≤ volume U + volume ((· + h) ⁻¹' U) := measure_union_le _ _
    _ = 2 * volume U := by rw [measure_preimage_add_right, two_mul]

end Measure

/-! ### The height above the graph of a Lipschitz graph domain -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The **height** `η(x) = ⟪x, e⟫ - φ(x)` of `x` above the graph of `Ω`; it is positive exactly on
the domain (`Rd.LipschitzGraph.mem_domain_iff_height_pos`). -/
def height (x : V) : ℝ := inner ℝ x Ω.e - Ω.phi x

/-- `x` lies in the graph domain iff its height is positive. -/
theorem mem_domain_iff_height_pos (x : V) : x ∈ Ω.domain ↔ 0 < Ω.height x := by
  show Ω.phi x < inner ℝ x Ω.e ↔ 0 < inner ℝ x Ω.e - Ω.phi x
  exact sub_pos.symm

/-- **The height grows by `r` along `r e`**: `η(x + r e) = η(x) + r`, since `⟪e, e⟫ = 1` and `φ`
is constant along `e`. -/
theorem height_add_smul (x : V) (r : ℝ) : Ω.height (x + r • Ω.e) = Ω.height x + r := by
  rw [height, height, inner_add_left, real_inner_smul_left, Ω.inner_e_self, Ω.const]
  ring

/-- The points `γ(x') = x' + φ(x') e` of the graph have height `0`. -/
theorem height_graphMap (x' : Ω.hyperplane) : Ω.height (Ω.graphMap x') = 0 := by
  rw [height, Ω.inner_graphMap, Ω.phi_graphMap, sub_self]

/-- **The height is `(1 + M)`-Lipschitz**: `|η(x + h) - η(x)| ≤ (1 + M) ‖h‖`, from
`|⟪h, e⟫| ≤ ‖h‖` (Cauchy–Schwarz, `‖e‖ = 1`) and the Lipschitz bound of `φ`. -/
theorem abs_height_add_sub_le (x h : V) :
    |Ω.height (x + h) - Ω.height x| ≤ (1 + Ω.M) * ‖h‖ := by
  have h1 := abs_real_inner_le_norm h Ω.e
  rw [Ω.norm_e, mul_one] at h1
  have h2 := Ω.lipschitz (x + h) x
  rw [add_sub_cancel_left] at h2
  have e : Ω.height (x + h) - Ω.height x = inner ℝ h Ω.e - (Ω.phi (x + h) - Ω.phi x) := by
    simp only [height, inner_add_left]
    ring
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  rw [e, abs_le, show (1 + Ω.M) * ‖h‖ = ‖h‖ + Ω.M * ‖h‖ by ring]
  constructor <;> linarith

/-- **Switch points of a graph domain lie near the graph**: if exactly one of `x` and `x + h` lies
in the domain (`Rd.switchSet_eq_symmDiff`, Mathlib's `Set.mem_symmDiff`), then
`|η(x)| ≤ (1 + M) ‖h‖`, since `η` changes sign between `x` and `x + h`
(`Rd.LipschitzGraph.mem_domain_iff_height_pos`) and is `(1 + M)`-Lipschitz
(`Rd.LipschitzGraph.abs_height_add_sub_le`). -/
theorem abs_height_le_of_mem_switchSet {h x : V} (hx : x ∈ switchSet Ω.domain h) :
    |Ω.height x| ≤ (1 + Ω.M) * ‖h‖ := by
  obtain ⟨hd1, hd2⟩ := abs_le.1 (Ω.abs_height_add_sub_le x h)
  simp only [switchSet_eq_symmDiff, Set.mem_symmDiff, mem_preimage, Ω.mem_domain_iff_height_pos,
    not_lt] at hx
  rw [abs_le]
  rcases hx with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> constructor <;> linarith

section Coordinates

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **The height is the last graph coordinate**: `η(γ(x') + t e) = t`
(`Rd.LipschitzGraph.height_add_smul`, `Rd.LipschitzGraph.height_graphMap`). -/
theorem height_graphEquiv (p : Ω.hyperplane × ℝ) : Ω.height (Ω.graphEquiv p) = p.2 := by
  rw [graphEquiv_apply, height_add_smul, height_graphMap, zero_add]

/-- **The projection of the graph coordinates is the first coordinate**: `P(γ(x') + t e) = x'`,
since `P e = 0` and `P γ(x') = x'`. -/
theorem proj_graphEquiv (p : Ω.hyperplane × ℝ) : Ω.proj (Ω.graphEquiv p) = p.1 := by
  rw [graphEquiv_apply, map_add, map_smul, Ω.proj_e, smul_zero, add_zero, Ω.proj_graphMap]

/-- **The slab `{|η| ≤ δ}` inside a ball**: `|{|η| ≤ δ} ∩ B̄(c, ρ)| ≤ 2 δ ρ^(n-1) |B^H_1|` for
`ρ ≥ 0` and every real `δ`, with `B^H_1` the unit ball of the hyperplane `H = e^⊥` of dimension
`n - 1`; for `δ < 0` the set is empty and the bound reads `0`. In graph
coordinates `(x', t)` the set lies in `B̄^H(Pc, ρ) × [-δ, δ]`
(`Rd.LipschitzGraph.height_graphEquiv`,
`Rd.LipschitzGraph.proj_graphEquiv`, `‖P‖ ≤ 1`), and the graph coordinates preserve the Lebesgue
measure (`Rd.LipschitzGraph.measurePreserving_graphEquiv`; Mathlib's
`MeasurePreserving.measure_preimage_equiv`, for every set). -/
theorem volume_abs_height_le_inter_closedBall (c : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (δ : ℝ) :
    volume ({x | |Ω.height x| ≤ δ} ∩ closedBall c ρ) ≤
      ENNReal.ofReal (2 * δ) * ENNReal.ofReal ρ ^ (finrank ℝ V - 1) *
        volume (ball (0 : Ω.hyperplane) 1) := by
  have hsub : Ω.graphEquiv ⁻¹' ({x | |Ω.height x| ≤ δ} ∩ closedBall c ρ) ⊆
      closedBall (Ω.proj c) ρ ×ˢ Icc (-δ) δ := by
    rintro p ⟨h1, h2⟩
    have h1' : |p.2| ≤ δ := by simpa only [mem_ofPred_eq, Ω.height_graphEquiv] using h1
    refine ⟨?_, abs_le.1 h1'⟩
    rw [mem_closedBall, dist_eq_norm, ← Ω.proj_graphEquiv p, ← map_sub]
    refine (Ω.norm_proj_le _).trans ?_
    rw [mem_closedBall, dist_eq_norm] at h2
    exact h2
  calc volume ({x | |Ω.height x| ≤ δ} ∩ closedBall c ρ)
      = (volume.prod volume) (Ω.graphEquiv ⁻¹' ({x | |Ω.height x| ≤ δ} ∩ closedBall c ρ)) :=
        (Ω.measurePreserving_graphEquiv.measure_preimage_equiv _).symm
    _ ≤ (volume.prod volume) (closedBall (Ω.proj c) ρ ×ˢ Icc (-δ) δ) := measure_mono hsub
    _ = volume (closedBall (Ω.proj c) ρ) * volume (Icc (-δ) δ) := Measure.prod_prod _ _
    _ = _ := by
        rw [Measure.addHaar_closedBall _ _ hρ, Real.volume_Icc, Ω.finrank_hyperplane_eq_sub_one,
          ENNReal.ofReal_pow hρ, sub_neg_eq_add, ← two_mul]
        ring

end Coordinates

end LipschitzGraph

/-! ### The boundary layer of a bounded Lipschitz domain -/

/-- `t (d 2^(-j))^(n-1) ≤ d^n 2^(-jn) min(1, 2^j t)` for `n ≥ 1`, `d ≥ 1` and
`0 ≤ t ≤ d 2^(-j)`: with `ρ = d 2^(-j)`, `ρ^n min(1, 2^j t) = ρ^(n-1) min(ρ, d t)`, and `t ≤ ρ`,
`t ≤ d t`. -/
theorem mul_div_two_pow_pow_sub_one_le {t d : ℝ} (ht : 0 ≤ t) (hd : 1 ≤ d) {j n : ℕ}
    (hn : 1 ≤ n) (htd : t ≤ d / 2 ^ j) :
    t * (d / 2 ^ j) ^ (n - 1) ≤ d ^ n * (1 / 2 ^ j) ^ n * min 1 (2 ^ j * t) := by
  have hρ : 0 < d / 2 ^ j := by positivity
  have e1 : d ^ n * (1 / 2 ^ j) ^ n = (d / 2 ^ j) ^ (n - 1) * (d / 2 ^ j) := by
    rw [pow_sub_one_mul (by omega), ← mul_pow, ← div_eq_mul_one_div]
  rw [e1, mul_assoc, mul_comm t]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [mul_min_of_nonneg _ _ hρ.le, mul_one]
  refine le_min htd ?_
  calc t = 1 * t := (one_mul t).symm
    _ ≤ d * t := mul_le_mul_of_nonneg_right hd ht
    _ = d / 2 ^ j * (2 ^ j * t) := by field_simp

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- In a boundary ball `B_i`, membership in `Ω` is membership in the graph domain `Ω_i`, since
`B_i ∩ Ω = B_i ∩ Ω_i`. -/
theorem mem_carrier_iff_of_mem_ball {i : Fin Ω.N} {x : V}
    (hx : x ∈ ball (Ω.center i) (Ω.radius i)) : x ∈ Ω.carrier ↔ x ∈ (Ω.graph i).domain := by
  simpa only [mem_inter_iff, hx, true_and] using Set.ext_iff.1 (Ω.ball_inter i) x

/-- **Short steps switch only near a chart graph**: if the shrunk balls `B(c_i, ρ_i - 2ε)` cover
the boundary and `‖h‖ ≤ ε`, every switch point `x` of `Ω` has `|η_i(x)| ≤ (1 + M_i) ‖h‖` for some
chart `i`. The step `[x, x + h]` contains a boundary point
(`Rd.exists_mem_frontier_of_mem_switchSet`), which lies in some `B(c_i, ρ_i - 2ε)`; so `x` and
`x + h` lie in `B_i`, where `Ω` is the graph domain `Ω_i`, and
`Rd.LipschitzGraph.abs_height_le_of_mem_switchSet` applies. -/
theorem switchSet_subset_iUnion {ε : ℝ}
    (hε : frontier Ω.carrier ⊆ ⋃ i, ball (Ω.center i) (Ω.radius i - 2 * ε)) {h : V}
    (hh : ‖h‖ ≤ ε) :
    switchSet Ω.carrier h ⊆ ⋃ i, {x | |(Ω.graph i).height x| ≤ (1 + (Ω.graph i).M) * ‖h‖} := by
  intro x hx
  obtain ⟨z, hzs, hzΓ⟩ := exists_mem_frontier_of_mem_switchSet hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hε hzΓ)
  rw [mem_ball] at hi
  have hd := dist_add_dist_of_mem_segment hzs
  have hxh : dist x (x + h) = ‖h‖ := by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
  rw [hxh] at hd
  have h0 := norm_nonneg h
  have h1 : x ∈ ball (Ω.center i) (Ω.radius i) := by
    rw [mem_ball]
    linarith [dist_triangle x z (Ω.center i), dist_nonneg (x := z) (y := x + h)]
  have h2 : x + h ∈ ball (Ω.center i) (Ω.radius i) := by
    rw [mem_ball]
    linarith [dist_triangle (x + h) z (Ω.center i), dist_comm z (x + h),
      dist_nonneg (x := x) (y := z)]
  have hsw : x ∈ switchSet (Ω.graph i).domain h := fun hiff => hx (by
    rw [Ω.mem_carrier_iff_of_mem_ball h1, Ω.mem_carrier_iff_of_mem_ball h2]
    exact hiff)
  exact mem_iUnion.2 ⟨i, (Ω.graph i).abs_height_le_of_mem_switchSet hsw⟩

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **The layer for short steps**: if the shrunk balls `B(c_i, ρ_i - 2ε)` cover the boundary,
`‖h‖ ≤ ε` and `ρ ≥ 0`, then `|S_h(Ω) ∩ B̄(c, ρ)| ≤ ∑_i 2 (1 + M_i) |B^{H_i}_1| · ‖h‖ ρ^(n-1)`, by
`Rd.BoundedLipschitzDomain.switchSet_subset_iUnion` and the slab volumes
`Rd.LipschitzGraph.volume_abs_height_le_inter_closedBall`. -/
theorem volume_switchSet_inter_closedBall_le_of_le {ε : ℝ}
    (hε : frontier Ω.carrier ⊆ ⋃ i, ball (Ω.center i) (Ω.radius i - 2 * ε)) {h : V}
    (hh : ‖h‖ ≤ ε) (c : V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (switchSet Ω.carrier h ∩ closedBall c ρ) ≤
      (∑ i, ENNReal.ofReal (2 * (1 + (Ω.graph i).M)) *
        volume (ball (0 : (Ω.graph i).hyperplane) 1)) *
        ENNReal.ofReal ‖h‖ * ENNReal.ofReal ρ ^ (finrank ℝ V - 1) := by
  set S : Fin Ω.N → Set V := fun i => {x | |(Ω.graph i).height x| ≤ (1 + (Ω.graph i).M) * ‖h‖}
  have hM : ∀ i, 0 ≤ 1 + (Ω.graph i).M := fun i => by linarith [(Ω.graph i).M_nonneg]
  calc volume (switchSet Ω.carrier h ∩ closedBall c ρ)
      ≤ volume (⋃ i, S i ∩ closedBall c ρ) := by
        rw [← iUnion_inter]
        exact measure_mono (inter_subset_inter_left _ (Ω.switchSet_subset_iUnion hε hh))
    _ ≤ ∑ i, volume (S i ∩ closedBall c ρ) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (2 * ((1 + (Ω.graph i).M) * ‖h‖)) *
          ENNReal.ofReal ρ ^ (finrank ℝ V - 1) * volume (ball (0 : (Ω.graph i).hyperplane) 1) :=
        Finset.sum_le_sum fun i _ => (Ω.graph i).volume_abs_height_le_inter_closedBall c hρ _
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show 2 * ((1 + (Ω.graph i).M) * ‖h‖) = 2 * (1 + (Ω.graph i).M) * ‖h‖ by ring,
          ENNReal.ofReal_mul (mul_nonneg zero_le_two (hM i))]
        ring

/-- **The boundary layer of a bounded Lipschitz domain**: there is `C < ∞` with
`|S_h(Ω) ∩ B̄(c, ρ)| ≤ C ‖h‖ ρ^(n-1)` for all `c, h ∈ V` and `ρ ≥ ‖h‖`. For short steps
`‖h‖ ≤ ε`, with `ε` from `Rd.BoundedLipschitzDomain.exists_shrink`, this is
`Rd.BoundedLipschitzDomain.volume_switchSet_inter_closedBall_le_of_le`; for long steps
`|S_h(Ω)| ≤ 2 |Ω|` (`Rd.volume_switchSet_le`) and `‖h‖ ρ^(n-1) ≥ ε^n`. -/
theorem exists_volume_switchSet_inter_closedBall_le :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (c h : V) (ρ : ℝ), ‖h‖ ≤ ρ →
      volume (switchSet Ω.carrier h ∩ closedBall c ρ) ≤
        C * ENNReal.ofReal ‖h‖ * ENNReal.ofReal ρ ^ (finrank ℝ V - 1) := by
  obtain ⟨ε, hε, hεΓ⟩ := Ω.exists_shrink
  set C₁ := ∑ i, ENNReal.ofReal (2 * (1 + (Ω.graph i).M)) *
    volume (ball (0 : (Ω.graph i).hyperplane) 1)
  set a := ENNReal.ofReal ε
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.2 hε).ne'
  have hai : a⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 ha0
  set C₂ := 2 * volume Ω.carrier * (a⁻¹ * a⁻¹ ^ (finrank ℝ V - 1))
  refine ⟨C₁ + C₂, ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) Ω.isBounded.measure_lt_top.ne)
      (ENNReal.mul_ne_top hai (ENNReal.pow_ne_top hai))⟩, fun c h ρ hhρ => ?_⟩
  rcases le_or_gt ‖h‖ ε with hh | hh
  · refine (Ω.volume_switchSet_inter_closedBall_le_of_le hεΓ hh c
      ((norm_nonneg h).trans hhρ)).trans ?_
    gcongr
    exact le_self_add
  · have hone : ∀ {t : ℝ}, ε ≤ t → 1 ≤ a⁻¹ * ENNReal.ofReal t := fun {t} ht =>
      calc (1 : ℝ≥0∞) = a⁻¹ * a := (ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top).symm
        _ ≤ a⁻¹ * ENNReal.ofReal t := by
          gcongr
          exact ENNReal.ofReal_le_ofReal ht
    have h1 := hone hh.le
    have h2 := hone (hh.le.trans hhρ)
    calc volume (switchSet Ω.carrier h ∩ closedBall c ρ)
        ≤ volume (switchSet Ω.carrier h) := measure_mono inter_subset_left
      _ ≤ 2 * volume Ω.carrier := volume_switchSet_le _ h
      _ = 2 * volume Ω.carrier * (1 * 1 ^ (finrank ℝ V - 1)) := by simp
      _ ≤ 2 * volume Ω.carrier * ((a⁻¹ * ENNReal.ofReal ‖h‖) *
            (a⁻¹ * ENNReal.ofReal ρ) ^ (finrank ℝ V - 1)) := by gcongr
      _ = C₂ * ENNReal.ofReal ‖h‖ * ENNReal.ofReal ρ ^ (finrank ℝ V - 1) := by
          rw [mul_pow]
          ring
      _ ≤ _ := by
          gcongr
          exact le_add_self

/-- **The boundary layer at the scale of an atom**: there is `C < ∞` with
`|S_h(Ω) ∩ B̄(c, d 2^(-j))| ≤ C d^n 2^(-jn) min(1, 2^j ‖h‖)` for all `c, h ∈ V`, `d ≥ 1` and
`j ∈ ℕ`. For `‖h‖ ≤ d 2^(-j)` this follows from
`Rd.BoundedLipschitzDomain.exists_volume_switchSet_inter_closedBall_le` and
`Rd.mul_div_two_pow_pow_sub_one_le` (for `h ≠ 0`, so `n ≥ 1`; for `h = 0` the switch set is
empty, `Rd.switchSet_zero`); for longer steps the ball has volume `d^n |B_1| 2^(-jn)`
(`Rd.volume_closedBall_div_two_pow`) and `min(1, 2^j ‖h‖) = 1`. -/
theorem exists_volume_switchSet_inter_closedBall_div_two_pow_le :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (c h : V) {d : ℝ}, 1 ≤ d → ∀ j : ℕ,
      volume (switchSet Ω.carrier h ∩ closedBall c (d / 2 ^ j)) ≤
        C * ENNReal.ofReal (d ^ finrank ℝ V) * dyadicWeight (-(finrank ℝ V : ℝ)) j *
          min 1 (ENNReal.ofReal (2 ^ j * ‖h‖)) := by
  obtain ⟨C, hC, hlayer⟩ := Ω.exists_volume_switchSet_inter_closedBall_le
  refine ⟨C + volume (ball (0 : V) 1), ENNReal.add_ne_top.2 ⟨hC, measure_ball_lt_top.ne⟩,
    fun c h d hd j => ?_⟩
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  rcases eq_or_ne h 0 with rfl | h0
  · rw [switchSet_zero, empty_inter, measure_empty]
    exact zero_le
  rcases le_or_gt ‖h‖ (d / 2 ^ j) with hh | hh
  · have hn : 1 ≤ finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.2 ⟨h, h0⟩
    have hr := mul_div_two_pow_pow_sub_one_le (norm_nonneg h) hd hn hh
    calc volume (switchSet Ω.carrier h ∩ closedBall c (d / 2 ^ j))
        ≤ C * ENNReal.ofReal ‖h‖ * ENNReal.ofReal (d / 2 ^ j) ^ (finrank ℝ V - 1) :=
          hlayer c h _ hh
      _ = C * ENNReal.ofReal (‖h‖ * (d / 2 ^ j) ^ (finrank ℝ V - 1)) := by
          rw [mul_assoc, ENNReal.ofReal_mul (norm_nonneg h), ENNReal.ofReal_pow (by positivity)]
      _ ≤ C * ENNReal.ofReal (d ^ finrank ℝ V * (1 / 2 ^ j) ^ finrank ℝ V *
            min 1 (2 ^ j * ‖h‖)) := by gcongr
      _ = C * ENNReal.ofReal (d ^ finrank ℝ V) * dyadicWeight (-(finrank ℝ V : ℝ)) j *
            min 1 (ENNReal.ofReal (2 ^ j * ‖h‖)) := by
          rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hd0 _) (by positivity)),
            ENNReal.ofReal_mul (pow_nonneg hd0 _), ENNReal.ofReal_one_div_two_pow_pow,
            ENNReal.ofReal_mono.map_min, ENNReal.ofReal_one]
          ring
      _ ≤ _ := by
          gcongr
          exact le_self_add
  · have hm : min 1 (ENNReal.ofReal (2 ^ j * ‖h‖)) = 1 := by
      refine min_eq_left ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_lt_iff₀ (by positivity), mul_comm] at hh
      linarith
    calc volume (switchSet Ω.carrier h ∩ closedBall c (d / 2 ^ j))
        ≤ volume (closedBall c (d / 2 ^ j)) := measure_mono inter_subset_right
      _ = ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1) *
            dyadicWeight (-(finrank ℝ V : ℝ)) j := volume_closedBall_div_two_pow hd0 j c
      _ ≤ _ := by
          rw [hm, mul_one, mul_comm (ENNReal.ofReal (d ^ finrank ℝ V))]
          gcongr
          exact le_add_self

end BoundedLipschitzDomain

end Rd
