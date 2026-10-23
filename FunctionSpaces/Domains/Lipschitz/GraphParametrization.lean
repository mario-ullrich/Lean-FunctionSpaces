/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Atoms.AtomAnalysis
public import FunctionSpaces.Domains.Lipschitz.LipschitzGraph

/-!
# The boundary of a Lipschitz graph domain as a graph over a hyperplane

For a Lipschitz graph domain `Ω = {x : φ(x) < ⟪x, e⟫}` (`Rd.LipschitzGraph`), the boundary is the
graph of `φ` over the hyperplane `H = e^⊥` (`Rd.LipschitzGraph.hyperplane`), of dimension `n - 1`
(`Rd.LipschitzGraph.finrank_hyperplane_add_one`), with `H^⊥ = ℝ e`
(`Rd.LipschitzGraph.orthogonal_hyperplane`) and the Lebesgue measure of its inner product.
The **graph map** `γ(x') = x' + φ(x') e` (`Rd.LipschitzGraph.graphMap`) satisfies `P(γ x') = x'`
for the orthogonal projection `Px = x - ⟪x, e⟫ e` onto `H` (`Rd.LipschitzGraph.proj`), and it is
Lipschitz with constant `1 + M` (`Rd.LipschitzGraph.norm_graphMap_sub_le`).

**Traces of atoms** (`Rd.LipschitzGraph.isRegularAtom_comp_graphMap`): a continuous `a` on `V`
that vanishes outside `B̄(c, d 2^(-j))`, with `|a| ≤ A` and `|a(x + h) - a(x)| ≤ A min(1, 2^j ‖h‖)`,
restricts to `a ∘ γ`, which vanishes outside `B̄(Pc, d 2^(-j))` in `H`, with `|a ∘ γ| ≤ A` and
`|a ∘ γ(x' + h') - a ∘ γ(x')| ≤ (1 + M) A min(1, 2^j ‖h'‖)`: a regular atom of order and exponent
`1` on `H`, as in the proof of Schneider–Vybíral, Theorem 4.2. Only sup bounds enter.
-/

@[expose] public section

open MeasureTheory Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-- `min(1, K t) ≤ K min(1, t)` for `K ≥ 1`. -/
theorem min_one_mul_le {K : ℝ≥0∞} (hK : 1 ≤ K) (t : ℝ≥0∞) : min 1 (K * t) ≤ K * min 1 t := by
  rcases le_total t 1 with ht | ht
  · rw [min_eq_right ht]
    exact min_le_right _ _
  · rw [min_eq_left ht, mul_one]
    exact (min_le_left _ _).trans hK

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-! ### The hyperplane and the graph map -/

/-- The **hyperplane** `H = e^⊥` over which the boundary of `Ω` is a graph. -/
noncomputable abbrev hyperplane : Submodule ℝ V := (ℝ ∙ Ω.e)ᗮ

/-- The orthogonal complement of the hyperplane is the line `ℝ e` (Mathlib's
`Submodule.orthogonal_orthogonal`). -/
theorem orthogonal_hyperplane : Ω.hyperplaneᗮ = ℝ ∙ Ω.e := Submodule.orthogonal_orthogonal _

/-- The upward direction is nonzero. -/
theorem e_ne_zero : Ω.e ≠ 0 := fun h => by simpa [h] using Ω.norm_e

/-- `⟪e, e⟫ = 1`. -/
theorem inner_e_self : inner ℝ Ω.e Ω.e = 1 := by
  rw [real_inner_self_eq_norm_sq, Ω.norm_e, one_pow]

/-- The points of `H` are orthogonal to `e`. -/
theorem inner_coe_e (x' : Ω.hyperplane) : inner ℝ (x' : V) Ω.e = 0 := by
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 x'.2

/-- `x - ⟪x, e⟫ e ∈ H`. -/
theorem sub_inner_smul_mem (x : V) : x - inner ℝ x Ω.e • Ω.e ∈ Ω.hyperplane := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right,
    Ω.inner_e_self, mul_one, real_inner_comm, sub_self]

/-- `H` has dimension `n - 1`. -/
theorem finrank_hyperplane_add_one [FiniteDimensional ℝ V] :
    finrank ℝ Ω.hyperplane + 1 = finrank ℝ V := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ Ω.e)
  rw [finrank_span_singleton Ω.e_ne_zero] at h
  show finrank ℝ ↥(ℝ ∙ Ω.e)ᗮ + 1 = finrank ℝ V
  omega

/-- `dim H = n - 1`, with the subtraction of natural numbers. -/
theorem finrank_hyperplane_eq_sub_one [FiniteDimensional ℝ V] :
    finrank ℝ Ω.hyperplane = finrank ℝ V - 1 := by
  have h := Ω.finrank_hyperplane_add_one
  omega

/-- The **orthogonal projection** onto `H`. -/
noncomputable def proj : V →L[ℝ] Ω.hyperplane := Ω.hyperplane.orthogonalProjectionOnto

/-- `Px = x - ⟪x, e⟫ e`. -/
theorem coe_proj (x : V) : (Ω.proj x : V) = x - inner ℝ x Ω.e • Ω.e := by
  rw [proj, Submodule.coe_orthogonalProjectionOnto_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Ω.sub_inner_smul_mem x)
    fun w hw => ?_
  rw [sub_sub_cancel, real_inner_smul_left,
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 hw, mul_zero]

/-- For `a ∈ H`, `⟪a, v⟫ = ⟪a, Pv⟫`: Mathlib's
`Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left`. -/
theorem inner_coe_eq_inner_proj (a : Ω.hyperplane) (v : V) :
    inner ℝ (a : V) v = inner ℝ a (Ω.proj v) :=
  (Ω.hyperplane.inner_orthogonalProjectionOnto_eq_of_mem_left a v).symm

/-- `‖Px‖ ≤ ‖x‖`. -/
theorem norm_proj_le (x : V) : ‖Ω.proj x‖ ≤ ‖x‖ :=
  Submodule.norm_orthogonalProjectionOnto_apply_le _ x

/-- `P x' = x'` on `H`. -/
theorem proj_coe (x' : Ω.hyperplane) : Ω.proj x' = x' :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x'

/-- `P e = 0`. -/
theorem proj_e : Ω.proj Ω.e = 0 := by
  apply Subtype.ext
  rw [coe_proj, Ω.inner_e_self, one_smul, sub_self]
  rfl

/-- The **graph map** `γ(x') = x' + φ(x') e`. -/
noncomputable def graphMap (x' : Ω.hyperplane) : V := (x' : V) + Ω.phi x' • Ω.e

/-- `P(γ x') = x'`. -/
theorem proj_graphMap (x' : Ω.hyperplane) : Ω.proj (Ω.graphMap x') = x' := by
  rw [graphMap, map_add, map_smul, Ω.proj_e, smul_zero, add_zero, Ω.proj_coe]

/-- `⟪γ x', e⟫ = φ(x')`: the graph map lands on the boundary. -/
theorem inner_graphMap (x' : Ω.hyperplane) : inner ℝ (Ω.graphMap x') Ω.e = Ω.phi x' := by
  rw [graphMap, inner_add_left, Ω.inner_coe_e, real_inner_smul_left, Ω.inner_e_self, mul_one,
    zero_add]

/-- `φ(γ x') = φ(x')`. -/
theorem phi_graphMap (x' : Ω.hyperplane) : Ω.phi (Ω.graphMap x') = Ω.phi x' :=
  Ω.const _ _

/-- **The graph map is Lipschitz**: `‖γ x' - γ y'‖ ≤ (1 + M) ‖x' - y'‖`. -/
theorem norm_graphMap_sub_le (x' y' : Ω.hyperplane) :
    ‖Ω.graphMap x' - Ω.graphMap y'‖ ≤ (1 + Ω.M) * ‖x' - y'‖ := by
  have hsub : Ω.graphMap x' - Ω.graphMap y' =
      ((x' - y' : Ω.hyperplane) : V) + (Ω.phi x' - Ω.phi y') • Ω.e := by
    simp only [graphMap, Submodule.coe_sub, sub_smul]
    abel
  have hlip : |Ω.phi x' - Ω.phi y'| ≤ Ω.M * ‖x' - y'‖ := by
    have h := Ω.lipschitz x' y'
    rwa [← Submodule.coe_sub, Submodule.norm_coe] at h
  rw [hsub]
  calc ‖((x' - y' : Ω.hyperplane) : V) + (Ω.phi x' - Ω.phi y') • Ω.e‖
      ≤ ‖((x' - y' : Ω.hyperplane) : V)‖ + ‖(Ω.phi x' - Ω.phi y') • Ω.e‖ := norm_add_le _ _
    _ = ‖x' - y'‖ + |Ω.phi x' - Ω.phi y'| := by
        rw [norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs, Submodule.norm_coe]
    _ ≤ ‖x' - y'‖ + Ω.M * ‖x' - y'‖ := add_le_add le_rfl hlip
    _ = (1 + Ω.M) * ‖x' - y'‖ := by ring

/-- The graph map is continuous. -/
theorem continuous_graphMap : Continuous Ω.graphMap :=
  continuous_subtype_val.add ((Ω.continuous_phi.comp continuous_subtype_val).smul continuous_const)

/-- **Steps into the cone from the boundary stay in the domain**: `γ x' + K ⊆ Ω`, since
`φ(γ x') = ⟪γ x', e⟫` and a step `y` into the cone raises `⟪·, e⟫` faster than `φ`. -/
theorem graphMap_add_mem (x' : Ω.hyperplane) {y : V} (hy : y ∈ Ω.cone) :
    Ω.graphMap x' + y ∈ Ω.domain := by
  set d := y - inner ℝ y Ω.e • Ω.e
  have h1 : Ω.phi (Ω.graphMap x' + y) = Ω.phi (Ω.graphMap x' + d) := by
    rw [← Ω.const (Ω.graphMap x' + d) (inner ℝ y Ω.e)]
    congr 1
    simp only [d]
    abel
  have h2 : Ω.phi (Ω.graphMap x' + d) ≤ Ω.phi (Ω.graphMap x') + Ω.M * ‖d‖ := by
    have h := Ω.lipschitz (Ω.graphMap x' + d) (Ω.graphMap x')
    rw [add_sub_cancel_left] at h
    linarith [le_abs_self (Ω.phi (Ω.graphMap x' + d) - Ω.phi (Ω.graphMap x'))]
  have hy' : Ω.M * ‖d‖ < inner ℝ y Ω.e := hy
  rw [Ω.phi_graphMap] at h2
  show Ω.phi (Ω.graphMap x' + y) < inner ℝ (Ω.graphMap x' + y) Ω.e
  rw [inner_add_left, h1, Ω.inner_graphMap]
  linarith

/-- `‖x' - Pc‖ ≤ ‖γ x' - c‖`: the projection is a contraction. -/
theorem norm_sub_proj_le (x' : Ω.hyperplane) (c : V) : ‖x' - Ω.proj c‖ ≤ ‖Ω.graphMap x' - c‖ := by
  calc ‖x' - Ω.proj c‖ = ‖Ω.proj (Ω.graphMap x' - c)‖ := by rw [map_sub, Ω.proj_graphMap]
    _ ≤ ‖Ω.graphMap x' - c‖ := Ω.norm_proj_le _

/-! ### Traces of atoms -/

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Traces of atoms** (as in the proof of Schneider–Vybíral, Theorem 4.2): if `a` is continuous,
vanishes outside `B̄(c, d 2^(-j))`, `|a| ≤ A` and `|a(x + h) - a(x)| ≤ A min(1, 2^j ‖h‖)`, then
`a ∘ γ` is a regular atom of order and exponent `1` on `H` with centre `Pc`, radius factor `d` and
constant `(1 + M) A (2 d^(n-1) |B_1|)^(1/p)`, since `γ` is Lipschitz with constant `1 + M`. -/
theorem isRegularAtom_comp_graphMap {p : ℝ≥0∞} {d : ℝ} (hd : 0 ≤ d) {A : ℝ≥0∞} {j : ℕ} {c : V}
    {a : V → ℂ} (hac : Continuous a) (h0 : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0)
    (hle : ∀ x, ‖a x‖ₑ ≤ A)
    (hdiff : ∀ h x, ‖a (x + h) - a x‖ₑ ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖))) :
    IsRegularAtom p 1 1 d (ENNReal.ofReal (1 + Ω.M) * A * (((1 + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (d ^ finrank ℝ Ω.hyperplane) * volume (ball (0 : Ω.hyperplane) 1))) ^
        (1 / p.toReal)) j (Ω.proj c) (a ∘ Ω.graphMap) := by
  have hK : 1 ≤ ENNReal.ofReal (1 + Ω.M) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Ω.M_nonneg])
  refine isRegularAtom_of_pointwise hd (hac.comp Ω.continuous_graphMap).aestronglyMeasurable
    (fun x' hx' => ?_) (fun x' => ?_) (fun h' x' => ?_)
  · exact h0 _ (hx'.trans_le (Ω.norm_sub_proj_le x' c))
  · exact (hle _).trans (le_mul_of_one_le_left' hK)
  · simp only [Function.iterate_one, fwdDiff, Function.comp_apply, ENNReal.rpow_one]
    set v := Ω.graphMap (x' + h') - Ω.graphMap x'
    have hv : ‖v‖ ≤ (1 + Ω.M) * ‖h'‖ := by
      have h := Ω.norm_graphMap_sub_le (x' + h') x'
      rwa [add_sub_cancel_left] at h
    have h1 := hdiff v (Ω.graphMap x')
    rw [add_sub_cancel] at h1
    have h2 : 2 ^ j * ‖v‖ ≤ (1 + Ω.M) * (2 ^ j * ‖h'‖) := by
      calc 2 ^ j * ‖v‖ ≤ 2 ^ j * ((1 + Ω.M) * ‖h'‖) :=
            mul_le_mul_of_nonneg_left hv (by positivity)
        _ = (1 + Ω.M) * (2 ^ j * ‖h'‖) := by ring
    calc ‖a (Ω.graphMap (x' + h')) - a (Ω.graphMap x')‖ₑ
        ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖v‖)) := h1
      _ ≤ A * min 1 (ENNReal.ofReal (1 + Ω.M) * ENNReal.ofReal (2 ^ j * ‖h'‖)) := by
          gcongr
          rw [← ENNReal.ofReal_mul (by linarith [Ω.M_nonneg])]
          exact ENNReal.ofReal_le_ofReal h2
      _ ≤ A * (ENNReal.ofReal (1 + Ω.M) * min 1 (ENNReal.ofReal (2 ^ j * ‖h'‖))) :=
          mul_le_mul' le_rfl (min_one_mul_le hK _)
      _ = ENNReal.ofReal (1 + Ω.M) * A * min 1 (ENNReal.ofReal (2 ^ j * ‖h'‖)) := by ring

end LipschitzGraph

end Rd
