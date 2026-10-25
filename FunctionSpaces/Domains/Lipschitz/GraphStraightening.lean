/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Lipschitz.LipschitzGraph
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Flattening a graph domain

For a Lipschitz graph domain `Ω = {x : φ(x) < ⟪x, e⟫}` the **flattening**
`F(x) = x - φ(x) e` (`Rd.LipschitzGraph.flatten`) maps `Ω` onto the half-space `{⟪y, e⟫ > 0}`
(`Rd.LipschitzGraph.inner_flatten`): it is a bijection of `V` with inverse `y ↦ y + φ(y) e`
(`Rd.LipschitzGraph.unflatten`), because `φ` is constant along `e`. The inverse is
`(1 + M)`-Lipschitz (`Rd.LipschitzGraph.lipschitzWith_unflatten`), and the image of the hyperplane
`e^⊥` under it contains the graph (`Rd.LipschitzGraph.graph_subset_image_unflatten`). For smooth
`φ` both maps are smooth, and the flattening preserves the Lebesgue measure
(`Rd.LipschitzGraph.measurePreserving_flatten`): its derivative `id - e ⊗ Dφ(x)` is a
transvection, since `Dφ(x) e = 0`, so its determinant is `1` (Mathlib's
`LinearMap.transvection.det`), and the change of variables formula
(`map_withDensity_abs_det_fderiv_eq_addHaar`) applies.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace Rd

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-- The **flattening** `x ↦ x - φ(x) e`. -/
def flatten (x : V) : V := x - Ω.phi x • Ω.e

/-- The inverse of the flattening, `y ↦ y + φ(y) e`. -/
def unflatten (y : V) : V := y + Ω.phi y • Ω.e

/-- `φ` is constant along `e`, also backwards: `φ(x - t e) = φ(x)`. -/
theorem phi_sub_smul (x : V) (t : ℝ) : Ω.phi (x - t • Ω.e) = Ω.phi x := by
  rw [sub_eq_add_neg, ← neg_smul, Ω.const]

/-- The inverse undoes the flattening. -/
theorem unflatten_flatten (x : V) : Ω.unflatten (Ω.flatten x) = x := by
  rw [unflatten, flatten, Ω.phi_sub_smul, sub_add_cancel]

/-- The flattening undoes the inverse. -/
theorem flatten_unflatten (y : V) : Ω.flatten (Ω.unflatten y) = y := by
  rw [flatten, unflatten, Ω.const, add_sub_cancel_right]

/-- **The flattening lowers the height by the graph**: `⟪F(x), e⟫ = ⟪x, e⟫ - φ(x)`. -/
theorem inner_flatten (x : V) : inner ℝ (Ω.flatten x) Ω.e = inner ℝ x Ω.e - Ω.phi x := by
  rw [flatten, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, Ω.norm_e]
  ring

/-- The flattening is a bijection of `V`. -/
noncomputable def flattenEquiv : V ≃ V where
  toFun := Ω.flatten
  invFun := Ω.unflatten
  left_inv := Ω.unflatten_flatten
  right_inv := Ω.flatten_unflatten

/-- The flattening is continuous. -/
theorem continuous_flatten : Continuous Ω.flatten :=
  continuous_id.sub (Ω.continuous_phi.smul continuous_const)

/-- The inverse of the flattening is continuous. -/
theorem continuous_unflatten : Continuous Ω.unflatten :=
  continuous_id.add (Ω.continuous_phi.smul continuous_const)

/-- **The inverse flattening is Lipschitz**: `y ↦ y + φ(y) e` is `(1 + M)`-Lipschitz, since `φ`
is `M`-Lipschitz and `‖e‖ = 1`. On the hyperplane `e^⊥` this is
`Rd.LipschitzGraph.norm_graphMap_sub_le`. -/
theorem lipschitzWith_unflatten :
    LipschitzWith ⟨1 + Ω.M, add_nonneg zero_le_one Ω.M_nonneg⟩ Ω.unflatten := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  show _ ≤ (1 + Ω.M) * _
  calc ‖Ω.unflatten x - Ω.unflatten y‖ = ‖(x - y) + (Ω.phi x - Ω.phi y) • Ω.e‖ := by
        rw [unflatten, unflatten, sub_smul]
        congr 1
        abel
    _ ≤ ‖x - y‖ + |Ω.phi x - Ω.phi y| := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs]
    _ ≤ (1 + Ω.M) * ‖x - y‖ := by linarith [Ω.lipschitz x y]

/-- **The graph lies in the image of the hyperplane** `e^⊥` under `y ↦ y + φ(y) e`: a point `x`
of the graph is the image of its flattening `x - φ(x) e`, which lies in `e^⊥`
(`Rd.LipschitzGraph.inner_flatten`). -/
theorem graph_subset_image_unflatten :
    {x | Ω.phi x = inner ℝ x Ω.e} ⊆ Ω.unflatten '' ((ℝ ∙ Ω.e)ᗮ : Set V) := by
  intro x (hx : Ω.phi x = inner ℝ x Ω.e)
  refine ⟨Ω.flatten x, ?_, Ω.unflatten_flatten x⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm,
    Ω.inner_flatten, hx, sub_self]

/-- For smooth `φ`, the flattening is smooth. -/
theorem contDiff_flatten {n : WithTop ℕ∞} (hφ : ContDiff ℝ n Ω.phi) : ContDiff ℝ n Ω.flatten :=
  contDiff_id.sub (hφ.smul contDiff_const)

/-- For smooth `φ`, the inverse of the flattening is smooth. -/
theorem contDiff_unflatten {n : WithTop ℕ∞} (hφ : ContDiff ℝ n Ω.phi) :
    ContDiff ℝ n Ω.unflatten :=
  contDiff_id.add (hφ.smul contDiff_const)

/-- **`φ` does not change along `e`**: `Dφ(x) e = 0`. -/
theorem fderiv_phi_e {x : V} (hφ : DifferentiableAt ℝ Ω.phi x) : fderiv ℝ Ω.phi x Ω.e = 0 := by
  rw [← hφ.lineDeriv_eq_fderiv, lineDeriv]
  simp only [Ω.const, deriv_const]

/-- The derivative of the flattening, `id - e ⊗ Dφ(x)`. -/
theorem hasFDerivAt_flatten {x : V} (hφ : DifferentiableAt ℝ Ω.phi x) :
    HasFDerivAt Ω.flatten (ContinuousLinearMap.id ℝ V - (fderiv ℝ Ω.phi x).smulRight Ω.e) x :=
  (hasFDerivAt_id x).sub (hφ.hasFDerivAt.smul_const Ω.e)

/-- **The derivative of the flattening has determinant `1`**: it is the transvection
`y ↦ y + (-Dφ(x) y) e` with `Dφ(x) e = 0`. -/
theorem det_fderiv_flatten [FiniteDimensional ℝ V] {x : V} (hφ : DifferentiableAt ℝ Ω.phi x) :
    (ContinuousLinearMap.id ℝ V - (fderiv ℝ Ω.phi x).smulRight Ω.e).det = 1 := by
  have h : ((ContinuousLinearMap.id ℝ V - (fderiv ℝ Ω.phi x).smulRight Ω.e : V →L[ℝ] V) :
      V →ₗ[ℝ] V) = LinearMap.transvection (-(fderiv ℝ Ω.phi x : V →ₗ[ℝ] ℝ)) Ω.e := by
    ext y
    simp [LinearMap.transvection, sub_eq_add_neg]
  rw [ContinuousLinearMap.det, h, LinearMap.transvection.det]
  simp [Ω.fderiv_phi_e hφ]

/-- **The flattening preserves the Lebesgue measure** for `C^1` graph functions. -/
theorem measurePreserving_flatten [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (hφ : ContDiff ℝ 1 Ω.phi) : MeasurePreserving Ω.flatten volume volume := by
  have hdiff : Differentiable ℝ Ω.phi := hφ.differentiable one_ne_zero
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure V)
    (s := univ) nullMeasurableSet_univ
    (fun x _ => (Ω.hasFDerivAt_flatten (hdiff x)).hasFDerivWithinAt)
    (Ω.flattenEquiv.injective.injOn)
  have hdet : (fun x => ENNReal.ofReal |(ContinuousLinearMap.id ℝ V -
      (fderiv ℝ Ω.phi x).smulRight Ω.e).det|) = fun _ => 1 := funext fun x => by
    rw [Ω.det_fderiv_flatten (hdiff x), abs_one, ENNReal.ofReal_one]
  have hsurj : Ω.flatten '' univ = univ :=
    image_univ_of_surjective (f := Ω.flatten) Ω.flattenEquiv.surjective
  rw [hdet, Measure.restrict_univ, withDensity_const, one_smul, hsurj,
    Measure.restrict_univ] at hmap
  exact ⟨(Ω.contDiff_flatten hφ).continuous.measurable, hmap⟩

end LipschitzGraph

end Rd
