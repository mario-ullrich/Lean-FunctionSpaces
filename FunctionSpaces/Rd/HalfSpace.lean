/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.DiffeoInvariance
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The half-space as a Besov domain

The closed half-space `{x : 0 ≤ ⟪x, e⟫}` for a unit vector `e` (`Rd.closedHalfSpace`) is a Besov
domain (`Rd.BesovDomain.closedHalfSpace`): it differs from the flat Lipschitz graph domain
`{x : 0 < ⟪x, e⟫}` (`Rd.LipschitzGraph.flat`) by the null set `e^⊥`, and on the latter Rychkov's
extension is bounded (`Rd.LipschitzGraph.modNorm_extension_le_modNormOn`).

Changing a set by a null set changes neither the step sets up to null sets (`Rd.stepSet_ae_eq`)
nor the moduli on the set (`Rd.modulusOn_congr_set`) nor the cut-off (`Rd.indicatorLp_congr_set`).

The models of manifolds are Besov domains: the range `{y : 0 ≤ y 0}` of the model with corners
of the Euclidean half-space (`Rd.BesovDomain.range_euclideanHalfSpace`), and the range `V` of a
model without boundary (`Rd.BesovDomain.range_of_boundaryless`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal NNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Changing the set by a null set -/

/-- **Step sets of almost equal sets are almost equal**: the translates by `l h` of almost equal
sets are almost equal, by the translation invariance of the Lebesgue measure. -/
theorem stepSet_ae_eq {U U' : Set V} (hUU' : U =ᵐ[volume] U') (r : ℕ) (h : V) :
    stepSet U r h =ᵐ[volume] stepSet U' r h := by
  have hl : ∀ l : ℕ, ∀ᵐ x ∂(volume : Measure V),
      (x + (l : ℝ) • h ∈ U) = (x + (l : ℝ) • h ∈ U') := fun l =>
    (measurePreserving_add_right volume ((l : ℝ) • h)).quasiMeasurePreserving.ae_eq_comp hUU'
  filter_upwards [ae_all_iff.2 hl] with x hx
  exact propext (forall₂_congr fun l _ => (hx l).to_iff)

/-- **The modulus on a set does not see null sets**: `ω_r(f, t, U)_p = ω_r(f, t, U')_p` if `U`
and `U'` agree up to a null set. -/
theorem modulusOn_congr_set {U U' : Set V} (hUU' : U =ᵐ[volume] U') (r : ℕ) (p : ℝ≥0∞)
    (f : V → ℂ) (t : ℝ) : modulusOn volume U r p f t = modulusOn volume U' r p f t := by
  simp only [modulusOn]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_congr_ae (indicator_ae_eq_of_ae_eq_set (stepSet_ae_eq hUU' r h))

/-- The dyadic moduli on almost equal sets agree. -/
theorem lpModulusOn_congr_set {p : ℝ≥0∞} {U U' : Set V} (hUU' : U =ᵐ[volume] U') (r : ℕ)
    (f : Lp ℂ p (volume : Measure V)) (k : ℕ) :
    lpModulusOn p U r f k = lpModulusOn p U' r f k :=
  modulusOn_congr_set hUU' r p _ _

/-- The cut-offs to almost equal sets agree. -/
theorem indicatorLp_congr_set {p : ℝ≥0∞} [Fact (1 ≤ p)] {U U' : Set V} (hU : MeasurableSet U)
    (hU' : MeasurableSet U') (hUU' : U =ᵐ[volume] U') (f : Lp ℂ p (volume : Measure V)) :
    indicatorLp hU f = indicatorLp hU' f := by
  refine Lp.ext ?_
  filter_upwards [indicatorLp_apply_ae hU f, indicatorLp_apply_ae hU' f,
    indicator_ae_eq_of_ae_eq_set (f := (f : V → ℂ)) hUU'] with x h1 h2 h3
  rw [h1, h2, h3]

/-! ### The half-space -/

/-- The **closed half-space** `{x : 0 ≤ ⟪x, e⟫}`. -/
def closedHalfSpace (e : V) : Set V := {x | 0 ≤ inner ℝ x e}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The closed half-space is closed. -/
theorem isClosed_closedHalfSpace (e : V) : IsClosed (closedHalfSpace e) :=
  isClosed_le continuous_const (continuous_id.inner continuous_const)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The closed half-space is convex. -/
theorem convex_closedHalfSpace (e : V) : Convex ℝ (closedHalfSpace e) := by
  intro x hx y hy a b ha hb _
  show 0 ≤ inner ℝ (a • x + b • y) e
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A nonzero `e` lies in the interior of its closed half-space. -/
theorem mem_interior_closedHalfSpace {e : V} (he : e ≠ 0) : e ∈ interior (closedHalfSpace e) := by
  refine mem_interior.2 ⟨{x | 0 < inner ℝ x e}, fun x (hx : 0 < inner ℝ x e) => hx.le,
    isOpen_lt continuous_const (continuous_id.inner continuous_const), ?_⟩
  show 0 < inner ℝ e e
  rw [real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.2 he) 2

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The **flat Lipschitz graph domain**: the open half-space `{x : 0 < ⟪x, e⟫}` for a unit
vector `e`, with graph function `0`. -/
def LipschitzGraph.flat (e : V) (he : ‖e‖ = 1) : LipschitzGraph V where
  e := e
  norm_e := he
  M := 0
  M_nonneg := le_rfl
  phi := 0
  lipschitz _ _ := by simp
  const _ _ := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The flat domain is the open half-space. -/
theorem LipschitzGraph.flat_domain (e : V) (he : ‖e‖ = 1) :
    (LipschitzGraph.flat e he).domain = {x | 0 < inner ℝ x e} := rfl

/-- **The closed half-space is the open one up to a null set**: they differ by the hyperplane
`e^⊥`, a proper subspace. -/
theorem closedHalfSpace_ae_eq {e : V} (he : ‖e‖ = 1) :
    closedHalfSpace e =ᵐ[volume] (LipschitzGraph.flat e he).domain := by
  have he0 : e ≠ 0 := fun h => by simp [h] at he
  have hnull : volume ((ℝ ∙ e)ᗮ : Set V) = 0 := by
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    have hmem : e ∈ (ℝ ∙ e)ᗮ := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq, he] at hmem
    norm_num at hmem
  refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => ?_) hnull, ?_⟩
  · have h1 : 0 ≤ inner ℝ x e := hx.1
    have h2 : ¬ 0 < inner ℝ x e := hx.2
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact le_antisymm (not_lt.1 h2) h1
  · have hsub : (LipschitzGraph.flat e he).domain ⊆ closedHalfSpace e :=
      fun x (hx : 0 < inner ℝ x e) => hx.le
    rw [sdiff_eq_empty.2 hsub, measure_empty]

/-- **The closed half-space is a Besov domain**: a function of finite intrinsic Besov quasi-norm
on it extends by Rychkov's extension of the flat graph domain, since the open and the closed
half-space differ by a null set. -/
theorem BesovDomain.closedHalfSpace {e : V} (he : ‖e‖ = 1) : BesovDomain (closedHalfSpace e) where
  convex := convex_closedHalfSpace e
  isClosed := isClosed_closedHalfSpace e
  interior_nonempty := ⟨e, mem_interior_closedHalfSpace fun h => by simp [h] at he⟩
  exists_extension p _ hp r s hs hsr q hq := by
    set Ω := LipschitzGraph.flat e he
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 fun h => by
      rw [h, Nat.cast_zero] at hsr
      exact lt_irrefl _ (hs.trans hsr)
    have hae := closedHalfSpace_ae_eq he
    have hC := (isClosed_closedHalfSpace e).measurableSet
    have hcut : ∀ g : Lp ℂ p (volume : Measure V), indicatorLp hC g = Ω.cutoff g := fun g =>
      indicatorLp_congr_set hC Ω.measurableSet_domain hae g
    have hmod : ∀ (g : Lp ℂ p (volume : Measure V)) k,
        lpModulusOn p (Rd.closedHalfSpace e) r g k = lpModulusOn p Ω.domain r g k :=
      fun g k => lpModulusOn_congr_set hae r g k
    refine ⟨Ω.coneBump.synthConst r s * Ω.intrinsicConst r, ENNReal.mul_ne_top
      (Ω.coneBump.synthConst_ne_top hs hsr) (Ω.intrinsicConst_ne_top r), fun f hf => ?_⟩
    simp_rw [hcut, hmod] at hf ⊢
    exact ⟨Ω.extension hp r f, Ω.cutoff_extension_of_modNormOn hp hr hs hq hf,
      Ω.modNorm_extension_le_modNormOn hp r hs hq hf⟩

/-! ### The models of manifolds -/

/-- **The Euclidean half-space model is a Besov domain**: the range of the model with corners
`𝓡∂ n` is the closed half-space `{y : 0 ≤ y 0}`. -/
instance BesovDomain.range_euclideanHalfSpace (n : ℕ) [NeZero n] :
    BesovDomain (Set.range (modelWithCornersEuclideanHalfSpace n)) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  have h : {y : EuclideanSpace ℝ (Fin n) | 0 ≤ y 0} =
      Rd.closedHalfSpace (EuclideanSpace.single 0 1) := by
    ext y
    simp [Rd.closedHalfSpace, EuclideanSpace.inner_single_right]
  rw [h]
  exact BesovDomain.closedHalfSpace (by simp)

/-- **A model without boundary is a Besov domain**: its range is the whole space. -/
instance BesovDomain.range_of_boundaryless {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ V H) [I.Boundaryless] : BesovDomain (Set.range I) := by
  rw [I.range_eq_univ]
  infer_instance

end Rd
