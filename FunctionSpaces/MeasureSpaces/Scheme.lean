/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Scheme
public import FunctionSpaces.Analysis.Lp.BoundedContinuous
public import Mathlib.Analysis.Complex.Basic

/-!
# Approximation schemes of functions

A **scheme of functions** on a measure space `(Ω, μ)` is an approximation scheme in the Banach
space `L_∞(μ)` of essentially bounded complex functions (`FunctionScheme μ`): an increasing
sequence of sets `S_n` of classes in `L_∞(μ)` with `S_0 = {0}`, `c S_n ⊆ S_n` and
`S_m + S_n ⊆ S_{m+n}`. Examples: trigonometric polynomials of degree `< n` on the torus,
algebraic polynomials on a compact set, splines, the `ℱ_k`-measurable functions of a filtration
`(ℱ_k)` (step functions for the dyadic filtration), Haar functions, eigenfunctions of a
Laplacian.

For a finite measure `μ`, every essentially bounded function lies in `L_p(μ)` for every `p`, and
for `1 ≤ p ≤ ∞` the scheme is sent into the normed space `L_p(μ)` by the inclusion
`ι_{∞,p} : L_∞ ↪ L_p` (`MeasureTheory.Lp.topInclusion`, `FunctionScheme.toLp`). One scheme thus
yields a scheme in every `L_p(μ)`, and these are compatible with the inclusions `L_r ↪ L_p`: the
inclusion maps the scheme in `L_r` onto the scheme in `L_p` (`image_toLp_of_le`), and the
preimage of the scheme in `L_p` is the scheme in `L_r` (`comap_toLp_of_le`). These two facts
are the only input the transfer theorems need.

**Schemes of bounded continuous functions.** On a topological space `Ω` with its Borel
`σ`-algebra, an approximation scheme `T` of bounded continuous functions gives a scheme of
functions through the classes of its elements (`FunctionScheme.ofContinuous`); its scheme in
`L_p` consists of the `L_p` classes of the elements of `T` (`FunctionScheme.toLp_ofContinuous`).
A scheme of functions has **continuous approximants** if every approximant is the class of a
bounded continuous function (`FunctionScheme.HasContinuousApproximants`), as the scheme of `T`
has. Continuity matters only where a theorem concludes that a function has a continuous
representative; boundedness costs nothing, since a Nikolskii inequality makes approximants
bounded anyway.
-/

@[expose] public section

open MeasureTheory
open scoped BoundedContinuousFunction
open scoped ENNReal

/-- A **scheme of functions** on a measure space `(Ω, μ)`: an approximation scheme of
essentially bounded complex functions, that is, of classes in `L_∞(μ)`. -/
abbrev FunctionScheme {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :=
  ApproximationScheme (Lp ℂ ∞ μ)

namespace FunctionScheme

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (S : FunctionScheme μ)

/-- The scheme `S^(p)` in `L_p(μ)`, `1 ≤ p ≤ ∞`: the images `ι_{∞,p}(S n)` of the sets of `S`
under the inclusion `ι_{∞,p} : L_∞ ↪ L_p`. -/
noncomputable def toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] : ApproximationScheme (Lp ℂ p μ) :=
  S.map (Lp.topInclusion (𝕜 := ℝ) μ p)

variable {S} {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- `g ∈ S^(p)_n` iff `g` is the class in `L_p` of some `a ∈ S_n`. -/
theorem mem_toLp {n : ℕ} {g : Lp ℂ p μ} :
    g ∈ S.toLp p n ↔ ∃ a ∈ S n, Lp.topInclusion (𝕜 := ℝ) μ p a = g :=
  Iff.rfl

/-- The class in `L_p` of `a ∈ S_n` lies in `S^(p)_n`. -/
theorem toLp_mem_toLp {n : ℕ} {a : Lp ℂ ∞ μ} (ha : a ∈ S n) :
    Lp.topInclusion (𝕜 := ℝ) μ p a ∈ S.toLp p n :=
  ⟨a, ha, rfl⟩

/-- The inclusion `L_r ↪ L_p` maps the scheme in `L_r` into the scheme in `L_p`. -/
theorem inclusion_mem_toLp (hpr : p ≤ r) {n : ℕ} {g : Lp ℂ r μ} (hg : g ∈ S.toLp r n) :
    Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g ∈ S.toLp p n := by
  obtain ⟨a, ha, rfl⟩ := hg
  rw [Lp.inclusionOfExponentLe_apply, Lp.inclusionOfExponentLeLinear_topInclusion]
  exact toLp_mem_toLp ha

/-- The inclusion `L_r ↪ L_p` maps the scheme in `L_r` onto the scheme in `L_p`. -/
theorem image_toLp_of_le (hpr : p ≤ r) (n : ℕ) :
    Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr '' S.toLp r n = S.toLp p n := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩; exact inclusion_mem_toLp hpr hg'
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, toLp_mem_toLp ha, Lp.inclusionOfExponentLeLinear_topInclusion hpr a⟩

/-- An `L_r` function whose `L_p` class is an approximant is itself an approximant. -/
theorem mem_toLp_of_inclusion_mem (hpr : p ≤ r) {n : ℕ} {g : Lp ℂ r μ}
    (hg : Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g ∈ S.toLp p n) : g ∈ S.toLp r n := by
  obtain ⟨a, ha, h⟩ := hg
  have : g = Lp.topInclusion (𝕜 := ℝ) μ r a :=
    Lp.inclusionOfExponentLe_injective (𝕜 := ℝ) hpr
      (h.symm.trans (Lp.inclusionOfExponentLeLinear_topInclusion hpr a).symm)
  exact this ▸ toLp_mem_toLp ha

/-- The preimage of the scheme in `L_p` under `L_r ↪ L_p` is the scheme in `L_r`. -/
theorem comap_toLp_of_le (hpr : p ≤ r) :
    (S.toLp p).comap (Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr).toLinearMap
      (Lp.inclusionOfExponentLe_injective hpr) = S.toLp r := by
  ext n g
  exact ⟨mem_toLp_of_inclusion_mem hpr, inclusion_mem_toLp hpr⟩

/-- Every approximant of the scheme in `L_p` is the inclusion of one in `L_r`. -/
theorem exists_toLp_of_mem (hpr : p ≤ r) {n : ℕ} {g : Lp ℂ p μ} (hg : g ∈ S.toLp p n) :
    ∃ g' ∈ S.toLp r n, Lp.inclusionOfExponentLe (𝕜 := ℝ) μ hpr g' = g := by
  rw [← image_toLp_of_le hpr] at hg
  exact hg

/-! ### Schemes of bounded continuous functions -/

section Continuous

variable [TopologicalSpace Ω] [BorelSpace Ω]

/-- The **scheme of functions of a scheme of bounded continuous functions** `T`: the classes in
`L_∞(μ)` of the elements of `T_n`. -/
noncomputable def ofContinuous (T : ApproximationScheme (Ω →ᵇ ℂ)) (μ : Measure Ω)
    [IsFiniteMeasure μ] : FunctionScheme μ :=
  T.map (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ).toLinearMap

/-- `a ∈ L_∞(μ)` is an approximant of complexity `n` of the scheme of `T` iff it is the class
of some `g ∈ T_n`. -/
theorem mem_ofContinuous {T : ApproximationScheme (Ω →ᵇ ℂ)} {n : ℕ} {a : Lp ℂ ∞ μ} :
    a ∈ ofContinuous T μ n ↔ ∃ g ∈ T n, BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ g = a :=
  Iff.rfl

/-- **The scheme of `T` in `L_p`**: for `1 ≤ p ≤ ∞`, the approximants of `(ofContinuous T μ)^(p)`
are the `L_p` classes of the elements of `T`. -/
theorem toLp_ofContinuous (T : ApproximationScheme (Ω →ᵇ ℂ)) :
    (ofContinuous T μ).toLp p =
      T.map (BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ).toLinearMap := by
  ext n g
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (BoundedContinuousFunction.inclusionOfExponentLeLinear_toLp le_top a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, BoundedContinuousFunction.inclusionOfExponentLeLinear_toLp le_top a⟩

/-- `g ∈ L_p(μ)` is an approximant of complexity `n` of the scheme of `T` in `L_p` iff it is the
`L_p` class of some element of `T_n`. -/
theorem mem_toLp_ofContinuous {T : ApproximationScheme (Ω →ᵇ ℂ)} {n : ℕ} {g : Lp ℂ p μ} :
    g ∈ (ofContinuous T μ).toLp p n ↔
      ∃ a ∈ T n, BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ a = g := by
  rw [toLp_ofContinuous]
  rfl

/-- The `L_p` class of an element `a ∈ T_n` lies in the scheme of `T` in `L_p`. -/
theorem toLp_mem_toLp_ofContinuous {T : ApproximationScheme (Ω →ᵇ ℂ)} {n : ℕ} {a : Ω →ᵇ ℂ}
    (ha : a ∈ T n) :
    BoundedContinuousFunction.toLp (E := ℂ) p μ ℝ a ∈ (ofContinuous T μ).toLp p n :=
  mem_toLp_ofContinuous.2 ⟨a, ha, rfl⟩

/-- A scheme of functions has **continuous approximants** if every element of every `S_n` is
the class of a bounded continuous function. The range of `BoundedContinuousFunction.toLp` is
Mathlib's subgroup `MeasureTheory.Lp.boundedContinuousFunction ℂ ∞ μ`
(`BoundedContinuousFunction.range_toLp`); the range form fits the closedness of this set,
`BoundedContinuousFunction.isClosed_range_toLp_top`. -/
def HasContinuousApproximants (S : FunctionScheme μ) : Prop :=
  ∀ n, S n ⊆ Set.range (BoundedContinuousFunction.toLp (E := ℂ) ∞ μ ℝ : (Ω →ᵇ ℂ) → Lp ℂ ∞ μ)

/-- The scheme of a scheme of bounded continuous functions has continuous approximants. -/
theorem hasContinuousApproximants_ofContinuous (T : ApproximationScheme (Ω →ᵇ ℂ)) :
    (ofContinuous T μ).HasContinuousApproximants := by
  rintro n _ ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩

end Continuous

end FunctionScheme
