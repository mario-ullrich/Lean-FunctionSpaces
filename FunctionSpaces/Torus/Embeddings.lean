/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.Sobolev

/-!
# Embedding theorems on the torus

The general embedding theorems of `FunctionSpaces.MeasureSpaces.Besov.Embeddings` and
`FunctionSpaces.MeasureSpaces.Sobolev.Embeddings`, applied to the scheme of trigonometric
polynomials on `𝕋^d`, which has the Nikolskii property of dimension `d`
(`Torus.trigScheme_hasNikolskii`):

* **Besov embedding** (`Torus.memBesov_exists_inclusion_eq`): for `0 < p ≤ r ≤ ∞`,
  `0 < q ≤ ∞` and `s > d(1/p - 1/r)`, `B^s_{p,q}(𝕋^d) ⊆ B^{s - d(1/p - 1/r)}_{r,q}(𝕋^d)`;
* **into continuous functions** (`Torus.memBesov_exists_continuous`): for `0 < p ≤ ∞`,
  `0 < q ≤ ∞` and `s > d/p`, every `f ∈ B^s_{p,q}(𝕋^d)` has a continuous representative;
* **Sobolev embedding** (`Torus.sobolev_exists_continuous`): for `s > d/2`, every
  `f ∈ L_2(𝕋^d)` with `∑_k (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞` has a continuous
  representative;
* **`H^s` and Besov spaces** (`Torus.periodic_sobolev_memBesov_top`,
  `Torus.periodic_exists_sobolev_of_memBesov`): `H^s(𝕋^d) ⊆ B^s_{2,∞}(𝕋^d)` and
  `B^t_{2,q}(𝕋^d) ⊆ H^s(𝕋^d)` for `t > s` and `0 < q ≤ ∞`; and `H^s(𝕋^d) ⊆ L_r(𝕋^d)` with
  `B^{s - d(1/2 - 1/r)}_{r,∞}` smoothness for `2 ≤ r` and `s > d(1/2 - 1/r)`
  (`Torus.sobolev_exists_inclusion_eq`).

The torus measure is Mathlib's normalised Haar measure, available as `volume` after
`open scoped TorusHaar`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus FunctionScheme
open scoped ENNReal BoundedContinuousFunction TorusHaar lp

namespace Torus

variable {d : Type*} [Fintype d] {p r : ℝ≥0∞} [Fact (1 ≤ r)] {s : ℝ} {q : ℝ≥0∞}

/-- A bounded continuous function on the compact torus is a continuous function, with the same
`L_∞` class. -/
theorem toLp_toContinuousMap (a : UnitAddTorus d →ᵇ ℂ) :
    ContinuousMap.toLp (E := ℂ) ∞ volume ℝ a.toContinuousMap =
      BoundedContinuousFunction.toLp (E := ℂ) ∞ volume ℝ a := by
  rw [ContinuousMap.toLp_def]
  congr 1

omit [Fact (1 ≤ r)] in
/-- **The Besov embedding on the torus**: for `0 < p ≤ r ≤ ∞`, `0 < q ≤ ∞` and
`s > d(1/p - 1/r)`, every `f ∈ B^s_{p,q}(𝕋^d)` lies in `L_r` and in
`B^{s - d(1/p - 1/r)}_{r,q}(𝕋^d)`: the Besov embedding of a scheme
(`FunctionScheme.MemBesov.exists_inclusion_eq_of_nikolskii`) for the trigonometric polynomials,
which have the Nikolskii property of dimension `d` (`Torus.trigScheme_hasNikolskii`). -/
theorem memBesov_exists_inclusion_eq (hp0 : p ≠ 0) (hpr : p ≤ r)
    (hs : (Fintype.card d : ℝ) * (p.toReal⁻¹ - r.toReal⁻¹) < s) (hq0 : q ≠ 0)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : (trigScheme d).MemBesov p s q f) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) volume hpr g = f ∧
        (trigScheme d).MemBesov r (s - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) q g :=
  MemBesov.exists_inclusion_eq_of_nikolskii (trigScheme_hasNikolskii.hasNikolskiiAt hp0)
    (Nat.cast_nonneg _) hp0 hpr hs hq0 hf

/-- **Besov functions are continuous** for `s > d/p`, `0 < p ≤ ∞` and `0 < q ≤ ∞`: every
`f ∈ B^s_{p,q}(𝕋^d)` has a continuous representative. The trigonometric polynomials have
continuous approximants (`FunctionScheme.hasContinuousApproximants_ofContinuous`) and the
Nikolskii property of dimension `d` (`Torus.trigScheme_hasNikolskii`), so
`FunctionScheme.MemBesov.exists_boundedContinuous_of_nikolskii` applies. -/
theorem memBesov_exists_continuous (hp0 : p ≠ 0) (hs : (Fintype.card d : ℝ) * p.toReal⁻¹ < s)
    (hq0 : q ≠ 0) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : (trigScheme d).MemBesov p s q f) :
    ∃ g : C(UnitAddTorus d, ℂ),
      Lp.topInclusion (𝕜 := ℝ) volume p (ContinuousMap.toLp (E := ℂ) ∞ volume ℝ g) = f := by
  obtain ⟨a, ha⟩ :=
    MemBesov.exists_boundedContinuous_of_nikolskii (hasContinuousApproximants_ofContinuous _)
      (trigScheme_hasNikolskii.hasNikolskiiAt hp0) (Nat.cast_nonneg _) hp0 hs hq0 hf
  exact ⟨a.toContinuousMap, by rw [toLp_toContinuousMap, ha]⟩

/-- **`H^s(𝕋^d) ⊆ B^s_{2,∞}(𝕋^d)`**, from Jackson's inequality. -/
theorem periodic_sobolev_memBesov_top (hs : 0 < s) (c : ℓ²(d → ℤ, ℂ)) :
    (trigScheme d).MemBesov 2 s ∞ ((periodicSobolevSpace s hs).incl c) :=
  FunctionScheme.memBesov_iff_memApprox.2 ((periodicSobolevSpace s hs).memApprox_top c)

/-- **`B^t_{2,q}(𝕋^d) ⊆ H^s(𝕋^d)` for `t > s > 0` and `0 < q ≤ ∞`**, from Bernstein's
inequality: `B^t_{2,q}(𝕋^d) ⊆ B^t_{2,∞}(𝕋^d)` (`FunctionScheme.MemBesov.mono`), which is the
approximation space `A^t_∞` of the trigonometric polynomials in `L_2(𝕋^d)`
(`FunctionScheme.memBesov_iff_memApprox`), and this space lies in `H^s(𝕋^d)` for `t > s`
(`ApproximationScheme.SmoothnessSpace.exists_eq_of_lt`). -/
theorem periodic_exists_sobolev_of_memBesov (hs : 0 < s) {t : ℝ} (hst : s < t) (hq0 : q ≠ 0)
    {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))} (hf : (trigScheme d).MemBesov 2 t q f) :
    ∃ c : ℓ²(d → ℤ, ℂ), (periodicSobolevSpace s hs).incl c = f :=
  (periodicSobolevSpace s hs).exists_eq_of_lt hst le_top (FunctionScheme.memBesov_iff_memApprox.1
    (hf.mono hq0 (hs.trans hst).le (Or.inr ⟨rfl, le_top⟩)))

/-- **The Sobolev embedding into `L_r`** on the torus: for `2 ≤ r ≤ ∞` and
`s > d(1/2 - 1/r)`, every element of `H^s(𝕋^d)` lies in `L_r` and in
`B^{s - d(1/2 - 1/r)}_{r,∞}(𝕋^d)`. -/
theorem sobolev_exists_inclusion_eq (h2r : (2 : ℝ≥0∞) ≤ r) (hs : 0 < s)
    (hsr : (Fintype.card d : ℝ) * ((2 : ℝ≥0∞).toReal⁻¹ - r.toReal⁻¹) < s) (c : ℓ²(d → ℤ, ℂ)) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume h2r g = (periodicSobolevSpace s hs).incl c ∧
        (trigScheme d).MemBesov r
          (s - Fintype.card d * ((2 : ℝ≥0∞).toReal⁻¹ - r.toReal⁻¹)) ∞ g := by
  obtain ⟨g, hg, hmem⟩ := memBesov_exists_inclusion_eq two_ne_zero h2r hsr ENNReal.top_ne_zero
    (periodic_sobolev_memBesov_top hs c)
  exact ⟨g, (Lp.inclusionOfExponentLe_apply (𝕜 := ℝ) h2r g).trans hg, hmem⟩

/-- **The Sobolev embedding into continuous functions** on the torus: for `s > d/2`, every
`f ∈ L_2(𝕋^d)` with `∑_k (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞` has a continuous
representative. -/
theorem sobolev_exists_continuous (hs : (Fintype.card d : ℝ) / 2 < s)
    {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hf : Memℓp (fun k => ((((1 + trigDeg k : ℕ) : ℝ) ^ s : ℝ) : ℂ) * mFourierCoeff f k) 2) :
    ∃ g : C(UnitAddTorus d, ℂ),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume le_top (ContinuousMap.toLp (E := ℂ) ∞ volume ℝ g) =
        f := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  obtain ⟨c, rfl⟩ := (periodic_mem_range_sobolev_iff s hs0 f).2 hf
  have hs' : (Fintype.card d : ℝ) * (2 : ℝ≥0∞).toReal⁻¹ <
      (periodicSobolevSpace (d := d) s hs0).order := by
    simpa [div_eq_mul_inv] using hs
  obtain ⟨a, ha⟩ := SobolevSpace.exists_boundedContinuous
    (hasContinuousApproximants_ofContinuous _) trigScheme_hasNikolskii (Nat.cast_nonneg _)
    (periodicSobolevSpace s hs0) hs' c
  exact ⟨a.toContinuousMap, by rw [toLp_toContinuousMap, ha]⟩

end Torus
