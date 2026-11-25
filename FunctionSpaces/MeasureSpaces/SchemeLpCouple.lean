/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Lp.QuasiNorm
public import FunctionSpaces.MeasureSpaces.Scheme
public import ApproximationSpaces.Interpolation.EFunctionalSpaces

/-!
# The couple of a scheme of functions in `L_p`, `0 < p ≤ ∞`

Let `μ` be a finite measure on `Ω` and `S` a scheme of functions on `(Ω, μ)` (`FunctionScheme μ`):
an increasing sequence of sets `S_n` of essentially bounded functions with `S_0 = {0}`,
`c S_n ⊆ S_n` and `S_m + S_n ⊆ S_{m+n}`. Since `μ` is finite, every `S_n` lies in every
`L_p(μ)`, and one scheme measures errors in all `L_p` at once. Mathlib makes `Lp ℂ p μ` a normed
space for `p ≥ 1` only, and an `ApproximationScheme` lives in a normed space; this file describes
the image of `S` in `L_p(μ)` for every `p` through the complexity couple of `InterpCouple`, which
needs only the abelian group `Lp ℂ p μ` and the quasi-norm `‖·‖_p`.

* **The approximants in `L_p`.** The sets `S^(p)_n = ι_{∞,p}(S_n)` with the inclusion
  `ι_{∞,p} = MeasureTheory.Lp.topInclusion μ p` (`FunctionScheme.lpSets`) increase, start with
  `{0}` and satisfy `c S^(p)_n ⊆ S^(p)_n`, `-S^(p)_n ⊆ S^(p)_n` and
  `S^(p)_m + S^(p)_n ⊆ S^(p)_{m+n}` (`FunctionScheme.monotone_lpSets`, `FunctionScheme.lpSets_zero`,
  `FunctionScheme.smul_mem_lpSets`, `FunctionScheme.neg_mem_lpSets`,
  `FunctionScheme.lpSets_add_subset`); the inclusion `L_r ↪ L_p` maps `S^(r)_n` into `S^(p)_n`
  (`FunctionScheme.inclusion_mem_lpSets`).
* **The couple of `S` in `L_p`** (`FunctionScheme.lpCouple`) is the complexity couple of
  `N₀(f) = ‖f‖_p` and the sets `S^(p)_n`, with `N₁(f) = inf {n : f ∈ S^(p)_n}`, the least such
  `n`, and `∞` if `f` lies in no `S^(p)_n`. It is quasi-normed with Mathlib's constant
  `LpAddConst p` (`FunctionScheme.isQuasiNormed_lpCouple`), satisfies the `ρ`-triangle inequality
  `N₀(f + g)^ρ ≤ N₀(f)^ρ + N₀(g)^ρ` with `ρ = min(1, p)`
  (`FunctionScheme.lpCouple_norm0_add_rpow_le`), and is homogeneous: `N₀(c f) = |c| N₀(f)` and
  `N₁(c f) ≤ N₁(f)` (`FunctionScheme.lpCouple_norm0_smul`, `FunctionScheme.lpCouple_norm1_smul_le`).
  Only `0` has complexity below `1`, and `N₁(f) ≤ n` iff `f ∈ S^(p)_n`
  (`FunctionScheme.eq_zero_of_lpCouple_norm1_lt_one`, `FunctionScheme.lpCouple_norm1_le_of_mem`,
  `FunctionScheme.mem_lpSets_of_lpCouple_norm1_le`).
* **Errors of best approximation.** At a natural number `n` the E-functional of the couple is the
  error `E_n(f)_p = inf {‖f - a‖_p : a ∈ S_n}` (`FunctionScheme.eFunctional_lpCouple_natCast`),
  through `‖f - ι_{∞,p} a‖_t = ‖f - a‖_t` for every exponent `t`
  (`MeasureTheory.Lp.eLpNorm_sub_topInclusion`). Near-best approximants `b_k ∈ S_{2^k}` with
  `‖f - b_k‖_p ≤ E_{2^k}(f)_p + ‖f‖_p 2^(-k(s+1))` exist for every `p`
  (`FunctionScheme.exists_nearBest_lpCouple`). They take the role of bounded linear projections
  onto the approximants: for a non-atomic `μ` and `p < 1` the dual space of `L_p(μ)` is `{0}`, so
  every bounded linear projection of `L_p(μ)` with finite-dimensional range is `0`.
* **Different exponents.** The inclusion `L_r ↪ L_p`, `p ≤ r`, does not increase the complexity
  (`FunctionScheme.lpCouple_norm1_inclusion_le`).
* **The normed case.** For `p ≥ 1` the couple is the complexity couple of the approximation
  scheme `S^(p) = S.toLp p` in the normed space `L_p(μ)`
  (`FunctionScheme.lpCouple_eq_complexityCouple`), so its E-functional and Pietsch's form give
  the errors and the quasi-norms of the approximation spaces of that scheme.

The Besov spaces of `S` for every `0 < p ≤ ∞` are defined through this couple
(`FunctionSpaces.MeasureSpaces.Besov.Basic`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Pointwise
open ENNReal (dyadicWeight LpAddConst)

/-! ### Differences with essentially bounded functions -/

namespace MeasureTheory.Lp

variable {α E 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] {p : ℝ≥0∞}

/-- **The quasi-norms of a difference with an essentially bounded function**: for `f ∈ L_p` and
`a ∈ L_∞` on a finite measure space, `‖f - ι_{∞,p} a‖_t = ‖f - a‖_t` for every exponent `t`,
since `ι_{∞,p} a = a` almost everywhere. -/
theorem eLpNorm_sub_topInclusion (f : Lp E p μ) (a : Lp E ∞ μ) (t : ℝ≥0∞) :
    eLpNorm (⇑(f - topInclusion (𝕜 := 𝕜) μ p a)) t μ = eLpNorm (⇑f - ⇑a) t μ := by
  refine eLpNorm_congr_ae ?_
  filter_upwards [coeFn_sub f (topInclusion (𝕜 := 𝕜) μ p a),
    coeFn_topInclusion (𝕜 := 𝕜) (p := p) a] with x h1 h2
  rw [h1, Pi.sub_apply, Pi.sub_apply, h2]

end MeasureTheory.Lp

namespace FunctionScheme

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (S : FunctionScheme μ)

/-! ### The approximants in `L_p` -/

/-- The **approximants of a scheme of functions in `L_p`**: for a scheme `S` of essentially
bounded functions and every exponent `p`, the sets `S^(p)_n = ι_{∞,p}(S_n)` of the classes in
`L_p(μ)` of the elements of `S_n`. -/
def lpSets (p : ℝ≥0∞) (n : ℕ) : Set (Lp ℂ p μ) :=
  Lp.topInclusion (𝕜 := ℝ) μ p '' S n

variable {S} {p r : ℝ≥0∞}

/-- `f ∈ S^(p)_n` iff `f` is the class in `L_p` of some `a ∈ S_n`. -/
theorem mem_lpSets {n : ℕ} {f : Lp ℂ p μ} :
    f ∈ lpSets S p n ↔ ∃ a ∈ S n, Lp.topInclusion (𝕜 := ℝ) μ p a = f :=
  Iff.rfl

/-- The class in `L_p` of `a ∈ S_n` lies in `S^(p)_n`. -/
theorem topInclusion_mem_lpSets {n : ℕ} {a : Lp ℂ ∞ μ} (ha : a ∈ S n) :
    Lp.topInclusion (𝕜 := ℝ) μ p a ∈ lpSets S p n :=
  ⟨a, ha, rfl⟩

variable (S p) in
/-- The only approximant of complexity `0` in `L_p` is `0`: `S^(p)_0 = {0}`. -/
theorem lpSets_zero : lpSets S p 0 = {0} := by
  rw [lpSets, S.coe_zero, Set.image_singleton, map_zero]

variable (S p) in
/-- The approximants in `L_p` increase with the complexity: `S^(p)_m ⊆ S^(p)_n` for `m ≤ n`. -/
theorem monotone_lpSets : Monotone (lpSets S p) :=
  fun _ _ h => Set.image_mono (S.mono h)

/-- The approximants in `L_p` are closed under real multiples: `c S^(p)_n ⊆ S^(p)_n`. -/
theorem smul_mem_lpSets (c : ℝ) {n : ℕ} {f : Lp ℂ p μ} (hf : f ∈ lpSets S p n) :
    c • f ∈ lpSets S p n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨c • a, S.smul_mem c ha, map_smul _ c a⟩

/-- The approximants in `L_p` are symmetric: `-S^(p)_n ⊆ S^(p)_n`. -/
theorem neg_mem_lpSets {n : ℕ} {f : Lp ℂ p μ} (hf : f ∈ lpSets S p n) : -f ∈ lpSets S p n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨-a, ApproximationScheme.neg_mem ha, map_neg _ a⟩

variable (S p) in
/-- The sum of two approximants in `L_p` has at most the sum of their complexities:
`S^(p)_m + S^(p)_n ⊆ S^(p)_{m+n}`. -/
theorem lpSets_add_subset (m n : ℕ) : lpSets S p m + lpSets S p n ⊆ lpSets S p (m + n) := by
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  exact ⟨a + b, ApproximationScheme.add_mem ha hb, map_add _ a b⟩

/-- The inclusion `ι_{r,p} : L_r ↪ L_p`, `p ≤ r`, maps the approximants in `L_r` into those in
`L_p`: `ι_{r,p}(S^(r)_n) ⊆ S^(p)_n`, since `ι_{r,p} ∘ ι_{∞,r} = ι_{∞,p}`. -/
theorem inclusion_mem_lpSets (hpr : p ≤ r) {n : ℕ} {f : Lp ℂ r μ} (hf : f ∈ lpSets S r n) :
    Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr f ∈ lpSets S p n := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [Lp.inclusionOfExponentLeLinear_topInclusion]
  exact topInclusion_mem_lpSets ha

/-! ### The couple in `L_p` -/

variable (S p) in
/-- The **couple of a scheme of functions in `L_p`**, for every exponent `p`: the complexity
couple of the quasi-norm `N₀(f) = ‖f‖_p` and the approximants `S^(p)_n`, so
that `N₁(f) = inf {n : f ∈ S^(p)_n}`, the least such `n`, and `∞` if `f` lies in no `S^(p)_n`.
It needs only the group structure of `Lp ℂ p μ`, which exists also for `p < 1`. -/
noncomputable def lpCouple : InterpCouple (Lp ℂ p μ) :=
  InterpCouple.complexity (fun f => eLpNorm f p μ) (lpSets S p)

/-- The first norm of the couple in `L_p` is the quasi-norm `‖f‖_p`. -/
@[simp]
theorem lpCouple_norm0 (f : Lp ℂ p μ) : (lpCouple S p).norm0 f = eLpNorm f p μ :=
  rfl

/-- **The `ρ`-triangle inequality of the couple in `L_p`**: with `ρ = min(1, p)`,
`N₀(f + g)^ρ ≤ N₀(f)^ρ + N₀(g)^ρ` for every `p ≠ 0`
(`MeasureTheory.eLpNorm_add_rpow_min_le`). -/
theorem lpCouple_norm0_add_rpow_le (hp0 : p ≠ 0) (f g : Lp ℂ p μ) :
    (lpCouple S p).norm0 (f + g) ^ (min 1 p).toReal ≤
      (lpCouple S p).norm0 f ^ (min 1 p).toReal + (lpCouple S p).norm0 g ^ (min 1 p).toReal := by
  rw [lpCouple_norm0, lpCouple_norm0, lpCouple_norm0, eLpNorm_congr_ae (Lp.coeFn_add f g)]
  exact eLpNorm_add_rpow_min_le hp0 _ _

/-- **Homogeneity of the quasi-norm**: `N₀(c f) = |c| N₀(f)` for every real `c`. -/
theorem lpCouple_norm0_smul (c : ℝ) (f : Lp ℂ p μ) :
    (lpCouple S p).norm0 (c • f) = ‖c‖ₑ * (lpCouple S p).norm0 f := by
  rw [lpCouple_norm0, lpCouple_norm0, eLpNorm_congr_ae (Lp.coeFn_smul c f), eLpNorm_const_smul]

/-- An approximant of `S^(p)_n` has complexity at most `n`. -/
theorem lpCouple_norm1_le_of_mem {n : ℕ} {f : Lp ℂ p μ} (hf : f ∈ lpSets S p n) :
    (lpCouple S p).norm1 f ≤ n :=
  InterpCouple.complexity_norm1_le_of_mem hf

/-- An element of complexity at most `n` lies in `S^(p)_n`, since the sets increase. -/
theorem mem_lpSets_of_lpCouple_norm1_le {n : ℕ} {f : Lp ℂ p μ}
    (hf : (lpCouple S p).norm1 f ≤ n) : f ∈ lpSets S p n :=
  InterpCouple.mem_of_complexity_norm1_le (monotone_lpSets S p) hf

variable (S p) in
/-- The element `0` has complexity `0` in the couple in `L_p`. -/
theorem lpCouple_norm1_zero : (lpCouple S p).norm1 0 = 0 :=
  InterpCouple.complexity_norm1_zero (by rw [lpSets_zero]; exact Set.mem_singleton 0)

/-- The complexity is even: `N₁(-f) = N₁(f)`. -/
theorem lpCouple_norm1_neg (f : Lp ℂ p μ) : (lpCouple S p).norm1 (-f) = (lpCouple S p).norm1 f :=
  InterpCouple.complexity_norm1_neg (fun _ _ hb => neg_mem_lpSets hb) f

/-- The complexity is subadditive: `N₁(f + g) ≤ N₁(f) + N₁(g)`. -/
theorem lpCouple_norm1_add_le (f g : Lp ℂ p μ) :
    (lpCouple S p).norm1 (f + g) ≤ (lpCouple S p).norm1 f + (lpCouple S p).norm1 g :=
  InterpCouple.complexity_norm1_add_le (lpSets_add_subset S p) f g

/-- Real multiples do not increase the complexity: `N₁(c f) ≤ N₁(f)` for every real `c`. -/
theorem lpCouple_norm1_smul_le (c : ℝ) (f : Lp ℂ p μ) :
    (lpCouple S p).norm1 (c • f) ≤ (lpCouple S p).norm1 f :=
  InterpCouple.complexity_norm1_map_le (fun g => c • g) (fun _ _ hb => smul_mem_lpSets c hb) f

/-- Only `0` has complexity below `1` in the couple in `L_p`, since `S^(p)_0 = {0}`. -/
theorem eq_zero_of_lpCouple_norm1_lt_one {f : Lp ℂ p μ} (hf : (lpCouple S p).norm1 f < 1) :
    f = 0 :=
  InterpCouple.eq_zero_of_complexity_norm1_lt_one (lpSets_zero S p) hf

variable (S p) in
/-- **The couple in `L_p` is quasi-normed** with Mathlib's constant `C_p = LpAddConst p`
(`2^(1/p - 1)` for `0 < p < 1`, `1` otherwise), for every exponent `p`: the quasi-triangle
inequality `‖f + g‖_p ≤ C_p (‖f‖_p + ‖g‖_p)` is `eLpNorm_add_le'`, and the complexity is
subadditive, so its quasi-triangle inequality holds with `C_p ≥ 1`. -/
theorem isQuasiNormed_lpCouple : (lpCouple S p).IsQuasiNormed (LpAddConst p) where
  ne_top := (ENNReal.LpAddConst_lt_top p).ne
  norm0_zero := by
    rw [lpCouple_norm0, eLpNorm_congr_ae (Lp.coeFn_zero ℂ p μ), eLpNorm_zero]
  norm1_zero := lpCouple_norm1_zero S p
  norm0_neg f := by
    rw [lpCouple_norm0, lpCouple_norm0, eLpNorm_congr_ae (Lp.coeFn_neg f), eLpNorm_neg]
  norm1_neg := lpCouple_norm1_neg
  norm0_add_le f g := by
    rw [lpCouple_norm0, lpCouple_norm0, lpCouple_norm0, eLpNorm_congr_ae (Lp.coeFn_add f g)]
    exact eLpNorm_add_le' p
  norm1_add_le f g :=
    (lpCouple_norm1_add_le f g).trans (le_mul_of_one_le_left' (ENNReal.one_le_LpAddConst p))

/-! ### Errors of best approximation and near-best approximants -/

/-- **The E-functional of the couple in `L_p` at a natural number** is the error of best
approximation from `S_n` in `L_p`: `E(n, f) = inf {‖f - a‖_p : a ∈ S_n}`, the quasi-norm taken of
the difference of `f` and the essentially bounded function `a`. -/
theorem eFunctional_lpCouple_natCast (n : ℕ) (f : Lp ℂ p μ) :
    (lpCouple S p).eFunctional n f = ⨅ a ∈ S n, eLpNorm (⇑f - ⇑a) p μ := by
  rw [lpCouple, InterpCouple.eFunctional_complexity_natCast (monotone_lpSets S p), lpSets,
    iInf_image]
  exact iInf_congr fun a => iInf_congr fun _ => Lp.eLpNorm_sub_topInclusion f a p

/-- **Near-best approximants from the scheme**, for every exponent `p`: for every `f ∈ L_p` and
`s ∈ ℝ` there are `b_k ∈ S_{2^k}` with `‖f - b_k‖_p ≤ E(2^k, f) + ‖f‖_p 2^(-k(s+1))`, from the
near-best elements of the couple (`InterpCouple.exists_nearBest_eFunctional`) and a choice of
preimages in `S_{2^k}`. They take the role of bounded linear projections onto the approximants
(for a non-atomic `μ` and `p < 1`, the dual space of `L_p(μ)` is `{0}`). -/
theorem exists_nearBest_lpCouple (f : Lp ℂ p μ) (s : ℝ) :
    ∃ b : ℕ → Lp ℂ ∞ μ, (∀ k, b k ∈ S (2 ^ k)) ∧ ∀ k, eLpNorm (⇑f - ⇑(b k)) p μ ≤
      (lpCouple S p).eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) f +
        eLpNorm f p μ * dyadicWeight (-(s + 1)) k := by
  obtain ⟨b, hb1, hb0⟩ := InterpCouple.exists_nearBest_eFunctional (lpCouple_norm1_zero S p) f s
  choose a ha hab using fun k => mem_lpSets.1 (mem_lpSets_of_lpCouple_norm1_le (hb1 k))
  refine ⟨a, ha, fun k => ?_⟩
  rw [← Lp.eLpNorm_sub_topInclusion (𝕜 := ℝ) f (a k) p, hab k]
  exact hb0 k

/-! ### Different exponents and the normed case -/

/-- **The inclusion `L_r ↪ L_p` does not increase the complexity**: for `p ≤ r` and `f ∈ L_r`,
`N₁(ι_{r,p} f) ≤ N₁(f)` in the couples of `S` in `L_p` and in `L_r`, since `ι_{r,p}` maps
`S^(r)_n` into `S^(p)_n`. -/
theorem lpCouple_norm1_inclusion_le (hpr : p ≤ r) (f : Lp ℂ r μ) :
    (lpCouple S p).norm1 (Lp.inclusionOfExponentLeLinear (𝕜 := ℝ) μ hpr f) ≤
      (lpCouple S r).norm1 f :=
  InterpCouple.complexity_norm1_map_le _ (fun _ _ hb => inclusion_mem_lpSets hpr hb) f

/-- **For `p ≥ 1` the couple in `L_p` is a complexity couple of an approximation scheme**: the
couple of `S` in `L_p` is the complexity couple of the scheme `S^(p) = S.toLp p`, the image of
`S` in the normed space `L_p(μ)`. The sets agree by definition, and the first norms since
`‖f‖ₑ = ‖f‖_p` on `Lp` (`MeasureTheory.Lp.enorm_def`). -/
theorem lpCouple_eq_complexityCouple [Fact (1 ≤ p)] :
    lpCouple S p = (S.toLp p).complexityCouple := by
  have hN : (fun f : Lp ℂ p μ => eLpNorm f p μ) = fun f => ‖f‖ₑ :=
    funext fun f => (Lp.enorm_def f).symm
  rw [lpCouple, ApproximationScheme.complexityCouple, hN]
  rfl

end FunctionScheme
