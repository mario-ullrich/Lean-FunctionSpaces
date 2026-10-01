/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Scheme
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The error of best approximation

For an approximation scheme `A` in a normed space `X`, the **error of best approximation** of
`f ∈ X` from `A n` is

`E_n(f) = dist(f, A n) = inf { ‖f - a‖ : a ∈ A n }`,

in Lean `A.approxError n f`, defined as `Metric.infDist f (A n)`.  This file collects its
calculus: `E_0(f) = ‖f‖`, `E_n(f) ≤ ‖f‖`, `E_n` decreases in `n`, `E_n(c f) = |c| E_n(f)`,
`E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`, `E_n` is `1`-Lipschitz in `f`, `E_n(f) → 0` exactly for
`f` in the closure of `⋃ A n`, and a bounded linear map `T` with `T (A n) ⊆ B n` satisfies
`E^B_n(T f) ≤ ‖T‖ E^A_n(f)`.

A best approximant need not exist, since the sets `A n` need not be closed (sets of `n`-term
approximants are not).  Proofs therefore pick approximants `a ∈ A n` with
`‖f - a‖ ≤ E_n(f) + ε` (`ApproximationScheme.exists_mem_norm_sub_le_add`) and let `ε → 0`.
-/

@[expose] public section

open Filter Topology

namespace ApproximationScheme

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (A : ApproximationScheme X)

/-- The **error of best approximation** `E_n(f) = dist(f, A n)` of `f` from the approximants
of complexity `n`. -/
noncomputable def approxError (n : ℕ) (f : X) : ℝ := Metric.infDist f (A n)

variable {A}

/-- `E_n(f) ≥ 0`. -/
theorem approxError_nonneg (n : ℕ) (f : X) : 0 ≤ A.approxError n f := Metric.infDist_nonneg

/-- Every approximant gives an upper bound for the error. -/
theorem approxError_le_norm_sub {n : ℕ} {a : X} (ha : a ∈ A n) (f : X) :
    A.approxError n f ≤ ‖f - a‖ := by
  rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem ha

/-- The error never exceeds the norm, since `0` is an approximant. -/
theorem approxError_le_norm (n : ℕ) (f : X) : A.approxError n f ≤ ‖f‖ := by
  simpa using approxError_le_norm_sub (A.zero_mem n) f

/-- `E_n(0) = 0`. -/
@[simp]
theorem approxError_zero_right (n : ℕ) : A.approxError n 0 = 0 :=
  Metric.infDist_zero_of_mem (A.zero_mem n)

/-- `E_0(f) = ‖f‖`, because `A 0 = {0}`. -/
@[simp]
theorem approxError_zero_left (f : X) : A.approxError 0 f = ‖f‖ := by
  simp [approxError, A.coe_zero, Metric.infDist_singleton]

/-- `E_n(f) = 0` for `f ∈ A_n`. -/
theorem approxError_eq_zero_of_mem {n : ℕ} {f : X} (hf : f ∈ A n) : A.approxError n f = 0 :=
  Metric.infDist_zero_of_mem hf

/-- `E_n(f) = 0` for `f` in the closure of `A_n`. -/
theorem approxError_eq_zero_of_mem_closure {n : ℕ} {f : X} (hf : f ∈ closure (A n)) :
    A.approxError n f = 0 :=
  Metric.infDist_zero_of_mem_closure hf

/-- The error decreases as the complexity grows. -/
theorem approxError_anti (f : X) : Antitone (A.approxError · f) := fun _ _ h =>
  Metric.infDist_le_infDist_of_subset (A.mono h) (A.nonempty _)

/-- A scheme with larger sets has smaller errors. -/
theorem approxError_anti_scheme {A' : ApproximationScheme X} (h : ∀ n, A n ⊆ A' n) (n : ℕ)
    (f : X) : A'.approxError n f ≤ A.approxError n f :=
  Metric.infDist_le_infDist_of_subset (h n) (A.nonempty n)

/-- `r ≤ E_n(f)` iff `r ≤ ‖f - a‖` for every `a ∈ A_n`. -/
theorem le_approxError_iff {n : ℕ} {f : X} {r : ℝ} :
    r ≤ A.approxError n f ↔ ∀ a ∈ A n, r ≤ ‖f - a‖ := by
  simp only [approxError, Metric.le_infDist (A.nonempty n), dist_eq_norm]

/-- If the error is below `r`, some approximant is closer than `r`. -/
theorem exists_mem_norm_sub_lt {n : ℕ} {f : X} {r : ℝ} (h : A.approxError n f < r) :
    ∃ a ∈ A n, ‖f - a‖ < r := by
  simpa [dist_eq_norm] using (Metric.infDist_lt_iff (A.nonempty n)).1 h

/-- **Near-best approximants.** For every `ε > 0` there is `a ∈ A n` with
`‖f - a‖ ≤ E_n(f) + ε`.  A best approximant (`ε = 0`) need not exist. -/
theorem exists_mem_norm_sub_le_add (n : ℕ) (f : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A n, ‖f - a‖ ≤ A.approxError n f + ε := by
  obtain ⟨a, ha, h⟩ := exists_mem_norm_sub_lt (lt_add_of_pos_right (A.approxError n f) hε)
  exact ⟨a, ha, h.le⟩

/-- To bound a quantity by `C · E_n(f)` it suffices to bound it by `C ‖f - a‖` for every
approximant `a`. -/
theorem le_mul_approxError_of_forall_mem {n : ℕ} {f : X} {e C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a ∈ A n, e ≤ C * ‖f - a‖) : e ≤ C * A.approxError n f := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨a, ha, hfa⟩ := exists_mem_norm_sub_le_add n f (div_pos hε hC1)
  calc e ≤ C * ‖f - a‖ := h a ha
    _ ≤ C * (A.approxError n f + ε / (C + 1)) := by gcongr
    _ = C * A.approxError n f + C * ε / (C + 1) := by ring
    _ ≤ C * A.approxError n f + ε := by
      gcongr
      rw [div_le_iff₀ hC1]; nlinarith

/-- **Subadditivity**: `E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`, because `A m + A n ⊆ A (m + n)`. -/
theorem approxError_add_le (m n : ℕ) (f g : X) :
    A.approxError (m + n) (f + g) ≤ A.approxError m f + A.approxError n g := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, hfa⟩ := exists_mem_norm_sub_le_add m f (half_pos hε)
  obtain ⟨b, hb, hgb⟩ := exists_mem_norm_sub_le_add n g (half_pos hε)
  calc A.approxError (m + n) (f + g) ≤ ‖f + g - (a + b)‖ :=
        approxError_le_norm_sub (add_mem ha hb) _
    _ = ‖(f - a) + (g - b)‖ := by rw [add_sub_add_comm]
    _ ≤ ‖f - a‖ + ‖g - b‖ := norm_add_le _ _
    _ ≤ A.approxError m f + A.approxError n g + ε := by linarith

/-- The dyadic form of subadditivity: `E_{2^(k+1)}(f + g) ≤ E_{2^k}(f) + E_{2^k}(g)`. -/
theorem approxError_add_le_pow_succ (k : ℕ) (f g : X) :
    A.approxError (2 ^ (k + 1)) (f + g) ≤ A.approxError (2 ^ k) f + A.approxError (2 ^ k) g := by
  have := approxError_add_le (A := A) (2 ^ k) (2 ^ k) f g
  rwa [← two_mul, ← pow_succ'] at this

/-- **Homogeneity**: `E_n(c f) = |c| E_n(f)`, because `c • A n = A n` for `c ≠ 0`. -/
theorem approxError_smul (n : ℕ) (c : ℝ) (f : X) :
    A.approxError n (c • f) = |c| * A.approxError n f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have := infDist_smul₀ hc (A n) f
    rw [A.smul_set_eq hc n, Real.norm_eq_abs] at this
    exact this

/-- `E_n(-f) = E_n(f)`. -/
@[simp]
theorem approxError_neg (n : ℕ) (f : X) : A.approxError n (-f) = A.approxError n f := by
  simpa using approxError_smul (A := A) n (-1) f

/-- `E_n(f) ≤ E_n(g) + ‖f - g‖`. -/
theorem approxError_le_approxError_add_norm (n : ℕ) (f g : X) :
    A.approxError n f ≤ A.approxError n g + ‖f - g‖ := by
  rw [← dist_eq_norm]; exact Metric.infDist_le_infDist_add_dist

/-- The error is `1`-Lipschitz in `f`. -/
theorem abs_approxError_sub_le (n : ℕ) (f g : X) :
    |A.approxError n f - A.approxError n g| ≤ ‖f - g‖ := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [approxError_le_approxError_add_norm (A := A) n f g]
  · linarith [approxError_le_approxError_add_norm (A := A) n g f, norm_sub_rev f g]

/-- `E_n` is continuous, being `1`-Lipschitz. -/
theorem continuous_approxError (n : ℕ) : Continuous (A.approxError n) :=
  Metric.continuous_infDist_pt _

/-- The errors tend to zero exactly for the elements of the closure of `⋃ n, A n`. -/
theorem tendsto_approxError_zero_iff (f : X) :
    Tendsto (A.approxError · f) atTop (𝓝 0) ↔ f ∈ closure (⋃ n, A n) := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 h) ε hε
    have hn' := hn n le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (approxError_nonneg n f)] at hn'
    obtain ⟨a, ha, hfa⟩ := exists_mem_norm_sub_lt hn'
    exact ⟨a, Set.mem_iUnion.2 ⟨n, ha⟩, by rwa [dist_eq_norm]⟩
  · intro h
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨a, ha, hfa⟩ := h ε hε
    obtain ⟨m, ha⟩ := Set.mem_iUnion.1 ha
    refine ⟨m, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (approxError_nonneg n f)]
    calc A.approxError n f ≤ A.approxError m f := approxError_anti f hn
      _ ≤ ‖f - a‖ := approxError_le_norm_sub ha f
      _ < ε := by rwa [← dist_eq_norm]

/-- Since the errors decrease, they tend to zero as soon as the dyadic errors `E_{2^k}` do. -/
theorem tendsto_approxError_zero_of_pow {f : X}
    (h : Tendsto (fun k => A.approxError (2 ^ k) f) atTop (𝓝 0)) :
    Tendsto (A.approxError · f) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 h) ε hε
  refine ⟨2 ^ K, fun n hn => ?_⟩
  have hK' := hK K le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (approxError_nonneg _ f)] at hK' ⊢
  exact (approxError_anti f hn).trans_lt hK'

/-- **Functoriality of the error**: a bounded linear map that sends approximants to
approximants satisfies `E^B_n(T f) ≤ ‖T‖ E^A_n(f)`. -/
theorem approxError_map_le (T : X →L[ℝ] Y) (B : ApproximationScheme Y)
    (hT : ∀ n, ∀ a ∈ A n, T a ∈ B n) (n : ℕ) (f : X) :
    B.approxError n (T f) ≤ ‖T‖ * A.approxError n f := by
  refine le_mul_approxError_of_forall_mem (norm_nonneg T) fun a ha => ?_
  calc B.approxError n (T f) ≤ ‖T f - T a‖ := approxError_le_norm_sub (hT n a ha) _
    _ = ‖T (f - a)‖ := by rw [map_sub]
    _ ≤ ‖T‖ * ‖f - a‖ := T.le_opNorm _

end ApproximationScheme
