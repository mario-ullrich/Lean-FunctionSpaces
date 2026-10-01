/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Atoms.Examples.TorusHat

/-!
# Analysis with Lipschitz atoms on the torus

Every `f ∈ B^s_{2,q}(𝕋^d)`, `0 < s < 1`, is a sum of Lipschitz atoms with coefficients in
`b^s_{2,q}`.  The atoms come from **quasi-interpolants** with hat functions: with the averages
`μ_{j,m} = |B_{j,m}|^(-1) ∫_{B_{j,m}} f` over the balls of radius `2^(-j)` around the grid
points,

`Q_j f = ∑_m μ_{j,m} φ_{j,m}`,

and `Q_j f - Q_{j-1} f = ∑_{m'} φ_{j,m'} (μ_{j,m'} - Q_{j-1} f)` splits into pieces supported near
the grid points of level `j`, each a multiple of a Lipschitz atom.  The size of the multiples is
controlled by differences of neighbouring averages, and these by the modulus of smoothness
through the **oscillation lemma** `Torus.sum_lintegral_pair_le`:

`∑_i ∫_{S_i} ∫_{S'_i} |f(z) - f(y)|² ≤ N |B(0, ρ)| ω(f, ρ)²`

for pairs of sets at distance `≤ ρ` with overlap `≤ N`.  The same lemma gives Jackson's
inequality `‖f - Q_j f‖_2 ≤ 2 · 6^d ω(f, 2^(-j))_2` for the quasi-interpolants
(`Torus.enorm_sub_toLp_quasiInterp_le`), so the levels sum to `f` (`Torus.hasSum_levels`).

The coefficients satisfy `‖λ‖_{b^s_{2,q}} ≤ K ‖f‖^ω_{s,q}` with the classical Besov norm through
the modulus of smoothness (`Torus.exists_lipAtoms`), and with the coincidence theorem and the
synthesis half (`Torus.memBesov_of_lipAtoms`) this gives the **Lipschitz-atomic
characterisation** of `B^s_{2,q}(𝕋^d)` for `0 < s < 1` (`Torus.memBesov_iff_exists_lipAtoms`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set
open scoped ENNReal BoundedContinuousFunction TorusHaar

namespace Torus

variable {d : Type*} [Fintype d]

/-- `‖g‖_2² = ∫ |g|²` for a measurable function. -/
theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : AEStronglyMeasurable g μ) : eLpNorm g 2 μ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hg]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `‖g‖_2² = ∫ |g|²` in `L_2(𝕋^d)`. -/
theorem enorm_sq_eq_lintegral (g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖g‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  rw [Lp.enorm_def, eLpNorm_two_sq (Lp.aestronglyMeasurable g)]

/-- `‖τ_h f - f‖_2² = ∫ |f(y + h) - f(y)|²`. -/
theorem enorm_translate_sub_sq_eq (h : UnitAddTorus d)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖translate h f - f‖ₑ ^ 2 = ∫⁻ y, ‖f (y + h) - f y‖ₑ ^ 2 := by
  rw [enorm_sq_eq_lintegral]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (translate h f) f, coeFn_translate h f] with y h1 h2
  rw [h1, Pi.sub_apply, h2]

/-- The volume of a ball of the circle: `|B(u, ρ)| = min(1, 2ρ)`. -/
theorem volume_closedBall_circle (u : UnitAddCircle) (ρ : ℝ) :
    volume (Metric.closedBall u ρ) = ENNReal.ofReal (min 1 (2 * ρ)) := by
  rw [TorusHaar.volume_eq_haarAddCircle]
  have h := AddCircle.volume_closedBall (T := 1) (x := u) ρ
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] at h
  exact h

/-- The volume of a ball of `𝕋^d` for the sup norm: `|B(c, ρ)| = min(1, 2ρ)^d`. -/
theorem volume_closedBall_eq (c : UnitAddTorus d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.closedBall c ρ) = ENNReal.ofReal (min 1 (2 * ρ)) ^ Fintype.card d := by
  rw [closedBall_pi c hρ, volume_pi, Measure.pi_pi]
  simp_rw [volume_closedBall_circle]
  rw [Finset.prod_const, Finset.card_univ]

/-- The closed ball `B_{j,m}` of radius `2^(-j)` around the grid point `2^(-j) m`. -/
def dyadicBall (j : ℕ) (m : d → Fin (2 ^ j)) : Set (UnitAddTorus d) :=
  Metric.closedBall (gridPoint j m) (1 / ((2 ^ j : ℕ) : ℝ))

/-- The balls `B_{j,m}` are measurable. -/
theorem measurableSet_dyadicBall (j : ℕ) (m : d → Fin (2 ^ j)) :
    MeasurableSet (dyadicBall j m) :=
  Metric.isClosed_closedBall.measurableSet

/-- `|B_{j,m}| ≥ 2^(-jd)`. -/
theorem dyadicWeight_le_volume_dyadicBall (j : ℕ) (m : d → Fin (2 ^ j)) :
    ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) j ≤ volume (dyadicBall j m) := by
  have h2 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  rw [dyadicBall, volume_closedBall_eq _ (by positivity)]
  calc ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) j
      = ENNReal.ofReal (1 / ((2 ^ j : ℕ) : ℝ)) ^ Fintype.card d := by
        rw [one_div, ENNReal.ofReal_inv_of_pos h2, ENNReal.ofReal_natCast,
          ← ENNReal.natCast_two_pow_rpow, ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]
    _ ≤ _ := by
        gcongr
        refine le_min ?_ ?_
        · rw [div_le_one h2]; exact_mod_cast Nat.one_le_two_pow
        · linarith [show 0 ≤ 1 / ((2 ^ j : ℕ) : ℝ) by positivity]

/-- `|B_{j,m}|^(-1) ≤ 2^(jd)`. -/
theorem inv_volume_dyadicBall_le (j : ℕ) (m : d → Fin (2 ^ j)) :
    (volume (dyadicBall j m))⁻¹ ≤ ENNReal.dyadicWeight (Fintype.card d) j := by
  rw [← inv_inv (ENNReal.dyadicWeight (Fintype.card d) j), ← ENNReal.dyadicWeight_neg]
  exact ENNReal.inv_le_inv.2 (dyadicWeight_le_volume_dyadicBall j m)

/-- `|B_{j,m}| ≠ 0`. -/
theorem volume_dyadicBall_ne_zero (j : ℕ) (m : d → Fin (2 ^ j)) :
    volume (dyadicBall j m) ≠ 0 :=
  (lt_of_lt_of_le (ENNReal.dyadicWeight_pos _ _) (dyadicWeight_le_volume_dyadicBall j m)).ne'

/-- **Jensen's inequality for averages**: `| |S|^(-1) ∫_S g |² ≤ |S|^(-1) ∫_S |g|²`. -/
theorem enorm_average_sq_le (S : Set (UnitAddTorus d)) {g : UnitAddTorus d → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict S)) :
    ‖(volume.real S)⁻¹ • ∫ x in S, g x‖ₑ ^ 2 ≤ (volume S)⁻¹ * ∫⁻ x in S, ‖g x‖ₑ ^ 2 := by
  rcases eq_or_ne (volume S) 0 with h0 | h0
  · rw [measureReal_def, h0, ENNReal.toReal_zero, inv_zero, zero_smul, enorm_zero]
    simp
  have hfin : volume S ≠ ∞ := measure_ne_top _ _
  have hinv : ‖(volume.real S)⁻¹‖ₑ = (volume S)⁻¹ := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_inv, measureReal_def,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos h0 hfin),
      ENNReal.ofReal_toReal hfin]
  have h1 : ‖∫ x in S, g x‖ₑ ≤ eLpNorm g 1 (volume.restrict S) := by
    rw [eLpNorm_one_eq_lintegral_enorm hg]
    exact enorm_integral_le_lintegral_enorm _
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hg
  rw [Measure.restrict_apply_univ] at h2
  have hV : (volume S ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) ^ 2 = volume S := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [enorm_smul, mul_pow, hinv]
  calc (volume S)⁻¹ ^ 2 * ‖∫ x in S, g x‖ₑ ^ 2
      ≤ (volume S)⁻¹ ^ 2 * (eLpNorm g 2 (volume.restrict S) *
          volume S ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) ^ 2 := by
        gcongr
        exact h1.trans h2
    _ = (volume S)⁻¹ * (∫⁻ x in S, ‖g x‖ₑ ^ 2) * ((volume S)⁻¹ * volume S) := by
        rw [mul_pow, hV, eLpNorm_two_sq hg]
        ring
    _ = (volume S)⁻¹ * ∫⁻ x in S, ‖g x‖ₑ ^ 2 := by
        rw [ENNReal.inv_mul_cancel h0 hfin, mul_one]

/-- Lower integrals are superadditive: `∑_i ∫ g_i ≤ ∫ ∑_i g_i`, without measurability. -/
theorem sum_lintegral_le_lintegral_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (g : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ x, g i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, g i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

open Classical in
/-- **Oscillation over pairs of sets**: for finitely many pairs `(S_i, S'_i)` of measurable sets
with `‖z - y‖ ≤ ρ` for `y ∈ S_i` and `z ∈ S'_i`, such that every `(y, z)` lies in at most `N`
of the products `S_i × S'_i`,
`∑_i ∫_{S_i} ∫_{S'_i} |f(z) - f(y)|² ≤ N |B(0, ρ)| ω(f, ρ)²`.
The proof substitutes `z = y + h`, exchanges the integrals and uses
`∫ |f(y + h) - f(y)|² dy = ‖τ_h f - f‖_2² ≤ ω(f, ρ)²` for `‖h‖ ≤ ρ`. -/
theorem sum_lintegral_pair_le {ι : Type*} (s : Finset ι) {S S' : ι → Set (UnitAddTorus d)}
    (hS : ∀ i, MeasurableSet (S i)) (hS' : ∀ i, MeasurableSet (S' i)) {ρ : ℝ}
    (hρ : ∀ i ∈ s, ∀ y ∈ S i, ∀ z ∈ S' i, ‖z - y‖ ≤ ρ) (N : ℕ)
    (hN : ∀ y z, (s.filter fun i => y ∈ S i ∧ z ∈ S' i).card ≤ N)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ∑ i ∈ s, ∫⁻ y in S i, ∫⁻ z in S' i, ‖f z - f y‖ₑ ^ 2 ≤
      N * volume (Metric.closedBall (0 : UnitAddTorus d) ρ) * modulus f ρ ^ 2 := by
  classical
  have hfm : Measurable (f : UnitAddTorus d → ℂ) := (Lp.stronglyMeasurable f).measurable
  set B := Metric.closedBall (0 : UnitAddTorus d) ρ
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  set G : UnitAddTorus d → UnitAddTorus d → ℝ≥0∞ :=
    fun y h => B.indicator (fun h => ‖f (y + h) - f y‖ₑ ^ 2) h
  have hGm : Measurable (Function.uncurry G) := by
    have h : Function.uncurry G = fun p : UnitAddTorus d × UnitAddTorus d =>
        (Prod.snd ⁻¹' B).indicator (fun p => ‖f (p.1 + p.2) - f p.1‖ₑ ^ 2) p := by
      funext p
      simp only [Function.uncurry, G, Set.indicator_apply, Set.mem_preimage]
    rw [h]
    exact (((hfm.comp (measurable_fst.add measurable_snd)).sub
      (hfm.comp measurable_fst)).enorm.pow_const 2).indicator (hB.preimage measurable_snd)
  have hb : ∀ h, ∫⁻ y, G y h ≤ B.indicator (fun _ => modulus f ρ ^ 2) h := by
    intro h
    by_cases hh : h ∈ B
    · simp only [G, Set.indicator_of_mem hh]
      rw [← enorm_translate_sub_sq_eq]
      gcongr
      exact enorm_translate_sub_le_modulus (by simpa [B] using hh)
    · simp [G, Set.indicator_of_notMem hh]
  have ha : ∀ y, ∑ i ∈ s, (S i).indicator (fun y => ∫⁻ z in S' i, ‖f z - f y‖ₑ ^ 2) y ≤
      N * ∫⁻ h, G y h := by
    intro y
    have hrw : ∀ i, (S i).indicator (fun y => ∫⁻ z in S' i, ‖f z - f y‖ₑ ^ 2) y =
        ∫⁻ z, if y ∈ S i ∧ z ∈ S' i then ‖f z - f y‖ₑ ^ 2 else 0 := by
      intro i
      by_cases hy : y ∈ S i
      · rw [Set.indicator_of_mem hy, ← lintegral_indicator (hS' i)]
        simp only [hy, true_and, Set.indicator_apply]
      · rw [Set.indicator_of_notMem hy]
        simp [hy]
    have htrans : ∫⁻ h, G y h =
        ∫⁻ z, (Metric.closedBall y ρ).indicator (fun z => ‖f z - f y‖ₑ ^ 2) z := by
      rw [← lintegral_add_left_eq_self
        (fun z => (Metric.closedBall y ρ).indicator (fun z => ‖f z - f y‖ₑ ^ 2) z) y]
      congr 1
      funext h
      simp only [G, B, Set.indicator_apply, Metric.mem_closedBall, dist_eq_norm,
        add_sub_cancel_left, sub_zero]
    rw [Finset.sum_congr rfl fun i _ => hrw i, htrans,
      ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
    refine (sum_lintegral_le_lintegral_sum _ _).trans (lintegral_mono fun z => ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    by_cases hz : (s.filter fun i => y ∈ S i ∧ z ∈ S' i).Nonempty
    · obtain ⟨i, hi⟩ := hz
      rw [Finset.mem_filter] at hi
      have hd : z ∈ Metric.closedBall y ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact hρ i hi.1 y hi.2.1 z hi.2.2
      rw [Set.indicator_of_mem hd]
      gcongr
      exact_mod_cast hN y z
    · rw [Finset.not_nonempty_iff_eq_empty.1 hz, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact bot_le
  calc ∑ i ∈ s, ∫⁻ y in S i, ∫⁻ z in S' i, ‖f z - f y‖ₑ ^ 2
      = ∑ i ∈ s, ∫⁻ y, (S i).indicator (fun y => ∫⁻ z in S' i, ‖f z - f y‖ₑ ^ 2) y :=
        Finset.sum_congr rfl fun i _ => (lintegral_indicator (hS i) _).symm
    _ ≤ ∫⁻ y, ∑ i ∈ s, (S i).indicator (fun y => ∫⁻ z in S' i, ‖f z - f y‖ₑ ^ 2) y :=
        sum_lintegral_le_lintegral_sum _ _
    _ ≤ ∫⁻ y, N * ∫⁻ h, G y h := lintegral_mono ha
    _ = N * ∫⁻ h, ∫⁻ y, G y h := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N),
          lintegral_lintegral_swap hGm.aemeasurable]
    _ ≤ N * ∫⁻ h, B.indicator (fun _ => modulus f ρ ^ 2) h :=
        mul_le_mul_right (lintegral_mono hb) _
    _ = N * volume B * modulus f ρ ^ 2 := by
        rw [lintegral_indicator_const hB]
        ring

/-- The **average** `μ_{j,m}(f) = |B_{j,m}|^(-1) ∫_{B_{j,m}} f` of `f` over the ball `B_{j,m}`. -/
noncomputable def ballAverage (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ)
    (m : d → Fin (2 ^ j)) : ℂ :=
  (volume.real (dyadicBall j m))⁻¹ • ∫ x in dyadicBall j m, f x

/-- `|μ_{j,m}(f) - c|² ≤ |B_{j,m}|^(-1) ∫_{B_{j,m}} |f - c|²` for every constant `c`. -/
theorem enorm_ballAverage_sub_sq_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ)
    (m : d → Fin (2 ^ j)) (c : ℂ) :
    ‖ballAverage f j m - c‖ₑ ^ 2 ≤
      (volume (dyadicBall j m))⁻¹ * ∫⁻ x in dyadicBall j m, ‖f x - c‖ₑ ^ 2 := by
  have hf : IntegrableOn (f : UnitAddTorus d → ℂ) (dyadicBall j m) :=
    ((Lp.memLp f).integrable one_le_two).integrableOn
  have hV : volume.real (dyadicBall j m) ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨volume_dyadicBall_ne_zero j m, measure_ne_top _ _⟩
  have h : ballAverage f j m - c =
      (volume.real (dyadicBall j m))⁻¹ • ∫ x in dyadicBall j m, (f x - c) := by
    rw [integral_sub hf (integrable_const c), setIntegral_const, smul_sub, smul_smul,
      inv_mul_cancel₀ hV, one_smul]
    rfl
  rw [h]
  exact enorm_average_sq_le _ ((Lp.aestronglyMeasurable f).restrict.sub aestronglyMeasurable_const)

/-- **Differences of averages**:
`|μ_B - μ_{B'}|² ≤ |B|^(-1) |B'|^(-1) ∫_{B'} ∫_B |f(y) - f(z)|²`. -/
theorem enorm_ballAverage_sub_sq_le' (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (j : ℕ) (m : d → Fin (2 ^ j)) (j' : ℕ) (m' : d → Fin (2 ^ j')) :
    ‖ballAverage f j m - ballAverage f j' m'‖ₑ ^ 2 ≤
      (volume (dyadicBall j m))⁻¹ * (volume (dyadicBall j' m'))⁻¹ *
        ∫⁻ z in dyadicBall j' m', ∫⁻ y in dyadicBall j m, ‖f y - f z‖ₑ ^ 2 := by
  have hne : (volume (dyadicBall j m))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (volume_dyadicBall_ne_zero j m)
  calc ‖ballAverage f j m - ballAverage f j' m'‖ₑ ^ 2
      = ‖ballAverage f j' m' - ballAverage f j m‖ₑ ^ 2 := by rw [enorm_sub_rev]
    _ ≤ (volume (dyadicBall j' m'))⁻¹ *
          ∫⁻ z in dyadicBall j' m', ‖f z - ballAverage f j m‖ₑ ^ 2 :=
        enorm_ballAverage_sub_sq_le f j' m' _
    _ ≤ (volume (dyadicBall j' m'))⁻¹ * ∫⁻ z in dyadicBall j' m',
          (volume (dyadicBall j m))⁻¹ * ∫⁻ y in dyadicBall j m, ‖f y - f z‖ₑ ^ 2 := by
        refine mul_le_mul_right (lintegral_mono fun z => ?_) _
        rw [enorm_sub_rev]
        exact enorm_ballAverage_sub_sq_le f j m _
    _ = _ := by rw [lintegral_const_mul' _ _ hne]; ring

variable [DecidableEq d]

/-- The **quasi-interpolant** `Q_j f = ∑_m μ_{j,m}(f) φ_{j,m}` of level `j`. -/
noncomputable def quasiInterp (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ)
    (x : UnitAddTorus d) : ℂ :=
  ∑ m : d → Fin (2 ^ j), ballAverage f j m * (torusHat j m x : ℂ)

/-- Quasi-interpolants are continuous. -/
theorem continuous_quasiInterp (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ) :
    Continuous (quasiInterp f j) :=
  continuous_finsetSum _ fun m _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_torusHat j m))

/-- The quasi-interpolant as a bounded continuous function. -/
noncomputable def quasiInterpBCF (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ) :
    UnitAddTorus d →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact ⟨quasiInterp f j, continuous_quasiInterp f j⟩

/-- The bounded continuous quasi-interpolant evaluates to `Q_j f`. -/
theorem quasiInterpBCF_apply (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ)
    (x : UnitAddTorus d) : quasiInterpBCF f j x = quasiInterp f j x := rfl

/-- The torus hats of one level sum to `1` in `ℂ`. -/
theorem sum_torusHat_complex (j : ℕ) (x : UnitAddTorus d) :
    ∑ m : d → Fin (2 ^ j), (torusHat j m x : ℂ) = 1 := by
  exact_mod_cast sum_torusHat j x

/-- `Q_j f(x) - c = ∑_m φ_{j,m}(x) (μ_{j,m} - c)`, by the partition of unity. -/
theorem quasiInterp_sub_const (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ)
    (x : UnitAddTorus d) (c : ℂ) :
    quasiInterp f j x - c = ∑ m, (torusHat j m x : ℂ) * (ballAverage f j m - c) := by
  rw [Finset.sum_congr rfl (fun m _ => mul_sub _ _ _), Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_torusHat_complex, one_mul, quasiInterp]
  congr 1
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

omit [DecidableEq d] in
/-- A torus hat is nonzero only on the ball `B_{j,m}`. -/
theorem mem_dyadicBall_of_torusHat_ne_zero {j : ℕ} {m : d → Fin (2 ^ j)} {x : UnitAddTorus d}
    (h : torusHat j m x ≠ 0) : x ∈ dyadicBall j m := by
  by_contra hx
  refine h (torusHat_eq_zero fun hlt => hx ?_)
  rw [dyadicBall, Metric.mem_closedBall, dist_eq_norm]
  exact hlt.le

open Classical in
/-- At most `3^d` of the balls `B_{j,m}` of one level contain a given point. -/
theorem card_filter_mem_dyadicBall_le (j : ℕ) (x : UnitAddTorus d) :
    (Finset.univ.filter fun m : d → Fin (2 ^ j) => x ∈ dyadicBall j m).card ≤
      3 ^ Fintype.card d := by
  have h := card_filter_norm_sub_gridPoint_le j 1 x
  simp only [Nat.cast_one] at h
  convert h using 3
  simp only [dyadicBall, Metric.mem_closedBall, dist_eq_norm]

open Classical in
/-- Pointwise bound for the error of the quasi-interpolant:
`|f(x) - Q_j f(x)|² ≤ 3^d ∑_m 1_{B_{j,m}}(x) |f(x) - μ_{j,m}|²`. -/
theorem enorm_sub_quasiInterp_sq_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ)
    (x : UnitAddTorus d) :
    ‖f x - quasiInterp f j x‖ₑ ^ 2 ≤ 3 ^ Fintype.card d *
      ∑ m, (dyadicBall j m).indicator (fun x => ‖f x - ballAverage f j m‖ₑ ^ 2) x := by
  set T := Finset.univ.filter fun m : d → Fin (2 ^ j) => x ∈ dyadicBall j m
  have hreal : ‖f x - quasiInterp f j x‖ ^ 2 ≤
      3 ^ Fintype.card d * ∑ m ∈ T, ‖f x - ballAverage f j m‖ ^ 2 := by
    have h1 : ‖f x - quasiInterp f j x‖ ≤ ∑ m ∈ T, ‖f x - ballAverage f j m‖ := by
      rw [← norm_neg, neg_sub, quasiInterp_sub_const]
      refine (norm_sum_le _ _).trans ?_
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun m : d → Fin (2 ^ j) => x ∈ dyadicBall j m)]
      have hzero : ∑ m ∈ Finset.univ.filter (fun m : d → Fin (2 ^ j) => x ∉ dyadicBall j m),
          ‖(torusHat j m x : ℂ) * (ballAverage f j m - f x)‖ = 0 :=
        Finset.sum_eq_zero fun m hm => by
          rw [Finset.mem_filter] at hm
          rw [by_contra fun h => hm.2 (mem_dyadicBall_of_torusHat_ne_zero h), Complex.ofReal_zero,
            zero_mul, norm_zero]
      rw [hzero, add_zero]
      refine Finset.sum_le_sum fun m _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (torusHat_nonneg _ _ _),
        norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) (torusHat_le_one _ _ _)
    calc ‖f x - quasiInterp f j x‖ ^ 2 ≤ (∑ m ∈ T, ‖f x - ballAverage f j m‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ T.card * ∑ m ∈ T, ‖f x - ballAverage f j m‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ 3 ^ Fintype.card d * ∑ m ∈ T, ‖f x - ballAverage f j m‖ ^ 2 := by
          gcongr
          exact_mod_cast card_filter_mem_dyadicBall_le j x
  have hind : ∑ m ∈ T, ENNReal.ofReal (‖f x - ballAverage f j m‖ ^ 2) =
      ∑ m, (dyadicBall j m).indicator (fun x => ‖f x - ballAverage f j m‖ₑ ^ 2) x := by
    simp only [T, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : x ∈ dyadicBall j m
    · simp only [hm, ↓reduceIte]
      rw [Set.indicator_of_mem hm, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    · simp only [hm, ↓reduceIte]
      rw [Set.indicator_of_notMem hm]
  calc ‖f x - quasiInterp f j x‖ₑ ^ 2 = ENNReal.ofReal (‖f x - quasiInterp f j x‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (3 ^ Fintype.card d * ∑ m ∈ T, ‖f x - ballAverage f j m‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity, hind]

open Classical in
/-- **Jackson's inequality for the quasi-interpolant**:
`‖f - Q_j f‖_2² ≤ 36^d ω(f, 2 · 2^(-j))_2²`. -/
theorem enorm_sub_quasiInterp_sq_le' (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ) :
    ‖f - BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (quasiInterpBCF f j)‖ₑ ^ 2 ≤
      36 ^ Fintype.card d * modulus f (2 / ((2 ^ j : ℕ) : ℝ)) ^ 2 := by
  have hfm : Measurable (f : UnitAddTorus d → ℂ) := (Lp.stronglyMeasurable f).measurable
  have h2 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hpair := sum_lintegral_pair_le (Finset.univ : Finset (d → Fin (2 ^ j)))
    (S := dyadicBall j) (S' := dyadicBall j) (measurableSet_dyadicBall j)
    (measurableSet_dyadicBall j) (ρ := 2 / ((2 ^ j : ℕ) : ℝ))
    (fun m _ y hy z hz => by
      rw [dyadicBall, Metric.mem_closedBall, dist_eq_norm] at hy hz
      calc ‖z - y‖ = ‖(z - gridPoint j m) - (y - gridPoint j m)‖ := by congr 1; abel
        _ ≤ ‖z - gridPoint j m‖ + ‖y - gridPoint j m‖ := norm_sub_le _ _
        _ ≤ 2 / ((2 ^ j : ℕ) : ℝ) := by linarith [show (2 : ℝ) / ((2 ^ j : ℕ) : ℝ) =
              1 / ((2 ^ j : ℕ) : ℝ) + 1 / ((2 ^ j : ℕ) : ℝ) by ring])
    (3 ^ Fintype.card d)
    (fun y z => (Finset.card_le_card fun m hm => by
      simp only [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.1⟩).trans
      (card_filter_mem_dyadicBall_le j y)) f
  have hvol : volume (Metric.closedBall (0 : UnitAddTorus d) (2 / ((2 ^ j : ℕ) : ℝ))) ≤
      4 ^ Fintype.card d * ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) j := by
    have h := volume_closedBall_gridPoint_le (d := d) j 2 0
    refine h.trans_eq ?_
    rw [show ENNReal.ofReal (2 * ((2 : ℕ) : ℝ)) = 4 by norm_num]
  have hmeas : ∀ m : d → Fin (2 ^ j), Measurable
      ((dyadicBall j m).indicator fun x => ‖f x - ballAverage f j m‖ₑ ^ 2) := fun m =>
    ((hfm.sub measurable_const).enorm.pow_const 2).indicator (measurableSet_dyadicBall j m)
  rw [enorm_sq_eq_lintegral]
  calc ∫⁻ x, ‖(f - BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (quasiInterpBCF f j)) x‖ₑ ^ 2
      = ∫⁻ x, ‖f x - quasiInterp f j x‖ₑ ^ 2 := by
        refine lintegral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub f (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ
          (quasiInterpBCF f j)), BoundedContinuousFunction.coeFn_toLp 2 volume ℝ
          (quasiInterpBCF f j)] with x h1 h2
        rw [h1, Pi.sub_apply, h2, quasiInterpBCF_apply]
    _ ≤ ∫⁻ x, 3 ^ Fintype.card d *
          ∑ m, (dyadicBall j m).indicator (fun x => ‖f x - ballAverage f j m‖ₑ ^ 2) x :=
        lintegral_mono fun x => enorm_sub_quasiInterp_sq_le f j x
    _ = 3 ^ Fintype.card d * ∑ m, ∫⁻ x in dyadicBall j m, ‖f x - ballAverage f j m‖ₑ ^ 2 := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun m _ => hmeas m),
          lintegral_finsetSum _ fun m _ => hmeas m]
        simp_rw [lintegral_indicator (measurableSet_dyadicBall j _)]
    _ ≤ 3 ^ Fintype.card d * ∑ m, ENNReal.dyadicWeight (Fintype.card d) j *
          ∫⁻ x in dyadicBall j m, ∫⁻ z in dyadicBall j m, ‖f z - f x‖ₑ ^ 2 := by
        gcongr with m
        calc ∫⁻ x in dyadicBall j m, ‖f x - ballAverage f j m‖ₑ ^ 2
            ≤ ∫⁻ x in dyadicBall j m, (volume (dyadicBall j m))⁻¹ *
                ∫⁻ z in dyadicBall j m, ‖f z - f x‖ₑ ^ 2 :=
              lintegral_mono fun x => by
                rw [enorm_sub_rev]
                exact enorm_ballAverage_sub_sq_le f j m _
          _ = (volume (dyadicBall j m))⁻¹ * ∫⁻ x in dyadicBall j m,
                ∫⁻ z in dyadicBall j m, ‖f z - f x‖ₑ ^ 2 :=
              lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (volume_dyadicBall_ne_zero j m))
          _ ≤ _ := by gcongr; exact inv_volume_dyadicBall_le j m
    _ = 3 ^ Fintype.card d * ENNReal.dyadicWeight (Fintype.card d) j *
          ∑ m, ∫⁻ x in dyadicBall j m, ∫⁻ z in dyadicBall j m, ‖f z - f x‖ₑ ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]
    _ ≤ 3 ^ Fintype.card d * ENNReal.dyadicWeight (Fintype.card d) j *
          ((3 ^ Fintype.card d : ℕ) * (4 ^ Fintype.card d *
            ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) j) *
              modulus f (2 / ((2 ^ j : ℕ) : ℝ)) ^ 2) := by
        gcongr
        exact hpair.trans (by gcongr)
    _ = 36 ^ Fintype.card d * modulus f (2 / ((2 ^ j : ℕ) : ℝ)) ^ 2 := by
        have hw := ENNReal.dyadicWeight_mul_neg_self (Fintype.card d : ℝ) j
        push_cast
        calc (3 : ℝ≥0∞) ^ Fintype.card d * ENNReal.dyadicWeight (Fintype.card d) j *
              (3 ^ Fintype.card d * (4 ^ Fintype.card d *
                ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) j) *
                  modulus f (2 / 2 ^ j) ^ 2)
            = (3 * 3 * 4) ^ Fintype.card d * (ENNReal.dyadicWeight (Fintype.card d) j *
                ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) j) * modulus f (2 / 2 ^ j) ^ 2 := by
              rw [mul_pow, mul_pow]; ring
          _ = _ := by rw [hw, mul_one]; norm_num

omit [DecidableEq d] in
/-- Where a torus hat is nonzero, the point is within `2^(-j)` of the grid point. -/
theorem norm_sub_gridPoint_lt {j : ℕ} {m : d → Fin (2 ^ j)} {x : UnitAddTorus d}
    (h : torusHat j m x ≠ 0) : ‖x - gridPoint j m‖ < 1 / ((2 ^ j : ℕ) : ℝ) := by
  by_contra h'
  exact h (torusHat_eq_zero h')

/-- The level-`k` **neighbours** of the grid point `2^(-(k+1)) m'`: the positions `m` of level `k`
with `‖2^(-k) m - 2^(-(k+1)) m'‖ < 3 · 2^(-(k+1))`. -/
noncomputable def nbr (k : ℕ) (m' : d → Fin (2 ^ (k + 1))) : Finset (d → Fin (2 ^ k)) :=
  Finset.univ.filter fun m => ‖gridPoint k m - gridPoint (k + 1) m'‖ < 3 / ((2 ^ (k + 1) : ℕ) : ℝ)

/-- If the hats `φ_{k+1,m'}` and `φ_{k,m}` are both nonzero at a point, `m` is a neighbour of
`m'`. -/
theorem mem_nbr {k : ℕ} {m' : d → Fin (2 ^ (k + 1))} {m : d → Fin (2 ^ k)} {x : UnitAddTorus d}
    (h' : torusHat (k + 1) m' x ≠ 0) (h : torusHat k m x ≠ 0) : m ∈ nbr k m' := by
  rw [nbr, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have h1 := norm_sub_gridPoint_lt h'
  have h2 := norm_sub_gridPoint_lt h
  have hk : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  calc ‖gridPoint k m - gridPoint (k + 1) m'‖
      = ‖(x - gridPoint (k + 1) m') - (x - gridPoint k m)‖ := by congr 1; abel
    _ ≤ ‖x - gridPoint (k + 1) m'‖ + ‖x - gridPoint k m‖ := norm_sub_le _ _
    _ < 1 / ((2 ^ (k + 1) : ℕ) : ℝ) + 1 / ((2 ^ k : ℕ) : ℝ) := add_lt_add h1 h2
    _ = 3 / ((2 ^ (k + 1) : ℕ) : ℝ) := by rw [hk]; field_simp; norm_num

/-- The **local oscillation** `M_{k+1,m'} = ∑_{m ∈ N(m')} |μ_{k,m} - μ_{k+1,m'}|`. -/
noncomputable def localOsc (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) : ℝ :=
  ∑ m ∈ nbr k m', ‖ballAverage f k m - ballAverage f (k + 1) m'‖

/-- The local oscillation is nonnegative. -/
theorem localOsc_nonneg (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) : 0 ≤ localOsc f k m' :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The **piece** `φ_{k+1,m'} (μ_{k+1,m'} - Q_k f)` of `Q_{k+1} f - Q_k f` at `m'`. -/
noncomputable def piece (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) (x : UnitAddTorus d) : ℂ :=
  (torusHat (k + 1) m' x : ℂ) * (ballAverage f (k + 1) m' - quasiInterp f k x)

/-- Pieces are continuous. -/
theorem continuous_piece (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) : Continuous (piece f k m') :=
  (Complex.continuous_ofReal.comp (continuous_torusHat _ _)).mul
    (continuous_const.sub (continuous_quasiInterp f k))

/-- **The pieces add up to the difference of quasi-interpolants**:
`∑_{m'} φ_{k+1,m'} (μ_{k+1,m'} - Q_k f) = Q_{k+1} f - Q_k f`. -/
theorem sum_piece (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (x : UnitAddTorus d) :
    ∑ m', piece f k m' x = quasiInterp f (k + 1) x - quasiInterp f k x := by
  simp only [piece, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_torusHat_complex, one_mul, quasiInterp]
  congr 1
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

/-- A sum over all positions of level `k` whose terms vanish outside `N(m')` and are bounded
there by `c` is at most the sum of `c` over `N(m')`. -/
theorem sum_le_sum_nbr {k : ℕ} {m' : d → Fin (2 ^ (k + 1))} {b c : (d → Fin (2 ^ k)) → ℝ}
    (hb : ∀ m, m ∉ nbr k m' → b m = 0) (hbc : ∀ m ∈ nbr k m', b m ≤ c m) :
    ∑ m, b m ≤ ∑ m ∈ nbr k m', c m := by
  rw [← Finset.sum_subset (Finset.subset_univ (nbr k m')) fun m _ hm => hb m hm]
  exact Finset.sum_le_sum hbc

/-- On the support of `φ_{k+1,m'}`, `|Q_k f - μ_{k+1,m'}| ≤ M_{k+1,m'}`. -/
theorem norm_quasiInterp_sub_le {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))} {k : ℕ}
    {m' : d → Fin (2 ^ (k + 1))} {x : UnitAddTorus d} (hx : torusHat (k + 1) m' x ≠ 0) :
    ‖quasiInterp f k x - ballAverage f (k + 1) m'‖ ≤ localOsc f k m' := by
  rw [quasiInterp_sub_const]
  refine (norm_sum_le _ _).trans (sum_le_sum_nbr (fun m hm => ?_) fun m _ => ?_)
  · rw [show torusHat k m x = 0 by by_contra h; exact hm (mem_nbr hx h), Complex.ofReal_zero,
      zero_mul, norm_zero]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (torusHat_nonneg _ _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (torusHat_le_one _ _ _)

/-- On the support of `φ_{k+1,m'}`, `Q_k f` is Lipschitz with constant `#d 2^k M_{k+1,m'}`. -/
theorem norm_quasiInterp_sub_quasiInterp_le {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    {k : ℕ} {m' : d → Fin (2 ^ (k + 1))} {x y : UnitAddTorus d}
    (hx : torusHat (k + 1) m' x ≠ 0) (hy : torusHat (k + 1) m' y ≠ 0) :
    ‖quasiInterp f k x - quasiInterp f k y‖ ≤
      Fintype.card d * 2 ^ k * ‖x - y‖ * localOsc f k m' := by
  have h : quasiInterp f k x - quasiInterp f k y = ∑ m, ((torusHat k m x : ℂ) -
      (torusHat k m y : ℂ)) * (ballAverage f k m - ballAverage f (k + 1) m') := by
    rw [← sub_sub_sub_cancel_right _ _ (ballAverage f (k + 1) m'), quasiInterp_sub_const,
      quasiInterp_sub_const, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => (sub_mul _ _ _).symm
  rw [h, localOsc, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum_nbr (fun m hm => ?_) fun m _ => ?_)
  · rw [show torusHat k m x = 0 by by_contra h; exact hm (mem_nbr hx h),
      show torusHat k m y = 0 by by_contra h; exact hm (mem_nbr hy h), sub_self, zero_mul,
      norm_zero]
  · rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact abs_torusHat_sub_le _ _ _ _

/-- **Size of a piece**: `|φ_{k+1,m'} (μ_{k+1,m'} - Q_k f)| ≤ M_{k+1,m'}`. -/
theorem norm_piece_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) (x : UnitAddTorus d) : ‖piece f k m' x‖ ≤ localOsc f k m' := by
  by_cases hx : torusHat (k + 1) m' x = 0
  · rw [piece, hx, Complex.ofReal_zero, zero_mul, norm_zero]
    exact localOsc_nonneg f k m'
  rw [piece, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (torusHat_nonneg _ _ _),
    norm_sub_rev]
  exact mul_le_of_le_one_left (norm_nonneg _) (torusHat_le_one _ _ _) |>.trans
    (norm_quasiInterp_sub_le hx)

/-- **Pieces are Lipschitz**: `|p(x) - p(y)| ≤ 2 #d 2^(k+1) M_{k+1,m'} ‖x - y‖` for the piece `p`
at `m'`. -/
theorem norm_piece_sub_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) (x y : UnitAddTorus d) :
    ‖piece f k m' x - piece f k m' y‖ ≤
      2 * Fintype.card d * 2 ^ (k + 1) * localOsc f k m' * ‖x - y‖ := by
  set M := localOsc f k m'
  have hM := localOsc_nonneg f k m'
  set u := torusHat (k + 1) m' x
  set v := torusHat (k + 1) m' y
  set A := ballAverage f (k + 1) m' - quasiInterp f k x
  set B := ballAverage f (k + 1) m' - quasiInterp f k y
  have huv : |u - v| ≤ Fintype.card d * 2 ^ (k + 1) * ‖x - y‖ := abs_torusHat_sub_le _ _ _ _
  have hdk : (Fintype.card d : ℝ) * 2 ^ (k + 1) * ‖x - y‖ * M ≤
      2 * Fintype.card d * 2 ^ (k + 1) * M * ‖x - y‖ := by
    have : 0 ≤ (Fintype.card d : ℝ) * 2 ^ (k + 1) * ‖x - y‖ * M := by positivity
    linarith
  have hA : u ≠ 0 → ‖A‖ ≤ M := fun hu => by
    rw [norm_sub_rev]; exact norm_quasiInterp_sub_le hu
  have hB : v ≠ 0 → ‖B‖ ≤ M := fun hv => by
    rw [norm_sub_rev]; exact norm_quasiInterp_sub_le hv
  have hp : piece f k m' x - piece f k m' y = (u - v : ℝ) * A + (v : ℂ) * (A - B) := by
    simp only [piece, u, v, A, B]; push_cast; ring
  by_cases hu : u = 0 <;> by_cases hv : v = 0
  · rw [hp, hu, hv]; simp only [sub_self, Complex.ofReal_zero, zero_mul, add_zero, norm_zero]
    positivity
  · -- `u = 0`: the difference is `-v B`
    have hp' : piece f k m' x - piece f k m' y = (u - v : ℝ) * B := by
      simp only [piece, u, v, B] at hu ⊢; rw [hu]; push_cast; ring
    rw [hp', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |u - v| * ‖B‖ ≤ (Fintype.card d * 2 ^ (k + 1) * ‖x - y‖) * M :=
          mul_le_mul huv (hB hv) (norm_nonneg _) (by positivity)
      _ ≤ _ := hdk
  · rw [hp, hv, Complex.ofReal_zero, zero_mul, add_zero, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, sub_zero]
    calc |u| * ‖A‖ ≤ (Fintype.card d * 2 ^ (k + 1) * ‖x - y‖) * M := by
          refine mul_le_mul ?_ (hA hu) (norm_nonneg _) (by positivity)
          simpa [hv] using huv
      _ ≤ _ := hdk
  · rw [hp]
    have hAB : ‖A - B‖ ≤ Fintype.card d * 2 ^ k * ‖x - y‖ * M := by
      rw [show A - B = quasiInterp f k y - quasiInterp f k x by simp only [A, B]; ring,
        norm_sub_rev]
      exact norm_quasiInterp_sub_quasiInterp_le hu hv
    have hv1 : |v| ≤ 1 := by
      rw [abs_of_nonneg (torusHat_nonneg _ _ _)]; exact torusHat_le_one _ _ _
    calc ‖((u - v : ℝ) : ℂ) * A + (v : ℂ) * (A - B)‖
        ≤ |u - v| * ‖A‖ + |v| * ‖A - B‖ := by
          refine (norm_add_le _ _).trans_eq ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ (Fintype.card d * 2 ^ (k + 1) * ‖x - y‖) * M +
            1 * (Fintype.card d * 2 ^ k * ‖x - y‖ * M) := by
          gcongr
          · exact hA hu
      _ ≤ 2 * Fintype.card d * 2 ^ (k + 1) * M * ‖x - y‖ := by
          have h2k : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
          have : (Fintype.card d : ℝ) * 2 ^ k * ‖x - y‖ * M ≤
              Fintype.card d * 2 ^ (k + 1) * ‖x - y‖ * M := by gcongr
          nlinarith [this]

/-- A piece vanishes outside the open ball of radius `2^(-(k+1))` around its grid point. -/
theorem piece_eq_zero {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))} {k : ℕ}
    {m' : d → Fin (2 ^ (k + 1))} {x : UnitAddTorus d}
    (hx : ¬ ‖x - gridPoint (k + 1) m'‖ < 1 / ((2 ^ (k + 1) : ℕ) : ℝ)) : piece f k m' x = 0 := by
  rw [piece, torusHat_eq_zero hx, Complex.ofReal_zero, zero_mul]

/-- The coefficient `λ_{k+1,m'} = (2 #d + 1) M_{k+1,m'}` of the piece at `m'`. -/
noncomputable def pieceCoeff (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) : ℝ :=
  (2 * Fintype.card d + 1) * localOsc f k m'

/-- The atom `λ_{k+1,m'}^(-1) p` of the piece `p` at `m'` (`0` if `λ_{k+1,m'} = 0`). -/
noncomputable def pieceAtom (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) : UnitAddTorus d →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (((pieceCoeff f k m')⁻¹ : ℝ) : ℂ) * piece f k m' x,
      continuous_const.mul (continuous_piece f k m')⟩

/-- The atom of a piece evaluates to `λ^(-1) p(x)`. -/
theorem pieceAtom_apply (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) (x : UnitAddTorus d) :
    pieceAtom f k m' x = (((pieceCoeff f k m')⁻¹ : ℝ) : ℂ) * piece f k m' x := rfl

/-- **The atom of a piece is a Lipschitz atom** of level `k + 1` with support radius `1`. -/
theorem isLipAtom_pieceAtom (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) : IsLipAtom 1 (k + 1) m' (pieceAtom f k m') := by
  have hM := localOsc_nonneg f k m'
  have hc : 0 ≤ pieceCoeff f k m' := by unfold pieceCoeff; positivity
  have hd : (0 : ℝ) ≤ Fintype.card d := Nat.cast_nonneg _
  refine ⟨fun x => ?_, fun x y => ?_, fun x hx => ?_⟩
  · rw [pieceAtom_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 hc)]
    rcases hc.eq_or_lt with h0 | hpos
    · rw [← h0, inv_zero, zero_mul]; exact zero_le_one
    rw [inv_mul_le_iff₀ hpos, mul_one]
    refine (norm_piece_le f k m' x).trans ?_
    unfold pieceCoeff
    nlinarith
  · rw [pieceAtom_apply, pieceAtom_apply, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hc)]
    rcases hc.eq_or_lt with h0 | hpos
    · rw [← h0, inv_zero, zero_mul]; positivity
    rw [inv_mul_le_iff₀ hpos]
    refine (norm_piece_sub_le f k m' x y).trans ?_
    unfold pieceCoeff
    have hxy := norm_nonneg (x - y)
    have : 0 ≤ (2 : ℝ) ^ (k + 1) * localOsc f k m' * ‖x - y‖ := by positivity
    nlinarith
  · rw [pieceAtom_apply, piece_eq_zero (not_lt.2 (by simpa using hx.le)), mul_zero]

/-- `λ_{k+1,m'} · (atom at m') = piece at m'`. -/
theorem pieceCoeff_mul_pieceAtom (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) (x : UnitAddTorus d) :
    (pieceCoeff f k m' : ℂ) * pieceAtom f k m' x = piece f k m' x := by
  rw [pieceAtom_apply]
  rcases eq_or_ne (pieceCoeff f k m') 0 with h0 | h0
  · have hM : localOsc f k m' = 0 := by
      unfold pieceCoeff at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exfalso; have : (0 : ℝ) ≤ Fintype.card d := Nat.cast_nonneg _; linarith
      · exact h
    have hp : piece f k m' x = 0 := norm_le_zero_iff.1 (hM ▸ norm_piece_le f k m' x)
    rw [hp, mul_zero, mul_zero]
  · rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_mul]

/-- A grid point of level `k + 1` has at most `5^d` neighbours `N(m')` of level `k`. -/
theorem card_nbr_le (k : ℕ) (m' : d → Fin (2 ^ (k + 1))) :
    (nbr k m').card ≤ 5 ^ Fintype.card d := by
  refine (Finset.card_le_card fun m hm => ?_).trans (card_filter_norm_sub_gridPoint_le k 2
    (gridPoint (k + 1) m'))
  rw [nbr, Finset.mem_filter] at hm
  rw [Finset.mem_filter, norm_sub_rev]
  refine ⟨Finset.mem_univ _, hm.2.le.trans ?_⟩
  have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  rw [show ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) by push_cast; ring]
  rw [div_le_div_iff₀ (by positivity) hpos, Nat.cast_ofNat]
  linarith

/-- `|λ_{k+1,m'}|² ≤ (2 #d + 1)² 5^d ∑_{m ∈ N(m')} |μ_{k,m} - μ_{k+1,m'}|²` (Cauchy–Schwarz). -/
theorem enorm_pieceCoeff_sq_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ)
    (m' : d → Fin (2 ^ (k + 1))) :
    ‖pieceCoeff f k m'‖ₑ ^ 2 ≤ (2 * Fintype.card d + 1) ^ 2 * 5 ^ Fintype.card d *
      ∑ m ∈ nbr k m', ‖ballAverage f k m - ballAverage f (k + 1) m'‖ₑ ^ 2 := by
  have hM := localOsc_nonneg f k m'
  have hreal : pieceCoeff f k m' ^ 2 ≤ (2 * Fintype.card d + 1) ^ 2 * 5 ^ Fintype.card d *
      ∑ m ∈ nbr k m', ‖ballAverage f k m - ballAverage f (k + 1) m'‖ ^ 2 := by
    rw [pieceCoeff, mul_pow, mul_assoc]
    gcongr
    calc localOsc f k m' ^ 2 ≤ (nbr k m').card *
          ∑ m ∈ nbr k m', ‖ballAverage f k m - ballAverage f (k + 1) m'‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ _ := by gcongr; exact_mod_cast card_nbr_le k m'
  have hc : 0 ≤ pieceCoeff f k m' := by unfold pieceCoeff; positivity
  calc ‖pieceCoeff f k m'‖ₑ ^ 2 = ENNReal.ofReal (pieceCoeff f k m' ^ 2) := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hc, ENNReal.ofReal_pow hc]
    _ ≤ ENNReal.ofReal ((2 * Fintype.card d + 1) ^ 2 * 5 ^ Fintype.card d *
          ∑ m ∈ nbr k m', ‖ballAverage f k m - ballAverage f (k + 1) m'‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity]
        congr 1
        · congr 1
          · rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul zero_le_two,
              ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
          · rw [ENNReal.ofReal_ofNat]
        · refine Finset.sum_congr rfl fun m _ => ?_
          rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

open Classical in
/-- **The oscillation of neighbouring averages**: summed over all grid points of level `k + 1`
and their neighbours,
`∑_{m'} ∑_{m ∈ N(m')} ∫_{B_{k+1,m'}} ∫_{B_{k,m}} |f(y) - f(z)|²`
`≤ 9^d 6^d 2^(-kd) ω(f, 3 · 2^(-k))²`. -/
theorem sum_nbr_lintegral_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ) :
    ∑ m' : d → Fin (2 ^ (k + 1)), ∑ m ∈ nbr k m', ∫⁻ z in dyadicBall (k + 1) m',
      ∫⁻ y in dyadicBall k m, ‖f y - f z‖ₑ ^ 2 ≤
        (3 ^ Fintype.card d * 3 ^ Fintype.card d : ℕ) *
          (6 ^ Fintype.card d * ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) k) *
            modulus f (3 / ((2 ^ k : ℕ) : ℝ)) ^ 2 := by
  have hk : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  rw [Finset.sum_sigma']
  refine (sum_lintegral_pair_le (Finset.univ.sigma (nbr k))
    (S := fun p => dyadicBall (k + 1) p.1) (S' := fun p => dyadicBall k p.2)
    (fun p => measurableSet_dyadicBall _ _) (fun p => measurableSet_dyadicBall _ _)
    (ρ := 3 / ((2 ^ k : ℕ) : ℝ)) (fun p hp z hz y hy => ?_)
    (3 ^ Fintype.card d * 3 ^ Fintype.card d)
    (fun z y => ?_) f).trans ?_
  · rw [Finset.mem_sigma] at hp
    have hn := hp.2
    rw [nbr, Finset.mem_filter] at hn
    rw [dyadicBall, Metric.mem_closedBall, dist_eq_norm] at hz hy
    calc ‖y - z‖ = ‖(y - gridPoint k p.2) + (gridPoint k p.2 - gridPoint (k + 1) p.1) -
          (z - gridPoint (k + 1) p.1)‖ := by congr 1; abel
      _ ≤ ‖y - gridPoint k p.2‖ + ‖gridPoint k p.2 - gridPoint (k + 1) p.1‖ +
          ‖z - gridPoint (k + 1) p.1‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1 / ((2 ^ k : ℕ) : ℝ) + 3 / ((2 ^ (k + 1) : ℕ) : ℝ) + 1 / ((2 ^ (k + 1) : ℕ) : ℝ) := by
          gcongr; exact hn.2.le
      _ = 3 / ((2 ^ k : ℕ) : ℝ) := by rw [hk]; field_simp; norm_num
  · refine (Finset.card_le_card (t := (Finset.univ.filter fun m' => z ∈ dyadicBall (k + 1) m').sigma
      fun _ => Finset.univ.filter fun m => y ∈ dyadicBall k m) fun p hp => ?_).trans ?_
    · rw [Finset.mem_filter] at hp
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, hp.2.1⟩, Finset.mem_univ _, hp.2.2⟩
    · rw [Finset.card_sigma]
      refine (Finset.sum_le_card_nsmul _ _ _ fun _ _ => card_filter_mem_dyadicBall_le k y).trans ?_
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ (card_filter_mem_dyadicBall_le (k + 1) z)
  · gcongr
    refine (volume_closedBall_gridPoint_le k 3 0).trans_eq ?_
    rw [show ENNReal.ofReal (2 * ((3 : ℕ) : ℝ)) = 6 by norm_num]

/-- **The coefficients of level `k + 1`**:
`∑_{m'} |λ_{k+1,m'}|² ≤ ((2 #d + 1) · 3 · 24^d · 2^(kd/2) ω(f, 2^(-k)))²`. -/
theorem sum_enorm_pieceCoeff_sq_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ) :
    ∑ m', ‖pieceCoeff f k m'‖ₑ ^ 2 ≤ ((2 * Fintype.card d + 1) * 3 * 24 ^ Fintype.card d *
      ENNReal.dyadicWeight (Fintype.card d / 2) k * modulus f (1 / ((2 ^ k : ℕ) : ℝ))) ^ 2 := by
  set V := ENNReal.dyadicWeight (Fintype.card d) k
  set W := ENNReal.dyadicWeight (-(Fintype.card d : ℝ)) k
  set ω := modulus f (1 / ((2 ^ k : ℕ) : ℝ))
  have hV1 : ENNReal.dyadicWeight (Fintype.card d) (k + 1) = 2 ^ Fintype.card d * V := by
    rw [ENNReal.dyadicWeight_succ, ENNReal.rpow_natCast]
  have hVW : V * W = 1 := ENNReal.dyadicWeight_mul_neg_self _ k
  have hW2 : ENNReal.dyadicWeight (Fintype.card d / 2) k ^ 2 = V := by
    rw [← ENNReal.rpow_two, ENNReal.dyadicWeight_rpow]
    congr 1
    ring
  have hω3 : modulus f (3 / ((2 ^ k : ℕ) : ℝ)) ≤ 3 * ω := by
    have h := modulus_natCast_mul_le (n := 3) (by norm_num) f
      (t := 1 / ((2 ^ k : ℕ) : ℝ)) (by positivity)
    rw [show ((3 : ℕ) : ℝ) * (1 / ((2 ^ k : ℕ) : ℝ)) = 3 / ((2 ^ k : ℕ) : ℝ) by ring] at h
    exact_mod_cast h
  have hpair : ∀ m' : d → Fin (2 ^ (k + 1)), ∀ m ∈ nbr k m',
      ‖ballAverage f k m - ballAverage f (k + 1) m'‖ₑ ^ 2 ≤
        V * (2 ^ Fintype.card d * V) * ∫⁻ z in dyadicBall (k + 1) m',
          ∫⁻ y in dyadicBall k m, ‖f y - f z‖ₑ ^ 2 := fun m' m _ => by
    refine (enorm_ballAverage_sub_sq_le' f k m (k + 1) m').trans ?_
    rw [← hV1]
    gcongr
    · exact inv_volume_dyadicBall_le k m
    · exact inv_volume_dyadicBall_le (k + 1) m'
  calc ∑ m', ‖pieceCoeff f k m'‖ₑ ^ 2
      ≤ ∑ m' : d → Fin (2 ^ (k + 1)), (2 * Fintype.card d + 1) ^ 2 * 5 ^ Fintype.card d *
          ∑ m ∈ nbr k m', ‖ballAverage f k m - ballAverage f (k + 1) m'‖ₑ ^ 2 :=
        Finset.sum_le_sum fun m' _ => enorm_pieceCoeff_sq_le f k m'
    _ ≤ ∑ m' : d → Fin (2 ^ (k + 1)), (2 * Fintype.card d + 1) ^ 2 * 5 ^ Fintype.card d *
          ∑ m ∈ nbr k m', V * (2 ^ Fintype.card d * V) * ∫⁻ z in dyadicBall (k + 1) m',
            ∫⁻ y in dyadicBall k m, ‖f y - f z‖ₑ ^ 2 := by
        gcongr with m' _ m hm
        exact hpair m' m hm
    _ = (2 * Fintype.card d + 1) ^ 2 * 5 ^ Fintype.card d * (V * (2 ^ Fintype.card d * V)) *
          ∑ m' : d → Fin (2 ^ (k + 1)), ∑ m ∈ nbr k m', ∫⁻ z in dyadicBall (k + 1) m',
            ∫⁻ y in dyadicBall k m, ‖f y - f z‖ₑ ^ 2 := by
        simp_rw [← Finset.mul_sum]; ring
    _ ≤ (2 * Fintype.card d + 1) ^ 2 * 5 ^ Fintype.card d * (V * (2 ^ Fintype.card d * V)) *
          ((3 ^ Fintype.card d * 3 ^ Fintype.card d : ℕ) * (6 ^ Fintype.card d * W) *
            (3 * ω) ^ 2) := by
        gcongr
        exact (sum_nbr_lintegral_le f k).trans (by gcongr)
    _ = (2 * Fintype.card d + 1) ^ 2 * 9 * (5 * 2 * 3 * 3 * 6) ^ Fintype.card d * V * (V * W) *
          ω ^ 2 := by
        push_cast
        simp only [mul_pow]
        ring
    _ ≤ (2 * Fintype.card d + 1) ^ 2 * 9 * (24 ^ Fintype.card d) ^ 2 * V * 1 * ω ^ 2 := by
        have h540 : (5 * 2 * 3 * 3 * 6 : ℝ≥0∞) ^ Fintype.card d ≤ (24 ^ Fintype.card d) ^ 2 :=
          calc (5 * 2 * 3 * 3 * 6 : ℝ≥0∞) ^ Fintype.card d ≤ (24 ^ 2) ^ Fintype.card d := by
                gcongr; norm_num
            _ = (24 ^ Fintype.card d) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        rw [hVW]
        exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl h540) le_rfl) le_rfl)
          le_rfl
    _ = _ := by
        rw [← hW2]
        ring

/-- The level-`0` atom: the constant `μ_0 / |μ_0|` (`0` if `μ_0 = 0`). -/
noncomputable def meanAtom (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : d → Fin (2 ^ 0)) : UnitAddTorus d →ᵇ ℂ :=
  BoundedContinuousFunction.const _ (ballAverage f 0 m / (‖ballAverage f 0 m‖ : ℂ))

omit [DecidableEq d] in
/-- The level-`0` atom is a Lipschitz atom. -/
theorem isLipAtom_meanAtom (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : d → Fin (2 ^ 0)) : IsLipAtom 1 0 m (meanAtom f m) where
  norm_le x := by
    rw [meanAtom, BoundedContinuousFunction.const_apply, norm_div, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  lipschitz x y := by simp [meanAtom]
  eq_zero x hx := absurd hx (not_lt.2 ((norm_le_half _).trans (by norm_num)))

omit [DecidableEq d] in
/-- `|μ_0| · (μ_0 / |μ_0|) = μ_0`. -/
theorem norm_mul_meanAtom (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : d → Fin (2 ^ 0)) (x : UnitAddTorus d) :
    (‖ballAverage f 0 m‖ : ℂ) * meanAtom f m x = ballAverage f 0 m := by
  rw [meanAtom, BoundedContinuousFunction.const_apply]
  rcases eq_or_ne (ballAverage f 0 m) 0 with h | h
  · rw [h, zero_div, mul_zero]
  · rw [mul_div_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.2 h)]

/-- The level-`0` coefficients: `∑_m |μ_{0,m}|² ≤ ‖f‖_2²`. -/
theorem sum_enorm_mean_sq_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ∑ m : d → Fin (2 ^ 0), ‖‖ballAverage f 0 m‖‖ₑ ^ 2 ≤ ‖f‖ₑ ^ 2 := by
  have hm : ∀ m : d → Fin (2 ^ 0), ‖‖ballAverage f 0 m‖‖ₑ ^ 2 ≤ ‖f‖ₑ ^ 2 := fun m => by
    rw [enorm_norm, ← sub_zero (ballAverage f 0 m)]
    refine (enorm_ballAverage_sub_sq_le f 0 m 0).trans ?_
    have h1 := inv_volume_dyadicBall_le (d := d) 0 m
    rw [ENNReal.dyadicWeight_zero_right] at h1
    simp_rw [sub_zero]
    rw [enorm_sq_eq_lintegral]
    calc (volume (dyadicBall 0 m))⁻¹ * ∫⁻ x in dyadicBall 0 m, ‖f x‖ₑ ^ 2
        ≤ 1 * ∫⁻ x, ‖f x‖ₑ ^ 2 := mul_le_mul' h1 (setLIntegral_le_lintegral _ _)
      _ = _ := one_mul _
  refine (Finset.sum_le_card_nsmul _ _ _ fun m _ => hm m).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero, one_pow, one_smul]

/-- The Lipschitz atoms of the decomposition of `f`: the constant `μ_0 / |μ_0|` on level `0` and
the atoms of the pieces of `Q_{k+1} f - Q_k f` on level `k + 1`. -/
noncomputable def lipAtomOf (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (j : ℕ) → (d → Fin (2 ^ j)) → UnitAddTorus d →ᵇ ℂ
  | 0 => meanAtom f
  | k + 1 => pieceAtom f k

/-- The coefficients of the decomposition of `f`: `|μ_0|` on level `0`, `λ_{k+1,m'}` on level
`k + 1`. -/
noncomputable def lipCoeffOf (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (j : ℕ) → (d → Fin (2 ^ j)) → ℝ
  | 0 => fun m => ‖ballAverage f 0 m‖
  | k + 1 => pieceCoeff f k

/-- The atoms of the decomposition are Lipschitz atoms with support radius `1`. -/
theorem isLipAtom_lipAtomOf (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ∀ j m, IsLipAtom 1 j m (lipAtomOf f j m)
  | 0, m => isLipAtom_meanAtom f m
  | k + 1, m' => isLipAtom_pieceAtom f k m'

/-- The level `j` of the decomposition: `Q_0 f` for `j = 0` and `Q_{k+1} f - Q_k f` for
`j = k + 1`. -/
noncomputable def levelBCF (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ℕ → UnitAddTorus d →ᵇ ℂ
  | 0 => quasiInterpBCF f 0
  | k + 1 => quasiInterpBCF f (k + 1) - quasiInterpBCF f k

omit [DecidableEq d] in
/-- The torus hat of level `0` is the constant `1`. -/
theorem torusHat_zero (m : d → Fin (2 ^ 0)) (x : UnitAddTorus d) : torusHat 0 m x = 1 := by
  simp [torusHat]

/-- **Each level is the sum of its atoms**: `∑_m λ_{j,m} a_{j,m} = (level j)`. -/
theorem sum_lipCoeff_smul_lipAtom (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ) :
    ∑ m, lipCoeffOf f j m • lipAtomOf f j m = levelBCF f j := by
  ext x
  cases j with
  | zero =>
    simp only [lipCoeffOf, lipAtomOf, levelBCF, BoundedContinuousFunction.coe_sum,
      Finset.sum_apply, BoundedContinuousFunction.smul_apply, Complex.real_smul,
      norm_mul_meanAtom, quasiInterpBCF_apply, quasiInterp, torusHat_zero, Complex.ofReal_one,
      mul_one]
  | succ k =>
    simp only [lipCoeffOf, lipAtomOf, levelBCF, BoundedContinuousFunction.coe_sum,
      Finset.sum_apply, BoundedContinuousFunction.smul_apply, Complex.real_smul,
      pieceCoeff_mul_pieceAtom, sum_piece, BoundedContinuousFunction.coe_sub, Pi.sub_apply,
      quasiInterpBCF_apply]

/-- Each level of the decomposition in `L_2` is the sum of its atoms. -/
theorem sum_lipCoeff_smul_toLp (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (j : ℕ) :
    ∑ m, lipCoeffOf f j m • BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (lipAtomOf f j m) =
      BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (levelBCF f j) := by
  rw [← sum_lipCoeff_smul_lipAtom, map_sum]
  simp_rw [map_smul]

/-- **The levels telescope**: `∑_{j ≤ J} (level j) = Q_J f`. -/
theorem sum_range_levelBCF (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), levelBCF f j = quasiInterpBCF f J := by
  induction J with
  | zero => simp [levelBCF]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [levelBCF]
    abel

/-- `‖f - Q_J f‖_2 ≤ 2 · 6^d ω(f, 2^(-J))_2`. -/
theorem enorm_sub_toLp_quasiInterp_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (J : ℕ) :
    ‖f - BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (quasiInterpBCF f J)‖ₑ ≤
      2 * 6 ^ Fintype.card d * modulus f (1 / ((2 ^ J : ℕ) : ℝ)) := by
  have h2 : modulus f (2 / ((2 ^ J : ℕ) : ℝ)) ≤ 2 * modulus f (1 / ((2 ^ J : ℕ) : ℝ)) := by
    have h := modulus_natCast_mul_le (n := 2) (by norm_num) f (t := 1 / ((2 ^ J : ℕ) : ℝ))
      (by positivity)
    rw [show ((2 : ℕ) : ℝ) * (1 / ((2 ^ J : ℕ) : ℝ)) = 2 / ((2 ^ J : ℕ) : ℝ) by ring] at h
    exact_mod_cast h
  have h36 : (36 : ℝ≥0∞) ^ Fintype.card d = (6 ^ Fintype.card d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
  refine (enorm_sub_quasiInterp_sq_le' f J).trans ?_
  calc 36 ^ Fintype.card d * modulus f (2 / ((2 ^ J : ℕ) : ℝ)) ^ 2
      ≤ 36 ^ Fintype.card d * (2 * modulus f (1 / ((2 ^ J : ℕ) : ℝ))) ^ 2 := by gcongr
    _ = _ := by rw [h36]; ring

omit [DecidableEq d] in
/-- `2^(ks) ω(f, 2^(-k))_2` is bounded by the classical Besov norm. -/
theorem dyadicWeight_mul_modulus_le_modulusNorm {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ) :
    ENNReal.dyadicWeight s k * modulus f (1 / ((2 ^ k : ℕ) : ℝ)) ≤ modulusNorm s q f := by
  have h := ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
    (fun j : ℕ => ENNReal.dyadicWeight s j * modulus f (1 / 2 ^ j)) k
  push_cast
  exact h.trans le_add_self

omit [DecidableEq d] in
/-- `ω(f, 2^(-k))_2 ≤ 2^(-ks) ‖f‖^ω_{s,q}`. -/
theorem modulus_le_dyadicWeight_mul {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ) :
    modulus f (1 / ((2 ^ k : ℕ) : ℝ)) ≤ ENNReal.dyadicWeight (-s) k * modulusNorm s q f := by
  calc modulus f (1 / ((2 ^ k : ℕ) : ℝ))
      = ENNReal.dyadicWeight (-s) k * (ENNReal.dyadicWeight s k *
          modulus f (1 / ((2 ^ k : ℕ) : ℝ))) := by
        rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
    _ ≤ _ := by gcongr; exact dyadicWeight_mul_modulus_le_modulusNorm hq f k

/-- The levels `k + 1` of the decomposition are small:
`‖Q_{k+1} f - Q_k f‖_2 ≤ 4 · 6^d ω(f, 2^(-k))`. -/
theorem enorm_toLp_levelBCF_succ_le (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (k : ℕ) :
    ‖BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (levelBCF f (k + 1))‖ₑ ≤
      4 * 6 ^ Fintype.card d * modulus f (1 / ((2 ^ k : ℕ) : ℝ)) := by
  have hmono : modulus f (1 / ((2 ^ (k + 1) : ℕ) : ℝ)) ≤ modulus f (1 / ((2 ^ k : ℕ) : ℝ)) :=
    modulus_mono f (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.le_succ k)))
  simp only [levelBCF, map_sub]
  set A := BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (quasiInterpBCF f (k + 1))
  set B := BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (quasiInterpBCF f k)
  rw [← sub_sub_sub_cancel_right A B f]
  calc ‖(A - f) - (B - f)‖ₑ ≤ ‖A - f‖ₑ + ‖B - f‖ₑ := enorm_sub_le
    _ = ‖f - A‖ₑ + ‖f - B‖ₑ := by rw [enorm_sub_rev A, enorm_sub_rev B]
    _ ≤ 2 * 6 ^ Fintype.card d * modulus f (1 / ((2 ^ k : ℕ) : ℝ)) +
          2 * 6 ^ Fintype.card d * modulus f (1 / ((2 ^ k : ℕ) : ℝ)) := by
        gcongr
        · exact (enorm_sub_toLp_quasiInterp_le f (k + 1)).trans (by gcongr)
        · exact enorm_sub_toLp_quasiInterp_le f k
    _ = _ := by ring

/-- **The levels sum to `f`** in `L_2`, for `s > 0` and finite classical Besov norm. -/
theorem hasSum_levels {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (hf : modulusNorm s q f < ∞) :
    HasSum (fun j => BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (levelBCF f j)) f := by
  set g := fun j => BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (levelBCF f j)
  set K := 4 * 6 ^ Fintype.card d * modulusNorm s q f
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
    (ENNReal.pow_ne_top (by norm_num))) hf.ne
  have hgk : ∀ k, ‖g (k + 1)‖ₑ ≤ K * ENNReal.dyadicWeight (-s) k := fun k =>
    (enorm_toLp_levelBCF_succ_le f k).trans (by
      rw [show K * ENNReal.dyadicWeight (-s) k = 4 * 6 ^ Fintype.card d *
        (ENNReal.dyadicWeight (-s) k * modulusNorm s q f) by simp only [K]; ring]
      gcongr
      exact modulus_le_dyadicWeight_mul hq f k)
  have hr : (2 : ℝ≥0∞) ^ (-s) < 1 := ENNReal.two_rpow_neg_lt_one hs
  have htsum : ∑' j, ‖g j‖ₑ ≠ ∞ := by
    rw [← Summable.sum_add_tsum_nat_add' (f := fun j => ‖g j‖ₑ) (k := 1) ENNReal.summable,
      Finset.sum_range_one]
    refine ENNReal.add_ne_top.2 ⟨enorm_ne_top, ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hgk)⟩
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
    exact ENNReal.mul_ne_top hK (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne')
  have hsum : Summable g := Summable.of_norm (by simpa using ENNReal.summable_toReal htsum)
  have hpart : ∀ J, ∑ j ∈ Finset.range (J + 1), g j =
      BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (quasiInterpBCF f J) := fun J => by
    simp only [g]
    rw [← map_sum, sum_range_levelBCF]
  have htend : Filter.Tendsto (fun J =>
      BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (quasiInterpBCF f J))
      Filter.atTop (nhds f) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hU : Filter.Tendsto (fun J : ℕ => 2 * 6 ^ Fintype.card d * modulusNorm s q f *
        ((2 : ℝ≥0∞) ^ (-s)) ^ J) Filter.atTop (nhds 0) := by
      have hK2 : 2 * 6 ^ Fintype.card d * modulusNorm s q f ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num)))
          hf.ne
      have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr)
        (Or.inr hK2)
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU (fun _ => zero_le)
      fun J => ?_
    rw [edist_eq_enorm_sub, enorm_sub_rev, ← ENNReal.dyadicWeight_eq_pow, mul_assoc]
    refine (enorm_sub_toLp_quasiInterp_le f J).trans ?_
    gcongr
    rw [mul_comm]
    exact modulus_le_dyadicWeight_mul hq f J
  have h2 : Filter.Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), g j) Filter.atTop
      (nhds (∑' j, g j)) :=
    hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  simp_rw [hpart] at h2
  have hfeq : f = ∑' j, g j := tendsto_nhds_unique htend h2
  exact (congrArg (HasSum g) hfeq).mpr hsum.hasSum

/-- `‖a‖_{ℓ_2} ≤ X` when `∑_m a_m² ≤ X²`. -/
theorem finLqNorm_two_le {M : Type*} [Fintype M] {a : M → ℝ≥0∞} {X : ℝ≥0∞}
    (h : ∑ m, a m ^ 2 ≤ X ^ 2) : ENNReal.finLqNorm 2 a ≤ X := by
  simp only [ENNReal.finLqNorm, ENNReal.ofNat_ne_top, ↓reduceIte, ENNReal.toReal_ofNat,
    ENNReal.rpow_two]
  calc (∑ m, a m ^ 2) ^ (1 / 2 : ℝ) ≤ (X ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = X := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

omit [DecidableEq d] in
/-- The constant of the Lipschitz-atomic analysis,
`1 + (2 #d + 1) · 3 · 24^d · 2^(s - d/2)`. -/
noncomputable def analysisConst (d : Type*) [Fintype d] (s : ℝ) : ℝ≥0∞ :=
  1 + (2 * Fintype.card d + 1) * 3 * 24 ^ Fintype.card d *
    ENNReal.dyadicWeight (s - Fintype.card d / 2) 1

omit [DecidableEq d] in
/-- The constant of the Lipschitz-atomic analysis is finite. -/
theorem analysisConst_ne_top (s : ℝ) : analysisConst d s ≠ ∞ := by
  unfold analysisConst
  refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ?_ (by norm_num)) (ENNReal.pow_ne_top (by norm_num)))
    (ENNReal.dyadicWeight_ne_top _ _)⟩
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _),
    ENNReal.one_ne_top⟩

/-- **The coefficients lie in `b^s_{2,q}`**: `‖λ‖_{b^s_{2,q}} ≤ K ‖f‖^ω_{s,q}` with
`K = analysisConst d s`. -/
theorem bNorm_lipCoeffOf_le {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ApproximationScheme.bNorm (fun j => d → Fin (2 ^ j)) s (Fintype.card d / 2) 2 q
      (lipCoeffOf f) ≤ analysisConst d s * modulusNorm s q f := by
  set K₁ := (2 * Fintype.card d + 1) * 3 * 24 ^ Fintype.card d *
    ENNReal.dyadicWeight (s - Fintype.card d / 2) 1
  set L := ENNReal.lqNorm q
    (fun k : ℕ => ENNReal.dyadicWeight s k * modulus f (1 / ((2 ^ k : ℕ) : ℝ)))
  have hL : L ≤ ENNReal.lqNorm q
      (fun k : ℕ => ENNReal.dyadicWeight s k * modulus f (1 / 2 ^ k)) := by
    simp only [L]; push_cast; exact le_rfl
  have h0 : ENNReal.dyadicWeight (s - Fintype.card d / 2) 0 *
      ENNReal.finLqNorm 2 (fun m => ‖lipCoeffOf f 0 m‖ₑ) ≤ ‖f‖ₑ := by
    rw [ENNReal.dyadicWeight_zero_right, one_mul]
    exact finLqNorm_two_le (sum_enorm_mean_sq_le f)
  have hk : ∀ k, ENNReal.dyadicWeight (s - Fintype.card d / 2) (k + 1) *
      ENNReal.finLqNorm 2 (fun m => ‖lipCoeffOf f (k + 1) m‖ₑ) ≤
        K₁ * (ENNReal.dyadicWeight s k * modulus f (1 / ((2 ^ k : ℕ) : ℝ))) := fun k => by
    have hX := finLqNorm_two_le (sum_enorm_pieceCoeff_sq_le f k)
    calc ENNReal.dyadicWeight (s - Fintype.card d / 2) (k + 1) *
          ENNReal.finLqNorm 2 (fun m => ‖lipCoeffOf f (k + 1) m‖ₑ)
        ≤ ENNReal.dyadicWeight (s - Fintype.card d / 2) (k + 1) *
            ((2 * Fintype.card d + 1) * 3 * 24 ^ Fintype.card d *
              ENNReal.dyadicWeight (Fintype.card d / 2) k *
                modulus f (1 / ((2 ^ k : ℕ) : ℝ))) := by gcongr; exact hX
      _ = K₁ * ((ENNReal.dyadicWeight (s - Fintype.card d / 2) k *
            ENNReal.dyadicWeight (Fintype.card d / 2) k) *
              modulus f (1 / ((2 ^ k : ℕ) : ℝ))) := by
          rw [ENNReal.dyadicWeight_add_nat]; simp only [K₁]; ring
      _ = _ := by rw [← ENNReal.dyadicWeight_add, sub_add_cancel]
  calc ApproximationScheme.bNorm (fun j => d → Fin (2 ^ j)) s (Fintype.card d / 2) 2 q
        (lipCoeffOf f)
      ≤ ENNReal.dyadicWeight (s - Fintype.card d / 2) 0 *
            ENNReal.finLqNorm 2 (fun m => ‖lipCoeffOf f 0 m‖ₑ) +
          ENNReal.lqNorm q (fun k => ENNReal.dyadicWeight (s - Fintype.card d / 2) (k + 1) *
            ENNReal.finLqNorm 2 (fun m => ‖lipCoeffOf f (k + 1) m‖ₑ)) :=
        ENNReal.lqNorm_le_head_add_shift hq _
    _ ≤ ‖f‖ₑ + K₁ * L := by
        gcongr
        rw [← ENNReal.lqNorm_const_mul]
        exact ENNReal.lqNorm_mono hk
    _ ≤ analysisConst d s * modulusNorm s q f := by
        rw [analysisConst, modulusNorm]
        calc ‖f‖ₑ + K₁ * L ≤ ‖f‖ₑ + K₁ * ENNReal.lqNorm q
              (fun k : ℕ => ENNReal.dyadicWeight s k * modulus f (1 / 2 ^ k)) := by gcongr
          _ ≤ (1 + K₁) * (‖f‖ₑ + ENNReal.lqNorm q
              (fun k : ℕ => ENNReal.dyadicWeight s k * modulus f (1 / 2 ^ k))) := by
            rw [add_mul, one_mul, mul_add]
            gcongr
            · exact le_self_add
            · exact le_add_self

/-- **Analysis with Lipschitz atoms on the torus**: for `s > 0`, `1 ≤ q ≤ ∞` and `f ∈ L_2(𝕋^d)`
with finite classical Besov norm `‖f‖^ω_{s,q}`, `f = ∑_j ∑_m λ_{j,m} a_{j,m}` in `L_2` with
Lipschitz atoms `a_{j,m}` of support radius `1` and `‖λ‖_{b^s_{2,q}} ≤ K ‖f‖^ω_{s,q}`. -/
theorem exists_lipAtoms {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (hf : modulusNorm s q f < ∞) :
    ∃ (A : ∀ j, (d → Fin (2 ^ j)) → UnitAddTorus d →ᵇ ℂ) (c : ∀ j, (d → Fin (2 ^ j)) → ℝ),
      (∀ j m, IsLipAtom 1 j m (A j m)) ∧
      HasSum (fun j => ∑ m, c j m • BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (A j m))
        f ∧
      ApproximationScheme.bNorm (fun j => d → Fin (2 ^ j)) s (Fintype.card d / 2) 2 q c ≤
        analysisConst d s * modulusNorm s q f := by
  refine ⟨lipAtomOf f, lipCoeffOf f, isLipAtom_lipAtomOf f, ?_, bNorm_lipCoeffOf_le hq f⟩
  simp_rw [sum_lipCoeff_smul_toLp]
  exact hasSum_levels hs hq f hf

/-- **The Lipschitz-atomic characterisation of `B^s_{2,q}(𝕋^d)`**: for `0 < s < 1` and
`1 ≤ q ≤ ∞`, `f ∈ B^s_{2,q}(𝕋^d)` iff `f = ∑_j ∑_m λ_{j,m} a_{j,m}` in `L_2` with Lipschitz atoms
`a_{j,m}` of support radius `1` and coefficients `λ ∈ b^s_{2,q}`; this is the characterisation of
Schneider–Vybíral on `𝕋^d` for `p = 2`. -/
theorem memBesov_iff_exists_lipAtoms {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (trigScheme d).MemBesov volume 2 s q f ↔
      ∃ (A : ∀ j, (d → Fin (2 ^ j)) → UnitAddTorus d →ᵇ ℂ) (c : ∀ j, (d → Fin (2 ^ j)) → ℝ),
        (∀ j m, IsLipAtom 1 j m (A j m)) ∧
        HasSum (fun j => ∑ m, c j m • BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℝ (A j m))
          f ∧
        ApproximationScheme.bNorm (fun j => d → Fin (2 ^ j)) s (Fintype.card d / 2) 2 q c < ∞ := by
  constructor
  · intro hf
    have hmod := (memBesov_iff_modulusNorm_lt_top hs hs1 hq f).1 hf
    obtain ⟨A, c, hA, hsum, hc⟩ := exists_lipAtoms hs hq f hmod
    exact ⟨A, c, hA, hsum, hc.trans_lt (ENNReal.mul_lt_top (analysisConst_ne_top s).lt_top hmod)⟩
  · rintro ⟨A, c, hA, hsum, hc⟩
    exact memBesov_of_lipAtoms 1 hs hs1 hq hA hsum hc

end Torus
