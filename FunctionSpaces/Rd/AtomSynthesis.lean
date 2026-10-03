/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.DyadicGrid
public import FunctionSpaces.Rd.LocalMeans
public import FunctionSpaces.Rd.Multipliers

/-!
# Atomic synthesis

Atomic decompositions in the sense of Schneider–Vybíral, for `1 ≤ p < ∞`. A **regular atom** of
level `j ∈ ℕ`, exponent `σ > 0` and order `r` with centre `c` (`Rd.IsRegularAtom`) vanishes
outside the ball `B(c, d 2^(-j))` and satisfies, with a constant `C`,

`‖a‖_p ≤ C 2^(-jn/p)`,  `‖Δ_h^r a‖_p ≤ C 2^(-jn/p) min(1, (2^j ‖h‖)^σ)`,

`n = dim V`. Lip atoms (Schneider–Vybíral, Definition 2.1: `|a| ≤ 1`, `|a(x) - a(y)| ≤ 2^j |x - y|`)
are regular with `σ = r = 1`, smooth `K`-atoms (`|D^α a| ≤ 2^(j|α|)`, Definition 1.3) with
`σ = r = K`; both follow from pointwise bounds (`Rd.isRegularAtom_of_pointwise`).

**Synthesis** (`Rd.modNorm_le_coeffNorm`; Schneider–Vybíral, Theorem 2.6 and Corollary 2.8,
direction ⇐): if the centres of each level have bounded overlap and `F = ∑_j f_j` with the level
sums `f_j = ∑_m λ_{j,m} a_{j,m}`, then for `0 < s < σ`

`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖λ‖_{b^s_{p,q}}`,
`‖λ‖_{b^s_{p,q}} = ‖(2^(j(s - n/p)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}` (`Rd.coeffNorm`).

The proof: by bounded overlap (`Rd.eLpNorm_rpow_le_of_overlap`),
`‖f_j‖_p ≲ 2^(-jn/p) ‖λ_{j,·}‖_{ℓ_p}` and
`ω_r(f_j, 2^(-k))_p ≲ 2^(-jn/p) ‖λ_{j,·}‖_{ℓ_p} min(1, 2^(-(k-j)σ))`
(`Rd.eLpNorm_levelSum_le`, `Rd.modulus_levelSum_le`); the almost diagonal lemma with exponent `σ`
sums the levels. Smooth functions with `‖D^l a‖ ≤ A 2^(jl)` for `l ≤ r` satisfy the pointwise
bounds with `σ = r` (`Rd.enorm_iterDiff_le_of_iteratedFDeriv`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Bounded overlap -/

/-- If every finite set of indices with property `P` has at most `N` elements, the indices with
property `P` form a finite set with at most `N` elements. -/
theorem exists_finset_of_card_le {ι : Type*} {P : ι → Prop} {N : ℕ}
    (h : ∀ S : Finset ι, (∀ m ∈ S, P m) → S.card ≤ N) :
    ∃ T : Finset ι, (∀ m, P m → m ∈ T) ∧ T.card ≤ N := by
  have hfin : {m | P m}.Finite := by
    by_contra hinf
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
    have := h S fun m hm => hS hm
    omega
  exact ⟨hfin.toFinset, fun m hm => hfin.mem_toFinset.2 hm,
    h _ fun m hm => hfin.mem_toFinset.1 hm⟩

/-- **Bounded overlap, pointwise**: if at most `N` of the `g m` are nonzero, then
`‖∑' m, g m‖^p ≤ N^(p-1) ∑' m, ‖g m‖^p` for `p ≥ 1`. -/
theorem enorm_tsum_rpow_le_of_overlap {ι : Type*} (g : ι → ℂ) {N : ℕ}
    (hN : ∀ S : Finset ι, (∀ m ∈ S, g m ≠ 0) → S.card ≤ N) {p : ℝ} (hp : 1 ≤ p) :
    ‖∑' m, g m‖ₑ ^ p ≤ (N : ℝ≥0∞) ^ (p - 1) * ∑' m, ‖g m‖ₑ ^ p := by
  obtain ⟨T, hT, hTN⟩ := exists_finset_of_card_le hN
  have hzero : ∀ m ∉ T, g m = 0 := fun m hm => by_contra fun h => hm (hT m h)
  rw [tsum_eq_sum hzero]
  calc ‖∑ m ∈ T, g m‖ₑ ^ p ≤ (∑ m ∈ T, ‖g m‖ₑ) ^ p :=
        ENNReal.rpow_le_rpow (enorm_sum_le _ _) (by linarith)
    _ ≤ (T.card : ℝ≥0∞) ^ (p - 1) * ∑ m ∈ T, ‖g m‖ₑ ^ p :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hp
    _ ≤ (N : ℝ≥0∞) ^ (p - 1) * ∑' m, ‖g m‖ₑ ^ p :=
        mul_le_mul' (ENNReal.rpow_le_rpow (by exact_mod_cast hTN) (by linarith))
          (ENNReal.sum_le_tsum _)

/-- **Bounded overlap in `L_p`**: if at every point at most `N` of the `g m` are nonzero and
`F = ∑' m, g m` almost everywhere, then `‖F‖_p^p ≤ N^(p-1) ∑' m, ‖g m‖_p^p`. -/
theorem eLpNorm_rpow_le_of_overlap {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Countable ι] {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g : ι → α → ℂ}
    (hg : ∀ m, AEStronglyMeasurable (g m) μ) {N : ℕ}
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, g m x ≠ 0) → S.card ≤ N) {F : α → ℂ}
    (hF : AEStronglyMeasurable F μ) (hFg : ∀ᵐ x ∂μ, F x = ∑' m, g m x) :
    eLpNorm F p μ ^ p.toReal ≤ (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, eLpNorm (g m) p μ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpr : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp hp1
  rw [Interval.eLpNorm_rpow_eq hF hp0 hp]
  calc ∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, ‖g m x‖ₑ ^ p.toReal ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hFg] with x hx
        rw [hx]
        exact enorm_tsum_rpow_le_of_overlap (fun m => g m x) (hN x) hpr
    _ = (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, ∫⁻ x, ‖g m x‖ₑ ^ p.toReal ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (ENNReal.natCast_ne_top N)), lintegral_tsum fun m => ((hg m).enorm.pow_const _)]
    _ = (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, eLpNorm (g m) p μ ^ p.toReal := by
        congr 2
        funext m
        rw [Interval.eLpNorm_rpow_eq (hg m) hp0 hp]

/-! ### Regular atoms -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A **regular atom** of level `j`, exponent `σ` and order `r` with centre `c`, radius factor `d`
and constant `C`: `a = 0` outside `B(c, d 2^(-j))`, `‖a‖_p ≤ C 2^(-jn/p)` and
`‖Δ_h^r a‖_p ≤ C 2^(-jn/p) min(1, (2^j ‖h‖)^σ)`. -/
structure IsRegularAtom (p : ℝ≥0∞) (σ : ℝ) (r : ℕ) (d : ℝ) (C : ℝ≥0∞) (j : ℕ) (c : V)
    (a : V → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable a volume
  eq_zero : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0
  eLpNorm_le : eLpNorm a p volume ≤ C * dyadicWeight (-(finrank ℝ V / p.toReal)) j
  eLpNorm_iterDiff_le : ∀ h : V, eLpNorm ((fwdDiff h)^[r] a) p volume ≤
    C * dyadicWeight (-(finrank ℝ V / p.toReal)) j * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ)

/-- The `ℓ_p`-norm `‖λ_{j,·}‖_{ℓ_p}` of the coefficients of one level. -/
noncomputable def levelNorm (p : ℝ≥0∞) {ι : Type*} (coef : ι → ℂ) : ℝ≥0∞ :=
  (∑' m, ‖coef m‖ₑ ^ p.toReal) ^ (1 / p.toReal)

/-- The `ℓ_p`-norm of the coefficients is monotone in their moduli. -/
theorem levelNorm_mono (p : ℝ≥0∞) {ι : Type*} {coef coef' : ι → ℂ}
    (h : ∀ m, ‖coef m‖ₑ ≤ ‖coef' m‖ₑ) : levelNorm p coef ≤ levelNorm p coef' :=
  ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun m => ENNReal.rpow_le_rpow (h m)
    ENNReal.toReal_nonneg) (div_nonneg zero_le_one ENNReal.toReal_nonneg)

/-- `0 ≤ 1 - 1/p` for `p ≥ 1`. -/
theorem one_sub_one_div_toReal_nonneg {p : ℝ≥0∞} (hp1 : 1 ≤ p) : 0 ≤ 1 - 1 / p.toReal := by
  rcases eq_or_ne p ∞ with hpt | hpt
  · simp [hpt]
  · have : 1 ≤ p.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hpt hp1
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this

/-- The **coefficient quasi-norm** `‖λ‖_{b^s_{p,q}} = ‖(2^(j(s - n/p)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}`. -/
noncomputable def coeffNorm (p : ℝ≥0∞) (n : ℕ) (s : ℝ) (q : ℝ≥0∞) {ι : Type*}
    (coef : ℕ → ι → ℂ) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight (s - n / p.toReal) j * levelNorm p (coef j))

/-! ### Level sums -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Differences of a pointwise convergent sum are the sums of the differences, if the sums
converge at all the points of the difference. -/
theorem iterDiff_tsum_apply [NormedSpace ℝ V] {ι : Type*} (g : ι → V → ℂ)
    (hg : ∀ y, Summable fun m => g m y) (r : ℕ) (h x : V) :
    (fwdDiff h)^[r] (fun y => ∑' m, g m y) x = ∑' m, (fwdDiff h)^[r] (g m) x := by
  simp_rw [iterDiff_apply]
  rw [Summable.tsum_finsetSum fun l _ => (hg _).mul_left _]
  exact Finset.sum_congr rfl fun l _ => (tsum_mul_left).symm

/-- From `X^p ≤ N^(p-1) ∑ (b_m |λ_m|)^p` with `b_m ≤ B` to `X ≤ N^(1-1/p) B ‖λ‖_{ℓ_p}`. -/
theorem le_of_rpow_le_overlap {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*} {X B : ℝ≥0∞}
    {N : ℕ} {b : ι → ℝ≥0∞} (hb : ∀ m, b m ≤ B) (coef : ι → ℂ)
    (hX : X ^ p.toReal ≤ (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, (‖coef m‖ₑ * b m) ^ p.toReal) :
    X ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * B * levelNorm p coef := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← ENNReal.rpow_le_rpow_iff hpos]
  refine hX.trans ?_
  rw [levelNorm, ENNReal.mul_rpow_of_nonneg _ _ hpos.le, ENNReal.mul_rpow_of_nonneg _ _ hpos.le,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (1 - 1 / p.toReal) * p.toReal = p.toReal - 1 by
      field_simp, show 1 / p.toReal * p.toReal = 1 by field_simp, ENNReal.rpow_one, mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le, mul_comm]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (hb m) hpos.le) le_rfl

/-- The pointwise sums of a level converge: at most `N` atoms of the level with nonzero
coefficients are nonzero at a point. -/
theorem summable_levelSum {ι : Type*} {p : ℝ≥0∞} {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j N : ℕ}
    (c : ι → V) (a : ι → V → ℂ) (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtom p σ r d C j (c m) (a m)) (y : V) :
    Summable fun m => coef m * a m y := by
  have hd : ∀ m, coef m * a m y ≠ 0 → coef m ≠ 0 ∧ ‖y - c m‖ ≤ (d + r) / 2 ^ j := fun m hm => by
    have ha' : a m y ≠ 0 := right_ne_zero_of_mul hm
    have h1 : ‖y - c m‖ ≤ d / 2 ^ j := not_lt.1 fun h => ha' ((ha m).eq_zero y h)
    exact ⟨left_ne_zero_of_mul hm, h1.trans (div_le_div_of_nonneg_right
      (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) (by positivity))⟩
  obtain ⟨T, hT, -⟩ := exists_finset_of_card_le (P := fun m => coef m * a m y ≠ 0)
    fun S hS => hN y S fun m hm => hd m (hS m hm)
  exact summable_of_ne_finset_zero fun m hm => by_contra fun h => hm (hT m h)

/-- **The level sums in `L_p`**: `‖∑_m λ_m a_m‖_p ≤ N^(1-1/p) C 2^(-jn/p) ‖λ‖_{ℓ_p}`. -/
theorem eLpNorm_levelSum_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j N : ℕ} (c : ι → V) (a : ι → V → ℂ) (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtom p σ r d C j (c m) (a m)) {F : V → ℂ} (hF : AEStronglyMeasurable F volume)
    (hFa : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x) :
    eLpNorm F p volume ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
      (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) * levelNorm p coef := by
  have hg : ∀ m, AEStronglyMeasurable (fun x => coef m * a m x) volume := fun m =>
    aestronglyMeasurable_const.mul (ha m).aestronglyMeasurable
  have hover : ∀ x (S : Finset ι), (∀ m ∈ S, coef m * a m x ≠ 0) → S.card ≤ N := fun x S hS =>
    hN x S fun m hm => by
      have ha' : a m x ≠ 0 := right_ne_zero_of_mul (hS m hm)
      have h1 : ‖x - c m‖ ≤ d / 2 ^ j := not_lt.1 fun h => ha' ((ha m).eq_zero x h)
      exact ⟨left_ne_zero_of_mul (hS m hm), h1.trans (div_le_div_of_nonneg_right
        (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) (by positivity))⟩
  have h := eLpNorm_rpow_le_of_overlap hp1 hp hg hover hF hFa
  refine le_of_rpow_le_overlap hp1 hp (fun m => (ha m).eLpNorm_le) coef (h.trans_eq ?_)
  congr 2
  funext m
  rw [show (fun x => coef m * a m x) = coef m • a m from rfl, eLpNorm_const_smul]

/-- **Moduli of the level sums**: `ω_r(∑_m λ_m a_m, 2^(-k))_p ≤
2^r N^(1-1/p) C 2^(-jn/p) ‖λ‖_{ℓ_p} c_{kj}` with `c_{kj} = 2^(-(k-j)σ)` for `j ≤ k` and `1`
otherwise. -/
theorem modulus_levelSum_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    {σ : ℝ} (hσ : 0 ≤ σ) {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j N : ℕ} (c : ι → V) (a : ι → V → ℂ)
    (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtom p σ r d C j (c m) (a m)) {F : V → ℂ} (hF : AEStronglyMeasurable F volume)
    (hFa : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x) (k : ℕ) :
    modulus volume r p F (1 / 2 ^ k) ≤ 2 ^ r * ((N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
      (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) * levelNorm p coef) *
        (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) := by
  set B := (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) *
    levelNorm p coef
  split_ifs with hjk
  · refine iSup₂_le fun h hh => ?_
    have hsum : ∀ y, Summable fun m => coef m * a m y := summable_levelSum c a coef hN ha
    have hae : (fwdDiff h)^[r] F =ᵐ[volume] fun x => ∑' m, coef m * (fwdDiff h)^[r] (a m) x := by
      filter_upwards [iterDiff_congr_ae hFa r h] with x hx
      rw [hx, iterDiff_tsum_apply _ hsum]
      refine tsum_congr fun m => ?_
      rw [show (fun y => coef m * a m y) = coef m • a m from rfl, fwdDiff_iter_const_smul]
      rfl
    have hg : ∀ m, AEStronglyMeasurable (fun x => coef m * (fwdDiff h)^[r] (a m) x) volume :=
      fun m => aestronglyMeasurable_const.mul
        (aestronglyMeasurable_iterDiff (ha m).aestronglyMeasurable r h)
    have hhk : ‖h‖ ≤ 1 / 2 ^ j := hh.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ one_le_two hjk))
    have hover : ∀ x (S : Finset ι), (∀ m ∈ S, coef m * (fwdDiff h)^[r] (a m) x ≠ 0) →
        S.card ≤ N := fun x S hS => hN x S fun m hm => by
      have hne : (fwdDiff h)^[r] (a m) x ≠ 0 := right_ne_zero_of_mul (hS m hm)
      rw [iterDiff_apply] at hne
      obtain ⟨l, hl, hl0⟩ : ∃ l ∈ Finset.range (r + 1), a m (x + (l : ℝ) • h) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (Finset.sum_eq_zero fun l hl => by rw [hcon l hl, mul_zero])
      have h1 : ‖x + (l : ℝ) • h - c m‖ ≤ d / 2 ^ j :=
        not_lt.1 fun h' => hl0 ((ha m).eq_zero _ h')
      have hl' : (l : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have h2 : ‖(l : ℝ) • h‖ ≤ r / 2 ^ j := by
        rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg l)]
        calc (l : ℝ) * ‖h‖ ≤ r * (1 / 2 ^ j) :=
              mul_le_mul hl' hhk (norm_nonneg h) (Nat.cast_nonneg r)
          _ = r / 2 ^ j := by ring
      refine ⟨left_ne_zero_of_mul (hS m hm), ?_⟩
      calc ‖x - c m‖ = ‖(x + (l : ℝ) • h - c m) - (l : ℝ) • h‖ := by congr 1; abel
        _ ≤ ‖x + (l : ℝ) • h - c m‖ + ‖(l : ℝ) • h‖ := norm_sub_le _ _
        _ ≤ d / 2 ^ j + r / 2 ^ j := add_le_add h1 h2
        _ = (d + r) / 2 ^ j := by ring
    have hbound := eLpNorm_rpow_le_of_overlap hp1 hp hg hover
      (aestronglyMeasurable_iterDiff hF r h) hae
    have hmin : min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ) ≤ dyadicWeight (-σ) (k - j) := by
      refine (min_le_right _ _).trans ?_
      have hk : (2 : ℝ) ^ j * ‖h‖ ≤ (1 / 2 ^ (k - j)) := by
        calc (2 : ℝ) ^ j * ‖h‖ ≤ 2 ^ j * (1 / 2 ^ k) :=
              mul_le_mul_of_nonneg_left hh (by positivity)
          _ = 1 / 2 ^ (k - j) := by
              rw [show k = (k - j) + j by omega, pow_add]
              field_simp
              simp
      calc ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ ≤ ENNReal.ofReal (1 / 2 ^ (k - j)) ^ σ :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hk) hσ
        _ = dyadicWeight (-σ) (k - j) := by
            rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
              ENNReal.ofReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_neg, ← ENNReal.rpow_mul,
              ENNReal.dyadicWeight]
            congr 1
            ring
    calc eLpNorm ((fwdDiff h)^[r] F) p volume
        ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j *
            dyadicWeight (-σ) (k - j)) * levelNorm p coef :=
          le_of_rpow_le_overlap hp1 hp (fun m => ((ha m).eLpNorm_iterDiff_le h).trans
            (mul_le_mul' le_rfl hmin)) coef (hbound.trans_eq (by
              congr 2
              funext m
              rw [show (fun x => coef m * (fwdDiff h)^[r] (a m) x) =
                coef m • (fwdDiff h)^[r] (a m) from rfl, eLpNorm_const_smul]))
      _ ≤ 2 ^ r * B * dyadicWeight (-σ) (k - j) := by
          calc (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j *
                dyadicWeight (-σ) (k - j)) * levelNorm p coef
              = 1 * B * dyadicWeight (-σ) (k - j) := by
                simp only [B]
                ring
            _ ≤ 2 ^ r * B * dyadicWeight (-σ) (k - j) := by
                gcongr
                exact one_le_pow₀ one_le_two
  · rw [mul_one]
    exact (modulus_le hF hp1 r _).trans (mul_le_mul' le_rfl
      (eLpNorm_levelSum_le hp1 hp c a coef hN ha hF hFa))


/-! ### The synthesis theorem -/

/-- The constant `N^(1-1/p) C ((1 - 2^(-s))⁻¹ + 2^r ((1 - 2^(-(σ-s)))⁻¹ + (1 - 2^(-s))⁻¹))` of the
atomic synthesis. -/
noncomputable def atomSynthConst (p : ℝ≥0∞) (N : ℕ) (C : ℝ≥0∞) (r : ℕ) (s σ : ℝ) : ℝ≥0∞ :=
  (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C * ((1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ +
    2 ^ r * ((1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹))

/-- The constant of the atomic synthesis is finite for `C < ∞` and `0 < s < σ`. -/
theorem atomSynthConst_ne_top {p : ℝ≥0∞} (hp1 : 1 ≤ p) (N : ℕ) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (r : ℕ) {s σ : ℝ} (hs : 0 < s) (hsσ : s < σ) :
    atomSynthConst p N C r s σ ≠ ∞ := by
  have hexp : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (ENNReal.natCast_ne_top N)) hC)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top hs,
      ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2
        ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith),
          ENNReal.one_sub_two_rpow_neg_inv_ne_top hs⟩)⟩)

/-- **Atomic synthesis** (Schneider–Vybíral, Theorem 2.6 and Corollary 2.8, direction ⇐): if the
centres of the atoms with nonzero coefficients have overlap at most `N` on balls of radius
`(d + r) 2^(-j)` at every level `j`,
`F = ∑_j f_j` in `L_p` with the level sums `f_j = ∑_m λ_{j,m} a_{j,m}` of regular atoms of
exponent `σ` and order `r`, and `0 < s < σ`, then
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖λ‖_{b^s_{p,q}}`. -/
theorem modNorm_le_coeffNorm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {N : ℕ} (c : ℕ → ι → V) (a : ℕ → ι → V → ℂ)
    (coef : ℕ → ι → ℂ)
    (hN : ∀ j x (S : Finset ι), (∀ m ∈ S, coef j m ≠ 0 ∧ ‖x - c j m‖ ≤ (d + r) / 2 ^ j) →
      S.card ≤ N)
    (ha : ∀ j m, IsRegularAtom p σ r d C j (c j m) (a j m)) {f : ℕ → Lp ℂ p (volume : Measure V)}
    (hf : ∀ j, ∀ᵐ x ∂volume, f j x = ∑' m, coef j m * a j m x)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F))
    {s : ℝ} (hs : 0 < s) (hsσ : s < σ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
      atomSynthConst p N C r s σ * coeffNorm p (finrank ℝ V) s q coef := by
  have hp1 : 1 ≤ p := Fact.out
  set K0 := (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C
  set b : ℕ → ℝ≥0∞ := fun j => dyadicWeight (-(finrank ℝ V / p.toReal)) j * levelNorm p (coef j)
  set X := lqNorm q (fun j => dyadicWeight s j * b j)
  have hX : coeffNorm p (finrank ℝ V) s q coef = X := by
    simp only [coeffNorm, X, b]
    congr 1
    funext j
    rw [← mul_assoc, ← ENNReal.dyadicWeight_add, ← sub_eq_add_neg]
  -- the level sums
  have hlevel : ∀ j, ‖f j‖ₑ ≤ K0 * b j := fun j => by
    rw [Lp.enorm_def]
    refine (eLpNorm_levelSum_le hp1 hp (c j) (a j) (coef j) (hN j) (ha j)
      (Lp.aestronglyMeasurable (f j)) (hf j)).trans_eq ?_
    simp only [K0, b]
    ring
  have hlevelMod : ∀ j k, lpModulus p r (f j) k ≤
      2 ^ r * K0 * ((if j ≤ k then dyadicWeight (-σ) (k - j) else 1) * b j) := fun j k => by
    rw [lpModulus]
    refine (modulus_levelSum_le hp1 hp (hs.le.trans hsσ.le) (c j) (a j) (coef j) (hN j) (ha j)
      (Lp.aestronglyMeasurable (f j)) (hf j) k).trans_eq ?_
    simp only [K0, b]
    ring
  -- the norm
  have hnorm : ‖F‖ₑ ≤ K0 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
    have h1 : ‖F‖ₑ ≤ ∑' j, ‖f j‖ₑ :=
      le_tsum_of_tendsto_sum (C := 1) ENNReal.one_ne_top (fun x y => enorm_add_le x y)
        (fun x => by rw [one_mul]) hF
    have h2 : ∀ j, ‖f j‖ₑ ≤ K0 * (dyadicWeight (-s) j * X) := fun j => by
      have hXj : dyadicWeight s j * b j ≤ X :=
        ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne' (fun j => dyadicWeight s j * b j) j
      calc ‖f j‖ₑ ≤ K0 * b j := hlevel j
        _ = K0 * (dyadicWeight (-s) j * (dyadicWeight s j * b j)) := by
            rw [← mul_assoc (dyadicWeight (-s) j), ENNReal.dyadicWeight_neg_mul_self, one_mul]
        _ ≤ K0 * (dyadicWeight (-s) j * X) := by gcongr
    calc ‖F‖ₑ ≤ ∑' j, K0 * (dyadicWeight (-s) j * X) := h1.trans (ENNReal.tsum_le_tsum h2)
      _ = K0 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_dyadicWeight_neg]
          ring
  -- the moduli
  have hmod : ∀ k, lpModulus p r F k ≤ 2 ^ r * K0 *
      ∑' j, (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) * b j := fun k => by
    have h1 : lpModulus p r F k ≤ ∑' j, lpModulus p r (f j) k :=
      le_tsum_of_tendsto_sum (C := 2 ^ r) (by simp) (fun x y => lpModulus_add_le r x y k)
        (fun x => lpModulus_le r x k) hF
    refine h1.trans ?_
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => hlevelMod j k
  have hlq : lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
      2 ^ r * K0 * (((1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * X) := by
    calc lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)
        ≤ lqNorm q (fun k => 2 ^ r * K0 * (dyadicWeight s k *
            ∑' j, (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) * b j)) :=
          ENNReal.lqNorm_mono fun k => by
            calc dyadicWeight s k * lpModulus p r F k
                ≤ dyadicWeight s k * (2 ^ r * K0 *
                    ∑' j, (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) * b j) :=
                  mul_le_mul' le_rfl (hmod k)
              _ = _ := by ring
      _ = 2 ^ r * K0 * lqNorm q (fun k => dyadicWeight s k *
            ∑' j, (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) * b j) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ 2 ^ r * K0 * (((1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * X) :=
          mul_le_mul' le_rfl (ENNReal.lqNorm_almostDiagonal_le hq s σ b)
  rw [hX]
  calc ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)
      ≤ K0 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X +
          2 ^ r * K0 * (((1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * X) :=
        add_le_add hnorm hlq
    _ = atomSynthConst p N C r s σ * X := by
        simp only [atomSynthConst, K0]
        ring

/-- `‖(…, 0, x, 0, …)‖_{ℓ_q} = x` for a sequence with one nonzero term. -/
theorem lqNorm_ite_eq {q : ℝ≥0∞} (hq : 1 ≤ q) (j : ℕ) (x : ℝ≥0∞) :
    lqNorm q (fun i => if i = j then x else 0) = x := by
  rcases eq_or_ne q ∞ with rfl | hqt
  · rw [ENNReal.lqNorm_top]
    refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le j (by simp))
    split_ifs <;> simp
  · have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
    have hpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
    rw [ENNReal.lqNorm_eq_tsum hq0 hqt]
    have h : (fun i => (if i = j then x else 0) ^ q.toReal) =
        fun i => if i = j then x ^ q.toReal else 0 := funext fun i => by
      split_ifs <;> simp [ENNReal.zero_rpow_of_pos hpos]
    rw [h, tsum_ite_eq, one_div, ENNReal.rpow_rpow_inv hpos.ne']

/-- The zero function is a regular atom at every level. -/
theorem isRegularAtom_zero {p : ℝ≥0∞} {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j : ℕ} {c : V} :
    IsRegularAtom p σ r d C j c (0 : V → ℂ) where
  aestronglyMeasurable := aestronglyMeasurable_const
  eq_zero _ _ := rfl
  eLpNorm_le := by simp
  eLpNorm_iterDiff_le h := by
    have h0 : (fwdDiff h)^[r] (0 : V → ℂ) = 0 := by
      induction r with
      | zero => rfl
      | succ r ih =>
        rw [Function.iterate_succ_apply', ih, fwdDiff_eq_sub]
        funext x
        simp
    simp [h0]

/-- **Synthesis of one level**: for regular atoms of level `j` with overlap `N` and
`F = ∑_m λ_m a_m` in `L_p`, `0 < s < σ`:
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K 2^(j(s - n/p)) ‖λ‖_{ℓ_p}`, the case of
`Rd.modNorm_le_coeffNorm` with one nonzero level. -/
theorem modNorm_level_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {N : ℕ} (j : ℕ) (c : ι → V) (a : ι → V → ℂ)
    (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtom p σ r d C j (c m) (a m)) {F : Lp ℂ p (volume : Measure V)}
    (hF : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x) {s : ℝ} (hs : 0 < s) (hsσ : s < σ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
      atomSynthConst p N C r s σ *
        (dyadicWeight (s - finrank ℝ V / p.toReal) j * levelNorm p coef) := by
  classical
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set coef' : ℕ → ι → ℂ := fun i m => if i = j then coef m else 0
  set a' : ℕ → ι → V → ℂ := fun i m => if i = j then a m else 0
  set f' : ℕ → Lp ℂ p (volume : Measure V) := fun i => if i = j then F else 0
  have hN' : ∀ i x (S : Finset ι), (∀ m ∈ S, coef' i m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ i) →
      S.card ≤ N := fun i x S hS => by
    by_cases hij : i = j
    · subst hij
      exact hN x S fun m hm => by simpa [coef'] using hS m hm
    · have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun m hm =>
        (hS m hm).1 (by simp [coef', hij])
      simp [hS0]
  have ha' : ∀ i m, IsRegularAtom p σ r d C i (c m) (a' i m) := fun i m => by
    by_cases hij : i = j
    · subst hij
      simpa [a'] using ha m
    · simpa [a', hij] using (isRegularAtom_zero : IsRegularAtom p σ r d C i (c m) 0)
  have hf' : ∀ i, ∀ᵐ x ∂volume, f' i x = ∑' m, coef' i m * a' i m x := fun i => by
    by_cases hij : i = j
    · subst hij
      simpa [f', coef', a'] using hF
    · filter_upwards [Lp.coeFn_zero ℂ p (volume : Measure V)] with x hx
      simp [f', coef', a', hij]
  have hF' : Tendsto (fun J => ∑ i ∈ Finset.range (J + 1), f' i) atTop (𝓝 F) := by
    refine tendsto_atTop_of_eventually_const (i₀ := j) fun J hJ => ?_
    rw [Finset.sum_ite_eq' (Finset.range (J + 1)) j (fun _ => F)]
    simp [Finset.mem_range, Nat.lt_succ_of_le hJ]
  refine (modNorm_le_coeffNorm hp (fun _ => c) (fun i => a' i) coef' hN' ha' hf' hF' hs hsσ
    hq).trans_eq ?_
  congr 1
  rw [coeffNorm]
  have hseq : (fun i => dyadicWeight (s - finrank ℝ V / p.toReal) i * levelNorm p (coef' i)) =
      fun i => if i = j then dyadicWeight (s - finrank ℝ V / p.toReal) j * levelNorm p coef
        else 0 := funext fun i => by
    by_cases hij : i = j
    · subst hij
      simp [coef']
    · have h0 : levelNorm p (coef' i) = 0 := by
        simp [levelNorm, coef', hij, ENNReal.zero_rpow_of_pos hpos, hpos]
      simp [hij, h0]
  rw [hseq, lqNorm_ite_eq hq]

/-! ### Atoms from pointwise bounds -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `‖g‖_p ≤ B μ(S)^(1/p)` for a function with `|g| ≤ B` that vanishes outside `S`. -/
theorem eLpNorm_le_of_bound_of_support {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {g : α → ℂ} (hg : AEStronglyMeasurable g μ) {S : Set α}
    (hS : ∀ x ∉ S, g x = 0) {B : ℝ≥0∞} (hB : ∀ x, ‖g x‖ₑ ≤ B) :
    eLpNorm g p μ ≤ B * μ S ^ (1 / p.toReal) := by
  have hsupp : Function.support g ⊆ S := fun x hx => by
    by_contra h
    exact (Function.mem_support.1 hx) (hS x h)
  rw [← eLpNorm_restrict_eq_of_support_subset hg hsupp]
  refine (eLpNorm_le_of_ae_enorm_bound hg.restrict (Eventually.of_forall hB)).trans_eq ?_
  rw [Measure.restrict_apply_univ, one_div, smul_eq_mul]

/-- The volume of a ball of radius `d 2^(-j)` is `d^n |B_1| 2^(-jn)`. -/
theorem volume_closedBall_div_two_pow {d : ℝ} (hd : 0 ≤ d) (j : ℕ) (z : V) :
    volume (closedBall z (d / 2 ^ j)) = ENNReal.ofReal (d ^ finrank ℝ V) *
      volume (ball (0 : V) 1) * dyadicWeight (-(finrank ℝ V : ℝ)) j := by
  rw [Measure.addHaar_closedBall _ _ (by positivity), div_eq_mul_one_div, mul_pow,
    ENNReal.ofReal_mul (by positivity), ofReal_one_div_two_pow_pow]
  ring

/-- `(X 2^(-jn))^(1/p) = X^(1/p) 2^(-jn/p)`. -/
theorem rpow_mul_dyadicWeight_neg (X : ℝ≥0∞) (n : ℕ) (p : ℝ≥0∞) (j : ℕ) :
    (X * dyadicWeight (-(n : ℝ)) j) ^ (1 / p.toReal) =
      X ^ (1 / p.toReal) * dyadicWeight (-(n / p.toReal)) j := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one ENNReal.toReal_nonneg),
    ENNReal.dyadicWeight_rpow]
  congr 2
  ring

/-- **Atoms from pointwise bounds**: a function that vanishes outside `B̄(c, d 2^(-j))` with
`|a| ≤ A` and `|Δ_h^r a| ≤ A min(1, (2^j ‖h‖)^σ)` is a regular atom with the constant
`A ((r + 1) d^n |B_1|)^(1/p)`. The support of `Δ_h^r a` lies in `r + 1` translated balls. -/
theorem isRegularAtom_of_pointwise {p : ℝ≥0∞} {σ : ℝ} {r : ℕ} {d : ℝ} (hd : 0 ≤ d)
    {A : ℝ≥0∞} {j : ℕ} {c : V} {a : V → ℂ} (hm : AEStronglyMeasurable a volume)
    (h0 : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0) (hle : ∀ x, ‖a x‖ₑ ≤ A)
    (hdiff : ∀ h x, ‖(fwdDiff h)^[r] a x‖ₑ ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ)) :
    IsRegularAtom p σ r d (A * (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ V) *
      volume (ball (0 : V) 1))) ^ (1 / p.toReal)) j c a := by
  set K := ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1)
  have hexp : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hball : ∀ z : V, volume (closedBall z (d / 2 ^ j)) ^ (1 / p.toReal) ≤
      (((r + 1 : ℕ) : ℝ≥0∞) * K) ^ (1 / p.toReal) * dyadicWeight (-(finrank ℝ V / p.toReal)) j :=
    fun z => by
      rw [volume_closedBall_div_two_pow hd j z, ← rpow_mul_dyadicWeight_neg]
      refine ENNReal.rpow_le_rpow ?_ hexp
      rw [mul_assoc (((r + 1 : ℕ) : ℝ≥0∞))]
      exact le_mul_of_one_le_left' (by exact_mod_cast Nat.succ_pos r)
  refine ⟨hm, h0, ?_, fun h => ?_⟩
  · refine (eLpNorm_le_of_bound_of_support hm (S := closedBall c (d / 2 ^ j)) (fun x hx => ?_)
      hle).trans ?_
    · rw [mem_closedBall, dist_eq_norm, not_le] at hx
      exact h0 x hx
    · rw [mul_assoc]
      exact mul_le_mul' le_rfl (hball c)
  · set T := ⋃ l ∈ Finset.range (r + 1), closedBall (c - (l : ℝ) • h) (d / 2 ^ j)
    have hT : ∀ x ∉ T, (fwdDiff h)^[r] a x = 0 := fun x hx => by
      rw [iterDiff_apply]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hxl : x ∉ closedBall (c - (l : ℝ) • h) (d / 2 ^ j) := fun hx' =>
        hx (Set.mem_biUnion hl hx')
      rw [mem_closedBall, dist_eq_norm, not_le] at hxl
      rw [h0 _ (by rwa [show x + (l : ℝ) • h - c = x - (c - (l : ℝ) • h) by abel]), mul_zero]
    have hvol : volume T ^ (1 / p.toReal) ≤
        (((r + 1 : ℕ) : ℝ≥0∞) * K) ^ (1 / p.toReal) *
          dyadicWeight (-(finrank ℝ V / p.toReal)) j := by
      rw [← rpow_mul_dyadicWeight_neg]
      refine ENNReal.rpow_le_rpow ((measure_biUnion_finset_le _ _).trans_eq ?_) hexp
      simp_rw [volume_closedBall_div_two_pow hd j]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [K]
      push_cast
      ring
    refine (eLpNorm_le_of_bound_of_support (aestronglyMeasurable_iterDiff hm r h) hT
      (hdiff h)).trans ?_
    calc A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ) * volume T ^ (1 / p.toReal)
        ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ) * ((((r + 1 : ℕ) : ℝ≥0∞) * K) ^
            (1 / p.toReal) * dyadicWeight (-(finrank ℝ V / p.toReal)) j) :=
          mul_le_mul' le_rfl hvol
      _ = _ := by ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Smooth atoms**: a smooth function vanishing outside `B̄(c, d 2^(-j))` with
`‖D^l a‖ ≤ A 2^(jl)` for `l ≤ r` satisfies the pointwise bounds of `Rd.isRegularAtom_of_pointwise`
with exponent `σ = r` and the constant `2^r A`: `|Δ_h^r a| ≤ A (2^j ‖h‖)^r` by the mean value
theorem and `|Δ_h^r a| ≤ 2^r A`. -/
theorem enorm_iterDiff_le_of_iteratedFDeriv {a : V → ℂ}
    (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) {r j : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l a x‖ ≤ A * 2 ^ (j * l)) (h x : V) :
    ‖(fwdDiff h)^[r] a x‖ₑ ≤
      ENNReal.ofReal (2 ^ r * A) * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)) := by
  have h1 : ‖(fwdDiff h)^[r] a x‖ ≤ A * 2 ^ (j * r) * ‖h‖ ^ r :=
    norm_iterDiff_le_of_iteratedFDeriv ha (hD r le_rfl) h x
  have h2 : ‖(fwdDiff h)^[r] a x‖ ≤ 2 ^ r * A := by
    rw [iterDiff_apply]
    calc ‖∑ l ∈ Finset.range (r + 1), ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) *
          a (x + (l : ℝ) • h)‖
        ≤ ∑ l ∈ Finset.range (r + 1), ‖((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) *
            a (x + (l : ℝ) • h)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * A := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          simpa using hD 0 (Nat.zero_le r) (x + (l : ℝ) • h)
      _ = 2 ^ r * A := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose r
  rcases le_total 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)) with hmin | hmin
  · rw [min_eq_left hmin, mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h2
  · rw [min_eq_right hmin, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (Nat.cast_nonneg r),
      Real.rpow_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
    rw [mul_pow, pow_mul]
    have hr : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ one_le_two
    calc A * (2 ^ j) ^ r * ‖h‖ ^ r = 1 * (A * ((2 ^ j) ^ r * ‖h‖ ^ r)) := by ring
      _ ≤ 2 ^ r * (A * ((2 ^ j) ^ r * ‖h‖ ^ r)) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ = 2 ^ r * A * ((2 ^ j) ^ r * ‖h‖ ^ r) := by ring

end Rd
