/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Sequences.Dyadic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# The decreasing rearrangement of a null family

For a family `r : ι → ℝ` of nonnegative numbers that tends to zero along the cofinite filter (a
**null family**: only finitely many entries exceed any `t > 0`), the **decreasing
rearrangement** `r* : ℕ → ℝ` lists the entries in decreasing order with multiplicities, padded by
zeros. It is defined without enumerating `ι`:

`r*_n = sup ({0} ∪ {a : a ≤ r_i for n + 1 distinct indices i})`.

**Source.** The definition and its first properties are copied from the Lean project TauCeti
(`TauCeti/Topology/Order/DecreasingRearrangement.lean`, main `0642eae`, Apache 2.0), into the
root namespace and with TauCeti's names, so that a later switch to Mathlib or TauCeti only drops
the copy: `decreasingRearrangement`, its nonnegativity, antitonicity and characterisation by
strict superlevel sets (`lt_decreasingRearrangement_iff`), the count of the entries above
`r*_n` (`card_le_of_forall_decreasingRearrangement_lt`), the equality of the superlevel counts
(`setOf_lt_decreasingRearrangement`), attainment of positive terms
(`exists_eq_decreasingRearrangement`) and `r*_n → 0` (`tendsto_decreasingRearrangement`).

**Sums.** The project adds what best `n`-term approximation needs. The distribution functions
of `r` and `r*` agree at every positive level (`encard_setOf_lt_decreasingRearrangement`), so by
the layer cake formula for sums (`tsum_ofReal_rpow_eq_lintegral`, from Mathlib's
`lintegral_rpow_eq_lintegral_meas_lt_mul` for the counting measure)

`∑_n (r*_n)^p = ∑_i r_i^p`   for every `p > 0`

(`tsum_ofReal_rpow_decreasingRearrangement`); in particular `(n + 1) (r*_n)^p ≤ ∑_i r_i^p`. Two
modifications of `r` compare with `r*`: removing the entries above `r*_N` leaves a family whose
`p`-th power sum is at most `∑_k min(r*_k, r*_N)^p` (`tsum_ite_rpow_le_tsum_min`), and removing
at most `N` entries leaves at least `∑_k (r*_{k+N})^p`
(`tsum_rpow_decreasingRearrangement_add_le`). Cauchy condensation of `r*` gives the **block
inequalities**

`∑_i r_i^p ≤ (r*_0)^p + ∑_l 2^l (r*_{2^l})^p`,   `∑_l 2^l (r*_{2^(l+1)})^p ≤ ∑_i r_i^p`

(`tsum_rpow_le_decreasingRearrangement`, `tsum_two_pow_decreasingRearrangement_le`) and
`∑_l 2^l (r*_{2^l})^p ≤ 2 ∑_i r_i^p` (`tsum_two_pow_mul_decreasingRearrangement_le_two_mul`).
Sums are in `[0, ∞]`, with the terms `ENNReal.ofReal (r*_n) ^ p`.
-/

@[expose] public section

open Filter Finset Topology
open scoped ENNReal

variable {ι : Type*} {r : ι → ℝ}

/-! ### The definition and its first properties (copied from TauCeti) -/

/-- The **decreasing rearrangement** of a family `r : ι → ℝ`, padded by zeros: the supremum of
`0` and of the numbers `a` with `a ≤ r_i` for `n + 1` distinct indices `i`. For a nonnegative
null family, `r*_0 ≥ r*_1 ≥ ⋯` are the entries of `r` in decreasing order, with multiplicities,
followed by zeros if only finitely many entries are positive. Copied from TauCeti
(`TauCeti.decreasingRearrangement`, main `0642eae`). -/
noncomputable def decreasingRearrangement (r : ι → ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 {a | ∃ s : Finset ι, s.card = n + 1 ∧ ∀ i ∈ s, a ≤ r i})

private theorem bddAbove_rearrangementBounds (hr : BddAbove (Set.range r)) (n : ℕ) :
    BddAbove (insert (0 : ℝ) {a | ∃ s : Finset ι, s.card = n + 1 ∧ ∀ i ∈ s, a ≤ r i}) := by
  obtain ⟨M, hM⟩ := hr
  refine ⟨max 0 M, ?_⟩
  rintro a (rfl | ⟨s, hs, ha⟩)
  · exact le_max_left _ _
  · obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < s.card)
    exact (ha i hi).trans ((hM (Set.mem_range_self i)).trans (le_max_right _ _))

/-- For a family that is not bounded above, every term of the rearrangement is `0`, the junk
value of `sSup` on unbounded sets. Copied from TauCeti
(`TauCeti.decreasingRearrangement_eq_zero_of_not_bddAbove`). -/
@[simp]
theorem decreasingRearrangement_eq_zero_of_not_bddAbove
    (hr : ¬ BddAbove (Set.range r)) (n : ℕ) : decreasingRearrangement r n = 0 := by
  apply Real.sSup_of_not_bddAbove
  rintro ⟨M, hM⟩
  apply hr
  have hT : {i | M + 1 ≤ r i}.Finite := by
    by_contra hinf
    obtain ⟨s, hsT, hs⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
    have hmem : M + 1 ∈ insert (0 : ℝ) {a | ∃ s : Finset ι, s.card = n + 1 ∧ ∀ i ∈ s, a ≤ r i} :=
      Set.mem_insert_of_mem _ ⟨s, hs, fun i hi ↦ hsT hi⟩
    linarith [hM hmem]
  obtain ⟨B, hB⟩ := (hT.image r).bddAbove
  refine ⟨max (M + 1) B, ?_⟩
  rintro _ ⟨i, rfl⟩
  by_cases hi : M + 1 ≤ r i
  · exact (hB ⟨i, hi, rfl⟩).trans (le_max_right _ _)
  · exact (not_le.1 hi).le.trans (le_max_left _ _)

/-- The terms of the rearrangement are nonnegative, also for an empty index type. Copied from
TauCeti (`TauCeti.decreasingRearrangement_nonneg`). -/
theorem decreasingRearrangement_nonneg (n : ℕ) : 0 ≤ decreasingRearrangement r n :=
  Real.sSup_nonneg' ⟨0, Set.mem_insert _ _, le_rfl⟩

/-- A lower bound `a` of `n + 1` distinct entries is at most `r*_n`. Copied from TauCeti
(`TauCeti.le_decreasingRearrangement`). -/
theorem le_decreasingRearrangement (hr : BddAbove (Set.range r))
    {n : ℕ} {s : Finset ι} (hs : s.card = n + 1) {a : ℝ} (ha : ∀ i ∈ s, a ≤ r i) :
    a ≤ decreasingRearrangement r n :=
  le_csSup (bddAbove_rearrangementBounds hr n) (Set.mem_insert_of_mem _ ⟨s, hs, ha⟩)

/-- The rearrangement is decreasing: `r*_n ≤ r*_m` for `m ≤ n`. Copied from TauCeti
(`TauCeti.antitone_decreasingRearrangement`). -/
theorem antitone_decreasingRearrangement : Antitone (decreasingRearrangement r) := by
  by_cases hr : BddAbove (Set.range r)
  · intro m n hmn
    apply csSup_le ⟨0, Set.mem_insert _ _⟩
    rintro a (rfl | ⟨s, hs, ha⟩)
    · exact decreasingRearrangement_nonneg m
    · obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (by omega : m + 1 ≤ s.card)
      exact le_decreasingRearrangement hr ht (fun i hi ↦ ha i (hts hi))
  · intro m n _
    rw [decreasingRearrangement_eq_zero_of_not_bddAbove hr,
      decreasingRearrangement_eq_zero_of_not_bddAbove hr]

/-- If a finite set `s` with at most `n` elements contains every entry larger than `a ≥ 0`, then
`r*_n ≤ a`. In particular a family bounded by `a` has `r* ≤ a` (take `s = ∅`). Copied from
TauCeti (`TauCeti.decreasingRearrangement_le_of_card_le`). -/
theorem decreasingRearrangement_le_of_card_le {a : ℝ} (ha : 0 ≤ a)
    {s : Finset ι} {n : ℕ} (hs : s.card ≤ n) (hr : ∀ i ∉ s, r i ≤ a) :
    decreasingRearrangement r n ≤ a := by
  apply csSup_le ⟨0, Set.mem_insert _ _⟩
  rintro b (rfl | ⟨t, ht, hb⟩)
  · exact ha
  · obtain ⟨i, hit, his⟩ := exists_mem_notMem_of_card_lt_card (by omega : s.card < t.card)
    exact (hb i hit).trans (hr i his)

/-- **Strict superlevel sets**: for `a ≥ 0`, `a < r*_n` iff `a < r_i` for `n + 1` distinct
indices `i`. The characterisation keeps repeated values with their multiplicities. Copied from
TauCeti (`TauCeti.lt_decreasingRearrangement_iff`). -/
theorem lt_decreasingRearrangement_iff (hr : BddAbove (Set.range r)) {a : ℝ}
    (ha : 0 ≤ a) (n : ℕ) :
    a < decreasingRearrangement r n ↔
      ∃ s : Finset ι, s.card = n + 1 ∧ ∀ i ∈ s, a < r i := by
  classical
  rw [decreasingRearrangement, lt_csSup_iff (bddAbove_rearrangementBounds hr n)
    ⟨0, Set.mem_insert _ _⟩]
  constructor
  · rintro ⟨b, rfl | ⟨s, hs, hb⟩, hab⟩
    · exact (ha.not_gt hab).elim
    · exact ⟨s, hs, fun i hi ↦ hab.trans_le (hb i hi)⟩
  · rintro ⟨s, hs, hsa⟩
    have hne : s.Nonempty := card_pos.mp (by omega : 0 < s.card)
    refine ⟨s.inf' hne r, Set.mem_insert_of_mem _ ⟨s, hs, fun i hi ↦ inf'_le _ hi⟩, ?_⟩
    exact (lt_inf'_iff hne).mpr hsa

/-- **At most `n` entries exceed `r*_n`**: a finite set of indices whose entries all exceed
`r*_n` has at most `n` elements. Copied from TauCeti
(`TauCeti.card_le_of_forall_decreasingRearrangement_lt`). -/
theorem card_le_of_forall_decreasingRearrangement_lt (hr : BddAbove (Set.range r)) {n : ℕ}
    {s : Finset ι} (hs : ∀ i ∈ s, decreasingRearrangement r n < r i) : s.card ≤ n := by
  by_contra! h
  obtain ⟨u, hu, hu'⟩ := exists_subset_card_eq (Nat.succ_le_of_lt h)
  exact lt_irrefl _ ((lt_decreasingRearrangement_iff hr (decreasingRearrangement_nonneg n)
    n).mpr ⟨u, hu', fun i hi ↦ hs i (hu hi)⟩)

/-- Only finitely many entries exceed `r*_n`. Copied from TauCeti
(`TauCeti.finite_setOf_decreasingRearrangement_lt`). -/
theorem finite_setOf_decreasingRearrangement_lt (hr : BddAbove (Set.range r)) (n : ℕ) :
    {i | decreasingRearrangement r n < r i}.Finite := by
  by_contra h
  obtain ⟨t, ht, ht'⟩ := Set.Infinite.exists_subset_card_eq h (n + 1)
  have := card_le_of_forall_decreasingRearrangement_lt hr fun i hi ↦ ht hi
  omega

/-- **Equal superlevel counts**: if only finitely many entries exceed `a ≥ 0`, then the indices
`n` with `a < r*_n` are exactly the first `#{i : a < r_i}` ones. So the rearrangement keeps the
multiplicities, ties included. Copied from TauCeti (`TauCeti.setOf_lt_decreasingRearrangement`). -/
theorem setOf_lt_decreasingRearrangement {a : ℝ}
    (ha : 0 ≤ a) (hfin : {i | a < r i}.Finite) :
    {n | a < decreasingRearrangement r n} = Set.Iio hfin.toFinset.card := by
  classical
  have hr : BddAbove (Set.range r) := by
    refine ((hfin.image r).bddAbove.union (bddAbove_Iic (a := a))).mono ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : a < r i
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (le_of_not_gt hi)
  ext n
  rw [Set.mem_ofPred_eq, Set.mem_Iio, lt_decreasingRearrangement_iff hr ha]
  constructor
  · rintro ⟨s, hs, hsa⟩
    have hsub : s ⊆ hfin.toFinset := fun i hi ↦ hfin.mem_toFinset.mpr (hsa i hi)
    have := card_le_card hsub
    omega
  · intro hn
    obtain ⟨s, hsub, hs⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hn)
    exact ⟨s, hs, fun i hi ↦ hfin.mem_toFinset.mp (hsub hi)⟩

/-- **Positive terms are entries**: for a null family, every positive term `r*_n` equals some
entry `r_i`. Copied from TauCeti (`TauCeti.exists_eq_decreasingRearrangement`). -/
theorem exists_eq_decreasingRearrangement (hr : Tendsto r cofinite (𝓝 0)) {n : ℕ}
    (hn : 0 < decreasingRearrangement r n) : ∃ i, r i = decreasingRearrangement r n := by
  classical
  set x := decreasingRearrangement r n
  have hfin : {i | x / 2 < r i}.Finite := by
    simpa only [Filter.eventually_cofinite, not_le] using
      hr.eventually_le_const (half_pos hn)
  let t := (hfin.toFinset.filter (fun i ↦ r i < x)).image r
  let s := insert (x / 2) t
  have hs : s.Nonempty := ⟨_, mem_insert_self _ _⟩
  let b := s.max' hs
  have hhalf : x / 2 ≤ b := le_max' s _ (mem_insert_self _ _)
  have hbx : b < x := by
    apply (max'_lt_iff s hs).mpr
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact half_lt_self hn
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
      exact (mem_filter.mp hi).2
  -- Only finitely many entries exceed `x / 2`. If `x` is not attained, the maximum `b` leaves
  -- a gap `(b, x)` without entries, and the superlevels at `b` and at `x` force `x < x`.
  by_contra! hne
  have hstep (i : ι) (hi : b < r i) : x < r i := by
    by_contra! hix
    have hlt : r i < x := hix.lt_of_ne (hne i)
    have hit : i ∈ hfin.toFinset := hfin.mem_toFinset.mpr (hhalf.trans_lt hi)
    have him : r i ∈ s := mem_insert_of_mem (mem_image.mpr ⟨i, mem_filter.mpr ⟨hit, hlt⟩, rfl⟩)
    exact hi.not_ge (le_max' s _ him)
  obtain ⟨u, hu, hur⟩ := (lt_decreasingRearrangement_iff hr.bddAbove_range_of_cofinite
    ((half_pos hn).le.trans hhalf) n).mp hbx
  exact (lt_irrefl x) ((lt_decreasingRearrangement_iff hr.bddAbove_range_of_cofinite hn.le n).mpr
    ⟨u, hu, fun i hi ↦ hstep i (hur i hi)⟩)

/-- **The rearrangement of a null family is null**: `r*_n → 0`. Copied from TauCeti
(`TauCeti.tendsto_decreasingRearrangement`). -/
theorem tendsto_decreasingRearrangement (hr : Tendsto r cofinite (𝓝 0)) :
    Tendsto (decreasingRearrangement r) atTop (𝓝 0) := by
  classical
  refine tendsto_order.mpr ⟨fun a ha ↦ Eventually.of_forall fun n ↦
    ha.trans_le (decreasingRearrangement_nonneg n), fun ε hε ↦ ?_⟩
  have hfin : {i | ε / 2 ≤ r i}.Finite := by
    simpa only [Filter.eventually_cofinite, not_lt] using
      hr.eventually_lt_const (half_pos hε)
  filter_upwards [eventually_ge_atTop hfin.toFinset.card] with n hn
  exact (decreasingRearrangement_le_of_card_le (half_pos hε).le hn
    (fun i hi ↦ le_of_lt (lt_of_not_ge (by simpa using hi)))).trans_lt (half_lt_self hε)

/-! ### Comparison of rearrangements -/

/-- **Monotonicity**: if `s_i ≤ r_i` for every `i` and `r` is bounded above, then
`s*_n ≤ r*_n`, since every lower bound of `n + 1` entries of `s` is one of `r`. -/
theorem decreasingRearrangement_mono {s : ι → ℝ} (hsr : ∀ i, s i ≤ r i)
    (hr : BddAbove (Set.range r)) (n : ℕ) :
    decreasingRearrangement s n ≤ decreasingRearrangement r n := by
  apply csSup_le ⟨0, Set.mem_insert _ _⟩
  rintro a (rfl | ⟨t, ht, ha⟩)
  · exact decreasingRearrangement_nonneg n
  · exact le_decreasingRearrangement hr ht fun i hi => (ha i hi).trans (hsr i)

/-- **Removing at most `N` entries shifts the rearrangement by at most `N`**: if `r` is bounded
above and `Λ` has at most `N` elements, the family `s` equal to `r` off `Λ` and to `0` on `Λ`
has `r*_{n+N} ≤ s*_n`. For `0 ≤ t < r*_{n+N}` there are `n + N + 1` entries above `t`, and at
least `n + 1` of them lie outside `Λ`. -/
theorem decreasingRearrangement_add_le_of_card_le [DecidableEq ι] (hr : BddAbove (Set.range r))
    {Λ : Finset ι} {N : ℕ} (hΛ : Λ.card ≤ N) (n : ℕ) :
    decreasingRearrangement r (n + N) ≤
      decreasingRearrangement (fun i => if i ∈ Λ then 0 else r i) n := by
  set s : ι → ℝ := fun i => if i ∈ Λ then 0 else r i
  have hs : BddAbove (Set.range s) := by
    obtain ⟨M, hM⟩ := hr
    refine ⟨max 0 M, ?_⟩
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ Λ
    · simp [s, hi]
    · simp only [s, hi, ite_false]; exact (hM ⟨i, rfl⟩).trans (le_max_right _ _)
  refine le_of_forall_lt fun t ht => ?_
  rcases lt_or_ge t 0 with ht0 | ht0
  · exact ht0.trans_le (decreasingRearrangement_nonneg n)
  obtain ⟨u, hu, hut⟩ := (lt_decreasingRearrangement_iff hr ht0 (n + N)).1 ht
  have hcard : n + 1 ≤ (u \ Λ).card := by
    have := le_card_sdiff Λ u
    omega
  obtain ⟨v, hvu, hv⟩ := exists_subset_card_eq hcard
  refine (lt_decreasingRearrangement_iff hs ht0 n).2 ⟨v, hv, fun i hi => ?_⟩
  obtain ⟨hiu, hiΛ⟩ := mem_sdiff.1 (hvu hi)
  simpa only [s, hiΛ, ite_false] using hut i hiu

/-! ### Sums of powers -/

/-- **The layer cake formula for sums**: for a nonnegative family `g` on any index set and
`p > 0`, `∑_a g(a)^p = p ∫_0^∞ #{a : t < g(a)} t^(p-1) dt`. It is Mathlib's
`lintegral_rpow_eq_lintegral_meas_lt_mul` for the counting measure on the discrete
`σ`-algebra. -/
theorem tsum_ofReal_rpow_eq_lintegral {α : Type*} {g : α → ℝ} (hg : ∀ a, 0 ≤ g a) {p : ℝ}
    (hp : 0 < p) :
    ∑' a, ENNReal.ofReal (g a) ^ p = ENNReal.ofReal p *
      ∫⁻ t in Set.Ioi 0, {a | t < g a}.encard * ENNReal.ofReal (t ^ (p - 1)) := by
  let _ : MeasurableSpace α := ⊤
  have hms (s : Set α) : MeasurableSet s := MeasurableSpace.measurableSet_top
  have : MeasurableSingletonClass α := ⟨fun _ => hms _⟩
  have h := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul MeasureTheory.Measure.count
    (Filter.Eventually.of_forall hg) measurable_from_top.aemeasurable hp
  rw [MeasureTheory.lintegral_count] at h
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (hg _) hp.le, h,
    MeasureTheory.Measure.count_apply (hms _)]

/-- **Equal distribution functions**: for a null family and `t > 0`, the number of terms of `r*`
above `t` is the number of entries of `r` above `t`. -/
theorem encard_setOf_lt_decreasingRearrangement (hr : Tendsto r cofinite (𝓝 0)) {t : ℝ}
    (ht : 0 < t) : {n | t < decreasingRearrangement r n}.encard = {i | t < r i}.encard := by
  have hfin : {i | t < r i}.Finite := by
    simpa only [Filter.eventually_cofinite, not_le] using hr.eventually_le_const ht
  rw [setOf_lt_decreasingRearrangement ht.le hfin, hfin.encard_eq_coe_toFinset_card,
    ← Finset.coe_range, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- **Rearrangement preserves sums of powers**: for a nonnegative null family and `p > 0`,
`∑_n (r*_n)^p = ∑_i r_i^p`. Both sides are given by the layer cake formula
(`tsum_ofReal_rpow_eq_lintegral`), and the distribution functions agree at every positive level
(`encard_setOf_lt_decreasingRearrangement`). -/
theorem tsum_ofReal_rpow_decreasingRearrangement (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) {p : ℝ} (hp : 0 < p) :
    ∑' n, ENNReal.ofReal (decreasingRearrangement r n) ^ p = ∑' i, ENNReal.ofReal (r i) ^ p := by
  rw [tsum_ofReal_rpow_eq_lintegral (fun n => decreasingRearrangement_nonneg n) hp,
    tsum_ofReal_rpow_eq_lintegral hr0 hp]
  congr 1
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [encard_setOf_lt_decreasingRearrangement hr ht]

/-- **The weak-type bound**: `(n + 1) (r*_n)^p ≤ ∑_i r_i^p` for a nonnegative null family and
`p > 0`, since `r*_0, …, r*_n` are all at least `r*_n`. -/
theorem succ_mul_rpow_decreasingRearrangement_le (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (decreasingRearrangement r n) ^ p ≤
      ∑' i, ENNReal.ofReal (r i) ^ p := by
  rw [← tsum_ofReal_rpow_decreasingRearrangement hr0 hr hp]
  calc ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (decreasingRearrangement r n) ^ p
      = ∑ _k ∈ range (n + 1), ENNReal.ofReal (decreasingRearrangement r n) ^ p := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ range (n + 1), ENNReal.ofReal (decreasingRearrangement r k) ^ p := by
        gcongr with k hk
        exact antitone_decreasingRearrangement (Nat.lt_succ_iff.1 (mem_range.1 hk))
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- `(r*_n)^p ≤ ∑_i r_i^p` for a nonnegative null family and `p > 0`. -/
theorem rpow_decreasingRearrangement_le_tsum (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ENNReal.ofReal (decreasingRearrangement r n) ^ p ≤ ∑' i, ENNReal.ofReal (r i) ^ p :=
  le_trans (le_mul_of_one_le_left zero_le (by exact_mod_cast Nat.succ_pos n))
    (succ_mul_rpow_decreasingRearrangement_le hr0 hr hp n)

/-- A nonnegative family below a null family is null. -/
private theorem tendsto_of_le {s : ι → ℝ} (hs0 : ∀ i, 0 ≤ s i) (hsr : ∀ i, s i ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) : Tendsto s cofinite (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr hs0 hsr

/-- **The tail above `r*_N` removed**: for a nonnegative null family and `p > 0`, the entries
`r_i ≤ r*_N` satisfy `∑_{r_i ≤ r*_N} r_i^p ≤ ∑_k min((r*_k)^p, (r*_N)^p)`. The family `s` with
the entries above `r*_N` set to `0` has `s ≤ r` and `s ≤ r*_N`, so `s*_k ≤ min(r*_k, r*_N)`, and
its power sum is that of `s*`. -/
theorem tsum_ite_rpow_le_tsum_min (hr0 : ∀ i, 0 ≤ r i) (hr : Tendsto r cofinite (𝓝 0))
    {p : ℝ} (hp : 0 < p) (N : ℕ) :
    ∑' i, (if decreasingRearrangement r N < r i then 0 else ENNReal.ofReal (r i) ^ p) ≤
      ∑' k, min (ENNReal.ofReal (decreasingRearrangement r k) ^ p)
        (ENNReal.ofReal (decreasingRearrangement r N) ^ p) := by
  set c := decreasingRearrangement r N
  set s : ι → ℝ := fun i => if c < r i then 0 else r i
  have hs0 : ∀ i, 0 ≤ s i := fun i => by
    by_cases hi : c < r i <;> simp [s, hi, hr0 i]
  have hsr : ∀ i, s i ≤ r i := fun i => by
    by_cases hi : c < r i <;> simp [s, hi, hr0 i]
  have hsc : ∀ i, s i ≤ c := fun i => by
    by_cases hi : c < r i
    · simpa [s, hi] using decreasingRearrangement_nonneg (r := r) N
    · rw [show s i = r i by simp [s, hi]]; exact le_of_not_gt hi
  have hterm : ∀ i, (if c < r i then 0 else ENNReal.ofReal (r i) ^ p) =
      ENNReal.ofReal (s i) ^ p := fun i => by
    by_cases hi : c < r i <;> simp [s, hi, ENNReal.zero_rpow_of_pos hp]
  simp_rw [hterm]
  rw [← tsum_ofReal_rpow_decreasingRearrangement hs0 (tendsto_of_le hs0 hsr hr) hp]
  refine ENNReal.tsum_le_tsum fun k => le_min ?_ ?_
  · gcongr
    exact decreasingRearrangement_mono hsr hr.bddAbove_range_of_cofinite k
  · gcongr
    exact decreasingRearrangement_le_of_card_le (decreasingRearrangement_nonneg N)
      (s := ∅) (Nat.zero_le k) fun i _ => hsc i

/-- **At most `N` entries removed**: for a nonnegative null family, `p > 0` and a set `Λ` of at
most `N` indices, `∑_k (r*_{k+N})^p ≤ ∑_{i ∉ Λ} r_i^p`. The family with the entries in `Λ` set
to `0` has power sum `∑_k (s*_k)^p`, and `r*_{k+N} ≤ s*_k`
(`decreasingRearrangement_add_le_of_card_le`). -/
theorem tsum_rpow_decreasingRearrangement_add_le [DecidableEq ι] (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) {p : ℝ} (hp : 0 < p) {Λ : Finset ι} {N : ℕ}
    (hΛ : Λ.card ≤ N) :
    ∑' k, ENNReal.ofReal (decreasingRearrangement r (k + N)) ^ p ≤
      ∑' i, if i ∈ Λ then 0 else ENNReal.ofReal (r i) ^ p := by
  set s : ι → ℝ := fun i => if i ∈ Λ then 0 else r i
  have hs0 : ∀ i, 0 ≤ s i := fun i => by by_cases hi : i ∈ Λ <;> simp [s, hi, hr0 i]
  have hsr : ∀ i, s i ≤ r i := fun i => by by_cases hi : i ∈ Λ <;> simp [s, hi, hr0 i]
  have hterm : ∀ i, (if i ∈ Λ then 0 else ENNReal.ofReal (r i) ^ p) =
      ENNReal.ofReal (s i) ^ p := fun i => by
    by_cases hi : i ∈ Λ <;> simp [s, hi, ENNReal.zero_rpow_of_pos hp]
  simp_rw [hterm]
  rw [← tsum_ofReal_rpow_decreasingRearrangement hs0 (tendsto_of_le hs0 hsr hr) hp]
  refine ENNReal.tsum_le_tsum fun k => ?_
  gcongr
  exact decreasingRearrangement_add_le_of_card_le hr.bddAbove_range_of_cofinite hΛ k

/-! ### The block inequalities -/

/-- The terms `(r*_n)^p` decrease in `n`. -/
private theorem antitone_rpow_decreasingRearrangement {p : ℝ} (hp : 0 ≤ p) :
    Antitone fun n => ENNReal.ofReal (decreasingRearrangement r n) ^ p := fun _ _ h => by
  dsimp only; gcongr; exact antitone_decreasingRearrangement h

/-- **Upper block inequality**: for a nonnegative null family and `p > 0`,
`∑_i r_i^p ≤ (r*_0)^p + ∑_l 2^l (r*_{2^l})^p`, Cauchy condensation of the decreasing sequence
`(r*_n)^p` (`ENNReal.tsum_pow_mul_le_dyadic`) together with
`tsum_ofReal_rpow_decreasingRearrangement`. -/
theorem tsum_rpow_le_decreasingRearrangement (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) {p : ℝ} (hp : 0 < p) :
    ∑' i, ENNReal.ofReal (r i) ^ p ≤ ENNReal.ofReal (decreasingRearrangement r 0) ^ p +
      ∑' l, 2 ^ l * ENNReal.ofReal (decreasingRearrangement r (2 ^ l)) ^ p := by
  have h := ENNReal.tsum_pow_mul_le_dyadic (antitone_rpow_decreasingRearrangement (r := r) hp.le) 0
  simp only [ENNReal.rpow_zero, one_mul, max_self, zero_add, ENNReal.dyadicWeight_eq_pow,
    ENNReal.rpow_one] at h
  rwa [tsum_ofReal_rpow_decreasingRearrangement hr0 hr hp] at h

/-- **Lower block inequality**: for a nonnegative null family and `p > 0`,
`∑_l 2^l (r*_{2^(l+1)})^p ≤ ∑_i r_i^p`, the lower condensation bound
(`ENNReal.dyadic_le_tsum_pow_mul`) for `(r*_n)^p`. -/
theorem tsum_two_pow_decreasingRearrangement_le (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) {p : ℝ} (hp : 0 < p) :
    ∑' l, 2 ^ l * ENNReal.ofReal (decreasingRearrangement r (2 ^ (l + 1))) ^ p ≤
      ∑' i, ENNReal.ofReal (r i) ^ p := by
  have h := ENNReal.dyadic_le_tsum_pow_mul (antitone_rpow_decreasingRearrangement (r := r) hp.le) 0
  simp only [ENNReal.rpow_zero, one_mul, neg_zero, max_self, zero_add,
    ENNReal.dyadicWeight_eq_pow, ENNReal.rpow_one] at h
  rwa [tsum_ofReal_rpow_decreasingRearrangement hr0 hr hp] at h

/-- **The dyadic sum of the rearrangement**: for a nonnegative null family and `p > 0`,
`∑_l 2^l (r*_{2^l})^p ≤ 2 ∑_i r_i^p`, condensation with constant `2`
(`ENNReal.tsum_two_pow_mul_le_two_mul`) for the decreasing sequence `(r*_n)^p`, together with
`tsum_ofReal_rpow_decreasingRearrangement`. -/
theorem tsum_two_pow_mul_decreasingRearrangement_le_two_mul (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) {p : ℝ} (hp : 0 < p) :
    ∑' l, 2 ^ l * ENNReal.ofReal (decreasingRearrangement r (2 ^ l)) ^ p ≤
      2 * ∑' i, ENNReal.ofReal (r i) ^ p := by
  rw [← tsum_ofReal_rpow_decreasingRearrangement hr0 hr hp]
  exact ENNReal.tsum_two_pow_mul_le_two_mul (antitone_rpow_decreasingRearrangement hp.le)
