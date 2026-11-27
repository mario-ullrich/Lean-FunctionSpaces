/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.HaarQuasiBanach

/-!
# The Haar system as a Schauder basis for `0 < p ≤ 1`

The Haar system in breadth-first order, `φ_0 = 1` and `φ_{2^k+i} = h_{k,i}` (`Haar.haarSystem`),
has the coefficient functionals `c_n(f) = ∫_0^1 φ_n f` (`Haar.haarSystemCoeff`), defined on
`L_1[0, 1]`, and the partial sums `S_n f = ∑_{i<n} c_i(f) φ_i` (`Haar.haarPartialSum`). The partial
sums of length `2^k` are the conditional expectations `E[f | ℱ_k]`
(`Haar.sum_haarSystem_two_pow_ae_eq`), and for `n = 2^k + i` the remainder `f - S_n f` is
`f - E[f | ℱ_{k+1}]` plus a part of the Haar sum of level `k`
(`Haar.sub_sum_haarSystem_ae_eq`), whose quasi-norm is at most the level norm `H_k(f)`.

For `0 < p ≤ 1`, `s > 1/p - 1` and `0 < q < ∞` the Haar system is a **Schauder basis** of the
approximation space `E_{s,q}` of the step couple, in the dyadic quasi-norm
`‖f‖_p + ‖(2^(ks) E(2^k, f))_k‖_{ℓ_q}`:

* every `f ∈ E_{s,q}` is the limit of its partial sums
  (`Haar.tendsto_eNormDyadic_sub_haarPartialSum`): `‖f - S_n f‖_p^p ≤ ∑_{j ≥ k} H_j(f)^p`,
  `E(2^l, f - S_n f) = E(2^l, f)` for `l > k`, and the tails of the convergent `ℓ_q` sums tend to
  `0` since `q < ∞`;
* the coefficients are unique (`Haar.eq_haarSystemCoeff_of_tendsto`), since `E_{s,q}` embeds into
  `L_1` (`Haar.eLpNorm_one_le_eNormDyadic`) and the `c_n` are bounded on `L_1`.

For `1/p - 1 < s < 1/p` the space is `B^s_{p,q,1}[0, 1]` of the first modulus
(`Haar.lqNorm_modulus_lt_top_iff_haarCoeff_of_le_one`), and this is the Schauder basis property
of the Haar system there (P. Oswald, *On inequalities for spline approximation and spline systems
in the space `L_p` (`0 < p < 1`)*, Gdańsk 1979, 1981; P. Oswald, *Haar system as Schauder basis in
Besov spaces: The limiting cases for `0 < p ≤ 1`*, arXiv:1808.08156, Theorem 1 with `d = 1`). For
`1/2 < p < 1`, `1/p - 1 < s < 1` and `q < ∞` the Haar system is also a Schauder basis of the
Fourier-analytic `B^s_{p,q}[0, 1]` (H. Triebel, *On Haar bases in Besov spaces*, Serdica 4, 1978;
Oswald 2018, Theorem 2); that space is not formalised here.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open ENNReal (dyadicWeight lqNorm)

namespace Haar

variable {p : ℝ≥0∞} {s : ℝ} {q : ℝ≥0∞}

/-! ### Coefficients and partial sums -/

/-- The **coefficient** of `f` at the `n`-th function of the Haar system, `c_n(f) = ∫_0^1 φ_n f`,
the `n`-th coefficient in the Haar basis (`Haar.haarBasis_repr_apply`) for `f ∈ L_2`. -/
noncomputable def haarSystemCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x, (haarSystem n x : ℂ) * f x ∂vol

/-- `c_0(f) = ∫_0^1 f`. -/
theorem haarSystemCoeff_zero (f : ℝ → ℂ) : haarSystemCoeff f 0 = ∫ x, f x ∂vol := by
  simp [haarSystemCoeff]

/-- `c_{2^k+i}(f) = ⟨f, h_{k,i}⟩` for `0 ≤ i < 2^k`. -/
theorem haarSystemCoeff_two_pow_add (f : ℝ → ℂ) {k i : ℕ} (hi : i < 2 ^ k) :
    haarSystemCoeff f (2 ^ k + i) = haarCoeff f k i := by
  rw [haarSystemCoeff, haarSystem_two_pow_add hi]
  rfl

variable (p) in
/-- The function `φ_n` of the Haar system as an element of `L_p[0, 1]`, for every `p`. -/
noncomputable def haarSystemLp (n : ℕ) : Lp ℂ p vol := (memLp_haarSystem p n).toLp _

/-- A finite combination `∑_{n<N} a_n φ_n` in `L_p[0, 1]` is the function `∑_{n<N} a_n φ_n`
almost everywhere. -/
theorem coeFn_sum_smul_haarSystemLp (a : ℕ → ℂ) (N : ℕ) :
    ⇑(∑ n ∈ Finset.range N, a n • haarSystemLp p n) =ᵐ[vol]
      fun x => ∑ n ∈ Finset.range N, a n * (haarSystem n x : ℂ) := by
  have hi : ∀ᵐ x ∂vol, ∀ n, (a n • haarSystemLp p n) x = a n * (haarSystem n x : ℂ) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (a n) (haarSystemLp p n),
      MemLp.coeFn_toLp (memLp_haarSystem p n)] with x h1 h2
    rw [h1, Pi.smul_apply, haarSystemLp, h2, smul_eq_mul]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range N) (fun n => a n • haarSystemLp p n), hi]
    with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun n _ => h2 n

/-- A function of the Haar system times an integrable function is integrable, since `φ_n` is
bounded and measurable (`Haar.exists_abs_haarSystem_le`). -/
theorem integrable_haarSystem_mul {F : ℝ → ℂ} (hF : Integrable F vol) (n : ℕ) :
    Integrable (fun x => (haarSystem n x : ℂ) * F x) vol := by
  obtain ⟨C, hC⟩ := exists_abs_haarSystem_le n
  exact hF.bdd_mul (Complex.measurable_ofReal.comp (measurable_haarSystem n)).aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x)

/-- A finite combination `∑_{n<N} a_n φ_n` of the Haar system is integrable on `[0, 1]`. -/
theorem integrable_sum_mul_haarSystem (a : ℕ → ℂ) (N : ℕ) :
    Integrable (fun x => ∑ n ∈ Finset.range N, a n * (haarSystem n x : ℂ)) vol :=
  integrable_finsetSum _ fun n _ => ((memLp_haarSystem 1 n).integrable le_rfl).const_mul (a n)

variable (p) in
/-- The **partial sum** `S_N f = ∑_{n<N} c_n(f) φ_n` of the Haar expansion of `f`, in
`L_p[0, 1]`. -/
noncomputable def haarPartialSum (f : ℝ → ℂ) (N : ℕ) : Lp ℂ p vol :=
  ∑ n ∈ Finset.range N, haarSystemCoeff f n • haarSystemLp p n

/-- A function of the Haar system of index `i < 2^l` is measurable for `ℱ_l`. -/
theorem stronglyMeasurable_haarSystem {i l : ℕ} (hi : i < 2 ^ l) :
    StronglyMeasurable[dyadicFiltration l] (fun x => (haarSystem i x : ℂ)) := by
  rcases eq_or_ne i 0 with rfl | hi0
  · simp only [haarSystem_zero, Complex.ofReal_one]
    exact stronglyMeasurable_const
  obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_two_pow_add hi0
  have hjl : j + 1 ≤ l := by
    by_contra h
    have : 2 ^ l ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
    omega
  rw [haarSystem_two_pow_add hm]
  have h : StronglyMeasurable[dyadicFiltration (j + 1)] (fun x => (haarFunction j m x : ℂ)) :=
    (Complex.measurable_ofReal.comp ((measurable_from_top (f := fun n : ℤ =>
      if n = 2 * (m : ℤ) then (2 : ℝ) ^ ((j : ℝ) / 2)
      else if n = 2 * (m : ℤ) + 1 then -(2 : ℝ) ^ ((j : ℝ) / 2) else 0)).comp
        (comap_measurable (m := ⊤) (dyadicIndex (j + 1))))).stronglyMeasurable
  exact h.mono (dyadicFiltration.mono hjl)

/-- A combination of the first `N ≤ 2^l` functions of the Haar system is `ℱ_l`-measurable. -/
theorem sum_smul_haarSystemLp_mem {a : ℕ → ℂ} {N l : ℕ} (hN : N ≤ 2 ^ l) :
    ∑ n ∈ Finset.range N, a n • haarSystemLp p n ∈
      lpMeasSubgroup ℂ (dyadicFiltration l) p vol :=
  mem_lpMeasSubgroup_iff_aestronglyMeasurable.2
    ⟨fun x => ∑ n ∈ Finset.range N, a n * (haarSystem n x : ℂ),
      Finset.stronglyMeasurable_fun_sum _ fun _ hn => stronglyMeasurable_const.mul
        (stronglyMeasurable_haarSystem ((Finset.mem_range.1 hn).trans_le hN)),
      coeFn_sum_smul_haarSystemLp a N⟩

/-- **The partial sums of length `2^k` are the conditional expectations**: for integrable `f`,
`∑_{n<2^k} c_n(f) φ_n = E[f | ℱ_k]`, by `E[f | ℱ_0] = ∫_0^1 f` and the Haar sums of the martingale
differences (`Haar.condExp_zero_ae_eq`, `Haar.condExp_succ_sub_ae_eq`). -/
theorem sum_haarSystem_two_pow_ae_eq {f : ℝ → ℂ} (hf : Integrable f vol) (k : ℕ) :
    (fun x => ∑ n ∈ Finset.range (2 ^ k), haarSystemCoeff f n * (haarSystem n x : ℂ)) =ᵐ[vol]
      vol[f | dyadicFiltration k] := by
  induction k with
  | zero =>
    filter_upwards [condExp_zero_ae_eq hf] with x hx
    simp [hx, haarSystemCoeff_zero]
  | succ k ih =>
    filter_upwards [ih, condExp_succ_sub_ae_eq k hf] with x h1 h2
    rw [Pi.sub_apply] at h2
    rw [pow_succ, mul_two, Finset.sum_range_add, h1, eq_add_of_sub_eq' h2,
      ← Fin.sum_univ_eq_sum_range (fun i => haarSystemCoeff f (2 ^ k + i) *
        (haarSystem (2 ^ k + i) x : ℂ))]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [haarSystemCoeff_two_pow_add f i.isLt, haarSystem_two_pow_add i.isLt]

/-- A sum over `m < n` of the terms with `m < i ≤ n` is the sum over `m < i`. -/
theorem sum_fin_ite_lt {M : Type*} [AddCommMonoid M] {n i : ℕ} (hi : i ≤ n) (g : ℕ → M) :
    ∑ m : Fin n, (if (m : ℕ) < i then g m else 0) = ∑ j ∈ Finset.range i, g j := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < i then g m else 0),
    ← Finset.sum_range_add_sum_Ico _ hi]
  rw [Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.1 hj),
    Finset.sum_eq_zero fun j hj => ite_eq_right (not_lt.2 (Finset.mem_Ico.1 hj).1), add_zero]

/-- **The remainder of a Haar partial sum**: for integrable `f` and `i ≤ 2^k`,
`f - S_{2^k+i} f = (f - E[f | ℱ_{k+1}]) + ∑_{m<2^k} c'_m h_{k,m}` almost everywhere, with
`c'_m = ⟨f, h_{k,m}⟩` for `m ≥ i` and `c'_m = 0` otherwise. -/
theorem sub_sum_haarSystem_ae_eq {f : ℝ → ℂ} (hf : Integrable f vol) {k i : ℕ} (hi : i ≤ 2 ^ k) :
    (fun x => f x - ∑ n ∈ Finset.range (2 ^ k + i), haarSystemCoeff f n * (haarSystem n x : ℂ))
      =ᵐ[vol] (f - vol[f | dyadicFiltration (k + 1)]) + fun x => ∑ m : Fin (2 ^ k),
        (if i ≤ (m : ℕ) then haarCoeff f k ((m : ℕ) : ℤ) else 0) *
          (haarFunction k ((m : ℕ) : ℤ) x : ℂ) := by
  filter_upwards [sum_haarSystem_two_pow_ae_eq hf k, condExp_succ_sub_ae_eq k hf] with x h1 h2
  rw [Pi.sub_apply] at h2
  have hA : ∑ j ∈ Finset.range i, haarSystemCoeff f (2 ^ k + j) * (haarSystem (2 ^ k + j) x : ℂ) =
      ∑ m : Fin (2 ^ k), (if (m : ℕ) < i then
        haarCoeff f k ((m : ℕ) : ℤ) * (haarFunction k ((m : ℕ) : ℤ) x : ℂ) else 0) := by
    rw [sum_fin_ite_lt hi (fun j : ℕ => haarCoeff f k (j : ℤ) * (haarFunction k (j : ℤ) x : ℂ))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 2 ^ k := (Finset.mem_range.1 hj).trans_le hi
    rw [haarSystemCoeff_two_pow_add f hj', haarSystem_two_pow_add hj']
  have hAB : (∑ m : Fin (2 ^ k), (if (m : ℕ) < i then
        haarCoeff f k ((m : ℕ) : ℤ) * (haarFunction k ((m : ℕ) : ℤ) x : ℂ) else 0)) +
      ∑ m : Fin (2 ^ k), (if i ≤ (m : ℕ) then haarCoeff f k ((m : ℕ) : ℤ) else 0) *
        (haarFunction k ((m : ℕ) : ℤ) x : ℂ) =
      ∑ m : Fin (2 ^ k), haarCoeff f k ((m : ℕ) : ℤ) * (haarFunction k ((m : ℕ) : ℤ) x : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℕ) < i
    · rw [ite_eq_left hm, ite_eq_right (not_le.2 hm), zero_mul, add_zero]
    · rw [ite_eq_right hm, ite_eq_left (not_lt.1 hm), zero_add]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [Finset.sum_range_add, h1, hA]
  linear_combination h2 - hAB

/-- The part `∑_{m ≥ i} ⟨f, h_{k,m}⟩ h_{k,m}` of the Haar sum of level `k` has quasi-norm at
most the level norm `H_k(f)` (`Haar.eLpNorm_sum_haar`), for `0 < p < ∞`. -/
theorem eLpNorm_sum_haar_ite_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : ℝ → ℂ) (k i : ℕ) :
    eLpNorm (fun x => ∑ m : Fin (2 ^ k),
      (if i ≤ (m : ℕ) then haarCoeff f k ((m : ℕ) : ℤ) else 0) *
        (haarFunction k ((m : ℕ) : ℤ) x : ℂ)) p vol ≤ haarLevelNorm p f k := by
  rw [eLpNorm_sum_haar hp0 hp, haarLevelNorm]
  refine mul_le_mul_right (ENNReal.lqNorm_mono fun m => ?_) _
  split_ifs <;> simp

/-- **The quasi-norm of the remainder**: for `0 < p ≤ 1`, integrable `f` and `i ≤ 2^k`,
`‖f - S_{2^k+i} f‖_p^p ≤ ∑_{j ≥ 0} H_{k+j}(f)^p`
(`Haar.sub_sum_haarSystem_ae_eq`, `Haar.eLpNorm_sub_condExp_rpow_le_tsum`). -/
theorem eLpNorm_sub_sum_haarSystem_rpow_le (hp0 : p ≠ 0) (hp1 : p ≤ 1) {f : ℝ → ℂ}
    (hf : Integrable f vol) {k i : ℕ} (hi : i ≤ 2 ^ k) :
    eLpNorm (fun x => f x - ∑ n ∈ Finset.range (2 ^ k + i),
      haarSystemCoeff f n * (haarSystem n x : ℂ)) p vol ^ p.toReal ≤
        ∑' j, haarLevelNorm p f (k + j) ^ p.toReal := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hT : ∑' j, haarLevelNorm p f (k + j) ^ p.toReal = haarLevelNorm p f k ^ p.toReal +
      ∑' j, haarLevelNorm p f (k + 1 + j) ^ p.toReal := by
    rw [tsum_eq_zero_add' CompleteLattice.summable]
    congr 1
    exact tsum_congr fun j => by rw [show k + (j + 1) = k + 1 + j by omega]
  rw [eLpNorm_congr_ae (sub_sum_haarSystem_ae_eq hf hi), hT,
    add_comm (haarLevelNorm p f k ^ p.toReal)]
  exact (eLpNorm_add_rpow_le_of_le_one hp0 hp1 _ _).trans
    (add_le_add (eLpNorm_sub_condExp_rpow_le_tsum hp0 hp1 hf (k + 1))
      (ENNReal.rpow_le_rpow (eLpNorm_sum_haar_ite_le hp0 hp f k i) hρ.le))

/-- The E-functional of the step couple at `2^l` ignores the `ℱ_l`-measurable elements:
`E(2^l, f - a) = E(2^l, f)` (`InterpCouple.eFunctional_ofMonotoneSubgroups_sub_of_mem`). -/
theorem eFunctional_stepCouple_sub_of_mem {l : ℕ} {a : Lp ℂ p vol}
    (ha : a ∈ lpMeasSubgroup ℂ (dyadicFiltration l) p vol) (f : Lp ℂ p vol) :
    (stepCouple p).eFunctional ((2 ^ l : ℕ) : ℝ≥0∞) (f - a) =
      (stepCouple p).eFunctional ((2 ^ l : ℕ) : ℝ≥0∞) f :=
  InterpCouple.eFunctional_ofMonotoneSubgroups_sub_of_mem ha f

/-- The partial sum `S_N f` is `ℱ_l`-measurable for `N ≤ 2^l`. -/
theorem haarPartialSum_mem (f : ℝ → ℂ) {N l : ℕ} (hN : N ≤ 2 ^ l) :
    haarPartialSum p f N ∈ lpMeasSubgroup ℂ (dyadicFiltration l) p vol :=
  sum_smul_haarSystemLp_mem hN

/-- The partial sum `S_N f` in `L_p` is the function `∑_{n<N} c_n(f) φ_n` almost everywhere. -/
theorem coeFn_haarPartialSum (f : ℝ → ℂ) (N : ℕ) :
    haarPartialSum p f N =ᵐ[vol]
      fun x => ∑ n ∈ Finset.range N, haarSystemCoeff f n * (haarSystem n x : ℂ) :=
  coeFn_sum_smul_haarSystemLp _ N

/-! ### Convergence of the partial sums -/

/-- **The dyadic norm of the remainder**: for `f ∈ L_p[0, 1]` and `i ≤ 2^k`, with
`R = f - S_{2^k+i} f`, `‖R‖_p + ‖(2^(ls) E(2^l, R))_l‖_{ℓ_q}` is at most
`‖R‖_p + C_q (‖R‖_p ‖(2^(ls) 1_{l ≤ k})_l‖_{ℓ_q} + ‖(2^(ls) E(2^l, f) 1_{l ≥ k+1})_l‖_{ℓ_q})`,
since `E(2^l, R) ≤ ‖R‖_p` and, for `l ≥ k + 1`, `E(2^l, R) = E(2^l, f)`
(`Haar.eFunctional_stepCouple_sub_of_mem`). -/
theorem eNormDyadic_sub_haarPartialSum_le (f : Lp ℂ p vol) {k i : ℕ} (hi : i ≤ 2 ^ k) :
    (stepCouple p).eNormDyadic s q (f - haarPartialSum p f (2 ^ k + i)) ≤
      ‖f - haarPartialSum p f (2 ^ k + i)‖ₑ + ENNReal.LpAddConst q *
        (‖f - haarPartialSum p f (2 ^ k + i)‖ₑ *
          lqNorm q (fun l => if l ≤ k then dyadicWeight s l else 0) +
        lqNorm q (fun l => if k + 1 ≤ l then
          dyadicWeight s l * (stepCouple p).eFunctional ((2 ^ l : ℕ) : ℝ≥0∞) f else 0)) := by
  set R := f - haarPartialSum p f (2 ^ k + i)
  have hN : ∀ l, k + 1 ≤ l → 2 ^ k + i ≤ 2 ^ l := fun l hl =>
    calc 2 ^ k + i ≤ 2 ^ k + 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by rw [pow_succ, mul_two]
      _ ≤ 2 ^ l := Nat.pow_le_pow_right two_pos hl
  have hpt : ∀ l, dyadicWeight s l * (stepCouple p).eFunctional ((2 ^ l : ℕ) : ℝ≥0∞) R ≤
      ‖R‖ₑ * (if l ≤ k then dyadicWeight s l else 0) + (if k + 1 ≤ l then
        dyadicWeight s l * (stepCouple p).eFunctional ((2 ^ l : ℕ) : ℝ≥0∞) f else 0) := fun l => by
    by_cases hl : l ≤ k
    · rw [ite_eq_left hl, ite_eq_right (by omega), add_zero, mul_comm ‖R‖ₑ]
      gcongr
      exact InterpCouple.eFunctional_le_norm0 InterpCouple.ofMonotoneSubgroups_norm1_zero R
    · rw [ite_eq_right hl, ite_eq_left (by omega), mul_zero, zero_add,
        eFunctional_stepCouple_sub_of_mem (haarPartialSum_mem f (hN l (by omega))) f]
  rw [InterpCouple.eNormDyadic]
  refine add_le_add le_rfl ((ENNReal.lqNorm_mono hpt).trans ?_)
  refine (ENNReal.lqNorm_add_le' q _ _).trans ?_
  rw [ENNReal.lqNorm_const_mul]

/-- **The weighted tails of the level norms tend to `0`**: for `0 < p ≤ 1`, `s > 0`,
`0 < q < ∞` and `‖(2^(ks) H_k(f))_k‖_{ℓ_q} < ∞`, `2^(ks) (∑_{j ≥ 0} H_{k+j}(f)^p)^(1/p) → 0`.
Hardy's inequality for tails in `ℓ_{q/p}` with the exponent `sp > 0`
(`ENNReal.lqNorm_rpow_le_of_rpow_le_tsum`) puts these numbers in `ℓ_q`, and the terms of a
sequence in `ℓ_q`, `q < ∞`, tend to `0` (`ENNReal.tendsto_zero_of_lqNorm_ne_top`). -/
theorem tendsto_dyadicWeight_mul_tsum_haarLevelNorm (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 0 < s)
    (hq0 : q ≠ 0) (hq : q ≠ ∞) {f : ℝ → ℂ}
    (hH : lqNorm q (fun k => dyadicWeight s k * haarLevelNorm p f k) < ∞) :
    Tendsto (fun k => dyadicWeight s k *
      (∑' j, haarLevelNorm p f (k + j) ^ p.toReal) ^ p.toReal⁻¹) atTop (𝓝 0) := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hk : ∀ k, ((∑' j, haarLevelNorm p f (k + j) ^ p.toReal) ^ p.toReal⁻¹) ^ p.toReal ≤
      1 * ∑' i, dyadicWeight 0 i * haarLevelNorm p f (k + i) ^ p.toReal := fun k => by
    rw [ENNReal.rpow_inv_rpow hρ.ne']
    simp only [ENNReal.dyadicWeight_zero_left, one_mul, le_refl]
  have h := (ENNReal.lqNorm_rpow_le_of_rpow_le_tsum (y := haarLevelNorm p f) hρ hk s q).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.one_lt_top (ENNReal.hardyConst_ne_top
      (by rw [sub_zero]; exact mul_pos hs hρ) _).lt_top)
      (ENNReal.rpow_lt_top_of_nonneg hρ.le hH.ne))
  rw [ENNReal.rpow_lt_top_iff_of_pos hρ] at h
  exact ENNReal.tendsto_zero_of_lqNorm_ne_top hq0 hq h.ne

/-- **The bound for the remainder at level `k`**: for `0 < p ≤ 1`, `s ≥ 0`, `q ≠ 0`,
integrable `f ∈ L_p[0, 1]` and `i ≤ 2^k`, the dyadic norm of `f - S_{2^k+i} f` is at most
`W_k + C_q (W_k γ_{s,q} + ‖(2^(ls) E(2^l, f) 1_{l ≥ k+1})_l‖_{ℓ_q})`, where
`W_k = 2^(ks) (∑_{j ≥ 0} H_{k+j}(f)^p)^(1/p)` and `γ_{s,q} = dyadicGeomConst s q`
(`Haar.eNormDyadic_sub_haarPartialSum_le`, `Haar.eLpNorm_sub_sum_haarSystem_rpow_le`,
`ENNReal.lqNorm_ite_le_dyadicWeight_le`). -/
theorem eNormDyadic_sub_haarPartialSum_le_of_le_one (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 0 ≤ s)
    (hq0 : q ≠ 0) {f : Lp ℂ p vol} (hf : Integrable f vol) {k i : ℕ} (hi : i ≤ 2 ^ k) :
    (stepCouple p).eNormDyadic s q (f - haarPartialSum p f (2 ^ k + i)) ≤
      dyadicWeight s k * (∑' j, haarLevelNorm p f (k + j) ^ p.toReal) ^ p.toReal⁻¹ +
        ENNReal.LpAddConst q *
          (dyadicWeight s k * (∑' j, haarLevelNorm p f (k + j) ^ p.toReal) ^ p.toReal⁻¹ *
            ENNReal.dyadicGeomConst s q +
          lqNorm q (fun l => if k + 1 ≤ l then
            dyadicWeight s l * (stepCouple p).eFunctional ((2 ^ l : ℕ) : ℝ≥0∞) f else 0)) := by
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hρ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set T := ∑' j, haarLevelNorm p f (k + j) ^ p.toReal
  have hR : ‖f - haarPartialSum p f (2 ^ k + i)‖ₑ ≤ T ^ p.toReal⁻¹ := by
    rw [ENNReal.le_rpow_inv_iff hρ, Lp.eNorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
      (EventuallyEq.rfl.sub (coeFn_haarPartialSum _ _)))]
    exact eLpNorm_sub_sum_haarSystem_rpow_le hp0 hp1 hf hi
  have hR' : ‖f - haarPartialSum p f (2 ^ k + i)‖ₑ ≤ dyadicWeight s k * T ^ p.toReal⁻¹ :=
    hR.trans (le_mul_of_one_le_left' (ENNReal.one_le_dyadicWeight hs k))
  refine (eNormDyadic_sub_haarPartialSum_le f hi).trans
    (add_le_add hR' (mul_le_mul_right (add_le_add ?_ le_rfl) _))
  calc ‖f - haarPartialSum p f (2 ^ k + i)‖ₑ *
        lqNorm q (fun l => if l ≤ k then dyadicWeight s l else 0)
      ≤ T ^ p.toReal⁻¹ * (dyadicWeight s k * ENNReal.dyadicGeomConst s q) :=
        mul_le_mul' hR (ENNReal.lqNorm_ite_le_dyadicWeight_le hs hq0 k)
    _ = dyadicWeight s k * T ^ p.toReal⁻¹ * ENNReal.dyadicGeomConst s q := by
        ring

/-- **The Haar partial sums converge in the approximation spaces of the step couple**: for
`0 < p ≤ 1`, `s > 1/p - 1`, `0 < q < ∞` and `f ∈ E_{s,q}`,
`‖f - S_n f‖_p + ‖(2^(ks) E(2^k, f - S_n f))_k‖_{ℓ_q} → 0`. For `2^k ≤ n < 2^(k+1)` the bound of
`Haar.eNormDyadic_sub_haarPartialSum_le_of_le_one` tends to `0` as `k → ∞`
(`Haar.tendsto_dyadicWeight_mul_tsum_haarLevelNorm`, `ENNReal.tendsto_lqNorm_ite_le`). With the
uniqueness of the coefficients (`Haar.eq_haarSystemCoeff_of_tendsto`) this is the Schauder basis
property of the Haar system (Oswald 1981; Oswald 2018, Theorem 1 with `d = 1`). -/
theorem tendsto_eNormDyadic_sub_haarPartialSum (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (hs : 1 / p.toReal - 1 < s) (hq0 : q ≠ 0) (hq : q ≠ ∞) {f : Lp ℂ p vol}
    (hf : (stepCouple p).MemEMethod s q f) :
    Tendsto (fun n => (stepCouple p).eNormDyadic s q (f - haarPartialSum p f n)) atTop (𝓝 0) := by
  have hs0 := pos_of_one_div_sub_one_lt hp0 hp1 hs
  have hN : (stepCouple p).eNormDyadic s q f < ∞ :=
    (InterpCouple.memEMethod_iff_eNormDyadic_lt_top (A := stepCouple p)
      InterpCouple.ofMonotoneSubgroups_norm1_zero
      (fun _ hb => InterpCouple.eq_zero_of_ofMonotoneSubgroups_norm1_lt_one hb) hs0.le
      (Or.inl hs0) hq0).1 hf
  have hfi := integrable_of_eNormDyadic_lt_top hp0 hp1 hs hq0 hN
  have hW := tendsto_dyadicWeight_mul_tsum_haarLevelNorm hp0 hp1 hs0 hq0 hq
    (lqNorm_haarLevelNorm_lt_top hp0 hp1 hs hq0 hN)
  have hE : lqNorm q (fun l => dyadicWeight s l *
      (stepCouple p).eFunctional ((2 ^ l : ℕ) : ℝ≥0∞) f) ≠ ∞ := (le_add_self.trans_lt hN).ne
  have hG : ENNReal.dyadicGeomConst s q ≠ ∞ := ENNReal.dyadicGeomConst_ne_top hs0 q
  have htail := (ENNReal.tendsto_lqNorm_ite_le hq0 hq hE).comp (tendsto_add_atTop_nat 1)
  have hB := hW.add (ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.mul_const hW (Or.inr hG)).add
    htail) (Or.inr (ENNReal.LpAddConst_lt_top q).ne))
  simp only [zero_mul, zero_add, mul_zero] at hB
  have hlog : Tendsto (Nat.log 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun K => ⟨2 ^ K, fun n hn => Nat.le_log_of_pow_le one_lt_two hn⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hB.comp hlog)
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  dsimp only [Function.comp_apply]
  set k := Nat.log 2 n
  have h1 : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self one_lt_two n
  obtain ⟨i, hni⟩ := Nat.exists_eq_add_of_le h1
  have hi : i ≤ 2 ^ k := by
    rw [pow_succ] at h2
    omega
  have h := eNormDyadic_sub_haarPartialSum_le_of_le_one hp0 hp1 hs0.le hq0 hfi hi
  rw [← hni] at h
  exact h

/-! ### Uniqueness of the coefficients -/

/-- **The coefficient functionals are bounded on `L_1`**: for every `n` there is a finite `M`
with `|c_n(g)| ≤ M ∫_0^1 |g|` for all `g`, since `φ_n` is bounded
(`Haar.exists_abs_haarSystem_le`). -/
theorem exists_enorm_haarSystemCoeff_le (n : ℕ) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ g : ℝ → ℂ, ‖haarSystemCoeff g n‖ₑ ≤ M * ∫⁻ x, ‖g x‖ₑ ∂vol := by
  obtain ⟨C, hC⟩ := exists_abs_haarSystem_le n
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun g =>
    (eNorm_integral_le_lintegral_eNorm _).trans ?_⟩
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [eNorm_mul]
  gcongr
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (hC x)

/-- Functions that agree almost everywhere on `[0, 1]` have the same coefficients. -/
theorem haarSystemCoeff_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[vol] g) (n : ℕ) :
    haarSystemCoeff f n = haarSystemCoeff g n :=
  integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- **The coefficients of a finite combination**: for integrable `F`,
`c_i(F - ∑_{n<N} a_n φ_n) = c_i(F) - a_i` for `i < N`, by the orthonormality of the Haar system
(`Haar.integral_haarSystem_mul`). -/
theorem haarSystemCoeff_sub_sum {F : ℝ → ℂ} (hF : Integrable F vol) (a : ℕ → ℂ) {i N : ℕ}
    (hiN : i < N) :
    haarSystemCoeff (fun x => F x - ∑ n ∈ Finset.range N, a n * (haarSystem n x : ℂ)) i =
      haarSystemCoeff F i - a i := by
  have hsum : ∫ x, (haarSystem i x : ℂ) * ∑ n ∈ Finset.range N, a n * (haarSystem n x : ℂ) ∂vol =
      a i := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun n _ => by
      simpa [mul_left_comm] using (integrable_haarSystem_mul
        ((memLp_haarSystem 1 n).integrable le_rfl) i).const_mul (a n)]
    have hn : ∀ n, ∫ x, (haarSystem i x : ℂ) * (a n * (haarSystem n x : ℂ)) ∂vol =
        a n * (if i = n then 1 else 0) := fun n => by
      rw [show (fun x => (haarSystem i x : ℂ) * (a n * (haarSystem n x : ℂ))) =
          fun x => a n * ((haarSystem i x * haarSystem n x : ℝ) : ℂ) from funext fun x => by
            push_cast; ring, integral_const_mul, integral_complex_ofReal,
        integral_haarSystem_mul]
      split_ifs <;> simp
    simp_rw [hn, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 hiN)]
  rw [haarSystemCoeff, haarSystemCoeff, ← hsum, ← integral_sub (integrable_haarSystem_mul hF i)
    (integrable_haarSystem_mul (integrable_sum_mul_haarSystem a N) i)]
  simp_rw [mul_sub]

/-- **The coefficients of the Haar expansion are unique**: for `0 < p ≤ 1`, `s > 1/p - 1` and
`q ≠ 0`, if `∑_{n<N} a_n φ_n → f` in the dyadic quasi-norm `‖·‖_p + ‖(2^(ks) E(2^k, ·))_k‖_{ℓ_q}`,
then `a_n = c_n(f)` for every `n`. The dyadic norm bounds the `L_1` norm
(`Haar.eLpNorm_one_le_eNormDyadic`), on which every `c_n` is bounded
(`Haar.exists_enorm_haarSystemCoeff_le`), and `c_i(f - ∑_{n<N} a_n φ_n) = c_i(f) - a_i` for
`N > i` (`Haar.haarSystemCoeff_sub_sum`). -/
theorem eq_haarSystemCoeff_of_tendsto (hp0 : p ≠ 0) (hp1 : p ≤ 1) (hs : 1 / p.toReal - 1 < s)
    (hq0 : q ≠ 0) {f : Lp ℂ p vol} {a : ℕ → ℂ}
    (h : Tendsto (fun N => (stepCouple p).eNormDyadic s q
      (f - ∑ n ∈ Finset.range N, a n • haarSystemLp p n)) atTop (𝓝 0)) :
    a = haarSystemCoeff f := by
  set g : ℕ → Lp ℂ p vol := fun N => f - ∑ n ∈ Finset.range N, a n • haarSystemLp p n
  have hg : ∀ N, ⇑(g N) =ᵐ[vol] fun x => f x - ∑ n ∈ Finset.range N, a n * (haarSystem n x : ℂ) :=
    fun N => (Lp.coeFn_sub _ _).trans (EventuallyEq.rfl.sub (coeFn_sum_smul_haarSystemLp a N))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds zero_lt_one))
  have hf : Integrable f vol := by
    have hg0 := integrable_of_eNormDyadic_lt_top hp0 hp1 hs hq0
      ((hN0 N0 le_rfl).trans ENNReal.one_lt_top)
    refine ((hg0.congr (hg N0)).add (integrable_sum_mul_haarSystem a N0)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  funext i
  obtain ⟨M, hM, hMb⟩ := exists_enorm_haarSystemCoeff_le i
  have hbound : ∀ N, i < N → ‖haarSystemCoeff f i - a i‖ₑ ≤
      M * (stepCoupleEmbedConst p s q * (stepCouple p).eNormDyadic s q (g N)) := fun N hiN => by
    rw [← haarSystemCoeff_sub_sum hf a hiN, ← haarSystemCoeff_congr_ae (hg N)]
    refine (hMb _).trans ?_
    rw [← eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable _)]
    gcongr
    exact eLpNorm_one_le_eNormDyadic hp0 hp1 hs hq0 (g N)
  have hlim : Tendsto (fun N => M * (stepCoupleEmbedConst p s q *
      (stepCouple p).eNormDyadic s q (g N))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h
      (Or.inr (stepCoupleEmbedConst_ne_top hs q))) (Or.inr hM)
  have h0 : ‖haarSystemCoeff f i - a i‖ₑ = 0 := le_antisymm (ge_of_tendsto hlim
    (eventually_atTop.2 ⟨i + 1, fun N hN => hbound N (by omega)⟩)) zero_le
  rw [eNorm_eq_zero, sub_eq_zero] at h0
  exact h0.symm
