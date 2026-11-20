/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.HaarBesov
public import ApproximationSpaces.Instances.NTermHilbertBasis
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Haar basis of `L_2[0, 1]` and `n`-term approximation

In breadth-first order the Haar system on `[0, 1]` is `φ_0 = 1` and `φ_{2^k+i} = h_{k,i}` for
`k ∈ ℕ` and `0 ≤ i < 2^k` (`Haar.haarSystem`; the index map is `Haar.haarIndex`). The functions
`φ_n` are orthonormal in `L_2[0, 1]` (`Haar.integral_haarSystem_mul`): Haar functions of one
level have disjoint supports, and a Haar function of a lower level is constant on the support of
one of a higher level, which has mean zero (`Haar.integral_haarFunction_mul`). Their span
contains every conditional expectation `E[f | ℱ_j]`, by the telescoping sum
`E[f | ℱ_j] = E[f | ℱ_0] + ∑_{k<j} (E[f | ℱ_{k+1}] - E[f | ℱ_k])` of Haar sums
(`Haar.condExpLp_succ_sub_ae_eq`), and these step functions are dense
(`Haar.closure_iUnion_scheme`). So the `φ_n` form a Hilbert basis (`Haar.haarBasis`), with the
coefficients `⟨φ_0, f⟩ = ∫_0^1 f` and `⟨φ_{2^k+i}, f⟩ = ⟨f, h_{k,i}⟩`
(`Haar.haarBasis_repr_zero`, `Haar.haarBasis_repr_two_pow_add`). TauCeti's
`TauCeti.unitInterval.haarBasis` uses the same order for the real, unnormalised Haar functions,
as a Schauder basis of `L_p[0, 1]`, `1 ≤ p < ∞`.

The theorem of Stechkin and DeVore (`HilbertBasis.memApprox_nTerm_iff`) then describes best
`n`-term approximation from the Haar basis in `L_2[0, 1]`: for `0 < τ < 2` and
`θ = 1/τ - 1/2`,

`f ∈ A^θ_τ(L_2, n-term)  ⟺  |∫_0^1 f|^τ + ∑_k ∑_{i<2^k} |⟨f, h_{k,i}⟩|^τ < ∞`
(`Haar.memApprox_nTerm_iff_haarCoeff`).

For `1 ≤ τ < 2` the right side is the Haar coefficient condition of `A^θ_τ(L_τ)` for the linear
Haar scheme (`Haar.memApprox_iff_haarCoeff` with the Lebesgue exponent and the fine index both
`τ`, where the weight `2^(k(θ + 1/2 - 1/τ))` is `1`), and since `θ < 1/τ`, of the Besov space
`B^θ_{τ,τ}[0, 1]` defined by moduli of smoothness: nonlinear approximation in `L_2` is linear
approximation in `L_τ` (`Haar.memApprox_nTerm_iff_memApprox_scheme`,
`Haar.memApprox_nTerm_iff_modulus`, `Haar.memApprox_nTerm_iff_perModulus`). In these three
theorems the exponent is `p : ℝ≥0∞` with `1 ≤ p < 2`, as in `Haar.memApprox_iff_haarCoeff`, and
`τ = p.toReal`. This is the case of the Haar system and `1 ≤ τ < 2` of the theorem of DeVore,
Jawerth and Popov (*Compression of wavelet decompositions*, Amer. J. Math. 114, 1992; DeVore,
*Nonlinear approximation*, Acta Numer. 7, 1998, §3.6 and Remark 7.6). For `τ < 1` the Besov
space lies in the quasi-Banach space `L_τ`; that case goes through approximation by steps in
`L_τ` (`Haar.memApprox_nTerm_iff_modulus_of_lt_two` in
`FunctionSpaces.Wavelets.Examples.HaarNTermBesov`).
-/

@[expose] public section

open MeasureTheory Set ApproximationScheme Interval
open scoped ENNReal InnerProductSpace
open ENNReal (dyadicWeight)

namespace Haar

/-! ### The breadth-first order -/

/-- The **breadth-first index** of the Haar system: `n ≥ 1` is written as `n = 2^k + i` with
`k = ⌊log₂ n⌋` and `0 ≤ i < 2^k`, and sent to the pair `(k, i)` of the level and the position of
the Haar function `h_{k,i}` (`Haar.haarIndex_two_pow_add`). -/
def haarIndex (n : ℕ) : ℕ × ℕ := (Nat.log 2 n, n - 2 ^ Nat.log 2 n)

/-- The index map inverts `(k, i) ↦ 2^k + i` on the pairs with `0 ≤ i < 2^k`, since
`⌊log₂ (2^k + i)⌋ = k` (`Nat.log_two_pow_add`). -/
theorem haarIndex_two_pow_add {k i : ℕ} (hi : i < 2 ^ k) : haarIndex (2 ^ k + i) = (k, i) := by
  simp [haarIndex, Nat.log_two_pow_add hi]

/-! ### The Haar system in breadth-first order -/

/-- The **Haar system** on `[0, 1]` in breadth-first order, as real functions: `φ_0 = 1` and
`φ_{2^k+i} = h_{k,i}` for `0 ≤ i < 2^k` (`Haar.haarSystem_two_pow_add`). -/
noncomputable def haarSystem (n : ℕ) : ℝ → ℝ :=
  if n = 0 then fun _ => 1 else haarFunction (haarIndex n).1 ((haarIndex n).2 : ℤ)

/-- `φ_0 = 1`. -/
@[simp]
theorem haarSystem_zero : haarSystem 0 = fun _ => 1 := ite_eq_left rfl

/-- `φ_{2^k+i} = h_{k,i}` for `0 ≤ i < 2^k`. -/
theorem haarSystem_two_pow_add {k i : ℕ} (hi : i < 2 ^ k) :
    haarSystem (2 ^ k + i) = haarFunction k i := by
  rw [haarSystem, ite_eq_right (by positivity : 2 ^ k + i ≠ 0), haarIndex_two_pow_add hi]

/-- The functions `φ_n` are measurable. -/
theorem measurable_haarSystem (n : ℕ) : Measurable (haarSystem n) := by
  unfold haarSystem
  split_ifs
  · exact measurable_const
  · exact measurable_haarFunction _ _

/-- The functions `φ_n` are bounded. -/
theorem exists_abs_haarSystem_le (n : ℕ) : ∃ C, ∀ x, |haarSystem n x| ≤ C := by
  unfold haarSystem
  split_ifs
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨_, abs_haarFunction_le _ _⟩

/-- Every `φ_n`, as a complex function, lies in `L_p[0, 1]` for every `p`, since it is bounded. -/
theorem memLp_haarSystem (p : ℝ≥0∞) (n : ℕ) : MemLp (fun x => (haarSystem n x : ℂ)) p vol := by
  obtain ⟨C, hC⟩ := exists_abs_haarSystem_le n
  refine MemLp.of_bound
    (Complex.measurable_ofReal.comp (measurable_haarSystem n)).aestronglyMeasurable C
    (ae_of_all _ fun x => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hC x

/-- The **Haar vectors** `φ_n` as elements of `L_2[0, 1]`. -/
noncomputable def haarVec (n : ℕ) : Lp ℂ 2 vol := (memLp_haarSystem 2 n).toLp _

/-- The Haar vector `φ_n` is the function `φ_n` almost everywhere. -/
theorem coeFn_haarVec (n : ℕ) : haarVec n =ᵐ[vol] fun x => (haarSystem n x : ℂ) :=
  MemLp.coeFn_toLp _

/-- The coefficient of `f` in the direction of `φ_n`: `⟨φ_n, f⟩ = ∫_0^1 φ_n f`, since `φ_n` is
real. -/
theorem inner_haarVec (n : ℕ) (f : Lp ℂ 2 vol) :
    ⟪haarVec n, f⟫_ℂ = ∫ x, (haarSystem n x : ℂ) * f x ∂vol := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_haarVec n] with x hx
  rw [RCLike.inner_apply', hx, Complex.conj_ofReal]

/-! ### Orthonormality -/

/-- Two points in one dyadic interval of level `j` lie in one dyadic interval of every coarser
level `i ≤ j`. -/
theorem dyadicIndex_eq_of_le {i j : ℕ} (hij : i ≤ j) {x y : ℝ}
    (h : dyadicIndex j x = dyadicIndex j y) : dyadicIndex i x = dyadicIndex i y := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j _ ih => exact ih (by rw [← dyadicIndex_succ_div j x, ← dyadicIndex_succ_div j y, h])

/-- A Haar function of level `k` is constant on every dyadic interval of a level `j > k`. -/
theorem haarFunction_eq_of_dyadicIndex_eq {k j : ℕ} (hkj : k < j) (m : ℤ) {x y : ℝ}
    (h : dyadicIndex j x = dyadicIndex j y) : haarFunction k m x = haarFunction k m y := by
  unfold haarFunction
  rw [dyadicIndex_eq_of_le (show k + 1 ≤ j from hkj) h]

/-- Outside the range `0 ≤ m < 2^j` the Haar function `h_{j,m}` vanishes almost everywhere on
`[0, 1]`: its support `I_{j,m}` meets `[0, 1]` in at most the point `1`. -/
theorem haarFunction_ae_eq_zero {j : ℕ} {m : ℤ} (hm : ¬(0 ≤ m ∧ m < 2 ^ j)) :
    haarFunction j m =ᵐ[vol] 0 := by
  filter_upwards [Interval.ae_mem_Ico_unitVol] with x hx
  refine haarFunction_eq_zero fun h => hm ?_
  rw [← h]
  exact ⟨dyadicIndex_nonneg hx, dyadicIndex_lt hx⟩

/-- **Haar functions have mean zero**: `∫_0^1 h_{j,m} = 0`. For `0 ≤ m < 2^j` the two halves of
`I_{j,m}`, where `h_{j,m}` takes the values `±2^(j/2)`, have the same length; for every other `m`,
`h_{j,m}` vanishes almost everywhere on `[0, 1]`. -/
theorem integral_haarFunction (j : ℕ) (m : ℤ) : ∫ x, haarFunction j m x ∂vol = 0 := by
  by_cases hm : 0 ≤ m ∧ m < 2 ^ j
  · obtain ⟨h0, h1⟩ := hm
    have h := haarCoeff_eq (integrable_const (1 : ℂ)) j m
    have h2 : 2 * m + 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
    simp only [haarCoeff, mul_one, setIntegral_const] at h
    rw [vol_real_dyadicInterval (by omega) (by omega), vol_real_dyadicInterval (by omega) h2,
      sub_self, mul_zero, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
    exact h
  · exact (integral_congr_ae (haarFunction_ae_eq_zero hm)).trans (integral_zero' _ _)

/-- **Haar functions are normalised**: `∫_0^1 h_{j,m}² = 1` for `0 ≤ m < 2^j`, since
`h_{j,m}² = 2^j` on `I_{j,m}`, of length `2^(-j)`, and `0` elsewhere. -/
theorem integral_haarFunction_mul_self {j : ℕ} {m : ℤ} (h0 : 0 ≤ m) (h1 : m < 2 ^ j) :
    ∫ x, haarFunction j m x * haarFunction j m x ∂vol = 1 := by
  have hpt : (fun x => haarFunction j m x * haarFunction j m x) =
      (dyadicInterval j m).indicator fun _ => (2 : ℝ) ^ j := by
    funext x
    by_cases hx : dyadicIndex j x = m
    · rw [indicator_of_mem (mem_dyadicInterval.2 hx), ← abs_mul_abs_self, abs_haarFunction hx,
        ← Real.rpow_add two_pos, add_halves, Real.rpow_natCast]
    · rw [indicator_of_notMem (mt mem_dyadicInterval.1 hx), haarFunction_eq_zero hx, zero_mul]
  rw [hpt, integral_indicator_const _ (measurableSet_dyadicInterval j m),
    vol_real_dyadicInterval h0 h1, smul_eq_mul, inv_mul_cancel₀ (by positivity)]

/-- Haar functions of one level at different positions have disjoint supports:
`h_{j,m} h_{j,n} = 0` for `m ≠ n`. -/
theorem haarFunction_mul_haarFunction_of_ne {j : ℕ} {m n : ℤ} (h : m ≠ n) (x : ℝ) :
    haarFunction j m x * haarFunction j n x = 0 := by
  by_cases hx : dyadicIndex j x = m
  · rw [haarFunction_eq_zero (m := n) (by rw [hx]; exact h), mul_zero]
  · rw [haarFunction_eq_zero hx, zero_mul]

/-- **Haar functions of different levels are orthogonal**: for `k < j`,
`∫_0^1 h_{k,m} h_{j,n} = 0`. For `0 ≤ n < 2^j` the function `h_{k,m}` is constant on `I_{j,n}`,
the support of `h_{j,n}`, and `h_{j,n}` has mean zero; for every other `n`, `h_{j,n}` vanishes
almost everywhere on `[0, 1]`. -/
theorem integral_haarFunction_mul_of_lt {k j : ℕ} (hkj : k < j) (m n : ℤ) :
    ∫ x, haarFunction k m x * haarFunction j n x ∂vol = 0 := by
  by_cases hn : 0 ≤ n ∧ n < 2 ^ j
  · obtain ⟨h0, -⟩ := hn
    lift n to ℕ using h0
    have hpt : (fun x => haarFunction k m x * haarFunction j n x) =
        fun x => haarFunction k m ((n : ℝ) / 2 ^ j) * haarFunction j n x := by
      funext x
      by_cases hx : dyadicIndex j x = n
      · rw [haarFunction_eq_of_dyadicIndex_eq hkj m (hx.trans (dyadicIndex_natCast_div j n).symm)]
      · rw [haarFunction_eq_zero hx, mul_zero, mul_zero]
    rw [hpt, integral_const_mul, integral_haarFunction, mul_zero]
  · refine (integral_congr_ae ?_).trans (integral_zero' _ _)
    filter_upwards [haarFunction_ae_eq_zero hn] with x hx
    simp [hx]

/-- **The Haar functions are orthonormal**: for `0 ≤ m < 2^k` and all `j`, `n`,
`∫_0^1 h_{k,m} h_{j,n}` is `1` if `(k, m) = (j, n)` and `0` otherwise. -/
theorem integral_haarFunction_mul {k j : ℕ} {m : ℤ} (hm0 : 0 ≤ m) (hm : m < 2 ^ k) (n : ℤ) :
    ∫ x, haarFunction k m x * haarFunction j n x ∂vol = if k = j ∧ m = n then 1 else 0 := by
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · rw [integral_haarFunction_mul_of_lt hkj m n, ite_eq_right fun h => hkj.ne h.1]
  · by_cases hmn : m = n
    · subst hmn
      rw [integral_haarFunction_mul_self hm0 hm, ite_eq_left ⟨rfl, rfl⟩]
    · simp_rw [haarFunction_mul_haarFunction_of_ne hmn, integral_zero]
      rw [ite_eq_right fun h => hmn h.2]
  · simp_rw [mul_comm (haarFunction k m _)]
    rw [integral_haarFunction_mul_of_lt hjk n m, ite_eq_right fun h => hjk.ne' h.1]

/-- **The Haar system is orthonormal**: `∫_0^1 φ_i φ_j = 1` if `i = j` and `0` otherwise. -/
theorem integral_haarSystem_mul (i j : ℕ) :
    ∫ x, haarSystem i x * haarSystem j x ∂vol = if i = j then 1 else 0 := by
  rcases eq_or_ne i 0 with rfl | hi <;> rcases eq_or_ne j 0 with rfl | hj
  · simp
  · obtain ⟨l, n, hn, rfl⟩ := Nat.exists_eq_two_pow_add hj
    simpa [haarSystem_two_pow_add hn, hj.symm] using integral_haarFunction l n
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_add hi
    simpa [haarSystem_two_pow_add hm, hi] using integral_haarFunction k m
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_add hi
    obtain ⟨l, n, hn, rfl⟩ := Nat.exists_eq_two_pow_add hj
    rw [haarSystem_two_pow_add hm, haarSystem_two_pow_add hn,
      integral_haarFunction_mul (Int.natCast_nonneg m) (by exact_mod_cast hm)]
    simp only [Nat.two_pow_add_eq_iff hm hn, Nat.cast_inj]

/-- **The Haar vectors are orthonormal** in `L_2[0, 1]`. -/
theorem orthonormal_haarVec : Orthonormal ℂ haarVec := by
  rw [orthonormal_iff_ite]
  intro i j
  have h : ∫ x, (haarSystem i x : ℂ) * haarVec j x ∂vol =
      ((∫ x, haarSystem i x * haarSystem j x ∂vol : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_haarVec j] with x hx
    rw [hx, Complex.ofReal_mul]
  rw [inner_haarVec, h, integral_haarSystem_mul]
  split_ifs <;> simp

/-! ### Completeness -/

/-- **The conditional expectations lie in the span of the Haar vectors**: `E[f | ℱ_j]` is a finite
combination of the `φ_n`, by the telescoping sum
`E[f | ℱ_j] = E[f | ℱ_0] + ∑_{k<j} (E[f | ℱ_{k+1}] - E[f | ℱ_k])`, where `E[f | ℱ_0] = ∫_0^1 f`
and every difference is a Haar sum of level `k` (`Haar.condExpLp_succ_sub_ae_eq`). -/
theorem condExpLp_mem_span_haarVec (j : ℕ) (f : Lp ℂ 2 vol) :
    Lp.condExpLp (dyadicFiltration j) f ∈ Submodule.span ℂ (range haarVec) := by
  induction j with
  | zero =>
    have h : Lp.condExpLp (dyadicFiltration 0) f = (∫ x, f x ∂vol) • haarVec 0 := by
      refine Lp.ext ?_
      filter_upwards [condExpLp_zero_ae_eq f, Lp.coeFn_smul (∫ x, f x ∂vol) (haarVec 0),
        coeFn_haarVec 0] with x h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, haarSystem_zero, Complex.ofReal_one, smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | succ j ih =>
    have hm : ∀ᵐ x ∂vol, ∀ m : Fin (2 ^ j),
        (haarCoeff f j ((m : ℕ) : ℤ) • haarVec (2 ^ j + m)) x =
          haarCoeff f j ((m : ℕ) : ℤ) * (haarFunction j ((m : ℕ) : ℤ) x : ℂ) := by
      rw [ae_all_iff]
      intro m
      filter_upwards [Lp.coeFn_smul (haarCoeff f j ((m : ℕ) : ℤ)) (haarVec (2 ^ j + m)),
        coeFn_haarVec (2 ^ j + m)] with x h1 h2
      rw [h1, Pi.smul_apply, h2, haarSystem_two_pow_add m.isLt, smul_eq_mul]
    have h : Lp.condExpLp (dyadicFiltration (j + 1)) f - Lp.condExpLp (dyadicFiltration j) f =
        ∑ m : Fin (2 ^ j), haarCoeff f j ((m : ℕ) : ℤ) • haarVec (2 ^ j + m) := by
      refine Lp.ext ?_
      filter_upwards [condExpLp_succ_sub_ae_eq j f, Lp.coeFn_fun_finsetSum Finset.univ
        (fun m : Fin (2 ^ j) => haarCoeff f j ((m : ℕ) : ℤ) • haarVec (2 ^ j + m)), hm]
        with x h1 h2 h3
      rw [h1, h2]
      exact (Finset.sum_congr rfl fun m _ => h3 m).symm
    rw [← sub_add_cancel (Lp.condExpLp (dyadicFiltration (j + 1)) f)
      (Lp.condExpLp (dyadicFiltration j) f), h]
    exact add_mem (Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) ih

/-- **The Haar approximants lie in the span of the Haar vectors**: every step function on the
dyadic intervals of one level is a finite combination of the `φ_n`. -/
theorem iUnion_scheme_subset_span :
    (⋃ n, scheme 2 n) ⊆ (Submodule.span ℂ (range haarVec) : Set (Lp ℂ 2 vol)) := by
  intro a ha
  obtain ⟨n, hn⟩ := mem_iUnion.1 ha
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [ApproximationScheme.mem_ofMonotoneSubmodules_zero.1 hn]
    exact zero_mem _
  · rw [dyadicFiltration.mem_scheme hn0] at hn
    rw [← Lp.condExpLp_of_mem (dyadicFiltration.le _) hn]
    exact condExpLp_mem_span_haarVec _ a

/-- **The Haar vectors span a dense subspace** of `L_2[0, 1]`: the closure of their span is the
whole space, since the step functions on the dyadic intervals are dense
(`Haar.closure_iUnion_scheme`). -/
theorem span_haarVec_closure_eq_top :
    (Submodule.span ℂ (range haarVec)).topologicalClosure = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  have h := closure_mono iUnion_scheme_subset_span
  rw [closure_iUnion_scheme (p := 2) ENNReal.ofNat_ne_top] at h
  exact h (mem_univ x)

/-! ### The Haar basis -/

/-- **The Haar basis** of `L_2[0, 1]`: the Hilbert basis `φ_0 = 1`, `φ_{2^k+i} = h_{k,i}`
(`k ∈ ℕ`, `0 ≤ i < 2^k`), in breadth-first order. -/
noncomputable def haarBasis : HilbertBasis ℕ ℂ (Lp ℂ 2 vol) :=
  HilbertBasis.mk orthonormal_haarVec span_haarVec_closure_eq_top.ge

/-- The vectors of the Haar basis are the Haar vectors `φ_n`. -/
@[simp]
theorem coe_haarBasis : ⇑haarBasis = haarVec := HilbertBasis.coe_mk _ _

/-- The coefficients in the Haar basis: `⟨φ_n, f⟩ = ∫_0^1 φ_n f`. -/
theorem haarBasis_repr_apply (f : Lp ℂ 2 vol) (n : ℕ) :
    haarBasis.repr f n = ∫ x, (haarSystem n x : ℂ) * f x ∂vol := by
  rw [haarBasis.repr_apply_apply, coe_haarBasis, inner_haarVec]

/-- The coefficient of `φ_0 = 1` is the mean `∫_0^1 f`. -/
theorem haarBasis_repr_zero (f : Lp ℂ 2 vol) : haarBasis.repr f 0 = ∫ x, f x ∂vol := by
  simp [haarBasis_repr_apply]

/-- The coefficient of `φ_{2^k+i} = h_{k,i}` is the Haar coefficient `⟨f, h_{k,i}⟩`. -/
theorem haarBasis_repr_two_pow_add (f : Lp ℂ 2 vol) {k i : ℕ} (hi : i < 2 ^ k) :
    haarBasis.repr f (2 ^ k + i) = haarCoeff f k i := by
  rw [haarBasis_repr_apply, haarSystem_two_pow_add hi]
  rfl

/-! ### `n`-term approximation from the Haar basis -/

/-- The `ℓ_τ` sum of the coefficients in the Haar basis, level by level:
`∑_n |⟨φ_n, f⟩|^τ = |∫_0^1 f|^τ + ∑_k ∑_{i<2^k} |⟨f, h_{k,i}⟩|^τ`. -/
theorem tsum_haarBasis_repr_rpow (τ : ℝ) (f : Lp ℂ 2 vol) :
    ∑' n, ‖haarBasis.repr f n‖ₑ ^ τ = ‖∫ x, f x ∂vol‖ₑ ^ τ +
      ∑' k, ∑ i : Fin (2 ^ k), ‖haarCoeff f k ((i : ℕ) : ℤ)‖ₑ ^ τ := by
  rw [ENNReal.tsum_eq_add_tsum_two_pow_add, haarBasis_repr_zero]
  congr 1
  exact tsum_congr fun k => Finset.sum_congr rfl fun i _ => by
    rw [haarBasis_repr_two_pow_add f i.isLt]

/-- **Best `n`-term approximation from the Haar basis** in `L_2[0, 1]`: for `0 < τ < 2` and
`θ = 1/τ - 1/2`, `f` lies in the approximation space `A^θ_τ` of `n`-term approximation from the
dictionary of the multiples `c φ_n` iff
`|∫_0^1 f|^τ + ∑_k ∑_{i<2^k} |⟨f, h_{k,i}⟩|^τ < ∞`: the theorem of Stechkin and DeVore
(`HilbertBasis.memApprox_nTerm_iff`) for the Haar basis, including the range `τ < 1`. DeVore
(*Nonlinear approximation*, Acta Numer. 7, 1998, §3.6) characterises the rate `n^(-θ)`, the space
`A^θ_∞`, by the decay `γ_n ≤ M n^(-θ-1/2)` of the rearranged Haar coefficients. -/
theorem memApprox_nTerm_iff_haarCoeff {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) (f : Lp ℂ 2 vol) :
    (nTerm haarBasis.coeffDictionary).MemApprox (1 / τ - 1 / 2) (ENNReal.ofReal τ) f ↔
      ‖∫ x, f x ∂vol‖ₑ ^ τ + ∑' k, ∑ i : Fin (2 ^ k), ‖haarCoeff f k ((i : ℕ) : ℤ)‖ₑ ^ τ < ∞ := by
  refine (haarBasis.memApprox_nTerm_iff hτ0 hτ2 f).trans ?_
  rw [tsum_haarBasis_repr_rpow]

/-- For `1 ≤ p < 2` the exponent `τ = p.toReal` satisfies `0 < τ < 2`, and
`θ = 1/τ - 1/2` satisfies `0 < θ < 1/τ`. -/
private theorem toReal_and_theta_bounds_of_one_le_of_lt_two {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp2 : p < 2) :
    0 < p.toReal ∧ p.toReal < 2 ∧ 0 < 1 / p.toReal - 1 / 2 ∧
      1 / p.toReal - 1 / 2 < 1 / p.toReal := by
  have hτ1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 (ne_top_of_lt hp2)
  have hτ2 : p.toReal < 2 := by
    simpa using ENNReal.toReal_strict_mono ENNReal.ofNat_ne_top hp2
  have hτ0 : 0 < p.toReal := by linarith
  have h := one_div_lt_one_div_of_lt hτ0 hτ2
  exact ⟨hτ0, hτ2, by linarith, by linarith⟩

/-- **Nonlinear approximation in `L_2` is linear approximation in `L_τ`** for the Haar system:
for an exponent `1 ≤ p < 2` with `τ = p.toReal` (so `1 ≤ τ < 2`) and `θ = 1/τ - 1/2`,
`f ∈ L_2[0, 1]` lies in the approximation space `A^θ_τ` of `n`-term approximation from the Haar
basis in `L_2` iff it lies in the space `A^θ_τ` of the linear Haar scheme of dyadic step functions
in `L_τ[0, 1]`. Both conditions are `|∫_0^1 f|^τ + ∑_k ∑_{i<2^k} |⟨f, h_{k,i}⟩|^τ < ∞`: for the
fine index `q = p` and `s = θ` the weight `2^(k(s + 1/2 - 1/τ))` of the Haar characterisation
(`Haar.memApprox_iff_haarCoeff`) is `1`. In Lean the exponent is `p : ℝ≥0∞`, with `1 ≤ p` as a
`Fact` instance as in `Haar.memApprox_iff_haarCoeff`; it is the Lebesgue exponent of `L_τ` and
the fine index of both spaces. The case of the Haar system and `1 ≤ τ < 2` of the theorem of
DeVore, Jawerth and Popov. -/
theorem memApprox_nTerm_iff_memApprox_scheme {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2)
    (f : Lp ℂ 2 vol) :
    (nTerm haarBasis.coeffDictionary).MemApprox (1 / p.toReal - 1 / 2) p f ↔
      (scheme p).MemApprox (1 / p.toReal - 1 / 2) p
        (Lp.inclusionOfExponentLe (𝕜 := ℝ) vol hp2.le f) := by
  have hp1 : 1 ≤ p := Fact.out
  have hpt : p ≠ ∞ := ne_top_of_lt hp2
  obtain ⟨hτ0, hτ2, hθ, -⟩ := toReal_and_theta_bounds_of_one_le_of_lt_two hp1 hp2
  have hg : (Lp.inclusionOfExponentLe (𝕜 := ℝ) vol hp2.le f : ℝ → ℂ) =ᵐ[vol] f :=
    Lp.coeFn_inclusionOfExponentLe hp2.le f
  have h1 := memApprox_nTerm_iff_haarCoeff hτ0 hτ2 f
  rw [ENNReal.ofReal_toReal hpt] at h1
  rw [h1, memApprox_iff_haarCoeff hpt hθ hp1,
    show 1 / p.toReal - 1 / 2 + (1 / 2 - 1 / p.toReal) = 0 by ring, integral_congr_ae hg]
  simp only [ENNReal.dyadicWeight_zero_left, one_mul, haarCoeff_congr_ae hg]
  rw [ENNReal.add_lt_top, ENNReal.add_lt_top, ENNReal.rpow_lt_top_iff_of_pos hτ0,
    ← ENNReal.rpow_lt_top_iff_of_pos hτ0 (x := ENNReal.lqNorm p _),
    ENNReal.lqNorm_lqNorm_rpow (zero_lt_one.trans_le hp1).ne' hpt]
  simp only [tsum_fintype]

/-- **Best `n`-term Haar approximation in `L_2` and Besov spaces on the interval**: for an
exponent `1 ≤ p < 2` with `τ = p.toReal` (so `1 ≤ τ < 2`) and `θ = 1/τ - 1/2`, `f ∈ L_2[0, 1]`
lies in the approximation space `A^θ_τ` of `n`-term approximation from the Haar basis iff
`‖f‖_τ + ‖(2^(kθ) ω_1(f, 2^(-k), [0, 1])_τ)_k‖_{ℓ_τ} < ∞`, that is, iff `f` lies in the Besov
space `B^θ_{τ,τ}[0, 1]` (`Haar.lqNorm_modulus_lt_top_iff_haarCoeff`, applicable since
`θ < 1/τ`). In Lean `p : ℝ≥0∞` is the Lebesgue exponent and the fine index, with `1 ≤ p` as a
`Fact` instance. This is the theorem of DeVore, Jawerth and Popov for the Haar system and
`1 ≤ τ < 2`. -/
theorem memApprox_nTerm_iff_modulus {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2) (f : Lp ℂ 2 vol) :
    (nTerm haarBasis.coeffDictionary).MemApprox (1 / p.toReal - 1 / 2) p f ↔
      ‖Lp.inclusionOfExponentLe (𝕜 := ℝ) vol hp2.le f‖ₑ + ENNReal.lqNorm p (fun k =>
        dyadicWeight (1 / p.toReal - 1 / 2) k *
          lpModulus p 1 (Lp.inclusionOfExponentLe (𝕜 := ℝ) vol hp2.le f) k) < ∞ := by
  obtain ⟨-, -, hθ, hθp⟩ := toReal_and_theta_bounds_of_one_le_of_lt_two Fact.out hp2
  rw [memApprox_nTerm_iff_memApprox_scheme hp2, ← memApprox_ppScheme_one_iff,
    memApprox_ppScheme_iff le_rfl (ne_top_of_lt hp2) Fact.out hθ.le hθp]

/-- **Best `n`-term Haar approximation in `L_2` and Besov spaces on the circle**: for an
exponent `1 ≤ p < 2` with `τ = p.toReal` (so `1 ≤ τ < 2`) and `θ = 1/τ - 1/2`, `f ∈ L_2[0, 1]`
lies in the approximation space `A^θ_τ` of `n`-term approximation from the Haar basis iff
`‖f‖_τ + ‖(2^(kθ) ω_1^per(f, 2^(-k))_τ)_k‖_{ℓ_τ} < ∞`, the periodic Besov condition of
`B^θ_{τ,τ}(𝕋)` (`Haar.lqNorm_perModulus_lt_top_iff_haarCoeff`). In Lean `p : ℝ≥0∞` is the
Lebesgue exponent and the fine index, with `1 ≤ p` as a `Fact` instance. -/
theorem memApprox_nTerm_iff_perModulus {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2)
    (f : Lp ℂ 2 vol) :
    (nTerm haarBasis.coeffDictionary).MemApprox (1 / p.toReal - 1 / 2) p f ↔
      ‖Lp.inclusionOfExponentLe (𝕜 := ℝ) vol hp2.le f‖ₑ + ENNReal.lqNorm p (fun k =>
        dyadicWeight (1 / p.toReal - 1 / 2) k *
          lpPerModulus p 1 (Lp.inclusionOfExponentLe (𝕜 := ℝ) vol hp2.le f) k) < ∞ := by
  obtain ⟨-, -, hθ, hθp⟩ := toReal_and_theta_bounds_of_one_le_of_lt_two Fact.out hp2
  rw [memApprox_nTerm_iff_memApprox_scheme hp2, ← memApprox_ppScheme_one_iff,
    memApprox_ppScheme_iff_per le_rfl (ne_top_of_lt hp2) Fact.out hθ.le hθp]

end Haar
