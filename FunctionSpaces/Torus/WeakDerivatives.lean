/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.Coefficients

/-!
# Weak derivatives on the torus and `W^m_2(𝕋^d)`

For a multi-index `α ∈ ℕ^d`, the derivative `∂^α` multiplies the Fourier coefficients by the
**symbol** `(2πi k)^α = ∏ᵢ (2πi kᵢ)^(αᵢ)` (`Torus.periodicDerivSymbol`).  So `g ∈ L_p` is the **weak
derivative** `∂^α f` of `f ∈ L_p` (`Torus.HasPeriodicWeakDeriv`) if

`ĝ(k) = (2πi k)^α f̂(k)`   for all `k ∈ ℤ^d`.

This is the distributional definition `∫ g φ = (-1)^|α| ∫ f ∂^α φ`, tested against the
trigonometric monomials `φ = e_{-k}`, whose span is dense.  For `1 ≤ p ≤ ∞` the weak derivative
`∂^α f` is the distributional derivative of the periodic lift `f ∘ π` on `ℝ^d`
(`Torus.hasPeriodicWeakDeriv_iff_comp_quotientProj`).  The **Sobolev space**
`W^m_p(𝕋^d)`, `m ∈ ℕ`, consists of the `f ∈ L_p` all of whose weak derivatives of order
`|α| ≤ m` lie in `L_p` (`Torus.MemPeriodicSobolev`).  The definitions are for every exponent `p`;
the theorems below, apart from `Torus.hasPeriodicWeakDeriv_zero`, are for `p = 2`.
`FunctionSpaces.Torus.LpWeakDerivatives` develops the calculus for `1 ≤ p ≤ ∞`.

**Coincidence** (`Torus.memPeriodicSobolev_iff`, `Torus.memPeriodicSobolev_iff_memBesov`):

`W^m_2(𝕋^d) = H^m(𝕋^d) = B^m_{2,2}(𝕋^d)`   (`m ≥ 1` for the Besov space),

because the symbols of order `≤ m` and the weight `(1 + max_i |k_i|)^m` dominate each other:
`|(2πi k)^α| ≤ (2π)^m (1 + max_i |k_i|)^m` for `|α| ≤ m` (`Torus.norm_periodicDerivSymbol_le`), and
`(1 + max_i |k_i|)^m ≤ 2^m (1 + ∑_j |k_j|^m)`, where `|k_j|^m` is at most the symbol of
`∂_j^m` (`Torus.one_add_trigDeg_pow_le`).  For functions with `C^1` lifts the classical derivatives
are the weak derivatives (`Torus.hasPeriodicWeakLineDeriv_of_contDiff`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal TorusHaar lp Real

namespace Torus

variable {d : Type*} [Fintype d]

/-- The **symbol** `(2πi k)^α = ∏ᵢ (2πi kᵢ)^(αᵢ)` of the derivative `∂^α`. -/
noncomputable def periodicDerivSymbol (α : d → ℕ) (k : d → ℤ) : ℂ :=
  ∏ i, (2 * π * Complex.I * (k i : ℂ)) ^ α i

/-- `|2πi a| = 2π |a|` for an integer `a`. -/
theorem norm_two_pi_I_mul_intCast (a : ℤ) :
    ‖2 * π * Complex.I * (a : ℂ)‖ = 2 * π * |(a : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat, mul_one]

/-- `|(2πi k)^α| = ∏ᵢ (2π |kᵢ|)^(αᵢ)`. -/
theorem norm_periodicDerivSymbol (α : d → ℕ) (k : d → ℤ) :
    ‖periodicDerivSymbol α k‖ = ∏ i, (2 * π * |(k i : ℝ)|) ^ α i := by
  simp only [periodicDerivSymbol, norm_prod, norm_pow, norm_two_pi_I_mul_intCast]

/-- The symbol of order `0` is `1`. -/
@[simp]
theorem periodicDerivSymbol_zero (k : d → ℤ) : periodicDerivSymbol 0 k = 1 := by
  simp [periodicDerivSymbol]

/-- The symbol of `∂_j^m` is `(2πi k_j)^m`. -/
theorem periodicDerivSymbol_single [DecidableEq d] (j : d) (m : ℕ) (k : d → ℤ) :
    periodicDerivSymbol (Pi.single j m) k = (2 * π * Complex.I * (k j : ℂ)) ^ m := by
  rw [periodicDerivSymbol, Fintype.prod_eq_single j fun i hi => by simp [hi]]
  simp

/-- `1 ≤ 2π`. -/
theorem one_le_two_pi : (1 : ℝ) ≤ 2 * π := by
  have := Real.one_le_pi_div_two; linarith

/-- `|kᵢ| ≤ 1 + max_j |k_j|`. -/
theorem abs_le_one_add_trigDeg (k : d → ℤ) (i : d) : |(k i : ℝ)| ≤ 1 + trigDeg k := by
  have h : ((k i).natAbs : ℝ) ≤ trigDeg k := by exact_mod_cast natAbs_le_trigDeg k i
  have he : ((k i).natAbs : ℝ) = |(k i : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  linarith

/-- **Symbols of order `≤ m` are dominated by the Sobolev weight**:
`|(2πi k)^α| ≤ (2π)^m (1 + max_i |k_i|)^m` for `|α| ≤ m`. -/
theorem norm_periodicDerivSymbol_le {m : ℕ} {α : d → ℕ} (hα : ∑ i, α i ≤ m) (k : d → ℤ) :
    ‖periodicDerivSymbol α k‖ ≤ (2 * π) ^ m * (1 + trigDeg k : ℝ) ^ m := by
  have hx : (1 : ℝ) ≤ 2 * π * (1 + trigDeg k) := by
    have : (1 : ℝ) ≤ 1 + trigDeg k := by have := (trigDeg k).cast_nonneg (α := ℝ); linarith
    nlinarith [one_le_two_pi]
  rw [norm_periodicDerivSymbol, ← mul_pow]
  calc ∏ i, (2 * π * |(k i : ℝ)|) ^ α i ≤ ∏ i, (2 * π * (1 + trigDeg k)) ^ α i := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        gcongr
        exact abs_le_one_add_trigDeg k i
    _ = (2 * π * (1 + trigDeg k)) ^ ∑ i, α i := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 * π * (1 + trigDeg k)) ^ m := pow_le_pow_right₀ hx hα

/-- **The Sobolev weight is dominated by symbols**: `(1 + max_i |k_i|)^m ≤ 2^m (1 + ∑_j |k_j|^m)`,
and `|k_j|^m ≤ |(2πi k_j)^m|` is the symbol of `∂_j^m`. -/
theorem one_add_trigDeg_pow_le [DecidableEq d] (m : ℕ) (k : d → ℤ) :
    (1 + trigDeg k : ℝ) ^ m ≤
      2 ^ m * (‖periodicDerivSymbol 0 k‖ + ∑ j, ‖periodicDerivSymbol (Pi.single j m) k‖) := by
  have hsym : ∀ j, |(k j : ℝ)| ^ m ≤ ‖periodicDerivSymbol (Pi.single j m) k‖ := fun j => by
    rw [periodicDerivSymbol_single, norm_pow, norm_two_pi_I_mul_intCast, mul_pow]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ one_le_two_pi)
  rw [periodicDerivSymbol_zero, norm_one]
  rcases (Finset.univ : Finset d).eq_empty_or_nonempty with he | hne
  · have h0 : trigDeg k = 0 := by simp [trigDeg, he]
    rw [h0, Nat.cast_zero, add_zero, one_pow]
    have : (0 : ℝ) ≤ ∑ j, ‖periodicDerivSymbol (Pi.single j m) k‖ := by positivity
    nlinarith [one_le_pow₀ (M₀ := ℝ) one_le_two (n := m)]
  · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup _ hne fun i => (k i).natAbs
    have hdeg : (trigDeg k : ℝ) = |(k j : ℝ)| := by
      rw [trigDeg, hj, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    refine (one_add_pow_le_two_pow_mul (Nat.cast_nonneg _) m).trans ?_
    gcongr
    rw [hdeg]
    exact (hsym j).trans
      (Finset.single_le_sum (f := fun j => ‖periodicDerivSymbol (Pi.single j m) k‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j))

/-- `g ∈ L_p(𝕋^d)` is the **weak derivative** `∂^α f` of `f ∈ L_p(𝕋^d)`:
`ĝ(k) = (2πi k)^α f̂(k)` for all `k ∈ ℤ^d`. The definition is meant for `1 ≤ p ≤ ∞`, where every
element of `L_p(𝕋^d)` is integrable and its coefficients are integrals. -/
def HasPeriodicWeakDeriv {p : ℝ≥0∞} (α : d → ℕ) (f g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Prop :=
  ∀ k : d → ℤ, mFourierCoeff g k = periodicDerivSymbol α k * mFourierCoeff f k

/-- `f ∈ W^m_p(𝕋^d)`: every weak derivative `∂^α f` of order `|α| ≤ m` lies in `L_p`. The
definition is meant for `1 ≤ p ≤ ∞`, where every element of `L_p(𝕋^d)` is integrable and its
coefficients are integrals. -/
def MemPeriodicSobolev {p : ℝ≥0∞} (m : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : Prop :=
  ∀ α : d → ℕ, ∑ i, α i ≤ m → ∃ g, HasPeriodicWeakDeriv α f g

/-- `f ∈ L_p(𝕋^d)` is its own derivative of order `0`. -/
theorem hasPeriodicWeakDeriv_zero {p : ℝ≥0∞} (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    HasPeriodicWeakDeriv 0 f f := fun k => by rw [periodicDerivSymbol_zero, one_mul]

/-- A weak derivative exists as soon as the multiplied coefficients are square-summable: it is
the `L_2` function with these coefficients. -/
theorem exists_hasPeriodicWeakDeriv {α : d → ℕ} {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (h : Memℓp (fun k => periodicDerivSymbol α k * mFourierCoeff f k) 2) :
    ∃ g, HasPeriodicWeakDeriv α f g := by
  refine ⟨mFourierBasis.repr.symm ⟨_, h⟩, fun k => ?_⟩
  rw [← mFourierBasis_repr, LinearIsometryEquiv.apply_symm_apply]

/-- The coefficients of a weak derivative are square-summable. -/
theorem HasPeriodicWeakDeriv.mem_l2 {α : d → ℕ} {f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hg : HasPeriodicWeakDeriv α f g) :
    Memℓp (fun k => periodicDerivSymbol α k * mFourierCoeff f k) 2 := by
  have h := lp.memℓp (mFourierBasis.repr g)
  convert h using 1
  funext k
  rw [mFourierBasis_repr, hg k]

/-- **`W^m_2(𝕋^d) = H^m(𝕋^d)`**: all weak derivatives of order `≤ m` lie in `L_2` iff
`∑_k (1 + max_i |k_i|)^(2m) |f̂(k)|² < ∞`. -/
theorem memPeriodicSobolev_iff (m : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    MemPeriodicSobolev m f ↔
      Memℓp (fun k => ((((1 + trigDeg k : ℕ) : ℝ) ^ (m : ℝ) : ℝ) : ℂ) * mFourierCoeff f k) 2 := by
  classical
  have hw : ∀ k : d → ℤ, ‖((((1 + trigDeg k : ℕ) : ℝ) ^ (m : ℝ) : ℝ) : ℂ) * mFourierCoeff f k‖ =
      (1 + trigDeg k : ℝ) ^ m * ‖mFourierCoeff f k‖ := fun k => by
    rw [norm_mul, Complex.norm_real, Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg
      (by positivity)]
    push_cast
    rfl
  constructor
  · intro hf
    -- the coefficient sequences of `f` and of the derivatives `∂_j^m f` dominate the weight
    have h0 := (hf 0 (by simp)).choose_spec.mem_l2
    have hj : ∀ j, Memℓp (fun k => periodicDerivSymbol (Pi.single j m) k * mFourierCoeff f k) 2 :=
      fun j => (hf _ (by simp [Finset.sum_pi_single'])).choose_spec.mem_l2
    have hdom : Memℓp (fun k => 2 ^ m * (‖periodicDerivSymbol 0 k * mFourierCoeff f k‖ +
        ∑ j, ‖periodicDerivSymbol (Pi.single j m) k * mFourierCoeff f k‖)) 2 :=
      ((memℓp_norm_iff.2 h0).add (Memℓp.finsetSum _ fun j _ => memℓp_norm_iff.2 (hj j))).const_mul
        _
    refine hdom.mono fun k => ?_
    rw [hw k]
    simp only [norm_mul, ← Finset.sum_mul, ← add_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (one_add_trigDeg_pow_le m k) (norm_nonneg _)
  · intro hf α hα
    refine exists_hasPeriodicWeakDeriv
      (((memℓp_norm_iff.2 hf).const_mul ((2 * π) ^ m)).mono fun k => ?_)
    rw [norm_mul, hw k, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_periodicDerivSymbol_le hα k) (norm_nonneg _)

/-- **`W^m_2(𝕋^d) = B^m_{2,2}(𝕋^d)`** for `m ≥ 1`: the classical Sobolev space through weak
derivatives is the Besov space of the trigonometric polynomials. -/
theorem memPeriodicSobolev_iff_memBesov {m : ℕ} (hm : 1 ≤ m)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    MemPeriodicSobolev m f ↔ (trigScheme d).MemBesov 2 m 2 f := by
  rw [memPeriodicSobolev_iff, periodic_memBesov_two_two_iff (by exact_mod_cast hm)]

/-- **`W^m_2(𝕋^d)` is the range of the Sobolev embedding** for `m ≥ 1`, the Sobolev space
`H^m(𝕋^d)` of the approximation theory. -/
theorem memPeriodicSobolev_iff_mem_range {m : ℕ} (hm : 1 ≤ m)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    MemPeriodicSobolev m f ↔
      f ∈ Set.range (periodicSobolevSpace (d := d) m (by exact_mod_cast hm)).incl := by
  rw [memPeriodicSobolev_iff, periodic_mem_range_sobolev_iff]

end Torus
