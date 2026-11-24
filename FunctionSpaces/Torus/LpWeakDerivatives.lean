/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.LpFourierCoefficients
public import FunctionSpaces.Torus.WeakDerivatives
public import FunctionSpaces.Rd.Sobolev.DerivativeKernels

/-!
# Weak derivatives in `L_p(𝕋^d)`

For directions `v = (v_0, …, v_{k-1}) ∈ (ℝ^d)^k`, the derivative `∂^v = ∂_{v_0} ⋯ ∂_{v_{k-1}}`
multiplies the Fourier coefficient of index `m ∈ ℤ^d` by the **symbol**
`σ_v(m) = ∏_l 2πi ⟪m, v_l⟫` (`Torus.periodicLineSymbol`). So `g ∈ L_p(𝕋^d)` is the **weak
derivative** `∂^v f` of `f ∈ L_p(𝕋^d)` (`Torus.HasPeriodicWeakLineDeriv`) if `ĝ(m) = σ_v(m) f̂(m)`
for every `m`: the identity `∫ g φ = (-1)^k ∫ f ∂^v φ` tested with the characters `φ = e_{-m}`,
whose span is dense in the smooth functions.

* **Symbols**: `σ_v(-m) = (-1)^k σ_v(m)`, `|σ_v(m)| ≤ ∏_l 2π |m| |v_l|`, the symbol of
  concatenated directions is the product, the coordinate directions of a multi-index `α` give
  `(2πi m)^α` (`Torus.periodicLineSymbol_coordDirs`), and `σ_v(m)` expands into the symbols of the
  coordinate derivatives of order `k` (`Torus.periodicLineSymbol_eq_sum`).
* **The calculus**: for `1 ≤ p ≤ ∞` the weak derivative is unique, linear, compatible with
  composition, with limits in `L_p` and with the inclusions `L_r ⊆ L_p`, and the characters
  have the derivatives `∂^v e_k = σ_v(k) e_k`. Derivatives along the coordinate directions are
  the derivatives `∂^α` of `Torus.HasPeriodicWeakDeriv`
  (`Torus.hasPeriodicWeakDeriv_iff_hasPeriodicWeakLineDeriv`).
* **Convolution**: for `1 ≤ p < ∞` and a Schwartz kernel `η` on `ℝ^d`,
  `∂^v (η ⋆ f) = (∂^v η) ⋆ f` (`Torus.hasPeriodicWeakLineDeriv_periodicEconvLp`); for every
  integrable kernel `Φ`, `Φ ⋆ ∂^v f = ∂^v (Φ ⋆ f)`
  (`Torus.HasPeriodicWeakLineDeriv.periodicEconvLp_right`); hence `(∂^v η) ⋆ f = η ⋆ ∂^v f`
  (`Torus.periodicEconvLp_iteratedLineDerivOp`).
* **Sobolev spaces**: `f ∈ W^m_p(𝕋^d)` iff `∂^v f ∈ L_p` for all directions of order `≤ m`
  (`Torus.memPeriodicSobolev_iff_exists_hasPeriodicWeakLineDeriv`); `W^0_p = L_p`, `W^m_p` is a
  linear subspace, decreasing in `m`, and `W^m_r ⊆ W^m_p` for `p ≤ r`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus Filter Topology
open scoped ENNReal FourierTransform TorusHaar Real SchwartzMap LineDeriv

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### The symbols -/

/-- The **symbol** `σ_v(m) = ∏_l 2πi ⟪m, v_l⟫` of the derivative `∂^v = ∂_{v_0} ⋯ ∂_{v_{k-1}}`
along the directions `v ∈ (ℝ^d)^k`, at the lattice point `m ∈ ℤ^d`. -/
noncomputable def periodicLineSymbol {k : ℕ} (v : Fin k → EuclideanSpace ℝ d) (m : d → ℤ) : ℂ :=
  ∏ l, 2 * π * Complex.I * (inner ℝ (latticeVec m) (v l) : ℂ)

/-- The symbol of no directions is `1`. -/
@[simp]
theorem periodicLineSymbol_fin_zero (v : Fin 0 → EuclideanSpace ℝ d) (m : d → ℤ) :
    periodicLineSymbol v m = 1 := by
  simp [periodicLineSymbol]

/-- **The symbol at `-m`**: `σ_v(-m) = (-1)^k σ_v(m)` for `k` directions. -/
theorem periodicLineSymbol_neg {k : ℕ} (v : Fin k → EuclideanSpace ℝ d) (m : d → ℤ) :
    periodicLineSymbol v (-m) = (-1) ^ k * periodicLineSymbol v m := by
  simp only [periodicLineSymbol, latticeVec_neg, inner_neg_left, Complex.ofReal_neg, mul_neg]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

/-- **The size of the symbol**: `|σ_v(m)| ≤ ∏_l 2π |m| |v_l|`, by the Cauchy–Schwarz
inequality; the real-norm form of `Rd.enorm_prod_inner_le` with `R = |m|`. -/
theorem norm_periodicLineSymbol_le {k : ℕ} (v : Fin k → EuclideanSpace ℝ d) (m : d → ℤ) :
    ‖periodicLineSymbol v m‖ ≤ ∏ l, 2 * π * ‖latticeVec m‖ * ‖v l‖ := by
  have h : ‖periodicLineSymbol v m‖ₑ ≤ ENNReal.ofReal (2 * π * ‖latticeVec m‖) ^ k * ∏ l, ‖v l‖ₑ :=
    Rd.enorm_prod_inner_le v le_rfl
  rw [Finset.prod_mul_distrib, Fin.prod_const,
    ← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_norm,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_prod_of_nonneg fun l _ => norm_nonneg _]
  simpa only [ofReal_norm] using h

/-- **The symbol of concatenated directions** is the product of the symbols:
`σ_{(v, w)}(m) = σ_v(m) σ_w(m)`. -/
theorem periodicLineSymbol_append {k l : ℕ} (v : Fin k → EuclideanSpace ℝ d)
    (w : Fin l → EuclideanSpace ℝ d) (m : d → ℤ) :
    periodicLineSymbol (Fin.append v w) m = periodicLineSymbol v m * periodicLineSymbol w m := by
  simp only [periodicLineSymbol, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-! ### Coordinate directions -/

/-- A fixed enumeration of the `∑_i α_i` slots of a multi-index `α ∈ ℕ^d` by
`0, …, ∑_i α_i - 1`: the slot `(i, j)`, `j < α_i`, is the `j`-th derivative in the
coordinate `i`. -/
noncomputable def coordIndexEquiv (α : d → ℕ) : (Σ i, Fin (α i)) ≃ Fin (∑ i, α i) :=
  Fintype.equivFinOfCardEq (by simp)

/-- The **coordinate directions of a multi-index** `α ∈ ℕ^d`: `α_i` copies of the unit vector
`e_i` for each coordinate `i`, so that `∂^{coordDirs α} = ∂^α`. -/
noncomputable def coordDirs [DecidableEq d] (α : d → ℕ) :
    Fin (∑ i, α i) → EuclideanSpace ℝ d :=
  fun l => EuclideanSpace.single ((coordIndexEquiv α).symm l).1 1

/-- **The coordinate directions give the symbol of `∂^α`**: `σ_{coordDirs α}(m) = (2πi m)^α`. -/
theorem periodicLineSymbol_coordDirs [DecidableEq d] (α : d → ℕ) (m : d → ℤ) :
    periodicLineSymbol (coordDirs α) m = periodicDerivSymbol α m := by
  simp only [periodicLineSymbol, coordDirs, inner_latticeVec_single, Complex.ofReal_intCast]
  rw [(coordIndexEquiv α).symm.prod_comp
    (fun s : Σ i, Fin (α i) => 2 * π * Complex.I * ((m s.1 : ℤ) : ℂ)), Fintype.prod_sigma,
    periodicDerivSymbol]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The **multiplicities** of a map `c : Fin k → d`: `coordCount c i` is the number of `l` with
`c l = i`. A word `c` of coordinates is the multi-index `coordCount c` up to order. -/
def coordCount [DecidableEq d] {k : ℕ} (c : Fin k → d) (i : d) : ℕ :=
  (Finset.univ.filter fun l => c l = i).card

/-- The multiplicities of `c : Fin k → d` add up to `k`. -/
theorem sum_coordCount [DecidableEq d] {k : ℕ} (c : Fin k → d) : ∑ i, coordCount c i = k := by
  simp only [coordCount]
  rw [← Finset.card_eq_sum_card_fiberwise fun l _ => Finset.mem_univ (c l), Finset.card_univ,
    Fintype.card_fin]

/-- **A word of coordinate derivatives is `∂^α`** with `α` its multiplicities:
`∏_l 2πi m_{c_l} = (2πi m)^{coordCount c}`. -/
theorem prod_eq_periodicDerivSymbol_coordCount [DecidableEq d] {k : ℕ} (c : Fin k → d) (m : d → ℤ) :
    ∏ l, 2 * π * Complex.I * (m (c l) : ℂ) = periodicDerivSymbol (coordCount c) m := by
  rw [← Finset.prod_fiberwise' Finset.univ c (fun i => 2 * π * Complex.I * (m i : ℂ)),
    periodicDerivSymbol]
  simp only [Finset.prod_const, coordCount]

/-- **The symbol in coordinates**: `σ_v(m) = ∑_{c : Fin k → d} (∏_l (v_l)_{c_l}) (2πi m)^α_c`
with `α_c = coordCount c`, by expanding `∏_l ∑_i 2πi m_i (v_l)_i` (Mathlib's
`Finset.prod_univ_sum`). -/
theorem periodicLineSymbol_eq_sum [DecidableEq d] {k : ℕ} (v : Fin k → EuclideanSpace ℝ d)
    (m : d → ℤ) :
    periodicLineSymbol v m =
      ∑ c : Fin k → d, ((∏ l, v l (c l) : ℝ) : ℂ) * periodicDerivSymbol (coordCount c) m := by
  have h : ∀ l, 2 * π * Complex.I * (inner ℝ (latticeVec m) (v l) : ℂ) =
      ∑ i, (v l i : ℂ) * (2 * π * Complex.I * (m i : ℂ)) := fun l => by
    rw [inner_latticeVec, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  simp only [periodicLineSymbol, h]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_mul_distrib, prod_eq_periodicDerivSymbol_coordCount, Complex.ofReal_prod]

/-! ### Weak derivatives along directions -/

/-- `g ∈ L_p(𝕋^d)` is the **weak derivative** `∂^v f` of `f ∈ L_p(𝕋^d)` along the directions
`v ∈ (ℝ^d)^k`: `ĝ(m) = σ_v(m) f̂(m)` for every `m ∈ ℤ^d`. This is the integral identity
`∫ g φ = (-1)^k ∫ f ∂^v φ` tested with the trigonometric polynomials `φ`. The definition is meant
for `1 ≤ p ≤ ∞`, where every element of `L_p(𝕋^d)` is integrable and its coefficients are
integrals. It is the distributional derivative of the periodic lifts on `ℝ^d`
(`Torus.hasPeriodicWeakLineDeriv_iff_comp_quotientProj`). -/
def HasPeriodicWeakLineDeriv {p : ℝ≥0∞} {k : ℕ} (v : Fin k → EuclideanSpace ℝ d)
    (f g : Lp ℂ p (volume : Measure (UnitAddTorus d))) : Prop :=
  ∀ m : d → ℤ, mFourierCoeff g m = periodicLineSymbol v m * mFourierCoeff f m

variable {p : ℝ≥0∞} {k : ℕ} {v : Fin k → EuclideanSpace ℝ d}

/-- `f` is its own derivative along no directions. -/
theorem hasPeriodicWeakLineDeriv_fin_zero (v : Fin 0 → EuclideanSpace ℝ d)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : HasPeriodicWeakLineDeriv v f f := fun m => by
  rw [periodicLineSymbol_fin_zero, one_mul]

/-- **Derivatives along coordinate directions are the derivatives `∂^α`**:
`∂^{coordDirs α} f = ∂^α f`. -/
theorem hasPeriodicWeakDeriv_iff_hasPeriodicWeakLineDeriv [DecidableEq d] {α : d → ℕ}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    HasPeriodicWeakDeriv α f g ↔ HasPeriodicWeakLineDeriv (coordDirs α) f g := by
  simp only [HasPeriodicWeakDeriv, HasPeriodicWeakLineDeriv, periodicLineSymbol_coordDirs]

/-- **The weak derivatives compose**: if `g = ∂^v f` and `h = ∂^w g`, then `h = ∂^{(w, v)} f`. -/
theorem HasPeriodicWeakLineDeriv.comp {l : ℕ} {w : Fin l → EuclideanSpace ℝ d}
    {f g h : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hg : HasPeriodicWeakLineDeriv v f g)
    (hh : HasPeriodicWeakLineDeriv w g h) :
    HasPeriodicWeakLineDeriv (Fin.append w v) f h := fun m => by
  rw [hh m, hg m, periodicLineSymbol_append, mul_assoc]

variable [Fact (1 ≤ p)]

/-- **The weak derivative is unique** in `L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, since an element of `L_p` is
determined by its Fourier coefficients (`Torus.eq_of_mFourierCoeff_eq`). -/
theorem HasPeriodicWeakLineDeriv.unique {f g g' : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : HasPeriodicWeakLineDeriv v f g) (hg' : HasPeriodicWeakLineDeriv v f g') : g = g' :=
  eq_of_mFourierCoeff_eq fun m => by rw [hg m, hg' m]

/-- **The weak derivative `∂^α` is unique** in `L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, since an element of
`L_p` is determined by its Fourier coefficients (`Torus.eq_of_mFourierCoeff_eq`). -/
theorem HasPeriodicWeakDeriv.unique {α : d → ℕ}
    {f g g' : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : HasPeriodicWeakDeriv α f g) (hg' : HasPeriodicWeakDeriv α f g') : g = g' :=
  eq_of_mFourierCoeff_eq fun m => by rw [hg m, hg' m]

/-- **The weak derivative is additive**: `∂^v (f₁ + f₂) = ∂^v f₁ + ∂^v f₂`. -/
theorem HasPeriodicWeakLineDeriv.add {f₁ f₂ g₁ g₂ : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h₁ : HasPeriodicWeakLineDeriv v f₁ g₁) (h₂ : HasPeriodicWeakLineDeriv v f₂ g₂) :
    HasPeriodicWeakLineDeriv v (f₁ + f₂) (g₁ + g₂) := fun m => by
  rw [mFourierCoeff_add, mFourierCoeff_add, h₁ m, h₂ m, mul_add]

omit [Fact (1 ≤ p)] in
/-- **The weak derivative is homogeneous**: `∂^v (c f) = c ∂^v f`. -/
theorem HasPeriodicWeakLineDeriv.smul (c : ℂ) {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : HasPeriodicWeakLineDeriv v f g) : HasPeriodicWeakLineDeriv v (c • f) (c • g) := fun m => by
  rw [mFourierCoeff_smul, mFourierCoeff_smul, h m, mul_left_comm]

/-- **`∂^α` is additive**: `∂^α (f₁ + f₂) = ∂^α f₁ + ∂^α f₂`. -/
theorem HasPeriodicWeakDeriv.add {α : d → ℕ}
    {f₁ f₂ g₁ g₂ : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h₁ : HasPeriodicWeakDeriv α f₁ g₁) (h₂ : HasPeriodicWeakDeriv α f₂ g₂) :
    HasPeriodicWeakDeriv α (f₁ + f₂) (g₁ + g₂) := fun m => by
  rw [mFourierCoeff_add, mFourierCoeff_add, h₁ m, h₂ m, mul_add]

omit [Fact (1 ≤ p)] in
/-- **`∂^α` is homogeneous**: `∂^α (c f) = c ∂^α f`. -/
theorem HasPeriodicWeakDeriv.smul {α : d → ℕ} (c : ℂ)
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : HasPeriodicWeakDeriv α f g) : HasPeriodicWeakDeriv α (c • f) (c • g) := fun m => by
  rw [mFourierCoeff_smul, mFourierCoeff_smul, h m, mul_left_comm]

/-- `∂^v (-f) = -∂^v f`. -/
theorem HasPeriodicWeakLineDeriv.neg {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : HasPeriodicWeakLineDeriv v f g) : HasPeriodicWeakLineDeriv v (-f) (-g) := fun m => by
  rw [mFourierCoeff_neg, mFourierCoeff_neg, h m, mul_neg]

/-- `∂^v (f₁ - f₂) = ∂^v f₁ - ∂^v f₂`. -/
theorem HasPeriodicWeakLineDeriv.sub {f₁ f₂ g₁ g₂ : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h₁ : HasPeriodicWeakLineDeriv v f₁ g₁) (h₂ : HasPeriodicWeakLineDeriv v f₂ g₂) :
    HasPeriodicWeakLineDeriv v (f₁ - f₂) (g₁ - g₂) := fun m => by
  rw [mFourierCoeff_sub, mFourierCoeff_sub, h₁ m, h₂ m, mul_sub]

/-- **The weak derivative of a finite sum** is the sum of the weak derivatives. -/
theorem HasPeriodicWeakLineDeriv.sum {ι : Type*} (s : Finset ι)
    {F G : ι → Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : ∀ i ∈ s, HasPeriodicWeakLineDeriv v (F i) (G i)) :
    HasPeriodicWeakLineDeriv v (∑ i ∈ s, F i) (∑ i ∈ s, G i) := fun m => by
  rw [mFourierCoeff_sum, mFourierCoeff_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi m

/-- **Weak derivatives pass to limits**: if `f_i → f` and `g_i → g` in `L_p(𝕋^d)` and eventually
`g_i = ∂^v f_i`, then `g = ∂^v f`, since every Fourier coefficient is a continuous functional
(`Torus.coeffCLM`). -/
theorem HasPeriodicWeakLineDeriv.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {F G : ι → Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hF : Tendsto F l (𝓝 f))
    (hG : Tendsto G l (𝓝 g)) (h : ∀ᶠ i in l, HasPeriodicWeakLineDeriv v (F i) (G i)) :
    HasPeriodicWeakLineDeriv v f g := fun m => by
  have hGm := ((coeffCLM p m).continuous.tendsto g).comp hG
  have hFm := (((coeffCLM p m).continuous.tendsto f).comp hF).const_mul (periodicLineSymbol v m)
  refine tendsto_nhds_unique hGm (hFm.congr' (h.mono fun i hi => ?_))
  simp only [Function.comp_apply, coeffCLM_apply]
  exact (hi m).symm

/-- **The derivatives of the characters**: `∂^v e_k = σ_v(k) e_k` in `L_p(𝕋^d)`. -/
theorem hasPeriodicWeakLineDeriv_mFourierLp (v : Fin k → EuclideanSpace ℝ d) (n : d → ℤ) :
    HasPeriodicWeakLineDeriv v (mFourierLp (d := d) p n)
      (periodicLineSymbol v n • mFourierLp p n) :=
  fun m => by
    rw [mFourierCoeff_smul, mFourierCoeff_mFourierLp]
    by_cases hn : n = m
    · rw [hn]
    · simp only [hn, ↓reduceIte, mul_zero]

/-! ### Weak derivatives and convolution -/

/-- **The derivative of a convolution** falls on the kernel: `∂^v (η ⋆ f) = (∂^v η) ⋆ f` for
`f ∈ L_p(𝕋^d)` and every Schwartz kernel `η` on `ℝ^d`. -/
theorem hasPeriodicWeakLineDeriv_periodicEconvLp (hp : p ≠ ∞) (v : Fin k → EuclideanSpace ℝ d)
    (η : 𝓢(EuclideanSpace ℝ d, ℂ)) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    HasPeriodicWeakLineDeriv v (periodicEconvLp hp η.integrable f)
      (periodicEconvLp hp (∂^{v} η).integrable f) :=
  fun m => by
    rw [mFourierCoeff_periodicEconvLp, mFourierCoeff_periodicEconvLp, ← SchwartzMap.fourier_coe,
      SchwartzMap.fourier_iteratedLineDerivOp_apply, ← SchwartzMap.fourier_coe, smul_eq_mul,
      periodicLineSymbol]
    ring

/-- **Convolution keeps weak derivatives**: if `g = ∂^v f` in `L_p(𝕋^d)`, `1 ≤ p < ∞`, then
`Φ ⋆ g = ∂^v (Φ ⋆ f)` for every integrable kernel `Φ` on `ℝ^d`; both sides have the coefficients
`𝓕Φ(m) σ_v(m) f̂(m)` (`Torus.mFourierCoeff_periodicEconvLp`). -/
theorem HasPeriodicWeakLineDeriv.periodicEconvLp_right (hp : p ≠ ∞)
    {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} (h : HasPeriodicWeakLineDeriv v f g) :
    HasPeriodicWeakLineDeriv v (Torus.periodicEconvLp hp hΦ f)
      (Torus.periodicEconvLp hp hΦ g) := fun m => by
  rw [mFourierCoeff_periodicEconvLp, mFourierCoeff_periodicEconvLp, h m, mul_left_comm]

/-- **Derivatives move from the kernel to the function**: if `g = ∂^v f` in `L_p(𝕋^d)`,
`1 ≤ p < ∞`, then `(∂^v η) ⋆ f = η ⋆ g` for every Schwartz kernel `η` on `ℝ^d`. Both sides have
the derivative `∂^v (η ⋆ f)` (`Torus.hasPeriodicWeakLineDeriv_periodicEconvLp`,
`Torus.HasPeriodicWeakLineDeriv.periodicEconvLp_right`), which is unique. -/
theorem periodicEconvLp_iteratedLineDerivOp (hp : p ≠ ∞)
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} (h : HasPeriodicWeakLineDeriv v f g)
    (η : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    periodicEconvLp hp (∂^{v} η).integrable f = periodicEconvLp hp η.integrable g :=
  (hasPeriodicWeakLineDeriv_periodicEconvLp hp v η f).unique
    (h.periodicEconvLp_right hp η.integrable)

/-! ### Sobolev spaces -/

/-- **A derivative along directions from the coordinate derivatives**: if `g_c = ∂^{α_c} f` for
the multiplicities `α_c` of every word `c : Fin k → d`, then
`∑_c (∏_l (v_l)_{c_l}) g_c = ∂^v f` (`Torus.periodicLineSymbol_eq_sum`). -/
theorem hasPeriodicWeakLineDeriv_sum_coordCount [DecidableEq d]
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin k → d) → Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ c, HasPeriodicWeakDeriv (coordCount c) f (g c)) :
    HasPeriodicWeakLineDeriv v f (∑ c, ((∏ l, v l (c l) : ℝ) : ℂ) • g c) := fun m => by
  rw [mFourierCoeff_sum, periodicLineSymbol_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mFourierCoeff_smul, hg c m, mul_assoc]

/-- **Sobolev spaces through directional derivatives**: `f ∈ W^m_p(𝕋^d)` iff for every order
`k ≤ m` and all directions `v ∈ (ℝ^d)^k` the weak derivative `∂^v f` lies in `L_p`. The coordinate
directions of a multi-index give one direction (`Torus.coordDirs`); the expansion of `σ_v` into
coordinate symbols gives the other (`Torus.hasPeriodicWeakLineDeriv_sum_coordCount`). -/
theorem memPeriodicSobolev_iff_exists_hasPeriodicWeakLineDeriv {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    MemPeriodicSobolev m f ↔
      ∀ k ≤ m, ∀ v : Fin k → EuclideanSpace ℝ d, ∃ g, HasPeriodicWeakLineDeriv v f g := by
  classical
  constructor
  · intro hf k hk v
    have hc : ∀ c : Fin k → d, ∃ g, HasPeriodicWeakDeriv (coordCount c) f g := fun c =>
      hf _ (by rw [sum_coordCount]; exact hk)
    choose g hg using hc
    exact ⟨_, hasPeriodicWeakLineDeriv_sum_coordCount hg⟩
  · intro hf α hα
    obtain ⟨g, hg⟩ := hf _ hα (coordDirs α)
    exact ⟨g, hasPeriodicWeakDeriv_iff_hasPeriodicWeakLineDeriv.2 hg⟩

omit [Fact (1 ≤ p)] in
/-- **`W^0_p = L_p`**: every `f ∈ L_p(𝕋^d)` lies in `W^0_p(𝕋^d)`. -/
theorem memPeriodicSobolev_zero (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    MemPeriodicSobolev 0 f :=
  fun α hα => by
    have h0 : α = 0 := funext fun i =>
      (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hα)) i (Finset.mem_univ i)
    exact ⟨f, h0 ▸ hasPeriodicWeakDeriv_zero f⟩

/-- **`W^m_p` is closed under addition**. -/
theorem MemPeriodicSobolev.add {m : ℕ} {f₁ f₂ : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h₁ : MemPeriodicSobolev m f₁) (h₂ : MemPeriodicSobolev m f₂) :
    MemPeriodicSobolev m (f₁ + f₂) := fun α hα => by
  obtain ⟨g₁, hg₁⟩ := h₁ α hα
  obtain ⟨g₂, hg₂⟩ := h₂ α hα
  exact ⟨g₁ + g₂, hg₁.add hg₂⟩

omit [Fact (1 ≤ p)] in
/-- **`W^m_p` is closed under scalar multiplication**. -/
theorem MemPeriodicSobolev.smul {m : ℕ} (c : ℂ) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (h : MemPeriodicSobolev m f) : MemPeriodicSobolev m (c • f) := fun α hα => by
  obtain ⟨g, hg⟩ := h α hα
  exact ⟨c • g, hg.smul c⟩

omit [Fact (1 ≤ p)] in
/-- **`W^m_p` decreases in `m`**: `W^m_p ⊆ W^{m'}_p` for `m' ≤ m`. -/
theorem MemPeriodicSobolev.mono_order {m m' : ℕ} (hm : m' ≤ m)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (h : MemPeriodicSobolev m f) :
    MemPeriodicSobolev m' f :=
  fun α hα => h α (hα.trans hm)

variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- **The inclusion `L_r ⊆ L_p` keeps weak derivatives**: for `p ≤ r`, if `g = ∂^v f` in `L_r`,
then the same holds for the classes in `L_p`. -/
theorem HasPeriodicWeakLineDeriv.of_inclusion (hpr : p ≤ r)
    {f g : Lp ℂ r (volume : Measure (UnitAddTorus d))} (h : HasPeriodicWeakLineDeriv v f g) :
    HasPeriodicWeakLineDeriv v (Lp.inclusionOfExponentLe (𝕜 := ℂ) volume hpr f)
      (Lp.inclusionOfExponentLe (𝕜 := ℂ) volume hpr g) := fun m => by
  rw [mFourierCoeff_inclusionOfExponentLe, mFourierCoeff_inclusionOfExponentLe, h m]

/-- **The inclusion `L_r ⊆ L_p` keeps the derivatives `∂^α`**, `p ≤ r`. -/
theorem HasPeriodicWeakDeriv.of_inclusion (hpr : p ≤ r) {α : d → ℕ}
    {f g : Lp ℂ r (volume : Measure (UnitAddTorus d))} (h : HasPeriodicWeakDeriv α f g) :
    HasPeriodicWeakDeriv α (Lp.inclusionOfExponentLe (𝕜 := ℂ) volume hpr f)
      (Lp.inclusionOfExponentLe (𝕜 := ℂ) volume hpr g) := fun m => by
  rw [mFourierCoeff_inclusionOfExponentLe, mFourierCoeff_inclusionOfExponentLe, h m]

/-- **`W^m_r ⊆ W^m_p` for `p ≤ r`**: the class in `L_p` of `f ∈ W^m_r(𝕋^d)` lies in
`W^m_p(𝕋^d)`. -/
theorem MemPeriodicSobolev.of_inclusion (hpr : p ≤ r) {m : ℕ}
    {f : Lp ℂ r (volume : Measure (UnitAddTorus d))} (h : MemPeriodicSobolev m f) :
    MemPeriodicSobolev m (Lp.inclusionOfExponentLe (𝕜 := ℂ) volume hpr f) := fun α hα => by
  obtain ⟨g, hg⟩ := h α hα
  exact ⟨_, hg.of_inclusion hpr⟩

end Torus
