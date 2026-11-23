/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Sobolev.SobolevRestrictionInclusions
public import FunctionSpaces.Analysis.Hilbert.GelfandTriple
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Duality of Sobolev spaces on open sets and Gelfand triples

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω ⊆ V` open and `s` real. The Hilbert spaces `H̃^s(Ω)` and `H^{-s}(Ω)` of
`FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean` are dual to each other, as in
Chandler-Wilde, Hewett and Moiola (Theorem 3.3), for every open set and every real `s`.

* **The Bessel potential on Schwartz functions**: `J_t u = 𝓕⁻(⟨ξ⟩^t 𝓕u)` (`Rd.besselSchwartz`, in
  `FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley`) is real for real `u`
  (`Rd.conj_besselSchwartz_apply`); for `g ∈ L_2(V)`, `(J_t g)(u) = ∫ J_t u · g`
  (`Rd.besselPotential_toLp_apply`).
* **`J_{2s}` as an isometry**: `Rd.besselShift s : H^s(V) ≃ₗᵢ[ℂ] H^{-s}(V)` keeps the `L_2`
  function `J_s U` and acts on distributions as `J_{2s}` (`Rd.toDistr_besselShift`).
* **The pairing** `[W, U] = ⟪J_{-s} W, J_s U⟫_{L_2}` of `W ∈ H^{-s}(V)` and `U ∈ H^s(V)`
  (`Rd.pairing`, bundled in `U` as `Rd.pairingCLM`) has `|[W, U]| ≤ ‖W‖ ‖U‖` and extends `U(φ)`
  and `conj (W(φ))` for test functions `φ` (`Rd.pairing_ofTest_left`, `Rd.pairing_ofTest_right`);
  at `s = 1` and for Schwartz `W` it is the `L_2` inner product (`Rd.pairing_one_toLp`).
* **Orthogonal complements**: `⟪U, φ⟫_{H^s} = conj ((J_{2s} U)(φ))` for test functions `φ`
  (`Rd.inner_ofTest_eq`), so `U ⊥ H̃^s(Ω)` iff `J_{2s} U` vanishes on `Ω`
  (`Rd.mem_orthogonal_tildeSpace_iff`), and `J_{2s}` maps `H̃^s(Ω)` onto `H^{-s}(Ω)`
  (`Rd.tildeEquivRestriction`) and `H^s(Ω)` onto `H̃^{-s}(Ω)` (`Rd.restrictionEquivTilde`).
  Elements vanishing on `Ω` pair to zero with `H̃^s(Ω)` (`Rd.pairing_eq_zero_of_mem_vanishOn_left`,
  `Rd.pairing_eq_zero_of_mem_vanishOn_right`).
* **Duality**: `(H̃^s(Ω))^* ≅ H^{-s}(Ω)` (`Rd.dualEquiv`), `(H^s(Ω))^* ≅ H̃^{-s}(Ω)`
  (`Rd.dualRestrictionEquiv`) and `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` (`Rd.dualZeroBoundaryEquiv`), each
  through the pairing, conjugate-linear and isometric; the pairing may use every extension of the
  representing element (`Rd.dualEquiv_apply_of_restrictProj_eq`,
  `Rd.dualRestrictionEquiv_apply_restrictProj`).
* **Gelfand triples**, `s ≥ 0`: `ι_s : H^s(V) → L_2(V)` and its restriction
  `H̃^s(Ω) → L_2(Ω)` (`Rd.tildeToL2`) are injective with dense range (`Rd.denseRange_sobolevToL2`,
  `Rd.tildeToL2_injective`, `Rd.denseRange_tildeToL2`), so their pivot duals are injective
  (`ContinuousLinearMap.pivotDual_injective_iff`) and `L_2` is the pivot space of
  `H^s(V) ⊂ L_2(V) ⊂ H^{-s}(V)` and of `H̃^s(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)`. The pivot dual of `ι_s`
  is the pairing with the element of `H^{-s}(V)` of an `L_2` function
  (`Rd.pivotDual_sobolevToL2_apply_apply`); the pivot dual of `H̃^s(Ω) → L_2(Ω)` sends
  `g ∈ L_2(Ω)` to `U ↦ ∫_Ω conj (g) ι_s U`, the pairing with an element of `H^{-s}(Ω)`
  (`Rd.pivotDual_tildeToL2_apply_apply`, `Rd.pairing_dualEquiv_pivotDual_tildeToL2`).
-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace ComplexConjugate
open scoped ENNReal SchwartzMap Real BesselPotentialSpace FourierTransform InnerProductSpace
  Distributions
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Bessel potential on Schwartz functions -/

/-- **`J_t` keeps real functions real**: for a Schwartz function `u` with real values,
`conj (J_t u(x)) = J_t u(x)` (`Rd.conj_fourierInv_apply`, `Rd.conj_fourier_apply`,
`Rd.besselSchwartz_apply_eq_fourier`). -/
theorem conj_besselSchwartz_apply (t : ℝ) {u : 𝓢(V, ℂ)} (hu : ∀ x, conj (u x) = u x) (x : V) :
    conj (besselSchwartz t u x) = besselSchwartz t u x := by
  conv_rhs => rw [besselSchwartz_apply_eq_fourier]
  rw [besselSchwartz_apply, conj_fourierInv_apply]
  refine congrFun (congrArg _ (funext fun ξ => ?_)) x
  rw [map_mul, Complex.conj_ofReal, conj_fourier_apply]
  simp only [hu]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **A test function is real**: `conj (φ(x)) = φ(x)` for the Schwartz function of a real test
function `φ`. -/
theorem conj_testSchwartz {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (x : V) :
    conj (testSchwartz φ x) = testSchwartz φ x := by
  simp

/-- **The Bessel potential of an `L_2` function at a Schwartz function**: for `g ∈ L_2(V)` and a
Schwartz function `u`, `(J_t g)(u) = ∫ J_t u · g`, since Mathlib's `J_t` acts by the transpose
(`Rd.besselPotential_apply_apply`). -/
theorem besselPotential_toLp_apply (t : ℝ) (g : Lp ℂ 2 (volume : Measure V)) (u : 𝓢(V, ℂ)) :
    besselPotential V ℂ t (g : 𝓢'(V, ℂ)) u = ∫ x, besselSchwartz t u x * g x := by
  rw [besselPotential_apply_apply, Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]

/-- **`J_t` of a real Schwartz function against `L_2`**: for a Schwartz function `u` with real
values and `g ∈ L_2(V)`, `⟪J_t u, g⟫_{L_2} = (J_t g)(u)`: the inner product is
`∫ conj (J_t u) · g`, and `J_t u` is real (`Rd.conj_besselSchwartz_apply`,
`Rd.besselPotential_toLp_apply`). -/
theorem inner_toLp_besselSchwartz (t : ℝ) {u : 𝓢(V, ℂ)} (hu : ∀ x, conj (u x) = u x)
    (g : Lp ℂ 2 (volume : Measure V)) :
    ⟪(besselSchwartz t u).toLp 2, g⟫_ℂ = besselPotential V ℂ t (g : 𝓢'(V, ℂ)) u := by
  rw [MeasureTheory.L2.inner_def, besselPotential_toLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [(besselSchwartz t u).coeFn_toLp 2 volume] with x hx
  rw [hx, RCLike.inner_apply', conj_besselSchwartz_apply t hu]

/-! ### The inner product of `H^t(V)` and Schwartz functions -/

/-- **The inner product of `H^t(V)` is that of the `L_2` functions**:
`⟪U, W⟫_{H^t} = ⟪J_t U, J_t W⟫_{L_2}`, which is how Mathlib defines the inner product of
`BesselPotentialSpace`. -/
theorem inner_toLp_toLp {t : ℝ} (U W : H^{t}(V)) : ⟪U.toLp, W.toLp⟫_ℂ = ⟪U, W⟫_ℂ :=
  rfl

/-- **The `L_2` function of a Schwartz function in `H^t(V)`**: for a Schwartz function `u`, the
element `u ∈ H^t(V)` (Mathlib's `SchwartzMap.memSobolev`) has `J_t u` as its `L_2` function, since
`L_2` functions are determined by their distributions (`Rd.eq_of_toTemperedDistribution_eq`). -/
theorem toLp_schwartz (t : ℝ) (u : 𝓢(V, ℂ)) :
    (u.memSobolev (s := t) (p := 2)).toBesselPotentialSpace.toLp =
      (besselSchwartz t u).toLp 2 := by
  have h : (((u.memSobolev (s := t) (p := 2)).toBesselPotentialSpace.toLp :
      Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (((besselSchwartz t u).toLp 2 : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) := by
    rw [← BesselPotentialSpace.bessel_toDistr_eq_toLp,
      TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr, besselPotential_schwartz,
      Lp.toTemperedDistribution_toLp_eq]
  exact eq_of_toTemperedDistribution_eq h

/-- The `L_2` function of a test function `φ` in `H^t(V)` is `J_t φ` (`Rd.toLp_schwartz`). -/
theorem toLp_ofTest {Ω : Opens V} (t : ℝ) (φ : 𝓓(Ω, ℝ)) :
    (ofTest t φ).toLp = (besselSchwartz t (testSchwartz φ)).toLp 2 :=
  toLp_schwartz t (testSchwartz φ)

/-- **Test functions against `L_2`**: for a test function `φ` of `Ω`, as an element of `H^t(V)`,
and `g ∈ L_2(V)`, `⟪J_t φ, g⟫_{L_2} = (J_t g)(φ)` (`Rd.inner_toLp_besselSchwartz`). -/
theorem inner_ofTest_toLp {Ω : Opens V} (t : ℝ) (φ : 𝓓(Ω, ℝ))
    (g : Lp ℂ 2 (volume : Measure V)) :
    ⟪(ofTest t φ).toLp, g⟫_ℂ = besselPotential V ℂ t (g : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [toLp_ofTest]
  exact inner_toLp_besselSchwartz t (conj_testSchwartz φ) g

/-- **Inner products with a test function in the left slot**: for a test function `φ` of `Ω` and
`U ∈ H^t(V)`, `⟪φ, U⟫_{H^t} = (J_t (J_t U))(φ)`, the distribution `J_t` of the `L_2` function
`J_t U` at `φ` (`Rd.inner_ofTest_toLp`). -/
theorem inner_ofTest_left {Ω : Opens V} (t : ℝ) (φ : 𝓓(Ω, ℝ)) (U : H^{t}(V)) :
    ⟪ofTest t φ, U⟫_ℂ = besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [← inner_toLp_toLp, inner_ofTest_toLp]

/-! ### `J_{2s}` as an isometry -/

variable (s : ℝ) in
/-- **`J_{2s}` as an isometry of `H^s(V)` onto `H^{-s}(V)`**: both spaces are isometric to
`L_2(V)` (Mathlib's `BesselPotentialSpace.toLpₗᵢ`), and `besselShift s U` is the element of
`H^{-s}(V)` with the same `L_2` function `J_s U` as `U`; on distributions it is `J_{2s}`
(`Rd.toDistr_besselShift`). -/
noncomputable def besselShift : H^{s}(V) ≃ₗᵢ[ℂ] H^{-s}(V) :=
  (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).trans (BesselPotentialSpace.toLpₗᵢ V ℂ (-s) 2).symm

variable {s : ℝ} {Ω : Opens V}

/-- An element of `H^t(V)` built from an `L_2` function `f` by the inverse of Mathlib's isometry
`BesselPotentialSpace.toLpₗᵢ` has `f` as its `L_2` function. -/
theorem toLp_toLpLinearIsometry_symm_apply (t : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    ((BesselPotentialSpace.toLpₗᵢ V ℂ t 2).symm f).toLp = f := by
  rw [← BesselPotentialSpace.toLpₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply]

/-- `besselShift s U` has the same `L_2` function as `U`. -/
@[simp]
theorem toLp_besselShift (U : H^{s}(V)) : (besselShift s U).toLp = U.toLp := by
  rw [besselShift, LinearIsometryEquiv.trans_apply, BesselPotentialSpace.toLpₗᵢ_apply,
    toLp_toLpLinearIsometry_symm_apply]

/-- The distribution of `besselShift s U` is `J_s` of the `L_2` function `J_s U`. -/
theorem toDistr_besselShift_eq_besselPotential_toLp (U : H^{s}(V)) :
    (besselShift s U).toDistr = besselPotential V ℂ s (U.toLp : 𝓢'(V, ℂ)) := by
  rw [besselShift, LinearIsometryEquiv.trans_apply, BesselPotentialSpace.toLpₗᵢ_apply,
    BesselPotentialSpace.toLpₗᵢ_symm_apply, neg_neg]

/-- **Inner products with test functions through `besselShift`**: for `U ∈ H^s(V)` and a test
function `φ` of `Ω`, `⟪U, φ⟫_{H^s} = conj ((J_{2s} U)(φ))`, the conjugate of the distribution
`besselShift s U` at `φ` (`Rd.inner_ofTest_left`,
`Rd.toDistr_besselShift_eq_besselPotential_toLp`). -/
theorem inner_ofTest_eq (U : H^{s}(V)) (φ : 𝓓(Ω, ℝ)) :
    ⟪U, ofTest s φ⟫_ℂ = conj ((besselShift s U).toDistr (testSchwartz φ)) := by
  rw [← inner_conj_symm, inner_ofTest_left, toDistr_besselShift_eq_besselPotential_toLp]

/-- **`besselShift s` is `J_{2s}` on distributions**: the distribution of `besselShift s U` is
`J_{2s} U`, since `J_s U` is the `L_2` function of `U` and `J_s J_s = J_{2s}` (Mathlib's
`TemperedDistribution.besselPotential_besselPotential_apply`). -/
theorem toDistr_besselShift (U : H^{s}(V)) :
    (besselShift s U).toDistr = besselPotential V ℂ (2 * s) U.toDistr := by
  rw [toDistr_besselShift_eq_besselPotential_toLp, ← U.bessel_toDistr_eq_toLp,
    TemperedDistribution.besselPotential_besselPotential_apply, two_mul]

/-- **The inverse of `besselShift s`** is `besselShift (-s)`, read in `H^s(V)` through
`-(-s) = s` (Mathlib's `BesselPotentialSpace.copy`): both keep the `L_2` function. -/
theorem besselShift_symm_apply (W : H^{-s}(V)) :
    (besselShift s).symm W = (besselShift (-s) W).copy s (neg_neg s) := by
  refine BesselPotentialSpace.injective_toLp V ℂ s 2 ?_
  rw [BesselPotentialSpace.toLp_copy _ (neg_neg s), toLp_besselShift, besselShift,
    LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm, BesselPotentialSpace.toLpₗᵢ_apply,
    toLp_toLpLinearIsometry_symm_apply]

/-- The inverse of `besselShift s` keeps the `L_2` function. -/
@[simp]
theorem toLp_besselShift_symm (W : H^{-s}(V)) : ((besselShift s).symm W).toLp = W.toLp := by
  rw [besselShift_symm_apply, BesselPotentialSpace.toLp_copy _ (neg_neg s), toLp_besselShift]

/-- The distribution of `(besselShift s)⁻¹ W` is `J_{-s}` of the `L_2` function of `W`. -/
theorem toDistr_besselShift_symm (W : H^{-s}(V)) :
    ((besselShift s).symm W).toDistr = besselPotential V ℂ (-s) (W.toLp : 𝓢'(V, ℂ)) := by
  rw [besselShift, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm, BesselPotentialSpace.toLpₗᵢ_apply,
    BesselPotentialSpace.toLpₗᵢ_symm_apply]

/-! ### The pairing of `H^{-s}(V)` and `H^s(V)` -/

variable (s) in
/-- **The pairing of `H^{-s}(V)` and `H^s(V)`**: `[W, U] = ⟪J_{-s} W, J_s U⟫_{L_2}`, the `L_2`
inner product of the `L_2` functions of `W` and `U`. It is conjugate-linear in `W`
(`Rd.pairing_add_left`, `Rd.pairing_smul_left`) and linear in `U` (`Rd.pairing_add_right`,
`Rd.pairing_smul_right`, `Rd.pairingCLM`), Mathlib's convention for inner products. For test
functions it is the distributional pairing (`Rd.pairing_ofTest_left`, `Rd.pairing_ofTest_right`). -/
noncomputable def pairing (W : H^{-s}(V)) (U : H^{s}(V)) : ℂ :=
  ⟪W.toLp, U.toLp⟫_ℂ

/-- The pairing is additive in `W`: `[W + W', U] = [W, U] + [W', U]`. -/
theorem pairing_add_left (W W' : H^{-s}(V)) (U : H^{s}(V)) :
    pairing s (W + W') U = pairing s W U + pairing s W' U := by
  simp only [pairing, BesselPotentialSpace.toLp_add, inner_add_left]

/-- The pairing respects differences in `W`: `[W - W', U] = [W, U] - [W', U]`. -/
theorem pairing_sub_left (W W' : H^{-s}(V)) (U : H^{s}(V)) :
    pairing s (W - W') U = pairing s W U - pairing s W' U := by
  simp only [pairing, BesselPotentialSpace.toLp_sub, inner_sub_left]

/-- The pairing is conjugate-homogeneous in `W`: `[c W, U] = conj c · [W, U]`. -/
theorem pairing_smul_left (c : ℂ) (W : H^{-s}(V)) (U : H^{s}(V)) :
    pairing s (c • W) U = conj c * pairing s W U := by
  simp only [pairing, BesselPotentialSpace.toLp_smul, inner_smul_left]

/-- The pairing is additive in `U`: `[W, U + U'] = [W, U] + [W, U']`. -/
theorem pairing_add_right (W : H^{-s}(V)) (U U' : H^{s}(V)) :
    pairing s W (U + U') = pairing s W U + pairing s W U' := by
  simp only [pairing, BesselPotentialSpace.toLp_add, inner_add_right]

/-- The pairing respects differences in `U`: `[W, U - U'] = [W, U] - [W, U']`. -/
theorem pairing_sub_right (W : H^{-s}(V)) (U U' : H^{s}(V)) :
    pairing s W (U - U') = pairing s W U - pairing s W U' := by
  simp only [pairing, BesselPotentialSpace.toLp_sub, inner_sub_right]

/-- The pairing is homogeneous in `U`: `[W, c U] = c · [W, U]`. -/
theorem pairing_smul_right (W : H^{-s}(V)) (c : ℂ) (U : H^{s}(V)) :
    pairing s W (c • U) = c * pairing s W U := by
  simp only [pairing, BesselPotentialSpace.toLp_smul, inner_smul_right]

variable (s) in
/-- **The pairing as a bounded functional**: for `W ∈ H^{-s}(V)`, `U ↦ [W, U]` as a continuous
linear map `H^s(V) → ℂ`, the inner product with `J_{-s} W` (Mathlib's `innerSL`) after the
isometry `U ↦ J_s U` onto `L_2(V)`. -/
noncomputable def pairingCLM (W : H^{-s}(V)) : H^{s}(V) →L[ℂ] ℂ :=
  (innerSL ℂ W.toLp).comp
    (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).toContinuousLinearEquiv.toContinuousLinearMap

/-- `pairingCLM s W U = [W, U]`. -/
@[simp]
theorem pairingCLM_apply (W : H^{-s}(V)) (U : H^{s}(V)) : pairingCLM s W U = pairing s W U := by
  simp only [pairingCLM, pairing, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply,
    innerSL_apply_apply]

/-- **The pairing is bounded**: `|[W, U]| ≤ ‖W‖ ‖U‖` (Cauchy–Schwarz in `L_2`). -/
theorem norm_pairing_le (W : H^{-s}(V)) (U : H^{s}(V)) : ‖pairing s W U‖ ≤ ‖W‖ * ‖U‖ := by
  rw [← BesselPotentialSpace.norm_toLp_eq W, ← BesselPotentialSpace.norm_toLp_eq U]
  exact norm_inner_le_norm _ _

/-- **The pairing through `besselShift`**: `[J_{2s} U', U] = ⟪U', U⟫_{H^s}`. -/
theorem pairing_besselShift (U' U : H^{s}(V)) : pairing s (besselShift s U') U = ⟪U', U⟫_ℂ := by
  rw [pairing, toLp_besselShift, inner_toLp_toLp]

/-- **The pairing extends the distribution in the first slot**: for a test function `φ` of `Ω`
and `U ∈ H^s(V)`, `[φ, U] = U(φ)`, since `[φ, U] = (J_{-s}(J_s U))(φ)`
(`Rd.inner_ofTest_toLp`). -/
theorem pairing_ofTest_left (φ : 𝓓(Ω, ℝ)) (U : H^{s}(V)) :
    pairing s (ofTest (-s) φ) U = U.toDistr (testSchwartz φ) := by
  rw [pairing, inner_ofTest_toLp, U.besselPotential_neg_toLp_eq]

/-- **The pairing extends the distribution in the second slot**: for `W ∈ H^{-s}(V)` and a test
function `φ` of `Ω`, `[W, φ] = conj (W(φ))`. -/
theorem pairing_ofTest_right (W : H^{-s}(V)) (φ : 𝓓(Ω, ℝ)) :
    pairing s W (ofTest s φ) = conj (W.toDistr (testSchwartz φ)) := by
  have hW := W.besselPotential_neg_toLp_eq
  rw [neg_neg] at hW
  rw [pairing, ← inner_conj_symm, inner_ofTest_toLp, hW]

/-- **The pairing at `s = 1` is the `L_2` inner product**: for a Schwartz function `ψ` as an
element of `H^{-1}(V)` and `U ∈ H^1(V)`, `[ψ, U] = ⟪ψ, U⟫_{L_2}`. By Plancherel both sides are
integrals of Fourier transforms, `∫ conj (⟨ξ⟩⁻¹ 𝓕ψ) 𝓕(J_1 U)` and `∫ conj (𝓕ψ) ⟨ξ⟩⁻¹ 𝓕(J_1 U)`
(`Rd.fourier_toL2_ae_eq`), and the weight is real. -/
theorem pairing_one_toLp (ψ : 𝓢(V, ℂ)) (U : H^{1}(V)) :
    pairing 1 (ψ.memSobolev (s := -1) (p := 2)).toBesselPotentialSpace U =
      ⟪ψ.toLp 2, toL2 U⟫_ℂ := by
  rw [pairing, toLp_schwartz, ← Lp.inner_fourier_eq]
  conv_rhs => rw [← Lp.inner_fourier_eq]
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(𝓕 (besselSchwartz (-1) ψ)).coeFn_toLp 2 volume, (𝓕 ψ).coeFn_toLp 2 volume,
    fourier_toL2_ae_eq U] with ξ h1 h2 h3
  rw [h1, h2, h3, RCLike.inner_apply', RCLike.inner_apply', besselSchwartz,
    SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_besselWeight (-1)), smul_eq_mul,
    map_mul, Complex.conj_ofReal]
  ring

/-! ### Orthogonal complements of `H̃^t(Ω)` -/

/-- **The orthogonal complement of `H̃^t(Ω)`**: `U ∈ H^t(V)` is orthogonal to `H̃^t(Ω)` iff the
distribution `J_t (J_t U)` vanishes on every test function of `Ω`. The orthogonal complement of a
closure is that of the set (Mathlib's `Submodule.orthogonal_closure`), orthogonality to a span is
orthogonality to its generators, and `⟪φ, U⟫ = (J_t (J_t U))(φ)` (`Rd.inner_ofTest_left`). -/
theorem mem_orthogonal_tildeSpace_iff_toLp {t : ℝ} (U : H^{t}(V)) :
    U ∈ (tildeSpace t Ω)ᗮ ↔
      ∀ φ : 𝓓(Ω, ℝ), besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ)) (testSchwartz φ) = 0 := by
  rw [tildeSpace, Submodule.orthogonal_closure, testSpan, Submodule.mem_orthogonal]
  constructor
  · intro h φ
    rw [← inner_ofTest_left]
    exact h _ (Submodule.subset_span ⟨φ, rfl⟩)
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      exact (inner_ofTest_left t φ U).trans (h φ)
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **The orthogonal complement of `H̃^t(Ω)` as a preimage**: for a linear isometry `e` of
`H^t(V)` onto `H^{t'}(V)` whose values are the distributions `J_t (J_t U)`, `H̃^t(Ω)^⊥` is the
preimage under `e` of the elements of `H^{t'}(V)` vanishing on `Ω`
(`Rd.mem_orthogonal_tildeSpace_iff_toLp`). The hypothesis determines `e`, and such an `e` exists
only for `t' = -t`; the lemma is stated with `t'` free so that it applies to both
`Rd.besselShift s` and its inverse. -/
theorem orthogonal_tildeSpace_eq_comap {t t' : ℝ} (e : H^{t}(V) ≃ₗᵢ[ℂ] H^{t'}(V))
    (he : ∀ U, (e U).toDistr = besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ))) :
    (tildeSpace t Ω)ᗮ = (vanishOn t' Ω).comap (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)) := by
  ext U
  rw [mem_orthogonal_tildeSpace_iff_toLp, Submodule.mem_comap, mem_vanishOn_iff]
  simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, he]

/-- **The image of `H̃^t(Ω)`**: for `e` as in `Rd.orthogonal_tildeSpace_eq_comap`, `e(H̃^t(Ω))`
is `H^{t'}(Ω)`, the orthogonal complement of the elements of `H^{t'}(V)` vanishing on `Ω`. Since
`H̃^t(Ω)` is closed it is its double orthogonal complement, and `e` maps orthogonal complements
to orthogonal complements (Mathlib's `Submodule.map_orthogonal_equiv`). As there, `t'` is free
only so that the lemma applies to both `Rd.besselShift s` and its inverse. -/
theorem map_tildeSpace_eq_orthogonal {t t' : ℝ} (e : H^{t}(V) ≃ₗᵢ[ℂ] H^{t'}(V))
    (he : ∀ U, (e U).toDistr = besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ))) :
    (tildeSpace t Ω).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)) = (vanishOn t' Ω)ᗮ := by
  calc (tildeSpace t Ω).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V))
      = ((tildeSpace t Ω)ᗮᗮ).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)) := by
        rw [Submodule.orthogonal_orthogonal]
    _ = (((tildeSpace t Ω)ᗮ).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)))ᗮ :=
        Submodule.map_orthogonal_equiv _ e
    _ = (vanishOn t' Ω)ᗮ := by
        rw [orthogonal_tildeSpace_eq_comap e he,
          Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective]

/-- **The orthogonal complement of `H̃^s(Ω)`**: `U ∈ H^s(V)` is orthogonal to `H̃^s(Ω)` iff
`J_{2s} U ∈ H^{-s}(V)` vanishes on `Ω`. -/
theorem mem_orthogonal_tildeSpace_iff (U : H^{s}(V)) :
    U ∈ (tildeSpace s Ω)ᗮ ↔ besselShift s U ∈ vanishOn (-s) Ω := by
  rw [orthogonal_tildeSpace_eq_comap (besselShift s) toDistr_besselShift_eq_besselPotential_toLp]
  rfl

/-- **`J_{2s}` maps `H̃^s(Ω)` onto `H^{-s}(Ω)`**: the image of `H̃^s(Ω)` under `besselShift s` is
the orthogonal complement of the elements of `H^{-s}(V)` vanishing on `Ω`. -/
theorem map_tildeSpace_besselShift :
    (tildeSpace s Ω).map ((besselShift (V := V) s).toLinearEquiv : H^{s}(V) →ₗ[ℂ] H^{-s}(V)) =
      (vanishOn (-s) Ω)ᗮ :=
  map_tildeSpace_eq_orthogonal (besselShift s) toDistr_besselShift_eq_besselPotential_toLp

/-- **`J_{-2s}` maps `H̃^{-s}(Ω)` onto `H^s(Ω)`**: the image of `H̃^{-s}(Ω)` under the inverse of
`besselShift s` is the orthogonal complement of the elements of `H^s(V)` vanishing on `Ω`. -/
theorem map_tildeSpace_besselShift_symm :
    (tildeSpace (-s) Ω).map
        ((besselShift (V := V) s).symm.toLinearEquiv : H^{-s}(V) →ₗ[ℂ] H^{s}(V)) =
      (vanishOn s Ω)ᗮ :=
  map_tildeSpace_eq_orthogonal (besselShift s).symm toDistr_besselShift_symm

/-- **Elements vanishing on `Ω` pair to zero with `H̃^s(Ω)`**: for `W ∈ H^{-s}(V)` vanishing on
`Ω` and `U ∈ H̃^s(Ω)`, `[W, U] = 0`. With `U' = (besselShift s)⁻¹ W`, `[W, U] = ⟪U', U⟫_{H^s}`,
and `U'` is orthogonal to `H̃^s(Ω)` (`Rd.mem_orthogonal_tildeSpace_iff`). -/
theorem pairing_eq_zero_of_mem_vanishOn_left {W : H^{-s}(V)} (hW : W ∈ vanishOn (-s) Ω)
    {U : H^{s}(V)} (hU : U ∈ tildeSpace s Ω) : pairing s W U = 0 := by
  have h : (besselShift s).symm W ∈ (tildeSpace s Ω)ᗮ := by
    rw [mem_orthogonal_tildeSpace_iff, LinearIsometryEquiv.apply_symm_apply]
    exact hW
  rw [pairing, ← toLp_besselShift_symm W, inner_toLp_toLp]
  exact Submodule.inner_left_of_mem_orthogonal hU h

/-- **`H̃^{-s}(Ω)` pairs to zero with the elements vanishing on `Ω`**: for `W ∈ H̃^{-s}(Ω)` and
`U ∈ H^s(V)` vanishing on `Ω`, `[W, U] = 0`, since `(besselShift s)⁻¹ W` lies in the orthogonal
complement of the elements vanishing on `Ω` (`Rd.map_tildeSpace_besselShift_symm`). -/
theorem pairing_eq_zero_of_mem_vanishOn_right {W : H^{-s}(V)} (hW : W ∈ tildeSpace (-s) Ω)
    {U : H^{s}(V)} (hU : U ∈ vanishOn s Ω) : pairing s W U = 0 := by
  have h : (besselShift s).symm W ∈ (vanishOn s Ω)ᗮ := by
    rw [← map_tildeSpace_besselShift_symm]
    exact Submodule.mem_map_of_mem hW
  rw [pairing, ← toLp_besselShift_symm W, inner_toLp_toLp]
  exact Submodule.inner_left_of_mem_orthogonal hU h

/-! ### `H̃^s(Ω) ≅ H^{-s}(Ω)` -/

variable (s Ω) in
/-- **`H̃^s(Ω) ≅ H^{-s}(Ω)` by `J_{2s}`**: for every open set `Ω` and every real `s`,
`besselShift s` restricts to an isometric isomorphism of `H̃^s(Ω)` onto `H^{-s}(Ω)`
(`Rd.map_tildeSpace_besselShift`, Mathlib's `LinearIsometryEquiv.submoduleMap`). -/
noncomputable def tildeEquivRestriction : tildeSpace s Ω ≃ₗᵢ[ℂ] RestrictionSpace (-s) Ω :=
  ((besselShift s).submoduleMap (tildeSpace s Ω)).trans
    (LinearIsometryEquiv.ofEq _ _ map_tildeSpace_besselShift)

/-- `tildeEquivRestriction s Ω U` is `besselShift s U`. -/
theorem coe_tildeEquivRestriction_apply (U : tildeSpace s Ω) :
    (tildeEquivRestriction s Ω U : H^{-s}(V)) = besselShift s U :=
  rfl

variable (s Ω) in
/-- **`H^s(Ω) ≅ H̃^{-s}(Ω)` by `J_{2s}`**: for every open set `Ω` and every real `s`,
`besselShift s` restricts to an isometric isomorphism of `H^s(Ω)` onto `H̃^{-s}(Ω)`, the inverse
of the restriction of `(besselShift s)⁻¹` to `H̃^{-s}(Ω)` (`Rd.map_tildeSpace_besselShift_symm`). -/
noncomputable def restrictionEquivTilde : RestrictionSpace s Ω ≃ₗᵢ[ℂ] tildeSpace (-s) Ω :=
  (((besselShift s).symm.submoduleMap (tildeSpace (-s) Ω)).trans
    (LinearIsometryEquiv.ofEq _ _ map_tildeSpace_besselShift_symm)).symm

/-- `restrictionEquivTilde s Ω u` is `besselShift s u`. -/
theorem coe_restrictionEquivTilde_apply (u : RestrictionSpace s Ω) :
    (restrictionEquivTilde s Ω u : H^{-s}(V)) = besselShift s u := by
  have h : ((restrictionEquivTilde s Ω).symm (restrictionEquivTilde s Ω u) : H^{s}(V)) =
      (besselShift s).symm (restrictionEquivTilde s Ω u) :=
    rfl
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  rw [h, LinearIsometryEquiv.apply_symm_apply]

/-! ### The dual of `H̃^s(Ω)` -/

variable (s Ω) in
/-- **The dual of `H̃^s(Ω)` is `H^{-s}(Ω)`**: for every open set `Ω` and every real `s`, every
bounded functional `ℓ` on `H̃^s(Ω)` is `U ↦ [W, U]` for exactly one `W ∈ H^{-s}(Ω)`
(`Rd.dualEquiv_apply`, `Rd.dualEquiv_eq_iff`), with `‖W‖ = ‖ℓ‖`, and every extension of `W` to
`V` gives the same pairing (`Rd.dualEquiv_apply_of_restrictProj_eq`); this is Theorem 3.3 of
Chandler-Wilde, Hewett and Moiola with the sesquilinear pairing. The map `ℓ ↦ W` is Riesz's
representation (Mathlib's `InnerProductSpace.toDual`) followed by `Rd.tildeEquivRestriction`,
conjugate-linear and isometric. -/
noncomputable def dualEquiv : StrongDual ℂ (tildeSpace s Ω) ≃ₗᵢ⋆[ℂ] RestrictionSpace (-s) Ω :=
  (InnerProductSpace.toDual ℂ (tildeSpace s Ω)).symm.trans (tildeEquivRestriction s Ω)

/-- **`ℓ` is the pairing with `dualEquiv s Ω ℓ`**: `ℓ(U) = [W, U]` for `W = dualEquiv s Ω ℓ` and
every `U ∈ H̃^s(Ω)` (Mathlib's `InnerProductSpace.toDual_symm_apply`,
`Rd.pairing_besselShift`). -/
theorem dualEquiv_apply (ℓ : StrongDual ℂ (tildeSpace s Ω)) (U : tildeSpace s Ω) :
    ℓ U = pairing s (dualEquiv s Ω ℓ : H^{-s}(V)) (U : H^{s}(V)) := by
  rw [← InnerProductSpace.toDual_symm_apply, Submodule.coe_inner, dualEquiv,
    LinearIsometryEquiv.trans_apply, coe_tildeEquivRestriction_apply, pairing_besselShift]

/-- The functional of `W ∈ H^{-s}(Ω)` is `U ↦ [W, U]`. -/
theorem dualEquiv_symm_apply (W : RestrictionSpace (-s) Ω) (U : tildeSpace s Ω) :
    (dualEquiv s Ω).symm W U = pairing s (W : H^{-s}(V)) (U : H^{s}(V)) := by
  rw [dualEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualEquiv s Ω ℓ = W` iff `ℓ(U) = [W, U]` for
every `U ∈ H̃^s(Ω)` (Mathlib's `LinearIsometryEquiv.eq_symm_apply`). -/
theorem dualEquiv_eq_iff (ℓ : StrongDual ℂ (tildeSpace s Ω)) (W : RestrictionSpace (-s) Ω) :
    dualEquiv s Ω ℓ = W ↔
      ∀ U : tildeSpace s Ω, ℓ U = pairing s (W : H^{-s}(V)) (U : H^{s}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualEquiv_symm_apply]

/-- `‖dualEquiv s Ω ℓ‖ = ‖ℓ‖`. -/
theorem norm_dualEquiv (ℓ : StrongDual ℂ (tildeSpace s Ω)) : ‖dualEquiv s Ω ℓ‖ = ‖ℓ‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- **Every extension represents `ℓ`**: if `W ∈ H^{-s}(V)` restricts to `dualEquiv s Ω ℓ`, then
`ℓ(U) = [W, U]` for every `U ∈ H̃^s(Ω)`. `W` and its restriction differ by an element vanishing
on `Ω` (`Rd.sub_restrictProj_mem`), which pairs to zero with `H̃^s(Ω)`
(`Rd.pairing_eq_zero_of_mem_vanishOn_left`). -/
theorem dualEquiv_apply_of_restrictProj_eq (ℓ : StrongDual ℂ (tildeSpace s Ω))
    (U : tildeSpace s Ω) {W : H^{-s}(V)} (hW : restrictProj (-s) Ω W = dualEquiv s Ω ℓ) :
    ℓ U = pairing s W (U : H^{s}(V)) := by
  have h := pairing_eq_zero_of_mem_vanishOn_left (sub_restrictProj_mem W) U.2
  rw [pairing_sub_left, sub_eq_zero, hW] at h
  rw [dualEquiv_apply, h]

/-! ### The duals of `H^s(Ω)` and `H^1_0(Ω)` -/

variable (s Ω) in
/-- **The dual of `H^s(Ω)` is `H̃^{-s}(Ω)`**: for every open set `Ω` and every real `s`, every
bounded functional `ℓ` on `H^s(Ω)` is `u ↦ [W, u]` for exactly one `W ∈ H̃^{-s}(Ω)`
(`Rd.dualRestrictionEquiv_apply`, `Rd.dualRestrictionEquiv_eq_iff`), with `‖W‖ = ‖ℓ‖`, and
`ℓ(U|_Ω) = [W, U]` for every `U ∈ H^s(V)` (`Rd.dualRestrictionEquiv_apply_restrictProj`):
Riesz's representation followed by `Rd.restrictionEquivTilde`, conjugate-linear and isometric. -/
noncomputable def dualRestrictionEquiv :
    StrongDual ℂ (RestrictionSpace s Ω) ≃ₗᵢ⋆[ℂ] tildeSpace (-s) Ω :=
  (InnerProductSpace.toDual ℂ (RestrictionSpace s Ω)).symm.trans (restrictionEquivTilde s Ω)

/-- **`ℓ` is the pairing with `dualRestrictionEquiv s Ω ℓ`**: `ℓ(u) = [W, u]` for
`W = dualRestrictionEquiv s Ω ℓ` and every `u ∈ H^s(Ω)`. -/
theorem dualRestrictionEquiv_apply (ℓ : StrongDual ℂ (RestrictionSpace s Ω))
    (u : RestrictionSpace s Ω) :
    ℓ u = pairing s (dualRestrictionEquiv s Ω ℓ : H^{-s}(V)) (u : H^{s}(V)) := by
  rw [← InnerProductSpace.toDual_symm_apply, Submodule.coe_inner, dualRestrictionEquiv,
    LinearIsometryEquiv.trans_apply, coe_restrictionEquivTilde_apply, pairing_besselShift]

/-- The functional of `W ∈ H̃^{-s}(Ω)` is `u ↦ [W, u]`. -/
theorem dualRestrictionEquiv_symm_apply (W : tildeSpace (-s) Ω) (u : RestrictionSpace s Ω) :
    (dualRestrictionEquiv s Ω).symm W u = pairing s (W : H^{-s}(V)) (u : H^{s}(V)) := by
  rw [dualRestrictionEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualRestrictionEquiv s Ω ℓ = W` iff
`ℓ(u) = [W, u]` for every `u ∈ H^s(Ω)`. -/
theorem dualRestrictionEquiv_eq_iff (ℓ : StrongDual ℂ (RestrictionSpace s Ω))
    (W : tildeSpace (-s) Ω) :
    dualRestrictionEquiv s Ω ℓ = W ↔
      ∀ u : RestrictionSpace s Ω, ℓ u = pairing s (W : H^{-s}(V)) (u : H^{s}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualRestrictionEquiv_symm_apply]

/-- **The pairing with every extension**: `ℓ(U|_Ω) = [W, U]` for `W = dualRestrictionEquiv s Ω ℓ`
and every `U ∈ H^s(V)`. `U` and its restriction differ by an element vanishing on `Ω`
(`Rd.sub_restrictProj_mem`), which pairs to zero with `H̃^{-s}(Ω)`
(`Rd.pairing_eq_zero_of_mem_vanishOn_right`). -/
theorem dualRestrictionEquiv_apply_restrictProj (ℓ : StrongDual ℂ (RestrictionSpace s Ω))
    (U : H^{s}(V)) :
    ℓ (restrictProj s Ω U) = pairing s (dualRestrictionEquiv s Ω ℓ : H^{-s}(V)) U := by
  have h := pairing_eq_zero_of_mem_vanishOn_right (dualRestrictionEquiv s Ω ℓ).2
    (sub_restrictProj_mem (Ω := Ω) U)
  rw [pairing_sub_right, sub_eq_zero] at h
  rw [dualRestrictionEquiv_apply, h]

variable (Ω) in
/-- **The dual of `H^1_0(Ω)` is `H^{-1}(Ω)`**: for every open set `Ω`, every bounded functional `ℓ`
on `H^1_0(Ω)` is `u ↦ [W, u]` for exactly one `W ∈ H^{-1}(Ω)` (`Rd.dualZeroBoundaryEquiv_apply`,
`Rd.dualZeroBoundaryEquiv_eq_iff`), with `‖W‖ = ‖ℓ‖`. Inside `H^1(V)`, `H^1_0(Ω)` is `H̃^1(Ω)`
(`Rd.coe_tildeEquivZeroBoundary_symm_apply`), so `W` is paired with `u` itself. -/
noncomputable def dualZeroBoundaryEquiv :
    StrongDual ℂ (zeroBoundarySpace 1 Ω) ≃ₗᵢ⋆[ℂ] RestrictionSpace (-1) Ω :=
  (InnerProductSpace.toDual ℂ (zeroBoundarySpace 1 Ω)).symm.trans
    ((tildeEquivZeroBoundary Ω).symm.trans (tildeEquivRestriction 1 Ω))

/-- **`ℓ` is the pairing with `dualZeroBoundaryEquiv Ω ℓ`**: `ℓ(u) = [W, u]` for
`W = dualZeroBoundaryEquiv Ω ℓ` and every `u ∈ H^1_0(Ω)`, read as an element of `H^1(V)`. The
isometry `Rd.tildeEquivZeroBoundary` preserves inner products, and its inverse is the identity
inside `H^1(V)` (`Rd.coe_tildeEquivZeroBoundary_symm_apply`). -/
theorem dualZeroBoundaryEquiv_apply (ℓ : StrongDual ℂ (zeroBoundarySpace 1 Ω))
    (u : zeroBoundarySpace 1 Ω) :
    ℓ u = pairing 1 (dualZeroBoundaryEquiv Ω ℓ : H^{-1}(V))
      ((u : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := zeroBoundarySpace 1 Ω) (x := u)
    (y := ℓ)
  rw [← h, ← LinearIsometryEquiv.inner_map_map (tildeEquivZeroBoundary Ω).symm,
    Submodule.coe_inner, dualZeroBoundaryEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, coe_tildeEquivRestriction_apply, pairing_besselShift,
    coe_tildeEquivZeroBoundary_symm_apply u]

/-- The functional of `W ∈ H^{-1}(Ω)` on `H^1_0(Ω)` is `u ↦ [W, u]`. -/
theorem dualZeroBoundaryEquiv_symm_apply (W : RestrictionSpace (-1) Ω)
    (u : zeroBoundarySpace 1 Ω) :
    (dualZeroBoundaryEquiv Ω).symm W u =
      pairing 1 (W : H^{-1}(V)) ((u : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  rw [dualZeroBoundaryEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualZeroBoundaryEquiv Ω ℓ = W` iff
`ℓ(u) = [W, u]` for every `u ∈ H^1_0(Ω)`. -/
theorem dualZeroBoundaryEquiv_eq_iff (ℓ : StrongDual ℂ (zeroBoundarySpace 1 Ω))
    (W : RestrictionSpace (-1) Ω) :
    dualZeroBoundaryEquiv Ω ℓ = W ↔ ∀ u : zeroBoundarySpace 1 Ω,
      ℓ u = pairing 1 (W : H^{-1}(V)) ((u : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualZeroBoundaryEquiv_symm_apply]

/-! ### Gelfand triples on `ℝ^d` -/

/-- **The `L_2` functions in `H^{-s}(V)`**, `s ≥ 0`: for `g ∈ L_2(V)`, the element
`ι_{-s,0} g ∈ H^{-s}(V)` of `g ∈ H^0(V)` (Mathlib's `BesselPotentialSpace.ofLp`) has the
distribution `g` (`Rd.toDistr_sobolevInclusion`, `TemperedDistribution.besselPotential_zero`). -/
theorem toDistr_sobolevInclusion_ofLp (hs : 0 ≤ s) (g : Lp ℂ 2 (volume : Measure V)) :
    (sobolevInclusion (neg_nonpos.2 hs) (BesselPotentialSpace.ofLp 0 g) : H^{-s}(V)).toDistr =
      (g : 𝓢'(V, ℂ)) := by
  rw [toDistr_sobolevInclusion, BesselPotentialSpace.toDistr_ofLp, neg_zero,
    TemperedDistribution.besselPotential_zero, ContinuousLinearMap.id_apply]

/-- **`H^s(V)` is dense in `L_2(V)`**, `s ≥ 0`: the range of `ι_s` contains the Schwartz functions
(`Rd.sobolevToL2_ofSchwartz`), which are dense in `L_2(V)` (Mathlib's
`SchwartzMap.denseRange_toLpCLM`). -/
theorem denseRange_sobolevToL2 (hs : 0 ≤ s) : DenseRange (sobolevToL2 (V := V) hs) :=
  (SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := (volume : Measure V)) two_ne_top).mono (by
    rintro _ ⟨w, rfl⟩
    exact ⟨ofSchwartz s w, sobolevToL2_ofSchwartz hs w⟩)

/-- **The Gelfand triple `H^s(V) ⊂ L_2(V) ⊂ H^{-s}(V)` is the Bessel duality**, `s ≥ 0`: the pivot
dual of `ι_s : H^s(V) → L_2(V)` (`ContinuousLinearMap.pivotDual`) sends `g ∈ L_2(V)` to the
pairing with the element `W ∈ H^{-s}(V)` whose distribution is `g`:
`⟪g, ι_s U⟫_{L_2} = [W, U]` for every `U ∈ H^s(V)` (`Rd.pairing`). Such `W` exists
(`Rd.toDistr_sobolevInclusion_ofLp`). By Plancherel both sides are
`∫ conj (𝓕 g) ⟨ξ⟩^{-s} 𝓕(J_s U) dξ` (Mathlib's `MeasureTheory.Lp.inner_fourier_eq`,
`Rd.fourier_toLp_sobolevInclusion_ae`). Since `ι_s` has dense range (`Rd.denseRange_sobolevToL2`),
the pivot dual is injective (`ContinuousLinearMap.pivotDual_injective_iff`), and `L_2(V)` is the
pivot space of the triple. -/
theorem pivotDual_sobolevToL2_apply_apply (hs : 0 ≤ s) (g : Lp ℂ 2 (volume : Measure V))
    {W : H^{-s}(V)} (hW : W.toDistr = (g : 𝓢'(V, ℂ))) (U : H^{s}(V)) :
    (sobolevToL2 hs).pivotDual g U = pairing s W U := by
  have hW' : W = sobolevInclusion (neg_nonpos.2 hs) (BesselPotentialSpace.ofLp 0 g) :=
    BesselPotentialSpace.ext (by rw [hW, toDistr_sobolevInclusion_ofLp hs])
  rw [ContinuousLinearMap.pivotDual_apply_apply, hW', pairing, sobolevToL2_apply hs]
  conv_lhs => rw [← Lp.inner_fourier_eq]
  conv_rhs => rw [← Lp.inner_fourier_eq]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fourier_toLp_sobolevInclusion_ae (neg_nonpos.2 hs)
      (BesselPotentialSpace.ofLp 0 g), fourier_toLp_sobolevInclusion_ae hs U] with ξ h1 h2
  rw [h1, h2, BesselPotentialSpace.toLp_ofLp, RCLike.inner_apply', RCLike.inner_apply', map_mul,
    Complex.conj_ofReal, sub_zero, zero_sub]
  ring

/-! ### Gelfand triples on open sets -/

variable (Ω) in
/-- **The embedding `H̃^s(Ω) → L_2(Ω)`**, `s ≥ 0`: `U ↦ (ι_s U)|_Ω`, the `L_2` function of
`U ∈ H̃^s(Ω) ⊆ H^s(V)` (`Rd.sobolevToL2`) restricted to `Ω` (Mathlib's `LpToLpRestrictCLM`). It
is injective, since the elements of `H̃^s(Ω)` vanish outside `Ω`, and it has dense range
(`Rd.tildeToL2_injective`, `Rd.denseRange_tildeToL2`), so its pivot dual
`L_2(Ω) → (H̃^s(Ω))^*` (`ContinuousLinearMap.pivotDual`) is injective
(`ContinuousLinearMap.pivotDual_injective_iff`): `H̃^s(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)` is a Gelfand
triple (`Rd.pairing_dualEquiv_pivotDual_tildeToL2`). -/
noncomputable def tildeToL2 (hs : 0 ≤ s) :
    tildeSpace s Ω →L[ℂ] Lp ℂ 2 (volume.restrict (Ω : Set V)) :=
  LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) ∘L sobolevToL2 hs ∘L (tildeSpace s Ω).subtypeL

/-- `tildeToL2 Ω hs U` is `ι_s U` almost everywhere on `Ω`. -/
theorem tildeToL2_apply_ae (hs : 0 ≤ s) (U : tildeSpace s Ω) :
    (tildeToL2 Ω hs U : V → ℂ) =ᵐ[volume.restrict (Ω : Set V)] sobolevToL2 hs (U : H^{s}(V)) :=
  LpToLpRestrictCLM_coeFn ℂ _ _

/-- **`H̃^s(Ω) → L_2(Ω)` is injective**, `s ≥ 0`: if `ι_s U = 0` on `Ω`, then `ι_s U = 0` on `V`,
since `ι_s U` vanishes outside `Ω` (`Rd.sobolevToL2_ae_eq_zero_of_mem_tildeSpace`), and `ι_s` is
injective (`Rd.sobolevToL2_injective`). -/
theorem tildeToL2_injective (hs : 0 ≤ s) : Function.Injective (tildeToL2 Ω hs) := by
  refine (injective_iff_map_eq_zero _).2 fun U hU => ?_
  have h1 := tildeToL2_apply_ae hs U
  rw [hU] at h1
  replace h1 := h1.symm.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict (Ω : Set V)))
  rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet] at h1
  have h0 : sobolevToL2 hs (U : H^{s}(V)) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [h1, sobolevToL2_ae_eq_zero_of_mem_tildeSpace hs U.2] with x hx hx'
    by_cases hxΩ : x ∈ (Ω : Set V)
    · exact hx hxΩ
    · exact hx' hxΩ
  exact Subtype.ext (sobolevToL2_injective hs (h0.trans (map_zero _).symm))

open scoped ContDiff in
/-- **`H̃^s(Ω)` is dense in `L_2(Ω)`**, `s ≥ 0`: a smooth real function `ψ` with compact support in
`Ω` is a test function `φ` of `Ω`, `ofTest s φ ∈ H̃^s(Ω)` has `ι_s φ = φ`
(`Rd.ofTest_eq_ofSchwartz`, `Rd.sobolevToL2_ofSchwartz`), and these functions are dense in
`L_2(Ω)` (`MeasureTheory.L2.denseRange_of_forall_contDiff`). -/
theorem denseRange_tildeToL2 (hs : 0 ≤ s) : DenseRange (tildeToL2 Ω hs) := by
  refine L2.denseRange_of_forall_contDiff _ Ω.isOpen (ae_restrict_mem Ω.isOpen.measurableSet)
    fun ψ hψ hc hsupp => ?_
  let φ : 𝓓(Ω, ℝ) := ⟨ψ, hψ.of_le (mod_cast le_top), hc, hsupp⟩
  have hφ : sobolevToL2 hs (ofTest s φ) = (testSchwartz φ).toLp 2 := by
    rw [ofTest_eq_ofSchwartz, sobolevToL2_ofSchwartz]
  let U : tildeSpace s Ω :=
    ⟨ofTest s φ, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, rfl⟩)⟩
  refine ⟨U, ?_⟩
  filter_upwards [tildeToL2_apply_ae hs U,
    ae_restrict_of_ae ((testSchwartz φ).coeFn_toLp 2 volume)] with x h1 h2
  rw [h1, hφ, h2, testSchwartz_apply]
  rfl

/-- **The pivot dual of `H̃^s(Ω) → L_2(Ω)`**, `s ≥ 0`: it sends `g ∈ L_2(Ω)` to the functional
`U ↦ ∫_Ω conj (g) ι_s U` on `H̃^s(Ω)` (`MeasureTheory.L2.pivotDual_apply_apply_eq_integral`,
`Rd.tildeToL2_apply_ae`). -/
theorem pivotDual_tildeToL2_apply_apply (hs : 0 ≤ s) (g : Lp ℂ 2 (volume.restrict (Ω : Set V)))
    (U : tildeSpace s Ω) :
    (tildeToL2 Ω hs).pivotDual g U =
      ∫ x in (Ω : Set V), conj (g x) * sobolevToL2 hs (U : H^{s}(V)) x := by
  rw [L2.pivotDual_apply_apply_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [tildeToL2_apply_ae hs U] with x hx
  rw [hx]

/-- **The Gelfand triple `H̃^s(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)`**, `s ≥ 0`: for `g ∈ L_2(Ω)`, the element
`W_g = dualEquiv s Ω (J g)` of `H^{-s}(Ω)` that represents the pivot dual `J g`
(`Rd.dualEquiv`) has `[W_g, U] = ∫_Ω conj (g) ι_s U` for every `U ∈ H̃^s(Ω)`
(`Rd.dualEquiv_apply`, `Rd.pivotDual_tildeToL2_apply_apply`): the pairing of `H^{-s}(Ω)` with
`H̃^s(Ω)` extends the inner product of `L_2(Ω)`. The map `g ↦ W_g` is injective, since `J` is
(`Rd.denseRange_tildeToL2`, `ContinuousLinearMap.pivotDual_injective_iff`) and `Rd.dualEquiv` is
an isometric isomorphism, so `L_2(Ω)` is the pivot space of the triple. For `s = 1`, restriction
maps `H̃^1(Ω)` isometrically onto `H^1_0(Ω)` (`Rd.tildeEquivZeroBoundary`), and the triple is
`H^1_0(Ω) ⊂ L_2(Ω) ⊂ H^{-1}(Ω)`. On a bounded Lipschitz domain, for `s ≥ 0` with
`s - 1/2 ∉ ℕ_0`, restriction is an isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)` with equivalent norms
(`Rd.BoundedLipschitzDomain.tildeEquivZeroBoundaryOfNeHalf`; McLean, Theorem 3.33), and up to
equivalent norms the triple is `H^s_0(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)`. -/
theorem pairing_dualEquiv_pivotDual_tildeToL2 (hs : 0 ≤ s)
    (g : Lp ℂ 2 (volume.restrict (Ω : Set V))) (U : tildeSpace s Ω) :
    pairing s (dualEquiv s Ω ((tildeToL2 Ω hs).pivotDual g) : H^{-s}(V)) (U : H^{s}(V)) =
      ∫ x in (Ω : Set V), conj (g x) * sobolevToL2 hs (U : H^{s}(V)) x := by
  rw [← dualEquiv_apply, pivotDual_tildeToL2_apply_apply]

end Rd
