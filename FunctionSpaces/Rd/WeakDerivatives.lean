/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.LittlewoodPaleyKernels
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Weak derivatives and Sobolev spaces on open sets

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
and `Ω ⊆ V` open. For directions `v = (v_0, …, v_{k-1})` in `V`,
`∂^v = ∂_{v_0} ⋯ ∂_{v_{k-1}}` is the iterated directional derivative (Mathlib's
`LineDeriv.iteratedLineDerivOp`, notation `∂^{v}`). A locally integrable function `f` on `Ω` is
the distribution `φ ↦ ∫ φ f` on `Ω` (Mathlib's `Distribution.ofFun`, test functions
`𝓓(Ω, ℝ)`), and Mathlib differentiates distributions by `∂_w T (φ) = T(-∂_w φ)`.

* **Weak derivatives** (`Rd.HasWeakLineDeriv Ω v f g`): `∂^v f = g` as distributions on `Ω`,
  that is, `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every test function `φ`
  (`Rd.hasWeakLineDeriv_iff_integral`). They are unique almost everywhere on `Ω`, linear, local
  (`Rd.HasWeakLineDeriv.mono`), classical on Schwartz functions
  (`Rd.hasWeakLineDeriv_schwartz`), and pass to limits in `L_p(Ω)`
  (`Rd.HasWeakLineDeriv.of_tendsto`).
* **Sobolev spaces**: `Rd.MemWeakSobolev Ω m p f` says that `f` and all its weak derivatives of
  order at most `m` lie in `L_p(Ω)`; `Rd.MemSobolev m f` is the case `Ω = V` for `f ∈ L_p(V)`.
* **The bridge to tempered distributions** (`Rd.hasWeakLineDeriv_top_iff`): for `f ∈ L_p(V)`,
  `g ∈ L_r(V)`, the weak derivative on `V` is the derivative of tempered distributions,
  `∂^v f = g` in `𝓢'(V, ℂ)`. The proof cuts Schwartz functions off to compact support
  (`Rd.tendsto_cutoffMul`), so that a tempered distribution vanishing on test functions is zero
  (`Rd.eq_zero_of_testSchwartz`).

Two facts about derivatives enter: directional derivatives of Schwartz functions commute
(`SchwartzMap.lineDerivOp_comm`, Mathlib's symmetry of second derivatives), and so do those of
test functions (`TestFunction.lineDerivOp_comm`); hence `∂^v T (φ) = (-1)^k T(∂^v φ)` for
distributions (`Distribution.iteratedLineDerivOp_apply_apply`) and tempered distributions
(`TemperedDistribution.iteratedLineDerivOp_apply_apply`). These facts hold on every real normed
space `V`.
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal SchwartzMap LineDeriv Distributions

/-! ### Commuting directional derivatives -/

namespace LineDeriv

variable {V E : Type*} [LineDeriv V E E]

/-- If directional derivatives commute pairwise, `∂_a ∂_b x = ∂_b ∂_a x`, then a directional
derivative commutes with every iterated one: `∂_a ∂^v x = ∂^v ∂_a x`. -/
theorem lineDerivOp_iteratedLineDerivOp_comm_of
    (h : ∀ (a b : V) (x : E), ∂_{a} (∂_{b} x) = ∂_{b} (∂_{a} x)) {k : ℕ} (a : V)
    (v : Fin k → V) (x : E) : ∂_{a} (∂^{v} x) = ∂^{v} (∂_{a} x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, h, ih]

end LineDeriv

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Directional derivatives of a Schwartz function commute: `∂_a ∂_b u = ∂_b ∂_a u`. This is the
symmetry of the second derivative of a `C^2` function (Mathlib's
`ContDiffAt.isSymmSndFDerivAt`), read through `∂^{(a, b)} u(x) = D^2 u(x)(a, b)`
(`SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`). -/
theorem lineDerivOp_comm (u : 𝓢(E, F)) (a b : E) : ∂_{a} (∂_{b} u) = ∂_{b} (∂_{a} u) := by
  ext x
  have h1 : ∂_{a} (∂_{b} u) x = ∂^{![a, b]} u x := rfl
  have h2 : ∂_{b} (∂_{a} u) x = ∂^{![b, a]} u x := rfl
  rw [h1, h2, iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_eq_iteratedFDeriv]
  exact IsSymmSndFDerivAt.iteratedFDeriv_cons
    (hf := ((u.smooth ⊤).contDiffAt).isSymmSndFDerivAt (by simp))

/-- A directional derivative commutes with every iterated directional derivative of a Schwartz
function: `∂_a ∂^v u = ∂^v ∂_a u`. -/
theorem lineDerivOp_iteratedLineDerivOp_comm {k : ℕ} (u : 𝓢(E, F)) (a : E) (v : Fin k → E) :
    ∂_{a} (∂^{v} u) = ∂^{v} (∂_{a} u) :=
  LineDeriv.lineDerivOp_iteratedLineDerivOp_comm_of (fun a b x => lineDerivOp_comm x a b) a v u

end SchwartzMap

/-! ### Test functions as Schwartz functions -/

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A real test function `φ` on an open set `Ω` as a complex Schwartz function on `V`,
`x ↦ (φ x : ℂ)`: it is smooth with compact support (Mathlib's
`HasCompactSupport.toSchwartzMap`). -/
noncomputable def testSchwartz {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) : 𝓢(V, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => ((φ x : ℝ) : ℂ))
    (φ.hasCompactSupport.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp φ.contDiff)

/-- The values of `Rd.testSchwartz φ` are those of `φ`. -/
@[simp]
theorem testSchwartz_apply {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (x : V) :
    testSchwartz φ x = ((φ x : ℝ) : ℂ) :=
  rfl

/-- The directional derivative of a test function is the derivative of the function:
`∂_a φ(x) = Dφ(x) a`. -/
theorem lineDerivOp_testFunction_apply {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (a x : V) :
    (∂_{a} φ) x = fderiv ℝ φ x a := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ le_top]

/-- Passing to complex values commutes with directional derivatives:
`∂_a (φ : ℂ) = (∂_a φ : ℂ)`. -/
theorem lineDerivOp_testSchwartz {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (a : V) :
    ∂_{a} (testSchwartz φ) = testSchwartz (∂_{a} φ) := by
  ext x
  have hd : HasFDerivAt (fun y => ((φ y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x
      ((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, testSchwartz_apply,
    lineDerivOp_testFunction_apply]
  exact congrArg (fun L : V →L[ℝ] ℂ => L a) hd.fderiv

/-- Passing to complex values commutes with iterated directional derivatives:
`∂^v (φ : ℂ) = (∂^v φ : ℂ)`. -/
theorem iteratedLineDerivOp_testSchwartz {Ω : Opens V} {k : ℕ} (φ : 𝓓(Ω, ℝ)) (v : Fin k → V) :
    ∂^{v} (testSchwartz φ) = testSchwartz (∂^{v} φ) := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_testSchwartz]

/-- Two test functions (possibly on different open sets) with the same values have iterated
directional derivatives with the same values. -/
theorem coe_iteratedLineDerivOp_eq {Ω Ω' : Opens V} {k : ℕ} {φ : 𝓓(Ω, ℝ)} {ψ : 𝓓(Ω', ℝ)}
    (h : (φ : V → ℝ) = ψ) (v : Fin k → V) : ((∂^{v} φ : 𝓓(Ω, ℝ)) : V → ℝ) = ∂^{v} ψ := by
  have hs : testSchwartz φ = testSchwartz ψ := by
    ext x
    simp [h]
  have h' := congrArg (fun u : 𝓢(V, ℂ) => (u : V → ℂ)) (congrArg (∂^{v} ·) hs)
  simp only [iteratedLineDerivOp_testSchwartz] at h'
  funext x
  have hx := congrFun h' x
  simp only [testSchwartz_apply, Complex.ofReal_inj] at hx
  exact hx

/-- A smooth compactly supported complex function `w` (given as a Schwartz function) is
`Re w + i Im w` with real test functions `Re w`, `Im w` on `V`. -/
theorem exists_testSchwartz_eq (w : 𝓢(V, ℂ)) (hw : HasCompactSupport w) :
    ∃ a b : 𝓓((⊤ : Opens V), ℝ), w = testSchwartz a + Complex.I • testSchwartz b := by
  refine ⟨⟨fun x => (w x).re, Complex.reCLM.contDiff.comp (w.smooth ⊤),
    hw.comp_left Complex.zero_re, by simp⟩, ⟨fun x => (w x).im,
    Complex.imCLM.contDiff.comp (w.smooth ⊤), hw.comp_left Complex.zero_im, by simp⟩, ?_⟩
  ext x
  apply Complex.ext <;> simp <;> rfl

end Rd

namespace TestFunction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens V}

/-- Directional derivatives of a test function commute: `∂_a ∂_b φ = ∂_b ∂_a φ`, read off the
complex Schwartz function `Rd.testSchwartz φ` (`SchwartzMap.lineDerivOp_comm`). -/
theorem lineDerivOp_comm (φ : 𝓓(Ω, ℝ)) (a b : V) : ∂_{a} (∂_{b} φ) = ∂_{b} (∂_{a} φ) := by
  have h := SchwartzMap.lineDerivOp_comm (Rd.testSchwartz φ) a b
  simp only [Rd.lineDerivOp_testSchwartz] at h
  ext x
  have hx := congrArg (fun u : 𝓢(V, ℂ) => u x) h
  simp only [Rd.testSchwartz_apply, Complex.ofReal_inj] at hx
  exact hx

/-- A directional derivative commutes with every iterated directional derivative of a test
function: `∂_a ∂^v φ = ∂^v ∂_a φ`. -/
theorem lineDerivOp_iteratedLineDerivOp_comm {k : ℕ} (φ : 𝓓(Ω, ℝ)) (a : V) (v : Fin k → V) :
    ∂_{a} (∂^{v} φ) = ∂^{v} (∂_{a} φ) :=
  LineDeriv.lineDerivOp_iteratedLineDerivOp_comm_of (fun a b x => lineDerivOp_comm x a b) a v φ

end TestFunction

/-! ### Iterated derivatives of distributions -/

namespace Distribution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens V}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The **transpose formula** for iterated derivatives of a distribution on `Ω`: for directions
`v = (v_0, …, v_{k-1})`, `∂^v T (φ) = (-1)^k T(∂^v φ)` for every test function `φ`. Mathlib
defines `∂_w T (φ) = T(-∂_w φ)` (`Distribution.lineDerivOp_apply_apply`); the order of the
derivatives on `φ` is irrelevant because they commute
(`TestFunction.lineDerivOp_iteratedLineDerivOp_comm`). -/
theorem iteratedLineDerivOp_apply_apply {k : ℕ} (T : 𝓓'(Ω, F)) (φ : 𝓓(Ω, ℝ)) (v : Fin k → V) :
    ∂^{v} T φ = ((-1 : ℝ) ^ k) • T (∂^{v} φ) := by
  induction k generalizing T φ with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left v T, lineDerivOp_apply_apply, ih,
      LineDeriv.iteratedLineDerivOp_succ_left v φ, LineDeriv.iteratedLineDerivOp_neg,
      ← TestFunction.lineDerivOp_iteratedLineDerivOp_comm, map_neg, smul_neg, pow_succ,
      mul_neg_one, neg_smul]

end Distribution

/-! ### Iterated derivatives of tempered distributions -/

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The **transpose formula** for iterated derivatives of a tempered distribution: for directions
`v = (v_0, …, v_{k-1})`, `∂^v T (u) = T((-1)^k ∂^v u)` for every Schwartz function `u`. Mathlib
defines `∂_w T (u) = T(-∂_w u)` (`TemperedDistribution.lineDerivOp_apply_apply`); the order of
the derivatives on `u` is irrelevant because they commute
(`SchwartzMap.lineDerivOp_iteratedLineDerivOp_comm`). -/
theorem iteratedLineDerivOp_apply_apply {k : ℕ} (T : 𝓢'(E, F)) (u : 𝓢(E, ℂ)) (v : Fin k → E) :
    ∂^{v} T u = T (((-1 : ℂ) ^ k) • ∂^{v} u) := by
  induction k generalizing T u with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left v T, lineDerivOp_apply_apply, ih,
      LineDeriv.iteratedLineDerivOp_succ_left v u, LineDeriv.iteratedLineDerivOp_neg,
      ← SchwartzMap.lineDerivOp_iteratedLineDerivOp_comm, pow_succ, mul_neg_one, smul_neg,
      neg_smul]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The distributional derivative `∂^v S_u` of the tempered distribution `S_u` of a Schwartz
function `u` is the tempered distribution `S_{∂^v u}` of its classical derivative `∂^v u` (the
iterated form of Mathlib's `TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq`). -/
theorem iteratedLineDerivOp_toTemperedDistributionCLM_eq {k : ℕ} (u : 𝓢(E, F)) (v : Fin k → E) :
    ∂^{v} (SchwartzMap.toTemperedDistributionCLM E F μ u) =
      SchwartzMap.toTemperedDistributionCLM E F μ (∂^{v} u) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_toTemperedDistributionCLM_eq]

end TemperedDistribution

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Weak derivatives on open sets -/

/-- `g` is the **weak derivative** `∂^v f` of `f` on the open set `Ω` along the directions
`v = (v_0, …, v_{k-1})`: both are locally integrable on `Ω` and `∂^v f = g` as distributions on
`Ω`, that is, `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every smooth compactly supported `φ` in `Ω`
(`Rd.hasWeakLineDeriv_iff_integral`). -/
structure HasWeakLineDeriv (Ω : Opens V) {k : ℕ} (v : Fin k → V) (f g : V → ℂ) : Prop where
  /-- `f` is locally integrable on `Ω`. -/
  locallyIntegrableOn : LocallyIntegrableOn f Ω volume
  /-- `g` is locally integrable on `Ω`. -/
  locallyIntegrableOn_deriv : LocallyIntegrableOn g Ω volume
  /-- `∂^v f = g` as distributions on `Ω`. -/
  eq : ∂^{v} (Distribution.ofFun Ω f volume ⊤) = Distribution.ofFun Ω g volume ⊤

/-- The **Sobolev space** `W^m_p(Ω)` as a predicate: `f ∈ L_p(Ω)`, and for every order `k ≤ m`
and all directions `v = (v_0, …, v_{k-1})` the weak derivative `∂^v f` exists on `Ω` and lies in
`L_p(Ω)`. -/
def MemWeakSobolev (Ω : Opens V) (m : ℕ) (p : ℝ≥0∞) (f : V → ℂ) : Prop :=
  MemLp f p (volume.restrict Ω) ∧ ∀ k ≤ m, ∀ v : Fin k → V,
    ∃ g : V → ℂ, MemLp g p (volume.restrict Ω) ∧ HasWeakLineDeriv Ω v f g

/-- The **Sobolev space** `W^m_p(V)` as a predicate on `f ∈ L_p(V)`: the case `Ω = V` of
`Rd.MemWeakSobolev`. -/
def MemSobolev {p : ℝ≥0∞} (m : ℕ) (f : Lp ℂ p (volume : Measure V)) : Prop :=
  MemWeakSobolev ⊤ m p f

/-- Lebesgue measure restricted to the whole space `Ω = V` is Lebesgue measure, so that
`L_p(Ω) = L_p(V)` for `Ω = V`; a rewrite form of Mathlib's simp lemmas `Opens.coe_top` and
`Measure.restrict_univ`. -/
theorem volume_restrict_top : (volume : Measure V).restrict ((⊤ : Opens V) : Set V) = volume := by
  simp

/-- A function in `L_p(Ω)`, `1 ≤ p`, is locally integrable on `Ω`. -/
theorem locallyIntegrableOn_of_memLp {Ω : Opens V} {p : ℝ≥0∞} (hp : 1 ≤ p) {f : V → ℂ}
    (hf : MemLp f p (volume.restrict Ω)) : LocallyIntegrableOn f Ω volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)

variable {Ω Ω' : Opens V} {k : ℕ} {v : Fin k → V} {f f' g g' : V → ℂ}

/-- The integral form of a weak derivative: if `g = ∂^v f` weakly on `Ω`, then
`∫ φ g = (-1)^k ∫ (∂^v φ) f` for every test function `φ` on `Ω`. -/
theorem HasWeakLineDeriv.integral_eq (h : HasWeakLineDeriv Ω v f g) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, φ x • g x = (-1 : ℝ) ^ k • ∫ x, (∂^{v} φ) x • f x := by
  have h' := DFunLike.congr_fun h.eq φ
  rw [Distribution.iteratedLineDerivOp_apply_apply, Distribution.ofFun_apply h.1,
    Distribution.ofFun_apply h.2] at h'
  exact h'.symm

/-- **Weak derivatives by integration by parts**: for locally integrable `f`, `g` on `Ω`, `g` is
the weak derivative `∂^v f` on `Ω` iff `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every test function `φ`
on `Ω`. -/
theorem hasWeakLineDeriv_iff_integral (hf : LocallyIntegrableOn f Ω volume)
    (hg : LocallyIntegrableOn g Ω volume) :
    HasWeakLineDeriv Ω v f g ↔
      ∀ φ : 𝓓(Ω, ℝ), ∫ x, φ x • g x = (-1 : ℝ) ^ k • ∫ x, (∂^{v} φ) x • f x := by
  refine ⟨fun h => h.integral_eq, fun h => ⟨hf, hg, ?_⟩⟩
  ext φ
  rw [Distribution.iteratedLineDerivOp_apply_apply, Distribution.ofFun_apply hf,
    Distribution.ofFun_apply hg, h φ]

/-- The weak derivative is **unique** almost everywhere on `Ω`. -/
theorem HasWeakLineDeriv.unique (h : HasWeakLineDeriv Ω v f g) (h' : HasWeakLineDeriv Ω v f g') :
    g =ᵐ[volume.restrict Ω] g' :=
  Distribution.ofFun_injective h.2 h'.2 (h.eq.symm.trans h'.eq)

/-- The derivative of order zero: a locally integrable `f` is its own weak derivative along the
empty family of directions. -/
theorem hasWeakLineDeriv_fin_zero (v : Fin 0 → V) (hf : LocallyIntegrableOn f Ω volume) :
    HasWeakLineDeriv Ω v f f :=
  ⟨hf, hf, LineDeriv.iteratedLineDerivOp_fin_zero v _⟩

/-- The weak derivative of the zero function is zero. -/
theorem hasWeakLineDeriv_zero : HasWeakLineDeriv Ω v (0 : V → ℂ) 0 := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  rw [Distribution.ofFun_zero, LineDeriv.iteratedLineDerivOp_zero]

/-- Weak derivatives are additive: `∂^v (f + f') = ∂^v f + ∂^v f'`. -/
theorem HasWeakLineDeriv.add (h : HasWeakLineDeriv Ω v f g) (h' : HasWeakLineDeriv Ω v f' g') :
    HasWeakLineDeriv Ω v (f + f') (g + g') := by
  refine ⟨h.1.add h'.1, h.2.add h'.2, ?_⟩
  rw [Distribution.ofFun_add h.1 h'.1, Distribution.ofFun_add h.2 h'.2,
    LineDeriv.iteratedLineDerivOp_add, h.eq, h'.eq]

/-- The weak derivative of `-f` is `-∂^v f`. -/
theorem HasWeakLineDeriv.neg (h : HasWeakLineDeriv Ω v f g) : HasWeakLineDeriv Ω v (-f) (-g) := by
  refine ⟨h.1.neg, h.2.neg, ?_⟩
  rw [Distribution.ofFun_neg, Distribution.ofFun_neg, LineDeriv.iteratedLineDerivOp_neg, h.eq]

/-- Weak derivatives of differences: `∂^v (f - f') = ∂^v f - ∂^v f'`. -/
theorem HasWeakLineDeriv.sub (h : HasWeakLineDeriv Ω v f g) (h' : HasWeakLineDeriv Ω v f' g') :
    HasWeakLineDeriv Ω v (f - f') (g - g') := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

/-- Weak derivatives are homogeneous: `∂^v (c f) = c ∂^v f` for `c ∈ ℂ`. -/
theorem HasWeakLineDeriv.smul (h : HasWeakLineDeriv Ω v f g) (c : ℂ) :
    HasWeakLineDeriv Ω v (c • f) (c • g) := by
  refine (hasWeakLineDeriv_iff_integral (h.1.smul c) (h.2.smul c)).2 fun φ => ?_
  have hc : ∀ (w : V → ℝ) (u : V → ℂ), ∫ x, w x • (c • u) x = c • ∫ x, w x • u x := by
    intro w u
    rw [← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun x => smul_comm (w x) c (u x))
  rw [hc, hc, h.integral_eq φ, smul_comm]

/-- Weak derivatives only see `f` and `g` almost everywhere on `Ω`. -/
theorem HasWeakLineDeriv.congr_ae (h : HasWeakLineDeriv Ω v f g)
    (hf : f =ᵐ[volume.restrict Ω] f') (hg : g =ᵐ[volume.restrict Ω] g') :
    HasWeakLineDeriv Ω v f' g' := by
  refine ⟨h.1.congr hf, h.2.congr hg, ?_⟩
  rw [← Distribution.ofFun_congr_ae hf, ← Distribution.ofFun_congr_ae hg]
  exact h.eq

/-- **Weak derivatives are local**: a weak derivative on `Ω` is one on every open `Ω' ⊆ Ω`,
because a test function on `Ω'` is one on `Ω` (Mathlib's `TestFunction.monoCLM`). -/
theorem HasWeakLineDeriv.mono (h : HasWeakLineDeriv Ω v f g) (hΩ : Ω' ≤ Ω) :
    HasWeakLineDeriv Ω' v f g := by
  have hs : (Ω' : Set V) ⊆ Ω := hΩ
  refine (hasWeakLineDeriv_iff_integral (h.1.mono_set hs) (h.2.mono_set hs)).2 fun φ => ?_
  have hφ : ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : V → ℝ) = φ := by
    simp [hΩ]
  have h' := h.integral_eq (TestFunction.monoCLM ℝ φ)
  rwa [coe_iteratedLineDerivOp_eq hφ, hφ] at h'

/-! ### Sobolev spaces on open sets -/

/-- `W^0_p(Ω) = L_p(Ω)` for `1 ≤ p`. -/
theorem memWeakSobolev_zero_iff {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWeakSobolev Ω 0 p f ↔ MemLp f p (volume.restrict Ω) := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun k hk v => ?_⟩⟩
  obtain rfl : k = 0 := Nat.le_zero.1 hk
  exact ⟨f, h, hasWeakLineDeriv_fin_zero v (locallyIntegrableOn_of_memLp hp h)⟩

/-- `W^m_p(Ω) ⊆ W^n_p(Ω)` for `n ≤ m`. -/
theorem MemWeakSobolev.mono_order {p : ℝ≥0∞} {m n : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hnm : n ≤ m) : MemWeakSobolev Ω n p f :=
  ⟨hf.1, fun k hk v => hf.2 k (hk.trans hnm) v⟩

/-- Restriction to a smaller open set: `f ∈ W^m_p(Ω)` gives `f ∈ W^m_p(Ω')` for `Ω' ⊆ Ω`. -/
theorem MemWeakSobolev.mono_set {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hΩ : Ω' ≤ Ω) : MemWeakSobolev Ω' m p f := by
  have hμ : volume.restrict (Ω' : Set V) ≤ volume.restrict Ω :=
    Measure.restrict_mono (show (Ω' : Set V) ⊆ Ω from hΩ) le_rfl
  refine ⟨hf.1.mono_measure hμ, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  exact ⟨g, hg.mono_measure hμ, hfg.mono hΩ⟩

/-- The zero function lies in `W^m_p(Ω)`. -/
theorem zero_memWeakSobolev {p : ℝ≥0∞} {m : ℕ} : MemWeakSobolev Ω m p 0 :=
  ⟨MemLp.zero, fun _ _ _ => ⟨0, MemLp.zero, hasWeakLineDeriv_zero⟩⟩

/-- `W^m_p(Ω)` is closed under addition. -/
theorem MemWeakSobolev.add {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hf' : MemWeakSobolev Ω m p f') : MemWeakSobolev Ω m p (f + f') := by
  refine ⟨hf.1.add hf'.1, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  obtain ⟨g', hg', hfg'⟩ := hf'.2 k hk v
  exact ⟨g + g', hg.add hg', hfg.add hfg'⟩

/-- `W^m_p(Ω)` is closed under multiplication by complex scalars. -/
theorem MemWeakSobolev.smul {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f) (c : ℂ) :
    MemWeakSobolev Ω m p (c • f) := by
  refine ⟨hf.1.const_smul c, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  exact ⟨c • g, hg.const_smul c, hfg.smul c⟩

/-! ### Limits -/

/-- **Hölder bound for the pairing with a test function**: for `1 ≤ p`, a test function `φ` on
`Ω` with support `K` and every `h` a.e. strongly measurable on `Ω`,
`‖φ h‖_{L_1(Ω)} ≤ ‖φ‖_∞ |K|^(1 - 1/p) ‖h‖_{L_p(Ω)}` (Hölder on the compact set `K`: Mathlib's
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` and `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm`). -/
theorem eLpNorm_testFunction_smul_le {p : ℝ≥0∞} (hp : 1 ≤ p) (φ : 𝓓(Ω, ℝ)) {h : V → ℂ}
    (hh : AEStronglyMeasurable h (volume.restrict Ω)) :
    eLpNorm (fun x => φ x • h x) 1 (volume.restrict Ω) ≤
      eLpNorm φ ∞ volume * volume (tsupport φ) ^ (1 - 1 / p.toReal) *
        eLpNorm h p (volume.restrict Ω) := by
  set μ := volume.restrict (Ω : Set V)
  have hm : AEStronglyMeasurable (fun x => φ x • h x) μ := φ.continuous.aestronglyMeasurable.smul hh
  have hsupp : (Function.support fun x => φ x • h x) ⊆ tsupport φ := fun x hx =>
    subset_tsupport _ fun h0 => hx (by simp [h0])
  calc eLpNorm (fun x => φ x • h x) 1 μ
      = eLpNorm (fun x => φ x • h x) 1 (μ.restrict (tsupport φ)) :=
        (eLpNorm_restrict_eq_of_support_subset hm hsupp).symm
    _ ≤ eLpNorm (fun x => φ x • h x) p (μ.restrict (tsupport φ)) *
          (μ.restrict (tsupport φ)) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hm.restrict
    _ ≤ (eLpNorm φ ∞ volume * eLpNorm h p μ) * volume (tsupport φ) ^ (1 - 1 / p.toReal) := by
        gcongr
        · calc eLpNorm (fun x => φ x • h x) p (μ.restrict (tsupport φ))
              ≤ eLpNorm φ ∞ (μ.restrict (tsupport φ)) * eLpNorm h p (μ.restrict (tsupport φ)) :=
                eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p φ.continuous.aestronglyMeasurable
            _ ≤ eLpNorm φ ∞ volume * eLpNorm h p μ := by
                gcongr
                · exact Measure.restrict_le_self.trans Measure.restrict_le_self
                · exact Measure.restrict_le_self
        · rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one]
          exact ENNReal.rpow_le_rpow (Measure.restrict_apply_le _ _)
            (one_sub_one_div_toReal_nonneg hp)
    _ = _ := by ring

/-- If `‖h_i - h‖_{L_p(μ)} → 0` and `h ∈ L_p(μ)`, then eventually every `h_i` lies in `L_p(μ)`:
`h_i = (h_i - h) + h` with `‖h_i - h‖_p < 1` eventually. -/
theorem eventually_memLp_of_tendsto {α : Type*} [MeasurableSpace α] {p : ℝ≥0∞} {μ : Measure α}
    {ι : Type*} {l : Filter ι} {hs : ι → α → ℂ} {h : α → ℂ} (hh : MemLp h p μ)
    (hlim : Tendsto (fun i => eLpNorm (hs i - h) p μ) l (𝓝 0)) : ∀ᶠ i in l, MemLp (hs i) p μ := by
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one)] with i hi
  have hd : MemLp (hs i - h) p μ := memLp_iff.2 (hi.trans ENNReal.one_lt_top)
  simpa using hd.add hh

/-- **Convergence in `L_p(Ω)` gives convergence of the pairings with a test function**: if
`h_i → h` in `L_p(Ω)`, `1 ≤ p`, with `h ∈ L_p(Ω)` and `h_i ∈ L_p(Ω)` eventually, then
`∫ φ h_i → ∫ φ h` for every test function `φ` on `Ω`. -/
theorem tendsto_integral_testFunction_smul {p : ℝ≥0∞} (hp : 1 ≤ p) (φ : 𝓓(Ω, ℝ)) {ι : Type*}
    {l : Filter ι} {hs : ι → V → ℂ} {h : V → ℂ}
    (hhs : ∀ᶠ i in l, MemLp (hs i) p (volume.restrict Ω))
    (hh : MemLp h p (volume.restrict Ω))
    (hlim : Tendsto (fun i => eLpNorm (hs i - h) p (volume.restrict Ω)) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, φ x • hs i x) l (𝓝 (∫ x, φ x • h x)) := by
  have hcompl : ∀ u : V → ℂ, ∫ x in (Ω : Set V), φ x • u x = ∫ x, φ x • u x := fun u =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [φ.zero_on_compl hx]
  simp only [← hcompl]
  refine tendsto_integral_of_L1' _ (hhs.mono fun i hi =>
    (φ.integrable_smul (locallyIntegrableOn_of_memLp hp hi)).restrict) ?_
  have hC : eLpNorm φ ∞ volume * volume (tsupport φ) ^ (1 - 1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (φ.memLp_top).eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (one_sub_one_div_toReal_nonneg hp)
        φ.hasCompactSupport.isCompact.measure_ne_top)
  have hlim' := ENNReal.Tendsto.const_mul hlim (Or.inr hC)
  rw [mul_zero] at hlim'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun _ => bot_le) (hhs.mono fun i hi => ?_)
  have he : ((fun x => φ x • hs i x) - fun x => φ x • h x) = fun x => φ x • (hs i - h) x := by
    funext x
    simp [smul_sub]
  simp only [he]
  exact eLpNorm_testFunction_smul_le hp φ (hi.aestronglyMeasurable.sub hh.aestronglyMeasurable)

/-- **Weak derivatives pass to limits in `L_p(Ω)`**: if `g_i = ∂^v f_i` weakly on `Ω`,
`f ∈ L_p(Ω)`, `g ∈ L_r(Ω)`, `‖f_i - f‖_{L_p(Ω)} → 0` and `‖g_i - g‖_{L_r(Ω)} → 0` with
`1 ≤ p, r`, along a nontrivial filter, then `g = ∂^v f` weakly on `Ω`. Eventually the `f_i`
lie in `L_p(Ω)` and the `g_i` in `L_r(Ω)` (`Rd.eventually_memLp_of_tendsto`). -/
theorem HasWeakLineDeriv.of_tendsto {p r : ℝ≥0∞} (hp : 1 ≤ p) (hr : 1 ≤ r) {ι : Type*}
    {l : Filter ι} [l.NeBot] {fs gs : ι → V → ℂ} (h : ∀ i, HasWeakLineDeriv Ω v (fs i) (gs i))
    (hf : MemLp f p (volume.restrict Ω)) (hg : MemLp g r (volume.restrict Ω))
    (hlf : Tendsto (fun i => eLpNorm (fs i - f) p (volume.restrict Ω)) l (𝓝 0))
    (hlg : Tendsto (fun i => eLpNorm (gs i - g) r (volume.restrict Ω)) l (𝓝 0)) :
    HasWeakLineDeriv Ω v f g := by
  refine (hasWeakLineDeriv_iff_integral (locallyIntegrableOn_of_memLp hp hf)
    (locallyIntegrableOn_of_memLp hr hg)).2 fun φ => ?_
  have hfs := eventually_memLp_of_tendsto hf hlf
  have hgs := eventually_memLp_of_tendsto hg hlg
  refine tendsto_nhds_unique (tendsto_integral_testFunction_smul hr φ hgs hg hlg) ?_
  have hlim := (tendsto_integral_testFunction_smul hp (∂^{v} φ) hfs hf hlf).const_smul
    ((-1 : ℝ) ^ k)
  exact hlim.congr fun i => ((h i).integral_eq φ).symm

/-! ### Cutting Schwartz functions off -/

omit [MeasurableSpace V] [BorelSpace V] in
/-- The product of the rescaled cut-off `x ↦ χ(x/(n+1))`, `χ = Rd.cutoff 1 2`, with any function
has compact support. This function-level form enters the definition of `Rd.cutoffMul`. -/
theorem hasCompactSupport_cutoff_smul_mul (n : ℕ) (u : V → ℂ) :
    HasCompactSupport fun x => cutoff 1 2 one_pos one_lt_two (((n : ℝ) + 1)⁻¹ • x) * u x := by
  have h := ((hasCompactSupport_cutoff (V := V) one_pos one_lt_two).comp_smul
    (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).mul_right (f' := u)
  exact h

/-- The **cut-off** of a Schwartz function `u` at radius `n + 1`: `x ↦ χ(x/(n+1)) u(x)` with the
smooth cut-off `χ = Rd.cutoff 1 2` (equal to `1` on the closed unit ball and to `0` outside the
ball of radius `2`), a smooth function with compact support. -/
noncomputable def cutoffMul (n : ℕ) (u : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  HasCompactSupport.toSchwartzMap (hasCompactSupport_cutoff_smul_mul n u)
    (((contDiff_cutoff one_pos one_lt_two).comp (contDiff_const_smul _)).mul (u.smooth ⊤))

omit [MeasurableSpace V] [BorelSpace V] in
/-- The values of the cut-off: `cutoffMul n u x = χ(x/(n+1)) u(x)`. -/
theorem cutoffMul_apply (n : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    cutoffMul n u x = cutoff 1 2 one_pos one_lt_two (((n : ℝ) + 1)⁻¹ • x) * u x :=
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off of a Schwartz function has compact support. -/
theorem hasCompactSupport_cutoffMul (n : ℕ) (u : 𝓢(V, ℂ)) : HasCompactSupport (cutoffMul n u) :=
  hasCompactSupport_cutoff_smul_mul n u

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off at radius `n + 1` agrees with `u` near every point of the open ball of radius
`n + 1`. -/
theorem cutoffMul_eventuallyEq (u : 𝓢(V, ℂ)) {n : ℕ} {x : V} (hx : ‖x‖ < n + 1) :
    (cutoffMul n u : V → ℂ) =ᶠ[𝓝 x] u := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
  have hy' : ‖((n : ℝ) + 1)⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity), mul_one]
    exact (mem_ball_zero_iff.1 hy).le
  rw [cutoffMul_apply, cutoff_eq_one one_pos one_lt_two hy', one_mul]

omit [MeasurableSpace V] [BorelSpace V] in
/-- For `0 ≤ c ≤ 1` the derivatives of the rescaled cut-off `x ↦ χ(c x)` are bounded by the
Schwartz seminorms `p_{0,i}(χ) = sup ‖D^i χ‖` of `χ = Rd.cutoffSchwartz 1 2`, because
`D^i (χ(c ·))(x) = c^i D^i χ(c x)` (Mathlib's `iteratedFDeriv_comp_const_smul`). -/
theorem norm_iteratedFDeriv_cutoff_comp_smul_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (i : ℕ)
    (x : V) :
    ‖iteratedFDeriv ℝ i (fun y => cutoff 1 2 one_pos one_lt_two (c • y)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) := by
  rw [iteratedFDeriv_comp_const_smul c
    ((contDiff_cutoff one_pos one_lt_two).of_le (mod_cast le_top)), norm_smul, norm_pow,
    Real.norm_of_nonneg hc0]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0 hc1)).trans
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
      (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) i (c • x))

omit [MeasurableSpace V] [BorelSpace V] in
/-- The **Leibniz bound** for the cut-off: `‖D^m (χ_n u)(x)‖ ≤ ∑_{i ≤ m} C(m,i) p_{0,i}(χ)
‖D^(m-i) u(x)‖`, uniformly in `n` (Mathlib's `norm_iteratedFDeriv_mul_le`). -/
theorem norm_iteratedFDeriv_cutoffMul_le (n m : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    ‖iteratedFDeriv ℝ m (cutoffMul n u) x‖ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
        ‖iteratedFDeriv ℝ (m - i) u x‖ := by
  have hc0 : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have hc1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
  refine (norm_iteratedFDeriv_mul_le
    ((contDiff_cutoff one_pos one_lt_two).comp (contDiff_const_smul ((n : ℝ) + 1)⁻¹))
    (u.smooth ⊤) x (mod_cast le_top)).trans ?_
  gcongr with i hi
  exact norm_iteratedFDeriv_cutoff_comp_smul_le hc0 hc1 i x

/-- The pointwise bound for the `m`-th derivative of `u - χ_n u`:
`B(x) = ‖D^m u(x)‖ + ∑_{i ≤ m} C(m,i) p_{0,i}(χ) ‖D^(m-i) u(x)‖`, the derivative of `u` plus the
Leibniz bound of `Rd.norm_iteratedFDeriv_cutoffMul_le`, with `χ = Rd.cutoffSchwartz 1 2`. -/
noncomputable def cutoffMulBound (m : ℕ) (u : 𝓢(V, ℂ)) (x : V) : ℝ :=
  ‖iteratedFDeriv ℝ m u x‖ + ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
      ‖iteratedFDeriv ℝ (m - i) u x‖

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivatives of `u - χ_n u` are bounded by the pointwise bound `Rd.cutoffMulBound`,
uniformly in `n`. -/
theorem norm_iteratedFDeriv_sub_cutoffMul_le (n m : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    ‖iteratedFDeriv ℝ m (u - cutoffMul n u) x‖ ≤ cutoffMulBound m u x := by
  have hsub : ((u - cutoffMul n u : 𝓢(V, ℂ)) : V → ℂ) = u - cutoffMul n u := rfl
  rw [hsub, iteratedFDeriv_sub_apply ((u.smooth ⊤).of_le (mod_cast le_top)).contDiffAt
    (((cutoffMul n u).smooth ⊤).of_le (mod_cast le_top)).contDiffAt, cutoffMulBound]
  exact (norm_sub_le _ _).trans (add_le_add_right (norm_iteratedFDeriv_cutoffMul_le n m u x) _)

omit [MeasurableSpace V] [BorelSpace V] in
/-- All derivatives of `u - χ_n u` vanish on the open ball of radius `n + 1`, where the cut-off
is `1`. -/
theorem iteratedFDeriv_sub_cutoffMul_eq_zero (u : 𝓢(V, ℂ)) {n : ℕ} {x : V} (hx : ‖x‖ < n + 1)
    (m : ℕ) : iteratedFDeriv ℝ m (u - cutoffMul n u) x = 0 := by
  have h : ((u - cutoffMul n u : 𝓢(V, ℂ)) : V → ℂ) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    filter_upwards [cutoffMul_eventuallyEq u hx] with y hy
    simp [hy]
  rw [(h.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply]

/-- The constant of the cut-off estimate `Rd.seminorm_sub_cutoffMul_le`:
`p_{k+1,m}(u) + ∑_{i ≤ m} C(m,i) p_{0,i}(χ) p_{k+1,m-i}(u)` in the Schwartz seminorms of `u` and
of the cut-off `χ = Rd.cutoffSchwartz 1 2`. -/
noncomputable def cutoffMulConst (k m : ℕ) (u : 𝓢(V, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ (k + 1) m u + ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
      SchwartzMap.seminorm ℝ (k + 1) (m - i) u

omit [MeasurableSpace V] [BorelSpace V] in
/-- The constant of the cut-off estimate is nonnegative. -/
theorem cutoffMulConst_nonneg (k m : ℕ) (u : 𝓢(V, ℂ)) : 0 ≤ cutoffMulConst k m u := by
  unfold cutoffMulConst
  positivity

omit [MeasurableSpace V] [BorelSpace V] in
/-- The pointwise form of the cut-off estimate: `‖x‖^(k+1) B(x) ≤ Rd.cutoffMulConst k m u` for
the pointwise bound `B = Rd.cutoffMulBound m u`. -/
theorem norm_pow_succ_mul_cutoffMulBound_le (k m : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    ‖x‖ ^ (k + 1) * cutoffMulBound m u x ≤ cutoffMulConst k m u := by
  rw [cutoffMulBound, mul_add, Finset.mul_sum, cutoffMulConst]
  refine add_le_add (SchwartzMap.le_seminorm ℝ (k + 1) m u x) (Finset.sum_le_sum fun i _ => ?_)
  rw [mul_comm, mul_assoc]
  gcongr
  rw [mul_comm]
  exact SchwartzMap.le_seminorm ℝ (k + 1) (m - i) u x

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The cut-off estimate**: the Schwartz seminorm `p_{k,m}(u - χ_n u)` is at most
`Rd.cutoffMulConst k m u / (n + 1)`, because `u - χ_n u` vanishes on the ball of radius `n + 1`
and `‖x‖^k ≤ ‖x‖^(k+1)/(n+1)` outside it. -/
theorem seminorm_sub_cutoffMul_le (k m n : ℕ) (u : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℝ k m (u - cutoffMul n u) ≤ cutoffMulConst k m u / ((n : ℝ) + 1) := by
  have hC := cutoffMulConst_nonneg k m u
  refine SchwartzMap.seminorm_le_bound ℝ k m _ (by positivity) fun x => ?_
  rcases lt_or_ge ‖x‖ (n + 1) with hx | hx
  · rw [iteratedFDeriv_sub_cutoffMul_eq_zero u hx, norm_zero, mul_zero]
    positivity
  rw [le_div_iff₀ (by positivity)]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (u - cutoffMul n u) x‖ * ((n : ℝ) + 1)
      ≤ ‖x‖ ^ k * cutoffMulBound m u x * ‖x‖ := by
        have hB := norm_iteratedFDeriv_sub_cutoffMul_le n m u x
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) hx (by positivity)
          (mul_nonneg (by positivity) ((norm_nonneg _).trans hB))
    _ = ‖x‖ ^ (k + 1) * cutoffMulBound m u x := by ring
    _ ≤ cutoffMulConst k m u := norm_pow_succ_mul_cutoffMulBound_le k m u x

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The cut-offs converge in the Schwartz space**: `χ_n u → u` in `𝓢(V, ℂ)`, since every
Schwartz seminorm of `u - χ_n u` is `O(1/(n+1))` (`Rd.seminorm_sub_cutoffMul_le`, Mathlib's
`schwartz_withSeminorms`). Hence smooth compactly supported functions are dense in
`𝓢(V, ℂ)`. -/
theorem tendsto_cutoffMul (u : 𝓢(V, ℂ)) :
    Tendsto (fun n : ℕ => cutoffMul n u) atTop (𝓝 u) := by
  rw [(schwartz_withSeminorms ℝ V ℂ).tendsto_nhds _ u]
  rintro ⟨k, m⟩ ε hε
  have h0 : Tendsto (fun n : ℕ => cutoffMulConst k m u / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with n hn
  rw [SchwartzMap.schwartzSeminormFamily_apply, map_sub_rev]
  exact (seminorm_sub_cutoffMul_le k m n u).trans_lt hn

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Test functions determine tempered distributions**: a tempered distribution on `V` that
vanishes on all real test functions is zero. The cut-offs `Rd.cutoffMul n u` of a Schwartz
function `u` are combinations of test functions (`Rd.exists_testSchwartz_eq`) and converge to `u`
in `𝓢(V, ℂ)` (`Rd.tendsto_cutoffMul`). -/
theorem eq_zero_of_testSchwartz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : 𝓢'(V, F)} (h : ∀ φ : 𝓓((⊤ : Opens V), ℝ), T (testSchwartz φ) = 0) : T = 0 := by
  ext1 u
  have hn : ∀ n : ℕ, T (cutoffMul n u) = 0 := fun n => by
    obtain ⟨a, b, hab⟩ := exists_testSchwartz_eq (cutoffMul n u) (hasCompactSupport_cutoffMul n u)
    rw [hab, map_add, map_smul, h, h, smul_zero, add_zero]
  have ht : Tendsto (fun n : ℕ => T (cutoffMul n u)) atTop (𝓝 (T u)) :=
    ((map_continuous T).tendsto u).comp (tendsto_cutoffMul u)
  simp only [hn] at ht
  simpa using tendsto_nhds_unique ht tendsto_const_nhds

/-! ### The bridge to tempered distributions -/

section Bridge

variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- An `L_p(V)` function, `1 ≤ p`, is locally integrable on `V`: the case `Ω = V` of
`Rd.locallyIntegrableOn_of_memLp`. -/
theorem locallyIntegrableOn_top_Lp (f : Lp ℂ p (volume : Measure V)) :
    LocallyIntegrableOn f ((⊤ : Opens V) : Set V) volume :=
  locallyIntegrableOn_of_memLp Fact.out (by simpa using Lp.memLp f)

/-- On `Ω = V`, the distribution of `f ∈ L_p(V)` applied to a test function `φ` is the tempered
distribution of `f` applied to the Schwartz function `φ`: both are `∫ φ f`. -/
theorem ofFun_top_apply (f : Lp ℂ p (volume : Measure V)) (φ : 𝓓((⊤ : Opens V), ℝ)) :
    Distribution.ofFun ⊤ (f : V → ℂ) volume ⊤ φ = (f : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [Distribution.ofFun_apply (locallyIntegrableOn_top_Lp f), Lp.toTemperedDistribution_apply]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [Complex.real_smul]

/-- On `Ω = V`, the iterated derivatives of `f ∈ L_p(V)` as a distribution and as a tempered
distribution agree on test functions. -/
theorem iteratedLineDerivOp_ofFun_top_apply (v : Fin k → V) (f : Lp ℂ p (volume : Measure V))
    (φ : 𝓓((⊤ : Opens V), ℝ)) :
    ∂^{v} (Distribution.ofFun ⊤ (f : V → ℂ) volume ⊤) φ =
      ∂^{v} (f : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [Distribution.iteratedLineDerivOp_apply_apply, ofFun_top_apply,
    TemperedDistribution.iteratedLineDerivOp_apply_apply, map_smul,
    iteratedLineDerivOp_testSchwartz]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one]

/-- **Weak derivatives on `V` are derivatives of tempered distributions**: for `f ∈ L_p(V)` and
`g ∈ L_r(V)`, `1 ≤ p, r`, `g` is the weak derivative `∂^v f` on `V` iff `∂^v f = g` in
`𝓢'(V, ℂ)`. One direction tests with the Schwartz functions `Rd.testSchwartz φ`; the other uses
that tempered distributions are determined by test functions (`Rd.eq_zero_of_testSchwartz`). -/
theorem hasWeakLineDeriv_top_iff {f : Lp ℂ p (volume : Measure V)}
    {g : Lp ℂ r (volume : Measure V)} :
    HasWeakLineDeriv ⊤ v f g ↔ ∂^{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ)) := by
  constructor
  · intro h
    rw [← sub_eq_zero]
    refine eq_zero_of_testSchwartz fun φ => ?_
    have h' := DFunLike.congr_fun h.eq φ
    rw [iteratedLineDerivOp_ofFun_top_apply, ofFun_top_apply] at h'
    simp [h']
  · intro h
    refine ⟨locallyIntegrableOn_top_Lp f, locallyIntegrableOn_top_Lp g, ?_⟩
    ext φ
    rw [iteratedLineDerivOp_ofFun_top_apply, ofFun_top_apply, h]

/-- The iterated derivative `∂^v` of the `L_p(V)` class of a Schwartz function `η`, as a tempered
distribution, is the `L_r(V)` class of the Schwartz function `∂^v η`, as a tempered
distribution. -/
theorem iteratedLineDerivOp_toLp_eq (η : 𝓢(V, ℂ)) (v : Fin k → V) :
    ∂^{v} ((η.toLp p (volume : Measure V) : Lp ℂ p (volume : Measure V)) : 𝓢'(V, ℂ)) =
      ((∂^{v} η).toLp r (volume : Measure V) : 𝓢'(V, ℂ)) := by
  rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq]

/-- **Schwartz functions**: on every open set `Ω`, the classical iterated derivative `∂^v η` of a
Schwartz function `η` is its weak derivative. -/
theorem hasWeakLineDeriv_schwartz (Ω : Opens V) (η : 𝓢(V, ℂ)) (v : Fin k → V) :
    HasWeakLineDeriv Ω v η ((∂^{v} η : 𝓢(V, ℂ)) : V → ℂ) := by
  have h := (hasWeakLineDeriv_top_iff (p := 2) (r := 2)).2
    (iteratedLineDerivOp_toLp_eq (p := 2) (r := 2) η v)
  refine (h.congr_ae ?_ ?_).mono le_top
  · rw [volume_restrict_top]
    exact η.coeFn_toLp 2 volume
  · rw [volume_restrict_top]
    exact (∂^{v} η).coeFn_toLp 2 volume

/-- **Sobolev spaces by tempered distributions**: `f ∈ L_p(V)` lies in `W^m_p(V)` iff for every
order `k ≤ m` and all directions `v`, the tempered derivative `∂^v f` is an `L_p(V)` function. -/
theorem memSobolev_iff_tempered {m : ℕ} (f : Lp ℂ p (volume : Measure V)) :
    MemSobolev m f ↔ ∀ k ≤ m, ∀ v : Fin k → V,
      ∃ g : Lp ℂ p (volume : Measure V), ∂^{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ)) := by
  constructor
  · rintro ⟨-, h⟩ k hk v
    obtain ⟨g, hg, hfg⟩ := h k hk v
    rw [volume_restrict_top] at hg
    refine ⟨hg.toLp g, hasWeakLineDeriv_top_iff.1 (hfg.congr_ae Filter.EventuallyEq.rfl ?_)⟩
    rw [volume_restrict_top]
    exact hg.coeFn_toLp.symm
  · intro h
    refine ⟨by simpa using Lp.memLp f, fun k hk v => ?_⟩
    obtain ⟨g, hg⟩ := h k hk v
    exact ⟨g, by simpa using Lp.memLp g, hasWeakLineDeriv_top_iff.2 hg⟩

/-- Schwartz functions lie in every Sobolev space `W^m_p(V)`. -/
theorem memSobolev_toLp (η : 𝓢(V, ℂ)) (m : ℕ) :
    MemSobolev m (η.toLp p (volume : Measure V)) :=
  (memSobolev_iff_tempered _).2 fun _ _ v => ⟨_, iteratedLineDerivOp_toLp_eq (r := p) η v⟩

end Bridge

end Rd
