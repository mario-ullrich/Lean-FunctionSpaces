/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.SchwartzCutoff

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
  (`Rd.hasWeakLineDeriv_iff_integral`, by the transpose formula
  `Distribution.iteratedLineDerivOp_apply_apply`). They are unique almost everywhere on `Ω`,
  linear, local (`Rd.HasWeakLineDeriv.mono`), vanish where `f` vanishes
  (`Rd.HasWeakLineDeriv.ae_eq_zero_of_ae_eq_zero`), classical on Schwartz functions
  (`Rd.hasWeakLineDeriv_schwartz`), and pass to limits in `L_p(Ω)`
  (`Rd.HasWeakLineDeriv.of_tendsto`).
* **Sobolev spaces**: `Rd.MemWeakSobolev Ω m p f` says that `f` and all its weak derivatives of
  order at most `m` lie in `L_p(Ω)`; `Rd.MemSobolev m f` is the case `Ω = V` for `f ∈ L_p(V)`.
* **The bridge to tempered distributions** (`Rd.hasWeakLineDeriv_top_iff`): for `f ∈ L_p(V)`,
  `g ∈ L_r(V)`, the weak derivative on `V` is the derivative of tempered distributions,
  `∂^v f = g` in `𝓢'(V, ℂ)`, since a tempered distribution that vanishes on all test functions
  is zero (`Rd.eq_zero_of_testSchwartz`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal SchwartzMap LineDeriv Distributions

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

/-- **Weak derivatives vanish where the function vanishes**: if `g` is a weak derivative `∂^v f`
on `Ω`, `O ⊆ Ω` is open and `f = 0` almost everywhere on `O`, then `g = 0` almost everywhere on
`O`, by locality (`Rd.HasWeakLineDeriv.mono`) and uniqueness (`Rd.HasWeakLineDeriv.unique`). -/
theorem HasWeakLineDeriv.ae_eq_zero_of_ae_eq_zero {O : Opens V} (h : HasWeakLineDeriv Ω v f g)
    (hO : O ≤ Ω) (hf : f =ᵐ[volume.restrict (O : Set V)] 0) :
    g =ᵐ[volume.restrict (O : Set V)] 0 :=
  ((h.mono hO).congr_ae hf EventuallyEq.rfl).unique hasWeakLineDeriv_zero

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

/-- `W^m_p(Ω)` only sees `f` almost everywhere on `Ω`: if `f ∈ W^m_p(Ω)` and `f = f'` almost
everywhere on `Ω`, then `f' ∈ W^m_p(Ω)`; the weak derivatives of `f` serve for `f'`
(`Rd.HasWeakLineDeriv.congr_ae`). -/
theorem MemWeakSobolev.congr_ae {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hff' : f =ᵐ[volume.restrict Ω] f') : MemWeakSobolev Ω m p f' := by
  refine ⟨MemLp.ae_eq hff' hf.1, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  exact ⟨g, hg, hfg.congr_ae hff' Filter.EventuallyEq.rfl⟩

/-- The zero class lies in `W^m_p(V)`. -/
theorem zero_memSobolev {p : ℝ≥0∞} {m : ℕ} : MemSobolev m (0 : Lp ℂ p (volume : Measure V)) :=
  zero_memWeakSobolev.congr_ae (ae_restrict_of_ae (Lp.coeFn_zero ..).symm)

/-- `W^m_p(V)` is closed under addition in `L_p(V)`. -/
theorem MemSobolev.add {p : ℝ≥0∞} {m : ℕ} {F G : Lp ℂ p (volume : Measure V)}
    (hF : MemSobolev m F) (hG : MemSobolev m G) : MemSobolev m (F + G) :=
  (MemWeakSobolev.add hF hG).congr_ae (ae_restrict_of_ae (Lp.coeFn_add F G).symm)

/-- `W^m_p(V)` is closed under multiplication by complex scalars in `L_p(V)`. -/
theorem MemSobolev.smul {p : ℝ≥0∞} {m : ℕ} {F : Lp ℂ p (volume : Measure V)}
    (hF : MemSobolev m F) (c : ℂ) : MemSobolev m (c • F) :=
  (MemWeakSobolev.smul hF c).congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c F).symm)

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
