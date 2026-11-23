/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.Daubechies.TensorWavelets

/-!
# Expansions in dilated and translated generators on `ℝ^d`

Let `G_ν : ℝ^d → ℂ`, `ν ∈ ι`, be a finite family of generators that vanish outside the cube
`[a, b]^d`. Their dilated and translated copies of level `j ∈ ℕ` and position `k ∈ ℤ^d` are
`G_{ν,j,k}(x) = 2^(jd/2) G_ν(2^j x - k)` (`Daubechies.tensorScaled`), and they give the expansions
and the coefficients

`∑_{(ν,k)} c_{ν,k} G_{ν,j,k}(x)` (`Daubechies.tensorExpand`) and
`⟨f, G_{ν,j,k}⟩ = ∫ f(y) conj G_{ν,j,k}(y) dy` (`Daubechies.tensorCoeff`).

This is the `d`-dimensional form of `FunctionSpaces.Wavelets.Examples.Daubechies.Expansion`; one
family serves the tensor scaling function `Φ` (`ι` with one element) and the `2^d - 1` tensor
wavelets alike (`Daubechies.tensorGen`). For a tensor product the dilated and translated copy is
the tensor product of the one-dimensional ones (`Daubechies.tensorScaled_tensorKernel`), so that
`Φ_{j,k}(x) = ∏_i φ_{j,k_i}(x_i)` (`Daubechies.tensorScaled_tensorGen_empty`).

* **Finitely many terms.** `G_{ν,j,k}` vanishes outside the window
  `{x : 2^j x_i - k_i ∈ [a, b] for all i}` (`Daubechies.tensorWindow`), and the positions of the
  windows of one level that contain a point lie in a box of at most `M^d` positions,
  `M = ⌈b - a⌉ + 1` (`Daubechies.tensorBox`, `Daubechies.card_tensorBox_le`). So every point lies
  in at most `|ι| M^d` windows of the family (`Daubechies.tensorOverlap`,
  `Daubechies.card_le_tensorOverlap`), every expansion is a finite sum at each point
  (`Daubechies.tensorExpand_eq_sum`), continuous for continuous generators
  (`Daubechies.continuous_tensorExpand`) and a.e. strongly measurable for a.e. strongly measurable
  ones (`Daubechies.aestronglyMeasurable_tensorExpand`).
* **`L_p` norms of the generators.** `‖G_{ν,j,k}‖_p = 2^(jd(1/2 - 1/p)) ‖G_ν‖_p`
  (`Daubechies.eLpNorm_tensorScaled`): the dilation `x ↦ 2^j x` scales Lebesgue measure on `ℝ^d`
  by `2^(-jd)` (Mathlib's `MeasureTheory.Measure.map_addHaar_smul`). A continuous function that
  vanishes outside `[a, b]^d` lies in every `L_q`
  (`Daubechies.memLp_of_continuous_of_exists_notMem`).
* **Orthonormality and coefficient recovery.** `∫ G_{ν,j,k} conj G_{ν',j,l}` equals the inner
  product of the integer translates `G_ν(· - k)` and `G_{ν'}(· - l)` at every level
  (`Daubechies.integral_tensorScaled_mul_conj`), so for continuous generators a coefficient of an
  expansion is a finite combination of these inner products
  (`Daubechies.tensorCoeff_tensorExpand_eq_sum`). If the translates are orthonormal, then
  `⟨∑ c_{ν',l} G_{ν',j,l}, G_{ν,j,k}⟩ = c_{ν,k}` for every coefficient family `c`
  (`Daubechies.tensorCoeff_tensorExpand`); if they are orthogonal to the translates of a second
  family `G'_μ`, then `⟨∑ c_{ν,l} G_{ν,j,l}, G'_{μ,j,k}⟩ = 0`
  (`Daubechies.tensorCoeff_tensorExpand_eq_zero`). The expansion of the coefficient family that
  is `1` at `(ν, k)` and `0` elsewhere is `G_{ν,j,k}` (`Daubechies.tensorExpand_single`), and the
  expansion of the zero family is `0` (`Daubechies.tensorExpand_zero`).
* **Stability.** For `1 ≤ p < ∞`, with the overlap number `L = |ι| M^d` and the conjugate exponent
  `p'`, the upper estimate
  `‖∑ c_{ν,k} G_{ν,j,k}‖_p ≤ L^(1 - 1/p) B 2^(jd(1/2 - 1/p)) ‖c‖_{ℓ_p}` for `‖G_ν‖_p ≤ B`
  (`Daubechies.eLpNorm_tensorExpand_le`) and the coefficient estimate
  `‖(⟨f, G_{ν,j,k}⟩)_{ν,k}‖_{ℓ_p} ≤ L^(1/p) B' 2^(-jd(1/2 - 1/p)) ‖f‖_p` for `‖G_ν‖_{p'} ≤ B'`
  (`Daubechies.lqNorm_tensorCoeff_le`, by Hölder's inequality on each window) hold. With
  `B = max_ν ‖G_ν‖_p` and `B' = max_ν ‖G_ν‖_{p'}` they give the constants
  `C = L^(1 - 1/p) max_ν ‖G_ν‖_p` (`Daubechies.tensorExpandConst`) and
  `C' = L^(1/p) max_ν ‖G_ν‖_{p'}` (`Daubechies.tensorCoeffConst`), the same for every level. For
  continuous generators with orthonormal translates the lower estimate
  `2^(jd(1/2 - 1/p)) ‖c‖_{ℓ_p} ≤ C' ‖∑ c_{ν,k} G_{ν,j,k}‖_p` holds
  (`Daubechies.lqNorm_le_eLpNorm_tensorExpand`), and for all generators
  `‖∑ ⟨f, G_{ν,j,k}⟩ G_{ν,j,k}‖_p ≤ C C' ‖f‖_p` (`Daubechies.eLpNorm_tensorExpand_tensorCoeff_le`).
* **The Bernstein inequality.** Differences commute with dilation and translation,
  `Δ_h^r G_{ν,j,k} = (Δ_{2^j h}^r G_ν)_{j,k}` (`Daubechies.iterate_fwdDiff_tensorScaled`), so
  `Δ_h^r ∑ c_{ν,k} G_{ν,j,k} = ∑ c_{ν,k} (Δ_{2^j h}^r G_ν)_{j,k}`
  (`Daubechies.iterate_fwdDiff_tensorExpand`), and `Δ_H^r G_ν` vanishes outside
  `[a - r‖H‖, b + r‖H‖]^d` (`Daubechies.iterate_fwdDiff_eq_zero_of_exists_notMem`). For a function
  `f` that is a.e. the expansion of its own coefficients of level `j` and for `2^j t ≤ 1`,
  `ω_r(f, t)_p ≤ C_B sup_{ν, ‖H‖ ≤ 2^j t} ‖Δ_H^r G_ν‖_p ‖f‖_p` with `C_B = L_r^(1 - 1/p) C'`,
  `L_r = |ι| (⌈b - a + 2r⌉ + 1)^d`, independent of `j`, `t` and `f`
  (`Daubechies.smoothnessModulus_tensorExpand_le`, `Daubechies.tensorBernsteinConst`).

The norm on `ℝ^d` is the sup norm, so `‖H‖ ≤ 1` bounds every coordinate `|H_i|`.
-/

@[expose] public section

open Filter MeasureTheory Topology Module
open scoped ENNReal ComplexConjugate
open ENNReal (dyadicWeight lqNorm)

namespace Daubechies

variable {d : ℕ}

/-! ### Dilated and translated generators -/

section Generators

variable {g : (Fin d → ℝ) → ℂ} {a b : ℝ}

/-- **The dilated and translated generator on `ℝ^d`**:
`g_{j,k}(x) = 2^(jd/2) g(2^j x - k)` of level `j ∈ ℕ` and position `k ∈ ℤ^d`, written with the
factor `(2^(j/2))^d`. The factor makes the `L_2` norm independent of `j` and `k`
(`Daubechies.eLpNorm_tensorScaled`). -/
noncomputable def tensorScaled (g : (Fin d → ℝ) → ℂ) (j : ℕ) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    ℂ :=
  (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) ^ d * g ((2 : ℝ) ^ j • x - fun i => (k i : ℝ))

/-- The coordinates of `2^j x - k` are `2^j x_i - k_i`. -/
theorem two_pow_smul_sub_apply (j : ℕ) (x : Fin d → ℝ) (k : Fin d → ℤ) (i : Fin d) :
    ((2 : ℝ) ^ j • x - fun i => (k i : ℝ)) i = 2 ^ j * x i - k i := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- **The generators of level `0` are the integer translates**: `g_{0,k}(x) = g(x - k)` for every
`k ∈ ℤ^d`, since `2^0 = 1`. -/
theorem tensorScaled_zero (g : (Fin d → ℝ) → ℂ) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    tensorScaled g 0 k x = g (x - fun i => (k i : ℝ)) := by
  simp [tensorScaled]

/-- **Dilated and translated tensor products**: for `K_1, …, K_d : ℝ → ℂ`,
`(⊗K)_{j,k} = ⊗_i (K_i)_{j,k_i}` with the one-dimensional
`(K_i)_{j,k_i}(t) = 2^(j/2) K_i(2^j t - k_i)` (`Daubechies.scaledFun`): the factor `(2^(j/2))^d`
splits into one factor `2^(j/2)` per coordinate. -/
theorem tensorScaled_tensorKernel (K : Fin d → ℝ → ℂ) (j : ℕ) (k : Fin d → ℤ) :
    tensorScaled (Rd.tensorKernel K) j k = Rd.tensorKernel fun i => scaledFun (K i) j (k i) := by
  funext x
  simp only [tensorScaled, Rd.tensorKernel_apply, scaledFun, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, two_pow_smul_sub_apply]

/-- **The tensor scaling function at level `j`**: for a Daubechies mask, `Φ = Ψ^∅` satisfies
`Φ_{j,k}(x) = ∏_i φ_{j,k_i}(x_i)` for every level `j`, position `k ∈ ℤ^d` and `x ∈ ℝ^d`
(`Daubechies.tensorScaled_tensorKernel`). -/
theorem tensorScaled_tensorGen_empty {N : ℕ} (m : Mask N) (j : ℕ) (k : Fin d → ℤ)
    (x : Fin d → ℝ) : tensorScaled (tensorGen m ∅) j k x = ∏ i, scaled m j (k i) (x i) := by
  rw [tensorGen, tensorScaled_tensorKernel, Rd.tensorKernel_apply]
  simp only [Finset.notMem_empty, ↓reduceIte]

/-- **The window of a generator**: the set `{x : 2^j x_i - k_i ∈ [a, b] for all i}`, the product
of the one-dimensional support windows (`Daubechies.supportWindow`), outside which `g_{j,k}`
vanishes when `g` vanishes outside `[a, b]^d` (`Daubechies.tensorScaled_eq_zero`). -/
def tensorWindow (a b : ℝ) (j : ℕ) (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => supportWindow a b j (k i)

/-- `x` lies in the window of level `j` and position `k` iff `2^j x_i - k_i ∈ [a, b]` for every
coordinate `i`. -/
theorem mem_tensorWindow {j : ℕ} {k : Fin d → ℤ} {x : Fin d → ℝ} :
    x ∈ tensorWindow a b j k ↔ ∀ i, (2 : ℝ) ^ j * x i - k i ∈ Set.Icc a b := by
  simp only [tensorWindow, Set.mem_univ_pi]
  rfl

/-- The windows are measurable (products of closed intervals). -/
theorem measurableSet_tensorWindow (a b : ℝ) (j : ℕ) (k : Fin d → ℤ) :
    MeasurableSet (tensorWindow a b j k) :=
  MeasurableSet.univ_pi fun i => measurableSet_supportWindow a b j (k i)

/-- The windows are compact (products of closed bounded intervals). -/
theorem isCompact_tensorWindow (a b : ℝ) (j : ℕ) (k : Fin d → ℤ) :
    IsCompact (tensorWindow a b j k) :=
  isCompact_univ_pi fun i => isCompact_supportWindow a b j (k i)

/-- **Support of `g_{j,k}`**: if `g(x) = 0` whenever some coordinate `x_i` lies outside `[a, b]`,
then `g_{j,k}(x) = 0` for every `x` outside the window `{x : 2^j x_i - k_i ∈ [a, b] for all i}`. -/
theorem tensorScaled_eq_zero (hg : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0) {j : ℕ}
    {k : Fin d → ℤ} {x : Fin d → ℝ} (hx : x ∉ tensorWindow a b j k) : tensorScaled g j k x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.1 fun h => hx (mem_tensorWindow.2 h)
  rw [tensorScaled, hg _ ⟨i, by rwa [two_pow_smul_sub_apply]⟩, mul_zero]

/-- If `g` vanishes outside `[a, b]^d` and `g_{j,k}(x) ≠ 0`, then `x` lies in the window of level
`j` and position `k` (`Daubechies.tensorScaled_eq_zero`). -/
theorem mem_tensorWindow_of_tensorScaled_ne_zero (hg : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0)
    {j : ℕ} {k : Fin d → ℤ} {x : Fin d → ℝ} (h : tensorScaled g j k x ≠ 0) :
    x ∈ tensorWindow a b j k :=
  by_contra fun hx => h (tensorScaled_eq_zero hg hx)

/-- **`g_{j,k}` has compact support** if `g` vanishes outside `[a, b]^d`: it vanishes outside the
compact window (`Daubechies.tensorScaled_eq_zero`). -/
theorem hasCompactSupport_tensorScaled (hg : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0) (j : ℕ)
    (k : Fin d → ℤ) : HasCompactSupport (tensorScaled g j k) :=
  HasCompactSupport.intro (isCompact_tensorWindow a b j k) fun _ hx => tensorScaled_eq_zero hg hx

/-- **Functions vanishing outside a cube have compact support**: if `F(x) = 0` whenever some
coordinate `x_i` lies outside `[a, b]`, then `F` vanishes outside the compact cube `[a, b]^d`. -/
theorem hasCompactSupport_of_exists_notMem {E : Type*} [Zero E] {F : (Fin d → ℝ) → E}
    (hF : ∀ x, (∃ i, x i ∉ Set.Icc a b) → F x = 0) : HasCompactSupport F :=
  HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc (a := a) (b := b))
    fun x hx => hF x (by simpa only [Set.mem_univ_pi, not_forall] using hx)

/-- **A continuous function vanishing outside a cube lies in every `L_q`**: if `g` is continuous
and `g(x) = 0` whenever some coordinate `x_i` lies outside `[a, b]`, then `g ∈ L_q(ℝ^d)` for every
`q ∈ [0, ∞]`: it is continuous with compact support
(`Daubechies.hasCompactSupport_of_exists_notMem`, Mathlib's
`Continuous.memLp_of_hasCompactSupport`). -/
theorem memLp_of_continuous_of_exists_notMem (hg : Continuous g)
    (hsupp : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0) (q : ℝ≥0∞) : MemLp g q volume :=
  hg.memLp_of_hasCompactSupport (hasCompactSupport_of_exists_notMem hsupp)

/-- **`g_{j,k}` is continuous** if `g` is. -/
theorem continuous_tensorScaled (hg : Continuous g) (j : ℕ) (k : Fin d → ℤ) :
    Continuous (tensorScaled g j k) :=
  continuous_const.mul (hg.comp ((continuous_const_smul _).sub continuous_const))

/-! ### Counting positions -/

/-- **The box of positions at a point**: the positions `k ∈ ℤ^d` with
`⌈2^j x_i - b⌉ ≤ k_i ≤ ⌊2^j x_i - a⌋` for every coordinate `i`. Every window of level `j` that
contains `x` has its position in this box (`Daubechies.mem_tensorBox_of_mem_tensorWindow`). -/
noncomputable def tensorBox (a b : ℝ) (j : ℕ) (x : Fin d → ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌈(2 : ℝ) ^ j * x i - b⌉ ⌊(2 : ℝ) ^ j * x i - a⌋

/-- If `x` lies in the window of level `j` and position `k`, then `k` lies in the box of positions
at `x` (`Daubechies.mem_Icc_ceil_floor` in every coordinate). -/
theorem mem_tensorBox_of_mem_tensorWindow {j : ℕ} {k : Fin d → ℤ} {x : Fin d → ℝ}
    (hx : x ∈ tensorWindow a b j k) : k ∈ tensorBox a b j x :=
  Fintype.mem_piFinset.2 fun i => mem_Icc_ceil_floor (mem_tensorWindow.1 hx i)

/-- **The box has at most `M^d` positions**, `M = ⌈b - a⌉ + 1`: it is a product of `d` integer
intervals with at most `M` elements each (`Daubechies.card_Icc_ceil_floor_le`). -/
theorem card_tensorBox_le (a b : ℝ) (j : ℕ) (x : Fin d → ℝ) :
    (tensorBox a b j x).card ≤ (⌈b - a⌉₊ + 1) ^ d := by
  rw [tensorBox, Fintype.card_piFinset]
  calc ∏ i, (Finset.Icc ⌈(2 : ℝ) ^ j * x i - b⌉ ⌊(2 : ℝ) ^ j * x i - a⌋).card
      ≤ ∏ _i : Fin d, (⌈b - a⌉₊ + 1) :=
        Finset.prod_le_prod fun i _ => card_Icc_ceil_floor_le _ a b
    _ = (⌈b - a⌉₊ + 1) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The overlap number** `|ι| M^d`, `M = ⌈b - a⌉ + 1`, of a family of generators indexed by the
finite type `ι` that vanish outside `[a, b]^d`: the number of generators of one level that can be
nonzero at a point (`Daubechies.card_le_tensorOverlap`). -/
noncomputable def tensorOverlap (ι : Type*) [Fintype ι] (a b : ℝ) (d : ℕ) : ℕ :=
  Fintype.card ι * (⌈b - a⌉₊ + 1) ^ d

/-- **Bounded overlap of the windows of a family**: every point `x` lies in the windows of at most
`|ι| M^d` pairs `(ν, k)` of a generator index and a position of one level `j`: such pairs lie in
`ι × B` with the box `B` of positions at `x` (`Daubechies.card_tensorBox_le`). -/
theorem card_le_tensorOverlap {ι : Type*} [Fintype ι] {j : ℕ} (x : Fin d → ℝ)
    (S : Finset (ι × (Fin d → ℤ))) (hS : ∀ νk ∈ S, x ∈ tensorWindow a b j νk.2) :
    S.card ≤ tensorOverlap ι a b d := by
  calc S.card ≤ (Finset.univ ×ˢ tensorBox a b j x).card :=
        Finset.card_le_card fun νk hνk => Finset.mem_product.2
          ⟨Finset.mem_univ _, mem_tensorBox_of_mem_tensorWindow (hS νk hνk)⟩
    _ ≤ tensorOverlap ι a b d := by
        rw [Finset.card_product, Finset.card_univ, tensorOverlap]
        exact Nat.mul_le_mul_left _ (card_tensorBox_le a b j x)

end Generators

/-! ### Measurability and `L_p` norms of the generators -/

section Norms

variable {g : (Fin d → ℝ) → ℂ}

/-- **Dilation and translation preserve measurability**: for every a.e. strongly measurable
`F : ℝ^d → ℂ`, `j ∈ ℕ` and `t ∈ ℝ^d`, the function `x ↦ F(2^j x - t)` is a.e. strongly measurable,
since translations preserve Lebesgue measure and the dilation `x ↦ 2^j x` is quasi measure
preserving (Mathlib's `MeasureTheory.Measure.quasiMeasurePreserving_smul`). -/
theorem aestronglyMeasurable_comp_two_pow_smul_sub {F : (Fin d → ℝ) → ℂ}
    (hF : AEStronglyMeasurable F volume) (j : ℕ) (t : Fin d → ℝ) :
    AEStronglyMeasurable (fun x => F ((2 : ℝ) ^ j • x - t)) volume :=
  (hF.comp_measurePreserving (measurePreserving_sub_right volume t)).comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul volume (pow_ne_zero j two_ne_zero))

/-- The generators `g_{j,k}` of an a.e. strongly measurable `g` are a.e. strongly measurable
(`Daubechies.aestronglyMeasurable_comp_two_pow_smul_sub`). -/
theorem aestronglyMeasurable_tensorScaled (hg : AEStronglyMeasurable g volume) (j : ℕ)
    (k : Fin d → ℤ) : AEStronglyMeasurable (tensorScaled g j k) volume :=
  (aestronglyMeasurable_comp_two_pow_smul_sub hg j _).const_mul _

/-- **The measure of a dilation**: the image of Lebesgue measure on `ℝ^d` under `x ↦ 2^j x` is
`2^(-jd)` times Lebesgue measure (Mathlib's `MeasureTheory.Measure.map_addHaar_smul`), with the
factor written as the inverse of the dyadic weight `2^(jd)`. -/
theorem map_two_pow_smul_volume (j : ℕ) :
    Measure.map (fun x : Fin d → ℝ => (2 : ℝ) ^ j • x) volume =
      (dyadicWeight d j)⁻¹ • (volume : Measure (Fin d → ℝ)) := by
  rw [Measure.map_addHaar_smul volume (pow_ne_zero j two_ne_zero), finrank_fin_fun,
    abs_of_pos (by positivity), ← pow_mul, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.dyadicWeight_natCast,
    mul_comm j d]

/-- **Dilation and translation in `L_p(ℝ^d)`**: for every a.e. strongly measurable `F`, every
`j ∈ ℕ`, `t ∈ ℝ^d` and every exponent `p`, `‖F(2^j · - t)‖_p = 2^(-jd/p) ‖F‖_p`
(`Daubechies.map_two_pow_smul_volume`; translations preserve Lebesgue measure). For `p = ∞` the
factor is `1`, since then `1/p.toReal = 0` in Lean. -/
theorem eLpNorm_comp_two_pow_smul_sub {F : (Fin d → ℝ) → ℂ} (hF : AEStronglyMeasurable F volume)
    (j : ℕ) (t : Fin d → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => F ((2 : ℝ) ^ j • x - t)) p volume =
      dyadicWeight (-(d / p.toReal)) j * eLpNorm F p volume := by
  have hm : AEStronglyMeasurable (fun u => F (u - t))
      (Measure.map (fun x : Fin d → ℝ => (2 : ℝ) ^ j • x) volume) := by
    rw [map_two_pow_smul_volume]
    exact (hF.comp_measurePreserving (measurePreserving_sub_right volume t)).smul_measure _
  rw [show (fun x => F ((2 : ℝ) ^ j • x - t)) =
      (fun u => F (u - t)) ∘ fun x : Fin d → ℝ => (2 : ℝ) ^ j • x from rfl,
    ← eLpNorm_map_measure hm (measurable_const_smul _).aemeasurable, map_two_pow_smul_volume,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.2 (ENNReal.dyadicWeight_ne_top _ _)),
    smul_eq_mul, show (fun u => F (u - t)) = F ∘ (fun u => u - t) from rfl,
    eLpNorm_comp_measurePreserving hF (measurePreserving_sub_right volume t),
    ← ENNReal.dyadicWeight_neg, ENNReal.dyadicWeight_rpow, ENNReal.toReal_div, ENNReal.toReal_one]
  congr 2
  ring

/-- **`L_p` norms of the generators**: for every a.e. strongly measurable `g`, level `j`, position
`k` and exponent `p`, `‖g_{j,k}‖_p = 2^(jd(1/2 - 1/p)) ‖g‖_p`
(`Daubechies.eLpNorm_comp_two_pow_smul_sub` and the factor `2^(jd/2)`, `enorm_two_rpow_half_pow`).
In particular `‖g_{j,k}‖_2 = ‖g‖_2`. -/
theorem eLpNorm_tensorScaled (hg : AEStronglyMeasurable g volume) (j : ℕ) (k : Fin d → ℤ)
    (p : ℝ≥0∞) :
    eLpNorm (tensorScaled g j k) p volume =
      dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j * eLpNorm g p volume := by
  have h : tensorScaled g j k = ((((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) ^ d) •
      fun x => g ((2 : ℝ) ^ j • x - fun i => (k i : ℝ)) := rfl
  rw [h, eLpNorm_const_smul, eLpNorm_comp_two_pow_smul_sub hg, ← mul_assoc,
    enorm_two_rpow_half_pow, ← ENNReal.dyadicWeight_add]
  congr 2
  ring

/-- **`L_p` norm of a multiple of a generator**: `‖z g_{j,k}‖_p = |z| 2^(jd(1/2 - 1/p)) ‖g‖_p` for
every `z ∈ ℂ` (`Daubechies.eLpNorm_tensorScaled`). -/
theorem eLpNorm_const_mul_tensorScaled (hg : AEStronglyMeasurable g volume) (z : ℂ) (j : ℕ)
    (k : Fin d → ℤ) (p : ℝ≥0∞) :
    eLpNorm (fun x => z * tensorScaled g j k x) p volume =
      ‖z‖ₑ * (dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j * eLpNorm g p volume) := by
  rw [show (fun x => z * tensorScaled g j k x) = z • tensorScaled g j k from rfl,
    eLpNorm_const_smul, eLpNorm_tensorScaled hg]

/-- **`L_{p'}` norms of the generators**: for `1 ≤ p` and the conjugate exponent `p'`,
`‖g_{j,k}‖_{p'} = 2^(-jd(1/2 - 1/p)) ‖g‖_{p'}`, since `1/2 - 1/p' = -(1/2 - 1/p)`
(`Daubechies.eLpNorm_tensorScaled`, `Daubechies.one_div_toReal_conjExponent`). -/
theorem eLpNorm_tensorScaled_conjExponent (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (j : ℕ) (k : Fin d → ℤ) :
    eLpNorm (tensorScaled g j k) (ENNReal.conjExponent p) volume =
      dyadicWeight (-(d * (1 / 2 - 1 / p.toReal))) j *
        eLpNorm g (ENNReal.conjExponent p) volume := by
  rw [eLpNorm_tensorScaled hg, one_div_toReal_conjExponent hp1]
  congr 2
  ring

end Norms

/-! ### Orthonormality at every level -/

section Orthonormality

variable {a b : ℝ}

/-- **Inner products at every level**: for all `g, g' : ℝ^d → ℂ`, every level `j` and all
positions `k, l ∈ ℤ^d`, `∫ g_{j,k} conj g'_{j,l} = ∫ g(x - k) conj g'(x - l) dx`. The integrand is
`2^(jd) F(2^j x)` with `F(u) = g(u - k) conj g'(u - l)` (`ofReal_two_rpow_half_pow_mul_self`), and
the substitution `u = 2^j x` gives the factor `2^(-jd)` (Mathlib's
`MeasureTheory.Measure.integral_comp_smul`). Both sides are `0` when the integrand is not
integrable. -/
theorem integral_tensorScaled_mul_conj (g g' : (Fin d → ℝ) → ℂ) (j : ℕ) (k l : Fin d → ℤ) :
    ∫ x, tensorScaled g j k x * conj (tensorScaled g' j l x) =
      ∫ x, g (x - fun i => (k i : ℝ)) * conj (g' (x - fun i => (l i : ℝ))) := by
  set F : (Fin d → ℝ) → ℂ :=
    fun u => g (u - fun i => (k i : ℝ)) * conj (g' (u - fun i => (l i : ℝ)))
  have h : ∀ x, tensorScaled g j k x * conj (tensorScaled g' j l x) =
      (2 : ℂ) ^ (j * d) * F ((2 : ℝ) ^ j • x) := fun x => by
    simp only [tensorScaled, F, map_mul, map_pow, Complex.conj_ofReal]
    rw [← ofReal_two_rpow_half_pow_mul_self]
    ring
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_smul volume F ((2 : ℝ) ^ j), finrank_fin_fun,
    Complex.real_smul, ← mul_assoc, abs_of_pos (by positivity), pow_mul]
  push_cast
  rw [mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)), one_mul]

/-- **Generators of one level overlap only for nearby positions**: if `g, g'` vanish outside
`[a, b]^d`, then `g_{j,l}(y) conj g'_{j,k}(y) = 0` for every `y` unless `|l_i - k_i| ≤ ⌈b - a⌉`
for every coordinate `i` (`Daubechies.mem_Icc_of_mem_supportWindow`). -/
theorem tensorScaled_mul_conj_eq_zero {g g' : (Fin d → ℝ) → ℂ}
    (hg : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0)
    (hg' : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g' x = 0) {j : ℕ} {k l : Fin d → ℤ}
    (hl : l ∉ Fintype.piFinset fun i => Finset.Icc (k i - ⌈b - a⌉₊) (k i + ⌈b - a⌉₊))
    (y : Fin d → ℝ) : tensorScaled g j l y * conj (tensorScaled g' j k y) = 0 := by
  by_contra h
  obtain ⟨hl', hk'⟩ := mul_ne_zero_iff.1 h
  have h1 := mem_tensorWindow_of_tensorScaled_ne_zero hg hl'
  have h2 := mem_tensorWindow_of_tensorScaled_ne_zero hg' fun h0 => hk' (by rw [h0, map_zero])
  exact hl (Fintype.mem_piFinset.2 fun i =>
    mem_Icc_of_mem_supportWindow (h1 i (Set.mem_univ i)) (h2 i (Set.mem_univ i)))

/-- If `g, g'` are continuous and `g` vanishes outside `[a, b]^d`, then
`y ↦ g_{j,l}(y) conj g'_{j,k}(y)` is integrable: it is continuous with compact support. -/
theorem integrable_tensorScaled_mul_conj {g g' : (Fin d → ℝ) → ℂ} (hg : Continuous g)
    (hg' : Continuous g') (hsupp : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0) (j : ℕ)
    (k l : Fin d → ℤ) : Integrable fun y => tensorScaled g j l y * conj (tensorScaled g' j k y) :=
  ((continuous_tensorScaled hg j l).mul (Complex.continuous_conj.comp
    (continuous_tensorScaled hg' j k))).integrable_of_hasCompactSupport
    (hasCompactSupport_tensorScaled hsupp j l).mul_right

end Orthonormality

/-! ### Expansions and coefficients -/

section Expansions

variable {ι : Type*}

/-- **The expansion of level `j`** `∑_{(ν,k) ∈ ι × ℤ^d} c_{ν,k} G_{ν,j,k}(x)` in a family of
generators `G_ν`, `ν ∈ ι`, with coefficients `c : ι × ℤ^d → ℂ`. For a finite family of generators
that vanish outside a cube, only finitely many terms are nonzero at each point
(`Daubechies.tensorExpand_eq_sum`), so the sum is meaningful for every coefficient family. -/
noncomputable def tensorExpand (G : ι → (Fin d → ℝ) → ℂ) (j : ℕ) (c : ι × (Fin d → ℤ) → ℂ)
    (x : Fin d → ℝ) : ℂ :=
  ∑' νk : ι × (Fin d → ℤ), c νk * tensorScaled (G νk.1) j νk.2 x

/-- **The coefficient functional** `⟨f, G_{ν,j,k}⟩ = ∫ f(y) conj G_{ν,j,k}(y) dy` of level `j`,
generator `ν` and position `k`. For orthonormal integer translates it recovers the coefficients of
an expansion (`Daubechies.tensorCoeff_tensorExpand`). -/
noncomputable def tensorCoeff (G : ι → (Fin d → ℝ) → ℂ) (j : ℕ) (f : (Fin d → ℝ) → ℂ)
    (νk : ι × (Fin d → ℤ)) : ℂ :=
  ∫ y, f y * conj (tensorScaled (G νk.1) j νk.2 y)

variable [Fintype ι] {G : ι → (Fin d → ℝ) → ℂ} {a b : ℝ}

/-- **Expansions are finite sums**: if every `G_ν` vanishes outside `[a, b]^d`, then for every
level `j`, coefficients `c` and point `x`, the expansion at `x` is the sum over the generators and
the positions in the box at `x` (`Daubechies.tensorBox`). -/
theorem tensorExpand_eq_sum (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) (j : ℕ)
    (c : ι × (Fin d → ℤ) → ℂ) (x : Fin d → ℝ) :
    tensorExpand G j c x =
      ∑ νk ∈ Finset.univ ×ˢ tensorBox a b j x, c νk * tensorScaled (G νk.1) j νk.2 x :=
  tsum_eq_sum fun νk hνk => by
    rw [tensorScaled_eq_zero (hsupp νk.1) fun hx => hνk (Finset.mem_product.2
      ⟨Finset.mem_univ _, mem_tensorBox_of_mem_tensorWindow hx⟩), mul_zero]

/-- The series of an expansion converges at every point, if every `G_ν` vanishes outside
`[a, b]^d`: only finitely many terms are nonzero (`Daubechies.tensorExpand_eq_sum`). -/
theorem summable_tensorExpand (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) (j : ℕ)
    (c : ι × (Fin d → ℤ) → ℂ) (x : Fin d → ℝ) :
    Summable fun νk : ι × (Fin d → ℤ) => c νk * tensorScaled (G νk.1) j νk.2 x :=
  summable_of_ne_finset_zero (s := Finset.univ ×ˢ tensorBox a b j x) fun νk hνk => by
    rw [tensorScaled_eq_zero (hsupp νk.1) fun hx => hνk (Finset.mem_product.2
      ⟨Finset.mem_univ _, mem_tensorBox_of_mem_tensorWindow hx⟩), mul_zero]

/-- **Expansions are continuous**: if every `G_ν` is continuous and vanishes outside `[a, b]^d`,
then `x ↦ ∑ c_{ν,k} G_{ν,j,k}(x)` is continuous for every level `j` and all coefficients `c`.
Near a point `x`, at all `y` with `|2^j y_i - 2^j x_i| < 1` for every `i`, the expansion is the
same finite sum over the generators and the box at `x` for `[a - 1, b + 1]`. -/
theorem continuous_tensorExpand (hG : ∀ ν, Continuous (G ν))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) (j : ℕ) (c : ι × (Fin d → ℤ) → ℂ) :
    Continuous (tensorExpand G j c) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hU : ∀ᶠ y in 𝓝 x, ∀ i,
      (2 : ℝ) ^ j * y i ∈ Set.Ioo ((2 : ℝ) ^ j * x i - 1) (2 ^ j * x i + 1) :=
    eventually_all.2 fun i =>
      (show Continuous fun y : Fin d → ℝ => (2 : ℝ) ^ j * y i from
        continuous_const.mul (continuous_apply i)).continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (by linarith) (by linarith))
  have hev : (fun y => ∑ νk ∈ Finset.univ ×ˢ tensorBox (a - 1) (b + 1) j x,
      c νk * tensorScaled (G νk.1) j νk.2 y) =ᶠ[𝓝 x] tensorExpand G j c := by
    filter_upwards [hU] with y hy
    refine (tsum_eq_sum fun νk hνk => ?_).symm
    refine by_contra fun h => hνk (Finset.mem_product.2 ⟨Finset.mem_univ _,
      mem_tensorBox_of_mem_tensorWindow (mem_tensorWindow.2 fun i => ?_)⟩)
    have hmem := mem_tensorWindow.1
      (mem_tensorWindow_of_tensorScaled_ne_zero (hsupp νk.1) (right_ne_zero_of_mul h)) i
    exact ⟨by linarith [hmem.1, (hy i).2], by linarith [hmem.2, (hy i).1]⟩
  exact ((continuous_finsetSum _ fun νk _ =>
    continuous_const.mul (continuous_tensorScaled (hG νk.1) j νk.2)).continuousAt).congr hev

/-- **Expansions are a.e. strongly measurable** for a.e. strongly measurable generators and all
coefficients: a countable sum of a.e. strongly measurable functions (Mathlib's
`MeasureTheory.AEStronglyMeasurable.tsum`). -/
theorem aestronglyMeasurable_tensorExpand (hG : ∀ ν, AEStronglyMeasurable (G ν) volume) (j : ℕ)
    (c : ι × (Fin d → ℤ) → ℂ) : AEStronglyMeasurable (tensorExpand G j c) volume :=
  AEStronglyMeasurable.tsum fun νk =>
    (aestronglyMeasurable_tensorScaled (hG νk.1) j νk.2).const_mul (c νk)

/-- **Coefficients of an expansion with respect to a second family**: let the generators `G_ν`,
`ν ∈ ι`, and `G'_μ`, `μ ∈ ι'`, be continuous and vanish outside `[a, b]^d`. Then for every level
`j`, every coefficient family `c` and every `(μ, k)`, the coefficient
`⟨∑ c_{ν,l} G_{ν,j,l}, G'_{μ,j,k}⟩` is the finite sum of
`c_{ν,l} ∫ G_ν(x - l) conj G'_μ(x - k) dx` over all `ν` and the positions `l` with
`|l_i - k_i| ≤ ⌈b - a⌉`. Only these terms meet `G'_{μ,j,k}`
(`Daubechies.tensorScaled_mul_conj_eq_zero`), and the inner products at level `j` are those at
level `0` (`Daubechies.integral_tensorScaled_mul_conj`). -/
theorem tensorCoeff_tensorExpand_eq_sum {ι' : Type*} {G' : ι' → (Fin d → ℝ) → ℂ}
    (hG : ∀ ν, Continuous (G ν)) (hG' : ∀ μ, Continuous (G' μ))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0)
    (hsupp' : ∀ μ x, (∃ i, x i ∉ Set.Icc a b) → G' μ x = 0)
    (j : ℕ) (c : ι × (Fin d → ℤ) → ℂ) (μ : ι') (k : Fin d → ℤ) :
    tensorCoeff G' j (tensorExpand G j c) (μ, k) = ∑ νl ∈ Finset.univ ×ˢ
        (Fintype.piFinset fun i => Finset.Icc (k i - ⌈b - a⌉₊) (k i + ⌈b - a⌉₊)),
      c νl * ∫ x, G νl.1 (x - fun i => (νl.2 i : ℝ)) * conj (G' μ (x - fun i => (k i : ℝ))) := by
  set s : Finset (ι × (Fin d → ℤ)) := Finset.univ ×ˢ
    Fintype.piFinset fun i => Finset.Icc (k i - ⌈b - a⌉₊) (k i + ⌈b - a⌉₊)
  have h : ∀ y, tensorExpand G j c y * conj (tensorScaled (G' μ) j k y) =
      ∑ νl ∈ s, c νl * (tensorScaled (G νl.1) j νl.2 y * conj (tensorScaled (G' μ) j k y)) :=
    fun y => by
      rw [tensorExpand, ← tsum_mul_right]
      refine (tsum_eq_sum fun νl hνl => ?_).trans
        (Finset.sum_congr rfl fun νl _ => mul_assoc _ _ _)
      rw [mul_assoc, tensorScaled_mul_conj_eq_zero (hsupp νl.1) (hsupp' μ)
        (fun hl => hνl (Finset.mem_product.2 ⟨Finset.mem_univ _, hl⟩)), mul_zero]
  rw [tensorCoeff]
  simp_rw [h]
  rw [integral_finsetSum _ fun νl _ =>
    (integrable_tensorScaled_mul_conj (hG νl.1) (hG' μ) (hsupp νl.1) j k νl.2).const_mul _]
  simp_rw [integral_const_mul, integral_tensorScaled_mul_conj]

/-- **Coefficient recovery**: let every `G_ν` be continuous and vanish outside `[a, b]^d`, and let
the integer translates be orthonormal,
`∫ G_ν(x - k) conj G_{ν'}(x - l) dx = 1` if `ν = ν'` and `k = l`, and `0` otherwise. Then for
every level `j`, every coefficient family `c` and every `(ν, k)`,
`⟨∑ c_{ν',l} G_{ν',j,l}, G_{ν,j,k}⟩ = c_{ν,k}`: of the finite sum of
`Daubechies.tensorCoeff_tensorExpand_eq_sum` only the term `(ν', l) = (ν, k)` remains. -/
theorem tensorCoeff_tensorExpand [DecidableEq ι] (hG : ∀ ν, Continuous (G ν))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0)
    (horth : ∀ ν ν' (k l : Fin d → ℤ),
      ∫ x, G ν (x - fun i => (k i : ℝ)) * conj (G ν' (x - fun i => (l i : ℝ))) =
        if ν = ν' ∧ k = l then 1 else 0)
    (j : ℕ) (c : ι × (Fin d → ℤ) → ℂ) (νk : ι × (Fin d → ℤ)) :
    tensorCoeff G j (tensorExpand G j c) νk = c νk := by
  obtain ⟨ν, k⟩ := νk
  have hcond : ∀ νl : ι × (Fin d → ℤ), (νl.1 = ν ∧ νl.2 = k) ↔ νl = (ν, k) := fun νl => by
    rw [Prod.ext_iff]
  rw [tensorCoeff_tensorExpand_eq_sum hG hG hsupp hsupp j c ν k]
  simp_rw [horth, hcond, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_product.2 ⟨Finset.mem_univ _,
    Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2
      ⟨by change k i - (⌈b - a⌉₊ : ℤ) ≤ k i; omega,
        by change k i ≤ k i + (⌈b - a⌉₊ : ℤ); omega⟩⟩)

/-- **Coefficients of an expansion in an orthogonal family**: let the generators `G_ν`, `ν ∈ ι`,
and `G'_μ`, `μ ∈ ι'`, be continuous and vanish outside `[a, b]^d`, and let every integer
translate of every `G_ν` be orthogonal to every integer translate of every `G'_μ`. Then the
coefficients `⟨∑ c_{ν,l} G_{ν,j,l}, G'_{μ,j,k}⟩` of every expansion of level `j` in the `G_ν`
with respect to the `G'_μ` vanish: every term of the finite sum of
`Daubechies.tensorCoeff_tensorExpand_eq_sum` vanishes. -/
theorem tensorCoeff_tensorExpand_eq_zero {ι' : Type*} {G' : ι' → (Fin d → ℝ) → ℂ}
    (hG : ∀ ν, Continuous (G ν)) (hG' : ∀ μ, Continuous (G' μ))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0)
    (hsupp' : ∀ μ x, (∃ i, x i ∉ Set.Icc a b) → G' μ x = 0)
    (horth : ∀ ν μ (k l : Fin d → ℤ),
      ∫ x, G ν (x - fun i => (k i : ℝ)) * conj (G' μ (x - fun i => (l i : ℝ))) = 0)
    (j : ℕ) (c : ι × (Fin d → ℤ) → ℂ) (μk : ι' × (Fin d → ℤ)) :
    tensorCoeff G' j (tensorExpand G j c) μk = 0 := by
  obtain ⟨μ, k⟩ := μk
  rw [tensorCoeff_tensorExpand_eq_sum hG hG' hsupp hsupp' j c μ k]
  simp_rw [horth, mul_zero, Finset.sum_const_zero]

/-! ### The coefficient estimate -/

/-- **Hölder's inequality on a window**: let `g` be a.e. strongly measurable and vanish outside
`[a, b]^d`, let `1 ≤ p`, and let `f` be a.e. strongly measurable. Then
`‖f conj g_{j,k}‖_1 ≤ ‖1_W f‖_p ‖g_{j,k}‖_{p'}` with the window `W` of level `j` and position `k`
and the conjugate exponent `p'`, since `g_{j,k}` vanishes outside `W`
(`MeasureTheory.eLpNorm_mul_conj_le_of_forall_notMem`). -/
theorem eLpNorm_mul_conj_tensorScaled_le {g : (Fin d → ℝ) → ℂ} (hg : AEStronglyMeasurable g volume)
    (hsupp : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume) (j : ℕ) (k : Fin d → ℤ) :
    eLpNorm (fun y => f y * conj (tensorScaled g j k y)) 1 volume ≤
      eLpNorm ((tensorWindow a b j k).indicator f) p volume *
        eLpNorm (tensorScaled g j k) (ENNReal.conjExponent p) volume :=
  eLpNorm_mul_conj_le_of_forall_notMem (measurableSet_tensorWindow a b j k)
    (aestronglyMeasurable_tensorScaled hg j k) (fun _ hy => tensorScaled_eq_zero hsupp hy) hp1 hf

omit [Fintype ι] in
/-- **A single coefficient**: under the hypotheses of
`Daubechies.eLpNorm_mul_conj_tensorScaled_le` for every generator,
`|⟨f, G_{ν,j,k}⟩| ≤ ‖1_W f‖_p ‖G_{ν,j,k}‖_{p'}` with the window `W` of level `j` and position `k`,
since `|∫ h| ≤ ‖h‖_1`. -/
theorem enorm_tensorCoeff_le (hG : ∀ ν, AEStronglyMeasurable (G ν) volume)
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume) (j : ℕ) (νk : ι × (Fin d → ℤ)) :
    ‖tensorCoeff G j f νk‖ₑ ≤ eLpNorm ((tensorWindow a b j νk.2).indicator f) p volume *
      eLpNorm (tensorScaled (G νk.1) j νk.2) (ENNReal.conjExponent p) volume := by
  have hm : AEStronglyMeasurable (fun y => f y * conj (tensorScaled (G νk.1) j νk.2 y)) volume :=
    hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable
      (aestronglyMeasurable_tensorScaled (hG νk.1) j νk.2))
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq_of_le ?_
    (eLpNorm_mul_conj_tensorScaled_le (hG νk.1) (hsupp νk.1) hp1 hf j νk.2))
  rw [eLpNorm_one_eq_lintegral_enorm hm]

/-- **Summing local bounds over the windows**: let `0 < p < ∞`, let `f` be a.e. strongly
measurable, and let `w : ι × ℤ^d → [0, ∞]` satisfy `w_{ν,k} ≤ ‖1_{W_k} f‖_p B` for every `(ν, k)`,
where `W_k` are the windows of level `j`. Then `‖w‖_{ℓ_p} ≤ L^(1/p) B ‖f‖_p` with the overlap
number `L = |ι| M^d`: every point lies in the windows of at most `L` pairs `(ν, k)`
(`Daubechies.card_le_tensorOverlap`), so the window inequality in `ℓ_p` form
(`MeasureTheory.lqNorm_le_mul_eLpNorm_of_overlap`) applies. -/
theorem lqNorm_le_of_le_eLpNorm_tensorWindow [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : (Fin d → ℝ) → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) {w : ι × (Fin d → ℤ) → ℝ≥0∞} {B : ℝ≥0∞}
    (hw : ∀ νk, w νk ≤ eLpNorm ((tensorWindow a b j νk.2).indicator f) p volume * B) :
    lqNorm p w ≤ (tensorOverlap ι a b d : ℝ≥0∞) ^ (1 / p.toReal) * B * eLpNorm f p volume :=
  lqNorm_le_mul_eLpNorm_of_overlap (W := fun νk : ι × (Fin d → ℤ) => tensorWindow a b j νk.2)
    (fun νk => measurableSet_tensorWindow a b j νk.2) (fun x S hS => card_le_tensorOverlap x S hS)
    hp0 hp hf hw

/-- **The coefficient estimate**: let every `G_ν` be a.e. strongly measurable and vanish outside
`[a, b]^d`, let `‖G_ν‖_{p'} ≤ B` for the conjugate exponent `p'`, and let `1 ≤ p < ∞`. Then for
every a.e. strongly measurable `f` and every level `j`,
`‖(⟨f, G_{ν,j,k}⟩)_{ν,k}‖_{ℓ_p} ≤ L^(1/p) B 2^(-jd(1/2 - 1/p)) ‖f‖_p` with the overlap number
`L = |ι| M^d`. Each coefficient is bounded by Hölder's inequality on its window
(`Daubechies.enorm_tensorCoeff_le`) with `‖G_{ν,j,k}‖_{p'} = 2^(-jd(1/2 - 1/p)) ‖G_ν‖_{p'}`
(`Daubechies.eLpNorm_tensorScaled_conjExponent`), and the windows overlap at most `L` times
(`Daubechies.lqNorm_le_of_le_eLpNorm_tensorWindow`). -/
theorem lqNorm_tensorCoeff_le [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hG : ∀ ν, AEStronglyMeasurable (G ν) volume)
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {B : ℝ≥0∞} (hB : ∀ ν, eLpNorm (G ν) (ENNReal.conjExponent p) volume ≤ B)
    {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    lqNorm p (fun νk => ‖tensorCoeff G j f νk‖ₑ) ≤
      (tensorOverlap ι a b d : ℝ≥0∞) ^ (1 / p.toReal) * B *
        dyadicWeight (-(d * (1 / 2 - 1 / p.toReal))) j * eLpNorm f p volume := by
  have h := lqNorm_le_of_le_eLpNorm_tensorWindow (a := a) (b := b)
    (zero_lt_one.trans_le hp1).ne' hp hf j
    (w := fun νk => ‖tensorCoeff G j f νk‖ₑ)
    (B := dyadicWeight (-(d * (1 / 2 - 1 / p.toReal))) j * B) fun νk => by
      refine (enorm_tensorCoeff_le hG hsupp hp1 hf j νk).trans ?_
      rw [eLpNorm_tensorScaled_conjExponent (hG νk.1) hp1]
      gcongr
      exact hB _
  refine h.trans (le_of_eq ?_)
  ring

/-- **The constant of the coefficient estimate**: `L^(1/p) sup_ν ‖G_ν‖_{p'}` with the overlap
number `L = |ι| M^d` (`Daubechies.tensorOverlap`) and the conjugate exponent `p'`. It is the same
for every level. -/
noncomputable def tensorCoeffConst (G : ι → (Fin d → ℝ) → ℂ) (a b : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  (tensorOverlap ι a b d : ℝ≥0∞) ^ (1 / p.toReal) *
    ⨆ ν, eLpNorm (G ν) (ENNReal.conjExponent p) volume

/-- The constant of the coefficient estimate is finite if every `G_ν` lies in `L_{p'}`. -/
theorem tensorCoeffConst_ne_top (a b : ℝ) {p : ℝ≥0∞}
    (hG : ∀ ν, MemLp (G ν) (ENNReal.conjExponent p) volume) : tensorCoeffConst G a b p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _))
    (iSup_ne_top fun ν => (hG ν).eLpNorm_ne_top)

/-- **The coefficient estimate, weighted form**:
`2^(jd(1/2 - 1/p)) ‖(⟨f, G_{ν,j,k}⟩)_{ν,k}‖_{ℓ_p} ≤ C' ‖f‖_p` with `C' = tensorCoeffConst G a b p`,
under the hypotheses of `Daubechies.lqNorm_tensorCoeff_le`, since the dyadic weights cancel. -/
theorem dyadicWeight_mul_lqNorm_tensorCoeff_le [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hG : ∀ ν, AEStronglyMeasurable (G ν) volume)
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j *
        lqNorm p (fun νk => ‖tensorCoeff G j f νk‖ₑ) ≤
      tensorCoeffConst G a b p * eLpNorm f p volume := by
  have h := lqNorm_tensorCoeff_le hG hsupp hp1 hp
    (fun ν => le_iSup (fun ν => eLpNorm (G ν) (ENNReal.conjExponent p) volume) ν) hf j
  calc dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j *
        lqNorm p (fun νk => ‖tensorCoeff G j f νk‖ₑ)
      ≤ dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j * (tensorCoeffConst G a b p *
          dyadicWeight (-(d * (1 / 2 - 1 / p.toReal))) j * eLpNorm f p volume) := by
        gcongr
        exact h.trans_eq (by rw [tensorCoeffConst, mul_assoc])
    _ = tensorCoeffConst G a b p * eLpNorm f p volume *
          (dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j *
            dyadicWeight (-(d * (1 / 2 - 1 / p.toReal))) j) := by ring
    _ = tensorCoeffConst G a b p * eLpNorm f p volume := by
        rw [ENNReal.dyadicWeight_mul_neg_self, mul_one]

end Expansions

/-! ### Upper and lower stability -/

section Stability

variable {ι : Type*} [Fintype ι] {G : ι → (Fin d → ℝ) → ℂ} {a b : ℝ}

/-- **Upper stability of the expansions**: let every `G_ν` be a.e. strongly measurable and
vanish outside `[a, b]^d`, let `‖G_ν‖_p ≤ B` for every `ν`, and let `1 ≤ p < ∞`. Then for every
level `j` and all coefficients `c`,
`‖∑ c_{ν,k} G_{ν,j,k}‖_p ≤ L^(1 - 1/p) B 2^(jd(1/2 - 1/p)) ‖c‖_{ℓ_p}` with the overlap number
`L = |ι| M^d`, `M = ⌈b - a⌉ + 1`. At each point at most `L` terms are nonzero
(`Daubechies.card_le_tensorOverlap`), so the bounded overlap inequality
`‖∑ F_n‖_p^p ≤ L^(p-1) ∑ ‖F_n‖_p^p` (`Rd.eLpNorm_rpow_le_of_overlap`) applies, and
`‖c_{ν,k} G_{ν,j,k}‖_p = |c_{ν,k}| 2^(jd(1/2 - 1/p)) ‖G_ν‖_p`
(`Daubechies.eLpNorm_const_mul_tensorScaled`). -/
theorem eLpNorm_tensorExpand_le [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hG : ∀ ν, AEStronglyMeasurable (G ν) volume)
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {B : ℝ≥0∞} (hB : ∀ ν, eLpNorm (G ν) p volume ≤ B) (j : ℕ) (c : ι × (Fin d → ℤ) → ℂ) :
    eLpNorm (tensorExpand G j c) p volume ≤
      (tensorOverlap ι a b d : ℝ≥0∞) ^ (1 - 1 / p.toReal) * B *
        dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j * lqNorm p (fun νk => ‖c νk‖ₑ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set W := dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j
  have h := Rd.eLpNorm_rpow_le_of_overlap (μ := volume) hp1 hp
    (g := fun νk x => c νk * tensorScaled (G νk.1) j νk.2 x)
    (fun νk => (aestronglyMeasurable_tensorScaled (hG νk.1) j νk.2).const_mul (c νk))
    (N := tensorOverlap ι a b d)
    (fun x S hS => card_le_tensorOverlap x S fun νk hνk =>
      mem_tensorWindow_of_tensorScaled_ne_zero (hsupp νk.1) (right_ne_zero_of_mul (hS νk hνk)))
    (aestronglyMeasurable_tensorExpand hG j c) (Eventually.of_forall fun x => rfl)
  have hterm : ∀ νk : ι × (Fin d → ℤ),
      eLpNorm (fun x => c νk * tensorScaled (G νk.1) j νk.2 x) p volume ^ p.toReal ≤
        (W * B) ^ p.toReal * ‖c νk‖ₑ ^ p.toReal := fun νk => by
    rw [eLpNorm_const_mul_tensorScaled (hG νk.1), mul_comm, ENNReal.mul_rpow_of_nonneg _ _ hr.le]
    gcongr
    exact hB _
  have he : (1 - 1 / p.toReal) * p.toReal = p.toReal - 1 := by field_simp
  rw [← ENNReal.rpow_le_rpow_iff hr]
  calc eLpNorm (tensorExpand G j c) p volume ^ p.toReal
      ≤ (tensorOverlap ι a b d : ℝ≥0∞) ^ (p.toReal - 1) * ∑' νk : ι × (Fin d → ℤ),
          eLpNorm (fun x => c νk * tensorScaled (G νk.1) j νk.2 x) p volume ^ p.toReal := h
    _ ≤ (tensorOverlap ι a b d : ℝ≥0∞) ^ (p.toReal - 1) * ∑' νk : ι × (Fin d → ℤ),
          (W * B) ^ p.toReal * ‖c νk‖ₑ ^ p.toReal :=
        mul_le_mul_right (ENNReal.tsum_le_tsum hterm) _
    _ = ((tensorOverlap ι a b d : ℝ≥0∞) ^ (1 - 1 / p.toReal) * B * W *
          lqNorm p (fun νk => ‖c νk‖ₑ)) ^ p.toReal := by
        rw [ENNReal.tsum_mul_left, ← ENNReal.lqNorm_rpow hp0 hp (fun νk => ‖c νk‖ₑ)]
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, he]
        ring

/-- **The constant of the upper estimate**: `L^(1 - 1/p) sup_ν ‖G_ν‖_p` with the overlap number
`L = |ι| M^d` (`Daubechies.tensorOverlap`). It is the same for every level. -/
noncomputable def tensorExpandConst (G : ι → (Fin d → ℝ) → ℂ) (a b : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  (tensorOverlap ι a b d : ℝ≥0∞) ^ (1 - 1 / p.toReal) * ⨆ ν, eLpNorm (G ν) p volume

/-- The constant of the upper estimate is finite for `1 ≤ p` if every `G_ν` lies in `L_p`; the
exponent `1 - 1/p` is then nonnegative (`Rd.one_sub_one_div_toReal_nonneg`). -/
theorem tensorExpandConst_ne_top (a b : ℝ) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hG : ∀ ν, MemLp (G ν) p volume) : tensorExpandConst G a b p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (Rd.one_sub_one_div_toReal_nonneg hp1)
    (ENNReal.natCast_ne_top _)) (iSup_ne_top fun ν => (hG ν).eLpNorm_ne_top)

/-- **Expansions with `ℓ_p` coefficients lie in `L_p`**: if every `G_ν ∈ L_p` vanishes outside
`[a, b]^d`, `1 ≤ p < ∞` and `‖c‖_{ℓ_p} < ∞`, then `∑ c_{ν,k} G_{ν,j,k} ∈ L_p` for every level `j`
(`Daubechies.eLpNorm_tensorExpand_le`). -/
theorem memLp_tensorExpand [MeasurableSpace ι] [MeasurableSingletonClass ι] {p : ℝ≥0∞}
    (hG : ∀ ν, MemLp (G ν) p volume) (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0)
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (j : ℕ) {c : ι × (Fin d → ℤ) → ℂ}
    (hc : lqNorm p (fun νk => ‖c νk‖ₑ) < ∞) : MemLp (tensorExpand G j c) p volume := by
  refine memLp_iff.2 ((eLpNorm_tensorExpand_le (fun ν => (hG ν).aestronglyMeasurable) hsupp hp1
    hp (fun ν => le_iSup (fun ν => eLpNorm (G ν) p volume) ν) j c).trans_lt ?_)
  have hC := tensorExpandConst_ne_top (G := G) a b hp1 hG
  rw [tensorExpandConst] at hC
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hC.lt_top (ENNReal.dyadicWeight_lt_top _ _)) hc

/-- **Lower stability of the expansions**: let every `G_ν` be continuous and vanish outside
`[a, b]^d`, let the integer translates be orthonormal (as in `Daubechies.tensorCoeff_tensorExpand`),
and let `1 ≤ p < ∞`. Then for every level `j` and all coefficients `c`,
`2^(jd(1/2 - 1/p)) ‖c‖_{ℓ_p} ≤ C' ‖∑ c_{ν,k} G_{ν,j,k}‖_p` with `C' = tensorCoeffConst G a b p`:
the coefficients are recovered from the expansion (`Daubechies.tensorCoeff_tensorExpand`), and the
coefficient estimate (`Daubechies.dyadicWeight_mul_lqNorm_tensorCoeff_le`) applies to it. -/
theorem lqNorm_le_eLpNorm_tensorExpand [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [DecidableEq ι] (hG : ∀ ν, Continuous (G ν))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0)
    (horth : ∀ ν ν' (k l : Fin d → ℤ),
      ∫ x, G ν (x - fun i => (k i : ℝ)) * conj (G ν' (x - fun i => (l i : ℝ))) =
        if ν = ν' ∧ k = l then 1 else 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (j : ℕ) (c : ι × (Fin d → ℤ) → ℂ) :
    dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j * lqNorm p (fun νk => ‖c νk‖ₑ) ≤
      tensorCoeffConst G a b p * eLpNorm (tensorExpand G j c) p volume := by
  have h := dyadicWeight_mul_lqNorm_tensorCoeff_le (fun ν => (hG ν).aestronglyMeasurable) hsupp
    hp1 hp (aestronglyMeasurable_tensorExpand (fun ν => (hG ν).aestronglyMeasurable) j c) j
  simp only [tensorCoeff_tensorExpand hG hsupp horth] at h
  exact h

/-- **The expansion of the coefficients is bounded on `L_p`, uniformly in the level**: if every
`G_ν` is a.e. strongly measurable and vanishes outside `[a, b]^d` and `1 ≤ p < ∞`, then for
every a.e. strongly measurable `f` and every level `j`,
`‖∑ ⟨f, G_{ν,j,k}⟩ G_{ν,j,k}‖_p ≤ C C' ‖f‖_p` with `C = tensorExpandConst G a b p` and
`C' = tensorCoeffConst G a b p`: the upper estimate (`Daubechies.eLpNorm_tensorExpand_le`) and
the coefficient estimate (`Daubechies.dyadicWeight_mul_lqNorm_tensorCoeff_le`), whose dyadic
weights cancel. The proof uses the `ℓ_p` norms for the discrete σ-algebra on `ι`, so no
measurable structure on `ι` is assumed. -/
theorem eLpNorm_tensorExpand_tensorCoeff_le (hG : ∀ ν, AEStronglyMeasurable (G ν) volume)
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    eLpNorm (tensorExpand G j (tensorCoeff G j f)) p volume ≤
      tensorExpandConst G a b p * tensorCoeffConst G a b p * eLpNorm f p volume := by
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  calc eLpNorm (tensorExpand G j (tensorCoeff G j f)) p volume
      ≤ tensorExpandConst G a b p * (dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j *
          lqNorm p (fun νk => ‖tensorCoeff G j f νk‖ₑ)) :=
        (eLpNorm_tensorExpand_le hG hsupp hp1 hp
          (fun ν => le_iSup (fun ν => eLpNorm (G ν) p volume) ν) j _).trans_eq
          (by rw [tensorExpandConst]; ring)
    _ ≤ tensorExpandConst G a b p * (tensorCoeffConst G a b p * eLpNorm f p volume) :=
        mul_le_mul_right (dyadicWeight_mul_lqNorm_tensorCoeff_le hG hsupp hp1 hp hf j) _
    _ = tensorExpandConst G a b p * tensorCoeffConst G a b p * eLpNorm f p volume :=
        (mul_assoc _ _ _).symm

/-- **The expansion of the coefficients of an `L_p` function lies in `L_p`**: if every `G_ν` is
continuous and vanishes outside `[a, b]^d`, `1 ≤ p < ∞` and `f ∈ L_p`, then
`∑ ⟨f, G_{ν,j,k}⟩ G_{ν,j,k} ∈ L_p` for every level `j`
(`Daubechies.eLpNorm_tensorExpand_tensorCoeff_le`); the constants are finite since every `G_ν`
lies in `L_p` and `L_{p'}` (`Daubechies.memLp_of_continuous_of_exists_notMem`). -/
theorem memLp_tensorExpand_tensorCoeff (hG : ∀ ν, Continuous (G ν))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : MemLp f p volume) (j : ℕ) :
    MemLp (tensorExpand G j (tensorCoeff G j f)) p volume := by
  have hGp : ∀ q, ∀ ν, MemLp (G ν) q volume := fun q ν =>
    memLp_of_continuous_of_exists_notMem (hG ν) (hsupp ν) q
  exact memLp_iff.2 ((eLpNorm_tensorExpand_tensorCoeff_le (fun ν => (hG ν).aestronglyMeasurable)
    hsupp hp1 hp hf.aestronglyMeasurable j).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (tensorExpandConst_ne_top a b hp1 (hGp p)).lt_top
      (tensorCoeffConst_ne_top a b (hGp _)).lt_top) hf.eLpNorm_lt_top))

end Stability

/-! ### Linearity -/

section Linearity

variable {ι : Type*} [Fintype ι] {G : ι → (Fin d → ℝ) → ℂ} {a b : ℝ}

/-- **Expansions are additive in the coefficients**: if every `G_ν` vanishes outside `[a, b]^d`,
then `∑ (c + c')_{ν,k} G_{ν,j,k}(x) = ∑ c_{ν,k} G_{ν,j,k}(x) + ∑ c'_{ν,k} G_{ν,j,k}(x)` at every
point `x`; all sums are finite (`Daubechies.summable_tensorExpand`). -/
theorem tensorExpand_add (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) (j : ℕ)
    (c c' : ι × (Fin d → ℤ) → ℂ) (x : Fin d → ℝ) :
    tensorExpand G j (fun νk => c νk + c' νk) x = tensorExpand G j c x + tensorExpand G j c' x := by
  simp only [tensorExpand, add_mul]
  exact (summable_tensorExpand hsupp j c x).tsum_add (summable_tensorExpand hsupp j c' x)

omit [Fintype ι] in
/-- **Expansions are homogeneous in the coefficients**:
`∑ (z c_{ν,k}) G_{ν,j,k}(x) = z ∑ c_{ν,k} G_{ν,j,k}(x)` for every `z ∈ ℂ` and every point `x`. -/
theorem tensorExpand_const_mul (j : ℕ) (z : ℂ) (c : ι × (Fin d → ℤ) → ℂ) (x : Fin d → ℝ) :
    tensorExpand G j (fun νk => z * c νk) x = z * tensorExpand G j c x := by
  simp only [tensorExpand, mul_assoc]
  exact tsum_mul_left

omit [Fintype ι] in
/-- **The expansion of the zero coefficients is zero**: for every level `j`, the expansion of the
coefficient family that is `0` everywhere vanishes at every point; every term of the sum is `0`
(Mathlib's `tsum_zero`). -/
theorem tensorExpand_zero (j : ℕ) : tensorExpand G j 0 = 0 := by
  funext x
  simp [tensorExpand]

omit [Fintype ι] in
/-- **The expansion of a single coefficient**: for every level `j` and every `(ν, k)`, the
expansion of the coefficient family that is `1` at `(ν, k)` and `0` elsewhere is the generator
`G_{ν,j,k}` itself; only one term of the sum is nonzero (Mathlib's `tsum_eq_single`). -/
theorem tensorExpand_single [DecidableEq ι] (j : ℕ) (νk : ι × (Fin d → ℤ)) :
    tensorExpand G j (Pi.single νk 1) = tensorScaled (G νk.1) j νk.2 := by
  funext x
  rw [tensorExpand, tsum_eq_single νk fun μk hμk => by rw [Pi.single_eq_of_ne hμk, zero_mul],
    Pi.single_eq_same, one_mul]

omit [Fintype ι] in
/-- **The coefficients depend only on the class of `f` almost everywhere**: if `f = f'` almost
everywhere, then `⟨f, G_{ν,j,k}⟩ = ⟨f', G_{ν,j,k}⟩` (Mathlib's
`MeasureTheory.integral_congr_ae`). -/
theorem tensorCoeff_congr_ae {f f' : (Fin d → ℝ) → ℂ} (h : f =ᵐ[volume] f') (j : ℕ)
    (νk : ι × (Fin d → ℤ)) : tensorCoeff G j f νk = tensorCoeff G j f' νk :=
  integral_congr_ae (h.mono fun y hy => by simp only [hy])

omit [Fintype ι] in
/-- **The integrands of the coefficients of `L_p` functions are integrable**: if `g` is continuous
and vanishes outside `[a, b]^d`, `1 ≤ p` and `f ∈ L_p`, then `f conj g_{j,k}` is integrable, by
Hölder's inequality with `conj g_{j,k} ∈ L_{p'}` (Mathlib's `MeasureTheory.MemLp.integrable_mul`).
-/
theorem integrable_mul_conj_tensorScaled {g : (Fin d → ℝ) → ℂ} (hg : Continuous g)
    (hsupp : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {f : (Fin d → ℝ) → ℂ} (hf : MemLp f p volume) (j : ℕ) (k : Fin d → ℤ) :
    Integrable fun y => f y * conj (tensorScaled g j k y) := by
  have := ENNReal.HolderConjugate.conjExponent hp1
  exact hf.integrable_mul (q := ENNReal.conjExponent p)
    ((Complex.continuous_conj.comp (continuous_tensorScaled hg j k)).memLp_of_hasCompactSupport
      ((hasCompactSupport_tensorScaled hsupp j k).comp_left (map_zero _)))

omit [Fintype ι] in
/-- **The coefficient integrands of locally integrable functions are integrable**: if `g` is
continuous and vanishes outside `[a, b]^d` and `f` is locally integrable, then
`y ↦ f(y) conj g_{j,k}(y)` is integrable, since `g_{j,k}` is continuous with compact support
(Mathlib's `MeasureTheory.LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`). -/
theorem integrable_mul_conj_tensorScaled_of_locallyIntegrable {g : (Fin d → ℝ) → ℂ}
    (hg : Continuous g) (hsupp : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0)
    {f : (Fin d → ℝ) → ℂ} (hf : LocallyIntegrable f volume) (j : ℕ) (k : Fin d → ℤ) :
    Integrable fun y => f y * conj (tensorScaled g j k y) := by
  have h := hf.integrable_smul_right_of_hasCompactSupport
    (Complex.continuous_conj.comp (continuous_tensorScaled hg j k))
    ((hasCompactSupport_tensorScaled hsupp j k).comp_left (map_zero _))
  simpa only [smul_eq_mul, Function.comp_apply] using h

omit [Fintype ι] in
/-- **The coefficients are additive in `f`**:
`⟨f + f', G_{ν,j,k}⟩ = ⟨f, G_{ν,j,k}⟩ + ⟨f', G_{ν,j,k}⟩` when both integrands are integrable,
for example for `f, f' ∈ L_p`, `1 ≤ p`, and a continuous generator that vanishes outside
`[a, b]^d` (`Daubechies.integrable_mul_conj_tensorScaled`). -/
theorem tensorCoeff_add {f f' : (Fin d → ℝ) → ℂ} {j : ℕ} {νk : ι × (Fin d → ℤ)}
    (hf : Integrable fun y => f y * conj (tensorScaled (G νk.1) j νk.2 y))
    (hf' : Integrable fun y => f' y * conj (tensorScaled (G νk.1) j νk.2 y)) :
    tensorCoeff G j (fun y => f y + f' y) νk = tensorCoeff G j f νk + tensorCoeff G j f' νk := by
  simp only [tensorCoeff, add_mul]
  exact integral_add hf hf'

omit [Fintype ι] in
/-- **The coefficients are homogeneous in `f`**: `⟨z f, G_{ν,j,k}⟩ = z ⟨f, G_{ν,j,k}⟩` for every
`z ∈ ℂ` (Mathlib's `MeasureTheory.integral_const_mul`). -/
theorem tensorCoeff_const_mul (z : ℂ) (f : (Fin d → ℝ) → ℂ) (j : ℕ) (νk : ι × (Fin d → ℤ)) :
    tensorCoeff G j (fun y => z * f y) νk = z * tensorCoeff G j f νk := by
  simp only [tensorCoeff, mul_assoc]
  exact integral_const_mul z _

end Linearity

/-! ### Differences of expansions and the Bernstein inequality -/

section Differences

/-- **Differences commute with dilation and translation**: for every `g : ℝ^d → ℂ`, level `j`,
position `k` and step `h ∈ ℝ^d`, `Δ_h g_{j,k} = (Δ_{2^j h} g)_{j,k}`, since
`2^j (x + h) - k = (2^j x - k) + 2^j h`. -/
theorem fwdDiff_tensorScaled (g : (Fin d → ℝ) → ℂ) (j : ℕ) (k : Fin d → ℤ) (h : Fin d → ℝ) :
    fwdDiff h (tensorScaled g j k) = tensorScaled (fwdDiff ((2 : ℝ) ^ j • h) g) j k := by
  funext x
  simp only [fwdDiff, tensorScaled]
  rw [← mul_sub, show (2 : ℝ) ^ j • (x + h) - (fun i => (k i : ℝ)) =
    (2 : ℝ) ^ j • x - (fun i => (k i : ℝ)) + (2 : ℝ) ^ j • h by rw [smul_add]; abel]

/-- **Higher differences commute with dilation and translation**: for every `g : ℝ^d → ℂ`, order
`r`, level `j`, position `k` and step `h`, `Δ_h^r g_{j,k} = (Δ_{2^j h}^r g)_{j,k}`. By induction
on `r` from `Daubechies.fwdDiff_tensorScaled`. -/
theorem iterate_fwdDiff_tensorScaled (g : (Fin d → ℝ) → ℂ) (r j : ℕ) (k : Fin d → ℤ)
    (h : Fin d → ℝ) :
    (fwdDiff h)^[r] (tensorScaled g j k) =
      tensorScaled ((fwdDiff ((2 : ℝ) ^ j • h))^[r] g) j k := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, fwdDiff_tensorScaled,
      ← Function.iterate_succ_apply' (fwdDiff ((2 : ℝ) ^ j • h)) r g]

/-- **The support of a difference on `ℝ^d`**: if `g(x) = 0` whenever some coordinate `x_i` lies
outside `[a, b]`, then `Δ_h^r g(x) = 0` whenever some coordinate `x_i` lies outside
`[a - r‖h‖, b + r‖h‖]`, for every `r ∈ ℕ` and `h ∈ ℝ^d` (sup norm). By induction on `r`:
`Δ_h^(r+1) g(x) = Δ_h^r g(x + h) - Δ_h^r g(x)`, and `|h_i| ≤ ‖h‖`. -/
theorem iterate_fwdDiff_eq_zero_of_exists_notMem {a b : ℝ} {g : (Fin d → ℝ) → ℂ}
    (hg : ∀ x, (∃ i, x i ∉ Set.Icc a b) → g x = 0) (r : ℕ) (h : Fin d → ℝ) {x : Fin d → ℝ}
    (hx : ∃ i, x i ∉ Set.Icc (a - r * ‖h‖) (b + r * ‖h‖)) : (fwdDiff h)^[r] g x = 0 := by
  induction r generalizing x with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero, add_zero] at hx
    exact hg x hx
  | succ r ih =>
    obtain ⟨i, hi⟩ := hx
    have hh := abs_le.1 ((Real.norm_eq_abs (h i)).symm.le.trans (norm_le_pi_norm h i))
    have hn := norm_nonneg h
    have h1 : (fwdDiff h)^[r] g (x + h) = 0 := ih ⟨i, fun hm => hi (by
      rw [Pi.add_apply, Set.mem_Icc] at hm
      push_cast
      exact ⟨by linarith, by linarith⟩)⟩
    have h2 : (fwdDiff h)^[r] g x = 0 := ih ⟨i, fun hm => hi (by
      rw [Set.mem_Icc] at hm
      push_cast
      exact ⟨by linarith, by linarith⟩)⟩
    rw [Function.iterate_succ_apply']
    show (fwdDiff h)^[r] g (x + h) - (fwdDiff h)^[r] g x = 0
    rw [h1, h2, sub_zero]

variable {ι : Type*} [Fintype ι] {G : ι → (Fin d → ℝ) → ℂ} {a b : ℝ}

/-- **A difference of an expansion**: if every `G_ν` vanishes outside `[a, b]^d`, then for every
level `j`, all coefficients `c` and every step `h`,
`Δ_h ∑ c_{ν,k} G_{ν,j,k} = ∑ c_{ν,k} (Δ_{2^j h} G_ν)_{j,k}` at every point. At each point only
finitely many terms are nonzero (`Daubechies.summable_tensorExpand`), so the difference may be
taken termwise (`Daubechies.fwdDiff_tensorScaled`). -/
theorem fwdDiff_tensorExpand (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) (j : ℕ)
    (c : ι × (Fin d → ℤ) → ℂ) (h : Fin d → ℝ) :
    fwdDiff h (tensorExpand G j c) =
      tensorExpand (fun ν => fwdDiff ((2 : ℝ) ^ j • h) (G ν)) j c := by
  funext x
  show tensorExpand G j c (x + h) - tensorExpand G j c x = _
  simp only [tensorExpand]
  rw [← (summable_tensorExpand hsupp j c (x + h)).tsum_sub (summable_tensorExpand hsupp j c x)]
  refine tsum_congr fun νk => ?_
  rw [← mul_sub]
  exact congrArg (c νk * ·) (congrFun (fwdDiff_tensorScaled (G νk.1) j νk.2 h) x)

/-- **Higher differences of an expansion**: if every `G_ν` vanishes outside `[a, b]^d`, then for
every order `r`, level `j`, all coefficients `c` and every step `h`,
`Δ_h^r ∑ c_{ν,k} G_{ν,j,k} = ∑ c_{ν,k} (Δ_{2^j h}^r G_ν)_{j,k}` at every point. By induction on
`r` from `Daubechies.fwdDiff_tensorExpand`; each `Δ_H^i G_ν` vanishes outside a cube
(`Daubechies.iterate_fwdDiff_eq_zero_of_exists_notMem`). -/
theorem iterate_fwdDiff_tensorExpand (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0)
    (r j : ℕ) (c : ι × (Fin d → ℤ) → ℂ) (h : Fin d → ℝ) :
    (fwdDiff h)^[r] (tensorExpand G j c) =
      tensorExpand (fun ν => (fwdDiff ((2 : ℝ) ^ j • h))^[r] (G ν)) j c := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, fwdDiff_tensorExpand fun ν x hx =>
      iterate_fwdDiff_eq_zero_of_exists_notMem (hsupp ν) r _ hx]
    simp only [Function.iterate_succ_apply']

/-- **The constant of the Bernstein inequality**: `L_r^(1 - 1/p) C'` with the overlap number
`L_r = |ι| (⌈b - a + 2r⌉ + 1)^d` of the cube `[a - r, b + r]^d`, outside which the differences
`Δ_H^r G_ν` with `‖H‖ ≤ 1` vanish, and the constant `C' = tensorCoeffConst G a b p` of the
coefficient estimate. It is the same for every level and every scale. -/
noncomputable def tensorBernsteinConst (G : ι → (Fin d → ℝ) → ℂ) (a b : ℝ) (p : ℝ≥0∞) (r : ℕ) :
    ℝ≥0∞ :=
  (tensorOverlap ι (a - r) (b + r) d : ℝ≥0∞) ^ (1 - 1 / p.toReal) * tensorCoeffConst G a b p

/-- The constant of the Bernstein inequality is finite for `1 ≤ p` if every `G_ν` lies in
`L_{p'}` (`Daubechies.tensorCoeffConst_ne_top`). -/
theorem tensorBernsteinConst_ne_top (a b : ℝ) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hG : ∀ ν, MemLp (G ν) (ENNReal.conjExponent p) volume) (r : ℕ) :
    tensorBernsteinConst G a b p r ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (Rd.one_sub_one_div_toReal_nonneg hp1)
    (ENNReal.natCast_ne_top _)) (tensorCoeffConst_ne_top a b hG)

/-- **The Bernstein inequality for expansions**: let every `G_ν` be a.e. strongly measurable and
vanish outside `[a, b]^d`, and let `1 ≤ p < ∞`. Let `f` be a.e. strongly measurable and almost
everywhere equal to the expansion of its own coefficients of level `j`. Then for every order `r`
and every `t` with `2^j t ≤ 1`,
`ω_r(f, t)_p ≤ C sup_{ν, ‖H‖ ≤ 2^j t} ‖Δ_H^r G_ν‖_p ‖f‖_p` with the constant
`C = tensorBernsteinConst G a b p r`, independent of `j`, `t` and `f`. For `‖h‖ ≤ t`,
`Δ_h^r f = ∑ ⟨f, G_{ν,j,k}⟩ (Δ_{2^j h}^r G_ν)_{j,k}` almost everywhere
(`Daubechies.iterate_fwdDiff_tensorExpand`); as `‖2^j h‖ ≤ 1` the generators `Δ_{2^j h}^r G_ν`
vanish outside `[a - r, b + r]^d`, and the upper estimate (`Daubechies.eLpNorm_tensorExpand_le`)
and the coefficient estimate (`Daubechies.dyadicWeight_mul_lqNorm_tensorCoeff_le`) give the bound,
with cancelling dyadic weights. -/
theorem smoothnessModulus_tensorExpand_le (hG : ∀ ν, AEStronglyMeasurable (G ν) volume)
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (r : ℕ) {j : ℕ} {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfe : f =ᵐ[volume] tensorExpand G j (tensorCoeff G j f)) {t : ℝ} (ht : 2 ^ j * t ≤ 1) :
    Rd.smoothnessModulus volume r p f t ≤
      tensorBernsteinConst G a b p r *
        (⨆ (ν : ι) (H : Fin d → ℝ) (_ : ‖H‖ ≤ 2 ^ j * t),
          eLpNorm ((fwdDiff H)^[r] (G ν)) p volume) * eLpNorm f p volume := by
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set S := ⨆ (ν : ι) (H : Fin d → ℝ) (_ : ‖H‖ ≤ 2 ^ j * t),
    eLpNorm ((fwdDiff H)^[r] (G ν)) p volume
  rw [Rd.smoothnessModulus_congr_ae hfe]
  refine iSup₂_le fun h hh => ?_
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hH : ‖(2 : ℝ) ^ j • h‖ ≤ 2 ^ j * t := by
    rw [norm_smul, Real.norm_of_nonneg h2.le]
    exact mul_le_mul_of_nonneg_left hh h2.le
  have hr : (r : ℝ) * ‖(2 : ℝ) ^ j • h‖ ≤ r := mul_le_of_le_one_right r.cast_nonneg (hH.trans ht)
  have hsupp' : ∀ ν x, (∃ i, x i ∉ Set.Icc (a - r) (b + r)) →
      (fwdDiff ((2 : ℝ) ^ j • h))^[r] (G ν) x = 0 := fun ν x ⟨i, hi⟩ =>
    iterate_fwdDiff_eq_zero_of_exists_notMem (hsupp ν) r _
      ⟨i, fun hm => hi ⟨by linarith [hm.1], by linarith [hm.2]⟩⟩
  have hexp := eLpNorm_tensorExpand_le (fun ν => Rd.aestronglyMeasurable_higherDiff (hG ν) r _)
    hsupp' hp1 hp (B := S)
    (fun ν => le_iSup_of_le ν (le_iSup₂_of_le ((2 : ℝ) ^ j • h) hH le_rfl)) j
    (tensorCoeff G j f)
  have hcoef := dyadicWeight_mul_lqNorm_tensorCoeff_le hG hsupp hp1 hp hf j
  rw [iterate_fwdDiff_tensorExpand hsupp]
  calc eLpNorm (tensorExpand (fun ν => (fwdDiff ((2 : ℝ) ^ j • h))^[r] (G ν)) j
        (tensorCoeff G j f)) p volume
      ≤ (tensorOverlap ι (a - r) (b + r) d : ℝ≥0∞) ^ (1 - 1 / p.toReal) * S *
          (dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j *
            lqNorm p (fun νk => ‖tensorCoeff G j f νk‖ₑ)) := hexp.trans_eq (by ring)
    _ ≤ (tensorOverlap ι (a - r) (b + r) d : ℝ≥0∞) ^ (1 - 1 / p.toReal) * S *
          (tensorCoeffConst G a b p * eLpNorm f p volume) := mul_le_mul_right hcoef _
    _ = tensorBernsteinConst G a b p r * S * eLpNorm f p volume := by
        rw [tensorBernsteinConst]
        ring

end Differences

end Daubechies
