/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.DivergenceKernels
public import FunctionSpaces.Rd.BoundedLipschitz
public import FunctionSpaces.Rd.TriebelLizorkinLocalMeans
public import FunctionSpaces.Rd.SobolevTriebelLizorkin
public import FunctionSpaces.Rd.SobolevRestrictionSpaces

/-!
# The extension theorem for Sobolev spaces on bounded Lipschitz domains

Let `Ω` be a bounded Lipschitz domain in a finite-dimensional real inner product space `V` of
dimension `n`, and `1 < p < ∞`. Every `f ∈ W^1_p(Ω)` agrees on `Ω` with some `F ∈ W^1_p(V)`
(`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev`), for `n ≥ 1` with
`‖F‖_{W^1_p(V)} ≤ C ‖f‖_{W^1_p(Ω)}` (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`): the
extension theorem of Calderón and Stein, here by Rychkov's local extension and the local means of
the gradient. For `n = 0`, `F = f` or `F = 0` serves
(`Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton`).

* **Local means by the gradient**: for a bump with moment kernel `m` of order two, the local
  means kernels are divergences, `k_{j+1} = 2^(-j) ∑_i ∂_{e_i} (K_i)_{2^j}` with the divergence
  kernels `K_i` of `m` (`Rd.LocalMeansBump.divKernel`, `Rd.LocalMeansBump.kernel_two_succ_apply`).
  If `g_i = ∂_{e_i} f` weakly on an open set `T` and the kernels at `x` only see `T`, then
  `(k_{j+1} ⋆ 1_T f)(x) = 2^(-j) ∑_i ((K_i)_{2^j} ⋆ 1_T g_i)(x)`
  (`Rd.LocalMeansBump.conv_kernel_two_succ_eq`), and the strong type of the Calderón–Zygmund
  families `((K_i)_{2^j})_j` bounds the local means quasi-norm of Triebel–Lizorkin type on a set
  (`Rd.LocalMeansBump.tlLocalNormOn`) by `‖f‖_{L_p(T)} + ∑_i ‖g_i‖_{L_p(T)}`
  (`Rd.LocalMeansBump.tlLocalNormOn_le_patchConst`).
* **One patch** (`Rd.LocalMeansBump.extendsSobolev`): the local extension
  `∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` lies in `F^1_{p,2}(V) = W^1_p(V)`
  (`Rd.LocalMeansBump.triebelLizorkinNorm_localExtension_le`) and agrees with `f` on the patch;
  `Rd.ExtendsSobolev p O U C` says that such extensions from `U` exist with the constant `C`.
* **Pasting** (`Rd.extendsSobolev_of_cover`): a smooth resolution of unity subordinate to the
  boundary patches and the inner patch pastes the local extensions in `W^1_p(V)`, by the product
  rule (`Rd.hasWeakLineDeriv_mulLp`).
* **For `p = 2`**: `H^1(Ω) = W^1_2(Ω)` (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_restrictL2`), Rellich's theorem in
  `W^1_2(Ω)` (`Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`), and the
  quotient norm of `H^1(Ω)` is bounded by the `W^1_2(Ω)` norm
  (`Rd.BoundedLipschitzDomain.exists_norm_le_restrictL2`), so the two norms are equivalent. The
  boundary traces of `H^1(Ω)` serve for `W^1_2(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.isBoundaryTrace_unique_of_memWeakSobolev`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric TopologicalSpace
open scoped ENNReal SchwartzMap FourierTransform LineDeriv Real BesselPotentialSpace

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The local means kernels as divergences -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The moment kernel of order two of a bump of radius `R` vanishes outside the ball of radius
`2R`. -/
theorem momentKernel_two_eq_zero {z : V} (hz : 2 * b.radius < ‖z‖) :
    momentKernel b.toFun 2 z = 0 :=
  b.momentKernel_eq_zero 2 (by exact_mod_cast hz)

/-- The **divergence kernels** `K_i` of a bump: the divergence kernels (`Rd.divergenceSchwartz`) of
its moment kernel `m` of order two in the directions of the orthonormal basis `e_i = Rd.gridBasis`,
so that `∑_i ∂_{e_i} K_i = m_2 - m` (`Rd.sum_lineDerivOp_divergenceSchwartz`); at the dyadic scales
this writes the local means kernels as divergences (`Rd.LocalMeansBump.kernel_two_succ_apply`). -/
noncomputable def divKernel (i : Fin (finrank ℝ V)) : 𝓢(V, ℂ) :=
  divergenceSchwartz (b.contDiff_momentKernel 2) (fun _ hz => b.momentKernel_two_eq_zero hz)
    (gridBasis V i)

/-- The divergence kernels of a bump have compact support. -/
theorem hasCompactSupport_divKernel (i : Fin (finrank ℝ V)) :
    HasCompactSupport (b.divKernel i : V → ℂ) :=
  hasCompactSupport_divergenceKernel (fun _ hz => b.momentKernel_two_eq_zero hz) _

/-- The divergence kernels vanish at `y` if the moment kernel vanishes at every `t y`,
`t ∈ [1, 2]`. -/
theorem divKernel_eq_zero (i : Fin (finrank ℝ V)) {y : V}
    (hy : ∀ t : ℝ, 1 ≤ t → t ≤ 2 → momentKernel b.toFun 2 (t • y) = 0) : b.divKernel i y = 0 :=
  divergenceKernel_eq_zero _ hy

/-- **The local means kernels of order two at dyadic scales**: `k_{j+1} = (m_2 - m)_{2^j}`. -/
theorem kernel_two_succ (j : ℕ) :
    b.kernel 2 (j + 1) =
      dilate (2 ^ j) (fun y => dilate 2 (momentKernel b.toFun 2) y - momentKernel b.toFun 2 y) := by
  rw [show (fun y => dilate 2 (momentKernel b.toFun 2) y - momentKernel b.toFun 2 y) =
    dilate 2 (momentKernel b.toFun 2) - momentKernel b.toFun 2 from rfl, dilate_sub,
    dilate_dilate, ← pow_succ]
  rfl

/-- **The local means kernels are divergences**: `k_{j+1} = 2^(-j) ∑_i ∂_{e_i} (K_i)_{2^j}`
(`Rd.sum_lineDerivOp_schwartzDilate_divergenceSchwartz`). -/
theorem kernel_two_succ_apply (j : ℕ) (y : V) :
    b.kernel 2 (j + 1) y = ((((2 : ℝ) ^ j)⁻¹ : ℝ) : ℂ) * ∑ i, (∂_{gridBasis V i}
      (schwartzDilate (2 ^ j) (by positivity) (b.divKernel i)) : 𝓢(V, ℂ)) y := by
  unfold divKernel
  rw [sum_lineDerivOp_schwartzDilate_divergenceSchwartz (gridBasis V), kernel_two_succ]
  have h : (((2 : ℝ) ^ j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos two_pos j).ne'
  push_cast
  field_simp

/-- **The moment kernel of order two of a bump has vanishing first moments**
(`Rd.integral_inner_mul_momentKernel_two`). -/
theorem integral_inner_mul_momentKernel (w : V) :
    ∫ x, (inner ℝ w x : ℂ) * momentKernel b.toFun 2 x = 0 :=
  integral_inner_mul_momentKernel_two w
    (((Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)).mul
      b.contDiff.continuous).integrable_of_hasCompactSupport b.hasCompactSupport.mul_left)

/-- **The divergence kernels form Calderón–Zygmund families**: the dilates `(K_i)_{2^j}` have the
Fourier overlap `Rd.meanZeroOverlap (K_i)` and the Hörmander constant `4 H_{K_i}`
(`Rd.isCZFamily_divergenceSchwartz`). -/
theorem isCZFamily_divKernel (i : Fin (finrank ℝ V)) :
    IsCZFamily (fun j => dilate (2 ^ j) (b.divKernel i : V → ℂ)) (meanZeroOverlap (b.divKernel i))
      (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i)) :=
  isCZFamily_divergenceSchwartz (b.contDiff_momentKernel 2)
    (fun _ hz => b.momentKernel_two_eq_zero hz) (b.integral_inner_mul_momentKernel (gridBasis V i))

/-! ### Local means by the gradient -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Local means of order two by the gradient, at one point**: let `g_i = ∂_{e_i} f` weakly on an
open set `T`, `f ∈ L_p(T)`, and let `x - y ∈ T` for every `y` in the support of every
`(K_i)_{2^j}`. Then `(k_{j+1} ⋆ 1_T f)(x) = 2^(-j) ∑_i ((K_i)_{2^j} ⋆ 1_T g_i)(x)`: the kernel is
`2^(-j) ∑_i ∂_{e_i} (K_i)_{2^j}` (`Rd.LocalMeansBump.kernel_two_succ_apply`), and each derivative
moves to `f` (`Rd.conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv`). -/
theorem conv_kernel_two_succ_eq {T : Opens V} {f : V → ℂ} {g : Fin (finrank ℝ V) → V → ℂ}
    (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i)) (j : ℕ) {x : V}
    (hx : ∀ i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    conv (b.kernel 2 (j + 1)) ((T : Set V).indicator f) volume x =
      ((((2 : ℝ) ^ j)⁻¹ : ℝ) : ℂ) * ∑ i, conv (dilate (2 ^ j) (b.divKernel i : V → ℂ))
        ((T : Set V).indicator (g i)) volume x := by
  have hc : (2 : ℝ) ^ j ≠ 0 := by positivity
  have hT := T.isOpen.measurableSet
  have hKc : ∀ i, (schwartzDilate (2 ^ j) hc (b.divKernel i) : V → ℂ) =
      dilate (2 ^ j) (b.divKernel i) := fun i => coe_schwartzDilate _ _ _
  have hcs : ∀ i, HasCompactSupport (schwartzDilate (2 ^ j) hc (b.divKernel i) : V → ℂ) :=
    fun i => by rw [hKc]; exact hasCompactSupport_dilate (b.hasCompactSupport_divKernel i) hc
  have hloc : LocallyIntegrable ((T : Set V).indicator f) volume :=
    ((memLp_indicator_iff_restrict hT).2 hf).locallyIntegrable Fact.out
  have hfg' : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) ((T : Set V).indicator f)
      ((T : Set V).indicator (g i)) := fun i =>
    (hfg i).congr_ae (indicator_ae_eq_restrict hT).symm (indicator_ae_eq_restrict hT).symm
  have hstep : ∀ i, conv (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i))
      volume x = conv (∂_{gridBasis V i} (schwartzDilate (2 ^ j) hc (b.divKernel i)) :
        𝓢(V, ℂ)) ((T : Set V).indicator f) volume x := fun i => by
    rw [← hKc, conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv (hfg' i) (hcs i)
      (by rw [hKc]; exact hx i), LineDeriv.iteratedLineDerivOp_one]
  have hint : ∀ i, Integrable fun y => (∂_{gridBasis V i} (schwartzDilate (2 ^ j) hc
      (b.divKernel i)) : 𝓢(V, ℂ)) y * (T : Set V).indicator f (x - y) := fun i =>
    ((hcs i).fderiv_apply (𝕜 := ℝ) (gridBasis V i)).convolutionExists_left
      (ContinuousLinearMap.mul ℂ ℂ) (∂_{gridBasis V i} (schwartzDilate (2 ^ j) hc
        (b.divKernel i))).continuous hloc x
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  simp only [conv_apply]
  simp_rw [b.kernel_two_succ_apply j, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]

/-- The constant `∑_i C_{p}(K_i)` of the gradient bound of the local means, with the constants
`C_p(K_i) = Rd.czConst V p B_i H_i` of the Calderón–Zygmund families of the divergence kernels
(`Rd.LocalMeansBump.isCZFamily_divKernel`). -/
noncomputable def gradientConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, czConst V p (meanZeroOverlap (b.divKernel i))
    (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i))

/-- The constant of the gradient bound is finite for `1 < p < ∞`. -/
theorem gradientConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) : b.gradientConst p ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun _ _ => czConst_ne_top hp1 hp (meanZeroOverlap_ne_top _)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

/-! ### Local means of Triebel–Lizorkin type on a set -/

/-- The **local means quasi-norm of Triebel–Lizorkin type on a set** `W`,
`‖ x ↦ ‖(2^(js) |1_W (k_j ⋆ f)(x)|)_j‖_{ℓ_q} ‖_p`. -/
noncomputable def tlLocalNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ) (s : ℝ)
    (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j *
    ‖(indicatorLp hW (b.localMean hp L j f) : V → ℂ) x‖ₑ)) p volume

/-- The local means on `W` are bounded by the local means quasi-norm of Triebel–Lizorkin type:
`‖1_W (k_j ⋆ f)‖_p ≤ 2^(-js) X` with `X = Rd.LocalMeansBump.tlLocalNormOn`. -/
theorem enorm_indicatorLp_localMean_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0) (f : Lp ℂ p (volume : Measure V)) (j : ℕ) :
    ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤
      dyadicWeight (-s) j * b.tlLocalNormOn hp hW L s q f :=
  enorm_le_dyadicWeight_neg_mul_eLpNorm_lqNorm hq s
    (fun j => indicatorLp hW (b.localMean hp L j f)) j

/-- The weighted local means on `W` are bounded by the local means quasi-norm of Triebel–Lizorkin
type: `2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X` with `X = Rd.LocalMeansBump.tlLocalNormOn`
(`Rd.LocalMeansBump.enorm_indicatorLp_localMean_le`). -/
theorem dyadicWeight_mul_enorm_indicatorLp_localMean_le (hp : p ≠ ∞) {W : Set V}
    (hW : MeasurableSet W) (L : ℕ) {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0)
    (f : Lp ℂ p (volume : Measure V)) (j : ℕ) :
    dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ b.tlLocalNormOn hp hW L s q f :=
  calc dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ
      ≤ dyadicWeight s j * (dyadicWeight (-s) j * b.tlLocalNormOn hp hW L s q f) := by
        gcongr
        exact b.enorm_indicatorLp_localMean_le hp hW L hq f j
    _ = b.tlLocalNormOn hp hW L s q f := by
        rw [← mul_assoc, ENNReal.dyadicWeight_mul_neg_self, one_mul]

/-- The terms of the local extension: `‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 2^(-js) X` with
`X = Rd.LocalMeansBump.tlLocalNormOn` (`Rd.LocalMeansBump.enorm_localExtTerm_le_of_forall_le`). -/
theorem enorm_localExtTerm_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0) (f : Lp ℂ p (volume : Measure V)) (j : ℕ) :
    ‖b.localExtTerm hp hW L j f‖ₑ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume *
      (dyadicWeight (-s) j * b.tlLocalNormOn hp hW L s q f) :=
  b.enorm_localExtTerm_le_of_forall_le hp hW L
    (b.dyadicWeight_mul_enorm_indicatorLp_localMean_le hp hW L hq f) j

/-- **The local extension converges absolutely** for `s > 0` and a finite local means quasi-norm
of Triebel–Lizorkin type on `W` (`Rd.LocalMeansBump.summable_localExtTerm_of_forall_le`). -/
theorem summable_localExtTerm_of_tlLocalNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : q ≠ 0) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.tlLocalNormOn hp hW L s q f < ∞) : Summable fun j => b.localExtTerm hp hW L j f :=
  b.summable_localExtTerm_of_forall_le hp hW L hs hf.ne
    (b.dyadicWeight_mul_enorm_indicatorLp_localMean_le hp hW L hq f)

/-- **The local extension in `L_p`**: for `s > 0`,
`‖∑_j η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 (1 - 2^(-s))⁻¹ X` with
`X = Rd.LocalMeansBump.tlLocalNormOn` (`Rd.LocalMeansBump.tsum_enorm_localExtTerm_le`). -/
theorem enorm_localExtension_le_of_tlLocalNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : q ≠ 0) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.tlLocalNormOn hp hW L s q f < ∞) :
    ‖b.localExtension hp hW L f‖ₑ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume *
      (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * b.tlLocalNormOn hp hW L s q f := by
  have h1 : ‖b.localExtension hp hW L f‖ₑ ≤ ∑' j, ‖b.localExtTerm hp hW L j f‖ₑ :=
    ENNReal.le_tsum_of_tendsto_sum (C := 1) ENNReal.one_ne_top (fun x y => enorm_add_le x y)
      (fun x => by rw [one_mul])
      (b.tendsto_sum_localExtTerm_of_summable hp hW L
        (b.summable_localExtTerm_of_tlLocalNormOn hp hW L hs hq hf))
  exact h1.trans (b.tsum_enorm_localExtTerm_le hp hW L
    (b.dyadicWeight_mul_enorm_indicatorLp_localMean_le hp hW L hq f))

/-- **The local extension lies in `F^s_{p,q}`**: for `1 < p < ∞`, `1 < q ≤ ∞`, `s > 0` and a
finite local means quasi-norm of Triebel–Lizorkin type on `W`,
`‖∑_j η_j ⋆ 1_W (k_j ⋆ f)‖_{F^s_{p,q}} ≤ C X` with `C = Rd.LocalMeansBump.tlUpperConst L p q s`
(`Rd.LocalMeansBump.triebelLizorkinNorm_le_of_tendsto_sum_dual`). -/
theorem triebelLizorkinNorm_localExtension_le (hp1 : 1 < p) (hp : p ≠ ∞) {W : Set V}
    (hW : MeasurableSet W) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq1 : 1 < q)
    {f : Lp ℂ p (volume : Measure V)} (hf : b.tlLocalNormOn hp hW L s q f < ∞) :
    triebelLizorkinNorm s q (b.localExtension hp hW L f) ≤
      b.tlUpperConst L p q s * b.tlLocalNormOn hp hW L s q f :=
  b.triebelLizorkinNorm_le_of_tendsto_sum_dual L hp1 hp hq1 s
    (b.tendsto_sum_localExtTerm_of_summable hp hW L
      (b.summable_localExtTerm_of_tlLocalNormOn hp hW L hs (zero_lt_one.trans hq1).ne' hf))

/-! ### The Triebel–Lizorkin local means of order two by the gradient -/

/-- **One local mean by the gradient**: under the hypotheses of
`Rd.LocalMeansBump.conv_kernel_two_succ_eq`,
`2^(j+1) |(k_{j+1} ⋆ 1_T f)(x)| ≤ 2 ∑_i |((K_i)_{2^j} ⋆ 1_T g_i)(x)|`. -/
theorem dyadicWeight_mul_enorm_conv_kernel_le {T : Opens V} {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i)) (j : ℕ) {x : V}
    (hx : ∀ i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    dyadicWeight 1 (j + 1) * ‖conv (b.kernel 2 (j + 1)) ((T : Set V).indicator f) volume x‖ₑ ≤
      2 * ∑ i, ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i))
        volume x‖ₑ := by
  have hw : dyadicWeight 1 (j + 1) * ‖(((((2 : ℝ) ^ j)⁻¹ : ℝ) : ℂ))‖ₑ = 2 := by
    rw [ENNReal.dyadicWeight_succ, ENNReal.dyadicWeight_eq_pow, ENNReal.rpow_one,
      ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), mul_one]
  rw [b.conv_kernel_two_succ_eq hf hfg j hx, enorm_mul, ← mul_assoc, hw]
  gcongr
  exact enorm_sum_le _ _

/-- **The local means of order two by the gradient, pointwise**: if `x - y ∈ T` for `x ∈ W`, every
level `j` and every `y` in the support of `(K_i)_{2^j}`, and `F = 1_T f` in `L_p`, then almost
everywhere `‖(2^j |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ≤ |1_W (k_0 ⋆ F)(x)| +
2 ∑_i ‖(((K_i)_{2^j} ⋆ 1_T g_i)(x))_j‖_{ℓ_2}`. -/
theorem ae_lqNorm_le_of_hasWeakLineDeriv (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    {T : Opens V} {f : V → ℂ} {g : Fin (finrank ℝ V) → V → ℂ}
    (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    ∀ᵐ x ∂volume, lqNorm 2 (fun j => dyadicWeight 1 j *
        ‖(indicatorLp hW (b.localMean hp 2 j F) : V → ℂ) x‖ₑ) ≤
      ‖(indicatorLp hW (b.localMean hp 2 0 F) : V → ℂ) x‖ₑ + 2 * ∑ i, lqNorm 2 (fun j =>
        ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i)) volume
          x‖ₑ) := by
  have hae : ∀ᵐ x ∂volume, ∀ j, (indicatorLp hW (b.localMean hp 2 j F) : V → ℂ) x =
      W.indicator (conv (b.kernel 2 j) ((T : Set V).indicator f) volume) x :=
      ae_all_iff.2 fun j => by
    filter_upwards [indicatorLp_apply_ae hW (b.localMean hp 2 j F), b.localMean_ae_eq hp 2 j F]
      with x h1 h2
    rw [h1, ← conv_congr_ae hF]
    by_cases hxW : x ∈ W
    · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW, h2]
    · rw [Set.indicator_of_notMem hxW, Set.indicator_of_notMem hxW]
  filter_upwards [hae] with x hx
  refine (ENNReal.lqNorm_le_head_add_shift one_le_two _).trans ?_
  rw [ENNReal.dyadicWeight_zero_right, one_mul]
  gcongr
  calc lqNorm 2 (fun j => dyadicWeight 1 (j + 1) *
        ‖(indicatorLp hW (b.localMean hp 2 (j + 1) F) : V → ℂ) x‖ₑ)
      ≤ lqNorm 2 (fun j => 2 * ∑ i, ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ))
          ((T : Set V).indicator (g i)) volume x‖ₑ) := ENNReal.lqNorm_mono fun j => by
        rw [hx (j + 1)]
        by_cases hxW : x ∈ W
        · rw [Set.indicator_of_mem hxW]
          exact b.dyadicWeight_mul_enorm_conv_kernel_le hf hfg j (hsupp x hxW j)
        · simp [Set.indicator_of_notMem hxW]
    _ = 2 * lqNorm 2 (fun j => ∑ i, ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ))
          ((T : Set V).indicator (g i)) volume x‖ₑ) := ENNReal.lqNorm_const_mul _ _
    _ ≤ _ := by
        gcongr
        exact ENNReal.lqNorm_sum_le one_le_two _ fun i j =>
          ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i)) volume x‖ₑ

omit [Fact (1 ≤ p)] in
/-- The square functions of the divergence kernels: for `1 < p < ∞`,
`‖ x ↦ ‖(((K_i)_{2^j} ⋆ 1_T g)(x))_j‖_{ℓ_2} ‖_p ≤ C_p(K_i) ‖g‖_{L_p(T)}`
(`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`). -/
theorem eLpNorm_lqNorm_conv_divKernel_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {T : Opens V} {g : V → ℂ} (hg : MemLp g p (volume.restrict T)) (i : Fin (finrank ℝ V)) :
    eLpNorm (fun x => lqNorm 2 (fun j => ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ))
        ((T : Set V).indicator g) volume x‖ₑ)) p volume ≤
      czConst V p (meanZeroOverlap (b.divKernel i))
        (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i)) *
        eLpNorm g p (volume.restrict T) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict T.isOpen.measurableSet]
  exact (b.isCZFamily_divKernel i).eLpNorm_lqNorm_conv_le hp1 hp
    ((memLp_indicator_iff_restrict T.isOpen.measurableSet).2 hg)

/-- **The local means of Triebel–Lizorkin type by the gradient**: let `g_i = ∂_{e_i} f` weakly on
an open set `T` with `f, g_i ∈ L_p(T)`, `1 < p < ∞`, let `x - y ∈ T` for every `x ∈ W`, every level
`j` and every `y` in the support of `(K_i)_{2^j}`, and let `F = 1_T f` in `L_p`. Then
`‖ x ↦ ‖(2^j |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ‖_p ≤ ‖m‖_1 ‖f‖_{L_p(T)} +
2 ∑_i C_p(K_i) ‖g_i‖_{L_p(T)}`. -/
theorem tlLocalNormOn_le_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {W : Set V} (hW : MeasurableSet W) {T : Opens V} {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hg : ∀ i, MemLp (g i) p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    b.tlLocalNormOn hp hW 2 1 2 F ≤ eLpNorm (momentKernel b.toFun 2) 1 volume *
      eLpNorm f p (volume.restrict T) + 2 * ∑ i, czConst V p (meanZeroOverlap (b.divKernel i))
        (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i)) *
        eLpNorm (g i) p (volume.restrict T) := by
  have hT := T.isOpen.measurableSet
  have hΛ : ∀ i, AEMeasurable (fun x => lqNorm 2 (fun j =>
      ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i)) volume x‖ₑ))
      volume := fun i => aemeasurable_lqNorm_comp (fun j =>
    (aestronglyMeasurable_conv (continuous_dilate (b.divKernel i).continuous _).aestronglyMeasurable
      ((memLp_indicator_iff_restrict hT).2 (hg i)).aestronglyMeasurable).enorm) 2
  have hFn : ‖F‖ₑ = eLpNorm f p (volume.restrict T) := by
    rw [Lp.enorm_def, eLpNorm_congr_ae hF, eLpNorm_indicator_eq_eLpNorm_restrict hT]
  have h1 : b.tlLocalNormOn hp hW 2 1 2 F ≤
      eLpNorm (fun x => ‖(indicatorLp hW (b.localMean hp 2 0 F) : V → ℂ) x‖ₑ) p volume +
        eLpNorm (fun x => 2 * ∑ i, lqNorm 2 (fun j => ‖conv (dilate (2 ^ j)
          (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i)) volume x‖ₑ)) p volume := by
    refine (eLpNorm_mono_enorm_ae
      (aemeasurable_lqNorm_comp (fun j => ((Lp.aestronglyMeasurable _).enorm.const_mul _))
        2).aestronglyMeasurable ?_).trans (eLpNorm_add_le Fact.out)
    filter_upwards [b.ae_lqNorm_le_of_hasWeakLineDeriv hp hW hf hfg hsupp hF] with x hx
    simpa only [enorm_eq_self, Pi.add_apply] using hx
  have h2 : eLpNorm (fun x => 2 * ∑ i, lqNorm 2 (fun j => ‖conv (dilate (2 ^ j)
      (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i)) volume x‖ₑ)) p volume ≤
      2 * ∑ i, eLpNorm (fun x => lqNorm 2 (fun j => ‖conv (dilate (2 ^ j)
        (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i)) volume x‖ₑ)) p volume := by
    rw [eLpNorm_const_mul_ennreal _ (Finset.aemeasurable_fun_sum _ fun i _ => hΛ i)]
    gcongr
    simpa only [Finset.sum_fn] using eLpNorm_sum_le (p := p) (μ := volume) Fact.out
  have h3 : eLpNorm (fun x => ‖(indicatorLp hW (b.localMean hp 2 0 F) : V → ℂ) x‖ₑ) p volume ≤
      eLpNorm (momentKernel b.toFun 2) 1 volume * eLpNorm f p (volume.restrict T) := by
    rw [eLpNorm_enorm _ (Lp.aestronglyMeasurable _), ← Lp.enorm_def, ← hFn]
    exact b.enorm_indicatorLp_localMean_zero_le hp hW 2 F
  refine h1.trans (add_le_add h3 (h2.trans ?_))
  gcongr with i
  exact b.eLpNorm_lqNorm_conv_divKernel_le hp1 hp (hg i) i

end LocalMeansBump

/-! ### Bounded extensions from a set -/

variable {p : ℝ≥0∞}

variable (p) in
/-- **Sobolev functions on `O` extend from `U` with constant `C`**: for every `f ∈ L_p(O)` with
weak derivatives `g_i = ∂_{e_i} f ∈ L_p(O)` along the orthonormal basis `e_i = Rd.gridBasis V i`
there are `F ∈ W^1_p(V)` with `F = f` almost everywhere on `U` and weak derivatives
`G_i = ∂_{e_i} F ∈ L_p(V)` with `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`. -/
def ExtendsSobolev (O : Opens V) (U : Set V) (C : ℝ≥0∞) : Prop :=
  ∀ (f : V → ℂ) (g : Fin (finrank ℝ V) → V → ℂ), MemLp f p (volume.restrict O) →
    (∀ i, MemLp (g i) p (volume.restrict O)) →
    (∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) f (g i)) →
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev 1 F ∧ (∀ᵐ x ∂volume, x ∈ U → F x = f x) ∧
      ∃ G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V),
        (∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) F (G i)) ∧
        ‖F‖ₑ + ∑ i, ‖G i‖ₑ ≤
          C * (eLpNorm f p (volume.restrict O) + ∑ i, eLpNorm (g i) p (volume.restrict O))

/-- **Larger domains**: an extension from `U` for Sobolev functions on `T` serves for Sobolev
functions on every open `O ⊇ T`, with the same constant, since `‖h‖_{L_p(T)} ≤ ‖h‖_{L_p(O)}` and
weak derivatives restrict to `T` (`Rd.HasWeakLineDeriv.mono`). -/
theorem ExtendsSobolev.of_le {T O : Opens V} {U : Set V} {C : ℝ≥0∞}
    (h : ExtendsSobolev p T U C) (hTO : T ≤ O) : ExtendsSobolev p O U C := by
  intro f g hf hg hfg
  have hμ : volume.restrict (T : Set V) ≤ volume.restrict O :=
    Measure.restrict_mono (show (T : Set V) ⊆ O from hTO) le_rfl
  obtain ⟨F, hF, hFf, G, hG, hb⟩ := h f g (hf.mono_measure hμ) (fun i => (hg i).mono_measure hμ)
    fun i => (hfg i).mono hTO
  refine ⟨F, hF, hFf, G, hG, hb.trans ?_⟩
  gcongr

/-- `∑_i a_i b_i ≤ (∑_i a_i)(∑_i b_i)` in `ℝ≥0∞`. -/
theorem sum_mul_le_sum_mul_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ≥0∞) :
    ∑ i ∈ s, a i * b i ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, b i := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_right (Finset.single_le_sum
    (fun j _ => zero_le) hi) _

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The constant `‖m‖_1 + 2 ∑_i C_p(K_i)` of the local means of a bump by the gradient. -/
noncomputable def patchConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (momentKernel b.toFun 2) 1 volume + 2 * b.gradientConst p

/-- The constant of the local means by the gradient is finite for `1 < p < ∞`. -/
theorem patchConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) : b.patchConst p ≠ ∞ :=
  ENNReal.add_ne_top.2
    ⟨(memLp_one_iff_integrable.2 (integrable_momentKernel b.integrable 2)).eLpNorm_ne_top,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (b.gradientConst_ne_top hp1 hp)⟩

/-- **The local means of Triebel–Lizorkin type by the gradient, with one constant**: under the
hypotheses of `Rd.LocalMeansBump.tlLocalNormOn_le_of_hasWeakLineDeriv`,
`‖ x ↦ ‖(2^j |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ‖_p ≤ C (‖f‖_{L_p(T)} + ∑_i ‖g_i‖_{L_p(T)})` with
`C = Rd.LocalMeansBump.patchConst b p`. -/
theorem tlLocalNormOn_le_patchConst [Fact (1 ≤ p)] [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {W : Set V} (hW : MeasurableSet W) {T : Opens V} {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hg : ∀ i, MemLp (g i) p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    b.tlLocalNormOn hp hW 2 1 2 F ≤ b.patchConst p *
      (eLpNorm f p (volume.restrict T) + ∑ i, eLpNorm (g i) p (volume.restrict T)) := by
  refine (b.tlLocalNormOn_le_of_hasWeakLineDeriv hp1 hp hW hf hg hfg hsupp hF).trans ?_
  rw [patchConst, add_mul, mul_assoc 2]
  refine add_le_add (mul_le_mul_right le_self_add _) (mul_le_mul_right ?_ 2)
  exact (sum_mul_le_sum_mul_sum _ _ _).trans (mul_le_mul_right le_add_self _)

/-- The constant `(2 ‖m‖_1 (1 - 2^(-1))⁻¹ + (∑_i C_i) A) C_b` of the extension from one patch, with
the constants `C_i = Rd.tlToSobolevConst p e_i` of the weak derivatives of `F^1_{p,2}` functions,
`A = Rd.LocalMeansBump.tlUpperConst b 2 p 2 1` and `C_b = Rd.LocalMeansBump.patchConst b p`. -/
noncomputable def extensionConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  (2 * eLpNorm (momentKernel b.toFun 2) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-(1 : ℝ)))⁻¹ +
    (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) * b.tlUpperConst 2 p 2 1) *
    b.patchConst p

/-- The constant of the extension from one patch is finite for `1 < p < ∞`. -/
theorem extensionConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) : b.extensionConst p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofNat_ne_top (memLp_one_iff_integrable.2
      (integrable_momentKernel b.integrable 2)).eLpNorm_ne_top)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top one_pos),
    ENNReal.mul_ne_top (ENNReal.sum_ne_top.2 fun _ _ => tlToSobolevConst_ne_top hp1 hp _)
      (b.tlUpperConst_ne_top 2 hp1 hp ENNReal.one_lt_two one_pos)⟩) (b.patchConst_ne_top hp1 hp)

/-- **The extension from one patch** (Rychkov's local extension with the local means of the
gradient): let `U ⊆ T` with `T` open, let the dual kernels at points of `U` only see `W`, and let
`x - y ∈ T` for every `x ∈ W`, every level `j` and every `y` in the support of `(K_i)_{2^j}`. Then
for `1 < p < ∞` the local extension `F = ∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` of order two lies in
`F^1_{p,2}(V) = W^1_p(V)` and agrees with `f` on `U`, with the constant
`Rd.LocalMeansBump.extensionConst b p` (`Rd.LocalMeansBump.tlLocalNormOn_le_patchConst`,
`Rd.LocalMeansBump.triebelLizorkinNorm_localExtension_le`,
`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin`). -/
theorem extendsSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W) {T : Opens V} (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual 2 j y ≠ 0 → x - y ∈ W)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    ExtendsSobolev p T U (b.extensionConst p) := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  intro f g hf hg hfg
  have hT := T.isOpen.measurableSet
  have hf₀ := (memLp_indicator_iff_restrict hT).2 hf
  set Y := eLpNorm f p (volume.restrict T) + ∑ i, eLpNorm (g i) p (volume.restrict T)
  have hY : Y ≠ ∞ := ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top,
    ENNReal.sum_ne_top.2 fun i _ => (hg i).eLpNorm_ne_top⟩
  have hX := b.tlLocalNormOn_le_patchConst hp1 hp hW hf hg hfg hsupp hf₀.coeFn_toLp
  have hXf : b.tlLocalNormOn hp hW 2 1 2 (hf₀.toLp _) < ∞ :=
    hX.trans_lt (ENNReal.mul_lt_top (b.patchConst_ne_top hp1 hp).lt_top hY.lt_top)
  have hTL := b.triebelLizorkinNorm_localExtension_le hp1 hp hW 2 one_pos ENNReal.one_lt_two hXf
  have hmem : MemTriebelLizorkin ((1 : ℕ) : ℝ) 2 (b.localExtension hp hW 2 (hf₀.toLp _)) := by
    rw [Nat.cast_one]
    exact hTL.trans_lt (ENNReal.mul_lt_top
      (b.tlUpperConst_ne_top 2 hp1 hp ENNReal.one_lt_two one_pos).lt_top hXf)
  choose G hG hGn using fun i => exists_hasWeakLineDeriv_of_memTriebelLizorkin hp1 hp
    (fun _ : Fin 1 => gridBasis V i) hmem
  have heq := b.indicatorLp_localExtension_of_summable hp one_le_two hU hW hUW
    (b.summable_localExtTerm_of_tlLocalNormOn hp hW 2 one_pos two_ne_zero hXf)
  refine ⟨_, memSobolev_of_memTriebelLizorkin hp1 hp hmem, ?_, G, hG, ?_⟩
  · filter_upwards [Lp.ext_iff.1 heq, indicatorLp_apply_ae hU (b.localExtension hp hW 2
      (hf₀.toLp _)), indicatorLp_apply_ae hU (hf₀.toLp _), hf₀.coeFn_toLp] with x h1 h2 h3 h4 hxU
    rw [h2, h3, Set.indicator_of_mem hxU, Set.indicator_of_mem hxU] at h1
    rw [h1, h4, Set.indicator_of_mem (hUT hxU)]
  · have hFn := b.enorm_localExtension_le_of_tlLocalNormOn hp hW 2 one_pos two_ne_zero hXf
    have hGs : ∑ i, ‖G i‖ₑ ≤ (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) *
        b.tlUpperConst 2 p 2 1 * b.tlLocalNormOn hp hW 2 1 2 (hf₀.toLp _) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => (hGn i).trans ?_
      rw [Nat.cast_one, mul_assoc]
      exact mul_le_mul_right hTL _
    calc _ ≤ _ := add_le_add hFn hGs
      _ = (2 * eLpNorm (momentKernel b.toFun 2) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-(1 : ℝ)))⁻¹ +
          (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) * b.tlUpperConst 2 p 2 1) *
          b.tlLocalNormOn hp hW 2 1 2 (hf₀.toLp _) := by ring
      _ ≤ (2 * eLpNorm (momentKernel b.toFun 2) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-(1 : ℝ)))⁻¹ +
          (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) * b.tlUpperConst 2 p 2 1) *
          (b.patchConst p * Y) := mul_le_mul_right hX _
      _ = _ := by rw [extensionConst]; ring

end LocalMeansBump

/-! ### Pasting in `W^1_p(V)` -/

/-- **The product rule in `L_p(V)`**: if `G = ∂_w F` weakly on `V` and `χ` is a smooth real
function, bounded with its derivative `∂_w χ` (bounds `C`, `C'`), then `χ G + (∂_w χ) F` is the weak
derivative `∂_w (χ F)` on `V`, with the products `Rd.mulLp` in `L_p(V)`
(`Rd.HasWeakLineDeriv.mul_contDiff`). -/
theorem hasWeakLineDeriv_mulLp {w : V} {F G : Lp ℂ p (volume : Measure V)}
    (h : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => w) F G) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {C C' : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C)
    (hc' : Continuous fun x => (fderiv ℝ χ x w : ℂ)) (hC' : ∀ x, ‖(fderiv ℝ χ x w : ℂ)‖ ≤ C') :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => w) (mulLp hc hC F)
      ((mulLp hc hC G + mulLp hc' hC' F : Lp ℂ p (volume : Measure V)) : V → ℂ) := by
  refine (h.mul_contDiff hχ).congr_ae ?_ ?_ <;> rw [volume_restrict_top]
  · exact (mulLp_apply_ae hc hC F).symm
  · filter_upwards [Lp.coeFn_add (mulLp hc hC G) (mulLp hc' hC' F), mulLp_apply_ae hc hC G,
      mulLp_apply_ae hc' hC' F] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]

/-- **Smooth compactly supported multipliers keep `W^1_p(V)`**: if `F ∈ W^1_p(V)` and `χ` is a
smooth real function with compact support, then `χ F ∈ W^1_p(V)` (`Rd.hasWeakLineDeriv_mulLp`). -/
theorem MemSobolev.mulLp [Fact (1 ≤ p)] {F : Lp ℂ p (volume : Measure V)} (hF : MemSobolev 1 F)
    {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hcs : HasCompactSupport χ) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) :
    MemSobolev 1 (mulLp hc hC F) := by
  refine memSobolev_one_of_forall_hasWeakLineDeriv fun v => ?_
  obtain ⟨G, hG⟩ := (memSobolev_iff_exists_hasWeakLineDeriv F).1 hF 1 le_rfl fun _ => v
  have hc' : Continuous fun x => (fderiv ℝ χ x v : ℂ) :=
    Complex.continuous_ofReal.comp ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨C', hC'⟩ := hc'.bounded_above_of_compact_support
    ((hcs.fderiv_apply (𝕜 := ℝ) v).comp_left Complex.ofReal_zero)
  exact ⟨_, hasWeakLineDeriv_mulLp hG hχ hc hC hc' hC'⟩

/-- **The arithmetic of the pasting bound**: if `‖F‖ ≤ ∑_k a_k x_k`,
`‖G_i‖ ≤ ∑_k (a_k y_{k,i} + d_{k,i} x_k)` and `x_k + ∑_i y_{k,i} ≤ C_k Y`, then
`‖F‖ + ∑_i ‖G_i‖ ≤ (∑_k (a_k + ∑_i d_{k,i}) C_k) Y`. -/
theorem pasting_bound {ι κ : Type*} [Fintype ι] [Fintype κ] {nF : ℝ≥0∞}
    {nG : κ → ℝ≥0∞} {a x C : ι → ℝ≥0∞} {d y : ι → κ → ℝ≥0∞} {Y : ℝ≥0∞}
    (hF : nF ≤ ∑ k, a k * x k) (hG : ∀ i, nG i ≤ ∑ k, (a k * y k i + d k i * x k))
    (hxy : ∀ k, x k + ∑ i, y k i ≤ C k * Y) :
    nF + ∑ i, nG i ≤ (∑ k, (a k + ∑ i, d k i) * C k) * Y := by
  calc nF + ∑ i, nG i ≤ ∑ k, a k * x k + ∑ i, ∑ k, (a k * y k i + d k i * x k) :=
        add_le_add hF (Finset.sum_le_sum fun i _ => hG i)
    _ = ∑ k, (a k * (x k + ∑ i, y k i) + (∑ i, d k i) * x k) := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.sum_mul]
        ring
    _ ≤ ∑ k, (a k + ∑ i, d k i) * (C k * Y) := Finset.sum_le_sum fun k _ => by
        calc a k * (x k + ∑ i, y k i) + (∑ i, d k i) * x k
            ≤ a k * (x k + ∑ i, y k i) + (∑ i, d k i) * (x k + ∑ i, y k i) := by
              gcongr
              exact le_self_add
          _ = (a k + ∑ i, d k i) * (x k + ∑ i, y k i) := by ring
          _ ≤ _ := mul_le_mul_right (hxy k) _
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring

/-- **Pasting bounded extensions**: let `(U_k)` be a finite cover of `Ō` by bounded open sets and
let Sobolev functions on `O` extend from every `O ∩ U_k` with finite constants. Then they extend
from `O` with a finite constant: for a smooth resolution of unity `(ψ_k)` subordinate to `(U_k)`
(`Rd.exists_smooth_partition`), `F = ∑_k ψ_k F_k` agrees with `f` on `O`, lies in `W^1_p(V)`
(`Rd.MemSobolev.mulLp`) and has the weak derivatives `∑_k (ψ_k ∂_{e_i} F_k + (∂_{e_i} ψ_k) F_k)`
(`Rd.hasWeakLineDeriv_mulLp`). -/
theorem extendsSobolev_of_cover [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {O : Opens V} (U : ι → Set V)
    (hUo : ∀ k, IsOpen (U k)) (hUb : ∀ k, Bornology.IsBounded (U k))
    (hcov : closure (O : Set V) ⊆ ⋃ k, U k) {C : ι → ℝ≥0∞} (hC : ∀ k, C k ≠ ∞)
    (hext : ∀ k, ExtendsSobolev p O ((O : Set V) ∩ U k) (C k)) :
    ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ ExtendsSobolev p O O C' := by
  classical
  obtain ⟨ψ, hψ, hψU, hψ1, -⟩ := exists_smooth_partition isClosed_closure U hUo hcov
  have hcs : ∀ k, HasCompactSupport (ψ k) := fun k =>
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) ((hUb k).subset (hψU k))
  have hc : ∀ k, Continuous fun x => ((ψ k x : ℝ) : ℂ) := fun k =>
    Complex.continuous_ofReal.comp (hψ k).continuous
  have hc' : ∀ k i, Continuous fun x => ((fderiv ℝ (ψ k) x (gridBasis V i) : ℝ) : ℂ) :=
    fun k i => Complex.continuous_ofReal.comp
      (((hψ k).continuous_fderiv (by simp)).clm_apply continuous_const)
  choose a ha using fun k =>
    (hc k).bounded_above_of_compact_support ((hcs k).comp_left Complex.ofReal_zero)
  choose d hd using fun k i => (hc' k i).bounded_above_of_compact_support
    (((hcs k).fderiv_apply (𝕜 := ℝ) (gridBasis V i)).comp_left Complex.ofReal_zero)
  refine ⟨∑ k, (ENNReal.ofReal (a k) + ∑ i, ENNReal.ofReal (d k i)) * C k,
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top⟩) (hC k), ?_⟩
  intro f g hf hg hfg
  choose F hF hFf G hG hb using fun k => hext k f g hf hg hfg
  refine ⟨∑ k, mulLp (hc k) (ha k) (F k), MemSobolev.sum _ fun k _ =>
    (hF k).mulLp (hψ k) (hcs k) (hc k) (ha k), ?_,
    fun i => ∑ k, (mulLp (hc k) (ha k) (G k i) + mulLp (hc' k i) (hd k i) (F k)), fun i => ?_, ?_⟩
  · have hall : ∀ᵐ x ∂(volume : Measure V), ∀ k, (x ∈ (O : Set V) ∩ U k → F k x = f x) ∧
        mulLp (hc k) (ha k) (F k) x = ((ψ k x : ℝ) : ℂ) * F k x :=
      ae_all_iff.2 fun k => (hFf k).and (mulLp_apply_ae _ _ (F k))
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun k => mulLp (hc k) (ha k) (F k), hall]
      with x h1 h2 hxO
    have hterm : ∀ k, mulLp (hc k) (ha k) (F k) x = ((ψ k x : ℝ) : ℂ) * f x := fun k => by
      rw [(h2 k).2]
      by_cases hψx : ψ k x = 0
      · simp [hψx]
      · rw [(h2 k).1 ⟨hxO, hψU k (subset_tsupport _ hψx)⟩]
    rw [h1]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hψ1 x (subset_closure hxO), Complex.ofReal_one,
      one_mul]
  · refine (HasWeakLineDeriv.sum (s := Finset.univ) fun k _ => hasWeakLineDeriv_mulLp (hG k i)
      (hψ k) (hc k) (ha k) (hc' k i) (hd k i)).congr_ae ?_ ?_ <;> rw [volume_restrict_top]
    · exact (Lp.coeFn_finsetSum _ _).symm
    · exact (Lp.coeFn_finsetSum _ _).symm
  · refine pasting_bound (x := fun k => ‖F k‖ₑ) (y := fun k i => ‖G k i‖ₑ)
      ((enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => enorm_mulLp_le _ _ _))
      (fun i => (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (enorm_add_le _ _).trans
        (add_le_add (enorm_mulLp_le _ _ _) (enorm_mulLp_le _ _ _)))) hb

/-! ### The supports of the divergence kernels -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- If a divergence kernel is nonzero at `y`, the moment kernel is nonzero at some `t y` with
`t ∈ [1, 2]` (`Rd.LocalMeansBump.divKernel_eq_zero`). -/
theorem exists_momentKernel_ne_zero_of_divKernel_ne_zero (i : Fin (finrank ℝ V)) {y : V}
    (hy : b.divKernel i y ≠ 0) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ 2 ∧ momentKernel b.toFun 2 (t • y) ≠ 0 := by
  by_contra h
  push Not at h
  exact hy (b.divKernel_eq_zero i h)

/-- **The supports of the dilated divergence kernels**: if the divergence kernel `K_i` vanishes
outside a closed set `S` with `c y ∈ S ⇒ y ∈ S` for `c ≥ 1`, then every dilate `(K_i)_{2^j}` is
supported in `S`. -/
theorem tsupport_dilate_divKernel_subset (i : Fin (finrank ℝ V)) {S : Set V} (hS : IsClosed S)
    (hK : ∀ y, b.divKernel i y ≠ 0 → y ∈ S) (hscale : ∀ c : ℝ, 1 ≤ c → ∀ y, c • y ∈ S → y ∈ S)
    (j : ℕ) : tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ⊆ S :=
  closure_minimal (fun y hy => hscale (2 ^ j) (one_le_pow₀ one_le_two) y
    (hK _ fun h => hy (by simp [dilate, h]))) hS

/-- The divergence kernels of a bump of radius `R` and their dilates `(K_i)_{2^j}` are supported
in the closed ball of radius `2R`. -/
theorem tsupport_dilate_divKernel_subset_closedBall (i : Fin (finrank ℝ V)) (j : ℕ) :
    tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ⊆ closedBall 0 (2 * b.radius) := by
  refine b.tsupport_dilate_divKernel_subset i isClosed_closedBall (fun y hy => ?_)
    (fun c hc y hy => ?_) j
  · obtain ⟨t, ht1, -, ht⟩ := b.exists_momentKernel_ne_zero_of_divKernel_ne_zero i hy
    have h := not_lt.1 fun h => ht (b.momentKernel_two_eq_zero h)
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht1)] at h
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg y]
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (zero_le_one.trans hc)]
      at hy
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg y]

end LocalMeansBump

namespace LipschitzGraph

variable (G : LipschitzGraph V)

/-- **The divergence kernels of a cone-supported bump lie in the reflected closed cone**: for a bump
of radius `R` supported in `-K`, every dilate `(K_i)_{2^j}` of its divergence kernels is supported
in `{y : -y ∈ K̄, ‖y‖ ≤ 2R}`. -/
theorem tsupport_dilate_divKernel_subset {b : LocalMeansBump V} (hb : G.ConeSupported b.toFun)
    (i : Fin (finrank ℝ V)) (j : ℕ) :
    tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ⊆
      {y | -y ∈ G.closedCone} ∩ closedBall 0 (2 * b.radius) := by
  refine Set.subset_inter (b.tsupport_dilate_divKernel_subset i
    (G.isClosed_closedCone.preimage continuous_neg) (fun y hy => ?_) (fun c hc y hy => ?_) j)
    (b.tsupport_dilate_divKernel_subset_closedBall i j)
  · obtain ⟨t, ht1, -, ht⟩ := b.exists_momentKernel_ne_zero_of_divKernel_ne_zero i hy
    have h := G.smul_mem_closedCone (inv_nonneg.2 (zero_le_one.trans ht1))
      (G.cone_subset_closedCone (G.coneSupported_momentKernel_of hb 2 _ ht))
    rwa [smul_neg, inv_smul_smul₀ (zero_lt_one.trans_le ht1).ne'] at h
  · have h := G.smul_mem_closedCone (inv_nonneg.2 (zero_le_one.trans hc)) hy
    rwa [smul_neg, inv_smul_smul₀ (zero_lt_one.trans_le hc).ne'] at h

/-- **Boundary patches, the support condition for the divergence kernels**: for a bump supported in
`-K` with `2R ≤ ε`, `x - y ∈ Ω ∩ B(c, ρ)` for `x ∈ Ω ∩ B(c, ρ - ε)` and `y` in the support of a
dilated divergence kernel (`Rd.LipschitzGraph.sub_mem_patch_of_mem_closedCone`). -/
theorem patch_support_divKernel {b : LocalMeansBump V} (hb : G.ConeSupported b.toFun)
    {ε ρ : ℝ} {c : V} (hR : 2 * b.radius ≤ ε) :
    ∀ x ∈ G.domain ∩ ball c (ρ - ε), ∀ (j : ℕ) (i : Fin (finrank ℝ V)),
      ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ G.domain ∩ ball c ρ := by
  intro x hx j i y hy
  obtain ⟨hyK, hyR⟩ := G.tsupport_dilate_divKernel_subset hb i j hy
  rw [mem_closedBall, dist_zero_right] at hyR
  exact G.sub_mem_patch_of_mem_closedCone hx hyK (hyR.trans hR)

end LipschitzGraph

/-! ### Dimension zero -/

/-- **Extension in dimension `0`**: if `V` is a single point, every `f ∈ W^1_p(O)` on an open set
`O` agrees almost everywhere on `O` with some `F ∈ W^1_p(V)`. Here `O` is empty, and `F = 0`
serves, or `O = V`, and `F = f` serves (Mathlib's `Subsingleton.eq_univ_of_nonempty`). -/
theorem exists_memSobolev_of_memWeakSobolev_of_subsingleton [Subsingleton V] {O : Opens V}
    {f : V → ℂ} (hf : MemWeakSobolev O 1 p f) :
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev 1 F ∧ (F : V → ℂ) =ᵐ[volume.restrict O] f := by
  rcases (O : Set V).eq_empty_or_nonempty with h | h
  · refine ⟨0, zero_memSobolev, ?_⟩
    rw [h, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  · obtain rfl : O = ⊤ :=
      Opens.ext ((Subsingleton.eq_univ_of_nonempty h).trans Opens.coe_top.symm)
    have hf1 : MemLp f p volume := volume_restrict_top (V := V) ▸ hf.1
    refine ⟨hf1.toLp f, hf.congr_ae ?_, ?_⟩ <;> rw [volume_restrict_top]
    · exact hf1.coeFn_toLp.symm
    · exact hf1.coeFn_toLp

/-! ### The extension theorem -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- If `‖x‖ + ∑_i ‖y_i‖ ≤ K` in `ℝ≥0∞` with `K` finite, then `‖x‖² + ∑_i ‖y_i‖² ≤ K²` in `ℝ`. -/
theorem sq_norm_add_sum_sq_le {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι] {x : E}
    {y : ι → E} {K : ℝ≥0∞} (hK : K ≠ ∞) (h : ‖x‖ₑ + ∑ i, ‖y i‖ₑ ≤ K) :
    ‖x‖ ^ 2 + ∑ i, ‖y i‖ ^ 2 ≤ K.toReal ^ 2 := by
  have hr : ‖x‖ + ∑ i, ‖y i‖ ≤ K.toReal := by
    have h1 := ENNReal.toReal_mono hK h
    rw [ENNReal.toReal_add enorm_ne_top (ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top),
      ENNReal.toReal_sum fun _ _ => enorm_ne_top] at h1
    simpa only [toReal_enorm] using h1
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) fun i _ => norm_nonneg (y i)
  have h0 : 0 ≤ ∑ i, ‖y i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  nlinarith [norm_nonneg x]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The boundary patches**: Sobolev functions on `Ω` extend from `Ω ∩ B(c_j, ρ_j - 2ε)` with a
finite constant, by the extension from one patch (`Rd.LocalMeansBump.extendsSobolev`) with the cone
bump of `Ω_j` rescaled to radius `≤ ε / 2`. -/
theorem exists_extendsSobolev_boundary [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {ε : ℝ}
    (hε : 0 < ε) (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens
      (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  set G := Ω.graph j
  set c := Ω.center j
  set ρ := Ω.radius j
  have hc0 : 0 < 1 + 1 / ε := by positivity
  set b := G.coneBump.rescale hc0
  have hbR : b.radius = (1 / 2) / (1 + 1 / ε) := by
    rw [LocalMeansBump.rescale_radius, G.coneBump_radius]
  have hR : 2 * b.radius ≤ ε := by
    rw [hbR, show 2 * ((1 : ℝ) / 2 / (1 + 1 / ε)) = ε / (ε + 1) by field_simp]
    exact div_le_self hε.le (by linarith)
  have hLR : ((2 : ℕ) : ℝ) * b.radius ≤ ε := by exact_mod_cast hR
  have hb : G.ConeSupported b.toFun := G.coneSupported_rescale G.coneSupported_coneBump hc0
  have hTo : IsOpen (G.domain ∩ ball c ρ) := G.isOpen_domain.inter isOpen_ball
  have hTΩ : (⟨_, hTo⟩ : Opens V) ≤ Ω.toOpens := by
    show G.domain ∩ ball c ρ ⊆ Ω.carrier
    rw [← Ω.inter_ball_eq j le_rfl]
    exact Set.inter_subset_left
  have hU : Ω.carrier ∩ ball c (ρ - 2 * ε) = G.domain ∩ ball c (ρ - 2 * ε) :=
    Ω.inter_ball_eq j (by linarith)
  refine ⟨b.extensionConst p, b.extensionConst_ne_top hp1 hp, ?_⟩
  rw [hU]
  exact (b.extendsSobolev hp1 hp ((G.isOpen_domain.inter isOpen_ball).measurableSet)
    ((G.isOpen_domain.inter isOpen_ball).measurableSet) (T := ⟨_, hTo⟩)
    (Set.inter_subset_inter_right _ (ball_subset_ball (by linarith)))
    (G.patch_support hb hLR) (G.patch_support_divKernel hb hR)).of_le hTΩ

/-- **The inner patch**: Sobolev functions on `Ω` extend from `{infDist(·, Ωᶜ) > 2δ}` with a finite
constant, by the extension from one patch (`Rd.LocalMeansBump.extendsSobolev`) with a centred bump
of radius `≤ δ / 2`. -/
theorem exists_extendsSobolev_interior [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens
      (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  have hR0 : 0 < δ / 2 := by positivity
  set b := LocalMeansBump.centered (V := V) hR0
  have hR : 2 * b.radius = δ := by rw [LocalMeansBump.centered_radius]; ring
  have hUΩ := setOf_lt_infDist_compl_subset Ω.carrier (by positivity : (0 : ℝ) ≤ 2 * δ)
  refine ⟨b.extensionConst p, b.extensionConst_ne_top hp1 hp, ?_⟩
  rw [Set.inter_eq_right.2 hUΩ]
  refine b.extendsSobolev hp1 hp (measurableSet_infDist_gt Ω.carrier (2 * δ))
    (measurableSet_infDist_gt Ω.carrier δ) (T := Ω.toOpens) hUΩ
    (fun x hx j y hy => interior_patch_support Ω.carrier (fun y hy =>
      (not_lt.1 fun h => hy (b.dual_eq_zero 2 j h)).trans (by rw [← hR]; push_cast; rfl)) x hx y hy)
    (fun x hx j i y hy => ?_)
  have hy' := b.tsupport_dilate_divKernel_subset_closedBall i j hy
  rw [mem_closedBall, dist_zero_right, hR] at hy'
  have hx' : dist x (x - y) < infDist x Ω.carrierᶜ := by
    rw [dist_eq_norm, sub_sub_cancel]
    exact hy'.trans_lt hx
  show x - y ∈ Ω.carrier
  simpa using notMem_of_dist_lt_infDist hx'

/-- **The extension theorem with a bound**: for a bounded Lipschitz domain `Ω` in dimension
`n ≥ 1` and `1 < p < ∞` there is a finite constant `C` such that every `f ∈ L_p(Ω)` with weak
derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` agrees on `Ω` with some `F ∈ W^1_p(V)` whose weak
derivatives `G_i = ∂_{e_i} F` satisfy
`‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`. The patches
`Rd.BoundedLipschitzDomain.patch` cover `Ω̄`
(`Rd.BoundedLipschitzDomain.exists_extendsSobolev_boundary`,
`Rd.BoundedLipschitzDomain.exists_extendsSobolev_interior`), pasted by
`Rd.extendsSobolev_of_cover`. -/
theorem exists_extendsSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolev p Ω.toOpens Ω.carrier C := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  obtain ⟨ε, hε0, hε⟩ := Ω.exists_shrink
  obtain ⟨δ, hδ0, hδ⟩ := Ω.exists_interior_margin Ω.nonempty_compl hε
  choose Cb hCb hb using fun j => Ω.exists_extendsSobolev_boundary hp1 hp hε0 j
  obtain ⟨C0, hC0, h0⟩ := Ω.exists_extendsSobolev_interior hp1 hp hδ0
  refine extendsSobolev_of_cover (O := Ω.toOpens) (Ω.patch ε δ) (Ω.isOpen_patch ε δ)
    (Ω.isBounded_patch ε hδ0.le) (Ω.closure_subset_iUnion_patch hε hδ)
    (C := fun i => i.elim C0 Cb) (fun i => ?_) (fun i => ?_)
  · cases i with
    | none => exact hC0
    | some j => exact hCb j
  · cases i with
    | none => exact h0
    | some j => exact hb j

/-- **The extension theorem** (H.2; the extension theorem of Calderón and Stein, by Rychkov's
extension and the local means of the gradient): for a bounded Lipschitz domain `Ω` and
`1 < p < ∞`, every `f ∈ W^1_p(Ω)` agrees almost everywhere on `Ω` with some `F ∈ W^1_p(V)`
(`Rd.BoundedLipschitzDomain.exists_extendsSobolev` in dimension `n ≥ 1`,
`Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton` in dimension `0`). -/
theorem exists_memSobolev_of_memWeakSobolev (hp1 : 1 < p) (hp : p ≠ ∞)
    {f : V → ℂ} (hf : MemWeakSobolev Ω.toOpens 1 p f) :
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev 1 F ∧
      (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact exists_memSobolev_of_memWeakSobolev_of_subsingleton hf
  obtain ⟨C, -, hC⟩ := Ω.exists_extendsSobolev hp1 hp
  choose g hg hfg using fun i => hf.2 1 le_rfl fun _ => gridBasis V i
  obtain ⟨F, hF, hFf, -⟩ := hC f g hf.1 hg hfg
  exact ⟨F, hF, (ae_restrict_iff' Ω.measurableSet).2 hFf⟩

/-- **`W^1_p(Ω)` is the space of restrictions of `W^1_p(V)`**: for a bounded Lipschitz domain `Ω`
and `1 < p < ∞`, `f` lies in `W^1_p(Ω)` iff it agrees almost everywhere on
`Ω` with some `F ∈ W^1_p(V)` (`Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev`;
the converse restricts the weak derivatives, `Rd.MemWeakSobolev.mono_set`). -/
theorem memWeakSobolev_iff_exists_memSobolev (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : V → ℂ) :
    MemWeakSobolev Ω.toOpens 1 p f ↔ ∃ F : Lp ℂ p (volume : Measure V), MemSobolev 1 F ∧
      (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f := by
  refine ⟨Ω.exists_memSobolev_of_memWeakSobolev hp1 hp, ?_⟩
  rintro ⟨F, hF, hFf⟩
  exact (MemWeakSobolev.mono_set hF le_top).congr_ae hFf

/-- **`H^1(Ω) = W^1_2(Ω)`** (H.2 for `p = 2`): for a bounded Lipschitz domain `Ω`, `f ∈ L_2(V)`
lies in the restriction space `H^1(Ω)` iff it lies in the Sobolev space
`W^1_2(Ω)` of weak derivatives on `Ω`. -/
theorem memSobolevOn_iff_memWeakSobolev (f : Lp ℂ 2 (volume : Measure V)) :
    Ω.MemSobolevOn f ↔ MemWeakSobolev Ω.toOpens 1 2 f :=
  (Ω.memWeakSobolev_iff_exists_memSobolev ENNReal.one_lt_two ENNReal.ofNat_ne_top f).symm

/-- **Rellich's theorem in `W^1_2(Ω)`** (I.6 and H.1 in the weak-derivative form): for a bounded
Lipschitz domain `Ω` in dimension `n ≥ 1`, every sequence `f_n ∈ L_2(Ω)` with weak derivatives
`g_{n,i} = ∂_{e_i} f_n ∈ L_2(Ω)` and `‖f_n‖_{L_2(Ω)} + ∑_i ‖g_{n,i}‖_{L_2(Ω)} ≤ M` has a
subsequence converging in `L_2(Ω)`: the bounded extensions
(`Rd.BoundedLipschitzDomain.exists_extendsSobolev`) are bounded in `W^1_2(V)`, and Rellich's
compactness on `V` (`Rd.exists_subseq_tendsto_restr_of_hasWeakLineDeriv`) gives the subsequence.
-/
theorem exists_subseq_tendsto_of_memWeakSobolev [Nontrivial V] {f : ℕ → V → ℂ}
    {g : ℕ → Fin (finrank ℝ V) → V → ℂ} (hf : ∀ n, MemLp (f n) 2 (volume.restrict Ω.carrier))
    (hg : ∀ n i, MemLp (g n i) 2 (volume.restrict Ω.carrier))
    (hfg : ∀ n i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i) (f n) (g n i))
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hb : ∀ n, eLpNorm (f n) 2 (volume.restrict Ω.carrier) +
      ∑ i, eLpNorm (g n i) 2 (volume.restrict Ω.carrier) ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : Lp ℂ 2 (volume.restrict Ω.carrier),
      Tendsto (fun k => eLpNorm (f (φ k) - (u : V → ℂ)) 2 (volume.restrict Ω.carrier)) atTop
        (𝓝 0) := by
  obtain ⟨C, hC, hext⟩ := Ω.exists_extendsSobolev (p := 2) ENNReal.one_lt_two ENNReal.ofNat_ne_top
  choose F hF hFf G hG hFG using fun n => hext (f n) (g n) (hf n) (hg n) (hfg n)
  have hK : C * M ≠ ∞ := ENNReal.mul_ne_top hC hM
  obtain ⟨φ, hφ, u, hu⟩ := exists_subseq_tendsto_restr_of_hasWeakLineDeriv Ω.isBounded
    (gridBasis V) hG (M := (C * M).toReal) fun n =>
      Rd.sq_norm_add_sum_sq_le hK ((hFG n).trans (mul_le_mul_right (hb n) _))
  refine ⟨φ, hφ, u, ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hu).congr fun k => ?_⟩
  refine eLpNorm_congr_ae (EventuallyEq.sub ?_ EventuallyEq.rfl)
  exact (LpToLpRestrictCLM_coeFn ℂ _ _).trans ((ae_restrict_iff' Ω.measurableSet).2 (hFf (φ k)))

/-- **The quotient norm of `H^1(Ω)` is bounded by the `W^1_2(Ω)` norm**: for a bounded Lipschitz
domain `Ω` in dimension `n ≥ 1` there is a constant `C` such that every `u ∈ H^1(Ω)` and all
`g_i ∈ L_2(Ω)` with `g_i = ∂_{e_i} u` weakly on `Ω` (`u` read as its `L_2` function) satisfy
`‖u‖_{H^1(Ω)} ≤ C (‖u|_Ω‖_{L_2(Ω)} + ∑_i ‖g_i‖_{L_2(Ω)})`. With
`Rd.sq_norm_restrictL2_add_sum_le`, the quotient norm of `H^1(Ω)` and the `W^1_2(Ω)` norm are
equivalent. The bounded extension `F` of `u|_Ω` (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`)
is an element of `H^1(V)` whose restriction is `u`. -/
theorem exists_norm_le_restrictL2 [Nontrivial V] :
    ∃ C : ℝ, ∀ (u : RestrictionSpace 1 Ω.toOpens)
      (g : Fin (finrank ℝ V) → Lp ℂ 2 (volume.restrict Ω.carrier)),
      (∀ i, HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => gridBasis V i)
        (toL2 (u : H^{1}(V))) (g i)) →
      ‖u‖ ≤ C * (‖restrictL2 Ω.toOpens u‖ + ∑ i, ‖g i‖) := by
  obtain ⟨C, hC, hext⟩ := Ω.exists_extendsSobolev (p := 2) ENNReal.one_lt_two ENNReal.ofNat_ne_top
  refine ⟨C.toReal, fun u g hg => ?_⟩
  have hf : MemLp (toL2 (u : H^{1}(V)) : V → ℂ) 2 (volume.restrict Ω.carrier) :=
    (Lp.memLp _).restrict _
  obtain ⟨F, hF, hFf, G, hG, hb⟩ := hext _ (fun i => g i) hf (fun i => Lp.memLp (g i)) hg
  have hS := (memSobolev_one_iff F).1 hF
  have hU : toL2 hS.toBesselPotentialSpace = F :=
    toL2_eq_of_toDistr_eq _ hS.toBesselPotentialSpace_toDistr.symm
  have hproj : restrictProj 1 Ω.toOpens hS.toBesselPotentialSpace = u := by
    refine restrictL2_injective (Ω := Ω.toOpens) ?_
    rw [restrictL2_restrictProj, hU]
    have hFu : (F : V → ℂ) =ᵐ[volume.restrict (Ω.toOpens : Set V)] (toL2 (u : H^{1}(V)) : V → ℂ) :=
      (ae_restrict_iff' Ω.measurableSet).2 hFf
    exact ((restrictL2_eq_iff_ae_eq u F).2 hFu.symm).symm
  have hY : eLpNorm (toL2 (u : H^{1}(V)) : V → ℂ) 2 (volume.restrict (Ω.toOpens : Set V)) +
      ∑ i, eLpNorm (g i : V → ℂ) 2 (volume.restrict (Ω.toOpens : Set V)) =
      ENNReal.ofReal (‖restrictL2 Ω.toOpens u‖ + ∑ i, ‖g i‖) := by
    rw [ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _),
      ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _, ofReal_norm, restrictL2_apply,
      Lp.enorm_def, eLpNorm_congr_ae (LpToLpRestrictCLM_coeFn ℂ _ _)]
    simp_rw [ofReal_norm, Lp.enorm_def]
    rfl
  rw [hY] at hb
  have hFG : ‖F‖ + ∑ i, ‖G i‖ ≤ C.toReal * (‖restrictL2 Ω.toOpens u‖ + ∑ i, ‖g i‖) := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hb
    rw [ENNReal.toReal_add enorm_ne_top (ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top),
      ENNReal.toReal_sum fun _ _ => enorm_ne_top, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)] at h1
    simpa only [toReal_enorm] using h1
  calc ‖u‖ = ‖restrictProj 1 Ω.toOpens hS.toBesselPotentialSpace‖ := by rw [hproj]
    _ ≤ ‖hS.toBesselPotentialSpace‖ := norm_restrictProj_apply_le _
    _ ≤ ‖toL2 hS.toBesselPotentialSpace‖ + ∑ i, ‖G i‖ :=
        norm_le_norm_toL2_add_sum (gridBasis V) _ fun i => by rw [hU]; exact hG i
    _ ≤ _ := by rw [hU]; exact hFG

/-- **`W^1_2(Ω)` and the Hilbert space `H^1(Ω)`**: for a bounded Lipschitz domain `Ω`,
`f ∈ L_2(V)` lies in `W^1_2(Ω)` iff its restriction to `Ω` is `u|_Ω` for some `u` in
the Hilbert space `H^1(Ω)` (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`,
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`). -/
theorem memWeakSobolev_iff_exists_restrictL2 (f : Lp ℂ 2 (volume : Measure V)) :
    MemWeakSobolev Ω.toOpens 1 2 f ↔ ∃ u : RestrictionSpace 1 Ω.toOpens,
      restrictL2 Ω.toOpens u = LpToLpRestrictCLM V ℂ ℂ volume 2 Ω.carrier f := by
  rw [← Ω.memSobolevOn_iff_memWeakSobolev f, Ω.memSobolevOn_iff_exists_restrictL2 f]

/-- **The boundary trace of a function of `W^1_2(Ω)`**: for a bounded Lipschitz domain `Ω`, every
resolution of unity `ψ` on the boundary `Γ` and every `f ∈ L_2(V)` whose restriction lies in
`W^1_2(Ω)`, `f` has a boundary trace `g ∈ B^{1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memSobolevOn` through
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`). -/
theorem exists_isBoundaryTrace_of_memWeakSobolev (ψ : Ω.BoundaryPartition)
    {f : Lp ℂ 2 (volume : Measure V)} (hf : MemWeakSobolev Ω.toOpens 1 2 f) :
    ∃ g : V → ℂ, Ω.MemBoundaryBesov 2 ψ (1 / 2) 2 g ∧
      Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g :=
  exists_isBoundaryTrace_of_memSobolevOn ψ ((Ω.memSobolevOn_iff_memWeakSobolev f).2 hf)

/-- **The boundary trace of a function of `W^1_2(Ω)` is unique** up to null sets of the boundary:
for every resolution of unity `ψ` on `Γ` and every `f ∈ L_2(V)` whose restriction lies in
`W^1_2(Ω)`, two boundary traces `g`, `g'` of `f` agree almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.MemSobolevOn.isBoundaryTrace_unique` through
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`). -/
theorem isBoundaryTrace_unique_of_memWeakSobolev (ψ : Ω.BoundaryPartition)
    {f : Lp ℂ 2 (volume : Measure V)} (hf : MemWeakSobolev Ω.toOpens 1 2 f) {g g' : V → ℂ}
    (hg : Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g)
    (hg' : Ω.IsBoundaryTrace ψ two_ne_top 2 1 2 f g') : g =ᶠ[Ω.aeBoundary] g' :=
  MemSobolevOn.isBoundaryTrace_unique ψ ((Ω.memSobolevOn_iff_memWeakSobolev f).2 hf) hg hg'

end BoundedLipschitzDomain

end Rd
