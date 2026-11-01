/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.TriebelLizorkin.SquareFunction
public import FunctionSpaces.Analysis.Fourier.SchwartzCutoff

/-!
# Triebel–Lizorkin spaces of tempered distributions

The Littlewood–Paley blocks of a tempered distribution `u` on `V` are the Fourier multipliers
`Δ_j u = (𝓕ψ_j)(D) u` (`Rd.distribBlock`), with the blocks `ψ_j` as Schwartz functions
(`Rd.psiS`). A tempered distribution lies in `F^s_{p,q}` when every block is an `L_p` function
`g_j` and `‖ x ↦ ‖(2^{js} |g_j(x)|)_j‖_{ℓ_q} ‖_p < ∞` (`Rd.triebelLizorkinNormDistr`,
`Rd.MemTriebelLizorkinDistr`); the quasi-norm is `∞` when some block is no `L_p` function. This
describes `F^s_{p,q}` for every real `s`, without the restriction to `L_p`.

* **Convolutions as Fourier multipliers**: for a Schwartz function `η`, `(𝓕η)(D) φ = η ⋆ φ` for
  Schwartz functions `φ`, Mathlib's convolution of Schwartz functions
  (`Rd.fourierMultiplierCLM_fourier_eq_convolution`, `Rd.fourierMultiplierCLM_fourier_eq_conv`),
  and, since Schwartz functions are dense in `L_r`, `(𝓕η)(D) G = η ⋆ G` for `G ∈ L_r`, `1 ≤ r < ∞`
  (`Rd.fourierMultiplierCLM_fourier_toLp_eq_conv`). In particular the blocks of an `L_r`
  function are its blocks `ψ_j ⋆ f` (`Rd.distribBlock_toTemperedDistribution`). Finite sums of
  such convolutions in `L_p` are the pointwise sums (`Rd.coeFn_sum_convLp_ae`).
* **The decomposition converges**: `∑_{j < J} Δ_j u → u` in `𝓢'` for every tempered
  distribution `u` (`Rd.tendsto_sum_distribBlock`), since `∑_{j ≤ J} 𝓕ψ_j = χ(2^{-J} ·)` and the
  cut-offs converge in the Schwartz space (`Rd.tendsto_cutoffMul`). If the blocks are `L_p`
  functions whose partial sums converge in `L_p`, the limit is `u`
  (`Rd.eq_of_tendsto_sum_distribBlock`).
* **The quasi-norm**: the blocks determine their `L_p` functions, so the quasi-norm is that of the
  unique family (`Rd.triebelLizorkinNormDistr_eq`); for `f ∈ L_p` it is the Triebel–Lizorkin
  quasi-norm of `f` (`Rd.triebelLizorkinNormDistr_toTemperedDistribution`); it decreases in `q`
  and increases in `s`; when it is finite, the blocks are `L_p` functions
  (`Rd.MemTriebelLizorkinDistr.exists_blocks`). The weighted `ℓ_q` norm of a family of `L_p`
  functions is almost everywhere measurable (`Rd.aemeasurable_lqNorm_dyadicWeight_Lp`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal SchwartzMap FourierTransform

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Convolutions as Fourier multipliers -/

/-- **Mathlib's convolution of Schwartz functions as a Fourier multiplier**: for Schwartz
functions `η` and `φ`, `(𝓕η)(D) φ` is Mathlib's convolution `SchwartzMap.convolution` of `η` and
`φ` with the multiplication of `ℂ`, since both have the Fourier transform `𝓕η 𝓕φ` (Mathlib's
`SchwartzMap.fourier_convolution`) and the Fourier transform is injective. -/
theorem fourierMultiplierCLM_fourier_eq_convolution (η φ : 𝓢(V, ℂ)) :
    SchwartzMap.fourierMultiplierCLM ℂ (𝓕 η : 𝓢(V, ℂ)) φ =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) η φ := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(V, ℂ)).injective
  ext ξ
  simp only [FourierTransform.fourierCLE_apply, SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, SchwartzMap.fourierMultiplierCLM_apply,
    FourierInvPair.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (𝓕 η).hasTemperateGrowth, smul_eq_mul,
    ContinuousLinearMap.mul_apply']

/-- **Convolution as a Fourier multiplier on Schwartz functions**: for Schwartz functions `η` and
`φ`, `(𝓕η)(D) φ = η ⋆ φ` (`Rd.fourierMultiplierCLM_fourier_eq_convolution`, and Mathlib's
`SchwartzMap.convolution_apply` for the convolution integral). -/
theorem fourierMultiplierCLM_fourier_eq_conv (η φ : 𝓢(V, ℂ)) :
    ⇑(SchwartzMap.fourierMultiplierCLM ℂ (𝓕 η : 𝓢(V, ℂ)) φ) = conv η φ volume := by
  rw [fourierMultiplierCLM_fourier_eq_convolution]
  exact funext (SchwartzMap.convolution_apply _ η φ)

/-- **Convolution as a Fourier multiplier on `L_r`**: for a Schwartz function `η`, `1 ≤ r < ∞`
and `G ∈ L_r(V)`, `(𝓕η)(D) G = η ⋆ G` as tempered distributions. Both sides are continuous in
`G` (Mathlib's `MeasureTheory.Lp.toTemperedDistributionCLM`, `Rd.convLp`), they agree on
Schwartz functions (`Rd.fourierMultiplierCLM_fourier_eq_conv`, Mathlib's
`TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq`), and Schwartz
functions are dense in `L_r` (Mathlib's `SchwartzMap.denseRange_toLpCLM`,
`DenseRange.equalizer`). -/
theorem fourierMultiplierCLM_fourier_toLp_eq_conv {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : r ≠ ∞)
    (η : 𝓢(V, ℂ)) (G : Lp ℂ r (volume : Measure V)) :
    TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 η : 𝓢(V, ℂ)) (G : 𝓢'(V, ℂ)) =
      (convLp hr η.integrable G : 𝓢'(V, ℂ)) := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := V) hr (μ := volume)
  have h := hd.equalizer
    ((TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 η : 𝓢(V, ℂ))).continuous.comp
      (Lp.toTemperedDistributionCLM ℂ volume r).continuous)
    ((Lp.toTemperedDistributionCLM ℂ volume r).continuous.comp
      (convLp hr η.integrable).continuous)
    (funext fun φ => ?_)
  · exact congrFun h G
  simp only [Function.comp_apply, Lp.toTemperedDistributionCLM_apply,
    SchwartzMap.toLpCLM_apply]
  rw [Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
      (𝓕 η).hasTemperateGrowth, ← Lp.toTemperedDistribution_toLp_eq (p := r) (μ := volume)]
  refine (toTemperedDistribution_eq_of_ae_eq ?_).symm
  filter_upwards [convLp_apply_ae hr η.integrable (φ.toLp r volume),
    (SchwartzMap.fourierMultiplierCLM ℂ (𝓕 η : 𝓢(V, ℂ)) φ).coeFn_toLp r volume] with x h1 h2
  rw [h1, h2, fourierMultiplierCLM_fourier_eq_conv,
    conv_congr_ae (φ.coeFn_toLp r volume)]

/-! ### The blocks of tempered distributions -/

/-- `𝓕(psiS j)` is the Fourier transform `𝓕ψ_j` of the block. -/
theorem fourier_psiS_apply (j : ℕ) (ξ : V) :
    (𝓕 (psiS (V := V) j) : 𝓢(V, ℂ)) ξ = 𝓕 (psi (V := V) j) ξ := by
  rw [SchwartzMap.fourier_coe, coe_psiS]

/-- The **Littlewood–Paley block of a tempered distribution**, `Δ_j u = (𝓕ψ_j)(D) u`, Mathlib's
Fourier multiplier with the Fourier transform of the block `ψ_j`. -/
noncomputable def distribBlock (j : ℕ) : 𝓢'(V, ℂ) →L[ℂ] 𝓢'(V, ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ (𝓕 (psiS (V := V) j) : 𝓢(V, ℂ))

/-- **The blocks of an `L_r` function**: for `1 ≤ r < ∞` and `f ∈ L_r(V)`, the block of the
tempered distribution of `f` is that of the `L_r` block `ψ_j ⋆ f` (`Rd.lpBlock`), by
`Rd.fourierMultiplierCLM_fourier_toLp_eq_conv`. -/
theorem distribBlock_toTemperedDistribution {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : r ≠ ∞) (j : ℕ)
    (f : Lp ℂ r (volume : Measure V)) :
    distribBlock j (f : 𝓢'(V, ℂ)) = (lpBlock hr j f : 𝓢'(V, ℂ)) := by
  rw [distribBlock, fourierMultiplierCLM_fourier_toLp_eq_conv hr]
  refine toTemperedDistribution_eq_of_ae_eq ?_
  filter_upwards [lpBlock_ae_eq_blockFun hr j f,
    convLp_apply_ae hr (psiS (V := V) j).integrable f] with x h1 h2
  rw [h1, h2, blockFun, coe_psiS]

/-! ### The decomposition of tempered distributions -/

/-- **The Fourier transforms of the blocks add up to a cut-off**:
`∑_{j ≤ J} 𝓕ψ_j(ξ) = χ(2^{-J} ξ)` with `χ = Rd.cutoff 1 2` (`Rd.sum_range_fourier_psi`,
`Rd.fourier_Phi`). -/
theorem sum_fourier_psiS_apply (J : ℕ) (ξ : V) :
    ∑ j ∈ Finset.range (J + 1), (𝓕 (psiS (V := V) j) : 𝓢(V, ℂ)) ξ =
      cutoff 1 2 one_pos one_lt_two (((2 : ℝ) ^ J)⁻¹ • ξ) := by
  simp_rw [fourier_psiS_apply]
  rw [sum_range_fourier_psi, fourier_Phi]

/-- **Partial sums of the blocks as one multiplier**: `∑_{j ≤ J} Δ_j u` is the Fourier multiplier
with `χ(2^{-J} ·)` (Mathlib's `TemperedDistribution.fourierMultiplierCLM_sum`,
`Rd.sum_fourier_psiS_apply`). -/
theorem sum_distribBlock (J : ℕ) (u : 𝓢'(V, ℂ)) :
    ∑ j ∈ Finset.range (J + 1), distribBlock j u =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ => ∑ j ∈ Finset.range (J + 1), (𝓕 (psiS (V := V) j) : 𝓢(V, ℂ)) ξ) u := by
  rw [TemperedDistribution.fourierMultiplierCLM_sum ℂ fun j _ =>
    (𝓕 (psiS (V := V) j)).hasTemperateGrowth]
  simp only [FunLike.coe_sum, Finset.sum_apply, distribBlock]

/-- **The cut-off of the inverse Fourier transform**: multiplying a Schwartz function `w` by
`∑_{j ≤ J} 𝓕ψ_j = χ(2^{-J} ·)` is the cut-off `Rd.cutoffMul (2^J - 1) w` at radius `2^J`
(`Rd.sum_fourier_psiS_apply`, `Rd.cutoffMul_apply`). -/
theorem smulLeftCLM_sum_fourier_psiS (J : ℕ) (w : 𝓢(V, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ
        (fun ξ => ∑ j ∈ Finset.range (J + 1), (𝓕 (psiS (V := V) j) : 𝓢(V, ℂ)) ξ) w =
      cutoffMul (2 ^ J - 1) w := by
  have hg : (fun ξ => ∑ j ∈ Finset.range (J + 1),
      (𝓕 (psiS (V := V) j) : 𝓢(V, ℂ)) ξ).HasTemperateGrowth :=
    Function.HasTemperateGrowth.sum fun j _ => (𝓕 (psiS (V := V) j)).hasTemperateGrowth
  have hcast : (((2 ^ J - 1 : ℕ) : ℝ) + 1) = (2 : ℝ) ^ J := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, sum_fourier_psiS_apply, cutoffMul_apply, hcast,
    smul_eq_mul]

/-- **The Littlewood–Paley decomposition of tempered distributions**: for every tempered
distribution `u` on `V`, `∑_{j < J} Δ_j u → u` in `𝓢'(V, ℂ)`. Tested against a Schwartz function
`φ`, `∑_{j ≤ J} Δ_j u (φ) = u(𝓕(χ_J 𝓕⁻¹ φ))` with the cut-offs `χ_J = χ(2^{-J} ·)`
(`Rd.sum_distribBlock`, `Rd.smulLeftCLM_sum_fourier_psiS`), and `χ_J 𝓕⁻¹ φ → 𝓕⁻¹ φ` in the
Schwartz space (`Rd.tendsto_cutoffMul`); `𝓕` and `u` are continuous. -/
theorem tendsto_sum_distribBlock (u : 𝓢'(V, ℂ)) :
    Tendsto (fun J => ∑ j ∈ Finset.range J, distribBlock j u) atTop (𝓝 u) := by
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  intro φ
  have hJ : Tendsto (fun J : ℕ => 2 ^ J - 1) atTop atTop :=
    tendsto_sub_atTop_nat 1 |>.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hlim : Tendsto (fun J : ℕ => u (𝓕 (cutoffMul (2 ^ J - 1) (𝓕⁻ φ)))) atTop
      (𝓝 (u (𝓕 (𝓕⁻ φ)))) :=
    (u.continuous.comp (FourierTransform.fourierCLM ℂ 𝓢(V, ℂ)).continuous).continuousAt.tendsto.comp
      ((tendsto_cutoffMul (𝓕⁻ φ)).comp hJ)
  rw [FourierInvPair.fourier_fourierInv_eq] at hlim
  refine hlim.congr fun J => ?_
  rw [sum_distribBlock, TemperedDistribution.fourierMultiplierCLM_apply_apply,
    smulLeftCLM_sum_fourier_psiS]

/-! ### The Triebel–Lizorkin quasi-norm of tempered distributions -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **partial sums of convolutions in `L_p`**: for Schwartz kernels `K_j`, `g_j ∈ L_p(V)`,
`1 ≤ p < ∞` and a finite set `t`, the sum `∑_{j ∈ t} K_j ⋆ g_j` of the classes in `L_p(V)` is
almost everywhere the pointwise sum of the convolutions (`Rd.convLp_apply_ae`). -/
theorem coeFn_sum_convLp_ae (hp : p ≠ ∞) (K : ℕ → 𝓢(V, ℂ))
    (g : ℕ → Lp ℂ p (volume : Measure V)) (t : Finset ℕ) :
    ⇑(∑ j ∈ t, convLp hp (K j).integrable (g j)) =ᵐ[volume]
      fun x => ∑ j ∈ t, conv (K j) (g j) volume x := by
  filter_upwards [ae_all_iff.2 fun j => convLp_apply_ae hp (K j).integrable (g j),
    Lp.coeFn_fun_finsetSum t fun j => convLp hp (K j).integrable (g j)] with x hx1 hx2
  rw [hx2]
  exact Finset.sum_congr rfl fun j _ => hx1 j

omit [Fact (1 ≤ p)] in
/-- The weighted `L_p` blocks of a family `g` are almost everywhere measurable, and so is their
pointwise `ℓ_q` norm `x ↦ ‖(2^{js} |g_j(x)|)_j‖_{ℓ_q}`. -/
theorem aemeasurable_lqNorm_dyadicWeight_Lp (s : ℝ) (q : ℝ≥0∞)
    (g : ℕ → Lp ℂ p (volume : Measure V)) :
    AEMeasurable (fun x => lqNorm q fun j => dyadicWeight s j * ‖g j x‖ₑ) volume :=
  aemeasurable_lqNorm_comp (fun j => (Lp.aestronglyMeasurable (g j)).enorm.const_mul _) q

variable (p) in
/-- The **Triebel–Lizorkin quasi-norm of a tempered distribution** `u`:
`‖ x ↦ ‖(2^{js} |g_j(x)|)_j‖_{ℓ_q} ‖_p` when every block `Δ_j u` is (the tempered distribution
of) an `L_p` function `g_j`, and `∞` otherwise (the infimum over the families `(g_j)` with
`Δ_j u = g_j`; there is at most one, `Rd.triebelLizorkinNormDistr_eq`). -/
noncomputable def triebelLizorkinNormDistr (s : ℝ) (q : ℝ≥0∞) (u : 𝓢'(V, ℂ)) : ℝ≥0∞ :=
  ⨅ (g : ℕ → Lp ℂ p (volume : Measure V)) (_ : ∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ))),
    eLpNorm (fun x => lqNorm q fun j => dyadicWeight s j * ‖g j x‖ₑ) p volume

variable (p) in
/-- `u ∈ F^s_{p,q}`: the Triebel–Lizorkin quasi-norm of the tempered distribution `u` is
finite. -/
def MemTriebelLizorkinDistr (s : ℝ) (q : ℝ≥0∞) (u : 𝓢'(V, ℂ)) : Prop :=
  triebelLizorkinNormDistr p s q u < ∞

/-- The quasi-norm is at most that of any family of `L_p` functions representing the blocks. -/
theorem triebelLizorkinNormDistr_le {s : ℝ} {q : ℝ≥0∞} {u : 𝓢'(V, ℂ)}
    {g : ℕ → Lp ℂ p (volume : Measure V)} (hg : ∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ))) :
    triebelLizorkinNormDistr p s q u ≤
      eLpNorm (fun x => lqNorm q fun j => dyadicWeight s j * ‖g j x‖ₑ) p volume :=
  iInf₂_le g hg

/-- **The quasi-norm of the representing family**: if the blocks of `u` are the `L_p` functions
`g_j`, the quasi-norm is `‖ x ↦ ‖(2^{js} |g_j(x)|)_j‖_{ℓ_q} ‖_p`, since `L_p` functions are
determined by their tempered distributions (`Rd.eq_of_toTemperedDistribution_eq`). -/
theorem triebelLizorkinNormDistr_eq {s : ℝ} {q : ℝ≥0∞} {u : 𝓢'(V, ℂ)}
    {g : ℕ → Lp ℂ p (volume : Measure V)} (hg : ∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ))) :
    triebelLizorkinNormDistr p s q u =
      eLpNorm (fun x => lqNorm q fun j => dyadicWeight s j * ‖g j x‖ₑ) p volume := by
  refine le_antisymm (triebelLizorkinNormDistr_le hg) (le_iInf₂ fun g' hg' => ?_)
  have h : g' = g := funext fun j => eq_of_toTemperedDistribution_eq ((hg' j).symm.trans (hg j))
  rw [h]

/-- If some block of `u` is no `L_p` function, the quasi-norm is `∞`. -/
theorem triebelLizorkinNormDistr_eq_top {s : ℝ} {q : ℝ≥0∞} {u : 𝓢'(V, ℂ)}
    (h : ¬ ∃ g : ℕ → Lp ℂ p (volume : Measure V), ∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ))) :
    triebelLizorkinNormDistr p s q u = ∞ :=
  iInf_eq_top.2 fun g => iInf_eq_top.2 fun hg => (h ⟨g, hg⟩).elim

/-- **Bounding by the quasi-norm**: if `x ≤ C ‖ x ↦ ‖(2^{js} |g_j(x)|)_j‖_{ℓ_q} ‖_p` for every
family of `L_p` functions `g_j` representing the blocks of `u`, and `C ≠ 0`, then
`x ≤ C ‖u‖_{F^s_{p,q}}` (`Rd.triebelLizorkinNormDistr_eq`, `Rd.triebelLizorkinNormDistr_eq_top`). -/
theorem le_mul_triebelLizorkinNormDistr {s : ℝ} {q : ℝ≥0∞} {u : 𝓢'(V, ℂ)} {x C : ℝ≥0∞}
    (hC : C ≠ 0) (h : ∀ g : ℕ → Lp ℂ p (volume : Measure V),
      (∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ))) →
        x ≤ C * eLpNorm (fun y => lqNorm q fun j => dyadicWeight s j * ‖g j y‖ₑ) p volume) :
    x ≤ C * triebelLizorkinNormDistr p s q u := by
  by_cases hex : ∃ g : ℕ → Lp ℂ p (volume : Measure V),
      ∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ))
  · obtain ⟨g, hg⟩ := hex
    rw [triebelLizorkinNormDistr_eq hg]
    exact h g hg
  · rw [triebelLizorkinNormDistr_eq_top hex, ENNReal.mul_top hC]
    exact le_top

/-- **Compatibility with `L_p`**: for `1 ≤ p < ∞` and `f ∈ L_p(V)`, the quasi-norm of the
tempered distribution of `f` is the Triebel–Lizorkin quasi-norm `‖f‖_{F^s_{p,q}}` of
`Rd.triebelLizorkinNorm`: the blocks of `f` are its `L_p` blocks `ψ_j ⋆ f`
(`Rd.distribBlock_toTemperedDistribution`, `Rd.lpBlock_ae_eq_blockFun`). -/
theorem triebelLizorkinNormDistr_toTemperedDistribution (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNormDistr p s q (f : 𝓢'(V, ℂ)) = triebelLizorkinNorm s q f := by
  rw [triebelLizorkinNormDistr_eq (g := fun j => lpBlock hp j f)
    (fun j => distribBlock_toTemperedDistribution hp j f), triebelLizorkinNorm]
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun j => lpBlock_ae_eq_blockFun hp j f] with x hx
  simp_rw [hx]

/-- `f ∈ L_p` lies in `F^s_{p,q}` as a tempered distribution iff it lies in `F^s_{p,q}` of
`Rd.MemTriebelLizorkin` (`Rd.triebelLizorkinNormDistr_toTemperedDistribution`). -/
theorem memTriebelLizorkinDistr_toTemperedDistribution_iff (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (f : Lp ℂ p (volume : Measure V)) :
    MemTriebelLizorkinDistr p s q (f : 𝓢'(V, ℂ)) ↔ MemTriebelLizorkin s q f := by
  rw [MemTriebelLizorkinDistr, MemTriebelLizorkin,
    triebelLizorkinNormDistr_toTemperedDistribution hp]

/-- **The quasi-norm decreases in `q`**: `‖u‖_{F^s_{p,r}} ≤ ‖u‖_{F^s_{p,q}}` for
`1 ≤ q ≤ r ≤ ∞` (`MeasureTheory.eLpNorm_lqNorm_mono_exponent`). -/
theorem triebelLizorkinNormDistr_mono_exponent {s : ℝ} {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    (u : 𝓢'(V, ℂ)) :
    triebelLizorkinNormDistr p s r u ≤ triebelLizorkinNormDistr p s q u :=
  le_iInf₂ fun g hg => (triebelLizorkinNormDistr_le hg).trans
    (eLpNorm_lqNorm_mono_exponent hq hqr fun j =>
      (Lp.aestronglyMeasurable (g j)).enorm.const_mul _)

/-- **The quasi-norm increases in `s`**: `‖u‖_{F^s_{p,q}} ≤ ‖u‖_{F^t_{p,q}}` for `s ≤ t`
(`MeasureTheory.eLpNorm_lqNorm_dyadicWeight_mono_smoothness`). -/
theorem triebelLizorkinNormDistr_mono_smoothness {s t : ℝ} (hst : s ≤ t) (q : ℝ≥0∞)
    (u : 𝓢'(V, ℂ)) :
    triebelLizorkinNormDistr p s q u ≤ triebelLizorkinNormDistr p t q u :=
  le_iInf₂ fun g hg => (triebelLizorkinNormDistr_le hg).trans
    (eLpNorm_lqNorm_dyadicWeight_mono_smoothness hst fun j =>
      (Lp.aestronglyMeasurable (g j)).enorm)

/-- **`F^s_{p,q}` increases in `q`**: `F^s_{p,q} ⊆ F^s_{p,r}` for `1 ≤ q ≤ r ≤ ∞`. -/
theorem MemTriebelLizorkinDistr.mono_exponent {s : ℝ} {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    {u : 𝓢'(V, ℂ)} (hu : MemTriebelLizorkinDistr p s q u) : MemTriebelLizorkinDistr p s r u :=
  (triebelLizorkinNormDistr_mono_exponent hq hqr u).trans_lt hu

/-- **`F^s_{p,q}` decreases in `s`**: `F^t_{p,q} ⊆ F^s_{p,q}` for `s ≤ t`. -/
theorem MemTriebelLizorkinDistr.mono_smoothness {s t : ℝ} (hst : s ≤ t) {q : ℝ≥0∞}
    {u : 𝓢'(V, ℂ)} (hu : MemTriebelLizorkinDistr p t q u) : MemTriebelLizorkinDistr p s q u :=
  (triebelLizorkinNormDistr_mono_smoothness hst q u).trans_lt hu

/-- **The blocks of `u ∈ F^s_{p,q}` are `L_p` functions**: if the quasi-norm of `u` is finite,
there is a family `(g_j)` in `L_p(V)` with `Δ_j u = g_j` for every `j`
(`Rd.triebelLizorkinNormDistr_eq_top`). -/
theorem MemTriebelLizorkinDistr.exists_blocks {s : ℝ} {q : ℝ≥0∞} {u : 𝓢'(V, ℂ)}
    (hu : MemTriebelLizorkinDistr p s q u) :
    ∃ g : ℕ → Lp ℂ p (volume : Measure V), ∀ j, distribBlock j u = (g j : 𝓢'(V, ℂ)) := by
  by_contra h
  exact hu.ne (triebelLizorkinNormDistr_eq_top h)

/-! ### Limits of the decomposition -/

/-- **A tempered distribution is the limit of its `L_p` blocks**: if every block `Δ_j w` is an
`L_p` function `G_j` and the partial sums `∑_{j < J} G_j` converge in `L_p(V)` to `h`, then
`w = h` as tempered distributions. The partial sums tend to `w` in `𝓢'`
(`Rd.tendsto_sum_distribBlock`) and to `h`, since `L_p` embeds continuously into `𝓢'`; limits in
`𝓢'` are unique. -/
theorem eq_of_tendsto_sum_distribBlock {w : 𝓢'(V, ℂ)} {G : ℕ → Lp ℂ p (volume : Measure V)}
    (hw : ∀ j, distribBlock j w = (G j : 𝓢'(V, ℂ))) {h : Lp ℂ p (volume : Measure V)}
    (hG : Tendsto (fun J => ∑ j ∈ Finset.range J, G j) atTop (𝓝 h)) :
    w = (h : 𝓢'(V, ℂ)) := by
  refine tendsto_nhds_unique (tendsto_sum_distribBlock w) ?_
  refine (((Lp.toTemperedDistributionCLM ℂ volume p).continuous.tendsto h).comp hG).congr
    fun J => ?_
  simp only [Function.comp_apply, map_sum, Lp.toTemperedDistributionCLM_apply, hw]

end Rd
