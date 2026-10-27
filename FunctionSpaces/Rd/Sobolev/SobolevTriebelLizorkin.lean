/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.Sobolev.DerivativeKernels
public import FunctionSpaces.Rd.TriebelLizorkin.SquareFunction

/-!
# Sobolev spaces `W^m_p = F^m_{p,2}`

Let `V` have dimension `n ≥ 1`, `1 < p < ∞` and `m ∈ ℕ`. A function `f ∈ L_p(V)` lies in the
Sobolev space `W^m_p(V)` (`Rd.MemSobolev`: all weak derivatives `∂^w f` of order `k ≤ m` exist
and lie in `L_p(V)`) iff it lies in the Triebel–Lizorkin space `F^m_{p,2}(V)`
(`Rd.MemTriebelLizorkin`: `‖ x ↦ ‖(2^{jm} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p < ∞`), see
`Rd.memSobolev_iff_memTriebelLizorkin`. Both directions have named constants
(`Rd.sobolevToTLConst`, `Rd.tlToSobolevConst`), formulas in the Schwartz seminorms of fixed
kernels that are proved finite.

* **`W^m_p ⊆ F^m_{p,2}`** (`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv`,
  `Rd.memTriebelLizorkin_of_hasWeakLineDeriv`): with the weak
  derivatives `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the orthonormal basis `e` of
  `Rd.gridBasis`, `‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p`
  (`Rd.sobolevToTLConst`). Young's inequality bounds `ψ_0 ⋆ f`; the dilated derivative kernels
  give `2^{jm} ψ_{j+1} ⋆ f = ∑_α (η_α)_{2^j} ⋆ g_α` (`Rd.two_pow_mul_blockFun_succ_ae`), and the
  analysis bound of the Calderón–Zygmund families `((η_α)_{2^j})_j` bounds each sum.
* **`F^m_{p,2} ⊆ W^m_p`** (`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin`): for
  `f ∈ F^k_{p,2}(V)` and directions `w ∈ V^k`, the partial sums
  `∑_{j < J} (∂^w ψ̃_j) ⋆ (ψ_j ⋆ f)` (`Rd.derivSynthesisSum`) are a Cauchy sequence in `L_p`, by
  the synthesis bound of the Calderón–Zygmund family `((∂^w G̃_j)_{2^j})_j` and the tails of the
  coefficients `2^{jk} ψ_j ⋆ f` in `L_p(ℓ_2)`. They are the weak derivatives `∂^w` of the
  reproducing sums `∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f) → f`, so their limit `g` is the weak derivative
  `∂^w f`, with `‖g‖_p ≤ C_w ‖f‖_{F^k_{p,2}}` (`Rd.tlToSobolevConst`). For `k ≤ m`,
  `F^m_{p,2} ⊆ F^k_{p,2}`.

With the Besov sandwich of the Triebel–Lizorkin spaces, `B^m_{p,min(p,2)} ⊆ W^m_p` and, for
`m ≥ 1`, `W^m_p ⊆ B^m_{p,max(p,2)}` (`Rd.memSobolev_of_memApprox`, `Rd.memApprox_of_memSobolev`,
with norm bounds in `Rd.exists_hasWeakLineDeriv_of_memApprox` and
`Rd.approxNormDyadic_le_of_hasWeakLineDeriv`), and `W^m_2 = B^m_{2,2}` for `m ≥ 1`
(`Rd.memSobolev_two_iff_memApprox`).
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal Topology SchwartzMap LineDeriv
open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### `W^m_p ⊆ F^m_{p,2}` -/

variable (V) in
/-- The constant `K_α = S_{V,p}(2, 4 H_{A^α})` of the bound `W^m_p ⊆ F^m_{p,2}` for the
multi-index `α`: the strong type constant `Rd.czConst` of the Calderón–Zygmund family of the
dilated derivative kernels `(η_α)_{2^j}`, with overlap `2` and Hörmander constant `4 H_{A^α}`
(`Rd.isCZFamily_derivFamily`). -/
noncomputable def sobolevToTLConst (p : ℝ≥0∞) {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) : ℝ≥0∞ :=
  czConst V p 2 (4 * familyHormanderConst V (derivKernelBound i))

/-- The constant `Rd.sobolevToTLConst V p α` is finite for `1 < p < ∞`. -/
theorem sobolevToTLConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ V)) : sobolevToTLConst V p i ≠ ∞ :=
  czConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

/-- **The blocks of `f` as convolutions with its derivatives**: for `1 ≤ p < ∞`, if
`g_α ∈ L_p(V)` is the weak derivative `∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` for every multi-index
`α`, then for almost every `x` and every `j`,
`2^{jm} (ψ_{j+1} ⋆ f)(x) = ∑_α ((η_α)_{2^j} ⋆ g_α)(x)`.
This is the dilated identity `2^{jm} ψ_{j+1} = ∑_α ∂^α ((η_α)_{2^j})`
(`Rd.two_pow_smul_psi_succ_eq_sum`) with each derivative moved from the kernel to `f`
(`Rd.conv_eq_conv_iteratedLineDerivOp`). -/
theorem two_pow_mul_blockFun_succ_ae (hp : p ≠ ∞) {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    ∀ᵐ x ∂volume, ∀ j, (2 : ℂ) ^ (j * m) * blockFun (j + 1) f x =
      ∑ i, conv (derivFamily i j) (g i) volume x := by
  refine ae_all_iff.2 fun j => ?_
  set K : (Fin m → Fin (finrank ℝ V)) → 𝓢(V, ℂ) := fun i =>
    ∂^{fun k => gridBasis V (i k)} (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero)
      (derivKernel i)) with hKdef
  have hsum : (fun y => ∑ i, (1 : ℂ) * K i y) = (2 : ℂ) ^ (j * m) • psi (V := V) (j + 1) := by
    rw [two_pow_smul_psi_succ_eq_sum]
    funext y
    simp [K, Finset.sum_apply]
  have h := conv_finsetSum_kernel_ae Fact.out hp Finset.univ (fun _ => (1 : ℂ))
    (K := fun i => ⇑(K i)) (fun i _ => (K i).integrable) (Lp.memLp f)
  rw [hsum, smul_conv] at h
  filter_upwards [h] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, one_mul] at hx
  rw [blockFun, hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hKdef, ← conv_eq_conv_iteratedLineDerivOp (hg i), coe_schwartzDilate]
  rfl

/-- **The pointwise bound of the higher blocks**: for `1 ≤ p < ∞`, under the hypotheses of
`Rd.two_pow_mul_blockFun_succ_ae`, for almost every `x`,
`‖(2^{(j+1)m} (ψ_{j+1} ⋆ f)(x))_j‖_{ℓ_2} ≤ 2^m ∑_α ‖(((η_α)_{2^j} ⋆ g_α)(x))_j‖_{ℓ_2}`, by
Minkowski's inequality in `ℓ_2`. -/
theorem lqNorm_blockFun_succ_le_sum_ae (hp : p ≠ ∞) {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    ∀ᵐ x ∂volume,
      lqNorm 2 (fun n => dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f x‖ₑ) ≤
        2 ^ m * ∑ i, lqNorm 2 (fun n => ‖conv (derivFamily i n) (g i) volume x‖ₑ) := by
  filter_upwards [two_pow_mul_blockFun_succ_ae hp hg] with x hx
  calc lqNorm 2 (fun n => dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f x‖ₑ)
      ≤ lqNorm 2 (fun n => 2 ^ m * ∑ i, ‖conv (derivFamily i n) (g i) volume x‖ₑ) := by
        refine ENNReal.lqNorm_mono fun n => ?_
        rw [ENNReal.dyadicWeight_natCast, show (n + 1) * m = m + n * m by ring, pow_add,
          mul_assoc]
        gcongr
        rw [← enorm_two_pow_complex, ← enorm_mul, hx n]
        exact enorm_sum_le _ _
    _ = 2 ^ m * lqNorm 2 (fun n => ∑ i, ‖conv (derivFamily i n) (g i) volume x‖ₑ) :=
        ENNReal.lqNorm_const_mul _ _
    _ ≤ 2 ^ m * ∑ i, lqNorm 2 (fun n => ‖conv (derivFamily i n) (g i) volume x‖ₑ) := by
        gcongr
        exact ENNReal.lqNorm_sum_le one_le_two _ _

/-- **The higher blocks in `L_p(ℓ_2)`**: in dimension `n ≥ 1`, for `1 < p < ∞`, under the
hypotheses of `Rd.two_pow_mul_blockFun_succ_ae`,
`‖ x ↦ ‖(2^{(j+1)m} (ψ_{j+1} ⋆ f)(x))_j‖_{ℓ_2} ‖_p ≤ 2^m ∑_α K_α ‖g_α‖_p` with
`K_α = Rd.sobolevToTLConst V p α`: the pointwise bound `Rd.lqNorm_blockFun_succ_le_sum_ae`,
Minkowski's inequality in `L_p`, and the analysis bound of the families `((η_α)_{2^j})_j`
(`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`). -/
theorem eLpNorm_lqNorm_blockFun_succ_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    eLpNorm (fun x => lqNorm 2 (fun n =>
        dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f x‖ₑ)) p volume ≤
      2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ := by
  set F : (Fin m → Fin (finrank ℝ V)) → V → ℝ≥0∞ :=
    fun i x => lqNorm 2 (fun n => ‖conv (derivFamily i n) (g i) volume x‖ₑ)
  have hF : ∀ i, AEMeasurable (F i) volume := fun i => aemeasurable_lqNorm_comp
    (fun n => (aestronglyMeasurable_conv
      ((isCZFamily_derivFamily i).integrable n).aestronglyMeasurable
      (Lp.aestronglyMeasurable (g i))).enorm) 2
  have hsum : AEMeasurable (fun x => ∑ i, F i x) volume :=
    Finset.aemeasurable_fun_sum _ fun i _ => hF i
  calc _ ≤ eLpNorm (fun x => 2 ^ m * ∑ i, F i x) p volume := by
        refine eLpNorm_mono_enorm_ae (aemeasurable_lqNorm_comp (fun n =>
          ((aestronglyMeasurable_blockFun (n + 1) f).enorm.const_mul _)) 2).aestronglyMeasurable
          ?_
        filter_upwards [lqNorm_blockFun_succ_le_sum_ae hp hg] with x hx
        simpa only [enorm_eq_self] using hx
    _ = 2 ^ m * eLpNorm (∑ i, F i) p volume := by
        rw [eLpNorm_const_mul_ennreal _ hsum, Finset.sum_fn]
    _ ≤ 2 ^ m * ∑ i, eLpNorm (F i) p volume := by
        gcongr
        exact eLpNorm_sum_le Fact.out
    _ ≤ 2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ := by
        gcongr with i
        rw [Lp.enorm_def]
        exact (isCZFamily_derivFamily i).eLpNorm_lqNorm_conv_le hp1 hp (Lp.memLp (g i))

/-- **`W^m_p ⊆ F^m_{p,2}` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞` and
`f ∈ L_p(V)` whose weak derivatives `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the orthonormal
basis `e` of `Rd.gridBasis` lie in `L_p(V)` for every multi-index `α`,
`‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p` with `K_α = Rd.sobolevToTLConst V p α`.
The block `j = 0` is split off from the `ℓ_2` norm (`ENNReal.lqNorm_le_sum_range_add_shift`)
and bounded by Young's inequality (`Rd.eLpNorm_blockFun_zero_le`); the other blocks by
`Rd.eLpNorm_lqNorm_blockFun_succ_le`. -/
theorem triebelLizorkinNorm_le_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    triebelLizorkinNorm (m : ℝ) 2 f ≤
      eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ := by
  set A : V → ℝ≥0∞ := fun x => ‖blockFun 0 f x‖ₑ
  set B : V → ℝ≥0∞ :=
    fun x => lqNorm 2 (fun n => dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f x‖ₑ)
  have h1 : triebelLizorkinNorm (m : ℝ) 2 f ≤ eLpNorm (A + B) p volume := by
    refine eLpNorm_mono_enorm (aemeasurable_lqNorm_blockFun _ _ f).aestronglyMeasurable
      fun x => ?_
    simp only [enorm_eq_self, Pi.add_apply]
    refine (ENNReal.lqNorm_le_sum_range_add_shift one_le_two _ 1).trans_eq ?_
    simp [A, B, ENNReal.dyadicWeight_zero_right]
  calc triebelLizorkinNorm (m : ℝ) 2 f ≤ eLpNorm (A + B) p volume := h1
    _ ≤ eLpNorm A p volume + eLpNorm B p volume := eLpNorm_add_le Fact.out
    _ ≤ _ := by
        gcongr
        · rw [eLpNorm_enorm _ (aestronglyMeasurable_blockFun 0 f)]
          exact eLpNorm_blockFun_zero_le hp f
        · exact eLpNorm_lqNorm_blockFun_succ_le hp1 hp hg

/-- **The weak derivatives of order `m` along the basis vectors give `f ∈ F^m_{p,2}`**: in
dimension `n ≥ 1`, for `1 < p < ∞`, if the weak derivatives `g_α = ∂^α f` of order `m` along the
basis `e` of `Rd.gridBasis` lie in `L_p(V)` for every multi-index `α`, then `f ∈ F^m_{p,2}(V)`,
since the bound `Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv` is finite. -/
theorem memTriebelLizorkin_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    MemTriebelLizorkin (m : ℝ) 2 f :=
  (triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg).trans_lt
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
      eLpNorm_lpKernel_lt_top enorm_lt_top,
      ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) (ENNReal.sum_lt_top.2 fun i _ =>
        ENNReal.mul_lt_top (sobolevToTLConst_ne_top hp1 hp i).lt_top enorm_lt_top)⟩)

/-- **`W^m_p ⊆ F^m_{p,2}`**: in dimension `n ≥ 1`, for `1 < p < ∞`, every `f ∈ W^m_p(V)` lies in
`F^m_{p,2}(V)`; the weak derivatives of order `m` along the basis vectors suffice
(`Rd.memTriebelLizorkin_of_hasWeakLineDeriv`). -/
theorem memTriebelLizorkin_of_memSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev m f) : MemTriebelLizorkin (m : ℝ) 2 f := by
  have hd : ∀ i : Fin m → Fin (finrank ℝ V), ∃ g : Lp ℂ p (volume : Measure V),
      HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f g := fun i =>
    (memSobolev_iff_exists_hasWeakLineDeriv f).1 hf m le_rfl _
  choose g hg using hd
  exact memTriebelLizorkin_of_hasWeakLineDeriv hp1 hp hg

/-! ### `F^m_{p,2} ⊆ W^m_p` -/

/-- The constant `C_w = S_{V,p}(4 ((8π)^k ∏_l ‖w_l‖)², 4 H_{Ã^w})` of the bound
`F^k_{p,2} ⊆ W^k_p` for the directions `w ∈ V^k`: the strong type constant `Rd.czConst` of the
Calderón–Zygmund family `((∂^w G̃_j)_{2^j})_j` of the rescaled derivatives of the synthesis
kernels (`Rd.isCZFamily_derivDualFamily`). -/
noncomputable def tlToSobolevConst (p : ℝ≥0∞) {k : ℕ} (w : Fin k → V) : ℝ≥0∞ :=
  czConst V p (derivDualOverlap w) (4 * familyHormanderConst V (derivDualBound w))

/-- The constant `Rd.tlToSobolevConst p w` is finite for `1 < p < ∞`. -/
theorem tlToSobolevConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ} (w : Fin k → V) :
    tlToSobolevConst p w ≠ ∞ :=
  czConst_ne_top hp1 hp (derivDualOverlap_ne_top w)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

omit [Fact (1 ≤ p)] in
/-- **Weighted blocks with terms set to zero**: for every predicate `P` on `ℕ`,
`‖ x ↦ ‖(1_P(j) 2^{js} |(ψ_j ⋆ f)(x)|)_j‖_{ℓ_q} ‖_p ≤ ‖f‖_{F^s_{p,q}}`, where the terms with `P j`
false are `0` (`MeasureTheory.eLpNorm_lqNorm_ite_le`). -/
theorem eLpNorm_lqNorm_ite_blockFun_le {P : ℕ → Prop} [DecidablePred P] (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (fun x => lqNorm q fun j =>
      if P j then dyadicWeight s j * ‖blockFun j f x‖ₑ else 0) p volume ≤
      triebelLizorkinNorm s q f :=
  eLpNorm_lqNorm_ite_le fun j => (aestronglyMeasurable_blockFun j f).enorm.const_mul _

/-- **The tails of the weighted blocks tend to zero**: for `1 ≤ p < ∞`, `0 < q < ∞`, `s ∈ ℝ` and
`f ∈ F^s_{p,q}(V)`, `‖ x ↦ ‖(2^{js} (ψ_j ⋆ f)(x))_{j ≥ N}‖_{ℓ_q} ‖_p → 0` as `N → ∞`, where the
terms `j < N` are `0` (`MeasureTheory.tendsto_eLpNorm_lqNorm_ite_le`). -/
theorem tendsto_eLpNorm_lqNorm_blockFun_tail (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin s q f) :
    Tendsto (fun N => eLpNorm (fun x => lqNorm q fun j =>
      if N ≤ j then dyadicWeight s j * ‖blockFun j f x‖ₑ else 0) p volume) atTop (𝓝 0) :=
  tendsto_eLpNorm_lqNorm_ite_le (zero_lt_one.trans_le Fact.out).ne' hp hq0 hq
    (fun j => (aestronglyMeasurable_blockFun j f).enorm.const_mul _) hf.ne

/-- **The synthesis bound for derivatives of the synthesis kernels**: in dimension `n ≥ 1`, for
`1 < p < ∞`, directions `w ∈ V^k`, every finite set `s ⊆ ℕ` and `f ∈ L_p(V)`,
`‖∑_{j ∈ s} (∂^w ψ̃_j) ⋆ (ψ_j ⋆ f)‖_p ≤ C_w ‖ x ↦ ‖(1_s(j) 2^{jk} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p`
with `C_w = Rd.tlToSobolevConst p w`. Since `∂^w ψ̃_j = 2^{jk} (∂^w G̃_j)_{2^j}`
(`Rd.iteratedLineDerivOp_psiDualS`), this is the synthesis bound of the family
`((∂^w G̃_j)_{2^j})_j` (`Rd.IsCZFamily.eLpNorm_sum_conv_le`) with the coefficients
`1_s(j) 2^{jk} ψ_j ⋆ f`. -/
theorem eLpNorm_sum_conv_derivDual_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → V) (s : Finset ℕ) (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (fun x => ∑ j ∈ s, conv (∂^{w} (psiDualS j) : 𝓢(V, ℂ)) (blockFun j f) volume x)
        p volume ≤
      tlToSobolevConst p w * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ s then dyadicWeight (k : ℝ) j * ‖blockFun j f x‖ₑ else 0) p volume := by
  set a : ℕ → V → ℂ := fun j => if j ∈ s then ((2 : ℂ) ^ (j * k)) • blockFun j f else 0
  have ha : ∀ j, MemLp (a j) p volume := fun j => by
    by_cases h : j ∈ s
    · simp only [a, h, ↓reduceIte]
      exact (memLp_blockFun hp j f).const_smul _
    · simp only [a, h, ↓reduceIte]
      exact MemLp.zero
  have hsum :
      (fun x => ∑ j ∈ s, conv (∂^{w} (psiDualS j) : 𝓢(V, ℂ)) (blockFun j f) volume x) =
        fun x => ∑ j ∈ s, conv (derivDualFamily w j) (a j) volume x := by
    funext x
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [a, hj, ↓reduceIte, iteratedLineDerivOp_psiDualS, smul_conv, conv_smul,
      Pi.smul_apply]
  have hnorm : (fun x => lqNorm 2 fun j => ‖a j x‖ₑ) = fun x => lqNorm 2 fun j =>
      if j ∈ s then dyadicWeight (k : ℝ) j * ‖blockFun j f x‖ₑ else 0 := by
    funext x
    congr 1
    funext j
    by_cases h : j ∈ s
    · simp only [a, h, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
      rw [enorm_mul, enorm_two_pow_complex, ENNReal.dyadicWeight_natCast]
    · simp only [a, h, ↓reduceIte, Pi.zero_apply, enorm_zero]
  rw [hsum, ← hnorm]
  exact (isCZFamily_derivDualFamily w).eLpNorm_sum_conv_le hp1 hp s ha

omit [Fact (1 ≤ p)] in
/-- The **partial sums of the derivative** `∂^w f`: `∑_{j < J} (∂^w ψ̃_j) ⋆ (ψ_j ⋆ f)`, the
derivatives of the reproducing sums `∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f)`. -/
noncomputable def derivSynthesisSum {k : ℕ} (w : Fin k → V) (f : Lp ℂ p (volume : Measure V))
    (J : ℕ) : V → ℂ :=
  fun x => ∑ j ∈ Finset.range J, conv (∂^{w} (psiDualS j) : 𝓢(V, ℂ)) (blockFun j f) volume x

/-- The partial sums of the derivative lie in `L_p(V)` for `1 ≤ p < ∞`, by Young's inequality. -/
theorem memLp_derivSynthesisSum (hp : p ≠ ∞) {k : ℕ} (w : Fin k → V)
    (f : Lp ℂ p (volume : Measure V)) (J : ℕ) : MemLp (derivSynthesisSum w f J) p volume :=
  memLp_finsetSum _ fun j _ =>
    memLp_conv Fact.out hp (∂^{w} (psiDualS j)).integrable (memLp_blockFun hp j f)

/-- **Differences of partial sums**: in dimension `n ≥ 1`, for `1 < p < ∞` and `N ≤ N'`, the
difference of the partial sums `Rd.derivSynthesisSum` at `N'` and at `N` has `L_p` norm at most
`C_w ‖ x ↦ ‖(2^{jk} (ψ_j ⋆ f)(x))_{j ≥ N}‖_{ℓ_2} ‖_p` (`Rd.eLpNorm_sum_conv_derivDual_le` for
the set `{N, …, N' - 1}`). -/
theorem eLpNorm_derivSynthesisSum_sub_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → V) (f : Lp ℂ p (volume : Measure V)) {N N' : ℕ} (hNN' : N ≤ N') :
    eLpNorm (derivSynthesisSum w f N' - derivSynthesisSum w f N) p volume ≤
      tlToSobolevConst p w * eLpNorm (fun x => lqNorm 2 fun j =>
        if N ≤ j then dyadicWeight (k : ℝ) j * ‖blockFun j f x‖ₑ else 0) p volume := by
  have hd : derivSynthesisSum w f N' - derivSynthesisSum w f N = fun x =>
      ∑ j ∈ Finset.Ico N N', conv (∂^{w} (psiDualS j) : 𝓢(V, ℂ)) (blockFun j f) volume x := by
    funext x
    rw [Pi.sub_apply, derivSynthesisSum, derivSynthesisSum, Finset.sum_Ico_eq_sub _ hNN']
  rw [hd]
  refine (eLpNorm_sum_conv_derivDual_le hp1 hp w _ f).trans ?_
  gcongr
  refine eLpNorm_mono_enorm (aemeasurable_lqNorm_ite (P := (· ∈ Finset.Ico N N'))
    (fun j => (aestronglyMeasurable_blockFun j f).enorm.const_mul _) 2).aestronglyMeasurable
    fun x => ?_
  simp only [enorm_eq_self]
  refine ENNReal.lqNorm_mono fun j => ?_
  by_cases h : j ∈ Finset.Ico N N'
  · simp only [h, (Finset.mem_Ico.1 h).1, ↓reduceIte, le_refl]
  · simp only [h, ↓reduceIte]
    exact zero_le

/-- **The partial sums of the derivative converge**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`w ∈ V^k` and `f ∈ F^k_{p,2}(V)`, the classes in `L_p(V)` of the partial sums
`Rd.derivSynthesisSum w f J` form a Cauchy sequence: their differences are bounded by the tails
of the weighted blocks (`Rd.eLpNorm_derivSynthesisSum_sub_le`), which tend to zero
(`Rd.tendsto_eLpNorm_lqNorm_blockFun_tail`). -/
theorem cauchySeq_toLp_derivSynthesisSum [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin (k : ℝ) 2 f) :
    CauchySeq fun J => (memLp_derivSynthesisSum hp w f J).toLp := by
  set T : ℕ → ℝ≥0∞ := fun N => eLpNorm (fun x => lqNorm 2 fun j =>
    if N ≤ j then dyadicWeight (k : ℝ) j * ‖blockFun j f x‖ₑ else 0) p volume
  have hT : ∀ N, T N ≠ ∞ := fun N =>
    ne_top_of_le_ne_top hf.ne (eLpNorm_lqNorm_ite_blockFun_le _ _ f)
  have hC := tlToSobolevConst_ne_top hp1 hp w
  refine cauchySeq_of_le_tendsto_0' (fun N => (tlToSobolevConst p w * T N).toReal)
    (fun N N' hNN' => ?_) ?_
  · rw [dist_comm, Lp.dist_def]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hC (hT N)) ?_
    rw [eLpNorm_congr_ae ((MemLp.coeFn_toLp _).sub (MemLp.coeFn_toLp _))]
    exact eLpNorm_derivSynthesisSum_sub_le hp1 hp w f hNN'
  · have h := ENNReal.Tendsto.const_mul
      (tendsto_eLpNorm_lqNorm_blockFun_tail hp two_ne_zero ENNReal.ofNat_ne_top hf) (Or.inr hC)
    rw [mul_zero] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h'
    exact h'

/-- **The partial sums are weak derivatives**: for `1 ≤ p < ∞`, `w ∈ V^k` and `f ∈ L_p(V)`,
`Rd.derivSynthesisSum w f J` is the weak derivative `∂^w` of the reproducing sum
`∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f)` on `V` (`Rd.hasWeakLineDeriv_conv` for each term,
`Rd.HasWeakLineDeriv.sum`). -/
theorem hasWeakLineDeriv_sum_conv_psiDual (hp : p ≠ ∞) {k : ℕ} (w : Fin k → V)
    (f : Lp ℂ p (volume : Measure V)) (J : ℕ) :
    HasWeakLineDeriv ⊤ w
      (fun x => ∑ j ∈ Finset.range J, conv (psiDual j) (blockFun j f) volume x)
      (derivSynthesisSum w f J) := by
  have h := HasWeakLineDeriv.sum (s := Finset.range J) fun j _ =>
    hasWeakLineDeriv_conv Fact.out hp (memLp_blockFun hp j f) (psiDualS j) w
  simp only [coe_psiDualS] at h
  rw [Finset.sum_fn, Finset.sum_fn] at h
  exact h

/-- **`F^k_{p,2} ⊆ W^k_p` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞`,
directions `w ∈ V^k` and `f ∈ F^k_{p,2}(V)`, the weak derivative `∂^w f` exists on `V` as a
class `g ∈ L_p(V)` with `‖g‖_p ≤ C_w ‖f‖_{F^k_{p,2}}`, `C_w = Rd.tlToSobolevConst p w`.
The function `g` is the limit of the partial sums `Rd.derivSynthesisSum w f J`
(`Rd.cauchySeq_toLp_derivSynthesisSum`), the weak derivatives of the reproducing sums, which
tend to `f` (`Rd.tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub`); weak derivatives pass to the
limit (`Rd.HasWeakLineDeriv.of_tendsto`). -/
theorem exists_hasWeakLineDeriv_of_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) {k : ℕ} (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)}
    (hf : MemTriebelLizorkin (k : ℝ) 2 f) :
    ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst p w * triebelLizorkinNorm (k : ℝ) 2 f := by
  obtain ⟨g, hg⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_toLp_derivSynthesisSum hp1 hp w hf)
  refine ⟨g, ?_, le_of_tendsto' hg.enorm fun J => ?_⟩
  · have hS : Tendsto (fun J => eLpNorm (derivSynthesisSum w f J - ⇑g) p volume) atTop (𝓝 0) :=
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ g).1 hg).congr fun J =>
        eLpNorm_congr_ae ((MemLp.coeFn_toLp _).sub EventuallyEq.rfl)
    refine HasWeakLineDeriv.of_tendsto (p := p) (r := p) (l := atTop) Fact.out Fact.out
      (fun J => hasWeakLineDeriv_sum_conv_psiDual hp w f J) ?_ ?_ ?_ ?_ <;>
      rw [volume_restrict_top]
    exacts [Lp.memLp f, Lp.memLp g, tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub hp f, hS]
  · rw [Lp.enorm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
    refine (eLpNorm_sum_conv_derivDual_le hp1 hp w _ f).trans ?_
    gcongr
    exact eLpNorm_lqNorm_ite_blockFun_le _ _ f

/-- **`F^m_{p,2} ⊆ W^m_p` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`k ≤ m`, directions `w ∈ V^k` and `f ∈ F^m_{p,2}(V)`, the weak derivative `∂^w f` exists on `V`
as a class `g ∈ L_p(V)` with `‖g‖_p ≤ C_w ‖f‖_{F^m_{p,2}}`, `C_w = Rd.tlToSobolevConst p w`
(`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin` and
`‖f‖_{F^k_{p,2}} ≤ ‖f‖_{F^m_{p,2}}`, `Rd.triebelLizorkinNorm_mono_smoothness`). -/
theorem exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) {k m : ℕ} (hkm : k ≤ m) (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)}
    (hf : MemTriebelLizorkin (m : ℝ) 2 f) :
    ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst p w * triebelLizorkinNorm (m : ℝ) 2 f := by
  have hkm' : (k : ℝ) ≤ m := Nat.cast_le.2 hkm
  obtain ⟨g, hg, hgn⟩ :=
    exists_hasWeakLineDeriv_of_memTriebelLizorkin hp1 hp w (hf.mono_smoothness hkm')
  refine ⟨g, hg, hgn.trans ?_⟩
  gcongr
  exact triebelLizorkinNorm_mono_smoothness hkm' 2 f

/-- **`F^m_{p,2} ⊆ W^m_p`**: in dimension `n ≥ 1`, for `1 < p < ∞`, every `f ∈ F^m_{p,2}(V)` lies
in `W^m_p(V)` (`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le`). -/
theorem memSobolev_of_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin (m : ℝ) 2 f) : MemSobolev m f :=
  (memSobolev_iff_exists_hasWeakLineDeriv f).2 fun _ hk w =>
    (exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le hp1 hp hk w hf).imp fun _ hg => hg.1

/-- **`W^m_p = F^m_{p,2}`**: in dimension `n ≥ 1`, for `1 < p < ∞`, `m ∈ ℕ` and `f ∈ L_p(V)`,
`f ∈ W^m_p(V)` iff `f ∈ F^m_{p,2}(V)`. The norm bounds are
`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv` and
`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le`. -/
theorem memSobolev_iff_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (f : Lp ℂ p (volume : Measure V)) : MemSobolev m f ↔ MemTriebelLizorkin (m : ℝ) 2 f :=
  ⟨memTriebelLizorkin_of_memSobolev hp1 hp, memSobolev_of_memTriebelLizorkin hp1 hp⟩

/-! ### The Besov sandwich -/

/-- **`B^s_{p,min(p,2)} ⊆ F^s_{p,2}` for `s ≥ 0`**: in dimension `n ≥ 1`, for `1 < p < ∞` and
`s ≥ 0`, every `f` in the approximation space `A^s_{min(p,2)}` of the band-limited scheme lies in
`F^s_{p,2}(V)`: for `s > 0` by the Besov sandwich (`Rd.memTriebelLizorkin_of_memApprox`), for
`s = 0` since `F^0_{p,2} = L_p(V)` by the square function theorem
(`Rd.memTriebelLizorkin_zero_two`). -/
theorem memTriebelLizorkin_two_of_memApprox [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 ≤ s) {f : Lp ℂ p (volume : Measure V)}
    (hf : (bandScheme hp).MemApprox s (min p 2) f) : MemTriebelLizorkin s 2 f := by
  rcases hs.eq_or_lt with rfl | hs
  · exact memTriebelLizorkin_zero_two hp1 hp f
  · exact memTriebelLizorkin_of_memApprox hp hs one_le_two hf

/-- **`W^m_p ⊆ B^m_{p,max(p,2)}`**: in dimension `n ≥ 1`, for `1 < p < ∞` and `m ≥ 1`, every
`f ∈ W^m_p(V)` lies in the approximation space `A^m_{max(p,2)}` of the band-limited scheme, the
Besov space `B^m_{p,max(p,2)}(V)` (`Rd.memApprox_of_memTriebelLizorkin`). -/
theorem memApprox_of_memSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ} (hm : 1 ≤ m)
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev m f) :
    (bandScheme hp).MemApprox (m : ℝ) (max p 2) f :=
  memApprox_of_memTriebelLizorkin hp (Nat.cast_pos.2 hm) one_le_two
    (memTriebelLizorkin_of_memSobolev hp1 hp hf)

/-- **`B^m_{p,min(p,2)} ⊆ W^m_p`**: in dimension `n ≥ 1`, for `1 < p < ∞` and `m ∈ ℕ`, every
`f` in the approximation space `A^m_{min(p,2)}` of the band-limited scheme, the Besov space
`B^m_{p,min(p,2)}(V)`, lies in `W^m_p(V)` (`Rd.memTriebelLizorkin_two_of_memApprox`). -/
theorem memSobolev_of_memApprox [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} (hf : (bandScheme hp).MemApprox (m : ℝ) (min p 2) f) :
    MemSobolev m f :=
  memSobolev_of_memTriebelLizorkin hp1 hp
    (memTriebelLizorkin_two_of_memApprox hp1 hp (Nat.cast_nonneg m) hf)

/-- **`W^m_2 = B^m_{2,2}`**: for `p = 2` and every order `m ≥ 1`, in dimension `n ≥ 1`,
`f ∈ L_2(V)` lies in `W^m_2(V)` iff `f` lies in the approximation space `A^m_2` of the
band-limited scheme, the Besov space `B^m_{2,2}(V)`, since `F^m_{2,2} = B^m_{2,2}`
(`Rd.memTriebelLizorkin_iff_memApprox`). The case `m = 1` holds in every dimension
(`Rd.memSobolev_one_iff_memApprox`). -/
theorem memSobolev_two_iff_memApprox [Nontrivial V] {m : ℕ} (hm : 1 ≤ m)
    (f : Lp ℂ 2 (volume : Measure V)) :
    MemSobolev m f ↔ (bandScheme (V := V) two_ne_top).MemApprox (m : ℝ) 2 f := by
  rw [memSobolev_iff_memTriebelLizorkin ENNReal.one_lt_two two_ne_top,
    memTriebelLizorkin_iff_memApprox two_ne_top (Nat.cast_pos.2 hm)]

/-- **`W^m_p ⊆ B^m_{p,max(p,2)}` with named constants**: under the hypotheses of
`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv` and `m ≥ 1`, the approximation norm of `f` in
`A^m_{max(p,2)}` of the band-limited scheme is at most
`2 (1 - 2^{-m})⁻¹ (‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p)`
(`Rd.approxNormDyadic_le_triebelLizorkinNorm`). -/
theorem approxNormDyadic_le_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} (hm : 1 ≤ m) {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    (bandScheme hp).approxNormDyadic (m : ℝ) (max p 2) f ≤
      2 * (1 - (2 : ℝ≥0∞) ^ (-(m : ℝ)))⁻¹ * (eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ) :=
  (approxNormDyadic_le_triebelLizorkinNorm hp (Nat.cast_pos.2 hm) one_le_two f).trans
    (by gcongr; exact triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg)

/-- **`B^m_{p,min(p,2)} ⊆ W^m_p` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`m ∈ ℕ`, `k ≤ m`, directions `w ∈ V^k` and `f` in the approximation space `A^m_{min(p,2)}` of
the band-limited scheme, the weak derivative `∂^w f` is a class `g ∈ L_p(V)` with
`‖g‖_p ≤ C_w · 8 · 2^{3m} ‖Φ‖_1 ‖f‖_{A^m_{min(p,2)}}`, `C_w = Rd.tlToSobolevConst p w`
(`Rd.triebelLizorkinNorm_le_approxNormDyadic`). -/
theorem exists_hasWeakLineDeriv_of_memApprox [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {k m : ℕ} (hkm : k ≤ m) (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)}
    (hf : (bandScheme hp).MemApprox (m : ℝ) (min p 2) f) :
    ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst p w * (8 * dyadicWeight (m : ℝ) 3 *
        eLpNorm (lpKernel (V := V)) 1 volume *
          (bandScheme hp).approxNormDyadic (m : ℝ) (min p 2) f) := by
  obtain ⟨g, hg, hgn⟩ := exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le hp1 hp hkm w
    (memTriebelLizorkin_two_of_memApprox hp1 hp (Nat.cast_nonneg m) hf)
  refine ⟨g, hg, hgn.trans ?_⟩
  gcongr
  exact triebelLizorkinNorm_le_approxNormDyadic hp (Nat.cast_nonneg m) one_le_two f

end Rd
