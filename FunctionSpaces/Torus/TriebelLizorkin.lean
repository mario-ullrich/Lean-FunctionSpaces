/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.LittlewoodPaley
public import FunctionSpaces.Torus.LpBesovModuli
public import FunctionSpaces.Analysis.Lp.MixedNorms

/-!
# Triebel–Lizorkin spaces on the torus

For `1 ≤ p ≤ ∞`, `s ∈ ℝ`, `1 ≤ q ≤ ∞` and `f ∈ L_p(𝕋^d)`, the **Triebel–Lizorkin quasi-norm**

`‖f‖_{F^s_{p,q}} = ‖ t ↦ ‖(2^(js) |ψ_j ⋆ f(t)|)_j‖_{ℓ_q} ‖_p`

(`Torus.periodicTriebelLizorkinNorm`) takes the `ℓ_q` norm of the Littlewood–Paley blocks at every
point before the `L_p` norm. The blocks are the pointwise convolutions `ψ_j ⋆ f` with the kernels of
`ℝ^d` (`Torus.periodicBlockFun`), representatives of `Torus.periodicLpBlock`, with
`‖ψ_0 ⋆ f‖_p ≤ ‖Φ‖_1 ‖f‖_p` by Young's inequality (`Torus.eLpNorm_periodicBlockFun_zero_le`). The
space `F^s_{p,q}(𝕋^d)` consists of the `f` with a finite quasi-norm
(`Torus.MemPeriodicTriebelLizorkin`); it is a subspace of `L_p` for `1 ≤ q ≤ ∞`
(`Torus.periodicTriebelLizorkinSpace`), increasing in `q` and decreasing in `s`. For `s = 0` the
weights are `1`, so `‖f‖_{F^0_{p,q}}` is the `L_p` norm of `t ↦ ‖((ψ_j ⋆ f)(t))_j‖_{ℓ_q}`
(`Torus.periodicTriebelLizorkinNorm_zero_left`). These are the properties of the mixed norms of
dyadically weighted families in `FunctionSpaces.Analysis.Lp.MixedNorms`. Setting terms of the
weighted blocks to zero keeps them below the quasi-norm, and for `p < ∞`, `0 < q < ∞` and
`f ∈ F^s_{p,q}(𝕋^d)` their tails tend to zero (`Torus.eLpNorm_lqNorm_ite_periodicBlockFun_le`,
`Torus.tendsto_eLpNorm_lqNorm_periodicBlockFun_tail`). The comparisons with Besov spaces below need
`p < ∞`.

The mixed-norm comparisons of `FunctionSpaces.Analysis.Lp.MixedNorms` give, for every `s ∈ ℝ`,
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{max(p,q)}} ≤ ‖f‖_{F^s_{p,q}} ≤ ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{min(p,q)}}`,
with equality for `q = p`. With the Littlewood–Paley characterisation of Besov spaces on the
torus (`Torus.memBesov_iff_periodicLittlewoodPaleyNorm_lt_top`) this gives, for `s > 0`:

* `F^s_{p,p}(𝕋^d) = B^s_{p,p}(𝕋^d)` (`Torus.memPeriodicTriebelLizorkin_iff_memBesov`), and hence the
  description of `F^s_{p,p}(𝕋^d)` by moduli of smoothness
  (`Torus.memPeriodicTriebelLizorkin_iff_modulus`);
* the **Besov sandwich** `B^s_{p,min(p,q)}(𝕋^d) ⊆ F^s_{p,q}(𝕋^d) ⊆ B^s_{p,max(p,q)}(𝕋^d)`
  (`Torus.memPeriodicTriebelLizorkin_of_memBesov`, `Torus.memBesov_of_memPeriodicTriebelLizorkin`),
  with explicit constants (`Torus.periodicTriebelLizorkinNorm_le_approxNormDyadic`,
  `Torus.approxNormDyadic_le_periodicTriebelLizorkinNorm`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter Topology
open scoped ENNReal FourierTransform TorusHaar

open ENNReal (lqNorm dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The blocks at every point -/

/-- The **Littlewood–Paley block at every point**, `t ↦ (ψ_j ⋆ f)(t) = ∫ ψ_j(y) f(t - π y) dy`,
with a representative of `f ∈ L_p(𝕋^d)`. Its class in `L_p` is the block `Torus.periodicLpBlock`
(`Torus.periodicLpBlock_ae_eq_periodicBlockFun`). -/
noncomputable def periodicBlockFun (j : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    UnitAddTorus d → ℂ :=
  periodicEconv (Rd.lpBlockKernel (V := EuclideanSpace ℝ d) j) f

/-- The block `Δ_j f ∈ L_p(𝕋^d)` is represented by the pointwise convolution `ψ_j ⋆ f`. -/
theorem periodicLpBlock_ae_eq_periodicBlockFun (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicLpBlock hp j f =ᵐ[volume] periodicBlockFun j f :=
  periodicEconvLp_apply_ae hp (Rd.integrable_lpBlockKernel j) f

omit [Fact (1 ≤ p)] in
/-- The pointwise blocks are measurable. -/
theorem aestronglyMeasurable_periodicBlockFun (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    AEStronglyMeasurable (periodicBlockFun j f) volume :=
  aestronglyMeasurable_periodicEconv (Rd.integrable_lpBlockKernel j).aestronglyMeasurable
    (Lp.stronglyMeasurable f).measurable

/-- `‖Δ_j f‖_p` is the `L_p` norm of the pointwise block `ψ_j ⋆ f`. -/
theorem enorm_periodicLpBlock_eq_eLpNorm_periodicBlockFun (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖periodicLpBlock hp j f‖ₑ = eLpNorm (periodicBlockFun j f) p volume := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae (periodicLpBlock_ae_eq_periodicBlockFun hp j f)

/-- **The block `j = 0` by Young's inequality**: for `1 ≤ p < ∞` and `f ∈ L_p(𝕋^d)`,
`‖ψ_0 ⋆ f‖_p ≤ ‖Φ‖_1 ‖f‖_p`. -/
theorem eLpNorm_periodicBlockFun_zero_le (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    eLpNorm (periodicBlockFun 0 f) p volume ≤
      eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume * ‖f‖ₑ := by
  rw [Lp.enorm_def, ← Rd.eLpNorm_dilatedLpKernel_one 0,
    eLpNorm_one_eq_lintegral_enorm (Rd.integrable_dilatedLpKernel 0).1]
  exact eLpNorm_periodicEconv_le Fact.out hp (Rd.integrable_lpBlockKernel 0)
    (Lp.stronglyMeasurable f).measurable

/-- The block of a sum is the sum of the blocks, almost everywhere and for all levels at once.
On the torus `L_p ⊆ L_1`, so the convolution integrals converge absolutely almost everywhere
(`Torus.ae_integrable_econv`). -/
theorem periodicBlockFun_add_ae (f g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ t ∂volume, ∀ j, periodicBlockFun j (f + g) t =
      periodicBlockFun j f t + periodicBlockFun j g t := by
  refine ae_all_iff.2 fun j => ?_
  have hfm := (Lp.stronglyMeasurable f).measurable
  have hgm := (Lp.stronglyMeasurable g).measurable
  filter_upwards [periodicEconv_congr_ae (Rd.lpBlockKernel j)
      (Lp.stronglyMeasurable (f + g)).measurable (hfm.add hgm) (Lp.coeFn_add f g),
    periodicEconv_add_ae (Rd.integrable_lpBlockKernel j) hfm hgm ((Lp.memLp f).integrable Fact.out)
      ((Lp.memLp g).integrable Fact.out)] with t h1 h2
  rw [periodicBlockFun, periodicBlockFun, periodicBlockFun, h1, h2, Pi.add_apply]

omit [Fact (1 ≤ p)] in
/-- The block of a complex multiple is the multiple of the block, almost everywhere and for all
levels at once. -/
theorem periodicBlockFun_smul_ae (c : ℂ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ t ∂volume, ∀ j, periodicBlockFun j (c • f) t = c * periodicBlockFun j f t := by
  refine ae_all_iff.2 fun j => ?_
  filter_upwards [periodicEconv_congr_ae (Rd.lpBlockKernel j)
    (Lp.stronglyMeasurable (c • f)).measurable ((Lp.stronglyMeasurable f).measurable.const_smul c)
    (Lp.coeFn_smul c f)] with t h
  rw [periodicBlockFun, periodicBlockFun, h, periodicEconv_smul, Pi.smul_apply, smul_eq_mul]

/-! ### The Triebel–Lizorkin quasi-norm -/

/-- The **Triebel–Lizorkin quasi-norm** `‖ t ↦ ‖(2^(js) |ψ_j ⋆ f(t)|)_j‖_{ℓ_q} ‖_p` of
`f ∈ L_p(𝕋^d)`: the `ℓ_q` norm of the weighted blocks at each point, then the `L_p` norm. -/
noncomputable def periodicTriebelLizorkinNorm (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : ℝ≥0∞ :=
  eLpNorm (fun t => lqNorm q (fun j => dyadicWeight s j * ‖periodicBlockFun j f t‖ₑ)) p volume

/-- `f ∈ F^s_{p,q}(𝕋^d)`: the Triebel–Lizorkin quasi-norm of `f` is finite. -/
def MemPeriodicTriebelLizorkin (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Prop :=
  periodicTriebelLizorkinNorm s q f < ∞

omit [Fact (1 ≤ p)] in
/-- The pointwise `ℓ_q` norm of the weighted blocks is measurable. -/
theorem aemeasurable_lqNorm_periodicBlockFun (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    AEMeasurable
      (fun t => lqNorm q (fun j => dyadicWeight s j * ‖periodicBlockFun j f t‖ₑ)) volume :=
  aemeasurable_lqNorm_comp
    (fun j => (aestronglyMeasurable_periodicBlockFun j f).enorm.const_mul _) q

/-- **The quasi-norm is subadditive**: for `1 ≤ q ≤ ∞`,
`‖f + g‖_{F^s_{p,q}} ≤ ‖f‖_{F^s_{p,q}} + ‖g‖_{F^s_{p,q}}`, by the triangle inequalities in
`ℓ_q` at every point and in `L_p`. -/
theorem periodicTriebelLizorkinNorm_add_le {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f g : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm s q (f + g) ≤
      periodicTriebelLizorkinNorm s q f + periodicTriebelLizorkinNorm s q g :=
  eLpNorm_lqNorm_le_add Fact.out hq
    (fun j => (aestronglyMeasurable_periodicBlockFun j (f + g)).enorm.const_mul _) <| by
      filter_upwards [periodicBlockFun_add_ae f g] with t ht j
      rw [ht j, ← mul_add]
      gcongr
      exact enorm_add_le _ _

omit [Fact (1 ≤ p)] in
/-- **The quasi-norm is homogeneous**: `‖c f‖_{F^s_{p,q}} = |c| ‖f‖_{F^s_{p,q}}` for `c ∈ ℂ`. -/
theorem periodicTriebelLizorkinNorm_smul (s : ℝ) (q : ℝ≥0∞) (c : ℂ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm s q (c • f) = ‖c‖ₑ * periodicTriebelLizorkinNorm s q f :=
  eLpNorm_lqNorm_eq_const_mul _
    (fun j => (aestronglyMeasurable_periodicBlockFun j f).enorm.const_mul _) <| by
      filter_upwards [periodicBlockFun_smul_ae c f] with t ht j
      rw [ht j, enorm_mul, mul_left_comm]

omit [Fact (1 ≤ p)] in
/-- The zero function has quasi-norm `0`. -/
theorem periodicTriebelLizorkinNorm_zero (s : ℝ) (q : ℝ≥0∞) :
    periodicTriebelLizorkinNorm s q (0 : Lp ℂ p (volume : Measure (UnitAddTorus d))) = 0 := by
  simpa using
    periodicTriebelLizorkinNorm_smul s q (0 : ℂ) (0 : Lp ℂ p (volume : Measure (UnitAddTorus d)))

omit [Fact (1 ≤ p)] in
/-- **Smoothness `0`**: `‖f‖_{F^0_{p,q}(𝕋^d)} = ‖ t ↦ ‖((ψ_j ⋆ f)(t))_j‖_{ℓ_q} ‖_p` for every `q`,
since the weights `2^(j·0)` are `1`. -/
theorem periodicTriebelLizorkinNorm_zero_left (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm 0 q f =
      eLpNorm (fun t => lqNorm q fun j => ‖periodicBlockFun j f t‖ₑ) p volume :=
  eLpNorm_lqNorm_dyadicWeight_zero_left _

omit [Fact (1 ≤ p)] in
/-- **The quasi-norm decreases in `q`**: `‖f‖_{F^s_{p,r}} ≤ ‖f‖_{F^s_{p,q}}` for
`1 ≤ q ≤ r ≤ ∞`, since `‖·‖_{ℓ_r} ≤ ‖·‖_{ℓ_q}` at every point. -/
theorem periodicTriebelLizorkinNorm_mono_exponent {s : ℝ} {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm s r f ≤ periodicTriebelLizorkinNorm s q f :=
  eLpNorm_lqNorm_mono_exponent (zero_lt_one.trans_le hq).ne' hqr fun j =>
    (aestronglyMeasurable_periodicBlockFun j f).enorm.const_mul _

omit [Fact (1 ≤ p)] in
/-- **The quasi-norm increases in `s`**: `‖f‖_{F^s_{p,q}} ≤ ‖f‖_{F^t_{p,q}}` for `s ≤ t`, since
`2^(js) ≤ 2^(jt)`. -/
theorem periodicTriebelLizorkinNorm_mono_smoothness {s t : ℝ} (hst : s ≤ t) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm s q f ≤ periodicTriebelLizorkinNorm t q f :=
  eLpNorm_lqNorm_dyadicWeight_mono_smoothness hst fun j =>
    (aestronglyMeasurable_periodicBlockFun j f).enorm

omit [Fact (1 ≤ p)] in
/-- **Weighted blocks with terms set to zero**: for every predicate `P` on `ℕ`,
`‖ t ↦ ‖(1_P(j) 2^{js} |(ψ_j ⋆ f)(t)|)_j‖_{ℓ_q} ‖_p ≤ ‖f‖_{F^s_{p,q}(𝕋^d)}`, where the terms with
`P j` false are `0` (`MeasureTheory.eLpNorm_lqNorm_ite_le`). -/
theorem eLpNorm_lqNorm_ite_periodicBlockFun_le {P : ℕ → Prop} [DecidablePred P] (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    eLpNorm (fun t => lqNorm q fun j =>
      if P j then dyadicWeight s j * ‖periodicBlockFun j f t‖ₑ else 0) p volume ≤
      periodicTriebelLizorkinNorm s q f :=
  eLpNorm_lqNorm_ite_le fun j => (aestronglyMeasurable_periodicBlockFun j f).enorm.const_mul _

/-- **The tails of the weighted blocks tend to zero**: for `1 ≤ p < ∞`, `0 < q < ∞`, `s ∈ ℝ` and
`f ∈ F^s_{p,q}(𝕋^d)`, `‖ t ↦ ‖(2^{js} (ψ_j ⋆ f)(t))_{j ≥ N}‖_{ℓ_q} ‖_p → 0` as `N → ∞`, where
the terms `j < N` are `0` (`MeasureTheory.tendsto_eLpNorm_lqNorm_ite_le`). -/
theorem tendsto_eLpNorm_lqNorm_periodicBlockFun_tail (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : MemPeriodicTriebelLizorkin s q f) :
    Tendsto (fun N => eLpNorm (fun t => lqNorm q fun j =>
      if N ≤ j then dyadicWeight s j * ‖periodicBlockFun j f t‖ₑ else 0) p volume) atTop (𝓝 0) :=
  tendsto_eLpNorm_lqNorm_ite_le (zero_lt_one.trans_le Fact.out).ne' hp hq0 hq
    (fun j => (aestronglyMeasurable_periodicBlockFun j f).enorm.const_mul _) hf.ne

/-! ### The spaces `F^s_{p,q}(𝕋^d)` -/

omit [Fact (1 ≤ p)] in
/-- **`F^s_{p,q}(𝕋^d)` increases in `q`**: `F^s_{p,q} ⊆ F^s_{p,r}` for `1 ≤ q ≤ r ≤ ∞`. -/
theorem MemPeriodicTriebelLizorkin.mono_exponent {s : ℝ} {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemPeriodicTriebelLizorkin s q f) :
    MemPeriodicTriebelLizorkin s r f :=
  (periodicTriebelLizorkinNorm_mono_exponent hq hqr f).trans_lt hf

omit [Fact (1 ≤ p)] in
/-- **`F^s_{p,q}(𝕋^d)` decreases in `s`**: `F^t_{p,q} ⊆ F^s_{p,q}` for `s ≤ t`. -/
theorem MemPeriodicTriebelLizorkin.mono_smoothness {s t : ℝ} (hst : s ≤ t) {q : ℝ≥0∞}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemPeriodicTriebelLizorkin t q f) :
    MemPeriodicTriebelLizorkin s q f :=
  (periodicTriebelLizorkinNorm_mono_smoothness hst q f).trans_lt hf

/-- `F^s_{p,q}(𝕋^d)` is closed under addition, for `1 ≤ q ≤ ∞`. -/
theorem MemPeriodicTriebelLizorkin.add {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f g : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemPeriodicTriebelLizorkin s q f)
    (hg : MemPeriodicTriebelLizorkin s q g) : MemPeriodicTriebelLizorkin s q (f + g) :=
  (periodicTriebelLizorkinNorm_add_le hq f g).trans_lt (ENNReal.add_lt_top.2 ⟨hf, hg⟩)

omit [Fact (1 ≤ p)] in
/-- `F^s_{p,q}(𝕋^d)` is closed under complex multiples. -/
theorem MemPeriodicTriebelLizorkin.smul {s : ℝ} {q : ℝ≥0∞} (c : ℂ)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemPeriodicTriebelLizorkin s q f) :
    MemPeriodicTriebelLizorkin s q (c • f) := by
  rw [MemPeriodicTriebelLizorkin, periodicTriebelLizorkinNorm_smul]
  exact ENNReal.mul_lt_top enorm_lt_top hf

/-- The **Triebel–Lizorkin space** `F^s_{p,q}(𝕋^d)` as a subspace of `L_p(𝕋^d)`, for
`1 ≤ p ≤ ∞`, `s ∈ ℝ` and `1 ≤ q ≤ ∞`, with real scalars as `FunctionScheme.besovSpace`. -/
noncomputable def periodicTriebelLizorkinSpace (s : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    Submodule ℝ (Lp ℂ p (volume : Measure (UnitAddTorus d))) where
  carrier := {f | MemPeriodicTriebelLizorkin s q f}
  add_mem' hf hg := hf.add hq hg
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, MemPeriodicTriebelLizorkin, periodicTriebelLizorkinNorm_zero]
    exact ENNReal.zero_lt_top
  smul_mem' r f hf := by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r f]
    exact hf.smul _

/-- Membership in the subspace `F^s_{p,q}(𝕋^d)` is a finite Triebel–Lizorkin quasi-norm. -/
theorem mem_periodicTriebelLizorkinSpace {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    f ∈ periodicTriebelLizorkinSpace s q hq ↔ MemPeriodicTriebelLizorkin s q f :=
  Iff.rfl

/-! ### Comparison with the Besov spaces -/

/-- The Littlewood–Paley quasi-norm on the torus in terms of the pointwise blocks:
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q} = ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q}`. -/
theorem periodicLittlewoodPaleyNorm_eq_lqNorm_eLpNorm (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicLittlewoodPaleyNorm hp s q f =
      lqNorm q (fun j => dyadicWeight s j * eLpNorm (periodicBlockFun j f) p volume) := by
  simp only [periodicLittlewoodPaleyNorm, enorm_periodicLpBlock_eq_eLpNorm_periodicBlockFun hp]

/-- **For `q = p` the two quasi-norms agree**: for every `s ∈ ℝ`,
`‖f‖_{F^s_{p,p}} = ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_p}` on `L_p(𝕋^d)`, by Tonelli's theorem
(`L_p(ℓ_p) = ℓ_p(L_p)`). -/
theorem periodicTriebelLizorkinNorm_eq_periodicLittlewoodPaleyNorm (hp : p ≠ ∞) (s : ℝ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm s p f = periodicLittlewoodPaleyNorm hp s p f := by
  rw [periodicLittlewoodPaleyNorm_eq_lqNorm_eLpNorm]
  exact eLpNorm_lqNorm_dyadicWeight_eq (zero_lt_one.trans_le Fact.out).ne' hp
    fun j => aestronglyMeasurable_periodicBlockFun j f

/-- **`F^s_{p,p}(𝕋^d) = B^s_{p,p}(𝕋^d)`**: for `1 ≤ p < ∞` and `s > 0`, `f ∈ F^s_{p,p}` iff `f`
lies in the Besov space `B^s_{p,p}(𝕋^d)`, the approximation space of the trigonometric
polynomials. -/
theorem memPeriodicTriebelLizorkin_iff_memBesov (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    MemPeriodicTriebelLizorkin s p f ↔ (trigScheme d).MemBesov volume p s p f := by
  rw [memBesov_iff_periodicLittlewoodPaleyNorm_lt_top hp hs Fact.out, MemPeriodicTriebelLizorkin,
    periodicTriebelLizorkinNorm_eq_periodicLittlewoodPaleyNorm hp]

/-- **The lower bound of the Triebel–Lizorkin quasi-norm on the torus**: for `1 ≤ p < ∞`,
`s ∈ ℝ` and `1 ≤ q ≤ ∞`, `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{max(p,q)}} ≤ ‖f‖_{F^s_{p,q}}`. -/
theorem periodicLittlewoodPaleyNorm_max_le_periodicTriebelLizorkinNorm (hp : p ≠ ∞) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicLittlewoodPaleyNorm hp s (max p q) f ≤ periodicTriebelLizorkinNorm s q f := by
  rw [periodicLittlewoodPaleyNorm_eq_lqNorm_eLpNorm]
  exact lqNorm_max_dyadicWeight_le Fact.out hp hq fun j => aestronglyMeasurable_periodicBlockFun j f

/-- **The upper bound of the Triebel–Lizorkin quasi-norm on the torus**: for `1 ≤ p < ∞`,
`s ∈ ℝ` and `1 ≤ q ≤ ∞`, `‖f‖_{F^s_{p,q}} ≤ ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{min(p,q)}}`. -/
theorem periodicTriebelLizorkinNorm_le_periodicLittlewoodPaleyNorm_min (hp : p ≠ ∞) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm s q f ≤ periodicLittlewoodPaleyNorm hp s (min p q) f := by
  rw [periodicLittlewoodPaleyNorm_eq_lqNorm_eLpNorm]
  exact eLpNorm_lqNorm_dyadicWeight_le_min Fact.out hp hq fun j =>
    aestronglyMeasurable_periodicBlockFun j f

/-- **`F^s_{p,q}(𝕋^d) ⊆ B^s_{p,max(p,q)}(𝕋^d)` with a constant**: for `1 ≤ p < ∞`, `s > 0` and
`1 ≤ q ≤ ∞`, the approximation norm of `f` in `A^s_{max(p,q)}` of the trigonometric polynomials
is at most `2 · 2^s (1 - 2^(-s))⁻¹ ‖f‖_{F^s_{p,q}}`. -/
theorem approxNormDyadic_le_periodicTriebelLizorkinNorm (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume p).approxNormDyadic s (max p q) f ≤
      2 * dyadicWeight s 1 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * periodicTriebelLizorkinNorm s q f :=
  (approxNormDyadic_trigScheme_le hp hs (le_max_of_le_right hq) f).trans
    (by gcongr; exact periodicLittlewoodPaleyNorm_max_le_periodicTriebelLizorkinNorm hp hq f)

/-- **`B^s_{p,min(p,q)}(𝕋^d) ⊆ F^s_{p,q}(𝕋^d)` with a constant**: for `1 ≤ p < ∞`, `s ≥ 0` and
`1 ≤ q ≤ ∞`, `‖f‖_{F^s_{p,q}} ≤ 2 (#d + 1) 2^((#d + 1) s) ‖Φ‖_1` times the approximation norm of
`f` in `A^s_{min(p,q)}` of the trigonometric polynomials. -/
theorem periodicTriebelLizorkinNorm_le_approxNormDyadic (hp : p ≠ ∞) {s : ℝ} (hs : 0 ≤ s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm s q f ≤
      2 * ((Fintype.card d : ℝ≥0∞) + 1) * dyadicWeight s (Fintype.card d + 1) *
        eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume *
          ((trigScheme d).toLp volume p).approxNormDyadic s (min p q) f :=
  (periodicTriebelLizorkinNorm_le_periodicLittlewoodPaleyNorm_min hp hq f).trans
    (periodicLittlewoodPaleyNorm_le_approxNormDyadic_trigScheme hp hs (le_min Fact.out hq) f)

/-- **`F^s_{p,q}(𝕋^d) ⊆ B^s_{p,max(p,q)}(𝕋^d)`**: for `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`.
For `q = 2`: `F^s_{p,2}(𝕋^d) ⊆ B^s_{p,max(p,2)}(𝕋^d)`. -/
theorem memBesov_of_memPeriodicTriebelLizorkin (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : MemPeriodicTriebelLizorkin s q f) : (trigScheme d).MemBesov volume p s (max p q) f :=
  (memBesov_iff_periodicLittlewoodPaleyNorm_lt_top hp hs (le_max_of_le_right hq)).2
    ((periodicLittlewoodPaleyNorm_max_le_periodicTriebelLizorkinNorm hp hq f).trans_lt hf)

/-- **`B^s_{p,min(p,q)}(𝕋^d) ⊆ F^s_{p,q}(𝕋^d)`**: for `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`.
For `q = 2`: `B^s_{p,min(p,2)}(𝕋^d) ⊆ F^s_{p,2}(𝕋^d)`. -/
theorem memPeriodicTriebelLizorkin_of_memBesov (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : (trigScheme d).MemBesov volume p s (min p q) f) : MemPeriodicTriebelLizorkin s q f :=
  (periodicTriebelLizorkinNorm_le_periodicLittlewoodPaleyNorm_min hp hq f).trans_lt
    ((memBesov_iff_periodicLittlewoodPaleyNorm_lt_top hp hs (le_min Fact.out hq)).1 hf)

/-- **`F^s_{p,p}(𝕋^d)` by differences**: for `1 ≤ p < ∞` and `0 < s < r`, `f ∈ F^s_{p,p}` iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_p} < ∞`, through `F^s_{p,p} = B^s_{p,p}` and the
description of `B^s_{p,p}(𝕋^d)` by moduli of smoothness. -/
theorem memPeriodicTriebelLizorkin_iff_modulus (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    MemPeriodicTriebelLizorkin s p f ↔
      ‖f‖ₑ + lqNorm p (fun k => dyadicWeight s k * Rd.lpModulus p r f k) < ∞ :=
  (memPeriodicTriebelLizorkin_iff_memBesov hp hs).trans
    (memBesov_iff_modNorm_lt_top_lp hp hs hsr Fact.out f)

end Torus
