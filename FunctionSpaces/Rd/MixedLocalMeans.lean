/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.MixedAveragedDifferences
public import FunctionSpaces.Rd.LocalMeans

/-!
# Mixed local means

Let `b` be a bump for local means on `ℝ` (`Rd.LocalMeansBump ℝ`) with the kernels `k_j` and the
dual kernels `η_j` of `FunctionSpaces.Rd.LocalMeans`. On `ℝ^d = Fin d → ℝ` the **mixed local means**
of `f ∈ L_p` are `k_k ⋆ f` with the tensor kernels `k_k = ⊗_i k_{k_i}`, `k ∈ ℕ^d`
(`Rd.LocalMeansBump.mixedKernel`, `Rd.LocalMeansBump.mixedLocalMean`), and the **mixed local means
quasi-norm** is `‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_{k ∈ ℕ^d}‖_{ℓ_q(ℕ^d)}`
(`Rd.LocalMeansBump.mixedLocalMeansNorm`).

**Local means are bounded by the mixed modulus** (`Rd.LocalMeansBump.enorm_mixedLocalMean_le`):
if the bump vanishes outside `[-1, 1]`, then
`‖k_k ⋆ f‖_p ≤ (‖g‖_1 (2^L + 1))^d Ω^{e(k)}_L(f, 2^(-k))_p`. In one variable
`k_j = ∑_l a_l (g_{2^j/(l+1)} - g_{2^j/(2(l+1))})` for `j ≥ 1` and `k_0 = ∑_l a_l g_{1/(l+1)}`
(`Rd.LocalMeansBump.kernel_eq_sum_dilate`), with the polynomials `P(Y) - P(Y²)` and `P(Y)` in the
translation `Y = δ_{-z/2^j}`, `P(Y) = 1 - (-1)^L (Y - 1)^L`. Since
`P(Y) - P(Y²) = (Y - 1)^L (-1)^L ((Y + 1)^L - 1)`, the tensor kernel averages the mixed differences
`Δ^{L,e(k)}_h f` with steps `|h_i| ≤ 2^(-k_i)` (`Rd.conv_tensorKernel_sum_dilate_ae`), and
Minkowski's inequality (`Rd.eLpNorm_integral_kernel_le`) gives the bound.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

open ENNReal (dyadicWeight)

namespace Rd

/-! ### Convolution, dilation and sums of kernels -/

section Helpers

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-- **Dilations commute with convolution**: `A_c ⋆ B_c = (A ⋆ B)_c` for `c > 0`. -/
theorem conv_dilate_dilate (A B : V → ℂ) {c : ℝ} (hc : 0 < c) :
    conv (dilate c A) (dilate c B) μ = dilate c (conv A B μ) := by
  funext x
  rw [conv_dilate_apply _ _ hc, dilate, conv_apply, ← integral_const_mul]
  congr 1
  funext z
  simp only [dilate, smul_sub, smul_inv_smul₀ hc.ne']
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Convolution operators with equal kernels are equal. -/
theorem convLp_congr (hp : p ≠ ∞) {K K' : V → ℂ} (hK : Integrable K μ) (hK' : Integrable K' μ)
    (h : K = K') (f : Lp ℂ p μ) : convLp hp hK f = convLp hp hK' f := by
  subst h
  rfl

/-- **Convolution is linear in the kernel**: `∑_i K_i ⋆ f = (∑_i K_i) ⋆ f` on `L_p`. -/
theorem convLp_finsetSum_kernel (hp : p ≠ ∞) {ι : Type*} (s : Finset ι) {K : ι → V → ℂ}
    (hK : ∀ i, Integrable (K i) μ) (f : Lp ℂ p μ) :
    ∑ i ∈ s, convLp hp (hK i) f = convLp hp (integrable_finsetSum s fun i _ => hK i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact (convLp_of_eq_zero hp _ (by funext a; simp) f).symm
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ih,
      ← convLp_add_kernel hp (hK i) (integrable_finsetSum s fun i _ => hK i)]
    exact convLp_congr hp _ _ (by funext a; simp [Finset.sum_insert hi]) f

/-- `(A + B) ⋆ (A - B) = A ⋆ A - B ⋆ B` for continuous kernels with compact support. -/
theorem conv_add_conv_sub {A B : ℝ → ℂ} (hA : Continuous A) (hAc : HasCompactSupport A)
    (hB : Continuous B) (hBc : HasCompactSupport B) :
    conv (A + B) (A - B) volume = conv A A volume - conv B B volume := by
  have hex : ∀ {F G : ℝ → ℂ}, Continuous F → HasCompactSupport F → Continuous G →
      ConvolutionExists F G (ContinuousLinearMap.mul ℂ ℂ) volume := fun hF hFc hG =>
    hFc.convolutionExists_left _ hF hG.locallyIntegrable
  have hsub : A - B = A + (-1 : ℂ) • B := by
    funext x
    simp [sub_eq_add_neg]
  have h1 : conv (A + B) (A - B) volume = conv A (A - B) volume + conv B (A - B) volume :=
    ConvolutionExists.add_distrib (hex hA hAc (hA.sub hB)) (hex hB hBc (hA.sub hB))
  have h2 : ∀ F : ℝ → ℂ, Continuous F → HasCompactSupport F →
      conv F (A - B) volume = conv F A volume - conv F B volume := fun F hF hFc => by
    have h := ConvolutionExists.distrib_add (hex hF hFc hA) (hex hF hFc (hB.const_smul (-1 : ℂ)))
    have h' : conv F (A + (-1 : ℂ) • B) volume = conv F A volume + conv F ((-1 : ℂ) • B) volume :=
      h
    rw [hsub, h', conv_smul, neg_one_smul, sub_eq_add_neg]
  rw [h1, h2 A hA hAc, h2 B hB hBc, conv_comm B A]
  abel

/-- **Subadditive functionals and multiple series**: if `Q` is subadditive, `Q a ≤ C ‖a‖` with
`C < ∞`, and the partial sums of `∑ u_k` over finite sets `S_J` converge to `F`, then
`Q F ≤ ∑_k Q(u_k)`. -/
theorem le_tsum_of_tendsto_finsetSum {E ι : Type*} [NormedAddCommGroup E] {Q : E → ℝ≥0∞}
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hadd : ∀ a b, Q (a + b) ≤ Q a + Q b) (hle : ∀ a, Q a ≤ C * ‖a‖ₑ)
    {S : ℕ → Finset ι} {u : ι → E} {F : E}
    (hu : Tendsto (fun J => ∑ k ∈ S J, u k) atTop (𝓝 F)) :
    Q F ≤ ∑' k, Q (u k) := by
  have hsum : ∀ s : Finset ι, Q (∑ k ∈ s, u k) ≤ ∑ k ∈ s, Q (u k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hle 0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (hadd _ _).trans (add_le_add le_rfl ih)
  have hJ : ∀ J, Q F ≤ ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ := fun J => by
    calc Q F = Q (∑ k ∈ S J, u k + (F - ∑ k ∈ S J, u k)) := by rw [add_sub_cancel]
      _ ≤ Q (∑ k ∈ S J, u k) + Q (F - ∑ k ∈ S J, u k) := hadd _ _
      _ ≤ ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ :=
          add_le_add ((hsum _).trans (ENNReal.sum_le_tsum _)) (hle _)
  have h1 : Tendsto (fun J => F - ∑ k ∈ S J, u k) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := F)).sub hu
    rwa [sub_self] at this
  have h2 : Tendsto (fun J => ‖F - ∑ k ∈ S J, u k‖ₑ) atTop (𝓝 0) := by
    have h3 := (continuous_enorm.tendsto (0 : E)).comp h1
    rw [enorm_zero] at h3
    exact h3
  have hlim : Tendsto (fun J => ∑' k, Q (u k) + C * ‖F - ∑ k ∈ S J, u k‖ₑ) atTop
      (𝓝 (∑' k, Q (u k) + C * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul h2 (Or.inr hC))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hJ)

end Helpers

namespace LocalMeansBump

variable {d : ℕ} (b : LocalMeansBump ℝ)

/-! ### Mixed kernels -/

/-- The **mixed local means kernels** `k_k = ⊗_i k_{k_i}`. -/
noncomputable def mixedKernel (L : ℕ) (k : Fin d → ℕ) : (Fin d → ℝ) → ℂ :=
  tensorKernel fun i => b.kernel L (k i)

/-- The **mixed dual kernels** `η_k = ⊗_i η_{k_i}`. -/
noncomputable def mixedDual (L : ℕ) (k : Fin d → ℕ) : (Fin d → ℝ) → ℂ :=
  tensorKernel fun i => b.dual L (k i)

/-- The mixed kernels are integrable. -/
theorem integrable_mixedKernel (L : ℕ) (k : Fin d → ℕ) : Integrable (b.mixedKernel L k) :=
  integrable_tensorKernel fun i => b.integrable_kernel L (k i)

/-- The mixed dual kernels are integrable. -/
theorem integrable_mixedDual (L : ℕ) (k : Fin d → ℕ) : Integrable (b.mixedDual L k) :=
  integrable_tensorKernel fun i => b.integrable_dual L (k i)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **mixed local means** `f ↦ k_k ⋆ f` on `L_p(ℝ^d)`. -/
noncomputable def mixedLocalMean (hp : p ≠ ∞) (L : ℕ) (k : Fin d → ℕ) :
    Lp ℂ p (volume : Measure (Fin d → ℝ)) →L[ℂ] Lp ℂ p (volume : Measure (Fin d → ℝ)) :=
  convLp hp (b.integrable_mixedKernel L k)

/-- The **mixed local means quasi-norm** `‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_{k ∈ ℕ^d}‖_{ℓ_q(ℕ^d)}`. -/
noncomputable def mixedLocalMeansNorm (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) : ℝ≥0∞ :=
  mixedLqNorm q fun k => mixedWeight s k * ‖b.mixedLocalMean hp L k f‖ₑ

/-! ### The local means kernels as sums of dilated bumps -/

/-- The exponents of the local means kernels: `l + 1` and `2(l + 1)`. -/
def lmExp : Bool × ℕ → ℕ
  | (true, l) => l + 1
  | (false, l) => 2 * (l + 1)

/-- The coefficients of the local means kernel `k_j`: `a_l` at `Y^(l+1)`, and `-a_l` at
`Y^(2(l+1))` for `j ≥ 1`, with the coefficients `a_l = (-1)^l C(L, l + 1)` of the moment
kernels. -/
noncomputable def lmCoeff (L j : ℕ) : Bool × ℕ → ℂ
  | (true, l) => jacksonCoeff L l
  | (false, l) => if j = 0 then 0 else -jacksonCoeff L l

/-- The exponents are at least `1`. -/
theorem one_le_lmExp (t : Bool × ℕ) : 1 ≤ lmExp t := by
  rcases t with ⟨_ | _, l⟩
  · show 1 ≤ 2 * (l + 1)
    omega
  · show 1 ≤ l + 1
    omega

/-- **The local means kernels are sums of dilated bumps**:
`k_j = ∑_l a_l (g_{2^j/(l+1)} - g_{2^j/(2(l+1))})` for `j ≥ 1` and `k_0 = ∑_l a_l g_{1/(l+1)}`. -/
theorem kernel_eq_sum_dilate (L j : ℕ) :
    b.kernel L j = ∑ t ∈ Finset.univ ×ˢ Finset.range L,
      lmCoeff L j t • dilate ((2 : ℝ) ^ j / lmExp t) b.toFun := by
  rw [Finset.sum_product, Fintype.sum_bool]
  funext x
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, lmCoeff, lmExp]
  cases j with
  | zero =>
    simp only [↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero]
    show b.scaled L 0 x = _
    rw [scaled, dilate_momentKernel]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring_nf
  | succ j =>
    show (b.scaled L (j + 1) - b.scaled L j) x = _
    rw [Pi.sub_apply, scaled, scaled, dilate_momentKernel, dilate_momentKernel,
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring_nf
    · refine Finset.sum_congr rfl fun l _ => ?_
      have h : (2 : ℝ) ^ (j + 1) / ((2 * (l + 1) : ℕ) : ℝ) = 2 ^ j / ((l : ℝ) + 1) := by
        push_cast
        rw [pow_succ]
        field_simp
      rw [h]
      ring

/-! ### Local means are bounded by the mixed modulus -/

/-- **The polynomial of one coordinate factors through a difference**: for `j ≥ 1`,
`∑_t c_j(t) Y^{ν(t)} = (Y - 1)^L (-1)^L ((Y + 1)^L - 1)`, and for `j = 0` it is `P(Y)`. -/
theorem sum_lmCoeff_smul_pow {A : Type*} [CommRing A] [Algebra ℂ A] (L j : ℕ) (Y : A) :
    ∑ t ∈ Finset.univ ×ˢ Finset.range L, lmCoeff L j t • Y ^ lmExp t =
      if j = 0 then 1 - (-1) ^ L * (Y - 1) ^ L
      else (Y - 1) ^ L * ((-1) ^ L * ((Y + 1) ^ L - 1)) := by
  rw [Finset.sum_product, Fintype.sum_bool]
  simp only [lmCoeff, lmExp]
  have hP := sum_jacksonCoeff_smul_pow L Y
  have hP2 := sum_jacksonCoeff_smul_pow L (Y ^ 2)
  simp_rw [← pow_mul] at hP2
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte, zero_smul, Finset.sum_const_zero, add_zero]
    exact hP
  · simp only [hj, ↓reduceIte, neg_smul, Finset.sum_neg_distrib]
    rw [hP, hP2, show Y ^ 2 - 1 = (Y - 1) * (Y + 1) by ring, mul_pow]
    ring

/-- **Mixed local means are bounded by the mixed modulus**: if the bump `g` vanishes outside
`[-1, 1]`, then `‖k_k ⋆ f‖_p ≤ (‖g‖_1 (2^L + 1))^d Ω^{e(k)}_L(f, 2^(-k))_p`. The tensor kernel
averages `B(z) Δ^{L,e(k)}_{h(z)} f` with `h(z)_i = -z_i/2^(k_i)` over `(⊗g)(z) dz`, where the
remaining polynomials `B(z)` in the translations act with norm at most `(2^L + 1)^d`. -/
theorem enorm_mixedLocalMean_le (hp : p ≠ ∞) (L : ℕ) (hR : b.radius ≤ 1) (k : Fin d → ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖b.mixedLocalMean hp L k f‖ₑ ≤
      ((∫⁻ t, ‖b.toFun t‖ₑ) * (2 ^ L + 1)) ^ d * lpMixedModulus p L f k := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set e := mixedSupp k
  set T := (Finset.univ ×ˢ Finset.range L : Finset (Bool × ℕ))
  set c : Fin d → ℝ := fun i => 2 ^ k i
  have hc : ∀ i, 0 < c i := fun i => by positivity
  set h : (Fin d → ℝ) → Fin d → ℝ := fun z i => -z i / c i
  set Y : (Fin d → ℝ) → Fin d → AddMonoidAlgebra ℂ (Fin d → ℝ) := fun z i =>
    AddMonoidAlgebra.single (Pi.single i (h z i)) (1 : ℂ)
  set A : (Fin d → ℝ) → AddMonoidAlgebra ℂ (Fin d → ℝ) := fun z =>
    ∏ i, ∑ t ∈ T, lmCoeff L (k i) t •
      AddMonoidAlgebra.single (Pi.single i (-z i / c i)) (1 : ℂ) ^ lmExp t
  set G : (Fin d → ℝ) → (Fin d → ℝ) → ℂ := fun x z =>
    Cube.diffAct (A z) (f : (Fin d → ℝ) → ℂ) x
  set Φ : (Fin d → ℝ) → ℂ := tensorKernel fun _ => b.toFun
  set ω := lpMixedModulus p L f k
  -- the local means average the translates
  have hkernel : b.mixedKernel L k = tensorKernel fun i =>
      ∑ t ∈ T, lmCoeff L (k i) t • dilate (c i / lmExp t) b.toFun := by
    simp only [mixedKernel, c]
    congr 1
    funext i
    exact b.kernel_eq_sum_dilate L (k i)
  have hae : (b.mixedLocalMean hp L k f : (Fin d → ℝ) → ℂ) =ᵐ[volume]
      fun x => ∫ z, Φ z * G x z := by
    have h1 := convLp_apply_ae hp (b.integrable_mixedKernel L k) f
    have h2 := conv_tensorKernel_sum_dilate_ae hp1 hp b.integrable T lmExp
      (fun t _ => one_le_lmExp t) (fun i => lmCoeff L (k i)) hc (Lp.memLp f)
    rw [← hkernel] at h2
    exact h1.trans h2
  -- the translates are jointly measurable
  have hfm : Measurable (f : (Fin d → ℝ) → ℂ) := (Lp.stronglyMeasurable f).measurable
  have hG : Measurable (Function.uncurry G) := by
    have heq : Function.uncurry G = fun q : (Fin d → ℝ) × (Fin d → ℝ) =>
        ∑ n ∈ Fintype.piFinset (fun _ => T), (∏ i, lmCoeff L (k i) (n i)) *
          (f : (Fin d → ℝ) → ℂ) (q.1 + fun i => (lmExp (n i) : ℝ) * (-q.2 i / c i)) := by
      funext q
      exact diffAct_prod_sum_pow_apply T lmExp (fun i => lmCoeff L (k i)) (fun i => -q.2 i / c i)
        _ q.1
    rw [heq]
    refine Finset.measurable_sum _ fun n _ => measurable_const.mul (hfm.comp ?_)
    exact measurable_fst.add (measurable_pi_iff.2 fun i => measurable_const.mul
      (((measurable_pi_apply i).comp measurable_snd).neg.div_const _))
  -- the polynomials factor through the mixed difference
  set B : (Fin d → ℝ) → AddMonoidAlgebra ℂ (Fin d → ℝ) := fun z => ∏ i,
    if k i = 0 then 1 - (-1) ^ L * (Y z i - 1) ^ L else (-1) ^ L * ((Y z i + 1) ^ L - 1)
  have hfactor : ∀ z, A z = B z * ∏ i ∈ e, Cube.coordElem (h z) i ^ L := fun z => by
    have hfac : ∀ i, ∑ t ∈ T, lmCoeff L (k i) t •
        AddMonoidAlgebra.single (Pi.single i (-z i / c i)) (1 : ℂ) ^ lmExp t =
        (if k i = 0 then 1 - (-1) ^ L * (Y z i - 1) ^ L else (-1) ^ L * ((Y z i + 1) ^ L - 1)) *
          (if k i = 0 then 1 else Cube.coordElem (h z) i ^ L) := fun i => by
      rw [sum_lmCoeff_smul_pow]
      simp only [Y, h]
      by_cases hk : k i = 0
      · simp [hk]
      · simp only [hk, ↓reduceIte, Cube.coordElem]
        ring
    simp only [A, B]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
    rfl
  have hGz : ∀ z, (fun x => G x z) =
      Cube.diffAct (B z) (mixedDiff L e (h z) (f : (Fin d → ℝ) → ℂ)) := fun z => by
    funext x
    simp only [G]
    rw [hfactor z, map_mul, Module.End.mul_apply]
    rfl
  -- the remaining polynomials act boundedly
  have hB : ∀ z, ActsBounded p (B z) ((2 ^ L + 1) ^ d) := fun z => by
    have h := ActsBounded.prod (p := p) (Finset.univ : Finset (Fin d))
      (a := fun i => if k i = 0 then 1 - (-1) ^ L * (Y z i - 1) ^ L
        else (-1) ^ L * ((Y z i + 1) ^ L - 1)) (C := fun _ => (2 : ℝ≥0∞) ^ L + 1)
      fun i _ => by
        by_cases hk : k i = 0
        · simp only [hk, ↓reduceIte]
          exact (actsBounded_momentPoly hp1 L _).mono (add_comm _ _).le
        · simp only [hk, ↓reduceIte]
          exact actsBounded_addPoly hp1 L _
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  -- the bound on the support of the weight
  have hbound : ∀ z, Φ z ≠ 0 →
      eLpNorm (fun x => G x z) p volume ≤ (2 ^ L + 1) ^ d * ω := fun z hz => by
    have hzR : ∀ i, |z i| ≤ 1 := fun i => by
      have hgi : b.toFun (z i) ≠ 0 := fun h0 =>
        hz (Finset.prod_eq_zero (Finset.mem_univ i) h0)
      have := not_lt.1 fun hlt => hgi (b.eq_zero (z i) hlt)
      exact (Real.norm_eq_abs _ ▸ this).trans hR
    have hsteps : ∀ i ∈ e, |h z i| ≤ 1 / 2 ^ k i := fun i _ => by
      simp only [h, c, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k i)]
      exact div_le_div_of_nonneg_right (hzR i) (by positivity)
    rw [hGz z]
    refine ((hB z) _ (aestronglyMeasurable_mixedDiff (Lp.aestronglyMeasurable f) L e (h z))).2.trans
      (mul_le_mul' le_rfl ?_)
    exact eLpNorm_mixedDiff_le_mixedModulus hsteps
  -- Minkowski's inequality
  set A₀ := ∫⁻ z, ‖Φ z‖ₑ
  have hA₀ : A₀ = (∫⁻ t, ‖b.toFun t‖ₑ) ^ d := by
    simp only [A₀, Φ]
    rw [lintegral_enorm_tensorKernel fun _ => b.integrable, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hg0 : (∫⁻ t, ‖b.toFun t‖ₑ) ≠ 0 :=
    lintegral_enorm_ne_zero_of_integral_eq_one b.integrable b.integral_eq_one
  have hA0 : A₀ ≠ 0 := by
    rw [hA₀]
    exact pow_ne_zero _ hg0
  have hAt : A₀ ≠ ∞ := by
    rw [hA₀]
    exact ENNReal.pow_ne_top b.integrable.2.ne
  have hΦ : AEStronglyMeasurable Φ volume :=
    (integrable_tensorKernel fun _ => b.integrable).aestronglyMeasurable
  set C := (2 : ℝ≥0∞) ^ L + 1
  rw [Lp.enorm_def, eLpNorm_congr_ae hae, ← ENNReal.rpow_le_rpow_iff hq]
  refine (eLpNorm_integral_kernel_le hp1 hp hΦ hG).trans ?_
  calc A₀ ^ (p.toReal - 1) * ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => G x z) p volume ^ p.toReal
      ≤ A₀ ^ (p.toReal - 1) * ∫⁻ z, ‖Φ z‖ₑ * (C ^ d * ω) ^ p.toReal :=
        mul_le_mul' le_rfl (lintegral_mono fun z => by
          by_cases hz : Φ z = 0
          · simp [hz]
          · exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hbound z hz) hq.le))
    _ = A₀ ^ (p.toReal - 1) * A₀ ^ (1 : ℝ) * (C ^ d * ω) ^ p.toReal := by
        rw [lintegral_mul_const'' _ hΦ.enorm, ENNReal.rpow_one, mul_assoc]
    _ = (A₀ * (C ^ d * ω)) ^ p.toReal := by
        rw [← ENNReal.rpow_add _ _ hA0 hAt, sub_add_cancel,
          ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    _ = (((∫⁻ t, ‖b.toFun t‖ₑ) * C) ^ d * ω) ^ p.toReal := by
        rw [hA₀, mul_pow, mul_assoc]

/-- **Local means quasi-norm and differences**:
`‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_k‖_{ℓ_q} ≤ (‖g‖_1 (2^L + 1))^d ‖(2^(s|k|_1) Ω^{e(k)}_L(f, 2^(-k))_p)_k‖_{ℓ_q}`
for a bump vanishing outside `[-1, 1]`. -/
theorem mixedLocalMeansNorm_le (hp : p ≠ ∞) (L : ℕ) (hR : b.radius ≤ 1) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    b.mixedLocalMeansNorm hp L s q f ≤
      ((∫⁻ t, ‖b.toFun t‖ₑ) * (2 ^ L + 1)) ^ d * mixedModNorm p L s q f := by
  rw [mixedModNorm, ← mixedLqNorm_const_mul]
  refine mixedLqNorm_mono fun k => ?_
  calc mixedWeight s k * ‖b.mixedLocalMean hp L k f‖ₑ
      ≤ mixedWeight s k * (((∫⁻ t, ‖b.toFun t‖ₑ) * (2 ^ L + 1)) ^ d * lpMixedModulus p L f k) :=
        mul_le_mul' le_rfl (b.enorm_mixedLocalMean_le hp L hR k f)
    _ = ((∫⁻ t, ‖b.toFun t‖ₑ) * (2 ^ L + 1)) ^ d * (mixedWeight s k * lpMixedModulus p L f k) := by
        ring

/-! ### The reproducing formula -/

/-- **The reproducing identity of the kernels** in one variable:
`∑_{j ≤ J} η_j ⋆ k_j = m_{2^J} ⋆ m_{2^J}` at every point, from `(a + b) ⋆ (a - b) = a ⋆ a - b ⋆ b`
for the commuting kernels `a = m_{2^(j+1)}`, `b = m_{2^j}`. -/
theorem sum_conv_dual_kernel (L J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), conv (b.dual L j) (b.kernel L j) volume =
      conv (b.scaled L J) (b.scaled L J) volume := by
  induction J with
  | zero =>
    rw [Finset.sum_range_one]
    rfl
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    show conv (b.scaled L J) (b.scaled L J) volume +
        conv (b.scaled L (J + 1) + b.scaled L J) (b.scaled L (J + 1) - b.scaled L J) volume = _
    rw [conv_add_conv_sub (b.continuous_scaled L (J + 1)) (b.hasCompactSupport_scaled L (J + 1))
      (b.continuous_scaled L J) (b.hasCompactSupport_scaled L J)]
    abel

/-- **The mixed reproducing identity of the kernels**: over the boxes `{k : k_i ≤ J}`,
`∑_k η_k ⋆ k_k = (⊗(m ⋆ m))_{2^J}`. -/
theorem sum_conv_mixedDual_mixedKernel (L J : ℕ) :
    ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)),
        conv (b.mixedDual L k) (b.mixedKernel L k) volume =
      dilate ((2 : ℝ) ^ J)
        (tensorKernel fun _ : Fin d => conv (momentKernel b.toFun L) (momentKernel b.toFun L) volume) := by
  simp only [mixedDual, mixedKernel, conv_tensorKernel]
  rw [sum_tensorKernel_piFinset (fun _ => Finset.range (J + 1))
    (fun _ j => conv (b.dual L j) (b.kernel L j) volume), dilate_tensorKernel]
  congr 1
  funext i
  rw [b.sum_conv_dual_kernel L J, scaled, conv_dilate_dilate _ _ (by positivity)]

/-- The convolution `m ⋆ m` of the moment kernel has integral `1`. -/
theorem integral_conv_momentKernel {L : ℕ} (hL : 1 ≤ L) :
    ∫ t, conv (momentKernel b.toFun L) (momentKernel b.toFun L) volume t = 1 := by
  have hm := integrable_momentKernel b.integrable L
  have h1 := integral_momentKernel b.integrable b.integral_eq_one hL
  have h := integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume)
    hm hm
  simp only [ContinuousLinearMap.mul_apply', h1, mul_one] at h
  exact h

/-- **The mixed reproducing formula**: `∑_{k ≤ J} η_k ⋆ k_k ⋆ f → f` in `L_p` over the boxes
`{k : k_i ≤ J}`, since the partial sums are `(⊗(m ⋆ m))_{2^J} ⋆ f`, an approximate identity. -/
theorem tendsto_sum_mixedDual_mixedLocalMean (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    Tendsto (fun J => ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)),
      convLp hp (b.integrable_mixedDual L k) (b.mixedLocalMean hp L k f)) atTop (𝓝 f) := by
  set Φ : (Fin d → ℝ) → ℂ :=
    tensorKernel fun _ : Fin d => conv (momentKernel b.toFun L) (momentKernel b.toFun L) volume
  have hm := integrable_momentKernel b.integrable L
  have hΦ : Integrable Φ := integrable_tensorKernel fun _ => integrable_conv hm hm
  have hΦ1 : ∫ x, Φ x = 1 := by
    rw [integral_tensorKernel]
    simp [b.integral_conv_momentKernel hL]
  have hlim := tendsto_convLp_dilate hp hΦ hΦ1 (c := fun J : ℕ => (2 : ℝ) ^ J)
    (fun J => pow_ne_zero J two_ne_zero) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) f
  refine hlim.congr fun J => ?_
  symm
  simp only [mixedLocalMean]
  simp_rw [convLp_convLp hp (b.integrable_mixedDual L _) (b.integrable_mixedKernel L _)]
  rw [convLp_finsetSum_kernel]
  have hker : (fun a => ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)),
      conv (b.mixedDual L k) (b.mixedKernel L k) volume a) = dilate ((2 : ℝ) ^ J) Φ := by
    rw [← b.sum_conv_mixedDual_mixedKernel L J]
    funext a
    rw [Finset.sum_apply]
  exact convLp_congr hp _ _ hker f

/-! ### The mixed modulus is bounded by the local means -/

/-- **The mixed moduli of the reproducing terms**:
`Ω^{e(m)}_L(η_k ⋆ h, 2^(-m))_p ≤ C_η^d ∏_i c(m_i, k_i) ‖h‖_p`, by the differences of the
one-dimensional dual kernels in `L_1` (`Rd.LocalMeansBump.eLpNorm_iterDiff_dual_le`). -/
theorem lpMixedModulus_convLp_mixedDual_le (hp : p ≠ ∞) (L : ℕ) (m k : Fin d → ℕ)
    (h : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    lpMixedModulus p L (convLp hp (b.integrable_mixedDual L k) h) m ≤
      b.dualConst L ^ d * (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h‖ₑ := by
  have hp1 : 1 ≤ p := Fact.out
  refine iSup₂_le fun v hv => ?_
  set e := mixedSupp m
  have hae := (mixedDiff_congr_ae (convLp_apply_ae hp (b.integrable_mixedDual L k) h) L e v).trans
    (mixedDiff_conv_ae hp1 hp (b.integrable_mixedDual L k) (Lp.memLp h) L e v)
  rw [eLpNorm_congr_ae hae]
  have hfac : ∀ i, Integrable (if i ∈ e then (fwdDiff (v i))^[L] (b.dual L (k i))
      else b.dual L (k i)) := fun i => by
    split_ifs
    · exact integrable_iterDiff (b.integrable_dual L (k i)) L _
    · exact b.integrable_dual L (k i)
  refine (eLpNorm_conv_le hp1 hp
    (integrable_mixedDiff (b.integrable_mixedDual L k) L e v).aestronglyMeasurable
    (Lp.aestronglyMeasurable h)).trans ?_
  rw [Lp.enorm_def]
  refine mul_le_mul' ?_ le_rfl
  rw [mixedDual, mixedDiff_tensorKernel, eLpNorm_tensorKernel_one hfac,
    ← Fin.prod_const d (b.dualConst L), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod fun i _ => ?_
  by_cases hi : i ∈ e
  · simp only [hi, ↓reduceIte]
    have hvi : ‖v i‖ ≤ 1 / 2 ^ m i := by
      rw [Real.norm_eq_abs]
      exact hv i hi
    exact b.eLpNorm_iterDiff_dual_le L hvi
  · simp only [hi, ↓reduceIte]
    have hm0 : m i = 0 := by
      by_contra h0
      exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, h0⟩)
    have hc : almostDiagCoeff L (m i) (k i) = 1 := by
      rw [almostDiagCoeff, hm0]
      split_ifs with hk
      · rw [show k i = 0 by omega, Nat.sub_zero, ENNReal.dyadicWeight_zero_right]
      · rfl
    rw [hc, mul_one]
    refine (b.eLpNorm_dual_one_le L (k i)).trans ?_
    rw [dualConst]
    refine mul_le_mul' le_rfl ?_
    exact le_add_left (le_mul_of_one_le_left' (one_le_pow₀ one_le_two))

/-- **Synthesis with the mixed dual kernels**: if `F = ∑_k η_k ⋆ h_k` as the limit of the partial
sums over the boxes `{k : k_i ≤ J}`, then for `0 ≤ s`,
`‖(2^(s|m|_1) Ω^{e(m)}_L(F, 2^(-m))_p)_m‖_{ℓ_q} ≤ (C_η C)^d ‖(2^(s|k|_1) ‖h_k‖_p)_k‖_{ℓ_q}` with the
constant `C` of the almost diagonal lemma, finite for `0 < s < L`. -/
theorem mixedModNorm_le_of_tendsto (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {F : Lp ℂ p (volume : Measure (Fin d → ℝ))}
    {h : (Fin d → ℕ) → Lp ℂ p (volume : Measure (Fin d → ℝ))}
    (hrep : Tendsto (fun J => ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (J + 1)),
      convLp hp (b.integrable_mixedDual L k) (h k)) atTop (𝓝 F)) :
    mixedModNorm p L s q F ≤ (b.dualConst L * almostDiagConst s L) ^ d *
      mixedLqNorm q (fun k => mixedWeight s k * ‖h k‖ₑ) := by
  have hmod : ∀ m, lpMixedModulus p L F m ≤ b.dualConst L ^ d *
      ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h k‖ₑ := fun m => by
    have h1 : lpMixedModulus p L F m ≤
        ∑' k, lpMixedModulus p L (convLp hp (b.integrable_mixedDual L k) (h k)) m :=
      le_tsum_of_tendsto_finsetSum (C := 2 ^ (L * d)) (by simp)
        (fun x y => lpMixedModulus_add_le L x y m) (fun x => lpMixedModulus_le L x m) hrep
    refine h1.trans ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [← mul_assoc]
    exact b.lpMixedModulus_convLp_mixedDual_le hp L m k (h k)
  calc mixedModNorm p L s q F
      ≤ mixedLqNorm q (fun m => b.dualConst L ^ d * (mixedWeight s m *
          ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h k‖ₑ)) :=
        mixedLqNorm_mono fun m => by
          calc mixedWeight s m * lpMixedModulus p L F m
              ≤ mixedWeight s m * (b.dualConst L ^ d *
                  ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h k‖ₑ) :=
                mul_le_mul' le_rfl (hmod m)
            _ = _ := by ring
    _ = b.dualConst L ^ d * mixedLqNorm q (fun m => mixedWeight s m *
          ∑' k, (∏ i, almostDiagCoeff L (m i) (k i)) * ‖h k‖ₑ) := mixedLqNorm_const_mul _ _
    _ ≤ b.dualConst L ^ d * (almostDiagConst s L ^ d *
          mixedLqNorm q (fun k => mixedWeight s k * ‖h k‖ₑ)) :=
        mul_le_mul' le_rfl (mixedLqNorm_almostDiagonal_le hq hs _)
    _ = _ := by rw [mul_pow, mul_assoc]

/-- **The mixed modulus is bounded by the mixed local means**: for `0 ≤ s`,
`‖(2^(s|m|_1) Ω^{e(m)}_L(f, 2^(-m))_p)_m‖_{ℓ_q} ≤ (C_η C)^d ‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_k‖_{ℓ_q}`, by
the mixed reproducing formula and the synthesis. -/
theorem mixedModNorm_le_mixedLocalMeansNorm (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ}
    (hs : 0 ≤ s) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    mixedModNorm p L s q f ≤
      (b.dualConst L * almostDiagConst s L) ^ d * b.mixedLocalMeansNorm hp L s q f :=
  b.mixedModNorm_le_of_tendsto hp L hs hq (b.tendsto_sum_mixedDual_mixedLocalMean hp hL f)

/-- **Mixed local means and mixed differences** (T. Ullrich; Vybíral): for `1 ≤ p < ∞`,
`0 < s < L`, `1 ≤ q ≤ ∞` and a bump vanishing outside `[-1, 1]`,
`‖(2^(s|k|_1) Ω^{e(k)}_L(f, 2^(-k))_p)_k‖_{ℓ_q(ℕ^d)} < ∞` iff
`‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_k‖_{ℓ_q(ℕ^d)} < ∞`, with equivalent quasi-norms. -/
theorem mixedBesov_iff_mixedLocalMeans (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) (hR : b.radius ≤ 1)
    {s : ℝ} (hs : 0 < s) (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    mixedModNorm p L s q f < ∞ ↔ b.mixedLocalMeansNorm hp L s q f < ∞ := by
  constructor
  · intro h
    refine (b.mixedLocalMeansNorm_le hp L hR s q f).trans_lt (ENNReal.mul_lt_top ?_ h)
    exact ENNReal.pow_lt_top (ENNReal.mul_lt_top b.integrable.2
      (ENNReal.add_lt_top.2 ⟨ENNReal.pow_lt_top (by simp), ENNReal.one_lt_top⟩))
  · intro h
    refine (b.mixedModNorm_le_mixedLocalMeansNorm hp hL hs.le hq f).trans_lt
      (ENNReal.mul_lt_top ?_ h)
    exact ENNReal.pow_lt_top (ENNReal.mul_lt_top (b.dualConst_ne_top L).lt_top
      (almostDiagConst_ne_top hs hsL).lt_top)

end LocalMeansBump

end Rd
