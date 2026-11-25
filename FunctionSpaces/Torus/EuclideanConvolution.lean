/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.Modulus
public import FunctionSpaces.Torus.Nikolskii
public import FunctionSpaces.Analysis.Lp.Young
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Convolution on the torus with kernels on `ℝ^d`

The quotient map `π : ℝ^d → 𝕋^d`, `π x = (x_i mod 1)_i` (`Torus.quotientProj`), lets an integrable
kernel `Φ` on `ℝ^d` act on functions on the torus by

`(Φ ⋆ f)(t) = ∫_{ℝ^d} Φ(y) f(t - π y) dy`   (`Torus.periodicEconv`),

the convolution of `f` with the periodisation `∑_{m ∈ ℤ^d} Φ(· + m)` of `Φ`, without forming it.

* **Young's inequality** `‖Φ ⋆ f‖_{L_p(𝕋)} ≤ ‖Φ‖_{L_1(ℝ^d)} ‖f‖_p`
  (`Torus.eLpNorm_periodicEconv_le`), from the weighted averages of
  `MeasureTheory.eLpNorm_integral_kernel_le_of_bound` and the invariance of the Haar measure of the
  torus; so `Φ ⋆ ·` is a bounded operator on `L_p(𝕋)` (`Torus.periodicEconvLp`). The convolution is
  linear (`Torus.periodicEconv_add_ae`, `Torus.periodicEconv_smul`), and a finite sum of
  convolutions in `L_p` is represented by the pointwise sum (`Torus.coeFn_sum_periodicEconvLp_ae`).
* **Fourier multipliers**: `Φ ⋆ e_m = 𝓕Φ(m) e_m` (`Torus.periodicEconv_mFourier`), since
  `e_m(-π y) = e^(-2πi⟨m, y⟩)`. If `𝓕Φ(m) = 0` for `deg m ≥ n`, the operator maps `L_p(𝕋)` into
  the trigonometric polynomials of degree `< n` (`Torus.periodicEconvLp_mem_trigPolyLp`): it maps
  the dense span of the `e_m` into this finite-dimensional, hence closed, subspace. If `𝓕Φ(m) = 1`
  for `deg m < n`, it reproduces them (`Torus.periodicEconvLp_eq_self_of_mem`).
* **Differences**: `Δ^r_{π h} (Φ ⋆ f) = (Δ^r_h Φ) ⋆ f` almost everywhere
  (`Torus.higherDiff_periodicEconv_ae`), by the translation invariance of the Lebesgue measure.
* **Bounded continuous functions**: `f ↦ Φ ⋆ f` is a bounded operator on the bounded continuous
  functions, `‖Φ ⋆ f‖_∞ ≤ ‖Φ‖_1 ‖f‖_∞` (`Torus.periodicEconvBCF`), and the class of `Φ ⋆ f` in `L_p`
  is `Torus.periodicEconvLp` of the class of `f` (`Torus.toLp_periodicEconvBCF`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter
open scoped ENNReal FourierTransform TorusHaar Real

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### The quotient map -/

/-- The **quotient map** `π : ℝ^d → 𝕋^d`, `π x = (x_i mod 1)_i`. -/
noncomputable def quotientProj : EuclideanSpace ℝ d →+ UnitAddTorus d where
  toFun x i := ((x i : ℝ) : UnitAddCircle)
  map_zero' := funext fun i => by simp
  map_add' x y := funext fun i => by simp

omit [Fintype d] in
/-- `(π x)_i = x_i mod 1`. -/
theorem quotientProj_apply (x : EuclideanSpace ℝ d) (i : d) :
    quotientProj x i = ((x i : ℝ) : UnitAddCircle) := rfl

omit [Fintype d] in
/-- The quotient map is continuous. -/
theorem continuous_quotientProj : Continuous (quotientProj : EuclideanSpace ℝ d → UnitAddTorus d) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (PiLp.continuous_apply 2 _ i)

/-- The quotient map is measurable. -/
theorem measurable_quotientProj : Measurable (quotientProj : EuclideanSpace ℝ d → UnitAddTorus d) :=
  continuous_quotientProj.measurable

/-- `‖π x‖ ≤ ‖x‖` for the sup norm of the torus. -/
theorem norm_quotientProj_le (x : EuclideanSpace ℝ d) : ‖quotientProj x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i =>
    (norm_coe_le_abs (x i)).trans (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le x i)

/-- **A norm bound by the coordinates**: `‖x‖ ≤ #d · M` if `|x_i| ≤ M` for every `i`. -/
theorem norm_le_card_mul {x : EuclideanSpace ℝ d} {M : ℝ} (hx : ∀ i, |x i| ≤ M) :
    ‖x‖ ≤ Fintype.card d * M := by
  rcases isEmpty_or_nonempty d with hd | ⟨⟨i₀⟩⟩
  · rw [Subsingleton.elim x 0, norm_zero, Fintype.card_eq_zero, Nat.cast_zero, zero_mul]
  · have hM : 0 ≤ M := (abs_nonneg _).trans (hx i₀)
    have hcard : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast Fintype.card_pos_iff.2 ⟨i₀⟩
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : d, M ^ 2 := Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hx i) 2
      _ = Fintype.card d * M ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card d * M) ^ 2 := by nlinarith [sq_nonneg M]

/-- **Every point of the torus is `π x` with `‖x‖ ≤ #d ‖h‖`**: choose representatives
`|x_i| = ‖h_i‖` (`Torus.exists_coe_eq_abs_eq_norm`). -/
theorem exists_quotientProj_eq (h : UnitAddTorus d) :
    ∃ x : EuclideanSpace ℝ d, quotientProj x = h ∧ ‖x‖ ≤ Fintype.card d * ‖h‖ := by
  choose x hx1 hx2 using fun i => exists_coe_eq_abs_eq_norm (h i)
  refine ⟨WithLp.toLp 2 x, funext fun i => hx1 i, norm_le_card_mul fun i => ?_⟩
  rw [show (WithLp.toLp 2 x : EuclideanSpace ℝ d) i = x i from rfl, hx2]
  exact norm_le_pi_norm h i

/-! ### Lattice points and characters -/

/-- The **lattice point** `(m_i)_i ∈ ℝ^d` of `m ∈ ℤ^d`. -/
noncomputable def latticeVec (m : d → ℤ) : EuclideanSpace ℝ d := WithLp.toLp 2 fun i => (m i : ℝ)

omit [Fintype d] in
/-- `(latticeVec m)_i = m_i`. -/
theorem latticeVec_apply (m : d → ℤ) (i : d) : latticeVec m i = (m i : ℝ) := rfl

omit [Fintype d] in
/-- The lattice vector of `-m` is `-m`. -/
theorem latticeVec_neg (m : d → ℤ) : latticeVec (-m) = -latticeVec m := by
  ext i
  simp [latticeVec_apply]

/-- `⟪m, v⟫ = ∑_i m_i v_i` in coordinates. -/
theorem inner_latticeVec (m : d → ℤ) (v : EuclideanSpace ℝ d) :
    inner ℝ (latticeVec m) v = ∑ i, (m i : ℝ) * v i := by
  simp only [PiLp.inner_apply, latticeVec_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `⟪m, e_i⟫ = m_i` for the unit vector `e_i`. -/
theorem inner_latticeVec_single [DecidableEq d] (m : d → ℤ) (i : d) :
    inner ℝ (latticeVec m) (EuclideanSpace.single i (1 : ℝ)) = (m i : ℝ) := by
  rw [EuclideanSpace.inner_single_right, latticeVec_apply, one_mul]
  rfl

/-- **The degree is at most the norm**: `max_i |m_i| ≤ ‖m‖`. -/
theorem trigDeg_le_norm_latticeVec (m : d → ℤ) : (trigDeg m : ℝ) ≤ ‖latticeVec m‖ := by
  have hi : ∀ i, ((m i).natAbs : ℝ) ≤ ‖latticeVec m‖ := fun i => by
    have h := PiLp.norm_apply_le (latticeVec m) i
    rwa [latticeVec_apply, Real.norm_eq_abs, ← Int.cast_abs, ← Nat.cast_natAbs] at h
  have h : trigDeg m ≤ ⌊‖latticeVec m‖⌋₊ := trigDeg_le_iff.2 fun i => Nat.le_floor (hi i)
  exact (Nat.cast_le.2 h).trans (Nat.floor_le (norm_nonneg _))

/-- **The norm is at most `#d` times the degree**. -/
theorem norm_latticeVec_le (m : d → ℤ) : ‖latticeVec m‖ ≤ Fintype.card d * trigDeg m :=
  norm_le_card_mul fun i => by
    rw [latticeVec_apply, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact Nat.cast_le.2 (natAbs_le_trigDeg m i)

/-- **The characters along the quotient map**: `e_m(-π y) = e^(-2πi⟨y, m⟩)`. -/
theorem mFourier_neg_quotientProj (m : d → ℤ) (y : EuclideanSpace ℝ d) :
    mFourier m (-quotientProj y) =
      Complex.exp (↑(-2 * π * inner ℝ y (latticeVec m)) * Complex.I) := by
  rw [← map_neg]
  have h : ∀ i, fourier (m i) (quotientProj (-y) i) =
      Complex.exp (↑(-2 * π * (y i * m i)) * Complex.I) := fun i => by
    rw [quotientProj_apply, fourier_coe_apply, PiLp.neg_apply]
    congr 1
    push_cast
    ring
  show ∏ i, fourier (m i) (quotientProj (-y) i) = _
  simp only [h]
  rw [← Complex.exp_sum]
  congr 1
  rw [PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial, latticeVec_apply]
  push_cast
  ring

/-- **The Fourier transform at the lattice points**: `∫ Φ(y) e_m(-π y) dy = 𝓕Φ(m)`. -/
theorem integral_mul_mFourier_neg_quotientProj (Φ : EuclideanSpace ℝ d → ℂ) (m : d → ℤ) :
    ∫ y, Φ y * mFourier m (-quotientProj y) = 𝓕 Φ (latticeVec m) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mFourier_neg_quotientProj, smul_eq_mul]
  ring

/-! ### Convolution with a kernel on `ℝ^d` -/

/-- The **convolution with a kernel on `ℝ^d`**: `(Φ ⋆ f)(t) = ∫ Φ(y) f(t - π y) dy` for a function
`f` on the torus. -/
noncomputable def periodicEconv (Φ : EuclideanSpace ℝ d → ℂ) (f : UnitAddTorus d → ℂ)
    (t : UnitAddTorus d) : ℂ :=
  ∫ y, Φ y * f (t - quotientProj y)

/-- The integrand `(t, y) ↦ f(t - π y)` is measurable. -/
theorem measurable_comp_sub_quotientProj {f : UnitAddTorus d → ℂ} (hf : Measurable f) :
    Measurable (Function.uncurry fun (t : UnitAddTorus d) (y : EuclideanSpace ℝ d) =>
      f (t - quotientProj y)) :=
  hf.comp (measurable_fst.sub (measurable_quotientProj.comp measurable_snd))

/-- Translations keep `L_p` norms on the torus. -/
theorem eLpNorm_comp_sub {f : UnitAddTorus d → ℂ} (hf : AEStronglyMeasurable f volume)
    (p : ℝ≥0∞) (c : UnitAddTorus d) :
    eLpNorm (fun t => f (t - c)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_sub_right volume c)

/-- The convolution is measurable. -/
theorem aestronglyMeasurable_periodicEconv {Φ : EuclideanSpace ℝ d → ℂ}
    (hΦ : AEStronglyMeasurable Φ volume) {f : UnitAddTorus d → ℂ} (hf : Measurable f) :
    AEStronglyMeasurable (periodicEconv Φ f) volume :=
  (hΦ.comp_snd.mul (measurable_comp_sub_quotientProj hf).aestronglyMeasurable).integral_prod_right'

/-- **Young's inequality on the torus**: `‖Φ ⋆ f‖_{L_p(𝕋)} ≤ ‖Φ‖_{L_1(ℝ^d)} ‖f‖_p`, `1 ≤ p < ∞`,
since every translate `f(· - π y)` has the norm of `f`. -/
theorem eLpNorm_periodicEconv_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ}
    (hΦ : Integrable Φ) {f : UnitAddTorus d → ℂ} (hf : Measurable f) :
    eLpNorm (periodicEconv Φ f) p volume ≤ (∫⁻ y, ‖Φ y‖ₑ) * eLpNorm f p volume := by
  by_cases h0 : ∫⁻ y, ‖Φ y‖ₑ = 0
  · have he : periodicEconv Φ f = 0 := funext fun t => integral_eq_zero_of_ae <| by
      filter_upwards [(lintegral_eq_zero_iff' hΦ.aestronglyMeasurable.enorm).1 h0] with y hy
      simp [enorm_eq_zero.1 hy]
    simp [he]
  · exact eLpNorm_integral_kernel_le_of_bound hp1 hp hΦ.aestronglyMeasurable h0 hΦ.2.ne
      (measurable_comp_sub_quotientProj hf) fun z _ =>
        (eLpNorm_comp_sub hf.aestronglyMeasurable p (quotientProj z)).le

/-- The convolution of `f ∈ L_p(𝕋)` with an integrable kernel is in `L_p(𝕋)`. -/
theorem memLp_periodicEconv {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ}
    (hΦ : Integrable Φ) {f : UnitAddTorus d → ℂ} (hf : Measurable f)
    (hfp : MemLp f p volume) : MemLp (periodicEconv Φ f) p volume :=
  (eLpNorm_periodicEconv_le hp1 hp hΦ hf).trans_lt (ENNReal.mul_lt_top hΦ.2 hfp)

/-- **The convolution integral converges absolutely almost everywhere** for `f ∈ L_1(𝕋)`:
`∫∫ |Φ(y)| |f(t - π y)| dy dt = ‖Φ‖_1 ‖f‖_1` by Tonelli's theorem. -/
theorem ae_integrable_econv {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {f : UnitAddTorus d → ℂ} (hf : Measurable f) (hfi : Integrable f volume) :
    ∀ᵐ t ∂volume, Integrable (fun y => Φ y * f (t - quotientProj y)) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (t : UnitAddTorus d)
      (y : EuclideanSpace ℝ d) => Φ y * f (t - quotientProj y)) (volume.prod volume) :=
    hΦ.aestronglyMeasurable.comp_snd.mul (measurable_comp_sub_quotientProj hf).aestronglyMeasurable
  have hF : Integrable (Function.uncurry fun (t : UnitAddTorus d) (y : EuclideanSpace ℝ d) =>
      Φ y * f (t - quotientProj y)) (volume.prod volume) := by
    refine ⟨hmeas, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.enorm]
    have hin : ∀ y, ∫⁻ t, ‖Function.uncurry (fun (t : UnitAddTorus d)
        (y : EuclideanSpace ℝ d) => Φ y * f (t - quotientProj y)) (t, y)‖ₑ =
          ‖Φ y‖ₑ * ∫⁻ t, ‖f t‖ₑ := fun y => by
      simp only [Function.uncurry_apply_pair, enorm_mul]
      rw [lintegral_const_mul' _ _ enorm_ne_top,
        lintegral_sub_right_eq_self (fun t => ‖f t‖ₑ) (quotientProj y)]
    simp_rw [hin]
    rw [lintegral_mul_const'' _ hΦ.aestronglyMeasurable.enorm]
    exact ENNReal.mul_lt_top hΦ.2 hfi.2
  exact hF.prod_right_ae

/-- **The convolution sees only classes**: `f = g` almost everywhere gives `Φ ⋆ f = Φ ⋆ g`
almost everywhere, since `f(t - π y) = g(t - π y)` for almost every `(t, y)`. -/
theorem periodicEconv_congr_ae (Φ : EuclideanSpace ℝ d → ℂ) {f g : UnitAddTorus d → ℂ}
    (hf : Measurable f) (hg : Measurable g) (hfg : f =ᵐ[volume] g) :
    periodicEconv Φ f =ᵐ[volume] periodicEconv Φ g := by
  have hset : MeasurableSet {z : UnitAddTorus d × EuclideanSpace ℝ d |
      f (z.1 - quotientProj z.2) = g (z.1 - quotientProj z.2)} :=
    measurableSet_eq_fun (measurable_comp_sub_quotientProj hf) (measurable_comp_sub_quotientProj hg)
  have h : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ d)), ∀ᵐ t ∂volume,
      f (t - quotientProj y) = g (t - quotientProj y) := Eventually.of_forall fun y =>
    (measurePreserving_sub_right volume (quotientProj y)).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [(Measure.ae_ae_comm hset).2 h] with t ht
  exact integral_congr_ae (ht.mono fun y hy => congrArg (Φ y * ·) hy)

/-- **The convolution is additive almost everywhere** for integrable `f, g` on the torus:
`Φ ⋆ (f + g) = Φ ⋆ f + Φ ⋆ g` almost everywhere, where both integrals converge absolutely
(`Torus.ae_integrable_econv`). -/
theorem periodicEconv_add_ae {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {f g : UnitAddTorus d → ℂ} (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f volume)
    (hgi : Integrable g volume) :
    periodicEconv Φ (f + g) =ᵐ[volume] periodicEconv Φ f + periodicEconv Φ g := by
  filter_upwards [ae_integrable_econv hΦ hf hfi, ae_integrable_econv hΦ hg hgi] with t h1 h2
  simp only [periodicEconv, Pi.add_apply, mul_add]
  exact integral_add h1 h2

/-- **The convolution is homogeneous**: `Φ ⋆ (c f) = c (Φ ⋆ f)` at every point, for every
`c ∈ ℂ`. -/
theorem periodicEconv_smul (Φ : EuclideanSpace ℝ d → ℂ) (c : ℂ) (f : UnitAddTorus d → ℂ) :
    periodicEconv Φ (c • f) = c • periodicEconv Φ f := funext fun t => by
  simp only [periodicEconv, Pi.smul_apply, smul_eq_mul, mul_left_comm (Φ _) c, integral_const_mul]

/-! ### The operator on `L_p` -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Convolution with an integrable kernel on `ℝ^d` as a bounded operator on `L_p(𝕋)`**,
`1 ≤ p < ∞`, of norm at most `‖Φ‖_1`. -/
noncomputable def periodicEconvLp (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_periodicEconv Fact.out hp hΦ (Lp.stronglyMeasurable f).measurable
        (Lp.memLp f)).toLp (periodicEconv Φ f)
      map_add' := fun f g => by
        refine Lp.ext ?_
        have hfm := (Lp.stronglyMeasurable f).measurable
        have hgm := (Lp.stronglyMeasurable g).measurable
        filter_upwards [MemLp.coeFn_toLp (memLp_periodicEconv Fact.out hp hΦ
            (Lp.stronglyMeasurable (f + g)).measurable (Lp.memLp (f + g))),
          MemLp.coeFn_toLp (memLp_periodicEconv Fact.out hp hΦ hfm (Lp.memLp f)),
          MemLp.coeFn_toLp (memLp_periodicEconv Fact.out hp hΦ hgm (Lp.memLp g)),
          Lp.coeFn_add
            ((memLp_periodicEconv Fact.out hp hΦ hfm (Lp.memLp f)).toLp (periodicEconv Φ f))
            ((memLp_periodicEconv Fact.out hp hΦ hgm (Lp.memLp g)).toLp (periodicEconv Φ g)),
          periodicEconv_congr_ae Φ (Lp.stronglyMeasurable (f + g)).measurable (hfm.add hgm)
            (Lp.coeFn_add f g),
          periodicEconv_add_ae hΦ hfm hgm ((Lp.memLp f).integrable Fact.out)
            ((Lp.memLp g).integrable Fact.out)] with t h1 h2 h3 h4 h5 h6
        rw [h1, h4, Pi.add_apply, h2, h3, h5, h6, Pi.add_apply]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have hfm := (Lp.stronglyMeasurable f).measurable
        filter_upwards [MemLp.coeFn_toLp (memLp_periodicEconv Fact.out hp hΦ
            (Lp.stronglyMeasurable (c • f)).measurable (Lp.memLp (c • f))),
          MemLp.coeFn_toLp (memLp_periodicEconv Fact.out hp hΦ hfm (Lp.memLp f)),
          Lp.coeFn_smul c
            ((memLp_periodicEconv Fact.out hp hΦ hfm (Lp.memLp f)).toLp (periodicEconv Φ f)),
          periodicEconv_congr_ae Φ (Lp.stronglyMeasurable (c • f)).measurable (hfm.const_smul c)
            (Lp.coeFn_smul c f)] with t h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, periodicEconv_smul, Pi.smul_apply] }
    (∫⁻ y, ‖Φ y‖ₑ).toReal (fun f => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hΦ.2.ne (Lp.eLpNorm_ne_top f))
        (eLpNorm_periodicEconv_le Fact.out hp hΦ (Lp.stronglyMeasurable f).measurable))

/-- The operator `periodicEconvLp` is the convolution, almost everywhere. -/
theorem periodicEconvLp_apply_ae (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicEconvLp hp hΦ f =ᵐ[volume] periodicEconv Φ f :=
  MemLp.coeFn_toLp
    (memLp_periodicEconv Fact.out hp hΦ (Lp.stronglyMeasurable f).measurable (Lp.memLp f))

/-- **Sums of convolutions are pointwise sums**: for integrable kernels `K_j` on `ℝ^d`,
`u_j ∈ L_p(𝕋^d)` and every finite set `s`, the class `∑_{j ∈ s} K_j ⋆ u_j` is represented by
`t ↦ ∑_{j ∈ s} (K_j ⋆ u_j)(t)` (`Torus.periodicEconvLp_apply_ae`, Mathlib's
`Lp.coeFn_fun_finsetSum`). -/
theorem coeFn_sum_periodicEconvLp_ae (hp : p ≠ ∞) {ι : Type*} (s : Finset ι)
    {K : ι → EuclideanSpace ℝ d → ℂ} (hK : ∀ j, Integrable (K j))
    (u : ι → Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ⇑(∑ j ∈ s, periodicEconvLp hp (hK j) (u j)) =ᵐ[volume]
      fun t => ∑ j ∈ s, periodicEconv (K j) (u j) t := by
  filter_upwards [Lp.coeFn_fun_finsetSum s fun j => periodicEconvLp hp (hK j) (u j),
    (eventually_all_finset s).2 fun j _ => periodicEconvLp_apply_ae hp (hK j) (u j)] with t h1 h2
  rw [h1]
  exact Finset.sum_congr rfl h2

/-- **Young's inequality on `L_p(𝕋)`** in extended norms: `‖Φ ⋆ f‖_p ≤ ‖Φ‖_1 ‖f‖_p`. -/
theorem enorm_periodicEconvLp_le (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖periodicEconvLp hp hΦ f‖ₑ ≤ (∫⁻ y, ‖Φ y‖ₑ) * ‖f‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (periodicEconvLp_apply_ae hp hΦ f)]
  exact eLpNorm_periodicEconv_le Fact.out hp hΦ (Lp.stronglyMeasurable f).measurable

/-! ### Fourier multipliers -/

/-- **The characters are eigenfunctions**: `Φ ⋆ e_m = 𝓕Φ(m) e_m`. -/
theorem periodicEconv_mFourier (Φ : EuclideanSpace ℝ d → ℂ) (m : d → ℤ) (t : UnitAddTorus d) :
    periodicEconv Φ (mFourier m) t = 𝓕 Φ (latticeVec m) * mFourier m t := by
  simp only [periodicEconv, sub_eq_add_neg, mFourier_add_apply]
  rw [← integral_mul_mFourier_neg_quotientProj, ← integral_mul_const]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

/-- **The characters are eigenfunctions in `L_p`**: `Φ ⋆ e_m = 𝓕Φ(m) e_m`. -/
theorem periodicEconvLp_mFourierLp (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (m : d → ℤ) : periodicEconvLp hp hΦ (mFourierLp p m) = 𝓕 Φ (latticeVec m) • mFourierLp p m := by
  refine Lp.ext ?_
  have hm := coeFn_mFourierLp (d := d) p m
  filter_upwards [periodicEconvLp_apply_ae hp hΦ (mFourierLp p m),
    periodicEconv_congr_ae Φ (Lp.stronglyMeasurable (mFourierLp p m)).measurable
      (mFourier m).continuous.measurable hm,
    Lp.coeFn_smul (𝓕 Φ (latticeVec m)) (mFourierLp p m), hm] with t h1 h2 h3 h4
  rw [h1, h2, periodicEconv_mFourier, h3, Pi.smul_apply, h4, smul_eq_mul]

variable (p) in
/-- The **trigonometric polynomials of degree `< n` in `L_p(𝕋)`**. -/
noncomputable def trigPolyLp (n : ℕ) : Submodule ℂ (Lp ℂ p (volume : Measure (UnitAddTorus d))) :=
  (trigPoly d n).map (BoundedContinuousFunction.toLp (E := ℂ) p volume ℂ).toLinearMap

/-- The trigonometric polynomials of degree `< n` in `L_p(𝕋)` are spanned by the characters
`e_m`, `deg m < n`. -/
theorem trigPolyLp_eq_span (n : ℕ) :
    trigPolyLp (d := d) p n = Submodule.span ℂ (mFourierLp p '' (boxLt d n : Set (d → ℤ))) := by
  rw [trigPolyLp, trigPoly, Submodule.map_span, ← Set.image_comp]
  rfl

/-- `e_m` is a trigonometric polynomial of degree `< n` for `deg m < n`. -/
theorem mFourierLp_mem_trigPolyLp {n : ℕ} {m : d → ℤ} (hm : trigDeg m < n) :
    mFourierLp p m ∈ trigPolyLp p n := by
  rw [trigPolyLp_eq_span]
  exact Submodule.subset_span ⟨m, mem_boxLt.2 hm, rfl⟩

/-- The trigonometric polynomials of degree `< n` form a closed subspace of `L_p(𝕋)`, being
finite-dimensional. -/
theorem isClosed_trigPolyLp (n : ℕ) :
    IsClosed (↑(trigPolyLp (d := d) p n) : Set (Lp ℂ p (volume : Measure (UnitAddTorus d)))) := by
  have : FiniteDimensional ℂ (trigPolyLp (d := d) p n) := by
    rw [trigPolyLp_eq_span]
    exact FiniteDimensional.span_of_finite ℂ ((boxLt d n).finite_toSet.image _)
  exact Submodule.closed_of_finiteDimensional _

/-- **The trigonometric polynomials of the scheme in `L_p`**: the approximants of degree `< n`
of `(trigScheme d).toLp p` are the trigonometric polynomials of degree `< n` in `L_p`. -/
theorem mem_toLp_trigScheme_iff {n : ℕ} {g : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    g ∈ (trigScheme d).toLp p n ↔ g ∈ trigPolyLp p n := by
  rw [trigScheme, FunctionScheme.mem_toLp_ofContinuous, trigPolyLp, Submodule.mem_map]
  simp only [mem_uniformTrigScheme]
  rfl

/-- **Band-limited kernels map `L_p(𝕋)` into trigonometric polynomials**: if `𝓕Φ(m) = 0` for
`deg m ≥ n`, then `Φ ⋆ f` has degree `< n`. The operator maps every `e_m` into the closed subspace
of trigonometric polynomials of degree `< n`, and the `e_m` span a dense subspace (Mathlib's
`span_mFourierLp_closure_eq_top`). -/
theorem periodicEconvLp_mem_trigPolyLp (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {n : ℕ} (hF : ∀ m : d → ℤ, n ≤ trigDeg m → 𝓕 Φ (latticeVec m) = 0)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicEconvLp hp hΦ f ∈ trigPolyLp p n := by
  set S := (trigPolyLp (d := d) p n).comap (periodicEconvLp hp hΦ).toLinearMap
  have hS : IsClosed (S : Set (Lp ℂ p (volume : Measure (UnitAddTorus d)))) :=
    (isClosed_trigPolyLp n).preimage (periodicEconvLp hp hΦ).continuous
  have hspan : Submodule.span ℂ (Set.range (mFourierLp (d := d) p)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    show periodicEconvLp hp hΦ (mFourierLp p m) ∈ trigPolyLp p n
    rw [periodicEconvLp_mFourierLp]
    by_cases hm : n ≤ trigDeg m
    · rw [hF m hm, zero_smul]
      exact zero_mem _
    · exact Submodule.smul_mem _ _ (mFourierLp_mem_trigPolyLp (not_le.1 hm))
  have hcl := Submodule.topologicalClosure_minimal _ hspan hS
  rw [span_mFourierLp_closure_eq_top hp] at hcl
  exact hcl Submodule.mem_top

/-- **Kernels with `𝓕Φ = 1` on the low frequencies reproduce trigonometric polynomials**: if
`𝓕Φ(m) = 1` for `deg m < n`, then `Φ ⋆ a = a` for every trigonometric polynomial `a` of degree
`< n`. -/
theorem periodicEconvLp_eq_self_of_mem (hp : p ≠ ∞) {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {n : ℕ} (hF : ∀ m : d → ℤ, trigDeg m < n → 𝓕 Φ (latticeVec m) = 1)
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p n) :
    periodicEconvLp hp hΦ a = a := by
  rw [trigPolyLp_eq_span] at ha
  refine LinearMap.eqOn_span (f := (periodicEconvLp hp hΦ).toLinearMap) (g := LinearMap.id) ?_ ha
  rintro _ ⟨m, hm, rfl⟩
  simp [periodicEconvLp_mFourierLp, hF m (mem_boxLt.1 hm)]

/-! ### Translations and differences -/

/-- **Translation**: `(Φ ⋆ f)(t + π h) = (Φ(· + h) ⋆ f)(t)`, by the translation invariance of the
Lebesgue measure. -/
theorem periodicEconv_add_quotientProj (Φ : EuclideanSpace ℝ d → ℂ) (f : UnitAddTorus d → ℂ)
    (t : UnitAddTorus d) (h : EuclideanSpace ℝ d) :
    periodicEconv Φ f (t + quotientProj h) = periodicEconv (fun y => Φ (y + h)) f t := by
  simp only [periodicEconv]
  rw [← integral_add_right_eq_self (fun y => Φ y * f (t + quotientProj h - quotientProj y)) h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_add]
  congr 2
  abel

/-- **Differences of the convolution**: `Δ^r_{π h} (Φ ⋆ f) = (Δ^r_h Φ) ⋆ f` almost everywhere,
for integrable `Φ` and `f ∈ L_1(𝕋)`. -/
theorem higherDiff_periodicEconv_ae {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {f : UnitAddTorus d → ℂ} (hf : Measurable f) (hfi : Integrable f volume) (r : ℕ)
    (h : EuclideanSpace ℝ d) :
    (fwdDiff (quotientProj h))^[r] (periodicEconv Φ f) =ᵐ[volume]
      periodicEconv ((fwdDiff h)^[r] Φ) f := by
  have hint : ∀ᵐ t ∂volume, ∀ l ∈ Finset.range (r + 1),
      Integrable (fun y => Φ (y + l • h) * f (t - quotientProj y)) :=
    (eventually_all_finset _).2 fun l _ => ae_integrable_econv (hΦ.comp_add_right (l • h)) hf hfi
  filter_upwards [hint] with t ht
  have hL : ∀ l : ℕ, periodicEconv Φ f (t + l • quotientProj h) =
      ∫ y, Φ (y + l • h) * f (t - quotientProj y) :=
    fun l => by rw [← map_nsmul, periodicEconv_add_quotientProj]; rfl
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [hL, zsmul_eq_mul]
  rw [periodicEconv]
  simp only [fwdDiff_iter_eq_sum_shift, zsmul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum _ fun l hl => by simpa only [mul_assoc] using (ht l hl).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

section BoundedContinuous

open scoped BoundedContinuousFunction

/-! ### Convolution of bounded continuous functions -/

/-- The integrand `y ↦ Φ(y) f(t - π y)` of the convolution of a bounded continuous `f` with an
integrable kernel is integrable. -/
theorem integrable_mul_comp_sub_quotientProj {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : UnitAddTorus d →ᵇ ℂ) (t : UnitAddTorus d) :
    Integrable fun y => Φ y * f (t - quotientProj y) :=
  hΦ.mul_bdd (f.continuous.comp (continuous_const.sub continuous_quotientProj)).aestronglyMeasurable
    (Eventually.of_forall fun _ => f.norm_coe_le_norm _)

/-- **The convolution of a continuous function is continuous**: for integrable `Φ` on `ℝ^d` and
bounded continuous `f` on `𝕋^d`, `Φ ⋆ f` is continuous, by dominated convergence with the bound
`|Φ(y)| ‖f‖_∞`. -/
theorem continuous_periodicEconv {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : UnitAddTorus d →ᵇ ℂ) : Continuous (periodicEconv Φ f) := by
  show Continuous fun t => ∫ y, Φ y * f (t - quotientProj y)
  refine continuous_of_dominated (bound := fun y => ‖Φ y‖ * ‖f‖)
    (fun t => (integrable_mul_comp_sub_quotientProj hΦ f t).aestronglyMeasurable)
    (fun t => Eventually.of_forall fun y => ?_) (hΦ.norm.mul_const _)
    (Eventually.of_forall fun y => ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)
  · exact continuous_const.mul (f.continuous.comp (continuous_id.sub continuous_const))

/-- **The convolution is bounded pointwise**: `|(Φ ⋆ f)(t)| ≤ ‖Φ‖_1 ‖f‖_∞` for every `t`. -/
theorem norm_periodicEconv_le {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : UnitAddTorus d →ᵇ ℂ) (t : UnitAddTorus d) :
    ‖periodicEconv Φ f t‖ ≤ (∫ y, ‖Φ y‖) * ‖f‖ := by
  rw [periodicEconv, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hΦ.norm.mul_const _) (Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)

/-- The **convolution of bounded continuous functions** with an integrable kernel `Φ` on `ℝ^d`,
`(Φ ⋆ f)(t) = ∫ Φ(y) f(t - π y) dy`, as a bounded linear operator on the bounded continuous
functions on `𝕋^d`, of norm at most `‖Φ‖_1`. -/
noncomputable def periodicEconvBCF {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ) :
    (UnitAddTorus d →ᵇ ℂ) →L[ℂ] (UnitAddTorus d →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f =>
      BoundedContinuousFunction.mkOfCompact ⟨periodicEconv Φ f, continuous_periodicEconv hΦ f⟩
      map_add' := fun f g => by
        ext t
        show periodicEconv Φ ⇑(f + g) t = periodicEconv Φ f t + periodicEconv Φ g t
        simp only [periodicEconv, BoundedContinuousFunction.coe_add, Pi.add_apply, mul_add]
        exact integral_add (integrable_mul_comp_sub_quotientProj hΦ f t)
          (integrable_mul_comp_sub_quotientProj hΦ g t)
      map_smul' := fun c f => by
        ext t
        show periodicEconv Φ (c • ⇑f) t = c * periodicEconv Φ f t
        rw [periodicEconv_smul, Pi.smul_apply, smul_eq_mul] }
    (∫ y, ‖Φ y‖) fun f => (BoundedContinuousFunction.norm_le
      (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))).2
        fun t => norm_periodicEconv_le hΦ f t

/-- The values of `periodicEconvBCF` are the convolution integrals. -/
@[simp]
theorem periodicEconvBCF_apply {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : UnitAddTorus d →ᵇ ℂ) (t : UnitAddTorus d) :
    periodicEconvBCF hΦ f t = periodicEconv Φ f t := rfl

/-- **Young's inequality in the sup norm**: `‖Φ ⋆ f‖_∞ ≤ ‖Φ‖_1 ‖f‖_∞`. -/
theorem norm_periodicEconvBCF_le {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    (f : UnitAddTorus d →ᵇ ℂ) : ‖periodicEconvBCF hΦ f‖ ≤ (∫ y, ‖Φ y‖) * ‖f‖ :=
  (BoundedContinuousFunction.norm_le
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))).2
      fun t => norm_periodicEconv_le hΦ f t

/-- **The two convolutions agree**: the `L_p` class of `Φ ⋆ f` for bounded continuous `f` is the
operator `Torus.periodicEconvLp` applied to the class of `f`, `1 ≤ p < ∞`. -/
theorem toLp_periodicEconvBCF {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ] (hp : p ≠ ∞)
    {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ) (f : UnitAddTorus d →ᵇ ℂ) :
    BoundedContinuousFunction.toLp (E := ℂ) p volume 𝕜 (periodicEconvBCF hΦ f) =
      periodicEconvLp hp hΦ (BoundedContinuousFunction.toLp (E := ℂ) p volume 𝕜 f) := by
  refine Lp.ext ?_
  have hf := BoundedContinuousFunction.coeFn_toLp (E := ℂ) p
    (volume : Measure (UnitAddTorus d)) 𝕜 f
  filter_upwards [BoundedContinuousFunction.coeFn_toLp (E := ℂ) p volume 𝕜 (periodicEconvBCF hΦ f),
    periodicEconvLp_apply_ae hp hΦ (BoundedContinuousFunction.toLp (E := ℂ) p volume 𝕜 f),
    periodicEconv_congr_ae Φ (Lp.stronglyMeasurable _).measurable f.continuous.measurable hf]
    with t h1 h2 h3
  rw [h1, h2, h3, periodicEconvBCF_apply]

/-- **Band-limited kernels map continuous functions into trigonometric polynomials**: if
`𝓕Φ(m) = 0` for `deg m ≥ N`, then `Φ ⋆ f` has degree `< N` (through `L_2` and the injectivity of
`f ↦ [f]` on continuous functions). -/
theorem periodicEconvBCF_mem_trigPoly {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ) {N : ℕ}
    (hF : ∀ m : d → ℤ, N ≤ trigDeg m → 𝓕 Φ (latticeVec m) = 0) (f : UnitAddTorus d →ᵇ ℂ) :
    periodicEconvBCF hΦ f ∈ trigPoly d N := by
  obtain ⟨a, ha, hae⟩ := Submodule.mem_map.1 (periodicEconvLp_mem_trigPolyLp (p := (2 : ℝ≥0∞))
    ENNReal.ofNat_ne_top hΦ hF (BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ f))
  have h : BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ a =
      BoundedContinuousFunction.toLp (E := ℂ) 2 volume ℂ (periodicEconvBCF hΦ f) := by
    rw [toLp_periodicEconvBCF (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top]
    exact hae
  rwa [← BoundedContinuousFunction.toLp_injective (E := ℂ) (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) volume h]

/-- **Kernels with `𝓕Φ = 1` on the low frequencies reproduce continuous trigonometric
polynomials**: if `𝓕Φ(m) = 1` for `deg m < N`, then `Φ ⋆ a = a` for `a` of degree `< N`. -/
theorem periodicEconvBCF_eq_self_of_mem {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ) {N : ℕ}
    (hF : ∀ m : d → ℤ, trigDeg m < N → 𝓕 Φ (latticeVec m) = 1) {a : UnitAddTorus d →ᵇ ℂ}
    (ha : a ∈ trigPoly d N) : periodicEconvBCF hΦ a = a := by
  refine BoundedContinuousFunction.toLp_injective (E := ℂ) (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) volume ?_
  rw [toLp_periodicEconvBCF (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top]
  exact periodicEconvLp_eq_self_of_mem _ hΦ hF (Submodule.mem_map_of_mem ha)

end BoundedContinuous

end Torus
