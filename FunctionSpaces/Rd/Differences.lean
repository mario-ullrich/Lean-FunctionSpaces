/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.ApproxIdentity
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Differences and the modulus of smoothness on `V`

For `f : V → ℂ`, a step `h ∈ V` and `r ∈ ℕ`, the **difference** of order `r` is
`Δ_h^r f = (Δ_h)^r f` with `Δ_h f(x) = f(x + h) - f(x)` (Mathlib's `fwdDiff`), and
`Δ_h^r f(x) = ∑_{l ≤ r} (-1)^(r-l) C(r, l) f(x + l h)` (`Rd.iterDiff_apply`). For a Haar
measure `μ` the **modulus of smoothness** in `L_p(μ)` is
`ω_r(f, t)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r f‖_p` (`Rd.modulus`). It increases in `t`, is subadditive in
`f`, is bounded by `2^r ‖f‖_p` (`Rd.modulus_le`), and depends only on the class of `f` modulo
null sets (`Rd.modulus_congr_ae`).

**Dilating the step** (`Rd.modulus_mul_le`): `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` for
`c, t ≥ 0`. For an integer `m ≥ 1`, `Δ_{mh} = ∑_{i<m} τ_{ih} Δ_h` with the translations
`τ_a g = g(· + a)` (`Rd.fwdDiff_nsmul`), translations commute with differences
(`Rd.iterDiff_comp_add`), and translations keep `L_p` norms, so
`‖Δ_{mh}^r f‖_p ≤ m^r ‖Δ_h^r f‖_p` (`Rd.eLpNorm_iterDiff_nsmul_iterDiff_le`).

`Rd.lpModulus` samples the modulus of `f ∈ L_p` at the dyadic scales `2^(-k)`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-! ### Differences and translations -/

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `Δ_h f = f(· + h) - f`. -/
theorem fwdDiff_eq_sub (h : V) (f : V → ℂ) : fwdDiff h f = (fun x => f (x + h)) - f :=
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `Δ_h^r f(x) = ∑_{l ≤ r} (-1)^(r-l) C(r, l) f(x + l h)` (Mathlib's
`fwdDiff_iter_eq_sum_shift`). -/
theorem iterDiff_apply (r : ℕ) (h : V) (f : V → ℂ) (x : V) :
    (fwdDiff h)^[r] f x = ∑ l ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) * f (x + (l : ℝ) • h) := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [zsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  push_cast
  ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences commute with translations**: `Δ_h^r (f(· + c)) = (Δ_h^r f)(· + c)`. -/
theorem iterDiff_comp_add (r : ℕ) (h c : V) (f : V → ℂ) :
    (fwdDiff h)^[r] (fun x => f (x + c)) = fun x => (fwdDiff h)^[r] f (x + c) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [fwdDiff, add_right_comm x h c]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences with a multiple step telescope**: `Δ_{mh} f = ∑_{i<m} (Δ_h f)(· + i h)`. -/
theorem fwdDiff_nsmul (m : ℕ) (h : V) (f : V → ℂ) :
    fwdDiff (m • h) f = ∑ i ∈ Finset.range m, fun x => fwdDiff h f (x + i • h) := by
  induction m with
  | zero =>
    funext x
    simp [fwdDiff]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    funext x
    simp only [fwdDiff, Pi.add_apply, succ_nsmul, ← add_assoc]
    ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Translates of a.e. strongly measurable functions are a.e. strongly measurable. -/
theorem aestronglyMeasurable_comp_add {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (c : V) :
    AEStronglyMeasurable (fun x => f (x + c)) μ :=
  hf.comp_measurePreserving (measurePreserving_add_right μ c)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Translations keep `L_p` norms**: `‖f(· + c)‖_p = ‖f‖_p`. -/
theorem eLpNorm_comp_add_right {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) (c : V) :
    eLpNorm (fun x => f (x + c)) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right μ c)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Translates of functions that agree almost everywhere agree almost everywhere. -/
theorem ae_comp_add_right {f g : V → ℂ} (hfg : f =ᵐ[μ] g) (c : V) :
    (fun x => f (x + c)) =ᵐ[μ] fun x => g (x + c) :=
  (measurePreserving_add_right μ c).quasiMeasurePreserving.ae_eq_comp hfg

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Differences of a.e. strongly measurable functions are a.e. strongly measurable. -/
theorem aestronglyMeasurable_iterDiff {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (r : ℕ)
    (h : V) : AEStronglyMeasurable ((fwdDiff h)^[r] f) μ := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff_eq_sub]
    exact (aestronglyMeasurable_comp_add ih h).sub ih

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Differences of functions that agree almost everywhere agree almost everywhere. -/
theorem iterDiff_congr_ae {f g : V → ℂ} (hfg : f =ᵐ[μ] g) (r : ℕ) (h : V) :
    (fwdDiff h)^[r] f =ᵐ[μ] (fwdDiff h)^[r] g := by
  induction r with
  | zero => exact hfg
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fwdDiff_eq_sub,
      fwdDiff_eq_sub]
    exact (ae_comp_add_right ih h).sub ih

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **`‖Δ_h^r f‖_p ≤ 2^r ‖f‖_p`**, from `‖Δ_h g‖_p ≤ ‖g(· + h)‖_p + ‖g‖_p = 2 ‖g‖_p`. -/
theorem eLpNorm_iterDiff_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (r : ℕ) (h : V) :
    eLpNorm ((fwdDiff h)^[r] f) p μ ≤ 2 ^ r * eLpNorm f p μ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff_eq_sub]
    calc eLpNorm ((fun x => (fwdDiff h)^[r] f (x + h)) - (fwdDiff h)^[r] f) p μ
        ≤ eLpNorm (fun x => (fwdDiff h)^[r] f (x + h)) p μ + eLpNorm ((fwdDiff h)^[r] f) p μ :=
          eLpNorm_sub_le hp
      _ = 2 * eLpNorm ((fwdDiff h)^[r] f) p μ := by
          rw [eLpNorm_comp_add_right (aestronglyMeasurable_iterDiff hf r h), two_mul]
      _ ≤ 2 * (2 ^ r * eLpNorm f p μ) := by gcongr
      _ = 2 ^ (r + 1) * eLpNorm f p μ := by rw [pow_succ]; ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Multiples of the step**: `‖Δ_{mh}^a Δ_h^b f‖_p ≤ m^a ‖Δ_h^(a+b) f‖_p`, by induction on
`a`, with `Δ_{mh} = ∑_{i<m} τ_{ih} Δ_h`. -/
theorem eLpNorm_iterDiff_nsmul_iterDiff_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (m : ℕ) (h : V) (a : ℕ) :
    ∀ b, eLpNorm ((fwdDiff (m • h))^[a] ((fwdDiff h)^[b] f)) p μ ≤
      (m : ℝ≥0∞) ^ a * eLpNorm ((fwdDiff h)^[a + b] f) p μ := by
  induction a with
  | zero => intro b; simp
  | succ a ih =>
    intro b
    have hsplit : (fwdDiff (m • h))^[a + 1] ((fwdDiff h)^[b] f) =
        ∑ i ∈ Finset.range m,
          fun x => (fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f) (x + i • h) := by
      rw [Function.iterate_succ_apply, fwdDiff_nsmul, fwdDiff_iter_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [iterDiff_comp_add, ← Function.iterate_succ_apply' (fwdDiff h) b f]
    have hmeas : AEStronglyMeasurable ((fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f)) μ :=
      aestronglyMeasurable_iterDiff (aestronglyMeasurable_iterDiff hf (b + 1) h) a (m • h)
    rw [hsplit]
    calc eLpNorm (∑ i ∈ Finset.range m,
          fun x => (fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f) (x + i • h)) p μ
        ≤ ∑ i ∈ Finset.range m,
            eLpNorm (fun x => (fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f) (x + i • h)) p μ :=
          eLpNorm_sum_le hp
      _ = ∑ _i ∈ Finset.range m,
            eLpNorm ((fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f)) p μ :=
          Finset.sum_congr rfl fun i _ => eLpNorm_comp_add_right hmeas p _
      _ ≤ ∑ _i ∈ Finset.range m,
            (m : ℝ≥0∞) ^ a * eLpNorm ((fwdDiff h)^[a + (b + 1)] f) p μ :=
          Finset.sum_le_sum fun i _ => ih (b + 1)
      _ = (m : ℝ≥0∞) ^ (a + 1) * eLpNorm ((fwdDiff h)^[a + 1 + b] f) p μ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            show a + (b + 1) = a + 1 + b by omega, pow_succ]
          ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Differences of integrable functions are integrable. -/
theorem integrable_iterDiff {K : V → ℂ} (hK : Integrable K μ) (r : ℕ) (h : V) :
    Integrable ((fwdDiff h)^[r] K) μ := by
  induction r with
  | zero => exact hK
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff_eq_sub]
    exact (ih.comp_add_right h).sub ih

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Translates of convolutions**: `(K ⋆ f)(x + c) = (K(· + c) ⋆ f)(x)`, by the substitution
`y ↦ y + c`. -/
theorem conv_comp_add (K f : V → ℂ) (c x : V) :
    conv K f μ (x + c) = conv (fun y => K (y + c)) f μ x := by
  rw [conv_apply, conv_apply, ← integral_add_right_eq_self (fun y => K y * f (x + c - y)) c]
  congr 1
  funext y
  rw [show x + c - (y + c) = x - y by abel]

/-- **Differences of convolutions**: `Δ_h^r (K ⋆ f) = (Δ_h^r K) ⋆ f` almost everywhere, for an
integrable `K` and `f ∈ L_p`, `1 ≤ p < ∞`. -/
theorem iterDiff_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : V → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) (r : ℕ) (h : V) :
    (fwdDiff h)^[r] (conv K f μ) =ᵐ[μ] conv ((fwdDiff h)^[r] K) f μ := by
  induction r with
  | zero => exact Filter.EventuallyEq.rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fwdDiff_eq_sub,
      fwdDiff_eq_sub]
    have hKr : Integrable ((fwdDiff h)^[r] K) μ := integrable_iterDiff hK r h
    have h1 : (fun x => (fwdDiff h)^[r] (conv K f μ) (x + h)) =ᵐ[μ]
        conv (fun y => (fwdDiff h)^[r] K (y + h)) f μ := by
      refine (ae_comp_add_right ih h).trans (Filter.EventuallyEq.of_eq ?_)
      funext x
      exact conv_comp_add _ _ h x
    exact (h1.sub ih).trans (sub_conv_ae hp1 hp (hKr.comp_add_right h) hKr hf).symm

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences of dilations**: `Δ_h^r (Φ_c) = (Δ_{ch}^r Φ)_c`. -/
theorem iterDiff_dilate (r : ℕ) (c : ℝ) (h : V) (Φ : V → ℂ) :
    (fwdDiff h)^[r] (dilate c Φ) = dilate c ((fwdDiff (c • h))^[r] Φ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [fwdDiff, dilate, smul_add]
    ring

/-! ### The modulus of smoothness -/

variable (μ) in
/-- The **modulus of smoothness** `ω_r(f, t)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r f‖_p`. -/
noncomputable def modulus (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (h : V) (_ : ‖h‖ ≤ t), eLpNorm ((fwdDiff h)^[r] f) p μ

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- `‖Δ_h^r f‖_p ≤ ω_r(f, t)_p` for `‖h‖ ≤ t`. -/
theorem eLpNorm_iterDiff_le_modulus {r : ℕ} {p : ℝ≥0∞} {f : V → ℂ} {t : ℝ}
    {h : V} (hh : ‖h‖ ≤ t) : eLpNorm ((fwdDiff h)^[r] f) p μ ≤ modulus μ r p f t :=
  le_iSup₂ (f := fun (h : V) (_ : ‖h‖ ≤ t) => eLpNorm ((fwdDiff h)^[r] f) p μ) h hh

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The modulus increases in `t`. -/
theorem modulus_mono (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) :
    Monotone (modulus μ r p f) :=
  fun _ _ hst => iSup₂_le fun _ hh => eLpNorm_iterDiff_le_modulus (hh.trans hst)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The modulus is subadditive. -/
theorem modulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (f g : V → ℂ)
    (t : ℝ) : modulus μ r p (f + g) t ≤ modulus μ r p f t + modulus μ r p g t := by
  refine iSup₂_le fun h hh => ?_
  rw [fwdDiff_iter_add]
  exact (eLpNorm_add_le hp).trans
    (add_le_add (eLpNorm_iterDiff_le_modulus hh) (eLpNorm_iterDiff_le_modulus hh))

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `ω_r(f, t)_p ≤ 2^r ‖f‖_p`. -/
theorem modulus_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) (t : ℝ) : modulus μ r p f t ≤ 2 ^ r * eLpNorm f p μ :=
  iSup₂_le fun h _ => eLpNorm_iterDiff_le hf hp r h

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The modulus depends only on the class modulo null sets.** -/
theorem modulus_congr_ae {f g : V → ℂ} (hfg : f =ᵐ[μ] g) (r : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    modulus μ r p f t = modulus μ r p g t := by
  simp only [modulus]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_congr_ae (iterDiff_congr_ae hfg r h)

omit [FiniteDimensional ℝ V] in
/-- **Integer multiples of the scale**: `ω_r(f, m t)_p ≤ m^r ω_r(f, t)_p` for `m ≥ 1`. -/
theorem modulus_nat_mul_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    modulus μ r p f (m * t) ≤ (m : ℝ≥0∞) ^ r * modulus μ r p f t := by
  refine iSup₂_le fun h hh => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨h', hh', rfl⟩ : ∃ h' : V, ‖h'‖ ≤ t ∧ h = m • h' := by
    refine ⟨(m : ℝ)⁻¹ • h, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hm0.le), inv_mul_le_iff₀ hm0]
      exact hh
    · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀ hm0.ne']
  have h1 := eLpNorm_iterDiff_nsmul_iterDiff_le hf hp m h' r 0
  simp only [Function.iterate_zero, id_eq, add_zero] at h1
  exact h1.trans (by gcongr; exact eLpNorm_iterDiff_le_modulus hh')

omit [FiniteDimensional ℝ V] in
/-- **Dilating the scale**: `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` for `c, t ≥ 0`, with the
integer `m = ⌊c⌋ + 1 ≤ 1 + c`. -/
theorem modulus_mul_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    modulus μ r p f (c * t) ≤ ENNReal.ofReal (1 + c) ^ r * modulus μ r p f t := by
  have hm : 1 ≤ ⌊c⌋₊ + 1 := Nat.le_add_left 1 _
  have hcm : c ≤ ((⌊c⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact (Nat.lt_floor_add_one c).le
  have hm1 : (((⌊c⌋₊ + 1 : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal (1 + c) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith [Nat.floor_le hc]
  calc modulus μ r p f (c * t) ≤ modulus μ r p f ((⌊c⌋₊ + 1 : ℕ) * t) :=
        modulus_mono r p f (mul_le_mul_of_nonneg_right hcm ht)
    _ ≤ ((⌊c⌋₊ + 1 : ℕ) : ℝ≥0∞) ^ r * modulus μ r p f t := modulus_nat_mul_le hf hp r hm t
    _ ≤ ENNReal.ofReal (1 + c) ^ r * modulus μ r p f t := by gcongr

/-! ### The modulus on `L_p` at dyadic scales -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The modulus of an element of `L_p` at the dyadic scale `2^(-k)`. -/
noncomputable def lpModulus (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) : ℝ≥0∞ :=
  modulus μ r p (f : V → ℂ) (1 / 2 ^ k)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The modulus on `L_p` is subadditive. -/
theorem lpModulus_add_le (r : ℕ) (f g : Lp ℂ p μ) (k : ℕ) :
    lpModulus p r (f + g) k ≤ lpModulus p r f k + lpModulus p r g k := by
  rw [lpModulus, modulus_congr_ae (Lp.coeFn_add f g)]
  exact modulus_add_le Fact.out r _ _ _

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `ω_r(f, 2^(-k))_p ≤ 2^r ‖f‖_p` on `L_p`. -/
theorem lpModulus_le (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) : lpModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.enorm_def]
  exact modulus_le (Lp.aestronglyMeasurable f) Fact.out r _

end Rd
