/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.RychkovExtension

/-!
# Besov spaces on Lipschitz graph domains by intrinsic differences

Let `Ω` be a Lipschitz graph domain with cone `K`. **Steps in the cone stay in `Ω`**: for `h ∈ K`
and `x ∈ Ω`, all points `x + l h`, `l ∈ ℕ`, lie in `Ω` (`Rd.LipschitzGraph.subset_stepSet`), so for
such steps the differences on `Ω` (`Rd.modulusOn`) are the differences on `V`. The cone bump `g`
vanishes outside `-K ∩ B(0, 1/2)`, so the steps `-c^(-1) z`, `g(z) ≠ 0`, of the averaged
differences lie in `K` and have length at most `1/(2c)`, and

`‖1_Ω (f - m_{2^j} ⋆ f)‖_p ≤ ‖g‖_1 ω_L(f, 2^(-(j+1)), Ω)_p`

(`Rd.LipschitzGraph.enorm_cutoff_sub_convLp_scaled_le`, from
`Rd.eLpNorm_indicator_sub_convLp_momentKernel_le`). Hence the intrinsic local means are bounded
by the moduli on `Ω` at the same scale, `‖1_Ω (k_j ⋆ f)‖_p ≤ 2 ‖g‖_1 ω_L(f, 2^(-j), Ω)_p` for
`j ≥ 1` (`Rd.LipschitzGraph.enorm_cutoff_localMean_succ_le`), and

`‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q} ≤ C (‖f‖_{L_p(Ω)} + ‖(2^(js) ω_L(f, 2^(-j), Ω)_p)_j‖_{ℓ_q})`

(`Rd.LipschitzGraph.intrinsicNorm_le`). The radius `1/2` of the bump matches the scales, so the
modulus on `Ω` is never dilated.

**Restrictions by intrinsic differences**
(`Rd.LipschitzGraph.exists_besov_extension_iff_modulusOn`): for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F ∈ L_p(V)` with
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`. The quasi-norms are equivalent: the
intrinsic one is at most that of every such `F` (`Rd.LipschitzGraph.modNormOn_le_modNorm`), and
Rychkov's extension `F = Ext f` attains it up to a constant
(`Rd.LipschitzGraph.modNorm_extension_le_modNormOn`). Since differences and band-limited
approximation describe the same spaces on `V` (`Rd.memApprox_bandScheme_iff_modulus`), the
restrictions of the approximation spaces `A^s_q(L_p(V))` of band-limited functions are described
by the same intrinsic condition (`Rd.LipschitzGraph.exists_memApprox_extension_iff`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-! ### Steps in the cone -/

/-- **Steps in the cone stay in `Ω`**: `Ω ⊆ Ω_{rh}` for `h ∈ K`. -/
theorem subset_stepSet {h : V} (hh : h ∈ Ω.cone) (r : ℕ) : Ω.domain ⊆ stepSet Ω.domain r h :=
  fun _ hx l _ => Ω.add_nsmul_mem hx hh l

/-- The steps of the averaged differences of a kernel supported in `-K` lie in the cone:
`Ω ⊆ Ω_{r h}` for `h = -c^(-1) z`, `c > 0` and `g(z) ≠ 0`. -/
theorem subset_stepSet_of_coneSupported {g : V → ℂ} (hg : Ω.ConeSupported g) {c : ℝ}
    (hc : 0 < c) (r : ℕ) {z : V} (hz : g z ≠ 0) : Ω.domain ⊆ stepSet Ω.domain r (-c⁻¹ • z) := by
  rw [neg_smul, ← smul_neg]
  exact Ω.subset_stepSet (Ω.smul_mem_cone (inv_pos.2 hc) (hg z hz)) r

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Intrinsic local means and moduli on `Ω` -/

/-- **Moment kernels approximate with the modulus on `Ω`**:
`‖1_Ω (f - m_{2^j} ⋆ f)‖_p ≤ ‖g‖_1 ω_L(f, 2^(-(j+1)), Ω)_p` for the cone bump `g`. -/
theorem enorm_cutoff_sub_convLp_scaled_le (hp : p ≠ ∞) (L j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    ‖Ω.cutoff (f - convLp hp (Ω.coneBump.integrable_scaled L j) f)‖ₑ ≤
      (∫⁻ z, ‖Ω.coneBump.toFun z‖ₑ) * lpModulusOn p Ω.domain L f (j + 1) := by
  have h := eLpNorm_indicator_sub_convLp_momentKernel_le hp Ω.coneBump.integrable
    Ω.coneBump.integral_eq_one Ω.coneBump.eq_zero L (c := 2 ^ j) (by positivity)
    Ω.measurableSet_domain
    (fun z hz => Ω.subset_stepSet_of_coneSupported Ω.coneSupported_coneBump (by positivity) L hz)
    f
  have hR : Ω.coneBump.radius / 2 ^ j = 1 / 2 ^ (j + 1) := by
    rw [Ω.coneBump_radius, pow_succ]
    ring
  rw [Ω.enorm_cutoff, lpModulusOn, ← hR]
  exact h

/-- `‖1_Ω (k_0 ⋆ f)‖_p ≤ ‖m‖_1 ‖f‖_{L_p(Ω)}`, by the support principle. -/
theorem enorm_cutoff_localMean_zero_le (hp : p ≠ ∞) (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖Ω.cutoff (Ω.coneBump.localMean hp L 0 f)‖ₑ ≤
      eLpNorm (momentKernel Ω.coneBump.toFun L) 1 volume * ‖Ω.cutoff f‖ₑ := by
  have h := Ω.cutoff_convLp_cutoff hp (Ω.coneBump.integrable_kernel L 0)
    (Ω.coneSupported_kernel L 0) f
  calc ‖Ω.cutoff (Ω.coneBump.localMean hp L 0 f)‖ₑ
      = ‖Ω.cutoff (Ω.coneBump.localMean hp L 0 (Ω.cutoff f))‖ₑ := congrArg (‖·‖ₑ) h.symm
    _ ≤ ‖Ω.coneBump.localMean hp L 0 (Ω.cutoff f)‖ₑ := Ω.enorm_cutoff_le _
    _ ≤ eLpNorm (momentKernel Ω.coneBump.toFun L) 1 volume * ‖Ω.cutoff f‖ₑ :=
        Ω.coneBump.enorm_localMean_zero_le hp L (Ω.cutoff f)

/-- **Intrinsic local means are bounded by the modulus on `Ω`**:
`‖1_Ω (k_{j+1} ⋆ f)‖_p ≤ 2 ‖g‖_1 ω_L(f, 2^(-(j+1)), Ω)_p`, since
`k_{j+1} ⋆ f = (f - m_{2^j} ⋆ f) - (f - m_{2^(j+1)} ⋆ f)`. -/
theorem enorm_cutoff_localMean_succ_le (hp : p ≠ ∞) (L j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    ‖Ω.cutoff (Ω.coneBump.localMean hp L (j + 1) f)‖ₑ ≤
      2 * (∫⁻ z, ‖Ω.coneBump.toFun z‖ₑ) * lpModulusOn p Ω.domain L f (j + 1) := by
  set A := ∫⁻ z, ‖Ω.coneBump.toFun z‖ₑ
  have hk : Ω.coneBump.localMean hp L (j + 1) f =
      (f - convLp hp (Ω.coneBump.integrable_scaled L j) f) -
        (f - convLp hp (Ω.coneBump.integrable_scaled L (j + 1)) f) := by
    rw [show Ω.coneBump.localMean hp L (j + 1) f =
        convLp hp (Ω.coneBump.integrable_scaled L (j + 1)) f -
          convLp hp (Ω.coneBump.integrable_scaled L j) f from
      convLp_sub_kernel hp (Ω.coneBump.integrable_scaled L (j + 1))
        (Ω.coneBump.integrable_scaled L j) f]
    abel
  calc ‖Ω.cutoff (Ω.coneBump.localMean hp L (j + 1) f)‖ₑ
      ≤ ‖Ω.cutoff (f - convLp hp (Ω.coneBump.integrable_scaled L j) f)‖ₑ +
          ‖Ω.cutoff (f - convLp hp (Ω.coneBump.integrable_scaled L (j + 1)) f)‖ₑ := by
        rw [hk, map_sub]
        exact enorm_sub_le
    _ ≤ A * lpModulusOn p Ω.domain L f (j + 1) + A * lpModulusOn p Ω.domain L f (j + 1) :=
        add_le_add (Ω.enorm_cutoff_sub_convLp_scaled_le hp L j f)
          ((Ω.enorm_cutoff_sub_convLp_scaled_le hp L (j + 1) f).trans
            (mul_le_mul' le_rfl (lpModulusOn_succ_le _ _ _ _)))
    _ = 2 * A * lpModulusOn p Ω.domain L f (j + 1) := by ring

/-- The constant `‖m‖_1 + 2 ‖g‖_1` of the intrinsic upper bound. -/
noncomputable def intrinsicConst (L : ℕ) : ℝ≥0∞ :=
  eLpNorm (momentKernel Ω.coneBump.toFun L) 1 volume + 2 * ∫⁻ z, ‖Ω.coneBump.toFun z‖ₑ

/-- The constant of the intrinsic upper bound is finite. -/
theorem intrinsicConst_ne_top (L : ℕ) : Ω.intrinsicConst L ≠ ∞ :=
  ENNReal.add_ne_top.2
    ⟨(memLp_one_iff_integrable.2 (integrable_momentKernel Ω.coneBump.integrable L)).eLpNorm_ne_top,
      ENNReal.mul_ne_top (by norm_num) Ω.coneBump.integrable.2.ne⟩

/-- **The intrinsic local means are bounded by the moduli on `Ω`**:
`‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q} ≤
C (‖f‖_{L_p(Ω)} + ‖(2^(js) ω_L(f, 2^(-j), Ω)_p)_j‖_{ℓ_q})`. -/
theorem intrinsicNorm_le (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure V)) :
    Ω.intrinsicNorm hp L s q f ≤ Ω.intrinsicConst L *
      (‖Ω.cutoff f‖ₑ + lqNorm q (fun j => dyadicWeight s j * lpModulusOn p Ω.domain L f j)) := by
  set A := ∫⁻ z, ‖Ω.coneBump.toFun z‖ₑ
  set M := eLpNorm (momentKernel Ω.coneBump.toFun L) 1 volume
  set Λ := lqNorm q (fun j => dyadicWeight s j * lpModulusOn p Ω.domain L f j)
  have htail : lqNorm q (fun j => dyadicWeight s (j + 1) *
      ‖Ω.cutoff (Ω.coneBump.localMean hp L (j + 1) f)‖ₑ) ≤ 2 * A * Λ :=
    calc lqNorm q (fun j => dyadicWeight s (j + 1) *
          ‖Ω.cutoff (Ω.coneBump.localMean hp L (j + 1) f)‖ₑ)
        ≤ lqNorm q (fun j => 2 * A *
            (dyadicWeight s (j + 1) * lpModulusOn p Ω.domain L f (j + 1))) :=
          ENNReal.lqNorm_mono fun j =>
            (mul_le_mul' le_rfl (Ω.enorm_cutoff_localMean_succ_le hp L j f)).trans_eq (by ring)
      _ = 2 * A * lqNorm q (fun j =>
            dyadicWeight s (j + 1) * lpModulusOn p Ω.domain L f (j + 1)) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ 2 * A * Λ := mul_le_mul' le_rfl
          (ENNReal.lqNorm_shift_le fun j => dyadicWeight s j * lpModulusOn p Ω.domain L f j)
  calc Ω.intrinsicNorm hp L s q f
      ≤ dyadicWeight s 0 * ‖Ω.cutoff (Ω.coneBump.localMean hp L 0 f)‖ₑ +
          lqNorm q (fun j => dyadicWeight s (j + 1) *
            ‖Ω.cutoff (Ω.coneBump.localMean hp L (j + 1) f)‖ₑ) :=
        ENNReal.lqNorm_le_head_add_shift hq _
    _ ≤ M * ‖Ω.cutoff f‖ₑ + 2 * A * Λ := by
        rw [ENNReal.dyadicWeight_zero_right, one_mul]
        exact add_le_add (Ω.enorm_cutoff_localMean_zero_le hp L f) htail
    _ ≤ Ω.intrinsicConst L * ‖Ω.cutoff f‖ₑ + Ω.intrinsicConst L * Λ := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = Ω.intrinsicConst L * (‖Ω.cutoff f‖ₑ + Λ) := by ring

/-- Finite intrinsic moduli give a finite intrinsic local means quasi-norm. -/
theorem intrinsicNorm_lt_top (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)}
    (hf : ‖Ω.cutoff f‖ₑ + lqNorm q (fun j => dyadicWeight s j * lpModulusOn p Ω.domain L f j) < ∞) :
    Ω.intrinsicNorm hp L s q f < ∞ :=
  (Ω.intrinsicNorm_le hp L s hq f).trans_lt
    (ENNReal.mul_lt_top (Ω.intrinsicConst_ne_top L).lt_top hf)

/-! ### Restrictions by intrinsic differences -/

/-- **The moduli on `Ω` are at most those of every function that agrees with `f` on `Ω`**: if
`1_Ω F = 1_Ω f`, then `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} ≤
‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q}`. -/
theorem modNormOn_le_modNorm (r : ℕ) (s : ℝ) (q : ℝ≥0∞) {F f : Lp ℂ p (volume : Measure V)}
    (hFf : Ω.cutoff F = Ω.cutoff f) :
    ‖Ω.cutoff f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω.domain r f k) ≤
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) := by
  refine add_le_add ?_ (ENNReal.lqNorm_mono fun k => mul_le_mul' le_rfl ?_)
  · rw [← hFf]
    exact Ω.enorm_cutoff_le F
  · rw [← lpModulusOn_congr (Ω.indicator_ae_eq_of_cutoff_eq hFf) r k]
    exact lpModulusOn_le_lpModulus Ω.measurableSet_domain r F k

/-- **Rychkov's extension agrees with `f` on `Ω`** when the intrinsic moduli are finite. -/
theorem cutoff_extension_of_modNormOn (hp : p ≠ ∞) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : ‖Ω.cutoff f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω.domain r f k) < ∞) :
    Ω.cutoff (Ω.extension hp r f) = Ω.cutoff f :=
  Ω.cutoff_extension hp hr hs hq (Ω.intrinsicNorm_lt_top hp r s hq hf)

/-- **Rychkov's extension is bounded in the moduli**: for `s > 0`,
`‖Ext f‖_p + ‖(2^(ks) ω_r(Ext f, 2^(-k))_p)_k‖_{ℓ_q} ≤
C (‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`, with `C` finite for `s < r`. -/
theorem modNorm_extension_le_modNormOn (hp : p ≠ ∞) (r : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : ‖Ω.cutoff f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω.domain r f k) < ∞) :
    ‖Ω.extension hp r f‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpModulus p r (Ω.extension hp r f) k) ≤
      Ω.coneBump.synthConst r s * Ω.intrinsicConst r *
        (‖Ω.cutoff f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω.domain r f k)) := by
  rw [mul_assoc]
  exact (Ω.modNorm_extension_le hp r hs hq (Ω.intrinsicNorm_lt_top hp r s hq hf)).trans
    (mul_le_mul' le_rfl (Ω.intrinsicNorm_le hp r s hq f))

/-- **Restrictions of Besov spaces to Lipschitz graph domains, by intrinsic differences**: for
`1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F ∈ L_p(V)` with
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`; Rychkov's extension is such an
`F`. -/
theorem exists_besov_extension_iff_modulusOn (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (∃ F : Lp ℂ p (volume : Measure V), Ω.cutoff F = Ω.cutoff f ∧
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞) ↔
      ‖Ω.cutoff f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω.domain r f k) < ∞ := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 fun h => by
    rw [h, Nat.cast_zero] at hsr
    exact lt_irrefl _ (hs.trans hsr)
  constructor
  · rintro ⟨F, hFf, hF⟩
    exact (Ω.modNormOn_le_modNorm r s q hFf).trans_lt hF
  · intro hf
    exact (Ω.exists_besov_extension_iff hp hr hs hsr hq f).2 (Ω.intrinsicNorm_lt_top hp r s hq hf)

/-- **Restrictions of band-limited approximation spaces to Lipschitz graph domains**: for
`1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F` in the approximation
space `A^s_q(L_p(V))` of band-limited functions iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`. -/
theorem exists_memApprox_extension_iff (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (∃ F : Lp ℂ p (volume : Measure V), Ω.cutoff F = Ω.cutoff f ∧
        (bandScheme hp).MemApprox s q F) ↔
      ‖Ω.cutoff f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω.domain r f k) < ∞ := by
  rw [← Ω.exists_besov_extension_iff_modulusOn hp hs hsr hq f]
  exact exists_congr fun F =>
    and_congr_right fun _ => memApprox_bandScheme_iff_modulus hp hs.le hsr hq F

end LipschitzGraph

end Rd
