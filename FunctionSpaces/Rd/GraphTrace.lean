/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.GraphParametrization
public import FunctionSpaces.Rd.LocalExtension

/-!
# Traces on Lipschitz graph domains

The **trace** of `f` on the boundary `Γ` of a Lipschitz graph domain `Ω`, a function on the
hyperplane `H = e^⊥` through the graph map `γ`, is the series of the restrictions of the terms of
Rychkov's extension (`Rd.LipschitzGraph.trace`):

`Tr f = ∑_j (η_j ⋆ h_j) ∘ γ`,  `h_j = 1_Ω (k_j ⋆ f)`,

with the local means `k_j` and dual kernels `η_j` of the cone bump; by the support principle only
`f` on `Ω` enters. More generally `Rd.LipschitzGraph.traceSeries` restricts `∑_j η_j ⋆ h_j` for
any `h_j ∈ L_p(V)`.

**The trace theorem** (`Rd.LipschitzGraph.modNorm_trace_le`; Schneider–Vybíral, Theorem 4.2,
for `p ≥ 1`): for `1 ≤ p < ∞`, `0 < s < 1` and `1 ≤ q ≤ ∞`,

`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr f, 2^(-k))_p)_k‖_{ℓ_q}
  ≤ K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`.

The proof follows Schneider–Vybíral with atoms: the cell atoms `a_{j,m}` of `η_j ⋆ h_j`
(`Rd.cellAtom`) satisfy pointwise Lipschitz bounds, so their restrictions `a_{j,m} ∘ γ` are
regular atoms of order and exponent `1` on `H` (`Rd.LipschitzGraph.isRegularAtom_comp_graphMap`),
centred at the projections of the cell centres. Only the cells whose atoms meet the graph count
(`Rd.LipschitzGraph.traceCoef`); their centres lie within `ρ 2^(-j)` of `Γ`, so they have bounded
overlap on `H` (`Rd.LipschitzGraph.exists_trace_atoms`). With `‖λ_{j,·}‖_{ℓ_p} ≤ 2^(jn/p) ‖h_j‖_p`
the coefficient quasi-norm on `H` is at most `‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q}`, since
`s - (n-1)/p = (s + 1/p) - n/p`, and the atomic synthesis on `H` (`Rd.modNorm_le_coeffNorm`)
concludes (`Rd.LipschitzGraph.modNorm_traceSeries_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

section ApproxIdentity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Approximate identities at points of continuity**: if `Φ` is integrable with `∫ Φ = 1` and
vanishes outside `B̄(0, R)`, and `F_J(z) → z₀` as `J → ∞` and `z → y`, then
`(Φ_{2^J} ⋆ F_J)(z) → z₀` as `J → ∞` and `z → y`: for every `ε > 0` there are `J₀` and `δ > 0`
with `|(Φ_{2^J} ⋆ F_J)(z) - z₀| < ε` for `J ≥ J₀` and `‖z - y‖ < δ`. Since `∫ Φ_{2^J} = 1`,
`(Φ_{2^J} ⋆ F_J)(z) - z₀ = ∫ Φ_{2^J}(w) (F_J(z - w) - z₀) dw`, and only `‖w‖ ≤ R 2^(-J)` enters. -/
theorem conv_dilate_near {Φ : V → ℂ} (hΦ : Integrable Φ) (h1 : ∫ x, Φ x = 1) {R : ℝ}
    (hR : 0 ≤ R) (hΦR : ∀ w, R < ‖w‖ → Φ w = 0) {F : ℕ → V → ℂ}
    (hFm : ∀ J, AEStronglyMeasurable (F J) volume) {y : V} {z₀ : ℂ}
    (hF : ∀ ε > 0, ∃ J₀ : ℕ, ∃ δ > 0, ∀ J ≥ J₀, ∀ z, ‖z - y‖ < δ → ‖F J z - z₀‖ < ε) :
    ∀ ε > 0, ∃ J₀ : ℕ, ∃ δ > 0, ∀ J ≥ J₀, ∀ z, ‖z - y‖ < δ →
      ‖conv (dilate (2 ^ J) Φ) (F J) volume z - z₀‖ < ε := by
  intro ε hε
  have hM : 0 ≤ ∫ x, ‖Φ x‖ := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨J₁, δ₁, hδ₁, hJ₁⟩ := hF (ε / ((∫ x, ‖Φ x‖) + 1)) (by positivity)
  obtain ⟨J₂, hJ₂⟩ := pow_unbounded_of_one_lt (2 * R / δ₁) (one_lt_two : (1 : ℝ) < 2)
  have hJ₂' : ∀ J ≥ J₂, R / 2 ^ J < δ₁ / 2 := fun J hJ => by
    have h2 : (2 : ℝ) ^ J₂ ≤ 2 ^ J := pow_le_pow_right₀ one_le_two hJ
    rw [div_lt_div_iff₀ (by positivity) two_pos]
    rw [div_lt_iff₀ hδ₁] at hJ₂
    nlinarith
  refine ⟨max J₁ J₂, δ₁ / 2, half_pos hδ₁, fun J hJ z hz => ?_⟩
  have hJ1 : J₁ ≤ J := le_of_max_le_left hJ
  have hJ2 : J₂ ≤ J := le_of_max_le_right hJ
  have hΦ' : Integrable (dilate ((2 : ℝ) ^ J) Φ) := integrable_dilate hΦ (by positivity)
  have hsupp : ∀ w, dilate ((2 : ℝ) ^ J) Φ w ≠ 0 → ‖w‖ < δ₁ / 2 := fun w hw => by
    by_contra hcon
    push Not at hcon
    apply hw
    rw [dilate, hΦR _ ?_, mul_zero]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h3 := hJ₂' J hJ2
    rw [div_lt_iff₀ (by positivity)] at h3
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) J]
  have hpt : ∀ w, ‖dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀)‖ ≤
      ‖dilate ((2 : ℝ) ^ J) Φ w‖ * (ε / ((∫ x, ‖Φ x‖) + 1)) := fun w => by
    by_cases hw : dilate ((2 : ℝ) ^ J) Φ w = 0
    · simp [hw]
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left (hJ₁ J hJ1 (z - w) ?_).le (norm_nonneg _)
      calc ‖z - w - y‖ = ‖(z - y) - w‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖w‖ := norm_sub_le _ _
        _ < δ₁ / 2 + δ₁ / 2 := add_lt_add hz (hsupp w hw)
        _ = δ₁ := by ring
  have hmeas : AEStronglyMeasurable (fun w => F J (z - w)) volume :=
    (hFm J).comp_measurePreserving (Measure.measurePreserving_sub_left volume z)
  have hint1 : Integrable (fun w => dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀)) volume :=
    Integrable.mono' (hΦ'.norm.mul_const _)
      (hΦ'.aestronglyMeasurable.mul (hmeas.sub aestronglyMeasurable_const))
      (Eventually.of_forall hpt)
  have hint2 : Integrable (fun w => dilate ((2 : ℝ) ^ J) Φ w * F J (z - w)) volume :=
    (hint1.add (hΦ'.mul_const z₀)).congr (Eventually.of_forall fun w => by
      simp only [Pi.add_apply]
      ring)
  have hone : ∫ w, dilate ((2 : ℝ) ^ J) Φ w = 1 := by
    rw [integral_dilate Φ (by positivity), h1]
  have hkey : conv (dilate (2 ^ J) Φ) (F J) volume z - z₀ =
      ∫ w, dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀) := by
    rw [conv_apply]
    calc (∫ w, dilate ((2 : ℝ) ^ J) Φ w * F J (z - w)) - z₀
        = (∫ w, dilate ((2 : ℝ) ^ J) Φ w * F J (z - w)) -
            ∫ w, dilate ((2 : ℝ) ^ J) Φ w * z₀ := by
          rw [integral_mul_const, hone, one_mul]
      _ = ∫ w, (dilate ((2 : ℝ) ^ J) Φ w * F J (z - w) - dilate ((2 : ℝ) ^ J) Φ w * z₀) :=
          (integral_sub hint2 (hΦ'.mul_const z₀)).symm
      _ = _ := by
          congr 1
          funext w
          ring
  have hnorm : ∫ w, ‖dilate ((2 : ℝ) ^ J) Φ w‖ = ∫ x, ‖Φ x‖ := by
    rw [integral_norm_eq_lintegral_enorm hΦ'.aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hΦ.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm hΦ'.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm hΦ.aestronglyMeasurable,
      eLpNorm_dilate_one hΦ (by positivity)]
  rw [hkey]
  calc ‖∫ w, dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀)‖
      ≤ ∫ w, ‖dilate ((2 : ℝ) ^ J) Φ w‖ * (ε / ((∫ x, ‖Φ x‖) + 1)) :=
        norm_integral_le_of_norm_le (hΦ'.norm.mul_const _) (Eventually.of_forall hpt)
    _ = (∫ x, ‖Φ x‖) * ε / ((∫ x, ‖Φ x‖) + 1) := by
        rw [integral_mul_const, hnorm]
        ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

end ApproxIdentity

namespace LocalMeansBump

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (b : LocalMeansBump V)

/-- The dilated moment kernels have compact support. -/
theorem hasCompactSupport_scaled (L j : ℕ) : HasCompactSupport (b.scaled L j) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (L * b.radius / 2 ^ j)) fun y hy =>
    b.scaled_eq_zero_of_lt L j (by simpa [mem_closedBall, dist_zero_right, not_le] using hy)

/-- The dilated moment kernels are continuous. -/
theorem continuous_scaled (L j : ℕ) : Continuous (b.scaled L j) :=
  continuous_dilate (b.contDiff_momentKernel L).continuous _

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The reproducing formula at every point**: `∑_{j ≤ J} (η_j ⋆ (k_j ⋆ f))(y) =
(m_{2^J} ⋆ (m_{2^J} ⋆ f))(y)` for all `y`, since both sides are continuous and agree almost
everywhere (`Rd.LocalMeansBump.sum_dual_localMean`). -/
theorem sum_conv_dual_localMean_apply (hp : p ≠ ∞) (L J : ℕ)
    (f : Lp ℂ p (volume : Measure V)) (y : V) :
    ∑ j ∈ Finset.range (J + 1), conv (b.dual L j) (b.localMean hp L j f) volume y =
      conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume y := by
  have hp1 : 1 ≤ p := Fact.out
  have hcont1 : Continuous fun y =>
      ∑ j ∈ Finset.range (J + 1), conv (b.dual L j) (b.localMean hp L j f) volume y :=
    continuous_finsetSum _ fun j _ => (b.hasCompactSupport_dual L j).continuous_convolution_left
      (ContinuousLinearMap.mul ℂ ℂ) (b.continuous_dual L j) ((Lp.memLp _).locallyIntegrable hp1)
  have hcont2 : Continuous (conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume) :=
    (b.hasCompactSupport_scaled L J).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
      (b.continuous_scaled L J) ((Lp.memLp _).locallyIntegrable hp1)
  have hae : (fun y => ∑ j ∈ Finset.range (J + 1),
      conv (b.dual L j) (b.localMean hp L j f) volume y) =ᵐ[volume]
        conv (b.scaled L J) (convLp hp (b.integrable_scaled L J) f) volume := by
    have h1 := Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
      (fun j => convLp hp (b.integrable_dual L j) (b.localMean hp L j f))
    rw [b.sum_dual_localMean hp L J f] at h1
    have h2 := convLp_apply_ae hp (b.integrable_scaled L J)
      (convLp hp (b.integrable_scaled L J) f)
    have h3 : ∀ᵐ y ∂volume, ∀ j, convLp hp (b.integrable_dual L j) (b.localMean hp L j f) y =
        conv (b.dual L j) (b.localMean hp L j f) volume y :=
      ae_all_iff.2 fun j => convLp_apply_ae hp _ _
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [← hy2, hy1]
    exact Finset.sum_congr rfl fun j _ => (hy3 j).symm
  exact congrFun ((Continuous.ae_eq_iff_eq volume hcont1 hcont2).1 hae) y

end LocalMeansBump

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V)

/-! ### Traces of the terms -/

section Terms

variable (b : LocalMeansBump V)

/-- The **trace of a term**: `x' ↦ (η_j ⋆ h)(γ x')`. -/
noncomputable def traceFun (L j : ℕ) (h : V → ℂ) (x' : Ω.hyperplane) : ℂ :=
  conv (b.dual L j) h volume (Ω.graphMap x')

open Classical in
/-- The **coefficients of the trace atoms**: `λ_{j,m}` for the cells whose atoms meet the graph,
`0` for the others. -/
noncomputable def traceCoef (p : ℝ≥0∞) (L j : ℕ) (h : V → ℂ) (m : Fin (finrank ℝ V) → ℤ) : ℂ :=
  if ∃ y', cellAtom p (b.dual L j) j h m (Ω.graphMap y') ≠ 0 then cellCoef p j h m else 0

/-- The trace of a term is continuous. -/
theorem continuous_traceFun {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) : Continuous (Ω.traceFun b L j h) :=
  ((b.hasCompactSupport_dual L j).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
    (b.continuous_dual L j) (hh.locallyIntegrable hp1)).comp Ω.continuous_graphMap

/-- **The trace of a term is the sum of the traces of its cell atoms**:
`(η_j ⋆ h)(γ x') = ∑_m λ'_{j,m} a_{j,m}(γ x')` with the coefficients of the cells meeting the
graph. -/
theorem traceFun_eq_tsum {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) (x' : Ω.hyperplane) :
    Ω.traceFun b L j h x' =
      ∑' m, Ω.traceCoef b p L j h m * (cellAtom p (b.dual L j) j h m ∘ Ω.graphMap) x' := by
  have hρ : 0 ≤ 2 * (L : ℝ) * b.radius / 2 ^ j :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg)
      (by positivity)
  rw [traceFun, conv_eq_tsum_cellAtom hp1 (b.continuous_dual L j) hρ
    (fun y hy => b.dual_eq_zero_of_lt L j hy) hh j]
  refine tsum_congr fun m => ?_
  rw [Function.comp_apply, traceCoef]
  split_ifs with hm
  · rfl
  · push Not at hm
    rw [hm x', mul_zero, mul_zero]

/-- `|λ'_{j,m}| ≤ |λ_{j,m}|`. -/
theorem enorm_traceCoef_le (p : ℝ≥0∞) (L j : ℕ) (h : V → ℂ) (m : Fin (finrank ℝ V) → ℤ) :
    ‖Ω.traceCoef b p L j h m‖ₑ ≤ ‖cellCoef p j h m‖ₑ := by
  rw [traceCoef]
  split_ifs
  · exact le_rfl
  · rw [enorm_zero]
    exact zero_le

/-- `‖λ'_{j,·}‖_{ℓ_p} ≤ 2^(jn/p) ‖h‖_p`. -/
theorem levelNorm_traceCoef_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) :
    levelNorm p (Ω.traceCoef b p L j h) ≤
      dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm h p volume :=
  (levelNorm_mono p (Ω.enorm_traceCoef_le b p L j h)).trans_eq (levelNorm_cellCoef hp0 hp hh j)

/-- **The trace atoms**: there are a radius factor `d`, a constant `C < ∞` and an overlap bound
`N` such that for every level `j` and `h ∈ L_p` the restrictions `a_{j,m} ∘ γ` of the cell atoms
of `η_j ⋆ h` are regular atoms of order and exponent `1` on `H` centred at `P c_{j,m}`, and the
centres of the cells meeting the graph have overlap at most `N`: such a centre lies within
`(d + (1 + M)(2d + 1)) 2^(-j)` of `γ x'` whenever its projection lies within `(d + 1) 2^(-j)` of
`x'`. -/
theorem exists_trace_atoms {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L : ℕ) :
    ∃ (d : ℝ) (C : ℝ≥0∞) (N : ℕ), 0 ≤ d ∧ C ≠ ∞ ∧ ∀ (j : ℕ) {h : V → ℂ}, MemLp h p volume →
      (∀ m, IsRegularAtom p 1 1 d C j (Ω.proj (cellCenter j m))
        (cellAtom p (b.dual L j) j h m ∘ Ω.graphMap)) ∧
      ∀ x' (S : Finset (Fin (finrank ℝ V) → ℤ)),
        (∀ m ∈ S, Ω.traceCoef b p L j h m ≠ 0 ∧ ‖x' - Ω.proj (cellCenter j m)‖ ≤ (d + 1) / 2 ^ j) →
          S.card ≤ N := by
  obtain ⟨A, hA, hb⟩ := b.exists_iterDiff_dual_bound L 1
  have ht : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  set ρ := 2 * (L : ℝ) * b.radius
  have hρ : 0 ≤ ρ := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg
  set d := ρ + finrank ℝ V
  have hd : 0 ≤ d := add_nonneg hρ (Nat.cast_nonneg _)
  set A1 := 2 ^ (1 : ℕ) * A * (ENNReal.ofReal ((ρ + 1) ^ finrank ℝ V) *
    volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal)
  have hA1 : A1 ≠ ∞ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA)
    (ENNReal.rpow_ne_top_of_nonneg ht (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      measure_ball_lt_top.ne))
  set ρ' := d + (1 + Ω.M) * (2 * d + 1)
  have hρ' : 0 ≤ ρ' := add_nonneg hd (mul_nonneg (by linarith [Ω.M_nonneg]) (by linarith))
  have hKρ : ∀ j y, ρ / 2 ^ j < ‖y‖ → b.dual L j y = 0 := fun j y hy => b.dual_eq_zero_of_lt L j hy
  refine ⟨d, ENNReal.ofReal (1 + Ω.M) * A1 * (((1 + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (d ^ finrank ℝ Ω.hyperplane) * volume (ball (0 : Ω.hyperplane) 1))) ^
        (1 / p.toReal), ⌈(2 * ρ' + 2) ^ finrank ℝ V⌉₊, hd, ?_, fun j h hh => ⟨fun m => ?_,
      fun x' S hS => ?_⟩⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA1)
      (ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one ENNReal.toReal_nonneg)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)))
  · have hK : ∀ y, ‖b.dual L j y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j := fun y => by
      simpa using hb 0 (Nat.zero_le 1) j 0 y
    refine Ω.isRegularAtom_comp_graphMap hd (continuous_cellAtom hp1 (b.continuous_dual L j)
      (b.hasCompactSupport_dual L j) hh j m) (fun x hx => cellAtom_eq_zero (hKρ j) m hx)
      (fun x => ?_) (fun v x => ?_)
    · refine (enorm_cellAtom_le hp1 hh m hK hρ (hKρ j) x).trans ?_
      have hXY : (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
          (1 - 1 / p.toReal) ≤ (ENNReal.ofReal ((ρ + 1) ^ finrank ℝ V) *
            volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal) :=
        ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ hρ (by linarith) _)) le_rfl) ht
      calc A * (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal)
          ≤ 1 * (A * (ENNReal.ofReal ((ρ + 1) ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
              (1 - 1 / p.toReal)) := by
            rw [one_mul]
            exact mul_le_mul' le_rfl hXY
        _ ≤ A1 := by
            simp only [A1]
            rw [mul_assoc]
            exact mul_le_mul' (by norm_num) le_rfl
    · have h1 := enorm_iterDiff_cellAtom_le hp1 (b.continuous_dual L j) hh m hK
        (hb 1 le_rfl j) hρ (hKρ j) v x
      rw [Nat.cast_one, ENNReal.rpow_one] at h1
      simpa only [Function.iterate_one, fwdDiff] using h1
  · refine card_le_of_norm_sub_cellCenter_le j hρ' (Ω.graphMap x') S fun m hm => ?_
    obtain ⟨hcoef, hdist⟩ := hS m hm
    have hex : ∃ y', cellAtom p (b.dual L j) j h m (Ω.graphMap y') ≠ 0 := by
      by_contra hcon
      exact hcoef (by simp [traceCoef, hcon])
    obtain ⟨y', hy'⟩ := hex
    have h1 : ‖Ω.graphMap y' - cellCenter j m‖ ≤ d / 2 ^ j :=
      not_lt.1 fun hlt => hy' (cellAtom_eq_zero (hKρ j) m hlt)
    have h2 : ‖y' - Ω.proj (cellCenter j m)‖ ≤ d / 2 ^ j := (Ω.norm_sub_proj_le y' _).trans h1
    have h3 : ‖x' - y'‖ ≤ (2 * d + 1) / 2 ^ j := by
      calc ‖x' - y'‖ = ‖(x' - Ω.proj (cellCenter j m)) - (y' - Ω.proj (cellCenter j m))‖ := by
            congr 1
            abel
        _ ≤ ‖x' - Ω.proj (cellCenter j m)‖ + ‖y' - Ω.proj (cellCenter j m)‖ := norm_sub_le _ _
        _ ≤ (d + 1) / 2 ^ j + d / 2 ^ j := add_le_add hdist h2
        _ = (2 * d + 1) / 2 ^ j := by ring
    calc ‖Ω.graphMap x' - cellCenter j m‖
        = ‖(Ω.graphMap x' - Ω.graphMap y') + (Ω.graphMap y' - cellCenter j m)‖ := by
          congr 1
          abel
      _ ≤ ‖Ω.graphMap x' - Ω.graphMap y'‖ + ‖Ω.graphMap y' - cellCenter j m‖ := norm_add_le _ _
      _ ≤ (1 + Ω.M) * ((2 * d + 1) / 2 ^ j) + d / 2 ^ j :=
          add_le_add ((Ω.norm_graphMap_sub_le x' y').trans
            (mul_le_mul_of_nonneg_left h3 (by linarith [Ω.M_nonneg]))) h1
      _ = ρ' / 2 ^ j := by
          simp only [ρ']
          ring

omit [MeasurableSpace V] [BorelSpace V] in
/-- `dim H = n - 1` as a real number. -/
theorem finrank_hyperplane_eq : (finrank ℝ Ω.hyperplane : ℝ) = finrank ℝ V - 1 := by
  have h := Ω.finrank_hyperplane_add_one
  rw [← h]
  push_cast
  ring

/-- **The traces of the terms are in `L_p(H)`**: `‖(η_j ⋆ h) ∘ γ‖_{L_p(H)} ≤ K 2^(j/p) ‖h‖_p`, by
the level sums of the trace atoms (`Rd.eLpNorm_levelSum_le` on `H`). -/
theorem eLpNorm_traceFun_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (L : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ j {h : V → ℂ}, MemLp h p volume →
      eLpNorm (Ω.traceFun b L j h) p (volume : Measure Ω.hyperplane) ≤
        K * dyadicWeight (1 / p.toReal) j * eLpNorm h p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨d, C, N, hd, hC, hatoms⟩ := Ω.exists_trace_atoms b hp1 L
  have hexp : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  refine ⟨(N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (ENNReal.natCast_ne_top N)) hC, fun j h hh => ?_⟩
  obtain ⟨hat, hN⟩ := hatoms j hh
  have hlev := eLpNorm_levelSum_le hp1 hp (fun m => Ω.proj (cellCenter j m))
    (fun m => cellAtom p (b.dual L j) j h m ∘ Ω.graphMap) (Ω.traceCoef b p L j h)
    (fun x' S hS => hN x' S fun m hm => ⟨(hS m hm).1, by simpa only [Nat.cast_one] using (hS m hm).2⟩)
    hat
    (Ω.continuous_traceFun b hp1 L j hh).aestronglyMeasurable
    (Eventually.of_forall (Ω.traceFun_eq_tsum b hp1 L j hh))
  refine hlev.trans ?_
  calc (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
        (C * dyadicWeight (-(finrank ℝ Ω.hyperplane / p.toReal)) j) *
        levelNorm p (Ω.traceCoef b p L j h)
      ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
          (C * dyadicWeight (-(finrank ℝ Ω.hyperplane / p.toReal)) j) *
          (dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm h p volume) :=
        mul_le_mul' le_rfl (Ω.levelNorm_traceCoef_le b hp0 hp L j hh)
    _ = (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C *
          (dyadicWeight (-(finrank ℝ Ω.hyperplane / p.toReal)) j *
            dyadicWeight (finrank ℝ V / p.toReal) j) * eLpNorm h p volume := by ring
    _ = (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C * dyadicWeight (1 / p.toReal) j *
          eLpNorm h p volume := by
        rw [← ENNReal.dyadicWeight_add, Ω.finrank_hyperplane_eq]
        congr 3
        ring

/-- The traces of the terms are in `L_p(H)`. -/
theorem memLp_traceFun {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (L j : ℕ) {h : V → ℂ}
    (hh : MemLp h p volume) : MemLp (Ω.traceFun b L j h) p (volume : Measure Ω.hyperplane) := by
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_traceFun_le b hp1 hp L
  exact memLp_iff.2 ((hle j hh).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK.lt_top (ENNReal.dyadicWeight_lt_top _ _))
      hh.eLpNorm_lt_top))

end Terms

/-! ### The trace of a series -/

section Series

variable (b : LocalMeansBump V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The trace of the `j`-th term `η_j ⋆ h` in `L_p(H)`. -/
noncomputable def traceTerm (hp : p ≠ ∞) (L j : ℕ) (h : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure Ω.hyperplane) :=
  (Ω.memLp_traceFun b Fact.out hp L j (Lp.memLp h)).toLp _

/-- The trace of a term agrees with `(η_j ⋆ h) ∘ γ` almost everywhere. -/
theorem traceTerm_ae (hp : p ≠ ∞) (L j : ℕ) (h : Lp ℂ p (volume : Measure V)) :
    Ω.traceTerm b hp L j h =ᵐ[volume] Ω.traceFun b L j h :=
  MemLp.coeFn_toLp _

/-- The **trace of a series** `∑_j η_j ⋆ h_j`: `∑_j (η_j ⋆ h_j) ∘ γ` in `L_p(H)`. -/
noncomputable def traceSeries (hp : p ≠ ∞) (L : ℕ) (h : ℕ → Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure Ω.hyperplane) :=
  ∑' j, Ω.traceTerm b hp L j (h j)

/-- **The trace series converges absolutely** for `s > 0` and
`X = ‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q} < ∞`: `‖(η_j ⋆ h_j) ∘ γ‖_{L_p(H)} ≤ K 2^(j/p) ‖h_j‖_p ≤
K X 2^(-js)`. -/
theorem summable_traceTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hX : lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞) :
    Summable fun j => Ω.traceTerm b hp L j (h j) := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_traceFun_le b hp1 hp L
  set X := lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ)
  have hterm : ∀ j, ‖Ω.traceTerm b hp L j (h j)‖ₑ ≤ K * X * dyadicWeight (-s) j := fun j => by
    have hXj : dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ ≤ X :=
      ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
        (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) j
    have hw : dyadicWeight (1 / p.toReal) j =
        dyadicWeight (s + 1 / p.toReal) j * dyadicWeight (-s) j := by
      rw [← ENNReal.dyadicWeight_add]
      congr 1
      ring
    rw [Lp.enorm_def, eLpNorm_congr_ae (Ω.traceTerm_ae b hp L j (h j))]
    refine (hle j (Lp.memLp (h j))).trans ?_
    rw [← Lp.enorm_def, hw]
    calc K * (dyadicWeight (s + 1 / p.toReal) j * dyadicWeight (-s) j) * ‖h j‖ₑ
        = K * (dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) * dyadicWeight (-s) j := by ring
      _ ≤ K * X * dyadicWeight (-s) j := by gcongr
  refine Summable.of_norm ?_
  have hfin : ∑' j, ‖Ω.traceTerm b hp L j (h j)‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hK hX.ne)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)
  simpa only [toReal_enorm] using ENNReal.summable_toReal hfin

/-- The partial sums of the trace series converge to it. -/
theorem tendsto_sum_traceTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hX : lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), Ω.traceTerm b hp L j (h j)) atTop
      (𝓝 (Ω.traceSeries b hp L h)) :=
  ((Ω.summable_traceTerm b hp L hs hq hX).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-- **The trace of a series** (Schneider–Vybíral, Theorem 4.2): for `0 < s < 1`
there is `K < ∞` such that the trace `Tr = ∑_j (η_j ⋆ h_j) ∘ γ` has
`‖Tr‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q}`,
by the atomic synthesis on `H` with the trace atoms. -/
theorem modNorm_traceSeries_le (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ h : ℕ → Lp ℂ p (volume : Measure V),
      lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞ →
      ‖Ω.traceSeries b hp L h‖ₑ +
          lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.traceSeries b hp L h) k) ≤
        K * lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨d, C, N, hd, hC, hatoms⟩ := Ω.exists_trace_atoms b hp1 L
  refine ⟨atomSynthConst p N C 1 s 1, atomSynthConst_ne_top hp1 N hC 1 hs hs1, fun h hX => ?_⟩
  have hsyn := modNorm_le_coeffNorm hp (fun j m => Ω.proj (cellCenter j m))
    (fun j m => cellAtom p (b.dual L j) j (h j) m ∘ Ω.graphMap)
    (fun j => Ω.traceCoef b p L j (h j))
    (fun j x' S hS => (hatoms j (Lp.memLp (h j))).2 x' S fun m hm =>
      ⟨(hS m hm).1, by simpa only [Nat.cast_one] using (hS m hm).2⟩)
    (fun j m => (hatoms j (Lp.memLp (h j))).1 m)
    (fun j => (Ω.traceTerm_ae b hp L j (h j)).mono fun x' hx' =>
      hx'.trans (Ω.traceFun_eq_tsum b hp1 L j (Lp.memLp (h j)) x'))
    (Ω.tendsto_sum_traceTerm b hp L hs hq hX) hs hs1 hq
  refine hsyn.trans (mul_le_mul' le_rfl ?_)
  rw [coeffNorm]
  refine ENNReal.lqNorm_mono fun j => ?_
  calc dyadicWeight (s - finrank ℝ Ω.hyperplane / p.toReal) j *
        levelNorm p (Ω.traceCoef b p L j (h j))
      ≤ dyadicWeight (s - finrank ℝ Ω.hyperplane / p.toReal) j *
          (dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm (h j) p volume) :=
        mul_le_mul' le_rfl (Ω.levelNorm_traceCoef_le b hp0 hp L j (Lp.memLp (h j)))
    _ = dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ := by
        rw [← mul_assoc, ← ENNReal.dyadicWeight_add, Lp.enorm_def, Ω.finrank_hyperplane_eq]
        congr 2
        ring

end Series

/-! ### The trace on a Lipschitz graph domain -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **trace** on the boundary of the Lipschitz graph domain `Ω`, a function on `H`:
`Tr f = ∑_j (η_j ⋆ 1_Ω (k_j ⋆ f)) ∘ γ` with the kernels of the cone bump; only `f` on `Ω`
enters. -/
noncomputable def trace (hp : p ≠ ∞) (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure Ω.hyperplane) :=
  Ω.traceSeries Ω.coneBump hp L fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)

/-- **The trace theorem on Lipschitz graph domains** (Schneider–Vybíral, Theorem 4.2,
for `p ≥ 1`): for `1 ≤ p < ∞`, `0 < s < 1` and `1 ≤ q ≤ ∞` there is `K < ∞` with
`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr f, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`. -/
theorem modNorm_trace_le (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      ‖Ω.cutoff f‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulusOn p Ω.domain L f k) < ∞ →
      ‖Ω.trace hp L f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.trace hp L f) k) ≤
        K * (‖Ω.cutoff f‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulusOn p Ω.domain L f k)) := by
  obtain ⟨K, hK, hle⟩ := Ω.modNorm_traceSeries_le Ω.coneBump hp L hs hs1 hq
  refine ⟨K * Ω.intrinsicConst L, ENNReal.mul_ne_top hK (Ω.intrinsicConst_ne_top L),
    fun f hf => ?_⟩
  have hX := Ω.intrinsicNorm_lt_top hp L (s + 1 / p.toReal) hq hf
  rw [mul_assoc]
  exact (hle (fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)) hX).trans
    (mul_le_mul' le_rfl (Ω.intrinsicNorm_le hp L (s + 1 / p.toReal) hq f))

/-! ### The trace of continuous functions -/

/-- **The partial sums of the trace at a boundary point**:
`∑_{j ≤ J} (η_j ⋆ 1_Ω (k_j ⋆ f))(γ x') = (m_{2^J} ⋆ (m_{2^J} ⋆ f))(γ x')`: at boundary points the
cut-off does not matter (the kernels are supported in `-K` and `γ x' + K ⊆ Ω`), and the partial
sums of the reproducing formula are `m_{2^J} ⋆ m_{2^J} ⋆ f` at every point. -/
theorem sum_traceFun_eq_conv (hp : p ≠ ∞) (L J : ℕ) (f : Lp ℂ p (volume : Measure V))
    (x' : Ω.hyperplane) :
    ∑ j ∈ Finset.range (J + 1),
        Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
      conv (Ω.coneBump.scaled L J) (convLp hp (Ω.coneBump.integrable_scaled L J) f) volume
        (Ω.graphMap x') := by
  have hcut : ∀ j, Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
      conv (Ω.coneBump.dual L j) (Ω.coneBump.localMean hp L j f) volume (Ω.graphMap x') :=
    fun j => by
      rw [traceFun, conv_congr_ae (Ω.cutoff_apply_ae _),
        conv_indicator_eq_of_forall _ (fun z hz => ?_) volume]
      rw [sub_eq_add_neg]
      exact Ω.graphMap_add_mem x' (Ω.coneSupported_dual L j z hz)
  simp_rw [hcut]
  rw [Ω.coneBump.sum_conv_dual_localMean_apply hp L J f]

/-- The partial sums of the trace for a representative `G` of `f`:
`(m_{2^J} ⋆ (m_{2^J} ⋆ G))(γ x')`. -/
theorem sum_traceFun_eq (hp : p ≠ ∞) (L J : ℕ) {f : Lp ℂ p (volume : Measure V)} {G : V → ℂ}
    (hfG : (f : V → ℂ) =ᵐ[volume] G) (x' : Ω.hyperplane) :
    ∑ j ∈ Finset.range (J + 1),
        Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
      conv (Ω.coneBump.scaled L J) (conv (Ω.coneBump.scaled L J) G volume) volume
        (Ω.graphMap x') := by
  rw [Ω.sum_traceFun_eq_conv hp L J f]
  have hG : ⇑(convLp hp (Ω.coneBump.integrable_scaled L J) f) =ᵐ[volume]
      conv (Ω.coneBump.scaled L J) G volume :=
    (convLp_apply_ae hp _ f).trans (Filter.EventuallyEq.of_eq (conv_congr_ae hfG))
  rw [conv_congr_ae hG]

/-- **The trace is an almost everywhere limit of mollified restrictions**: for a finite intrinsic
norm of smoothness `s + 1/p`, `s > 0`, a subsequence of `(m_{2^J} ⋆ (m_{2^J} ⋆ f))(γ x')` converges to
`Tr f(x')` for almost every `x'`, since the partial sums of the trace series converge in `L_p(H)`. -/
theorem exists_subseq_tendsto_trace (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hX : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f < ∞) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x' ∂(volume : Measure Ω.hyperplane),
      Tendsto (fun k => conv (Ω.coneBump.scaled L (ns k))
        (convLp hp (Ω.coneBump.integrable_scaled L (ns k)) f) volume (Ω.graphMap x')) atTop
          (𝓝 (Ω.trace hp L f x')) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hS := Ω.tendsto_sum_traceTerm Ω.coneBump hp L hs hq
    (h := fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)) hX
  have hSae : ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), ∀ J,
      (∑ j ∈ Finset.range (J + 1), Ω.traceTerm Ω.coneBump hp L j
        (Ω.cutoff (Ω.coneBump.localMean hp L j f))) x' =
      conv (Ω.coneBump.scaled L J) (convLp hp (Ω.coneBump.integrable_scaled L J) f) volume
        (Ω.graphMap x') := by
    rw [ae_all_iff]
    intro J
    have h1 := Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
      (fun j => Ω.traceTerm Ω.coneBump hp L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)))
    have h2 : ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), ∀ j,
        Ω.traceTerm Ω.coneBump hp L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' =
          Ω.traceFun Ω.coneBump L j (Ω.cutoff (Ω.coneBump.localMean hp L j f)) x' :=
      ae_all_iff.2 fun j => Ω.traceTerm_ae Ω.coneBump hp L j _
    filter_upwards [h1, h2] with x' hx1 hx2
    rw [hx1, ← Ω.sum_traceFun_eq_conv hp L J f x']
    exact Finset.sum_congr rfl fun j _ => hx2 j
  obtain ⟨ns, hns, hns_ae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hS)).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hSae, hns_ae] with x' hx1 hx2
  simp only [hx1] at hx2
  exact hx2

/-- **The trace of continuous functions**: if `f ∈ L_p(V)` has a continuous representative `G`
and a finite intrinsic `B^{s+1/p}_{p,q}`-norm on `Ω`, then `Tr f = G ∘ γ` almost everywhere on
`H`: the mollified restrictions converge at every point to `G(γ x')`
(`Rd.conv_dilate_near`, twice), and a subsequence converges almost everywhere to `Tr f`. -/
theorem trace_ae_eq_comp_graphMap (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : ‖Ω.cutoff f‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulusOn p Ω.domain L f k) < ∞)
    {G : V → ℂ} (hG : Continuous G) (hfG : (f : V → ℂ) =ᵐ[volume] G) :
    Ω.trace hp L f =ᵐ[volume] G ∘ Ω.graphMap := by
  obtain ⟨ns, hns, hae⟩ := Ω.exists_subseq_tendsto_trace hp L hs hq
    (Ω.intrinsicNorm_lt_top hp L (s + 1 / p.toReal) hq hf)
  have hΦ := integrable_momentKernel Ω.coneBump.integrable L
  have hone := integral_momentKernel Ω.coneBump.integrable Ω.coneBump.integral_eq_one hL
  have hR : 0 ≤ (L : ℝ) * Ω.coneBump.radius :=
    mul_nonneg (Nat.cast_nonneg L) Ω.coneBump.radius_nonneg
  have hΦR : ∀ w, L * Ω.coneBump.radius < ‖w‖ → momentKernel Ω.coneBump.toFun L w = 0 :=
    fun w hw => Ω.coneBump.momentKernel_eq_zero L hw
  have hlim : ∀ y : V, Tendsto (fun J => conv (Ω.coneBump.scaled L J)
      (conv (Ω.coneBump.scaled L J) G volume) volume y) atTop (𝓝 (G y)) := fun y => by
    have hG1 := conv_dilate_near hΦ hone hR hΦR (F := fun _ => G)
      (fun _ => hG.aestronglyMeasurable) (y := y) (z₀ := G y) fun ε hε => by
        obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hG.continuousAt ε hε
        exact ⟨0, δ, hδ, fun J _ z hz => by
          rw [← dist_eq_norm]
          exact hδG (by rwa [dist_eq_norm])⟩
    have hG2 := conv_dilate_near hΦ hone hR hΦR
      (F := fun J => conv (Ω.coneBump.scaled L J) G volume)
      (fun J => ((Ω.coneBump.hasCompactSupport_scaled L J).continuous_convolution_left
        (ContinuousLinearMap.mul ℂ ℂ) (Ω.coneBump.continuous_scaled L J)
          hG.locallyIntegrable).aestronglyMeasurable) hG1
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J₀, δ, hδ, hJ⟩ := hG2 ε hε
    exact ⟨J₀, fun J hJ0 => by
      rw [dist_eq_norm]
      exact hJ J hJ0 y (by simpa using hδ)⟩
  filter_upwards [hae] with x' hx
  refine tendsto_nhds_unique hx ?_
  have hJ : ∀ J, conv (Ω.coneBump.scaled L J) (convLp hp (Ω.coneBump.integrable_scaled L J) f)
      volume (Ω.graphMap x') = conv (Ω.coneBump.scaled L J)
        (conv (Ω.coneBump.scaled L J) G volume) volume (Ω.graphMap x') := fun J => by
    rw [conv_congr_ae ((convLp_apply_ae hp _ f).trans
      (Filter.EventuallyEq.of_eq (conv_congr_ae hfG)))]
  simp_rw [hJ]
  exact (hlim (Ω.graphMap x')).comp hns.tendsto_atTop

/-! ### Linearity and continuity of the trace -/

/-- The traces of the terms are linear in `h`. -/
theorem traceTerm_sub (b : LocalMeansBump V) (hp : p ≠ ∞) (L j : ℕ)
    (h₁ h₂ : Lp ℂ p (volume : Measure V)) :
    Ω.traceTerm b hp L j (h₁ - h₂) = Ω.traceTerm b hp L j h₁ - Ω.traceTerm b hp L j h₂ := by
  have hp1 : 1 ≤ p := Fact.out
  have hint : ∀ (h : Lp ℂ p (volume : Measure V)) (y : V),
      Integrable (fun z => b.dual L j z * h (y - z)) volume := fun h y => by
    simpa using integrable_translate_mul hp1 (b.continuous_dual L j) (b.hasCompactSupport_dual L j)
      (Lp.memLp h) 0 y
  refine Lp.ext ?_
  filter_upwards [Ω.traceTerm_ae b hp L j (h₁ - h₂), Ω.traceTerm_ae b hp L j h₁,
    Ω.traceTerm_ae b hp L j h₂, Lp.coeFn_sub (Ω.traceTerm b hp L j h₁)
      (Ω.traceTerm b hp L j h₂)] with x' hx hx₁ hx₂ hxs
  rw [hx, hxs, Pi.sub_apply, hx₁, hx₂, traceFun, traceFun, traceFun,
    conv_congr_ae (Lp.coeFn_sub h₁ h₂), conv_apply, conv_apply, conv_apply,
    ← integral_sub (hint h₁ _) (hint h₂ _)]
  congr 1
  funext z
  simp only [Pi.sub_apply]
  ring

/-- **The trace is linear** on the functions with a finite intrinsic norm of smoothness `> 1/p`. -/
theorem trace_sub (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f₁ f₂ : Lp ℂ p (volume : Measure V)}
    (h₁ : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f₁ < ∞)
    (h₂ : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f₂ < ∞) :
    Ω.trace hp L (f₁ - f₂) = Ω.trace hp L f₁ - Ω.trace hp L f₂ := by
  simp only [trace, traceSeries, map_sub]
  simp_rw [Ω.traceTerm_sub]
  exact Summable.tsum_sub (Ω.summable_traceTerm Ω.coneBump hp L hs hq
      (h := fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f₁)) h₁)
    (Ω.summable_traceTerm Ω.coneBump hp L hs hq
      (h := fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f₂)) h₂)

/-- **The trace in `L_p(H)` is bounded by the `B^{1/p}_{p,1}`-norm**:
`‖Tr f‖_{L_p(H)} ≤ K (‖f‖_p + ∑_k 2^(k/p) ω_L(f, 2^(-k))_p)`, by the bounds of the terms
(`Rd.LipschitzGraph.eLpNorm_traceFun_le`) and of the local means by the moduli. -/
theorem enorm_trace_le (hp : p ≠ ∞) (L : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      ‖Ω.trace hp L f‖ₑ ≤
        K * (‖f‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / p.toReal) k * lpModulus p L f k)) := by
  obtain ⟨K, hK, hle⟩ := Ω.eLpNorm_traceFun_le Ω.coneBump Fact.out hp L
  refine ⟨K * Ω.coneBump.upperConst L (1 / p.toReal),
    ENNReal.mul_ne_top hK (Ω.coneBump.upperConst_ne_top L _), fun f => ?_⟩
  calc ‖Ω.trace hp L f‖ₑ ≤ ∑' j, ‖Ω.traceTerm Ω.coneBump hp L j
        (Ω.cutoff (Ω.coneBump.localMean hp L j f))‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' j, K * (dyadicWeight (1 / p.toReal) j * ‖Ω.coneBump.localMean hp L j f‖ₑ) :=
        ENNReal.tsum_le_tsum fun j => by
          rw [Lp.enorm_def, eLpNorm_congr_ae (Ω.traceTerm_ae Ω.coneBump hp L j _)]
          refine (hle j (Lp.memLp _)).trans ?_
          rw [← Lp.enorm_def, mul_assoc]
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (Ω.enorm_cutoff_le _))
    _ = K * Ω.coneBump.localMeansNorm hp L (1 / p.toReal) 1 f := by
        rw [ENNReal.tsum_mul_left, LocalMeansBump.localMeansNorm, ENNReal.lqNorm_one]
    _ ≤ K * (Ω.coneBump.upperConst L (1 / p.toReal) * (‖f‖ₑ +
          lqNorm 1 (fun k => dyadicWeight (1 / p.toReal) k * lpModulus p L f k))) :=
        mul_le_mul' le_rfl (Ω.coneBump.localMeansNorm_le hp L _ le_rfl f)
    _ = _ := by ring

end LipschitzGraph

end Rd
