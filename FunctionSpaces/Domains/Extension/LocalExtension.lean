/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Extension.LipschitzGraphBesov

/-!
# Local extensions

Rychkov's construction works locally. Let `b` be a bump for local means with kernels `k_j`, dual
kernels `η_j` and radius `R ≤ 1/2`, and let `U ⊆ W` and `U ⊆ T` be measurable sets such that

* `x - y ∈ W` for `x ∈ U` and `y` in the support of a dual kernel (`η_j ⋆` at points of `U` only
  sees `W`), and
* `W ⊆ T_{L h}` for the steps `h = -c^(-1) z`, `c ≥ 1`, `b(z) ≠ 0` (the averaged differences of
  the moment kernels at points of `W` stay in `T`).

Then for `f ∈ L_p(V)` with `‖f‖_{L_p(T)} + ‖(2^(ks) ω_L(f, 2^(-k), T)_p)_k‖_{ℓ_q} < ∞` and
`0 < s < L`, the series `F = ∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` has a finite Besov quasi-norm on `V`
and `F = f` almost everywhere on `U` (`Rd.LocalMeansBump.exists_local_extension`). The proof is
that of Rychkov's extension (`Rd.LipschitzGraph.extension`), with the support principle for two
sets (`Rd.indicatorLp_convLp_indicatorLp`) and the moment kernel bound for two sets
(`Rd.eLpNorm_indicator_sub_convLp_momentKernel_le`).

Two kinds of patches satisfy the conditions:

* **boundary patches** of a Lipschitz graph domain `Ω`, `U = Ω ∩ B(c, ρ - 2ε)`,
  `W = Ω ∩ B(c, ρ - ε)`, `T = Ω ∩ B(c, ρ)`, for a bump supported in the reflected cone with
  `L R ≤ ε` (`Rd.LipschitzGraph.patch_support`, `Rd.LipschitzGraph.patch_step`);
* **interior patches** of an open set `O`, `U = {infDist(·, Oᶜ) > 2δ}`, `W = {infDist(·, Oᶜ) > δ}`,
  `T = O`, for any bump with `L R ≤ δ` (`Rd.interior_patch_support`, `Rd.interior_patch_step`);
  these sets lie in `O` (`Rd.setOf_lt_infDist_compl_subset`).

Short steps `-y ∈ K̄`, `‖y‖ ≤ ε`, take `Ω ∩ B(c, ρ - ε)` into `Ω ∩ B(c, ρ)`
(`Rd.LipschitzGraph.sub_mem_patch_of_mem_closedCone`); this gives the support conditions of all
cone-supported kernels of small support. The terms of the local extension are linear in `f`
(`Rd.LocalMeansBump.localExtTerm_add`, `Rd.LocalMeansBump.localExtTerm_smul`). A bound
`2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X < ∞` makes the local extension converge absolutely
(`Rd.LocalMeansBump.enorm_localExtTerm_le_of_forall_le`,
`Rd.LocalMeansBump.tsum_enorm_localExtTerm_le`,
`Rd.LocalMeansBump.summable_localExtTerm_of_forall_le`).

Bumps of every radius come from rescaling (`Rd.LocalMeansBump.rescale`) and from the normalised
smooth bump centred at `0` (`Rd.LocalMeansBump.centered`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The support principle for two sets -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **The support principle for two sets**: if `x - y ∈ W` whenever `k(y) ≠ 0`, then
`(k ⋆ 1_W f)(x) = (k ⋆ f)(x)`. -/
theorem conv_indicator_eq_of_forall {k : V → ℂ} {W : Set V} (f : V → ℂ) {x : V}
    (hx : ∀ y, k y ≠ 0 → x - y ∈ W) (μ : Measure V) :
    conv k (W.indicator f) μ x = conv k f μ x := by
  rw [conv_apply, conv_apply]
  congr 1
  funext y
  by_cases hy : k y = 0
  · simp [hy]
  · rw [Set.indicator_of_mem (hx y hy)]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The support principle for two sets on `L_p`**: `1_U (k ⋆ (1_W h)) = 1_U (k ⋆ h)` if
`x - y ∈ W` for `x ∈ U` and `k(y) ≠ 0`. -/
theorem indicatorLp_convLp_indicatorLp (hp : p ≠ ∞) {k : V → ℂ} (hk : Integrable k)
    {U W : Set V} (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUW : ∀ x ∈ U, ∀ y, k y ≠ 0 → x - y ∈ W) (h : Lp ℂ p (volume : Measure V)) :
    indicatorLp hU (convLp hp hk (indicatorLp hW h)) = indicatorLp hU (convLp hp hk h) := by
  refine Lp.ext ?_
  have h3 : conv k (indicatorLp hW h : V → ℂ) volume = conv k (W.indicator h) volume :=
    conv_congr_ae (indicatorLp_apply_ae hW h)
  filter_upwards [indicatorLp_apply_ae hU (convLp hp hk (indicatorLp hW h)),
    convLp_apply_ae hp hk (indicatorLp hW h), indicatorLp_apply_ae hU (convLp hp hk h),
    convLp_apply_ae hp hk h] with x hx1 hx2 hx4 hx5
  rw [hx1, hx4]
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hx2, hx5, h3,
      conv_indicator_eq_of_forall _ (hUW x hx) volume]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-! ### Bumps of every radius -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The **rescaled bump** `c^n b(c ·)`, of radius `R / c`. -/
noncomputable def rescale {c : ℝ} (hc : 0 < c) : LocalMeansBump V where
  toFun := Rd.dilate c b.toFun
  radius := b.radius / c
  radius_nonneg := div_nonneg b.radius_nonneg hc.le
  contDiff := contDiff_const.mul (b.contDiff.comp (contDiff_const_smul c))
  eq_zero z hz := by
    have hz' : b.radius < ‖c • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc.le]
      rwa [div_lt_iff₀ hc, mul_comm] at hz
    simp only [Rd.dilate, b.eq_zero _ hz', mul_zero]
  integral_eq_one := by rw [integral_dilate _ hc, b.integral_eq_one]

/-- The rescaled bump has radius `R / c`. -/
theorem rescale_radius {c : ℝ} (hc : 0 < c) : (b.rescale hc).radius = b.radius / c := rfl

/-- The dilated moment kernels vanish outside the ball of radius `L R`. -/
theorem scaled_eq_zero (L j : ℕ) {y : V} (hy : L * b.radius < ‖y‖) : b.scaled L j y = 0 := by
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have hy' : L * b.radius < ‖(2 : ℝ) ^ j • y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (L : ℝ) * b.radius < ‖y‖ := hy
      _ ≤ 2 ^ j * ‖y‖ := le_mul_of_one_le_left (norm_nonneg y) h1
  simp only [scaled, Rd.dilate, b.momentKernel_eq_zero L hy', mul_zero]

/-- The dual kernels vanish outside the ball of radius `L R`. -/
theorem dual_eq_zero (L j : ℕ) {y : V} (hy : L * b.radius < ‖y‖) : b.dual L j y = 0 := by
  cases j with
  | zero => exact b.scaled_eq_zero L 0 hy
  | succ j =>
    show b.scaled L (j + 1) y + b.scaled L j y = 0
    rw [b.scaled_eq_zero L _ hy, b.scaled_eq_zero L _ hy, add_zero]

/-- The local means kernels vanish outside the ball of radius `L R`. -/
theorem kernel_eq_zero (L j : ℕ) {y : V} (hy : L * b.radius < ‖y‖) : b.kernel L j y = 0 := by
  cases j with
  | zero => exact b.scaled_eq_zero L 0 hy
  | succ j =>
    show b.scaled L (j + 1) y - b.scaled L j y = 0
    rw [b.scaled_eq_zero L _ hy, b.scaled_eq_zero L _ hy, sub_zero]

end LocalMeansBump

/-! ### Kernels supported in the reflected cone -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The moment kernels of a bump supported in `-K` are supported in `-K`. -/
theorem coneSupported_momentKernel_of {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun)
    (L : ℕ) : Ω.ConeSupported (momentKernel b.toFun L) :=
  ConeSupported.finsetSum _ _ fun _ _ => hb.dilate (by positivity)

/-- The dilated moment kernels of a bump supported in `-K` are supported in `-K`. -/
theorem coneSupported_scaled_of {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun)
    (L j : ℕ) : Ω.ConeSupported (b.scaled L j) :=
  (Ω.coneSupported_momentKernel_of hb L).dilate (by positivity)

/-- The dual kernels of a bump supported in `-K` are supported in `-K`. -/
theorem coneSupported_dual_of {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun)
    (L j : ℕ) : Ω.ConeSupported (b.dual L j) := by
  cases j with
  | zero => exact Ω.coneSupported_scaled_of hb L 0
  | succ j => exact (Ω.coneSupported_scaled_of hb L (j + 1)).add (Ω.coneSupported_scaled_of hb L j)

/-- Rescaled bumps supported in `-K` are supported in `-K`. -/
theorem coneSupported_rescale {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun) {c : ℝ}
    (hc : 0 < c) : Ω.ConeSupported (b.rescale hc).toFun :=
  hb.dilate hc

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Short steps into the reflected closed cone stay in a patch**: if `x ∈ Ω ∩ B(c, ρ - ε)`,
`-y ∈ K̄` and `‖y‖ ≤ ε`, then `x - y ∈ Ω ∩ B(c, ρ)` (`Rd.LipschitzGraph.add_mem_of_mem_closedCone`
and the triangle inequality). -/
theorem sub_mem_patch_of_mem_closedCone {ε ρ : ℝ} {c x y : V}
    (hx : x ∈ Ω.domain ∩ ball c (ρ - ε)) (hy : -y ∈ Ω.closedCone) (hyR : ‖y‖ ≤ ε) :
    x - y ∈ Ω.domain ∩ ball c ρ := by
  obtain ⟨hxΩ, hxc⟩ := hx
  refine ⟨by simpa [sub_eq_add_neg] using Ω.add_mem_of_mem_closedCone hxΩ hy, ?_⟩
  rw [mem_ball] at hxc ⊢
  calc dist (x - y) c ≤ dist x c + ‖y‖ := by
        rw [dist_eq_norm, dist_eq_norm, sub_right_comm]
        exact norm_sub_le _ _
    _ < ρ - ε + ε := by linarith
    _ = ρ := by ring

/-- **Boundary patches, the support condition**: for a bump supported in `-K` with `L R ≤ ε`, the
dual kernels at points of `Ω ∩ B(c, ρ - 2ε)` only see `Ω ∩ B(c, ρ - ε)`
(`Rd.LipschitzGraph.sub_mem_patch_of_mem_closedCone`). -/
theorem patch_support {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun) {L : ℕ} {ε ρ : ℝ}
    {c : V} (hLR : L * b.radius ≤ ε) :
    ∀ x ∈ Ω.domain ∩ ball c (ρ - 2 * ε), ∀ j y, b.dual L j y ≠ 0 →
      x - y ∈ Ω.domain ∩ ball c (ρ - ε) := by
  intro x hx j y hy
  have hyR : ‖y‖ ≤ L * b.radius := not_lt.1 fun h => hy (b.dual_eq_zero L j h)
  rw [show ρ - 2 * ε = ρ - ε - ε by ring] at hx
  exact Ω.sub_mem_patch_of_mem_closedCone hx
    (Ω.cone_subset_closedCone (Ω.coneSupported_dual_of hb L j y hy)) (hyR.trans hLR)

/-- **Boundary patches, the step condition**: for a bump supported in `-K` with `L R ≤ ε`, the steps
`-c'^(-1) z`, `c' ≥ 1`, `b(z) ≠ 0`, take `Ω ∩ B(c, ρ - ε)` into `Ω ∩ B(c, ρ)`. -/
theorem patch_step {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun) {L : ℕ} {ε ρ : ℝ}
    {c : V} (hLR : L * b.radius ≤ ε) :
    ∀ c' : ℝ, 1 ≤ c' → ∀ z, b.toFun z ≠ 0 →
      Ω.domain ∩ ball c (ρ - ε) ⊆ stepSet (Ω.domain ∩ ball c ρ) L (-c'⁻¹ • z) := by
  intro c' hc' z hz x ⟨hxΩ, hxc⟩ l hl
  have hc0 : 0 < c' := zero_lt_one.trans_le hc'
  have hzK : -z ∈ Ω.cone := hb z hz
  have hzR : ‖z‖ ≤ b.radius := not_lt.1 fun h => hz (b.eq_zero z h)
  have hh : -c'⁻¹ • z = c'⁻¹ • -z := by rw [neg_smul, smul_neg]
  have hnorm : ‖(l : ℝ) • (-c'⁻¹ • z)‖ ≤ L * b.radius := by
    rw [norm_smul, norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hc0.le,
      Real.norm_of_nonneg (Nat.cast_nonneg l)]
    have hl' : (l : ℝ) ≤ L := by exact_mod_cast hl
    have hinv : c'⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc'
    calc (l : ℝ) * (c'⁻¹ * ‖z‖) ≤ L * (1 * b.radius) := by
          gcongr
      _ = L * b.radius := by ring
  refine ⟨?_, ?_⟩
  · rw [hh]
    exact Ω.add_nsmul_mem hxΩ (Ω.smul_mem_cone (inv_pos.2 hc0) hzK) l
  · rw [mem_ball] at hxc ⊢
    calc dist (x + (l : ℝ) • (-c'⁻¹ • z)) c ≤ dist x c + ‖(l : ℝ) • (-c'⁻¹ • z)‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ < ρ - ε + ε := by linarith
      _ = ρ := by ring

end LipschitzGraph

/-! ### Interior patches -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Points at distance more than `r ≥ 0` from the complement of `s` lie in `s`. -/
theorem setOf_lt_infDist_compl_subset (s : Set V) {r : ℝ} (hr : 0 ≤ r) :
    {x : V | r < infDist x sᶜ} ⊆ s := fun x hx => by
  by_contra h
  have h0 : infDist x sᶜ = 0 := infDist_zero_of_mem h
  simp only [Set.mem_ofPred_eq] at hx
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Interior patches, the support condition**: if the dual kernels vanish outside the ball of
radius `δ`, they see `{infDist(·, Oᶜ) > δ}` from points of `{infDist(·, Oᶜ) > 2δ}`. -/
theorem interior_patch_support (O : Set V) {k : V → ℂ} {δ : ℝ} (hk : ∀ y, k y ≠ 0 → ‖y‖ ≤ δ) :
    ∀ x ∈ {x : V | 2 * δ < infDist x Oᶜ}, ∀ y, k y ≠ 0 → x - y ∈ {x : V | δ < infDist x Oᶜ} := by
  intro x hx y hy
  have h := infDist_le_infDist_add_dist (s := Oᶜ) (x := x) (y := x - y)
  rw [dist_eq_norm, sub_sub_cancel] at h
  simp only [Set.mem_ofPred_eq] at hx ⊢
  linarith [hk y hy]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Interior patches, the step condition**: steps of length at most `δ / L` take
`{infDist(·, Oᶜ) > δ}` into `O_{L h}`. -/
theorem interior_patch_step (O : Set V) {L : ℕ} {δ : ℝ} {h : V} (hh : L * ‖h‖ ≤ δ) :
    {x : V | δ < infDist x Oᶜ} ⊆ stepSet O L h := by
  intro x hx l hl
  by_contra hmem
  have h1 : infDist x Oᶜ ≤ dist x (x + (l : ℝ) • h) := infDist_le_dist_of_mem hmem
  have hl' : (l : ℝ) ≤ L := by exact_mod_cast hl
  have h2 : dist x (x + (l : ℝ) • h) ≤ δ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg (Nat.cast_nonneg l)]
    exact (mul_le_mul_of_nonneg_right hl' (norm_nonneg h)).trans hh
  simp only [Set.mem_ofPred_eq] at hx
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The sets `{infDist(·, Oᶜ) > δ}` are measurable. -/
theorem measurableSet_infDist_gt (O : Set V) (δ : ℝ) :
    MeasurableSet {x : V | δ < infDist x Oᶜ} :=
  (isOpen_lt continuous_const (continuous_infDist_pt _)).measurableSet

/-! ### The local extension -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The **local means quasi-norm on a set** `‖(2^(js) ‖1_W (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
noncomputable def localNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ) (s : ℝ)
    (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ)

/-- The terms `η_j ⋆ 1_W (k_j ⋆ f)` of the local extension. -/
noncomputable def localExtTerm (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) : Lp ℂ p (volume : Measure V) :=
  convLp hp (b.integrable_dual L j) (indicatorLp hW (b.localMean hp L j f))

/-- The terms of the local extension are additive in `f`. -/
theorem localExtTerm_add (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L j : ℕ)
    (f g : Lp ℂ p (volume : Measure V)) :
    b.localExtTerm hp hW L j (f + g) = b.localExtTerm hp hW L j f + b.localExtTerm hp hW L j g := by
  simp only [localExtTerm, map_add]

/-- The terms of the local extension commute with complex scalars. -/
theorem localExtTerm_smul (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L j : ℕ) (c : ℂ)
    (f : Lp ℂ p (volume : Measure V)) :
    b.localExtTerm hp hW L j (c • f) = c • b.localExtTerm hp hW L j f := by
  simp only [localExtTerm, map_smul]

/-- The **local extension** `∑_j η_j ⋆ 1_W (k_j ⋆ f)`. -/
noncomputable def localExtension (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    (f : Lp ℂ p (volume : Measure V)) : Lp ℂ p (volume : Measure V) :=
  ∑' j, b.localExtTerm hp hW L j f

/-- **The terms of the local extension from a bound on the weighted local means**: if
`2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X` for every `j`, then `‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 2^(-js) X`. -/
theorem enorm_localExtTerm_le_of_forall_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} {f : Lp ℂ p (volume : Measure V)} {X : ℝ≥0∞}
    (hX : ∀ j, dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ X) (j : ℕ) :
    ‖b.localExtTerm hp hW L j f‖ₑ ≤
      2 * eLpNorm (momentKernel b.toFun L) 1 volume * (dyadicWeight (-s) j * X) :=
  calc ‖b.localExtTerm hp hW L j f‖ₑ
      ≤ eLpNorm (b.dual L j) 1 volume * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ :=
        enorm_convLp_le hp _ _
    _ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume * (dyadicWeight (-s) j *
          (dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ)) := by
        rw [← mul_assoc (dyadicWeight (-s) j), ENNReal.dyadicWeight_neg_mul_self, one_mul]
        exact mul_le_mul' (b.eLpNorm_dual_one_le L j) le_rfl
    _ ≤ _ := by gcongr; exact hX j

/-- **The sum of the norms of the terms**: if `2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X` for every `j`, then
`∑_j ‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 (1 - 2^(-s))⁻¹ X`
(`Rd.LocalMeansBump.enorm_localExtTerm_le_of_forall_le`, `ENNReal.tsum_dyadicWeight_neg`). -/
theorem tsum_enorm_localExtTerm_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} {f : Lp ℂ p (volume : Measure V)} {X : ℝ≥0∞}
    (hX : ∀ j, dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ X) :
    ∑' j, ‖b.localExtTerm hp hW L j f‖ₑ ≤
      2 * eLpNorm (momentKernel b.toFun L) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
  refine (ENNReal.tsum_le_tsum (b.enorm_localExtTerm_le_of_forall_le hp hW L hX)).trans_eq ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_dyadicWeight_neg]
  ring

/-- **The local extension converges absolutely** for `s > 0` if
`2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X < ∞` for every `j`
(`Rd.LocalMeansBump.tsum_enorm_localExtTerm_le`). -/
theorem summable_localExtTerm_of_forall_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} (hs : 0 < s) {f : Lp ℂ p (volume : Measure V)} {X : ℝ≥0∞} (hXf : X ≠ ∞)
    (hX : ∀ j, dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ X) :
    Summable fun j => b.localExtTerm hp hW L j f := by
  have htsum : ∑' j, ‖b.localExtTerm hp hW L j f‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (memLp_one_iff_integrable.2 (integrable_momentKernel b.integrable L)).eLpNorm_ne_top)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)) hXf) (b.tsum_enorm_localExtTerm_le hp hW L hX)
  exact Summable.of_norm (by simpa using ENNReal.summable_toReal htsum)

/-- **The local extension converges absolutely** for `s > 0` and a finite local means
quasi-norm on `W`: `‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 2^(-js) ‖f‖_W`
(`Rd.LocalMeansBump.summable_localExtTerm_of_forall_le`). -/
theorem summable_localExtTerm (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ) {s : ℝ}
    (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.localNormOn hp hW L s q f < ∞) : Summable fun j => b.localExtTerm hp hW L j f :=
  b.summable_localExtTerm_of_forall_le hp hW L hs hf.ne fun j =>
    ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
      (fun j => dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ) j

/-- The partial sums of the local extension converge to it if its terms are summable. -/
theorem tendsto_sum_localExtTerm_of_summable (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {f : Lp ℂ p (volume : Measure V)}
    (hsum : Summable fun j => b.localExtTerm hp hW L j f) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), b.localExtTerm hp hW L j f) atTop
      (𝓝 (b.localExtension hp hW L f)) :=
  (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-- The partial sums of the local extension converge to it. -/
theorem tendsto_sum_localExtTerm (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.localNormOn hp hW L s q f < ∞) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), b.localExtTerm hp hW L j f) atTop
      (𝓝 (b.localExtension hp hW L f)) :=
  b.tendsto_sum_localExtTerm_of_summable hp hW L (b.summable_localExtTerm hp hW L hs hq hf)

/-- **The local extension satisfies the Besov condition by differences**: for `0 < s`,
`‖F‖_p + ‖(2^(is) ω_L(F, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖1_W (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
theorem modNorm_localExtension_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.localNormOn hp hW L s q f < ∞) :
    ‖b.localExtension hp hW L f‖ₑ +
        lqNorm q (fun i => dyadicWeight s i * lpModulus p L (b.localExtension hp hW L f) i) ≤
      b.synthConst L s * b.localNormOn hp hW L s q f :=
  b.modNorm_le_of_tendsto hp L s hq (b.tendsto_sum_localExtTerm hp hW L hs hq hf)

/-- **The local extension agrees with `f` on `U`** if its terms are summable and the dual kernels
at points of `U` only see `W`: on `U` the terms are those of the reproducing formula. -/
theorem indicatorLp_localExtension_of_summable (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W) {f : Lp ℂ p (volume : Measure V)}
    (hsum : Summable fun j => b.localExtTerm hp hW L j f) :
    indicatorLp hU (b.localExtension hp hW L f) = indicatorLp hU f := by
  have hsum' : ∀ J, indicatorLp hU (∑ j ∈ Finset.range (J + 1), b.localExtTerm hp hW L j f) =
      indicatorLp hU (∑ j ∈ Finset.range (J + 1),
        convLp hp (b.integrable_dual L j) (b.localMean hp L j f)) := fun J => by
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      indicatorLp_convLp_indicatorLp hp _ hU hW (fun x hx y hy => hUW x hx j y hy) _
  have h1 : Tendsto (fun J => indicatorLp hU (∑ j ∈ Finset.range (J + 1),
      b.localExtTerm hp hW L j f)) atTop (𝓝 (indicatorLp hU (b.localExtension hp hW L f))) :=
    ((indicatorLp hU).continuous.tendsto _).comp
      (b.tendsto_sum_localExtTerm_of_summable hp hW L hsum)
  have h2 : Tendsto (fun J => indicatorLp hU (∑ j ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L j) (b.localMean hp L j f))) atTop (𝓝 (indicatorLp hU f)) :=
    ((indicatorLp hU).continuous.tendsto _).comp (b.tendsto_sum_dual_localMean hp hL f)
  simp_rw [hsum'] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The local extension agrees with `f` on `U`** if the dual kernels at points of `U` only see
`W`: on `U` the terms are those of the reproducing formula. -/
theorem indicatorLp_localExtension (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} (hf : b.localNormOn hp hW L s q f < ∞) :
    indicatorLp hU (b.localExtension hp hW L f) = indicatorLp hU f :=
  b.indicatorLp_localExtension_of_summable hp hL hU hW hUW
    (b.summable_localExtTerm hp hW L hs hq hf)

/-! ### Local means and moduli on a set -/

/-- `‖1_W (k_0 ⋆ f)‖_p ≤ ‖m‖_1 ‖f‖_p`. -/
theorem enorm_indicatorLp_localMean_zero_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ‖indicatorLp hW (b.localMean hp L 0 f)‖ₑ ≤
      eLpNorm (momentKernel b.toFun L) 1 volume * ‖f‖ₑ :=
  (enorm_indicatorLp_le hW _).trans (b.enorm_localMean_zero_le hp L f)

/-- **The local means on `W` are bounded by the moduli on `T`**:
`‖(2^(js) ‖1_W (k_j ⋆ f)‖_p)_j‖_{ℓ_q} ≤
(‖m‖_1 + 2 ‖g‖_1) (‖f‖_p + ‖(2^(js) ω_L(f, 2^(-j), T)_p)_j‖_{ℓ_q})`. -/
theorem localNormOn_le (hp : p ≠ ∞) {W T : Set V} (hW : MeasurableSet W) (L : ℕ) (s : ℝ)
    {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hstep : ∀ c : ℝ, 1 ≤ c → ∀ z, b.toFun z ≠ 0 → W ⊆ stepSet T L (-c⁻¹ • z))
    (hR : b.radius ≤ 1 / 2) (f : Lp ℂ p (volume : Measure V)) :
    b.localNormOn hp hW L s q f ≤
      (eLpNorm (momentKernel b.toFun L) 1 volume + 2 * ∫⁻ z, ‖b.toFun z‖ₑ) *
        (‖f‖ₑ + lqNorm q (fun j => dyadicWeight s j * lpModulusOn p T L f j)) := by
  set A := ∫⁻ z, ‖b.toFun z‖ₑ
  set M := eLpNorm (momentKernel b.toFun L) 1 volume
  set Λ := lqNorm q (fun j => dyadicWeight s j * lpModulusOn p T L f j)
  have htail : lqNorm q (fun j => dyadicWeight s (j + 1) *
      ‖indicatorLp hW (b.localMean hp L (j + 1) f)‖ₑ) ≤ 2 * A * Λ :=
    calc lqNorm q (fun j => dyadicWeight s (j + 1) *
          ‖indicatorLp hW (b.localMean hp L (j + 1) f)‖ₑ)
        ≤ lqNorm q (fun j => 2 * A *
            (dyadicWeight s (j + 1) * lpModulusOn p T L f (j + 1))) :=
          ENNReal.lqNorm_mono fun j =>
            (mul_le_mul' le_rfl (b.enorm_indicatorLp_localMean_succ_le hp hW L j hstep hR f)).trans_eq
              (by ring)
      _ = 2 * A * lqNorm q (fun j => dyadicWeight s (j + 1) * lpModulusOn p T L f (j + 1)) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ 2 * A * Λ := mul_le_mul' le_rfl
          (ENNReal.lqNorm_shift_le fun j => dyadicWeight s j * lpModulusOn p T L f j)
  calc b.localNormOn hp hW L s q f
      ≤ dyadicWeight s 0 * ‖indicatorLp hW (b.localMean hp L 0 f)‖ₑ +
          lqNorm q (fun j => dyadicWeight s (j + 1) *
            ‖indicatorLp hW (b.localMean hp L (j + 1) f)‖ₑ) :=
        ENNReal.lqNorm_le_head_add_shift hq _
    _ ≤ M * ‖f‖ₑ + 2 * A * Λ := by
        rw [ENNReal.dyadicWeight_zero_right, one_mul]
        exact add_le_add (b.enorm_indicatorLp_localMean_zero_le hp hW L f) htail
    _ ≤ (M + 2 * A) * ‖f‖ₑ + (M + 2 * A) * Λ := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = (M + 2 * A) * (‖f‖ₑ + Λ) := by ring

/-- **The local extension theorem**: let `U ⊆ W`, `U ⊆ T` be measurable sets such that the dual
kernels at points of `U` only see `W` and the steps take `W` into `T`, and let the bump have
radius `R ≤ 1/2`. For `1 ≤ p < ∞`, `0 < s < L`, `1 ≤ q ≤ ∞` and `f` with
`‖f‖_{L_p(T)} + ‖(2^(ks) ω_L(f, 2^(-k), T)_p)_k‖_{ℓ_q} < ∞` there is `F` with a finite Besov
quasi-norm by differences on `V` and `F = f` almost everywhere on `U`. -/
theorem exists_local_extension (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {U W T : Set V} (hU : MeasurableSet U)
    (hW : MeasurableSet W) (hT : MeasurableSet T) (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W)
    (hstep : ∀ c : ℝ, 1 ≤ c → ∀ z, b.toFun z ≠ 0 → W ⊆ stepSet T L (-c⁻¹ • z))
    (hR : b.radius ≤ 1 / 2) (f : Lp ℂ p (volume : Measure V))
    (hf : ‖indicatorLp hT f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p T L f k) <
      ∞) :
    ∃ F : Lp ℂ p (volume : Measure V),
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L F k) < ∞ ∧
        indicatorLp hU F = indicatorLp hU f := by
  set f' := indicatorLp hT f
  have hae : T.indicator f' =ᵐ[volume] T.indicator f := by
    filter_upwards [indicatorLp_apply_ae hT f] with x hx
    by_cases hxT : x ∈ T
    · rw [Set.indicator_of_mem hxT, Set.indicator_of_mem hxT, hx, Set.indicator_of_mem hxT]
    · rw [Set.indicator_of_notMem hxT, Set.indicator_of_notMem hxT]
  have hmod : ∀ k, lpModulusOn p T L f' k = lpModulusOn p T L f k := fun k =>
    lpModulusOn_congr hae L k
  have hfin : b.localNormOn hp hW L s q f' < ∞ := by
    refine (b.localNormOn_le hp hW L s hq hstep hR f').trans_lt (ENNReal.mul_lt_top ?_ ?_)
    · exact (ENNReal.add_ne_top.2
        ⟨(memLp_one_iff_integrable.2 (integrable_momentKernel b.integrable L)).eLpNorm_ne_top,
          ENNReal.mul_ne_top (by norm_num) b.integrable.2.ne⟩).lt_top
    · simp_rw [hmod]
      exact hf
  refine ⟨b.localExtension hp hW L f', (b.modNorm_localExtension_le hp hW L hs hq hfin).trans_lt
    (ENNReal.mul_lt_top (b.synthConst_ne_top hs hsL).lt_top hfin), ?_⟩
  rw [b.indicatorLp_localExtension hp hL hU hW hUW hs hq hfin]
  refine Lp.ext ?_
  filter_upwards [indicatorLp_apply_ae hU f', indicatorLp_apply_ae hU f,
    indicatorLp_apply_ae hT f] with x h1 h2 h3
  rw [h1, h2]
  by_cases hxU : x ∈ U
  · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, h3, Set.indicator_of_mem (hUT hxU)]
  · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]

end LocalMeansBump

end Rd
