/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Traces.BoundaryGagliardo

/-!
# The Hilbert space `H^t(Γ)` and the trace onto `H^{s-1/2}(Γ)`

Let `Ω` be a bounded Lipschitz domain in `V`, `dim V = n`, with boundary `Γ`, surface measure `σ`,
charts `γ_j : H_j → V` and a resolution of unity `(ψ_j)` on `Γ`.

* **The Hilbert space `H^t(Γ)`** (`Rd.BoundedLipschitzDomain.BoundarySobolev`), `0 < t < 1`:
  `B^t_{2,2}(Γ)` with the chart-wise Gagliardo norm
  `‖g‖²_{L_2(Γ)} + ∑_j ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t) dy' dx'` of the
  chart pieces `G_j = (ψ_j g) ∘ γ_j`, the norm of the injective linear map
  `g ↦ (g, (G_j(y') - G_j(x'))_j)` into a Hilbert space built from the Gagliardo measures
  `Rd.gagliardoMeasure` on `H_j × H_j` (`Rd.BoundedLipschitzDomain.gagliardoEmbedding`), which
  gives the inner product. It is isomorphic to `B^t_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`), complete, its dual
  `H^{-t}(Γ)` is identified with it by Riesz
  (`Rd.BoundedLipschitzDomain.dualBoundarySobolevEquiv`), and its norm is equivalent to
  Gagliardo's norm with the surface measure
  (`Rd.BoundedLipschitzDomain.exists_boundarySobolev_norm_equiv_slobodeckij`).
* **The trace onto `H^{s-1/2}(Γ)`**, `1/2 < s < 3/2` (McLean, Theorem 3.38): the trace space of
  `H^s(Ω)` is isomorphic to `H^{s-1/2}(Γ)`
  (`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev`; for `s = 1` with values in
  `H^{1/2}(Γ)`, `Rd.BoundedLipschitzDomain.traceSpaceOneEquivBoundarySobolevHalf`); the trace
  `H^s(Ω) → H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.sobolevTrace`) is bounded with kernel
  `ker γ_s` and the bounded linear right inverse `Rd.BoundedLipschitzDomain.sobolevExtend`, and it
  is the Besov trace of `B^s_{2,2}(Ω)` at `p = q = 2`
  (`Rd.BoundedLipschitzDomain.toLp_sobolevTrace_eq_besovTrace`).

The constants depend on `Ω`, `t` and `s` and are fixed before the functions. The results
hold in every dimension `n ≥ 1`.
-/

@[expose] public section

open MeasureTheory Filter Metric Module Set
open scoped ENNReal InnerProductSpace BesselPotentialSpace

open ENNReal (lqNorm dyadicWeight)

namespace Rd

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : BoundedLipschitzDomain V)

/-! ### The Hilbert space `H^t(Γ)` -/

/-- **The pair differences of a chart piece lie in `L_2` of the Gagliardo measure**: for `t > 0`,
`g ∈ B^t_{2,2}(Γ)` and its chart piece `G_j = (ψ_j g) ∘ γ_j` on `H_j` for the canonical
resolution of unity, `(x', y') ↦ G_j(y') - G_j(x')` lies in `L_2(H_j × H_j)` for
`Rd.gagliardoMeasure`: its square norm is the Gagliardo form of `G_j`
(`Rd.eLpNorm_sub_sq_gagliardoMeasure`), finite by the bound by the first-difference norm
(`Rd.slobodeckijForm_le`) and `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_chartPieceLp`. -/
theorem memLp_chartPiece_sub (j : Fin Ω.N) {t : ℝ} (ht : 0 < t) (g : Ω.BoundaryBesov 2 t 2) :
    MemLp (fun z : (Ω.graph j).hyperplane × (Ω.graph j).hyperplane =>
      (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ) z.2 -
        (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ) z.1) 2
      (gagliardoMeasure (Ω.graph j).hyperplane t) := by
  set G := Ω.chartPieceLp Ω.boundaryPartition j g.toLp
  have hG : Measurable (G : (Ω.graph j).hyperplane → ℂ) := (Lp.stronglyMeasurable G).measurable
  refine memLp_iff.2 ?_
  have hfin := (Ω.memBoundaryBesov_iff_chartPieceLp _ t 2 g.toLp).1 g.mem j
  have hS := slobodeckijForm_le two_ne_top ht G
  rw [ENNReal.toReal_ofNat] at hS
  have hlt : slobodeckijForm 2 t (G : (Ω.graph j).hyperplane → ℂ) < ∞ := by
    refine hS.trans_lt (ENNReal.mul_lt_top (slobodeckijConstLower_ne_top two_ne_zero
      ENNReal.ofNat_ne_top ht).lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.1 hfin).2.ne
  rw [← eLpNorm_sub_sq_gagliardoMeasure t hG] at hlt
  exact (ENNReal.pow_lt_top_iff.1 hlt).resolve_right two_ne_zero

/-- **The pair differences of the chart piece `j`** as a linear map
`δ_j : B^t_{2,2}(Γ) → L_2(H_j × H_j, |y' - x'|^(-(n-1+2t)) dx' dy')`,
`δ_j g = ((x', y') ↦ G_j(y') - G_j(x'))`
with the chart piece `G_j = (ψ_j g) ∘ γ_j` of the canonical resolution of unity
(`Rd.BoundedLipschitzDomain.memLp_chartPiece_sub`), for `t > 0`. Its square norm is the
Gagliardo form of `G_j` on `H_j` (`Rd.BoundedLipschitzDomain.enorm_chartGagliardoDiff_sq`). For
`t ≤ 0` the map is `0`, and the norm of `Rd.BoundedLipschitzDomain.BoundarySobolev t` is then the
norm of `L_2(Γ)`; that space is `H^t(Γ)` for `0 < t < 1`. -/
noncomputable def chartGagliardoDiff (j : Fin Ω.N) (t : ℝ) :
    Ω.BoundaryBesov 2 t 2 →ₗ[ℂ] Lp ℂ 2 (gagliardoMeasure (Ω.graph j).hyperplane t) :=
  if ht : 0 < t then
    { toFun g := (Ω.memLp_chartPiece_sub j ht g).toLp _
      map_add' g h := by
        rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
        have hadd : Ω.chartPieceLp Ω.boundaryPartition j (g + h).toLp =
            Ω.chartPieceLp Ω.boundaryPartition j g.toLp +
              Ω.chartPieceLp Ω.boundaryPartition j h.toLp := map_add _ _ _
        filter_upwards [ae_gagliardoMeasure t (hadd ▸ Lp.coeFn_add
          (Ω.chartPieceLp Ω.boundaryPartition j g.toLp)
          (Ω.chartPieceLp Ω.boundaryPartition j h.toLp))] with z hz
        simp only [Pi.add_apply, hz.1, hz.2]
        ring
      map_smul' c g := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
        have hsmul : Ω.chartPieceLp Ω.boundaryPartition j (c • g).toLp =
            c • Ω.chartPieceLp Ω.boundaryPartition j g.toLp := map_smul _ _ _
        filter_upwards [ae_gagliardoMeasure t (hsmul ▸ Lp.coeFn_smul c
          (Ω.chartPieceLp Ω.boundaryPartition j g.toLp))] with z hz
        simp only [Pi.smul_apply, smul_eq_mul, hz.1, hz.2]
        ring }
  else 0

/-- **The square norm of the pair differences is the Gagliardo form of the chart piece**: for
`t > 0` and `g ∈ B^t_{2,2}(Γ)`,
`‖δ_j g‖² = ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t) dy' dx'`, the Gagliardo form
`Rd.slobodeckijForm 2 t G_j` on the hyperplane `H_j` of dimension `n - 1`
(`Rd.eLpNorm_sub_sq_gagliardoMeasure`). -/
theorem enorm_chartGagliardoDiff_sq (j : Fin Ω.N) {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) :
    ‖Ω.chartGagliardoDiff j t g‖ₑ ^ 2 =
      slobodeckijForm 2 t (Ω.chartPieceLp Ω.boundaryPartition j g.toLp :
        (Ω.graph j).hyperplane → ℂ) := by
  rw [chartGagliardoDiff, dite_eq_left ht, LinearMap.coe_mk, AddHom.coe_mk, Lp.enorm_def,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  exact eLpNorm_sub_sq_gagliardoMeasure t (Lp.stronglyMeasurable _).measurable

/-- **The Gagliardo embedding** `g ↦ (g, (δ_j g)_j)` of `B^t_{2,2}(Γ)` into the Hilbert space
`L_2(Γ) × ∏_j L_2(H_j × H_j, |y' - x'|^(-(n-1+2t)) dx' dy')`, with the `L_2` norm on the product
(Mathlib's `WithLp 2`) and the pair differences `δ_j g` of the chart pieces
(`Rd.BoundedLipschitzDomain.chartGagliardoDiff`): a linear map, injective by its first component
(`Rd.BoundedLipschitzDomain.gagliardoEmbedding_injective`), whose square norm is
`‖g‖²_{L_2(Γ)}` plus the Gagliardo forms of the chart pieces
(`Rd.BoundedLipschitzDomain.enorm_sq_gagliardoEmbedding`). It defines the norm and the inner
product of `H^t(Γ)` (`Rd.BoundedLipschitzDomain.BoundarySobolev`). -/
noncomputable def gagliardoEmbedding (t : ℝ) : Ω.BoundaryBesov 2 t 2 →ₗ[ℂ]
    WithLp 2 (Ω.BoundaryL2 ×
      PiLp 2 fun j : Fin Ω.N => Lp ℂ 2 (gagliardoMeasure (Ω.graph j).hyperplane t)) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ
    (BoundaryBesov.toLpL : Ω.BoundaryBesov 2 t 2 →L[ℂ] Ω.BoundaryL2).toLinearMap.prod
      ((WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ
        LinearMap.pi fun j => Ω.chartGagliardoDiff j t)

/-- The Gagliardo embedding sends `g` to `(g, (δ_j g)_j)`. -/
theorem gagliardoEmbedding_apply (t : ℝ) (g : Ω.BoundaryBesov 2 t 2) :
    Ω.gagliardoEmbedding t g =
      WithLp.toLp 2 (g.toLp, WithLp.toLp 2 fun j => Ω.chartGagliardoDiff j t g) :=
  rfl

/-- The Gagliardo embedding is injective: its first component is `g ∈ L_2(Γ)`. -/
theorem gagliardoEmbedding_injective (t : ℝ) : Function.Injective (Ω.gagliardoEmbedding t) :=
  fun _ _ hgh => BoundaryBesov.ext (congrArg WithLp.fst hgh)

/-- **The square norm of the Gagliardo embedding**:
`‖(g, (δ_j g)_j)‖² = ‖g‖²_{L_2(Γ)} + ∑_j ‖δ_j g‖²` (Mathlib's `WithLp.prod_norm_sq_eq_of_L2`,
`PiLp.norm_sq_eq_of_L2`). -/
theorem sq_norm_gagliardoEmbedding (t : ℝ) (g : Ω.BoundaryBesov 2 t 2) :
    ‖Ω.gagliardoEmbedding t g‖ ^ 2 = ‖g.toLp‖ ^ 2 + ∑ j, ‖Ω.chartGagliardoDiff j t g‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, gagliardoEmbedding_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    PiLp.norm_sq_eq_of_L2]

/-- **The chart-wise Gagliardo norm**: for `t > 0` and `g ∈ B^t_{2,2}(Γ)`,
`‖(g, (δ_j g)_j)‖² = ‖g‖²_{L_2(Γ)} + ∑_j ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t)`
with the chart pieces `G_j = (ψ_j g) ∘ γ_j`
(`Rd.BoundedLipschitzDomain.sq_norm_gagliardoEmbedding`,
`Rd.BoundedLipschitzDomain.enorm_chartGagliardoDiff_sq`). -/
theorem enorm_sq_gagliardoEmbedding {t : ℝ} (ht : 0 < t) (g : Ω.BoundaryBesov 2 t 2) :
    ‖Ω.gagliardoEmbedding t g‖ₑ ^ 2 = ‖g.toLp‖ₑ ^ 2 + ∑ j, slobodeckijForm 2 t
      (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ) := by
  have h := congrArg ENNReal.ofReal (Ω.sq_norm_gagliardoEmbedding t g)
  rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun _ _ => by positivity),
    ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity] at h
  simp only [ENNReal.ofReal_pow, norm_nonneg, ofReal_norm] at h
  rw [h]
  simp only [Ω.enorm_chartGagliardoDiff_sq _ ht]

/-- **`L_2(Γ)` is bounded by the Gagliardo embedding**: `‖g‖_{L_2(Γ)} ≤ ‖Φ g‖` for
`Φ g = (g, (δ_j g)_j)`, `t > 0` (`Rd.BoundedLipschitzDomain.enorm_sq_gagliardoEmbedding`). -/
theorem enorm_toLp_le_enorm_gagliardoEmbedding {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) :
    ‖g.toLp‖ₑ ≤ ‖Ω.gagliardoEmbedding t g‖ₑ := by
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, Ω.enorm_sq_gagliardoEmbedding ht]
  exact le_self_add

/-- **The Gagliardo form of a chart piece is bounded by the Gagliardo embedding**: the Gagliardo
form of `G_j = (ψ_j g) ∘ γ_j` on `H_j` is at most `‖Φ g‖²` for `Φ g = (g, (δ_j g)_j)`, `t > 0`
(`Rd.BoundedLipschitzDomain.enorm_sq_gagliardoEmbedding`). -/
theorem slobodeckijForm_chartPieceLp_le_enorm_gagliardoEmbedding_sq {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) (j : Fin Ω.N) :
    slobodeckijForm 2 t (Ω.chartPieceLp Ω.boundaryPartition j g.toLp :
      (Ω.graph j).hyperplane → ℂ) ≤ ‖Ω.gagliardoEmbedding t g‖ₑ ^ 2 := by
  rw [Ω.enorm_sq_gagliardoEmbedding ht]
  exact (Finset.single_le_sum (f := fun j => slobodeckijForm 2 t
    (Ω.chartPieceLp Ω.boundaryPartition j g.toLp : (Ω.graph j).hyperplane → ℂ))
    (fun _ _ => zero_le) (Finset.mem_univ j)).trans le_add_self

/-- **The Gagliardo embedding is bounded on `B^t_{2,2}(Γ)`**, `t > 0`: there is `C < ∞` with
`‖(g, (δ_j g)_j)‖ ≤ C ‖g‖_{B^t_{2,2}(Γ)}`, by `‖g‖_{L_2(Γ)} ≤ C₀ ‖g‖_{B^t_{2,2}(Γ)}`
(`Rd.BoundedLipschitzDomain.exists_eLpNorm_le_boundaryBesovNorm`) and the bound of the Gagliardo
form of each chart piece by its first-difference norm (`Rd.slobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.modNorm_chartPieceLp_le`). -/
theorem exists_enorm_gagliardoEmbedding_le {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundaryBesov 2 t 2,
      ‖Ω.gagliardoEmbedding t g‖ₑ ≤ C * ‖g‖ₑ := by
  obtain ⟨C₀, hC₀, h₀⟩ := Ω.exists_eLpNorm_le_boundaryBesovNorm (p := 2) Ω.boundaryPartition t 2
  set K := C₀ ^ 2 + ∑ j : Fin Ω.N, slobodeckijConstLower (Ω.graph j).hyperplane 2 t with hKdef
  have hK : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hC₀, ENNReal.sum_ne_top.2
    fun j _ => slobodeckijConstLower_ne_top two_ne_zero ENNReal.ofNat_ne_top ht⟩
  have hK2 : (K ^ (1 / 2 : ℝ)) ^ 2 = K := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  refine ⟨K ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK, fun g => ?_⟩
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, hK2, Ω.enorm_sq_gagliardoEmbedding ht,
    BoundaryBesov.enorm_eq, hKdef, add_mul, Finset.sum_mul]
  refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
  · rw [← mul_pow, Lp.enorm_def]
    exact pow_le_pow_left₀ zero_le (h₀ _ (Lp.aestronglyMeasurable _)) 2
  · have hS := slobodeckijForm_le two_ne_top ht (Ω.chartPieceLp Ω.boundaryPartition j g.toLp)
    have hsum := ENNReal.add_rpow_le_rpow_add
      ‖Ω.chartPieceLp Ω.boundaryPartition j g.toLp‖ₑ (lqNorm 2 fun k => dyadicWeight t k *
        lpModulus 2 1 (Ω.chartPieceLp Ω.boundaryPartition j g.toLp) k)
      (by norm_num : (1 : ℝ) ≤ (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hsum hS
    exact hS.trans (mul_le_mul' le_rfl (hsum.trans (pow_le_pow_left₀ zero_le
      (Ω.modNorm_chartPieceLp_le _ t 2 g.toLp j) 2)))

/-- **`B^t_{2,2}(Γ)` is bounded by the Gagliardo embedding**, `t > 0`: there is `C < ∞` with
`‖g‖_{B^t_{2,2}(Γ)} ≤ C ‖Φ g‖` for `Φ g = (g, (δ_j g)_j)`. Chart by chart,
`‖G_j‖_{L_2(H_j)} ≤ D_j ‖g‖_{L_2(Γ)} ≤ D_j ‖Φ g‖` with the bound
`D_j = Ω.boundaryPartition.derivBound j` of `ψ⁰_j`
(`Rd.BoundedLipschitzDomain.eLpNorm_chartPiece_le`,
`Rd.BoundedLipschitzDomain.enorm_toLp_le_enorm_gagliardoEmbedding`), and the square of the
first-difference norm of `G_j` is at most a constant times its Gagliardo form
(`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`), which is at most `‖Φ g‖²`
(`Rd.BoundedLipschitzDomain.slobodeckijForm_chartPieceLp_le_enorm_gagliardoEmbedding_sq`). -/
theorem exists_enorm_le_enorm_gagliardoEmbedding {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundaryBesov 2 t 2,
      ‖g‖ₑ ≤ C * ‖Ω.gagliardoEmbedding t g‖ₑ := by
  refine ⟨∑ j, (ENNReal.ofReal (Ω.boundaryPartition.derivBound j) +
      slobodeckijConstUpper (Ω.graph j).hyperplane 2 t ^ (1 / 2 : ℝ)),
    ENNReal.sum_ne_top.2 fun j _ => ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (slobodeckijConstUpper_ne_top two_ne_zero ENNReal.ofNat_ne_top ht)⟩, fun g => ?_⟩
  rw [BoundaryBesov.enorm_eq, Ω.boundaryBesovNorm_eq_sum_chartPieceLp, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [add_mul]
  refine add_le_add ?_ ?_
  · rw [Lp.enorm_def, eLpNorm_congr_ae (Ω.chartPieceLp_ae _ j g.toLp)]
    refine (Ω.eLpNorm_chartPiece_le _ j (Lp.stronglyMeasurable g.toLp)).trans
      (mul_le_mul' le_rfl ?_)
    rw [← Lp.enorm_def]
    exact Ω.enorm_toLp_le_enorm_gagliardoEmbedding ht g
  · have hL := lqNorm_modulus_rpow_le_slobodeckijForm two_ne_top ht
      (Ω.chartPieceLp Ω.boundaryPartition j g.toLp)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hL
    have hC2 : (slobodeckijConstUpper (Ω.graph j).hyperplane 2 t ^ (1 / 2 : ℝ)) ^ 2 =
        slobodeckijConstUpper (Ω.graph j).hyperplane 2 t := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, hC2]
    exact hL.trans (mul_le_mul' le_rfl
      (Ω.slobodeckijForm_chartPieceLp_le_enorm_gagliardoEmbedding_sq ht g j))

/-- **The Gagliardo embedding and `B^t_{2,2}(Γ)` have equivalent norms**, `t > 0`: there is
`C < ∞` with `‖g‖_{B^t_{2,2}(Γ)} ≤ C ‖(g, (δ_j g)_j)‖` and `‖(g, (δ_j g)_j)‖ ≤ C ‖g‖_{B^t_{2,2}(Γ)}`
(`Rd.BoundedLipschitzDomain.exists_enorm_le_enorm_gagliardoEmbedding`,
`Rd.BoundedLipschitzDomain.exists_enorm_gagliardoEmbedding_le`). -/
theorem exists_gagliardoEmbedding_norm_equiv {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundaryBesov 2 t 2,
      ‖g‖ₑ ≤ C * ‖Ω.gagliardoEmbedding t g‖ₑ ∧ ‖Ω.gagliardoEmbedding t g‖ₑ ≤ C * ‖g‖ₑ := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_enorm_le_enorm_gagliardoEmbedding ht
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_enorm_gagliardoEmbedding_le ht
  exact ⟨max C₁ C₂, (max_lt hC₁.lt_top hC₂.lt_top).ne, fun g =>
    ⟨(h₁ g).trans (mul_le_mul' (le_max_left _ _) le_rfl),
      (h₂ g).trans (mul_le_mul' (le_max_right _ _) le_rfl)⟩⟩

/-- **The Sobolev space `H^t(Γ)`** on the boundary of a bounded Lipschitz domain, `0 < t < 1`:
the space `B^t_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.BoundaryBesov`) with the chart-wise
Gagliardo norm
`‖g‖²_{H^t(Γ)} = ‖g‖²_{L_2(Γ)} + ∑_j ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t)`
for the chart pieces `G_j = (ψ_j g) ∘ γ_j` of the canonical resolution of unity, the norm of the
Gagliardo embedding (`Rd.BoundedLipschitzDomain.gagliardoEmbedding`). This norm satisfies the
parallelogram law and comes from an inner product, so `H^t(Γ)` is a Hilbert space; it is
equivalent to the norm of `B^t_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`) and to Gagliardo's norm with the
surface measure
(`Rd.BoundedLipschitzDomain.exists_boundarySobolev_norm_equiv_slobodeckij`). The definition is a
type synonym of `B^t_{2,2}(Γ)` with its own norm, for every `t`. For `0 < t < 1` it is `H^t(Γ)`.
For `t < 0` it is `L_2(Γ)` with its norm, and for `t ≥ 1` and `n ≥ 2` it is `{0}`, since
`ω_1(G, h) = o(h)` forces `G = 0` in `L_2(H_j)`. The space `H^{-t}(Γ)` is
`Rd.BoundedLipschitzDomain.DualBoundarySobolev t`. -/
def BoundarySobolev (t : ℝ) : Type _ := Ω.BoundaryBesov 2 t 2

namespace BoundarySobolev

variable {Ω} {t : ℝ}

/-- `H^t(Γ)` is an additive group, that of `B^t_{2,2}(Γ)`. -/
noncomputable instance instAddCommGroup : AddCommGroup (Ω.BoundarySobolev t) :=
  inferInstanceAs (AddCommGroup (Ω.BoundaryBesov 2 t 2))

/-- `H^t(Γ)` is a complex vector space, that of `B^t_{2,2}(Γ)`. -/
noncomputable instance instModule : Module ℂ (Ω.BoundarySobolev t) :=
  inferInstanceAs (Module ℂ (Ω.BoundaryBesov 2 t 2))

/-- **The norm of `H^t(Γ)`**: the norm of the Gagliardo embedding (Mathlib's
`NormedAddCommGroup.induced`, the embedding being injective). -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Ω.BoundarySobolev t) :=
  NormedAddCommGroup.induced (Ω.BoundarySobolev t) _
    (Ω.gagliardoEmbedding t : Ω.BoundarySobolev t →ₗ[ℂ] _) (Ω.gagliardoEmbedding_injective t)

/-- `H^t(Γ)` is a complex normed space: the Gagliardo embedding is linear (Mathlib's
`NormedSpace.induced`). -/
noncomputable instance instNormedSpace : NormedSpace ℂ (Ω.BoundarySobolev t) :=
  NormedSpace.induced ℂ (Ω.BoundarySobolev t) _
    (Ω.gagliardoEmbedding t : Ω.BoundarySobolev t →ₗ[ℂ] _)

/-- **The inner product of `H^t(Γ)`**: `⟪g, h⟫ = ⟪(g, (δ_j g)_j), (h, (δ_j h)_j)⟫` in the
Hilbert space of the Gagliardo embedding, so that `‖g‖² = ⟪g, g⟫`; by polarisation it is the
only inner product with the chart-wise Gagliardo norm. The fields are those of Mathlib's
`InnerProductSpace.induced`, written out over the norm `instNormedAddCommGroup`, so that instance
search finds the norm of the dual space `H^{-t}(Γ)`. -/
noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (Ω.BoundarySobolev t) where
  inner g h := ⟪Ω.gagliardoEmbedding t g, Ω.gagliardoEmbedding t h⟫_ℂ
  norm_sq_eq_re_inner g := norm_sq_eq_re_inner (Ω.gagliardoEmbedding t g)
  conj_inner_symm _ _ := inner_conj_symm _ _
  add_left g g' h :=
    (congrArg (⟪·, Ω.gagliardoEmbedding t h⟫_ℂ) ((Ω.gagliardoEmbedding t).map_add g g')).trans
      (inner_add_left _ _ _)
  smul_left g h c :=
    (congrArg (⟪·, Ω.gagliardoEmbedding t h⟫_ℂ) ((Ω.gagliardoEmbedding t).map_smul c g)).trans
      (inner_smul_left _ _ _)

end BoundarySobolev

/-- The norm of `g ∈ H^t(Γ)` is the norm of its Gagliardo embedding. -/
theorem norm_boundarySobolev {t : ℝ} (g : Ω.BoundarySobolev t) :
    ‖g‖ = ‖Ω.gagliardoEmbedding t g‖ :=
  rfl

/-- The extended norm of `g ∈ H^t(Γ)` is that of its Gagliardo embedding. -/
theorem enorm_boundarySobolev {t : ℝ} (g : Ω.BoundarySobolev t) :
    ‖g‖ₑ = ‖Ω.gagliardoEmbedding t g‖ₑ :=
  rfl

/-- **The inner product of `H^t(Γ)`** is the inner product of the Gagliardo embeddings:
`⟪g, h⟫_{H^t(Γ)} = ⟪g, h⟫_{L_2(Γ)} + ∑_j ⟪δ_j g, δ_j h⟫`. -/
theorem inner_boundarySobolev {t : ℝ} (g h : Ω.BoundarySobolev t) :
    ⟪g, h⟫_ℂ = ⟪Ω.gagliardoEmbedding t g, Ω.gagliardoEmbedding t h⟫_ℂ :=
  rfl

/-- **Equal smoothness gives the same space**: for `t = t'`, the identity `H^t(Γ) → H^{t'}(Γ)` as
a linear isometric isomorphism, as Mathlib's `LinearEquiv.cast` does for linear isomorphisms. It
identifies, for example, `H^{1 - 1/2}(Γ)` with `H^{1/2}(Γ)`, two types that Lean does not identify
by computation. -/
noncomputable def boundarySobolevCongr {t t' : ℝ} (h : t = t') :
    Ω.BoundarySobolev t ≃ₗᵢ[ℂ] Ω.BoundarySobolev t' :=
  h ▸ LinearIsometryEquiv.refl ℂ _

/-- The identification `H^t(Γ) = H^{t'}(Γ)` keeps the function in `L_2(Γ)`. -/
theorem toLp_boundarySobolevCongr {t t' : ℝ} (h : t = t') (g : Ω.BoundarySobolev t) :
    (Ω.boundarySobolevCongr h g).toLp = g.toLp := by
  subst h
  rfl

/-- **`H^t(Γ)` and `B^t_{2,2}(Γ)` are isomorphic**, `t > 0`: the identity is an isomorphism of
normed spaces from `B^t_{2,2}(Γ)` with the chart-wise Gagliardo norm onto `B^t_{2,2}(Γ)` with the
norm by chart pieces (`Rd.BoundedLipschitzDomain.exists_gagliardoEmbedding_norm_equiv`). -/
noncomputable def boundarySobolevEquivBoundaryBesov (t : ℝ) (ht : 0 < t) :
    Ω.BoundarySobolev t ≃L[ℂ] Ω.BoundaryBesov 2 t 2 :=
  { (LinearEquiv.refl ℂ (Ω.BoundaryBesov 2 t 2) :
      Ω.BoundarySobolev t ≃ₗ[ℂ] Ω.BoundaryBesov 2 t 2) with
    continuous_toFun := by
      obtain ⟨C, hC, h⟩ := Ω.exists_gagliardoEmbedding_norm_equiv ht
      have hb : ∀ g : Ω.BoundaryBesov 2 t 2, ‖g‖ ≤ C.toReal * ‖Ω.gagliardoEmbedding t g‖ :=
        fun g => norm_le_toReal_mul_of_enorm_le hC (h g).1
      let e : Ω.BoundarySobolev t ≃ₗ[ℂ] Ω.BoundaryBesov 2 t 2 := LinearEquiv.refl ℂ _
      exact AddMonoidHomClass.continuous_of_bound e C.toReal hb
    continuous_invFun := by
      obtain ⟨C, hC, h⟩ := Ω.exists_gagliardoEmbedding_norm_equiv ht
      have hb : ∀ g : Ω.BoundaryBesov 2 t 2, ‖Ω.gagliardoEmbedding t g‖ ≤ C.toReal * ‖g‖ :=
        fun g => norm_le_toReal_mul_of_enorm_le hC (h g).2
      let e : Ω.BoundaryBesov 2 t 2 ≃ₗ[ℂ] Ω.BoundarySobolev t := LinearEquiv.refl ℂ _
      exact AddMonoidHomClass.continuous_of_bound e C.toReal hb }

/-- The isomorphism `H^t(Γ) ≅ B^t_{2,2}(Γ)` keeps the function in `L_2(Γ)`. -/
theorem toLp_boundarySobolevEquivBoundaryBesov {t : ℝ} (ht : 0 < t) (g : Ω.BoundarySobolev t) :
    (Ω.boundarySobolevEquivBoundaryBesov t ht g).toLp = g.toLp :=
  rfl

/-- The inverse isomorphism `B^t_{2,2}(Γ) ≅ H^t(Γ)` keeps the function in `L_2(Γ)`. -/
theorem toLp_boundarySobolevEquivBoundaryBesov_symm {t : ℝ} (ht : 0 < t)
    (g : Ω.BoundaryBesov 2 t 2) :
    BoundaryBesov.toLp ((Ω.boundarySobolevEquivBoundaryBesov t ht).symm g) = g.toLp :=
  rfl

/-- **`H^t(Γ)` is a Hilbert space**, `t > 0`: it is isomorphic to the Banach space
`B^t_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`,
`Rd.BoundedLipschitzDomain.completeSpace_boundaryBesov`; Mathlib's `completeSpace_congr`). -/
instance completeSpace_boundarySobolev {t : ℝ} [Fact (0 < t)] :
    CompleteSpace (Ω.BoundarySobolev t) :=
  (completeSpace_congr (e := (Ω.boundarySobolevEquivBoundaryBesov t Fact.out).toEquiv)
    (Ω.boundarySobolevEquivBoundaryBesov t Fact.out).isUniformEmbedding).2 inferInstance

/-- **The dual space `H^{-t}(Γ)`**: the bounded linear functionals on `H^t(Γ)`. -/
abbrev DualBoundarySobolev (t : ℝ) := StrongDual ℂ (Ω.BoundarySobolev t)

/-- **Riesz for `H^{-t}(Γ)`**, `t > 0`: the conjugate-linear isometric isomorphism of the dual
onto `H^t(Γ)` that represents a functional by an element (Mathlib's `InnerProductSpace.toDual`):
`ℓ g = ⟪dualBoundarySobolevEquiv t ht ℓ, g⟫`
(`Rd.BoundedLipschitzDomain.dualBoundarySobolevEquiv_apply`). The identification depends on the
chosen Hilbert norm, that is, on the charts and on the resolution of unity `ψ⁰`. -/
noncomputable def dualBoundarySobolevEquiv (t : ℝ) (ht : 0 < t) :
    Ω.DualBoundarySobolev t ≃ₗᵢ⋆[ℂ] Ω.BoundarySobolev t :=
  haveI : Fact (0 < t) := ⟨ht⟩
  (InnerProductSpace.toDual ℂ (Ω.BoundarySobolev t)).symm

/-- Every functional on `H^t(Γ)` is the inner product with its representing element. -/
theorem dualBoundarySobolevEquiv_apply {t : ℝ} (ht : 0 < t) (ℓ : Ω.DualBoundarySobolev t)
    (g : Ω.BoundarySobolev t) :
    ℓ g = ⟪Ω.dualBoundarySobolevEquiv t ht ℓ, g⟫_ℂ := by
  have : Fact (0 < t) := ⟨ht⟩
  rw [dualBoundarySobolevEquiv, InnerProductSpace.toDual_symm_apply]

/-- **The norm of `H^t(Γ)` by the Sobolev–Slobodeckij norm on `Γ`**, `0 < t < 1`: there is
`C < ∞` with `‖g‖²_{H^t(Γ)} ≤ C (‖g‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |g(y) - g(x)|² / |y - x|^(n-1+2t) dσ dσ)`
and the reverse bound, for every `g ∈ H^t(Γ)`: the norm equivalence with `B^t_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.exists_gagliardoEmbedding_norm_equiv`), the bounds of Gagliardo's form
on `Γ` by the chart-wise norm (`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`,
`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`) and of `L_2(Γ)` by
`B^t_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.exists_eLpNorm_le_boundaryBesovNorm`). -/
theorem exists_boundarySobolev_norm_equiv_slobodeckij {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Ω.BoundarySobolev t,
      ‖g‖ₑ ^ 2 ≤ C * (‖g.toLp‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 t g.toLp) ∧
        ‖g.toLp‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 t g.toLp ≤ C * ‖g‖ₑ ^ 2 := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_gagliardoEmbedding_norm_equiv ht
  obtain ⟨C₀, hC₀, h₀⟩ := Ω.exists_eLpNorm_le_boundaryBesovNorm (p := 2) Ω.boundaryPartition t 2
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundarySlobodeckijForm_le (p := 2) Ω.boundaryPartition
    two_ne_top ht
  obtain ⟨C₃, hC₃, h₃⟩ := Ω.exists_boundaryBesovNorm_rpow_le (p := 2) Ω.boundaryPartition
    two_ne_top ht ht1
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h₂ h₃
  refine ⟨C₁ ^ 2 * C₃ + (C₀ ^ 2 + C₂) * C₁ ^ 2, ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.pow_ne_top hC₁) hC₃, ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.pow_ne_top hC₀, hC₂⟩) (ENNReal.pow_ne_top hC₁)⟩, fun g => ⟨?_, ?_⟩⟩
  · have hB := (h₁ g).2.trans_eq (congrArg (C₁ * ·) (BoundaryBesov.enorm_eq g))
    rw [enorm_boundarySobolev]
    calc _ ≤ (C₁ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp) ^ 2 :=
          pow_le_pow_left₀ zero_le hB 2
      _ ≤ C₁ ^ 2 * (C₃ * (‖g.toLp‖ₑ ^ 2 + Ω.boundarySlobodeckijForm 2 t g.toLp)) := by
          rw [mul_pow, Lp.enorm_def]
          exact mul_le_mul' le_rfl (h₃ _ (Lp.aestronglyMeasurable _))
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · have hB := (BoundaryBesov.enorm_eq g).symm.trans_le (h₁ g).1
    rw [enorm_boundarySobolev]
    calc _ ≤ (C₀ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp) ^ 2 +
          C₂ * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp ^ 2 := by
          rw [Lp.enorm_def]
          exact add_le_add (pow_le_pow_left₀ zero_le (h₀ _ (Lp.aestronglyMeasurable _)) 2)
            (h₂ _)
      _ = (C₀ ^ 2 + C₂) * Ω.boundaryBesovNorm 2 Ω.boundaryPartition t 2 g.toLp ^ 2 := by ring
      _ ≤ (C₀ ^ 2 + C₂) * (C₁ * ‖Ω.gagliardoEmbedding t g‖ₑ) ^ 2 :=
          mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le hB 2)
      _ = (C₀ ^ 2 + C₂) * C₁ ^ 2 * ‖Ω.gagliardoEmbedding t g‖ₑ ^ 2 := by ring
      _ ≤ _ := mul_le_mul' le_add_self le_rfl

/-! ### The trace onto `H^{s-1/2}(Γ)` -/

/-- **The trace space of `H^s(Ω)` is isomorphic to `H^{s-1/2}(Γ)`**, `1/2 < s < 3/2` (McLean,
Theorem 3.38): `w ↦ τ_s w`, the isomorphism with `B^{s-1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesov`) followed by the identity onto
`H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`). For `s = 1`,
`Rd.BoundedLipschitzDomain.traceSpaceOneEquivBoundarySobolevHalf` has values in `H^{1/2}(Γ)`. -/
noncomputable def traceSpaceEquivBoundarySobolev (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.TraceSpace s hs hs' ≃L[ℂ] Ω.BoundarySobolev (s - 1 / 2) :=
  (Ω.traceSpaceEquivBoundaryBesov s hs hs').trans
    (Ω.boundarySobolevEquivBoundaryBesov (s - 1 / 2) (sub_pos.2 hs)).symm

/-- The isomorphism `Ω.TraceSpace s ≅ H^{s-1/2}(Γ)` sends `w` to `τ_s w ∈ L_2(Γ)`. -/
theorem toLp_traceSpaceEquivBoundarySobolev {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (w : Ω.TraceSpace s hs hs') :
    (Ω.traceSpaceEquivBoundarySobolev s hs hs' w).toLp = Ω.traceL2 s hs hs' w :=
  rfl

/-- **The trace space of `H^1(Ω)` is isomorphic to `H^{1/2}(Γ)`**: the isomorphism
`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev` at `s = 1`, followed by the
identification of `H^{1 - 1/2}(Γ)` with `H^{1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.boundarySobolevCongr`). -/
noncomputable def traceSpaceOneEquivBoundarySobolevHalf :
    Ω.TraceSpace 1 ≃L[ℂ] Ω.BoundarySobolev (1 / 2) :=
  (Ω.traceSpaceEquivBoundarySobolev 1).trans
    (Ω.boundarySobolevCongr (by norm_num)).toContinuousLinearEquiv

/-- The isomorphism `Ω.TraceSpace 1 ≅ H^{1/2}(Γ)` sends `w` to `τ_1 w ∈ L_2(Γ)`. -/
theorem toLp_traceSpaceOneEquivBoundarySobolevHalf (w : Ω.TraceSpace 1) :
    (Ω.traceSpaceOneEquivBoundarySobolevHalf w).toLp = (Ω.traceL2 1) w :=
  Ω.toLp_boundarySobolevCongr _ _

/-- **The trace `H^s(Ω) → H^{s-1/2}(Γ)`**, `1/2 < s < 3/2` (McLean, Theorem 3.38): the trace
`γ_s` onto the trace space followed by the isomorphism with `H^{s-1/2}(Γ)`
(`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev`). It is onto, with the bounded linear
right inverse `Rd.BoundedLipschitzDomain.sobolevExtend`, its kernel is the trace kernel, and its
function in `L_2(Γ)` is the Besov trace of `1_Ω ι_s u`
(`Rd.BoundedLipschitzDomain.toLp_sobolevTrace_eq_besovTrace`). -/
noncomputable def sobolevTrace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    RestrictionSpace s Ω.toOpens →L[ℂ] Ω.BoundarySobolev (s - 1 / 2) :=
  (Ω.traceSpaceEquivBoundarySobolev s hs hs' :
    Ω.TraceSpace s hs hs' →L[ℂ] Ω.BoundarySobolev (s - 1 / 2)) ∘L Ω.trace s hs hs'

/-- **The extension `H^{s-1/2}(Γ) → H^s(Ω)`**, `1/2 < s < 3/2`: the inverse of the isomorphism
`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev` followed by the extension `E_s`, a
bounded linear right inverse of the trace
(`Rd.BoundedLipschitzDomain.sobolevTrace_sobolevExtend`). -/
noncomputable def sobolevExtend (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.BoundarySobolev (s - 1 / 2) →L[ℂ] RestrictionSpace s Ω.toOpens :=
  Ω.extend s hs hs' ∘L ((Ω.traceSpaceEquivBoundarySobolev s hs hs').symm :
    Ω.BoundarySobolev (s - 1 / 2) →L[ℂ] Ω.TraceSpace s hs hs')

/-- The trace into `H^{s-1/2}(Γ)` has the function `γ^s_{L_2} u ∈ L_2(Γ)`
(`Rd.BoundedLipschitzDomain.boundaryTraceL2`). -/
theorem toLp_sobolevTrace (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.sobolevTrace s hs hs' u).toLp = Ω.boundaryTraceL2 s hs hs' u :=
  rfl

/-- **The extension is a right inverse of the trace**: `γ(E g) = g` for every
`g ∈ H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.trace_extend`). -/
theorem sobolevTrace_sobolevExtend (s : ℝ) (g : Ω.BoundarySobolev (s - 1 / 2))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.sobolevTrace s hs hs' (Ω.sobolevExtend s hs hs' g) = g := by
  change Ω.traceSpaceEquivBoundarySobolev s hs hs' (Ω.trace s hs hs'
    (Ω.extend s hs hs' ((Ω.traceSpaceEquivBoundarySobolev s hs hs').symm g))) = g
  rw [trace_extend, ContinuousLinearEquiv.apply_symm_apply]

/-- **The kernel of the trace `H^s(Ω) → H^{s-1/2}(Γ)` is the trace kernel**: the isomorphism with
`H^{s-1/2}(Γ)` is injective (`Rd.BoundedLipschitzDomain.ker_trace`). -/
theorem ker_sobolevTrace (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.sobolevTrace s hs hs').ker = Ω.traceKer s hs hs' := by
  rw [← Ω.ker_trace s hs hs']
  ext u
  change Ω.traceSpaceEquivBoundarySobolev s hs hs' (Ω.trace s hs hs' u) = 0 ↔
    Ω.trace s hs hs' u = 0
  exact (Ω.traceSpaceEquivBoundarySobolev s hs hs').map_eq_zero_iff

/-- **Restrictions of `H^s(V)` lie in `B^s_{2,2}(Ω)`**, `0 < s < 2`: for `U ∈ H^s(V)`,
`N_Ω(1_Ω ι_s U) ≤ ‖ι_s U‖_2 + ‖(2^(ks) ω_2(ι_s U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with
`C = Rd.sobolevBesovConst V s 2` (`Rd.modNormOn_le_modNorm_of_indicatorLp`,
`Rd.modNorm_sobolevToL2_le`). -/
theorem modNormOn_indicatorLp_sobolevToL2_le {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (U : H^{s}(V)) :
    modNormOn Ω.measurableSet 2 s 2 (indicatorLp Ω.measurableSet (sobolevToL2 hs.le U)) ≤
      sobolevBesovConst V s 2 * ‖U‖ₑ :=
  (modNormOn_le_modNorm_of_indicatorLp Ω.measurableSet 2 s 2
    (indicatorLp_indicatorLp _ _).symm).trans
    (modNorm_sobolevToL2_le hs (r := 2) (by exact_mod_cast hs2) U)

/-- **The restriction `H^s(Ω) → B^s_{2,2}(Ω)`**, `0 < s < 2`: `u ↦ 1_Ω ι_s u`, the `L_2` function
of `u` cut off outside `Ω`, in the Banach space `B^s_{2,2}(Ω)` of
`Rd.BoundedLipschitzDomain.DomainBesov` with differences of order `2`, bounded by
`Rd.BoundedLipschitzDomain.modNormOn_indicatorLp_sobolevToL2_le`. -/
noncomputable def restrictionToDomainBesov (s : ℝ) (hs : 0 < s) (hs2 : s < 2) :
    RestrictionSpace s Ω.toOpens →L[ℂ] Ω.DomainBesov 2 2 s 2 :=
  LinearMap.mkContinuous
    { toFun u := ⟨indicatorLp Ω.measurableSet (sobolevToL2 hs.le (u : H^{s}(V))),
        indicatorLp_indicatorLp _ _,
        (Ω.modNormOn_indicatorLp_sobolevToL2_le hs hs2 _).trans_lt (ENNReal.mul_lt_top
          (sobolevBesovConst_ne_top hs (r := 2) (by exact_mod_cast hs2)).lt_top enorm_lt_top)⟩
      map_add' u w := DomainBesov.ext (by
        change indicatorLp Ω.measurableSet (sobolevToL2 hs.le ((u : H^{s}(V)) + w)) = _
        rw [map_add, map_add]
        rfl)
      map_smul' c u := DomainBesov.ext (by
        change indicatorLp Ω.measurableSet (sobolevToL2 hs.le (c • (u : H^{s}(V)))) = _
        rw [map_smul, map_smul]
        rfl) }
    (sobolevBesovConst V s 2).toReal fun u => by
      refine norm_le_toReal_mul_of_enorm_le
        (sobolevBesovConst_ne_top hs (r := 2) (by exact_mod_cast hs2)) ?_
      rw [DomainBesov.enorm_eq]
      exact Ω.modNormOn_indicatorLp_sobolevToL2_le hs hs2 _

/-- The restriction sends `u` to `1_Ω ι_s u`. -/
theorem toLp_restrictionToDomainBesov (s : ℝ) (hs : 0 < s) (hs2 : s < 2)
    (u : RestrictionSpace s Ω.toOpens) :
    (Ω.restrictionToDomainBesov s hs hs2 u).toLp =
      indicatorLp Ω.measurableSet (sobolevToL2 hs.le (u : H^{s}(V))) :=
  rfl

/-- **The trace into `H^{s-1/2}(Γ)` is the Besov trace at `p = q = 2`**, `1/2 < s < 3/2`: the
function in `L_2(Γ)` of the trace of `u ∈ H^s(Ω)` is the Besov trace
(`Rd.BoundedLipschitzDomain.besovTrace`) of `1_Ω ι_s u ∈ B^s_{2,2}(Ω)`; both are the boundary
trace `Tr_Γ ι_s u` (`Rd.BoundedLipschitzDomain.besovTrace_ae` with the extension `ι_s u`,
`Rd.BoundedLipschitzDomain.boundaryTraceL2_apply_ae`). -/
theorem toLp_sobolevTrace_eq_besovTrace (s : ℝ) (u : RestrictionSpace s Ω.toOpens)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    (Ω.sobolevTrace s hs hs' u).toLp = (Ω.besovTrace two_ne_top s 2 (by norm_num; linarith)
      (by norm_num; linarith) (Ω.restrictionToDomainBesov s (one_half_pos.trans hs)
        (by linarith) u)).toLp := by
  have hs0 : 0 < s := one_half_pos.trans hs
  rw [Ω.toLp_sobolevTrace s u hs hs']
  refine Lp.ext ((Ω.boundaryTraceL2_apply_ae Ω.boundaryPartition s u hs hs').trans ?_)
  exact (Ω.besovTrace_ae two_ne_top _ _ _ (F := sobolevToL2 hs0.le (u : H^{s}(V))) rfl
    ((modNorm_sobolevToL2_le hs0 (r := 2) (by norm_num; linarith) _).trans_lt
      (ENNReal.mul_lt_top (sobolevBesovConst_ne_top hs0 (r := 2)
        (by norm_num; linarith)).lt_top enorm_lt_top))).symm

end BoundedLipschitzDomain

end Rd
