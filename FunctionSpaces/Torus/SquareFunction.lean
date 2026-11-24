/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.SingularIntegrals
public import FunctionSpaces.Torus.TriebelLizorkin

/-!
# The square function theorem on the torus

Let `d ≥ 1` and `1 < p < ∞`. The norm `‖f‖_{F^0_{p,2}(𝕋^d)}` of `f ∈ L_p(𝕋^d)` is the `L_p` norm
of the square function `t ↦ ‖((ψ_j ⋆ f)(t))_j‖_{ℓ_2}` of the Littlewood–Paley blocks
(`Torus.periodicTriebelLizorkinNorm_zero_left`). The square function theorem on the torus is the
two-sided bound of this norm by `‖f‖_p`, with named constants that are proved finite
(`Torus.periodicSquareFunctionConst_ne_top`, `Torus.periodicSquareSynthesisConst_ne_top`):

* `‖f‖_{F^0_{p,2}(𝕋^d)} ≤ Q^𝕋_p ‖f‖_p` (`Torus.periodicTriebelLizorkinNorm_zero_two_le`, constant
  `Torus.periodicSquareFunctionConst`): the analysis bound of the vector-valued singular integrals
  on the torus for the Calderón–Zygmund family `(ψ_j)_j`;
* `‖f‖_p ≤ Q̃^𝕋_p ‖f‖_{F^0_{p,2}(𝕋^d)}` (`Torus.enorm_le_periodicTriebelLizorkinNorm_zero_two`,
  constant `Torus.periodicSquareSynthesisConst`): the synthesis kernels
  `ψ̃_j = Rd.dualLpBlockKernel j` reproduce the blocks, `ψ̃_j ⋆ Δ_j f = Δ_j f`
  (`Torus.periodicEconvLp_dualLpBlockKernel_periodicLpBlock`), so
  `∑_{j ∈ s} ψ̃_j ⋆ Δ_j f = ∑_{j ∈ s} Δ_j f` almost everywhere
  (`Torus.sum_periodicEconv_dualLpBlockKernel_periodicLpBlock_ae`); these partial sums tend to `f`
  (`Torus.tendsto_sum_periodicLpBlock`), and the synthesis bound for the family `(ψ̃_j)_j`
  applies.

Hence `F^0_{p,2}(𝕋^d) = L_p(𝕋^d)` (`Torus.periodicTriebelLizorkinSpace_zero_two_eq_top`), and
`B^s_{p,min(p,2)}(𝕋^d) ⊆ F^s_{p,2}(𝕋^d)` holds for every `s ≥ 0`
(`Torus.memPeriodicTriebelLizorkin_two_of_memBesov`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Filter
open scoped ENNReal TorusHaar Topology

open ENNReal (lqNorm)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The constants -/

variable (d) in
/-- The constant `Q^𝕋_p` of the **upper square function bound on the torus**: the constant
`Torus.periodicCZConst` of the Calderón–Zygmund family of the blocks `ψ_j`, with overlap `2`,
Hörmander constant `4 H_{A^ψ}` and far mass bound `2 T_{A^ψ}`, where
`A^ψ = Rd.lpBlockKernelBaseBound` (`Rd.isCZFamily_lpBlockKernel`,
`Torus.farMass_lpBlockKernel_le`). -/
noncomputable def periodicSquareFunctionConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  periodicCZConst d p 2
    (4 * Rd.familyHormanderConst (EuclideanSpace ℝ d)
      (Rd.lpBlockKernelBaseBound (EuclideanSpace ℝ d)))
    (2 * Rd.familyTailConst (EuclideanSpace ℝ d)
      (Rd.lpBlockKernelBaseBound (EuclideanSpace ℝ d)) 0 1)

/-- The constant `Torus.periodicSquareFunctionConst d p` is finite for `1 < p < ∞`. -/
theorem periodicSquareFunctionConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    periodicSquareFunctionConst d p ≠ ∞ :=
  periodicCZConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyHormanderConst_ne_top _))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyTailConst_ne_top _ _ _))

variable (d) in
/-- The constant `Q̃^𝕋_p` of the **lower square function bound on the torus**: the constant
`Torus.periodicCZConst` of the Calderón–Zygmund family of the synthesis kernels `ψ̃_j`,
with overlap `4`, Hörmander constant `4 H_Ã` and far mass bound `2 T_Ã`, where
`Ã = Rd.dualLpBlockKernelBaseBound` (`Rd.isCZFamily_dualLpBlockKernel`,
`Torus.farMass_dualLpBlockKernel_le`). -/
noncomputable def periodicSquareSynthesisConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  periodicCZConst d p 4
    (4 * Rd.familyHormanderConst (EuclideanSpace ℝ d)
      (Rd.dualLpBlockKernelBaseBound (EuclideanSpace ℝ d)))
    (2 * Rd.familyTailConst (EuclideanSpace ℝ d)
      (Rd.dualLpBlockKernelBaseBound (EuclideanSpace ℝ d)) 0 1)

/-- The constant `Torus.periodicSquareSynthesisConst d p` is finite for `1 < p < ∞`. -/
theorem periodicSquareSynthesisConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    periodicSquareSynthesisConst d p ≠ ∞ :=
  periodicCZConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyHormanderConst_ne_top _))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyTailConst_ne_top _ _ _))

/-! ### The upper bound -/

/-- **The upper square function bound on the torus**: for `d ≥ 1`, `1 < p < ∞` and
`f ∈ L_p(𝕋^d)`, `‖f‖_{F^0_{p,2}(𝕋^d)} ≤ Q^𝕋_p ‖f‖_p` with
`Q^𝕋_p = Torus.periodicSquareFunctionConst d p`: the analysis bound on the torus
(`Torus.eLpNorm_lqNorm_periodicEconv_le`) for the Calderón–Zygmund family `(ψ_j)_j`. -/
theorem periodicTriebelLizorkinNorm_zero_two_le [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicTriebelLizorkinNorm 0 2 f ≤ periodicSquareFunctionConst d p * ‖f‖ₑ := by
  rw [periodicTriebelLizorkinNorm_zero_left]
  exact eLpNorm_lqNorm_periodicEconv_le Rd.isCZFamily_lpBlockKernel farMass_lpBlockKernel_le
    hp1 hp f

/-- **`L_p(𝕋^d) ⊆ F^0_{p,2}(𝕋^d)`**: for `d ≥ 1` and `1 < p < ∞`, every `f ∈ L_p(𝕋^d)` has a
finite Triebel–Lizorkin norm `‖f‖_{F^0_{p,2}(𝕋^d)}`. -/
theorem memPeriodicTriebelLizorkin_zero_two [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : MemPeriodicTriebelLizorkin 0 2 f :=
  (periodicTriebelLizorkinNorm_zero_two_le hp1 hp f).trans_lt
    (ENNReal.mul_lt_top (periodicSquareFunctionConst_ne_top hp1 hp).lt_top enorm_lt_top)

/-! ### The reproducing formula -/

/-- **The synthesis kernels reproduce the blocks**: for `1 ≤ p < ∞` and `f ∈ L_p(𝕋^d)`,
`ψ̃_j ⋆ Δ_j f = Δ_j f`, since `ψ̃_j ⋆ ψ_j = ψ_j` on `ℝ^d`
(`Rd.conv_dualLpBlockKernel_lpBlockKernel`). -/
theorem periodicEconvLp_dualLpBlockKernel_periodicLpBlock (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    periodicEconvLp hp (Rd.integrable_dualLpBlockKernel j) (periodicLpBlock hp j f) =
      periodicLpBlock hp j f :=
  periodicEconvLp_comp_periodicEconvLp_of_eq hp (Rd.integrable_dualLpBlockKernel j)
    (Rd.integrable_lpBlockKernel j)
    (Rd.integrable_lpBlockKernel j) (Rd.conv_dualLpBlockKernel_lpBlockKernel j) f

/-- **The reproducing sums**: for `1 ≤ p < ∞`, `f ∈ L_p(𝕋^d)` and every finite set `s ⊆ ℕ`,
`∑_{j ∈ s} ψ̃_j ⋆ Δ_j f = ∑_{j ∈ s} Δ_j f` almost everywhere, with the pointwise
convolutions of representatives on the left. -/
theorem sum_periodicEconv_dualLpBlockKernel_periodicLpBlock_ae (hp : p ≠ ∞) (s : Finset ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    (fun t => ∑ j ∈ s, periodicEconv (Rd.dualLpBlockKernel j) (periodicLpBlock hp j f) t) =ᵐ[volume]
      ⇑(∑ j ∈ s, periodicLpBlock hp j f) := by
  have h :=
    coeFn_sum_periodicEconvLp_ae hp s
      (fun j => Rd.integrable_dualLpBlockKernel (V := EuclideanSpace ℝ d) j)
    fun j => periodicLpBlock hp j f
  simp only [periodicEconvLp_dualLpBlockKernel_periodicLpBlock] at h
  exact h.symm

/-! ### The lower bound and `L_p = F^0_{p,2}` -/

/-- **The lower square function bound on the torus**: for `d ≥ 1`, `1 < p < ∞` and
`f ∈ L_p(𝕋^d)`, `‖f‖_p ≤ Q̃^𝕋_p ‖f‖_{F^0_{p,2}(𝕋^d)}` with
`Q̃^𝕋_p = Torus.periodicSquareSynthesisConst d p`. The partial sums `∑_{j < J} Δ_j f` tend to `f`
(`Torus.tendsto_sum_periodicLpBlock`) and equal `∑_{j < J} ψ̃_j ⋆ Δ_j f`, whose `L_p` norms the
synthesis bound on the torus (`Torus.eLpNorm_sum_periodicEconv_le`) for the family `(ψ̃_j)_j`
controls. -/
theorem enorm_le_periodicTriebelLizorkinNorm_zero_two [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖f‖ₑ ≤ periodicSquareSynthesisConst d p * periodicTriebelLizorkinNorm 0 2 f := by
  have h : Tendsto (fun J => ‖∑ j ∈ Finset.range J, periodicLpBlock hp j f‖ₑ) atTop (𝓝 ‖f‖ₑ) :=
    (tendsto_sum_periodicLpBlock hp f).enorm
  have hblock : (fun t => lqNorm 2 fun j => ‖periodicLpBlock hp j f t‖ₑ) =ᵐ[volume]
      fun t => lqNorm 2 fun j => ‖periodicBlockFun j f t‖ₑ := by
    filter_upwards [ae_all_iff.2 fun j => periodicLpBlock_ae_eq_periodicBlockFun hp j f] with t ht
    simp only [ht]
  refine le_of_tendsto' h fun J => ?_
  rw [Lp.enorm_def,
    ← eLpNorm_congr_ae (sum_periodicEconv_dualLpBlockKernel_periodicLpBlock_ae hp _ f),
    periodicTriebelLizorkinNorm_zero_left, ← eLpNorm_congr_ae hblock]
  exact eLpNorm_sum_periodicEconv_le Rd.isCZFamily_dualLpBlockKernel farMass_dualLpBlockKernel_le
    hp1 hp _ (fun j => (Lp.stronglyMeasurable _).measurable) fun j => Lp.memLp _

/-- **The square function theorem on the torus**: for `d ≥ 1` and `1 < p < ∞`, the subspace
`F^0_{p,2}(𝕋^d)` of `L_p(𝕋^d)` is all of `L_p(𝕋^d)`. The norms are equivalent by
`Torus.periodicTriebelLizorkinNorm_zero_two_le` and
`Torus.enorm_le_periodicTriebelLizorkinNorm_zero_two`. -/
theorem periodicTriebelLizorkinSpace_zero_two_eq_top [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) :
    periodicTriebelLizorkinSpace (d := d) (p := p) 0 2 one_le_two = ⊤ :=
  Submodule.eq_top_iff'.2 fun f => memPeriodicTriebelLizorkin_zero_two hp1 hp f

/-- **`B^s_{p,min(p,2)}(𝕋^d) ⊆ F^s_{p,2}(𝕋^d)` for every `s ≥ 0`**: for `d ≥ 1` and
`1 < p < ∞`; for `s > 0` this is the Besov sandwich
(`Torus.memPeriodicTriebelLizorkin_of_memBesov`), and for `s = 0` the square function theorem gives
`F^0_{p,2}(𝕋^d) = L_p(𝕋^d)`. This is the torus form of `Rd.memTriebelLizorkin_two_of_memApprox`. -/
theorem memPeriodicTriebelLizorkin_two_of_memBesov [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ}
    (hs : 0 ≤ s) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : (trigScheme d).MemBesov volume p s (min p 2) f) : MemPeriodicTriebelLizorkin s 2 f := by
  rcases hs.lt_or_eq with hs | rfl
  · exact memPeriodicTriebelLizorkin_of_memBesov hp hs one_le_two hf
  · exact memPeriodicTriebelLizorkin_zero_two hp1 hp f

end Torus
