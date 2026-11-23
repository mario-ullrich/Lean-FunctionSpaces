/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Traces.BoundaryBesovNorm

/-!
# The norm of the trace space of `H^s(Ω)`

Let `Ω` be a bounded Lipschitz domain with boundary `Γ`, `1/2 < s < 3/2`, `H^s(Ω)` the Hilbert
space `Rd.RestrictionSpace s Ω`, and `Ω.TraceSpace s` the trace space of `H^s(Ω)`, the orthogonal
complement of the trace kernel in `H^s(Ω)` (`Rd.BoundedLipschitzDomain.TraceSpace`), with the
trace `γ_s` and the extension `E_s`. For `U ∈ H^s(V)` with `L_2` function `ι_s U`
(`Rd.sobolevToL2`), `Tr_Γ ι_s U` is its boundary trace, and `B^{s-1/2}_{2,2}(Γ)` carries the
quasi-norm by chart pieces (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`).

* **The least extension norm** (`Rd.BoundedLipschitzDomain.enorm_eq_iInf`): the norm of
  `t ∈ Ω.TraceSpace s` is the least `H^s(V)` norm of a function with the boundary trace of `t`,
  the quotient norm of `γ_s(H^s(Ω))`, which McLean, Theorem 3.38, shows to be equivalent to his
  chart norm of `H^{s-1/2}(Γ)`. The restriction to `Ω` keeps the boundary trace
  (`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`), and it does not increase the norm
  (`Rd.BoundedLipschitzDomain.enorm_trace_restrictProj_le`).
* **The norm equivalence** (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`): for every
  resolution of unity `ψ` there is `C < ∞` with `‖t‖ ≤ C ‖τ_s t‖_{B^{s-1/2}_{2,2}(Γ)}` and
  `‖τ_s t‖_{B^{s-1/2}_{2,2}(Γ)} ≤ C ‖t‖`: the trace bound for `p = q = L = 2` at smoothness
  `s - 1/2`, with `H^s(V) ⊆ B^s_{2,2}(V)` (`Rd.modNorm_sobolevToL2_le`), and the bounded
  extension with the bound of `H^s(V)` by `B^s_{2,2}(V)` (`Rd.enorm_le_modNorm_sobolevToL2`).
  Every `g ∈ B^{s-1/2}_{2,2}(Γ)` has a preimage under the trace of norm at most `C ‖g‖`
  (`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov_le`).
* **The range** of `τ_s : Ω.TraceSpace s → L_2(Γ)` is `B^{s-1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`).
* **The isomorphism with `B^{s-1/2}_{2,2}(Γ)`**
  (`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesov`): `τ_s` is an isomorphism of normed
  spaces of `Ω.TraceSpace s` onto the Banach space `Ω.BoundaryBesov 2 (s - 1 / 2) 2`
  (`Rd.BoundedLipschitzDomain.BoundaryBesov`). The trace `H^s(Ω) → B^{s-1/2}_{2,2}(Γ)` has a
  bounded linear right inverse, as in McLean, Theorem 3.38
  (`Rd.BoundedLipschitzDomain.traceRightInverse`).
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped ENNReal BesselPotentialSpace

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-- **A bound in `[0, ∞]` is a bound of norms**: `‖x‖ₑ ≤ C ‖y‖ₑ` with `C < ∞` gives
`‖x‖ ≤ C.toReal ‖y‖` for elements of seminormed groups (Mathlib's `toReal_enorm`,
`ENNReal.toReal_mono`). -/
theorem norm_le_toReal_mul_of_enorm_le {E F : Type*} [SeminormedAddGroup E]
    [SeminormedAddGroup F] {x : E} {y : F} {C : ℝ≥0∞} (hC : C ≠ ∞) (h : ‖x‖ₑ ≤ C * ‖y‖ₑ) :
    ‖x‖ ≤ C.toReal * ‖y‖ := by
  rw [← toReal_enorm x, ← toReal_enorm y, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC enorm_ne_top) h

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : BoundedLipschitzDomain V)

/-! ### The norm of the trace space as a least extension norm -/

/-- The trace of the restriction to `Ω` has norm at most that of `U ∈ H^s(V)`, `1/2 < s < 3/2`:
`‖γ_s(U|_Ω)‖ ≤ ‖U|_Ω‖ ≤ ‖U‖` (`Rd.BoundedLipschitzDomain.norm_trace_apply_le`,
`Rd.norm_restrictProj_apply_le`). -/
theorem enorm_trace_restrictProj_le (s : ℝ) (U : H^{s}(V)) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    ‖Ω.trace s hs hs' (restrictProj s Ω.toOpens U)‖ₑ ≤ ‖U‖ₑ :=
  enorm_le_iff_norm_le.2 ((Ω.norm_trace_apply_le s _ hs hs').trans (norm_restrictProj_apply_le U))

/-- **Functions with the boundary trace of `t` restrict to extensions of `t`**: for every
resolution of unity `ψ`, `U ∈ H^s(V)` and `t ∈ Ω.TraceSpace s`, if `Tr_Γ ι_s U = Tr_Γ ι_s(E_s t)`
almost everywhere on `Γ`, then `γ_s(U|_Ω) = t`
(`Rd.BoundedLipschitzDomain.boundaryTrace_restrictProj`,
`Rd.BoundedLipschitzDomain.trace_eq_iff`, `Rd.BoundedLipschitzDomain.trace_extend`). -/
theorem trace_restrictProj_eq (ψ : Ω.BoundaryPartition) {s : ℝ} {hs : 1 / 2 < s}
    {hs' : s < 3 / 2} {U : H^{s}(V)} {t : Ω.TraceSpace s hs hs'}
    (h : Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le
        ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))) :
    Ω.trace s hs hs' (restrictProj s Ω.toOpens U) = t :=
  ((Ω.trace_eq_iff ψ s _ _ hs hs').2 ((Ω.boundaryTrace_restrictProj ψ s U hs hs').trans h)).trans
    (Ω.trace_extend t)

/-- `‖t‖ ≤ ‖U‖` for every `U ∈ H^s(V)` with the boundary trace of `t ∈ Ω.TraceSpace s`, for every
resolution of unity (`Rd.BoundedLipschitzDomain.trace_restrictProj_eq`). -/
theorem enorm_le_of_boundaryTrace_eventuallyEq (ψ : Ω.BoundaryPartition) {s : ℝ}
    {hs : 1 / 2 < s} {hs' : s < 3 / 2} {U : H^{s}(V)} {t : Ω.TraceSpace s hs hs'}
    (h : Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)
      =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le
        ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))) :
    ‖t‖ₑ ≤ ‖U‖ₑ := by
  rw [← Ω.trace_restrictProj_eq ψ h]
  exact Ω.enorm_trace_restrictProj_le s U hs hs'

/-- **The norm of the trace space of `H^s(Ω)` is the least extension norm**, `1/2 < s < 3/2` (the
quotient norm of `γ_s(H^s(Ω))`, which McLean, Theorem 3.38, shows to be equivalent to his chart
norm of `H^{s-1/2}(Γ)`): for every resolution of unity `ψ` and `t ∈ Ω.TraceSpace s`,
`‖t‖ = inf {‖U‖ : U ∈ H^s(V), Tr_Γ ι_s U = Tr_Γ ι_s(E_s t) almost everywhere on Γ}`. Here the
trace space is defined by orthogonality; the infimum is attained at `U = E_s t`. -/
theorem enorm_eq_iInf (ψ : Ω.BoundaryPartition) {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (t : Ω.TraceSpace s hs hs') :
    ‖t‖ₑ = ⨅ (U : H^{s}(V)) (_ : Ω.boundaryTrace ψ two_ne_top 2
      (sobolevToL2 (one_half_pos.trans hs).le U) =ᶠ[Ω.aeBoundary] Ω.boundaryTrace ψ two_ne_top 2
        (sobolevToL2 (one_half_pos.trans hs).le
          ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))), ‖U‖ₑ :=
  le_antisymm (le_iInf₂ fun _ hU => Ω.enorm_le_of_boundaryTrace_eventuallyEq ψ hU)
    ((iInf₂_le ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V))
      EventuallyEq.rfl).trans_eq rfl)

/-! ### The norm equivalence with `B^{s-1/2}_{2,2}(Γ)` -/

/-- **The boundary trace of `H^s(V)` is bounded into `B^{s-1/2}_{2,2}(Γ)`**, `1/2 < s < 3/2`: for
every resolution of unity `ψ` there is `C < ∞` with
`‖Tr_Γ ι_s U‖_{B^{s-1/2}_{2,2}(Γ)} ≤ C ‖U‖` for every `U ∈ H^s(V)`: the trace bound
(`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le` at `p = q = L = 2` and
smoothness `s - 1/2`) and `H^s(V) ⊆ B^s_{2,2}(V)` with differences of order `2`
(`Rd.modNorm_sobolevToL2_le`). -/
theorem exists_boundaryBesovNorm_sobolevToL2_le (ψ : Ω.BoundaryPartition) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : H^{s}(V), Ω.boundaryBesovNorm 2 ψ (s - 1 / 2) 2
      (Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)) ≤ C * ‖U‖ₑ := by
  have hs0 : 0 < s := one_half_pos.trans hs
  have hs2 : s < ((2 : ℕ) : ℝ) := by norm_num; linarith
  obtain ⟨C, hC, hle⟩ := Ω.exists_boundaryBesovNorm_boundaryTrace_le ψ two_ne_top (L := 2)
    (s := s - 1 / 2) (sub_pos.2 hs) (by linarith) (by norm_num; linarith) one_le_two
  refine ⟨C * sobolevBesovConst V s 2,
    ENNReal.mul_ne_top hC (sobolevBesovConst_ne_top hs0 hs2), fun U => ?_⟩
  have hσ : s - 1 / 2 + 1 / (2 : ℝ≥0∞).toReal = s := by norm_num
  have h := hle (sobolevToL2 hs0.le U) (modNorm_sobolevToL2_lt_top hs (by linarith) U)
  rw [hσ] at h
  rw [mul_assoc]
  exact h.trans (mul_le_mul' le_rfl (modNorm_sobolevToL2_le hs0 hs2 U))

/-- **The trace of the trace space of `H^s(Ω)` is bounded into `B^{s-1/2}_{2,2}(Γ)`**: for every
resolution of unity `ψ` there is `C < ∞` with `‖Tr_Γ ι_s(E_s t)‖_{B^{s-1/2}_{2,2}(Γ)} ≤ C ‖t‖`
for every `t ∈ Ω.TraceSpace s`
(`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_sobolevToL2_le`, `‖E_s t‖ = ‖t‖`). -/
theorem exists_boundaryBesovNorm_extend_le (ψ : Ω.BoundaryPartition) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : Ω.TraceSpace s hs hs', Ω.boundaryBesovNorm 2 ψ (s - 1 / 2) 2
      (Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le
        ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))) ≤ C * ‖t‖ₑ := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_boundaryBesovNorm_sobolevToL2_le ψ s hs hs'
  exact ⟨C, hC, fun t => hle _⟩

/-- **A bounded extension from `B^{s-1/2}_{2,2}(Γ)` into `H^s(V)`**, `1/2 < s < 3/2`: for every
resolution of unity `ψ` there is `C < ∞` such that every `g ∈ B^{s-1/2}_{2,2}(Γ)` is
`Tr_Γ ι_s U` almost everywhere on `Γ` for some `U ∈ H^s(V)` with
`‖U‖ ≤ C ‖g‖_{B^{s-1/2}_{2,2}(Γ)}`: the bounded extension
(`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le` at `p = q = L = 2` and smoothness
`s - 1/2`) gives `F ∈ B^s_{2,2}(V)`, which is `ι_s U` for some `U ∈ H^s(V)`
(`Rd.exists_sobolevToL2_eq_of_modNorm_lt_top`) with
`‖U‖ ≤ Rd.sobolevBesovInvConst V s 2 ‖F‖_{B^s_{2,2}}` (`Rd.enorm_le_modNorm_sobolevToL2`). -/
theorem exists_sobolevToL2_boundaryTrace_eq_le (ψ : Ω.BoundaryPartition) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 g →
      ∃ U : H^{s}(V), ‖U‖ₑ ≤ C * Ω.boundaryBesovNorm 2 ψ (s - 1 / 2) 2 g ∧
        Ω.boundaryTrace ψ two_ne_top 2 (sobolevToL2 (one_half_pos.trans hs).le U)
          =ᶠ[Ω.aeBoundary] g := by
  have hs0 : 0 < s := one_half_pos.trans hs
  obtain ⟨C, hC, hle⟩ := Ω.exists_boundaryTrace_eq_le ψ two_ne_top le_rfl (s := s - 1 / 2)
    (sub_pos.2 hs) (by linarith) one_le_two
  refine ⟨sobolevBesovInvConst V s 2 * C,
    ENNReal.mul_ne_top (sobolevBesovInvConst_ne_top s 2) hC, fun g hg => ?_⟩
  obtain ⟨F, hFle, hFg⟩ := hle g hg
  have hσ : s - 1 / 2 + 1 / (2 : ℝ≥0∞).toReal = s := by norm_num
  rw [hσ] at hFle
  have hF := hFle.trans_lt (ENNReal.mul_lt_top hC.lt_top
    ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg))
  obtain ⟨U, rfl⟩ := exists_sobolevToL2_eq_of_modNorm_lt_top hs0 (r := 2)
    (by norm_num; linarith) hF
  refine ⟨U, ?_, hFg⟩
  rw [mul_assoc]
  exact (enorm_le_modNorm_sobolevToL2 hs0.le 2 U).trans (mul_le_mul' le_rfl hFle)

/-- **Bounded preimages under the trace**, `1/2 < s < 3/2`: for every resolution of unity `ψ`
there is `C < ∞` such that every `g ∈ B^{s-1/2}_{2,2}(Γ)` is `Tr_Γ ι_s(E_s t)` almost everywhere
on `Γ` for some `t ∈ Ω.TraceSpace s` with `‖t‖ ≤ C ‖g‖_{B^{s-1/2}_{2,2}(Γ)}`; `t = γ_s(U|_Ω)` for
the `U` of `Rd.BoundedLipschitzDomain.exists_sobolevToL2_boundaryTrace_eq_le`. By uniqueness
(`Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`) `t` is determined by `g`; the
linear right inverse is `Rd.BoundedLipschitzDomain.traceRightInverse`. -/
theorem exists_traceSpace_of_memBoundaryBesov_le (ψ : Ω.BoundaryPartition) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 g →
      ∃ t : Ω.TraceSpace s hs hs', Ω.boundaryTrace ψ two_ne_top 2
          (sobolevToL2 (one_half_pos.trans hs).le
            ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))
            =ᶠ[Ω.aeBoundary] g ∧
        ‖t‖ₑ ≤ C * Ω.boundaryBesovNorm 2 ψ (s - 1 / 2) 2 g := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_sobolevToL2_boundaryTrace_eq_le ψ s hs hs'
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨U, hU, hUg⟩ := hle g hg
  exact ⟨Ω.trace s hs hs' (restrictProj s Ω.toOpens U),
    ((Ω.boundaryTrace_extend_trace ψ s _ hs hs').trans
      (Ω.boundaryTrace_restrictProj ψ s U hs hs')).trans hUg,
    (Ω.enorm_trace_restrictProj_le s U hs hs').trans hU⟩

/-- **The norm of the trace space of `H^s(Ω)` is bounded by the norm of the boundary trace**: for
every resolution of unity `ψ` there is `C < ∞` with
`‖t‖ ≤ C ‖Tr_Γ ι_s(E_s t)‖_{B^{s-1/2}_{2,2}(Γ)}` for every `t ∈ Ω.TraceSpace s`: the bounded
preimage (`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov_le`) is `t`, since
elements of the trace space are determined by their boundary traces
(`Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`). -/
theorem exists_enorm_le_boundaryBesovNorm_extend (ψ : Ω.BoundaryPartition) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : Ω.TraceSpace s hs hs', ‖t‖ₑ ≤ C *
      Ω.boundaryBesovNorm 2 ψ (s - 1 / 2) 2 (Ω.boundaryTrace ψ two_ne_top 2
        (sobolevToL2 (one_half_pos.trans hs).le
          ((Ω.extend s hs hs' t : RestrictionSpace s Ω.toOpens) : H^{s}(V)))) := by
  obtain ⟨C, hC, hle⟩ := Ω.exists_traceSpace_of_memBoundaryBesov_le ψ s hs hs'
  refine ⟨C, hC, fun t => ?_⟩
  obtain ⟨t', ht', hle'⟩ := hle _ (Ω.memBoundaryBesov_extend ψ t)
  rwa [(Ω.boundaryTrace_extend_eventuallyEq_iff ψ t' t).1 ht'] at hle'

/-- **The trace space of `H^s(Ω)` and `B^{s-1/2}_{2,2}(Γ)` have equivalent norms**,
`1/2 < s < 3/2` (McLean, Theorem 3.38; following Schneider–Vybíral, Theorem 4.11, for
`p = q = 2`): for every resolution of unity `ψ` there is `C < ∞` with
`‖t‖ ≤ C ‖τ_s t‖_{B^{s-1/2}_{2,2}(Γ)}` and `‖τ_s t‖_{B^{s-1/2}_{2,2}(Γ)} ≤ C ‖t‖` for every
`t ∈ Ω.TraceSpace s`, with the trace `τ_s : Ω.TraceSpace s → L_2(Γ)`
(`Rd.BoundedLipschitzDomain.traceL2`). -/
theorem exists_traceL2_norm_equiv (ψ : Ω.BoundaryPartition) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : Ω.TraceSpace s hs hs',
      ‖t‖ₑ ≤ C * Ω.boundaryBesovNorm 2 ψ (s - 1 / 2) 2 (Ω.traceL2 s hs hs' t) ∧
        Ω.boundaryBesovNorm 2 ψ (s - 1 / 2) 2 (Ω.traceL2 s hs hs' t) ≤ C * ‖t‖ₑ := by
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_enorm_le_boundaryBesovNorm_extend ψ s hs hs'
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundaryBesovNorm_extend_le ψ s hs hs'
  refine ⟨max C₁ C₂, (max_lt hC₁.lt_top hC₂.lt_top).ne, fun t => ?_⟩
  rw [Ω.boundaryBesovNorm_congr ψ
    (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Ω.traceL2_apply_ae ψ t))]
  exact ⟨(h₁ t).trans (mul_le_mul' (le_max_left _ _) le_rfl),
    (h₂ t).trans (mul_le_mul' (le_max_right _ _) le_rfl)⟩

/-- **The range of the trace `Ω.TraceSpace s → L_2(Γ)` is `B^{s-1/2}_{2,2}(Γ)`**,
`1/2 < s < 3/2`: for every resolution of unity `ψ`, `g ∈ L_2(Γ)` is `τ_s t` for some
`t ∈ Ω.TraceSpace s` iff `g ∈ B^{s-1/2}_{2,2}(Γ)`
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
`Rd.BoundedLipschitzDomain.exists_traceL2_ae_eq`). -/
theorem mem_range_traceL2_iff (ψ : Ω.BoundaryPartition) (s : ℝ) (g : Ω.BoundaryL2)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    g ∈ LinearMap.range (Ω.traceL2 s hs hs' : Ω.TraceSpace s hs hs' →ₗ[ℂ] Ω.BoundaryL2) ↔
      Ω.MemBoundaryBesov 2 ψ (s - 1 / 2) 2 g := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact (Ω.memBoundaryBesov_extend ψ t).congr
      (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Ω.traceL2_apply_ae ψ t)))
  · intro hg
    obtain ⟨t, ht⟩ := Ω.exists_traceL2_ae_eq ψ s hg hs hs'
    exact ⟨t, Lp.ext ht⟩

/-! ### The isomorphism with `B^{s-1/2}_{2,2}(Γ)` -/

/-- The trace `t ↦ τ_s t` from the trace space of `H^s(Ω)`, `1/2 < s < 3/2`, into the Banach space
`B^{s-1/2}_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.BoundaryBesov`) as a linear map
(`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`). -/
noncomputable def traceSpaceToBoundaryBesov (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.TraceSpace s hs hs' →ₗ[ℂ] Ω.BoundaryBesov 2 (s - 1 / 2) 2 where
  toFun t := ⟨Ω.traceL2 s hs hs' t, (Ω.mem_range_traceL2_iff Ω.boundaryPartition s _ hs hs').1
    (LinearMap.mem_range.2 ⟨t, rfl⟩)⟩
  map_add' t t' := BoundaryBesov.ext (map_add (Ω.traceL2 s hs hs') t t')
  map_smul' c t := BoundaryBesov.ext (map_smul (Ω.traceL2 s hs hs') c t)

/-- The trace `Ω.TraceSpace s → B^{s-1/2}_{2,2}(Γ)` is bijective: injective by
`Rd.BoundedLipschitzDomain.traceL2_injective`, surjective by
`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`. -/
theorem traceSpaceToBoundaryBesov_bijective (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Function.Bijective (Ω.traceSpaceToBoundaryBesov s hs hs') := by
  refine ⟨fun t t' h => (Ω.traceL2_injective s hs hs') (congrArg BoundaryBesov.toLp h),
    fun b => ?_⟩
  obtain ⟨t, ht⟩ := LinearMap.mem_range.1
    ((Ω.mem_range_traceL2_iff Ω.boundaryPartition s b.toLp hs hs').2 b.mem)
  exact ⟨t, BoundaryBesov.ext ht⟩

/-- The trace `Ω.TraceSpace s → B^{s-1/2}_{2,2}(Γ)` as a linear isomorphism. -/
noncomputable def traceSpaceLinearEquiv (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.TraceSpace s hs hs' ≃ₗ[ℂ] Ω.BoundaryBesov 2 (s - 1 / 2) 2 :=
  LinearEquiv.ofBijective _ (Ω.traceSpaceToBoundaryBesov_bijective s hs hs')

/-- The linear isomorphism sends `t` to `τ_s t`. -/
theorem toLp_traceSpaceLinearEquiv {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (t : Ω.TraceSpace s hs hs') :
    (Ω.traceSpaceLinearEquiv s hs hs' t).toLp = Ω.traceL2 s hs hs' t :=
  rfl

/-- **The constant of the norm equivalence** of the trace space of `H^s(Ω)` with
`B^{s-1/2}_{2,2}(Γ)` for the canonical resolution of unity, a choice among the constants of
`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`. -/
noncomputable def traceNormConst (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : ℝ≥0∞ :=
  (Ω.exists_traceL2_norm_equiv Ω.boundaryPartition s hs hs').choose

/-- The constant of the norm equivalence is finite. -/
theorem traceNormConst_ne_top (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : Ω.traceNormConst s hs hs' ≠ ∞ :=
  (Ω.exists_traceL2_norm_equiv Ω.boundaryPartition s hs hs').choose_spec.1

/-- The two bounds of the norm equivalence with the constant `Ω.traceNormConst s`. -/
theorem traceNormConst_spec {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (t : Ω.TraceSpace s hs hs') :
    ‖t‖ₑ ≤ Ω.traceNormConst s hs hs' *
        Ω.boundaryBesovNorm 2 Ω.boundaryPartition (s - 1 / 2) 2 (Ω.traceL2 s hs hs' t) ∧
      Ω.boundaryBesovNorm 2 Ω.boundaryPartition (s - 1 / 2) 2 (Ω.traceL2 s hs hs' t) ≤
        Ω.traceNormConst s hs hs' * ‖t‖ₑ :=
  (Ω.exists_traceL2_norm_equiv Ω.boundaryPartition s hs hs').choose_spec.2 t

/-- `‖τ_s t‖_{B^{s-1/2}_{2,2}(Γ)} ≤ C ‖t‖` with `C = Ω.traceNormConst s`. -/
theorem norm_traceSpaceLinearEquiv_le {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (t : Ω.TraceSpace s hs hs') :
    ‖Ω.traceSpaceLinearEquiv s hs hs' t‖ ≤ (Ω.traceNormConst s hs hs').toReal * ‖t‖ := by
  refine norm_le_toReal_mul_of_enorm_le (Ω.traceNormConst_ne_top s hs hs') ?_
  rw [BoundaryBesov.enorm_eq, toLp_traceSpaceLinearEquiv]
  exact (Ω.traceNormConst_spec t).2

/-- `‖t‖ ≤ C ‖τ_s t‖_{B^{s-1/2}_{2,2}(Γ)}` with `C = Ω.traceNormConst s`, for the inverse map. -/
theorem norm_traceSpaceLinearEquiv_symm_le (s : ℝ) (b : Ω.BoundaryBesov 2 (s - 1 / 2) 2)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ‖(Ω.traceSpaceLinearEquiv s hs hs').symm b‖ ≤ (Ω.traceNormConst s hs hs').toReal * ‖b‖ := by
  have h := (Ω.traceNormConst_spec ((Ω.traceSpaceLinearEquiv s hs hs').symm b)).1
  have hb : Ω.traceL2 s hs hs' ((Ω.traceSpaceLinearEquiv s hs hs').symm b) = b.toLp :=
    congrArg BoundaryBesov.toLp ((Ω.traceSpaceLinearEquiv s hs hs').apply_symm_apply b)
  rw [hb, ← BoundaryBesov.enorm_eq] at h
  exact norm_le_toReal_mul_of_enorm_le (Ω.traceNormConst_ne_top s hs hs') h

/-- **The trace space of `H^s(Ω)` is isomorphic to `B^{s-1/2}_{2,2}(Γ)`**, `1/2 < s < 3/2`
(McLean, Theorem 3.38; following Schneider–Vybíral, Theorem 4.11, for `p = q = 2`): the trace
`t ↦ τ_s t` is an isomorphism of normed spaces from the trace space onto the Banach space
`B^{s-1/2}_{2,2}(Γ)` with the norm by chart pieces (Mathlib's
`LinearEquiv.toContinuousLinearEquivOfBounds`), with the bounds of
`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv` in both directions. -/
noncomputable def traceSpaceEquivBoundaryBesov (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.TraceSpace s hs hs' ≃L[ℂ] Ω.BoundaryBesov 2 (s - 1 / 2) 2 :=
  (Ω.traceSpaceLinearEquiv s hs hs').toContinuousLinearEquivOfBounds
    (Ω.traceNormConst s hs hs').toReal (Ω.traceNormConst s hs hs').toReal
    Ω.norm_traceSpaceLinearEquiv_le
    fun b => Ω.norm_traceSpaceLinearEquiv_symm_le s b hs hs'

/-- The isomorphism of normed spaces sends `t` to `τ_s t`. -/
theorem toLp_traceSpaceEquivBoundaryBesov {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (t : Ω.TraceSpace s hs hs') :
    (Ω.traceSpaceEquivBoundaryBesov s hs hs' t).toLp = Ω.traceL2 s hs hs' t :=
  rfl

/-- **The bounded linear right inverse of the trace**, `1/2 < s < 3/2` (as in McLean,
Theorem 3.38): the map `B^{s-1/2}_{2,2}(Γ) → H^s(Ω)`, `g ↦ E_s τ_s⁻¹ g`, the inverse of the
isomorphism `Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesov` followed by the extension
`E_s`. -/
noncomputable def traceRightInverse (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.BoundaryBesov 2 (s - 1 / 2) 2 →L[ℂ] RestrictionSpace s Ω.toOpens :=
  Ω.extend s hs hs' ∘L ((Ω.traceSpaceEquivBoundaryBesov s hs hs').symm :
    Ω.BoundaryBesov 2 (s - 1 / 2) 2 →L[ℂ] Ω.TraceSpace s hs hs')

/-- The trace of `E_s τ_s⁻¹ g` is `τ_s⁻¹ g` (`Rd.BoundedLipschitzDomain.trace_extend`). -/
theorem trace_traceRightInverse (s : ℝ) (b : Ω.BoundaryBesov 2 (s - 1 / 2) 2)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.trace s hs hs' (Ω.traceRightInverse s hs hs' b) =
      (Ω.traceSpaceEquivBoundaryBesov s hs hs').symm b :=
  Ω.trace_extend _

/-- **The right inverse inverts the trace**: `γ^s_{L_2}(E_s τ_s⁻¹ g) = g` in `L_2(Γ)` for every
`g ∈ B^{s-1/2}_{2,2}(Γ)`, with the trace `γ^s_{L_2} = τ_s ∘ γ_s : H^s(Ω) → L_2(Γ)`
(`Rd.BoundedLipschitzDomain.boundaryTraceL2`). -/
theorem boundaryTraceL2_traceRightInverse (s : ℝ) (b : Ω.BoundaryBesov 2 (s - 1 / 2) 2)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.boundaryTraceL2 s hs hs' (Ω.traceRightInverse s hs hs' b) = b.toLp := by
  change Ω.traceL2 s hs hs' (Ω.trace s hs hs' (Ω.traceRightInverse s hs hs' b)) = b.toLp
  rw [Ω.trace_traceRightInverse s b hs hs', ← Ω.toLp_traceSpaceEquivBoundaryBesov,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **The right inverse is bounded**: `‖E_s τ_s⁻¹ g‖ ≤ C ‖g‖_{B^{s-1/2}_{2,2}(Γ)}` with
`C = Ω.traceNormConst s`, since `E_s` is an isometry
(`Rd.BoundedLipschitzDomain.norm_extend_apply`,
`Rd.BoundedLipschitzDomain.norm_traceSpaceLinearEquiv_symm_le`). -/
theorem norm_traceRightInverse_le (s : ℝ) (b : Ω.BoundaryBesov 2 (s - 1 / 2) 2)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    ‖Ω.traceRightInverse s hs hs' b‖ ≤ (Ω.traceNormConst s hs hs').toReal * ‖b‖ :=
  (Ω.norm_extend_apply _).trans_le (Ω.norm_traceSpaceLinearEquiv_symm_le s b hs hs')

end BoundedLipschitzDomain

end Rd
