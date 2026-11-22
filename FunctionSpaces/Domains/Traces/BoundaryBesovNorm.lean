/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Lipschitz.SurfaceMeasure

/-!
# Besov spaces on the boundary of a bounded Lipschitz domain and the trace operator

Let `Ω` be a bounded Lipschitz domain with boundary `Γ`, charts `γ_j : H_j → V` and a smooth
resolution of unity `(ψ_j)` on `Γ` (`Rd.BoundedLipschitzDomain.BoundaryPartition`). Let
`1 ≤ p < ∞`, `0 < s < 1` and `1 ≤ q ≤ ∞`.

* **The quasi-norm** (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`; Schneider–Vybíral,
  Definition 3.3; Triebel 2002): `‖g‖_{B^s_{p,q}(Γ)}` is the sum over the charts of
  `‖G_j‖_{L_p(H_j)} + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q}` for the chart pieces
  `G_j = (ψ_j g) ∘ γ_j` (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_sum`). It is finite
  exactly on `B^s_{p,q}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundaryBesovNorm_lt_top`), sees `g` only
  almost everywhere on `Γ`, and it is subadditive and homogeneous.
* **The trace is bounded** (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`):
  `‖Tr_Γ F‖_{B^s_{p,q}(Γ)} ≤ C (‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q})`, chart by chart
  (`Rd.LipschitzGraph.exists_modNorm_trace_mulLp_le`).
* **The extension is bounded** (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le`): every
  `g ∈ B^s_{p,q}(Γ)` is `Tr_Γ F` almost everywhere on `Γ` for an `F` with
  `‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C ‖g‖_{B^s_{p,q}(Γ)}`, namely
  `F = ∑_j ζ_j E_j G_j` (`Rd.LipschitzGraph.exists_modNorm_mulLp_graphExtension_le`).
* **Independence of the resolution of unity**
  (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_le_of_partition`): two resolutions
  of unity give equivalent quasi-norms.

The constants depend on `Ω`, `ψ`, `p`, `s`, `q` and `L` and are fixed before the functions; the
bounds follow Schneider–Vybíral, Theorem 4.11, for `p ≥ 1`.

With the surface measure `σ` of `Γ` and the linearity of the boundary trace
(`Rd.BoundedLipschitzDomain.boundaryTrace_add`, `Rd.BoundedLipschitzDomain.boundaryTrace_smul`):

* **Chart pieces in `L_p`** (`Rd.BoundedLipschitzDomain.chartPieceLp`): `g ↦ (ψ_j g) ∘ γ_j` is a
  bounded operator `L_p(Γ) → L_p(H_j)` for every `1 ≤ p ≤ ∞`, and
  `‖g‖_{L_p(Γ)} ≤ C ‖g‖_{B^s_{p,q}(Γ)}`
  (`Rd.BoundedLipschitzDomain.exists_eLpNorm_le_boundaryBesovNorm`).
* **The Banach space `B^t_{p,q}(Γ)`** (`Rd.BoundedLipschitzDomain.BoundaryBesov`): the
  `g ∈ L_p(Γ)` in `B^t_{p,q}(Γ)` for the canonical resolution of unity, normed by the quasi-norm
  by chart pieces, `1 ≤ q ≤ ∞`; it is complete
  (`Rd.BoundedLipschitzDomain.completeSpace_boundaryBesov`), since Cauchy sequences converge in
  `L_p(Γ)` and, chart by chart, for the quasi-norms of the hyperplanes
  (`Rd.BoundedLipschitzDomain.tendsto_boundaryBesovNorm_sub_of_cauchy`).
* **The Besov trace** (`Rd.BoundedLipschitzDomain.besovTrace`; Schneider–Vybíral, Theorem 4.11;
  Mayboroda, Theorem 1.1.3(i)): for `1 ≤ p < ∞`, `1/p < s < 1 + 1/p` and `1 ≤ q ≤ ∞`, the bounded
  operator `B^s_{p,q}(Ω) → B^{s-1/p}_{p,q}(Γ)`, `f ↦ Tr_Γ F` for any extension `F` of `f` to `V`
  with a finite quasi-norm (`Rd.BoundedLipschitzDomain.besovTrace_ae`), where `B^s_{p,q}(Ω)` is the
  space of `Rd.BoundedLipschitzDomain.DomainBesov` with differences of order `2`. It is onto
  (`Rd.BoundedLipschitzDomain.besovTrace_surjective`).
* **A bounded linear right inverse** (`Rd.BoundedLipschitzDomain.besovExtend`; Mayboroda builds
  one in the proof of Theorem 1.1.3(i), (4.2.19)): for `0 < t < 1`,
  `g ↦ 1_Ω ∑_j ζ_j E_j G_j` with the chart pieces `G_j`, the extensions `E_j` of the graph domains
  and the cut-offs `ζ_j` of the canonical resolution of unity
  (`Rd.BoundedLipschitzDomain.besovExtendLp`, `Rd.BoundedLipschitzDomain.boundaryCutoff`), a
  bounded operator `B^t_{p,q}(Γ) → B^{t+1/p}_{p,q}(Ω)` whose trace is the identity
  (`Rd.BoundedLipschitzDomain.toLp_besovTrace_besovExtend`). It is linear since the extensions of
  the graph domains are (`Rd.LipschitzGraph.graphExtension_add`).
-/

@[expose] public section

open MeasureTheory Filter Metric Topology
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### The extension in one chart -/

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The localised extension is bounded**: for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞`, `L ≥ 2`
and a smooth `ζ` with derivatives bounded by `M` up to order `L`, there is `K < ∞` with
`‖ζ E g‖_p + ‖(2^(k(s+1/p)) ω_L(ζ E g, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖g‖_p + ‖(2^(ks) ω_1(g, 2^(-k))_p)_k‖_{ℓ_q})` for every `g ∈ B^s_{p,q}(H)`, with
`K = M_ζ 2^(L-2) K_E`: the multiplier bound (`Rd.modNorm_mulLp_le`), the change of the order of the
differences (`Rd.modNorm_order_le_of_le`) and the bound of the extension
(`Rd.LipschitzGraph.modNorm_graphExtension_le`). -/
theorem exists_modNorm_mulLp_graphExtension_le (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) {ζ : V → ℂ}
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) {M : ℝ}
    (hM : ∀ l ≤ L, ∀ x, ‖iteratedFDeriv ℝ l ζ x‖ ≤ M) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : Lp ℂ p (volume : Measure Ω.hyperplane),
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k) < ∞ →
      ‖mulLp hζ.continuous (norm_le_of_iteratedFDeriv_le hM) (Ω.graphExtension hp 1 g)‖ₑ +
          lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k * lpModulus p L
            (mulLp hζ.continuous (norm_le_of_iteratedFDeriv_le hM) (Ω.graphExtension hp 1 g)) k) ≤
        K * (‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k)) := by
  have hsL := add_one_div_toReal_lt hp hs1 hL
  obtain ⟨K, hK, hle⟩ := Ω.modNorm_graphExtension_le hp hs hs1 hq
  refine ⟨multiplierTotal (V := V) hp L (s + 1 / p.toReal) M * 2 ^ (L - 2) * K,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (multiplierTotal_ne_top hp hsL M) (by simp)) hK,
    fun g hg => ?_⟩
  calc _ ≤ multiplierTotal (V := V) hp L (s + 1 / p.toReal) M *
        (‖Ω.graphExtension hp 1 g‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k *
          lpModulus p L (Ω.graphExtension hp 1 g) k)) := modNorm_mulLp_le hp hζ hM hsL hq _
    _ ≤ multiplierTotal (V := V) hp L (s + 1 / p.toReal) M *
        (2 ^ (L - 2) * (‖Ω.graphExtension hp 1 g‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p 2 (Ω.graphExtension hp 1 g) k))) :=
        mul_le_mul' le_rfl (modNorm_order_le_of_le hL _ q _)
    _ ≤ multiplierTotal (V := V) hp L (s + 1 / p.toReal) M * (2 ^ (L - 2) *
        (K * (‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hle g hg))
    _ = _ := by ring

end LipschitzGraph

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : BoundedLipschitzDomain V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The quasi-norm -/

variable (p) in
/-- **The Besov quasi-norm on the boundary** (Schneider–Vybíral, Definition 3.3; Triebel 2002, with
Lebesgue measure on the hyperplanes): for a resolution of unity `ψ`,
`‖g‖_{B^s_{p,q}(Γ)} = ∑_j (‖G_j‖_{L_p(H_j)} + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q})` for the
chart pieces `G_j ∈ L_p(H_j)` with `G_j = (ψ_j g) ∘ γ_j` almost everywhere on `H_j`. Each infimum
runs over at most one element of `L_p(H_j)`, the class of the chart piece, and is `∞` if the chart
piece is not in `L_p(H_j)` (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_sum`). -/
noncomputable def boundaryBesovNorm (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) (g : V → ℂ) :
    ℝ≥0∞ :=
  ∑ j, ⨅ (G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (_ : (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')),
    (‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 G k))

/-- **The quasi-norm is at most the sum for chart pieces**: for `G_j = (ψ_j g) ∘ γ_j` almost
everywhere on `H_j`,
`‖g‖_{B^s_{p,q}(Γ)} ≤ ∑_j (‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q})`. -/
theorem boundaryBesovNorm_le_sum (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} {g : V → ℂ}
    (G : ∀ j, Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (hG : ∀ j, (G j : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) :
    Ω.boundaryBesovNorm p ψ s q g ≤
      ∑ j, (‖G j‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (G j) k)) :=
  Finset.sum_le_sum fun j _ => iInf₂_le (G j) (hG j)

/-- **The quasi-norm is the sum for chart pieces**: for `G_j = (ψ_j g) ∘ γ_j` almost everywhere on
`H_j`, `‖g‖_{B^s_{p,q}(Γ)} = ∑_j (‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q})`, since two
elements of `L_p(H_j)` that agree almost everywhere are equal. -/
theorem boundaryBesovNorm_eq_sum (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} {g : V → ℂ}
    (G : ∀ j, Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (hG : ∀ j, (G j : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) :
    Ω.boundaryBesovNorm p ψ s q g =
      ∑ j, (‖G j‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (G j) k)) := by
  refine le_antisymm (Ω.boundaryBesovNorm_le_sum ψ G hG)
    (Finset.sum_le_sum fun j _ => le_iInf₂ fun G' hG' => ?_)
  rw [Lp.ext ((hG j).trans hG'.symm)]

/-- **The quasi-norm is finite exactly on `B^s_{p,q}(Γ)`**: `g ∈ B^s_{p,q}(Γ)` iff
`‖g‖_{B^s_{p,q}(Γ)} < ∞`. -/
theorem memBoundaryBesov_iff_boundaryBesovNorm_lt_top (ψ : Ω.BoundaryPartition) {s : ℝ}
    {q : ℝ≥0∞} (g : V → ℂ) :
    Ω.MemBoundaryBesov p ψ s q g ↔ Ω.boundaryBesovNorm p ψ s q g < ∞ := by
  constructor
  · intro hg
    choose G hG hGfin using hg
    rw [Ω.boundaryBesovNorm_eq_sum ψ G hG]
    exact ENNReal.sum_lt_top.2 fun j _ => hGfin j
  · intro h j
    obtain ⟨G, hG⟩ := iInf_lt_iff.1 (ENNReal.sum_lt_top.1 h j (Finset.mem_univ j))
    obtain ⟨hGg, hGfin⟩ := iInf_lt_iff.1 hG
    exact ⟨G, hGg, hGfin⟩

/-- **The quasi-norm is infinite outside `B^s_{p,q}(Γ)`**: if `g ∉ B^s_{p,q}(Γ)`, then
`‖g‖_{B^s_{p,q}(Γ)} = ∞`
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundaryBesovNorm_lt_top`). -/
theorem boundaryBesovNorm_eq_top_of_not_mem (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    {g : V → ℂ} (hg : ¬ Ω.MemBoundaryBesov p ψ s q g) : Ω.boundaryBesovNorm p ψ s q g = ∞ :=
  not_lt_top_iff.1 fun h => hg ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).2 h)

/-- **The quasi-norm sees `g` only almost everywhere on `Γ`**: if `g = h` almost everywhere on
`Γ`, then `‖g‖_{B^s_{p,q}(Γ)} = ‖h‖_{B^s_{p,q}(Γ)}`. -/
theorem boundaryBesovNorm_congr (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} {g h : V → ℂ}
    (hgh : g =ᶠ[Ω.aeBoundary] h) :
    Ω.boundaryBesovNorm p ψ s q g = Ω.boundaryBesovNorm p ψ s q h := by
  refine Finset.sum_congr rfl fun j _ => iInf_congr fun G => ?_
  have hj := chart_ae_eq_of_eventuallyEq ψ hgh j
  exact iInf_congr_Prop ⟨fun hG => hG.trans hj, fun hG => hG.trans hj.symm⟩ fun _ => rfl

/-- The quasi-norm of `0` vanishes. -/
theorem boundaryBesovNorm_zero (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) :
    Ω.boundaryBesovNorm p ψ s q 0 = 0 := by
  rw [Ω.boundaryBesovNorm_eq_sum ψ (fun _ => 0) fun j => ?_]
  · simp [lpModulus_zero, ENNReal.lqNorm_zero_right]
  · exact (Lp.coeFn_zero ℂ p _).trans (Eventually.of_forall fun x' => by simp)

/-- **The quasi-norm is subadditive on `B^s_{p,q}(Γ)`**: for `q ≥ 1` and
`g, h ∈ B^s_{p,q}(Γ)`, `‖g + h‖_{B^s_{p,q}(Γ)} ≤ ‖g‖_{B^s_{p,q}(Γ)} + ‖h‖_{B^s_{p,q}(Γ)}`; the
chart pieces of `g + h` are the sums of those of `g` and `h` (`Rd.modNorm_add_le`). -/
theorem boundaryBesovNorm_add_le_of_mem (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) {g h : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g)
    (hh : Ω.MemBoundaryBesov p ψ s q h) :
    Ω.boundaryBesovNorm p ψ s q (g + h) ≤
      Ω.boundaryBesovNorm p ψ s q g + Ω.boundaryBesovNorm p ψ s q h := by
  choose G hG _ using hg
  choose H hH _ using hh
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Ω.boundaryBesovNorm_eq_sum ψ H hH,
    ← Finset.sum_add_distrib]
  refine (Ω.boundaryBesovNorm_le_sum ψ (fun j => G j + H j) fun j => ?_).trans
    (Finset.sum_le_sum fun j _ => modNorm_add_le (G j) (H j) 1 s hq)
  filter_upwards [Lp.coeFn_add (G j) (H j), hG j, hH j] with x' h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.add_apply, mul_add]

/-- **The quasi-norm is subadditive**: for `q ≥ 1` and all functions `g`, `h` on `V`,
`‖g + h‖_{B^s_{p,q}(Γ)} ≤ ‖g‖_{B^s_{p,q}(Γ)} + ‖h‖_{B^s_{p,q}(Γ)}`: for `g, h ∈ B^s_{p,q}(Γ)` by
`Rd.BoundedLipschitzDomain.boundaryBesovNorm_add_le_of_mem`; otherwise the right side is `∞`
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_top_of_not_mem`). -/
theorem boundaryBesovNorm_add_le (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g h : V → ℂ) :
    Ω.boundaryBesovNorm p ψ s q (g + h) ≤
      Ω.boundaryBesovNorm p ψ s q g + Ω.boundaryBesovNorm p ψ s q h := by
  by_cases hg : Ω.MemBoundaryBesov p ψ s q g
  · by_cases hh : Ω.MemBoundaryBesov p ψ s q h
    · exact Ω.boundaryBesovNorm_add_le_of_mem ψ hq hg hh
    · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hh, add_top]
      exact le_top
  · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg, top_add]
    exact le_top

variable {Ω} in
/-- `B^s_{p,q}(Γ)` is closed under addition, for `q ≥ 1`
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_add_le`). -/
theorem MemBoundaryBesov.add {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {g h : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) (hh : Ω.MemBoundaryBesov p ψ s q h) :
    Ω.MemBoundaryBesov p ψ s q (g + h) :=
  (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ _).2
    ((Ω.boundaryBesovNorm_add_le ψ hq g h).trans_lt (ENNReal.add_lt_top.2
      ⟨(Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg,
        (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ h).1 hh⟩))

/-- **The quasi-norm is homogeneous on `B^s_{p,q}(Γ)`**: for `c ∈ ℂ` and
`g ∈ B^s_{p,q}(Γ)`, `‖c g‖_{B^s_{p,q}(Γ)} = |c| ‖g‖_{B^s_{p,q}(Γ)}`; the chart pieces of `c g` are
`c G_j` (`Rd.modNorm_const_smul`). -/
theorem boundaryBesovNorm_const_smul_of_mem (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    (c : ℂ) {g : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) :
    Ω.boundaryBesovNorm p ψ s q (c • g) = ‖c‖ₑ * Ω.boundaryBesovNorm p ψ s q g := by
  choose G hG _ using hg
  have hcG : ∀ j, ((c • G j : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane)) :
      (Ω.graph j).hyperplane → ℂ) =ᵐ[volume] fun x' =>
        ψ.toComplex j ((Ω.graph j).graphMap x') * (c • g) ((Ω.graph j).graphMap x') := fun j => by
    filter_upwards [Lp.coeFn_smul c (G j), hG j] with x' h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Finset.mul_sum,
    Ω.boundaryBesovNorm_eq_sum ψ (fun j => c • G j) hcG]
  exact Finset.sum_congr rfl fun j _ => modNorm_const_smul c (G j) 1 s q

variable {Ω} in
/-- `B^s_{p,q}(Γ)` is closed under multiplication by constants
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_const_smul_of_mem`). -/
theorem MemBoundaryBesov.const_smul {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (c : ℂ)
    {g : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) : Ω.MemBoundaryBesov p ψ s q (c • g) := by
  rw [memBoundaryBesov_iff_boundaryBesovNorm_lt_top, Ω.boundaryBesovNorm_const_smul_of_mem ψ c hg]
  exact ENNReal.mul_lt_top enorm_lt_top
    ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg)

/-- **The quasi-norm is homogeneous**: for `c ∈ ℂ` and every function `g` on `V`,
`‖c g‖_{B^s_{p,q}(Γ)} = |c| ‖g‖_{B^s_{p,q}(Γ)}`. For `c = 0` both sides vanish; for `c ≠ 0`,
`c g ∈ B^s_{p,q}(Γ)` iff `g ∈ B^s_{p,q}(Γ)`, since `g = c⁻¹ (c g)`, and outside the space both
sides are `∞` (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_const_smul_of_mem`,
`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_top_of_not_mem`). -/
theorem boundaryBesovNorm_const_smul (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} (c : ℂ)
    (g : V → ℂ) :
    Ω.boundaryBesovNorm p ψ s q (c • g) = ‖c‖ₑ * Ω.boundaryBesovNorm p ψ s q g := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, enorm_zero, zero_mul]
    exact Ω.boundaryBesovNorm_zero ψ s q
  by_cases hg : Ω.MemBoundaryBesov p ψ s q g
  · exact Ω.boundaryBesovNorm_const_smul_of_mem ψ c hg
  have hcg : ¬ Ω.MemBoundaryBesov p ψ s q (c • g) := fun h => hg (by
    have h' := h.const_smul c⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h')
  rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hcg, Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg,
    ENNReal.mul_top (enorm_ne_zero.2 hc)]

/-- **Vanishing quasi-norm**: if `‖g‖_{B^s_{p,q}(Γ)} = 0`, then every chart piece
`(ψ_j g) ∘ γ_j` vanishes almost everywhere on `H_j`. -/
theorem chart_ae_eq_zero_of_boundaryBesovNorm_eq_zero (ψ : Ω.BoundaryPartition) {s : ℝ}
    {q : ℝ≥0∞} {g : V → ℂ} (h0 : Ω.boundaryBesovNorm p ψ s q g = 0) (j : Fin Ω.N) :
    (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) =ᵐ[volume]
      0 := by
  have hg : Ω.MemBoundaryBesov p ψ s q g :=
    (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).2 (h0 ▸ ENNReal.zero_lt_top)
  choose G hG _ using hg
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Finset.sum_eq_zero_iff] at h0
  have hG0 : G j = 0 := enorm_eq_zero.1 (add_eq_zero.1 (h0 j (Finset.mem_univ j))).1
  refine (hG j).symm.trans ?_
  rw [hG0]
  exact Lp.coeFn_zero ℂ p _

/-! ### The bounded trace and the bounded extension -/

/-- **The boundary trace is bounded** (following Schneider–Vybíral, Theorem 4.11, for `p ≥ 1`): for
`1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `s + 1/p < L` (so `L ≥ 1`), there is `C < ∞` with
`‖Tr_Γ F‖_{B^s_{p,q}(Γ)} ≤ C (‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q})` for every `F`
with a finite right side. The chart pieces of `Tr_Γ F` are the traces `Tr_j(ψ_j F)`
(`Rd.BoundedLipschitzDomain.trace_mulLp_ae_boundaryTrace`), bounded chart by chart
(`Rd.LipschitzGraph.exists_modNorm_trace_mulLp_le`); `C = ∑_j K_j`. -/
theorem exists_boundaryBesovNorm_boundaryTrace_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {L : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (hsL : s + 1 / p.toReal < L)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : Lp ℂ p (volume : Measure V), ‖F‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞ →
      Ω.boundaryBesovNorm p ψ s q (Ω.boundaryTrace ψ hp L F) ≤
        C * (‖F‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k)) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2
    (Nat.cast_pos.1 ((show (0 : ℝ) < s + 1 / p.toReal by positivity).trans hsL)).ne'
  choose M hM using fun j => exists_iteratedFDeriv_bound (ψ.contDiff_toComplex j)
    (ψ.hasCompactSupport_toComplex j) L
  choose K hK hle using fun j =>
    (Ω.graph j).exists_modNorm_trace_mulLp_le hp hs hs1 hsL hq (ψ.contDiff_toComplex j) (hM j)
  refine ⟨∑ j, K j, ENNReal.sum_ne_top.2 fun j _ => hK j, fun F hF => ?_⟩
  rw [Finset.sum_mul]
  exact (Ω.boundaryBesovNorm_le_sum ψ _ fun j =>
    Ω.trace_mulLp_ae_boundaryTrace ψ hp hL hs hsL hq hF j (hM j)).trans
    (Finset.sum_le_sum fun j _ => hle j F hF)

/-- **A bounded extension from the boundary** (following Schneider–Vybíral, Theorem 4.11, for
`p ≥ 1`): for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, there is `C < ∞` such that every
`g ∈ B^s_{p,q}(Γ)` is `Tr_Γ F` almost everywhere on `Γ` for some `F` with
`‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C ‖g‖_{B^s_{p,q}(Γ)}`. The function is
`F = ∑_j ζ_j E_j G_j` for the chart pieces `G_j` and the cut-offs `ζ_j`
(`Rd.BoundedLipschitzDomain.boundaryTrace_extensionSum_eventuallyEq`), with the triangle inequality
`Rd.modNorm_finsetSum_le` and the chart bounds
`Rd.LipschitzGraph.exists_modNorm_mulLp_graphExtension_le`; `C = ∑_j K_j`. -/
theorem exists_boundaryTrace_eq_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Ω.MemBoundaryBesov p ψ s q g →
      ∃ F : Lp ℂ p (volume : Measure V), ‖F‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) ≤
          C * Ω.boundaryBesovNorm p ψ s q g ∧
        Ω.boundaryTrace ψ hp L F =ᶠ[Ω.aeBoundary] g := by
  choose ζ hζs hζc hζB hζ1 using ψ.exists_cutoff
  choose M hM using fun j => exists_iteratedFDeriv_bound (hζs j) (hζc j) L
  choose K hK hle using fun j =>
    (Ω.graph j).exists_modNorm_mulLp_graphExtension_le hp hL hs hs1 hq (hζs j) (hM j)
  refine ⟨∑ j, K j, ENNReal.sum_ne_top.2 fun j _ => hK j, fun g hg => ?_⟩
  choose G hG hGfin using hg
  refine ⟨_, ?_, Ω.boundaryTrace_extensionSum_eventuallyEq ψ hp hL hs hs1 hq hζs hζB hζ1 hM G hG
    hGfin⟩
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Finset.mul_sum]
  refine (modNorm_finsetSum_le _ _ L _ hq).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (hle j (G j) (hGfin j)).trans
    (mul_le_mul' (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)) le_rfl)

/-- **The quasi-norms of two resolutions of unity are equivalent**: for `1 ≤ p < ∞`, `0 < s < 1`
and `1 ≤ q ≤ ∞` and resolutions of unity `ψ`, `ψ'` there is `C < ∞` with
`‖g‖_{B^s_{p,q}(Γ), ψ'} ≤ C ‖g‖_{B^s_{p,q}(Γ), ψ}` for every `g`. For `g ∈ B^s_{p,q}(Γ)`, the
bounded extension for `ψ` (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le`) gives `F` with
`Tr_Γ F = g`, the boundary traces of `ψ` and `ψ'` agree
(`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`), and the trace bound for `ψ'`
(`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`) finishes; otherwise the
right side is `∞`. -/
theorem exists_boundaryBesovNorm_le_of_partition (ψ ψ' : Ω.BoundaryPartition)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ,
      Ω.boundaryBesovNorm p ψ' s q g ≤ C * Ω.boundaryBesovNorm p ψ s q g := by
  have hsL := add_one_div_toReal_lt hp hs1 (le_refl 2)
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_boundaryTrace_eq_le ψ hp le_rfl hs hs1 hq
  obtain ⟨C₂, hC₂, h₂⟩ :=
    Ω.exists_boundaryBesovNorm_boundaryTrace_le ψ' hp hs hs1 hsL hq
  refine ⟨C₂ * C₁ + 1, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC₂ hC₁, ENNReal.one_ne_top⟩,
    fun g => ?_⟩
  by_cases hg : Ω.MemBoundaryBesov p ψ s q g
  · obtain ⟨F, hFle, hFg⟩ := h₁ g hg
    have hF := hFle.trans_lt (ENNReal.mul_lt_top hC₁.lt_top
      ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg))
    rw [← Ω.boundaryBesovNorm_congr ψ'
      ((Ω.boundaryTrace_eventuallyEq ψ' ψ hp one_le_two hs hsL hq hF).trans hFg)]
    calc _ ≤ C₂ * (‖F‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / (p.toReal)) k * lpModulus p 2 F k)) := h₂ F hF
      _ ≤ C₂ * (C₁ * Ω.boundaryBesovNorm p ψ s q g) := mul_le_mul' le_rfl hFle
      _ ≤ (C₂ * C₁ + 1) * Ω.boundaryBesovNorm p ψ s q g := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg, ENNReal.mul_top (by positivity)]
    exact le_top

/-! ### `B^s_{p,q}(Γ)` and the operations of `L_p(Γ)` -/

section SurfaceLp

variable {Ω} {p' : ℝ≥0∞}

/-- `B^s_{p,q}(Γ)` contains the class `0` of `L_{p'}(Γ)`, for every exponent `p'`. -/
theorem memBoundaryBesov_coe_zero (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) :
    Ω.MemBoundaryBesov p ψ s q ((0 : Lp ℂ p' Ω.surfaceMeasure) : V → ℂ) :=
  ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ 0).2
    ((Ω.boundaryBesovNorm_zero ψ s q).trans_lt ENNReal.zero_lt_top)).congr
    (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1
      (Lp.coeFn_zero ℂ p' Ω.surfaceMeasure)))

/-- `B^s_{p,q}(Γ)` is closed under the addition of `L_{p'}(Γ)`, for `q ≥ 1`
(`Rd.BoundedLipschitzDomain.MemBoundaryBesov.add`). -/
theorem MemBoundaryBesov.coe_add {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f g : Lp ℂ p' Ω.surfaceMeasure} (hf : Ω.MemBoundaryBesov p ψ s q f)
    (hg : Ω.MemBoundaryBesov p ψ s q g) :
    Ω.MemBoundaryBesov p ψ s q ((f + g : Lp ℂ p' Ω.surfaceMeasure) : V → ℂ) :=
  (hf.add hq hg).congr
    (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_add f g)))

/-- `B^s_{p,q}(Γ)` is closed under the scalar multiplication of `L_{p'}(Γ)`
(`Rd.BoundedLipschitzDomain.MemBoundaryBesov.const_smul`). -/
theorem MemBoundaryBesov.coe_smul {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (c : ℂ)
    {f : Lp ℂ p' Ω.surfaceMeasure} (hf : Ω.MemBoundaryBesov p ψ s q f) :
    Ω.MemBoundaryBesov p ψ s q ((c • f : Lp ℂ p' Ω.surfaceMeasure) : V → ℂ) :=
  (hf.const_smul c).congr
    (EventuallyEq.symm (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_smul c f)))

/-- `B^s_{p,q}(Γ)` is closed under the negation of `L_{p'}(Γ)`, the multiplication by `-1`. -/
theorem MemBoundaryBesov.coe_neg {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞}
    {f : Lp ℂ p' Ω.surfaceMeasure} (hf : Ω.MemBoundaryBesov p ψ s q f) :
    Ω.MemBoundaryBesov p ψ s q ((-f : Lp ℂ p' Ω.surfaceMeasure) : V → ℂ) := by
  rw [← neg_one_smul ℂ f]
  exact hf.coe_smul (-1)

end SurfaceLp

/-! ### Chart pieces in `L_p` -/

/-- **The `L_p` norm of a chart piece**: for `P > 0`,
`∫_{H_j} |ψ_j(γ_j x') g(γ_j x')|^P dx' ≤ D_j^P ∫_Γ |g|^P dσ` with `D_j = ψ.derivBound j`
(`Rd.BoundedLipschitzDomain.lintegral_chart_le`). -/
theorem lintegral_chartPiece_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {P : ℝ} (hP : 0 < P)
    (g : V → ℂ) :
    ∫⁻ x', ‖ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')‖ₑ ^ P ≤
      ENNReal.ofReal (ψ.derivBound j) ^ P * ∫⁻ y, ‖g y‖ₑ ^ P ∂Ω.surfaceMeasure := by
  refine (Ω.lintegral_chart_le j (fun y => ‖ψ.toComplex j y * g y‖ₑ ^ P) fun y hy =>
    ψ.mem_ball_of_ne_zero fun h => hy ?_).trans ?_
  · rw [ψ.toComplex_of_eq_zero h, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hP]
  · rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun y => ?_
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hP.le]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (ψ.enorm_toComplex_le j y) hP.le) le_rfl

omit [FiniteDimensional ℝ V] in
/-- **Chart pieces are measurable**: for a strongly measurable `g` on `V`, the chart piece
`(ψ_j g) ∘ γ_j` is strongly measurable on `H_j`, since `ψ_j` and `γ_j` are continuous. -/
theorem stronglyMeasurable_chartPiece (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {g : V → ℂ}
    (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x' =>
      ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x') :=
  ((ψ.contDiff_toComplex j).continuous.comp
    (Ω.graph j).continuous_graphMap).stronglyMeasurable.mul
    (hg.comp_measurable (Ω.graph j).continuous_graphMap.measurable)

/-- **The `L_p` norm of a chart piece, for every `1 ≤ p ≤ ∞`**: for a strongly measurable `g`,
`‖(ψ_j g) ∘ γ_j‖_{L_p(H_j)} ≤ D_j ‖g‖_{L_p(Γ)}` with `D_j = ψ.derivBound j`; for `p < ∞` by
`Rd.BoundedLipschitzDomain.lintegral_chartPiece_le`, for `p = ∞` since `σ`-null sets are null in
the charts (`Rd.BoundedLipschitzDomain.ae_graphMap_of_ae_surfaceMeasure`) and `ψ_j = 0` outside
`B_j`. -/
theorem eLpNorm_chartPiece_le (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {g : V → ℂ}
    (hg : StronglyMeasurable g) :
    eLpNorm (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) p
      volume ≤ ENNReal.ofReal (ψ.derivBound j) * eLpNorm g p Ω.surfaceMeasure := by
  have hm := (Ω.stronglyMeasurable_chartPiece ψ j hg).aestronglyMeasurable
    (μ := (volume : Measure (Ω.graph j).hyperplane))
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hm, eLpNorm_exponent_top hg.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    filter_upwards [Ω.ae_graphMap_of_ae_surfaceMeasure j
      (ae_le_eLpNormEssSup (f := g) (μ := Ω.surfaceMeasure))] with x' hx'
    by_cases hψ : ψ.toFun j ((Ω.graph j).graphMap x') = 0
    · rw [ψ.toComplex_of_eq_zero hψ, zero_mul, enorm_zero]
      exact zero_le
    · rw [enorm_mul]
      exact mul_le_mul' (ψ.enorm_toComplex_le j _) (hx' (ψ.mem_ball_of_ne_zero hψ))
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg.aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (ψ.derivBound j) ^ p.toReal *
          ∫⁻ y, ‖g y‖ₑ ^ p.toReal ∂Ω.surfaceMeasure) ^ (1 / p.toReal) :=
          ENNReal.rpow_le_rpow (Ω.lintegral_chartPiece_le ψ j hP g) (by positivity)
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hP.ne', ENNReal.rpow_one]

/-- The chart piece `(ψ_j g) ∘ γ_j` of `g ∈ L_p(Γ)` lies in `L_p(H_j)`
(`Rd.BoundedLipschitzDomain.eLpNorm_chartPiece_le`). -/
theorem memLp_chartPiece (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (g : Lp ℂ p Ω.surfaceMeasure) :
    MemLp (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) p
      volume :=
  memLp_iff.2 ((Ω.eLpNorm_chartPiece_le ψ j (Lp.stronglyMeasurable g)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top g)))

/-- **The chart piece as a linear map** `L_p(Γ) → L_p(H_j)`, `g ↦ (ψ_j g) ∘ γ_j`: additive and
homogeneous, since `σ`-almost everywhere identities hold almost everywhere in the chart where
`ψ_j ≠ 0` (`Rd.BoundedLipschitzDomain.chart_ae_eq_of_eventuallyEq`). -/
noncomputable def chartPieceLinear (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) :
    Lp ℂ p Ω.surfaceMeasure →ₗ[ℂ] Lp ℂ p (volume : Measure (Ω.graph j).hyperplane) where
  toFun g := (Ω.memLp_chartPiece ψ j g).toLp _
  map_add' g h := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [chart_ae_eq_of_eventuallyEq ψ
      (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_add g h)) j] with x' hx'
    simp only [Pi.add_apply] at hx' ⊢
    rw [hx', mul_add]
  map_smul' c g := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [chart_ae_eq_of_eventuallyEq ψ
      (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_smul c g)) j] with x' hx'
    simp only [Pi.smul_apply, smul_eq_mul] at hx' ⊢
    rw [hx', mul_left_comm]

/-- **The chart piece as a bounded operator** `L_p(Γ) → L_p(H_j)`, `g ↦ (ψ_j g) ∘ γ_j`, for every
`1 ≤ p ≤ ∞`, of norm at most `D_j = ψ.derivBound j`
(`Rd.BoundedLipschitzDomain.eLpNorm_chartPiece_le`). -/
noncomputable def chartPieceLp (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) :
    Lp ℂ p Ω.surfaceMeasure →L[ℂ] Lp ℂ p (volume : Measure (Ω.graph j).hyperplane) :=
  (Ω.chartPieceLinear ψ j).mkContinuous (ENNReal.ofReal (ψ.derivBound j)).toReal fun g => by
    change ‖(Ω.memLp_chartPiece ψ j g).toLp _‖ ≤ _
    rw [Lp.norm_toLp, ← toReal_enorm g, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) ?_
    rw [Lp.enorm_def]
    exact Ω.eLpNorm_chartPiece_le ψ j (Lp.stronglyMeasurable g)

/-- The chart piece in `L_p(H_j)` is `(ψ_j g) ∘ γ_j` almost everywhere on `H_j`. -/
theorem chartPieceLp_ae (ψ : Ω.BoundaryPartition) (j : Fin Ω.N)
    (g : Lp ℂ p Ω.surfaceMeasure) :
    (Ω.chartPieceLp ψ j g : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x') :=
  MemLp.coeFn_toLp (Ω.memLp_chartPiece ψ j g)

/-- **The quasi-norm on the boundary by the chart pieces in `L_p`**: for `g ∈ L_p(Γ)`,
`‖g‖_{B^s_{p,q}(Γ)} = ∑_j (‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q})` for the chart pieces
`G_j` of `Rd.BoundedLipschitzDomain.chartPieceLp`
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_sum`). -/
theorem boundaryBesovNorm_eq_sum_chartPieceLp (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞)
    (g : Lp ℂ p Ω.surfaceMeasure) :
    Ω.boundaryBesovNorm p ψ s q g = ∑ j, (‖Ω.chartPieceLp ψ j g‖ₑ +
      lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.chartPieceLp ψ j g) k)) :=
  Ω.boundaryBesovNorm_eq_sum ψ _ fun j => Ω.chartPieceLp_ae ψ j g

/-- **Each chart piece is bounded by the quasi-norm on the boundary**: for `g ∈ L_p(Γ)` and every
`j`, `‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q} ≤ ‖g‖_{B^s_{p,q}(Γ)}`. -/
theorem modNorm_chartPieceLp_le (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞)
    (g : Lp ℂ p Ω.surfaceMeasure) (j : Fin Ω.N) :
    ‖Ω.chartPieceLp ψ j g‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.chartPieceLp ψ j g) k) ≤
      Ω.boundaryBesovNorm p ψ s q g := by
  rw [Ω.boundaryBesovNorm_eq_sum_chartPieceLp ψ s q g]
  exact Finset.single_le_sum (f := fun j => ‖Ω.chartPieceLp ψ j g‖ₑ +
    lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.chartPieceLp ψ j g) k))
    (fun _ _ => zero_le) (Finset.mem_univ j)

/-- **`B^s_{p,q}(Γ)` by the chart pieces in `L_p`**: `g ∈ L_p(Γ)` lies in `B^s_{p,q}(Γ)` iff
every chart piece `G_j` has `‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem memBoundaryBesov_iff_chartPieceLp (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞)
    (g : Lp ℂ p Ω.surfaceMeasure) :
    Ω.MemBoundaryBesov p ψ s q g ↔ ∀ j, ‖Ω.chartPieceLp ψ j g‖ₑ +
      lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (Ω.chartPieceLp ψ j g) k) < ∞ := by
  rw [memBoundaryBesov_iff_boundaryBesovNorm_lt_top, Ω.boundaryBesovNorm_eq_sum_chartPieceLp,
    ENNReal.sum_lt_top]
  simp only [Finset.mem_univ, forall_const]

/-! ### The `L_p(Γ)` norm by the quasi-norm on the boundary -/

/-- **`L_p(Γ)` norms in a chart**: for `1 ≤ p ≤ ∞`, `g` almost everywhere strongly measurable for
`σ` and `G ∈ L_p(H_j)` with `G = (ψ_j g) ∘ γ_j` almost everywhere on `H_j`,
`‖ψ_j g‖_{L_p(Γ)} ≤ (1 + M_j²)^(1/(2p)) ‖G‖_{L_p(H_j)}` (the factor is `1` for `p = ∞`), since
`ψ_j g = 0` outside `B_j` and the density of `σ` in the chart is at most `√(1 + M_j²)`
(`Rd.BoundedLipschitzDomain.lintegral_le_chart`,
`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_ball_iff`). -/
theorem eLpNorm_mul_le_chart (ψ : Ω.BoundaryPartition) (j : Fin Ω.N) {g : V → ℂ}
    (hg : AEStronglyMeasurable g Ω.surfaceMeasure)
    {G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane)}
    (hG : (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) :
    eLpNorm (fun y => ψ.toComplex j y * g y) p Ω.surfaceMeasure ≤
      ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ (1 / p.toReal) * ‖G‖ₑ := by
  have hm : AEStronglyMeasurable (fun y => ψ.toComplex j y * g y) Ω.surfaceMeasure :=
    (ψ.contDiff_toComplex j).continuous.aestronglyMeasurable.mul hg
  have hout : ∀ y, ψ.toFun j y = 0 → ψ.toComplex j y * g y = 0 := fun y h => by
    rw [ψ.toComplex_of_eq_zero h, zero_mul]
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [ENNReal.toReal_top, div_zero, ENNReal.rpow_zero, one_mul, eLpNorm_exponent_top hm,
      Lp.enorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable G)]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    have h := (Ω.ae_surfaceMeasure_ball_iff j
      (P := fun y => ‖ψ.toComplex j y * g y‖ₑ ≤ eLpNormEssSup G volume)).2
      (by filter_upwards [hG, ae_le_eLpNormEssSup (f := (G : _ → ℂ)) (μ := volume)] with
            x' h1 h2 _
          rwa [← h1])
    filter_upwards [h] with y hy
    by_cases hψ : ψ.toFun j y = 0
    · rw [hout y hψ, enorm_zero]
      exact zero_le
    · exact hy (ψ.mem_ball_of_ne_zero hψ)
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have hGint : ∫⁻ x', ‖G x'‖ₑ ^ p.toReal = ∫⁻ x', ‖ψ.toComplex j ((Ω.graph j).graphMap x') *
        g ((Ω.graph j).graphMap x')‖ₑ ^ p.toReal :=
      lintegral_congr_ae (hG.mono fun x' hx' => by simp only [hx'])
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm, Lp.enorm_def,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable G), hGint,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    refine ENNReal.rpow_le_rpow ((Ω.lintegral_le_chart j _ fun y hy =>
      ψ.mem_ball_of_ne_zero fun h => hy ?_).trans_eq rfl) (by positivity)
    rw [hout y h, enorm_zero, ENNReal.zero_rpow_of_pos hP]

/-- **The `L_p(Γ)` norm is bounded by the quasi-norm on the boundary**: for `1 ≤ p ≤ ∞`, every
resolution of unity `ψ`, `s ∈ ℝ` and `q`, there is `C < ∞` with
`‖g‖_{L_p(Γ)} ≤ C ‖g‖_{B^s_{p,q}(Γ)}` for every `g` almost everywhere strongly measurable for
`σ`: `g = ∑_j ψ_j g` on `Γ`, the triangle inequality, and the chart bounds
`Rd.BoundedLipschitzDomain.eLpNorm_mul_le_chart`; `C = 1 + ∑_j (1 + M_j²)^(1/(2p))`, positive so
that `C · ∞ = ∞` outside `B^s_{p,q}(Γ)`. -/
theorem exists_eLpNorm_le_boundaryBesovNorm (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, AEStronglyMeasurable g Ω.surfaceMeasure →
      eLpNorm g p Ω.surfaceMeasure ≤ C * Ω.boundaryBesovNorm p ψ s q g := by
  set c : Fin Ω.N → ℝ≥0∞ := fun j => ENNReal.ofReal √(1 + (Ω.graph j).M ^ 2) ^ (1 / p.toReal)
  have hc : ∀ j, c j ≠ ∞ := fun j =>
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  refine ⟨1 + ∑ j, c j, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.sum_ne_top.2 fun j _ => hc j⟩, fun g hg => ?_⟩
  by_cases hmem : Ω.MemBoundaryBesov p ψ s q g
  · choose G hG _ using hmem
    have hsum : g =ᵐ[Ω.surfaceMeasure] ∑ j, fun y => ψ.toComplex j y * g y :=
      (Ω.ae_eq_sum_mul ψ g).trans (Eventually.of_forall fun y => by simp only [Finset.sum_apply])
    calc eLpNorm g p Ω.surfaceMeasure
        = eLpNorm (∑ j, fun y => ψ.toComplex j y * g y) p Ω.surfaceMeasure :=
          eLpNorm_congr_ae hsum
      _ ≤ ∑ j, eLpNorm (fun y => ψ.toComplex j y * g y) p Ω.surfaceMeasure :=
          eLpNorm_sum_le Fact.out
      _ ≤ ∑ j, (1 + ∑ i, c i) *
            (‖G j‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (G j) k)) :=
          Finset.sum_le_sum fun j _ => (Ω.eLpNorm_mul_le_chart ψ j hg (hG j)).trans
            (mul_le_mul' (show c j ≤ 1 + ∑ i, c i from (Finset.single_le_sum (f := c)
              (fun _ _ => zero_le) (Finset.mem_univ j)).trans le_add_self) le_self_add)
      _ = _ := by rw [← Finset.mul_sum, Ω.boundaryBesovNorm_eq_sum ψ G hG]
  · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hmem, ENNReal.mul_top (by simp)]
    exact le_top

/-! ### The Banach space `B^t_{p,q}(Γ)` -/

variable (p) in
/-- **The Besov space `B^t_{p,q}(Γ)`** on the boundary of a bounded Lipschitz domain: the
`g ∈ L_p(Γ)` that lie in `B^t_{p,q}(Γ)` for the canonical resolution of unity
`Rd.BoundedLipschitzDomain.boundaryPartition`, with the quasi-norm by chart pieces
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm`), a norm for `1 ≤ q ≤ ∞`. A structure around
`L_p(Γ)` that carries the norm by chart pieces; it is a Banach space
(`Rd.BoundedLipschitzDomain.completeSpace_boundaryBesov`). The structure is defined for every
`t`; it is the Besov space of Schneider–Vybíral, Definition 3.3, for `0 < t < 1`, where first
differences suffice. For `1 ≤ p < ∞` and `0 < t < 1` it is the range of the Besov trace
(`Rd.BoundedLipschitzDomain.besovTrace`, `Rd.BoundedLipschitzDomain.besovTrace_surjective`). -/
@[ext]
structure BoundaryBesov (t : ℝ) (q : ℝ≥0∞) where
  /-- The function in `L_p(Γ)`. -/
  toLp : Lp ℂ p Ω.surfaceMeasure
  /-- It lies in `B^t_{p,q}(Γ)`. -/
  mem : Ω.MemBoundaryBesov p Ω.boundaryPartition t q toLp

namespace BoundaryBesov

variable {Ω} {t : ℝ} {q : ℝ≥0∞}

/-- An element of `B^t_{p,q}(Γ)` is determined by its function in `L_p(Γ)`. -/
theorem toLp_injective :
    Function.Injective (toLp : Ω.BoundaryBesov p t q → Lp ℂ p Ω.surfaceMeasure) :=
  fun _ _ h => BoundaryBesov.ext h

/-- The zero function. -/
noncomputable instance instZero : Zero (Ω.BoundaryBesov p t q) :=
  ⟨⟨0, memBoundaryBesov_coe_zero _ _ _⟩⟩

/-- Complex multiples of a function of `B^t_{p,q}(Γ)`. -/
noncomputable instance instSMul : SMul ℂ (Ω.BoundaryBesov p t q) :=
  ⟨fun c a => ⟨c • a.toLp, a.mem.coe_smul c⟩⟩

/-- The negative of a function of `B^t_{p,q}(Γ)`. -/
noncomputable instance instNeg : Neg (Ω.BoundaryBesov p t q) :=
  ⟨fun a => ⟨-a.toLp, a.mem.coe_neg⟩⟩

/-- The sum of two functions of `B^t_{p,q}(Γ)`, for `q ≥ 1`. -/
noncomputable instance instAdd [Fact (1 ≤ q)] : Add (Ω.BoundaryBesov p t q) :=
  ⟨fun a b => ⟨a.toLp + b.toLp, a.mem.coe_add Fact.out b.mem⟩⟩

/-- The difference of two functions of `B^t_{p,q}(Γ)`, for `q ≥ 1`. -/
noncomputable instance instSub [Fact (1 ≤ q)] : Sub (Ω.BoundaryBesov p t q) :=
  ⟨fun a b => ⟨a.toLp - b.toLp, by
    rw [sub_eq_add_neg]
    exact a.mem.coe_add Fact.out b.mem.coe_neg⟩⟩

/-- Natural multiples of a function of `B^t_{p,q}(Γ)`. -/
noncomputable instance instSMulNat : SMul ℕ (Ω.BoundaryBesov p t q) :=
  ⟨fun n a => ⟨n • a.toLp, by
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    exact a.mem.coe_smul _⟩⟩

/-- Integer multiples of a function of `B^t_{p,q}(Γ)`. -/
noncomputable instance instSMulInt : SMul ℤ (Ω.BoundaryBesov p t q) :=
  ⟨fun n a => ⟨n • a.toLp, by
    rw [← Int.cast_smul_eq_zsmul ℂ]
    exact a.mem.coe_smul _⟩⟩

/-- `B^t_{p,q}(Γ)` is an additive group, a subgroup of `L_p(Γ)`, for `q ≥ 1`. -/
noncomputable instance instAddCommGroup [Fact (1 ≤ q)] : AddCommGroup (Ω.BoundaryBesov p t q) :=
  toLp_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The inclusion `B^t_{p,q}(Γ) → L_p(Γ)` as an additive map. -/
noncomputable def toLpAddMonoidHom [Fact (1 ≤ q)] :
    Ω.BoundaryBesov p t q →+ Lp ℂ p Ω.surfaceMeasure where
  toFun := toLp
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `B^t_{p,q}(Γ)` is a complex vector space, a subspace of `L_p(Γ)`, for `q ≥ 1`. -/
noncomputable instance instModule [Fact (1 ≤ q)] : Module ℂ (Ω.BoundaryBesov p t q) :=
  Function.Injective.module (R := ℂ) toLpAddMonoidHom toLp_injective fun _ _ => rfl

/-- **The norm of `B^t_{p,q}(Γ)`**: `‖g‖_{B^t_{p,q}(Γ)}` by chart pieces, for the canonical
resolution of unity. -/
noncomputable instance instNorm : Norm (Ω.BoundaryBesov p t q) :=
  ⟨fun a => (Ω.boundaryBesovNorm p Ω.boundaryPartition t q a.toLp).toReal⟩

/-- The norm of `B^t_{p,q}(Γ)` is `‖g‖_{B^t_{p,q}(Γ)}` by chart pieces. -/
protected theorem norm_def (a : Ω.BoundaryBesov p t q) :
    ‖a‖ = (Ω.boundaryBesovNorm p Ω.boundaryPartition t q a.toLp).toReal :=
  rfl

/-- The quasi-norm of an element of `B^t_{p,q}(Γ)` is finite. -/
theorem boundaryBesovNorm_lt_top (a : Ω.BoundaryBesov p t q) :
    Ω.boundaryBesovNorm p Ω.boundaryPartition t q a.toLp < ∞ :=
  (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top _ _).1 a.mem

/-- The norm is homogeneous (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_const_smul`). -/
protected theorem norm_smul (c : ℂ) (a : Ω.BoundaryBesov p t q) : ‖c • a‖ = ‖c‖ * ‖a‖ := by
  rw [BoundaryBesov.norm_def, BoundaryBesov.norm_def]
  change (Ω.boundaryBesovNorm p Ω.boundaryPartition t q
    ((c • a.toLp : Lp ℂ p Ω.surfaceMeasure) : V → ℂ)).toReal = _
  rw [Ω.boundaryBesovNorm_congr _
      (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_smul c a.toLp)),
    Ω.boundaryBesovNorm_const_smul _ c _, ENNReal.toReal_mul, toReal_enorm]

/-- The triangle inequality, for `q ≥ 1`
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_add_le`). -/
protected theorem norm_add_le [Fact (1 ≤ q)] (a b : Ω.BoundaryBesov p t q) :
    ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [BoundaryBesov.norm_def, BoundaryBesov.norm_def, BoundaryBesov.norm_def,
    ← ENNReal.toReal_add a.boundaryBesovNorm_lt_top.ne b.boundaryBesovNorm_lt_top.ne]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2
    ⟨a.boundaryBesovNorm_lt_top.ne, b.boundaryBesovNorm_lt_top.ne⟩) ?_
  change Ω.boundaryBesovNorm p Ω.boundaryPartition t q
    ((a.toLp + b.toLp : Lp ℂ p Ω.surfaceMeasure) : V → ℂ) ≤ _
  rw [Ω.boundaryBesovNorm_congr _
    (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_add a.toLp b.toLp))]
  exact Ω.boundaryBesovNorm_add_le _ Fact.out _ _

/-- **The norm is definite**: `‖g‖_{B^t_{p,q}(Γ)} = 0` iff `g = 0`; a vanishing norm makes all
chart pieces vanish (`Rd.BoundedLipschitzDomain.chart_ae_eq_zero_of_boundaryBesovNorm_eq_zero`),
hence `g = 0` almost everywhere on `Γ`
(`Rd.BoundedLipschitzDomain.eventuallyEq_zero_iff_forall_chart`). -/
protected theorem norm_eq_zero_iff [Fact (1 ≤ q)] (a : Ω.BoundaryBesov p t q) :
    ‖a‖ = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [BoundaryBesov.norm_def, ENNReal.toReal_eq_zero_iff] at h
    have h0 := h.resolve_right a.boundaryBesovNorm_lt_top.ne
    ext1
    change a.toLp = 0
    rw [Lp.eq_zero_iff_ae_eq_zero]
    exact Ω.ae_surfaceMeasure_iff_aeBoundary.2
      ((Ω.eventuallyEq_zero_iff_forall_chart Ω.boundaryPartition _).2
        (Ω.chart_ae_eq_zero_of_boundaryBesovNorm_eq_zero _ h0))
  · rintro rfl
    rw [BoundaryBesov.norm_def]
    change (Ω.boundaryBesovNorm p Ω.boundaryPartition t q
      ((0 : Lp ℂ p Ω.surfaceMeasure) : V → ℂ)).toReal = 0
    rw [Ω.boundaryBesovNorm_congr _
        (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (Lp.coeFn_zero ℂ p Ω.surfaceMeasure)),
      Ω.boundaryBesovNorm_zero, ENNReal.toReal_zero]

/-- The axioms of a normed space for `B^t_{p,q}(Γ)`, `q ≥ 1`. -/
theorem normedSpaceCore [Fact (1 ≤ q)] : NormedSpace.Core ℂ (Ω.BoundaryBesov p t q) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul := BoundaryBesov.norm_smul
  norm_triangle := BoundaryBesov.norm_add_le
  norm_eq_zero_iff := BoundaryBesov.norm_eq_zero_iff

/-- `B^t_{p,q}(Γ)` is a normed group, `q ≥ 1` (Mathlib's `NormedAddCommGroup.ofCore`). -/
noncomputable instance instNormedAddCommGroup [Fact (1 ≤ q)] :
    NormedAddCommGroup (Ω.BoundaryBesov p t q) :=
  NormedAddCommGroup.ofCore normedSpaceCore

/-- `B^t_{p,q}(Γ)` is a complex normed space, `q ≥ 1` (Mathlib's `NormedSpace.ofCore`). -/
noncomputable instance instNormedSpace [Fact (1 ≤ q)] : NormedSpace ℂ (Ω.BoundaryBesov p t q) :=
  NormedSpace.ofCore normedSpaceCore

/-- The extended norm of `g ∈ B^t_{p,q}(Γ)` is the quasi-norm `‖g‖_{B^t_{p,q}(Γ)}`. -/
theorem enorm_eq [Fact (1 ≤ q)] (a : Ω.BoundaryBesov p t q) :
    ‖a‖ₑ = Ω.boundaryBesovNorm p Ω.boundaryPartition t q a.toLp := by
  rw [← ofReal_norm, BoundaryBesov.norm_def, ENNReal.ofReal_toReal a.boundaryBesovNorm_lt_top.ne]

/-- **The inclusion `B^t_{p,q}(Γ) → L_p(Γ)`** as a bounded operator
(`Rd.BoundedLipschitzDomain.exists_eLpNorm_le_boundaryBesovNorm`). -/
noncomputable def toLpL [Fact (1 ≤ q)] : Ω.BoundaryBesov p t q →L[ℂ] Lp ℂ p Ω.surfaceMeasure :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := toLp
      map_add' _ _ := rfl
      map_smul' _ _ := rfl } (by
    obtain ⟨C, hC, hle⟩ :=
      Ω.exists_eLpNorm_le_boundaryBesovNorm (p := p) Ω.boundaryPartition t q
    refine ⟨C.toReal, fun a => ?_⟩
    change ‖a.toLp‖ ≤ C.toReal * ‖a‖
    rw [← toReal_enorm a.toLp, ← toReal_enorm a, ← ENNReal.toReal_mul, a.enorm_eq]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hC a.boundaryBesovNorm_lt_top.ne) ?_
    rw [Lp.enorm_def]
    exact hle _ (Lp.aestronglyMeasurable _))

/-- The inclusion `B^t_{p,q}(Γ) → L_p(Γ)` sends `g` to its function. -/
theorem toLpL_apply [Fact (1 ≤ q)] (a : Ω.BoundaryBesov p t q) : toLpL a = a.toLp :=
  rfl

end BoundaryBesov

/-- **Cauchy sequences for the quasi-norm on the boundary converge in it**: if `g_n → g` in
`L_p(Γ)`, `1 ≤ p ≤ ∞`, and `(g_n)` is a Cauchy sequence for `‖·‖_{B^s_{p,q}(Γ)}`, then
`‖g - g_n‖_{B^s_{p,q}(Γ)} → 0`. In each chart `G_j(g_n) → G_j(g)` in `L_p(H_j)`, since
`Rd.BoundedLipschitzDomain.chartPieceLp` is continuous, `(G_j(g_n))` is a Cauchy sequence for the
quasi-norm of `H_j` (`Rd.BoundedLipschitzDomain.modNorm_chartPieceLp_le`), and
`Rd.tendsto_modNormOn_sub_of_cauchy` applies on `U = H_j`. -/
theorem tendsto_boundaryBesovNorm_sub_of_cauchy (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    {f : ℕ → Lp ℂ p Ω.surfaceMeasure} {g : Lp ℂ p Ω.surfaceMeasure}
    (hfg : Tendsto f atTop (𝓝 g))
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      Ω.boundaryBesovNorm p ψ s q ((f m - f n : Lp ℂ p Ω.surfaceMeasure) : V → ℂ) ≤ ε) :
    Tendsto (fun n => Ω.boundaryBesovNorm p ψ s q
      ((g - f n : Lp ℂ p Ω.surfaceMeasure) : V → ℂ)) atTop (𝓝 0) := by
  have hj : ∀ j, Tendsto (fun n => modNormOn MeasurableSet.univ 1 s q
      (Ω.chartPieceLp ψ j g - Ω.chartPieceLp ψ j (f n))) atTop (𝓝 0) := fun j => by
    have hT : Tendsto (fun n => Ω.chartPieceLp ψ j (f n)) atTop (𝓝 (Ω.chartPieceLp ψ j g)) :=
      ((Ω.chartPieceLp ψ j).continuous.tendsto g).comp hfg
    refine tendsto_modNormOn_sub_of_cauchy MeasurableSet.univ 1 s q hT fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [modNormOn_univ, ← map_sub]
    exact (Ω.modNorm_chartPieceLp_le ψ s q _ j).trans (hN m hm n hn)
  have hsum := tendsto_finsetSum Finset.univ fun j _ => hj j
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr fun n => ?_
  rw [Ω.boundaryBesovNorm_eq_sum_chartPieceLp ψ s q]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [modNormOn_univ, map_sub]

/-- **`B^t_{p,q}(Γ)` is a Banach space**, `1 ≤ p ≤ ∞`, `1 ≤ q ≤ ∞`. A Cauchy sequence `(g_n)` is
a Cauchy sequence in `L_p(Γ)` (`Rd.BoundedLipschitzDomain.BoundaryBesov.toLpL`); for its limit
`g`, `‖g - g_n‖_{B^t_{p,q}(Γ)} → 0`
(`Rd.BoundedLipschitzDomain.tendsto_boundaryBesovNorm_sub_of_cauchy`), so `g ∈ B^t_{p,q}(Γ)` and
`g` is the limit in `B^t_{p,q}(Γ)`. -/
instance completeSpace_boundaryBesov {t : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] :
    CompleteSpace (Ω.BoundaryBesov p t q) := by
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    ((BoundaryBesov.toLpL : Ω.BoundaryBesov p t q →L[ℂ] Lp ℂ p Ω.surfaceMeasure
      ).uniformContinuous.comp_cauchySeq hu)
  have hg' : Tendsto (fun n => (u n).toLp) atTop (𝓝 g) := hg
  have hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, Ω.boundaryBesovNorm p Ω.boundaryPartition t q
      (((u m).toLp - (u n).toLp : Lp ℂ p Ω.surfaceMeasure) : V → ℂ) ≤ ε := fun ε hε => by
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rw [edist_eq_enorm_sub, BoundaryBesov.enorm_eq] at h
    exact h.le
  have hlim := Ω.tendsto_boundaryBesovNorm_sub_of_cauchy Ω.boundaryPartition hg' hC
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim 1 one_pos).exists
  have hmem : Ω.MemBoundaryBesov p Ω.boundaryPartition t q g := by
    have h := ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top _ _).2
      (hn.trans_lt ENNReal.one_lt_top)).coe_add Fact.out (u n).mem
    rwa [sub_add_cancel] at h
  refine ⟨⟨g, hmem⟩, tendsto_iff_edist_tendsto_0.2 (hlim.congr fun n => ?_)⟩
  rw [edist_comm, edist_eq_enorm_sub, BoundaryBesov.enorm_eq]
  rfl

/-! ### The Besov trace operator -/

/-- **The extension used by the Besov trace**: for `1 ≤ p < ∞`, `1/p < s < 1 + 1/p` and
`f ∈ B^s_{p,q}(Ω)`, an `F ∈ L_p(V)` with `F = f` on `Ω` and
`‖F‖_p + ‖(2^(ks) ω_2(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
(`Rd.BoundedLipschitzDomain.domainBesovExtension` with `r = 2`). -/
noncomputable def besovTraceExtension (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q) :
    Lp ℂ p (volume : Measure V) :=
  Ω.domainBesovExtension hp (besovTrace_index_bounds hp hs hs').2.2.1
    (besovTrace_index_bounds hp hs hs').2.2.2 Fact.out f

/-- The extension used by the Besov trace agrees with `f` on `Ω`
(`Rd.BoundedLipschitzDomain.indicatorLp_domainBesovExtension`). -/
theorem indicatorLp_besovTraceExtension (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q) :
    indicatorLp Ω.measurableSet (Ω.besovTraceExtension hp hs hs' f) = f.toLp :=
  Ω.indicatorLp_domainBesovExtension hp _ _ _ f

/-- The extension used by the Besov trace has a finite quasi-norm
(`Rd.BoundedLipschitzDomain.modNorm_domainBesovExtension_lt_top`). -/
theorem modNorm_besovTraceExtension_lt_top (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q) :
    ‖Ω.besovTraceExtension hp hs hs' f‖ₑ + lqNorm q (fun k =>
      dyadicWeight s k * lpModulus p 2 (Ω.besovTraceExtension hp hs hs' f) k) < ∞ :=
  Ω.modNorm_domainBesovExtension_lt_top hp _ _ _ f

/-- **The Besov trace of `f ∈ B^s_{p,q}(Ω)` in `L_p(Γ)`**, `1 ≤ p < ∞`, `1/p < s < 1 + 1/p`,
`1 ≤ q ≤ ∞`: the boundary trace `Tr_Γ F` of the extension `F` of
`Rd.BoundedLipschitzDomain.besovTraceExtension`, in `L_p(σ)`
(`Rd.BoundedLipschitzDomain.memLp_boundaryTrace` with `t = s - 1/p`). Every extension `F` of `f`
with a finite quasi-norm gives the same class
(`Rd.BoundedLipschitzDomain.besovTraceLp_ae`). -/
noncomputable def besovTraceLp (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q) :
    Lp ℂ p Ω.surfaceMeasure :=
  (Ω.memLp_boundaryTrace Ω.boundaryPartition hp one_le_two
    (besovTrace_index_bounds hp hs hs').1
    (by simpa only [sub_add_cancel] using (besovTrace_index_bounds hp hs hs').2.2.2)
    (q := q) Fact.out (F := Ω.besovTraceExtension hp hs hs' f)
    (by simpa only [sub_add_cancel] using Ω.modNorm_besovTraceExtension_lt_top hp hs hs' f)).toLp
    _

/-- **The Besov trace is the boundary trace of every extension**: for every `F ∈ L_p(V)` with
`1_Ω F = f` and `‖F‖_p + ‖(2^(ks) ω_2(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`, the Besov trace of `f` is
`Tr_Γ F` `σ`-almost everywhere (`Rd.BoundedLipschitzDomain.boundaryTrace_congr`). -/
theorem besovTraceLp_ae (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q)
    {F : Lp ℂ p (volume : Measure V)} (hF : indicatorLp Ω.measurableSet F = f.toLp)
    (hFfin : ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 2 F k) < ∞) :
    (Ω.besovTraceLp hp hs hs' f : V → ℂ) =ᵐ[Ω.surfaceMeasure]
      Ω.boundaryTrace Ω.boundaryPartition hp 2 F := by
  obtain ⟨ht0, -, -, hs2⟩ := besovTrace_index_bounds hp hs hs'
  have hE : ‖Ω.besovTraceExtension hp hs hs' f‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s - 1 / p.toReal + 1 / p.toReal) k *
        lpModulus p 2 (Ω.besovTraceExtension hp hs hs' f) k) < ∞ := by
    simpa only [sub_add_cancel] using Ω.modNorm_besovTraceExtension_lt_top hp hs hs' f
  have hF' : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s - 1 / p.toReal + 1 / p.toReal) k * lpModulus p 2 F k) < ∞ := by
    simpa only [sub_add_cancel] using hFfin
  refine (MemLp.coeFn_toLp _).trans (Ω.ae_surfaceMeasure_iff_aeBoundary.2 ?_)
  exact Ω.boundaryTrace_congr _ hp one_le_two ht0 (by rwa [sub_add_cancel]) Fact.out hE hF'
    (ae_eq_of_indicatorLp_eq Ω.measurableSet
      ((Ω.indicatorLp_besovTraceExtension hp hs hs' f).trans hF.symm))

/-- **The Besov trace lies in `B^{s-1/p}_{p,q}(Γ)`**
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_boundaryTrace`). -/
theorem memBoundaryBesov_besovTraceLp (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q) :
    Ω.MemBoundaryBesov p Ω.boundaryPartition (s - 1 / p.toReal) q
      (Ω.besovTraceLp hp hs hs' f) := by
  obtain ⟨ht0, ht1, -, hs2⟩ := besovTrace_index_bounds hp hs hs'
  have hE : ‖Ω.besovTraceExtension hp hs hs' f‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s - 1 / p.toReal + 1 / p.toReal) k *
        lpModulus p 2 (Ω.besovTraceExtension hp hs hs' f) k) < ∞ := by
    simpa only [sub_add_cancel] using Ω.modNorm_besovTraceExtension_lt_top hp hs hs' f
  exact (Ω.memBoundaryBesov_boundaryTrace _ hp one_le_two ht0 ht1 (by rwa [sub_add_cancel])
    Fact.out hE).congr
    (Ω.ae_surfaceMeasure_iff_aeBoundary.1 (MemLp.coeFn_toLp _).symm)

/-- **The Besov trace is additive**: the sum of the extensions of `f` and `g` is an extension of
`f + g` (`Rd.BoundedLipschitzDomain.besovTraceLp_ae`), and the boundary trace is additive
(`Rd.BoundedLipschitzDomain.boundaryTrace_add`). -/
theorem besovTraceLp_add (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f g : Ω.DomainBesov p 2 s q) :
    Ω.besovTraceLp hp hs hs' (f + g) = Ω.besovTraceLp hp hs hs' f + Ω.besovTraceLp hp hs hs' g := by
  obtain ⟨ht0, -, -, hs2⟩ := besovTrace_index_bounds hp hs hs'
  have hEf := Ω.modNorm_besovTraceExtension_lt_top hp hs hs' f
  have hEg := Ω.modNorm_besovTraceExtension_lt_top hp hs hs' g
  have hsum := (modNorm_add_le _ _ 2 s Fact.out).trans_lt (ENNReal.add_lt_top.2 ⟨hEf, hEg⟩)
  have hind : indicatorLp Ω.measurableSet (Ω.besovTraceExtension hp hs hs' f +
      Ω.besovTraceExtension hp hs hs' g) = (f + g).toLp := by
    rw [map_add, Ω.indicatorLp_besovTraceExtension, Ω.indicatorLp_besovTraceExtension]
    rfl
  have hf := Ω.besovTraceLp_ae hp hs hs' f (Ω.indicatorLp_besovTraceExtension hp hs hs' f) hEf
  have hg := Ω.besovTraceLp_ae hp hs hs' g (Ω.indicatorLp_besovTraceExtension hp hs hs' g) hEg
  have hadd := Ω.boundaryTrace_add Ω.boundaryPartition hp ht0
    (by rwa [sub_add_cancel]) Fact.out (by simpa only [sub_add_cancel] using hEf)
    (by simpa only [sub_add_cancel] using hEg)
  refine Lp.ext ((Ω.besovTraceLp_ae hp hs hs' (f + g) hind hsum).trans ?_)
  filter_upwards [Ω.ae_surfaceMeasure_iff_aeBoundary.2 hadd, hf, hg,
    Lp.coeFn_add (Ω.besovTraceLp hp hs hs' f) (Ω.besovTraceLp hp hs hs' g)] with y h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, Pi.add_apply, h2, h3]

/-- **The Besov trace is homogeneous**: `c F` is an extension of `c f`
(`Rd.BoundedLipschitzDomain.besovTraceLp_ae`), and the boundary trace is homogeneous
(`Rd.BoundedLipschitzDomain.boundaryTrace_smul`). -/
theorem besovTraceLp_smul (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (c : ℂ) (f : Ω.DomainBesov p 2 s q) :
    Ω.besovTraceLp hp hs hs' (c • f) = c • Ω.besovTraceLp hp hs hs' f := by
  obtain ⟨ht0, -, -, hs2⟩ := besovTrace_index_bounds hp hs hs'
  have hE := Ω.modNorm_besovTraceExtension_lt_top hp hs hs' f
  have hcE : ‖c • Ω.besovTraceExtension hp hs hs' f‖ₑ + lqNorm q (fun k =>
      dyadicWeight s k * lpModulus p 2 (c • Ω.besovTraceExtension hp hs hs' f) k) < ∞ := by
    rw [modNorm_const_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hE
  have hind : indicatorLp Ω.measurableSet (c • Ω.besovTraceExtension hp hs hs' f) =
      (c • f).toLp := by
    rw [map_smul, Ω.indicatorLp_besovTraceExtension]
    rfl
  have hf := Ω.besovTraceLp_ae hp hs hs' f (Ω.indicatorLp_besovTraceExtension hp hs hs' f) hE
  have hsmul := Ω.boundaryTrace_smul Ω.boundaryPartition hp ht0
    (by rwa [sub_add_cancel]) Fact.out c (by simpa only [sub_add_cancel] using hE)
  refine Lp.ext ((Ω.besovTraceLp_ae hp hs hs' (c • f) hind hcE).trans ?_)
  filter_upwards [Ω.ae_surfaceMeasure_iff_aeBoundary.2 hsmul, hf,
    Lp.coeFn_smul c (Ω.besovTraceLp hp hs hs' f)] with y h1 h2 h3
  rw [h1, h3, Pi.smul_apply, Pi.smul_apply, h2]

/-- **The bound of the Besov trace** (following Schneider–Vybíral, Theorem 4.11, for `p ≥ 1`):
there is `C < ∞` with `‖Tr_Γ f‖_{B^{s-1/p}_{p,q}(Γ)} ≤ C N_Ω(f)` for every `f ∈ B^s_{p,q}(Ω)`.
Rychkov's extension with a bound (`Rd.BoundedLipschitzDomain.exists_besov_extension_le`) and the
bound of the boundary trace
(`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`) give `C = C₂ C₁`. -/
theorem exists_boundaryBesovNorm_besovTraceLp_le (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Ω.DomainBesov p 2 s q,
      Ω.boundaryBesovNorm p Ω.boundaryPartition (s - 1 / p.toReal) q
        (Ω.besovTraceLp hp hs hs' f) ≤ C * ‖f‖ₑ := by
  obtain ⟨ht0, ht1, hs0, hs2⟩ := besovTrace_index_bounds hp hs hs'
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_besov_extension_le hp hs0 hs2 (Fact.out : 1 ≤ q)
  obtain ⟨C₂, hC₂, h₂⟩ := Ω.exists_boundaryBesovNorm_boundaryTrace_le Ω.boundaryPartition hp
    (L := 2) ht0 ht1 (by rwa [sub_add_cancel]) (Fact.out : 1 ≤ q)
  simp only [sub_add_cancel] at h₂
  refine ⟨C₂ * C₁, ENNReal.mul_ne_top hC₂ hC₁, fun f => ?_⟩
  obtain ⟨F, hFf, hFle⟩ := h₁ f.toLp f.mem
  have hF := hFle.trans_lt (ENNReal.mul_lt_top hC₁.lt_top f.mem)
  rw [Ω.boundaryBesovNorm_congr _ (Ω.ae_surfaceMeasure_iff_aeBoundary.1
    (Ω.besovTraceLp_ae hp hs hs' f (hFf.trans f.indicator_eq) hF)), DomainBesov.enorm_eq,
    mul_assoc]
  exact (h₂ F hF).trans (mul_le_mul' le_rfl hFle)

/-- **The trace operator `B^s_{p,q}(Ω) → B^{s-1/p}_{p,q}(Γ)`** (Schneider–Vybíral, Theorem 4.11;
Mayboroda, Theorem 1.1.3(i)), `1 ≤ p < ∞`, `1/p < s < 1 + 1/p`, `1 ≤ q ≤ ∞`: `f ↦ Tr_Γ F` for an
extension `F` of `f` with a finite quasi-norm on `V`, a bounded linear operator
(`Rd.BoundedLipschitzDomain.besovTraceLp_add`, `Rd.BoundedLipschitzDomain.besovTraceLp_smul`,
`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_besovTraceLp_le`). It is onto
(`Rd.BoundedLipschitzDomain.besovTrace_surjective`), with the bounded linear right inverse
`Rd.BoundedLipschitzDomain.besovExtend`. -/
noncomputable def besovTrace (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) :
    Ω.DomainBesov p 2 s q →L[ℂ] Ω.BoundaryBesov p (s - 1 / p.toReal) q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun f := ⟨Ω.besovTraceLp hp hs hs' f, Ω.memBoundaryBesov_besovTraceLp hp hs hs' f⟩
      map_add' f g := BoundaryBesov.ext (Ω.besovTraceLp_add hp hs hs' f g)
      map_smul' c f := BoundaryBesov.ext (Ω.besovTraceLp_smul hp hs hs' c f) } (by
    obtain ⟨C, hC, hle⟩ := Ω.exists_boundaryBesovNorm_besovTraceLp_le (q := q) hp hs hs'
    refine ⟨C.toReal, fun f => ?_⟩
    show (Ω.boundaryBesovNorm p Ω.boundaryPartition (s - 1 / p.toReal) q
      (Ω.besovTraceLp hp hs hs' f)).toReal ≤ C.toReal * ‖f‖
    rw [← toReal_enorm f, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC enorm_ne_top) (hle f))

/-- The Besov trace of `f` has the function `Rd.BoundedLipschitzDomain.besovTraceLp`. -/
theorem toLp_besovTrace (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q) :
    (Ω.besovTrace hp s q hs hs' f).toLp = Ω.besovTraceLp hp hs hs' f :=
  rfl

/-- **The Besov trace is the boundary trace of every extension**: for every `F ∈ L_p(V)` with
`1_Ω F = f` and `‖F‖_p + ‖(2^(ks) ω_2(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`,
`Tr_Γ f = Tr_Γ F` `σ`-almost everywhere (`Rd.BoundedLipschitzDomain.besovTraceLp_ae`). -/
theorem besovTrace_ae (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) (f : Ω.DomainBesov p 2 s q)
    {F : Lp ℂ p (volume : Measure V)} (hF : indicatorLp Ω.measurableSet F = f.toLp)
    (hFfin : ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 2 F k) < ∞) :
    ((Ω.besovTrace hp s q hs hs' f).toLp : V → ℂ) =ᵐ[Ω.surfaceMeasure]
      Ω.boundaryTrace Ω.boundaryPartition hp 2 F :=
  Ω.besovTraceLp_ae hp hs hs' f hF hFfin

/-! ### The linear right inverse -/

/-- **The cut-offs of the canonical resolution of unity**: smooth `ζ_j` with compact support,
`ζ_j ≠ 0` only in `B_j` and `ζ_j = 1` where `ψ_j ≠ 0`, for
`ψ = Rd.BoundedLipschitzDomain.boundaryPartition`; a choice among the cut-offs of
`Rd.BoundedLipschitzDomain.BoundaryPartition.exists_cutoff`. -/
noncomputable def boundaryCutoff (j : Fin Ω.N) : V → ℂ :=
  (Ω.boundaryPartition.exists_cutoff j).choose

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `ζ_j` is smooth. -/
theorem contDiff_boundaryCutoff (j : Fin Ω.N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ω.boundaryCutoff j) :=
  (Ω.boundaryPartition.exists_cutoff j).choose_spec.1

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `ζ_j` has compact support. -/
theorem hasCompactSupport_boundaryCutoff (j : Fin Ω.N) :
    HasCompactSupport (Ω.boundaryCutoff j) :=
  (Ω.boundaryPartition.exists_cutoff j).choose_spec.2.1

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `ζ_j` vanishes outside `B_j`. -/
theorem mem_ball_of_boundaryCutoff_ne_zero (j : Fin Ω.N) {y : V}
    (hy : Ω.boundaryCutoff j y ≠ 0) : y ∈ ball (Ω.center j) (Ω.radius j) :=
  (Ω.boundaryPartition.exists_cutoff j).choose_spec.2.2.1 y hy

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `ζ_j` is `1` where `ψ_j ≠ 0`. -/
theorem boundaryCutoff_eq_one (j : Fin Ω.N) {y : V}
    (hy : Ω.boundaryPartition.toFun j y ≠ 0) : Ω.boundaryCutoff j y = 1 :=
  (Ω.boundaryPartition.exists_cutoff j).choose_spec.2.2.2 y hy

/-- **A bound of the derivatives of `ζ_j`** up to order `2`, a choice among the bounds of
`Rd.exists_iteratedFDeriv_bound`. -/
noncomputable def boundaryCutoffBound (j : Fin Ω.N) : ℝ :=
  (exists_iteratedFDeriv_bound (Ω.contDiff_boundaryCutoff j)
    (Ω.hasCompactSupport_boundaryCutoff j) 2).choose

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivatives of `ζ_j` of order at most `2` are bounded by `Ω.boundaryCutoffBound j`. -/
theorem boundaryCutoffBound_spec (j : Fin Ω.N) :
    ∀ l ≤ 2, ∀ x, ‖iteratedFDeriv ℝ l (Ω.boundaryCutoff j) x‖ ≤ Ω.boundaryCutoffBound j :=
  (exists_iteratedFDeriv_bound (Ω.contDiff_boundaryCutoff j)
    (Ω.hasCompactSupport_boundaryCutoff j) 2).choose_spec

/-- **The extension from the boundary** `E_Γ g = ∑_j ζ_j E_j G_j` for `g ∈ L_p(Γ)`, `1 ≤ p < ∞`,
with the chart pieces `G_j = (ψ_j g) ∘ γ_j` (`Rd.BoundedLipschitzDomain.chartPieceLp`) of the
canonical resolution of unity, the extensions `E_j` of the graph domains
(`Rd.LipschitzGraph.graphExtension`, moment order `1`) and the cut-offs `ζ_j`
(`Rd.BoundedLipschitzDomain.boundaryCutoff`). The same operator serves every smoothness index. -/
noncomputable def besovExtendLp (hp : p ≠ ∞) (g : Lp ℂ p Ω.surfaceMeasure) :
    Lp ℂ p (volume : Measure V) :=
  ∑ j, mulLp (Ω.contDiff_boundaryCutoff j).continuous
    (norm_le_of_iteratedFDeriv_le (Ω.boundaryCutoffBound_spec j))
    ((Ω.graph j).graphExtension hp 1 (Ω.chartPieceLp Ω.boundaryPartition j g))

/-- **The extension from the boundary has a finite quasi-norm**: for `1 ≤ p < ∞`, `0 < t < 1`,
`1 ≤ q ≤ ∞` and `g ∈ B^t_{p,q}(Γ)`,
`‖E_Γ g‖_p + ‖(2^(k(t+1/p)) ω_2(E_Γ g, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
(`Rd.BoundedLipschitzDomain.modNorm_extensionSum_lt_top`). -/
theorem modNorm_besovExtendLp_lt_top (hp : p ≠ ∞) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {g : Lp ℂ p Ω.surfaceMeasure}
    (hg : Ω.MemBoundaryBesov p Ω.boundaryPartition t q g) :
    ‖Ω.besovExtendLp hp g‖ₑ + lqNorm q (fun k => dyadicWeight (t + 1 / p.toReal) k *
      lpModulus p 2 (Ω.besovExtendLp hp g) k) < ∞ :=
  Ω.modNorm_extensionSum_lt_top hp le_rfl ht ht1 hq Ω.contDiff_boundaryCutoff
    Ω.boundaryCutoffBound_spec _ ((Ω.memBoundaryBesov_iff_chartPieceLp _ t q g).1 hg)

/-- **The extension from the boundary is bounded** (following Schneider–Vybíral, Theorem 4.11,
for `p ≥ 1`): for `1 ≤ p < ∞`, `0 < t < 1` and `1 ≤ q ≤ ∞` there is `C < ∞` with
`‖E_Γ g‖_p + ‖(2^(k(t+1/p)) ω_2(E_Γ g, 2^(-k))_p)_k‖_{ℓ_q} ≤ C ‖g‖_{B^t_{p,q}(Γ)}` for every
`g ∈ B^t_{p,q}(Γ)`: the triangle inequality `Rd.modNorm_finsetSum_le` and the chart bounds
`Rd.LipschitzGraph.exists_modNorm_mulLp_graphExtension_le`, `C = ∑_j K_j`. -/
theorem exists_modNorm_besovExtendLp_le (hp : p ≠ ∞) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : Lp ℂ p Ω.surfaceMeasure,
      Ω.MemBoundaryBesov p Ω.boundaryPartition t q g →
      ‖Ω.besovExtendLp hp g‖ₑ + lqNorm q (fun k => dyadicWeight (t + 1 / p.toReal) k *
          lpModulus p 2 (Ω.besovExtendLp hp g) k) ≤
        C * Ω.boundaryBesovNorm p Ω.boundaryPartition t q g := by
  choose K hK hle using fun j => (Ω.graph j).exists_modNorm_mulLp_graphExtension_le hp le_rfl
    ht ht1 hq (Ω.contDiff_boundaryCutoff j) (Ω.boundaryCutoffBound_spec j)
  refine ⟨∑ j, K j, ENNReal.sum_ne_top.2 fun j _ => hK j, fun g hg => ?_⟩
  rw [Ω.boundaryBesovNorm_eq_sum_chartPieceLp, Finset.mul_sum]
  refine (modNorm_finsetSum_le _ _ 2 _ hq).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (hle j _ ((Ω.memBoundaryBesov_iff_chartPieceLp _ t q g).1 hg j)).trans
    (mul_le_mul' (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)) le_rfl)

/-- **The extension from the boundary is a right inverse of the boundary trace**: for
`1 ≤ p < ∞`, `0 < t < 1`, `1 ≤ q ≤ ∞` and `g ∈ B^t_{p,q}(Γ)`, `Tr_Γ E_Γ g = g` almost everywhere
on `Γ` (`Rd.BoundedLipschitzDomain.boundaryTrace_extensionSum_eventuallyEq`). -/
theorem boundaryTrace_besovExtendLp (hp : p ≠ ∞) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {g : Lp ℂ p Ω.surfaceMeasure}
    (hg : Ω.MemBoundaryBesov p Ω.boundaryPartition t q g) :
    Ω.boundaryTrace Ω.boundaryPartition hp 2 (Ω.besovExtendLp hp g) =ᶠ[Ω.aeBoundary] g :=
  Ω.boundaryTrace_extensionSum_eventuallyEq _ hp le_rfl ht ht1 hq Ω.contDiff_boundaryCutoff
    (fun j _ hy => Ω.mem_ball_of_boundaryCutoff_ne_zero j hy)
    (fun j _ hy => Ω.boundaryCutoff_eq_one j hy) Ω.boundaryCutoffBound_spec _
    (fun j => Ω.chartPieceLp_ae _ j g) ((Ω.memBoundaryBesov_iff_chartPieceLp _ t q g).1 hg)

/-- **The extension from the boundary is additive** on `B^t_{p,q}(Γ)`, `0 < t`, `1 ≤ q`: the chart
pieces are additive, and so are the extensions of the graph domains on functions with finite local
means quasi-norms (`Rd.LipschitzGraph.graphExtension_add`, `Rd.LocalMeansBump.localMeansNorm_le`)
and the multiplications by `ζ_j` (`Rd.mulLp_add`). -/
theorem besovExtendLp_add (hp : p ≠ ∞) {t : ℝ} (ht : 0 < t) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {g g' : Lp ℂ p Ω.surfaceMeasure} (hg : Ω.MemBoundaryBesov p Ω.boundaryPartition t q g)
    (hg' : Ω.MemBoundaryBesov p Ω.boundaryPartition t q g') :
    Ω.besovExtendLp hp (g + g') = Ω.besovExtendLp hp g + Ω.besovExtendLp hp g' := by
  have hloc : ∀ {h : Lp ℂ p Ω.surfaceMeasure},
      Ω.MemBoundaryBesov p Ω.boundaryPartition t q h → ∀ j,
        (Ω.graph j).graphBump.localMeansNorm hp 1 t q
          (Ω.chartPieceLp Ω.boundaryPartition j h) < ∞ := fun hh j =>
    ((Ω.graph j).graphBump.localMeansNorm_le hp 1 t hq _).trans_lt (ENNReal.mul_lt_top
      ((Ω.graph j).graphBump.upperConst_ne_top 1 t).lt_top
      ((Ω.memBoundaryBesov_iff_chartPieceLp _ t q _).1 hh j))
  unfold besovExtendLp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, (Ω.graph j).graphExtension_add hp 1 ht hq (hloc hg j) (hloc hg' j), mulLp_add]

/-- **The extension from the boundary is homogeneous**: `E_Γ(c g) = c E_Γ g` for every
`g ∈ L_p(Γ)` (`Rd.LipschitzGraph.graphExtension_smul`, `Rd.mulLp_smul`). -/
theorem besovExtendLp_smul (hp : p ≠ ∞) (c : ℂ) (g : Lp ℂ p Ω.surfaceMeasure) :
    Ω.besovExtendLp hp (c • g) = c • Ω.besovExtendLp hp g := by
  unfold besovExtendLp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, (Ω.graph j).graphExtension_smul, mulLp_smul]

/-- **The extension restricted to `Ω` is bounded by the extension**: for every smoothness `s`,
`N_Ω(1_Ω E_Γ g) ≤ ‖E_Γ g‖_p + ‖(2^(ks) ω_2(E_Γ g, 2^(-k))_p)_k‖_{ℓ_q}`
(`Rd.modNormOn_le_modNorm_of_indicatorLp`, `Rd.indicatorLp_indicatorLp`). -/
theorem modNormOn_indicatorLp_besovExtendLp_le (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞)
    (g : Lp ℂ p Ω.surfaceMeasure) :
    modNormOn Ω.measurableSet 2 s q (indicatorLp Ω.measurableSet (Ω.besovExtendLp hp g)) ≤
      ‖Ω.besovExtendLp hp g‖ₑ + lqNorm q (fun k => dyadicWeight s k *
        lpModulus p 2 (Ω.besovExtendLp hp g) k) :=
  modNormOn_le_modNorm_of_indicatorLp Ω.measurableSet 2 s q
    (indicatorLp_indicatorLp Ω.measurableSet _).symm

/-- **The bounded linear right inverse of the Besov trace**, `1 ≤ p < ∞`, `0 < t < 1`,
`1 ≤ q ≤ ∞`, a bounded linear right inverse as Mayboroda's `Ex` in the proof of Theorem 1.1.3(i),
(4.2.19); the extension of Schneider–Vybíral, Theorem 4.10, is non-linear, and their Theorem 4.11
gives the range of the trace. The operator `B^t_{p,q}(Γ) → B^{t+1/p}_{p,q}(Ω)`,
`g ↦ 1_Ω E_Γ g` (`Rd.BoundedLipschitzDomain.besovExtendLp`), linear
(`Rd.BoundedLipschitzDomain.besovExtendLp_add`, `Rd.BoundedLipschitzDomain.besovExtendLp_smul`)
and bounded (`Rd.BoundedLipschitzDomain.exists_modNorm_besovExtendLp_le`), with
`Tr_Γ ∘ besovExtend = id` (`Rd.BoundedLipschitzDomain.toLp_besovTrace_besovExtend`). -/
noncomputable def besovExtend (hp : p ≠ ∞) (t : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (ht : 0 < t)
    (ht1 : t < 1) : Ω.BoundaryBesov p t q →L[ℂ] Ω.DomainBesov p 2 (t + 1 / p.toReal) q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun g := ⟨indicatorLp Ω.measurableSet (Ω.besovExtendLp hp g.toLp),
        indicatorLp_indicatorLp _ _,
        (Ω.modNormOn_indicatorLp_besovExtendLp_le hp _ q _).trans_lt
          (Ω.modNorm_besovExtendLp_lt_top hp ht ht1 Fact.out g.mem)⟩
      map_add' g g' := DomainBesov.ext (by
        change indicatorLp Ω.measurableSet (Ω.besovExtendLp hp (g.toLp + g'.toLp)) = _
        rw [Ω.besovExtendLp_add hp ht Fact.out g.mem g'.mem, map_add]
        rfl)
      map_smul' c g := DomainBesov.ext (by
        change indicatorLp Ω.measurableSet (Ω.besovExtendLp hp (c • g.toLp)) = _
        rw [Ω.besovExtendLp_smul hp c, map_smul]
        rfl) } (by
    obtain ⟨C, hC, hle⟩ := Ω.exists_modNorm_besovExtendLp_le hp ht ht1 (Fact.out : 1 ≤ q)
    refine ⟨C.toReal, fun g => ?_⟩
    show (modNormOn Ω.measurableSet 2 (t + 1 / p.toReal) q
      (indicatorLp Ω.measurableSet (Ω.besovExtendLp hp g.toLp))).toReal ≤ C.toReal * ‖g‖
    rw [← toReal_enorm g, ← ENNReal.toReal_mul, BoundaryBesov.enorm_eq]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC g.boundaryBesovNorm_lt_top.ne)
      ((Ω.modNormOn_indicatorLp_besovExtendLp_le hp _ q _).trans (hle _ g.mem)))

/-- The right inverse sends `g` to `1_Ω E_Γ g`. -/
theorem toLp_besovExtend (hp : p ≠ ∞) {t : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] (ht : 0 < t)
    (ht1 : t < 1) (g : Ω.BoundaryBesov p t q) :
    (Ω.besovExtend hp t q ht ht1 g).toLp =
      indicatorLp Ω.measurableSet (Ω.besovExtendLp hp g.toLp) :=
  rfl

/-- **The Besov trace inverts the extension**: for `1 ≤ p < ∞`, `0 < t < 1`, `1 ≤ q ≤ ∞` and
`g ∈ B^t_{p,q}(Γ)`, the trace of `besovExtend g ∈ B^{t+1/p}_{p,q}(Ω)` is `g`
(`Rd.BoundedLipschitzDomain.besovTrace_ae` with the extension `E_Γ g`,
`Rd.BoundedLipschitzDomain.boundaryTrace_besovExtendLp`). The statement compares the functions in
`L_p(Γ)`, since the trace lands in `B^{(t+1/p)-1/p}_{p,q}(Γ)`, whose index is `t` only up to a
computation. -/
theorem toLp_besovTrace_besovExtend (hp : p ≠ ∞) {t : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (ht : 0 < t) (ht1 : t < 1) (g : Ω.BoundaryBesov p t q) :
    (Ω.besovTrace hp (t + 1 / p.toReal) q (by linarith) (by linarith)
      (Ω.besovExtend hp t q ht ht1 g)).toLp = g.toLp := by
  refine Lp.ext ((Ω.besovTrace_ae hp _ _ _ rfl
    (Ω.modNorm_besovExtendLp_lt_top hp ht ht1 Fact.out g.mem)).trans ?_)
  exact Ω.ae_surfaceMeasure_iff_aeBoundary.2
    (Ω.boundaryTrace_besovExtendLp hp ht ht1 Fact.out g.mem)

/-- **The Besov trace is onto**: for `1 ≤ p < ∞`, `1/p < s < 1 + 1/p` and `1 ≤ q ≤ ∞`, every
`g ∈ B^{s-1/p}_{p,q}(Γ)` is the trace of `1_Ω E_Γ g ∈ B^s_{p,q}(Ω)`, since `E_Γ g` is an extension
of it with a finite quasi-norm (`Rd.BoundedLipschitzDomain.besovTrace_ae`) and
`Tr_Γ E_Γ g = g` (`Rd.BoundedLipschitzDomain.boundaryTrace_besovExtendLp`). -/
theorem besovTrace_surjective (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) :
    Function.Surjective (Ω.besovTrace hp s q hs hs') := by
  intro g
  obtain ⟨ht0, ht1, -, -⟩ := besovTrace_index_bounds hp hs hs'
  have hE := Ω.modNorm_besovExtendLp_lt_top hp ht0 ht1 Fact.out g.mem
  rw [sub_add_cancel] at hE
  refine ⟨⟨indicatorLp Ω.measurableSet (Ω.besovExtendLp hp g.toLp), indicatorLp_indicatorLp _ _,
    (Ω.modNormOn_indicatorLp_besovExtendLp_le hp s q _).trans_lt hE⟩, ?_⟩
  refine BoundaryBesov.ext (Lp.ext ((Ω.besovTrace_ae hp hs hs' _ rfl hE).trans ?_))
  exact Ω.ae_surfaceMeasure_iff_aeBoundary.2
    (Ω.boundaryTrace_besovExtendLp hp ht0 ht1 Fact.out g.mem)

end BoundedLipschitzDomain

end Rd
