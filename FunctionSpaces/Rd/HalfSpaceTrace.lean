/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.HalfSpace
public import FunctionSpaces.Rd.GraphTraceCharts

/-!
# Traces of every order on the half-space

For the flat graph domain `Ω = {x : 0 < ⟪x, e⟫}` (`Rd.LipschitzGraph.flat`) the graph map is the
inclusion of `H = e^⊥` (`Rd.LipschitzGraph.flat_graphMap`), so the restrictions of smooth atoms
to `H` are smooth atoms of the same order (`Rd.LipschitzGraph.isSmoothAtom_comp_graphMap_flat`).
The trace atoms are therefore regular atoms of every order and exponent
(`Rd.LipschitzGraph.exists_trace_atoms_flat`), and the trace theorem holds for every `s > 0`:

`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_r(Tr f, 2^(-k))_p)_k‖_{ℓ_q}
  ≤ K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`   (`r > s`)

(`Rd.LipschitzGraph.modNorm_trace_le_flat`), where the Lipschitz case allows only `s < 1`.

**The extension of every order.** The extension `A(x) = a(Px) χ(2^j ⟪x, e⟫)` of a smooth atom on
`H` is a smooth atom on `V` of the same order
(`Rd.LipschitzGraph.exists_isSmoothAtom_extendAtom_flat`; for the flat graph the vertical cut-off
is `χ(2^j ⟪x, e⟫)`, `Rd.LipschitzGraph.vertCutoff_flat`).
With the terms `g_j = η_j ⋆ (k_j ⋆ g)` of the reproducing formula on `H` of moment order `Lh`,
the extension `E g = ∑_j g_j(Px) χ(2^j ⟪x, e⟫)` (`Rd.LipschitzGraph.flatExtension`) satisfies, for
`s > 0` and `s + 1/p < r`,

`‖E g‖_p + ‖(2^(k(s+1/p)) ω_r(E g, 2^(-k))_p)_k‖_{ℓ_q}
  ≤ K (‖g‖_{L_p(H)} + ‖(2^(ks) ω_{Lh}(g, 2^(-k))_p)_k‖_{ℓ_q})`

(`Rd.LipschitzGraph.modNorm_flatExtension_le`), and `Tr (E g) = g`
(`Rd.LipschitzGraph.trace_flatExtension`). Hence `B^s_{p,q}(H)` is the trace space of
`B^{s+1/p}_{p,q}` of the half-space for every `s > 0`
(`Rd.LipschitzGraph.exists_trace_eq_iff_flat`). The extension of the Lipschitz case uses moment
order `1` on `H` and reaches only `s < 1`; here the moment order `Lh > s` matches the smoothness.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal NNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-- **Derivatives of a composition with a linear map**:
`‖D^i (f ∘ L)(x)‖ ≤ ‖D^i f(L x)‖ ‖L‖^i`. -/
theorem norm_iteratedFDeriv_comp_clm_le {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] E) {f : E → F} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (x : G) {i : ℕ}
    (hi : (i : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ i (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * ‖L‖ ^ i := by
  rw [L.iteratedFDeriv_comp_right hf x hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (e : V) (he : ‖e‖ = 1)

/-! ### Restrictions of smooth atoms to the hyperplane -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The graph map of the flat graph is the inclusion of `H = e^⊥`. -/
theorem flat_graphMap (x' : (flat e he).hyperplane) : (flat e he).graphMap x' = x' := by
  simp [graphMap, flat]

/-- **Restrictions of smooth atoms to the hyperplane**: for the flat graph, a smooth atom on `V`
of order `K` with centre `c` restricts to a smooth atom on `H` of order `K` with centre `P c`,
the same radius factor and the same constant. -/
theorem isSmoothAtom_comp_graphMap_flat {K : ℕ} {d A : ℝ} {j : ℕ} {c : V}
    {a : V → ℂ} (ha : IsSmoothAtom Set.univ K d A j c a) :
    IsSmoothAtom Set.univ K d A j ((flat e he).proj c) (a ∘ (flat e he).graphMap) := by
  set Ω := flat e he
  set ι : Ω.hyperplane →L[ℝ] V := Ω.hyperplane.subtypeL
  have hγ : Ω.graphMap = ι := funext (flat_graphMap e he)
  have hι : ‖ι‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp [ι]
  have hac : ContDiff ℝ K a := contDiffOn_univ.1 ha.contDiffOn
  have hc : ContDiff ℝ K (a ∘ Ω.graphMap) := by
    rw [hγ]
    exact hac.comp ι.contDiff
  refine ⟨hc.continuous.aestronglyMeasurable,
    fun x' hx' => ha.eq_zero _ (hx'.trans_le (Ω.norm_sub_proj_le x' c)), hc.contDiffOn,
    fun l hl y _ => ?_⟩
  rw [iteratedFDerivWithin_univ, hγ]
  refine (norm_iteratedFDeriv_comp_clm_le ι hac y (by exact_mod_cast hl)).trans ?_
  have h1 := ha.norm_iteratedFDerivWithin_le l hl (ι y) (mem_univ _)
  rw [iteratedFDerivWithin_univ] at h1
  calc ‖iteratedFDeriv ℝ l a (ι y)‖ * ‖ι‖ ^ l ≤ (A * 2 ^ (j * l)) * 1 :=
        mul_le_mul h1 (pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg ι) hι) (by positivity)
          ((norm_nonneg _).trans h1)
    _ = A * 2 ^ (j * l) := mul_one _

/-! ### The trace of every order -/

/-- **The trace atoms of every order** on the flat graph: for every order `r ≥ 1` there are a
radius factor `d`, a constant `C < ∞` and an overlap bound `N` such that the restrictions
`a_{j,m} ∘ γ` of the cell atoms of `η_j ⋆ h` are regular atoms on `H` of order and exponent `r`
centred at `P c_{j,m}`, and the centres of the cells meeting `H` have overlap at most `N`. -/
theorem exists_trace_atoms_flat (b : LocalMeansBump V) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L : ℕ) {r : ℕ}
    (hr : 1 ≤ r) :
    ∃ (d : ℝ) (C : ℝ≥0∞) (N : ℕ), 0 ≤ d ∧ C ≠ ∞ ∧ ∀ (j : ℕ) {h : V → ℂ}, MemLp h p volume →
      (∀ m, IsRegularAtom p r r d C j ((flat e he).proj (cellCenter j m))
        (cellAtom p (b.dual L j) j h m ∘ (flat e he).graphMap)) ∧
      ∀ x' (S : Finset (Fin (finrank ℝ V) → ℤ)),
        (∀ m ∈ S, (flat e he).traceCoef b p L j h m ≠ 0 ∧
          ‖x' - (flat e he).proj (cellCenter j m)‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N := by
  set Ω := flat e he
  obtain ⟨A, hA, hsm⟩ := b.exists_isSmoothAtom_cellAtom hp1 L r
  set d := 2 * (L : ℝ) * b.radius + finrank ℝ V with hd_def
  have hd : 0 ≤ d :=
    add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg)
      (Nat.cast_nonneg _)
  have hint : (interior (Set.univ : Set Ω.hyperplane)).Nonempty := by
    rw [interior_univ]
    exact univ_nonempty
  refine ⟨d, ENNReal.ofReal (2 ^ r * (r : ℝ) ^ (r + 1) * A) *
      (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ Ω.hyperplane) *
        volume (ball (0 : Ω.hyperplane) 1))) ^ (1 / p.toReal),
    ⌈(2 * (3 * d + r) + 2) ^ finrank ℝ V⌉₊, hd, ?_, fun j h hh => ⟨fun m => ?_, fun x' S hS => ?_⟩⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)))
  · exact isRegularAtomOn_of_isSmoothAtom convex_univ MeasurableSet.univ hint hr le_rfl hd hA
      (isSmoothAtom_comp_graphMap_flat e he (hsm j hh m))
  · refine card_le_of_norm_sub_cellCenter_le j (by positivity) (x' : V) S fun m hm => ?_
    obtain ⟨hcoef, hdist⟩ := hS m hm
    obtain ⟨y', hy'⟩ : ∃ y', cellAtom p (b.dual L j) j h m (Ω.graphMap y') ≠ 0 := by
      by_contra hcon
      exact hcoef (by simp [traceCoef, hcon])
    have h1 : ‖Ω.graphMap y' - cellCenter j m‖ ≤ d / 2 ^ j :=
      not_lt.1 fun hlt => hy' ((hsm j hh m).eq_zero _ hlt)
    rw [flat_graphMap] at h1
    have h2 : ‖(y' : V) - (Ω.proj (cellCenter j m) : V)‖ ≤ d / 2 ^ j := by
      have h3 := Ω.norm_proj_le ((y' : V) - cellCenter j m)
      rw [map_sub, Ω.proj_coe] at h3
      rw [← Submodule.coe_sub, Submodule.norm_coe]
      exact h3.trans h1
    have h4 : ‖(x' : V) - (Ω.proj (cellCenter j m) : V)‖ ≤ (d + r) / 2 ^ j := by
      rw [← Submodule.coe_sub, Submodule.norm_coe]
      exact hdist
    calc ‖(x' : V) - cellCenter j m‖ = ‖((x' : V) - Ω.proj (cellCenter j m)) -
          ((y' : V) - Ω.proj (cellCenter j m)) + ((y' : V) - cellCenter j m)‖ := by
          congr 1
          abel
      _ ≤ ‖(x' : V) - Ω.proj (cellCenter j m)‖ + ‖(y' : V) - Ω.proj (cellCenter j m)‖ +
          ‖(y' : V) - cellCenter j m‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ (d + r) / 2 ^ j + d / 2 ^ j + d / 2 ^ j := add_le_add (add_le_add h4 h2) h1
      _ = (3 * d + r) / 2 ^ j := by ring

/-- **The trace of a series, of every order**: on the flat graph, for `0 < s < r` there is
`K < ∞` with `‖Tr‖_{L_p(H)} + ‖(2^(ks) ω_r(Tr, 2^(-k))_p)_k‖_{ℓ_q} ≤
K ‖(2^(j(s+1/p)) ‖h_j‖_p)_j‖_{ℓ_q}` for the trace `Tr = ∑_j (η_j ⋆ h_j) ∘ γ`. -/
theorem modNorm_traceSeries_le_flat (b : LocalMeansBump V) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (L : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞}
    (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ h : ℕ → Lp ℂ p (volume : Measure V),
      lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) < ∞ →
      ‖(flat e he).traceSeries b hp L h‖ₑ + lqNorm q (fun k =>
          dyadicWeight s k * lpModulus p r ((flat e he).traceSeries b hp L h) k) ≤
        K * lqNorm q (fun j => dyadicWeight (s + 1 / p.toReal) j * ‖h j‖ₑ) := by
  set Ω := flat e he
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨d, C, N, hd, hC, hatoms⟩ := exists_trace_atoms_flat e he b hp1 L hr
  refine ⟨atomSynthConst p N C r s r, atomSynthConst_ne_top hp1 N hC r hs hsr, fun h hX => ?_⟩
  have hsyn := modNorm_le_coeffNorm hp (fun j m => Ω.proj (cellCenter j m))
    (fun j m => cellAtom p (b.dual L j) j (h j) m ∘ Ω.graphMap)
    (fun j => Ω.traceCoef b p L j (h j))
    (fun j x' S hS => (hatoms j (Lp.memLp (h j))).2 x' S hS)
    (fun j m => (hatoms j (Lp.memLp (h j))).1 m)
    (fun j => (Ω.traceTerm_ae b hp L j (h j)).mono fun x' hx' =>
      hx'.trans (Ω.traceFun_eq_tsum b hp1 L j (Lp.memLp (h j)) x'))
    (Ω.tendsto_sum_traceTerm b hp L hs hq hX) hs hsr hq
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

/-- **The trace theorem of every order on the half-space**: for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞` there is `K < ∞` with
`‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_r(Tr f, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`. -/
theorem modNorm_trace_le_flat {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (L : ℕ) {r : ℕ}
    (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s) (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      ‖(flat e he).cutoff f‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulusOn p (flat e he).domain L f k) < ∞ →
      ‖(flat e he).trace hp L f‖ₑ +
          lqNorm q (fun k => dyadicWeight s k * lpModulus p r ((flat e he).trace hp L f) k) ≤
        K * (‖(flat e he).cutoff f‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulusOn p (flat e he).domain L f k)) := by
  set Ω := flat e he
  obtain ⟨K, hK, hle⟩ := modNorm_traceSeries_le_flat e he Ω.coneBump hp L hr hs hsr hq
  refine ⟨K * Ω.intrinsicConst L, ENNReal.mul_ne_top hK (Ω.intrinsicConst_ne_top L),
    fun f hf => ?_⟩
  have hX := Ω.intrinsicNorm_lt_top hp L (s + 1 / p.toReal) hq hf
  rw [mul_assoc]
  exact (hle (fun j => Ω.cutoff (Ω.coneBump.localMean hp L j f)) hX).trans
    (mul_le_mul' le_rfl (Ω.intrinsicNorm_le hp L (s + 1 / p.toReal) hq f))

/-! ### Extended atoms of every order -/

/-- The mollified graph of the flat graph vanishes. -/
theorem smoothGraph_flat (j : ℕ) (x' : (flat e he).hyperplane) :
    (flat e he).smoothGraph j x' = 0 := by
  have h : (flat e he).graphFun = 0 := funext fun x' => by simp [graphFun, flat]
  simp [smoothGraph, h, conv, convolution_zero]

/-- The vertical cut-off of the flat graph is `v_j(x) = χ(2^j ⟪x, e⟫)`. -/
theorem vertCutoff_flat (j : ℕ) (x : V) :
    (flat e he).vertCutoff j x = (flat e he).profile (2 ^ j * inner ℝ x e) := by
  rw [vertCutoff, vertCoord, smoothGraph_flat, sub_zero]
  rfl

/-- **Extended atoms of every order**: for the flat graph and every order `K` there is `B ≥ 0`
such that the extension `A(x) = a(Px) χ(2^j ⟪x, e⟫)` of a smooth atom `a` on `H` of order `K`,
level `j`, radius factor `d` and constant `A` is a smooth atom on `V` of order `K` with radius
factor `extendRadius d`, constant `2^K B A` and centre `c'`, by Leibniz's rule. -/
theorem exists_isSmoothAtom_extendAtom_flat (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {d A : ℝ} {j : ℕ} {c' : (flat e he).hyperplane}
      {a : (flat e he).hyperplane → ℂ}, 0 ≤ A → IsSmoothAtom Set.univ K d A j c' a →
      IsSmoothAtom Set.univ K ((flat e he).extendRadius d) (2 ^ K * B * A) j
        ((flat e he).extendCenter j c') ((flat e he).extendAtom j a) := by
  set Ω := flat e he
  obtain ⟨B₀, hB₀⟩ := exists_iteratedFDeriv_bound Ω.contDiff_profile Ω.hasCompactSupport_profile K
  refine ⟨|B₀|, abs_nonneg _, fun {d A j c' a} hA ha => ?_⟩
  set P : V →L[ℝ] Ω.hyperplane := Ω.proj
  set ℓ : V →L[ℝ] ℝ := (2 ^ j : ℝ) • innerSL ℝ e
  have hℓx : ∀ x, ℓ x = 2 ^ j * inner ℝ x e := fun x => by
    simp [ℓ, real_inner_comm]
  have hext : Ω.extendAtom j a = fun x => (a ∘ P) x * (Ω.profile ∘ ℓ) x := funext fun x => by
    rw [extendAtom, vertCutoff_flat, Function.comp_apply, Function.comp_apply, hℓx]
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact Ω.norm_proj_le x
  have hℓ : ‖ℓ‖ ≤ 2 ^ j := ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => by
    rw [hℓx, norm_mul, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact (norm_inner_le_norm x e).trans (by rw [he, mul_one])
  have hac : ContDiff ℝ K a := contDiffOn_univ.1 ha.contDiffOn
  have h1 : ContDiff ℝ K (a ∘ P) := hac.comp P.contDiff
  have h2 : ContDiff ℝ K (Ω.profile ∘ ℓ) :=
    (Ω.contDiff_profile.of_le (by exact_mod_cast le_top)).comp ℓ.contDiff
  have hc : ContDiff ℝ K (Ω.extendAtom j a) := by
    rw [hext]
    exact h1.mul h2
  refine ⟨hc.continuous.aestronglyMeasurable, fun x hx => Ω.extendAtom_eq_zero j ha.eq_zero hx,
    hc.contDiffOn, fun l hl y _ => ?_⟩
  have hu : ∀ i ≤ K, ‖iteratedFDeriv ℝ i (a ∘ P) y‖ ≤ A * 2 ^ (j * i) := fun i hi => by
    refine (norm_iteratedFDeriv_comp_clm_le P hac y (by exact_mod_cast hi)).trans ?_
    have h := ha.norm_iteratedFDerivWithin_le i hi (P y) (mem_univ _)
    rw [iteratedFDerivWithin_univ] at h
    calc ‖iteratedFDeriv ℝ i a (P y)‖ * ‖P‖ ^ i ≤ (A * 2 ^ (j * i)) * 1 :=
          mul_le_mul h (pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg P) hP) (by positivity)
            ((norm_nonneg _).trans h)
      _ = A * 2 ^ (j * i) := mul_one _
  have hv : ∀ i ≤ K, ‖iteratedFDeriv ℝ i (Ω.profile ∘ ℓ) y‖ ≤ |B₀| * 2 ^ (j * i) := fun i hi => by
    refine (norm_iteratedFDeriv_comp_clm_le ℓ Ω.contDiff_profile y
      (by exact_mod_cast le_top)).trans ?_
    rw [pow_mul]
    exact mul_le_mul ((hB₀ i hi (ℓ y)).trans (le_abs_self _))
      (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg ℓ) hℓ i) (by positivity)
      (abs_nonneg _)
  rw [iteratedFDerivWithin_univ, hext]
  refine (norm_iteratedFDeriv_mul_le h1 h2 y (by exact_mod_cast hl)).trans ?_
  calc ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (a ∘ P) y‖ *
        ‖iteratedFDeriv ℝ (l - i) (Ω.profile ∘ ℓ) y‖
      ≤ ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (A * |B₀| * 2 ^ (j * l)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc ‖iteratedFDeriv ℝ i (a ∘ P) y‖ * ‖iteratedFDeriv ℝ (l - i) (Ω.profile ∘ ℓ) y‖
            ≤ (A * 2 ^ (j * i)) * (|B₀| * 2 ^ (j * (l - i))) :=
              mul_le_mul (hu i (hil.trans hl)) (hv (l - i) ((Nat.sub_le l i).trans hl))
                (norm_nonneg _) (by positivity)
          _ = A * |B₀| * 2 ^ (j * l) := by
              rw [show j * l = j * i + j * (l - i) by rw [← Nat.mul_add, Nat.add_sub_cancel' hil],
                pow_add]
              ring
    _ = 2 ^ l * (A * |B₀| * 2 ^ (j * l)) := by
        rw [← Finset.sum_mul]
        have hsum : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) = 2 ^ l := by
          exact_mod_cast Nat.sum_range_choose l
        rw [hsum]
    _ ≤ 2 ^ K * (A * |B₀| * 2 ^ (j * l)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hl) (by positivity)
    _ = 2 ^ K * |B₀| * A * 2 ^ (j * l) := by ring

/-! ### The extension of every order -/

section Extension

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The terms `g_j = η_j ⋆ (k_j ⋆ g)` of the reproducing formula on `H`, with moment order `Lh`. -/
noncomputable def flatLevelH (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) (x' : (flat e he).hyperplane) : ℂ :=
  conv ((flat e he).graphBump.dual Lh j) ((flat e he).graphBump.localMean hp Lh j g) volume x'

/-- The terms on `H` are continuous. -/
theorem continuous_flatLevelH (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) :
    Continuous (flatLevelH e he hp Lh j g) :=
  ((flat e he).graphBump.hasCompactSupport_dual Lh j).continuous_convolution_left
    (ContinuousLinearMap.mul ℂ ℂ) ((flat e he).graphBump.continuous_dual Lh j)
    ((Lp.memLp _).locallyIntegrable Fact.out)

/-- The levels of the extension: `F_j(x) = g_j(Px) χ(2^j ⟪x, e⟫)`. -/
noncomputable def flatLevel (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) : V → ℂ :=
  (flat e he).extendAtom j (flatLevelH e he hp Lh j g)

/-- **The levels are sums of extended atoms**: `F_j = ∑_m λ_{j,m} A_{j,m}` at every point. -/
theorem flatLevel_eq_tsum (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) (x : V) :
    flatLevel e he hp Lh j g x = ∑' m, cellCoef p j ((flat e he).graphBump.localMean hp Lh j g) m *
      (flat e he).extendAtom j (cellAtom p ((flat e he).graphBump.dual Lh j) j
        ((flat e he).graphBump.localMean hp Lh j g) m) x := by
  set Ω := flat e he
  have hρ : 0 ≤ 2 * (Lh : ℝ) * Ω.graphBump.radius / 2 ^ j :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
      Ω.graphBump.radius_nonneg) (by positivity)
  rw [flatLevel, extendAtom, flatLevelH, conv_eq_tsum_cellAtom Fact.out
    (Ω.graphBump.continuous_dual Lh j) hρ (fun y hy => Ω.graphBump.dual_eq_zero_of_lt Lh j hy)
    (Lp.memLp _) j, ← tsum_mul_right]
  refine tsum_congr fun m => ?_
  rw [extendAtom, mul_assoc]

/-- The levels of the extension are continuous. -/
theorem continuous_flatLevel (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) :
    Continuous (flatLevel e he hp Lh j g) :=
  (flat e he).continuous_extendAtom j (continuous_flatLevelH e he hp Lh j g)

/-- **The extended atoms of every order**: for `r ≥ 1` there are a radius factor `d`, a constant
`C < ∞` and an overlap bound `N` such that for every level `j` and `h ∈ L_p(H)` the extensions of
the cell atoms of `η_j ⋆ h` (moment order `Lh`) are regular atoms on `V` of order and exponent `r`
centred at the cell centres of `H`, with overlap at most `N`. -/
theorem exists_flat_extension_atoms (Lh : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ∃ (d : ℝ) (C : ℝ≥0∞) (N : ℕ), C ≠ ∞ ∧ ∀ (j : ℕ) {h : (flat e he).hyperplane → ℂ},
      MemLp h p volume →
      (∀ m, IsRegularAtom p r r d C j ((flat e he).extendCenter j (cellCenter j m))
        ((flat e he).extendAtom j (cellAtom p ((flat e he).graphBump.dual Lh j) j h m))) ∧
      ∀ x (S : Finset (Fin (finrank ℝ (flat e he).hyperplane) → ℤ)),
        (∀ m ∈ S, cellCoef p j h m ≠ 0 ∧
          ‖x - (flat e he).extendCenter j (cellCenter j m)‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N := by
  set Ω := flat e he
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨A, hA, hsm⟩ := Ω.graphBump.exists_isSmoothAtom_cellAtom hp1 Lh r
  obtain ⟨B, hB, hext⟩ := exists_isSmoothAtom_extendAtom_flat e he r
  set dH := 2 * (Lh : ℝ) * Ω.graphBump.radius + finrank ℝ Ω.hyperplane
  have hdH : 0 ≤ dH := add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
    Ω.graphBump.radius_nonneg) (Nat.cast_nonneg _)
  set d := Ω.extendRadius dH
  have hd : 0 ≤ d := by
    have := Ω.cutoffLevel_pos
    have := mul_nonneg hdH (add_nonneg zero_le_one (mul_nonneg Ω.M_nonneg Ω.graphBumpNorm_nonneg))
    simp only [d, extendRadius]
    linarith
  have hBA : 0 ≤ 2 ^ r * B * A := by positivity
  have hint : (interior (Set.univ : Set V)).Nonempty := by
    rw [interior_univ]
    exact univ_nonempty
  refine ⟨d, ENNReal.ofReal (2 ^ r * (r : ℝ) ^ (r + 1) * (2 ^ r * B * A)) *
      (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1))) ^
        (1 / p.toReal), ⌈(2 * (d + r) + 2) ^ finrank ℝ Ω.hyperplane⌉₊,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne))),
    fun j h hh => ⟨fun m => ?_, fun x S hS => ?_⟩⟩
  · exact isRegularAtomOn_of_isSmoothAtom convex_univ MeasurableSet.univ hint hr le_rfl hd hBA
      (hext hA (hsm j hh m))
  · refine card_le_of_norm_sub_cellCenter_le j (by positivity) (Ω.proj x) S fun m hm => ?_
    calc ‖Ω.proj x - cellCenter j m‖ = ‖Ω.proj (x - Ω.extendCenter j (cellCenter j m))‖ := by
          rw [map_sub, Ω.proj_extendCenter]
      _ ≤ ‖x - Ω.extendCenter j (cellCenter j m)‖ := Ω.norm_proj_le _
      _ ≤ (d + r) / 2 ^ j := (hS m hm).2

/-- **The levels of the extension in `L_p`**: `‖F_j‖_p ≤ K 2^(-j/p) ‖k_j ⋆ g‖_p`. -/
theorem eLpNorm_flatLevel_le (hp : p ≠ ∞) (Lh : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ j (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)),
      eLpNorm (flatLevel e he hp Lh j g) p volume ≤
        K * dyadicWeight (-(1 / p.toReal)) j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ := by
  set Ω := flat e he
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨d, C, N, hC, hatoms⟩ := exists_flat_extension_atoms e he (p := p) Lh le_rfl
  have hexp : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  refine ⟨(N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (ENNReal.natCast_ne_top N)) hC, fun j g => ?_⟩
  obtain ⟨hat, hN⟩ := hatoms j (Lp.memLp (Ω.graphBump.localMean hp Lh j g))
  have hlev := eLpNorm_levelSum_le hp1 hp (fun m => Ω.extendCenter j (cellCenter j m))
    (fun m => Ω.extendAtom j (cellAtom p (Ω.graphBump.dual Lh j) j
      (Ω.graphBump.localMean hp Lh j g) m))
    (cellCoef p j (Ω.graphBump.localMean hp Lh j g)) hN hat
    (continuous_flatLevel e he hp Lh j g).aestronglyMeasurable
    (Eventually.of_forall (flatLevel_eq_tsum e he hp Lh j g))
  refine hlev.trans_eq ?_
  rw [levelNorm_cellCoef hp0 hp (Lp.memLp _) j, ← Lp.enorm_def]
  have hw : dyadicWeight (-(finrank ℝ V / p.toReal)) j *
      dyadicWeight (finrank ℝ Ω.hyperplane / p.toReal) j = dyadicWeight (-(1 / p.toReal)) j := by
    rw [← ENNReal.dyadicWeight_add, Ω.finrank_hyperplane_eq]
    congr 1
    ring
  calc (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) *
        (dyadicWeight (finrank ℝ Ω.hyperplane / p.toReal) j *
          ‖Ω.graphBump.localMean hp Lh j g‖ₑ)
      = (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C * (dyadicWeight (-(finrank ℝ V / p.toReal)) j *
          dyadicWeight (finrank ℝ Ω.hyperplane / p.toReal) j) *
            ‖Ω.graphBump.localMean hp Lh j g‖ₑ := by ring
    _ = _ := by rw [hw]

/-- The levels of the extension are in `L_p`. -/
theorem memLp_flatLevel (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) :
    MemLp (flatLevel e he hp Lh j g) p volume := by
  obtain ⟨K, hK, hle⟩ := eLpNorm_flatLevel_le e he hp Lh
  exact memLp_iff.2 ((hle j g).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK.lt_top
    (ENNReal.dyadicWeight_lt_top _ _)) enorm_lt_top))

/-- The level `F_j` of the extension in `L_p(V)`. -/
noncomputable def flatTerm (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) : Lp ℂ p (volume : Measure V) :=
  (memLp_flatLevel e he hp Lh j g).toLp _

/-- The level in `L_p` agrees with `F_j` almost everywhere. -/
theorem flatTerm_ae (hp : p ≠ ∞) (Lh j : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) :
    flatTerm e he hp Lh j g =ᵐ[volume] flatLevel e he hp Lh j g :=
  MemLp.coeFn_toLp _

/-- The **extension of every order** `E g = ∑_j F_j` from the hyperplane, with moment order `Lh`
on `H`. -/
noncomputable def flatExtension (hp : p ≠ ∞) (Lh : ℕ)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) : Lp ℂ p (volume : Measure V) :=
  ∑' j, flatTerm e he hp Lh j g

/-- **The extension converges absolutely** for `s > 0` and a finite local means quasi-norm
`X = ‖(2^(js) ‖k_j ⋆ g‖_p)_j‖_{ℓ_q}`: `‖F_j‖_p ≤ K X 2^(-js)`. -/
theorem summable_flatTerm (hp : p ≠ ∞) (Lh : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {g : Lp ℂ p (volume : Measure (flat e he).hyperplane)}
    (hX : (flat e he).graphBump.localMeansNorm hp Lh s q g < ∞) :
    Summable fun j => flatTerm e he hp Lh j g := by
  obtain ⟨K, hK, hle⟩ := eLpNorm_flatLevel_le e he hp Lh
  set X := (flat e he).graphBump.localMeansNorm hp Lh s q g
  have hterm : ∀ j, ‖flatTerm e he hp Lh j g‖ₑ ≤ K * X * dyadicWeight (-s) j := fun j => by
    have hXj : dyadicWeight s j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ ≤ X :=
      ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
        (fun j => dyadicWeight s j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ) j
    rw [Lp.enorm_def, eLpNorm_congr_ae (flatTerm_ae e he hp Lh j g)]
    refine (hle j g).trans ?_
    have hw : dyadicWeight (-(1 / p.toReal)) j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ ≤
        dyadicWeight (-s) j *
          (dyadicWeight s j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ) := by
      rw [← mul_assoc, ← ENNReal.dyadicWeight_add, neg_add_cancel, ENNReal.dyadicWeight_zero_left,
        one_mul]
      calc dyadicWeight (-(1 / p.toReal)) j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ
          ≤ 1 * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ := by
            refine mul_le_mul' ?_ le_rfl
            have := ENNReal.dyadicWeight_anti (s := -(1 / p.toReal))
              (by have := ENNReal.toReal_nonneg (a := p); simp only [neg_nonpos]; positivity)
              (Nat.zero_le j)
            simpa using this
        _ = ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ := one_mul _
    calc K * dyadicWeight (-(1 / p.toReal)) j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ
        = K * (dyadicWeight (-(1 / p.toReal)) j *
            ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ) := by ring
      _ ≤ K * (dyadicWeight (-s) j * X) :=
          mul_le_mul' le_rfl (hw.trans (mul_le_mul' le_rfl hXj))
      _ = K * X * dyadicWeight (-s) j := by ring
  refine Summable.of_norm ?_
  have hfin : ∑' j, ‖flatTerm e he hp Lh j g‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hK hX.ne)
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)
  simpa only [toReal_enorm] using ENNReal.summable_toReal hfin

/-- The coefficient quasi-norm of the cell coefficients on `H` with smoothness `s + 1/p` in
dimension `n` is the local means quasi-norm of `g` with smoothness `s`, since
`(s + 1/p) - n/p = s - (n-1)/p`. -/
theorem coeffNorm_flat_eq (hp : p ≠ ∞) (Lh : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) :
    coeffNorm p (finrank ℝ V) (s + 1 / p.toReal) q
        (fun j => cellCoef p j ((flat e he).graphBump.localMean hp Lh j g)) =
      (flat e he).graphBump.localMeansNorm hp Lh s q g := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  rw [coeffNorm, LocalMeansBump.localMeansNorm]
  congr 1
  funext j
  rw [levelNorm_cellCoef hp0 hp (Lp.memLp _) j, ← Lp.enorm_def, ← mul_assoc,
    ← ENNReal.dyadicWeight_add, (flat e he).finrank_hyperplane_eq]
  congr 2
  ring

/-- **The extension of every order is bounded**: for `s > 0` and `s + 1/p < r` there is `K < ∞`
with `‖E g‖_p + ‖(2^(k(s+1/p)) ω_r(E g, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖(2^(js) ‖k_j ⋆ g‖_p)_j‖_{ℓ_q}`,
by the atomic synthesis on `V` with the extended atoms of order `r`. -/
theorem modNorm_flatExtension_le_localMeansNorm (hp : p ≠ ∞) (Lh : ℕ) {r : ℕ} {s : ℝ}
    (hs : 0 < s) (hsr : s + 1 / p.toReal < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : Lp ℂ p (volume : Measure (flat e he).hyperplane),
      (flat e he).graphBump.localMeansNorm hp Lh s q g < ∞ →
      ‖flatExtension e he hp Lh g‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p r (flatExtension e he hp Lh g) k) ≤
        K * (flat e he).graphBump.localMeansNorm hp Lh s q g := by
  set Ω := flat e he
  have hp1 : 1 ≤ p := Fact.out
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  have hr : 1 ≤ r := by
    by_contra h
    have h0 : r = 0 := by omega
    rw [h0, Nat.cast_zero] at hsr
    linarith
  obtain ⟨d, C, N, hC, hatoms⟩ := exists_flat_extension_atoms e he (p := p) Lh hr
  refine ⟨atomSynthConst p N C r (s + 1 / p.toReal) r,
    atomSynthConst_ne_top hp1 N hC r hσ0 hsr, fun g hX => ?_⟩
  have hsyn := modNorm_le_coeffNorm hp (fun j m => Ω.extendCenter j (cellCenter j m))
    (fun j m => Ω.extendAtom j (cellAtom p (Ω.graphBump.dual Lh j) j
      (Ω.graphBump.localMean hp Lh j g) m))
    (fun j => cellCoef p j (Ω.graphBump.localMean hp Lh j g))
    (fun j x S hS => (hatoms j (Lp.memLp _)).2 x S hS)
    (fun j m => (hatoms j (Lp.memLp _)).1 m)
    (fun j => (flatTerm_ae e he hp Lh j g).mono fun x hx =>
      hx.trans (flatLevel_eq_tsum e he hp Lh j g x))
    (((summable_flatTerm e he hp Lh hs hq hX).hasSum.tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)) hσ0 hsr hq
  rwa [coeffNorm_flat_eq] at hsyn

/-- **The extension of every order, bounded by the moduli of `g`**: for `s > 0` and
`s + 1/p < r` there is `K < ∞` with
`‖E g‖_p + ‖(2^(k(s+1/p)) ω_r(E g, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖g‖_{L_p(H)} + ‖(2^(ks) ω_{Lh}(g, 2^(-k))_p)_k‖_{ℓ_q})`. -/
theorem modNorm_flatExtension_le (hp : p ≠ ∞) (Lh : ℕ) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s + 1 / p.toReal < r) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : Lp ℂ p (volume : Measure (flat e he).hyperplane),
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p Lh g k) < ∞ →
      ‖flatExtension e he hp Lh g‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p r (flatExtension e he hp Lh g) k) ≤
        K * (‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p Lh g k)) := by
  set Ω := flat e he
  obtain ⟨K, hK, hle⟩ := modNorm_flatExtension_le_localMeansNorm e he hp Lh hs hsr hq
  refine ⟨K * Ω.graphBump.upperConst Lh s,
    ENNReal.mul_ne_top hK (Ω.graphBump.upperConst_ne_top Lh s), fun g hg => ?_⟩
  have hLM := Ω.graphBump.localMeansNorm_le hp Lh s hq g
  have hX : Ω.graphBump.localMeansNorm hp Lh s q g < ∞ :=
    hLM.trans_lt (ENNReal.mul_lt_top (Ω.graphBump.upperConst_ne_top Lh s).lt_top hg)
  rw [mul_assoc]
  exact (hle g hX).trans (mul_le_mul' le_rfl hLM)

/-- **One level of the extension**: there are `C < ∞` and `N` such that for `0 < σ < r`,
`1 ≤ q ≤ ∞`, `g ∈ L_p(H)` and every level `j`,
`‖F_j‖_p + ‖(2^(kσ) ω_r(F_j, 2^(-k))_p)_k‖_{ℓ_q} ≤ K_σ 2^(j(σ - 1/p)) ‖k_j ⋆ g‖_p` with
`K_σ = Rd.atomSynthConst p N C r σ r`. -/
theorem exists_modNorm_flatTerm_le (hp : p ≠ ∞) (Lh : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ∃ (C : ℝ≥0∞) (N : ℕ), C ≠ ∞ ∧ ∀ {σ : ℝ}, 0 < σ → σ < r → ∀ {q : ℝ≥0∞}, 1 ≤ q →
      ∀ (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) (j : ℕ),
        ‖flatTerm e he hp Lh j g‖ₑ + lqNorm q (fun k =>
            dyadicWeight σ k * lpModulus p r (flatTerm e he hp Lh j g) k) ≤
          atomSynthConst p N C r σ r *
            (dyadicWeight (σ - 1 / p.toReal) j * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨d, C, N, hC, hatoms⟩ := exists_flat_extension_atoms e he (p := p) Lh hr
  refine ⟨C, N, hC, fun {σ'} hσ' hσ'r {q'} hq' g j => ?_⟩
  obtain ⟨hat, hN⟩ := hatoms j (Lp.memLp ((flat e he).graphBump.localMean hp Lh j g))
  refine (modNorm_level_le hp j (fun m => (flat e he).extendCenter j (cellCenter j m))
    (fun m => (flat e he).extendAtom j (cellAtom p ((flat e he).graphBump.dual Lh j) j
      ((flat e he).graphBump.localMean hp Lh j g) m))
    (cellCoef p j ((flat e he).graphBump.localMean hp Lh j g)) hN hat
    ((flatTerm_ae e he hp Lh j g).mono fun x hx => hx.trans (flatLevel_eq_tsum e he hp Lh j g x))
    hσ' hσ'r hq').trans_eq ?_
  rw [levelNorm_cellCoef hp0 hp (Lp.memLp _) j, ← Lp.enorm_def]
  congr 1
  rw [← mul_assoc, ← ENNReal.dyadicWeight_add, (flat e he).finrank_hyperplane_eq]
  congr 2
  ring

/-- **The traces of the partial sums of the extension** are the partial sums of the reproducing
formula on `H`: `Tr (∑_{j ≤ J} F_j) = ∑_{j ≤ J} η_j ⋆ (k_j ⋆ g)`, since the partial sums are
continuous with the values `∑_{j ≤ J} (η_j ⋆ (k_j ⋆ g))(x')` on `H`. -/
theorem trace_sum_flatTerm (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) (Lh : ℕ) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) (J : ℕ)
    (hFJ : ‖∑ j ∈ Finset.range (J + 1), flatTerm e he hp Lh j g‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k *
        lpModulus p L (∑ j ∈ Finset.range (J + 1), flatTerm e he hp Lh j g) k) < ∞) :
    (flat e he).trace hp L (∑ j ∈ Finset.range (J + 1), flatTerm e he hp Lh j g) =
      ∑ j ∈ Finset.range (J + 1),
        convLp hp ((flat e he).graphBump.integrable_dual Lh j)
          ((flat e he).graphBump.localMean hp Lh j g) := by
  have hcont : Continuous fun x => ∑ j ∈ Finset.range (J + 1), flatLevel e he hp Lh j g x :=
    continuous_finsetSum _ fun j _ => continuous_flatLevel e he hp Lh j g
  have hae : ((∑ j ∈ Finset.range (J + 1), flatTerm e he hp Lh j g :
      Lp ℂ p (volume : Measure V)) : V → ℂ) =ᵐ[volume]
        fun x => ∑ j ∈ Finset.range (J + 1), flatLevel e he hp Lh j g x := by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
      (fun j => flatTerm e he hp Lh j g), ae_all_iff.2 fun j => flatTerm_ae e he hp Lh j g]
      with x hx1 hx2
    rw [hx1]
    exact Finset.sum_congr rfl fun j _ => hx2 j
  have htr := (flat e he).trace_ae_eq_comp_graphMap hp hL hs hq
    ((flat e he).intrinsicNorm_lt_top_of_modNorm' hp L hq hFJ).1 hcont hae
  refine Lp.ext ?_
  filter_upwards [htr, Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
    (fun j => convLp hp ((flat e he).graphBump.integrable_dual Lh j)
      ((flat e he).graphBump.localMean hp Lh j g)),
    ae_all_iff.2 fun j => convLp_apply_ae hp ((flat e he).graphBump.integrable_dual Lh j)
      ((flat e he).graphBump.localMean hp Lh j g)] with x' h1 h2 h3
  rw [h1, h2, Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3 j, flatLevel, (flat e he).extendAtom_graphMap]
  rfl

/-- **The trace of the extension of every order**: for `L ≥ 2`, `Lh ≥ 1`, `s > 0` with
`s + 1/p < L` and `g ∈ L_p(H)` with a finite local means quasi-norm
`‖(2^(js) ‖k_j ⋆ g‖_p)_j‖_{ℓ_q}`, `Tr (E g) = g`. The partial sums `∑_{j ≤ J} F_j` are continuous
with traces `∑_{j ≤ J} η_j ⋆ (k_j ⋆ g) → g`, and they converge to `E g` in `B^{1/p}_{p,1}`, where
the trace is continuous (`Rd.LipschitzGraph.tendsto_trace_of_modNorm_sub_le`). -/
theorem trace_flatExtension (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {Lh : ℕ} (hLh : 1 ≤ Lh) {s : ℝ}
    (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {g : Lp ℂ p (volume : Measure (flat e he).hyperplane)}
    (hX : (flat e he).graphBump.localMeansNorm hp Lh s q g < ∞) :
    (flat e he).trace hp L (flatExtension e he hp Lh g) = g := by
  have hp1 : 1 ≤ p := Fact.out
  have hpr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hpinv0 : 0 < 1 / p.toReal := by positivity
  have hpinv1 : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hpr
  have hpinvL : 1 / p.toReal < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hσ0 : 0 < s + 1 / p.toReal := by positivity
  set T : ℕ → Lp ℂ p (volume : Measure V) := fun j => flatTerm e he hp Lh j g
  have hsum : Summable T := summable_flatTerm e he hp Lh hs hq hX
  obtain ⟨C, N, hC, hlevel⟩ := exists_modNorm_flatTerm_le e he hp Lh (r := L) (by omega)
  have hfinT : ∀ j, ‖T j‖ₑ + lqNorm q
      (fun k => dyadicWeight (s + 1 / p.toReal) k * lpModulus p L (T j) k) < ∞ := fun j =>
    (hlevel hσ0 hsL hq g j).trans_lt (ENNReal.mul_lt_top
      (atomSynthConst_ne_top hp1 N hC L hσ0 hsL).lt_top (ENNReal.mul_lt_top
        (ENNReal.dyadicWeight_lt_top _ _) enorm_lt_top))
  -- the finite norms of the extension and of its partial sums
  obtain ⟨KE, hKE, hEle⟩ := modNorm_flatExtension_le_localMeansNorm e he hp Lh hs hsL hq
  have hF : ‖flatExtension e he hp Lh g‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L (flatExtension e he hp Lh g) k) < ∞ :=
    (hEle g hX).trans_lt (ENNReal.mul_lt_top hKE.lt_top hX)
  have hFJ : ∀ J, ‖∑ j ∈ Finset.range (J + 1), T j‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L (∑ j ∈ Finset.range (J + 1), T j) k) <
        ∞ := fun J => modNorm_finsetSum_lt_top _ T hq fun j _ => hfinT j
  -- the tail in the norm of `B^{1/p}_{p,1}` with order `L`
  set K1 := atomSynthConst p N C L (1 / p.toReal) L
  have hK1 : K1 ≠ ∞ := atomSynthConst_ne_top hp1 N hC L hpinv0 hpinvL
  set Q : Lp ℂ p (volume : Measure V) → ℝ≥0∞ := fun G =>
    ‖G‖ₑ + lqNorm 1 (fun k => dyadicWeight (1 / p.toReal) k * lpModulus p L G k)
  have hQT : ∀ j, Q (T j) ≤ K1 * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ := fun j =>
    (hlevel hpinv0 hpinvL le_rfl g j).trans_eq (by
      rw [sub_self, ENNReal.dyadicWeight_zero_left, one_mul])
  have hQtail : ∀ J, Q (∑' i, T (i + (J + 1))) ≤
      ∑' i, K1 * ‖(flat e he).graphBump.localMean hp Lh (i + (J + 1)) g‖ₑ := fun J =>
    (modNorm_one_tsum_le L (1 / p.toReal) ((summable_nat_add_iff (J + 1)).2 hsum)).trans
      (ENNReal.tsum_le_tsum fun i => hQT (i + (J + 1)))
  -- the tails tend to `0`
  have hhsum : ∑' j, K1 * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hK1 (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs) hX.ne)
      (ENNReal.tsum_le_lqNorm_dyadicWeight hq s _))
  have htail : Tendsto (fun J => ∑' i, K1 *
      ‖(flat e he).graphBump.localMean hp Lh (i + (J + 1)) g‖ₑ) atTop (𝓝 0) :=
    (ENNReal.tendsto_sum_nat_add _ hhsum).comp (tendsto_add_atTop_nat 1)
  -- the traces of the partial sums converge to the trace of the extension
  have hsplit : ∀ J, flatExtension e he hp Lh g - ∑ j ∈ Finset.range (J + 1), T j =
      ∑' i, T (i + (J + 1)) := fun J => by
    rw [flatExtension, ← hsum.sum_add_tsum_nat_add (J + 1)]
    abel
  have hconv := (flat e he).tendsto_trace_of_modNorm_sub_le hp L hs hq
    ((flat e he).intrinsicNorm_lt_top_of_modNorm' hp L hq hF).2
    (fun J => ((flat e he).intrinsicNorm_lt_top_of_modNorm' hp L hq (hFJ J)).2) htail
    (fun J => ne_top_of_le_ne_top hhsum (ENNReal.tsum_comp_le_tsum_of_injective
      (add_left_injective (J + 1)) fun j => K1 * ‖(flat e he).graphBump.localMean hp Lh j g‖ₑ))
    fun J => by rw [hsplit J]; exact hQtail J
  -- the traces of the partial sums are the partial sums of the reproducing formula on `H`
  have hpart : ∀ J, (flat e he).trace hp L (∑ j ∈ Finset.range (J + 1), T j) =
      ∑ j ∈ Finset.range (J + 1), convLp hp ((flat e he).graphBump.integrable_dual Lh j)
        ((flat e he).graphBump.localMean hp Lh j g) := fun J =>
    trace_sum_flatTerm e he hp (by omega) Lh hs hq g J (hFJ J)
  have hlim := (flat e he).graphBump.tendsto_sum_dual_localMean hp hLh g
  simp_rw [← hpart] at hlim
  exact tendsto_nhds_unique hconv hlim

/-- **The trace space of the half-space, for every smoothness**: for `1 ≤ p < ∞`, `s > 0`,
`1 ≤ q ≤ ∞`, `L ≥ 2` with `s + 1/p < L`, and `r > s`, `g ∈ L_p(H)` is the trace of some `f` with
`‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff
`‖g‖_p + ‖(2^(ks) ω_r(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. The trace is bounded
(`Rd.LipschitzGraph.modNorm_trace_le_flat`), and the extension of moment order `r` is such an `f`
(`Rd.LipschitzGraph.trace_flatExtension`). -/
theorem exists_trace_eq_iff_flat (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : Lp ℂ p (volume : Measure (flat e he).hyperplane)) :
    (∃ f : Lp ℂ p (volume : Measure V), ‖(flat e he).cutoff f‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * lpModulusOn p (flat e he).domain L f k) < ∞ ∧
        (flat e he).trace hp L f = g) ↔
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r g k) < ∞ := by
  have hr : 1 ≤ r := by
    by_contra h
    have h0 : r = 0 := by omega
    rw [h0, Nat.cast_zero] at hsr
    linarith
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨K, hK, hle⟩ := modNorm_trace_le_flat e he hp L hr hs hsr hq
    exact (hle f hf).trans_lt (ENNReal.mul_lt_top hK.lt_top hf)
  · intro hg
    have hX : (flat e he).graphBump.localMeansNorm hp r s q g < ∞ :=
      ((flat e he).graphBump.localMeansNorm_le hp r s hq g).trans_lt
        (ENNReal.mul_lt_top ((flat e he).graphBump.upperConst_ne_top r s).lt_top hg)
    obtain ⟨K, hK, hle⟩ := modNorm_flatExtension_le_localMeansNorm e he hp r hs hsL hq
    exact ⟨flatExtension e he hp r g, ((flat e he).intrinsicNorm_lt_top_of_modNorm' hp L hq
      ((hle g hX).trans_lt (ENNReal.mul_lt_top hK.lt_top hX))).1,
      trace_flatExtension e he hp hL hr hs hsL hq hX⟩

end Extension

end LipschitzGraph

end Rd
