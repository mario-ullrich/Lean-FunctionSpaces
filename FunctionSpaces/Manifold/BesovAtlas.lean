/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Manifold.SmoothMeasure
public import FunctionSpaces.Rd.HalfSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Besov atlases

A **Besov atlas** of a manifold `M` (`Manifold.BesovAtlas`) consists of finitely many charts
`e_i` of the atlas, a smooth partition of unity `(ψ_i)` with `tsupport ψ_i ⊆ e_i.source`, and
smooth cut-offs `θ_i` with `θ_i = 1` on `tsupport ψ_i` and `tsupport θ_i ⊆ e_i.source`. Every
compact manifold has one (`Manifold.BesovAtlas.nonempty`): finitely many chart sources cover `M`,
Mathlib's smooth partitions of unity are subordinate to them
(`SmoothPartitionOfUnity.exists_isSubordinate`), and smooth Urysohn functions give the cut-offs.

A smooth function on `M` read in an extended chart is smooth within the target of the chart
(`Manifold.contDiffOn_comp_extend_symm`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A **Besov atlas**: finitely many charts of the atlas, a smooth partition of unity `(ψ_i)`
subordinate to their sources, and smooth cut-offs `θ_i` with `θ_i = 1` on `tsupport ψ_i` and
`tsupport θ_i` inside the source of the `i`-th chart. -/
structure BesovAtlas where
  /-- The number of charts. -/
  n : ℕ
  /-- The charts. -/
  chart : Fin n → OpenPartialHomeomorph M H
  chart_mem : ∀ i, chart i ∈ atlas H M
  /-- The partition of unity. -/
  psi : Fin n → M → ℝ
  contMDiff_psi : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (psi i)
  nonneg_psi : ∀ i x, 0 ≤ psi i x
  tsupport_psi_subset : ∀ i, tsupport (psi i) ⊆ (chart i).source
  sum_psi : ∀ x, ∑ i, psi i x = 1
  /-- The cut-offs. -/
  theta : Fin n → M → ℝ
  contMDiff_theta : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (theta i)
  theta_eq_one : ∀ i, ∀ x ∈ tsupport (psi i), theta i x = 1
  tsupport_theta_subset : ∀ i, tsupport (theta i) ⊆ (chart i).source

/-- **Every compact manifold has a Besov atlas**: finitely many chart sources cover `M`, a smooth
partition of unity is subordinate to them, and a smooth Urysohn function between `tsupport ψ_i`
and the complement of an open set `V_i` with `closure V_i ⊆ e_i.source` is the cut-off. -/
theorem BesovAtlas.nonempty [CompactSpace M] [T2Space M] [IsManifold I ∞ M] :
    Nonempty (BesovAtlas I M) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source) (fun x _ => mem_iUnion.2 ⟨x, mem_chart_source H x⟩)
  set pt : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  have hcover : (univ : Set M) ⊆ ⋃ i, (chartAt H (pt i)).source := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
    refine mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    simpa [pt] using hxy
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i => (chartAt H (pt i)).source) (fun i => (chartAt H (pt i)).open_source) hcover
  have hθ : ∀ i, ∃ θ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ θ ∧ (∀ x ∈ tsupport (f i), θ x = 1) ∧
      tsupport θ ⊆ (chartAt H (pt i)).source := fun i => by
    have hK : IsCompact (tsupport (f i)) := (isClosed_tsupport _).isCompact
    obtain ⟨V, hVo, hKV, hVU, -⟩ :=
      exists_open_between_and_isCompact_closure hK (chartAt H (pt i)).open_source (hf i)
    obtain ⟨g, hg0, hg1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := ⊤) I
      hVo.isClosed_compl (isClosed_tsupport _) (disjoint_compl_left_iff_subset.2 hKV)
    refine ⟨g, g.contMDiff, fun x hx => hg1 hx, (closure_mono fun x hx => ?_).trans hVU⟩
    by_contra hxV
    exact hx (hg0 hxV)
  choose θ hθs hθ1 hθsub using hθ
  exact ⟨{ n := t.card
           chart := fun i => chartAt H (pt i)
           chart_mem := fun i => chart_mem_atlas H _
           psi := fun i => f i
           contMDiff_psi := fun i => (f i).contMDiff
           nonneg_psi := fun i x => f.nonneg i x
           tsupport_psi_subset := hf
           sum_psi := fun x => by
             have h := f.sum_eq_one (mem_univ x)
             rwa [finsum_eq_sum_of_fintype] at h
           theta := θ
           contMDiff_theta := hθs
           theta_eq_one := hθ1
           tsupport_theta_subset := hθsub }⟩

variable {I M}

omit [FiniteDimensional ℝ E] in
/-- **Smooth functions in a chart**: for a chart `e` of the atlas and a smooth `g : M → ℝ`,
`g ∘ κ⁻¹` is smooth within the target of the extended chart `κ = e.extend I`. -/
theorem contDiffOn_comp_extend_symm [IsManifold I ∞ M] {e : OpenPartialHomeomorph M H}
    (he : e ∈ atlas H M) {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) :
    ContDiffOn ℝ ∞ (g ∘ (e.extend I).symm) (e.extend I).target := by
  have h := (contMDiffOn_iff_of_mem_maximalAtlas' (IsManifold.subset_maximalAtlas he)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℝ)) (0 : ℝ)) subset_rfl
    (fun x _ => by simp [chartAt_self_eq])).1 hg.contMDiffOn
  rw [← e.extend_target_eq_image_source] at h
  simpa [chartAt_self_eq, Function.comp_def] using h

/-! ### Changes of charts -/

section CoordChange

omit [FiniteDimensional ℝ E] [ChartedSpace H M]

variable (e e' : OpenPartialHomeomorph M H)

/-- The source of the change of charts is the relatively open set `range I ∩ U`. -/
theorem range_inter_coordChange_source :
    range I ∩ I.symm ⁻¹' (e.symm ≫ₕ e').source = (I.extendCoordChange e e').source := by
  rw [I.extendCoordChange_source, I.image_eq, inter_comm]

/-- The target of the change of charts is the relatively open set `range I ∩ U'`. -/
theorem range_inter_coordChange_target :
    range I ∩ I.symm ⁻¹' (e.symm ≫ₕ e').target = (I.extendCoordChange e e').target := by
  rw [I.extendCoordChange_target, I.image_eq, inter_comm]

/-- `y` lies in the source of the change of charts iff it lies in the target of `e.extend I`
and its preimage lies in the source of `e'`. -/
theorem mem_coordChange_source {y : E} :
    y ∈ (I.extendCoordChange e e').source ↔
      y ∈ (e.extend I).target ∧ (e.extend I).symm y ∈ e'.source := by
  rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
    e'.extend_source]
  rfl

/-- The target of the change of charts is the image of `e.source ∩ e'.source` under
`e'.extend I`. -/
theorem coordChange_target_eq_image :
    (I.extendCoordChange e e').target = e'.extend I '' (e'.source ∩ e.source) := by
  rw [← PartialEquiv.symm_source, ModelWithCorners.extendCoordChange_symm,
    OpenPartialHomeomorph.extend_image_source_inter]

/-- The change of charts is `e'.extend I ∘ (e.extend I).symm`. -/
theorem coordChange_apply (y : E) :
    I.extendCoordChange e e' y = e'.extend I ((e.extend I).symm y) := rfl

end CoordChange

namespace BesovAtlas

variable (A : BesovAtlas I M)

/-- The extended chart `κ_i = e_i.extend I`. -/
noncomputable abbrev ext (i : Fin A.n) : PartialEquiv M E := (A.chart i).extend I

omit [FiniteDimensional ℝ E] in
/-- `ψ_i ≤ 1`. -/
theorem psi_le_one (i : Fin A.n) (x : M) : A.psi i x ≤ 1 := by
  rw [← A.sum_psi x]
  exact Finset.single_le_sum (fun j _ => A.nonneg_psi j x) (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] in
/-- `θ_i ψ_i = ψ_i`, since `θ_i = 1` on `tsupport ψ_i`. -/
theorem theta_mul_psi (i : Fin A.n) (x : M) : A.theta i x * A.psi i x = A.psi i x := by
  by_cases hx : x ∈ tsupport (A.psi i)
  · rw [A.theta_eq_one i x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- The **chart piece** `(ψ_i g) ∘ κ_i⁻¹` on the target of `κ_i`, `0` outside. -/
noncomputable def piece (i : Fin A.n) (g : M → ℂ) : E → ℂ :=
  (A.ext i).target.indicator fun y => (A.psi i ((A.ext i).symm y) : ℂ) * g ((A.ext i).symm y)

/-! ### Pieces in `L_p` -/

section Lp

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]

/-- The pieces of strongly measurable functions are almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_piece (i : Fin A.n) {g : M → ℂ} (hg : StronglyMeasurable g) :
    AEStronglyMeasurable (A.piece i g) volume := by
  have hT := measurableSet_extend_target I (A.chart i)
  refine (aestronglyMeasurable_indicator_iff hT).2 ?_
  have hκ : AEMeasurable (A.ext i).symm (volume.restrict (A.ext i).target) :=
    ((A.chart i).continuousOn_extend_symm (I := I)).aemeasurable hT
  have hψ : ContinuousOn (fun y => (A.psi i ((A.ext i).symm y) : ℂ)) (A.ext i).target :=
    Complex.continuous_ofReal.comp_continuousOn ((A.contMDiff_psi i).continuous.comp_continuousOn
      (A.chart i).continuousOn_extend_symm)
  exact (hψ.aestronglyMeasurable hT).mul (hg.aestronglyMeasurable.comp_aemeasurable hκ)

variable [CompactSpace M] (μ : Measure M) [IsSmoothMeasure I μ]

/-- **The pieces are bounded in `L_p`**: `‖piece_i g‖_{L_p(E)} ≤ C ‖g‖_{L_p(μ)}`, since
`0 ≤ ψ_i ≤ 1` and the integrals over `M` and in the chart are comparable on `tsupport ψ_i`. -/
theorem exists_eLpNorm_piece_le (i : Fin A.n) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g : M → ℂ, StronglyMeasurable g →
      eLpNorm (A.piece i g) p volume ≤ C * eLpNorm g p μ := by
  have hK : IsCompact (tsupport (A.psi i)) := (isClosed_tsupport _).isCompact
  obtain ⟨c, C, hc, -, hcmp⟩ :=
    IsSmoothMeasure.exists_lintegral_chart_le (I := I) μ (A.chart_mem i) hK
      (A.tsupport_psi_subset i)
  set e := p.toReal
  have he : 0 < e := ENNReal.toReal_pos hp0 hp
  refine ⟨c⁻¹ ^ (1 / e), ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.2 hc),
    fun g hg => ?_⟩
  set F : M → ℝ≥0∞ := fun x => ‖(A.psi i x : ℂ) * g x‖ₑ ^ e
  have hFm : Measurable F :=
    (((A.contMDiff_psi i).continuous.measurable.complex_ofReal.mul hg.measurable).enorm).pow_const e
  have hFK : ∀ x ∉ tsupport (A.psi i), F x = 0 := fun x hx => by
    simp only [F, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul, enorm_zero,
      ENNReal.zero_rpow_of_pos he]
  have hpiece : (fun y => ‖A.piece i g y‖ₑ ^ e) =
      (A.ext i).target.indicator (fun y => F ((A.ext i).symm y)) := funext fun y => by
    by_cases hy : y ∈ (A.ext i).target
    · simp only [piece, indicator_of_mem hy, F]
    · simp only [piece, indicator_of_notMem hy, enorm_zero, ENNReal.zero_rpow_of_pos he]
  rw [← ENNReal.rpow_le_rpow_iff he, ENNReal.mul_rpow_of_nonneg _ _ he.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel he.ne', ENNReal.rpow_one,
    eLpNorm_rpow_eq (A.aestronglyMeasurable_piece i hg) hp0 hp,
    eLpNorm_rpow_eq hg.aestronglyMeasurable hp0 hp, hpiece,
    lintegral_indicator (measurableSet_extend_target I _)]
  refine (hcmp F hFm hFK).1.trans (mul_le_mul' le_rfl (lintegral_mono fun x => ?_))
  refine ENNReal.rpow_le_rpow ?_ he.le
  rw [enorm_mul]
  calc ‖(A.psi i x : ℂ)‖ₑ * ‖g x‖ₑ ≤ 1 * ‖g x‖ₑ := by
        refine mul_le_mul' ?_ le_rfl
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (A.nonneg_psi i x),
          ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (A.psi_le_one i x)
    _ = ‖g x‖ₑ := one_mul _

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)

include hp in
/-- The pieces of `f ∈ L_p(μ)` are in `L_p(E)`. -/
theorem memLp_piece (i : Fin A.n) (f : Lp ℂ p μ) : MemLp (A.piece i f) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨C, hC, hle⟩ := A.exists_eLpNorm_piece_le μ i hp0 hp
  exact memLp_iff.2 ((hle f (Lp.stronglyMeasurable f)).trans_lt
    (ENNReal.mul_lt_top hC.lt_top (Lp.eLpNorm_lt_top f)))

/-- The **chart piece** of `f ∈ L_p(μ)` as an element of `L_p(E)`. -/
noncomputable def pieceLp (i : Fin A.n) (f : Lp ℂ p μ) : Lp ℂ p (volume : Measure E) :=
  (A.memLp_piece μ hp i f).toLp _

/-- The chart piece in `L_p(E)` agrees with `(ψ_i f) ∘ κ_i⁻¹` almost everywhere. -/
theorem pieceLp_ae (i : Fin A.n) (f : Lp ℂ p μ) : A.pieceLp μ hp i f =ᵐ[volume] A.piece i f :=
  MemLp.coeFn_toLp _

end Lp

/-! ### The change of charts with a cut-off -/

section Transition

variable [IsManifold I ∞ M] [CompactSpace M]

omit [FiniteDimensional ℝ E] in
/-- **The change of charts with a cut-off** from a chart `e` to a chart `e'` of the atlas, with a
smooth cut-off `c` on `M` whose support lies in both sources: `Φ = κ' ∘ κ⁻¹` with
`χ = c ∘ κ'⁻¹`, as a smooth change of variables with a cut-off on `range I`. -/
noncomputable def chartChange {e e' : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (he' : e' ∈ atlas H M) (c : M → ℝ) (hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ c)
    (hcs : tsupport c ⊆ e.source ∩ e'.source) : Rd.CutoffDiffeo (range I) where
  U := I.symm ⁻¹' (e.symm ≫ₕ e').source
  U' := I.symm ⁻¹' (e.symm ≫ₕ e').target
  isOpen_U := I.continuous_symm.isOpen_preimage _ (OpenPartialHomeomorph.open_source _)
  isOpen_U' := I.continuous_symm.isOpen_preimage _ (OpenPartialHomeomorph.open_target _)
  Phi := I.extendCoordChange e e'
  Psi := (I.extendCoordChange e e').symm
  chi := (e'.extend I).target.indicator fun y => (c ((e'.extend I).symm y) : ℂ)
  K0 := e'.extend I '' tsupport c
  contDiffOn_Phi := by
    rw [range_inter_coordChange_source]
    exact I.contDiffOn_extendCoordChange (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he')
  contDiffOn_Psi := by
    rw [range_inter_coordChange_target]
    exact I.contDiffOn_extendCoordChange_symm (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he')
  contDiffOn_chi := by
    rw [range_inter_coordChange_target]
    have hsub : (I.extendCoordChange e e').target ⊆ (e'.extend I).target := by
      rw [coordChange_target_eq_image]
      rintro _ ⟨x, hx, rfl⟩
      exact (e'.extend I).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hx.1)
    have hsm := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_comp_extend_symm he' hc)
    refine (hsm.mono hsub).congr fun y hy => ?_
    rw [indicator_of_mem (hsub hy)]
    rfl
  mapsTo_Phi := by
    rw [range_inter_coordChange_source, range_inter_coordChange_target]
    exact (I.extendCoordChange e e').mapsTo
  mapsTo_Psi := by
    rw [range_inter_coordChange_source, range_inter_coordChange_target]
    exact (I.extendCoordChange e e').mapsTo_symm
  left_inv x hx := by
    rw [range_inter_coordChange_source] at hx
    exact (I.extendCoordChange e e').left_inv hx
  right_inv y hy := by
    rw [range_inter_coordChange_target] at hy
    exact (I.extendCoordChange e e').right_inv hy
  isCompact_K0 := (isClosed_tsupport c).isCompact.image_of_continuousOn
    (e'.continuousOn_extend.mono (by
      rw [OpenPartialHomeomorph.extend_source]
      exact hcs.trans inter_subset_right))
  K0_subset := by
    rw [range_inter_coordChange_target, coordChange_target_eq_image]
    exact image_mono fun x hx => ⟨(hcs hx).2, (hcs hx).1⟩
  chi_eq_zero y _ hyK := by
    by_cases hy : y ∈ (e'.extend I).target
    · rw [indicator_of_mem hy]
      by_contra h
      have hne : c ((e'.extend I).symm y) ≠ 0 := fun h0 => h (by rw [h0, Complex.ofReal_zero])
      exact hyK ⟨(e'.extend I).symm y, subset_tsupport _ hne, (e'.extend I).right_inv hy⟩
    · exact indicator_of_notMem hy _

omit [FiniteDimensional ℝ E] in
/-- The change of charts with a cut-off acts on the source of the change of charts:
`T G = 1_{κ(s ∩ s')} (χ G) ∘ Φ`. -/
theorem chartChange_apply {e e' : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (he' : e' ∈ atlas H M) (c : M → ℝ) (hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ c)
    (hcs : tsupport c ⊆ e.source ∩ e'.source) (G : E → ℂ) (y : E) :
    (chartChange he he' c hc hcs).apply G y = (I.extendCoordChange e e').source.indicator
      (fun y => (chartChange he he' c hc hcs).chi (I.extendCoordChange e e' y) *
        G (I.extendCoordChange e e' y)) y := by
  rw [Rd.CutoffDiffeo.apply, ← range_inter_coordChange_source]
  rfl

variable (A' : BesovAtlas I M)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] in
/-- The cut-off `ψ_i θ'_j` of two atlases has its support in both sources. -/
theorem tsupport_psi_mul_theta_subset (i : Fin A.n) (j : Fin A'.n) :
    tsupport (fun x => A.psi i x * A'.theta j x) ⊆ (A.chart i).source ∩ (A'.chart j).source :=
  subset_inter (tsupport_mul_subset_left.trans (A.tsupport_psi_subset i))
    (tsupport_mul_subset_right.trans (A'.tsupport_theta_subset j))

/-- The **change of charts** from the `i`-th chart of `A` to the `j`-th chart of `A'`, with the
cut-off `(ψ_i θ'_j) ∘ κ'_j⁻¹`, as a smooth change of variables with a cut-off on `range I`. -/
noncomputable def transition (i : Fin A.n) (j : Fin A'.n) : Rd.CutoffDiffeo (range I) :=
  chartChange (A.chart_mem i) (A'.chart_mem j) (fun x => A.psi i x * A'.theta j x)
    ((A.contMDiff_psi i).mul (A'.contMDiff_theta j)) (A.tsupport_psi_mul_theta_subset A' i j)

omit [FiniteDimensional ℝ E] in
/-- The change of charts acts on the source of the change of charts:
`T_{ij} G = 1_{κ_i(s_i ∩ s'_j)} (χ G) ∘ Φ`. -/
theorem transition_apply (i : Fin A.n) (j : Fin A'.n) (G : E → ℂ) (y : E) :
    (A.transition A' i j).apply G y =
      (I.extendCoordChange (A.chart i) (A'.chart j)).source.indicator
        (fun y => (A.transition A' i j).chi (I.extendCoordChange (A.chart i) (A'.chart j) y) *
          G (I.extendCoordChange (A.chart i) (A'.chart j) y)) y := by
  exact chartChange_apply _ _ _ _ _ G y

omit [FiniteDimensional ℝ E] in
/-- **The pieces of two atlases** (pointwise): `piece_i g = ∑_j T_{ij}(piece'_j g)`, since
`ψ_i g = ∑_j ψ_i ψ'_j g` and `θ'_j ψ'_j = ψ'_j`. -/
theorem piece_eq_sum_apply (i : Fin A.n) (g : M → ℂ) (y : E) :
    A.piece i g y = ∑ j, (A.transition A' i j).apply (A'.piece j g) y := by
  by_cases hy : y ∈ (A.ext i).target
  · set x := (A.ext i).symm y
    have hterm : ∀ j, (A.transition A' i j).apply (A'.piece j g) y =
        (A.psi i x : ℂ) * (A'.psi j x : ℂ) * g x := fun j => by
      rw [transition_apply]
      by_cases hxj : x ∈ (A'.chart j).source
      · have hyj : y ∈ (I.extendCoordChange (A.chart i) (A'.chart j)).source :=
          (mem_coordChange_source _ _).2 ⟨hy, hxj⟩
        have hxj' : x ∈ (A'.ext j).source := by rwa [OpenPartialHomeomorph.extend_source]
        have hz : A'.ext j x ∈ (A'.ext j).target := (A'.ext j).map_source hxj'
        have hzx : (A'.ext j).symm (A'.ext j x) = x := (A'.ext j).left_inv hxj'
        rw [indicator_of_mem hyj, coordChange_apply]
        simp only [transition, chartChange, piece]
        rw [indicator_of_mem hz, indicator_of_mem hz, hzx]
        push_cast
        have h := congrArg (fun t : ℝ => (t : ℂ)) (A'.theta_mul_psi j x)
        push_cast at h
        linear_combination (A.psi i x : ℂ) * g x * h
      · have hyj : y ∉ (I.extendCoordChange (A.chart i) (A'.chart j)).source := fun h =>
          hxj ((mem_coordChange_source _ _).1 h).2
        have hψ : A'.psi j x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hxj (A'.tsupport_psi_subset j h)
        rw [indicator_of_notMem hyj, hψ, Complex.ofReal_zero, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Complex.ofReal_sum, A'.sum_psi, Complex.ofReal_one, mul_one, piece, indicator_of_mem hy]
  · rw [piece, indicator_of_notMem hy]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [transition_apply, indicator_of_notMem fun h => hy ((mem_coordChange_source _ _).1 h).1]

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] (μ : Measure M)
  [IsSmoothMeasure I μ] [hB : Rd.BesovDomain (range I)] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)

/-- **The pieces of two atlases in `L_p`**: `piece_i f = ∑_j T_{ij}(piece'_j f)`, with the changes
of charts acting on `L_p(E)`. -/
theorem pieceLp_eq_sum (i : Fin A.n) (f : Lp ℂ p μ) :
    A.pieceLp μ hp i f = ∑ j, (A.transition A' i j).applyLp hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp (A'.pieceLp μ hp j f) := by
  refine Lp.ext ?_
  have h3 : ∀ᵐ y ∂volume, ∀ j, (A.transition A' i j).applyLp hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp (A'.pieceLp μ hp j f) y =
        (A.transition A' i j).apply (A'.piece j f) y :=
    ae_all_iff.2 fun j => ((A.transition A' i j).applyLp_ae hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp _).trans
        ((A.transition A' i j).apply_ae_eq ((A'.pieceLp_ae μ hp j f).mono fun y hy _ => hy))
  filter_upwards [A.pieceLp_ae μ hp i f, Lp.coeFn_fun_finsetSum Finset.univ
    (fun j => (A.transition A' i j).applyLp hB.convex hB.interior_nonempty
      (Rd.BesovDomain.measurableSet (range I)) hp (A'.pieceLp μ hp j f)), h3] with y hy1 hy2 hy3
  rw [hy1, hy2, A.piece_eq_sum_apply A' i f y]
  exact Finset.sum_congr rfl fun j _ => (hy3 j).symm

end Transition

end BesovAtlas

end Manifold
