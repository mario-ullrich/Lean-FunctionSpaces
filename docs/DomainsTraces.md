# Domains, manifolds and traces

Part of [Function spaces via approximation](../README.md). Blueprint chapters: the domain and trace
sections of Function spaces on `ℝ^d`, *Besov spaces on compact manifolds*.

With `V` and the kernels of [Function spaces on `ℝ^d`](Rd.md), the Besov spaces of a domain
`Ω ⊆ V` are described by intrinsic differences on `Ω` and as restrictions of `B^s_{p,q}(V)`, for
Lipschitz graph domains (Rychkov's extension) and for bounded Lipschitz domains (pasting with a
resolution of unity and pointwise multipliers). Traces on Lipschitz boundaries are built from the
atoms and hold for `0 < s < 1`; on the half-space, where smooth atoms restrict to smooth atoms,
the trace theorem holds for every `s > 0`. Compact manifolds with boundary carry Besov spaces in
the charts of a Besov atlas; the invariance under changes of variables makes them independent of
the atlas, and the trace theorem of the half-space carries over to the boundary for every
`s > 0`. Smooth bounded domains are such manifolds, and their chart spaces are the intrinsic
Besov spaces.

## Main results

* **Rychkov's extension for Lipschitz graph domains.** Let `Ω = {x ∈ V : φ(x) < ⟪x, e⟫}` for a
  unit vector `e` and a Lipschitz function `φ` that is constant along `e`
  (`Rd.LipschitzGraph`), and let `k_j`, `η_j` be the local means kernels of
  [Function spaces on `ℝ^d`](Rd.md) for a bump `g` that vanishes
  outside `-K ∩ B(0, 1/2)`, where `K` is a cone with `Ω + K ⊆ Ω`
  (`Rd.LipschitzGraph.coneBump`). For `0 < s < L`, `1 ≤ q ≤ ∞` and `f ∈ L_p(V)`, `f` agrees on
  `Ω` with some `F ∈ L_p(V)` with `‖F‖_p + ‖(2^(ks) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖(2^(js) ‖k_j ⋆ f‖_{L_p(Ω)})_j‖_{ℓ_q} < ∞` (`Rd.LipschitzGraph.exists_besov_extension_iff`).
  Then `Ext f = ∑_j η_j ⋆ (1_Ω (k_j ⋆ f))` is such an `F`, the same operator for all
  `0 < s < L` (`Rd.LipschitzGraph.extension`, `Rd.LipschitzGraph.cutoff_extension`,
  `Rd.LipschitzGraph.modNorm_extension_le`).
* **Besov spaces on Lipschitz graph domains by intrinsic differences.** With `Ω` as above, let
  `ω_r(f, t, Ω)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_{L_p(Ω_{rh})}`, where
  `Ω_{rh} = {x : x, x + h, …, x + rh ∈ Ω}`, be the modulus of smoothness on `Ω`
  (`Rd.modulusOn`). For `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)` agrees on `Ω`
  with some `F ∈ L_p(V)` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, with equivalent quasi-norms, and
  `Ext f` is such an `F` (`Rd.LipschitzGraph.exists_besov_extension_iff_modulusOn`,
  `Rd.LipschitzGraph.modNormOn_le_modNorm`, `Rd.LipschitzGraph.modNorm_extension_le_modNormOn`).
  The same condition describes the restrictions to `Ω` of the band-limited approximation spaces
  `A^s_q(L_p(V), (E_k))` (`Rd.LipschitzGraph.exists_memApprox_extension_iff`).
* **Besov spaces on bounded Lipschitz domains by intrinsic differences.** Let `Ω ⊆ V` be a bounded
  Lipschitz domain: a bounded open set whose boundary is covered by finitely many open balls `B_j`,
  centred on the boundary, with `B_j ∩ Ω = B_j ∩ Ω_j` for Lipschitz graph domains `Ω_j`
  (`Rd.BoundedLipschitzDomain`). For `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)` agrees
  on `Ω` with some `F ∈ L_p(V)` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, and the same condition describes the
  restrictions of the band-limited approximation spaces
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn`,
  `Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff`). The proof pastes local versions of
  Rychkov's extension (`Rd.LocalMeansBump.exists_local_extension`) with a smooth resolution of
  unity; smooth functions with bounded derivatives are pointwise multipliers of the Besov spaces
  by differences (`Rd.modNorm_mulLp_le`).
* **Traces on Lipschitz graph domains.** Let `Ω` be a Lipschitz graph domain as above, with
  Lipschitz constant `M`, and `H = e^⊥`. The boundary of `Ω` is the image of the graph map
  `γ(x') = x' + φ(x') e`, `x' ∈ H` (`Rd.LipschitzGraph.graphMap`). For `f ∈ L_p(V)` the trace
  `Tr f = ∑_j (η_j ⋆ 1_Ω (k_j ⋆ f)) ∘ γ`, with the kernels of the cone bump, is a function in
  `L_p(H)` (`Rd.LipschitzGraph.trace`). For `1 ≤ p < ∞`, `0 < s < 1` and `1 ≤ q ≤ ∞` there is
  `K < ∞` with
  `‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr f, 2^(-k))_p)_k‖_{ℓ_q} ≤ K (‖f‖_{L_p(Ω)} +
  ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})` (`Rd.LipschitzGraph.modNorm_trace_le`), and
  `Tr f = G ∘ γ` almost everywhere if `f` has a continuous representative `G`
  (`Rd.LipschitzGraph.trace_ae_eq_comp_graphMap`). The cell atoms of the terms restrict to atoms of
  order `1` on `H` (`Rd.LipschitzGraph.isRegularAtom_comp_graphMap`), and the atomic synthesis on
  `H` gives the bound.
* **The trace space of a Lipschitz graph domain.** For `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and
  `L ≥ 2`, `g ∈ L_p(H)` is the trace of some `f ∈ L_p(V)` with
  `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff
  `‖g‖_p + ‖(2^(ks) ω_1(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (`Rd.LipschitzGraph.exists_trace_eq_iff`). The
  extension `E g` (`Rd.LipschitzGraph.graphExtension`) extends the atoms of `g` by
  `A(x) = a(Px) χ(2^j (⟪x, e⟫ - φ_j(Px)))` with a graph `φ_j` mollified at scale `2^(-j)`; it has a
  finite `B^{s+1/p}_{p,q}`-norm on `V` (`Rd.LipschitzGraph.modNorm_graphExtension_le`) and the trace
  `g` (`Rd.LipschitzGraph.trace_graphExtension`).
* **Traces of every order on the half-space.** Let `Ω = {x : ⟪x, e⟫ > 0}` for a unit vector `e`
  (`Rd.LipschitzGraph.flat`) and `H = e^⊥`. For `1 ≤ p < ∞`, `s > 0`, `1 ≤ q ≤ ∞`, `L ≥ 2` with
  `s + 1/p < L`, and `r > s`, `g ∈ L_p(H)` is the trace of some `f ∈ L_p(V)` with
  `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff
  `‖g‖_p + ‖(2^(ks) ω_r(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (`Rd.LipschitzGraph.exists_trace_eq_iff_flat`).
  The trace is bounded for every `s > 0` (`Rd.LipschitzGraph.modNorm_trace_le_flat`), since the cell
  atoms restrict to smooth atoms on `H`; the extension
  `E g = ∑_j (η_j ⋆ k_j ⋆ g)(Px) χ(2^j ⟪x, e⟫)` with local means of moment order `r` on `H`
  (`Rd.LipschitzGraph.flatExtension`) is bounded
  (`Rd.LipschitzGraph.modNorm_flatExtension_le`) and has the trace `g`
  (`Rd.LipschitzGraph.trace_flatExtension`).
* **The half-space is a Besov domain.** A Besov domain is a closed convex set with nonempty
  interior whose functions of finite intrinsic quasi-norm extend to `V` with a bound
  (`Rd.BesovDomain`, see [Function spaces on `ℝ^d`](Rd.md)). The closed half-space is a Besov
  domain (`Rd.BesovDomain.closedHalfSpace`), and so are the models of manifolds with and without
  boundary (`Rd.BesovDomain.range_euclideanHalfSpace`, `Rd.BesovDomain.range_of_boundaryless`).
* **Besov spaces on compact manifolds.** Let `M` be a compact smooth manifold modelled on `E` with
  corners `I` whose range is a Besov domain (the half-space or `E`), `μ` a smooth measure (in
  every chart a continuous positive density with respect to the Lebesgue measure,
  `Manifold.IsSmoothMeasure`) and `1 ≤ p < ∞`. A Besov atlas consists of finitely many charts
  `κ_i`, a smooth partition of unity `ψ_i` subordinate to them and cut-offs
  (`Manifold.BesovAtlas`); every compact manifold has one (`Manifold.BesovAtlas.nonempty`). Its
  Besov quasi-norm is `‖f‖_{A,r,s,q} = ∑_i N_Ω((ψ_i f) ∘ κ_i⁻¹)` with
  `N_Ω(G) = ‖G‖_{L_p(Ω)} + ‖(2^(ks) ω_r(G, 2^(-k), Ω)_p)_k‖_{ℓ_q}`, `Ω = range I`
  (`Manifold.BesovAtlas.besovNorm`). For two Besov atlases, `0 < s < r` and `1 ≤ q ≤ ∞` there is
  `C < ∞` with `‖f‖_{A,r,s,q} ≤ C ‖f‖_{A',r,s,q}` for all `f ∈ L_p(μ)`
  (`Manifold.BesovAtlas.besovNorm_le_besovNorm`), so `B^s_{p,q}(M)` (`Manifold.MemBesov`) depends
  neither on the atlas nor on the order (`Manifold.memBesov_iff`,
  `Manifold.BesovAtlas.memBesov_iff_besovNorm_lt_top`). The pieces of two atlases are related by
  the changes of charts with cut-offs (`Manifold.BesovAtlas.pieceLp_eq_sum`), which are bounded on
  the Besov domain.
* **Smooth bounded domains as manifolds with boundary.** The closure of a smooth bounded domain
  `Ω ⊆ ℝ^n` (a bounded Lipschitz domain with smooth graph functions, `Rd.SmoothDomain`) is a
  compact smooth manifold with boundary modelled on the half-space `{y : y_0 ≥ 0}`
  (`Rd.SmoothDomain.isManifold`): near the boundary the charts are the straightenings
  `x ↦ A(x - φ(x) e)`, which preserve the Lebesgue measure
  (`Rd.LipschitzGraph.measurePreserving_flatten`), so the Lebesgue measure is a smooth measure
  (`Rd.SmoothDomain.isSmoothMeasure_volumeOn`). For `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`,
  `f ∈ L_p(closure Ω)` lies in the Besov space `B^s_{p,q}` of this manifold iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
  (`Rd.SmoothDomain.memBesov_iff_modNormOn_lt_top`): the descriptions by charts, by intrinsic
  differences and as restrictions of `B^s_{p,q}(ℝ^n)` coincide.
* **Besov spaces on the boundary of a compact manifold.** Let `M` be a compact smooth manifold
  with boundary modelled on the half-space `{y ∈ ℝ^n : y_0 ≥ 0}`. The changes of charts map the
  boundary hyperplane `H₀ = {y_0 = 0}` into itself (`Manifold.coordChange_mem_bdry`), and their
  restrictions to `H₀` are smooth changes of variables with cut-offs on all of `H₀`
  (`Manifold.boundaryChartChange`). For a Besov atlas `A`, `g : M → ℂ` lies in `B^s_{p,q}(∂M)`
  (`Manifold.BesovAtlas.MemBoundaryBesov`) if the restrictions to `H₀` of its chart pieces agree
  almost everywhere with functions in `B^s_{p,q}(H₀)`. For `1 ≤ p < ∞`, `s > 0` and
  `1 ≤ q ≤ ∞` this does not depend on the atlas
  (`Manifold.BesovAtlas.memBoundaryBesov_iff_memBoundaryBesov`).
* **The trace theorem on compact manifolds with boundary.** With `M` as above, a smooth measure `μ`,
  `1 ≤ p < ∞`, `s > 0`, `1 ≤ q ≤ ∞` and the trace `Tr` of order `L ≥ 2`, `L > s + 1/p`, of the
  half-space, the trace of `f ∈ L_p(μ)` on `∂M` is
  `Tr_A f = ∑_i θ_i · Tr((ψ_i f) ∘ κ_i⁻¹) ∘ P ∘ κ_i` (`Manifold.BesovAtlas.boundaryTrace`). The
  trace commutes with the changes of charts
  (`Manifold.trace_chartChange_applyLp`), so for `f ∈ B^{s+1/p}_{p,q}(M)` the boundary pieces of
  `Tr_A f` are the traces of the chart pieces of `f`, for every atlas
  (`Manifold.BesovAtlas.boundaryPiece_boundaryTrace_of_atlas`). `B^s_{p,q}(∂M)` is the trace space
  of `B^{s+1/p}_{p,q}(M)`: `g ∈ B^s_{p,q}(∂M)` iff the boundary pieces of `g` agree almost
  everywhere with those of `Tr_A f` for some `f ∈ B^{s+1/p}_{p,q}(M)`
  (`Manifold.BesovAtlas.memBoundaryBesov_iff_exists_boundaryTrace`). For the closure of a smooth
  bounded domain this is the trace theorem on its boundary for every `s > 0`.
* **Traces on bounded Lipschitz domains.** Let `Ω` be a bounded Lipschitz domain with boundary `Γ`,
  boundary balls `B_j` and graph domains `Ω_j` as above, and `(ψ_j)` a smooth resolution of unity on
  `Γ` with `tsupport ψ_j ⊆ B_j` (`Rd.BoundedLipschitzDomain.BoundaryPartition`). A property holds
  almost everywhere on `Γ` if for every `j` it holds at `γ_j(x')` for almost every `x' ∈ H_j` with
  `γ_j(x') ∈ B_j` (`Rd.BoundedLipschitzDomain.aeBoundary`), and `g ∈ B^s_{p,q}(Γ)` if every chart
  piece `(ψ_j g) ∘ γ_j` agrees almost everywhere with some `G_j ∈ L_p(H_j)` with
  `‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Rd.BoundedLipschitzDomain.MemBoundaryBesov`). The boundary trace is
  `Tr_Γ F(y) = ∑_k ψ_k(y) Tr_k F(P_k y)` (`Rd.BoundedLipschitzDomain.boundaryTrace`). For
  `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, `g ∈ B^s_{p,q}(Γ)` iff `g = Tr_Γ F` almost
  everywhere on `Γ` for some `F ∈ L_p(V)` with
  `‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_iff`), and iff `g` is the boundary trace of
  some `f` with `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`); every such `f` has a
  boundary trace in `B^s_{p,q}(Γ)`, unique almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_modNormOn_lt_top`,
  `Rd.BoundedLipschitzDomain.IsBoundaryTrace.unique`). The boundary trace
  depends only on `F` on `Ω` (`Rd.BoundedLipschitzDomain.boundaryTrace_congr`), it is the
  restriction for continuous `F`
  (`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq_of_continuous`), and neither the trace nor
  `B^s_{p,q}(Γ)` depends on the resolution of unity
  (`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`,
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_of_boundaryPartition`). The proof rests on the
  change of chart for the traces of graph domains (`Rd.LipschitzGraph.trace_ae_eq_trace_comp`),
  whose Lipschitz chart maps keep null sets (`Rd.volume_image_eq_zero_of_lipschitzWith`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Lipschitz graph domains: cone and closed cone, cone bump, support principle | ✅ | ✗ | `Rd/LipschitzGraph` |
| Rychkov's extension, restrictions to Lipschitz graph domains by intrinsic local means | ✅ | ✗ | `Rd/RychkovExtension` |
| Restrictions to Lipschitz graph domains by intrinsic differences | ✅ | ✗ | `Rd/LipschitzGraphBesov` |
| Local versions of Rychkov's extension: boundary and inner patches, short steps into the closed cone, absolute convergence from bounds of the weighted local means, agreement on the patch for every convergent local extension | ✅ | ✗ | `Rd/LocalExtension` |
| Bounded Lipschitz domains: the patches covering the closure, restrictions by intrinsic differences | ✅ | ✗ | `Rd/BoundedLipschitz` |
| The half-space and the models of manifolds as Besov domains | ✅ | ✗ | `Rd/HalfSpace` |
| Traces of every order on the half-space: trace theorem, extension, trace space | ✅ | ✗ | `Rd/HalfSpaceTrace` |
| Graph map of a Lipschitz graph domain, restrictions of atoms to the graph | ✅ | ✗ | `Rd/GraphParametrization` |
| Traces on Lipschitz graph domains: boundedness, linearity, trace of continuous functions | ✅ | ✗ | `Rd/GraphTrace` |
| Mollified graph and vertical cut-off with bounds of their differences | ✅ | ✗ | `Rd/MollifiedGraph` |
| Extension from the boundary of a Lipschitz graph domain, its trace space | ✅ | ✗ | `Rd/GraphTraceExtension` |
| Traces in charts: locality, approximation, change of chart, products, finite sums | ✅ | ✗ | `Rd/GraphTraceCharts` |
| Traces on bounded Lipschitz domains: Besov spaces on the boundary, the trace space | ✅ | ✗ | `Rd/LipschitzBoundaryTrace` |
| Smooth measures on manifolds, integrals in charts | ✅ | ✗ | `Manifold/SmoothMeasure` |
| Besov atlases, chart pieces, changes of charts with cut-offs | ✅ | ✗ | `Manifold/BesovAtlas` |
| Besov spaces on compact manifolds, independence of the atlas and of the order | ✅ | ✗ | `Manifold/Besov` |
| Flattening of graph domains, preservation of the Lebesgue measure | ✅ | ✗ | `Rd/GraphStraightening` |
| Smooth bounded domains as compact manifolds with boundary, Lebesgue measure as smooth measure | ✅ | ✗ | `Manifold/SmoothDomain` |
| Besov spaces of smooth domains by charts equal the intrinsic Besov spaces | ✅ | ✗ | `Manifold/SmoothDomainBesov` |
| Besov spaces on the boundary of a compact manifold, independence of the atlas | ✅ | ✗ | `Manifold/BoundaryBesov` |
| Trace theorem on compact manifolds: commutation with charts, boundedness, trace space | ✅ | ✗ | `Manifold/BoundaryTrace` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
