# Domains, traces and manifolds

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Domains,
traces and manifolds*, chapters *Lipschitz domains*, *Traces on Lipschitz domains*, *Sobolev
spaces on domains* and *Besov spaces on compact manifolds*.

With `V` and the kernels of [Besov spaces on `ℝ^d`](Rd.md), the Besov spaces of a domain
`Ω ⊆ V` are described by intrinsic differences on `Ω` and as restrictions of `B^s_{p,q}(V)`, for
Lipschitz graph domains (Rychkov's extension) and for bounded Lipschitz domains (pasting with a
resolution of unity and pointwise multipliers). Traces on Lipschitz boundaries are built from the
atoms and hold for `0 < s < 1`; on the half-space, where smooth atoms restrict to smooth atoms,
the trace theorem holds for every `s > 0`. Compact manifolds with boundary or with corners carry
Besov spaces in the charts of a Besov atlas, since the half-space and the quadrant are Besov
domains; the invariance under changes of variables makes them independent of the atlas, and for
manifolds with boundary the trace theorem of the half-space carries over to the boundary for every
`s > 0`. Smooth bounded domains are such manifolds, and their chart spaces are the intrinsic Besov
spaces. In finite dimension the bounded Lipschitz domains are the sets of the usual definition by
local Lipschitz graphs, the open balls and the bounded open convex sets among them; the smooth
bounded domains are the sets of the usual definition by smooth local graphs, the open
balls among them.

On a bounded Lipschitz domain, `H^1` is the space of restrictions of `H^1(ℝ^d)`, with weak
derivatives in `L_2` of the domain and boundary traces in `B^{1/2}_{2,2}` of the boundary. On every
open set the Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)`, for real `s`, are built inside
Mathlib's `H^s(ℝ^d)`, with the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`. On a bounded Lipschitz domain the
trace space `H^{1/2}(Γ)` is defined as the orthogonal complement of the trace kernel in `H^1(Ω)`, a
Hilbert space whose trace and extension operators have norm at most `1` by this definition, and
`H^{-1/2}(Γ)` is its dual; the link to `B^{1/2}_{2,2}(Γ)` is qualitative. On a Lipschitz graph
domain the area formula expresses Mathlib's Euclidean Hausdorff measure of the boundary in the
chart, with the Gram density `√(1 + ‖∇φ‖²)`. On a bounded Lipschitz domain the surface measure is
this Hausdorff measure on the boundary `Γ`; it gives the space `L_2(Γ)`, into which `H^1(Ω)` and
`H^{1/2}(Γ)` have bounded trace operators. The outward unit normal field is pasted from the chart
normals. On a bounded Lipschitz domain, every function of `W^1_p(Ω)`, `1 < p < ∞`, is the
restriction of a function of `W^1_p(ℝ^d)` under a bounded linear extension operator, built from
Rychkov's local extension with the local means of the gradient: the local means kernels of order two
are divergences of dilated kernels with mean zero, which form Calderón–Zygmund families. For `p = 2`
this identifies `H^1(Ω)` with `W^1_2(Ω)`. On a Lipschitz graph domain, the Gauss–Green theorem
`∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` holds for compactly supported `C^1` functions, and Green's formula
`∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)`, by the density of the
compactly supported Schwartz functions in every `H^s(ℝ^d)`. On a bounded Lipschitz domain, Green's
formula `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` holds for `u, w ∈ H^1(Ω)`,
with the trace `γ_{L_2} : H^1(Ω) → L_2(Γ)`, pasted from the graph domains with a resolution of unity
equal to one near the boundary; the outward unit normal is the chart normal almost everywhere on the
boundary, and the zero extension of `u ∈ H^1(Ω)` lies in `W^1_2(ℝ^d)` iff the trace of `u` vanishes.
The kernel of the trace is `H^1_0(Ω)`: mollification converges in `H^1(ℝ^d)`, and mollifiers
supported in the cone of a chart push the pieces of a function that vanishes outside `Ω` into `Ω`,
so `H̃^1(Ω)` consists of the functions of `H^1(ℝ^d)` that vanish outside `Ω`; with the zero
extension this gives `ker γ = H^1_0(Ω)`, `H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)` and
`(ker γ)^* ≅ H^{-1}(Ω)`. The [interface document](FEECInterface.md) lists the results for `p = 2`
for a FEEC/BEEC library built on this project, with the decisions behind their form.

## Main results

* **Rychkov's extension for Lipschitz graph domains.** Let `Ω = {x ∈ V : φ(x) < ⟪x, e⟫}` for a
  unit vector `e` and a Lipschitz function `φ` that is constant along `e`
  (`Rd.LipschitzGraph`), and let `k_j`, `η_j` be the local means kernels of
  [Besov spaces on `ℝ^d`](Rd.md) for a bump `g` that vanishes
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
  (`Rd.BoundedLipschitzDomain`, a structure that carries the balls and graph domains as data).
  Every bounded open set that agrees near each boundary point with the region above a Lipschitz
  graph in some direction (the usual definition, `Rd.IsBoundedLipschitzDomain`) is the carrier of
  such a structure, and conversely (`Rd.isBoundedLipschitzDomain_iff_exists`); every open ball and
  every bounded open convex set is such a carrier (`Rd.BoundedLipschitzDomain.ball`,
  `Rd.BoundedLipschitzDomain.ofConvex`). For
  `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)` agrees on `Ω` with some `F ∈ L_p(V)`
  with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, and the same condition describes the
  restrictions of the band-limited approximation spaces
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn`,
  `Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff`). The extension comes with a bound:
  there is `C < ∞` such that `F` can be chosen with
  `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤`
  `C (‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})` for every `f`
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_le`). The proof pastes local
  versions of Rychkov's extension with a bound (`Rd.LocalMeansBump.exists_local_extension_le`)
  with a smooth resolution of unity fixed before `f` (`Rd.exists_pasting_le`); smooth functions
  with bounded derivatives are pointwise multipliers of the Besov spaces by differences
  (`Rd.modNorm_mulLp_le`).
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
  (`Rd.BesovDomain`, see [Besov spaces on `ℝ^d`](Rd.md)), a hypothesis class whose field is
  this extension. The closed half-space is a Besov domain (`Rd.BesovDomain.closedHalfSpace`), and
  so are `V` and the models of manifolds with and without boundary (`Rd.BesovDomain.univ`,
  `Rd.BesovDomain.range_euclideanHalfSpace`, `Rd.BesovDomain.range_of_boundaryless`). The class
  consists of closed convex sets; the quadrant, closed balls of positive radius and the closed
  unit cube are Besov domains as well (next item).
* **The extension property of Lipschitz graph domains and bounded Lipschitz domains; the quadrant
  and closures of convex sets as Besov domains.** A measurable set `Ω` has the extension property
  (`Rd.HasBesovExtension`) if for `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞` there is `C < ∞`
  such that every `f` with `N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
  agrees on `Ω` with some `F` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C N_Ω(f)`; a
  closed convex set with nonempty interior has it iff it is a Besov domain. The property passes to
  sets that agree up to a null set (`Rd.HasBesovExtension.congr_set`), and with it every order
  `r > s` gives the same space (`Rd.HasBesovExtension.modNormOn_order_le`). Every Lipschitz graph
  domain `{x : φ(x) < ⟪x, e⟫}` has it (`Rd.LipschitzGraph.hasBesovExtension`), its graph and its
  frontier are null sets (`Rd.LipschitzGraph.volume_graph`,
  `Rd.LipschitzGraph.volume_frontier_domain`), and for convex `φ` its closure is a Besov domain
  (`Rd.BesovDomain.closure_lipschitzGraph`). The open quadrant `{y ∈ ℝ^n : y_i > 0 for all i}` is
  the Lipschitz graph domain of `φ(y) = ⟪y, e⟫ - √n min_i y_i` with the diagonal
  `e = (1, …, 1)/√n` (`Rd.LipschitzGraph.quadrant`, `Rd.LipschitzGraph.quadrant_domain`), so the
  range `{y : y_i ≥ 0 for all i}` of Mathlib's model of manifolds with corners
  `modelWithCornersEuclideanQuadrant n` is a Besov domain
  (`Rd.BesovDomain.range_euclideanQuadrant`). Every bounded Lipschitz domain has the extension
  property (`Rd.BoundedLipschitzDomain.hasBesovExtension`), so the order `r > s` does not matter on
  it, convex or not (`Rd.BoundedLipschitzDomain.modNormOn_order_le`); its closure agrees with it up
  to the null frontier (`Rd.BoundedLipschitzDomain.closure_ae_eq`), and for nonempty convex
  domains the closure is a Besov domain (`Rd.BesovDomain.closure_boundedLipschitzDomain`). Hence
  the closure of every nonempty bounded open convex set is a Besov domain
  (`Rd.BesovDomain.closure_of_convex`), for example every closed ball `B̄(c, R)` with `R > 0` and
  the closed unit cube `[0, 1]^n` (`Rd.BesovDomain.closedBall`, `Rd.BesovDomain.closedUnitCube`).
* **Besov spaces on compact manifolds.** Let `M` be a compact smooth manifold modelled on `E` with
  corners `I` whose range is a Besov domain (the half-space, the quadrant of manifolds with
  corners, or `E`), `μ` a smooth measure (in every chart a continuous positive density with
  respect to the Lebesgue measure, `Manifold.IsSmoothMeasure`) and `1 ≤ p < ∞`. A Besov atlas
  consists of finitely many charts `κ_i`, a smooth partition of unity `ψ_i` subordinate to them and
  cut-offs (`Manifold.BesovAtlas`); every compact manifold has one
  (`Manifold.BesovAtlas.nonempty`). Its Besov quasi-norm is
  `‖f‖_{A,r,s,q} = ∑_i N_Ω((ψ_i f) ∘ κ_i⁻¹)` with
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
  differences and as restrictions of `B^s_{p,q}(ℝ^n)` coincide. `Rd.SmoothDomain` carries its
  charts as data; its carriers are exactly the bounded open sets that agree near each boundary
  point with the region above the graph of a function smooth near the origin
  (`Rd.IsBoundedSmoothDomain`, `Rd.isBoundedSmoothDomain_iff_exists`), and every open ball is one
  (`Rd.SmoothDomain.ball`, with its Besov spaces in `Rd.SmoothDomain.memBesov_ball_iff`).
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
  (`Rd.BoundedLipschitzDomain.MemBoundaryBesov`); first differences describe the range
  `0 < s < 1` of the trace theorem. The boundary trace is
  `Tr_Γ F(y) = ∑_k ψ_k(y) Tr_k F(P_k y)` (`Rd.BoundedLipschitzDomain.boundaryTrace`). For
  `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, `g ∈ B^s_{p,q}(Γ)` iff `g = Tr_Γ F` almost
  everywhere on `Γ` for some `F ∈ L_p(V)` with
  `‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_iff`), and iff `g` is the boundary trace of
  some `f` with `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`); every such `f` has a
  boundary trace in `B^s_{p,q}(Γ)`, unique almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_modNormOn_lt_top`,
  `Rd.BoundedLipschitzDomain.IsBoundaryTrace.unique`). The same statements hold for the
  predicate `Rd.BoundedLipschitzDomain.HasBoundaryTrace`, which contains the finite intrinsic
  norm of `f` (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_hasBoundaryTrace`,
  `Rd.BoundedLipschitzDomain.exists_hasBoundaryTrace_of_modNormOn_lt_top`,
  `Rd.BoundedLipschitzDomain.HasBoundaryTrace.unique`). The boundary trace
  depends only on `F` on `Ω` (`Rd.BoundedLipschitzDomain.boundaryTrace_congr`), it is the
  restriction for continuous `F`
  (`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq_of_continuous`), and neither the trace nor
  `B^s_{p,q}(Γ)` depends on the resolution of unity
  (`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`,
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_of_boundaryPartition`). The proof rests on the
  change of chart for the traces of graph domains (`Rd.LipschitzGraph.trace_ae_eq_trace_comp`),
  whose Lipschitz chart maps keep null sets (`Rd.volume_image_eq_zero_of_lipschitzWith`).
* **`H^1` on bounded Lipschitz domains.** Let `Ω` be a bounded Lipschitz domain with boundary `Γ`.
  `f ∈ L_2(V)` lies in `H^1(Ω)` if `f = F` almost everywhere on `Ω` for some `F ∈ W^1_2(V)`
  (`Rd.BoundedLipschitzDomain.MemSobolevOn`, a definition by extension); `H^1(Ω)` contains `0`, is
  closed under sums and complex multiples, and depends only on the values on `Ω`. For every order
  `r ≥ 2`, `f ∈ H^1(Ω)` iff `‖f‖_{L_2(Ω)} + ‖(2^k ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞`, with the
  moduli of smoothness inside `Ω` (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_modulusOn`). Every
  `f ∈ H^1(Ω)` lies in `W^1_2(Ω)`: its weak derivatives on `Ω` exist and lie in `L_2(Ω)`
  (`Rd.BoundedLipschitzDomain.MemSobolevOn.memWeakSobolev`); this direction holds by the definition,
  and the converse is the extension theorem below. For every resolution of unity on `Γ`, every
  `f ∈ H^1(Ω)` has a boundary trace in `B^{1/2}_{2,2}(Γ)`, unique almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memSobolevOn`,
  `Rd.BoundedLipschitzDomain.MemSobolevOn.isBoundaryTrace_unique`), and a function `g` lies in
  `B^{1/2}_{2,2}(Γ)` iff it is the boundary trace of some `f ∈ H^1(Ω)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_memSobolevOn`). The extensions in the
  definition of the boundary trace are the `F ∈ W^1_2(V)` with `F = f` on `Ω`
  (`Rd.BoundedLipschitzDomain.isBoundaryTrace_iff_forall_memSobolev`), and `f` has the boundary
  trace `g` with a finite intrinsic norm iff `f ∈ H^1(Ω)` and `g` is its boundary trace
  (`Rd.BoundedLipschitzDomain.hasBoundaryTrace_iff_memSobolevOn`). The extension and trace theorems
  for bounded Lipschitz domains are qualitative, and so are these statements; the restriction
  direction has constant `1` (`Rd.BoundedLipschitzDomain.modNormOn_le_modNorm_of_ae_eq`).
* **Sobolev spaces on open sets as Hilbert spaces.** Let `Ω ⊆ V` be open and `s` real. The
  elements of Mathlib's `H^s(V)` whose distribution vanishes on every test function of `Ω` form
  a closed subspace (`Rd.vanishOn`); for `s = 1` they are the elements vanishing almost
  everywhere on `Ω` (`Rd.mem_vanishOn_one_iff`). Its orthogonal complement is the Hilbert space
  `H^s(Ω)` (`Rd.RestrictionSpace`), and the restriction `U ↦ U|_Ω` is the orthogonal projection
  onto it (`Rd.restrictProj`). By this definition as an orthogonal complement, `H^s(Ω)` is
  isometric to the quotient of `H^s(V)` by the elements vanishing on `Ω`
  (`Rd.quotientEquivRestrictionSpace`), so `‖U|_Ω‖` is the minimum
  of `‖U + W‖` over the `W` vanishing on `Ω` (`Rd.norm_restrictProj_le_of_mem`,
  `Rd.exists_norm_restrictProj_eq`).
  The map `H^1(Ω) → L_2(Ω)` is injective with norm at most `1` (`Rd.restrictL2_injective`,
  `Rd.norm_restrictL2_apply_le`) and compact for bounded `Ω` (`Rd.isCompactOperator_restrictL2`;
  for the restriction space, this is the compactness of Assumption F of Hiptmair, Pauly and
  Schulz). Every `u ∈ H^1(Ω)` lies in `W^1_2(Ω)` (`Rd.memWeakSobolev_toL2`), and for an
  orthonormal basis `(e_i)` and the weak derivatives `∂_{e_i} u`,
  `‖u|_Ω‖_2² + (2π)⁻² ∑_i ‖(∂_{e_i} u)|_Ω‖_2² ≤ ‖u‖²` (`Rd.sq_norm_restr_add_sum_le`,
  `Rd.sq_norm_restrictL2_add_sum_le`), so the `W^1_2(Ω)` norm of `u|_Ω` is at most `2π ‖u‖`. On a
  bounded Lipschitz domain, `f ∈ L_2(V)` lies in `H^1(Ω)` in the sense of
  `Rd.BoundedLipschitzDomain.MemSobolevOn` iff `f|_Ω = u|_Ω` for some `u` in the Hilbert space
  `H^1(Ω)` (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`). `H̃^s(Ω)` is the
  closure of the test functions of `Ω` in `H^s(V)` (`Rd.tildeSpace`), `H^s_0(Ω)` the closure of
  their restrictions in `H^s(Ω)` (`Rd.zeroBoundarySpace`); for every open `Ω`, restriction is an
  isometry of `H̃^1(Ω)` onto `H^1_0(Ω)` (`Rd.tildeEquivZeroBoundary`), and inside `H^1(V)` the
  two are the same subspace (`Rd.coe_tildeEquivZeroBoundary_symm_apply`).
* **Duality on open sets.** Let `Ω ⊆ V` be open and `s` real. `J_{2s}` is an isometry of
  `H^s(V)` onto `H^{-s}(V)` (`Rd.besselShift`, `Rd.toDistr_besselShift`), and
  `[W, U] = ⟪J_{-s} W, J_s U⟫_{L_2}` pairs `W ∈ H^{-s}(V)` with `U ∈ H^s(V)` (`Rd.pairing`), with
  `|[W, U]| ≤ ‖W‖ ‖U‖`, `[φ, U] = U(φ)` for test functions `φ` of `Ω`, and
  `[ψ, U] = ⟪ψ, U⟫_{L_2}` for Schwartz `ψ` at `s = 1` (`Rd.norm_pairing_le`,
  `Rd.pairing_ofTest_left`, `Rd.pairing_one_toLp`). `U` is orthogonal to `H̃^s(Ω)` iff `J_{2s} U`
  vanishes on `Ω` (`Rd.mem_orthogonal_tildeSpace_iff`), so `J_{2s}` maps `H̃^s(Ω)` isometrically
  onto `H^{-s}(Ω)` and `H^s(Ω)` onto `H̃^{-s}(Ω)` (`Rd.tildeEquivRestriction`,
  `Rd.restrictionEquivTilde`). Every bounded functional `ℓ` on `H̃^s(Ω)` is `U ↦ [W, U]` for
  exactly one `W ∈ H^{-s}(Ω)`, with `‖W‖ = ‖ℓ‖` (`Rd.dualEquiv`, `Rd.dualEquiv_apply`,
  `Rd.dualEquiv_eq_iff`; Chandler-Wilde, Hewett and Moiola, Theorem 3.3), and every extension
  of `W` to `V` gives the same pairing (`Rd.dualEquiv_apply_of_restrictProj_eq`); likewise
  `(H^s(Ω))^* ≅ H̃^{-s}(Ω)` and `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` (`Rd.dualRestrictionEquiv`,
  `Rd.dualZeroBoundaryEquiv`). On the way, the Bessel potential `J_t` of a real Schwartz
  function is real (`Rd.conj_besselSchwartz_apply`), from `conj (𝓕 f) = 𝓕⁻(conj f)` on `V`
  (`Rd.conj_fourier_apply`).
* **The trace space of a bounded Lipschitz domain.** For every `U ∈ H^1(V)` with `L_2` function
  `ι U` (`Rd.toL2`), `‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with an explicit
  constant (`Rd.modNorm_two_le_norm`, `Rd.sobolevOneBesovConst`), and the `B^{1/2}_{2,1}` quantity
  is at most `√2` times this `B^1_{2,2}` quantity (`Rd.modNorm_half_one_le`), so
  `‖ι U‖_2 + ∑_k 2^(k/2) ω_2(ι U, 2^(-k))_2 ≤ √2 C ‖U‖` (`Rd.modNorm_half_one_le_norm`). Let `Ω` be
  a bounded Lipschitz domain with boundary `Γ` and `H^1(Ω)` the Hilbert space of the restriction
  space (`Rd.BoundedLipschitzDomain.SobolevOne`). The chart traces `u ↦ Tr_j(ψ_j u)` are bounded
  operators from `H^1(Ω)` to `L_2` of the hyperplanes of the charts
  (`Rd.BoundedLipschitzDomain.chartTrace`), and their common kernel, the trace kernel
  (`Rd.BoundedLipschitzDomain.traceKer`), consists of the `u` whose boundary trace vanishes almost
  everywhere on `Γ`, for every resolution of unity (`Rd.BoundedLipschitzDomain.mem_traceKer_iff`).
  The trace space `H^{1/2}(Γ)` is defined as its orthogonal complement
  (`Rd.BoundedLipschitzDomain.TraceSpace`), with the trace, the orthogonal projection, and the
  extension, the inclusion. By this definition `γ E = id`, `‖γ u‖ ≤ ‖u‖`, `‖E t‖ = ‖t‖`, the kernel
  of `γ` is the trace kernel, and `H^1(Ω) ⧸ ker γ ≅ H^{1/2}(Γ)` isometrically
  (`Rd.BoundedLipschitzDomain.trace_extend`, `Rd.BoundedLipschitzDomain.ker_trace`,
  `Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`). Two elements of `H^1(Ω)` have the same trace
  iff their boundary traces agree almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.trace_eq_iff`), and `t ↦ Tr_Γ(E t)` maps `H^{1/2}(Γ)` onto
  `B^{1/2}_{2,2}(Γ)` modulo null sets of `Γ` (`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
  `Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`); this link is qualitative, a
  norm equivalence of `H^{1/2}(Γ)` with `B^{1/2}_{2,2}(Γ)` is not formalised. `H^{-1/2}(Γ)` is the
  dual of the trace space (`Rd.BoundedLipschitzDomain.DualTraceSpace`), conjugate-linearly isometric
  to it by Riesz (`Rd.BoundedLipschitzDomain.dualTraceEquiv`), and the adjoint of the trace is the
  extension (`Rd.BoundedLipschitzDomain.adjoint_trace`).
* **The area formula for Lipschitz graphs.** Let `Ω = {x : φ(x) < ⟪x, e⟫}` be a Lipschitz graph
  domain in `V`, `dim V = n`, with the graph map `γ(x') = x' + φ(x') e` over the hyperplane
  `H = e^⊥`, whose range is the boundary of `Ω` (`Rd.LipschitzGraph.range_graphMap`), and let
  `∇φ(x') ∈ H` be the gradient of `φ` on `H`, which exists almost everywhere
  (`Rd.LipschitzGraph.gradPhi`). For every measurable `A ⊆ H`,
  `μHE[n-1] (γ(A)) = ∫_A √(1 + ‖∇φ(x')‖²) dx'` for Mathlib's `(n-1)`-dimensional Euclidean
  Hausdorff measure `μHE[n-1]`, normalised to be the volume on hyperplanes
  (`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphMap_image`); equivalently, for every
  `F : V → [0, ∞]`, `∫_{γ(H)} F dμHE[n-1] = ∫_H F(γ x') √(1 + ‖∇φ(x')‖²) dx'`
  (`Rd.LipschitzGraph.lintegral_graphMap`, `Rd.LipschitzGraph.map_graphMap_withDensity`). For
  the linear graphs `S_g x' = x' + ⟪g, x'⟫ e`, `μHE[n-1] (S_g(P)) = √(1 + ‖g‖²) vol(P)` for every
  `P ⊆ H` (`Rd.LipschitzGraph.euclideanHausdorffMeasure_linearGraph_image`), by Mathlib's area
  formula for linear maps with the norm determinant `√(1 + ‖g‖²)` of `S_g`
  (`Rd.LipschitzGraph.normDet_linearGraph`). The outward unit normal
  `ν = (∇φ - e)/√(1 + ‖∇φ‖²)` is a measurable unit vector with `⟪ν, y⟫ < 0` for every `y` in the
  cone of `Ω` (`Rd.LipschitzGraph.normalAt`, `Rd.LipschitzGraph.norm_normalAt`,
  `Rd.LipschitzGraph.inner_normalAt_neg_of_mem_cone`).
* **The surface measure of a bounded Lipschitz domain.** Let `Ω` be a bounded Lipschitz domain
  in `V`, `dim V = n`, with boundary `Γ`, boundary balls `B_j` and charts `γ_j` over the
  hyperplanes `H_j`. The surface measure `σ` is `μHE[n-1]` restricted to `Γ`
  (`Rd.BoundedLipschitzDomain.surfaceMeasure`). For every `F : V → [0, ∞]` vanishing outside
  `B_j`, `∫_Γ F dσ = ∫_{H_j} F(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'`
  (`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support`), and for every resolution of
  unity `ψ` with `ψ_j ≥ 0` on `Γ` and every `F`,
  `∫_Γ F dσ = ∑_j ∫_{H_j} ψ_j(γ_j x') F(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'`
  (`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure`); the same holds for every resolution of
  unity and every `σ`-integrable `f : V → ℂ`
  (`Rd.BoundedLipschitzDomain.integral_surfaceMeasure`). `σ` is finite
  (`Rd.BoundedLipschitzDomain.isFiniteMeasure_surfaceMeasure`), its null sets are those of the
  charts (`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_iff_aeBoundary`), and `|Γ| = 0`
  (`Rd.BoundedLipschitzDomain.volume_frontier`). The boundary trace of the trace theorem lies in
  `L_p(σ)` (`Rd.BoundedLipschitzDomain.memLp_boundaryTrace`). With `L_2(Γ) = L_2(σ)`
  (`Rd.BoundedLipschitzDomain.BoundaryL2`), the trace `γ_{L_2} : H^1(Ω) → L_2(Γ)` and the
  injective `τ : H^{1/2}(Γ) → L_2(Γ)` are bounded operators with `γ_{L_2} = τ ∘ γ`, given almost
  everywhere by the boundary trace, and the kernel of `γ_{L_2}` is the trace kernel
  (`Rd.BoundedLipschitzDomain.boundaryTraceL2`, `Rd.BoundedLipschitzDomain.traceL2`,
  `Rd.BoundedLipschitzDomain.traceL2_injective`, `Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`);
  every `g ∈ B^{1/2}_{2,2}(Γ)` is `τ t` for some `t`, so `B^{1/2}_{2,2}(Γ) ⊆ L_2(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_ae_eq`,
  `Rd.BoundedLipschitzDomain.memLp_of_memBoundaryBesov`). The outward unit normal field
  `ν(y) = ∑_j ψ_j(y) ν_j(P_j y)`, with the chart normals `ν_j` and the canonical resolution of
  unity `ψ` (`Rd.BoundedLipschitzDomain.boundaryPartition`, nonnegative), is measurable with
  `‖ν‖ ≤ 1` (`Rd.BoundedLipschitzDomain.normal`, `Rd.BoundedLipschitzDomain.norm_normal_le`).
* **Divergence kernels.** Let `(e_i)` be an orthonormal basis of `V`, `n = dim V`, and
  `m_c(x) = c^n m(c x)`. For every smooth `m`, `m_2 - m = ∑_i ∂_{e_i} K_i` with the divergence
  kernels `K_i(x) = ⟪e_i, x⟫ ∫_1^2 t⁻¹ m_t(x) dt` (`Rd.divergenceKernel`,
  `Rd.dilationAverage_eq_integral_inv_mul`, `Rd.sum_fderiv_divergenceKernel`), by Euler's identity
  `d/ds m_{e^s}(x) = n m_{e^s}(x) + D(m_{e^s})(x) x` (`Rd.hasDerivAt_dilate_exp`). The kernels
  are smooth, since parametric integrals of smooth functions are smooth
  (`intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff`), they vanish where
  `m(t x) = 0` for all `t ∈ [1, 2]` (`Rd.divergenceKernel_eq_zero`), and they have mean zero when
  the first moments of `m` vanish (`Rd.integral_divergenceKernel`), as for the moment kernels of
  order two (`Rd.integral_inner_mul_momentKernel_two`). For every Schwartz function `G` with
  `∫ G = 0`, `|𝓕G(ξ)| ≤ C min(‖ξ‖, ‖ξ‖⁻¹)` with `C = 2π ∫ ‖x‖ |G(x)| dx + C_G/(2π)`
  (`Rd.enorm_fourier_le_mul_min`), so `∑_j |𝓕(G_{2^j})(ξ)|² ≤ 4C²` and the dilates `G_{2^j}`
  form a Calderón–Zygmund family (`Rd.isCZFamily_dilate_of_integral_eq_zero`).
* **The extension theorem.** Let `Ω` be a bounded Lipschitz domain in `V` of dimension `n ≥ 1`,
  `(e_i)` the orthonormal basis `Rd.gridBasis V`, and `1 < p < ∞`. There is a finite `C` such that
  every `f ∈ L_p(Ω)` with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` on `Ω` agrees almost
  everywhere on `Ω` with some `F ∈ W^1_p(V)` whose weak derivatives `G_i = ∂_{e_i} F` satisfy
  `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`); hence `f ∈ W^1_p(Ω)` iff `f` agrees on `Ω`
  with some `F ∈ W^1_p(V)` (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev`).
  For `p = 2`, `f ∈ L_2(V)` lies in `H^1(Ω)` iff `f ∈ W^1_2(Ω)`
  (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_restrictL2`), every sequence bounded in
  `W^1_2(Ω)` has a subsequence converging in `L_2(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`), and the quotient norm of
  the Hilbert space `H^1(Ω)` is bounded by the `W^1_2(Ω)` norm
  (`Rd.BoundedLipschitzDomain.exists_norm_le_restrictL2`), so the two norms are equivalent; the
  boundary traces of `H^1(Ω)` serve for `W^1_2(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.isBoundaryTrace_unique_of_memWeakSobolev`). The membership
  statements hold in every dimension; for `n = 0`, `F = f` or `F = 0` serves
  (`Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton`). The proof is Rychkov's local
  extension with the local means of the gradient: for a bump with the moment kernel `m` of order
  two, `k_{j+1} = 2^{-j} ∑_i ∂_{e_i} (K_i)_{2^j}`
  (`Rd.LocalMeansBump.kernel_two_succ_apply`), so on a patch
  `k_{j+1} ⋆ 1_T f = 2^{-j} ∑_i (K_i)_{2^j} ⋆ 1_T g_i`
  (`Rd.LocalMeansBump.conv_kernel_two_succ_eq`),
  the strong type of the Calderón–Zygmund families `((K_i)_{2^j})_j` bounds the local means of
  Triebel–Lizorkin type of `f` on the patch (`Rd.LocalMeansBump.tlLocalNormOn_le_patchConst`), the
  local extension lies in `F^1_{p,2} = W^1_p` (`Rd.LocalMeansBump.extendsSobolev`), and a smooth
  resolution of unity pastes the local extensions in `W^1_p(V)` (`Rd.extendsSobolev_of_cover`).
  The constants are existential. The extension is a bounded linear operator
  `E : W^1_p(Ω) → W^1_p(V)` on value–derivative jets with `E u = u` on `Ω`
  (`Rd.BoundedLipschitzDomain.sobolevExtensionL`, `Rd.BoundedLipschitzDomain.exists_extensionL`);
  it is of first order, and the exponents `p ∈ {1, ∞}` are not formalised.
* **Gauss–Green on Lipschitz graph domains.** Let `Ω = {x : φ(x) < ⟪x, e⟫}` be a Lipschitz graph
  domain with the graph map `γ(x') = x' + φ(x') e` over the hyperplane `H = e^⊥`, the gradient
  `∇φ` of `φ|_H`, the outward unit normal `ν` and `n = dim V`, and let
  `n_v = ⟪∇φ, v⟫ - ⟪v, e⟫ = ⟪v, ν⟫ √(1 + ‖∇φ‖²)` (`Rd.LipschitzGraph.normalWeight`,
  `Rd.LipschitzGraph.inner_normalAt_mul_gram`). For every `C^1` function `g` with compact support
  and every `v ∈ V`, `∫_Ω ∂_v g = ∫_H g(γ x') n_v(x') dx' = ∫_{γ(H)} g ⟪v, ν ∘ P⟫ dμHE[n-1]`
  (`Rd.LipschitzGraph.setIntegral_lineDeriv_eq`,
  `Rd.LipschitzGraph.setIntegral_lineDeriv_eq_surface`). For all `f, g ∈ W^1_2(V)` and their weak
  derivatives `f_v = ∂_v f`, `g_v = ∂_v g` in `L_2(V)`,
  `∫_Ω f_v g + f g_v = ∫_H Tr f · Tr g · n_v` with the traces of the trace theorem
  (`Rd.LipschitzGraph.setIntegral_green`); for `U, W ∈ H^1(V)` with the bounded trace operator
  `H^1(V) → L_2(H)` (`Rd.LipschitzGraph.traceH1`), also in surface form
  (`Rd.LipschitzGraph.setIntegral_green_besselPotentialSpace`,
  `Rd.LipschitzGraph.setIntegral_green_surface`).
  The proof writes `∫_Ω ∂_v g` in product coordinates (`Rd.LipschitzGraph.setIntegral_domain_eq`)
  through the ray integral `Ψ(y) = ∫_0^∞ g(y + t e) dt` (`Rd.rayIntegral`), whose composition with
  `γ` is Lipschitz with compact support (`Rd.LipschitzGraph.graphRayIntegral`), so that its
  directional derivatives integrate to zero (`Rd.integral_lineDeriv_eq_zero_complex`); Green's
  formula follows by continuity from compactly
  supported Schwartz functions, which are dense in `H^s(V)` for every real `s`
  (`Rd.dense_ofSchwartz_hasCompactSupport`; hence `H̃^s(V) = H^s(V)`, `Rd.tildeSpace_top`), with
  the weak derivative `∂_v` as a bounded operator `H^1(V) → L_2(V)` (`Rd.weakDerivL2`,
  `Rd.norm_weakDerivL2_le`).
* **Green's formula on bounded Lipschitz domains.** Let `Ω` be a bounded Lipschitz domain with
  boundary `Γ`, surface measure `σ`, outward unit normal field `ν`
  (`Rd.BoundedLipschitzDomain.normal`), boundary balls `B_j`, graph domains `Ω_j` with traces
  `Tr_j`, graph maps `γ_j` and normal weights `n^j_v`. For all `U, W ∈ H^1(V)` and every `v ∈ V`,
  `∫_Ω (∂_v U) W + U ∂_v W = ∫_Γ T_Γ U · T_Γ W ⟪v, ν⟫ dσ` with the trace `T_Γ : H^1(V) → L_2(Γ)`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_surface`), and for all `u, w ∈ H^1(Ω)`,
  `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` with the trace
  `γ_{L_2} : H^1(Ω) → L_2(Γ)` (`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne`), also
  with weak derivatives on `Ω`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne_of_hasWeakLineDeriv`). In chart form,
  for every resolution of unity `ψ` on `Γ`, all `f, g ∈ W^1_2(V)` and the weak derivatives
  `f_v = ∂_v f`, `g_v = ∂_v g` in `L_2(V)`,
  `∫_Ω f_v g + f g_v = ∑_j ∫_{H_j} ψ_j(γ_j x') Tr_j f(x') Tr_j g(x') n^j_v(x') dx'`
  (`Rd.BoundedLipschitzDomain.setIntegral_green`). On every ball `B_j`, `ν = ν_j ∘ P_j`
  `σ`-almost everywhere, so `‖ν‖ = 1` `σ`-almost everywhere
  (`Rd.BoundedLipschitzDomain.normal_ae_eq_normalAt`, `Rd.BoundedLipschitzDomain.norm_normal_ae`).
  For every `u ∈ H^1(Ω)`, the zero extension `1_Ω u` lies in `W^1_2(V)` iff the trace of `u`
  vanishes (`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_iff_mem_traceKer`), and then
  `∂_v (1_Ω u) = 1_Ω ∂_v u`
  (`Rd.BoundedLipschitzDomain.hasWeakLineDeriv_indicatorLp_of_mem_traceKer`). The proof pastes
  Green's formula on the graph domains with a resolution of unity equal to one near `Γ`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_of_nhds`); the interior piece integrates to zero
  by integration by parts in `H^1(V)` (`Rd.integral_weakDeriv_mul_add_eq_zero`). The chart normals
  agree almost everywhere because Gauss–Green for `C^1` functions in two charts gives the same
  boundary integrals (`Rd.BoundedLipschitzDomain.normalAt_graphMap_ae_eq`), and the traces from
  above and from below a graph agree (`Rd.LipschitzGraph.traceH1_ae_eq_traceH1_lower`).
* **The kernel of the trace.** Let `Ω` be a bounded Lipschitz domain with boundary `Γ`, `H^1(Ω)`
  the Hilbert space of restrictions of `H^1(V)`, `H̃^1(Ω)` the closure of the test functions of
  `Ω` in `H^1(V)`, `H^1_0(Ω)` the closure of their restrictions in `H^1(Ω)`, and `ker γ` the
  `u ∈ H^1(Ω)` whose boundary trace vanishes almost everywhere on `Γ`. Then
  `ker γ = H^1_0(Ω)` (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`; McLean,
  Theorem 3.40). For every `U ∈ H^1(V)`, `U ∈ H̃^1(Ω)` iff the `L_2` function of `U` vanishes
  almost everywhere outside `Ω` (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`). The map
  sending the class of `u` modulo `H^1_0(Ω)` to `γ u` is an isometric isomorphism
  `H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)`
  (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`), restriction is an isometric
  isomorphism `H̃^1(Ω) ≅ ker γ` (`Rd.BoundedLipschitzDomain.tildeEquivTraceKer`), and every
  bounded functional `ℓ` on `ker γ` is `u ↦ [W, u]` for exactly one `W ∈ H^{-1}(Ω)` with
  `‖W‖ = ‖ℓ‖` (`Rd.BoundedLipschitzDomain.dualTraceKerEquiv`,
  `Rd.BoundedLipschitzDomain.dualTraceKerEquiv_apply`,
  `Rd.BoundedLipschitzDomain.dualTraceKerEquiv_eq_iff`). The proof mollifies: for a Schwartz
  function `η` with `∫ η = 1` and `c_i → ∞`, `η_{c_i} ⋆ U → U` in `H^1(V)`
  (`Rd.tendsto_of_toL2_eq_convLp`), since weak derivatives commute with convolution
  (`Rd.hasWeakLineDeriv_convLp`); the pieces of `U` near the boundary vanish outside the closure
  of a graph domain, which convolution with a mollifier supported in the cone of the graph moves
  into the domain (`Rd.LipschitzGraph.coneMollifier`,
  `Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Lipschitz graph domains: cone and closed cone, the closure of the domain plus the cone, cone bump, support principle | ✅ | ✗ | `Domains/Lipschitz/LipschitzGraph` |
| Rychkov's extension, restrictions to Lipschitz graph domains by intrinsic local means | ✅ | ✗ | `Domains/Extension/RychkovExtension` |
| Restrictions to Lipschitz graph domains by intrinsic differences | ✅ | ✗ | `Domains/Extension/LipschitzGraphBesov` |
| Local versions of Rychkov's extension: boundary and inner patches, short steps into the closed cone, absolute convergence from bounds of the weighted local means, agreement on the patch for every convergent local extension, the local extension with a bound | ✅ | ✗ | `Domains/Extension/LocalExtension` |
| Bounded Lipschitz domains: the patches covering the closure, pasting of local extensions, the extension with a bound | ✅ | ✗ | `Domains/Lipschitz/BoundedLipschitz` |
| Null hyperplanes, the half-space and the models of manifolds as Besov domains | ✅ | ✗ | `Domains/Lipschitz/HalfSpace` |
| Traces of every order on the half-space: trace theorem, extension, trace space | ✅ | ✗ | `Domains/Traces/HalfSpaceTrace` |
| Graph map of a Lipschitz graph domain, restrictions of atoms to the graph | ✅ | ✗ | `Domains/Lipschitz/GraphParametrization` |
| Traces on Lipschitz graph domains: boundedness, linearity, trace of continuous functions | ✅ | ✗ | `Domains/Traces/GraphTrace` |
| Mollified graph and vertical cut-off with bounds of their differences | ✅ | ✗ | `Domains/Traces/MollifiedGraph` |
| Extension from the boundary of a Lipschitz graph domain, its trace space | ✅ | ✗ | `Domains/Traces/GraphTraceExtension` |
| Traces in charts: locality, approximation, change of chart, products, finite sums | ✅ | ✗ | `Domains/Traces/GraphTraceCharts` |
| Traces on bounded Lipschitz domains: Besov spaces on the boundary, the trace space | ✅ | ✗ | `Domains/Traces/LipschitzBoundaryTrace` |
| Smooth measures on manifolds, integrals in charts | ✅ | ✗ | `Domains/Manifolds/SmoothMeasure` |
| Besov atlases, chart pieces, changes of charts with cut-offs | ✅ | ✗ | `Domains/Manifolds/BesovAtlas` |
| Besov spaces on compact manifolds, independence of the atlas and of the order | ✅ | ✗ | `Domains/Manifolds/Besov` |
| Flattening of graph domains, the Lipschitz inverse and the graph in the image of the hyperplane, preservation of the Lebesgue measure | ✅ | ✗ | `Domains/Lipschitz/GraphStraightening` |
| Smooth bounded domains as compact manifolds with boundary, Lebesgue measure as smooth measure | ✅ | ✗ | `Domains/Manifolds/SmoothDomain` |
| Besov spaces of smooth domains by charts equal the intrinsic Besov spaces | ✅ | ✗ | `Domains/Manifolds/SmoothDomainBesov` |
| Besov spaces on the boundary of a compact manifold, independence of the atlas | ✅ | ✗ | `Domains/Manifolds/BoundaryBesov` |
| Trace theorem on compact manifolds: commutation with charts, boundedness, trace space | ✅ | ✗ | `Domains/Manifolds/BoundaryTrace` |
| `H^1` on bounded Lipschitz domains defined as restrictions of `H^1(ℝ^d)`, by intrinsic differences, the weak gradient, and the boundary traces, which form `B^{1/2}_{2,2}(Γ)` | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainH1` |
| The Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` on open sets inside Mathlib's `H^s(ℝ^d)`, `H^s(Ω)` as a quotient, Rellich's theorem for `H^1(Ω)`, the identification with the restriction space of a bounded Lipschitz domain, the restriction of an element agreeing with `u ∈ H^1(Ω)` on `Ω`, the bound of the `H^1` norm by the `W^1_2` norm, the weak derivatives as bounded operators on `H^1(ℝ^d)`, the density of compactly supported Schwartz functions in `H^s(ℝ^d)`, Schwartz functions with compact support in `Ω` in the span of the test functions, `H̃^s(ℝ^d) = H^s(ℝ^d)`, and the isometry `H̃^1(Ω) ≅ H^1_0(Ω)` | ✅ | ✗ | `Domains/Sobolev/SobolevRestrictionSpaces` |
| The Bessel potential of real Schwartz functions as a real function, the isometry `J_{2s} : H^s(ℝ^d) → H^{-s}(ℝ^d)`, the pairing of `H^{-s}` and `H^s`, and the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`, `(H^s(Ω))^* ≅ H̃^{-s}(Ω)`, `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` on open sets | ✅ | ✗ | `Domains/Sobolev/SobolevDuality` |
| `H^1(ℝ^d) ⊆ B^{1/2}_{2,1}(ℝ^d)` with explicit constants, the trace of `H^1(ℝ^d)` on a Lipschitz graph and the chart traces of `H^1(Ω)` on a bounded Lipschitz domain as bounded operators, the trace kernel, the trace space `H^{1/2}(Γ)` defined as its orthogonal complement, with trace and extension operators, `H^1(Ω) ⧸ ker γ ≅ H^{1/2}(Γ)`, and `H^{-1/2}(Γ)` | ✅ | ✗ | `Domains/Traces/BoundaryTraceSpace` |
| The area formula for Lipschitz graphs: Lipschitz maps and Mathlib's Euclidean Hausdorff measure, the linear case by Mathlib's norm determinant, stretches and tilts, the gradient and the Gram density, good pieces, `μHE[n-1](γ(A)) = ∫_A √(1 + ‖∇φ‖²)` with `n = dim V` in set, measure and integral form; the outward unit normal | ✅ | ✗ | `Domains/Lipschitz/LipschitzGraphArea` |
| The surface measure of a bounded Lipschitz domain as `μHE[n-1]` on the boundary, its chart form, finiteness and null sets, the boundary `Γ` as a Lebesgue null set, the boundary trace in `L_p(Γ)`, `L_2(Γ)` with the traces of `H^1(Ω)` and `H^{1/2}(Γ)`, and the outward unit normal field | ✅ | ✗ | `Domains/Lipschitz/SurfaceMeasure` |
| Smoothness of parametric integrals, the dilation identity `m_2 - m = ∑_i ∂_{e_i} K_i` with the divergence kernels `K_i(x) = ⟪e_i, x⟫ ∫_1^2 t⁻¹ m_t(x) dt`, their supports and mean zero, and the Calderón–Zygmund families of the dilates of mean-zero Schwartz functions | ✅ | ✗ | `Domains/Extension/DivergenceKernels` |
| The local means of order two by the gradient, local means of Triebel–Lizorkin type on a set, bounded extensions from one patch, pasting in `W^1_p(ℝ^d)`, the extension theorem (`W^1_p(Ω)` is the space of restrictions of `W^1_p(ℝ^d)`) for `1 < p < ∞` with a bound, and for `p = 2` `H^1(Ω) = W^1_2(Ω)`, Rellich's theorem in `W^1_2(Ω)`, the quotient norm of `H^1(Ω)` and the boundary traces of `W^1_2(Ω)` | ✅ | ✗ | `Domains/Extension/SobolevExtension` |
| The extension operator for `W^1_p`, `1 < p < ∞`, on value–derivative jets, `E u = u` on `Ω` | ✅ | ✗ | `Domains/Extension/SobolevExtensionOperator` |
| Gauss–Green on Lipschitz graph domains: product coordinates and Fubini, ray integrals, integrals of line derivatives of Lipschitz functions, the normal weight, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` for compactly supported `C^1` functions in chart and surface form, the product rule for line derivatives, and Green's formula `∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)` | ✅ | ✗ | `Domains/Sobolev/LipschitzGraphGreen` |
| Green's formula on bounded Lipschitz domains: integration by parts in `H^1(ℝ^d)`, resolutions of unity equal to one near the boundary, the chart form for every resolution of unity, the outward unit normal as the chart normal and a unit vector almost everywhere on the boundary, `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` for `u, w ∈ H^1(Ω)`, the traces from both sides of a graph, and the zero extension: `1_Ω u ∈ W^1_2(ℝ^d)` iff the trace of `u` vanishes | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainGreen` |
| The kernel of the trace: convergence and mollification in `H^1(ℝ^d)`, smoothing with compact support, bump mollifiers and cone mollifiers, `H̃^1(Ω)` as the functions of `H^1(ℝ^d)` vanishing outside `Ω`, `ker γ = H^1_0(Ω)`, `H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)`, `H̃^1(Ω) ≅ ker γ` and `(ker γ)^* ≅ H^{-1}(Ω)` | ✅ | ✗ | `Domains/Traces/TraceKernel` |
| Bounded Lipschitz domains from the set-level definition: sets Lipschitz near a point, local graphs as Lipschitz graph domains, McShane's extension of local graphs, the structure from a family of charts and the converse, the ball | ✅ | ✗ | `Domains/Lipschitz/LocalLipschitzGraphs` |
| Bounded open convex sets as bounded Lipschitz domains: the ray length, its cone estimate, open convex sets, bounded or not, near a frontier point as regions above a Lipschitz graph, and the open unit cube with its closure | ✅ | ✗ | `Domains/Lipschitz/ConvexDomains` |
| The extension property and null sets, Lipschitz graph domains with null graphs and boundaries, closures of convex Lipschitz graph domains as Besov domains, the quadrant as a Lipschitz graph domain and the quadrant model of manifolds with corners as a Besov domain, bounded Lipschitz domains with the extension property, closures of nonempty convex bounded Lipschitz domains and of nonempty bounded open convex sets, closed balls of positive radius and the closed unit cube as Besov domains | ✅ | ✗ | `Domains/Lipschitz/BesovDomains` |
| Smooth bounded domains from the set-level definition: sets smooth near a point, the smooth cut-off of a local graph, the smooth domain from smooth charts and the converse, the ball as a smooth domain and the Besov spaces of its closure | ✅ | ✗ | `Domains/Manifolds/SmoothLocalGraphs` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
