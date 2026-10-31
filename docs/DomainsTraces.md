# Domains, traces and manifolds

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Domains,
traces and manifolds*, chapters *Lipschitz domains*, *Traces on Lipschitz domains*, *Sobolev
spaces on domains*, *Eigenbases of the Laplacian* and *Besov spaces on compact manifolds*.

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
`H^{-1/2}(Γ)` is its dual; its norm is the least `H^1` norm of an extension and is equivalent to
the norm of `B^{1/2}_{2,2}(Γ)` by chart pieces. On a Lipschitz graph
domain the area formula expresses Mathlib's Euclidean Hausdorff measure of the boundary in the
chart, with the Gram density `√(1 + ‖∇φ‖²)`. On a bounded Lipschitz domain the surface measure is
this Hausdorff measure on the boundary `Γ`; it gives the space `L_2(Γ)`, into which `H^1(Ω)` and
`H^{1/2}(Γ)` have bounded trace operators. The outward unit normal field is pasted from the chart
normals. On a bounded Lipschitz domain, every function of `W^1_p(Ω)`, `1 < p < ∞`, is the
restriction of a function of `W^1_p(ℝ^d)` under a bounded linear extension operator, built from
Rychkov's local extension with the local means of the gradient: the local means kernels of order two
are divergences of dilated kernels with mean zero, which form Calderón–Zygmund families. For `p = 2`
this identifies `H^1(Ω)` with `W^1_2(Ω)`. For every `1 ≤ p ≤ ∞` every function of `W^1_p(Ω)` is
the restriction of a function of `W^1_p(ℝ^d)` under a bounded linear extension operator, by
reflection across the boundary in the flattened coordinates of the graph domains. For
`1 < p < ∞` and every order `m` every function of `W^m_p(Ω)` is the restriction of a function of
`W^m_p(ℝ^d)` with a bound, by Rychkov's local extension with the local means of the derivatives
of order `m`, pasted with the Leibniz rule. On a Lipschitz graph domain, the Gauss–Green theorem
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
`(ker γ)^* ≅ H^{-1}(Ω)`. On a bounded open set the embedding `H^1_0(Ω) → L_2(Ω)` is compact with
dense range, and its singular basis gives the eigenbasis of the Dirichlet Laplacian as a spectral
scheme, with the weak eigenvalue equation; `H^1_0(Ω)` is the Sobolev space of order `1` of this
scheme, and the real interpolation spaces between `L_2(Ω)` and `H^1_0(Ω)` are its approximation
spaces. On a bounded Lipschitz domain the same holds for `W^1_2(Ω)`, the graph of the weak
gradient in `L_2(Ω) × L_2(Ω)^n`: Rellich's theorem through the extension theorem makes
`W^1_2(Ω) → L_2(Ω)` compact, and its singular basis is the eigenbasis of the Neumann Laplacian,
with the eigenvalue `0` of the constants. There the Besov space
`B^θ_{2,q}(Ω)`, `0 < θ < 1`, defined by intrinsic differences, is the approximation space of the
Neumann eigenbasis; on a bounded open set the zero extension maps the approximation spaces of the
Dirichlet eigenbasis into `B^θ_{2,q}(ℝ^d)`. On a compact manifold, with or without boundary, the
chart Sobolev space `H^1_A(M) = B^1_{2,2}(M)` embeds compactly and densely into `L_2(μ)`, and the
eigenvector basis `e_i = J φ_i` of the embedding is an eigenbasis of the chart form whose
approximation spaces are `B^θ_{2,q}(M)`, `0 < θ < 1`. The
[interface document](FEECInterface.md) lists the results for `p = 2` for a FEEC/BEEC library built
on this project, with the decisions behind their form.

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
  extension `E g` of moment order `1` (`Rd.LipschitzGraph.graphExtension`) extends the atoms of
  `g` by
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
  (`Rd.LipschitzGraph.graphExtension` of the flat graph, whose extended atoms are smooth of every
  order) is bounded
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
* **Functions vanishing outside a ball on a Besov domain.** Let `Ω` be a Besov domain with interior
  `O`, which agrees with `Ω` up to a null set (`Rd.BesovDomain.interior_ae_eq`), and let `g` vanish
  almost everywhere outside `B(0, R)`. For `1 ≤ p < ∞`, `0 < s < r`, `1 ≤ q ≤ ∞` and `R < R'`,
  `N_Ω(g) < ∞` iff `N_D(g) < ∞` on the bounded convex Lipschitz domain `D = O ∩ B(0, R')`
  (`Rd.BesovDomain.ballDomain`, `Rd.BesovDomain.modNormOn_lt_top_iff_ballDomain`), through the
  extension from `D` and a smooth cutoff, a Besov multiplier (`Rd.exists_mul_modNorm_le`). Hence
  `g ∈ L_2(V)` has weak derivatives `∂_{e_j} g ∈ L_2(O)` on `O` iff
  `‖g‖_{L_2(Ω)} + ‖(2^k ω_r(g, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞` for every order `r ≥ 2`
  (`Rd.BesovDomain.exists_hasWeakLineDeriv_iff_modNormOn_lt_top`).
* **Besov spaces on compact manifolds.** Let `M` be a compact smooth manifold modelled on `E` with
  corners `I` whose range is a Besov domain (the half-space, the quadrant of manifolds with
  corners, or `E`), `μ` a smooth measure (in every chart a continuous positive density with
  respect to the Lebesgue measure, `Manifold.IsSmoothMeasure`) and `1 ≤ p < ∞`. A Besov atlas
  consists of finitely many charts `κ_i`, a smooth partition of unity `ψ_i` subordinate to them and
  cut-offs (`Manifold.BesovAtlas`); every compact manifold has one
  (`Manifold.BesovAtlas.nonempty`). Its chart measure
  `μ_A = ∑_i (κ_i⁻¹)_* (ψ_i ∘ κ_i⁻¹ · vol|_{T_i})`, with `T_i = κ_i(e_i.source)` the target of
  the extended chart (`Manifold.BesovAtlas.chartMeasure`), has the density
  `∑_i |det DΦ_i| ψ_i ∘ κ⁻¹` in every chart `κ`, `Φ_i = κ_i ∘ κ⁻¹`, so it is a finite smooth
  measure (`Manifold.BesovAtlas.isSmoothMeasure_chartMeasure`), and every compact manifold, with or
  without boundary, carries one (`Manifold.exists_isSmoothMeasure`), for example the sphere
  (`Manifold.exists_isSmoothMeasure_sphere`). The Besov quasi-norm of a Besov atlas `A` is
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
  (`Rd.LipschitzGraph.measurePreserving_flatten_of_lipschitz`), so the Lebesgue measure is a
  smooth measure (`Rd.SmoothDomain.isSmoothMeasure_volumeOn`). For `1 ≤ p < ∞`, `0 < s < r` and
  `1 ≤ q ≤ ∞`, `f ∈ L_p(closure Ω)` lies in the Besov space `B^s_{p,q}` of this manifold iff
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
* **Besov quasi-norms on the boundary.** With `Ω`, `Γ` and `ψ` as above, the quasi-norm
  `‖g‖_{B^s_{p,q}(Γ)}` is the sum over the charts of
  `‖G_j‖_{L_p(H_j)} + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q}` for the chart pieces
  `G_j = (ψ_j g) ∘ γ_j` (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`,
  `Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_sum`; Schneider–Vybíral, Definition 3.3). It is
  finite exactly on `B^s_{p,q}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundaryBesovNorm_lt_top`), sees `g` only almost
  everywhere on `Γ`, and is subadditive and homogeneous
  (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_add_le`,
  `Rd.BoundedLipschitzDomain.boundaryBesovNorm_const_smul`). For `1 ≤ p < ∞`, `0 < s < 1` and
  `1 ≤ q ≤ ∞` there are `C < ∞` with
  `‖Tr_Γ F‖_{B^s_{p,q}(Γ)} ≤ C (‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q})` for
  `s + 1/p < L` (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`); for
  `L ≥ 2` every `g ∈ B^s_{p,q}(Γ)` is `Tr_Γ F` almost everywhere on `Γ` for some `F` with
  `‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C ‖g‖_{B^s_{p,q}(Γ)}`
  (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le`). Two resolutions of
  unity give equivalent quasi-norms
  (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_le_of_partition`).
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
  for bounded Lipschitz domains hold with bounds
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_le`,
  `Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`,
  `Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le`), and the restriction direction has
  constant `1` (`Rd.BoundedLipschitzDomain.modNormOn_le_modNorm_of_ae_eq`).
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
  constant (`Rd.modNorm_two_le_norm`, `Rd.sobolevOneBesovConst`). Conversely
  `‖U‖ ≤ C' (‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2})` with an explicit constant
  (`Rd.enorm_le_modNorm_two`, `Rd.sobolevOneInvConst`). The `B^{1/2}_{2,1}` quantity
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
  `Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`), with equivalent norms (*The
  norm of the trace space* below). `H^{-1/2}(Γ)` is the
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
* **The norm of the trace space.** Let `Ω` be a bounded Lipschitz domain with boundary `Γ`,
  `H^{1/2}(Γ)` its trace space and `τ : H^{1/2}(Γ) → L_2(Γ)` the trace. For every resolution of
  unity `ψ` and `t ∈ H^{1/2}(Γ)`, `‖t‖` is the least norm `‖U‖` of a `U ∈ H^1(V)` with the
  boundary trace of `t` (`Rd.BoundedLipschitzDomain.enorm_eq_iInf`), the quotient norm of
  `γ(H^1(Ω))`, which McLean, Theorem 3.37, shows to be equivalent to his chart norm, and
  there is `C < ∞` with `‖t‖ ≤ C ‖τ t‖_{B^{1/2}_{2,2}(Γ)}` and `‖τ t‖_{B^{1/2}_{2,2}(Γ)} ≤ C ‖t‖`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`). Every `g ∈ B^{1/2}_{2,2}(Γ)` is the
  boundary trace of some `E t` with `‖t‖ ≤ C ‖g‖_{B^{1/2}_{2,2}(Γ)}`
  (`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov_le`), and the range of `τ` is
  `B^{1/2}_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`). With the canonical
  resolution of unity, the functions of `L_2(Γ)` in `B^{1/2}_{2,2}(Γ)` form a Banach space with
  the norm by chart pieces (`Rd.BoundedLipschitzDomain.BoundaryBesovHalf`), and `τ` is an
  isomorphism of `H^{1/2}(Γ)` onto it
  (`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesovHalf`). The trace has the bounded linear
  right inverse `E τ⁻¹ : B^{1/2}_{2,2}(Γ) → H^1(Ω)`, as in McLean, Theorem 3.37
  (`Rd.BoundedLipschitzDomain.traceRightInverse`,
  `Rd.BoundedLipschitzDomain.boundaryTraceL2_traceRightInverse`).
* **The Sobolev–Slobodeckij norm on the boundary.** Let `Ω` be a bounded Lipschitz domain in `V`,
  `dim V = n`, with boundary `Γ` and surface measure `σ`, let `ψ` be a resolution of unity,
  `1 ≤ p < ∞` and `0 < s < 1`. For `g ∈ L_p(Γ)`, `g ∈ B^s_{p,p}(Γ)` iff Gagliardo's form
  `E(g) = ∫_Γ ∫_Γ |g(y) - g(x)|^p / |y - x|^(n-1+sp) dσ(y) dσ(x)` is finite
  (`Rd.BoundedLipschitzDomain.boundarySlobodeckijForm`,
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundarySlobodeckijForm_lt_top`); there is
  `C < ∞` with `E(g) ≤ C ‖g‖_{B^s_{p,p}(Γ)}^p` for all `g` (for every `s > 0`) and
  `‖g‖_{B^s_{p,p}(Γ)}^p ≤ C (‖g‖_{L_p(Γ)}^p + E(g))` for all `g` measurable on `Γ`
  (`Rd.BoundedLipschitzDomain.exists_boundarySlobodeckijForm_le`,
  `Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`). For `p = 2`, `s = 1/2` there is
  `C < ∞` with `‖t‖² ≤ C (‖τ t‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |τ t(y) - τ t(x)|² / |y - x|^n dσ dσ)` and the
  reverse bound for all `t ∈ H^{1/2}(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`), and `g ∈ L_2(Γ)` lies in
  the range of `τ` iff its form is finite
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff_slobodeckij`).
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
  (`Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton`). The membership statements are the
  cases `1 < p < ∞` of the theorem by reflection below
  (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_of_one_le`); the bound with
  the constant `C`, and with it Rellich's theorem and the quotient norm, is Rychkov's local
  extension with the local means of the gradient: for a bump with the moment kernel `m` of order
  two, `k_{j+1} = 2^{-j} ∑_i ∂_{e_i} (K_i)_{2^j}`
  (`Rd.LocalMeansBump.kernel_two_succ_apply`), so on a patch
  `k_{j+1} ⋆ 1_T f = 2^{-j} ∑_i (K_i)_{2^j} ⋆ 1_T g_i`
  (`Rd.LocalMeansBump.conv_kernel_two_succ_eq`),
  the strong type of the Calderón–Zygmund families `((K_i)_{2^j})_j` bounds the local means of
  Triebel–Lizorkin type of `f` on the patch (`Rd.LocalMeansBump.tlLocalNormOn_le_patchConst`), the
  local extension lies in `F^1_{p,2} = W^1_p` and is linear in `f`
  (`Rd.LocalMeansBump.sobolevExtensionOp`, `Rd.LocalMeansBump.extendsSobolev`), and a smooth
  resolution of unity pastes the local extensions in `W^1_p(V)` (`Rd.sobolevExtensionOp_of_cover`).
  The constants are existential. The extension is a linear extension operator on value–derivative
  jets with a finite constant (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp`), so a
  bounded linear right inverse of the restriction; it is of first order.
* **The extension theorem for `1 ≤ p ≤ ∞` by reflection.** For a bounded Lipschitz domain `Ω` in
  `V` of dimension `n ≥ 1` and every `1 ≤ p ≤ ∞` there is a finite `C` such that every
  `f ∈ L_p(Ω)` with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` on `Ω` agrees almost everywhere on
  `Ω` with some `F ∈ W^1_p(V)` whose weak derivatives `G_i = ∂_{e_i} F` satisfy
  `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev_of_one_le`); hence `f ∈ W^1_p(Ω)` iff `f`
  agrees on `Ω` with some `F ∈ W^1_p(V)`, in every dimension
  (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_of_one_le`). On a Lipschitz
  graph domain `Ω = {x : φ(x) < ⟪x, e⟫}` with `M`-Lipschitz `φ`, the flattening
  `F(x) = x - φ(x) e` and its inverse are `(1 + M)`-Lipschitz and preserve Lebesgue measure
  (`Rd.LipschitzGraph.measurePreserving_flatten_of_lipschitz`,
  `Rd.LipschitzGraph.measurePreserving_unflatten`), and the even reflection of `f ∘ F⁻¹` across
  `e^⊥`, composed with `F` (`Rd.LipschitzGraph.reflectionExtension`), is `f` on `Ω`, is weakly
  differentiable on `V` (`Rd.LipschitzGraph.hasWeakLineDeriv_reflectionExtension`) and satisfies
  `‖E f‖_p ≤ 2 ‖f‖_{L_p(Ω)}` and `‖∂_v E f‖_p ≤ 2 (1 + M)² ‖v‖ ∑_i ‖g_i‖_{L_p(Ω)}`
  (`Rd.LipschitzGraph.eLpNorm_reflectionExtension_le`,
  `Rd.LipschitzGraph.eLpNorm_reflectionDeriv_le`). On the half-space the even reflection is
  weakly differentiable by integration by parts with cutoffs near the hyperplane
  (`Rd.hasWeakLineDeriv_evenReflection`). The boundary patches of `Ω` extend by a cutoff and the
  reflection, the inner patch by a cutoff, and `Rd.sobolevExtensionOp_of_cover` pastes them. The
  extension is a bounded linear operator `E : W^1_p(Ω) → W^1_p(V)` on value–derivative jets with
  `E u = u` on `Ω` (`Rd.BoundedLipschitzDomain.sobolevExtensionL`,
  `Rd.BoundedLipschitzDomain.exists_extensionL`), since every patch extension is linear and sees
  only the values on `Ω` (`Rd.IsSobolevExtensionMap`); it is the chosen extension operator for
  every `1 ≤ p ≤ ∞`.
* **The extension theorem of higher order.** For a bounded Lipschitz domain `Ω` in `V` of
  dimension `n ≥ 1`, `1 < p < ∞` and `m ∈ ℕ` there is a finite `C` such that every `f` with weak
  derivatives `g_{k,w} = ∂^{e_w} f ∈ L_p(Ω)` on `Ω` along all words `w` of length `k ≤ m` agrees
  almost everywhere on `Ω` with some `F ∈ W^m_p(V)` whose weak derivatives `G_{k,w} = ∂^{e_w} F`
  satisfy `∑_{k ≤ m} ∑_w ‖G_{k,w}‖_p ≤ C ∑_{k ≤ m} ∑_w ‖g_{k,w}‖_{L_p(Ω)}`
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder`); hence `f ∈ W^m_p(Ω)` iff `f` agrees
  on `Ω` with some `F ∈ W^m_p(V)`, in every dimension
  (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_order`). For the smoothed bump
  `b'` of a bump `b` and `m ≤ L`, the local means kernels of order `L` are
  `k_{j+1} = 2^{-jm} ∑_i ∂^{e_i} (K_i)_{2^j}` with the higher divergence kernels `K_i` of `b`, so
  on a patch `k_{j+1} ⋆ 1_T f = 2^{-jm} ∑_i (K_i)_{2^j} ⋆ 1_T ∂^{e_i} f`
  (`Rd.LocalMeansBump.conv_kernel_succ_eq_sum_higherKernel`); for `L = m + 1` the strong type of
  the Calderón–Zygmund families `((K_i)_{2^j})_j` bounds the local means of Triebel–Lizorkin type
  with smoothness `m` (`Rd.LocalMeansBump.tlLocalNormOn_le_higherPatchConst`), the local extension
  lies in `F^m_{p,2} ⊆ W^m_p` (`Rd.LocalMeansBump.extendsSobolevOrder`), and a smooth resolution of
  unity pastes the local extensions by the Leibniz rule (`Rd.extendsSobolevOrder_of_cover`). The
  inner patch extends by a cutoff for every `1 ≤ p ≤ ∞`
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder_interior`). The constants are
  existential.
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
* **The Dirichlet eigenbasis.** Let `Ω ⊆ V` be a bounded open set and
  `J : H^1_0(Ω) → L_2(Ω)` the restriction (`Rd.dirichletEmbedding`). Then `J` is a compact
  dense embedding (`Rd.dirichletCompactEmbedding`), and its spectral scheme
  (`Rd.dirichletScheme`) is a Hilbert basis `(e_i)` of `L_2(Ω)` with eigenvalues
  `λ_i = 4π²(σ_i⁻² - 1) ≥ 0` (`Rd.dirichletEigenvalue`, `Rd.dirichletEigenvalue_nonneg`), `σ_i`
  the singular values of `J`, and levels `⌊√(1 + λ_i/(4π²))⌋` (`Rd.dirichletScheme_level`). The
  eigenfunctions `φ_i ∈ H^1_0(Ω)` with `J φ_i = e_i` (`Rd.dirichletEigenfunction`,
  `Rd.dirichletEmbedding_dirichletEigenfunction`) satisfy, for every orthonormal basis `(b_k)`
  of `V` and every `w ∈ H^1_0(Ω)`, `∑_k ⟨∂_{b_k} φ_i, ∂_{b_k} w⟩_2 = λ_i ⟨φ_i, w⟩_2`
  (`Rd.dirichletEigenfunction_weak`), the weak form of `-Δ φ_i = λ_i φ_i`, `φ_i = 0` on `∂Ω`
  (Brezis, Theorem 9.31). `f ∈ L_2(Ω)` lies in `J(H^1_0(Ω))` iff
  `∑_i (1 + ⌊σ_i⁻¹⌋)² |⟨e_i, f⟩|² < ∞` (`Rd.exists_dirichletEmbedding_eq_iff`), and for
  `0 < θ < 1`, `1 ≤ q ≤ ∞`, `(L_2(Ω), H^1_0(Ω))_{θ,q}` is the approximation space `A^θ_q` of the
  Dirichlet scheme (`Rd.memKMethod_dirichlet_iff`), described by dyadic blocks of coefficients
  (`Rd.memKMethod_dirichlet_iff_blockNorm_lt_top`).
* **The Neumann eigenbasis.** Let `Ω ⊆ V` be a bounded Lipschitz domain in dimension `n ≥ 1`
  and `N(Ω)` the pairs `(f, g)` in `L_2(Ω) × L_2(Ω)^n` with `g_k = ∂_{b_k} f` weakly on `Ω` for
  the basis `b_k = Rd.gridBasis V k`, with the inner product `⟨f, f'⟩_2 + ∑_k ⟨g_k, g'_k⟩_2`
  (`Rd.neumannSpace`). The embedding `(f, g) ↦ f` into `L_2(Ω)` (`Rd.neumannEmbedding`) is compact
  (`Rd.BoundedLipschitzDomain.isCompactOperator_neumannEmbedding`), injective and has dense range,
  and its spectral scheme (`Rd.BoundedLipschitzDomain.neumannScheme`) is a Hilbert basis `(e_i)`
  of `L_2(Ω)` with eigenvalues `λ_i = σ_i⁻² - 1 ≥ 0` (`Rd.BoundedLipschitzDomain.neumannEigenvalue`,
  `Rd.BoundedLipschitzDomain.neumannEigenvalue_nonneg`) and levels `⌊√(1 + λ_i)⌋`
  (`Rd.BoundedLipschitzDomain.neumannScheme_level`). The eigenfunctions `φ_i ∈ N(Ω)` with value
  `e_i` satisfy `∑_k ⟨∂_{b_k} φ_i, g_k⟩_{L_2(Ω)} = λ_i ⟨φ_i, f⟩_{L_2(Ω)}` for every `(f, g)` in
  `N(Ω)` (`Rd.BoundedLipschitzDomain.neumannEigenfunction_weak`), the weak form of
  `-Δ φ_i = λ_i φ_i`, `∂_ν φ_i = 0` on `∂Ω`; for nonempty `Ω` some `λ_i` is `0`
  (`Rd.BoundedLipschitzDomain.exists_neumannEigenvalue_eq_zero`). Every `(f, g)` in `N(Ω)` has
  `f = u|_Ω` for some `u ∈ H^1(Ω)` with `‖u‖ ≤ C ‖(f, g)‖`
  (`Rd.BoundedLipschitzDomain.exists_restrictionSpace_of_neumannSpace`). `f ∈ L_2(Ω)` lies in
  `W^1_2(Ω)` iff `∑_i (1 + ⌊σ_i⁻¹⌋)² |⟨e_i, f⟩|² < ∞`
  (`Rd.BoundedLipschitzDomain.exists_neumannEmbedding_eq_iff`), and for `0 < θ < 1`,
  `1 ≤ q ≤ ∞`, `(L_2(Ω), W^1_2(Ω))_{θ,q}` is the approximation space `A^θ_q` of the Neumann
  scheme (`Rd.BoundedLipschitzDomain.memKMethod_neumann_iff`), described by dyadic blocks of
  coefficients (`Rd.BoundedLipschitzDomain.memKMethod_neumann_iff_blockNorm_lt_top`).
* **Besov spaces on domains by eigenfunction expansions.** Let `Ω` be a bounded Lipschitz domain
  in dimension `n ≥ 1`, `0 < θ < 1`, `1 ≤ q ≤ ∞` and `r ≥ 1` an integer. For every `f ∈ L_2(V)`,
  `f|_Ω` lies in the approximation space `A^θ_q` of the Neumann eigenbasis iff
  `‖f‖_{L_2(Ω)} + ‖(2^(kθ) ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_q} < ∞`, that is iff
  `f|_Ω ∈ B^θ_{2,q}(Ω)` (`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_iff`); equivalently
  the dyadic blocks of the Neumann coefficients of `f|_Ω` have finite `B^θ_{2,q}` norm
  (`Rd.BoundedLipschitzDomain.modNormOn_lt_top_iff_blockNorm_lt_top`), and for `q = 2` iff
  `∑_i (1 + λ_i)^θ |⟨e_i, f|_Ω⟩|² < ∞` (`Rd.BoundedLipschitzDomain.modNormOn_two_lt_top_iff`).
  On every bounded open set `Ω` in dimension `n ≥ 1`, the zero extension of every `g` in the
  approximation space `A^θ_q` of the Dirichlet eigenbasis lies in `B^θ_{2,q}(V)`
  (`Rd.memApprox_bandScheme_extendByZero_of_memApprox_dirichletScheme`).
  The proof bounds the modulus on `Ω` by the K-functional of `(L_2(Ω), W^1_2(Ω))`
  (`Rd.BoundedLipschitzDomain.exists_lpModulusOn_le_kFunctional`), with
  `ω_r(ι U, 2^(-k))_2 ≤ 2^(r-1) 2π 2^(-k) ‖U‖` for `U ∈ H^1(V)` (`Rd.lpModulus_toL2_le`), and
  restricts `(L_2(V), H^1(V))_{θ,q} = B^θ_{2,q}(V)` to `Ω`
  (`Rd.memKMethod_neumann_restrict_of_memKMethod`).
* **Eigenfunction expansions on compact manifolds.** Let `M` be a compact manifold whose model
  range `Ω_I` is a Besov domain, of dimension `n ≥ 1`, with a smooth measure `μ`, a Besov atlas
  `A` with pieces `P_k` and lifts `L_k`, and `J : H^1_A(M) → L_2(μ)` the chart Sobolev embedding.
  `J = ∑_k L_k E_k J^N_k T_k` through the Neumann embeddings `J^N_k` of the bounded convex pieces
  `D_k = O_I ∩ B(0, R_k + 1)` (`Manifold.BesovAtlas.chartSobolevEmbedding_eq_sum`), so `J` is
  compact (`Manifold.BesovAtlas.isCompactOperator_chartSobolevEmbedding`); its range is dense
  (`Manifold.BesovAtlas.denseRange_chartSobolevEmbedding`). Its spectral scheme
  (`Manifold.BesovAtlas.chartScheme`) is a Hilbert basis `(e_i)` of `L_2(μ)` with eigenvalues
  `λ_i = σ_i⁻² - 1 ≥ 0` (`Manifold.BesovAtlas.chartEigenvalue_nonneg`), finitely many below each
  bound, and eigenfunctions `φ_i ∈ H^1_A(M)`, `J φ_i = e_i`, with
  `a_A(φ_i, w) = λ_i ⟨e_i, J w⟩` for every `w ∈ H^1_A(M)`
  (`Manifold.BesovAtlas.chartForm_eigenfunction`), the weak eigenvalue equation of the chart form
  with the natural boundary condition. `f ∈ B^1_{2,2}(M)` iff
  `∑_i (1 + ⌊√(1 + λ_i)⌋)² |⟨e_i, f⟩|² < ∞` (`Manifold.BesovAtlas.memBesov_one_two_iff_spectral`).
  For `0 < θ < 1` and `1 ≤ q ≤ ∞`, `f ∈ (L_2(μ), H^1_A(M))_{θ,q}` iff every piece `P_k f` has a
  finite intrinsic quasi-norm on `Ω_I` (`Manifold.BesovAtlas.memKMethod_chartSobolev_iff`), so
  `f ∈ B^θ_{2,q}(M)` iff `f` lies in the approximation space `A^θ_q` of the chart eigenbasis
  (`Manifold.BesovAtlas.memApprox_chartScheme_iff`), iff
  `‖P_1 f‖_2 + ‖(2^(kθ) ‖Δ_k f‖_2)_k‖_{ℓ_q} < ∞` for the dyadic blocks `Δ_k f` of its
  eigenfunction expansion (`Manifold.BesovAtlas.memBesov_iff_blockNorm_lt_top`), and for `q = 2`
  iff `∑_i (1 + λ_i)^θ |⟨e_i, f⟩|² < ∞` (`Manifold.BesovAtlas.memBesov_two_iff_chartEigenvalue`).
  On the closure of a bounded smooth domain `Ω` these are the intrinsic `B^θ_{2,q}(Ω)`
  (`Rd.SmoothDomain.memApprox_chartScheme_iff_modNormOn`); the sphere `S^n`, `n ≥ 1`, with the
  chart measure of a Besov atlas is an example without boundary
  (`Manifold.memApprox_chartScheme_sphere_iff`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Lipschitz graph domains: cone and closed cone, the closure of the domain, the closure plus the cone, cone bump, kernels supported in the reflected cone, support principle for two sets and for the domain | ✅ | ✗ | `Domains/Lipschitz/LipschitzGraph` |
| The local extension of a bump on a set: absolute convergence from bounds of the weighted local means, the Besov bound, agreement on the set it sees; Rychkov's extension as its case `W = Ω`, restrictions to Lipschitz graph domains by intrinsic local means | ✅ | ✗ | `Domains/Extension/RychkovExtension` |
| Restrictions to Lipschitz graph domains by intrinsic differences, weighted `ℓ_q` norms from the first term and a bound of the others | ✅ | ✗ | `Domains/Extension/LipschitzGraphBesov` |
| Local versions of Rychkov's extension: boundary and inner patches, cone bumps of small radius, short steps into the closed cone, local means on a set bounded by the moduli on a larger set, the local extension with a bound | ✅ | ✗ | `Domains/Extension/LocalExtension` |
| Bounded Lipschitz domains: the patches covering the closure, pasting over the patches, pasting of local extensions, subadditivity and homogeneity of the quasi-norms by differences, the extension with a bound | ✅ | ✗ | `Domains/Lipschitz/BoundedLipschitz` |
| Null hyperplanes, Lipschitz graph domains with the extension property, the half-space, the first axis `e₀` of `ℝ^n`, and the models of manifolds as Besov domains | ✅ | ✗ | `Domains/Lipschitz/HalfSpace` |
| Traces of every order on the half-space: trace theorem, extension, trace space | ✅ | ✗ | `Domains/Traces/HalfSpaceTrace` |
| Graph map of a Lipschitz graph domain, the boundary as the graph, restrictions of atoms to the graph | ✅ | ✗ | `Domains/Lipschitz/GraphParametrization` |
| Traces on Lipschitz graph domains: boundedness, linearity, trace of continuous functions | ✅ | ✗ | `Domains/Traces/GraphTrace` |
| Mollified graph and vertical cut-off with bounds of their differences | ✅ | ✗ | `Domains/Traces/MollifiedGraph` |
| Extension from the boundary of a Lipschitz graph domain, its trace space | ✅ | ✗ | `Domains/Traces/GraphTraceExtension` |
| Traces in charts: locality, approximation, change of chart, products and their bound, finite sums | ✅ | ✗ | `Domains/Traces/GraphTraceCharts` |
| Traces on bounded Lipschitz domains: Besov spaces on the boundary, the trace space | ✅ | ✗ | `Domains/Traces/LipschitzBoundaryTrace` |
| Besov quasi-norms on the boundary: chart pieces, bounded trace and extension for `1 ≤ p < ∞`, independence of the resolution of unity | ✅ | ✗ | `Domains/Traces/BoundaryBesovNorm` |
| Smooth measures on manifolds, measurability of extended charts on their sources, integrals and `L_p` norms in charts, null sets in charts | ✅ | ✗ | `Domains/Manifolds/SmoothMeasure` |
| Besov atlases, chart pieces, images and measurable sources of changes of charts, changes of charts with cut-offs, lifts from a chart and their `L_p` bound | ✅ | ✗ | `Domains/Manifolds/BesovAtlas` |
| Smooth measures exist: the chart measure of a Besov atlas, its density in every chart by the Jacobian determinants of the changes of charts, continuity and positivity of the density, finiteness, every compact manifold with or without boundary carries a finite smooth measure, the sphere as an example without boundary | ✅ | ✗ | `Domains/Manifolds/SmoothMeasureExistence` |
| Besov spaces on compact manifolds, independence of the atlas and of the order, membership piece by piece, lifts from a chart | ✅ | ✗ | `Domains/Manifolds/Besov` |
| Flattening of graph domains, the Lipschitz bounds of the flattening and its inverse, the graph in the image of the hyperplane, product and graph coordinates, preservation of the Lebesgue measure for every Lipschitz graph | ✅ | ✗ | `Domains/Lipschitz/GraphStraightening` |
| Smooth bounded domains as compact manifolds with boundary, Lebesgue measure as smooth measure | ✅ | ✗ | `Domains/Manifolds/SmoothDomain` |
| Besov spaces of smooth domains by charts equal the intrinsic Besov spaces | ✅ | ✗ | `Domains/Manifolds/SmoothDomainBesov` |
| Besov spaces on the boundary of a compact manifold, independence of the atlas | ✅ | ✗ | `Domains/Manifolds/BoundaryBesov` |
| Trace theorem on compact manifolds: commutation with charts, boundedness, trace space | ✅ | ✗ | `Domains/Manifolds/BoundaryTrace` |
| The chart Sobolev space of a compact manifold with or without boundary: the open model set, pieces and lifts as bounded operators, the retract identity `∑_k L_k P_k = id`, the graph space of the weak gradients of the pieces on the open model set, the chart form, the embedding into `L_2(μ)`, and `H^1_A(M) = B^1_{2,2}(M)` for every Besov atlas | ✅ | ✗ | `Domains/Manifolds/ChartSobolev` |
| `H^1` on bounded Lipschitz domains defined as restrictions of `H^1(ℝ^d)`, by intrinsic differences, the identification with the restriction space, the weak gradient, and the boundary traces, which form `B^{1/2}_{2,2}(Γ)` | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainH1` |
| The Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` on open sets inside Mathlib's `H^s(ℝ^d)`, `H^s(Ω)` as a quotient, Rellich's theorem for `H^1(Ω)`, the restriction of an element agreeing with `u ∈ H^1(Ω)` on `Ω`, the bound of the `H^1` norm by the `W^1_2` norm, the weak derivatives as bounded operators on `H^1(ℝ^d)`, the density of compactly supported Schwartz functions in `H^s(ℝ^d)`, Schwartz functions with compact support in `Ω` in the span of the test functions, `H̃^s(ℝ^d) = H^s(ℝ^d)`, the isometry `H̃^1(Ω) ≅ H^1_0(Ω)`, and the vanishing of `H̃^1(Ω)` outside `Ω` | ✅ | ✗ | `Domains/Sobolev/SobolevRestrictionSpaces` |
| The Bessel potential of real Schwartz functions as a real function, the isometry `J_{2s} : H^s(ℝ^d) → H^{-s}(ℝ^d)`, the pairing of `H^{-s}` and `H^s`, and the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`, `(H^s(Ω))^* ≅ H̃^{-s}(Ω)`, `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` on open sets | ✅ | ✗ | `Domains/Sobolev/SobolevDuality` |
| `H^1(ℝ^d) ⊆ B^{1/2}_{2,1}(ℝ^d)` and its converse `B^1_{2,2}(ℝ^d) ⊆ H^1(ℝ^d)` with explicit constants, the trace of `H^1(ℝ^d)` on a Lipschitz graph and the chart traces of `H^1(Ω)` on a bounded Lipschitz domain as bounded operators, the trace kernel, the trace space `H^{1/2}(Γ)` defined as its orthogonal complement, with trace and extension operators, `H^1(Ω) ⧸ ker γ ≅ H^{1/2}(Γ)`, and `H^{-1/2}(Γ)` | ✅ | ✗ | `Domains/Traces/BoundaryTraceSpace` |
| The area formula for Lipschitz graphs: Lipschitz maps and Mathlib's Euclidean Hausdorff measure, the linear case by Mathlib's norm determinant, stretches and tilts, the gradient and the Gram density, good pieces, `μHE[n-1](γ(A)) = ∫_A √(1 + ‖∇φ‖²)` with `n = dim V` in set, measure and integral form; the outward unit normal | ✅ | ✗ | `Domains/Lipschitz/LipschitzGraphArea` |
| The surface measure of a bounded Lipschitz domain as `μHE[n-1]` on the boundary, its chart form, finiteness and null sets, the boundary `Γ` as a Lebesgue null set, the boundary trace in `L_p(Γ)`, `L_2(Γ)` with the traces of `H^1(Ω)` and `H^{1/2}(Γ)`, and the outward unit normal field | ✅ | ✗ | `Domains/Lipschitz/SurfaceMeasure` |
| The norm of the trace space: least extension norm, equivalence with the norm of `B^{1/2}_{2,2}(Γ)`, bounded preimages, the range of `H^{1/2}(Γ) → L_2(Γ)`, the Banach space `B^{1/2}_{2,2}(Γ)` isomorphic to `H^{1/2}(Γ)`, and the bounded linear right inverse of the trace | ✅ | ✗ | `Domains/Traces/TraceSpaceNorm` |
| The Sobolev–Slobodeckij norm on the boundary: Gagliardo's double integral for the surface measure, double integrals in the charts, the bounds by the chart-wise norm of `B^s_{p,p}(Γ)` in both directions, `W^{s,p}(Γ) = B^s_{p,p}(Γ)` for `0 < s < 1`, and the norm of `H^{1/2}(Γ)` as the Sobolev–Slobodeckij norm of `W^{1/2,2}(Γ)` | ✅ | ✗ | `Domains/Traces/BoundaryGagliardo` |
| Convolutions with sums of derivatives of dilated kernels, the local means of order two by the gradient, local means of Triebel–Lizorkin type on a set, the bounds of the local extension from one patch, bounded extensions from `L_p` bounds, pasting in `W^1_p(ℝ^d)`, the supports of the divergence kernels in the patches, the smooth cutoffs of the patches, dimension zero | ✅ | ✗ | `Domains/Extension/SobolevExtension` |
| Rychkov's extension operator for `W^1_p`, `1 < p < ∞`, on value–derivative jets with a finite constant, and from it the extension from one patch and the extension theorem for `1 < p < ∞` with a bound | ✅ | ✗ | `Domains/Extension/SobolevExtensionOperator` |
| The half-space and the reflection across a hyperplane, cutoffs near the hyperplane, integration by parts on the half-space, the linearity, weak derivatives and `L_p` bounds of the even reflection | ✅ | ✗ | `Domains/Extension/HalfSpaceReflection` |
| The flattening of a Lipschitz graph domain onto the half-space, the extension by reflection across the graph with its linearity, weak derivatives and `L_p` bounds, cutoffs from a bounded Lipschitz domain to its graph domains with the bounds of the patches | ✅ | ✗ | `Domains/Extension/ReflectionExtension` |
| Linear extensions of functions as extension operators on jets, the patches by reflection as linear extensions, the chosen extension operator for `W^1_p`, `1 ≤ p ≤ ∞`, built by reflection on value–derivative jets, `E u = u` on `Ω`, and from it the extension theorem for `W^1_p` on bounded Lipschitz domains for `1 ≤ p ≤ ∞` with a bound | ✅ | ✗ | `Domains/Extension/ReflectionExtensionOperator` |
| Weighted dilation averages `∫_a^b w(s) G_{e^s} ds`, their writing as sums of derivatives of order `m` of the higher divergence kernels when the weight has vanishing moments, the smoothed bump with its moment and kernel weights, and the local means kernels of order `L` as sums of derivatives of order `m ≤ L` of the higher divergence kernels, which have mean zero for `m < L` and lie in the reflected cone for bumps supported in `-K` | ✅ | ✗ | `Domains/Extension/HigherDivergenceKernels` |
| The local means of order `m + 1` of the smoothed bump by the derivatives of order `m`, local means of Triebel–Lizorkin type with smoothness `m` on a set, bounded extensions of order `m` from one patch and by a cutoff, pasting in `W^m_p(ℝ^d)` by the Leibniz rule, and the extension theorem (`W^m_p(Ω)` is the space of restrictions of `W^m_p(ℝ^d)`) on bounded Lipschitz domains for `1 < p < ∞` and every `m`, with a bound | ✅ | ✗ | `Domains/Extension/HigherSobolevExtension` |
| `W^1_p(Ω)` as the space of restrictions of `W^1_p(ℝ^d)` for `1 < p < ∞` (the extension theorem), and for `p = 2` `H^1(Ω) = W^1_2(Ω)`, Rellich's theorem in `W^1_2(Ω)`, the quotient norm of `H^1(Ω)` and the boundary traces of `W^1_2(Ω)` | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainW1p` |
| Gauss–Green on Lipschitz graph domains: Fubini in product coordinates, ray integrals, the normal weight, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` for compactly supported `C^1` functions in chart and surface form, the product rule for line derivatives, and Green's formula `∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)` | ✅ | ✗ | `Domains/Sobolev/LipschitzGraphGreen` |
| Green's formula on bounded Lipschitz domains: integration by parts in `H^1(ℝ^d)`, resolutions of unity equal to one near the boundary, the chart form for every resolution of unity, the outward unit normal as the chart normal and a unit vector almost everywhere on the boundary, `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` for `u, w ∈ H^1(Ω)`, the traces from both sides of a graph, and the zero extension: `1_Ω u ∈ W^1_2(ℝ^d)` iff the trace of `u` vanishes | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainGreen` |
| The kernel of the trace: convergence and mollification in `H^1(ℝ^d)`, smoothing with compact support, cone mollifiers, `H̃^1(Ω)` as the functions of `H^1(ℝ^d)` vanishing outside `Ω`, `ker γ = H^1_0(Ω)`, `H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)`, `H̃^1(Ω) ≅ ker γ` and `(ker γ)^* ≅ H^{-1}(Ω)` | ✅ | ✗ | `Domains/Traces/TraceKernel` |
| The Dirichlet Laplacian on bounded open sets: the inner product of `H^1(ℝ^d)` by the weak gradient, the compact dense embedding `H^1_0(Ω) → L_2(Ω)`, the Dirichlet eigenbasis as a spectral scheme with eigenvalues `λ_i ≥ 0`, the weak eigenvalue equation, `H^1_0(Ω)` as the Sobolev space of order `1` of the scheme, and `(L_2(Ω), H^1_0(Ω))_{θ,q} = A^θ_q` | ✅ | ✗ | `Domains/Spectral/DirichletEigenbasis` |
| The Neumann Laplacian on bounded Lipschitz domains: `W^1_2(Ω)` as the graph of the weak gradient in `L_2(Ω) × L_2(Ω)^n` and as jets, the dense embedding into `L_2(Ω)` through `H^1_0(Ω)`, Rellich's theorem with bounded `H^1(Ω)` representatives, the Neumann eigenbasis as a spectral scheme with eigenvalues `λ_i = σ_i⁻² - 1 ≥ 0`, among them `0`, the weak eigenvalue equation, `W^1_2(Ω)` as the Sobolev space of order `1` of the scheme, and `(L_2(Ω), W^1_2(Ω))_{θ,q} = A^θ_q` | ✅ | ✗ | `Domains/Spectral/NeumannEigenbasis` |
| Besov spaces on domains by eigenfunction expansions: differences and moduli of `H^1(ℝ^d)` functions by the gradient, the intrinsic modulus by the K-functional of `(L_2(Ω), W^1_2(Ω))`, `B^θ_{2,q}(Ω)` for `0 < θ < 1` as the approximation space of the Neumann eigenbasis on bounded Lipschitz domains, in dyadic blocks and for `q = 2` by the eigenvalues, and the Dirichlet approximation spaces in `B^θ_{2,q}(ℝ^d)` by zero extension | ✅ | ✗ | `Domains/Spectral/SpectralBesov` |
| The eigenbasis of the chart form on a compact manifold with or without boundary: zero extensions of restrictions, the bounded convex piece of each chart, the jets of the pieces in its Neumann space, Rellich's theorem `J = ∑_k L_k E_k J^N_k T_k` compact, dense range by lifts of `H^1(E)` functions, the chart scheme with eigenvalues `λ_i = σ_i⁻² - 1 ≥ 0`, levels `⌊√(1 + λ_i)⌋₊` and finitely many eigenvalues below each bound, the weak eigenvalue equation `a_A(φ_i, w) = λ_i ⟨e_i, J w⟩` with the natural boundary condition, and `H^1(M) = B^1_{2,2}(M)` in the eigenbasis | ✅ | ✗ | `Domains/Spectral/ChartFormEigenbasis` |
| Besov spaces on compact manifolds by eigenfunction expansions of the chart form: the pieces map `(L_2(μ), H^1_A(M))` into the Neumann couples of the bounded convex pieces, the lifts `H^1(E) → H^1_A(M)` by the closed graph theorem map `(L_2(E), H^1(E))` into it, `(L_2(μ), H^1_A(M))_{θ,q}` by the pieces, `B^θ_{2,q}(M)` for `0 < θ < 1` as the approximation space of the chart eigenbasis, in dyadic blocks and for `q = 2` by the eigenvalues, closures of smooth domains and the closed ball as examples with boundary, and the sphere with the chart measure of an atlas as an example without boundary | ✅ | ✗ | `Domains/Spectral/ManifoldSpectralBesov` |
| Bounded Lipschitz domains from the set-level definition: sets Lipschitz near a point, local graphs as Lipschitz graph domains, McShane's extension of local graphs, the structure from a family of charts and the converse, the ball | ✅ | ✗ | `Domains/Lipschitz/LocalLipschitzGraphs` |
| Bounded open convex sets as bounded Lipschitz domains: the ray length, its cone estimate, open convex sets, bounded or not, near a frontier point as regions above a Lipschitz graph, and the open unit cube with its closure | ✅ | ✗ | `Domains/Lipschitz/ConvexDomains` |
| Lipschitz graph domains with null graphs and boundaries, closures of convex Lipschitz graph domains as Besov domains, the quadrant as a Lipschitz graph domain and the quadrant model of manifolds with corners as a Besov domain, bounded Lipschitz domains with the extension property, closures of nonempty convex bounded Lipschitz domains and of nonempty bounded open convex sets, closed balls of positive radius and the closed unit cube as Besov domains | ✅ | ✗ | `Domains/Lipschitz/BesovDomains` |
| Functions vanishing outside a ball on a Besov domain: the interior up to a null set, the bounded convex pieces `interior Ω ∩ B(0, R)`, the cutoff identity, the intrinsic quasi-norm through the pieces, and `W^1_2 = B^1_{2,2}` on the interior | ✅ | ✗ | `Domains/Lipschitz/BesovDomainLocalisation` |
| Smooth bounded domains from the set-level definition: sets smooth near a point, the smooth cut-off of a local graph, the smooth domain from smooth charts and the converse, the ball as a smooth domain and the Besov spaces of its closure | ✅ | ✗ | `Domains/Manifolds/SmoothLocalGraphs` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
