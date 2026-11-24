# Lipschitz domains and traces

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Domains, traces and
manifolds*, chapters *Lipschitz domains*, *Traces on Lipschitz domains* and *Sobolev spaces on
domains*.

With `V` and the kernels of [Besov spaces on `ℝ^d`](Rd.md), the Besov spaces of a domain `Ω ⊆ V` are
described by intrinsic differences on `Ω` and as restrictions of `B^s_{p,q}(V)`, for Lipschitz graph
domains (Rychkov's extension) and for bounded Lipschitz domains (pasting with a resolution of unity
and pointwise multipliers). Traces on Lipschitz boundaries are built from the atoms and hold for
`0 < s < 1`; on the half-space, where smooth atoms restrict to smooth atoms, the trace theorem holds
for every `s > 0`. On a bounded Lipschitz domain, `B^s_{p,q}(Ω)` and `B^t_{p,q}(Γ)` are Banach
spaces, and the trace is a bounded linear operator from `B^s_{p,q}(Ω)` onto `B^{s-1/p}_{p,q}(Γ)`,
`1/p < s < 1 + 1/p`, with a bounded linear right inverse. In finite dimension the bounded
Lipschitz domains are the sets of the usual definition by local Lipschitz graphs, the open balls
and the bounded open convex sets among them. On a bounded Lipschitz domain inside a cube the Besov
spaces are the restrictions of the approximation spaces of tensor splines on the cube, also in
block form, and the splines restricted to the domain approximate at the corresponding rate in
`L_p` of the domain.
The Besov spaces on compact manifolds, the smooth bounded domains and the eigenbases of the
Laplacian are in [Manifolds and eigenbases](Manifolds.md), and the comparison of `H̃^s(Ω)` with
`H^s_0(Ω)` is in [Fractional Sobolev spaces on Lipschitz domains](FractionalSobolev.md).

On a bounded Lipschitz domain, `H^1` is the space of restrictions of `H^1(ℝ^d)`, with weak
derivatives in `L_2` of the domain and boundary traces in `B^{1/2}_{2,2}` of the boundary. On every
open set the Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)`, for real `s`, are built inside
Mathlib's `H^s(ℝ^d)`, with the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`; for `s ≥ 0`, `L_2(Ω)` is the
pivot space of the Gelfand triple `H̃^s(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)`. On a bounded Lipschitz domain the
trace space of `H^s(Ω)`, `1/2 < s < 3/2`, is defined as the orthogonal complement of the trace
kernel in `H^s(Ω)`, a Hilbert space whose trace and extension operators have norm at most `1` by
this definition, and its dual is identified with it by Riesz; the boundary traces of its elements
are the functions of
`B^{s-1/2}_{2,2}(Γ)`. Its norm is the least `H^s` norm of an extension and is equivalent to the
norm of `B^{s-1/2}_{2,2}(Γ)` by chart pieces. With the Gagliardo norm of its chart pieces,
`B^t_{2,2}(Γ)`, `0 < t < 1`, is the Hilbert space `H^t(Γ)`, the trace space of `H^s(Ω)` is
isomorphic to `H^{s-1/2}(Γ)`, and `H^t(Γ) ⊂ L_2(Γ) ⊂ H^{-t}(Γ)` is a Gelfand triple. On a
Lipschitz graph domain the area formula expresses Mathlib's Euclidean Hausdorff measure of the
boundary in the chart, with the Gram density `√(1 + ‖∇φ‖²)`. On a bounded Lipschitz domain the
surface measure is this Hausdorff measure on the boundary `Γ`; it gives the space `L_2(Γ)`, into
which `H^s(Ω)` and its trace space have bounded trace operators. The outward unit normal field is
pasted from the chart normals. On a bounded Lipschitz domain, every function of `W^1_p(Ω)`,
`1 < p < ∞`, is the restriction of a function of `W^1_p(ℝ^d)` under a bounded linear extension
operator, built from Rychkov's local extension with the local means of the gradient: the local means
kernels of order two are divergences of dilated kernels with mean zero, which form Calderón–Zygmund
families. For `p = 2` this identifies `H^1(Ω)` with `W^1_2(Ω)`. For every `1 ≤ p ≤ ∞` every function
of `W^1_p(Ω)` is the restriction of a function of `W^1_p(ℝ^d)` under a bounded linear extension
operator, by reflection across the boundary in the flattened coordinates of the graph domains. For
`1 < p < ∞` and every order `m` every function of `W^m_p(Ω)` is the restriction of a function of
`W^m_p(ℝ^d)` with a bound, by Rychkov's local extension with the local means of the derivatives of
order `m`, pasted with the Leibniz rule. On a Lipschitz graph domain, the Gauss–Green theorem
`∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` holds for compactly supported `C^1` functions, and Green's formula
`∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)`, by the density of the
compactly supported Schwartz functions in every `H^s(ℝ^d)`. On a bounded Lipschitz domain, Green's
formula `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` holds for `u, w ∈ H^1(Ω)`,
with the trace `γ_{L_2} : H^1(Ω) → L_2(Γ)`, pasted from the graph domains with a resolution of unity
equal to one near the boundary; the outward unit normal is the chart normal almost everywhere on the
boundary, and the zero extension of `u ∈ H^1(Ω)` lies in `W^1_2(ℝ^d)` iff the trace of `u` vanishes.
The kernel of the trace is `H^1_0(Ω)`: `H̃^1(Ω)` consists of the functions of `H^1(ℝ^d)` that
vanish outside `Ω` ([Fractional Sobolev spaces on Lipschitz domains](FractionalSobolev.md)), and
with the zero extension this gives `ker γ = H^1_0(Ω)` for the trace of `H^1(Ω)`; hence
`H^1(Ω) ⧸ H^1_0(Ω)` is isometric to the trace space of `H^1(Ω)`, by its definition as the
orthogonal complement of `ker γ`, and `(ker γ)^* ≅ H^{-1}(Ω)`. For `1/2 < s ≤ 1` the kernel of
the trace of `H^s(Ω)` is `H^s_0(Ω)`: an approximation from `H^1(ℝ^d)` is corrected by the
extension from the boundary, one operator for every smoothness, so that the correction lies in
`H^1_0(Ω) ⊆ H^s_0(Ω)`. For `1 ≤ s < 3/2` the zero extension gives `ker γ_s = H^s_0(Ω)` as well
([Fractional Sobolev spaces on Lipschitz domains](FractionalSobolev.md)).

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
  `0 < s < L` (`Rd.LipschitzGraph.rychkovExtension`,
  `Rd.LipschitzGraph.graphCutoff_rychkovExtension`,
  `Rd.LipschitzGraph.modNorm_rychkovExtension_le`).
* **Besov spaces on Lipschitz graph domains by intrinsic differences.** With `Ω` as above, let
  `ω_r(f, t, Ω)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_{L_p(Ω_{rh})}`, where
  `Ω_{rh} = {x : x, x + h, …, x + rh ∈ Ω}`, be the modulus of smoothness on `Ω`
  (`Rd.modulusOn`). For `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)` agrees on `Ω`
  with some `F ∈ L_p(V)` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, with equivalent quasi-norms, and
  `Ext f` is such an `F` (`Rd.LipschitzGraph.exists_besov_extension_iff_modulusOn`,
  `Rd.LipschitzGraph.modNormOn_le_modNorm`,
  `Rd.LipschitzGraph.modNorm_rychkovExtension_le_modNormOn`). The same condition describes the
  restrictions to `Ω` of the band-limited approximation spaces `A^s_q(L_p(V), (E_k))`
  (`Rd.LipschitzGraph.exists_memApprox_extension_iff`).
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
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn_indicator`,
  `Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff_indicator`). The extension comes with a
  bound: there is `C < ∞` such that `F` can be chosen with
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
  `L_p(H)` (`Rd.LipschitzGraph.graphTrace`). For `1 ≤ p < ∞`, `0 < s < 1` and `1 ≤ q ≤ ∞` there is
  `K < ∞` with
  `‖Tr f‖_{L_p(H)} + ‖(2^(ks) ω_1(Tr f, 2^(-k))_p)_k‖_{ℓ_q} ≤ K (‖f‖_{L_p(Ω)} +
  ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})` (`Rd.LipschitzGraph.modNorm_graphTrace_le`), and
  `Tr f = G ∘ γ` almost everywhere if `f` has a continuous representative `G`
  (`Rd.LipschitzGraph.graphTrace_ae_eq_comp_graphMap`). The cell atoms of the terms restrict to
  atoms of order `1` on `H` (`Rd.LipschitzGraph.isRegularAtom_comp_graphMap`), and the atomic
  synthesis on `H` gives the bound.
* **The trace space of a Lipschitz graph domain.** For `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and
  `L ≥ 2`, `g ∈ L_p(H)` is the trace of some `f ∈ L_p(V)` with
  `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff
  `‖g‖_p + ‖(2^(ks) ω_1(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (`Rd.LipschitzGraph.exists_graphTrace_eq_iff`).
  The extension `E g` of moment order `1` (`Rd.LipschitzGraph.graphExtension`) extends the atoms of
  `g` by
  `A(x) = a(Px) χ(2^j (⟪x, e⟫ - φ_j(Px)))` with a graph `φ_j` mollified at scale `2^(-j)`; it has a
  finite `B^{s+1/p}_{p,q}`-norm on `V` (`Rd.LipschitzGraph.modNorm_graphExtension_le`) and the trace
  `g` (`Rd.LipschitzGraph.graphTrace_graphExtension`).
* **Traces of every order on the half-space.** Let `Ω = {x : ⟪x, e⟫ > 0}` for a unit vector `e`
  (`Rd.LipschitzGraph.halfSpaceGraph`) and `H = e^⊥`. For `1 ≤ p < ∞`, `s > 0`, `1 ≤ q ≤ ∞`, `L ≥ 2`
  with `s + 1/p < L`, and `r > s`, `g ∈ L_p(H)` is the trace of some `f ∈ L_p(V)` with
  `‖f‖_{L_p(Ω)} + ‖(2^(k(s+1/p)) ω_L(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff
  `‖g‖_p + ‖(2^(ks) ω_r(g, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Rd.LipschitzGraph.exists_graphTrace_eq_iff_halfSpaceGraph`). The trace is bounded for every
  `s > 0` (`Rd.LipschitzGraph.modNorm_graphTrace_le_halfSpaceGraph`), since the cell atoms restrict
  to smooth atoms on `H`; the extension `E g = ∑_j (η_j ⋆ k_j ⋆ g)(Px) χ(2^j ⟪x, e⟫)` with local
  means of moment order `r` on `H` (`Rd.LipschitzGraph.graphExtension` of the flat graph, whose
  extended atoms are smooth of every order) is bounded
  (`Rd.LipschitzGraph.modNorm_flatExtension_le`) and has the trace `g`
  (`Rd.LipschitzGraph.graphTrace_flatExtension`).
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
  `r > s` gives the same space (`Rd.HasBesovExtension.modNormOn_order_le_of_hasBesovExtension`).
  Every Lipschitz graph domain `{x : φ(x) < ⟪x, e⟫}` has it (`Rd.LipschitzGraph.hasBesovExtension`),
  its graph and its frontier are null sets (`Rd.LipschitzGraph.volume_graph`,
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
* **Splines on bounded Lipschitz domains.** Let `Ω` be a bounded Lipschitz domain in a cube
  `Q = a + L [0, 1]^d` of the Euclidean space `ℝ^d` (`Cube.euclideanCubeAt`), `1 ≤ p < ∞`,
  `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 < s < r - 1 + 1/p`, and let the tensor splines of order `r` on `Q`
  be those of `[0, 1]^d` moved by `x ↦ a + L x` (`Cube.cubeSplineSchemeAt`). Then
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff `f` agrees on `Ω` with a
  function in the approximation space `A^s_q` of these splines
  (`Rd.BoundedLipschitzDomain.exists_memApprox_cubeSplineSchemeAt_iff`), iff `f = ∑_k b_k` on `Ω`,
  the series converging in `L_p(Q)`, with tensor splines `b_k` of level `k` on `Q` and
  `‖(2^(ks) ‖b_k‖_{L_p(Q)})_k‖_{ℓ_q} < ∞`
  (`Rd.HasBesovExtension.exists_cubeSplineBlocksAt_iff`). Both hold for every measurable `Ω ⊆ Q`
  with the extension property, where the function `G` in `A^s_q` can be chosen with
  `‖G‖_{A^s_q} ≤ C (‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})` for one `C < ∞`
  (`Rd.HasBesovExtension.exists_cubeSplineAt_le`) and the modulus may have any order `r' > s`
  (`Rd.HasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff_of_order_of_hasBesovExtension`),
  and one direction holds for every measurable `Ω ⊆ Q` and `0 ≤ s < r - 1 + 1/p`
  (`Rd.modNormOn_lt_top_of_memApprox_cubeSplineSchemeAt`). The errors `E_k(f)` of best
  approximation of `f` in `L_p(Ω)` by the restrictions of the splines of level `k`
  (`Rd.domainSplineScheme`) then satisfy
  `‖(2^(ks) E_k(f))_k‖_{ℓ_q} ≤ C (‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q})`
  (`Rd.HasBesovExtension.exists_approxNormDyadic_domainSplineScheme_le`). On `[0, 1]^d` itself the
  tensor splines describe the restrictions of `B^s_{p,q}(ℝ^d)`
  (`Cube.memApprox_cubeSplineScheme_iff_exists_besov`).
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
  change of chart for the traces of graph domains
  (`Rd.LipschitzGraph.graphTrace_ae_eq_graphTrace_comp`), whose Lipschitz chart maps keep null sets
  (`Rd.volume_image_eq_zero_of_lipschitzWith`).
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
* **Besov spaces on `Γ` and the trace operator.** With `Ω` and `Γ` as above and the surface
  measure `σ` of `Γ`, let `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`. `B^s_{p,q}(Ω)` is the space of the
  `f ∈ L_p(V)` vanishing outside `Ω` with
  `N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` for differences of a
  fixed order `r`, normed by `N_Ω`
  (`Rd.BoundedLipschitzDomain.DomainBesov`), and `B^t_{p,q}(Γ)` is the space of the
  `g ∈ L_p(Γ)` with a finite quasi-norm by chart pieces for a fixed resolution of unity, normed by
  it (`Rd.BoundedLipschitzDomain.BoundaryBesov`); both are Banach spaces
  (`Rd.BoundedLipschitzDomain.completeSpace_domainBesov`,
  `Rd.BoundedLipschitzDomain.completeSpace_boundaryBesov`), since the quasi-norms pass to `L_p`
  limits by Fatou's lemma for `ℓ_q` norms (`Rd.tendsto_modNormOn_sub_of_cauchy`), and
  `‖g‖_{L_p(Γ)} ≤ C ‖g‖_{B^t_{p,q}(Γ)}`
  (`Rd.BoundedLipschitzDomain.exists_eLpNorm_le_boundaryBesovNorm`). For `1 ≤ p < ∞`,
  `1/p < s < 1 + 1/p` and differences of order `2` on `Ω`, the trace
  `Tr : B^s_{p,q}(Ω) → B^{s-1/p}_{p,q}(Γ)` is a bounded linear operator, with `Tr f = Tr_Γ F` for
  every extension `F` of `f` with a finite norm on `V` (`Rd.BoundedLipschitzDomain.besovTrace`,
  `Rd.BoundedLipschitzDomain.besovTrace_ae`; Schneider–Vybíral, Theorem 4.11; Mayboroda,
  Theorem 1.1.3(i)), and it is onto (`Rd.BoundedLipschitzDomain.besovTrace_surjective`). For
  `0 < t < 1`, `g ↦ 1_Ω ∑_j ζ_j E_j G_j`, with the chart pieces `G_j` of `g`, the extensions
  `E_j` of the graph domains and cut-offs `ζ_j`, is a bounded linear right inverse
  `B^t_{p,q}(Γ) → B^{t+1/p}_{p,q}(Ω)` (`Rd.BoundedLipschitzDomain.besovExtend`,
  `Rd.BoundedLipschitzDomain.toLp_besovTrace_besovExtend`); it is linear because the `E_j` are
  (`Rd.LipschitzGraph.graphExtension_add`).
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
  (`Rd.BoundedLipschitzDomain.isBoundaryTrace_iff_forall_memSobolevW`), and `f` has the boundary
  trace `g` with a finite intrinsic norm iff `f ∈ H^1(Ω)` and `g` is its boundary trace
  (`Rd.BoundedLipschitzDomain.hasBoundaryTrace_iff_memSobolevOn`). The extension and trace theorems
  for bounded Lipschitz domains hold with bounds
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_le`,
  `Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`,
  `Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le`), and the restriction direction has
  constant `1` (`Rd.BoundedLipschitzDomain.modNormOn_le_modNorm_of_ae_eq`).
* **Sobolev spaces on open sets as Hilbert spaces.** Let `Ω ⊆ V` be open and `s` real. The
  elements of Mathlib's `H^s(V)` whose distribution vanishes on every test function of `Ω` form
  a closed subspace (`Rd.vanishOn`); for `s ≥ 0` they are the elements whose `L_2` function
  vanishes almost everywhere on `Ω` (`Rd.mem_vanishOn_iff_sobolevToL2`, `Rd.mem_vanishOn_one_iff`
  for `s = 1`). Its orthogonal complement is the Hilbert space
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
  `[W, U] = ⟪J_{-s} W, J_s U⟫_{L_2}` pairs `W ∈ H^{-s}(V)` with `U ∈ H^s(V)` (`Rd.sobolevPairing`),
  with `|[W, U]| ≤ ‖W‖ ‖U‖`, `[φ, U] = U(φ)` for test functions `φ` of `Ω`, and
  `[ψ, U] = ⟪ψ, U⟫_{L_2}` for Schwartz `ψ` at `s = 1` (`Rd.norm_sobolevPairing_le`,
  `Rd.sobolevPairing_ofTest_left`, `Rd.sobolevPairing_one_toLp`). `U` is orthogonal to `H̃^s(Ω)` iff
  `J_{2s} U` vanishes on `Ω` (`Rd.mem_orthogonal_tildeSpace_iff`), so `J_{2s}` maps `H̃^s(Ω)`
  isometrically onto `H^{-s}(Ω)` and `H^s(Ω)` onto `H̃^{-s}(Ω)` (`Rd.tildeEquivRestriction`,
  `Rd.restrictionEquivTilde`). Every bounded functional `ℓ` on `H̃^s(Ω)` is `U ↦ [W, U]` for
  exactly one `W ∈ H^{-s}(Ω)`, with `‖W‖ = ‖ℓ‖` (`Rd.tildeDualEquiv`, `Rd.tildeDualEquiv_apply`,
  `Rd.tildeDualEquiv_eq_iff`; Chandler-Wilde, Hewett and Moiola, Theorem 3.3), and every extension
  of `W` to `V` gives the same pairing (`Rd.tildeDualEquiv_apply_of_restrictProj_eq`); likewise
  `(H^s(Ω))^* ≅ H̃^{-s}(Ω)` and `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` (`Rd.dualRestrictionEquiv`,
  `Rd.dualZeroBoundaryEquiv`). On the way, the Bessel potential `J_t` of a real Schwartz
  function is real (`Rd.conj_besselSchwartz_apply`), from `conj (𝓕 f) = 𝓕⁻(conj f)` on `V`
  (`Rd.conj_fourier_apply`).
* **Gelfand triples on `ℝ^d` and on open sets.** Each triple follows from the general theorem
  on the pivot dual (`ContinuousLinearMap.pivotDual_injective_iff`): the space contributes its
  embedding into `L_2`, the dense range of the embedding and the identification of the pivot
  dual. Let `s ≥ 0`. `ι_s : H^s(V) → L_2(V)` is injective with dense range
  (`Rd.denseRange_sobolevToL2`), and its pivot dual `L_2(V) → (H^s(V))^*`,
  `g ↦ ⟪g, ι_s ·⟫_{L_2}` (`ContinuousLinearMap.pivotDual`), is the pairing `[W, ·]` with the
  element `W ∈ H^{-s}(V)` whose distribution is `g` (`Rd.toDistr_sobolevInclusion_ofLp`,
  `Rd.pivotDual_sobolevToL2_apply_apply`): `L_2(V)` is the pivot space of
  `H^s(V) ⊂ L_2(V) ⊂ H^{-s}(V)`. For open `Ω`, `U ↦ (ι_s U)|_Ω` is injective with dense range
  from `H̃^s(Ω)` into `L_2(Ω)` (`Rd.tildeToL2`, `Rd.tildeToL2_injective`,
  `Rd.denseRange_tildeToL2`), and its pivot dual followed by the duality
  `(H̃^s(Ω))^* ≅ H^{-s}(Ω)` (`Rd.tildeDualEquiv`) sends `g ∈ L_2(Ω)` to the `W_g ∈ H^{-s}(Ω)` with
  `[W_g, U] = ∫_Ω conj (g) ι_s U` for every `U ∈ H̃^s(Ω)`
  (`Rd.pivotDual_tildeToL2_apply_apply`, `Rd.sobolevPairing_tildeDualEquiv_pivotDual_tildeToL2`):
  the triple `H̃^s(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)`, for `s = 1` the triple `H^1_0(Ω) ⊂ L_2(Ω) ⊂ H^{-1}(Ω)`.
* **The trace spaces of a bounded Lipschitz domain.** For every `U ∈ H^1(V)` with `L_2` function
  `ι U` (`Rd.toL2`), `‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2} ≤ C ‖U‖` with an explicit
  constant (`Rd.modNorm_two_le_norm`, `Rd.sobolevOneBesovConst`). Conversely
  `‖U‖ ≤ C' (‖ι U‖_2 + ‖(2^k ω_2(ι U, 2^(-k))_2)_k‖_{ℓ_2})` with an explicit constant
  (`Rd.enorm_le_modNorm_two`, `Rd.sobolevOneInvConst`). The `B^{1/2}_{2,1}` quantity
  is at most `√2` times this `B^1_{2,2}` quantity (`Rd.modNorm_half_one_le`), so
  `‖ι U‖_2 + ∑_k 2^(k/2) ω_2(ι U, 2^(-k))_2 ≤ √2 C ‖U‖` (`Rd.modNorm_half_one_le_norm`); for
  `1/2 < s < 2` and `U ∈ H^s(V)` with `L_2` function `ι_s U` (`Rd.sobolevToL2`) the same
  quantity of `ι_s U` is at most `c_s C_{s,2} ‖U‖` with explicit constants
  (`Rd.modNorm_half_one_le_norm_of_lt`), so the trace of `H^s(V)` on a Lipschitz graph is
  bounded (`Rd.LipschitzGraph.exists_enorm_graphTrace_sobolevToL2_le`). Let `Ω` be a bounded
  Lipschitz domain with boundary `Γ`, `1/2 < s < 3/2`, and `H^s(Ω)` the Hilbert space of the
  restriction space. The chart traces
  `u ↦ Tr_j(ψ_j ι_s u)` are bounded operators from `H^s(Ω)` to `L_2` of the hyperplanes of the
  charts (`Rd.BoundedLipschitzDomain.chartTrace`), and their common kernel, the trace kernel
  `ker γ_s` (`Rd.BoundedLipschitzDomain.traceKer`), consists of the `u` whose boundary trace
  vanishes almost everywhere on `Γ`, for every resolution of unity
  (`Rd.BoundedLipschitzDomain.mem_traceKer_iff`). The trace space of `H^s(Ω)` is defined as its
  orthogonal complement (`Rd.BoundedLipschitzDomain.TraceSpace`), with the trace `γ_s`, the
  orthogonal projection, and the extension `E_s`, the inclusion
  (`Rd.BoundedLipschitzDomain.domainTrace`, `Rd.BoundedLipschitzDomain.domainExtend`). By this
  definition `γ_s E_s = id`, `‖γ_s u‖ ≤ ‖u‖`, `‖E_s w‖ = ‖w‖`, the kernel of `γ_s` is the trace
  kernel, and `H^s(Ω) ⧸ ker γ_s` is isometrically isomorphic to the trace space
  (`Rd.BoundedLipschitzDomain.domainTrace_domainExtend`,
  `Rd.BoundedLipschitzDomain.ker_domainTrace`, `Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`).
  Two elements of `H^s(Ω)` have the same trace iff their boundary traces agree almost everywhere on
  `Γ` (`Rd.BoundedLipschitzDomain.domainTrace_eq_iff`), and `w ↦ Tr_Γ(E_s w)` maps the trace space
  onto `B^{s-1/2}_{2,2}(Γ)` modulo null sets of `Γ`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_domainExtend`,
  `Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_domainExtend_eventuallyEq_iff`), with equivalent norms
  (*The norm of the trace space* below). The dual of the trace space
  (`Rd.BoundedLipschitzDomain.DualTraceSpace`) is conjugate-linearly isometric to it by Riesz
  (`Rd.BoundedLipschitzDomain.dualTraceEquiv`), and the adjoint of the trace is the extension
  (`Rd.BoundedLipschitzDomain.adjoint_domainTrace`). The family is indexed by `s`; `Ω.TraceSpace 1`
  is the trace space of `H^1(Ω)`, and its statements with `Rd.toL2` are
  `Rd.BoundedLipschitzDomain.mem_traceKer_one_iff` and
  `Rd.BoundedLipschitzDomain.domainTrace_one_eq_iff`.
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
  `Rd.LipschitzGraph.inner_normalAt_neg_of_mem_graphCone`).
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
  (`Rd.BoundedLipschitzDomain.BoundaryL2`) and `1/2 < s < 3/2`, the trace
  `γ_{L_2} : H^s(Ω) → L_2(Γ)` and the injective trace `τ` of the trace space of `H^s(Ω)` are
  bounded operators with `γ_{L_2} = τ ∘ γ_s`, given almost everywhere by the boundary trace, and
  the kernel of `γ_{L_2}` is the trace kernel
  (`Rd.BoundedLipschitzDomain.boundaryTraceL2`, `Rd.BoundedLipschitzDomain.traceL2`,
  `Rd.BoundedLipschitzDomain.boundaryTraceL2_apply_ae`,
  `Rd.BoundedLipschitzDomain.traceL2_injective`, `Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`);
  every `g ∈ B^{s-1/2}_{2,2}(Γ)` is `τ w` for some `w`, so `B^{s-1/2}_{2,2}(Γ) ⊆ L_2(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_ae_eq`,
  `Rd.BoundedLipschitzDomain.memLp_of_memBoundaryBesov`). The outward unit normal field
  `ν(y) = ∑_j ψ_j(y) ν_j(P_j y)`, with the chart normals `ν_j` and the canonical resolution of
  unity `ψ` (`Rd.BoundedLipschitzDomain.boundaryPartition`, nonnegative), is measurable with
  `‖ν‖ ≤ 1` (`Rd.BoundedLipschitzDomain.outwardNormal`,
  `Rd.BoundedLipschitzDomain.norm_outwardNormal_le`).
* **The norm of the trace space.** Let `Ω` be a bounded Lipschitz domain with boundary `Γ`,
  `1/2 < s < 3/2`, `Ω.TraceSpace s` the trace space of `H^s(Ω)` and `τ_s` its trace into
  `L_2(Γ)`. For every resolution of unity `ψ` and `w` in the trace space, `‖w‖` is the least norm
  `‖U‖` of a `U ∈ H^s(V)` with the boundary trace of `w`
  (`Rd.BoundedLipschitzDomain.enorm_eq_iInf`), the quotient norm of `γ_s(H^s(Ω))`, which McLean,
  Theorem 3.38, shows to be equivalent to his chart norm, and there is `C < ∞` with
  `‖w‖ ≤ C ‖τ_s w‖_{B^{s-1/2}_{2,2}(Γ)}` and `‖τ_s w‖_{B^{s-1/2}_{2,2}(Γ)} ≤ C ‖w‖`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`). Every `g ∈ B^{s-1/2}_{2,2}(Γ)` is the
  boundary trace of some `E_s w` with `‖w‖ ≤ C ‖g‖_{B^{s-1/2}_{2,2}(Γ)}`
  (`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov_le`), and the range of `τ_s`
  is `B^{s-1/2}_{2,2}(Γ)` (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff`). `τ_s` is an
  isomorphism of the trace space of `H^s(Ω)` onto the Banach space `B^{s-1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.traceSpaceEquivBoundaryBesov`), and the trace has the bounded
  linear right inverse `E_s τ_s⁻¹ : B^{s-1/2}_{2,2}(Γ) → H^s(Ω)`, as in McLean, Theorem 3.38
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
  `Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_rpow_le`). For `p = 2` and
  `1/2 < s < 3/2` there is `C < ∞` with
  `‖w‖² ≤ C (‖τ_s w‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |τ_s w(y) - τ_s w(x)|² / |y - x|^(n+2s-2) dσ dσ)` and the
  reverse bound for all `w` in the trace space of `H^s(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`), and `g ∈ L_2(Γ)` lies in
  the range of `τ_s` iff its form with smoothness `s - 1/2` is finite
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff_slobodeckij`).
* **`H^t(Γ)`.** With `Ω`, `Γ` and `σ` as above and `0 < t < 1`, `H^t(Γ)` is `B^t_{2,2}(Γ)` with
  the chart-wise Gagliardo norm
  `‖g‖²_{L_2(Γ)} + ∑_j ∫_{H_j} ∫_{H_j} |G_j(y') - G_j(x')|² / |y' - x'|^(n-1+2t) dy' dx'` of the
  chart pieces `G_j = (ψ_j g) ∘ γ_j` (`Rd.BoundedLipschitzDomain.BoundarySobolev`). This norm is the
  norm of the injective linear map `g ↦ (g, ((x', y') ↦ G_j(y') - G_j(x'))_j)` into a product of
  `L_2` spaces, for the measures `|y' - x'|^(-(n-1+2t)) dx' dy'` on `H_j × H_j`
  (`Rd.gagliardoMeasure`, `Rd.BoundedLipschitzDomain.gagliardoEmbedding`), so it comes from an
  inner product: `H^t(Γ)` is a Hilbert space, isomorphic to `B^t_{2,2}(Γ)` by the identity
  (`Rd.BoundedLipschitzDomain.boundarySobolevEquivBoundaryBesov`), with a norm equivalent to
  `(‖g‖²_{L_2(Γ)} + ∫_Γ ∫_Γ |g(y) - g(x)|² / |y - x|^(n-1+2t) dσ dσ)^(1/2)`
  (`Rd.BoundedLipschitzDomain.exists_boundarySobolev_norm_equiv_slobodeckij`); its dual
  `H^{-t}(Γ)` is conjugate-linearly isometric to it by Riesz
  (`Rd.BoundedLipschitzDomain.dualBoundarySobolevEquiv`). `H^t(Γ)` is dense in `L_2(Γ)`, since it
  contains the restrictions to `Γ` of the smooth functions with compact support
  (`Rd.BoundedLipschitzDomain.boundarySobolevToL2`,
  `Rd.BoundedLipschitzDomain.denseRange_boundarySobolevToL2`), so its pivot dual
  `g ↦ (h ↦ ∫_Γ conj (g) h dσ)` maps `L_2(Γ)` injectively into `H^{-t}(Γ)`
  (`Rd.BoundedLipschitzDomain.pivotDual_boundarySobolevToL2_apply_apply`,
  `ContinuousLinearMap.pivotDual_injective_iff`): `H^t(Γ) ⊂ L_2(Γ) ⊂ H^{-t}(Γ)` is a Gelfand
  triple with pivot space `L_2(Γ)`. For `1/2 < s < 3/2` the trace space of
  `H^s(Ω)` is isomorphic to `H^{s-1/2}(Γ)` (McLean, Theorem 3.38;
  `Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev`; for `s = 1` with values in
  `H^{1/2}(Γ)`, `Rd.BoundedLipschitzDomain.traceSpaceOneEquivBoundarySobolevHalf`); the trace
  `H^s(Ω) → H^{s-1/2}(Γ)` (`Rd.BoundedLipschitzDomain.sobolevTrace`) has kernel `ker γ_s` and the
  bounded linear right inverse `Rd.BoundedLipschitzDomain.sobolevExtend`, and it is the Besov
  trace of `1_Ω ι_s u ∈ B^s_{2,2}(Ω)` (`Rd.BoundedLipschitzDomain.toLp_sobolevTrace_eq_besovTrace`).
* **The extension theorem.** Let `Ω` be a bounded Lipschitz domain in `V` of dimension `n ≥ 1`,
  `(e_i)` the orthonormal basis `Rd.gridBasis V`, and `1 < p < ∞`. There is a finite `C` such that
  every `f ∈ L_p(Ω)` with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` on `Ω` agrees almost
  everywhere on `Ω` with some `F ∈ W^1_p(V)` whose weak derivatives `G_i = ∂_{e_i} F` satisfy
  `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`); hence `f ∈ W^1_p(Ω)` iff `f` agrees on `Ω`
  with some `F ∈ W^1_p(V)` (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolevW`).
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
  (`Rd.exists_memSobolevW_of_memWeakSobolev_of_subsingleton`). The membership statements hold for
  every `1 ≤ p ≤ ∞` by the theorem by reflection below; the bound with
  the constant `C`, and with it Rellich's theorem and the quotient norm, is Rychkov's local
  extension with the local means of the gradient: for a bump with the moment kernel `m` of order
  two, `k_{j+1} = 2^{-j} ∑_i ∂_{e_i} (K_i)_{2^j}`
  (`Rd.LocalMeansBump.meansKernel_two_succ_apply`), so on a patch
  `k_{j+1} ⋆ 1_T f = 2^{-j} ∑_i (K_i)_{2^j} ⋆ 1_T g_i`
  (`Rd.LocalMeansBump.conv_meansKernel_two_succ_eq`),
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
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev_reflection`); hence `f ∈ W^1_p(Ω)` iff `f`
  agrees on `Ω` with some `F ∈ W^1_p(V)`, in every dimension
  (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolevW`). On a Lipschitz
  graph domain `Ω = {x : φ(x) < ⟪x, e⟫}` with `M`-Lipschitz `φ`, the flattening
  `F(x) = x - φ(x) e` and its inverse are `(1 + M)`-Lipschitz and preserve Lebesgue measure
  (`Rd.LipschitzGraph.measurePreserving_graphFlatten`,
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
  (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolevW_order`). For the smoothed bump
  `b'` of a bump `b` and `m ≤ L`, the local means kernels of order `L` are
  `k_{j+1} = 2^{-jm} ∑_i ∂^{e_i} (K_i)_{2^j}` with the higher divergence kernels `K_i` of `b`, so
  on a patch `k_{j+1} ⋆ 1_T f = 2^{-jm} ∑_i (K_i)_{2^j} ⋆ 1_T ∂^{e_i} f`
  (`Rd.LocalMeansBump.conv_meansKernel_succ_eq_sum_higherKernel`); for `L = m + 1` the strong type
  of the Calderón–Zygmund families `((K_i)_{2^j})_j` bounds the local means of Triebel–Lizorkin type
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
  `Rd.LipschitzGraph.inner_normalAt_mul_gramDensity`). For every `C^1` function `g` with compact
  support and every `v ∈ V`, `∫_Ω ∂_v g = ∫_H g(γ x') n_v(x') dx' = ∫_{γ(H)} g ⟪v, ν ∘ P⟫ dμHE[n-1]`
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
  (`Rd.BoundedLipschitzDomain.outwardNormal`), boundary balls `B_j`, graph domains `Ω_j` with traces
  `Tr_j`, graph maps `γ_j` and normal weights `n^j_v`. For all `U, W ∈ H^1(V)` and every `v ∈ V`,
  `∫_Ω (∂_v U) W + U ∂_v W = ∫_Γ T_Γ U · T_Γ W ⟪v, ν⟫ dσ` with the trace `T_Γ : H^1(V) → L_2(Γ)`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_surfaceMeasure`), and for all `u, w ∈ H^1(Ω)`,
  `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` with the trace
  `γ_{L_2} : H^1(Ω) → L_2(Γ)` (`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne`), also
  with weak derivatives on `Ω`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne_of_hasWeakLineDeriv`). In chart form,
  for every resolution of unity `ψ` on `Γ`, all `f, g ∈ W^1_2(V)` and the weak derivatives
  `f_v = ∂_v f`, `g_v = ∂_v g` in `L_2(V)`,
  `∫_Ω f_v g + f g_v = ∑_j ∫_{H_j} ψ_j(γ_j x') Tr_j f(x') Tr_j g(x') n^j_v(x') dx'`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_of_boundaryPartition`). On every ball `B_j`,
  `ν = ν_j ∘ P_j` `σ`-almost everywhere, so `‖ν‖ = 1` `σ`-almost everywhere
  (`Rd.BoundedLipschitzDomain.outwardNormal_ae_eq_normalAt`,
  `Rd.BoundedLipschitzDomain.norm_outwardNormal_ae`). For every `u ∈ H^1(Ω)`, the zero extension
  `1_Ω u` lies in `W^1_2(V)` iff the trace of `u` vanishes
  (`Rd.BoundedLipschitzDomain.memSobolevW_indicatorLp_iff_mem_traceKer`), and then
  `∂_v (1_Ω u) = 1_Ω ∂_v u`
  (`Rd.BoundedLipschitzDomain.hasWeakLineDeriv_indicatorLp_of_mem_traceKer`). The proof pastes
  Green's formula on the graph domains with a resolution of unity equal to one near `Γ`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_of_nhds`); the interior piece integrates to zero by
  integration by parts in `H^1(V)` (`Rd.integral_weakDeriv_mul_add_eq_zero`). The chart normals
  agree almost everywhere because Gauss–Green for `C^1` functions in two charts gives the same
  boundary integrals (`Rd.BoundedLipschitzDomain.normalAt_graphMap_ae_eq`), and the traces from
  above and from below a graph agree (`Rd.LipschitzGraph.traceH1_ae_eq_traceH1_lowerGraph`).
* **The kernel of the trace.** Let `Ω` be a bounded Lipschitz domain with boundary `Γ`, `H^1(Ω)`
  the Hilbert space of restrictions of `H^1(V)`, `H̃^1(Ω)` the closure of the test functions of
  `Ω` in `H^1(V)`, `H^1_0(Ω)` the closure of their restrictions in `H^1(Ω)`, and `ker γ` the
  `u ∈ H^1(Ω)` whose boundary trace vanishes almost everywhere on `Γ`. Then
  `ker γ = H^1_0(Ω)` (`Rd.BoundedLipschitzDomain.traceKer_one_eq_zeroBoundarySpace`; McLean,
  Theorem 3.40). For every `U ∈ H^1(V)`, `U ∈ H̃^1(Ω)` iff the `L_2` function of `U` vanishes
  almost everywhere outside `Ω` (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`). The map
  sending the class of `u` modulo `H^1_0(Ω)` to `γ u` is an isometric isomorphism of
  `H^1(Ω) ⧸ H^1_0(Ω)` onto the trace space of `H^1(Ω)`, by `ker γ = H^1_0(Ω)` and the definition
  of the trace space as the orthogonal complement of `ker γ`
  (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace` at `s = 1`, in
  [Fractional Sobolev spaces on Lipschitz domains](FractionalSobolev.md)); restriction is an
  isometric isomorphism `H̃^1(Ω) ≅ ker γ` (`Rd.BoundedLipschitzDomain.tildeEquivTraceKer`), and
  every bounded functional `ℓ` on `ker γ` is `u ↦ [W, u]` for exactly one `W ∈ H^{-1}(Ω)` with
  `‖W‖ = ‖ℓ‖` (`Rd.BoundedLipschitzDomain.dualTraceKerEquiv`,
  `Rd.BoundedLipschitzDomain.dualTraceKerEquiv_apply`,
  `Rd.BoundedLipschitzDomain.dualTraceKerEquiv_eq_iff`). For a Schwartz function `η` with
  `∫ η = 1` and `c_i → ∞`, `η_{c_i} ⋆ U → U` in `H^1(V)` (`Rd.tendsto_of_toL2_eq_convLp`), since
  weak derivatives commute with convolution (`Rd.hasWeakLineDeriv_convLp`); the description of
  `H̃^1(Ω)` is the case `s = 1` of `Rd.BoundedLipschitzDomain.mem_tildeSpace_iff_of_nonneg`.
* **The kernel of the trace of `H^s(Ω)`, `1/2 < s ≤ 1`.** With `Ω` and `Γ` as above,
  `1/2 < s < 3/2` and `ker γ_s` the `u ∈ H^s(Ω)` whose boundary trace vanishes almost everywhere
  on `Γ`, `H^s_0(Ω) ⊆ ker γ_s` (`Rd.BoundedLipschitzDomain.zeroBoundarySpace_le_traceKer`), and
  for `1/2 < s ≤ 1`, `ker γ_s = H^s_0(Ω)`
  (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace_of_le_one`; McLean, Theorem 3.40,
  applied in this range by Hewett–Moiola, Remark 2.6). Quantitatively, there is `K < ∞` such that
  for every `u ∈ ker γ_s` and every `W' ∈ H^1(V)` some `y ∈ H^s_0(Ω)` has
  `‖y - u‖ ≤ K ‖W' - u‖_{H^s(V)}`, with `W'` and `u` read in `H^s(V)`
  (`Rd.BoundedLipschitzDomain.exists_mem_zeroBoundarySpace_enorm_sub_le`). The trace
  `T^s_Γ : H^s(V) → L_2(Γ)` commutes with the inclusions `H^s(V) ⊆ H^t(V)`, and the inclusions
  `H^s(Ω) ⊆ H^t(Ω)` map `ker γ_s` into `ker γ_t`, for `1/2 < t ≤ s`
  (`Rd.BoundedLipschitzDomain.ambientTraceL2_sobolevInclusion`,
  `Rd.BoundedLipschitzDomain.restrictionInclusion_mem_traceKer`); the extension `E_Γ` from the
  boundary maps `B^{s-1/2}_{2,2}(Γ)` into `H^s(V)` with a bound
  (`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_besovExtendLp`,
  `Rd.BoundedLipschitzDomain.exists_enorm_le_of_sobolevToL2_eq_besovExtendLp`), and for
  `ι_s W = E_Γ T^s_Γ U` the difference `(U - W)|_Ω` lies in `ker γ_s`
  (`Rd.BoundedLipschitzDomain.restrictProj_sub_mem_traceKer`). The proof corrects `W'` by
  `E_Γ T^1_Γ W'` inside `H^1(Ω)`, where `ker γ_1 = H^1_0(Ω) ⊆ H^s_0(Ω)`, and bounds the
  correction in `H^s(V)` through the same function `E_Γ T^1_Γ W'`. For `1 ≤ s < 3/2` the zero
  extension gives `ker γ_s = H^s_0(Ω)` as well
  ([Fractional Sobolev spaces on Lipschitz domains](FractionalSobolev.md)).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Lipschitz graph domains: cone and closed cone, the closure of the domain, the closure plus the cone, cone bump, kernels supported in the reflected cone, support principle for two sets and for the domain | ✅ | ✗ | `Domains/Lipschitz/LipschitzGraph` |
| The local extension of a bump on a set: absolute convergence from bounds of the weighted local means, the Besov bound, agreement on the set it sees; Rychkov's extension as its case `W = Ω`, restrictions to Lipschitz graph domains by intrinsic local means | ✅ | ✗ | `Domains/Extension/RychkovExtension` |
| Restrictions to Lipschitz graph domains by intrinsic differences | ✅ | ✗ | `Domains/Extension/LipschitzGraphBesov` |
| Local versions of Rychkov's extension: boundary and inner patches, cone bumps of small radius, short steps into the closed cone, local means on a set bounded by the moduli on a larger set, the local extension with a bound | ✅ | ✗ | `Domains/Extension/LocalExtension` |
| Bounded Lipschitz domains: the domain as the graph domain inside each boundary ball, the patches covering the closure, pasting over the patches, pasting of local extensions, subadditivity and homogeneity of the quasi-norms by differences, the extension with a bound, the Banach space `B^s_{p,q}(Ω)` by intrinsic differences and extensions of its elements | ✅ | ✗ | `Domains/Lipschitz/BoundedLipschitz` |
| Null hyperplanes, Lipschitz graph domains with the extension property, the half-space, the first axis `e₀` of `ℝ^n`, and the models of manifolds as Besov domains | ✅ | ✗ | `Domains/Lipschitz/HalfSpace` |
| Traces of every order on the half-space: trace theorem, extension, trace space | ✅ | ✗ | `Domains/Traces/HalfSpaceTrace` |
| Graph map of a Lipschitz graph domain, the boundary as the graph, restrictions of atoms to the graph | ✅ | ✗ | `Domains/Lipschitz/GraphParametrization` |
| Traces on Lipschitz graph domains: boundedness, linearity, trace of continuous functions | ✅ | ✗ | `Domains/Traces/GraphTrace` |
| Mollified graph and vertical cut-off with bounds of their differences | ✅ | ✗ | `Domains/Traces/MollifiedGraph` |
| Extension from the boundary of a Lipschitz graph domain, its linearity, its trace space | ✅ | ✗ | `Domains/Traces/GraphTraceExtension` |
| Traces in charts: locality, approximation, change of chart, products and their bound, finite sums | ✅ | ✗ | `Domains/Traces/GraphTraceCharts` |
| Traces on bounded Lipschitz domains: Besov spaces on the boundary, linearity of the boundary trace, the trace space | ✅ | ✗ | `Domains/Traces/LipschitzBoundaryTrace` |
| Besov quasi-norms on the boundary: chart pieces, bounded trace and extension for `1 ≤ p < ∞`, independence of the resolution of unity, chart pieces as bounded operators `L_p(Γ) → L_p(H_j)`, the bound of the `L_p(Γ)` norm, the Banach space `B^t_{p,q}(Γ)`, the trace operator from `B^s_{p,q}(Ω)` onto `B^{s-1/p}_{p,q}(Γ)` and its bounded linear right inverse | ✅ | ✗ | `Domains/Traces/BoundaryBesovNorm` |
| Flattening of graph domains, the Lipschitz bounds of the flattening and its inverse, the graph in the image of the hyperplane, product and graph coordinates, preservation of the Lebesgue measure for every Lipschitz graph | ✅ | ✗ | `Domains/Lipschitz/GraphStraightening` |
| `H^1` on bounded Lipschitz domains defined as restrictions of `H^1(ℝ^d)`, by intrinsic differences, the identification with the restriction space, the weak gradient, and the boundary traces, which form `B^{1/2}_{2,2}(Γ)` | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainH1` |
| The Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` on open sets inside Mathlib's `H^s(ℝ^d)`, `H^s(Ω)` as a quotient, Rellich's theorem for `H^1(Ω)`, the restriction of an element agreeing with `u ∈ H^1(Ω)` on `Ω`, restrictions determined by the `L_2` functions on `Ω` for `s ≥ 0` and with the same `L_2` function on `Ω`, the bound of the `H^1` norm by the `W^1_2` norm, the weak derivatives as bounded operators on `H^1(ℝ^d)` and as derivatives of tempered distributions, with `∂_v U ∈ H^{s-1}(ℝ^d)` for `U ∈ H^s(ℝ^d)`, `s ≥ 1`; the locality of the weak derivatives and the weak derivatives of restrictions on `Ω`; differences and moduli of `H^1(ℝ^d)` functions by the gradient, the density of compactly supported Schwartz functions in `H^s(ℝ^d)`, Schwartz functions with compact support in `Ω` in the span of the test functions, vanishing on `Ω` by the `L_2` function for every `s ≥ 0`, `H̃^s(ℝ^d) = H^s(ℝ^d)`, the isometry `H̃^1(Ω) ≅ H^1_0(Ω)`, the vanishing of `H̃^s(Ω)` outside `Ω` for `s ≥ 0`, and `ι_s U = 1_Ω ι_s(U + W)` for `U ∈ H̃^s(Ω)` and `W` vanishing on `Ω` | ✅ | ✗ | `Domains/Sobolev/SobolevRestrictionSpaces` |
| The Bessel potential of real Schwartz functions as a real function, the isometry `J_{2s} : H^s(ℝ^d) → H^{-s}(ℝ^d)`, the pairing of `H^{-s}` and `H^s`, and the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`, `(H^s(Ω))^* ≅ H̃^{-s}(Ω)`, `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` on open sets; the Gelfand triples `H^s(ℝ^d) ⊂ L_2(ℝ^d) ⊂ H^{-s}(ℝ^d)` and `H̃^s(Ω) ⊂ L_2(Ω) ⊂ H^{-s}(Ω)`, `s ≥ 0`, with dense range of `ι_s` and of its restriction to `Ω` | ✅ | ✗ | `Domains/Sobolev/SobolevDuality` |
| `H^1(ℝ^d) ⊆ B^{1/2}_{2,1}(ℝ^d)` and its converse `B^1_{2,2}(ℝ^d) ⊆ H^1(ℝ^d)` with explicit constants, the traces of `H^1(ℝ^d)` and `H^s(ℝ^d)`, `1/2 < s < 2`, on a Lipschitz graph, and for `1/2 < s < 3/2` the chart traces of `H^s(Ω)` on a bounded Lipschitz domain as bounded operators, the trace kernel, the restriction keeping the boundary trace, the trace space of `H^s(Ω)` defined as the orthogonal complement of the trace kernel, with trace and extension operators, `H^s(Ω) ⧸ ker γ_s` isometric to it, its boundary traces in `B^{s-1/2}_{2,2}(Γ)`, and its dual | ✅ | ✗ | `Domains/Traces/BoundaryTraceSpace` |
| The area formula for Lipschitz graphs: Lipschitz maps and Mathlib's Euclidean Hausdorff measure, the linear case by Mathlib's norm determinant, stretches and tilts, the gradient and the Gram density, good pieces, `μHE[n-1](γ(A)) = ∫_A √(1 + ‖∇φ‖²)` with `n = dim V` in set, measure and integral form; the outward unit normal | ✅ | ✗ | `Domains/Lipschitz/LipschitzGraphArea` |
| The surface measure of a bounded Lipschitz domain as `μHE[n-1]` on the boundary, its chart form, finiteness and null sets, the boundary `Γ` as a Lebesgue null set, the boundary trace in `L_p(Γ)`, `L_2(Γ)` with the traces of `H^s(Ω)` and of its trace space for `1/2 < s < 3/2`, the traces of `H^s(ℝ^d)` in `B^{s-1/2}_{2,2}(Γ)`, their vanishing on the trace kernel, and the outward unit normal field | ✅ | ✗ | `Domains/Lipschitz/SurfaceMeasure` |
| The norm of the trace space of `H^s(Ω)`, `1/2 < s < 3/2`: least extension norm, equivalence with the norm of `B^{s-1/2}_{2,2}(Γ)`, bounded preimages, the range of its trace in `L_2(Γ)`, the isomorphism with the Banach space `B^{s-1/2}_{2,2}(Γ)`, and the bounded linear right inverse of the trace | ✅ | ✗ | `Domains/Traces/TraceSpaceNorm` |
| The Sobolev–Slobodeckij norm on the boundary: Gagliardo's double integral for the surface measure, double integrals in the charts, the bounds by the chart-wise norm of `B^s_{p,p}(Γ)` in both directions, `W^{s,p}(Γ) = B^s_{p,p}(Γ)` for `0 < s < 1`, the norm of the trace space of `H^s(Ω)` as the Sobolev–Slobodeckij norm of `W^{s-1/2,2}(Γ)` | ✅ | ✗ | `Domains/Traces/BoundaryGagliardo` |
| The Hilbert space `H^t(Γ)` as `B^t_{2,2}(Γ)` with the chart-wise Gagliardo norm, its dual, the trace space of `H^s(Ω)` isomorphic to `H^{s-1/2}(Γ)`, the trace onto `H^{s-1/2}(Γ)` with a bounded linear right inverse, and its agreement with the Besov trace; the Gelfand triple `H^t(Γ) ⊂ L_2(Γ) ⊂ H^{-t}(Γ)`, `0 < t < 1`, with `H^t(Γ)` dense in `L_2(Γ)` | ✅ | ✗ | `Domains/Traces/BoundarySobolev` |
| Convolutions with sums of derivatives of dilated kernels, the local means of order two by the gradient, local means of Triebel–Lizorkin type on a set, the bounds of the local extension from one patch, bounded extensions from `L_p` bounds, pasting in `W^1_p(ℝ^d)`, the supports of the divergence kernels in the patches, the smooth cutoffs of the patches, dimension zero | ✅ | ✗ | `Domains/Extension/SobolevExtension` |
| Rychkov's extension operator for `W^1_p`, `1 < p < ∞`, on value–derivative jets with a finite constant, and from it the extension from one patch and the extension theorem for `1 < p < ∞` with a bound | ✅ | ✗ | `Domains/Extension/SobolevExtensionOperator` |
| The half-space and the reflection across a hyperplane, cutoffs near the hyperplane, integration by parts on the half-space, the linearity, weak derivatives and `L_p` bounds of the even reflection | ✅ | ✗ | `Domains/Extension/HalfSpaceReflection` |
| The flattening of a Lipschitz graph domain onto the half-space, the extension by reflection across the graph with its linearity, weak derivatives and `L_p` bounds, cutoffs from a bounded Lipschitz domain to its graph domains with the bounds of the patches | ✅ | ✗ | `Domains/Extension/ReflectionExtension` |
| Linear extensions of functions as extension operators on jets, the patches by reflection as linear extensions, the chosen extension operator for `W^1_p`, `1 ≤ p ≤ ∞`, built by reflection on value–derivative jets, `E u = u` on `Ω`, and from it the extension theorem for `W^1_p` on bounded Lipschitz domains for `1 ≤ p ≤ ∞` with a bound | ✅ | ✗ | `Domains/Extension/ReflectionExtensionOperator` |
| Weighted dilation averages `∫_a^b w(s) G_{e^s} ds`, their writing as sums of derivatives of order `m` of the higher divergence kernels when the weight has vanishing moments, the smoothed bump with its moment and kernel weights, and the local means kernels of order `L` as sums of derivatives of order `m ≤ L` of the higher divergence kernels, which have mean zero for `m < L` and lie in the reflected cone for bumps supported in `-K` | ✅ | ✗ | `Domains/Extension/HigherDivergenceKernels` |
| The local means of order `m + 1` of the smoothed bump by the derivatives of order `m`, local means of Triebel–Lizorkin type with smoothness `m` on a set, bounded extensions of order `m` from one patch and by a cutoff, pasting in `W^m_p(ℝ^d)` by the Leibniz rule, and the extension theorem (`W^m_p(Ω)` is the space of restrictions of `W^m_p(ℝ^d)`) on bounded Lipschitz domains for `1 < p < ∞` and every `m`, with a bound | ✅ | ✗ | `Domains/Extension/HigherSobolevExtension` |
| `W^1_p(Ω)` as the space of restrictions of `W^1_p(ℝ^d)` for `1 ≤ p ≤ ∞` (the extension theorem), and for `p = 2` `H^1(Ω) = W^1_2(Ω)`, Rellich's theorem in `W^1_2(Ω)`, the quotient norm of `H^1(Ω)` and the boundary traces of `W^1_2(Ω)` | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainW1p` |
| Gauss–Green on Lipschitz graph domains: Fubini in product coordinates, ray integrals, the normal weight, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` for compactly supported `C^1` functions in chart and surface form, the product rule for line derivatives, and Green's formula `∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)` | ✅ | ✗ | `Domains/Sobolev/LipschitzGraphGreen` |
| Green's formula on bounded Lipschitz domains: integration by parts in `H^1(ℝ^d)`, resolutions of unity equal to one near the boundary, the chart form for every resolution of unity, the outward unit normal as the chart normal and a unit vector almost everywhere on the boundary, `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` for `u, w ∈ H^1(Ω)`, the traces from both sides of a graph, and the zero extension: `1_Ω u ∈ W^1_2(ℝ^d)` iff the trace of `u` vanishes | ✅ | ✗ | `Domains/Sobolev/LipschitzDomainGreen` |
| The kernel of the trace: convergence and mollification in `H^1(ℝ^d)`, `H̃^1(Ω)` as the functions of `H^1(ℝ^d)` vanishing outside `Ω`, `H^s_0(Ω) ⊆ ker γ_s` for `1/2 < s < 3/2`, `ker γ = H^1_0(Ω)` for the trace of `H^1(Ω)`, `H̃^1(Ω) ≅ ker γ` and `(ker γ)^* ≅ H^{-1}(Ω)`; the trace of `H^s(ℝ^d)` under the inclusions, the extension from the boundary into `H^s(ℝ^d)` with a bound, and `ker γ_s = H^s_0(Ω)` for `1/2 < s ≤ 1` | ✅ | ✗ | `Domains/Traces/TraceKernel` |
| Bounded Lipschitz domains from the set-level definition: sets Lipschitz near a point, local graphs as Lipschitz graph domains, McShane's extension of local graphs, the structure from a family of charts and the converse, the ball | ✅ | ✗ | `Domains/Lipschitz/LocalLipschitzGraphs` |
| Bounded open convex sets as bounded Lipschitz domains: the ray length, its cone estimate, open convex sets, bounded or not, near a frontier point as regions above a Lipschitz graph, and the open unit cube with its closure | ✅ | ✗ | `Domains/Lipschitz/ConvexDomains` |
| Lipschitz graph domains with null graphs and boundaries, closures of convex Lipschitz graph domains as Besov domains, the quadrant as a Lipschitz graph domain and the quadrant model of manifolds with corners as a Besov domain, bounded Lipschitz domains with the extension property, closures of nonempty convex bounded Lipschitz domains and of nonempty bounded open convex sets, closed balls of positive radius and the closed unit cube as Besov domains | ✅ | ✗ | `Domains/Lipschitz/BesovDomains` |
| Functions vanishing outside a ball on a Besov domain: the interior up to a null set, the bounded convex pieces `interior Ω ∩ B(0, R)`, the cutoff identity, the intrinsic quasi-norm through the pieces, and `W^1_2 = B^1_{2,2}` on the interior | ✅ | ✗ | `Domains/Lipschitz/BesovDomainLocalisation` |
| Splines on domains through restriction: agreement of cut-offs on subsets and under affine maps; the cube `a + L [0, 1]^d` with its transported tensor splines and their approximation spaces; functions of finite intrinsic quasi-norm on a measurable subset of a cube with the extension property as restrictions of the tensor spline space of the cube, with a bound, for every order of the differences and in block form; bounded Lipschitz domains; the unit cube (restrictions of `B^s_{p,q}(ℝ^d)`); the restricted tensor splines on `Ω` and their Jackson estimate | ✅ | ✗ | `Domains/Lipschitz/SplinesOnDomains` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
