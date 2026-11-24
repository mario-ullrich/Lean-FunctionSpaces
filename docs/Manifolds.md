# Manifolds and eigenbases

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Domains, traces and
manifolds*, chapters *Eigenbases of the Laplacian*, *Besov spaces on compact manifolds* and
*Eigenfunction expansions on compact manifolds*.

The domains and traces used here are in [Lipschitz domains and traces](DomainsTraces.md). Compact
manifolds with boundary or with corners carry Besov spaces in the charts of a Besov atlas, since the
half-space and the quadrant are Besov domains; the invariance under changes of variables makes them
independent of the atlas, and for manifolds with boundary the trace theorem of the half-space
carries over to the boundary for every `s > 0`. Smooth bounded domains are such manifolds, and their
chart spaces are the intrinsic Besov spaces. In finite dimension the smooth bounded domains are the
sets of the usual definition by smooth local graphs, the open balls among them.

On a bounded open set the embedding `H^1_0(Ω) → L_2(Ω)` is compact with dense range, and its
singular basis gives the eigenbasis of the Dirichlet Laplacian as a spectral scheme, with the weak
eigenvalue equation; `H^1_0(Ω)` is the Sobolev space of order `1` of this scheme, and the real
interpolation spaces between `L_2(Ω)` and `H^1_0(Ω)` are its approximation spaces. On a bounded
Lipschitz domain the same holds for `W^1_2(Ω)`, the graph of the weak gradient in
`L_2(Ω) × L_2(Ω)^n`: Rellich's theorem through the extension theorem makes `W^1_2(Ω) → L_2(Ω)`
compact, and its singular basis is the eigenbasis of the Neumann Laplacian, with the eigenvalue `0`
of the constants. There the Besov space `B^θ_{2,q}(Ω)`, `0 < θ < 1`, defined by intrinsic
differences, is the approximation space of the Neumann eigenbasis; on a bounded open set the zero
extension maps the approximation spaces of the Dirichlet eigenbasis into `B^θ_{2,q}(ℝ^d)`. On every
compact manifold of positive dimension, without boundary, with boundary or with corners, the chart
Sobolev space `H^1_A(M) = B^1_{2,2}(M)` embeds compactly and densely into `L_2(μ)`, and the
eigenvector basis `e_i = J φ_i` of the embedding is an eigenbasis of the chart form whose
approximation spaces are `B^θ_{2,q}(M)`, `0 < θ < 1`.

## Main results

* **Besov spaces on compact manifolds.** Let `M` be a compact smooth manifold modelled on `E` with
  corners `I` whose range is a Besov domain (the half-space, the quadrant of manifolds with
  corners, or `E`), `μ` a smooth measure (in every chart a continuous positive density with
  respect to the Lebesgue measure, `Manifold.IsSmoothMeasure`) and `1 ≤ p < ∞`. A Besov atlas
  consists of finitely many charts `κ_i`, a smooth partition of unity `ψ_i` subordinate to them and
  cut-offs (`Manifold.BesovAtlas`); every compact Hausdorff manifold has one
  (`Manifold.BesovAtlas.nonempty`). Its chart measure
  `μ_A = ∑_i (κ_i⁻¹)_* (ψ_i ∘ κ_i⁻¹ · vol|_{T_i})`, with `T_i = κ_i(e_i.source)` the target of
  the extended chart (`Manifold.BesovAtlas.chartMeasure`), has the density
  `∑_i |det DΦ_i| ψ_i ∘ κ⁻¹` in every chart `κ`, `Φ_i = κ_i ∘ κ⁻¹`, so it is a finite smooth
  measure (`Manifold.BesovAtlas.isSmoothMeasure_chartMeasure`), and every compact Hausdorff
  manifold, with or without boundary, carries one (`Manifold.exists_isSmoothMeasure`), for
  example the sphere (`Manifold.exists_isSmoothMeasure_sphere`). The Besov quasi-norm of a Besov
  atlas `A` is `‖f‖_{A,r,s,q} = ∑_i N_Ω((ψ_i f) ∘ κ_i⁻¹)` with
  `N_Ω(G) = ‖G‖_{L_p(Ω)} + ‖(2^(ks) ω_r(G, 2^(-k), Ω)_p)_k‖_{ℓ_q}`, `Ω = range I`
  (`Manifold.BesovAtlas.atlasBesovNorm`). For two Besov atlases, `0 < s < r` and `1 ≤ q ≤ ∞` there
  is `C < ∞` with `‖f‖_{A,r,s,q} ≤ C ‖f‖_{A',r,s,q}` for all `f ∈ L_p(μ)`
  (`Manifold.BesovAtlas.atlasBesovNorm_le_atlasBesovNorm`), so `B^s_{p,q}(M)`
  (`Manifold.MemManifoldBesov`) depends neither on the atlas nor on the order
  (`Manifold.memManifoldBesov_iff`, `Manifold.BesovAtlas.memAtlasBesov_iff_atlasBesovNorm_lt_top`).
  The pieces of two atlases are related by the changes of charts with cut-offs
  (`Manifold.BesovAtlas.pieceLp_eq_sum`), which are bounded on the Besov domain.
* **Smooth bounded domains as manifolds with boundary.** The closure of a smooth bounded domain
  `Ω ⊆ ℝ^n` (a bounded Lipschitz domain with smooth graph functions, `Rd.SmoothDomain`) is a
  compact smooth manifold with boundary modelled on the half-space `{y : y_0 ≥ 0}`
  (`Rd.SmoothDomain.isManifold`): near the boundary the charts are the straightenings
  `x ↦ A(x - φ(x) e)`, which preserve the Lebesgue measure
  (`Rd.LipschitzGraph.measurePreserving_graphFlatten`), so the Lebesgue measure is a
  smooth measure (`Rd.SmoothDomain.isSmoothMeasure_volumeOn`). For `1 ≤ p < ∞`, `0 < s < r` and
  `1 ≤ q ≤ ∞`, `f ∈ L_p(closure Ω)` lies in the Besov space `B^s_{p,q}` of this manifold iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
  (`Rd.SmoothDomain.memManifoldBesov_iff_modNormOn_lt_top`): the descriptions by charts, by
  intrinsic differences and as restrictions of `B^s_{p,q}(ℝ^n)` coincide. `Rd.SmoothDomain` carries
  its charts as data; its carriers are exactly the bounded open sets that agree near each boundary
  point with the region above the graph of a function smooth near the origin
  (`Rd.IsBoundedSmoothDomain`, `Rd.isBoundedSmoothDomain_iff_exists`), each such set carries the
  smooth domain `Rd.SmoothDomain.ofIsBoundedSmoothDomain`, and every open ball is such a set
  (`Rd.SmoothDomain.ball`, with its Besov spaces in `Rd.SmoothDomain.memManifoldBesov_ball_iff`).
* **Besov spaces on the boundary of a compact manifold.** Let `M` be a compact smooth manifold
  with boundary modelled on the half-space `{y ∈ ℝ^n : y_0 ≥ 0}`. The changes of charts map the
  boundary hyperplane `H₀ = {y_0 = 0}` into itself (`Manifold.coordChange_mem_bdry`), and their
  restrictions to `H₀` are smooth changes of variables with cut-offs on all of `H₀`
  (`Manifold.boundaryChartChange`). For a Besov atlas `A`, `g : M → ℂ` lies in `B^s_{p,q}(∂M)`
  (`Manifold.BesovAtlas.MemAtlasBoundaryBesov`) if the restrictions to `H₀` of its chart pieces
  agree almost everywhere with functions in `B^s_{p,q}(H₀)`. For `1 ≤ p < ∞`, `s > 0` and
  `1 ≤ q ≤ ∞` this does not depend on the atlas
  (`Manifold.BesovAtlas.memAtlasBoundaryBesov_iff_memAtlasBoundaryBesov`).
* **The trace theorem on compact manifolds with boundary.** With `M` as above, a smooth measure `μ`,
  `1 ≤ p < ∞`, `s > 0`, `1 ≤ q ≤ ∞` and the trace `Tr` of order `L ≥ 2`, `L > s + 1/p`, of the
  half-space, the trace of `f ∈ L_p(μ)` on `∂M` is
  `Tr_A f = ∑_i θ_i · Tr((ψ_i f) ∘ κ_i⁻¹) ∘ P ∘ κ_i` (`Manifold.BesovAtlas.atlasBoundaryTrace`). The
  trace commutes with the changes of charts
  (`Manifold.graphTrace_chartChange_applyLp`), so for `f ∈ B^{s+1/p}_{p,q}(M)` the boundary pieces
  of `Tr_A f` are the traces of the chart pieces of `f`, for every atlas
  (`Manifold.BesovAtlas.boundaryPiece_atlasBoundaryTrace_of_atlas`). The trace is bounded: there is
  `C < ∞` such that every boundary piece of `Tr_A f` agrees almost everywhere with some
  `G ∈ L_p(H₀)` with `‖G‖_p + ‖(2^(js) ω_{⌊s⌋+1}(G, 2^(-j))_p)_j‖_{ℓ_q} ≤ C ‖f‖_{A,L,s+1/p,q}`
  (`Manifold.BesovAtlas.exists_atlasBoundaryTrace_norm_le`). `B^s_{p,q}(∂M)` is the trace space
  of `B^{s+1/p}_{p,q}(M)`: `g ∈ B^s_{p,q}(∂M)` iff the boundary pieces of `g` agree almost
  everywhere with those of `Tr_A f` for some `f ∈ B^{s+1/p}_{p,q}(M)`
  (`Manifold.BesovAtlas.memAtlasBoundaryBesov_iff_exists_atlasBoundaryTrace`). If `f` has a
  continuous representative `g`, the boundary pieces of `Tr_A f` are those of `g`: the trace is the
  restriction to the boundary
  (`Manifold.BesovAtlas.boundaryPiece_atlasBoundaryTrace_of_continuous`). For the closure of a
  smooth bounded domain with the Lebesgue measure this is the trace theorem for the Besov spaces of
  its boundary defined by charts, for every `s > 0`
  (`Rd.SmoothDomain.smooth_memAtlasBoundaryBesov_iff_exists_atlasBoundaryTrace`,
  `Rd.SmoothDomain.smooth_boundaryPiece_atlasBoundaryTrace_of_continuous`).
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
  (`Rd.BoundedLipschitzDomain.exists_lpModulusOn_le_inclKFunctional`), with
  `ω_r(ι U, 2^(-k))_2 ≤ 2^(r-1) 2π 2^(-k) ‖U‖` for `U ∈ H^1(V)` (`Rd.lpModulus_toL2_le`), and
  restricts `(L_2(V), H^1(V))_{θ,q} = B^θ_{2,q}(V)` to `Ω`
  (`Rd.memKMethod_neumann_restrict_of_memKMethod`).
* **Eigenfunction expansions on compact manifolds.** Let `M` be a compact manifold whose model
  range `Ω_I` is a Besov domain, of dimension `n ≥ 1`, with a smooth measure `μ`, a Besov atlas
  `A` with pieces `P_k` and lifts `L_k`, and `J : H^1_A(M) → L_2(μ)` the chart Sobolev embedding.
  `J = ∑_k L_k E_k J^N_k T_k` through the Neumann embeddings `J^N_k` of the bounded convex pieces
  `D_k = O_I ∩ B(0, R_k + 1)` (`Manifold.BesovAtlas.chartSobolevEmbedding_eq_sum`), so `J` is
  compact (`Manifold.BesovAtlas.isCompactOperator_chartSobolevEmbedding`); its range is dense
  (`Manifold.BesovAtlas.denseRange_chartSobolevEmbedding`), and for a Hausdorff `M` it is
  `B^1_{2,2}(M)` (`Manifold.BesovAtlas.mem_range_chartSobolevEmbedding_iff`). Its spectral scheme
  (`Manifold.BesovAtlas.chartScheme`) is a Hilbert basis `(e_i)` of `L_2(μ)` with eigenvalues
  `λ_i = σ_i⁻² - 1 ≥ 0` (`Manifold.BesovAtlas.chartEigenvalue_nonneg`), finitely many below each
  bound, and eigenfunctions `φ_i ∈ H^1_A(M)`, `J φ_i = e_i`, with
  `a_A(φ_i, w) = λ_i ⟨e_i, J w⟩` for every `w ∈ H^1_A(M)`
  (`Manifold.BesovAtlas.chartForm_eigenfunction`), the weak eigenvalue equation of the chart form
  with the natural boundary condition. In the principal part `∑_k (ψ_k ∘ κ_k⁻¹)² |∇(u ∘ κ_k⁻¹)|²`
  of the chart form the weights satisfy `∑_k ψ_k² ≥ 1/N` for `N` charts
  (`Manifold.BesovAtlas.inv_card_le_sum_sq_psi`), a step toward its uniform
  ellipticity in the charts. `f ∈ B^1_{2,2}(M)` iff
  `∑_i (1 + ⌊√(1 + λ_i)⌋)² |⟨e_i, f⟩|² < ∞`
  (`Manifold.BesovAtlas.memManifoldBesov_one_two_iff_spectral`). For `0 < θ < 1` and `1 ≤ q ≤ ∞`,
  `f ∈ (L_2(μ), H^1_A(M))_{θ,q}` iff every piece `P_k f` has a finite intrinsic quasi-norm on `Ω_I`
  (`Manifold.BesovAtlas.memKMethod_chartSobolev_iff`), so `f ∈ B^θ_{2,q}(M)` iff `f` lies in the
  approximation space `A^θ_q` of the chart eigenbasis
  (`Manifold.BesovAtlas.memApprox_chartScheme_iff`), iff
  `‖P_1 f‖_2 + ‖(2^(kθ) ‖Δ_k f‖_2)_k‖_{ℓ_q} < ∞` for the dyadic blocks `Δ_k f` of its eigenfunction
  expansion (`Manifold.BesovAtlas.memManifoldBesov_iff_blockNorm_lt_top`), and for `q = 2` iff
  `∑_i (1 + λ_i)^θ |⟨e_i, f⟩|² < ∞`
  (`Manifold.BesovAtlas.memManifoldBesov_two_iff_chartEigenvalue`). On the closure of a bounded
  smooth domain `Ω` these are the intrinsic `B^θ_{2,q}(Ω)`
  (`Rd.SmoothDomain.memApprox_chartScheme_iff_modNormOn`); the sphere `S^n`, `n ≥ 1`, with the chart
  measure of a Besov atlas is an example without boundary
  (`Manifold.memApprox_chartScheme_sphere_iff`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Smooth measures on manifolds (a continuous positive density in every chart), measurability of extended charts on their sources, integrals and `L_p` norms in charts, null sets in charts | ✅ | ✗ | `Domains/Manifolds/SmoothMeasure` |
| Besov atlases, `∑_i ψ_i² ≥ 1/N` for the partition of unity, chart pieces with their compact carriers and their continuity on the model range for continuous functions, images and measurable sources of changes of charts, changes of charts with cut-offs, lifts from a chart and their `L_p` bound | ✅ | ✗ | `Domains/Manifolds/BesovAtlas` |
| Smooth measures exist: the chart measure of a Besov atlas, its density in every chart by the Jacobian determinants of the changes of charts, continuity and positivity of the density, finiteness, every compact Hausdorff manifold with or without boundary carries a finite smooth measure (a continuous positive density in every chart), the sphere as an example without boundary | ✅ | ✗ | `Domains/Manifolds/SmoothMeasureExistence` |
| Besov spaces on compact manifolds, independence of the atlas and of the order, membership piece by piece, lifts from a chart | ✅ | ✗ | `Domains/Manifolds/Besov` |
| Smooth bounded domains as compact manifolds with boundary, Lebesgue measure as smooth measure | ✅ | ✗ | `Domains/Manifolds/SmoothDomain` |
| Besov spaces of smooth domains by charts equal the intrinsic Besov spaces | ✅ | ✗ | `Domains/Manifolds/SmoothDomainBesov` |
| Besov spaces on the boundary of a compact manifold, independence of the atlas | ✅ | ✗ | `Domains/Manifolds/BoundaryBesov` |
| Trace theorem on compact manifolds: commutation with charts, the quasi-norm bound, trace space, the trace of a continuous function as its restriction, and the closures of smooth bounded domains | ✅ | ✗ | `Domains/Manifolds/BoundaryTrace` |
| The chart Sobolev space of a compact manifold with or without boundary: the open model set, pieces and lifts as bounded operators, the retract identity `∑_k L_k P_k = id`, the graph space of the weak gradients of the pieces on the open model set, the chart form, the embedding into `L_2(μ)`, and `H^1_A(M) = B^1_{2,2}(M)` for every Besov atlas | ✅ | ✗ | `Domains/Manifolds/ChartSobolev` |
| The Dirichlet Laplacian on bounded open sets: the polarization of a norm identity, the inner product of `H^1(ℝ^d)` by the weak gradient, the compact dense embedding `H^1_0(Ω) → L_2(Ω)`, the Dirichlet eigenbasis as a spectral scheme with eigenvalues `λ_i ≥ 0`, the weak eigenvalue equation, `H^1_0(Ω)` as the Sobolev space of order `1` of the scheme, and `(L_2(Ω), H^1_0(Ω))_{θ,q} = A^θ_q` | ✅ | ✗ | `Domains/Spectral/DirichletEigenbasis` |
| The Neumann Laplacian on bounded Lipschitz domains: `W^1_2(Ω)` as the graph of the weak gradient in `L_2(Ω) × L_2(Ω)^n` and as jets, the dense embedding into `L_2(Ω)` through `H^1_0(Ω)`, Rellich's theorem with bounded `H^1(Ω)` representatives, the Neumann eigenbasis as a spectral scheme with eigenvalues `λ_i = σ_i⁻² - 1 ≥ 0`, among them `0`, the weak eigenvalue equation, `W^1_2(Ω)` as the Sobolev space of order `1` of the scheme, and `(L_2(Ω), W^1_2(Ω))_{θ,q} = A^θ_q` | ✅ | ✗ | `Domains/Spectral/NeumannEigenbasis` |
| Besov spaces on domains by eigenfunction expansions: the intrinsic modulus by the K-functional of `(L_2(Ω), W^1_2(Ω))`, `B^θ_{2,q}(Ω)` for `0 < θ < 1` as the approximation space of the Neumann eigenbasis on bounded Lipschitz domains, in dyadic blocks and for `q = 2` by the eigenvalues, and the Dirichlet approximation spaces in `B^θ_{2,q}(ℝ^d)` by zero extension | ✅ | ✗ | `Domains/Spectral/SpectralBesov` |
| The eigenbasis of the chart form on a compact manifold with or without boundary: the bounded convex piece of each chart, the jets of the pieces in its Neumann space, Rellich's theorem `J = ∑_k L_k E_k J^N_k T_k` compact, dense range by lifts of `H^1(E)` functions, the chart scheme with eigenvalues `λ_i = σ_i⁻² - 1 ≥ 0`, levels `⌊√(1 + λ_i)⌋₊` and finitely many eigenvalues below each bound, the weak eigenvalue equation `a_A(φ_i, w) = λ_i ⟨e_i, J w⟩` with the natural boundary condition, and `H^1(M) = B^1_{2,2}(M)` in the eigenbasis | ✅ | ✗ | `Domains/Spectral/ChartFormEigenbasis` |
| Besov spaces on compact manifolds by eigenfunction expansions of the chart form: the pieces map `(L_2(μ), H^1_A(M))` into the Neumann couples of the bounded convex pieces, the lifts `H^1(E) → H^1_A(M)` by the closed graph theorem map `(L_2(E), H^1(E))` into it, `(L_2(μ), H^1_A(M))_{θ,q}` by the pieces, `B^θ_{2,q}(M)` for `0 < θ < 1` as the approximation space of the chart eigenbasis, in dyadic blocks and for `q = 2` by the eigenvalues, closures of smooth domains and the closed ball as examples with boundary, and the sphere with the chart measure of an atlas as an example without boundary | ✅ | ✗ | `Domains/Spectral/ManifoldSpectralBesov` |
| Smooth bounded domains from the set-level definition: sets smooth near a point, the smooth cut-off of a local graph, the smooth domain from smooth charts and the converse, the ball as a smooth domain and the Besov spaces of its closure | ✅ | ✗ | `Domains/Manifolds/SmoothLocalGraphs` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
