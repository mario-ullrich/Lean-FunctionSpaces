# Sobolev spaces on `ℝ^d`

Part of [Function spaces via approximation](../README.md). Blueprint chapters: *Sobolev spaces on
`ℝ^d`*.

This block develops the Sobolev spaces `W^m_p` defined by weak derivatives. A weak derivative is
an identity between distributions on an open set, in Mathlib's distributions `𝓓'(Ω, ℂ)`; on the
whole space and for `L_p` functions it is an identity between tempered distributions `𝓢'(V, ℂ)`,
where Mathlib's Fourier transform and Bessel potential spaces live. For `p = 2` it identifies
Mathlib's Bessel potential spaces `H^s`, `s ≥ 0`, with the Triebel–Lizorkin spaces `F^s_{2,2}`
(and, for `s > 0`, with the Besov spaces `B^s_{2,2}`) and shows `W^1_2 = H^1 = B^1_{2,2}`. On a
bounded Lipschitz domain, `H^1` is the space of restrictions of `H^1(ℝ^d)`, with weak derivatives
in `L_2` of the domain and boundary traces in `B^{1/2}_{2,2}` of the boundary. On every bounded
set the restriction from `H^1(ℝ^d)` to `L_2` is compact (Rellich's theorem). On every open set
the Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)`, for real `s`, are built inside Mathlib's
`H^s(ℝ^d)`, with the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`. On a bounded Lipschitz domain the trace
space `H^{1/2}(Γ)` is the orthogonal complement of the trace kernel in `H^1(Ω)`, a Hilbert space
with trace and extension operators of norm at most `1`, and `H^{-1/2}(Γ)` is its dual. On a
Lipschitz graph domain the area formula expresses Mathlib's Euclidean Hausdorff measure of the
boundary in the chart, with the Gram density `√(1 + ‖∇φ‖²)`. On a bounded Lipschitz domain the
surface measure is this Hausdorff measure on the boundary `Γ`; it gives the space `L_2(Γ)`, into
which `H^1(Ω)` and `H^{1/2}(Γ)` have bounded trace operators. The outward unit normal field is
pasted from the chart normals. The theory for `1 < p < ∞` starts with families of dilated
Schwartz kernels with their Fourier overlap and Hörmander condition, the adjoint of a
convolution, which moves kernels and their derivatives to the other side of an integral, the
`L_2` bounds of the analysis and synthesis operators of every kernel family with bounded Fourier
overlap, and the Calderón–Zygmund decomposition of functions with values in a normed space, and
of families of them, into a bounded good part and bad pieces with mean zero on dyadic cubes.
With these, the analysis and synthesis operators of every Calderón–Zygmund family are of weak
type `(1,1)`.
The [interface document](FEECInterface.md) lists the results for `p = 2` for a FEEC/BEEC library
built on this project, with the decisions behind their form.

## Main results

* **Weak derivatives on open sets.** Let `V` be a finite-dimensional real inner product space,
  such as `ℝ^d`, with Lebesgue measure, `Ω ⊆ V` open, and `v = (v_0, …, v_{k-1})` directions in
  `V` with the iterated directional derivative `∂^v = ∂_{v_0} ⋯ ∂_{v_{k-1}}`. A locally
  integrable `g` is the weak derivative `∂^v f` of a locally integrable `f` on `Ω` if
  `∂^v f = g` as distributions on `Ω` (`Rd.HasWeakLineDeriv`), that is, iff
  `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every smooth compactly supported real `φ` in `Ω`
  (`Rd.hasWeakLineDeriv_iff_integral`). The weak derivative is unique almost everywhere on `Ω`
  (`Rd.HasWeakLineDeriv.unique`), linear, local (`Rd.HasWeakLineDeriv.mono`), the classical
  derivative on Schwartz functions (`Rd.hasWeakLineDeriv_schwartz`), and stable under limits in
  `L_p(Ω) × L_r(Ω)` for `1 ≤ p, r ≤ ∞` (`Rd.HasWeakLineDeriv.of_tendsto`).
* **Sobolev spaces.** For `m ∈ ℕ` and `1 ≤ p ≤ ∞`, `W^m_p(Ω)` consists of the `f ∈ L_p(Ω)` whose
  weak derivatives `∂^v f` of every order `k ≤ m` in all directions exist on `Ω` and lie in
  `L_p(Ω)` (`Rd.MemWeakSobolev`); `W^0_p(Ω) = L_p(Ω)` (`Rd.memWeakSobolev_zero_iff`), the spaces
  decrease in `m` and restrict to smaller open sets (`Rd.MemWeakSobolev.mono_order`,
  `Rd.MemWeakSobolev.mono_set`). For `f ∈ L_p(V)`, `f ∈ W^m_p(V)` is the case `Ω = V`
  (`Rd.MemSobolev`), and Schwartz functions lie in every `W^m_p(V)` (`Rd.memSobolev_toLp`).
* **The bridge to tempered distributions.** For `f ∈ L_p(V)` and `g ∈ L_r(V)`,
  `1 ≤ p, r ≤ ∞`, `g` is the weak derivative `∂^v f` on `V` iff `∂^v f = g` as tempered
  distributions (`Rd.hasWeakLineDeriv_top_iff`); hence `f ∈ W^m_p(V)` iff every tempered
  derivative `∂^v f` of order at most `m` is an `L_p(V)` function (`Rd.memSobolev_iff_tempered`).
  The proof uses that a tempered distribution vanishing on all test functions is zero
  (`Rd.eq_zero_of_testSchwartz`), because the cut-offs `x ↦ χ(x/(N+1)) u(x)` of a Schwartz
  function `u` converge to `u` in the Schwartz space, with every seminorm of the difference at
  most `C/(N+1)` for an explicit `C` (`Rd.seminorm_sub_cutoffMul_le`, `Rd.tendsto_cutoffMul`).
  On the way, directional derivatives of Schwartz functions and of test functions commute
  (`SchwartzMap.lineDerivOp_comm`, `TestFunction.lineDerivOp_comm`), so iterated derivatives of
  distributions satisfy `∂^v T(φ) = (-1)^k T(∂^v φ)`
  (`Distribution.iteratedLineDerivOp_apply_apply`,
  `TemperedDistribution.iteratedLineDerivOp_apply_apply`).
* **Mathlib's `H^s` as a Triebel–Lizorkin space.** Mathlib's Sobolev space `H^s(V)` consists of
  the tempered distributions `u` whose Bessel potential `J_s u = 𝓕⁻¹(⟨ξ⟩^s 𝓕u)`,
  `⟨ξ⟩^s = (1 + ‖ξ‖²)^(s/2)`, is an `L_2(V)` function (`TemperedDistribution.MemSobolev s 2`).
  For `s ≥ 0`, `u ∈ H^s(V)` iff `u` is an `L_2(V)` function in the Triebel–Lizorkin space
  `F^s_{2,2}(V)` (`Rd.memSobolev_two_iff_memTriebelLizorkin`), and for `f, h ∈ L_2(V)` with
  `J_s f = h`, `‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖h‖_2` and
  `‖h‖_2 ≤ (2 · 5^s)^{1/2} ‖f‖_{F^s_{2,2}}`
  (`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`,
  `Rd.enorm_besselPotential_le_triebelLizorkinNorm`). For `s > 0`, `H^s(V)` is the Besov space
  `B^s_{2,2}(V)`, the approximation space of the band-limited classes
  (`Rd.memSobolev_two_iff_exists_memApprox`). For `s ≥ 0`, every element `F` of the bundled
  space `H^{s}(V)` is an `L_2(V)` function `f ∈ F^s_{2,2}(V)` with
  `‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖F‖` (`Rd.exists_eq_toDistr_two`). The proof is
  Plancherel's theorem: the convolution theorem `𝓕(K ⋆ f) = 𝓕K · 𝓕f` on `L_2(V)` for integrable
  `K` (`Rd.fourier_convLp`), and, at every frequency, at most two Littlewood–Paley blocks whose
  Fourier transforms add up to `1` (`Rd.exists_fourier_psi_window`), so that
  `∑_j 2^(2js) |𝓕ψ_j(ξ)|² ≤ 2 · 4^s ⟨ξ⟩^{2s}` and `⟨ξ⟩^{2s} ≤ 2 · 5^s ∑_j 2^(2js) |𝓕ψ_j(ξ)|²`
  (`Rd.tsum_dyadicWeight_fourier_psi_sq_le`, `Rd.ofReal_besselWeight_sq_le_tsum`).
* **`W^1_2 = H^1`.** For `f ∈ L_2(V)`, `f ∈ W^1_2(V)` iff `f ∈ H^1(V)` (`Rd.memSobolev_one_iff`).
  If `g ∈ L_2(V)` is the weak derivative `∂_v f` and `J_1 f = h`, then `‖g‖_2 ≤ 2π ‖v‖ ‖h‖_2`
  (`Rd.enorm_le_of_hasWeakLineDeriv`); for the weak derivatives `g_i = ∂_{e_i} f` along any
  orthonormal basis `(e_i)`, `(2π)² ‖h‖_2² = (2π)² ‖f‖_2² + ∑_i ‖g_i‖_2²`
  (`Rd.enorm_besselPotential_one_sq_eq`), hence `‖h‖_2² ≤ ‖f‖_2² + ∑_i ‖g_i‖_2²`
  (`Rd.sq_norm_besselPotential_one_le`). For `F ∈ L_2(V)`, `F ∈ W^1_2(V)` iff `F` lies in the
  Besov space `B^1_{2,2}(V)`, the approximation space of the band-limited classes
  (`Rd.memSobolev_one_iff_memApprox`), iff
  `‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2} < ∞` for every order `r ≥ 2`
  (`Rd.memSobolev_one_iff_modulus`).
* **`H^1` on bounded Lipschitz domains.** Let `Ω` be a bounded Lipschitz domain with boundary
  `Γ`. `f ∈ L_2(V)` lies in `H^1(Ω)` if `f = F` almost everywhere on `Ω` for some
  `F ∈ W^1_2(V)` (`Rd.BoundedLipschitzDomain.MemSobolevOn`); `H^1(Ω)` contains `0`, is closed
  under sums and complex multiples, and depends only on the values on `Ω`. For every order
  `r ≥ 2`, `f ∈ H^1(Ω)` iff
  `‖f‖_{L_2(Ω)} + ‖(2^k ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞`, with the moduli of smoothness inside
  `Ω` (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_modulusOn`). Every `f ∈ H^1(Ω)` lies in
  `W^1_2(Ω)`: its weak derivatives on `Ω` exist and lie in `L_2(Ω)`
  (`Rd.BoundedLipschitzDomain.MemSobolevOn.memWeakSobolev`). For every resolution of unity on
  `Γ`, every `f ∈ H^1(Ω)` has a boundary trace in `B^{1/2}_{2,2}(Γ)`, unique almost everywhere
  on `Γ` (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memSobolevOn`,
  `Rd.BoundedLipschitzDomain.MemSobolevOn.isBoundaryTrace_unique`), and a function `g` lies in
  `B^{1/2}_{2,2}(Γ)` iff it is the boundary trace of some `f ∈ H^1(Ω)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_memSobolevOn`). The extensions in the
  definition of the boundary trace are the `F ∈ W^1_2(V)` with `F = f` on `Ω`
  (`Rd.BoundedLipschitzDomain.isBoundaryTrace_iff_forall_memSobolev`). The extension and trace
  theorems for bounded Lipschitz domains are qualitative, and so are these statements; the
  restriction direction has constant `1`
  (`Rd.BoundedLipschitzDomain.modNormOn_le_modNorm_of_ae_eq`).
* **Rellich's theorem.** For every bounded set `Ω ⊆ V`, of any shape, the restriction
  `F ↦ F|_Ω` from Mathlib's `H^1(V) = H^{1,2}(V, ℂ)` to `L_2(Ω)` is a compact operator
  (`Rd.isCompactOperator_restr_toL2`). Every bounded sequence in `H^1(V)` has a subsequence
  whose restrictions converge in `L_2(Ω)` (`Rd.exists_subseq_tendsto_restr`), and so has every
  sequence `f_n ∈ L_2(V)` with weak derivatives `∂_{e_i} f_n ∈ L_2(V)` along an orthonormal
  basis `(e_i)` and `‖f_n‖_2² + ∑_i ‖∂_{e_i} f_n‖_2² ≤ M²`
  (`Rd.exists_subseq_tendsto_restr_of_hasWeakLineDeriv`). The proof truncates in frequency:
  cutting `𝓕F` off to the ball `|ξ| ≤ K` changes `F` by at most `K⁻¹ ‖F‖_{H^1}` in `L_2(V)`
  (`Rd.norm_toL2_sub_truncL2_le`); the truncated functions are bounded by `|B_K|^{1/2}` and
  Lipschitz with constant `2πK |B_K|^{1/2}` on `V` for `‖F‖_{H^1} ≤ 1`
  (`Rd.norm_fourierInv_indicator_le`, `Rd.lipschitzWith_fourierInv_indicator`), so the
  Arzelà–Ascoli theorem on the compact closure of `Ω` (`Rd.totallyBounded_setOf_lipschitzWith`)
  makes the truncated operators compact (`Rd.isCompactOperator_restr_truncL2`). On the way, the
  `L_2` inverse Fourier transform of an integrable `h ∈ L_2(V)` is the pointwise inverse
  Fourier integral (`Rd.fourierInv_Lp_ae_eq_of_integrable`).
* **Sobolev spaces on open sets as Hilbert spaces.** Let `Ω ⊆ V` be open and `s` real. The
  elements of Mathlib's `H^s(V)` whose distribution vanishes on every test function of `Ω` form
  a closed subspace (`Rd.vanishOn`); for `s = 1` they are the elements vanishing almost
  everywhere on `Ω` (`Rd.mem_vanishOn_one_iff`). Its orthogonal complement is the Hilbert space
  `H^s(Ω)` (`Rd.RestrictionSpace`), and the restriction `U ↦ U|_Ω` is the orthogonal projection
  onto it (`Rd.restrictProj`). `H^s(Ω)` is isometric to the quotient of `H^s(V)` by the
  elements vanishing on `Ω` (`Rd.quotientEquivRestrictionSpace`), so `‖U|_Ω‖` is the minimum
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
  constant (`Rd.modNorm_two_le_norm`, `Rd.sobolevOneBesovConst`), and the `B^{1/2}_{2,1}`
  quantity is at most `√2` times this `B^1_{2,2}` quantity (`Rd.modNorm_half_one_le`), so
  `‖ι U‖_2 + ∑_k 2^(k/2) ω_2(ι U, 2^(-k))_2 ≤ √2 C ‖U‖` (`Rd.modNorm_half_one_le_norm`). Let
  `Ω` be a bounded Lipschitz domain with boundary `Γ` and `H^1(Ω)` the Hilbert space of the
  restriction space (`Rd.BoundedLipschitzDomain.SobolevOne`). The chart traces
  `u ↦ Tr_j(ψ_j u)` are bounded operators from `H^1(Ω)` to `L_2` of the hyperplanes of the charts
  (`Rd.BoundedLipschitzDomain.chartTrace`), and their common kernel, the trace kernel
  (`Rd.BoundedLipschitzDomain.traceKer`), consists of the `u` whose boundary trace vanishes
  almost everywhere on `Γ`, for every resolution of unity
  (`Rd.BoundedLipschitzDomain.mem_traceKer_iff`). Its orthogonal complement is the trace space
  `H^{1/2}(Γ)` (`Rd.BoundedLipschitzDomain.TraceSpace`), with the trace, the orthogonal
  projection, and the extension, the inclusion: `γ E = id`, `‖γ u‖ ≤ ‖u‖`, `‖E t‖ = ‖t‖`, the
  kernel of `γ` is the trace kernel, and `H^1(Ω) ⧸ ker γ ≅ H^{1/2}(Γ)` isometrically
  (`Rd.BoundedLipschitzDomain.trace_extend`, `Rd.BoundedLipschitzDomain.ker_trace`,
  `Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`). Two elements of `H^1(Ω)` have the same
  trace iff their boundary traces agree almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.trace_eq_iff`), and `t ↦ Tr_Γ(E t)` maps `H^{1/2}(Γ)` onto
  `B^{1/2}_{2,2}(Γ)` modulo null sets of `Γ`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_extend`,
  `Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`). `H^{-1/2}(Γ)` is the dual
  of the trace space (`Rd.BoundedLipschitzDomain.DualTraceSpace`), conjugate-linearly isometric
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
* **Dilation families and the Hörmander condition.** Let `(G_j)_{j ∈ ℕ}` be Schwartz functions
  on `V`, `dim V = n`, whose Schwartz seminorms `sup_x ‖x‖^k ‖D^l G_j(x)‖` are at most `A_{k,l}`
  for every `j` (`Rd.IsUniformSchwartz`), and `θ_j(x) = 2^(jn) G_j(2^j x)`. For every `y ∈ V`,
  `∫_{‖x‖ > 2‖y‖} ‖(θ_j(x - y) - θ_j(x))_j‖_{ℓ_2} dx ≤ 4 H_A` with an explicit constant `H_A`
  built from the bounds `A` (`Rd.lintegral_lqNorm_sub_le`, `Rd.familyHormanderConst`); the proof
  bounds each term by `H_A min(2^j ‖y‖, (2^j ‖y‖)⁻¹)`
  (`Rd.setLIntegral_enorm_dilate_sub_le_min`) and uses
  `∑_j min(2^j a, (2^j a)⁻¹) ≤ 4` for every `a ∈ [0, ∞]` (`ENNReal.tsum_min_two_pow_le`). A
  Calderón–Zygmund family with Fourier overlap `B` and Hörmander constant `H`
  (`Rd.IsCZFamily`) consists of integrable, continuous, bounded kernels `θ_j` with integrable
  Fourier transforms, `∑_j |𝓕θ_j(ξ)|² ≤ B` for every `ξ`, and the Hörmander integral at most `H`
  for every `y`; uniform dilation families with overlap `B` are such families with
  `H = 4 H_A` (`Rd.IsCZFamily.of_dilation`), and so are the adjoint kernels
  `θ_j^*(x) = conj θ_j(-x)` with the same `B` and `H` (`Rd.IsCZFamily.adjoint`). The
  Littlewood–Paley blocks `ψ_j` form such a family with overlap `2` (`Rd.isCZFamily_psi`), and so
  do the synthesis kernels `ψ̃_0 = Φ_1`, `ψ̃_1 = Φ_2`, `ψ̃_j = Φ_{j+1} - Φ_{j-2}` with overlap `4`
  (`Rd.psiDual`, `Rd.isCZFamily_psiDual`), which reproduce the blocks: `ψ̃_j ⋆ ψ_j = ψ_j`
  (`Rd.conv_psiDual_psi`).
* **The adjoint of a convolution.** For `K ∈ L_1(V)`, `f ∈ L_p(V)` and `g ∈ L_q(V)` with
  `1/p + 1/q = 1`, `p < ∞`, and the reflection `K^∨(x) = K(-x)` (`Rd.reflect`),
  `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)` (`Rd.integral_conv_mul`). For Schwartz functions `η`, `u`,
  `f ∈ L_p(V)`, `1 ≤ p < ∞`, and `w ∈ V^k`, `∫ ((∂^w η) ⋆ f) u = (-1)^k ∫ (η ⋆ f) ∂^w u`
  (`Rd.integral_conv_iteratedLineDerivOp_mul`). Weak derivatives commute with convolution by a
  Schwartz function `η`: if `g ∈ L_r(V)` is the weak derivative `∂^v f` of `f ∈ L_p(V)` on `V`,
  `1 ≤ p, r ≤ ∞`, then `η ⋆ g = (∂^v η) ⋆ f` at every point
  (`Rd.conv_eq_conv_iteratedLineDerivOp`), and `(∂^v η) ⋆ f` is the weak derivative
  `∂^v (η ⋆ f)` for `f ∈ L_p(V)`, `1 ≤ p < ∞` (`Rd.hasWeakLineDeriv_conv`).
* **Plancherel bounds.** For integrable kernels `θ_j` on `V` with `∑_j |𝓕θ_j(ξ)|² ≤ B` for
  almost every `ξ`, the analysis operator satisfies `∑_j ‖θ_j ⋆ f‖_2² ≤ B ‖f‖_2²` for every
  `f ∈ L_2(V)` (`Rd.tsum_enorm_convLp_sq_le`, `Rd.lintegral_lqNorm_conv_sq_le`), and the
  synthesis operator satisfies `‖∑_{j ∈ s} θ_j ⋆ g_j‖_2² ≤ B ∑_{j ∈ s} ‖g_j‖_2²` for all
  `g_j ∈ L_2(V)` and every finite set `s` (`Rd.enorm_sum_convLp_sq_le`,
  `Rd.lintegral_enorm_sum_conv_sq_le`); in particular for every Calderón–Zygmund family with
  overlap `B` (`Rd.IsCZFamily.lintegral_lqNorm_conv_sq_le`,
  `Rd.IsCZFamily.lintegral_enorm_sum_conv_sq_le`).
* **The signed Calderón–Zygmund decomposition.** Let `E` be a real normed space, such as `ℂ`,
  and `f : V → E`. For the maximal big dyadic cubes `Q` of a function `G : V → [0, ∞]` at height
  `t`, the good part `czGoodC f` is `f` outside the cubes and the mean `⨍_Q f` on each cube
  (`Rd.czGoodC`), and the bad part `f - czGoodC f` (`Rd.czBadC`) is the sum of the pieces
  `b_Q = 1_Q (f - ⨍_Q f)` (`Rd.czBadPart`, `Rd.hasSum_czBadPart`). Every piece has mean zero
  (`Rd.integral_czBadPart`), and `∑_Q ∫ ‖b_Q‖ ≤ 2 ∫ ‖f‖`
  (`Rd.tsum_lintegral_enorm_czBadPart_le`). If `n = dim V ≥ 1`, `f` is integrable, `t > 0` and
  `G = ‖f‖`, then `‖czGoodC f‖ ≤ 2^n t` almost everywhere and
  `∫ ‖czGoodC f‖² ≤ 2^n t ∫ ‖f‖` (`Rd.ae_enorm_czGoodC_le`, `Rd.lintegral_enorm_czGoodC_sq_le`).
  For a family `(g_j)_j` and `1 ≤ q ≤ ∞` the cubes of `G = ‖(‖g_j‖)_j‖_{ℓ_q}` serve every `g_j`,
  with the same bounds for the pointwise `ℓ_q` norms (`Rd.ae_lqNorm_czGoodC_le`,
  `Rd.lintegral_lqNorm_czGoodC_sq_le`, `Rd.tsum_lintegral_lqNorm_czBadPart_le`).
* **The weak type `(1,1)` of vector-valued singular integrals.** Let `n = dim V ≥ 1` and let
  `(θ_j)_j` be a Calderón–Zygmund family with overlap `B` and Hörmander constant `H`, and put
  `C = 4 · 2^n B + (2n)^n |B(0, 1)| + 4H` (`Rd.vectorWeakConst`). For every `0 < t < ∞` and
  every integrable `f : V → ℂ`, `|{x : ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} > t}| ≤ C t⁻¹ ∫ |f|`
  (`Rd.IsCZFamily.volume_lqNorm_conv_gt_le`), and for every finite set `s` and all almost
  everywhere strongly measurable `g_j` with `∫ ‖(g_j(x))_j‖_{ℓ_2} dx < ∞`,
  `|{x : |∑_{j ∈ s} (θ_j ⋆ g_j)(x)| > t}| ≤ C t⁻¹ ∫ ‖(g_j(x))_j‖_{ℓ_2} dx`
  (`Rd.IsCZFamily.volume_enorm_sum_conv_gt_le`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Test functions as Schwartz functions, commuting directional derivatives, the transpose formula for distributions and tempered distributions; cut-offs of Schwartz functions converge in the Schwartz space (smooth compactly supported functions are dense), tempered distributions determined by test functions | ✅ | ✗ | `Rd/SchwartzCutoff` |
| Weak derivatives and Sobolev spaces on open sets, integration by parts, uniqueness, locality, limits; the bridge to tempered distributions | ✅ | ✗ | `Rd/WeakDerivatives` |
| The convolution theorem and Plancherel for a convolution on `L_2`, the comparison of the Bessel weight with the Littlewood–Paley weights, Mathlib's `H^s` as `F^s_{2,2}` (`s ≥ 0`) and `B^s_{2,2}` (`s > 0`) with explicit constants, `W^1_2 = H^1 = B^1_{2,2}` | ✅ | ✗ | `Rd/SobolevTwoLittlewoodPaley` |
| `H^1` on bounded Lipschitz domains as restrictions of `H^1(ℝ^d)`, by intrinsic differences, the weak gradient, and the trace space `B^{1/2}_{2,2}` of the boundary | ✅ | ✗ | `Rd/LipschitzDomainH1` |
| The inverse Fourier transform of integrable `L_2` functions, band-limited functions as bounded Lipschitz functions, truncation in frequency, and Rellich's theorem: the restriction from `H^1(ℝ^d)` to `L_2(Ω)` is compact for bounded `Ω` | ✅ | ✗ | `Rd/RellichCompactness` |
| The Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` on open sets inside Mathlib's `H^s(ℝ^d)`, `H^s(Ω)` as a quotient, Rellich's theorem for `H^1(Ω)`, the identification with the restriction space of a bounded Lipschitz domain, and the isometry `H̃^1(Ω) ≅ H^1_0(Ω)` | ✅ | ✗ | `Rd/SobolevRestrictionSpaces` |
| The Bessel potential on Schwartz functions, the isometry `J_{2s} : H^s(ℝ^d) → H^{-s}(ℝ^d)`, the pairing of `H^{-s}` and `H^s`, and the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`, `(H^s(Ω))^* ≅ H̃^{-s}(Ω)`, `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` on open sets | ✅ | ✗ | `Rd/SobolevDuality` |
| `H^1(ℝ^d) ⊆ B^{1/2}_{2,1}(ℝ^d)` with explicit constants, the chart traces of `H^1(Ω)` on a bounded Lipschitz domain as bounded operators, the trace kernel, the trace space `H^{1/2}(Γ)` with trace and extension operators, `H^1(Ω) ⧸ ker γ ≅ H^{1/2}(Γ)`, and `H^{-1/2}(Γ)` | ✅ | ✗ | `Rd/BoundaryTraceSpace` |
| The area formula for Lipschitz graphs: Lipschitz maps and Mathlib's Euclidean Hausdorff measure, the linear case by Mathlib's norm determinant, stretches and tilts, the gradient and the Gram density, good pieces, `μHE[n-1](γ(A)) = ∫_A √(1 + ‖∇φ‖²)` with `n = dim V` in set, measure and integral form; the outward unit normal | ✅ | ✗ | `Rd/LipschitzGraphArea` |
| The surface measure of a bounded Lipschitz domain as `μHE[n-1]` on the boundary, its chart form, finiteness and null sets, the boundary `Γ` as a Lebesgue null set, the boundary trace in `L_p(Γ)`, `L_2(Γ)` with the traces of `H^1(Ω)` and `H^{1/2}(Γ)`, and the outward unit normal field | ✅ | ✗ | `Rd/SurfaceMeasure` |
| Dilation, reflection and conjugation of Schwartz functions, uniform Schwartz families, the Hörmander condition for dilation families with explicit constants, Calderón–Zygmund families and their adjoints, the Littlewood–Paley blocks and the synthesis kernels as such families | ✅ | ✗ | `Rd/DilationFamilies` |
| The adjoint identity `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)` for `f ∈ L_p`, `g ∈ L_q`, derivatives of Schwartz kernels moved to the other Schwartz factor, translates and reflections of Schwartz functions, and weak derivatives commuting with convolution by Schwartz functions | ✅ | ✗ | `Rd/ConvolutionAdjoint` |
| The Cauchy–Schwarz inequality for finite sums, the `L_2` bounds of the analysis operator and of the synthesis operators on finite index sets for a kernel family with Fourier overlap `B`, and for every Calderón–Zygmund family | ✅ | ✗ | `Rd/PlancherelBounds` |
| The signed Calderón–Zygmund decomposition of functions with values in a normed space and of families: good parts bounded by `2^n t` with `∫ ‖·‖² ≤ 2^n t ∫ ‖f‖`, bad pieces with mean zero on their cubes and total mass at most `2 ∫ ‖f‖` | ✅ | ✗ | `Rd/CalderonZygmundSigned` |
| Chebyshev's inequality for split functions, the Hörmander condition around a cube, convolutions of pieces with mean zero, and the weak type `(1,1)` of the analysis and synthesis operators of a Calderón–Zygmund family with an explicit constant | ✅ | ✗ | `Rd/VectorValuedWeakType` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
