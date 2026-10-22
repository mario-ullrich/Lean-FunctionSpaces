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
type `(1,1)`. Marcinkiewicz interpolation between weak type `(1,1)` and strong type `(2,2)`, in
the terms of the Carleson project, gives strong type `(p,p)` for `1 < p < 2`, and duality with
the adjoint family extends it to `2 < p < ∞`, for the analysis and the synthesis operators.
Applied to the Littlewood–Paley blocks and their synthesis kernels, this gives the square
function theorem `L_p = F^0_{p,2}` for `1 < p < ∞`. For `W^m_p`, the block `ψ_1` is a sum of
derivatives of order `m` of Schwartz kernels, whose dilates form Calderón–Zygmund families, and
so do the rescaled derivatives `2^{-jk} ∂^w ψ̃_j` of the synthesis kernels. With them,
`W^m_p = F^m_{p,2}` for `1 < p < ∞`, with explicit constants in both directions, and, for
`m ≥ 1`, `W^m_p` lies between the Besov spaces `B^m_{p,min(p,2)}` and `B^m_{p,max(p,2)}`.
The Littlewood–Paley blocks are continuous and satisfy the Nikolskii inequality, which gives the
embeddings of `B^s_{p,q}` into `L_r` for `s > n(1/p - 1/r)` and into bounded continuous functions
for `s > n/p`, and with `W^m_p ⊆ F^m_{p,2}` the Sobolev embeddings `W^m_p ↪ L_r` and
`W^m_p ↪ C_b`, all with explicit constants.
For the Bessel potential spaces, uniform Schwartz families stay uniform under continuous linear
maps of the Schwartz space, and the Bessel potential maps the dilates of every Schwartz function
to multiples of the dilates of its Bessel kernels; when the Fourier transform of the function
lives in an annulus, the Bessel kernels form a uniform Schwartz family and their dilates a
Calderón–Zygmund family. Applied to the Littlewood–Paley blocks and their synthesis kernels, this
gives, for `1 < p < ∞` and with existential constants, `H^{s,p} ∩ L_p = F^s_{p,2}` for every
real `s`, `H^{s,p} = F^s_{p,2}` for `s ≥ 0`, and Calderón's theorem `W^m_p = H^{m,p}`.
On a bounded Lipschitz domain, every function of `W^1_p(Ω)`, `1 < p < ∞`, is the restriction of
a function of `W^1_p(ℝ^d)` with a bounded extension, by Rychkov's local extension with the local
means of the gradient: the local means kernels of order two are divergences of dilated kernels
with mean zero, which form Calderón–Zygmund families. For `p = 2` this identifies `H^1(Ω)` with
`W^1_2(Ω)`.
On a Lipschitz graph domain, the Gauss–Green theorem `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` holds for
compactly supported `C^1` functions, and Green's formula
`∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)`, by the density of
the compactly supported Schwartz functions in every `H^s(ℝ^d)`.
On a bounded Lipschitz domain, Green's formula
`∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` holds for `u, w ∈ H^1(Ω)`, with
the trace `γ_{L_2} : H^1(Ω) → L_2(Γ)`, pasted from the
graph domains with a resolution of unity equal to one near the boundary; the outward unit normal
is the chart normal almost everywhere on the boundary, and the zero extension of `u ∈ H^1(Ω)` lies
in `W^1_2(ℝ^d)` iff the trace of `u` vanishes.
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
* **Marcinkiewicz interpolation.** With the Carleson project's definitions of weak type,
  strong type and almost everywhere subadditive operators (`MeasureTheory.HasWeakType`,
  `MeasureTheory.HasStrongType`, `MeasureTheory.AESubadditiveOn`): let `μ` be an s-finite
  measure, `ν` a measure and `1 < p < 2`. If an operator `T` is almost everywhere subadditive
  with constant `A` on `L_1(μ) ∪ L_2(μ)`, of weak type `(1,1)` with constant `C₁` and of strong
  type `(2,2)` with constant `C₂`, and maps `L_p(μ)` to almost everywhere strongly measurable
  functions, then it has strong type `(p,p)` with constant
  `(p (2 A C₁/(p - 1) + 4 A² C₂²/(2 - p)))^(1/p)`
  (`MeasureTheory.hasStrongType_of_hasWeakType_one_of_hasStrongType_two`). For operators on an
  abstract input type with a size `G x` and restrictions to measurable sets (such as families of
  functions with their pointwise `ℓ_2` norms) that are subadditive with constant `1`, satisfy
  `ν{T x > t} ≤ C₁ t⁻¹ ∫ G x dμ` and `∫ (T x)² dν ≤ C₂ ∫ (G x)² dμ`, the bound is
  `‖T x‖_{L_p(ν)} ≤ (p (2 C₁/(p - 1) + 4 C₂/(2 - p)))^(1/p) ‖G x‖_{L_p(μ)}`
  (`MeasureTheory.eLpNorm_le_of_weak_one_strong_two`).
* **The strong type of vector-valued singular integrals.** Let `n = dim V ≥ 1`, `1 < p < ∞`, and
  let `(θ_j)_j` be a Calderón–Zygmund family with overlap `B` and Hörmander constant `H`. With the
  explicit constant `S = S_{V,p}(B, H)` (`Rd.czConst`: `B^{1/2}` for `p = 2`, the Marcinkiewicz
  constant `(p (2 C/(p - 1) + 4B/(2 - p)))^(1/p)` with the weak type constant `C` above for
  `p < 2`, and that constant at the conjugate exponent `p/(p - 1)` for `p > 2`), every
  `f ∈ L_p(V)` satisfies `‖ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p ≤ S ‖f‖_p`
  (`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`), and for every finite set `s` and all `g_j ∈ L_p(V)`,
  `‖∑_{j ∈ s} θ_j ⋆ g_j‖_p ≤ S ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_p` (`Rd.IsCZFamily.eLpNorm_sum_conv_le`).
  For `p > 2` the norms are bounded through their pairings with `L_{p/(p-1)}`
  (`MeasureTheory.eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le`), tested on the norming
  family `u_j ‖(u_i)_i‖_{ℓ_2}^{p-2}` (`MeasureTheory.normingFamily`).
* **The square function theorem.** Let `n = dim V ≥ 1` and `1 < p < ∞`. For every `f ∈ L_p(V)`
  the square function `x ↦ ‖((ψ_j ⋆ f)(x))_j‖_{ℓ_2}` of the Littlewood–Paley blocks has `L_p`
  norm `‖f‖_{F^0_{p,2}}` (`Rd.triebelLizorkinNorm_zero_two_eq`), and
  `‖f‖_{F^0_{p,2}} ≤ Q_{V,p} ‖f‖_p` (`Rd.triebelLizorkinNorm_zero_two_le`) and
  `‖f‖_p ≤ Q̃_{V,p} ‖f‖_{F^0_{p,2}}` (`Rd.enorm_le_triebelLizorkinNorm_zero_two`) with the
  explicit constants `Q_{V,p} = S_{V,p}(2, 4 H_{A^ψ})` and `Q̃_{V,p} = S_{V,p}(4, 4 H_Ã)` of the
  Calderón–Zygmund families of the blocks and of the synthesis kernels
  (`Rd.squareFunctionConst`, `Rd.squareSynthesisConst`), where `A^ψ` and `Ã` are the seminorm
  bounds of the blocks and of the synthesis kernels (`Rd.psiBaseBound`, `Rd.psiDualBaseBound`).
  Hence `F^0_{p,2} = L_p(V)` (`Rd.triebelLizorkinSpace_zero_two_eq_top`). The lower bound uses
  the reproducing formula `∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f) → f` in `L_p(V)`
  (`Rd.tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub`).
* **Derivative kernels.** Let `e_0, …, e_{n-1}` be an orthonormal basis of `V` (`Rd.gridBasis`)
  and `m ∈ ℕ`. For every multi-index `α = (α_0, …, α_{m-1})` with entries below `n`, the
  derivative kernel `η_α` is the Schwartz function with Fourier transform
  `∏_k ⟪ξ, e_{α_k}⟫ / ((2πi)^m ‖ξ‖^{2m}) · 𝓕ψ_1(ξ)` (`Rd.derivSymbol`, `Rd.derivKernel`), and
  `ψ_1 = ∑_α ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} η_α` (`Rd.sum_iteratedLineDerivOp_derivKernel`), by
  `‖ξ‖^{2m} = ∑_α ∏_k ⟪ξ, e_{α_k}⟫²` (`Rd.norm_pow_eq_sum_prod_inner`). Dilated,
  `2^{jm} ψ_{j+1} = ∑_α ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} ((η_α)_{2^j})` for every `j`
  (`Rd.two_pow_smul_psi_succ_eq_sum`), and the dilates `((η_α)_{2^j})_j` form a
  Calderón–Zygmund family with overlap `2` (`Rd.isCZFamily_derivFamily`). For directions
  `w ∈ V^k`, `∂^w ψ̃_j = 2^{jk} (∂^w G̃_j)_{2^j}` with the Schwartz functions `G̃_j` behind the
  synthesis kernels (`Rd.iteratedLineDerivOp_psiDualS`), and the dilates `((∂^w G̃_j)_{2^j})_j`
  form a Calderón–Zygmund family with overlap `4 ((8π)^k ∏_l ‖w_l‖)²`
  (`Rd.isCZFamily_derivDualFamily`). On the way, `𝓕(∂^w G)(ξ) = ∏_l 2πi ⟪ξ, w_l⟫ 𝓕G(ξ)` for
  Schwartz functions `G` with values in a complex normed space
  (`SchwartzMap.fourier_iteratedLineDerivOp_apply`) and
  `∂^w (G_c) = c^k (∂^w G)_c` for the dilation `G_c(x) = c^n G(cx)`
  (`Rd.iteratedLineDerivOp_schwartzDilate`).
* **`W^m_p = F^m_{p,2}`.** Let `dim V ≥ 1`, `1 < p < ∞` and `m ∈ ℕ`. For `f ∈ L_p(V)`,
  `f ∈ W^m_p(V)` iff `f ∈ F^m_{p,2}(V)` (`Rd.memSobolev_iff_memTriebelLizorkin`), with explicit
  constants in both directions. If the weak derivatives
  `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the orthonormal basis `e` of `Rd.gridBasis` lie in
  `L_p(V)` for all multi-indices `α`, then
  `‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_{V,p,α} ‖g_α‖_p`
  (`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv`, `Rd.sobolevToTLConst`); if
  `f ∈ F^k_{p,2}(V)`, then for all directions `w ∈ V^k` the weak derivative `∂^w f` is a
  function `g ∈ L_p(V)` with `‖g‖_p ≤ C_{V,p,w} ‖f‖_{F^k_{p,2}}`
  (`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin`, `Rd.tlToSobolevConst`). The constants are
  strong type constants of the Calderón–Zygmund families of the dilated derivative kernels and of
  the rescaled derivatives of the synthesis kernels. This gives the Besov sandwich:
  `B^m_{p,min(p,2)} ⊆ W^m_p(V)` and, for `m ≥ 1`, `W^m_p(V) ⊆ B^m_{p,max(p,2)}`
  (`Rd.memSobolev_of_memApprox`, `Rd.memApprox_of_memSobolev`, with norm bounds
  `Rd.exists_hasWeakLineDeriv_of_memApprox`, `Rd.approxNormDyadic_le_of_hasWeakLineDeriv`), and
  `W^m_2 = B^m_{2,2}` for `m ≥ 1` (`Rd.memSobolev_two_iff_memApprox`).
  The bound of `‖f‖_{F^m_{p,2}}` writes `2^{jm} ψ_{j+1} ⋆ f` as `∑_α (η_α)_{2^j} ⋆ g_α`; the
  bound for `∂^w f` obtains `∂^w f` as the limit in `L_p` of the derivatives
  `∑_{j < J} (∂^w ψ̃_j) ⋆ (ψ_j ⋆ f)` of the reproducing sums (`Rd.derivSynthesisSum`), whose
  tails in `L_p(ℓ_2)` tend to zero (`MeasureTheory.tendsto_eLpNorm_lqNorm_ite_le`).
* **Sobolev and Besov embeddings.** Let `n = dim V`, `1 ≤ p ≤ r ≤ ∞`, `p < ∞`,
  `α = n(1/p - 1/r)` (`nikolskiiExponent`) and `1 ≤ q ≤ ∞`. The blocks `ψ_j ⋆ f` of
  `f ∈ L_p(V)` are continuous (`Rd.continuous_blockFun`) and satisfy the Nikolskii inequality
  `‖ψ_j ⋆ f‖_r ≤ N_p^(1-p/r) 2^(jα) ‖ψ_j ⋆ f‖_p` (`Rd.eLpNorm_blockFun_le_nikolskii`,
  `Rd.nikolskiiBlockConst`). For `s > α`, every `f ∈ B^s_{p,q}` has a representative `g ∈ L_r(V)`
  with `‖g‖_r ≤ K_{V,p,r,s} ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q}`
  (`Rd.exists_memLp_ae_eq_of_memApprox`, `Rd.besovEmbeddingConst`); for `s > n/p` it has a
  bounded continuous representative with the same bound for `r = ∞`
  (`Rd.exists_boundedContinuous_ae_eq_of_memApprox`). For `dim V ≥ 1`, `1 < p < ∞` and
  `f ∈ L_p(V)` whose weak derivatives `g_α` of order `m` along the basis of `Rd.gridBasis` lie
  in `L_p(V)`, put `M_f = ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p` (`Rd.sobolevToTLConst`). If
  `m > n(1/p - 1/r)`, `f` has a representative `u ∈ L_r(V)` with `‖u‖_r ≤ K_{V,p,r,m} M_f`
  (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv`); if `m > n/p`, a bounded continuous one with
  `sup |a| ≤ K_{V,p,∞,m} M_f` (`Rd.exists_boundedContinuous_ae_eq_of_hasWeakLineDeriv`). In
  particular every `f ∈ W^m_p(V)` has these representatives
  (`Rd.exists_memLp_ae_eq_of_memSobolev`, `Rd.exists_boundedContinuous_ae_eq_of_memSobolev`).
  The critical case `1/r = 1/p - m/n` with `r < ∞` (Sobolev's inequality) is not covered.
* **Bessel kernels.** A family `(G_j)` of Schwartz functions is uniformly Schwartz for some
  bounds iff `{G_j}` is a bounded set of the Schwartz space
  (`Rd.exists_isUniformSchwartz_iff_isVonNBounded`). If `(G_j)` is a uniform Schwartz family and
  `T` a continuous linear map of the Schwartz space, then `(T G_j)` is a uniform Schwartz family
  (`Rd.IsUniformSchwartz.exists_map`), in particular for `T = 𝓕⁻¹`. Let `ω̂` be a Schwartz
  function vanishing outside the annulus `{a ≤ ‖ζ‖ ≤ b}`, `a > 0`, and `σ` real. The Bessel
  kernels `K_j = 𝓕⁻¹[(2^{-2j} + ‖ζ‖²)^{σ/2} ω̂]` (`Rd.besselKernelFamily`) form a uniform
  Schwartz family (`Rd.exists_isUniformSchwartz_besselKernelFamily`), because the shifted
  symbols `(ε + ‖ζ‖²)^{σ/2}` have derivatives bounded on the annulus uniformly in `ε ∈ (0, 1]`
  (`Rd.exists_norm_iteratedFDeriv_besselSymbol_le`). For every Schwartz `ω` with `𝓕ω = ω̂`,
  the Bessel potential on Schwartz functions, the Fourier multiplier with Mathlib's Bessel symbol
  `⟨ξ⟩^σ` (`Rd.besselSchwartz`), maps the dilate `ω_{2^j}` to `2^{jσ} (K_j)_{2^j}`
  (`Rd.besselSchwartz_schwartzDilate`), and so does Mathlib's Bessel potential on tempered
  distributions (`Rd.besselPotential_schwartzDilate`); this identity needs no annulus. For
  `b = 2^N a`
  the dilates `((K_j)_{2^j})_j` form a Calderón–Zygmund family with overlap
  `(N + 1) (max((a²)^{σ/2}, (1 + b²)^{σ/2}) sup |ω̂|)²` (`Rd.besselOverlap`) and a finite
  Hörmander constant (`Rd.exists_isCZFamily_besselKernelFamily`); the seminorm bounds and the
  Hörmander constant are existential. The Fourier transforms of `ψ_1`, of `Φ - δ_{1/2} Φ` and
  of `δ_2 Φ - δ_{1/4} Φ` vanish outside such annuli
  (`Rd.mem_annulus_of_fourier_psiOneS_ne_zero`, `Rd.mem_annulus_of_fourier_psiBase_ne_zero`,
  `Rd.mem_annulus_of_fourier_psiDualBase_ne_zero`).
* **Bessel potential spaces `H^{s,p} = F^s_{p,2}`.** Let `V` have dimension `n ≥ 1`,
  `1 < p < ∞`, and let `J_s` be Mathlib's Bessel potential, the Fourier multiplier with
  `⟨ξ⟩^s = (1 + ‖ξ‖²)^{s/2}`; a tempered distribution `f` lies in Mathlib's Bessel potential
  space `H^{s,p}(V)` iff `J_s f ∈ L_p(V)` (`TemperedDistribution.MemSobolev`). For every real `s`
  there is a finite `C` such that for every `f ∈ F^s_{p,2}(V)`, `J_s f` is an `L_p` function `h`
  with `‖h‖_p ≤ C ‖f‖_{F^s_{p,2}}` (`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`; for
  Mathlib's bundled space `Rd.exists_enorm_toBesselPotentialSpace_le`), and a
  finite `C` such that `‖g‖_{F^s_{p,2}} ≤ C ‖J_s g‖_p` for every `g ∈ L_p(V)` with
  `J_s g ∈ L_p(V)` (`Rd.exists_triebelLizorkinNorm_le_of_besselPotential_eq`). Hence, for every
  real `s`, `f ∈ L_p(V)` lies in `F^s_{p,2}(V)` iff it lies in `H^{s,p}(V)`
  (`Rd.memTriebelLizorkin_iff_memSobolev_bessel`). For `s ≥ 0` there
  is a finite `C` such that every tempered distribution `f` with `J_s f = h ∈ L_p(V)` is an `L_p`
  function `g ∈ F^s_{p,2}(V)` with `‖g‖_{F^s_{p,2}} ≤ C ‖h‖_p`
  (`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`; for Mathlib's bundled space
  `Rd.exists_memTriebelLizorkin_toDistr`), and `W^m_p(V) = H^{m,p}(V)` for every `m ∈ ℕ`
  (Calderón; `Rd.memSobolev_iff_memSobolev_bessel`). The constants are existential.
  The kernels are the Bessel potentials of the blocks and of the synthesis kernels, dilates of
  Bessel kernels up to `2^{±js}` (`Rd.besselBase`), which form Calderón–Zygmund families
  (`Rd.exists_isCZFamily_besselBase_psiBase`, `Rd.exists_isCZFamily_besselBase_psiDualBase`).
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
  The constants are existential.
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

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Test functions as Schwartz functions and compactly supported complex Schwartz functions as complex test functions, commuting directional derivatives, the transpose formula for distributions and tempered distributions; cut-offs of Schwartz functions converge in the Schwartz space (smooth compactly supported functions are dense), tempered distributions determined by test functions | ✅ | ✗ | `Rd/SchwartzCutoff` |
| Weak derivatives and Sobolev spaces on open sets, integration by parts, also against complex test functions, uniqueness, locality, finite sums, the product rule with smooth functions, limits; the bridge to tempered distributions | ✅ | ✗ | `Rd/WeakDerivatives` |
| The convolution theorem and Plancherel for a convolution on `L_2`, the Bessel potential on Schwartz functions, even Fourier multipliers acting by the transpose, the comparison of the Bessel weight with the Littlewood–Paley weights, Mathlib's `H^s` as `F^s_{2,2}` (`s ≥ 0`) and `B^s_{2,2}` (`s > 0`) with explicit constants, `W^1_2 = H^1 = B^1_{2,2}` | ✅ | ✗ | `Rd/SobolevTwoLittlewoodPaley` |
| `H^1` on bounded Lipschitz domains as restrictions of `H^1(ℝ^d)`, by intrinsic differences, the weak gradient, and the trace space `B^{1/2}_{2,2}` of the boundary | ✅ | ✗ | `Rd/LipschitzDomainH1` |
| The inverse Fourier transform of integrable `L_2` functions, band-limited functions as bounded Lipschitz functions, truncation in frequency, and Rellich's theorem: the restriction from `H^1(ℝ^d)` to `L_2(Ω)` is compact for bounded `Ω` | ✅ | ✗ | `Rd/RellichCompactness` |
| The Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` on open sets inside Mathlib's `H^s(ℝ^d)`, `H^s(Ω)` as a quotient, Rellich's theorem for `H^1(Ω)`, the identification with the restriction space of a bounded Lipschitz domain, the bound of the `H^1` norm by the `W^1_2` norm, the weak derivatives as bounded operators on `H^1(ℝ^d)`, the density of compactly supported Schwartz functions in `H^s(ℝ^d)` with `H̃^s(ℝ^d) = H^s(ℝ^d)`, and the isometry `H̃^1(Ω) ≅ H^1_0(Ω)` | ✅ | ✗ | `Rd/SobolevRestrictionSpaces` |
| The Bessel potential of real Schwartz functions as a real function, the isometry `J_{2s} : H^s(ℝ^d) → H^{-s}(ℝ^d)`, the pairing of `H^{-s}` and `H^s`, and the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`, `(H^s(Ω))^* ≅ H̃^{-s}(Ω)`, `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` on open sets | ✅ | ✗ | `Rd/SobolevDuality` |
| `H^1(ℝ^d) ⊆ B^{1/2}_{2,1}(ℝ^d)` with explicit constants, the trace of `H^1(ℝ^d)` on a Lipschitz graph and the chart traces of `H^1(Ω)` on a bounded Lipschitz domain as bounded operators, the trace kernel, the trace space `H^{1/2}(Γ)` with trace and extension operators, `H^1(Ω) ⧸ ker γ ≅ H^{1/2}(Γ)`, and `H^{-1/2}(Γ)` | ✅ | ✗ | `Rd/BoundaryTraceSpace` |
| The area formula for Lipschitz graphs: Lipschitz maps and Mathlib's Euclidean Hausdorff measure, the linear case by Mathlib's norm determinant, stretches and tilts, the gradient and the Gram density, good pieces, `μHE[n-1](γ(A)) = ∫_A √(1 + ‖∇φ‖²)` with `n = dim V` in set, measure and integral form; the outward unit normal | ✅ | ✗ | `Rd/LipschitzGraphArea` |
| The surface measure of a bounded Lipschitz domain as `μHE[n-1]` on the boundary, its chart form, finiteness and null sets, the boundary `Γ` as a Lebesgue null set, the boundary trace in `L_p(Γ)`, `L_2(Γ)` with the traces of `H^1(Ω)` and `H^{1/2}(Γ)`, and the outward unit normal field | ✅ | ✗ | `Rd/SurfaceMeasure` |
| Dilation, reflection and conjugation of Schwartz functions, derivatives of dilations, uniform Schwartz families and finitely many exceptions in them, the Hörmander condition for dilation families with explicit constants, Calderón–Zygmund families, also with finitely many exceptional members, and their adjoints, the Littlewood–Paley blocks and the synthesis kernels as such families | ✅ | ✗ | `Rd/DilationFamilies` |
| The adjoint identity `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)` for `f ∈ L_p`, `g ∈ L_q`, and its form `∫ (K ⋆ f) conj g = ∫ f conj(K^* ⋆ g)` with the adjoint kernel, derivatives of Schwartz kernels moved to the other Schwartz factor, translates and reflections of Schwartz functions, and weak derivatives commuting with convolution by Schwartz functions, on `ℝ^d` and on open sets | ✅ | ✗ | `Rd/ConvolutionAdjoint` |
| The Cauchy–Schwarz inequality for finite sums, the `L_2` bounds of the analysis operator and of the synthesis operators on finite index sets for a kernel family with Fourier overlap `B`, and for every Calderón–Zygmund family | ✅ | ✗ | `Rd/PlancherelBounds` |
| The signed Calderón–Zygmund decomposition of functions with values in a normed space and of families: good parts bounded by `2^n t` with `∫ ‖·‖² ≤ 2^n t ∫ ‖f‖`, bad pieces with mean zero on their cubes and total mass at most `2 ∫ ‖f‖` | ✅ | ✗ | `Rd/CalderonZygmundSigned` |
| Chebyshev's inequality for split functions, the Hörmander condition around a cube, convolutions of pieces with mean zero, and the weak type `(1,1)` of the analysis and synthesis operators of a Calderón–Zygmund family with an explicit constant | ✅ | ✗ | `Rd/VectorValuedWeakType` |
| The distribution function, weak `L_p` norms, operators of weak and strong type and almost everywhere subadditive operators, with the definitions of the Carleson project, and their elementary properties | ✅ | ✗ | `Lp/WeakType` |
| The layer cake formula `∫ F^p dν = p ∫_0^∞ ν{F > t} t^(p-1) dt` for `[0, ∞]`-valued functions on every measure space, and the integrals of powers of `t` over `(0, b)`, `(0, ∞)` and the level sets `{t < a}`, `{t ≥ a}` | ✅ | ✗ | `Lp/LayerCake` |
| The parts of a function above and below a level, two Tonelli steps on s-finite measure spaces, integrals of powers from bounds at every level, and Marcinkiewicz interpolation between weak type `(1,1)` and strong type `(2,2)` with an explicit constant, for operators on an abstract input type and in the terms of the Carleson project | ✅ | ✗ | `Lp/Marcinkiewicz` |
| `L_p` and `L_p(ℓ_2)` norms by duality for `1 < p < ∞` through the norming family, Hölder's inequality for `[0, ∞]`-valued functions in `L_p` norms, and families in `L_p` vanishing outside a finite set | ✅ | ✗ | `Lp/NormingFamily` |
| The strong type `(p,p)`, `1 < p < ∞`, of the analysis and synthesis operators of a Calderón–Zygmund family with explicit constants: Plancherel for `p = 2`, Marcinkiewicz interpolation for `p < 2`, duality with the adjoint family for `p > 2` | ✅ | ✗ | `Rd/VectorValuedSingularIntegrals` |
| The square function theorem `L_p = F^0_{p,2}` for `1 < p < ∞` with explicit constants in both directions, and the reproducing formula `∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f) → f` in `L_p` | ✅ | ✗ | `Rd/SquareFunction` |
| Fourier transforms of iterated derivatives, the derivative symbols and kernels, the block `ψ_1` as a sum of derivatives of order `m`, and the Calderón–Zygmund families of the dilated derivative kernels and of the rescaled derivatives `2^{-jk} ∂^w ψ̃_j` of the synthesis kernels | ✅ | ✗ | `Rd/DerivativeKernels` |
| `W^m_p = F^m_{p,2}` for `1 < p < ∞` with explicit constants in both directions: the blocks as convolutions with the weak derivatives, the derivatives of the reproducing sums and their limit, the Besov sandwich `B^m_{p,min(p,2)} ⊆ W^m_p ⊆ B^m_{p,max(p,2)}` and `W^m_2 = B^m_{2,2}` for `m ≥ 1` | ✅ | ✗ | `Rd/SobolevTriebelLizorkin` |
| Continuity of convolutions of integrable bounded kernels with `L_p` functions, the Nikolskii inequality for the Littlewood–Paley blocks, almost everywhere convergence of the block series, the Besov embeddings into `L_r` for `s > n(1/p - 1/r)` and into bounded continuous functions for `s > n/p`, and the Sobolev embeddings `W^m_p ↪ L_r` and `W^m_p ↪ C_b` with explicit constants | ✅ | ✗ | `Rd/SobolevEmbedding` |
| Uniform Schwartz families as bounded sets and under continuous linear maps, the shifted Bessel symbols `(ε + ‖ζ‖²)^{σ/2}` with derivative bounds on annuli uniform in `ε`, the Bessel symbol and kernel families as uniform Schwartz families, the Bessel potential of a dilate, the dilated Bessel kernels as a Calderón–Zygmund family with explicit overlap, and the annuli of the Littlewood–Paley kernels | ✅ | ✗ | `Rd/UniformSchwartzFamilies` |
| Even Fourier multipliers, among them Mathlib's Bessel potential, commuting with translations and reflections of Schwartz functions and with convolutions, the Bessel kernels of the Littlewood–Paley kernels, convergent synthesis sums, `H^{s,p} ∩ L_p = F^s_{p,2}` for real `s`, `H^{s,p} = F^s_{p,2}` for `s ≥ 0` and `W^m_p = H^{m,p}` for `1 < p < ∞`, with existential constants | ✅ | ✗ | `Rd/BesselPotentialLifting` |
| Smoothness of parametric integrals, the dilation identity `m_2 - m = ∑_i ∂_{e_i} K_i` with the divergence kernels `K_i(x) = ⟪e_i, x⟫ ∫_1^2 t⁻¹ m_t(x) dt`, their supports and mean zero, and the Calderón–Zygmund families of the dilates of mean-zero Schwartz functions | ✅ | ✗ | `Rd/DivergenceKernels` |
| The local means of order two by the gradient, local means of Triebel–Lizorkin type on a set, bounded extensions from one patch, pasting in `W^1_p(ℝ^d)`, the extension theorem (`W^1_p(Ω)` is the space of restrictions of `W^1_p(ℝ^d)`) for `1 < p < ∞` with a bound, and for `p = 2` `H^1(Ω) = W^1_2(Ω)`, Rellich's theorem in `W^1_2(Ω)`, the quotient norm of `H^1(Ω)` and the boundary traces of `W^1_2(Ω)` | ✅ | ✗ | `Rd/SobolevExtension` |
| Gauss–Green on Lipschitz graph domains: product coordinates and Fubini, ray integrals, integrals of line derivatives of Lipschitz functions, the normal weight, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` for compactly supported `C^1` functions in chart and surface form, the product rule for line derivatives, and Green's formula `∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)` | ✅ | ✗ | `Rd/LipschitzGraphGreen` |
| Green's formula on bounded Lipschitz domains: integration by parts in `H^1(ℝ^d)`, resolutions of unity equal to one near the boundary, the chart form for every resolution of unity, the outward unit normal as the chart normal and a unit vector almost everywhere on the boundary, `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` for `u, w ∈ H^1(Ω)`, the traces from both sides of a graph, and the zero extension: `1_Ω u ∈ W^1_2(ℝ^d)` iff the trace of `u` vanishes | ✅ | ✗ | `Rd/LipschitzDomainGreen` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
