# Sobolev spaces on `ℝ^d`

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Sobolev and Bessel
potential spaces*, chapters *Sobolev spaces on `ℝ^d`*, *Bessel potential spaces* and *Fourier
multipliers*.

This block develops the Sobolev spaces `W^m_p` defined by weak derivatives. A weak derivative is an
identity between distributions on an open set, in Mathlib's distributions `𝓓'(Ω, ℂ)`; on the whole
space and for `L_p` functions it is an identity between tempered distributions `𝓢'(V, ℂ)`, where
Mathlib's Fourier transform and Bessel potential spaces live. Lipschitz functions are weakly
differentiable, and weak derivatives satisfy the product rule with cutoffs and the chain rule
under Lipschitz maps that preserve Lebesgue measure. For `p = 2` it identifies Mathlib's
Bessel potential spaces `H^s`, `s ≥ 0`, with the Triebel–Lizorkin spaces `F^s_{2,2}` (and, for
`s > 0`, with the Besov spaces `B^s_{2,2}`) and shows `W^1_2 = H^1 = B^1_{2,2}`. On every bounded
set the restriction from `H^1(ℝ^d)` to `L_2` is compact (Rellich's theorem). For `W^m_p`, the block
`ψ_1` is a sum of derivatives of order `m` of Schwartz kernels, whose dilates form Calderón–Zygmund
families, and so do the rescaled derivatives `2^{-jk} ∂^w ψ̃_j` of the synthesis kernels.
With them, `W^m_p = F^m_{p,2}` for `1 < p < ∞`, with named constants in both directions, and,
for `m ≥ 1`, `W^m_p` lies between the Besov spaces `B^m_{p,min(p,2)}` and `B^m_{p,max(p,2)}`.
The difference of two dilates of a smooth function is a divergence of smooth kernels, with mean
zero when its first moments vanish; these kernels give the extension theorems on Lipschitz
domains ([Lipschitz domains and traces](DomainsTraces.md)). The
Littlewood–Paley blocks are continuous and satisfy the Nikolskii inequality, which gives the
embeddings of `B^s_{p,q}` into `L_r` for `s > n(1/p - 1/r)` and into bounded continuous functions
for `s > n/p`, and with `W^m_p ⊆ F^m_{p,2}` the Sobolev embeddings `W^m_p ↪ L_r` and `W^m_p ↪ C_b`,
all with named constants: formulas in norms and Schwartz seminorms of fixed kernels, proved finite.
An interpolation inequality for dyadic suprema (Brezis–Mironescu) adds the critical case: Jawerth's
embedding `F^{s₀}_{p₀,∞} ↪ F^{s₁}_{p₁,q}`, `F^{n(1/p₀ - 1/p₁)}_{p₀,∞} ↪ L_{p₁}` and Sobolev's
inequality `W^m_p ↪ L_r` for `1/r = 1/p - m/n`, `1 < p < ∞`, following Johnsen–Sickel.
Mathlib's Gagliardo–Nirenberg–Sobolev inequality, carried to weakly differentiable functions by
mollification, cut-off and Fatou's lemma, adds `p = 1`: `W^1_p ↪ L_r` for `1/r = 1/p - 1/n` and
every `1 ≤ p`, and `W^m_1 ↪ L_r` for `1/r = 1 - m/n`.
For the Bessel potential spaces, uniform Schwartz families stay uniform under continuous linear maps
of the Schwartz space, and the Bessel potential maps the dilates of every Schwartz function to
multiples of the dilates of its Bessel kernels; when the Fourier transform of the function lives in
an annulus, the Bessel kernels form a uniform Schwartz family and their dilates a Calderón–Zygmund
family. Applied to the Littlewood–Paley blocks and their synthesis kernels, this gives, for
`1 < p < ∞` and with existential constants, `H^{s,p} ∩ L_p = F^s_{p,2}` for every real `s`,
`H^{s,p} = F^s_{p,2}` for `s ≥ 0`, and Calderón's theorem `W^m_p = H^{m,p}`. The real
interpolation spaces of `L_p` and `W^m_p`, of two Sobolev spaces, and of two Bessel potential
spaces are Besov spaces. Symbols of order `σ`, Hörmander's class `S^σ_{1,0}`, lie between the
Schwartz functions and the functions of temperate growth; rescaled to the dyadic annuli they
give uniformly Schwartz kernels, whose convolutions lie below the maximal function; hence a
symbol of order `σ` maps `F^s_{p,q}` of tempered distributions into `F^{s-σ}_{p,q}` for every real
`s`, `1 < p < ∞` and `1 < q ≤ ∞`. With `L_p = F^0_{p,2}` this gives `H^{s,p} = F^s_{p,2}` for
tempered distributions and every real `s`, Mihlin's theorem on `L_p` for symbols of order `0`, and
the mapping properties of `H^{s,p}` for all `1 < p < ∞`: symbols of order `σ` lower the
smoothness by `σ`, derivatives by `1`, and `H^{s+1,p}` consists of the `u ∈ H^{s,p}` whose first
derivatives lie in `H^{s,p}`.

Sobolev spaces on open sets and on bounded Lipschitz domains, the trace space, the extension
theorem, Green's formula and the kernel of the trace are in [Lipschitz domains and
traces](DomainsTraces.md); the vector-valued singular integrals and the square function
theorem are in [Triebel–Lizorkin spaces](TriebelLizorkin.md).

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
* **Changes of variables and cutoffs.** For a Lipschitz `f : V → ℂ` the almost everywhere line
  derivative `D_v f` (Mathlib's `lineDeriv`) is the weak derivative on every open set
  (`Rd.hasWeakLineDeriv_of_lipschitzWith`). Weak derivatives are linear in the direction
  (`Rd.HasWeakLineDeriv.sum_smul_dir`), so the derivatives `g_i = ∂_{e_i} f` along an orthonormal
  basis give `∂_v f = ∑_i ⟪v, e_i⟫ g_i` (`Rd.hasWeakLineDeriv_of_forall_gridBasis`). If
  `g = ∂_w f` on `O ∩ B` and the smooth `χ` has closed support in `B`, then
  `χ g + (∂_w χ) f = ∂_w (χ f)` on `O` (`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`). On every
  compact `L ⊆ O`, smooth compactly supported functions approximate a locally integrable `f` and
  its weak derivatives in `L_1(L)` (`Rd.exists_tendsto_contDiff_of_hasWeakLineDeriv`). For a
  `K`-Lipschitz map `Φ` that preserves Lebesgue measure and maps `U` into `O`,
  `∂_v (f ∘ Φ)(x) = ∑_i ⟪DΦ(x) v, e_i⟫ g_i(Φ x)` weakly on `U`
  (`Rd.HasWeakLineDeriv.comp_lipschitzWith`), with
  `‖∑_i ⟪DΦ v, e_i⟫ h_i ∘ Φ‖_{L_p(U)} ≤ K ‖v‖ ∑_i ‖h_i‖_{L_p(O)}` for `1 ≤ p ≤ ∞`
  (`Rd.eLpNorm_sum_inner_fderiv_mul_comp_le`).
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
* **`W^m_p = F^m_{p,2}`.** Let `dim V ≥ 1`, `1 < p < ∞` and `m ∈ ℕ`. For `f ∈ L_p(V)`,
  `f ∈ W^m_p(V)` iff `f ∈ F^m_{p,2}(V)` (`Rd.memSobolev_iff_memTriebelLizorkin`), with named
  constants in both directions. If the weak derivatives
  `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the orthonormal basis `e` of `Rd.gridBasis` lie in
  `L_p(V)` for all multi-indices `α`, then
  `‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_{V,p,α} ‖g_α‖_p`
  (`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv`, `Rd.sobolevToTLConst`); if
  `f ∈ F^k_{p,2}(V)`, then for all directions `w ∈ V^k` the weak derivative `∂^w f` is a
  function `g ∈ L_p(V)` with `‖g‖_p ≤ C_{V,p,w} ‖f‖_{F^k_{p,2}}`
  (`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin`, `Rd.tlToSobolevConst`). The constants are
  strong type constants of the Calderón–Zygmund families of the dilated derivative kernels and of
  the rescaled derivatives of the synthesis kernels, formulas in Schwartz seminorms of these fixed
  kernels, proved finite (`Rd.sobolevToTLConst_ne_top`, `Rd.tlToSobolevConst_ne_top`). This gives
  the Besov sandwich:
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
  The constants are named formulas in norms and Schwartz seminorms of fixed kernels, proved
  finite (`Rd.besovEmbeddingConst_ne_top`, `Rd.sobolevToTLConst_ne_top`).
* **The critical Sobolev embedding.** Let `dim V = n ≥ 1`, `1 ≤ p₀ < p₁ < ∞`, `θ = p₀/p₁` and
  `α = n(1/p₀ - 1/p₁)`. At every point, `∑_j 2^(js₁) |(ψ_j ⋆ f)(x)|` with `s₀ - s₁ = α` is at most
  `c G(x)^θ (N_{p₀} ‖(2^(js₀) ‖ψ_j ⋆ f‖_{p₀})_j‖_{ℓ_∞})^(1-θ)` with
  `G(x) = sup_j 2^(js₀) |(ψ_j ⋆ f)(x)|`
  (`Rd.tsum_dyadicWeight_enorm_blockFun_le`), by the interpolation inequality for dyadic suprema
  (`ENNReal.tsum_dyadicWeight_mul_le_iSup`) and the Nikolskii inequality; integrated, its `L_{p₁}`
  norm is at most `K_{V,p₀,p₁} ‖f‖_{F^{s₀}_{p₀,∞}}`
  (`Rd.eLpNorm_tsum_dyadicWeight_enorm_blockFun_le`,
  `Rd.criticalEmbeddingConst`). Hence every `f ∈ F^α_{p₀,q}`, `1 ≤ q ≤ ∞`, has a representative
  `g ∈ L_{p₁}(V)` with `‖g‖_{p₁} ≤ K_{V,p₀,p₁} ‖f‖_{F^α_{p₀,∞}}`
  (`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`,
  `Rd.exists_memLp_ae_eq_of_memTriebelLizorkin`),
  for `p₀ = 1` as well, and Jawerth's embedding `F^{s₀}_{p₀,∞} ↪ F^{s₁}_{p₁,q}` holds for `s₁ ≥ 0`
  and every `q` (`Rd.exists_triebelLizorkinNorm_le_of_nikolskiiExponent`). For `1 < p < ∞`, `r < ∞`
  and `m = n(1/p - 1/r) ≥ 1`, `f` with weak derivatives `g_α ∈ L_p(V)` of order `m` has a
  representative `u ∈ L_r(V)` with `‖u‖_r ≤ K_{V,p,r} M_f`
  (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_of_eq`), and `W^m_p(V) ↪ L_r(V)` for every
  `p ≤ r < ∞` with `n(1/p - 1/r) ≤ m` (`Rd.exists_memLp_ae_eq_of_memSobolev_of_le`,
  `Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`).
* **The Gagliardo–Nirenberg–Sobolev inequality.** Let `dim V = n ≥ 1`, `1 ≤ p < ∞` and
  `1/p' = 1/p - 1/n`. Every `f ∈ L_p(V)` with weak derivatives `g_k` along the orthonormal basis
  of `Rd.gridBasis` satisfies `‖f‖_{p'} ≤ C_{V,p} ∑_k ‖g_k‖_p` with Mathlib's constant
  `C_{V,p}` (`Rd.eLpNorm_le_of_hasWeakLineDeriv`,
  `MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst`). The proof mollifies with a normalised
  bump, applies Mathlib's inequality for compactly supported `C^1` functions
  (`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`), passes to the limit along the
  convergence in measure of the mollifications, and removes the compact support by cut-offs and
  Fatou's lemma. Hence, for `r < ∞`, `1/r = 1/p - 1/n` and `g_k ∈ L_p(V)`, `f` has a
  representative `u ∈ L_r(V)` with `‖u‖_r ≤ C_{V,p} ∑_k ‖g_k‖_p`, `p = 1` included
  (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_one`, `Rd.exists_memLp_ae_eq_of_memSobolev_one`,
  and with the exponents `1/r + 1/n = 1/p`:
  `Rd.exists_memLp_ae_eq_of_memSobolev_one_of_inv_add_inv`), and every `f ∈ W^m_1(V)`,
  `m ≥ 1`, has a representative in `L_r(V)` for `r < ∞` and `1/r = 1 - m/n`
  (`Rd.exists_memLp_ae_eq_of_memSobolev_one_of_eq`).
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
  For `p ≤ r < ∞` and real `s ≥ n(1/p - 1/r)`, every element of `H^{s,p}(V)` is a function in
  `L_r(V)` (`Rd.exists_memLp_eq_of_memSobolev_bessel`), with `‖g‖_r ≤ C ‖F‖_{H^{s,p}}` in Mathlib's
  bundled space (`Rd.exists_enorm_le_of_besselPotentialSpace`).
* **`H^{s,p} = F^s_{p,2}` for tempered distributions.** Let `n ≥ 1` and `1 < p < ∞`. For every
  real `s` a tempered distribution `u` lies in `H^{s,p}(V)` iff it lies in `F^s_{p,2}` of tempered
  distributions (`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`), with finite constants in
  `‖u‖_{F^s_{p,2}} ≤ C ‖h‖_p` whenever `J_s u = h ∈ L_p(V)`
  (`Rd.exists_triebelLizorkinNormDistr_le_of_besselPotential_eq`) and in
  `‖J_s u‖_p ≤ C' ‖u‖_{F^s_{p,2}}` (`Rd.exists_besselPotential_eq_of_memTriebelLizorkinDistr`;
  for Mathlib's bundled space `Rd.exists_triebelLizorkinNormDistr_le_besselPotentialSpace`,
  `Rd.exists_enorm_besselPotentialSpace_le_triebelLizorkinNormDistr`). The first is the multiplier
  theorem below for `⟨ξ⟩^{-s}` and `L_p = F^0_{p,2}`; for the second, the blocks of `J_s u` are
  `(J_s ψ̃_j) ⋆ g_j` with the blocks `g_j` of `u` (`Rd.distribBlock_besselPotential`), whose
  partial sums converge in `L_p` (`Rd.exists_tendsto_sum_convLp`) to `J_s u`
  (`Rd.eq_of_tendsto_sum_distribBlock`).
* **Symbols of order `σ`.** A smooth `m` is a symbol of order `σ` (`Rd.HasSymbolGrowth`,
  written `Rd.HasSymbolGrowth σ m`; Hörmander's class `S^σ_{1,0}`) if
  `‖D^k m(ξ)‖ ≤ C_k (1 + ‖ξ‖²)^{(σ - k)/2}` for every `k`.
  Schwartz functions are symbols of every order (`Rd.hasSymbolGrowth_schwartz`), and symbols
  have temperate growth (`Rd.HasSymbolGrowth.hasTemperateGrowth`), so they are Fourier
  multipliers of tempered distributions; orders add under products
  (`Rd.HasSymbolGrowth.mul`). The Bessel weight `⟨ξ⟩^s` is a symbol of order `s`
  (`Rd.hasSymbolGrowth_besselWeight`, from the derivative bounds for powers of the Japanese
  bracket mirrored from TauCeti), `⟪ξ, v⟫` one of order `1` and `‖ξ‖²` one of order `2`. For a
  symbol `m` of order `σ` and a Schwartz `ω̂` vanishing outside an annulus `{a ≤ ‖ζ‖ ≤ b}`,
  `a > 0`, the kernels `K_j = 𝓕⁻¹[2^{-jσ} m(2^j ·) ω̂]` are uniformly Schwartz
  (`Rd.HasSymbolGrowth.exists_isUniformSchwartz_symbolKernelFamily`), and
  `m(D) ω_{2^j} = 2^{jσ} (K_j)_{2^j}` with `ω = 𝓕⁻¹ ω̂` (`Rd.fourierMultiplierCLM_schwartzDilate`);
  in particular `m(D) ψ̃_j = 2^{jσ} (G_j)_{2^j}` for the synthesis kernels with a uniform family
  `(G_j)` (`Rd.HasSymbolGrowth.exists_isUniformSchwartz_psiDualS`). Convolutions with the
  dilates of a uniform family lie below the maximal function, uniformly in `j`
  (`Rd.IsUniformSchwartz.enorm_conv_dilate_le_maximal`).
* **Fourier multipliers on Triebel–Lizorkin spaces.** Let `1 < p < ∞`, `1 < q ≤ ∞` and `m` a
  symbol of order `σ`. For every real `s` there is `C < ∞` with
  `‖m(D) u‖_{F^{s-σ}_{p,q}} ≤ C ‖u‖_{F^s_{p,q}}` for every tempered distribution `u`, in the
  Triebel–Lizorkin quasi-norm of tempered distributions of
  [Triebel–Lizorkin spaces](TriebelLizorkin.md)
  (`Rd.exists_triebelLizorkinNormDistr_fourierMultiplier_le`,
  `Rd.MemTriebelLizorkinDistr.fourierMultiplierCLM`); in particular
  `‖g‖_{F^{s-σ}_{p,q}} ≤ C ‖f‖_{F^s_{p,q}}` for `f, g ∈ L_p(V)` with `g = m(D) f`
  (`Rd.exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq`). The block of `m(D) u` is the
  convolution of the block of `u` with `m(D) ψ̃_j = 2^{jσ} (G_j)_{2^j}`
  (`Rd.distribBlock_fourierMultiplierCLM_eq_convLp`), which lies below the maximal function, and
  the Fefferman–Stein inequality finishes.
* **Mihlin's theorem and Fourier multipliers on `H^{s,p}`.** Let `1 < p < ∞`. For `n ≥ 1` and a
  symbol `m` of order `0` there is `C < ∞` such that `m(D) f` is a function `g ∈ L_p(V)` with
  `‖g‖_p ≤ C ‖f‖_p` for every `f ∈ L_p(V)` (`Rd.exists_fourierMultiplier_eq_of_hasSymbolGrowth`;
  the bounded operator `Rd.symbolLp`), a case of Mihlin's theorem, which TauCeti proves for
  symbols satisfying Mihlin's condition with finitely many derivatives. In every dimension a
  symbol of order `σ` maps `H^{s,p}(V)` into `H^{s-σ,p}(V)` for every real `s`
  (`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_hasSymbolGrowth`); hence
  `H^{s,p} ⊆ H^{s',p}` for `s' ≤ s` (`TemperedDistribution.MemSobolev.mono_of_one_lt`),
  `L_p ⊆ H^{s,p}` for `s ≤ 0` (`Rd.memSobolev_bessel_of_nonpos`), `∂_v` maps `H^{s,p}` into
  `H^{s-1,p}` and `Δ` into `H^{s-2,p}` (`TemperedDistribution.MemSobolev.lineDerivOp_of_one_lt`,
  `TemperedDistribution.MemSobolev.laplacian_of_one_lt`), and `u ∈ H^{s+1,p}` iff
  `u ∈ H^{s,p}` and `∂_v u ∈ H^{s,p}` for every `v`
  (`TemperedDistribution.memSobolev_add_one_iff`, mirrored from TauCeti with
  `J_2 = 1 - (2π)^{-2} Δ`, `TemperedDistribution.besselPotential_two_eq_sub_laplacian`). For
  `1 < q ≤ ∞` and `g, J_σ g ∈ L_p(V)`, `‖J_σ g‖_{F^{s-σ}_{p,q}}` and `‖g‖_{F^s_{p,q}}` are
  equivalent, Triebel's lifting property (`Rd.exists_triebelLizorkinNorm_besselPotential_le`,
  `Rd.exists_triebelLizorkinNorm_le_besselPotential`).
* **Sobolev spaces and real interpolation.** Let `dim V ≥ 1` and `1 < p < ∞`. The grid norm
  of `W^m_p(V)` is `‖f‖_p + inf ∑_α ‖g_α‖_p`, the infimum over the families of weak derivatives
  `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f ∈ L_p(V)` along the basis of `Rd.gridBasis`
  (`Rd.sobolevGridNorm`); weak derivatives are unique, so it is `‖f‖_p + ∑_α ‖g_α‖_p` for the
  family when it exists (`Rd.sobolevGridNorm_eq`), and it is finite exactly on `W^m_p(V)`
  (`Rd.sobolevGridNorm_lt_top_iff`).
  It lies between the dyadic quasi-norms of `B^m_{p,max(p,2)}` (for `m ≥ 1`) and
  `B^m_{p,min(p,2)}`, with the named constants `Rd.approxSobolevGridConst` and
  `Rd.sobolevGridApproxConst` (`Rd.approxNormDyadic_le_sobolevGridNorm`,
  `Rd.sobolevGridNorm_le_approxNormDyadic`). Hence, for `0 < θ, η < 1` and `1 ≤ q ≤ ∞`,
  `(L_p, W^m_p)_{θ,q} = B^{θm}_{p,q}` for `m ≥ 1` (`Rd.memKMethod_lpSobolevCouple_iff`) and
  `(W^{m₀}_p, W^{m₁}_p)_{η,q} = B^{(1-η)m₀+ηm₁}_{p,q}` for `1 ≤ m₀ < m₁`
  (`Rd.memKMethod_sobolevCouple_iff`), for the K-method of the couples of these norms. An additive
  map `T` with `‖T f‖_p ≤ M₀ ‖f‖_p` and `‖T f‖_{W^m_p} ≤ M₁ ‖f‖_{W^m_p}` maps `B^{θm}_{p,q}` into
  itself (`Rd.memApprox_map_of_bounded_lp_sobolev`) and satisfies
  `‖T f‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖f‖_{K,θ,q}` (`Rd.kMethodNorm_map_le_of_bounded_lp_sobolev`).
* **Bessel potential spaces and real interpolation.** Let `dim V ≥ 1` and `1 < p < ∞`. The
  Bessel potential norm `‖J_s f‖_p` of `f ∈ L_p(V)` (`Rd.besselPotentialNorm`) is finite exactly
  on Mathlib's `H^{s,p}(V)` (`Rd.besselPotentialNorm_lt_top_iff`), where it is the norm of the
  bundled space (`Rd.besselPotentialNorm_eq_enorm`), and equivalent to the quasi-norm of
  `F^s_{p,2}`, with existential constants (`Rd.exists_triebelLizorkinNorm_le_besselPotentialNorm`,
  `Rd.exists_besselPotentialNorm_le_triebelLizorkinNorm`). Hence, for `0 < η < 1` and
  `1 ≤ q ≤ ∞`, `(H^{s₀,p}, H^{s₁,p})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}` for `0 < s₀ < s₁` and
  `(L_p, H^{s₁,p})_{η,q} = B^{ηs₁}_{p,q}` for `s₁ > 0`, in the Bessel potential norms
  (Bergh–Löfström, Theorem 6.4.5(4); `Rd.memKMethod_besselPotentialCouple_iff`,
  `Rd.memKMethod_lpBesselPotentialCouple_iff`). For `p = 2` and `s₁ = 1` the couple is that of the
  embedding `H^1(V) → L_2(V)` with its quotient norm (`Rd.ofMap_toL2_eq_lpBesselPotentialCouple`),
  so `(L_2(V), H^1(V))_{θ,q} = B^θ_{2,q}(V)` for `0 < θ < 1`, by differences of every order
  `r > θ` (`Rd.memKMethod_ofMap_toL2_iff`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Weak derivatives and Sobolev spaces on open sets, integration by parts, also against complex test functions, uniqueness, locality, finite sums, the product rule with smooth functions, also with a cutoff `χ` supported in `B`, which carries a weak derivative on `O ∩ B` to one on `O`, limits; the bridge to tempered distributions | ✅ | ✗ | `Rd/Sobolev/WeakDerivatives` |
| Lipschitz and `C^1` functions as weakly differentiable functions, weak derivatives linear in the direction, `W^1_p(ℝ^d)` from the basis directions, the `L_p` bounds of the product rule with a cutoff, bounded multipliers on `L_p`, smooth cutoffs with bounded derivatives, the derivative of a mollification, mollification on open sets in `L_1`, `L_p` norms of compositions with measure-preserving maps, and the chain rule for Lipschitz measure-preserving maps | ✅ | ✗ | `Rd/Sobolev/WeakDerivativeChangeOfVariables` |
| Composition of weak derivatives, the derivatives along all directions from those along words in the basis, sums and choices over words, the Leibniz rule for `χ f` with a smooth compactly supported `χ` and the Leibniz constant `2^k sup_x ∑_{j ≤ k} ‖D^j χ(x)‖`, smooth compactly supported multipliers on `W^m_p(ℝ^d)`, the product rule in `L_p(ℝ^d)` | ✅ | ✗ | `Rd/Sobolev/WeakDerivativeLeibniz` |
| The convolution theorem and Plancherel for a convolution on `L_2`, the Bessel potential on Schwartz functions, Fourier multipliers multiplying the Fourier transform and even ones acting by the transpose, the comparison of the Bessel weight with the Littlewood–Paley weights, Mathlib's `H^s` as `F^s_{2,2}` (`s ≥ 0`) and `B^s_{2,2}` (`s > 0`) with explicit constants, `W^1_2 = H^1 = B^1_{2,2}` | ✅ | ✗ | `Rd/Sobolev/SobolevTwoLittlewoodPaley` |
| The inverse Fourier transform of integrable `L_2` functions, band-limited functions as bounded Lipschitz functions, truncation in frequency, the injectivity of `H^1(ℝ^d) → L_2(ℝ^d)`, and Rellich's theorem: the restriction from `H^1(ℝ^d)` to `L_2(Ω)` is compact for bounded `Ω` | ✅ | ✗ | `Rd/Sobolev/RellichCompactness` |
| Fourier transforms of iterated derivatives, the derivative symbols and kernels, the block `ψ_1` as a sum of derivatives of order `m`, and the Calderón–Zygmund families of the dilated derivative kernels and of the rescaled derivatives `2^{-jk} ∂^w ψ̃_j` of the synthesis kernels | ✅ | ✗ | `Rd/Sobolev/DerivativeKernels` |
| Smoothness of parametric integrals, the dilation identity `m_2 - m = ∑_i ∂_{e_i} K_i` with the divergence kernels `K_i(x) = ⟪e_i, x⟫ ∫_1^2 t⁻¹ m_t(x) dt`, their supports and those of dyadic dilates, mean zero, the local means kernels as dilation differences `k_{j+1} = (m_2 - m)_{2^j}`, and the Calderón–Zygmund families of the dilates of mean-zero Schwartz functions | ✅ | ✗ | `Rd/Sobolev/DivergenceKernels` |
| `W^m_p = F^m_{p,2}` for `1 < p < ∞` with named constants in both directions: the blocks as convolutions with the weak derivatives, convergent synthesis sums, the derivatives of the reproducing sums and their limit, the Besov sandwich `B^m_{p,min(p,2)} ⊆ W^m_p ⊆ B^m_{p,max(p,2)}` and `W^m_2 = B^m_{2,2}` for `m ≥ 1` | ✅ | ✗ | `Rd/Sobolev/SobolevTriebelLizorkin` |
| Continuity of convolutions of integrable bounded kernels with `L_p` functions, the Nikolskii inequality for the Littlewood–Paley blocks, almost everywhere convergence of the block series, the Besov embeddings into `L_r` for `s > n(1/p - 1/r)` and into bounded continuous functions for `s > n/p`, and the Sobolev embeddings `W^m_p ↪ L_r` and `W^m_p ↪ C_b` with named constants | ✅ | ✗ | `Rd/Sobolev/SobolevEmbedding` |
| The Nikolskii inequality in supremum form, the pointwise and the integrated bound of the weighted blocks, `F^{n(1/p₀ - 1/p₁)}_{p₀,q} ↪ L_{p₁}`, Jawerth's embedding `F^{s₀}_{p₀,∞} ↪ F^{s₁}_{p₁,q}` and the critical Sobolev embedding `W^m_p ↪ L_r` for `1/r = 1/p - m/n` with named constants | ✅ | ✗ | `Rd/Sobolev/CriticalSobolevEmbedding` |
| Mathlib's Gagliardo–Nirenberg–Sobolev inequality for weakly differentiable functions, by mollification, cut-off and Fatou's lemma; `W^1_p ↪ L_r` for `1/r = 1/p - 1/n` and every `1 ≤ p`, and `W^m_1 ↪ L_r` for `1/r = 1 - m/n` | ✅ | ✗ | `Rd/Sobolev/GagliardoNirenbergSobolev` |
| Value–derivative jets of `W^1_p(O)` and `W^1_p(V)`, restriction | ✅ | ✗ | `Rd/Sobolev/SobolevJets` |
| The grid norm of `W^m_p` between two Besov quasi-norms with named constants, `(L_p, W^m_p)_{θ,q} = B^{θm}_{p,q}`, `(W^{m₀}_p, W^{m₁}_p)_{η,q} = B^{(1-η)m₀+ηm₁}_{p,q}` for `1 < p < ∞`, and operators bounded on `L_p` and on `W^m_p` | ✅ | ✗ | `Rd/Interpolation/SobolevInterpolation` |
| The Bessel potential norm `‖J_s f‖_p`, equivalent to the quasi-norm of `F^s_{p,2}`; `(H^{s₀,p}, H^{s₁,p})_{η,q}` and `(L_p, H^{s₁,p})_{η,q}` are Besov spaces, and the couple of `H^1 → L_2` with `(L_2, H^1)_{θ,q} = B^θ_{2,q}` | ✅ | ✗ | `Rd/Interpolation/BesselPotentialInterpolation` |
| Uniform Schwartz families as bounded sets and under continuous linear maps, the shifted Bessel symbols `(ε + ‖ζ‖²)^{σ/2}` with derivative bounds on annuli uniform in `ε`, the Bessel symbol and kernel families as uniform Schwartz families, the Bessel potential of a dilate, the dilated Bessel kernels as a Calderón–Zygmund family with explicit overlap, and the annuli of the Littlewood–Paley kernels | ✅ | ✗ | `Rd/BesselPotentials/UniformSchwartzFamilies` |
| Even Fourier multipliers, among them Mathlib's Bessel potential, commuting with translations and reflections of Schwartz functions and with convolutions, the Bessel kernels of the Littlewood–Paley kernels, `H^{s,p} ∩ L_p = F^s_{p,2}` for real `s`, `H^{s,p} = F^s_{p,2}` for `s ≥ 0` and `W^m_p = H^{m,p}` for `1 < p < ∞`, with existential constants | ✅ | ✗ | `Rd/BesselPotentials/BesselPotentialLifting` |
| `H^{s,p} ↪ L_r` for `1 < p ≤ r < ∞` and `s ≥ n(1/p - 1/r)`, also in Mathlib's bundled space | ✅ | ✗ | `Rd/BesselPotentials/BesselPotentialEmbedding` |
| `H^{s,p} = F^s_{p,2}` for tempered distributions and every real `s`, `1 < p < ∞`, with existential constants, also in Mathlib's bundled space; the blocks of `J_s u` and convergent synthesis sums of `L_p` families | ✅ | ✗ | `Rd/BesselPotentials/BesselPotentialDistributions` |
| Derivative bounds for powers of the Japanese bracket (mirrored from TauCeti), symbols of order `σ` between the Schwartz functions and the functions of temperate growth, their algebra, the Bessel weight, `⟪ξ, v⟫` and `‖ξ‖²` as symbols, rescaled symbols on annuli, the uniformly Schwartz symbol kernels with `m(D) ω_{2^j} = 2^{jσ} (K_j)_{2^j}`, and the maximal bound of convolutions with dilates of uniform families | ✅ | ✗ | `Rd/FourierMultipliers/SymbolKernels` |
| The blocks of `m(D) u` as convolutions of the blocks of `u`, and symbols of order `σ` as maps from `F^s_{p,q}` to `F^{s-σ}_{p,q}` of tempered distributions for every real `s`, `1 < p < ∞`, `1 < q ≤ ∞`, also on `L_p` | ✅ | ✗ | `Rd/FourierMultipliers/TriebelLizorkinMultipliers` |
| Mihlin's theorem on `L_p`, `1 < p < ∞`, for symbols of order `0`, and the multiplier as a bounded operator on `L_p` | ✅ | ✗ | `Rd/FourierMultipliers/MihlinMultipliers` |
| Symbols of order `σ` from `H^{s,p}` to `H^{s-σ,p}` for `1 < p < ∞`, `H^{s,p} ⊆ H^{s',p}`, derivatives and the Laplacian on `H^{s,p}`, `J_2 = 1 - (2π)^{-2} Δ`, the derivative characterisation of `H^{s+1,p}` (mirrored from TauCeti), and the lifting property of `J_σ` on `F^s_{p,q}` for `1 < q ≤ ∞` | ✅ | ✗ | `Rd/FourierMultipliers/BesselPotentialMultipliers` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
