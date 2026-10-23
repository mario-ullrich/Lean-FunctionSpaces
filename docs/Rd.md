# Function spaces on `ℝ^d`

Part of [Function spaces via approximation](../README.md). Blueprint chapters: *Function spaces on
`ℝ^d`, up to the invariance under changes of variables*.

Here `V` is a finite-dimensional real inner product space, such as `ℝ^d`, with its Lebesgue
measure, and `1 ≤ p < ∞`. The scheme consists of the band-limited classes
`E_k = {g ∈ L_p(V) : Θ_k ⋆ g = g}`. Young's inequality (on every measurable group), approximate
identities and kernel identities proved by Fourier inversion lead to the Littlewood–Paley
characterisation; Jackson's and Bernstein's inequalities identify the approximation spaces with
the Besov spaces defined by differences; local means, moment kernels and the reproducing formula
give the atomic decompositions with regular and smooth atoms; and smooth atoms yield the
invariance of the Besov spaces under smooth changes of variables with a cut-off. The domains,
traces and manifolds built on this block are in [Domains, manifolds and traces](DomainsTraces.md),
the mixed smoothness in [Dominating mixed smoothness](MixedSmoothness.md).

## Main results

* **Littlewood–Paley blocks on `ℝ^d`.** Let `V` be a finite-dimensional real inner product
  space, such as `ℝ^d`, and `1 ≤ p < ∞`. Let `χ` be a smooth cut-off, `1` on the unit ball and
  `0` outside the ball of radius `2`, and `ψ_j` the kernels with `𝓕ψ_0 = χ` and
  `𝓕ψ_j = χ(2^(-j) ·) - χ(2^(1-j) ·)`; let `Θ_k` be a kernel with `𝓕Θ_k = 1` on the ball of
  radius `2^(k+1)` and `0` outside the ball of radius `2^(k+2)`, and
  `E_k = {g ∈ L_p(V) : Θ_k ⋆ g = g}` the band-limited classes, the approximants of complexity
  `2^k`. For `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p(V), (E_k))` iff
  `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`, with equivalent quasi-norms
  (`Rd.memApprox_bandScheme_iff`, `Rd.approxNormDyadic_bandScheme_le`,
  `Rd.littlewoodPaleyNorm_le_approxNormDyadic`). The ingredients are Young's inequality
  `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p` (`Rd.eLpNorm_conv_le`), approximate identities in `L_p`
  (`Rd.tendsto_convLp_dilate`), and identities between the kernels such as `ψ_j ⋆ Θ_k = 0`
  for `j ≥ k + 3`, proved by Fourier inversion (`Rd.conv_psi_Theta`).
* **Besov spaces on `ℝ^d` by differences.** With `V`, `p`, `E_k` and `ψ_j` as above, let
  `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_p` be the modulus of smoothness of order `r ≥ 1`. For
  `0 < s < r` and `1 ≤ q ≤ ∞`, the following are equivalent for `f ∈ L_p(V)`:
  `f ∈ A^s_q(L_p(V), (E_k))`; `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`; and
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Rd.memApprox_bandScheme_iff_modulus`, `Rd.littlewoodPaleyNorm_lt_top_iff_modulus`). The
  proof combines Jackson's inequality `E(f, E_k)_p ≤ C ω_r(f, 2^(-k))_p`, through the approximant
  `∑_{l=1}^r (-1)^(l+1) C(r, l) Φ_{2^k/l} ⋆ f` (`Rd.enorm_sub_jacksonApprox_le`), with the inverse
  inequality `ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` for `a ∈ E_j`
  (`Rd.lpModulus_le_of_mem_bandSpace`), which rests on `‖Δ_v^r G‖_1 ≤ |v|^r ‖D^r G‖_1` for
  Schwartz functions `G` (`Rd.lintegral_enorm_higherDiff_schwartz_le`).
* **Local means on `ℝ^d`.** With `V` and `p` as above, let `g` be a smooth function with
  `∫ g = 1` that vanishes outside a ball, `g_c = c^n g(c ·)` its dilations (`n = dim V`),
  `L ≥ 1`, `m = ∑_{l=1}^L (-1)^(l+1) C(L, l) g_{1/l}` the moment kernel, and `k_0 = m`,
  `k_j = m_{2^j} - m_{2^(j-1)}` the local means kernels. For `0 < s < L` and `1 ≤ q ≤ ∞`,
  `‖f‖_p + ‖(2^(ks) ω_L(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff `‖(2^(js) ‖k_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`,
  with equivalent quasi-norms (`Rd.LocalMeansBump.besov_iff_localMeans`,
  `Rd.LocalMeansBump.localMeansNorm_le`, `Rd.LocalMeansBump.modNorm_le_localMeansNorm`), so
  local means describe the same spaces as band-limited approximation
  (`Rd.LocalMeansBump.memApprox_bandScheme_iff_localMeans`). Every estimate runs through the
  averaged differences `f - m_c ⋆ f = (-1)^L ∫ g(z) Δ^L_{-z/c} f dz`
  (`Rd.ae_sub_conv_dilate_momentKernel_eq`) and the reproducing formula
  `∑_{j ≤ J} η_j ⋆ k_j ⋆ f = m_{2^J} ⋆ m_{2^J} ⋆ f → f` with `η_0 = m`,
  `η_j = m_{2^j} + m_{2^(j-1)}` (`Rd.LocalMeansBump.tendsto_sum_dual_localMean`).
* **Atomic decompositions.** Let `1 ≤ p < ∞`. A regular atom of level `j`, order `r` and
  exponent `σ` with centre `c` vanishes outside `B(c, d 2^(-j))` and has `‖a‖_p ≤ C 2^(-jn/p)` and
  `‖Δ_h^r a‖_p ≤ C 2^(-jn/p) min(1, (2^j ‖h‖)^σ)` (`Rd.IsRegularAtom`). If at every level at most
  `N` centres of atoms with nonzero coefficients lie in a ball of radius `(d + r) 2^(-j)`, and
  `F = ∑_j ∑_m λ_{j,m} a_{j,m}` in `L_p(V)`, then for `0 < s < σ` and `1 ≤ q ≤ ∞`,
  `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖(2^(j(s - n/p)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}`
  (`Rd.modNorm_le_coeffNorm`). Conversely, the terms `η_j ⋆ (k_j ⋆ F)` of the reproducing formula
  split along the dyadic cells `P_{j,m}` into regular atoms of every order, with the coefficients
  `λ_{j,m} = 2^(jn/p) ‖1_{P_{j,m}} (k_j ⋆ F)‖_p` (`Rd.LocalMeansBump.atomic_decomposition`). Hence
  for `0 < s < L`, `F ∈ L_p(V)` has `‖F‖_p + ‖(2^(ks) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff it has
  such an atomic decomposition with atoms of order and exponent `L` and finite coefficient
  quasi-norm (`Rd.LocalMeansBump.besov_iff_atomic`). On a measurable set `Ω`, regular atoms on `Ω`
  bound `‖a‖_{L_p(Ω)}` and the differences on the step sets `Ω_{rh}` (`Rd.IsRegularAtomOn`), and
  the synthesis bounds `‖F‖_{L_p(Ω)} + ‖(2^(ks) ω_r(F, 2^(-k), Ω)_p)_k‖_{ℓ_q}` in the same way
  (`Rd.modNormOn_le_coeffNorm`).
* **Smooth atoms.** A smooth atom on `Ω` of order `K` vanishes outside `B(c, d 2^(-j))`, is `K`
  times continuously differentiable within `Ω` and has `‖D^l a‖ ≤ A 2^(jl)` on `Ω` for `l ≤ K`
  (`Rd.IsSmoothAtom`). On a convex set with nonempty interior it is a regular atom on `Ω` of order
  and exponent `r` for every `1 ≤ r ≤ K`, since `|Δ_h^r a(x)| ≤ 2^r r^(r+1) C ‖h‖^r` whenever
  `x, …, x + r h ∈ Ω` and `‖D^i a‖ ≤ C` on `Ω` (`Rd.isRegularAtomOn_of_isSmoothAtom`,
  `Rd.norm_higherDiff_le_of_iteratedFDerivWithin`). The cell atoms of the atomic decomposition are
  smooth atoms of every order (`Rd.LocalMeansBump.atomic_decomposition_smooth`). Smooth atoms keep
  their form under a smooth change of variables `T f = 1_{Ω ∩ U} (χ f) ∘ Φ` with a cut-off `χ`
  that vanishes outside a compact set: `T a` is a smooth atom on `Ω` of the same order, with
  uniform constants (`Rd.CutoffDiffeo.isSmoothAtom_apply`).
* **Invariance under changes of variables.** Let `Ω` be a measurable convex set with nonempty
  interior, `T` as above, `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`. There is `C < ∞` such that
  for all `F ∈ L_p(V)`,
  `‖T F‖_{L_p(Ω)} + ‖(2^(ks) ω_r(T F, 2^(-k), Ω)_p)_k‖_{ℓ_q} ≤
  C (‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q})` (`Rd.CutoffDiffeo.modNormOn_applyLp_le`). On a
  Besov domain, a closed convex set with nonempty interior whose functions of finite intrinsic
  quasi-norm `N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}` extend to `V` with
  a bound (`Rd.BesovDomain`, a hypothesis class whose instances are `V`, the closed half-space
  and the models of manifolds), `N_Ω(T f) ≤ C N_Ω(f)`
  (`Rd.CutoffDiffeo.modNormOn_applyLp_le_modNormOn`), and the order `r > s` of the differences
  does not matter (`Rd.BesovDomain.modNormOn_order_le`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Young's inequality on measurable groups, weighted Jensen inequality, weighted averages in `L_p` | ✅ | ✗ | `Lp/Young` |
| Convolution with integrable kernels on `ℝ^d`: Young's inequality, pointwise bounds, associativity, operators on `L_p` | ✅ | ✗ | `Rd/Convolution` |
| Dilations, their supports and their first moments, continuity of translation, approximate identities in `L_p(ℝ^d)` | ✅ | ✗ | `Rd/ApproxIdentity` |
| The Fourier transform of integrable functions (continuity, `L_1` bounds, convolutions, multiplication formula, conjugation, Lipschitz bound for band-limited inverse transforms); Littlewood–Paley kernels: smooth cut-offs, dilation formula for `𝓕`, the kernels on the frequency side with `|𝓕ψ_j| ≤ 1`, telescoping sums and at most two blocks at every frequency, kernel identities by Fourier inversion | ✅ | ✗ | `Rd/LittlewoodPaleyKernels` |
| Band-limited classes on `ℝ^d`, Littlewood–Paley blocks, `A^s_q(band-limited)` characterised by Littlewood–Paley blocks for `s > 0` | ✅ | ✗ | `Rd/BandLimited`, `Rd/LittlewoodPaley` |
| Differences `higherDiff` on any additive monoid, steps of either sign; the modulus of smoothness on `ℝ^d`, dilation of the scale, differences of convolutions and dilations | ✅ | ✗ | `Rd/Differences`, `Rd/DilatedDifferences` |
| Jackson's inequality for band-limited approximation | ✅ | ✗ | `Rd/BandJackson` |
| Differences of Schwartz functions in `L_1`, inverse inequality for band-limited functions | ✅ | ✗ | `Rd/BandInverse` |
| Besov spaces on `ℝ^d`: approximation, Littlewood–Paley blocks and differences agree for `0 < s < r` | ✅ | ✗ | `Rd/BesovDifferences` |
| Moduli of smoothness on subsets of `ℝ^d`, restrictions by intrinsic differences | ✅ | ✗ | `Rd/DomainModuli` |
| Moment kernels: averaged differences, approximation with the modulus, also on subsets, vanishing first moments of the moment kernels of order two | ✅ | ✗ | `Rd/MomentKernels` |
| Local means on `ℝ^d`: reproducing formula, agreement with differences for `0 < s < L` | ✅ | ✗ | `Rd/LocalMeans` |
| Pointwise multipliers on `ℝ^d`: the multiplication operator on `L_p`, Leibniz's rule for differences, moduli of lower order | ✅ | ✗ | `Rd/Multipliers` |
| Dyadic cells of `ℝ^d`: partition, counting of their centres, bounded overlap | ✅ | ✗ | `Rd/DyadicGrid` |
| Atomic synthesis: bounded overlap, regular atoms on sets, coefficient quasi-norm | ✅ | ✗ | `Rd/AtomSynthesis` |
| Atomic decomposition by cell atoms, atomic characterisation of Besov spaces | ✅ | ✗ | `Rd/AtomAnalysis` |
| Differences within convex sets through derivatives within the set | ✅ | ✗ | `Rd/ConvexDifferences` |
| Smooth atoms on convex sets, smooth cell atoms of every order | ✅ | ✗ | `Rd/SmoothAtoms` |
| Smooth atoms under smooth changes of variables with a cut-off | ✅ | ✗ | `Rd/AtomComposition` |
| Invariance of Besov spaces under changes of variables, Besov domains | ✅ | ✗ | `Rd/DiffeoInvariance` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
