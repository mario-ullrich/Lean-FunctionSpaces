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
set the restriction from `H^1(ℝ^d)` to `L_2` is compact (Rellich's theorem). The
[interface document](FEECInterface.md) lists these results for a FEEC/BEEC library built on this
project, with the decisions behind their form.

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

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Test functions as Schwartz functions, commuting directional derivatives, the transpose formula for distributions and tempered distributions; cut-offs of Schwartz functions converge in the Schwartz space (smooth compactly supported functions are dense), tempered distributions determined by test functions | ✅ | ✗ | `Rd/SchwartzCutoff` |
| Weak derivatives and Sobolev spaces on open sets, integration by parts, uniqueness, locality, limits; the bridge to tempered distributions | ✅ | ✗ | `Rd/WeakDerivatives` |
| The convolution theorem on `L_2`, the comparison of the Bessel weight with the Littlewood–Paley weights, Mathlib's `H^s` as `F^s_{2,2}` (`s ≥ 0`) and `B^s_{2,2}` (`s > 0`) with explicit constants, `W^1_2 = H^1 = B^1_{2,2}` | ✅ | ✗ | `Rd/SobolevTwoLittlewoodPaley` |
| `H^1` on bounded Lipschitz domains as restrictions of `H^1(ℝ^d)`, by intrinsic differences, the weak gradient, and the trace space `B^{1/2}_{2,2}` of the boundary | ✅ | ✗ | `Rd/LipschitzDomainH1` |
| The inverse Fourier transform of integrable `L_2` functions, band-limited functions as bounded Lipschitz functions, truncation in frequency, and Rellich's theorem: the restriction from `H^1(ℝ^d)` to `L_2(Ω)` is compact for bounded `Ω` | ✅ | ✗ | `Rd/RellichCompactness` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
