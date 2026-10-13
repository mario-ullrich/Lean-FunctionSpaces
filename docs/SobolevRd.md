# Sobolev spaces on `ℝ^d`

Part of [Function spaces via approximation](../README.md). Blueprint chapters: *Sobolev spaces on
`ℝ^d`*.

This block develops the Sobolev spaces `W^m_p` defined by weak derivatives. A weak derivative is
an identity between distributions on an open set, in Mathlib's distributions `𝓓'(Ω, ℂ)`; on the
whole space and for `L_p` functions it is an identity between tempered distributions `𝓢'(V, ℂ)`,
where Mathlib's Fourier transform and Bessel potential spaces live. For `p = 2` it identifies
Mathlib's Bessel potential spaces `H^s`, `s ≥ 0`, with the Triebel–Lizorkin spaces `F^s_{2,2}`
(and, for `s > 0`, with the Besov spaces `B^s_{2,2}`) and shows `W^1_2 = H^1`.

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
  (`Rd.enorm_besselPotential_one_sq_eq`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Weak derivatives and Sobolev spaces on open sets, integration by parts, uniqueness, locality, limits; cut-offs of Schwartz functions and the density of test functions in the Schwartz space; the bridge to tempered distributions | ✅ | ✗ | `Rd/WeakDerivatives` |
| The convolution theorem on `L_2`, the comparison of the Bessel weight with the Littlewood–Paley weights, Mathlib's `H^s` as `F^s_{2,2}` (`s ≥ 0`) and `B^s_{2,2}` (`s > 0`) with explicit constants, `W^1_2 = H^1` | ✅ | ✗ | `Rd/SobolevTwoLittlewoodPaley` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
