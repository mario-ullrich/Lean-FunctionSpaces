# Sobolev spaces on `ℝ^d`

Part of [Function spaces via approximation](../README.md). Blueprint chapters: *Sobolev spaces on
`ℝ^d`*.

This block develops the Sobolev spaces `W^m_p` defined by weak derivatives. A weak derivative is
an identity between distributions on an open set, in Mathlib's distributions `𝓓'(Ω, ℂ)`; on the
whole space and for `L_p` functions it is an identity between tempered distributions `𝓢'(V, ℂ)`,
where Mathlib's Fourier transform and Bessel potential spaces live.

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

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Weak derivatives and Sobolev spaces on open sets, integration by parts, uniqueness, locality, limits; cut-offs of Schwartz functions and the density of test functions in the Schwartz space; the bridge to tempered distributions | ✅ | ✗ | `Rd/WeakDerivatives` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
