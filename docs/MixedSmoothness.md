# Dominating mixed smoothness

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Besov spaces*,
chapter *Dominating mixed smoothness on `ℝ^d`*.

On `ℝ^d = Fin d → ℝ` the spaces of dominating mixed smoothness measure differences in several
coordinates at once, with the weight `2^(s|k|_1)` for `k ∈ ℕ^d`. Mixed differences are powers in the
translation algebra of [Tools from analysis](Analysis.md), the kernels are tensor products of the
one-dimensional kernels of [Besov spaces on `ℝ^d`](Rd.md), and the levels are summed by the Schur
test and an almost diagonal lemma on `ℕ^d`, the counterpart of the almost diagonal sums of
[Approximation spaces](ApproximationSpaces.md). Mixed differences, mixed local means and the tensor
Littlewood–Paley blocks give the same space, and the hyperbolic cross sums approximate it at the
rate `2^(-sN) (N + 1)^((d-1)(1-1/q))`.

## Main results

* **Dominating mixed smoothness on `ℝ^d`.** On `ℝ^d = Fin d → ℝ` let
  `Δ^{L,e}_h f = (∏_{i ∈ e} Δ^L_{h_i e_i}) f` be the mixed differences (`Rd.mixedDiff`) and
  `Ω^e_L(f, t)_p = sup_{|h_i| ≤ t_i, i ∈ e} ‖Δ^{L,e}_h f‖_p` the mixed moduli (`Rd.mixedModulus`),
  used for `k ∈ ℕ^d` in the coordinates `e(k) = {i : k_i ≠ 0}` at the scale `2^(-k)`. Let
  `k_k = ⊗_i k_{k_i}` be the tensor products of the one-dimensional local means kernels of a bump
  vanishing outside `[-1, 1]` (`Rd.LocalMeansBump.mixedKernel`) and `δ_k = ⊗_i ψ_{k_i}` those of the
  one-dimensional Littlewood–Paley blocks (`Rd.mixedPsi`), so that `δ_k ⋆ f = 𝓕⁻¹(φ_k 𝓕 f)` for the
  tensor decomposition of unity. For `1 ≤ p < ∞`, `0 < s < L`, `1 ≤ q ≤ ∞` and `f ∈ L_p(ℝ^d)`,
  `‖(2^(s|k|_1) Ω^{e(k)}_L(f, 2^(-k))_p)_{k ∈ ℕ^d}‖_{ℓ_q} < ∞` iff
  `‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_k‖_{ℓ_q} < ∞` (`Rd.LocalMeansBump.mixedBesov_iff_mixedLocalMeans`) iff
  `‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q} < ∞` (`Rd.mixedBesov_iff_mixedLP`), the last being Vybíral's
  quasi-norm. The local means average mixed differences
  (`Rd.LocalMeansBump.enorm_mixedLocalMean_le`), the reproducing formulas give the converse, and
  the almost diagonal lemma on `ℕ^d` (`Rd.lqNorm_almostDiagonal_pi_le`, by the Schur test) sums
  the levels.
* **Hyperbolic cross approximation.** With `S_N f = ∑_{|k|_1 ≤ N} δ_k ⋆ f`, `|k|_1 = ∑_i k_i`
  (`Rd.hyperbolicSum`), for `s > 0`, `1 ≤ q ≤ ∞` and `N ∈ ℕ`,
  `‖f - S_N f‖_p ≤ C 2^(-sN) (N + 1)^((d-1)(1-1/q)) ‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q}` with the
  finite constant `C = ∑_l 2^(-sl) (l + 1)^((d-1)(1-1/q))` (`Rd.hyperbolicCrossConst`,
  `Rd.enorm_sub_hyperbolicSum_le_of_pos`); the counting step is
  `#{k : |k|_1 = n} ≤ (n + 1)^(d-1)` (`Rd.card_levelSet_le`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Tensor kernels on `ℝ^d`: integrals, convolutions, dilations, diagonal changes of variables | ✅ | ✗ | `Rd/MixedSmoothness/TensorKernels` |
| Sequences on `ℕ^d`: `ℓ_q` norms, Schur test, almost diagonal lemma | ✅ | ✗ | `Rd/MixedSmoothness/MixedSequences` |
| Mixed differences, mixed moduli, the mixed Besov quasi-norm | ✅ | ✗ | `Rd/MixedSmoothness/MixedDifferences` |
| Averaged mixed differences, bounded polynomials in translations | ✅ | ✗ | `Rd/MixedSmoothness/MixedAveragedDifferences` |
| Mixed local means and mixed differences | ✅ | ✗ | `Rd/MixedSmoothness/MixedLocalMeans` |
| Tensor Littlewood–Paley blocks, Vybíral's quasi-norm | ✅ | ✗ | `Rd/MixedSmoothness/MixedLittlewoodPaley` |
| Hyperbolic cross approximation | ✅ | ✗ | `Rd/MixedSmoothness/HyperbolicCross` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
