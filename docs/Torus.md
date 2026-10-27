# The torus

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Besov spaces*,
chapters *The torus* and *Classical definitions on the torus*; part *Sobolev and Bessel
potential spaces*, chapter *Sobolev spaces on the torus*.

On `𝕋^d` with its normalised Haar measure, the scheme consists of the trigonometric polynomials of
degree `< n`. They satisfy the Nikolskii inequality, so all the embeddings of [Besov and Sobolev
spaces on measure spaces](MeasureSpaces.md) hold on `𝕋^d`. For `p = 2` the Fourier coefficients
describe `B^s_{2,q}`, `H^s` and the Sobolev spaces `W^m_2` of weak derivatives, defined by Fourier
multipliers. For every `1 ≤ p < ∞` the Besov spaces are described by moduli of smoothness of every
order: the kernels of `ℝ^d` act on `𝕋^d` by convolution with their periodisations, using Young's
inequality on measurable groups of [Tools from analysis](Analysis.md) and the band-limited
approximation of [Besov spaces on `ℝ^d`](Rd.md); the same kernels give smooth Littlewood–Paley
blocks, which describe the Besov spaces for every `1 ≤ p < ∞`. Weak derivatives in `L_p`,
`1 ≤ p ≤ ∞`, defined by Fourier coefficients, are the distributional derivatives of the periodic
lifts on `ℝ^d`; for `1 < p < ∞` they give `W^m_p(𝕋^d) = F^m_{p,2}(𝕋^d)`, with the Besov
sandwich and the Sobolev embeddings. The restriction to a face of `𝕋^(n+1)` is the model case of
the trace theorem.

## Main results

* **Besov spaces through moduli of smoothness.** For `f ∈ L_2(𝕋^d)` let
  `ω(f, t)_2 = sup_{‖h‖ ≤ t} ‖f(· + h) - f‖_2`. Jackson's theorem
  `E_n(f)_2² ≤ d ω(f, 1/n)_2²` holds (`Torus.approxError_sq_le_card_mul_modulus_sq`), and for
  `0 < s < 1` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{2,q}(𝕋^d)` iff
  `‖f‖_2 + ‖(2^(js) ω(f, 2^(-j))_2)_j‖_{ℓ_q} < ∞`, with equivalent norms
  (`Torus.memBesov_iff_modulusNorm_lt_top`, `Torus.approxNormDyadic_le_modulusNorm`,
  `Torus.modulusNorm_le_approxNormDyadic`): the modulus is compatible with the trigonometric
  scheme with inverse order `1` (`Torus.trigModulusData`). For every `1 ≤ p < ∞`, `0 < s < r`
  and `1 ≤ q ≤ ∞`, `f ∈ B^s_{p,q}(𝕋^d)` iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  for the modulus `ω_r` of order `r` (`Torus.memBesov_iff_modNorm_lt_top_lp`). The kernels of
  `ℝ^d` act on `𝕋^d` by `(Φ ⋆ f)(t) = ∫ Φ(y) f(t - π y) dy` (`Torus.econvLp`), with their Fourier
  transforms at the lattice points as multipliers (`Torus.econv_mFourier`); this transfers
  Jackson's inequality (`Torus.approxError_trigScheme_le`) and Bernstein's inequality
  (`Torus.lpModulus_le_of_mem_trigPolyLp`) from band-limited approximation on `ℝ^d`.
* **Besov spaces on the torus as interpolation spaces.** With `p` and `ω_r` as above, let
  `N_{s,q}(f) = ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}`, `0 < s₀ < s₁ < r`, `0 < η < 1` and
  `1 ≤ q₀, q₁, q ≤ ∞`. The real interpolation space `(N_{s₀,q₀}, N_{s₁,q₁})_{η,q}` of the
  continuous K-method consists of the `f ∈ L_p(𝕋^d)` with `N_{(1-η)s₀+ηs₁,q}(f) < ∞`, and
  `(‖·‖_p, N_{s₁,q₁})_{η,q}` of the `f` with `N_{ηs₁,q}(f) < ∞`
  (`Torus.memKMethod_modCouple_iff`, `Torus.memKMethod_leftModCouple_iff`).
* **Besov spaces on the torus through Littlewood–Paley blocks.** Let `ψ_j` be the
  Littlewood–Paley kernels on `ℝ^d` of [Besov spaces on `ℝ^d`](Rd.md), acting on `𝕋^d` by
  convolution, and `Δ_j f = ψ_j ⋆ f` (`Torus.lpBlock`). For every `1 ≤ p < ∞`, `s > 0` and
  `1 ≤ q ≤ ∞`, `f ∈ B^s_{p,q}(𝕋^d)` iff `‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q} < ∞`
  (`Torus.memBesov_iff_littlewoodPaleyNorm_lt_top`), with explicit constants in both directions
  (`Torus.approxNormDyadic_trigScheme_le`,
  `Torus.littlewoodPaleyNorm_le_approxNormDyadic_trigScheme`). The identities between the
  convolution operators follow from their Fourier multipliers and the density of the
  trigonometric polynomials (`Torus.econvLp_comp_econvLp`, `Torus.tendsto_econvLp_of_fourier`).
* **Traces on the torus.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `s > 0`, the restriction
  `f ↦ f(0, ·)` to the face `{x_0 = 0}` of `𝕋^(n+1)` extends from trigonometric polynomials to
  a map from `B^{s+1/p}_{p,q}(𝕋^(n+1))` into `B^s_{p,q}(𝕋^n)`, and every element of
  `B^s_{p,q}(𝕋^n)` is a trace (`Torus.trace_besov`). The proof uses the trace inequality
  `‖a(0, ·)‖_p ≤ (2⌈p/2⌉ m)^(1/p) ‖a‖_p` for polynomials of degree `< m`
  (`Torus.eLpNorm_restrictFace_le`) and an extension by the normalised Fejér kernel. For
  continuous `f ∈ B^{1/p}_{p,1}(𝕋^(n+1))`, in particular for continuous
  `f ∈ B^{s+1/p}_{p,q}(𝕋^(n+1))` with `s > 0`, the trace is `f(0, ·)`
  (`Torus.traceBound_ext_eq_restrictFace`, `Torus.trace_besov_eq_restrictFace`); for `s > n/p`
  every `f ∈ B^{s+1/p}_{p,q}(𝕋^(n+1))` has a continuous representative whose restriction is its
  trace (`Torus.exists_trace_eq_restrictFace`). The approximants in this proof are the
  de la Vallée Poussin means `V_k f = Θ_{k+n+1} ⋆ f`, near-best both in `L_p` and in the sup
  norm.
* **Sobolev spaces through weak derivatives.** Call `g ∈ L_2(𝕋^d)` the weak derivative
  `∂^α f` of `f ∈ L_2(𝕋^d)` if `ĝ(k) = (2πi k)^α f̂(k)` for all `k ∈ ℤ^d`, and let
  `W^m_2(𝕋^d)` consist of the `f` all of whose weak derivatives of order `|α| ≤ m` lie in
  `L_2`. Then `f ∈ W^m_2(𝕋^d)` iff `∑_k (1 + max_i |k_i|)^(2m) |f̂(k)|² < ∞`
  (`Torus.memSobolev_iff`), and for `m ≥ 1`, `W^m_2(𝕋^d) = B^m_{2,2}(𝕋^d)`
  (`Torus.memSobolev_iff_memBesov`). In every `L_p(𝕋^d)`, `1 ≤ p ≤ ∞`, the same rule
  `ĝ(m) = σ_v(m) f̂(m)` with `σ_v(m) = ∏_l 2πi ⟪m, v_l⟫` defines weak derivatives `∂^v` along
  directions `v ∈ (ℝ^d)^k`, tested against trigonometric polynomials
  (`Torus.HasWeakLineDeriv`). These are the distributional derivatives of the periodic lifts:
  `g = ∂^v f` iff `g ∘ π = ∂^v (f ∘ π)` in Mathlib's `𝓓'(ℝ^d)` for the quotient map
  `π : ℝ^d → 𝕋^d` (`Torus.hasWeakLineDeriv_iff_comp_proj`, `Torus.hasWeakDeriv_iff_comp_proj`,
  `Torus.memSobolev_iff_comp_proj`), through the pairing `h ↦ ∫ φ(x) h(π x) dx` with test
  functions (`Torus.periodicPairing`); classical derivatives of `C^1` lifts are weak derivatives
  (`Torus.hasWeakLineDeriv_of_contDiff`, `Torus.hasWeakLineDeriv_of_contDiff_chain`). An
  element of `L_p(𝕋^d)` is determined by its Fourier coefficients
  (`Torus.eq_of_mFourierCoeff_eq`), so the weak derivative is unique; it is linear
  and passes to limits, for `p < ∞` it commutes with convolution by Schwartz kernels
  (`Torus.econvLp_iteratedLineDerivOp`), and `f ∈ W^m_p(𝕋^d)` iff `∂^v f ∈ L_p` for all
  directions of order `≤ m` (`Torus.memSobolev_iff_forall_hasWeakLineDeriv`). For `d ≥ 1` and
  `1 < p < ∞`, `W^m_p(𝕋^d) = F^m_{p,2}(𝕋^d)` for every `m ∈ ℕ`
  (`Torus.memSobolev_iff_memTriebelLizorkin`), with named constants in both directions
  (`Torus.triebelLizorkinNorm_le_of_hasWeakLineDeriv`,
  `Torus.exists_hasWeakLineDeriv_of_memTriebelLizorkin`): the vector-valued singular integrals on
  the torus act on the derivative kernels of `ℝ^d`. Hence
  `B^m_{p,min(p,2)}(𝕋^d) ⊆ W^m_p(𝕋^d) ⊆ B^m_{p,max(p,2)}(𝕋^d)` for `m ≥ 1`
  (`Torus.memSobolev_of_memBesov`, `Torus.memBesov_of_memSobolev`), `W^m_p(𝕋^d)` is described by
  local means (`Torus.memSobolev_iff_tlLocalMeans`), and with `α = d (1/p - 1/r)` every
  `f ∈ W^m_p(𝕋^d)` lies in `L_r(𝕋^d)` for `p ≤ r ≤ ∞` and `m > α`, has a continuous
  representative for `m > d/p`, and lies in `W^k_r(𝕋^d)` for `p ≤ r < ∞` and `k < m - α`
  (`Torus.memSobolev_exists_inclusion_eq`, `Torus.memSobolev_exists_continuous`,
  `Torus.memSobolev_of_memSobolev_of_lt`).
* **The Nikolskii inequality and the Besov embeddings.** For a trigonometric polynomial `T` of
  degree `< n` on `𝕋^d`, `n ≥ 1`, and `1 ≤ p < ∞`, `‖T‖_∞ ≤ (2⌈p/2⌉)^(d/p) n^(d/p) ‖T‖_p`
  (`Torus.norm_le_rpow_mul_eLpNorm`). Hence the trigonometric polynomials have the
  Nikolskii property of dimension `d` (`Torus.trigScheme_hasNikolskii`), and all the Besov
  embeddings of [Besov and Sobolev spaces on measure spaces](MeasureSpaces.md) hold on
  `𝕋^d` with `α = d (1/p - 1/r)`
  (`Torus.memBesov_exists_inclusion_eq`, `Torus.memBesov_exists_continuous`).
* **The Sobolev embedding on the torus.** Let `s > d/2` and `f ∈ L_2(𝕋^d)` with
  `∑_{k ∈ ℤ^d} (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞`. Then `f` has a continuous representative
  (`Torus.sobolev_exists_continuous`). The space `H^s(𝕋^d)` of these functions satisfies
  Jackson's and Bernstein's inequalities with constant `1` (`Torus.sobolevSpace`), so
  `H^s(𝕋^d) ⊆ B^s_{2,∞}(𝕋^d)`, `B^t_{2,q}(𝕋^d) ⊆ H^s(𝕋^d)` for `t > s`, and
  `H^s(𝕋^d) ⊆ L_r(𝕋^d)` for `2 ≤ r ≤ ∞` and `s > d(1/2 - 1/r)`
  (`Torus.sobolev_memBesov_top`, `Torus.exists_sobolev_of_memBesov`,
  `Torus.sobolev_exists_inclusion_eq`).
* **Fourier coefficients and dyadic blocks on the torus.** For the Fourier basis on `𝕋^d` the
  dyadic blocks of the abstract theory give the Littlewood–Paley characterisation of
  `B^s_{2,q}(𝕋^d)` (`Torus.memBesov_two_iff_blockNorm_lt_top`), and for `q = 2`
  `B^s_{2,2}(𝕋^d) = H^s(𝕋^d)` (`Torus.memBesov_two_two_iff`). The Fourier basis, an eigenbasis
  of the Laplacian, is a continuous spectral basis with the local Weyl bound of dimension `d`
  (`Torus.fourierEigenbasis`, `Torus.localWeylBound_fourierEigenbasis`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| The torus: trigonometric polynomials and their uniform density, Nikolskii inequality | ✅ | ✗ | `Torus/Measure`, `Torus/Scheme`, `Torus/Nikolskii` |
| The torus: `H^s(𝕋^d)`, Besov and Sobolev embeddings, `H^s(𝕋^d) ↪ C(𝕋^d)` | ✅ | ✗ | `Torus/Sobolev`, `Torus/Embeddings` |
| Fourier-coefficient characterisations, `H^s(𝕋^d) = B^s_{2,2}(𝕋^d)` | ✅ | ✗ | `Torus/Coefficients` |
| The Fourier basis as a continuous spectral basis with the local Weyl bound | ✅ | ✗ | `Torus/FourierSpectralBasis` |
| Moduli of smoothness in `L_2(𝕋^d)`, Jackson's theorem, coincidence for `0 < s < 1` | ✅ | ✗ | `Torus/Translation`, `Torus/Modulus`, `Torus/BesovModuli` |
| Convolution on the torus with kernels on `ℝ^d`: Young's inequality, Fourier multipliers, differences, convolution of bounded continuous functions | ✅ | ✗ | `Torus/EuclideanConvolution` |
| Jackson's and Bernstein's inequalities in `L_p(𝕋^d)`, moduli of every order | ✅ | ✗ | `Torus/LpJackson` |
| Convolution identities, approximate identities | ✅ | ✗ | `Torus/EuclideanConvolutionIdentities` |
| Littlewood–Paley blocks, Besov spaces by them for `1 ≤ p < ∞` | ✅ | ✗ | `Torus/LittlewoodPaley` |
| Besov spaces on the torus by moduli of smoothness for all `1 ≤ p < ∞` | ✅ | ✗ | `Torus/LpBesovModuli` |
| Besov spaces on the torus by moduli of smoothness as interpolation spaces | ✅ | ✗ | `Torus/BesovInterpolation` |
| Traces on the torus: trace inequality, Fejér extension, `B^{s+1/p}_{p,q}(𝕋^(n+1)) → B^s_{p,q}(𝕋^n)` onto | ✅ | ✗ | `Torus/Trace` |
| The trace of a continuous function is its restriction; de la Vallée Poussin operators | ✅ | ✗ | `Torus/TraceContinuous` |
| Weak derivatives on the torus, `W^m_2(𝕋^d) = H^m(𝕋^d) = B^m_{2,2}(𝕋^d)` | ✅ | ✗ | `Torus/WeakDerivatives` |
| Fourier coefficients in `L_p(𝕋^d)`: convolutions, uniqueness | ✅ | ✗ | `Torus/LpFourierCoefficients` |
| Weak derivatives along directions in `L_p(𝕋^d)`, `W^m_p(𝕋^d)` by them | ✅ | ✗ | `Torus/LpWeakDerivatives` |
| `W^m_p(𝕋^d) = F^m_{p,2}(𝕋^d)` for `1 < p < ∞`, the Besov sandwich, local means | ✅ | ✗ | `Torus/SobolevTriebelLizorkin` |
| Embeddings of `W^m_p(𝕋^d)` into `L_r`, `C(𝕋^d)`, `W^k_r(𝕋^d)` | ✅ | ✗ | `Torus/SobolevEmbedding` |
| Weak and classical derivatives of periodic lifts | ✅ | ✗ | `Torus/PeriodicDistributions` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
