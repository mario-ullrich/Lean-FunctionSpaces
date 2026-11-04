# Characterizations of Function Spaces in Lean 4 / Mathlib

This project formalises function spaces of smooth functions in Lean 4 and Mathlib: Besov,
Triebel–Lizorkin, Sobolev and Bessel potential spaces. Each space has several classical
descriptions, and the project proves that they define the same space, on `ℝ^d`, the torus,
intervals and the cube, bounded Lipschitz domains and compact manifolds. Approximation spaces
give an abstract framework for many of these descriptions. The project contains no `sorry`.

* **Blueprint** (a webpage explaining the mathematics):
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/>
* **Blueprint as PDF**: <https://mario-ullrich.github.io/Lean-FunctionSpaces/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/dep_graph_document.html>
* **PDF and dependency graph as images**, built from the latest commit on `main`: branch
  [`blueprint-build`](https://github.com/mario-ullrich/Lean-FunctionSpaces/tree/blueprint-build)

## The setting

Let `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `s > 0` and `r > s` an integer. The Besov space `B^s_{p,q}(ℝ^d)`
consists of the `f ∈ L_p(ℝ^d)` with `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_{k ≥ 0}‖_{ℓ_q} < ∞`,
where `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_p`. The Triebel–Lizorkin space `F^s_{p,q}(ℝ^d)`
takes the `ℓ_q` norm of the Littlewood–Paley blocks `ψ_j ⋆ f` at each point before the `L_p`
norm. The Sobolev space `W^m_p` consists of the functions whose weak derivatives up to order `m`
lie in `L_p`, and the Bessel potential space `H^{s,p}` is Mathlib's space of the tempered
distributions `u` with `(1 - Δ)^{s/2} u ∈ L_p`.

An approximation scheme in a normed space `X` is a sequence of sets `{0} = A_0 ⊆ A_1 ⊆ ⋯` with
`c A_n ⊆ A_n` and `A_m + A_n ⊆ A_{m+n}`. With the error of best approximation
`E_n(f) = inf { ‖f - a‖ : a ∈ A_n }`, the approximation space `A^s_q` consists of the `f` with
`(n^(s - 1/q) E_{n-1}(f))_{n ≥ 1} ∈ ℓ_q` (Pietsch 1981). For trigonometric polynomials, splines,
band-limited functions, wavelets and eigenfunctions these are Besov spaces. The theory of spaces
of a scheme on a finite measure space has the torus as its concrete instance; the other settings
prove their characterisations directly.

On a domain the descriptions use the values of `f` in the domain (intrinsic differences, weak
derivatives, eigenfunction expansions) or extensions to `ℝ^d` (restrictions). A compact manifold
carries its spaces in the charts of an atlas and a smooth measure, that is, a measure with a
continuous positive density in every chart.

## The map of characterisations

Each row names descriptions that the project proves to define the same space, with the range of
the statement and a link to it in the blueprint, which names the Lean declarations. Throughout
`1 ≤ q ≤ ∞`, and `1 ≤ p < ∞` unless the row says otherwise. Ranges `0 < s < r` or `0 < s < L`
refer to differences, local means or atoms of order `r` or `L`. The blueprint chapter
[The representations of Besov spaces][representations] explains what each description measures
and how they differ.

[representations]: https://mario-ullrich.github.io/Lean-FunctionSpaces/chap-representations.html

**Besov spaces `B^s_{p,q}`**

| Setting | Descriptions proved equivalent | Range | Statement |
|---|---|---|---|
| `ℝ^d` | band-limited approximation, Littlewood–Paley blocks, differences | `0 < s < r` | [Besov spaces on ℝ^d](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-besov-differences.html#thm:rd-besov) |
| `ℝ^d` | local means, differences, band-limited approximation | `0 < s < L` | [Local means](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-local-means.html#thm:local-means) |
| `ℝ^d` | atoms with coefficients in `b^s_{p,q}`, differences | `0 < s < L` | [Atomic decompositions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-atomic-decompositions.html#thm:atomic-characterisation) |
| `ℝ^d`, `q = p` | Gagliardo form of `W^{s,p}`, approximation | `0 < s < 1` | [Sobolev–Slobodeckij spaces](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-slobodeckij.html#thm:sobolev-slobodeckij-besov) |
| `ℝ^d` | real interpolation of two difference spaces, differences, Littlewood–Paley blocks | `0 < s₀ < s₁ < r` | [Interpolation of Besov spaces](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-besov-interpolation.html#thm:rd-besov-interpolate) |
| `ℝ`, Daubechies D4 | wavelet coefficients, differences of order `2` | `0 < s < 2 - log₂(1 + √3)` | [Daubechies D4 coefficients](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-daubechies-besov-coefficients.html#thm:daub-besov-d4) |
| torus `𝕋^d` | trigonometric approximation, differences | `0 < s < r` | [Moduli on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-lp-moduli.html#thm:torus-lp-moduli) |
| `𝕋^d` | trigonometric approximation, Littlewood–Paley blocks | `s > 0` | [Littlewood–Paley blocks on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-lp-blocks.html#thm:torus-lp-besov) |
| `𝕋^d`, `p = 2` | trigonometric approximation, dyadic blocks of Fourier coefficients | `s > 0` | [Fourier coefficients](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-torus.html#thm:torus-coefficients) |
| `[0, 1]` | splines of order `r`, differences | `0 ≤ s < r - 1 + 1/p` | [Dyadic splines](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spline-jackson-coincidence.html#thm:spline-besov) |
| `[0, 1]` | step functions, Haar coefficients | `s > 0` (the space `A^s_q`; it is `B^s_{p,q}[0, 1]` for `s < 1/p`) | [Haar coefficients](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-haar.html#thm:haar) |
| `[0, 1]` | piecewise polynomials, multiwavelet coefficients | `s > 0` (the space `A^s_q`; it is `B^s_{p,q}[0, 1]` for `s < 1/p`) | [Multiwavelets](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-multiwavelets.html#thm:multiwavelet-besov) |
| `[0, 1]^d` | tensor splines of order `r`, isotropic differences, coordinate differences | `0 ≤ s < r - 1 + 1/p` | [The isotropic modulus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-iso-modulus.html#thm:iso-besov) |
| Lipschitz graph domain | intrinsic differences, restrictions of `B^s_{p,q}(ℝ^d)` | `0 < s < r` | [Lipschitz graph domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-graph-intrinsic-differences.html#thm:graph-besov) |
| bounded Lipschitz domain | intrinsic differences, restrictions of `B^s_{p,q}(ℝ^d)` | `0 < s < r` | [Bounded Lipschitz domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bounded-lipschitz-domains.html#thm:bounded-lipschitz-besov) |
| bounded smooth domain | chart pieces of its closure as a manifold, intrinsic differences | `0 < s < r` | [Smooth domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-smooth-domain-charts.html#thm:smooth-domain-besov) |
| bounded Lipschitz domain, `d ≥ 1`, `p = 2` | Neumann eigenfunction expansions, intrinsic differences | `0 < s < 1` | [Neumann eigenfunctions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spectral-besov-domains.html#thm:spectral-besov-neumann) |
| compact manifold | chart pieces of any two Besov atlases | `s > 0` | [Besov spaces on manifolds](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-manifold-besov.html#def:manifold-besov) |
| compact manifold, `d ≥ 1`, `p = 2` | eigenfunction expansions of a chart form, chart pieces | `0 < s < 1` | [Chart eigenfunctions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spectral-besov-manifold.html#thm:spectral-besov-manifold) |
| `ℝ^d`, mixed smoothness | mixed differences, mixed local means, tensor Littlewood–Paley blocks | `0 < s < L` | [Mixed smoothness](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-mixed-lp-blocks.html#thm:mixed-lp) |

**Traces.** The trace maps `B^{s+1/p}_{p,q}` of the domain onto `B^s_{p,q}` of the boundary; in
the last two rows it maps `H^1(Ω)` onto the boundary space.

| Setting | Boundary space | Range | Statement |
|---|---|---|---|
| `𝕋^{n+1}` to a face `𝕋^n` | Besov space of the torus | `s > 0` | [Traces on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-traces.html#thm:trace-torus) |
| half-space to its hyperplane | Besov space of the hyperplane | `s > 0` | [Traces on the half-space](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-half-space-traces.html#thm:half-space-trace-space) |
| bounded Lipschitz domain to `Γ` | chart pieces with first differences | `0 < s < 1` | [Traces on Lipschitz domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bounded-lipschitz-traces.html#thm:boundary-trace-space) |
| compact manifold with boundary to `∂M` | chart pieces of the boundary | `s > 0` | [Traces on manifolds](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-manifold-trace.html#thm:manifold-trace) |
| `H^1(Ω)` of a bounded Lipschitz domain to `Γ`, `p = 2` | `B^{1/2}_{2,2}(Γ)` by chart pieces | `s = 1/2` | [The trace space of H^1](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-lipschitz-domain-h1.html#thm:sobolev-lipschitz-domain-trace) |
| `H^1(Ω)` of a bounded Lipschitz domain to `Γ`, `p = 2` | the `g ∈ L_2(Γ)` with finite Gagliardo form `∫_Γ ∫_Γ \|g(x) - g(y)\|² / \|x - y\|^d dσ dσ`, with equivalent norms | `s = 1/2` | [The Gagliardo form on Γ](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-boundary-slobodeckij.html#thm:trace-space-slobodeckij) |

**Triebel–Lizorkin spaces `F^s_{p,q}`**

| Setting | Descriptions proved equivalent | Range | Statement |
|---|---|---|---|
| `ℝ^d` | Littlewood–Paley blocks: `B^s_{p,min(p,q)} ⊆ F^s_{p,q} ⊆ B^s_{p,max(p,q)}`, so `F^s_{p,p} = B^s_{p,p}` | `s > 0` | [The Besov sandwich](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-besov-sandwich.html#thm:tl-besov-sandwich) |
| `ℝ^d`, `1 < p < ∞`, `1 < q ≤ ∞` | Littlewood–Paley blocks, local means | `0 < s < L` | [Local means](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-local-means.html#thm:tl-local-means) |
| `ℝ^d`, `1 < p < ∞`, `1 < q ≤ ∞` | Littlewood–Paley blocks, ball means of differences | `0 < s < L` | [Ball means](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-ball-means.html#cor:tl-ball-means) |
| `ℝ^d`, `1 < p < ∞`, `1 < q ≤ ∞` | Littlewood–Paley blocks, atoms with coefficients in `f^s_{p,q}` | `0 < s < L` | [Atoms](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-atomic.html#cor:tl-atomic) |
| `ℝ^d`, `1 < p < ∞`, `1 < q ≤ ∞` | the blocks of any two families generated by admissible kernels | `s ∈ ℝ` | [Independence of the family](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-lp-family-independence.html#cor:lp-family-same-spaces) |
| `ℝ^d` | real interpolation of two `F` spaces, Besov spaces | `0 < s₀ < s₁` | [Interpolation](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-interpolation.html#thm:tl-interpolate) |
| `𝕋^d` | the Besov sandwich, so `F^s_{p,p} = B^s_{p,p}` | `s > 0` | [The Besov sandwich on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-triebel-lizorkin.html#thm:torus-tl-besov-sandwich) |
| `𝕋^d` | real interpolation of two `F` spaces, Besov spaces | `0 < s₀ < s₁` | [Interpolation on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-tl-interpolation.html#thm:torus-tl-interpolate) |
| `𝕋^d`, `1 < p < ∞`, `1 < q ≤ ∞` | Littlewood–Paley blocks, local means | `0 < s < L` | [Local means on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-tl-local-means.html#thm:torus-tl-local-means) |

**Sobolev spaces `W^m_p` and Bessel potential spaces `H^{s,p}`**

| Setting | Descriptions proved equivalent | Range | Statement |
|---|---|---|---|
| `ℝ^d`, `d ≥ 1`, `1 < p < ∞` | `L_p = F^0_{p,2}` (square function) | | [The square function theorem](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-square-function.html#cor:square-function-theorem) |
| `ℝ^d`, `d ≥ 1`, `1 < p < ∞` | weak derivatives, `F^m_{p,2}` | `m ∈ ℕ` | [W^m_p = F^m_{p,2}](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-triebel-lizorkin.html#cor:sobolev-triebel-lizorkin) |
| `ℝ^d`, `d ≥ 1`, `1 < p < ∞` | weak derivatives, Bessel potentials `H^{m,p}` (Calderón) | `m ∈ ℕ` | [W^m_p = H^{m,p}](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-lifting.html#cor:sobolev-bessel) |
| `ℝ^d`, `d ≥ 1`, `1 < p < ∞` | `B^m_{p,min(p,2)} ⊆ W^m_p ⊆ B^m_{p,max(p,2)}` | `m ≥ 1` | [The Besov sandwich](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-triebel-lizorkin.html#cor:sobolev-besov-sandwich) |
| `ℝ^d`, `d ≥ 1`, `1 < p < ∞` | `(L_p, W^m_p)_{θ,q} = B^{θm}_{p,q}` | `m ≥ 1`, `0 < θ < 1` | [Interpolation](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-interpolation.html#thm:sobolev-interpolate) |
| `ℝ^d`, `p = 2` | Mathlib's `H^s`, Littlewood–Paley blocks (`F^s_{2,2}`), and `B^s_{2,2}` for `s > 0` | `s ≥ 0` | [H^s = B^s_{2,2}](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-two-littlewood-paley.html#cor:sobolev-two-besov) |
| `ℝ^d`, `d ≥ 1`, `p = 2` | weak derivatives, `B^m_{2,2}` | `m ≥ 1` | [W^m_2 = B^m_{2,2}](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-triebel-lizorkin.html#cor:sobolev-integer-two-besov) |
| `ℝ^d`, `d ≥ 1`, `1 < p < ∞` | Mathlib's `H^{s,p}`, `F^s_{p,2}` of tempered distributions | `s ∈ ℝ` | [H^{s,p} = F^s_{p,2}](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-distributions.html#thm:bessel-triebel-lizorkin-distr) |
| `ℝ^d`, `1 < p < ∞` | `u ∈ H^{s+1,p}` iff `u ∈ H^{s,p}` and `∂_v u ∈ H^{s,p}` for all `v` | `s ∈ ℝ` | [Derivatives in H^{s,p}](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-multipliers.html#thm:bessel-potential-derivatives) |
| `ℝ^d`, `d ≥ 1`, `1 < p < ∞` | `(H^{s₀,p}, H^{s₁,p})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}` | `0 < s₀ < s₁` | [Interpolation of H^{s,p}](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-interpolation.html#thm:bessel-potential-interpolate) |
| `𝕋^d`, `p = 2` | weak derivatives, weighted Fourier coefficients, `B^m_{2,2}`, `H^m` | `m ≥ 1` | [W^m_2 on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-weak-derivatives.html#thm:weak-sobolev) |
| `𝕋^d`, `d ≥ 1`, `1 < p < ∞` | weak derivatives, `F^m_{p,2}`; for `m = 0`, `L_p = F^0_{p,2}` | `m ∈ ℕ` | [W^m_p = F^m_{p,2} on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-sobolev-triebel-lizorkin.html#cor:torus-sobolev-triebel-lizorkin) |
| `𝕋^d`, `d ≥ 1`, `1 < p < ∞` | weak derivatives, local means | `1 ≤ m < L` | [Local means on the torus](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-sobolev-triebel-lizorkin.html#cor:torus-sobolev-local-means) |
| bounded Lipschitz domain, `d ≥ 1`, `1 < p < ∞` | weak derivatives on `Ω`, restrictions of `W^m_p(ℝ^d)` | `m ∈ ℕ` | [Extension of higher order](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-higher-sobolev-extension.html#thm:higher-sobolev-extension) |
| bounded Lipschitz domain, `d ≥ 1`, `1 ≤ p ≤ ∞` | weak derivatives on `Ω`, restrictions of `W^1_p(ℝ^d)` by a bounded linear extension operator | `m = 1` | [Extension by reflection](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-reflection-extension.html#thm:reflection-extension-operator) |
| bounded Lipschitz domain, `p = 2` | restrictions of `H^1(ℝ^d)`, weak derivatives | `m = 1` | [H^1(Ω) = W^1_2(Ω)](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-extension.html#cor:sobolev-extension-two) |
| bounded Lipschitz domain, `p = 2` | restrictions of `H^1(ℝ^d)`, intrinsic differences of order `r ≥ 2` | `m = 1` | [H^1(Ω) by differences](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-lipschitz-domain-h1.html#thm:sobolev-lipschitz-domain-intrinsic) |
| compact manifold, `p = 2` | chart Sobolev space `H^1_A(M)`, `B^1_{2,2}(M)` | | [H^1_A(M) = B^1_{2,2}(M)](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-chart-sobolev.html#thm:chart-sobolev-besov) |

**Approximation spaces `A^s_q`**

| Setting | Descriptions proved equivalent | Range | Statement |
|---|---|---|---|
| scheme in a normed space, Jackson and Bernstein of order `r` | approximation, real interpolation `(X, Y)_{s/r,q}` | `0 < s < r` | [The representation theorem](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-continuous-k-method.html#cor:representation-continuous-k-method) |
| scheme with a modulus, Jackson and inverse inequality of order `θ` | approximation, modulus of smoothness | `0 ≤ s < θ` | [Approximation and moduli](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-moduli-abstract.html#thm:modulus-coincidence) |
| scheme in a normed space | real interpolation of two approximation spaces (reiteration) | `0 < s₀ < s₁` | [Reiteration](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-approximation-spaces-interpolate.html#thm:approximation-spaces-reiteration) |
| scheme in a Banach space | approximation, block decompositions | `s > 0` | [Block decompositions](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-decompositions.html#thm:block-decomposition) |
| Hilbert basis with levels | approximation, dyadic blocks of coefficients | `s > 0` | [Spectral coefficients](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-spectral.html#thm:spectral-coefficients) |
| `L_p` of a filtration with dense union | approximation, martingale differences | `s > 0` | [Martingale differences](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-filtrations.html#thm:martingale) |
| finite measure space, `1 ≤ p ≤ ∞` | real interpolation of two Besov spaces of a scheme | `0 < s₀ < s₁` | [Interpolation of Besov spaces](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-besov-interpolation.html#thm:besov-interpolate) |
| bounded open set | `(L_2, H^1_0)_{θ,q}`, approximation by Dirichlet eigenfunctions | `0 < θ < 1` | [Dirichlet eigenfunctions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-dirichlet-eigenbasis.html#cor:dirichlet-interpolation) |
| bounded Lipschitz domain, `d ≥ 1` | `(L_2, W^1_2)_{θ,q}`, approximation by Neumann eigenfunctions | `0 < θ < 1` | [Neumann eigenfunctions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-neumann-eigenbasis.html#cor:neumann-interpolation) |

## Why several descriptions

Applications use different descriptions of the same space: finite element methods use weak
derivatives, wavelet methods use coefficients, approximation theory uses best approximation and
moduli of smoothness, and harmonic analysis uses Littlewood–Paley blocks. The proof that two
descriptions agree is often long and technical. With the equivalences above, a statement proved
in one description holds in the others, in the stated ranges.

## Main results

`V` is a finite-dimensional real inner product space, such as `ℝ^d`, of dimension `n`.

* **Approximation spaces are interpolation spaces.** Let `ι : Y → X` be a bounded linear map
  of real normed spaces and `(A_n)` a scheme in `X` with Jackson's inequality
  `E_n(ι y) ≤ C n^(-r) ‖y‖` and Bernstein's inequality (every `a ∈ A_n` is `ι y` with
  `‖y‖ ≤ C n^r ‖a‖`), `n ≥ 1`. For `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q = (X, Y)_{s/r,q}` for the
  continuous K-method with `K(t, f) = inf_y (‖f - ι y‖ + t ‖y‖)`
  (`ApproximationScheme.memApprox_iff_memKMethod`).
* **Besov spaces on `ℝ^d`.** Let `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `0 < s < r`. For `f ∈ L_p(V)` these
  are equivalent: `f ∈ A^s_q` of the band-limited functions; `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`;
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (`Rd.memApprox_bandScheme_iff_modulus`,
  `Rd.littlewoodPaleyNorm_lt_top_iff_modulus`).
* **Daubechies wavelets.** Let `φ`, `ψ` be the D4 scaling function and wavelet, `1 ≤ p < ∞`,
  `1 ≤ q ≤ ∞` and `0 < s < 2 - log₂(1 + √3) ≈ 0.55`. Then `f ∈ L_p(ℝ)` has
  `‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s+1/2-1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
  (`Daubechies.besov_iff_coeff_d4`).
* **Sobolev, Bessel potential and Triebel–Lizorkin spaces.** Let `n ≥ 1` and `1 < p < ∞`. Every
  `f ∈ L_p(V)` has `‖f‖_{F^0_{p,2}} ≤ C ‖f‖_p` and `‖f‖_p ≤ C' ‖f‖_{F^0_{p,2}}`, with finite
  constants depending on `V` and `p` (`Rd.triebelLizorkinNorm_zero_two_le`,
  `Rd.enorm_le_triebelLizorkinNorm_zero_two`). For `m ∈ ℕ`, `f ∈ L_p(V)` lies in `W^m_p(V)` iff
  in `F^m_{p,2}(V)` iff in `H^{m,p}(V)`, the last being Calderón's theorem
  (`Rd.memSobolev_iff_memTriebelLizorkin`, `Rd.memSobolev_iff_memSobolev_bessel`). For real `s`,
  a tempered distribution lies in `H^{s,p}(V)` iff it lies in `F^s_{p,2}(V)`
  (`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`).
* **Sobolev embeddings.** Let `n ≥ 1`, `1 < p < ∞`, `m ∈ ℕ` and `f ∈ W^m_p(V)`. If `r < ∞` and
  `1/r = 1/p - m/n`, then `f` agrees almost everywhere with a function in `L_r(V)`
  (`Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`); if `m > n/p`, with a bounded continuous function
  (`Rd.exists_boundedContinuous_ae_eq_of_memSobolev`). For `1 ≤ p < ∞`, `r < ∞`,
  `1/r = 1/p - 1/n` and `f ∈ W^1_p(V)`, some `u ∈ L_r(V)` equals `f` almost everywhere with
  `‖u‖_r ≤ C ∑_k ‖∂_k f‖_p`, `C` Mathlib's Gagliardo–Nirenberg–Sobolev constant
  (`Rd.exists_memLp_ae_eq_of_memSobolev_one`).
* **Bounded Lipschitz domains.** Let `Ω ⊆ V` be a bounded open set that agrees near each
  boundary point with the region above a Lipschitz graph (`Rd.isBoundedLipschitzDomain_iff_exists`),
  `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `0 < s < r`. Then `f ∈ L_p(V)` agrees on `Ω` with some `F` with
  `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, with differences inside `Ω`; some
  such `F` has quasi-norm at most `C` times the intrinsic one, one `C < ∞` for all `f`
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn`,
  `Rd.BoundedLipschitzDomain.exists_besov_extension_le`). For `1 < p < ∞` and every `m`, every
  `f ∈ L_p(Ω)` with weak derivatives of order at most `m` in `L_p(Ω)` agrees on `Ω` with some
  `F ∈ W^m_p(V)` (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_order`); for
  `m = 1`, `n ≥ 1` and `1 ≤ p ≤ ∞` a bounded linear operator does this
  (`Rd.BoundedLipschitzDomain.sobolevExtensionL`).
* **Traces.** Let `Ω` be as above, with boundary `Γ` and surface measure `σ`, the
  `(n-1)`-dimensional Hausdorff measure on `Γ`. In the restrictions `H^1(Ω)` of `H^1(V)`, the
  kernel `ker γ` of the boundary trace is `H^1_0(Ω)`, the closure of the restricted test
  functions (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`). Let `H^{1/2}(Γ)` be the
  orthogonal complement of `ker γ` in `H^1(Ω)` and `τ` its trace into `L_2(Γ)`. Then `g ∈ L_2(Γ)`
  is `τ t` for some `t` iff `∫_Γ ∫_Γ |g(x) - g(y)|² / |x - y|^n dσ(x) dσ(y) < ∞`, and `‖t‖²` is
  equivalent to `‖τ t‖²_{L_2(Γ)}` plus this form
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff_slobodeckij`,
  `Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`).
* **Eigenfunction expansions.** For an orthonormal basis of weak eigenfunctions `e_i` with
  eigenvalues `λ_i`, let `A_k` be the span of the `e_i` with `⌊√(1 + λ_i)⌋ < k`, and let
  `0 < θ < 1`, `1 ≤ q ≤ ∞`. On `Ω` as above, `n ≥ 1`, with the Neumann eigenbasis, `f ∈ L_2(V)`
  has `f|_Ω ∈ A^θ_q` iff `‖f‖_{L_2(Ω)} + ‖(2^(kθ) ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_q} < ∞`, for every
  `r ≥ 1` (`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_iff`). Let `M` be a compact
  Hausdorff smooth manifold of dimension `n ≥ 1`, without boundary, with boundary or with corners,
  with a smooth measure `μ`. For `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, `B^s_{p,q}(M)`, defined by
  the chart pieces of a Besov atlas, is the same for every atlas (`Manifold.memBesov_iff`). For
  the eigenbasis of the chart form `a_A(u, w) = ∑_{k,j} ⟨∂_j P_k u, ∂_j P_k w⟩` of an atlas `A`,
  `f ∈ L_2(μ)` lies in `A^θ_q` iff `f ∈ B^θ_{2,q}(M)`
  (`Manifold.BesovAtlas.memApprox_chartScheme_iff`). In the principal part
  `∑_k (ψ_k ∘ κ_k⁻¹)² |∇(u ∘ κ_k⁻¹)|²` of the chart form the weights satisfy `∑_k ψ_k² ≥ 1/N` for `N`
  charts (`Manifold.BesovAtlas.inv_card_le_sum_sq_psi`), a step toward its uniform
  ellipticity in the charts.

## Organisation

The library `ApproximationSpaces` holds the abstract theory: schemes, the spaces `A^s_q`, real
interpolation of couples (`Interpolation/`) and decompositions (`Decompositions/`). The library
`FunctionSpaces` holds the function spaces in folders by setting: `Analysis/`, `MeasureSpaces/`,
`Rd/` (one folder per characterisation), `Torus/`, `Domains/` (intervals, the cube, Lipschitz
domains, traces, eigenbases, manifolds) and `Wavelets/`. The block documents in
[`docs/`](docs/) state every result with its Lean name and list the files; the blueprint gives
the proofs. [MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed, and
[docs/FEECFoundations.md](docs/FEECFoundations.md) describes what a FEEC/BEEC library can build on.

## What is left to do

* Interpolation: Lorentz spaces, real Riesz–Thorin, off-diagonal Marcinkiewicz, J- and complex
  method.
* `n`-term approximation from a Hilbert basis, and the quasi-Banach range `0 < p, q < 1`.
* Triebel–Lizorkin spaces with `p = 1` or `q = 1`, and ball means and atoms on the torus.
* Sobolev spaces: Jawerth–Franke with Besov targets, Hardy–Littlewood–Sobolev, Trudinger, Mihlin
  multipliers with finitely many derivatives (Riesz transforms).
* Manifolds with corners: the cube as an example, traces on faces, products of models.
* Higher smoothness: Marchaud's inequality, splines on domains, sharp Daubechies exponents,
  tensor wavelets.
* Extension operators for `W^m_p` of every order, and Stein's universal operator.
* Eigenbases: elliptic regularity, the local Weyl law, spectral `B^s_{p,q}` for `p ≠ 2` or
  `s ≥ 1`, the two-sided description of the Dirichlet approximation spaces, and the
  Laplace–Beltrami operator.

## Building

Requires [`elan`](https://github.com/leanprover/elan); Lean and Mathlib are pinned to
`v4.35.0-rc2`. Run `lake exe cache get` and then `lake build` from inside this folder, and do not
run `lake update`, which re-resolves the dependencies. The blueprint follows
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) (`leanblueprint pdf`,
`leanblueprint web`). GitHub Actions builds the project and the blueprint on every push, checks
that every `\lean{...}` of the blueprint resolves, and publishes both.

## AI assistance

The formalisation was written with Claude Code, and Lean checks every statement and proof. The
mathematical design, the choice of statements and the review of what the proofs say are the
author's; the column "Human-checked" in the tables of [`docs/`](docs/) records that review.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

The [blueprint's bibliography](https://mario-ullrich.github.io/Lean-FunctionSpaces/) lists all
sources. The essential ones:

* J. Bergh, J. Löfström, *Interpolation Spaces. An Introduction*, Springer-Verlag, 1976.
* A. P. Calderón, *Lebesgue spaces of differentiable functions and distributions*, Proc. Sympos.
  Pure Math. **4** (1961), 33–49.
* I. Daubechies, *Ten Lectures on Wavelets*, SIAM, 1992.
* R. A. DeVore, G. G. Lorentz, *Constructive Approximation*, Springer-Verlag, 1993.
* R. A. DeVore, V. A. Popov, *Interpolation of Besov spaces*, Trans. Amer. Math. Soc. **305**
  (1988), 397–414.
* C. Fefferman, E. M. Stein, *Some maximal inequalities*, Amer. J. Math. **93** (1971), 107–115.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Springer, 2014.
* J. Johnsen, W. Sickel, *A direct proof of Sobolev embeddings for quasi-homogeneous
  Lizorkin–Triebel spaces with mixed norms*, J. Funct. Spaces Appl. **5** (2007), 183–198.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University
  Press, 2000.
* S. M. Nikol'skii, *Approximation of Functions of Several Variables and Imbedding Theorems*,
  Springer-Verlag, 1975.
* A. Pietsch, *Approximation spaces*, J. Approx. Theory **32** (1981), 115–134.
* V. S. Rychkov, *On restrictions and extensions of the Besov and Triebel–Lizorkin spaces with
  respect to Lipschitz domains*, J. London Math. Soc. (2) **60** (1999), 237–257.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  University Press, 1970.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983.
* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992.

Lean projects whose code is mirrored here, with credit:

* L. Becker et al., *Formalizing Carleson's theorem in Lean*, preprint, 2026,
  [arXiv:2609.31334](https://arxiv.org/abs/2609.31334), and its blueprint,
  [arXiv:2405.06423](https://arxiv.org/abs/2405.06423): weak and strong type, real
  interpolation and the Calderón–Zygmund decomposition.
* F. van Doorn, J. Portegies, M. Rothgang, L. Viana Reis, *MultilinearInterpolation*, 2026,
  [lua-vr/MultilinearInterpolation](https://github.com/lua-vr/MultilinearInterpolation): couples
  as two extended quasi-norms on one group.
* The Tau Ceti contributors, *TauCeti*, 2026,
  [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti): eigenbases of compact
  self-adjoint operators, the Japanese bracket and Mathlib's Bessel potential spaces.
