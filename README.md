# Characterizations of Function Spaces in Lean 4 / Mathlib

This project formalises function spaces of smooth functions in Lean 4 and Mathlib: Besov,
Triebel–Lizorkin, Sobolev and Bessel potential spaces. Each space has several classical
descriptions, and the project proves that they define the same space, on `ℝ^d`, the torus,
intervals and the cube, bounded Lipschitz domains and compact manifolds. Wherever possible, a
space is also identified with an approximation space: the functions whose error of best
approximation by a fixed scheme (band-limited functions, trigonometric polynomials, splines,
wavelets, eigenfunctions) decays at a given rate. This form makes the general methods of
approximation theory available, such as interpolation, embeddings, decompositions and traces,
and it is the form numerical analysis needs. The project has about 120 000 lines of Lean in 303
files and contains no `sorry`.

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

The spaces are studied in these settings:

* `ℝ^d`, with the Daubechies wavelets on `ℝ` and their tensor products on `ℝ^d`;
* the torus `𝕋^d`;
* the interval `[0, 1]` and the cube `[0, 1]^d`;
* Lipschitz graph domains, bounded Lipschitz domains and bounded smooth domains in `ℝ^d`;
* compact manifolds without boundary, with boundary or with corners.

On a domain the descriptions use the values of `f` in the domain (intrinsic differences, weak
derivatives, eigenfunction expansions) or extensions to `ℝ^d` (restrictions). A compact manifold
carries its spaces in the charts of an atlas and a smooth measure, that is, a measure with a
continuous positive density in every chart.

An approximation scheme in a normed space `X` is a sequence of sets `{0} = A_0 ⊆ A_1 ⊆ ⋯` with
`c A_n ⊆ A_n` and `A_m + A_n ⊆ A_{m+n}`. With the error of best approximation
`E_n(f) = inf { ‖f - a‖ : a ∈ A_n }`, the approximation space `A^s_q` consists of the `f` with
`(n^(s - 1/q) E_{n-1}(f))_{n ≥ 1} ∈ ℓ_q` (Pietsch 1981). For trigonometric polynomials, splines,
band-limited functions, wavelets and eigenfunctions these are Besov spaces. The theory of spaces
of a scheme on a finite measure space has the torus as its concrete instance; the other settings
prove their characterisations directly.

## Why several descriptions

Applications use different descriptions of the same space: finite element methods use weak
derivatives, wavelet methods use coefficients, approximation theory uses best approximation and
moduli of smoothness, and harmonic analysis uses Littlewood–Paley blocks. The proof that two
descriptions agree is often long and technical. With the equivalences below, a statement proved
in one description holds in the others, in the stated ranges.

## The map of characterisations

Each table collects descriptions of one kind of space. A row names a description, and each
setting in it links to the blueprint statement that proves the description equivalent to another
one of the same space; the blueprint names the Lean declarations. Throughout `1 ≤ q ≤ ∞`, and
`1 ≤ p < ∞` unless an entry says otherwise. Ranges `0 < s < r` or `0 < s < L` refer to
differences, local means or atoms of order `r` or `L`. The blueprint chapter
[The representations of Besov spaces][representations] explains what each description measures
and how they differ.

[representations]: https://mario-ullrich.github.io/Lean-FunctionSpaces/chap-representations.html

**Besov spaces `B^s_{p,q}`**

| Characterization by | Settings |
|---|---|
| differences (moduli of smoothness) | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-besov-differences.html#thm:rd-besov), [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-lp-moduli.html#thm:torus-lp-moduli) (`0 < s < r`); [`[0, 1]`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spline-jackson-coincidence.html#thm:spline-besov), [`[0, 1]^d`, isotropic or coordinate differences](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-iso-modulus.html#thm:iso-besov) (`0 ≤ s < r - 1 + 1/p`) |
| intrinsic differences | [Lipschitz graph domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-graph-intrinsic-differences.html#thm:graph-besov), [bounded Lipschitz domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bounded-lipschitz-domains.html#thm:bounded-lipschitz-besov), [bounded smooth domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-smooth-domain-charts.html#thm:smooth-domain-besov) (`0 < s < r`) |
| restrictions of `B^s_{p,q}(ℝ^d)` | [Lipschitz graph domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-graph-intrinsic-differences.html#thm:graph-besov), [bounded Lipschitz domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bounded-lipschitz-domains.html#thm:bounded-lipschitz-besov) (`0 < s < r`) |
| Littlewood–Paley blocks | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-besov-differences.html#thm:rd-besov), [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-lp-blocks.html#thm:torus-lp-besov) |
| dyadic blocks of Fourier coefficients | [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-torus.html#thm:torus-coefficients) (`p = 2`) |
| local means | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-local-means.html#thm:local-means) (`0 < s < L`) |
| atoms with coefficients in `b^s_{p,q}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-atomic-decompositions.html#thm:atomic-characterisation) (`0 < s < L`) |
| wavelet coefficients | [`ℝ`, Daubechies D4](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-daubechies-besov-coefficients.html#thm:daub-besov-d4) (`0 < s < 2 - log₂(1 + √3)`), [`ℝ^d`, tensor Daubechies](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-daub-rd-besov.html#thm:daub-rd-besov) (`0 < s < min(θ, N)`), [`[0, 1]`, multiwavelets](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-multiwavelets.html#thm:multiwavelet-besov) (`0 < s < 1/p`) |
| the Gagliardo form, `W^{s,p} = B^s_{p,p}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-slobodeckij.html#thm:sobolev-slobodeckij-besov) (`0 < s < 1`) |
| real interpolation of two difference spaces | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-besov-interpolation.html#thm:rd-besov-interpolate) (`0 < s₀ < s₁ < r`) |
| chart pieces | [bounded smooth domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-smooth-domain-charts.html#thm:smooth-domain-besov), [compact manifolds, any two Besov atlases](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-manifold-besov.html#def:manifold-besov) |
| eigenfunction expansions | [bounded Lipschitz domains, Neumann](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spectral-besov-domains.html#thm:spectral-besov-neumann), [compact manifolds, a chart form](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spectral-besov-manifold.html#thm:spectral-besov-manifold) (`d ≥ 1`, `p = 2`, `0 < s < 1`) |
| best approximation | the table of approximation spaces below |
| mixed differences, mixed local means, tensor Littlewood–Paley blocks | [`ℝ^d`, dominating mixed smoothness](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-mixed-lp-blocks.html#thm:mixed-lp) (`0 < s < L`) |

**Triebel–Lizorkin spaces `F^s_{p,q}`**, defined by Littlewood–Paley blocks. Here `1 < p < ∞`
and `1 < q ≤ ∞` unless an entry says otherwise.

| Characterization by | Settings |
|---|---|
| Littlewood–Paley blocks of any admissible family | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-lp-family-independence.html#cor:lp-family-same-spaces) (`s ∈ ℝ`) |
| local means | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-local-means.html#thm:tl-local-means), [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-tl-local-means.html#thm:torus-tl-local-means) (`0 < s < L`) |
| ball means of differences | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-ball-means.html#cor:tl-ball-means) (`0 < s < L`) |
| atoms with coefficients in `f^s_{p,q}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-atomic.html#cor:tl-atomic) (`0 < s < L`) |
| Besov spaces: `B^s_{p,min(p,q)} ⊆ F^s_{p,q} ⊆ B^s_{p,max(p,q)}`, so `F^s_{p,p} = B^s_{p,p}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-besov-sandwich.html#thm:tl-besov-sandwich), [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-triebel-lizorkin.html#thm:torus-tl-besov-sandwich) (`1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `s > 0`) |
| real interpolation: `(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-interpolation.html#thm:tl-interpolate), [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-tl-interpolation.html#thm:torus-tl-interpolate) (`1 ≤ p < ∞`, `0 < s₀ < s₁`) |

**Sobolev spaces `W^m_p`**, defined by weak derivatives. Here `1 < p < ∞`, `m ∈ ℕ` and `d ≥ 1`
unless an entry says otherwise.

| Characterization by | Settings |
|---|---|
| Littlewood–Paley blocks: `W^m_p = F^m_{p,2}`, and `L_p = F^0_{p,2}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-triebel-lizorkin.html#cor:sobolev-triebel-lizorkin), [`ℝ^d`, the square function theorem](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-square-function.html#cor:square-function-theorem), [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-sobolev-triebel-lizorkin.html#cor:torus-sobolev-triebel-lizorkin) |
| Bessel potentials: `W^m_p = H^{m,p}` (Calderón) | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-lifting.html#cor:sobolev-bessel) |
| local means | [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-sobolev-triebel-lizorkin.html#cor:torus-sobolev-local-means) (`1 ≤ m < L`) |
| Besov spaces: `B^m_{p,min(p,2)} ⊆ W^m_p ⊆ B^m_{p,max(p,2)}`, and `W^m_2 = B^m_{2,2}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-triebel-lizorkin.html#cor:sobolev-besov-sandwich), [`ℝ^d`, `p = 2`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-triebel-lizorkin.html#cor:sobolev-integer-two-besov), [`𝕋^d`, `p = 2`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-weak-derivatives.html#thm:weak-sobolev) (`m ≥ 1`) |
| weighted Fourier coefficients | [`𝕋^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-weak-derivatives.html#thm:weak-sobolev) (`p = 2`) |
| real interpolation: `(L_p, W^m_p)_{θ,q} = B^{θm}_{p,q}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-interpolation.html#thm:sobolev-interpolate) (`m ≥ 1`, `0 < θ < 1`) |
| restrictions of `W^m_p(ℝ^d)` | [bounded Lipschitz domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-higher-sobolev-extension.html#thm:higher-sobolev-extension), with [a bounded linear extension operator for `m = 1`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-reflection-extension.html#thm:reflection-extension-operator) (`1 ≤ p ≤ ∞`); [`H^1(Ω) = W^1_2(Ω)`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-extension.html#cor:sobolev-extension-two) (`p = 2`) |
| intrinsic differences | [`H^1(Ω)` of a bounded Lipschitz domain](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-lipschitz-domain-h1.html#thm:sobolev-lipschitz-domain-intrinsic) (`p = 2`, order `r ≥ 2`) |
| chart pieces | [compact manifolds, `H^1_A(M) = B^1_{2,2}(M)`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-chart-sobolev.html#thm:chart-sobolev-besov) (`p = 2`) |

**Bessel potential spaces `H^{s,p}`**, Mathlib's spaces of tempered distributions. Here
`1 < p < ∞` and `d ≥ 1` unless an entry says otherwise.

| Characterization by | Settings |
|---|---|
| Littlewood–Paley blocks: `H^{s,p} = F^s_{p,2}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-distributions.html#thm:bessel-triebel-lizorkin-distr) (`s ∈ ℝ`), [`ℝ^d`, `p = 2`, and `H^s = B^s_{2,2}` for `s > 0`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-two-littlewood-paley.html#cor:sobolev-two-besov) (`s ≥ 0`) |
| derivatives: `u ∈ H^{s+1,p}` iff `u` and every `∂_v u` lie in `H^{s,p}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-multipliers.html#thm:bessel-potential-derivatives) (`s ∈ ℝ`) |
| real interpolation: `(H^{s₀,p}, H^{s₁,p})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}` | [`ℝ^d`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-interpolation.html#thm:bessel-potential-interpolate) (`0 < s₀ < s₁`) |
| tensor Daubechies wavelet coefficients | [`ℝ^d`, `p = 2`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-daub-rd-besov.html#cor:daub-rd-sobolev) (`0 < s < 3 - log₂ 3` for masks of order three) |

**Traces.** The trace maps `B^{s+1/p}_{p,q}` of the domain onto `B^s_{p,q}` of the boundary, and
`H^1(Ω)` onto a space on the boundary `Γ`. The rows describe the space on the boundary.

| Boundary space described by | Settings |
|---|---|
| the Besov space of the boundary | [`𝕋^{n+1}` to a face `𝕋^n`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-traces.html#thm:trace-torus), [the half-space to its hyperplane](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-half-space-traces.html#thm:half-space-trace-space) (`s > 0`) |
| chart pieces | [bounded Lipschitz domains](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bounded-lipschitz-traces.html#thm:boundary-trace-space) (first differences, `0 < s < 1`), [compact manifolds with boundary](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-manifold-trace.html#thm:manifold-trace) (`s > 0`), [`H^1(Ω)` of a bounded Lipschitz domain, `B^{1/2}_{2,2}(Γ)`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-lipschitz-domain-h1.html#thm:sobolev-lipschitz-domain-trace) |
| the Gagliardo form `∫_Γ ∫_Γ \|g(x) - g(y)\|² / \|x - y\|^d dσ dσ` | [`H^1(Ω)` of a bounded Lipschitz domain](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-boundary-slobodeckij.html#thm:trace-space-slobodeckij) (equivalent norms) |

**Approximation spaces `A^s_q`.** Each row names a space and the scheme whose approximation
spaces it is.

| Space | Approximation space of |
|---|---|
| `B^s_{p,q}(ℝ^d)` | [band-limited functions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rd-besov-differences.html#thm:rd-besov) (`s > 0`), [tensor Daubechies scaling spaces](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-daub-rd-besov.html#thm:daub-rd-approx-modulus) (`0 < s < min(θ, N)`) |
| `B^s_{p,q}(𝕋^d)` | [trigonometric polynomials](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-lp-moduli.html#thm:torus-lp-moduli) (`s > 0`) |
| `B^s_{p,q}[0, 1]` | [dyadic splines of order `r`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spline-jackson-coincidence.html#thm:spline-besov) (`0 < s < r - 1 + 1/p`), [dyadic piecewise polynomials](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-multiwavelets.html#thm:multiwavelet-besov) (`0 < s < 1/p`) |
| `B^s_{p,q,1}[0, 1]`, `0 < p < 1`, by the first modulus | [dyadic step functions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-steps-below-one.html#thm:steps-besov-below-one) (`0 < s < 1/p`) |
| `B^θ_{τ,τ}[0, 1]`, `θ = 1/τ - 1/2` | [`n`-term combinations of Haar functions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-haar-below-one.html#thm:haar-nterm-besov-all), a nonlinear scheme in `L_2[0, 1]` (`2/3 < τ < 2`; for `0 < τ ≤ 2/3` the space of the first modulus) |
| `B^s_{p,q}([0, 1]^d)` | [tensor splines of order `r`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-iso-modulus.html#thm:iso-besov) (`0 < s < r - 1 + 1/p`) |
| `F^s_{p,p}(ℝ^d)`, `F^s_{p,p}(𝕋^d)` | band-limited functions and trigonometric polynomials, since [`F^s_{p,p}(ℝ^d) = B^s_{p,p}(ℝ^d)`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-tl-besov-sandwich.html#thm:tl-besov-sandwich) and [`F^s_{p,p}(𝕋^d) = B^s_{p,p}(𝕋^d)`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-triebel-lizorkin.html#thm:torus-tl-besov-sandwich) (`s > 0`) |
| `W^{s,p}(ℝ^d)`, Sobolev–Slobodeckij | [band-limited functions, `q = p`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-slobodeckij.html#thm:sobolev-slobodeckij-besov) (`0 < s < 1`) |
| `H^s(ℝ^d)` | [band-limited functions, `q = 2`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-two-littlewood-paley.html#cor:sobolev-two-besov) (`s > 0`) |
| `W^m_2(ℝ^d)`, `W^m_2(𝕋^d)` | [band-limited functions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-triebel-lizorkin.html#cor:sobolev-integer-two-besov) (`d ≥ 1`), [trigonometric polynomials](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-torus-weak-derivatives.html#thm:weak-sobolev), `q = 2` (`m ≥ 1`) |
| `B^θ_{2,q}(Ω)` of a bounded Lipschitz domain | [Neumann eigenfunctions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spectral-besov-domains.html#thm:spectral-besov-neumann) (`d ≥ 1`, `0 < θ < 1`) |
| `(L_2(Ω), W^1_2(Ω))_{θ,q}` of a bounded Lipschitz domain | [Neumann eigenfunctions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-neumann-eigenbasis.html#cor:neumann-interpolation) (`d ≥ 1`, `0 < θ < 1`) |
| `(L_2(Ω), H^1_0(Ω))_{θ,q}` of a bounded open set | [Dirichlet eigenfunctions](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-dirichlet-eigenbasis.html#cor:dirichlet-interpolation) (`0 < θ < 1`) |
| `B^θ_{2,q}(M)` of a compact manifold | [eigenfunctions of a chart form](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-spectral-besov-manifold.html#thm:spectral-besov-manifold) (`d ≥ 1`, `0 < θ < 1`) |
| `(X, Y)_{s/r,q}` for a bounded linear map `Y → X` | [every scheme in `X` with Jackson and Bernstein inequalities of order `r`](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-continuous-k-method.html#cor:representation-continuous-k-method) (`0 < s < r`) |

For a general scheme the project describes `A^s_q`

* by a [modulus of smoothness](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-moduli-abstract.html#thm:modulus-coincidence), under Jackson's and an inverse
  inequality of order `θ` (`0 ≤ s < θ`), also in quasi-normed groups, through the E-functional
  (`InterpCouple.ModulusData.eNormDyadic_lt_top_iff`);
* by [block decompositions](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-decompositions.html#thm:block-decomposition), in a Banach space (`s > 0`);
* by [dyadic blocks of coefficients](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-spectral.html#thm:spectral-coefficients), for a Hilbert basis with
  levels (`s > 0`);
* by [coefficients in `ℓ_τ`](
  https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-nterm-hilbert-basis.html#thm:stechkin),
  for `n`-term approximation from a Hilbert basis (`s = 1/τ - 1/2`, `q = τ`, `0 < τ < 2`);
* by [martingale differences](https://mario-ullrich.github.io/Lean-FunctionSpaces/ch-filtrations.html#thm:martingale), in `L_p` of a filtration with dense union, and
  on `[0, 1]` by [Haar coefficients](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-haar.html#thm:haar) and
  [multiwavelet coefficients](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-multiwavelets.html#thm:multiwavelet-besov) (`s > 0`);
* by real interpolation: [two approximation spaces](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-approximation-spaces-interpolate.html#thm:approximation-spaces-reiteration)
  interpolate to a third (reiteration, `0 < s₀ < s₁`), and so do
  [two Besov spaces of a scheme](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-besov-interpolation.html#thm:besov-interpolate) on a finite measure space,
  `1 ≤ p ≤ ∞`.

## Main results

`V` is a finite-dimensional real inner product space of dimension `d`, such as `ℝ^d`.

* **Besov spaces on `ℝ^d`.** Let `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `0 < s < r`. For `f ∈ L_p(V)` these
  are equivalent: `f ∈ A^s_q` of the band-limited functions; `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`;
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (`Rd.memApprox_bandScheme_iff_modulus`,
  `Rd.littlewoodPaleyNorm_lt_top_iff_modulus`).
* **Daubechies wavelets.** Let `φ`, `ψ` be the D4 scaling function and wavelet, `1 ≤ p < ∞`,
  `1 ≤ q ≤ ∞` and `0 < s < 2 - log₂(1 + √3) ≈ 0.55`. Then `f ∈ L_p(ℝ)` has
  `‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s+1/2-1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
  (`Daubechies.besov_iff_coeff_d4`).
* **Tensor Daubechies wavelets on `ℝ^d`.** Let `φ`, `ψ` be the scaling function and wavelet of a
  mask of order `N ≥ 2` with `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1`, `Φ = φ ⊗ ⋯ ⊗ φ` and, for
  nonempty `e ⊆ {1, …, d}`, `Ψ^e` the tensor product with `ψ` in the coordinates of `e` and `φ`
  in the others; let `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `0 < s < min(θ, N)` (every such `θ` is at most
  `N`). Then `f ∈ L_p(ℝ^d)`, with the maximum norm on `ℝ^d`, has
  `‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s+d/2-d/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
  (`Daubechies.tensor_besov_iff_coeff`). For masks of order three and `0 < s < 3 - log₂ 3`,
  `u ∈ H^s(V)` iff `u` is an `L_2` function with
  `∑_k |⟨u, Φ(· - k)⟩|² + ∑_j 2^(2js) ∑_{e,k} |⟨u, Ψ^e_{j,k}⟩|² < ∞` in the coordinates of a
  fixed orthonormal basis (`Daubechies.memSobolev_two_iff_tensorCoeff_order_three`).
* **Sobolev, Bessel potential and Triebel–Lizorkin spaces.** Let `d ≥ 1` and `1 < p < ∞`. Every
  `f ∈ L_p(V)` has `‖f‖_{F^0_{p,2}} ≤ C ‖f‖_p` and `‖f‖_p ≤ C' ‖f‖_{F^0_{p,2}}`, with finite
  constants depending on `V` and `p` (`Rd.triebelLizorkinNorm_zero_two_le`,
  `Rd.enorm_le_triebelLizorkinNorm_zero_two`). For `m ∈ ℕ`, `f ∈ L_p(V)` lies in `W^m_p(V)` iff
  in `F^m_{p,2}(V)` iff in `H^{m,p}(V)`, the last being Calderón's theorem
  (`Rd.memSobolev_iff_memTriebelLizorkin`, `Rd.memSobolev_iff_memSobolev_bessel`). For real `s`,
  a tempered distribution lies in `H^{s,p}(V)` iff it lies in `F^s_{p,2}(V)`
  (`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`).
* **Sobolev embeddings.** Let `d ≥ 1`, `1 < p < ∞`, `m ∈ ℕ` and `f ∈ W^m_p(V)`. If `r < ∞` and
  `1/r = 1/p - m/d`, then `f` agrees almost everywhere with a function in `L_r(V)`
  (`Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`); if `m > d/p`, with a bounded continuous function
  (`Rd.exists_boundedContinuous_ae_eq_of_memSobolev`). For `1 ≤ p < ∞`, `r < ∞`,
  `1/r = 1/p - 1/d` and `f ∈ W^1_p(V)`, some `u ∈ L_r(V)` equals `f` almost everywhere with
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
  `m = 1`, `d ≥ 1` and `1 ≤ p ≤ ∞` a bounded linear operator does this
  (`Rd.BoundedLipschitzDomain.sobolevExtensionL`).
* **Compact manifolds.** Let `M` be a compact Hausdorff smooth manifold of dimension `d ≥ 1`,
  without boundary, with boundary or with corners, with a smooth measure `μ`. For `1 ≤ p < ∞`,
  `s > 0` and `1 ≤ q ≤ ∞`, `B^s_{p,q}(M)`, defined by the chart pieces of a Besov atlas, is the
  same for every atlas (`Manifold.memBesov_iff`).
* **Traces.** Let `Ω` be as above, with boundary `Γ` and surface measure `σ`, the
  `(d-1)`-dimensional Hausdorff measure on `Γ`. In the restrictions `H^1(Ω)` of `H^1(V)`, the
  kernel `ker γ` of the boundary trace is `H^1_0(Ω)`, the closure of the restricted test
  functions (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`). Let `H^{1/2}(Γ)` be the
  orthogonal complement of `ker γ` in `H^1(Ω)` and `τ` its trace into `L_2(Γ)`. Then `g ∈ L_2(Γ)`
  is `τ t` for some `t` iff `∫_Γ ∫_Γ |g(x) - g(y)|² / |x - y|^d dσ(x) dσ(y) < ∞`, and `‖t‖²` is
  equivalent to `‖τ t‖²_{L_2(Γ)}` plus this form
  (`Rd.BoundedLipschitzDomain.mem_range_traceL2_iff_slobodeckij`,
  `Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`).
* **Eigenfunction expansions.** For an orthonormal basis of weak eigenfunctions `e_i` with
  eigenvalues `λ_i`, let `A_k` be the span of the `e_i` with `⌊√(1 + λ_i)⌋ < k`, and let
  `0 < θ < 1`, `1 ≤ q ≤ ∞`. On a bounded Lipschitz domain `Ω`, `d ≥ 1`, with the Neumann
  eigenbasis, `f ∈ L_2(V)` has `f|_Ω ∈ A^θ_q` iff
  `‖f‖_{L_2(Ω)} + ‖(2^(kθ) ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_q} < ∞`, for every `r ≥ 1`
  (`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_iff`). On `M` as above, with the eigenbasis
  of the chart form `a_A(u, w) = ∑_{k,j} ⟨∂_j P_k u, ∂_j P_k w⟩` of an atlas `A`, `f ∈ L_2(μ)`
  lies in `A^θ_q` iff `f ∈ B^θ_{2,q}(M)` (`Manifold.BesovAtlas.memApprox_chartScheme_iff`).
* **Approximation spaces are interpolation spaces.** Let `ι : Y → X` be a bounded linear map
  of real normed spaces and `(A_n)` a scheme in `X` with Jackson's inequality
  `E_n(ι y) ≤ C n^(-r) ‖y‖` and Bernstein's inequality (every `a ∈ A_n` is `ι y` with
  `‖y‖ ≤ C n^r ‖a‖`), `n ≥ 1`. For `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q = (X, Y)_{s/r,q}` for the
  continuous K-method with `K(t, f) = inf_y (‖f - ι y‖ + t ‖y‖)`
  (`ApproximationScheme.memApprox_iff_memKMethod`).
* **Nonlinear approximation from an orthonormal basis.** Let `(e_i)_{i ∈ I}` be a Hilbert basis
  of a complex Hilbert space `H`, and let `A_n` be the set of linear combinations of at most `n`
  of the vectors `e_i`. For `0 < τ < 2` and `θ = 1/τ - 1/2`, `f ∈ H` lies in the approximation
  space `A^θ_τ` of `(A_n)` iff `∑_i |⟨e_i, f⟩|^τ < ∞` (Stechkin for `τ = 1`; Pietsch, DeVore in
  general; `HilbertBasis.memApprox_nTerm_iff`). For the Fourier basis of `L_2(𝕋^d)` the
  condition is `∑_{k ∈ ℤ^d} |f̂(k)|^τ < ∞` (`Torus.memApprox_nTerm_iff`). For the Haar basis
  `1`, `h_{k,i}` (`0 ≤ i < 2^k`) of `L_2[0, 1]` it is
  `|∫_0^1 f|^τ + ∑_k ∑_{i<2^k} |⟨f, h_{k,i}⟩|^τ < ∞` (`Haar.memApprox_nTerm_iff_haarCoeff`); for
  `1 ≤ τ < 2`, `f ∈ A^θ_τ` iff `‖f‖_τ + ‖(2^(kθ) ω_1(f, 2^(-k), [0, 1])_τ)_k‖_{ℓ_τ} < ∞`, that is,
  iff `f ∈ B^θ_{τ,τ}[0, 1]` (DeVore–Jawerth–Popov; `Haar.memApprox_nTerm_iff_modulus`).
* **Besov spaces for `0 < p < 1` on `[0, 1]`.** Let `0 < p ≤ 1` and `0 < q ≤ ∞`, and let
  `E_k(f)` be the error of best approximation of `f ∈ L_p[0, 1]` by step functions on the dyadic
  intervals of length `2^(-k)`. For `0 ≤ s < 1/p`, `‖f‖_p + ‖(2^(ks) E_k(f))_k‖_{ℓ_q} < ∞` iff
  `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`, that is, iff `f ∈ B^s_{p,q,1}[0, 1]`
  (`Haar.eNormDyadic_stepCouple_lt_top_iff_modulus`). For `1/p - 1 < s < 1/p`,
  `f ∈ B^s_{p,q,1}[0, 1]` iff `f ∈ L_1[0, 1]` and
  `|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`
  (`Haar.lqNorm_modulus_lt_top_iff_haarCoeff_of_le_one`), and for `q < ∞` the partial sums of the
  Haar expansion of `f` converge to `f` in the quasi-norm `‖g‖_p + ‖(2^(ks) E_k(g))_k‖_{ℓ_q}`, and
  the coefficients of a convergent Haar expansion are unique
  (`Haar.tendsto_eNormDyadic_sub_haarPartialSum`, `Haar.eq_haarSystemCoeff_of_tendsto`). For
  `0 < τ < 2` and `θ = 1/τ - 1/2`, `f ∈ L_2[0, 1]` lies in the approximation space `A^θ_τ` of
  `n`-term approximation from the Haar basis iff
  `‖f‖_τ + ‖(2^(kθ) ω_1(f, 2^(-k), [0, 1])_τ)_k‖_{ℓ_τ} < ∞`
  (`Haar.memApprox_nTerm_iff_modulus_of_lt_two`). For `s < 1`, and for `τ > 2/3`, these are the
  Besov spaces of DeVore–Popov; for `1/p - 1 < s < 1` and `q < ∞` also the Fourier-analytic
  `B^s_{p,q}[0, 1]` (Oswald).

## Organisation

The library `ApproximationSpaces` holds the abstract theory: schemes, the spaces `A^s_q`, real
interpolation of couples (`Interpolation/`) and decompositions (`Decompositions/`). The library
`FunctionSpaces` holds the function spaces in folders by setting: `Analysis/`, `MeasureSpaces/`,
`Rd/` (one folder per characterisation), `Torus/`, `Domains/` (intervals, the cube, Lipschitz
domains, traces, eigenbases, manifolds) and `Wavelets/`. The blueprint gives the proofs. The
block documents state every result with its Lean name and list the files:

* [Besov spaces on `ℝ^d`](docs/Rd.md): Littlewood–Paley blocks, differences, local means, atoms.
* [Daubechies wavelets](docs/Daubechies.md): wavelet coefficients on `ℝ` and `ℝ^d`, `H^s` by
  tensor wavelets.
* [Dominating mixed smoothness](docs/MixedSmoothness.md): mixed differences, hyperbolic crosses.
* [The torus](docs/Torus.md): trigonometric approximation, moduli, traces, Sobolev spaces.
* [Intervals, the cube, splines and wavelets](docs/IntervalCube.md): splines, Haar,
  multiwavelets.
* [Triebel–Lizorkin spaces](docs/TriebelLizorkin.md): maximal inequalities, local means, atoms,
  singular integrals.
* [Sobolev spaces on `ℝ^d`](docs/SobolevRd.md): weak derivatives, `W^m_p = F^m_{p,2} = H^{m,p}`,
  embeddings.
* [Lipschitz domains and traces](docs/DomainsTraces.md): extension, traces, `H^1(Ω)`, Green's
  formula.
* [Manifolds and eigenbases](docs/Manifolds.md): compact manifolds, Dirichlet and Neumann
  eigenfunctions.
* [Besov and Sobolev spaces on measure spaces](docs/MeasureSpaces.md): spaces of a scheme,
  embeddings.
* [Approximation spaces](docs/ApproximationSpaces.md): schemes, `A^s_q`, interpolation,
  decompositions.
* [Tools from analysis](docs/Analysis.md): `L_p` tools, convolution, maximal functions.

[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.

## What is left to do

* Interpolation: Lorentz spaces, real Riesz–Thorin, off-diagonal Marcinkiewicz, J- and complex
  method.
* The quasi-Banach range on the torus and on `ℝ^d`, splines of order `r ≥ 2` for `p < 1`, and
  Triebel–Lizorkin spaces with `p < 1`.
* Triebel–Lizorkin spaces with `p = 1` or `q = 1`, and ball means and atoms on the torus.
* Sobolev spaces: Jawerth–Franke with Besov targets, Hardy–Littlewood–Sobolev, Trudinger, Mihlin
  multipliers with finitely many derivatives (Riesz transforms).
* Manifolds with corners: the cube as an example, traces on faces, products of models.
* Higher smoothness: Marchaud's inequality, splines on domains, sharp Daubechies exponents.
* Extension operators for `W^m_p` of every order, and Stein's universal operator.
* Eigenbases: elliptic regularity, the local Weyl law, spectral `B^s_{p,q}` for `p ≠ 2` or
  `s ≥ 1`, the two-sided description of the Dirichlet approximation spaces, and the
  Laplace–Beltrami operator.

## Building

Requires [`elan`](https://github.com/leanprover/elan); Lean and Mathlib are pinned to
`v4.35.0`. Run `lake exe cache get` and then `lake build` from inside this folder, and do not
run `lake update`, which re-resolves the dependencies. The blueprint follows
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) (`leanblueprint pdf`,
`leanblueprint web`). GitHub Actions builds the project and the blueprint on every push, checks
that every `\lean{...}` of the blueprint resolves, and publishes both.

## AI assistance

The formalisation was written with Claude Code, and Lean checks every statement and proof. The
mathematical design and the choice of statements are the author's. The author has read all
statements in broad terms; a detailed check and a second opinion are pending. The column
"Human-checked" in the tables of the block documents records the detailed check.

## Citing and contact

[CITATION.cff](CITATION.cff) holds the citation data; GitHub shows it under "Cite this
repository". Questions, corrections and wishes go to the
[issue tracker](https://github.com/mario-ullrich/Lean-FunctionSpaces/issues).

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

The [blueprint's bibliography](https://mario-ullrich.github.io/Lean-FunctionSpaces/) lists all
sources. The essential ones:

* J. Bergh, J. Löfström, *Interpolation Spaces. An Introduction*, Springer-Verlag, 1976.
* A. P. Calderón, *Lebesgue spaces of differentiable functions and distributions*, Proc. Sympos.
  Pure Math. **4** (1961), 33–49.
* I. Daubechies, *Ten Lectures on Wavelets*, SIAM, 1992.
* R. A. DeVore, *Nonlinear approximation*, Acta Numer. **7** (1998), 51–150.
* R. A. DeVore, B. Jawerth, V. A. Popov, *Compression of wavelet decompositions*, Amer. J. Math.
  **114** (1992), 737–785.
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
* S. B. Stechkin, *On absolute convergence of orthogonal series* (in Russian), Dokl. Akad. Nauk
  SSSR (N.S.) **102** (1955), 37–40.
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
  self-adjoint operators, the Japanese bracket, Mathlib's Bessel potential spaces and the
  decreasing rearrangement of null families.
