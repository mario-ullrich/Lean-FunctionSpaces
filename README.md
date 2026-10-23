# Function spaces via approximation in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of **Besov, Triebel–Lizorkin and Sobolev spaces** on several
domains, their equivalent **characterisations** and their **embedding theorems**, built on the
theory of **approximation spaces**. The project is work in progress; the details are in ten
block documents under [`docs/`](docs/), listed under [What is formalised](#what-is-formalised).

* **Blueprint** (a webpage explaining the mathematics):
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/>
* **Blueprint as PDF**:
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/dep_graph_document.html>
* **PDF and dependency graph as images**, built from the latest commit on `main` and shown by
  GitHub itself: branch
  [`blueprint-build`](https://github.com/mario-ullrich/Lean-FunctionSpaces/tree/blueprint-build)

## The setting

**Besov and Sobolev spaces.** Let `1 ≤ p < ∞`, `s > 0`, `1 ≤ q ≤ ∞` and `r > s` an integer. The
classical Besov space `B^s_{p,q}(ℝ^d)` consists of the `f ∈ L_p(ℝ^d)` with

```
‖f‖_p + ‖ (2^(ks) ω_r(f, 2^(-k))_p)_{k ≥ 0} ‖_{ℓ_q}  <  ∞ ,
ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_p .
```

Sobolev spaces appear as `W^m_p` through weak derivatives on open subsets of `ℝ^d` and as `W^m_2`
on the torus, as `H^{s,p}` through Mathlib's Bessel potentials on `ℝ^d`, as `H^s` through Fourier
coefficients on the torus, and abstractly as every space with Jackson's and Bernstein's
inequalities of order `s`, the form in which their embeddings are proved.

**Triebel–Lizorkin spaces** `F^s_{p,q}(ℝ^d)` take the `ℓ_q` norm of the Littlewood–Paley blocks
`ψ_j ⋆ f` at every point before the `L_p` norm: they consist of the `f ∈ L_p(ℝ^d)` with
`‖ x ↦ ‖(2^(js) |ψ_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p < ∞`. For `q = p` and `s > 0` they are the Besov
spaces `B^s_{p,p}`.

**Characterisations and domains.** Each setting has its natural descriptions of these spaces:
Fourier coefficients and Littlewood–Paley blocks on the torus and on `ℝ^d`, splines and Haar or
multiwavelet coefficients on intervals and the cube, local means and atoms on `ℝ^d`, intrinsic
differences and extensions on Lipschitz domains, chart pieces on manifolds, traces on
boundaries, and mixed differences for dominating mixed smoothness. Triebel–Lizorkin spaces are
described by local means on `ℝ^d` and on the torus, and by ball means of differences and atoms
on `ℝ^d`. The project proves them
equivalent; the last chapter of the blueprint, *The representations of Besov spaces*, lists
them with their settings and ranges of parameters and explains how they differ.

**Approximation spaces.** Let `X` be a real normed space. An **approximation scheme** is a
sequence of subsets `A₀ ⊆ A₁ ⊆ A₂ ⊆ ⋯` of `X` with `A₀ = {0}`, `c · a ∈ A_n` for real `c` and
`a ∈ A_n`, and `A_m + A_n ⊆ A_{m+n}`. The sets need not be subspaces: for `n`-term
approximation from a dictionary `D`, `A_n` is the set of linear combinations of at most `n`
elements of `D`. The **error of best approximation** of `f ∈ X` is
`E_n(f) = inf { ‖f - a‖ : a ∈ A_n }`.

For `s > 0` and `1 ≤ q ≤ ∞`, the **approximation space** `A^s_q` consists of those `f` with

```
‖f‖_{A^s_q} = ‖ (n^(s - 1/q) E_{n-1}(f))_{n ≥ 1} ‖_{ℓ_q}  <  ∞ .
```

For a finite measure space `(Ω, μ)` and a scheme `S` of bounded continuous functions on `Ω`,
the **Besov space** is `B^s_{p,q}(Ω, S) = A^s_q(L_p(μ), S)`: the functions whose best
approximation from `S` in `L_p` decays at rate `s`. On the torus `𝕋^d` with `S_n` the
trigonometric polynomials of degree `< n`, these are the classical periodic Besov spaces. On each
concrete domain the block documents show that this definition, for the natural scheme, agrees
with the classical one. It uses only approximation by explicit classes (trigonometric
polynomials, splines, band-limited functions, step functions), so it measures directly what
numerical methods can achieve, and the embeddings follow from the abstract theory together with
a Nikolskii inequality.

## Main results

The list below gives some results of each block; the block documents list all of them, and the
blueprint chapter *The representations of Besov spaces* collects the characterisations.

**Approximation spaces** ([details](docs/ApproximationSpaces.md))

* **Nikolskii transfer theorem.** Let `ι : Y → X` be an injective bounded linear map from a
  Banach space `Y`, let `0 ≤ α < s`, and let every `a ∈ A_n` be `ι y` with `‖y‖ ≤ C n^α ‖a‖`
  (a Nikolskii inequality). Then every `f ∈ A^s_q(X)` is `ι y` for some `y` in the approximation
  space `B^{s-α}_q(Y)` of the pulled-back scheme `B_n = ι⁻¹(A_n)`, with
  `‖y‖_{B^{s-α}_q} ≤ K ‖f‖_{A^s_q}` (`ApproximationScheme.exists_preimage_of_nikolskii`).
* **The representation theorem.** Let `ι : Y → X` satisfy Jackson's inequality
  `E_n(ι y) ≤ C n^(-r) ‖y‖` and Bernstein's inequality (every `a ∈ A_n` is `ι y` with
  `‖y‖ ≤ C n^r ‖a‖`) of order `r`. Then for `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q` is the real
  interpolation space `(X, Y)_{s/r, q}`, with equivalent norms
  (`ApproximationScheme.memApprox_iff_memInterp`).
* **Moduli of smoothness and approximation.** Let `ω(f, 2^(-k))` be subadditive with
  `ω(f, t) ≤ C₀ ‖f‖`, and assume a Jackson inequality `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for
  `k ≥ k₀` and an inverse inequality `ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`. Then
  for `0 ≤ s < θ` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞`,
  with equivalent quasi-norms (`ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top`).

**Besov and Sobolev spaces on measure spaces** ([details](docs/BesovSobolev.md))

* **Besov embeddings.** Let `μ` be a finite measure on `Ω` and `S` a scheme of bounded
  continuous functions with the Nikolskii property of dimension `D ≥ 0`: for every
  `1 ≤ p ≤ ∞` there is `C` with `‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all `a ∈ S_n`, `n ≥ 1`. Let
  `1 ≤ p ≤ r ≤ ∞`, `1 ≤ q ≤ ∞` and `α = D (1/p - 1/r) < s`. Then every `f ∈ B^s_{p,q}`
  belongs to `L_r` and to `B^{s-α}_{r,q}`, with `‖f‖_{B^{s-α}_{r,q}} ≤ K ‖f‖_{B^s_{p,q}}`
  (`FunctionScheme.MemBesov.exists_inclusion_eq_of_nikolskii`). If `μ` charges every nonempty
  open set and `s > D/p`, every `f ∈ B^s_{p,q}` has a bounded continuous representative
  (`FunctionScheme.MemBesov.exists_boundedContinuous`).
* **Sobolev embeddings.** Call a Banach space `V` with an injective bounded map into `L_p(μ)`
  a Sobolev space of order `s` for `S` if it satisfies Jackson's inequality
  `E_n(f)_p ≤ C n^(-s) ‖f‖_V` and Bernstein's inequality (every `a ∈ S_n` lies in `V` with
  `‖a‖_V ≤ C n^s ‖a‖_p`). For `S` with the Nikolskii property of dimension `D ≥ 0`, Sobolev
  spaces `V` of order `s` in `L_p` and `V'` of order `t` in `L_r`, `p ≤ r` and
  `t - D/r < s - D/p`, every element of `V` lies in `V'`
  (`FunctionScheme.SobolevSpace.exists_eq_inclusion'`); for `s > D/p` every element of `V`
  has a bounded continuous representative
  (`FunctionScheme.SobolevSpace.exists_boundedContinuous`).

**The torus** ([details](docs/Torus.md))

* **Besov spaces on the torus through moduli of smoothness.** For `1 ≤ p < ∞`, `0 < s < r` and
  `1 ≤ q ≤ ∞`, `f ∈ B^s_{p,q}(𝕋^d)` iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` for
  the modulus `ω_r(f, t)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r f‖_p` of order `r`
  (`Torus.memBesov_iff_modNorm_lt_top_lp`). The kernels of `ℝ^d` act on `𝕋^d` by
  `(Φ ⋆ f)(t) = ∫ Φ(y) f(t - π y) dy` (`Torus.econvLp`), which transfers Jackson's and
  Bernstein's inequalities from band-limited approximation on `ℝ^d`.
* **Besov spaces on the torus through Littlewood–Paley blocks.** Let `ψ_j` be the
  Littlewood–Paley kernels on `ℝ^d` (below), acting on `𝕋^d` by
  `ψ_j ⋆ f(t) = ∫ ψ_j(y) f(t - π y) dy` with the quotient map `π : ℝ^d → 𝕋^d`. For every
  `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{p,q}(𝕋^d)` iff
  `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞` (`Torus.memBesov_iff_littlewoodPaleyNorm_lt_top`).
* **The Nikolskii inequality on the torus.** For a trigonometric polynomial `T` of degree `< n`
  on `𝕋^d`, `n ≥ 1`, and `1 ≤ p < ∞`, `‖T‖_∞ ≤ (2⌈p/2⌉)^(d/p) n^(d/p) ‖T‖_p`
  (`Torus.norm_le_rpow_mul_eLpNorm`). Hence the Besov embeddings hold on `𝕋^d` with
  `α = d (1/p - 1/r)` (`Torus.memBesov_exists_inclusion_eq`, `Torus.memBesov_exists_continuous`).

**Intervals, the cube, splines and wavelets** ([details](docs/IntervalCube.md))

* **Splines and higher smoothness.** Let `S_k ⊆ L_p[0, 1]` consist of the splines of order
  `r ≥ 1` on the dyadic grid of level `k`: piecewise polynomials of degree `< r` that are `r - 2`
  times continuously differentiable, and let
  `ω_r(f, t, [0, 1])_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r f‖_{L_p[0, 1-rh]}`. For `1 ≤ p < ∞`,
  `1 ≤ q ≤ ∞` and `0 ≤ s < r - 1 + 1/p`, `f ∈ A^s_q` iff
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
  (`Interval.memApprox_splineScheme_iff`).
* **The isotropic modulus on the cube.** On `Q = [0, 1]^d` let
  `ω_r^iso(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r f‖_{L_p({x ∈ Q : x + rh ∈ Q})}`. For `1 ≤ p < ∞`,
  `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < r - 1 + 1/p`, `f ∈ A^s_q` of the tensor splines of order `r`
  on the dyadic grids of `Q` iff `‖f‖_p + ‖(2^(ks) ω_r^iso(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Cube.memApprox_cubeSplineScheme_iff_iso`), and the same holds for the piecewise polynomials
  and `0 ≤ s < 1/p` (`Cube.memApprox_cubePPScheme_iff_iso`).
* **The Haar system.** Let `h_{k,m} = 2^(k/2) (1_{[2m, 2m+1) 2^(-k-1)} - 1_{[2m+1, 2m+2) 2^(-k-1)})`
  be the Haar functions on `[0, 1)` and `A_n` the step functions on the dyadic intervals of
  length `2^(-⌊log₂ n⌋)`. For `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p[0, 1))` iff
  `|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`
  (`Haar.memApprox_iff_haarCoeff`).

**Daubechies wavelets** ([details](docs/Daubechies.md))

* **Daubechies wavelets and Besov spaces.** For a mask of order `N ≥ 2` with filter
  coefficients `c_k`, a real polynomial `L` of degree `< N` with `L(1) = 1` and
  `|L(e^(-2πiξ))|² = ∑_{k<N} C(N-1+k, k) sin^(2k)(πξ)`, which exists by the Fejér–Riesz theorem
  (`Daubechies.nonempty_mask_iff`, `Polynomial.fejer_riesz`), the scaling function `φ` is
  continuous, vanishes outside `[0, 2N - 1]`, satisfies `φ(x) = ∑_k c_k φ(2x - k)` and has
  orthonormal integer translates (`Daubechies.scalingFun_eq_zero`,
  `Daubechies.scalingFun_refine`, `Daubechies.integral_scalingFun_translate_mul_conj_translate`).
  Let `ψ` be the wavelet and `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`. If `ω_N(φ, t)_p ≤ K t^θ` and `0 < s < θ`,
  then `f ∈ L_p(ℝ)` lies in `B^s_{p,q}(ℝ)` iff
  `‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s+1/2-1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
  (`Daubechies.besov_iff_coeff`). The bound holds for `p ≤ 2` and every
  `θ < N - log₄ λ` whenever the transfer operator satisfies `T^n 1 ≤ C λ^n`
  (`Daubechies.besov_iff_coeff_of_le_two`); `λ = 4` for `N = 2` and `λ = 9` for `N = 3`, the
  Sobolev exponents `1` and `3 - log₂ 3`. The scaling function of D4 is Hölder continuous of
  every order `a ≤ 2 - log₂(1 + √3) ≈ 0.55` (`Daubechies.holder_d4`).

**Function spaces on `ℝ^d`** ([details](docs/Rd.md))

* **Besov spaces on `ℝ^d` by differences.** Let `V` be a finite-dimensional real inner product
  space, `1 ≤ p < ∞`, `E_k = {g ∈ L_p(V) : Θ_k ⋆ g = g}` the band-limited classes, with
  `𝓕Θ_k = 1` on the ball of radius `2^(k+1)` and `0` outside the ball of radius `2^(k+2)`, `ψ_j`
  the kernels of a smooth dyadic decomposition of unity on the Fourier side, and
  `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_p`. For `0 < s < r` and `1 ≤ q ≤ ∞`, the following are
  equivalent for `f ∈ L_p(V)`: `f ∈ A^s_q(L_p(V), (E_k))`;
  `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q} < ∞`; and `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Rd.memApprox_bandScheme_iff_modulus`, `Rd.littlewoodPaleyNorm_lt_top_iff_modulus`).
* **Atomic decompositions on `ℝ^d`.** Let `1 ≤ p < ∞` and `n = dim V`. A regular atom of level
  `j`, order `r` and exponent `σ` vanishes outside a ball `B(c, d 2^(-j))` and has
  `‖a‖_p ≤ C 2^(-jn/p)` and `‖Δ_h^r a‖_p ≤ C 2^(-jn/p) min(1, (2^j ‖h‖)^σ)`
  (`Rd.IsRegularAtom`). For `0 < s < L` and `1 ≤ q ≤ ∞`, `F ∈ L_p(V)` has
  `‖F‖_p + ‖(2^(ks) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff `F = ∑_j ∑_m λ_{j,m} a_{j,m}` with
  regular atoms of order and exponent `L` whose centres have bounded overlap at every level, and
  `‖(2^(j(s - n/p)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q} < ∞` (`Rd.LocalMeansBump.besov_iff_atomic`).

**Triebel–Lizorkin spaces** ([details](docs/TriebelLizorkin.md))

* **The Fefferman–Stein inequality.** Let `V` be a finite-dimensional real inner product space,
  such as `ℝ^d`, and `M g(x) = sup_{r > 0} |B(x, r)|⁻¹ ∫_{B(x, r)} g` the Hardy–Littlewood
  maximal function. For `1 < p < ∞`, `1 < q ≤ ∞` and almost everywhere measurable
  `g_j : V → [0, ∞]`, `j ∈ ℕ`,
  `‖ x ↦ ‖(M g_j(x))_j‖_{ℓ_q} ‖_p ≤ C ‖ x ↦ ‖(g_j(x))_j‖_{ℓ_q} ‖_p` with an explicit constant
  `C` that depends only on `dim V`, `p` and `q` (`Rd.feffermanStein`).
* **Triebel–Lizorkin spaces and the Besov sandwich.** For `1 ≤ p < ∞`, `s ∈ ℝ` and
  `1 ≤ q ≤ ∞`, `F^s_{p,q}` consists of the `f ∈ L_p(V)` with
  `‖ x ↦ ‖(2^(js) |ψ_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p < ∞`, for the Littlewood–Paley kernels `ψ_j` of
  `ℝ^d` above. For `s > 0`, `F^s_{p,p} = B^s_{p,p}` and
  `B^s_{p,min(p,q)} ⊆ F^s_{p,q} ⊆ B^s_{p,max(p,q)}`, where `B^s_{p,q}` is the approximation space
  `A^s_q` of the band-limited classes (`Rd.memTriebelLizorkin_iff_memApprox`,
  `Rd.memTriebelLizorkin_of_memApprox`, `Rd.memApprox_of_memTriebelLizorkin`). The same holds on
  the torus `𝕋^d`, with the blocks `ψ_j ⋆ f(t) = ∫ ψ_j(y) f(t - π y) dy` and the approximation
  spaces of the trigonometric polynomials (`Torus.memTriebelLizorkin_iff_memBesov`,
  `Torus.memTriebelLizorkin_of_memBesov`, `Torus.memBesov_of_memTriebelLizorkin`).
* **The local means characterisation.** Let `g` be a smooth function on `V` with `∫ g = 1` that
  vanishes outside a ball, `g_c = c^n g(c ·)` its dilations (`n = dim V`), `L ≥ 1`,
  `m = ∑_{l=1}^L (-1)^(l+1) C(L, l) g_{1/l}`, and `k_0 = m`, `k_j = m_{2^j} - m_{2^(j-1)}` the
  local means kernels. For `1 < p < ∞`, `1 < q ≤ ∞`, `0 < s < L` and `f ∈ L_p(V)`,
  `f ∈ F^s_{p,q}` iff `‖ x ↦ ‖(2^(js) |k_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p < ∞`
  (`Rd.LocalMeansBump.memTriebelLizorkin_iff_tlLocalMeans`), and the same holds on `𝕋^d`
  (`Torus.memTriebelLizorkin_iff_tlLocalMeans`).
* **Ball means of differences.** For `f ∈ L_p(V)` let
  `d_j f(x) = |B(0,2^(-j))|⁻¹ ∫_{B(0,2^(-j))} |Δ_h^L f(x)| dh`. For `1 < p < ∞`, `1 < q ≤ ∞`
  and `0 < s < L`, `f ∈ F^s_{p,q}` iff `‖f‖_p + ‖ x ↦ ‖(2^(js) d_j f(x))_j‖_{ℓ_q} ‖_p < ∞`
  (`Rd.memTriebelLizorkin_iff_tlDiffNorm_lt_top`). The block document also describes
  `F^s_{p,q}` by atoms.

**Sobolev spaces on `ℝ^d`** ([details](docs/SobolevRd.md))

* **The Mathlib bridge: `H^s(ℝ^d) = B^s_{2,2}(ℝ^d)`.** Let `V` be a finite-dimensional real
  inner product space, such as `ℝ^d`, and `H^s(V)` Mathlib's Sobolev space of the tempered
  distributions `u` with `J_s u = 𝓕⁻¹(⟨ξ⟩^s 𝓕u) ∈ L_2(V)`, `⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. For `s ≥ 0`,
  `u ∈ H^s(V)` iff `u` is a function `f ∈ L_2(V)` in `F^s_{2,2}(V)`, and then
  `(2 · 5^s)^(-1/2) ‖J_s f‖_2 ≤ ‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^(1/2) ‖J_s f‖_2`
  (`Rd.memSobolev_two_iff_memTriebelLizorkin`, `Rd.triebelLizorkinNorm_le_of_besselPotential_eq`,
  `Rd.enorm_besselPotential_le_triebelLizorkinNorm`); for `s > 0` this is the Besov space
  `B^s_{2,2}(V)` (`Rd.memSobolev_two_iff_exists_memApprox`).
* **Weak derivatives and `W^1_2 = H^1`.** For locally integrable `f`, `g` on an open set `Ω ⊆ V`,
  `g` is the weak derivative `∂^v f = ∂_{v_0} ⋯ ∂_{v_{k-1}} f` on `Ω` iff
  `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every smooth compactly supported real `φ` in `Ω`
  (`Rd.HasWeakLineDeriv`, `Rd.hasWeakLineDeriv_iff_integral`), and `f ∈ L_2(V)` lies in
  `W^1_2(V)` iff it lies in `H^1(V)` (`Rd.memSobolev_one_iff`).
* **`H^1` on bounded Lipschitz domains.** On a bounded Lipschitz domain `Ω` with boundary `Γ`,
  `H^1(Ω)` consists of the `f ∈ L_2(V)` that agree on `Ω` with a function of `H^1(V)`
  (`Rd.BoundedLipschitzDomain.MemSobolevOn`); for every order `r ≥ 2`, `f ∈ H^1(Ω)` iff
  `‖f‖_{L_2(Ω)} + ‖(2^k ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞`
  (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_modulusOn`); every `f ∈ H^1(Ω)` has weak
  derivatives in `L_2(Ω)` (`Rd.BoundedLipschitzDomain.MemSobolevOn.memWeakSobolev`), and the
  boundary traces of the functions of `H^1(Ω)` are the functions of `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_memSobolevOn`).
* **Rellich's theorem.** For every bounded set `Ω ⊆ V`, the restriction from `H^1(V)` to
  `L_2(Ω)` is a compact operator (`Rd.isCompactOperator_restr_toL2`).
* **Sobolev spaces on open sets as Hilbert spaces.** For every open `Ω ⊆ V` and real `s`,
  `H^s(Ω)` is the orthogonal complement in `H^s(V)` of the elements whose distribution vanishes
  on every test function of `Ω` (`Rd.RestrictionSpace`), isometric to the quotient of `H^s(V)`
  by them (`Rd.quotientEquivRestrictionSpace`); `H^1(Ω) → L_2(Ω)` is injective and, for
  bounded `Ω`, compact (`Rd.restrictL2_injective`, `Rd.isCompactOperator_restrictL2`); and
  restriction is an isometry from `H̃^1(Ω)`, the closure of the test functions in `H^1(V)`, onto
  `H^1_0(Ω)`, the closure of their restrictions in `H^1(Ω)` (`Rd.tildeEquivZeroBoundary`).
* **Duality on open sets.** For every open `Ω ⊆ V` and real `s`, every bounded functional `ℓ` on
  `H̃^s(Ω)` is `U ↦ ⟪J_{-s} W, J_s U⟫_{L_2}` for exactly one `W ∈ H^{-s}(Ω)`, with `‖W‖ = ‖ℓ‖`
  (`Rd.dualEquiv`, `Rd.dualEquiv_apply`, `Rd.dualEquiv_eq_iff`), and likewise
  `(H^s(Ω))^* ≅ H̃^{-s}(Ω)` and `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` (`Rd.dualRestrictionEquiv`,
  `Rd.dualZeroBoundaryEquiv`).
* **The trace space `H^{1/2}(Γ)`.** On a bounded Lipschitz domain `Ω` with boundary `Γ`, the
  trace space `H^{1/2}(Γ)` is the orthogonal complement in `H^1(Ω)` of the `u` whose boundary
  trace vanishes almost everywhere on `Γ` (`Rd.BoundedLipschitzDomain.TraceSpace`,
  `Rd.BoundedLipschitzDomain.mem_traceKer_iff`). The trace is the orthogonal projection onto it
  and the extension is the inclusion, both of norm at most `1`, `H^1(Ω) ⧸ ker γ ≅ H^{1/2}(Γ)`
  isometrically (`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`), and the boundary traces
  of its elements are the functions of `B^{1/2}_{2,2}(Γ)` modulo null sets of `Γ`
  (`Rd.BoundedLipschitzDomain.exists_traceSpace_of_memBoundaryBesov`).
* **The area formula for Lipschitz graphs.** Let `Ω = {x : φ(x) < ⟪x, e⟫}` be a Lipschitz graph
  domain in `V`, `dim V = n`, with the graph map `γ(x') = x' + φ(x') e` over the hyperplane
  `H = e^⊥` and the gradient `∇φ(x') ∈ H` of `φ` on `H`, which exists almost everywhere. For
  every measurable `A ⊆ H`, `μHE[n-1] (γ(A)) = ∫_A √(1 + ‖∇φ(x')‖²) dx'` for Mathlib's
  `(n-1)`-dimensional Euclidean Hausdorff measure `μHE[n-1]`, normalised to be the volume on
  hyperplanes (`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphMap_image`).
* **The surface measure and `L_2(Γ)`.** On a bounded Lipschitz domain `Ω` with boundary `Γ`,
  charts `γ_j` over the hyperplanes `H_j` and boundary balls `B_j`, the surface measure `σ` is
  `μHE[n-1]` restricted to `Γ` (`Rd.BoundedLipschitzDomain.surfaceMeasure`), and
  `∫_Γ F dσ = ∫_{H_j} F(γ_j x') √(1 + ‖∇φ_j(x')‖²) dx'` for every `F : V → [0, ∞]` vanishing
  outside `B_j` (`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support`). It is finite,
  `|Γ| = 0` (`Rd.BoundedLipschitzDomain.volume_frontier`), and the trace
  `γ_{L_2} : H^1(Ω) → L_2(Γ) = L_2(σ)` is a bounded operator, given almost everywhere by the
  boundary trace, with the trace kernel as its kernel (`Rd.BoundedLipschitzDomain.boundaryTraceL2`,
  `Rd.BoundedLipschitzDomain.boundaryTraceL2_apply_ae`,
  `Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`); on `H^{1/2}(Γ)` the trace into `L_2(Γ)` is
  injective (`Rd.BoundedLipschitzDomain.traceL2_injective`).
* **The square function theorem.** Let `dim V ≥ 1` and `1 < p < ∞`. For every `f ∈ L_p(V)`,
  the square function `x ↦ ‖((ψ_j ⋆ f)(x))_j‖_{ℓ_2}` of the Littlewood–Paley blocks `ψ_j ⋆ f`
  has `L_p` norm `‖f‖_{F^0_{p,2}}` (`Rd.triebelLizorkinNorm_zero_two_eq`), and
  `‖f‖_{F^0_{p,2}} ≤ Q_{V,p} ‖f‖_p`, `‖f‖_p ≤ Q̃_{V,p} ‖f‖_{F^0_{p,2}}`
  (`Rd.triebelLizorkinNorm_zero_two_le`, `Rd.enorm_le_triebelLizorkinNorm_zero_two`), with the
  strong type constants of the Calderón–Zygmund families of the blocks and of the synthesis
  kernels (`Rd.squareFunctionConst`, `Rd.squareSynthesisConst`); hence `F^0_{p,2} = L_p(V)`
  (`Rd.triebelLizorkinSpace_zero_two_eq_top`). The proof is the strong type `(p,p)` of
  vector-valued singular integrals with Calderón–Zygmund kernel families
  (`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`, `Rd.IsCZFamily.eLpNorm_sum_conv_le`).
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
  The proof writes the blocks through the weak derivatives and back, with the strong type of
  the Calderón–Zygmund families of the derivative kernels.
* **`H^{s,p} = F^s_{p,2}` and `W^m_p = H^{m,p}`.** Let `dim V ≥ 1` and `1 < p < ∞`, and let
  `J_s` be Mathlib's Bessel potential, the Fourier multiplier with `(1 + ‖ξ‖²)^{s/2}`; a tempered
  distribution `f` lies in Mathlib's Bessel potential space `H^{s,p}(V)` iff `J_s f ∈ L_p(V)`.
  For every real `s` there is `C < ∞` such that for every `f ∈ F^s_{p,2}(V)`, `J_s f` is a
  function `h ∈ L_p(V)` with `‖h‖_p ≤ C ‖f‖_{F^s_{p,2}}`
  (`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`). For every real `s ≥ 0` there is
  `C < ∞` such that every tempered distribution `f` with `J_s f = h ∈ L_p(V)` is a function
  `g ∈ F^s_{p,2}(V)` with `‖g‖_{F^s_{p,2}} ≤ C ‖h‖_p`
  (`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`). For every real `s`, `f ∈ L_p(V)` lies
  in `F^s_{p,2}(V)` iff it lies in `H^{s,p}(V)` (`Rd.memTriebelLizorkin_iff_memSobolev_bessel`),
  and for every `m ∈ ℕ`, `f ∈ W^m_p(V)` iff `f ∈ H^{m,p}(V)`, Calderón's theorem
  (`Rd.memSobolev_iff_memSobolev_bessel`). The constants are existential: the kernels are the
  Bessel potentials of the Littlewood–Paley blocks and of their synthesis kernels, which form
  Calderón–Zygmund families whose Schwartz bounds come from bounded derivatives on a compact
  annulus and the continuity of the inverse Fourier transform on the Schwartz space.
* **Sobolev and Besov embeddings on `ℝ^d`.** Let `n = dim V`, `1 ≤ p ≤ r ≤ ∞`, `p < ∞` and
  `1 ≤ q ≤ ∞`. For `s > n(1/p - 1/r)`, every `f ∈ B^s_{p,q}(V)` agrees almost everywhere with
  some `g ∈ L_r(V)` with `‖g‖_r ≤ K_{V,p,r,s} ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q}`
  (`Rd.exists_memLp_ae_eq_of_memApprox`, `Rd.besovEmbeddingConst`); for `s > n/p` it agrees
  almost everywhere with a bounded continuous function `a` with
  `sup |a| ≤ K_{V,p,∞,s} ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q}`
  (`Rd.exists_boundedContinuous_ae_eq_of_memApprox`). For `n ≥ 1`, `1 < p < ∞` and `f ∈ L_p(V)`
  whose weak derivatives `g_α = ∂^α f` of order `m` along a basis lie in `L_p(V)`, put
  `M_f = ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p` (`Rd.sobolevToTLConst`). If `m > n(1/p - 1/r)`,
  then `f` agrees almost everywhere with some `u ∈ L_r(V)` with `‖u‖_r ≤ K_{V,p,r,m} M_f`
  (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv`); if `m > n/p`, then `f` agrees almost
  everywhere with a bounded continuous function `a` with `sup |a| ≤ K_{V,p,∞,m} M_f`
  (`Rd.exists_boundedContinuous_ae_eq_of_hasWeakLineDeriv`). In particular every
  `f ∈ W^m_p(V)` has such representatives (`Rd.exists_memLp_ae_eq_of_memSobolev`,
  `Rd.exists_boundedContinuous_ae_eq_of_memSobolev`). The proof is the Nikolskii inequality
  `‖ψ_j ⋆ f‖_r ≤ N_p^(1-p/r) 2^(jn(1/p - 1/r)) ‖ψ_j ⋆ f‖_p` for the Littlewood–Paley blocks
  (`Rd.eLpNorm_blockFun_le_nikolskii`, `Rd.nikolskiiBlockConst`) and the bound of
  `‖f‖_{F^m_{p,2}}` by `M_f`; the critical case `1/r = 1/p - m/n` with `r < ∞` (Sobolev's
  inequality) is not covered.
* **The extension theorem for `W^1_p` on bounded Lipschitz domains.** Let `Ω` be a bounded
  Lipschitz domain in `V`, `dim V ≥ 1`, `(e_i)` the orthonormal basis `Rd.gridBasis V` and
  `1 < p < ∞`. There
  is a finite `C` such that every `f ∈ L_p(Ω)` whose weak derivatives `g_i = ∂_{e_i} f` on `Ω` lie
  in `L_p(Ω)` agrees almost everywhere on `Ω` with some `F ∈ W^1_p(V)` with
  `‖F‖_p + ∑_i ‖∂_{e_i} F‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`
  (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`); so `f ∈ W^1_p(Ω)` iff `f` agrees on `Ω`
  with some `F ∈ W^1_p(V)` (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev`).
  For `p = 2`, `f ∈ L_2(V)` lies in `H^1(Ω)` iff it lies in `W^1_2(Ω)`
  (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`), every sequence bounded in
  `W^1_2(Ω)` has a subsequence converging in `L_2(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`), and the quotient norm of
  `H^1(Ω)` is equivalent to the `W^1_2(Ω)` norm
  (`Rd.BoundedLipschitzDomain.exists_norm_le_restrictL2`,
  `Rd.sq_norm_restrictL2_add_sum_le`).
* **Gauss–Green on Lipschitz graph domains.** Let `Ω = {x : φ(x) < ⟪x, e⟫}` be a Lipschitz
  graph domain in `V`, `n = dim V`, with the graph map `γ(x') = x' + φ(x') e` over the hyperplane
  `H = e^⊥`, the gradient `∇φ` of `φ|_H`, the outward unit normal `ν` and the normal weight
  `n_v = ⟪∇φ, v⟫ - ⟪v, e⟫ = ⟪v, ν⟫ √(1 + ‖∇φ‖²)`. For every `C^1` function `g : V → ℂ` with
  compact support and every `v ∈ V`,
  `∫_Ω ∂_v g = ∫_H g(γ x') n_v(x') dx' = ∫_{γ(H)} g ⟪v, ν ∘ P⟫ dμHE[n-1]`
  (`Rd.LipschitzGraph.setIntegral_lineDeriv_eq`,
  `Rd.LipschitzGraph.setIntegral_lineDeriv_eq_surface`), and for all `f, g ∈ W^1_2(V)`, every
  `v ∈ V` and the weak derivatives `f_v = ∂_v f`, `g_v = ∂_v g` in `L_2(V)`,
  `∫_Ω f_v g + f g_v = ∫_H Tr f · Tr g · n_v` with the traces of the trace theorem on `Ω`
  (`Rd.LipschitzGraph.setIntegral_green`; in surface form
  `Rd.LipschitzGraph.setIntegral_green_surface`).
* **Green's formula on bounded Lipschitz domains.** Let `Ω` be a bounded Lipschitz domain in `V`
  with boundary `Γ`, surface measure `σ` and outward unit normal field `ν`. For all
  `u, w ∈ H^1(Ω)` and every `v ∈ V`,
  `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ_{L_2} u · γ_{L_2} w ⟪v, ν⟫ dσ` with the trace
  `γ_{L_2} : H^1(Ω) → L_2(Γ)`
  (`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne`; for `U, W ∈ H^1(V)`
  `Rd.BoundedLipschitzDomain.setIntegral_green_surface`, in chart form for every resolution of
  unity `Rd.BoundedLipschitzDomain.setIntegral_green`). On every boundary ball `B_j`, `ν` is the
  outward unit normal of the chart `σ`-almost everywhere, so `‖ν‖ = 1` `σ`-almost everywhere
  (`Rd.BoundedLipschitzDomain.normal_ae_eq_normalAt`, `Rd.BoundedLipschitzDomain.norm_normal_ae`).
  For every `u ∈ H^1(Ω)`, the zero extension `1_Ω u` lies in `W^1_2(V)` iff the trace of `u`
  vanishes (`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_iff_mem_traceKer`).
* **The kernel of the trace.** Let `Ω` be a bounded Lipschitz domain in `V` with boundary `Γ`,
  `H^1_0(Ω)` the closure in `H^1(Ω)` of the restrictions of the test functions of `Ω`, and
  `ker γ` the `u ∈ H^1(Ω)` whose boundary trace vanishes almost everywhere on `Γ`. Then
  `ker γ = H^1_0(Ω)` (`Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`; McLean,
  Theorem 3.40), and `H^1(Ω) ⧸ H^1_0(Ω)` is isometrically isomorphic to the trace space
  `H^{1/2}(Γ)` by `[u] ↦ γ u` (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`).
  An element of `H^1(V)` lies in the closure `H̃^1(Ω)` of the test functions of `Ω` iff it
  vanishes almost everywhere outside `Ω` (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`).

**Domains, manifolds and traces** ([details](docs/DomainsTraces.md))

* **Besov spaces on bounded Lipschitz domains by intrinsic differences.** Let `Ω ⊆ V` be a bounded
  Lipschitz domain: a bounded open set whose boundary is covered by finitely many open balls
  `B_j`, centred on the boundary, with `B_j ∩ Ω = B_j ∩ Ω_j` for Lipschitz graph domains `Ω_j`
  (`Rd.BoundedLipschitzDomain`), and let
  `ω_r(f, t, Ω)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_{L_p(Ω_{rh})}` with
  `Ω_{rh} = {x : x, x + h, …, x + rh ∈ Ω}`. For `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`,
  `f ∈ L_p(V)` agrees on `Ω` with some `F ∈ L_p(V)` with
  `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn`).
* **Besov spaces on compact manifolds.** Let `M` be a compact smooth manifold, with or without
  boundary, and `μ` a smooth measure. A Besov atlas consists of finitely many charts `κ_i`, a
  smooth partition of unity `ψ_i` subordinate to them and cut-offs (`Manifold.BesovAtlas`), and
  `f ∈ B^s_{p,q}(M)` if every piece `(ψ_i f) ∘ κ_i⁻¹` has finite intrinsic Besov quasi-norm on the
  model space. For `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞` this depends neither on the atlas nor on
  the order of the differences (`Manifold.memBesov_iff`,
  `Manifold.BesovAtlas.memBesov_iff_besovNorm_lt_top`).
* **The trace theorem on compact manifolds with boundary.** Let `M` be as above with boundary,
  modelled on the half-space `{y ∈ ℝ^n : y_0 ≥ 0}`, and let `B^s_{p,q}(∂M)` consist of the `g`
  whose chart pieces restricted to the boundary hyperplane lie in its Besov space. For
  `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, `B^s_{p,q}(∂M)` is the trace space of
  `B^{s+1/p}_{p,q}(M)`: `g ∈ B^s_{p,q}(∂M)` iff the boundary pieces of `g` agree almost
  everywhere with those of the trace `Tr_A f` of some `f ∈ B^{s+1/p}_{p,q}(M)`
  (`Manifold.BesovAtlas.memBoundaryBesov_iff_exists_boundaryTrace`). For the closure of a smooth
  bounded domain this is the trace theorem on its boundary for every `s > 0`.

**Dominating mixed smoothness** ([details](docs/MixedSmoothness.md))

* **Mixed smoothness and hyperbolic crosses.** For `1 ≤ p < ∞`, `0 < s < L`, `1 ≤ q ≤ ∞` and
  `f ∈ L_p(ℝ^d)`, the mixed moduli `Ω^{e(k)}_L` in the coordinates `e(k) = {i : k_i ≠ 0}`, the
  tensor local means kernels `k_k` and the tensor Littlewood–Paley kernels `δ_k = ⊗_i ψ_{k_i}`
  describe the same space:
  `‖(2^(s|k|_1) Ω^{e(k)}_L(f, 2^(-k))_p)_{k ∈ ℕ^d}‖_{ℓ_q} < ∞` iff
  `‖(2^(s|k|_1) ‖k_k ⋆ f‖_p)_k‖_{ℓ_q} < ∞` iff `‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q} < ∞`
  (`Rd.LocalMeansBump.mixedBesov_iff_mixedLocalMeans`, `Rd.mixedBesov_iff_mixedLP`). The
  hyperbolic cross sums `S_N f = ∑_{|k|_1 ≤ N} δ_k ⋆ f` satisfy
  `‖f - S_N f‖_p ≤ C 2^(-sN) (N + 1)^((d-1)(1-1/q)) ‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q}` with
  the finite constant `C = ∑_l 2^(-sl) (l + 1)^((d-1)(1-1/q))`
  (`Rd.enorm_sub_hyperbolicSum_le_of_pos`).

## What is formalised

| Block | Lean | Checked |
|---|---|---|
| [**Approximation spaces**](docs/ApproximationSpaces.md): schemes, `A^s_q` and its embeddings, lifting and the Nikolskii transfer theorem, the representation theorem, moduli of smoothness, decompositions, traces and intrinsic norms | ✅ | ✗ |
| [**Besov and Sobolev spaces on measure spaces**](docs/BesovSobolev.md): schemes of functions, Besov and Sobolev embeddings under a Nikolskii inequality, spectral schemes, continuous spectral bases | ✅ | ✗ |
| [**The torus**](docs/Torus.md): trigonometric polynomials, `H^s`, embeddings, Fourier coefficients, moduli of smoothness and smooth Littlewood–Paley blocks for all `p`, weak derivatives, traces | ✅ | ✗ |
| [**Intervals, the cube, splines and wavelets**](docs/IntervalCube.md): piecewise polynomials and splines on `[0, 1]`, the circle and `[0, 1]^d`, Whitney's inequality, coordinate and isotropic moduli, multiwavelets, the Haar system | ✅ | ✗ |
| [**Daubechies wavelets**](docs/Daubechies.md): masks of every order by Fejér–Riesz, the scaling function and its orthonormal translates, Sobolev and Hölder regularity, the D4 Hölder exponent, the multiresolution analysis, Jackson and Bernstein inequalities, Besov spaces by Daubechies coefficients | ✅ | ✗ |
| [**Function spaces on `ℝ^d`**](docs/Rd.md): convolution, Littlewood–Paley blocks, differences, local means, atoms, invariance under changes of variables | ✅ | ✗ |
| [**Triebel–Lizorkin spaces**](docs/TriebelLizorkin.md): mixed norms, maximal functions, the Calderón–Zygmund decomposition, the Fefferman–Stein inequality, local means, ball means of differences, atoms, the torus | ✅ | ✗ |
| [**Sobolev spaces on `ℝ^d`**](docs/SobolevRd.md): weak derivatives on open sets, `W^m_p(Ω)` and `W^m_p(ℝ^d)`, weak derivatives as derivatives of tempered distributions, Mathlib's `H^s` as `F^s_{2,2}` and `B^s_{2,2}`, `W^1_2 = H^1`, `H^1` on bounded Lipschitz domains with weak gradient and trace, Rellich's theorem, the Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)`, `H^s_0(Ω)` on open sets and their duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`, the trace space `H^{1/2}(Γ)` of a bounded Lipschitz domain with trace and extension operators, the area formula for Lipschitz graphs with the outward unit normal, the surface measure of a bounded Lipschitz domain with `L_2(Γ)` and the trace into it, the square function theorem `L_p = F^0_{p,2}` for `1 < p < ∞`, `W^m_p = F^m_{p,2}` with the Besov sandwich, the Sobolev embeddings, `H^{s,p} ∩ L_p = F^s_{p,2}`, `H^{s,p} = F^s_{p,2}` for `s ≥ 0`, `W^m_p = H^{m,p}`, the extension theorem for `W^1_p` on bounded Lipschitz domains with `H^1(Ω) = W^1_2(Ω)`, Gauss–Green and Green's formula on Lipschitz graph domains, Green's formula on bounded Lipschitz domains with the zero extension of functions with vanishing trace, and `ker γ = H^1_0(Ω)` with `H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)` | ✅ | ✗ |
| [**Domains, manifolds and traces**](docs/DomainsTraces.md): Lipschitz graph and bounded Lipschitz domains, traces, the half-space, compact manifolds with boundary, smooth domains | ✅ | ✗ |
| [**Dominating mixed smoothness**](docs/MixedSmoothness.md): mixed differences, mixed local means, tensor Littlewood–Paley blocks, hyperbolic crosses | ✅ | ✗ |

Lean: ✅ every file proved without `sorry` · 🟡 some statement still `sorry` · ⬜ planned.
Checked (human-checked): ✅ mathematics and documentation both reviewed by the author ·
🧮 mathematics reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A block shows the
weakest mark of its files; the block documents hold the tables per file, and a change to a file
resets its row there and the block here to ✗.

## Organisation

Two libraries. `ApproximationSpaces` holds the abstract theory, which mentions neither functions
nor measures; `FunctionSpaces` holds the Besov, Triebel–Lizorkin and Sobolev spaces built on
it, in folders by setting.
The blocks map onto the folders as follows: approximation spaces are all of
`ApproximationSpaces/`; Besov and Sobolev spaces on measure spaces are
`FunctionSpaces/{Lp,Scheme,Besov,Sobolev,Spectral}`; the torus is `FunctionSpaces/Torus/` with
the torus traces in `FunctionSpaces/Traces/`; intervals, the cube, splines and wavelets are
`FunctionSpaces/{Interval,Cube,Wavelets}` without `FunctionSpaces/Wavelets/Daubechies/`, which
holds the Daubechies wavelets, and `FunctionSpaces/TranslationAlgebra.lean`; function
spaces on `ℝ^d`, domains and traces, and mixed smoothness share `FunctionSpaces/Rd/`, with the
manifolds in `FunctionSpaces/Manifold/`; the Triebel–Lizorkin block is the mixed norms in
`FunctionSpaces/Lp/MixedNorms.lean`, the files
`FunctionSpaces/Rd/{DyadicCubes,HardyLittlewoodMaximal,CalderonZygmund}`,
`FunctionSpaces/Rd/{FeffermanStein,KernelMajorants}` and `FunctionSpaces/Rd/TriebelLizorkin*`, and
`FunctionSpaces/Torus/{TriebelLizorkin,PeriodicLift,FeffermanStein,TriebelLizorkinLocalMeans}`;
Sobolev spaces on `ℝ^d` are the files `SchwartzCutoff`, `WeakDerivatives`,
`SobolevTwoLittlewoodPaley`, `LipschitzDomainH1`, `RellichCompactness`,
`SobolevRestrictionSpaces`, `SobolevDuality`, `BoundaryTraceSpace`, `LipschitzGraphArea`,
`SurfaceMeasure`, `DilationFamilies`, `ConvolutionAdjoint`, `PlancherelBounds`,
`CalderonZygmundSigned`, `VectorValuedWeakType`, `VectorValuedSingularIntegrals`,
`SquareFunction`, `DerivativeKernels`, `SobolevTriebelLizorkin`, `SobolevEmbedding`,
`UniformSchwartzFamilies`, `BesselPotentialLifting`, `DivergenceKernels`, `SobolevExtension`,
`LipschitzGraphGreen`, `LipschitzDomainGreen` and `TraceKernel` in `FunctionSpaces/Rd/`, with
`WeakType`, `LayerCake`, `Marcinkiewicz` and `NormingFamily` in `FunctionSpaces/Lp/`.
Each block document lists its files.
[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
[docs/FEECInterface.md](docs/FEECInterface.md) describes the interface to a FEEC/BEEC library
built on this project: the Lean names of its interface items, the decisions behind them, and what
that library builds itself.
`blueprint/` holds the LaTeX source of the blueprint and the scripts that check and link its
`\lean` references.

## What is left to do

* **Reiteration** for approximation and interpolation spaces.
* **Eigenbases of the Laplace–Beltrami operator** on compact manifolds (Rellich's compactness,
  elliptic regularity), joining the spectral and the chart descriptions of Besov spaces.
* **Triebel–Lizorkin spaces** with `p = 1` or `q = 1`, and their ball means and atoms on the
  torus.
* **Sobolev spaces**: Sobolev spaces on the torus for all `p`, the critical Sobolev embedding,
  Mihlin multipliers and `H^{s,p}` for `s < 0`.
* **Higher smoothness**: splines on domains; for the Daubechies wavelets the sharp `L_p`
  exponents of the scaling functions, Hölder exponents beyond D4, and `ℝ^d`.
* **The quasi-Banach range** `0 < p, q < 1`, the setting of nonlinear `n`-term approximation.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib in `lake-manifest.json`, so a clone builds against Lean /
Mathlib `v4.35.0-rc2`:

```bash
lake exe cache get   # downloads the prebuilt Mathlib oleans
lake build           # builds the project
```

Run `lake` from inside this folder, since `elan` reads `lean-toolchain` from the
working directory, and do not run `lake update`: it re-resolves the dependencies and
makes the build non-reproducible.

The blueprint follows the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) convention and needs a
TeX installation, `graphviz` for the dependency graph, and the `leanblueprint` package:

```bash
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/index.html and the dependency graph
python blueprint/scripts/check_lean_decls.py   # checks that every \lean{Decl} resolves
```

GitHub Actions builds the project and the blueprint on every push to `main`, deploys the
blueprint to GitHub Pages, and puts the PDF and the dependency graphs as SVG images on the
branch `blueprint-build`, replacing its single commit each time. `main` holds no build
output. `node blueprint/scripts/dep_graph_svg.js` draws the images from a local web build.

## AI assistance

The formalisation was written with Claude Code. Every statement and proof was checked
by Lean; the mathematical design, the choice of statements and the review of what the
proofs actually say are the author's. The columns "Human-checked" in the tables record that
review.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics **140**,
  Elsevier/Academic Press, 2003. Sobolev spaces on domains and their compact embeddings,
  with the rooms-and-passages domains.
* L. Becker, M. I. de Frutos-Fernández, L. Diedering, F. van Doorn, S. Gouëzel, A. Jamneshan,
  E. Karunus, E. van de Meent, P. Monticone, J. Mulder-Sohn, J. Portegies, J. Roos, M. Rothgang,
  R. Srivastava, J. Sundstrom, J. Tan, C. Thiele, *A blueprint for the formalization of
  Carleson's theorem on convergence of Fourier series*, preprint, 2024, revised 2025,
  [arXiv:2405.06423](https://arxiv.org/abs/2405.06423). The Calderón–Zygmund decomposition on
  doubling metric measure spaces.
* L. Becker, M. I. de Frutos-Fernández, L. Diedering, F. van Doorn, S. Gouëzel, E. Karunus,
  E. van de Meent, P. Monticone, J. Mulder-Sohn, J. Portegies, J. Roos, M. Rothgang,
  J. Sundstrom, J. Tan, *Formalizing Carleson's theorem in Lean*, preprint, 2026,
  [arXiv:2609.31334](https://arxiv.org/abs/2609.31334). The definitions of weak and strong type,
  taken over here, and the real interpolation theorem.
* A. Benedek, A. P. Calderón, R. Panzone, *Convolution operators on Banach space valued
  functions*, Proc. Nat. Acad. Sci. U.S.A. **48** (1962), no. 3, 356–365. Singular integrals
  with values in a Hilbert space.
* J. Bergh, J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren der
  mathematischen Wissenschaften **223**, Springer-Verlag, 1976. Real interpolation and the
  K-functional.
* A. P. Calderón, *Lebesgue spaces of differentiable functions and distributions*, in: Partial
  Differential Equations, Proc. Sympos. Pure Math. **4**, American Mathematical Society, 1961,
  33–49. Sobolev spaces as Bessel potential spaces, `W^m_p = H^{m,p}`.
* A. P. Calderón, A. Zygmund, *On the existence of certain singular integrals*, Acta Math.
  **88** (1952), no. 1, 85–139. The Calderón–Zygmund decomposition.
* S. N. Chandler-Wilde, D. P. Hewett, A. Moiola, *Sobolev spaces on non-Lipschitz subsets of
  ℝ^n with application to boundary integral equations on fractal screens*, Integral Equations
  Operator Theory **87** (2017), no. 2, 179–224. Sobolev spaces on domains as restriction spaces.
* I. Daubechies, *Ten Lectures on Wavelets*, CBMS-NSF Regional Conference Series in Applied
  Mathematics **61**, SIAM, 1992. The construction of the compactly supported wavelets and the
  cascade algorithm.
* I. Daubechies, J. C. Lagarias, *Two-scale difference equations. II. Local regularity,
  infinite products of matrices and fractals*, SIAM J. Math. Anal. **23** (1992), no. 4,
  1031–1079. The matrix method for the Hölder exponent.
* R. A. DeVore, G. G. Lorentz, *Constructive Approximation*, Grundlehren der
  mathematischen Wissenschaften **303**, Springer-Verlag, 1993. Chapter 7: approximation
  spaces, Jackson and Bernstein inequalities, and their relation to interpolation.
* R. A. DeVore, R. C. Sharpley, *Besov spaces on domains in ℝ^d*, Trans. Amer. Math. Soc.
  **335** (1993), no. 2, 843–864. The modulus of smoothness on a domain.
* T. Eirola, *Sobolev characterization of solutions of dilation equations*, SIAM J. Math.
  Anal. **23** (1992), no. 4, 1015–1030. The transfer operator and the Sobolev exponent.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  Textbooks in Mathematics, CRC Press, 2015. The area formula.
* H. Federer, *Geometric Measure Theory*, Grundlehren der mathematischen Wissenschaften **153**,
  Springer-Verlag, 1969. The area formula.
* C. Fefferman, E. M. Stein, *Some maximal inequalities*, Amer. J. Math. **93** (1971), no. 1,
  107–115. The vector-valued maximal inequality.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics **249**,
  Springer, 2014. Littlewood–Paley theory, vector-valued singular integrals and Marcinkiewicz
  interpolation.
* N. Guglielmi, V. Yu. Protasov, *Invariant polytopes of linear operators with applications to
  regularity of wavelets and of subdivisions*, SIAM J. Matrix Anal. Appl. **37** (2016), no. 1,
  18–52, [arXiv:1502.01192](https://arxiv.org/abs/1502.01192). Hölder exponents of the
  Daubechies wavelets of higher order.
* E. Hernández, G. Weiss, *A First Course on Wavelets*, Studies in Advanced Mathematics, CRC
  Press, 1996. Multiresolution analyses.
* R. Hiptmair, D. Pauly, E. Schulz, *Traces for Hilbert complexes*, J. Funct. Anal. **284**
  (2023), Paper No. 109905. Assumption F, the compactness of the restriction to bounded domains.
* L. Hörmander, *Estimates for translation invariant operators in L^p spaces*, Acta Math.
  **104** (1960), no. 1–2, 93–140. The Hörmander condition.
* J. Marcinkiewicz, *Sur l'interpolation d'opérations*, C. R. Acad. Sci. Paris **208** (1939),
  1272–1273. The interpolation theorem.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University
  Press, 2000. Traces on Lipschitz domains and the kernel of the trace map.
* S. M. Nikol'skii, *Approximation of Functions of Several Variables and Imbedding
  Theorems*, Grundlehren der mathematischen Wissenschaften **205**, Springer-Verlag, 1975.
  The Nikolskii inequality and the embedding theorems it yields.
* H. Ojanen, *Orthonormal compactly supported wavelets with optimal Sobolev regularity:
  numerical results*, Appl. Comput. Harmon. Anal. **10** (2001), no. 1, 93–98,
  [arXiv:math/9807089](https://arxiv.org/abs/math/9807089). The Sobolev exponents of the
  Daubechies wavelets.
* A. Pietsch, *Approximation spaces*, J. Approx. Theory **32** (1981), no. 2, 115–134.
  The definition of approximation schemes and spaces followed here.
* V. S. Rychkov, *On restrictions and extensions of the Besov and Triebel–Lizorkin spaces with
  respect to Lipschitz domains*, J. London Math. Soc. (2) **60** (1999), no. 1, 237–257. Local
  means and the universal extension operator for Lipschitz domains.
* C. Schneider, J. Vybíral, *Non-smooth atomic decompositions, traces on Lipschitz domains, and
  pointwise multipliers in function spaces*, J. Funct. Anal. **264** (2013), no. 5, 1197–1237,
  [arXiv:1201.2280](https://arxiv.org/abs/1201.2280). Atoms with bounds instead of smoothness, and
  traces on Lipschitz domains through atoms.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  Mathematical Series **30**, Princeton University Press, 1970. The extension theorem for
  Sobolev spaces on Lipschitz domains, the Calderón–Zygmund decomposition, Marcinkiewicz
  interpolation, vector-valued singular integrals, the Littlewood–Paley theorem and Calderón's
  theorem `W^m_p = H^{m,p}`.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Princeton Mathematical Series **43**, Princeton University Press, 1993. The
  maximal function and the Calderón–Zygmund decomposition.
* V. Temlyakov, *Multivariate Approximation*, Cambridge University Press, 2018. Periodic
  function spaces and trigonometric approximation.
* H. Triebel, *Theory of Function Spaces*, Monographs in Mathematics **78**, Birkhäuser, 1983.
  Besov and Sobolev spaces and the equivalence of their definitions, among them
  `L_p = F^0_{p,2}`, `W^m_p = F^m_{p,2}` and `H^{s,p} = F^s_{p,2}`.
* H. Triebel, *Theory of Function Spaces II*, Monographs in Mathematics **84**, Birkhäuser, 1992.
  Triebel–Lizorkin spaces, local means, ball means of differences and atoms; the atoms there are
  `(s,p)`-atoms normalised in `L_p`, here they are normalised in `L_∞`.
* T. Ullrich, *Function spaces with dominating mixed smoothness, characterization by
  differences*, Jenaer Schriften zur Mathematik und Informatik Math/Inf/05/06, 2006. Mixed
  differences and mixed local means.
* L. F. Villemoes, *Energy moments in time and frequency for two-scale difference equation
  solutions and wavelets*, SIAM J. Math. Anal. **23** (1992), no. 6, 1519–1543. The transfer
  operator and the Sobolev exponent.
* J. Vybíral, *Function spaces with dominating mixed smoothness*, Dissertationes Math. **436**
  (2006), 1–73. Tensor Littlewood–Paley decompositions of spaces of dominating mixed smoothness.
