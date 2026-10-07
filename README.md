# Function spaces via approximation in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of **Besov, Triebel–Lizorkin and Sobolev spaces** on several
domains, their equivalent **characterisations** and their **embedding theorems**, built on the
theory of **approximation spaces**. The project is work in progress; the details are in eight
documents under [`docs/`](docs/), listed under [What is formalised](#what-is-formalised).

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

Sobolev spaces appear as `W^m_2` through weak derivatives and as `H^s` through Fourier
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
  `‖f - S_N f‖_p ≤ C 2^(-sN) (N + 1)^((d-1)(1-1/q)) ‖(2^(s|k|_1) ‖δ_k ⋆ f‖_p)_k‖_{ℓ_q}`
  (`Rd.enorm_sub_hyperbolicSum_le_mixedLPNorm`).

## What is formalised

| Block | Lean | Checked |
|---|---|---|
| [**Approximation spaces**](docs/ApproximationSpaces.md): schemes, `A^s_q` and its embeddings, lifting and the Nikolskii transfer theorem, the representation theorem, moduli of smoothness, decompositions, traces and intrinsic norms | ✅ | ✗ |
| [**Besov and Sobolev spaces on measure spaces**](docs/BesovSobolev.md): schemes of functions, Besov and Sobolev embeddings under a Nikolskii inequality, spectral schemes, eigenbases | ✅ | ✗ |
| [**The torus**](docs/Torus.md): trigonometric polynomials, `H^s`, embeddings, Fourier coefficients, moduli of smoothness and smooth Littlewood–Paley blocks for all `p`, weak derivatives, traces | ✅ | ✗ |
| [**Intervals, the cube, splines and wavelets**](docs/IntervalCube.md): piecewise polynomials and splines on `[0, 1]`, the circle and `[0, 1]^d`, Whitney's inequality, coordinate and isotropic moduli, multiwavelets, the Haar system | ✅ | ✗ |
| [**Function spaces on `ℝ^d`**](docs/Rd.md): convolution, Littlewood–Paley blocks, differences, local means, atoms, invariance under changes of variables | ✅ | ✗ |
| [**Triebel–Lizorkin spaces**](docs/TriebelLizorkin.md): mixed norms, maximal functions, the Calderón–Zygmund decomposition, the Fefferman–Stein inequality, local means, ball means of differences, atoms, the torus | ✅ | ✗ |
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
`FunctionSpaces/{Interval,Cube,Wavelets}` and `FunctionSpaces/TranslationAlgebra.lean`; function
spaces on `ℝ^d`, domains and traces, and mixed smoothness share `FunctionSpaces/Rd/`, with the
manifolds in `FunctionSpaces/Manifold/`; the Triebel–Lizorkin block is the mixed norms in
`FunctionSpaces/Lp/MixedNorms.lean`, the files
`FunctionSpaces/Rd/{DyadicCubes,HardyLittlewoodMaximal,CalderonZygmund}`,
`FunctionSpaces/Rd/{FeffermanStein,KernelMajorants}` and `FunctionSpaces/Rd/TriebelLizorkin*`, and
`FunctionSpaces/Torus/{TriebelLizorkin,PeriodicLift,FeffermanStein,TriebelLizorkinLocalMeans}`.
Each block document lists its files.
[MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
`blueprint/` holds the LaTeX source of the blueprint and the scripts that check and link its
`\lean` references.

## What is left to do

* **Reiteration** for approximation and interpolation spaces.
* **Eigenbases of the Laplace–Beltrami operator** on compact manifolds (Rellich's compactness,
  elliptic regularity), joining the spectral and the chart descriptions of Besov spaces.
* **Sobolev spaces for all `p`**: weak derivatives in `L_p`, Fourier multipliers and
  `H^s_p = F^s_{p,2}`.
* **Triebel–Lizorkin spaces** with `p = 1` or `q = 1`, and their ball means and atoms on the
  torus.
* **Higher smoothness**: splines on domains, and compactly supported wavelets such as
  Daubechies'.
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

* J. Bergh, J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren der
  mathematischen Wissenschaften **223**, Springer-Verlag, 1976. Real interpolation and the
  K-functional.
* R. A. DeVore, G. G. Lorentz, *Constructive Approximation*, Grundlehren der
  mathematischen Wissenschaften **303**, Springer-Verlag, 1993. Chapter 7: approximation
  spaces, Jackson and Bernstein inequalities, and their relation to interpolation.
* R. A. DeVore, R. C. Sharpley, *Besov spaces on domains in ℝ^d*, Trans. Amer. Math. Soc.
  **335** (1993), no. 2, 843–864. The modulus of smoothness on a domain.
* C. Fefferman, E. M. Stein, *Some maximal inequalities*, Amer. J. Math. **93** (1971), no. 1,
  107–115. The vector-valued maximal inequality.
* S. M. Nikol'skii, *Approximation of Functions of Several Variables and Imbedding
  Theorems*, Grundlehren der mathematischen Wissenschaften **205**, Springer-Verlag, 1975.
  The Nikolskii inequality and the embedding theorems it yields.
* A. Pietsch, *Approximation spaces*, J. Approx. Theory **32** (1981), no. 2, 115–134.
  The definition of approximation schemes and spaces followed here.
* V. S. Rychkov, *On restrictions and extensions of the Besov and Triebel–Lizorkin spaces with
  respect to Lipschitz domains*, J. London Math. Soc. (2) **60** (1999), no. 1, 237–257. Local
  means and the universal extension operator for Lipschitz domains.
* C. Schneider, J. Vybíral, *Non-smooth atomic decompositions, traces on Lipschitz domains, and
  pointwise multipliers in function spaces*, J. Funct. Anal. **264** (2013), no. 5, 1197–1237,
  [arXiv:1201.2280](https://arxiv.org/abs/1201.2280). Atoms with bounds instead of smoothness, and
  traces on Lipschitz domains through atoms.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Princeton Mathematical Series **43**, Princeton University Press, 1993. The
  maximal function and the Calderón–Zygmund decomposition.
* V. Temlyakov, *Multivariate Approximation*, Cambridge University Press, 2018. Periodic
  function spaces and trigonometric approximation.
* H. Triebel, *Theory of Function Spaces*, Monographs in Mathematics **78**, Birkhäuser, 1983.
  Besov and Sobolev spaces and the equivalence of their definitions.
* H. Triebel, *Theory of Function Spaces II*, Monographs in Mathematics **84**, Birkhäuser, 1992.
  Triebel–Lizorkin spaces, local means, ball means of differences and atoms; the atoms there are
  `(s,p)`-atoms normalised in `L_p`, here they are normalised in `L_∞`.
* T. Ullrich, *Function spaces with dominating mixed smoothness, characterization by
  differences*, Jenaer Schriften zur Mathematik und Informatik Math/Inf/05/06, 2006. Mixed
  differences and mixed local means.
* J. Vybíral, *Function spaces with dominating mixed smoothness*, Dissertationes Math. **436**
  (2006), 1–73. Tensor Littlewood–Paley decompositions of spaces of dominating mixed smoothness.
