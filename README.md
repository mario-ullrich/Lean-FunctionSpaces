# Function spaces via approximation in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of **approximation spaces** in the sense of Pietsch, and of
**Besov and Sobolev spaces** defined through them, with their **embedding theorems**. An
approximation scheme is an increasing family of sets `A₀ ⊆ A₁ ⊆ ⋯` in a normed space, and a
function belongs to the approximation space `A^s_q` when its errors of best approximation
`E_n(f) = dist(f, A_n)` decay like `n^(-s)` in the `ℓ_q` sense. Besov spaces on a general
finite measure space are the approximation spaces of `L_p` for a scheme of bounded
continuous functions, and the embedding theorems follow from the abstract theory together
with a Nikolskii inequality for the scheme. The torus is the first concrete instance. The
project is work in progress; the table below lists what is formalised.

* **Blueprint** (a webpage explaining the mathematics):
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/>
* **Blueprint as PDF**:
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/dep_graph_document.html>

## The setting

Let `X` be a real normed space. An **approximation scheme** is a sequence of subsets
`A₀ ⊆ A₁ ⊆ A₂ ⊆ ⋯` of `X` with `A₀ = {0}`, `c · a ∈ A_n` for real `c` and `a ∈ A_n`, and
`A_m + A_n ⊆ A_{m+n}`. The sets need not be subspaces: for `n`-term approximation from a
dictionary `D`, `A_n` is the set of linear combinations of at most `n` elements of `D`.
The **error of best approximation** of `f ∈ X` is `E_n(f) = inf { ‖f - a‖ : a ∈ A_n }`.

For `s > 0` and `1 ≤ q ≤ ∞`, the **approximation space** `A^s_q` consists of those `f` with

```
‖f‖_{A^s_q} = ‖ (n^(s - 1/q) E_{n-1}(f))_{n ≥ 1} ‖_{ℓ_q}  <  ∞ .
```

For a finite measure space `(Ω, μ)` and a scheme `S` of bounded continuous functions on `Ω`,
the **Besov space** is `B^s_{p,q}(Ω, S) = A^s_q(L_p(μ), S)`: the functions whose best
approximation from `S` in `L_p` decays at rate `s`. On the torus `𝕋^d` with `S_n` the
trigonometric polynomials of degree `< n`, these are the classical periodic Besov spaces.

## Main results

* **The error of best approximation.** For every approximation scheme, `E₀(f) = ‖f‖`,
  `E_n(f)` decreases in `n`, `E_n(c f) = |c| E_n(f)`, `E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`,
  and `|E_n(f) - E_n(g)| ≤ ‖f - g‖`
  (`ApproximationScheme.approxError_zero_left`, `.approxError_anti`, `.approxError_smul`,
  `.approxError_add_le`, `.abs_approxError_sub_le`). The errors tend to zero exactly on the
  closure of `⋃ A_n` (`ApproximationScheme.tendsto_approxError_zero_iff`).
* **The dyadic quasi-norm.** For `s ≥ 0` and `1 ≤ q ≤ ∞`,
  `‖f‖_{A^s_q} ≤ 2^s (‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}) ≤ 4 · 4^s ‖f‖_{A^s_q}`
  (`ApproximationScheme.approxNorm_le_approxNormDyadic`,
  `.approxNormDyadic_le_approxNorm`).
* **Linear structure.** For `s ≥ 0` and `1 ≤ q ≤ ∞`, `A^s_q` is a linear subspace of `X`
  containing every `A_n`, `‖f‖ ≤ ‖f‖_{A^s_q}`, and
  `‖f + g‖_{A^s_q} ≤ 8 · 8^s (‖f‖_{A^s_q} + ‖g‖_{A^s_q})`
  (`ApproximationScheme.approxSpace`, `.memApprox_of_mem`, `.enorm_le_approxNorm`,
  `.approxNorm_add_le`). For `s > 0` it lies in the closure of `⋃ A_n`
  (`ApproximationScheme.mem_closure_iUnion_of_memApprox`).
* **Embeddings.** For `0 ≤ t` and `1 ≤ q, r ≤ ∞`, `A^s_q ⊆ A^t_r` whenever `t < s`, or
  `t = s` and `q ≤ r` (`ApproximationScheme.MemApprox.mono`); for `t < s` the norm bound is
  `‖f‖_{A^t_r} ≤ (1 - 2^(t-s))⁻¹ ‖f‖_{A^s_q}` in the dyadic form
  (`ApproximationScheme.approxNormDyadic_le_of_lt`).
* **Functoriality.** A bounded linear map `T : X → Y` with `T(A_n) ⊆ B_n` satisfies
  `E^B_n(T f) ≤ ‖T‖ E^A_n(f)` and `‖T f‖_{B^s_q} ≤ ‖T‖ ‖f‖_{A^s_q}`
  (`ApproximationScheme.approxError_map_le`, `.approxNorm_map_le`).
* **Lifting.** Let `ι : Y → X` be a bounded linear map from a Banach space `Y` such that every
  `a ∈ A_n`, `n ≥ 1`, is `ι y` with `‖y‖ ≤ C n^β ‖a‖` (a Bernstein inequality). If
  `β ≥ 0` and `∑_k 2^(kβ) E_{2^k}(f) < ∞`, then `f = ι y` for some `y ∈ Y` with
  `‖y‖ ≤ K (‖f‖ + ∑_k 2^(kβ) E_{2^k}(f))` (`ApproximationScheme.exists_preimage_of_liftBound`).
* **Nikolskii transfer theorem.** If moreover `ι` is injective and `0 ≤ α < s`, and every
  `a ∈ A_n` is `ι y` with `‖y‖ ≤ C n^α ‖a‖` (a Nikolskii inequality), then every
  `f ∈ A^s_q(X)` is `ι y` for some `y` in the approximation space `B^{s-α}_q(Y)` of the
  pulled-back scheme `B_n = ι⁻¹(A_n)`, with `‖y‖_{B^{s-α}_q} ≤ K ‖f‖_{A^s_q}`
  (`ApproximationScheme.exists_preimage_of_nikolskii`).
* **The representation theorem.** Let `ι : Y → X` satisfy Jackson's inequality
  `E_n(ι y) ≤ C n^(-r) ‖y‖` and Bernstein's inequality (every `a ∈ A_n` is `ι y` with
  `‖y‖ ≤ C n^r ‖a‖`) of order `r`. Then for `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q` is the real
  interpolation space `(X, Y)_{s/r, q}`, with equivalent norms
  (`ApproximationScheme.memApprox_iff_memInterp`,
  `.approxNormDyadic_le_interpNorm_of_jackson`,
  `.interpNorm_le_approxNormDyadic_of_bernstein`). In particular two schemes with Jackson and
  Bernstein inequalities of the same order for the same `ι` have the same approximation
  spaces (`ApproximationScheme.approxSpace_eq_of_jackson_bernstein`).
* **Besov spaces through moduli of smoothness.** For `f ∈ L_2(𝕋^d)` let
  `ω(f, t)_2 = sup_{‖h‖ ≤ t} ‖f(· + h) - f‖_2`. Jackson's theorem
  `E_n(f)_2² ≤ d ω(f, 1/n)_2²` holds (`Torus.approxSeq_sq_le_card_mul_modulus_sq`), and for
  `0 < s < 1` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{2,q}(𝕋^d)` iff
  `‖f‖_2 + ‖(2^(js) ω(f, 2^(-j))_2)_j‖_{ℓ_q} < ∞`, with equivalent norms
  (`Torus.memBesov_iff_modulusNorm_lt_top`, `Torus.approxNormDyadic_le_modulusNorm`,
  `Torus.modulusNorm_le_approxNormDyadic`).
* **Traces on the torus.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `s > 0`, the restriction
  `f ↦ f(0, ·)` to the face `{x_0 = 0}` of `𝕋^(n+1)` extends from trigonometric polynomials to
  a map from `B^{s+1/p}_{p,q}(𝕋^(n+1))` into `B^s_{p,q}(𝕋^n)`, and every element of
  `B^s_{p,q}(𝕋^n)` is a trace (`Torus.trace_besov`). The proof uses the trace inequality
  `‖a(0, ·)‖_p ≤ (2⌈p/2⌉ m)^(1/p) ‖a‖_p` for polynomials of degree `< m`
  (`Torus.eLpNorm_restrictFace_le`) and an extension by the normalised Fejér kernel.
* **Sobolev spaces through weak derivatives.** Call `g ∈ L_2(𝕋^d)` the weak derivative
  `∂^α f` of `f ∈ L_2(𝕋^d)` if `ĝ(k) = (2πi k)^α f̂(k)` for all `k ∈ ℤ^d`, and let
  `W^m_2(𝕋^d)` consist of the `f` all of whose weak derivatives of order `|α| ≤ m` lie in
  `L_2`. Then `f ∈ W^m_2(𝕋^d)` iff `∑_k (1 + max_i |k_i|)^(2m) |f̂(k)|² < ∞`
  (`Torus.memSobolev_iff`), and for `m ≥ 1`, `W^m_2(𝕋^d) = B^m_{2,2}(𝕋^d)`
  (`Torus.memSobolev_iff_memBesov`).
* **Moduli of smoothness and approximation.** Let `ω(f, 2^(-k))` be subadditive with
  `ω(f, t) ≤ C₀ ‖f‖`, and assume a Jackson inequality `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for
  `k ≥ k₀` and an inverse inequality `ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`. Then
  for `0 ≤ s < θ` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞`,
  with equivalent quasi-norms (`ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top`).
* **Whitney's inequality.** For `1 ≤ p < ∞`, `r ≥ 1` and `0 < t ≤ 1/3` there is `W` such that
  every continuous `F` has a polynomial `P` of degree `< r` with
  `‖F - P‖_{L_p[0, 1]} ≤ W ω_r(F, t, [0, 1])_p` (`Interval.exists_eLpNorm_sub_polyFun_le_modulus`),
  with the modulus `ω_r` of the next item. In `L_p[0, 1]` the error of best approximation by the
  polynomials of degree `< r` satisfies `E_1(f)_p ≤ W ω_r(f, 2^(-m), [0, 1])_p` for `m ≥ 2`
  (`Interval.exists_approxSeq_ppScheme_one_le`).
* **Piecewise polynomials on an interval.** Let `V_k ⊆ L_p[0, 1]` consist of the functions that
  agree on each dyadic interval `[n 2^(-k), (n+1) 2^(-k))` with a polynomial of degree `< r`,
  and let `ω_r(f, t, [0, 1])_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r f‖_{L_p[0, 1-rh]}`. For `1 ≤ p < ∞`
  and `r ≥ 1`, `E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p` for `k ≥ 1`
  (`Interval.approxSeq_ppScheme_le`), with Whitney's inequality a bound
  `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k), [0, 1])_p` for all `k ≥ 0`
  (`Interval.exists_approxSeq_ppScheme_le`), and there is `C` with
  `ω_r(a, 2^(-k), [0, 1])_p ≤ C 2^(-(k-j)/p) ‖a‖_p` for all `a ∈ V_j` and `k ≥ j`
  (`Interval.exists_inverse_ppScheme`). Hence for `1 ≤ q ≤ ∞` and `0 ≤ s < 1/p`, `f ∈ A^s_q`
  iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
  (`Interval.memApprox_ppScheme_iff`), so the approximation space is `B^s_{p,q}[0, 1]` for
  `0 < s < 1/p`.
* **Piecewise polynomials on the circle.** Identify `L_p(𝕋)` with `L_p[0, 1]` through the
  periodic extension `f̃(x) = f(x - ⌊x⌋)`, and let
  `ω_r^per(f, t)_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r f̃‖_{L_p[0, 1]}`. For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
  `r ≥ 1` and `0 ≤ s < 1/p`, `f ∈ A^s_q` of the dyadic piecewise polynomials iff
  `‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (`Interval.memApprox_ppScheme_iff_per`).
  In particular `B^s_{p,q}[0, 1]` and `B^s_{p,q}(𝕋)` contain the same functions for
  `0 < s < 1/p` (`Interval.lqNorm_modulus_lt_top_iff_perModulus`).
* **Splines and higher smoothness.** Let `S_k ⊆ L_p[0, 1]` consist of the splines of order
  `r ≥ 1` on the dyadic grid of level `k`: piecewise polynomials of degree `< r` that are `r - 2`
  times continuously differentiable. For `1 ≤ p < ∞` there is `C` with
  `E_{2^k}(f)_p ≤ C ω_r(f, 2^(-k), [0, 1])_p` for all `k ≥ 0`
  (`Interval.exists_approxSeq_splineScheme_le`) and with
  `ω_r(a, 2^(-k), [0, 1])_p ≤ C 2^(-(k-j)(r-1+1/p)) ‖a‖_p` for `a ∈ S_j`, `k ≥ j`
  (`Interval.exists_inverse_splineScheme`). Hence for `1 ≤ q ≤ ∞` and `0 ≤ s < r - 1 + 1/p`,
  `f ∈ A^s_q` iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
  (`Interval.memApprox_splineScheme_iff`). The proof uses cardinal B-splines with Marsden's
  identity (`Interval.polyFun_eq_sum_bsplineCoef`) and a quasi-interpolant built from local
  projections, which reproduces every spline in `S_k` (`Interval.ppFun_qiPieces_ppFun`); so the
  B-splines `N_r(2^k x - n)`, `-r < n < 2^k`, span `S_k` (`Interval.ppFun_eq_sum_bsplinePieces`).
* **Splines on the circle.** Let `S_k(𝕋) ⊆ L_p(𝕋) = L_p[0, 1]` consist of the periodic splines
  of order `r ≥ 1` and level `k`, the splines whose periodic extension is a spline on `ℝ`. For
  `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `0 ≤ s < r - 1 + 1/p`, `f ∈ A^s_q` of the periodic splines iff
  `‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Interval.memApprox_perSplineScheme_iff`), with Jackson's inequality from level `r` on
  (`Interval.exists_approxSeq_perSplineScheme_le`) and the inverse inequality of order
  `r - 1 + 1/p` (`Interval.exists_inverse_perSplineScheme`).
* **Local projections and multiscale details.** Let `P_k` be the projection of `L_p[0, 1]`
  onto the piecewise polynomials of degree `< r` on the dyadic intervals of level `k` that is
  the `L_2`-orthogonal projection on every interval. For `1 ≤ p < ∞` there is `C` with
  `‖P_k f‖_p ≤ C ‖f‖_p` for all `k` and `f` (`Interval.ppProj`, `Interval.norm_ppProj_le`), and
  for `s > 0`, `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff
  `‖P_0 f‖_p + ‖(2^(ks) ‖P_{k+1} f - P_k f‖_p)_k‖_{ℓ_q} < ∞`
  (`Interval.memApprox_ppScheme_iff_block`). For `0 < s < 1/p` this characterises
  `B^s_{p,q}[0, 1]` and `B^s_{p,q}(𝕋)` (`Interval.lqNorm_modulus_lt_top_iff_block`,
  `Interval.lqNorm_perModulus_lt_top_iff_block`).
* **Multiwavelets.** Let `ψ_1, …, ψ_r` be an orthonormal basis of the piecewise polynomials of
  degree `< r` on `[0, 1/2)` and `[1/2, 1)` that are `L_2`-orthogonal to the polynomials of
  degree `< r` (`Alpert.psi`), and `ψ_{k,m,i}(x) = 2^(k/2) ψ_i(2^k x - m)`. For `1 ≤ p < ∞`,
  `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` of the dyadic piecewise polynomials of degree `< r` iff
  `‖P_0 f‖_p + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, ψ_{k,m,i}⟩)_{m,i}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`
  (`Alpert.memApprox_ppScheme_iff_coeff`); for `0 < s < 1/p` this characterises
  `B^s_{p,q}[0, 1]` and `B^s_{p,q}(𝕋)` (`Alpert.lqNorm_modulus_lt_top_iff_coeff`,
  `Alpert.lqNorm_perModulus_lt_top_iff_coeff`).
* **Piecewise polynomials on the cube.** On `Q = [0, 1]^d` let
  `ω_r^(i)(f, t)_p = sup_{0 ≤ h ≤ t} ‖Δ^r_{h e_i} f‖_{L_p({x ∈ Q : x_i ≤ 1 - rh})}` be the modulus
  in coordinate `i` and `ω_r = ∑_i ω_r^(i)`. Let `V_k^d ⊆ L_p(Q)` consist of the bounded
  measurable functions that have in every coordinate `i` the form `∑_j c_j(x) φ_j(x_i)` of the
  projection onto the piecewise polynomials of level `k` and degree `< r` in one variable, with
  coefficients `c_j` not depending on `x_i`; these are exactly the combinations of products
  `∏_i u_i(x_i)` of piecewise polynomials `u_i` of level `k` and degree `< r` on `[0, 1]`
  (`Cube.isCubePP_iff_mem_span_prod_ppFun`), and on each dyadic cube of level `k` they are
  polynomials of degree `< r` in each variable separately. For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
  `r ≥ 1` and `0 ≤ s < 1/p`, `f ∈ A^s_q` of these spaces iff
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (`Cube.memApprox_cubePPScheme_iff`), with
  Jackson's inequality at every level (`Cube.exists_approxSeq_cubePPScheme_le`; level `0` is
  Whitney's inequality on the cube, `Cube.exists_approxSeq_cubePPScheme_one_le`) and the inverse
  inequality of order `1/p` (`Cube.exists_inverse_cubePPScheme`). The approximants are tensor
  products of the projections in one variable, applied to the slices one coordinate at a time.
* **Tensor splines on the cube.** Let `S_k^d ⊆ L_p(Q)` consist of the bounded measurable functions
  whose slices, in every coordinate and through every point, are dyadic splines of order `r` and
  level `k` on `[0, 1]`; these are exactly the combinations of products `∏_i u_i(x_i)` of such
  splines `u_i` (`Cube.isCubeSpline_iff_mem_span_prod_ppFun`). For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 ≤ s < r - 1 + 1/p`,
  `f ∈ A^s_q` of these spaces iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Cube.memApprox_cubeSplineScheme_iff`), with Jackson's inequality at every level through the
  tensor quasi-interpolant (`Cube.exists_approxSeq_cubeSplineScheme_le`) and the inverse
  inequality of order `r - 1 + 1/p` (`Cube.exists_inverse_cubeSplineScheme`).
* **The isotropic modulus on the cube.** Let
  `ω_r^iso(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r f‖_{L_p({x ∈ Q : x + rh ∈ Q})}` with
  `Δ_h^r f(x) = ∑_k (-1)^(r-k) C(r,k) f(x + kh)` for steps `h ∈ ℝ^d` of every direction. For
  `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `r ≥ 1`, `f ∈ A^s_q` of the piecewise polynomials iff
  `‖f‖_p + ‖(2^(ks) ω_r^iso(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` for `0 ≤ s < 1/p`
  (`Cube.memApprox_cubePPScheme_iff_iso`), and likewise for the tensor splines of order `r` and
  `0 ≤ s < r - 1 + 1/p` (`Cube.memApprox_cubeSplineScheme_iff_iso`). Hence the Besov conditions
  with the coordinate moduli and with the isotropic modulus agree for `0 ≤ s < r - 1 + 1/p`
  (`Cube.lqNorm_cubeModulus_lt_top_iff_iso`). The proof expands `Δ_h^r` into `d^r` mixed
  coordinate differences in the translation algebra `ℂ[ℝ^d]` (`Cube.isoDiff_eq_sum`) and bounds
  them by differences of every order in one variable
  (`Interval.exists_eLpNorm_iterDiff_ppFun_le`, `Interval.exists_eLpNorm_iterDiff_spline_le_of_lt`).
* **Block decompositions.** In a Banach space, for `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff
  `f = ∑_k g_k` with blocks `g_k ∈ A_{2^k}` and `(2^(ks) ‖g_k‖)_k ∈ ℓ_q`; the infimum over
  such decompositions is an equivalent quasi-norm
  (`ApproximationScheme.memApprox_iff_blockDecompNorm_lt_top`).
* **Atomic decompositions.** Let `A` be a linear scheme with atoms `a_{j,m}` at finitely many
  positions `m` of level `j`, such that `‖∑_m c_m a_m‖ ≤ C 2^(-jδ) ‖c‖_{ℓ_p}` and
  `E_{2^k}(∑_m c_m a_m) ≤ C 2^(-(k-j)σ) 2^(-jδ) ‖c‖_{ℓ_p}` for `k ≥ j`. For `0 < s < σ`,
  every `f = ∑_j ∑_m λ_{j,m} a_{j,m}` satisfies `‖f‖_{A^s_q} ≲ ‖λ‖_{b^s_{p,q}}`, where
  `‖λ‖_{b^s_{p,q}} = ‖(2^(j(s-δ)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}`
  (`ApproximationScheme.AtomicSystem.approxNormDyadic_le_bNorm`). If every approximant of
  `A_{2^j}` expands stably in atoms of level `j`, then conversely every `f ∈ A^s_q` has such a
  decomposition, and `A^s_q` is the space of atomic sums with coefficients in `b^s_{p,q}`
  (`ApproximationScheme.AtomicSystem.memApprox_iff_exists_atomic`).
* **Lipschitz atoms on the torus.** Call `a` a Lipschitz atom of level `j` at the grid point
  `2^(-j) m` of `𝕋^d` if `|a| ≤ 1`, `|a(x) - a(y)| ≤ 2^j ‖x - y‖` and `a = 0` outside the ball
  of radius `D 2^(-j)` around `2^(-j) m`. For `0 < s < 1` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{2,q}(𝕋^d)`
  iff `f = ∑_j ∑_m λ_{j,m} a_{j,m}` in `L_2(𝕋^d)` with Lipschitz atoms of support radius `1` and
  `‖(2^(j(s-d/2)) ‖λ_{j,·}‖_{ℓ_2})_j‖_{ℓ_q} < ∞` (`Torus.memBesov_iff_exists_lipAtoms`). Every
  such sum with atoms of any support radius `D` lies in `B^s_{2,q}(𝕋^d)`
  (`Torus.memBesov_of_lipAtoms`), and the atoms of a given `f` come from quasi-interpolants
  with hat functions (`Torus.exists_lipAtoms`).
* **The trace theorem.** Let `T` be linear with `T(A_n) ⊆ B_n` and `‖T a‖ ≤ C n^β ‖a‖` for
  `a ∈ A_n`, `n ≥ 1`, as for the restriction of functions to a hyperplane. Then `T` extends to
  `A^β_1`, and for `0 ≤ β < s` it maps `A^s_q` into `B^{s-β}_q` with
  `‖Tr f‖_{B^{s-β}_q} ≲ ‖f‖_{A^s_q}` (`ApproximationScheme.TraceBound.approxNormDyadic_ext_le`).
  If every `b ∈ B_{2^k}` is `T a` with `a ∈ A_{2^(k+γ)}` and `‖a‖ ≤ C' 2^(-kβ) ‖b‖`, then every
  `g ∈ B^s_q`, `s > 0`, is the trace of some `f ∈ A^{s+β}_q` with `‖f‖ ≲ ‖g‖`
  (`ApproximationScheme.TraceBound.exists_ext_eq`).
* **Intrinsic norms.** Let `R` be bounded linear with `R(A_n) ⊆ B_n`, as for the restriction
  to a domain, and let `E` be a possibly nonlinear map with `R(E g) = g`, `‖E g‖ ≤ C ‖g‖` and
  `E^A_{2^(k+γ)}(E g) ≤ C E^B_{2^k}(g)`. Then the intrinsic quasi-norm of `B^s_q` and the
  restriction quasi-norm `inf {‖f‖_{A^s_q} : R f = g}` are equivalent, and `B^s_q = R(A^s_q)`
  (`ApproximationScheme.approxNormDyadic_extension_le`,
  `ApproximationScheme.memApprox_iff_exists_restrict`).
* **Dyadic blocks.** If the scheme has projections `P_n` onto `A_n` with `‖P_n‖ ≤ M` and
  `⋃ A_n` is dense, then for `s > 0`, `f ∈ A^s_q` iff
  `‖P_1 f‖ + ‖(2^(ks) ‖P_{2^(k+1)} f - P_{2^k} f‖)_k‖_{ℓ_q} < ∞`
  (`ApproximationScheme.ProjectionScheme.memApprox_iff_blockNorm_lt_top`). For the Fourier
  basis on `𝕋^d` this is the Littlewood–Paley characterisation of `B^s_{2,q}(𝕋^d)`
  (`Torus.memBesov_two_iff_blockNorm_lt_top`), and for `q = 2` it gives
  `B^s_{2,2}(𝕋^d) = H^s(𝕋^d)` (`Torus.memBesov_two_two_iff`).
* **Martingale differences.** For a filtration `ℱ_0 ≤ ℱ_1 ≤ ⋯` on a finite measure space,
  let `A_n ⊆ L_p` be the `ℱ_⌊log₂ n⌋`-measurable functions (for the dyadic filtration of
  `[0, 1)`, the step functions of the Haar system). If these are dense in `L_p`, then for
  `s > 0`, `f ∈ A^s_q` iff
  `‖E[f | ℱ_0]‖_p + ‖(2^(ks) ‖E[f | ℱ_{k+1}] - E[f | ℱ_k]‖_p)_k‖_{ℓ_q} < ∞`
  (`MeasureTheory.Filtration.memApprox_iff_martingale`), using the conditional expectation
  as a contraction of `L_p` (`MeasureTheory.Lp.condExpLp`).
* **The Haar system.** Let `h_{k,m} = 2^(k/2) (1_{[2m, 2m+1) 2^(-k-1)} - 1_{[2m+1, 2m+2) 2^(-k-1)})`
  be the Haar functions on `[0, 1)` and `A_n` the step functions on the dyadic intervals of
  length `2^(-⌊log₂ n⌋)`. For `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p[0, 1))` iff
  `|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`
  (`Haar.memApprox_iff_haarCoeff`). The proof computes `E[f | ℱ_k]` as averages over dyadic
  intervals, from the formula for the conditional expectation onto a countable partition
  (`MeasureTheory.condExp_comap_ae_eq`), and uses
  `‖∑_m c_m h_{k,m}‖_p = 2^(k(1/2-1/p)) ‖c‖_{ℓ_p}` (`Haar.eLpNorm_sum_haar`). The Haar scheme is
  the scheme of piecewise constants, so for `0 < s < 1/p` the Haar condition is also equivalent
  to `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞` and to its periodic version
  (`Haar.lqNorm_modulus_lt_top_iff_haarCoeff`, `Haar.lqNorm_perModulus_lt_top_iff_haarCoeff`).
* **Sequence spaces.** For `1 ≤ q ≤ r ≤ ∞` and every sequence `a` in `[0, ∞]`,
  `‖a‖_{ℓ_r} ≤ ‖a‖_{ℓ_q}` (`ENNReal.lqNorm_le_lqNorm_of_le`), and the norm of a series of
  sequences is at most the series of the norms (`ENNReal.lqNorm_tsum_le`).
* **Hardy inequalities.** For `α > 0`, `1 ≤ q ≤ ∞` and every sequence `b` in `[0, ∞]`,
  `‖(2^(kα) ∑_{i ≥ 0} b_{k+i})_k‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖(2^(kα) b_k)_k‖_{ℓ_q}` and
  `‖(2^(-kα) ∑_{j ≤ k} b_j)_k‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖(2^(-kα) b_k)_k‖_{ℓ_q}`
  (`ENNReal.hardy_tail_le`, `ENNReal.hardy_sum_le`).
* **Besov embeddings.** Let `μ` be a finite measure on `Ω` and `S` a scheme of bounded
  continuous functions with the Nikolskii property of dimension `D ≥ 0`: for every
  `1 ≤ p ≤ ∞` there is `C` with `‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all `a ∈ S_n`, `n ≥ 1`. Let
  `1 ≤ p ≤ r ≤ ∞`, `1 ≤ q ≤ ∞` and `α = D (1/p - 1/r) < s`. Then every `f ∈ B^s_{p,q}`
  belongs to `L_r` and to `B^{s-α}_{r,q}`, with `‖f‖_{B^{s-α}_{r,q}} ≤ K ‖f‖_{B^s_{p,q}}`
  (`FunctionScheme.MemBesov.exists_inclusion_eq_of_nikolskii`,
  `FunctionScheme.exists_inclusion_eq_of_nikolskii`). If `μ` charges every nonempty open
  set and `s > D/p`, every `f ∈ B^s_{p,q}` has a bounded continuous representative
  (`FunctionScheme.MemBesov.exists_boundedContinuous`).
* **Sobolev embeddings.** Call a Banach space `V` with an injective bounded map into `L_p(μ)`
  a Sobolev space of order `s` for `S` if it satisfies Jackson's inequality
  `E_n(f)_p ≤ C n^(-s) ‖f‖_V` and Bernstein's inequality (every `a ∈ S_n` lies in `V` with
  `‖a‖_V ≤ C n^s ‖a‖_p`). For `S` with the Nikolskii property of dimension `D ≥ 0`, Sobolev
  spaces `V` of order `s` in `L_p` and `V'` of order `t` in `L_r`, `p ≤ r` and
  `t - D/r < s - D/p`, every element of `V` lies in `V'`
  (`FunctionScheme.SobolevSpace.exists_eq_inclusion'`); for `s > D/p` every element of `V`
  has a bounded continuous representative
  (`FunctionScheme.SobolevSpace.exists_boundedContinuous`). The limiting cases are not
  covered.
* **The torus.** For a trigonometric polynomial `T` of degree `< n` on `𝕋^d`, `n ≥ 1`, and
  `1 ≤ p < ∞`, `‖T‖_∞ ≤ (2⌈p/2⌉)^(d/p) n^(d/p) ‖T‖_p`
  (`Torus.norm_le_rpow_mul_eLpNorm`). Hence the trigonometric polynomials have the
  Nikolskii property of dimension `d` (`Torus.trigScheme_hasNikolskii`), and all the Besov
  embeddings above hold on `𝕋^d` with `α = d (1/p - 1/r)`
  (`Torus.memBesov_exists_inclusion_eq`, `Torus.memBesov_exists_continuous`).
* **The Sobolev embedding on the torus.** Let `s > d/2` and `f ∈ L_2(𝕋^d)` with
  `∑_{k ∈ ℤ^d} (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞`. Then `f` has a continuous representative
  (`Torus.sobolev_exists_continuous`). The space `H^s(𝕋^d)` of these functions satisfies
  Jackson's and Bernstein's inequalities with constant `1` (`Torus.sobolevSpace`), so
  `H^s(𝕋^d) ⊆ B^s_{2,∞}(𝕋^d)`, `B^t_{2,q}(𝕋^d) ⊆ H^s(𝕋^d)` for `t > s`, and
  `H^s(𝕋^d) ⊆ L_r(𝕋^d)` for `2 ≤ r ≤ ∞` and `s > d(1/2 - 1/r)`
  (`Torus.sobolev_memBesov_top`, `Torus.exists_sobolev_of_memBesov`,
  `Torus.sobolev_exists_inclusion_eq`).
* **Two schemes.** Linear approximation from the first `n` elements of a sequence
  (`ApproximationScheme.ofSpan`) and `n`-term approximation from a dictionary
  (`ApproximationScheme.nTerm`) are approximation schemes, and the first has larger errors
  than the second (`ApproximationScheme.approxError_nTerm_le_ofSpan`).

## What is formalised

| Result | Lean | Human-checked | File |
|---|---|---|---|
| Approximation schemes, preimage and image | ✅ proved | ✗ | `ApproximationSpaces/Scheme.lean` |
| Error of best approximation and its calculus | ✅ proved | ✗ | `ApproximationSpaces/Error.lean` |
| Linear approximation from a sequence | ✅ proved | ✗ | `ApproximationSpaces/Instances/Span.lean` |
| `n`-term approximation from a dictionary | ✅ proved | ✗ | `ApproximationSpaces/Instances/NTerm.lean` |
| `ℓ_q` norms of sequences in `ℝ≥0∞`, Minkowski, monotonicity in `q` | ✅ proved | ✗ | `ApproximationSpaces/Sequences/Lq.lean` |
| Cauchy condensation with power weights | ✅ proved | ✗ | `ApproximationSpaces/Sequences/Dyadic.lean` |
| Countable Minkowski inequality, discrete Hardy inequalities | ✅ proved | ✗ | `ApproximationSpaces/Sequences/Hardy.lean` |
| `A^s_q`, its dyadic quasi-norm and linear structure | ✅ proved | ✗ | `ApproximationSpaces/{Norm,Dyadic,Space}.lean` |
| Embeddings `A^s_q ↪ A^t_r` and functoriality | ✅ proved | ✗ | `ApproximationSpaces/{Embedding,Transfer}.lean` |
| Telescoping lift, Bernstein gives `A^β_1 ↪ Y`, Nikolskii transfer theorem | ✅ proved | ✗ | `ApproximationSpaces/{Lift,Nikolskii}.lean` |
| K-functional, real interpolation, representation theorem | ✅ proved | ✗ | `ApproximationSpaces/{KFunctional,Representation}.lean` |
| Moduli compatible with a scheme, coincidence with the classical space | ✅ proved | ✗ | `ApproximationSpaces/Moduli.lean` |
| One variable: differences, moduli on intervals, Nikolskii for polynomials, Taylor in `L_p`, Steklov smoothing | ✅ proved | ✗ | `FunctionSpaces/Interval/{Differences,Modulus,Polynomials,Taylor,Steklov,Smoothing}.lean` |
| Whitney's inequality on `[0, 1]` | ✅ proved | ✗ | `FunctionSpaces/Interval/Whitney.lean` |
| Dyadic piecewise polynomials on `[0, 1]`: Jackson and inverse inequalities, `A^s_q = B^s_{p,q}[0, 1]` for `0 < s < 1/p` | ✅ proved | ✗ | `FunctionSpaces/Interval/{PiecewisePoly,PiecewiseJackson,PiecewiseInverse}.lean` |
| Periodic modulus, piecewise polynomials on the circle, `A^s_q = B^s_{p,q}(𝕋) = B^s_{p,q}[0, 1]` for `0 < s < 1/p` | ✅ proved | ✗ | `FunctionSpaces/Interval/{Periodic,PiecewisePeriodic}.lean` |
| Dual basis for `∫_0^1 P Q`, local projections, bounded projections onto piecewise polynomials | ✅ proved | ✗ | `FunctionSpaces/Interval/LocalProjection.lean` |
| Cardinal B-splines, B-spline basis on a unit interval, Marsden's identity, vanishing coefficients of shifted powers | ✅ proved | ✗ | `FunctionSpaces/Interval/BSpline.lean` |
| Dyadic splines (jump form = `C^(r-2)`), spline scheme, dyadic B-splines, B-spline coefficients of the pieces | ✅ proved | ✗ | `FunctionSpaces/Interval/Splines.lean` |
| Inverse inequality of order `r - 1 + 1/p` for splines | ✅ proved | ✗ | `FunctionSpaces/Interval/SplineInverse.lean` |
| Spline quasi-interpolant: local reproduction of polynomials, reproduction of splines, B-splines span the splines, local bounds | ✅ proved | ✗ | `FunctionSpaces/Interval/QuasiInterp.lean` |
| Jackson's inequality for splines, `A^s_q(splines) = B^s_{p,q}[0, 1]` for `0 < s < r - 1 + 1/p` | ✅ proved | ✗ | `FunctionSpaces/Interval/SplineJackson.lean` |
| Periodic splines, their inverse inequality | ✅ proved | ✗ | `FunctionSpaces/Interval/SplinePeriodic.lean` |
| Periodic quasi-interpolant, Jackson's inequality for periodic splines, `A^s_q(periodic splines) = B^s_{p,q}(𝕋)` for `0 < s < r - 1 + 1/p` | ✅ proved | ✗ | `FunctionSpaces/Interval/SplinePeriodicJackson.lean` |
| Density of piecewise polynomials, multiscale characterisation of `A^s_q` and of `B^s_{p,q}` for `0 < s < 1/p` | ✅ proved | ✗ | `FunctionSpaces/Wavelets/Examples/Multiscale.lean` |
| Multiwavelets (orthonormal, `r` vanishing moments), stability, coefficient characterisation of `A^s_q` and of `B^s_{p,q}` for `0 < s < 1/p` | ✅ proved | ✗ | `FunctionSpaces/Wavelets/Examples/Alpert.lean` |
| The cube `[0, 1]^d`: slices, integration through slices, moduli in the coordinates | ✅ proved | ✗ | `FunctionSpaces/Cube/{Basic,Modulus}.lean` |
| Steklov smoothing in one coordinate near both ends of the cube | ✅ proved | ✗ | `FunctionSpaces/Cube/Smoothing.lean` |
| Kernel operators of finite rank on slices, their forms, tensor products, telescoping over the coordinates | ✅ proved | ✗ | `FunctionSpaces/Cube/SlicewiseOperators.lean` |
| Piecewise polynomials on the cube: tensor projection, tensor-product description, Whitney, Jackson and inverse inequalities, `A^s_q = B^s_{p,q}([0, 1]^d)` for `0 < s < 1/p` | ✅ proved | ✗ | `FunctionSpaces/Cube/{PiecewisePoly,PiecewiseJackson,PiecewiseInverse}.lean` |
| Tensor splines on the cube: quasi-interpolant as a kernel operator, tensor-product description, Jackson and inverse inequalities, `A^s_q = B^s_{p,q}([0, 1]^d)` for `0 < s < r - 1 + 1/p` | ✅ proved | ✗ | `FunctionSpaces/Cube/{Splines,SplineJackson,SplineInverse}.lean` |
| Differences of every order: difference bound for polynomials, piecewise polynomials (gain `1/p`), splines (gain `m` below order `r`), steps of either sign | ✅ proved | ✗ | `FunctionSpaces/Interval/{PolyDifferences,LowerDifferences}.lean` |
| Isotropic differences: translation algebra, expansion into mixed coordinate differences | ✅ proved | ✗ | `FunctionSpaces/Cube/Translation.lean` |
| Isotropic modulus on the cube, comparison with the moduli in the coordinates | ✅ proved | ✗ | `FunctionSpaces/Cube/IsoModulus.lean` |
| Isotropic inverse inequalities, `A^s_q` with the isotropic modulus, coordinate and isotropic Besov conditions agree for `0 < s < r - 1 + 1/p` | ✅ proved | ✗ | `FunctionSpaces/Cube/{IsoInverse,IsoCoincidence}.lean` |
| Block decompositions, projection schemes and dyadic blocks | ✅ proved | ✗ | `ApproximationSpaces/Decompositions/{Blocks,Projection}.lean` |
| Synthesis with decay, atomic systems, `b^s_{p,q}`, atomic characterisation | ✅ proved | ✗ | `ApproximationSpaces/Decompositions/{Synthesis,Atomic}.lean` |
| Trace theorem: extension, transfer, surjectivity | ✅ proved | ✗ | `ApproximationSpaces/Trace.lean` |
| Intrinsic and restriction quasi-norms (retract theorem) | ✅ proved | ✗ | `ApproximationSpaces/Retract.lean` |
| Coefficient characterisations, `H^s = B^s_{2,2}` (spectral schemes, torus) | ✅ proved | ✗ | `FunctionSpaces/Spectral/Blocks.lean`, `FunctionSpaces/Torus/Coefficients.lean` |
| Inclusion `L_r ↪ L_p`, schemes of functions, Besov spaces, elementary embeddings | ✅ proved | ✗ | `FunctionSpaces/{Lp/Inclusion,Lp/BoundedContinuous,Scheme,Besov/Basic,Besov/Trivial}.lean` |
| Interpolation `L_p`–`L_∞`, Nikolskii property, Besov embeddings | ✅ proved | ✗ | `FunctionSpaces/{Lp/Interpolation,Besov/Nikolskii,Besov/Embeddings}.lean` |
| Jackson inequality, smoothness spaces, Sobolev embeddings | ✅ proved | ✗ | `ApproximationSpaces/Jackson.lean`, `FunctionSpaces/Sobolev/Embeddings.lean` |
| Spectral schemes and `L_2` Sobolev spaces, Jackson and Bernstein | ✅ proved | ✗ | `FunctionSpaces/Spectral/Basic.lean` |
| The torus: trigonometric polynomials, Nikolskii inequality | ✅ proved | ✗ | `FunctionSpaces/Torus/{Measure,Scheme,Nikolskii}.lean` |
| The torus: `H^s(𝕋^d)`, Besov and Sobolev embeddings, `H^s(𝕋^d) ↪ C(𝕋^d)` | ✅ proved | ✗ | `FunctionSpaces/Torus/{Sobolev,Embeddings}.lean` |
| Filtration schemes (Haar), martingale-difference characterisation | ✅ proved | ✗ | `FunctionSpaces/Wavelets/Filtration.lean` |
| Haar system on `[0, 1)`: dyadic conditional expectations, density, Haar coefficient characterisation | ✅ proved | ✗ | `FunctionSpaces/Wavelets/{Partition,Examples/Haar}.lean` |
| Haar coefficients and Besov spaces on the interval and the circle for `0 < s < 1/p` | ✅ proved | ✗ | `FunctionSpaces/Wavelets/Examples/HaarBesov.lean` |
| Moduli of smoothness in `L_2(𝕋^d)`, Jackson's theorem, coincidence for `0 < s < 1` | ✅ proved | ✗ | `FunctionSpaces/Classical/{Translation,Modulus,BesovModuli}.lean` |
| Traces on the torus: trace inequality, Fejér extension, `B^{s+1/p}_{p,q}(𝕋^(n+1)) → B^s_{p,q}(𝕋^n)` onto | ✅ proved | ✗ | `FunctionSpaces/Traces/Examples/Torus.lean` |
| Lipschitz atoms on the torus: synthesis, quasi-interpolants with hat functions, characterisation of `B^s_{2,q}(𝕋^d)` | ✅ proved | ✗ | `FunctionSpaces/Atoms/Examples/{Torus,TorusHat,TorusAnalysis}.lean` |
| Weak derivatives on the torus, `W^m_2(𝕋^d) = H^m(𝕋^d) = B^m_{2,2}(𝕋^d)` | ✅ proved | ✗ | `FunctionSpaces/Classical/SobolevDeriv.lean` |
| Classical definitions for `p ≠ 2`, higher differences | ⬜ planned | ✗ | `FunctionSpaces/Classical/…` |

Lean: ✅ proved (no `sorry`) · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author ·
🧮 mathematics reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a
file resets its rows to ✗.

## Organisation

Two libraries. `ApproximationSpaces` holds the abstract theory: approximation schemes in a
real normed space, the approximation spaces and their embeddings, lifting and the Nikolskii
transfer theorem, the K-functional and the representation theorem, block and atomic
decompositions, projection schemes, traces and intrinsic norms, and the coincidence of
approximation spaces with spaces defined by moduli of smoothness. Nothing in it mentions
functions or measures. `FunctionSpaces` holds the Besov and Sobolev spaces built on it:
schemes of bounded continuous functions on a finite measure space and their embedding
theorems, spectral schemes in Hilbert spaces, the torus with its traces and Lipschitz atoms,
filtration schemes for wavelets and multiwavelets, the classical definitions through moduli of smoothness
and weak derivatives, and polynomial and piecewise polynomial approximation on intervals and
on the cube `[0, 1]^d`. [MathlibCandidates.md](MathlibCandidates.md) lists what could be
upstreamed.
`blueprint/` holds the LaTeX source of the blueprint and the scripts that check and link its
`\lean` references.

## What is left to do

* **Reiteration** for approximation and interpolation spaces.
* **Function spaces beyond the torus**: `ℝ^d`, compact manifolds, bounded domains.
* **Classical definitions for all `p`**: Sobolev spaces by weak derivatives and Besov spaces
  by moduli of smoothness in `L_p`, with the coincidence theorems of Triebel's school.
* **Higher smoothness**: splines on domains, and compactly supported wavelets such as
  Daubechies'.

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

GitHub Actions builds the project and the blueprint on every push to `main`, and deploys
the blueprint to GitHub Pages. Neither output is committed.

## AI assistance

The formalisation was written with Claude Code. Every statement and proof was checked
by Lean; the mathematical design, the choice of statements and the review of what the
proofs actually say are the author's. The column "Human-checked" above records that review.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

* J. Bergh, J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren der
  mathematischen Wissenschaften **223**, Springer-Verlag, 1976. Real interpolation and the
  K-functional.
* R. A. DeVore, G. G. Lorentz, *Constructive Approximation*, Grundlehren der
  mathematischen Wissenschaften **303**, Springer-Verlag, 1993. Chapter 7: approximation
  spaces, Jackson and Bernstein inequalities, and their relation to interpolation.
* S. M. Nikol'skii, *Approximation of Functions of Several Variables and Imbedding
  Theorems*, Grundlehren der mathematischen Wissenschaften **205**, Springer-Verlag, 1975.
  The Nikolskii inequality and the embedding theorems it yields.
* A. Pietsch, *Approximation spaces*, J. Approx. Theory **32** (1981), no. 2, 115–134.
  The definition of approximation schemes and spaces followed here.
* V. Temlyakov, *Multivariate Approximation*, Cambridge University Press, 2018. Periodic
  function spaces and trigonometric approximation.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983. Besov and Sobolev spaces and
  the equivalence of their definitions.
