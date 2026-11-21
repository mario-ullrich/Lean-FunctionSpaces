# Intervals, the cube, splines and wavelets

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Besov spaces*,
chapters *Filtrations and martingale differences*, *Polynomial approximation on intervals* and
*Approximation on the cube*.

On `[0, 1]`, the circle and the cube `[0, 1]^d`, the schemes are dyadic piecewise polynomials
and splines, and the approximation spaces are the Besov spaces defined by moduli of smoothness:
for `0 < s < 1/p` with piecewise polynomials and for `0 < s < r - 1 + 1/p` with splines of order
`r`. The tools are differences and moduli on intervals, Whitney's inequality, Steklov smoothing,
B-splines with Marsden's identity and quasi-interpolants; on the cube, operators act on slices
one coordinate at a time, and the translation algebra `ℂ[ℝ^d]` of
[Tools from analysis](Analysis.md) relates the isotropic modulus to
the moduli in the coordinates. The martingale differences of [Besov and Sobolev spaces on measure
spaces](MeasureSpaces.md) give the Haar characterisation, and multiwavelets refine it to higher
degree. In breadth-first order the Haar functions form a Hilbert basis of `L_2[0, 1]`, and for
`0 < τ < 2` and `θ = 1/τ - 1/2` best `n`-term approximation from it in `L_2` gives the same
approximation space `A^θ_τ` as approximation by dyadic step functions in `L_τ`, for `τ < 1` in
the quasi-Banach space `L_τ`.

## Main results

* **Whitney's inequality.** For `1 ≤ p < ∞`, `r ≥ 1` and `0 < t ≤ 1/3` there is `W` such that
  every continuous `F` has a polynomial `P` of degree `< r` with
  `‖F - P‖_{L_p[0, 1]} ≤ W ω_r(F, t, [0, 1])_p` (`Interval.exists_eLpNorm_sub_polyFun_le_modulus`),
  with the modulus `ω_r` of the next item. In `L_p[0, 1]` the error of best approximation by the
  polynomials of degree `< r` satisfies `E_1(f)_p ≤ W ω_r(f, 2^(-m), [0, 1])_p` for `m ≥ 2`
  (`Interval.exists_approxError_ppScheme_one_le`).
* **Piecewise polynomials on an interval.** Let `V_k ⊆ L_p[0, 1]` consist of the functions that
  agree on each dyadic interval `[n 2^(-k), (n+1) 2^(-k))` with a polynomial of degree `< r`,
  and let `ω_r(f, t, [0, 1])_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r f‖_{L_p[0, 1-rh]}`. For `1 ≤ p < ∞`
  and `r ≥ 1`, `E_{2^k}(f)_p ≤ 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k), [0, 1])_p` for `k ≥ 1`
  (`Interval.approxError_ppScheme_le`), with Whitney's inequality a bound
  `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k), [0, 1])_p` for all `k ≥ 0`
  (`Interval.exists_approxError_ppScheme_le`), and there is `C` with
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
  (`Interval.exists_approxError_splineScheme_le`) and with
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
  (`Interval.exists_approxError_perSplineScheme_le`) and the inverse inequality of order
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
  Jackson's inequality at every level (`Cube.exists_approxError_cubePPScheme_le`; level `0` is
  Whitney's inequality on the cube, `Cube.exists_approxError_cubePPScheme_one_le`) and the inverse
  inequality of order `1/p` (`Cube.exists_inverse_cubePPScheme`). The approximants are tensor
  products of the projections in one variable, applied to the slices one coordinate at a time.
* **Tensor splines on the cube.** Let `S_k^d ⊆ L_p(Q)` consist of the bounded measurable functions
  whose slices, in every coordinate and through every point, are dyadic splines of order `r` and
  level `k` on `[0, 1]`; these are exactly the combinations of products `∏_i u_i(x_i)` of such
  splines `u_i` (`Cube.isCubeSpline_iff_mem_span_prod_ppFun`). For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
  `r ≥ 1` and `0 ≤ s < r - 1 + 1/p`, `f ∈ A^s_q` of these spaces iff
  `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
  (`Cube.memApprox_cubeSplineScheme_iff`), with Jackson's inequality at every level through the
  tensor quasi-interpolant (`Cube.exists_approxError_cubeSplineScheme_le`) and the inverse
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
  coordinate differences in the translation algebra `ℂ[ℝ^d]` (`Cube.higherDiff_eq_sum`) and bounds
  them by differences of every order in one variable
  (`Interval.exists_eLpNorm_higherDiff_ppFun_le`,
  `Interval.exists_eLpNorm_higherDiff_spline_le_of_lt`).
* **The Haar system.** Let `h_{k,m} = 2^(k/2) (1_{[2m, 2m+1) 2^(-k-1)} - 1_{[2m+1, 2m+2) 2^(-k-1)})`
  be the Haar functions on `[0, 1)` and `A_n` the step functions on the dyadic intervals of
  length `2^(-⌊log₂ n⌋)`. For `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p[0, 1])` iff
  `|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`
  (`Haar.memApprox_iff_haarCoeff`). The proof computes `E[f | ℱ_k]` as averages over dyadic
  intervals, from the formula for the conditional expectation onto a countable partition
  (`MeasureTheory.condExp_comap_ae_eq`), and uses
  `‖∑_m c_m h_{k,m}‖_p = 2^(k(1/2-1/p)) ‖c‖_{ℓ_p}` (`Haar.eLpNorm_sum_haar`). The Haar scheme is
  the scheme of piecewise constants, so for `0 < s < 1/p` the Haar condition is also equivalent
  to `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞` and to its periodic version
  (`Haar.lqNorm_modulus_lt_top_iff_haarCoeff`, `Haar.lqNorm_perModulus_lt_top_iff_haarCoeff`).
  For `0 < p ≤ 1`, `0 < q ≤ ∞` and `0 < s < 1/p`, `f` lies in the approximation space of the
  step functions in the quasi-Banach space `L_p[0, 1]` (the spaces `E_{s,q}` of the couple
  `Haar.stepCouple`) iff `‖f‖_p + ‖(2^(ks) ω_1(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q} < ∞`
  (`Haar.memEMethod_stepCouple_iff_modulus`), by Jackson's inequality by averaging and an inverse
  inequality of order `1/p` (`Haar.eFunctional_stepCouple_le`, `Haar.lpModulus_le_of_mem_lpMeas`);
  for `s > 1`, and for `s = 1` with `q < ∞`, this space misses the line `x ↦ x`, whose second
  modulus vanishes (`Haar.not_memEMethod_stepCouple_idLp`). For `1 ≤ p` the step couple is the
  complexity couple of the Haar scheme (`Haar.memEMethod_stepCouple_iff_memApprox`). For
  `0 < p ≤ 1`, `s > 1/p - 1` and `0 < q ≤ ∞` the space `E_{s,q}` embeds into `L_1[0, 1]`
  (`Haar.eLpNorm_one_le_eNormDyadic`), and `f ∈ E_{s,q}` iff `f ∈ L_1[0, 1]` and
  `|∫_0^1 f| + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, h_{k,m}⟩)_{m<2^k}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`
  (`Haar.memEMethod_stepCouple_iff_haarCoeff`); for `1/p - 1 < s < 1/p` this describes
  `B^s_{p,q,1}[0, 1]` by Haar coefficients (`Haar.lqNorm_modulus_lt_top_iff_haarCoeff_of_le_one`).
  For `q < ∞` the Haar system is a Schauder basis of `E_{s,q}`: the partial sums converge
  (`Haar.tendsto_eNormDyadic_sub_haarPartialSum`) and the coefficients are unique
  (`Haar.eq_haarSystemCoeff_of_tendsto`). The proofs use martingale convergence in `L_1`
  (`Haar.tendsto_eLpNorm_condExp_sub`) and Fatou's lemma for telescoping sums in `L_r`,
  `0 < r ≤ 1` (`MeasureTheory.eLpNorm_sub_rpow_le_tsum`).
* **The Haar basis and `n`-term approximation.** The functions `φ_0 = 1` and
  `φ_{2^k+i} = h_{k,i}`, `k ∈ ℕ`, `0 ≤ i < 2^k`, form a Hilbert basis of `L_2[0, 1]`
  (`Haar.haarBasis`, with the coefficients `Haar.haarBasis_repr_zero`,
  `Haar.haarBasis_repr_two_pow_add`). For `0 < τ < 2` and `θ = 1/τ - 1/2`, `f ∈ L_2[0, 1]` lies in
  the approximation space `A^θ_τ` of `n`-term approximation from the multiples `c φ_n` iff
  `|∫_0^1 f|^τ + ∑_k ∑_{i<2^k} |⟨f, h_{k,i}⟩|^τ < ∞` (`Haar.memApprox_nTerm_iff_haarCoeff`). For
  `1 ≤ τ < 2` this is the space `A^θ_τ(L_τ[0, 1])` of the Haar scheme
  (`Haar.memApprox_nTerm_iff_memApprox_scheme`), so it is the Besov condition
  `‖f‖_τ + ‖(2^(kθ) ω_1(f, 2^(-k), [0, 1])_τ)_k‖_{ℓ_τ} < ∞` and its periodic version
  (`Haar.memApprox_nTerm_iff_modulus`, `Haar.memApprox_nTerm_iff_perModulus`): the Haar case of
  the theorem of DeVore, Jawerth and Popov. For `0 < τ ≤ 1` the space `A^θ_τ` is, as a set, the
  approximation space `E_{θ,τ}` of dyadic steps in `L_τ` (`Haar.memApprox_nTerm_iff_memEMethod`,
  `Haar.exists_inclusion_eq_of_memEMethod`), and for every `0 < τ < 2`, `f ∈ A^θ_τ` iff
  `‖f‖_τ + ‖(2^(kθ) ω_1(f, 2^(-k), [0, 1])_τ)_k‖_{ℓ_τ} < ∞`
  (`Haar.memApprox_nTerm_iff_modulus_of_lt_two`), the classical `B^θ_{τ,τ}[0, 1]` for
  `2/3 < τ < 2`.

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| One variable: differences, moduli on intervals, Nikolskii for polynomials, Taylor in `L_p`, Steklov smoothing | ✅ | ✗ | `Domains/Interval/Differences`, `Domains/Interval/Modulus`, `Domains/Interval/Polynomials`, `Domains/Interval/Taylor`, `Domains/Interval/Steklov`, `Domains/Interval/Smoothing` |
| Whitney's inequality on `[0, 1]` | ✅ | ✗ | `Domains/Interval/Whitney` |
| Dyadic piecewise polynomials on `[0, 1]`: Jackson and inverse inequalities, `A^s_q = B^s_{p,q}[0, 1]` for `0 < s < 1/p` | ✅ | ✗ | `Domains/Interval/PiecewisePoly`, `Domains/Interval/PiecewiseJackson`, `Domains/Interval/PiecewiseInverse` |
| Periodic modulus, piecewise polynomials on the circle, `A^s_q = B^s_{p,q}(𝕋) = B^s_{p,q}[0, 1]` for `0 < s < 1/p` | ✅ | ✗ | `Domains/Interval/Periodic`, `Domains/Interval/PiecewisePeriodic` |
| Dual basis for `∫_0^1 P Q`, local projections, bounded projections onto piecewise polynomials | ✅ | ✗ | `Domains/Interval/LocalProjection` |
| Cardinal B-splines, B-spline basis on a unit interval, Marsden's identity, vanishing coefficients of shifted powers | ✅ | ✗ | `Domains/Interval/BSpline` |
| Dyadic splines (jump form = `C^(r-2)`), spline scheme, dyadic B-splines, B-spline coefficients of the pieces | ✅ | ✗ | `Domains/Interval/Splines` |
| Inverse inequality of order `r - 1 + 1/p` for splines | ✅ | ✗ | `Domains/Interval/SplineInverse` |
| Spline quasi-interpolant: local reproduction of polynomials, reproduction of splines, B-splines span the splines, local bounds | ✅ | ✗ | `Domains/Interval/QuasiInterp` |
| Jackson's inequality for splines, `A^s_q(splines) = B^s_{p,q}[0, 1]` for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Domains/Interval/SplineJackson` |
| Periodic splines, their inverse inequality | ✅ | ✗ | `Domains/Interval/SplinePeriodic` |
| Periodic quasi-interpolant, Jackson's inequality for periodic splines, `A^s_q(periodic splines) = B^s_{p,q}(𝕋)` for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Domains/Interval/SplinePeriodicJackson` |
| Density of piecewise polynomials, multiscale characterisation of `A^s_q` and of `B^s_{p,q}` for `0 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/Multiscale` |
| Multiwavelets (orthonormal, `r` vanishing moments), stability, coefficient characterisation of `A^s_q` and of `B^s_{p,q}` for `0 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/Alpert` |
| The cube `[0, 1]^d`: slices, integration through slices, moduli in the coordinates | ✅ | ✗ | `Domains/Cube/Basic`, `Domains/Cube/Modulus` |
| Steklov smoothing in one coordinate near both ends of the cube | ✅ | ✗ | `Domains/Cube/Smoothing` |
| Kernel operators of finite rank on slices, their forms, tensor products, telescoping over the coordinates | ✅ | ✗ | `Domains/Cube/SlicewiseOperators` |
| Piecewise polynomials on the cube: tensor projection, tensor-product description, Whitney, Jackson and inverse inequalities, `A^s_q = B^s_{p,q}([0, 1]^d)` for `0 < s < 1/p` | ✅ | ✗ | `Domains/Cube/PiecewisePoly`, `Domains/Cube/PiecewiseJackson`, `Domains/Cube/PiecewiseInverse` |
| Tensor splines on the cube: quasi-interpolant as a kernel operator, tensor-product description, Jackson and inverse inequalities, `A^s_q = B^s_{p,q}([0, 1]^d)` for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Domains/Cube/Splines`, `Domains/Cube/SplineJackson`, `Domains/Cube/SplineInverse` |
| Differences of every order: difference bound for polynomials, piecewise polynomials (gain `1/p`), splines (gain `m` below order `r`), steps of either sign | ✅ | ✗ | `Domains/Interval/PolyDifferences`, `Domains/Interval/LowerDifferences` |
| Isotropic differences and their expansion into mixed coordinate differences | ✅ | ✗ | `Domains/Cube/IsoDifferences` |
| Isotropic modulus on the cube, comparison with the moduli in the coordinates | ✅ | ✗ | `Domains/Cube/IsoModulus` |
| Isotropic inverse inequalities, `A^s_q` with the isotropic modulus, coordinate and isotropic Besov conditions agree for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Domains/Cube/IsoInverse`, `Domains/Cube/IsoCoincidence` |
| The normalising factor `2^(j/2)` of dyadic dilations: its square and its extended norm, also for its `d`-th power | ✅ | ✗ | `Wavelets/DyadicNormalisation` |
| Haar system on `[0, 1]`: dyadic conditional expectations, density, Haar coefficient characterisation | ✅ | ✗ | `Wavelets/Examples/Haar` |
| Haar coefficients and Besov spaces on the interval and the circle for `0 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/HaarBesov` |
| The Haar basis of `L_2[0, 1]`, `n`-term approximation | ✅ | ✗ | `Wavelets/Examples/HaarBasis` |
| Dyadic step functions in `L_p[0, 1]`, `0 < p ≤ 1`: the step couple, Jackson's inequality by averaging, inverse inequality of order `1/p`, `A^s_q = B^s_{p,q,1}[0, 1]` for `0 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/DyadicStepsQuasiBanach` |
| The Haar system for `0 < p ≤ 1`: steps in `L_1`, level norms, embedding of `A^s_q(L_p, steps)` into `L_1` for `s > 1/p - 1`, martingale convergence in `L_1`, Haar coefficient characterisation, `B^s_{p,q,1}[0, 1]` by Haar coefficients for `1/p - 1 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/HaarQuasiBanach` |
| Haar partial sums for `0 < p ≤ 1`: convergence in `A^s_q(L_p, steps)` for `s > 1/p - 1` and `q < ∞`, uniqueness of the coefficients (Schauder basis) | ✅ | ✗ | `Wavelets/Examples/HaarSchauderBasis` |
| `n`-term Haar approximation in `L_2` for every `0 < τ < 2`: approximation by steps in `L_τ`, `τ ≤ 1`, and the Besov space of the first modulus | ✅ | ✗ | `Wavelets/Examples/HaarNTermBesov` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
