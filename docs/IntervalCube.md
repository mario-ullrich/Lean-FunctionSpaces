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
the moduli in the coordinates. Martingale differences of a filtration on a finite measure space
are the general theorem behind the Haar characterisation, and multiwavelets refine it to higher
degree.

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

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| One variable: differences, moduli on intervals, Nikolskii for polynomials, Taylor in `L_p`, Steklov smoothing | ✅ | ✗ | `Interval/Differences`, `Interval/Modulus`, `Interval/Polynomials`, `Interval/Taylor`, `Interval/Steklov`, `Interval/Smoothing` |
| Whitney's inequality on `[0, 1]` | ✅ | ✗ | `Interval/Whitney` |
| Dyadic piecewise polynomials on `[0, 1]`: Jackson and inverse inequalities, `A^s_q = B^s_{p,q}[0, 1]` for `0 < s < 1/p` | ✅ | ✗ | `Interval/PiecewisePoly`, `Interval/PiecewiseJackson`, `Interval/PiecewiseInverse` |
| Periodic modulus, piecewise polynomials on the circle, `A^s_q = B^s_{p,q}(𝕋) = B^s_{p,q}[0, 1]` for `0 < s < 1/p` | ✅ | ✗ | `Interval/Periodic`, `Interval/PiecewisePeriodic` |
| Dual basis for `∫_0^1 P Q`, local projections, bounded projections onto piecewise polynomials | ✅ | ✗ | `Interval/LocalProjection` |
| Cardinal B-splines, B-spline basis on a unit interval, Marsden's identity, vanishing coefficients of shifted powers | ✅ | ✗ | `Interval/BSpline` |
| Dyadic splines (jump form = `C^(r-2)`), spline scheme, dyadic B-splines, B-spline coefficients of the pieces | ✅ | ✗ | `Interval/Splines` |
| Inverse inequality of order `r - 1 + 1/p` for splines | ✅ | ✗ | `Interval/SplineInverse` |
| Spline quasi-interpolant: local reproduction of polynomials, reproduction of splines, B-splines span the splines, local bounds | ✅ | ✗ | `Interval/QuasiInterp` |
| Jackson's inequality for splines, `A^s_q(splines) = B^s_{p,q}[0, 1]` for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Interval/SplineJackson` |
| Periodic splines, their inverse inequality | ✅ | ✗ | `Interval/SplinePeriodic` |
| Periodic quasi-interpolant, Jackson's inequality for periodic splines, `A^s_q(periodic splines) = B^s_{p,q}(𝕋)` for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Interval/SplinePeriodicJackson` |
| Density of piecewise polynomials, multiscale characterisation of `A^s_q` and of `B^s_{p,q}` for `0 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/Multiscale` |
| Multiwavelets (orthonormal, `r` vanishing moments), stability, coefficient characterisation of `A^s_q` and of `B^s_{p,q}` for `0 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/Alpert` |
| The cube `[0, 1]^d`: slices, integration through slices, moduli in the coordinates | ✅ | ✗ | `Cube/Basic`, `Cube/Modulus` |
| Steklov smoothing in one coordinate near both ends of the cube | ✅ | ✗ | `Cube/Smoothing` |
| Kernel operators of finite rank on slices, their forms, tensor products, telescoping over the coordinates | ✅ | ✗ | `Cube/SlicewiseOperators` |
| Piecewise polynomials on the cube: tensor projection, tensor-product description, Whitney, Jackson and inverse inequalities, `A^s_q = B^s_{p,q}([0, 1]^d)` for `0 < s < 1/p` | ✅ | ✗ | `Cube/PiecewisePoly`, `Cube/PiecewiseJackson`, `Cube/PiecewiseInverse` |
| Tensor splines on the cube: quasi-interpolant as a kernel operator, tensor-product description, Jackson and inverse inequalities, `A^s_q = B^s_{p,q}([0, 1]^d)` for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Cube/Splines`, `Cube/SplineJackson`, `Cube/SplineInverse` |
| Differences of every order: difference bound for polynomials, piecewise polynomials (gain `1/p`), splines (gain `m` below order `r`), steps of either sign | ✅ | ✗ | `Interval/PolyDifferences`, `Interval/LowerDifferences` |
| Isotropic differences and their expansion into mixed coordinate differences | ✅ | ✗ | `Cube/Translation` |
| Isotropic modulus on the cube, comparison with the moduli in the coordinates | ✅ | ✗ | `Cube/IsoModulus` |
| Isotropic inverse inequalities, `A^s_q` with the isotropic modulus, coordinate and isotropic Besov conditions agree for `0 < s < r - 1 + 1/p` | ✅ | ✗ | `Cube/IsoInverse`, `Cube/IsoCoincidence` |
| Filtration schemes (Haar), martingale-difference characterisation | ✅ | ✗ | `Wavelets/Filtration` |
| Haar system on `[0, 1)`: dyadic conditional expectations, density, Haar coefficient characterisation | ✅ | ✗ | `Wavelets/Partition`, `Wavelets/Examples/Haar` |
| Haar coefficients and Besov spaces on the interval and the circle for `0 < s < 1/p` | ✅ | ✗ | `Wavelets/Examples/HaarBesov` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
