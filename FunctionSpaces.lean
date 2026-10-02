/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces
public import FunctionSpaces.Lp.Inclusion
public import FunctionSpaces.Lp.BoundedContinuous
public import FunctionSpaces.Scheme
public import FunctionSpaces.Besov.Basic
public import FunctionSpaces.Besov.Trivial
public import FunctionSpaces.Lp.Interpolation
public import FunctionSpaces.Besov.Nikolskii
public import FunctionSpaces.Besov.Embeddings
public import FunctionSpaces.Sobolev.Embeddings
public import FunctionSpaces.Torus.Measure
public import FunctionSpaces.Torus.Scheme
public import FunctionSpaces.Torus.Nikolskii
public import FunctionSpaces.Spectral.Basic
public import FunctionSpaces.Torus.Sobolev
public import FunctionSpaces.Torus.Embeddings
public import FunctionSpaces.Spectral.Blocks
public import FunctionSpaces.Torus.Coefficients
public import FunctionSpaces.Wavelets.Filtration
public import FunctionSpaces.Wavelets.Partition
public import FunctionSpaces.Wavelets.Examples.Haar
public import FunctionSpaces.Wavelets.Examples.HaarBesov
public import FunctionSpaces.Wavelets.Examples.Multiscale
public import FunctionSpaces.Wavelets.Examples.Alpert
public import FunctionSpaces.Torus.Translation
public import FunctionSpaces.Torus.Modulus
public import FunctionSpaces.Torus.BesovModuli
public import FunctionSpaces.Torus.WeakDerivatives
public import FunctionSpaces.Traces.Examples.Torus
public import FunctionSpaces.Atoms.Examples.Torus
public import FunctionSpaces.Atoms.Examples.TorusHat
public import FunctionSpaces.Atoms.Examples.TorusAnalysis
public import FunctionSpaces.Interval.Differences
public import FunctionSpaces.Interval.Modulus
public import FunctionSpaces.Interval.Polynomials
public import FunctionSpaces.Interval.Taylor
public import FunctionSpaces.Interval.Steklov
public import FunctionSpaces.Interval.Smoothing
public import FunctionSpaces.Interval.Whitney
public import FunctionSpaces.Interval.PiecewisePoly
public import FunctionSpaces.Interval.PiecewiseJackson
public import FunctionSpaces.Interval.PiecewiseInverse
public import FunctionSpaces.Interval.Periodic
public import FunctionSpaces.Interval.PiecewisePeriodic
public import FunctionSpaces.Interval.LocalProjection
public import FunctionSpaces.Interval.BSpline
public import FunctionSpaces.Interval.Splines
public import FunctionSpaces.Interval.SplineInverse
public import FunctionSpaces.Interval.QuasiInterp
public import FunctionSpaces.Interval.SplineJackson
public import FunctionSpaces.Interval.SplinePeriodic
public import FunctionSpaces.Interval.SplinePeriodicJackson
public import FunctionSpaces.Interval.PolyDifferences
public import FunctionSpaces.Interval.LowerDifferences
public import FunctionSpaces.Cube.Basic
public import FunctionSpaces.Cube.Modulus
public import FunctionSpaces.Cube.Smoothing
public import FunctionSpaces.Cube.SlicewiseOperators
public import FunctionSpaces.Cube.PiecewisePoly
public import FunctionSpaces.Cube.PiecewiseJackson
public import FunctionSpaces.Cube.PiecewiseInverse
public import FunctionSpaces.Cube.Splines
public import FunctionSpaces.Cube.SplineJackson
public import FunctionSpaces.Cube.SplineInverse
public import FunctionSpaces.Cube.Translation
public import FunctionSpaces.Cube.IsoModulus
public import FunctionSpaces.Cube.IsoInverse
public import FunctionSpaces.Cube.IsoCoincidence
public import FunctionSpaces.Rd.Convolution
public import FunctionSpaces.Rd.ApproxIdentity
public import FunctionSpaces.Rd.LittlewoodPaleyKernels
public import FunctionSpaces.Rd.BandLimited
public import FunctionSpaces.Rd.LittlewoodPaley
public import FunctionSpaces.Rd.Differences
public import FunctionSpaces.Rd.DomainModuli
public import FunctionSpaces.Rd.MomentKernels
public import FunctionSpaces.Rd.BandJackson
public import FunctionSpaces.Rd.BandInverse
public import FunctionSpaces.Rd.BesovDifferences
public import FunctionSpaces.Rd.LocalMeans
public import FunctionSpaces.Rd.LipschitzGraph
public import FunctionSpaces.Rd.RychkovExtension
public import FunctionSpaces.Rd.LipschitzGraphBesov
public import FunctionSpaces.Rd.Multipliers
public import FunctionSpaces.Rd.LocalExtension
public import FunctionSpaces.Rd.BoundedLipschitz
public import FunctionSpaces.Rd.DyadicGrid
public import FunctionSpaces.Rd.AtomSynthesis
public import FunctionSpaces.Rd.AtomAnalysis
public import FunctionSpaces.Rd.GraphParametrization
public import FunctionSpaces.Rd.GraphTrace

/-!
# Function spaces

Besov and Sobolev spaces on a finite measure space, defined through approximation schemes of
bounded continuous functions, and their embedding theorems.  The library builds on
`ApproximationSpaces`.

## Layout

* `FunctionSpaces.Lp.Inclusion`: the bounded linear inclusion `L_r ↪ L_p` for `p ≤ r` and a
  finite measure, `MeasureTheory.Lp.inclusionOfExponentLe`.
* `FunctionSpaces.Lp.BoundedContinuous`: bounded continuous functions in `L_p`; for a measure
  charging open sets, `L_∞` restricted to them is the sup norm.
* `FunctionSpaces.Scheme`: schemes of functions `FunctionScheme` and their transport
  `FunctionScheme.toLp` to every `L_p(μ)`, compatible with the inclusions.
* `FunctionSpaces.Besov.Basic`: the Besov spaces `B^s_{p,q}(Ω, S) = A^s_q(L_p(μ), S)`.
* `FunctionSpaces.Besov.Trivial`: the embeddings that need no property of the scheme.
* `FunctionSpaces.Lp.Interpolation`: `‖f‖_r ≤ ‖f‖_∞^(1-p/r) ‖f‖_p^(p/r)`.
* `FunctionSpaces.Besov.Nikolskii`: the Nikolskii property of a scheme and the Nikolskii
  inequality `‖a‖_r ≲ n^(D(1/p-1/r)) ‖a‖_p` it implies.
* `FunctionSpaces.Besov.Embeddings`: the Besov embeddings into `B^{s-α}_{r,q}`, `L_∞` and
  bounded continuous functions.
* `FunctionSpaces.Sobolev.Embeddings`: Sobolev spaces as smoothness spaces for a scheme, the
  Sobolev embedding `W^s_p ↪ W^t_r` and the embedding into bounded continuous functions.
* `FunctionSpaces.Torus.Measure`: Mathlib's normalised Haar measure on the torus as a scoped
  instance, `open scoped TorusHaar`.
* `FunctionSpaces.Torus.Scheme`: trigonometric polynomials of degree `< n` and their scheme
  `Torus.trigScheme`.
* `FunctionSpaces.Torus.Nikolskii`: the Nikolskii inequality for trigonometric polynomials by
  the power trick, `Torus.trigScheme_hasNikolskii`.
* `FunctionSpaces.Spectral.Basic`: spectral schemes in a Hilbert space and their `L_2` Sobolev
  spaces, with Jackson and Bernstein inequalities from Parseval's identity.
* `FunctionSpaces.Torus.Sobolev`: the Fourier basis of `L_2(𝕋^d)` as a spectral scheme and
  the Sobolev spaces `H^s(𝕋^d)`.
* `FunctionSpaces.Torus.Embeddings`: the embedding theorems on the torus.
* `FunctionSpaces.Spectral.Blocks`: spectral schemes as projection schemes, the coefficient
  characterisation of their approximation spaces and `H^s = A^s_2`.
* `FunctionSpaces.Torus.Coefficients`: `B^s_{2,2}(𝕋^d) = H^s(𝕋^d)` and the Littlewood–Paley
  characterisation of `B^s_{2,q}(𝕋^d)`.
* `FunctionSpaces.Wavelets.Filtration`: conditional expectations as contractions on `L_p`,
  filtration schemes (the Haar system for the dyadic filtration) and the characterisation of
  their approximation spaces by martingale differences.
* `FunctionSpaces.Wavelets.Partition`: the conditional expectation onto the σ-algebra of a
  countable partition is the average over the cells.
* `FunctionSpaces.Wavelets.Examples.Haar`: the Haar system on `[0, 1)` and the characterisation
  of its approximation spaces by Haar coefficients.
* `FunctionSpaces.Wavelets.Examples.HaarBesov`: the Haar scheme as the scheme of piecewise
  constants, and Besov spaces on the interval and the circle through Haar coefficients for
  `0 < s < 1/p`.
* `FunctionSpaces.Wavelets.Examples.Multiscale`: density of piecewise polynomials and the
  characterisation of their approximation spaces, and of `B^s_{p,q}[0, 1]` and `B^s_{p,q}(𝕋)` for
  `0 < s < 1/p`, by the details `P_{k+1} f - P_k f` of local polynomial projections.
* `FunctionSpaces.Wavelets.Examples.Alpert`: multiwavelets of Alpert type, an orthonormal basis
  of the detail space, and the characterisation of `A^s_q` of piecewise polynomials, and of
  `B^s_{p,q}` for `0 < s < 1/p`, by multiwavelet coefficients.
* `FunctionSpaces.Torus.Translation`: translations on `L_2(𝕋^d)` and their Fourier
  multipliers.
* `FunctionSpaces.Torus.Modulus`: the modulus of smoothness `ω(f, t)_2` and Jackson's
  theorem `E_n(f)_2 ≤ √d ω(f, 1/n)_2`.
* `FunctionSpaces.Torus.BesovModuli`: the classical Besov norm through the modulus and
  the coincidence theorem with `B^s_{2,q}(𝕋^d)` for `0 < s < 1`.
* `FunctionSpaces.Torus.WeakDerivatives`: weak derivatives on the torus through Fourier
  coefficients and `W^m_2(𝕋^d) = H^m(𝕋^d) = B^m_{2,2}(𝕋^d)`.
* `FunctionSpaces.Traces.Examples.Torus`: the trace on the face `{x_0 = 0}` of `𝕋^(n+1)`,
  `B^{s+1/p}_{p,q}(𝕋^(n+1)) → B^s_{p,q}(𝕋^n)`, bounded and onto.
* `FunctionSpaces.Atoms.Examples.Torus`: Lipschitz atoms on `𝕋^d` as an atomic system for the
  trigonometric scheme in `L_2`, and synthesis `b^s_{2,q} → B^s_{2,q}(𝕋^d)` for `0 < s < 1`.
* `FunctionSpaces.Atoms.Examples.TorusHat`: hat functions on the circle and the torus and their
  partitions of unity.
* `FunctionSpaces.Atoms.Examples.TorusAnalysis`: decomposition of `f ∈ B^s_{2,q}(𝕋^d)` into
  Lipschitz atoms through quasi-interpolants, and the Lipschitz-atomic characterisation.
* `FunctionSpaces.Interval.Differences`: differences of order `r` and their action on polynomials.
* `FunctionSpaces.Interval.Modulus`: the modulus of smoothness `ω_r(f, t, [a, b])_p` on an interval.
* `FunctionSpaces.Interval.Polynomials`: polynomials of degree `< r` on intervals, equivalence of
  norms and the Nikolskii inequality.
* `FunctionSpaces.Interval.Taylor`: approximation of `C^r` functions by polynomials in `L_p`.
* `FunctionSpaces.Interval.Steklov`: Steklov averages and their derivatives.
* `FunctionSpaces.Interval.Smoothing`: the Steklov smoothing `S_δ f`, Minkowski's inequality for
  averages, and the bounds of `f - S_δ f` and `(S_δ f)^(r)` by the modulus, on a left and a right
  part of `[0, 1]`.
* `FunctionSpaces.Interval.Whitney`: Whitney's inequality on `[0, 1]`, the best polynomial
  approximation bounded by the modulus at one scale.
* `FunctionSpaces.Interval.PiecewisePoly`: dyadic piecewise polynomials on `[0, 1]` and their
  scheme in `L_p[0, 1]`.
* `FunctionSpaces.Interval.PiecewiseJackson`: piecewise Taylor approximation from two
  smoothings, Jackson's inequality for dyadic piecewise polynomials, and the passage from
  continuous functions to `L_p` by density.
* `FunctionSpaces.Interval.PiecewiseInverse`: local estimates for piecewise polynomials on
  `[0, ∞)` and the strip integral, the inverse inequality of order `1/p`, and the identification
  of their approximation spaces with `B^s_{p,q}[0, 1]` for `0 < s < 1/p`.
* `FunctionSpaces.Interval.Periodic`: periodic extensions from `[0, 1)` and the periodic modulus
  of smoothness on the circle.
* `FunctionSpaces.Interval.PiecewisePeriodic`: piecewise polynomials on the circle, their
  approximation spaces `B^s_{p,q}(𝕋)` for `0 < s < 1/p`, and `B^s_{p,q}[0, 1] = B^s_{p,q}(𝕋)` in
  that range.
* `FunctionSpaces.Interval.LocalProjection`: the pairing `∫_0^1 P Q` and its dual basis, local
  projections onto polynomials, and the uniformly bounded projections onto piecewise
  polynomials in `L_p[0, 1]`.
* `FunctionSpaces.Interval.BSpline`: cardinal B-splines, the B-spline basis of the polynomials on
  a unit interval, and Marsden's identity.
* `FunctionSpaces.Interval.Splines`: dyadic splines on `[0, 1]` in jump form, their scheme, and the
  dyadic B-splines as splines.
* `FunctionSpaces.Interval.SplineInverse`: the inverse inequality of order `r - 1 + 1/p` for
  dyadic splines.
* `FunctionSpaces.Interval.QuasiInterp`: a spline quasi-interpolant through local projections and
  B-spline coefficients, its local reproduction of polynomials and its local bounds.
* `FunctionSpaces.Interval.SplineJackson`: Jackson's inequality for dyadic splines and the
  identification of their approximation spaces with `B^s_{p,q}[0, 1]` for `0 < s < r - 1 + 1/p`.
* `FunctionSpaces.Interval.SplinePeriodic`: periodic splines on the circle, their scheme, and
  their inverse inequality of order `r - 1 + 1/p`.
* `FunctionSpaces.Interval.SplinePeriodicJackson`: the periodic quasi-interpolant, Jackson's
  inequality for periodic splines, density of continuous periodic functions, and the
  identification of their approximation spaces with `B^s_{p,q}(𝕋)` for `0 < s < r - 1 + 1/p`.
* `FunctionSpaces.Interval.PolyDifferences`: differences of every order of polynomials by their
  derivatives, and the difference bound `|Δ_t^m P| ≤ K (t/L)^m L^(-1/p) ‖P‖_p`.
* `FunctionSpaces.Interval.LowerDifferences`: differences of every order `m ≤ r` of piecewise
  polynomials and splines, and steps of either sign.
* `FunctionSpaces.Cube.Basic`: the unit cube `[0, 1]^d` with Lebesgue measure, slices in one
  coordinate, and `L_p` norms through slices.
* `FunctionSpaces.Cube.Modulus`: differences in one coordinate, the moduli of smoothness in the
  coordinates, and their sum, the modulus on the cube.
* `FunctionSpaces.Cube.Smoothing`: the Steklov smoothing in one coordinate and its bounds by the
  coordinate modulus near the two ends of the coordinate.
* `FunctionSpaces.Cube.SlicewiseOperators`: finite-rank kernel operators on `[0, 1]`, their
  action on the slices in one coordinate, the forms they produce, and telescoping over the
  coordinates.
* `FunctionSpaces.Cube.PiecewisePoly`: the local projection as a kernel operator, the piecewise
  polynomials of degree `< r` in each variable on dyadic cubes, their scheme, and the tensor
  projection.
* `FunctionSpaces.Cube.PiecewiseJackson`: Jackson's inequality for piecewise polynomials on the
  cube.
* `FunctionSpaces.Cube.PiecewiseInverse`: the inverse inequality of order `1/p` on the cube and
  the identification of the approximation spaces with `B^s_{p,q}([0, 1]^d)` for `0 < s < 1/p`.
* `FunctionSpaces.Cube.Splines`: the spline quasi-interpolant as a kernel operator, the splines of
  order `r` in each variable on the cube, their scheme, and the tensor quasi-interpolant.
* `FunctionSpaces.Cube.SplineJackson`: Jackson's inequality for tensor splines on the cube.
* `FunctionSpaces.Cube.SplineInverse`: the inverse inequality of order `r - 1 + 1/p` for tensor
  splines and the identification of their approximation spaces with `B^s_{p,q}([0, 1]^d)` for
  `0 < s < r - 1 + 1/p`.
* `FunctionSpaces.Cube.Translation`: the translation algebra `ℂ[ℝ^d]` acting on functions, the
  isotropic difference `Δ_h^r`, and its expansion into mixed coordinate differences.
* `FunctionSpaces.Cube.IsoModulus`: the isotropic modulus of smoothness on the cube and its
  comparison with the moduli in the coordinates.
* `FunctionSpaces.Cube.IsoInverse`: isotropic differences of functions whose slices lie in a
  class with bounds for differences of every order.
* `FunctionSpaces.Cube.IsoCoincidence`: the inverse inequalities with the isotropic modulus, the
  identification of the approximation spaces with the isotropic Besov spaces, and the agreement
  of the coordinate and the isotropic Besov conditions for `0 < s < r - 1 + 1/p`.
* `FunctionSpaces.Rd.Convolution`: convolution with integrable kernels on a finite-dimensional
  space, Young's inequality, associativity, and the convolution operators on `L_p`.
* `FunctionSpaces.Rd.ApproxIdentity`: dilations, continuity of translation in `L_p`, and
  approximate identities.
* `FunctionSpaces.Rd.LittlewoodPaleyKernels`: smooth frequency cut-offs, the kernels `Φ_k`,
  `Θ_k`, `ψ_j` of the Littlewood–Paley decomposition, and their identities by Fourier inversion.
* `FunctionSpaces.Rd.BandLimited`: the band-limited classes `E_k` in `L_p(ℝ^d)` and their
  scheme.
* `FunctionSpaces.Rd.LittlewoodPaley`: the Littlewood–Paley blocks, reconstruction, and the
  characterisation of band-limited approximation spaces by Littlewood–Paley blocks.
* `FunctionSpaces.Rd.Differences`: differences and the modulus of smoothness on a
  finite-dimensional space, dilation of the scale, differences of convolutions and dilations.
* `FunctionSpaces.Rd.DomainModuli`: differences and moduli of smoothness on subsets of a
  finite-dimensional space.
* `FunctionSpaces.Rd.MomentKernels`: moment kernels built from dilations, convolution with them as
  an average of differences, and approximation with the modulus, also on subsets.
* `FunctionSpaces.Rd.BandJackson`: the Jackson approximant and Jackson's inequality for
  band-limited approximation.
* `FunctionSpaces.Rd.BandInverse`: differences of Schwartz functions in `L_1` and the inverse
  inequality for band-limited functions.
* `FunctionSpaces.Rd.BesovDifferences`: the modulus of smoothness as a modulus compatible with the
  band-limited scheme, and the agreement of the Besov conditions by approximation, by
  Littlewood–Paley blocks and by differences.
* `FunctionSpaces.Rd.LocalMeans`: local means with moment kernels, the reproducing formula, and
  the characterisation of Besov spaces by local means.
* `FunctionSpaces.Rd.LipschitzGraph`: Lipschitz graph domains, their cones, the cone bump, the
  support principle and the cut-off on `L_p`.
* `FunctionSpaces.Rd.RychkovExtension`: intrinsic local means on a Lipschitz graph domain,
  Rychkov's extension, and the restrictions of Besov spaces described by intrinsic local means.
* `FunctionSpaces.Rd.LipschitzGraphBesov`: the restrictions of Besov spaces to Lipschitz graph
  domains described by intrinsic differences.
* `FunctionSpaces.Rd.Multipliers`: Leibniz's rule for differences and pointwise multipliers of
  the Besov spaces by differences.
* `FunctionSpaces.Rd.LocalExtension`: local versions of Rychkov's extension, for boundary patches
  of Lipschitz graph domains and for inner patches.
* `FunctionSpaces.Rd.BoundedLipschitz`: bounded Lipschitz domains, smooth resolutions of unity, and
  the restrictions of Besov spaces described by intrinsic differences.
* `FunctionSpaces.Rd.DyadicGrid`: the dyadic cells of a finite-dimensional inner product space,
  their centres, and the counting of centres in balls.
* `FunctionSpaces.Rd.AtomSynthesis`: bounded overlap, regular atoms, the coefficient quasi-norm, and
  the atomic synthesis of Besov spaces by differences.
* `FunctionSpaces.Rd.AtomAnalysis`: cell atoms of convolutions, the atomic decomposition by local
  means, and the atomic characterisation of Besov spaces.
* `FunctionSpaces.Rd.GraphParametrization`: the hyperplane and the graph map of a Lipschitz graph
  domain, and the restrictions of atoms to the graph.
* `FunctionSpaces.Rd.GraphTrace`: the trace on the boundary of a Lipschitz graph domain, its
  boundedness from the intrinsic Besov spaces, and the trace of continuous functions.
-/
