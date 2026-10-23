/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces
public import FunctionSpaces.Analysis.Lp.LintegralForm
public import FunctionSpaces.Analysis.Lp.Young
public import FunctionSpaces.Analysis.Lp.Inclusion
public import FunctionSpaces.Analysis.Lp.IndicatorOperator
public import FunctionSpaces.Analysis.Lp.BoundedContinuous
public import FunctionSpaces.Analysis.Lp.MixedNorms
public import FunctionSpaces.Analysis.Lp.Interpolation
public import FunctionSpaces.Analysis.Differences.TranslationAlgebra
public import FunctionSpaces.Analysis.Fourier.Convolution
public import FunctionSpaces.Analysis.Fourier.ApproxIdentity
public import FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels
public import FunctionSpaces.Analysis.Differences.Differences
public import FunctionSpaces.Analysis.Maximal.DyadicGrid
public import FunctionSpaces.Analysis.Maximal.DyadicCubes
public import FunctionSpaces.Analysis.Maximal.HardyLittlewoodMaximal
public import FunctionSpaces.Analysis.Maximal.CalderonZygmund
public import FunctionSpaces.Analysis.Maximal.FeffermanStein
public import FunctionSpaces.Analysis.Fourier.SchwartzCutoff
public import FunctionSpaces.Analysis.Maximal.CalderonZygmundSigned
public import FunctionSpaces.Analysis.Lp.WeakType
public import FunctionSpaces.Analysis.Lp.LayerCake
public import FunctionSpaces.Analysis.Lp.Marcinkiewicz
public import FunctionSpaces.Analysis.Lp.NormingFamily
public import FunctionSpaces.MeasureSpaces.Scheme
public import FunctionSpaces.MeasureSpaces.Besov.Basic
public import FunctionSpaces.MeasureSpaces.Besov.Trivial
public import FunctionSpaces.MeasureSpaces.Besov.Nikolskii
public import FunctionSpaces.MeasureSpaces.Besov.Embeddings
public import FunctionSpaces.MeasureSpaces.Sobolev.Embeddings
public import FunctionSpaces.MeasureSpaces.Spectral.Basic
public import FunctionSpaces.MeasureSpaces.Spectral.Blocks
public import FunctionSpaces.MeasureSpaces.Spectral.ContinuousSpectralBasis
public import FunctionSpaces.MeasureSpaces.Spectral.LocalWeyl
public import FunctionSpaces.Rd.Approximation.BandLimited
public import FunctionSpaces.Rd.LittlewoodPaley.LittlewoodPaley
public import FunctionSpaces.Rd.Differences.DilatedDifferences
public import FunctionSpaces.Rd.Differences.DomainModuli
public import FunctionSpaces.Rd.Differences.MomentKernels
public import FunctionSpaces.Rd.Approximation.BandJackson
public import FunctionSpaces.Rd.Approximation.BandInverse
public import FunctionSpaces.Rd.LittlewoodPaley.BesovDifferences
public import FunctionSpaces.Rd.LocalMeans.LocalMeans
public import FunctionSpaces.Rd.LocalMeans.Multipliers
public import FunctionSpaces.Rd.Atoms.AtomSynthesis
public import FunctionSpaces.Rd.Atoms.AtomAnalysis
public import FunctionSpaces.Rd.Atoms.ConvexDifferences
public import FunctionSpaces.Rd.Atoms.SmoothAtoms
public import FunctionSpaces.Rd.Atoms.AtomComposition
public import FunctionSpaces.Rd.Atoms.DiffeoInvariance
public import FunctionSpaces.Rd.MixedSmoothness.TensorKernels
public import FunctionSpaces.Rd.MixedSmoothness.MixedSequences
public import FunctionSpaces.Rd.MixedSmoothness.MixedDifferences
public import FunctionSpaces.Rd.MixedSmoothness.MixedAveragedDifferences
public import FunctionSpaces.Rd.MixedSmoothness.MixedLocalMeans
public import FunctionSpaces.Rd.MixedSmoothness.MixedLittlewoodPaley
public import FunctionSpaces.Rd.MixedSmoothness.HyperbolicCross
public import FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkin
public import FunctionSpaces.Rd.LocalMeans.KernelMajorants
public import FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans
public import FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinDifferences
public import FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinAtoms
public import FunctionSpaces.Rd.Sobolev.WeakDerivatives
public import FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley
public import FunctionSpaces.Rd.Sobolev.RellichCompactness
public import FunctionSpaces.Rd.SingularIntegrals.DilationFamilies
public import FunctionSpaces.Rd.SingularIntegrals.ConvolutionAdjoint
public import FunctionSpaces.Rd.SingularIntegrals.PlancherelBounds
public import FunctionSpaces.Rd.SingularIntegrals.VectorValuedWeakType
public import FunctionSpaces.Rd.SingularIntegrals.VectorValuedSingularIntegrals
public import FunctionSpaces.Rd.TriebelLizorkin.SquareFunction
public import FunctionSpaces.Rd.Sobolev.DerivativeKernels
public import FunctionSpaces.Rd.Sobolev.SobolevTriebelLizorkin
public import FunctionSpaces.Rd.Sobolev.SobolevEmbedding
public import FunctionSpaces.Rd.BesselPotentials.UniformSchwartzFamilies
public import FunctionSpaces.Rd.BesselPotentials.BesselPotentialLifting
public import FunctionSpaces.Domains.Lipschitz.LipschitzGraph
public import FunctionSpaces.Domains.Extension.RychkovExtension
public import FunctionSpaces.Domains.Extension.LipschitzGraphBesov
public import FunctionSpaces.Domains.Extension.LocalExtension
public import FunctionSpaces.Domains.Lipschitz.BoundedLipschitz
public import FunctionSpaces.Domains.Lipschitz.HalfSpace
public import FunctionSpaces.Domains.Traces.HalfSpaceTrace
public import FunctionSpaces.Domains.Lipschitz.GraphParametrization
public import FunctionSpaces.Domains.Traces.GraphTrace
public import FunctionSpaces.Domains.Traces.MollifiedGraph
public import FunctionSpaces.Domains.Traces.GraphTraceExtension
public import FunctionSpaces.Domains.Traces.GraphTraceCharts
public import FunctionSpaces.Domains.Traces.LipschitzBoundaryTrace
public import FunctionSpaces.Domains.Manifolds.SmoothMeasure
public import FunctionSpaces.Domains.Manifolds.BesovAtlas
public import FunctionSpaces.Domains.Manifolds.Besov
public import FunctionSpaces.Domains.Lipschitz.GraphStraightening
public import FunctionSpaces.Domains.Manifolds.SmoothDomain
public import FunctionSpaces.Domains.Manifolds.SmoothDomainBesov
public import FunctionSpaces.Domains.Manifolds.BoundaryBesov
public import FunctionSpaces.Domains.Manifolds.BoundaryTrace
public import FunctionSpaces.Domains.Sobolev.LipschitzDomainH1
public import FunctionSpaces.Domains.Sobolev.SobolevRestrictionSpaces
public import FunctionSpaces.Domains.Sobolev.SobolevDuality
public import FunctionSpaces.Domains.Traces.BoundaryTraceSpace
public import FunctionSpaces.Domains.Lipschitz.LipschitzGraphArea
public import FunctionSpaces.Domains.Lipschitz.SurfaceMeasure
public import FunctionSpaces.Domains.Extension.DivergenceKernels
public import FunctionSpaces.Domains.Extension.SobolevExtension
public import FunctionSpaces.Domains.Sobolev.LipschitzGraphGreen
public import FunctionSpaces.Domains.Sobolev.LipschitzDomainGreen
public import FunctionSpaces.Domains.Traces.TraceKernel
public import FunctionSpaces.Torus.Measure
public import FunctionSpaces.Torus.Scheme
public import FunctionSpaces.Torus.Nikolskii
public import FunctionSpaces.Torus.Sobolev
public import FunctionSpaces.Torus.Embeddings
public import FunctionSpaces.Torus.Coefficients
public import FunctionSpaces.Torus.FourierSpectralBasis
public import FunctionSpaces.Torus.Translation
public import FunctionSpaces.Torus.Modulus
public import FunctionSpaces.Torus.BesovModuli
public import FunctionSpaces.Torus.EuclideanConvolution
public import FunctionSpaces.Torus.LpJackson
public import FunctionSpaces.Torus.LpBesovModuli
public import FunctionSpaces.Torus.EuclideanConvolutionIdentities
public import FunctionSpaces.Torus.LittlewoodPaley
public import FunctionSpaces.Torus.WeakDerivatives
public import FunctionSpaces.Torus.Trace
public import FunctionSpaces.Torus.TriebelLizorkin
public import FunctionSpaces.Torus.PeriodicLift
public import FunctionSpaces.Torus.FeffermanStein
public import FunctionSpaces.Torus.TriebelLizorkinLocalMeans
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
public import FunctionSpaces.Wavelets.Filtration
public import FunctionSpaces.Wavelets.Partition
public import FunctionSpaces.Wavelets.Examples.Haar
public import FunctionSpaces.Wavelets.Examples.HaarBesov
public import FunctionSpaces.Wavelets.Examples.Multiscale
public import FunctionSpaces.Wavelets.Examples.Alpert
public import FunctionSpaces.Wavelets.Daubechies.DaubechiesPolynomial
public import FunctionSpaces.Wavelets.Daubechies.FourierIntegrable
public import FunctionSpaces.Wavelets.Daubechies.FejerRiesz
public import FunctionSpaces.Wavelets.Daubechies.Mask
public import FunctionSpaces.Wavelets.Daubechies.MaskExistence
public import FunctionSpaces.Wavelets.Daubechies.FilterIdentities
public import FunctionSpaces.Wavelets.Daubechies.D4
public import FunctionSpaces.Wavelets.Daubechies.SymbolProduct
public import FunctionSpaces.Wavelets.Daubechies.TransferOperator
public import FunctionSpaces.Wavelets.Daubechies.SymbolDecay
public import FunctionSpaces.Wavelets.Daubechies.TransferExamples
public import FunctionSpaces.Wavelets.Daubechies.ScalingFunction
public import FunctionSpaces.Wavelets.Daubechies.Cascade
public import FunctionSpaces.Wavelets.Daubechies.Orthonormality
public import FunctionSpaces.Wavelets.Daubechies.ScalingMoments
public import FunctionSpaces.Wavelets.Daubechies.PolynomialReproduction
public import FunctionSpaces.Wavelets.Daubechies.SobolevRegularity
public import FunctionSpaces.Wavelets.Daubechies.HolderRegularity
public import FunctionSpaces.Wavelets.Daubechies.MatrixMethod
public import FunctionSpaces.Wavelets.Daubechies.MatrixMethodD4
public import FunctionSpaces.Wavelets.Daubechies.Expansion
public import FunctionSpaces.Wavelets.Daubechies.ExpansionScaling
public import FunctionSpaces.Wavelets.Daubechies.Projections
public import FunctionSpaces.Wavelets.Daubechies.Wavelet
public import FunctionSpaces.Wavelets.Daubechies.JacksonSmoothing
public import FunctionSpaces.Wavelets.Daubechies.Jackson
public import FunctionSpaces.Wavelets.Daubechies.Bernstein
public import FunctionSpaces.Wavelets.Daubechies.Besov
public import FunctionSpaces.Wavelets.Daubechies.D4Besov
public import FunctionSpaces.Wavelets.Daubechies.OrderThree

/-!
# Function spaces

Besov and Sobolev spaces on a finite measure space, defined through approximation schemes of
bounded continuous functions, and their embedding theorems.  The library builds on
`ApproximationSpaces`.

## Layout

### Analysis: tools without function-space content

* `FunctionSpaces.Analysis.Lp.LintegralForm`: `L_p` norms through integrals of powers.
* `FunctionSpaces.Analysis.Lp.Young`: the weighted Jensen inequality, Young's inequality on
  measurable groups, and weighted averages in `L_p`.
* `FunctionSpaces.Analysis.Lp.IndicatorOperator`: multiplication by the indicator of a measurable
  set as an operator on `L_p` of norm at most `1`, and integrals over a set as `L_2` pairings.
* `FunctionSpaces.Analysis.Lp.Inclusion`: the bounded linear inclusion `L_r ↪ L_p` for `p ≤ r` and a
  finite measure, `MeasureTheory.Lp.inclusionOfExponentLe`.
* `FunctionSpaces.Analysis.Lp.BoundedContinuous`: bounded continuous functions in `L_p`; for a
  measure charging open sets, `L_∞` restricted to them is the sup norm.
* `FunctionSpaces.Analysis.Lp.MixedNorms`: the mixed norms `L_p(ℓ_q)` and `ℓ_q(L_p)` and their
  comparison, from Minkowski's integral inequality for `ℓ_u`-valued functions, and the
  cancellation of a power in Hölder's inequality.
* `FunctionSpaces.Analysis.Lp.Interpolation`: `‖f‖_r ≤ ‖f‖_∞^(1-p/r) ‖f‖_p^(p/r)`.
* `FunctionSpaces.Analysis.Differences.TranslationAlgebra`: the translation algebra `ℂ[G]` acting on
  functions on an additive commutative monoid `G`, differences as its powers, and the expansion of
  `(δ_h - 1)^r` on `ℝ^d` along the coordinates.
* `FunctionSpaces.Analysis.Fourier.Convolution`: convolution with integrable kernels on a
  finite-dimensional space, Young's inequality, associativity, and the convolution operators on
  `L_p`.
* `FunctionSpaces.Analysis.Fourier.ApproxIdentity`: dilations and their supports, continuity of
  translation in `L_p`, and approximate identities.
* `FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels`: the Fourier transform of integrable
  functions (continuity, `L_1` bounds, convolutions, the multiplication formula, conjugation),
  smooth frequency cut-offs, the kernels `Φ_k`, `Θ_k`, `ψ_j` of the Littlewood–Paley decomposition,
  and their identities by Fourier inversion.
* `FunctionSpaces.Analysis.Differences.Differences`: differences on any additive group, and the
  modulus of smoothness on a finite-dimensional space with the dilation of the scale.
* `FunctionSpaces.Analysis.Maximal.DyadicGrid`: the dyadic cells of a finite-dimensional inner
  product space, their centres, and the counting of centres in balls.
* `FunctionSpaces.Analysis.Maximal.DyadicCubes`: dyadic cubes of every integer level, their nesting,
  and the Lebesgue differentiation theorem along them.
* `FunctionSpaces.Analysis.Maximal.HardyLittlewoodMaximal`: the Hardy–Littlewood maximal function,
  its weighted weak and strong types, and the Hardy–Littlewood maximal theorem.
* `FunctionSpaces.Analysis.Maximal.CalderonZygmund`: the Calderón–Zygmund decomposition on dyadic
  cubes, with the averages over the maximal big cubes, the measure of the exceptional set, and the
  bound `G ≤ t` almost everywhere outside it.
* `FunctionSpaces.Analysis.Maximal.FeffermanStein`: the Fefferman–Stein inequality for the maximal
  functions of a family in `L_p(ℓ_q)`, `1 < p < ∞`, `1 < q ≤ ∞`, with the vector-valued weak type
  `(1,1)`.
* `FunctionSpaces.Analysis.Fourier.SchwartzCutoff`: real test functions as complex Schwartz
  functions, commuting directional derivatives, the transpose formula for iterated derivatives of
  distributions and tempered distributions, and cut-offs converging in the Schwartz space, so that
  test functions determine tempered distributions.
* `FunctionSpaces.Analysis.Maximal.CalderonZygmundSigned`: the signed Calderón–Zygmund decomposition
  of functions with values in a normed space and of families: the good part with its bounds `2^n t`
  and `∫ ‖·‖² ≤ 2^n t ∫ ‖f‖`, and the bad pieces with mean zero on their cubes and total mass at
  most `2 ∫ ‖f‖`.
* `FunctionSpaces.Analysis.Lp.WeakType`: the distribution function, weak `L_p` norms and operators
  of weak and strong type, with the definitions of the Carleson project.
* `FunctionSpaces.Analysis.Lp.LayerCake`: the layer cake formula
  `∫ F^p dν = p ∫_0^∞ ν{F > t} t^(p-1) dt` for `[0, ∞]`-valued functions on every measure space,
  and the integrals of powers of `t` over `(0, b)`, `(0, ∞)` and the level sets `{t < a}`,
  `{t ≥ a}`.
* `FunctionSpaces.Analysis.Lp.Marcinkiewicz`: Marcinkiewicz interpolation between weak type `(1,1)`
  and strong type `(2,2)` for `1 < p < 2` with an explicit constant, by the layer cake argument, for
  operators on an abstract input type and in the terms of the Carleson project.
* `FunctionSpaces.Analysis.Lp.NormingFamily`: `L_p` norms and `L_p(ℓ_2)` norms of families vanishing
  outside a finite set by duality, `1 < p < ∞`, through the norming family
  `u_j ‖(u_i)_i‖_{ℓ_2}^{p-2}`, and Hölder's inequality for `[0, ∞]`-valued functions in `L_p`
  norms.

### Function spaces on measure spaces

* `FunctionSpaces.MeasureSpaces.Scheme`: schemes of functions `FunctionScheme` and their transport
  `FunctionScheme.toLp` to every `L_p(μ)`, compatible with the inclusions.
* `FunctionSpaces.MeasureSpaces.Besov.Basic`: the Besov spaces `B^s_{p,q}(Ω, S) = A^s_q(L_p(μ), S)`.
* `FunctionSpaces.MeasureSpaces.Besov.Trivial`: the embeddings that need no property of the scheme.
* `FunctionSpaces.MeasureSpaces.Besov.Nikolskii`: the Nikolskii property of a scheme and the
  Nikolskii inequality `‖a‖_r ≲ n^(D(1/p-1/r)) ‖a‖_p` it implies.
* `FunctionSpaces.MeasureSpaces.Besov.Embeddings`: the Besov embeddings into `B^{s-α}_{r,q}`, `L_∞`
  and bounded continuous functions.
* `FunctionSpaces.MeasureSpaces.Sobolev.Embeddings`: Sobolev spaces for a scheme as a hypothesis
  structure (smoothness spaces), the Sobolev embedding `W^s_p ↪ W^t_r` and the embedding into
  bounded continuous functions.
* `FunctionSpaces.MeasureSpaces.Spectral.Basic`: spectral schemes in a Hilbert space and their `L_2`
  Sobolev spaces, with Jackson and Bernstein inequalities from Parseval's identity.
* `FunctionSpaces.MeasureSpaces.Spectral.Blocks`: spectral schemes as projection schemes, the
  coefficient characterisation of their approximation spaces and `H^s = A^s_2`.
* `FunctionSpaces.MeasureSpaces.Spectral.ContinuousSpectralBasis`: continuous spectral bases,
  Hilbert bases of `L_2` of a finite measure represented by bounded continuous functions (modelled
  on the eigenfunctions of a Laplacian), their scheme, `B^s_{2,2} = H^s` and the Sobolev spaces.
* `FunctionSpaces.MeasureSpaces.Spectral.LocalWeyl`: the local Weyl bound, the Nikolskii inequality
  for `p ≤ 2` and the continuity of `H^s` for `s > D/2`.

### Function spaces on ℝ^d

* `FunctionSpaces.Rd.Approximation.BandLimited`: the band-limited classes `E_k` in `L_p(ℝ^d)` and
  their scheme.
* `FunctionSpaces.Rd.LittlewoodPaley.LittlewoodPaley`: the Littlewood–Paley blocks, reconstruction,
  and the characterisation of band-limited approximation spaces by Littlewood–Paley blocks.
* `FunctionSpaces.Rd.Differences.DilatedDifferences`: differences of convolutions and dilations, and
  the modulus of a convolution.
* `FunctionSpaces.Rd.Differences.DomainModuli`: differences and moduli of smoothness on subsets of a
  finite-dimensional space.
* `FunctionSpaces.Rd.Differences.MomentKernels`: moment kernels built from dilations, convolution
  with them as an average of differences, and approximation with the modulus, also on subsets.
* `FunctionSpaces.Rd.Approximation.BandJackson`: the Jackson approximant and Jackson's inequality
  for band-limited approximation.
* `FunctionSpaces.Rd.Approximation.BandInverse`: differences of Schwartz functions in `L_1` and the
  inverse inequality for band-limited functions.
* `FunctionSpaces.Rd.LittlewoodPaley.BesovDifferences`: the modulus of smoothness as a modulus
  compatible with the band-limited scheme, and the agreement of the Besov conditions by
  approximation, by Littlewood–Paley blocks and by differences.
* `FunctionSpaces.Rd.LocalMeans.LocalMeans`: local means with moment kernels, the reproducing
  formula, and the characterisation of Besov spaces by local means.
* `FunctionSpaces.Rd.LocalMeans.Multipliers`: Leibniz's rule for differences and pointwise
  multipliers of the Besov spaces by differences.
* `FunctionSpaces.Rd.Atoms.AtomSynthesis`: bounded overlap, regular atoms on a set, the coefficient
  quasi-norm, and the atomic synthesis of Besov spaces by differences, on `V` and on a set.
* `FunctionSpaces.Rd.Atoms.AtomAnalysis`: cell atoms of convolutions, the atomic decomposition by
  local means, and the atomic characterisation of Besov spaces.
* `FunctionSpaces.Rd.Atoms.ConvexDifferences`: differences within a convex set bounded by
  derivatives within the set.
* `FunctionSpaces.Rd.Atoms.SmoothAtoms`: derivatives of convolutions and dilations, smooth atoms on
  a convex set as regular atoms, and the atomic decomposition into smooth atoms of every order.
* `FunctionSpaces.Rd.Atoms.AtomComposition`: smooth changes of variables with a cut-off on a convex
  set, their action on continuous functions, and smooth atoms under them.
* `FunctionSpaces.Rd.Atoms.DiffeoInvariance`: the change of variables on `L_p`, the transport of
  smooth atoms, the invariance of the Besov spaces, and Besov domains.
* `FunctionSpaces.Rd.MixedSmoothness.TensorKernels`: tensor products of one-dimensional kernels on
  `ℝ^d`, their integrals, convolutions, dilations, and diagonal changes of variables.
* `FunctionSpaces.Rd.MixedSmoothness.MixedSequences`: `ℓ_q` norms on `ℕ^d`, the mixed weights
  `2^(s|k|_1)`, the Schur test and the almost diagonal lemma on `ℕ^d`.
* `FunctionSpaces.Rd.MixedSmoothness.MixedDifferences`: mixed differences through the algebra of
  translations, mixed moduli of smoothness, and the Besov quasi-norm of dominating mixed smoothness.
* `FunctionSpaces.Rd.MixedSmoothness.MixedAveragedDifferences`: bounded action of polynomials in
  translations, the moment kernel polynomial, and convolutions with tensor products of dilated bumps
  as averages of translates.
* `FunctionSpaces.Rd.MixedSmoothness.MixedLocalMeans`: mixed local means, their bound by the mixed
  modulus, the mixed reproducing formula, and the equivalence of mixed local means and mixed
  differences.
* `FunctionSpaces.Rd.MixedSmoothness.MixedLittlewoodPaley`: tensor Littlewood–Paley blocks,
  Vybíral's quasi-norm, and its equivalence with mixed local means and mixed differences.
* `FunctionSpaces.Rd.MixedSmoothness.HyperbolicCross`: levels, hyperbolic crosses, and the rate of
  approximation by the hyperbolic cross partial sums.
* `FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkin`: the Triebel–Lizorkin quasi-norm by
  Littlewood–Paley blocks, `F^s_{p,p} = B^s_{p,p}` and the sandwich
  `B^s_{p,min(p,q)} ⊆ F^s_{p,q} ⊆ B^s_{p,max(p,q)}`.
* `FunctionSpaces.Rd.LocalMeans.KernelMajorants`: Peetre majorants of the cross kernels `k_j ⋆ Θ_i`
  and `ψ_j ⋆ η_i` with explicit constants, and the maximal function bound of convolutions with such
  kernels.
* `FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans`: the local means quasi-norm of
  Triebel–Lizorkin type, pointwise bounds of blocks and local means by maximal functions, and
  the local means characterisation of `F^s_{p,q}` for `1 < p < ∞`, `1 < q ≤ ∞`, `0 < s < L`.
* `FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinDifferences`: ball means of differences, their
  pointwise comparison with local means, and the characterisation of `F^s_{p,q}` by ball means of
  differences for `1 < p < ∞`, `1 < q ≤ ∞`, `0 < s < L`.
* `FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinAtoms`: the sequence space `f^s_{p,q}`, local
  means of smooth atoms by maximal functions of the coefficients, and the atomic characterisation of
  `F^s_{p,q}` for `1 < p < ∞`, `1 < q ≤ ∞`, `0 < s < L`.
* `FunctionSpaces.Rd.Sobolev.WeakDerivatives`: weak derivatives on open sets as equalities of
  distributions, integration by parts against test functions, uniqueness, locality, limits in
  `L_p`, the Sobolev spaces `W^m_p(Ω)` and `W^m_p(ℝ^d)`, and the identification with derivatives
  of tempered distributions on `ℝ^d`.
* `FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley`: the convolution theorem and Plancherel for
  a convolution on `L_2(ℝ^d)`, the Bessel potential on Schwartz functions, even Fourier multipliers
  acting on tempered distributions by the transpose, Mathlib's Sobolev spaces `H^s(ℝ^d)` as the
  Triebel–Lizorkin spaces `F^s_{2,2}(ℝ^d)` for `s ≥ 0` and the Besov spaces `B^s_{2,2}(ℝ^d)` for
  `s > 0`, with explicit constants, and `W^1_2(ℝ^d) = H^1(ℝ^d) = B^1_{2,2}(ℝ^d)`.
* `FunctionSpaces.Rd.Sobolev.RellichCompactness`: the inverse Fourier transform of integrable `L_2`
  functions, band-limited functions as bounded Lipschitz functions, truncation in frequency, and
  Rellich's theorem: the restriction from `H^1(ℝ^d)` to `L_2(Ω)` is compact for bounded `Ω`;
  an element of `H^1(ℝ^d)` is determined by its `L_2` function.
* `FunctionSpaces.Rd.SingularIntegrals.DilationFamilies`: dilations of Schwartz functions and their
  derivatives, families of dilated Schwartz kernels with uniformly bounded seminorms, their
  Hörmander condition with explicit constants, Calderón–Zygmund families with finitely many
  exceptional members and their adjoints, and the Littlewood–Paley blocks and synthesis kernels as
  such families.
* `FunctionSpaces.Rd.SingularIntegrals.ConvolutionAdjoint`: the adjoint identity
  `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)` for `f ∈ L_p`, `g ∈ L_q` and the reflection `K^∨(x) = K(-x)`,
  derivatives of Schwartz kernels moved to the other Schwartz factor, and weak derivatives commuting
  with convolution by Schwartz functions, also for the convolution operators on `L_p`.
* `FunctionSpaces.Rd.SingularIntegrals.PlancherelBounds`: the `L_2` bounds of the analysis operator
  `f ↦ (θ_j ⋆ f)_j` and of the synthesis operators `(g_j)_j ↦ ∑_{j ∈ s} θ_j ⋆ g_j` for finite
  sets `s` by the Fourier overlap `B`, for integrable kernels and for Calderón–Zygmund
  families.
* `FunctionSpaces.Rd.SingularIntegrals.VectorValuedWeakType`: the weak type `(1,1)` of the analysis
  operator and of the synthesis operators of a Calderón–Zygmund family, with the explicit constant
  `4 · 2^n B + (2n)^n |B(0, 1)| + 4H`.
* `FunctionSpaces.Rd.SingularIntegrals.VectorValuedSingularIntegrals`: the strong type `(p,p)`,
  `1 < p < ∞`, of the analysis operator and of the synthesis operators of a Calderón–Zygmund family
  with explicit constants: Plancherel for `p = 2`, Marcinkiewicz interpolation for `p < 2` and
  duality with the adjoint family for `p > 2`.
* `FunctionSpaces.Rd.TriebelLizorkin.SquareFunction`: the square function theorem `L_p = F^0_{p,2}`
  for `1 < p < ∞`, with named constants in both directions, and the reproducing formula
  `∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f) → f` in `L_p` with the synthesis kernels `ψ̃_j`.
* `FunctionSpaces.Rd.Sobolev.DerivativeKernels`: the block `ψ_1` as a sum of derivatives of order
  `m` of Schwartz kernels, `ψ_1 = ∑_i ∂_{e_{i_0}} ⋯ ∂_{e_{i_{m-1}}} η_i`, the Fourier transforms of
  iterated derivatives, and the Calderón–Zygmund families of the dilated derivative kernels and of
  the rescaled derivatives `2^{-jk} ∂^w ψ̃_j` of the synthesis kernels.
* `FunctionSpaces.Rd.Sobolev.SobolevTriebelLizorkin`: the Sobolev spaces `W^m_p = F^m_{p,2}` for
  `1 < p < ∞` with named constants in both directions, and, for `m ≥ 1`, the Besov sandwich
  `B^m_{p,min(p,2)} ⊆ W^m_p ⊆ B^m_{p,max(p,2)}`.
* `FunctionSpaces.Rd.Sobolev.SobolevEmbedding`: continuity of convolutions of integrable bounded
  kernels with `L_p` functions, the Nikolskii inequality for the Littlewood–Paley blocks, the
  Besov embeddings into `L_r` for `s > n(1/p - 1/r)` and into bounded continuous functions for
  `s > n/p`, and the Sobolev embeddings `W^m_p ↪ L_r` and `W^m_p ↪ C_b` with named
  constants.
* `FunctionSpaces.Rd.BesselPotentials.UniformSchwartzFamilies`: uniform Schwartz families under
  continuous linear maps, the shifted Bessel symbols `(ε + ‖ζ‖²)^{σ/2}`, the Bessel kernels
  `K_j = 𝓕⁻¹[(2^{-2j} + ‖ζ‖²)^{σ/2} ω̂]` with `J_σ ω_{2^j} = 2^{jσ} (K_j)_{2^j}`, sums over the
  dyadic scales of an annulus, and the Calderón–Zygmund family of the dilated Bessel kernels for
  `ω̂` supported in an annulus.
* `FunctionSpaces.Rd.BesselPotentials.BesselPotentialLifting`: even Fourier multipliers, among them
  Mathlib's Bessel potential `J_s`, against translations, reflections and convolutions, the
  Calderón–Zygmund families of the Bessel kernels of the Littlewood–Paley kernels,
  `H^{s,p} ∩ L_p = F^s_{p,2}` for real `s` and `H^{s,p} = F^s_{p,2}` for `s ≥ 0`, for `1 < p < ∞`
  with existential constants, and `W^m_p = H^{m,p}`.

### Domains, traces and manifolds

* `FunctionSpaces.Domains.Lipschitz.LipschitzGraph`: Lipschitz graph domains, their cones, the
  closure of the domain plus the cone, the cone bump, the support principle, the cut-off on `L_p`,
  and integrals over a set as `L_2` pairings.
* `FunctionSpaces.Domains.Extension.RychkovExtension`: intrinsic local means on a Lipschitz graph
  domain, Rychkov's extension, and the restrictions of Besov spaces described by intrinsic local
  means.
* `FunctionSpaces.Domains.Extension.LipschitzGraphBesov`: the restrictions of Besov spaces to
  Lipschitz graph domains described by intrinsic differences.
* `FunctionSpaces.Domains.Extension.LocalExtension`: local versions of Rychkov's extension, for
  boundary patches of Lipschitz graph domains and for inner patches.
* `FunctionSpaces.Domains.Lipschitz.BoundedLipschitz`: bounded Lipschitz domains, smooth resolutions
  of unity, and the restrictions of Besov spaces described by intrinsic differences.
* `FunctionSpaces.Domains.Lipschitz.HalfSpace`: null sets and moduli on sets, the closed half-space
  and the models of manifolds as Besov domains.
* `FunctionSpaces.Domains.Traces.HalfSpaceTrace`: restrictions and extensions of smooth atoms on the
  flat graph, the trace theorem and the trace space of the half-space for every smoothness, and the
  traces of functions continuous on the closed half-space.
* `FunctionSpaces.Domains.Lipschitz.GraphParametrization`: the hyperplane and the graph map of a
  Lipschitz graph domain, and the restrictions of atoms to the graph.
* `FunctionSpaces.Domains.Traces.GraphTrace`: the trace on the boundary of a Lipschitz graph domain,
  its boundedness from the intrinsic Besov spaces, its linearity, and the trace of continuous
  functions.
* `FunctionSpaces.Domains.Traces.MollifiedGraph`: the mollified graph function and the vertical
  cut-off, with bounds of their differences.
* `FunctionSpaces.Domains.Traces.GraphTraceExtension`: the extension from the boundary by extended
  atoms and the trace space of a Lipschitz graph domain.
* `FunctionSpaces.Domains.Traces.GraphTraceCharts`: locality of the trace, its bound by the
  intrinsic norm, approximation by the partial sums of the reproducing formula, change of chart,
  traces of products with smooth functions and of finite sums.
* `FunctionSpaces.Domains.Traces.LipschitzBoundaryTrace`: almost everywhere on the boundary of a
  bounded Lipschitz domain, Besov spaces on the boundary, the boundary trace, its existence and
  uniqueness for functions with a finite intrinsic Besov norm, and its trace space.
* `FunctionSpaces.Domains.Manifolds.SmoothMeasure`: smooth measures on manifolds, integrals in
  charts and their comparison with integrals on the manifold.
* `FunctionSpaces.Domains.Manifolds.BesovAtlas`: Besov atlases, chart pieces in `L_p`, the changes
  of charts with cut-offs, the pieces of two atlases, and lifts of functions from a chart.
* `FunctionSpaces.Domains.Manifolds.Besov`: the Besov quasi-norm of an atlas, its independence of
  the atlas and of the order, the Besov spaces of a compact manifold, and lifts from a chart in
  them.
* `FunctionSpaces.Domains.Lipschitz.GraphStraightening`: the flattening of a graph domain, its
  inverse, and its preservation of the Lebesgue measure.
* `FunctionSpaces.Domains.Manifolds.SmoothDomain`: smooth bounded domains, straighteners and their
  charts, the closure as a compact manifold with boundary, and the Lebesgue measure as a smooth
  measure.
* `FunctionSpaces.Domains.Manifolds.SmoothDomainBesov`: global atlases, extension by zero, and the
  Besov space of a smooth domain by charts as the intrinsic Besov space.
* `FunctionSpaces.Domains.Manifolds.BoundaryBesov`: the boundary hyperplane of the half-space, the
  changes of charts restricted to it, boundary pieces, and the Besov spaces of the boundary of a
  compact manifold with their independence of the atlas.
* `FunctionSpaces.Domains.Manifolds.BoundaryTrace`: the trace commutes with the changes of charts,
  the trace on the boundary of a compact manifold, its independence of the atlas, and the trace
  theorem.
* `FunctionSpaces.Domains.Sobolev.LipschitzDomainH1`: `H^1(Ω)` on a bounded Lipschitz domain `Ω` as
  the space of restrictions of `H^1(ℝ^d)`, its description by intrinsic differences, the weak
  gradient on `Ω`, and the boundary traces in `B^{1/2}_{2,2}(∂Ω)`, which form the trace space.
* `FunctionSpaces.Domains.Sobolev.SobolevRestrictionSpaces`: the Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)`
  and `H^s_0(Ω)` on open sets `Ω ⊆ ℝ^d` for real `s`, built inside Mathlib's `H^s(ℝ^d)`: restriction
  as an orthogonal projection, `H^s(Ω)` as a quotient, elements of `H^1(Ω)` determined by their
  values on `Ω`, the compact embedding `H^1(Ω) → L_2(Ω)` for bounded `Ω`, the weak derivatives
  `∂_v : H^1(ℝ^d) → L_2(ℝ^d)` as bounded operators, the density of the compactly supported Schwartz
  functions in `H^s(ℝ^d)`, Schwartz functions with compact support in `Ω` in the span of the test
  functions, `H̃^s(ℝ^d) = H^s(ℝ^d)`, and the isometry `H̃^1(Ω) ≅ H^1_0(Ω)`.
* `FunctionSpaces.Domains.Sobolev.SobolevDuality`: the Bessel potential of real Schwartz functions
  as a real function, the isometry `J_{2s} : H^s(ℝ^d) → H^{-s}(ℝ^d)`, the pairing of `H^{-s}(ℝ^d)`
  and `H^s(ℝ^d)`, and the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)`, `(H^s(Ω))^* ≅ H̃^{-s}(Ω)` and
  `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` on open sets for real `s`.
* `FunctionSpaces.Domains.Traces.BoundaryTraceSpace`: `H^1(ℝ^d) ⊆ B^{1/2}_{2,1}(ℝ^d)` with explicit
  constants, the trace of `H^1(ℝ^d)` on a Lipschitz graph and the chart traces of `H^1(Ω)` on a
  bounded Lipschitz domain as bounded operators, the trace kernel, the trace space `H^{1/2}(Γ)`
  of the boundary `Γ`, defined as its orthogonal complement, with the trace and extension
  operators, and its dual `H^{-1/2}(Γ)`.
* `FunctionSpaces.Domains.Lipschitz.LipschitzGraphArea`: the area formula for Lipschitz graphs: the
  image of a measurable set `A` of the hyperplane under the graph map has `(n-1)`-dimensional
  Euclidean Hausdorff measure `∫_A √(1 + ‖∇φ‖²)`, where `n = dim V`; the outward unit normal of a
  Lipschitz graph domain.
* `FunctionSpaces.Domains.Lipschitz.SurfaceMeasure`: the surface measure of the boundary `Γ` of a
  bounded Lipschitz domain as the `(n-1)`-dimensional Euclidean Hausdorff measure on `Γ`, its chart
  form, `|Γ| = 0`, the space `L_2(Γ)`, the traces `H^1(Ω) → L_2(Γ)` and `H^{1/2}(Γ) → L_2(Γ)`, and
  the outward unit normal field.
* `FunctionSpaces.Domains.Extension.DivergenceKernels`: smoothness of parametric integrals, the
  dilation identity `m_2 - m = ∑_i ∂_{e_i} K_i` with `K_i(x) = ⟪e_i, x⟫ ∫_1^2 t⁻¹ m_t(x) dt`, the
  divergence kernels as Schwartz functions with mean zero when `m` has vanishing first moments, and
  the Calderón–Zygmund families of the dilates of mean-zero Schwartz functions.
* `FunctionSpaces.Domains.Extension.SobolevExtension`: the local means of order two by the gradient,
  the local means of Triebel–Lizorkin type on a set, bounded extensions from the patches of a
  bounded Lipschitz domain pasted in `W^1_p(ℝ^d)`, and the extension theorem
  `W^1_p(Ω) = W^1_p(ℝ^d)|_Ω` for `1 < p < ∞` with a bound; for `p = 2`, `H^1(Ω) = W^1_2(Ω)`,
  Rellich's theorem in `W^1_2(Ω)`, the equivalence of the quotient norm of `H^1(Ω)` with the
  `W^1_2(Ω)` norm, and the boundary traces of `W^1_2(Ω)`.
* `FunctionSpaces.Domains.Sobolev.LipschitzGraphGreen`: Gauss–Green on a Lipschitz graph domain:
  product coordinates and Fubini, ray integrals and integrals of line derivatives of Lipschitz
  functions, `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dσ` for compactly supported `C^1` functions in chart and
  surface form, the product rule for line derivatives, and Green's formula
  `∫_Ω (∂_v f) g + f ∂_v g = ∫_Γ Tr f · Tr g ⟪v, ν⟫ dσ` for `f, g ∈ W^1_2(ℝ^d)`.
* `FunctionSpaces.Domains.Sobolev.LipschitzDomainGreen`: Green's formula on a bounded Lipschitz
  domain: integration by parts in `H^1(ℝ^d)`, resolutions of unity equal to one near the boundary,
  the chart form `∑_j ∫_{H_j} ψ_j Tr_j f · Tr_j g · n^j_v`, the unit normal as the chart normal
  almost everywhere on the boundary, the surface form
  `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γ u · γ w ⟪v, ν⟫ dσ` for `u, w ∈ H^1(Ω)`, and the zero extension:
  `1_Ω u ∈ W^1_2(ℝ^d)` iff the trace of `u` vanishes.
* `FunctionSpaces.Domains.Traces.TraceKernel`: the kernel of the trace on a bounded Lipschitz
  domain: mollification converges in `H^1(ℝ^d)`, mollifiers supported in the cone of a chart,
  `H̃^1(Ω)` as the space of `H^1(ℝ^d)` functions vanishing outside `Ω`, `ker γ = H^1_0(Ω)` (McLean,
  Theorem 3.40), `H^1(Ω) ⧸ H^1_0(Ω) ≅ H^{1/2}(Γ)`, `H̃^1(Ω) ≅ ker γ` and `(ker γ)^* ≅ H^{-1}(Ω)`.

### The torus

* `FunctionSpaces.Torus.Measure`: Mathlib's normalised Haar measure on the torus as a scoped
  instance, `open scoped TorusHaar`.
* `FunctionSpaces.Torus.Scheme`: trigonometric polynomials of degree `< n` and their scheme
  `Torus.trigScheme`.
* `FunctionSpaces.Torus.Nikolskii`: the Nikolskii inequality for trigonometric polynomials by
  the power trick, `Torus.trigScheme_hasNikolskii`.
* `FunctionSpaces.Torus.Sobolev`: the Fourier basis of `L_2(𝕋^d)` as a spectral scheme and
  the Sobolev spaces `H^s(𝕋^d)`.
* `FunctionSpaces.Torus.Embeddings`: the embedding theorems on the torus.
* `FunctionSpaces.Torus.Coefficients`: `B^s_{2,2}(𝕋^d) = H^s(𝕋^d)` and the Littlewood–Paley
  characterisation of `B^s_{2,q}(𝕋^d)`.
* `FunctionSpaces.Torus.FourierSpectralBasis`: the Fourier basis as a continuous spectral basis,
  with the local Weyl bound and the Nikolskii property.
* `FunctionSpaces.Torus.Translation`: translations on `L_2(𝕋^d)` and their Fourier
  multipliers.
* `FunctionSpaces.Torus.Modulus`: the modulus of smoothness `ω(f, t)_2`, the growth of the
  moduli of order `r` in `L_p`, and Jackson's theorem `E_n(f)_2 ≤ √d ω(f, 1/n)_2`.
* `FunctionSpaces.Torus.BesovModuli`: the classical Besov norm through the modulus and
  the coincidence theorem with `B^s_{2,q}(𝕋^d)` for `0 < s < 1`.
* `FunctionSpaces.Torus.EuclideanConvolution`: the quotient map `ℝ^d → 𝕋^d`, convolution on the
  torus with kernels on `ℝ^d`, Young's inequality, Fourier multipliers and differences.
* `FunctionSpaces.Torus.LpJackson`: Jackson's and Bernstein's inequalities for trigonometric
  polynomials in `L_p(𝕋^d)`, `1 ≤ p < ∞`, with moduli of every order.
* `FunctionSpaces.Torus.LpBesovModuli`: the Besov spaces `B^s_{p,q}(𝕋^d)` through moduli of
  smoothness for all `1 ≤ p < ∞`.
* `FunctionSpaces.Torus.EuclideanConvolutionIdentities`: identities of the convolution
  operators on the torus through their Fourier multipliers, and approximate identities.
* `FunctionSpaces.Torus.LittlewoodPaley`: Littlewood–Paley blocks on the torus and the
  characterisation of `B^s_{p,q}(𝕋^d)` by them for all `1 ≤ p < ∞`.
* `FunctionSpaces.Torus.WeakDerivatives`: weak derivatives on the torus through Fourier
  coefficients and `W^m_2(𝕋^d) = H^m(𝕋^d) = B^m_{2,2}(𝕋^d)`.
* `FunctionSpaces.Torus.Trace`: the trace on the face `{x_0 = 0}` of `𝕋^(n+1)`,
  `B^{s+1/p}_{p,q}(𝕋^(n+1)) → B^s_{p,q}(𝕋^n)`, bounded and onto.
* `FunctionSpaces.Torus.TriebelLizorkin`: the Triebel–Lizorkin quasi-norm on the torus,
  `F^s_{p,p}(𝕋^d) = B^s_{p,p}(𝕋^d)` and the Besov sandwich on the torus.
* `FunctionSpaces.Torus.PeriodicLift`: period boxes, the quotient map `ℝ^d → 𝕋^d` as a measure
  preserving map on them, lifts of almost everywhere statements, convolutions and differences of
  lifts, counting boxes in a ball.
* `FunctionSpaces.Torus.FeffermanStein`: the Fefferman–Stein inequality for the maximal functions
  of periodic lifts on the period box, by localisation.
* `FunctionSpaces.Torus.TriebelLizorkinLocalMeans`: the local means characterisation of
  `F^s_{p,q}(𝕋^d)` for `1 < p < ∞`, `1 < q ≤ ∞`, `0 < s < L`, through the periodic lift.

### Intervals

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

### The cube

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
* `FunctionSpaces.Cube.Translation`: the isotropic difference `Δ_h^r` on `ℝ^d` and its expansion
  into mixed coordinate differences.
* `FunctionSpaces.Cube.IsoModulus`: the isotropic modulus of smoothness on the cube and its
  comparison with the moduli in the coordinates.
* `FunctionSpaces.Cube.IsoInverse`: isotropic differences of functions whose slices lie in a
  class with bounds for differences of every order.
* `FunctionSpaces.Cube.IsoCoincidence`: the inverse inequalities with the isotropic modulus, the
  identification of the approximation spaces with the isotropic Besov spaces, and the agreement
  of the coordinate and the isotropic Besov conditions for `0 < s < r - 1 + 1/p`.

### Wavelets

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
* `FunctionSpaces.Wavelets.Daubechies.DaubechiesPolynomial`: the Daubechies polynomial
  `P_N(y) = ∑_{k<N} C(N-1+k, k) y^k`, its Bézout identity, its values and bounds, and its
  trigonometric form `P_N(sin²(πξ))`.
* `FunctionSpaces.Wavelets.Daubechies.FourierIntegrable`: the Fourier transform of integrable
  functions on `ℝ`: continuity and bounds, translations and dilations, the multiplication formula,
  Parseval's identity for integrable functions with integrable transforms, and the fundamental lemma
  with Schwartz test functions.
* `FunctionSpaces.Wavelets.Daubechies.FejerRiesz`: the Fejér–Riesz theorem: a real polynomial `Q`
  positive on `[-1, 1]` satisfies `Q(cos θ) = |L(e^{iθ})|²` for a real polynomial `L` without zeros
  in the closed unit disk.
* `FunctionSpaces.Wavelets.Daubechies.Mask`: the point `e^{-2πiξ}` of the unit circle, masks of
  order `N` (a real polynomial `L` of degree `< N` with `L(1) = 1` and
  `|L(e^{-2πiξ})|² = P_N(sin²(πξ))`), the mask polynomial, the filter coefficients and the symbol
  `m_0` with the quadrature mirror filter identity.
* `FunctionSpaces.Wavelets.Daubechies.MaskExistence`: masks of every order `N ≥ 1` by the
  Fejér–Riesz theorem applied to `P_N((1 - t)/2)`, the minimum-phase mask, whose polynomial `L`
  has no zeros in the closed unit disk, and its identification with D4 for `N = 2`.
* `FunctionSpaces.Wavelets.Daubechies.FilterIdentities`: identities of the filter coefficients:
  orthogonality of the even shifts, the sum rules, parity sums and first moments, the vanishing
  derivatives of the symbol at the half-integers, and the dual filter of the wavelet.
* `FunctionSpaces.Wavelets.Daubechies.D4`: the Daubechies mask D4 of order `2` and its four filter
  coefficients.
* `FunctionSpaces.Wavelets.Daubechies.SymbolProduct`: the infinite product
  `Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))`: convergence, continuity, the two-scale relation, zeros, and
  `|Φ(ξ)|² = sinc(πξ)^(2N) ∏_j P(ξ/2^(j+1))` through Viète's cosine product.
* `FunctionSpaces.Wavelets.Daubechies.TransferOperator`: the transfer operator
  `T g(ξ) = P(ξ/2) g(ξ/2) + P((ξ+1)/2) g((ξ+1)/2)`, its adjoint identity, the integrals of the
  dyadic products of `P` as integrals of `T^n 1`, and growth bounds.
* `FunctionSpaces.Wavelets.Daubechies.SymbolDecay`: the decay of `Φ` on dyadic annuli:
  `(1 + |ξ|)^(2s) |Φ|²` is integrable for `s < N - log₄ λ` and `(1 + |ξ|)^a |Φ|` for
  `a < N - log₄ λ - 1/2` when `T^n 1 ≤ C λ^n`; `Φ ∈ L¹ ∩ L²` for `N ≥ 2`.
* `FunctionSpaces.Wavelets.Daubechies.TransferExamples`: the transfer operator for `N = 2`
  (`T 1 = 4`) and `N = 3` (eigenvalues `9` and `-4`), with the growth rates `4` and `9` and the
  exponents `1` and `3 - log₂ 3`.
* `FunctionSpaces.Wavelets.Daubechies.ScalingFunction`: the scaling function `φ = 𝓕⁻ Φ`, its
  continuity and bound, the refinement equation `φ(x) = ∑_k c_k φ(2x - k)`, and the fact that `φ` is
  real.
* `FunctionSpaces.Wavelets.Daubechies.Cascade`: the cascade algorithm
  `η_{n+1}(x) = ∑_k c_k η_n(2x - k)` from the indicator of `[0, 1)`, its Fourier transform, the
  compact support of `φ` in `[0, 2N - 1]` by testing against Schwartz functions, and `𝓕 φ = Φ`,
  `∫ φ = 1`.
* `FunctionSpaces.Wavelets.Daubechies.Orthonormality`: `∫ w |Φ|² = ∫_0^1 w` for continuous
  `1`-periodic `w` through the truncated products, and the orthonormality of the integer translates
  of `φ`.
* `FunctionSpaces.Wavelets.Daubechies.ScalingMoments`: the smoothness of `Φ`, its vanishing
  derivatives of order `< N` at the nonzero integers, the constant periodised moments of `φ` by
  Poisson summation, and the partition of unity `∑_k φ(x - k) = 1`.
* `FunctionSpaces.Wavelets.Daubechies.PolynomialReproduction`: every polynomial of degree `< N` as a
  combination of the translates of `φ` with polynomial coefficients, the recovery of coefficients by
  orthonormality, and the projection identity `∑_k ⟨Q, φ(· - k)⟩ φ(x - k) = Q(x)`, also at every
  level `j`.
* `FunctionSpaces.Wavelets.Daubechies.SobolevRegularity`: the Fourier transform of differences,
  Parseval for the differences of `φ`, and the bound `ω_r(φ, t)_p ≤ K t^s` for `p ≤ 2` and
  `s < N - log₄ λ` under a growth bound of the transfer operator, with the instances `s < 1` for
  `N = 2` and `s < 3 - log₂ 3` for `N = 3`.
* `FunctionSpaces.Wavelets.Daubechies.HolderRegularity`: the differences of `φ` through the inverse
  Fourier transform: the Hölder bound `|Δ_h^r φ(x)| ≤ K |h|^a` for `a < N - log₄ λ - 1/2`, the
  modulus in `L_∞`, and the moduli in `L_p` for `p ≥ 2` by interpolation between `L²` and `L_∞`,
  with the instances for `N = 2, 3`.
* `FunctionSpaces.Wavelets.Daubechies.MatrixMethod`: the dyadic descent: two functions on `[0, 1)`
  with halving and triangular recursions on the two halves have differences `O(ρ^n)` on dyadic
  intervals of level `n`, which gives a Hölder bound with exponent `-log₂ ρ`.
* `FunctionSpaces.Wavelets.Daubechies.MatrixMethodD4`: the matrix method of Daubechies and Lagarias
  for D4 in scalar form: the scaling function of D4 is Hölder continuous of every order
  `a ≤ 2 - log₂(1 + √3)`, and `2 - log₂(1 + √3) > 0.55`.
* `FunctionSpaces.Wavelets.Daubechies.Expansion`: expansions `∑_k c_k g_{j,k}` in the dilated
  translates `g_{j,k}(x) = 2^{j/2} g(2^j x - k)` of a compactly supported generator: finite sums at
  each point, the window inequality, coefficient recovery under orthonormality, and the two-sided
  stability `‖∑_k c_k g_{j,k}‖_p ≍ 2^{j(1/2 - 1/p)} ‖c‖_{ℓ_p}` with explicit constants.
* `FunctionSpaces.Wavelets.Daubechies.ExpansionScaling`: the expansions in the scaling function:
  `φ_{j,k}` with its support, orthonormality at every level, coefficient recovery, and the
  refinement relation `φ_{j,k} = ∑_i (c_i/√2) φ_{j+1,2k+i}`.
* `FunctionSpaces.Wavelets.Daubechies.Projections`: the projections
  `P_j f = ∑_k ⟨f, φ_{j,k}⟩ φ_{j,k}`: uniform bounds on `L_p`, the local bound on dyadic cells,
  reproduction of expansions and of polynomials of degree `< N`, the nested spaces `V_j`, density,
  and the approximation scheme with its projection scheme.
* `FunctionSpaces.Wavelets.Daubechies.Wavelet`: the Daubechies wavelet
  `ψ(x) = ∑_k (-1)^k c_{1-k} φ(2x - k)`: support, orthonormality of its translates and orthogonality
  to those of `φ`, the decomposition `P_{j+1} f - P_j f = ∑_k ⟨f, ψ_{j,k}⟩ ψ_{j,k}`, the norms of
  the blocks through the wavelet coefficients, and the vanishing moments of order `< N`.
* `FunctionSpaces.Wavelets.Daubechies.JacksonSmoothing`: Steklov smoothing on the whole line:
  `‖f - S_δ f‖_p ≤ ω_r(f, rδ)_p` and `‖(S_δ f)^(r)‖_p ≤ 2^r δ^(-r) ω_r(f, rδ)_p` for continuous `f`,
  in the dyadic form used by Jackson's inequality.
* `FunctionSpaces.Wavelets.Daubechies.Jackson`: Jackson's inequality
  `E_{2^j}(f)_p ≤ C_J ω_N(f, 2^(-j))_p` for the spaces `V_j`, from Steklov smoothing, Taylor
  polynomials on the windows of the dyadic cells and the local reproduction of polynomials.
* `FunctionSpaces.Wavelets.Daubechies.Bernstein`: Bernstein's inequality for the spaces `V_j`:
  `ω_r(a, t)_p ≤ C ω_r(φ, 2^j t)_p ‖a‖_p` for `a ∈ V_j`, the bounds `ω_r(φ, t)_p ≤ K t^θ` from the
  regularity theorems (also for D4 with its Hölder exponent), and the inverse inequality of the
  scheme.
* `FunctionSpaces.Wavelets.Daubechies.Besov`: the approximation spaces of the Daubechies scheme are
  the Besov spaces: `A^s_q = B^s_{p,q}(ℝ)` for `0 < s < θ` under a Bernstein bound of order `θ`, and
  `f ∈ B^s_{p,q}(ℝ)` iff its Daubechies coefficients lie in `b^s_{p,q}`, with the ranges
  `s < N - log₄ λ` for `p ≤ 2` and the interpolated range for `p ≥ 2`.
* `FunctionSpaces.Wavelets.Daubechies.D4Besov`: Besov spaces by D4 coefficients: the range
  `0 < s < 1` for `p ≤ 2`, the interpolated range `0 < s < 2/p + (1 - 2/p)(2 - log₂(1 + √3))` for
  `p ≥ 2`, and `0 < s < 2 - log₂(1 + √3)` for every `p`.
* `FunctionSpaces.Wavelets.Daubechies.OrderThree`: masks of order three: `φ ∈ H^s` for
  `s < 3 - log₂ 3`, Hölder continuity of order `9/10`, and Besov spaces by coefficients for
  `0 < s < 3 - log₂ 3` if `p ≤ 2`, for `0 < s < 5/2 - log₂ 3 + 1/p` if `p ≥ 2`.
-/
