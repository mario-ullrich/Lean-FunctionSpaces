# Candidates for Mathlib

General results from this project that Mathlib lacks, grouped by topic, with the main
declarations.

* **Distance to an increasing family of sets** (`ApproximationSpaces/Error.lean`): for an
  increasing family `A n` of nonempty sets, `Metric.infDist f (A n)` tends to zero exactly
  for `f` in the closure of `⋃ n, A n` (`ApproximationScheme.tendsto_approxError_zero_iff`),
  and it does so as soon as it does along the subsequence `2 ^ k`
  (`ApproximationScheme.tendsto_approxError_zero_of_pow`). Stated here for approximation
  schemes; the proofs use only monotonicity and nonemptiness.
* **`ℓ_q` norms of sequences in `ℝ≥0∞`** (`ApproximationSpaces/Sequences/Lq.lean`), as the
  `L_q` norm for the counting measure on `ℕ`: the norm bound `‖a‖_r ≤ ‖a‖_q` for
  `1 ≤ q ≤ r` behind `lp.monotone` (`ENNReal.lqNorm_le_lqNorm_of_le`), homogeneity for
  `ℝ≥0∞` scalars, and splitting off the first terms (`ENNReal.lqNorm_le_head_add_shift`,
  `ENNReal.lqNorm_le_sum_range_add_shift`).
* **Monotone convergence and countable Minkowski for `eLpNorm`**
  (`ApproximationSpaces/Sequences/Hardy.lean`): `ENNReal.lqNorm_iSup` and
  `ENNReal.lqNorm_tsum_le`, stated for the counting measure; the same proof works for
  `eLpNorm` on any measure space. Mathlib has only the finite version `eLpNorm_sum_le`.
* **Weighted Cauchy condensation** (`ApproximationSpaces/Sequences/Dyadic.lean`): for a
  decreasing sequence and a power weight `(n + 1)^γ`, the comparison with the dyadic series
  in both directions (`ENNReal.tsum_pow_mul_le_dyadic`, `ENNReal.dyadic_le_tsum_pow_mul`),
  generalising `ENNReal.le_tsum_condensed` / `ENNReal.tsum_condensed_le`; and
  `ENNReal.rpow_le_rpow_of_nonpos`, which exists for `ℝ` and `ℝ≥0` but not for `ℝ≥0∞`.
* **Discrete Hardy inequalities** (`ApproximationSpaces/Sequences/Hardy.lean`):
  `ENNReal.hardy_tail_le`, `ENNReal.hardy_sum_le`, and the almost diagonal estimate that
  combines both (`ENNReal.lqNorm_almostDiagonal_le`, in `FunctionSpaces/Rd/LocalMeans.lean`).
* **The inclusion `L_r ↪ L_p`** (`FunctionSpaces/Lp/Inclusion.lean`): for a finite measure
  and `p ≤ r`, the bounded linear injection `MeasureTheory.Lp.inclusionOfExponentLe`, with
  its norm bound and compatibility with `BoundedContinuousFunction.toLp`. Mathlib has the
  subgroup inclusion `MeasureTheory.Lp.antitone` but no bundled map.
* **Interpolation between `L_p` and `L_∞`** (`FunctionSpaces/Lp/Interpolation.lean`):
  `eLpNorm f r μ ≤ M^(1-p/r) eLpNorm f p μ^(p/r)` for `‖f‖ ≤ M` a.e.
  (`MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow`).
* **`L_∞` norm of bounded continuous functions** (`FunctionSpaces/Lp/BoundedContinuous.lean`):
  for a measure charging open sets, `‖toLp ∞ μ a‖ = ‖a‖`, and the range is closed
  (`BoundedContinuousFunction.norm_toLp_top`, `.isClosed_range_toLp_top`).
* **Conditional expectation on `L_p`** (`FunctionSpaces/Wavelets/Filtration.lean`): for a finite
  measure and `1 ≤ p ≤ ∞`, `E[· | m]` as a contraction `Lp E p μ →L Lp E p μ`
  (`MeasureTheory.Lp.condExpLp`); Mathlib bundles it only on `L_1` and `L_2`.
* **Conditional expectation onto a countable partition**
  (`FunctionSpaces/Wavelets/Partition.lean`): for `φ : α → ι` with `ι` countable, measurable
  fibres and a finite measure, `μ[f | MeasurableSpace.comap φ ⊤]` is a.e. the average of `f`
  over the fibre through the point (`MeasureTheory.condExp_comap_ae_eq`).
* **Fourier analysis on the torus** (`FunctionSpaces/Torus/Translation.lean`): the Fourier
  coefficients of a translate, `(τ_h f)^(k) = e_k(h) f̂(k)`
  (`Torus.mFourierCoeff_translate`), and `|∏ aᵢ - 1| ≤ ∑ |aᵢ - 1|` for unimodular `aᵢ`
  (`Torus.norm_prod_sub_one_le`). Mathlib's measure on `UnitAddCircle` is a local instance
  in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, so `mFourierBasis` cannot be used
  outside that file without re-declaring it (`FunctionSpaces/Torus/Measure.lean`); worth
  reporting upstream.
* **Differences of polynomials by derivatives** (`FunctionSpaces/Interval/PolyDifferences.lean`):
  `|Δ_σ^m P(y)| ≤ σ^m sup_{[y, y+mσ]} |P^(m)|` (`Interval.norm_iterDiff_polyFun_le`), and the
  boundedness of every linear map of the polynomials of degree `< r` by the `L_p` norm on an
  interval (`Interval.exists_enorm_linearMap_le_eLpNorm`), a form of Markov's inequality.
* **The translation algebra** (`FunctionSpaces/Cube/Translation.lean`): `ℂ[ℝ^d]` acting on
  functions on `ℝ^d` by translations (`Cube.diffAct`, from `AddMonoidAlgebra.lift`), with
  `(fwdDiff h)^[r] = (δ_h - 1)^r` and the expansion of an isotropic difference into mixed
  coordinate differences (`Cube.isoDiff_eq_sum`); Mathlib's `fwdDiff` has no such link to the
  group algebra.
* **Young's inequality and convolution operators** (`FunctionSpaces/Rd/Convolution.lean`): for a
  Haar measure on a finite-dimensional space, `1 ≤ p < ∞`, integrable `K` and `f ∈ L_p`,
  `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p` (`Rd.eLpNorm_conv_le`), from the weighted Jensen inequality
  `(∫ a g)^p ≤ (∫ a)^(p-1) ∫ a g^p` (`Rd.lintegral_mul_rpow_le`); associativity
  `(K ⋆ L) ⋆ f = K ⋆ (L ⋆ f)` a.e. (`Rd.conv_conv_ae`), convolution as a bounded operator on
  `L_p` (`Rd.convLp`), and Minkowski's integral inequality in the weighted form
  `‖∫ Φ(z) G(·, z) dz‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖G(·, z)‖_p^p dz`
  (`Rd.eLpNorm_integral_kernel_le`). Mathlib has only pointwise bounds of convolutions.
* **Approximate identities in `L_p`** (`FunctionSpaces/Rd/ApproxIdentity.lean`): for integrable
  `Φ` with `∫ Φ = 1`, `‖Φ_c ⋆ f - f‖_p → 0` as `c → ∞`, `Φ_c = c^n Φ(c ·)`
  (`Rd.tendsto_eLpNorm_conv_dilate_sub`, `Rd.tendsto_convLp_dilate`), and the continuity of
  `w ↦ ‖f(· - w) - f‖_p` (`Rd.continuous_eLpNorm_comp_sub_sub`). Mathlib has the pointwise
  convergence of mollifiers for continuous functions.
* **The Fourier transform of dilations and kernel identities**
  (`FunctionSpaces/Rd/LittlewoodPaleyKernels.lean`): `𝓕(c^n Φ(c ·))(ξ) = 𝓕Φ(c⁻¹ ξ)`
  (`Rd.fourier_dilate`), `𝓕(f - g) = 𝓕f - 𝓕g` for integrable functions (`Rd.fourier_sub_apply`),
  and `K ⋆ L = M` from `𝓕K · 𝓕L = 𝓕M` by Fourier inversion (`Rd.conv_eq_of_fourier`).
* **Moduli of smoothness on finite-dimensional spaces** (`FunctionSpaces/Rd/Differences.lean`):
  for Mathlib's `fwdDiff` and a Haar measure, `‖Δ_h^r f‖_p ≤ 2^r ‖f‖_p`, the dilation property
  `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` (`Rd.modulus_mul_le`), and
  `Δ_h^r (K ⋆ f) = (Δ_h^r K) ⋆ f` almost everywhere (`Rd.iterDiff_conv_ae`); the modulus on a
  subset `U`, with the differences restricted to the points `x` with `x, …, x + rh ∈ U`
  (`Rd.modulusOn`, `FunctionSpaces/Rd/DomainModuli.lean`).
* **Multiplication by an indicator on `L_p`** (`FunctionSpaces/Rd/LipschitzGraph.lean`): for a
  measurable set `s`, `g ↦ 1_s g` as a continuous linear operator of norm at most `1` on
  `Lp ℂ p μ` (`Rd.indicatorLp`). Mathlib has `indicatorConstLp` for constant functions.
* **Differences of Schwartz functions in `L_1`** (`FunctionSpaces/Rd/BandInverse.lean`):
  `‖Δ_v^r G‖_1 ≤ ‖v‖^r ‖D^r G‖_1` (`Rd.lintegral_enorm_iterDiff_schwartz_le`), from
  `‖Δ_v G‖_1 ≤ ‖∂_v G‖_1` (`Rd.lintegral_enorm_fwdDiff_le`) and the commutation of differences
  with line derivatives (`Rd.lineDerivOp_fwdDiffSchwartz`).
