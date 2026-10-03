# Candidates for Mathlib

General results from this project that Mathlib lacks, grouped by topic, with the main
declarations.

* **Distance to an increasing family of sets** (`ApproximationSpaces/Error.lean`): for an
  increasing family `A n` of nonempty sets, `Metric.infDist f (A n)` tends to zero exactly
  for `f` in the closure of `⋃ n, A n` (`ApproximationScheme.tendsto_approxError_zero_iff`),
  and it does so as soon as it does along the subsequence `2 ^ k`
  (`ApproximationScheme.tendsto_approxError_zero_of_pow`). Stated here for approximation
  schemes; the proofs use only monotonicity and nonemptiness.
* **`ℓ_q` norms of families in `ℝ≥0∞`** (`ApproximationSpaces/Sequences/Lq.lean`), as the
  `L_q` norm for the counting measure on any countable index set: the norm bound
  `‖a‖_r ≤ ‖a‖_q` for `1 ≤ q ≤ r` behind `lp.monotone` (`ENNReal.lqNorm_le_lqNorm_of_le`),
  homogeneity for `ℝ≥0∞` scalars, the finite-index forms (`ENNReal.lqNorm_eq_sum`,
  `ENNReal.lqNorm_le_card_rpow_mul`, `ENNReal.lqNorm_prod_rpow`), and, on `ℕ`, splitting off the
  first terms (`ENNReal.lqNorm_le_head_add_shift`, `ENNReal.lqNorm_le_sum_range_add_shift`).
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
  `|Δ_σ^m P(y)| ≤ σ^m sup_{[y, y+mσ]} |P^(m)|` (`Interval.norm_higherDiff_polyFun_le`), and the
  boundedness of every linear map of the polynomials of degree `< r` by the `L_p` norm on an
  interval (`Interval.exists_enorm_linearMap_le_eLpNorm`), a form of Markov's inequality.
* **The translation algebra** (`FunctionSpaces/TranslationAlgebra.lean`): `ℂ[G]` acting on
  functions on an additive commutative monoid `G` by translations (`TranslationAlgebra.diffAct`,
  from `AddMonoidAlgebra.lift`), with `(fwdDiff h)^[r] = (δ_h - 1)^r`
  (`TranslationAlgebra.higherDiff_eq_diffAct`), and the expansion of an isotropic difference on
  `ℝ^d` into mixed coordinate differences (`Cube.higherDiff_eq_sum`); Mathlib's `fwdDiff` has no
  such link to the group algebra.
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
  `Δ_h^r (K ⋆ f) = (Δ_h^r K) ⋆ f` almost everywhere (`Rd.higherDiff_conv_ae`); the modulus on a
  subset `U`, with the differences restricted to the points `x` with `x, …, x + rh ∈ U`
  (`Rd.modulusOn`, `FunctionSpaces/Rd/DomainModuli.lean`).
* **Leibniz's rule for iterated forward differences** (`FunctionSpaces/Rd/Multipliers.lean`):
  `Δ_h^r(u v)(x) = ∑_{l ≤ r} C(r, l) Δ_h^l u(x) Δ_h^(r-l) v(x + l h)` (`Rd.higherDiff_mul`); Mathlib
  has only the one-step `fwdDiff_smul`. Also `‖Δ_h^l G(x)‖ ≤ ‖h‖^l sup ‖D^l G‖` for smooth `G`
  (`Rd.norm_higherDiff_le_of_iteratedFDeriv`).
* **Smooth resolutions of unity in a finite-dimensional space**
  (`FunctionSpaces/Rd/BoundedLipschitz.lean`): `Rd.exists_smooth_partition`, with `ContDiff`
  functions, from Mathlib's manifold version, and bounded derivatives of compactly supported smooth
  functions (`Rd.exists_iteratedFDeriv_bound`, `FunctionSpaces/Rd/Multipliers.lean`).
* **Multiplication by an indicator on `L_p`** (`FunctionSpaces/Rd/LipschitzGraph.lean`): for a
  measurable set `s`, `g ↦ 1_s g` as a continuous linear operator of norm at most `1` on
  `Lp ℂ p μ` (`Rd.indicatorLp`). Mathlib has `indicatorConstLp` for constant functions.
* **Differences of Schwartz functions in `L_1`** (`FunctionSpaces/Rd/BandInverse.lean`):
  `‖Δ_v^r G‖_1 ≤ ‖v‖^r ‖D^r G‖_1` (`Rd.lintegral_enorm_higherDiff_schwartz_le`), from
  `‖Δ_v G‖_1 ≤ ‖∂_v G‖_1` (`Rd.lintegral_enorm_fwdDiff_le`) and the commutation of differences
  with line derivatives (`Rd.lineDerivOp_fwdDiffSchwartz`).
* **Bounded overlap in `L_p`** (`FunctionSpaces/Rd/AtomSynthesis.lean`): if at every point at most
  `N` of the functions `g_m` are nonzero, then `‖∑_m g_m‖_p^p ≤ N^(p-1) ∑_m ‖g_m‖_p^p`
  (`Rd.eLpNorm_rpow_le_of_overlap`); a set all of whose finite subsets have at most `N` elements is
  finite with at most `N` elements (`Rd.exists_finset_of_card_le`).
* **Dyadic cells of a finite-dimensional inner product space** (`FunctionSpaces/Rd/DyadicGrid.lean`):
  the cells `⌊2^j ⟪b_i, x⟫⌋ = m_i`, their centres, and the count of at most `(2ρ + 2)^n` centres in
  a ball of radius `ρ 2^(-j)` (`Rd.card_le_of_norm_cellCenter_sub_le`).
* **Pointwise bounds of convolutions** (`FunctionSpaces/Rd/AtomAnalysis.lean`): Hölder's inequality
  on a ball `∫_B |g| ≤ |B|^(1-1/p) ‖g‖_p` (`Rd.lintegral_closedBall_le`),
  `|(K ⋆ g)(x)| ≤ sup |K| |B(0, ρ)|^(1-1/p) ‖g‖_p` for `K` vanishing outside `B(0, ρ)`
  (`Rd.enorm_conv_le_of_bound`), and `Δ_h^r (K ⋆ g) = (Δ_h^r K) ⋆ g` at every point
  (`Rd.higherDiff_conv_apply`).
* **Approximate identities at points of continuity** (`FunctionSpaces/Rd/GraphTrace.lean`): for
  integrable `Φ` with `∫ Φ = 1` and bounded support, `(Φ_{2^J} ⋆ F_J)(z) → z₀` as `J → ∞` and
  `z → y` whenever `F_J(z) → z₀` (`Rd.conv_dilate_near`). Mathlib's `convolution_tendsto_right`
  needs nonnegative kernels.
* **Convolution with Lipschitz functions** (`FunctionSpaces/Rd/MollifiedGraph.lean`): for an
  integrable kernel `K` with bounded support and an `M`-Lipschitz `u`, `K ⋆ u` is Lipschitz with
  constant `M ‖K‖_1` (`Rd.norm_conv_sub_conv_le`), `|K ⋆ u - u| ≤ M R ‖K‖_1` for `∫ K = 1`
  (`Rd.norm_conv_sub_self_le`), and `|Δ_h^2 (K ⋆ u)| ≤ M (R + 2‖h‖) ‖Δ_h^2 K‖_1`
  (`Rd.norm_higherDiff_two_conv_le`); `∫ Δ_h^r K = 0` for `r ≥ 1`
  (`Rd.integral_higherDiff_eq_zero`).
* **Lipschitz images of null sets** (`FunctionSpaces/Rd/GraphTraceCharts.lean`): a Lipschitz map
  between finite-dimensional inner product spaces of the same dimension maps null sets to null sets
  (`Rd.volume_image_eq_zero_of_lipschitzWith`), through the Hausdorff measure, a Haar measure in
  finite dimension.
* **Tensor products of functions** (`FunctionSpaces/Rd/TensorKernels.lean`): for
  `(⊗K)(x) = ∏_i K_i(x_i)` on `ℝ^d`, `‖⊗K‖_1 = ∏_i ‖K_i‖_1` (`Rd.lintegral_enorm_tensorKernel`),
  `(⊗K) ⋆ (⊗K') = ⊗(K_i ⋆ K'_i)` (`Rd.conv_tensorKernel`), and diagonal changes of variables
  `∫ F((a_i z_i)_i) dz = (∏_i a_i)⁻¹ ∫ F` (`Rd.integral_comp_diagMap`).
* **The Schur test on `ℓ_q`** (`FunctionSpaces/Rd/MixedSequences.lean`): row and column sums at most
  `A` give `‖(∑_k w(m, k) b_k)_m‖_{ℓ_q} ≤ A ‖b‖_{ℓ_q}` for `1 ≤ q ≤ ∞` (`Rd.lqNorm_schur_le`),
  for countable index sets; `∑_k ∏_i f_i(k_i) ≤ ∏_i ∑_j f_i(j)` on `ℕ^d`
  (`Rd.tsum_prod_le_prod_tsum`).
