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
* **Monotone convergence and countable Minkowski for `eLpNorm`**: on any measure space,
  `‖sup_b F_b‖_p = sup_b ‖F_b‖_p` for directed countable families of a.e. measurable `F_b`
  (`MeasureTheory.eLpNorm_iSup_of_directed`) and `‖∑_i g_i‖_p ≤ ∑_i ‖g_i‖_p` for
  `1 ≤ p ≤ ∞` and countably many `g_i : α → [0, ∞]` (`MeasureTheory.eLpNorm_tsum_le`), both in
  `FunctionSpaces/Lp/MixedNorms.lean`; the counting-measure versions `ENNReal.lqNorm_iSup` and
  `ENNReal.lqNorm_tsum_le` are in `ApproximationSpaces/Sequences/Hardy.lean`. Mathlib has only
  the finite version `eLpNorm_sum_le`.
* **Mixed norms `L_p(ℓ_q)` and `ℓ_q(L_p)`** (`FunctionSpaces/Lp/MixedNorms.lean`): Minkowski's
  integral inequality for `ℓ_u`-valued functions, `‖(∫ g_i)_i‖_{ℓ_u} ≤ ∫ ‖(g_i(x))_i‖_{ℓ_u}` for
  `1 ≤ u ≤ ∞` (`MeasureTheory.lqNorm_lintegral_le`); `L_p(ℓ_p) = ℓ_p(L_p)` for `0 < p < ∞`
  (`MeasureTheory.eLpNorm_lqNorm_eq_lqNorm_eLpNorm`) and the comparisons for `p ≤ q` and
  `q ≤ p` (`MeasureTheory.lqNorm_eLpNorm_le_eLpNorm_lqNorm`,
  `MeasureTheory.eLpNorm_lqNorm_le_lqNorm_eLpNorm`); and the passage of pointwise bounds to
  limits, `u ≤ v + w_J` a.e. with `‖w_J‖_p → 0` gives `u ≤ v` a.e.
  (`MeasureTheory.ae_le_of_le_add_of_tendsto_eLpNorm`).
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
  `(∫ a g)^p ≤ (∫ a)^(p-1) ∫ a g^p` (`MeasureTheory.lintegral_mul_rpow_le`); associativity
  `(K ⋆ L) ⋆ f = K ⋆ (L ⋆ f)` a.e. (`Rd.conv_conv_ae`), convolution as a bounded operator on
  `L_p` (`Rd.convLp`), and Minkowski's integral inequality in the weighted form
  `‖∫ Φ(z) G(·, z) dz‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖G(·, z)‖_p^p dz`
  (`MeasureTheory.eLpNorm_integral_kernel_le`). Mathlib has only pointwise bounds of convolutions.
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
  has only the one-step `fwdDiff_smul`. Also `‖Δ_h^l G(x)‖ ≤ C ‖h‖^l` for `G` of class `C^l`
  with `‖D^l G‖ ≤ C` on the segment from `x` to `x + l h` (`Rd.norm_higherDiff_le_of_segment`),
  and its global form `‖Δ_h^l G(x)‖ ≤ ‖h‖^l sup ‖D^l G‖`
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
* **The layer cake formula for `[0, ∞]`-valued functions**
  (`FunctionSpaces/Rd/HardyLittlewoodMaximal.lean`): `∫ F^p dν = p ∫_0^∞ ν{F > t} t^(p-1) dt` for
  `p > 0`, every measure and every a.e. measurable `F : α → [0, ∞]`
  (`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal`); Mathlib's
  `lintegral_rpow_eq_lintegral_meas_lt_mul` is for real `f ≥ 0`. Also the `lintegral` of powers
  over intervals, `∫_{(0,b)} t^r dt = b^(r+1)/(r+1)` for `r > -1` and `b ≥ 0`
  (`MeasureTheory.lintegral_Ioo_rpow`) and
  `∫_{(0,∞)} t^r dt = ∞` (`MeasureTheory.lintegral_Ioi_rpow_eq_top`).
* **The Hardy–Littlewood maximal function** (`FunctionSpaces/Rd/HardyLittlewoodMaximal.lean`): the
  centred maximal function on a finite-dimensional inner product space (`Rd.maximal`), its lower
  semicontinuity and measurability for every `g` (`Rd.lowerSemicontinuous_maximal`,
  `Rd.measurable_maximal`), the weighted weak type
  `∫_{Mg > t} w ≤ C t⁻¹ ∫ g Mw` (`Rd.setLIntegral_maximal_gt_le`), the weak type `(1,1)`
  (`Rd.volume_maximal_gt_le`), the weighted strong type `∫ (Mg)^p w ≤ C ∫ g^p Mw`
  (`Rd.lintegral_maximal_rpow_mul_le`) and the maximal theorem `‖Mg‖_p ≤ C ‖g‖_p` for
  `1 < p < ∞` (`Rd.eLpNorm_maximal_le`), with explicit constants. Mathlib has Vitali's covering
  lemma and the differentiation theorem, but no maximal function.
* **Dyadic cubes and Lebesgue differentiation along them** (`FunctionSpaces/Rd/DyadicCubes.lean`):
  the dyadic cubes of every level `k ∈ ℤ` (`Rd.zcell`), their nesting
  (`Rd.zcell_subset_or_disjoint`), and the convergence of the averages over the cubes containing
  `x` to `F(x)` for almost every `x` and locally integrable `F` (`Rd.ae_tendsto_average_cubeAt`),
  from Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`.
* **The Calderón–Zygmund decomposition** (`FunctionSpaces/Rd/CalderonZygmund.lean`): for
  `n ≥ 1`, `t > 0` and a.e. measurable `G` with `∫ G < ∞`, the maximal dyadic cubes with
  average `> t` are disjoint, have averages at most `2^n t`, total measure at most `t⁻¹ ∫ G`
  (`Rd.cz_volume_le`), and `G ≤ t` almost everywhere off their union (`Rd.cz_ae_le_of_notMem`).
* **The Fefferman–Stein inequality** (`FunctionSpaces/Rd/FeffermanStein.lean`):
  `‖ ‖(M g_j)_j‖_{ℓ_q} ‖_p ≤ C ‖ ‖(g_j)_j‖_{ℓ_q} ‖_p` for `1 < p < ∞`, `1 < q ≤ ∞`
  (`Rd.feffermanStein`), with the vector-valued weak type `(1,1)`
  (`Rd.volume_lqNorm_maximal_gt_le`) and the bound of the maximal function off enlarged sets,
  `M(1_{⋃ Q_i} g)(x) ≤ 3^n M g̃(x)` for countably many sets `Q_i ⊆ B̄(c_i, ρ_i)` of positive
  finite measure and `x` outside every `B̄(c_i, 2ρ_i)`, where `g̃ = ∑_i (⨍_{Q_i} g) 1_{Q_i}`
  (`Rd.maximal_indicator_iUnion_le`).
* **Integrals under a change of scale** (`FunctionSpaces/Rd/KernelMajorants.lean`):
  `∫ f(r x) dx = |r^(-n)| ∫ f` for `f : V → [0, ∞]` and `r ≠ 0` (`Rd.lintegral_comp_smul`),
  from Mathlib's `Measure.map_addHaar_smul`; Mathlib has the Bochner version
  `Measure.integral_comp_smul`.
* **The quotient map of the torus** (`FunctionSpaces/Torus/PeriodicLift.lean`): Mathlib has the
  period-box identity `∫_{a + (0,1]^d} g(π x) dx = ∫_{𝕋^d} g` on `d → ℝ`
  (`UnitAddTorus.lintegral_preimage`). New here are the measure preservation of
  `π : ℝ^d → 𝕋^d` on every period box of `EuclideanSpace ℝ d`
  (`Torus.measurePreserving_proj_periodBox`) and the fact that `π` pulls null sets back to null
  sets (`Torus.quasiMeasurePreserving_proj`).
* **The Fejér–Riesz theorem** (`FunctionSpaces/Wavelets/Daubechies/FejerRiesz.lean`): a real
  polynomial `Q` with `Q > 0` on `[-1, 1]` satisfies `Q(cos θ) = |L(e^(iθ))|²` for a real
  polynomial `L` of degree `≤ deg Q` with `L(1) > 0` and without zeros in the closed unit disk
  (`Polynomial.fejer_riesz`, `Polynomial.fejer_riesz_outer`); Mathlib has no factorisation of
  positive trigonometric polynomials.
* **Fourier transforms of integrable functions**
  (`FunctionSpaces/Wavelets/Daubechies/FourierIntegrable.lean`):
  the fundamental lemma with Schwartz test functions on an open set, pointwise for continuous `f`
  (`Real.eqOn_zero_of_integral_mul_schwartz_eq_zero`); Mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` tests with smooth compactly supported
  functions and concludes almost everywhere. Also the transform of differences
  `𝓕(Δ_h^r f)(ξ) = (e^(2πihξ) - 1)^r 𝓕 f(ξ)` (`Real.fourier_iterate_fwdDiff_apply`,
  `SobolevRegularity.lean`).
* **Viète's product** (`FunctionSpaces/Wavelets/Daubechies/SymbolProduct.lean`):
  `∏_{j ≥ 0} cos(x/2^(j+1)) = sinc x` (`Daubechies.tprod_cos`), with `|cos y - 1| ≤ y²/2`
  (`Daubechies.norm_cos_sub_one_le`) and the two-sided bound `|sinc x| ≤ 1/|x|`
  (`Daubechies.abs_sinc_le_inv_abs`, `SymbolDecay.lean`); Mathlib has Wallis's product and the
  one-sided `Real.sinc_le_inv_abs`.
* **Poisson summation with vanishing coefficients**
  (`FunctionSpaces/Wavelets/Daubechies/ScalingMoments.lean`):
  the periodisation `∑_n f(x + n)` of a continuous `f` vanishing outside a bounded interval, with
  `𝓕 f(n) = 0` for `n ≠ 0`, is the constant `∫ f` (`Real.tsum_comp_add_int_eq_integral`).
* **Sums over overlapping sets and shifts in `ℓ_q(ℤ)`**
  (`FunctionSpaces/Wavelets/Daubechies/Expansion.lean`):
  if every point lies in at most `M` of the sets `I_i`, then `∑_i ∫_{I_i} F ≤ M ∫ F`
  (`MeasureTheory.tsum_setLIntegral_le_mul_lintegral`); `ℓ_q(ℤ)` norms are invariant under
  shifts (`ENNReal.lqNorm_comp_add_int`).
* **Derivatives of exponential sums in a real variable**
  (`FunctionSpaces/Wavelets/Daubechies/FilterIdentities.lean`):
  `(d/dt)^l ∑_i a_i e^(b_i t) = ∑_i a_i b_i^l e^(b_i t)` for `t ∈ ℝ`
  (`Daubechies.iteratedDeriv_sum_mul_cexp`); Mathlib has these derivatives for a complex variable.
* **Distributions and Schwartz functions** (`FunctionSpaces/Rd/WeakDerivatives.lean`):
  directional derivatives commute on Schwartz functions and on test functions
  (`SchwartzMap.lineDerivOp_comm`, `TestFunction.lineDerivOp_comm`), and a directional derivative
  commutes with every iterated one as soon as two of them commute
  (`LineDeriv.lineDerivOp_iteratedLineDerivOp_comm_of`); the transpose formulas
  `∂^v T(φ) = (-1)^k T(∂^v φ)` for distributions and tempered distributions
  (`Distribution.iteratedLineDerivOp_apply_apply`,
  `TemperedDistribution.iteratedLineDerivOp_apply_apply`) and the iterated derivative of a
  Schwartz function as a tempered distribution
  (`TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq`); the cut-offs
  `χ(x/(n+1)) u(x)` of a Schwartz function converge to it in the Schwartz space
  (`Rd.tendsto_cutoffMul`), so tempered distributions are determined by test functions
  (`Rd.eq_zero_of_testSchwartz`).
* **The convolution theorem on `L_2`** (`FunctionSpaces/Rd/SobolevTwoLittlewoodPaley.lean`): for
  integrable `K` and `f ∈ L_2(V)`, `𝓕(K ⋆ f) = 𝓕K · 𝓕f` almost everywhere, with Plancherel's
  Fourier transform on `L_2` (`Rd.fourier_convLp`), from the multiplication formulas
  `∫ 𝓕u · g = ∫ u · 𝓕g` and `∫ 𝓕⁻u · g = ∫ u · 𝓕⁻g` for Schwartz `u` and integrable `g`
  (Mathlib's `VectorFourier.integral_fourierIntegral_smul_eq_flip`, in the `𝓕` form
  `Rd.integral_fourier_smul_eq_of_integrable`, `Rd.integral_fourierInv_smul_eq_of_integrable`;
  Mathlib's `SchwartzMap.integral_fourier_smul_eq` and `SchwartzMap.integral_fourierInv_smul_eq`
  are the forms for two Schwartz functions).
  Mathlib has the convolution theorem for integrable functions
  (`Real.fourier_bilin_convolution_eq`) and for Schwartz functions.
* **Temperate weights times `L_p` functions** (`FunctionSpaces/Rd/SobolevTwoLittlewoodPaley.lean`):
  if `w` has temperate growth, `g ∈ L_p(V)` and `w g ∈ L_q(V)`, then the product of `w` with the
  tempered distribution of `g` is the tempered distribution of `w g`
  (`Rd.smulLeftCLM_toTemperedDistribution_eq`), and an identity `w G = H` of tempered
  distributions with `G ∈ L_p(V)`, `H ∈ L_q(V)` holds almost everywhere
  (`Rd.ae_eq_of_smulLeftCLM_eq`).
* **`H^1` by derivatives in `L_2`** (`FunctionSpaces/Rd/SobolevTwoLittlewoodPaley.lean`): for
  `f ∈ L_2(V)`, Mathlib's `TemperedDistribution.MemSobolev 1 2 f` holds iff every directional
  derivative `∂_v f` of the tempered distribution `f` is an `L_2` function
  (`Rd.memSobolev_one_iff` with `Rd.memSobolev_iff_tempered`); the derivatives along one
  orthonormal basis `(e_i)` suffice (`Rd.memSobolev_one_two_of_lineDerivOp_eq`), and
  `(2π)² ‖J_1 f‖_2² = (2π)² ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²`
  (`Rd.lintegral_besselWeight_one_sq_eq`, `Rd.enorm_besselPotential_one_sq_eq`). Mathlib has
  `∂_v : H^s → H^{s-1}` (`TemperedDistribution.MemSobolev.lineDerivOp`); the converse at `s = 1`
  is new, and these results belong next to it in `Mathlib/Analysis/Distribution/Sobolev.lean`.
* **The inverse Fourier transform on `L_1 ∩ L_2` and Rellich's theorem**
  (`FunctionSpaces/Rd/RellichCompactness.lean`): for an integrable `h ∈ L_2(V)`, Mathlib's
  `L_2` inverse Fourier transform of `h` is the pointwise inverse Fourier integral almost
  everywhere (`Rd.fourierInv_Lp_ae_eq_of_integrable`). Mathlib has the `L_1` inverse transform
  (`Real.Lp.fourierTransformInv`) and the `L_2` inverse transform, and identifies the two on
  Schwartz functions (`SchwartzMap.toLp_fourierInv_eq`); this lemma identifies them on
  `L_1 ∩ L_2`. For every bounded `Ω ⊆ V`, the restriction
  from Mathlib's `H^{1,2}(V, ℂ)` to `L_2(Ω)` is a compact operator
  (`Rd.isCompactOperator_restr_toL2`).
