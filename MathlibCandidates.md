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
  `ℝ≥0∞` scalars, and splitting off the first term.
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
  `ENNReal.hardy_tail_le`, `ENNReal.hardy_sum_le`.
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
* **Fourier analysis on the torus** (`FunctionSpaces/Classical/Translation.lean`): the Fourier
  coefficients of a translate, `(τ_h f)^(k) = e_k(h) f̂(k)`
  (`Torus.mFourierCoeff_translate`), and `|∏ aᵢ - 1| ≤ ∑ |aᵢ - 1|` for unimodular `aᵢ`
  (`Torus.norm_prod_sub_one_le`). Mathlib's measure on `UnitAddCircle` is a local instance
  in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, so `mFourierBasis` cannot be used
  outside that file without re-declaring it (`FunctionSpaces/Torus/Measure.lean`); worth
  reporting upstream.
