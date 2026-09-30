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
