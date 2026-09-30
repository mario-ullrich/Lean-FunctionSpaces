# Candidates for Mathlib

General results from this project that Mathlib lacks, grouped by topic, with the main
declarations.

* **Distance to an increasing family of sets** (`ApproximationSpaces/Error.lean`): for an
  increasing family `A n` of nonempty sets, `Metric.infDist f (A n)` tends to zero exactly
  for `f` in the closure of `⋃ n, A n` (`ApproximationScheme.tendsto_approxError_zero_iff`),
  and it does so as soon as it does along the subsequence `2 ^ k`
  (`ApproximationScheme.tendsto_approxError_zero_of_pow`). Stated here for approximation
  schemes; the proofs use only monotonicity and nonemptiness.
