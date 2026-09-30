/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Scheme
public import ApproximationSpaces.Error
public import ApproximationSpaces.Instances.Span
public import ApproximationSpaces.Instances.NTerm
public import ApproximationSpaces.Sequences.Lq
public import ApproximationSpaces.Sequences.Dyadic
public import ApproximationSpaces.Sequences.Hardy
public import ApproximationSpaces.Norm
public import ApproximationSpaces.Dyadic
public import ApproximationSpaces.Space
public import ApproximationSpaces.Embedding
public import ApproximationSpaces.Transfer

/-!
# Approximation spaces

The abstract theory of approximation spaces in the sense of Pietsch (J. Approx. Theory 32,
1981).  An approximation scheme is an increasing sequence of sets `A 0 ⊆ A 1 ⊆ ⋯` in a real
normed space `X`, and `E_n(f) = dist(f, A n)` is the error of best approximation of `f`.
Nothing in this library mentions functions or measures.

## Layout

* `ApproximationSpaces.Scheme`: the structure `ApproximationScheme`, its elementary
  consequences, and the preimage and image of a scheme under a linear map.
* `ApproximationSpaces.Error`: the error `ApproximationScheme.approxError` and its calculus.
* `ApproximationSpaces.Instances.Span`: linear approximation from the first `n` elements of
  a sequence, `ApproximationScheme.ofSpan`.
* `ApproximationSpaces.Instances.NTerm`: nonlinear `n`-term approximation from a
  dictionary, `ApproximationScheme.nTerm`.
* `ApproximationSpaces.Sequences.Lq`: the `ℓ_q` norm `ENNReal.lqNorm` of a sequence in
  `ℝ≥0∞`, its monotonicity in `q`, and the dyadic weights `ENNReal.dyadicWeight`.
* `ApproximationSpaces.Sequences.Dyadic`: Cauchy condensation with power weights, which
  compares `∑ (n+1)^γ b n` with `∑ 2^(k(γ+1)) b (2^k)` for decreasing `b`.
* `ApproximationSpaces.Sequences.Hardy`: the countable Minkowski inequality and the two
  discrete Hardy inequalities.
* `ApproximationSpaces.Norm`: Pietsch's quasi-norm `ApproximationScheme.approxNorm` of
  `A^s_q` and membership `ApproximationScheme.MemApprox`.
* `ApproximationSpaces.Dyadic`: the equivalent dyadic quasi-norm
  `ApproximationScheme.approxNormDyadic`, the working norm of all later files.
* `ApproximationSpaces.Space`: the quasi-triangle inequality and `A^s_q` as a submodule,
  `ApproximationScheme.approxSpace`.
* `ApproximationSpaces.Embedding`: the embeddings `A^s_q ↪ A^t_r`.
* `ApproximationSpaces.Transfer`: functoriality under bounded linear maps.
-/
