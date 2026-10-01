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
public import ApproximationSpaces.Lift
public import ApproximationSpaces.Nikolskii
public import ApproximationSpaces.Jackson
public import ApproximationSpaces.KFunctional
public import ApproximationSpaces.Representation
public import ApproximationSpaces.Decompositions.Projection
public import ApproximationSpaces.Decompositions.Blocks
public import ApproximationSpaces.Decompositions.Synthesis
public import ApproximationSpaces.Decompositions.Atomic
public import ApproximationSpaces.Trace
public import ApproximationSpaces.Retract
public import ApproximationSpaces.Moduli

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
* `ApproximationSpaces.Lift`: lifting bounds (Bernstein and Nikolskii inequalities), dyadic
  near-best approximants and the telescoping construction; a lifting bound of exponent `β`
  gives `A^β_1 ↪ Y`.
* `ApproximationSpaces.Nikolskii`: the Nikolskii transfer theorem
  `A^s_q(X) ↪ B^{s-α}_q(Y)`.
* `ApproximationSpaces.Jackson`: Jackson's inequality, `ι(Y) ⊆ A^r_∞`, and smoothness spaces
  `ApproximationScheme.SmoothnessSpace` with `A^r_1 ⊆ Y ⊆ A^r_∞`.
* `ApproximationSpaces.KFunctional`: the Peetre K-functional and the real interpolation
  spaces `(X, Y)_{θ,q}`.
* `ApproximationSpaces.Representation`: the representation theorem `A^s_q = (X, Y)_{s/r,q}`
  under Jackson's and Bernstein's inequalities of order `r`.
* `ApproximationSpaces.Decompositions.Projection`: schemes with uniformly bounded projections
  and the characterisation of `A^s_q` by dyadic blocks.
* `ApproximationSpaces.Decompositions.Blocks`: the characterisation of `A^s_q` by block
  decompositions `f = ∑ g_k`, `g_k ∈ A (2^k)`.
* `ApproximationSpaces.Decompositions.Synthesis`: linear schemes and synthesis from blocks that
  are approximable at rate `σ`.
* `ApproximationSpaces.Decompositions.Atomic`: atomic systems, the sequence spaces `b^s_{p,q}`
  and the atomic characterisation of `A^s_q`.
* `ApproximationSpaces.Trace`: maps defined on approximants (traces), their extension to
  `A^β_1`, the transfer `A^s_q → B^{s-β}_q` and its surjectivity.
* `ApproximationSpaces.Retract`: approximation-preserving extensions and the equivalence of
  intrinsic and restriction quasi-norms.
* `ApproximationSpaces.Moduli`: moduli of smoothness compatible with a scheme (Jackson and
  inverse inequalities) and the coincidence of `A^s_q` with the classical space for `0 < s < θ`.
-/
