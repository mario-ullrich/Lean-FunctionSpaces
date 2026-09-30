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
-/
