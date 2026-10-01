/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces
public import FunctionSpaces.Lp.Inclusion
public import FunctionSpaces.Lp.BoundedContinuous
public import FunctionSpaces.Scheme
public import FunctionSpaces.Besov.Basic
public import FunctionSpaces.Besov.Trivial
public import FunctionSpaces.Lp.Interpolation
public import FunctionSpaces.Besov.Nikolskii
public import FunctionSpaces.Besov.Embeddings

/-!
# Function spaces

Besov and Sobolev spaces on a finite measure space, defined through approximation schemes of
bounded continuous functions, and their embedding theorems.  The library builds on
`ApproximationSpaces`.

## Layout

* `FunctionSpaces.Lp.Inclusion`: the bounded linear inclusion `L_r ↪ L_p` for `p ≤ r` and a
  finite measure, `MeasureTheory.Lp.inclusionOfExponentLe`.
* `FunctionSpaces.Lp.BoundedContinuous`: bounded continuous functions in `L_p`; for a measure
  charging open sets, `L_∞` restricted to them is the sup norm.
* `FunctionSpaces.Scheme`: schemes of functions `FunctionScheme` and their transport
  `FunctionScheme.toLp` to every `L_p(μ)`, compatible with the inclusions.
* `FunctionSpaces.Besov.Basic`: the Besov spaces `B^s_{p,q}(Ω, S) = A^s_q(L_p(μ), S)`.
* `FunctionSpaces.Besov.Trivial`: the embeddings that need no property of the scheme.
* `FunctionSpaces.Lp.Interpolation`: `‖f‖_r ≤ ‖f‖_∞^(1-p/r) ‖f‖_p^(p/r)`.
* `FunctionSpaces.Besov.Nikolskii`: the Nikolskii property of a scheme and the Nikolskii
  inequality `‖a‖_r ≲ n^(D(1/p-1/r)) ‖a‖_p` it implies.
* `FunctionSpaces.Besov.Embeddings`: the Besov embeddings into `B^{s-α}_{r,q}`, `L_∞` and
  bounded continuous functions.
-/
