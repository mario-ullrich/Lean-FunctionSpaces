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
public import FunctionSpaces.Sobolev.Embeddings
public import FunctionSpaces.Torus.Measure
public import FunctionSpaces.Torus.Scheme
public import FunctionSpaces.Torus.Nikolskii
public import FunctionSpaces.Spectral.Basic
public import FunctionSpaces.Torus.Sobolev
public import FunctionSpaces.Torus.Embeddings
public import FunctionSpaces.Spectral.Blocks
public import FunctionSpaces.Torus.Coefficients
public import FunctionSpaces.Wavelets.Filtration
public import FunctionSpaces.Classical.Translation
public import FunctionSpaces.Classical.Modulus
public import FunctionSpaces.Classical.BesovModuli
public import FunctionSpaces.Classical.SobolevDeriv
public import FunctionSpaces.Traces.Examples.Torus
public import FunctionSpaces.Atoms.Examples.Torus

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
* `FunctionSpaces.Sobolev.Embeddings`: Sobolev spaces as smoothness spaces for a scheme, the
  Sobolev embedding `W^s_p ↪ W^t_r` and the embedding into bounded continuous functions.
* `FunctionSpaces.Torus.Measure`: Mathlib's normalised Haar measure on the torus as a scoped
  instance, `open scoped TorusHaar`.
* `FunctionSpaces.Torus.Scheme`: trigonometric polynomials of degree `< n` and their scheme
  `Torus.trigScheme`.
* `FunctionSpaces.Torus.Nikolskii`: the Nikolskii inequality for trigonometric polynomials by
  the power trick, `Torus.trigScheme_hasNikolskii`.
* `FunctionSpaces.Spectral.Basic`: spectral schemes in a Hilbert space and their `L_2` Sobolev
  spaces, with Jackson and Bernstein inequalities from Parseval's identity.
* `FunctionSpaces.Torus.Sobolev`: the Fourier basis of `L_2(𝕋^d)` as a spectral scheme and
  the Sobolev spaces `H^s(𝕋^d)`.
* `FunctionSpaces.Torus.Embeddings`: the embedding theorems on the torus.
* `FunctionSpaces.Spectral.Blocks`: spectral schemes as projection schemes, the coefficient
  characterisation of their approximation spaces and `H^s = A^s_2`.
* `FunctionSpaces.Torus.Coefficients`: `B^s_{2,2}(𝕋^d) = H^s(𝕋^d)` and the Littlewood–Paley
  characterisation of `B^s_{2,q}(𝕋^d)`.
* `FunctionSpaces.Wavelets.Filtration`: conditional expectations as contractions on `L_p`,
  filtration schemes (the Haar system for the dyadic filtration) and the characterisation of
  their approximation spaces by martingale differences.
* `FunctionSpaces.Classical.Translation`: translations on `L_2(𝕋^d)` and their Fourier
  multipliers.
* `FunctionSpaces.Classical.Modulus`: the modulus of smoothness `ω(f, t)_2` and Jackson's
  theorem `E_n(f)_2 ≤ √d ω(f, 1/n)_2`.
* `FunctionSpaces.Classical.BesovModuli`: the classical Besov norm through the modulus and
  the coincidence theorem with `B^s_{2,q}(𝕋^d)` for `0 < s < 1`.
* `FunctionSpaces.Classical.SobolevDeriv`: weak derivatives on the torus through Fourier
  coefficients and `W^m_2(𝕋^d) = H^m(𝕋^d) = B^m_{2,2}(𝕋^d)`.
* `FunctionSpaces.Traces.Examples.Torus`: the trace on the face `{x_0 = 0}` of `𝕋^(n+1)`,
  `B^{s+1/p}_{p,q}(𝕋^(n+1)) → B^s_{p,q}(𝕋^n)`, bounded and onto.
* `FunctionSpaces.Atoms.Examples.Torus`: Lipschitz atoms on `𝕋^d` as an atomic system for the
  trigonometric scheme in `L_2`, and synthesis `b^s_{2,q} → B^s_{2,q}(𝕋^d)` for `0 < s < 1`.
-/
