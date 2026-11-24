/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.Scheme
public import ApproximationSpaces.Space

/-!
# Besov spaces as approximation spaces

Let `S` be a scheme of functions on `Ω`, `μ` a finite measure and `1 ≤ p ≤ ∞`.  The **Besov
space** `B^s_{p,q}(Ω, S)` is the approximation space of `L_p(μ)` for the scheme `S`:

`B^s_{p,q} = A^s_q(L_p(μ), S^(p))`,   `‖f‖_{B^s_{p,q}} = ‖(n^(s-1/q) E_{n-1}(f)_p)_n‖_{ℓ_q}`,

where `E_n(f)_p` is the error of best `L_p` approximation of `f` from `S n`, the
`ApproximationScheme.approxError` of the transported scheme `S^(p) = S.toLp μ p`.  On the torus
with `S n` the trigonometric polynomials of degree `< n` these are the classical periodic Besov
spaces; for other schemes (splines, wavelets, eigenfunctions) one obtains the Besov spaces
adapted to the scheme.  Whether they agree with a definition through moduli of smoothness is
a separate theorem for each scheme (Jackson and Bernstein inequalities).

The names in this file are abbreviations for the general notions of `ApproximationSpaces`, so
every result proved there applies to Besov spaces directly.  Two identities state this link,
`FunctionScheme.besovNorm_eq_approxNorm` and `FunctionScheme.memBesov_iff_memApprox`, and
`FunctionScheme.mem_besovSpace` describes membership in the subspace `FunctionScheme.besovSpace`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace FunctionScheme

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (S : FunctionScheme Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **Besov quasi-norm** `‖f‖_{B^s_{p,q}}`, Pietsch's quasi-norm of `A^s_q(L_p(μ), S^(p))`
for the scheme `S^(p) = S.toLp μ p` in `L_p(μ)`. -/
noncomputable abbrev besovNorm (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : ℝ≥0∞ :=
  (S.toLp μ p).approxNorm s q f

/-- `f` belongs to the **Besov space** `B^s_{p,q}(Ω, S)`. -/
abbrev MemBesov (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : Prop := (S.toLp μ p).MemApprox s q f

/-- The **Besov space** `B^s_{p,q}(Ω, S)` as a real subspace of `L_p(μ)`, for `s ≥ 0`,
`1 ≤ q ≤ ∞`. -/
noncomputable abbrev besovSpace (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq : 1 ≤ q) :
    Submodule ℝ (Lp ℂ p μ) :=
  (S.toLp μ p).approxSpace s q hs hq

/-- The **uniform Besov space**: the approximation space of `S` in the sup norm, a space of
bounded continuous functions. -/
noncomputable abbrev besovSpaceSup (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq : 1 ≤ q) :
    Submodule ℝ (Ω →ᵇ ℂ) :=
  S.approxSpace s q hs hq

variable {S μ p}

/-- **The Besov quasi-norm is Pietsch's quasi-norm of the approximation space**:
`‖f‖_{B^s_{p,q}} = ‖f‖_{A^s_q(L_p(μ), S^(p))}` for `1 ≤ p ≤ ∞`, where `S^(p) = S.toLp μ p` is
the scheme `S` sent into `L_p(μ)`. -/
theorem besovNorm_eq_approxNorm (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) :
    S.besovNorm μ p s q f = (S.toLp μ p).approxNorm s q f := rfl

/-- **The Besov space is the approximation space**: for `1 ≤ p ≤ ∞`, `f ∈ B^s_{p,q}(Ω, S)` iff
`f ∈ A^s_q(L_p(μ), S^(p))`, where `S^(p) = S.toLp μ p` is the scheme `S` sent into `L_p(μ)`. -/
theorem memBesov_iff_memApprox {s : ℝ} {q : ℝ≥0∞} {f : Lp ℂ p μ} :
    S.MemBesov μ p s q f ↔ (S.toLp μ p).MemApprox s q f := Iff.rfl

/-- **Membership in the Besov space as a subspace**: for `1 ≤ p ≤ ∞`, `s ≥ 0` and `1 ≤ q ≤ ∞`,
`f` lies in the subspace `B^s_{p,q}(Ω, S)` of `L_p(μ)` iff `S.MemBesov μ p s q f`, that is, iff
`‖f‖_{B^s_{p,q}} < ∞`. -/
@[simp]
theorem mem_besovSpace {s : ℝ} {q : ℝ≥0∞} {hs : 0 ≤ s} {hq : 1 ≤ q} {f : Lp ℂ p μ} :
    f ∈ S.besovSpace μ p s q hs hq ↔ S.MemBesov μ p s q f := Iff.rfl

end FunctionScheme
