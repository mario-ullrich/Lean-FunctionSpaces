/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.MeasureSpaces.SchemeLpCouple
public import ApproximationSpaces.Space

/-!
# Besov spaces of a scheme of functions, `0 < p ≤ ∞`

Let `μ` be a finite measure on `Ω`, `S` a scheme of functions on `(Ω, μ)` (an approximation
scheme of essentially bounded functions), `0 < p ≤ ∞`, `s ∈ ℝ` and `0 < q ≤ ∞`. The **Besov
space** `B^s_{p,q}(Ω, S)` consists of the `f ∈ L_p(μ)` with finite Pietsch quasi-norm

`‖f‖_{B^s_{p,q}} = ‖((n + 1)^(s - 1/q) E_n(f)_p)_{n ∈ ℕ}‖_{ℓ_q}`,

where `E_n(f)_p = inf {‖f - a‖_p : a ∈ S_n}` is the error of best `L_p` approximation of `f`
from `S_n`. The error `E_n(f)_p` is the E-functional at `t = n` of the couple
`(‖·‖_p, complexity)` of `S` in `L_p` (`FunctionScheme.lpCouple`,
`FunctionScheme.eFunctional_lpCouple_natCast`), and the quasi-norm is Pietsch's form of that
couple (`InterpCouple.eNormPietsch`). The couple needs only the abelian group `Lp ℂ p μ`, so the
definition holds for every exponent, also for `0 < p < 1`, where `Lp ℂ p μ` is an abelian group
with the quasi-norm `‖·‖_p`.
On the torus with `S_n` the trigonometric polynomials of degree `< n`, for `1 ≤ p < ∞`,
`s > 0` and `1 ≤ q ≤ ∞` these are the classical periodic Besov spaces
(`Torus.memBesov_iff_modNorm_lt_top_lp`); for other schemes (splines, wavelets, eigenfunctions)
one obtains the Besov spaces adapted to the scheme. Whether they agree with a definition through
moduli of smoothness is a separate theorem for each scheme (Jackson and Bernstein inequalities).

* **The dyadic norm and the linear structure.** For `s ≥ 0` and `0 < q ≤ ∞`, `f ∈ B^s_{p,q}`
  iff the dyadic norm `‖f‖_p + ‖(2^(ks) E_{2^k}(f)_p)_k‖_{ℓ_q}` of the couple is finite
  (`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`,
  `FunctionScheme.MemBesov.of_eNormDyadic_lt_top`); if moreover `s > 0` or `q = ∞`, the Besov
  space is the space `E_{s,q}` of the couple (`FunctionScheme.memBesov_iff_memEMethod`). The
  quasi-norm vanishes at `0` and is homogeneous, `‖c f‖_{B^s_{p,q}} = |c| ‖f‖_{B^s_{p,q}}`
  (`FunctionScheme.besovNorm_zero`, `FunctionScheme.besovNorm_smul_le`,
  `FunctionScheme.besovNorm_smul`). The Besov space contains `0`, is closed under sums by the
  quasi-triangle inequality of the dyadic norm and under real multiples
  (`FunctionScheme.memBesov_zero`, `FunctionScheme.MemBesov.add`, `FunctionScheme.MemBesov.smul`),
  so it is a real subspace of `L_p(μ)` (`FunctionScheme.besovSpace`,
  `FunctionScheme.mem_besovSpace`).
* **The normed case.** For `1 ≤ p ≤ ∞` the couple of `S` in `L_p` is the complexity couple of
  the scheme `S^(p) = S.toLp p` in the normed space `L_p(μ)`, so the Besov space is the
  approximation space `A^s_q(L_p(μ), S^(p))` with its quasi-norm
  (`FunctionScheme.besovNorm_eq_approxNorm`, `FunctionScheme.memBesov_iff_memApprox`), and every
  result of `ApproximationSpaces` applies to it.

For an approximation scheme `T` of bounded continuous functions, the **uniform Besov space**
`FunctionScheme.besovSpaceSup T` is the approximation space of `T` in the sup norm.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace FunctionScheme

/-- The **uniform Besov space** of an approximation scheme `T` of bounded continuous functions,
for `s ≥ 0` and `0 < q ≤ ∞`: the approximation space of `T` in the sup norm, a space of bounded
continuous functions. -/
noncomputable abbrev besovSpaceSup {Ω : Type*} [TopologicalSpace Ω]
    (T : ApproximationScheme (Ω →ᵇ ℂ)) (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq0 : q ≠ 0) :
    Submodule ℝ (Ω →ᵇ ℂ) :=
  T.approxSpace s q hs hq0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (S : FunctionScheme μ) (p : ℝ≥0∞)

/-- The **Besov quasi-norm** `‖f‖_{B^s_{p,q}} = ‖((n + 1)^(s - 1/q) E_n(f)_p)_n‖_{ℓ_q}` of
`f ∈ L_p(μ)`, for every exponent `p`: Pietsch's form of the couple of `S` in `L_p`, whose
E-functional at `t = n` is the error `E_n(f)_p` of best approximation from `S_n` in `L_p`. It is
meant for `0 < p ≤ ∞` and `0 < q ≤ ∞`: at `q = 0` it vanishes by the convention
`lqNorm 0 = 0`, and at `p = 0` since `eLpNorm f 0 μ = 0`. -/
noncomputable abbrev besovNorm (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : ℝ≥0∞ :=
  (S.lpCouple p).eNormPietsch s q f

/-- `f` belongs to the **Besov space** `B^s_{p,q}(Ω, S)`: its Besov quasi-norm is finite. Meant
for `0 < p ≤ ∞` and `0 < q ≤ ∞`; at `p = 0` or `q = 0` every `f` belongs to it
(`FunctionScheme.besovNorm`). -/
abbrev MemBesov (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) : Prop := S.besovNorm p s q f < ∞

variable {S p}

/-- **The Besov space through the dyadic norm**: for `s ≥ 0` and `0 < q ≤ ∞`, `f ∈ B^s_{p,q}` iff
`‖f‖_p + ‖(2^(ks) E_{2^k}(f)_p)_k‖_{ℓ_q} < ∞`, the dyadic norm of the couple of `S` in `L_p`.
Only `0` has complexity `0`, so Pietsch's form and the dyadic norm are finite together
(`InterpCouple.eNormPietsch_lt_top_iff`). -/
theorem memBesov_iff_eNormDyadic_lt_top {s : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hs : 0 ≤ s)
    {f : Lp ℂ p μ} : S.MemBesov p s q f ↔ (S.lpCouple p).eNormDyadic s q f < ∞ :=
  InterpCouple.eNormPietsch_lt_top_iff (lpCouple_norm1_zero S p)
    (fun _ hb => eq_zero_of_lpCouple_norm1_lt_one hb) hq0 hs

/-- **A finite dyadic norm gives membership in the Besov space**, for `s ≥ 0` and every fine
index `q`: if `‖f‖_p + ‖(2^(ks) E_{2^k}(f)_p)_k‖_{ℓ_q} < ∞`, then `f ∈ B^s_{p,q}`, since
Pietsch's form is at most `C_q 2^s` times the dyadic norm
(`InterpCouple.eNormPietsch_le_eNormDyadic`). No hypothesis on `q` is needed in this direction. -/
theorem MemBesov.of_eNormDyadic_lt_top {s : ℝ} {q : ℝ≥0∞} (hs : 0 ≤ s) {f : Lp ℂ p μ}
    (h : (S.lpCouple p).eNormDyadic s q f < ∞) : S.MemBesov p s q f :=
  (InterpCouple.eNormPietsch_le_eNormDyadic (lpCouple_norm1_zero S p) hs f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top q)
      (ENNReal.two_rpow_ne_top s).lt_top) h)

/-- **The Besov space is the space `E_{s,q}` of the couple of `S` in `L_p`**: for `s ≥ 0`,
`0 < q ≤ ∞` and `s > 0` or `q = ∞`, `f ∈ B^s_{p,q}` iff `f ∈ E_{s,q}`; both are described by
the dyadic norm (`FunctionScheme.memBesov_iff_eNormDyadic_lt_top`,
`InterpCouple.memEMethod_iff_eNormDyadic_lt_top`). -/
theorem memBesov_iff_memEMethod {s : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hs : 0 ≤ s)
    (hsq : 0 < s ∨ q = ∞) {f : Lp ℂ p μ} :
    S.MemBesov p s q f ↔ (S.lpCouple p).MemEMethod s q f :=
  (memBesov_iff_eNormDyadic_lt_top hq0 hs).trans
    (InterpCouple.memEMethod_iff_eNormDyadic_lt_top (lpCouple_norm1_zero S p)
      (fun _ hb => eq_zero_of_lpCouple_norm1_lt_one hb) hs hsq hq0).symm

variable (S p) in
/-- **The Besov quasi-norm of `0` is `0`**, for every `s` and `q`: every error `E_n(0)_p`
vanishes, since `0` is an approximant of every level (`InterpCouple.eNormPietsch_zero`). -/
@[simp]
theorem besovNorm_zero (s : ℝ) (q : ℝ≥0∞) : S.besovNorm p s q 0 = 0 :=
  InterpCouple.eNormPietsch_zero (isQuasiNormed_lpCouple S p).norm0_zero
    (lpCouple_norm1_zero S p) s q

variable (S p) in
/-- The function `0` lies in every Besov space: its quasi-norm is `0`. -/
theorem memBesov_zero (s : ℝ) (q : ℝ≥0∞) : S.MemBesov p s q 0 :=
  (besovNorm_zero S p s q).trans_lt ENNReal.zero_lt_top

/-- **The Besov space is closed under sums**: for `s ≥ 0` and `0 < q ≤ ∞`, `f, g ∈ B^s_{p,q}`
imply `f + g ∈ B^s_{p,q}`, by the quasi-triangle inequality of the dyadic norm of the couple of
`S` in `L_p` (`InterpCouple.eNormDyadic_add_le`), whose constant is finite. -/
theorem MemBesov.add {s : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hs : 0 ≤ s) {f g : Lp ℂ p μ}
    (hf : S.MemBesov p s q f) (hg : S.MemBesov p s q g) : S.MemBesov p s q (f + g) := by
  rw [memBesov_iff_eNormDyadic_lt_top hq0 hs] at hf hg ⊢
  exact (InterpCouple.eNormDyadic_add_le (isQuasiNormed_lpCouple S p) lpCouple_norm1_add_le s q
    f g).trans_lt (ENNReal.mul_lt_top
      (InterpCouple.eAddConst_ne_top (ENNReal.LpAddConst_lt_top p).ne s q).lt_top
      (ENNReal.add_lt_top.2 ⟨hf, hg⟩))

/-- **Multiples in the Besov quasi-norm**: `‖c f‖_{B^s_{p,q}} ≤ |c| ‖f‖_{B^s_{p,q}}` for every
real `c`, since `‖c a‖_p = |c| ‖a‖_p` and multiples of approximants are approximants
(`InterpCouple.eNormPietsch_map_le` for `f ↦ c f`). -/
theorem besovNorm_smul_le {s : ℝ} {q : ℝ≥0∞} (c : ℝ) (f : Lp ℂ p μ) :
    S.besovNorm p s q (c • f) ≤ ‖c‖ₑ * S.besovNorm p s q f :=
  InterpCouple.eNormPietsch_map_le (DistribSMul.toAddMonoidHom (Lp ℂ p μ) c)
    (lpCouple_norm1_zero S p) eNorm_ne_top (fun a => (lpCouple_norm0_smul c a).le)
    (fun a => lpCouple_norm1_smul_le c a) s q f

/-- **Homogeneity of the Besov quasi-norm**: `‖c f‖_{B^s_{p,q}} = |c| ‖f‖_{B^s_{p,q}}` for every
real `c`. For `c ≠ 0` the bound `FunctionScheme.besovNorm_smul_le` for `c⁻¹` applied to `c f`
gives the reverse inequality; for `c = 0` both sides are `0` (`FunctionScheme.besovNorm_zero`). -/
theorem besovNorm_smul {s : ℝ} {q : ℝ≥0∞} (c : ℝ) (f : Lp ℂ p μ) :
    S.besovNorm p s q (c • f) = ‖c‖ₑ * S.besovNorm p s q f := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, besovNorm_zero, eNorm_zero, zero_mul]
  refine le_antisymm (besovNorm_smul_le c f) ?_
  have h := besovNorm_smul_le (S := S) (s := s) (q := q) c⁻¹ (c • f)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  calc ‖c‖ₑ * S.besovNorm p s q f ≤ ‖c‖ₑ * (‖c⁻¹‖ₑ * S.besovNorm p s q (c • f)) := by gcongr
    _ = S.besovNorm p s q (c • f) := by
      rw [← mul_assoc, ← eNorm_mul, mul_inv_cancel₀ hc, eNorm_one, one_mul]

/-- **The Besov space is closed under real multiples**: `f ∈ B^s_{p,q}` implies
`c f ∈ B^s_{p,q}` for every real `c`. -/
theorem MemBesov.smul {s : ℝ} {q : ℝ≥0∞} {f : Lp ℂ p μ} (hf : S.MemBesov p s q f) (c : ℝ) :
    S.MemBesov p s q (c • f) :=
  (besovNorm_smul_le c f).trans_lt (ENNReal.mul_lt_top eNorm_lt_top hf)

variable (S p) in
/-- The **Besov space** `B^s_{p,q}(Ω, S)` as a real subspace of `L_p(μ)`, for every exponent `p`,
`s ≥ 0` and `0 < q ≤ ∞`. -/
def besovSpace (s : ℝ) (q : ℝ≥0∞) (hs : 0 ≤ s) (hq0 : q ≠ 0) : Submodule ℝ (Lp ℂ p μ) where
  carrier := {f | S.MemBesov p s q f}
  zero_mem' := memBesov_zero S p s q
  add_mem' hf hg := MemBesov.add hq0 hs hf hg
  smul_mem' c _ hf := MemBesov.smul hf c

/-- **Membership in the Besov space as a subspace**: for `s ≥ 0` and `0 < q ≤ ∞`, `f` lies in the
subspace `B^s_{p,q}(Ω, S)` of `L_p(μ)` iff `S.MemBesov p s q f`, that is, iff
`‖f‖_{B^s_{p,q}} < ∞`. -/
@[simp]
theorem mem_besovSpace {s : ℝ} {q : ℝ≥0∞} {hs : 0 ≤ s} {hq0 : q ≠ 0} {f : Lp ℂ p μ} :
    f ∈ S.besovSpace p s q hs hq0 ↔ S.MemBesov p s q f := Iff.rfl

/-- **For `p ≥ 1` the Besov quasi-norm is Pietsch's quasi-norm of the approximation space**:
`‖f‖_{B^s_{p,q}} = ‖f‖_{A^s_q(L_p(μ), S^(p))}` for `1 ≤ p ≤ ∞`, where `S^(p) = S.toLp p` is the
scheme `S` sent into the normed space `L_p(μ)`. The couple of `S` in `L_p` is the complexity
couple of `S^(p)` (`FunctionScheme.lpCouple_eq_complexityCouple`), whose Pietsch form is
Pietsch's quasi-norm (`ApproximationScheme.eNormPietsch_complexityCouple`). -/
theorem besovNorm_eq_approxNorm [Fact (1 ≤ p)] (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) :
    S.besovNorm p s q f = (S.toLp p).approxNorm s q f := by
  rw [besovNorm, lpCouple_eq_complexityCouple, ApproximationScheme.eNormPietsch_complexityCouple]

/-- **For `p ≥ 1` the Besov space is the approximation space**: for `1 ≤ p ≤ ∞`,
`f ∈ B^s_{p,q}(Ω, S)` iff `f ∈ A^s_q(L_p(μ), S^(p))`, where `S^(p) = S.toLp p` is the scheme `S`
sent into the normed space `L_p(μ)`. -/
theorem memBesov_iff_memApprox [Fact (1 ≤ p)] {s : ℝ} {q : ℝ≥0∞} {f : Lp ℂ p μ} :
    S.MemBesov p s q f ↔ (S.toLp p).MemApprox s q f := by
  rw [MemBesov, besovNorm_eq_approxNorm]
  rfl

end FunctionScheme
