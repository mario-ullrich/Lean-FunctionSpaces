# Candidates for Mathlib

General results from this project that Mathlib lacks, grouped by topic, with the main
declarations.

* **`ℓ_q` norms of families in `ℝ≥0∞`** (`ApproximationSpaces/Sequences/Lq.lean`), as the
  `L_q` norm for the counting measure on any countable index set: the norm bound
  `‖a‖_r ≤ ‖a‖_q` for `0 < q ≤ r` behind `lp.monotone` (`ENNReal.lqNorm_le_lqNorm_of_le`),
  homogeneity for `ℝ≥0∞` scalars, the quasi-triangle inequality
  `‖a + b‖_q ≤ LpAddConst q (‖a‖_q + ‖b‖_q)` for every `q`, the case of the counting measure of
  Mathlib's `eLpNorm_add_le'` (`ENNReal.lqNorm_add_le'`), the finite-index forms
  (`ENNReal.lqNorm_eq_sum`, `ENNReal.lqNorm_le_card_rpow_mul`, `ENNReal.lqNorm_prod_rpow`), the
  iterated norm `‖(‖a_k‖_q)_k‖_q^q = ∑_k ∑_n a_{k,n}^q` (`ENNReal.lqNorm_lqNorm_rpow`), and,
  on `ℕ`, splitting off the first terms (`ENNReal.lqNorm_le_head_add_shift`,
  `ENNReal.lqNorm_le_head_add_shift'`, `ENNReal.lqNorm_le_sum_range_add_shift`); reindexing along
  bijections and injections (`ENNReal.lqNorm_comp_equiv`, `ENNReal.lqNorm_extend_zero`,
  `ENNReal.lqNorm_comp_le_of_injective`); Fatou's lemma for termwise limits, `a_m → b` termwise
  and `‖a_m‖_q ≤ d_m → D` give `‖b‖_q ≤ D` (`ENNReal.lqNorm_le_of_tendsto`).
* **Subadditivity of `x ↦ x^p` for series** (`ApproximationSpaces/Sequences/Lq.lean`): for
  `0 < p ≤ 1` and every family `f` in `[0, ∞]`, `(∑_i f_i)^p ≤ ∑_i f_i^p`
  (`ENNReal.rpow_tsum_le_tsum_rpow`), from the finite form of Mathlib PR #44783 by the supremum
  over partial sums; neither Mathlib nor the PR has the series form. Its consequence, the
  decrease of `(∑_i f_i^p)^(1/p)` in `p` for series over any index set
  (`ENNReal.rpow_tsum_rpow_le`), is the norm bound behind `lp.monotone` without a countability
  assumption.
* **The constant of the quasi-triangle inequality** (`ApproximationSpaces/Sequences/Lq.lean`):
  `1 ≤ LpAddConst q` for every `q` (`ENNReal.one_le_LpAddConst`), a companion of Mathlib's
  `ENNReal.LpAddConst_lt_top` and `ENNReal.LpAddConst_ne_zero`. The Bonn project
  *MultilinearInterpolation* has the same lemma under the same name, and Carleson uses one, so an
  upstreaming can be coordinated.
* **`L_q` norms of functions bounded on pieces** (`ApproximationSpaces/Sequences/Lq.lean`): on any
  measure space, for disjoint measurable pieces of equal measure `c` and `G` between step
  values `a_n` on the pieces, the comparisons `∫ G ≤ c ∑ a_n`, `c ∑ a_n ≤ ∫ G` and their `L_q`
  forms with `c^(1/q) ‖a‖_{ℓ_q}` (`MeasureTheory.lintegral_le_of_le_on_pieces`,
  `MeasureTheory.le_lintegral_of_le_on_pieces`, `MeasureTheory.eLpNorm_le_of_le_on_pieces`,
  `MeasureTheory.le_eLpNorm_of_le_on_pieces`).
* **The K-method** (`ApproximationSpaces/Interpolation/KMethod.lean`): the change of scale
  `K(c t, f) ≤ max(1, c) K(t, f)` (`ApproximationScheme.inclKFunctional_mul_le`); for every
  increasing `φ` and `θ ≥ 0`, the comparison of the functional `Φ_{θ,q}(φ)` with its discrete
  version on the grid `2^(nρ)`, `n ∈ ℤ`
  (`ApproximationScheme.phiFunctional_le_lqNorm_discretePhiSeq`,
  `ApproximationScheme.lqNorm_discretePhiSeq_le_phiFunctional`), which for `ρ = 1` gives the two
  inequalities of `discreteKMethod_equiv_kmethod` in the Bonn project *MultilinearInterpolation*;
  and, for the couple given by a bounded linear map, the analogue of that equivalence with the
  grid on `ℕ` and the term `‖f‖` (`ApproximationScheme.inclKMethodNorm_le_inclInterpNorm`,
  `ApproximationScheme.inclInterpNorm_le_inclKMethodNorm`,
  `ApproximationScheme.memInterp_iff_memInclKMethod`). Upstreamed, these would take the shape of
  the definitions `kMethod` and `discreteKMethod` of that project.
* **Couples and their K-method** (`ApproximationSpaces/Interpolation/Couple.lean`): couples
  `InterpCouple` of two functions `U → [0, ∞]` on an abelian group with the axioms
  `InterpCouple.IsQuasiNormed`, the quasi-triangle inequality of the K-functional
  (`InterpCouple.kFunctional_add_le`), the K-functional of the swapped couple
  (`InterpCouple.kFunctional_swap`), the equivalence of the continuous and the discrete K-method
  (`InterpCouple.memKMethod_iff_discreteKMethodNorm_lt_top`), the reflection `θ ↦ 1 - θ`
  (`InterpCouple.discreteKMethodNorm_swap`) and the interpolation space as a submodule
  (`InterpCouple.kMethodSpace`). They have the shape of `kNorm`, `kMethod` and `discreteKMethod`
  of the Bonn project *MultilinearInterpolation*; coordinate with
  lua-vr/MultilinearInterpolation.
* **The interpolation property of the K-method**
  (`ApproximationSpaces/Interpolation/Property.lean`): the invariance of `dt/t` under dilations
  (`ApproximationScheme.measurePreserving_mul_left_kMethodMeasure`), the dilation formula
  `Φ_{θ,q}(φ(c ·)) = c^θ Φ_{θ,q}(φ)` (`ApproximationScheme.phiFunctional_comp_mul`), the
  K-functional under a map (`InterpCouple.kFunctional_map_le`) and exactness of exponent `θ`
  (`InterpCouple.kMethodNorm_map_le`), the theorem behind the commented-out definition
  `IsOfExponent` of *MultilinearInterpolation*; coordinate with lua-vr/MultilinearInterpolation.
* **The reiteration theorem** (`ApproximationSpaces/Interpolation/Reiteration.lean`): the
  inclusion for couples of class `C_K` (`InterpCouple.discreteKMethodNorm_le_of_kFunctional_le`),
  the upper bound of Holmstedt's formula in discrete form with `ℓ₁` sums
  (`InterpCouple.kFunctional_kCouple_le`) and the reiteration theorem for quasi-normed couples
  (`InterpCouple.memKMethod_kCouple_iff`, `InterpCouple.memKMethod_kMethodCouple_iff`), with the
  geometric convolutions on `ℤ` (`ENNReal.lqNorm_tsum_geom_sub_le`,
  `ENNReal.lqNorm_tsum_geom_add_le`); this complements *MultilinearInterpolation*, which has
  the K-method, parts of the J-method and Janson's lemma, and no reiteration theorem; coordinate
  with lua-vr/MultilinearInterpolation.
* **Monotone convergence and countable Minkowski for `eLpNorm`**: on any measure space,
  `‖sup_b F_b‖_p = sup_b ‖F_b‖_p` for directed countable families of a.e. measurable `F_b`
  (`MeasureTheory.eLpNorm_iSup_of_directed`) and `‖∑_i g_i‖_p ≤ ∑_i ‖g_i‖_p` for `1 ≤ p ≤ ∞` and
  countably many `g_i : α → [0, ∞]` (`MeasureTheory.eLpNorm_tsum_le`), both in
  `ApproximationSpaces/Sequences/Lq.lean`; the counting-measure versions `ENNReal.lqNorm_iSup`
  and `ENNReal.lqNorm_tsum_le` are in `ApproximationSpaces/Sequences/Hardy.lean`. Mathlib has only
  the finite version `eLpNorm_sum_le`.
* **Subadditivity of `‖·‖_p^ρ`, `ρ = min(1, p)`, and Fatou's lemma for telescoping sums**: on
  any measure space and for all functions with values in an `ESeminormedAddMonoid` with
  continuous addition, at the generality of Mathlib's lemmas (a normed group, or `[0, ∞]`),
  `‖f + g‖_p^p ≤ ‖f‖_p^p + ‖g‖_p^p` for `0 < p ≤ 1`
  (`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`, in `ApproximationSpaces/Sequences/Lq.lean`),
  from Mathlib's `inhmgELpNorm_add_le` and `inhmgELpNorm_eq_eLpNorm_pow`; for every `0 < p ≤ ∞` with
  `ρ = min(1, p)`, `‖f + g‖_p^ρ ≤ ‖f‖_p^ρ + ‖g‖_p^ρ` (`MeasureTheory.eLpNorm_add_rpow_min_le`),
  since `inhmgELpNorm f p μ = ‖f‖_p^ρ` (`MeasureTheory.inhmgELpNorm_eq_eLpNorm_rpow_min`); and
  for elements of `Lp E p μ`, whose `NormedAddCommGroup` instance needs `Fact (1 ≤ p)`
  (`MeasureTheory.Lp.enorm_add_rpow_le_of_le_one`, beside `‖0‖ₑ = 0` and `‖-f‖ₑ = ‖f‖ₑ` for
  every `p`, `MeasureTheory.Lp.enorm_zero` and `MeasureTheory.Lp.enorm_neg`, which Mathlib states
  for `‖·‖` and `‖·‖₊`), these in `FunctionSpaces/Analysis/Lp/QuasiNorm.lean`. Mathlib states
  the power form only for `inhmgELpNorm`; for `eLpNorm` it has the bounds with the constant
  `2^(1/p - 1)` (`eLpNorm'_add_le_of_le_one`, `eLpNorm_add_le'`). With it, Fatou's lemma for
  telescoping sums, in `FunctionSpaces/Analysis/Lp/QuasiNorm.lean`: if `u_n → g` in measure,
  with a.e. strongly measurable `u_n` with values in a seminormed group, then for every
  `0 < r ≤ ∞` with `ρ = min(1, r)`, `‖g - u_k‖_r^ρ ≤ ∑_{i ≥ 0} ‖u_{k+i+1} - u_{k+i}‖_r^ρ`
  (`MeasureTheory.eLpNorm_sub_rpow_min_le_tsum`, from its finite version
  `MeasureTheory.eLpNorm_sub_rpow_min_le_sum`, Mathlib's `eLpNorm_le_of_tendstoInMeasure` and the
  invariance of convergence in measure under subtracting a function,
  `MeasureTheory.TendstoInMeasure.sub_right`). Its case `ρ = r` is
  `‖g - u_k‖_r^r ≤ ∑_{i ≥ 0} ‖u_{k+i+1} - u_{k+i}‖_r^r` for `0 < r ≤ 1`
  (`MeasureTheory.eLpNorm_sub_rpow_le_tsum`, finite version
  `MeasureTheory.eLpNorm_sub_rpow_le_sum`), and its case `ρ = 1` the triangle inequality
  `‖g - u_k‖_r ≤ ∑_{i ≥ 0} ‖u_{k+i+1} - u_{k+i}‖_r` for `1 ≤ r` and every limit in measure, of
  finite or infinite quasi-norm (`MeasureTheory.eLpNorm_sub_le_tsum`).
* **Series in `L_p` for every `0 < p ≤ ∞` and finiteness almost everywhere**
  (`FunctionSpaces/Analysis/Lp/QuasiNorm.lean`): for `0 < p ≤ 1` and countably many
  `g_i : α → [0, ∞]`, `‖∑_i g_i‖_p^p ≤ ∑_i ‖g_i‖_p^p`
  (`MeasureTheory.eLpNorm_tsum_rpow_le_of_le_one`), the series form of
  `MeasureTheory.eLpNorm_add_rpow_le_of_le_one`, and `‖∑_i g_i‖_p^ρ ≤ ∑_i ‖g_i‖_p^ρ` with
  `ρ = min(1, p)` for every `p ≠ 0` (`MeasureTheory.eLpNorm_tsum_rpow_min_le`); a function
  `F : α → [0, ∞]` with finite `eLpNorm F p μ`, `p ≠ 0`, is finite almost everywhere
  (`MeasureTheory.ae_lt_top_of_eLpNorm_ne_top`); and for every `p ≠ 0` and `ρ = min(1, p)`,
  `∑_i ‖g_i‖_p^ρ < ∞` gives `∑_i ‖g_i(x)‖ < ∞` almost everywhere
  (`MeasureTheory.summable_norm_of_tsum_eLpNorm_rpow_min_ne_top`), which extends Mathlib's
  `summable_norm_of_tsum_eLpNorm_ne_top` (`1 ≤ p`) below `1`.
* **The Ditzian–Prymak bootstrap** (`FunctionSpaces/Analysis/Lp/QuasiNorm.lean`): every
  function satisfies `‖f x‖ ≤ ‖f‖_∞` for almost every `x`, measurable or not
  (`MeasureTheory.ae_enorm_le_eLpNorm_top`; Mathlib states this bound for `eLpNormEssSup` only,
  `ae_le_eLpNormEssSup`); an almost everywhere bound `N < ∞` of `‖f‖` with `N ≤ M ‖f‖_{p₀}`
  gives `N ≤ M^(p₀/p) ‖f‖_p` for every `0 < p ≤ p₀ < ∞`
  (`MeasureTheory.le_rpow_mul_eLpNorm_of_ae_enorm_le`), and
  `‖f‖_∞ ≤ M ‖f‖_p` gives `‖f‖_r ≤ M^(1 - p/r) ‖f‖_p` for every `p ≤ r ≤ ∞`
  (`MeasureTheory.eLpNorm_le_of_eLpNorm_top_le`); Ditzian–Prymak 2016, Theorem 2.1.
* **Mixed norms `L_p(ℓ_q)` and `ℓ_q(L_p)`** (`FunctionSpaces/Analysis/Lp/MixedNorms.lean`):
  Minkowski's integral inequality for `ℓ_u`-valued functions,
  `‖(∫ g_i)_i‖_{ℓ_u} ≤ ∫ ‖(g_i(x))_i‖_{ℓ_u}` for `1 ≤ u ≤ ∞` (`MeasureTheory.lqNorm_lintegral_le`);
  `L_p(ℓ_p) = ℓ_p(L_p)` for `0 < p < ∞` (`MeasureTheory.eLpNorm_lqNorm_eq_lqNorm_eLpNorm`) and the
  comparisons for `p ≤ q` and `q ≤ p` (`MeasureTheory.lqNorm_eLpNorm_le_eLpNorm_lqNorm`,
  `MeasureTheory.eLpNorm_lqNorm_le_lqNorm_eLpNorm`); and the passage of pointwise bounds to limits,
  `u ≤ v + w_J` a.e. with `‖w_J‖_p → 0` gives `u ≤ v` a.e.
  (`MeasureTheory.ae_le_of_le_add_of_tendsto_eLpNorm`).
* **Weighted Cauchy condensation** (`ApproximationSpaces/Sequences/Dyadic.lean`): for a
  decreasing sequence and a power weight `(n + 1)^γ`, the comparison with the dyadic series
  in both directions (`ENNReal.tsum_pow_mul_le_dyadic`, `ENNReal.dyadic_le_tsum_pow_mul`),
  generalising `ENNReal.le_tsum_condensed` / `ENNReal.tsum_condensed_le`, and its form for the
  sequence capped at `b_{2^m}` (`ENNReal.tsum_min_le_dyadic`); the bound
  `∑_k 2^k b_{2^k} ≤ 2 ∑_n b_n` (`ENNReal.tsum_two_pow_mul_le_two_mul`), where Mathlib's
  `ENNReal.tsum_condensed_le` has `b_1 + 2 ∑_n b_n`; and
  `ENNReal.rpow_le_rpow_of_nonpos`, which exists for `ℝ` and `ℝ≥0` but not for `ℝ≥0∞`.
* **`x^z ≤ x` in `[0, ∞]`** (`FunctionSpaces/Domains/Lipschitz/IndicatorMultiplier.lean`):
  `x^z ≤ x` for `x ≥ 1` and `z ≤ 1` (`ENNReal.rpow_le_self_of_one_le`), the companion of
  Mathlib's `ENNReal.rpow_le_self_of_le_one`; Mathlib has it for `ℝ`
  (`Real.rpow_le_self_of_one_le`).
* **Products and sums in canonically ordered semirings**
  (`ApproximationSpaces/Sequences/Lq.lean`): `a x + b y ≤ (a + b)(x + y)`
  (`ENNReal.mul_add_mul_le_add_mul_add`) and `∑_{i ∈ s} a_i b_i ≤ (∑_{i ∈ s} a_i)(∑_{i ∈ s} b_i)`
  for every finite set `s` (`ENNReal.sum_mul_le_sum_mul_sum`). Stated here for `ℝ≥0∞`; both hold
  in every `[CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]`.
* **A dyadic sum** (`ApproximationSpaces/Sequences/Dyadic.lean`):
  `∑_{j ∈ ℕ} min(2^j a, (2^j a)⁻¹) ≤ 4` for every `a ∈ [0, ∞]` (`ENNReal.tsum_min_two_pow_le`),
  the sum behind every Hörmander condition for dyadic dilations; the same bound holds for
  `j ∈ ℤ`.
* **Dyadic blocks of `ℕ`** (`ApproximationSpaces/Sequences/Dyadic.lean`): every `n ≥ 1` is
  `2^k + i` for exactly one pair with `0 ≤ i < 2^k`, and then `k = ⌊log₂ n⌋`
  (`Nat.exists_eq_two_pow_add`, `Nat.two_pow_add_eq_iff`, `Nat.log_two_pow_add`); so a series
  in `[0, ∞]` splits into dyadic blocks, `∑_n g(n) = g(0) + ∑_k ∑_{i<2^k} g(2^k + i)`
  (`ENNReal.tsum_eq_add_tsum_two_pow_add`), with the finite form `ENNReal.sum_range_two_pow_eq`.
* **Interpolation of dyadic suprema** (`ApproximationSpaces/Sequences/Dyadic.lean`): the
  Brezis–Mironescu inequality
  `∑_j 2^(j(θσ₀ + (1-θ)σ₁)) a_j ≤ c (sup_j 2^(jσ₀) a_j)^θ (sup_j 2^(jσ₁) a_j)^(1-θ)` for
  `σ₁ < σ₀`, `0 < θ < 1` (`ENNReal.tsum_dyadicWeight_mul_le_iSup`, `ENNReal.dyadicInterpConst`),
  with its `ℓ_q` form; a candidate only together with `ENNReal.lqNorm` and
  `ENNReal.dyadicWeight`.
* **Discrete Hardy inequalities** (`ApproximationSpaces/Sequences/Hardy.lean`):
  `ENNReal.hardy_tail_le`, `ENNReal.hardy_sum_le`, and the almost diagonal estimate that combines
  both (`ENNReal.lqNorm_almostDiagonal_le`), with its constant `ENNReal.almostDiagonalConst`, and
  their forms for `0 < q ≤ 1` (`ENNReal.hardy_tail_le_of_le_one`,
  `ENNReal.hardy_sum_le_of_le_one`, `ENNReal.lqNorm_almostDiagonal_le_of_le_one`).
* **A fractional Hardy inequality on `(0, 1]`**
  (`FunctionSpaces/Analysis/Lp/HalfLineHardy.lean`): for `s > 1/2` and a measurable `u : ℝ → ℂ`
  that vanishes almost everywhere on some `(0, ε)`,
  `∫_0^1 |u(t)|² t^(-2s) dt ≤ K_s ∫_0^1 ∫_0^1 |u(t) - u(τ)|² / |t - τ|^(1+2s) dτ dt` with
  `K_s = 2^(2s+2) (1 - 2^(-(s-1/2)))^(-2)` (`Rd.lintegral_div_rpow_le_halfLineForm`,
  `Rd.halfLineForm`, `Rd.halfLineHardyConst`). Mathlib has no fractional Hardy inequality. Two
  general steps of the proof are candidates on their own: Minkowski's inequality twice,
  `μ(B)^(1/2) ‖u‖_{L_2(A)} ≤ (∫_A ∫_B |u(t) - u(τ)|²)^(1/2) + μ(A)^(1/2) ‖u‖_{L_2(B)}` on every
  s-finite measure space (`MeasureTheory.rpow_mul_lintegral_rpow_le`), and telescoping in
  `[0, ∞]`, `m_k ≤ ∑_{i ≥ 0} b_{k+i}` for `m_k ≤ m_{k+1} + b_k` with `m` eventually `0`
  (`ENNReal.le_tsum_of_le_add_of_eq_zero`).
* **Decreasing rearrangements and the layer cake formula for sums**
  (`ApproximationSpaces/Sequences/Rearrangement.lean`): for a nonnegative family `g` on any
  index set and `p > 0`, `∑_a g(a)^p = p ∫_0^∞ #{a : t < g(a)} t^(p-1) dt`
  (`tsum_ofReal_rpow_eq_lintegral`, Mathlib's layer cake formula for the counting measure), and,
  for the decreasing rearrangement `r*` of a nonnegative null family, `∑_n (r*_n)^p = ∑_i r_i^p`
  (`tsum_ofReal_rpow_decreasingRearrangement`). The rearrangement itself is TauCeti's
  (`TauCeti.decreasingRearrangement`, main `0642eae`), copied with its names, so these are
  candidates together with TauCeti's file.
* **Parseval's identity in `ℝ≥0∞`** (`ApproximationSpaces/Sequences/Lq.lean`):
  `‖x‖² = ∑_i ‖x_i‖²` for every `x ∈ ℓ²` (`lp.enorm_sq_eq_tsum`), next to Mathlib's
  `lp.norm_rpow_eq_tsum`.
* **Best `n`-term approximation from a Hilbert basis**
  (`ApproximationSpaces/Instances/NTermHilbertBasis.lean`): for a Mathlib `HilbertBasis` of a
  complex Hilbert space, the error of best approximation by combinations of at most `n` basis
  vectors is the smallest tail of the squared coefficients
  (`HilbertBasis.approxError_nTerm_sq_eq`), the tail bound
  `E_n(f) ≤ (n + 1)^(-(1/τ - 1/2)) ‖(⟨e_i, f⟩)_i‖_{ℓ_τ}` for `0 < τ ≤ 2` and every `n ≥ 0`
  (`HilbertBasis.approxError_nTerm_le`), and the theorem of Stechkin and DeVore,
  `f ∈ A^(1/τ - 1/2)_τ` iff `(⟨e_i, f⟩)_i ∈ ℓ_τ` for `0 < τ < 2`
  (`HilbertBasis.memApprox_nTerm_iff`). The statements use the project's
  approximation schemes (`ApproximationScheme.nTerm`, `ApproximationScheme.MemApprox`), so they
  are candidates together with that framework; the error formula alone could be stated with
  `Metric.infEDist`.
* **The tail of a convergent series** (`ApproximationSpaces/Lift.lean`): in every normed group,
  `∑_i a_i = f` gives `‖f - ∑_{i<n} a_i‖ ≤ ∑_{i ≥ 0} ‖a_{i+n}‖` for every `n`
  (`HasSum.enorm_sub_sum_range_le`).
* **The inclusion `L_r ↪ L_p`** (`FunctionSpaces/Analysis/Lp/Inclusion.lean`): for a finite measure
  and `p ≤ r`, the bounded linear injection `MeasureTheory.Lp.inclusionOfExponentLe`, with
  its norm bound and compatibility with `BoundedContinuousFunction.toLp`; the linear map
  underneath, `MeasureTheory.Lp.inclusionOfExponentLeLinear`, needs no `Fact (1 ≤ p)` and is
  injective for all exponents (`MeasureTheory.Lp.inclusionOfExponentLeLinear_injective`). Mathlib
  has the subgroup inclusion `MeasureTheory.Lp.antitone` but no bundled map.
* **Interpolation between `L_p` and `L_∞`** (`FunctionSpaces/Analysis/Lp/Interpolation.lean`):
  `eLpNorm f r μ ≤ M^(1-p/r) eLpNorm f p μ^(p/r)` for `‖f‖ ≤ M` a.e.
  (`MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow`), and its consequence that a bounded
  function in `L_p` lies in `L_r` for every `r ≥ p`
  (`MeasureTheory.MemLp.mono_exponent_of_enorm_le`).
* **`L_∞` norm of bounded continuous functions**
  (`FunctionSpaces/Analysis/Lp/BoundedContinuous.lean`): `‖a‖_{L_∞(μ)} ≤ ‖a‖` in `[0, ∞]` for
  every measure (`BoundedContinuousFunction.eLpNorm_top_le_enorm`, with the real form
  `BoundedContinuousFunction.toReal_eLpNorm_top_le_norm`), and for a finite measure the class of
  `a` in `L_p`, taken through `L_∞`, has `‖a‖_p ≤ μ(Ω)^(1/p) ‖a‖` for every exponent `p`, also
  `p < 1` (`BoundedContinuousFunction.eLpNorm_topInclusion_toLp_le`; Mathlib has
  `BoundedContinuousFunction.Lp_nnnorm_le` for `1 ≤ p`); for a measure charging open sets,
  `‖toLp ∞ μ a‖ = ‖a‖`, and the range is closed (`BoundedContinuousFunction.norm_toLp_top`,
  `.isClosed_range_toLp_top`).
* **Conditional expectation on `L_p`**
  (`FunctionSpaces/MeasureSpaces/Martingales/Filtration.lean`): for a finite measure and
  `1 ≤ p ≤ ∞`, `E[· | m]` as a contraction `Lp E p μ →L Lp E p μ`
  (`MeasureTheory.Lp.condExpLp`); Mathlib bundles it only on `L_1` and `L_2`.
* **Conditional expectation onto a countable partition**
  (`FunctionSpaces/MeasureSpaces/Martingales/Partition.lean`): for `φ : α → ι` with `ι` countable,
  measurable fibres and a finite measure, `μ[f | MeasurableSpace.comap φ ⊤]` is a.e. the average
  of `f` over the fibre through the point (`MeasureTheory.condExp_comap_ae_eq`).
* **The Haar basis of `L_2[0, 1]`** (`FunctionSpaces/Wavelets/Examples/HaarBasis.lean`): the Haar
  functions in breadth-first order, `φ_0 = 1` and `φ_{2^k+i} = h_{k,i}` for `0 ≤ i < 2^k`, as a
  `HilbertBasis ℕ ℂ (Lp ℂ 2 vol)` (`Haar.haarBasis`), with the coefficients `∫_0^1 f` and
  `⟨f, h_{k,i}⟩` (`Haar.haarBasis_repr_zero`, `Haar.haarBasis_repr_two_pow_add`). Mathlib has no
  Haar system; TauCeti has the real, unnormalised Haar functions in the same order as a Schauder
  basis of `L_p[0, 1]`, `1 ≤ p < ∞` (`TauCeti.unitInterval.haarBasis`).
* **Hilbert bases of eigenvectors**
  (`FunctionSpaces/MeasureSpaces/Spectral/CompactEigenbasis.lean`): for a symmetric operator such
  that the orthogonal complement of the sum of all eigenspaces is `{0}`, in particular a compact
  self-adjoint one, every choice of Hilbert bases of the eigenspaces gives a Hilbert basis of
  eigenvectors indexed by pairs of an eigenvalue and an index of a basis of its eigenspace
  (`ContinuousLinearMap.hilbertBasisOfEigenspaces`), with nonzero eigenvalues for injective
  operators (`ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero`), and the
  helper `HilbertBasis.inner_eq_zero_of_forall_inner_eq_zero`. The construction follows
  TauCeti's proof, and the helper and the statement of the theorem are taken from TauCeti
  (`TauCeti/Analysis/InnerProductSpace/Spectrum.lean` and `HilbertBasis/Basic.lean`, commit
  `463ab293`, Apache-2.0).
* **Compact dense embeddings have finitely many large singular values**
  (`FunctionSpaces/MeasureSpaces/Spectral/CompactEmbedding.lean`): for a compact injective
  `J : V → H` with dense range, the singular values `σ_i = ‖J† e_i‖` of the eigenvector basis of
  `J J†` satisfy `σ_i² = μ_i`, `v_i = σ_i⁻¹ J† e_i` is a Hilbert basis of `V`, and
  `{i : σ_i ≥ ε}` is finite for every `ε > 0` (`CompactDenseEmbedding.singularBasis`,
  `CompactDenseEmbedding.finite_setOf_le_singularValue`). EllipticPDE has the eigenvalue form,
  `IsCompactOperator.finite_setOf_hasEigenvalue_norm_ge` (`CompactSpectrum.lean`).
* **Polarization of a norm identity**
  (`FunctionSpaces/Domains/Spectral/DirichletEigenbasis.lean`):
  for linear maps `T`, `S_i` between inner product spaces over `ℝ` or `ℂ` and a real `c` with
  `‖x‖² = ‖T x‖² + c ∑_i ‖S_i x‖²`, the inner products satisfy
  `⟨x, y⟩ = ⟨T x, T y⟩ + c ∑_i ⟨S_i x, S_i y⟩` (`inner_eq_of_forall_sq_norm_eq`).
* **Gelfand triples** (`FunctionSpaces/Analysis/Hilbert/GelfandTriple.lean`): for a bounded
  linear `ι : V → H` between Hilbert spaces, the pivot dual `J : H → V*`, `J g = ⟪g, ι ·⟫`, the
  adjoint followed by `InnerProductSpace.toDual` (`ContinuousLinearMap.pivotDual`), with
  `‖J‖ = ‖ι‖`, `ker J = (range ι)^⊥`, `J` injective iff `ι` has dense range, and `J ∘ ι` injective
  iff `ι` is (`ContinuousLinearMap.norm_pivotDual`, `ContinuousLinearMap.ker_pivotDual`,
  `ContinuousLinearMap.pivotDual_injective_iff`,
  `ContinuousLinearMap.pivotDual_comp_injective_iff`), and `J g v = ∫ conj (g) ι v dμ` for
  `H = L_2(μ)` (`MeasureTheory.L2.pivotDual_apply_apply_eq_integral`); a continuous linear map
  into a Hilbert space has dense range iff `(range T)^⊥ = ⊥`
  (`ContinuousLinearMap.denseRange_iff_orthogonal_range_eq_bot`, next to
  `ContinuousLinearMap.orthogonal_range` in `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`);
  a function of `L_p(μ)`, `p ≥ 1`, that integrates to zero against the smooth real functions with
  compact support in an open set carrying `μ` vanishes
  (`MeasureTheory.Lp.eq_zero_of_forall_integral_contDiff_smul_eq_zero`, from
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`); and dense range in `L_2(μ)` of a map
  whose range contains these functions (`MeasureTheory.L2.denseRange_of_forall_contDiff`).
  Mathlib `v4.35.0` has adjoints and Riesz's representation but no pivot dual or Gelfand triple.
* **Fourier analysis on the torus** (`FunctionSpaces/Torus/Translation.lean`): the Fourier
  coefficients of a translate, `(τ_h f)^(k) = e_k(h) f̂(k)`
  (`Torus.mFourierCoeff_periodicTranslate`), and `|∏ aᵢ - 1| ≤ ∑ |aᵢ - 1|` for unimodular `aᵢ`
  (`Torus.norm_prod_sub_one_le`). Mathlib's measure on `UnitAddCircle` is a local instance
  in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, so `mFourierBasis` cannot be used
  outside that file without re-declaring it (`FunctionSpaces/Torus/HaarMeasure.lean`); worth
  reporting upstream.
* **Differences of polynomials by derivatives**
  (`FunctionSpaces/Domains/Interval/PolyDifferences.lean`):
  `|Δ_σ^m P(y)| ≤ σ^m sup_{[y, y+mσ]} |P^(m)|` (`Interval.norm_higherDiff_polyFun_le`), and the
  boundedness of every linear map of the polynomials of degree `< r` by the `L_p` norm on an
  interval (`Interval.exists_enorm_linearMap_le_eLpNorm`, in
  `FunctionSpaces/Domains/Interval/Polynomials.lean`), a form of Markov's inequality.
* **The translation algebra** (`FunctionSpaces/Analysis/Differences/TranslationAlgebra.lean`):
  `ℂ[G]` acting on functions on an additive commutative monoid `G` by translations
  (`TranslationAlgebra.diffAct`, from `AddMonoidAlgebra.lift`), with `(fwdDiff h)^[r] = (δ_h - 1)^r`
  (`TranslationAlgebra.higherDiff_eq_diffAct`), and the expansion of an isotropic difference on
  `ℝ^d` into mixed coordinate differences (`Cube.higherDiff_eq_sum`); Mathlib's `fwdDiff` has no
  such link to the group algebra.
* **Young's inequality and convolution operators**
  (`FunctionSpaces/Analysis/Fourier/Convolution.lean`): for a Haar measure on a finite-dimensional
  space, `1 ≤ p < ∞`, integrable `K` and `f ∈ L_p`, `‖K ⋆ f‖_p ≤ ‖K‖_1 ‖f‖_p`
  (`Rd.eLpNorm_conv_le`), from the weighted Jensen inequality `(∫ a g)^p ≤ (∫ a)^(p-1) ∫ a g^p`
  (`MeasureTheory.lintegral_mul_rpow_le`); associativity `(K ⋆ L) ⋆ f = K ⋆ (L ⋆ f)` a.e.
  (`Rd.conv_conv_ae`), convolution as a bounded operator on `L_p` (`Rd.convLp`), and Minkowski's
  integral inequality in the weighted form
  `‖∫ Φ(z) G(·, z) dz‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖G(·, z)‖_p^p dz`
  (`MeasureTheory.eLpNorm_integral_kernel_le`). Mathlib has only pointwise bounds of convolutions.
* **The adjoint of a convolution** (`FunctionSpaces/Rd/SingularIntegrals/ConvolutionAdjoint.lean`):
  for integrable `K`, `f ∈ L_p(V)` and `g ∈ L_q(V)` with `1/p + 1/q = 1`, `p < ∞`, and the
  reflection `K^∨(x) = K(-x)`, `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)` (`Rd.integral_conv_mul`), and with the
  adjoint kernel `K^*(x) = conj K(-x)`, `∫ (K ⋆ f) conj g = ∫ f conj(K^* ⋆ g)`
  (`Rd.integral_conv_mul_conj`). Mathlib has the associativity of convolutions but no such transpose
  formula for `L_p` functions.
* **Approximate identities in `L_p`** (`FunctionSpaces/Analysis/Fourier/ApproxIdentity.lean`): for
  integrable `Φ` with `∫ Φ = 1`, `‖Φ_c ⋆ f - f‖_p → 0` as `c → ∞`, `Φ_c = c^n Φ(c ·)`
  (`Rd.tendsto_eLpNorm_conv_dilate_sub`, `Rd.tendsto_convLp_dilate`), and the continuity of
  `w ↦ ‖f(· - w) - f‖_p` (`Rd.continuous_eLpNorm_comp_sub_sub`). Mathlib has the pointwise
  convergence of mollifiers for continuous functions.
* **The Fourier transform of dilations and kernel identities**
  (`FunctionSpaces/Analysis/Fourier/LittlewoodPaleyKernels.lean`): `𝓕(c^n Φ(c ·))(ξ) = 𝓕Φ(c⁻¹ ξ)`
  (`Rd.fourier_dilate`), `𝓕(f - g) = 𝓕f - 𝓕g` for integrable functions (`Rd.fourier_sub_apply`),
  and `K ⋆ L = M` from `𝓕K · 𝓕L = 𝓕M` by Fourier inversion (`Rd.conv_eq_of_fourier`).
* **Moduli of smoothness on finite-dimensional spaces**
  (`FunctionSpaces/Analysis/Differences/Differences.lean`): for Mathlib's `fwdDiff` and a Haar
  measure, `‖Δ_h^r f‖_p ≤ 2^r ‖f‖_p`, the dilation property `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p`
  (`Rd.smoothnessModulus_mul_le`), and `Δ_h^r (K ⋆ f) = (Δ_h^r K) ⋆ f` almost everywhere
  (`Rd.higherDiff_conv_ae`); the modulus on a subset `U`, with the differences restricted to the
  points `x` with `x, …, x + rh ∈ U` (`Rd.modulusOn`,
  `FunctionSpaces/Analysis/Differences/DomainModuli.lean`); `ω_r(f, t)_p → 0` as `t → 0` for
  `f ∈ L_p`, `1 ≤ p < ∞` (`Rd.tendsto_smoothnessModulus`,
  `FunctionSpaces/Rd/Differences/DilatedDifferences.lean`); `Δ_h^r (f ∘ e) = (Δ_{e h}^r f) ∘ e`
  for every additive map `e` (`Rd.higherDiff_comp_addHom`, `Differences.lean`) and
  `ω_r(f ∘ e, t)_p ≤ ω_r(f, ‖e‖ t)_p` for a measure preserving continuous linear map `e`
  (`Rd.smoothnessModulus_comp_le`, `FunctionSpaces/Analysis/Differences/LinearEquivModuli.lean`),
  also for the modulus on a set, `ω_r(f ∘ e, t, e⁻¹(U))_p ≤ ω_r(f, ‖e‖ t, U)_p`
  (`Rd.modulusOn_comp_le`), and for affine maps `A x = a + L x`,
  `ω_r(f ∘ A, t, A⁻¹(U))_p ≤ L^(-n/p) ω_r(f, L t, U)_p` (`Rd.modulusOn_comp_affine_le`).
* **Composition with measure preserving maps in `L_p`**
  (`FunctionSpaces/Analysis/Differences/LinearEquivModuli.lean`): `‖g ∘ f‖_p = ‖g‖_p` in
  `[0, ∞]` for a measure preserving `f` (`MeasureTheory.Lp.enorm_compMeasurePreserving`). Mathlib
  has only the real-valued form `MeasureTheory.Lp.norm_compMeasurePreserving`. For affine maps
  `x ↦ a + L x`, `L > 0`, on a space of dimension `n` with an additive Haar measure:
  `x ↦ a + L x` carries `μ` to `L^(-n) μ` and `‖G(a + L ·)‖_p = L^(-n/p) ‖G‖_p` for every `p`
  (`Rd.measurePreserving_affine`, `Rd.eLpNorm_comp_affine`); Mathlib has
  `MeasureTheory.Measure.map_addHaar_smul` but no `L_p` form.
* **Operator norms of `PiLp.continuousLinearEquiv`**
  (`FunctionSpaces/Analysis/Differences/LinearEquivModuli.lean`): `‖ofLp‖ ≤ 1` and
  `‖toLp‖ ≤ (#ι)^(1/p)` (`PiLp.norm_continuousLinearEquiv_le`,
  `PiLp.norm_continuousLinearEquiv_symm_le`); Mathlib has the Lipschitz constants
  (`PiLp.lipschitzWith_ofLp`, `PiLp.lipschitzWith_toLp`) but no operator-norm form.
* **Componentwise maps and orthogonal complements in finite `L_2` sums**
  (`FunctionSpaces/Analysis/Hilbert/PiLpMaps.lean`): on `WithLp 2 (Fin m → X)`, a continuous
  linear map acting componentwise with operator norm at most `‖f‖`, isometric if `f` is, onto if
  `f` is, with kernel `(ker f)^m` and range `(range f)^m` (`PiLp.compLeftL`,
  `PiLp.norm_compLeftL_le`, `PiLp.norm_compLeftL_apply`, `PiLp.compLeftL_surjective`,
  `PiLp.ker_compLeftL`, `PiLp.range_compLeftL`, `PiLp.range_compLeftL_subtypeL`), continuous
  linear equivalences and semilinear isometric equivalences acting componentwise
  (`PiLp.congrRightL`, `PiLp.congrRightSL`), `⟪single i a, x⟫ = ⟪a, x i⟫` for a general inner
  product space (`PiLp.inner_single_left_eq_inner`, `PiLp.inner_single_right_eq_inner`), the
  orthogonal complement `(K^m)ᗮ = (Kᗮ)^m` of `Submodule.pi` for every submodule `K`
  (`PiLp.orthogonal_piSubmodule`, with `K^m = PiLp.piSubmodule m K`), and for a Hilbert space
  `E` the linear isometric equivalence of the dual of `WithLp 2 (Fin m → E)` with
  `WithLp 2 (Fin m → StrongDual ℂ E)`, `ℓ ↦ (ℓ ∘ PiLp.single 2 i)_i`, built from Riesz's maps
  (`PiLp.strongDualEquiv`), stated over `ℂ`. The upstream form would take any `RCLike` field and
  any finite index type, and the two inner product identities would become
  `PiLp.inner_single_left` and `PiLp.inner_single_right`. Upstream, the identification of the
  dual needs neither completeness nor an inner product: for every normed space `X` and conjugate
  exponents `p`, `q`, the same map identifies the dual of `WithLp p (ι → X)` isometrically with
  `WithLp q (ι → StrongDual 𝕜 X)` (Hölder duality of `ℓ_p^m(X)`), and that is the form Mathlib
  would want. Mathlib has the linear maps `LinearMap.withLpMap` and `LinearEquiv.withLpCongr`
  without continuity or norm bounds, `ContinuousLinearMap.piMap` on the plain product with its
  surjectivity, kernel and range (`Function.Surjective.piMap`, `LinearMap.ker_compLeft`,
  `LinearMap.range_compLeft`), the linear isometric case `LinearIsometryEquiv.piLpCongrRight`,
  and the inner product identities for `lp`, `EuclideanSpace` and the Hilbert `C⋆`-module
  `C⋆ᵐᵒᵈ(A, Π i, E i)` (`lp.inner_single_left`, `EuclideanSpace.inner_single_left`,
  `WithCStarModule.inner_single_left`), the last one the closest analogue. These belong in
  `Mathlib/Analysis/Normed/Lp/PiLp.lean` and `Mathlib/Analysis/InnerProductSpace/PiL2.lean`, in
  the namespace `PiLp`.
* **Sobolev–Slobodeckij norms** (`FunctionSpaces/Rd/Differences/SobolevSlobodeckij.lean`):
  Mathlib has no fractional Sobolev spaces. The Gagliardo form
  `∫∫ |f(y) - f(x)|^p / |y - x|^(n+sp) dy dx` on a finite-dimensional inner product space
  (`Rd.slobodeckijForm`), its form `∫ ‖Δ_h f‖_p^p / |h|^(n+sp) dh` by Tonelli's theorem
  (`Rd.slobodeckijForm_eq_lintegral_eLpNorm`), its two-sided bounds by the first-difference
  Besov norm (`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`, `Rd.slobodeckijForm_le`) and
  `W^{s,p} = B^s_{p,p}` for `0 < s < 1` (`Rd.slobodeckijForm_lt_top_iff_memApprox`); for `p = 2`
  the form is the square of the `L_2` norm of `(x, y) ↦ f(y) - f(x)` for the measure
  `|y - x|^(-(n+2s)) dx dy` (`Rd.gagliardoMeasure`, `Rd.eLpNorm_sub_sq_gagliardoMeasure`), which
  gives `W^{s,2}` an inner product; the radial integrals `∫_{|z| ≥ R} |z|^(-a)` for `a > n` and
  `∫_{|z| < R} |z|^(-a)` for `a < n` with explicit constants
  (`Rd.lintegral_compl_ball_norm_rpow_neg_le`, `Rd.lintegral_ball_norm_rpow_neg_le`) belong next
  to Mathlib's `integrableOn_ball_of_norm_le_rpow`. The Lean project *quadratic-forms-sobolev-lean*
  has the form for `p = 2` (`formHs`); *grunweg/SobolevSlobodeckij* has integer orders only.
* **Leibniz's rule for iterated forward differences**
  (`FunctionSpaces/Rd/Differences/PointwiseMultipliers.lean`):
  `Δ_h^r(u v)(x) = ∑_{l ≤ r} C(r, l) Δ_h^l u(x) Δ_h^(r-l) v(x + l h)` (`Rd.higherDiff_mul`); Mathlib
  has only the one-step `fwdDiff_smul`. Also `‖Δ_h^l G(x)‖ ≤ C ‖h‖^l` for `G` of class `C^l` with
  `‖D^l G‖ ≤ C` on the segment from `x` to `x + l h` (`Rd.norm_higherDiff_le_of_segment`), and its
  global form `‖Δ_h^l G(x)‖ ≤ ‖h‖^l sup ‖D^l G‖` (`Rd.norm_higherDiff_le_of_iteratedFDeriv`).
* **Smooth resolutions of unity in a finite-dimensional space**
  (`FunctionSpaces/Domains/Lipschitz/BoundedLipschitz.lean`): `Rd.exists_smooth_partition`, with
  `ContDiff` functions, from Mathlib's manifold version, its form equal to `1` on a neighbourhood of
  a compact set (`Rd.exists_smooth_partition_nhds`), and bounded derivatives of compactly supported
  smooth functions (`Rd.exists_iteratedFDeriv_bound`,
  `FunctionSpaces/Rd/Differences/PointwiseMultipliers.lean`).
* **Multiplication by an indicator on `L_p`** (`FunctionSpaces/Analysis/Lp/IndicatorOperator.lean`):
  for a measurable set `s`, `g ↦ 1_s g` as a continuous linear operator of norm at most `1` on
  `Lp ℂ p μ` (`Rd.indicatorLp`). Mathlib has `indicatorConstLp` for constant functions.
* **Extension by zero on `L_p`** (`FunctionSpaces/Analysis/Lp/IndicatorOperator.lean`): for
  measurable `T ⊆ O`, `g ↦ 1_T g` from `Lp ℂ p (μ.restrict O)` to `Lp ℂ p μ` as a continuous
  linear operator of norm at most `1` (`Rd.indicatorExtendLp`; TauCeti has `extendByZeroLpₗᵢ`).
  With Mathlib's restriction `LpToLpRestrictCLM`: the restriction of the extension by zero is the
  identity, and two restrictions agree iff the cut-offs agree
  (`Rd.LpToLpRestrictCLM_indicatorExtendLp`, `Rd.LpToLpRestrictCLM_eq_iff_indicatorLp_eq`,
  `FunctionSpaces/Domains/Lipschitz/SplinesOnDomains.lean`).
* **Differences of Schwartz functions in `L_p`**
  (`FunctionSpaces/Rd/Approximation/BandInverse.lean`): for a Schwartz function `G` on a
  finite-dimensional real inner product space and `1 ≤ p < ∞`, `‖G(· + v) - G‖_p ≤ ‖∂_v G‖_p`
  (`Rd.lintegral_enorm_fwdDiff_rpow_le`), from `(∫_0^1 φ)^p ≤ ∫_0^1 φ^p`
  (`Rd.rpow_lintegral_Ioc_le`); `‖Δ_v^r G‖_1 ≤ ‖v‖^r ‖D^r G‖_1`
  (`Rd.lintegral_enorm_higherDiff_schwartz_le`) by the commutation of differences with line
  derivatives (`Rd.lineDerivOp_fwdDiffSchwartz`); and the difference `f ↦ f(· + v) - f` as a
  bounded operator on `L_2` (`Rd.fwdDiffL2`).
* **Bounded overlap in `L_p`** (`FunctionSpaces/Rd/Atoms/AtomSynthesis.lean`): if at every point at
  most `N` of the functions `g_m` are nonzero, then `‖∑_m g_m‖_p^p ≤ N^(p-1) ∑_m ‖g_m‖_p^p`
  (`Rd.eLpNorm_rpow_le_of_overlap`); a set all of whose finite subsets have at most `N` elements is
  finite with at most `N` elements (`Rd.exists_finset_of_card_le`).
* **Dyadic cubes of a finite-dimensional inner product space**
  (`FunctionSpaces/Analysis/Maximal/DyadicGrid.lean`): the cubes `⌊2^k ⟪b_i, x⟫⌋ = m_i` of every
  level `k ∈ ℤ` (`Rd.zcell`), the cells `Rd.dyadicCell` of the levels `j ∈ ℕ`, their centres, and
  the count of at most `(2ρ + 2)^n` centres in a ball of radius `ρ 2^(-j)`
  (`Rd.card_le_of_norm_cellCenter_sub_le`).
* **Pointwise bounds of convolutions** (`FunctionSpaces/Rd/Atoms/AtomAnalysis.lean`): Hölder's
  inequality on a ball `∫_B |g| ≤ |B|^(1-1/p) ‖g‖_p` (`Rd.lintegral_closedBall_le`),
  `|(K ⋆ g)(x)| ≤ sup |K| |B(0, ρ)|^(1-1/p) ‖g‖_p` for `K` vanishing outside `B(0, ρ)`
  (`Rd.enorm_conv_le_of_bound`), and `Δ_h^r (K ⋆ g) = (Δ_h^r K) ⋆ g` at every point
  (`Rd.higherDiff_conv_apply`).
* **Continuity of convolutions with `L_p` functions**
  (`FunctionSpaces/Rd/Sobolev/SobolevEmbedding.lean`): for `1 ≤ p < ∞`, an integrable bounded kernel
  `K` and `f ∈ L_p`, `K ⋆ f` is continuous (`Rd.continuous_conv_of_enorm_le`). Mathlib's
  `HasCompactSupport.continuous_convolution_right` needs a continuous function of compact support.
* **Approximate identities at points of continuity**
  (`FunctionSpaces/Domains/Traces/GraphTrace.lean`): for integrable `Φ` with `∫ Φ = 1` and bounded
  support, `(Φ_{2^J} ⋆ F_J)(z) → z₀` as `J → ∞` and `z → y` whenever `F_J(z) → z₀`
  (`Rd.conv_dilate_near`). Mathlib's `convolution_tendsto_right` needs nonnegative kernels.
* **Convolution with Lipschitz functions** (`FunctionSpaces/Domains/Traces/MollifiedGraph.lean`):
  for an integrable kernel `K` with bounded support and an `M`-Lipschitz `u`, `K ⋆ u` is Lipschitz
  with constant `M ‖K‖_1` (`Rd.norm_conv_sub_conv_le`), `|K ⋆ u - u| ≤ M R ‖K‖_1` for `∫ K = 1`
  (`Rd.norm_conv_sub_self_le`), and `|Δ_h^2 (K ⋆ u)| ≤ M (R + 2‖h‖) ‖Δ_h^2 K‖_1`
  (`Rd.norm_higherDiff_two_conv_le`); `∫ Δ_h^r K = 0` for `r ≥ 1`
  (`Rd.integral_higherDiff_eq_zero`).
* **Lipschitz images of null sets** (`FunctionSpaces/Domains/Traces/GraphTraceCharts.lean`): a
  Lipschitz map between finite-dimensional inner product spaces of the same dimension maps null sets
  to null sets (`Rd.volume_image_eq_zero_of_lipschitzWith`), through the Hausdorff measure, a Haar
  measure in finite dimension.
* **Null graphs of Lipschitz functions** (`FunctionSpaces/Domains/Lipschitz/BesovDomains.lean`):
  for a unit vector `e` and a Lipschitz `φ` constant along `e`, the graph `{x : φ(x) = ⟪x, e⟫}` is
  a null set (`Rd.LipschitzGraph.volume_graph`), as the image of the null hyperplane `e^⊥`
  (`Rd.volume_orthogonal_singleton_eq_zero`) under the Lipschitz map `y ↦ y + φ(y) e`; Mathlib
  has no null-graph lemma (checked 2026-10-25). The quadrant lemmas of the same file
  (`Rd.quadrant_ae_eq`) overlap Mathlib PR #44352 (`closure_quadrant`, `frontier_quadrant`,
  `range_modelWithCornersEuclideanQuadrant`), which is newer than the Mathlib tag of the project.
* **Tensor products of functions** (`FunctionSpaces/Rd/MixedSmoothness/TensorKernels.lean`): for
  `(⊗K)(x) = ∏_i K_i(x_i)` on `ℝ^d`, `‖⊗K‖_1 = ∏_i ‖K_i‖_1` (`Rd.lintegral_enorm_tensorKernel`),
  `‖⊗K‖_p = ∏_i ‖K_i‖_p` for `0 < p < ∞` and a.e. strongly measurable `K_i`
  (`Rd.eLpNorm_tensorKernel`), from the `lintegral` product formula
  `∫⁻ ∏_i f_i(x_i) dx = ∏_i ∫⁻ f_i` for all a.e. measurable `f_i : ℝ → [0, ∞]`
  (`Rd.lintegral_fin_nat_prod_volume_eq_prod`; Mathlib has only the Bochner form
  `integral_fintype_prod_eq_prod`, TauCeti has the general `Measure.pi` form
  `TauCeti.lintegral_fintype_prod_eq_prod`),
  `(⊗K) ⋆ (⊗K') = ⊗(K_i ⋆ K'_i)` (`Rd.conv_tensorKernel`), and diagonal changes of variables
  `∫ F((a_i z_i)_i) dz = (∏_i a_i)⁻¹ ∫ F` (`Rd.integral_comp_diagMap`).
* **`L_p` norms on `Fin (n+1) → ℝ` through slices**
  (`FunctionSpaces/Analysis/Lp/CoordinateSlices.lean`): integrating out the coordinate `i`,
  `∫⁻ G = ∫⁻ y, ∫⁻ t, G (i.insertNth t y)` for a.e. measurable `G ≥ 0`
  (`Rd.lintegral_eq_lintegral_slices`), `‖f‖_p = ‖y ↦ ‖t ↦ f (i.insertNth t y)‖_p‖_p` for
  measurable `f` and `0 < p < ∞` (`Rd.eLpNorm_eq_eLpNorm_slices`), and bounds through the slices
  `t ↦ f (Function.update x i t)` with Minkowski's inequality (`Rd.eLpNorm_le_add_of_slice_le`);
  Mathlib has `volume_preserving_piFinSuccAbove` and the marginals `lmarginal`, but no `L_p` form
  (TauCeti has the product-measure form `TauCeti.eLpNorm_prod_eq_eLpNorm_eLpNorm`).
* **The Schur test on `ℓ_q`** (`FunctionSpaces/Rd/MixedSmoothness/MixedSequences.lean`): row and
  column sums at most `A` give `‖(∑_k w(m, k) b_k)_m‖_{ℓ_q} ≤ A ‖b‖_{ℓ_q}` for `1 ≤ q ≤ ∞`
  (`Rd.lqNorm_schur_le`), for countable index sets; `∑_k ∏_i f_i(k_i) ≤ ∏_i ∑_j f_i(j)` on `ℕ^d`
  (`Rd.tsum_prod_le_prod_tsum`).
* **Sums of products of finitely supported factors**
  (`FunctionSpaces/Rd/MixedSmoothness/MixedSequences.lean`): for a finite index type `ι` and
  `F_i : κ → R` vanishing outside finite sets, `∑' k : ι → κ, ∏ i, F i (k i) =
  ∏ i, ∑' n, F i n` in every commutative topological semiring (`Rd.tsum_prod_eq_prod_tsum`), from
  `Finset.prod_univ_sum`; Mathlib has the finite form and the two-factor product formula
  `Summable.tsum_mul_tsum`, but no `tsum` over function types `ι → κ`.
* **The layer cake formula for `[0, ∞]`-valued functions**
  (`FunctionSpaces/Analysis/Lp/LayerCake.lean`): `∫ F^p dν = p ∫_0^∞ ν{F > t} t^(p-1) dt` for
  `p > 0`, every measure and every a.e. measurable `F : α → [0, ∞]`
  (`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal`); Mathlib's
  `lintegral_rpow_eq_lintegral_meas_lt_mul` is for real `f ≥ 0`. Mathlib PR #44813 (open,
  October 2026) adds the layer cake formula in `ℝ≥0∞`, which overlaps with this candidate. Also
  the `lintegral` of powers over intervals, `∫_{(0,b)} t^r dt = b^(r+1)/(r+1)` for `r > -1` and
  `b ≥ 0` (`MeasureTheory.lintegral_Ioo_rpow`) and `∫_{(0,∞)} t^r dt = ∞`
  (`MeasureTheory.lintegral_Ioi_rpow_eq_top`).
* **The Hardy–Littlewood maximal function**
  (`FunctionSpaces/Analysis/Maximal/HardyLittlewoodMaximal.lean`): the centred maximal function on a
  finite-dimensional inner product space (`Rd.maximalFunction`), its lower semicontinuity and
  measurability for every `g` (`Rd.lowerSemicontinuous_maximalFunction`,
  `Rd.measurable_maximalFunction`), the weighted weak type `∫_{Mg > t} w ≤ C t⁻¹ ∫ g Mw`
  (`Rd.setLIntegral_maximalFunction_gt_le`), the weak type `(1,1)`
  (`Rd.volume_maximalFunction_gt_le`), the weighted strong type `∫ (Mg)^p w ≤ C ∫ g^p Mw`
  (`Rd.lintegral_maximalFunction_rpow_mul_le`) and the maximal theorem `‖Mg‖_p ≤ C ‖g‖_p` for
  `1 < p < ∞` (`Rd.eLpNorm_maximalFunction_le`), with explicit constants. Mathlib has Vitali's
  covering lemma and the differentiation theorem, but no maximal function.
* **Dyadic cubes and Lebesgue differentiation along them**
  (`FunctionSpaces/Analysis/Maximal/DyadicCubes.lean`): the volume and the nesting of the dyadic
  cubes (`Rd.volume_zcell`, `Rd.zcell_subset_or_disjoint`), and the convergence of the averages
  over the cubes containing `x` to `F(x)` for almost every `x` and locally integrable `F`
  (`Rd.ae_tendsto_average_cubeAt`), from Mathlib's
  `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`.
* **The Calderón–Zygmund decomposition** (`FunctionSpaces/Analysis/Maximal/CalderonZygmund.lean`):
  for `n ≥ 1`, `t > 0` and a.e. measurable `G` with `∫ G < ∞`, the maximal dyadic cubes with average
  `> t` are disjoint, have averages at most `2^n t`, total measure at most `t⁻¹ ∫ G`
  (`Rd.cz_volume_le`), and `G ≤ t` almost everywhere off their union (`Rd.cz_ae_le_of_notMem`).
* **The Fefferman–Stein inequality** (`FunctionSpaces/Analysis/Maximal/FeffermanStein.lean`):
  `‖ ‖(M g_j)_j‖_{ℓ_q} ‖_p ≤ C ‖ ‖(g_j)_j‖_{ℓ_q} ‖_p` for `1 < p < ∞`, `1 < q ≤ ∞`
  (`Rd.feffermanStein`), with the vector-valued weak type `(1,1)`
  (`Rd.volume_lqNorm_maximalFunction_gt_le`) and the bound of the maximal function off enlarged
  sets, `M(1_{⋃ Q_i} g)(x) ≤ 3^n M g̃(x)` for countably many sets `Q_i ⊆ B̄(c_i, ρ_i)` of positive
  finite measure and `x` outside every `B̄(c_i, 2ρ_i)`, where `g̃ = ∑_i (⨍_{Q_i} g) 1_{Q_i}`
  (`Rd.maximalFunction_indicator_iUnion_le`).
* **Norms of means of vector-valued functions**
  (`FunctionSpaces/Analysis/Maximal/CalderonZygmund.lean`): `‖⨍ f‖ₑ ≤ ⨍⁻ ‖f‖ₑ` for `f` with
  values in a real normed space (`MeasureTheory.enorm_average_le`), next to Mathlib's
  `enorm_integral_le_lintegral_enorm`; on a set `s` of finite measure `μ s * ‖⨍_s f‖ₑ ≤ ∫⁻_s ‖f‖ₑ`
  (`MeasureTheory.measure_mul_enorm_setAverage_le`) and `∫⁻_s ‖f - ⨍_s f‖ₑ ≤ 2 ∫⁻_s ‖f‖ₑ`
  (`MeasureTheory.setLIntegral_enorm_sub_setAverage_le`), the step behind the mass of the bad pieces
  of a Calderón–Zygmund decomposition.
* **Level sets of a split function**
  (`FunctionSpaces/Analysis/Lp/Marcinkiewicz.lean`): if `u ≤ a + b` almost
  everywhere, `∫⁻ a² ≤ A t I`, `μ S ≤ D t⁻¹ I` and `∫⁻_{Sᶜ} b ≤ K I`, then
  `μ {u > t} ≤ (4A + D + 2K) t⁻¹ I` (`MeasureTheory.measure_lt_le_of_ae_le_add`), from the two forms
  of Chebyshev's inequality at half height (`MeasureTheory.measure_half_lt_le_lintegral_sq`,
  `MeasureTheory.measure_half_lt_le_add_setLIntegral_compl`): the level-set bookkeeping of a
  Calderón–Zygmund argument; the first form is Chebyshev's inequality with a power in lintegral
  form, `μ {F > t} ≤ t^(-r) ∫⁻ F^r` (`MeasureTheory.measure_lt_le_inv_rpow_mul_lintegral`; Mathlib
  has the `eLpNorm` form `meas_ge_le_mul_pow_eLpNorm_enorm`). The three lemmas assume
  `0 < t < ∞`; for Mathlib these hypotheses would be removed, since at `t = ∞` the level sets are
  empty and at `t = 0` the bounds are either `∞` or force the functions to vanish almost
  everywhere. Also `MemLp f 2 μ` from `∫⁻ ‖f‖ₑ ^ 2 ∂μ ≠ ∞`
  (`MeasureTheory.memLp_two_of_lintegral_enorm_sq_ne_top`), with the exponent `2 : ℕ`.
* **The Hörmander condition for dilation families**
  (`FunctionSpaces/Rd/SingularIntegrals/DilationFamilies.lean`): for Schwartz functions `G_j` with
  seminorms bounded uniformly in `j` (`Rd.IsUniformSchwartz`) and `θ_j = 2^(jn) G_j(2^j ·)`,
  `∫_{‖x‖ > 2‖y‖} ‖(θ_j(x - y) - θ_j(x))_j‖_{ℓ_2} dx ≤ 4 H_A` for every `y`, with an explicit
  constant built from the seminorm bounds (`Rd.lintegral_lqNorm_sub_le`, `Rd.familyHormanderConst`);
  such a family with bounded Fourier overlap is a Calderón–Zygmund family
  (`Rd.IsCZFamily.of_dilation`), and so is its adjoint family (`Rd.IsCZFamily.adjoint`).
* **Vector-valued singular integrals**
  (`FunctionSpaces/Rd/SingularIntegrals/VectorValuedWeakType.lean`,
  `FunctionSpaces/Rd/SingularIntegrals/VectorValuedSingularIntegrals.lean`): for a Calderón–Zygmund
  family `(θ_j)_j` with overlap `B` and Hörmander constant `H` on a space of dimension `n ≥ 1`, the
  analysis operator `f ↦ ‖(θ_j ⋆ f)_j‖_{ℓ_2}` and the synthesis operators
  `(g_j)_j ↦ ∑_{j ∈ s} θ_j ⋆ g_j` have weak type `(1,1)` (`Rd.IsCZFamily.volume_lqNorm_conv_gt_le`,
  `Rd.IsCZFamily.volume_enorm_sum_conv_gt_le`) and strong type `(p,p)` for `1 < p < ∞`
  (`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`, `Rd.IsCZFamily.eLpNorm_sum_conv_le`), with explicit
  constants (`Rd.vectorWeakConst`, `Rd.czConst`). Mathlib has no singular integrals; the Carleson
  project has the scalar Calderón–Zygmund theory on doubling metric measure spaces.
* **Marcinkiewicz interpolation between weak type `(1,1)` and strong type `(2,2)`**
  (`FunctionSpaces/Analysis/Lp/Marcinkiewicz.lean`): the two Tonelli steps
  `∫_0^∞ τ^(p-2) ∫_{F > τ} F dμ dτ = (p - 1)⁻¹ ∫ F^p` and
  `∫_0^∞ τ^(p-1-r) ∫_{F ≤ τ} F^r dμ dτ ≤ (r - p)⁻¹ ∫ F^p` on s-finite measure spaces
  (`MeasureTheory.lintegral_Ioi_lintegral_indicator_lt_mul_rpow`,
  `MeasureTheory.lintegral_Ioi_lintegral_indicator_compl_mul_rpow_le`), the layer cake argument
  `MeasureTheory.lintegral_rpow_le_of_forall_le_add`, and the case `(1,1)`, `(2,2)` of real
  interpolation with an explicit constant in the terms of the Carleson project
  (`MeasureTheory.hasStrongType_of_hasWeakType_one_of_hasStrongType_two`); the definitions in
  `FunctionSpaces/Analysis/Lp/WeakType.lean` are the Carleson project's own candidates. The file
  imports the layer cake formula and the integrals of powers from
  `FunctionSpaces/Analysis/Lp/LayerCake.lean`. The Carleson project proves the general real
  interpolation theorem for `A ≥ 1` and positive finite constants; new here are s-finite input
  measures, every `A ≥ 0`, constants in `[0, ∞]` and the explicit constant
  `(p (2 A C₁/(p - 1) + 4 A² C₂²/(2 - p)))^(1/p)`.
* **`L_p` norms by duality** (`FunctionSpaces/Analysis/Lp/NormingFamily.lean`): for `1 < p < ∞` with
  conjugate `q` and `v ∈ L_p(μ)`, if `|∫ v conj g| ≤ A ‖g‖_q` for every `g ∈ L_q(μ)`, then
  `‖v‖_p ≤ A` (`MeasureTheory.eLpNorm_le_of_forall_enorm_integral_mul_conj_le`), and the same
  for the `L_p(ℓ_2)` norm of a family in `L_p` vanishing outside a finite set
  (`MeasureTheory.eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le`), by testing on
  `u_j ‖(u_i)_i‖_{ℓ_2}^{p-2}`; Mathlib's `MeasureTheory/Function/Holder.lean` has the pairing
  of `L_p` and `L_q` with its upper bound (`lpPairing`), and this is the converse. Also
  Hölder's inequality for `[0, ∞]`-valued functions written with `eLpNorm`
  (`MeasureTheory.lintegral_mul_le_eLpNorm_mul_eLpNorm`).
* **Integrals under a change of scale** (`FunctionSpaces/Analysis/Fourier/ApproxIdentity.lean`):
  `∫ f(r x) dμ(x) = |r^(-n)| ∫ f dμ` for an additive Haar measure `μ`, `f : V → [0, ∞]` and `r ≠ 0`
  (`Rd.lintegral_comp_smul`), from Mathlib's `Measure.map_addHaar_smul`; Mathlib has the Bochner
  version `Measure.integral_comp_smul`.
* **The quotient map of the torus** (`FunctionSpaces/Torus/PeriodicLift.lean`): Mathlib has the
  period-box identity `∫_{a + (0,1]^d} g(π x) dx = ∫_{𝕋^d} g` on `d → ℝ`
  (`UnitAddTorus.lintegral_preimage`). New here are the measure preservation of
  `π : ℝ^d → 𝕋^d` on every period box of `EuclideanSpace ℝ d`
  (`Torus.measurePreserving_quotientProj_periodBox`) and the fact that `π` pulls null sets back to
  null sets (`Torus.quasiMeasurePreserving_quotientProj`).
* **Fourier coefficients in `L_p(𝕋^d)`** (`FunctionSpaces/Torus/LpFourierCoefficients.lean`),
  for `Mathlib/Analysis/Fourier/AddCircleMulti.lean`: the coefficient `f ↦ f̂(m)` as a bounded
  linear functional of norm at most `1` on `L_p(𝕋^d)`, `1 ≤ p ≤ ∞` (`Torus.coeffCLM`,
  `Torus.norm_coeffCLM_le`), the coefficients of the characters
  (`Torus.mFourierCoeff_mFourierLp`), of convolutions with integrable kernels on `ℝ^d`
  (`Torus.mFourierCoeff_periodicEconvLp`), and uniqueness for `1 ≤ p ≤ ∞`
  (`Torus.eq_of_mFourierCoeff_eq`). Mathlib has uniqueness in `L_2`, through `mFourierBasis`;
  the open PR #43803 (Fejér's theorem on `AddCircle`) overlaps with uniqueness for `d = 1`.
* **The Fejér–Riesz theorem** (`FunctionSpaces/Wavelets/Examples/Daubechies/FejerRiesz.lean`): a
  real polynomial `Q` with `Q > 0` on `[-1, 1]` satisfies `Q(cos θ) = |L(e^(iθ))|²` for a real
  polynomial `L` of degree `≤ deg Q` with `L(1) > 0` and without zeros in the closed unit disk
  (`Polynomial.fejer_riesz`, `Polynomial.fejer_riesz_outer`); Mathlib has no factorisation of
  positive trigonometric polynomials.
* **Fourier transforms of integrable functions**
  (`FunctionSpaces/Wavelets/Examples/Daubechies/FourierIntegrable.lean`):
  the fundamental lemma with Schwartz test functions on an open set, pointwise for continuous `f`
  (`Real.eqOn_zero_of_integral_mul_schwartz_eq_zero`); Mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` tests with smooth compactly supported
  functions and concludes almost everywhere. Also the transform of differences
  `𝓕(Δ_h^r f)(ξ) = (e^(2πihξ) - 1)^r 𝓕 f(ξ)` (`Real.fourier_iterate_fwdDiff_apply`,
  `SobolevRegularity.lean`).
* **Viète's product** (`FunctionSpaces/Wavelets/Examples/Daubechies/SymbolProduct.lean`):
  `∏_{j ≥ 0} cos(x/2^(j+1)) = sinc x` (`Daubechies.tprod_cos`), with `|cos y - 1| ≤ y²/2`
  (`Daubechies.norm_cos_sub_one_le`) and the two-sided bound `|sinc x| ≤ 1/|x|`
  (`Daubechies.abs_sinc_le_inv_abs`, `SymbolDecay.lean`); Mathlib has Wallis's product and the
  one-sided `Real.sinc_le_inv_abs`.
* **Poisson summation with vanishing coefficients**
  (`FunctionSpaces/Wavelets/Examples/Daubechies/ScalingMoments.lean`):
  the periodisation `∑_n f(x + n)` of a continuous `f` vanishing outside a bounded interval, with
  `𝓕 f(n) = 0` for `n ≠ 0`, is the constant `∫ f` (`Real.tsum_comp_add_int_eq_integral`).
* **Sums over overlapping sets and shifts in `ℓ_q(ℤ)`**
  (`FunctionSpaces/Wavelets/Examples/Daubechies/Expansion.lean`,
  `ApproximationSpaces/Sequences/Hardy.lean`):
  if every point lies in at most `M` of the sets `I_i`, then `∑_i ∫_{I_i} F ≤ M ∫ F`
  (`MeasureTheory.tsum_setLIntegral_le_mul_lintegral`); `ℓ_q(ℤ)` norms are invariant under
  shifts (`ENNReal.lqNorm_comp_add_int`).
* **Derivatives of exponential sums in a real variable**
  (`FunctionSpaces/Wavelets/Examples/Daubechies/FilterIdentities.lean`):
  `(d/dt)^l ∑_i a_i e^(b_i t) = ∑_i a_i b_i^l e^(b_i t)` for `t ∈ ℝ`
  (`Daubechies.iteratedDeriv_sum_mul_cexp`); Mathlib has these derivatives for a complex variable.
* **Distributions and Schwartz functions** (`FunctionSpaces/Analysis/Fourier/SchwartzCutoff.lean`):
  directional derivatives commute on Schwartz functions and on test functions
  (`SchwartzMap.lineDerivOp_comm`, `TestFunction.lineDerivOp_comm`), and a directional derivative
  commutes with every iterated one as soon as two of them commute
  (`LineDeriv.lineDerivOp_iteratedLineDerivOp_comm_of`); the transpose formulas
  `∂^v T(φ) = (-1)^k T(∂^v φ)` for distributions and tempered distributions
  (`Distribution.iteratedLineDerivOp_apply_apply`,
  `TemperedDistribution.iteratedLineDerivOp_apply_apply`) and the iterated derivative of a
  Schwartz function as a tempered distribution
  (`TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq`); the cut-offs
  `χ(x/(n+1)) u(x)` of a Schwartz function converge to it in the Schwartz space
  (`Rd.tendsto_cutoffMul`), so tempered distributions are determined by test functions
  (`Rd.eq_zero_of_testSchwartz`).
* **The convolution theorem on `L_2`** (`FunctionSpaces/Rd/Sobolev/SobolevTwoLittlewoodPaley.lean`):
  for integrable `K` and `f ∈ L_2(V)`, `𝓕(K ⋆ f) = 𝓕K · 𝓕f` almost everywhere, with Plancherel's
  Fourier transform on `L_2` (`Rd.fourier_convLp`), from the multiplication formulas
  `∫ 𝓕u · g = ∫ u · 𝓕g` and `∫ 𝓕⁻u · g = ∫ u · 𝓕⁻g` for Schwartz `u` and integrable `g` (Mathlib's
  `VectorFourier.integral_fourierIntegral_smul_eq_flip`, in the `𝓕` form
  `Rd.integral_fourier_smul_eq_of_integrable`, `Rd.integral_fourierInv_smul_eq_of_integrable` of
  `FunctionSpaces/Analysis/Fourier/LittlewoodPaleyKernels.lean`; Mathlib's
  `SchwartzMap.integral_fourier_smul_eq` and `SchwartzMap.integral_fourierInv_smul_eq` are the forms
  for two Schwartz functions). Mathlib has the convolution theorem for integrable functions
  (`Real.fourier_bilin_convolution_eq`) and for Schwartz functions.
* **Temperate weights times `L_p` functions**
  (`FunctionSpaces/Rd/Sobolev/SobolevTwoLittlewoodPaley.lean`): if `w` has temperate growth,
  `g ∈ L_p(V)` and `w g ∈ L_q(V)`, then the product of `w` with the tempered distribution of `g` is
  the tempered distribution of `w g` (`Rd.smulLeftCLM_toTemperedDistribution_eq`), and an identity
  `w G = H` of tempered distributions with `G ∈ L_p(V)`, `H ∈ L_q(V)` holds almost everywhere
  (`Rd.ae_eq_of_smulLeftCLM_eq`).
* **`H^1` by derivatives in `L_2`** (`FunctionSpaces/Rd/Sobolev/SobolevTwoLittlewoodPaley.lean`):
  for `f ∈ L_2(V)`, Mathlib's `TemperedDistribution.MemSobolev 1 2 f` holds iff every directional
  derivative `∂_v f` of the tempered distribution `f` is an `L_2` function (`Rd.memSobolevW_one_iff`
  with `Rd.memSobolevW_iff_tempered`); the derivatives along one orthonormal basis `(e_i)` suffice
  (`Rd.memSobolev_one_two_of_lineDerivOp_eq`), and
  `(2π)² ‖J_1 f‖_2² = (2π)² ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²` (`Rd.lintegral_besselWeight_one_sq_eq`,
  `Rd.enorm_besselPotential_one_sq_eq`). Mathlib has `∂_v : H^s → H^{s-1}`
  (`TemperedDistribution.MemSobolev.lineDerivOp`); the converse at `s = 1` is new, and these results
  belong next to it in `Mathlib/Analysis/Distribution/Sobolev.lean`.
* **The inverse Fourier transform on `L_1 ∩ L_2` and Rellich's theorem**
  (`FunctionSpaces/Rd/Sobolev/RellichCompactness.lean`): for an integrable `h ∈ L_2(V)`, Mathlib's
  `L_2` inverse Fourier transform of `h` is the pointwise inverse Fourier integral almost
  everywhere (`Rd.fourierInv_Lp_ae_eq_of_integrable`). Mathlib has the `L_1` inverse transform
  (`Real.Lp.fourierTransformInv`) and the `L_2` inverse transform, and identifies the two on
  Schwartz functions (`SchwartzMap.toLp_fourierInv_eq`); this lemma identifies them on
  `L_1 ∩ L_2`. For every bounded `Ω ⊆ V`, the restriction
  from Mathlib's `H^{1,2}(V, ℂ)` to `L_2(Ω)` is a compact operator
  (`Rd.isCompactOperator_restr_toL2`).
* **Inclusions and derivatives of Mathlib's Sobolev spaces `H^s`**
  (`FunctionSpaces/Rd/Sobolev/SobolevScale.lean`): for every real `s`, the inclusion
  `H^{s,2}(V, ℂ) → H^{t,2}(V, ℂ)`, `t ≤ s`, as a continuous linear map of norm at most `1` that
  keeps the distribution (`Rd.sobolevInclusion`), the `L_2` function of an element of
  `H^{s,2}(V, ℂ)` for `s ≥ 0` (`Rd.sobolevToL2`), the derivative
  `∂_v : H^{s+1,2}(V, ℂ) → H^{s,2}(V, ℂ)` as a continuous linear map of norm at most `2π ‖v‖`
  (`Rd.sobolevLineDeriv`), and the identity
  `(2π)² ‖U‖²_{s+1} = (2π)² ‖U‖²_s + ∑_i ‖∂_{e_i} U‖²_s` for an orthonormal basis `(e_i)`
  (`Rd.sq_norm_eq_add_sum_sobolevLineDeriv`); the inclusion of `H^{s,2}` into itself is the
  identity (`Rd.sobolevInclusion_self`), the `L_2` functions of `H^{0,2}(V, ℂ)` are all of
  `L_2(V)` (`Rd.sobolevToL2_zero_surjective`), convolution with an integrable kernel acts on
  every `H^{s,2}(V, ℂ)` (`Rd.sobolevConv`), and convolution with the dilates of a kernel of
  integral `1` converges to the identity in `H^{s,2}(V, ℂ)` (`Rd.tendsto_sobolevConv_dilate`).
  For `s ≥ 0` an `L_2` function lies in `H^{s,2}(V, ℂ)` as a tempered distribution iff it is the
  `L_2` function of an element (`Rd.memSobolev_bessel_iff_exists_sobolevToL2_eq`). Mathlib has
  `BesselPotentialSpace` and the unbundled `TemperedDistribution.MemSobolev.mono` and
  `MemSobolev.lineDerivOp`, but no maps between the bundled spaces; each map here is an explicit
  Fourier multiplier on the `L_2` functions, with the identification of `𝓕⁻(w 𝓕g)` with
  Mathlib's `w(D) g` (`Rd.fourierMultiplierCLM_toTemperedDistribution_eq`). These belong in
  `Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean`.
* **Evaluation on `H^s` and Sobolev spaces on open sets**
  (`FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean`): for every Schwartz function `φ`,
  `U ↦ U(φ)` is a continuous linear functional on Mathlib's `H^{s,2}(V, ℂ)` (`Rd.besselEvalCLM`,
  `Rd.continuous_toDistr_apply`), which belongs next to `BesselPotentialSpace` in
  `Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean`. Mathlib's Sobolev spaces live
  on the whole space; the Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` of an open set, built
  inside `H^{s,2}(V, ℂ)` as in Chandler-Wilde, Hewett and Moiola, extend them to open sets. Among
  their properties, restriction is an isometry of `H̃^1(Ω)` onto `H^1_0(Ω)` for every open `Ω`
  (`Rd.tildeEquivZeroBoundary`), a form with constant `1` of the identity
  `H̃^1(Ω) = H^1_0(Ω)` that McLean (Theorem 3.33) proves on Lipschitz domains up to equivalence
  of norms. A general `L_p` fact proved there has no Mathlib counterpart: if `a` vanishes almost
  everywhere outside a measurable set `S` and `b` almost everywhere on `S`, then
  `‖a‖_p ≤ ‖a + b‖_p` in every `Lp E p μ` (`Rd.norm_le_norm_add_of_ae_eq_zero`), which belongs
  next to `Lp.norm_le_norm_of_ae_le` in `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`.
* **Duality of Bessel potential spaces** (`FunctionSpaces/Domains/Sobolev/SobolevDuality.lean`): the
  inner product of Mathlib's `H^{s,2}(V, ℂ)` is that of the `L_2` functions `J_s U`
  (`Rd.besselPotential_inner_toLp_toLp`); the isometry `J_{2s} : H^{s,2} → H^{-s,2}`
  (`Rd.besselShift`) and the pairing `⟪J_{-s} W, J_s U⟫_{L_2}` of `H^{-s,2}` and `H^{s,2}`
  (`Rd.sobolevPairing`), which extends the action of distributions on test functions
  (`Rd.sobolevPairing_ofTest_left`); `⟪U, φ⟫ = conj ((J_{2s} U)(φ))` for real test functions `φ`
  (`Rd.inner_ofTest_eq`). These belong in
  `Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean`. Also the reality of the Bessel
  potential of real Schwartz functions (`Rd.conj_besselSchwartz_apply`), and the conjugation
  identities `conj (𝓕 f) = 𝓕⁻(conj f)` and `conj (𝓕⁻ f) = 𝓕(conj f)` for `f : V → ℂ`
  (`Rd.conj_fourier_apply`, `Rd.conj_fourierInv_apply` in
  `FunctionSpaces/Analysis/Fourier/LittlewoodPaleyKernels.lean`), next to
  `Real.fourierInv_eq_fourier_neg` in `Mathlib/Analysis/Fourier/FourierTransform.lean`.
* **`H^{s,p} = F^s_{p,2}` and `W^m_p = H^{m,p}`**
  (`FunctionSpaces/Rd/BesselPotentials/BesselPotentialLifting.lean`): for `dim V ≥ 1` and
  `1 < p < ∞`, every `f ∈ F^s_{p,2}(V)` lies in Mathlib's `H^{s,p}(V)`
  (`TemperedDistribution.MemSobolev s p`, `BesselPotentialSpace`) for every real `s`
  (`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`), an `f ∈ L_p(V)` lies in `F^s_{p,2}(V)` iff
  it lies in `H^{s,p}(V)`, for every real `s` (`Rd.memTriebelLizorkin_iff_memSobolev_bessel`), for
  `s ≥ 0` every element of `H^{s,p}(V)` is an `L_p` function in `F^s_{p,2}(V)`
  (`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`), and `W^m_p(V) = H^{m,p}(V)`, Calderón's
  theorem (`Rd.memSobolevW_iff_memSobolev_bessel`), with existential constants. Mathlib has
  `H^{s,p}` with `∂_v : H^{s,p} → H^{s-1,p}` (`TemperedDistribution.MemSobolev.lineDerivOp`); this
  project identifies it with `F^s_{2,2}` for `p = 2` by Plancherel
  (`FunctionSpaces/Rd/Sobolev/SobolevTwoLittlewoodPaley.lean`), and for all `1 < p < ∞` through its
  vector-valued singular integrals and Triebel–Lizorkin spaces, so the identity would follow them
  into Mathlib. Three general facts on Mathlib's Fourier multipliers are short and self-contained:
  an even multiplier acts on tempered distributions by the transpose, `(m(D) T)(u) = T(m(D) u)`
  (`Rd.fourierMultiplierCLM_apply_apply_of_even`, in
  `FunctionSpaces/Rd/Sobolev/SobolevTwoLittlewoodPaley.lean`, with the Bessel case
  `Rd.besselPotential_apply_apply`), every multiplier commutes with translations of Schwartz
  functions and an even one with reflections (`Rd.fourierMultiplierCLM_compSubConstCLM`,
  `Rd.fourierMultiplierCLM_schwartzReflect`, with the Fourier transform of a translate
  `Rd.fourier_compSubConstCLM_apply`); they belong in
  `Mathlib/Analysis/Distribution/FourierMultiplier.lean` and next to `SchwartzMap.compSubConstCLM`.
* **Symbols of order `σ`** (`FunctionSpaces/Rd/FourierMultipliers/SymbolKernels.lean`): the
  predicate `Rd.HasSymbolGrowth σ m`, Hörmander's class `S^σ_{1,0}` with the bracket weight
  `(1 + ‖ξ‖²)^{(σ - k)/2}`, beside Mathlib's `Function.HasTemperateGrowth`, with Schwartz
  functions as symbols of every order (`Rd.hasSymbolGrowth_schwartz`), symbols of temperate
  growth (`Rd.HasSymbolGrowth.hasTemperateGrowth`), products (`Rd.HasSymbolGrowth.mul`) and the
  Bessel weight (`Rd.hasSymbolGrowth_besselWeight`); it belongs in
  `Mathlib/Analysis/Distribution/TemperateGrowth.lean`. The derivative bounds for powers of the
  Japanese bracket behind the Bessel weight
  (`ContinuousLinearMap.norm_iteratedFDeriv_le_one_add_norm_sq_rpow`,
  `ContinuousLinearMap.exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow`,
  `Rd.hasFDerivAt_one_add_norm_sq_rpow`, `Rd.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le`)
  are mirrored from TauCeti (`TauCeti/Analysis/SpecialFunctions/JapaneseBracket/Deriv.lean`,
  commit `b61a90d`, Apache-2.0), which imports only Mathlib; they belong next to
  `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean`, and an upstream version should come
  from TauCeti.
* **Convolution with a Schwartz kernel as a Fourier multiplier**
  (`FunctionSpaces/Rd/TriebelLizorkin/TriebelLizorkinDistributions.lean`): for Schwartz functions
  `η`, `φ`, `SchwartzMap.convolution (mul ℂ ℂ) η φ = SchwartzMap.fourierMultiplierCLM ℂ (𝓕η) φ`
  (`Rd.fourierMultiplierCLM_fourier_eq_convolution`), and for `G ∈ L_r`, `1 ≤ r < ∞`,
  `(𝓕η)(D) G = η ⋆ G` as tempered distributions (`Rd.fourierMultiplierCLM_fourier_toLp_eq_conv`,
  by density of the Schwartz functions in `L_r`). Mathlib defines the convolution of Schwartz
  functions through the Fourier transform and identifies it with the convolution integral
  (`SchwartzMap.convolution`, `SchwartzMap.fourier_convolution`,
  `SchwartzMap.convolution_apply`); the identification with
  `SchwartzMap.fourierMultiplierCLM ℂ (𝓕η)` and its extension to `L_r` and to
  `TemperedDistribution.fourierMultiplierCLM` are missing. They belong in
  `Mathlib/Analysis/Distribution/FourierMultiplier.lean`.
* **Mihlin multipliers and Bessel potential spaces for every `p`**
  (`FunctionSpaces/Rd/FourierMultipliers/MihlinMultipliers.lean`,
  `BesselPotentialMultipliers.lean`): for `1 < p < ∞`, a symbol of order `0` is a bounded Fourier
  multiplier on `L_p` (`Rd.exists_fourierMultiplier_eq_of_hasSymbolGrowth`), and a symbol of
  order `σ` maps Mathlib's `H^{s,p}` into `H^{s-σ,p}`
  (`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_hasSymbolGrowth`), with the
  inclusions `H^{s,p} ⊆ H^{s',p}`, derivatives, the Laplacian and the derivative characterisation
  of `H^{s+1,p}` (`TemperedDistribution.MemSobolev.mono_of_one_lt`, `.lineDerivOp_of_one_lt`,
  `.laplacian_of_one_lt`, `TemperedDistribution.memSobolev_add_one_iff`). Mathlib proves these
  for `p = 2` only. TauCeti is prior work and the likely upstream source: it proves Mihlin's
  theorem for Mihlin's condition with finitely many derivatives
  (`TauCeti.exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le`,
  `TauCeti/Analysis/Fourier/MihlinHormander.lean`), and the statements of `mono_of_one_lt`,
  `lineDerivOp_of_one_lt` and the derivative characterisation, with the proofs of the latter, are
  mirrored from `TauCeti/Analysis/Distribution/Sobolev.lean` (commit `b61a90d`, Apache-2.0). The
  project's proofs go through `H^{s,p} = F^s_{p,2}` for tempered distributions
  (`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`) instead of TauCeti's Calderón–Zygmund
  theory.
* **The area formula for Lipschitz graphs**
  (`FunctionSpaces/Domains/Lipschitz/LipschitzGraphArea.lean`): Mathlib has the area formula for
  linear maps, `μHE[dim U] (f '' s) = normDet f · vol(s)`
  (`LinearMap.euclideanHausdorffMeasure_image`,
  `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`, with `LinearMap.normDet` in
  `Mathlib/Analysis/InnerProductSpace/NormDet.lean`), and lacks the one for Lipschitz maps
  (2026-10-14). Two steps are general: a map that is `K`-Lipschitz on `s` satisfies
  `μHE[d] (f '' s) ≤ K^d μHE[d] s` (`LipschitzOnWith.euclideanHausdorffMeasure_image_le_pow_mul`,
  next to `Isometry.euclideanHausdorffMeasure_image`), and images under two maps with nearby
  increments have comparable measures (`Rd.euclideanHausdorffMeasure_image_le_of_near`). For the
  graph `γ(x') = x' + φ(x') e` of a Lipschitz function over the hyperplane `H = e^⊥`, the area
  formula `μHE[n-1] (γ '' A) = ∫_A √(1 + ‖∇φ‖²)` with its measure and integral forms
  (`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphMap_image`,
  `Rd.LipschitzGraph.map_graphMap_withDensity`, `Rd.LipschitzGraph.lintegral_graphMap`). For Mathlib
  the graph would be stated for a Lipschitz function on a Euclidean space without the structure
  `Rd.LipschitzGraph`.
* **The boundary of a bounded Lipschitz domain is a null set**
  (`FunctionSpaces/Domains/Lipschitz/SurfaceMeasure.lean`): `volume (frontier Ω) = 0`
  (`Rd.BoundedLipschitzDomain.volume_frontier`), since the boundary has finite `μHE[n-1]`-measure
  and hence `μHE[n]`-measure zero (`MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top`).
  In Mathlib it would follow from the finiteness of `μHE[n-1]` on the graph of a Lipschitz
  function over a bounded subset of a hyperplane, a consequence of
  `LipschitzOnWith.euclideanHausdorffMeasure_image_le_pow_mul`.
* **Preconnected sets cross the frontier** (`FunctionSpaces/Domains/Lipschitz/BoundaryLayers.lean`):
  a preconnected set that meets `U` and its complement meets `frontier U`
  (`Rd.inter_frontier_nonempty_of_isPreconnected`), from Mathlib's
  `IsPreconnected.subset_or_subset`; the segment form for a step `x ↦ x + h` that leaves or enters
  `U` is `Rd.exists_mem_frontier_of_mem_switchSet`. Mathlib states the case of a preconnected
  whole space (`nonempty_frontier_iff`). In Mathlib the statement would read
  `IsPreconnected.inter_frontier_nonempty (hS : IsPreconnected S) …`.
* **Bounded Lipschitz domains from local graphs**
  (`FunctionSpaces/Domains/Lipschitz/LocalLipschitzGraphs.lean`): the set-level definition
  (`Rd.IsLipschitzDomainAt`, `Rd.IsBoundedLipschitzDomain`), the ball
  (`Rd.isBoundedLipschitzDomain_ball`) and every bounded open convex set
  (`Rd.isBoundedLipschitzDomain_of_convex`, `FunctionSpaces/Domains/Lipschitz/ConvexDomains.lean`)
  are candidates only together with TauCeti's definitions of
  Lipschitz domains (`Set.IsLipschitzDomain`, `Set.IsLipschitzChart`), whose shape they would take.
* **The smooth cut-off** (`FunctionSpaces/Domains/Manifolds/SmoothLocalGraphs.lean`): the product
  of a `C^n` function `b` with a function `C^n` on an open set containing its closed support
  (`tsupport b`) is `C^n` (`Rd.contDiff_mul_of_tsupport_subset`), the flat analogue of Mathlib's
  `ContMDiffOn.smul_section_of_tsupport`, and a function smooth on the ball `B(0, r)` of a
  finite-dimensional inner product space agrees on `B(0, r/4)` with a smooth Lipschitz function on
  the whole space (`Rd.exists_contDiff_lipschitzWith_eqOn_ball`).
* **Smoothness of parametric integrals**
  (`FunctionSpaces/Rd/Sobolev/DivergenceKernels.lean`): if `(x, t) ↦ F(x, t)` is smooth on
  `H × ℝ`, `H` finite dimensional, then `x ↦ ∫_a^b F(x, t) dt` is smooth
  (`intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff`), with the derivative under
  the integral sign for jointly `C^1` integrands
  (`intervalIntegral.hasFDerivAt_integral_of_contDiff`,
  `intervalIntegral.fderiv_integral_apply_of_contDiff`). Mathlib has the derivative at one point
  under a domination hypothesis (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`)
  and the continuity (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`); the
  smoothness follows by induction on the order, with all target spaces in one universe
  (`intervalIntegral.contDiff_parametric_intervalIntegral_of_contDiff_aux`), reached through `ULift`
  as in `contDiffOn_convolution_right_with_param`.
* **Weak derivatives on open sets** (`FunctionSpaces/Rd/Sobolev/WeakDerivatives.lean`,
  `FunctionSpaces/Rd/SingularIntegrals/ConvolutionAdjoint.lean`): for Mathlib's distributions
  `𝓓'(Ω, ℂ)`, the integration by parts against smooth compactly supported complex functions with
  support in `Ω` (`Rd.HasWeakLineDeriv.integral_mul_eq`, through
  `Rd.exists_testSchwartz_eq_of_tsupport_subset`), the product rule with smooth real functions
  (`Rd.HasWeakLineDeriv.mul_contDiff`), and `(η ⋆ g)(x) = ((∂^v η) ⋆ f)(x)` for a compactly
  supported Schwartz `η` whose reflected translate lies in `Ω`
  (`Rd.conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv`); these belong next to the weak
  derivatives of the Sobolev library prepared for Mathlib.
* **Gauss–Green on Lipschitz graph domains**
  (`FunctionSpaces/Domains/Sobolev/LipschitzGraphGreen.lean`): for a Lipschitz graph domain
  `Ω = {φ < ⟪·, e⟫}`, Fubini in the product coordinates `(x', t) ↦ x' + t e` and
  `(x', t) ↦ γ(x') + t e` of `H × ℝ` (`Rd.LipschitzGraph.setIntegral_domain_eq`,
  `Rd.LipschitzGraph.setIntegral_domain_eq_graphMap`), the vertical and horizontal directions
  (`Rd.LipschitzGraph.setIntegral_lineDeriv_e`, and
  `Rd.LipschitzGraph.setIntegral_lineDeriv_hyperplane`, a Leibniz rule with a Lipschitz lower limit
  in integrated form), and the divergence theorem `∫_Ω ∂_v g = ∫_Γ g ⟪v, ν⟫ dμHE[n-1]` for compactly
  supported `C^1` functions (`Rd.LipschitzGraph.setIntegral_lineDeriv_eq`,
  `Rd.LipschitzGraph.setIntegral_lineDeriv_eq_surface`). Mathlib's divergence theorem is the one on
  boxes (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`, checked 2026-10-22);
  these results extend it to Lipschitz graph domains. Two general facts are short: the product
  rule for line derivatives
  (`Rd.lineDeriv_mul`, next to `DifferentiableAt.lineDeriv_eq_fderiv`), and the ray integral
  `∫_0^∞ g(y + t w) dt` of a compactly supported `C^1` function is differentiable with bounded
  derivative and derivative `-g` along the ray (`Rd.hasFDerivAt_rayIntegral`,
  `Rd.fderiv_rayIntegral_self`, `Rd.exists_norm_fderiv_rayIntegral_le`). The density of the
  compactly supported Schwartz functions in Mathlib's `H^{s,2}(V, ℂ)` (`Rd.denseRange_ofSchwartz`,
  `Rd.dense_ofSchwartz_hasCompactSupport`,
  `FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean`) belongs in
  `Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean`.
* **Integration by parts in `H^1`** (`FunctionSpaces/Domains/Sobolev/LipschitzDomainGreen.lean`):
  for `U, W ∈ H^{1,2}(V, ℂ)` and every direction `v`, `∫ (∂_v U) W + U ∂_v W = 0`
  (`Rd.integral_weakDeriv_mul_add_eq_zero`), and the weak derivatives of `H^1(V)` are local
  (`Rd.weakDerivL2_ae_eq_of_ae_eq`,
  `FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean`); both belong next to the
  density of the Schwartz functions in
  `Mathlib/Analysis/FunctionalSpaces/BesselPotentialSpace.lean`. Two general facts are short:
  integrals over two sets that agree inside a set `B` agree for functions vanishing outside `B`
  (`Rd.setIntegral_eq_of_inter_eq`), and line derivatives vanish outside the closed support
  (`Rd.lineDeriv_eq_zero_of_notMem_tsupport`).
* **Mollification in `H^1`** (`FunctionSpaces/Rd/SingularIntegrals/ConvolutionAdjoint.lean`,
  `FunctionSpaces/Domains/Traces/TraceKernel.lean`): if `g = ∂^v f` weakly on `V` for `f ∈ L_p(V)`,
  `g ∈ L_r(V)`, `1 ≤ p, r < ∞`, then `η ⋆ g = ∂^v (η ⋆ f)` weakly for every Schwartz
  function `η` (`Rd.hasWeakLineDeriv_convLp`); hence the mollified `η_c ⋆ U` converge to `U` in
  `H^{1,2}(V, ℂ)` as `c → ∞` for `∫ η = 1` (`Rd.tendsto_of_toL2_eq_convLp`), and the elements of
  `H^{1,2}(V, ℂ)` vanishing outside a compact subset of an open set `Ω` lie in the closure of the
  test functions of `Ω` (`Rd.mem_tildeSpace_of_isCompact`), the case `s = 1` of the same statement
  for `H^{s,2}(V, ℂ)`, `s ≥ 0` (`Rd.mem_tildeSpace_of_isCompact_of_nonneg`,
  `FunctionSpaces/Domains/Sobolev/TildeSpaceSupport.lean`). Mathlib's convolution files cover the
  smoothness of `η ⋆ f`; these statements add its weak derivatives.
* **The Gagliardo–Nirenberg–Sobolev inequality for weak derivatives**
  (`FunctionSpaces/Rd/Sobolev/GagliardoNirenbergSobolev.lean`): Mathlib's inequality
  `‖f‖_{p'} ≤ C ∑_k ‖∂_{e_k} f‖_p` for every `f ∈ L_p(V)` with weak derivatives along the
  orthonormal basis `Rd.gridBasis`, by mollification, cut-off and Fatou's lemma
  (`Rd.eLpNorm_le_of_hasWeakLineDeriv`), a candidate together with TauCeti's
  `W1p0.sobolevEmbeddingL`. Fatou's lemma with convergent bounds
  `B_i → b` (`MeasureTheory.eLpNorm_le_of_ae_tendsto_of_tendsto`) generalises Mathlib's
  `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`, the case of a constant bound, and belongs next to it;
  the bound `‖L‖ ≤ ∑_i ‖L b_i‖` of a continuous linear map through an orthonormal basis
  (`ContinuousLinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`) belongs next to
  `OrthonormalBasis.sum_repr'`.
* **Weak derivatives under Lipschitz changes of variables**
  (`FunctionSpaces/Rd/Sobolev/WeakDerivativeChangeOfVariables.lean`): the line derivative of a
  compactly supported Lipschitz function is integrable and integrates to zero
  (`Rd.integrable_lineDeriv`, `Rd.integral_lineDeriv_eq_zero`,
  `Rd.integral_lineDeriv_eq_zero_complex`, next to `LipschitzWith.integral_lineDeriv_mul_eq` in
  `Mathlib/Analysis/Calculus/Rademacher.lean`), and
  `D(K ⋆ h)(x) v = (K ⋆ g)(x)` for a smooth compactly supported `K` and `g = ∂_v h` weakly
  (`Rd.fderiv_conv_apply_eq_conv`); Lipschitz functions are weakly differentiable
  (`Rd.hasWeakLineDeriv_of_lipschitzWith`), weak derivatives are linear in the direction
  (`Rd.HasWeakLineDeriv.sum_smul_dir`), satisfy the product rule with cutoffs
  (`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`, in
  `FunctionSpaces/Rd/Sobolev/WeakDerivatives.lean`), are approximated by mollification on open sets
  (`Rd.exists_tendsto_contDiff_of_hasWeakLineDeriv`) and satisfy the chain rule for Lipschitz
  measure-preserving maps (`Rd.HasWeakLineDeriv.comp_lipschitzWith`), candidates together with
  TauCeti's `LocallyLipschitzOn.hasWeakLineDerivOn` and `HasWeakFDerivOn.comp_measurePreserving`.
  Four measure-theoretic facts of the file are short: `‖h ∘ Φ‖_{L_p(U)} ≤ ‖h‖_{L_p(O)}` for a
  measure-preserving `Φ` with `Φ(U) ⊆ O` (`Rd.eLpNorm_comp_le_of_mapsTo`, next to
  `eLpNorm_comp_measurePreserving`), locally integrable functions with compact support are
  integrable (`MeasureTheory.LocallyIntegrable.integrable_of_hasCompactSupport`, next to
  `Continuous.integrable_of_hasCompactSupport`), finite sums of locally integrable functions on a
  set are locally integrable on it (`Rd.locallyIntegrableOn_sum_smul`, next to
  `locallyIntegrable_finsetSum'`), and `‖c u‖_{L_p} ≤ C ‖u‖_{L_p}` for a measurable `|c| ≤ C`
  and every `u` (`MeasureTheory.eLpNorm_mul_le_of_forall_norm_le`, next to
  `eLpNorm_le_mul_eLpNorm_of_ae_le_mul'`).
* **The smooth step and balls** (`FunctionSpaces/Domains/Extension/HalfSpaceReflection.lean`): the
  derivative of `Real.smoothTransition` vanishes outside `[0, 1]` and is bounded
  (`Real.smoothTransition.deriv_eq_zero_of_one_lt`, `Real.smoothTransition.deriv_eq_zero_of_neg`,
  `Real.smoothTransition.exists_abs_deriv_le`), and a function integrable on every ball around a
  point is locally integrable (`MeasureTheory.locallyIntegrable_of_forall_integrableOn_ball`).
* **The Leibniz rule for weak derivatives**
  (`FunctionSpaces/Rd/Sobolev/WeakDerivativeLeibniz.lean`): derivatives of every order of `χ f`
  for a smooth compactly supported `χ`, with the bound `C_k(χ) = 2^k sup_x ∑_{j ≤ k} ‖D^j χ(x)‖`
  (`Rd.exists_hasWeakLineDeriv_mul_of_tsupport_subset`), a candidate together with TauCeti's
  `Wkp.exists_value_ae_eq_mul_of_contDiffOn`.
* **Weighted dilation averages** (`FunctionSpaces/Domains/Extension/HigherDivergenceKernels.lean`):
  `∫_a^b w(s) G_{e^s} ds` is smooth with integral `(∫_a^b w) ∫ G` (`Rd.weightedDilation`,
  `Rd.contDiff_weightedDilation`, `Rd.integral_weightedDilation`).
* **Weighted dilation averages as divergences** (same file): `A_w G = ∑_i ∂_{e_i} A_W(⟪e_i, ·⟫ G)`
  for `∫_a^b w = 0` with the anti-weight `W` (`Rd.weightedDilation_eq_sum_fderiv`,
  `Rd.antiWeight`).
* **Weighted dilation averages as derivatives of order `m`** (same file): `A_w G = ∑_i ∂^{e_i} K_i`
  for weights with `m` vanishing moments (`Rd.weightedDilation_eq_sum_iteratedLineDeriv`,
  `Rd.higherDivKernel`), the kernels of Calderón's and Rychkov's extension.
