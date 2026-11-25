# Tools from analysis

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Tools from analysis*,
chapters *Convolution and the Fourier transform on `ℝ^d`*, *Maximal functions*, *Interpolation of
operators* and *Gelfand triples*; the other tools are cited where they are used, in *Besov spaces
and their embeddings*, *Polynomial approximation on intervals*, *Approximation on the cube*,
*Besov spaces on `ℝ^d`*, *Tensor Daubechies wavelets on `ℝ^d`*, *Lipschitz domains*, *Traces on
Lipschitz domains* and *Fractional Sobolev spaces on Lipschitz domains*.

This block holds the folder `FunctionSpaces/Analysis/`, whose files import only Mathlib,
`ApproximationSpaces` and each other: `L_p` norms, the quasi-norms of `L_p` for every
`0 < p ≤ ∞`, the inclusion `L_r ↪ L_p` and bounded continuous functions on finite measure
spaces, Young's inequality on measurable groups, mixed norms `L_p(ℓ_q)` and `ℓ_q(L_p)` on every
measure space, weak type, the layer cake formula, Marcinkiewicz interpolation, `L_p` norms by
duality, `L_p` norms on `ℝ^d` through slices in one coordinate and a fractional Hardy inequality
on `(0, 1]`; differences on additive monoids, the translation algebra, moduli of smoothness on
subsets and under linear and affine changes of variables; convolution, approximate identities,
the Littlewood–Paley kernels and test functions on `ℝ^d`; dyadic cubes and cells, the
Hardy–Littlewood maximal function, the Calderón–Zygmund decomposition, also for functions with
values in a normed space, and the Fefferman–Stein inequality; the pivot dual of a bounded
operator between Hilbert spaces, which makes `L_2` the pivot space of the Gelfand triples of
Sobolev spaces, and a test for dense range in `L_2(μ)`; componentwise operators on finite `L_2`
sums of normed and Hilbert spaces, with their kernels, ranges, orthogonal complements and duals,
on which the vector-valued Sobolev spaces rest. The `L_p` norms are handled through integrals of
powers (`MeasureTheory.eLpNorm_rpow_eq`).

## Main results

* **Mixed norms.** Let `(X, μ)` be a measure space and `g_i : X → [0, ∞]` measurable functions
  indexed by a countable set, with the mixed norms
  `‖g‖_{L_p(ℓ_q)} = ‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_p` and `‖g‖_{ℓ_q(L_p)} = ‖(‖g_i‖_p)_i‖_{ℓ_q}`.
  For `0 < p < ∞`, `‖g‖_{L_p(ℓ_p)} = ‖g‖_{ℓ_p(L_p)}`
  (`MeasureTheory.eLpNorm_lqNorm_eq_lqNorm_eLpNorm`); for `0 < p ≤ q ≤ ∞`,
  `‖g‖_{ℓ_q(L_p)} ≤ ‖g‖_{L_p(ℓ_q)}` (`MeasureTheory.lqNorm_eLpNorm_le_eLpNorm_lqNorm`); for
  `0 < q ≤ p < ∞`, `‖g‖_{L_p(ℓ_q)} ≤ ‖g‖_{ℓ_q(L_p)}`
  (`MeasureTheory.eLpNorm_lqNorm_le_lqNorm_eLpNorm`). Hence for `1 ≤ p < ∞` and `1 ≤ q ≤ ∞`,
  `‖g‖_{ℓ_{max(p,q)}(L_p)} ≤ ‖g‖_{L_p(ℓ_q)} ≤ ‖g‖_{ℓ_{min(p,q)}(L_p)}`
  (`MeasureTheory.lqNorm_max_le_eLpNorm_lqNorm`, `MeasureTheory.eLpNorm_lqNorm_le_lqNorm_min`),
  also for the weighted families `w_j ‖u_j‖` of functions `u_j` with values in a normed group
  (`MeasureTheory.lqNorm_max_weighted_le`, `MeasureTheory.eLpNorm_lqNorm_weighted_le_min`), such
  as `2^(js) ‖u_j‖` (`MeasureTheory.lqNorm_max_dyadicWeight_le`,
  `MeasureTheory.eLpNorm_lqNorm_dyadicWeight_le_min`). The tools are Minkowski's inequality for
  series in `L_p`, `‖∑_i g_i‖_p ≤ ∑_i ‖g_i‖_p` for `1 ≤ p ≤ ∞` (`MeasureTheory.eLpNorm_tsum_le`),
  and Minkowski's integral inequality for `ℓ_u`-valued functions,
  `‖(∫ g_i dμ)_i‖_{ℓ_u} ≤ ∫ ‖(g_i(x))_i‖_{ℓ_u} dμ(x)` for `1 ≤ u ≤ ∞`
  (`MeasureTheory.lqNorm_lintegral_le`).
* **The Fefferman–Stein inequality.** Let `V` be a finite-dimensional real inner product space,
  such as `ℝ^d`, and `M` the Hardy–Littlewood maximal operator. For `1 < p < ∞`, `1 < q ≤ ∞` and
  almost everywhere measurable `g_j : V → [0, ∞]`, `j ∈ ℕ`,
  `‖ x ↦ ‖(M g_j(x))_j‖_{ℓ_q} ‖_p ≤ C ‖ x ↦ ‖(g_j(x))_j‖_{ℓ_q} ‖_p` with the explicit constant
  `C = Rd.feffermanSteinConst V p q` (`Rd.feffermanStein`). The case `p < q` rests on a
  vector-valued weak type `(1,1)` (`Rd.volume_lqNorm_maximalFunction_gt_le`), proved with the
  Calderón–Zygmund decomposition on dyadic cubes.
* **The signed Calderón–Zygmund decomposition.** Let `E` be a real normed space, such as `ℂ`,
  and `f : V → E`. For the maximal big dyadic cubes `Q` of a function `G : V → [0, ∞]` at height
  `t`, the good part `czGoodC f` is `f` outside the cubes and the mean `⨍_Q f` on each cube
  (`Rd.czGoodC`), and the bad part `f - czGoodC f` (`Rd.czBadC`) is the sum of the pieces
  `b_Q = 1_Q (f - ⨍_Q f)` (`Rd.czBadPart`, `Rd.hasSum_czBadPart`). Every piece has mean zero
  (`Rd.integral_czBadPart`), and `∑_Q ∫ ‖b_Q‖ ≤ 2 ∫ ‖f‖`
  (`Rd.tsum_lintegral_enorm_czBadPart_le`). If `n = dim V ≥ 1`, `f` is integrable, `t > 0` and
  `G = ‖f‖`, then `‖czGoodC f‖ ≤ 2^n t` almost everywhere and
  `∫ ‖czGoodC f‖² ≤ 2^n t ∫ ‖f‖` (`Rd.ae_enorm_czGoodC_le`, `Rd.lintegral_enorm_czGoodC_sq_le`).
  For a family `(g_j)_j` and `1 ≤ q ≤ ∞` the cubes of `G = ‖(‖g_j‖)_j‖_{ℓ_q}` serve every `g_j`,
  with the same bounds for the pointwise `ℓ_q` norms (`Rd.ae_lqNorm_czGoodC_le`,
  `Rd.lintegral_lqNorm_czGoodC_sq_le`, `Rd.tsum_lintegral_lqNorm_czBadPart_le`).
* **Marcinkiewicz interpolation.** With the Carleson project's definitions of weak type,
  strong type and almost everywhere subadditive operators (`MeasureTheory.HasWeakType`,
  `MeasureTheory.HasStrongType`, `MeasureTheory.AESubadditiveOn`): let `μ` be an s-finite
  measure, `ν` a measure and `1 < p < 2`. If an operator `T` is almost everywhere subadditive
  with constant `A` on `L_1(μ) ∪ L_2(μ)`, of weak type `(1,1)` with constant `C₁` and of strong
  type `(2,2)` with constant `C₂`, and maps `L_p(μ)` to almost everywhere strongly measurable
  functions, then it has strong type `(p,p)` with constant
  `(p (2 A C₁/(p - 1) + 4 A² C₂²/(2 - p)))^(1/p)`
  (`MeasureTheory.hasStrongType_of_hasWeakType_one_of_hasStrongType_two`). For operators on an
  abstract input type with a size `G x` and restrictions to measurable sets (such as families of
  functions with their pointwise `ℓ_2` norms) that are subadditive with constant `1`, satisfy
  `ν{T x > t} ≤ C₁ t⁻¹ ∫ G x dμ` and `∫ (T x)² dν ≤ C₂ ∫ (G x)² dμ`, the bound is
  `‖T x‖_{L_p(ν)} ≤ (p (2 C₁/(p - 1) + 4 C₂/(2 - p)))^(1/p) ‖G x‖_{L_p(μ)}`
  (`MeasureTheory.eLpNorm_le_of_weak_one_strong_two`).
* **Gelfand triples.** Let `X`, `H` be Hilbert spaces over `ℝ` or `ℂ` and `ι : X → H` bounded
  and linear. The pivot dual `ι^♭ : H → X*`, `ι^♭ g = ⟪g, ι ·⟫_H`, is the adjoint of `ι` followed
  by Riesz's isometry, conjugate-linear with `‖ι^♭‖ = ‖ι‖` (`ContinuousLinearMap.pivotDual`,
  `ContinuousLinearMap.pivotDual_apply_apply`, `ContinuousLinearMap.norm_pivotDual`); its kernel
  is `(range ι)^⊥`, so `ι^♭` is injective iff `ι` has dense range
  (`ContinuousLinearMap.ker_pivotDual`, `ContinuousLinearMap.pivotDual_injective_iff`), and
  `ι^♭ ∘ ι` is injective iff `ι` is (`ContinuousLinearMap.pivotDual_comp_injective_iff`). For
  `H = L_2(μ)`, `ι^♭ g v = ∫ conj (g) ι v dμ`
  (`MeasureTheory.L2.pivotDual_apply_apply_eq_integral`). For a locally finite measure `μ` on a
  finite-dimensional real space carried by an open set `U`, a function of `L_p(μ)`, `p ≥ 1`, that
  integrates to zero against the smooth real functions with compact support in `U` vanishes, by
  the fundamental lemma of the calculus of variations
  (`MeasureTheory.Lp.eq_zero_of_forall_integral_contDiff_smul_eq_zero`), so a continuous linear
  map into `L_2(μ)` whose range contains these functions has dense range
  (`MeasureTheory.L2.denseRange_of_forall_contDiff`). The Sobolev spaces on `ℝ^d`, on open sets
  and on the boundary of a bounded Lipschitz domain give their Gelfand triples through
  `ContinuousLinearMap.pivotDual_injective_iff`: each contributes its embedding into `L_2`, the
  dense range of that embedding (on open sets and on the boundary by
  `MeasureTheory.L2.denseRange_of_forall_contDiff`, on `ℝ^d` by the density of the Schwartz
  functions) and the identification of the pivot dual with the pairing of the space of negative
  order (see [Lipschitz domains and traces](DomainsTraces.md)).
* **Finite `L_2` sums.** Let `X`, `Y` be complex normed spaces, `m ∈ ℕ` and
  `X^m = WithLp 2 (Fin m → X)` with `‖x‖² = ∑_i ‖x_i‖²`. A bounded operator `f : X → Y` acts
  componentwise on `X^m` with norm at most `‖f‖`, kernel `(ker f)^m` and range `(range f)^m`,
  isometrically if `f` is isometric and onto if `f` is (`PiLp.compLeftL`,
  `PiLp.norm_compLeftL_le`, `PiLp.ker_compLeftL`, `PiLp.range_compLeftL`,
  `PiLp.norm_compLeftL_apply`, `PiLp.compLeftL_surjective`), and isomorphisms and semilinear
  isometric isomorphisms act as such (`PiLp.congrRightL`, `PiLp.congrRightSL`). For a complex
  inner product space `E`, `(K^m)ᗮ = (Kᗮ)^m` for every subspace `K ⊆ E`
  (`PiLp.orthogonal_piSubmodule`), and for a Hilbert space `E` the dual of `E^m` is `(E^*)^m`
  isometrically, `ℓ ↦ (ℓ ∘ ι_i)_i` for the inclusions `ι_i` of the components
  (`PiLp.strongDualEquiv`, `PiLp.strongDualEquiv_apply`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| `L_p` norms through integrals of powers | ✅ | ✗ | `Analysis/Lp/LintegralForm` |
| Multiplication by an indicator as an operator on `L_p`, its idempotence, integrals over a set as `L_2` pairings, zero extension from `L_p(μ|_s)`, restriction to a smaller set | ✅ | ✗ | `Analysis/Lp/IndicatorOperator` |
| Inclusion `L_r ↪ L_p`, as a linear map for every `0 < p ≤ r ≤ ∞` (injective, composing, keeping every quasi-norm; the inclusion `L_∞ ↪ L_p` and differences with essentially bounded functions; the Hölder exponent `1/p - 1/r ≥ 0`) and as a bounded map for `p ≥ 1`, bounded continuous functions in `L_p`, their sup-norm bounds in `L_∞` and in every `L_p` | ✅ | ✗ | `Analysis/Lp/Inclusion`, `Analysis/Lp/BoundedContinuous` |
| Interpolation `L_p`–`L_∞` | ✅ | ✗ | `Analysis/Lp/Interpolation` |
| `L_p` for every `0 < p ≤ ∞`: the `ρ`-triangle inequality with `ρ = min(1, p)` and Mathlib's `inhmgELpNorm`, Fatou's lemma for telescoping sums in every `L_r`, also in the `r`-th power for `r ≤ 1`, series in `L_p` and their absolute convergence almost everywhere, the almost everywhere bound by the `L_∞` quasi-norm, the sup-norm bootstrap of Ditzian–Prymak, the transfer of near-best sequences from `L_p` to `L_r` and its weighted `ℓ_q` form, the quasi-norm facts of `Lp` and the first moment method | ✅ | ✗ | `Analysis/Lp/QuasiNorm` |
| Young's inequality on measurable groups, weighted Jensen inequality, weighted averages in `L_p` | ✅ | ✗ | `Analysis/Lp/Young` |
| Mixed norms `L_p(ℓ_q)` and `ℓ_q(L_p)`: Minkowski's inequality for `ℓ_u`-valued functions, comparison, limits of pointwise bounds, terms set to zero and tails, Cauchy sequences from tails, the first weighted term split off, triangle inequality, homogeneity and monotonicity of mixed norms of families and of dyadically weighted families, cancellation in Hölder's inequality and conjugate exponents | ✅ | ✗ | `Analysis/Lp/MixedNorms` |
| The distribution function, weak `L_p` norms, operators of weak and strong type and almost everywhere subadditive operators, with the definitions of the Carleson project, and their elementary properties | ✅ | ✗ | `Analysis/Lp/WeakType` |
| The layer cake formula `∫ F^p dν = p ∫_0^∞ ν{F > t} t^(p-1) dt` for `[0, ∞]`-valued functions on every measure space, and the integrals of powers of `t` over `(0, b)`, `(0, ∞)` and the level sets `{t < a}`, `{t ≥ a}` | ✅ | ✗ | `Analysis/Lp/LayerCake` |
| Chebyshev's inequality with a power and at half height, the level sets of a split function, the parts of a function above and below a level, two Tonelli steps on s-finite measure spaces, integrals of powers from bounds at every level, and Marcinkiewicz interpolation between weak type `(1,1)` and strong type `(2,2)` with an explicit constant, for operators on an abstract input type and in the terms of the Carleson project | ✅ | ✗ | `Analysis/Lp/Marcinkiewicz` |
| `L_p` and `L_p(ℓ_2)` norms by duality for `1 < p < ∞` through the norming family, Hölder's inequality for `[0, ∞]`-valued functions in `L_p` norms, and families in `L_p` vanishing outside a finite set | ✅ | ✗ | `Analysis/Lp/NormingFamily` |
| `L_p` norms on `ℝ^d` through slices in one coordinate: integrating out a coordinate, `L_p` norms as mixed norms of slices, bounds through slices | ✅ | ✗ | `Analysis/Lp/CoordinateSlices` |
| A fractional Hardy inequality on `(0, 1]`, `∫_0^1 \|u(t)\|² t^(-2s) dt ≤ K_s ∫_0^1 ∫_0^1 \|u(t) - u(τ)\|² / \|t - τ\|^(1+2s) dτ dt` for `s > 1/2` and measurable `u` vanishing near `0`, with two Minkowski steps between sets, Hardy's inequality for telescoping sequences, the scaled dyadic intervals `(c 2^(-k-1), c 2^(-k)]` and weighted layers of a height function | ✅ | ✗ | `Analysis/Lp/HalfLineHardy` |
| Differences `higherDiff` on any additive monoid, steps of either sign, under additive maps; the modulus of smoothness on `ℝ^d`, its homogeneity, dilation of the scale | ✅ | ✗ | `Analysis/Differences/Differences` |
| Translation algebra of an additive monoid, differences as its powers | ✅ | ✗ | `Analysis/Differences/TranslationAlgebra` |
| Moduli of smoothness on subsets of `ℝ^d`, restrictions by intrinsic differences, sets equal up to null sets, the intrinsic quasi-norm, its lower semicontinuity along `L_p` limits, and the convergence of its Cauchy sequences | ✅ | ✗ | `Analysis/Differences/DomainModuli` |
| Moduli of smoothness and Besov quasi-norms under measure preserving linear changes of variables; moduli on subsets under linear and affine maps, `L_p` norms and intrinsic quasi-norms under affine maps, composition with an affine map on `L_p`, the norms of the identification of `ℓ_p^n` with the product | ✅ | ✗ | `Analysis/Differences/LinearEquivModuli` |
| Convolution with integrable kernels on `ℝ^d`: Young's inequality, pointwise bounds, associativity, operators on `L_p` | ✅ | ✗ | `Analysis/Fourier/Convolution` |
| Changes of scale `x ↦ r x` in integrals, dilations, their supports, `L_1` norms and first moments, continuity of translation, approximate identities in `L_p(ℝ^d)` | ✅ | ✗ | `Analysis/Fourier/ApproxIdentity` |
| The Fourier transform of integrable functions (continuity, `L_1` bounds, convolutions, multiplication formula, conjugation, Lipschitz bound for band-limited inverse transforms); Littlewood–Paley kernels: smooth cut-offs, dilation formula for `𝓕`, the kernels on the frequency side with `|𝓕ψ_j| ≤ 1`, telescoping sums and at most two blocks at every frequency, kernel identities by Fourier inversion | ✅ | ✗ | `Analysis/Fourier/LittlewoodPaleyKernels` |
| Test functions as Schwartz functions and compactly supported complex Schwartz functions as complex test functions, commuting directional derivatives, the transpose formula for distributions and tempered distributions; cut-offs of Schwartz functions converge in the Schwartz space (smooth compactly supported functions are dense), tempered distributions determined by test functions | ✅ | ✗ | `Analysis/Fourier/SchwartzCutoff` |
| Volume and nesting of the dyadic cubes, Lebesgue differentiation along them | ✅ | ✗ | `Analysis/Maximal/DyadicCubes` |
| Dyadic cubes of every level and dyadic cells of `ℝ^d`: the coordinates of the grid as a measure preserving linear equivalence with `Fin n → ℝ`, partition, counting of their centres, bounded overlap | ✅ | ✗ | `Analysis/Maximal/DyadicGrid` |
| Hardy–Littlewood maximal function: volumes of dyadic balls, measurability, convolutions with kernels under radial majorants, weighted weak type `(1,1)` and weighted strong type, the maximal theorem | ✅ | ✗ | `Analysis/Maximal/HardyLittlewoodMaximal` |
| The Calderón–Zygmund decomposition on dyadic cubes, norms of means of vector-valued functions | ✅ | ✗ | `Analysis/Maximal/CalderonZygmund` |
| The signed Calderón–Zygmund decomposition of functions with values in a normed space and of families: good parts bounded by `2^n t` with `∫ ‖·‖² ≤ 2^n t ∫ ‖f‖`, bad pieces with mean zero on their cubes and total mass at most `2 ∫ ‖f‖` | ✅ | ✗ | `Analysis/Maximal/CalderonZygmundSigned` |
| The Fefferman–Stein inequality | ✅ | ✗ | `Analysis/Maximal/FeffermanStein` |
| The pivot dual `H → X*` of a bounded operator `X → H` between Hilbert spaces: the inner product of `H`, the integral form for `H = L_2(μ)`, its norm, its kernel `(range ι)^⊥`, injectivity iff dense range, dense range by orthogonal complements, smooth functions with compact support separating `L_p(μ)`, `p ≥ 1`, and dense range in `L_2(μ)` from them | ✅ | ✗ | `Analysis/Hilbert/GelfandTriple` |
| Componentwise operators, isomorphisms and semilinear isometric isomorphisms on finite `L_2` sums `X^m` with their norms, kernels and ranges, inner products with a single component, orthogonal complements `(K^m)ᗮ = (Kᗮ)^m` and the dual of `E^m` | ✅ | ✗ | `Analysis/Hilbert/PiLpMaps` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
