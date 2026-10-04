# Approximation spaces

Part of [Function spaces via approximation](../README.md). Blueprint chapters: *Approximation
schemes*, *Sequence spaces*, *Approximation spaces*, *Lifting and the Nikolskii transfer theorem*,
*Interpolation and the representation theorem*, *Block decompositions and projections*, *Traces and
intrinsic norms*, *Moduli of smoothness and approximation*.

The library `ApproximationSpaces` holds the abstract theory in a real normed space `X`:
approximation schemes and the errors of best approximation, the approximation spaces `A^s_q` with
their dyadic quasi-norm, embeddings and functoriality, lifting under a Bernstein inequality and
the Nikolskii transfer theorem, the K-functional and the representation of `A^s_q` as a real
interpolation space, block, projection and atomic decompositions, abstract trace and retract
theorems, and the comparison with spaces defined by moduli of smoothness (`ModulusData`). A
smoothness space of order `r` is a Banach space with an injective bounded map into `X` satisfying
Jackson's and Bernstein's inequalities of order `r` (`ApproximationScheme.JacksonBound`,
`ApproximationScheme.SmoothnessSpace`); Sobolev spaces are the examples. Nothing in this block
mentions functions or measures; the other blocks instantiate it.

## Main results

* **The error of best approximation.** For every approximation scheme, `E₀(f) = ‖f‖`,
  `E_n(f)` decreases in `n`, `E_n(c f) = |c| E_n(f)`, `E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`,
  and `|E_n(f) - E_n(g)| ≤ ‖f - g‖`
  (`ApproximationScheme.approxError_zero_left`, `.approxError_anti`, `.approxError_smul`,
  `.approxError_add_le`, `.abs_approxError_sub_le`). The errors tend to zero exactly on the
  closure of `⋃ A_n` (`ApproximationScheme.tendsto_approxError_zero_iff`).
* **The dyadic quasi-norm.** For `s ≥ 0` and `1 ≤ q ≤ ∞`,
  `‖f‖_{A^s_q} ≤ 2^s (‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}) ≤ 4 · 4^s ‖f‖_{A^s_q}`
  (`ApproximationScheme.approxNorm_le_approxNormDyadic`,
  `.approxNormDyadic_le_approxNorm`).
* **Linear structure.** For `s ≥ 0` and `1 ≤ q ≤ ∞`, `A^s_q` is a linear subspace of `X`
  containing every `A_n`, `‖f‖ ≤ ‖f‖_{A^s_q}`, and
  `‖f + g‖_{A^s_q} ≤ 8 · 8^s (‖f‖_{A^s_q} + ‖g‖_{A^s_q})`
  (`ApproximationScheme.approxSpace`, `.memApprox_of_mem`, `.enorm_le_approxNorm`,
  `.approxNorm_add_le`). For `s > 0` it lies in the closure of `⋃ A_n`
  (`ApproximationScheme.mem_closure_iUnion_of_memApprox`).
* **Embeddings.** For `0 ≤ t` and `1 ≤ q, r ≤ ∞`, `A^s_q ⊆ A^t_r` whenever `t < s`, or
  `t = s` and `q ≤ r` (`ApproximationScheme.MemApprox.mono`); for `t < s` the norm bound is
  `‖f‖_{A^t_r} ≤ (1 - 2^(t-s))⁻¹ ‖f‖_{A^s_q}` in the dyadic form
  (`ApproximationScheme.approxNormDyadic_le_of_lt`). For Pietsch's quasi-norm,
  `‖f‖_{A^s_r} ≤ 2^s · 4 · 2^s ‖f‖_{A^s_q}` for `s ≥ 0`, `q ≤ r`, and
  `‖f‖_{A^t_r} ≤ 2^t (1 - 2^(t-s))⁻¹ · 4 · 2^s ‖f‖_{A^s_q}` for `0 ≤ t < s`
  (`ApproximationScheme.approxNorm_le_of_exponent_le`, `.approxNorm_le_of_lt`).
* **Functoriality.** A bounded linear map `T : X → Y` with `T(A_n) ⊆ B_n` satisfies
  `E^B_n(T f) ≤ ‖T‖ E^A_n(f)` and `‖T f‖_{B^s_q} ≤ ‖T‖ ‖f‖_{A^s_q}`
  (`ApproximationScheme.approxError_map_le`, `.approxNorm_map_le`).
* **Lifting.** Let `ι : Y → X` be a bounded linear map from a Banach space `Y` such that every
  `a ∈ A_n`, `n ≥ 1`, is `ι y` with `‖y‖ ≤ C n^β ‖a‖` (a Bernstein inequality). If
  `β ≥ 0` and `∑_k 2^(kβ) E_{2^k}(f) < ∞`, then `f = ι y` for some `y ∈ Y` with
  `‖y‖ ≤ K (‖f‖ + ∑_k 2^(kβ) E_{2^k}(f))` (`ApproximationScheme.exists_preimage_of_liftBound`).
* **Nikolskii transfer theorem.** If moreover `ι` is injective and `0 ≤ α < s`, and every
  `a ∈ A_n` is `ι y` with `‖y‖ ≤ C n^α ‖a‖` (a Nikolskii inequality), then every
  `f ∈ A^s_q(X)` is `ι y` for some `y` in the approximation space `B^{s-α}_q(Y)` of the
  pulled-back scheme `B_n = ι⁻¹(A_n)`, with `‖y‖_{B^{s-α}_q} ≤ K ‖f‖_{A^s_q}`
  (`ApproximationScheme.exists_preimage_of_nikolskii`).
* **The representation theorem.** Let `ι : Y → X` satisfy Jackson's inequality
  `E_n(ι y) ≤ C n^(-r) ‖y‖` and Bernstein's inequality (every `a ∈ A_n` is `ι y` with
  `‖y‖ ≤ C n^r ‖a‖`) of order `r`. Then for `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q` is the real
  interpolation space `(X, Y)_{s/r, q}`, with equivalent norms
  (`ApproximationScheme.memApprox_iff_memInterp`,
  `.approxNormDyadic_le_interpNorm_of_jackson`,
  `.interpNorm_le_approxNormDyadic_of_bernstein`). In particular two schemes with Jackson and
  Bernstein inequalities of the same order for the same `ι` have the same approximation
  spaces (`ApproximationScheme.approxSpace_eq_of_jackson_bernstein`).
* **Moduli of smoothness and approximation.** Let `ω(f, 2^(-k))` be subadditive with
  `ω(f, t) ≤ C₀ ‖f‖`, and assume a Jackson inequality `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for
  `k ≥ k₀` and an inverse inequality `ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`. Then
  for `0 ≤ s < θ` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞`,
  with equivalent quasi-norms (`ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top`).
* **Block decompositions.** In a Banach space, for `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff
  `f = ∑_k g_k` with blocks `g_k ∈ A_{2^k}` and `(2^(ks) ‖g_k‖)_k ∈ ℓ_q`; the infimum over
  such decompositions is an equivalent quasi-norm
  (`ApproximationScheme.memApprox_iff_blockDecompNorm_lt_top`).
* **Atomic decompositions.** Let `A` be a linear scheme with atoms `a_{j,m}` at finitely many
  positions `m` of level `j`, such that `‖∑_m c_m a_m‖ ≤ C 2^(-jδ) ‖c‖_{ℓ_p}` and
  `E_{2^k}(∑_m c_m a_m) ≤ C 2^(-(k-j)σ) 2^(-jδ) ‖c‖_{ℓ_p}` for `k ≥ j`. For `0 < s < σ`,
  every `f = ∑_j ∑_m λ_{j,m} a_{j,m}` satisfies `‖f‖_{A^s_q} ≲ ‖λ‖_{b^s_{p,q}}`, where
  `‖λ‖_{b^s_{p,q}} = ‖(2^(j(s-δ)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}`
  (`ApproximationScheme.AtomicSystem.approxNormDyadic_le_bNorm`). If every approximant of
  `A_{2^j}` expands stably in atoms of level `j`, then conversely every `f ∈ A^s_q` has such a
  decomposition, and `A^s_q` is the space of atomic sums with coefficients in `b^s_{p,q}`
  (`ApproximationScheme.AtomicSystem.memApprox_iff_exists_atomic`).
* **The trace theorem.** Let `T` be linear with `T(A_n) ⊆ B_n` and `‖T a‖ ≤ C n^β ‖a‖` for
  `a ∈ A_n`, `n ≥ 1`, as for the restriction of functions to a hyperplane. Then `T` extends to
  `A^β_1`, and for `0 ≤ β < s` it maps `A^s_q` into `B^{s-β}_q` with
  `‖Tr f‖_{B^{s-β}_q} ≲ ‖f‖_{A^s_q}` (`ApproximationScheme.TraceBound.approxNormDyadic_ext_le`).
  If every `b ∈ B_{2^k}` is `T a` with `a ∈ A_{2^(k+γ)}` and `‖a‖ ≤ C' 2^(-kβ) ‖b‖`, then every
  `g ∈ B^s_q`, `s > 0`, is the trace of some `f ∈ A^{s+β}_q` with `‖f‖ ≲ ‖g‖`
  (`ApproximationScheme.TraceBound.exists_ext_eq`).
* **Intrinsic norms.** Let `R` be bounded linear with `R(A_n) ⊆ B_n`, as for the restriction
  to a domain, and let `E` be a possibly nonlinear map with `R(E g) = g`, `‖E g‖ ≤ C ‖g‖` and
  `E^A_{2^(k+γ)}(E g) ≤ C E^B_{2^k}(g)`. Then the intrinsic quasi-norm of `B^s_q` and the
  restriction quasi-norm `inf {‖f‖_{A^s_q} : R f = g}` are equivalent, and `B^s_q = R(A^s_q)`
  (`ApproximationScheme.approxNormDyadic_extension_le`,
  `ApproximationScheme.memApprox_iff_exists_restrict`).
* **Dyadic blocks.** If the scheme has projections `P_n` onto `A_n` with `‖P_n‖ ≤ M` and
  `⋃ A_n` is dense, then for `s > 0`, `f ∈ A^s_q` iff
  `‖P_1 f‖ + ‖(2^(ks) ‖P_{2^(k+1)} f - P_{2^k} f‖)_k‖_{ℓ_q} < ∞`
  (`ApproximationScheme.ProjectionScheme.memApprox_iff_blockNorm_lt_top`).
* **Sequence spaces.** For `1 ≤ q ≤ r ≤ ∞` and every sequence `a` in `[0, ∞]`,
  `‖a‖_{ℓ_r} ≤ ‖a‖_{ℓ_q}` (`ENNReal.lqNorm_le_lqNorm_of_le`), and the norm of a series of
  sequences is at most the series of the norms (`ENNReal.lqNorm_tsum_le`).
* **Hardy inequalities.** For `α > 0`, `1 ≤ q ≤ ∞` and every sequence `b` in `[0, ∞]`,
  `‖(2^(kα) ∑_{i ≥ 0} b_{k+i})_k‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖(2^(kα) b_k)_k‖_{ℓ_q}` and
  `‖(2^(-kα) ∑_{j ≤ k} b_j)_k‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖(2^(-kα) b_k)_k‖_{ℓ_q}`
  (`ENNReal.hardy_tail_le`, `ENNReal.hardy_sum_le`).
* **Two schemes.** Linear approximation from the first `n` elements of a sequence
  (`ApproximationScheme.ofSpan`) and `n`-term approximation from a dictionary
  (`ApproximationScheme.nTerm`) are approximation schemes, and the first has larger errors
  than the second (`ApproximationScheme.approxError_nTerm_le_ofSpan`).

## What is formalised

Paths are relative to `ApproximationSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Approximation schemes, preimage and image | ✅ | ✗ | `Scheme` |
| Error of best approximation and its calculus | ✅ | ✗ | `Error` |
| Linear approximation from a sequence | ✅ | ✗ | `Instances/Span` |
| `n`-term approximation from a dictionary | ✅ | ✗ | `Instances/NTerm` |
| `ℓ_q` norms of sequences in `ℝ≥0∞`, Minkowski, monotonicity in `q` | ✅ | ✗ | `Sequences/Lq` |
| Cauchy condensation with power weights | ✅ | ✗ | `Sequences/Dyadic` |
| Countable Minkowski inequality, discrete Hardy inequalities, almost diagonal sums | ✅ | ✗ | `Sequences/Hardy` |
| `A^s_q`, its dyadic quasi-norm and linear structure | ✅ | ✗ | `Norm`, `Dyadic`, `Space` |
| Embeddings `A^s_q ↪ A^t_r` and functoriality | ✅ | ✗ | `Embedding`, `Transfer` |
| Telescoping lift, Bernstein gives `A^β_1 ↪ Y`, Nikolskii transfer theorem | ✅ | ✗ | `Lift`, `Nikolskii` |
| K-functional, real interpolation, representation theorem | ✅ | ✗ | `KFunctional`, `Representation` |
| Moduli compatible with a scheme, coincidence with the classical space | ✅ | ✗ | `Moduli` |
| Block decompositions, projection schemes and dyadic blocks | ✅ | ✗ | `Decompositions/Blocks`, `Decompositions/Projection` |
| Synthesis with decay, atomic systems, `b^s_{p,q}`, atomic characterisation | ✅ | ✗ | `Decompositions/Synthesis`, `Decompositions/Atomic` |
| Trace theorem: extension, transfer, surjectivity | ✅ | ✗ | `Trace` |
| Intrinsic and restriction quasi-norms (retract theorem) | ✅ | ✗ | `Retract` |
| Jackson's inequality, smoothness spaces | ✅ | ✗ | `Jackson` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
