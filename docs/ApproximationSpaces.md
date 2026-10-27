# Approximation spaces

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Approximation
spaces*, chapters *Approximation schemes*, *Sequence spaces*, *Approximation spaces*, *Lifting
and the Nikolskii transfer theorem*, *Interpolation and the representation theorem*, *Real
interpolation of couples*, *Block decompositions and projections*, *Traces and intrinsic norms*
and *Moduli of smoothness and approximation*.

The library `ApproximationSpaces` holds the abstract theory: in a real normed space `X`,
approximation schemes and the errors of best approximation, the approximation spaces `A^s_q` with
their dyadic quasi-norm, embeddings and functoriality, lifting under a Bernstein inequality and the
Nikolskii transfer theorem, the K-functional, the discrete and the continuous K-method and the
representation of `A^s_q` as a real interpolation space, couples of two extended quasi-norms on
an abelian group with their K-method, its interpolation property and the reiteration theorem
(`InterpCouple`), approximation spaces as interpolation spaces of the couple `(X, A^r_∞)`,
block, projection and atomic decompositions, abstract trace and retract theorems, and the
comparison with spaces defined by moduli of smoothness (`ModulusData`). A
smoothness space of order `r` is a Banach space with an injective bounded map into `X` satisfying
Jackson's and Bernstein's inequalities of order `r` (`ApproximationScheme.JacksonBound`,
`ApproximationScheme.SmoothnessSpace`, a hypothesis structure whose fields are the embedding, the
order and Jackson's and Bernstein's inequalities); Sobolev spaces are the motivating examples.
The schemes live in real normed spaces and the couples on abelian groups; the measures are the
counting measure behind the `ℓ_q` norms and `dt/t` on `(0, ∞)` of the continuous K-method. The
other blocks instantiate the theory.

## Main results

* **The error of best approximation.** For every approximation scheme, `E₀(f) = ‖f‖`,
  `E_n(f)` decreases in `n`, `E_n(c f) = |c| E_n(f)`, `E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`,
  and `E_n(f) ≤ E_n(g) + ‖f - g‖`
  (`ApproximationScheme.approxError_zero_right`, `.approxError_anti`, `.approxError_smul`,
  `.approxError_add_le`, `.approxError_le_approxError_add_enorm`). The errors tend to zero
  exactly on the closure of `⋃ A_n` (`ApproximationScheme.tendsto_approxError_zero_iff`).
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
  interpolation space `(X, Y)_{s/r, q}` of the discrete K-method on the grid `t = 2^(-kr)`, the `f`
  with `‖f‖ + ‖(2^(ks) K(2^(-kr), f))_k‖_{ℓ_q} < ∞` (`ApproximationScheme.MemInterp`), with
  equivalent norms (`ApproximationScheme.memApprox_iff_memInterp`,
  `.approxNormDyadic_le_interpNorm_of_jackson`, `.interpNorm_le_approxNormDyadic_of_bernstein`). In
  particular two schemes with Jackson and Bernstein inequalities of the same order
  for the same `ι` have the same approximation spaces
  (`ApproximationScheme.approxSpace_eq_of_jackson_bernstein`).
* **The discrete and the continuous K-method.** For `θ > 0`, `0 < q ≤ ∞` and every grid
  `t = 2^(-kρ)`, `ρ > 0`, the discrete K-norm `‖f‖ + ‖(2^(kρθ) K(2^(-kρ), f))_k‖_{ℓ_q}` and the
  continuous K-norm `(∫_0^∞ (t^(-θ) K(t, f))^q dt/t)^(1/q)` (the essential supremum of
  `t^(-θ) K(t, f)` for `q = ∞`) are equivalent, with explicit
  constants (Bergh–Löfström, Lemma 3.1.3; `ApproximationScheme.kMethodNorm_le_interpNorm`,
  `.interpNorm_le_kMethodNorm`, `.memInterp_iff_memKMethod`). Hence the grid does not matter
  (`ApproximationScheme.memInterp_iff_memInterp_of_pos`), and the representation theorem reads
  `A^s_q = (X, Y)_{s/r, q}` for the continuous K-method
  (`ApproximationScheme.memApprox_iff_memKMethod`).
* **Couples and their K-method.** For a couple `(N₀, N₁)` of functions `U → [0, ∞]` on an
  abelian group, with `K(t, u) = inf_b (N₀(u - b) + t N₁(b))`, every `θ ≥ 0`, `ρ > 0` and
  `0 < q ≤ ∞`, the continuous K-norm `(∫_0^∞ (t^(-θ) K(t, u))^q dt/t)^(1/q)` is finite if and
  only if `‖(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}‖_{ℓ_q}` is, with the constants
  `(ρ log 2)^(1/q) 2^(±ρθ)` (Bergh–Löfström, Lemma 3.1.3;
  `InterpCouple.memKMethod_iff_discreteKMethodNorm_lt_top`); swapping the couple replaces `θ` by
  `1 - θ` (`InterpCouple.discreteKMethodNorm_swap`). For a couple quasi-normed with constant `C`,
  `K(t, u + v) ≤ C (K(t, u) + K(t, v))` (`InterpCouple.kFunctional_add_le`); for a quasi-normed
  homogeneous couple on a real vector space the K-method gives a linear subspace
  (`InterpCouple.kMethodSpace`). The couple of a bounded
  linear map `ι : Y → X` has the K-method of the previous item
  (`InterpCouple.kMethodNorm_ofMap`).
* **The interpolation property.** If an additive map `T` between two couples satisfies
  `N_i'(T a) ≤ M_i N_i(a)` with `0 < M_i < ∞`, then `‖T u‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖u‖_{K,θ,q}`
  for every `θ` and `q` (Bergh–Löfström, Theorems 3.1.2 and 3.11.2;
  `InterpCouple.kMethodNorm_map_le`), also for maps that are additive only on decompositions
  into pieces of finite norm (`InterpCouple.kMethodNorm_map_le_of_additiveOn`). The proof uses
  `K'(t, T u) ≤ M₀ K((M₁/M₀) t, u)` (`InterpCouple.kFunctional_map_le`) and the invariance of
  `dt/t` under dilations (`ApproximationScheme.measurePreserving_mul_left_kMethodMeasure`).
  Equivalent couples give the same spaces (`InterpCouple.memKMethod_congr`), the space of a
  retract is the image of the space (Bergh–Löfström, Theorem 6.4.2;
  `InterpCouple.memKMethod_iff_of_retract`, `InterpCouple.memKMethod_iff_exists_map_eq`), and
  bounded linear maps `T : X → X'`, `S : Y → Y'` with `T ι = ι' S` map `(X, Y)_{θ,q}` into
  `(X', Y')_{θ,q}` (`ApproximationScheme.kMethodNorm_map_le_of_comp_eq`,
  `ApproximationScheme.MemInterp.map`).
* **The reiteration theorem.** For a couple quasi-normed with constant `C` (`N_i(0) = 0`,
  `N_i(-a) = N_i(a)`, `N_i(a + b) ≤ C (N_i(a) + N_i(b))`, `C < ∞`), `0 < θ₀ < θ₁ < 1`,
  `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`,
  `((X₀, X₁)_{θ₀,q₀}, (X₀, X₁)_{θ₁,q₁})_{η,q} = (X₀, X₁)_{(1-η)θ₀+ηθ₁,q}` (Bergh–Löfström,
  Theorems 3.5.3 and 3.11.5), where `X_i = {N_i < ∞}` and
  `(X₀, X₁)_{θ,q} = {u : ‖u‖_{K,θ,q} < ∞}`, for the discrete K-norms
  `‖(2^(-nθ_i) K(2^n, u))_{n ∈ ℤ}‖_{ℓ_{q_i}}` and for the continuous K-norms `‖·‖_{K,θ_i,q_i}` of
  the two inner K-spaces (`InterpCouple.memKMethod_kCouple_iff`,
  `InterpCouple.memKMethod_kMethodCouple_iff`), with the explicit constants
  `InterpCouple.reiterationConst` (`InterpCouple.kCouple_discreteKMethodNorm_le`); the endpoint
  cases are
  `(X₀, (X₀, X₁)_{θ₁,q₁})_{η,q} = (X₀, X₁)_{ηθ₁,q}` and
  `((X₀, X₁)_{θ₀,q₀}, X₁)_{η,q} = (X₀, X₁)_{(1-η)θ₀+η,q}`
  (`InterpCouple.memKMethod_leftKCouple_iff`, `InterpCouple.memKMethod_rightKCouple_iff`), and
  for a bounded linear map `ι : Y → X`, `((X, Y)_{θ₀,q₀}, (X, Y)_{θ₁,q₁})_{η,q} = (X, Y)_{θ,q}`
  (`ApproximationScheme.memKMethod_reiteration`). The proof uses the upper bound of Holmstedt's
  formula in discrete form with `ℓ_1` sums,
  `K̄(2^(m(θ₁-θ₀)), u) ≤ c (∑_{n<m} 2^(-nθ₀) K(2^n, u) + 2^(m(θ₁-θ₀)) ∑_{n≥m} 2^(-nθ₁)
  K(2^n, u))`
  (Holmstedt 1970; Bergh–Löfström, Theorem 3.6.1 has `L_{q_i}(dt/t)` norms of the two pieces;
  `InterpCouple.kFunctional_kCouple_le`, with the endpoint versions
  `InterpCouple.kFunctional_leftKCouple_le` and `InterpCouple.kFunctional_rightKCouple_le`), which
  suffices for reiteration, and the geometric convolutions on `ℤ`
  (`ENNReal.lqNorm_tsum_geom_sub_le`, `ENNReal.lqNorm_tsum_geom_add_le`).
* **Approximation spaces as interpolation spaces.** For every scheme, `0 < s < r` and
  `1 ≤ q ≤ ∞`, `A^s_q = (X, A^r_∞)_{s/r,q}` for the couple of the norm of `X` and the dyadic
  quasi-norm of `A^r_∞` (Pietsch 1981; DeVore–Popov, LNM 1302 (1988);
  `ApproximationScheme.memApprox_iff_memKMethod_reprCouple`), with the explicit constants `2 · 2^s`
  and `ApproximationScheme.devorePopovConst r s = 3 + 7 (1 - 2^(-(r-s)))⁻¹` for the norm on the
  grid `t = 2^(-kr)` (`ApproximationScheme.approxNormDyadic_le_interpNorm_reprCouple`,
  `ApproximationScheme.interpNorm_reprCouple_le_approxNormDyadic`); the proof uses the scheme
  alone, with the near-best approximants in place of lifts. For `0 < s₀ < s₁`, `0 < η < 1`
  and `1 ≤ q₀, q₁, q ≤ ∞`,
  `(A^{s₀}_{q₀}, A^{s₁}_{q₁})_{η,q} = A^{(1-η)s₀+ηs₁}_q` and `(X, A^{s₁}_{q₁})_{η,q} = A^{ηs₁}_q`
  (`ApproximationScheme.memKMethod_approxCouple_iff`,
  `ApproximationScheme.memKMethod_approxCouple_zero_iff`), and every couple whose norms lie
  between two dyadic quasi-norms of the same smoothness has these spaces as interpolation spaces
  (`ApproximationScheme.memKMethod_iff_memApprox_of_sandwich`,
  `ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches`).
* **Moduli of smoothness and approximation.** Let `ω(f, 2^(-k))` be subadditive with
  `ω(f, t) ≤ C₀ ‖f‖`, and assume a Jackson inequality `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for
  `k ≥ k₀` and an inverse inequality `ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`. Then
  for `0 ≤ s < θ` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞`,
  with equivalent quasi-norms (`ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top`).
  For `0 < s₀ < s₁ < θ`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, the `(η, q)` interpolation space
  of the couple of the classical quasi-norms of smoothness and fine index `(s₀, q₀)` and
  `(s₁, q₁)` consists of the `f` with `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞`,
  `s = (1-η)s₀ + ηs₁`; for the couple of `‖·‖` and the classical quasi-norm of `(s₁, q₁)` the
  same holds with `s = ηs₁` (`ApproximationScheme.ModulusData.memKMethod_modCouple_iff`,
  `ApproximationScheme.ModulusData.memKMethod_leftModCouple_iff`).
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
* **Interpolation of dyadic suprema** (Brezis–Mironescu). For `σ₁ < σ₀`, `0 < θ < 1` and every
  sequence `a` in `[0, ∞]`,
  `∑_j 2^(j(θσ₀ + (1-θ)σ₁)) a_j ≤ c (sup_j 2^(jσ₀) a_j)^θ (sup_j 2^(jσ₁) a_j)^(1-θ)` with
  `c = 2^(θδ) (2^(θδ) - 1)⁻¹ + (1 - 2^(-(1-θ)δ))⁻¹`, `δ = σ₀ - σ₁`
  (`ENNReal.tsum_dyadicWeight_mul_le_iSup`, `ENNReal.dyadicInterpConst`).
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
| `ℓ_q` norms in `ℝ≥0∞`, Minkowski, Cauchy–Schwarz, monotonicity in `q`, tails, sequences with finitely many nonzero terms, reindexing, geometric sequences, dyadic weights; `L_p` norms of `[0, ∞]`-valued functions: homogeneity, powers, monotone convergence, Minkowski's inequality for series | ✅ | ✗ | `Sequences/Lq` |
| Cauchy condensation with power weights, the dyadic sum `∑_j min(2^j a, (2^j a)⁻¹) ≤ 4`, finitely many changed terms, sums over the dyadic scales of an annulus, the interpolation inequality for dyadic suprema (Brezis–Mironescu) | ✅ | ✗ | `Sequences/Dyadic` |
| Countable Minkowski inequality, monotone convergence and truncations in `ℓ_q`, discrete Hardy inequalities, almost diagonal sums, shift invariance and geometric convolutions on `ℤ` | ✅ | ✗ | `Sequences/Hardy` |
| `A^s_q`, its dyadic quasi-norm and linear structure | ✅ | ✗ | `Norm`, `Dyadic`, `Space` |
| Embeddings `A^s_q ↪ A^t_r` and functoriality | ✅ | ✗ | `Embedding`, `Transfer` |
| Telescoping lift, Bernstein gives `A^β_1 ↪ Y`, Nikolskii transfer theorem | ✅ | ✗ | `Lift`, `Nikolskii` |
| K-functional, real interpolation, representation theorem | ✅ | ✗ | `KFunctional`, `Representation` |
| Continuous K-method and its equivalence with the discrete K-method | ✅ | ✗ | `KMethod` |
| Couples of extended quasi-norms, their K-functional and K-method, quasi-triangle inequalities of the K-norms, the couple of a bounded linear map | ✅ | ✗ | `Interpolation/Couple` |
| Dilations of `dt/t`, the interpolation property of the K-method, comparable couples, retracts, compatible maps between couples of bounded linear maps | ✅ | ✗ | `Interpolation/Property` |
| Couples of K-spaces, Holmstedt's formula, the reiteration theorem and its endpoint cases | ✅ | ✗ | `Interpolation/Reiteration` |
| Approximation spaces as interpolation spaces `A^s_q = (X, A^r_∞)_{s/r,q}`, reiteration of approximation spaces, the sandwich principle | ✅ | ✗ | `Interpolation/ApproxSpaces` |
| Moduli compatible with a scheme, coincidence with the classical space, interpolation of the classical spaces | ✅ | ✗ | `Moduli` |
| Block decompositions, projection schemes and dyadic blocks | ✅ | ✗ | `Decompositions/Blocks`, `Decompositions/Projection` |
| Synthesis with decay, atomic systems, `b^s_{p,q}`, atomic characterisation | ✅ | ✗ | `Decompositions/Synthesis`, `Decompositions/Atomic` |
| Trace theorem: extension, transfer, surjectivity | ✅ | ✗ | `Trace` |
| Intrinsic and restriction quasi-norms (retract theorem) | ✅ | ✗ | `Retract` |
| Jackson's inequality, smoothness spaces | ✅ | ✗ | `Jackson` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
