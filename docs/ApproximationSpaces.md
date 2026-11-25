# Approximation spaces

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Approximation
spaces*, chapters *Approximation schemes*, *Sequence spaces*, *Approximation spaces*, *Lifting
and the Nikolskii transfer theorem*, *Interpolation and the representation theorem*, *Real
interpolation of couples*, *Block decompositions and projections*, *Traces and intrinsic norms*
and *Moduli of smoothness and approximation*, and the section *Nonlinear approximation from a
Hilbert basis* of the chapter *Spectral schemes*.

The library `ApproximationSpaces` holds the abstract theory: in a real normed space `X`,
approximation schemes and the errors of best approximation, the approximation spaces `A^s_q` with
their dyadic quasi-norm, embeddings and functoriality, lifting under a Bernstein inequality and the
Nikolskii transfer theorem, the K-functional, the discrete and the continuous K-method and the
representation of `A^s_q` as a real interpolation space, couples of two extended quasi-norms on
an abelian group with their K-method, its interpolation property and the reiteration theorem
(`InterpCouple`), approximation spaces as interpolation spaces of the couple `(X, A^r_∞)`,
block, projection and atomic decompositions, abstract trace and retract theorems, the
comparison with spaces defined by moduli of smoothness (`ModulusData`), and best `n`-term
approximation from a Hilbert basis with the theorem of Stechkin and DeVore. The E-functional of a
couple, the error of best approximation under a bound on the complexity, gives approximation
spaces on abelian groups with a quasi-norm, such as `L_p` for `0 < p < 1`, and a comparison with
moduli of smoothness that needs only the subadditivity of a power of the quasi-norm. A
smoothness space of order `r` is a Banach space with an injective bounded map into `X` satisfying
Jackson's and Bernstein's inequalities of order `r` (`ApproximationScheme.JacksonBound`,
`ApproximationScheme.SmoothnessSpace`, a hypothesis structure whose fields are the embedding, the
order and Jackson's and Bernstein's inequalities); Sobolev spaces are the motivating examples.
The schemes live in real normed spaces and the couples on abelian groups; the measures are the
counting measure behind the `ℓ_q` norms, Lebesgue measure on `(0, ∞)` in the layer cake formula
for sums, and `dt/t` on `(0, ∞)` of the continuous K-method. The other blocks instantiate the
theory.

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
  `.approxNormDyadic_le_approxNorm`). For `0 < q < 1` the same comparison holds with the extra
  factors `C_q` and `C_q²`, where `C_q = 2^(1/q - 1)` is the constant of the quasi-triangle
  inequality in `ℓ_q` (`ApproximationScheme.approxNorm_le_approxNormDyadic'`,
  `.approxNormDyadic_le_approxNorm'`, `.memApprox_iff_lqNorm_dyadic_lt_top'`).
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
  (`ApproximationScheme.exists_preimage_approxNormDyadic_le_of_nikolskii`).
* **The representation theorem.** Let `ι : Y → X` satisfy Jackson's inequality
  `E_n(ι y) ≤ C n^(-r) ‖y‖` and Bernstein's inequality (every `a ∈ A_n` is `ι y` with
  `‖y‖ ≤ C n^r ‖a‖`) of order `r`. Then for `0 < s < r` and `1 ≤ q ≤ ∞`, `A^s_q` is the real
  interpolation space `(X, Y)_{s/r, q}` of the discrete K-method on the grid `t = 2^(-kr)`, the `f`
  with `‖f‖ + ‖(2^(ks) K(2^(-kr), f))_k‖_{ℓ_q} < ∞` (`ApproximationScheme.MemInterp`), with
  equivalent norms (`ApproximationScheme.memApprox_iff_memInterp_of_jacksonBound_of_liftBound`,
  `.approxNormDyadic_le_inclInterpNorm_of_jackson`,
  `.inclInterpNorm_le_approxNormDyadic_of_bernstein`). In particular two schemes with Jackson
  and Bernstein inequalities of the same order for the same `ι` have the same approximation spaces
  (`ApproximationScheme.approxSpace_eq_of_jackson_bernstein`).
* **The discrete and the continuous K-method.** For `θ > 0`, `0 < q ≤ ∞` and every grid
  `t = 2^(-kρ)`, `ρ > 0`, the discrete K-norm `‖f‖ + ‖(2^(kρθ) K(2^(-kρ), f))_k‖_{ℓ_q}` and the
  continuous K-norm `(∫_0^∞ (t^(-θ) K(t, f))^q dt/t)^(1/q)` (the essential supremum of
  `t^(-θ) K(t, f)` for `q = ∞`) are equivalent, with explicit
  constants (Bergh–Löfström, Lemma 3.1.3; `ApproximationScheme.inclKMethodNorm_le_inclInterpNorm`,
  `ApproximationScheme.inclInterpNorm_le_inclKMethodNorm`,
  `ApproximationScheme.memInterp_iff_memInclKMethod`). Hence the grid does not matter
  (`ApproximationScheme.memInterp_iff_memInterp_of_pos`), and the representation theorem reads
  `A^s_q = (X, Y)_{s/r, q}` for the continuous K-method
  (`ApproximationScheme.memApprox_iff_memInclKMethod_of_jacksonBound_of_liftBound`).
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
  (`InterpCouple.kMethodNorm_ofMap`); the prefix `incl` in `ApproximationScheme.inclKFunctional`,
  `.inclKMethodNorm`, `.MemInclKMethod` and their relatives marks this couple `(X, ι(Y))`.
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
  `(X', Y')_{θ,q}` (`ApproximationScheme.inclKMethodNorm_map_le_of_comp_eq`,
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
  (`ApproximationScheme.memInclKMethod_reiteration`). The proof uses the upper bound of Holmstedt's
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
* **The E-functional and its approximation spaces.** For a couple `(N₀, N₁)` on an abelian
  group, with `N₀` the quasi-norm of the errors and `N₁` the complexity, the E-functional is
  `E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}` (Bergh–Löfström, Section 7.1;
  `InterpCouple.eFunctional`). It decreases in `t`, and
  `E(t + s, u + v)^ρ ≤ E(t, u)^ρ + E(s, v)^ρ` if `N₀^ρ` and `N₁` are subadditive
  (`InterpCouple.eFunctional_add_rpow_le`). If `N₁(0) = 0` and only `0` has complexity below
  `1`, then for `α > 0` and `0 < q ≤ ∞`, and for `α = 0` and `q = ∞`, the norm
  `(∫_0^∞ (t^α E(t, u))^q dt/t)^(1/q)` of `E_{α,q}` (Bergh–Löfström, Definition 7.1.5) is finite
  iff `N₀(u) + ‖(2^(kα) E(2^k, u))_k‖_{ℓ_q}` is
  (`InterpCouple.memEMethod_iff_eNormDyadic_lt_top`). For the complexity couple of an
  approximation scheme, `N₁(b) = min {n : b ∈ A_n}`, `E(n, f) = E_n(f)` and `E_{s,q} = A^s_q`
  for `s > 0`, `0 < q ≤ ∞`, and for `s = 0`, `q = ∞`
  (`ApproximationScheme.eFunctional_complexityCouple`,
  `ApproximationScheme.memEMethod_complexityCouple_iff`).
* **Moduli of smoothness for `ρ`-normed couples.** Let `N₀(a + b)^ρ ≤ N₀(a)^ρ + N₀(b)^ρ` for
  some `ρ > 0`, as for `‖·‖_p` with `ρ = p ≤ 1`, let `N₁` be subadditive, let `N₀` and `N₁` be
  even and vanish at `0`, and let `ω(f, 2^(-k))`
  satisfy `ω(f + g, ·)^ρ ≤ ω(f, ·)^ρ + ω(g, ·)^ρ`, `ω(f, ·) ≤ C₀ N₀(f)`, the Jackson inequality
  `E(2^k, f) ≤ C_J ω(f, 2^(-k))` for every `k` and the inverse inequality
  `ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) N₀(a)` for `N₁(a) ≤ 2^j`. If only `0` has complexity below
  `1`, then for `0 < s < θ` and `0 < q ≤ ∞`, `f ∈ E_{s,q}` iff
  `N₀(f) + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞`, with equivalent quasi-norms (DeVore–Popov,
  Trans. Amer. Math. Soc. 305 (1988), proof of Theorem 4.8;
  `InterpCouple.CoupleModulusData.memEMethod_iff_coupleModNorm_lt_top`). The telescoping sums
  are estimated in the `ρ`-th power, with Hardy's inequality in `ℓ_{q/ρ}`.
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
  `‖Tr f‖_{B^{s-β}_q} ≲ ‖f‖_{A^s_q}`
  (`ApproximationScheme.TraceBound.approxNormDyadic_limitTrace_le`). If every `b ∈ B_{2^k}` is
  `T a` with `a ∈ A_{2^(k+γ)}` and `‖a‖ ≤ C' 2^(-kβ) ‖b‖`, then every `g ∈ B^s_q`, `s > 0`, is
  the trace of some `f ∈ A^{s+β}_q` with `‖f‖ ≲ ‖g‖`
  (`ApproximationScheme.TraceBound.exists_limitTrace_eq`).
* **Intrinsic norms.** Let `R` be bounded linear with `R(A_n) ⊆ B_n`, as for the restriction
  to a domain, and let `E` be a possibly nonlinear map with `R(E g) = g`, `‖E g‖ ≤ C ‖g‖` and
  `E^A_{2^(k+γ)}(E g) ≤ C E^B_{2^k}(g)`. Then the intrinsic quasi-norm of `B^s_q` and the
  restriction quasi-norm `inf {‖f‖_{A^s_q} : R f = g}` are equivalent, and `B^s_q = R(A^s_q)`
  (`ApproximationScheme.approxNormDyadic_extension_le`,
  `ApproximationScheme.memApprox_iff_exists_restrict`).
* **Dyadic blocks.** If the scheme has projections `P_n` onto `A_n` with `‖P_n‖ ≤ M` and
  `⋃ A_n` is dense, then for `s > 0`, `f ∈ A^s_q` iff
  `‖P_1 f‖ + ‖(2^(ks) ‖P_{2^(k+1)} f - P_{2^k} f‖)_k‖_{ℓ_q} < ∞`
  (`ApproximationScheme.ProjectionScheme.memApprox_iff_blockNorm_lt_top_of_dense`).
* **Sequence spaces.** For `0 < q ≤ r ≤ ∞` and every sequence `a` in `[0, ∞]`,
  `‖a‖_{ℓ_r} ≤ ‖a‖_{ℓ_q}` (`ENNReal.lqNorm_le_lqNorm_of_le`), and for `q ≥ 1` the norm of a
  series of sequences is at most the series of the norms (`ENNReal.lqNorm_tsum_le`). For
  `0 < p ≤ 1`, `(∑_i f_i)^p ≤ ∑_i f_i^p` in `[0, ∞]` (`ENNReal.rpow_tsum_le_tsum_rpow`), and for
  `0 < q < 1`, `‖a + b‖_{ℓ_q} ≤ 2^(1/q - 1) (‖a‖_{ℓ_q} + ‖b‖_{ℓ_q})` (`ENNReal.lqNorm_add_le'`).
  For `0 < p ≤ 1` and functions `f`, `g` on any measure space,
  `‖f + g‖_p^p ≤ ‖f‖_p^p + ‖g‖_p^p` (`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`).
* **Hardy inequalities.** For `α > 0`, `1 ≤ q ≤ ∞` and every sequence `b` in `[0, ∞]`,
  `‖(2^(kα) ∑_{i ≥ 0} b_{k+i})_k‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖(2^(kα) b_k)_k‖_{ℓ_q}` and
  `‖(2^(-kα) ∑_{j ≤ k} b_j)_k‖_{ℓ_q} ≤ (1 - 2^(-α))⁻¹ ‖(2^(-kα) b_k)_k‖_{ℓ_q}`
  (`ENNReal.hardy_tail_le`, `ENNReal.hardy_sum_le`). For `0 < q ≤ 1` both hold with the constant
  `(1 - 2^(-αq))^(-1/q)` (`ENNReal.hardy_tail_le_of_le_one`, `ENNReal.hardy_sum_le_of_le_one`).
* **Interpolation of dyadic suprema** (Brezis–Mironescu). For `σ₁ < σ₀`, `0 < θ < 1` and every
  sequence `a` in `[0, ∞]`,
  `∑_j 2^(j(θσ₀ + (1-θ)σ₁)) a_j ≤ c (sup_j 2^(jσ₀) a_j)^θ (sup_j 2^(jσ₁) a_j)^(1-θ)` with
  `c = 2^(θδ) (2^(θδ) - 1)⁻¹ + (1 - 2^(-(1-θ)δ))⁻¹`, `δ = σ₀ - σ₁`
  (`ENNReal.tsum_dyadicWeight_mul_le_iSup`, `ENNReal.dyadicInterpConst`).
* **Two schemes.** Linear approximation from the first `n` elements of a sequence
  (`ApproximationScheme.ofSpan`) and `n`-term approximation from a dictionary
  (`ApproximationScheme.nTerm`) are approximation schemes, and the first has larger errors
  than the second (`ApproximationScheme.approxError_nTerm_le_ofSpan`).
* **Decreasing rearrangement.** For a family `(r_i)_{i ∈ I}` of nonnegative numbers with only
  finitely many `r_i > t` for every `t > 0`, the decreasing rearrangement `r*` lists the entries
  in decreasing order with multiplicities (`decreasingRearrangement`, copied from TauCeti), and
  `∑_n (r*_n)^p = ∑_i r_i^p` for every `p > 0` (`tsum_ofReal_rpow_decreasingRearrangement`,
  from the layer cake formula `tsum_ofReal_rpow_eq_lintegral`).
* **Best `n`-term approximation from a Hilbert basis.** Let `(e_i)` be a Hilbert basis of a
  complex Hilbert space `H` and `E_n` the errors of `n`-term approximation from the multiples
  `c e_i`, `c ∈ ℂ`. Then `E_n(f)² = inf_{#Λ ≤ n} ∑_{i ∉ Λ} |⟨e_i, f⟩|²`
  (`HilbertBasis.approxError_nTerm_sq_eq`), and for `0 < τ ≤ 2`, `θ = 1/τ - 1/2` and every
  `n ≥ 0`, `E_n(f) ≤ (n + 1)^(-θ) (∑_i |⟨e_i, f⟩|^τ)^(1/τ)`
  (`HilbertBasis.approxError_nTerm_le`).
* **The theorem of Stechkin and DeVore.** For `0 < τ < 2` and `θ = 1/τ - 1/2`, `f ∈ H` lies in
  `A^θ_τ` of `n`-term approximation from the basis iff `∑_i |⟨e_i, f⟩|^τ < ∞`
  (`HilbertBasis.memApprox_nTerm_iff`), with `∑_i |⟨e_i, f⟩|^τ ≤ 4 ‖f‖_{A^θ_τ}^τ` and
  `‖f‖_{A^θ_τ} ≤ C_τ (∑_i |⟨e_i, f⟩|^τ)^(1/τ)` for the dyadic quasi-norm `‖·‖_{A^θ_τ}`
  (`HilbertBasis.tsum_repr_rpow_le`, `HilbertBasis.approxNormDyadic_nTerm_le`). The Fourier
  basis of `L_2(𝕋^d)`, the Haar basis of `L_2[0, 1]` and the tensor Daubechies wavelet basis of
  `L_2(ℝ^d)` are instances, in [The torus](Torus.md),
  [Intervals, the cube, splines and wavelets](IntervalCube.md) and
  [Daubechies wavelets](Daubechies.md).

## What is formalised

Paths are relative to `ApproximationSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Approximation schemes, preimage and image | ✅ | ✗ | `Scheme` |
| Error of best approximation and its calculus | ✅ | ✗ | `Error` |
| Linear approximation from a sequence | ✅ | ✗ | `Instances/Span` |
| `n`-term approximation from a dictionary | ✅ | ✗ | `Instances/NTerm` |
| Hilbert-basis `n`-term approximation, Stechkin–DeVore | ✅ | ✗ | `Instances/NTermHilbertBasis` |
| Sums of powers in `[0, ∞]`, `ℓ_q` norms in `ℝ≥0∞`, Minkowski, the quasi-triangle inequality for `q < 1`, Cauchy–Schwarz, monotonicity in `q`, Fatou's lemma for termwise limits, tails, sequences with finitely many nonzero terms, reindexing, geometric sequences, dyadic weights, weighted `ℓ_q` norms from the first term and a bound of the others, weighted `ℓ_q` norms under a shift of the levels, iterated `ℓ_q` norms, powers of two, products and quotients in `[0, ∞]`; `L_p` norms of `[0, ∞]`-valued functions: homogeneity, powers, monotone convergence, Minkowski's inequality for series, functions bounded on pieces; subadditivity of `‖·‖_p^p` for `0 < p ≤ 1` | ✅ | ✗ | `Sequences/Lq` |
| Cauchy condensation with power weights, `n ≥ 1` written as `2^k + i` with `0 ≤ i < 2^k` and series split into dyadic blocks, the dyadic sum `∑_j min(2^j a, (2^j a)⁻¹) ≤ 4`, Pietsch's weights against the dyadic ones for a decreasing sequence, finitely many changed terms, sums over the dyadic scales of an annulus, the interpolation inequality for dyadic suprema (Brezis–Mironescu) | ✅ | ✗ | `Sequences/Dyadic` |
| Decreasing rearrangement, layer cake formula for sums | ✅ | ✗ | `Sequences/Rearrangement` |
| Countable Minkowski inequality, monotone convergence and truncations in `ℓ_q`, window sums in `ℓ_q`, discrete Hardy inequalities, almost diagonal sums and their constant, the Hardy and almost diagonal bounds for `0 < q ≤ 1`, Hardy's inequalities for every exponent, powers inside `ℓ_q` norms, shift invariance and geometric convolutions on `ℤ` | ✅ | ✗ | `Sequences/Hardy` |
| `A^s_q` and its dyadic quasi-norm for `q > 0`, linear structure for `q ≥ 1` | ✅ | ✗ | `Norm`, `Dyadic`, `Space` |
| Embeddings `A^s_q ↪ A^t_r` and functoriality | ✅ | ✗ | `Embedding`, `Transfer` |
| Telescoping lift, Bernstein gives `A^β_1 ↪ Y`, Nikolskii transfer theorem | ✅ | ✗ | `Lift`, `Nikolskii` |
| K-functional, real interpolation, representation theorem | ✅ | ✗ | `Interpolation/KFunctional`, `Interpolation/Representation` |
| Continuous K-method and its equivalence with the discrete K-method | ✅ | ✗ | `Interpolation/KMethod` |
| Couples of extended quasi-norms, their K-functional and K-method, quasi-triangle inequalities of the K-norms, the couple of a bounded linear map | ✅ | ✗ | `Interpolation/Couple` |
| Dilations of `dt/t`, the interpolation property of the K-method, comparable couples, retracts, compatible maps between couples of bounded linear maps | ✅ | ✗ | `Interpolation/Property` |
| Couples of K-spaces, Holmstedt's formula, the reiteration theorem and its endpoint cases | ✅ | ✗ | `Interpolation/Reiteration` |
| Approximation spaces as interpolation spaces `A^s_q = (X, A^r_∞)_{s/r,q}`, reiteration of approximation spaces, the sandwich principle | ✅ | ✗ | `Interpolation/ApproxSpaces` |
| The E-functional of a couple, near-best sequences, the spaces `E_{α,q}` and their dyadic norm, complexity couples, `E_{s,q} = A^s_q` for schemes | ✅ | ✗ | `Interpolation/EFunctional` |
| The blocks of near-best sequences, moduli compatible with a `ρ`-normed couple, coincidence of `E_{s,q}` with the classical space | ✅ | ✗ | `Interpolation/EFunctionalModuli` |
| Homogeneity of the E-functional, embeddings of the dyadic norms in the smoothness and the fine index, additive maps, Pietsch's form of a couple and its equivalence with the dyadic norm | ✅ | ✗ | `Interpolation/EFunctionalSpaces` |
| Moduli compatible with a scheme, coincidence with the classical space, interpolation of the classical spaces | ✅ | ✗ | `Moduli` |
| Block decompositions, series moved up by a number of levels, projection schemes and dyadic blocks | ✅ | ✗ | `Decompositions/Blocks`, `Decompositions/Projection` |
| Synthesis with decay, atomic systems, `b^s_{p,q}`, atomic characterisation | ✅ | ✗ | `Decompositions/Synthesis`, `Decompositions/Atomic` |
| Trace theorem: extension, transfer, surjectivity | ✅ | ✗ | `Trace` |
| Intrinsic and restriction quasi-norms (retract theorem) | ✅ | ✗ | `Retract` |
| Jackson's inequality, smoothness spaces | ✅ | ✗ | `Jackson` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
