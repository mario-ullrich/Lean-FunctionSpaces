# Triebel–Lizorkin spaces

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part
*Triebel–Lizorkin spaces*, chapters *Triebel–Lizorkin spaces* and *Vector-valued singular
integrals*.

Besov quasi-norms take the `L_p` norm of every Littlewood–Paley block `ψ_j ⋆ f` and then the
`ℓ_q` norm over the levels; the Triebel–Lizorkin quasi-norm
`‖ (∑_j 2^(jsq) |ψ_j ⋆ f|^q)^(1/q) ‖_p`, with the supremum over `j` for `q = ∞`, takes the
`ℓ_q` norm at every point first. This block develops the spaces `F^s_{p,q}` on `ℝ^d` and on the
torus `𝕋^d` with the blocks of [Besov spaces on `ℝ^d`](Rd.md); the mixed norms `L_p(ℓ_q)` and
`ℓ_q(L_p)`, the maximal functions and the Fefferman–Stein inequality are in
[Tools from analysis](Analysis.md).
The theory for `1 < p < ∞` starts with families of dilated Schwartz kernels with their Fourier
overlap and Hörmander condition, the adjoint of a convolution, which moves kernels and their
derivatives to the other side of an integral, the `L_2` bounds of the analysis and synthesis
operators of every kernel family with bounded Fourier overlap, and the Calderón–Zygmund
decomposition of functions with values in a normed space, and of families of them, into a bounded
good part and bad pieces with mean zero on dyadic cubes. With these, the analysis and synthesis
operators of every Calderón–Zygmund family are of weak type `(1,1)`. Marcinkiewicz interpolation
between weak type `(1,1)` and strong type `(2,2)`, in the terms of the Carleson project, gives
strong type `(p,p)` for `1 < p < 2`, and duality with the adjoint family extends it to `2 < p < ∞`,
for the analysis and the synthesis operators. Applied to the Littlewood–Paley blocks and their
synthesis kernels, this gives the square function theorem, the two-sided bound of `‖f‖_{F^0_{p,2}}`
by `‖f‖_p`, for `1 < p < ∞`. Localising the periodic lift transfers the strong type, and with it the
square function theorem, to the torus. The real interpolation spaces of two Triebel–Lizorkin spaces,
and of `L_p` and one of them, are Besov spaces.

## Main results

* **Triebel–Lizorkin spaces and the Besov sandwich on `ℝ^d`.** Let `V` be a finite-dimensional
  real inner product space, such as `ℝ^d`, `1 ≤ p < ∞`, `s ∈ ℝ`, `1 ≤ q ≤ ∞`, and `ψ_j` the
  Littlewood–Paley kernels of [Besov spaces on `ℝ^d`](Rd.md). For `f ∈ L_p(V)` the
  Triebel–Lizorkin quasi-norm is `‖f‖_{F^s_{p,q}} = ‖ x ↦ ‖(2^(js) |ψ_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p`
  (`Rd.triebelLizorkinNorm`), and `F^s_{p,q}` consists of the `f` with `‖f‖_{F^s_{p,q}} < ∞`
  (`Rd.MemTriebelLizorkin`, a subspace of `L_p`: `Rd.triebelLizorkinSpace`; for `s < 0` this is
  `F^s_{p,q} ∩ L_p`). Then
  `‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_{max(p,q)}} ≤ ‖f‖_{F^s_{p,q}}` and
  `‖f‖_{F^s_{p,q}} ≤ ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_{min(p,q)}}`
  (`Rd.littlewoodPaleyNorm_max_le_triebelLizorkinNorm`,
  `Rd.triebelLizorkinNorm_le_littlewoodPaleyNorm_min`), with equality for `q = p`
  (`Rd.triebelLizorkinNorm_eq_littlewoodPaleyNorm`). Hence for `s > 0`,
  `F^s_{p,p} = B^s_{p,p}` (`Rd.memTriebelLizorkin_iff_memApprox`) and
  `B^s_{p,min(p,q)} ⊆ F^s_{p,q} ⊆ B^s_{p,max(p,q)}` (`Rd.memTriebelLizorkin_of_memApprox`,
  `Rd.memApprox_of_memTriebelLizorkin`), where `B^s_{p,q}` is the approximation space `A^s_q` of
  the band-limited classes, with explicit constants
  (`Rd.approxNormDyadic_le_triebelLizorkinNorm`, `Rd.triebelLizorkinNorm_le_approxNormDyadic`).
* **Triebel–Lizorkin spaces and the Besov sandwich on the torus.** For `f ∈ L_p(𝕋^d)`,
  `1 ≤ p < ∞`, the same quasi-norm with the blocks `ψ_j ⋆ f(t) = ∫ ψ_j(y) f(t - π y) dy` of the
  kernels on `ℝ^d`, with the quotient map `π : ℝ^d → 𝕋^d`, defines `F^s_{p,q}(𝕋^d)`
  (`Torus.triebelLizorkinNorm`, `Torus.MemTriebelLizorkin`). The same bounds hold
  (`Torus.littlewoodPaleyNorm_max_le_triebelLizorkinNorm`,
  `Torus.triebelLizorkinNorm_le_littlewoodPaleyNorm_min`), and for `s > 0`,
  `F^s_{p,p}(𝕋^d) = B^s_{p,p}(𝕋^d)` (`Torus.memTriebelLizorkin_iff_memBesov`), also described by
  moduli of smoothness (`Torus.memTriebelLizorkin_iff_modulus`), and
  `B^s_{p,min(p,q)}(𝕋^d) ⊆ F^s_{p,q}(𝕋^d) ⊆ B^s_{p,max(p,q)}(𝕋^d)`
  (`Torus.memTriebelLizorkin_of_memBesov`, `Torus.memBesov_of_memTriebelLizorkin`), with explicit
  constants (`Torus.approxNormDyadic_le_triebelLizorkinNorm`,
  `Torus.triebelLizorkinNorm_le_approxNormDyadic`), where
  `B^s_{p,q}(𝕋^d)` is the approximation space of the trigonometric polynomials, described by the
  Littlewood–Paley blocks of [the torus](Torus.md).
* **Local means.** Let `k_j` be the local means kernels of order `L` of a bump `g`
  ([Besov spaces on `ℝ^d`](Rd.md)) and
  `‖f‖^{g,L}_{F^s_{p,q}} = ‖ x ↦ ‖(2^(js) |k_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p`
  (`Rd.LocalMeansBump.tlLocalMeansNorm`). For `1 < p < ∞`, `1 < q ≤ ∞` and `f ∈ L_p(V)`,
  `‖f‖^{g,L}_{F^s_{p,q}} ≤ D ‖f‖_{F^s_{p,q}}` and, for `L ≥ 1`,
  `‖f‖_{F^s_{p,q}} ≤ U ‖f‖^{g,L}_{F^s_{p,q}}`, with explicit constants `D`, `U` that are
  finite for `0 < s < L` (`Rd.LocalMeansBump.tlLocalMeansNorm_le_triebelLizorkinNorm`,
  `Rd.LocalMeansBump.triebelLizorkinNorm_le_tlLocalMeansNorm`). Hence for `0 < s < L`,
  `f ∈ F^s_{p,q}` iff `‖f‖^{g,L}_{F^s_{p,q}} < ∞`
  (`Rd.LocalMeansBump.memTriebelLizorkin_iff_tlLocalMeans`), for every bump and every such
  order (`Rd.LocalMeansBump.tlLocalMeansNorm_lt_top_iff`). The proof bounds blocks and local
  means by maximal functions of each other at every point and applies the Fefferman–Stein
  inequality.
* **Local means on the torus.** For a bump `g` on `ℝ^d` with local means kernels `k_j` of order
  `L`, acting on the torus by `k_j ⋆ f(t) = ∫ k_j(y) f(t - π y) dy`, the quasi-norm
  `‖f‖^{g,L}_{F^s_{p,q}(𝕋^d)} = ‖ t ↦ ‖(2^(js) |k_j ⋆ f(t)|)_j‖_{ℓ_q} ‖_p`
  (`Torus.tlLocalMeansNorm`) satisfies the same two bounds with explicit constants
  (`Torus.tlLocalMeansNorm_le_triebelLizorkinNorm`,
  `Torus.triebelLizorkinNorm_le_tlLocalMeansNorm`), so for `1 < p < ∞`, `1 < q ≤ ∞` and
  `0 < s < L`, `f ∈ F^s_{p,q}(𝕋^d)` iff `‖f‖^{g,L}_{F^s_{p,q}(𝕋^d)} < ∞`
  (`Torus.memTriebelLizorkin_iff_tlLocalMeans`). The pointwise bounds of `ℝ^d` apply to the
  periodic lifts `h ∘ π`, and the Fefferman–Stein inequality holds for the maximal functions of
  lifts on the period box `(0, 1]^d`, with the constant `Torus.periodicFSConst d p q`
  (`Torus.feffermanStein_periodic`).
* **Ball means of differences.** For `f : V → ℂ`, an order `L` and a level `j`, the ball mean
  of differences is `d_j f(x) = |B(0,2^(-j))|⁻¹ ∫_{B(0,2^(-j))} |Δ^L_h f(x)| dh`
  (`Rd.ballMeanDiff`), and for `f ∈ L_p(V)` the quasi-norm
  `‖f‖_p + ‖ x ↦ ‖(2^(js) d_j f(x))_j‖_{ℓ_q} ‖_p` is `Rd.tlDiffNorm`. For `1 < p < ∞`,
  `1 < q ≤ ∞`, `0 < s < L` and `f ∈ L_p(V)`, `f ∈ F^s_{p,q}` iff this quasi-norm is finite
  (`Rd.memTriebelLizorkin_iff_tlDiffNorm_lt_top`), with explicit constants in both comparisons
  with the local means quasi-norm of a bump (`Rd.LocalMeansBump.tlDiffNorm_le_tlLocalMeansNorm`,
  `Rd.LocalMeansBump.tlLocalMeansNorm_le_tlDiffNorm`). Pointwise, a local mean is bounded by a
  ball mean (`Rd.LocalMeansBump.enorm_localMean_le_ballMeanDiff`), and a ball mean by maximal
  functions of the local means (`Rd.LocalMeansBump.ballMeanDiff_le_tsum_maximal`).
* **Atoms.** For complex coefficients `λ_{j,m}` of the dyadic cells `P_{j,m}` let `λ_j(x)` be
  `|λ_{j,m}|` for the cell of level `j` containing `x` (`Rd.cellCoefFun`) and
  `‖λ‖_{f^s_{p,q}} = ‖ x ↦ ‖(2^(js) λ_j(x))_j‖_{ℓ_q} ‖_p` (`Rd.tlCoeffNorm`). For `1 < p < ∞`,
  `1 < q ≤ ∞`, `0 < s < L` and `F ∈ L_p(V)`, `F ∈ F^s_{p,q}` iff `F = ∑_j f_j` in `L_p` with
  `f_j = ∑_m λ_{j,m} a_{j,m}` almost everywhere, for smooth atoms `a_{j,m}` of level `j` and
  order `L` centred at the cells, with a common radius factor `ρ ≥ 0` and constant `A`,
  normalised in `L_∞`, and `‖λ‖_{f^s_{p,q}} < ∞`
  (`Rd.memTriebelLizorkin_iff_atomic`); no moment conditions are needed. The synthesis bounds
  the local means quasi-norm of `F` by `‖λ‖_{f^s_{p,q}}` with an explicit constant
  (`Rd.LocalMeansBump.tlLocalMeansNorm_le_tlCoeffNorm`); the decomposition takes the cell atoms
  of `η_j ⋆ (k_j ⋆ F)` with the means of `|k_j ⋆ F|` over the cells as coefficients
  (`Rd.LocalMeansBump.tl_atomic_decomposition`, `Rd.LocalMeansBump.tlCoeffNorm_cellCoef_le`).
  Triebel's *Theory of Function Spaces II* states the characterisation with `(s,p)`-atoms
  normalised in `L_p`; the two forms correspond under `λ_{j,m} ↦ 2^(j(s - n/p)) λ_{j,m}`,
  `n = dim V`.
* **Real interpolation.** Let `1 ≤ p < ∞`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`. By the
  Besov sandwich and the sandwich principle of real interpolation,
  `(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}` for `0 < s₀ < s₁` and
  `(L_p, F^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}` for `s₁ > 0`
  (`Rd.memKMethod_triebelLizorkinCouple_iff`, `Rd.memKMethod_lpTriebelLizorkinCouple_iff`), and
  the same for every couple of quasi-norms equivalent to these
  (`Rd.memKMethod_iff_memApprox_of_triebelLizorkin_equiv`,
  `Rd.memKMethod_iff_memApprox_of_triebelLizorkin_equiv_left`); on the torus the same two
  identities hold (`Torus.memKMethod_triebelLizorkinCouple_iff`,
  `Torus.memKMethod_lpTriebelLizorkinCouple_iff`).
* **Dilation families and the Hörmander condition.** Let `(G_j)_{j ∈ ℕ}` be Schwartz functions
  on `V`, `dim V = n`, whose Schwartz seminorms `sup_x ‖x‖^k ‖D^l G_j(x)‖` are at most `A_{k,l}`
  for every `j` (`Rd.IsUniformSchwartz`), and `θ_j(x) = 2^(jn) G_j(2^j x)`. For every `y ∈ V`,
  `∫_{‖x‖ > 2‖y‖} ‖(θ_j(x - y) - θ_j(x))_j‖_{ℓ_2} dx ≤ 4 H_A` with an explicit constant `H_A`
  built from the bounds `A` (`Rd.lintegral_lqNorm_sub_le`, `Rd.familyHormanderConst`); the proof
  bounds each term by `H_A min(2^j ‖y‖, (2^j ‖y‖)⁻¹)`
  (`Rd.setLIntegral_enorm_dilate_sub_le_min`) and uses
  `∑_j min(2^j a, (2^j a)⁻¹) ≤ 4` for every `a ∈ [0, ∞]` (`ENNReal.tsum_min_two_pow_le`). A
  Calderón–Zygmund family with Fourier overlap `B` and Hörmander constant `H`
  (`Rd.IsCZFamily`) consists of integrable, continuous, bounded kernels `θ_j` with integrable
  Fourier transforms, `∑_j |𝓕θ_j(ξ)|² ≤ B` for every `ξ`, and the Hörmander integral at most `H`
  for every `y`; uniform dilation families with overlap `B` are such families with
  `H = 4 H_A` (`Rd.IsCZFamily.of_dilation`), and so are the adjoint kernels
  `θ_j^*(x) = conj θ_j(-x)` with the same `B` and `H` (`Rd.IsCZFamily.adjoint`). The
  Littlewood–Paley blocks `ψ_j` form such a family with overlap `2` (`Rd.isCZFamily_psi`), and so
  do the synthesis kernels `ψ̃_0 = Φ_1`, `ψ̃_1 = Φ_2`, `ψ̃_j = Φ_{j+1} - Φ_{j-2}` with overlap `4`
  (`Rd.psiDual`, `Rd.isCZFamily_psiDual`), which reproduce the blocks: `ψ̃_j ⋆ ψ_j = ψ_j`
  (`Rd.conv_psiDual_psi`).
* **The adjoint of a convolution.** For `K ∈ L_1(V)`, `f ∈ L_p(V)` and `g ∈ L_q(V)` with
  `1/p + 1/q = 1`, `p < ∞`, and the reflection `K^∨(x) = K(-x)` (`Rd.reflect`),
  `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)` (`Rd.integral_conv_mul`). For Schwartz functions `η`, `u`,
  `f ∈ L_p(V)`, `1 ≤ p < ∞`, and `w ∈ V^k`, `∫ ((∂^w η) ⋆ f) u = (-1)^k ∫ (η ⋆ f) ∂^w u`
  (`Rd.integral_conv_iteratedLineDerivOp_mul`). Weak derivatives commute with convolution by a
  Schwartz function `η`: if `g ∈ L_r(V)` is the weak derivative `∂^v f` of `f ∈ L_p(V)` on `V`,
  `1 ≤ p, r ≤ ∞`, then `η ⋆ g = (∂^v η) ⋆ f` at every point
  (`Rd.conv_eq_conv_iteratedLineDerivOp`), and `(∂^v η) ⋆ f` is the weak derivative
  `∂^v (η ⋆ f)` for `f ∈ L_p(V)`, `1 ≤ p < ∞` (`Rd.hasWeakLineDeriv_conv`).
* **Plancherel bounds.** For integrable kernels `θ_j` on `V` with `∑_j |𝓕θ_j(ξ)|² ≤ B` for
  almost every `ξ`, the analysis operator satisfies `∑_j ‖θ_j ⋆ f‖_2² ≤ B ‖f‖_2²` for every
  `f ∈ L_2(V)` (`Rd.tsum_enorm_convLp_sq_le`, `Rd.lintegral_lqNorm_conv_sq_le`), and the
  synthesis operator satisfies `‖∑_{j ∈ s} θ_j ⋆ g_j‖_2² ≤ B ∑_{j ∈ s} ‖g_j‖_2²` for all
  `g_j ∈ L_2(V)` and every finite set `s` (`Rd.enorm_sum_convLp_sq_le`,
  `Rd.lintegral_enorm_sum_conv_sq_le`); in particular for every Calderón–Zygmund family with
  overlap `B` (`Rd.IsCZFamily.lintegral_lqNorm_conv_sq_le`,
  `Rd.IsCZFamily.lintegral_enorm_sum_conv_sq_le`).
* **The weak type `(1,1)` of vector-valued singular integrals.** Let `n = dim V ≥ 1` and let
  `(θ_j)_j` be a Calderón–Zygmund family with overlap `B` and Hörmander constant `H`, and put
  `C = 4 · 2^n B + (2n)^n |B(0, 1)| + 4H` (`Rd.vectorWeakConst`). For every `0 < t < ∞` and
  every integrable `f : V → ℂ`, `|{x : ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} > t}| ≤ C t⁻¹ ∫ |f|`
  (`Rd.IsCZFamily.volume_lqNorm_conv_gt_le`), and for every finite set `s` and all almost
  everywhere strongly measurable `g_j` with `∫ ‖(g_j(x))_j‖_{ℓ_2} dx < ∞`,
  `|{x : |∑_{j ∈ s} (θ_j ⋆ g_j)(x)| > t}| ≤ C t⁻¹ ∫ ‖(g_j(x))_j‖_{ℓ_2} dx`
  (`Rd.IsCZFamily.volume_enorm_sum_conv_gt_le`).
* **The strong type of vector-valued singular integrals.** Let `n = dim V ≥ 1`, `1 < p < ∞`, and
  let `(θ_j)_j` be a Calderón–Zygmund family with overlap `B` and Hörmander constant `H`. With the
  explicit constant `S = S_{V,p}(B, H)` (`Rd.czConst`: `B^{1/2}` for `p = 2`, the Marcinkiewicz
  constant `(p (2 C/(p - 1) + 4B/(2 - p)))^(1/p)` with the weak type constant `C` above for
  `p < 2`, and that constant at the conjugate exponent `p/(p - 1)` for `p > 2`), every
  `f ∈ L_p(V)` satisfies `‖ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p ≤ S ‖f‖_p`
  (`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`), and for every finite set `s` and all `g_j ∈ L_p(V)`,
  `‖∑_{j ∈ s} θ_j ⋆ g_j‖_p ≤ S ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_p` (`Rd.IsCZFamily.eLpNorm_sum_conv_le`).
  For `p > 2` the norms are bounded through their pairings with `L_{p/(p-1)}`
  (`MeasureTheory.eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le`), tested on the norming
  family `u_j ‖(u_i)_i‖_{ℓ_2}^{p-2}` (`MeasureTheory.normingFamily`).
* **The square function theorem.** Let `n = dim V ≥ 1` and `1 < p < ∞`. By definition,
  `‖f‖_{F^0_{p,2}}` is the `L_p` norm of the square function `x ↦ ‖((ψ_j ⋆ f)(x))_j‖_{ℓ_2}` of
  the Littlewood–Paley blocks (`Rd.triebelLizorkinNorm_zero_two_eq`). The theorem is the
  two-sided bound: for every `f ∈ L_p(V)`,
  `‖f‖_{F^0_{p,2}} ≤ Q_{V,p} ‖f‖_p` (`Rd.triebelLizorkinNorm_zero_two_le`) and
  `‖f‖_p ≤ Q̃_{V,p} ‖f‖_{F^0_{p,2}}` (`Rd.enorm_le_triebelLizorkinNorm_zero_two`) with the
  named constants `Q_{V,p} = S_{V,p}(2, 4 H_{A^ψ})` and `Q̃_{V,p} = S_{V,p}(4, 4 H_Ã)` of the
  Calderón–Zygmund families of the blocks and of the synthesis kernels
  (`Rd.squareFunctionConst`, `Rd.squareSynthesisConst`), where `A^ψ` and `Ã` are the seminorm
  bounds of the blocks and of the synthesis kernels (`Rd.psiBaseBound`, `Rd.psiDualBaseBound`),
  formulas in Schwartz seminorms of fixed kernels, proved finite
  (`Rd.squareFunctionConst_ne_top`, `Rd.squareSynthesisConst_ne_top`).
  Hence `F^0_{p,2} = L_p(V)` (`Rd.triebelLizorkinSpace_zero_two_eq_top`). The lower bound uses
  the reproducing formula `∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f) → f` in `L_p(V)`
  (`Rd.tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub`).
* **The square function theorem on the torus.** Let `d ≥ 1` and `1 < p < ∞`. A
  Calderón–Zygmund family `(θ_j)_j` on `ℝ^d` with overlap `B` and Hörmander constant `H` acts on
  the torus by `(θ_j ⋆ f)(t) = ∫ θ_j(y) f(t - π y) dy`. If its far mass
  `∫_{‖y‖ ≥ 1} ∑_j |θ_j(y)| dy` is at most `D` (`Torus.farMass`), its analysis and synthesis
  operators satisfy the bounds of the strong type on `L_p(𝕋^d)` with the constant
  `3^{d/p} S_{ℝ^d,p}(B, H) + D` (`Torus.periodicCZConst`, `Torus.eLpNorm_lqNorm_econv_le`,
  `Torus.eLpNorm_sum_econv_le`). The proof localises the periodic lift: the part of the lift on
  the box `(-1, 2]^d` is a function on `ℝ^d`, and the rest is bounded by Young's inequality
  with the far mass (`Torus.eLpNorm_farConv_le`). Dilation families of uniform Schwartz families
  with bounds `A` have far mass at most `2 T_A` (`Torus.farMass_dilate_le`). Hence
  `‖f‖_{F^0_{p,2}(𝕋^d)} ≤ Q^𝕋_p ‖f‖_p` and `‖f‖_p ≤ Q̃^𝕋_p ‖f‖_{F^0_{p,2}(𝕋^d)}` for every
  `f ∈ L_p(𝕋^d)` (`Torus.triebelLizorkinNorm_zero_two_le`,
  `Torus.enorm_le_triebelLizorkinNorm_zero_two`), with named constants proved finite
  (`Torus.squareFunctionConst`, `Torus.squareSynthesisConst`), and
  `F^0_{p,2}(𝕋^d) = L_p(𝕋^d)` (`Torus.triebelLizorkinSpace_zero_two_eq_top`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Triebel–Lizorkin spaces on `ℝ^d`: definition, `F_{p,p} = B_{p,p}`, the Besov sandwich | ✅ | ✗ | `Rd/TriebelLizorkin/TriebelLizorkin` |
| Local means characterisation of Triebel–Lizorkin spaces, and synthesis with the dual kernels in `F^s_{p,q}` | ✅ | ✗ | `Rd/TriebelLizorkin/TriebelLizorkinLocalMeans` |
| Characterisation by ball means of differences | ✅ | ✗ | `Rd/TriebelLizorkin/TriebelLizorkinDifferences` |
| `f^s_{p,q}`, atomic analysis, synthesis, characterisation | ✅ | ✗ | `Rd/TriebelLizorkin/TriebelLizorkinAtoms` |
| Triebel–Lizorkin spaces on the torus, the Besov sandwich | ✅ | ✗ | `Torus/TriebelLizorkin` |
| The periodic lift: period boxes, lifted null sets, counting boxes | ✅ | ✗ | `Torus/PeriodicLift` |
| The Fefferman–Stein inequality for periodic lifts | ✅ | ✗ | `Torus/FeffermanStein` |
| Local means characterisation on the torus | ✅ | ✗ | `Torus/TriebelLizorkinLocalMeans` |
| Triebel–Lizorkin spaces on `ℝ^d` interpolate to Besov spaces: `(F^{s₀}_{p,q₀}, F^{s₁}_{p,q₁})_{η,q}` and `(L_p, F^{s₁}_{p,q₁})_{η,q}` | ✅ | ✗ | `Rd/Interpolation/TriebelLizorkinInterpolation` |
| Triebel–Lizorkin spaces on the torus interpolate to Besov spaces | ✅ | ✗ | `Torus/TriebelLizorkinInterpolation` |
| Dilation, reflection and conjugation of Schwartz functions, derivatives of dilations, uniform Schwartz families and finitely many exceptions in them, the Hörmander condition for dilation families with explicit constants, Calderón–Zygmund families, also with finitely many exceptional members, and their adjoints, the Littlewood–Paley blocks and the synthesis kernels as such families | ✅ | ✗ | `Rd/SingularIntegrals/DilationFamilies` |
| The adjoint identity `∫ (K ⋆ f) g = ∫ f (K^∨ ⋆ g)` for `f ∈ L_p`, `g ∈ L_q`, and its form `∫ (K ⋆ f) conj g = ∫ f conj(K^* ⋆ g)` with the adjoint kernel, derivatives of Schwartz kernels moved to the other Schwartz factor, translates and reflections of Schwartz functions, and weak derivatives commuting with convolution by Schwartz functions, on `ℝ^d`, in `L_p` and on open sets | ✅ | ✗ | `Rd/SingularIntegrals/ConvolutionAdjoint` |
| The Cauchy–Schwarz inequality for finite sums, the `L_2` bounds of the analysis operator and of the synthesis operators on finite index sets for a kernel family with Fourier overlap `B`, and for every Calderón–Zygmund family | ✅ | ✗ | `Rd/SingularIntegrals/PlancherelBounds` |
| Chebyshev's inequality for split functions, the Hörmander condition around a cube, convolutions of pieces with mean zero, and the weak type `(1,1)` of the analysis and synthesis operators of a Calderón–Zygmund family with an explicit constant | ✅ | ✗ | `Rd/SingularIntegrals/VectorValuedWeakType` |
| The strong type `(p,p)`, `1 < p < ∞`, of the analysis and synthesis operators of a Calderón–Zygmund family with explicit constants: Plancherel for `p = 2`, Marcinkiewicz interpolation for `p < 2`, duality with the adjoint family for `p > 2` | ✅ | ✗ | `Rd/SingularIntegrals/VectorValuedSingularIntegrals` |
| The square function theorem `L_p = F^0_{p,2}` for `1 < p < ∞`, the two-sided bound with named constants, and the reproducing formula `∑_{j < J} ψ̃_j ⋆ (ψ_j ⋆ f) → f` in `L_p` | ✅ | ✗ | `Rd/TriebelLizorkin/SquareFunction` |
| Strong type of vector-valued singular integrals on the torus | ✅ | ✗ | `Torus/SingularIntegrals` |
| The square function theorem `L_p(𝕋^d) = F^0_{p,2}(𝕋^d)` | ✅ | ✗ | `Torus/SquareFunction` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
