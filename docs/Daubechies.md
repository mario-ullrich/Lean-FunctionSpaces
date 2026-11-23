# Daubechies wavelets

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Besov spaces*,
chapters *Daubechies wavelets* and *Tensor Daubechies wavelets on `ℝ^d`*.

The compactly supported orthonormal wavelets of Daubechies on `ℝ` and `ℝ^d`, built from the
filter up, and the description of `B^s_{p,q}(ℝ)`, `B^s_{p,q}(ℝ^d)` and `H^s(ℝ^d)` by their
coefficients. A mask of order `N`
comes from the Fejér–Riesz theorem, the scaling function is the inverse Fourier transform of the
infinite product of its symbol, and everything about it is proved with the Fourier transform of
integrable functions: the refinement equation, the compact support through the cascade
algorithm, the orthonormality of the translates and the reproduction of polynomials. The
transfer operator of Eirola and Villemoes gives the Sobolev regularity, the matrix method of
Daubechies and Lagarias the Hölder exponent of D4. The projections onto the spaces `V_j` form a
projection scheme in the sense of [Approximation spaces](ApproximationSpaces.md); Jackson's and
Bernstein's inequalities identify its approximation spaces with the Besov spaces of
[Besov spaces on `ℝ^d`](Rd.md), as for the Haar system and the multiwavelets of
[Intervals, the cube, splines and wavelets](IntervalCube.md). On `ℝ^d` the integer translates of
the tensor products of the scaling function and the wavelet are orthonormal, the Bernstein bounds
of the scaling function bound their moduli of smoothness, and the expansions in their dilated and
translated copies are stable in `L_p` and satisfy Bernstein's inequality. Their projections form a
multiresolution analysis of `L_p(ℝ^d)` with the block identity and the inverse inequality, and the
projections of one variable, applied in one coordinate, satisfy Jackson's inequality with the
isotropic modulus of smoothness of `ℝ^d`. Applied in all coordinates they map continuous functions
into the scaling spaces, which gives Jackson's inequality on `ℝ^d`, and as on `ℝ` the Besov spaces
on `ℝ^d` and on every finite-dimensional inner product space, and `H^s`, are described by the
coefficients of the tensor wavelets. The translates of the tensor scaling function and the tensor
wavelets of all levels form a Hilbert basis of `L_2(ℝ^d)`, in which `H^s` is a weighted `ℓ_2` and
`n`-term approximation is described by the Besov spaces `B^{d(1/τ - 1/2)}_{τ,τ}(ℝ^d)`.

## Main results

* **Masks of every order.** A mask of order `N` is a real polynomial `L` of degree `< N` with
  `L(1) = 1` and `|L(e^(-2πiξ))|² = P_N(sin²(πξ))`, where `P_N(y) = ∑_{k<N} C(N-1+k, k) y^k`
  (`Daubechies.Mask`, `Daubechies.daubPoly`); its filter coefficients `c_k` are those of
  `2 ((1 + z)/2)^N L(z)` (`Daubechies.daubechiesCoeff`). Masks of order `N` exist iff `N ≥ 1`
  (`Daubechies.nonempty_mask_iff`), by the Fejér–Riesz theorem: a real polynomial `Q` with
  `Q > 0` on `[-1, 1]` satisfies `Q(cos θ) = |L(e^(iθ))|²` for all `θ` with a real polynomial `L`
  of degree `≤ deg Q` and `L(1) > 0` (`Polynomial.fejer_riesz`). For `N = 2` the mask whose
  polynomial `L` has no zeros in the closed unit disk is D4, with
  `c = ((1+√3), (3+√3), (3-√3), (1-√3))/4` (`Daubechies.eq_d4_iff_aeval_ne_zero`,
  `Daubechies.daubechiesCoeff_d4`).
* **The scaling function.** Let `N ≥ 2`, `m_0(ξ) = (1/2) ∑_k c_k e^(-2πikξ)` and
  `Φ(ξ) = ∏_{j ≥ 1} m_0(2^(-j) ξ)`. Then `Φ` is integrable, and `φ = 𝓕⁻¹ Φ` is a continuous real
  function with `φ(x) = ∑_k c_k φ(2x - k)` (`Daubechies.scalingFun_refine`), `φ = 0` outside
  `[0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`), `∫ φ = 1` (`Daubechies.integral_scalingFun`)
  and `∫ φ(x - k) conj φ(x - l) dx = δ_{kl}` for `k, l ∈ ℤ`
  (`Daubechies.integral_scalingFun_translate_mul_conj_translate`). Every polynomial `Q` of
  degree `< N` satisfies `∑_k ⟨Q, φ(· - k)⟩ φ(x - k) = Q(x)` for all `x`
  (`Daubechies.sum_inner_poly_mul_scalingFun`).
* **Sobolev regularity.** Let `T g(ξ) = P(ξ/2) g(ξ/2) + P((ξ+1)/2) g((ξ+1)/2)` with
  `P(ξ) = P_N(sin²(πξ))` (`Daubechies.transferOp`). If `T^n 1 ≤ C λ^n` for all `n` (the
  hypothesis `Daubechies.TransferGrowth`), then `∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ < ∞` for every
  `s < N - log₄ λ` (`Daubechies.integrable_rpow_mul_normSq`), and for `p ≤ 2`, `0 ≤ s ≤ r` and
  `0 < t ≤ 1`, `ω_r(φ, t)_p ≤ K t^s` (`Daubechies.smoothnessModulus_scalingFun_le_two`). For
  `N = 2`, `T 1 = 4`, and for `N = 3`, `T^n 1 ≤ 2 · 9^n` (`Daubechies.transferGrowth_two`,
  `Daubechies.transferGrowth_three`): the scaling functions lie in `H^s` for `s < 1` and for
  `s < 3 - log₂ 3 ≈ 1.415`, the Sobolev exponents of Eirola and Villemoes.
* **Hölder regularity.** Under the same growth bound, `|φ(x) - φ(y)| ≤ K |x - y|^a` for
  `0 ≤ a ≤ 1` with `a < N - log₄ λ - 1/2` (`Daubechies.holder_scalingFun_fourier`). For D4 the
  matrix method of Daubechies and Lagarias, in a scalar form, gives every exponent
  `a ≤ 2 - log₂(1 + √3)`, and `2 - log₂(1 + √3) > 0.55` (`Daubechies.holder_d4`,
  `Daubechies.two_sub_logb_two_one_add_sqrt_three_gt`).
* **Besov spaces by Daubechies coefficients.** Let `ψ(x) = ∑_k (-1)^k c_(1-k) φ(2x - k)`
  (`Daubechies.wavelet`) and `g_{j,k}(x) = 2^(j/2) g(2^j x - k)`. Let `N ≥ 2`, `1 ≤ p < ∞`,
  `1 ≤ q ≤ ∞`, assume `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1` (the hypothesis
  `Daubechies.BernsteinBound`, proved by the regularity theorems above) and
  let `0 < s < θ`. Then `f ∈ L_p(ℝ)` satisfies the Besov condition
  `‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff it satisfies the coefficient condition
  `‖(⟨f, φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s+1/2-1/p)) ‖(⟨f, ψ_{j,k}⟩)_k‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
  (`Daubechies.besov_iff_coeff`, `Daubechies.daubechiesCoeffNorm`), and the same holds for the
  Littlewood–Paley norm (`Daubechies.littlewoodPaleyNorm_lt_top_iff_coeff`). The bound holds
  for every `θ < N - log₄ λ` if `p ≤ 2` (`Daubechies.besov_iff_coeff_of_le_two`) and for
  `θ = (2/p) s' + (1 - 2/p) a` with `s' < N - log₄ λ` and a Hölder exponent `a` of `φ` if
  `p ≥ 2` (`Daubechies.besov_iff_coeff_of_two_le`,
  `Daubechies.besov_iff_coeff_of_two_le_of_holder`).
  The theorem rests on Jackson's inequality `E_{2^j}(f)_p ≤ C ω_N(f, 2^(-j))_p` for the spaces
  `V_j = span{φ_{j,k}}` (`Daubechies.approxError_scheme_le`) and on Bernstein's inequality for them
  (`Daubechies.inverse_scheme`).
* **D4.** Let `α = 2 - log₂(1 + √3) ≈ 0.55`. With differences of order `2`, the Besov condition
  and the coefficient condition are equivalent for `1 ≤ p ≤ 2` and `0 < s < 1`
  (`Daubechies.besov_iff_coeff_d4_le_two`), for `2 ≤ p < ∞` and `0 < s < 2/p + (1 - 2/p) α`
  (`Daubechies.besov_iff_coeff_d4_two_le`), and hence for every `1 ≤ p < ∞` and `0 < s < α`
  (`Daubechies.besov_iff_coeff_d4`).
* **Order three.** Every mask of order `3` has `φ ∈ H^s` for `s < 3 - log₂ 3 ≈ 1.415`
  (`Daubechies.sobolev_scalingFun_order_three`) and `|φ(x) - φ(y)| ≤ K |x - y|^(9/10)`
  (`Daubechies.holder_scalingFun_order_three_nine_tenths`). With differences of order `3`, the
  Besov condition and the coefficient condition are equivalent for `1 ≤ p ≤ 2` and
  `0 < s < 3 - log₂ 3` (`Daubechies.besov_iff_coeff_order_three_le_two`), for `2 ≤ p < ∞` and
  `0 < s < 5/2 - log₂ 3 + 1/p` (`Daubechies.besov_iff_coeff_order_three_two_le`), and hence for
  every `1 ≤ p < ∞` and `0 < s < 5/2 - log₂ 3` (`Daubechies.besov_iff_coeff_order_three`).
* **Tensor generators on `ℝ^d`.** For a set `e` of coordinates let
  `Ψ^e(x) = ∏_{i ∈ e} ψ(x_i) ∏_{i ∉ e} φ(x_i)` (`Daubechies.tensorGen`). For `N ≥ 2` and
  `k, l ∈ ℤ^d`, `∫ Ψ^e(x - k) conj Ψ^{e'}(x - l) dx` is `1` if `e = e'` and `k = l`, and `0`
  otherwise (`Daubechies.integral_tensorGen_translate_mul_conj_translate`). If `φ` has a
  Bernstein bound of order `θ` in `L_p`, `1 ≤ p < ∞`, with differences of order `N`, and
  `0 ≤ θ' ≤ θ` with `θ' < N`, then there is `K < ∞` with `‖Δ_h^N Ψ^e‖_p ≤ K ‖h‖^{θ'}` for every
  `e` and every `h ∈ ℝ^d` with `‖h‖ ≤ 1` in the sup norm
  (`Daubechies.eLpNorm_higherDiff_tensorGen_le`).
* **Expansions on `ℝ^d`.** Let `G_ν`, `ν ∈ I`, be finitely many measurable functions on `ℝ^d`
  that vanish outside `[a, b]^d`, let `G_{ν,j,k}(x) = 2^(jd/2) G_ν(2^j x - k)`
  (`Daubechies.tensorScaled`), `1 ≤ p < ∞`, `p'` the conjugate exponent and
  `L = |I| (⌈b - a⌉ + 1)^d`. Then
  `‖∑ c_{ν,k} G_{ν,j,k}‖_p ≤ L^(1 - 1/p) max_ν ‖G_ν‖_p 2^(jd(1/2 - 1/p)) ‖c‖_{ℓ_p}`
  (`Daubechies.eLpNorm_tensorExpand_le`) and, for every measurable `f`,
  `‖(⟨f, G_{ν,j,k}⟩)_{ν,k}‖_{ℓ_p} ≤ L^(1/p) max_ν ‖G_ν‖_{p'} 2^(-jd(1/2 - 1/p)) ‖f‖_p`
  (`Daubechies.lqNorm_tensorCoeff_le`). Let `C' = L^(1/p) max_ν ‖G_ν‖_{p'}`
  (`Daubechies.tensorCoeffConst`). If the `G_ν` are continuous with orthonormal integer
  translates, the coefficients of an expansion are recovered
  (`Daubechies.tensorCoeff_tensorExpand`), so
  `2^(jd(1/2 - 1/p)) ‖c‖_{ℓ_p} ≤ C' ‖∑ c_{ν,k} G_{ν,j,k}‖_p`
  (`Daubechies.lqNorm_le_eLpNorm_tensorExpand`). If a measurable `f` is almost everywhere the
  expansion of its own coefficients of level `j` and `2^j t ≤ 1`, then
  `ω_r(f, t)_p ≤ C sup_{ν, ‖H‖ ≤ 2^j t} ‖Δ_H^r G_ν‖_p ‖f‖_p` with `C = L_r^(1 - 1/p) C'` and
  `L_r = |I| (⌈b - a + 2r⌉ + 1)^d` (`Daubechies.smoothnessModulus_tensorExpand_le`,
  `Daubechies.tensorBernsteinConst`).
* **The multiresolution analysis on `ℝ^d`.** Let `N ≥ 2`, `Φ = Ψ^∅`,
  `P_j f = ∑_k ⟨f, Φ_{j,k}⟩ Φ_{j,k}` and `Q_j f = ∑_{e ≠ ∅} ∑_k ⟨f, Ψ^e_{j,k}⟩ Ψ^e_{j,k}` with
  `G_{j,k}(x) = 2^(jd/2) G(2^j x - k)` (`Daubechies.tensorProjFun`, `Daubechies.tensorDetailFun`).
  Then `P_{j+1} f = P_j f + Q_j f` for every locally integrable `f`
  (`Daubechies.tensorProjFun_succ_eq_add`), from the kernel identity
  `∑_k Φ_{j+1,k}(x) conj Φ_{j+1,k}(y) = ∑_e ∑_k Ψ^e_{j,k}(x) conj Ψ^e_{j,k}(y)` over all sets `e`
  of coordinates (`Daubechies.tsum_tensorGen_empty_mul_conj_succ`). For `1 ≤ p < ∞` the `P_j`
  are projections on `L_p(ℝ^d)`, bounded uniformly in `j`, onto increasing spaces `V_j`
  (`Daubechies.tensorProj`, `Daubechies.tensorScalingSpace`, `Daubechies.tensorScheme`), and
  `‖P_{j+1} f - P_j f‖_p` is comparable with `2^(jd(1/2 - 1/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p}`
  uniformly in `j` (`Daubechies.enorm_tensorBlock_equiv`). If `φ` has a Bernstein bound of order
  `θ` with differences of order `N` and `0 ≤ θ' ≤ θ`, `θ' < N`, then
  `ω_N(v, 2^(-k))_p ≤ C 2^(-(k-j)θ') ‖v‖_p` for all `v ∈ V_j` and `k ≥ j`
  (`Daubechies.tensor_inverse_scheme`).
* **Jackson's inequality in one coordinate.** Let `P_j^{(i)} f(x) = P_j(f_{x,i})(x_i)` apply the
  projection of one variable to the slices of `f` in coordinate `i` (`Daubechies.sliceProj`). For
  `N ≥ 2`, `1 ≤ p < ∞` and continuous `f : ℝ^d → ℂ`,
  `‖f - P_j^{(i)} f‖_p ≤ C_J ω_N(f, 2^(-j))_p` with the Jackson constant of one variable and the
  isotropic modulus of `ℝ^d` (`Daubechies.eLpNorm_sub_sliceProj_le`), and
  `‖P_j^{(i)} f‖_p ≤ C ‖f‖_p` for measurable `f` (`Daubechies.eLpNorm_sliceProj_le`).
* **Jackson's inequality on `ℝ^d`.** Let `R_j = P_j^{(1)} ⋯ P_j^{(d)}`
  (`Daubechies.foldSliceProj`). For continuous `f`, `R_j f = ∑_k c_k Φ_{j,k}` with constants
  `c_k` (`Daubechies.foldSliceProj_eq_tensorExpand`) and
  `‖f - R_j f‖_p ≤ (1 + C)^d d C_J ω_N(f, 2^(-j))_p`
  (`Daubechies.eLpNorm_sub_foldSliceProj_le_smoothnessModulus`). Hence, for `N ≥ 2`, `1 ≤ p < ∞` and
  every `f ∈ L_p(ℝ^d)`, `E_{2^j}(f)_p ≤ C_{J,d} ω_N(f, 2^(-j))_p` for the best approximation from
  `V_j` (`Daubechies.approxError_tensorScheme_le`), `‖f - P_j f‖_p ≤ C ω_N(f, 2^(-j))_p`
  (`Daubechies.enorm_sub_tensorProj_le`), and `P_j f → f` (`Daubechies.tendsto_tensorProj`).
* **Besov spaces by tensor wavelet coefficients.** Let `N ≥ 2`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, let
  `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1` and `0 < s < min(θ, N)`. Then `f ∈ L_p(ℝ^d)` satisfies
  `‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (sup norm on `ℝ^d`) iff
  `‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s+d/2-d/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e≠∅,k}‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
  (`Daubechies.tensor_besov_iff_coeff`, `Daubechies.tensorCoeffNorm`); both describe the
  approximation space `A^s_q` of the spaces `V_j` (`Daubechies.memApprox_tensorScheme_iff_modulus`,
  `Daubechies.memApprox_tensorScheme_iff_coeff`). The ranges of one variable carry over: for
  masks of order three, `0 < s < 3 - log₂ 3` if `p ≤ 2` and `0 < s < 5/2 - log₂ 3` for every `p`
  (`Daubechies.tensor_besov_iff_coeff_order_three_le_two`,
  `Daubechies.tensor_besov_iff_coeff_order_three`); for D4 and `α = 2 - log₂(1 + √3)`,
  `0 < s < 1` if `p ≤ 2`, `0 < s < 2/p + (1 - 2/p) α` if `p ≥ 2`, and `0 < s < α` for every `p`
  (`Daubechies.tensor_besov_iff_coeff_d4_le_two`, `Daubechies.tensor_besov_iff_coeff_d4_two_le`,
  `Daubechies.tensor_besov_iff_coeff_d4`). The condition `s < N` costs nothing, since every
  Bernstein bound has `θ ≤ N`. On
  a finite-dimensional inner product space `V` the same holds for `F ∈ L_p(V)` with the
  coefficients of `F` in the coordinates of the dyadic grid
  (`Daubechies.tensor_besov_iff_coeff_grid`, `Rd.gridCoord`).
* **`H^s` by coefficients.** Under the same hypotheses for `p = 2`, a tempered distribution `u`
  lies in `H^s(V)` iff it is an `f ∈ L_2(V)` with
  `∑_k |⟨f, Φ(· - k)⟩|² + ∑_j 2^(2js) ∑_{e≠∅,k} |⟨f, Ψ^e_{j,k}⟩|² < ∞` in grid coordinates
  (`Daubechies.memSobolev_two_iff_tensorCoeff`); for masks of order three this holds for
  `0 < s < 3 - log₂ 3 ≈ 1.415`, which covers `H^1`
  (`Daubechies.memSobolev_two_iff_tensorCoeff_order_three`).
* **The tensor wavelet basis of `L_2(ℝ^d)`.** For `N ≥ 2` the functions `Φ(· - k)`, `k ∈ ℤ^d`,
  and `Ψ^e_{j,k}`, `j ∈ ℕ`, `e ≠ ∅`, `k ∈ ℤ^d`, form a Hilbert basis of `L_2(ℝ^d)` whose
  coefficients are `⟨f, Φ(· - k)⟩` and `⟨f, Ψ^e_{j,k}⟩` (`Daubechies.tensorWaveletBasis`,
  `Daubechies.tensorWaveletBasis_repr_inl`, `Daubechies.tensorWaveletBasis_repr_inr`); an
  `f ∈ L_p(ℝ^d)`, `1 ≤ p < ∞`, with all coefficients zero is zero
  (`Daubechies.eq_zero_of_tensorCoeff_eq_zero`). With the weights `w_i = 1` at the scaling
  functions and `w_i = 2^(js)` at the wavelets of level `j`, `u ∈ H^s(V)` iff `u` is an
  `f ∈ L_2(V)` with `∑_i (w_i |⟨f, b_i⟩|)² < ∞` in grid coordinates, under the hypotheses of
  `H^s` by coefficients (`Daubechies.memSobolev_two_iff_weighted`,
  `Daubechies.memSobolev_two_iff_weighted_order_three`). For `s > 0`, `1 ≤ p < ∞` and
  `1 ≤ r < ∞`, every `f ∈ L_r(ℝ^d)` with finite coefficient quasi-norm in `L_p` lies in `L_p`
  (`Daubechies.memLp_of_tensorCoeffNorm_lt_top`).
* **`n`-term approximation from the tensor wavelet basis.** For `0 < τ < 2` and
  `θ = 1/τ - 1/2`, an `f ∈ L_2(ℝ^d)` lies in the approximation space `A^θ_τ` of `n`-term
  approximation from the basis iff
  `‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_τ} + ‖(‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_τ})_j‖_{ℓ_τ} < ∞`
  (`Daubechies.memApprox_nTerm_tensorWaveletBasis_iff_coeff`). For `d ≥ 1`, `1 ≤ τ < 2` and
  `α = dθ < min(θ_B, N)`, where `θ_B` is the order of a Bernstein bound of `φ` in `L_τ`, this
  holds iff `f ∈ L_τ(ℝ^d)` and `‖f‖_τ + ‖(2^(kα) ω_N(f, 2^(-k))_τ)_k‖_{ℓ_τ} < ∞`, that is,
  `A^θ_τ = B^α_{τ,τ}(ℝ^d) ∩ L_2(ℝ^d)` (`Daubechies.memApprox_nTerm_tensorWaveletBasis_iff`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| The Daubechies polynomial, its Bézout identity, values and bounds | ✅ | ✗ | `Wavelets/Examples/Daubechies/DaubechiesPolynomial` |
| Fourier transforms of integrable functions on `ℝ`: multiplication formula, Parseval, Schwartz test functions | ✅ | ✗ | `Wavelets/Examples/Daubechies/FourierIntegrable` |
| The Fejér–Riesz theorem and masks of every order | ✅ | ✗ | `Wavelets/Examples/Daubechies/FejerRiesz`, `Wavelets/Examples/Daubechies/MaskExistence` |
| Masks, the symbol, filter identities, the mask D4 | ✅ | ✗ | `Wavelets/Examples/Daubechies/Mask`, `Wavelets/Examples/Daubechies/FilterIdentities`, `Wavelets/Examples/Daubechies/D4` |
| The symbol product and its modulus | ✅ | ✗ | `Wavelets/Examples/Daubechies/SymbolProduct` |
| The transfer operator, the decay of the symbol product, orders two and three | ✅ | ✗ | `Wavelets/Examples/Daubechies/TransferOperator`, `Wavelets/Examples/Daubechies/SymbolDecay`, `Wavelets/Examples/Daubechies/TransferExamples` |
| The scaling function, the cascade algorithm, compact support | ✅ | ✗ | `Wavelets/Examples/Daubechies/ScalingFunction`, `Wavelets/Examples/Daubechies/Cascade` |
| Orthonormality and moments | ✅ | ✗ | `Wavelets/Examples/Daubechies/Orthonormality`, `Wavelets/Examples/Daubechies/ScalingMoments` |
| Sobolev and Hölder regularity of the scaling function | ✅ | ✗ | `Wavelets/Examples/Daubechies/SobolevRegularity`, `Wavelets/Examples/Daubechies/HolderRegularity` |
| The matrix method and the Hölder exponent of D4 | ✅ | ✗ | `Wavelets/Examples/Daubechies/MatrixMethod`, `Wavelets/Examples/Daubechies/MatrixMethodD4` |
| Expansions, polynomial reproduction, projections, the multiresolution analysis, the wavelet | ✅ | ✗ | `Wavelets/Examples/Daubechies/Expansion`, `Wavelets/Examples/Daubechies/ExpansionScaling`, `Wavelets/Examples/Daubechies/PolynomialReproduction`, `Wavelets/Examples/Daubechies/Projections`, `Wavelets/Examples/Daubechies/Wavelet` |
| Jackson's and Bernstein's inequalities | ✅ | ✗ | `Wavelets/Examples/Daubechies/JacksonSmoothing`, `Wavelets/Examples/Daubechies/Jackson`, `Wavelets/Examples/Daubechies/Bernstein` |
| Besov spaces by Daubechies coefficients; D4 and order three | ✅ | ✗ | `Wavelets/Examples/Daubechies/Besov`, `Wavelets/Examples/Daubechies/D4Besov`, `Wavelets/Examples/Daubechies/OrderThree` |
| Tensor generators on `ℝ^d` and their moduli | ✅ | ✗ | `Wavelets/Examples/Daubechies/TensorWavelets` |
| Expansions on `ℝ^d`: windows and overlap, stability, coefficient recovery, Bernstein's inequality | ✅ | ✗ | `Wavelets/Examples/Daubechies/TensorExpansion` |
| The multiresolution analysis on `ℝ^d`: kernels, the block identity, the levels, scaling spaces, norms of the blocks, the inverse inequality | ✅ | ✗ | `Wavelets/Examples/Daubechies/TensorProjections` |
| Jackson's inequality in one coordinate | ✅ | ✗ | `Wavelets/Examples/Daubechies/SlicewiseProjections` |
| Jackson's inequality on `ℝ^d`: projections in all coordinates, their range, density of the scaling spaces | ✅ | ✗ | `Wavelets/Examples/Daubechies/TensorJackson` |
| Besov spaces on `ℝ^d` and on inner product spaces, and `H^s`, by tensor wavelet coefficients | ✅ | ✗ | `Wavelets/Examples/Daubechies/TensorBesov` |
| The tensor wavelet basis of `L_2(ℝ^d)`, `H^s` as a weighted `ℓ_2`, synthesis in `L_p`, `n`-term approximation | ✅ | ✗ | `Wavelets/Examples/Daubechies/TensorWaveletBasis` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
