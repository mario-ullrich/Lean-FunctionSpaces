# Daubechies wavelets

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Besov spaces*,
chapter *Daubechies wavelets*.

The compactly supported orthonormal wavelets of Daubechies on `ℝ`, built from the filter up, and
the description of `B^s_{p,q}(ℝ)` by their coefficients. A mask of order `N` comes from the
Fejér–Riesz theorem, the scaling function is the inverse Fourier transform of the infinite
product of its symbol, and everything about it is proved with the Fourier transform of
integrable functions: the refinement equation, the compact support through the cascade
algorithm, the orthonormality of the translates and the reproduction of polynomials. The
transfer operator of Eirola and Villemoes gives the Sobolev regularity, the matrix method of
Daubechies and Lagarias the Hölder exponent of D4. The projections onto the spaces `V_j` form a
projection scheme in the sense of [Approximation spaces](ApproximationSpaces.md); Jackson's and
Bernstein's inequalities identify its approximation spaces with the Besov spaces of
[Besov spaces on `ℝ^d`](Rd.md), as for the Haar system and the multiwavelets of
[Intervals, the cube, splines and wavelets](IntervalCube.md).

## Main results

* **Masks of every order.** A mask of order `N` is a real polynomial `L` of degree `< N` with
  `L(1) = 1` and `|L(e^(-2πiξ))|² = P_N(sin²(πξ))`, where `P_N(y) = ∑_{k<N} C(N-1+k, k) y^k`
  (`Daubechies.Mask`, `Daubechies.daubPoly`); its filter coefficients `c_k` are those of
  `2 ((1 + z)/2)^N L(z)` (`Daubechies.coeff`). Masks of order `N` exist iff `N ≥ 1`
  (`Daubechies.nonempty_mask_iff`), by the Fejér–Riesz theorem: a real polynomial `Q` with
  `Q > 0` on `[-1, 1]` satisfies `Q(cos θ) = |L(e^(iθ))|²` for all `θ` with a real polynomial `L`
  of degree `≤ deg Q` and `L(1) > 0` (`Polynomial.fejer_riesz`). For `N = 2` the mask whose
  polynomial `L` has no zeros in the closed unit disk is D4, with
  `c = ((1+√3), (3+√3), (3-√3), (1-√3))/4` (`Daubechies.eq_d4_iff_aeval_ne_zero`,
  `Daubechies.coeff_d4`).
* **The scaling function.** Let `N ≥ 2`, `m_0(ξ) = (1/2) ∑_k c_k e^(-2πikξ)` and
  `Φ(ξ) = ∏_{j ≥ 1} m_0(2^(-j) ξ)`. Then `Φ` is integrable, and `φ = 𝓕⁻¹ Φ` is a continuous real
  function with `φ(x) = ∑_k c_k φ(2x - k)` (`Daubechies.scalingFun_refine`), `φ = 0` outside
  `[0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`), `∫ φ = 1` (`Daubechies.integral_scalingFun`)
  and `∫ φ(x - k) conj φ(x - l) dx = δ_{kl}` for `k, l ∈ ℤ`
  (`Daubechies.integral_scalingFun_translate_mul_conj_translate`). Every polynomial `Q` of
  degree `< N` satisfies `∑_k ⟨Q, φ(· - k)⟩ φ(x - k) = Q(x)` for all `x`
  (`Daubechies.sum_inner_poly_mul_scalingFun`).
* **Sobolev regularity.** Let `T g(ξ) = P(ξ/2) g(ξ/2) + P((ξ+1)/2) g((ξ+1)/2)` with
  `P(ξ) = P_N(sin²(πξ))` (`Daubechies.transfer`). If `T^n 1 ≤ C λ^n` for all `n` (the
  hypothesis `Daubechies.TransferGrowth`), then `∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ < ∞` for every
  `s < N - log₄ λ` (`Daubechies.integrable_rpow_mul_normSq`), and for `p ≤ 2`, `0 ≤ s ≤ r` and
  `0 < t ≤ 1`, `ω_r(φ, t)_p ≤ K t^s` (`Daubechies.modulus_scalingFun_le_two`). For `N = 2`,
  `T 1 = 4`, and for `N = 3`, `T^n 1 ≤ 2 · 9^n` (`Daubechies.transferGrowth_two`,
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
  (`Daubechies.besov_iff_coeff`, `Daubechies.coeffNorm`), and the same holds for the
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

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
