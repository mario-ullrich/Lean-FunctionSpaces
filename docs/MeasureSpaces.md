# Besov and Sobolev spaces on measure spaces

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Approximation
spaces*, chapters *Besov spaces and their embeddings*, *Sobolev spaces and their embeddings* and
*Spectral schemes*; part *Besov spaces*, the opening of chapter *Filtrations and martingale
differences*.

For a finite measure space `(Ω, μ)` and a scheme `S` of bounded continuous functions, the
Besov space is `B^s_{p,q}(Ω, S) = A^s_q(L_p(μ), S)`, and the embedding theorems follow from the
Nikolskii transfer theorem of [Approximation spaces](ApproximationSpaces.md) together with a
Nikolskii inequality for the scheme. Spectral schemes in a Hilbert space give the Sobolev spaces
`H^s` with Jackson and Bernstein constants `1`, and their dyadic Fourier blocks characterise
`A^s_q` (`SpectralScheme.memApprox_iff_blockNorm_lt_top`). A compact dense embedding
`J : V → H` of Hilbert spaces gives such a scheme, from the eigenvectors of `J J†`
(`CompactDenseEmbedding.spectralScheme`). Orthonormal bases of continuous functions with
levels (continuous spectral bases), modelled on the eigenfunctions of the
Laplacian on a compact manifold, enter as a hypothesis. The torus is the first instance
([The torus](Torus.md)). A filtration gives a projection scheme, whose approximation spaces are
described by martingale differences. The `L_p` tools are in [Tools from analysis](Analysis.md).

## Main results

* **Besov embeddings.** Let `μ` be a finite measure on `Ω` and `S` a scheme of bounded continuous
  functions with the Nikolskii property of dimension `D ≥ 0`: for every `1 ≤ p ≤ ∞` there is `C`
  with `‖a‖_∞ ≤ C n^(D/p) ‖a‖_p` for all `a ∈ S_n`, `n ≥ 1` (the hypothesis
  `FunctionScheme.HasNikolskii`, proved on the torus, `Torus.trigScheme_hasNikolskii`). Let
  `1 ≤ p ≤ r ≤ ∞`, `1 ≤ q ≤ ∞` and `α = D (1/p - 1/r) < s`. Then every `f ∈ B^s_{p,q}` belongs to
  `L_r` and to `B^{s-α}_{r,q}`, with `‖f‖_{B^{s-α}_{r,q}} ≤ K ‖f‖_{B^s_{p,q}}`
  (`FunctionScheme.MemBesov.exists_inclusion_eq_of_nikolskii`,
  `FunctionScheme.exists_inclusion_eq_of_nikolskii`). If `μ` charges every nonempty open set and
  `s > D/p`, every `f ∈ B^s_{p,q}` has a bounded continuous representative
  (`FunctionScheme.MemBesov.exists_boundedContinuous`).
* **Besov spaces interpolate.** For every scheme of functions `S`, `1 ≤ p ≤ ∞`, `0 < η < 1` and
  `1 ≤ q₀, q₁, q ≤ ∞`, the real interpolation spaces of the continuous K-method of the couples
  of dyadic quasi-norms are `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{η,q} = B^{(1-η)s₀+ηs₁}_{p,q}` for
  `0 < s₀ < s₁` and `(L_p, B^{s₁}_{p,q₁})_{η,q} = B^{ηs₁}_{p,q}` for `s₁ > 0`
  (`FunctionScheme.memKMethod_besovCouple_iff`, `FunctionScheme.memKMethod_lpBesovCouple_iff`),
  by the reiteration theorem for approximation spaces of
  [Approximation spaces](ApproximationSpaces.md). The couples of Pietsch's quasi-norms
  `FunctionScheme.besovNorm` have the same interpolation spaces
  (`FunctionScheme.memKMethod_besovNormCouple_iff`,
  `FunctionScheme.memKMethod_lpBesovNormCouple_iff`).
* **Sobolev embeddings.** Call a Banach space `V` with an injective bounded map into `L_p(μ)` a
  Sobolev space of order `s` for `S` (the hypothesis structure `FunctionScheme.SobolevSpace`) if it
  satisfies Jackson's inequality `E_n(f)_p ≤ C n^(-s) ‖f‖_V` and Bernstein's inequality (every
  `a ∈ S_n` lies in `V` with `‖a‖_V ≤ C n^s ‖a‖_p`). For `S` with the Nikolskii property of
  dimension `D ≥ 0`, Sobolev spaces `V` of order `s` in `L_p` and `V'` of order `t` in `L_r`,
  `p ≤ r` and `t - D/r < s - D/p`, every element of `V` lies in `V'`
  (`FunctionScheme.SobolevSpace.exists_eq_inclusion'`); for `s > D/p` every element of `V` has a
  bounded continuous representative (`FunctionScheme.SobolevSpace.exists_boundedContinuous`). The
  instances of the structure are the spaces `H^s`, `p = 2`, on the torus and for a continuous
  spectral basis (`Torus.sobolevSpace`, `ContinuousSpectralBasis.sobolevSpace`). The limiting cases
  are not covered.
* **Spaces with a continuous spectral basis.** Let `μ` be a finite Borel measure on a
  topological space `M`, and `(e_i)` an orthonormal basis of `L_2(μ)` of bounded continuous
  functions with levels `λ(i) ∈ ℕ`, finitely many of each level (`ContinuousSpectralBasis`). The
  model is the eigenbasis of the Laplacian on a compact Riemannian manifold with
  `λ(i) = ⌊√λ_i⌋`; the structure consists of the basis, its levels and its continuous
  representatives, and the torus is an instance (`Torus.fourierEigenbasis`). For the scheme of
  the spans of `{e_i : λ(i) < n}` and `s > 0`, `f ∈ B^s_{2,2}` iff
  `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞` (`ContinuousSpectralBasis.memBesov_two_two_iff`). If
  moreover `∑_{λ(i) < n} |e_i(x)|² ≤ C n^D` for all `x` and `n ≥ 1` (the local Weyl bound, the
  hypothesis `ContinuousSpectralBasis.LocalWeylBound`, proved on the torus), then
  `‖a‖_∞^p ≤ C n^D ‖a‖_p^p` for `1 ≤ p ≤ 2` and `a` in the span of level `< n`
  (`ContinuousSpectralBasis.norm_rpow_le_of_localWeyl`), and for `2s > D` every such `f` has a
  bounded continuous representative (`ContinuousSpectralBasis.exists_continuous_of_localWeyl`).
* **Martingale differences.** For a filtration `ℱ_0 ≤ ℱ_1 ≤ ⋯` on a finite measure space,
  let `A_n ⊆ L_p` be the `ℱ_⌊log₂ n⌋`-measurable functions (for the dyadic filtration of
  `[0, 1)`, the step functions of the Haar system). If these are dense in `L_p`, then for
  `s > 0`, `f ∈ A^s_q` iff
  `‖E[f | ℱ_0]‖_p + ‖(2^(ks) ‖E[f | ℱ_{k+1}] - E[f | ℱ_k]‖_p)_k‖_{ℓ_q} < ∞`
  (`MeasureTheory.Filtration.memApprox_iff_martingale`), using the conditional expectation
  as a contraction of `L_p` (`MeasureTheory.Lp.condExpLp`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Schemes of functions, Besov spaces, elementary embeddings | ✅ | ✗ | `MeasureSpaces/Scheme`, `MeasureSpaces/Besov/Basic`, `MeasureSpaces/Besov/ElementaryEmbeddings` |
| Nikolskii property, the sign of the Nikolskii exponent, Besov embeddings | ✅ | ✗ | `MeasureSpaces/Besov/Nikolskii`, `MeasureSpaces/Besov/Embeddings` |
| Besov spaces as interpolation spaces | ✅ | ✗ | `MeasureSpaces/Besov/Interpolation` |
| Sobolev spaces as a hypothesis structure, Sobolev embeddings | ✅ | ✗ | `MeasureSpaces/Sobolev/Embeddings` |
| Spectral schemes and `L_2` Sobolev spaces, Jackson and Bernstein | ✅ | ✗ | `MeasureSpaces/Spectral/Basic` |
| Coefficient characterisations of spectral schemes, `H^s = B^s_{2,2}` | ✅ | ✗ | `MeasureSpaces/Spectral/Blocks` |
| Hilbert bases of eigenvectors of compact self-adjoint operators, and the polarization of a norm identity | ✅ | ✗ | `MeasureSpaces/Spectral/CompactEigenbasis` |
| Compact dense embeddings: singular basis, spectral scheme, Jackson and Bernstein, `(H, J(V))_{θ,q} = A^θ_q` | ✅ | ✗ | `MeasureSpaces/Spectral/CompactEmbedding` |
| Continuous spectral bases (hypothesis), `B^s_{2,2} = H^s`, local Weyl bound, Nikolskii for `p ≤ 2`, continuity of `H^s` for `s > D/2` | ✅ | ✗ | `MeasureSpaces/Spectral/ContinuousSpectralBasis`, `MeasureSpaces/Spectral/LocalWeyl` |
| Conditional expectations on `L_p`, filtration schemes (Haar), martingale-difference characterisation | ✅ | ✗ | `MeasureSpaces/Martingales/Filtration` |
| The conditional expectation onto a countable partition as the average over the cells | ✅ | ✗ | `MeasureSpaces/Martingales/Partition` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
