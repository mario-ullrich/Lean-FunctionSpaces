# Function spaces via approximation in Lean 4 / Mathlib

A Lean 4 / Mathlib formalisation of **approximation spaces** in the sense of Pietsch, and of
**Besov and Sobolev spaces** defined through them, with their **embedding theorems**. An
approximation scheme is an increasing family of sets `A₀ ⊆ A₁ ⊆ ⋯` in a normed space, and a
function belongs to the approximation space `A^s_q` when its errors of best approximation
`E_n(f) = dist(f, A_n)` decay like `n^(-s)` in the `ℓ_q` sense. Besov spaces on a general
finite measure space are the approximation spaces of `L_p` for a scheme of bounded
continuous functions, and the embedding theorems follow from the abstract theory together
with a Nikolskii inequality for the scheme. The torus is the first concrete instance. The
project is work in progress; the table below lists what is formalised.

* **Blueprint** (a webpage explaining the mathematics):
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/>
* **Blueprint as PDF**:
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/blueprint.pdf>
* **Dependency graph**:
  <https://mario-ullrich.github.io/Lean-FunctionSpaces/dep_graph_document.html>

## The setting

Let `X` be a real normed space. An **approximation scheme** is a sequence of subsets
`A₀ ⊆ A₁ ⊆ A₂ ⊆ ⋯` of `X` with `A₀ = {0}`, `c · a ∈ A_n` for real `c` and `a ∈ A_n`, and
`A_m + A_n ⊆ A_{m+n}`. The sets need not be subspaces: for `n`-term approximation from a
dictionary `D`, `A_n` is the set of linear combinations of at most `n` elements of `D`.
The **error of best approximation** of `f ∈ X` is `E_n(f) = inf { ‖f - a‖ : a ∈ A_n }`.

For `s > 0` and `1 ≤ q ≤ ∞`, the **approximation space** `A^s_q` consists of those `f` with

```
‖f‖_{A^s_q} = ‖ (n^(s - 1/q) E_{n-1}(f))_{n ≥ 1} ‖_{ℓ_q}  <  ∞ .
```

For a finite measure space `(Ω, μ)` and a scheme `S` of bounded continuous functions on `Ω`,
the **Besov space** is `B^s_{p,q}(Ω, S) = A^s_q(L_p(μ), S)`: the functions whose best
approximation from `S` in `L_p` decays at rate `s`. On the torus `𝕋^d` with `S_n` the
trigonometric polynomials of degree `< n`, these are the classical periodic Besov spaces.

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
  (`ApproximationScheme.approxNormDyadic_le_of_lt`).
* **Functoriality.** A bounded linear map `T : X → Y` with `T(A_n) ⊆ B_n` satisfies
  `E^B_n(T f) ≤ ‖T‖ E^A_n(f)` and `‖T f‖_{B^s_q} ≤ ‖T‖ ‖f‖_{A^s_q}`
  (`ApproximationScheme.approxError_map_le`, `.approxNorm_map_le`).
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

| Result | Lean | Human-checked | File |
|---|---|---|---|
| Approximation schemes, preimage and image | ✅ proved | ✗ | `ApproximationSpaces/Scheme.lean` |
| Error of best approximation and its calculus | ✅ proved | ✗ | `ApproximationSpaces/Error.lean` |
| Linear approximation from a sequence | ✅ proved | ✗ | `ApproximationSpaces/Instances/Span.lean` |
| `n`-term approximation from a dictionary | ✅ proved | ✗ | `ApproximationSpaces/Instances/NTerm.lean` |
| `ℓ_q` norms of sequences in `ℝ≥0∞`, Minkowski, monotonicity in `q` | ✅ proved | ✗ | `ApproximationSpaces/Sequences/Lq.lean` |
| Cauchy condensation with power weights | ✅ proved | ✗ | `ApproximationSpaces/Sequences/Dyadic.lean` |
| Countable Minkowski inequality, discrete Hardy inequalities | ✅ proved | ✗ | `ApproximationSpaces/Sequences/Hardy.lean` |
| `A^s_q`, its dyadic quasi-norm and linear structure | ✅ proved | ✗ | `ApproximationSpaces/{Norm,Dyadic,Space}.lean` |
| Embeddings `A^s_q ↪ A^t_r` and functoriality | ✅ proved | ✗ | `ApproximationSpaces/{Embedding,Transfer}.lean` |
| Nikolskii transfer theorem | ⬜ planned | ✗ | `ApproximationSpaces/{Lift,Nikolskii}.lean` |
| K-functional, real interpolation, representation theorem | ⬜ planned | ✗ | `ApproximationSpaces/{KFunctional,Interpolation,Representation}.lean` |
| Atomic decompositions, projection schemes | ⬜ planned | ✗ | `ApproximationSpaces/{Decomposition,Projection}.lean` |
| Inclusion `L_r ↪ L_p`, schemes of functions, Besov spaces | ⬜ planned | ✗ | `FunctionSpaces/{Lp,Scheme,Besov}/…` |
| Besov embeddings from a Nikolskii inequality | ⬜ planned | ✗ | `FunctionSpaces/Besov/Embeddings.lean` |
| Smoothness spaces and Sobolev embeddings | ⬜ planned | ✗ | `FunctionSpaces/Smoothness/…` |
| Spectral schemes and `L_2` Sobolev spaces | ⬜ planned | ✗ | `FunctionSpaces/Spectral/…` |
| The torus: Nikolskii inequality, `W^s_2(𝕋^d) ↪ C(𝕋^d)` | ⬜ planned | ✗ | `FunctionSpaces/Torus/…` |
| Haar wavelets | ⬜ planned | ✗ | `FunctionSpaces/Atoms/Haar.lean` |
| Classical definitions by derivatives and differences, coincidence | ⬜ planned | ✗ | `FunctionSpaces/Classical/…` |

Lean: ✅ proved (no `sorry`) · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author ·
🧮 mathematics reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a
file resets its rows to ✗.

## Organisation

Two libraries. `ApproximationSpaces` holds the abstract theory: approximation schemes in a
real normed space, the error of best approximation, and the two basic schemes, linear
approximation from a sequence and `n`-term approximation from a dictionary. Nothing in it
mentions functions or measures. `FunctionSpaces` will hold the Besov and Sobolev spaces built
on it. [MathlibCandidates.md](MathlibCandidates.md) lists what could be upstreamed.
`blueprint/` holds the LaTeX source of the blueprint and the scripts that check and link its
`\lean` references.

## What is left to do

* **Real interpolation**: the representation theorem `A^s_q = (X, Y)_{s/r, q}` under Jackson
  and Bernstein inequalities, and reiteration.
* **Function spaces beyond the torus**: `ℝ^d`, compact manifolds, bounded domains.
* **Classical definitions**: Sobolev spaces by weak derivatives and Besov spaces by moduli
  of smoothness for all `p`, with the coincidence theorems of Triebel's school.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib in `lake-manifest.json`, so a clone builds against Lean /
Mathlib `v4.35.0-rc2`:

```bash
lake exe cache get   # downloads the prebuilt Mathlib oleans
lake build           # builds the project
```

Run `lake` from inside this folder, since `elan` reads `lean-toolchain` from the
working directory, and do not run `lake update`: it re-resolves the dependencies and
makes the build non-reproducible.

The blueprint follows the
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) convention and needs a
TeX installation, `graphviz` for the dependency graph, and the `leanblueprint` package:

```bash
leanblueprint pdf          # blueprint/print/print.pdf
leanblueprint web          # blueprint/web/index.html and the dependency graph
python blueprint/scripts/check_lean_decls.py   # checks that every \lean{Decl} resolves
```

GitHub Actions builds the project and the blueprint on every push to `main`, and deploys
the blueprint to GitHub Pages. Neither output is committed.

## AI assistance

The formalisation was written with Claude Code. Every statement and proof was checked
by Lean; the mathematical design, the choice of statements and the review of what the
proofs actually say are the author's. The column "Human-checked" above records that review.

## License

Apache 2.0, the same as Mathlib. See [LICENSE](LICENSE).

## References

* J. Bergh, J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren der
  mathematischen Wissenschaften **223**, Springer-Verlag, 1976. Real interpolation and the
  K-functional.
* R. A. DeVore, G. G. Lorentz, *Constructive Approximation*, Grundlehren der
  mathematischen Wissenschaften **303**, Springer-Verlag, 1993. Chapter 7: approximation
  spaces, Jackson and Bernstein inequalities, and their relation to interpolation.
* S. M. Nikol'skii, *Approximation of Functions of Several Variables and Imbedding
  Theorems*, Grundlehren der mathematischen Wissenschaften **205**, Springer-Verlag, 1975.
  The Nikolskii inequality and the embedding theorems it yields.
* A. Pietsch, *Approximation spaces*, J. Approx. Theory **32** (1981), no. 2, 115–134.
  The definition of approximation schemes and spaces followed here.
* V. Temlyakov, *Multivariate Approximation*, Cambridge University Press, 2018. Periodic
  function spaces and trigonometric approximation.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983. Besov and Sobolev spaces and
  the equivalence of their definitions.
