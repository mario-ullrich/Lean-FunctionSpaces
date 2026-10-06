# Triebel–Lizorkin spaces

Part of [Function spaces via approximation](../README.md). Blueprint chapters:
*Triebel–Lizorkin spaces*.

Besov quasi-norms take the `L_p` norm of every Littlewood–Paley block `ψ_j ⋆ f` and then the
`ℓ_q` norm over the levels; the Triebel–Lizorkin quasi-norm
`‖ (∑_j 2^(jsq) |ψ_j ⋆ f|^q)^(1/q) ‖_p` takes the `ℓ_q` norm at every point first. This block
develops the spaces `F^s_{p,q}` on `ℝ^d` and on the torus `𝕋^d` with the blocks of
[Function spaces on `ℝ^d`](Rd.md). Its first part compares the two mixed norms `L_p(ℓ_q)` and
`ℓ_q(L_p)` on every measure space; the rows marked ⬜ in the table below are the planned files
of the block.

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
* **Triebel–Lizorkin spaces and the Besov sandwich on `ℝ^d`.** Let `V` be a finite-dimensional
  real inner product space, such as `ℝ^d`, `1 ≤ p < ∞`, `s ∈ ℝ`, `1 ≤ q ≤ ∞`, and `ψ_j` the
  Littlewood–Paley kernels of [Function spaces on `ℝ^d`](Rd.md). For `f ∈ L_p(V)` the
  Triebel–Lizorkin quasi-norm is `‖f‖_{F^s_{p,q}} = ‖ x ↦ ‖(2^(js) |ψ_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p`
  (`Rd.triebelLizorkinNorm`), and `F^s_{p,q}` consists of the `f` with `‖f‖_{F^s_{p,q}} < ∞`
  (`Rd.MemTriebelLizorkin`, a subspace of `L_p`: `Rd.triebelLizorkinSpace`). Then
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
* **The Fefferman–Stein inequality.** Let `V` be a finite-dimensional real inner product space,
  such as `ℝ^d`, and `M` the Hardy–Littlewood maximal operator. For `1 < p < ∞`, `1 < q ≤ ∞` and
  almost everywhere measurable `g_j : V → [0, ∞]`, `j ∈ ℕ`,
  `‖ x ↦ ‖(M g_j(x))_j‖_{ℓ_q} ‖_p ≤ C ‖ x ↦ ‖(g_j(x))_j‖_{ℓ_q} ‖_p` with the explicit constant
  `C = Rd.feffermanSteinConst V p q` (`Rd.feffermanStein`). The case `p < q` rests on a
  vector-valued weak type `(1,1)` (`Rd.volume_lqNorm_maximal_gt_le`), proved with the
  Calderón–Zygmund decomposition on dyadic cubes.
* **Local means.** Let `k_j` be the local means kernels of order `L` of a bump `g`
  ([Function spaces on `ℝ^d`](Rd.md)) and
  `‖f‖^{g,L}_{F^s_{p,q}} = ‖ x ↦ ‖(2^(js) |k_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p`
  (`Rd.LocalMeansBump.tlLocalMeansNorm`). For `1 < p < ∞`, `1 < q ≤ ∞` and `f ∈ L_p(V)`,
  `‖f‖^{g,L}_{F^s_{p,q}} ≤ D ‖f‖_{F^s_{p,q}}` and, for `L ≥ 1`,
  `‖f‖_{F^s_{p,q}} ≤ U ‖f‖^{g,L}_{F^s_{p,q}}`, with explicit constants `D`, `U` that are
  finite for `0 < s < L` (`Rd.LocalMeansBump.tlLocalMeansNorm_le_triebelLizorkinNorm`,
  `Rd.LocalMeansBump.triebelLizorkinNorm_le_tlLocalMeansNorm`). Hence for `L ≥ 1` and
  `0 < s < L`, `f ∈ F^s_{p,q}` iff `‖f‖^{g,L}_{F^s_{p,q}} < ∞`
  (`Rd.LocalMeansBump.memTriebelLizorkin_iff_tlLocalMeans`), for every bump and every such
  order (`Rd.LocalMeansBump.tlLocalMeansNorm_lt_top_iff`). The proof bounds blocks and local
  means by maximal functions of each other at every point and applies the Fefferman–Stein
  inequality.
* **Local means on the torus.** For a bump `g` on `ℝ^d` with local means kernels `k_j` of order
  `L`, acting on the torus by `k_j ⋆ f(t) = ∫ k_j(y) f(t - π y) dy`, the quasi-norm
  `‖f‖^{g,L}_{F^s_{p,q}(𝕋^d)} = ‖ t ↦ ‖(2^(js) |k_j ⋆ f(t)|)_j‖_{ℓ_q} ‖_p`
  (`Torus.tlLocalMeansNorm`) satisfies the same two bounds with explicit constants
  (`Torus.tlLocalMeansNorm_le_triebelLizorkinNorm`,
  `Torus.triebelLizorkinNorm_le_tlLocalMeansNorm`), so for `1 < p < ∞`, `1 < q ≤ ∞`, `L ≥ 1`
  and `0 < s < L`, `f ∈ F^s_{p,q}(𝕋^d)` iff `‖f‖^{g,L}_{F^s_{p,q}(𝕋^d)} < ∞`
  (`Torus.memTriebelLizorkin_iff_tlLocalMeans`). The pointwise bounds of `ℝ^d` apply to the
  periodic lifts `h ∘ π`, and the Fefferman–Stein inequality holds for the maximal functions of
  lifts on the period box `(0, 1]^d`, with the constant `Torus.periodicFSConst d p q`
  (`Torus.feffermanStein_periodic`).

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Mixed norms `L_p(ℓ_q)` and `ℓ_q(L_p)`: Minkowski's inequalities for series and for `ℓ_u`-valued functions, comparison, limits of pointwise bounds | ✅ | ✗ | `Lp/MixedNorms` |
| Triebel–Lizorkin spaces on `ℝ^d`: definition, `F_{p,p} = B_{p,p}`, the Besov sandwich | ✅ | ✗ | `Rd/TriebelLizorkin` |
| Dyadic cubes of every level, Lebesgue differentiation along them | ✅ | ✗ | `Rd/DyadicCubes` |
| Hardy–Littlewood maximal function: weighted weak and strong types | ✅ | ✗ | `Rd/MaximalFunction` |
| The Calderón–Zygmund decomposition on dyadic cubes | ✅ | ✗ | `Rd/CalderonZygmund` |
| The Fefferman–Stein inequality | ✅ | ✗ | `Rd/FeffermanStein` |
| Peetre majorants of cross kernels, maximal function bounds | ✅ | ✗ | `Rd/KernelMajorants` |
| Local means characterisation of Triebel–Lizorkin spaces | ✅ | ✗ | `Rd/TriebelLizorkinLocalMeans` |
| Ball means of differences | ⬜ | ✗ | `Rd/TriebelLizorkinDifferences` |
| Atomic characterisation | ⬜ | ✗ | `Rd/TriebelLizorkinAtoms` |
| Triebel–Lizorkin spaces on the torus, the Besov sandwich | ✅ | ✗ | `Torus/TriebelLizorkin` |
| The periodic lift: period boxes, lifted null sets, counting boxes | ✅ | ✗ | `Torus/PeriodicLift` |
| The Fefferman–Stein inequality for periodic lifts | ✅ | ✗ | `Torus/FeffermanStein` |
| Local means characterisation on the torus | ✅ | ✗ | `Torus/TriebelLizorkinLocalMeans` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
