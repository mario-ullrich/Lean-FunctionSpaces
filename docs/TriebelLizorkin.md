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

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| Mixed norms `L_p(ℓ_q)` and `ℓ_q(L_p)`: Minkowski's inequalities for series and for `ℓ_u`-valued functions, comparison, limits of pointwise bounds | ✅ | ✗ | `Lp/MixedNorms` |
| Triebel–Lizorkin spaces on `ℝ^d`: definition, `F_{p,p} = B_{p,p}`, the Besov sandwich | ⬜ | ✗ | `Rd/TriebelLizorkin` |
| Dyadic cubes of every level, the Lebesgue differentiation theorem along them | ⬜ | ✗ | `Rd/DyadicCubes` |
| The Hardy–Littlewood maximal function, weighted weak and strong types | ⬜ | ✗ | `Rd/MaximalFunction` |
| The Calderón–Zygmund decomposition | ⬜ | ✗ | `Rd/CalderonZygmund` |
| The Fefferman–Stein inequality | ⬜ | ✗ | `Rd/FeffermanStein` |
| Kernel majorants and maximal function bounds of convolutions | ⬜ | ✗ | `Rd/KernelMajorants` |
| Local means characterisation of Triebel–Lizorkin spaces | ⬜ | ✗ | `Rd/TriebelLizorkinLocalMeans` |
| Ball means of differences | ⬜ | ✗ | `Rd/TriebelLizorkinDifferences` |
| Atomic characterisation | ⬜ | ✗ | `Rd/TriebelLizorkinAtoms` |
| Triebel–Lizorkin spaces on the torus, the Besov sandwich | ⬜ | ✗ | `Torus/TriebelLizorkin` |
| The periodic lift of functions on the torus | ⬜ | ✗ | `Torus/PeriodicLift` |
| The Fefferman–Stein inequality for periodic lifts | ⬜ | ✗ | `Torus/FeffermanStein` |
| Local means on the torus | ⬜ | ✗ | `Torus/TriebelLizorkinLocalMeans` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
