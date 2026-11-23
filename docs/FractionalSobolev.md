# Fractional Sobolev spaces on Lipschitz domains

Part of [Characterizations of Function Spaces](../README.md). Blueprint: part *Domains, traces and
manifolds*, chapter *Fractional Sobolev spaces on Lipschitz domains*.

The Sobolev spaces of an open set `Ω ⊆ V` are built inside Mathlib's `H^s(ℝ^d)` for every real `s`
([Lipschitz domains and traces](DomainsTraces.md)): `H^s(Ω)` is the space of restrictions,
`H̃^s(Ω)` the closure of the test functions of `Ω` in `H^s(ℝ^d)`, and `H^s_0(Ω)` the closure of
their restrictions in `H^s(Ω)`. This block compares `H̃^s(Ω)` with `H^s_0(Ω)`, following Hewett and
Moiola. The inclusions `H^s(ℝ^d) ⊆ H^t(ℝ^d)`, `t ≤ s`, of [Sobolev spaces on `ℝ^d`](SobolevRd.md)
keep test functions and vanishing on `Ω`, so they give bounded injective inclusions
`H^s(Ω) ⊆ H^t(Ω)` with dense range that map `H^s_0(Ω)` into `H^t_0(Ω)`. Restriction maps
`H̃^s(Ω)` into `H^s_0(Ω)`; it is an isomorphism as soon as the zero extension bound
`‖U‖ ≤ C ‖U + W‖` holds for the test functions `U` of `Ω` and the `W` that vanish on `Ω`, and then
`‖U‖ ≤ C ‖U|_Ω‖` on `H̃^s(Ω)`. The derivatives `H^{s+1}(ℝ^d) → H^s(ℝ^d)` keep test functions and
vanishing on `Ω`, and the exact recursion of the norms carries the bound from `s` to `s + 1` with
the same constant. At `s = 0` the bound holds with
`C = 1` on every open set, since the `L_2` functions of `U` and `W` have disjoint supports; hence
restriction is an isometry of `H̃^m(Ω)` onto `H^m_0(Ω)` for every open `Ω` and every `m ∈ ℕ`. For
`s ≥ 0` the `L_2` functions of `H̃^s(Ω)` vanish outside `Ω`, so restriction is injective on
`H̃^s(Ω)` for every open `Ω`. On a bounded Lipschitz domain, conversely, every element of
`H^s(ℝ^d)`, `s ≥ 0`, whose `L_2` function vanishes outside `Ω` lies in `H̃^s(Ω)`: mollification
converges in `H^s(ℝ^d)` and smooth cut-offs keep `H^s(ℝ^d)` ([Sobolev spaces on
`ℝ^d`](SobolevRd.md)), and the cone mollifiers of the charts push such an element into
`H̃^s(Ω)`. The indicator `1_Ω` of a bounded Lipschitz domain is a pointwise multiplier of
`B^s_{p,q}(ℝ^d)` for `0 < s < 1/p`: the steps `h` that cross the boundary start in a layer of
width `≲ ‖h‖` along it, so `1_Ω` turns smooth atoms into atoms of smoothness `1/p`. At
`p = q = 2` this gives the zero extension bound and `H̃^s(Ω) = H^s_0(Ω) = H^s(Ω)` for
`0 ≤ s < 1/2`. For `1/2 < s < 1` a Hardy inequality takes its place: a function that vanishes
near the boundary of a Lipschitz graph domain, divided by the `s`-th power of its height above
the graph, is controlled by its first differences in the domain, through a dyadic Hardy
inequality on the vertical lines. Extension by zero from a graph domain is then bounded on such
functions, with a constant independent of how close to the boundary they vanish, and the charts
of a bounded Lipschitz domain give the zero extension bound.

## Main results

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω ⊆ V` open, `N^s(Ω)` the elements of `H^s(V)` vanishing on `Ω` (`Rd.vanishOn`), `T^s(Ω)` the
span of the test functions of `Ω` in `H^s(V)` (`Rd.testSpan`), and `U ↦ U|_Ω` the restriction
(`Rd.restrictProj`).

* **Inclusions of restriction spaces.** For `t ≤ s`, the inclusion `ι_{t,s} : H^s(V) → H^t(V)`
  maps Schwartz and test functions to themselves (`Rd.sobolevInclusion_ofSchwartz`,
  `Rd.sobolevInclusion_ofTest`), has dense range (`Rd.denseRange_sobolevInclusion`), satisfies
  `ι_{t,s} W ∈ N^t(Ω)` iff `W ∈ N^s(Ω)` (`Rd.sobolevInclusion_mem_vanishOn_iff`), and maps
  `T^s(Ω)` into `T^t(Ω)` (`Rd.sobolevInclusion_mem_testSpan`). The inclusion
  `H^s(Ω) ⊆ H^t(Ω)`, `u ↦ (ι_{t,s} u)|_Ω` (`Rd.restrictionInclusion`), is injective, has norm
  at most `1`, satisfies `ι_{t,s}(U|_Ω) = (ι_{t,s} U)|_Ω` for `U ∈ H^s(V)`, has dense range, and
  maps `H^s_0(Ω)` into `H^t_0(Ω)` (`Rd.restrictionInclusion_injective`,
  `Rd.norm_restrictionInclusion_apply_le`, `Rd.restrictionInclusion_restrictProj`,
  `Rd.denseRange_restrictionInclusion`, `Rd.restrictionInclusion_mem_zeroBoundarySpace`).
* **Derivatives keep test functions and vanishing.** For every real `s` and `v ∈ V`, the
  derivative `∂_v : H^{s+1}(V) → H^s(V)` maps a test function `φ` of `Ω` to the test function
  `∂_v φ`, `T^{s+1}(Ω)` into `T^s(Ω)` and `N^{s+1}(Ω)` into `N^s(Ω)`
  (`Rd.sobolevLineDeriv_ofTest`, `Rd.sobolevLineDeriv_mem_testSpan`,
  `Rd.sobolevLineDeriv_mem_vanishOn`).
* **Injectivity for `s ≥ 0`.** For `s ≥ 0` and every `U ∈ H̃^s(Ω)`, the `L_2` function of `U`
  vanishes almost everywhere outside `Ω` (`Rd.sobolevToL2_ae_eq_zero_of_mem_tildeSpace`), and
  `U|_Ω = 0` implies `U = 0` (`Rd.eq_zero_of_mem_tildeSpace_of_restrictProj_eq_zero`,
  `Rd.tildeToRestrictionL_injective`; Hewett–Moiola, Lemma 2.2(iii)).
* **`H̃^s(Ω)` by supports.** Let `s ≥ 0` and `ι_s U` be the `L_2` function of `U ∈ H^s(V)`. For
  a smooth `η` with compact support, `∫ η = 1` and dilates `η_c(x) = c^d η(c x)`: if `ι_s U`
  vanishes almost everywhere outside a compact set `S` and `supp η_{2^n} + S ⊆ Ω` for large `n`,
  then `U ∈ H̃^s(Ω)`
  (`Rd.mem_tildeSpace_of_dilate_of_nonneg`). If `Ω` is a bounded Lipschitz domain, `U ∈ H̃^s(Ω)`
  iff `ι_s U = 0` almost everywhere outside `Ω`
  (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff_of_nonneg`; McLean, Theorem 3.29;
  Chandler-Wilde–Hewett–Moiola, Lemma 3.15).
* **The zero extension bound.** `Ω` has the zero extension bound with constant `C` at `s` if
  `‖U‖ ≤ C ‖U + W‖` for every `U ∈ T^s(Ω)` and every `W ∈ N^s(Ω)`
  (`Rd.HasZeroExtensionBound`; Hewett–Moiola, condition (iv) after Lemma 2.9). Then
  `‖U‖ ≤ C ‖U|_Ω‖` for every `U ∈ H̃^s(Ω)`, and restriction is an isomorphism of `H̃^s(Ω)` onto
  `H^s_0(Ω)` with `‖U|_Ω‖ ≤ ‖U‖ ≤ C ‖U|_Ω‖`
  (`Rd.HasZeroExtensionBound.norm_le_norm_restrictProj`,
  `Rd.HasZeroExtensionBound.range_tildeToRestrictionL`,
  `Rd.HasZeroExtensionBound.tildeEquivZeroBoundary`), an isometry if `C = 1`
  (`Rd.HasZeroExtensionBound.norm_restrictProj_eq`). The bound at `s` gives the bound with the
  same constant at `s + 1` (`Rd.HasZeroExtensionBound.add_one`).
* **`H̃^m(Ω) ≅ H^m_0(Ω)` isometrically on every open set.** Every open `Ω` has the zero extension
  bound with constant `1` at every `m ∈ ℕ` (`Rd.hasZeroExtensionBound_zero`,
  `Rd.hasZeroExtensionBound_natCast`), and restriction is an isometric isomorphism of `H̃^m(Ω)`
  onto `H^m_0(Ω)` (`Rd.tildeEquivZeroBoundaryNat`; Hewett–Moiola, Lemma 2.2(iii);
  Chandler-Wilde–Hewett–Moiola, Lemma 3.31(vi)).
* **The indicator of a Lipschitz domain as a multiplier.** Let `Ω` be a bounded Lipschitz domain,
  `1 ≤ p < ∞` and `0 < s < 1/p`. There is `C < ∞` with
  `‖1_Ω F‖_p + ‖(2^(ks) ω_1(1_Ω F, 2^(-k))_p)_k‖_{ℓ_q}`
  `≤ C (‖F‖_p + ‖(2^(ks) ω_1(F, 2^(-k))_p)_k‖_{ℓ_q})` for every `1 ≤ q ≤ ∞` and every
  `F ∈ L_p(V)`
  (`Rd.BoundedLipschitzDomain.exists_modNorm_indicatorLp_le`; Triebel 2002, Proposition 5.3 and
  Remark 5.4; Schneider–Vybíral, Theorem 5.4(i) and Remark 5.10). The ingredients: the steps that
  cross the boundary form a layer, `|S_h(Ω) ∩ B̄(c, ρ)| ≤ C ‖h‖ ρ^(d-1)` for `ρ ≥ ‖h‖`
  (`Rd.BoundedLipschitzDomain.exists_volume_switchSet_inter_closedBall_le`), and `1_Ω a` is a
  regular atom of exponent `1/p` for every smooth atom `a` of order `1`
  (`Rd.BoundedLipschitzDomain.exists_isRegularAtom_indicator`).
* **`H̃^s(Ω) = H^s_0(Ω) = H^s(Ω)` for `0 ≤ s < 1/2`.** On a bounded Lipschitz domain the zero
  extension bound holds at every `0 ≤ s < 1/2`
  (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_lt_half`), every `U ∈ H^s(V)` has a
  zero extension `U' ∈ H̃^s(Ω)` with `ι_s U' = 1_Ω ι_s U` and `U'|_Ω = U|_Ω`
  (`Rd.BoundedLipschitzDomain.exists_sobolevToL2_eq_indicatorLp`,
  `Rd.BoundedLipschitzDomain.mem_tildeSpace_of_sobolevToL2_eq_indicatorLp`,
  `Rd.BoundedLipschitzDomain.restrictProj_eq_of_sobolevToL2_eq_indicatorLp`),
  `H^s_0(Ω) = H^s(Ω)` (`Rd.BoundedLipschitzDomain.zeroBoundarySpace_eq_top_of_lt_half`; Grisvard,
  Theorem 1.4.2.4; McLean, Theorem 3.40), and restriction is an isomorphism of `H̃^s(Ω)` onto
  `H^s(Ω)` (`Rd.BoundedLipschitzDomain.tildeEquivRestrictionSpaceOfLtHalf`; Hewett–Moiola,
  Lemma 2.1; Chandler-Wilde–Hewett–Moiola, Corollary 3.29(ix)).
* **A Hardy inequality and the zero extension bound for `1/2 < s < 1`.** For `s > 1/2` and a
  measurable `u : ℝ → ℂ` that vanishes almost everywhere on some `(0, ε)`,
  `∫_0^1 |u(t)|² t^(-2s) dt ≤ K_s ∫_0^1 ∫_0^1 |u(t) - u(τ)|² / |t - τ|^(1+2s) dτ dt` with
  `K_s = 2^(2s+2) (1 - 2^(-(s-1/2)))^(-2)` (`Rd.lintegral_div_rpow_le_halfLineForm`). Let `Ω'` be
  a Lipschitz graph domain with height `η` above its graph and
  `N_{s,Ω'}(G) = ‖G‖_{L_2(Ω')} + ‖(2^(ks) ω_1(G, 2^(-k), Ω')_2)_k‖_{ℓ_2}`. Every `G ∈ L_2(V)`
  that vanishes almost everywhere on `{x ∈ Ω' : η(x) < ε}` for some `ε > 0` satisfies
  `∫_{Ω'} |G|² / min(η, 1)^(2s) ≤ (1 + K_s 2^(2s+2)) N_{s,Ω'}(G)²`
  (`Rd.LipschitzGraph.lintegral_div_min_height_le_modNormOn`; for `1/2 < s < 1` a weaker,
  directional form of Dyda 2004, Theorem 1.1), and there is `C < ∞`, independent of `ε`, with
  `‖1_{Ω'} G‖_2 + ‖(2^(ks) ω_1(1_{Ω'} G, 2^(-k))_2)_k‖_{ℓ_2} ≤ C N_{s,Ω'}(G)`
  (`Rd.LipschitzGraph.exists_modNorm_indicatorLp_le_of_vanish`). On a bounded Lipschitz domain
  the zero extension bound holds at every `1/2 < s < 1`
  (`Rd.BoundedLipschitzDomain.exists_hasZeroExtensionBound_of_half_lt`; McLean, Theorem 3.33;
  Hewett–Moiola, Lemma 2.1), so restriction is an isomorphism of `H̃^s(Ω)` onto `H^s_0(Ω)`.

## What is formalised

Paths are relative to `FunctionSpaces/`, without `.lean`.

| Result | Lean | Human-checked | Files |
|---|---|---|---|
| The inclusions `H^s(ℝ^d) ⊆ H^t(ℝ^d)` on Schwartz and test functions, their dense range, the `L_2` functions of Schwartz functions, vanishing on `Ω` and the span of the test functions under the inclusions, the injective inclusion `H^s(Ω) ⊆ H^t(Ω)` with norm at most `1`, dense range and `H^s_0(Ω) ⊆ H^t_0(Ω)`, and derivatives that keep test functions and vanishing on `Ω` | ✅ | ✗ | `Domains/Sobolev/SobolevRestrictionInclusions` |
| The injectivity of restriction on `H̃^s(Ω)` for `s ≥ 0`, the zero extension bound, the isomorphism `H̃^s(Ω) ≅ H^s_0(Ω)` under it, its lift from `s` to `s + 1`, and the isometry `H̃^m(Ω) ≅ H^m_0(Ω)` for every open set and `m ∈ ℕ` | ✅ | ✗ | `Domains/Sobolev/ZeroExtensionBound` |
| Smoothing with compact support, cone mollifiers, mollified functions and functions with compact support in `Ω` as elements of `H̃^s(Ω)`, localised functions, the chart pieces, and `H̃^s(Ω)`, `s ≥ 0`, on a bounded Lipschitz domain as the functions of `H^s(ℝ^d)` that vanish outside `Ω` | ✅ | ✗ | `Domains/Sobolev/TildeSpaceSupport` |
| Switch sets of a step and crossing points on the boundary, the height above a Lipschitz graph, slabs along a graph, and the boundary layer `\|S_h(Ω) ∩ B̄(c, ρ)\| ≤ C ‖h‖ ρ^(d-1)` of a bounded Lipschitz domain, also at the scales of atoms | ✅ | ✗ | `Domains/Lipschitz/BoundaryLayers` |
| Differences of cut-off functions, indicators of smooth atoms as regular atoms of exponent `1/p`, and the indicator of a bounded Lipschitz domain as a pointwise multiplier of `B^s_{p,q}(ℝ^d)` for `0 < s < 1/p`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` | ✅ | ✗ | `Domains/Lipschitz/IndicatorMultiplier` |
| Restrictions determined by the `L_2` functions on `Ω`, the zero extension bound for `0 ≤ s < 1/2`, zero extensions in `H^s(ℝ^d)`, `H^s_0(Ω) = H^s(Ω)` and the isomorphism `H̃^s(Ω) ≅ H^s(Ω)` for `0 ≤ s < 1/2` | ✅ | ✗ | `Domains/Sobolev/SobolevZeroExtension` |
| Integrals over the line by dyadic shells, integrals in graph coordinates, vertical forms and vertical difference quotients, the Hardy inequality `∫_{Ω'} \|G\|² / min(η, 1)^(2s) ≤ (1 + K_s 2^(2s+2)) N_{s,Ω'}(G)²` on a Lipschitz graph domain for `s > 1/2` and `G` vanishing near the graph, differences of the extension by zero, and the extension by zero from a graph domain | ✅ | ✗ | `Domains/Lipschitz/GraphHardy` |
| The cut-off by the charts, extensions of test functions that vanish on `Ω` outside a compact set, localised functions that vanish near the graphs, and the zero extension bound for `1/2 < s < 1` on a bounded Lipschitz domain | ✅ | ✗ | `Domains/Sobolev/TildeZeroBoundaryEquiv` |

Lean: ✅ proved without `sorry` · 🟡 stated, proof still `sorry` · ⬜ planned, not yet stated.
Human-checked: ✅ mathematics and documentation both reviewed by the author · 🧮 mathematics
reviewed · 📝 documentation reviewed · ✗ not yet reviewed. A change to a file resets its row
to ✗.
