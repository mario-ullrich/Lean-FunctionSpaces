# Foundations for FEEC and BEEC

Part of [Characterizations of Function Spaces](../README.md). Block documents:
[Sobolev spaces on `ℝ^d`](SobolevRd.md) and [Domains, traces and manifolds](DomainsTraces.md).

This document is for the authors of the FEEC/BEEC library proposed in *FEEC and BEEC in Lean: a
proposed proof structure* (version 4, 10 October 2026). It lists what Lean-FunctionSpaces offers
that library, how to use it, and what comes next. Every result is proved in Lean without
`sorry`. The [blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/) states each result
with its proof and its Lean names, and each item below links to its place there.

Throughout, `V` is a finite-dimensional real inner product space of dimension `d`, standing for
`ℝ^d`, with Lebesgue measure. `Ω` is an open set or a bounded Lipschitz domain with boundary `Γ`.
`H^s(V)` is Mathlib's Hilbert space of tempered distributions `u` with
`(1 + |ξ|²)^{s/2} 𝓕u ∈ L_2`.

## 1. What can be used

### On `ℝ^d`

* **I.8: Mathlib's `H^s` is the Besov space `B^s_{2,2}`.**
  - For `s > 0`, a tempered distribution lies in `H^s(ℝ^d)` iff it is an `L_2` function in
    `B^s_{2,2}(ℝ^d)`.
  - For `s ≥ 0` it lies in `H^s(ℝ^d)` iff it is an `L_2` function in `F^s_{2,2}(ℝ^d)`.
  - With `J_s f = h` the norms satisfy `‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖h‖_2` and
    `‖h‖_2 ≤ (2 · 5^s)^{1/2} ‖f‖_{F^s_{2,2}}`.
  - So every description of `B^s_{2,2}` in the library applies to `H^s`: differences, local
    means, atoms and wavelets.
  - `Rd.memSobolev_two_iff_exists_memApprox`, `Rd.memSobolev_two_iff_memTriebelLizorkin`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-two-littlewood-paley.html#cor:sobolev-two-besov)).
* **Weak derivatives.**
  - `g` is the weak derivative `∂^v f` of `f` on an open set `Ω`, along directions
    `v_1, …, v_k`, if `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every test function `φ` of `Ω`. This is an
    equality in Mathlib's distributions `𝓓'(Ω)`.
  - `W^m_p(Ω)` consists of the `f ∈ L_p(Ω)` whose weak derivatives up to order `m` lie in
    `L_p(Ω)`.
  - On `ℝ^d` the weak derivative is the derivative of tempered distributions.
  - `Rd.HasWeakLineDeriv`, `Rd.MemWeakSobolev`, `Rd.hasWeakLineDeriv_top_iff`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-weak-derivatives.html#def:weak-line-derivative)).
* **`W^1_2 = H^1`.** For every orthonormal basis `(e_i)`, the norm identity is
  `(2π)² ‖J_1 f‖_2² = (2π)² ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²`.
  `Rd.memSobolev_one_iff`, `Rd.enorm_besselPotential_one_sq_eq`
  ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-two-littlewood-paley.html#thm:sobolev-one-two)).
* **All `1 < p < ∞`.**
  - `W^m_p = F^m_{p,2}`.
  - `H^{s,p} ∩ L_p = F^s_{p,2}` for every real `s`, hence `W^m_p = H^{m,p}` (Calderón).
  - Sobolev embeddings into `L_r` and into bounded continuous functions.
  - `Rd.memSobolev_iff_memTriebelLizorkin`, `Rd.memTriebelLizorkin_iff_memSobolev_bessel`,
    `Rd.memSobolev_iff_memSobolev_bessel`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-bessel-potential-lifting.html#cor:sobolev-bessel)).
* **Rellich on bounded sets.** For every bounded set `Ω ⊆ ℝ^d`, of any shape, the restriction
  `H^1(ℝ^d) → L_2(Ω)` is compact. `Rd.isCompactOperator_restr_toL2`
  ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-rellich-compactness.html#thm:rellich-compactness)).

### On open sets

All spaces below are Hilbert spaces: closed subspaces of `H^s(ℝ^d)` with its inner product.

* **The spaces of Chandler-Wilde, Hewett and Moiola.** For every open `Ω` and every real `s`:
  - `H^s(Ω)` is the orthogonal complement of the elements vanishing on `Ω`. It is isometric to
    the quotient of `H^s(ℝ^d)` by these elements, so its norm is the smallest norm of an
    extension.
  - `H̃^s(Ω)` is the closure of the test functions of `Ω` in `H^s(ℝ^d)`.
  - `H^s_0(Ω)` is the closure of their restrictions in `H^s(Ω)`.
  - `Rd.RestrictionSpace`, `Rd.tildeSpace`, `Rd.zeroBoundarySpace`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-restriction-spaces.html#def:sobolev-restriction-space)).
* **H.4 at `s = 1`.** Restriction is an isometry of `H̃^1(Ω)` onto `H^1_0(Ω)`, for every open
  `Ω`. `Rd.tildeEquivZeroBoundary`
  ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-restriction-spaces.html#thm:sobolev-tilde-zero-boundary)).
* **Duality for every real `s`.** `(H̃^s(Ω))^* ≅ H^{-s}(Ω)` and `(H^s(Ω))^* ≅ H̃^{-s}(Ω)`,
  isometrically. The pairing is the `L_2` pairing of `H^{-s}(ℝ^d)` with `H^s(ℝ^d)`, and is the
  value of the distribution on test functions. In particular `H^{-1}(Ω) = (H^1_0(Ω))^*`.
  `Rd.dualEquiv`, `Rd.dualRestrictionEquiv`
  ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-duality.html#thm:sobolev-duality)).
* **I.6: Rellich on `H^1(Ω)`.** For every bounded open `Ω`, the restriction
  `H^1(Ω) → L_2(Ω)` is injective, of norm at most one, and compact. This is Assumption F of
  Hiptmair, Pauly and Schulz. `Rd.isCompactOperator_restrictL2`
  ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-restriction-spaces.html#thm:sobolev-restriction-rellich)).

### On bounded Lipschitz domains

* **The domains.**
  - A bounded open set that is, near each boundary point, the region above the graph of a
    Lipschitz function is a bounded Lipschitz domain.
  - Open balls, bounded open convex sets and the open unit cube are examples.
  - Smooth local graphs give smooth bounded domains, whose closures are compact manifolds with
    boundary.
  - `Rd.IsBoundedLipschitzDomain`, `Rd.BoundedLipschitzDomain.ofIsBoundedLipschitzDomain`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-local-lipschitz-graphs.html#thm:bounded-lipschitz-sets)).
* **H.2: the extension theorem.**
  - For `1 ≤ p ≤ ∞` there is a bounded linear operator `E` from `W^1_p(Ω)` to `W^1_p(ℝ^d)` with
    `Eu = u` on `Ω`. It is built by reflection, and acts on pairs of a function and its weak
    gradient.
  - Hence `W^1_p(Ω)` is the space of restrictions of `W^1_p(ℝ^d)`.
  - For `1 < p < ∞` and every `m`, `W^m_p(Ω)` is the space of restrictions of `W^m_p(ℝ^d)`.
  - `Rd.BoundedLipschitzDomain.exists_extensionL`,
    `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-reflection-extension.html#thm:reflection-extension-operator)).
* **`H^1(Ω) = W^1_2(Ω)`, with equivalent norms, and Rellich for `W^1_2(Ω)`.** Every sequence
  bounded in `W^1_2(Ω)` has a subsequence converging in `L_2(Ω)`.
  `Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`
  ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-sobolev-extension.html#cor:rellich-weak-sobolev)).
* **Green's formula.**
  - For `u, w ∈ H^1(Ω)` and every direction `v`,
    `∫_Ω (∂_v u) w + u ∂_v w = ∫_Γ γu · γw ⟪v, ν⟫ dσ`.
  - Here `σ` is the surface measure, `γ` the trace into `L_2(Γ)` and `ν` the outward unit
    normal.
  - The normal is the normal of each chart almost everywhere.
  - `Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-lipschitz-domain-green.html#thm:domain-green)).

### On the boundary

* **The surface measure.**
  - The surface measure `σ` is Mathlib's `(d-1)`-dimensional Hausdorff measure on `Γ`, defined
    without charts.
  - The area formula for Lipschitz graphs, `σ(γ_j(A)) = ∫_A √(1 + |∇φ_j|²)`, expresses its
    integrals in the charts.
  - `L_2(Γ)` is the `L_2` space of `σ`.
  - `Rd.BoundedLipschitzDomain.surfaceMeasure`, `Rd.LipschitzGraph.lintegral_graphMap`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-surface-measure.html#thm:surface-measure-charts)).
* **The trace space `H^{1/2}(Γ)`.**
  - It is defined as the orthogonal complement of the kernel of the trace in `H^1(Ω)`.
  - The trace `H^1(Ω) → H^{1/2}(Γ)` and the extension `H^{1/2}(Γ) → H^1(Ω)` have norm at most
    one, and `H^1(Ω)/ker γ ≅ H^{1/2}(Γ)` isometrically.
  - Its norm is equivalent to the norm of `B^{1/2}_{2,2}(Γ)` taken chart by chart, and to the
    Sobolev–Slobodeckij norm `‖g‖_{L_2(Γ)}² + ∫_Γ ∫_Γ |g(x) - g(y)|² / |x - y|^d dσ dσ`.
  - `H^{-1/2}(Γ)` is its dual.
  - `Rd.BoundedLipschitzDomain.TraceSpace`, `Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`,
    `Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-boundary-trace-space.html#thm:trace-space-operators)).
* **The trace into `L_2(Γ)`.** `γ : H^1(Ω) → L_2(Γ)` is bounded and its kernel is the trace
  kernel. `Rd.BoundedLipschitzDomain.boundaryTraceL2`,
  `Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`
  ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-surface-measure.html#thm:trace-l2)).
* **`ker γ = H^1_0(Ω)` and the HPS quotient.**
  - `ker γ = H^1_0(Ω)` (McLean, Theorem 3.40).
  - `H^1(Ω)/H^1_0(Ω) ≅ H^{1/2}(Γ)`.
  - The zero extension of `u ∈ H^1(Ω)` lies in `H^1(ℝ^d)` iff `γu = 0`.
  - `Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`,
    `Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`
    ([blueprint](https://mario-ullrich.github.io/Lean-FunctionSpaces/sec-trace-kernel.html#thm:trace-kernel-zero-boundary)).

### Results that predate the proposal

* X.1, bounded Lipschitz domains: `Rd.BoundedLipschitzDomain`.
* X.2, the restriction space of `B^s_{p,q}(ℝ^d)` equals the intrinsic Besov space on `Ω`
  (Rychkov's extension): `Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn`.
* X.3, `B^s_{p,q}(Γ)` is the trace space of `B^{s+1/p}_{p,q}(Ω)` for `0 < s < 1`:
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`.
* X.4, Daubechies wavelets on `ℝ`: `Daubechies.besov_iff_coeff`.
* X.5, `F^s_{p,p} = B^s_{p,p}` on `ℝ^d`: `Rd.memTriebelLizorkin_iff_memApprox`.
* X.7 and X.8 are Mathlib's Bessel potential spaces, distributions on open sets and
  `extDeriv`.

## 2. How to use it

In the `lakefile.toml` of the FEEC/BEEC library:

```toml
[[require]]
name = "functionspaces"
git = "https://github.com/mario-ullrich/Lean-FunctionSpaces"
rev = "<commit>"
```

The toolchain is `leanprover/lean4:v4.35.0`, and Mathlib comes in at the tag `v4.35.0`.
`lake exe cache get` fetches the prebuilt Mathlib, `lake build` builds, and
`import FunctionSpaces` imports everything.

Conventions:

* Scalars are complex: functions are `V → ℂ`, and `L_p` is Mathlib's `Lp ℂ p volume`.
* The ambient space is any finite-dimensional real inner product space `V`; for `ℝ^d` take
  `EuclideanSpace ℝ (Fin d)`. Mathlib's Bessel potential spaces use the same `V`.
* Function spaces on `ℝ^d` are conditions on `L_p` functions, with norms in `[0, ∞]`. The
  Hilbert spaces are Mathlib's `H^{s, 2}(V, ℂ)` and its closed subspaces (Section 1).
* Results on `ℝ^d` live in the namespace `Rd`, results on bounded Lipschitz domains in
  `Rd.BoundedLipschitzDomain`. Results on domains assume `d ≥ 1` where the proofs need it.

Missing lemmas and wishes for other statement shapes go to the issue tracker of the repository,
with the item number of the proposal and the intended Lean statement. Commits keep the names of
this document; a commit that renames one updates this document and lists the old name in
Section 5.2.

## 3. What comes next

In Lean-FunctionSpaces:

* **One version for all libraries (I.0).** Lean-FunctionSpaces and Lean-SNumbers are on
  `v4.35.0`, and TauCeti is on `v4.36.0-rc2`. The FEEC/BEEC library should use the same version
  as the two:
  - `v4.35.0` needs no change in either library;
  - `v4.36.0` is the choice if the FEEC/BEEC library also uses TauCeti.
* **Wavelets on `ℝ^d` (I.4, then H.3).** Tensor-product Daubechies wavelets on `ℝ^d`, and the
  description of `B^s_{2,2}(ℝ^d) = H^s(ℝ^d)` by wavelet coefficients. The case `d = 1` is X.4.
  This is the last open interface item.
* **On request.**
  - `H̃^s(Ω) = H^s_0(Ω)` for `s ≠ 1` on Lipschitz domains (McLean, Theorem 3.33).
  - The trace `H^s(Ω) → H^{s-1/2}(Γ)` for `1/2 < s < 3/2` between the Hilbert spaces; X.3 has it
    for Besov spaces.
  - Vector-valued versions on `Ω` and `Γ`.

Bridges to other libraries:

* TauCeti has `W^{1,p}(Ω)` as a type, a trace `W^{1,p}(Ω) → L_p(Γ)` with the same Hausdorff
  measure on `Γ`, and its kernel `W^{1,p}_0(Ω)`. Once the versions agree, `H^1(Ω)` and the
  trace of this library can be identified with TauCeti's `W1p volume Ω 2` and
  `W1p.frontierTrace`.
* The Sobolev library of Rothgang, Nuccio and van Doorn has the total weak derivative
  `HasWeakDeriv`. Once it is in Mathlib, one lemma `HasWeakDeriv ↔ ∀ v, HasWeakLineDeriv`
  connects the two.

Together with the FEEC/BEEC team:

* Find out which statements the FEEC/BEEC library calls first, and adjust their shapes.
* The optional s-number track: widths of `H^s(Ω) ↪ H^t(Ω)` with Lean-SNumbers, once the
  versions agree.

In the FEEC/BEEC library:

* the forms layer: `L^2Λ^k`, the weak exterior derivative, `HΛ^k`, regular decompositions,
  `H^{-1/2}(curl_Γ, Γ)`;
* Picard's theorem from I.6.

## 4. Answers to the seven questions

1. **Field (I.0).**
   - Option (d): the abstract layers over `RCLike 𝕜`, as in Lean-SNumbers.
   - The function spaces are complex, as in Mathlib's `H^{s,p}`.
   - A transfer lemma to the real-valued functions where real Hilbert spaces are needed.
2. **Shapes.**
   - I.8 is `Rd.memSobolev_two_iff_exists_memApprox`.
   - I.6 is `Rd.isCompactOperator_restrictL2`.
   - I.4 is the `ℝ^d` version of `Daubechies.besov_iff_coeff` (Section 3).
3. **I.8.** Formalised for `p = 2` with explicit constants, and for every `1 < p < ∞`.
4. **Rellich on bounded Lipschitz domains.**
   - Yes for `H^1(Ω)` on every bounded open set.
   - Yes for `W^1_2(Ω)` on bounded Lipschitz domains, through the extension theorem.
5. **Vector values.**
   - Scalar here.
   - Mathlib's `H^{s,p}(V, F)` takes vector values on `ℝ^d`.
   - On `Ω` and `Γ` the FEEC/BEEC library works componentwise.
6. **Space types and surface measure.** Built here (Section 1).
7. **Split and versions.** The split Lean-SNumbers / Lean-FunctionSpaces / FEEC/BEEC library is
   right. The common version is open (Section 3).

## 5. Changes, removed names and design decisions

### 5.1 Changes to the proposal

* The space types on `Ω` and `Γ`, the duality, the trace space `H^{1/2}(Γ)`, the surface measure
  and the area formula were left to the FEEC/BEEC library by the first version of this document
  (commit `ec3c133`). They are built here.
* Green's formula and `ker γ = H^1_0(Ω)` are built here.
* H.2 holds for every `1 ≤ p ≤ ∞` with a bounded linear operator, and for `W^m_p` of every order
  when `1 < p < ∞`; the proposal asks for `p = 2`.
* I.8 holds for every `1 < p < ∞`.
* Beyond the proposal: `H^s(Ω) ≅ H̃^{-s}(Ω)`. Bounded Lipschitz domains also come from the usual
  definition by local graphs, with balls, convex sets and the cube as examples.
* The surface measure is Mathlib's Hausdorff measure, so "almost everywhere on `Γ`" means
  `σ`-almost everywhere; the chart filter `aeBoundary` of the trace theorem has the same null
  sets.

### 5.2 Renamed and removed Lean names

Names cited by earlier versions of this document:

| Earlier name | Present name |
|---|---|
| `Rd.BoundedLipschitzDomain.exists_extendsSobolev_of_one_le` | `Rd.BoundedLipschitzDomain.exists_extendsSobolev_reflection` |
| `Rd.BoundedLipschitzDomain.sobolevExtensionL_of_one_le` | `Rd.BoundedLipschitzDomain.sobolevExtensionL` |
| `Rd.BoundedLipschitzDomain.exists_extensionL_of_one_le` | `Rd.BoundedLipschitzDomain.exists_extensionL` |
| `Rd.BoundedLipschitzDomain.memWeakSobolev_of_mem_weakSobolevJet_of_one_le` | `Rd.BoundedLipschitzDomain.memWeakSobolev_of_mem_weakSobolevJet` |
| `Rd.exists_extensionL_of_isBoundedLipschitzDomain_of_one_le` | `Rd.exists_extensionL_of_isBoundedLipschitzDomain` |
| `Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev_of_one_le` | `Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev` |
| `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_of_one_le` | `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev` |
| `Rd.BoundedLipschitzDomain.nonnegPartition` | removed; `Rd.BoundedLipschitzDomain.boundaryPartition` is nonnegative |

The two names `Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev` and
`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev` first stood for `1 < p` and now
cover `1 ≤ p ≤ ∞`. Module paths changed with the folder layout of 23 October 2026 (commit
`cf58fd0`); declaration names did not, so a downstream file changes only its `import` lines.

### 5.3 Design decisions

* **Complex scalars and the ambient space `V`**, as in Mathlib's Bessel potential spaces, so both
  sides share types.
* **Conditions on `L_p` functions plus Hilbert-space types.** The Besov and Triebel–Lizorkin
  spaces stay conditions with norms in `[0, ∞]`. The Hilbert spaces are Mathlib's `H^s(ℝ^d)` and
  its closed subspaces, so Mathlib's projections, duals and compact operators apply directly.
* **`H^s(Ω)` is the restriction space** of Chandler-Wilde, Hewett and Moiola. Rellich then holds
  on every bounded set. On bounded Lipschitz domains it equals `W^1_2(Ω)` by the extension
  theorem; on some bounded open sets the two differ (a slit disc), and Rellich fails for
  `W^1_2(Ω)` (rooms and passages, Adams and Fournier, Chapter 6).
* **`H^{1/2}(Γ)` is the orthogonal complement of the trace kernel in `H^1(Ω)`.** Trace,
  extension and the quotient isometry then hold by construction. The content is the norm
  equivalence with `B^{1/2}_{2,2}(Γ)` and the Slobodeckij form.
* **Weak derivatives in Mathlib's `𝓓'(Ω)`, along directions**, the foundation that the Sobolev
  library prepared for Mathlib and a distributional exterior derivative also use.
* **The surface measure is Mathlib's Hausdorff measure** `μHE[d-1]` on `Γ`, normalised to be
  the volume on hyperplanes. The area formula gives its chart form, so two charts give the same
  integral on their overlap.
* **`B^s_{p,q}(Γ)` is defined chart by chart**, with Lebesgue measure on the hyperplanes of the
  charts and a fixed resolution of unity. Lemmas show independence of the resolution of unity.
* **Constants.**
  - On `ℝ^d` they are explicit for `p = 2`.
  - On `Ω` and `Γ`, and for `p ≠ 2`, they are existential: `∃ C, C ≠ ∞ ∧ …`.
  - The statements with constant one (restriction, trace, extension, quotient isometries) are
    exact.
* **The `H^1` norm has Mathlib's normalisation**, with the factor `2π` from the kernel
  `e^{-2πi⟨x, ξ⟩}`: `‖u|_Ω‖_2² + (2π)^{-2} ∑_i ‖∂_{e_i} u‖_{L_2(Ω)}² ≤ ‖u‖²`.
* **The duality is conjugate-linear in the first slot**, Mathlib's convention for inner products
  and for the Riesz map, so the duality isomorphisms are conjugate-linear isometries.
* **Rellich by truncation in frequency.** Cutting `𝓕F` off at `|ξ| ≤ K` changes `F` by at most
  `K⁻¹ ‖F‖_{H^1}` in `L_2`. The truncated functions are bounded and uniformly Lipschitz, so
  Arzelà–Ascoli makes the truncated operators compact, and their limit is compact.
* **Extension by reflection** across the boundary in flattened coordinates (Evans–Gariepy,
  Section 4.4), which covers `p = 1` and `p = ∞`. Rychkov's extension with local means of the
  gradient is a second operator for `1 < p < ∞`, and it gives `W^m_p` of every order.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics **140**,
  Elsevier/Academic Press, Amsterdam, 2003.
* S. N. Chandler-Wilde, D. P. Hewett, A. Moiola, *Sobolev spaces on non-Lipschitz subsets of `ℝ^n`
  with application to boundary integral equations on fractal screens*, Integral Equations
  Operator Theory **87** (2017), no. 2, 179–224.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  Textbooks in Mathematics, CRC Press, 2015.
* *FEEC and BEEC in Lean: a proposed proof structure*, version 4, 10 October 2026.
* R. Hiptmair, D. Pauly, E. Schulz, *Traces for Hilbert complexes*, J. Funct. Anal. **284**
  (2023), Paper No. 109905.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University
  Press, Cambridge, 2000.
* M. B. Rothgang, F. A. E. Nuccio, F. van Doorn, *SobolevSlobodeckij*, a Lean library of Sobolev
  spaces prepared for Mathlib, `github.com/grunweg/SobolevSlobodeckij`.
* V. S. Rychkov, *On restrictions and extensions of the Besov and Triebel–Lizorkin spaces with
  respect to Lipschitz domains*, J. London Math. Soc. (2) **60** (1999), no. 1, 237–257.
* *TauCeti*, a Lean library downstream of Mathlib, `github.com/TauCetiProject/TauCeti`.
