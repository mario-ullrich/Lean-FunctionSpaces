# Lean-FunctionSpaces for FEEC and BEEC: the interface

Part of [Function spaces via approximation](../README.md). Blueprint chapter: *Sobolev spaces on
`ℝ^d`*. Block document: [Sobolev spaces on `ℝ^d`](SobolevRd.md).

## 1. Purpose

This document is written for the authors of the FEEC/BEEC library proposed in *FEEC and BEEC in
Lean: a proposed proof structure* (version 4, 10 October 2026). It lists the results of
Lean-FunctionSpaces that the interface items of the proposal ask for, with Lean names, files and
hypotheses, records the decisions behind their form, and names what the FEEC/BEEC library builds
on top of them.

Lean-FunctionSpaces formalises function-space foundations: Sobolev, Besov and Triebel–Lizorkin
spaces, their characterisations, extensions, traces and embeddings. For the collaboration it
supplies Mathlib's Hilbert spaces `H^s(ℝ^d)` as Besov spaces `B^s_{2,2}(ℝ^d)` (item I.8), weak
derivatives, `H^1` on bounded Lipschitz domains with its weak gradient and its trace, and
Rellich's compactness theorem for the restriction space (items I.6 and H.1 in that form,
Section 4.5; the weak-derivative form needs H.2, Section 5). Forms, Hilbert complexes, duality,
negative smoothness, the space types on domains and boundaries, and the surface measure belong
to the FEEC/BEEC library (Section 6); Section 9 records how this division changes: most of
Section 6 moves into Lean-FunctionSpaces, the forms layer stays with the FEEC/BEEC library.

## 2. Depending on Lean-FunctionSpaces

In the `lakefile.toml` of the FEEC/BEEC library:

```toml
[[require]]
name = "functionspaces"
git = "https://github.com/mario-ullrich/Lean-FunctionSpaces"
rev = "<commit>"
```

with `<commit>` a commit of `main` (Section 8). The toolchain is `leanprover/lean4:v4.35.0-rc2`
in `lean-toolchain`, and Mathlib comes in through Lean-FunctionSpaces at the tag `v4.35.0-rc2`; a
direct Mathlib requirement of the FEEC/BEEC library names the same tag. Then

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

from the project folder. `import FunctionSpaces` imports everything; single files are imported
by their module names, such as `import FunctionSpaces.Rd.RellichCompactness`. Lean-FunctionSpaces
uses Lean's module system (`module`, `public import`, `@[expose] public section`), so every
declaration and every definition body is public, and the importing files need no special form.

The blueprint states every result with its proof and its Lean name:
<https://mario-ullrich.github.io/Lean-FunctionSpaces/>, as PDF
<https://mario-ullrich.github.io/Lean-FunctionSpaces/blueprint.pdf>, and the dependency graph
<https://mario-ullrich.github.io/Lean-FunctionSpaces/dep_graph_document.html>. The results of this
document are in its chapter *Sobolev spaces on `ℝ^d`*, the bounded Lipschitz domains and traces in
the chapter *Function spaces on `ℝ^d`*.

## 3. Conventions (item I.0)

* **Scalars**: complex. Functions are `V → ℂ`, and `L_p` is Mathlib's `Lp ℂ p volume`.
* **Ambient space**: any finite-dimensional real inner product space `V`, with
  `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]`. For `ℝ^d` this is `EuclideanSpace ℝ (Fin d)` (the type `Fin d → ℝ` carries
  the sup norm). Mathlib's Bessel potential spaces use the same `V`, so both sides share the
  ambient type.
* **Measure**: Lebesgue measure `volume`; on a set `Ω`, `volume.restrict Ω`.
* **Function spaces are predicates** on `Lp ℂ p volume` (for weak derivatives on open sets, on
  functions `V → ℂ`), with quasi-norms in `ℝ≥0∞` (`‖f‖ₑ`, `eLpNorm`, `triebelLizorkinNorm`). The
  Hilbert-space type on `V` is Mathlib's `BesselPotentialSpace V ℂ s 2`, notation `H^{s}(V)` or
  `H^{s, 2}(V, ℂ)` (scoped in `BesselPotentialSpace`), a complete complex inner product space;
  item I.8 below relates it to the predicates.
* **Values**: scalar. Vector values are handled componentwise. Mathlib's `BesselPotentialSpace`
  takes every complete complex normed space `F` as value space, so `H^s(V; F)` exists on `V` for
  the form values `F = V [⋀^Fin k]→L[ℝ] ℂ` as well, the type of Mathlib's `extDeriv`, which
  carries the instances `NormedSpace ℂ` and `CompleteSpace`.
* **Universes**: every statement takes `V : Type*`, so one universe serves the whole
  development.
* **Field for the FEEC/BEEC library**: see question 1 in Section 7.
* **Names**: the results on `V` live in the namespace `Rd`, those on bounded Lipschitz domains in
  `Rd.BoundedLipschitzDomain`. `Rd.MemSobolev` (weak derivatives) and Mathlib's
  `TemperedDistribution.MemSobolev` (Bessel potentials) share their last component, so files that
  use both write both namespaces in full. Notation needs
  `open scoped SchwartzMap FourierTransform LineDeriv Distributions BesselPotentialSpace` for
  `𝓢(V, ℂ)`, `𝓢'(V, ℂ)`, `𝓕`, `∂^{v}`, `𝓓'(Ω, F)` and `H^{s, p}(V, F)`.

## 4. The interface items

Throughout, `V` is as in Section 3, `f : Lp ℂ 2 (volume : Measure V)` unless said otherwise, and
`J_s = TemperedDistribution.besselPotential V ℂ s` is the Fourier multiplier
`⟨ξ⟩^s = (1 + ‖ξ‖²)^(s/2)` on tempered distributions. Mathlib's `H^s(V)` consists of the tempered
distributions `u` with `J_s u ∈ L_2(V)` (`TemperedDistribution.MemSobolev s 2 u`).

### 4.1 I.8: Mathlib's `H^s(ℝ^d)` is the Besov space `B^s_{2,2}(ℝ^d)`

File `FunctionSpaces/Rd/SobolevTwoLittlewoodPaley.lean`.

* `Rd.memSobolev_two_iff_exists_memApprox (hs : 0 < s) (u : 𝓢'(V, ℂ))`: for `s > 0`,
  `TemperedDistribution.MemSobolev s 2 u` iff `u` is an `L_2(V)` function `f` in the
  approximation space `A^s_2` of the band-limited functions,
  `(bandScheme two_ne_top).MemApprox s 2 f`, which is `B^s_{2,2}(V)`. This is I.8 in the shape of
  the proposal.
* `Rd.memSobolev_two_iff_memTriebelLizorkin (hs : 0 ≤ s) (u)`: for `s ≥ 0`, the same with the
  Triebel–Lizorkin space `F^s_{2,2}(V)` (`Rd.MemTriebelLizorkin s 2 f`), and
  `Rd.memSobolev_two_iff_littlewoodPaleyNorm_lt_top (hs : 0 ≤ s) (u)` with the Littlewood–Paley
  norm `‖(2^(js) ‖ψ_j ⋆ f‖_2)_j‖_{ℓ_2}`.
* Explicit norm bounds, for `s ≥ 0` and `f, h ∈ L_2(V)` with `J_s f = h`:
  `‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖h‖_2` (`Rd.triebelLizorkinNorm_le_of_besselPotential_eq`)
  and `‖h‖_2 ≤ (2 · 5^s)^{1/2} ‖f‖_{F^s_{2,2}}`
  (`Rd.enorm_besselPotential_le_triebelLizorkinNorm`).
* The bundled form `Rd.exists_eq_toDistr_two (hs : 0 ≤ s) (F : H^{s}(V))`: every element `F` of
  Mathlib's Hilbert space is an `L_2(V)` function `f` with `MemTriebelLizorkin s 2 f` and
  `‖f‖_{F^s_{2,2}} ≤ (2 · 4^s)^{1/2} ‖F‖`.

Through I.8 every description of `B^s_{2,2}(V)` in the library applies to `H^s(V)`: moduli of
smoothness (`Rd.memApprox_bandScheme_iff_modulus`), local means and atoms (chapter *Function
spaces on `ℝ^d`* of the blueprint).

### 4.2 Weak derivatives

File `FunctionSpaces/Rd/WeakDerivatives.lean` (definitions, `W^m_p`) and
`FunctionSpaces/Rd/SobolevTwoLittlewoodPaley.lean` (`W^1_2 = H^1`).

* `Rd.HasWeakLineDeriv (Ω : Opens V) (v : Fin k → V) (f g : V → ℂ)`: `f` and `g` are locally
  integrable on `Ω` and `∂^v f = g` as distributions on `Ω` (Mathlib's
  `Distribution.ofFun Ω f volume ⊤` in `𝓓'(Ω, ℂ)`), where `∂^v = ∂_{v_0} ⋯ ∂_{v_{k-1}}` is the
  iterated directional derivative. Equivalently `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every real test
  function `φ ∈ 𝓓(Ω, ℝ)` (`Rd.hasWeakLineDeriv_iff_integral`). Basic facts:
  `Rd.HasWeakLineDeriv.unique` (a.e. on `Ω`), `.add`, `.sub`, `.neg`, `.smul`, `.congr_ae`,
  `.mono` (restriction to a smaller open set), `.of_tendsto` (limits in `L_p(Ω) × L_r(Ω)`), and
  `Rd.hasWeakLineDeriv_schwartz` (the classical derivative of a Schwartz function).
* `Rd.MemWeakSobolev (Ω : Opens V) (m : ℕ) (p : ℝ≥0∞) (f : V → ℂ)`: `W^m_p(Ω)`, that is,
  `f ∈ L_p(Ω)` and every weak derivative of order at most `m`, in all directions, exists on `Ω` and
  lies in `L_p(Ω)`. `Rd.MemSobolev m f := MemWeakSobolev ⊤ m p f` for `f : Lp ℂ p volume` is
  `W^m_p(V)`.
* The bridge to tempered distributions, `Rd.hasWeakLineDeriv_top_iff`: for `f ∈ L_p(V)` and
  `g ∈ L_r(V)`, `1 ≤ p, r ≤ ∞`, `HasWeakLineDeriv ⊤ v f g` iff `∂^{v} (f : 𝓢'(V, ℂ)) = g`; and
  `Rd.memSobolev_iff_tempered`.
* `W^1_2 = H^1`, `Rd.memSobolev_one_iff (f)`:
  `Rd.MemSobolev 1 f ↔ TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(V, ℂ))`, with
  `‖∂_v f‖_2 ≤ 2π ‖v‖ ‖J_1 f‖_2` (`Rd.enorm_le_of_hasWeakLineDeriv`) and, for every orthonormal
  basis `(e_i)` of `V`, `(2π)² ‖J_1 f‖_2² = (2π)² ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²`
  (`Rd.enorm_besselPotential_one_sq_eq`), hence `‖J_1 f‖_2² ≤ ‖f‖_2² + ∑_i ‖∂_{e_i} f‖_2²`
  (`Rd.sq_norm_besselPotential_one_le`). Also `W^1_2(V) = B^1_{2,2}(V)`
  (`Rd.memSobolev_one_iff_memApprox`, `Rd.memSobolev_one_iff_modulus`).

**Relation to other Lean libraries.** Rothgang, Nuccio and van Doorn prepare a Sobolev library for
Mathlib (`github.com/grunweg/SobolevSlobodeckij`) with `HasWeakDeriv` for the total derivative and
`MemSobolev f k p Ω`. It is built on the same objects as `Rd.HasWeakLineDeriv`: Mathlib's
distributions `𝓓'(Ω, ·)` on `Ω : Opens V`, real test functions, `Distribution.ofFun`, unbundled
functions with local integrability. The directional derivatives along a basis determine the total
derivative, so a lemma `HasWeakDeriv ↔ ∀ v, HasWeakLineDeriv` is the first bridge to write once
that library is in Mathlib. The De Giorgi–Nash–Moser library of Armstrong and Kempe
(`github.com/scottnarmstrong/DeGiorgi`) defines
`HasWeakPartialDeriv` and `HasWeakGrad` by test-function integrals, the form of
`Rd.hasWeakLineDeriv_iff_integral` with `v` a coordinate direction.

### 4.3 `H^1` on bounded Lipschitz domains (step 2 of the proposal; the inclusion half of H.2)

File `FunctionSpaces/Rd/LipschitzDomainH1.lean`; `Ω : Rd.BoundedLipschitzDomain V` (X.1), with
`Ω.carrier` the open set and `Ω.toOpens : Opens V` the same set as an element of `Opens V`.

* `Rd.BoundedLipschitzDomain.MemSobolevOn Ω f`: `H^1(Ω)` as the restriction space,
  `∃ F, Rd.MemSobolev 1 F ∧ F =ᵐ[volume.restrict Ω.carrier] f`; only the values of `f` on `Ω`
  matter (`.MemSobolevOn.congr_ae`), and `H^1(Ω)` is a linear subspace
  (`.memSobolevOn_of_memSobolev`, `.zero_memSobolevOn`, `.MemSobolevOn.add`, `.MemSobolevOn.smul`).
* Intrinsic description, `Rd.BoundedLipschitzDomain.memSobolevOn_iff_modulusOn (hr : 2 ≤ r)`:
  `f ∈ H^1(Ω)` iff `‖f‖_{L_2(Ω)} + ‖(2^k ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_2} < ∞`, with the moduli of
  smoothness inside `Ω` (`Rd.lpModulusOn`); the Besov form is
  `Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_memApprox`.
* The weak gradient, `Rd.BoundedLipschitzDomain.MemSobolevOn.memWeakSobolev`: every
  `f ∈ H^1(Ω)` satisfies `Rd.MemWeakSobolev Ω.toOpens 1 2 f`, so its weak derivatives on `Ω`
  exist and lie in `L_2(Ω)`. The converse inclusion, and with it H.2, needs the extension
  theorem for `W^{1,2}` (Section 5).
* Norms on `Ω`: the restriction direction has constant `1`: the intrinsic quantity of `f` is at
  most `‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2}` for every `F` with `F = f` on `Ω`
  (`Rd.BoundedLipschitzDomain.modNormOn_le_modNorm_of_ae_eq`). The extension direction is
  qualitative (Section 5).

### 4.4 The trace (H.7 at `k = 0` in qualitative form, X.3)

File `FunctionSpaces/Rd/LipschitzDomainH1.lean`, on top of
`FunctionSpaces/Rd/LipschitzBoundaryTrace.lean`. For a resolution of unity
`ψ : Ω.BoundaryPartition` on the boundary `Γ`:

* `Rd.BoundedLipschitzDomain.MemBoundaryBesov Ω p ψ s q g`: `g ∈ B^s_{p,q}(Γ)`, chart by chart:
  every piece `(ψ_j g) ∘ γ_j` on the hyperplane of the `j`-th chart lies in `B^s_{p,q}` of that
  hyperplane, with Lebesgue measure there, by first differences, which describe `B^s_{p,q}` for
  `0 < s < 1`, the range of the trace theorem.
* Resolutions of unity exist (`Rd.BoundedLipschitzDomain.nonempty_boundaryPartition`), and for
  `0 < s < 1` neither `MemBoundaryBesov` nor the boundary trace depends on the choice of `ψ`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_of_boundaryPartition`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`).
* `Rd.BoundedLipschitzDomain.IsBoundaryTrace Ω ψ hp L σ q f g`: `g` is the boundary trace of
  `f`, that is, the trace `Rd.BoundedLipschitzDomain.boundaryTrace` of every admissible extension
  of `f` agrees with `g` almost everywhere on `Γ`, in the sense of the chart filter
  `Rd.BoundedLipschitzDomain.aeBoundary`.
  For `H^1(Ω)` the admissible extensions are the `F ∈ W^1_2(V)` with `F = f` on `Ω`
  (`Rd.BoundedLipschitzDomain.isBoundaryTrace_iff_forall_memSobolev`).
* Every `f ∈ H^1(Ω)` has a boundary trace in `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memSobolevOn`), unique almost everywhere
  on `Γ` (`Rd.BoundedLipschitzDomain.MemSobolevOn.isBoundaryTrace_unique`), and every
  `g ∈ B^{1/2}_{2,2}(Γ)` is the boundary trace of some `f ∈ H^1(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_memSobolevOn_of_memBoundaryBesov`); together
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_memSobolevOn`.
* The trace bound on one Lipschitz graph domain has an existential constant
  (`Rd.LipschitzGraph.modNorm_trace_le`); on bounded Lipschitz domains the trace statements are
  qualitative.

### 4.5 I.6 and H.1 for the restriction space: Rellich's theorem

File `FunctionSpaces/Rd/RellichCompactness.lean`.

* `Rd.toL2 : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 volume` reads an element of Mathlib's `H^1(V)` as the
  `L_2` function it is (`Rd.toTemperedDistribution_toL2`), with `‖toL2 F‖ ≤ ‖F‖`
  (`Rd.norm_toL2_le`).
* `Rd.isCompactOperator_restr_toL2 (hΩ : Bornology.IsBounded Ω)`: for every bounded set
  `Ω : Set V`, of any shape and without measurability hypotheses,
  `IsCompactOperator (LpToLpRestrictCLM V ℂ ℂ volume 2 Ω ∘L toL2)`, the restriction from `H^1(V)`
  to `L_2(Ω)` is compact.
* Sequence forms: `Rd.exists_subseq_tendsto_restr` (bounded sequences in `H^1(V)`) and
  `Rd.exists_subseq_tendsto_restr_of_hasWeakLineDeriv` (sequences `f_n ∈ L_2(V)` with weak
  derivatives `∂_{e_i} f_n ∈ L_2(V)` along an orthonormal basis and
  `‖f_n‖_2² + ∑_i ‖∂_{e_i} f_n‖_2² ≤ M²`).

Two further steps belong to the FEEC/BEEC library, which builds the quotient type (Section 6).
On a bounded Lipschitz domain, the restrictions to `Ω` of the functions of `H^1(Ω)` of
Section 4.3 form the image of `LpToLpRestrictCLM V ℂ ℂ volume 2 Ω.carrier ∘L toL2`, so the
theorem above is H.1 for the restriction space. The ingredients for the way from the predicate
to Mathlib's type: for `f ∈ L_2(V)`, `Rd.memSobolev_one_iff` turns `Rd.MemSobolev 1 f` into
`TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(V, ℂ))`, Mathlib's
`TemperedDistribution.MemSobolev.toBesselPotentialSpace` makes this an element of
`H^{1, 2}(V, ℂ)`, and `Rd.toL2_eq_of_toDistr_eq` shows that `toL2` of that element is `f`.
With `H^1(Ω)` as a quotient of `H^{1, 2}(V, ℂ)` by the closed subspace of the `F` with
`toL2 F = 0` almost everywhere on `Ω`, the restriction factors through the quotient, and the
induced operator `H^1(Ω) → L_2(Ω)` is compact, since the unit ball of the quotient lies in the
image of every ball of radius larger than `1`. This is I.6, for the restriction space, in the
form that the proposal needs for Assumption F of Hiptmair, Pauly and Schulz (HPS), which asks
for the compactness of `H^1(Ω) ↪ L_2(Ω)`.

### 4.6 Items X.1–X.5, X.7, X.8

* X.1, bounded Lipschitz domains: `Rd.BoundedLipschitzDomain`
  (`FunctionSpaces/Rd/BoundedLipschitz.lean`).
* X.2, restriction equals intrinsic Besov space, by Rychkov's extension: for `1 ≤ p < ∞`,
  `0 < s < r`, `1 ≤ q ≤ ∞`, `Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn` and
  `Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff` (same file).
* X.3, `B^s_{p,q}(Γ)` is the trace space of `B^{s+1/p}_{p,q}(Ω)` for `0 < s < 1`:
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`
  (`FunctionSpaces/Rd/LipschitzBoundaryTrace.lean`).
* X.4, Daubechies wavelets on `ℝ`: `Daubechies.besov_iff_coeff`
  (`FunctionSpaces/Wavelets/Daubechies/Besov.lean`).
* X.5, `F^s_{p,p} = B^s_{p,p}` on `ℝ^d`: `Rd.memTriebelLizorkin_iff_memApprox`
  (`FunctionSpaces/Rd/TriebelLizorkin.lean`); `B^s_{2,2} = H^s` on the torus:
  `Torus.memBesov_two_two_iff` (`FunctionSpaces/Torus/Coefficients.lean`).
* X.7, Mathlib's Bessel potential spaces: `BesselPotentialSpace`, `TemperedDistribution.MemSobolev`,
  `TemperedDistribution.besselPotential`.
* X.8, Mathlib's distributions on open sets and differential forms: `Distribution` (`𝓓'(Ω, F)`),
  `extDeriv`.

### 4.7 Later

The next part of Lean-FunctionSpaces continues with the square function theorem
`L_p = F^0_{p,2}`, `W^m_p = F^m_{p,2}` and Mathlib's `H^{s,p} = F^s_{p,2}` for all `1 < p < ∞`,
and the Sobolev embeddings on `ℝ^d`. They generalise Sections 4.1 and 4.2 from `p = 2`; the
`p = 2` statements above stay, with their explicit constants.

## 5. Decisions and reasons

* **Statements on `Ω` are qualitative.** The extension theorem for bounded Lipschitz domains
  (Rychkov's extension, assembled with a resolution of unity) and the trace theorem carry
  existential constants, so the statements on `Ω` are equivalences of membership, with the
  restriction bound of constant `1` as the one norm statement. Norm equivalences with explicit
  constants hold on `V` (Sections 4.1 and 4.2).
* **`H^s(Ω)` is the restriction space**, the definition of Chandler-Wilde, Hewett and Moiola (the
  proposal cites their §3.1.4). Rellich's theorem then holds on every bounded set. Every function
  of `H^1(Ω)` lies in the weak-derivative space `W^1_2(Ω)`, on every open set. On bounded Lipschitz
  domains the two spaces agree by the extension theorem for `W^{1,2}` of Calderón and Stein
  (Stein 1970, Chapter VI, §3), which the libraries built on this one supply (Section 6); on some
  bounded open sets they differ (a slit disc), and the embedding `W^1_2(Ω) ↪ L_2(Ω)` can fail to
  be compact (the rooms-and-passages domains, Adams and Fournier, Chapter 6). This splits H.1
  and I.6: the restriction version is formalised for every bounded set, and the weak-derivative
  version on Lipschitz domains follows from it together with the extension theorem.
* **`B^s_{p,q}(Γ)` is defined chart by chart**, with Lebesgue measure on the hyperplanes of the
  charts, and "almost everywhere on `Γ`" is the chart filter `aeBoundary`, whose exceptional sets
  are, mathematically, the null sets of the surface measure. Boundary integral operators need the
  surface measure itself (Section 6).
* **Predicates plus Mathlib's type.** The spaces of Lean-FunctionSpaces are predicates on
  `Lp ℂ p volume`; the Hilbert-space type on `V` is Mathlib's `H^{s, 2}(V, ℂ)`, tied to the
  predicates by I.8 and `Rd.toL2`. Space types on `Ω` and `Γ` belong to the FEEC/BEEC library,
  which knows which norms and which quotient or subspace structure it needs.
* **Weak derivatives in Mathlib's distributions on open sets**, along directions `v : Fin k → V`,
  so that they meet the Sobolev library prepared for Mathlib (Section 4.2) and the distributional
  exterior derivative that the FEEC/BEEC library builds on the same `𝓓'(Ω, ·)`; Mathlib's
  `extDeriv` is its classical counterpart on smooth forms.
* **Rellich by truncation in frequency.** For `K > 0`, cutting `𝓕F` off to the ball `|ξ| ≤ K`
  changes `F` by at most `K⁻¹ ‖F‖_{H^1}` in `L_2` (`Rd.norm_toL2_sub_truncL2_apply_le`; in
  operator norm `Rd.norm_toL2_sub_truncL2_le`); the truncated functions are
  bounded and uniformly Lipschitz on `V`, so the Arzelà–Ascoli theorem makes the truncated
  operators compact (`Rd.isCompactOperator_restr_truncL2`), and their operator-norm limit is
  compact. The argument works on all of `V` with band-limited functions and holds for every
  bounded set.

## 6. What the FEEC/BEEC library builds

The list below is the division of the first version of this document. Its first five items now
move into Lean-FunctionSpaces (Section 9); the last item stays with the FEEC/BEEC library.

* Space types on `Ω` and `Γ` with their norms: `H^1(Ω)` as a quotient or a closed subspace of
  `H^{1, 2}(V, ℂ)`, `H^{1/2}(Γ)` as a normed type, restriction, extension and trace as bounded
  operators.
* `ker γ = H^1_0(Ω)` on Lipschitz domains (McLean, Theorem 3.40), needed for the HPS quotient
  `H^1(Ω)/H^1_0(Ω) ≅ H^{1/2}(Γ)`.
* Negative order and duality: `H^{-1/2}(Γ)`, `H^{-1/2}(curl_Γ, Γ)`, `H̃^s(Ω)` and H.4.
* The surface measure on `Γ` and `L_2(Γ)`: Mathlib's Hausdorff measure `μH[d-1]` restricted to
  `Γ`, related to the charts by the area formula for Lipschitz graphs, a candidate for a Mathlib
  contribution.
* The extension theorem for `W^{1,2}` on Lipschitz domains, if the weak-derivative `H^1(Ω)` is
  wanted on its own (two routes: Rychkov's extension operator of the library, shown bounded from
  weak `W^{1,2}(Ω)` to `H^1(V)` by integrating its cone kernels by parts; or reflection in the
  straightened coordinates of `FunctionSpaces/Rd/GraphStraightening.lean`, which needs a chain
  rule for `W^{1,2}` under bi-Lipschitz maps and a Meyers–Serrin density theorem).
* The forms layer (`L^2Λ^k`, weak `d`, `HΛ^k`, regular decompositions), Picard's theorem from I.6,
  and the s-number track together with Lean-SNumbers.

## 7. Answers to the seven questions

1. **Field (I.0).** Option (d): the abstract layers over `RCLike 𝕜` (Lean-SNumbers already works
   this way; Lax–Milgram over `RCLike` is a short addition to Mathlib's real `IsCoercive` version
   through `InnerProductSpace.toDual`), the function spaces complex as in Mathlib's `H^{s,p}` and
   here, and a transfer lemma to the closed real subspace of real-valued functions where real
   Hilbert spaces are wanted.
2. **Shapes.** I.8 is `Rd.memSobolev_two_iff_exists_memApprox` (Section 4.1). I.6 is
   `Rd.isCompactOperator_restr_toL2` for the restriction space (Section 4.5). I.4 is the `ℝ^d`
   version of `Daubechies.besov_iff_coeff`, with tensor-product wavelets on
   `EuclideanSpace ℝ (Fin d)`; it is on the list of later goals of Lean-FunctionSpaces.
3. **I.8.** Yes, it is formalised for `p = 2` (Section 4.1); `H^s_p = F^s_{p,2}` for all
   `1 < p < ∞` follows in the next part of Lean-FunctionSpaces.
4. **Rellich on bounded Lipschitz domains.** Yes for the restriction space, on every bounded set
   (Section 4.5). For the weak-derivative space on Lipschitz domains it follows together with the
   extension theorem for `W^{1,2}` (Section 5).
5. **Vector values.** Scalar in Lean-FunctionSpaces; on `V` Mathlib's `H^{s,p}(V, F)` takes vector
   values directly, and on `Ω` and `Γ` the FEEC/BEEC library works with `Fin m → ℂ`-valued
   functions and componentwise lemmas.
6. **Space types and surface measure.** Predicates and Mathlib's type on `V` here; the types on
   `Ω` and `Γ` and the surface measure follow here as well (Section 9).
7. **Split and versions.** The split Lean-SNumbers / Lean-FunctionSpaces / FEEC/BEEC library is
   right. Lean-FunctionSpaces pins Lean and Mathlib `v4.35.0-rc2`, Lean-SNumbers moves to the
   same pin, and the FEEC/BEEC library takes it as well; the three move to the stable release
   together.

## 8. Versioning

The Lean declarations cited here are those of commit `199a2ef` of `main`; later commits keep them
unless this document says otherwise, and the commit that changes an interface name updates this
document. Pin `rev` to a commit at or after the one that adds this document. Missing lemmas and
wishes for other statement shapes go to the issue tracker of the GitHub repository, with the item
number of the proposal and the intended Lean statement.

## 9. Changes to the original plan (14 October 2026)

The first version of this document (commit `ec3c133`) left items 1–5 of Section 6 to the
FEEC/BEEC library. Lean-FunctionSpaces now builds them itself, in its current part (Part Ib of
its development plan); the statements below are in preparation and enter Section 4 with their
Lean names as they are formalised.

* **Space types.** `H^s(Ω)` for every open `Ω` and every real `s` as a Hilbert space: the
  orthogonal complement, in Mathlib's `H^{s}(ℝ^d)`, of the elements that vanish on `Ω`, hence
  isometric to the quotient of CWHM, §3.1.4; `H̃^s(Ω)` as the closure of the test functions of
  `Ω` in `H^s(ℝ^d)`, `H^s_0(Ω)` as their closure in `H^s(Ω)`; the restriction to `L_2(Ω)` as a
  bounded injective operator, compact for bounded `Ω` (Rellich in operator form, HPS Assumption
  F).
* **H.4 and duality.** `H̃^1(Ω) ≅ H^1_0(Ω)` isometrically for every open `Ω`; for every real `s`
  the duality `(H̃^s(Ω))^* ≅ H^{-s}(Ω)` and `(H^s(Ω))^* ≅ H̃^{-s}(Ω)` with the pairing of
  `H^{-s}(ℝ^d)` and `H^s(ℝ^d)` (CWHM, Theorem 3.3).
* **The trace space.** `H^{1/2}(Γ)` as the orthogonal complement of the kernel of the trace in
  `H^1(Ω)`, with the trace as orthogonal projection and the extension as inclusion (both of norm
  one), `H^1(Ω)/ker γ ≅ H^{1/2}(Γ)`, and `H^{-1/2}(Γ)` as its dual.
* **The surface measure.** Mathlib's Hausdorff measure `μHE[d-1]` restricted to `Γ`, with no
  charts in the definition. The area formula for Lipschitz graphs, proved here, expresses its
  integrals in the charts with the Gram density `√(1 + ‖∇φ‖²)`; `L_2(Γ)` is the `L_2` space of
  this measure, and the trace is an injective bounded operator `H^{1/2}(Γ) → L_2(Γ)`.
* **Green's formula** on bounded Lipschitz domains for `H^1` functions, in chart form and with
  the surface measure and the outward unit normal.
* **`ker γ = H^1_0(Ω)`** (McLean, Theorem 3.40) and the HPS quotient
  `H^1(Ω)/H^1_0(Ω) ≅ H^{1/2}(Γ)`.
* **The extension theorem H.2** for `W^{1,2}` on bounded Lipschitz domains (the restriction space
  equals the weak-derivative space), by Rychkov's extension operator with local means of the
  gradient; with it Rellich and the trace statements hold for the weak-derivative space.

The FEEC/BEEC library keeps the forms layer (`L^2Λ^k`, weak `d`, `HΛ^k`, regular
decompositions, `H^{-1/2}(curl_Γ, Γ)`), Picard's theorem and the s-number track.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics **140**,
  Elsevier/Academic Press, Amsterdam, 2003.
* S. Armstrong, J. Kempe, *Formalization of De Giorgi–Nash–Moser theory in Lean*,
  arXiv:2604.05984, 2026; the Lean library `github.com/scottnarmstrong/DeGiorgi`.
* S. N. Chandler-Wilde, D. P. Hewett, A. Moiola, *Sobolev spaces on non-Lipschitz subsets of `ℝ^n`
  with application to boundary integral equations on fractal screens*, Integral Equations
  Operator Theory **87** (2017), no. 2, 179–224.
* *FEEC and BEEC in Lean: a proposed proof structure*, version 4, 10 October 2026.
* R. Hiptmair, D. Pauly, E. Schulz, *Traces for Hilbert complexes*, J. Funct. Anal. **284**
  (2023), Paper No. 109905.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University
  Press, Cambridge, 2000.
* M. B. Rothgang, F. A. E. Nuccio, F. van Doorn, *SobolevSlobodeckij*, a Lean library of Sobolev
  spaces prepared for Mathlib, `github.com/grunweg/SobolevSlobodeckij`.
* V. S. Rychkov, *On restrictions and extensions of the Besov and Triebel–Lizorkin spaces with
  respect to Lipschitz domains*, J. London Math. Soc. (2) **60** (1999), no. 1, 237–257.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  Mathematical Series **30**, Princeton University Press, Princeton, NJ, 1970.
