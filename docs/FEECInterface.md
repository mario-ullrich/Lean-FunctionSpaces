# Lean-FunctionSpaces for FEEC and BEEC: the interface

Part of [Characterizations of Function Spaces](../README.md). Blueprint: parts *Sobolev and
Bessel potential spaces* and *Domains, traces and manifolds*, chapters *Sobolev spaces on `ℝ^d`*,
*Bessel potential spaces*, *Lipschitz domains*, *Traces on Lipschitz domains* and *Sobolev spaces
on domains*. Block documents: [Sobolev spaces on `ℝ^d`](SobolevRd.md) and [Domains, traces and
manifolds](DomainsTraces.md).

## 1. Purpose

This document is written for the authors of the FEEC/BEEC library proposed in *FEEC and BEEC in
Lean: a proposed proof structure* (version 4, 10 October 2026). It lists the results of
Lean-FunctionSpaces that the interface items of the proposal ask for, with Lean names, files and
hypotheses, records the decisions behind their form, and names what the FEEC/BEEC library builds
on top of them.

Lean-FunctionSpaces formalises function-space foundations: Sobolev, Besov and Triebel–Lizorkin
spaces, their characterisations, extensions, traces and embeddings. For the collaboration it
supplies Mathlib's Hilbert spaces `H^s(ℝ^d)` as Besov spaces `B^s_{2,2}(ℝ^d)` (item I.8), weak
derivatives, `H^1` on bounded Lipschitz domains with its weak gradient and its trace, the
Hilbert spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` on open sets and their duality, the trace
space `H^{1/2}(Γ)` of a bounded Lipschitz domain, defined as the orthogonal complement of the
trace kernel in `H^1(Ω)`, with its trace and extension operators and its dual `H^{-1/2}(Γ)`, the
area formula for Lipschitz graphs, the surface measure of `Γ` with
`L_2(Γ)` and the trace into it, Rellich's compactness theorem for the restriction space
(items I.6 and H.1 in that form, Section 4.5), and the extension theorem H.2 for `W^{1,p}`,
`1 ≤ p ≤ ∞`, with `H^1(Ω) = W^{1,2}(Ω)` and Rellich's theorem in the weak-derivative form
(Section 4.3), Gauss–Green and Green's formula on Lipschitz graph domains (Section 4.11),
Green's formula on bounded Lipschitz domains with the zero extension of functions with vanishing
trace (Section 4.12), and `ker γ = H^1_0(Ω)` with the quotient `H^1(Ω)/H^1_0(Ω) ≅ H^{1/2}(Γ)` of
Hiptmair, Pauly and Schulz (Section 4.13). The forms layer, Hilbert complexes and Picard's
theorem belong to the FEEC/BEEC library (Section 6).
Section 9 records how this division differs from the first version of this document.

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

from the project folder. `import FunctionSpaces` imports everything; single files are imported by
their module names, such as `import FunctionSpaces.Rd.Sobolev.RellichCompactness`.
Lean-FunctionSpaces uses Lean's module system (`module`, `public import`,
`@[expose] public section`), so every declaration and every definition body is public, and the
importing files need no special form.

The blueprint states every result with its proof and its Lean name:
<https://mario-ullrich.github.io/Lean-FunctionSpaces/>, as PDF
<https://mario-ullrich.github.io/Lean-FunctionSpaces/blueprint.pdf>, and the dependency graph
<https://mario-ullrich.github.io/Lean-FunctionSpaces/dep_graph_document.html>. The results of this
document on `ℝ^d` are in its chapters *Sobolev spaces on `ℝ^d`* and *Bessel potential spaces*;
the bounded Lipschitz domains, the area formula and the surface measure are in the chapter
*Lipschitz domains*, the traces in *Traces on Lipschitz domains*, and the Sobolev spaces on open
sets and on bounded Lipschitz domains, the trace space, the extension theorem, Green's formula and
the kernel of the trace in *Sobolev spaces on domains*.

## 3. Conventions (item I.0)

* **Scalars**: complex. Functions are `V → ℂ`, and `L_p` is Mathlib's `Lp ℂ p volume`.
* **Ambient space**: any finite-dimensional real inner product space `V`, with
  `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]`. For `ℝ^d` this is `EuclideanSpace ℝ (Fin d)` (the type `Fin d → ℝ` carries
  the sup norm). Mathlib's Bessel potential spaces use the same `V`, so both sides share the
  ambient type.
* **Measure**: Lebesgue measure `volume`; on a set `Ω`, `volume.restrict Ω`. On the boundary
  `Γ` of a bounded Lipschitz domain, the surface measure `Ω.surfaceMeasure`, Mathlib's
  `μHE[finrank ℝ V - 1]` restricted to `Γ` (Section 4.8).
* **Function spaces are predicates** on `Lp ℂ p volume` (for weak derivatives on open sets, on
  functions `V → ℂ`), with quasi-norms in `ℝ≥0∞` (`‖f‖ₑ`, `eLpNorm`, `triebelLizorkinNorm`). The
  Hilbert-space type on `V` is Mathlib's `BesselPotentialSpace V ℂ s 2`, notation `H^{s}(V)` or
  `H^{s, 2}(V, ℂ)` (scoped in `BesselPotentialSpace`), a complete complex inner product space;
  item I.8 below relates it to the predicates. The Hilbert-space types on open sets and on `Γ`
  are orthogonal complements and closures of subspaces of `H^{s}(V)` (Sections 4.5 and 4.6), and
  `L_2(Γ)` is `Lp ℂ 2 Ω.surfaceMeasure` (Section 4.8).
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

File `FunctionSpaces/Rd/Sobolev/SobolevTwoLittlewoodPaley.lean`.

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
smoothness (`Rd.memApprox_bandScheme_iff_modulus`), local means and atoms (chapter *Besov
spaces on `ℝ^d`* of the blueprint).

### 4.2 Weak derivatives

File `FunctionSpaces/Rd/Sobolev/WeakDerivatives.lean` (definitions, `W^m_p`) and
`FunctionSpaces/Rd/Sobolev/SobolevTwoLittlewoodPaley.lean` (`W^1_2 = H^1`).

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

TauCeti (`github.com/TauCetiProject/TauCeti`, Lean `v4.36.0-rc1` and Mathlib master as of
21 October 2026) has `W^{1,p}` spaces as submodules with total weak derivatives and, merged
between 14 and 19 October 2026, Lipschitz domains (`Set.IsLipschitzDomainWith`), a bounded
`W^{1,p}` extension operator on bounded Lipschitz domains for `1 ≤ p ≤ ∞` by reflection across
the graph (`TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`), Rellich's theorem on
bounded Lipschitz domains, `ker γ = H^1_0(Ω)` with the traces of the charts
(`W1p.exists_iInf_ker_lipschitzChartTrace_eq_of_isLipschitzDomainWith`), the area formula for
injective Lipschitz maps, and Gauss–Green on the half-space. Gauss–Green on Lipschitz domains,
the outward unit normal and one trace into `L_2(Γ)` with the surface measure are formalised here
and not there. Its toolchain differs from the pin of Section 2, so neither library can import the
other; Lean-FunctionSpaces follows its statement shapes where that costs nothing.

### 4.3 `H^1` on bounded Lipschitz domains and the extension theorem H.2 (step 2 of the proposal)

Files `FunctionSpaces/Domains/Sobolev/LipschitzDomainH1.lean`,
`FunctionSpaces/Domains/Extension/SobolevExtension.lean` (`Rd.ExtendsSobolev`),
`FunctionSpaces/Domains/Extension/SobolevExtensionOperator.lean`,
`FunctionSpaces/Domains/Extension/ReflectionExtensionOperator.lean` and
`FunctionSpaces/Domains/Sobolev/LipschitzDomainW1p.lean`;
`Ω : Rd.BoundedLipschitzDomain V` (X.1), with `Ω.carrier` the open set and
`Ω.toOpens : Opens V` the same set as an element of `Opens V`.

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
  exist and lie in `L_2(Ω)`. This direction holds by the definition through extensions; the
  converse is the extension theorem H.2 below.
* H.2, the extension theorem of Calderón and Stein for `W^{1,p}`, `1 < p < ∞`, with the bound in
  dimension `d ≥ 1` (`[Nontrivial V]`) and the weak derivatives along the orthonormal basis
  `e_i = Rd.gridBasis V i`: `Rd.BoundedLipschitzDomain.exists_extendsSobolev (hp1 : 1 < p)
  (hp : p ≠ ∞) : ∃ C, C ≠ ∞ ∧ Rd.ExtendsSobolev p Ω.toOpens Ω.carrier C`, that is, every
  `f ∈ L_p(Ω)` with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` agrees almost everywhere on `Ω`
  with some `F ∈ W^{1,p}(ℝ^d)` with weak derivatives `G_i = ∂_{e_i} F` and
  `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(Ω)} + ∑_i ‖g_i‖_{L_p(Ω)})`. The same holds for every
  `1 ≤ p ≤ ∞`, by reflection across the boundary in flattened coordinates (Evans–Gariepy,
  Section 4.4): `Rd.BoundedLipschitzDomain.exists_extendsSobolev_of_one_le (hp : 1 ≤ p) :
  ∃ C, C ≠ ∞ ∧ Rd.ExtendsSobolev p Ω.toOpens Ω.carrier C`, with `[Nontrivial V]`. For every
  `1 ≤ p ≤ ∞` the extension is a bounded linear operator on value–derivative jets, built by
  reflection (`FunctionSpaces/Rd/Sobolev/SobolevJets.lean`,
  `FunctionSpaces/Domains/Extension/ReflectionExtensionOperator.lean`):
  `Rd.BoundedLipschitzDomain.exists_extensionL : ∃ E :
  Rd.weakSobolevJet p Ω.toOpens →L[ℂ] Rd.sobolevJet p, (Rd.sobolevJet.restrictL Ω.toOpens).comp E
  = ContinuousLinearMap.id ℂ _ ∧ ∀ u, MemSobolev 1 (E u).1.1`, with `[Fact (1 ≤ p)]` and
  `[Nontrivial V]`. Here `Rd.weakSobolevJet p O` is the submodule of `L_p(O) × L_p(O)^d` of the
  pairs `(f, (g_i)_i)` with `g_i = ∂_{e_i} f` weakly on `O`, `Rd.sobolevJet p` the same on `V`,
  and `Rd.sobolevJet.restrictL O` the restriction. The chosen operator is
  `Rd.BoundedLipschitzDomain.sobolevExtensionL p`. The values of the jets of `W^{1,p}(Ω)` are
  exactly the functions of `W^{1,p}(Ω)` (`Rd.exists_mem_weakSobolevJet_of_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.memWeakSobolev_of_mem_weakSobolevJet`), and
  `Rd.exists_extensionL_of_isBoundedLipschitzDomain` is the same for the set-level definition
  `Rd.IsBoundedLipschitzDomain`. For `1 < p < ∞` Rychkov's extension gives an extension operator
  as well (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp`,
  `FunctionSpaces/Domains/Extension/SobolevExtensionOperator.lean`). The theorem is of first
  order. Membership form, for every `1 ≤ p ≤ ∞`:
  `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_of_one_le (hp : 1 ≤ p)
  (f : V → ℂ) : MemWeakSobolev Ω.toOpens 1 p f ↔ ∃ F : Lp ℂ p volume, MemSobolev 1 F ∧
  (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f`, and the direction
  `Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev_of_one_le`, in every dimension
  (for `d = 0`, `Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton`); for `1 < p < ∞` also
  `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev (hp1) (hp)` and
  `Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev`.
* `H^1(Ω) = W^{1,2}(Ω)`: `Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev
  (f : Lp ℂ 2 volume) : Ω.MemSobolevOn f ↔ MemWeakSobolev Ω.toOpens 1 2 f`, and with the
  Hilbert space of Section 4.5,
  `Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_restrictL2`.
* Rellich's theorem in `W^{1,2}(Ω)` (I.6 and H.1 in the weak-derivative form, `d ≥ 1`):
  `Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`: every sequence `f_n` with
  weak derivatives `g_{n,i}` on `Ω` and `‖f_n‖_{L_2(Ω)} + ∑_i ‖g_{n,i}‖_{L_2(Ω)} ≤ M`
  (`eLpNorm` on `volume.restrict Ω.carrier`), `M ≠ ∞`, has a subsequence converging in `L_2(Ω)`.
* The quotient norm of the Hilbert space `H^1(Ω)` and the `W^{1,2}(Ω)` norm are equivalent
  (`d ≥ 1`):
  `Rd.BoundedLipschitzDomain.exists_norm_le_restrictL2` (`‖u‖ ≤ C (‖u|_Ω‖_2 + ∑_i ‖g_i‖_2)` for the
  weak derivatives `g_i ∈ L_2(Ω)` on `Ω`) and `Rd.sq_norm_restrictL2_add_sum_le` (Section 4.5).
* Norms on `Ω`: the restriction direction has constant `1`: the intrinsic quantity of `f` is at
  most `‖F‖_2 + ‖(2^k ω_r(F, 2^(-k))_2)_k‖_{ℓ_2}` for every `F` with `F = f` on `Ω`
  (`Rd.BoundedLipschitzDomain.modNormOn_le_modNorm_of_ae_eq`). The extension direction has an
  existential constant for the intrinsic moduli
  (`Rd.BoundedLipschitzDomain.exists_besov_extension_le`) and for the `W^{1,p}(Ω)` norm of the
  weak gradient (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`, Section 5).

### 4.4 The trace (H.7 at `k = 0` in qualitative form, X.3)

File `FunctionSpaces/Domains/Sobolev/LipschitzDomainH1.lean`, on top of
`FunctionSpaces/Domains/Traces/LipschitzBoundaryTrace.lean`. For a resolution of unity
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
* `Rd.BoundedLipschitzDomain.HasBoundaryTrace Ω ψ hp L σ q f g`: `f` has a finite intrinsic
  norm on `Ω` and `g` is its boundary trace; for `L = 2`, `σ = 1`, `q = 2` this says
  `f ∈ H^1(Ω)` and `g` is its boundary trace
  (`Rd.BoundedLipschitzDomain.hasBoundaryTrace_iff_memSobolevOn`), and two such `g` agree almost
  everywhere on `Γ` (`Rd.BoundedLipschitzDomain.HasBoundaryTrace.unique`).
* Every `f ∈ H^1(Ω)` has a boundary trace in `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memSobolevOn`), unique almost everywhere
  on `Γ` (`Rd.BoundedLipschitzDomain.MemSobolevOn.isBoundaryTrace_unique`), and every
  `g ∈ B^{1/2}_{2,2}(Γ)` is the boundary trace of some `f ∈ H^1(Ω)`
  (`Rd.BoundedLipschitzDomain.exists_memSobolevOn_of_memBoundaryBesov`); together
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_memSobolevOn`.
* The same holds for the weak-derivative space `W^{1,2}(Ω)` through
  `Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev` (Section 4.3): every `f ∈ L_2(V)`
  with `MemWeakSobolev Ω.toOpens 1 2 f` has a boundary trace in `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memWeakSobolev`), unique almost
  everywhere on `Γ` (`Rd.BoundedLipschitzDomain.isBoundaryTrace_unique_of_memWeakSobolev`).
* The trace bound on one Lipschitz graph domain has an existential constant
  (`Rd.LipschitzGraph.modNorm_trace_le`); the trace statements of
  `FunctionSpaces/Domains/Sobolev/LipschitzDomainH1.lean` on bounded Lipschitz domains are
  qualitative; Section 4.6 makes the trace a bounded operator on the Hilbert space `H^1(Ω)`, and
  Section 4.8 a bounded operator into `L_2(Γ)`.

### 4.5 I.6, H.1 and H.4: Rellich's theorem, the Hilbert spaces on `Ω` and their duality

Files `FunctionSpaces/Rd/Sobolev/RellichCompactness.lean` (on `H^1(V)`),
`FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean` (the Hilbert spaces on open sets) and
`FunctionSpaces/Domains/Sobolev/SobolevDuality.lean` (their duality).

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

The Hilbert spaces on an open set `Ω : Opens V`, built inside Mathlib's `H^{s}(V)`, which is
`H^{s, 2}(V, ℂ)`:

* `Rd.RestrictionSpace s Ω`: `H^s(Ω)` for every real `s`, the orthogonal complement of
  `Rd.vanishOn s Ω`, the elements whose distribution vanishes on every test function of `Ω`;
  for `s = 1` these are the `F` with `toL2 F = 0` almost everywhere on `Ω`
  (`Rd.mem_vanishOn_one_iff`). The restriction `Rd.restrictProj s Ω` is the orthogonal
  projection, of norm at most `1`, and
  `Rd.quotientEquivRestrictionSpace s Ω : (H^{s}(V) ⧸ vanishOn s Ω) ≃ₗᵢ[ℂ] RestrictionSpace s Ω`
  makes it isometric to the quotient of CWHM, §3.1.4.
* `Rd.restrictL2 Ω : RestrictionSpace 1 Ω →L[ℂ] Lp ℂ 2 (volume.restrict Ω)`, `u ↦ u|_Ω`, is
  injective (`Rd.restrictL2_injective`) with norm at most `1` (`Rd.norm_restrictL2_apply_le`).
* I.6 for the restriction space, the compactness that Assumption F of Hiptmair, Pauly and
  Schulz (HPS) asks for: `Rd.isCompactOperator_restrictL2 (hΩ : Bornology.IsBounded Ω)`, for
  every bounded open set.
* The weak gradient: every `u ∈ H^1(Ω)` lies in `W^1_2(Ω)` (`Rd.memWeakSobolev_toL2`), and for an
  orthonormal basis `(e_i)`, `‖u|_Ω‖_2² + (2π)⁻² ∑_i ‖∂_{e_i} u‖_{L_2(Ω)}² ≤ ‖u‖²`, with the weak
  derivatives on `V` (`Rd.sq_norm_restr_add_sum_le`) or on `Ω`
  (`Rd.sq_norm_restrictL2_add_sum_le`). The weight `(2π)⁻²` comes from Mathlib's normalisation
  (`⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}` and the kernel `e^{-2πi⟨x, ξ⟩}`), so for the unweighted `W^{1,2}(Ω)`
  norm the constant is `2π`.
* The bridge to the predicate of Section 4.3: for a bounded Lipschitz domain `Ω` and
  `f ∈ L_2(V)`, `Ω.MemSobolevOn f` iff `f|_Ω = restrictL2 Ω.toOpens u` for some
  `u : RestrictionSpace 1 Ω.toOpens`
  (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`, in
  `FunctionSpaces/Domains/Sobolev/LipschitzDomainH1.lean`). So the compactness above is H.1 for
  the restriction space.
* H.4 at `s = 1`: `Rd.tildeSpace s Ω` is `H̃^s(Ω)`, the closure of the test functions of `Ω` in
  `H^{s}(V)`, and `Rd.zeroBoundarySpace s Ω` is `H^s_0(Ω)`, the closure of their restrictions in
  `RestrictionSpace s Ω`. Restriction is an isometry of `H̃^1(Ω)` onto `H^1_0(Ω)` for every open
  `Ω`: `Rd.tildeEquivZeroBoundary Ω : tildeSpace 1 Ω ≃ₗᵢ[ℂ] zeroBoundarySpace 1 Ω`. Inside
  `H^{1}(V)` the two are the same subspace: `Rd.tildeSpace_one_le_orthogonal` and
  `Rd.coe_tildeEquivZeroBoundary_symm_apply` (the element of `H̃^1(Ω)` with restriction `u` is
  `u`).

Negative order and duality, for every open `Ω` and every real `s`
(`FunctionSpaces/Domains/Sobolev/SobolevDuality.lean`):

* `Rd.besselShift s : H^{s}(V) ≃ₗᵢ[ℂ] H^{-s}(V)` keeps the `L_2` function `J_s U` and is `J_{2s}`
  on distributions (`Rd.toDistr_besselShift`).
* The pairing `Rd.pairing s (W : H^{-s}(V)) (U : H^{s}(V)) : ℂ`, the `L_2` inner product of the
  `L_2` functions of `W` and `U`, conjugate-linear in `W` and linear in `U`
  (`Rd.pairing_add_left`, `Rd.pairing_smul_left`, `Rd.pairing_add_right`, `Rd.pairing_smul_right`),
  and `U ↦ [W, U]` as `Rd.pairingCLM s W : H^{s}(V) →L[ℂ] ℂ`. It is bounded by `‖W‖ ‖U‖`
  (`Rd.norm_pairing_le`), is the distribution `U(φ)` for a test function `φ` of `Ω` in the first
  slot (`Rd.pairing_ofTest_left`, and `Rd.pairing_ofTest_right` for the second slot), and is the
  `L_2` inner product `⟪ψ, U⟫` for a Schwartz function `ψ` at `s = 1` (`Rd.pairing_one_toLp`).
* `Rd.tildeEquivRestriction s Ω : tildeSpace s Ω ≃ₗᵢ[ℂ] RestrictionSpace (-s) Ω` and
  `Rd.restrictionEquivTilde s Ω : RestrictionSpace s Ω ≃ₗᵢ[ℂ] tildeSpace (-s) Ω`, both
  `U ↦ J_{2s} U`; the key fact is `Rd.mem_orthogonal_tildeSpace_iff`: `U ⊥ H̃^s(Ω)` iff `J_{2s} U`
  vanishes on `Ω`. Elements vanishing on `Ω` pair to zero with `H̃^s(Ω)`
  (`Rd.pairing_eq_zero_of_mem_vanishOn_left`, `Rd.pairing_eq_zero_of_mem_vanishOn_right`).
* The duality of CWHM, Theorem 3.3:
  `Rd.dualEquiv s Ω : StrongDual ℂ (tildeSpace s Ω) ≃ₗᵢ⋆[ℂ] RestrictionSpace (-s) Ω` with
  `ℓ U = pairing s (dualEquiv s Ω ℓ) U` (`Rd.dualEquiv_apply`), uniqueness of the representing
  element (`Rd.dualEquiv_eq_iff`), and the same value for every extension `W'` of the
  representing element to `V` (`Rd.dualEquiv_apply_of_restrictProj_eq`, hypothesis
  `restrictProj (-s) Ω W' = dualEquiv s Ω ℓ`);
  `Rd.dualRestrictionEquiv s Ω : StrongDual ℂ (RestrictionSpace s Ω) ≃ₗᵢ⋆[ℂ] tildeSpace (-s) Ω`,
  with `ℓ (restrictProj s Ω U) = pairing s (dualRestrictionEquiv s Ω ℓ) U` for every
  `U : H^{s}(V)` (`Rd.dualRestrictionEquiv_apply_restrictProj`); and
  `Rd.dualZeroBoundaryEquiv Ω`, of type
  `StrongDual ℂ (zeroBoundarySpace 1 Ω) ≃ₗᵢ⋆[ℂ] RestrictionSpace (-1) Ω`,
  `H^{-1}(Ω) = (H^1_0(Ω))^*`, where `W` is paired with `u` itself
  (`Rd.dualZeroBoundaryEquiv_apply`). Each has `_symm_apply` and `_eq_iff` lemmas.

### 4.6 The trace space `H^{1/2}(Γ)` and `H^{-1/2}(Γ)`

File `FunctionSpaces/Domains/Traces/BoundaryTraceSpace.lean`, with
`Ω.SobolevOne := Rd.RestrictionSpace 1 Ω.toOpens`, the Hilbert space `H^1(Ω)` of Section 4.5, and
boundary traces at `L = 2`, `p = q = 2`, `s = 1/2` (`Ω.boundaryTrace ψ two_ne_top 2`):

* `Rd.modNorm_two_le_norm`: for `U : H^{1, 2}(V, ℂ)`,
  `‖toL2 U‖_2 + ‖(2^k ω_2(toL2 U, 2^(-k))_2)_k‖_{ℓ_2} ≤ Rd.sobolevOneBesovConst V * ‖U‖`, an
  explicit product of three constants; `Rd.modNorm_half_one_le`: the `B^{1/2}_{2,1}` quantity is
  at most `√2` times this one; together `Rd.modNorm_half_one_le_norm`,
  `‖toL2 U‖_2 + ∑_k 2^(k/2) ω_2(toL2 U, 2^(-k))_2 ≤ √2 * Rd.sobolevOneBesovConst V * ‖U‖`.
* `Rd.BoundedLipschitzDomain.chartTrace Ω j : Ω.SobolevOne →L[ℂ] Lp ℂ 2 volume` (on the
  hyperplane of the chart `j`), `u ↦ Tr_j(ψ_j u)` with the canonical resolution of unity
  `Ω.boundaryPartition`, a fixed choice; its constant is existential
  (`Rd.BoundedLipschitzDomain.exists_enorm_trace_localize_le`).
* `Rd.BoundedLipschitzDomain.traceKer Ω`, the common kernel of the chart traces, a closed
  subspace; `Rd.BoundedLipschitzDomain.mem_traceKer_iff`: for every resolution of unity `ψ`,
  `u ∈ traceKer Ω` iff `Ω.boundaryTrace ψ two_ne_top 2 (toL2 u) =ᶠ[Ω.aeBoundary] 0`.
* `Rd.BoundedLipschitzDomain.TraceSpace Ω := (traceKer Ω)ᗮ`, the definition of the space
  `H^{1/2}(Γ)`, with `Rd.BoundedLipschitzDomain.trace Ω : Ω.SobolevOne →L[ℂ] TraceSpace Ω`, the
  orthogonal projection, and `Rd.BoundedLipschitzDomain.extend Ω : TraceSpace Ω →L[ℂ] Ω.SobolevOne`,
  the inclusion: `trace_extend` (`γ ∘ E = id`), `norm_trace_apply_le`, `norm_extend_apply`,
  `ker_trace` (the kernel of `γ` is `traceKer Ω`), `sub_extend_trace_mem`, and
  `quotientEquivTraceSpace Ω : (Ω.SobolevOne ⧸ traceKer Ω) ≃ₗᵢ[ℂ] TraceSpace Ω`, the quotient
  `H^1(Ω)/ker γ ≅ H^{1/2}(Γ)`. These operator statements hold by the definition of the trace space
  as an orthogonal complement (Mathlib's projection and quotient lemmas).
* The functions of `H^{1/2}(Γ)`, for every resolution of unity `ψ`:
  `Rd.BoundedLipschitzDomain.trace_eq_iff` (`γ u = γ u'` iff the boundary traces agree almost
  everywhere on `Γ`), `memBoundaryBesov_extend` (the boundary trace of `E t` lies in
  `B^{1/2}_{2,2}(Γ)`), `exists_traceSpace_of_memBoundaryBesov` (every `g ∈ B^{1/2}_{2,2}(Γ)` is
  the boundary trace of some `E t`), `boundaryTrace_extend_eventuallyEq_iff` (`t` is determined
  by the boundary trace of `E t`).
* The norms (file `FunctionSpaces/Domains/Traces/TraceSpaceNorm.lean`, with the quasi-norm
  `Rd.BoundedLipschitzDomain.boundaryBesovNorm Ω 2 ψ (1 / 2) 2` of `B^{1/2}_{2,2}(Γ)` by chart
  pieces from `FunctionSpaces/Domains/Traces/BoundaryBesovNorm.lean`), for every resolution of
  unity `ψ`: `Rd.BoundedLipschitzDomain.enorm_eq_iInf` (`‖t‖ₑ` is the infimum of `‖U‖ₑ` over the
  `U : H^{1, 2}(V, ℂ)` with the boundary trace of `E t`, the quotient norm, equivalent to
  McLean's norm by his Theorem 3.37),
  `Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv` (`∃ C, C ≠ ∞ ∧ ∀ t, ‖t‖ₑ ≤ C *
  boundaryBesovNorm (traceL2 t) ∧ boundaryBesovNorm (traceL2 t) ≤ C * ‖t‖ₑ`),
  `exists_traceSpace_of_memBoundaryBesov_le` (bounded preimages under the trace),
  `mem_range_traceL2_iff` (the range of `traceL2` is `B^{1/2}_{2,2}(Γ)`), and
  `traceSpaceEquivBoundaryBesovHalf Ω : TraceSpace Ω ≃L[ℂ] BoundaryBesovHalf Ω`, the isomorphism
  with the Banach space of the `g ∈ L_2(Γ)` in `B^{1/2}_{2,2}(Γ)` for `Ω.boundaryPartition`, and
  `traceRightInverse Ω : BoundaryBesovHalf Ω →L[ℂ] SobolevOne Ω`, the bounded linear right inverse
  of McLean's Theorem 3.37 (`boundaryTraceL2_traceRightInverse`:
  `boundaryTraceL2 (traceRightInverse b) = b.toL2`; `norm_traceRightInverse_le`). The constants
  are existential. On `V`, `Rd.enorm_le_modNorm_two` is the converse of
  `Rd.modNorm_two_le_norm`, with the explicit `Rd.sobolevOneInvConst V`.
  `Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv_slobodeckij` (file
  `FunctionSpaces/Domains/Traces/BoundaryGagliardo.lean`) gives the chart-free form:
  `‖t‖ₑ ^ 2` and `‖traceL2 t‖ₑ ^ 2 + boundarySlobodeckijForm 2 (1 / 2) (traceL2 t)`, with
  Gagliardo's double integral `∫_Γ ∫_Γ |g(y) - g(x)|² / |y - x|^n dσ dσ`, `n = dim V`, for the
  surface measure `σ`, are equivalent up to an existential constant, and
  `mem_range_traceL2_iff_slobodeckij` describes the range of `traceL2` by the finiteness of that
  integral.
* `H^{-1/2}(Γ)`: `Rd.BoundedLipschitzDomain.DualTraceSpace Ω := StrongDual ℂ (TraceSpace Ω)`,
  `Rd.BoundedLipschitzDomain.dualTraceEquiv Ω : DualTraceSpace Ω ≃ₗᵢ⋆[ℂ] TraceSpace Ω` (Riesz,
  `dualTraceEquiv_apply`, uniqueness `eq_dualTraceEquiv_of_forall`), and
  `Rd.BoundedLipschitzDomain.adjoint_trace`: the adjoint of `γ` is `E`.

### 4.7 The area formula for Lipschitz graphs

File `FunctionSpaces/Domains/Lipschitz/LipschitzGraphArea.lean`, for a Lipschitz graph domain
`Ω : Rd.LipschitzGraph V`, `n = dim V`, with the graph map `Ω.graphMap x' = x' + φ(x') e` over
the hyperplane `H = Ω.hyperplane = e^⊥` and Mathlib's Euclidean Hausdorff measures `μHE[k]`
(`MeasureTheory.Measure.euclideanHausdorffMeasure`), normalised to be the volume on every
`k`-dimensional subspace:

* `Rd.LipschitzGraph.gradPhi Ω x' : H`, the gradient of `φ` on `H` (Mathlib's `gradient`, `0`
  where `φ|_H` is not differentiable, which happens only on a null set:
  `ae_differentiableAt_phiH`), and `Rd.LipschitzGraph.gram Ω x' = √(1 + ‖gradPhi x'‖²)`, with
  `1 ≤ gram x' ≤ √(1 + M²)` (`one_le_gram`, `gram_le`) and `measurable_gram`.
* `Rd.LipschitzGraph.range_graphMap : Set.range Ω.graphMap = frontier Ω.domain` (in
  `FunctionSpaces/Domains/Lipschitz/GraphParametrization.lean`), and
  `measurableEmbedding_graphMap`, `graphMap_injective`, `lipschitzWith_graphMap` (constant
  `1 + M`), `antilipschitzWith_graphMap` (constant `1`).
* The area formula `Rd.LipschitzGraph.euclideanHausdorffMeasure_graphMap_image`, its measure form
  `map_graphMap_withDensity` and its integral forms `lintegral_graphMap`, for every
  `F : V → ℝ≥0∞`, measurable or not, and `integral_graphMap`, for every `F : V → ℂ`:

  ```lean
  theorem euclideanHausdorffMeasure_graphMap_image {A : Set Ω.hyperplane}
      (hA : MeasurableSet A) :
      μHE[finrank ℝ V - 1] (Ω.graphMap '' A) = ∫⁻ x' in A, ENNReal.ofReal (Ω.gram x')
  theorem map_graphMap_withDensity :
      Measure.map Ω.graphMap
          ((volume : Measure Ω.hyperplane).withDensity fun x' => ENNReal.ofReal (Ω.gram x')) =
        (μHE[finrank ℝ V - 1] : Measure V).restrict (Set.range Ω.graphMap)
  theorem lintegral_graphMap (F : V → ℝ≥0∞) :
      ∫⁻ y in Set.range Ω.graphMap, F y ∂(μHE[finrank ℝ V - 1] : Measure V) =
        ∫⁻ x', F (Ω.graphMap x') * ENNReal.ofReal (Ω.gram x')
  theorem integral_graphMap (F : V → ℂ) :
      ∫ y in Set.range Ω.graphMap, F y ∂(μHE[finrank ℝ V - 1] : Measure V) =
        ∫ x', F (Ω.graphMap x') * (Ω.gram x' : ℂ)
  ```
* `Rd.LipschitzGraph.normalAt Ω x' = (gram x')⁻¹ • (gradPhi x' - e)`, the outward unit normal at
  `Ω.graphMap x'`: `norm_normalAt` (`‖ν‖ = 1`), `inner_normalAt_e` (`⟪ν, e⟫ = -(gram x')⁻¹`),
  `inner_normalAt_neg_of_mem_cone` (`⟪ν, y⟫ < 0` on the cone of `Ω`), `measurable_normalAt`.
* General tools: `LipschitzOnWith.euclideanHausdorffMeasure_image_le`
  (`μHE[k] (f '' s) ≤ K^k μHE[k] s` for `K`-Lipschitz maps on `s`),
  `Rd.euclideanHausdorffMeasure_image_le_of_near`, and the linear
  case `Rd.LipschitzGraph.euclideanHausdorffMeasure_linearGraph_image`
  (`μHE[n-1] (S_g '' P) = √(1 + ‖g‖²) vol(P)` for `S_g x' = x' + ⟪g, x'⟫ e`, from the norm
  determinant `Rd.LipschitzGraph.normDet_linearGraph` and Mathlib's
  `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`).

### 4.8 The surface measure, `L_2(Γ)` and the trace into it

File `FunctionSpaces/Domains/Lipschitz/SurfaceMeasure.lean`, for `Ω : Rd.BoundedLipschitzDomain V`
with boundary `Γ`, boundary balls `B_j = ball (Ω.center j) (Ω.radius j)` and charts
`(Ω.graph j).graphMap` over the hyperplanes `(Ω.graph j).hyperplane`:

* `Rd.BoundedLipschitzDomain.surfaceMeasure Ω : Measure V`, defined as
  `(μHE[finrank ℝ V - 1]).restrict (frontier Ω.carrier)`, with no charts in the definition;
  `isFiniteMeasure_surfaceMeasure` (an instance), `ae_mem_frontier`,
  `surfaceMeasure_compl_frontier`.
* The chart form, from the area formula of Section 4.7: `surfaceMeasure_restrict_ball` (on `B_j`,
  `σ` is `μHE[finrank ℝ V - 1]` on the graph), `lintegral_surfaceMeasure_of_support` (for every
  `F : V → ℝ≥0∞` vanishing outside `B_j`,
  `∫⁻ y, F y ∂σ = ∫⁻ x', F (γ_j x') * ENNReal.ofReal (gram_j x')`, measurable or not),
  `lintegral_chart_eq` (two charts give the same integral for `F` vanishing outside
  `B_j ∩ B_k`), `lintegral_surfaceMeasure` (for every resolution of unity `ψ` with `ψ_j ≥ 0` on
  `Γ` and every `F`,
  `∫⁻ F dσ = ∑ j, ∫⁻ x', ofReal (ψ_j (γ_j x')) * F (γ_j x') * ofReal (gram_j x')`),
  `integral_surfaceMeasure` (for every resolution of unity `ψ`, of any sign, and every
  `σ`-integrable `f : V → ℂ`,
  `∫ f dσ = ∑ j, ∫ x', ψ.toComplex j (γ_j x') * f (γ_j x') * gram_j x'`; the single-chart form is
  `integral_surfaceMeasure_of_support`), `lintegral_surfaceMeasure_le_sum`. The canonical
  resolution of unity `Rd.BoundedLipschitzDomain.boundaryPartition` is nonnegative
  (`boundaryPartition_nonneg`, from `exists_boundaryPartition_nonneg`), so the chart formula
  applies to it.
* Null sets: `ae_surfaceMeasure_iff_aeBoundary : (∀ᵐ y ∂σ, P y) ↔ ∀ᶠ y in Ω.aeBoundary, P y`
  for every property `P`, so the chart filter of Section 4.4 is "`σ`-almost everywhere", and
  `ae_surfaceMeasure_ball_iff` chart by chart; `volume_frontier : volume (frontier Ω.carrier) = 0`.
* The boundary trace in `L_p(Γ)`: `memLp_boundaryTrace` (hypotheses of the trace theorem,
  every `1 ≤ p < ∞`), with the bound `lintegral_enorm_boundaryTrace_le`
  (`∫_Γ |Tr_Γ F|^p dσ ≤ ∑_j √(1 + M_j²) ‖Tr_j F‖_p^p`).
* `Rd.BoundedLipschitzDomain.BoundaryL2 Ω := Lp ℂ 2 Ω.surfaceMeasure`, the space `L_2(Γ)`, and
  three bounded operators into it, each given almost everywhere on `Γ` by the boundary trace of
  every resolution of unity `ψ`:
  `ambientTraceL2 Ω : H^{1, 2}(V, ℂ) →L[ℂ] BoundaryL2 Ω` (`ambientTraceL2_apply_ae`; existential
  constant, `exists_eLpNorm_boundaryTrace_toL2_le`),
  `traceL2 Ω : TraceSpace Ω →L[ℂ] BoundaryL2 Ω` (`traceL2_apply_ae`, injective:
  `traceL2_injective`), and `boundaryTraceL2 Ω : Ω.SobolevOne →L[ℂ] BoundaryL2 Ω`, equal to
  `traceL2 Ω ∘L trace Ω` (`boundaryTraceL2_apply_ae`) and to `ambientTraceL2` on `H^1(Ω)`
  (`boundaryTraceL2_eq_ambientTraceL2`), with
  `ker_boundaryTraceL2 : (boundaryTraceL2 Ω).ker = traceKer Ω`. This is H.7 at `k = 0` as an
  operator `γ : H^1(Ω) → L_2(Γ)`.
* `exists_traceL2_ae_eq`: every `g ∈ B^{1/2}_{2,2}(Γ)` is `traceL2 Ω t` for some
  `t ∈ H^{1/2}(Γ)`, `σ`-almost everywhere; hence `memLp_of_memBoundaryBesov`.
* `Rd.BoundedLipschitzDomain.normal Ω : V → V`, the outward unit normal field
  `∑_j ψ_j • ν_j ∘ P_j` with `ψ = boundaryPartition` and the chart normals of Section 4.7:
  `measurable_normal`, `norm_normal_le` (`‖ν y‖ ≤ 1` for every `y`). On every boundary ball it is
  the chart normal `σ`-almost everywhere, a unit vector `σ`-almost everywhere (Section 4.12).

### 4.9 Items X.1–X.5, X.7, X.8

* X.1, bounded Lipschitz domains: `Rd.BoundedLipschitzDomain`
  (`FunctionSpaces/Domains/Lipschitz/BoundedLipschitz.lean`).
* X.2, restriction equals intrinsic Besov space, by Rychkov's extension: for `1 ≤ p < ∞`,
  `0 < s < r`, `1 ≤ q ≤ ∞`, `Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn` and
  `Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff` (same file).
* X.3, `B^s_{p,q}(Γ)` is the trace space of `B^{s+1/p}_{p,q}(Ω)` for `0 < s < 1`:
  `Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_exists_isBoundaryTrace`
  (`FunctionSpaces/Domains/Traces/LipschitzBoundaryTrace.lean`).
* X.4, Daubechies wavelets on `ℝ`: `Daubechies.besov_iff_coeff`
  (`FunctionSpaces/Wavelets/Daubechies/Besov.lean`).
* X.5, `F^s_{p,p} = B^s_{p,p}` on `ℝ^d`: `Rd.memTriebelLizorkin_iff_memApprox`
  (`FunctionSpaces/Rd/TriebelLizorkin/TriebelLizorkin.lean`); `B^s_{2,2} = H^s` on the torus:
  `Torus.memBesov_two_two_iff` (`FunctionSpaces/Torus/Coefficients.lean`).
* X.7, Mathlib's Bessel potential spaces: `BesselPotentialSpace`, `TemperedDistribution.MemSobolev`,
  `TemperedDistribution.besselPotential`.
* X.8, Mathlib's distributions on open sets and differential forms: `Distribution` (`𝓓'(Ω, F)`),
  `extDeriv`.

### 4.10 Sobolev and Bessel potential spaces for `1 < p < ∞`

Lean-FunctionSpaces proves, for all `1 < p < ∞`, `W^m_p = F^m_{p,2}` and, for Mathlib's Bessel
potential space, `H^{s,p} ∩ L_p = F^s_{p,2}` for every real `s` and `H^{s,p} = F^s_{p,2}` for
`s ≥ 0`, and the Sobolev embeddings on `ℝ^d`
(`Rd.exists_memLp_ae_eq_of_memSobolev`, `Rd.exists_boundedContinuous_ae_eq_of_memSobolev`). Its
tools are formalised: Plancherel bounds for families of convolution kernels
(`Rd.tsum_enorm_convLp_sq_le`, `Rd.enorm_sum_convLp_sq_le`), the weak type `(1,1)` of the
analysis and synthesis operators of every Calderón–Zygmund family
(`Rd.IsCZFamily.volume_lqNorm_conv_gt_le`, `Rd.IsCZFamily.volume_enorm_sum_conv_gt_le`),
Marcinkiewicz interpolation
(`MeasureTheory.hasStrongType_of_hasWeakType_one_of_hasStrongType_two`), and the strong type
`(p,p)`, `1 < p < ∞`, of the analysis and synthesis operators of every Calderón–Zygmund family
(`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`,
`Rd.IsCZFamily.eLpNorm_sum_conv_le`) (blueprint chapters *Vector-valued singular integrals* and
*Interpolation of operators*, block documents [Triebel–Lizorkin spaces](TriebelLizorkin.md) and
[Tools from analysis](Analysis.md)).

The square function theorem `L_p = F^0_{p,2}` on `ℝ^d`, `d = dim V ≥ 1`, `1 < p < ∞`, is
formalised as the two-sided bound of `‖f‖_{F^0_{p,2}}` (by definition the `L_p` norm of the
square function) in terms of `‖f‖_p`, with named constants (formulas in Schwartz seminorms of
fixed kernels, proved finite) in both directions
(`Rd.triebelLizorkinNorm_zero_two_le`, `Rd.enorm_le_triebelLizorkinNorm_zero_two`,
`Rd.triebelLizorkinSpace_zero_two_eq_top`), and so is `W^m_p = F^m_{p,2}` for `1 < p < ∞`
(`Rd.memSobolev_iff_memTriebelLizorkin`), with named constants of the same kind
(`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv`,
`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin`) and, for `m ≥ 1`, the Besov sandwich
`B^m_{p,min(p,2)} ⊆ W^m_p ⊆ B^m_{p,max(p,2)}` (`Rd.memSobolev_of_memApprox`,
`Rd.memApprox_of_memSobolev`). The identity `H^{s,p} = F^s_{p,2}` for Mathlib's
Bessel potential space, `1 < p < ∞`, is formalised with existential constants, on `L_p` for every
real `s` and on all tempered distributions for `s ≥ 0`
(`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`,
`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`,
`Rd.memTriebelLizorkin_iff_memSobolev_bessel`), and with it `W^m_p = H^{m,p}`
(`Rd.memSobolev_iff_memSobolev_bessel`). These results generalise Sections 4.1 and 4.2 from
`p = 2`, whose statements carry explicit constants.

### 4.11 Green's formula on Lipschitz graph domains

File `FunctionSpaces/Domains/Sobolev/LipschitzGraphGreen.lean` (the trace operator in
`FunctionSpaces/Domains/Traces/BoundaryTraceSpace.lean`), for a Lipschitz graph domain
`Ω : Rd.LipschitzGraph V`, `n = dim V`, with the notation of Section 4.7 and the normal weight
`Rd.LipschitzGraph.normalWeight Ω v x' = ⟪gradPhi x', v⟫ - ⟪v, e⟫`, which is
`⟪v, normalAt x'⟫ * gram x'` (`inner_normalAt_mul_gram`) and bounded by `(M + 1) ‖v‖`
(`abs_normalWeight_le`):

* Gauss–Green for `C^1` functions with compact support, in chart form and in surface form, with
  the corollaries `setIntegral_lineDeriv_eq_normal`, `setIntegral_lineDeriv_e` and
  `setIntegral_lineDeriv_hyperplane`, and Fubini in product coordinates
  (`setIntegral_domain_eq`, `setIntegral_domain_eq_graphMap`):

  ```lean
  theorem setIntegral_lineDeriv_eq (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : V) :
      ∫ x in Ω.domain, lineDeriv ℝ g x v = ∫ x', g (Ω.graphMap x') * Ω.normalWeight v x'
  theorem setIntegral_lineDeriv_eq_surface (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
      (v : V) :
      ∫ x in Ω.domain, lineDeriv ℝ g x v = ∫ y in range Ω.graphMap,
        g y * (inner ℝ v (Ω.normalAt (Ω.proj y)) : ℂ) ∂(μHE[finrank ℝ V - 1] : Measure V)
  ```
* The trace of `H^1(ℝ^d)` on the graph as an operator,
  `Rd.LipschitzGraph.traceH1 Ω : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure Ω.hyperplane)`,
  with `traceH1 U = Ω.trace two_ne_top 2 (toL2 U)` (`traceH1_apply`) and `w ∘ γ` for Schwartz
  functions `w` (`traceH1_ofSchwartz_ae`).
* Green's formula, for `W^1_2(ℝ^d)` functions with their weak derivatives and the traces of the
  trace theorem; for elements of `H^{1, 2}(V, ℂ)` with `Rd.weakDerivL2` it is
  `Rd.LipschitzGraph.setIntegral_green_besselPotentialSpace`, in surface form
  `Rd.LipschitzGraph.setIntegral_green_surface`
  (`∫_{range γ} Tr U (P y) * Tr W (P y) * ⟪v, ν (P y)⟫ ∂μHE[n-1]`):

  ```lean
  theorem setIntegral_green (f g : Lp ℂ 2 (volume : Measure V)) (hf : MemSobolev 1 f)
      (hg : MemSobolev 1 g) (v : V) {fv gv : Lp ℂ 2 (volume : Measure V)}
      (hfv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) f fv)
      (hgv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) g gv) :
      ∫ x in Ω.domain, fv x * g x + f x * gv x =
        ∫ x', Ω.trace two_ne_top 2 f x' * Ω.trace two_ne_top 2 g x' *
          (Ω.normalWeight v x' : ℂ)
  ```
* General tools (`FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean`): the weak
  derivative `Rd.weakDerivL2 v : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 volume`, of norm at most `2π ‖v‖`
  (`norm_weakDerivL2_le`, `hasWeakLineDeriv_weakDerivL2`, `weakDerivL2_eq`); the Schwartz functions
  in every `H^s(V)`, `Rd.ofSchwartz s : 𝓢(V, ℂ) →L[ℂ] H^{s, 2}(V, ℂ)`, dense
  (`Rd.denseRange_ofSchwartz`), also with compact support (`Rd.dense_ofSchwartz_hasCompactSupport`),
  so `Rd.tildeSpace_top : tildeSpace s ⊤ = ⊤`.

### 4.12 Green's formula on bounded Lipschitz domains

File `FunctionSpaces/Domains/Sobolev/LipschitzDomainGreen.lean`, namespace
`Rd.BoundedLipschitzDomain`, for `Ω : Rd.BoundedLipschitzDomain V` with the notation of Sections
4.6–4.8 and 4.11:

* Green's formula with the surface measure and the outward unit normal (Grisvard, Theorem 1.5.3.1),
  for elements of `H^{1, 2}(V, ℂ)` with the trace `ambientTraceL2` and for `H^1(Ω)` with
  `boundaryTraceL2`:

  ```lean
  theorem setIntegral_green_surface (U W : H^{1, 2}(V, ℂ)) (v : V) :
      ∫ x in Ω.carrier, weakDerivL2 v U x * toL2 W x + toL2 U x * weakDerivL2 v W x =
        ∫ y, Ω.ambientTraceL2 U y * Ω.ambientTraceL2 W y * (inner ℝ v (Ω.normal y) : ℂ)
          ∂Ω.surfaceMeasure
  theorem setIntegral_green_sobolevOne (u w : Ω.SobolevOne) (v : V) :
      ∫ x in Ω.carrier, weakDerivL2 v (u : H^{1, 2}(V, ℂ)) x * toL2 (w : H^{1, 2}(V, ℂ)) x +
          toL2 (u : H^{1, 2}(V, ℂ)) x * weakDerivL2 v (w : H^{1, 2}(V, ℂ)) x =
        ∫ y, Ω.boundaryTraceL2 u y * Ω.boundaryTraceL2 w y * (inner ℝ v (Ω.normal y) : ℂ)
          ∂Ω.surfaceMeasure
  ```

  For a FEEC user holding weak derivatives `u_v`, `w_v` on `Ω` itself
  (`HasWeakLineDeriv Ω.toOpens (fun _ : Fin 1 => v) (toL2 (u : H^{1, 2}(V, ℂ))) uv`, and likewise
  for `w`), `setIntegral_green_sobolevOne_of_hasWeakLineDeriv` gives
  `∫ x in Ω.carrier, uv x * toL2 (w : H^{1, 2}(V, ℂ)) x + toL2 (u : H^{1, 2}(V, ℂ)) x * wv x`
  equal to the same boundary integral.
* The chart form, for every resolution of unity `ψ : Ω.BoundaryPartition` of any sign, for
  `W^1_2(ℝ^d)` functions with their weak derivatives and the traces of the graph domains
  (`Rd.BoundedLipschitzDomain.setIntegral_green_besselPotentialSpace` for elements of
  `H^{1, 2}(V, ℂ)` with `Rd.LipschitzGraph.traceH1`):

  ```lean
  theorem setIntegral_green (ψ : Ω.BoundaryPartition) (f g : Lp ℂ 2 (volume : Measure V))
      (hf : MemSobolev 1 f) (hg : MemSobolev 1 g) (v : V) {fv gv : Lp ℂ 2 (volume : Measure V)}
      (hfv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) f fv)
      (hgv : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) g gv) :
      ∫ x in Ω.carrier, fv x * g x + f x * gv x =
        ∑ j, ∫ x', ψ.toComplex j ((Ω.graph j).graphMap x') *
          (Ω.graph j).trace two_ne_top 2 f x' * (Ω.graph j).trace two_ne_top 2 g x' *
            ((Ω.graph j).normalWeight v x' : ℂ)
  ```
* The unit normal: `normal_ae_eq_normalAt (j) : ∀ᵐ y ∂Ω.surfaceMeasure, y ∈ ball (Ω.center j)
  (Ω.radius j) → Ω.normal y = (Ω.graph j).normalAt ((Ω.graph j).proj y)`, `norm_normal_ae`
  (`‖ν‖ = 1` `σ`-almost everywhere) and `inner_normal_neg_ae` (`⟪ν, w⟫ < 0` for `w` in the cone
  of the chart).
* The zero extension, the bounded Lipschitz domain form of TauCeti's half-space statement
  `TauCeti.W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTrace_eq_zero`, with the weak
  derivatives `1_Ω ∂_v u` (`hasWeakLineDeriv_indicatorLp_of_mem_traceKer`):

  ```lean
  theorem memSobolev_indicatorLp_iff_mem_traceKer (u : Ω.SobolevOne) :
      MemSobolev 1 (indicatorLp Ω.measurableSet (toL2 (u : H^{1, 2}(V, ℂ)))) ↔ u ∈ Ω.traceKer
  ```
* General tools: integration by parts in `H^1(ℝ^d)`, `Rd.integral_weakDeriv_mul_add_eq_zero`,
  and for `W^1_2(ℝ^d)` functions, `Rd.integral_mul_add_eq_zero_of_hasWeakLineDeriv`;
  smooth resolutions of unity equal to one near a compact set, `Rd.exists_smooth_partition_nhds`
  (`FunctionSpaces/Domains/Lipschitz/BoundedLipschitz.lean`), and `exists_boundaryPartition_nhds`
  (`FunctionSpaces/Domains/Traces/LipschitzBoundaryTrace.lean`); the graph
  domain below a graph, `Rd.LipschitzGraph.lower`, with the traces from both sides of the graph
  equal (`Rd.LipschitzGraph.traceH1_ae_eq_traceH1_lower`).

### 4.13 The kernel of the trace (H.7 at `k = 0`, the HPS quotient)

File `FunctionSpaces/Domains/Traces/TraceKernel.lean`, namespace `Rd.BoundedLipschitzDomain`, for
`Ω : Rd.BoundedLipschitzDomain V` with the notation of Sections 4.5 and 4.6:

* `ker γ = H^1_0(Ω)` (McLean, Theorem 3.40; HPS cite it in this form); the trace kernel is the
  common kernel of the chart traces, `⨅ j, (Ω.chartTrace j).ker`, the shape of TauCeti's
  `W1p.exists_iInf_ker_lipschitzChartTrace_eq_of_isLipschitzDomainWith`:

  ```lean
  theorem traceKer_eq_zeroBoundarySpace : Ω.traceKer = Rd.zeroBoundarySpace 1 Ω.toOpens
  ```
* The HPS quotient, the trace space of Hiptmair, Pauly and Schulz for `k = 0`, with the class of
  `u` going to `γ u` (`quotientZeroBoundaryEquivTraceSpace_mk`):

  ```lean
  noncomputable def quotientZeroBoundaryEquivTraceSpace :
      (Ω.SobolevOne ⧸ Rd.zeroBoundarySpace 1 Ω.toOpens) ≃ₗᵢ[ℂ] Ω.TraceSpace
  ```
* `H̃^1(Ω) ≅ ker γ` by restriction (`tildeEquivTraceKer : Rd.tildeSpace 1 Ω.toOpens ≃ₗᵢ[ℂ]
  Ω.traceKer`), and the dual of the trace kernel as `H^{-1}(Ω)`
  (`dualTraceKerEquiv : StrongDual ℂ Ω.traceKer ≃ₗᵢ⋆[ℂ] Rd.RestrictionSpace (-1) Ω.toOpens`, with
  `dualTraceKerEquiv_apply : ℓ u = Rd.pairing 1 (Ω.dualTraceKerEquiv ℓ) u` and the uniqueness
  `dualTraceKerEquiv_eq_iff`).
* `H̃^1(Ω)` by supports: `mem_tildeSpace_iff (U : H^{1, 2}(V, ℂ)) : U ∈ Rd.tildeSpace 1 Ω.toOpens ↔
  ∀ᵐ x ∂volume, x ∉ Ω.carrier → toL2 U x = 0`; the direction `⇒` holds for every open set
  (`Rd.toL2_ae_eq_zero_of_mem_tildeSpace`).
* General tools: weak derivatives commute with convolution by Schwartz functions in every `L_p`,
  `1 ≤ p < ∞` (`Rd.hasWeakLineDeriv_convLp`, file
  `FunctionSpaces/Rd/SingularIntegrals/ConvolutionAdjoint.lean`); mollification converges in
  `H^1(ℝ^d)` (`Rd.tendsto_of_toL2_eq_convLp`); every element of `H^1(ℝ^d)` vanishing outside a
  compact subset of an open set `Ω` lies in `H̃^1(Ω)` (`Rd.mem_tildeSpace_of_isCompact`).

## 5. Decisions and reasons

* **Constants on `Ω` are existential.** The extension theorem for bounded Lipschitz domains
  (Rychkov's extension, assembled with a resolution of unity) and the trace theorem carry
  existential constants, so the bounds on `Ω` are statements `∃ C, C ≠ ∞ ∧ …`: the extension
  bound for `W^{1,p}` (Section 4.3) and the norm equivalence of `H^{1/2}(Γ)` with
  `B^{1/2}_{2,2}(Γ)` by chart pieces (Section 4.6). The norm statements on `Ω` with constant `1`
  are the restriction bound, and on the trace space the trace, the extension and the quotient
  isometry `H^1(Ω)/ker γ ≅ H^{1/2}(Γ)` (Section 4.6), which hold by the definition of
  `H^{1/2}(Γ)` as the orthogonal complement of the trace kernel. The trace into `L_2(Γ)` has an
  existential constant (Section 4.8). Norm equivalences with explicit constants hold on `V`
  (Sections 4.1, 4.2 and 4.6).
* **`H^s(Ω)` is the restriction space**, the definition of Chandler-Wilde, Hewett and Moiola (the
  proposal cites their §3.1.4). Rellich's theorem then holds on every bounded set. Every function
  of `H^1(Ω)` lies in the weak-derivative space `W^1_2(Ω)`, on every open set
  (`Rd.memWeakSobolev_toL2`). On bounded Lipschitz
  domains the two spaces agree by the extension theorem for `W^{1,2}` of Calderón and Stein
  (Stein 1970, Chapter VI, §3), formalised here for every `W^{1,p}`, `1 ≤ p ≤ ∞`
  (Section 4.3); on some
  bounded open sets they differ (a slit disc), and the embedding `W^1_2(Ω) ↪ L_2(Ω)` can fail to
  be compact (the rooms-and-passages domains, Adams and Fournier, Chapter 6). This splits H.1
  and I.6: the restriction version is formalised for every bounded set, and the weak-derivative
  version on Lipschitz domains follows from it together with the extension theorem
  (`Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`, Section 4.3).
* **`B^s_{p,q}(Γ)` is defined chart by chart**, with Lebesgue measure on the hyperplanes of the
  charts, and "almost everywhere on `Γ`" is the chart filter `aeBoundary`, whose exceptional sets
  are exactly the null sets of the surface measure
  (`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_iff_aeBoundary`).
* **The surface measure is Mathlib's Hausdorff measure** `μHE[d-1]` restricted to `Γ`, defined
  without charts and normalised to be the volume on hyperplanes. The area formula for Lipschitz
  graphs (Section 4.7) gives its chart form with the Gram density `√(1 + ‖∇φ_j‖²)`, so the
  integrals of two charts agree on their overlap, both being integrals over `Γ`
  (`Rd.BoundedLipschitzDomain.lintegral_chart_eq`); a resolution of unity enters only the chart
  formula for whole integrals, with nonnegative `ψ_j`.
* **Predicates plus Hilbert-space types.** The spaces of Lean-FunctionSpaces are predicates on
  `Lp ℂ p volume`; the Hilbert-space type on `V` is Mathlib's `H^{s, 2}(V, ℂ)`, tied to the
  predicates by I.8 and `Rd.toL2`. The Hilbert spaces on open sets are closed subspaces of
  `H^{s, 2}(V, ℂ)`, orthogonal complements and closures (Section 4.5), and the trace space is the
  orthogonal complement of the trace kernel in `H^1(Ω)` (Section 4.6), so Mathlib's Hilbert-space
  theory (projections, duals, compact operators) applies to them directly; the quotient of CWHM
  and the quotient `H^1(Ω)/ker γ` are isometric copies.
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

The FEEC/BEEC library builds:

* The forms layer: `L^2Λ^k`, the weak exterior derivative `d`, `HΛ^k`, regular decompositions,
  and `H^{-1/2}(curl_Γ, Γ)`.
* Picard's theorem from I.6, and the s-number track together with Lean-SNumbers.

Of the interface items, I.4 on `ℝ^d` (tensor-product Daubechies wavelets) is a later goal of
Lean-FunctionSpaces (Section 7, answer 2); the other items are formalised here (Section 4), and
the FEEC/BEEC library builds the layers above on them.

## 7. Answers to the seven questions

1. **Field (I.0).** Option (d): the abstract layers over `RCLike 𝕜` (Lean-SNumbers already works
   this way; Lax–Milgram over `RCLike` is a short addition to Mathlib's real `IsCoercive` version
   through `InnerProductSpace.toDual`), the function spaces complex as in Mathlib's `H^{s,p}` and
   here, and a transfer lemma to the closed real subspace of real-valued functions where real
   Hilbert spaces are wanted.
2. **Shapes.** I.8 is `Rd.memSobolev_two_iff_exists_memApprox` (Section 4.1). I.6 is
   `Rd.isCompactOperator_restr_toL2` for the restriction space, and
   `Rd.isCompactOperator_restrictL2` for its Hilbert space `H^1(Ω)` (Section 4.5). I.4 is the `ℝ^d`
   version of `Daubechies.besov_iff_coeff`, with tensor-product wavelets on
   `EuclideanSpace ℝ (Fin d)`; it is on the list of later goals of Lean-FunctionSpaces.
3. **I.8.** Yes, it is formalised for `p = 2` (Section 4.1), and for all `1 < p < ∞` with
   existential constants: `H^{s,p} ∩ L_p = F^s_{p,2}` for every real `s`
   (`Rd.memTriebelLizorkin_iff_memSobolev_bessel`) and `H^{s,p} = F^s_{p,2}` for `s ≥ 0`
   (`Rd.exists_memTriebelLizorkin_of_besselPotential_eq`, Section 4.10).
4. **Rellich on bounded Lipschitz domains.** Yes for the restriction space, on every bounded set,
   as the compact operator `H^1(Ω) → L_2(Ω)` (Section 4.5), and for the weak-derivative space
   on bounded Lipschitz domains through the extension theorem
   (`Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`, Section 4.3).
5. **Vector values.** Scalar in Lean-FunctionSpaces; on `V` Mathlib's `H^{s,p}(V, F)` takes vector
   values directly, and on `Ω` and `Γ` the FEEC/BEEC library works with `Fin m → ℂ`-valued
   functions and componentwise lemmas.
6. **Space types and surface measure.** Predicates and Mathlib's type on `V` here, the Hilbert
   spaces `H^s(Ω)`, `H̃^s(Ω)` and `H^s_0(Ω)` on open sets (Section 4.5), the trace space
   `H^{1/2}(Γ)` and its dual `H^{-1/2}(Γ)` (Section 4.6), the surface measure `μHE[d-1]` on
   `Γ` with `L_2(Γ)` and the trace into it (Section 4.8), and `H^1_0(Ω) = ker γ` with the quotient
   `H^1(Ω)/H^1_0(Ω) ≅ H^{1/2}(Γ)` (Section 4.13).
7. **Split and versions.** The split Lean-SNumbers / Lean-FunctionSpaces / FEEC/BEEC library is
   right. Lean-FunctionSpaces pins Lean and Mathlib `v4.35.0-rc2`, and the FEEC/BEEC library
   takes the same pin. Lean-SNumbers is on the stable release `v4.35.0`; Lean-FunctionSpaces moves
   to it later, and the FEEC/BEEC library follows.

## 8. Versioning

The Lean declarations cited here are those of the commit of `main` that adds the bounded linear
extension operator (`Rd.BoundedLipschitzDomain.exists_extensionL`), and the norms of Section 4.6
those of the commit that adds `Rd.BoundedLipschitzDomain.exists_traceL2_norm_equiv`; later commits
keep them unless this document says otherwise, and the commit that changes an interface name
updates this document.
The module paths are those of the folder layout by setting (Section 9): declaration names do not
depend on folders, so a downstream file changes only its `import` lines. Pin `rev` to that commit
or a later one. Missing lemmas and wishes for other statement shapes go to the issue tracker of
the GitHub repository, with the item number of the proposal and the intended Lean statement.

## 9. Changes to the original plan (14 October 2026)

The first version of this document (commit `ec3c133`) left items 1–5 of its Section 6 to the
FEEC/BEEC library. Lean-FunctionSpaces now builds them itself, in its current part (Part Ib of
its development plan). The space types, the isometry of H.4 and the duality are formalised,
with their Lean names in Section 4.5, the trace space, with its Lean names in Section 4.6, the
area formula for Lipschitz graphs, with its Lean names in Section 4.7, and the surface measure
with `L_2(Γ)` and the trace into it, with their Lean names in Section 4.8, and the extension
theorem H.2, with its Lean names in Section 4.3, Green's formula, with its Lean names in
Section 4.12, and `ker γ = H^1_0(Ω)`, with its Lean names in Section 4.13.

* **Space types (formalised, Section 4.5).** `H^s(Ω)` for every open `Ω` and every real `s` as a
  Hilbert space: the orthogonal complement, in Mathlib's `H^{s}(ℝ^d)`, of the elements that
  vanish on `Ω` (`Rd.RestrictionSpace`, with the restriction `Rd.restrictProj`), isometric to
  the quotient of CWHM, §3.1.4 (`Rd.quotientEquivRestrictionSpace`); `H̃^s(Ω)` as the closure of
  the test functions of `Ω` in `H^s(ℝ^d)` (`Rd.tildeSpace`), `H^s_0(Ω)` as their closure in
  `H^s(Ω)` (`Rd.zeroBoundarySpace`); the restriction to `L_2(Ω)` as a bounded injective
  operator (`Rd.restrictL2`), compact for bounded `Ω` (Rellich in operator form, HPS
  Assumption F, `Rd.isCompactOperator_restrictL2`). File
  `FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean`. The bridge to the predicate on
  bounded Lipschitz domains (`Rd.BoundedLipschitzDomain.memSobolevOn_iff_exists_restrictL2`) is in
  `FunctionSpaces/Domains/Sobolev/LipschitzDomainH1.lean`.
* **H.4 and duality (formalised, Section 4.5).** `H̃^1(Ω) ≅ H^1_0(Ω)` isometrically for every
  open `Ω` (`Rd.tildeEquivZeroBoundary`); for every real `s` the duality
  `(H̃^s(Ω))^* ≅ H^{-s}(Ω)` and `(H^s(Ω))^* ≅ H̃^{-s}(Ω)` with the pairing of `H^{-s}(ℝ^d)` and
  `H^s(ℝ^d)` (CWHM, Theorem 3.3; `Rd.dualEquiv`, `Rd.dualRestrictionEquiv`), and
  `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` (`Rd.dualZeroBoundaryEquiv`). File
  `FunctionSpaces/Domains/Sobolev/SobolevDuality.lean`.
* **The trace space (formalised, Section 4.6).** `H^{1/2}(Γ)` defined as the orthogonal complement
  of the kernel of the trace in `H^1(Ω)` (`Rd.BoundedLipschitzDomain.TraceSpace`), with the trace as
  orthogonal projection and the extension as inclusion (both of norm at most one;
  `Rd.BoundedLipschitzDomain.trace`, `Rd.BoundedLipschitzDomain.extend`),
  `H^1(Ω)/ker γ ≅ H^{1/2}(Γ)` (`Rd.BoundedLipschitzDomain.quotientEquivTraceSpace`), and
  `H^{-1/2}(Γ)` as its dual (`Rd.BoundedLipschitzDomain.DualTraceSpace`). File
  `FunctionSpaces/Domains/Traces/BoundaryTraceSpace.lean`.
* **The surface measure (formalised, Sections 4.7 and 4.8).** Mathlib's Hausdorff measure `μHE[d-1]`
  restricted to `Γ`, with no charts in the definition (`Rd.BoundedLipschitzDomain.surfaceMeasure`).
  The area formula for Lipschitz graphs
  (`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphMap_image`,
  `Rd.LipschitzGraph.lintegral_graphMap`, file
  `FunctionSpaces/Domains/Lipschitz/LipschitzGraphArea.lean`) expresses its integrals in the charts
  with the Gram density `√(1 + ‖∇φ‖²)` (`Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure`);
  `L_2(Γ)` is the `L_2` space of this measure (`Rd.BoundedLipschitzDomain.BoundaryL2`), the trace is
  an injective bounded operator `H^{1/2}(Γ) → L_2(Γ)` (`Rd.BoundedLipschitzDomain.traceL2`), and
  `γ : H^1(Ω) → L_2(Γ)` has the trace kernel as its kernel
  (`Rd.BoundedLipschitzDomain.ker_boundaryTraceL2`). The outward unit normal is
  `Rd.LipschitzGraph.normalAt` on a graph domain and `Rd.BoundedLipschitzDomain.normal` on a bounded
  Lipschitz domain. File `FunctionSpaces/Domains/Lipschitz/SurfaceMeasure.lean`.
* **Green's formula (formalised, Section 4.12)** on bounded Lipschitz domains for `H^1`
  functions, in chart form and with the surface measure and the outward unit normal
  (`Rd.BoundedLipschitzDomain.setIntegral_green_sobolevOne`), with the unit normal as the chart
  normal almost everywhere (`Rd.BoundedLipschitzDomain.normal_ae_eq_normalAt`) and the zero
  extension of functions with vanishing trace
  (`Rd.BoundedLipschitzDomain.memSobolev_indicatorLp_iff_mem_traceKer`). File
  `FunctionSpaces/Domains/Sobolev/LipschitzDomainGreen.lean`.
* **`ker γ = H^1_0(Ω)` (formalised, Section 4.13)** (McLean, Theorem 3.40;
  `Rd.BoundedLipschitzDomain.traceKer_eq_zeroBoundarySpace`) and the HPS quotient
  `H^1(Ω)/H^1_0(Ω) ≅ H^{1/2}(Γ)`
  (`Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`). File
  `FunctionSpaces/Domains/Traces/TraceKernel.lean`.
* **The extension theorem H.2 (formalised, Section 4.3)** for `W^{1,2}` on bounded Lipschitz domains
  (the restriction space equals the weak-derivative space), by the extension by reflection. With
  it the trace statements hold for the weak-derivative space
  (`Rd.BoundedLipschitzDomain.exists_isBoundaryTrace_of_memWeakSobolev`,
  `Rd.BoundedLipschitzDomain.isBoundaryTrace_unique_of_memWeakSobolev`), and Rychkov's extension
  operator with local means of the gradient gives Rellich's theorem in the weak-derivative form
  (`Rd.BoundedLipschitzDomain.exists_subseq_tendsto_of_memWeakSobolev`). Files
  `FunctionSpaces/Domains/Extension/DivergenceKernels.lean`,
  `FunctionSpaces/Domains/Extension/SobolevExtension.lean`,
  `FunctionSpaces/Domains/Extension/SobolevExtensionOperator.lean`,
  `FunctionSpaces/Domains/Extension/ReflectionExtensionOperator.lean` and
  `FunctionSpaces/Domains/Sobolev/LipschitzDomainW1p.lean`. **Extended (decision of 21 October
  2026):** H.2 is stated for every `1 < p < ∞`, every function of `W^{1,p}(Ω)` is the restriction of
  a function of `W^{1,p}(ℝ^d)`, through the `L_p` bounds of the part on `L_p` Sobolev spaces;
  Rellich in the weak-derivative form and the equivalence of the quotient norm of `H^1(Ω)` with the
  `W^{1,2}(Ω)` norm stay at `p = 2`. The local means of the gradient come from writing the
  difference of two dilates of a bump as a divergence, `d/dt (m_t) = t⁻¹ div(x m_t)`, which works
  for every bump of the construction.
* **Order (decision of 14 October 2026).** These three statements follow the part on `L_p`
  Sobolev spaces of Section 4.10. The square-function estimate in the proof of H.2, the bound
  `∑_j ‖K_j ⋆ g‖_2² ≤ B ‖g‖_2²` for a family of integrable kernels whose Fourier transforms
  satisfy `∑_j |𝓕K_j(ξ)|² ≤ B`, is formalised there (`Rd.tsum_enorm_convLp_sq_le`, file
  `FunctionSpaces/Rd/SingularIntegrals/PlancherelBounds.lean`).

The FEEC/BEEC library keeps the forms layer (`L^2Λ^k`, weak `d`, `HΛ^k`, regular
decompositions, `H^{-1/2}(curl_Γ, Γ)`), Picard's theorem and the s-number track.

The formalisation of the space types and of the duality settled the following points of the plan.

* **`H^s(Ω)` is the orthogonal complement** of the elements vanishing on `Ω`, a closed subspace
  of `H^{s}(ℝ^d)`; the quotient of CWHM enters as the isometry
  `Rd.quotientEquivRestrictionSpace`, and the norm of `H^s(Ω)` is the minimal norm of an
  extension (`Rd.norm_restrictProj_le_of_mem`, `Rd.exists_norm_restrictProj_eq`).
* **The `W^{1,2}(Ω)` bound carries Mathlib's normalisation**: the bound "with constant `1`" of
  the plan is `‖u|_Ω‖_2² + (2π)⁻² ∑_i ‖∂_{e_i} u‖_{L_2(Ω)}² ≤ ‖u‖²`
  (`Rd.sq_norm_restr_add_sum_le`); for the unweighted `W^{1,2}(Ω)` norm the constant is `2π`.
  Two statements extend the plan: `Rd.memWeakSobolev_toL2` (every `u ∈ H^1(Ω)` lies in
  `W^1_2(Ω)`) and `Rd.sq_norm_restrictL2_add_sum_le` (the bound with weak derivatives on `Ω`).
* **The isometry `H̃^1(Ω) ≅ H^1_0(Ω)`** rests on the weak-gradient form of the `H^1(ℝ^d)` norm
  (`Rd.sq_norm_eq_of_hasWeakLineDeriv`) and on disjoint supports
  (`Rd.norm_le_norm_add_of_ae_eq_zero`, for every `L_p` space). Two lemmas on the span of the test
  functions carry it: its elements are Schwartz functions supported in `Ω`
  (`Rd.exists_schwartz_of_mem_testSpan`) and vanish near `ℝ^d \ Ω`
  (`Rd.exists_opens_toL2_ae_eq_zero`). Weak derivatives of every order of an element vanishing on
  `Ω` vanish on `Ω` (`Rd.weakDeriv_ae_zero_of_mem_vanishOn`, from the locality lemma
  `Rd.HasWeakLineDeriv.ae_eq_zero_of_ae_eq_zero` of
  `FunctionSpaces/Rd/Sobolev/WeakDerivatives.lean`). The literature reference is McLean, Theorem
  3.33 (`H̃^s(Ω) = H^s_0(Ω)` on Lipschitz domains for `s ≥ 0` with `s - 1/2 ∉ ℤ`, up to equivalence
  of norms), in place of CWHM, Lemma 3.31.
* **The duality** settled these points. The pairing `Rd.pairing` is sesquilinear,
  conjugate-linear in the element of `H^{-s}(ℝ^d)`, the convention of Mathlib's inner products
  and of its Riesz map `InnerProductSpace.toDual`, so the duality isomorphisms are
  conjugate-linear isometries (`≃ₗᵢ⋆[ℂ]`). The orthogonal complement of `H̃^t(Ω)` is computed
  once, for an isometry `e : H^t(ℝ^d) → H^{t'}(ℝ^d)` that acts as `J_{2t}` on distributions
  (`Rd.orthogonal_tildeSpace_eq_comap`, `Rd.map_tildeSpace_eq_orthogonal`); this hypothesis
  determines `e`, which exists only for `t' = -t`, and `t'` is free so that the lemmas apply to
  both `Rd.besselShift s` and its inverse. This gives `H̃^s(Ω) ≅ H^{-s}(Ω)` and, beyond the
  plan, `H^s(Ω) ≅ H̃^{-s}(Ω)` (`Rd.restrictionEquivTilde`). The conjugation lemma of the plan
  holds for every real-valued Schwartz function: its Bessel potential `J_t`
  (`Rd.besselSchwartz`) is real (`Rd.conj_besselSchwartz_apply`), from
  `conj (𝓕 f) = 𝓕⁻(conj f)` on `ℝ^d` (`Rd.conj_fourier_apply`). Mathlib defines the inner product
  of `H^{s}(ℝ^d)` as `⟪J_s U, J_s W⟫_{L_2}`, with the definition visible only inside its module;
  `Rd.inner_toLp_toLp` states it as `⟪U, W⟫ = ⟪J_s U, J_s W⟫_{L_2}`. Additions to the plan: the
  pairing extends distributions in both slots (`Rd.pairing_ofTest_left`,
  `Rd.pairing_ofTest_right`), the representing element is unique (`Rd.dualEquiv_eq_iff`), every
  extension of it to `ℝ^d` gives the same pairing (`Rd.dualEquiv_apply_of_restrictProj_eq`,
  `Rd.dualRestrictionEquiv_apply_restrictProj`), and `H̃^1(Ω)` and `H^1_0(Ω)` are the same
  subspace of `H^1(ℝ^d)` (`Rd.coe_tildeEquivZeroBoundary_symm_apply`), so the dual of
  `H^1_0(Ω)` pairs `W` with `u` itself (`Rd.dualZeroBoundaryEquiv_apply`).
* **Names**: `H^s_0(Ω)` is the submodule `Rd.zeroBoundarySpace`, in lower case like the other
  submodules `Rd.vanishOn`, `Rd.testSpan` and `Rd.tildeSpace`; the quotient isometry is
  `Rd.quotientEquivRestrictionSpace`, and evaluation at a Schwartz function is
  `Rd.besselEvalCLM`.

The formalisation of the trace space settled the following points of the plan.

* **The trace kernel is defined by chart traces.** `Rd.BoundedLipschitzDomain.traceKer` is the
  common kernel of the bounded operators `u ↦ Tr_j(ψ_j u)` into `L_2` of the hyperplanes of the
  charts, for the canonical resolution of unity `Ω.boundaryPartition`; that it consists of the
  `u` whose boundary trace vanishes almost everywhere on `Γ`, for every resolution of unity, is a
  theorem (`Rd.BoundedLipschitzDomain.mem_traceKer_iff`), so the kernel does not depend on the
  choice.
* **The bound `H^1(ℝ^d) ⊆ B^{1/2}_{2,1}(ℝ^d)` composes existing inclusions.** The moduli are
  bounded by the band-limited approximation norm, that by the norm of `F^1_{2,2}`, and that by
  the `H^1` norm, each with an explicit constant (`Rd.modNorm_two_le_norm`,
  `Rd.sobolevOneBesovConst`); the step from `B^1_{2,2}` to `B^{1/2}_{2,1}` has constant `√2`
  (`Rd.modNorm_half_one_le`, by the Cauchy–Schwarz inequality `ENNReal.lqNorm_one_mul_le`), and
  `Rd.modNorm_half_one_le_norm` is the composite bound.
* **Additions to the plan**: the trace of a Lipschitz graph domain commutes with complex scalars
  (`Rd.LipschitzGraph.trace_smul`); the boundary trace is linear on `H^1(ℝ^d)`
  (`Rd.BoundedLipschitzDomain.boundaryTrace_toL2_sub`); a function vanishes almost everywhere on
  `Γ` iff its chart pieces vanish (`Rd.BoundedLipschitzDomain.eventuallyEq_zero_iff_forall_chart`);
  the boundary trace of every element of `H^1(ℝ^d)` lies in `B^{1/2}_{2,2}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_toL2`); and an element of `H^{1/2}(Γ)` is
  determined by its boundary trace
  (`Rd.BoundedLipschitzDomain.boundaryTrace_extend_eventuallyEq_iff`).
* **Names**: `H^1(Ω)` of a bounded Lipschitz domain is the abbreviation
  `Rd.BoundedLipschitzDomain.SobolevOne`, `H^{-1/2}(Γ)` is
  `Rd.BoundedLipschitzDomain.DualTraceSpace`, and the Riesz map is
  `Rd.BoundedLipschitzDomain.dualTraceEquiv`.

The formalisation of the area formula settled the following points of the plan.

* **The linear case is Mathlib's area formula for linear maps.** The linear graph
  `S_g x' = x' + ⟪g, x'⟫ e` is the linear map `Rd.LipschitzGraph.linearGraph g : H →ₗ[ℝ] V`, the
  graph of `⟪g, ·⟫` in the sense of `Rd.LipschitzGraph.graphOver`. Its Gram operator
  `S_g* S_g` is the transvection `x' ↦ x' + ⟪g, x'⟫ g` of determinant `1 + ‖g‖²`, so its norm
  determinant is `√(1 + ‖g‖²)` (`Rd.LipschitzGraph.normDet_linearGraph`, through
  `LinearMap.normDet_sq` and `LinearMap.transvection.det`), and
  `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume` gives the area. The file also
  writes `S_g` explicitly as the stretch of `H` by `√(1 + ‖g‖²)` along `g/‖g‖` (`Rd.stretch`)
  followed by an isometry of `H` into `V`, linear in `x'` (`Rd.LipschitzGraph.tilt`,
  norm-preserving by an inner-product computation, `Rd.LipschitzGraph.isometry_tilt`).
* **The comparison of nearby graphs** is one lemma for the graphs of any two functions on `H`
  (`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphOver_image_le`), applied in both
  directions, on top of a general lemma for two maps with nearby increments
  (`Rd.euclideanHausdorffMeasure_image_le_of_near`).
* **Measurability of the good sets**: the Taylor condition is required only at the points of a
  dense sequence of `H` (`Rd.LipschitzGraph.goodSet`, Mathlib's `TopologicalSpace.denseSeq`), so
  the sets are countable intersections of measurable sets, and it extends to all nearby points
  because it is closed (`Rd.LipschitzGraph.abs_taylor_le_of_mem_goodSet`). The cells of small
  diameter are balls around the same dense sequence, made disjoint with Mathlib's `disjointed`
  (`Rd.LipschitzGraph.exists_goodPartition`).
* **Every dimension**: the formula holds for every `V`, including `dim V = 1`, where `H` is `{0}`
  and the boundary a point; it is stated with `μHE[finrank ℝ V - 1]`
  (`Rd.LipschitzGraph.finrank_hyperplane_eq_sub_one`, next to `finrank_hyperplane_add_one` in
  `FunctionSpaces/Domains/Lipschitz/GraphParametrization.lean`).
* **Additions to the plan**: the integral form holds for every `F : V → [0, ∞]`, measurable or
  not (`Rd.LipschitzGraph.lintegral_graphMap`, through
  `lintegral_withDensity_eq_lintegral_mul_non_measurable`); the outward unit normal is
  measurable (`Rd.LipschitzGraph.measurable_normalAt`); the bound
  `LipschitzOnWith.euclideanHausdorffMeasure_image_le` holds on all metric spaces.
* **Names**: the lemmas on `μHE` carry Mathlib's prefix `euclideanHausdorffMeasure_`, the area
  formula included (`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphMap_image`).

The formalisation of the surface measure settled the following points of the plan.

* **The chart formula asks for a nonnegative resolution of unity.** The plan stated
  `∫⁻ F dσ = ∑_j ∫⁻ x', ofReal (ψ_j (γ_j x')) * F (γ_j x') * ofReal (gram_j x')` for every
  resolution of unity; with values in `[0, ∞]` this needs `ψ_j ≥ 0`, which
  `Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure` assumes. Smooth partitions of unity
  provide such resolutions (`Rd.BoundedLipschitzDomain.exists_boundaryPartition_nonneg`, with
  `∑_j ψ_j ≤ 1` everywhere), and the canonical resolution of unity
  `Rd.BoundedLipschitzDomain.boundaryPartition`, used by every definition on `Γ`, is chosen among
  them (decision of 14 October 2026), so it is nonnegative. For
  complex integrals the chart formula holds for every resolution of unity
  (`Rd.BoundedLipschitzDomain.integral_surfaceMeasure`). The formula for a single chart,
  `Rd.BoundedLipschitzDomain.lintegral_surfaceMeasure_of_support`, needs no resolution of unity,
  and none of the chart formulas asks for measurability of `F`.
* **Charts agree on overlaps for `F` supported in `B_j ∩ B_k`**
  (`Rd.BoundedLipschitzDomain.lintegral_chart_eq`), without the condition `F = 0` off `Γ` of the
  plan.
* **`|Γ| = 0`** comes from the finiteness of `σ`: a set of finite `μHE[d-1]`-measure has
  `μHE[d]`-measure zero (`MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top`), and
  `μHE[d]` is the volume (`Rd.BoundedLipschitzDomain.volume_frontier`).
* **The unit normal field** `Rd.BoundedLipschitzDomain.normal` is pasted with the nonnegative
  resolution of unity, so that `‖ν‖ ≤ 1` everywhere (`Rd.BoundedLipschitzDomain.norm_normal_le`).
* **Additions to the plan**: the null sets of `σ` in one chart
  (`Rd.BoundedLipschitzDomain.ae_surfaceMeasure_ball_iff`), the boundary trace in `L_p(Γ)` for
  every `1 ≤ p < ∞` with an explicit bound by the chart traces
  (`Rd.BoundedLipschitzDomain.memLp_boundaryTrace`,
  `Rd.BoundedLipschitzDomain.lintegral_enorm_boundaryTrace_le`), the trace of `H^1(ℝ^d)` into
  `L_2(Γ)` (`Rd.BoundedLipschitzDomain.ambientTraceL2`), which agrees with `boundaryTraceL2` on
  `H^1(Ω)` (`Rd.BoundedLipschitzDomain.boundaryTraceL2_eq_ambientTraceL2`), its linearity on
  `H^1(ℝ^d)` almost everywhere on `Γ`
  (`Rd.BoundedLipschitzDomain.boundaryTrace_toL2_add`,
  `Rd.BoundedLipschitzDomain.boundaryTrace_toL2_smul`), the bound of the trace of `H^1(ℝ^d)` on
  one Lipschitz graph (`Rd.LipschitzGraph.exists_enorm_trace_toL2_le`), and every function of
  `B^{1/2}_{2,2}(Γ)` as the trace of an element of `H^{1/2}(Γ)` in `L_2(Γ)`
  (`Rd.BoundedLipschitzDomain.exists_traceL2_ae_eq`).

The formalisation of the trace kernel settled the following points of the plan.

* **One mollifier per chart** (decision of 21 October 2026) pushes the chart pieces into `Ω` and
  smooths them in one step: its support lies in the open cone of the chart
  (`Rd.LipschitzGraph.coneMollifier`), and the closure of a graph domain plus the open cone lies
  in the domain (`Rd.LipschitzGraph.add_mem_of_mem_closure`), so its dilates map a function that
  vanishes outside the closure of `Ω_j` to smooth functions with compact support in `Ω`
  (`Rd.BoundedLipschitzDomain.mem_tildeSpace_of_mulLp_chart`).
* **`H̃^1(Ω)` by supports.** The theorem is proved as
  `ker γ → (zero extension) → H̃^1(Ω) → H^1_0(Ω)`: by Section 4.12, `u ∈ ker γ` iff
  `1_Ω u ∈ H^1(ℝ^d)`, and an element of `H^1(ℝ^d)` lies in `H̃^1(Ω)` iff it vanishes outside `Ω`
  (`Rd.BoundedLipschitzDomain.mem_tildeSpace_iff`); the isometry `H̃^1(Ω) ≅ H^1_0(Ω)` of
  Section 4.5 finishes. The inclusion `H^1_0(Ω) ⊆ ker γ` runs the same chain backwards.
* **Names**: the quotient isometry is
  `Rd.BoundedLipschitzDomain.quotientZeroBoundaryEquivTraceSpace`, the isometry
  `H̃^1(Ω) ≅ ker γ` is `Rd.BoundedLipschitzDomain.tildeEquivTraceKer`, and the dual of the trace
  kernel is `Rd.BoundedLipschitzDomain.dualTraceKerEquiv`.

**Folder layout by setting** (23 October 2026). The project is now organised as
*Characterizations of Function Spaces*: the files of `FunctionSpaces/` lie in folders by setting
with one folder per characterisation, `FunctionSpaces/Analysis/` for the tools,
`FunctionSpaces/Rd/` for `ℝ^d` and `FunctionSpaces/Domains/` for Lipschitz domains, traces,
Sobolev spaces on domains and manifolds. The module paths of this document follow the new layout
(for instance `FunctionSpaces.Domains.Traces.TraceKernel`); the package, the library names, the
namespaces and every declaration name are unchanged.

**The extension as a bounded linear operator** (24 October 2026). H.2 also holds in operator
form: a bounded linear extension operator on value–derivative jets, a right inverse of the
restriction, in the shape of TauCeti's `W1p.exists_extensionL_of_isLipschitzDomainWith`, for
every `1 ≤ p ≤ ∞` by reflection (`Rd.BoundedLipschitzDomain.exists_extensionL`,
`Rd.BoundedLipschitzDomain.sobolevExtensionL`), Section 4.3; for `1 < p < ∞` Rychkov's extension
gives an extension operator as well (`Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp`).

**The extension theorem from the operators** (29 October 2026). The extensions of single
functions are the extension operators applied to one function
(`Rd.SobolevExtensionOp.extendsSobolev`): `Rd.BoundedLipschitzDomain.exists_extendsSobolev` lies
in `FunctionSpaces.Domains.Extension.SobolevExtensionOperator`, the forms for `1 ≤ p ≤ ∞`
(`Rd.BoundedLipschitzDomain.exists_extendsSobolev_of_one_le`,
`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_of_one_le`) in
`FunctionSpaces.Domains.Extension.ReflectionExtensionOperator`, and the consequences of
Section 4.3 (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev`,
`Rd.BoundedLipschitzDomain.memSobolevOn_iff_memWeakSobolev`, Rellich, the quotient norm and the
boundary traces of `W^{1,2}(Ω)`) in `FunctionSpaces.Domains.Sobolev.LipschitzDomainW1p`. The
chosen extension operator is the one by reflection for every `1 ≤ p ≤ ∞`, under the names
`Rd.BoundedLipschitzDomain.sobolevExtensionL`, `Rd.BoundedLipschitzDomain.exists_extensionL` and
`Rd.exists_extensionL_of_isBoundedLipschitzDomain`, stated with `[Fact (1 ≤ p)]`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics **140**,
  Elsevier/Academic Press, Amsterdam, 2003.
* S. Armstrong, J. Kempe, *Formalization of De Giorgi–Nash–Moser theory in Lean*,
  arXiv:2604.05984, 2026; the Lean library `github.com/scottnarmstrong/DeGiorgi`.
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
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  Mathematical Series **30**, Princeton University Press, Princeton, NJ, 1970.
* *TauCeti*, a Lean library downstream of Mathlib, `github.com/TauCetiProject/TauCeti`.
