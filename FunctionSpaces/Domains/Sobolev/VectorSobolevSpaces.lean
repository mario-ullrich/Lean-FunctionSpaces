/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Traces.TraceKernelGeneral
public import FunctionSpaces.Domains.Sobolev.TildeZeroBoundaryEquiv
public import FunctionSpaces.Domains.Traces.BoundarySobolev
public import FunctionSpaces.Analysis.Hilbert.PiLpMaps

/-!
# Vector-valued Sobolev spaces on domains and boundaries

For a normed space `X` and `m ∈ ℕ`, `X^m = WithLp 2 (Fin m → X)` is the space of `m`-tuples
`x = (x_1, …, x_m)` with the norm `‖x‖² = ∑_i ‖x_i‖²`; for a Hilbert space `X` it is the Hilbert
direct sum with `⟪x, y⟫ = ∑_i ⟪x_i, y_i⟫` (Mathlib's `PiLp.innerProductSpace`). The spaces of
`ℂ^m`-valued functions are taken componentwise in this form, as in McLean, Chapter 4, and the
spaces `H^s Λ^k` of differential forms are such sums in the basis `dx_I`. The maps act
componentwise through the general maps of `FunctionSpaces.Analysis.Hilbert.PiLpMaps`:
`PiLp.compLeftL` for bounded operators `f` and `PiLp.congrRightL` for isomorphisms, with the
kernel `(ker f)^m` (`PiLp.ker_compLeftL`) and, for a subspace `K ⊆ X`, the range
`K^m = PiLp.piSubmodule m K` of the componentwise inclusion (`PiLp.range_compLeftL_subtypeL`).
For an inner product space `X` the orthogonal complement of `K^m` is `(Kᗮ)^m`
(`PiLp.orthogonal_piSubmodule`), and for a Hilbert space `X` the dual of `X^m` is `(X^*)^m`
isometrically (`PiLp.strongDualEquiv`).

* **The vector spaces** of an open set `Ω`: `H^s(Ω)^m`, `H̃^s(Ω)^m`, `H^s_0(Ω)^m`
  (`Rd.VecRestrictionSpace`, `Rd.VecTildeSpace`, `Rd.VecZeroBoundarySpace`); of a bounded
  Lipschitz domain with boundary `Γ`: the trace space of `H^s(Ω)^m`, `1/2 < s < 3/2`
  (`Rd.BoundedLipschitzDomain.VecTraceSpace`), isometric to the orthogonal complement of the
  vector trace kernel `(ker γ_s)^m` (`Rd.BoundedLipschitzDomain.range_vecExtend`,
  `Rd.BoundedLipschitzDomain.norm_vecExtend_apply`), and `H^t(Γ)^m` with the
  componentwise Gagliardo inner product (`Rd.BoundedLipschitzDomain.VecBoundarySobolev`,
  `Rd.BoundedLipschitzDomain.inner_vecBoundarySobolev`).
* **Traces**: for `1/2 < s < 3/2` the trace maps `H^s(Ω)^m` onto `H^{s-1/2}(Γ)^m` with a bounded
  linear right inverse and kernel `H^s_0(Ω)^m`, and the trace space of `H^s(Ω)^m` is isomorphic to
  `H^{s-1/2}(Γ)^m` (`Rd.BoundedLipschitzDomain.vecSobolevTrace`,
  `Rd.BoundedLipschitzDomain.vecSobolevTrace_vecSobolevExtend`,
  `Rd.BoundedLipschitzDomain.ker_vecSobolevTrace`,
  `Rd.BoundedLipschitzDomain.vecTraceSpaceEquivBoundarySobolev`); for `1 ≤ p < ∞`,
  `1 ≤ q ≤ ∞` and `1/p < s < 1 + 1/p` the Besov trace maps `B^s_{p,q}(Ω)^m` onto
  `B^{s-1/p}_{p,q}(Γ)^m` with a bounded linear right inverse
  (`Rd.BoundedLipschitzDomain.vecBesovTrace`, `Rd.BoundedLipschitzDomain.vecBesovExtend`).
* **`H̃^s = H^s_0` and duality**: restriction is an isometric isomorphism of `H̃^l(Ω)^m` onto
  `H^l_0(Ω)^m` for every open `Ω` and `l ∈ ℕ` (`Rd.vecTildeEquivZeroBoundaryNat`), an
  isomorphism of `H̃^s(Ω)^m` onto `H^s_0(Ω)^m` on a bounded Lipschitz domain for `s ≥ 0`,
  `s - 1/2 ∉ ℕ_0` (`Rd.BoundedLipschitzDomain.vecTildeEquivZeroBoundaryOfNeHalf`); the dual of
  `H̃^s(Ω)^m` is `H^{-s}(Ω)^m` (`Rd.vecDualEquiv`), and the dual of `H^t(Γ)^m` is identified with
  `H^t(Γ)^m` by Riesz (`Rd.BoundedLipschitzDomain.vecDualBoundarySobolevEquiv`).
-/

@[expose] public section

open TopologicalSpace
open scoped ENNReal InnerProductSpace BesselPotentialSpace

namespace Rd

/-! ### The vector spaces of an open set -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The space `H^s(Ω)^m`** of an open set `Ω`, the Hilbert direct sum of `m` copies of the
restriction space `H^s(Ω)`: the restrictions to `Ω` of the `ℂ^m`-valued functions of `H^s(V)`,
taken componentwise. -/
abbrev VecRestrictionSpace (m : ℕ) (s : ℝ) (Ω : Opens V) :=
  WithLp 2 (Fin m → RestrictionSpace s Ω)

/-- **The space `H̃^s(Ω)^m`**, the Hilbert direct sum of `m` copies of `H̃^s(Ω)`, the closure of
the test functions of `Ω` in `H^s(V)`. -/
abbrev VecTildeSpace (m : ℕ) (s : ℝ) (Ω : Opens V) :=
  WithLp 2 (Fin m → ↥(tildeSpace s Ω))

/-- **The space `H^s_0(Ω)^m`**, the Hilbert direct sum of `m` copies of `H^s_0(Ω)`, the closure of
the restricted test functions in `H^s(Ω)`. Inside `H^s(Ω)^m` the corresponding subspace is
`PiLp.piSubmodule m (Rd.zeroBoundarySpace s Ω)` (the kernel in
`Rd.BoundedLipschitzDomain.ker_vecSobolevTrace`). -/
abbrev VecZeroBoundarySpace (m : ℕ) (s : ℝ) (Ω : Opens V) :=
  WithLp 2 (Fin m → ↥(zeroBoundarySpace s Ω))

/-- **`H̃^l(Ω)^m ≅ H^l_0(Ω)^m` isometrically** for every open `Ω` and every `l ∈ ℕ`: restriction
in each component, the isometry `Rd.tildeEquivZeroBoundaryNat` (Hewett–Moiola, Lemma 2.2(iii))
acting componentwise (Mathlib's `LinearIsometryEquiv.piLpCongrRight`). -/
noncomputable def vecTildeEquivZeroBoundaryNat (m l : ℕ) (Ω : Opens V) :
    VecTildeSpace m l Ω ≃ₗᵢ[ℂ] VecZeroBoundarySpace m l Ω :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ => tildeEquivZeroBoundaryNat l Ω

/-- The `i`-th component of the image of `U` is the restriction of `U_i` to `Ω`. -/
theorem coe_vecTildeEquivZeroBoundaryNat_apply (m l : ℕ) (Ω : Opens V) (U : VecTildeSpace m l Ω)
    (i : Fin m) :
    (vecTildeEquivZeroBoundaryNat m l Ω U i : RestrictionSpace l Ω) = restrictProj l Ω (U i) :=
  rfl

/-- **The dual of `H̃^s(Ω)^m` is `H^{-s}(Ω)^m`**, for every open `Ω` and every real `s`: Riesz's
representation on `H̃^s(Ω)^m` (Mathlib's `InnerProductSpace.toDual`) followed by the isometry
`H̃^s(Ω) ≅ H^{-s}(Ω)` of `Rd.tildeEquivRestriction` in each component; conjugate-linear and
isometric. A functional `ℓ` is the sum of the pairings of the components
(`Rd.vecDualEquiv_apply`), the vector form of `Rd.tildeDualEquiv`. -/
noncomputable def vecDualEquiv (m : ℕ) (s : ℝ) (Ω : Opens V) :
    StrongDual ℂ (VecTildeSpace m s Ω) ≃ₗᵢ⋆[ℂ] VecRestrictionSpace m (-s) Ω :=
  (InnerProductSpace.toDual ℂ (VecTildeSpace m s Ω)).symm.trans
    (LinearIsometryEquiv.piLpCongrRight 2 fun _ => tildeEquivRestriction s Ω)

/-- **`ℓ` is the sum of the componentwise pairings**: `ℓ(U) = ∑_i [W_i, U_i]` for
`W = vecDualEquiv m s Ω ℓ` and every `U ∈ H̃^s(Ω)^m` (Mathlib's
`InnerProductSpace.toDual_symm_apply`, `PiLp.inner_apply`; `Rd.sobolevPairing_besselShift`). -/
theorem vecDualEquiv_apply (m : ℕ) {s : ℝ} {Ω : Opens V} (ℓ : StrongDual ℂ (VecTildeSpace m s Ω))
    (U : VecTildeSpace m s Ω) :
    ℓ U = ∑ i, sobolevPairing s (vecDualEquiv m s Ω ℓ i : H^{-s}(V)) (U i : H^{s}(V)) := by
  have h : ℓ U = InnerProductSpace.toDual ℂ (VecTildeSpace m s Ω)
      ((InnerProductSpace.toDual ℂ (VecTildeSpace m s Ω)).symm ℓ) U := by
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [h, InnerProductSpace.toDual_apply_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_inner, vecDualEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply, coe_tildeEquivRestriction_apply,
    sobolevPairing_besselShift]

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-! ### Traces of vector functions on a bounded Lipschitz domain -/

/-- **The trace space of `H^s(Ω)^m`**, `1/2 < s < 3/2`: the Hilbert direct sum of `m` copies of
the trace space `Ω.TraceSpace s`. The componentwise extension maps it isometrically onto the
orthogonal complement of the vector trace kernel `(ker γ_s)^m` in `H^s(Ω)^m`
(`Rd.BoundedLipschitzDomain.norm_vecExtend_apply`, `Rd.BoundedLipschitzDomain.range_vecExtend`). -/
abbrev VecTraceSpace (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :=
  WithLp 2 (Fin m → Ω.TraceSpace s hs hs')

/-- **The vector trace kernel** `(ker γ_s)^m ⊆ H^s(Ω)^m`, `1/2 < s < 3/2`: the tuples whose
components all lie in the trace kernel. -/
noncomputable def vecTraceKer (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : Submodule ℂ (VecRestrictionSpace m s Ω.toOpens) :=
  PiLp.piSubmodule m (Ω.traceKer s hs hs')

/-- **The vector trace** `H^s(Ω)^m → Ω.VecTraceSpace m s`, `1/2 < s < 3/2`: the trace `γ_s` in
each component. -/
noncomputable def vecTrace (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    VecRestrictionSpace m s Ω.toOpens →L[ℂ] Ω.VecTraceSpace m s hs hs' :=
  PiLp.compLeftL m (Ω.domainTrace s hs hs')

/-- **The vector extension** `Ω.VecTraceSpace m s → H^s(Ω)^m`, `1/2 < s < 3/2`: the extension
`E_s` in each component, an isometry (`Rd.BoundedLipschitzDomain.norm_vecExtend_apply`). -/
noncomputable def vecExtend (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.VecTraceSpace m s hs hs' →L[ℂ] VecRestrictionSpace m s Ω.toOpens :=
  PiLp.compLeftL m (Ω.domainExtend s hs hs')

/-- **The vector extension is a right inverse of the vector trace**
(`Rd.BoundedLipschitzDomain.domainTrace_domainExtend` in each component). -/
@[simp]
theorem vecTrace_vecExtend {m : ℕ} {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (w : Ω.VecTraceSpace m s hs hs') : Ω.vecTrace m s hs hs' (Ω.vecExtend m s hs hs' w) = w :=
  PiLp.ext fun i => Ω.domainTrace_domainExtend (w i)

/-- **The vector extension is an isometry**: `‖E_s^m w‖ = ‖w‖`
(`Rd.BoundedLipschitzDomain.norm_domainExtend_apply` in each component,
`PiLp.norm_compLeftL_apply`). -/
theorem norm_vecExtend_apply {m : ℕ} {s : ℝ} {hs : 1 / 2 < s} {hs' : s < 3 / 2}
    (w : Ω.VecTraceSpace m s hs hs') : ‖Ω.vecExtend m s hs hs' w‖ = ‖w‖ :=
  PiLp.norm_compLeftL_apply m (fun t => Ω.norm_domainExtend_apply t) w

/-- **The kernel of the vector trace is the vector trace kernel** (`PiLp.ker_compLeftL`,
`Rd.BoundedLipschitzDomain.ker_domainTrace`). -/
theorem ker_vecTrace (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.vecTrace m s hs hs').ker = Ω.vecTraceKer m s hs hs' := by
  rw [vecTrace, PiLp.ker_compLeftL, Ω.ker_domainTrace s hs hs', vecTraceKer]

/-- **The orthogonal complement of the vector trace kernel** is `((ker γ_s)ᗮ)^m`, the tuples of
elements of the trace space (`PiLp.orthogonal_piSubmodule`). -/
theorem orthogonal_vecTraceKer (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.vecTraceKer m s hs hs')ᗮ = PiLp.piSubmodule m (Ω.traceKer s hs hs')ᗮ :=
  PiLp.orthogonal_piSubmodule m _

/-- **The trace space of `H^s(Ω)^m` is the orthogonal complement of the vector trace kernel**:
the range of the vector extension is `((ker γ_s)^m)ᗮ` (`PiLp.range_compLeftL_subtypeL`,
`Rd.BoundedLipschitzDomain.orthogonal_vecTraceKer`). -/
theorem range_vecExtend (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.vecExtend m s hs hs').range = (Ω.vecTraceKer m s hs hs')ᗮ := by
  rw [Ω.orthogonal_vecTraceKer m s hs hs']
  exact PiLp.range_compLeftL_subtypeL m _

/-- **The space `H^t(Γ)^m`**, the Hilbert direct sum of `m` copies of `H^t(Γ)`, `0 < t < 1`, with
the componentwise chart-wise Gagliardo inner product
(`Rd.BoundedLipschitzDomain.inner_vecBoundarySobolev`). -/
abbrev VecBoundarySobolev (m : ℕ) (t : ℝ) :=
  WithLp 2 (Fin m → Ω.BoundarySobolev t)

/-- **The inner product of `H^t(Γ)^m`**: `⟪g, h⟫ = ∑_i ⟪Φ g_i, Φ h_i⟫` for the Gagliardo
embedding `Φ` (Mathlib's `PiLp.inner_apply`, `Rd.BoundedLipschitzDomain.inner_boundarySobolev`):
the sum over `i` of `⟪g_i, h_i⟫_{L_2(Γ)} + ∑_j ⟪δ_j g_i, δ_j h_i⟫`, the polarised Gagliardo forms
of the chart pieces. -/
theorem inner_vecBoundarySobolev {m : ℕ} {t : ℝ} (g h : Ω.VecBoundarySobolev m t) :
    ⟪g, h⟫_ℂ = ∑ i, ⟪Ω.gagliardoEmbedding t (g i), Ω.gagliardoEmbedding t (h i)⟫_ℂ :=
  rfl

/-- **Riesz for the dual of `H^t(Γ)^m`**, `t > 0`: the conjugate-linear isometric isomorphism of
the dual of the Hilbert space `H^t(Γ)^m` onto it (Mathlib's `InnerProductSpace.toDual`), the
vector form of `Rd.BoundedLipschitzDomain.dualBoundarySobolevEquiv`. The componentwise
identification of this dual with `H^{-t}(Γ)^m` is `PiLp.strongDualEquiv`. -/
noncomputable def vecDualBoundarySobolevEquiv (m : ℕ) (t : ℝ) (ht : 0 < t) :
    StrongDual ℂ (Ω.VecBoundarySobolev m t) ≃ₗᵢ⋆[ℂ] Ω.VecBoundarySobolev m t :=
  haveI : Fact (0 < t) := ⟨ht⟩
  (InnerProductSpace.toDual ℂ (Ω.VecBoundarySobolev m t)).symm

/-- Every functional on `H^t(Γ)^m` is the sum of the inner products of the components of its
representing element with the components of the argument. -/
theorem vecDualBoundarySobolevEquiv_apply {m : ℕ} {t : ℝ} (ht : 0 < t)
    (ℓ : StrongDual ℂ (Ω.VecBoundarySobolev m t)) (g : Ω.VecBoundarySobolev m t) :
    ℓ g = ∑ i, ⟪Ω.vecDualBoundarySobolevEquiv m t ht ℓ i, g i⟫_ℂ := by
  have : Fact (0 < t) := ⟨ht⟩
  rw [← PiLp.inner_apply, vecDualBoundarySobolevEquiv, InnerProductSpace.toDual_symm_apply]

/-- **The vector trace `H^s(Ω)^m → H^{s-1/2}(Γ)^m`**, `1/2 < s < 3/2`: the trace
`Rd.BoundedLipschitzDomain.sobolevTrace` in each component (McLean, Theorem 3.38). -/
noncomputable def vecSobolevTrace (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    VecRestrictionSpace m s Ω.toOpens →L[ℂ] Ω.VecBoundarySobolev m (s - 1 / 2) :=
  PiLp.compLeftL m (Ω.sobolevTrace s hs hs')

/-- **The vector extension `H^{s-1/2}(Γ)^m → H^s(Ω)^m`**, `1/2 < s < 3/2`: the extension
`Rd.BoundedLipschitzDomain.sobolevExtend` in each component, a bounded linear right inverse of the
vector trace (`Rd.BoundedLipschitzDomain.vecSobolevTrace_vecSobolevExtend`). -/
noncomputable def vecSobolevExtend (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.VecBoundarySobolev m (s - 1 / 2) →L[ℂ] VecRestrictionSpace m s Ω.toOpens :=
  PiLp.compLeftL m (Ω.sobolevExtend s hs hs')

/-- **The vector extension is a right inverse of the vector trace**
(`Rd.BoundedLipschitzDomain.sobolevTrace_sobolevExtend` in each component). -/
theorem vecSobolevTrace_vecSobolevExtend (m : ℕ) (s : ℝ) (g : Ω.VecBoundarySobolev m (s - 1 / 2))
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.vecSobolevTrace m s hs hs' (Ω.vecSobolevExtend m s hs hs' g) = g :=
  PiLp.ext fun i => Ω.sobolevTrace_sobolevExtend s (g i) hs hs'

/-- **The vector trace maps `H^s(Ω)^m` onto `H^{s-1/2}(Γ)^m`**: it has a right inverse. -/
theorem vecSobolevTrace_surjective (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) : Function.Surjective (Ω.vecSobolevTrace m s hs hs') :=
  fun g => ⟨_, Ω.vecSobolevTrace_vecSobolevExtend m s g hs hs'⟩

/-- **The kernel of the vector trace is `H^s_0(Ω)^m`**, `1/2 < s < 3/2` (McLean, Theorem 3.40, in
each component): `PiLp.ker_compLeftL` and
`Rd.BoundedLipschitzDomain.ker_sobolevTrace_eq_zeroBoundarySpace`. -/
theorem ker_vecSobolevTrace (m : ℕ) (s : ℝ) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    (Ω.vecSobolevTrace m s hs hs').ker = PiLp.piSubmodule m (zeroBoundarySpace s Ω.toOpens) := by
  rw [vecSobolevTrace, PiLp.ker_compLeftL, Ω.ker_sobolevTrace_eq_zeroBoundarySpace s hs hs']

/-- **The trace space of `H^s(Ω)^m` is isomorphic to `H^{s-1/2}(Γ)^m`**, `1/2 < s < 3/2`: the
isomorphism `Rd.BoundedLipschitzDomain.traceSpaceEquivBoundarySobolev` in each component
(`PiLp.congrRightL`). -/
noncomputable def vecTraceSpaceEquivBoundarySobolev (m : ℕ) (s : ℝ)
    (hs : 1 / 2 < s := by norm_num) (hs' : s < 3 / 2 := by norm_num) :
    Ω.VecTraceSpace m s hs hs' ≃L[ℂ] Ω.VecBoundarySobolev m (s - 1 / 2) :=
  PiLp.congrRightL m (Ω.traceSpaceEquivBoundarySobolev s hs hs')

/-- The vector trace into `H^{s-1/2}(Γ)^m` is the vector trace into the trace space followed by the
isomorphism `Rd.BoundedLipschitzDomain.vecTraceSpaceEquivBoundarySobolev`. -/
theorem vecTraceSpaceEquivBoundarySobolev_vecTrace (m : ℕ) (s : ℝ)
    (u : VecRestrictionSpace m s Ω.toOpens) (hs : 1 / 2 < s := by norm_num)
    (hs' : s < 3 / 2 := by norm_num) :
    Ω.vecTraceSpaceEquivBoundarySobolev m s hs hs' (Ω.vecTrace m s hs hs' u) =
      Ω.vecSobolevTrace m s hs hs' u :=
  rfl

/-! ### Vector Besov traces -/

section Besov

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The vector Besov trace** `B^s_{p,q}(Ω)^m → B^{s-1/p}_{p,q}(Γ)^m`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `1/p < s < 1 + 1/p`: the Besov trace `Rd.BoundedLipschitzDomain.besovTrace` in each
component, on the finite `L_2` sums (every `ℓ_r` sum of the component norms, `1 ≤ r ≤ ∞`, gives
an equivalent norm). -/
noncomputable def vecBesovTrace (m : ℕ) (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) :
    WithLp 2 (Fin m → Ω.DomainBesov p 2 s q) →L[ℂ]
      WithLp 2 (Fin m → Ω.BoundaryBesov p (s - 1 / p.toReal) q) :=
  PiLp.compLeftL m (Ω.besovTrace hp s q hs hs')

/-- **The vector Besov extension** `B^t_{p,q}(Γ)^m → B^{t+1/p}_{p,q}(Ω)^m`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `0 < t < 1`: the extension `Rd.BoundedLipschitzDomain.besovExtend` in each
component, a right inverse of the vector Besov trace
(`Rd.BoundedLipschitzDomain.toLp_vecBesovTrace_vecBesovExtend`). -/
noncomputable def vecBesovExtend (m : ℕ) (hp : p ≠ ∞) (t : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (ht : 0 < t) (ht1 : t < 1) :
    WithLp 2 (Fin m → Ω.BoundaryBesov p t q) →L[ℂ]
      WithLp 2 (Fin m → Ω.DomainBesov p 2 (t + 1 / p.toReal) q) :=
  PiLp.compLeftL m (Ω.besovExtend hp t q ht ht1)

/-- **The vector Besov trace is onto** (`Rd.BoundedLipschitzDomain.besovTrace_surjective` in each
component, `PiLp.compLeftL_surjective`). -/
theorem vecBesovTrace_surjective (m : ℕ) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hs : 1 / p.toReal < s) (hs' : s < 1 + 1 / p.toReal) :
    Function.Surjective (Ω.vecBesovTrace m hp s q hs hs') :=
  PiLp.compLeftL_surjective m (Ω.besovTrace_surjective hp hs hs')

/-- **The vector Besov trace inverts the vector extension**: each component of the trace of
`vecBesovExtend g` has the function `g_i` in `L_p(Γ)`
(`Rd.BoundedLipschitzDomain.toLp_besovTrace_besovExtend`). The statement compares the functions
in `L_p(Γ)`, since the trace lands in `B^{(t+1/p)-1/p}_{p,q}(Γ)^m`. -/
theorem toLp_vecBesovTrace_vecBesovExtend (m : ℕ) (hp : p ≠ ∞) {t : ℝ} {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (ht : 0 < t) (ht1 : t < 1) (g : WithLp 2 (Fin m → Ω.BoundaryBesov p t q))
    (i : Fin m) :
    (Ω.vecBesovTrace m hp (t + 1 / p.toReal) q (by linarith) (by linarith)
      (Ω.vecBesovExtend m hp t q ht ht1 g) i).toLp = (g i).toLp :=
  Ω.toLp_besovTrace_besovExtend hp ht ht1 (g i)

end Besov

/-! ### `H̃^s = H^s_0` for vector functions -/

/-- **`H̃^s(Ω)^m ≅ H^s_0(Ω)^m`** on a bounded Lipschitz domain, for `s ≥ 0` with
`s - 1/2 ∉ ℕ_0` (McLean, Theorem 3.33, in each component): the isomorphism
`Rd.BoundedLipschitzDomain.tildeEquivZeroBoundaryOfNeHalf` acting componentwise
(`PiLp.congrRightL`). -/
noncomputable def vecTildeEquivZeroBoundaryOfNeHalf (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ∀ k : ℕ, s ≠ k + 1 / 2) :
    VecTildeSpace m s Ω.toOpens ≃L[ℂ] VecZeroBoundarySpace m s Ω.toOpens :=
  PiLp.congrRightL m (Ω.tildeEquivZeroBoundaryOfNeHalf hs0 hs)

/-- The `i`-th component of the image of `U` is the restriction of `U_i` to `Ω`. -/
theorem coe_vecTildeEquivZeroBoundaryOfNeHalf_apply (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ∀ k : ℕ, s ≠ k + 1 / 2) (U : VecTildeSpace m s Ω.toOpens) (i : Fin m) :
    (Ω.vecTildeEquivZeroBoundaryOfNeHalf m hs0 hs U i : RestrictionSpace s Ω.toOpens) =
      restrictProj s Ω.toOpens (U i) :=
  rfl

end BoundedLipschitzDomain

end Rd
