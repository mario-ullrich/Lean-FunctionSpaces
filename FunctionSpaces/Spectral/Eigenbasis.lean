/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Spectral.Blocks
public import FunctionSpaces.Sobolev.Embeddings
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Eigenbases of continuous functions

Let `M` be a topological space with a finite Borel measure `μ`. An **eigenbasis** of `M`
(`LaplaceEigenbasis`) is a spectral scheme in `L_2(μ)`, a Hilbert basis `(e_i)` with a level
`λ : ι → ℕ` and finitely many basis elements of each level, whose elements are the `L_2` classes
of bounded continuous functions (`LaplaceEigenbasis.eigenfun`). The model is the Laplace–Beltrami
operator of a compact Riemannian manifold: its eigenfunctions form such a basis, continuous by
elliptic regularity, with `λ(i) = ⌊√λ_i⌋`. Mathlib has neither the operator nor these facts, so
they enter as the fields of the structure; every statement below is proved from them. The
Fourier basis of the torus is an eigenbasis (`Torus.fourierEigenbasis`).

The continuous eigenfunctions of level `< n` span the space `eigenSpan n` of bounded continuous
functions (`LaplaceEigenbasis.eigenSpan`), and these spaces form a scheme of functions
(`LaplaceEigenbasis.eigenScheme`). Its classes in `L_2` are the spectral scheme
(`LaplaceEigenbasis.toLp_eigenScheme_eq`), so the spectral theory applies:

* **`B^s_{2,2} = H^s`** (`LaplaceEigenbasis.memBesov_two_two_iff`): for `s > 0`, `f ∈ L_2(μ)`
  lies in `B^s_{2,2}` iff `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞`;
* **Littlewood–Paley blocks** (`LaplaceEigenbasis.memBesov_two_iff_blockNorm_lt_top`) with sharp
  cut-offs at the levels `2^k`;
* **the Sobolev space** `H^s` as a Sobolev space for the scheme in `L_2`
  (`LaplaceEigenbasis.sobolevSpace`), with Jackson's and Bernstein's inequalities of constant `1`.

The Besov spaces `B^s_{p,q}` of the scheme are defined for every `1 ≤ p ≤ ∞` by
`FunctionScheme.MemBesov`; their embeddings need the Nikolskii property
(`FunctionSpaces.Spectral.EigenbasisNikolskii`).
-/

@[expose] public section

open MeasureTheory FunctionScheme
open scoped ENNReal BoundedContinuousFunction lp

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

/-- An **eigenbasis** on `M`: a spectral scheme in `L_2(μ)` whose basis elements are the `L_2`
classes of bounded continuous functions. For the Laplace–Beltrami operator of a compact
Riemannian manifold these are the eigenfunctions, with the level `⌊√λ⌋` of the eigenvalue `λ`;
the existence of such a basis (Rellich's compactness and elliptic regularity) is not in Mathlib
and enters through the fields. -/
structure LaplaceEigenbasis (ι : Type*) (μ : Measure M) [IsFiniteMeasure μ]
    extends SpectralScheme ι (Lp ℂ 2 μ) where
  /-- The continuous representatives of the basis elements. -/
  eigenfun : ι → (M →ᵇ ℂ)
  toLp_eigenfun : ∀ i, BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (eigenfun i) = basis i

namespace LaplaceEigenbasis

variable {ι : Type*} {μ : Measure M} [IsFiniteMeasure μ] (B : LaplaceEigenbasis ι μ)

/-- The **span of the eigenfunctions of level `< n`**, a space of bounded continuous
functions. -/
noncomputable def eigenSpan (n : ℕ) : Submodule ℂ (M →ᵇ ℂ) :=
  Submodule.span ℂ (B.eigenfun '' {i | B.level i < n})

/-- No eigenfunction has level `< 0`. -/
@[simp]
theorem eigenSpan_zero : B.eigenSpan 0 = ⊥ := by simp [eigenSpan]

/-- The spans increase with the level. -/
theorem eigenSpan_mono : Monotone B.eigenSpan := fun _ _ h =>
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

/-- An eigenfunction of level `< n` lies in the span of level `< n`. -/
theorem eigenfun_mem_eigenSpan {n : ℕ} {i : ι} (hi : B.level i < n) :
    B.eigenfun i ∈ B.eigenSpan n :=
  Submodule.subset_span ⟨i, hi, rfl⟩

/-- The **scheme of eigenfunctions**: the approximants of complexity `n` are the combinations of
the eigenfunctions of level `< n`. -/
noncomputable def eigenScheme : FunctionScheme M :=
  ApproximationScheme.ofSubmodules (fun n => (B.eigenSpan n).restrictScalars ℝ)
    (by simp) (fun _ _ h => B.eigenSpan_mono h)

/-- The approximants of the eigenfunction scheme are the spans of the eigenfunctions. -/
@[simp]
theorem mem_eigenScheme {n : ℕ} {a : M →ᵇ ℂ} : a ∈ B.eigenScheme n ↔ a ∈ B.eigenSpan n :=
  Iff.rfl

/-- **The scheme in `L_2` is the spectral scheme**: the `L_2` classes of the combinations of
eigenfunctions of level `< n` are the combinations of the basis elements of level `< n`. -/
theorem toLp_eigenScheme_eq : B.eigenScheme.toLp μ 2 = B.toScheme := by
  ext n f
  change f ∈ (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℝ) '' (B.eigenSpan n : Set _) ↔
    f ∈ (B.span n : Set _)
  have hmap : (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℝ : _ → _) '' (B.eigenSpan n : Set _)
      = SetLike.coe ((B.eigenSpan n).map
          (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).toLinearMap) := by
    rw [Submodule.map_coe]; rfl
  rw [hmap, eigenSpan, Submodule.map_span, ← Set.image_comp]
  have hset : ((BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).toLinearMap ∘ B.eigenfun) ''
      {i | B.level i < n} = B.basis '' {i | B.level i < n} := by
    ext g
    simp only [Set.mem_image, Function.comp_apply, ContinuousLinearMap.coe_coe, B.toLp_eigenfun]
  rw [hset]
  rfl

/-! ### The spectral theory in `L_2` -/

variable {s : ℝ} {q : ℝ≥0∞}

/-- **`B^s_{2,2} = H^s`** for an eigenbasis: for `s > 0`, `f ∈ L_2(μ)` lies in `B^s_{2,2}` iff
`∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞`. -/
theorem memBesov_two_two_iff (hs : 0 < s) (f : Lp ℂ 2 μ) :
    B.eigenScheme.MemBesov μ 2 s 2 f ↔
      Memℓp (fun i => ((((1 + B.level i : ℕ) : ℝ) ^ s : ℝ) : ℂ) * B.basis.repr f i) 2 := by
  change (B.eigenScheme.toLp μ 2).MemApprox s 2 f ↔ _
  rw [toLp_eigenScheme_eq]
  exact B.memApprox_two_iff hs f

/-- **The Littlewood–Paley characterisation of `B^s_{2,q}`** for an eigenbasis, with sharp
cut-offs at the levels `2^k`: for `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{2,q}` iff
`‖P_1 f‖ + ‖(2^(ks) ‖Δ_k f‖_2)_k‖_{ℓ_q} < ∞`, with
`‖Δ_k f‖_2² = ∑_{2^k ≤ λ(i) < 2^(k+1)} |⟨e_i, f⟩|²`. -/
theorem memBesov_two_iff_blockNorm_lt_top (hs : 0 < s) (hq : 1 ≤ q) (f : Lp ℂ 2 μ) :
    B.eigenScheme.MemBesov μ 2 s q f ↔ B.projectionScheme.blockNorm s q f < ∞ := by
  change (B.eigenScheme.toLp μ 2).MemApprox s q f ↔ _
  rw [toLp_eigenScheme_eq]
  exact B.memApprox_iff_blockNorm_lt_top hs hq

/-- The **Sobolev space `H^s`** of an eigenbasis, `s > 0`, as a Sobolev space for the scheme of
eigenfunctions in `L_2`: the image of `ℓ²(ι)` under `c ↦ ∑_i (1 + λ(i))^(-s) c_i e_i`, with
Jackson's and Bernstein's inequalities of order `s` and constant `1`. -/
noncomputable def sobolevSpace (s : ℝ) (hs : 0 < s) : B.eigenScheme.SobolevSpace μ 2 ℓ²(ι, ℂ) :=
  ApproximationScheme.SmoothnessSpace.congr B.toLp_eigenScheme_eq.symm
    (B.toSmoothnessSpace s hs)

/-- `H^s` has order `s`. -/
@[simp]
theorem sobolevSpace_order (hs : 0 < s) : (B.sobolevSpace s hs).order = s := rfl

/-- The embedding of `H^s` is `J_s`. -/
theorem sobolevSpace_iota (hs : 0 < s) (c : ℓ²(ι, ℂ)) :
    (B.sobolevSpace s hs).ι c = B.sobolevEmbed s hs.le c := rfl

/-- **Membership in `H^s`** through the coefficients: `f ∈ L_2(μ)` lies in the range of the
Sobolev embedding iff `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞`. -/
theorem mem_range_sobolev_iff (hs : 0 < s) (f : Lp ℂ 2 μ) :
    f ∈ Set.range (B.sobolevSpace s hs).ι ↔
      Memℓp (fun i => ((((1 + B.level i : ℕ) : ℝ) ^ s : ℝ) : ℂ) * B.basis.repr f i) 2 :=
  B.mem_range_sobolevEmbed_iff s hs.le f

/-- **`H^s ⊆ B^s_{2,∞}`**, from Jackson's inequality. -/
theorem sobolev_memBesov_top (hs : 0 < s) (c : ℓ²(ι, ℂ)) :
    B.eigenScheme.MemBesov μ 2 s ∞ ((B.sobolevSpace s hs).ι c) :=
  (B.sobolevSpace s hs).memApprox_top c

/-- **`B^t_{2,q} ⊆ H^s` for `t > s`**, from Bernstein's inequality. -/
theorem exists_sobolev_of_memBesov (hs : 0 < s) {t : ℝ} (hst : s < t) (hq : 1 ≤ q)
    {f : Lp ℂ 2 μ} (hf : B.eigenScheme.MemBesov μ 2 t q f) :
    ∃ c : ℓ²(ι, ℂ), (B.sobolevSpace s hs).ι c = f :=
  (B.sobolevSpace s hs).exists_eq_of_lt hst hq hf

end LaplaceEigenbasis
