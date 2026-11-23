/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Componentwise maps on finite `L_2` sums

For a complex normed space `X` and `m ∈ ℕ`, `X^m = WithLp 2 (Fin m → X)` is the space of
`m`-tuples `x = (x_1, …, x_m)` with the norm `‖x‖² = ∑_i ‖x_i‖²`; for an inner product space `X`
it carries the inner product `⟪x, y⟫ = ∑_i ⟪x_i, y_i⟫` (Mathlib's `PiLp.innerProductSpace`), and
for a Hilbert space `X` it is the Hilbert direct sum of `m` copies of `X`. The vector-valued
Sobolev spaces on domains and boundaries are such sums of scalar Sobolev spaces, and their traces,
extensions and isomorphisms act componentwise through the maps of this file.

* **Componentwise maps** (any normed spaces): a bounded operator `f : X → Y` acts on `X^m` with
  norm at most `‖f‖`, isometrically if `f` is isometric (`PiLp.compLeftL`,
  `PiLp.norm_compLeftL_le`, `PiLp.norm_compLeftL_apply`), onto if `f` is onto
  (`PiLp.compLeftL_surjective`), an isomorphism acts as an isomorphism (`PiLp.congrRightL`), and a
  semilinear isometric isomorphism as a semilinear isometric isomorphism (`PiLp.congrRightSL`;
  Mathlib's `LinearIsometryEquiv.piLpCongrRight` covers the linear case). The kernel and the range
  of `f` acting on `X^m` are `(ker f)^m` and `(range f)^m` (`PiLp.ker_compLeftL`,
  `PiLp.range_compLeftL`, with `K^m = PiLp.piSubmodule m K`).
* **Orthogonal complements and duals** (inner product spaces): `⟪ι_i a, x⟫ = ⟪a, x_i⟫` for the
  tuple `ι_i a` with `a` at `i` and `0` elsewhere (`PiLp.inner_single_left_eq_inner`),
  `(K^m)ᗮ = (Kᗮ)^m` for every subspace `K` (`PiLp.orthogonal_piSubmodule`), and for a Hilbert
  space `E` the dual of `E^m` is `(E^*)^m` isometrically, the functional `ℓ` going to
  `(ℓ ∘ ι_i)_i` (`PiLp.strongDualEquiv`).

On the plain product `Fin m → X` Mathlib has the linear maps (`LinearMap.compLeft`,
`ContinuousLinearMap.piMap`, `ContinuousLinearEquiv.piCongrRight`), their kernels and ranges
(`LinearMap.ker_compLeft`, `LinearMap.range_compLeft`) and the submodule `Submodule.pi`.
`PiLp.compLeftL` and `PiLp.congrRightL` are `ContinuousLinearMap.piMap` and
`ContinuousLinearEquiv.piCongrRight` transported by `PiLp.continuousLinearEquiv`,
`PiLp.piSubmodule` is `Submodule.pi` pulled back by `WithLp.linearEquiv`, and the semilinear
`PiLp.congrRightSL` is built directly.
-/

@[expose] public section

open scoped InnerProductSpace

namespace PiLp

/-! ### Componentwise maps -/

section CompLeft

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
  [NormedSpace ℂ Y]

/-- **A bounded operator acting componentwise** on the finite `L_2` sums `X^m → Y^m`,
`(x_1, …, x_m) ↦ (f x_1, …, f x_m)`: Mathlib's `ContinuousLinearMap.piMap` on `Fin m → X`,
transported to `WithLp 2` by `PiLp.continuousLinearEquiv`, the bounded form of Mathlib's
`LinearMap.compLeft`. Its norm is at most `‖f‖` (`PiLp.norm_compLeftL_le`). -/
noncomputable def compLeftL (m : ℕ) (f : X →L[ℂ] Y) :
    WithLp 2 (Fin m → X) →L[ℂ] WithLp 2 (Fin m → Y) :=
  ((PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin m => Y).symm :
      (Fin m → Y) →L[ℂ] WithLp 2 (Fin m → Y)) ∘L
    ContinuousLinearMap.piMap (fun _ : Fin m => f) ∘L
      (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin m => X :
        WithLp 2 (Fin m → X) →L[ℂ] (Fin m → X))

/-- The `i`-th component of `compLeftL m f x` is `f x_i`. -/
@[simp]
theorem compLeftL_apply (m : ℕ) (f : X →L[ℂ] Y) (x : WithLp 2 (Fin m → X)) (i : Fin m) :
    compLeftL m f x i = f (x i) :=
  rfl

/-- **The componentwise operator has norm at most `‖f‖`**:
`‖compLeftL m f x‖² = ∑_i ‖f x_i‖² ≤ ‖f‖² ∑_i ‖x_i‖² = ‖f‖² ‖x‖²` (Mathlib's
`PiLp.norm_sq_eq_of_L2`, `ContinuousLinearMap.opNorm_le_bound`). -/
theorem norm_compLeftL_le (m : ℕ) (f : X →L[ℂ] Y) : ‖compLeftL m f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun x => ?_
  have h : ‖compLeftL m f x‖ ^ 2 ≤ (‖f‖ * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [compLeftL_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (f.le_opNorm (x i)) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- **A componentwise isometry is an isometry**: if `‖f x‖ = ‖x‖` for every `x ∈ X`, then
`‖compLeftL m f x‖² = ∑_i ‖f x_i‖² = ∑_i ‖x_i‖² = ‖x‖²` (Mathlib's `PiLp.norm_eq_of_L2`). -/
theorem norm_compLeftL_apply (m : ℕ) {f : X →L[ℂ] Y} (hf : ∀ x, ‖f x‖ = ‖x‖)
    (x : WithLp 2 (Fin m → X)) : ‖compLeftL m f x‖ = ‖x‖ := by
  simp only [PiLp.norm_eq_of_L2, compLeftL_apply, hf]

/-- **A componentwise operator is onto if `f` is**: a preimage of `y` is a tuple of preimages of
the components. On the plain product `Fin m → X` this is Mathlib's
`Function.Surjective.piMap`. -/
theorem compLeftL_surjective (m : ℕ) {f : X →L[ℂ] Y} (hf : Function.Surjective f) :
    Function.Surjective (compLeftL m f) := fun y =>
  ⟨WithLp.toLp 2 fun i => (hf (y i)).choose, PiLp.ext fun i => (hf (y i)).choose_spec⟩

/-- **An isomorphism acting componentwise** on the finite `L_2` sums, `X^m ≅ Y^m`: Mathlib's
`ContinuousLinearEquiv.piCongrRight` on `Fin m → X`, transported to `WithLp 2` by
`PiLp.continuousLinearEquiv`. -/
noncomputable def congrRightL (m : ℕ) (e : X ≃L[ℂ] Y) :
    WithLp 2 (Fin m → X) ≃L[ℂ] WithLp 2 (Fin m → Y) :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin m => X).trans
    ((ContinuousLinearEquiv.piCongrRight fun _ : Fin m => e).trans
      (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin m => Y).symm)

/-- The `i`-th component of `congrRightL m e x` is `e x_i`. -/
@[simp]
theorem congrRightL_apply (m : ℕ) (e : X ≃L[ℂ] Y) (x : WithLp 2 (Fin m → X)) (i : Fin m) :
    congrRightL m e x i = e (x i) :=
  rfl

/-- The `i`-th component of `(congrRightL m e)⁻¹ y` is `e⁻¹ y_i`. -/
@[simp]
theorem congrRightL_symm_apply (m : ℕ) (e : X ≃L[ℂ] Y) (y : WithLp 2 (Fin m → Y))
    (i : Fin m) : (congrRightL m e).symm y i = e.symm (y i) :=
  rfl

/-- **A semilinear isometric isomorphism acting componentwise** on the finite `L_2` sums,
`X^m ≅ Y^m`, for a ring automorphism `σ` of `ℂ` such as complex conjugation: the norm is kept since
`‖x‖² = ∑_i ‖x_i‖²` (Mathlib's `PiLp.norm_eq_of_L2`). Mathlib's
`LinearIsometryEquiv.piLpCongrRight` is the linear case. -/
noncomputable def congrRightSL {σ σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (m : ℕ) (e : X ≃ₛₗᵢ[σ] Y) : WithLp 2 (Fin m → X) ≃ₛₗᵢ[σ] WithLp 2 (Fin m → Y) where
  toFun x := WithLp.toLp 2 fun i => e (x i)
  invFun y := WithLp.toLp 2 fun i => e.symm (y i)
  map_add' x y := PiLp.ext fun i => e.map_add (x i) (y i)
  map_smul' c x := PiLp.ext fun i => e.map_smulₛₗ c (x i)
  left_inv x := PiLp.ext fun i => e.symm_apply_apply (x i)
  right_inv y := PiLp.ext fun i => e.apply_symm_apply (y i)
  norm_map' x := by
    simp only [PiLp.norm_eq_of_L2, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      LinearIsometryEquiv.norm_map]

/-- The `i`-th component of `congrRightSL m e x` is `e x_i`. -/
@[simp]
theorem congrRightSL_apply {σ σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (m : ℕ) (e : X ≃ₛₗᵢ[σ] Y) (x : WithLp 2 (Fin m → X)) (i : Fin m) :
    congrRightSL m e x i = e (x i) :=
  rfl

/-- **The subspace `K^m`** of the finite `L_2` sum `X^m`: the tuples whose components all lie in
`K` (`PiLp.mem_piSubmodule`), Mathlib's `Submodule.pi` transported to `WithLp 2`. -/
noncomputable def piSubmodule (m : ℕ) (K : Submodule ℂ X) :
    Submodule ℂ (WithLp 2 (Fin m → X)) :=
  (Submodule.pi Set.univ fun _ : Fin m => K).comap
    (WithLp.linearEquiv 2 ℂ (Fin m → X)).toLinearMap

/-- `x ∈ K^m` iff every component `x_i` lies in `K`, the `WithLp 2` form of Mathlib's
`Submodule.mem_pi`. -/
@[simp]
theorem mem_piSubmodule {m : ℕ} {K : Submodule ℂ X} {x : WithLp 2 (Fin m → X)} :
    x ∈ piSubmodule m K ↔ ∀ i, x i ∈ K := by
  simp only [piSubmodule, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  rfl

/-- **The kernel of a componentwise operator** is `(ker f)^m`: `compLeftL m f x = 0` iff
`f x_i = 0` for every `i`. On the plain product `Fin m → X` this is Mathlib's
`LinearMap.ker_compLeft`. -/
theorem ker_compLeftL (m : ℕ) (f : X →L[ℂ] Y) : (compLeftL m f).ker = piSubmodule m f.ker := by
  ext x
  rw [LinearMap.mem_ker, mem_piSubmodule]
  refine ⟨fun h i => ?_, fun h => PiLp.ext fun i => ?_⟩
  · exact congrArg (fun y : WithLp 2 (Fin m → Y) => y i) h
  · exact h i

/-- **The range of a componentwise operator** is `(range f)^m`: a tuple lies in the range iff each
component lies in the range of `f`, a preimage being a tuple of preimages of the components. On the
plain product `Fin m → X` this is Mathlib's `LinearMap.range_compLeft`. -/
theorem range_compLeftL (m : ℕ) (f : X →L[ℂ] Y) :
    (compLeftL m f).range = piSubmodule m f.range := by
  ext y
  rw [LinearMap.mem_range, mem_piSubmodule]
  refine ⟨fun ⟨x, hx⟩ i => ⟨x i, ?_⟩, fun h => ?_⟩
  · rw [← hx]
    rfl
  · choose x hx using fun i => LinearMap.mem_range.1 (h i)
    exact ⟨WithLp.toLp 2 x, PiLp.ext fun i => hx i⟩

/-- **The range of the componentwise inclusion of a subspace** `K ⊆ X` is `K^m`
(`PiLp.range_compLeftL` and Mathlib's `Submodule.range_subtype`). -/
theorem range_compLeftL_subtypeL (m : ℕ) (K : Submodule ℂ X) :
    (compLeftL m K.subtypeL).range = piSubmodule m K := by
  rw [range_compLeftL]
  exact congrArg (piSubmodule m) K.range_subtype

end CompLeft

/-! ### Orthogonal complements and duals -/

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Inner products with a single component**: in the inner product space `E^m`,
`⟪ι_i a, x⟫ = ⟪a, x_i⟫` for the tuple `ι_i a` with `a` at `i` and `0` elsewhere (Mathlib's
`PiLp.inner_apply`; Mathlib has the identity for `EuclideanSpace` as
`EuclideanSpace.inner_single_left`, for `ℓ_2` sums as `lp.inner_single_left` and for finite sums
of Hilbert `C⋆`-modules as `WithCStarModule.inner_single_left`). -/
theorem inner_single_left_eq_inner (m : ℕ) (i : Fin m) (a : E) (x : WithLp 2 (Fin m → E)) :
    ⟪(PiLp.single 2 i a : WithLp 2 (Fin m → E)), x⟫_ℂ = ⟪a, x i⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i
    (fun j _ hj => by rw [PiLp.single_eq_of_ne (p := 2) hj, inner_zero_left])
    (fun hi => absurd (Finset.mem_univ i) hi), PiLp.single_eq_same]

/-- **Inner products with a single component, on the right**: `⟪x, ι_i a⟫ = ⟪x_i, a⟫`. -/
theorem inner_single_right_eq_inner (m : ℕ) (i : Fin m) (a : E) (x : WithLp 2 (Fin m → E)) :
    ⟪x, (PiLp.single 2 i a : WithLp 2 (Fin m → E))⟫_ℂ = ⟪x i, a⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i
    (fun j _ hj => by rw [PiLp.single_eq_of_ne (p := 2) hj, inner_zero_right])
    (fun hi => absurd (Finset.mem_univ i) hi), PiLp.single_eq_same]

/-- **`(K^m)ᗮ = (Kᗮ)^m`** in the inner product space `E^m`, for every subspace `K ⊆ E`, closed or
not: `x ⊥ K^m` forces `x_i ⊥ k` by testing against the tuple `ι_i k ∈ K^m`
(`PiLp.inner_single_left_eq_inner`), and conversely `⟪y, x⟫ = ∑_i ⟪y_i, x_i⟫ = 0` for `y ∈ K^m`
if every `x_i ⊥ K` (Mathlib's `PiLp.inner_apply`). -/
theorem orthogonal_piSubmodule (m : ℕ) (K : Submodule ℂ E) :
    (piSubmodule m K)ᗮ = piSubmodule m Kᗮ := by
  ext x
  rw [mem_piSubmodule, Submodule.mem_orthogonal]
  refine ⟨fun h i => (Submodule.mem_orthogonal _ _).2 fun k hk => ?_, fun h y hy => ?_⟩
  · rw [← inner_single_left_eq_inner m i k x]
    refine h _ (mem_piSubmodule.2 fun j => ?_)
    by_cases hj : j = i
    · subst hj
      rwa [PiLp.single_eq_same]
    · rw [PiLp.single_eq_of_ne (p := 2) hj]
      exact K.zero_mem
  · rw [PiLp.inner_apply]
    exact Finset.sum_eq_zero fun i _ =>
      Submodule.inner_right_of_mem_orthogonal (mem_piSubmodule.1 hy i) (h i)

variable (E) in
/-- **The dual of a finite `L_2` sum**: for a Hilbert space `E`, the dual of `E^m` is isometrically
isomorphic to `(E^*)^m`, the functional `ℓ` going to `(ℓ ∘ ι_i)_i`
(`PiLp.strongDualEquiv_apply`). It is the inverse of Riesz's map on `E^m`
(`(InnerProductSpace.toDual ℂ _).symm`, taking `ℓ` to its representing vector) followed by
Riesz's map on each component (`PiLp.congrRightSL m (InnerProductSpace.toDual ℂ E)`); both are
conjugate-linear, so the composite is linear. The space `E` is an explicit argument, as in
`InnerProductSpace.toDual`. -/
noncomputable def strongDualEquiv [CompleteSpace E] (m : ℕ) :
    StrongDual ℂ (WithLp 2 (Fin m → E)) ≃ₗᵢ[ℂ] WithLp 2 (Fin m → StrongDual ℂ E) :=
  (InnerProductSpace.toDual ℂ (WithLp 2 (Fin m → E))).symm.trans
    (congrRightSL m (InnerProductSpace.toDual ℂ E))

/-- The `i`-th component of the image of `ℓ` is `a ↦ ℓ(ι_i a)`, with Riesz's representation
(Mathlib's `InnerProductSpace.toDual_symm_apply`) and `PiLp.inner_single_right_eq_inner`. -/
theorem strongDualEquiv_apply (m : ℕ) [CompleteSpace E]
    (ℓ : StrongDual ℂ (WithLp 2 (Fin m → E))) (i : Fin m) (a : E) :
    strongDualEquiv E m ℓ i a = ℓ (PiLp.single 2 i a : WithLp 2 (Fin m → E)) := by
  rw [strongDualEquiv, LinearIsometryEquiv.trans_apply, congrRightSL_apply,
    InnerProductSpace.toDual_apply_apply, ← inner_single_right_eq_inner,
    InnerProductSpace.toDual_symm_apply]

end InnerProduct

end PiLp
