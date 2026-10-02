/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Cube.Modulus
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Isotropic differences and their expansion into coordinate differences

The **isotropic difference** of order `r` with step `h ∈ ℝ^d`,
`Δ_h^r f(x) = ∑_k (-1)^(r-k) C(r,k) f(x + kh)` (`Cube.isoDiff`, `Cube.isoDiff_apply`), moves all
coordinates at once. It is expanded into differences in single coordinates through the algebra
of translations: the commutative algebra `ℂ[ℝ^d]` (Mathlib's `AddMonoidAlgebra`) acts on
functions on `ℝ^d` by an algebra homomorphism (`Cube.diffAct`, from Mathlib's
`AddMonoidAlgebra.lift`), the generator `δ_v` by the translation `τ_v f(x) = f(x + v)`
(`Cube.transl`). Then `Δ_h^r = (δ_h - 1)^r` (`Cube.isoDiff_eq_diffAct`), and identities between
differences become ring identities in `ℂ[ℝ^d]`.

With `δ_i = δ_{h_i e_i}`, `δ_h = ∏_i δ_i`, and `δ_h - 1 = ∑_i (δ_i - 1) ∏_{j<i} δ_j` (Mathlib's
`Finset.prod_add_ordered`). The `r`-th power is a sum over `α : Fin r → Fin d`,
`(δ_h - 1)^r = ∑_α δ_{s_α} ∏_i (δ_i - 1)^{m_i(α)}` with `m_i(α) = #α⁻¹(i)`
(`Cube.single_sub_one_pow_eq_sum`), so
`Δ_h^r f(x) = ∑_α M_{m(α)} f(x + s_α)` (`Cube.isoDiff_eq_sum`): a sum of `d^r` mixed coordinate
differences `M_m f = Δ^{m_0}_{h_0 e_0} ⋯ Δ^{m_{d-1}}_{h_{d-1} e_{d-1}} f` (`Cube.mixedDiff`) of total
order `∑_i m_i(α) = r` (`Cube.sum_count`), at points shifted by `(s_α)_i = h_i #{l : i < α_l}`
(`Cube.shiftVec`, `Cube.shiftVec_apply`).

The slices in coordinate `i` of a mixed difference in other coordinates are combinations of
slices of `f` (`Cube.slice_mixedDiff_mem`), so they stay in every subspace of functions of one
variable that contains the slices of `f`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Cube

open Interval

variable {d : ℕ}

/-! ### Translations and the translation algebra -/

/-- The **translation** `τ_v f(x) = f(x + v)`, a linear map of functions on `ℝ^d`. -/
def transl (v : Fin d → ℝ) : Module.End ℂ ((Fin d → ℝ) → ℂ) where
  toFun f x := f (x + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `τ_v f(x) = f(x + v)`. -/
@[simp] theorem transl_apply (v : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    transl v f x = f (x + v) := rfl

/-- The translations form a monoid homomorphism from `ℝ^d`, written multiplicatively. -/
def translHom : Multiplicative (Fin d → ℝ) →* Module.End ℂ ((Fin d → ℝ) → ℂ) where
  toFun v := transl v.toAdd
  map_one' := by
    ext f x
    simp
  map_mul' v w := by
    ext f x
    simp [Module.End.mul_apply, add_assoc]

/-- The **action of the translation algebra** `ℂ[ℝ^d]` on functions on `ℝ^d`: `δ_v` acts by the
translation `τ_v` (Mathlib's `AddMonoidAlgebra.lift`). -/
noncomputable def diffAct :
    AddMonoidAlgebra ℂ (Fin d → ℝ) →ₐ[ℂ] Module.End ℂ ((Fin d → ℝ) → ℂ) :=
  AddMonoidAlgebra.lift ℂ (Module.End ℂ ((Fin d → ℝ) → ℂ)) (Fin d → ℝ) translHom

/-- `c δ_v` acts by `c τ_v`. -/
theorem diffAct_single (v : Fin d → ℝ) (c : ℂ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    diffAct (AddMonoidAlgebra.single v c) f x = c * f (x + v) := by
  rw [diffAct, AddMonoidAlgebra.lift_single]
  rfl

/-- `δ_v` acts by the translation `τ_v`. -/
theorem diffAct_single_one (v : Fin d → ℝ) :
    diffAct (AddMonoidAlgebra.single v (1 : ℂ)) = transl v := by
  ext f x
  rw [diffAct_single, one_mul, transl_apply]

/-! ### Isotropic differences -/

/-- The **isotropic difference** of order `r` with step `h ∈ ℝ^d`, the `r`-fold iterate of the
forward difference `f ↦ f(· + h) - f` (Mathlib's `fwdDiff`). -/
noncomputable def isoDiff (r : ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  (fwdDiff h)^[r] f

/-- `Δ_h^r f(x) = ∑_{k ≤ r} (-1)^(r-k) C(r,k) f(x + kh)`. -/
theorem isoDiff_apply (r : ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    isoDiff r h f x = ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (x + (k : ℝ) • h) := by
  rw [isoDiff, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  push_cast
  ring

/-- **The isotropic difference is a power in the translation algebra**: `Δ_h^r = (δ_h - 1)^r`. -/
theorem isoDiff_eq_diffAct (r : ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) :
    isoDiff r h f = diffAct ((AddMonoidAlgebra.single h (1 : ℂ) - 1) ^ r) f := by
  have hfwd : ⇑(diffAct (AddMonoidAlgebra.single h (1 : ℂ) - 1)) = fwdDiff h := by
    funext g x
    rw [map_sub, map_one, diffAct_single_one, LinearMap.sub_apply, Pi.sub_apply, transl_apply,
      Module.End.one_apply]
    rfl
  rw [map_pow, Module.End.pow_apply, hfwd, isoDiff]

/-- Isotropic differences are linear. -/
theorem isoDiff_add (r : ℕ) (h : Fin d → ℝ) (f g : (Fin d → ℝ) → ℂ) :
    isoDiff r h (f + g) = isoDiff r h f + isoDiff r h g := by
  rw [isoDiff_eq_diffAct, isoDiff_eq_diffAct, isoDiff_eq_diffAct, map_add]

/-- **Isotropic differences in a coordinate direction** are the coordinate differences:
`Δ^r_{t e_i} f = Δ^r_{t e_i} f` of `Cube.cubeDiff`. -/
theorem isoDiff_single (r : ℕ) (i : Fin d) (t : ℝ) (f : (Fin d → ℝ) → ℂ) :
    isoDiff r (Pi.single i t) f = cubeDiff r t i f := by
  funext x
  rw [isoDiff_apply, cubeDiff_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  funext c
  by_cases hc : c = i
  · subst hc
    simp
  · simp [hc]

/-- Isotropic differences of measurable functions are measurable. -/
theorem measurable_isoDiff {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) (r : ℕ)
    (h : Fin d → ℝ) : Measurable (isoDiff r h f) := by
  have : isoDiff r h f = fun x => ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (x + (k : ℝ) • h) :=
    funext fun x => isoDiff_apply r h f x
  rw [this]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (hf.comp (measurable_add_const _))

/-! ### Mixed coordinate differences -/

/-- The **mixed coordinate difference** along a list of coordinates: the difference of order
`m_i` with step `h_i` in each coordinate `i` of the list, the last one first. -/
noncomputable def mixedDiff (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d))
    (f : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  l.foldr (fun i g => cubeDiff (m i) (h i) i g) f

/-- The mixed difference along the empty list is the function itself. -/
theorem mixedDiff_nil (m : Fin d → ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) :
    mixedDiff m h [] f = f := rfl

/-- The mixed difference along `i :: l`. -/
theorem mixedDiff_cons (m : Fin d → ℕ) (h : Fin d → ℝ) (i : Fin d) (l : List (Fin d))
    (f : (Fin d → ℝ) → ℂ) :
    mixedDiff m h (i :: l) f = cubeDiff (m i) (h i) i (mixedDiff m h l f) := rfl

/-- Mixed differences of measurable functions are measurable. -/
theorem measurable_mixedDiff (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d))
    {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) : Measurable (mixedDiff m h l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact measurable_cubeDiff ih _ _ i

/-- The element `δ_{h_i e_i} - 1` of the translation algebra, the first difference in
coordinate `i`. -/
noncomputable def coordElem (h : Fin d → ℝ) (i : Fin d) : AddMonoidAlgebra ℂ (Fin d → ℝ) :=
  AddMonoidAlgebra.single (Pi.single i (h i)) 1 - 1

/-- `(δ_{h_i e_i} - 1)^m` acts by the coordinate difference `Δ^m_{h_i e_i}`. -/
theorem diffAct_coordElem_pow (h : Fin d → ℝ) (i : Fin d) (m : ℕ) (f : (Fin d → ℝ) → ℂ) :
    diffAct (coordElem h i ^ m) f = cubeDiff m (h i) i f := by
  rw [coordElem, ← isoDiff_eq_diffAct, isoDiff_single]

/-- **Products of coordinate elements act by mixed differences**. -/
theorem diffAct_list_prod (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d))
    (f : (Fin d → ℝ) → ℂ) :
    diffAct ((l.map fun i => coordElem h i ^ m i).prod) f = mixedDiff m h l f := by
  induction l with
  | nil => simp [mixedDiff_nil]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih,
      diffAct_coordElem_pow, mixedDiff_cons]

/-! ### The expansion -/

/-- The multiplicities `m_i(α) = #{l : α_l = i}` of a word `α : Fin r → Fin d`. -/
def count {r : ℕ} (α : Fin r → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun l => α l = i).card

/-- The multiplicities of a word add up to its length. -/
theorem sum_count {r : ℕ} (α : Fin r → Fin d) : ∑ i, count α i = r := by
  simp only [count]
  rw [← Finset.card_eq_sum_card_fiberwise (fun l _ => Finset.mem_univ (α l)), Finset.card_univ,
    Fintype.card_fin]

/-- The vector `∑_{j < i} h_j e_j`. -/
def lowerVec (h : Fin d → ℝ) (i : Fin d) : Fin d → ℝ := fun c => if c < i then h c else 0

/-- The shift `s_α = ∑_l ∑_{j < α_l} h_j e_j` of the term of a word `α`. -/
def shiftVec {r : ℕ} (h : Fin d → ℝ) (α : Fin r → Fin d) : Fin d → ℝ := ∑ l, lowerVec h (α l)

/-- The coordinates of the shift: `(s_α)_c = #{l : c < α_l} h_c`. -/
theorem shiftVec_apply {r : ℕ} (h : Fin d → ℝ) (α : Fin r → Fin d) (c : Fin d) :
    shiftVec h α c = (Finset.univ.filter fun l => c < α l).card * h c := by
  simp only [shiftVec, lowerVec, Finset.sum_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The shift and the multiplicity of a coordinate add up to at most the length of the word:
`#{l : c < α_l} + #{l : α_l = c} ≤ r`. -/
theorem card_lt_add_count_le {r : ℕ} (α : Fin r → Fin d) (c : Fin d) :
    (Finset.univ.filter fun l => c < α l).card + count α c ≤ r := by
  rw [count, ← Finset.card_union_of_disjoint]
  · calc _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_univ _
      _ = r := by rw [Finset.card_univ, Fintype.card_fin]
  · rw [Finset.disjoint_filter]
    intro l _ hl heq
    rw [heq] at hl
    exact lt_irrefl c hl

/-- `δ_{v + w} = δ_v δ_w`. -/
theorem single_add_one (v w : Fin d → ℝ) :
    AddMonoidAlgebra.single (v + w) (1 : ℂ) =
      AddMonoidAlgebra.single v 1 * AddMonoidAlgebra.single w 1 := by
  rw [AddMonoidAlgebra.single_mul_single, one_mul]

/-- `δ_{∑ v_i} = ∏ δ_{v_i}`. -/
theorem single_sum_one {ι : Type*} (s : Finset ι) (v : ι → Fin d → ℝ) :
    AddMonoidAlgebra.single (∑ i ∈ s, v i) (1 : ℂ) = ∏ i ∈ s, AddMonoidAlgebra.single (v i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, AddMonoidAlgebra.one_def]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, single_add_one, ih]

/-- The lower products: `∏_{j < i} δ_{h_j e_j} = δ_{∑_{j<i} h_j e_j}`. -/
theorem prod_lt_single (h : Fin d → ℝ) (i : Fin d) :
    ∏ j ∈ Finset.univ.filter (· < i), AddMonoidAlgebra.single (Pi.single j (h j)) (1 : ℂ) =
      AddMonoidAlgebra.single (lowerVec h i) 1 := by
  rw [← single_sum_one]
  congr 1
  funext c
  simp only [lowerVec, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp

/-- **The first-order telescoping**: `δ_h - 1 = ∑_i (δ_{h_i e_i} - 1) δ_{∑_{j<i} h_j e_j}`
(Mathlib's `Finset.prod_add_ordered` for `∏_i (1 + (δ_{h_i e_i} - 1))`). -/
theorem single_sub_one_eq_sum (h : Fin d → ℝ) :
    AddMonoidAlgebra.single h (1 : ℂ) - 1 =
      ∑ i, coordElem h i * AddMonoidAlgebra.single (lowerVec h i) 1 := by
  have hprod : AddMonoidAlgebra.single h (1 : ℂ) =
      ∏ i, (1 + coordElem h i) := by
    conv_lhs => rw [← Finset.univ_sum_single h]
    rw [single_sum_one]
    exact Finset.prod_congr rfl fun i _ => by rw [coordElem, add_sub_cancel]
  rw [hprod, Finset.prod_add_ordered]
  simp only [Finset.prod_const_one, mul_one, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← prod_lt_single]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [coordElem, add_sub_cancel]

/-- **The expansion in the translation algebra**:
`(δ_h - 1)^r = ∑_α δ_{s_α} ∏_i (δ_{h_i e_i} - 1)^{m_i(α)}`, summed over the words
`α : Fin r → Fin d`. -/
theorem single_sub_one_pow_eq_sum (r : ℕ) (h : Fin d → ℝ) :
    (AddMonoidAlgebra.single h (1 : ℂ) - 1) ^ r = ∑ α : Fin r → Fin d,
      AddMonoidAlgebra.single (shiftVec h α) 1 * ∏ i, coordElem h i ^ count α i := by
  classical
  rw [single_sub_one_eq_sum, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  · rw [shiftVec, single_sum_one]
  · rw [← Finset.prod_fiberwise Finset.univ α fun l => coordElem h (α l)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.1 hl).2],
      Finset.prod_const, count]

/-- **The isotropic difference as a sum of mixed coordinate differences**:
`Δ_h^r f(x) = ∑_α M_{m(α)} f(x + s_α)`, summed over the words `α : Fin r → Fin d`, with the
multiplicities `m_i(α)` and the shifts `s_α`. -/
theorem isoDiff_eq_sum (r : ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    isoDiff r h f x = ∑ α : Fin r → Fin d,
      mixedDiff (count α) h (List.finRange d) f (x + shiftVec h α) := by
  rw [isoDiff_eq_diffAct, single_sub_one_pow_eq_sum, map_sum, LinearMap.sum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, Module.End.mul_apply, diffAct_single_one, transl_apply, Fin.prod_univ_def,
    diffAct_list_prod]

/-! ### Slices of mixed differences -/

/-- **Slices of coordinate differences in other coordinates**: for `c ≠ i`, the slice in
coordinate `i` of `Δ^m_{t e_c} G` is a combination of slices of `G` in coordinate `i`. -/
theorem slice_cubeDiff_of_ne (m : ℕ) (t : ℝ) {c i : Fin d} (hci : c ≠ i)
    (G : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    slice (cubeDiff m t c G) x i = ∑ k ∈ Finset.range (m + 1),
      ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) •
        slice G (Function.update x c (x c + k * t)) i := by
  funext s
  rw [Finset.sum_apply]
  simp only [slice, cubeDiff_eq, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Function.update_of_ne hci, Function.update_comm hci]

/-- **Slices of mixed differences stay in a subspace**: if every slice of `f` in coordinate `i`
lies in a subspace `V` of functions of one variable, so does every slice in coordinate `i` of a
mixed difference along a list of coordinates `≠ i`. -/
theorem slice_mixedDiff_mem (V : Submodule ℂ (ℝ → ℂ)) (m : Fin d → ℕ) (h : Fin d → ℝ)
    {i : Fin d} {l : List (Fin d)} (hl : i ∉ l) {f : (Fin d → ℝ) → ℂ}
    (hf : ∀ x, slice f x i ∈ V) (x : Fin d → ℝ) : slice (mixedDiff m h l f) x i ∈ V := by
  induction l generalizing x with
  | nil => exact hf x
  | cons c l ih =>
    have hci : c ≠ i := fun h => hl (h ▸ List.mem_cons_self)
    have hl' : i ∉ l := fun h => hl (List.mem_cons_of_mem c h)
    rw [mixedDiff_cons, slice_cubeDiff_of_ne _ _ hci]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ih hl' _)

end Cube
