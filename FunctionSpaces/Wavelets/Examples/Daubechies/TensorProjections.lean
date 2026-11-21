/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.Daubechies.TensorExpansion

/-!
# The tensor Daubechies multiresolution analysis on `ℝ^d`

For a Daubechies mask of order `N ≥ 2`, the tensor scaling function `Φ = Ψ^∅` and the tensor
wavelets `Ψ^e`, `e ≠ ∅` (`Daubechies.tensorGen`), form two families of generators on `ℝ^d`:
the scaling family with one member (`Daubechies.tensorScalingFamily`) and the wavelet family
indexed by the nonempty sets of coordinates (`Daubechies.tensorWaveletFamily`). With the
dilated and translated copies `G_{j,k}(x) = 2^(jd/2) G(2^j x - k)` of
`FunctionSpaces.Wavelets.Examples.Daubechies.TensorExpansion`, the **projection of level `j`** is

`P_j f = ∑_{k ∈ ℤ^d} ⟨f, Φ_{j,k}⟩ Φ_{j,k}` (`Daubechies.tensorProjFun`, on `L_p`
`Daubechies.tensorProj`),

and the **wavelet part of level `j`** is `Q_j f = ∑_{e ≠ ∅} ∑_k ⟨f, Ψ^e_{j,k}⟩ Ψ^e_{j,k}`
(`Daubechies.tensorDetailFun`).

* **Kernels.** For a finite family of continuous generators vanishing outside a cube, the
  expansion of the coefficients of a locally integrable `f` is the integral of `f` against the
  kernel `K_j(x, y) = ∑_{(ν,k)} G_{ν,j,k}(x) conj G_{ν,j,k}(y)` (`Daubechies.expansionKernel`,
  `Daubechies.tensorExpand_tensorCoeff_eq_integral`). For a tensor product the kernel is the
  product of the one-dimensional kernels (`Daubechies.tsum_tensorScaled_tensorKernel_mul_conj`),
  since a sum over `ℤ^d` of products of finitely supported factors is the product of the sums
  (`Rd.tsum_prod_eq_prod_tsum`).
* **The kernel identity.** In one variable the kernel of level `j + 1` of `φ` is the sum of the
  kernels of level `j` of `φ` and of `ψ` (`Daubechies.tsum_scaled_mul_scaled_succ`). Multiplying
  out the product over the coordinates gives the sum over all sets `e` of coordinates of the
  kernels of `Ψ^e` (`Daubechies.tsum_tensorGen_empty_mul_conj_succ`), so the kernel of `Φ` of
  level `j + 1` is the kernel of `Φ` of level `j` plus the kernel of the wavelets of level `j`
  (`Daubechies.expansionKernel_tensorScalingFamily_succ`).
* **The block identity.** Hence `P_{j+1} f = P_j f + Q_j f` for locally integrable `f`
  (`Daubechies.tensorProjFun_succ_eq_add`) and on `L_p`
  (`Daubechies.tensorProj_succ_sub_tensorProj`).
  The wavelet coefficients of level `j` of an expansion in the `Φ_{j,k}` vanish
  (`Daubechies.tensorCoeff_tensorExpand_eq_zero`), so `P_{j+1} P_j = P_j`
  (`Daubechies.tensorProjFun_succ_tensorProjFun`).
* **Projections and scaling spaces.** On `L_p`, `1 ≤ p < ∞`, the `P_j` are bounded operators,
  uniformly in `j` (`Daubechies.norm_tensorProj_le`), with `P_j P_j = P_j`; their ranges, the
  **scaling spaces** `V_j` (`Daubechies.tensorScalingSpace`), increase with `j`. They form the
  approximation scheme `Daubechies.tensorScheme` with the projection scheme
  `Daubechies.tensorProjectionScheme`.
* **Norms of the blocks.** `‖P_{j+1} f - P_j f‖_p` is comparable with
  `2^(jd(1/2 - 1/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p}` uniformly in `j`
  (`Daubechies.enorm_tensorBlock_equiv`), and `‖P_0 f‖_p` with `‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p}`
  (`Daubechies.enorm_tensorProj_zero_equiv`), by the stability of the expansions.
* **The inverse inequality.** If `‖Δ_h^N Φ‖_p ≤ K ‖h‖^θ` for `‖h‖ ≤ 1`, then
  `ω_N(a, 2^(-k))_p ≤ C K 2^(-(k-j)θ) ‖a‖_p` for every `a ∈ V_j` and `k ≥ j`
  (`Daubechies.lpModulus_le_of_mem_tensorScalingSpace`), from Bernstein's inequality for
  expansions (`Daubechies.modulus_tensorExpand_le`). If `φ` has a Bernstein bound of order `θ`
  with differences of order `N` and `0 ≤ θ' ≤ θ`, `θ' < N`, the moduli of the generators give
  such a bound with `θ'` (`Daubechies.eLpNorm_higherDiff_tensorGen_le`), hence the inverse
  inequality of the scheme (`Daubechies.tensor_inverse_scheme`).

The norm on `ℝ^d` is the sup norm.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal ComplexConjugate
open ENNReal (dyadicWeight lqNorm)

/-- **Splitting off the empty set**: for every finite type `α` and `F : Finset α → M`,
`∑_e F(e) = F(∅) + ∑_{e ≠ ∅} F(e)`, the second sum over the subtype of nonempty sets. This is
Mathlib's `Fintype.sum_eq_add_sum_subtype_ne` at `∅`, with `e ≠ ∅` read as `e.Nonempty`
(`Finset.nonempty_iff_ne_empty`). -/
theorem Fintype.sum_finset_eq_add_sum_nonempty {α M : Type*} [Fintype α] [AddCommMonoid M]
    (F : Finset α → M) :
    ∑ e, F e = F ∅ + ∑ e : {e : Finset α // e.Nonempty}, F e := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne F ∅]
  congr 1
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun e => Finset.nonempty_iff_ne_empty.symm)
    _ _ fun _ => rfl

namespace Daubechies

/-! ### Kernels of expansions -/

section Kernels

variable {d : ℕ} {ι : Type*} [Fintype ι] {G : ι → (Fin d → ℝ) → ℂ} {a b : ℝ}

omit [Fintype ι] in
/-- **The kernel of level `j`** of a family of generators `G_ν`, `ν ∈ ι`:
`K_j(x, y) = ∑_{(ν,k) ∈ ι × ℤ^d} G_{ν,j,k}(x) conj G_{ν,j,k}(y)`. For finitely many generators
that vanish outside a cube it is a finite sum at each `x` (`Daubechies.expansionKernel_eq_sum`),
and, if the generators are continuous and `f` is locally integrable, the expansion of the
coefficients of level `j` of `f` is `x ↦ ∫ f(y) K_j(x, y) dy`
(`Daubechies.tensorExpand_tensorCoeff_eq_integral`). -/
noncomputable def expansionKernel (G : ι → (Fin d → ℝ) → ℂ) (j : ℕ) (x y : Fin d → ℝ) : ℂ :=
  ∑' νk : ι × (Fin d → ℤ), tensorScaled (G νk.1) j νk.2 x * conj (tensorScaled (G νk.1) j νk.2 y)

/-- **The kernel is a finite sum at each point**: if every `G_ν` vanishes outside `[a, b]^d`, then
`K_j(x, y)` is the sum over the generators and the positions in the box at `x`
(`Daubechies.tensorBox`). -/
theorem expansionKernel_eq_sum (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) (j : ℕ)
    (x y : Fin d → ℝ) :
    expansionKernel G j x y = ∑ νk ∈ Finset.univ ×ˢ tensorBox a b j x,
      tensorScaled (G νk.1) j νk.2 x * conj (tensorScaled (G νk.1) j νk.2 y) :=
  tsum_eq_sum fun νk hνk => by
    rw [tensorScaled_eq_zero (hsupp νk.1) fun hx => hνk (Finset.mem_product.2
      ⟨Finset.mem_univ _, mem_tensorBox_of_mem_tensorWindow hx⟩), zero_mul]

/-- **The kernel generator by generator**: if every `G_ν` vanishes outside `[a, b]^d`, then
`K_j(x, y) = ∑_ν ∑_{k ∈ ℤ^d} G_{ν,j,k}(x) conj G_{ν,j,k}(y)`
(`Daubechies.expansionKernel_eq_sum`). -/
theorem expansionKernel_eq_sum_tsum (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0)
    (j : ℕ) (x y : Fin d → ℝ) :
    expansionKernel G j x y = ∑ ν, ∑' k : Fin d → ℤ,
      tensorScaled (G ν) j k x * conj (tensorScaled (G ν) j k y) := by
  rw [expansionKernel_eq_sum hsupp, Finset.sum_product]
  refine Finset.sum_congr rfl fun ν _ => (tsum_eq_sum fun k hk => ?_).symm
  rw [tensorScaled_eq_zero (hsupp ν) (fun hx => hk (mem_tensorBox_of_mem_tensorWindow hx)),
    zero_mul]

/-- **The kernel against a locally integrable function is integrable**: if every `G_ν` is
continuous and vanishes outside `[a, b]^d` and `f` is locally integrable, then
`y ↦ f(y) K_j(x, y)` is integrable for every `x`, as a finite sum of the integrable functions
`G_{ν,j,k}(x) f(y) conj G_{ν,j,k}(y)`
(`Daubechies.integrable_mul_conj_tensorScaled_of_locallyIntegrable`). -/
theorem integrable_mul_expansionKernel (hG : ∀ ν, Continuous (G ν))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {f : (Fin d → ℝ) → ℂ}
    (hf : LocallyIntegrable f volume) (j : ℕ) (x : Fin d → ℝ) :
    Integrable fun y => f y * expansionKernel G j x y := by
  simp_rw [expansionKernel_eq_sum hsupp j x, Finset.mul_sum]
  refine integrable_finsetSum _ fun νk _ =>
    ((integrable_mul_conj_tensorScaled_of_locallyIntegrable (hG νk.1) (hsupp νk.1) hf j
      νk.2).const_mul (tensorScaled (G νk.1) j νk.2 x)).congr
      (Eventually.of_forall fun y => ?_)
  ring

/-- **The kernel form of the expansion of the coefficients**: if every `G_ν` is continuous and
vanishes outside `[a, b]^d` and `f` is locally integrable, then for every level `j` and point `x`,
`∑_{(ν,k)} ⟨f, G_{ν,j,k}⟩ G_{ν,j,k}(x) = ∫ f(y) K_j(x, y) dy`. Both sides are finite sums over the
box at `x` (`Daubechies.tensorExpand_eq_sum`, `Daubechies.expansionKernel_eq_sum`), and the
integral is linear on the integrable terms. -/
theorem tensorExpand_tensorCoeff_eq_integral (hG : ∀ ν, Continuous (G ν))
    (hsupp : ∀ ν x, (∃ i, x i ∉ Set.Icc a b) → G ν x = 0) {f : (Fin d → ℝ) → ℂ}
    (hf : LocallyIntegrable f volume) (j : ℕ) (x : Fin d → ℝ) :
    tensorExpand G j (tensorCoeff G j f) x = ∫ y, f y * expansionKernel G j x y := by
  simp_rw [expansionKernel_eq_sum hsupp j x, Finset.mul_sum]
  rw [integral_finsetSum _ fun νk _ =>
    ((integrable_mul_conj_tensorScaled_of_locallyIntegrable (hG νk.1) (hsupp νk.1) hf j
      νk.2).const_mul (tensorScaled (G νk.1) j νk.2 x)).congr
      (Eventually.of_forall fun y => by ring), tensorExpand_eq_sum hsupp]
  refine Finset.sum_congr rfl fun νk _ => ?_
  rw [tensorCoeff, ← integral_mul_const]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

end Kernels

/-! ### Kernels of tensor products -/

section TensorKernels

variable {d : ℕ} {a b : ℝ}

/-- **The kernel of a tensor product is the product of the kernels**: if every `K_i : ℝ → ℂ`
vanishes outside `[a, b]`, then for every level `j` and all `x, y ∈ ℝ^d`,
`∑_{k ∈ ℤ^d} (⊗K)_{j,k}(x) conj (⊗K)_{j,k}(y)` equals
`∏_i ∑_{n ∈ ℤ} (K_i)_{j,n}(x_i) conj (K_i)_{j,n}(y_i)`, with the one-dimensional `(K_i)_{j,n}`
(`Daubechies.scaledFun`). The term of `k` is the product over `i` of the terms of `k_i`
(`Daubechies.tensorScaled_tensorKernel`), each vanishing unless `2^j x_i - k_i ∈ [a, b]`
(`Rd.tsum_prod_eq_prod_tsum`). -/
theorem tsum_tensorScaled_tensorKernel_mul_conj {K : Fin d → ℝ → ℂ}
    (hK : ∀ i t, t ∉ Set.Icc a b → K i t = 0) (j : ℕ) (x y : Fin d → ℝ) :
    ∑' k : Fin d → ℤ, tensorScaled (Rd.tensorKernel K) j k x *
        conj (tensorScaled (Rd.tensorKernel K) j k y) =
      ∏ i, ∑' n : ℤ, scaledFun (K i) j n (x i) * conj (scaledFun (K i) j n (y i)) := by
  simp only [tensorScaled_tensorKernel, Rd.tensorKernel_apply, map_prod,
    ← Finset.prod_mul_distrib]
  exact Rd.tsum_prod_eq_prod_tsum
    (F := fun i n => scaledFun (K i) j n (x i) * conj (scaledFun (K i) j n (y i)))
    (T := fun i => Finset.Icc ⌈(2 : ℝ) ^ j * x i - b⌉ ⌊(2 : ℝ) ^ j * x i - a⌋)
    fun i n hn => by rw [scaledFun_eq_zero (hK i) fun hx => hn (mem_Icc_ceil_floor hx), zero_mul]

variable {N : ℕ} (m : Mask N)

/-- **The kernel of a tensor generator**: for `N ≥ 2`, a set `e` of coordinates, every level `j`
and all `x, y ∈ ℝ^d`,
`∑_k Ψ^e_{j,k}(x) conj Ψ^e_{j,k}(y) = ∏_i k_i(x_i, y_i)` with the one-dimensional kernels
`k_i(s, t) = ∑_n ψ_{j,n}(s) ψ_{j,n}(t)` for `i ∈ e` and `k_i(s, t) = ∑_n φ_{j,n}(s) φ_{j,n}(t)`
otherwise (`Daubechies.tsum_tensorScaled_tensorKernel_mul_conj`; `φ` and `ψ` are real,
`Daubechies.conj_scalingFun`, `Daubechies.conj_wavelet`). -/
theorem tsum_tensorGen_mul_conj (hN : 2 ≤ N) (e : Finset (Fin d)) (j : ℕ) (x y : Fin d → ℝ) :
    ∑' k : Fin d → ℤ, tensorScaled (tensorGen m e) j k x *
        conj (tensorScaled (tensorGen m e) j k y) =
      ∏ i, if i ∈ e then ∑' n : ℤ, waveletScaled m j n (x i) * waveletScaled m j n (y i)
        else ∑' n : ℤ, scaled m j n (x i) * scaled m j n (y i) := by
  rw [tensorGen, tsum_tensorScaled_tensorKernel_mul_conj (a := 1 - N) (b := 2 * N - 1)
    (fun i t ht => ite_wavelet_scalingFun_eq_zero m hN (i ∈ e) ht)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ e
  · simp only [hi, ↓reduceIte, conj_scaledFun (conj_wavelet m)]
  · simp only [hi, ↓reduceIte, conj_scaledFun (conj_scalingFun m)]

/-- **The kernel identity on `ℝ^d`, generator by generator**: for `N ≥ 2`, every level `j` and
all `x, y ∈ ℝ^d`, the kernel of `Φ` of level `j + 1` is the sum over all sets `e` of coordinates
of the kernels of `Ψ^e` of level `j`:
`∑_k Φ_{j+1,k}(x) conj Φ_{j+1,k}(y) = ∑_e ∑_k Ψ^e_{j,k}(x) conj Ψ^e_{j,k}(y)`. Both sides are
products of one-dimensional kernels (`Daubechies.tsum_tensorGen_mul_conj`); in each coordinate
the kernel of `φ` of level `j + 1` is the sum of the kernels of `φ` and `ψ` of level `j`
(`Daubechies.tsum_scaled_mul_scaled_succ`), and the product of the sums is the sum over `e` of
the products with `ψ` in the coordinates of `e` (Mathlib's `Finset.prod_add`). -/
theorem tsum_tensorGen_empty_mul_conj_succ (hN : 2 ≤ N) (j : ℕ) (x y : Fin d → ℝ) :
    ∑' k : Fin d → ℤ, tensorScaled (tensorGen m ∅) (j + 1) k x *
        conj (tensorScaled (tensorGen m ∅) (j + 1) k y) =
      ∑ e : Finset (Fin d), ∑' k : Fin d → ℤ, tensorScaled (tensorGen m e) j k x *
        conj (tensorScaled (tensorGen m e) j k y) := by
  simp_rw [tsum_tensorGen_mul_conj m hN]
  simp only [Finset.notMem_empty, ↓reduceIte, tsum_scaled_mul_scaled_succ m hN j]
  simp_rw [add_comm (∑' k : ℤ, scaled m j k _ * scaled m j k _)]
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sdiff_eq_filter]

end TensorKernels

variable {N : ℕ} (m : Mask N)

section Families

variable {d : ℕ}

/-! ### The scaling family and the wavelet family -/

/-- **The tensor scaling family**: the single generator `Φ = Ψ^∅` (`Daubechies.tensorGen`),
indexed by `Unit`. Its expansions of level `j` are the functions of the scaling space `V_j`. -/
noncomputable abbrev tensorScalingFamily (d : ℕ) : Unit → (Fin d → ℝ) → ℂ :=
  fun _ => tensorGen m ∅

/-- **The tensor wavelet family**: the `2^d - 1` tensor wavelets `Ψ^e` (`Daubechies.tensorGen`),
indexed by the nonempty sets `e` of coordinates. -/
noncomputable abbrev tensorWaveletFamily (d : ℕ) :
    {e : Finset (Fin d) // e.Nonempty} → (Fin d → ℝ) → ℂ :=
  fun e => tensorGen m e.1

/-- **Orthonormality of the scaling family**: for `N ≥ 2`, the integer translates of `Φ` are
orthonormal (`Daubechies.integral_tensorGen_translate_mul_conj_translate` with `e = e' = ∅`). -/
theorem integral_tensorScalingFamily_translate_mul_conj_translate (hN : 2 ≤ N) (ν ν' : Unit)
    (k l : Fin d → ℤ) :
    ∫ x, tensorScalingFamily m d ν (x - fun i => (k i : ℝ)) *
        conj (tensorScalingFamily m d ν' (x - fun i => (l i : ℝ))) =
      if ν = ν' ∧ k = l then 1 else 0 := by
  simpa using integral_tensorGen_translate_mul_conj_translate m hN ∅ ∅ k l

/-- **Orthonormality of the wavelet family**: for `N ≥ 2`, the integer translates of the tensor
wavelets `Ψ^e`, `e ≠ ∅`, are orthonormal
(`Daubechies.integral_tensorGen_translate_mul_conj_translate`). -/
theorem integral_tensorWaveletFamily_translate_mul_conj_translate (hN : 2 ≤ N)
    (e e' : {e : Finset (Fin d) // e.Nonempty}) (k l : Fin d → ℤ) :
    ∫ x, tensorWaveletFamily m d e (x - fun i => (k i : ℝ)) *
        conj (tensorWaveletFamily m d e' (x - fun i => (l i : ℝ))) =
      if e = e' ∧ k = l then 1 else 0 := by
  simpa only [Subtype.ext_iff] using integral_tensorGen_translate_mul_conj_translate m hN e e' k l

/-- **The scaling family is orthogonal to the wavelet family**: for `N ≥ 2`, every integer
translate of `Φ` is orthogonal to every integer translate of every `Ψ^e`, `e ≠ ∅`
(`Daubechies.integral_tensorGen_translate_mul_conj_translate`, since `∅ ≠ e`). -/
theorem integral_tensorScalingFamily_translate_wavelet (hN : 2 ≤ N) (ν : Unit)
    (e : {e : Finset (Fin d) // e.Nonempty}) (k l : Fin d → ℤ) :
    ∫ x, tensorScalingFamily m d ν (x - fun i => (k i : ℝ)) *
        conj (tensorWaveletFamily m d e (x - fun i => (l i : ℝ))) = 0 := by
  rw [integral_tensorGen_translate_mul_conj_translate m hN ∅ e.1 k l]
  exact ite_eq_right_iff.2 fun h => absurd h.1.symm e.2.ne_empty

/-- **The kernel identity**: for `N ≥ 2`, every level `j` and all `x, y ∈ ℝ^d`, the kernel of the
scaling family of level `j + 1` is the kernel of the scaling family of level `j` plus the kernel
of the wavelet family of level `j` (`Daubechies.tsum_tensorGen_empty_mul_conj_succ`, with the
term `e = ∅` split off, `Fintype.sum_finset_eq_add_sum_nonempty`). -/
theorem expansionKernel_tensorScalingFamily_succ (hN : 2 ≤ N) (j : ℕ) (x y : Fin d → ℝ) :
    expansionKernel (tensorScalingFamily m d) (j + 1) x y =
      expansionKernel (tensorScalingFamily m d) j x y +
        expansionKernel (tensorWaveletFamily m d) j x y := by
  have hφ : ∀ ν x, (∃ i, x i ∉ Set.Icc (1 - N : ℝ) (2 * N - 1)) →
      tensorScalingFamily m d ν x = 0 := fun _ _ hx => tensorGen_eq_zero m hN ∅ hx
  have hψ : ∀ e x, (∃ i, x i ∉ Set.Icc (1 - N : ℝ) (2 * N - 1)) →
      tensorWaveletFamily m d e x = 0 := fun e _ hx => tensorGen_eq_zero m hN e.1 hx
  rw [expansionKernel_eq_sum_tsum hφ, expansionKernel_eq_sum_tsum hφ,
    expansionKernel_eq_sum_tsum hψ, Fintype.sum_unique, Fintype.sum_unique,
    tsum_tensorGen_empty_mul_conj_succ m hN, Fintype.sum_finset_eq_add_sum_nonempty]

/-! ### The projections, pointwise -/

/-- **The projection of level `j` on `ℝ^d`, pointwise**: for every `f : ℝ^d → ℂ`,
`P_j f(x) = ∑_{k ∈ ℤ^d} ⟨f, Φ_{j,k}⟩ Φ_{j,k}(x)`, the expansion of level `j` of the coefficients
of `f` in the scaling family. Only finitely many terms are nonzero at each point. -/
noncomputable def tensorProjFun (j : ℕ) (f : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  tensorExpand (tensorScalingFamily m d) j (tensorCoeff (tensorScalingFamily m d) j f)

/-- **The wavelet part of level `j`, pointwise**:
`Q_j f(x) = ∑_{e ≠ ∅} ∑_{k ∈ ℤ^d} ⟨f, Ψ^e_{j,k}⟩ Ψ^e_{j,k}(x)`, the expansion of level `j` of the
coefficients of `f` in the wavelet family. For `N ≥ 2` and locally integrable `f` it is
`P_{j+1} f - P_j f` (`Daubechies.tensorProjFun_succ_eq_add`). -/
noncomputable def tensorDetailFun (j : ℕ) (f : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  tensorExpand (tensorWaveletFamily m d) j (tensorCoeff (tensorWaveletFamily m d) j f)

/-- **The projection is continuous**, for `N ≥ 2`: an expansion in continuous generators
(`Daubechies.continuous_tensorExpand`). -/
theorem continuous_tensorProjFun (hN : 2 ≤ N) (j : ℕ) (f : (Fin d → ℝ) → ℂ) :
    Continuous (tensorProjFun m j f) :=
  continuous_tensorExpand (fun _ => continuous_tensorGen m hN ∅)
    (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx) j _

/-- **The projection depends only on the class of `f`**: if `f = f'` almost everywhere, then
`P_j f = P_j f'` at every point (`Daubechies.tensorCoeff_congr_ae`). -/
theorem tensorProjFun_congr_ae {f f' : (Fin d → ℝ) → ℂ} (h : f =ᵐ[volume] f') (j : ℕ) :
    tensorProjFun m j f = tensorProjFun m j f' := by
  rw [tensorProjFun, tensorProjFun, show tensorCoeff (tensorScalingFamily m d) j f =
    tensorCoeff (tensorScalingFamily m d) j f' from funext fun νk => tensorCoeff_congr_ae h j νk]

/-- **The projection is additive** on locally integrable functions, for `N ≥ 2`
(`Daubechies.tensorCoeff_add`, `Daubechies.tensorExpand_add`). -/
theorem tensorProjFun_add (hN : 2 ≤ N) {f g : (Fin d → ℝ) → ℂ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (j : ℕ) :
    tensorProjFun m j (fun y => f y + g y) =
      fun x => tensorProjFun m j f x + tensorProjFun m j g x := by
  funext x
  have hc : tensorCoeff (tensorScalingFamily m d) j (fun y => f y + g y) = fun νk =>
      tensorCoeff (tensorScalingFamily m d) j f νk + tensorCoeff (tensorScalingFamily m d) j g νk :=
    funext fun νk => tensorCoeff_add
      (integrable_mul_conj_tensorScaled_of_locallyIntegrable (continuous_tensorGen m hN ∅)
        (fun _ hx => tensorGen_eq_zero m hN ∅ hx) hf j νk.2)
      (integrable_mul_conj_tensorScaled_of_locallyIntegrable (continuous_tensorGen m hN ∅)
        (fun _ hx => tensorGen_eq_zero m hN ∅ hx) hg j νk.2)
  rw [tensorProjFun, hc]
  exact tensorExpand_add (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx) j _ _ x

/-- **The projection is homogeneous**: `P_j (z f) = z P_j f` for every `z ∈ ℂ`
(`Daubechies.tensorCoeff_const_mul`, `Daubechies.tensorExpand_const_mul`). -/
theorem tensorProjFun_const_mul (z : ℂ) (f : (Fin d → ℝ) → ℂ) (j : ℕ) :
    tensorProjFun m j (fun y => z * f y) = fun x => z * tensorProjFun m j f x := by
  funext x
  have hc : tensorCoeff (tensorScalingFamily m d) j (fun y => z * f y) =
      fun νk => z * tensorCoeff (tensorScalingFamily m d) j f νk :=
    funext fun νk => tensorCoeff_const_mul z f j νk
  rw [tensorProjFun, hc]
  exact tensorExpand_const_mul j z _ x

/-- **The projection reproduces the expansions in `Φ`**: for `N ≥ 2`, every level `j` and all
coefficients `c`, `P_j (∑ c_k Φ_{j,k}) = ∑ c_k Φ_{j,k}`, since the coefficients are recovered
(`Daubechies.tensorCoeff_tensorExpand`,
`Daubechies.integral_tensorScalingFamily_translate_mul_conj_translate`). -/
theorem tensorProjFun_tensorExpand (hN : 2 ≤ N) (j : ℕ) (c : Unit × (Fin d → ℤ) → ℂ) :
    tensorProjFun m j (tensorExpand (tensorScalingFamily m d) j c) =
      tensorExpand (tensorScalingFamily m d) j c := by
  rw [tensorProjFun, show tensorCoeff (tensorScalingFamily m d) j
      (tensorExpand (tensorScalingFamily m d) j c) = c from
    funext (tensorCoeff_tensorExpand (fun _ => continuous_tensorGen m hN ∅)
      (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx)
      (integral_tensorScalingFamily_translate_mul_conj_translate m hN) j c)]

/-- **The pointwise projection is idempotent**: `P_j (P_j f) = P_j f` for `N ≥ 2`
(`Daubechies.tensorProjFun_tensorExpand`). -/
theorem tensorProjFun_tensorProjFun (hN : 2 ≤ N) (j : ℕ) (f : (Fin d → ℝ) → ℂ) :
    tensorProjFun m j (tensorProjFun m j f) = tensorProjFun m j f :=
  tensorProjFun_tensorExpand m hN j _

/-! ### The block identity -/

/-- **The block identity on `ℝ^d`, pointwise**: for `N ≥ 2`, locally integrable `f`, every level
`j` and every point `x`, `P_{j+1} f(x) = P_j f(x) + Q_j f(x)`. All three are integrals of `f`
against kernels (`Daubechies.tensorExpand_tensorCoeff_eq_integral`), and the kernels satisfy the
kernel identity (`Daubechies.expansionKernel_tensorScalingFamily_succ`). -/
theorem tensorProjFun_succ_eq_add (hN : 2 ≤ N) {f : (Fin d → ℝ) → ℂ}
    (hf : LocallyIntegrable f volume) (j : ℕ) (x : Fin d → ℝ) :
    tensorProjFun m (j + 1) f x = tensorProjFun m j f x + tensorDetailFun m j f x := by
  have hφ : ∀ ν x, (∃ i, x i ∉ Set.Icc (1 - N : ℝ) (2 * N - 1)) →
      tensorScalingFamily m d ν x = 0 := fun _ _ hx => tensorGen_eq_zero m hN ∅ hx
  have hψ : ∀ e x, (∃ i, x i ∉ Set.Icc (1 - N : ℝ) (2 * N - 1)) →
      tensorWaveletFamily m d e x = 0 := fun e _ hx => tensorGen_eq_zero m hN e.1 hx
  have hφc : ∀ ν, Continuous (tensorScalingFamily m d ν) := fun _ => continuous_tensorGen m hN ∅
  have hψc : ∀ e, Continuous (tensorWaveletFamily m d e) := fun e => continuous_tensorGen m hN e.1
  rw [tensorProjFun, tensorProjFun, tensorDetailFun,
    tensorExpand_tensorCoeff_eq_integral hφc hφ hf, tensorExpand_tensorCoeff_eq_integral hφc hφ hf,
    tensorExpand_tensorCoeff_eq_integral hψc hψ hf, ← integral_add
      (integrable_mul_expansionKernel hφc hφ hf j x) (integrable_mul_expansionKernel hψc hψ hf j x)]
  simp_rw [expansionKernel_tensorScalingFamily_succ m hN, mul_add]

/-- **The wavelet coefficients of the projection vanish**: for `N ≥ 2`, every level `j` and every
`f`, `⟨P_j f, Ψ^e_{j,k}⟩ = 0` for every `e ≠ ∅` and `k`, since `P_j f` is an expansion in the
`Φ_{j,k}` and the families are orthogonal (`Daubechies.tensorCoeff_tensorExpand_eq_zero`,
`Daubechies.integral_tensorScalingFamily_translate_wavelet`). -/
theorem tensorCoeff_tensorProjFun_eq_zero (hN : 2 ≤ N) (j : ℕ) (f : (Fin d → ℝ) → ℂ)
    (ek : {e : Finset (Fin d) // e.Nonempty} × (Fin d → ℤ)) :
    tensorCoeff (tensorWaveletFamily m d) j (tensorProjFun m j f) ek = 0 :=
  tensorCoeff_tensorExpand_eq_zero (G := tensorScalingFamily m d) (G' := tensorWaveletFamily m d)
    (a := 1 - N) (b := 2 * N - 1) (fun _ => continuous_tensorGen m hN ∅)
    (fun e => continuous_tensorGen m hN e.1) (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx)
    (fun e _ hx => tensorGen_eq_zero m hN e.1 hx)
    (integral_tensorScalingFamily_translate_wavelet m hN) j _ ek

/-- **The projections of consecutive levels**: `P_{j+1} (P_j f) = P_j f` at every point, for
`N ≥ 2` and every `f`. By the block identity (`Daubechies.tensorProjFun_succ_eq_add`) for the
continuous function `P_j f`, `P_{j+1} (P_j f) = P_j (P_j f) + Q_j (P_j f)`, where
`P_j (P_j f) = P_j f` (`Daubechies.tensorProjFun_tensorProjFun`) and `Q_j (P_j f) = 0`
(`Daubechies.tensorCoeff_tensorProjFun_eq_zero`). -/
theorem tensorProjFun_succ_tensorProjFun (hN : 2 ≤ N) (j : ℕ) (f : (Fin d → ℝ) → ℂ) :
    tensorProjFun m (j + 1) (tensorProjFun m j f) = tensorProjFun m j f := by
  funext x
  rw [tensorProjFun_succ_eq_add m hN (continuous_tensorProjFun m hN j f).locallyIntegrable,
    tensorProjFun_tensorProjFun m hN, tensorDetailFun,
    show tensorCoeff (tensorWaveletFamily m d) j (tensorProjFun m j f) = fun _ => 0 from
      funext (tensorCoeff_tensorProjFun_eq_zero m hN j f)]
  simp [tensorExpand]

/-! ### Bounds -/

/-- **The bound of the projections on `ℝ^d`**: the real number `C C'` with the constants
`C = Daubechies.tensorExpandConst` and `C' = Daubechies.tensorCoeffConst` of the scaling family
and its cube `[1 - N, 2N - 1]^d`. It is the same for every level. -/
noncomputable def tensorProjConst (p : ℝ≥0∞) (d : ℕ) : ℝ :=
  (tensorExpandConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p *
    tensorCoeffConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p).toReal

/-- The bound `tensorProjConst m p d` is nonnegative. -/
theorem tensorProjConst_nonneg (p : ℝ≥0∞) : 0 ≤ tensorProjConst m p d := ENNReal.toReal_nonneg

/-- For `N ≥ 2` and `1 ≤ p` the bound is the product of the two finite constants
(`Daubechies.tensorExpandConst_ne_top`, `Daubechies.tensorCoeffConst_ne_top`). -/
theorem ofReal_tensorProjConst (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    ENNReal.ofReal (tensorProjConst m p d) =
      tensorExpandConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p *
        tensorCoeffConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p :=
  ENNReal.ofReal_toReal (ENNReal.mul_ne_top
    (tensorExpandConst_ne_top _ _ hp1 fun _ => memLp_tensorGen m hN ∅ p)
    (tensorCoeffConst_ne_top _ _ fun _ => memLp_tensorGen m hN ∅ _))

/-- **The projections are bounded on `L_p(ℝ^d)`, uniformly in the level**: for `N ≥ 2`,
`1 ≤ p < ∞`, every a.e. strongly measurable `f` and every level `j`,
`‖P_j f‖_p ≤ C ‖f‖_p` with `C = tensorProjConst m p d`
(`Daubechies.eLpNorm_tensorExpand_tensorCoeff_le`). -/
theorem eLpNorm_tensorProjFun_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    eLpNorm (tensorProjFun m j f) p volume ≤
      ENNReal.ofReal (tensorProjConst m p d) * eLpNorm f p volume := by
  rw [ofReal_tensorProjConst m hN hp1]
  exact eLpNorm_tensorExpand_tensorCoeff_le
    (fun _ => (continuous_tensorGen m hN ∅).aestronglyMeasurable)
    (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx) hp1 hp hf j

/-- **The projection of an `L_p` function lies in `L_p`**, for `N ≥ 2` and `1 ≤ p < ∞`
(`Daubechies.memLp_tensorExpand_tensorCoeff`). -/
theorem memLp_tensorProjFun (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : MemLp f p volume) (j : ℕ) : MemLp (tensorProjFun m j f) p volume :=
  memLp_tensorExpand_tensorCoeff (fun _ => continuous_tensorGen m hN ∅)
    (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx) hp1 hp hf j

/-- **The wavelet part of an `L_p` function lies in `L_p`**, for `N ≥ 2` and `1 ≤ p < ∞`
(`Daubechies.memLp_tensorExpand_tensorCoeff`). -/
theorem memLp_tensorDetailFun (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : (Fin d → ℝ) → ℂ} (hf : MemLp f p volume) (j : ℕ) :
    MemLp (tensorDetailFun m j f) p volume :=
  memLp_tensorExpand_tensorCoeff (G := tensorWaveletFamily m d) (a := 1 - N) (b := 2 * N - 1)
    (fun e => continuous_tensorGen m hN e.1)
    (fun e _ hx => tensorGen_eq_zero m hN e.1 hx) hp1 hp hf j

end Families

/-! ### The projections on `L_p` -/

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {d : ℕ}

variable (p d) in
/-- **The projection of level `j` as a linear map on `L_p(ℝ^d)`**, for `N ≥ 2` and `1 ≤ p < ∞`:
the class of the pointwise projection `P_j f` (`Daubechies.tensorProjFun`) of a representative. -/
noncomputable def tensorProjLinear (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    Lp ℂ p (volume : Measure (Fin d → ℝ)) →ₗ[ℝ] Lp ℂ p (volume : Measure (Fin d → ℝ)) where
  toFun f := (memLp_tensorProjFun m hN Fact.out hp (Lp.memLp f) j).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    rw [tensorProjFun_congr_ae m (Lp.coeFn_add f g) j]
    exact congrFun (tensorProjFun_add m hN ((Lp.memLp f).locallyIntegrable Fact.out)
      ((Lp.memLp g).locallyIntegrable Fact.out) j) x
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    have hcf : ⇑(c • f) =ᵐ[volume] fun y => (c : ℂ) * f y :=
      (Lp.coeFn_smul c f).mono fun y hy => by rw [hy, Pi.smul_apply, Complex.real_smul]
    rw [tensorProjFun_congr_ae m hcf j, tensorProjFun_const_mul, Pi.smul_apply, Complex.real_smul]

variable (p d) in
/-- **The projection of level `j` on `L_p(ℝ^d)`**, for `N ≥ 2` and `1 ≤ p < ∞`:
`P_j f = ∑_{k ∈ ℤ^d} ⟨f, Φ_{j,k}⟩ Φ_{j,k}`, a bounded operator whose norm is at most
`tensorProjConst m p d` for every level (`Daubechies.norm_tensorProj_le`). -/
noncomputable def tensorProj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    Lp ℂ p (volume : Measure (Fin d → ℝ)) →L[ℝ] Lp ℂ p (volume : Measure (Fin d → ℝ)) :=
  LinearMap.mkContinuous (tensorProjLinear m p d hN hp j) (tensorProjConst m p d) fun f => by
    have hmem := memLp_tensorProjFun m hN Fact.out hp (Lp.memLp f) j
    rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal (tensorProjConst_nonneg m p),
      ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) ?_
    rw [show tensorProjLinear m p d hN hp j f = hmem.toLp _ from rfl,
      eLpNorm_congr_ae (MemLp.coeFn_toLp hmem)]
    exact eLpNorm_tensorProjFun_le m hN Fact.out hp (Lp.aestronglyMeasurable f) j

/-- **The projection is the pointwise projection almost everywhere**. -/
theorem tensorProj_apply_ae (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    tensorProj m p d hN hp j f =ᵐ[volume] tensorProjFun m j f :=
  MemLp.coeFn_toLp (memLp_tensorProjFun m hN Fact.out hp (Lp.memLp f) j)

/-- **The projections are uniformly bounded**: `‖P_j‖ ≤ tensorProjConst m p d` for every level
`j`. -/
theorem norm_tensorProj_le (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    ‖tensorProj m p d hN hp j‖ ≤ tensorProjConst m p d :=
  LinearMap.mkContinuous_norm_le _ (tensorProjConst_nonneg m p) _

/-- **`P_j` is a projection**: `P_j (P_j f) = P_j f` for every `f ∈ L_p(ℝ^d)`
(`Daubechies.tensorProjFun_tensorProjFun`). -/
theorem tensorProj_tensorProj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    tensorProj m p d hN hp j (tensorProj m p d hN hp j f) = tensorProj m p d hN hp j f := by
  refine Lp.ext ((tensorProj_apply_ae m hN hp j _).trans ?_)
  rw [tensorProjFun_congr_ae m (tensorProj_apply_ae m hN hp j f) j,
    tensorProjFun_tensorProjFun m hN]
  exact (tensorProj_apply_ae m hN hp j f).symm

/-- **The projections of consecutive levels**: `P_{j+1} (P_j f) = P_j f` for every
`f ∈ L_p(ℝ^d)` (`Daubechies.tensorProjFun_succ_tensorProjFun`). -/
theorem tensorProj_succ_tensorProj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    tensorProj m p d hN hp (j + 1) (tensorProj m p d hN hp j f) = tensorProj m p d hN hp j f := by
  refine Lp.ext ((tensorProj_apply_ae m hN hp (j + 1) _).trans ?_)
  rw [tensorProjFun_congr_ae m (tensorProj_apply_ae m hN hp j f) (j + 1),
    tensorProjFun_succ_tensorProjFun m hN]
  exact (tensorProj_apply_ae m hN hp j f).symm

/-! ### The scaling spaces and the schemes -/

variable (p d) in
/-- **The scaling space of level `j` on `ℝ^d`**: the range `V_j` of the projection `P_j` in
`L_p(ℝ^d)`, for `N ≥ 2` and `1 ≤ p < ∞`, a real subspace consisting of the classes of the
expansions `∑_k ⟨f, Φ_{j,k}⟩ Φ_{j,k}`, `f ∈ L_p(ℝ^d)`. -/
noncomputable def tensorScalingSpace (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    Submodule ℝ (Lp ℂ p (volume : Measure (Fin d → ℝ))) :=
  LinearMap.range (tensorProj m p d hN hp j).toLinearMap

/-- `a ∈ V_j` iff `a = P_j f` for some `f ∈ L_p(ℝ^d)`. -/
theorem mem_tensorScalingSpace {hN : 2 ≤ N} {hp : p ≠ ∞} {j : ℕ}
    {a : Lp ℂ p (volume : Measure (Fin d → ℝ))} :
    a ∈ tensorScalingSpace m p d hN hp j ↔ ∃ f, tensorProj m p d hN hp j f = a :=
  LinearMap.mem_range

/-- The projection `P_j f` lies in the scaling space `V_j`. -/
theorem tensorProj_mem_tensorScalingSpace (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    tensorProj m p d hN hp j f ∈ tensorScalingSpace m p d hN hp j :=
  LinearMap.mem_range_self _ f

/-- **The projection fixes the scaling space**: `P_j a = a` for every `a ∈ V_j`
(`Daubechies.tensorProj_tensorProj`). -/
theorem tensorProj_eq_self_of_mem (hN : 2 ≤ N) (hp : p ≠ ∞) {j : ℕ}
    {a : Lp ℂ p (volume : Measure (Fin d → ℝ))} (ha : a ∈ tensorScalingSpace m p d hN hp j) :
    tensorProj m p d hN hp j a = a := by
  obtain ⟨f, rfl⟩ := (mem_tensorScalingSpace m).1 ha
  exact tensorProj_tensorProj m hN hp j f

/-- **The scaling spaces increase with the level**: `V_i ⊆ V_j` for `i ≤ j`, since
`P_j f = P_{j+1} (P_j f)` (`Daubechies.tensorProj_succ_tensorProj`). -/
theorem tensorScalingSpace_mono (hN : 2 ≤ N) (hp : p ≠ ∞) :
    Monotone (tensorScalingSpace m p d hN hp) :=
  monotone_nat_of_le_succ fun j a ha => by
    obtain ⟨f, rfl⟩ := (mem_tensorScalingSpace m).1 ha
    exact (mem_tensorScalingSpace m).2
      ⟨tensorProj m p d hN hp j f, tensorProj_succ_tensorProj m hN hp j f⟩

variable (p d) in
/-- **The tensor Daubechies scheme** in `L_p(ℝ^d)`, for `N ≥ 2` and `1 ≤ p < ∞`: `{0}` at
complexity `0` and the scaling space `V_{⌊log₂ n⌋}` at complexity `n ≥ 1`
(`ApproximationScheme.ofMonotoneSubmodules`). -/
noncomputable def tensorScheme (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ApproximationScheme (Lp ℂ p (volume : Measure (Fin d → ℝ))) :=
  ApproximationScheme.ofMonotoneSubmodules (tensorScalingSpace m p d hN hp)
    (tensorScalingSpace_mono m hN hp)

/-- The approximants of complexity `2^k` are the elements of the scaling space `V_k`. -/
theorem mem_tensorScheme_two_pow {hN : 2 ≤ N} {hp : p ≠ ∞} {k : ℕ}
    {a : Lp ℂ p (volume : Measure (Fin d → ℝ))} :
    a ∈ tensorScheme m p d hN hp (2 ^ k) ↔ a ∈ tensorScalingSpace m p d hN hp k :=
  ApproximationScheme.mem_ofMonotoneSubmodules_two_pow

variable (p d) in
/-- **The projection scheme of the tensor scaling spaces** in `L_p(ℝ^d)`, for `N ≥ 2` and
`1 ≤ p < ∞`: the projection of complexity `n ≥ 1` is `P_{⌊log₂ n⌋}`, the one of complexity `0`
is `0`, and all are bounded by `tensorProjConst m p d`. -/
noncomputable def tensorProjectionScheme (hN : 2 ≤ N) (hp : p ≠ ∞) :
    (tensorScheme m p d hN hp).ProjectionScheme :=
  ApproximationScheme.ProjectionScheme.ofMonotone (tensorScalingSpace m p d hN hp)
    (tensorScalingSpace_mono m hN hp) (tensorProj m p d hN hp)
    (tensorProj_mem_tensorScalingSpace m hN hp) (fun _ _ ha => tensorProj_eq_self_of_mem m hN hp ha)
    (tensorProjConst m p d) (norm_tensorProj_le m hN hp)

/-- The projection of complexity `2^k` is `P_k`. -/
theorem tensorProjectionScheme_two_pow (hN : 2 ≤ N) (hp : p ≠ ∞) (k : ℕ) :
    (tensorProjectionScheme m p d hN hp).P (2 ^ k) = tensorProj m p d hN hp k :=
  ApproximationScheme.ProjectionScheme.ofMonotone_two_pow k

/-! ### The blocks -/

/-- **The block identity on `L_p(ℝ^d)`**: for `N ≥ 2`, `1 ≤ p < ∞`, every level `j` and every
`f ∈ L_p(ℝ^d)`, `P_{j+1} f - P_j f` is the class of the wavelet part
`∑_{e ≠ ∅} ∑_k ⟨f, Ψ^e_{j,k}⟩ Ψ^e_{j,k}` (`Daubechies.tensorProjFun_succ_eq_add`). -/
theorem tensorProj_succ_sub_tensorProj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    tensorProj m p d hN hp (j + 1) f - tensorProj m p d hN hp j f =
      (memLp_tensorDetailFun m hN Fact.out hp (Lp.memLp f) j).toLp _ := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (tensorProj m p d hN hp (j + 1) f) (tensorProj m p d hN hp j f),
    tensorProj_apply_ae m hN hp (j + 1) f, tensorProj_apply_ae m hN hp j f,
    MemLp.coeFn_toLp (memLp_tensorDetailFun m hN Fact.out hp (Lp.memLp f) j)] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4,
    tensorProjFun_succ_eq_add m hN ((Lp.memLp f).locallyIntegrable Fact.out) j x,
    add_sub_cancel_left]

/-- **The norm of a block**: `‖P_{j+1} f - P_j f‖_p = ‖Q_j f‖_p` for every `f ∈ L_p(ℝ^d)`
(`Daubechies.tensorProj_succ_sub_tensorProj`). -/
theorem enorm_tensorProj_succ_sub_tensorProj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖tensorProj m p d hN hp (j + 1) f - tensorProj m p d hN hp j f‖ₑ =
      eLpNorm (tensorDetailFun m j f) p volume := by
  rw [tensorProj_succ_sub_tensorProj, Lp.enorm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]

/-- **The norms of the blocks through the wavelet coefficients**: for `N ≥ 2` and `1 ≤ p < ∞`
there are constants `K, M < ∞` such that for every `f ∈ L_p(ℝ^d)` and every level `j`,
`2^(jd(1/2 - 1/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p} ≤ K ‖P_{j+1} f - P_j f‖_p` and
`‖P_{j+1} f - P_j f‖_p ≤ M 2^(jd(1/2 - 1/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p}`. The block is the
expansion of the wavelet coefficients (`Daubechies.enorm_tensorProj_succ_sub_tensorProj`), so
lower stability (`Daubechies.lqNorm_le_eLpNorm_tensorExpand`, with the orthonormality of the
wavelet family) and upper stability (`Daubechies.eLpNorm_tensorExpand_le`) give the constants
`K = Daubechies.tensorCoeffConst` and `M = Daubechies.tensorExpandConst` of the wavelet family. -/
theorem enorm_tensorBlock_equiv (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ∃ K M : ℝ≥0∞, K ≠ ∞ ∧ M ≠ ∞ ∧ ∀ (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) (j : ℕ),
      dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j *
          lqNorm p (fun ek => ‖tensorCoeff (tensorWaveletFamily m d) j f ek‖ₑ) ≤
        K * ‖tensorProj m p d hN hp (j + 1) f - tensorProj m p d hN hp j f‖ₑ ∧
      ‖tensorProj m p d hN hp (j + 1) f - tensorProj m p d hN hp j f‖ₑ ≤
        M * (dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j *
          lqNorm p (fun ek => ‖tensorCoeff (tensorWaveletFamily m d) j f ek‖ₑ)) := by
  refine ⟨tensorCoeffConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p,
    tensorExpandConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p,
    tensorCoeffConst_ne_top _ _ fun e => memLp_tensorGen m hN e.1 _,
    tensorExpandConst_ne_top _ _ Fact.out fun e => memLp_tensorGen m hN e.1 p,
    fun f j => ⟨?_, ?_⟩⟩
  · rw [enorm_tensorProj_succ_sub_tensorProj]
    exact lqNorm_le_eLpNorm_tensorExpand (G := tensorWaveletFamily m d) (a := 1 - N)
      (b := 2 * N - 1) (fun e => continuous_tensorGen m hN e.1)
      (fun e _ hx => tensorGen_eq_zero m hN e.1 hx)
      (integral_tensorWaveletFamily_translate_mul_conj_translate m hN) Fact.out hp j _
  · rw [enorm_tensorProj_succ_sub_tensorProj]
    refine (eLpNorm_tensorExpand_le (G := tensorWaveletFamily m d) (a := 1 - N) (b := 2 * N - 1)
      (fun e => (continuous_tensorGen m hN e.1).aestronglyMeasurable)
      (fun e _ hx => tensorGen_eq_zero m hN e.1 hx) Fact.out hp
      (fun e => le_iSup (fun e => eLpNorm (tensorWaveletFamily m d e) p volume) e) j _).trans_eq ?_
    rw [tensorExpandConst]
    ring

/-- **The norm of the projection of level `0` through the scaling coefficients**: for `N ≥ 2` and
`1 ≤ p < ∞` there are constants `K, M < ∞` with `‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p} ≤ K ‖P_0 f‖_p` and
`‖P_0 f‖_p ≤ M ‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p}` for every `f ∈ L_p(ℝ^d)`: the stability of the
expansions in the scaling family at level `0` (`Daubechies.lqNorm_le_eLpNorm_tensorExpand`,
`Daubechies.eLpNorm_tensorExpand_le`), with the index set `Unit × ℤ^d` identified with `ℤ^d`
(`ENNReal.lqNorm_comp_equiv`). -/
theorem enorm_tensorProj_zero_equiv (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ∃ K M : ℝ≥0∞, K ≠ ∞ ∧ M ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure (Fin d → ℝ)),
      lqNorm p (fun k : Fin d → ℤ => ‖tensorCoeff (tensorScalingFamily m d) 0 f ((), k)‖ₑ) ≤
        K * ‖tensorProj m p d hN hp 0 f‖ₑ ∧
      ‖tensorProj m p d hN hp 0 f‖ₑ ≤
        M * lqNorm p (fun k : Fin d → ℤ =>
          ‖tensorCoeff (tensorScalingFamily m d) 0 f ((), k)‖ₑ) := by
  refine ⟨tensorCoeffConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p,
    tensorExpandConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p,
    tensorCoeffConst_ne_top _ _ fun _ => memLp_tensorGen m hN ∅ _,
    tensorExpandConst_ne_top _ _ Fact.out fun _ => memLp_tensorGen m hN ∅ p, fun f => ?_⟩
  have hl : lqNorm p (fun k : Fin d → ℤ => ‖tensorCoeff (tensorScalingFamily m d) 0 f ((), k)‖ₑ) =
      lqNorm p (fun νk => ‖tensorCoeff (tensorScalingFamily m d) 0 f νk‖ₑ) :=
    ENNReal.lqNorm_comp_equiv (Equiv.punitProd (Fin d → ℤ)).symm
      (fun νk => ‖tensorCoeff (tensorScalingFamily m d) 0 f νk‖ₑ)
  have he : ‖tensorProj m p d hN hp 0 f‖ₑ = eLpNorm (tensorProjFun m 0 f) p volume := by
    rw [Lp.enorm_def, eLpNorm_congr_ae (tensorProj_apply_ae m hN hp 0 f)]
  rw [hl, he]
  constructor
  · have h := lqNorm_le_eLpNorm_tensorExpand (G := tensorScalingFamily m d) (a := 1 - N)
      (b := 2 * N - 1) (fun _ => continuous_tensorGen m hN ∅)
      (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx)
      (integral_tensorScalingFamily_translate_mul_conj_translate m hN) Fact.out hp 0
      (tensorCoeff (tensorScalingFamily m d) 0 f)
    rw [ENNReal.dyadicWeight_zero_right, one_mul] at h
    exact h
  · refine (eLpNorm_tensorExpand_le (G := tensorScalingFamily m d) (a := 1 - N) (b := 2 * N - 1)
      (fun _ => (continuous_tensorGen m hN ∅).aestronglyMeasurable)
      (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx) Fact.out hp
      (fun ν => le_iSup (fun ν => eLpNorm (tensorScalingFamily m d ν) p volume) ν) 0
      _).trans_eq ?_
    rw [tensorExpandConst, ENNReal.dyadicWeight_zero_right, mul_one]

/-! ### The inverse inequality -/

/-- **The modulus of an element of `V_j` at the dyadic scales `2^(-k)`, `k ≥ j`**: let `N ≥ 2`,
`1 ≤ p < ∞`, `θ ≥ 0`, and let `‖Δ_h^N Φ‖_p ≤ K ‖h‖^θ` for every `h ∈ ℝ^d` with `‖h‖ ≤ 1`. Then for
all levels `j ≤ k` and every `a ∈ V_j`, `ω_N(a, 2^(-k))_p ≤ C K 2^(-(k-j)θ) ‖a‖_p` with the
constant `C` of Bernstein's inequality for the scaling family
(`Daubechies.tensorBernsteinConst`). The element `a` is almost everywhere the expansion of its
own coefficients of level `j` (`Daubechies.tensorProj_eq_self_of_mem`), so Bernstein's inequality
for expansions (`Daubechies.modulus_tensorExpand_le`) applies at `t = 2^(-k)`, where
`2^j t = 2^(-(k-j)) ≤ 1` bounds the steps `H`. -/
theorem lpModulus_le_of_mem_tensorScalingSpace (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ} (hθ : 0 ≤ θ)
    {K : ℝ≥0∞} (hK : ∀ h : Fin d → ℝ, ‖h‖ ≤ 1 →
      eLpNorm ((fwdDiff h)^[N] (tensorGen m ∅)) p volume ≤ K * ENNReal.ofReal (‖h‖ ^ θ))
    {j k : ℕ} (hjk : j ≤ k) {a : Lp ℂ p (volume : Measure (Fin d → ℝ))}
    (ha : a ∈ tensorScalingSpace m p d hN hp j) :
    Rd.lpModulus p N a k ≤ tensorBernsteinConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p N *
      K * dyadicWeight (-θ) (k - j) * ‖a‖ₑ := by
  have hae : (a : (Fin d → ℝ) → ℂ) =ᵐ[volume] tensorProjFun m j a := by
    have h := tensorProj_apply_ae m hN hp j a
    rwa [tensorProj_eq_self_of_mem m hN hp ha] at h
  have ht := two_pow_mul_one_div_two_pow hjk
  have ht1 : (2 : ℝ) ^ j * (1 / 2 ^ k) ≤ 1 := by
    rw [ht]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ one_le_two)
  have hS : (⨆ (ν : Unit) (H : Fin d → ℝ) (_ : ‖H‖ ≤ 2 ^ j * (1 / 2 ^ k)),
      eLpNorm ((fwdDiff H)^[N] (tensorScalingFamily m d ν)) p volume) ≤
        K * dyadicWeight (-θ) (k - j) := by
    refine iSup_le fun _ => iSup₂_le fun H hH => (hK H (hH.trans ht1)).trans ?_
    rw [← ENNReal.ofReal_one_div_two_pow_rpow, ← ht]
    gcongr
  calc Rd.lpModulus p N a k = Rd.modulus volume N p (a : (Fin d → ℝ) → ℂ) (1 / 2 ^ k) := rfl
    _ ≤ tensorBernsteinConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p N *
          (⨆ (ν : Unit) (H : Fin d → ℝ) (_ : ‖H‖ ≤ 2 ^ j * (1 / 2 ^ k)),
            eLpNorm ((fwdDiff H)^[N] (tensorScalingFamily m d ν)) p volume) * ‖a‖ₑ := by
        rw [Lp.enorm_def]
        exact modulus_tensorExpand_le (fun _ => (continuous_tensorGen m hN ∅).aestronglyMeasurable)
          (fun _ _ hx => tensorGen_eq_zero m hN ∅ hx) Fact.out hp N (Lp.aestronglyMeasurable a)
          hae ht1
    _ ≤ tensorBernsteinConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p N *
          (K * dyadicWeight (-θ) (k - j)) * ‖a‖ₑ := by gcongr
    _ = _ := by ring

/-- **The inverse inequality of the tensor Daubechies scheme**: let `N ≥ 2`, `1 ≤ p < ∞`, let `φ`
have a Bernstein bound of order `θ` with differences of order `N`
(`Daubechies.BernsteinBound`), and let `0 ≤ θ' ≤ θ` with `θ' < N`. Then there is a finite
constant `C_B` with `ω_N(a, 2^(-k))_p ≤ C_B 2^(-(k-j)θ') ‖a‖_p` for all `j, k ∈ ℕ` and every
approximant `a` of complexity `2^j` of the tensor scheme (the elements of `V_j`), where `k - j` is
truncated at `0`. For `k ≥ j` this is `Daubechies.lpModulus_le_of_mem_tensorScalingSpace` with
the bound `‖Δ_h^N Φ‖_p ≤ K ‖h‖^{θ'}` of `Daubechies.eLpNorm_higherDiff_tensorGen_le`; for `k < j`
the weight is `1` and `ω_N(a, t)_p ≤ 2^N ‖a‖_p` (`Rd.lpModulus_le`). -/
theorem tensor_inverse_scheme (hN : 2 ≤ N) (hp : p ≠ ∞) {θ θ' : ℝ} (hB : BernsteinBound m p θ N)
    (hθ'0 : 0 ≤ θ') (hθ' : θ' ≤ θ) (hθ'N : θ' < N) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ tensorScheme m p d hN hp (2 ^ j),
      Rd.lpModulus p N a k ≤ CB * dyadicWeight (-θ') (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hmod⟩ := eLpNorm_higherDiff_tensorGen_le m (d := d) hN hp hB hθ'0 hθ' hθ'N
  have hC := tensorBernsteinConst_ne_top (G := tensorScalingFamily m d) (1 - N) (2 * N - 1)
    (Fact.out : 1 ≤ p) (fun _ => memLp_tensorGen m hN ∅ _) N
  refine ⟨tensorBernsteinConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p N * K + 2 ^ N,
    by finiteness, fun j k a ha => ?_⟩
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (Rd.lpModulus_le N a k).trans (by gcongr; exact le_add_self)
  · exact (lpModulus_le_of_mem_tensorScalingSpace m hN hp hθ'0 (hmod ∅) hjk
      ((mem_tensorScheme_two_pow m).1 ha)).trans (by gcongr; exact le_self_add)

end Lp

end Daubechies
