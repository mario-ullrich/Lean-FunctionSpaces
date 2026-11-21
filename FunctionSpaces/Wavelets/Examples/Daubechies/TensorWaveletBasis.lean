/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import ApproximationSpaces.Instances.NTermHilbertBasis
public import FunctionSpaces.Wavelets.Examples.Daubechies.TensorBesov

/-!
# The tensor Daubechies wavelets as a Hilbert basis of `L_2(ℝ^d)`

For a Daubechies mask of order `N ≥ 2`, the integer translates `Φ(· - k)`, `k ∈ ℤ^d`, of the
tensor scaling function and the dilated and translated tensor wavelets
`Ψ^e_{j,k}(x) = 2^(jd/2) Ψ^e(2^j x - k)`, `j ∈ ℕ`, `e ≠ ∅`, `k ∈ ℤ^d`
(`Daubechies.tensorWaveletFun`, indexed by `Daubechies.TensorWaveletIndex`), form a Hilbert
basis of `L_2(ℝ^d)` (`Daubechies.tensorWaveletBasis`). DeVore, *Nonlinear approximation*, Acta
Numer. 1998, (7.18) and (7.19), states this in homogeneous form, with the dyadic cubes of all
levels `k ∈ ℤ`; here the translates of `Φ` span `V_0`, which takes the place of the levels
`k < 0`. The system with this index set is the one of Triebel, *Function Spaces and Wavelets on
Domains*, 2008, Theorem 1.20.

* **Orthonormality.** The functions of one level are orthonormal, since the integer translates
  of the generators are (`Daubechies.integral_tensorGen_translate_mul_conj_translate`). Across
  levels, `P_0` fixes `Φ(· - k)` and `P_{j+1}` fixes `Ψ^e_{j,k}`
  (`Daubechies.tensorProjFun_tensorScaled_tensorGen_empty`,
  `Daubechies.tensorProjFun_succ_tensorScaled_tensorGen`),
  and the wavelet coefficients of level `j` of a function fixed by `P_i`, `i ≤ j`, vanish
  (`Daubechies.tensorCoeff_tensorWaveletFamily_eq_zero_of_le`). So the system is orthonormal
  (`Daubechies.integral_tensorWaveletFun_mul_conj`, `Daubechies.orthonormal_tensorWaveletVec`).
* **Completeness.** If all coefficients of `f ∈ L_p(ℝ^d)`, `1 ≤ p < ∞`, vanish, then
  `P_J f = P_0 f + ∑_{j<J} Q_j f = 0` for every `J` (`Daubechies.tensorProjFun_eq_add_sum`), and
  `P_J f → f` (`Daubechies.tendsto_tensorProj`), so `f = 0`
  (`Daubechies.eq_zero_of_tensorCoeff_eq_zero`). For `p = 2` the orthogonal complement of the
  span of the system is `0` (`Daubechies.orthogonal_span_tensorWaveletVec_eq_bot`).
* **Coefficients.** The coefficients of `f` in the basis are `⟨f, Φ(· - k)⟩` and
  `⟨f, Ψ^e_{j,k}⟩` (`Daubechies.tensorWaveletBasis_repr_inl`,
  `Daubechies.tensorWaveletBasis_repr_inr`). For `q = p` the coefficient quasi-norm
  `Daubechies.tensorCoeffNorm` is finite iff `∑_i (w_i |⟨f, b_i⟩|)^p < ∞` with the weights
  `w_i = 1` at the scaling functions and `w_i = 2^(j(s + d/2 - d/p))` at the wavelets of level
  `j` (`Daubechies.tensorWaveletWeight`, `Daubechies.tensorCoeffNorm_lt_top_iff_tsum`). At
  `p = 2` this gives `H^s(V)` as a weighted `ℓ_2` of the coefficients in the basis
  (`Daubechies.memSobolev_two_iff_weighted`).
* **Synthesis in `L_p`.** `‖P_J f‖_p ≤ C ‖f‖_coef` uniformly in `J`, with the constant
  `C = Daubechies.tensorSynthesisConst`, finite for `s > 0`
  (`Daubechies.eLpNorm_tensorProjFun_le_tensorCoeffNorm`). So a function of some `L_r`,
  `1 ≤ r < ∞`, whose coefficient quasi-norm in `L_p` of a smoothness `s > 0` is finite lies in
  `L_p` (`Daubechies.memLp_of_tensorCoeffNorm_lt_top`): `f` is the almost everywhere limit of a
  subsequence of `P_J f`, and Fatou's lemma applies.
* **`n`-term approximation.** For `0 < τ < 2` and `θ = 1/τ - 1/2`, `f ∈ L_2(ℝ^d)` lies in the
  approximation space `A^θ_τ` of `n`-term approximation from the basis iff its coefficient
  quasi-norm for `p = q = τ` and `s = dθ` is finite, where the weight `2^(j(dθ + d/2 - d/τ))` is
  `1` (`Daubechies.memApprox_nTerm_tensorWaveletBasis_iff_coeff`, from the theorem of Stechkin
  and DeVore, `HilbertBasis.memApprox_nTerm_iff`). For `1 ≤ τ < 2` the coefficient condition puts
  `f` into `L_τ`, and with the Besov theorem `A^θ_τ = B^{dθ}_{τ,τ}(ℝ^d) ∩ L_2(ℝ^d)`
  (`Daubechies.memApprox_nTerm_tensorWaveletBasis_iff`; DeVore–Jawerth–Popov, and DeVore 1998,
  §7.6 and Remark 7.6).

The norm on `ℝ^d` is the sup norm.
-/

@[expose] public section

open Filter MeasureTheory Topology Module ApproximationScheme
open scoped ENNReal ComplexConjugate InnerProductSpace SchwartzMap
open ENNReal (dyadicWeight lqNorm)

/-- **Conjugate symmetry of the pairing**: `∫ f conj g = conj (∫ g conj f)` for all complex
functions `f, g` on a measure space (Mathlib's `integral_conj`). -/
theorem MeasureTheory.integral_mul_conj_eq_conj {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) : ∫ x, f x * conj (g x) ∂μ = conj (∫ x, g x * conj (f x) ∂μ) := by
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, Complex.conj_conj, mul_comm]

namespace Daubechies

/-! ### The index set and the weights -/

/-- **The index set of the tensor wavelet basis** of `L_2(ℝ^d)`: a position `k ∈ ℤ^d` for the
integer translate `Φ(· - k)` of the tensor scaling function, or a triple `(j, e, k)` of a level
`j ∈ ℕ`, a nonempty set `e` of coordinates and a position `k ∈ ℤ^d` for the tensor wavelet
`Ψ^e_{j,k}`. -/
abbrev TensorWaveletIndex (d : ℕ) : Type :=
  (Fin d → ℤ) ⊕ (ℕ × {e : Finset (Fin d) // e.Nonempty} × (Fin d → ℤ))

section Weights

variable {d : ℕ}

/-- **The weights of the tensor wavelet basis** for the smoothness `s`: `1` at the scaling
functions `Φ(· - k)` and `2^(js)` at the wavelets `Ψ^e_{j,k}` of level `j`. With
`s + d(1/2 - 1/p)` in place of `s` they turn the coefficient quasi-norm with `q = p` into a
weighted `ℓ_p` norm (`Daubechies.tensorCoeffNorm_lt_top_iff_tsum`). -/
noncomputable def tensorWaveletWeight (s : ℝ) (i : TensorWaveletIndex d) : ℝ≥0∞ :=
  Sum.elim (fun _ => 1) (fun jek => dyadicWeight s jek.1) i

/-- The weight of a scaling function is `1`. -/
@[simp]
theorem tensorWaveletWeight_inl (s : ℝ) (k : Fin d → ℤ) :
    tensorWaveletWeight s (Sum.inl k : TensorWaveletIndex d) = 1 := rfl

/-- The weight of a wavelet of level `j` is `2^(js)`. -/
@[simp]
theorem tensorWaveletWeight_inr (s : ℝ) (j : ℕ)
    (ek : {e : Finset (Fin d) // e.Nonempty} × (Fin d → ℤ)) :
    tensorWaveletWeight s (Sum.inr (j, ek) : TensorWaveletIndex d) = dyadicWeight s j := rfl

/-- For the smoothness `0` every weight is `1` (`ENNReal.dyadicWeight_zero_left`). -/
theorem tensorWaveletWeight_zero (i : TensorWaveletIndex d) : tensorWaveletWeight 0 i = 1 := by
  rcases i with k | ⟨j, ek⟩
  · rfl
  · exact ENNReal.dyadicWeight_zero_left j

end Weights

variable {N : ℕ} (m : Mask N) {d : ℕ}

/-! ### The tensor wavelet system -/

section System

variable (d) in
/-- **The tensor wavelet system** on `ℝ^d`: `Φ(· - k)` at the index `k ∈ ℤ^d`, written as the
generator `Φ_{0,k}` of level `0` (`Daubechies.tensorScaled_zero`), and
`Ψ^e_{j,k}(x) = 2^(jd/2) Ψ^e(2^j x - k)` at the index `(j, e, k)` (`Daubechies.tensorScaled`,
`Daubechies.tensorGen`). -/
noncomputable def tensorWaveletFun (i : TensorWaveletIndex d) : (Fin d → ℝ) → ℂ :=
  Sum.elim (fun k => tensorScaled (tensorGen m ∅) 0 k)
    (fun jek => tensorScaled (tensorGen m jek.2.1.1) jek.1 jek.2.2) i

/-- The function of the index `k ∈ ℤ^d` is `Φ_{0,k}`. -/
@[simp]
theorem tensorWaveletFun_inl (k : Fin d → ℤ) :
    tensorWaveletFun m d (Sum.inl k) = tensorScaled (tensorGen m ∅) 0 k := rfl

/-- The function of the index `(j, e, k)` is `Ψ^e_{j,k}`. -/
@[simp]
theorem tensorWaveletFun_inr (j : ℕ) (e : {e : Finset (Fin d) // e.Nonempty})
    (k : Fin d → ℤ) :
    tensorWaveletFun m d (Sum.inr (j, e, k)) = tensorScaled (tensorGen m e.1) j k := rfl

/-- **Pairings with the scaling functions**: `∫ f conj Φ(· - k)` is the coefficient
`⟨f, Φ_{0,k}⟩` of the scaling family at level `0` (`Daubechies.tensorCoeff`). -/
theorem integral_mul_conj_tensorWaveletFun_inl (f : (Fin d → ℝ) → ℂ) (k : Fin d → ℤ) :
    ∫ x, f x * conj (tensorWaveletFun m d (Sum.inl k) x) =
      tensorCoeff (tensorScalingFamily m d) 0 f ((), k) := rfl

/-- **Pairings with the wavelets**: `∫ f conj Ψ^e_{j,k}` is the coefficient `⟨f, Ψ^e_{j,k}⟩` of
the wavelet family at level `j` (`Daubechies.tensorCoeff`). -/
theorem integral_mul_conj_tensorWaveletFun_inr (f : (Fin d → ℝ) → ℂ) (j : ℕ)
    (ek : {e : Finset (Fin d) // e.Nonempty} × (Fin d → ℤ)) :
    ∫ x, f x * conj (tensorWaveletFun m d (Sum.inr (j, ek)) x) =
      tensorCoeff (tensorWaveletFamily m d) j f ek := rfl

/-- The functions of the system are continuous, for `N ≥ 2`
(`Daubechies.continuous_tensorScaled`). -/
theorem continuous_tensorWaveletFun (hN : 2 ≤ N) (i : TensorWaveletIndex d) :
    Continuous (tensorWaveletFun m d i) := by
  rcases i with k | ⟨j, e, k⟩
  · exact continuous_tensorScaled (continuous_tensorGen m hN ∅) 0 k
  · exact continuous_tensorScaled (continuous_tensorGen m hN e.1) j k

/-- The functions of the system have compact support, for `N ≥ 2`
(`Daubechies.hasCompactSupport_tensorScaled`). -/
theorem hasCompactSupport_tensorWaveletFun (hN : 2 ≤ N) (i : TensorWaveletIndex d) :
    HasCompactSupport (tensorWaveletFun m d i) := by
  rcases i with k | ⟨j, e, k⟩
  · exact hasCompactSupport_tensorScaled (fun _ hx => tensorGen_eq_zero m hN ∅ hx) 0 k
  · exact hasCompactSupport_tensorScaled (fun _ hx => tensorGen_eq_zero m hN e.1 hx) j k

/-- The functions of the system lie in every `L_p`, for `N ≥ 2`: they are continuous with compact
support. -/
theorem memLp_tensorWaveletFun (hN : 2 ≤ N) (i : TensorWaveletIndex d) (p : ℝ≥0∞) :
    MemLp (tensorWaveletFun m d i) p volume :=
  (continuous_tensorWaveletFun m hN i).memLp_of_hasCompactSupport
    (hasCompactSupport_tensorWaveletFun m hN i)

variable (d) in
/-- **The vectors of the tensor wavelet system** in `L_2(ℝ^d)`, for `N ≥ 2`: the classes of the
functions `Daubechies.tensorWaveletFun`. -/
noncomputable def tensorWaveletVec (hN : 2 ≤ N) (i : TensorWaveletIndex d) :
    Lp ℂ 2 (volume : Measure (Fin d → ℝ)) :=
  (memLp_tensorWaveletFun m hN i 2).toLp _

/-- The vector of the index `i` is the function of `i` almost everywhere. -/
theorem coeFn_tensorWaveletVec (hN : 2 ≤ N) (i : TensorWaveletIndex d) :
    tensorWaveletVec m d hN i =ᵐ[volume] tensorWaveletFun m d i :=
  MemLp.coeFn_toLp _

/-- **The inner products with the vectors of the system** are the pairings:
`⟪b_i, f⟫ = ∫ f conj b_i` for every `f ∈ L_2(ℝ^d)` (Mathlib's `MeasureTheory.L2.inner_def`). -/
theorem inner_tensorWaveletVec (hN : 2 ≤ N) (i : TensorWaveletIndex d)
    (f : Lp ℂ 2 (volume : Measure (Fin d → ℝ))) :
    ⟪tensorWaveletVec m d hN i, f⟫_ℂ = ∫ x, f x * conj (tensorWaveletFun m d i x) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_tensorWaveletVec m hN i] with x hx
  rw [RCLike.inner_apply', hx, mul_comm]

end System

/-! ### Orthonormality -/

section Orthonormality

/-- **The tensor wavelet system is orthonormal**: for `N ≥ 2` and all indices `i, i'`,
`∫ b_i conj b_{i'} = 1` if `i = i'` and `0` otherwise. Within one level this is the
orthonormality of the integer translates (`Daubechies.integral_tensorScaled_mul_conj`,
`Daubechies.integral_tensorGen_translate_mul_conj_translate`). Across levels, `Φ(· - k)` is fixed
by `P_0` and `Ψ^e_{j,k}` by `P_{j+1}` (`Daubechies.tensorProjFun_tensorScaled_tensorGen_empty`,
`Daubechies.tensorProjFun_succ_tensorScaled_tensorGen`), so their wavelet coefficients of every
higher level vanish (`Daubechies.tensorCoeff_tensorWaveletFamily_eq_zero_of_le`); the other
order follows by conjugation (`MeasureTheory.integral_mul_conj_eq_conj`). -/
theorem integral_tensorWaveletFun_mul_conj (hN : 2 ≤ N) (i i' : TensorWaveletIndex d) :
    ∫ x, tensorWaveletFun m d i x * conj (tensorWaveletFun m d i' x) =
      if i = i' then 1 else 0 := by
  have hcross : ∀ (g : (Fin d → ℝ) → ℂ) {l j : ℕ}, tensorProjFun m l g = g → l ≤ j →
      ∀ e k, ∫ x, g x * conj (tensorWaveletFun m d (Sum.inr (j, e, k)) x) = 0 :=
    fun _ _ _ hg hlj e k => tensorCoeff_tensorWaveletFamily_eq_zero_of_le m hN hg hlj (e, k)
  rcases i with k | ⟨j, e, k⟩ <;> rcases i' with k' | ⟨j', e', k'⟩
  · simp only [tensorWaveletFun_inl]
    rw [integral_tensorScaled_mul_conj, integral_tensorGen_translate_mul_conj_translate m hN]
    simp
  · rw [ite_eq_right Sum.inl_ne_inr]
    exact hcross _ (tensorProjFun_tensorScaled_tensorGen_empty m hN 0 k) (Nat.zero_le j') e' k'
  · rw [ite_eq_right Sum.inr_ne_inl, integral_mul_conj_eq_conj,
      hcross (tensorWaveletFun m d (Sum.inl k'))
        (tensorProjFun_tensorScaled_tensorGen_empty m hN 0 k') (Nat.zero_le j) e k, map_zero]
  · rcases lt_trichotomy j j' with h | rfl | h
    · rw [ite_eq_right fun h' => h.ne (congrArg Prod.fst (Sum.inr_injective h'))]
      exact hcross _ (tensorProjFun_succ_tensorScaled_tensorGen m hN e j k) h e' k'
    · simp only [tensorWaveletFun_inr]
      rw [integral_tensorScaled_mul_conj, integral_tensorGen_translate_mul_conj_translate m hN]
      simp [Subtype.ext_iff]
    · rw [ite_eq_right fun h' => h.ne' (congrArg Prod.fst (Sum.inr_injective h')),
        integral_mul_conj_eq_conj,
        hcross (tensorWaveletFun m d (Sum.inr (j', e', k')))
          (tensorProjFun_succ_tensorScaled_tensorGen m hN e' j' k') h e k, map_zero]

/-- **The vectors of the tensor wavelet system are orthonormal** in `L_2(ℝ^d)`, for `N ≥ 2`
(`Daubechies.inner_tensorWaveletVec`, `Daubechies.integral_tensorWaveletFun_mul_conj`). -/
theorem orthonormal_tensorWaveletVec (hN : 2 ≤ N) : Orthonormal ℂ (tensorWaveletVec m d hN) := by
  classical
  rw [orthonormal_iff_ite]
  intro i i'
  have h : ∫ x, (tensorWaveletVec m d hN i' : (Fin d → ℝ) → ℂ) x *
      conj (tensorWaveletFun m d i x) =
        ∫ x, tensorWaveletFun m d i' x * conj (tensorWaveletFun m d i x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_tensorWaveletVec m hN i'] with x hx
    rw [hx]
  rw [inner_tensorWaveletVec, h, integral_tensorWaveletFun_mul_conj m hN i' i]
  exact if_congr eq_comm rfl rfl

end Orthonormality

/-! ### Completeness and the basis -/

section Basis

/-- **A function without coefficients is zero**: let `N ≥ 2` and `1 ≤ p < ∞`. If
`⟨f, Φ(· - k)⟩ = 0` for every `k` and `⟨f, Ψ^e_{j,k}⟩ = 0` for all `j`, `e ≠ ∅` and `k`, then
`f = 0` in `L_p(ℝ^d)`. Then `P_J f = P_0 f + ∑_{j<J} Q_j f = 0` for every level `J`
(`Daubechies.tensorProjFun_eq_add_sum`, `Daubechies.tensorExpand_zero`), and `P_J f → f`
(`Daubechies.tendsto_tensorProj`). -/
theorem eq_zero_of_tensorCoeff_eq_zero (hN : 2 ≤ N) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ)))
    (h0 : ∀ k, tensorCoeff (tensorScalingFamily m d) 0 f ((), k) = 0)
    (h1 : ∀ j ek, tensorCoeff (tensorWaveletFamily m d) j f ek = 0) : f = 0 := by
  have hP : ∀ J, tensorProjFun m J f = 0 := fun J => by
    rw [tensorProjFun_eq_add_sum m hN ((Lp.memLp f).locallyIntegrable Fact.out) J, tensorProjFun,
      show tensorCoeff (tensorScalingFamily m d) 0 f = 0 from
        funext fun νk => by obtain ⟨⟨⟩, k⟩ := νk; exact h0 k, tensorExpand_zero, zero_add]
    exact Finset.sum_eq_zero fun j _ => by
      rw [tensorDetailFun, show tensorCoeff (tensorWaveletFamily m d) j f = 0 from
        funext (h1 j), tensorExpand_zero]
  have hzero : ∀ J, tensorProj m p d hN hp J f = 0 := fun J =>
    Lp.ext ((tensorProj_apply_ae m hN hp J f).trans (by
      rw [hP J]
      exact (Lp.coeFn_zero ℂ p volume).symm))
  have hlim := tendsto_tensorProj m hN hp f
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **The span of the tensor wavelet system is dense** in `L_2(ℝ^d)`, for `N ≥ 2`: its orthogonal
complement is `0`. A vector orthogonal to every `b_i` has all coefficients zero
(`Daubechies.inner_tensorWaveletVec`), so it is zero
(`Daubechies.eq_zero_of_tensorCoeff_eq_zero`). -/
theorem orthogonal_span_tensorWaveletVec_eq_bot (hN : 2 ≤ N) :
    (Submodule.span ℂ (Set.range (tensorWaveletVec m d hN)))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun g hg => ?_
  have hi : ∀ i, ∫ x, g x * conj (tensorWaveletFun m d i x) = 0 := fun i => by
    rw [← inner_tensorWaveletVec m hN i g]
    exact Submodule.inner_right_of_mem_orthogonal
      (K := Submodule.span ℂ (Set.range (tensorWaveletVec m d hN)))
      (Submodule.subset_span (Set.mem_range_self i)) hg
  exact eq_zero_of_tensorCoeff_eq_zero m hN ENNReal.ofNat_ne_top g (fun k => hi (Sum.inl k))
    fun j ek => hi (Sum.inr (j, ek))

variable (d) in
/-- **The tensor Daubechies wavelet basis** of `L_2(ℝ^d)`, for `N ≥ 2`: the Hilbert basis of the
functions `Φ(· - k)`, `k ∈ ℤ^d`, and `Ψ^e_{j,k}`, `j ∈ ℕ`, `e ≠ ∅`, `k ∈ ℤ^d`
(`Daubechies.orthonormal_tensorWaveletVec`,
`Daubechies.orthogonal_span_tensorWaveletVec_eq_bot`, Mathlib's
`HilbertBasis.mkOfOrthogonalEqBot`). -/
noncomputable def tensorWaveletBasis (hN : 2 ≤ N) :
    HilbertBasis (TensorWaveletIndex d) ℂ (Lp ℂ 2 (volume : Measure (Fin d → ℝ))) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_tensorWaveletVec m hN)
    (orthogonal_span_tensorWaveletVec_eq_bot m hN)

/-- The vectors of the basis are the vectors of the tensor wavelet system. -/
@[simp]
theorem coe_tensorWaveletBasis (hN : 2 ≤ N) :
    ⇑(tensorWaveletBasis m d hN) = tensorWaveletVec m d hN :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **The coefficients in the basis** are the pairings `∫ f conj b_i`
(`Daubechies.inner_tensorWaveletVec`). -/
theorem tensorWaveletBasis_repr (hN : 2 ≤ N) (f : Lp ℂ 2 (volume : Measure (Fin d → ℝ)))
    (i : TensorWaveletIndex d) :
    (tensorWaveletBasis m d hN).repr f i = ∫ x, f x * conj (tensorWaveletFun m d i x) := by
  rw [HilbertBasis.repr_apply_apply, coe_tensorWaveletBasis, inner_tensorWaveletVec]

/-- The coefficient of `Φ(· - k)` is `⟨f, Φ(· - k)⟩`. -/
theorem tensorWaveletBasis_repr_inl (hN : 2 ≤ N) (f : Lp ℂ 2 (volume : Measure (Fin d → ℝ)))
    (k : Fin d → ℤ) :
    (tensorWaveletBasis m d hN).repr f (Sum.inl k) =
      tensorCoeff (tensorScalingFamily m d) 0 f ((), k) :=
  tensorWaveletBasis_repr m hN f _

/-- The coefficient of `Ψ^e_{j,k}` is `⟨f, Ψ^e_{j,k}⟩`. -/
theorem tensorWaveletBasis_repr_inr (hN : 2 ≤ N) (f : Lp ℂ 2 (volume : Measure (Fin d → ℝ)))
    (j : ℕ) (ek : {e : Finset (Fin d) // e.Nonempty} × (Fin d → ℤ)) :
    (tensorWaveletBasis m d hN).repr f (Sum.inr (j, ek)) =
      tensorCoeff (tensorWaveletFamily m d) j f ek :=
  tensorWaveletBasis_repr m hN f _

end Basis

/-! ### The coefficient quasi-norm as a weighted `ℓ_p` norm -/

section CoeffSums

/-- **The coefficient quasi-norm with `q = p` as a weighted sum**: for `0 < p < ∞`, every `s` and
every `f : ℝ^d → ℂ`, `Daubechies.tensorCoeffNorm m p s p f < ∞` iff
`∑_i (w_i |∫ f conj b_i|)^p < ∞` over the tensor wavelet system, with the weights
`w_i = 2^(j(s + d/2 - d/p))` at the wavelets of level `j` and `1` at the scaling functions
(`Daubechies.tensorWaveletWeight`). The sum splits into the scaling part and the wavelet part
(Mathlib's `Summable.tsum_sum`, `ENNReal.tsum_prod'`), and the `p`-th power of the `ℓ_p` norm of
the `ℓ_p` norms of the levels is the double sum (`ENNReal.lqNorm_lqNorm_rpow`). -/
theorem tensorCoeffNorm_lt_top_iff_tsum {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (s : ℝ)
    (f : (Fin d → ℝ) → ℂ) :
    tensorCoeffNorm m p s p f < ∞ ↔
      ∑' i, (tensorWaveletWeight (s + d * (1 / 2 - 1 / p.toReal)) i *
        ‖∫ x, f x * conj (tensorWaveletFun m d i x)‖ₑ) ^ p.toReal < ∞ := by
  have hτ : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable, ENNReal.tsum_prod', tensorCoeffNorm,
    ENNReal.add_lt_top, ENNReal.add_lt_top, ← ENNReal.rpow_lt_top_iff_of_pos hτ,
    ENNReal.lqNorm_rpow hp0 hp]
  simp only [tensorWaveletWeight_inl, tensorWaveletWeight_inr, one_mul,
    integral_mul_conj_tensorWaveletFun_inl, integral_mul_conj_tensorWaveletFun_inr]
  refine and_congr Iff.rfl ?_
  simp_rw [← ENNReal.lqNorm_const_mul]
  rw [← ENNReal.rpow_lt_top_iff_of_pos hτ, ENNReal.lqNorm_lqNorm_rpow hp0 hp]

/-- **The coefficient quasi-norm for `p = q = 2`** is finite iff
`∑_i (w_i |∫ f conj b_i|)² < ∞` with the weights `w_i = 2^(js)` at the wavelets of level `j` and
`1` at the scaling functions: the case `p = 2` of
`Daubechies.tensorCoeffNorm_lt_top_iff_tsum`, where `s + d(1/2 - 1/2) = s`. -/
theorem tensorCoeffNorm_two_lt_top_iff (s : ℝ) (f : (Fin d → ℝ) → ℂ) :
    tensorCoeffNorm m 2 s 2 f < ∞ ↔
      ∑' i, (tensorWaveletWeight s i * ‖∫ x, f x * conj (tensorWaveletFun m d i x)‖ₑ) ^ 2 < ∞ := by
  have h := tensorCoeffNorm_lt_top_iff_tsum m two_ne_zero ENNReal.ofNat_ne_top s f
  simpa only [ENNReal.toReal_ofNat, sub_self, mul_zero, add_zero, ENNReal.rpow_two] using h

end CoeffSums

/-! ### `H^s` as a weighted `ℓ_2` of the coefficients -/

section Sobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The coefficient quasi-norm in grid coordinates through the basis**: for `N ≥ 2`, every `s`
and every `f ∈ L_2(V)`, the coefficient quasi-norm of `f ∘ (Rd.gridCoord V)⁻¹` for `p = q = 2`
is finite iff `∑_i (w_i |⟨b_i, f ∘ (Rd.gridCoord V)⁻¹⟩|)² < ∞`, with the coefficients in the
tensor wavelet basis of `L_2(ℝ^n)` of the class of `f ∘ (Rd.gridCoord V)⁻¹` and the weights
`Daubechies.tensorWaveletWeight s` (`Daubechies.tensorCoeffNorm_two_lt_top_iff`,
`Daubechies.tensorWaveletBasis_repr`). -/
theorem tensorCoeffNorm_two_comp_gridCoord_lt_top_iff (hN : 2 ≤ N) (s : ℝ)
    (f : Lp ℂ 2 (volume : Measure V)) :
    tensorCoeffNorm m 2 s 2 (f ∘ (Rd.gridCoord V).symm) < ∞ ↔
      ∑' i, (tensorWaveletWeight s i * ‖(tensorWaveletBasis m (finrank ℝ V) hN).repr
        (Lp.compMeasurePreserving (Rd.gridCoord V).symm
          (Rd.measurePreserving_gridCoord_symm (V := V)) f) i‖ₑ) ^ 2 < ∞ := by
  rw [← tensorCoeffNorm_congr_ae m (Lp.coeFn_compMeasurePreserving f
    (Rd.measurePreserving_gridCoord_symm (V := V))) 2 s 2, tensorCoeffNorm_two_lt_top_iff]
  simp only [tensorWaveletBasis_repr]

/-- **`H^s` as a weighted `ℓ_2` of the tensor wavelet coefficients**: let `V` be a
finite-dimensional real inner product space of dimension `n`, `N ≥ 2`, let `φ` have a Bernstein
bound of order `θ` in `L_2` with differences of order `N`, and let `0 < s < θ` with `s < N`.
A tempered distribution `u` lies in `H^s(V)` iff it is a function `f ∈ L_2(V)` whose
coefficients in the tensor wavelet basis of `L_2(ℝ^n)`, taken in the coordinates of the dyadic
grid, satisfy `∑_k |⟨b_k, f⟩|² + ∑_{j,e,k} 2^(2js) |⟨b_{j,e,k}, f⟩|² < ∞`, that is,
`∑_i (w_i |⟨b_i, f⟩|)² < ∞` with `w_i = 2^(js)` at the wavelets of level `j`
(`Daubechies.memSobolev_two_iff_tensorCoeff`,
`Daubechies.tensorCoeffNorm_two_comp_gridCoord_lt_top_iff`). -/
theorem memSobolev_two_iff_weighted (hN : 2 ≤ N) {θ : ℝ} (hB : BernsteinBound m 2 θ N) {s : ℝ}
    (hs : 0 < s) (hsθ : s < θ) (hsN : s < N) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure V),
      (f : 𝓢'(V, ℂ)) = u ∧ ∑' i, (tensorWaveletWeight s i *
        ‖(tensorWaveletBasis m (finrank ℝ V) hN).repr (Lp.compMeasurePreserving
          (Rd.gridCoord V).symm (Rd.measurePreserving_gridCoord_symm (V := V)) f) i‖ₑ) ^ 2 < ∞ := by
  rw [memSobolev_two_iff_tensorCoeff m hN hB hs hsθ hsN]
  exact exists_congr fun f =>
    and_congr_right fun _ => tensorCoeffNorm_two_comp_gridCoord_lt_top_iff m hN s f

/-- **`H^s` as a weighted `ℓ_2` for masks of order three**: for every Daubechies mask of order
`N = 3`, every finite-dimensional real inner product space `V` and every
`0 < s < 3 - log₂ 3 ≈ 1.415`, a tempered distribution `u` lies in `H^s(V)` iff it is a function
`f ∈ L_2(V)` with `∑_i (w_i |⟨b_i, f⟩|)² < ∞` in the tensor wavelet basis, in the coordinates of
the dyadic grid. The range covers `H^1`
(`Daubechies.memSobolev_two_iff_tensorCoeff_order_three`,
`Daubechies.tensorCoeffNorm_two_comp_gridCoord_lt_top_iff`). -/
theorem memSobolev_two_iff_weighted_order_three (m : Mask 3) {s : ℝ} (hs : 0 < s)
    (hsl : s < 3 - Real.logb 2 3) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure V),
      (f : 𝓢'(V, ℂ)) = u ∧ ∑' i, (tensorWaveletWeight s i *
        ‖(tensorWaveletBasis m (finrank ℝ V) (by norm_num)).repr (Lp.compMeasurePreserving
          (Rd.gridCoord V).symm (Rd.measurePreserving_gridCoord_symm (V := V)) f) i‖ₑ) ^ 2 < ∞ := by
  rw [memSobolev_two_iff_tensorCoeff_order_three m hs hsl]
  exact exists_congr fun f =>
    and_congr_right fun _ => tensorCoeffNorm_two_comp_gridCoord_lt_top_iff m _ s f

end Sobolev

/-! ### Synthesis in `L_p` -/

section Synthesis

/-- **The constant of the synthesis bound**: `C_0 + C (1 - 2^(-s))⁻¹` with the constants `C_0`
and `C` of the upper estimates of the scaling and the wavelet family on the cube
`[1 - N, 2N - 1]^d` (`Daubechies.tensorExpandConst`). For `s > 0` the factor
`(1 - 2^(-s))⁻¹ = ∑_j 2^(-js)` is finite (`ENNReal.tsum_dyadicWeight_neg`); for `s ≤ 0` it is `∞`.
The constant is the same for every level and every function. -/
noncomputable def tensorSynthesisConst (p : ℝ≥0∞) (s : ℝ) (d : ℕ) : ℝ≥0∞ :=
  tensorExpandConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p +
    tensorExpandConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p * (1 - 2 ^ (-s))⁻¹

/-- **The synthesis constant is finite** for `N ≥ 2`, `1 ≤ p` and `s > 0`: both upper constants
are finite (`Daubechies.tensorExpandConst_ne_top`), and so is `(1 - 2^(-s))⁻¹`
(`ENNReal.one_sub_two_rpow_neg_inv_ne_top`). -/
theorem tensorSynthesisConst_ne_top (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) {s : ℝ} (hs : 0 < s) :
    tensorSynthesisConst m p s d ≠ ∞ :=
  ENNReal.add_ne_top.2
    ⟨tensorExpandConst_ne_top (G := tensorScalingFamily m d) _ _ hp1
        fun _ => memLp_tensorGen m hN ∅ p,
      ENNReal.mul_ne_top (tensorExpandConst_ne_top (G := tensorWaveletFamily m d) _ _ hp1
        fun e => memLp_tensorGen m hN e.1 p) (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)⟩

/-- **The wavelet part of level `j` through the coefficient quasi-norm**: for `N ≥ 2`,
`1 ≤ p < ∞`, `q ≠ 0`, every `s`, every `f : ℝ^d → ℂ` and every level `j`,
`‖Q_j f‖_p ≤ C ‖f‖_coef 2^(-js)` with the constant `C` of the upper estimate of the wavelet family
and the coefficient quasi-norm `‖f‖_coef = Daubechies.tensorCoeffNorm m p s q f`. Upper stability
(`Daubechies.eLpNorm_tensorDetailFun_le`) bounds `‖Q_j f‖_p` by
`C 2^(jd(1/2 - 1/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p}`, and
`2^(j(s + d/2 - d/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p}` is one term of the `ℓ_q` norm in
`‖f‖_coef` (`ENNReal.le_lqNorm`). -/
theorem eLpNorm_tensorDetailFun_le_tensorCoeffNorm (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0) (j : ℕ) (f : (Fin d → ℝ) → ℂ) :
    eLpNorm (tensorDetailFun m j f) p volume ≤
      tensorExpandConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p *
        tensorCoeffNorm m p s q f * dyadicWeight (-s) j := by
  set β := lqNorm p (fun ek => ‖tensorCoeff (tensorWaveletFamily m d) j f ek‖ₑ)
  have hβ : dyadicWeight (s + d * (1 / 2 - 1 / p.toReal)) j * β ≤ tensorCoeffNorm m p s q f :=
    (ENNReal.le_lqNorm hq (fun j => dyadicWeight (s + d * (1 / 2 - 1 / p.toReal)) j *
      lqNorm p (fun ek => ‖tensorCoeff (tensorWaveletFamily m d) j f ek‖ₑ)) j).trans le_add_self
  have hw : dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j =
      dyadicWeight (-s) j * dyadicWeight (s + d * (1 / 2 - 1 / p.toReal)) j := by
    rw [← ENNReal.dyadicWeight_add]
    congr 1
    ring
  calc eLpNorm (tensorDetailFun m j f) p volume
      ≤ tensorExpandConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p *
          (dyadicWeight (d * (1 / 2 - 1 / p.toReal)) j * β) :=
        eLpNorm_tensorDetailFun_le m hN hp1 hp j f
    _ = tensorExpandConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p *
          (dyadicWeight (s + d * (1 / 2 - 1 / p.toReal)) j * β) * dyadicWeight (-s) j := by
        rw [hw]
        ring
    _ ≤ tensorExpandConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p *
          tensorCoeffNorm m p s q f * dyadicWeight (-s) j := by
        gcongr

/-- **The projections are bounded by the coefficient quasi-norm, uniformly in the level**: for
`N ≥ 2`, `1 ≤ p < ∞`, `q ≠ 0`, every `s`, every locally integrable `f` and every level `J`,
`‖P_J f‖_p ≤ (C_0 + C (1 - 2^(-s))⁻¹) ‖f‖_coef` with the synthesis constant
`Daubechies.tensorSynthesisConst`, finite for `s > 0`
(`Daubechies.tensorSynthesisConst_ne_top`). By `P_J f = P_0 f + ∑_{j<J} Q_j f`
(`Daubechies.tensorProjFun_eq_add_sum`), Minkowski's inequality,
`Daubechies.eLpNorm_tensorProjFun_zero_le`,
`Daubechies.eLpNorm_tensorDetailFun_le_tensorCoeffNorm` and `∑_j 2^(-js) = (1 - 2^(-s))⁻¹`
(`ENNReal.tsum_dyadicWeight_neg`). -/
theorem eLpNorm_tensorProjFun_le_tensorCoeffNorm (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0) {f : (Fin d → ℝ) → ℂ}
    (hf : LocallyIntegrable f volume) (J : ℕ) :
    eLpNorm (tensorProjFun m J f) p volume ≤
      tensorSynthesisConst m p s d * tensorCoeffNorm m p s q f := by
  rw [tensorSynthesisConst, tensorProjFun_eq_add_sum m hN hf J]
  set C₀ := tensorExpandConst (tensorScalingFamily m d) (1 - N) (2 * N - 1) p
  set C := tensorExpandConst (tensorWaveletFamily m d) (1 - N) (2 * N - 1) p
  have h0 : eLpNorm (tensorProjFun m 0 f) p volume ≤ C₀ * tensorCoeffNorm m p s q f :=
    (eLpNorm_tensorProjFun_zero_le m hN hp1 hp f).trans (by gcongr; exact le_self_add)
  calc eLpNorm (tensorProjFun m 0 f + ∑ j ∈ Finset.range J, tensorDetailFun m j f) p volume
      ≤ eLpNorm (tensorProjFun m 0 f) p volume +
          ∑ j ∈ Finset.range J, eLpNorm (tensorDetailFun m j f) p volume :=
        (eLpNorm_add_le hp1).trans (add_le_add le_rfl (eLpNorm_sum_le hp1))
    _ ≤ C₀ * tensorCoeffNorm m p s q f +
          ∑' j, C * tensorCoeffNorm m p s q f * dyadicWeight (-s) j :=
        add_le_add h0 ((Finset.sum_le_sum fun j _ =>
          eLpNorm_tensorDetailFun_le_tensorCoeffNorm m hN hp1 hp hq j f).trans
          (ENNReal.sum_le_tsum _))
    _ = (C₀ + C * (1 - 2 ^ (-s))⁻¹) * tensorCoeffNorm m p s q f := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
        ring

/-- **A finite coefficient quasi-norm gives a function of `L_p`**: let `N ≥ 2`, `1 ≤ r < ∞`,
`1 ≤ p < ∞`, `s > 0` and `q ≠ 0`. Every `f ∈ L_r(ℝ^d)` with
`Daubechies.tensorCoeffNorm m p s q f < ∞` lies in `L_p(ℝ^d)`. The projections `P_J f` converge to
`f` in `L_r` (`Daubechies.tendsto_tensorProj`), hence in measure, and their `L_p` norms are
bounded uniformly by a finite multiple of the quasi-norm
(`Daubechies.eLpNorm_tensorProjFun_le_tensorCoeffNorm`, `Daubechies.tensorSynthesisConst_ne_top`),
so the bound passes to `f` (Mathlib's `MeasureTheory.eLpNorm_le_of_tendstoInMeasure`, by
Fatou's lemma along an almost everywhere convergent subsequence). -/
theorem memLp_of_tensorCoeffNorm_lt_top (hN : 2 ≤ N) {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : r ≠ ∞)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : q ≠ 0)
    (f : Lp ℂ r (volume : Measure (Fin d → ℝ))) (hf : tensorCoeffNorm m p s q f < ∞) :
    MemLp f p volume := by
  have hm : TendstoInMeasure volume (fun J => tensorProjFun m J f) atTop f :=
    (tendstoInMeasure_of_tendsto_Lp (tendsto_tensorProj m hN hr f)).congr_left
      fun J => tensorProj_apply_ae m hN hr J f
  exact memLp_iff.2 ((eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall fun J =>
      eLpNorm_tensorProjFun_le_tensorCoeffNorm m hN hp1 hp hq
        ((Lp.memLp f).locallyIntegrable Fact.out) J) hm
      fun J => (continuous_tensorProjFun m hN J f).aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top (tensorSynthesisConst_ne_top m hN hp1 hs).lt_top hf))

end Synthesis

/-! ### `n`-term approximation from the basis -/

section NTerm

/-- **`n`-term approximation from the tensor wavelet basis by coefficients**: let `N ≥ 2` and
`0 < p < 2`, with `τ = p.toReal` and `θ = 1/τ - 1/2`. An `f ∈ L_2(ℝ^d)` lies in the
approximation space `A^θ_τ` of `n`-term approximation from the basis iff its coefficient
quasi-norm with `p = q = τ` and the smoothness `dθ`,
`‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_τ} + ‖(‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_τ})_j‖_{ℓ_τ}`, is finite: the weight
`2^(j(dθ + d/2 - d/τ))` is `1`. This is the theorem of Stechkin and DeVore
(`HilbertBasis.memApprox_nTerm_iff`) with the coefficients of the basis
(`Daubechies.tensorWaveletBasis_repr`, `Daubechies.tensorCoeffNorm_lt_top_iff_tsum`). -/
theorem memApprox_nTerm_tensorWaveletBasis_iff_coeff (hN : 2 ≤ N) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp2 : p < 2) (f : Lp ℂ 2 (volume : Measure (Fin d → ℝ))) :
    (nTerm (tensorWaveletBasis m d hN).coeffDictionary).MemApprox (1 / p.toReal - 1 / 2) p f ↔
      tensorCoeffNorm m p (d * (1 / p.toReal - 1 / 2)) p f < ∞ := by
  have hp : p ≠ ∞ := ne_top_of_lt hp2
  have hτ0 : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hτ2 : p.toReal < 2 := by simpa using ENNReal.toReal_strict_mono ENNReal.ofNat_ne_top hp2
  have h := (tensorWaveletBasis m d hN).memApprox_nTerm_iff hτ0 hτ2 f
  rw [ENNReal.ofReal_toReal hp] at h
  refine h.trans ?_
  rw [tensorCoeffNorm_lt_top_iff_tsum m hp0 hp,
    show (d : ℝ) * (1 / p.toReal - 1 / 2) + d * (1 / 2 - 1 / p.toReal) = 0 by ring]
  simp only [tensorWaveletWeight_zero, one_mul, tensorWaveletBasis_repr]

/-- **`n`-term approximation from the tensor wavelet basis and Besov spaces**: let `N ≥ 2`,
`d ≥ 1`, `1 ≤ p < 2` with `τ = p.toReal`, `θ = 1/τ - 1/2` and `α = dθ`, and let `φ` have a
Bernstein bound of order `θ_B` in `L_τ` with differences of order `N`, where `α < θ_B` and
`α < N`. An `f ∈ L_2(ℝ^d)` lies in the approximation space `A^θ_τ` of `n`-term approximation from
the basis iff it lies in `L_τ(ℝ^d)` and `‖f‖_τ + ‖(2^(kα) ω_N(f, 2^(-k))_τ)_k‖_{ℓ_τ} < ∞`, that is,
`A^θ_τ = B^α_{τ,τ}(ℝ^d) ∩ L_2(ℝ^d)`. Both conditions say that the coefficient quasi-norm with
`p = q = τ` and smoothness `α` is finite
(`Daubechies.memApprox_nTerm_tensorWaveletBasis_iff_coeff`, `Daubechies.tensor_besov_iff_coeff`);
a function of `L_2` with this quasi-norm finite lies in `L_τ`
(`Daubechies.memLp_of_tensorCoeffNorm_lt_top`, as `α > 0`). This is the case `1 ≤ τ < 2` of
the theorem of DeVore, Jawerth and Popov for the tensor Daubechies wavelets (DeVore, *Nonlinear
approximation*, Acta Numer. 1998, §7.6 and Remark 7.6). -/
theorem memApprox_nTerm_tensorWaveletBasis_iff (hN : 2 ≤ N) (hd : 0 < d) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp2 : p < 2) {θB : ℝ} (hB : BernsteinBound m p θB N)
    (hαθ : d * (1 / p.toReal - 1 / 2) < θB) (hαN : d * (1 / p.toReal - 1 / 2) < N)
    (f : Lp ℂ 2 (volume : Measure (Fin d → ℝ))) :
    (nTerm (tensorWaveletBasis m d hN).coeffDictionary).MemApprox (1 / p.toReal - 1 / 2) p f ↔
      ∃ g : Lp ℂ p (volume : Measure (Fin d → ℝ)), (g : (Fin d → ℝ) → ℂ) =ᵐ[volume] f ∧
        ‖g‖ₑ + lqNorm p (fun k => dyadicWeight (d * (1 / p.toReal - 1 / 2)) k *
          Rd.lpModulus p N g k) < ∞ := by
  have hp1 : 1 ≤ p := Fact.out
  have hp : p ≠ ∞ := ne_top_of_lt hp2
  have hτ2 : p.toReal < 2 := by simpa using ENNReal.toReal_strict_mono ENNReal.ofNat_ne_top hp2
  have hα : 0 < (d : ℝ) * (1 / p.toReal - 1 / 2) := by
    have hτ0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp1).ne' hp
    have h := one_div_lt_one_div_of_lt hτ0 hτ2
    exact mul_pos (Nat.cast_pos.2 hd) (by linarith)
  rw [memApprox_nTerm_tensorWaveletBasis_iff_coeff m hN (zero_lt_one.trans_le hp1).ne' hp2]
  constructor
  · intro hc
    have hfp := memLp_of_tensorCoeffNorm_lt_top m hN ENNReal.ofNat_ne_top hp1 hp hα
      (zero_lt_one.trans_le hp1).ne' f hc
    refine ⟨hfp.toLp _, MemLp.coeFn_toLp hfp, ?_⟩
    rw [tensor_besov_iff_coeff m hN hp hB hα hαθ hαN hp1,
      tensorCoeffNorm_congr_ae m (MemLp.coeFn_toLp hfp)]
    exact hc
  · rintro ⟨g, hg, hb⟩
    rwa [tensor_besov_iff_coeff m hN hp hB hα hαθ hαN hp1, tensorCoeffNorm_congr_ae m hg] at hb

end NTerm

end Daubechies
