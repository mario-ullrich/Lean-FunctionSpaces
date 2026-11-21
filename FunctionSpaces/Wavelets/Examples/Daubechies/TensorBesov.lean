/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Analysis.Differences.LinearEquivModuli
public import FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley
public import FunctionSpaces.Wavelets.Examples.Daubechies.D4Besov
public import FunctionSpaces.Wavelets.Examples.Daubechies.OrderThree
public import FunctionSpaces.Wavelets.Examples.Daubechies.TensorJackson

/-!
# Besov spaces on `ℝ^d` by tensor Daubechies coefficients

For a Daubechies mask of order `N ≥ 2` with tensor scaling function `Φ` and tensor wavelets
`Ψ^e`, `e ≠ ∅` (`Daubechies.tensorGen`), `1 ≤ p < ∞` and `1 ≤ q ≤ ∞`, this file characterises the
Besov spaces `B^s_{p,q}(ℝ^d)` by the coefficients `⟨f, Φ(· - k)⟩` and `⟨f, Ψ^e_{j,k}⟩`, where
`G_{j,k}(x) = 2^(jd/2) G(2^j x - k)`. With the **coefficient quasi-norm**

`‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + d/2 - d/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p})_j‖_{ℓ_q}`

(`Daubechies.tensorCoeffNorm`), the main theorem (`Daubechies.tensor_besov_iff_coeff`) reads: if
`φ` has a Bernstein bound `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1` (`Daubechies.BernsteinBound`),
then for `0 < s < θ` with `s < N` and every `f ∈ L_p(ℝ^d)`

`‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞  ⟺  ‖f‖_coef < ∞`,

with the isotropic modulus of smoothness for the sup norm of `ℝ^d`.

* **Approximation and moduli.** For `s < θ' ≤ θ`, `θ' < N`, Jackson's inequality
  (`Daubechies.approxError_tensorScheme_le`) and the inverse inequality of order `θ'`
  (`Daubechies.tensor_inverse_scheme`) make the modulus compatible with the tensor scheme
  (`Daubechies.tensorModulusData`), so the coincidence theorem gives
  `f ∈ A^s_q ⟺ ‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` for `0 ≤ s < θ`, `s < N`
  (`Daubechies.memApprox_tensorScheme_iff_modulus`).
* **Approximation and coefficients.** The projections form a projection scheme with dense union
  (`Daubechies.closure_iUnion_tensorScheme`), the blocks are the wavelet expansions of one level,
  and their norms are comparable with the weighted `ℓ_p` norms of the wavelet coefficients
  (`Daubechies.enorm_tensorBlock_equiv`), so `f ∈ A^s_q ⟺ ‖f‖_coef < ∞` for `s > 0`
  (`Daubechies.memApprox_tensorScheme_iff_coeff`).
* **The regularity of `φ`.** As on `ℝ`, the theorem holds for `0 < s < N - log₄ λ` if `p ≤ 2`
  and `T^n 1 ≤ C λ^n` (`Daubechies.tensor_besov_iff_coeff_of_le_two`), for interpolated orders if
  `p ≥ 2` (`Daubechies.tensor_besov_iff_coeff_of_two_le`), for masks of order three
  (`Daubechies.tensor_besov_iff_coeff_order_three_le_two`,
  `Daubechies.tensor_besov_iff_coeff_order_three_two_le`,
  `Daubechies.tensor_besov_iff_coeff_order_three`) and for D4
  (`Daubechies.tensor_besov_iff_coeff_d4_le_two`, `Daubechies.tensor_besov_iff_coeff_d4_two_le`,
  `Daubechies.tensor_besov_iff_coeff_d4`), with the same ranges of `s` as on `ℝ`. The condition
  `s < N` costs no generality, since every Bernstein bound has `θ ≤ N` (a function with
  `ω_N(f, t)_p = o(t^N)` is a polynomial).
* **Every inner product space.** For a finite-dimensional real inner product space `V` of
  dimension `n`, the coordinates of the dyadic grid (`Rd.gridCoord`) carry `L_p(V)` to `L_p(ℝ^n)`,
  and the Besov quasi-norms by differences are finite together
  (`Rd.modNorm_compMeasurePreserving_lt_top_iff`), so `F ∈ L_p(V)` lies in `B^s_{p,q}(V)` iff the
  coefficients of `F` in these coordinates have finite quasi-norm
  (`Daubechies.tensor_besov_iff_coeff_grid`). For `p = q = 2` the weight is `2^(js)`, and
  `H^s(V) = B^s_{2,2}(V)` is the weighted `ℓ_2` of the coefficients
  (`Daubechies.memSobolev_two_iff_tensorCoeff`); for masks of order three this holds for
  `0 < s < 3 - log₂ 3 ≈ 1.415`, which covers `H^1`
  (`Daubechies.memSobolev_two_iff_tensorCoeff_order_three`).
-/

@[expose] public section

open Filter MeasureTheory Module
open scoped ENNReal SchwartzMap Real
open ENNReal (dyadicWeight lqNorm)

namespace Daubechies

/-- **An inverse order between `s` and the bounds**: for `0 ≤ s < θ` and `s < N` there is `θ'`
with `s < θ'`, `0 ≤ θ' ≤ θ` and `θ' < N`, for instance `θ' = (s + min(θ, N))/2`. -/
theorem exists_tensor_inverse_order {s θ : ℝ} {N : ℕ} (hs : 0 ≤ s) (hsθ : s < θ)
    (hsN : s < N) : ∃ θ' : ℝ, s < θ' ∧ 0 ≤ θ' ∧ θ' ≤ θ ∧ θ' < N := by
  have h := lt_min hsθ hsN
  refine ⟨(s + min θ N) / 2, by linarith, by linarith, ?_, ?_⟩
  · linarith [min_le_left θ (N : ℝ)]
  · linarith [min_le_right θ (N : ℝ)]

variable {N : ℕ} (m : Mask N)

/-! ### The coefficient quasi-norm -/

section CoeffNorm

variable {d : ℕ}

/-- **The tensor Daubechies coefficient quasi-norm** of `f : ℝ^d → ℂ`, for the exponents `p, q`
and the smoothness `s`:
`‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + d/2 - d/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p})_j‖_{ℓ_q}`
with the coefficients `⟨f, G_{j,k}⟩ = ∫ f(x) conj G_{j,k}(x) dx` (`Daubechies.tensorCoeff`) of the
tensor scaling function `Φ` at level `0` and of the tensor wavelets `Ψ^e`, `e ≠ ∅`, at the levels
`j ∈ ℕ`. Its finiteness describes `B^s_{p,q}(ℝ^d)` (`Daubechies.tensor_besov_iff_coeff`). -/
noncomputable def tensorCoeffNorm (p : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) :
    ℝ≥0∞ :=
  lqNorm p (fun k : Fin d → ℤ => ‖tensorCoeff (tensorScalingFamily m d) 0 f ((), k)‖ₑ) +
    lqNorm q (fun j => dyadicWeight (s + d * (1 / 2 - 1 / p.toReal)) j *
      lqNorm p (fun ek => ‖tensorCoeff (tensorWaveletFamily m d) j f ek‖ₑ))

/-- **The coefficient quasi-norm depends only on the class of `f`**: if `f = f'` almost
everywhere, the coefficients agree (`Daubechies.tensorCoeff_congr_ae`). -/
theorem tensorCoeffNorm_congr_ae {f f' : (Fin d → ℝ) → ℂ} (h : f =ᵐ[volume] f') (p : ℝ≥0∞)
    (s : ℝ) (q : ℝ≥0∞) : tensorCoeffNorm m p s q f = tensorCoeffNorm m p s q f' := by
  simp only [tensorCoeffNorm, tensorCoeff_congr_ae h]

end CoeffNorm

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {d : ℕ}

/-! ### The modulus of smoothness and the tensor scheme -/

variable (p d) in
/-- **The modulus of smoothness is compatible with the tensor Daubechies scheme**: for `N ≥ 2`,
`1 ≤ p < ∞`, a Bernstein bound of order `θ` for `φ` with differences of order `N`
(`Daubechies.BernsteinBound`) and `0 ≤ θ' ≤ θ` with `θ' < N`, the isotropic modulus
`ω_N(f, 2^(-k))_p` (`Rd.lpModulus p N`) on `L_p(ℝ^d)` is compatible with the tensor scheme with
inverse order `θ'` (`ApproximationScheme.ModulusData`): Jackson's inequality from level `0` on
(`Daubechies.approxError_tensorScheme_le`) and the inverse inequality of order `θ'`
(`Daubechies.tensor_inverse_scheme`). -/
noncomputable def tensorModulusData (hN : 2 ≤ N) (hp : p ≠ ∞) {θ θ' : ℝ}
    (hB : BernsteinBound m p θ N) (hθ'0 : 0 ≤ θ') (hθ' : θ' ≤ θ) (hθ'N : θ' < N) :
    ApproximationScheme.ModulusData (tensorScheme m p d hN hp) θ' where
  modulus := Rd.lpModulus p N
  add_le := Rd.lpModulus_add_le N
  C0 := 2 ^ N
  C0_ne_top := by simp
  le_enorm := Rd.lpModulus_le N
  jacksonStart := 0
  CJ := tensorJacksonConst m p d
  CJ_ne_top := tensorJacksonConst_ne_top m hN p d
  jackson f k _ := approxError_tensorScheme_le m hN hp f k
  CB := (tensor_inverse_scheme m (d := d) hN hp hB hθ'0 hθ' hθ'N).choose
  CB_ne_top := (tensor_inverse_scheme m (d := d) hN hp hB hθ'0 hθ' hθ'N).choose_spec.1
  inverse := (tensor_inverse_scheme m (d := d) hN hp hB hθ'0 hθ' hθ'N).choose_spec.2

/-- **Approximation by the tensor scaling spaces and moduli of smoothness**: for `N ≥ 2`,
`1 ≤ p < ∞`, a Bernstein bound of order `θ` for `φ` with differences of order `N`, `1 ≤ q ≤ ∞`
and `0 ≤ s < θ` with `s < N`, an `f ∈ L_p(ℝ^d)` lies in the approximation space `A^s_q` of the
tensor Daubechies scheme iff `‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. This is the
coincidence theorem `ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top` for
`Daubechies.tensorModulusData` with an inverse order `θ'` between `s` and `min(θ, N)`
(`Daubechies.exists_tensor_inverse_order`). -/
theorem memApprox_tensorScheme_iff_modulus (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ}
    (hB : BernsteinBound m p θ N) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 ≤ s) (hsθ : s < θ)
    (hsN : s < N) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    (tensorScheme m p d hN hp).MemApprox s q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ := by
  obtain ⟨θ', hsθ', hθ'0, hθ', hθ'N⟩ := exists_tensor_inverse_order hs hsθ hsN
  exact (tensorModulusData m p d hN hp hB hθ'0 hθ' hθ'N).memApprox_iff_modNorm_lt_top hq hs hsθ' f

/-! ### Approximation and coefficients -/

/-- **The projection of complexity `1` of the tensor projection scheme is `P_0`**: the case
`k = 0` of `Daubechies.tensorProjectionScheme_two_pow`. -/
theorem tensorProjectionScheme_one (hN : 2 ≤ N) (hp : p ≠ ∞) :
    (tensorProjectionScheme m p d hN hp).P 1 = tensorProj m p d hN hp 0 := by
  simpa using tensorProjectionScheme_two_pow m (d := d) hN hp 0

/-- **The dyadic blocks of the tensor projection scheme**: for every `f ∈ L_p(ℝ^d)` and level `j`,
the block `P(2^(j+1)) f - P(2^j) f` is `P_{j+1} f - P_j f`
(`Daubechies.tensorProjectionScheme_two_pow`). -/
theorem tensorProjectionScheme_block (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    (tensorProjectionScheme m p d hN hp).block j f =
      tensorProj m p d hN hp (j + 1) f - tensorProj m p d hN hp j f := by
  rw [ApproximationScheme.ProjectionScheme.block, tensorProjectionScheme_two_pow,
    tensorProjectionScheme_two_pow]

/-- **Approximation by the tensor scaling spaces through coefficients**: for `N ≥ 2`,
`1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, an `f ∈ L_p(ℝ^d)` lies in the approximation space `A^s_q`
of the tensor Daubechies scheme iff its coefficient quasi-norm
`‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + d/2 - d/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p})_j‖_{ℓ_q}`
(`Daubechies.tensorCoeffNorm`) is finite. The projections form a projection scheme with dense
union (`Daubechies.closure_iUnion_tensorScheme`), so `f ∈ A^s_q` iff
`‖P_0 f‖_p + ‖(2^(js) ‖P_{j+1} f - P_j f‖_p)_j‖_{ℓ_q} < ∞`
(`ApproximationScheme.ProjectionScheme.memApprox_iff_blockNorm_lt_top`); `‖P_0 f‖_p` and the
scaling coefficients are finite together (`Daubechies.enorm_tensorProj_zero_equiv`), and
`2^(js) ‖P_{j+1} f - P_j f‖_p` is comparable with `2^(j(s + d/2 - d/p))` times the `ℓ_p` norm of
the wavelet coefficients of level `j`, uniformly in `j` (`Daubechies.enorm_tensorBlock_equiv`,
`ENNReal.lqNorm_lt_top_iff_of_le_mul`). -/
theorem memApprox_tensorScheme_iff_coeff (hN : 2 ≤ N) (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    (tensorScheme m p d hN hp).MemApprox s q f ↔ tensorCoeffNorm m p s q f < ∞ := by
  obtain ⟨K₀, _, hK₀, _, hKM₀⟩ := enorm_tensorProj_zero_equiv m (d := d) hN hp
  obtain ⟨K, M, hK, hM, hKM⟩ := enorm_tensorBlock_equiv m (d := d) hN hp
  rw [(tensorProjectionScheme m p d hN hp).memApprox_iff_blockNorm_lt_top
    (closure_iUnion_tensorScheme m hN hp) hs hq, ApproximationScheme.ProjectionScheme.blockNorm,
    tensorProjectionScheme_one, tensorCoeffNorm]
  simp only [tensorProjectionScheme_block, ENNReal.add_lt_top]
  refine and_congr ⟨fun _ => (hKM₀ f).1.trans_lt (ENNReal.mul_lt_top hK₀.lt_top enorm_lt_top),
    fun _ => enorm_lt_top⟩
    (ENNReal.lqNorm_lt_top_iff_of_le_mul hK hM (fun j => ?_) fun j => ?_)
  · rw [ENNReal.dyadicWeight_add, mul_assoc, mul_left_comm M]
    exact mul_le_mul' le_rfl (hKM f j).2
  · rw [ENNReal.dyadicWeight_add, mul_assoc, mul_left_comm K]
    exact mul_le_mul' le_rfl (hKM f j).1

/-! ### Besov spaces by tensor Daubechies coefficients -/

/-- **Besov spaces on `ℝ^d` by tensor Daubechies coefficients**: let `N ≥ 2`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, and let `φ` have a Bernstein bound `ω_N(φ, t)_p ≤ K t^θ` for `0 < t ≤ 1`
(`Daubechies.BernsteinBound`). Then for `0 < s < θ` with `s < N` and every `f ∈ L_p(ℝ^d)`,
`‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_p} + ‖(2^(j(s + d/2 - d/p)) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_p})_j‖_{ℓ_q} < ∞`
(`Daubechies.tensorCoeffNorm`), with the isotropic modulus of smoothness for the sup norm of
`ℝ^d`. Both conditions describe the approximation space `A^s_q` of the tensor Daubechies scheme
(`Daubechies.memApprox_tensorScheme_iff_modulus`, `Daubechies.memApprox_tensorScheme_iff_coeff`).
The condition `s < N` is needed only by the proof, which takes moduli of the generators of every
order `r ≤ N` (`Daubechies.eLpNorm_higherDiff_tensorGen_le`). It costs no generality, since every
Bernstein bound has `θ ≤ N`: for `θ > N` it would give `ω_N(φ, t)_p = o(t^N)`, so `φ` would be a
polynomial, and the only polynomial in `L_p(ℝ)`, `p < ∞`, is `0`, while `‖φ‖_2 = 1`.
-/
theorem tensor_besov_iff_coeff (hN : 2 ≤ N) (hp : p ≠ ∞) {θ : ℝ} (hB : BernsteinBound m p θ N)
    {s : ℝ} (hs : 0 < s) (hsθ : s < θ) (hsN : s < N) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ ↔
      tensorCoeffNorm m p s q f < ∞ :=
  (memApprox_tensorScheme_iff_modulus m hN hp hB hq hs.le hsθ hsN f).symm.trans
    (memApprox_tensorScheme_iff_coeff m hN hp hs hq f)

/-- **Besov spaces on `ℝ^d` by tensor Daubechies coefficients, `p ≤ 2`**: let `N ≥ 2`,
`1 ≤ p ≤ 2`, `1 ≤ q ≤ ∞`, and let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator
(`Daubechies.TransferGrowth`). Then for `0 < s < N - log₄ λ` and every `f ∈ L_p(ℝ^d)` the Besov
condition `‖f‖_p + ‖(2^(ks) ω_N(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` and the coefficient condition
`Daubechies.tensorCoeffNorm m p s q f < ∞` are equivalent (`Daubechies.tensor_besov_iff_coeff`
with the Bernstein bound of `Daubechies.exists_bernsteinBound_of_le_two`; `s < N` since `λ ≥ 1`,
`Daubechies.TransferGrowth.sub_logb_le`). -/
theorem tensor_besov_iff_coeff_of_le_two (hN : 2 ≤ N) (hp : p ≠ ∞) (hp2 : p ≤ 2) {lam C : ℝ}
    (hg : TransferGrowth N lam C) {s : ℝ} (hs : 0 < s) (hsl : s < N - Real.logb 4 lam)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ ↔
      tensorCoeffNorm m p s q f < ∞ := by
  obtain ⟨θ, hsθ, hB⟩ := exists_bernsteinBound_of_le_two m hN hp2 hg hs.le hsl
  exact tensor_besov_iff_coeff m hN hp hB hs hsθ (hsl.trans_le (hg.sub_logb_le (by omega))) hq f

/-- **Besov spaces on `ℝ^d` by tensor Daubechies coefficients, `p ≥ 2`**: let `N ≥ 2`,
`2 ≤ p < ∞`, `1 ≤ q ≤ ∞`, let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator, and
let `0 ≤ s' < N - log₄ λ` and `0 ≤ a < N - log₄ λ - 1/2`. Then for
`0 < s < (2/p) s' + (1 - 2/p) a` and every `f ∈ L_p(ℝ^d)` the Besov condition and the
coefficient condition `Daubechies.tensorCoeffNorm m p s q f < ∞` are equivalent
(`Daubechies.tensor_besov_iff_coeff` with the interpolated Bernstein bound
`Daubechies.bernsteinBound_interp`; the interpolated order is at most `N`,
`Daubechies.mul_add_one_sub_mul_le`). -/
theorem tensor_besov_iff_coeff_of_two_le (hN : 2 ≤ N) (hp : p ≠ ∞) (hp2 : 2 ≤ p) {lam C : ℝ}
    (hg : TransferGrowth N lam C) {s' a : ℝ} (hs'0 : 0 ≤ s') (hs' : s' < N - Real.logb 4 lam)
    (ha0 : 0 ≤ a) (ha : a < N - Real.logb 4 lam - 1 / 2) {s : ℝ} (hs : 0 < s)
    (hsθ : s < 2 / p.toReal * s' + (1 - 2 / p.toReal) * a) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N f k) < ∞ ↔
      tensorCoeffNorm m p s q f < ∞ := by
  have hle := hg.sub_logb_le (by omega)
  exact tensor_besov_iff_coeff m hN hp (bernsteinBound_interp m hN hp2 hg hs'0 hs' (by linarith)
    ha0 (by linarith) ha) hs hsθ
    (hsθ.trans_le (mul_add_one_sub_mul_le (two_div_toReal_mem_Icc hp hp2) (by linarith)
      (by linarith))) hq f

/-- **Tensor coefficients of order three, `p ≤ 2`**: for every Daubechies mask of order `N = 3`,
every `1 ≤ p ≤ 2`, `1 ≤ q ≤ ∞` and `0 < s < 3 - log₂ 3`, an `f ∈ L_p(ℝ^d)` satisfies
`‖f‖_p + ‖(2^(ks) ω_3(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`Daubechies.tensorCoeffNorm m p s q f < ∞` (`Daubechies.tensor_besov_iff_coeff_of_le_two` with
the growth bound `Daubechies.transferGrowth_three`). -/
theorem tensor_besov_iff_coeff_order_three_le_two (m : Mask 3) (hp2 : p ≤ 2) {s : ℝ}
    (hs : 0 < s) (hsl : s < 3 - Real.logb 2 3) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 3 f k) < ∞ ↔
      tensorCoeffNorm m p s q f < ∞ :=
  tensor_besov_iff_coeff_of_le_two m (by norm_num) (ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp2)
    hp2 transferGrowth_three hs (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hsl) hq f

/-- **Tensor coefficients of order three, `p ≥ 2`**: for every Daubechies mask of order `N = 3`,
every `2 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < (2/p)(3 - log₂ 3) + (1 - 2/p)(5/2 - log₂ 3)`, an `f ∈ L_p(ℝ^d)` satisfies the Besov
condition with differences of order `3` iff `Daubechies.tensorCoeffNorm m p s q f < ∞`
(`Daubechies.tensor_besov_iff_coeff_of_two_le` with the orders of
`Daubechies.exists_orders_order_three`). -/
theorem tensor_besov_iff_coeff_order_three_two_le (m : Mask 3) (hp : p ≠ ∞) (hp2 : 2 ≤ p)
    {s : ℝ} (hs : 0 < s)
    (hsθ : s < 2 / p.toReal * (3 - Real.logb 2 3) + (1 - 2 / p.toReal) * (5 / 2 - Real.logb 2 3))
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 3 f k) < ∞ ↔
      tensorCoeffNorm m p s q f < ∞ :=
  let ⟨_, _, hs'0, hs', ha0, ha, hsθ'⟩ := exists_orders_order_three hsθ
  tensor_besov_iff_coeff_of_two_le m (by norm_num) hp hp2 transferGrowth_three hs'0 hs' ha0 ha hs
    hsθ' hq f

/-- **Tensor coefficients of order three for every `p`**: for every Daubechies mask of order
`N = 3`, every `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `0 < s < 5/2 - log₂ 3 ≈ 0.915`, an `f ∈ L_p(ℝ^d)`
satisfies `‖f‖_p + ‖(2^(ks) ω_3(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`Daubechies.tensorCoeffNorm m p s q f < ∞`: for `p ≤ 2` by
`Daubechies.tensor_besov_iff_coeff_order_three_le_two`, for `p ≥ 2` by
`Daubechies.tensor_besov_iff_coeff_order_three_two_le`. -/
theorem tensor_besov_iff_coeff_order_three (m : Mask 3) (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsa : s < 5 / 2 - Real.logb 2 3) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 3 f k) < ∞ ↔
      tensorCoeffNorm m p s q f < ∞ := by
  rcases le_total p 2 with hp2 | hp2
  · exact tensor_besov_iff_coeff_order_three_le_two m hp2 hs (by linarith) hq f
  · have hw := (two_div_toReal_mem_Icc hp hp2).1
    exact tensor_besov_iff_coeff_order_three_two_le m hp hp2 hs (by linarith) hq f

/-- **Tensor D4 coefficients, `p ≤ 2`**: let `1 ≤ p ≤ 2`, `1 ≤ q ≤ ∞` and `0 < s < 1`. Then for
every `f ∈ L_p(ℝ^d)`, `‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`Daubechies.tensorCoeffNorm d4 p s q f < ∞`, with the tensor products of the scaling function
and the wavelet of D4. This is `Daubechies.tensor_besov_iff_coeff_of_le_two` with the growth
bound `T^n 1 ≤ 4^n` (`Daubechies.transferGrowth_two`), whose exponent is `2 - log₄ 4 = 1`;
`p ≤ 2` forces `p < ∞`. -/
theorem tensor_besov_iff_coeff_d4_le_two (hp2 : p ≤ 2) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 2 f k) < ∞ ↔
      tensorCoeffNorm d4 p s q f < ∞ :=
  tensor_besov_iff_coeff_of_le_two d4 le_rfl (ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp2) hp2
    transferGrowth_two hs (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; exact hs1) hq f

/-- **Tensor D4 coefficients, `p ≥ 2`**: let `2 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < 2/p + (1 - 2/p) α` with the Hölder exponent `α = 2 - log₂(1 + √3) ≈ 0.5500` of D4.
Then for every `f ∈ L_p(ℝ^d)`, `‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`Daubechies.tensorCoeffNorm d4 p s q f < ∞`. This is `Daubechies.tensor_besov_iff_coeff` with a
Bernstein bound of an order `θ ∈ (s, 1]` (`Daubechies.exists_bernsteinBound_d4_of_two_le`), so
`s < θ ≤ 1 < 2`. The bound decreases from `1` at `p = 2` to `α` as `p → ∞`. -/
theorem tensor_besov_iff_coeff_d4_two_le (hp : p ≠ ∞) (hp2 : 2 ≤ p) {s : ℝ} (hs : 0 < s)
    (hsb : s < 2 / p.toReal + (1 - 2 / p.toReal) * (2 - Real.logb 2 (1 + √3))) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 2 f k) < ∞ ↔
      tensorCoeffNorm d4 p s q f < ∞ := by
  obtain ⟨θ, hsθ, hθ1, hB⟩ := exists_bernsteinBound_d4_of_two_le hp hp2 hsb
  exact tensor_besov_iff_coeff d4 le_rfl hp hB hs hsθ (by push_cast; linarith) hq f

/-- **Tensor D4 coefficients for every `p`**: let `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and
`0 < s < α = 2 - log₂(1 + √3) ≈ 0.5500`. Then for every `f ∈ L_p(ℝ^d)`,
`‖f‖_p + ‖(2^(ks) ω_2(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff
`Daubechies.tensorCoeffNorm d4 p s q f < ∞`, with the tensor products of the scaling function
and the wavelet of D4. For `p ≤ 2` this is `Daubechies.tensor_besov_iff_coeff_d4_le_two`, since
`α < 1`; for `p ≥ 2` it is `Daubechies.tensor_besov_iff_coeff_d4_two_le`, since
`α ≤ 2/p + (1 - 2/p) α`. -/
theorem tensor_besov_iff_coeff_d4 (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (hsα : s < 2 - Real.logb 2 (1 + √3)) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure (Fin d → ℝ))) :
    ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p 2 f k) < ∞ ↔
      tensorCoeffNorm d4 p s q f < ∞ := by
  have hα1 := two_sub_logb_two_one_add_sqrt_three_lt_one
  rcases le_total p 2 with hp2 | hp2
  · exact tensor_besov_iff_coeff_d4_le_two hp2 hs (hsα.trans hα1) hq f
  · have hw := two_div_toReal_mem_Icc hp hp2
    have h := mul_nonneg hw.1 (sub_nonneg.2 hα1.le)
    exact tensor_besov_iff_coeff_d4_two_le hp hp2 hs (by linarith) hq f

end Lp

/-! ### Every finite-dimensional inner product space -/

section Grid

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Besov spaces on an inner product space by tensor Daubechies coefficients**: let `V` be a
finite-dimensional real inner product space of dimension `n`, `N ≥ 2`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
and let `φ` have a Bernstein bound of order `θ` with differences of order `N`. Then for
`0 < s < θ` with `s < N` and every `F ∈ L_p(V)`,
`‖F‖_p + ‖(2^(ks) ω_N(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` (with the Euclidean norm of `V`) iff the
coefficient quasi-norm of `F` in the coordinates of the dyadic grid, `F ∘ (Rd.gridCoord V)⁻¹`
on `ℝ^n`, is finite. The inverse coordinates preserve Lebesgue measure
(`Rd.measurePreserving_gridCoord_symm`), so the Besov quasi-norms of `F` and of
`F ∘ (Rd.gridCoord V)⁻¹` are finite together (`Rd.modNorm_compMeasurePreserving_lt_top_iff`),
and `Daubechies.tensor_besov_iff_coeff` applies on `ℝ^n`. -/
theorem tensor_besov_iff_coeff_grid {p : ℝ≥0∞} [Fact (1 ≤ p)] (hN : 2 ≤ N) (hp : p ≠ ∞)
    {θ : ℝ} (hB : BernsteinBound m p θ N) {s : ℝ} (hs : 0 < s) (hsθ : s < θ) (hsN : s < N)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (F : Lp ℂ p (volume : Measure V)) :
    ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p N F k) < ∞ ↔
      tensorCoeffNorm m p s q (F ∘ (Rd.gridCoord V).symm) < ∞ := by
  have he := Rd.measurePreserving_gridCoord_symm (V := V)
  rw [← Rd.modNorm_compMeasurePreserving_lt_top_iff (Rd.gridCoord V).symm he N s q F,
    tensor_besov_iff_coeff m hN hp hB hs hsθ hsN hq,
    tensorCoeffNorm_congr_ae m (Lp.coeFn_compMeasurePreserving F he)]

/-- **`H^s` on an inner product space by tensor Daubechies coefficients**: let `V` be a
finite-dimensional real inner product space, `N ≥ 2`, let `φ` have a Bernstein bound of order `θ`
in `L_2` with differences of order `N`, and let `0 < s < θ` with `s < N`. Then a tempered
distribution `u` lies in `H^s(V)` iff it is an `L_2(V)` function `f` whose coefficients in the
coordinates of the dyadic grid satisfy
`‖(⟨f, Φ(· - k)⟩)_k‖_{ℓ_2} + ‖(2^(js) ‖(⟨f, Ψ^e_{j,k}⟩)_{e,k}‖_{ℓ_2})_j‖_{ℓ_2} < ∞`; at
`p = q = 2` the weight `2^(j(s + d/2 - d/p))` is `2^(js)`. This is `H^s(V) = B^s_{2,2}(V)`
(`Rd.memSobolev_two_iff_exists_memApprox`, `Rd.memApprox_bandScheme_iff_modulus` with differences
of order `N > s`) and `Daubechies.tensor_besov_iff_coeff_grid`. -/
theorem memSobolev_two_iff_tensorCoeff (hN : 2 ≤ N) {θ : ℝ} (hB : BernsteinBound m 2 θ N)
    {s : ℝ} (hs : 0 < s) (hsθ : s < θ) (hsN : s < N) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure V),
      (f : 𝓢'(V, ℂ)) = u ∧ tensorCoeffNorm m 2 s 2 (f ∘ (Rd.gridCoord V).symm) < ∞ := by
  rw [Rd.memSobolev_two_iff_exists_memApprox hs]
  refine exists_congr fun f => and_congr_right fun _ => ?_
  rw [Rd.memApprox_bandScheme_iff_modulus Rd.two_ne_top hs.le hsN one_le_two f]
  exact tensor_besov_iff_coeff_grid m hN Rd.two_ne_top hB hs hsθ hsN one_le_two f

/-- **`H^s` by tensor Daubechies coefficients of order three**: for every Daubechies mask of
order `N = 3`, every finite-dimensional real inner product space `V` and every
`0 < s < 3 - log₂ 3 ≈ 1.415`, a tempered distribution `u` lies in `H^s(V)` iff it is an `L_2(V)`
function `f` with
`∑_k |⟨f, Φ(· - k)⟩|² + ∑_j 2^(2js) ∑_{e ≠ ∅, k} |⟨f, Ψ^e_{j,k}⟩|² < ∞` in the coordinates of the
dyadic grid (in the form `Daubechies.tensorCoeffNorm m 2 s 2 < ∞`). The range covers `H^1`.
This is `Daubechies.memSobolev_two_iff_tensorCoeff` with the Bernstein bound in `L_2` of
`Daubechies.exists_bernsteinBound_of_le_two` for the growth bound
`Daubechies.transferGrowth_three`; `s < 3` since `log₂ 3 > 0`. -/
theorem memSobolev_two_iff_tensorCoeff_order_three (m : Mask 3) {s : ℝ} (hs : 0 < s)
    (hsl : s < 3 - Real.logb 2 3) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure V),
      (f : 𝓢'(V, ℂ)) = u ∧ tensorCoeffNorm m 2 s 2 (f ∘ (Rd.gridCoord V).symm) < ∞ := by
  have hl : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  obtain ⟨θ, hsθ, hB⟩ := exists_bernsteinBound_of_le_two m (by norm_num) (le_refl (2 : ℝ≥0∞))
    transferGrowth_three hs.le (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hsl)
  exact memSobolev_two_iff_tensorCoeff m (by norm_num) hB hs hsθ (by push_cast; linarith) u

end Grid

end Daubechies
