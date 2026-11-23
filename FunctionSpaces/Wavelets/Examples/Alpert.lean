/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Wavelets.Examples.Multiscale
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Multiwavelets of Alpert type

The **detail space** on `[0, 1]` consists of the piecewise polynomials of degree `< r` on the
two halves `[0, 1/2)`, `[1/2, 1)` that are `L_2`-orthogonal to the polynomials of degree `< r`
(`Alpert.detail`). It has dimension `2r - r = r` (`Alpert.finrank_detail`, Mathlib's
`Submodule.finrank_add_inf_finrank_orthogonal'`), and an orthonormal basis of it
(`Alpert.detailBasis`, from Mathlib's `stdOrthonormalBasis`) gives the **multiwavelets**
`ψ_1, …, ψ_r` (`Alpert.psi`): piecewise polynomials on the two halves with `r` vanishing
moments, `∫_0^1 ψ_i x^l dx = 0` for `l < r`. B. Alpert (1993) chose one such basis explicitly
through Legendre polynomials; every orthonormal basis serves the same purpose, and the
characterisation below does not depend on the choice.

Here the detail space is constructed in `L_2[0, 1] = Lp ℂ 2 unitVol`, the piecewise polynomials
being parametrised by the coefficients of their two pieces (`Alpert.levelOne`), and the
polynomials by `Interval.coeffToLp`.

**The details in the multiwavelets.** Let `P_k` be the local `L_2`-orthogonal projections onto
the piecewise polynomials of level `k` (`Interval.ppProj`; their orthogonality is
`Interval.integral_sub_locProj_mul`). On each dyadic interval `I_{k,m}` the detail
`Δ_k f = P_{k+1} f - P_k f` (`Alpert.detailFun`) is a piecewise polynomial on the two halves,
orthogonal to the polynomials (`Alpert.integral_detailFun_mul`); moved to `[0, 1]` it lies in
the detail space, so
`Δ_k f = ∑_i ⟨f, ψ_{k,m,i}⟩ ψ_{k,m,i}` on `I_{k,m}`, `ψ_{k,m,i}(x) = 2^(k/2) ψ_i(2^k x - m)`
(`Alpert.ppFun_detailPieces_ae_eq`), with the coefficients `⟨f, ψ_{k,m,i}⟩` of `f` itself
(`Alpert.coeff`, `Alpert.integral_detailFun_mul_conj_psi`).

**Norms.** The multiwavelets are stable: `‖∑_i β_i ψ_i‖_{L_p[0,1]}` is comparable with
`‖β‖_{ℓ_p}` (`Alpert.exists_stable`, finite dimension). Hence
`‖Δ_k f‖_p ≍ 2^(k(1/2-1/p)) ‖(⟨f, ψ_{k,m,i}⟩)_{m,i}‖_{ℓ_p}` with constants independent of `f`
and `k` (`Alpert.exists_eLpNorm_detailFun_equiv`), and the multiscale characterisation of
`FunctionSpaces.Wavelets.Examples.Multiscale` becomes, for `1 ≤ p < ∞`, `1 ≤ q ≤ ∞` and `s > 0`,
`f ∈ A^s_q ↔ ‖P_0 f‖_p + ‖(2^(k(s+1/2-1/p)) ‖(⟨f, ψ_{k,m,i}⟩)_{m,i}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`
(`Alpert.memApprox_ppScheme_iff_coeff`). For `0 < s < 1/p` this describes `B^s_{p,q}[0, 1]` and
`B^s_{p,q}(𝕋)` (`Alpert.lqNorm_modulus_lt_top_iff_coeff`,
`Alpert.lqNorm_perModulus_lt_top_iff_coeff`). For `r = 1` the multiwavelet is a multiple of
modulus `1` of the Haar function, since the basis of the detail space comes from Mathlib's
`stdOrthonormalBasis`.
-/

@[expose] public section

open MeasureTheory Set Polynomial Module
open scoped ENNReal ComplexConjugate InnerProductSpace
open ENNReal (dyadicWeight)

namespace Alpert

open Interval

variable (r : ℕ)

/-! ### The detail space on `[0, 1]` -/

/-- The polynomial of degree `< r` with coefficients `c`. -/
noncomputable def pieceOf (c : Fin r → ℂ) : ℂ[X] := ((degreeLTEquiv ℂ r).symm c : ℂ[X])

/-- The polynomial with coefficients `c` has degree `< r`. -/
theorem pieceOf_mem (c : Fin r → ℂ) : pieceOf r c ∈ degreeLT ℂ r :=
  ((degreeLTEquiv ℂ r).symm c).2

/-- The polynomial with given coefficients is additive in them. -/
theorem pieceOf_add (c d : Fin r → ℂ) : pieceOf r (c + d) = pieceOf r c + pieceOf r d := by
  simp only [pieceOf, map_add, Submodule.coe_add]

/-- The polynomial with given coefficients is homogeneous in them. -/
theorem pieceOf_smul (a : ℂ) (c : Fin r → ℂ) : pieceOf r (a • c) = C a * pieceOf r c := by
  simp only [pieceOf, map_smul, Submodule.coe_smul, smul_eq_C_mul]

/-- The polynomial with the coefficients of `P` is `P`. -/
theorem pieceOf_degreeLTEquiv {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) :
    pieceOf r (degreeLTEquiv ℂ r ⟨P, hP⟩) = P := by
  simp only [pieceOf, LinearEquiv.symm_apply_apply]

/-- The pieces of level `1` on `[0, 1)` with coefficients `u 0` on `[0, 1/2)` and `u 1` on
`[1/2, 1)`. -/
noncomputable def twoPieces (u : Fin 2 → Fin r → ℂ) (n : ℕ) : ℂ[X] :=
  pieceOf r (u (if n = 0 then 0 else 1))

/-- The two pieces have degree `< r`. -/
theorem twoPieces_mem (u : Fin 2 → Fin r → ℂ) (n : ℕ) : twoPieces r u n ∈ degreeLT ℂ r :=
  pieceOf_mem r _

/-- The two pieces are additive in the coefficients. -/
theorem twoPieces_add (u v : Fin 2 → Fin r → ℂ) :
    twoPieces r (u + v) = twoPieces r u + twoPieces r v := by
  funext n
  simp only [twoPieces, Pi.add_apply, pieceOf_add]

/-- The two pieces are homogeneous in the coefficients. -/
theorem twoPieces_smul (a : ℂ) (u : Fin 2 → Fin r → ℂ) :
    twoPieces r (a • u) = fun n => C a * twoPieces r u n := by
  funext n
  simp only [twoPieces, Pi.smul_apply, pieceOf_smul]

/-- **The piecewise polynomials of level `1`** in `L_2[0, 1]`, parametrised by the coefficients
of their pieces on `[0, 1/2)` and on `[1/2, 1)`. -/
noncomputable def levelOne : (Fin 2 → Fin r → ℂ) →ₗ[ℂ] Lp ℂ 2 unitVol where
  toFun u := (memLp_ppFun 1 (twoPieces r u) 2).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    rw [twoPieces_add, ppFun_add]
  map_smul' a u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    rw [twoPieces_smul, ppFun_const_mul, Pi.smul_apply, smul_eq_mul]

/-- The function of `Alpert.levelOne u` is the piecewise polynomial with the pieces `u`. -/
theorem coeFn_levelOne (u : Fin 2 → Fin r → ℂ) :
    levelOne r u =ᵐ[unitVol] ppFun 1 (twoPieces r u) :=
  MemLp.coeFn_toLp (memLp_ppFun 1 (twoPieces r u) 2)

/-- A polynomial vanishing almost everywhere on a dyadic interval is zero. -/
theorem eq_zero_of_ae_dyadicIco {P : ℂ[X]} {j m : ℕ}
    (h : polyFun P =ᵐ[volume.restrict (dyadicIco j m)] 0) : P = 0 := by
  have hlt : (m : ℝ) / 2 ^ j < (m + 1) / 2 ^ j :=
    div_lt_div_of_pos_right (by linarith) (by positivity)
  rw [dyadicIco, Measure.restrict_congr_set Ico_ae_eq_Icc] at h
  exact eq_zero_of_ae_eq_zero hlt h

/-- The piecewise polynomials of level `1` are determined by their pieces. -/
theorem levelOne_injective : Function.Injective (levelOne r) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h0 : ppFun 1 (twoPieces r u) =ᵐ[unitVol] 0 :=
    (coeFn_levelOne r u).symm.trans ((Lp.ext_iff.1 hu).trans (Lp.coeFn_zero ℂ 2 unitVol))
  have hpiece : ∀ n < 2 ^ 1, twoPieces r u n = 0 := fun n hn =>
    eq_zero_of_ae_dyadicIco (j := 1) (m := n) <| by
      filter_upwards [ae_dyadicIco_of_unitVol h0 hn, ae_restrict_mem (measurableSet_dyadicIco 1 n)]
        with x hx hxI
      rw [← ppFun_eq_of_mem _ hn hxI, hx]
  funext i
  have hi := hpiece (i : ℕ) (by have := i.isLt; norm_num; omega)
  have hcoe : (u i : Fin r → ℂ) = degreeLTEquiv ℂ r ((degreeLTEquiv ℂ r).symm (u i)) := by
    simp
  fin_cases i
  · simp only [twoPieces, pieceOf, ↓reduceIte] at hi
    have h' : (degreeLTEquiv ℂ r).symm (u 0) = 0 := Subtype.ext hi
    simpa using congrArg (degreeLTEquiv ℂ r) h'
  · simp only [twoPieces, pieceOf, one_ne_zero, ↓reduceIte] at hi
    have h' : (degreeLTEquiv ℂ r).symm (u 1) = 0 := Subtype.ext hi
    simpa using congrArg (degreeLTEquiv ℂ r) h'

/-- The polynomials of degree `< r` in `L_2[0, 1]`. -/
noncomputable abbrev polyL2 : (Fin r → ℂ) →ₗ[ℂ] Lp ℂ 2 unitVol := coeffToLp 2 r 0 1

/-- **Polynomials are piecewise polynomials of level `1`**, with equal pieces. -/
theorem range_polyL2_le : LinearMap.range (polyL2 r) ≤ LinearMap.range (levelOne r) := by
  rintro _ ⟨c, rfl⟩
  refine ⟨fun _ => c, Lp.ext ?_⟩
  filter_upwards [coeFn_levelOne r (fun _ => c), MemLp.coeFn_toLp (memLp_polyFun
    ((degreeLTEquiv ℂ r).symm c : ℂ[X]) 2 0 1), ae_mem_Ico_unitVol] with x h1 h2 hx
  obtain ⟨hxI, hn⟩ := mem_dyadicIco_floor (k := 1) hx
  rw [h1, show polyL2 r c = (memLp_polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) 2 0 1).toLp _
    from rfl, h2, ppFun_eq_of_mem _ hn hxI]
  rfl

/-- The polynomials of degree `< r` form an `r`-dimensional subspace of `L_2[0, 1]`. -/
theorem finrank_range_polyL2 : finrank ℂ (LinearMap.range (polyL2 r)) = r := by
  rw [LinearMap.finrank_range_of_inj (coeffToLp_injective r zero_lt_one), Module.finrank_fin_fun]

/-- The piecewise polynomials of level `1` form a `2r`-dimensional subspace of `L_2[0, 1]`. -/
theorem finrank_range_levelOne : finrank ℂ (LinearMap.range (levelOne r)) = 2 * r := by
  rw [LinearMap.finrank_range_of_inj (levelOne_injective r), Module.finrank_pi_fintype]
  simp

/-- The **detail space** on `[0, 1]`: the piecewise polynomials of level `1` that are orthogonal
in `L_2[0, 1]` to the polynomials of degree `< r`. -/
noncomputable def detail : Submodule ℂ (Lp ℂ 2 unitVol) :=
  (LinearMap.range (polyL2 r))ᗮ ⊓ LinearMap.range (levelOne r)

/-- The detail space is finite-dimensional, as a subspace of the piecewise polynomials of
level `1`. -/
instance finiteDimensional_detail : FiniteDimensional ℂ (detail r) := by
  unfold detail
  infer_instance

/-- The detail space has dimension `r`: `2r` for the piecewise polynomials, less `r` for the
polynomials. -/
theorem finrank_detail : finrank ℂ (detail r) = r :=
  Submodule.finrank_add_inf_finrank_orthogonal' (range_polyL2_le r)
    (by rw [finrank_range_polyL2, finrank_range_levelOne]; ring)

/-- An **orthonormal basis of the detail space**. -/
noncomputable def detailBasis : OrthonormalBasis (Fin r) ℂ (detail r) :=
  (stdOrthonormalBasis ℂ (detail r)).reindex (finCongr (finrank_detail r))

/-- The basis vectors are piecewise polynomials of level `1`. -/
theorem detailBasis_mem_range (i : Fin r) :
    ((detailBasis r i : detail r) : Lp ℂ 2 unitVol) ∈ LinearMap.range (levelOne r) :=
  (detailBasis r i).2.2

/-- The coefficients of the pieces of the multiwavelet `ψ_i`. -/
noncomputable def psiPieces (i : Fin r) : Fin 2 → Fin r → ℂ :=
  (detailBasis_mem_range r i).choose

/-- `ψ_i` is the basis vector `i` of the detail space. -/
theorem levelOne_psiPieces (i : Fin r) :
    levelOne r (psiPieces r i) = (detailBasis r i : Lp ℂ 2 unitVol) :=
  (detailBasis_mem_range r i).choose_spec

/-- The **multiwavelets** `ψ_i`, `i < r`: the orthonormal basis `Alpert.detailBasis` of the
detail space as piecewise polynomials on `[0, 1/2)` and `[1/2, 1)`. -/
noncomputable def psi (i : Fin r) : ℝ → ℂ := ppFun 1 (twoPieces r (psiPieces r i))

/-- The function of the basis vector `i` is `ψ_i`. -/
theorem coeFn_detailBasis (i : Fin r) :
    ((detailBasis r i : detail r) : Lp ℂ 2 unitVol) =ᵐ[unitVol] psi r i := by
  rw [← levelOne_psiPieces]
  exact coeFn_levelOne r _

/-- The `L_2[0, 1]` inner product as an integral, `⟨f, g⟩ = ∫_0^1 conj f · g`. -/
theorem inner_eq_integral (f g : Lp ℂ 2 unitVol) :
    ⟪f, g⟫_ℂ = ∫ x in Icc (0 : ℝ) 1, conj (f x) * g x := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply']

/-! ### The multiwavelets as functions -/

/-- **The multiwavelets are orthonormal**: `∫_0^1 conj ψ_i ψ_j = δ_{ij}`. -/
theorem integral_conj_psi_mul_psi (i j : Fin r) :
    ∫ x in Icc (0 : ℝ) 1, conj (psi r i x) * psi r j x = if i = j then 1 else 0 := by
  rw [← orthonormal_iff_ite.1 (detailBasis r).orthonormal i j, Submodule.coe_inner,
    inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_detailBasis r i, coeFn_detailBasis r j] with x hi hj
  rw [hi, hj]

/-- **The multiwavelets have `r` vanishing moments**: `∫_0^1 conj P · ψ_i = 0` for every
polynomial `P` of degree `< r`. -/
theorem integral_conj_polyFun_mul_psi {P : ℂ[X]} (hP : P ∈ degreeLT ℂ r) (i : Fin r) :
    ∫ x in Icc (0 : ℝ) 1, conj (polyFun P x) * psi r i x = 0 := by
  have hmem : polyL2 r (degreeLTEquiv ℂ r ⟨P, hP⟩) ∈ LinearMap.range (polyL2 r) := ⟨_, rfl⟩
  have horth := Submodule.inner_right_of_mem_orthogonal hmem (detailBasis r i).2.1
  rw [inner_eq_integral] at horth
  rw [← horth]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_polyFun ((degreeLTEquiv ℂ r).symm
    (degreeLTEquiv ℂ r ⟨P, hP⟩) : ℂ[X]) 2 0 1), coeFn_detailBasis r i] with x h1 h2
  rw [show polyL2 r (degreeLTEquiv ℂ r ⟨P, hP⟩) = (memLp_polyFun ((degreeLTEquiv ℂ r).symm
    (degreeLTEquiv ℂ r ⟨P, hP⟩) : ℂ[X]) 2 0 1).toLp _ from rfl, h1, h2,
    LinearEquiv.symm_apply_apply]

/-- **Vanishing moments**, in the form `∫_0^1 Q ψ_i = 0` for every polynomial `Q` of degree
`< r`: apply `Alpert.integral_conj_polyFun_mul_psi` to the conjugate polynomial `Q̄`. -/
theorem integral_polyFun_mul_psi {Q : ℂ[X]} (hQ : Q ∈ degreeLT ℂ r) (i : Fin r) :
    ∫ x in Icc (0 : ℝ) 1, polyFun Q x * psi r i x = 0 := by
  have hmem : Q.map (starRingEnd ℂ) ∈ degreeLT ℂ r :=
    mem_degreeLT.2 (degree_map_le.trans_lt (mem_degreeLT.1 hQ))
  have h := integral_conj_polyFun_mul_psi r hmem i
  simpa only [polyFun_map_conj, Complex.conj_conj] using h

/-- **Expansion in the multiwavelets**: a piecewise polynomial `u` of level `1` orthogonal to the
polynomials of degree `< r` is `u = ∑_i ⟨ψ_i, u⟩ ψ_i` almost everywhere on `[0, 1]`. -/
theorem ppFun_ae_eq_sum_psi {u : Fin 2 → Fin r → ℂ}
    (hu : levelOne r u ∈ (LinearMap.range (polyL2 r))ᗮ) :
    ppFun 1 (twoPieces r u) =ᵐ[unitVol] fun x => ∑ i, (∫ t in Icc (0 : ℝ) 1,
      conj (psi r i t) * ppFun 1 (twoPieces r u) t) * psi r i x := by
  set w : detail r := ⟨levelOne r u, hu, ⟨u, rfl⟩⟩
  have hsum : ∑ i, ⟪(detailBasis r i : Lp ℂ 2 unitVol), levelOne r u⟫_ℂ •
      (detailBasis r i : Lp ℂ 2 unitVol) = levelOne r u := by
    have h := congrArg (fun v : detail r => (v : Lp ℂ 2 unitVol)) ((detailBasis r).sum_repr' w)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] using h
  have hcoef : ∀ i, ⟪(detailBasis r i : Lp ℂ 2 unitVol), levelOne r u⟫_ℂ =
      ∫ t in Icc (0 : ℝ) 1, conj (psi r i t) * ppFun 1 (twoPieces r u) t := fun i => by
    rw [inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_detailBasis r i, coeFn_levelOne r u] with x h1 h2
    rw [h1, h2]
  have hterms : ∀ᵐ x ∂unitVol, ∀ i, ((⟪(detailBasis r i : Lp ℂ 2 unitVol), levelOne r u⟫_ℂ •
      (detailBasis r i : Lp ℂ 2 unitVol) : Lp ℂ 2 unitVol) x) =
        ⟪(detailBasis r i : Lp ℂ 2 unitVol), levelOne r u⟫_ℂ * psi r i x := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [Lp.coeFn_smul (⟪(detailBasis r i : Lp ℂ 2 unitVol), levelOne r u⟫_ℂ)
      (detailBasis r i : Lp ℂ 2 unitVol), coeFn_detailBasis r i] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [(coeFn_levelOne r u).symm, Lp.coeFn_finsetSum Finset.univ
    (fun i => ⟪(detailBasis r i : Lp ℂ 2 unitVol), levelOne r u⟫_ℂ •
      (detailBasis r i : Lp ℂ 2 unitVol)), hterms] with x h1 h2 h3
  rw [h1, ← hsum, h2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [h3 i, hcoef i]

/-! ### Details on a dyadic interval -/

/-- **The fine projection is orthogonal on a coarse interval**: on `I_{k,m}`,
`∫ (g - P_{k+1} g) φ = 0` for every `φ` that is a polynomial of degree `< r` on each half. -/
theorem integral_sub_ppFun_succ_mul {g : ℝ → ℂ} (hg : IntegrableOn g (Icc 0 1)) {k m : ℕ}
    (hm : m < 2 ^ k) {φ : ℝ → ℂ}
    (hφ : ∀ e < 2, ∃ Q ∈ degreeLT ℂ r, ∀ x ∈ dyadicIco (k + 1) (2 * m + e), φ x = polyFun Q x) :
    ∫ x in dyadicIco k m, (g x - ppFun (k + 1) (locProj r (k + 1) g) x) * φ x = 0 := by
  have hidx : ∀ e < 2, 2 * m + e < 2 ^ (k + 1) := fun e he => by rw [pow_succ]; omega
  have hsub : ∀ e < 2, dyadicIco (k + 1) (2 * m + e) ⊆ Icc 0 1 := fun e he =>
    (dyadicIco_subset (hidx e he)).trans Ico_subset_Icc_self
  have hhalf : ∀ e < 2, IntegrableOn (fun x => (g x - ppFun (k + 1) (locProj r (k + 1) g) x) *
      φ x) (dyadicIco (k + 1) (2 * m + e)) ∧
      ∫ x in dyadicIco (k + 1) (2 * m + e),
        (g x - ppFun (k + 1) (locProj r (k + 1) g) x) * φ x = 0 := fun e he => by
    obtain ⟨Q, hQ, hφQ⟩ := hφ e he
    have heq : EqOn (fun x => (g x - polyFun (locProj r (k + 1) g (2 * m + e)) x) * polyFun Q x)
        (fun x => (g x - ppFun (k + 1) (locProj r (k + 1) g) x) * φ x)
        (dyadicIco (k + 1) (2 * m + e)) := fun x hx => by
      simp only [ppFun_eq_of_mem _ (hidx e he) hx, hφQ x hx]
    have hgI : IntegrableOn g (dyadicIco (k + 1) (2 * m + e)) := hg.mono_set (hsub e he)
    refine ⟨IntegrableOn.congr_fun ?_ heq (measurableSet_dyadicIco _ _), ?_⟩
    · exact integrableOn_mul_polyFun (hgI.sub (integrableOn_dyadicIco_of_continuous
        (continuous_polyFun _) _ _)) (measurableSet_dyadicIco _ _) (hsub e he) Q
    · rw [← setIntegral_congr_fun (measurableSet_dyadicIco _ _) heq]
      exact integral_sub_locProj_mul hgI hQ
  have h0 := hhalf 0 (by norm_num)
  have h1 := hhalf 1 (by norm_num)
  simp only [add_zero] at h0
  rw [dyadicIco_eq_union, setIntegral_union (disjoint_dyadicIco_halves k m)
    (measurableSet_dyadicIco _ _) h0.1 h1.1, h0.2, h1.2, add_zero]

variable {r}

/-- The **detail** `Δ_k g = P_{k+1} g - P_k g` of `g` at level `k`, as a function: the
difference of the local projections of levels `k + 1` and `k`. -/
noncomputable def detailFun (r : ℕ) (g : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ppFun (k + 1) (locProj r (k + 1) g) x - ppFun k (locProj r k g) x

/-- **The details are orthogonal to the polynomials** on every interval `I_{k,m}`:
`∫_{I_{k,m}} Δ_k g · Q = 0` for every polynomial `Q` of degree `< r`. -/
theorem integral_detailFun_mul {g : ℝ → ℂ} (hg : IntegrableOn g (Icc 0 1)) {k m : ℕ}
    (hm : m < 2 ^ k) {Q : ℂ[X]} (hQ : Q ∈ degreeLT ℂ r) :
    ∫ x in dyadicIco k m, detailFun r g k x * polyFun Q x = 0 := by
  have hsub : dyadicIco k m ⊆ Icc 0 1 := (dyadicIco_subset hm).trans Ico_subset_Icc_self
  have hgI : IntegrableOn g (dyadicIco k m) := hg.mono_set hsub
  have hfine : IntegrableOn (fun x => (g x - ppFun (k + 1) (locProj r (k + 1) g) x) *
      polyFun Q x) (dyadicIco k m) :=
    integrableOn_mul_polyFun (hgI.sub ((integrableOn_ppFun _ _).mono_set hsub))
      (measurableSet_dyadicIco _ _) hsub Q
  have hcoarse : IntegrableOn (fun x => (g x - polyFun (locProj r k g m) x) * polyFun Q x)
      (dyadicIco k m) :=
    integrableOn_mul_polyFun (hgI.sub (integrableOn_dyadicIco_of_continuous
      (continuous_polyFun _) _ _)) (measurableSet_dyadicIco _ _) hsub Q
  have heq : EqOn (fun x => (g x - polyFun (locProj r k g m) x) * polyFun Q x -
      (g x - ppFun (k + 1) (locProj r (k + 1) g) x) * polyFun Q x)
      (fun x => detailFun r g k x * polyFun Q x) (dyadicIco k m) := fun x hx => by
    simp only [detailFun, ppFun_eq_of_mem _ hm hx]
    ring
  rw [← setIntegral_congr_fun (measurableSet_dyadicIco _ _) heq, integral_sub hcoarse hfine,
    integral_sub_locProj_mul hgI hQ,
    integral_sub_ppFun_succ_mul r hg hm fun e _ => ⟨Q, hQ, fun _ _ => rfl⟩, sub_zero]

/-- On the half `I_{k+1,2m+e}` of `I_{k,m}` the rescaled conjugate wavelet
`conj ψ_i(2^k x - m)` is a polynomial of degree `< r`. -/
theorem exists_conj_psi_eq_polyFun (i : Fin r) {k m e : ℕ} (he : e < 2) :
    ∃ Q ∈ degreeLT ℂ r, ∀ x ∈ dyadicIco (k + 1) (2 * m + e),
      conj (psi r i (2 ^ k * x - m)) = polyFun Q x := by
  set P := twoPieces r (psiPieces r i) e
  have hP : P ∈ degreeLT ℂ r := twoPieces_mem r _ e
  have hPc : P.map (starRingEnd ℂ) ∈ degreeLT ℂ r :=
    mem_degreeLT.2 (degree_map_le.trans_lt (mem_degreeLT.1 hP))
  refine ⟨(P.map (starRingEnd ℂ)).comp (C ((-(m : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X),
    comp_affine_mem_degreeLT hPc _ _, fun x hx => ?_⟩
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have ht : 2 ^ k * x - m ∈ dyadicIco 1 e := by
    rw [mem_dyadicIco] at hx ⊢
    push_cast at hx
    rw [pow_succ] at hx
    constructor <;> nlinarith [hx.1, hx.2]
  rw [psi, ppFun_eq_of_mem _ (by norm_num; omega) ht, polyFun_comp_affine, polyFun_map_conj]
  congr 2
  ring

/-- **The coarse projection is orthogonal to the wavelets** of its level:
`∫_{I_{k,m}} P_k g · conj ψ_i(2^k x - m) = 0`, by the vanishing moments of `ψ_i`. -/
theorem integral_ppFun_mul_conj_psi (g : ℝ → ℂ) {k m : ℕ} (hm : m < 2 ^ k) (i : Fin r) :
    ∫ x in dyadicIco k m, ppFun k (locProj r k g) x * conj (psi r i (2 ^ k * x - m)) = 0 := by
  have h2 : (((2 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  set R := (locProj r k g m).comp (C ((((m : ℝ) / 2 ^ k : ℝ)) : ℂ) + C (((1 / 2 ^ k : ℝ)) : ℂ) * X)
  have hR : R ∈ degreeLT ℂ r := comp_affine_mem_degreeLT (locProj_mem r k g m) _ _
  have hcongr : ∫ x in dyadicIco k m, ppFun k (locProj r k g) x * conj (psi r i (2 ^ k * x - m)) =
      ∫ x in dyadicIco k m, polyFun (locProj r k g m) x * conj (psi r i (2 ^ k * x - m)) :=
    setIntegral_congr_fun (measurableSet_dyadicIco _ _) fun x hx => by
      rw [ppFun_eq_of_mem _ hm hx]
  rw [hcongr]
  refine (mul_eq_zero.1 ?_).resolve_left h2
  rw [integral_dyadicIco_eq]
  have hval : ∀ t : ℝ, polyFun (locProj r k g m) (t / 2 ^ k + m / 2 ^ k) *
      conj (psi r i (2 ^ k * (t / 2 ^ k + m / 2 ^ k) - m)) =
        conj (conj (polyFun R t) * psi r i t) := fun t => by
    have e1 : (2 : ℝ) ^ k * (t / 2 ^ k + m / 2 ^ k) - m = t := by field_simp; ring
    rw [e1, map_mul, Complex.conj_conj, polyFun_comp_affine]
    congr 2
    ring
  simp only [hval]
  rw [integral_conj, integral_conj_polyFun_mul_psi r hR i, map_zero]

/-- **The wavelet coefficients of the detail are those of the function**:
`∫_{I_{k,m}} Δ_k g · conj ψ_i(2^k x - m) = ∫_{I_{k,m}} g · conj ψ_i(2^k x - m)`. -/
theorem integral_detailFun_mul_conj_psi {g : ℝ → ℂ} (hg : IntegrableOn g (Icc 0 1)) {k m : ℕ}
    (hm : m < 2 ^ k) (i : Fin r) :
    ∫ x in dyadicIco k m, detailFun r g k x * conj (psi r i (2 ^ k * x - m)) =
      ∫ x in dyadicIco k m, g x * conj (psi r i (2 ^ k * x - m)) := by
  have hsub : dyadicIco k m ⊆ Icc 0 1 := (dyadicIco_subset hm).trans Ico_subset_Icc_self
  have hgI : IntegrableOn g (dyadicIco k m) := hg.mono_set hsub
  -- the rescaled wavelet is bounded, since `ψ_i` is a piecewise polynomial
  obtain ⟨M, hM⟩ := exists_norm_ppFun_le 1 (twoPieces r (psiPieces r i))
  have hmeas : AEStronglyMeasurable (fun x => conj (psi r i (2 ^ k * x - m)))
      (volume.restrict (dyadicIco k m)) :=
    (Complex.continuous_conj.measurable.comp ((measurable_ppFun 1 _).comp
      (by fun_prop))).aestronglyMeasurable
  have hint : ∀ {F : ℝ → ℂ}, IntegrableOn F (dyadicIco k m) →
      IntegrableOn (fun x => F x * conj (psi r i (2 ^ k * x - m))) (dyadicIco k m) :=
    fun hF => hF.mul_bdd (c := M) hmeas (Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_conj]
      exact hM _)
  have hPfine := (integrableOn_ppFun (k + 1) (locProj r (k + 1) g)).mono_set hsub
  have hPcoarse := (integrableOn_ppFun k (locProj r k g)).mono_set hsub
  have heq : EqOn (fun x => g x * conj (psi r i (2 ^ k * x - m)) -
      (g x - ppFun (k + 1) (locProj r (k + 1) g) x) * conj (psi r i (2 ^ k * x - m)) -
      ppFun k (locProj r k g) x * conj (psi r i (2 ^ k * x - m)))
      (fun x => detailFun r g k x * conj (psi r i (2 ^ k * x - m))) (dyadicIco k m) :=
    fun x _ => by simp only [detailFun]; ring
  have hA : IntegrableOn (fun x => g x * conj (psi r i (2 ^ k * x - m))) (dyadicIco k m) :=
    hint hgI
  have hB : IntegrableOn (fun x => (g x - ppFun (k + 1) (locProj r (k + 1) g) x) *
      conj (psi r i (2 ^ k * x - m))) (dyadicIco k m) := hint (hgI.sub hPfine)
  have hC : IntegrableOn (fun x => ppFun k (locProj r k g) x * conj (psi r i (2 ^ k * x - m)))
      (dyadicIco k m) := hint hPcoarse
  have hAB : IntegrableOn (fun x => g x * conj (psi r i (2 ^ k * x - m)) -
      (g x - ppFun (k + 1) (locProj r (k + 1) g) x) * conj (psi r i (2 ^ k * x - m)))
      (dyadicIco k m) := hA.sub hB
  rw [← setIntegral_congr_fun (measurableSet_dyadicIco _ _) heq, integral_sub hAB hC,
    integral_sub hA hB,
    integral_sub_ppFun_succ_mul r hg hm fun _ he => exists_conj_psi_eq_polyFun i he,
    integral_ppFun_mul_conj_psi g hm i, sub_zero, sub_zero]

/-! ### Multiwavelet coefficients -/

variable (r) in
/-- The **multiwavelet coefficient** `⟨g, ψ_{k,m,i}⟩ = 2^(k/2) ∫_{I_{k,m}} g · conj ψ_i(2^k x - m)`
of `g`, for the wavelet `ψ_{k,m,i}(x) = 2^(k/2) ψ_i(2^k x - m)` supported in `I_{k,m}`. -/
noncomputable def coeff (g : ℝ → ℂ) (k m : ℕ) (i : Fin r) : ℂ :=
  (((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ∫ x in dyadicIco k m, g x * conj (psi r i (2 ^ k * x - m))

variable (r) in
/-- The coefficients of the pieces of the detail `Δ_k g` on `I_{k,m}` moved to `[0, 1]`: on the
half `e` the polynomial `(Π_{I_{k+1,2m+e}} g - Π_{I_{k,m}} g)(m 2^(-k) + 2^(-k) t)`. -/
noncomputable def detailPieces (g : ℝ → ℂ) (k m : ℕ) (e : Fin 2) : Fin r → ℂ :=
  degreeLTEquiv ℂ r ⟨(locProj r (k + 1) g (2 * m + e) - locProj r k g m).comp
    (C ((((m : ℝ) / 2 ^ k : ℝ)) : ℂ) + C (((1 / 2 ^ k : ℝ)) : ℂ) * X),
    comp_affine_mem_degreeLT (Submodule.sub_mem _ (locProj_mem _ _ _ _) (locProj_mem _ _ _ _))
      _ _⟩

/-- **The detail moved to `[0, 1]`**: for `t ∈ [0, 1)`, `Δ_k g(m 2^(-k) + 2^(-k) t)` is the
piecewise polynomial of level `1` with the pieces `Alpert.detailPieces`. -/
theorem ppFun_detailPieces (g : ℝ → ℂ) {k m : ℕ} (hm : m < 2 ^ k) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    ppFun 1 (twoPieces r (detailPieces r g k m)) t =
      detailFun r g k ((m : ℝ) / 2 ^ k + 1 / 2 ^ k * t) := by
  obtain ⟨htI, hn⟩ := mem_dyadicIco_floor (k := 1) ht
  set e := ⌊2 ^ 1 * t⌋₊ with he
  have he2 : e < 2 := by simpa using hn
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  set x := (m : ℝ) / 2 ^ k + 1 / 2 ^ k * t
  have hx1 : (2 : ℝ) ^ k * x = m + t := by simp only [x]; field_simp
  have hx2 : (2 : ℝ) ^ (k + 1) * x = 2 * m + 2 ^ 1 * t := by
    rw [pow_succ, mul_comm _ (2 : ℝ), mul_assoc, hx1]; ring
  have hxk : x ∈ dyadicIco k m := by
    rw [mem_dyadicIco, hx1]
    constructor <;> linarith [ht.1, ht.2]
  have hxk1 : x ∈ dyadicIco (k + 1) (2 * m + e) := by
    rw [mem_dyadicIco] at htI ⊢
    rw [hx2]
    push_cast
    constructor <;> linarith [htI.1, htI.2]
  have hidx : 2 * m + e < 2 ^ (k + 1) := by rw [pow_succ]; omega
  rw [ppFun_eq_of_mem _ hn htI, detailFun, ppFun_eq_of_mem _ hidx hxk1, ppFun_eq_of_mem _ hm hxk]
  have hpiece : twoPieces r (detailPieces r g k m) e =
      (locProj r (k + 1) g (2 * m + e) - locProj r k g m).comp
        (C ((((m : ℝ) / 2 ^ k : ℝ)) : ℂ) + C (((1 / 2 ^ k : ℝ)) : ℂ) * X) := by
    rcases (by omega : e = 0 ∨ e = 1) with h | h
    · simp only [twoPieces, h, ↓reduceIte, detailPieces, pieceOf_degreeLTEquiv, Fin.val_zero]
    · simp only [twoPieces, h, one_ne_zero, ↓reduceIte, detailPieces, pieceOf_degreeLTEquiv,
        Fin.val_one]
  rw [hpiece, polyFun_comp_affine]
  simp only [polyFun, eval_sub]
  rfl

/-- **The moved detail is orthogonal to the polynomials** in `L_2[0, 1]`. -/
theorem levelOne_detailPieces_mem {g : ℝ → ℂ} (hg : IntegrableOn g (Icc 0 1)) {k m : ℕ}
    (hm : m < 2 ^ k) : levelOne r (detailPieces r g k m) ∈ (LinearMap.range (polyL2 r))ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨c, rfl⟩
  rw [inner_eq_integral]
  set P : ℂ[X] := pieceOf r c
  have hP : P ∈ degreeLT ℂ r := pieceOf_mem r c
  have hPc : P.map (starRingEnd ℂ) ∈ degreeLT ℂ r :=
    mem_degreeLT.2 (degree_map_le.trans_lt (mem_degreeLT.1 hP))
  set Q : ℂ[X] := (P.map (starRingEnd ℂ)).comp
    (C ((-(m : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X)
  have hQ : Q ∈ degreeLT ℂ r := comp_affine_mem_degreeLT hPc _ _
  have h2 : (((2 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  have hcongr : ∫ t in Icc (0 : ℝ) 1, conj ((polyL2 r c : Lp ℂ 2 unitVol) t) *
      (levelOne r (detailPieces r g k m) : Lp ℂ 2 unitVol) t =
      ∫ t in Icc (0 : ℝ) 1, detailFun r g k (t / 2 ^ k + m / 2 ^ k) *
        polyFun Q (t / 2 ^ k + m / 2 ^ k) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_polyFun P 2 0 1),
      coeFn_levelOne r (detailPieces r g k m), ae_mem_Ico_unitVol] with t h1 h2' ht
    rw [show (polyL2 r c : Lp ℂ 2 unitVol) = (memLp_polyFun P 2 0 1).toLp _ from rfl, h1, h2',
      ppFun_detailPieces g hm ht, polyFun_comp_affine, polyFun_map_conj]
    have e1 : -(m : ℝ) + 2 ^ k * (t / 2 ^ k + m / 2 ^ k) = t := by field_simp; ring
    have e2 : (m : ℝ) / 2 ^ k + 1 / 2 ^ k * t = t / 2 ^ k + m / 2 ^ k := by ring
    rw [e1, e2, mul_comm]
  calc ∫ t in Icc (0 : ℝ) 1, conj ((polyL2 r c : Lp ℂ 2 unitVol) t) *
        (levelOne r (detailPieces r g k m) : Lp ℂ 2 unitVol) t
      = ∫ t in Icc (0 : ℝ) 1, detailFun r g k (t / 2 ^ k + m / 2 ^ k) *
          polyFun Q (t / 2 ^ k + m / 2 ^ k) := hcongr
    _ = (((2 : ℝ) ^ k : ℝ) : ℂ) * ∫ x in dyadicIco k m, detailFun r g k x * polyFun Q x :=
        (integral_dyadicIco_eq k m (fun x => detailFun r g k x * polyFun Q x)).symm
    _ = 0 := by rw [integral_detailFun_mul hg hm hQ, mul_zero]

/-- The coefficient of `ψ_i` in the moved detail is `2^(k/2)` times the multiwavelet coefficient
`⟨g, ψ_{k,m,i}⟩`. -/
theorem integral_conj_psi_mul_detailPieces {g : ℝ → ℂ} (hg : IntegrableOn g (Icc 0 1))
    {k m : ℕ} (hm : m < 2 ^ k) (i : Fin r) :
    ∫ t in Icc (0 : ℝ) 1, conj (psi r i t) * ppFun 1 (twoPieces r (detailPieces r g k m)) t =
      (((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * coeff r g k m i := by
  have hcongr : ∫ t in Icc (0 : ℝ) 1, conj (psi r i t) *
      ppFun 1 (twoPieces r (detailPieces r g k m)) t =
      ∫ t in Icc (0 : ℝ) 1, detailFun r g k (t / 2 ^ k + m / 2 ^ k) *
        conj (psi r i (2 ^ k * (t / 2 ^ k + m / 2 ^ k) - m)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Ico_unitVol] with t ht
    have e1 : (2 : ℝ) ^ k * (t / 2 ^ k + m / 2 ^ k) - m = t := by field_simp; ring
    have e2 : (m : ℝ) / 2 ^ k + 1 / 2 ^ k * t = t / 2 ^ k + m / 2 ^ k := by ring
    rw [ppFun_detailPieces g hm ht, e1, e2, mul_comm]
  have hc : (((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) =
      (((2 : ℝ) ^ k : ℝ) : ℂ) := by
    rw [ofReal_two_rpow_half_mul_self]
    push_cast
    rfl
  calc ∫ t in Icc (0 : ℝ) 1, conj (psi r i t) * ppFun 1 (twoPieces r (detailPieces r g k m)) t
      = ∫ t in Icc (0 : ℝ) 1, detailFun r g k (t / 2 ^ k + m / 2 ^ k) *
          conj (psi r i (2 ^ k * (t / 2 ^ k + m / 2 ^ k) - m)) := hcongr
    _ = (((2 : ℝ) ^ k : ℝ) : ℂ) * ∫ x in dyadicIco k m,
          detailFun r g k x * conj (psi r i (2 ^ k * x - m)) :=
        (integral_dyadicIco_eq k m
          (fun x => detailFun r g k x * conj (psi r i (2 ^ k * x - m)))).symm
    _ = _ := by
        rw [integral_detailFun_mul_conj_psi hg hm i, coeff, ← mul_assoc, hc]

/-- **The moved detail in the multiwavelets**: almost everywhere on `[0, 1]`,
`Δ_k g(m 2^(-k) + 2^(-k) t) = ∑_i 2^(k/2) ⟨g, ψ_{k,m,i}⟩ ψ_i(t)`. -/
theorem ppFun_detailPieces_ae_eq {g : ℝ → ℂ} (hg : IntegrableOn g (Icc 0 1)) {k m : ℕ}
    (hm : m < 2 ^ k) :
    ppFun 1 (twoPieces r (detailPieces r g k m)) =ᵐ[unitVol] fun t =>
      ∑ i, ((((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * coeff r g k m i) * psi r i t := by
  filter_upwards [ppFun_ae_eq_sum_psi r (levelOne_detailPieces_mem hg hm)] with t ht
  rw [ht]
  simp only [integral_conj_psi_mul_detailPieces hg hm]

/-! ### Stability and the norms of the details -/

variable (r) in
/-- `conj ψ_j · F` is integrable on `[0, 1]` for bounded `F`. -/
theorem integrable_conj_psi_mul (j : Fin r) {F : ℝ → ℂ} (hF : MemLp F ∞ unitVol) :
    Integrable (fun t => conj (psi r j t) * F t) unitVol := by
  have h1 : Integrable (fun t => conj (psi r j t)) unitVol := by
    simp only [psi, conj_ppFun]
    exact (memLp_ppFun 1 _ 1).integrable le_rfl
  exact h1.mul_of_top_left hF

variable (r) in
/-- `∫_0^1 conj ψ_j ∑_i β_i ψ_i = β_j`, by orthonormality. -/
theorem integral_conj_psi_mul_sum (β : Fin r → ℂ) (j : Fin r) :
    ∫ t in Icc (0 : ℝ) 1, conj (psi r j t) * ∑ i, β i * psi r i t = β j := by
  have hint : ∀ i, Integrable (fun t => conj (psi r j t) * (β i * psi r i t)) unitVol := fun i =>
    integrable_conj_psi_mul r j ((memLp_ppFun 1 (twoPieces r (psiPieces r i)) ∞).const_mul (β i))
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint i]
  simp only [mul_left_comm _ (β _), integral_const_mul, integral_conj_psi_mul_psi, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
variable (r p) in
/-- Combinations of the multiwavelets lie in `L_p[0, 1]`. -/
theorem memLp_sum_psi (β : Fin r → ℂ) : MemLp (fun t => ∑ i, β i * psi r i t) p unitVol :=
  memLp_finsetSum _ fun i _ => (memLp_ppFun 1 (twoPieces r (psiPieces r i)) p).const_mul (β i)

variable (r p) in
/-- The combinations `∑_i β_i ψ_i` in `L_p[0, 1]`, as a linear map of the coefficients. -/
noncomputable def sumPsi : (Fin r → ℂ) →ₗ[ℂ] Lp ℂ p unitVol where
  toFun β := (memLp_sum_psi r p β).toLp _
  map_add' β γ := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a β := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [Fact (1 ≤ p)] in
/-- The function of `Alpert.sumPsi β` is `∑_i β_i ψ_i`. -/
theorem coeFn_sumPsi (β : Fin r → ℂ) :
    sumPsi r p β =ᵐ[unitVol] fun t => ∑ i, β i * psi r i t :=
  MemLp.coeFn_toLp (memLp_sum_psi r p β)

omit [Fact (1 ≤ p)] in
variable (r p) in
/-- The multiwavelets are linearly independent in `L_p[0, 1]`: `β_j` is the coefficient of `ψ_j`
in `∑_i β_i ψ_i` (`Alpert.integral_conj_psi_mul_sum`). -/
theorem sumPsi_injective : Function.Injective (sumPsi r p) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro β hβ
  have h0 : (fun t => ∑ i, β i * psi r i t) =ᵐ[unitVol] 0 :=
    (coeFn_sumPsi β).symm.trans ((Lp.ext_iff.1 hβ).trans (Lp.coeFn_zero ℂ p unitVol))
  funext j
  rw [← integral_conj_psi_mul_sum r β j, Pi.zero_apply]
  refine (integral_congr_ae (h0.mono fun t ht => ?_)).trans (integral_zero _ _)
  simp only [ht, Pi.zero_apply, mul_zero]

variable (r) in
/-- **Stability of the multiwavelet combinations** in `L_p[0, 1]`, `1 ≤ p ≤ ∞`: there are
`K, M < ∞` with `‖β‖_{ℓ_p} ≤ K ‖∑_i β_i ψ_i‖_p` and `‖∑_i β_i ψ_i‖_p ≤ M ‖β‖_{ℓ_p}` for all
coefficients `β`; the first by the equivalence of norms on the `r`-dimensional space of
coefficients (`LinearMap.injective_iff_antilipschitz`, applied to `β` and `0`), the second by the
triangle inequality. -/
theorem exists_stable : ∃ K M : ℝ≥0∞, K ≠ ∞ ∧ M ≠ ∞ ∧ ∀ β : Fin r → ℂ,
    ENNReal.lqNorm p (fun i => ‖β i‖ₑ) ≤
      K * eLpNorm (fun t => ∑ i, β i * psi r i t) p unitVol ∧
    eLpNorm (fun t => ∑ i, β i * psi r i t) p unitVol ≤
      M * ENNReal.lqNorm p (fun i => ‖β i‖ₑ) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  obtain ⟨K, -, hK⟩ := (sumPsi r p).injective_iff_antilipschitz.1 (sumPsi_injective r p)
  refine ⟨(Fintype.card (Fin r) : ℝ≥0∞) ^ (1 / p.toReal) * K, ∑ i, eLpNorm (psi r i) p unitVol,
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _))
      ENNReal.coe_ne_top,
    ENNReal.sum_ne_top.2 fun i _ => (memLp_ppFun 1 (twoPieces r (psiPieces r i)) p).eLpNorm_ne_top,
    fun β => ⟨?_, ?_⟩⟩
  · have hnorm : ‖sumPsi r p β‖ₑ = eLpNorm (fun t => ∑ i, β i * psi r i t) p unitVol := by
      rw [Lp.enorm_def]
      exact eLpNorm_congr_ae (coeFn_sumPsi β)
    have hbe : ‖β‖ₑ ≤ K * ‖sumPsi r p β‖ₑ := by
      simpa only [edist_zero_right, map_zero] using hK β 0
    calc ENNReal.lqNorm p (fun i => ‖β i‖ₑ)
        ≤ (Fintype.card (Fin r) : ℝ≥0∞) ^ (1 / p.toReal) * ‖β‖ₑ :=
          ENNReal.lqNorm_le_card_rpow_mul fun i => by
            rw [← ofReal_norm, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm β i)
      _ ≤ (Fintype.card (Fin r) : ℝ≥0∞) ^ (1 / p.toReal) * (K * ‖sumPsi r p β‖ₑ) := by gcongr
      _ = _ := by rw [hnorm, mul_assoc]
  · have hsmul : ∀ i, (fun t => β i * psi r i t) = β i • psi r i := fun i => rfl
    calc eLpNorm (fun t => ∑ i, β i * psi r i t) p unitVol
        ≤ ∑ i, eLpNorm (fun t => β i * psi r i t) p unitVol := by
          have h := eLpNorm_sum_le (f := fun i t => β i * psi r i t) (s := Finset.univ)
            (μ := unitVol) (Fact.out : 1 ≤ p)
          convert h using 2
          funext t
          simp only [Finset.sum_apply]
      _ = ∑ i, ‖β i‖ₑ * eLpNorm (psi r i) p unitVol := by
          simp only [hsmul, eLpNorm_const_smul]
      _ ≤ ∑ i, ENNReal.lqNorm p (fun i => ‖β i‖ₑ) * eLpNorm (psi r i) p unitVol := by
          gcongr with i
          exact ENNReal.le_lqNorm hp0 (fun i => ‖β i‖ₑ) i
      _ = _ := by rw [← Finset.mul_sum, mul_comm]

omit [Fact (1 ≤ p)] in
/-- **The detail on one interval through the multiwavelets**:
`2^(k/p) ‖Δ_k g‖_{L_p(I_{k,m})} = ‖∑_i 2^(k/2) ⟨g, ψ_{k,m,i}⟩ ψ_i‖_{L_p[0, 1]}`. -/
theorem eLpNorm_detailFun_dyadicIco (hp : p ≠ ∞) {g : ℝ → ℂ} (hg : IntegrableOn g (Icc 0 1))
    {k m : ℕ} (hm : m < 2 ^ k) :
    dyadicWeight (1 / p.toReal) k * eLpNorm (detailFun r g k) p (volume.restrict (dyadicIco k m)) =
      eLpNorm (fun t => ∑ i, ((((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * coeff r g k m i) *
        psi r i t) p unitVol := by
  have hmeas : Measurable (detailFun r g k) := (measurable_ppFun _ _).sub (measurable_ppFun _ _)
  have h :=
    interval_eLpNorm_comp_affine hmeas hp ((m : ℝ) / 2 ^ k) (L := 1 / 2 ^ k) (by positivity) 0 1
  rw [mul_zero, add_zero, mul_one] at h
  have hL : eLpNorm (fun y => detailFun r g k ((m : ℝ) / 2 ^ k + 1 / 2 ^ k * y)) p unitVol =
      eLpNorm (fun t => ∑ i, ((((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * coeff r g k m i) *
        psi r i t) p unitVol := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_mem_Ico_unitVol, ppFun_detailPieces_ae_eq hg hm] with t ht h2
    rw [← ppFun_detailPieces g hm ht, h2]
  have hR : volume.restrict (Icc ((m : ℝ) / 2 ^ k) (m / 2 ^ k + 1 / 2 ^ k)) =
      volume.restrict (dyadicIco k m) := by
    rw [dyadicIco, show ((m : ℝ) + 1) / 2 ^ k = m / 2 ^ k + 1 / 2 ^ k by ring]
    exact (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  have hw : ENNReal.ofReal (1 / 2 ^ k)⁻¹ ^ (1 / p.toReal) = dyadicWeight (1 / p.toReal) k := by
    rw [one_div ((2 : ℝ) ^ k), inv_inv, ENNReal.ofReal_two_pow_eq, ENNReal.dyadicWeight_rpow, one_mul]
  rw [← hL, show (unitVol : Measure ℝ) = volume.restrict (Icc 0 1) from rfl, h, hR, hw]

/-- **The norm of a detail through its multiwavelet coefficients**: for `1 ≤ p < ∞` there are
`K, M < ∞` with
`2^(k(1/2-1/p)) ‖(⟨g, ψ_{k,m,i}⟩)_{m,i}‖_{ℓ_p} ≤ K ‖Δ_k g‖_p` and
`‖Δ_k g‖_p ≤ M 2^(k(1/2-1/p)) ‖(⟨g, ψ_{k,m,i}⟩)_{m,i}‖_{ℓ_p}`
for every `g` integrable on `[0, 1]` and every `k`: on each of the `2^k` intervals the detail is
a moved multiwavelet combination (`Alpert.eLpNorm_detailFun_dyadicIco`), whose norm is that of
its coefficients up to the constants of `Alpert.exists_stable`. -/
theorem exists_eLpNorm_detailFun_equiv (hp : p ≠ ∞) : ∃ K M : ℝ≥0∞, K ≠ ∞ ∧ M ≠ ∞ ∧
    ∀ g : ℝ → ℂ, IntegrableOn g (Icc 0 1) → ∀ k : ℕ,
      dyadicWeight (1 / 2 - 1 / p.toReal) k * ENNReal.lqNorm p
        (fun mi : Fin (2 ^ k) × Fin r => ‖coeff r g k mi.1 mi.2‖ₑ) ≤
          K * eLpNorm (detailFun r g k) p unitVol ∧
      eLpNorm (detailFun r g k) p unitVol ≤ M * (dyadicWeight (1 / 2 - 1 / p.toReal) k *
        ENNReal.lqNorm p (fun mi : Fin (2 ^ k) × Fin r => ‖coeff r g k mi.1 mi.2‖ₑ)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨K, M, hK, hM, hKM⟩ := exists_stable (p := p) r
  refine ⟨K, M, hK, hM, fun g hg k => ?_⟩
  set A := eLpNorm (detailFun r g k) p unitVol
  set β : Fin (2 ^ k) → Fin r → ℂ := fun m i =>
    (((2 : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * coeff r g k m i
  set S : Fin (2 ^ k) → ℝ≥0∞ := fun m => eLpNorm (fun t => ∑ i, β m i * psi r i t) p unitVol
  set F := ENNReal.lqNorm p (fun mi : Fin (2 ^ k) × Fin r => ‖coeff r g k mi.1 mi.2‖ₑ)
  have hmeas : Measurable (detailFun r g k) := (measurable_ppFun _ _).sub (measurable_ppFun _ _)
  -- the level norm in pieces
  have hA : dyadicWeight 1 k * A ^ p.toReal = ∑ m, S m ^ p.toReal := by
    rw [eLpNorm_rpow_eq hmeas.aestronglyMeasurable hp0 hp,
      show (∫⁻ x, ‖detailFun r g k x‖ₑ ^ p.toReal ∂unitVol) =
        ∫⁻ x in Icc (0 : ℝ) 1, ‖detailFun r g k x‖ₑ ^ p.toReal from rfl,
      lintegral_unit_eq_sum_dyadicIco _ k, Finset.mul_sum, Finset.sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← eLpNorm_rpow_eq hmeas.aestronglyMeasurable hp0 hp,
      show dyadicWeight 1 k = dyadicWeight (1 / p.toReal) k ^ p.toReal by
        rw [ENNReal.dyadicWeight_rpow, one_div_mul_cancel hq.ne'],
      ← ENNReal.mul_rpow_of_nonneg _ _ hq.le, eLpNorm_detailFun_dyadicIco hp hg m.isLt]
  -- the coefficients in pieces
  have hβ : ENNReal.lqNorm p (fun mi : Fin (2 ^ k) × Fin r => ‖β mi.1 mi.2‖ₑ) =
      dyadicWeight (1 / 2) k * F := by
    simp only [β, enorm_mul, enorm_two_rpow_half]
    exact ENNReal.lqNorm_const_mul _ _
  have hβm : (dyadicWeight (1 / 2) k * F) ^ p.toReal =
      ∑ m, ENNReal.lqNorm p (fun i => ‖β m i‖ₑ) ^ p.toReal := by
    rw [← hβ, ENNReal.lqNorm_prod_rpow hp0 hp]
  have hroot : ∀ {x y : ℝ≥0∞}, x ^ p.toReal ≤ y ^ p.toReal → x ≤ y := fun h =>
    (ENNReal.rpow_le_rpow_iff hq).1 h
  have hw : dyadicWeight (1 / p.toReal) k ^ p.toReal = dyadicWeight 1 k := by
    rw [ENNReal.dyadicWeight_rpow, one_div_mul_cancel hq.ne']
  have hsplit : dyadicWeight (1 / 2 - 1 / p.toReal) k * dyadicWeight (1 / p.toReal) k =
      dyadicWeight (1 / 2) k := by
    rw [← ENNReal.dyadicWeight_add, sub_add_cancel]
  have hw0 := ENNReal.dyadicWeight_ne_zero (1 / p.toReal) k
  have hwt := ENNReal.dyadicWeight_ne_top (1 / p.toReal) k
  constructor
  · -- `2^(k/2) F ≤ K 2^(k/p) A`, then cancel `2^(k/p)`
    have h1 : dyadicWeight (1 / 2) k * F ≤ K * (dyadicWeight (1 / p.toReal) k * A) := by
      refine hroot ?_
      rw [hβm, ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le, hw, hA,
        Finset.mul_sum]
      exact Finset.sum_le_sum fun m _ => by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
        exact ENNReal.rpow_le_rpow (hKM (β m)).1 hq.le
    rw [← ENNReal.mul_le_mul_iff_left hw0 hwt]
    exact le_of_eq_of_le (by rw [← hsplit]; ring) (h1.trans_eq (by ring))
  · -- `2^(k/p) A ≤ M 2^(k/2) F`, then cancel `2^(k/p)`
    have h1 : dyadicWeight (1 / p.toReal) k * A ≤ M * (dyadicWeight (1 / 2) k * F) := by
      refine hroot ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, hw, hA, ENNReal.mul_rpow_of_nonneg _ _ hq.le, hβm,
        Finset.mul_sum]
      exact Finset.sum_le_sum fun m _ => by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
        exact ENNReal.rpow_le_rpow (hKM (β m)).2 hq.le
    rw [← ENNReal.mul_le_mul_iff_left hw0 hwt]
    exact le_of_eq_of_le (mul_comm _ _) (h1.trans_eq (by rw [← hsplit]; ring))

/-! ### The coefficient characterisation -/

/-- The detail `P_{k+1} f - P_k f` in `L_p[0, 1]` is the function `Alpert.detailFun`. -/
theorem enorm_ppProj_sub (hp : p ≠ ∞) (f : Lp ℂ p unitVol) (k : ℕ) :
    ‖ppProj p hp r (k + 1) f - ppProj p hp r k f‖ₑ = eLpNorm (detailFun r f k) p unitVol := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
    ((coeFn_ppProj hp r (k + 1) f).sub (coeFn_ppProj hp r k f)))

/-- **Approximation by piecewise polynomials through multiwavelet coefficients**: for
`1 ≤ p < ∞`, `r ≥ 1`, `s > 0` and `1 ≤ q ≤ ∞`, an `f ∈ L_p[0, 1]` lies in the approximation space
`A^s_q` of the dyadic piecewise polynomials of degree `< r` iff
`‖P_0 f‖_p + ‖(2^(k(s + 1/2 - 1/p)) ‖(⟨f, ψ_{k,m,i}⟩)_{m < 2^k, i < r}‖_{ℓ_p})_k‖_{ℓ_q} < ∞`. -/
theorem memApprox_ppScheme_iff_coeff (hp : p ≠ ∞) (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    (ppScheme p r).MemApprox s q f ↔ ‖ppProj p hp r 0 f‖ₑ + ENNReal.lqNorm q (fun k =>
      dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k * ENNReal.lqNorm p
        (fun mi : Fin (2 ^ k) × Fin r => ‖coeff r f k mi.1 mi.2‖ₑ)) < ∞ := by
  obtain ⟨K, M, hK, hM, hKM⟩ := exists_eLpNorm_detailFun_equiv (r := r) hp
  have hf : IntegrableOn (f : ℝ → ℂ) (Icc 0 1) := (Lp.memLp f).integrable Fact.out
  rw [memApprox_ppScheme_iff_block hp hr hs hq f]
  simp only [enorm_ppProj_sub hp f, ENNReal.add_lt_top]
  refine and_congr Iff.rfl (ENNReal.lqNorm_lt_top_iff_of_le_mul hK hM (fun k => ?_) fun k => ?_)
  · rw [ENNReal.dyadicWeight_add, mul_assoc, mul_left_comm M]
    exact mul_le_mul' le_rfl (hKM f hf k).2
  · rw [ENNReal.dyadicWeight_add, mul_assoc, mul_left_comm K]
    exact mul_le_mul' le_rfl (hKM f hf k).1

/-- **Besov spaces on the interval through multiwavelet coefficients**: for `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `r ≥ 1` and `0 < s < 1/p`, the Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), [0, 1])_p)_k‖_{ℓ_q}` is finite iff
`‖P_0 f‖_p + ‖(2^(k(s + 1/2 - 1/p)) ‖(⟨f, ψ_{k,m,i}⟩)_{m,i}‖_{ℓ_p})_k‖_{ℓ_q}` is. -/
theorem lqNorm_modulus_lt_top_iff_coeff (hp : p ≠ ∞) (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * intervalLpModulus p r f k) < ∞ ↔
      ‖ppProj p hp r 0 f‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k * ENNReal.lqNorm p
          (fun mi : Fin (2 ^ k) × Fin r => ‖coeff r f k mi.1 mi.2‖ₑ)) < ∞ :=
  (memApprox_ppScheme_iff hr hp hq hs.le hsp f).symm.trans
    (memApprox_ppScheme_iff_coeff hp hr hs hq f)

/-- **Besov spaces on the circle through multiwavelet coefficients**: for `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `r ≥ 1` and `0 < s < 1/p`, the periodic Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r^per(f, 2^(-k))_p)_k‖_{ℓ_q}` is finite iff
`‖P_0 f‖_p + ‖(2^(k(s + 1/2 - 1/p)) ‖(⟨f, ψ_{k,m,i}⟩)_{m,i}‖_{ℓ_p})_k‖_{ℓ_q}` is. -/
theorem lqNorm_perModulus_lt_top_iff_coeff (hp : p ≠ ∞) (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s)
    (hsp : s < 1 / p.toReal) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p unitVol) :
    ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpPerModulus p r f k) < ∞ ↔
      ‖ppProj p hp r 0 f‖ₑ + ENNReal.lqNorm q (fun k =>
        dyadicWeight (s + (1 / 2 - 1 / p.toReal)) k * ENNReal.lqNorm p
          (fun mi : Fin (2 ^ k) × Fin r => ‖coeff r f k mi.1 mi.2‖ₑ)) < ∞ :=
  (memApprox_ppScheme_iff_per hr hp hq hs.le hsp f).symm.trans
    (memApprox_ppScheme_iff_coeff hp hr hs hq f)

end Alpert
