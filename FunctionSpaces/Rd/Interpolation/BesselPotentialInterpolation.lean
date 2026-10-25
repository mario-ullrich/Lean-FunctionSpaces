/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.BesselPotentials.BesselPotentialLifting
public import FunctionSpaces.Rd.Interpolation.TriebelLizorkinInterpolation

/-!
# Bessel potential spaces on `V` and real interpolation

The **Bessel potential norm** `‖J_s f‖_p` of `f ∈ L_p(V)` (`Rd.besselPotentialNorm`) is finite
exactly on Mathlib's Bessel potential space `H^{s,p}(V)` (`Rd.besselPotentialNorm_lt_top_iff`),
where it is the norm of the bundled space (`Rd.besselPotentialNorm_eq_enorm`).
In dimension `n ≥ 1` and for `1 < p < ∞` it is equivalent to the quasi-norm of `F^s_{p,2}`, with
existential constants (`Rd.exists_triebelLizorkinNorm_le_besselPotentialNorm`,
`Rd.exists_besselPotentialNorm_le_triebelLizorkinNorm`), so the interpolation theorem for
Triebel–Lizorkin spaces gives, for `0 < η < 1`, `1 ≤ q ≤ ∞`, `0 < s₀ < s₁` and
`s = (1-η)s₀ + ηs₁`,

`(H^{s₀,p}, H^{s₁,p})_{η,q} = B^s_{p,q}` and `(L_p, H^{s₁,p})_{η,q} = B^{ηs₁}_{p,q}`

in the Bessel potential norms (Bergh–Löfström, Theorem 6.4.5(4);
`Rd.memKMethod_besselPotentialCouple_iff`, `Rd.memKMethod_lpBesselPotentialCouple_iff`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap BesselPotentialSpace
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ η : ℝ}
  {q₀ q₁ q : ℝ≥0∞}

/-- The **Bessel potential norm** `‖J_s f‖_p` of `f ∈ L_p(V)`: the infimum of `‖h‖_p` over the
`h ∈ L_p(V)` with `J_s f = h` as tempered distributions, where `J_s` is Mathlib's Bessel
potential.  It is `‖J_s f‖_p` when `J_s f ∈ L_p(V)` (`Rd.besselPotentialNorm_eq`) and `∞`
otherwise.  On Mathlib's Bessel potential space `H^{s,p}(V)` it is the norm of the bundled space
(`Rd.besselPotentialNorm_eq_enorm`, `Rd.besselPotentialNorm_eq_enorm_toBesselPotentialSpace`). -/
noncomputable def besselPotentialNorm (s : ℝ) (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  ⨅ (h : Lp ℂ p (volume : Measure V)) (_ : besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = h), ‖h‖ₑ

/-- The Bessel potential norm is at most `‖h‖_p` whenever `J_s f = h`. -/
theorem besselPotentialNorm_le {s : ℝ} {f h : Lp ℂ p (volume : Measure V)}
    (hh : besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = h) : besselPotentialNorm s f ≤ ‖h‖ₑ :=
  iInf₂_le h hh

/-- **The Bessel potential norm is `‖J_s f‖_p`**: if `J_s f = h ∈ L_p(V)`, the Bessel potential
norm of `f` is `‖h‖_p`, since `h` is determined by its tempered distribution
(`Rd.eq_of_toTemperedDistribution_eq`). -/
theorem besselPotentialNorm_eq {s : ℝ} {f h : Lp ℂ p (volume : Measure V)}
    (hh : besselPotential V ℂ s (f : 𝓢'(V, ℂ)) = h) : besselPotentialNorm s f = ‖h‖ₑ :=
  le_antisymm (besselPotentialNorm_le hh) (le_iInf₂ fun _ hh' => by
    rw [eq_of_toTemperedDistribution_eq (hh.symm.trans hh')])

/-- **The Bessel potential norm is the norm of Mathlib's `H^{s,p}`**: if `f ∈ L_p(V)` is the
tempered distribution of an element `F` of Mathlib's bundled Bessel potential space
`H^{s,p}(V)`, then the Bessel potential norm of `f` is the norm of `F`, the `L_p` norm of its
function `J_s F` (`BesselPotentialSpace.enorm_toLp_eq`). -/
theorem besselPotentialNorm_eq_enorm {s : ℝ} {f : Lp ℂ p (volume : Measure V)}
    (F : H^{s, p}(V, ℂ)) (hF : (f : 𝓢'(V, ℂ)) = F.toDistr) : besselPotentialNorm s f = ‖F‖ₑ :=
  (besselPotentialNorm_eq (by rw [hF]; exact F.bessel_toDistr_eq_toLp)).trans F.enorm_toLp_eq

/-- **The Bessel potential norm of `f ∈ H^{s,p}`**: for `f ∈ L_p(V)` in Mathlib's Bessel
potential space `H^{s,p}(V)`, the Bessel potential norm of `f` is the norm of `f` as an element
of the bundled space. -/
theorem besselPotentialNorm_eq_enorm_toBesselPotentialSpace {s : ℝ}
    {f : Lp ℂ p (volume : Measure V)} (hf : TemperedDistribution.MemSobolev s p (f : 𝓢'(V, ℂ))) :
    besselPotentialNorm s f = ‖hf.toBesselPotentialSpace‖ₑ :=
  besselPotentialNorm_eq_enorm _ hf.toBesselPotentialSpace_toDistr.symm

/-- **The Bessel potential norm is finite exactly on `H^{s,p}`**: for `f ∈ L_p(V)`, the Bessel
potential norm of `f` is finite iff `f` lies in Mathlib's Bessel potential space `H^{s,p}(V)`,
`J_s f ∈ L_p(V)`. -/
theorem besselPotentialNorm_lt_top_iff {s : ℝ} {f : Lp ℂ p (volume : Measure V)} :
    besselPotentialNorm s f < ∞ ↔ TemperedDistribution.MemSobolev s p (f : 𝓢'(V, ℂ)) := by
  refine ⟨fun hf => ?_, fun ⟨h, hh⟩ => (besselPotentialNorm_le hh).trans_lt enorm_lt_top⟩
  obtain ⟨h, hh⟩ := iInf_lt_iff.1 hf
  exact ⟨h, (iInf_lt_iff.1 hh).choose⟩

/-- **`H^{s,p} ⊆ F^s_{p,2}` in the Bessel potential norm**: in dimension `n ≥ 1`, for
`1 < p < ∞` and real `s`, there is a finite `C` with `‖f‖_{F^s_{p,2}} ≤ C ‖J_s f‖_p` for every
`f ∈ L_p(V)` (`Rd.exists_triebelLizorkinNorm_le_of_besselPotential_eq`); the constant is
existential. -/
theorem exists_triebelLizorkinNorm_le_besselPotentialNorm [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      triebelLizorkinNorm s 2 f ≤ C * besselPotentialNorm s f := by
  obtain ⟨C, hC, hC₂⟩ := exists_triebelLizorkinNorm_le_of_besselPotential_eq (V := V) hp1 hp s
  have hC' : max C 1 ≠ ∞ := max_ne_top hC ENNReal.one_ne_top
  have h0 : max C 1 ≠ 0 := (zero_lt_one.trans_le (le_max_right _ _)).ne'
  refine ⟨max C 1, hC', fun f => ?_⟩
  rw [besselPotentialNorm, ENNReal.mul_iInf_of_ne h0 hC']
  refine le_iInf fun h => ?_
  rw [ENNReal.mul_iInf_of_ne h0 hC']
  exact le_iInf fun hh => (hC₂ f h hh).trans (mul_le_mul_left (le_max_left _ _) _)

/-- **`F^s_{p,2} ⊆ H^{s,p}` in the Bessel potential norm**: in dimension `n ≥ 1`, for
`1 < p < ∞` and real `s`, there is a finite `C` with `‖J_s f‖_p ≤ C ‖f‖_{F^s_{p,2}}` for every
`f ∈ L_p(V)` (`Rd.exists_besselPotential_eq_of_memTriebelLizorkin`); the constant is
existential. -/
theorem exists_besselPotentialNorm_le_triebelLizorkinNorm [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      besselPotentialNorm s f ≤ C * triebelLizorkinNorm s 2 f := by
  obtain ⟨C, hC, hC₁⟩ := exists_besselPotential_eq_of_memTriebelLizorkin (V := V) hp1 hp s
  refine ⟨max C 1, max_ne_top hC ENNReal.one_ne_top, fun f => ?_⟩
  by_cases hf : MemTriebelLizorkin s 2 f
  · obtain ⟨h, hh, hnorm⟩ := hC₁ f hf
    exact (besselPotentialNorm_le hh).trans (hnorm.trans (mul_le_mul_left (le_max_left _ _) _))
  · rw [MemTriebelLizorkin, not_lt, top_le_iff] at hf
    rw [hf, ENNReal.mul_top (zero_lt_one.trans_le (le_max_right _ _)).ne']
    exact le_top

/-- The **couple `(H^{s₀,p}, H^{s₁,p})`** on `L_p(V)`: the Bessel potential norms `‖J_{s₀} f‖_p`
and `‖J_{s₁} f‖_p`. -/
noncomputable def besselPotentialCouple (s₀ s₁ : ℝ) :
    InterpCouple (Lp ℂ p (volume : Measure V)) :=
  ⟨besselPotentialNorm s₀, besselPotentialNorm s₁⟩

/-- The first norm of `(H^{s₀,p}, H^{s₁,p})` is the Bessel potential norm of order `s₀`. -/
@[simp]
theorem besselPotentialCouple_norm0 (f : Lp ℂ p (volume : Measure V)) :
    (besselPotentialCouple s₀ s₁).norm0 f = besselPotentialNorm s₀ f := rfl

/-- The second norm of `(H^{s₀,p}, H^{s₁,p})` is the Bessel potential norm of order `s₁`. -/
@[simp]
theorem besselPotentialCouple_norm1 (f : Lp ℂ p (volume : Measure V)) :
    (besselPotentialCouple s₀ s₁).norm1 f = besselPotentialNorm s₁ f := rfl

/-- The **couple `(L_p, H^{s₁,p})`** on `L_p(V)`: the `L_p` norm and the Bessel potential norm
`‖J_{s₁} f‖_p`. -/
noncomputable def lpBesselPotentialCouple (s₁ : ℝ) : InterpCouple (Lp ℂ p (volume : Measure V)) :=
  ⟨fun f => ‖f‖ₑ, besselPotentialNorm s₁⟩

/-- The first norm of `(L_p, H^{s₁,p})` is the `L_p` norm. -/
@[simp]
theorem lpBesselPotentialCouple_norm0 (f : Lp ℂ p (volume : Measure V)) :
    (lpBesselPotentialCouple s₁).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of `(L_p, H^{s₁,p})` is the Bessel potential norm of order `s₁`. -/
@[simp]
theorem lpBesselPotentialCouple_norm1 (f : Lp ℂ p (volume : Measure V)) :
    (lpBesselPotentialCouple s₁).norm1 f = besselPotentialNorm s₁ f := rfl

/-- **Bessel potential spaces interpolate to Besov spaces** (Bergh–Löfström, Theorem 6.4.5(4)): in
dimension `n ≥ 1`, for `1 < p < ∞`, `0 < s₀ < s₁`, `0 < η < 1` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)`
lies in the real interpolation space `(H^{s₀,p}, H^{s₁,p})_{η,q}` of the Bessel potential norms
iff `f` lies in the Besov space `B^{(1-η)s₀+ηs₁}_{p,q}(V)`.  The Bessel potential norms are
equivalent to the quasi-norms of `F^{s_i}_{p,2}`
(`Rd.memKMethod_iff_memApprox_of_triebelLizorkin_equiv`). -/
theorem memKMethod_besselPotentialCouple_iff [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hη : 0 < η) (hη' : η < 1) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} :
    (besselPotentialCouple s₀ s₁).MemKMethod η q f ↔
      (bandScheme hp).MemApprox ((1 - η) * s₀ + η * s₁) q f := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_besselPotentialNorm_le_triebelLizorkinNorm (V := V) hp1 hp s₀
  obtain ⟨C₀', hC₀', h₀'⟩ := exists_triebelLizorkinNorm_le_besselPotentialNorm (V := V) hp1 hp s₀
  obtain ⟨C₁, hC₁, h₁⟩ := exists_besselPotentialNorm_le_triebelLizorkinNorm (V := V) hp1 hp s₁
  obtain ⟨C₁', hC₁', h₁'⟩ := exists_triebelLizorkinNorm_le_besselPotentialNorm (V := V) hp1 hp s₁
  exact memKMethod_iff_memApprox_of_triebelLizorkin_equiv hp hC₀ hC₀' hC₁ hC₁' hs₀ hs hη hη'
    one_le_two one_le_two hq h₀ h₀' h₁ h₁'

/-- **`L_p` and a Bessel potential space interpolate to Besov spaces**: in dimension `n ≥ 1`, for
`1 < p < ∞`, `s₁ > 0`, `0 < η < 1` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)` lies in the real interpolation
space `(L_p, H^{s₁,p})_{η,q}` of the `L_p` norm and the Bessel potential norm iff `f` lies in the
Besov space `B^{ηs₁}_{p,q}(V)`. -/
theorem memKMethod_lpBesselPotentialCouple_iff [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hs₁ : 0 < s₁) (hη : 0 < η) (hη' : η < 1) (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} :
    (lpBesselPotentialCouple s₁).MemKMethod η q f ↔ (bandScheme hp).MemApprox (η * s₁) q f := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_besselPotentialNorm_le_triebelLizorkinNorm (V := V) hp1 hp s₁
  obtain ⟨C₁', hC₁', h₁'⟩ := exists_triebelLizorkinNorm_le_besselPotentialNorm (V := V) hp1 hp s₁
  exact memKMethod_iff_memApprox_of_triebelLizorkin_equiv_left hp hC₁ hC₁' hs₁ hη hη' one_le_two hq
    h₁ h₁'

end Rd
