/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Rd.BesselPotentials.BesselPotentialDistributions

/-!
# Fourier multipliers on Bessel potential spaces

For `1 < p < ∞`, a symbol `m` of order `σ` (`Rd.HasSymbolGrowth σ m`) maps Mathlib's Bessel
potential space `H^{s,p}` into `H^{s-σ,p}`, for every real `s`
(`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_hasSymbolGrowth`): in dimension
`n ≥ 1` by `H^{s,p} = F^s_{p,2}` (`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`) and the
multiplier theorem on `F^s_{p,2}`, in dimension `0` since every symbol is constant there and
`J_s` is the identity (`Rd.besselPotential_of_subsingleton`).

* **Mapping properties**: `H^{s,p} ⊆ H^{s',p}` for `s' ≤ s`
  (`TemperedDistribution.MemSobolev.mono_of_one_lt`), so `L_p ⊆ H^{s,p}` for `s ≤ 0`
  (`Rd.memSobolev_bessel_of_nonpos`); derivatives map `H^{s,p}` into `H^{s-1,p}`
  (`TemperedDistribution.MemSobolev.lineDerivOp_of_one_lt`) and the Laplacian into `H^{s-2,p}`
  (`TemperedDistribution.MemSobolev.laplacian_of_one_lt`).
* **The derivative characterisation**: `J_2 = 1 - (2π)^{-2} Δ`
  (`TemperedDistribution.besselPotential_two_eq_sub_laplacian`), and `f ∈ H^{s+1,p}` iff
  `f ∈ H^{s,p}` and `∂_v f ∈ H^{s,p}` for every direction `v`
  (`TemperedDistribution.memSobolev_add_one_iff`).
* **The lifting property for every `q`**: for `g, J_σ g ∈ L_p` and `1 < q ≤ ∞`,
  `‖J_σ g‖_{F^{s-σ}_{p,q}}` and `‖g‖_{F^s_{p,q}}` are equivalent
  (`Rd.exists_triebelLizorkinNorm_besselPotential_le`,
  `Rd.exists_triebelLizorkinNorm_le_besselPotential`; Triebel 1983, Theorem 2.3.8).

The statements of `MemSobolev.mono_of_one_lt`, `MemSobolev.lineDerivOp_of_one_lt`,
`besselPotential_two_eq_sub_laplacian`, `MemSobolev.sum`, `MemSobolev.smul_of_tower`,
`memSobolev_add_one_of_lineDerivOp`, `memSobolev_add_one_iff` and
`memSobolev_natCast_add_one_iff`, and the proofs of the last six, are mirrored from TauCeti
(`Analysis/Distribution/Sobolev.lean`, commit `b61a90d`, Apache-2.0), where Mihlin's theorem
supplies the multipliers of order `0`; here the multiplier theorem on `F^s_{p,2}` supplies all
orders at once, for complex-valued distributions.
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal SchwartzMap Real Laplacian LineDeriv
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The Bessel potential in dimension `0`**: on a space with one point, `⟨ξ⟩^s = 1`, so `J_s`
is the identity (Mathlib's `TemperedDistribution.fourierMultiplierCLM_const`). -/
theorem besselPotential_of_subsingleton [Subsingleton V] (s : ℝ) (u : 𝓢'(V, ℂ)) :
    besselPotential V ℂ s u = u := by
  have h : (fun x : V => ((((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) : ℂ)) = fun _ => 1 := by
    funext x
    rw [Subsingleton.elim x 0, norm_zero]
    simp
  rw [TemperedDistribution.besselPotential, h, TemperedDistribution.fourierMultiplierCLM_const,
    one_smul, ContinuousLinearMap.id_apply]

/-- **Fourier multipliers on `H^{s,p}` in dimension `0`**: on a space with one point every
function `m` is constant, `m(D) u = m(0) u`, and `H^{s,p} = H^{t,p}` for all `s`, `t`
(`Rd.besselPotential_of_subsingleton`). -/
theorem memSobolev_fourierMultiplierCLM_of_subsingleton [Subsingleton V] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {s t : ℝ} (m : V → ℂ) {u : 𝓢'(V, ℂ)}
    (hu : TemperedDistribution.MemSobolev s p u) :
    TemperedDistribution.MemSobolev t p (TemperedDistribution.fourierMultiplierCLM ℂ m u) := by
  have hm : m = fun _ => m 0 := funext fun x => by rw [Subsingleton.elim x 0]
  obtain ⟨f, hf⟩ := hu
  rw [besselPotential_of_subsingleton] at hf
  refine ⟨m 0 • f, ?_⟩
  rw [besselPotential_of_subsingleton, hm, TemperedDistribution.fourierMultiplierCLM_const,
    smul_apply, ContinuousLinearMap.id_apply, hf,
    ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_smul]

end Rd

namespace TemperedDistribution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Fourier multipliers on Bessel potential spaces**: for `1 < p < ∞`, a symbol `m` of order
`σ` and every real `s`, `m(D)` maps Mathlib's Bessel potential space `H^{s,p}(V)` into
`H^{s-σ,p}(V)`. In dimension `n ≥ 1`, `H^{s,p} = F^s_{p,2}`
(`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`) and `m(D)` maps `F^s_{p,2}` into
`F^{s-σ}_{p,2}` (`Rd.MemTriebelLizorkinDistr.fourierMultiplierCLM`); dimension `0` is
`Rd.memSobolev_fourierMultiplierCLM_of_subsingleton`. -/
theorem MemSobolev.fourierMultiplierCLM_of_hasSymbolGrowth (hp1 : 1 < p) (hp : p ≠ ∞)
    {σ s : ℝ} {m : V → ℂ} (hm : Rd.HasSymbolGrowth σ m) {u : 𝓢'(V, ℂ)}
    (hu : MemSobolev s p u) : MemSobolev (s - σ) p (fourierMultiplierCLM ℂ m u) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Rd.memSobolev_fourierMultiplierCLM_of_subsingleton m hu
  rw [Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr hp1 hp] at hu ⊢
  exact hu.fourierMultiplierCLM hp1 hp ENNReal.one_lt_two hm

/-- **`H^{s,p}` decreases in `s`**: for `1 < p < ∞`, `H^{s,p} ⊆ H^{s',p}` whenever `s' ≤ s`. Here
`f ∈ H^{s',p}` iff `J_{s'-s} f ∈ H^{s,p}` (Mathlib's
`TemperedDistribution.memSobolev_besselPotential_iff`), and `⟨ξ⟩^{s'-s}` is a symbol of order
`s' - s ≤ 0` (`Rd.hasSymbolGrowth_besselWeight`), hence of order `0`. Statement mirrored from
TauCeti; for `p = 2` this is Mathlib's `TemperedDistribution.MemSobolev.mono`. -/
theorem MemSobolev.mono_of_one_lt (hp1 : 1 < p) (hp : p ≠ ∞) {s s' : ℝ} (h : s' ≤ s)
    {f : 𝓢'(V, ℂ)} (hf : MemSobolev s p f) : MemSobolev s' p f := by
  rw [← sub_add_cancel s' s, ← memSobolev_besselPotential_iff]
  have hm := ((Rd.hasSymbolGrowth_besselWeight (V := V) (s' - s)).mono
    (by linarith : s' - s ≤ 0))
  have h0 := hf.fourierMultiplierCLM_of_hasSymbolGrowth hp1 hp hm
  rwa [sub_zero] at h0

/-- **Derivatives on Bessel potential spaces**: for `1 < p < ∞` and every direction `v`, the
derivative `∂_v` maps `H^{s,p}` into `H^{s-1,p}`, since `∂_v = 2πi ⟪ξ, v⟫(D)` (Mathlib's
`TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`) with the symbol `⟪ξ, v⟫` of order `1`
(`Rd.hasSymbolGrowth_inner`). Statement mirrored from TauCeti; for `p = 2` this is Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp`. -/
theorem MemSobolev.lineDerivOp_of_one_lt (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ} {f : 𝓢'(V, ℂ)}
    (hf : MemSobolev s p f) {v : V} : MemSobolev (s - 1) p (∂_{v} f) := by
  rw [lineDeriv_eq_fourierMultiplierCLM]
  exact (hf.fourierMultiplierCLM_of_hasSymbolGrowth hp1 hp (Rd.hasSymbolGrowth_inner v)).smul _

/-- `H^{s,p}` is closed under multiplication by scalars acting through `ℂ`, such as real
numbers. Mirrored from TauCeti. -/
theorem MemSobolev.smul_of_tower {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {R : Type*} [SMul R ℂ] [SMul R 𝓢'(V, F)] [IsScalarTower R ℂ 𝓢'(V, F)]
    {s : ℝ} (c : R) {f : 𝓢'(V, F)} (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  rw [← smul_one_smul ℂ c f]
  exact hf.smul _

/-- **The Laplacian on Bessel potential spaces**: for `1 < p < ∞`, the Laplacian maps `H^{s,p}`
into `H^{s-2,p}`, since `Δ = -(2π)^2 ‖ξ‖^2(D)` (Mathlib's
`TemperedDistribution.laplacian_eq_fourierMultiplierCLM`) with the symbol `‖ξ‖^2` of order `2`
(`Rd.hasSymbolGrowth_norm_sq`). For `p = 2` this is Mathlib's
`TemperedDistribution.MemSobolev.laplacian`. -/
theorem MemSobolev.laplacian_of_one_lt (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ} {f : 𝓢'(V, ℂ)}
    (hf : MemSobolev s p f) : MemSobolev (s - 2) p (Δ f) := by
  rw [laplacian_eq_fourierMultiplierCLM]
  exact (hf.fourierMultiplierCLM_of_hasSymbolGrowth hp1 hp
    Rd.hasSymbolGrowth_norm_sq).smul_of_tower _

/-- **`J_2 = 1 - (2π)^{-2} Δ`**: the Bessel potential of order `2` is the identity minus
`(2π)^{-2}` times the Laplacian; the factor comes from Mathlib's normalisation of the Fourier
transform. Mirrored from TauCeti. -/
theorem besselPotential_two_eq_sub_laplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : 𝓢'(V, F)) : besselPotential V F 2 f = f - ((2 * π) ^ 2)⁻¹ • Δ f := by
  have hsymb : (fun x : V ↦ (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun _ ↦ (1 : ℂ)) + fun x ↦ ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    ext x
    norm_num
  have hsplit : besselPotential V F 2 f =
      f + fourierMultiplierCLM F (fun x : V ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)) f := by
    rw [besselPotential, hsymb, fourierMultiplierCLM_apply,
      smulLeftCLM_add (by fun_prop) (by fun_prop)]
    simp [fourierMultiplierCLM_apply]
  have hΔ : ((2 * π) ^ 2)⁻¹ • Δ f =
      -fourierMultiplierCLM F (fun x : V ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)) f := by
    rw [laplacian_eq_fourierMultiplierCLM, smul_smul, mul_neg,
      inv_mul_cancel₀ (by positivity), neg_one_smul]
  rw [hsplit, hΔ, sub_neg_eq_add]

/-- **Finite sums in `H^{s,p}`**: a finite sum of tempered distributions in `H^{s,p}` lies in
`H^{s,p}`. Mirrored from TauCeti. -/
theorem MemSobolev.sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} {t : Finset ι} {s : ℝ} {g : ι → 𝓢'(V, F)} (hg : ∀ i ∈ t, MemSobolev s p (g i)) :
    MemSobolev s p (∑ i ∈ t, g i) :=
  Finset.sum_induction g (MemSobolev s p) (fun _ _ => MemSobolev.add)
    (memSobolev_fun_zero V F s p) hg

/-- **`H^{s+1,p}` from first derivatives along a basis**: for `1 < p < ∞`, if `f ∈ H^{s,p}` and
the derivatives of `f` along an orthonormal basis lie in `H^{s,p}`, then `f ∈ H^{s+1,p}`. Here
`J_1 f = J_{-1}(J_2 f) = J_{-1} f - (2π)^{-2} ∑_i J_{-1} ∂_{b_i} ∂_{b_i} f`
(`TemperedDistribution.besselPotential_two_eq_sub_laplacian`, Mathlib's
`TemperedDistribution.laplacian_eq_sum`), and `J_{-1}` maps `f` and each `∂_{b_i} ∂_{b_i} f` into
`H^{s,p}`. Mirrored from TauCeti. -/
theorem memSobolev_add_one_of_lineDerivOp (hp1 : 1 < p) (hp : p ≠ ∞) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {s : ℝ} {f : 𝓢'(V, ℂ)} (hf : MemSobolev s p f)
    (hdf : ∀ i, MemSobolev s p (∂_{b i} f)) : MemSobolev (s + 1) p f := by
  have hJ : besselPotential V ℂ 1 f = besselPotential V ℂ (-1) f -
      ((2 * π) ^ 2)⁻¹ • ∑ i, besselPotential V ℂ (-1) (∂_{b i} (∂_{b i} f)) := by
    calc besselPotential V ℂ 1 f
        = besselPotential V ℂ (-1) (besselPotential V ℂ 2 f) := by
          rw [besselPotential_besselPotential_apply]
          norm_num
      _ = _ := by
          rw [besselPotential_two_eq_sub_laplacian, laplacian_eq_sum b, map_sub,
            ContinuousLinearMap.map_smul_of_tower, map_sum]
  rw [add_comm, ← memSobolev_besselPotential_iff, hJ, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  refine MemSobolev.sub ?_ (MemSobolev.smul _ (MemSobolev.sum fun i _ => ?_))
  · rw [memSobolev_besselPotential_iff]
    exact hf.mono_of_one_lt hp1 hp (by linarith)
  · rw [memSobolev_besselPotential_iff, neg_add_eq_sub]
    exact (hdf i).lineDerivOp_of_one_lt hp1 hp

/-- **The derivative characterisation of `H^{s+1,p}`**: for `1 < p < ∞` and every real `s`, a
tempered distribution lies in `H^{s+1,p}` iff it and all its first directional derivatives lie in
`H^{s,p}` (`TemperedDistribution.MemSobolev.mono_of_one_lt`,
`TemperedDistribution.MemSobolev.lineDerivOp_of_one_lt`,
`TemperedDistribution.memSobolev_add_one_of_lineDerivOp`). Mirrored from TauCeti. -/
theorem memSobolev_add_one_iff (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ} {f : 𝓢'(V, ℂ)} :
    MemSobolev (s + 1) p f ↔ MemSobolev s p f ∧ ∀ v : V, MemSobolev s p (∂_{v} f) := by
  refine ⟨fun hf => ⟨hf.mono_of_one_lt hp1 hp (by linarith), fun v => by
      simpa using hf.lineDerivOp_of_one_lt hp1 hp (v := v)⟩,
    fun h => memSobolev_add_one_of_lineDerivOp hp1 hp (stdOrthonormalBasis ℝ V) h.1
      fun i => h.2 _⟩

/-- **The derivative characterisation at natural orders**: for `1 < p < ∞` and `k ∈ ℕ`, a
tempered distribution lies in `H^{k+1,p}` iff it lies in `H^{0,p} = L_p` and all its first
directional derivatives lie in `H^{k,p}` (induction on `k` with
`TemperedDistribution.memSobolev_add_one_iff`). Mirrored from TauCeti. -/
theorem memSobolev_natCast_add_one_iff (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ} {f : 𝓢'(V, ℂ)} :
    MemSobolev ((k : ℝ) + 1) p f ↔ MemSobolev 0 p f ∧ ∀ v : V, MemSobolev k p (∂_{v} f) := by
  induction k generalizing f with
  | zero => simpa using memSobolev_add_one_iff hp1 hp (s := 0) (f := f)
  | succ k ih =>
      rw [Nat.cast_succ, memSobolev_add_one_iff hp1 hp, ih]
      exact ⟨fun h => ⟨h.1.1, h.2⟩,
        fun h => ⟨⟨h.1, fun v => (h.2 v).mono_of_one_lt hp1 hp (by linarith)⟩, h.2⟩⟩

end TemperedDistribution

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`L_p ⊆ H^{s,p}` for `s ≤ 0`**: for `1 < p < ∞`, real `s ≤ 0` and `f ∈ L_p(V)`, the tempered
distribution of `f` lies in Mathlib's `H^{s,p}(V)`, since it lies in `H^{0,p}` (Mathlib's
`TemperedDistribution.memSobolev_zero_iff`) and `H^{0,p} ⊆ H^{s,p}`
(`TemperedDistribution.MemSobolev.mono_of_one_lt`). -/
theorem memSobolev_bessel_of_nonpos (hp1 : 1 < p) (hp : p ≠ ∞) {s : ℝ} (hs : s ≤ 0)
    (f : Lp ℂ p (volume : Measure V)) : TemperedDistribution.MemSobolev s p (f : 𝓢'(V, ℂ)) :=
  (TemperedDistribution.memSobolev_zero_iff.2 ⟨f, rfl⟩).mono_of_one_lt hp1 hp hs

/-- **The lifting property for every `q`, first half**: for `1 < p < ∞`, `1 < q ≤ ∞` and all
reals `σ`, `s` there is a finite constant `C` such that
`‖h‖_{F^{s-σ}_{p,q}} ≤ C ‖g‖_{F^s_{p,q}}` for all `g, h ∈ L_p(V)` with `J_σ g = h`; the constant is
existential. `J_σ` is the Fourier multiplier with the symbol `⟨ξ⟩^σ` of order `σ`
(`Rd.hasSymbolGrowth_besselWeight`, `Rd.exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq`). -/
theorem exists_triebelLizorkinNorm_besselPotential_le (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) (σ s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g h : Lp ℂ p (volume : Measure V),
      besselPotential V ℂ σ (g : 𝓢'(V, ℂ)) = h →
        triebelLizorkinNorm (s - σ) q h ≤ C * triebelLizorkinNorm s q g := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq (V := V) hp1 hp hq1
    (hasSymbolGrowth_besselWeight σ) s
  exact ⟨C, hC, fun g h hgh => hCu g h hgh.symm⟩

/-- **The lifting property for every `q`, second half**: for `1 < p < ∞`, `1 < q ≤ ∞` and all
reals `σ`, `s` there is a finite constant `C` such that
`‖g‖_{F^s_{p,q}} ≤ C ‖h‖_{F^{s-σ}_{p,q}}` for all `g, h ∈ L_p(V)` with `J_σ g = h`; the constant is
existential. Here `g = J_{-σ} h` (Mathlib's
`TemperedDistribution.besselPotential_neg_apply_eq_iff`) with the symbol `⟨ξ⟩^{-σ}` of order
`-σ`. With `Rd.exists_triebelLizorkinNorm_besselPotential_le` this is Triebel's lifting property
(Triebel 1983, Theorem 2.3.8) for `1 < q ≤ ∞`. -/
theorem exists_triebelLizorkinNorm_le_besselPotential (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) (σ s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g h : Lp ℂ p (volume : Measure V),
      besselPotential V ℂ σ (g : 𝓢'(V, ℂ)) = h →
        triebelLizorkinNorm s q g ≤ C * triebelLizorkinNorm (s - σ) q h := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNorm_le_of_fourierMultiplier_eq (V := V) hp1 hp hq1
    (hasSymbolGrowth_besselWeight (-σ)) (s - σ)
  refine ⟨C, hC, fun g h hgh => ?_⟩
  have h' := hCu h g ((TemperedDistribution.besselPotential_neg_apply_eq_iff σ _ _).2 hgh).symm
  rwa [sub_neg_eq_add, sub_add_cancel] at h'

end Rd
