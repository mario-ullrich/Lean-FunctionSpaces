/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Torus.SobolevTriebelLizorkin
public import FunctionSpaces.Torus.Embeddings

/-!
# Sobolev embeddings on the torus

Let `d ≥ 1` and `1 < p < ∞`. Through `W^m_p(𝕋^d) ⊆ B^m_{p,max(p,2)}(𝕋^d)` for `m ≥ 1`
(`Torus.memBesov_of_memPeriodicSobolev`) the Besov embeddings of the torus
(`FunctionSpaces.Torus.Embeddings`) give, with `α = d (1/p - 1/r)`:

* **into `L_r`** (`Torus.memPeriodicSobolev_exists_inclusion_eq`): for `p ≤ r ≤ ∞` and `m > α`,
  every `f ∈ W^m_p(𝕋^d)` lies in `L_r(𝕋^d)` and in `B^{m - α}_{r,max(p,2)}(𝕋^d)`;
* **into continuous functions** (`Torus.memPeriodicSobolev_exists_continuous`): for `m > d/p`, every
  `f ∈ W^m_p(𝕋^d)` has a continuous representative;
* **between Sobolev spaces** (`Torus.memPeriodicSobolev_of_memPeriodicSobolev_of_lt`): for
  `p ≤ r < ∞` and `k < m - α`, `W^m_p(𝕋^d) ⊆ W^k_r(𝕋^d)`, through
  `B^{m - α}_{r,max(p,2)} ⊆ B^k_{r,min(r,2)}` (`FunctionScheme.MemBesov.mono`) and
  `B^k_{r,min(r,2)} ⊆ W^k_r` (`Torus.memPeriodicSobolev_of_memBesov`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal TorusHaar

namespace Torus

variable {d : Type*} [Fintype d] {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- **The Sobolev embedding into `L_r` on the torus**: for `d ≥ 1`, `1 < p < ∞`, `p ≤ r ≤ ∞` and
`m > d (1/p - 1/r)`, every `f ∈ W^m_p(𝕋^d)` is the class in `L_p` of some `g ∈ L_r(𝕋^d)`, and
`g` lies in the Besov space `B^{m - d(1/p - 1/r)}_{r,max(p,2)}(𝕋^d)`
(`Torus.memBesov_of_memPeriodicSobolev` and `Torus.memBesov_exists_inclusion_eq`). The order
satisfies `m ≥ 1` since `d (1/p - 1/r) ≥ 0`. -/
theorem memPeriodicSobolev_exists_inclusion_eq [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) (hpr : p ≤ r)
    {m : ℕ} (hm : (Fintype.card d : ℝ) * (p.toReal⁻¹ - r.toReal⁻¹) < m)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemPeriodicSobolev m f) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume hpr g = f ∧
        (trigScheme d).MemBesov r
          ((m : ℝ) - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) (max p 2) g := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  obtain ⟨g, hg, hmem⟩ := memBesov_exists_inclusion_eq hp0 hpr hm
    (zero_lt_two.trans_le (le_max_right p 2)).ne'
    (memBesov_of_memPeriodicSobolev hp1 hp
      (one_le_of_nikolskiiExponent_lt (Nat.cast_nonneg _) hp0 hpr hm) hf)
  exact ⟨g, (Lp.inclusionOfExponentLe_apply (𝕜 := ℝ) hpr g).trans hg, hmem⟩

/-- **The Sobolev embedding into continuous functions on the torus**: for `d ≥ 1`, `1 < p < ∞`
and `m > d/p`, every `f ∈ W^m_p(𝕋^d)` has a continuous representative
(`Torus.memBesov_of_memPeriodicSobolev` and `Torus.memBesov_exists_continuous`). -/
theorem memPeriodicSobolev_exists_continuous [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (hm : (Fintype.card d : ℝ) * p.toReal⁻¹ < m)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemPeriodicSobolev m f) :
    ∃ g : C(UnitAddTorus d, ℂ),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume le_top (ContinuousMap.toLp (E := ℂ) ∞ volume ℝ g) =
        f := by
  obtain ⟨g, hg⟩ := memBesov_exists_continuous (zero_lt_one.trans hp1).ne' hm
    (zero_lt_two.trans_le (le_max_right p 2)).ne'
    (memBesov_of_memPeriodicSobolev hp1 hp (Nat.cast_pos.1 (lt_of_le_of_lt (by positivity) hm)) hf)
  exact ⟨g, (Lp.inclusionOfExponentLe_apply (𝕜 := ℝ) le_top _).trans hg⟩

/-- **The embeddings between Sobolev spaces on the torus**: for `d ≥ 1`, `1 < p ≤ r < ∞` and
orders `k < m - d (1/p - 1/r)`, every `f ∈ W^m_p(𝕋^d)` is the class in `L_p` of some
`g ∈ W^k_r(𝕋^d)`. The class `g ∈ B^{m - d(1/p - 1/r)}_{r,max(p,2)}(𝕋^d)` of
`Torus.memPeriodicSobolev_exists_inclusion_eq` lies in `B^k_{r,min(r,2)}(𝕋^d)` since `k` is smaller
(`FunctionScheme.MemBesov.mono`), hence in `W^k_r(𝕋^d)`
(`Torus.memPeriodicSobolev_of_memBesov`). -/
theorem memPeriodicSobolev_of_memPeriodicSobolev_of_lt [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hpr : p ≤ r) (hr : r ≠ ∞) {k m : ℕ}
    (hkm : (k : ℝ) < m - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹))
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemPeriodicSobolev m f) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume hpr g = f ∧ MemPeriodicSobolev k g := by
  have hm : (Fintype.card d : ℝ) * (p.toReal⁻¹ - r.toReal⁻¹) < m := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨g, hgf, hg⟩ := memPeriodicSobolev_exists_inclusion_eq hp1 hp hpr hm hf
  exact ⟨g, hgf, memPeriodicSobolev_of_memBesov (hp1.trans_le hpr) hr
    (hg.mono (zero_lt_two.trans_le (le_max_right p 2)).ne' (Nat.cast_nonneg k) (Or.inl hkm))⟩

end Torus
