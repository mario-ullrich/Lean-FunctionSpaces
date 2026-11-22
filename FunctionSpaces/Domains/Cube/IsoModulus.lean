/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Cube.IsoDifferences
public import FunctionSpaces.Analysis.Differences.LinearEquivModuli
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The isotropic modulus of smoothness on the cube

The **isotropic modulus** on the cube `Q = [0, 1]^d` is the modulus on the set `Q` of
`Rd.modulusOn` (`Cube.isoModulus`),

`ω_r(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r f‖_{L_p({x ∈ Q : x + rh ∈ Q})}`   (`Cube.isoModulus_eq_iSup`),

with steps `h ∈ ℝ^d` of every direction and sign and the region `{x ∈ Q : x + rh ∈ Q}`
(`Cube.isoRegion`), which is the set of the points `x` with `x, x + h, …, x + rh ∈ Q`
(`Cube.isoRegion_inter_cubeSet`). It increases in `t`, is subadditive, is bounded by
`2^r ‖f‖_p`, and depends only on the class of `f` in `L_p(Q)`, as every modulus on a set.
Translations that stay in the cube keep `L_p` norms and null sets (`Cube.eLpNorm_comp_add_le`,
`Cube.ae_comp_add_of_ae`).

Steps along a coordinate are isotropic steps, so the moduli in the coordinates are bounded by
the isotropic modulus (`Cube.coordModulus_le_isoModulus`) and `ω_cube ≤ d ω_iso`
(`Cube.cubeModulus_le_isoModulus`). Jackson's inequalities with the coordinate moduli therefore
hold with the isotropic modulus as well. The converse comparison, for the approximants, is the
inverse inequality of `FunctionSpaces.Domains.Cube.IsoInverse`.

**The cube in the Euclidean space.** The closed unit cube `Q_E = [0, 1]^d` in the Euclidean space
`ℝ^d = EuclideanSpace ℝ (Fin d)` (`Cube.euclideanCube`) corresponds to `Q` under Mathlib's
coordinates `ofLp` and `toLp`, which preserve Lebesgue measure (`Cube.preimage_ofLp_cubeSet`,
`Cube.measurePreserving_toLp_cubeVol`). Restriction to the cube followed by the change of
coordinates maps `L_p(ℝ^d)` to `L_p(Q)` (`Cube.restrictEuclidean`), and extension by zero maps
back (`Cube.extendEuclidean`); the restriction of an extension is the identity
(`Cube.restrictEuclidean_extendEuclidean`), and the restriction sees only `1_{Q_E} F`
(`Cube.restrictEuclidean_eq_of_indicatorLp_eq`, `Cube.enorm_restrictEuclidean`). Since
`‖h‖_∞ ≤ ‖h‖_2 ≤ √d ‖h‖_∞ ≤ 2^d ‖h‖_∞` (`Cube.norm_euclideanEquiv_symm_le`), the modulus on
`Q_E` for the Euclidean norm (`Rd.modulusOn`) and the isotropic modulus compare with a shift of `d`
levels (`Cube.lpModulusOn_euclideanCube_le_lpIsoModulus`,
`Cube.lpIsoModulus_add_le_lpModulusOn`), so the intrinsic quasi-norm `N_{Q_E}(F)` of
`Rd.modNormOn` and the isotropic quasi-norm of `F|_Q` are equivalent for `s ≥ 0` and
`1 ≤ q ≤ ∞` (`Cube.modNormOn_euclideanCube_le_isoNorm`,
`Cube.isoNorm_restrictEuclidean_le_modNormOn`).
-/

@[expose] public section

open MeasureTheory Set
open Rd (higherDiff)
open scoped ENNReal

namespace Cube

open Interval

variable {d : ℕ}

/-! ### The cube as a set, and translations inside it -/

/-- The **cube** `Q = [0, 1]^d` as a subset of `ℝ^d`. -/
def cubeSet (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Icc (0 : ℝ) 1

/-- The cube is measurable. -/
theorem measurableSet_cubeSet (d : ℕ) : MeasurableSet (cubeSet d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The cube measure is Lebesgue measure restricted to the cube (Mathlib's
`Measure.restrict_pi_pi`). -/
theorem cubeVol_eq_restrict (d : ℕ) : cubeVol d = volume.restrict (cubeSet d) := by
  rw [cubeSet, volume_pi, Measure.restrict_pi_pi]

/-- The cube measure restricted to two sets that agree on the cube. -/
theorem cubeVol_restrict_congr {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ∩ cubeSet d = B ∩ cubeSet d) :
    (cubeVol d).restrict A = (cubeVol d).restrict B := by
  rw [cubeVol_eq_restrict, Measure.restrict_restrict hA, Measure.restrict_restrict hB, hAB]

/-- **Translation inside the cube**: if `x + v ∈ R' ∩ Q` for all `x ∈ R ∩ Q`, then
`‖G(· + v)‖_{L_p(R ∩ Q)} ≤ ‖G‖_{L_p(R' ∩ Q)}`, by the translation invariance of Lebesgue measure
(Mathlib's `measurePreserving_add_right`). -/
theorem eLpNorm_comp_add_le {G : (Fin d → ℝ) → ℂ} (hG : Measurable G) (p : ℝ≥0∞)
    {R R' : Set (Fin d → ℝ)} (hR : MeasurableSet R) (hR' : MeasurableSet R') (v : Fin d → ℝ)
    (hsub : ∀ x ∈ R ∩ cubeSet d, x + v ∈ R' ∩ cubeSet d) :
    eLpNorm (fun x => G (x + v)) p ((cubeVol d).restrict R) ≤
      eLpNorm G p ((cubeVol d).restrict R') := by
  have hC' : MeasurableSet (R' ∩ cubeSet d) := hR'.inter (measurableSet_cubeSet d)
  have hmp : MeasurePreserving (· + v) (volume.restrict ((· + v) ⁻¹' (R' ∩ cubeSet d)))
      (volume.restrict (R' ∩ cubeSet d)) :=
    (measurePreserving_add_right volume v).restrict_preimage hC'
  rw [cubeVol_eq_restrict, Measure.restrict_restrict hR, Measure.restrict_restrict hR']
  calc eLpNorm (fun x => G (x + v)) p (volume.restrict (R ∩ cubeSet d))
      ≤ eLpNorm (fun x => G (x + v)) p (volume.restrict ((· + v) ⁻¹' (R' ∩ cubeSet d))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (fun x hx => hsub x hx) le_rfl)
    _ = eLpNorm G p (volume.restrict (R' ∩ cubeSet d)) :=
        eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hmp

/-- **Translation inside the cube preserves almost everywhere equality**: if `f = g` almost
everywhere on the cube and `x + v ∈ Q` for `x ∈ R ∩ Q`, then `f(x + v) = g(x + v)` for almost
every `x ∈ R ∩ Q`. -/
theorem ae_comp_add_of_ae {f g : (Fin d → ℝ) → ℂ} (hfg : f =ᵐ[cubeVol d] g)
    {R : Set (Fin d → ℝ)} (hR : MeasurableSet R) (v : Fin d → ℝ)
    (hsub : ∀ x ∈ R ∩ cubeSet d, x + v ∈ cubeSet d) :
    ∀ᵐ x ∂(cubeVol d).restrict R, f (x + v) = g (x + v) := by
  rw [cubeVol_eq_restrict] at hfg ⊢
  rw [Measure.restrict_restrict hR]
  have hmp : MeasurePreserving (· + v) (volume.restrict ((· + v) ⁻¹' cubeSet d))
      (volume.restrict (cubeSet d)) :=
    (measurePreserving_add_right volume v).restrict_preimage (measurableSet_cubeSet d)
  have h1 : (fun x => f (x + v)) =ᵐ[volume.restrict ((· + v) ⁻¹' cubeSet d)]
      fun x => g (x + v) :=
    hmp.quasiMeasurePreserving.ae_eq_comp hfg
  exact ae_restrict_of_ae_restrict_of_subset (fun x hx => hsub x hx) h1

/-- **Convexity of intervals**: if `a, a + R b ∈ [0, 1]` and `0 ≤ n ≤ R`, then
`a + n b ∈ [0, 1]`. -/
theorem add_mul_mem_Icc {a b R n : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hR : a + R * b ∈ Icc (0 : ℝ) 1)
    (hn : 0 ≤ n) (hnR : n ≤ R) : a + n * b ∈ Icc (0 : ℝ) 1 := by
  rcases le_total 0 b with hb | hb
  · have h1 := mul_le_mul_of_nonneg_right hnR hb
    have h2 := mul_nonneg hn hb
    constructor <;> linarith [ha.1, ha.2, hR.1, hR.2]
  · have h1 := mul_le_mul_of_nonpos_right hnR hb
    have h2 := mul_nonpos_of_nonneg_of_nonpos hn hb
    constructor <;> linarith [ha.1, ha.2, hR.1, hR.2]

/-! ### The isotropic modulus -/

/-- The **region of the isotropic difference** of order `r` and step `h`: the points `x` with
`x + rh ∈ [0, 1]^d`. Together with `x ∈ Q` (the cube measure lives on `Q`) all points `x + kh`,
`k ≤ r`, lie in `Q`. -/
def isoRegion (r : ℕ) (h : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i + r * h i ∈ Icc (0 : ℝ) 1}

/-- The isotropic region is measurable. -/
theorem measurableSet_isoRegion (r : ℕ) (h : Fin d → ℝ) : MeasurableSet (isoRegion r h) := by
  have : isoRegion r h = ⋂ i, (fun x : Fin d → ℝ => x i + r * h i) ⁻¹' Icc 0 1 := by
    ext x
    simp [isoRegion]
  rw [this]
  exact MeasurableSet.iInter fun i => ((measurable_pi_apply i).add_const _) measurableSet_Icc

/-- For `x` in the isotropic region of the cube and `0 ≤ n ≤ r`, `x + nh` lies in the cube. -/
theorem add_smul_mem_cubeSet {r : ℕ} {h x : Fin d → ℝ} (hx : x ∈ isoRegion r h ∩ cubeSet d)
    {n : ℝ} (hn : 0 ≤ n) (hnr : n ≤ r) : x + n • h ∈ cubeSet d := by
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_mul_mem_Icc (hx.2 i (mem_univ i)) (hx.1 i) hn hnr

/-- **The isotropic region on the cube is a step set**: `{x ∈ Q : x + rh ∈ Q}` is the set `Q_{rh}`
of the points `x` with `x, x + h, …, x + rh ∈ Q` (`Rd.stepSet`). -/
theorem isoRegion_inter_cubeSet (r : ℕ) (h : Fin d → ℝ) :
    isoRegion r h ∩ cubeSet d = Rd.stepSet (cubeSet d) r h := by
  ext x
  constructor
  · intro hx l hl
    exact add_smul_mem_cubeSet hx (Nat.cast_nonneg l) (by exact_mod_cast hl)
  · intro hx
    refine ⟨fun i => ?_, by simpa using hx 0 (Nat.zero_le r)⟩
    simpa using hx r le_rfl i (mem_univ i)

/-- The isotropic difference on the cube is the restricted difference on the set `Q`:
`‖Δ_h^r f‖_{L_p(Q_{rh})} = ‖Δ_h^r(f, ·, Q)‖_p`. -/
theorem eLpNorm_higherDiff_isoRegion_eq (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ)
    (h : Fin d → ℝ) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) =
      eLpNorm ((Rd.stepSet (cubeSet d) r h).indicator ((fwdDiff h)^[r] f)) p volume := by
  rw [cubeVol_eq_restrict, Measure.restrict_restrict (measurableSet_isoRegion r h),
    isoRegion_inter_cubeSet, eLpNorm_indicator_eq_eLpNorm_restrict
      (Rd.measurableSet_stepSet (measurableSet_cubeSet d) r h).nullMeasurableSet]
  rfl

/-- The **isotropic modulus of smoothness** on the cube, the modulus on the set `Q` of
`Rd.modulusOn`: `ω_r(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r(f, ·, Q)‖_p`. -/
noncomputable def isoModulus (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : ℝ) : ℝ≥0∞ :=
  Rd.modulusOn volume (cubeSet d) r p f t

/-- **The isotropic modulus through the isotropic regions**:
`ω_r(f, t)_p = sup_{‖h‖_∞ ≤ t} ‖Δ_h^r f‖_{L_p({x ∈ Q : x + rh ∈ Q})}`. -/
theorem isoModulus_eq_iSup (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : ℝ) :
    isoModulus r p f t = ⨆ (h : Fin d → ℝ) (_ : ‖h‖ ≤ t),
      eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) := by
  simp only [eLpNorm_higherDiff_isoRegion_eq]
  rfl

/-- `‖Δ_h^r f‖_{L_p(Q_{rh})} ≤ ω_r(f, t)_p` for `‖h‖_∞ ≤ t`. -/
theorem eLpNorm_higherDiff_le_isoModulus {r : ℕ} {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℂ} {t : ℝ}
    {h : Fin d → ℝ} (hh : ‖h‖ ≤ t) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) ≤
      isoModulus r p f t := by
  rw [eLpNorm_higherDiff_isoRegion_eq]
  exact Rd.eLpNorm_indicator_higherDiff_le_modulusOn hh

/-- The isotropic modulus increases in `t`. -/
theorem isoModulus_mono (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) :
    Monotone (isoModulus r p f) :=
  Rd.modulusOn_mono _ r p f

/-- The isotropic modulus is subadditive. -/
theorem isoModulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (f g : (Fin d → ℝ) → ℂ) (t : ℝ) :
    isoModulus r p (f + g) t ≤ isoModulus r p f t + isoModulus r p g t :=
  Rd.modulusOn_add_le hp _ r f g t

/-- `ω_r(f, t)_p ≤ 2^r ‖f‖_{L_p(Q)}` for the isotropic modulus (`Rd.modulusOn_le`). -/
theorem isoModulus_le {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) (t : ℝ) : isoModulus r p f t ≤ 2 ^ r * eLpNorm f p (cubeVol d) := by
  have h := Rd.modulusOn_le (μ := volume) hf.aestronglyMeasurable (measurableSet_cubeSet d) hp
    r t
  rwa [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_cubeSet d).nullMeasurableSet,
    ← cubeVol_eq_restrict]
    at h

/-- **`‖Δ_h^r f‖_{L_p(Q_{rh})} ≤ 2^r ‖f‖_{L_p(Q)}`**, the bound of `Cube.isoModulus_le` at
`t = ‖h‖_∞`. -/
theorem eLpNorm_higherDiff_le {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) (h : Fin d → ℝ) :
    eLpNorm (higherDiff r h f) p ((cubeVol d).restrict (isoRegion r h)) ≤
      2 ^ r * eLpNorm f p (cubeVol d) :=
  (eLpNorm_higherDiff_le_isoModulus le_rfl).trans (isoModulus_le hf hp r ‖h‖)

/-- **The isotropic modulus depends only on the class in `L_p(Q)`** (`Rd.modulusOn_congr_ae`,
with Mathlib's `ae_eq_restrict_iff_indicator_ae_eq`). -/
theorem isoModulus_congr_ae {f g : (Fin d → ℝ) → ℂ} (hfg : f =ᵐ[cubeVol d] g) (r : ℕ)
    (p : ℝ≥0∞) (t : ℝ) : isoModulus r p f t = isoModulus r p g t := by
  rw [cubeVol_eq_restrict, ae_eq_restrict_iff_indicator_ae_eq (measurableSet_cubeSet d)] at hfg
  exact Rd.modulusOn_congr_ae hfg r p t

/-! ### Coordinate moduli and the isotropic modulus -/

/-- The region of a coordinate difference is the isotropic region of the step `s e_i`, on the
cube. -/
theorem diffRegion_eq_isoRegion (r : ℕ) {s : ℝ} (hs : 0 ≤ s) (i : Fin d) :
    diffRegion d r s i = (cubeVol d).restrict (isoRegion r (Pi.single i s)) := by
  refine cubeVol_restrict_congr (measurable_pi_apply i measurableSet_Icc)
    (measurableSet_isoRegion r _) ?_
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, isoRegion, cubeSet, mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨hxi, hx⟩
    refine ⟨fun c => ?_, hx⟩
    by_cases hc : c = i
    · subst hc
      simp only [Pi.single_eq_same]
      constructor <;> nlinarith [hxi.1, hxi.2, mul_nonneg (Nat.cast_nonneg r) hs]
    · simpa [hc] using hx c
  · rintro ⟨hiso, hx⟩
    refine ⟨?_, hx⟩
    have h := hiso i
    simp only [Pi.single_eq_same] at h
    exact ⟨(hx i).1, by linarith [h.2]⟩

/-- **Coordinate moduli are bounded by the isotropic modulus**: steps `s e_i`, `0 ≤ s ≤ t`, are
isotropic steps with `‖s e_i‖_∞ = s`. -/
theorem coordModulus_le_isoModulus (r : ℕ) (p : ℝ≥0∞) (i : Fin d) (f : (Fin d → ℝ) → ℂ)
    (t : ℝ) : coordModulus r p i f t ≤ isoModulus r p f t := by
  classical
  refine iSup₂_le fun s hs => ?_
  have hnorm : ‖(Pi.single i s : Fin d → ℝ)‖ ≤ t := by
    rw [Pi.norm_single, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  rw [← higherDiff_single, diffRegion_eq_isoRegion r hs.1 i]
  exact eLpNorm_higherDiff_le_isoModulus hnorm

/-- **The modulus on the cube is bounded by the isotropic modulus**: `ω_cube ≤ d ω_iso`. -/
theorem cubeModulus_le_isoModulus (r : ℕ) (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℂ) (t : ℝ) :
    cubeModulus r p f t ≤ d * isoModulus r p f t := by
  calc cubeModulus r p f t ≤ ∑ _i : Fin d, isoModulus r p f t :=
        Finset.sum_le_sum fun i _ => coordModulus_le_isoModulus r p i f t
    _ = d * isoModulus r p f t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The isotropic modulus on `L_p(Q)` at dyadic scales -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The isotropic modulus of an element of `L_p(Q)` at the dyadic scale `2^(-k)`. -/
noncomputable def lpIsoModulus (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) : ℝ≥0∞ :=
  isoModulus r p (f : (Fin d → ℝ) → ℂ) (1 / 2 ^ k)

/-- The isotropic modulus on `L_p(Q)` is subadditive. -/
theorem lpIsoModulus_add_le (r : ℕ) (f g : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpIsoModulus p r (f + g) k ≤ lpIsoModulus p r f k + lpIsoModulus p r g k := by
  rw [lpIsoModulus, isoModulus_congr_ae (Lp.coeFn_add f g)]
  exact isoModulus_add_le Fact.out r _ _ _

/-- `ω_r(f, t)_p ≤ 2^r ‖f‖_p` in `L_p(Q)`, for the isotropic modulus. -/
theorem lpIsoModulus_le (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpIsoModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.enorm_def]
  exact isoModulus_le (Lp.stronglyMeasurable f).measurable Fact.out r _

omit [Fact (1 ≤ p)] in
/-- The isotropic modulus at the dyadic scales decreases with the level. -/
theorem lpIsoModulus_anti (r : ℕ) (f : Lp ℂ p (cubeVol d)) : Antitone (lpIsoModulus p r f) :=
  fun _ _ hjk => isoModulus_mono r p _ (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hjk))

omit [Fact (1 ≤ p)] in
/-- `ω_cube(f, 2^(-k)) ≤ d ω_iso(f, 2^(-k))` in `L_p(Q)`. -/
theorem lpCubeModulus_le_lpIsoModulus (r : ℕ) (f : Lp ℂ p (cubeVol d)) (k : ℕ) :
    lpCubeModulus p r f k ≤ d * lpIsoModulus p r f k :=
  cubeModulus_le_isoModulus r p _ _

/-! ### The cube in the Euclidean space -/

section Euclidean

open ENNReal (lqNorm dyadicWeight)

/-- The **closed unit cube** `[0, 1]^d` as a subset of the Euclidean space `ℝ^d`, the set of
`Rd.BesovDomain.closedUnitCube`. -/
abbrev euclideanCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

/-- The points of `Fin d → ℝ` whose Euclidean copy lies in `[0, 1]^d` form the cube `Q`. -/
theorem preimage_toLp_euclideanCube (d : ℕ) :
    (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' euclideanCube d =
      cubeSet d := by
  ext x
  simp [cubeSet, euclideanCube, -Set.pi_univ_Icc]

/-- The points of `ℝ^d` whose coordinates lie in the cube `Q` form `[0, 1]^d`. -/
theorem preimage_ofLp_cubeSet (d : ℕ) :
    (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) ⁻¹' cubeSet d = euclideanCube d := by
  ext x
  simp [cubeSet, euclideanCube, -Set.pi_univ_Icc]

/-- The cube `[0, 1]^d` in the Euclidean space is measurable: it is the preimage of `Q` under the
coordinates (`Cube.preimage_ofLp_cubeSet`). -/
theorem measurableSet_euclideanCube (d : ℕ) : MeasurableSet (euclideanCube d) := by
  rw [← preimage_ofLp_cubeSet]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measurable (measurableSet_cubeSet d)

/-- **The Euclidean copy preserves the cube measure**: `toLp` carries the cube measure on `Q` to
Lebesgue measure on `[0, 1]^d ⊆ ℝ^d` (Mathlib's `PiLp.volume_preserving_toLp`, restricted with
`MeasureTheory.MeasurePreserving.restrict_preimage`). -/
theorem measurePreserving_toLp_cubeVol (d : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) (cubeVol d)
      (volume.restrict (euclideanCube d)) := by
  have h := (PiLp.volume_preserving_toLp (Fin d)).restrict_preimage
    (measurableSet_euclideanCube d)
  rwa [preimage_toLp_euclideanCube, ← cubeVol_eq_restrict] at h

/-- **The coordinates preserve the cube measure**: `ofLp` carries Lebesgue measure on
`[0, 1]^d ⊆ ℝ^d` to the cube measure on `Q` (Mathlib's `PiLp.volume_preserving_ofLp`). -/
theorem measurePreserving_ofLp_euclideanCube (d : ℕ) :
    MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
      (volume.restrict (euclideanCube d)) (cubeVol d) := by
  have h := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage (measurableSet_cubeSet d)
  rwa [preimage_ofLp_cubeSet, ← cubeVol_eq_restrict] at h

/-- **The Euclidean norm against the maximum norm**: `‖x‖_2 ≤ √d ‖x‖_∞ ≤ 2^d ‖x‖_∞` on `ℝ^d`,
the norm bound of the map from `Fin d → ℝ` to the Euclidean space
(`PiLp.norm_continuousLinearEquiv_symm_le`), with `√d ≤ d < 2^d`. -/
theorem norm_euclideanEquiv_symm_le (d : ℕ) :
    ‖((EuclideanSpace.equiv (Fin d) ℝ).symm : (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ≤
      2 ^ d := by
  refine (PiLp.norm_continuousLinearEquiv_symm_le 2 ℝ (fun _ : Fin d => ℝ)).trans ?_
  rw [Fintype.card_fin]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · calc (d : ℝ) ^ (1 / (2 : ℝ≥0∞)).toReal ≤ (d : ℝ) ^ (1 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hd) ?_
          simpa using ENNReal.toReal_mono ENNReal.one_ne_top
            (show (1 / 2 : ℝ≥0∞) ≤ 1 by norm_num)
      _ ≤ 2 ^ d := by
          rw [Real.rpow_one]
          exact_mod_cast Nat.lt_two_pow_self.le

variable (p) in
/-- **Restriction to the unit cube in coordinates**: `F ↦ F|_{Q_E} ∘ toLp`, from `L_p(ℝ^d)` on
the Euclidean space to `L_p(Q)`, `Q = [0, 1]^d` in `Fin d → ℝ`: the restriction to
`Q_E = [0, 1]^d ⊆ ℝ^d` (Mathlib's `MeasureTheory.LpToLpRestrictCLM`) followed by the measure
preserving change of coordinates (`Cube.measurePreserving_toLp_cubeVol`). -/
noncomputable def restrictEuclidean (d : ℕ) :
    Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℂ] Lp ℂ p (cubeVol d) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      (measurePreserving_toLp_cubeVol d)).toContinuousLinearMap ∘L
    LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p (euclideanCube d)

variable (p) in
/-- **Extension by zero from the unit cube**: `g ↦ 1_{Q_E} (g ∘ ofLp)`, from `L_p(Q)` to
`L_p(ℝ^d)` on the Euclidean space (`Rd.indicatorExtendLp` after the measure preserving change of
coordinates `Cube.measurePreserving_ofLp_euclideanCube`). -/
noncomputable def extendEuclidean (d : ℕ) :
    Lp ℂ p (cubeVol d) →L[ℂ] Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  Rd.indicatorExtendLp (measurableSet_euclideanCube d) subset_rfl ∘L
    (Lp.compMeasurePreservingₗᵢ ℂ (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
      (measurePreserving_ofLp_euclideanCube d)).toContinuousLinearMap

/-- The restriction to the cube is `F ∘ toLp` almost everywhere on `Q`. -/
theorem restrictEuclidean_ae (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (restrictEuclidean p d F : (Fin d → ℝ) → ℂ) =ᵐ[cubeVol d] F ∘ WithLp.toLp 2 :=
  (Lp.coeFn_compMeasurePreserving _ (measurePreserving_toLp_cubeVol d)).trans
    ((measurePreserving_toLp_cubeVol d).quasiMeasurePreserving.ae_eq_comp
      (LpToLpRestrictCLM_coeFn ℂ (euclideanCube d) F))

/-- The extension by zero is `1_{Q_E} (g ∘ ofLp)` almost everywhere on `ℝ^d`. -/
theorem extendEuclidean_ae (g : Lp ℂ p (cubeVol d)) :
    (extendEuclidean p d g : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      (euclideanCube d).indicator (g ∘ WithLp.ofLp) :=
  (Rd.indicatorExtendLp_apply_ae (measurableSet_euclideanCube d) subset_rfl _).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (measurableSet_euclideanCube d)).1
      (Lp.coeFn_compMeasurePreserving g (measurePreserving_ofLp_euclideanCube d)))

/-- **The restriction of the extension by zero is the identity** on `L_p(Q)`, since
`ofLp (toLp x) = x` and `toLp x ∈ Q_E` for `x ∈ Q`. -/
theorem restrictEuclidean_extendEuclidean (g : Lp ℂ p (cubeVol d)) :
    restrictEuclidean p d (extendEuclidean p d g) = g := by
  refine Lp.ext ?_
  have hmem : ∀ᵐ x ∂(cubeVol d), x ∈ cubeSet d := by
    rw [cubeVol_eq_restrict]
    exact ae_restrict_mem (measurableSet_cubeSet d)
  filter_upwards [restrictEuclidean_ae (extendEuclidean p d g),
    (measurePreserving_toLp_cubeVol d).quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae (extendEuclidean_ae g)), hmem] with x h1 h2 h3
  rw [h1, h2, Function.comp_apply, Set.indicator_of_mem
    (show WithLp.toLp 2 x ∈ euclideanCube d by rwa [← Set.mem_preimage,
      preimage_toLp_euclideanCube])]
  rfl

/-- **The extension of the restriction agrees with `F` on the cube**:
`1_{Q_E} E(F|_Q) = 1_{Q_E} F` in `L_p(ℝ^d)` (`Rd.indicatorLp_eq_iff_ae_eq_restrict`). -/
theorem indicatorLp_extendEuclidean_restrictEuclidean
    (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Rd.indicatorLp (measurableSet_euclideanCube d)
        (extendEuclidean p d (restrictEuclidean p d F)) =
      Rd.indicatorLp (measurableSet_euclideanCube d) F := by
  refine (Rd.indicatorLp_eq_iff_ae_eq_restrict (measurableSet_euclideanCube d)).2 ?_
  filter_upwards [ae_restrict_of_ae (extendEuclidean_ae (restrictEuclidean p d F)),
    (measurePreserving_ofLp_euclideanCube d).quasiMeasurePreserving.ae_eq_comp
      (restrictEuclidean_ae F), ae_restrict_mem (measurableSet_euclideanCube d)] with y h1 h2 h3
  rw [h1, Set.indicator_of_mem (show y ∈ euclideanCube d from h3)]
  exact h2

/-- **The restriction sees only the cube**: if `1_{Q_E} F = 1_{Q_E} G` in `L_p(ℝ^d)`, then
`F|_Q = G|_Q` in `L_p(Q)`. -/
theorem restrictEuclidean_eq_of_indicatorLp_eq
    {F G : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (h : Rd.indicatorLp (measurableSet_euclideanCube d) F =
      Rd.indicatorLp (measurableSet_euclideanCube d) G) :
    restrictEuclidean p d F = restrictEuclidean p d G := by
  refine Lp.ext ?_
  filter_upwards [restrictEuclidean_ae F, restrictEuclidean_ae G,
    (measurePreserving_toLp_cubeVol d).quasiMeasurePreserving.ae_eq_comp
      ((Rd.indicatorLp_eq_iff_ae_eq_restrict (measurableSet_euclideanCube d)).1 h)]
    with x h1 h2 h3
  rw [h1, h2]
  exact h3

/-- **The norm of the restriction**: `‖F|_Q‖_{L_p(Q)} = ‖1_{Q_E} F‖_{L_p(ℝ^d)}`
(`Rd.enorm_indicatorLp_eq`, `MeasureTheory.Lp.enorm_compMeasurePreserving`). -/
theorem enorm_restrictEuclidean (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖restrictEuclidean p d F‖ₑ = ‖Rd.indicatorLp (measurableSet_euclideanCube d) F‖ₑ := by
  rw [Rd.enorm_indicatorLp_eq]
  exact Lp.enorm_compMeasurePreserving _ (measurePreserving_toLp_cubeVol d)

/-- **Extension by zero keeps the norm**: `‖E g‖_{L_p(ℝ^d)} = ‖g‖_{L_p(Q)}`. -/
theorem enorm_extendEuclidean (g : Lp ℂ p (cubeVol d)) : ‖extendEuclidean p d g‖ₑ = ‖g‖ₑ := by
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (extendEuclidean_ae g),
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_euclideanCube d).nullMeasurableSet,
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable g)
      (measurePreserving_ofLp_euclideanCube d)]

/-- **The Euclidean modulus on the cube is at most the isotropic one**: for `F ∈ L_p(ℝ^d)`,
`ω_r(F, 2^(-k), Q_E)_p ≤ ω^iso_r(F|_Q, 2^(-k))_p`, with the modulus on `Q_E` for the Euclidean
norm (`Rd.lpModulusOn`), since `‖ofLp h‖_∞ ≤ ‖h‖_2` (`Rd.modulusOn_comp_le`,
`PiLp.norm_continuousLinearEquiv_le`). -/
theorem lpModulusOn_euclideanCube_le_lpIsoModulus (r : ℕ)
    (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) (k : ℕ) :
    Rd.lpModulusOn p (euclideanCube d) r F k ≤ lpIsoModulus p r (restrictEuclidean p d F) k := by
  have hcongr : (euclideanCube d).indicator (F : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      (euclideanCube d).indicator
        ((restrictEuclidean p d F : (Fin d → ℝ) → ℂ) ∘ WithLp.ofLp) :=
    (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_euclideanCube d)).1
      ((measurePreserving_ofLp_euclideanCube d).quasiMeasurePreserving.ae_eq_comp
        (restrictEuclidean_ae F)).symm
  have hcoe : ⇑(EuclideanSpace.equiv (Fin d) ℝ : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ)) =
      WithLp.ofLp := rfl
  have he : MeasurePreserving
      (EuclideanSpace.equiv (Fin d) ℝ : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ)) := by
    rw [hcoe]
    exact PiLp.volume_preserving_ofLp (Fin d)
  have h := Rd.modulusOn_comp_le _ he (measurableSet_cubeSet d)
    (Lp.stronglyMeasurable (restrictEuclidean p d F)).aestronglyMeasurable r p (1 / 2 ^ k)
  rw [hcoe, preimage_ofLp_cubeSet] at h
  rw [Rd.lpModulusOn, Rd.modulusOn_congr_ae hcongr]
  exact h.trans (isoModulus_mono r p _ (mul_le_of_le_one_left (by positivity)
    (PiLp.norm_continuousLinearEquiv_le 2 ℝ _)))

/-- **The isotropic modulus is at most the Euclidean one `d` levels coarser**: for
`F ∈ L_p(ℝ^d)`, `ω^iso_r(F|_Q, 2^(-(k+d)))_p ≤ ω_r(F, 2^(-k), Q_E)_p`, since
`‖toLp h‖_2 ≤ 2^d ‖h‖_∞` (`Rd.modulusOn_comp_le`, `Cube.norm_euclideanEquiv_symm_le`). -/
theorem lpIsoModulus_add_le_lpModulusOn (r : ℕ)
    (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) (k : ℕ) :
    lpIsoModulus p r (restrictEuclidean p d F) (k + d) ≤
      Rd.lpModulusOn p (euclideanCube d) r F k := by
  have hscale : ‖((EuclideanSpace.equiv (Fin d) ℝ).symm :
      (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ * (1 / 2 ^ (k + d)) ≤ 1 / 2 ^ k :=
    calc _ ≤ 2 ^ d * (1 / 2 ^ (k + d)) :=
          mul_le_mul_of_nonneg_right (norm_euclideanEquiv_symm_le d) (by positivity)
      _ = 1 / 2 ^ k := by
          rw [pow_add]
          field_simp
  have hcoe : ⇑((EuclideanSpace.equiv (Fin d) ℝ).symm :
      (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d)) = WithLp.toLp 2 := rfl
  have he : MeasurePreserving ((EuclideanSpace.equiv (Fin d) ℝ).symm :
      (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [hcoe]
    exact PiLp.volume_preserving_toLp (Fin d)
  have h := Rd.modulusOn_comp_le _ he (measurableSet_euclideanCube d)
    (Lp.aestronglyMeasurable F) r p (1 / 2 ^ (k + d))
  rw [hcoe, preimage_toLp_euclideanCube] at h
  rw [lpIsoModulus, isoModulus_congr_ae (restrictEuclidean_ae F)]
  exact h.trans (Rd.modulusOn_mono _ r p _ hscale)

/-- **The Euclidean intrinsic quasi-norm on the cube is at most the isotropic one**:
`N_{Q_E}(F) ≤ ‖F|_Q‖_p + ‖(2^(ks) ω^iso_r(F|_Q, 2^(-k))_p)_k‖_{ℓ_q}` for `F ∈ L_p(ℝ^d)`, with
the intrinsic quasi-norm `N_{Q_E}` of `Rd.modNormOn` (`Cube.enorm_restrictEuclidean`,
`Cube.lpModulusOn_euclideanCube_le_lpIsoModulus`). -/
theorem modNormOn_euclideanCube_le_isoNorm (r : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Rd.modNormOn (measurableSet_euclideanCube d) r s q F ≤ ‖restrictEuclidean p d F‖ₑ +
      lqNorm q (fun k => dyadicWeight s k * lpIsoModulus p r (restrictEuclidean p d F) k) := by
  rw [Rd.modNormOn, enorm_restrictEuclidean]
  exact add_le_add le_rfl (ENNReal.lqNorm_mono fun k =>
    mul_le_mul' le_rfl (lpModulusOn_euclideanCube_le_lpIsoModulus r F k))

/-- **The isotropic quasi-norm of the restriction is at most a multiple of the Euclidean one**:
for `s ≥ 0`, `1 ≤ q ≤ ∞` and `F ∈ L_p(ℝ^d)`,
`‖F|_Q‖_p + ‖(2^(ks) ω^iso_r(F|_Q, 2^(-k))_p)_k‖_{ℓ_q} ≤ (1 + 2^(ds) (d 2^r + 1)) N_{Q_E}(F)`.
The comparison of the moduli `d` levels apart (`Cube.lpIsoModulus_add_le_lpModulusOn`) passes to
the quasi-norms at the cost `2^(ds)` (`ENNReal.lqNorm_dyadicWeight_le_of_shift`), and the first `d`
levels are at most `2^r ‖F|_Q‖_p` (`Cube.lpIsoModulus_le`). -/
theorem isoNorm_restrictEuclidean_le_modNormOn (r : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ‖restrictEuclidean p d F‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpIsoModulus p r (restrictEuclidean p d F) k) ≤
      (1 + dyadicWeight s d * (d * 2 ^ r + 1)) *
        Rd.modNormOn (measurableSet_euclideanCube d) r s q F := by
  set N := Rd.modNormOn (measurableSet_euclideanCube d) r s q F
  have hI : ‖restrictEuclidean p d F‖ₑ ≤ N := by
    rw [enorm_restrictEuclidean]
    exact le_self_add
  have hΛ : lqNorm q (fun k => dyadicWeight s k * Rd.lpModulusOn p (euclideanCube d) r F k) ≤
      N := le_add_self
  have hshift := ENNReal.lqNorm_dyadicWeight_le_of_shift hq hs d
    (B := 2 ^ r * ‖restrictEuclidean p d F‖ₑ) (fun k _ => lpIsoModulus_le r _ k)
    (fun k => lpIsoModulus_add_le_lpModulusOn r F k)
  calc ‖restrictEuclidean p d F‖ₑ +
        lqNorm q (fun k => dyadicWeight s k * lpIsoModulus p r (restrictEuclidean p d F) k)
      ≤ ‖restrictEuclidean p d F‖ₑ + dyadicWeight s d * (d * (2 ^ r *
          ‖restrictEuclidean p d F‖ₑ) + lqNorm q (fun k => dyadicWeight s k *
            Rd.lpModulusOn p (euclideanCube d) r F k)) := add_le_add le_rfl hshift
    _ ≤ N + dyadicWeight s d * (d * (2 ^ r * N) + N) := by gcongr
    _ = (1 + dyadicWeight s d * (d * 2 ^ r + 1)) * N := by ring

end Euclidean

end Cube
