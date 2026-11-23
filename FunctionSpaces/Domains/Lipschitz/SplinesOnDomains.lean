/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import FunctionSpaces.Domains.Cube.IsoCoincidence
public import FunctionSpaces.Domains.Lipschitz.BesovDomains
public import ApproximationSpaces.Transfer
public import ApproximationSpaces.Decompositions.Blocks

/-!
# Splines on domains through restriction to a cube

Let `Ω` be a measurable subset of the Euclidean space `ℝ^d`, let `a ∈ ℝ^d` and `L > 0`, and let
`Q = a + L [0, 1]^d = {x : a_i ≤ x_i ≤ a_i + L}` (`Cube.euclideanCubeAt`) be a cube with `Ω ⊆ Q`.
In the theorems on `Ω`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1`, and
`N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}` is the intrinsic quasi-norm of
`Rd.modNormOn`.

* **The cube `Q` and its tensor splines.** The affine map `A x = a + L x` carries the unit cube
  `Q_E = [0, 1]^d ⊆ ℝ^d` onto `Q` (`Cube.preimage_affine_euclideanCubeAt`,
  `Cube.preimage_affine_inv_euclideanCube`). Composition with `A` followed by the restriction to
  the unit cube (`Cube.restrictEuclideanAt`), and the extension by zero followed by composition
  with `A⁻¹` (`Cube.extendEuclideanAt`), move functions between `L_p(ℝ^d)` and `L_p([0, 1]^d)`.
  The tensor splines of order `r` on `Q` are those of `[0, 1]^d` moved along `A`, as a scheme in
  `L_p(Q)` (`Cube.cubeSplineSchemeAt`), and its approximation spaces are those of the unit cube
  moved along `A` (`Cube.memApprox_cubeSplineSchemeAt_iff`).
* **Restrictions of spline space elements.** For every measurable `Ω ⊆ Q` and
  `0 ≤ s < r - 1 + 1/p`, every `f` that agrees on `Ω` with an element of the approximation space
  `A^s_q` of the tensor splines on `Q` has `N_Ω(f) < ∞`
  (`Rd.modNormOn_lt_top_of_memApprox_cubeSplineSchemeAt`): the cube theorem with the Euclidean
  modulus (`Cube.memApprox_cubeSplineScheme_restrictEuclidean_iff`), moved to `Q` by the affine
  transport (`Rd.exists_modNormOn_compAffineLp_le`), and `N_Ω ≤ N_Q`.
* **Functions of finite intrinsic quasi-norm are restrictions.** If `Ω` has the extension property
  (`Rd.HasBesovExtension`) and `0 < s < r - 1 + 1/p`, every `f` with `N_Ω(f) < ∞` agrees on `Ω`
  with some `G` in that approximation space, with `‖G‖_{A^s_q} ≤ C N_Ω(f)` for one `C < ∞`
  (`Rd.HasBesovExtension.exists_cubeSplineAt_le`,
  `Rd.HasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff`), also with an intrinsic modulus
  of every order `r' > s`
  (`Rd.HasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff_of_order`); equivalently
  `f = ∑_k b_k` on `Ω` with tensor splines `b_k` of level `k` on `Q` and
  `‖(2^(ks) ‖b_k‖_{L_p(Q)})_k‖_{ℓ_q} < ∞` (`Rd.HasBesovExtension.exists_cubeSplineBlocksAt_iff`,
  the norm `N_3` of DeVore–Popov, Theorem 5.1).
* **Bounded Lipschitz domains and the unit cube.** Every bounded Lipschitz domain in `Q` has the
  extension property, so the functions of `B^s_{p,q}(Ω)` (`Rd.BoundedLipschitzDomain.DomainBesov`)
  agree on `Ω` with elements of the approximation spaces of the tensor splines on `Q`, and
  conversely (`Rd.BoundedLipschitzDomain.exists_memApprox_cubeSplineSchemeAt_iff`), also with an
  intrinsic modulus of every order `r' > s`
  (`Rd.BoundedLipschitzDomain.exists_memApprox_cubeSplineSchemeAt_iff_of_order`); on `Ω` these
  are the restrictions of `B^s_{p,q}(ℝ^d)`
  (`Rd.BoundedLipschitzDomain.exists_memApprox_cubeSplineSchemeAt_iff_exists_besov`). On the unit
  cube itself the tensor splines describe the restrictions of `B^s_{p,q}(ℝ^d)`
  (`Cube.memApprox_cubeSplineScheme_iff_exists_besov`).
* **The restricted splines on `Ω`.** The restrictions to `Ω` of the tensor splines on `Q` form an
  approximation scheme in `L_p(Ω)` (`Rd.domainSplineScheme`), whose error at complexity `2^k` is
  `inf_S ‖f - S‖_{L_p(Ω)}` over the restrictions `S` of the splines of level `k`. They satisfy the
  one-sided intrinsic Jackson theorem
  `‖f‖_{L_p(Ω)} + ‖(2^(ks) inf_S ‖f - S‖_{L_p(Ω)})_k‖_{ℓ_q} ≤ C N_Ω(f)`
  (`Rd.HasBesovExtension.exists_approxNormDyadic_domainSplineScheme_le`,
  `Rd.HasBesovExtension.memApprox_domainSplineScheme`), the functorial half of the retract theorem
  (`ApproximationScheme.approxNormDyadic_map_le`).

The converse inclusion, from the approximation space of the restricted splines into the Besov
space of `Ω`, would follow from a Bernstein inequality for the restricted splines in `L_p(Ω)`,
whose constants degenerate on cells that meet `Ω` in thin pieces, or from an
approximation-preserving extension for the restriction `Rd.restrictSubsetLp`
(`ApproximationScheme.memApprox_iff_exists_restrict`); the extended B-splines of
Höllig–Reif–Wipper are the standard stabilisation.

Sources: DeVore, *Nonlinear approximation*, §6.2 and §7.7 (the restriction form);
DeVore–Sharpley, *Besov spaces on domains in `ℝ^d`*, §6 (Theorem 6.6 for `p ≥ 1`, Theorems
6.1–6.3 for `p ≤ 1`); Johnen–Scherer (an extension that bounds the moduli of smoothness, for
`p ≥ 1`); DeVore–Popov, *Interpolation of Besov spaces*, Theorem 5.1.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight)

/-- The spline range `s < r - 1 + 1/p` lies below `r` for `1 ≤ p ≤ ∞`, since `1/p ≤ 1` (with
`1/p = 0` for `p = ∞`). -/
private theorem lt_of_lt_splineRange {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℕ} {s : ℝ}
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) : s < r := by
  have h1p : 1 / p.toReal ≤ 1 := by
    rcases eq_or_ne p ∞ with hpinf | hpinf
    · simp [hpinf]
    · have h := ENNReal.one_le_toReal_of_one_le Fact.out hpinf
      exact (div_le_one (by linarith)).2 h
  linarith

namespace Rd

/-! ### Restrictions and cut-offs -/

section Restrict

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Agreement passes to subsets**: if `1_t F = 1_t f` in `L_p(μ)` and `s ⊆ t` are measurable,
then `1_s F = 1_s f` (`Rd.indicatorLp_eq_iff_ae_eq_restrict`). -/
theorem indicatorLp_eq_of_subset {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) {F f : Lp ℂ p μ} (h : indicatorLp ht F = indicatorLp ht f) :
    indicatorLp hs F = indicatorLp hs f :=
  (indicatorLp_eq_iff_ae_eq_restrict hs).2
    (ae_restrict_of_ae_restrict_of_subset hst ((indicatorLp_eq_iff_ae_eq_restrict ht).1 h))

/-- **The restriction sees only the cut-off**: for a measurable `s` and `F, G ∈ L_p(μ)`, the
restrictions `F|_s, G|_s ∈ L_p(μ|_s)` (Mathlib's `MeasureTheory.LpToLpRestrictCLM`) agree iff
`1_s F = 1_s G` in `L_p(μ)`. -/
theorem LpToLpRestrictCLM_eq_iff_indicatorLp_eq {s : Set α} (hs : MeasurableSet s)
    {F G : Lp ℂ p μ} :
    LpToLpRestrictCLM α ℂ ℂ μ p s F = LpToLpRestrictCLM α ℂ ℂ μ p s G ↔
      indicatorLp hs F = indicatorLp hs G := by
  rw [indicatorLp_eq_iff_ae_eq_restrict hs, Lp.ext_iff]
  exact ⟨fun h => (LpToLpRestrictCLM_coeFn ℂ s F).symm.trans
      (h.trans (LpToLpRestrictCLM_coeFn ℂ s G)),
    fun h => (LpToLpRestrictCLM_coeFn ℂ s F).trans
      (h.trans (LpToLpRestrictCLM_coeFn ℂ s G).symm)⟩

/-- **The restriction of the extension by zero is the identity**: for a measurable `s` and
`G ∈ L_p(μ|_s)`, `(1_s G)|_s = G` (`Rd.restrictSubsetLp_ae`). -/
theorem LpToLpRestrictCLM_indicatorExtendLp {s : Set α} (hs : MeasurableSet s)
    (G : Lp ℂ p (μ.restrict s)) :
    LpToLpRestrictCLM α ℂ ℂ μ p s (indicatorExtendLp hs subset_rfl G) = G :=
  Lp.ext (restrictSubsetLp_ae hs subset_rfl G)

/-- **Restriction of a function that agrees with `f` on the smaller set**: for measurable
`D ⊆ O`, `G ∈ L_p(μ|_O)` and `f ∈ L_p(μ)` with `1_D (1_O G) = 1_D f`, the restriction
`G|_D ∈ L_p(μ|_D)` (`Rd.restrictSubsetLp`) is `f|_D`. -/
theorem restrictSubsetLp_eq_of_indicatorLp_eq {D O : Set α} (hD : MeasurableSet D)
    (hO : MeasurableSet O) (hDO : D ⊆ O) {G : Lp ℂ p (μ.restrict O)} {f : Lp ℂ p μ}
    (h : indicatorLp hD (indicatorExtendLp hO subset_rfl G) = indicatorLp hD f) :
    restrictSubsetLp hD hDO G = LpToLpRestrictCLM α ℂ ℂ μ p D f := by
  refine Lp.ext ?_
  filter_upwards [restrictSubsetLp_ae hD hDO G, LpToLpRestrictCLM_coeFn ℂ D f,
    (indicatorLp_eq_iff_ae_eq_restrict hD).1 h,
    ae_restrict_of_ae (indicatorExtendLp_apply_ae hO subset_rfl G), ae_restrict_mem hD]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, ← h3, h4, Set.indicator_of_mem (hDO h5)]

end Restrict

/-! ### Cut-offs under affine maps -/

section Affine

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] {μ : Measure V} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- **Agreement on a set moves along affine maps**: for `A x = a + L x`, `L > 0`, measurable `U`
and `T = A⁻¹(U)`, if `1_U G₁ = 1_U G₂` in `L_p(μ)`, then `1_T (G₁ ∘ A) = 1_T (G₂ ∘ A)`
(`Rd.compAffineLp`, `Rd.ae_eq_comp_affine`). -/
theorem indicatorLp_compAffineLp_eq_of_indicatorLp_eq (a : V) {L : ℝ} (hL : 0 < L)
    {U T : Set V} (hU : MeasurableSet U) (hT : MeasurableSet T)
    (hUT : (fun x => a + L • x) ⁻¹' U = T) {G₁ G₂ : Lp ℂ p μ}
    (h : indicatorLp hU G₁ = indicatorLp hU G₂) :
    indicatorLp hT (compAffineLp a hL G₁) = indicatorLp hT (compAffineLp a hL G₂) := by
  refine (indicatorLp_eq_iff_ae_eq_restrict hT).2 ?_
  have h' := ae_eq_comp_affine a hL
    ((ae_eq_restrict_iff_indicator_ae_eq hU).1 ((indicatorLp_eq_iff_ae_eq_restrict hU).1 h))
  filter_upwards [ae_restrict_of_ae (compAffineLp_ae a hL G₁),
    ae_restrict_of_ae (compAffineLp_ae a hL G₂), ae_restrict_of_ae h', ae_restrict_mem hT]
    with x h1 h2 h3 hx
  have hx' : a + L • x ∈ U := by
    rw [← hUT] at hx
    exact hx
  rw [h1, h2]
  simpa only [Set.indicator_of_mem hx'] using h3

end Affine

end Rd

namespace Cube

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The cube `a + L [0, 1]^d` and its tensor splines -/

/-- The **cube** `a + L [0, 1]^d = {x : a_i ≤ x_i ≤ a_i + L for every i}` in the Euclidean
space `ℝ^d`. -/
def euclideanCubeAt (a : EuclideanSpace ℝ (Fin d)) (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Icc (a i) (a i + L)}

/-- The cube `a + L [0, 1]^d` is measurable: it is the preimage of a product of closed intervals
under the coordinates (Mathlib's `PiLp.volume_preserving_ofLp`). -/
theorem measurableSet_euclideanCubeAt (a : EuclideanSpace ℝ (Fin d)) (L : ℝ) :
    MeasurableSet (euclideanCubeAt a L) := by
  have h : euclideanCubeAt a L = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) ⁻¹'
      Set.univ.pi fun i => Icc (a i) (a i + L) := by
    ext x
    simp [euclideanCubeAt, -Set.pi_univ_Icc]
  rw [h]
  exact (PiLp.volume_preserving_ofLp (Fin d)).measurable
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc)

/-- **The affine map carries the unit cube onto the cube**: for `L > 0`, `x ↦ a + L x` maps
`x` into `a + L [0, 1]^d` iff `x ∈ [0, 1]^d`. -/
theorem preimage_affine_euclideanCubeAt (a : EuclideanSpace ℝ (Fin d)) {L : ℝ} (hL : 0 < L) :
    (fun x => a + L • x) ⁻¹' euclideanCubeAt a L = euclideanCube d := by
  ext x
  simp only [euclideanCubeAt, euclideanCube, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, le_add_iff_nonneg_right, add_le_add_iff_left,
    mul_nonneg_iff_of_pos_left hL, mul_le_iff_le_one_right hL]

/-- **The inverse affine map carries the cube onto the unit cube**: for `L > 0`,
`y ↦ -(L⁻¹ a) + L⁻¹ y = L⁻¹ (y - a)` maps `y` into `[0, 1]^d` iff `y ∈ a + L [0, 1]^d`. -/
theorem preimage_affine_inv_euclideanCube (a : EuclideanSpace ℝ (Fin d)) {L : ℝ} (hL : 0 < L) :
    (fun y => -(L⁻¹ • a) + L⁻¹ • y) ⁻¹' euclideanCube d = euclideanCubeAt a L := by
  have hcomp : (fun x => a + L • x) ∘ (fun y => -(L⁻¹ • a) + L⁻¹ • y) = id := by
    funext y
    simp only [Function.comp_apply, id, smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hL.ne',
      one_smul, add_neg_cancel_left]
  rw [← preimage_affine_euclideanCubeAt a hL, ← Set.preimage_comp, hcomp, Set.preimage_id]

variable (p) in
/-- **Restriction to the cube `a + L [0, 1]^d` in the coordinates of `[0, 1]^d`**: for `L > 0`,
`F ↦ F(a + L ·)|_{[0, 1]^d}`, from `L_p(ℝ^d)` to `L_p([0, 1]^d)`: the composition with the affine
map (`Rd.compAffineLp`) followed by the restriction to the unit cube (`Cube.restrictEuclidean`). -/
noncomputable def restrictEuclideanAt (a : EuclideanSpace ℝ (Fin d)) {L : ℝ} (hL : 0 < L) :
    Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℂ] Lp ℂ p (cubeVol d) :=
  restrictEuclidean p d ∘L Rd.compAffineLp a hL

variable (p) in
/-- **Transport from `[0, 1]^d` to the cube `a + L [0, 1]^d` with extension by zero**: for
`L > 0`, `g ↦ 1_Q g(L⁻¹ (· - a))`, `Q = a + L [0, 1]^d`, from `L_p([0, 1]^d)` to `L_p(ℝ^d)`: the
extension by zero (`Cube.extendEuclidean`) followed by the composition with the inverse affine
map. -/
noncomputable def extendEuclideanAt (a : EuclideanSpace ℝ (Fin d)) {L : ℝ} (hL : 0 < L) :
    Lp ℂ p (cubeVol d) →L[ℂ] Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  Rd.compAffineLp (-(L⁻¹ • a)) (inv_pos.2 hL) ∘L extendEuclidean p d

/-- **The restriction of the transport is the identity** on `L_p([0, 1]^d)`
(`Rd.compAffineLp_compAffineLp_inv`, `Cube.restrictEuclidean_extendEuclidean`). -/
theorem restrictEuclideanAt_extendEuclideanAt (a : EuclideanSpace ℝ (Fin d)) {L : ℝ}
    (hL : 0 < L) (g : Lp ℂ p (cubeVol d)) :
    restrictEuclideanAt p a hL (extendEuclideanAt p a hL g) = g := by
  change restrictEuclidean p d (Rd.compAffineLp a hL
    (Rd.compAffineLp (-(L⁻¹ • a)) (inv_pos.2 hL) (extendEuclidean p d g))) = g
  rw [Rd.compAffineLp_compAffineLp_inv, restrictEuclidean_extendEuclidean]

/-- **The restriction to the cube sees only the cube**: if `1_Q F = 1_Q G` in `L_p(ℝ^d)` for
`Q = a + L [0, 1]^d`, then `F` and `G` have the same restriction in `L_p([0, 1]^d)`
(`Rd.indicatorLp_compAffineLp_eq_of_indicatorLp_eq`,
`Cube.restrictEuclidean_eq_of_indicatorLp_eq`). -/
theorem restrictEuclideanAt_eq_of_indicatorLp_eq (a : EuclideanSpace ℝ (Fin d)) {L : ℝ}
    (hL : 0 < L) {F G : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (h : Rd.indicatorLp (measurableSet_euclideanCubeAt a L) F =
      Rd.indicatorLp (measurableSet_euclideanCubeAt a L) G) :
    restrictEuclideanAt p a hL F = restrictEuclideanAt p a hL G :=
  restrictEuclidean_eq_of_indicatorLp_eq (Rd.indicatorLp_compAffineLp_eq_of_indicatorLp_eq a hL
    (measurableSet_euclideanCubeAt a L) (measurableSet_euclideanCube d)
    (preimage_affine_euclideanCubeAt a hL) h)

/-- **The transport of the restriction agrees with `F` on the cube**: for
`Q = a + L [0, 1]^d` and `F ∈ L_p(ℝ^d)`, `1_Q E(R F) = 1_Q F`, where `R` is the restriction to
`Q` in the coordinates of `[0, 1]^d` and `E` the transport back with extension by zero. -/
theorem indicatorLp_extendEuclideanAt_restrictEuclideanAt (a : EuclideanSpace ℝ (Fin d))
    {L : ℝ} (hL : 0 < L) (F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Rd.indicatorLp (measurableSet_euclideanCubeAt a L)
        (extendEuclideanAt p a hL (restrictEuclideanAt p a hL F)) =
      Rd.indicatorLp (measurableSet_euclideanCubeAt a L) F := by
  have h := Rd.indicatorLp_compAffineLp_eq_of_indicatorLp_eq (-(L⁻¹ • a)) (inv_pos.2 hL)
    (measurableSet_euclideanCube d) (measurableSet_euclideanCubeAt a L)
    (preimage_affine_inv_euclideanCube a hL)
    (indicatorLp_extendEuclidean_restrictEuclidean (Rd.compAffineLp a hL F))
  rw [Rd.compAffineLp_inv_compAffineLp] at h
  exact h

variable (p) in
/-- **The tensor splines of order `r` on the cube `Q = a + L [0, 1]^d`**: the scheme of the
tensor splines of `[0, 1]^d` (`Cube.cubeSplineScheme`) moved along `x ↦ a + L x`, as a scheme in
`L_p(Q)`: its approximants of complexity `n` are the restrictions to `Q` of
`Cube.extendEuclideanAt p a hL g` for the approximants `g` of `[0, 1]^d`
(`ApproximationScheme.map`). -/
noncomputable def cubeSplineSchemeAt (a : EuclideanSpace ℝ (Fin d)) {L : ℝ} (hL : 0 < L)
    (r : ℕ) : ApproximationScheme (Lp ℂ p (volume.restrict (euclideanCubeAt a L))) :=
  (cubeSplineScheme p d r).map
    ((LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p (euclideanCubeAt a L) ∘L
      extendEuclideanAt p a hL).restrictScalars ℝ).toLinearMap

/-- The approximants of complexity `2^k` on the cube `a + L [0, 1]^d` are the splines of level
`k` of `[0, 1]^d` moved to the cube. -/
theorem mem_cubeSplineSchemeAt_two_pow (a : EuclideanSpace ℝ (Fin d)) {L : ℝ} (hL : 0 < L)
    {r k : ℕ} {G : Lp ℂ p (volume.restrict (euclideanCubeAt a L))} :
    G ∈ cubeSplineSchemeAt p a hL r (2 ^ k) ↔ ∃ g ∈ cubeSplineSpace p r k,
      LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p (euclideanCubeAt a L)
        (extendEuclideanAt p a hL g) = G :=
  (ApproximationScheme.mem_map _).trans
    (exists_congr fun _ => and_congr_left fun _ => mem_cubeSplineScheme_two_pow)

/-- **The approximation spaces move along the affine map**: for `Q = a + L [0, 1]^d`, every `s`
and `q`, `G ∈ L_p(Q)` lies in the approximation space `A^s_q` of the tensor splines on `Q` iff its
transport `R(1_Q G)` to `[0, 1]^d`, `R = Cube.restrictEuclideanAt p a hL`, lies in `A^s_q` of the
tensor splines of `[0, 1]^d`. The two transports are inverse to each other and carry splines to
splines
(`ApproximationScheme.MemApprox.map`). -/
theorem memApprox_cubeSplineSchemeAt_iff (a : EuclideanSpace ℝ (Fin d)) {L : ℝ} (hL : 0 < L)
    {r : ℕ} {s : ℝ} {q : ℝ≥0∞} (G : Lp ℂ p (volume.restrict (euclideanCubeAt a L))) :
    (cubeSplineSchemeAt p a hL r).MemApprox s q G ↔ (cubeSplineScheme p d r).MemApprox s q
      (restrictEuclideanAt p a hL
        (Rd.indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G)) := by
  set hQ := measurableSet_euclideanCubeAt a L
  set T : Lp ℂ p (cubeVol d) →L[ℝ] Lp ℂ p (volume.restrict (euclideanCubeAt a L)) :=
    (LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p (euclideanCubeAt a L) ∘L
      extendEuclideanAt p a hL).restrictScalars ℝ
  set S : Lp ℂ p (volume.restrict (euclideanCubeAt a L)) →L[ℝ] Lp ℂ p (cubeVol d) :=
    (restrictEuclideanAt p a hL ∘L Rd.indicatorExtendLp hQ subset_rfl).restrictScalars ℝ
  have hST : ∀ g, S (T g) = g := fun g => by
    change restrictEuclideanAt p a hL (Rd.indicatorExtendLp hQ subset_rfl
      (LpToLpRestrictCLM _ ℂ ℂ volume p _ (extendEuclideanAt p a hL g))) = g
    rw [restrictEuclideanAt_eq_of_indicatorLp_eq a hL
      (Rd.indicatorLp_indicatorExtendLp_restrict hQ _), restrictEuclideanAt_extendEuclideanAt]
  have hTS : ∀ G, T (S G) = G := fun G => by
    change LpToLpRestrictCLM _ ℂ ℂ volume p _ (extendEuclideanAt p a hL
      (restrictEuclideanAt p a hL (Rd.indicatorExtendLp hQ subset_rfl G))) = G
    rw [(Rd.LpToLpRestrictCLM_eq_iff_indicatorLp_eq hQ).2
      (indicatorLp_extendEuclideanAt_restrictEuclideanAt a hL _)]
    exact Rd.LpToLpRestrictCLM_indicatorExtendLp hQ G
  constructor
  · intro hG
    refine ApproximationScheme.MemApprox.map S (fun n x hx => ?_) hG
    obtain ⟨g, hg, rfl⟩ := (ApproximationScheme.mem_map _).1 hx
    exact (hST g).symm ▸ hg
  · intro hG
    have h := ApproximationScheme.MemApprox.map T (ApproximationScheme.mem_map_of_mem' T)
      (show (cubeSplineScheme p d r).MemApprox s q (S G) from hG)
    rw [hTS] at h
    exact h

end Cube

namespace Rd

open Cube

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Restrictions of spline space elements -/

/-- **Restrictions of the tensor spline space of a cube have finite intrinsic quasi-norm**: let
`Q = a + L [0, 1]^d`, `Ω ⊆ Q` measurable, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 ≤ s < r - 1 + 1/p`. If `G ∈ L_p(Q)` lies in the approximation space `A^s_q` of the tensor
splines of order `r` on `Q` and `f ∈ L_p(ℝ^d)` agrees with `G` on `Ω`, then
`N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`: the cube theorem with the
Euclidean modulus (`Cube.memApprox_cubeSplineScheme_restrictEuclidean_iff`), moved to `Q` along
the inverse affine map (`Rd.exists_modNormOn_compAffineLp_le`), and `N_Ω ≤ N_Q`
(`Rd.modNormOn_mono_of_subset`). -/
theorem modNormOn_lt_top_of_memApprox_cubeSplineSchemeAt (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : MeasurableSet Ω) (hΩQ : Ω ⊆ euclideanCubeAt a L) {r : ℕ} (hr : 1 ≤ r) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 ≤ s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    {G : Lp ℂ p (volume.restrict (euclideanCubeAt a L))}
    (hG : (cubeSplineSchemeAt p a hL r).MemApprox s q G)
    {f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (hfG : indicatorLp hΩ (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
      indicatorLp hΩ f) : modNormOn hΩ r s q f < ∞ := by
  set hQ := measurableSet_euclideanCubeAt a L
  set g := restrictEuclideanAt p a hL (indicatorExtendLp hQ subset_rfl G)
  have h1 : modNormOn (measurableSet_euclideanCube d) r s q (extendEuclidean p d g) < ∞ := by
    rw [← memApprox_cubeSplineScheme_restrictEuclidean_iff hr hp hq hs hsr,
      restrictEuclidean_extendEuclidean]
    exact (memApprox_cubeSplineSchemeAt_iff a hL G).1 hG
  have hpre := preimage_affine_inv_euclideanCube a hL
  have hBQ : MeasurableSet ((fun y => -(L⁻¹ • a) + L⁻¹ • y) ⁻¹' euclideanCube d) := by
    rw [hpre]
    exact hQ
  obtain ⟨C, hC, hle⟩ := exists_modNormOn_compAffineLp_le (μ := volume) (p := p) (-(L⁻¹ • a))
    (inv_pos.2 hL) (measurableSet_euclideanCube d) hBQ r hs hq
  have h2 : modNormOn hQ r s q (extendEuclideanAt p a hL g) < ∞ := by
    rw [← modNormOn_congr_set hBQ hQ hpre.eventuallyEq]
    exact (hle _).trans_lt (ENNReal.mul_lt_top hC.lt_top h1)
  have h3 : indicatorLp hΩ (extendEuclideanAt p a hL g) = indicatorLp hΩ f :=
    (indicatorLp_eq_of_subset hΩ hQ hΩQ
      (indicatorLp_extendEuclideanAt_restrictEuclideanAt a hL _)).trans hfG
  rw [← modNormOn_congr hΩ h3]
  exact (modNormOn_mono_of_subset hΩ hQ hΩQ r s q _).trans_lt h2

/-! ### Functions of finite intrinsic quasi-norm as restrictions -/

namespace HasBesovExtension

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {hΩ : MeasurableSet Ω}

/-- **Functions of finite intrinsic quasi-norm are restrictions of the tensor spline space, with
a bound**: let `Ω` have the extension property, `Ω ⊆ Q = a + L [0, 1]^d`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `r ≥ 1` and `0 < s < r - 1 + 1/p`. Then there is `C < ∞` such that every `f` with
`N_Ω(f) < ∞` agrees on `Ω` with some `G ∈ L_p(Q)` with `‖G‖^dy_{A^s_q} ≤ C N_Ω(f)` in the
approximation space of the tensor splines of order `r` on `Q`. The extension `F` of `f` to
`ℝ^d`, with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C₁ N_Ω(f)`, has `N_Q(F)` at most this
quasi-norm (`Rd.modNormOn_le_modNorm_of_indicatorLp`); its transport `F ∘ A`, `A x = a + L x`, to
`[0, 1]^d` has Euclidean intrinsic quasi-norm at most `C₃ N_Q(F)`
(`Rd.exists_modNormOn_compAffineLp_le`); Jackson's direction on the unit cube with constant `C₂`
(`Cube.exists_approxNormDyadic_restrictEuclidean_le`) and the transport `T` back to `Q`
(`ApproximationScheme.approxNormDyadic_map_le`) give `C = ‖T‖ C₂ C₃ C₁`. -/
theorem exists_cubeSplineAt_le (h : HasBesovExtension hΩ) (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) (hΩQ : Ω ⊆ euclideanCubeAt a L) {r : ℕ}
    (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s)
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))),
      modNormOn hΩ r s q f < ∞ → ∃ G : Lp ℂ p (volume.restrict (euclideanCubeAt a L)),
        indicatorLp hΩ (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
            indicatorLp hΩ f ∧
          (cubeSplineSchemeAt p a hL r).approxNormDyadic s q G ≤ C * modNormOn hΩ r s q f := by
  set hQ := measurableSet_euclideanCubeAt a L
  have hpre := preimage_affine_euclideanCubeAt a hL
  have hAQ : MeasurableSet ((fun x => a + L • x) ⁻¹' euclideanCubeAt a L) := by
    rw [hpre]
    exact measurableSet_euclideanCube d
  obtain ⟨C₁, hC₁, hext⟩ := h p hp r s hs (lt_of_lt_splineRange hsr) q hq
  obtain ⟨C₂, hC₂, hjack⟩ := exists_approxNormDyadic_restrictEuclidean_le (d := d) hr hp hs.le hq
  obtain ⟨C₃, hC₃, haff⟩ := exists_modNormOn_compAffineLp_le (μ := volume) (p := p) a hL hQ hAQ r
    hs.le hq
  set T : Lp ℂ p (cubeVol d) →L[ℝ] Lp ℂ p (volume.restrict (euclideanCubeAt a L)) :=
    (LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p (euclideanCubeAt a L) ∘L
      extendEuclideanAt p a hL).restrictScalars ℝ
  refine ⟨‖T‖ₑ * (C₂ * (C₃ * C₁)),
    ENNReal.mul_ne_top enorm_ne_top (ENNReal.mul_ne_top hC₂ (ENNReal.mul_ne_top hC₃ hC₁)),
    fun f hf => ?_⟩
  obtain ⟨F, hFf, hF⟩ := hext f hf
  refine ⟨T (restrictEuclideanAt p a hL F), ?_, ?_⟩
  · have hQF : indicatorLp hQ
        (indicatorExtendLp hQ subset_rfl (T (restrictEuclideanAt p a hL F))) = indicatorLp hQ F :=
      (indicatorLp_indicatorExtendLp_restrict hQ _).trans
        (indicatorLp_extendEuclideanAt_restrictEuclideanAt a hL F)
    exact (indicatorLp_eq_of_subset hΩ hQ hΩQ hQF).trans hFf
  · have hE : modNormOn (measurableSet_euclideanCube d) r s q (compAffineLp a hL F) ≤
        C₃ * modNormOn hQ r s q F := by
      rw [modNormOn_congr_set (measurableSet_euclideanCube d) hAQ hpre.symm.eventuallyEq]
      exact haff F
    calc (cubeSplineSchemeAt p a hL r).approxNormDyadic s q (T (restrictEuclideanAt p a hL F))
        ≤ ‖T‖ₑ * (cubeSplineScheme p d r).approxNormDyadic s q (restrictEuclideanAt p a hL F) :=
          ApproximationScheme.approxNormDyadic_map_le T (ApproximationScheme.mem_map_of_mem' T) _
      _ ≤ ‖T‖ₑ * (C₂ * (C₃ *
            (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)))) := by
          refine mul_le_mul' le_rfl ((hjack (compAffineLp a hL F)).trans
            (mul_le_mul' le_rfl (hE.trans (mul_le_mul' le_rfl ?_))))
          exact modNormOn_le_modNorm_of_indicatorLp hQ r s q rfl
      _ ≤ ‖T‖ₑ * (C₂ * (C₃ * (C₁ * modNormOn hΩ r s q f))) := by gcongr
      _ = ‖T‖ₑ * (C₂ * (C₃ * C₁)) * modNormOn hΩ r s q f := by ring

/-- **Splines on domains through restriction**: let `Ω` have the extension property,
`Ω ⊆ Q = a + L [0, 1]^d`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 < s < r - 1 + 1/p`. Then
`f ∈ L_p(ℝ^d)` agrees on `Ω` with an element of the approximation space `A^s_q` of the tensor
splines of order `r` on `Q` iff
`N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
(`Rd.modNormOn_lt_top_of_memApprox_cubeSplineSchemeAt`,
`Rd.HasBesovExtension.exists_cubeSplineAt_le`). -/
theorem exists_memApprox_cubeSplineSchemeAt_iff (h : HasBesovExtension hΩ) (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) (hΩQ : Ω ⊆ euclideanCubeAt a L) {r : ℕ}
    (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s)
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    (f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (∃ G : Lp ℂ p (volume.restrict (euclideanCubeAt a L)),
        indicatorLp hΩ (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
          indicatorLp hΩ f ∧ (cubeSplineSchemeAt p a hL r).MemApprox s q G) ↔
      modNormOn hΩ r s q f < ∞ := by
  constructor
  · rintro ⟨G, hGf, hG⟩
    exact modNormOn_lt_top_of_memApprox_cubeSplineSchemeAt hp hL hΩ hΩQ hr hq hs.le hsr hG hGf
  · intro hf
    obtain ⟨C, hC, hle⟩ := h.exists_cubeSplineAt_le hp hL hΩQ hr hq hs hsr
    obtain ⟨G, hGf, hG⟩ := hle f hf
    exact ⟨G, hGf, (ApproximationScheme.memApprox_iff_approxNormDyadic_lt_top hq hs.le).2
      (hG.trans_lt (ENNReal.mul_lt_top hC.lt_top hf))⟩

/-- **The same with an intrinsic modulus of every order `r' > s`**: under the hypotheses of
`Rd.HasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff`, `f` agrees on `Ω` with an
element of the approximation space `A^s_q` of the tensor splines of order `r` on `Q` iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_{r'}(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`, since on a set with the
extension property the order of the differences does not matter
(`Rd.HasBesovExtension.modNormOn_order_le_of_hasBesovExtension`). -/
theorem exists_memApprox_cubeSplineSchemeAt_iff_of_order (h : HasBesovExtension hΩ)
    (hp : p ≠ ∞) {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L)
    (hΩQ : Ω ⊆ euclideanCubeAt a L) {r r' : ℕ} (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hs : 0 < s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) (hsr' : s < r')
    (f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (∃ G : Lp ℂ p (volume.restrict (euclideanCubeAt a L)),
        indicatorLp hΩ (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
          indicatorLp hΩ f ∧ (cubeSplineSchemeAt p a hL r).MemApprox s q G) ↔
      modNormOn hΩ r' s q f < ∞ := by
  rw [h.exists_memApprox_cubeSplineSchemeAt_iff hp hL hΩQ hr hq hs hsr f]
  have hsr₀ := lt_of_lt_splineRange hsr
  obtain ⟨C, hC, hle⟩ := h.modNormOn_order_le_of_hasBesovExtension hp hs hsr₀ hsr' hq
  obtain ⟨C', hC', hle'⟩ := h.modNormOn_order_le_of_hasBesovExtension hp hs hsr' hsr₀ hq
  exact ⟨fun hf => (hle f hf).trans_lt (ENNReal.mul_lt_top hC.lt_top hf),
    fun hf => (hle' f hf).trans_lt (ENNReal.mul_lt_top hC'.lt_top hf)⟩

/-- **Spline blocks on domains**: let `Ω` have the extension property, `Ω ⊆ Q = a + L [0, 1]^d`,
`1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 < s < r - 1 + 1/p`. Then
`N_Ω(f) = ‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞` iff `f` agrees on `Ω` with
the sum `G = ∑_k b_k` in `L_p(Q)` of tensor splines `b_k` of order `r` and level `k` on `Q` with
`‖(2^(ks) ‖b_k‖_{L_p(Q)})_k‖_{ℓ_q} < ∞` (DeVore–Popov, Theorem 5.1, the norm `N_3`): the block
decomposition of the approximation space
(`ApproximationScheme.memApprox_iff_blockDecompNorm_lt_top`) and
`Rd.HasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff`. -/
theorem exists_cubeSplineBlocksAt_iff (h : HasBesovExtension hΩ) (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) (hΩQ : Ω ⊆ euclideanCubeAt a L) {r : ℕ}
    (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s)
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    (f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (∃ (b : ℕ → Lp ℂ p (volume.restrict (euclideanCubeAt a L)))
        (G : Lp ℂ p (volume.restrict (euclideanCubeAt a L))),
        (∀ k, b k ∈ cubeSplineSchemeAt p a hL r (2 ^ k)) ∧ HasSum b G ∧
        lqNorm q (fun k => dyadicWeight s k * ‖b k‖ₑ) < ∞ ∧
        indicatorLp hΩ (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
          indicatorLp hΩ f) ↔ modNormOn hΩ r s q f < ∞ := by
  rw [← h.exists_memApprox_cubeSplineSchemeAt_iff hp hL hΩQ hr hq hs hsr f]
  constructor
  · rintro ⟨b, G, hb, hbG, hlq, hGf⟩
    exact ⟨G, hGf, (ApproximationScheme.memApprox_iff_blockDecompNorm_lt_top hs hq).2
      ((ApproximationScheme.blockDecompNorm_le_of_hasSum hb hbG).trans_lt hlq)⟩
  · rintro ⟨G, hGf, hG⟩
    have hlt := (ApproximationScheme.memApprox_iff_blockDecompNorm_lt_top hs hq).1 hG
    simp only [ApproximationScheme.blockDecompNorm, iInf_lt_iff] at hlt
    obtain ⟨b, hb, hbG, hlq⟩ := hlt
    exact ⟨b, G, hb, hbG, hlq, hGf⟩

end HasBesovExtension

/-! ### Bounded Lipschitz domains -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain (EuclideanSpace ℝ (Fin d)))

/-- **Splines on bounded Lipschitz domains through restriction**: let `Ω` be a bounded Lipschitz
domain in a cube `Q = a + L [0, 1]^d`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 < s < r - 1 + 1/p`. Then `f ∈ L_p(ℝ^d)` agrees on `Ω` with an element of the approximation
space `A^s_q` of the tensor splines of order `r` on `Q` iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
(`Rd.BoundedLipschitzDomain.hasBesovExtension`,
`Rd.HasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff`). -/
theorem exists_memApprox_cubeSplineSchemeAt_iff (hp : p ≠ ∞) {a : EuclideanSpace ℝ (Fin d)}
    {L : ℝ} (hL : 0 < L) (hΩQ : Ω.carrier ⊆ euclideanCubeAt a L) {r : ℕ} (hr : 1 ≤ r) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    (f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (∃ G : Lp ℂ p (volume.restrict (euclideanCubeAt a L)),
        indicatorLp Ω.measurableSet
            (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
          indicatorLp Ω.measurableSet f ∧ (cubeSplineSchemeAt p a hL r).MemApprox s q G) ↔
      modNormOn Ω.measurableSet r s q f < ∞ :=
  Ω.hasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff hp hL hΩQ hr hq hs hsr f

/-- **The same with an intrinsic modulus of every order `r' > s`**: under the hypotheses of
`Rd.BoundedLipschitzDomain.exists_memApprox_cubeSplineSchemeAt_iff`, `f` agrees on `Ω` with an
element of the approximation space `A^s_q` of the tensor splines of order `r` on `Q` iff
`‖f‖_{L_p(Ω)} + ‖(2^(ks) ω_{r'}(f, 2^(-k), Ω)_p)_k‖_{ℓ_q} < ∞`
(`Rd.BoundedLipschitzDomain.hasBesovExtension`,
`Rd.HasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff_of_order`). -/
theorem exists_memApprox_cubeSplineSchemeAt_iff_of_order (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) (hΩQ : Ω.carrier ⊆ euclideanCubeAt a L)
    {r r' : ℕ} (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s)
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) (hsr' : s < r')
    (f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (∃ G : Lp ℂ p (volume.restrict (euclideanCubeAt a L)),
        indicatorLp Ω.measurableSet
            (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
          indicatorLp Ω.measurableSet f ∧ (cubeSplineSchemeAt p a hL r).MemApprox s q G) ↔
      modNormOn Ω.measurableSet r' s q f < ∞ :=
  Ω.hasBesovExtension.exists_memApprox_cubeSplineSchemeAt_iff_of_order hp hL hΩQ hr hq hs hsr
    hsr' f

/-- **The restrictions of `B^s_{p,q}(ℝ^d)` and of the tensor spline space of the cube to `Ω`
agree**: under the hypotheses of
`Rd.BoundedLipschitzDomain.exists_memApprox_cubeSplineSchemeAt_iff`, `f` agrees on `Ω` with an
element of the approximation space `A^s_q` of the tensor splines of order `r` on `Q` iff it
agrees on `Ω` with some `F ∈ L_p(ℝ^d)` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
(`Rd.BoundedLipschitzDomain.exists_besov_extension_iff_modulusOn`). -/
theorem exists_memApprox_cubeSplineSchemeAt_iff_exists_besov (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) (hΩQ : Ω.carrier ⊆ euclideanCubeAt a L)
    {r : ℕ} (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s)
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    (f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (∃ G : Lp ℂ p (volume.restrict (euclideanCubeAt a L)),
        indicatorLp Ω.measurableSet
            (indicatorExtendLp (measurableSet_euclideanCubeAt a L) subset_rfl G) =
          indicatorLp Ω.measurableSet f ∧ (cubeSplineSchemeAt p a hL r).MemApprox s q G) ↔
      ∃ F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))),
        indicatorLp Ω.measurableSet F = indicatorLp Ω.measurableSet f ∧
          ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) < ∞ := by
  rw [Ω.exists_besov_extension_iff_modulusOn hp hs (lt_of_lt_splineRange hsr) hq f]
  exact Ω.exists_memApprox_cubeSplineSchemeAt_iff hp hL hΩQ hr hq hs hsr f

end BoundedLipschitzDomain

/-! ### The restricted splines on `Ω` -/

variable (p) in
/-- **Tensor splines of a cube restricted to `Ω ⊆ Q = a + L [0, 1]^d`**: the image of the scheme
of the tensor splines of order `r` on `Q` (`Cube.cubeSplineSchemeAt`) under the restriction
`L_p(Q) → L_p(Ω)` (`Rd.restrictSubsetLp`). Its error at complexity `2^k` is
`inf_S ‖f - S‖_{L_p(Ω)}` over the restrictions `S` of the splines of level `k`. -/
noncomputable def domainSplineScheme {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω) (hΩQ : Ω ⊆ euclideanCubeAt a L)
    (r : ℕ) : ApproximationScheme (Lp ℂ p (volume.restrict Ω)) :=
  (cubeSplineSchemeAt p a hL r).map
    ((restrictSubsetLp (μ := volume) (p := p) hΩ hΩQ).restrictScalars ℝ).toLinearMap

namespace HasBesovExtension

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {hΩ : MeasurableSet Ω}

/-- **One-sided intrinsic Jackson theorem for the restricted splines**: let `Ω` have the
extension property, `Ω ⊆ Q = a + L [0, 1]^d`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 < s < r - 1 + 1/p`. Then there is `C < ∞` with `‖f|_Ω‖^dy_{A^s_q} ≤ C N_Ω(f)` for every `f` with
`N_Ω(f) < ∞`, in the approximation space of the tensor splines of `Q` restricted to `Ω`
(`Rd.domainSplineScheme`), that is
`‖f‖_{L_p(Ω)} + ‖(2^(ks) inf_S ‖f - S‖_{L_p(Ω)})_k‖_{ℓ_q} ≤ C N_Ω(f)` with `S` over the
restrictions of the splines of level `k`. The restriction maps the spline `G` of
`Rd.HasBesovExtension.exists_cubeSplineAt_le` to `f|_Ω`, and restriction is functorial
(`ApproximationScheme.approxNormDyadic_map_le`). The converse would follow from a Bernstein
inequality for the restricted splines in `L_p(Ω)`, whose constants degenerate on cells that meet
`Ω` in thin pieces, or from an approximation-preserving extension for `Rd.restrictSubsetLp`
(`ApproximationScheme.memApprox_iff_exists_restrict`). -/
theorem exists_approxNormDyadic_domainSplineScheme_le (h : HasBesovExtension hΩ) (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) (hΩQ : Ω ⊆ euclideanCubeAt a L) {r : ℕ}
    (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s)
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))),
      modNormOn hΩ r s q f < ∞ →
        (domainSplineScheme p hL hΩ hΩQ r).approxNormDyadic s q
            (LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p Ω f) ≤
          C * modNormOn hΩ r s q f := by
  obtain ⟨C, hC, hle⟩ := h.exists_cubeSplineAt_le hp hL hΩQ hr hq hs hsr
  set T := (restrictSubsetLp (μ := volume) (p := p) hΩ hΩQ).restrictScalars ℝ
  refine ⟨‖T‖ₑ * C, ENNReal.mul_ne_top enorm_ne_top hC, fun f hf => ?_⟩
  obtain ⟨G, hGf, hG⟩ := hle f hf
  have hTG : T G = LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p Ω f :=
    restrictSubsetLp_eq_of_indicatorLp_eq hΩ (measurableSet_euclideanCubeAt a L) hΩQ hGf
  rw [← hTG, mul_assoc]
  exact (ApproximationScheme.approxNormDyadic_map_le T (ApproximationScheme.mem_map_of_mem' T)
    G).trans (mul_le_mul' le_rfl hG)

/-- **The restriction lies in the approximation space of the restricted splines**: under the
hypotheses of `Rd.HasBesovExtension.exists_approxNormDyadic_domainSplineScheme_le`, every `f` with
`N_Ω(f) < ∞` has `f|_Ω ∈ A^s_q` of the tensor splines of `Q` restricted to `Ω`. -/
theorem memApprox_domainSplineScheme (h : HasBesovExtension hΩ) (hp : p ≠ ∞)
    {a : EuclideanSpace ℝ (Fin d)} {L : ℝ} (hL : 0 < L) (hΩQ : Ω ⊆ euclideanCubeAt a L) {r : ℕ}
    (hr : 1 ≤ r) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s)
    (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    {f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d)))} (hf : modNormOn hΩ r s q f < ∞) :
    (domainSplineScheme p hL hΩ hΩQ r).MemApprox s q
      (LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℂ ℂ volume p Ω f) := by
  obtain ⟨C, hC, hle⟩ := h.exists_approxNormDyadic_domainSplineScheme_le hp hL hΩQ hr hq hs hsr
  exact (ApproximationScheme.memApprox_iff_approxNormDyadic_lt_top hq hs.le).2
    ((hle f hf).trans_lt (ENNReal.mul_lt_top hC.lt_top hf))

end HasBesovExtension

end Rd

namespace Cube

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The unit cube -/

/-- **Tensor splines describe the restrictions of `B^s_{p,q}(ℝ^d)` to the unit cube**: for
`1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and `0 < s < r - 1 + 1/p`, `g ∈ L_p([0, 1]^d)` lies in the
approximation space `A^s_q` of the tensor splines of order `r` iff `g = F|_{[0, 1]^d}` for some
`F ∈ L_p(ℝ^d)` with `‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. The tensor splines describe
the Euclidean intrinsic quasi-norm on the unit cube
(`Cube.memApprox_cubeSplineScheme_restrictEuclidean_iff`), and the closed unit cube has the
extension property (`Rd.BesovDomain.closedUnitCube`). -/
theorem memApprox_cubeSplineScheme_iff_exists_besov {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ}
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hs : 0 < s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal)
    (g : Lp ℂ p (cubeVol d)) :
    (cubeSplineScheme p d r).MemApprox s q g ↔
      ∃ F : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin d))), restrictEuclidean p d F = g ∧
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * Rd.lpModulus p r F k) < ∞ := by
  constructor
  · intro hg
    have h1 : Rd.modNormOn (measurableSet_euclideanCube d) r s q (extendEuclidean p d g) < ∞ := by
      rw [← memApprox_cubeSplineScheme_restrictEuclidean_iff hr hp hq hs.le hsr,
        restrictEuclidean_extendEuclidean]
      exact hg
    obtain ⟨C, hC, hext⟩ := Rd.BesovDomain.hasBesovExtension (euclideanCube d) p hp r s hs
      (lt_of_lt_splineRange hsr) q hq
    obtain ⟨F, hFf, hF⟩ := hext (extendEuclidean p d g) h1
    exact ⟨F, (restrictEuclidean_eq_of_indicatorLp_eq hFf).trans
      (restrictEuclidean_extendEuclidean g), hF.trans_lt (ENNReal.mul_lt_top hC.lt_top h1)⟩
  · rintro ⟨F, rfl, hF⟩
    exact (memApprox_cubeSplineScheme_restrictEuclidean_iff hr hp hq hs.le hsr F).2
      ((Rd.modNormOn_le_modNorm_of_indicatorLp _ r s q rfl).trans_lt hF)

end Cube
