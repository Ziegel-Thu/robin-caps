import RobinCaps.Cap.EntranceL2Hemi
import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.SliceAC
import RobinCaps.Sobolev.RadialSlice
import RobinCaps.ThinDomain.Slice
import RobinCaps.Cap.PoincareOne
import RobinCaps.ThinDomain.Reflect

/-!
# The entrance trace of a weak `H¹` function on the hemispherical cap body (general `m`)

This file discharges the interface `RobinCaps.Cap.CapEntranceL2` of `RobinCaps/Cap/LowerWeak.lean`
for the hemispherical cap `Cap.hemisphere m` in **arbitrary** transverse dimension `m ≥ 1`,

`C = {(s,z) | -1 < s < 0, ‖z‖ < √(1-(s+1)²)} ⊆ ℝ × EuclideanSpace ℝ (Fin m)`.

## Relation to `RobinCaps.Cap.EntranceL2Hemi` (the `m = 1` template)

The one-dimensional trace step (the axial fundamental theorem of calculus,
`RobinCaps.Cap.ae_entranceVal_sq_le_el`) and the bookkeeping identities relating the mass/energy
forms `massP`/`dirichletP` to the axial slice energies (`RobinCaps.Cap.axEnergy_el`,
`RobinCaps.Cap.axMass_el`, `massP_eq_rep_el`, `dirichletP_eq_rep_el`) are **already stated for a
general `Cap m`** in the template file and are reused here verbatim, together with the geometric
constant `RobinCaps.Cap.rad_el = 1/√2` and its elementary properties.

The only genuinely new content is the **general-dimension geometry** (Section 1, a verbatim
generalisation of the template's `EuclideanSpace ℝ (Fin 1)` computations to `Fin m`), the
**general-dimension singular weight** and its integrability on the entrance ball via polar
coordinates (Section 2), and the **transverse short-slice bound** (Section 3): the analogue of
the template's two-region slicing argument, which in the one-dimensional transverse case reduces
to comparing `u` at a point of the (interval) transverse section to the mean over the *whole*
central segment, but which for `m ≥ 2` transverse dimensions would need a multi-dimensional
(direction-uniform) Poincaré/trace-type bound on the transverse ball. The radial ACL of
`RobinCaps.Sobolev.RadialSlice` only controls `u` along the *single* ray through the point in
question, so it cannot by itself produce a bound independent of that ray's direction; making the
comparison direction-independent needs either a genuine multi-dimensional Poincaré inequality on
a Euclidean ball (Riesz-potential estimates, not present in the imported files) or an
axis-by-axis "staircase" ACL argument that is not currently available as a general lemma. This
one analytic ingredient is therefore isolated as the explicit hypothesis
`RobinCaps.Cap.TransverseShortSliceBound_elg`, and the main theorem
`RobinCaps.Cap.capEntranceL2_hemi_elg` is proved from it; every other step is proved outright.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Transverse

noncomputable section

/-! ## 1. The geometry of the hemispherical cap in general transverse dimension -/

variable {m : ℕ}

@[simp] theorem hemi_K_elg (m : ℕ) : (hemisphere m).K = 1 := rfl

theorem hemi_theta_elg (m : ℕ) (s : ℝ) :
    (hemisphere m).θ s = Real.sqrt (1 - (s + 1) ^ 2) := rfl

/-- The radial slice of the hemispherical body at radius `t`, in general dimension. -/
theorem radialSlice_hemi_elg (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) :
    radialSlice (hemisphere m) t = Ioo (-1) (Real.sqrt (1 - t ^ 2) - 1) := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  have hs1 : Real.sqrt (1 - t ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  have hs0 : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hpos
  ext s
  simp only [mem_radialSlice, mem_Ioo, hemi_K_elg, hemi_theta_elg]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨by linarith, ?_⟩
    have hts : t ^ 2 < 1 - (s + 1) ^ 2 := (Real.lt_sqrt ht0).1 h3
    have : (s + 1) ^ 2 < 1 - t ^ 2 := by linarith
    have := (Real.lt_sqrt (by linarith : (0:ℝ) ≤ s + 1)).2 this
    linarith
  · rintro ⟨h1, h2⟩
    have hs2 : s < 0 := by linarith
    refine ⟨⟨by linarith, hs2⟩, ?_⟩
    have h3 : s + 1 < Real.sqrt (1 - t ^ 2) := by linarith
    have h4 : (s + 1) ^ 2 < 1 - t ^ 2 := (Real.lt_sqrt (by linarith : (0:ℝ) ≤ s + 1)).1 h3
    exact (Real.lt_sqrt ht0).2 (by linarith)

/-- **The length of the axial slice of the hemispherical body**, in general dimension:
`exitTime + K = √(1-‖z‖²)`. -/
theorem exitTime_hemi_elg (m : ℕ) {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1) :
    exitTime (hemisphere m) z + 1 = Real.sqrt (1 - ‖z‖ ^ 2) := by
  have h1 : radialSlice (hemisphere m) ‖z‖ = Ioo (-1) (exitTime (hemisphere m) z) := by
    have := radialSlice_eq (hemisphere m) ‖z‖
    rwa [hemi_K_elg, ← exitTime] at this
  have h2 := radialSlice_hemi_elg m (norm_nonneg z) hz
  have hlt1 : (-1 : ℝ) < exitTime (hemisphere m) z := by
    have := (exitTime_mem (hemisphere m) hz).1
    rwa [hemi_K_elg] at this
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hs0 : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.2 hpos
  have := Ioo_right_eq_el hlt1 (by linarith : (-1:ℝ) < Real.sqrt (1 - ‖z‖ ^ 2) - 1)
    (h1 ▸ h2)
  linarith

/-- On the far-left part of the hemispherical body the transverse section is wider than
`rad_el`, in general dimension. -/
theorem rad_lt_theta_elg (m : ℕ) {s : ℝ} (h1 : -1 < s) (h2 : s + 1 < rad_el) :
    rad_el < (hemisphere m).θ s := by
  rw [hemi_theta_elg]
  refine (Real.lt_sqrt rad_pos_el.le).2 ?_
  have h3 : (s + 1) ^ 2 < rad_el ^ 2 := by
    have h0 : 0 < s + 1 := by linarith
    nlinarith
  rw [rad_sq_el] at h3 ⊢
  linarith

/-- The threshold `rad_el` is self-dual under `ℓ ↦ √(1-‖z‖²)`: `‖z‖ ≤ rad_el ↔ rad_el ≤ ℓ(z)`. -/
theorem norm_le_rad_iff_elg {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1) :
    ‖z‖ ≤ rad_el ↔ rad_el ≤ Real.sqrt (1 - ‖z‖ ^ 2) := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  constructor
  · intro h
    have h3 : rad_el ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [rad_sq_el, rad_pos_el]
    have := Real.sqrt_le_sqrt h3
    rwa [Real.sqrt_sq rad_pos_el.le] at this
  · intro h
    have hpos : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
    have h3 : rad_el ^ 2 ≤ 1 - ‖z‖ ^ 2 := by
      have hle := pow_le_pow_left₀ rad_pos_el.le h 2
      rwa [Real.sq_sqrt hpos] at hle
    have h4 : ‖z‖ ^ 2 ≤ rad_el ^ 2 := by nlinarith [rad_sq_el]
    have h5 : Real.sqrt (‖z‖ ^ 2) ≤ Real.sqrt (rad_el ^ 2) := Real.sqrt_le_sqrt h4
    rwa [Real.sqrt_sq hz0, Real.sqrt_sq rad_pos_el.le] at h5

/-! ## 2. The singular weight `1/ℓ` is integrable on the entrance ball, general dimension -/

/-- The singular weight `z ↦ 2/ℓ(z)` on `EuclideanSpace ℝ (Fin m)`, cut off to the outer
annulus `‖z‖ > 1/√2`. -/
def wt_elg (m : ℕ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  if rad_el < ‖z‖ then 2 / Real.sqrt (1 - ‖z‖ ^ 2) else 0

theorem wt_nonneg_elg (m : ℕ) (z : EuclideanSpace ℝ (Fin m)) : 0 ≤ wt_elg m z := by
  rw [wt_elg]; split
  · positivity
  · exact le_rfl

theorem measurable_wt_elg (m : ℕ) : Measurable (wt_elg m) := by
  refine Measurable.ite (measurableSet_lt measurable_const measurable_norm) ?_ measurable_const
  fun_prop

/-- The weight agrees with twice the arcsine density evaluated at the norm. -/
theorem wt_le_elg (m : ℕ) (z : EuclideanSpace ℝ (Fin m)) : wt_elg m z ≤ 2 * arcDen_el ‖z‖ := by
  rw [wt_elg, arcDen_el]
  split
  · rw [mul_one_div]
  · positivity

/-- **The singular weight is integrable on the entrance ball**, general dimension, via
polar coordinates: the angular part contributes the finite constant `sphereMeasure m univ`, and
the radial part is dominated by `2 * arcDen_el`, whose interval integrability was already
established (`RobinCaps.Cap.intervalIntegrable_arcDen_el`). -/
theorem integrableOn_wt_elg (m : ℕ) (hm : 1 ≤ m) :
    IntegrableOn (wt_elg m) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  haveI := RobinCaps.ThinDomain.nontrivial_euclidean hm
  refine ⟨(measurable_wt_elg m).aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (wt_nonneg_elg m))]
  have harcmeas : Measurable arcDen_el := by unfold arcDen_el; fun_prop
  have hmajmeas : Measurable (fun z : EuclideanSpace ℝ (Fin m) => (2 : ℝ) * arcDen_el ‖z‖) := by
    exact measurable_const.mul (harcmeas.comp measurable_norm)
  have hmono : (∫⁻ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ENNReal.ofReal (wt_elg m z))
      ≤ ∫⁻ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ENNReal.ofReal (2 * arcDen_el ‖z‖) :=
    lintegral_mono fun z => ENNReal.ofReal_le_ofReal (wt_le_elg m z)
  refine lt_of_le_of_lt hmono ?_
  rw [lintegral_ball_polar m hm 1 _ (hmajmeas.ennreal_ofReal)]
  have hinner : ∀ r : ℝ, 0 < r →
      (∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          ENNReal.ofReal (2 * arcDen_el ‖r • (w : EuclideanSpace ℝ (Fin m))‖)
          ∂(sphereMeasure m))
        = ENNReal.ofReal (2 * arcDen_el r) * sphereMeasure m Set.univ := by
    intro r hr
    have hpt : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        ENNReal.ofReal (2 * arcDen_el ‖r • (w : EuclideanSpace ℝ (Fin m))‖)
          = ENNReal.ofReal (2 * arcDen_el r) := by
      intro w
      rw [RobinCaps.ThinDomain.norm_smul_sphere hr w]
    simp [hpt]
  have hcongr : (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (m - 1)) *
        ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          ENNReal.ofReal (2 * arcDen_el ‖r • (w : EuclideanSpace ℝ (Fin m))‖)
          ∂(sphereMeasure m))
      = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (m - 1)) *
          (ENNReal.ofReal (2 * arcDen_el r) * sphereMeasure m Set.univ) := by
    refine lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => ?_)
    dsimp only
    rw [hinner r hr.1]
  rw [hcongr]
  have hrpow : ∀ᵐ r ∂(volume.restrict (Ioo (0:ℝ) 1)), ENNReal.ofReal (r ^ (m - 1)) ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hr.1.le hr.2.le)
  have hstep1 : (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (m - 1)) *
        (ENNReal.ofReal (2 * arcDen_el r) * sphereMeasure m Set.univ))
      ≤ ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * arcDen_el r) * sphereMeasure m Set.univ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hrpow] with r hr
    calc ENNReal.ofReal (r ^ (m - 1)) * (ENNReal.ofReal (2 * arcDen_el r) * sphereMeasure m Set.univ)
        ≤ 1 * (ENNReal.ofReal (2 * arcDen_el r) * sphereMeasure m Set.univ) :=
          mul_le_mul_right' hr _
      _ = ENNReal.ofReal (2 * arcDen_el r) * sphereMeasure m Set.univ := one_mul _
  refine lt_of_le_of_lt hstep1 ?_
  have hmeas2 : Measurable (fun r : ℝ => ENNReal.ofReal (2 * arcDen_el r)) :=
    (measurable_const.mul harcmeas).ennreal_ofReal
  rw [lintegral_mul_const _ hmeas2]
  have hfin1 : (sphereMeasure m Set.univ) < ⊤ := measure_lt_top _ _
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hmaj : IntervalIntegrable (fun y => 2 * arcDen_el y) volume (-1) 1 :=
    intervalIntegrable_arcDen_el.const_mul 2
  have hI : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo (-1 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).1 hmaj
  have hI' : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo (0 : ℝ) 1) volume :=
    hI.mono_set (Set.Ioo_subset_Ioo (by norm_num) le_rfl)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] fun y => 2 * arcDen_el y :=
    ae_of_all _ fun y => by simp only [Pi.zero_apply]; linarith [arcDen_nonneg_el y]
  have hfin2 : (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * arcDen_el r)) < ⊤ := by
    have := (hasFiniteIntegral_iff_ofReal hnonneg).1 hI'.2
    simpa using this
  exact ENNReal.mul_lt_top hfin2 hfin1

/-! ## 3. The transverse short-slice bound (isolated hypothesis) and the assembly

The one remaining analytic ingredient, discussed in the module docstring: a uniform bound,
controlled only by the mass and Dirichlet energy of `u`, on the total contribution of the
singular weight against the axial mass over the region `‖z‖ > 1/√2` of the entrance ball (the
region where the axial slice through `z` is short). In transverse dimension `1` this is exactly
what the template's `ae_axMass_le_el`/`ae_entranceVal_sq_le_maj_el` combination provides, via a
POINTWISE (in `z`) bound by a quantity depending only on the axial level; the proof there uses
that the one-dimensional transverse section has only two directions, so that "averaging over the
whole central segment" automatically covers both of them. In dimension `m ≥ 2` the radial ACL
(`RobinCaps.Sobolev.Weak.radialSlice_ae`) only connects two points lying on a *common* ray issued
from the origin, so it cannot by itself yield a bound uniform over all directions of the unit
sphere; supplying one would need either a genuine multi-dimensional Poincaré/trace inequality on
a Euclidean ball (a Riesz-potential estimate, not present in the imported files) or an
axis-by-axis "staircase" ACL argument that is not currently available as a general lemma. -/

/-- **The transverse short-slice bound.**  A uniform bound on
`∫_{B_m(1)} wt(z) · axMass(z) dz`, the total contribution of the singular weight against the
axial mass, by the mass and Dirichlet energy of `u` alone. This is the genuinely new analytic
content that the general-dimension entrance-trace bound needs beyond what is already available
(general-`m`) in `RobinCaps.Cap.EntranceL2Hemi`; see the section docstring above for why it is
isolated here rather than proved. -/
structure TransverseShortSliceBound_elg (m : ℕ) (C0 : ℝ) : Prop where
  /-- The constant is nonnegative. -/
  C0_nonneg : 0 ≤ C0
  /-- The weighted axial mass is integrable on the entrance ball. -/
  integrableOn : ∀ u : H1P (hemisphere m).body,
    IntegrableOn (fun z => wt_elg m z * axMass_el (hemisphere m) u z)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume
  /-- **The bound itself.** -/
  bound : ∀ u : H1P (hemisphere m).body,
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        wt_elg m z * axMass_el (hemisphere m) u z)
      ≤ C0 * (massP u + dirichletP u)

variable {m : ℕ}

/-- The pointwise majorant of the squared entrance trace on the entrance ball, general
dimension. -/
def majFun_elg (m : ℕ) (u : H1P (hemisphere m).body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  2 * Real.sqrt 2 * axMass_el (hemisphere m) u z + 2 * axEnergy_el (hemisphere m) u z
    + wt_elg m z * axMass_el (hemisphere m) u z

theorem majFun_nonneg_elg (m : ℕ) (u : H1P (hemisphere m).body)
    (z : EuclideanSpace ℝ (Fin m)) : 0 ≤ majFun_elg m u z := by
  have h1 := axMass_nonneg_el (hemisphere m) u z
  have h2 := axEnergy_nonneg_el (hemisphere m) u z
  have h3 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h4 := wt_nonneg_elg m z
  rw [majFun_elg]; positivity

/-- **The pointwise bound on the entrance ball**, general dimension. Purely algebraic given
`ae_entranceVal_sq_le_el` (already general in `m`): in the outer region `‖z‖ > 1/√2` the weight
`wt_elg` agrees exactly with `2/ℓ(z)`, so the mass term matches with equality; in the inner
region `‖z‖ ≤ 1/√2` the weight `1/ℓ(z)` is bounded by `√2` via `two_div_le_el`. -/
theorem ae_entranceVal_sq_le_maj_elg (m : ℕ) (u : H1P (hemisphere m).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      entranceVal (hemisphere m) u z ^ 2 ≤ majFun_elg m u z := by
  filter_upwards [ae_entranceVal_sq_le_el (hemisphere m) u, ae_restrict_mem measurableSet_ball]
    with z h1 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  have hℓ : exitTime (hemisphere m) z + (hemisphere m).K = Real.sqrt (1 - ‖z‖ ^ 2) := by
    rw [hemi_K_elg]; exact exitTime_hemi_elg m hznorm
  have hℓpos : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.2 hpos
  have hℓle : Real.sqrt (1 - ‖z‖ ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; nlinarith
  rw [hℓ] at h1
  have hA0 : 0 ≤ axEnergy_el (hemisphere m) u z := axEnergy_nonneg_el _ _ _
  have hM0 : 0 ≤ axMass_el (hemisphere m) u z := axMass_nonneg_el _ _ _
  have hdir : 2 * Real.sqrt (1 - ‖z‖ ^ 2) * axEnergy_el (hemisphere m) u z
      ≤ 2 * axEnergy_el (hemisphere m) u z := by nlinarith
  rw [majFun_elg]
  by_cases hcase : rad_el < ‖z‖
  · have hwt : wt_elg m z = 2 / Real.sqrt (1 - ‖z‖ ^ 2) := by rw [wt_elg, if_pos hcase]
    rw [hwt]
    have hsq0 : 0 ≤ 2 * Real.sqrt 2 * axMass_el (hemisphere m) u z := by
      have : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      positivity
    linarith
  · push_neg at hcase
    have hwt : wt_elg m z = 0 := by rw [wt_elg, if_neg (not_lt.2 hcase)]
    have hshort : rad_el ≤ Real.sqrt (1 - ‖z‖ ^ 2) := (norm_le_rad_iff_elg hznorm).1 hcase
    have hstep : 2 / Real.sqrt (1 - ‖z‖ ^ 2) * axMass_el (hemisphere m) u z
        ≤ 2 * Real.sqrt 2 * axMass_el (hemisphere m) u z :=
      mul_le_mul_of_nonneg_right (two_div_le_el hshort) hM0
    rw [hwt, zero_mul]
    linarith

/-- Integrability of the majorant, given the transverse short-slice bound hypothesis. -/
theorem integrableOn_majFun_elg (m : ℕ) (_hm : 1 ≤ m) {C0 : ℝ} (H : TransverseShortSliceBound_elg m C0)
    (u : H1P (hemisphere m).body) :
    IntegrableOn (majFun_elg m u) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  refine Integrable.add (Integrable.add ?_ ?_) (H.integrableOn u)
  · exact (integrable_axMass_el (hemisphere m) u).integrableOn.const_mul _
  · exact (integrable_axEnergy_el (hemisphere m) u).integrableOn.const_mul _

/-- **The trace bound**, given the transverse short-slice bound hypothesis. -/
theorem integral_majFun_le_elg (m : ℕ) (_hm : 1 ≤ m) {C0 : ℝ} (H : TransverseShortSliceBound_elg m C0)
    (u : H1P (hemisphere m).body) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, majFun_elg m u z)
      ≤ (2 * Real.sqrt 2 + C0) * (massP u + dirichletP u) := by
  set M : ℝ := ∫ p in (hemisphere m).body, repFun (hemisphere m) u p ^ 2 with hM
  set A : ℝ := ∫ p in (hemisphere m).body, repGx (hemisphere m) u p ^ 2 with hA
  set B : ℝ := ∫ p in (hemisphere m).body, ‖repGz_el (hemisphere m) u p‖ ^ 2 with hB
  have hM0 : 0 ≤ M := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hA0 : 0 ≤ A := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hmass : massP u = M := massP_eq_rep_el _ u
  have hdir : dirichletP u = A + B := dirichletP_eq_rep_el _ u
  have hax : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axMass_el (hemisphere m) u z) ≤ M := by
    rw [hM, ← integral_axMass_el (hemisphere m) u]
    exact setIntegral_le_integral (integrable_axMass_el _ u)
      (Eventually.of_forall fun z => axMass_nonneg_el _ _ _)
  have hae : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axEnergy_el (hemisphere m) u z) ≤ A := by
    rw [hA, ← integral_axEnergy_el (hemisphere m) u]
    exact setIntegral_le_integral (integrable_axEnergy_el _ u)
      (Eventually.of_forall fun z => axEnergy_nonneg_el _ _ _)
  have hwt := H.bound u
  have hI1 : IntegrableOn (fun z => 2 * Real.sqrt 2 * axMass_el (hemisphere m) u z)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume :=
    (integrable_axMass_el (hemisphere m) u).integrableOn.const_mul (2 * Real.sqrt 2)
  have hI2 : IntegrableOn (fun z => 2 * axEnergy_el (hemisphere m) u z)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume :=
    (integrable_axEnergy_el (hemisphere m) u).integrableOn.const_mul 2
  have hI3 := H.integrableOn u
  have hI12 : IntegrableOn (fun z => 2 * Real.sqrt 2 * axMass_el (hemisphere m) u z
      + 2 * axEnergy_el (hemisphere m) u z)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := hI1.add hI2
  have hsplit : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, majFun_elg m u z)
      = 2 * Real.sqrt 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            axMass_el (hemisphere m) u z)
        + 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axEnergy_el (hemisphere m) u z)
        + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            wt_elg m z * axMass_el (hemisphere m) u z := by
    simp only [majFun_elg]
    rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul, integral_const_mul]
  have hs2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [hsplit, hmass, hdir]
  have hterm1 : 2 * Real.sqrt 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      axMass_el (hemisphere m) u z) ≤ 2 * Real.sqrt 2 * M :=
    mul_le_mul_of_nonneg_left hax (by positivity)
  have hterm2 : 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      axEnergy_el (hemisphere m) u z) ≤ 2 * A :=
    mul_le_mul_of_nonneg_left hae (by norm_num)
  have hC0 := H.C0_nonneg
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_body' _) fun p _ => by positivity
  have hwt' : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      wt_elg m z * axMass_el (hemisphere m) u z) ≤ C0 * (M + (A + B)) := by
    rwa [hmass, hdir] at hwt
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hAbound : 2 * A ≤ 2 * Real.sqrt 2 * (A + B) := by nlinarith [hsqrt1, hA0, hB0]
  have hexpand : (2 * Real.sqrt 2 + C0) * (M + (A + B))
      = 2 * Real.sqrt 2 * M + 2 * Real.sqrt 2 * (A + B) + C0 * (M + (A + B)) := by ring
  rw [hexpand]
  linarith [hterm1, hterm2, hwt', hAbound]

/-! ## 4. The main theorem -/

/-- **The entrance trace of a weak `H¹` function on the hemispherical cap body is square
integrable**, in every transverse dimension `m ≥ 1`, given the transverse short-slice bound
hypothesis `TransverseShortSliceBound_elg m`. This discharges the interface
`RobinCaps.Cap.CapEntranceL2` for `Cap.hemisphere m`. -/
theorem capEntranceL2_hemi_elg (m : ℕ) (hm : 1 ≤ m) {C0 : ℝ} (H : TransverseShortSliceBound_elg m C0) :
    ∃ C₁ : ℝ, CapEntranceL2 (Cap.hemisphere m) C₁ := by
  refine ⟨2 * Real.sqrt 2 + C0, ⟨by positivity [Real.sqrt_nonneg 2, H.C0_nonneg], fun u => ?_,
    fun u => ?_⟩⟩
  · have hmeas : AEStronglyMeasurable (entranceVal (hemisphere m) u)
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
      (measurable_entranceVal (hemisphere m) u).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    refine Integrable.mono' (integrableOn_majFun_elg m hm H u) (hmeas.pow 2) ?_
    filter_upwards [ae_entranceVal_sq_le_maj_elg m u] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  · have hmeas : AEStronglyMeasurable (entranceVal (hemisphere m) u)
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
      (measurable_entranceVal (hemisphere m) u).aestronglyMeasurable
    have hint : IntegrableOn (fun z => entranceVal (hemisphere m) u z ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
      refine Integrable.mono' (integrableOn_majFun_elg m hm H u) (hmeas.pow 2) ?_
      filter_upwards [ae_entranceVal_sq_le_maj_elg m u] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz
    have hstep : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        entranceVal (hemisphere m) u z ^ 2)
        ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, majFun_elg m u z :=
      integral_mono_ae hint (integrableOn_majFun_elg m hm H u) (ae_entranceVal_sq_le_maj_elg m u)
    exact hstep.trans (integral_majFun_le_elg m hm H u)

end

end Cap
end RobinCaps

