import RobinCaps.ThinDomain.TraceIneqStadium
import RobinCaps.ThinDomain.SphereSlicing
import RobinCaps.ThinDomain.VertRadIdent
import RobinCaps.Sobolev.RadialSlice

/-!
# The radial ACL interface of the stadium, from `Sobolev/RadialSlice.lean`

This file discharges the interface `RobinCaps.ThinDomain.ArcTraceSt` of
`RobinCaps/ThinDomain/TraceIneqStadium.lean` — hence `RadialACL` and, with
`RobinCaps/ThinDomain/VertRadIdent.lean`, the hypothesis of `traceIneqOne_hemisphere`.

## The chart

`capChart_br c : ℝ² → ℝ × ℝ¹`, `x ↦ (c + x₀, x₁)`, is the affine measure preserving chart that
identifies the Euclidean plane with the product model `CapSpace 1` used by `H1P`, centred at the
cap centre `(c, 0)`.  Under it the open disk `capDisk_br c R` of radius `R` about `(c, 0)`
corresponds to `ball (0 : EuclideanSpace ℝ (Fin 2)) R`, and:

* `diskH1_br` transports an `H1P (thinDomain …)` to an element of `Weak.H1 (ball 0 R)`
  (the weak gradient is transported by pulling test functions back along the chart), with
  `mass_diskH1_le_br`, `dirichlet_diskH1_le_br` bounding its mass and Dirichlet energy by
  `massP u` and `dirichletP u`;
* `capGeom_centre_mem_br` shows that the hypothesis `CapGeomSt L R c e` forces `|c| = L/2 − R`,
  so that the disk really sits inside `Ω_R`.

## The angular parametrisation

`dirSt_br e s φ = (e cos φ, s sin φ)` and `sphDir_br` (its unit-circle version) give the
directions of the quarter-disk.  The key measure-theoretic fact is

* `map_sphDir_le_br`: the push-forward of Lebesgue measure on `(0, π/2)` along `sphDir_br` is
  at most `sphereMeasure 2`.  It is proved from the height-slicing identity
  `lintegral_sphere_slicing` of `ThinDomain/SphereSlicing.lean` with `m = 1`, the computation
  `sphereMeasure_one_singleton_br` of the two atoms of `σ₀`, and the substitution `t = cos φ`.

Its consequences (`ae_angle_of_ae_sphere_br`, `integral_angle_le_br`, `integrableOn_angle_br`,
`aestronglyMeasurable_angle_br`) turn every `σ₂`-a.e. statement of `RadialSlice.lean` into a
statement for a.e. angle `φ ∈ (0, π/2)`.

## The fields

`arcTrace_br L R u c e s φ = traceSphere R (u ∘ chart) (∇u ∘ chart) (dirSt_br e s φ)` and

* `radAC_br` — from `radialSlice_h1` with `ε = R/2`, the endpoint value being identified with
  `traceSphere` by `traceSphere_eq_const_add` and uniqueness of continuous representatives;
* `radIntegrable_br` — from `ae_integrableOn_slice`, translated by `R/2`;
* `energy_integrable_br`, `energy_le_br` — from `integral_ball_polar_symm` and
  `integrable_ball_angular`, splitting the ray at `R/2`;
* `aesm_arcTrace_br` — measurability of `traceSphere` in the direction
  (`stronglyMeasurable_traceSphere_br`, a parametric-integral argument), combined with
  `ae_radial_congr_br` (a.e. equality passes to a.e. radial slice) to replace the
  representatives of `u` by strongly measurable ones.

## Main results

* `arcTraceSt_br : ArcTraceSt L R u c e s (arcTrace_br L R u c e s)`;
* `vertRadIdent_br : VertRadIdent_br L R`;
* `radialACL_br : RadialACL L R u`;
* `traceIneqOne_hemisphere_br : TraceIneqOne (Cap.hemisphere 1) (Cap.hemisphere 1) L R`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter Module

open scoped ContDiff ENNReal Topology Pointwise

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse

set_option autoImplicit false

section Bridge

/-! ## 0. The chart identifying the plane with the product model -/

/-- `ℝ → EuclideanSpace ℝ (Fin 1)` as a continuous linear map. -/
def eptCLM_br : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (ept 1)

@[simp] theorem eptCLM_br_apply (t : ℝ) : eptCLM_br t = ept t := by
  simp [eptCLM_br, (ept_eq_smul t).symm]

theorem ept_smul_br (r t : ℝ) : ept (r * t) = r • ept t := by
  refine PiLp.ext fun j => ?_
  fin_cases j
  rfl

/-- The identification `ℝ² → ℝ × ℝ¹` as a continuous linear map. -/
def ofEuclidCLM_br : EuclideanSpace ℝ (Fin 2) →L[ℝ] CapSpace 1 :=
  (EuclideanSpace.proj (0 : Fin 2)).prod (eptCLM_br.comp (EuclideanSpace.proj (1 : Fin 2)))

@[simp] theorem ofEuclidCLM_br_apply (x : EuclideanSpace ℝ (Fin 2)) :
    ofEuclidCLM_br x = (x 0, ept (x 1)) := by
  simp [ofEuclidCLM_br]

theorem ofEuclid_one_eq_br (x : EuclideanSpace ℝ (Fin 2)) :
    ofEuclid 1 x = (x 0, ept (x 1)) := by
  refine Prod.ext rfl ?_
  ext i
  fin_cases i
  rfl

theorem ofEuclidCLM_br_eq (x : EuclideanSpace ℝ (Fin 2)) :
    ofEuclidCLM_br x = ofEuclid 1 x := by
  rw [ofEuclid_one_eq_br, ofEuclidCLM_br_apply]

/-- The identification `ℝ × ℝ¹ → ℝ²` as a continuous linear map. -/
def toEuclidCLM_br : CapSpace 1 →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 1))).smulRight
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    + ((EuclideanSpace.proj (0 : Fin 1)).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 1)))).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

theorem toEuclidCLM_br_eq (p : CapSpace 1) : toEuclidCLM_br p = toEuclid 1 p := by
  refine PiLp.ext fun j => ?_
  fin_cases j <;> simp [toEuclidCLM_br, toEuclid, EuclideanSpace.single_apply]


/-! ### The affine chart centred at a cap centre -/

/-- The centre `(c, 0)` of a cap, as a point of the product model. -/
def capCtr_br (c : ℝ) : CapSpace 1 := (c, 0)

/-- The chart `ℝ² → ℝ × ℝ¹`, `x ↦ (c + x₀, x₁)`. -/
def capChart_br (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : CapSpace 1 :=
  ofEuclidCLM_br x + capCtr_br c

/-- The inverse chart. -/
def capUnchart_br (c : ℝ) (p : CapSpace 1) : EuclideanSpace ℝ (Fin 2) :=
  toEuclidCLM_br (p - capCtr_br c)

@[simp] theorem capChart_br_apply (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    capChart_br c x = (c + x 0, ept (x 1)) := by
  simp [capChart_br, capCtr_br, add_comm]

theorem capUnchart_capChart_br (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    capUnchart_br c (capChart_br c x) = x := by
  rw [capUnchart_br, capChart_br, add_sub_cancel_right, toEuclidCLM_br_eq, ofEuclidCLM_br_eq,
    toEuclid_ofEuclid]

theorem capChart_capUnchart_br (c : ℝ) (p : CapSpace 1) :
    capChart_br c (capUnchart_br c p) = p := by
  rw [capChart_br, capUnchart_br, ofEuclidCLM_br_eq, toEuclidCLM_br_eq, ofEuclid_toEuclid,
    sub_add_cancel]

theorem continuous_capChart_br (c : ℝ) : Continuous (capChart_br c) :=
  ofEuclidCLM_br.continuous.add continuous_const

theorem continuous_capUnchart_br (c : ℝ) : Continuous (capUnchart_br c) :=
  toEuclidCLM_br.continuous.comp (continuous_id.sub continuous_const)

/-- The chart as a homeomorphism. -/
def capChartHomeo_br (c : ℝ) : EuclideanSpace ℝ (Fin 2) ≃ₜ CapSpace 1 where
  toFun := capChart_br c
  invFun := capUnchart_br c
  left_inv := capUnchart_capChart_br c
  right_inv := capChart_capUnchart_br c
  continuous_toFun := continuous_capChart_br c
  continuous_invFun := continuous_capUnchart_br c

/-- The chart as a measurable equivalence. -/
def capChartMEquiv_br (c : ℝ) : EuclideanSpace ℝ (Fin 2) ≃ᵐ CapSpace 1 :=
  (capChartHomeo_br c).toMeasurableEquiv

@[simp] theorem capChartMEquiv_br_apply (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    capChartMEquiv_br c x = capChart_br c x := rfl

theorem capChart_eq_comp_br (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    capChart_br c x = ofEuclid 1 (x + toEuclid 1 (capCtr_br c)) := by
  rw [capChart_br, ← ofEuclidCLM_br_eq, map_add, ofEuclidCLM_br_eq (toEuclid 1 (capCtr_br c)),
    ofEuclid_toEuclid]

theorem measurePreserving_capChart_br (c : ℝ) :
    MeasurePreserving (capChart_br c) volume volume := by
  have h1 : MeasurePreserving (ofEuclid 1) (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (volume : Measure (CapSpace 1)) := measurePreserving_ofEuclid 1
  have h2 : MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin 2) => x + toEuclid 1 (capCtr_br c)) volume volume :=
    measurePreserving_add_right volume (toEuclid 1 (capCtr_br c))
  have h3 := h1.comp h2
  have heq : (ofEuclid 1) ∘ (fun x : EuclideanSpace ℝ (Fin 2) =>
      x + toEuclid 1 (capCtr_br c)) = capChart_br c :=
    funext fun x => (capChart_eq_comp_br c x).symm
  rwa [heq] at h3

theorem measurableEmbedding_capChart_br (c : ℝ) : MeasurableEmbedding (capChart_br c) :=
  (capChartMEquiv_br c).measurableEmbedding

/-! ### The disk about a cap centre -/

theorem norm_sq_two_br (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]
  simp

/-- The open disk of radius `R` about the cap centre `(c, 0)`. -/
def capDisk_br (c R : ℝ) : Set (CapSpace 1) :=
  {p : CapSpace 1 | (p.1 - c) ^ 2 + ‖p.2‖ ^ 2 < R ^ 2}

theorem capChart_sq_br (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ((capChart_br c x).1 - c) ^ 2 + ‖(capChart_br c x).2‖ ^ 2 = ‖x‖ ^ 2 := by
  have h2 : ‖ept (x 1)‖ ^ 2 = x 1 ^ 2 := by rw [ept_norm, sq_abs]
  rw [capChart_br_apply]
  show (c + x 0 - c) ^ 2 + ‖ept (x 1)‖ ^ 2 = ‖x‖ ^ 2
  rw [h2, norm_sq_two_br]
  ring

theorem capChart_preimage_disk_br (c : ℝ) {R : ℝ} (hR : 0 < R) :
    capChart_br c ⁻¹' (capDisk_br c R) = ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
  ext x
  have hx := capChart_sq_br c x
  constructor
  · intro h
    have h' : ‖x‖ ^ 2 < R ^ 2 := hx ▸ h
    rw [mem_ball, dist_zero_right]
    nlinarith [norm_nonneg x, hR]
  · intro h
    rw [mem_ball, dist_zero_right] at h
    show ((capChart_br c x).1 - c) ^ 2 + ‖(capChart_br c x).2‖ ^ 2 < R ^ 2
    rw [hx]
    nlinarith [norm_nonneg x, hR]

theorem capDisk_eq_image_br (c : ℝ) {R : ℝ} (hR : 0 < R) :
    capDisk_br c R = capChart_br c '' ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
  rw [← capChart_preimage_disk_br c hR]
  exact ((capChartHomeo_br c).toEquiv.image_preimage _).symm

theorem isOpen_capDisk_br (c : ℝ) {R : ℝ} (hR : 0 < R) : IsOpen (capDisk_br c R) := by
  have : capDisk_br c R = capUnchart_br c ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    rw [← capChart_preimage_disk_br c hR]
    ext p
    simp only [mem_preimage, capChart_capUnchart_br]
  rw [this]
  exact isOpen_ball.preimage (continuous_capUnchart_br c)

theorem capDisk_subset_thinDomain_br {L R : ℝ} (hR : 0 < R) (hL : 2 * R < L) {c : ℝ}
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    capDisk_br c R ⊆ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R := by
  intro p hp
  rw [mem_thinDomain_hemisphere_iff hR hL]
  exact ⟨c, hc, hp⟩


/-! ## 1. Transporting an `H1P` element to a weak `H¹` element of the disk -/

section Transport

variable {L R : ℝ}

/-- The transported gradient: the pair `(∂ₓu, ∇_z u)` read as a vector of `ℝ²`. -/
def diskGrad_br (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  toEuclidCLM_br (u.gx (capChart_br c x), u.gz (capChart_br c x))

theorem diskGrad_eq_sum_br (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    diskGrad_br u c x = u.gx (capChart_br c x) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
      + u.gz (capChart_br c x) 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := rfl

@[simp] theorem diskGrad_apply_zero_br
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : diskGrad_br u c x 0 = u.gx (capChart_br c x) := by
  rw [diskGrad_br, toEuclidCLM_br_eq]; rfl

@[simp] theorem diskGrad_apply_one_br
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : diskGrad_br u c x 1 = u.gz (capChart_br c x) 0 := by
  rw [diskGrad_br, toEuclidCLM_br_eq]; rfl

theorem norm_diskGrad_sq_br (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖diskGrad_br u c x‖ ^ 2
      = u.gx (capChart_br c x) ^ 2 + ‖u.gz (capChart_br c x)‖ ^ 2 := by
  rw [diskGrad_br, toEuclidCLM_br_eq, norm_toEuclid_sq]

/-! ### The two reference directions -/

theorem toEuclidCLM_axial_br :
    toEuclidCLM_br ((1, 0) : CapSpace 1) = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
  rw [toEuclidCLM_br_eq]
  refine PiLp.ext fun j => ?_
  fin_cases j <;> simp [toEuclid, EuclideanSpace.single_apply]

theorem toEuclidCLM_trans_br :
    toEuclidCLM_br ((0, EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : CapSpace 1)
      = EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  rw [toEuclidCLM_br_eq]
  refine PiLp.ext fun j => ?_
  fin_cases j <;> simp [toEuclid, EuclideanSpace.single_apply]

/-! ### The change of variables for integrals over the disk -/

theorem setIntegral_disk_br (hR : 0 < R) (c : ℝ) (F : CapSpace 1 → ℝ) :
    (∫ p in capDisk_br c R, F p)
      = ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) R, F (capChart_br c x) := by
  have h := (measurePreserving_capChart_br c).setIntegral_preimage_emb
    (measurableEmbedding_capChart_br c) F (capDisk_br c R)
  rw [capChart_preimage_disk_br c hR] at h
  exact h.symm

/-! ### The transported test function -/

theorem contDiff_capUnchart_br (c : ℝ) : ContDiff ℝ ∞ (capUnchart_br c) :=
  toEuclidCLM_br.contDiff.comp (contDiff_id.sub contDiff_const)

theorem fderiv_comp_capUnchart_br {Φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (c : ℝ) (p : CapSpace 1) (v : CapSpace 1) :
    fderiv ℝ (fun q => Φ (capUnchart_br c q)) p v
      = fderiv ℝ Φ (capUnchart_br c p) (toEuclidCLM_br v) := by
  have hid : HasFDerivAt (fun q : CapSpace 1 => q - capCtr_br c)
      (ContinuousLinearMap.id ℝ (CapSpace 1)) p := (hasFDerivAt_id p).sub_const _
  have h1 : HasFDerivAt (capUnchart_br c) toEuclidCLM_br p := by
    have h : HasFDerivAt (fun q : CapSpace 1 => toEuclidCLM_br (q - capCtr_br c))
        (toEuclidCLM_br.comp (ContinuousLinearMap.id ℝ (CapSpace 1))) p :=
      toEuclidCLM_br.hasFDerivAt.comp p hid
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have h2 : HasFDerivAt Φ (fderiv ℝ Φ (capUnchart_br c p)) (capUnchart_br c p) :=
    (hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h3 : HasFDerivAt (fun q => Φ (capUnchart_br c q))
      ((fderiv ℝ Φ (capUnchart_br c p)).comp toEuclidCLM_br) p := h2.comp p h1
  rw [h3.fderiv]
  rfl


/-- **The weak gradient transports along the chart.** -/
theorem hasWeakGrad_disk_br (hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hsub : capDisk_br c R ⊆ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) :
    Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin 2)) R)
      (fun x => u.toFun (capChart_br c x)) (diskGrad_br u c) := by
  intro Φ hΦ hΦc hΦs i
  have hφ : ContDiff ℝ ∞ (fun q => Φ (capUnchart_br c q)) :=
    hΦ.comp (contDiff_capUnchart_br c)
  have hφc : HasCompactSupport (fun q => Φ (capUnchart_br c q)) :=
    hΦc.comp_homeomorph (capChartHomeo_br c).symm
  have hφs : tsupport (fun q => Φ (capUnchart_br c q)) ⊆ capDisk_br c R := by
    have hsupp : Function.support (fun q => Φ (capUnchart_br c q))
        = capUnchart_br c ⁻¹' Function.support Φ :=
      Function.support_comp_eq_preimage Φ (capUnchart_br c)
    have hcl : capUnchart_br c ⁻¹' closure (Function.support Φ)
        = closure (capUnchart_br c ⁻¹' Function.support Φ) :=
      ((capChartHomeo_br c).symm).preimage_closure _
    rw [tsupport, hsupp, ← hcl]
    intro q hq
    have hb : capUnchart_br c q ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R := hΦs hq
    rw [← capChart_preimage_disk_br c hR, mem_preimage, capChart_capUnchart_br] at hb
    exact hb
  obtain ⟨e1, f1⟩ := (u.hasWeakGrad.mono hsub) _ hφ hφc hφs
  rw [setIntegral_disk_br hR c, setIntegral_disk_br hR c] at e1
  have f1' := f1 (0 : Fin 1)
  rw [setIntegral_disk_br hR c, setIntegral_disk_br hR c] at f1'
  have hchart : ∀ x : EuclideanSpace ℝ (Fin 2),
      capUnchart_br c (capChart_br c x) = x := capUnchart_capChart_br c
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · refine Eq.trans ?_ (Eq.trans e1 ?_)
    · refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
      show u.toFun (capChart_br c x) * fderiv ℝ Φ x (EuclideanSpace.single (0 : Fin 2) 1)
        = u.toFun (capChart_br c x)
          * fderiv ℝ (fun q => Φ (capUnchart_br c q)) (capChart_br c x) ((1, 0) : CapSpace 1)
      rw [fderiv_comp_capUnchart_br hΦ c (capChart_br c x) ((1, 0) : CapSpace 1), hchart,
        toEuclidCLM_axial_br]
    · congr 1
      refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
      show u.gx (capChart_br c x) * Φ (capUnchart_br c (capChart_br c x))
        = diskGrad_br u c x 0 * Φ x
      rw [diskGrad_apply_zero_br, hchart]
  · refine Eq.trans ?_ (Eq.trans f1' ?_)
    · refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
      show u.toFun (capChart_br c x) * fderiv ℝ Φ x (EuclideanSpace.single (1 : Fin 2) 1)
        = u.toFun (capChart_br c x)
          * fderiv ℝ (fun q => Φ (capUnchart_br c q)) (capChart_br c x)
              ((0, EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : CapSpace 1)
      rw [fderiv_comp_capUnchart_br hΦ c (capChart_br c x)
        ((0, EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : CapSpace 1), hchart,
        toEuclidCLM_trans_br]
    · congr 1
      refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
      show u.gz (capChart_br c x) 0 * Φ (capUnchart_br c (capChart_br c x))
        = diskGrad_br u c x 1 * Φ x
      rw [diskGrad_apply_one_br, hchart]


/-! ### The transported element of `Weak.H1 (ball 0 R)` -/

theorem measurePreserving_chart_restrict_br (hR : 0 < R) (c : ℝ) :
    MeasurePreserving (capChart_br c)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R))
      (volume.restrict (capDisk_br c R)) := by
  have h := (measurePreserving_capChart_br c).restrict_preimage_emb
    (measurableEmbedding_capChart_br c) (capDisk_br c R)
  rwa [capChart_preimage_disk_br c hR] at h

theorem memLp_disk_toFun_br (hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hsub : capDisk_br c R ⊆ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) :
    MemLp (fun x => u.toFun (capChart_br c x)) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) :=
  (u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)).comp_measurePreserving
    (measurePreserving_chart_restrict_br hR c)

theorem memLp_disk_gx_br (hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hsub : capDisk_br c R ⊆ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) :
    MemLp (fun x => u.gx (capChart_br c x)) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) :=
  (u.gx_memL2.mono_measure (Measure.restrict_mono hsub le_rfl)).comp_measurePreserving
    (measurePreserving_chart_restrict_br hR c)

theorem memLp_disk_gz_br (hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hsub : capDisk_br c R ⊆ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) :
    MemLp (fun x => u.gz (capChart_br c x)) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) :=
  (u.gz_memL2.mono_measure (Measure.restrict_mono hsub le_rfl)).comp_measurePreserving
    (measurePreserving_chart_restrict_br hR c)

theorem memLp_diskGrad_br (hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hsub : capDisk_br c R ⊆ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) :
    MemLp (diskGrad_br u c) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) := by
  have hgx := memLp_disk_gx_br hR u hsub
  have hgz0 : MemLp (fun x => u.gz (capChart_br c x) 0) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) := by
    have h := (EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).comp_memLp' (memLp_disk_gz_br hR u hsub)
    simpa [Function.comp_def] using h
  have h1 : MemLp (fun x => u.gx (capChart_br c x)
      • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) := by
    have h := ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).comp_memLp' hgx
    simpa [Function.comp_def] using h
  have h2 : MemLp (fun x => u.gz (capChart_br c x) 0
      • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) := by
    have h := ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))).comp_memLp' hgz0
    simpa [Function.comp_def] using h
  have heq : diskGrad_br u c = fun x => u.gx (capChart_br c x)
      • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
      + u.gz (capChart_br c x) 0 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) :=
    funext (diskGrad_eq_sum_br u c)
  rw [heq]
  exact h1.add h2

/-- **Deliverable 1.**  The element of `Weak.H1 (ball 0 R) ⊆ ℝ²` obtained by restricting `u`
to the disk of radius `R` about the cap centre `(c, 0)` and reading it in the chart. -/
def diskH1_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin 2)) R) where
  toFun := fun x => u.toFun (capChart_br c x)
  grad := diskGrad_br u c
  memL2 := memLp_disk_toFun_br hR u (capDisk_subset_thinDomain_br hR hL hc)
  grad_memL2 := memLp_diskGrad_br hR u (capDisk_subset_thinDomain_br hR hL hc)
  hasWeakGrad := hasWeakGrad_disk_br hR u (capDisk_subset_thinDomain_br hR hL hc)

@[simp] theorem diskH1_toFun_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) (x : EuclideanSpace ℝ (Fin 2)) :
    (diskH1_br hR hL u c hc).toFun x = u.toFun (capChart_br c x) := rfl

@[simp] theorem diskH1_grad_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    (diskH1_br hR hL u c hc).grad = diskGrad_br u c := rfl

/-! ### The mass and Dirichlet energies of the transported element -/

theorem integrableOn_sq_thin_br
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    IntegrableOn (fun p => u.toFun p ^ 2)
      (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) volume := by
  refine (u.memL2.integrable_mul u.memL2).congr (Eventually.of_forall fun p => ?_)
  show u.toFun p * u.toFun p = u.toFun p ^ 2
  rw [pow_two]

theorem integrableOn_gradSq_thin_br
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    IntegrableOn (fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2)
      (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) volume := by
  have h1 : IntegrableOn (fun p => u.gx p ^ 2)
      (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) volume := by
    refine (u.gx_memL2.integrable_mul u.gx_memL2).congr (Eventually.of_forall fun p => ?_)
    show u.gx p * u.gx p = u.gx p ^ 2
    rw [pow_two]
  have h2 : IntegrableOn (fun p => ‖u.gz p‖ ^ 2)
      (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) volume := by
    refine (u.gz_memL2.norm.integrable_mul u.gz_memL2.norm).congr
      (Eventually.of_forall fun p => ?_)
    show ‖u.gz p‖ * ‖u.gz p‖ = ‖u.gz p‖ ^ 2
    rw [pow_two]
  exact h1.add h2

theorem mass_diskH1_le_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    Weak.mass (diskH1_br hR hL u c hc) ≤ massP u := by
  have hsub := capDisk_subset_thinDomain_br hR hL hc
  have hstep : Weak.mass (diskH1_br hR hL u c hc) = ∫ p in capDisk_br c R, u.toFun p ^ 2 := by
    rw [Weak.mass, setIntegral_disk_br hR c]
    rfl
  rw [hstep, massP]
  refine setIntegral_mono_set (integrableOn_sq_thin_br u) ?_ (HasSubset.Subset.eventuallyLE hsub)
  filter_upwards with p using sq_nonneg _

theorem dirichlet_diskH1_le_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    Weak.dirichlet (diskH1_br hR hL u c hc) ≤ dirichletP u := by
  have hsub := capDisk_subset_thinDomain_br hR hL hc
  have hstep : Weak.dirichlet (diskH1_br hR hL u c hc)
      = ∫ p in capDisk_br c R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2) := by
    rw [Weak.dirichlet, setIntegral_disk_br hR c]
    refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
    exact norm_diskGrad_sq_br u c x
  rw [hstep, dirichletP]
  refine setIntegral_mono_set (integrableOn_gradSq_thin_br u) ?_
    (HasSubset.Subset.eventuallyLE hsub)
  filter_upwards with p using by positivity


end Transport



/-! ## 2. The angular parametrisation of the unit circle -/

section Angle

theorem ept_injective_br : Function.Injective ept := fun _ _ h => eptEquiv.injective h

/-- The sphere measure of a one-point set of `S⁰ ⊆ ℝ¹` is `1`. -/
theorem sphereMeasure_one_singleton_br (v : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    sphereMeasure 1 {v} = 1 := by
  have hv : ‖(v : EuclideanSpace ℝ (Fin 1))‖ = 1 := mem_sphere_zero_iff_norm.1 v.2
  obtain ⟨a, hveq, ha2⟩ : ∃ a : ℝ, (v : EuclideanSpace ℝ (Fin 1)) = ept a ∧ a ^ 2 = 1 := by
    refine ⟨(v : EuclideanSpace ℝ (Fin 1)) 0, ?_, ?_⟩
    · refine PiLp.ext fun j => ?_
      fin_cases j
      rfl
    · have h := norm_sq_one_dim (v : EuclideanSpace ℝ (Fin 1))
      rw [hv] at h
      simpa using h.symm
  have hsmul : (Ioo (0 : ℝ) 1) •
        (Subtype.val '' ({v} : Set (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)))
      = ept '' ((fun r : ℝ => r * a) '' Ioo (0 : ℝ) 1) := by
    rw [Set.image_singleton]
    ext y
    constructor
    · rintro ⟨r, hr, z, hz, rfl⟩
      rw [Set.mem_singleton_iff] at hz
      refine ⟨r * a, ⟨r, hr, rfl⟩, ?_⟩
      rw [ept_smul_br, ← hveq, hz]
    · rintro ⟨t, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨r, hr, (v : EuclideanSpace ℝ (Fin 1)), rfl, ?_⟩
      show r • (v : EuclideanSpace ℝ (Fin 1)) = ept (r * a)
      rw [hveq, ept_smul_br]
  have hcases : a = 1 ∨ a = -1 := by
    have hz : (a - 1) * (a + 1) = 0 := by nlinarith [ha2]
    rcases mul_eq_zero.1 hz with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hmeas : volume ((fun r : ℝ => r * a) '' Ioo (0 : ℝ) 1) = 1 := by
    rcases hcases with rfl | rfl
    · have himg : (fun r : ℝ => r * 1) '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
        ext y; simp
      rw [himg, Real.volume_Ioo]
      norm_num
    · have himg : (fun r : ℝ => r * (-1)) '' Ioo (0 : ℝ) 1 = Ioo (-1 : ℝ) 0 := by
        ext y
        constructor
        · rintro ⟨r, hr, rfl⟩
          exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
        · intro hy
          exact ⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by ring⟩
      rw [himg, Real.volume_Ioo]
      norm_num
  have himg : volume (ept '' ((fun r : ℝ => r * a) '' Ioo (0 : ℝ) 1))
      = volume ((fun r : ℝ => r * a) '' Ioo (0 : ℝ) 1) := by
    have hemb : MeasurableEmbedding ept := eptEquiv.measurableEmbedding
    rw [← measurePreserving_ept.measure_preimage_emb hemb
      (ept '' ((fun r : ℝ => r * a) '' Ioo (0 : ℝ) 1))]
    congr 1
    exact Set.preimage_image_eq _ ept_injective_br
  rw [Measure.toSphere_apply' _ (measurableSet_singleton v), hsmul, himg, hmeas, finrank_eq 1]
  norm_num



/-! ### The angular parametrisation -/

/-- The point of the unit circle at polar angle `θ`, with transverse sign `s`. -/
def angPt_br (s θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  toEuclid 1 (Real.cos θ, ept (Real.sin θ * s))

/-- The unit direction of angle `φ`, axial sign `e` and transverse sign `s`. -/
def dirSt_br (e s φ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  toEuclid 1 (e * Real.cos φ, ept (s * Real.sin φ))

/-- The polar angle attached to `φ ∈ (0, π/2)` by the axial sign `e`. -/
def angSt_br (e φ : ℝ) : ℝ := Real.pi / 2 - e * (Real.pi / 2 - φ)

theorem angSt_one_br (φ : ℝ) : angSt_br 1 φ = φ := by rw [angSt_br]; ring

theorem angSt_neg_one_br (φ : ℝ) : angSt_br (-1) φ = Real.pi - φ := by rw [angSt_br]; ring

theorem sign_cases_br {e : ℝ} (he : e ^ 2 = 1) : e = 1 ∨ e = -1 := by
  have hz : (e - 1) * (e + 1) = 0 := by nlinarith [he]
  rcases mul_eq_zero.1 hz with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem angPt_angSt_br {e : ℝ} (he : e ^ 2 = 1) (s φ : ℝ) :
    angPt_br s (angSt_br e φ) = dirSt_br e s φ := by
  rcases sign_cases_br he with rfl | rfl
  · rw [angSt_one_br, angPt_br, dirSt_br]
    congr 2
    · ring
    · rw [mul_comm]
  · rw [angSt_neg_one_br, angPt_br, dirSt_br, Real.cos_pi_sub, Real.sin_pi_sub]
    congr 2
    · ring
    · rw [mul_comm]

theorem angSt_mem_br {e : ℝ} (he : e ^ 2 = 1) {φ : ℝ} (hφ : φ ∈ Ioo 0 (Real.pi / 2)) :
    angSt_br e φ ∈ Ioo 0 Real.pi := by
  have hpi := Real.pi_pos
  rcases sign_cases_br he with rfl | rfl
  · rw [angSt_one_br]; exact ⟨hφ.1, by linarith [hφ.2]⟩
  · rw [angSt_neg_one_br]; exact ⟨by linarith [hφ.2], by linarith [hφ.1]⟩

@[simp] theorem dirSt_apply_zero_br (e s φ : ℝ) : dirSt_br e s φ 0 = e * Real.cos φ := rfl

@[simp] theorem dirSt_apply_one_br (e s φ : ℝ) : dirSt_br e s φ 1 = s * Real.sin φ := rfl

theorem norm_dirSt_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (φ : ℝ) :
    ‖dirSt_br e s φ‖ = 1 := by
  have hpy := Real.sin_sq_add_cos_sq φ
  have hsq : ‖dirSt_br e s φ‖ ^ 2 = 1 := by
    rw [dirSt_br, norm_toEuclid_sq, ept_norm, sq_abs]
    nlinarith [he, hs, hpy]
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at this

theorem measurable_dirSt_br (e s : ℝ) : Measurable (dirSt_br e s) :=
  (measurable_toEuclid 1).comp (Measurable.prodMk
    (measurable_const.mul Real.continuous_cos.measurable)
    ((eptEquiv.measurable).comp (measurable_const.mul Real.continuous_sin.measurable)))

theorem measurable_angPt_br (s : ℝ) : Measurable (angPt_br s) :=
  (measurable_toEuclid 1).comp (Measurable.prodMk
    Real.continuous_cos.measurable
    ((eptEquiv.measurable).comp (Real.continuous_sin.measurable.mul measurable_const)))



/-- The direction of angle `φ` as a point of the unit circle. -/
def sphDir_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (φ : ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  ⟨dirSt_br e s φ, mem_sphere_zero_iff_norm.2 (norm_dirSt_br he hs φ)⟩

@[simp] theorem sphDir_coe_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (φ : ℝ) :
    (sphDir_br he hs φ : EuclideanSpace ℝ (Fin 2)) = dirSt_br e s φ := rfl

theorem measurable_sphDir_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1) :
    Measurable (sphDir_br he hs) := (measurable_dirSt_br e s).subtype_mk

/-- `x ↦ a - x` as an equivalence of `ℝ`. -/
def subLeftEquiv_br (a : ℝ) : ℝ ≃ ℝ where
  toFun := fun x => a - x
  invFun := fun x => a - x
  left_inv := fun x => by simp
  right_inv := fun x => by simp

/-- `x ↦ a - x` as a measurable equivalence of `ℝ`. -/
def subLeftMEquiv_br (a : ℝ) : ℝ ≃ᵐ ℝ where
  toEquiv := subLeftEquiv_br a
  measurable_toFun := measurable_const.sub measurable_id
  measurable_invFun := measurable_const.sub measurable_id

theorem measurableEmbedding_subLeft_br (a : ℝ) :
    MeasurableEmbedding (fun x : ℝ => a - x) := (subLeftMEquiv_br a).measurableEmbedding

theorem lintegral_reflect_br (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ φ in Ioo 0 (Real.pi / 2), G (Real.pi - φ))
      = ∫⁻ φ in Ioo (Real.pi / 2) Real.pi, G φ := by
  have hpre : (fun x : ℝ => Real.pi - x) ⁻¹' Ioo (Real.pi / 2) Real.pi
      = Ioo 0 (Real.pi / 2) := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hmp : MeasurePreserving (fun x : ℝ => Real.pi - x)
      (volume.restrict (Ioo 0 (Real.pi / 2)))
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)) := by
    have h := (Measure.measurePreserving_sub_left (volume : Measure ℝ) Real.pi).restrict_preimage_emb
      (measurableEmbedding_subLeft_br Real.pi) (Ioo (Real.pi / 2) Real.pi)
    rwa [hpre] at h
  exact hmp.lintegral_comp hG

/-- **The angular parametrisation dominates the sphere measure.**  The push-forward of Lebesgue
measure on `(0, π/2)` along `φ ↦ (e cos φ, s sin φ)` is at most the surface measure of the unit
circle. -/
theorem map_sphDir_le_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1) :
    Measure.map (sphDir_br he hs) (volume.restrict (Ioo 0 (Real.pi / 2)))
      ≤ sphereMeasure 2 := by
  classical
  refine Measure.le_iff.2 (fun A hA => ?_)
  have hsph : MeasurableSet (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.measurableSet
  have hA'meas : MeasurableSet
      ((Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → _) '' A) :=
    (MeasurableEmbedding.subtype_coe hsph).measurableSet_image' hA
  set g : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    ((Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → _) '' A).indicator 1 with hgdef
  have hgmeas : Measurable g := measurable_one.indicator hA'meas
  have hgval : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      g (w : EuclideanSpace ℝ (Fin 2))
        = A.indicator (1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ≥0∞) w := by
    intro w
    by_cases hw : w ∈ A
    · rw [Set.indicator_of_mem hw, hgdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hw)]
      rfl
    · rw [Set.indicator_of_notMem hw, hgdef, Set.indicator_of_notMem]
      intro hcon
      exact hw (Subtype.val_injective.mem_set_image.1 hcon)
  have hgval2 : ∀ φ : ℝ, (sphDir_br he hs ⁻¹' A).indicator (1 : ℝ → ℝ≥0∞) φ
      = g (dirSt_br e s φ) := by
    intro φ
    by_cases hw : sphDir_br he hs φ ∈ A
    · have hw' : φ ∈ sphDir_br he hs ⁻¹' A := hw
      rw [Set.indicator_of_mem hw', hgdef,
        Set.indicator_of_mem (show dirSt_br e s φ ∈
          (Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → _) '' A from
          Set.mem_image_of_mem _ hw)]
      rfl
    · have hw' : φ ∉ sphDir_br he hs ⁻¹' A := hw
      rw [Set.indicator_of_notMem hw', hgdef, Set.indicator_of_notMem]
      intro hcon
      exact hw (Subtype.val_injective.mem_set_image.1 hcon)
  -- the two sides as lower integrals of `g`
  have hRHS : sphereMeasure 2 A = ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      g (w : EuclideanSpace ℝ (Fin 2)) ∂(sphereMeasure 2) := by
    rw [← lintegral_indicator_one hA]
    exact (lintegral_congr hgval).symm
  have hLHS : Measure.map (sphDir_br he hs) (volume.restrict (Ioo 0 (Real.pi / 2))) A
      = ∫⁻ φ in Ioo 0 (Real.pi / 2), g (dirSt_br e s φ) := by
    rw [Measure.map_apply (measurable_sphDir_br he hs) hA,
      ← lintegral_indicator_one ((measurable_sphDir_br he hs) hA)]
    exact lintegral_congr hgval2
  rw [hLHS, hRHS]
  -- the height slicing of the sphere measure
  have hslice := lintegral_sphere_slicing 1 le_rfl hgmeas
  -- a lower bound for the inner integral over `S⁰`
  have hv0 : ‖ept s‖ = 1 := by rw [ept_norm]; nlinarith [hs, abs_nonneg s, sq_abs s]
  set v0 : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := ⟨ept s, mem_sphere_zero_iff_norm.2 hv0⟩
    with hv0def
  have hinner : ∀ t : ℝ, g (heightPoint 1 t (ept s))
      ≤ ∫⁻ v : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
          g (heightPoint 1 t (v : EuclideanSpace ℝ (Fin 1))) ∂(sphereMeasure 1) := by
    intro t
    have hfm : Measurable fun v : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 =>
        g (heightPoint 1 t (v : EuclideanSpace ℝ (Fin 1))) :=
      hgmeas.comp ((measurable_heightPoint 1).comp
        (Measurable.prodMk measurable_const measurable_subtype_coe))
    have h1 := setLIntegral_le_lintegral (μ := sphereMeasure 1) ({v0} : Set _)
      (fun v => g (heightPoint 1 t (v : EuclideanSpace ℝ (Fin 1))))
    rwa [lintegral_singleton' hfm v0, sphereMeasure_one_singleton_br v0, mul_one] at h1
  have hstep1 : (∫⁻ t in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (sliceDensity 1 t) * g (heightPoint 1 t (ept s)))
      ≤ ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        g (w : EuclideanSpace ℝ (Fin 2)) ∂(sphereMeasure 2) := by
    rw [hslice]
    exact lintegral_mono (fun t => mul_le_mul_right (hinner t) _)
  refine le_trans ?_ hstep1
  -- the substitution `t = cos φ`
  have hhp : ∀ t : ℝ, heightPoint 1 t (ept s)
      = toEuclid 1 (t, ept (Real.sqrt (1 - t ^ 2) * s)) := by
    intro t
    rw [heightPoint, ept_smul_br]
  have hsubst := lintegral_sliceDensity_eq_sin 1 le_rfl
    (fun t v => g (toEuclid 1 (t, ept (v * s))))
  have hL : (∫⁻ t in Ioo (-1 : ℝ) 1,
        ENNReal.ofReal (sliceDensity 1 t) * g (heightPoint 1 t (ept s)))
      = ∫⁻ φ in Ioo 0 Real.pi, g (angPt_br s φ) := by
    rw [show (∫⁻ t in Ioo (-1 : ℝ) 1,
          ENNReal.ofReal (sliceDensity 1 t) * g (heightPoint 1 t (ept s)))
        = ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sliceDensity 1 t)
            * g (toEuclid 1 (t, ept (Real.sqrt (1 - t ^ 2) * s))) from by
      refine lintegral_congr (fun t => ?_)
      rw [hhp t], hsubst]
    refine lintegral_congr (fun φ => ?_)
    norm_num [angPt_br]
  rw [hL]
  -- the change of variables `θ = angSt_br e φ`
  have hGmeas : Measurable fun φ : ℝ => g (angPt_br s φ) := hgmeas.comp (measurable_angPt_br s)
  have hhalf : Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo 0 Real.pi :=
    Ioo_subset_Ioo le_rfl (by linarith [Real.pi_pos])
  have hhalf2 : Ioo (Real.pi / 2) Real.pi ⊆ Ioo 0 Real.pi :=
    Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl
  rcases sign_cases_br he with rfl | rfl
  · have hrw : ∀ φ : ℝ, g (dirSt_br 1 s φ) = g (angPt_br s φ) := by
      intro φ
      rw [← angPt_angSt_br (by norm_num : (1 : ℝ) ^ 2 = 1) s φ, angSt_one_br]
    calc (∫⁻ φ in Ioo 0 (Real.pi / 2), g (dirSt_br 1 s φ))
        = ∫⁻ φ in Ioo 0 (Real.pi / 2), g (angPt_br s φ) := lintegral_congr fun φ => hrw φ
      _ ≤ ∫⁻ φ in Ioo 0 Real.pi, g (angPt_br s φ) :=
          lintegral_mono' (Measure.restrict_mono hhalf le_rfl) le_rfl
  · have hrw : ∀ φ : ℝ, g (dirSt_br (-1) s φ) = g (angPt_br s (Real.pi - φ)) := by
      intro φ
      rw [← angPt_angSt_br (by norm_num : ((-1 : ℝ)) ^ 2 = 1) s φ, angSt_neg_one_br]
    calc (∫⁻ φ in Ioo 0 (Real.pi / 2), g (dirSt_br (-1) s φ))
        = ∫⁻ φ in Ioo 0 (Real.pi / 2), g (angPt_br s (Real.pi - φ)) :=
          lintegral_congr fun φ => hrw φ
      _ = ∫⁻ φ in Ioo (Real.pi / 2) Real.pi, g (angPt_br s φ) :=
          lintegral_reflect_br _ hGmeas
      _ ≤ ∫⁻ φ in Ioo 0 Real.pi, g (angPt_br s φ) :=
          lintegral_mono' (Measure.restrict_mono hhalf2 le_rfl) le_rfl



/-! ### Consequences of the measure comparison -/

theorem quasiMeasurePreserving_sphDir_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1) :
    Measure.QuasiMeasurePreserving (sphDir_br he hs)
      (volume.restrict (Ioo 0 (Real.pi / 2))) (sphereMeasure 2) :=
  ⟨measurable_sphDir_br he hs,
    Measure.absolutelyContinuous_of_le (map_sphDir_le_br he hs)⟩

theorem ae_angle_of_ae_sphere_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1)
    {p : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → Prop}
    (h : ∀ᵐ w ∂(sphereMeasure 2), p w) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))), p (sphDir_br he hs φ) :=
  (quasiMeasurePreserving_sphDir_br he hs).ae h

theorem integral_angle_le_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1)
    {F : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ}
    (hF : Integrable F (sphereMeasure 2)) (hF0 : 0 ≤ᵐ[sphereMeasure 2] F) :
    (∫ φ in Ioo 0 (Real.pi / 2), F (sphDir_br he hs φ))
      ≤ ∫ w, F w ∂(sphereMeasure 2) := by
  have hle := map_sphDir_le_br he hs
  have hasm : AEStronglyMeasurable F
      (Measure.map (sphDir_br he hs) (volume.restrict (Ioo 0 (Real.pi / 2)))) :=
    hF.aestronglyMeasurable.mono_measure hle
  have hmap : (∫ φ in Ioo 0 (Real.pi / 2), F (sphDir_br he hs φ))
      = ∫ w, F w ∂(Measure.map (sphDir_br he hs)
        (volume.restrict (Ioo 0 (Real.pi / 2)))) :=
    (integral_map (measurable_sphDir_br he hs).aemeasurable hasm).symm
  rw [hmap]
  exact integral_mono_measure hle hF0 hF

theorem integrableOn_angle_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1)
    {F : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ}
    (hF : Integrable F (sphereMeasure 2)) :
    IntegrableOn (fun φ => F (sphDir_br he hs φ)) (Ioo 0 (Real.pi / 2)) volume := by
  have hle := map_sphDir_le_br he hs
  have hasm : AEStronglyMeasurable F
      (Measure.map (sphDir_br he hs) (volume.restrict (Ioo 0 (Real.pi / 2)))) :=
    hF.aestronglyMeasurable.mono_measure hle
  exact (integrable_map_measure hasm (measurable_sphDir_br he hs).aemeasurable).1
    (hF.mono_measure hle)

theorem aestronglyMeasurable_angle_br {e s : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1)
    {F : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ}
    (hF : AEStronglyMeasurable F (sphereMeasure 2)) :
    AEStronglyMeasurable (fun φ => F (sphDir_br he hs φ))
      (volume.restrict (Ioo 0 (Real.pi / 2))) := by
  refine ⟨fun φ => hF.mk F (sphDir_br he hs φ),
    hF.stronglyMeasurable_mk.comp_measurable (measurable_sphDir_br he hs), ?_⟩
  exact ae_angle_of_ae_sphere_br he hs hF.ae_eq_mk


end Angle



/-! ## 3. Almost-everywhere equality passes to almost every radial slice -/

section RadialAe

theorem ae_radial_congr_br {R : ℝ} {α : Type*}
    {f₁ f₂ : EuclideanSpace ℝ (Fin 2) → α}
    (h : f₁ =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)] f₂) :
    ∀ᵐ w ∂(sphereMeasure 2), ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      f₁ (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)))
        = f₂ (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have h21 : (2 : ℕ) - 1 = 1 := rfl
  have hne : volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)
      {x | ¬ f₁ x = f₂ x} = 0 := ae_iff.1 h
  obtain ⟨N, hNsup, hNmeas, hN0⟩ := exists_measurable_superset_of_null hne
  have hFmeas : Measurable (N.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hNmeas
  have hFnn : ∀ x, 0 ≤ N.indicator (fun _ => (1 : ℝ)) x := fun x => by
    by_cases hx : x ∈ N
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]
  have hFle : ∀ x, N.indicator (fun _ => (1 : ℝ)) x ≤ 1 := fun x => by
    by_cases hx : x ∈ N
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; norm_num
  have hFint : IntegrableOn (N.indicator (fun _ => (1 : ℝ)))
      (ball (0 : EuclideanSpace ℝ (Fin 2)) R) volume := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hFmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
    exact hFle x
  have hFzero : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) R,
      N.indicator (fun _ => (1 : ℝ)) x) = 0 := by
    refine integral_eq_zero_of_ae ?_
    have hmemN : ∀ᵐ x ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) R)), x ∉ N := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [hmemN] with x hx
    rw [Set.indicator_of_notMem hx]
    rfl
  have hpolar := Weak.integral_ball_polar_symm (m := 2) (by norm_num) hFint
  rw [hFzero] at hpolar
  have hBint := Weak.integrable_ball_angular (m := 2) (by norm_num) hFint
  have hnn : 0 ≤ᵐ[sphereMeasure 2] fun w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      ∫ r in Ioo (0 : ℝ) R, r ^ (2 - 1) *
        N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin 2))) := by
    filter_upwards with w
    refine setIntegral_nonneg measurableSet_Ioo (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := hr.1
    exact mul_nonneg (by positivity) (hFnn _)
  have hinner0 := (integral_eq_zero_iff_of_nonneg_ae hnn hBint).1 hpolar.symm
  have hwint := Weak.ae_integrableOn_weighted (m := 2) (R := R) (by norm_num) hFint
  filter_upwards [hinner0, hwint] with w hw hwi
  have haez : (fun r : ℝ => r ^ (2 - 1) *
      N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin 2))))
      =ᵐ[volume.restrict (Ioo (0 : ℝ) R)] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hwi).1 hw
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hr0 : (0 : ℝ) < r := hr.1
    exact mul_nonneg (by positivity) (hFnn _)
  filter_upwards [haez, ae_restrict_mem measurableSet_Ioo] with r hrz hr
  have hrpos : (0 : ℝ) < r := hr.1
  have hzero : r ^ (2 - 1) *
      N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin 2))) = 0 := hrz
  rw [h21, pow_one] at hzero
  have hFz : N.indicator (fun _ => (1 : ℝ)) (r • (w : EuclideanSpace ℝ (Fin 2))) = 0 := by
    rcases mul_eq_zero.1 hzero with h' | h'
    · exact absurd h' (ne_of_gt hrpos)
    · exact h'
  by_contra hcon
  have hmem : r • (w : EuclideanSpace ℝ (Fin 2)) ∈ N := hNsup hcon
  rw [Set.indicator_of_mem hmem] at hFz
  exact one_ne_zero hFz

end RadialAe



/-! ## 4. The centre of a cap is an interface abscissa -/

section CapCentre

variable {L R : ℝ}

/-- On the open segment swept by a cap the stadium profile is the circular arc about the cap
centre, which forces `|c + e τ| = (L/2 − R) + τ` for every `τ ∈ (0, R)`. -/
theorem capGeom_sq_eq_br (hR : 0 < R) (hL : 2 * R < L) {c e : ℝ} (hg : CapGeomSt L R c e)
    {τ : ℝ} (hτ : τ ∈ Ioo 0 R) :
    (c + e * τ) ^ 2 = (L / 2 - R + τ) ^ 2 := by
  have he := hg.sq_one
  have hd : 0 < L / 2 - R := by linarith
  have hmem : c + e * τ ∈ capSetSt c e R := by
    have hkey : e * (c + e * τ - c) = τ := by
      have h0 : e * (e * τ) = τ := by linear_combination τ * he
      simpa using h0
    rw [capSetSt, mem_setOf_eq, hkey]
    exact hτ
  obtain ⟨hφmem, hφeq⟩ := hg.capSetSt_inv hR hmem
  set φ := Real.arccos (e * (c + e * τ - c) / R) with hφdef
  obtain ⟨hsin, hcos0, hcos1⟩ := CapGeomSt.trig_bounds_st hφmem
  have hprof : profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R (c + e * τ) = R * Real.sin φ := by
    rw [← hφeq]
    exact hg.profile_capXSt hR hφmem
  have hcosval : R * Real.cos φ = τ := by
    have h : c + e * (R * Real.cos φ) = c + e * τ := hφeq
    have h4 : e * (e * (R * Real.cos φ)) = e * (e * τ) := by
      have : e * (R * Real.cos φ) = e * τ := by linarith
      rw [this]
    have ha : e * (e * (R * Real.cos φ)) = R * Real.cos φ := by
      linear_combination (R * Real.cos φ) * he
    have hb : e * (e * τ) = τ := by linear_combination τ * he
    linarith [h4, ha, hb]
  have hmemIoo : c + e * τ ∈ Ioo (-L / 2) (L / 2) := hg.sub hmem
  have hpy := Real.sin_sq_add_cos_sq φ
  set y := c + e * τ with hydef
  rcases lt_trichotomy y (-(L / 2 - R)) with hy | hy | hy
  · -- left cap
    have hlt : y < -(L / 2 - R) := hy
    have hgt : -L / 2 < y := hmemIoo.1
    rw [profile_hemisphere_left hR hL hgt hlt] at hprof
    have hnn : (0 : ℝ) ≤ R ^ 2 - (y + (L / 2 - R)) ^ 2 := by
      nlinarith [mul_pos (show (0 : ℝ) < y + (L / 2 - R) + R by linarith)
        (show (0 : ℝ) < -(y + (L / 2 - R)) by linarith), hR]
    have hsq := congrArg (fun z : ℝ => z ^ 2) hprof
    simp only at hsq
    rw [Real.sq_sqrt hnn] at hsq
    have hkey : (y + (L / 2 - R)) ^ 2 = τ ^ 2 := by
      linear_combination (-1 : ℝ) * hsq - R ^ 2 * hpy + (R * Real.cos φ + τ) * hcosval
    have hfac : (y + (L / 2 - R) - τ) * (y + (L / 2 - R) + τ) = 0 := by
      linear_combination hkey
    rcases mul_eq_zero.1 hfac with h | h
    · exfalso; linarith [hlt, hτ.1]
    · have h' : y = -(L / 2 - R) - τ := by linarith
      rw [h']; ring
  · exfalso
    have h1 : -L / 2 + (Cap.hemisphere 1).K * R ≤ y := by
      rw [hemisphere_K_st, one_mul, hy]; linarith
    have h2 : y ≤ L / 2 - (Cap.hemisphere 1).K * R := by
      rw [hemisphere_K_st, one_mul, hy]; linarith
    rw [profile_bulk h1 h2] at hprof
    have hsin1 : Real.sin φ = 1 := by
      have hz : R * (1 - Real.sin φ) = 0 := by linarith [hprof]
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (ne_of_gt hR)
      · linarith
    nlinarith [hpy, hsin1, hcos0]
  · rcases le_or_gt y (L / 2 - R) with hy2 | hy2
    · exfalso
      have h1 : -L / 2 + (Cap.hemisphere 1).K * R ≤ y := by
        rw [hemisphere_K_st, one_mul]; linarith
      have h2 : y ≤ L / 2 - (Cap.hemisphere 1).K * R := by
        rw [hemisphere_K_st, one_mul]; exact hy2
      rw [profile_bulk h1 h2] at hprof
      have hsin1 : Real.sin φ = 1 := by
        have hz : R * (1 - Real.sin φ) = 0 := by linarith [hprof]
        rcases mul_eq_zero.1 hz with h | h
        · exact absurd h (ne_of_gt hR)
        · linarith
      nlinarith [hpy, hsin1, hcos0]
    · have hlt : y < L / 2 := hmemIoo.2
      rw [profile_hemisphere_right hR hL hy2 hlt] at hprof
      have hnn : (0 : ℝ) ≤ R ^ 2 - (y - (L / 2 - R)) ^ 2 := by
        nlinarith [mul_pos (show (0 : ℝ) < R - (y - (L / 2 - R)) by linarith)
          (show (0 : ℝ) < y - (L / 2 - R) by linarith), hR]
      have hsq := congrArg (fun z : ℝ => z ^ 2) hprof
      simp only at hsq
      rw [Real.sq_sqrt hnn] at hsq
      have hkey : (y - (L / 2 - R)) ^ 2 = τ ^ 2 := by
        linear_combination (-1 : ℝ) * hsq - R ^ 2 * hpy + (R * Real.cos φ + τ) * hcosval
      have hfac : (y - (L / 2 - R) - τ) * (y - (L / 2 - R) + τ) = 0 := by
        linear_combination hkey
      rcases mul_eq_zero.1 hfac with h | h
      · have h' : y = (L / 2 - R) + τ := by linarith
        rw [h']
      · exfalso; linarith [hy2, hτ.1]

/-- **The centre of a cap is an interface abscissa**: `|c| = L/2 − R`. -/
theorem capGeom_centre_mem_br (hR : 0 < R) (hL : 2 * R < L) {c e : ℝ}
    (hg : CapGeomSt L R c e) : c ∈ Icc (-(L / 2 - R)) (L / 2 - R) := by
  have he := hg.sq_one
  have hd : 0 < L / 2 - R := by linarith
  have h1 := capGeom_sq_eq_br hR hL hg (τ := R / 2) ⟨by linarith, by linarith⟩
  have h2 := capGeom_sq_eq_br hR hL hg (τ := R / 4) ⟨by linarith, by linarith⟩
  have hstep : (c * e - (L / 2 - R)) * R = 0 := by
    linear_combination 2 * h1 - 2 * h2 - (3 / 8) * R ^ 2 * he
  have hce : c * e = L / 2 - R := by
    rcases mul_eq_zero.1 hstep with h | h
    · linarith
    · exact absurd h (ne_of_gt hR)
  have hc2 : c ^ 2 = (L / 2 - R) ^ 2 := by
    linear_combination h2 - (R / 2) * hce - (R ^ 2 / 16) * he
  have hfac : (c - (L / 2 - R)) * (c + (L / 2 - R)) = 0 := by linear_combination hc2
  rcases mul_eq_zero.1 hfac with h | h
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

end CapCentre



/-! ## 5. The radial trace and the fields of `ArcTraceSt` -/

section ArcTrace

variable {L R : ℝ}

theorem smul_dirSt_apply_zero_br (ρ e s φ : ℝ) :
    (ρ • dirSt_br e s φ) 0 = ρ * (e * Real.cos φ) := rfl

theorem smul_dirSt_apply_one_br (ρ e s φ : ℝ) :
    (ρ • dirSt_br e s φ) 1 = ρ * (s * Real.sin φ) := rfl

/-- The chart takes the scaled unit direction to the cap point. -/
theorem capChart_smul_dir_br (c e s φ ρ : ℝ) :
    capChart_br c (ρ • dirSt_br e s φ) = capPtSt c e s φ ρ := by
  rw [capChart_br_apply, capPtSt, smul_dirSt_apply_zero_br, smul_dirSt_apply_one_br]
  refine Prod.ext ?_ ?_
  · show c + ρ * (e * Real.cos φ) = c + e * (ρ * Real.cos φ)
    ring
  · show ept (ρ * (s * Real.sin φ)) = ept (s * (ρ * Real.sin φ))
    rw [mul_left_comm]

theorem capChart_slice_br (c e s R φ t : ℝ) :
    capChart_br c ((t + R / 2) • dirSt_br e s φ) = capSliceSt c e s R φ t :=
  capChart_smul_dir_br c e s φ (t + R / 2)

/-- The radial component of the transported gradient. -/
theorem inner_diskGrad_dir_br
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c e s φ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (diskGrad_br u c x) (dirSt_br e s φ)
      = e * Real.cos φ * u.gx (capChart_br c x)
        + s * Real.sin φ * u.gz (capChart_br c x) 0 := by
  rw [Weak.inner_eq_sum, Fin.sum_univ_two, diskGrad_apply_zero_br, diskGrad_apply_one_br,
    dirSt_apply_zero_br, dirSt_apply_one_br]
  ring

/-- The `H¹` density of `u` read in the chart. -/
def diskDens_br (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  u.toFun (capChart_br c x) ^ 2 + ‖diskGrad_br u c x‖ ^ 2

theorem diskDens_nonneg_br (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : 0 ≤ diskDens_br u c x := by
  unfold diskDens_br; positivity

theorem diskDens_slice_br (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c e s φ t : ℝ) :
    diskDens_br u c ((t + R / 2) • dirSt_br e s φ) = capDensSt R u c e s φ t := by
  rw [diskDens_br, capDensSt, norm_diskGrad_sq_br, capChart_slice_br]
  ring

/-- **The radial trace.** -/
def arcTrace_br (L R : ℝ) (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c e s : ℝ) (φ : ℝ) : ℝ :=
  Weak.traceSphere R (fun x => u.toFun (capChart_br c x)) (diskGrad_br u c) (dirSt_br e s φ)

end ArcTrace



section Fields

variable {L R : ℝ}

theorem integrableOn_diskDens_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    IntegrableOn (diskDens_br u c) (ball (0 : EuclideanSpace ℝ (Fin 2)) R) volume := by
  have hsub := capDisk_subset_thinDomain_br hR hL hc
  have hu := memLp_disk_toFun_br hR u hsub
  have hgr := memLp_diskGrad_br hR u hsub
  have h1 : IntegrableOn (fun x => u.toFun (capChart_br c x) ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) R) volume := by
    refine (hu.integrable_mul hu).congr (Eventually.of_forall fun x => ?_)
    show u.toFun (capChart_br c x) * u.toFun (capChart_br c x)
      = u.toFun (capChart_br c x) ^ 2
    rw [pow_two]
  have h2 : IntegrableOn (fun x => ‖diskGrad_br u c x‖ ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) R) volume := by
    refine (hgr.norm.integrable_mul hgr.norm).congr (Eventually.of_forall fun x => ?_)
    show ‖diskGrad_br u c x‖ * ‖diskGrad_br u c x‖ = ‖diskGrad_br u c x‖ ^ 2
    rw [pow_two]
  exact h1.add h2

/-- (F1) **Fubini along the rays.** -/
theorem radIntegrable_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c e s : ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume ∧
        IntegrableOn (fun t => capDensSt R u c e s φ t * (t + R / 2))
          (Ioo 0 (R / 2)) volume := by
  have hc := capGeom_centre_mem_br hR hL hg
  have hD := integrableOn_diskDens_br hR hL u hc
  have hslice := Weak.ae_integrableOn_slice (m := 2) (R := R) (by norm_num) hD
  have hae := ae_angle_of_ae_sphere_br (e := e) (s := s) hg.sq_one hs
    (p := fun w => ∀ ε ∈ Ioo (0 : ℝ) R,
      IntegrableOn (fun r : ℝ => diskDens_br u c
        (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))))
        (Ioo ε R) volume) hslice
  filter_upwards [hae] with φ hφ
  have h1 := hφ (R / 2) ⟨by linarith, by linarith⟩
  have h2 := Weak.integrableOn_translate (c := R / 2) h1
  rw [Weak.preimage_addRight_Ioo, sub_self, show R - R / 2 = R / 2 by ring] at h2
  have hfirst : IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume := by
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioo
    exact diskDens_slice_br u c e s φ t
  refine ⟨hfirst, ?_⟩
  refine Integrable.mono' (hfirst.const_mul R)
    (hfirst.aestronglyMeasurable.mul
      ((continuous_id.add continuous_const).aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht1 : (0 : ℝ) < t := ht.1
  have ht2 : t < R / 2 := ht.2
  have hdn : 0 ≤ capDensSt R u c e s φ t := capDensSt_nonneg R u c e s φ t
  rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith [hdn, ht1, hR])]
  nlinarith [hdn, ht1, ht2, hR]


/-! ### The polar energy -/

/-- The polar energy of the whole ray of direction `w`. -/
def angFull_br (R : ℝ) (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c : ℝ) (w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : ℝ :=
  ∫ r in Ioo (0 : ℝ) R, r ^ (2 - 1) * diskDens_br u c
    (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)))

/-- The polar energy of the inner half of the ray of direction `w`. -/
def angHalf_br (R : ℝ) (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c : ℝ) (w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : ℝ :=
  ∫ r in Ioo (0 : ℝ) (R / 2), r ^ (2 - 1) * diskDens_br u c
    (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)))

theorem angFull_nonneg_br (_hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ) (w) :
    0 ≤ angFull_br R u c w := by
  refine setIntegral_nonneg measurableSet_Ioo (fun r hr => ?_)
  have : (0 : ℝ) < r := hr.1
  exact mul_nonneg (by positivity) (diskDens_nonneg_br u c _)

theorem angHalf_nonneg_br (_hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c : ℝ) (w) :
    0 ≤ angHalf_br R u c w := by
  refine setIntegral_nonneg measurableSet_Ioo (fun r hr => ?_)
  have : (0 : ℝ) < r := hr.1
  exact mul_nonneg (by positivity) (diskDens_nonneg_br u c _)

theorem integrable_angFull_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    Integrable (angFull_br R u c) (sphereMeasure 2) :=
  Weak.integrable_ball_angular (m := 2) (by norm_num) (integrableOn_diskDens_br hR hL u hc)

theorem integrable_angHalf_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    Integrable (angHalf_br R u c) (sphereMeasure 2) :=
  Weak.integrable_ball_angular (m := 2) (by norm_num)
    ((integrableOn_diskDens_br hR hL u hc).mono_set (ball_subset_ball (by linarith)))

theorem Ioo_ae_union_br (_hR : 0 < R) :
    Ioo (0 : ℝ) R =ᵐ[volume] (Ioo (0 : ℝ) (R / 2) ∪ Ioo (R / 2) R : Set ℝ) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_) (measure_singleton (R / 2))
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    simp only [mem_union, mem_Ioo, not_or] at hx3
    obtain ⟨hA, hB⟩ := hx3
    push_neg at hA hB
    have h1 : R / 2 ≤ x := hA hx1
    rcases eq_or_lt_of_le h1 with h | h
    · exact h.symm
    · exact absurd (hB h) (by linarith)
  · have hsub : (Ioo (0 : ℝ) (R / 2) ∪ Ioo (R / 2) R : Set ℝ) ⊆ Ioo 0 R := by
      rintro x (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
    rw [Set.diff_eq_empty.2 hsub]
    simp

theorem setIntegral_split_br (hR : 0 < R) {H : ℝ → ℝ}
    (hHint : IntegrableOn H (Ioo (0 : ℝ) R) volume) :
    (∫ r in Ioo (0 : ℝ) R, H r)
      = (∫ r in Ioo (0 : ℝ) (R / 2), H r) + ∫ r in Ioo (R / 2) R, H r := by
  have hdisj : Disjoint (Ioo (0 : ℝ) (R / 2)) (Ioo (R / 2) R) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hx2⟩ ⟨hx3, _⟩
    linarith
  rw [setIntegral_congr_set (Ioo_ae_union_br hR),
    setIntegral_union hdisj measurableSet_Ioo
      (hHint.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2]⟩))
      (hHint.mono_set (fun x hx => ⟨by linarith [hx.1], hx.2⟩))]

/-- For almost every direction the difference of the two polar energies is the energy of the
outer half of the ray. -/
theorem angFull_sub_angHalf_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    ∀ᵐ w ∂(sphereMeasure 2), angFull_br R u c w - angHalf_br R u c w
      = ∫ r in Ioo (R / 2) R, r ^ (2 - 1) * diskDens_br u c
          (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
            EuclideanSpace ℝ (Fin 2))) := by
  have hD := integrableOn_diskDens_br hR hL u hc
  filter_upwards [Weak.ae_integrableOn_weighted (m := 2) (R := R) (by norm_num) hD] with w hw
  have h := setIntegral_split_br hR hw
  rw [angFull_br, angHalf_br, h]
  ring

theorem angFull_sub_angHalf_nonneg_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    0 ≤ᵐ[sphereMeasure 2] fun w => angFull_br R u c w - angHalf_br R u c w := by
  filter_upwards [angFull_sub_angHalf_br hR hL u hc] with w hw
  rw [Pi.zero_apply, hw]
  refine setIntegral_nonneg measurableSet_Ioo (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := by linarith [hr.1]
  exact mul_nonneg (by positivity) (diskDens_nonneg_br u c _)

/-- The polar energy of the outer half of a ray, in the angular variable. -/
theorem arcEnergy_eq_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c e s : ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      arcEnergySt R u c e s φ
        = angFull_br R u c (sphDir_br hg.sq_one hs φ)
          - angHalf_br R u c (sphDir_br hg.sq_one hs φ) := by
  have hc := capGeom_centre_mem_br hR hL hg
  have hD := integrableOn_diskDens_br hR hL u hc
  have hw := Weak.ae_integrableOn_weighted (m := 2) (R := R) (by norm_num) hD
  have hae := ae_angle_of_ae_sphere_br (e := e) (s := s) hg.sq_one hs
    (p := fun w => IntegrableOn (fun r : ℝ => r ^ (2 - 1) * diskDens_br u c
      (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))))
      (Ioo (0 : ℝ) R) volume) hw
  filter_upwards [hae] with φ hφ
  set H : ℝ → ℝ := fun r => r ^ (2 - 1) * diskDens_br u c (r • dirSt_br e s φ) with hHdef
  have hHint : IntegrableOn H (Ioo (0 : ℝ) R) volume := hφ
  have hsplit : (∫ r in Ioo (0 : ℝ) R, H r)
      = (∫ r in Ioo (0 : ℝ) (R / 2), H r) + ∫ r in Ioo (R / 2) R, H r :=
    setIntegral_split_br hR hHint
  have houter : arcEnergySt R u c e s φ = ∫ r in Ioo (R / 2) R, H r := by
    rw [arcEnergySt, ← Weak.setIntegral_translate (R / 2) H (Ioo (R / 2) R),
      Weak.preimage_addRight_Ioo, sub_self, show R - R / 2 = R / 2 by ring]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
    rw [hHdef]
    show capDensSt R u c e s φ t * (t + R / 2)
      = (t + R / 2) ^ (2 - 1) * diskDens_br u c ((t + R / 2) • dirSt_br e s φ)
    rw [diskDens_slice_br]
    norm_num
    ring
  rw [houter]
  have hF : angFull_br R u c (sphDir_br hg.sq_one hs φ) = ∫ r in Ioo (0 : ℝ) R, H r := rfl
  have hH2 : angHalf_br R u c (sphDir_br hg.sq_one hs φ)
      = ∫ r in Ioo (0 : ℝ) (R / 2), H r := rfl
  rw [hF, hH2, hsplit]
  ring



/-- (F2) **Fubini in the angle.** -/
theorem energy_integrable_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c e s : ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1) :
    IntegrableOn (arcEnergySt R u c e s) (Ioo 0 (Real.pi / 2)) volume := by
  have hc := capGeom_centre_mem_br hR hL hg
  have hI : Integrable (fun w => angFull_br R u c w - angHalf_br R u c w) (sphereMeasure 2) :=
    (integrable_angFull_br hR hL u hc).sub (integrable_angHalf_br hR hL u hc)
  have h1 := integrableOn_angle_br hg.sq_one hs hI
  exact h1.congr (Filter.EventuallyEq.symm (arcEnergy_eq_br hR hL u hg hs))

theorem integral_diskDens_le_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c : ℝ}
    (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R)) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin 2)) R, diskDens_br u c z)
      ≤ massP u + dirichletP u := by
  have hsub := capDisk_subset_thinDomain_br hR hL hc
  have hu := memLp_disk_toFun_br hR u hsub
  have hgr := memLp_diskGrad_br hR u hsub
  have h1 : IntegrableOn (fun x => u.toFun (capChart_br c x) ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) R) volume := by
    refine (hu.integrable_mul hu).congr (Eventually.of_forall fun x => ?_)
    show u.toFun (capChart_br c x) * u.toFun (capChart_br c x)
      = u.toFun (capChart_br c x) ^ 2
    rw [pow_two]
  have h2 : IntegrableOn (fun x => ‖diskGrad_br u c x‖ ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) R) volume := by
    refine (hgr.norm.integrable_mul hgr.norm).congr (Eventually.of_forall fun x => ?_)
    show ‖diskGrad_br u c x‖ * ‖diskGrad_br u c x‖ = ‖diskGrad_br u c x‖ ^ 2
    rw [pow_two]
  have hsplit : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 2)) R, diskDens_br u c z)
      = Weak.mass (diskH1_br hR hL u c hc) + Weak.dirichlet (diskH1_br hR hL u c hc) := by
    have hadd : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 2)) R, diskDens_br u c z)
        = (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) R, u.toFun (capChart_br c x) ^ 2)
          + ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) R, ‖diskGrad_br u c x‖ ^ 2 := by
      rw [← integral_add h1 h2]
      rfl
    rw [hadd]
    rfl
  rw [hsplit]
  have hm := mass_diskH1_le_br hR hL u c hc
  have hd := dirichlet_diskH1_le_br hR hL u c hc
  linarith

/-- (P) **The polar change of variables on the quarter-disk.** -/
theorem energy_le_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c e s : ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1) :
    (∫ φ in Ioo 0 (Real.pi / 2), arcEnergySt R u c e s φ) ≤ massP u + dirichletP u := by
  have hc := capGeom_centre_mem_br hR hL hg
  have hF := integrable_angFull_br hR hL u hc
  have hH := integrable_angHalf_br hR hL u hc
  have hI := hF.sub hH
  have hnn := angFull_sub_angHalf_nonneg_br hR hL u hc
  have hstep1 : (∫ φ in Ioo 0 (Real.pi / 2), arcEnergySt R u c e s φ)
      = ∫ φ in Ioo 0 (Real.pi / 2), (angFull_br R u c (sphDir_br hg.sq_one hs φ)
          - angHalf_br R u c (sphDir_br hg.sq_one hs φ)) :=
    integral_congr_ae (arcEnergy_eq_br hR hL u hg hs)
  rw [hstep1]
  have h3 : 0 ≤ ∫ w, angHalf_br R u c w ∂(sphereMeasure 2) :=
    integral_nonneg (fun w => angHalf_nonneg_br hR u c w)
  have h4 : (∫ w, angFull_br R u c w ∂(sphereMeasure 2))
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin 2)) R, diskDens_br u c z :=
    (Weak.integral_ball_polar_symm (m := 2) (by norm_num)
      (integrableOn_diskDens_br hR hL u hc)).symm
  have h5 := integral_diskDens_le_br hR hL u hc
  have hbound : (∫ w, (angFull_br R u c w - angHalf_br R u c w) ∂(sphereMeasure 2))
      ≤ massP u + dirichletP u := by
    rw [integral_sub hF hH, h4]
    linarith
  exact le_trans (integral_angle_le_br hg.sq_one hs hI hnn) hbound



/-- (AC) **Radial absolute continuity.** -/
theorem radAC_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c e s : ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∃ W : Sobolev.H1 (R / 2),
        W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => u.toFun (capSliceSt c e s R φ t)) ∧
          deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
              + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ∧
          W.toFun (R / 2) = arcTrace_br L R u c e s φ := by
  have hc := capGeom_centre_mem_br hR hL hg
  have hslice := Weak.radialSlice_h1 (m := 2) (by norm_num) hR (diskH1_br hR hL u c hc)
  have htrace := Weak.traceSphere_eq_const_add (m := 2) (by norm_num) hR (diskH1_br hR hL u c hc)
  have hginner := Weak.ae_integrableOn_slice_inner (m := 2) (R := R) (by norm_num)
    (diskH1_br hR hL u c hc).grad_memL2
  have hA := ae_angle_of_ae_sphere_br (e := e) (s := s) hg.sq_one hs hslice
  have hB := ae_angle_of_ae_sphere_br (e := e) (s := s) hg.sq_one hs htrace
  have hC := ae_angle_of_ae_sphere_br (e := e) (s := s) hg.sq_one hs hginner
  filter_upwards [hA, hB, hC] with φ h1 h2 h3
  have hhalf : (0 : ℝ) < R / 2 := by linarith
  have hmem : (R / 2) ∈ Ioo (0 : ℝ) R := ⟨by linarith, by linarith⟩
  have h1' := h1 (R / 2) hmem
  rw [show R - R / 2 = R / 2 by ring] at h1'
  obtain ⟨W, hW1, hW2⟩ := h1'
  refine ⟨W, ?_, ?_, ?_⟩
  · refine hW1.trans (Eventually.of_forall fun t => ?_)
    show u.toFun (capChart_br c ((t + R / 2) • dirSt_br e s φ))
      = u.toFun (capSliceSt c e s R φ t)
    rw [capChart_slice_br]
  · refine hW2.trans (Eventually.of_forall fun t => ?_)
    show inner ℝ (diskGrad_br u c ((t + R / 2) • dirSt_br e s φ)) (dirSt_br e s φ)
      = e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
        + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0
    rw [inner_diskGrad_dir_br, capChart_slice_br]
  · obtain ⟨κ, hκ1, hκ2⟩ := h2
    have hGII : IntervalIntegrable
        (fun t => inner ℝ ((diskH1_br hR hL u c hc).grad (t • dirSt_br e s φ))
          (dirSt_br e s φ)) volume (R / 2) R :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2 (h3 (R / 2) hmem).1
    have hamem : ((R / 2 + R) / 2) ∈ uIcc (R / 2) R := by
      rw [uIcc_of_le (by linarith : R / 2 ≤ R)]
      exact ⟨by linarith, by linarith⟩
    have hP : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
        inner ℝ ((diskH1_br hR hL u c hc).grad (t • dirSt_br e s φ))
          (dirSt_br e s φ)) (Icc (R / 2) R) := by
      have h := intervalIntegral.continuousOn_primitive_interval' hGII hamem
      rwa [uIcc_of_le (by linarith : R / 2 ≤ R)] at h
    have hmaps : MapsTo (fun t : ℝ => t + R / 2) (Icc 0 (R / 2)) (Icc (R / 2) R) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hFcont : ContinuousOn (fun t : ℝ => κ + ∫ τ in ((R / 2 + R) / 2)..(t + R / 2),
        inner ℝ ((diskH1_br hR hL u c hc).grad (τ • dirSt_br e s φ))
          (dirSt_br e s φ)) (Icc 0 (R / 2)) :=
      continuousOn_const.add (hP.comp (continuous_add_right (R / 2)).continuousOn hmaps)
    have hWcont : ContinuousOn W.toFun (Icc 0 (R / 2)) := H1_continuousOn hhalf W
    have hκ1' := Weak.ae_eq_translate (c := R / 2) hκ1
    rw [Weak.preimage_addRight_Ioo, sub_self, show R - R / 2 = R / 2 by ring] at hκ1'
    have hFae : (fun t : ℝ => κ + ∫ τ in ((R / 2 + R) / 2)..(t + R / 2),
        inner ℝ ((diskH1_br hR hL u c hc).grad (τ • dirSt_br e s φ)) (dirSt_br e s φ))
        =ᵐ[volume.restrict (Ioo 0 (R / 2))] W.toFun := (hW1.trans hκ1').symm
    have hend := Weak.eq_of_ae_eq_of_continuousOn hhalf hFcont hWcont hFae
    rw [← hend, arcTrace_br]
    have hκ2' : Weak.traceSphere R (fun x => u.toFun (capChart_br c x)) (diskGrad_br u c)
        (dirSt_br e s φ)
        = κ + ∫ t in ((R / 2 + R) / 2)..R,
          inner ℝ ((diskH1_br hR hL u c hc).grad (t • dirSt_br e s φ))
            (dirSt_br e s φ) := hκ2
    rw [hκ2', show R / 2 + R / 2 = R by ring]



/-! ### Measurability of the sphere trace -/

/-- The sphere trace only depends on the radial slices, up to null sets. -/
theorem traceSphere_congr_br (hR : 0 < R) {v₁ v₂ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {w : EuclideanSpace ℝ (Fin 2)}
    (hv : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), v₁ (r • w) = v₂ (r • w))
    (hgg : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), g₁ (r • w) = g₂ (r • w)) :
    Weak.traceSphere R v₁ g₁ w = Weak.traceSphere R v₂ g₂ w := by
  have hGae : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (0 : ℝ) R →
      inner ℝ (g₁ (r • w)) w = inner ℝ (g₂ (r • w)) w := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hgg] with r hr hmem
    rw [hr hmem]
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ R := by
    rw [ae_iff]
    simp
  have hII : ∀ p q : ℝ, p ∈ Icc (0 : ℝ) R → q ∈ Icc (0 : ℝ) R →
      (∫ t in p..q, inner ℝ (g₁ (t • w)) w) = ∫ t in p..q, inner ℝ (g₂ (t • w)) w := by
    intro p q hp hq
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hGae, hne] with r hr hrR hmem
    rw [Set.uIoc, mem_Ioc] at hmem
    refine hr ⟨?_, ?_⟩
    · exact lt_of_le_of_lt (le_min hp.1 hq.1) hmem.1
    · exact lt_of_le_of_ne (le_trans hmem.2 (max_le hp.2 hq.2)) hrR
  have haM : ((R / 2 + R) / 2) ∈ Icc (0 : ℝ) R := ⟨by linarith, by linarith⟩
  have hRM : R ∈ Icc (0 : ℝ) R := ⟨by linarith, le_rfl⟩
  have houter : (∫ r in Ioo (R / 2) R,
        (v₁ (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (g₁ (t • w)) w))
      = ∫ r in Ioo (R / 2) R,
        (v₂ (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (g₂ (t • w)) w) := by
    refine integral_congr_ae ?_
    have hvsub : ∀ᵐ r ∂(volume.restrict (Ioo (R / 2) R)), v₁ (r • w) = v₂ (r • w) :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (by linarith) le_rfl) hv
    filter_upwards [hvsub, ae_restrict_mem measurableSet_Ioo] with r hr hmem
    rw [hr, hII _ _ haM ⟨by linarith [hmem.1], le_of_lt hmem.2⟩]
  simp only [Weak.traceSphere]
  rw [houter, hII _ _ haM hRM]

/-- **The sphere trace of strongly measurable data is measurable in the direction.** -/
theorem stronglyMeasurable_traceSphere_br {R : ℝ} {v : EuclideanSpace ℝ (Fin 2) → ℝ}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hv : Measurable v) (hgm : Measurable g) :
    StronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      Weak.traceSphere R v g (w : EuclideanSpace ℝ (Fin 2))) := by
  classical
  have hsmul : Measurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ =>
      p.2 • ((p.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        EuclideanSpace ℝ (Fin 2))) :=
    measurable_snd.smul (measurable_subtype_coe.comp measurable_fst)
  have hH : StronglyMeasurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ =>
      inner ℝ (g (p.2 • ((p.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        EuclideanSpace ℝ (Fin 2))))
        ((p.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))) :=
    ((hgm.comp hsmul).inner (measurable_subtype_coe.comp measurable_fst)).stronglyMeasurable
  -- the fixed-interval pieces
  have hInd : ∀ S : Set ℝ, StronglyMeasurable
      (fun w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => ∫ t in S,
        inner ℝ (g (t • ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))))
          ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))) :=
    fun S => hH.integral_prod_right' (ν := volume.restrict S)
  -- the variable-interval piece
  have hmeasS : ∀ b : ℝ, MeasurableSet
      {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ | b < z.2 ∧ z.2 ≤ z.1.2} :=
    fun b => (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hmeasS' : ∀ b : ℝ, MeasurableSet
      {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ | z.1.2 < z.2 ∧ z.2 ≤ b} :=
    fun b => (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hG1 : StronglyMeasurable
      (fun z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ =>
        inner ℝ (g (z.2 • ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))))
          ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))) :=
    hH.comp_measurable (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd)
  have hJ1 : ∀ b : ℝ, StronglyMeasurable
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))) := by
    intro b
    have hF : StronglyMeasurable
        (fun z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))) z.2) := by
      have heq : (fun z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))) z.2)
          = Set.indicator {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2}
            (fun z => inner ℝ (g (z.2 • ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))))
              ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
                EuclideanSpace ℝ (Fin 2))) := by
        funext z
        by_cases hz : b < z.2 ∧ z.2 ≤ z.1.2
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc b z.1.2 from hz),
            Set.indicator_of_mem (show z ∈ {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc b z.1.2 from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ |
                b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS b)
    have hEq : (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)))
        = fun q => ∫ y : ℝ, (Ioc b q.2).indicator
          (fun t => inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
            EuclideanSpace ℝ (Fin 2))))
            ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF.integral_prod_right' (ν := (volume : Measure ℝ))
  have hJ2 : ∀ b : ℝ, StronglyMeasurable
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))) := by
    intro b
    have hF : StronglyMeasurable
        (fun z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))) z.2) := by
      have heq : (fun z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (g (t •
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2))))
            ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))) z.2)
          = Set.indicator {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b}
            (fun z => inner ℝ (g (z.2 • ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))))
              ((z.1.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
                EuclideanSpace ℝ (Fin 2))) := by
        funext z
        by_cases hz : z.1.2 < z.2 ∧ z.2 ≤ b
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc z.1.2 b from hz),
            Set.indicator_of_mem (show z ∈ {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc z.1.2 b from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) × ℝ |
                z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS' b)
    have hEq : (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))))
          ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)))
        = fun q => ∫ y : ℝ, (Ioc q.2 b).indicator
          (fun t => inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
            EuclideanSpace ℝ (Fin 2))))
            ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF.integral_prod_right' (ν := (volume : Measure ℝ))
  -- assembling
  have hinner : StronglyMeasurable
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ =>
        v (q.2 • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)))
          - ∫ t in ((R / 2 + R) / 2)..q.2,
            inner ℝ (g (t • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
              EuclideanSpace ℝ (Fin 2))))
              ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
                EuclideanSpace ℝ (Fin 2))) := by
    have hv' : StronglyMeasurable
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ =>
          v (q.2 • ((q.1 : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
            EuclideanSpace ℝ (Fin 2)))) := (hv.comp hsmul).stronglyMeasurable
    exact hv'.sub ((hJ1 ((R / 2 + R) / 2)).sub (hJ2 ((R / 2 + R) / 2)))
  have hI1 := hinner.integral_prod_right' (ν := volume.restrict (Ioo (R / 2) R))
  have hI2 := ((hInd (Ioc ((R / 2 + R) / 2) R)).sub (hInd (Ioc R ((R / 2 + R) / 2))))
  exact (hI1.const_mul (2 / R)).add hI2



/-- (M) **Measurability of the radial trace in the angle.** -/
theorem aesm_arcTrace_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {c e s : ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1) :
    AEStronglyMeasurable (arcTrace_br L R u c e s)
      (volume.restrict (Ioo 0 (Real.pi / 2))) := by
  have hc := capGeom_centre_mem_br hR hL hg
  have hsub := capDisk_subset_thinDomain_br hR hL hc
  have hu := memLp_disk_toFun_br hR u hsub
  have hgr := memLp_diskGrad_br hR u hsub
  have hTr : AEStronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
      Weak.traceSphere R (fun x => u.toFun (capChart_br c x)) (diskGrad_br u c)
        ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)))
      (sphereMeasure 2) := by
    refine ⟨fun w => Weak.traceSphere R (hu.1.mk _) (hgr.1.mk _)
      ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)),
      stronglyMeasurable_traceSphere_br hu.1.stronglyMeasurable_mk.measurable
        hgr.1.stronglyMeasurable_mk.measurable, ?_⟩
    filter_upwards [ae_radial_congr_br (R := R) hu.1.ae_eq_mk,
      ae_radial_congr_br (R := R) hgr.1.ae_eq_mk] with w hw1 hw2
    exact traceSphere_congr_br hR hw1 hw2
  exact aestronglyMeasurable_angle_br hg.sq_one hs hTr

/-- **All the analytic fields of `ArcTraceSt` for the radial trace.** -/
theorem arcTraceSt_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c e s : ℝ)
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1) :
    ArcTraceSt L R u c e s (arcTrace_br L R u c e s) :=
  arcTraceSt_of_fields_vr hR hL hg hs (aesm_arcTrace_br hR hL u hg hs)
    (radAC_br hR hL u hg hs) (radIntegrable_br hR hL u hg hs)
    (energy_integrable_br hR hL u hg hs) (energy_le_br hR hL u hg hs)

/-- **The identification statement**, now a theorem. -/
def VertRadIdent_br (L R : ℝ) : Prop :=
  ∀ (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c e s : ℝ),
    CapGeomSt L R c e → s ^ 2 = 1 →
      ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
        trSideSt s u (capXSt c e R φ) = arcTrace_br L R u c e s φ

theorem vertRadIdent_br (hR : 0 < R) (hL : 2 * R < L) : VertRadIdent_br L R :=
  fun u c e s hg hs => (arcTraceSt_br hR hL u c e s hg hs).vert_eq

/-- **Deliverable 3: the radial ACL hypothesis of `TraceIneqStadium`.** -/
theorem radialACL_br (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) : RadialACL L R u where
  arc := fun c e s hg hs => ⟨arcTrace_br L R u c e s, arcTraceSt_br hR hL u c e s hg hs⟩

/-- **The trace inequality on the planar stadium.** -/
theorem traceIneqOne_hemisphere_br (hR : 0 < R) (hL : 2 * R < L) :
    TraceIneqOne (Cap.hemisphere 1) (Cap.hemisphere 1) L R :=
  traceIneqOne_hemisphere hR hL (fun u => radialACL_br hR hL u)


end Fields


end Bridge

end RobinCaps.ThinDomain

end
