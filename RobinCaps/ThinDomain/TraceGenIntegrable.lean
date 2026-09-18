import RobinCaps.ThinDomain.TraceGen
import RobinCaps.ThinDomain.SphereSlicing
import RobinCaps.ThinDomain.BoundaryIntegrable

/-!
# Discharging the two remaining integrability hypotheses of `TraceGen.lean`

`RobinCaps/ThinDomain/TraceGen.lean` isolates two Fubini/polar-coordinates facts as explicit
`Prop`-valued structures, `CapTraceIntegrable_tgn` and `ContinuousBoundaryIntegrable_tgn`, and
proves the trace datum of the thin domain (in general transverse dimension, for hemispherical
caps) conditional on them.  This file discharges both.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap RobinCaps.Sobolev RobinCaps.Compact

/-! ## 1. `CapTraceIntegrable_tgn` -/

/-- The sphere integrand of a product of `Γ`-traces is integrable on `S^m` w.r.t. the sphere
measure of `ℝ^{m+1}`.  Reproduces the intermediate step of
`RobinCaps.Cap.capLateralIntegral_trGamma_th`, which is not exported. -/
theorem integrable_capSphereFun_trGamma_tgi (m : ℕ) (hm : 1 ≤ m)
    (u v : H1P ((Cap.hemisphere m).body)) :
    Integrable (capSphereFun m (fun p => trGamma_th m u p * trGamma_th m v p))
      (sphereMeasure (m + 1)) := by
  have hae : (capSphereFun m (fun p => trGamma_th m u p * trGamma_th m v p))
      =ᵐ[sphereMeasure (m + 1)]
      Set.indicator (upperSphere_th m)
        (fun w => gammaTrace u ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          * gammaTrace v ((w : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))) := by
    filter_upwards [trGamma_ae_th u, trGamma_ae_th v] with w h1 h2
    rw [capSphereFun_mul_th]
    by_cases hw : w ∈ upperSphere_th m
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, h1, h2]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
  exact ((integrable_gammaTrace_mul_th u v).indicator measurableSet_upperSphere_th).congr hae.symm

/-- **Genuine integrability of the lateral density of the hemispherical end cap.**  Given
integrability of `capSphereFun m G` on `S^m`, the underlying revolution-coordinate density
`capLateralDensity (Cap.hemisphere m) G` is Bochner-integrable on `Ioo (-1) 0`, not just formally
so via `capLateralIntegral_hemisphere_eq`'s value identity.  This tracks genuine integrability
through the same Fubini apparatus (`map_heightSplit`, `heightMeasure`) that underlies
`RobinCaps.ThinDomain.integral_sphere_slicing`. -/
theorem integrableOn_capLateralDensity_hemisphere_tgi (m : ℕ) (hm : 1 ≤ m) (G : CapSpace m → ℝ)
    (hG : Integrable (capSphereFun m G) (sphereMeasure (m + 1))) :
    IntegrableOn (capLateralDensity (Cap.hemisphere m) G) (Ioo (-1 : ℝ) 0) := by
  -- Step 1: pull `hG` back along `heightSplit`.
  have hmap := map_heightSplit m hm
  have hφ : AEMeasurable (heightSplit m) ((heightMeasure m).prod (sphereMeasure m)) :=
    (measurable_heightSplit m).aemeasurable
  have hfsm : AEStronglyMeasurable (capSphereFun m G)
      (Measure.map (heightSplit m) ((heightMeasure m).prod (sphereMeasure m))) := by
    rw [hmap]; exact hG.aestronglyMeasurable
  have hint : Integrable (fun p => capSphereFun m G (heightSplit m p))
      ((heightMeasure m).prod (sphereMeasure m)) :=
    (integrable_map_measure hfsm hφ).1 (by rw [hmap]; exact hG)
  -- Step 2: integrate out the transverse sphere variable (Fubini).
  have hintL : Integrable (fun t => ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      capSphereFun m G (heightSplit m (t, ω)) ∂(sphereMeasure m)) (heightMeasure m) :=
    hint.integral_prod_left
  -- Step 3: unfold `heightMeasure` as a `withDensity` over `Ioo (-1) 1`.
  unfold heightMeasure at hintL
  have hIoo : IntegrableOn (fun t => (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      capSphereFun m G (heightSplit m (t, ω)) ∂(sphereMeasure m)) * sliceDensity m t)
      (Ioo (-1 : ℝ) 1) := by
    have h := (integrable_withDensity_iff (measurable_ofReal_sliceDensity m)
      (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))).1 hintL
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [ENNReal.toReal_ofReal (sliceDensity_nonneg m ht)]
  -- Step 4: restrict to `(0,1)` and identify the sphere integral via `capSphereFun_heightSplit`.
  set Φ : ℝ → ℝ := fun t => sliceDensity m t *
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      G (t - 1, Real.sqrt (1 - t ^ 2) • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)
    with hΦdef
  have hIoo01 : IntegrableOn Φ (Ioo (0 : ℝ) 1) := by
    have hsub : IntegrableOn (fun t => (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        capSphereFun m G (heightSplit m (t, ω)) ∂(sphereMeasure m)) * sliceDensity m t)
        (Ioo (0 : ℝ) 1) := hIoo.mono_set (Set.Ioo_subset_Ioo (by norm_num) le_rfl)
    refine hsub.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have ht1 : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hcongrOmega : (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        capSphereFun m G (heightSplit m (t, ω)) ∂(sphereMeasure m))
        = ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            G (t - 1, Real.sqrt (1 - t ^ 2) • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only []
      rw [capSphereFun_heightSplit m G ht1 ω, if_pos ht.1]
    rw [hΦdef]
    simp only []
    rw [hcongrOmega]
    ring
  -- Step 5: shift the interval `(0,1) ↦ (-1,0)` and identify with `capLateralDensity`.
  have hInterval : IntervalIntegrable Φ volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hIoo01
  have hShift := hInterval.comp_add_right (1 : ℝ)
  rw [show (0 : ℝ) - 1 = -1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num] at hShift
  have hShiftIoo : IntegrableOn (fun x => Φ (x + 1)) (Ioo (-1 : ℝ) 0) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 0)).1 hShift
  have hstep : ∀ s ∈ Ioo (-1 : ℝ) 0, capLateralDensity (Cap.hemisphere m) G s = Φ (s + 1) := by
    intro s hs
    rw [capLateralDensity, capAreaElement_hemisphere m hm hs, hΦdef]
    simp only [add_sub_cancel_right]
    rfl
  exact hShiftIoo.congr_fun (fun s hs => (hstep s hs).symm) measurableSet_Ioo

/-- **Deliverable 1.**  `CapTraceIntegrable_tgn`, discharged. -/
theorem capTraceIntegrable_tgi (m : ℕ) (hm : 1 ≤ m) : CapTraceIntegrable_tgn m hm where
  integrableOn a b := by
    have hK1 : (Cap.hemisphere m).K = 1 := rfl
    rw [hK1]
    exact integrableOn_capLateralDensity_hemisphere_tgi m hm _
      (integrable_capSphereFun_trGamma_tgi m hm a b)

/-! ## 2. `ContinuousBoundaryIntegrable_tgn` -/

section ContinuousBoundary

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-- **The spherical average of a function continuous up to the boundary is a.e. strongly
measurable**, on any measurable subset of the axial interval `(-L/2, L/2)`.  This is the
analogue of `aestronglyMeasurable_sphereAverage` (`RobinCaps/ThinDomain/BoundaryIntegrable.lean`)
for a `g` which is only `ContinuousOn` the closure of the thin domain (as `H1P.toFun` need not be
globally measurable), rather than globally `Measurable`. -/
theorem aestronglyMeasurable_sphereAverage_of_continuousOn_tgi (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) {g : CapSpace m → ℝ}
    (hgc : ContinuousOn g (closure (thinDomain Cm Cp L R))) {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Ioo (-L/2) (L/2)) :
    AEStronglyMeasurable
      (fun x => ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      (volume.restrict s) := by
  set F : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℝ :=
    fun q => g (q.1, profile Cm Cp L R q.1 • (q.2 : EuclideanSpace ℝ (Fin m))) with hFdef
  have hcompcont : ContinuousOn (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ((q.1, profile Cm Cp L R q.1 • (q.2 : EuclideanSpace ℝ (Fin m))) : CapSpace m))
      (s ×ˢ (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin m)) 1))) := by
    refine ContinuousOn.prodMk continuousOn_fst ?_
    refine ContinuousOn.smul ?_ (continuous_subtype_val.comp continuous_snd).continuousOn
    exact (continuousOn_profile hR hL).comp continuous_fst.continuousOn
      (fun q hq => hsub hq.1)
  have hmaps : MapsTo (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ((q.1, profile Cm Cp L R q.1 • (q.2 : EuclideanSpace ℝ (Fin m))) : CapSpace m))
      (s ×ˢ (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
      (closure (thinDomain Cm Cp L R)) := by
    rintro ⟨x, ω⟩ ⟨hx, -⟩
    exact mem_closure_thinDomain_lateral hR hL (hsub hx) ω
  have hFcont : ContinuousOn F
      (s ×ˢ (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin m)) 1))) :=
    hgc.comp hcompcont hmaps
  have hFmeas : AEStronglyMeasurable F ((volume.restrict s).prod (sphereMeasure m)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hFcont.aestronglyMeasurable (hs.prod MeasurableSet.univ)
  exact hFmeas.integral_prod_right'

/-- **The workhorse**, for a `g` continuous on the closure of the thin domain: on any
sub-interval of the axial interval on which the area element is integrable, the lateral density
of `g` (bounded on the lateral surface over that interval) is integrable.  Analogue of
`integrableOn_lateralDensity_of_bounded_aux`. -/
theorem integrableOn_lateralDensity_of_continuousOn_aux_tgi (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) {g : CapSpace m → ℝ}
    (hgc : ContinuousOn g (closure (thinDomain Cm Cp L R))) {M a b : ℝ}
    (hsub : Ioo a b ⊆ Ioo (-L/2) (L/2))
    (harea : IntegrableOn (areaElement Cm Cp L R) (Ioo a b))
    (hg : ∀ x ∈ Ioo a b, ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo a b) := by
  have hmeas : AEStronglyMeasurable
      (fun x => ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      (volume.restrict (Ioo a b)) :=
    aestronglyMeasurable_sphereAverage_of_continuousOn_tgi hR hL hgc measurableSet_Ioo hsub
  have hbound : IntegrableOn
      (fun x => |areaElement Cm Cp L R x| * (M * ((sphereMeasure m) univ).toReal))
      (Ioo a b) := harea.abs.mul_const _
  have key : IntegrableOn
      (fun x => areaElement Cm Cp L R x *
        ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      (Ioo a b) := by
    refine Integrable.mono' hbound (harea.aestronglyMeasurable.mul hmeas) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (sphereIntegral_abs_le_of_forall (hg x hx)) (abs_nonneg _)
  exact key.congr_fun (fun x _ => (lateralDensity_eq_areaElement g x).symm) measurableSet_Ioo

/-- The three integrability hypotheses, discharged for a `g` continuous on the closure of the
thin domain, with no bound hypothesis (the bound is produced by compactness of the closure, as in
`integrableOn_lateralDensity_of_continuous`). -/
theorem integrableOn_lateralDensity_of_continuousOn_closure_tgi (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) {g : CapSpace m → ℝ}
    (hgc : ContinuousOn g (closure (thinDomain Cm Cp L R))) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (-L/2) (-L/2 + Cm.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R g)
        (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (L/2 - Cp.K * R) (L/2)) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  obtain ⟨M, hM⟩ := (isCompact_closure_thinDomain hR hL).exists_bound_of_continuousOn hgc
  have hbd : ∀ x ∈ Ioo (-L/2) (L/2), ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M :=
    fun x hx ω => by
      simpa only [Real.norm_eq_abs] using hM _ (mem_closure_thinDomain_lateral hR hL hx ω)
  have harea1 : IntegrableOn (areaElement Cm Cp L R) (Ioo (-L/2) (-L/2 + Cm.K * R)) := by
    have h := intervalIntegrable_areaElement_left (Cm := Cm) (Cp := Cp) (L := L) hR
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le] at h
  have harea2 : IntegrableOn (areaElement Cm Cp L R)
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) := by
    have h := intervalIntegrable_areaElement_bulk (Cm := Cm) (Cp := Cp) hR hL
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le] at h
  have harea3 : IntegrableOn (areaElement Cm Cp L R) (Ioo (L/2 - Cp.K * R) (L/2)) := by
    have h := intervalIntegrable_areaElement_right (Cm := Cm) (Cp := Cp) hR hL
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le] at h
  exact ⟨integrableOn_lateralDensity_of_continuousOn_aux_tgi hR hL hgc
      (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) harea1 (fun x hx => hbd x ⟨hx.1, by linarith [hx.2]⟩),
    integrableOn_lateralDensity_of_continuousOn_aux_tgi hR hL hgc
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) harea2
      (fun x hx => hbd x ⟨by linarith [hx.1], by linarith [hx.2]⟩),
    integrableOn_lateralDensity_of_continuousOn_aux_tgi hR hL hgc
      (fun x hx => ⟨by linarith [hx.1], hx.2⟩) harea3
      (fun x hx => hbd x ⟨by linarith [hx.1], hx.2⟩)⟩

/-- **Deliverable 2.**  `ContinuousBoundaryIntegrable_tgn`, discharged. -/
theorem continuousBoundaryIntegrable_tgi (m : ℕ) (hm : 1 ≤ m) (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L) :
    ContinuousBoundaryIntegrable_tgn m L R hR hL where
  integrableOn u hc :=
    integrableOn_lateralDensity_of_continuousOn_closure_tgi hR hL (hc.pow 2)

end ContinuousBoundary

end RobinCaps.ThinDomain

end
