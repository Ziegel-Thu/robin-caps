import RobinCaps.Sobolev.RadialSlice
import RobinCaps.ThinDomain.SliceThin
import RobinCaps.ThinDomain.BulkEnergy
import RobinCaps.ThinDomain.BdSliceableGen
import RobinCaps.Compact.BoundaryForm
import RobinCaps.Cap.TraceDataHemi
import RobinCaps.ThinDomain.BdSliceableOne
import RobinCaps.ThinDomain.Boundary
import RobinCaps.ThinDomain.BoundaryPieces

/-!
# The bulk lateral trace of a weak-`H¹` function on the thin domain, general transverse dimension

This file builds, for `u : H1P (thinDomain Cm Cp L R)` on the thin domain `Ω_R` of transverse
dimension `m`, the **lateral trace on the bulk cylinder**

`bulkTrace_tgb u (x, z) = Weak.traceSphere R (slice u' x).toFun (slice u' x).grad (z / ‖z‖)`,

for `x` in the bulk interval `(x₋, x₊)` and `z ≠ 0`, where `u' = restrictBulkP_tgb hR hL u` is the
restriction of `u` to the bulk cylinder and `slice u' x` is the transverse slice at `x`
(`RobinCaps.ThinDomain.slice` of `BulkEnergy.lean`), built from the sphere trace of the
transverse slices (`RobinCaps.Sobolev.Weak.traceSphere` of `RadialSlice.lean`).

## Contents

* `bulkCyl_subset_thinDomain_tgb`, `restrictBulkP_tgb`: the restriction of `u` to the bulk
  cylinder, rebuilt from `H1P.restrictTo` of `SliceThin.lean` (the `BulkProj.lean` version is not
  importable here).
* `bulkTrace_tgb` (**deliverable 1**), together with the hard measurability step:
  `stronglyMeasurable_traceSphere_joint_tgb` (the direction-only measurability of
  `RobinCaps.Cap.stronglyMeasurable_traceSphere_th`, generalized to carry an inert axial
  parameter `x`) and `ae_radial_congr_joint_tgb` (the ball-to-radial-slice a.e. transport of
  `RobinCaps.Cap.ae_radial_congr_th`, generalized to a joint statement over `(x, w)` by an
  explicit double application of Fubini's theorem — the general "iterated a.e. on a product"
  converse used pointwise per `x` is *not* true without measurability of the exceptional set,
  so the axial and directional null sets are merged into a single measurable set and the
  polar identity is applied to a genuinely jointly-measurable nonnegative integrand).  These
  combine into `aestronglyMeasurable_bulkTrace_tgb`.
* `SphFormEqBdR_tgb`: the interface Prop recording the slice-wise identity of the sphere-trace
  form with the Rellich form `bdR`, to be supplied later by `Sobolev/SphereTraceForm.lean`.
* `bulkDensity_tgb` (**deliverable 2**): the sphere-averaged squared trace, and its integral
  identity with `bdCyl (bdR m R)` given `SphFormEqBdR_tgb`.
* `bulkDensity_eq_lateralDensity_tgb` (**deliverable 3**): identification with
  `RobinCaps.ThinDomain.lateralDensity` on the bulk, via `lateralDensity_bulk`.
* `bulkTrace_sq_integral_le_tgb` (**deliverable 4**): the trace bound on the bulk, from
  `RobinCaps.Sobolev.Weak.traceSphere_sq_integral_le` slice-wise and Fubini, without any
  interface hypothesis.
* `bulkTrace_eq_of_continuousOn_tgb` (**deliverable 5**): consistency with a continuous
  representative, from `RobinCaps.Sobolev.Weak.traceSphere_eq_of_continuous`.
* `bulkTrace_add_tgb`, `bulkTrace_smul_tgb` (**deliverable 6**): a.e. linearity in `u` on the
  lateral bulk boundary.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Compact RobinCaps.Cap

noncomputable section

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## 0. Restriction of `u` to the bulk cylinder

`RobinCaps/ThinDomain/BulkProj.lean` already builds this restriction as `restrictBulkP`, but that
file is not importable here; it is rebuilt from `H1P.restrictTo` of `SliceThin.lean`, exactly as
`BulkProj.lean` does with `HasWeakGradP.mono`. -/

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- **The open bulk cylinder sits inside the thin domain.** Rebuilt from
`RobinCaps.Domain.profile_bulk`, as `RobinCaps.ThinDomain.bulkCyl_subset_thinDomain` of
`BulkProj.lean`. -/
theorem bulkCyl_subset_thinDomain_tgb (hR : 0 < R) :
    Ioo (interfaceL Cm L R) (interfaceR Cp L R) ×ˢ transverseBall m R
      ⊆ thinDomain Cm Cp L R := by
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  have hKm : 0 < Cm.K * R := mul_pos Cm.hK hR
  have hKp : 0 < Cp.K * R := mul_pos Cp.hK hR
  have hzR : ‖z‖ < R := by
    have : z ∈ Metric.ball (0 : E) R := hz
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hx1 : -L / 2 + Cm.K * R < x := hx.1
  have hx2 : x < L / 2 - Cp.K * R := hx.2
  refine ⟨by linarith, by linarith, ?_⟩
  show ‖z‖ < profile Cm Cp L R x
  rw [profile_bulk hx1.le hx2.le]
  exact hzR

/-- **Restriction of `u` to the bulk cylinder** (deliverable-0 helper). -/
def restrictBulkP_tgb (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    H1P (bulkCyl (interfaceL Cm L R) (interfaceR Cp L R) m R) :=
  u.restrictTo (bulkCyl_subset_thinDomain_tgb hR)

@[simp] theorem restrictBulkP_tgb_toFun (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    (restrictBulkP_tgb hR u).toFun = u.toFun := rfl

/-! ## 1. The bulk lateral trace (deliverable 1) -/

/-- **The bulk lateral trace.**  At an axial coordinate `x` in the bulk interval
`(x₋, x₊) = (interfaceL Cm L R, interfaceR Cp L R)` and a transverse point `z ≠ 0`, the trace is
the sphere trace of the transverse slice `slice (restrictBulkP_tgb hR u) x` in direction
`z / ‖z‖`.  It is set to `0` off this region. -/
def bulkTrace_tgb (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    CapSpace m → ℝ :=
  fun p =>
    if p.1 ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) ∧ p.2 ≠ 0 then
      Weak.traceSphere R (slice (restrictBulkP_tgb hR u) p.1).toFun
        (slice (restrictBulkP_tgb hR u) p.1).grad (‖p.2‖⁻¹ • p.2)
    else 0

/-- **On the bulk, at a sphere point `R • w`, the trace is the sphere trace of the slice in
direction `w`.** The normalisation `‖R • w‖ = R` collapses `(R • w) / ‖R • w‖` to `w`. -/
theorem bulkTrace_tgb_apply (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {x : ℝ}
    (hx : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)) (w : sphere (0 : E) 1) :
    bulkTrace_tgb hR hL u (x, R • (w : E))
      = Weak.traceSphere R (slice (restrictBulkP_tgb hR u) x).toFun
          (slice (restrictBulkP_tgb hR u) x).grad (w : E) := by
  have hwn : ‖(w : E)‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
  have hRw : ‖R • (w : E)‖ = R := by
    rw [norm_smul, hwn, mul_one, Real.norm_eq_abs, abs_of_pos hR]
  have hRwne : R • (w : E) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hRw
    exact hR.ne' hRw.symm
  have hquot : ‖R • (w : E)‖⁻¹ • (R • (w : E)) = (w : E) := by
    rw [hRw, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  simp only [bulkTrace_tgb, hx, hRwne, ne_eq, not_false_eq_true, and_self, if_true]
  rw [hquot]

/-! ## 2. Joint measurability infrastructure

The hard part of deliverable 1.  `stronglyMeasurable_traceSphere_joint_tgb` generalizes
`RobinCaps.Cap.stronglyMeasurable_traceSphere_th` by threading an inert axial parameter `x`
through the same parametric-integral argument.  `ae_radial_congr_joint_tgb` generalizes
`RobinCaps.Cap.ae_radial_congr_th` from a single ball to the bulk cylinder: since the general
converse "iterated a.e. on a product measure" is *not* true without measurability of the
exceptional set (`MeasureTheory.measure_prod_null_of_ae_null`), the mismatch set is embedded
in a single *measurable* null superset of the bulk cylinder, and polar coordinates are
applied to the (jointly measurable, nonnegative) indicator of that superset via a genuine
iterated/product Fubini identity (`MeasureTheory.integral_prod`), rather than argued
pointwise in `x`. -/

theorem isFiniteMeasure_sphereMeasure_tgb : IsFiniteMeasure (sphereMeasure m) := by
  refine ⟨?_⟩
  rw [Measure.toSphere_apply_univ]
  exact ENNReal.mul_lt_top (by finiteness) measure_ball_lt_top

theorem stronglyMeasurable_traceSphere_joint_tgb {R : ℝ}
    {V : ℝ × E → ℝ} {G : ℝ × E → E}
    (hV : Measurable V) (hG : Measurable G) :
    StronglyMeasurable (fun p : ℝ × sphere (0 : E) 1 =>
      traceSphere R (fun z => V (p.1, z)) (fun z => G (p.1, z)) (p.2 : E)) := by
  classical
  have hsmul : Measurable (fun p : (ℝ × sphere (0 : E) 1) × ℝ =>
      p.2 • ((p.1.2 : sphere (0 : E) 1) : E)) :=
    measurable_snd.smul (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))
  have hH : StronglyMeasurable (fun p : (ℝ × sphere (0 : E) 1) × ℝ =>
      inner ℝ (G (p.1.1, p.2 • ((p.1.2 : sphere (0 : E) 1) : E)))
        ((p.1.2 : sphere (0 : E) 1) : E)) := by
    have hGcomp : Measurable (fun p : (ℝ × sphere (0 : E) 1) × ℝ =>
        G (p.1.1, p.2 • ((p.1.2 : sphere (0 : E) 1) : E))) :=
      hG.comp (Measurable.prodMk (measurable_fst.comp measurable_fst) hsmul)
    exact (hGcomp.inner (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))
      ).stronglyMeasurable
  have hInd : ∀ S : Set ℝ, StronglyMeasurable (fun q : ℝ × sphere (0 : E) 1 => ∫ t in S,
      inner ℝ (G (q.1, t • ((q.2 : sphere (0 : E) 1) : E))) ((q.2 : sphere (0 : E) 1) : E)) :=
    fun S => hH.integral_prod_right' (ν := volume.restrict S)
  have hmeasS : ∀ b : ℝ, MeasurableSet
      {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ | b < z.2 ∧ z.2 ≤ z.1.2} :=
    fun b => (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hmeasS' : ∀ b : ℝ, MeasurableSet
      {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ | z.1.2 < z.2 ∧ z.2 ≤ b} :=
    fun b => (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hG1 : StronglyMeasurable
      (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
        inner ℝ (G (z.1.1.1, z.2 • ((z.1.1.2 : sphere (0 : E) 1) : E)))
          ((z.1.1.2 : sphere (0 : E) 1) : E)) :=
    hH.comp_measurable (Measurable.prodMk (measurable_fst.comp measurable_fst) measurable_snd)
  have hJ1 : ∀ b : ℝ, StronglyMeasurable
      (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (G (q.1.1, t • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E)) := by
    intro b
    have hF : StronglyMeasurable
        (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (G (z.1.1.1, t •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2) := by
      have heq : (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc b z.1.2).indicator (fun t => inner ℝ (G (z.1.1.1, t •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2)
          = Set.indicator {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2}
            (fun z => inner ℝ (G (z.1.1.1, z.2 • ((z.1.1.2 : sphere (0 : E) 1) : E)))
              ((z.1.1.2 : sphere (0 : E) 1) : E)) := by
        funext z
        by_cases hz : b < z.2 ∧ z.2 ≤ z.1.2
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc b z.1.2 from hz),
            Set.indicator_of_mem (show z ∈ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc b z.1.2 from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
                b < z.2 ∧ z.2 ≤ z.1.2} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS b)
    have hEq : (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc b q.2,
        inner ℝ (G (q.1.1, t • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E))
        = fun q => ∫ y : ℝ, (Ioc b q.2).indicator
          (fun t => inner ℝ (G (q.1.1, t • ((q.1.2 : sphere (0 : E) 1) : E)))
            ((q.1.2 : sphere (0 : E) 1) : E)) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF.integral_prod_right' (ν := (volume : Measure ℝ))
  have hJ2 : ∀ b : ℝ, StronglyMeasurable
      (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (G (q.1.1, t • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E)) := by
    intro b
    have hF : StronglyMeasurable
        (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (G (z.1.1.1, t •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2) := by
      have heq : (fun z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ =>
          (Ioc z.1.2 b).indicator (fun t => inner ℝ (G (z.1.1.1, t •
            ((z.1.1.2 : sphere (0 : E) 1) : E)))
            ((z.1.1.2 : sphere (0 : E) 1) : E)) z.2)
          = Set.indicator {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b}
            (fun z => inner ℝ (G (z.1.1.1, z.2 • ((z.1.1.2 : sphere (0 : E) 1) : E)))
              ((z.1.1.2 : sphere (0 : E) 1) : E)) := by
        funext z
        by_cases hz : z.1.2 < z.2 ∧ z.2 ≤ b
        · rw [Set.indicator_of_mem (show z.2 ∈ Ioc z.1.2 b from hz),
            Set.indicator_of_mem (show z ∈ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
              z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
        · rw [Set.indicator_of_notMem (show z.2 ∉ Ioc z.1.2 b from hz),
            Set.indicator_of_notMem
              (show z ∉ {z : ((ℝ × sphere (0 : E) 1) × ℝ) × ℝ |
                z.1.2 < z.2 ∧ z.2 ≤ b} from hz)]
      rw [heq]
      exact hG1.indicator (hmeasS' b)
    have hEq : (fun q : (ℝ × sphere (0 : E) 1) × ℝ => ∫ t in Ioc q.2 b,
        inner ℝ (G (q.1.1, t • ((q.1.2 : sphere (0 : E) 1) : E)))
          ((q.1.2 : sphere (0 : E) 1) : E))
        = fun q => ∫ y : ℝ, (Ioc q.2 b).indicator
          (fun t => inner ℝ (G (q.1.1, t • ((q.1.2 : sphere (0 : E) 1) : E)))
            ((q.1.2 : sphere (0 : E) 1) : E)) y := by
      funext q
      exact (integral_indicator measurableSet_Ioc).symm
    rw [hEq]
    exact hF.integral_prod_right' (ν := (volume : Measure ℝ))
  have hinner : StronglyMeasurable
      (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
        V (q.1.1, q.2 • ((q.1.2 : sphere (0 : E) 1) : E))
          - ∫ t in ((R / 2 + R) / 2)..q.2,
            inner ℝ (G (q.1.1, t • ((q.1.2 : sphere (0 : E) 1) : E)))
              ((q.1.2 : sphere (0 : E) 1) : E)) := by
    have hsmul' : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
        (q.1.1, q.2 • ((q.1.2 : sphere (0 : E) 1) : E))) :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.smul (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)))
    have hv' : StronglyMeasurable
        (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
          V (q.1.1, q.2 • ((q.1.2 : sphere (0 : E) 1) : E))) := (hV.comp hsmul').stronglyMeasurable
    exact hv'.sub ((hJ1 ((R / 2 + R) / 2)).sub (hJ2 ((R / 2 + R) / 2)))
  have hI1 := hinner.integral_prod_right' (ν := volume.restrict (Ioo (R / 2) R))
  have hI2 := ((hInd (Ioc ((R / 2 + R) / 2) R)).sub (hInd (Ioc R ((R / 2 + R) / 2))))
  exact (hI1.const_mul (2 / R)).add hI2

theorem ae_radial_congr_joint_tgb (hm : 1 ≤ m) {a b R : ℝ}
    {α : Type*} {f₁ f₂ : CapSpace m → α}
    (h : f₁ =ᵐ[volume.restrict (bulkCyl a b m R)] f₂) :
    ∀ᵐ p : ℝ × sphere (0 : E) 1 ∂((volume.restrict (Ioo a b)).prod (sphereMeasure m)),
      ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
        f₁ (p.1, r • (p.2 : E)) = f₂ (p.1, r • (p.2 : E)) := by
  classical
  haveI : IsFiniteMeasure (sphereMeasure m) := isFiniteMeasure_sphereMeasure_tgb
  haveI hIooFin : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  haveI hBallFin : IsFiniteMeasure (volume.restrict (transverseBall m R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  haveI hBulkFin : IsFiniteMeasure (volume.restrict (bulkCyl a b m R)) := by
    rw [volume_restrict_bulkCyl]; infer_instance
  have hne : volume.restrict (bulkCyl a b m R) {p | ¬ f₁ p = f₂ p} = 0 := ae_iff.1 h
  obtain ⟨N, hNsup, hNmeas, hN0⟩ := exists_measurable_superset_of_null hne
  set indN : CapSpace m → ℝ := N.indicator (fun _ => (1 : ℝ)) with hindN_def
  have hindNmeas : Measurable indN := measurable_const.indicator hNmeas
  have hindNnn : ∀ p, 0 ≤ indN p := fun p => by
    by_cases hp : p ∈ N
    · rw [hindN_def]; simp [Set.indicator_of_mem hp]
    · rw [hindN_def]; simp [Set.indicator_of_notMem hp]
  have hindNle : ∀ p, indN p ≤ 1 := fun p => by
    by_cases hp : p ∈ N
    · rw [hindN_def]; simp [Set.indicator_of_mem hp]
    · rw [hindN_def]; simp [Set.indicator_of_notMem hp]
  have hindNint : Integrable indN (volume.restrict (bulkCyl a b m R)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hindNmeas.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hindNnn p)]
    exact hindNle p
  have hindNzero : (∫ p in bulkCyl a b m R, indN p) = 0 := by
    refine integral_eq_zero_of_ae ?_
    have hmemN : ∀ᵐ p ∂(volume.restrict (bulkCyl a b m R)), p ∉ N := by
      rw [ae_iff]; simpa using hN0
    filter_upwards [hmemN] with p hp
    rw [hindN_def]
    exact Set.indicator_of_notMem hp _
  -- the joint (x, w, r) function whose r-integral is Θ
  set H : (ℝ × sphere (0 : E) 1) × ℝ → ℝ :=
    fun q => q.2 ^ (m - 1) * indN (q.1.1, q.2 • (q.1.2 : E)) with hH_def
  have hHmeas : Measurable H := by
    have h1 : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ => q.2 ^ (m - 1)) :=
      (measurable_snd).pow_const _
    have h2 : Measurable (fun q : (ℝ × sphere (0 : E) 1) × ℝ =>
        indN (q.1.1, q.2 • (q.1.2 : E))) :=
      hindNmeas.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.smul (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))))
    exact h1.mul h2
  set Θ : ℝ × sphere (0 : E) 1 → ℝ :=
    fun p => ∫ r in Ioo (0 : ℝ) R, H (p, r) with hΘ_def
  have hΘmeas : StronglyMeasurable Θ := by
    have := hHmeas.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) R))
    simpa [hΘ_def] using this
  have hΘnn : ∀ p, 0 ≤ Θ p := by
    intro p
    rw [hΘ_def]
    refine setIntegral_nonneg measurableSet_Ioo (fun r hr => ?_)
    exact mul_nonneg (pow_nonneg hr.1.le _) (hindNnn _)
  have hpowint : IntegrableOn (fun r : ℝ => r ^ (m - 1)) (Ioo (0 : ℝ) R) :=
    ((continuous_pow (m - 1)).integrableOn_Icc (a := (0:ℝ)) (b := R)).mono_set Ioo_subset_Icc_self
  set C : ℝ := ∫ r in Ioo (0 : ℝ) R, r ^ (m - 1) with hC_def
  have hHrint : ∀ p : ℝ × sphere (0 : E) 1,
      IntegrableOn (fun r => H (p, r)) (Ioo (0 : ℝ) R) := by
    intro p
    refine Integrable.mono' hpowint
      ((hHmeas.comp measurable_prodMk_left).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hH_def]
    have hrp : (0:ℝ) ≤ r ^ (m - 1) := pow_nonneg hr.1.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrp (hindNnn _))]
    calc r ^ (m - 1) * indN (p.1, r • (p.2 : E)) ≤ r ^ (m - 1) * 1 :=
          mul_le_mul_of_nonneg_left (hindNle _) hrp
      _ = r ^ (m - 1) := mul_one _
  have hΘle : ∀ p, Θ p ≤ C := by
    intro p
    rw [hΘ_def, hC_def]
    refine setIntegral_mono_on (hHrint p) hpowint measurableSet_Ioo (fun r hr => ?_)
    rw [hH_def]
    have hrp : (0:ℝ) ≤ r ^ (m - 1) := pow_nonneg hr.1.le _
    calc r ^ (m - 1) * indN (p.1, r • (p.2 : E)) ≤ r ^ (m - 1) * 1 :=
          mul_le_mul_of_nonneg_left (hindNle _) hrp
      _ = r ^ (m - 1) := mul_one _
  have hΘint : Integrable Θ ((volume.restrict (Ioo a b)).prod (sphereMeasure m)) := by
    refine Integrable.mono' (integrable_const C) hΘmeas.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hΘnn p)]
    exact hΘle p
  have hFubini : (∫ p, Θ p ∂((volume.restrict (Ioo a b)).prod (sphereMeasure m)))
      = ∫ x in Ioo a b, (∫ w, Θ (x, w) ∂(sphereMeasure m)) := integral_prod Θ hΘint
  have hindNprod : Integrable indN
      ((volume.restrict (Ioo a b)).prod (volume.restrict (transverseBall m R))) := by
    rw [← volume_restrict_bulkCyl]; exact hindNint
  have hae_x_int : ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      IntegrableOn (fun z => indN (x, z)) (transverseBall m R) := hindNprod.prod_right_ae
  have hae_x_eq : ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      (∫ z in transverseBall m R, indN (x, z)) = (∫ w, Θ (x, w) ∂(sphereMeasure m)) := by
    filter_upwards [hae_x_int] with x hx
    exact integral_ball_polar_symm hm hx
  have hkey : (∫ x in Ioo a b, (∫ w, Θ (x, w) ∂(sphereMeasure m)))
      = ∫ x in Ioo a b, ∫ z in transverseBall m R, indN (x, z) :=
    integral_congr_ae (hae_x_eq.mono fun x hx => hx.symm)
  have hprodzero : (∫ p, Θ p ∂((volume.restrict (Ioo a b)).prod (sphereMeasure m))) = 0 := by
    rw [hFubini, hkey, ← integral_bulk_eq hindNint, hindNzero]
  have hΘzero : ∀ᵐ p ∂((volume.restrict (Ioo a b)).prod (sphereMeasure m)), Θ p = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hΘnn) hΘint).1 hprodzero
  filter_upwards [hΘzero] with p hp
  have hHnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) R)] fun r => H (p, r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hH_def]
    exact mul_nonneg (pow_nonneg hr.1.le _) (hindNnn _)
  have hrzero : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), H (p, r) = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hHnn (hHrint p)).1 hp
  filter_upwards [hrzero, ae_restrict_mem measurableSet_Ioo] with r hr0 hrmem
  rw [hH_def] at hr0
  have hrp : (0:ℝ) < r ^ (m - 1) := pow_pos hrmem.1 _
  have hind0 : indN (p.1, r • (p.2 : E)) = 0 := by
    rcases mul_eq_zero.1 hr0 with h' | h'
    · exact absurd h' hrp.ne'
    · exact h'
  have hnotN : (p.1, r • (p.2 : E)) ∉ N := by
    intro hmemN
    rw [hindN_def, Set.indicator_of_mem hmemN] at hind0
    exact one_ne_zero hind0
  by_contra hcon
  exact hnotN (hNsup hcon)

/-! ## 3. Deliverable 1: joint measurability of the bulk trace -/

/-- **The bulk lateral trace is jointly almost-everywhere strongly measurable** in the axial
coordinate and the direction.  `slice (restrictBulkP_tgb hR u)` is `dite`-defined and therefore
not manifestly measurable in `x`; the argument replaces it a.e. by the sphere trace of the
strongly measurable representatives `F, Gv` of `u'.toFun, u'.gz` (`MemLp.aestronglyMeasurable.mk`)
using `stronglyMeasurable_traceSphere_joint_tgb` for the formula and
`ae_radial_congr_joint_tgb` to transport the representative mismatch (null on the bulk cylinder)
to a joint a.e. statement in the direction and the radius. -/
theorem aestronglyMeasurable_bulkTrace_tgb (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    AEStronglyMeasurable
      (fun p : ℝ × sphere (0 : E) 1 => bulkTrace_tgb hR hL u (p.1, R • (p.2 : E)))
      ((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)) := by
  set u' := restrictBulkP_tgb hR u with hu'_def
  set F : CapSpace m → ℝ := u'.memL2.aestronglyMeasurable.mk u'.toFun with hF_def
  set Gv : CapSpace m → E := u'.gz_memL2.aestronglyMeasurable.mk u'.gz with hGv_def
  have hFmeas : Measurable F := u'.memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hGvmeas : Measurable Gv := u'.gz_memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hFeq := u'.memL2.aestronglyMeasurable.ae_eq_mk
  have hGveq := u'.gz_memL2.aestronglyMeasurable.ae_eq_mk
  refine ⟨fun p => traceSphere R (fun z => F (p.1, z)) (fun z => Gv (p.1, z)) (p.2 : E),
    stronglyMeasurable_traceSphere_joint_tgb hFmeas hGvmeas, ?_⟩
  have h0 : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      p.1 ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  have h1 : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      IsGoodSlice u' p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_isGoodSlice u')
  have h2 := ae_radial_congr_joint_tgb (m := m) hm
    (a := interfaceL Cm L R) (b := interfaceR Cp L R) (R := R) hFeq
  have h3 := ae_radial_congr_joint_tgb (m := m) hm
    (a := interfaceL Cm L R) (b := interfaceR Cp L R) (R := R) hGveq
  filter_upwards [h0, h1, h2, h3] with p hxmem hgood hp2 hp3
  rw [bulkTrace_tgb_apply hR hL u hxmem p.2, slice_toFun hgood, slice_grad hgood]
  exact traceSphere_congr_th hR hp2 hp3

/-! ## 4. The interface with `Sobolev/SphereTraceForm.lean` -/

/-- **The sphere-trace form agrees with the Rellich form `bdR` on `H¹(B_R)`.**  Supplied later by
`RobinCaps/Sobolev/SphereTraceForm.lean`. -/
def SphFormEqBdR_tgb (m : ℕ) (R : ℝ) : Prop :=
  ∀ v : Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R),
    R ^ (m - 1) * ∫ w, (Weak.traceSphere R v.toFun v.grad (w : EuclideanSpace ℝ (Fin m))) ^ 2
        ∂(sphereMeasure m)
      = bdR m R v v

/-! ## 5. Deliverable 2: the bulk trace density -/

/-- **The bulk trace density** `R^{m-1} ∫_{S^{m-1}} (Tr u)(x, Rω)² dσ(ω)`. -/
def bulkDensity_tgb (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R))
    (x : ℝ) : ℝ :=
  R ^ (m - 1) * ∫ w : sphere (0 : E) 1, (bulkTrace_tgb hR hL u (x, R • (w : E))) ^ 2
    ∂(sphereMeasure m)

/-- **On the whole bulk interval, given the interface, the bulk density is the Rellich form of
the transverse slice.**  Unlike the measurability step this holds for *every* `x` in the bulk
interval, not merely almost every one: `bulkTrace_tgb_apply` is a pointwise identity there. -/
theorem bulkDensity_eq_bdR_tgb (hSph : SphFormEqBdR_tgb m R) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) {x : ℝ}
    (hx : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)) :
    bulkDensity_tgb hR hL u x
      = bdR m R (slice (restrictBulkP_tgb hR u) x) (slice (restrictBulkP_tgb hR u) x) := by
  have hpt : (fun w : sphere (0 : E) 1 => (bulkTrace_tgb hR hL u (x, R • (w : E))) ^ 2)
      = fun w : sphere (0 : E) 1 =>
        (Weak.traceSphere R (slice (restrictBulkP_tgb hR u) x).toFun
          (slice (restrictBulkP_tgb hR u) x).grad (w : E)) ^ 2 :=
    funext fun w => by rw [bulkTrace_tgb_apply hR hL u hx w]
  rw [bulkDensity_tgb, hpt]
  exact hSph (slice (restrictBulkP_tgb hR u) x)

/-- **The bulk trace density is integrable on the bulk interval, given the interface.** -/
theorem integrableOn_bulkDensity_tgb (hSph : SphFormEqBdR_tgb m R) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (bulkDensity_tgb hR hL u) (Ioo (interfaceL Cm L R) (interfaceR Cp L R)) := by
  have hint := (bdSliceable_bdR_bsg hR (interfaceL Cm L R) (interfaceR Cp L R)).integrableOn
    (restrictBulkP_tgb hR u) (restrictBulkP_tgb hR u)
  exact hint.congr_fun (fun x hx => (bulkDensity_eq_bdR_tgb hSph hR hL u hx).symm)
    measurableSet_Ioo

/-- **The bulk trace density integrates, over the bulk interval, to `bdCyl (bdR m R)` on the
restriction of `u`, given the interface.** -/
theorem integral_bulkDensity_tgb (hSph : SphFormEqBdR_tgb m R) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), bulkDensity_tgb hR hL u x)
      = bdCyl (bdR m R) (restrictBulkP_tgb hR u) (restrictBulkP_tgb hR u) := by
  rw [bdCyl]
  exact setIntegral_congr_fun measurableSet_Ioo (fun x hx => bulkDensity_eq_bdR_tgb hSph hR hL u hx)

/-! ## 6. Deliverable 3: identification with `lateralDensity` -/

/-- **On the bulk interval the trace density is the lateral density of the squared trace.**
On the bulk the profile is constant `R` with vanishing derivative (`profile_bulk`,
`deriv_profile_bulk`), which is exactly `lateralDensity_bulk`; as with `bulkDensity_eq_bdR_tgb`
this holds for every `x` in the bulk interval, not merely almost every one. -/
theorem bulkDensity_eq_lateralDensity_tgb (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {x : ℝ}
    (hx : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)) :
    bulkDensity_tgb hR hL u x
      = lateralDensity Cm Cp L R (fun p => (bulkTrace_tgb hR hL u p) ^ 2) x := by
  have h1 : -L / 2 + Cm.K * R < x := hx.1
  have h2 : x < L / 2 - Cp.K * R := hx.2
  rw [lateralDensity_bulk _ h1 h2, bulkDensity_tgb]

/-! ## 7. Deliverable 4: the trace bound on the bulk (no interface needed) -/

/-- **The trace bound on the bulk.**  Slice-wise `traceSphere_sq_integral_le` plus Fubini
(`integrableOn_NB_slice`, `integrableOn_dirichlet_slice`, `massP_eq_integral_NB_slice`,
`dirichletP_eq_axial_add_slice`): no interface hypothesis is needed. -/
theorem bulkDensity_integral_le_tgb (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), bulkDensity_tgb hR hL u x)
      ≤ R ^ (m - 1) * max ((4 / R) * ((R / 2) ^ (m - 1))⁻¹) (R * ((R / 2) ^ (m - 1))⁻¹)
        * (massP (restrictBulkP_tgb hR u) + dirichletP (restrictBulkP_tgb hR u)) := by
  set u' := restrictBulkP_tgb hR u with hu'_def
  set C := max ((4 / R) * ((R / 2) ^ (m - 1))⁻¹) (R * ((R / 2) ^ (m - 1))⁻¹) with hC_def
  have hRpow : (0 : ℝ) ≤ R ^ (m - 1) := by positivity
  have hCnn : 0 ≤ C := le_trans (by positivity) (le_max_left _ _)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))]
      (bulkDensity_tgb hR hL u) :=
    Filter.Eventually.of_forall fun x => mul_nonneg hRpow (integral_nonneg fun w => sq_nonneg _)
  have hmaj : Integrable (fun x => R ^ (m - 1) * C * (NB (slice u' x) + Weak.dirichlet (slice u' x)))
      (volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))) :=
    ((integrableOn_NB_slice u').add (integrableOn_dirichlet_slice u')).const_mul _
  have hle : (bulkDensity_tgb hR hL u)
      ≤ᵐ[volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))]
      fun x => R ^ (m - 1) * C * (NB (slice u' x) + Weak.dirichlet (slice u' x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hpt : bulkDensity_tgb hR hL u x
        = R ^ (m - 1) * ∫ w : sphere (0 : E) 1,
            (Weak.traceSphere R (slice u' x).toFun (slice u' x).grad (w : E)) ^ 2
              ∂(sphereMeasure m) := by
      rw [bulkDensity_tgb]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      dsimp only
      rw [bulkTrace_tgb_apply hR hL u hx w]
    rw [hpt]
    calc R ^ (m - 1) * ∫ w : sphere (0 : E) 1,
          (Weak.traceSphere R (slice u' x).toFun (slice u' x).grad (w : E)) ^ 2
            ∂(sphereMeasure m)
        ≤ R ^ (m - 1) * (C * (NB (slice u' x) + Weak.dirichlet (slice u' x))) :=
          mul_le_mul_of_nonneg_left (traceSphere_sq_integral_le hm hR (slice u' x)) hRpow
      _ = R ^ (m - 1) * C * (NB (slice u' x) + Weak.dirichlet (slice u' x)) := by ring
  have hmono := integral_mono_of_nonneg hnn hmaj hle
  have hstep1 : (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
      (NB (slice u' x) + Weak.dirichlet (slice u' x)))
      = massP u' + ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
          Weak.dirichlet (slice u' x) := by
    rw [integral_add (integrableOn_NB_slice u') (integrableOn_dirichlet_slice u'),
      ← massP_eq_integral_NB_slice]
  have hstep2 : (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), Weak.dirichlet (slice u' x))
      ≤ dirichletP u' := by
    have hax := dirichletP_eq_axial_add_slice u'
    linarith [axialDirichletP_nonneg u']
  rw [integral_const_mul, hstep1] at hmono
  have hfin : massP u' + ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
      Weak.dirichlet (slice u' x) ≤ massP u' + dirichletP u' := by linarith
  calc (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), bulkDensity_tgb hR hL u x)
      ≤ R ^ (m - 1) * C * (massP u'
          + ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), Weak.dirichlet (slice u' x)) :=
        hmono
    _ ≤ R ^ (m - 1) * C * (massP u' + dirichletP u') :=
        mul_le_mul_of_nonneg_left hfin (mul_nonneg hRpow hCnn)

/-! ## 8. Deliverable 5: consistency with a continuous representative -/

/-- **A bulk sphere point lies in the closure of the thin domain.**  For `x` in the bulk interval
and `r < R`, `(x, r • w) ∈ thinDomain` (the transverse slice is `ball 0 R`); letting `r → R⁻`
and using continuity of `r ↦ (x, r • w)` places the limit point `(x, R • w)` in the closure. -/
theorem bulkSpherePt_mem_closure_thinDomain_tgb (hR : 0 < R) {x : ℝ}
    (hx : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)) (w : sphere (0 : E) 1) :
    (x, R • (w : E)) ∈ closure (thinDomain Cm Cp L R) := by
  have hcont : Continuous (fun r : ℝ => (x, r • (w : E)) : ℝ → CapSpace m) :=
    continuous_const.prodMk (continuous_id.smul continuous_const)
  have htendsto : Tendsto (fun r : ℝ => (x, r • (w : E))) (𝓝[<] R) (𝓝 (x, R • (w : E))) :=
    (hcont.tendsto R).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htendsto ?_
  have h1 : ∀ᶠ r in 𝓝[<] R, r ∈ Iio R := self_mem_nhdsWithin
  have h2 : ∀ᶠ r in 𝓝[<] R, (0 : ℝ) < r := (eventually_gt_nhds hR).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2] with r hr1 hr2
  refine bulkCyl_subset_thinDomain_tgb hR ⟨hx, ?_⟩
  show r • (w : E) ∈ ball (0 : E) R
  rw [mem_ball_zero_iff, norm_smul_sphere hr2 w]
  exact hr1

/-- A whole open radius, not merely the endpoint, sits in the closure of the thin domain: for
`0 < r ≤ R`, `r < R` puts the point directly in the bulk cylinder (hence in the thin domain) and
`r = R` is `bulkSpherePt_mem_closure_thinDomain_tgb`. -/
theorem bulkRadialPt_mem_closure_thinDomain_tgb (hR : 0 < R) {x : ℝ}
    (hx : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)) (w : sphere (0 : E) 1) {r : ℝ}
    (hr0 : 0 < r) (hrR : r ≤ R) : (x, r • (w : E)) ∈ closure (thinDomain Cm Cp L R) := by
  rcases hrR.lt_or_eq with hlt | heq
  · refine subset_closure (bulkCyl_subset_thinDomain_tgb hR ⟨hx, ?_⟩)
    show r • (w : E) ∈ ball (0 : E) R
    rw [mem_ball_zero_iff, norm_smul_sphere hr0 w]
    exact hlt
  · rw [heq]
    exact bulkSpherePt_mem_closure_thinDomain_tgb hR hx w

/-- **Deliverable 5: consistency with a continuous representative.**  If `u.toFun` is continuous
on the closure of the thin domain, then for a.e. `x` in the bulk interval and a.e. direction `w`
the bulk trace agrees with the restriction of `u.toFun` to the lateral sphere.  The radial
segments `[R/2, R] · w` stay inside the closure of the thin domain
(`bulkRadialPt_mem_closure_thinDomain_tgb`), so `RobinCaps.Cap.traceSphere_eq_of_continuousOn_th`
applies to the transverse slice without requiring global continuity of `u.toFun`. -/
theorem bulkTrace_eq_of_continuousOn_tgb (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R))
    (hcont : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        bulkTrace_tgb hR hL u (x, R • (w : E))
          = u.toFun (x, R • (w : E)) := by
  set u' := restrictBulkP_tgb hR u with hu'_def
  filter_upwards [ae_isGoodSlice u', ae_restrict_mem measurableSet_Ioo] with x hgood hx
  have hcont' : ∀ w : sphere (0 : E) 1,
      ContinuousOn (fun r : ℝ => (slice u' x).toFun (r • (w : E))) (Icc (R / 2) R) := by
    intro w
    have heq : (fun r : ℝ => (slice u' x).toFun (r • (w : E)))
        = fun r : ℝ => u.toFun (x, r • (w : E)) := by
      funext r; rw [slice_toFun hgood, restrictBulkP_tgb_toFun]
    rw [heq]
    have hmap : MapsTo (fun r : ℝ => (x, r • (w : E))) (Icc (R / 2) R)
        (closure (thinDomain Cm Cp L R)) := fun r hr =>
      bulkRadialPt_mem_closure_thinDomain_tgb hR hx w (by linarith [hr.1, hR]) hr.2
    exact hcont.comp
      ((continuous_const.prodMk (continuous_id.smul continuous_const)).continuousOn) hmap
  have h := traceSphere_eq_of_continuousOn_th hm hR (slice u' x) hcont'
  filter_upwards [h] with w hw
  rw [bulkTrace_tgb_apply hR hL u hx w, hw, slice_toFun hgood, restrictBulkP_tgb_toFun]

/-! ## 9. Deliverable 6: a.e. linearity in `u` -/

theorem restrictBulkP_tgb_add (hR : 0 < R) (u v : H1P (thinDomain Cm Cp L R)) :
    restrictBulkP_tgb hR (u + v) = restrictBulkP_tgb hR u + restrictBulkP_tgb hR v :=
  H1P.ext rfl rfl rfl

theorem restrictBulkP_tgb_smul (hR : 0 < R) (c : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    restrictBulkP_tgb hR (c • u) = c • restrictBulkP_tgb hR u :=
  H1P.ext rfl rfl rfl

/-- `IsGoodSlice` is additive: if `x` is jointly good for `u` and `v` it is good for `u + v`. -/
theorem isGoodSlice_add_tgb {a b : ℝ} {u v : H1P (bulkCyl a b m R)} {x : ℝ}
    (hu : IsGoodSlice u x) (hv : IsGoodSlice v x) : IsGoodSlice (u + v) x := by
  have hteq : (fun z => (u + v).toFun (x, z))
      = (fun z => u.toFun (x, z)) + fun z => v.toFun (x, z) := by
    funext z; simp [H1P.add_toFun]
  have hgeq : (fun z => (u + v).gz (x, z)) = (fun z => u.gz (x, z)) + fun z => v.gz (x, z) := by
    funext z; simp [H1P.add_gz]
  refine ⟨?_, ?_, ?_⟩
  · rw [hteq, hgeq]; exact Weak.HasWeakGrad.add hu.2.1 hv.2.1 hu.2.2 hv.2.2 hu.1 hv.1
  · rw [hteq]; exact hu.2.1.add hv.2.1
  · rw [hgeq]; exact hu.2.2.add hv.2.2

/-- `IsGoodSlice` is homogeneous. -/
theorem isGoodSlice_smul_tgb {a b : ℝ} (c : ℝ) {u : H1P (bulkCyl a b m R)} {x : ℝ}
    (hu : IsGoodSlice u x) : IsGoodSlice (c • u) x := by
  have hteq : (fun z => (c • u).toFun (x, z)) = c • fun z => u.toFun (x, z) := by
    funext z; simp [H1P.smul_toFun]
  have hgeq : (fun z => (c • u).gz (x, z)) = c • fun z => u.gz (x, z) := by
    funext z; simp [H1P.smul_gz]
  refine ⟨?_, ?_, ?_⟩
  · rw [hteq, hgeq]; exact Weak.HasWeakGrad.smul c hu.1
  · rw [hteq]; exact hu.2.1.const_smul c
  · rw [hgeq]; exact hu.2.2.const_smul c

/-- `slice` is additive on a jointly good axial coordinate. -/
theorem slice_add_tgb {a b : ℝ} {u v : H1P (bulkCyl a b m R)} {x : ℝ}
    (hu : IsGoodSlice u x) (hv : IsGoodSlice v x) :
    slice (u + v) x = slice u x + slice v x := by
  have hgooduv := isGoodSlice_add_tgb hu hv
  refine Weak.H1.ext ?_ ?_
  · rw [slice_toFun hgooduv, Weak.H1.add_toFun, slice_toFun hu, slice_toFun hv]
    funext z; simp [H1P.add_toFun]
  · rw [slice_grad hgooduv, Weak.H1.add_grad, slice_grad hu, slice_grad hv]
    funext z; simp [H1P.add_gz]

/-- `slice` is homogeneous on a good axial coordinate. -/
theorem slice_smul_tgb {a b : ℝ} (c : ℝ) {u : H1P (bulkCyl a b m R)} {x : ℝ}
    (hu : IsGoodSlice u x) : slice (c • u) x = c • slice u x := by
  have hgoodc := isGoodSlice_smul_tgb c hu
  refine Weak.H1.ext ?_ ?_
  · rw [slice_toFun hgoodc, Weak.H1.smul_toFun, slice_toFun hu]
    funext z; simp [H1P.smul_toFun]
  · rw [slice_grad hgoodc, Weak.H1.smul_grad, slice_grad hu]
    funext z; simp [H1P.smul_gz]

/-- **The sphere trace is a.e. additive.**  The formula is a finite combination of ordinary and
interval integrals of `(u, g)`; each piece is additive by `intervalIntegral.integral_add` /
`integral_add`, using the a.e. radial integrability of `RadialSlice.lean`
(`ae_integrableOn_slice`, `ae_integrableOn_slice_inner`) and continuity of the FTC primitive
(`intervalIntegral.continuousOn_primitive_interval'`) for integrability of the primitive itself. -/
theorem traceSphere_add_tgb (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (u1 u2 : Weak.H1 (ball (0 : E) R)) :
    ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
      Weak.traceSphere R (u1 + u2).toFun (u1 + u2).grad (w : E)
        = Weak.traceSphere R u1.toFun u1.grad (w : E)
          + Weak.traceSphere R u2.toFun u2.grad (w : E) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : E) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hu1int : IntegrableOn u1.toFun (ball (0 : E) R) := u1.memL2.integrable one_le_two
  have hu2int : IntegrableOn u2.toFun (ball (0 : E) R) := u2.memL2.integrable one_le_two
  have hab : R / 2 < R := by linarith
  have hhalf : R / 2 ∈ Ioo (0 : ℝ) R := ⟨by linarith, hab⟩
  filter_upwards [ae_integrableOn_slice hm hu1int, ae_integrableOn_slice hm hu2int,
    ae_integrableOn_slice_inner hm u1.grad_memL2, ae_integrableOn_slice_inner hm u2.grad_memL2]
    with w h1u h2u h1g h2g
  have hI1 : IntervalIntegrable (fun t => inner ℝ (u1.grad (t • (w : E))) (w : E)) volume
      (R / 2) R := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (h1g _ hhalf).1
  have hI2 : IntervalIntegrable (fun t => inner ℝ (u2.grad (t • (w : E))) (w : E)) volume
      (R / 2) R := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (h2g _ hhalf).1
  have hmidIcc : ((R / 2 + R) / 2) ∈ uIcc (R / 2) R := by
    rw [uIcc_of_le hab.le]; constructor <;> linarith
  have hP1cont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u1.grad (t • (w : E))) (w : E)) (Icc (R / 2) R) := by
    have := intervalIntegral.continuousOn_primitive_interval' hI1 hmidIcc
    rwa [uIcc_of_le hab.le] at this
  have hP2cont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u2.grad (t • (w : E))) (w : E)) (Icc (R / 2) R) := by
    have := intervalIntegral.continuousOn_primitive_interval' hI2 hmidIcc
    rwa [uIcc_of_le hab.le] at this
  have hP1int : IntegrableOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u1.grad (t • (w : E))) (w : E)) (Ioo (R / 2) R) :=
    (hP1cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hP2int : IntegrableOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u2.grad (t • (w : E))) (w : E)) (Ioo (R / 2) R) :=
    (hP2cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hptwise : ∀ r ∈ Ioo (R / 2) R,
      (u1 + u2).toFun (r • (w : E)) - ∫ t in ((R / 2 + R) / 2)..r,
        inner ℝ ((u1 + u2).grad (t • (w : E))) (w : E)
      = (u1.toFun (r • (w : E)) - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u1.grad (t • (w : E))) (w : E))
        + (u2.toFun (r • (w : E)) - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u2.grad (t • (w : E))) (w : E)) := by
    intro r hr
    have hIcc : uIcc ((R / 2 + R) / 2) r ⊆ uIcc (R / 2) R := by
      rw [uIcc_of_le hab.le]
      exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨hr.1.le, hr.2.le⟩
    have hIr1 : IntervalIntegrable (fun t => inner ℝ (u1.grad (t • (w : E))) (w : E)) volume
        ((R / 2 + R) / 2) r := hI1.mono_set hIcc
    have hIr2 : IntervalIntegrable (fun t => inner ℝ (u2.grad (t • (w : E))) (w : E)) volume
        ((R / 2 + R) / 2) r := hI2.mono_set hIcc
    have hgadd : ∀ t : ℝ, inner ℝ ((u1 + u2).grad (t • (w : E))) (w : E)
        = inner ℝ (u1.grad (t • (w : E))) (w : E) + inner ℝ (u2.grad (t • (w : E))) (w : E) := by
      intro t
      rw [Weak.H1.add_grad]
      simp only [Pi.add_apply]
      exact inner_add_left _ _ _
    have hint : (∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((u1 + u2).grad (t • (w : E))) (w : E))
        = (∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u1.grad (t • (w : E))) (w : E))
          + ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u2.grad (t • (w : E))) (w : E) := by
      rw [← intervalIntegral.integral_add hIr1 hIr2]
      exact intervalIntegral.integral_congr (fun t _ => hgadd t)
    rw [Weak.H1.add_toFun]
    simp only [Pi.add_apply]
    rw [hint]
    ring
  have houter : (∫ r in Ioo (R / 2) R, ((u1 + u2).toFun (r • (w : E)) -
        ∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((u1 + u2).grad (t • (w : E))) (w : E)))
      = (∫ r in Ioo (R / 2) R, (u1.toFun (r • (w : E)) -
          ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u1.grad (t • (w : E))) (w : E)))
        + ∫ r in Ioo (R / 2) R, (u2.toFun (r • (w : E)) -
          ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u2.grad (t • (w : E))) (w : E)) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hptwise]
    exact integral_add ((h1u (R / 2) hhalf).sub hP1int) ((h2u (R / 2) hhalf).sub hP2int)
  have hImidR : uIcc ((R / 2 + R) / 2) R ⊆ uIcc (R / 2) R := by
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨hab.le, le_refl R⟩
  have hImid1 : IntervalIntegrable (fun t => inner ℝ (u1.grad (t • (w : E))) (w : E)) volume
      ((R / 2 + R) / 2) R := hI1.mono_set hImidR
  have hImid2 : IntervalIntegrable (fun t => inner ℝ (u2.grad (t • (w : E))) (w : E)) volume
      ((R / 2 + R) / 2) R := hI2.mono_set hImidR
  have hendadd : (∫ t in ((R / 2 + R) / 2)..R, inner ℝ ((u1 + u2).grad (t • (w : E))) (w : E))
      = (∫ t in ((R / 2 + R) / 2)..R, inner ℝ (u1.grad (t • (w : E))) (w : E))
        + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ (u2.grad (t • (w : E))) (w : E) := by
    rw [← intervalIntegral.integral_add hImid1 hImid2]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [Weak.H1.add_grad]
    simp only [Pi.add_apply]
    exact inner_add_left _ _ _
  simp only [traceSphere]
  rw [houter, hendadd]
  ring

/-- **The sphere trace is a.e. homogeneous.** -/
theorem traceSphere_smul_tgb (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R) (c : ℝ)
    (u : Weak.H1 (ball (0 : E) R)) :
    ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
      Weak.traceSphere R (c • u).toFun (c • u).grad (w : E)
        = c * Weak.traceSphere R u.toFun u.grad (w : E) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : E) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have huint : IntegrableOn u.toFun (ball (0 : E) R) := u.memL2.integrable one_le_two
  have hab : R / 2 < R := by linarith
  have hhalf : R / 2 ∈ Ioo (0 : ℝ) R := ⟨by linarith, hab⟩
  filter_upwards [ae_integrableOn_slice hm huint, ae_integrableOn_slice_inner hm u.grad_memL2]
    with w hu hg
  have hI : IntervalIntegrable (fun t => inner ℝ (u.grad (t • (w : E))) (w : E)) volume
      (R / 2) R := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hg _ hhalf).1
  have hmidIcc : ((R / 2 + R) / 2) ∈ uIcc (R / 2) R := by
    rw [uIcc_of_le hab.le]; constructor <;> linarith
  have hPcont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u.grad (t • (w : E))) (w : E)) (Icc (R / 2) R) := by
    have := intervalIntegral.continuousOn_primitive_interval' hI hmidIcc
    rwa [uIcc_of_le hab.le] at this
  have hPint : IntegrableOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u.grad (t • (w : E))) (w : E)) (Ioo (R / 2) R) :=
    (hPcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hgsmul : ∀ t : ℝ, inner ℝ ((c • u).grad (t • (w : E))) (w : E)
      = c * inner ℝ (u.grad (t • (w : E))) (w : E) := by
    intro t
    rw [Weak.H1.smul_grad]
    simp only [Pi.smul_apply]
    exact real_inner_smul_left _ _ _
  have hptwise : ∀ r ∈ Ioo (R / 2) R,
      (c • u).toFun (r • (w : E)) - ∫ t in ((R / 2 + R) / 2)..r,
        inner ℝ ((c • u).grad (t • (w : E))) (w : E)
      = c * (u.toFun (r • (w : E)) - ∫ t in ((R / 2 + R) / 2)..r,
          inner ℝ (u.grad (t • (w : E))) (w : E)) := by
    intro r hr
    have hint : (∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((c • u).grad (t • (w : E))) (w : E))
        = c * ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • (w : E))) (w : E) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => hgsmul t)
    rw [Weak.H1.smul_toFun]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hint]
    ring
  have houter : (∫ r in Ioo (R / 2) R, ((c • u).toFun (r • (w : E)) -
        ∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((c • u).grad (t • (w : E))) (w : E)))
      = c * ∫ r in Ioo (R / 2) R, (u.toFun (r • (w : E)) -
          ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • (w : E))) (w : E)) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hptwise, integral_const_mul]
  have hImidR : uIcc ((R / 2 + R) / 2) R ⊆ uIcc (R / 2) R := by
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨hab.le, le_refl R⟩
  have hendmul : (∫ t in ((R / 2 + R) / 2)..R, inner ℝ ((c • u).grad (t • (w : E))) (w : E))
      = c * ∫ t in ((R / 2 + R) / 2)..R, inner ℝ (u.grad (t • (w : E))) (w : E) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => hgsmul t)
  simp only [traceSphere]
  rw [houter, hendmul]
  ring

/-- **Deliverable 6 (additivity).**  On the lateral bulk boundary the trace is a.e. additive
in `u`. -/
theorem bulkTrace_add_tgb (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        bulkTrace_tgb hR hL (u + v) (x, R • (w : E))
          = bulkTrace_tgb hR hL u (x, R • (w : E)) + bulkTrace_tgb hR hL v (x, R • (w : E)) := by
  set u' := restrictBulkP_tgb hR u with hu'_def
  set v' := restrictBulkP_tgb hR v with hv'_def
  have huv' : restrictBulkP_tgb hR (u + v) = u' + v' := restrictBulkP_tgb_add hR u v
  filter_upwards [ae_isGoodSlice u', ae_isGoodSlice v', ae_restrict_mem measurableSet_Ioo]
    with x h1 h2 hx
  have hslice_eq : slice (u' + v') x = slice u' x + slice v' x := slice_add_tgb h1 h2
  filter_upwards [traceSphere_add_tgb hm hR (slice u' x) (slice v' x)] with w hw
  rw [bulkTrace_tgb_apply hR hL (u + v) hx w, huv', hslice_eq,
    bulkTrace_tgb_apply hR hL u hx w, bulkTrace_tgb_apply hR hL v hx w]
  exact hw

/-- **Deliverable 6 (homogeneity).**  On the lateral bulk boundary the trace is a.e. homogeneous
in `u`. -/
theorem bulkTrace_smul_tgb (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        bulkTrace_tgb hR hL (c • u) (x, R • (w : E)) = c * bulkTrace_tgb hR hL u (x, R • (w : E)) := by
  set u' := restrictBulkP_tgb hR u with hu'_def
  have hcu' : restrictBulkP_tgb hR (c • u) = c • u' := restrictBulkP_tgb_smul hR c u
  filter_upwards [ae_isGoodSlice u', ae_restrict_mem measurableSet_Ioo] with x h1 hx
  have hslice_eq : slice (c • u') x = c • slice u' x := slice_smul_tgb c h1
  filter_upwards [traceSphere_smul_tgb hm hR c (slice u' x)] with w hw
  rw [bulkTrace_tgb_apply hR hL (c • u) hx w, hcu', hslice_eq, bulkTrace_tgb_apply hR hL u hx w]
  exact hw

end

end RobinCaps.ThinDomain

