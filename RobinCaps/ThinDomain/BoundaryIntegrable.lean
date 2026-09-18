import RobinCaps.ThinDomain.BoundaryPieces

/-!
# Discharging the integrability hypotheses of the boundary splitting

The splitting lemmas of `RobinCaps/ThinDomain/BoundaryPieces.lean`
(`lateralIntegral_split`, `boundaryIntegral_split`, `boundaryEnergy_tensor_split`) take the
integrability of the lateral density on the three axial pieces as hypotheses.  This file
discharges them for **bounded measurable** integrands, which covers in particular the trial
functions of the main theorem (continuous, hence bounded on the compact closure).

## Method

The lateral density is `areaElement · (spherical average)` (`lateralDensity_eq_areaElement`).

* The spherical average is bounded by `M · σ(S^{m-1})` because `sphereMeasure m` is a **finite**
  measure (`Measure.toSphere` is finite for a Haar measure on a finite-dimensional space):
  `sphereIntegral_abs_le_of_forall`, `sphereIntegral_abs_le`.
* The spherical average is measurable in `x`: the profile is continuous on `(-L/2, L/2)`
  (`continuousOn_profile`), hence a.e. measurable on each piece, and
  `StronglyMeasurable.integral_prod_right'` turns the joint measurability of
  `(x, ω) ↦ g (x, r_R(x) ω)` into measurability of the average
  (`aestronglyMeasurable_sphereAverage`).
* `areaElement` is integrable on each piece (`intervalIntegrable_areaElement_left/bulk/right`),
  so domination (`Integrable.mono'`) gives integrability of the density
  (`integrableOn_lateralDensity_of_bounded_aux` and its three instances).

The bound is only ever needed **on the lateral surface parametrisation**
`{(x, r_R(x) ω)}`, which is the weakest usable form; the global form `∀ p, |g p| ≤ M` is
provided as the convenient corollary `integrableOn_lateralDensity_of_bounded`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## 1. The spherical average of a bounded integrand is bounded

`sphereMeasure m = volume.toSphere` is a finite measure, so no integrability hypothesis is
needed: `norm_integral_le_of_norm_le_const` holds for any function (an integral of a
non-integrable function is `0`). -/

/-- **Bound for the spherical average**, in the weakest form: the bound is only required at the
points `(x, r ω)` actually integrated over. -/
theorem sphereIntegral_abs_le_of_forall {g : CapSpace m → ℝ} {M : ℝ} {x r : ℝ}
    (hg : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, r • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    |∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, r • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)|
      ≤ M * ((sphereMeasure m) univ).toReal := by
  have h := norm_integral_le_of_norm_le_const (μ := sphereMeasure m)
    (f := fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g (x, r • (ω : EuclideanSpace ℝ (Fin m)))) (C := M)
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hg ω)
  simpa only [Real.norm_eq_abs, measureReal_def] using h

/-- **Bound for the spherical average of a globally bounded integrand.**  No measurability is
needed: the sphere measure is finite. -/
theorem sphereIntegral_abs_le (g : CapSpace m → ℝ) (M : ℝ) (hg : ∀ p, |g p| ≤ M) (x r : ℝ) :
    |∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, r • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)|
      ≤ M * ((sphereMeasure m) univ).toReal :=
  sphereIntegral_abs_le_of_forall fun _ => hg _

/-- The same bound with the total mass evaluated: `|∫_{S^{m-1}} g| ≤ M · m ω_m`. -/
theorem sphereIntegral_abs_le' (hm : 1 ≤ m) (g : CapSpace m → ℝ) (M : ℝ) (hg : ∀ p, |g p| ≤ M)
    (x r : ℝ) :
    |∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, r • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)|
      ≤ M * ((m : ℝ) * omega m) := by
  have h := sphereIntegral_abs_le g M hg x r
  rwa [sphere_measure_univ m hm] at h

/-! ## 2. Measurability of the spherical average as a function of the axial variable -/

/-- **The spherical average `x ↦ ∫_{S^{m-1}} g (x, r_R(x) ω) dσ(ω)` is a.e. strongly measurable**
on any measurable subset of the axial interval `(-L/2, L/2)`.

The profile is continuous there (`continuousOn_profile`), hence a.e. measurable for the
restricted measure; replacing it by a measurable representative makes
`(x, ω) ↦ g (x, r_R(x) ω)` jointly measurable, and `StronglyMeasurable.integral_prod_right'`
(applicable since `sphereMeasure m` is finite, hence s-finite) concludes. -/
theorem aestronglyMeasurable_sphereAverage (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {g : CapSpace m → ℝ} (hgm : Measurable g) {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Ioo (-L/2) (L/2)) :
    AEStronglyMeasurable
      (fun x => ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      (volume.restrict s) := by
  have hp : AEMeasurable (profile Cm Cp L R) (volume.restrict s) :=
    ((continuousOn_profile hR hL).mono hsub).aemeasurable hs
  obtain ⟨p, hpm, hae⟩ := hp
  have hmap : Measurable fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ((q.1 : ℝ), p q.1 • (q.2 : EuclideanSpace ℝ (Fin m))) :=
    measurable_fst.prodMk
      ((hpm.comp measurable_fst).smul (measurable_subtype_coe.comp measurable_snd))
  have hF : StronglyMeasurable fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g (q.1, p q.1 • (q.2 : EuclideanSpace ℝ (Fin m))) :=
    (hgm.comp hmap).stronglyMeasurable
  have h1 : StronglyMeasurable fun x : ℝ =>
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, p x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) :=
    hF.integral_prod_right' (ν := sphereMeasure m)
  refine h1.aestronglyMeasurable.congr (hae.mono fun x hx => ?_)
  simp only [hx]

/-! ## 3. Integrability of the lateral density of a bounded measurable integrand -/

/-- **The workhorse**: on any sub-interval of the axial interval on which the area element is
integrable, the lateral density of a measurable integrand which is bounded *on the lateral
surface over that interval* is integrable.

Domination: `|lateralDensity g x| = |areaElement x| · |spherical average|
≤ |areaElement x| · (M σ(S^{m-1}))`. -/
theorem integrableOn_lateralDensity_of_bounded_aux (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {g : CapSpace m → ℝ} (hgm : Measurable g) {M a b : ℝ}
    (hsub : Ioo a b ⊆ Ioo (-L/2) (L/2))
    (harea : IntegrableOn (areaElement Cm Cp L R) (Ioo a b))
    (hg : ∀ x ∈ Ioo a b, ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo a b) := by
  have hmeas : AEStronglyMeasurable
      (fun x => ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      (volume.restrict (Ioo a b)) :=
    aestronglyMeasurable_sphereAverage hR hL hgm measurableSet_Ioo hsub
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

/-- Integrability of the lateral density on the **left cap piece**, weak (parametrisation) form
of the bound. -/
theorem integrableOn_lateralDensity_left_of_bounded' (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {g : CapSpace m → ℝ} (hgm : Measurable g) {M : ℝ}
    (hg : ∀ x ∈ Ioo (-L/2) (-L/2 + Cm.K * R), ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (-L/2) (-L/2 + Cm.K * R)) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have harea : IntegrableOn (areaElement Cm Cp L R) (Ioo (-L/2) (-L/2 + Cm.K * R)) := by
    have h := intervalIntegrable_areaElement_left (Cm := Cm) (Cp := Cp) (L := L) hR
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le] at h
  exact integrableOn_lateralDensity_of_bounded_aux hR hL hgm
    (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) harea hg

/-- Integrability of the lateral density on the **bulk piece**, weak form of the bound. -/
theorem integrableOn_lateralDensity_bulk_of_bounded' (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {g : CapSpace m → ℝ} (hgm : Measurable g) {M : ℝ}
    (hg : ∀ x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
      ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have harea : IntegrableOn (areaElement Cm Cp L R)
      (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) := by
    have h := intervalIntegrable_areaElement_bulk (Cm := Cm) (Cp := Cp) hR hL
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le] at h
  exact integrableOn_lateralDensity_of_bounded_aux hR hL hgm
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) harea hg

/-- Integrability of the lateral density on the **right cap piece**, weak form of the bound. -/
theorem integrableOn_lateralDensity_right_of_bounded' (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {g : CapSpace m → ℝ} (hgm : Measurable g) {M : ℝ}
    (hg : ∀ x ∈ Ioo (L/2 - Cp.K * R) (L/2), ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (L/2 - Cp.K * R) (L/2)) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have harea : IntegrableOn (areaElement Cm Cp L R) (Ioo (L/2 - Cp.K * R) (L/2)) := by
    have h := intervalIntegrable_areaElement_right (Cm := Cm) (Cp := Cp) hR hL
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le] at h
  exact integrableOn_lateralDensity_of_bounded_aux hR hL hgm
    (fun x hx => ⟨by linarith [hx.1], hx.2⟩) harea hg

/-- **The three integrability hypotheses of the splitting lemmas, for a bounded measurable
integrand.**  This is the form in which the hypotheses of `lateralIntegral_split`,
`boundaryIntegral_split` and `boundaryEnergy_tensor_split` are discharged.

(The hypothesis `1 ≤ m` is not needed for the proof; it is kept in the signature because every
consumer of the splitting lemmas carries it.) -/
theorem integrableOn_lateralDensity_of_bounded (_hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (g : CapSpace m → ℝ) (hgm : Measurable g) (M : ℝ)
    (hg : ∀ p, |g p| ≤ M) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (-L/2) (-L/2 + Cm.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R g)
        (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (L/2 - Cp.K * R) (L/2)) :=
  ⟨integrableOn_lateralDensity_left_of_bounded' hR hL hgm (M := M) (fun _ _ _ => hg _),
    integrableOn_lateralDensity_bulk_of_bounded' hR hL hgm (M := M) (fun _ _ _ => hg _),
    integrableOn_lateralDensity_right_of_bounded' hR hL hgm (M := M) (fun _ _ _ => hg _)⟩

/-! ## 4. The splitting lemmas for bounded measurable integrands -/

/-- **Splitting of the lateral integral**, weak form of the bound (only on the lateral surface
parametrisation over the axial interval). -/
theorem lateralIntegral_split_of_bounded' (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hgm : Measurable g) {M : ℝ}
    (hg : ∀ x ∈ Ioo (-L/2) (L/2), ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    lateralIntegral Cm Cp L R g
      = (∫ x in Ioo (-L/2) (-L/2 + Cm.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Ioo (L/2 - Cp.K * R) (L/2), lateralDensity Cm Cp L R g x) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  refine lateralIntegral_split hR hL g
    (integrableOn_lateralDensity_left_of_bounded' hR hL hgm (M := M)
      (fun x hx => hg x ⟨hx.1, by linarith [hx.2]⟩))
    (integrableOn_lateralDensity_bulk_of_bounded' hR hL hgm (M := M)
      (fun x hx => hg x ⟨by linarith [hx.1], by linarith [hx.2]⟩))
    (integrableOn_lateralDensity_right_of_bounded' hR hL hgm (M := M)
      (fun x hx => hg x ⟨by linarith [hx.1], hx.2⟩))

/-- **Splitting of the lateral integral** for a globally bounded measurable integrand. -/
theorem lateralIntegral_split_of_bounded (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hgm : Measurable g) (M : ℝ) (hg : ∀ p, |g p| ≤ M) :
    lateralIntegral Cm Cp L R g
      = (∫ x in Ioo (-L/2) (-L/2 + Cm.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Ioo (L/2 - Cp.K * R) (L/2), lateralDensity Cm Cp L R g x) :=
  lateralIntegral_split_of_bounded' hR hL g hgm (M := M) (fun _ _ _ => hg _)

/-- **Splitting of the lateral integral for a continuous integrand**, with the bound required
only on the lateral boundary parametrisation `{(x, r_R(x) ω) : x ∈ (-L/2, L/2), ω ∈ S^{m-1}}`.
This is the weakest usable form; for a `g` continuous on the (compact) closure of the thin domain
such a bound is furnished by `IsCompact.exists_bound_of_continuousOn`. -/
theorem lateralIntegral_split_of_continuous (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hgc : Continuous g) {M : ℝ}
    (hg : ∀ x ∈ Ioo (-L/2) (L/2), ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M) :
    lateralIntegral Cm Cp L R g
      = (∫ x in Ioo (-L/2) (-L/2 + Cm.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Ioo (L/2 - Cp.K * R) (L/2), lateralDensity Cm Cp L R g x) :=
  lateralIntegral_split_of_bounded' hR hL g hgc.measurable (M := M) hg

/-- **The boundary integral of `Ω_R`, split into its three axial pieces**, for a bounded
measurable integrand: `boundaryIntegral_split` with its integrability hypotheses discharged. -/
theorem boundaryIntegral_split_of_bounded (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hgm : Measurable g) (M : ℝ) (hg : ∀ p, |g p| ≤ M) :
    boundaryIntegral Cm Cp L R g
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + R ^ m * (capLateralIntegral Cm (fun p => g (-L/2 - R * p.1, R • p.2))
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), g (-L/2, R • z))
        + R ^ m * (capLateralIntegral Cp (fun p => g (L/2 + R * p.1, R • p.2))
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), g (L/2, R • z)) := by
  obtain ⟨h₁, h₂, h₃⟩ := integrableOn_lateralDensity_of_bounded hm hR hL g hgm M hg
  exact boundaryIntegral_split hm hR hL g h₁ h₂ h₃

/-- The square of a bounded function is bounded by the square of the bound. -/
theorem abs_sq_le_of_abs_le {g : CapSpace m → ℝ} {M : ℝ} (hg : ∀ p, |g p| ≤ M) (p : CapSpace m) :
    |g p ^ 2| ≤ M ^ 2 := by
  have h0 : (0 : ℝ) ≤ |g p| := abs_nonneg _
  rw [abs_of_nonneg (sq_nonneg (g p)), ← sq_abs]
  exact pow_le_pow_left₀ h0 (hg p) 2

/-- **The boundary energy of a trial function of the manuscript's shape**, for a bounded
measurable `u`: `boundaryEnergy_tensor_split` with its integrability hypotheses discharged
(the integrand is `u²`, bounded by `M²`). -/
theorem boundaryEnergy_tensor_split_of_bounded (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : CapSpace m → ℝ) (F : ℝ → ℝ)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hum : Measurable u) (M : ℝ) (hu : ∀ p, |u p| ≤ M)
    (hbulk : ∀ x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
      ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        u (x, R • (ω : EuclideanSpace ℝ (Fin m)))
          = F x * h (R • (ω : EuclideanSpace ℝ (Fin m)))) :
    boundaryEnergy Cm Cp L R u
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
            * sphereIntegral m R (fun z => h z ^ 2)
        + R ^ m * (capLateralIntegral Cm (fun p => u (-L/2 - R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), u (-L/2, R • z) ^ 2)
        + R ^ m * (capLateralIntegral Cp (fun p => u (L/2 + R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), u (L/2, R • z) ^ 2) := by
  obtain ⟨h₁, h₂, h₃⟩ := integrableOn_lateralDensity_of_bounded (Cm := Cm) (Cp := Cp) (L := L)
    (R := R) hm hR hL (fun p => u p ^ 2) (hum.pow_const 2) (M ^ 2) (abs_sq_le_of_abs_le hu)
  exact boundaryEnergy_tensor_split hm hR hL u F h hbulk h₁ h₂ h₃

/-- The boundary energy splitting for a **continuous** trial function, with a global bound. -/
theorem boundaryEnergy_tensor_split_of_continuous (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : CapSpace m → ℝ) (F : ℝ → ℝ)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (huc : Continuous u) (M : ℝ) (hu : ∀ p, |u p| ≤ M)
    (hbulk : ∀ x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
      ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        u (x, R • (ω : EuclideanSpace ℝ (Fin m)))
          = F x * h (R • (ω : EuclideanSpace ℝ (Fin m)))) :
    boundaryEnergy Cm Cp L R u
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
            * sphereIntegral m R (fun z => h z ^ 2)
        + R ^ m * (capLateralIntegral Cm (fun p => u (-L/2 - R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), u (-L/2, R • z) ^ 2)
        + R ^ m * (capLateralIntegral Cp (fun p => u (L/2 + R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), u (L/2, R • z) ^ 2) :=
  boundaryEnergy_tensor_split_of_bounded hm hR hL u F h huc.measurable M hu hbulk


/-! ## 5. Continuous integrands: the bound from compactness of the closure

For a `g` which is continuous on the whole ambient space the bound is automatic: the lateral
surface parametrisation lands in the closure of the thin domain, which is compact. -/

/-- **The lateral boundary points lie in the closure of the thin domain**:
`(x, r_R(x) ω) ∈ closure Ω_R` for `x ∈ (-L/2, L/2)` and `ω ∈ S^{m-1}`.  Indeed the interior
points `(x, t r_R(x) ω)` with `0 < t < 1` belong to `Ω_R` and converge to it as `t → 1⁻`. -/
theorem mem_closure_thinDomain_lateral (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {x : ℝ} (hx : x ∈ Ioo (-L/2) (L/2)) (ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    ((x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) : CapSpace m)
      ∈ closure (thinDomain Cm Cp L R) := by
  have hpos := profile_pos hR hL hx
  have hnorm : ‖(ω : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  have hcont : Continuous fun t : ℝ =>
      ((x, (t * profile Cm Cp L R x) • (ω : EuclideanSpace ℝ (Fin m))) : CapSpace m) :=
    continuous_const.prodMk ((continuous_id.mul continuous_const).smul continuous_const)
  have htend : Filter.Tendsto
      (fun t : ℝ => ((x, (t * profile Cm Cp L R x) • (ω : EuclideanSpace ℝ (Fin m))) : CapSpace m))
      (nhdsWithin (1 : ℝ) (Iio 1))
      (nhds ((x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m))) : CapSpace m)) := by
    have h := (hcont.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1:ℝ)))
    simpa only [one_mul] using h
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with t ht
  refine ⟨hx.1, hx.2, ?_⟩
  rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ht.1.le hpos.le)]
  nlinarith [ht.2, hpos]

/-- The closure of the thin domain is compact (it is bounded, and the ambient space is a proper
metric space). -/
theorem isCompact_closure_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    IsCompact (closure (thinDomain Cm Cp L R)) :=
  (isBounded_thinDomain hR hL).isCompact_closure

/-- **Splitting of the lateral integral for a continuous integrand, with no bound hypothesis**:
the bound is produced by compactness of `closure Ω_R`. -/
theorem lateralIntegral_split_of_continuous_closure (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hgc : Continuous g) :
    lateralIntegral Cm Cp L R g
      = (∫ x in Ioo (-L/2) (-L/2 + Cm.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + (∫ x in Ioo (L/2 - Cp.K * R) (L/2), lateralDensity Cm Cp L R g x) := by
  obtain ⟨M, hM⟩ :=
    (isCompact_closure_thinDomain hR hL).exists_bound_of_continuousOn hgc.continuousOn
  exact lateralIntegral_split_of_bounded' hR hL g hgc.measurable (M := M)
    (fun x hx ω => by
      simpa only [Real.norm_eq_abs] using hM _ (mem_closure_thinDomain_lateral hR hL hx ω))

/-- The three integrability hypotheses, discharged for a **continuous** integrand with no bound
hypothesis. -/
theorem integrableOn_lateralDensity_of_continuous (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hgc : Continuous g) :
    IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (-L/2) (-L/2 + Cm.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R g)
        (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) ∧
      IntegrableOn (lateralDensity Cm Cp L R g) (Ioo (L/2 - Cp.K * R) (L/2)) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  obtain ⟨M, hM⟩ :=
    (isCompact_closure_thinDomain hR hL).exists_bound_of_continuousOn hgc.continuousOn
  have hbd : ∀ x ∈ Ioo (-L/2) (L/2), ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      |g (x, profile Cm Cp L R x • (ω : EuclideanSpace ℝ (Fin m)))| ≤ M :=
    fun x hx ω => by
      simpa only [Real.norm_eq_abs] using hM _ (mem_closure_thinDomain_lateral hR hL hx ω)
  exact ⟨integrableOn_lateralDensity_left_of_bounded' hR hL hgc.measurable (M := M)
      (fun x hx => hbd x ⟨hx.1, by linarith [hx.2]⟩),
    integrableOn_lateralDensity_bulk_of_bounded' hR hL hgc.measurable (M := M)
      (fun x hx => hbd x ⟨by linarith [hx.1], by linarith [hx.2]⟩),
    integrableOn_lateralDensity_right_of_bounded' hR hL hgc.measurable (M := M)
      (fun x hx => hbd x ⟨by linarith [hx.1], hx.2⟩)⟩

/-- **The boundary integral splitting for a continuous integrand**, with no bound hypothesis. -/
theorem boundaryIntegral_split_of_continuous (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (g : CapSpace m → ℝ) (hgc : Continuous g) :
    boundaryIntegral Cm Cp L R g
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), lateralDensity Cm Cp L R g x)
        + R ^ m * (capLateralIntegral Cm (fun p => g (-L/2 - R * p.1, R • p.2))
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), g (-L/2, R • z))
        + R ^ m * (capLateralIntegral Cp (fun p => g (L/2 + R * p.1, R • p.2))
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), g (L/2, R • z)) := by
  obtain ⟨h₁, h₂, h₃⟩ := integrableOn_lateralDensity_of_continuous hR hL g hgc
  exact boundaryIntegral_split hm hR hL g h₁ h₂ h₃

/-- **The boundary energy splitting for a continuous trial function**, with no bound
hypothesis. -/
theorem boundaryEnergy_tensor_split_of_continuous' (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : CapSpace m → ℝ) (F : ℝ → ℝ)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (huc : Continuous u)
    (hbulk : ∀ x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
      ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        u (x, R • (ω : EuclideanSpace ℝ (Fin m)))
          = F x * h (R • (ω : EuclideanSpace ℝ (Fin m)))) :
    boundaryEnergy Cm Cp L R u
      = (∫ x in Icc (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
            * sphereIntegral m R (fun z => h z ^ 2)
        + R ^ m * (capLateralIntegral Cm (fun p => u (-L/2 - R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cm.θ 0), u (-L/2, R • z) ^ 2)
        + R ^ m * (capLateralIntegral Cp (fun p => u (L/2 + R * p.1, R • p.2) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (Cp.θ 0), u (L/2, R • z) ^ 2) := by
  obtain ⟨h₁, h₂, h₃⟩ := integrableOn_lateralDensity_of_continuous (Cm := Cm) (Cp := Cp)
    (L := L) (R := R) hR hL (fun p => u p ^ 2) (huc.pow 2)
  exact boundaryEnergy_tensor_split hm hR hL u F h hbulk h₁ h₂ h₃

end RobinCaps.ThinDomain

end

