import RobinCaps.Cap.SharpInequality

/-!
# Polar (radial) reduction of integrals over balls

This file provides the polar-coordinates (radial reduction) formula for integrals
over a ball of `EuclideanSpace ℝ (Fin m)` centred at the origin, the basic brick
for the transverse analysis of the thin-domain theorem.

Writing `σ = (volume : Measure E).toSphere` (`sphereMeasure m` below) for the
unnormalised surface measure on the unit sphere of `E = EuclideanSpace ℝ (Fin m)`,
the main results are

* `lintegral_ball_polar` / `integral_ball_polar` :
  `∫ z in ball 0 R, f z = ∫ r in Ioo 0 R, r ^ (m - 1) * ∫ ω, f (r • ω) ∂σ`
  (the `lintegral` version needs no integrability hypothesis);
* `sphere_measure_univ` : `σ(S^{m-1}) = m ω_m`;
* `integral_ball_radial` : the radial case, `∫ z in ball 0 R, g ‖z‖ =
  m ω_m ∫ r in Ioo 0 R, r ^ (m - 1) * g r`, together with the interval-integral
  form `integral_ball_intervalIntegral` and the compatibility statement
  `integral_ball_slog` with `RobinCaps.Cap.ballProfileIntegral`;
* `sphereIntegral` : the surface integral over the sphere of radius `R`, with its
  radial evaluation, positivity, linearity and scaling lemmas;
* `integral_ball_smul` : `∫ z in ball 0 R, f z = R ^ m * ∫ z in ball 0 1, f (R • z)`.

The section `General` proves everything for an arbitrary finite-dimensional real
normed space equipped with an additive Haar measure; the section `Euclidean`
specialises to `EuclideanSpace ℝ (Fin m)` with the Lebesgue measure.

The key Mathlib input is `MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`
together with Fubini for the product `σ ⊗ volumeIoiPow (m - 1)`.
-/

open MeasureTheory Metric Set Module Filter
open scoped ENNReal NNReal

noncomputable section

namespace RobinCaps.ThinDomain

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Pointwise form of the polar change of variables: the homeomorphism
`homeomorphUnitSphereProd` recovers `x` from its polar coordinates. -/
theorem polar_comp_apply {α : Type*} (F : E → α) (x : ({0}ᶜ : Set E)) :
    F ((((homeomorphUnitSphereProd E) x).2 : ℝ) • (((homeomorphUnitSphereProd E) x).1 : E))
      = F (x : E) := by
  have hx : (x : E) ≠ 0 := x.2
  simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe,
    smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]

theorem integrable_polar_iff (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → ℝ) :
    Integrable (fun p : sphere (0:E) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
      (μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) ↔ Integrable F μ := by
  have h := (μ.measurePreserving_homeomorphUnitSphereProd).integrable_comp_emb
    (Homeomorph.measurableEmbedding _)
    (g := fun p : sphere (0:E) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : E)))
  have hcomp : ((fun p : sphere (0:E) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : E))) ∘
      (homeomorphUnitSphereProd E)) = (F ∘ Subtype.val) :=
    funext fun x => polar_comp_apply F x
  rw [← h, hcomp,
    ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:E)).compl (f := F),
    IntegrableOn, restrict_compl_singleton]

/-- **Polar coordinates**, integral over the whole space. -/
theorem integral_polar (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → ℝ) (hF : Integrable F μ) :
    ∫ z, F z ∂μ = ∫ r in Ioi (0:ℝ), r ^ (finrank ℝ E - 1) *
      ∫ ω : sphere (0:E) 1, F (r • (ω : E)) ∂μ.toSphere := by
  have key : ∫ z, F z ∂μ
      = ∫ r : Ioi (0:ℝ), (∫ ω : sphere (0:E) 1, F ((r : ℝ) • (ω : E)) ∂μ.toSphere)
          ∂(Measure.volumeIoiPow (finrank ℝ E - 1)) := by
    calc ∫ z, F z ∂μ = ∫ x : ({0}ᶜ : Set E), F (x : E) ∂(Measure.comap (↑) μ) := by
          rw [integral_subtype_comap (measurableSet_singleton (0:E)).compl F,
            restrict_compl_singleton]
      _ = ∫ p, F ((p.2 : ℝ) • (p.1 : E))
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) := by
          rw [← μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
            (Homeomorph.measurableEmbedding _)
            (fun p : sphere (0:E) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : E)))]
          exact integral_congr_ae (Eventually.of_forall fun x => (polar_comp_apply F x).symm)
      _ = _ := integral_prod_symm _ ((integrable_polar_iff μ F).2 hF)
  rw [key]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul, integral_subtype_comap measurableSet_Ioi
    (fun a : ℝ => Real.toNNReal (a ^ (finrank ℝ E - 1)) •
      ∫ ω : sphere (0:E) 1, F (a • (ω : E)) ∂μ.toSphere)]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem norm_smul_sphere {r : ℝ} (hr : 0 < r) (ω : sphere (0:E) 1) : ‖r • (ω : E)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.1 ω.2, mul_one]

/-- **Polar coordinates** over a ball centred at the origin. -/
theorem integral_ball_polar_gen (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ)
    (f : E → ℝ) (hf : IntegrableOn f (ball (0:E) R) μ) :
    ∫ z in ball (0:E) R, f z ∂μ = ∫ r in Ioo (0:ℝ) R, r ^ (finrank ℝ E - 1) *
      ∫ ω : sphere (0:E) 1, f (r • (ω : E)) ∂μ.toSphere := by
  set F : E → ℝ := (ball (0:E) R).indicator f with hFdef
  have hFint : Integrable F μ := hf.integrable_indicator measurableSet_ball
  rw [← integral_indicator (measurableSet_ball), ← hFdef, integral_polar μ F hFint]
  have hinner : EqOn (fun r : ℝ => r ^ (finrank ℝ E - 1) *
        ∫ ω : sphere (0:E) 1, F (r • (ω : E)) ∂μ.toSphere)
      ((Ioo (0:ℝ) R).indicator (fun r : ℝ => r ^ (finrank ℝ E - 1) *
        ∫ ω : sphere (0:E) 1, f (r • (ω : E)) ∂μ.toSphere)) (Ioi (0:ℝ)) := by
    intro r hr
    have hr0 : (0:ℝ) < r := hr
    by_cases hrR : r < R
    · have hpt : ∀ ω : sphere (0:E) 1, F (r • (ω : E)) = f (r • (ω : E)) := fun ω =>
        Set.indicator_of_mem (by
          simpa [mem_ball_zero_iff, norm_smul_sphere hr0 ω] using hrR) f
      simp only [hpt]
      rw [Set.indicator_of_mem (Set.mem_Ioo.2 ⟨hr0, hrR⟩)]
    · have hpt : ∀ ω : sphere (0:E) 1, F (r • (ω : E)) = 0 := fun ω =>
        Set.indicator_of_notMem (by
          simpa [mem_ball_zero_iff, norm_smul_sphere hr0 ω] using hrR) f
      simp only [hpt, integral_zero, mul_zero]
      rw [Set.indicator_of_notMem (fun h => hrR h.2)]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_self_of_subset_right Set.Ioo_subset_Ioi_self]

/-- **Polar coordinates**, `lintegral` version: no integrability hypothesis needed. -/
theorem lintegral_polar (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F z ∂μ = ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
      ∫⁻ ω : sphere (0:E) 1, F (r • (ω : E)) ∂μ.toSphere := by
  have hmeas : Measurable
      (fun p : sphere (0:E) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : E))) := by
    refine hF.comp ?_
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).measurable
  have key : ∫⁻ z, F z ∂μ
      = ∫⁻ r : Ioi (0:ℝ), (∫⁻ ω : sphere (0:E) 1, F ((r : ℝ) • (ω : E)) ∂μ.toSphere)
          ∂(Measure.volumeIoiPow (finrank ℝ E - 1)) := by
    calc ∫⁻ z, F z ∂μ = ∫⁻ x : ({0}ᶜ : Set E), F (x : E) ∂(Measure.comap (↑) μ) := by
          rw [lintegral_subtype_comap (measurableSet_singleton (0:E)).compl F,
            restrict_compl_singleton]
      _ = ∫⁻ p, F ((p.2 : ℝ) • (p.1 : E))
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) := by
          rw [← μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
            (Homeomorph.measurableEmbedding _)
            (fun p : sphere (0:E) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : E)))]
          exact lintegral_congr fun x => (polar_comp_apply F x).symm
      _ = _ := lintegral_prod_symm' _ hmeas
  rw [key, Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul _
      (by fun_prop : Measurable fun r : Ioi (0:ℝ) => ENNReal.ofReal ((r : ℝ) ^ (finrank ℝ E - 1)))
      hmeas.lintegral_prod_left']
  simp only [Pi.mul_apply]
  rw [lintegral_subtype_comap measurableSet_Ioi
      (fun a : ℝ => ENNReal.ofReal (a ^ (finrank ℝ E - 1)) *
        ∫⁻ ω : sphere (0:E) 1, F (a • (ω : E)) ∂μ.toSphere)]

/-- **Polar coordinates** over a ball, `lintegral` version. -/
theorem lintegral_ball_polar_gen (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z in ball (0:E) R, f z ∂μ
      = ∫⁻ r in Ioo (0:ℝ) R, ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
          ∫⁻ ω : sphere (0:E) 1, f (r • (ω : E)) ∂μ.toSphere := by
  rw [← lintegral_indicator measurableSet_ball,
    lintegral_polar μ _ (hf.indicator measurableSet_ball)]
  have hinner : EqOn (fun r : ℝ => ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
        ∫⁻ ω : sphere (0:E) 1, (ball (0:E) R).indicator f (r • (ω : E)) ∂μ.toSphere)
      ((Ioo (0:ℝ) R).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
        ∫⁻ ω : sphere (0:E) 1, f (r • (ω : E)) ∂μ.toSphere)) (Ioi (0:ℝ)) := by
    intro r hr
    have hr0 : (0:ℝ) < r := hr
    by_cases hrR : r < R
    · have hpt : ∀ ω : sphere (0:E) 1,
          (ball (0:E) R).indicator f (r • (ω : E)) = f (r • (ω : E)) := fun ω =>
        Set.indicator_of_mem (by
          simpa [mem_ball_zero_iff, norm_smul_sphere hr0 ω] using hrR) f
      simp only [hpt]
      rw [Set.indicator_of_mem (Set.mem_Ioo.2 ⟨hr0, hrR⟩)]
    · have hpt : ∀ ω : sphere (0:E) 1,
          (ball (0:E) R).indicator f (r • (ω : E)) = 0 := fun ω =>
        Set.indicator_of_notMem (by
          simpa [mem_ball_zero_iff, norm_smul_sphere hr0 ω] using hrR) f
      simp only [hpt, lintegral_zero, mul_zero]
      rw [Set.indicator_of_notMem (fun h => hrR h.2)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left Set.Ioo_subset_Ioi_self]

omit [Nontrivial E] in
/-- Scaling a ball integral to the unit ball. -/
theorem integral_ball_smul_gen (μ : Measure E) [μ.IsAddHaarMeasure] {R : ℝ} (hR : 0 < R)
    (f : E → ℝ) :
    ∫ z in ball (0:E) R, f z ∂μ = R ^ (finrank ℝ E) * ∫ z in ball (0:E) 1, f (R • z) ∂μ := by
  have hiff : ∀ z : E, (R • z ∈ ball (0:E) R) ↔ z ∈ ball (0:E) 1 := by
    intro z
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith [norm_nonneg z]
  have hind : (fun z : E => (ball (0:E) 1).indicator (fun w => f (R • w)) z)
      = fun z : E => (ball (0:E) R).indicator f (R • z) := by
    funext z
    by_cases hz : z ∈ ball (0:E) 1
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hiff z).2 hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hiff z).1 h))]
  have hne : (R : ℝ) ^ (finrank ℝ E) ≠ 0 := pow_ne_zero _ hR.ne'
  rw [← integral_indicator (measurableSet_ball (x := (0:E)) (ε := R)),
    ← integral_indicator (measurableSet_ball (x := (0:E)) (ε := (1:ℝ))), hind,
    Measure.integral_comp_smul, smul_eq_mul,
    abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _)), ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]

end General

/-! ## The Euclidean case -/

section Euclidean

/-- `σ` : the (unnormalised) surface measure on the unit sphere of `ℝ^m`,
i.e. `volume.toSphere`. -/
noncomputable abbrev sphereMeasure (m : ℕ) :
    Measure (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere

theorem finrank_eq (m : ℕ) : finrank ℝ (EuclideanSpace ℝ (Fin m)) = m :=
  finrank_euclideanSpace_fin

theorem nontrivial_euclidean {m : ℕ} (hm : 1 ≤ m) :
    Nontrivial (EuclideanSpace ℝ (Fin m)) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_eq]; omega)

set_option linter.unusedVariables false in
/-- **Polar coordinates** for an integral over a ball of `ℝ^m`. -/
theorem integral_ball_polar (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 < R)
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) R)) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, f z
      = ∫ r in Ioo (0:ℝ) R, r ^ (m - 1) *
          ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            f (r • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
  haveI := nontrivial_euclidean hm
  have h := integral_ball_polar_gen (volume : Measure (EuclideanSpace ℝ (Fin m))) R f hf
  rw [finrank_eq] at h
  exact h

set_option linter.unusedVariables false in
/-- The total mass of the sphere measure: `σ(S^{m-1}) = m ω_m`. -/
theorem sphere_measure_univ (m : ℕ) (hm : 1 ≤ m) :
    ((sphereMeasure m) Set.univ).toReal = m * omega m := by
  rw [Measure.toSphere_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_natCast, finrank_eq]
  rfl

/-- Radial reduction of a ball integral (no integrability hypothesis needed). -/
theorem integral_ball_radial' (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (g : ℝ → ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, g ‖z‖
      = m * omega m * ∫ r in Ioo (0:ℝ) R, r ^ (m - 1) * g r := by
  haveI := nontrivial_euclidean hm
  have hind : ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator (fun z => g ‖z‖))
      = fun z : EuclideanSpace ℝ (Fin m) => ((Iio R).indicator g) ‖z‖ := by
    funext z
    by_cases hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R
    · rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem (show ‖z‖ ∈ Iio R from mem_ball_zero_iff.1 hz) g]
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (show ‖z‖ ∉ Iio R from fun h => hz (mem_ball_zero_iff.2 h)) g]
  have hsub : (fun y : ℝ => y ^ (m - 1) • ((Iio R).indicator g) y)
      = (Iio R).indicator (fun y : ℝ => y ^ (m - 1) * g y) := by
    funext y
    by_cases hy : y ∈ Iio R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, smul_eq_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
  rw [← integral_indicator (measurableSet_ball), hind,
    integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
      ((Iio R).indicator g),
    finrank_eq, hsub, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
  rfl

set_option linter.unusedVariables false in
/-- Radial reduction of a ball integral. -/
theorem integral_ball_radial (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 < R) (g : ℝ → ℝ)
    (hg : IntegrableOn (fun r => r ^ (m - 1) * g r) (Ioo (0:ℝ) R)) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, g ‖z‖
      = m * omega m * ∫ r in Ioo (0:ℝ) R, r ^ (m - 1) * g r :=
  integral_ball_radial' m hm R g

/-- Radial reduction written with an interval integral, as used in the cap chapter. -/
theorem integral_ball_intervalIntegral (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (g : ℝ → ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, g ‖z‖
      = m * omega m * ∫ r in (0:ℝ)..R, r ^ (m - 1) * g r := by
  rw [integral_ball_radial' m hm R g, intervalIntegral.integral_of_le hR,
    integral_Ioc_eq_integral_Ioo]

/-- Consistency with the cap chapter: the transverse slice integral of `slog`
is `m ω_m` times `Cap.ballProfileIntegral`. -/
theorem integral_ball_slog (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, Cap.slog t ‖z‖
      = m * omega m * Cap.ballProfileIntegral m t R := by
  rw [Cap.ballProfileIntegral]
  exact integral_ball_intervalIntegral m hm hR (Cap.slog t)

set_option linter.unusedVariables false in
/-- **Polar coordinates** for `lintegral`s over a ball of `ℝ^m`. -/
theorem lintegral_ball_polar (m : ℕ) (hm : 1 ≤ m) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin m) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, f z
      = ∫⁻ r in Ioo (0:ℝ) R, ENNReal.ofReal (r ^ (m - 1)) *
          ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            f (r • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by
  haveI := nontrivial_euclidean hm
  have h := lintegral_ball_polar_gen (volume : Measure (EuclideanSpace ℝ (Fin m))) R f hf
  rwa [finrank_eq] at h

/-! ### Integrals over the sphere of radius `R` -/

/-- The (unnormalised) surface integral of `g` over the sphere of radius `R` in `ℝ^m`. -/
noncomputable def sphereIntegral (m : ℕ) (R : ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  R ^ (m - 1) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    g (R • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)

theorem sphereIntegral_radial (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R) (g : ℝ → ℝ) :
    sphereIntegral m R (fun z => g ‖z‖) = m * omega m * R ^ (m - 1) * g R := by
  have hpt : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      g ‖R • (ω : EuclideanSpace ℝ (Fin m))‖ = g R := fun ω => by
    rw [norm_smul_sphere hR ω]
  simp only [sphereIntegral, hpt]
  rw [integral_const, measureReal_def, sphere_measure_univ m hm, smul_eq_mul]
  ring

theorem sphereIntegral_nonneg (m : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : ∀ z, 0 ≤ g z) : 0 ≤ sphereIntegral m R g :=
  mul_nonneg (pow_nonneg hR _) (integral_nonneg fun _ => hg _)

@[simp]
theorem sphereIntegral_zero (m : ℕ) (R : ℝ) :
    sphereIntegral m R (fun _ => (0:ℝ)) = 0 := by
  simp [sphereIntegral]

theorem sphereIntegral_const_mul (m : ℕ) (R : ℝ) (c : ℝ)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) :
    sphereIntegral m R (fun z => c * g z) = c * sphereIntegral m R g := by
  simp only [sphereIntegral, integral_const_mul]
  ring

theorem sphereIntegral_neg (m : ℕ) (R : ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ) :
    sphereIntegral m R (fun z => -g z) = -sphereIntegral m R g := by
  simp only [sphereIntegral, integral_neg]
  ring

theorem sphereIntegral_add (m : ℕ) (R : ℝ) {g₁ g₂ : EuclideanSpace ℝ (Fin m) → ℝ}
    (h₁ : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g₁ (R • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m))
    (h₂ : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g₂ (R • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m)) :
    sphereIntegral m R (fun z => g₁ z + g₂ z)
      = sphereIntegral m R g₁ + sphereIntegral m R g₂ := by
  simp only [sphereIntegral]
  rw [integral_add h₁ h₂]
  ring

theorem sphereIntegral_sub (m : ℕ) (R : ℝ) {g₁ g₂ : EuclideanSpace ℝ (Fin m) → ℝ}
    (h₁ : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g₁ (R • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m))
    (h₂ : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      g₂ (R • (ω : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m)) :
    sphereIntegral m R (fun z => g₁ z - g₂ z)
      = sphereIntegral m R g₁ - sphereIntegral m R g₂ := by
  simp only [sphereIntegral]
  rw [integral_sub h₁ h₂]
  ring

theorem sphereIntegral_sq_eq (m : ℕ) (R : ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ) :
    sphereIntegral m R (fun z => (g z) ^ 2)
      = R ^ (m - 1) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          (g (R • (ω : EuclideanSpace ℝ (Fin m)))) ^ 2 ∂(sphereMeasure m) := rfl

theorem sphereIntegral_sq_nonneg (m : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) : 0 ≤ sphereIntegral m R (fun z => (g z) ^ 2) :=
  sphereIntegral_nonneg m hR fun _ => sq_nonneg _

/-! ### Scaling -/

theorem integral_ball_smul (m : ℕ) {R : ℝ} (hR : 0 < R) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, f z
      = R ^ m * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f (R • z) := by
  have h := integral_ball_smul_gen (volume : Measure (EuclideanSpace ℝ (Fin m))) hR f
  rwa [finrank_eq] at h

theorem sphereIntegral_smul (m : ℕ) (R : ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ) :
    sphereIntegral m R g = R ^ (m - 1) * sphereIntegral m 1 (fun z => g (R • z)) := by
  simp [sphereIntegral]

end Euclidean

end RobinCaps.ThinDomain

