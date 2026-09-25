import Mathlib
import RobinCaps.Compact.ConvexRellichIface

/-!
# Smooth mollification and dilation estimates on a general bounded set

This file proves the two `Prop`-valued interface statements of `Compact/ConvexRellichIface.lean`:

* `smoothConvSetEst_ses : SmoothConvSetEst n` (**(S-smooth) on a set**): for a `C¹` function
  `v`, a mollifier `ρ` at scale `ε` and a bounded measurable `Ω`,
  `∫_Ω (ρ_ε ⋆ v - v)² ≤ ε² ∫_{cthickening ε Ω} ‖Dv‖²`.
* `smoothDilateSetEst_ses : SmoothDilateSetEst n` (**(D-smooth) on a bounded star-shaped
  set**): for a `C¹` function `v` and a bounded measurable `Ω` that is star-shaped about `0` and
  contained in `closedBall 0 ρ₀`, `∫_Ω (v(λx) − v x)² ≤ (1 − λ)² ρ₀² 2ⁿ ∫_Ω |∇v|²` for
  `1/2 ≤ λ ≤ 1`.

These mirror the ball estimates `integral_ball_conv_sub_sq_le` and
`integral_ball_dilate_sub_sq_le` of `Compact/SmoothEstimates.lean` verbatim; the fundamental
theorem of calculus along a segment/ray (`sub_eq_intervalIntegral_fderiv`,
`sub_eq_intervalIntegral_fderiv_smul`), the weighted Cauchy–Schwarz/Jensen inequality
(`sq_integral_weight_le`) and the pointwise bounds on the squared increment
(`sq_sub_le_intervalIntegral`, `sq_dilate_sub_le_intervalIntegral`) are reused unchanged from
that file — none of them mention balls. Only the two "ball-specific" facts are redone for a
general bounded set `Ω`:

* **Translation** (`lintegral_set_comp_sub_le_ses`): translating `Ω` by a vector of norm at
  most `ε` lands inside `Metric.cthickening ε Ω` (`Metric.mem_cthickening_of_dist_le`), and
  Lebesgue measure is translation invariant (`lintegral_sub_right_eq_self`).
* **Dilation** (`lintegral_set_comp_smul_le_ses`): for `x ∈ Ω` and `s ∈ [0,1]`, star-shapedness
  gives `s • x ∈ Ω`, so `s • Ω ⊆ Ω`; the change of variables `Measure.setIntegral_comp_smul_of_pos`
  (a set-agnostic Haar-measure identity) then gives the `2ⁿ` factor exactly as on balls.

Integrability inputs that used `integrableOn_ball_of_continuous` on a ball are replaced by
integrability of a continuous function on the compact set `Metric.cthickening ε Ω` (resp.
`closure Ω`), obtained from `Bornology.IsBounded Ω` via `Bornology.IsBounded.cthickening`
(resp. `.closure`), `Metric.isClosed_cthickening` (resp. `isClosed_closure`),
`Metric.isCompact_of_isClosed_isBounded`, `Continuous.continuousOn.integrableOn_compact`, and
`IntegrableOn.mono_set` along `Metric.self_subset_cthickening` (resp. `subset_closure`).

Convolutions are scalar convolutions with respect to Lebesgue measure,
`⋆ = ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]`, as in `RobinCaps/Compact/Basic.lean`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology Pointwise

namespace RobinCaps.Compact

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Integrability of a continuous function on a bounded set's closure/thickening -/

/-- A continuous function is integrable on the closed `ε`-thickening of a bounded set: the
thickening is closed and bounded, hence compact. -/
theorem integrableOn_cthickening_of_continuous_ses {F : E → ℝ} (hF : Continuous F)
    {Ω : Set E} (hbdd : Bornology.IsBounded Ω) (ε : ℝ) :
    IntegrableOn F (Metric.cthickening ε Ω) volume := by
  have hcpt : IsCompact (Metric.cthickening ε Ω) :=
    Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening hbdd.cthickening
  exact hF.continuousOn.integrableOn_compact hcpt

/-- A continuous function is integrable on the closure of a bounded set. -/
theorem integrableOn_closure_of_continuous_ses {F : E → ℝ} (hF : Continuous F)
    {Ω : Set E} (hbdd : Bornology.IsBounded Ω) :
    IntegrableOn F (closure Ω) volume := by
  have hcpt : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbdd.closure
  exact hF.continuousOn.integrableOn_compact hcpt

/-- A continuous function is integrable on a bounded set. -/
theorem integrableOn_of_continuous_ses {F : E → ℝ} (hF : Continuous F)
    {Ω : Set E} (hbdd : Bornology.IsBounded Ω) : IntegrableOn F Ω volume :=
  (integrableOn_closure_of_continuous_ses hF hbdd).mono_set subset_closure

/-- The lower Lebesgue integral of a nonnegative function over a set is the `ENNReal.ofReal` of
its Bochner integral, given integrability on that set. -/
theorem lintegral_ofReal_eq_ses {F : E → ℝ} (hF0 : ∀ y, 0 ≤ F y) {S : Set E}
    (hFS : IntegrableOn F S volume) :
    ∫⁻ x in S, ENNReal.ofReal (F x) = ENNReal.ofReal (∫ x in S, F x) :=
  (ofReal_integral_eq_lintegral_ofReal hFS (Eventually.of_forall hF0)).symm

/-! ## Translation and scaling of integrals over a bounded set -/

/-- **Translation.** Translating `Ω` by a vector of norm at most `ε` moves it into
`Metric.cthickening ε Ω`; Lebesgue measure is translation invariant. This is the set version of
`lintegral_ball_comp_sub_le`. -/
theorem lintegral_set_comp_sub_le_ses {F : E → ℝ} (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y)
    {Ω : Set E} (hΩ : MeasurableSet Ω) (hbdd : Bornology.IsBounded Ω) {ε : ℝ} {c : E}
    (hc : ‖c‖ ≤ ε) :
    ∫⁻ x in Ω, ENNReal.ofReal (F (x - c))
      ≤ ENNReal.ofReal (∫ y in Metric.cthickening ε Ω, F y) := by
  set g : E → ℝ≥0∞ := fun y => ENNReal.ofReal (F y) with hg
  set S : Set E := (fun y : E => y + c) ⁻¹' Ω with hS
  have hSmeas : MeasurableSet S := hΩ.preimage (measurable_id.add_const c)
  have hmem : ∀ y : E, y - c ∈ S ↔ y ∈ Ω := by
    intro y
    simp only [hS, mem_preimage, sub_add_cancel]
  have hstep1 : ∫⁻ x in Ω, g (x - c) = ∫⁻ x, S.indicator g (x - c) := by
    rw [← lintegral_indicator hΩ]
    congr 1
    funext x
    by_cases hx : x ∈ Ω
    · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).mpr hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem fun h => hx ((hmem x).mp h)]
  have hsub : S ⊆ Metric.cthickening ε Ω := by
    intro y hy
    have hy2 : y + c ∈ Ω := hy
    have hdeq : dist y (y + c) = ‖c‖ := by
      have hyy : y - (y + c) = -c := by abel
      rw [dist_eq_norm, hyy, norm_neg]
    exact Metric.mem_cthickening_of_dist_le y (y + c) ε Ω hy2 (hdeq ▸ hc)
  have hFcth : IntegrableOn F (Metric.cthickening ε Ω) volume :=
    integrableOn_cthickening_of_continuous_ses hF hbdd ε
  calc ∫⁻ x in Ω, ENNReal.ofReal (F (x - c))
      = ∫⁻ x, S.indicator g (x - c) := hstep1
    _ = ∫⁻ y, S.indicator g y := lintegral_sub_right_eq_self _ c
    _ = ∫⁻ y in S, g y := lintegral_indicator hSmeas g
    _ ≤ ∫⁻ y in Metric.cthickening ε Ω, g y := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ y in Metric.cthickening ε Ω, F y) := lintegral_ofReal_eq_ses hF0 hFcth

/-- **Dilation.** For a star-shaped `Ω` and `1/2 ≤ s ≤ 1`, `s • Ω ⊆ Ω`, so the change-of-variables
formula for dilations gives `∫_Ω F (s • ·) ≤ 2ⁿ ∫_Ω F`. This is the set version of
`lintegral_ball_comp_smul_le`. -/
theorem lintegral_set_comp_smul_le_ses {F : E → ℝ} (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y)
    {Ω : Set E} (hbdd : Bornology.IsBounded Ω)
    (hstar : ∀ x ∈ Ω, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s • x ∈ Ω)
    {s : ℝ} (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    ∫⁻ x in Ω, ENNReal.ofReal (F (s • x)) ≤ ENNReal.ofReal (2 ^ n * ∫ x in Ω, F x) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs
  have hFs : Continuous fun x : E => F (s • x) := hF.comp (continuous_const_smul s)
  have hFΩ : IntegrableOn F Ω volume := integrableOn_of_continuous_ses hF hbdd
  have hFsΩ : IntegrableOn (fun x => F (s • x)) Ω volume := integrableOn_of_continuous_ses hFs hbdd
  have h1 : ∫⁻ x in Ω, ENNReal.ofReal (F (s • x)) = ENNReal.ofReal (∫ x in Ω, F (s • x)) :=
    lintegral_ofReal_eq_ses (fun y => hF0 _) hFsΩ
  have h2 : ∫ x in Ω, F (s • x) = (s ^ n)⁻¹ * ∫ x in s • Ω, F x := by
    rw [Measure.setIntegral_comp_smul_of_pos volume F Ω hs0, finrank_euclideanSpace_fin,
      smul_eq_mul]
  have hsubset : s • Ω ⊆ Ω := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hy
    exact hstar x hx s (by linarith) hs1
  have h3 : ∫ x in s • Ω, F x ≤ ∫ x in Ω, F x :=
    setIntegral_mono_set hFΩ (Eventually.of_forall hF0) (HasSubset.Subset.eventuallyLE hsubset)
  have h4 : (0 : ℝ) ≤ ∫ x in s • Ω, F x := integral_nonneg hF0
  have hsn : (0 : ℝ) < s ^ n := pow_pos hs0 n
  have hinv : (s ^ n)⁻¹ ≤ 2 ^ n := by
    have hone : (1 : ℝ) ≤ 2 ^ n * s ^ n := by
      rw [← mul_pow]
      exact one_le_pow₀ (by linarith)
    have := mul_le_mul_of_nonneg_right hone (inv_nonneg.mpr hsn.le)
    rwa [one_mul, mul_assoc, mul_inv_cancel₀ hsn.ne', mul_one] at this
  have h5 : ∫ x in Ω, F (s • x) ≤ 2 ^ n * ∫ x in Ω, F x := by
    rw [h2]
    calc (s ^ n)⁻¹ * ∫ x in s • Ω, F x
        ≤ 2 ^ n * ∫ x in s • Ω, F x := mul_le_mul_of_nonneg_right hinv h4
      _ ≤ 2 ^ n * ∫ x in Ω, F x := mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [h1]
  exact ENNReal.ofReal_le_ofReal h5

/-! ## (S-smooth) on a set -/

/-- **The translation estimate on a set.** For a fixed translation vector `t` of norm at most
`ε`, the `L²(Ω)` distance between `v (· - t)` and `v` is controlled by the gradient on
`Metric.cthickening ε Ω`. Set version of `lintegral_ball_sq_sub_le`. -/
theorem lintegral_set_sq_sub_le_ses {v : E → ℝ} (hv : ContDiff ℝ 1 v) {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hbdd : Bornology.IsBounded Ω) {t : E} {ε : ℝ} (ht : ‖t‖ ≤ ε) :
    ∫⁻ x in Ω, ENNReal.ofReal ((v (x - t) - v x) ^ 2)
      ≤ ENNReal.ofReal (ε ^ 2 * ∫ y in Metric.cthickening ε Ω, ‖fderiv ℝ v y‖ ^ 2) := by
  set F : E → ℝ := fun y => ‖fderiv ℝ v y‖ ^ 2 with hFdef
  have hF : Continuous F := continuous_norm_fderiv_sq hv
  have hF0 : ∀ y, 0 ≤ F y := fun y => sq_nonneg _
  set C : ℝ := ∫ y in Metric.cthickening ε Ω, F y with hCdef
  have hpt : ∀ x : E, ENNReal.ofReal ((v (x - t) - v x) ^ 2)
      ≤ ENNReal.ofReal (ε ^ 2) * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (F (x - s • t)) := by
    intro x
    have hcont2 : Continuous fun s : ℝ => F (x - s • t) :=
      hF.comp (continuous_const.sub (continuous_id.smul continuous_const))
    have hA0 : 0 ≤ ∫ s in (0 : ℝ)..1, F (x - s • t) :=
      intervalIntegral.integral_nonneg zero_le_one fun s _ => hF0 _
    have hreal : (v (x - t) - v x) ^ 2 ≤ ε ^ 2 * ∫ s in (0 : ℝ)..1, F (x - s • t) := by
      refine (sq_sub_le_intervalIntegral hv x t).trans ?_
      have : ‖t‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg t]
      exact mul_le_mul_of_nonneg_right this hA0
    have hAint : IntegrableOn (fun s : ℝ => F (x - s • t)) (Ioc (0 : ℝ) 1) volume :=
      (hcont2.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set
        Ioc_subset_Icc_self
    calc ENNReal.ofReal ((v (x - t) - v x) ^ 2)
        ≤ ENNReal.ofReal (ε ^ 2 * ∫ s in (0 : ℝ)..1, F (x - s • t)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (∫ s in (0 : ℝ)..1, F (x - s • t)) :=
          ENNReal.ofReal_mul (sq_nonneg ε)
      _ = ENNReal.ofReal (ε ^ 2) * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (F (x - s • t)) := by
          rw [intervalIntegral.integral_of_le zero_le_one,
            ofReal_integral_eq_lintegral_ofReal hAint (Eventually.of_forall fun s => hF0 _)]
  have hmeas : AEMeasurable (Function.uncurry fun (x : E) (s : ℝ) =>
      ENNReal.ofReal (F (x - s • t)))
      ((volume.restrict Ω).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    have : Continuous fun p : E × ℝ => ENNReal.ofReal (F (p.1 - p.2 • t)) :=
      ENNReal.continuous_ofReal.comp
        (hF.comp (continuous_fst.sub (continuous_snd.smul continuous_const)))
    exact this.measurable
  have hεnn : 0 ≤ ε := (norm_nonneg t).trans ht
  calc ∫⁻ x in Ω, ENNReal.ofReal ((v (x - t) - v x) ^ 2)
      ≤ ∫⁻ x in Ω, ENNReal.ofReal (ε ^ 2)
          * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (F (x - s • t)) := lintegral_mono hpt
    _ = ENNReal.ofReal (ε ^ 2)
          * ∫⁻ x in Ω, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (F (x - s • t)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (ε ^ 2)
          * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in Ω, ENNReal.ofReal (F (x - s • t)) := by
        rw [lintegral_lintegral_swap hmeas]
    _ ≤ ENNReal.ofReal (ε ^ 2) * ∫⁻ _s in Ioc (0 : ℝ) 1, ENNReal.ofReal C := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hsn : ‖s • t‖ ≤ ε := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
          nlinarith [norm_nonneg t, hs.2]
        exact lintegral_set_comp_sub_le_ses hF hF0 hΩ hbdd hsn
    _ = ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal C := by
        rw [setLIntegral_const]
        simp
    _ = ENNReal.ofReal (ε ^ 2 * C) := (ENNReal.ofReal_mul (sq_nonneg ε)).symm

/-- **(S-smooth) on a set.** Set version of `integral_ball_conv_sub_sq_le`; proves
`SmoothConvSetEst` after uncurrying the mollifier hypotheses. -/
theorem integral_set_conv_sub_sq_le_ses {ε : ℝ} {ρ : E → ℝ} (hρ : IsMollifier ε ρ) (hε : 0 ≤ ε)
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) {Ω : Set E} (hΩ : MeasurableSet Ω)
    (hbdd : Bornology.IsBounded Ω) :
    ∫ x in Ω, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2
      ≤ ε ^ 2 * ∫ x in Metric.cthickening ε Ω, ‖fderiv ℝ v x‖ ^ 2 := by
  set F : E → ℝ := fun y => ‖fderiv ℝ v y‖ ^ 2 with hFdef
  have hF : Continuous F := continuous_norm_fderiv_sq hv
  have hF0 : ∀ y, 0 ≤ F y := fun y => sq_nonneg _
  set C : ℝ := ∫ y in Metric.cthickening ε Ω, F y with hCdef
  have hCmeas : MeasurableSet (Metric.cthickening ε Ω) := Metric.isClosed_cthickening.measurableSet
  have hC0 : 0 ≤ C := setIntegral_nonneg hCmeas fun y _ => hF0 y
  have hvloc : LocallyIntegrable v volume := hv.continuous.locallyIntegrable
  have hconv : Continuous (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) :=
    hρ.continuous_conv hvloc
  have hkey : ∀ x : E, (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x
      = ∫ t, ρ t * (v (x - t) - v x) := by
    intro x
    have h1 : Integrable (fun t => ρ t * v (x - t)) := hρ.integrable_conv_integrand hvloc x
    have h2 : Integrable (fun t => ρ t * v x) := hρ.integrable.mul_const (v x)
    simp_rw [mul_sub]
    rw [integral_sub h1 h2, integral_mul_const, hρ.integral_eq_one, one_mul,
      ← IsMollifier.conv_apply (ρ := ρ) v x]
  have hpt : ∀ x : E,
      ENNReal.ofReal (((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
        ≤ ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal ((v (x - t) - v x) ^ 2) := by
    intro x
    have hg : Continuous fun t : E => v (x - t) - v x :=
      (hv.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const
    have hi1 : Integrable (fun t => ρ t * (v (x - t) - v x)) :=
      integrable_mollifier_mul hρ hg
    have hi2 : Integrable (fun t => ρ t * (v (x - t) - v x) ^ 2) :=
      integrable_mollifier_mul hρ (hg.pow 2)
    have hjensen := sq_integral_weight_le (μ := volume) (w := ρ)
      (g := fun t => v (x - t) - v x) hρ.nonneg hρ.integrable hρ.integral_eq_one hi1 hi2
    rw [← hkey x] at hjensen
    calc ENNReal.ofReal (((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
        ≤ ENNReal.ofReal (∫ t, ρ t * (v (x - t) - v x) ^ 2) :=
          ENNReal.ofReal_le_ofReal hjensen
      _ = ∫⁻ t, ENNReal.ofReal (ρ t * (v (x - t) - v x) ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal hi2
            (Eventually.of_forall fun t => mul_nonneg (hρ.nonneg t) (sq_nonneg _))
      _ = ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal ((v (x - t) - v x) ^ 2) := by
          refine lintegral_congr fun t => ?_
          exact ENNReal.ofReal_mul (hρ.nonneg t)
  have hmeas : AEMeasurable (Function.uncurry fun (x : E) (t : E) =>
      ENNReal.ofReal (ρ t) * ENNReal.ofReal ((v (x - t) - v x) ^ 2))
      ((volume.restrict Ω).prod volume) := by
    refine Measurable.aemeasurable ?_
    refine Measurable.mul ?_ ?_
    · exact ENNReal.continuous_ofReal.measurable.comp
        (hρ.continuous.measurable.comp measurable_snd)
    · exact ENNReal.continuous_ofReal.measurable.comp
        ((((hv.continuous.comp (continuous_fst.sub continuous_snd)).sub
          (hv.continuous.comp continuous_fst)).pow 2).measurable)
  have hchain : ∫⁻ x in Ω,
      ENNReal.ofReal (((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
      ≤ ENNReal.ofReal (ε ^ 2 * C) := by
    calc ∫⁻ x in Ω,
          ENNReal.ofReal (((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
        ≤ ∫⁻ x in Ω, ∫⁻ t,
            ENNReal.ofReal (ρ t) * ENNReal.ofReal ((v (x - t) - v x) ^ 2) := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ x in Ω,
            ENNReal.ofReal (ρ t) * ENNReal.ofReal ((v (x - t) - v x) ^ 2) :=
          lintegral_lintegral_swap hmeas
      _ = ∫⁻ t, ENNReal.ofReal (ρ t) * ∫⁻ x in Ω,
            ENNReal.ofReal ((v (x - t) - v x) ^ 2) := by
          refine lintegral_congr fun t => ?_
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (ε ^ 2 * C) := by
          refine lintegral_mono fun t => ?_
          by_cases ht : ‖t‖ ≤ ε
          · exact mul_le_mul_right (lintegral_set_sq_sub_le_ses hv hΩ hbdd ht) _
          · rw [hρ.eq_zero_of_lt_norm (lt_of_not_ge ht)]
            simp
      _ = (∫⁻ t, ENNReal.ofReal (ρ t)) * ENNReal.ofReal (ε ^ 2 * C) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (ε ^ 2 * C) := by rw [hρ.lintegral_ofReal_eq_one, one_mul]
  have hmeas2 : AEStronglyMeasurable
      (fun x : E => ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
      (volume.restrict Ω) :=
    ((hconv.sub hv.continuous).pow 2).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _) hmeas2]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (sq_nonneg ε) hC0) hchain

/-! ## (D-smooth) on a bounded star-shaped set -/

/-- **(D-smooth) on a bounded star-shaped set.** Set version of `integral_ball_dilate_sub_sq_le`;
proves `SmoothDilateSetEst`. -/
theorem integral_set_dilate_sub_sq_le_ses {v : E → ℝ} (hv : ContDiff ℝ 1 v) {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hbdd : Bornology.IsBounded Ω)
    (hstar : ∀ x ∈ Ω, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s • x ∈ Ω)
    {ρ₀ : ℝ} (hρ₀0 : 0 ≤ ρ₀) (hρ₀ : ∀ x ∈ Ω, ‖x‖ ≤ ρ₀)
    {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) :
    ∫ x in Ω, (v (lam • x) - v x) ^ 2
      ≤ (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * ∫ x in Ω, ‖fderiv ℝ v x‖ ^ 2 := by
  set F : E → ℝ := fun y => ‖fderiv ℝ v y‖ ^ 2 with hFdef
  have hF : Continuous F := continuous_norm_fderiv_sq hv
  have hF0 : ∀ y, 0 ≤ F y := fun y => sq_nonneg _
  set D : ℝ := ∫ y in Ω, F y with hDdef
  have hD0 : 0 ≤ D := integral_nonneg hF0
  have hnn : 0 ≤ 1 - lam := by linarith
  have hpt : ∀ x ∈ Ω, ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
      ≤ ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2)
        * ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) := by
    intro x hx
    have hxr : ‖x‖ ≤ ρ₀ := hρ₀ x hx
    have hcont2 : Continuous fun s : ℝ => F (s • x) :=
      hF.comp (continuous_id.smul continuous_const)
    have hAint : IntegrableOn (fun s : ℝ => F (s • x)) (Ioc lam 1) volume :=
      (hcont2.continuousOn.integrableOn_compact (isCompact_Icc (a := lam) (b := 1))).mono_set
        Ioc_subset_Icc_self
    calc ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
        ≤ ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2 * ∫ s in lam..1, F (s • x)) :=
          ENNReal.ofReal_le_ofReal (sq_dilate_sub_le_intervalIntegral hv hlam1 hxr)
      _ = ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2) * ENNReal.ofReal (∫ s in lam..1, F (s • x)) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2) * ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) := by
          rw [intervalIntegral.integral_of_le hlam1,
            ofReal_integral_eq_lintegral_ofReal hAint (Eventually.of_forall fun s => hF0 _)]
  have hmeas : AEMeasurable (Function.uncurry fun (x : E) (s : ℝ) =>
      ENNReal.ofReal (F (s • x)))
      ((volume.restrict Ω).prod (volume.restrict (Ioc lam 1))) := by
    refine Measurable.aemeasurable ?_
    have : Continuous fun p : E × ℝ => ENNReal.ofReal (F (p.2 • p.1)) :=
      ENNReal.continuous_ofReal.comp (hF.comp (continuous_snd.smul continuous_fst))
    exact this.measurable
  have hchain : ∫⁻ x in Ω, ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
      ≤ ENNReal.ofReal ((1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * D) := by
    calc ∫⁻ x in Ω, ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
        ≤ ∫⁻ x in Ω, ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2)
            * ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hΩ] with x hx
          exact hpt x hx
      _ = ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2)
            * ∫⁻ x in Ω, ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2)
            * ∫⁻ s in Ioc lam 1, ∫⁻ x in Ω, ENNReal.ofReal (F (s • x)) := by
          rw [lintegral_lintegral_swap hmeas]
      _ ≤ ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2)
            * ∫⁻ _s in Ioc lam 1, ENNReal.ofReal (2 ^ n * D) := by
          refine mul_le_mul_right (lintegral_mono_ae ?_) _
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact lintegral_set_comp_smul_le_ses hF hF0 hbdd hstar (by linarith [hs.1]) hs.2
      _ = ENNReal.ofReal ((1 - lam) * ρ₀ ^ 2)
            * (ENNReal.ofReal (2 ^ n * D) * ENNReal.ofReal (1 - lam)) := by
          rw [setLIntegral_const, Real.volume_Ioc]
      _ = ENNReal.ofReal ((1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * D) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hmeas2 : AEStronglyMeasurable (fun x : E => (v (lam • x) - v x) ^ 2)
      (volume.restrict Ω) :=
    (((hv.continuous.comp (continuous_const_smul lam)).sub hv.continuous).pow 2).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _) hmeas2]
  refine ENNReal.toReal_le_of_le_ofReal ?_ hchain
  positivity

/-! ## The two `Prop`-valued interface statements -/

/-- **(S-smooth) on a bounded set**, discharging `SmoothConvSetEst`. -/
theorem smoothConvSetEst_ses (n : ℕ) : SmoothConvSetEst n := by
  intro ε ρ hρ hε v hv Ω hΩ hbdd
  exact integral_set_conv_sub_sq_le_ses hρ hε hv hΩ hbdd

/-- **(D-smooth) on a bounded star-shaped set**, discharging `SmoothDilateSetEst`. -/
theorem smoothDilateSetEst_ses (n : ℕ) : SmoothDilateSetEst n := by
  intro v hv Ω hΩ hbdd hstar ρ₀ hρ₀0 hρ₀ lam hlam hlam1
  exact integral_set_dilate_sub_sq_le_ses hv hΩ hbdd hstar hρ₀0 hρ₀ hlam hlam1

end RobinCaps.Compact

end
