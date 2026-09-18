import Mathlib
import RobinCaps.Compact.Basic

/-!
# Smooth mollification and dilation estimates

This file proves the two elementary `L²`-estimates for *globally `C¹`* functions
`v : ℝⁿ → ℝ` that drive the approximation step of the Rellich–Kondrachov theorem on a
ball (see `RobinCaps/Compact/PLAN.md`):

* **(S-smooth)** `integral_ball_conv_sub_sq_le`: the mollification error
  `ρ_ε ⋆ v - v` is controlled on `B_r` by the gradient of `v` on the slightly larger ball
  `B_{r+ε}`,
  `∫_{B_r} (ρ_ε ⋆ v - v)² ≤ ε² ∫_{B_{r+ε}} ‖Dv‖²`.
* **(D-smooth)** `integral_ball_dilate_sub_sq_le`: the dilation error
  `v (λ ·) - v` is controlled on `B_r` by the gradient of `v` on `B_r`,
  `∫_{B_r} (v (λ x) - v x)² dx ≤ (1-λ)² r² 2ⁿ ∫_{B_r} ‖Dv‖²`, for `1/2 ≤ λ ≤ 1`.

The proofs follow the classical route: the fundamental theorem of calculus along a segment
(`sub_eq_intervalIntegral_fderiv`, `sub_eq_intervalIntegral_fderiv_smul`), a weighted
Cauchy–Schwarz/Jensen inequality (`sq_integral_weight_le` and its interval corollary
`sq_intervalIntegral_le`), Tonelli's theorem to exchange the order of integration (carried out
in `ℝ≥0∞`, where measurability of the — everywhere continuous — integrands is immediate), and
finally translation invariance (`lintegral_ball_comp_sub_le`) resp. the scaling behaviour of
Lebesgue measure (`lintegral_ball_comp_smul_le`).

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

/-! ## A weighted Cauchy–Schwarz (Jensen) inequality -/

/-- **Jensen/Cauchy–Schwarz for a probability density.**  If `w ≥ 0` has total integral `1`,
then `(∫ w g)² ≤ ∫ w g²`. -/
theorem sq_integral_weight_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w g : α → ℝ}
    (hw0 : ∀ a, 0 ≤ w a) (hw : Integrable w μ) (hw1 : ∫ a, w a ∂μ = 1)
    (hwg : Integrable (fun a => w a * g a) μ)
    (hwg2 : Integrable (fun a => w a * g a ^ 2) μ) :
    (∫ a, w a * g a ∂μ) ^ 2 ≤ ∫ a, w a * g a ^ 2 ∂μ := by
  set c := ∫ a, w a * g a ∂μ with hc
  have h2 : (0 : ℝ) ≤ ∫ a, w a * (g a - c) ^ 2 ∂μ :=
    integral_nonneg fun a => mul_nonneg (hw0 a) (sq_nonneg _)
  have hexp : (fun a => w a * (g a - c) ^ 2)
      = fun a => w a * g a ^ 2 - 2 * c * (w a * g a) + c ^ 2 * w a := by
    funext a; ring
  have hi2 : Integrable (fun a => 2 * c * (w a * g a)) μ := hwg.const_mul (2 * c)
  have hi3 : Integrable (fun a => c ^ 2 * w a) μ := hw.const_mul (c ^ 2)
  have hi1 : Integrable (fun a => w a * g a ^ 2 - 2 * c * (w a * g a)) μ := hwg2.sub hi2
  rw [hexp, integral_add hi1 hi3, integral_sub hwg2 hi2, integral_const_mul, integral_const_mul,
    hw1, ← hc] at h2
  nlinarith [h2]

/-- Integrability of a continuous function on a metric ball (finite dimensional setting). -/
theorem integrableOn_ball_of_continuous {F : E → ℝ} (hF : Continuous F) (r : ℝ) :
    IntegrableOn F (ball (0 : E) r) volume :=
  (hF.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) r)).mono_set
    ball_subset_closedBall

/-- **Cauchy–Schwarz on an interval**: `(∫_a^b g)² ≤ (b-a) ∫_a^b g²`. -/
theorem sq_intervalIntegral_le {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ s in a..b, g s) ^ 2 ≤ (b - a) * ∫ s in a..b, g s ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hba : 0 < b - a := sub_pos.mpr hlt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hg1 : IntegrableOn g (Ioc a b) volume :=
    (hg.continuousOn.integrableOn_compact (isCompact_Icc (a := a) (b := b))).mono_set
      Ioc_subset_Icc_self
  have hg2 : IntegrableOn (fun s => g s ^ 2) (Ioc a b) volume :=
    ((hg.pow 2).continuousOn.integrableOn_compact (isCompact_Icc (a := a) (b := b))).mono_set
      Ioc_subset_Icc_self
  have hvol : ∫ _s in Ioc a b, (b - a)⁻¹ = 1 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
    exact mul_inv_cancel₀ hba.ne'
  have key := sq_integral_weight_le (μ := volume.restrict (Ioc a b))
    (w := fun _ => (b - a)⁻¹) (g := g)
    (fun _ => by positivity) (integrable_const _) hvol (hg1.const_mul _)
    (hg2.const_mul _)
  rw [integral_const_mul, integral_const_mul, mul_pow] at key
  have h2 := mul_le_mul_of_nonneg_left key (le_of_lt (pow_pos hba 2))
  rw [show (b - a) ^ 2 * ((b - a)⁻¹ ^ 2 * (∫ s in Ioc a b, g s) ^ 2)
        = (∫ s in Ioc a b, g s) ^ 2 by field_simp,
    show (b - a) ^ 2 * ((b - a)⁻¹ * ∫ s in Ioc a b, g s ^ 2)
        = (b - a) * ∫ s in Ioc a b, g s ^ 2 by field_simp] at h2
  exact h2

/-! ## The fundamental theorem of calculus along a segment -/

section FTC

variable {v : EuclideanSpace ℝ (Fin n) → ℝ}

/-- `v (x - t) - v x` as an integral of the derivative along the segment `s ↦ x - s • t`. -/
theorem sub_eq_intervalIntegral_fderiv (hv : ContDiff ℝ 1 v) (x t : E) :
    v (x - t) - v x = ∫ s in (0 : ℝ)..1, -(fderiv ℝ v (x - s • t) t) := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => v (x - s • t)) (-(fderiv ℝ v (x - s • t) t)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => x - s • t) (-t) s := by
      simpa using ((hasDerivAt_id s).smul_const t).const_sub x
    have h2 := ((hv.differentiable le_rfl).differentiableAt (x := x - s • t)).hasFDerivAt
    simpa [Function.comp_def] using h2.comp_hasDerivAt s h1
  have hcont : Continuous fun s : ℝ => -(fderiv ℝ v (x - s • t) t) :=
    Continuous.neg <| (hv.continuous_fderiv_apply le_rfl).comp
      ((continuous_const.sub (continuous_id.smul continuous_const)).prodMk continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  simpa using h.symm

/-- `v x - v (lam • x)` as an integral of the derivative along the ray `s ↦ s • x`. -/
theorem sub_eq_intervalIntegral_fderiv_smul (hv : ContDiff ℝ 1 v) (lam : ℝ) (x : E) :
    v x - v (lam • x) = ∫ s in lam..1, fderiv ℝ v (s • x) x := by
  have hderiv : ∀ s ∈ uIcc lam 1,
      HasDerivAt (fun s : ℝ => v (s • x)) (fderiv ℝ v (s • x) x) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x s := by
      simpa using (hasDerivAt_id s).smul_const x
    have h2 := ((hv.differentiable le_rfl).differentiableAt (x := s • x)).hasFDerivAt
    simpa [Function.comp_def] using h2.comp_hasDerivAt s h1
  have hcont : Continuous fun s : ℝ => fderiv ℝ v (s • x) x :=
    (hv.continuous_fderiv_apply le_rfl).comp
      ((continuous_id.smul continuous_const).prodMk continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  simpa using h.symm

/-- Continuity of `y ↦ ‖fderiv ℝ v y‖ ^ 2`. -/
theorem continuous_norm_fderiv_sq (hv : ContDiff ℝ 1 v) :
    Continuous fun y : E => ‖fderiv ℝ v y‖ ^ 2 :=
  ((hv.continuous_fderiv le_rfl).norm).pow 2

/-- The squared increment along a segment, bounded by the gradient. -/
theorem sq_sub_le_intervalIntegral (hv : ContDiff ℝ 1 v) (x t : E) :
    (v (x - t) - v x) ^ 2 ≤ ‖t‖ ^ 2 * ∫ s in (0 : ℝ)..1, ‖fderiv ℝ v (x - s • t)‖ ^ 2 := by
  have hcont : Continuous fun s : ℝ => -(fderiv ℝ v (x - s • t) t) :=
    Continuous.neg <| (hv.continuous_fderiv_apply le_rfl).comp
      ((continuous_const.sub (continuous_id.smul continuous_const)).prodMk continuous_const)
  have hcont2 : Continuous fun s : ℝ => ‖fderiv ℝ v (x - s • t)‖ ^ 2 :=
    (continuous_norm_fderiv_sq hv).comp (continuous_const.sub (continuous_id.smul continuous_const))
  have h1 := sq_intervalIntegral_le (zero_le_one (α := ℝ)) hcont
  rw [← sub_eq_intervalIntegral_fderiv hv x t] at h1
  have h2 : ∫ s in (0 : ℝ)..1, (-(fderiv ℝ v (x - s • t) t)) ^ 2
      ≤ ∫ s in (0 : ℝ)..1, ‖fderiv ℝ v (x - s • t)‖ ^ 2 * ‖t‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((hcont.pow 2).intervalIntegrable _ _)
      ((hcont2.mul continuous_const).intervalIntegrable _ _) ?_
    intro s _
    have habs : |fderiv ℝ v (x - s • t) t| ≤ ‖fderiv ℝ v (x - s • t)‖ * ‖t‖ := by
      simpa [Real.norm_eq_abs] using (fderiv ℝ v (x - s • t)).le_opNorm t
    have hb := abs_le.mp habs
    have : (fderiv ℝ v (x - s • t) t) ^ 2 ≤ (‖fderiv ℝ v (x - s • t)‖ * ‖t‖) ^ 2 :=
      sq_le_sq' hb.1 hb.2
    calc (-(fderiv ℝ v (x - s • t) t)) ^ 2 = (fderiv ℝ v (x - s • t) t) ^ 2 := by ring
      _ ≤ (‖fderiv ℝ v (x - s • t)‖ * ‖t‖) ^ 2 := this
      _ = ‖fderiv ℝ v (x - s • t)‖ ^ 2 * ‖t‖ ^ 2 := by ring
  rw [intervalIntegral.integral_mul_const] at h2
  have := h1.trans (by linarith [h2] : (1 - 0 : ℝ) * ∫ s in (0 : ℝ)..1,
      (-(fderiv ℝ v (x - s • t) t)) ^ 2
      ≤ (∫ s in (0 : ℝ)..1, ‖fderiv ℝ v (x - s • t)‖ ^ 2) * ‖t‖ ^ 2)
  linarith [this]

/-- The squared increment along a ray, bounded by the gradient. -/
theorem sq_dilate_sub_le_intervalIntegral (hv : ContDiff ℝ 1 v) {lam r : ℝ} (hlam1 : lam ≤ 1)
    {x : E} (hx : ‖x‖ ≤ r) :
    (v (lam • x) - v x) ^ 2
      ≤ (1 - lam) * r ^ 2 * ∫ s in lam..1, ‖fderiv ℝ v (s • x)‖ ^ 2 := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  have hcont : Continuous fun s : ℝ => fderiv ℝ v (s • x) x :=
    (hv.continuous_fderiv_apply le_rfl).comp
      ((continuous_id.smul continuous_const).prodMk continuous_const)
  have hcont2 : Continuous fun s : ℝ => ‖fderiv ℝ v (s • x)‖ ^ 2 :=
    (continuous_norm_fderiv_sq hv).comp (continuous_id.smul continuous_const)
  have h1 := sq_intervalIntegral_le hlam1 hcont
  have h0 : (v (lam • x) - v x) ^ 2 = (∫ s in lam..1, fderiv ℝ v (s • x) x) ^ 2 := by
    rw [← sub_eq_intervalIntegral_fderiv_smul hv lam x]; ring
  have h2 : ∫ s in lam..1, (fderiv ℝ v (s • x) x) ^ 2
      ≤ ∫ s in lam..1, ‖fderiv ℝ v (s • x)‖ ^ 2 * r ^ 2 := by
    refine intervalIntegral.integral_mono_on hlam1
      ((hcont.pow 2).intervalIntegrable _ _)
      ((hcont2.mul continuous_const).intervalIntegrable _ _) ?_
    intro s _
    have habs : |fderiv ℝ v (s • x) x| ≤ ‖fderiv ℝ v (s • x)‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using (fderiv ℝ v (s • x)).le_opNorm x
    have hb := abs_le.mp habs
    have hsq : (fderiv ℝ v (s • x) x) ^ 2 ≤ (‖fderiv ℝ v (s • x)‖ * ‖x‖) ^ 2 :=
      sq_le_sq' hb.1 hb.2
    have hxr : ‖x‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg x]
    nlinarith [sq_nonneg ‖fderiv ℝ v (s • x)‖, hsq]
  rw [intervalIntegral.integral_mul_const] at h2
  rw [h0]
  have hnn : 0 ≤ 1 - lam := by linarith
  calc (∫ s in lam..1, fderiv ℝ v (s • x) x) ^ 2
      ≤ (1 - lam) * ∫ s in lam..1, (fderiv ℝ v (s • x) x) ^ 2 := h1
    _ ≤ (1 - lam) * ((∫ s in lam..1, ‖fderiv ℝ v (s • x)‖ ^ 2) * r ^ 2) := by
        exact mul_le_mul_of_nonneg_left h2 hnn
    _ = (1 - lam) * r ^ 2 * ∫ s in lam..1, ‖fderiv ℝ v (s • x)‖ ^ 2 := by ring

end FTC

/-! ## Translation and scaling of integrals over balls -/

/-- The lower Lebesgue integral of a nonnegative continuous function over a ball is the
`ENNReal.ofReal` of its Bochner integral. -/
theorem lintegral_ball_ofReal {F : E → ℝ} (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y) (r : ℝ) :
    ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (F x)
      = ENNReal.ofReal (∫ x in ball (0 : E) r, F x) :=
  (ofReal_integral_eq_lintegral_ofReal (integrableOn_ball_of_continuous hF r)
    (Eventually.of_forall hF0)).symm

/-- Translating by a vector of norm at most `ε` moves `ball 0 r` into `ball 0 (r + ε)`. -/
theorem lintegral_ball_comp_sub_le {F : E → ℝ} (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y)
    {r ε : ℝ} {c : E} (hc : ‖c‖ ≤ ε) :
    ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (F (x - c))
      ≤ ENNReal.ofReal (∫ y in ball (0 : E) (r + ε), F y) := by
  set g : E → ℝ≥0∞ := fun y => ENNReal.ofReal (F y) with hg
  set S : Set E := (fun y : E => y + c) ⁻¹' ball (0 : E) r with hS
  have hSmeas : MeasurableSet S := measurableSet_ball.preimage (measurable_id.add_const c)
  have hgmeas : Measurable g := (ENNReal.continuous_ofReal.comp hF).measurable
  have hmem : ∀ y : E, y - c ∈ S ↔ y ∈ ball (0 : E) r := by
    intro y
    simp only [hS, mem_preimage, sub_add_cancel]
  have hstep1 : ∫⁻ x in ball (0 : E) r, g (x - c) = ∫⁻ x, S.indicator g (x - c) := by
    rw [← lintegral_indicator measurableSet_ball]
    congr 1
    funext x
    by_cases hx : x ∈ ball (0 : E) r
    · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).mpr hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem fun h => hx ((hmem x).mp h)]
  have hsub : S ⊆ ball (0 : E) (r + ε) := by
    intro y hy
    have hy2 : y + c ∈ ball (0 : E) r := hy
    have hy' : ‖y + c‖ < r := by simpa [mem_ball, dist_zero_right] using hy2
    have h1 : ‖y‖ ≤ ‖y + c‖ + ‖c‖ := by
      have h := norm_sub_le (y + c) c
      rwa [add_sub_cancel_right] at h
    simp only [mem_ball, dist_zero_right]
    linarith
  calc ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (F (x - c))
      = ∫⁻ x, S.indicator g (x - c) := hstep1
    _ = ∫⁻ y, S.indicator g y := lintegral_sub_right_eq_self _ c
    _ = ∫⁻ y in S, g y := lintegral_indicator hSmeas g
    _ ≤ ∫⁻ y in ball (0 : E) (r + ε), g y := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ y in ball (0 : E) (r + ε), F y) := lintegral_ball_ofReal hF hF0 _

/-- Scaling: for `1/2 ≤ s ≤ 1` the integral of `F (s • ·)` over `ball 0 r` is at most
`2 ^ n` times the integral of `F` over `ball 0 r`. -/
theorem lintegral_ball_comp_smul_le {F : E → ℝ} (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (F (s • x))
      ≤ ENNReal.ofReal (2 ^ n * ∫ x in ball (0 : E) r, F x) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs
  have hFs : Continuous fun x : E => F (s • x) := hF.comp (continuous_const_smul s)
  have h1 : ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (F (s • x))
      = ENNReal.ofReal (∫ x in ball (0 : E) r, F (s • x)) :=
    lintegral_ball_ofReal hFs (fun y => hF0 _) r
  have hball : s • ball (0 : E) r = ball (0 : E) (s * r) := by
    rw [_root_.smul_ball hs0.ne' (0 : E) r]
    simp [Real.norm_eq_abs, abs_of_pos hs0]
  have h2 : ∫ x in ball (0 : E) r, F (s • x)
      = (s ^ n)⁻¹ * ∫ x in ball (0 : E) (s * r), F x := by
    rw [Measure.setIntegral_comp_smul_of_pos volume F (ball (0 : E) r) hs0,
      finrank_euclideanSpace_fin, hball, smul_eq_mul]
  have hsubset : ball (0 : E) (s * r) ⊆ ball (0 : E) r :=
    ball_subset_ball (by nlinarith)
  have h3 : ∫ x in ball (0 : E) (s * r), F x ≤ ∫ x in ball (0 : E) r, F x :=
    setIntegral_mono_set (integrableOn_ball_of_continuous hF r)
      (Eventually.of_forall hF0) (HasSubset.Subset.eventuallyLE hsubset)
  have h4 : (0 : ℝ) ≤ ∫ x in ball (0 : E) (s * r), F x :=
    setIntegral_nonneg measurableSet_ball fun y _ => hF0 y
  have hsn : (0 : ℝ) < s ^ n := pow_pos hs0 n
  have hinv : (s ^ n)⁻¹ ≤ 2 ^ n := by
    have hone : (1 : ℝ) ≤ 2 ^ n * s ^ n := by
      rw [← mul_pow]
      exact one_le_pow₀ (by linarith)
    have := mul_le_mul_of_nonneg_right hone (inv_nonneg.mpr hsn.le)
    rwa [one_mul, mul_assoc, mul_inv_cancel₀ hsn.ne', mul_one] at this
  have h5 : ∫ x in ball (0 : E) r, F (s • x) ≤ 2 ^ n * ∫ x in ball (0 : E) r, F x := by
    rw [h2]
    calc (s ^ n)⁻¹ * ∫ x in ball (0 : E) (s * r), F x
        ≤ 2 ^ n * ∫ x in ball (0 : E) (s * r), F x := by
          exact mul_le_mul_of_nonneg_right hinv h4
      _ ≤ 2 ^ n * ∫ x in ball (0 : E) r, F x := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [h1]
  exact ENNReal.ofReal_le_ofReal h5

/-! ## (S-smooth): the mollification estimate -/

section Smooth

variable {ε : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n) → ℝ}

/-- Integrability of `ρ * g` for a mollifier `ρ` and a continuous `g`. -/
theorem integrable_mollifier_mul (hρ : IsMollifier ε ρ) {g : E → ℝ} (hg : Continuous g) :
    Integrable (fun t => ρ t * g t) :=
  (hρ.continuous.mul hg).integrable_of_hasCompactSupport hρ.hasCompactSupport.mul_right

/-- **The translation estimate.**  For a fixed translation vector `t` of norm at most `ε`, the
`L²(B_r)` distance between `v (· - t)` and `v` is controlled by the gradient on `B_{r+ε}`. -/
theorem lintegral_ball_sq_sub_le (hv : ContDiff ℝ 1 v) {r : ℝ} {t : E} {ε : ℝ} (ht : ‖t‖ ≤ ε) :
    ∫⁻ x in ball (0 : E) r, ENNReal.ofReal ((v (x - t) - v x) ^ 2)
      ≤ ENNReal.ofReal (ε ^ 2 * ∫ y in ball (0 : E) (r + ε), ‖fderiv ℝ v y‖ ^ 2) := by
  set F : E → ℝ := fun y => ‖fderiv ℝ v y‖ ^ 2 with hFdef
  have hF : Continuous F := continuous_norm_fderiv_sq hv
  have hF0 : ∀ y, 0 ≤ F y := fun y => sq_nonneg _
  set C : ℝ := ∫ y in ball (0 : E) (r + ε), F y with hCdef
  -- the pointwise estimate
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
      (hcont2.continuousOn.integrableOn_compact (isCompact_Icc (a := (0:ℝ)) (b := 1))).mono_set
        Ioc_subset_Icc_self
    calc ENNReal.ofReal ((v (x - t) - v x) ^ 2)
        ≤ ENNReal.ofReal (ε ^ 2 * ∫ s in (0 : ℝ)..1, F (x - s • t)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (∫ s in (0 : ℝ)..1, F (x - s • t)) :=
          ENNReal.ofReal_mul (sq_nonneg ε)
      _ = ENNReal.ofReal (ε ^ 2) * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (F (x - s • t)) := by
          rw [intervalIntegral.integral_of_le zero_le_one,
            ofReal_integral_eq_lintegral_ofReal hAint (Eventually.of_forall fun s => hF0 _)]
  -- measurability for Tonelli
  have hmeas : AEMeasurable (Function.uncurry fun (x : E) (s : ℝ) =>
      ENNReal.ofReal (F (x - s • t)))
      ((volume.restrict (ball (0 : E) r)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    have : Continuous fun p : E × ℝ => ENNReal.ofReal (F (p.1 - p.2 • t)) :=
      ENNReal.continuous_ofReal.comp
        (hF.comp (continuous_fst.sub (continuous_snd.smul continuous_const)))
    exact this.measurable
  have hεnn : 0 ≤ ε := (norm_nonneg t).trans ht
  calc ∫⁻ x in ball (0 : E) r, ENNReal.ofReal ((v (x - t) - v x) ^ 2)
      ≤ ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (ε ^ 2)
          * ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (F (x - s • t)) := lintegral_mono hpt
    _ = ENNReal.ofReal (ε ^ 2)
          * ∫⁻ x in ball (0 : E) r, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (F (x - s • t)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (ε ^ 2)
          * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (F (x - s • t)) := by
        rw [lintegral_lintegral_swap hmeas]
    _ ≤ ENNReal.ofReal (ε ^ 2) * ∫⁻ _s in Ioc (0 : ℝ) 1, ENNReal.ofReal C := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hsn : ‖s • t‖ ≤ ε := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
          nlinarith [norm_nonneg t, hs.2]
        exact lintegral_ball_comp_sub_le hF hF0 hsn
    _ = ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal C := by
        rw [setLIntegral_const]
        simp
    _ = ENNReal.ofReal (ε ^ 2 * C) := (ENNReal.ofReal_mul (sq_nonneg ε)).symm

/-- **(S-smooth): mollification error controlled by the gradient on a slightly larger ball.** -/
theorem integral_ball_conv_sub_sq_le (hρ : IsMollifier ε ρ) (hε : 0 ≤ ε)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv : ContDiff ℝ 1 v) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in ball (0 : E) r, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2
      ≤ ε ^ 2 * ∫ x in ball (0 : E) (r + ε), ‖fderiv ℝ v x‖ ^ 2 := by
  set F : E → ℝ := fun y => ‖fderiv ℝ v y‖ ^ 2 with hFdef
  have hF : Continuous F := continuous_norm_fderiv_sq hv
  have hF0 : ∀ y, 0 ≤ F y := fun y => sq_nonneg _
  set C : ℝ := ∫ y in ball (0 : E) (r + ε), F y with hCdef
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_ball fun y _ => hF0 y
  have hvloc : LocallyIntegrable v volume := hv.continuous.locallyIntegrable
  have hconv : Continuous (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) :=
    hρ.continuous_conv hvloc
  -- the convolution error as an averaged increment
  have hkey : ∀ x : E, (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x
      = ∫ t, ρ t * (v (x - t) - v x) := by
    intro x
    have h1 : Integrable (fun t => ρ t * v (x - t)) := hρ.integrable_conv_integrand hvloc x
    have h2 : Integrable (fun t => ρ t * v x) := hρ.integrable.mul_const (v x)
    simp_rw [mul_sub]
    rw [integral_sub h1 h2, integral_mul_const, hρ.integral_eq_one, one_mul,
      ← IsMollifier.conv_apply (ρ := ρ) v x]
  -- pointwise Jensen
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
      ((volume.restrict (ball (0 : E) r)).prod volume) := by
    refine Measurable.aemeasurable ?_
    refine Measurable.mul ?_ ?_
    · exact ENNReal.continuous_ofReal.measurable.comp
        (hρ.continuous.measurable.comp measurable_snd)
    · exact ENNReal.continuous_ofReal.measurable.comp
        ((((hv.continuous.comp (continuous_fst.sub continuous_snd)).sub
          (hv.continuous.comp continuous_fst)).pow 2).measurable)
  have hchain : ∫⁻ x in ball (0 : E) r,
      ENNReal.ofReal (((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
      ≤ ENNReal.ofReal (ε ^ 2 * C) := by
    calc ∫⁻ x in ball (0 : E) r,
          ENNReal.ofReal (((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
        ≤ ∫⁻ x in ball (0 : E) r, ∫⁻ t,
            ENNReal.ofReal (ρ t) * ENNReal.ofReal ((v (x - t) - v x) ^ 2) := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ x in ball (0 : E) r,
            ENNReal.ofReal (ρ t) * ENNReal.ofReal ((v (x - t) - v x) ^ 2) :=
          lintegral_lintegral_swap hmeas
      _ = ∫⁻ t, ENNReal.ofReal (ρ t) * ∫⁻ x in ball (0 : E) r,
            ENNReal.ofReal ((v (x - t) - v x) ^ 2) := by
          refine lintegral_congr fun t => ?_
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (ε ^ 2 * C) := by
          refine lintegral_mono fun t => ?_
          by_cases ht : ‖t‖ ≤ ε
          · exact mul_le_mul_right (lintegral_ball_sq_sub_le hv ht) _
          · rw [hρ.eq_zero_of_lt_norm (lt_of_not_ge ht)]
            simp
      _ = (∫⁻ t, ENNReal.ofReal (ρ t)) * ENNReal.ofReal (ε ^ 2 * C) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (ε ^ 2 * C) := by rw [hρ.lintegral_ofReal_eq_one, one_mul]
  have hmeas2 : AEStronglyMeasurable
      (fun x : E => ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2)
      (volume.restrict (ball (0 : E) r)) :=
    ((hconv.sub hv.continuous).pow 2).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _) hmeas2]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (sq_nonneg ε) hC0) hchain

end Smooth

/-! ## (D-smooth): the dilation estimate -/

/-- **(D-smooth): dilation error controlled by the gradient.** -/
theorem integral_ball_dilate_sub_sq_le {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv : ContDiff ℝ 1 v)
    {r : ℝ} (hr : 0 ≤ r) {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) :
    ∫ x in ball (0 : E) r, (v (lam • x) - v x) ^ 2
      ≤ (1 - lam) ^ 2 * r ^ 2 * 2 ^ n * ∫ x in ball (0 : E) r, ‖fderiv ℝ v x‖ ^ 2 := by
  set F : E → ℝ := fun y => ‖fderiv ℝ v y‖ ^ 2 with hFdef
  have hF : Continuous F := continuous_norm_fderiv_sq hv
  have hF0 : ∀ y, 0 ≤ F y := fun y => sq_nonneg _
  set D : ℝ := ∫ y in ball (0 : E) r, F y with hDdef
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_ball fun y _ => hF0 y
  have hnn : 0 ≤ 1 - lam := by linarith
  -- pointwise estimate on the ball
  have hpt : ∀ x ∈ ball (0 : E) r, ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
      ≤ ENNReal.ofReal ((1 - lam) * r ^ 2)
        * ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) := by
    intro x hx
    have hxr : ‖x‖ ≤ r := le_of_lt (by simpa [mem_ball, dist_zero_right] using hx)
    have hcont2 : Continuous fun s : ℝ => F (s • x) :=
      hF.comp (continuous_id.smul continuous_const)
    have hAint : IntegrableOn (fun s : ℝ => F (s • x)) (Ioc lam 1) volume :=
      (hcont2.continuousOn.integrableOn_compact (isCompact_Icc (a := lam) (b := 1))).mono_set
        Ioc_subset_Icc_self
    calc ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
        ≤ ENNReal.ofReal ((1 - lam) * r ^ 2 * ∫ s in lam..1, F (s • x)) :=
          ENNReal.ofReal_le_ofReal (sq_dilate_sub_le_intervalIntegral hv hlam1 hxr)
      _ = ENNReal.ofReal ((1 - lam) * r ^ 2) * ENNReal.ofReal (∫ s in lam..1, F (s • x)) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal ((1 - lam) * r ^ 2) * ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) := by
          rw [intervalIntegral.integral_of_le hlam1,
            ofReal_integral_eq_lintegral_ofReal hAint (Eventually.of_forall fun s => hF0 _)]
  have hmeas : AEMeasurable (Function.uncurry fun (x : E) (s : ℝ) =>
      ENNReal.ofReal (F (s • x)))
      ((volume.restrict (ball (0 : E) r)).prod (volume.restrict (Ioc lam 1))) := by
    refine Measurable.aemeasurable ?_
    have : Continuous fun p : E × ℝ => ENNReal.ofReal (F (p.2 • p.1)) :=
      ENNReal.continuous_ofReal.comp (hF.comp (continuous_snd.smul continuous_fst))
    exact this.measurable
  have hchain : ∫⁻ x in ball (0 : E) r, ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
      ≤ ENNReal.ofReal ((1 - lam) ^ 2 * r ^ 2 * 2 ^ n * D) := by
    calc ∫⁻ x in ball (0 : E) r, ENNReal.ofReal ((v (lam • x) - v x) ^ 2)
        ≤ ∫⁻ x in ball (0 : E) r, ENNReal.ofReal ((1 - lam) * r ^ 2)
            * ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          exact hpt x hx
      _ = ENNReal.ofReal ((1 - lam) * r ^ 2)
            * ∫⁻ x in ball (0 : E) r, ∫⁻ s in Ioc lam 1, ENNReal.ofReal (F (s • x)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((1 - lam) * r ^ 2)
            * ∫⁻ s in Ioc lam 1, ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (F (s • x)) := by
          rw [lintegral_lintegral_swap hmeas]
      _ ≤ ENNReal.ofReal ((1 - lam) * r ^ 2)
            * ∫⁻ _s in Ioc lam 1, ENNReal.ofReal (2 ^ n * D) := by
          refine mul_le_mul_right (lintegral_mono_ae ?_) _
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact lintegral_ball_comp_smul_le hF hF0 hr (by linarith [hs.1]) hs.2
      _ = ENNReal.ofReal ((1 - lam) * r ^ 2)
            * (ENNReal.ofReal (2 ^ n * D) * ENNReal.ofReal (1 - lam)) := by
          rw [setLIntegral_const, Real.volume_Ioc]
      _ = ENNReal.ofReal ((1 - lam) ^ 2 * r ^ 2 * 2 ^ n * D) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hmeas2 : AEStronglyMeasurable (fun x : E => (v (lam • x) - v x) ^ 2)
      (volume.restrict (ball (0 : E) r)) :=
    (((hv.continuous.comp (continuous_const_smul lam)).sub hv.continuous).pow 2).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _) hmeas2]
  refine ENNReal.toReal_le_of_le_ofReal ?_ hchain
  positivity

end RobinCaps.Compact

end
