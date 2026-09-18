import RobinCaps.Compact.Basic

/-!
# Convolution with a mollifier is an `L²` contraction

This file proves the estimate (J) of `RobinCaps/Compact/PLAN.md`: convolution with a
probability kernel `ρ` (a mollifier, `IsMollifier δ ρ`) does not increase the `L²` norm,

`∫ (ρ ⋆ g)² ≤ ∫ g²`.

The proof is carried out in `ℝ≥0∞`, so that no integrability side condition is needed for the
core estimate `lintegral_conv_sq_le`: pointwise Cauchy–Schwarz (through
`ENNReal.lintegral_mul_norm_pow_le` with the exponents `1/2, 1/2`, using `∫ ρ = 1`) gives

`ofReal ((ρ ⋆ g) x ^ 2) ≤ ∫⁻ t, ofReal (ρ t) * ofReal (g (x - t) ^ 2)`,

and Tonelli together with the translation invariance of Lebesgue measure turns the right-hand
side, after integration in `x`, into `∫⁻ x, ofReal (g x ^ 2)`.

## Main results

* `lintegral_conv_sq_le` — the `ℝ≥0∞` form of the contraction property;
* `memLp_conv` — `ρ ⋆ g ∈ L²` whenever `g ∈ L²`;
* `integral_conv_sq_le`, `integral_conv_sub_sq_le` — the real (Bochner) forms;
* `abs_conv_le` — the pointwise Cauchy–Schwarz bound `|(ρ ⋆ g) x| ≤ ‖ρ‖₂ ‖g‖₂`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

variable {n : ℕ} {δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## The pointwise estimate -/

/-- The algebraic identity underlying the pointwise Cauchy–Schwarz estimate: for `a ≥ 0`,
`‖a * b‖ₑ` is the product of the square roots of `ofReal a` and of `ofReal a * ofReal (b ^ 2)`. -/
private theorem enorm_mul_eq_rpow (a b : ℝ) (ha : 0 ≤ a) :
    ‖a * b‖ₑ = ENNReal.ofReal a ^ (1 / 2 : ℝ)
      * (ENNReal.ofReal a * ENNReal.ofReal (b ^ 2)) ^ (1 / 2 : ℝ) := by
  have h2 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have habs : ‖a * b‖ₑ = ENNReal.ofReal (a * |b|) := by
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg ha]
  have key : ENNReal.ofReal a * (ENNReal.ofReal a * ENNReal.ofReal (b ^ 2))
      = ENNReal.ofReal (a * |b|) ^ (2 : ℕ) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a * a),
      ← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [mul_pow, sq_abs]
    ring
  calc ‖a * b‖ₑ = ENNReal.ofReal (a * |b|) := habs
    _ = (ENNReal.ofReal (a * |b|) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast (ENNReal.ofReal (a * |b|)) 2, ← ENNReal.rpow_mul]
        norm_num
    _ = _ := by rw [← key, ENNReal.mul_rpow_of_nonneg _ _ h2]

/-- **Pointwise Jensen/Cauchy–Schwarz estimate.**  Since `ρ` has integral one,
`(ρ ⋆ g) x ^ 2 ≤ ∫ ρ t * g (x - t) ^ 2 dt`, in `ℝ≥0∞` form (no integrability needed). -/
theorem ofReal_conv_sq_le (hρ : IsMollifier δ ρ) {g : E → ℝ}
    (hg : AEStronglyMeasurable g volume) (x : E) :
    ENNReal.ofReal ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x ^ 2)
      ≤ ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (g (x - t) ^ 2) := by
  have hgx : AEMeasurable (fun t : E => g (x - t)) volume :=
    hg.aemeasurable.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
  have hmρ : AEMeasurable (fun t : E => ENNReal.ofReal (ρ t)) volume :=
    hρ.continuous.measurable.ennreal_ofReal.aemeasurable
  have hm2 : AEMeasurable
      (fun t : E => ENNReal.ofReal (ρ t) * ENNReal.ofReal (g (x - t) ^ 2)) volume :=
    hmρ.mul (hgx.pow_const 2).ennreal_ofReal
  set B := ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (g (x - t) ^ 2) with hB
  have step1 : ‖∫ t, ρ t * g (x - t)‖ₑ ≤ ∫⁻ t, ‖ρ t * g (x - t)‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  have step2 : ∫⁻ t, ‖ρ t * g (x - t)‖ₑ ≤ B ^ (1 / 2 : ℝ) := by
    have hcongr : ∫⁻ t, ‖ρ t * g (x - t)‖ₑ
        = ∫⁻ t, ENNReal.ofReal (ρ t) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (ρ t) * ENNReal.ofReal (g (x - t) ^ 2)) ^ (1 / 2 : ℝ) :=
      lintegral_congr fun t => enorm_mul_eq_rpow (ρ t) (g (x - t)) (hρ.nonneg t)
    rw [hcongr]
    refine le_trans (ENNReal.lintegral_mul_norm_pow_le hmρ hm2 (by norm_num) (by norm_num)
      (by norm_num)) ?_
    rw [hρ.lintegral_ofReal_eq_one, ENNReal.one_rpow, one_mul, ← hB]
  have hstep : ‖∫ t, ρ t * g (x - t)‖ₑ ≤ B ^ (1 / 2 : ℝ) := step1.trans step2
  rw [IsMollifier.conv_apply]
  calc ENNReal.ofReal ((∫ t, ρ t * g (x - t)) ^ 2)
      = ‖∫ t, ρ t * g (x - t)‖ₑ ^ (2 : ℕ) := by
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    _ ≤ (B ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by gcongr
    _ = B := by
        rw [← ENNReal.rpow_natCast (B ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
        norm_num

/-! ## The contraction property -/

/-- **(J), `ℝ≥0∞` form.**  Convolution with a mollifier does not increase `∫ g²`. -/
theorem lintegral_conv_sq_le (hρ : IsMollifier δ ρ) {g : E → ℝ}
    (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, ENNReal.ofReal ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x ^ 2)
      ≤ ∫⁻ x, ENNReal.ofReal (g x ^ 2) := by
  have hmρ : Measurable fun t : E => ENNReal.ofReal (ρ t) :=
    hρ.continuous.measurable.ennreal_ofReal
  have hprod : AEMeasurable
      (Function.uncurry fun x t : E => ENNReal.ofReal (ρ t) * ENNReal.ofReal (g (x - t) ^ 2))
      (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : E × E => ENNReal.ofReal (ρ p.2)) (volume.prod volume) :=
      (hmρ.comp measurable_snd).aemeasurable
    have h2 : AEMeasurable (fun p : E × E => g (p.1 - p.2)) (volume.prod volume) :=
      hg.aemeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    exact h1.mul (h2.pow_const 2).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x ^ 2)
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ t) * ENNReal.ofReal (g (x - t) ^ 2) :=
        lintegral_mono fun x => ofReal_conv_sq_le hρ hg x
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ t) * ENNReal.ofReal (g (x - t) ^ 2) :=
        lintegral_lintegral_swap hprod
    _ = ∫⁻ t, ENNReal.ofReal (ρ t) * ∫⁻ x, ENNReal.ofReal (g (x - t) ^ 2) :=
        lintegral_congr fun t => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ t, ENNReal.ofReal (ρ t) * ∫⁻ x, ENNReal.ofReal (g x ^ 2) := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (g x ^ 2)) t]
    _ = (∫⁻ t, ENNReal.ofReal (ρ t)) * ∫⁻ x, ENNReal.ofReal (g x ^ 2) :=
        lintegral_mul_const _ hmρ
    _ = ∫⁻ x, ENNReal.ofReal (g x ^ 2) := by rw [hρ.lintegral_ofReal_eq_one, one_mul]

/-- Convolution with a mollifier maps `L²(ℝⁿ)` into itself. -/
theorem memLp_conv (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) :
    MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 2 volume := by
  have hcont : Continuous (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    hρ.continuous_conv (hg.locallyIntegrable one_le_two)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine ⟨(hcont.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
  refine lt_of_le_of_lt (lintegral_conv_sq_le hρ hg.aestronglyMeasurable) ?_
  have h := hg.integrable_sq.2
  rwa [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)] at h

/-- **(J).**  Convolution with a mollifier is an `L²`-contraction. -/
theorem integral_conv_sq_le (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) :
    ∫ x, (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x ^ 2 ≤ ∫ x, g x ^ 2 := by
  have hc := (memLp_conv hρ hg).integrable_sq
  have hgi := hg.integrable_sq
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      hc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      hgi.aestronglyMeasurable]
  refine ENNReal.toReal_mono ?_ (lintegral_conv_sq_le hρ hg.aestronglyMeasurable)
  have h := hgi.2
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)] at h
  exact h.ne

/-- The contraction property applied to a difference: mollification is `1`-Lipschitz in `L²`. -/
theorem integral_conv_sub_sq_le (hρ : IsMollifier δ ρ) {g h : E → ℝ} (hg : MemLp g 2 volume)
    (hh : MemLp h 2 volume) :
    ∫ x, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x
        - (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x) ^ 2
      ≤ ∫ x, (g x - h x) ^ 2 := by
  have key := integral_conv_sq_le hρ (hg.sub hh)
  rw [hρ.conv_sub (hg.locallyIntegrable one_le_two) (hh.locallyIntegrable one_le_two)] at key
  simpa using key

/-! ## The pointwise Cauchy–Schwarz bound -/

/-- **Pointwise Cauchy–Schwarz.**  `|(ρ ⋆ g) x| ≤ ‖ρ‖₂ ‖g‖₂`, uniformly in `x`. -/
theorem abs_conv_le (hρ : IsMollifier δ ρ) {g : E → ℝ} (hg : MemLp g 2 volume) (x : E) :
    |(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x|
      ≤ Real.sqrt (∫ t, ρ t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hmp : MeasurePreserving (fun t : E => x - t) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hgx : MemLp (fun t : E => g (x - t)) 2 volume := hg.comp_measurePreserving hmp
  have hρ2 : MemLp ρ (ENNReal.ofReal (2 : ℝ)) volume := by rw [h2]; exact hρ.memLp_two
  have habs : MemLp (fun t : E => |g (x - t)|) (ENNReal.ofReal (2 : ℝ)) volume := by
    rw [h2]; exact hgx.abs
  have hrpow : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ 2 := fun y => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : ∫ t, ρ t ^ (2 : ℝ) = ∫ t, ρ t ^ 2 := by simp only [hrpow]
  have e2 : ∫ t, |g (x - t)| ^ (2 : ℝ) = ∫ t, g t ^ 2 := by
    simp only [hrpow, sq_abs]
    exact integral_sub_left_eq_self (fun y => g y ^ 2) volume x
  rw [IsMollifier.conv_apply]
  calc |∫ t, ρ t * g (x - t)| ≤ ∫ t, |ρ t * g (x - t)| := abs_integral_le_integral_abs
    _ = ∫ t, ρ t * |g (x - t)| := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [abs_mul, abs_of_nonneg (hρ.nonneg t)]
    _ ≤ (∫ t, ρ t ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫ t, |g (x - t)| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
          (Eventually.of_forall fun t => hρ.nonneg t)
          (Eventually.of_forall fun t => abs_nonneg _) hρ2 habs
    _ = Real.sqrt (∫ t, ρ t ^ 2) * Real.sqrt (∫ t, g t ^ 2) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, e1, e2]

end RobinCaps.Compact

end
