import Mathlib
import RobinCaps.Sobolev.ConvexDensity
import RobinCaps.Compact.BoundaryForm

/-!
# The Poincaré–Wirtinger inequality on a bounded convex open set

This file proves the Poincaré–Wirtinger inequality for `RobinCaps.Sobolev.Weak.H1 Ω`, `Ω` a
bounded convex open subset of `EuclideanSpace ℝ (Fin n)` containing `0`: there is `CP ≥ 0` with

`∀ u : H1 Ω, ∃ t : ℝ, ∫ x in Ω, (u.toFun x - t)^2 ≤ CP * dirichlet u`.

The route is the classical convex-domain segment argument: for `F` globally `C¹` with compact
support, the fundamental theorem of calculus along the segment `[y,x] ⊆ Ω` (`Ω` convex) together
with Jensen's inequality gives `(F x - F y)^2 ≤ ‖x-y‖^2 ∫_0^1 ‖∇F(y+t(x-y))‖^2 dt`; a dilation
(about `x`, resp. `y`) change-of-variables bounds the `y`- (resp. `x`-)integral of the right side
uniformly, which is then combined into the Poincaré-with-mean inequality for `F`
(`poincare_c1_convex_pcx`).  Density of such `F` in `H1 Ω` (`exists_smooth_close_cd` of
`RobinCaps/Sobolev/ConvexDensity.lean`) then transports the inequality to all of `H1 Ω`
(`poincare_wirtinger_convex_pcx`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology InnerProductSpace

namespace RobinCaps.Sobolev.PoincareConvex

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Elementary helper lemmas -/

/-- **The directional derivative is controlled by the classical gradient.**  No differentiability
is needed (`fderiv` is junk `0` otherwise). -/
theorem abs_fderiv_apply_le_pcx (g : E → ℝ) (x v : E) :
    |fderiv ℝ g x v| ≤ ‖Weak.classicalGrad g x‖ * ‖v‖ := by
  classical
  have hv : (∑ i, (v i) • (EuclideanSpace.single i (1 : ℝ))) = v := by
    ext j
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  have hsum : fderiv ℝ g x v
      = ∑ i, v i * fderiv ℝ g x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← hv]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hin : ⟪Weak.classicalGrad g x, v⟫_ℝ
      = ∑ i, v i * fderiv ℝ g x (EuclideanSpace.single i 1) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Weak.classicalGrad_apply, RCLike.inner_apply]
  rw [hsum, ← hin]
  exact abs_real_inner_le_norm _ _

/-! ## The affine change-of-variables identity -/

/-- Translation does not change the integral over all of `E` (unconditionally: both sides use the
junk-value convention when the integrand is not integrable). -/
theorem integral_comp_add_right_pcx (G : E → ℝ) (b : E) :
    (∫ z : E, G (z + b)) = ∫ z : E, G z := by
  have h := integral_add_left_eq_self (μ := (volume : Measure E)) G b
  simpa [add_comm] using h

/-- **The affine change-of-variables identity.**  Unconditional (junk-value convention). -/
theorem integral_comp_smul_add_pcx (G : E → ℝ) {c : ℝ} (hc : 0 < c) (b : E) :
    (∫ y : E, G (c • y + b)) = (c ^ n)⁻¹ * ∫ z : E, G z := by
  have h1 := Measure.integral_comp_smul (volume : Measure E) (fun z => G (z + b)) c
  rw [finrank_euclideanSpace_fin] at h1
  rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hc.le n))] at h1
  simp only [smul_eq_mul] at h1
  rw [integral_comp_add_right_pcx G b] at h1
  exact h1

/-! ## Integrability of an indicator of a bounded set -/

/-- A continuous function restricted to a bounded measurable set is in `L²` of that set (hence
integrable, being on a finite-measure set). -/
theorem memLp_two_of_continuous_bounded_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    (hΩbdd : Bornology.IsBounded Ω) {F : Type*} [NormedAddCommGroup F] {G : E → F}
    (hGcont : Continuous G) :
    MemLp G 2 (volume.restrict Ω) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hΩbdd.isCompact_closure.exists_bound_of_continuousOn hGcont.continuousOn
  refine MemLp.of_bound hGcont.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hΩmeas] with x hx
  exact hC x (subset_closure hx)

/-- **The indicator of a bounded set against a continuous function is integrable** over all of
`E`. -/
theorem integrable_indicator_of_continuous_bounded_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    (hΩbdd : Bornology.IsBounded Ω) {G : E → ℝ} (hGcont : Continuous G) :
    Integrable (Ω.indicator G) volume := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  rw [integrable_indicator_iff hΩmeas]
  exact (memLp_two_of_continuous_bounded_pcx hΩmeas hΩbdd hGcont).integrable one_le_two

/-- Integrability transports along the affine map `y ↦ c • y + b` (`c ≠ 0`). -/
theorem integrable_comp_smul_add_pcx {H : E → ℝ} (hH : Integrable H volume) {c : ℝ} (hc : 0 < c)
    (b : E) : Integrable (fun y => H (c • y + b)) volume := by
  set Hb : E → ℝ := fun z => H (z + b) with hHbdef
  have hHb : Integrable Hb volume :=
    (measurePreserving_add_right (volume : Measure E) b).integrable_comp_of_integrable hH
  have hHbUniv : MemLp Hb 1 (volume.restrict (Set.univ : Set E)) := by
    rw [Measure.restrict_univ]
    exact memLp_one_iff_integrable.2 hHb
  have hstep := RobinCaps.Compact.memLp_comp_smul_restrict (n := n) hc MeasurableSet.univ hHbUniv
  rw [Set.preimage_univ, Measure.restrict_univ] at hstep
  have := memLp_one_iff_integrable.1 hstep
  simpa [hHbdef] using this

/-! ## The key scaling bound -/

/-- **The key scaling bound.**  If the affine map `y ↦ c • y + b` (`c > 0`) sends `Ω` into `Ω`,
then the `Ω`-integral of `G ∘ (c • · + b)` is bounded by `(c^n)⁻¹` times the `Ω`-integral of `G`,
for any continuous nonnegative `G`. -/
theorem setIntegral_comp_affine_le_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    (hΩbdd : Bornology.IsBounded Ω) {G : E → ℝ} (hGnn : ∀ z, 0 ≤ G z) (hGcont : Continuous G)
    {c : ℝ} (hc : 0 < c) (b : E) (hmaps : ∀ y ∈ Ω, c • y + b ∈ Ω) :
    (∫ y in Ω, G (c • y + b)) ≤ (c ^ n)⁻¹ * ∫ z in Ω, G z := by
  set H : E → ℝ := Ω.indicator G with hHdef
  have hHnn : ∀ z, 0 ≤ H z := fun z => by
    by_cases hz : z ∈ Ω <;> simp [hHdef, hz, hGnn]
  have hHint : Integrable H volume :=
    integrable_indicator_of_continuous_bounded_pcx hΩmeas hΩbdd hGcont
  have hHcompint : Integrable (fun y => H (c • y + b)) volume :=
    integrable_comp_smul_add_pcx hHint hc b
  have hpt : ∀ y : E, Ω.indicator (fun y => G (c • y + b)) y ≤ H (c • y + b) := by
    intro y
    by_cases hy : y ∈ Ω
    · have hy' : c • y + b ∈ Ω := hmaps y hy
      simp [hHdef, hy, hy']
    · simp [hy, hHnn]
  have h1 : (∫ y in Ω, G (c • y + b)) = ∫ y, Ω.indicator (fun y => G (c • y + b)) y := by
    rw [integral_indicator hΩmeas]
  have h2 : (∫ y, Ω.indicator (fun y => G (c • y + b)) y) ≤ ∫ y, H (c • y + b) := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun y => by
      by_cases hy : y ∈ Ω <;> simp [hy, hGnn])
      hHcompint (Eventually.of_forall hpt)
  have h3 : (∫ y : E, H (c • y + b)) = (c ^ n)⁻¹ * ∫ z : E, H z :=
    integral_comp_smul_add_pcx H hc b
  have h4 : (∫ z : E, H z) = ∫ z in Ω, G z := integral_indicator hΩmeas
  calc (∫ y in Ω, G (c • y + b)) = ∫ y, Ω.indicator (fun y => G (c • y + b)) y := h1
    _ ≤ ∫ y, H (c • y + b) := h2
    _ = (c ^ n)⁻¹ * ∫ z : E, H z := h3
    _ = (c ^ n)⁻¹ * ∫ z in Ω, G z := by rw [h4]

/-! ## FTC along a segment, combined with Jensen's inequality -/

instance isProbabilityMeasure_restrict_Ioc01_pcx :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num⟩

/-- **The segment estimate.**  For `F` globally `C¹`, `x y : E`, and `d` bounding `‖x - y‖`,
`(F x - F y)^2 ≤ d^2 ∫_0^1 ‖∇F(y + t(x-y))‖^2 dt`. -/
theorem sq_sub_le_intervalIntegral_sq_classicalGrad_pcx {F : E → ℝ} (hF : ContDiff ℝ 1 F)
    (x y : E) {d : ℝ} (hd : ‖x - y‖ ≤ d) :
    (F x - F y) ^ 2
      ≤ d ^ 2 * ∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2 := by
  set seg : ℝ → E := fun t => y + t • (x - y) with hsegdef
  have hseg0 : seg 0 = y := by simp [hsegdef]
  have hseg1 : seg 1 = x := by simp [hsegdef]
  have hdervseg : ∀ t : ℝ, HasDerivAt seg (x - y) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t • (x - y)) (x - y) t := by
      simpa using (hasDerivAt_id t).smul_const (x - y)
    simpa [hsegdef] using h1.const_add y
  set h : ℝ → ℝ := fun t => fderiv ℝ F (seg t) (x - y) with hhdef
  have hcomp : ∀ t : ℝ, HasDerivAt (fun t => F (seg t)) (h t) t := fun t =>
    (hF.differentiable le_rfl (seg t)).hasFDerivAt.comp_hasDerivAt t (hdervseg t)
  have hsegcont : Continuous seg := by fun_prop
  have hcont : Continuous h := by
    have : Continuous (fun t => fderiv ℝ F (seg t)) :=
      (hF.continuous_fderiv le_rfl).comp hsegcont
    exact this.clm_apply continuous_const
  have hFTC : (∫ t in (0:ℝ)..1, h t) = F x - F y := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => F (seg t)) (f' := h) (fun t _ => hcomp t)
      (hcont.intervalIntegrable 0 1)
    simp only at this
    rwa [hseg0, hseg1] at this
  -- Jensen's inequality on the probability measure `volume.restrict (Ioc 0 1)`
  have hmeq : (∫ t in (0:ℝ)..1, h t) = ∫ t in Set.Ioc (0:ℝ) 1, h t :=
    intervalIntegral.integral_of_le (by norm_num)
  have hmeq2 : (∫ t in (0:ℝ)..1, h t ^ 2) = ∫ t in Set.Ioc (0:ℝ) 1, h t ^ 2 :=
    intervalIntegral.integral_of_le (by norm_num)
  have hjensen : (∫ t in Set.Ioc (0:ℝ) 1, h t) ^ 2 ≤ ∫ t in Set.Ioc (0:ℝ) 1, h t ^ 2 := by
    have hconv : ConvexOn ℝ Set.univ (fun r : ℝ => r ^ 2) := (even_two).convexOn_pow
    have hcontOn : ContinuousOn (fun r : ℝ => r ^ 2) Set.univ := (continuous_pow 2).continuousOn
    have hcl : IsClosed (Set.univ : Set ℝ) := isClosed_univ
    have hfs : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), h t ∈ (Set.univ : Set ℝ) :=
      Eventually.of_forall fun _ => Set.mem_univ _
    have hfi : Integrable h (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hcont.continuousOn.integrableOn_compact (isCompact_Icc (a := (0:ℝ)) (b := 1))
        |>.mono_set Set.Ioc_subset_Icc_self
    have hgi : Integrable (fun t => h t ^ 2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (hcont.pow 2).continuousOn.integrableOn_compact (isCompact_Icc (a := (0:ℝ)) (b := 1))
        |>.mono_set Set.Ioc_subset_Icc_self
    exact hconv.map_integral_le hcontOn hcl hfs hfi hgi
  have hbound : ∀ t : ℝ, h t ^ 2 ≤ d ^ 2 * ‖Weak.classicalGrad F (seg t)‖ ^ 2 := by
    intro t
    have hb := abs_fderiv_apply_le_pcx F (seg t) (x - y)
    have hsq : h t ^ 2 ≤ (‖Weak.classicalGrad F (seg t)‖ * ‖x - y‖) ^ 2 := by
      rw [← sq_abs (h t)]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hxy2 : ‖x - y‖ ^ 2 ≤ d ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hd 2
    calc h t ^ 2 ≤ (‖Weak.classicalGrad F (seg t)‖ * ‖x - y‖) ^ 2 := hsq
      _ = ‖Weak.classicalGrad F (seg t)‖ ^ 2 * ‖x - y‖ ^ 2 := by ring
      _ ≤ ‖Weak.classicalGrad F (seg t)‖ ^ 2 * d ^ 2 :=
          mul_le_mul_of_nonneg_left hxy2 (sq_nonneg _)
      _ = d ^ 2 * ‖Weak.classicalGrad F (seg t)‖ ^ 2 := by ring
  have hintbound : (∫ t in Set.Ioc (0:ℝ) 1, h t ^ 2)
      ≤ ∫ t in Set.Ioc (0:ℝ) 1, d ^ 2 * ‖Weak.classicalGrad F (seg t)‖ ^ 2 := by
    apply setIntegral_mono_on _ _ measurableSet_Ioc (fun t _ => hbound t)
    · exact (hcont.pow 2).continuousOn.integrableOn_compact (isCompact_Icc (a := (0:ℝ)) (b := 1))
        |>.mono_set Set.Ioc_subset_Icc_self
    · have hgcont : Continuous (fun t => Weak.classicalGrad F (seg t)) :=
        (Weak.continuous_classicalGrad F hF).comp hsegcont
      have : Continuous (fun t => d ^ 2 * ‖Weak.classicalGrad F (seg t)‖ ^ 2) := by fun_prop
      exact this.continuousOn.integrableOn_compact (isCompact_Icc (a := (0:ℝ)) (b := 1))
        |>.mono_set Set.Ioc_subset_Icc_self
  have hfinal : (∫ t in Set.Ioc (0:ℝ) 1, d ^ 2 * ‖Weak.classicalGrad F (seg t)‖ ^ 2)
      = d ^ 2 * ∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (seg t)‖ ^ 2 := by
    rw [integral_const_mul, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  calc (F x - F y) ^ 2 = (∫ t in (0:ℝ)..1, h t) ^ 2 := by rw [hFTC]
    _ = (∫ t in Set.Ioc (0:ℝ) 1, h t) ^ 2 := by rw [hmeq]
    _ ≤ ∫ t in Set.Ioc (0:ℝ) 1, h t ^ 2 := hjensen
    _ ≤ ∫ t in Set.Ioc (0:ℝ) 1, d ^ 2 * ‖Weak.classicalGrad F (seg t)‖ ^ 2 := hintbound
    _ = d ^ 2 * ∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (seg t)‖ ^ 2 := hfinal

/-! ## The two directional key bounds -/

theorem segment_eq_pcx (x y : E) (t : ℝ) : y + t • (x - y) = (1 - t) • y + t • x := by
  simp only [smul_sub, sub_smul, one_smul]
  abel

/-- **Key bound, `y`-integral.**  For `x ∈ Ω`, `t ∈ [0, 1/2]`, the `y`-integral of
`‖∇F(y + t(x-y))‖²` over `Ω` is at most `2ⁿ` times `∫_Ω ‖∇F‖²`. -/
theorem yIntegral_bound_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hconv : Convex ℝ Ω) {F : E → ℝ} (hF : ContDiff ℝ 1 F) {x : E} (hx : x ∈ Ω)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (∫ y in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
      ≤ 2 ^ n * ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 := by
  have hcpos : (0:ℝ) < 1 - t := by linarith
  have hmaps : ∀ y ∈ Ω, (1 - t) • y + t • x ∈ Ω := fun y hy =>
    hconv hy hx (by linarith) ht0 (by ring)
  have hcont : Continuous (fun z : E => ‖Weak.classicalGrad F z‖ ^ 2) :=
    (Weak.continuous_classicalGrad F hF).norm.pow 2
  have hkey := setIntegral_comp_affine_le_pcx hΩmeas hΩbdd
    (G := fun z => ‖Weak.classicalGrad F z‖ ^ 2) (fun z => sq_nonneg _) hcont hcpos (t • x) hmaps
  have hbound : ((1 - t) ^ n)⁻¹ ≤ 2 ^ n := by
    have h1 : (1:ℝ)/2 ≤ 1 - t := by linarith
    have h2 : (0:ℝ) < 1/2 := by norm_num
    have h3 : ((1:ℝ)/2) ^ n ≤ (1 - t) ^ n := pow_le_pow_left₀ h2.le h1 n
    have h4 : ((1 - t) ^ n)⁻¹ ≤ (((1:ℝ)/2) ^ n)⁻¹ := inv_anti₀ (by positivity) h3
    calc ((1 - t) ^ n)⁻¹ ≤ (((1:ℝ)/2) ^ n)⁻¹ := h4
      _ = 2 ^ n := by rw [div_pow, one_pow, one_div, inv_inv]
  have heq : ∀ y : E, (1 - t) • y + t • x = y + t • (x - y) := fun y => (segment_eq_pcx x y t).symm
  simp only [heq] at hkey
  calc (∫ y in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
      ≤ ((1 - t) ^ n)⁻¹ * ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 := hkey
    _ ≤ 2 ^ n * ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hbound (integral_nonneg fun z => sq_nonneg _)

/-- **Key bound, `x`-integral.**  For `y ∈ Ω`, `t ∈ [1/2, 1]`, the `x`-integral of
`‖∇F(y + t(x-y))‖²` over `Ω` is at most `2ⁿ` times `∫_Ω ‖∇F‖²`. -/
theorem xIntegral_bound_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω) (hΩbdd : Bornology.IsBounded Ω)
    (hconv : Convex ℝ Ω) {F : E → ℝ} (hF : ContDiff ℝ 1 F) {y : E} (hy : y ∈ Ω)
    {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    (∫ x in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
      ≤ 2 ^ n * ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 := by
  have hcpos : (0:ℝ) < t := by linarith
  have hmaps : ∀ x ∈ Ω, t • x + (1 - t) • y ∈ Ω := fun x hx =>
    hconv hx hy (by linarith) (by linarith) (by ring)
  have hcont : Continuous (fun z : E => ‖Weak.classicalGrad F z‖ ^ 2) :=
    (Weak.continuous_classicalGrad F hF).norm.pow 2
  have hkey := setIntegral_comp_affine_le_pcx hΩmeas hΩbdd
    (G := fun z => ‖Weak.classicalGrad F z‖ ^ 2) (fun z => sq_nonneg _) hcont hcpos
    ((1 - t) • y) hmaps
  have hbound : (t ^ n)⁻¹ ≤ 2 ^ n := by
    have h1 : (1:ℝ)/2 ≤ t := ht0
    have h2 : (0:ℝ) < 1/2 := by norm_num
    have h3 : ((1:ℝ)/2) ^ n ≤ t ^ n := pow_le_pow_left₀ h2.le h1 n
    have h4 : (t ^ n)⁻¹ ≤ (((1:ℝ)/2) ^ n)⁻¹ := inv_anti₀ (by positivity) h3
    calc (t ^ n)⁻¹ ≤ (((1:ℝ)/2) ^ n)⁻¹ := h4
      _ = 2 ^ n := by rw [div_pow, one_pow, one_div, inv_inv]
  have heq : ∀ x : E, t • x + (1 - t) • y = y + t • (x - y) := fun x => by
    have := segment_eq_pcx x y t
    rw [this]; abel
  simp only [heq] at hkey
  calc (∫ x in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
      ≤ (t ^ n)⁻¹ * ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 := hkey
    _ ≤ 2 ^ n * ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hbound (integral_nonneg fun z => sq_nonneg _)

/-! ## A weighted Cauchy–Schwarz inequality, by expanding the square -/

/-- A continuous function is integrable on a bounded measurable set. -/
theorem integrableOn_of_continuous_bounded_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    (hΩbdd : Bornology.IsBounded Ω) {g : E → ℝ} (hgcont : Continuous g) :
    IntegrableOn g Ω volume := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  exact (memLp_two_of_continuous_bounded_pcx hΩmeas hΩbdd hgcont).integrable one_le_two

/-- **Weighted Cauchy–Schwarz.**  `(∫_Ω h)² ≤ vol(Ω) * ∫_Ω h²`, proved by expanding the
nonnegative double integral `∫_Ω ∫_Ω (h x - h y)² ≥ 0`. -/
theorem sq_setIntegral_le_measureReal_mul_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    (hΩbdd : Bornology.IsBounded Ω) {h : E → ℝ} (hcont : Continuous h) :
    (∫ y in Ω, h y) ^ 2 ≤ (volume Ω).toReal * ∫ y in Ω, h y ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  set V : ℝ := (volume Ω).toReal with hVdef
  have hIh : IntegrableOn h Ω volume := integrableOn_of_continuous_bounded_pcx hΩmeas hΩbdd hcont
  have hIh2 : IntegrableOn (fun y => h y ^ 2) Ω volume :=
    integrableOn_of_continuous_bounded_pcx hΩmeas hΩbdd (hcont.pow 2)
  have hinner : ∀ x : E, (∫ y in Ω, (h x - h y) ^ 2)
      = h x ^ 2 * V - 2 * h x * (∫ y in Ω, h y) + ∫ y in Ω, h y ^ 2 := by
    intro x
    have hcong : (∫ y in Ω, (h x - h y) ^ 2)
        = ∫ y in Ω, (h x ^ 2 - 2 * h x * h y + h y ^ 2) := by
      refine setIntegral_congr_fun hΩmeas fun y _ => ?_
      ring
    have hI1 : IntegrableOn (fun _ : E => h x ^ 2) Ω volume :=
      integrableOn_const hΩbdd.measure_lt_top.ne
    have hI2 : IntegrableOn (fun y => 2 * h x * h y) Ω volume := hIh.const_mul _
    have step1 : (∫ y in Ω, (h x ^ 2 - 2 * h x * h y + h y ^ 2))
        = (∫ y in Ω, h x ^ 2 - 2 * h x * h y) + ∫ y in Ω, h y ^ 2 :=
      integral_add (hI1.sub hI2) hIh2
    have step2 : (∫ y in Ω, h x ^ 2 - 2 * h x * h y)
        = (∫ _y in Ω, h x ^ 2) - ∫ y in Ω, 2 * h x * h y :=
      integral_sub hI1 hI2
    have step3 : (∫ _y in Ω, h x ^ 2) = h x ^ 2 * V := by
      rw [setIntegral_const]; simp [measureReal_def, hVdef, mul_comm]
    have step4 : (∫ y in Ω, 2 * h x * h y) = 2 * h x * ∫ y in Ω, h y :=
      integral_const_mul _ _
    rw [hcong, step1, step2, step3, step4]
  have houter : (∫ x in Ω, ∫ y in Ω, (h x - h y) ^ 2)
      = 2 * V * (∫ y in Ω, h y ^ 2) - 2 * (∫ y in Ω, h y) ^ 2 := by
    have hcong2 : (∫ x in Ω, ∫ y in Ω, (h x - h y) ^ 2)
        = ∫ x in Ω, (h x ^ 2 * V - 2 * h x * (∫ y in Ω, h y) + ∫ y in Ω, h y ^ 2) :=
      setIntegral_congr_fun hΩmeas fun x _ => hinner x
    have hJ1 : IntegrableOn (fun x => h x ^ 2 * V) Ω volume := hIh2.mul_const _
    have hJ2 : IntegrableOn (fun x => 2 * h x * (∫ y in Ω, h y)) Ω volume :=
      hIh.const_mul _ |>.mul_const _
    have hJ3 : IntegrableOn (fun _ : E => ∫ y in Ω, h y ^ 2) Ω volume :=
      integrableOn_const hΩbdd.measure_lt_top.ne
    have step1 : (∫ x in Ω, (h x ^ 2 * V - 2 * h x * (∫ y in Ω, h y)) + ∫ y in Ω, h y ^ 2)
        = (∫ x in Ω, h x ^ 2 * V - 2 * h x * (∫ y in Ω, h y)) + ∫ x in Ω, ∫ y in Ω, h y ^ 2 :=
      integral_add (hJ1.sub hJ2) hJ3
    have step2 : (∫ x in Ω, h x ^ 2 * V - 2 * h x * (∫ y in Ω, h y))
        = (∫ x in Ω, h x ^ 2 * V) - ∫ x in Ω, 2 * h x * (∫ y in Ω, h y) :=
      integral_sub hJ1 hJ2
    have step3 : (∫ x in Ω, h x ^ 2 * V) = (∫ x in Ω, h x ^ 2) * V := integral_mul_const _ _
    have step4a : (∫ x in Ω, 2 * h x * (∫ y in Ω, h y))
        = (∫ x in Ω, 2 * h x) * ∫ y in Ω, h y :=
      integral_mul_const _ _
    have step4b : (∫ x in Ω, 2 * h x) = 2 * ∫ x in Ω, h x := integral_const_mul _ _
    have step4 : (∫ x in Ω, 2 * h x * (∫ y in Ω, h y))
        = 2 * (∫ y in Ω, h y) * ∫ x in Ω, h x := by
      rw [step4a, step4b]
    have step5 : (∫ _x in Ω, ∫ y in Ω, h y ^ 2) = (∫ y in Ω, h y ^ 2) * V := by
      rw [setIntegral_const]; simp [measureReal_def, hVdef, mul_comm]
    rw [hcong2, step1, step2, step3, step4, step5]
    ring
  have hnonneg : 0 ≤ ∫ x in Ω, ∫ y in Ω, (h x - h y) ^ 2 :=
    integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _
  rw [houter] at hnonneg
  linarith

/-! ## Global boundedness and joint continuity for the double-integral assembly -/

/-- A `C¹` compactly supported `F` has a globally bounded squared classical gradient. -/
theorem exists_global_bound_classicalGrad_sq_pcx {F : E → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : E, ‖Weak.classicalGrad F z‖ ^ 2 ≤ M := by
  have hgc : Continuous (Weak.classicalGrad F) := Weak.continuous_classicalGrad F hF
  have hgcs : HasCompactSupport (Weak.classicalGrad F) := Weak.hasCompactSupport_classicalGrad F hFc
  obtain ⟨C, hC⟩ := hgcs.exists_bound_of_continuousOn hgc.continuousOn
  refine ⟨C ^ 2, sq_nonneg C, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (Weak.classicalGrad F)
  · exact pow_le_pow_left₀ (norm_nonneg _) (hC z hz) 2
  · have hz0 : Weak.classicalGrad F z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [hz0]
    positivity

/-- The joint segment map `(x, y, t) ↦ ‖∇F(y + t(x-y))‖²` is continuous. -/
theorem continuous_Phi_pcx {F : E → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun p : (E × E) × ℝ =>
      ‖Weak.classicalGrad F (p.1.2 + p.2 • (p.1.1 - p.1.2))‖ ^ 2) := by
  have h1 : Continuous (fun p : (E × E) × ℝ => p.1.2 + p.2 • (p.1.1 - p.1.2)) := by fun_prop
  exact ((Weak.continuous_classicalGrad F hF).comp h1).norm.pow 2

/-- A jointly continuous, globally bounded function on a product of finite-measure spaces is
integrable for the product measure. -/
theorem integrable_uncurry_of_bounded_pcx {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace α] [TopologicalSpace β] [OpensMeasurableSpace α] [OpensMeasurableSpace β]
    [SecondCountableTopologyEither α β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β → ℝ} (hcont : Continuous (Function.uncurry f)) {M : ℝ}
    (hbound : ∀ a b, |f a b| ≤ M) :
    Integrable (Function.uncurry f) (μ.prod ν) := by
  have hUniv : IntegrableOn (Function.uncurry f) Set.univ (μ.prod ν) :=
    Measure.integrableOn_of_bounded (measure_ne_top _ _) hcont.aestronglyMeasurable
      (Eventually.of_forall fun z => hbound z.1 z.2)
  rwa [integrableOn_univ] at hUniv

/-- `(x, y) ↦ ‖∇F(y + t(x-y))‖²` is continuous, for fixed `t`. -/
theorem continuous_Phi_xy_pcx {F : E → ℝ} (hF : ContDiff ℝ 1 F) (t : ℝ) :
    Continuous (fun q : E × E => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) := by
  have h1 : Continuous (fun q : E × E => q.2 + t • (q.1 - q.2)) := by fun_prop
  exact ((Weak.continuous_classicalGrad F hF).comp h1).norm.pow 2

/-- `(t, (x, y)) ↦ ‖∇F(y + t(x-y))‖²` is jointly continuous. -/
theorem continuous_Phi_joint_pcx {F : E → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun q : ℝ × (E × E) =>
      ‖Weak.classicalGrad F (q.2.2 + q.1 • (q.2.1 - q.2.2))‖ ^ 2) := by
  have h1 : Continuous (fun q : ℝ × (E × E) => q.2.2 + q.1 • (q.2.1 - q.2.2)) := by fun_prop
  exact ((Weak.continuous_classicalGrad F hF).comp h1).norm.pow 2

/-- A `C¹` compactly supported `F` is globally bounded. -/
theorem exists_global_bound_pcx {F : E → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ z : E, |F z| ≤ M0 := by
  obtain ⟨C, hC⟩ := hFc.exists_bound_of_continuousOn hF.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ tsupport F
  · exact (hC z hz).trans (le_max_left _ _)
  · have hz0 : F z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [hz0]

/-- `t ↦ ‖∇F(y + t(x-y))‖²` is continuous, for fixed `x, y`. -/
theorem continuous_Phi_t_pcx {F : E → ℝ} (hF : ContDiff ℝ 1 F) (x y : E) :
    Continuous (fun t : ℝ => ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2) := by
  have h1 : Continuous (fun t : ℝ => y + t • (x - y)) := by fun_prop
  exact ((Weak.continuous_classicalGrad F hF).comp h1).norm.pow 2

/-- Converting a `uIoc` set integral to the interval-integral notation. -/
theorem integral_uIoc_eq_intervalIntegral_pcx {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    (∫ t in Set.uIoc a b, g t) = ∫ t in a..b, g t := by
  rw [Set.uIoc_of_le hab, ← intervalIntegral.integral_of_le hab]

/-! ## The double-integral bound -/

/-- **The double-integral bound.**  `∫_Ω ∫_Ω (F x - F y)² ≤ d² 2ⁿ vol(Ω) ∫_Ω ‖∇F‖²` whenever
`‖x - y‖ ≤ d` for `x, y ∈ Ω`. -/
theorem doubleIntegral_bound_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    (hΩbdd : Bornology.IsBounded Ω) (hconv : Convex ℝ Ω) {F : E → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {d : ℝ} (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ d) :
    (∫ x in Ω, ∫ y in Ω, (F x - F y) ^ 2)
      ≤ d ^ 2 * 2 ^ n * (volume Ω).toReal * ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 := by
  haveI hΩfin : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  set V : ℝ := (volume Ω).toReal with hVdef
  set W : ℝ := ∫ z in Ω, ‖Weak.classicalGrad F z‖ ^ 2 with hWdef
  have hWnn : 0 ≤ W := integral_nonneg fun z => sq_nonneg _
  set μΩΩ : Measure (E × E) := (volume.restrict Ω).prod (volume.restrict Ω) with hμΩΩdef
  haveI hμΩΩfin : IsFiniteMeasure μΩΩ := by rw [hμΩΩdef]; infer_instance
  obtain ⟨M, hM0, hM⟩ := exists_global_bound_classicalGrad_sq_pcx hF hFc
  obtain ⟨M0, hM00, hM0'⟩ := exists_global_bound_pcx hF hFc
  have hFcont : Continuous F := hF.continuous
  -- `(F x - F y)²` is jointly continuous and globally bounded.
  have hFsubBound : ∀ q : E × E, (F q.1 - F q.2) ^ 2 ≤ (2 * M0) ^ 2 := by
    intro q
    have h1 := abs_le.1 (hM0' q.1)
    have h2 := abs_le.1 (hM0' q.2)
    have h3 : |F q.1 - F q.2| ≤ 2 * M0 :=
      abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    calc (F q.1 - F q.2) ^ 2 = |F q.1 - F q.2| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * M0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hFsub_integrable : Integrable (fun q : E × E => (F q.1 - F q.2) ^ 2) μΩΩ := by
    have := integrable_uncurry_of_bounded_pcx (volume.restrict Ω) (volume.restrict Ω)
      (f := fun x y => (F x - F y) ^ 2)
      (by fun_prop : Continuous (Function.uncurry (fun x y => (F x - F y) ^ 2)))
      (M := (2 * M0) ^ 2)
      (fun a b => by rw [abs_of_nonneg (sq_nonneg _)]; exact hFsubBound (a, b))
    simpa [hμΩΩdef, Function.uncurry] using this
  have hDeq : (∫ x in Ω, ∫ y in Ω, (F x - F y) ^ 2)
      = ∫ q : E × E, (F q.1 - F q.2) ^ 2 ∂μΩΩ :=
    integral_integral hFsub_integrable
  -- Joint integrability of `Φ` over `[0,1] × (Ω × Ω)`, and over each half.
  have hΦbound : ∀ (t : ℝ) (q : E × E),
      |‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2| ≤ M := by
    intro t q
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hM _
  have hΦcont_joint : Continuous (Function.uncurry
      (fun (t : ℝ) (q : E × E) => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)) :=
    continuous_Phi_joint_pcx hF
  haveI hfin01 : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  haveI hfin0h : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) (1/2))) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2), Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  haveI hfinh1 : IsFiniteMeasure (volume.restrict (Set.uIoc (1/2:ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Set.uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1), Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hΦ_int_full : Integrable (Function.uncurry
      (fun (t : ℝ) (q : E × E) => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod μΩΩ) :=
    integrable_uncurry_of_bounded_pcx _ _ hΦcont_joint hΦbound
  have hΦ_int_lo : Integrable (Function.uncurry
      (fun (t : ℝ) (q : E × E) => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2))
      ((volume.restrict (Set.uIoc (0:ℝ) (1/2))).prod μΩΩ) :=
    integrable_uncurry_of_bounded_pcx _ _ hΦcont_joint hΦbound
  have hΦ_int_hi : Integrable (Function.uncurry
      (fun (t : ℝ) (q : E × E) => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2))
      ((volume.restrict (Set.uIoc (1/2 : ℝ) 1)).prod μΩΩ) :=
    integrable_uncurry_of_bounded_pcx _ _ hΦcont_joint hΦbound
  -- a.e. membership of `q` in `Ω ×ˢ Ω` under `μΩΩ`.
  have hμΩΩae : ∀ᵐ q : E × E ∂μΩΩ, q ∈ Ω ×ˢ Ω := by
    rw [hμΩΩdef, Measure.prod_restrict]
    exact ae_restrict_mem (hΩmeas.prod hΩmeas)
  -- Step 1: `D ≤ d² * ∫ q, (∫ t in 0..1, Φ q) ∂μΩΩ`.
  have hIntFull : Integrable
      (fun q : E × E => ∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
      μΩΩ := by
    have h := hΦ_int_full.integral_prod_right
    simp only [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num), Function.uncurry] at h
    have hfeq : (fun q : E × E =>
        ∫ t in Set.Ioc (0:ℝ) 1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
        = fun q : E × E =>
          ∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 :=
      funext fun q => (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
    rwa [hfeq] at h
  have hstep1 : (∫ q : E × E, (F q.1 - F q.2) ^ 2 ∂μΩΩ)
      ≤ d ^ 2 * ∫ q : E × E,
          (∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun q => sq_nonneg _)
      (hIntFull.const_mul _)
    filter_upwards [hμΩΩae] with q hq
    exact sq_sub_le_intervalIntegral_sq_classicalGrad_pcx hF q.1 q.2 (hd q.1 hq.1 q.2 hq.2)
  -- Step 2: split at `t = 1/2` and bound each piece.
  have hApiece : ∀ q : E × E,
      (∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
      = (∫ t in (0:ℝ)..(1/2), ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
        + ∫ t in (1/2:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 := by
    intro q
    have hc : Continuous (fun t : ℝ => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) :=
      continuous_Phi_t_pcx hF q.1 q.2
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 (1/2)) (hc.intervalIntegrable (1/2) 1)).symm
  have hIntLo : Integrable
      (fun q : E × E => ∫ t in (0:ℝ)..(1/2), ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
      μΩΩ := by
    have h := hΦ_int_lo.integral_prod_right
    simp only [Set.uIoc_of_le (show (0:ℝ) ≤ 1/2 by norm_num), Function.uncurry] at h
    have hfeq : (fun q : E × E =>
        ∫ t in Set.Ioc (0:ℝ) (1/2), ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
        = fun q : E × E =>
          ∫ t in (0:ℝ)..(1/2), ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 :=
      funext fun q => (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2)).symm
    rwa [hfeq] at h
  have hIntHi : Integrable
      (fun q : E × E => ∫ t in (1/2:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
      μΩΩ := by
    have h := hΦ_int_hi.integral_prod_right
    simp only [Set.uIoc_of_le (show (1/2:ℝ) ≤ 1 by norm_num), Function.uncurry] at h
    have hfeq : (fun q : E × E =>
        ∫ t in Set.Ioc (1/2:ℝ) 1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2)
        = fun q : E × E =>
          ∫ t in (1/2:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 :=
      funext fun q => (intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 1)).symm
    rwa [hfeq] at h
  have hSplit : (∫ q : E × E,
      (∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ)
      = (∫ q : E × E,
          (∫ t in (0:ℝ)..(1/2), ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ)
        + ∫ q : E × E,
          (∫ t in (1/2:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ := by
    rw [← integral_add hIntLo hIntHi]
    exact integral_congr_ae (Eventually.of_forall hApiece)
  -- Piece `A` (`t ∈ [0, 1/2]`), bounded via `yIntegral_bound_pcx`.
  have hPieceA : (∫ q : E × E,
      (∫ t in (0:ℝ)..(1/2), ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ)
      ≤ 1/2 * V * 2 ^ n * W := by
    have hswap := intervalIntegral_integral_swap (a := (0:ℝ)) (b := 1/2) (μ := μΩΩ)
      (f := fun t q => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) hΦ_int_lo
    rw [← hswap]
    have hInner : ∀ t ∈ Set.Icc (0:ℝ) (1/2),
        (∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
          ≤ V * 2 ^ n * W := by
      intro t ht
      have hInt_t : Integrable
          (fun q : E × E => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) μΩΩ := by
        have hc : Continuous (Function.uncurry
            (fun x y : E => ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)) :=
          continuous_Phi_xy_pcx hF t
        have := integrable_uncurry_of_bounded_pcx (volume.restrict Ω) (volume.restrict Ω)
          (f := fun x y : E => ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2) hc
          (fun a b => by rw [abs_of_nonneg (sq_nonneg _)]; exact hM _)
        simpa [hμΩΩdef, Function.uncurry] using this
      have hunfold : (∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
          = ∫ x in Ω, ∫ y in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2 := by
        rw [hμΩΩdef]; exact integral_prod _ hInt_t
      rw [hunfold]
      have hInnerInt : IntegrableOn
          (fun x => ∫ y in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2) Ω volume :=
        hInt_t.integral_prod_left
      have hxbound : ∀ x ∈ Ω, (∫ y in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
          ≤ 2 ^ n * W := fun x hx => yIntegral_bound_pcx hΩmeas hΩbdd hconv hF hx ht.1 ht.2
      calc (∫ x in Ω, ∫ y in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
          ≤ ∫ _x in Ω, (2 ^ n * W : ℝ) :=
            setIntegral_mono_on hInnerInt (integrableOn_const hΩbdd.measure_lt_top.ne) hΩmeas
              hxbound
        _ = V * (2 ^ n * W) := by rw [setIntegral_const]; simp [measureReal_def, hVdef]
        _ = V * 2 ^ n * W := by ring
    have hHloInt : IntervalIntegrable
        (fun t => ∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
        volume 0 (1/2) :=
      intervalIntegrable_iff.2 hΦ_int_lo.integral_prod_left
    calc (∫ t in (0:ℝ)..(1/2), ∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
        ≤ ∫ _t in (0:ℝ)..(1/2), (V * 2 ^ n * W : ℝ) := by
          apply intervalIntegral.integral_mono_on (by norm_num) hHloInt intervalIntegrable_const
          exact hInner
      _ = 1/2 * V * 2 ^ n * W := by
          rw [intervalIntegral.integral_const]
          simp; ring
  -- Piece `B` (`t ∈ [1/2, 1]`), bounded via `xIntegral_bound_pcx`.
  have hPieceB : (∫ q : E × E,
      (∫ t in (1/2:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ)
      ≤ 1/2 * V * 2 ^ n * W := by
    have hswap := intervalIntegral_integral_swap (a := (1/2:ℝ)) (b := 1) (μ := μΩΩ)
      (f := fun t q => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) hΦ_int_hi
    rw [← hswap]
    have hInner : ∀ t ∈ Set.Icc (1/2:ℝ) 1,
        (∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
          ≤ V * 2 ^ n * W := by
      intro t ht
      have hInt_t : Integrable
          (fun q : E × E => ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) μΩΩ := by
        have hc : Continuous (Function.uncurry
            (fun x y : E => ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)) :=
          continuous_Phi_xy_pcx hF t
        have := integrable_uncurry_of_bounded_pcx (volume.restrict Ω) (volume.restrict Ω)
          (f := fun x y : E => ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2) hc
          (fun a b => by rw [abs_of_nonneg (sq_nonneg _)]; exact hM _)
        simpa [hμΩΩdef, Function.uncurry] using this
      have hunfold : (∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
          = ∫ y in Ω, ∫ x in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2 := by
        rw [hμΩΩdef]; exact integral_prod_symm _ hInt_t
      rw [hunfold]
      have hInnerInt : IntegrableOn
          (fun y => ∫ x in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2) Ω volume :=
        hInt_t.integral_prod_right
      have hybound : ∀ y ∈ Ω, (∫ x in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
          ≤ 2 ^ n * W := fun y hy => xIntegral_bound_pcx hΩmeas hΩbdd hconv hF hy ht.1 ht.2
      calc (∫ y in Ω, ∫ x in Ω, ‖Weak.classicalGrad F (y + t • (x - y))‖ ^ 2)
          ≤ ∫ _y in Ω, (2 ^ n * W : ℝ) :=
            setIntegral_mono_on hInnerInt (integrableOn_const hΩbdd.measure_lt_top.ne) hΩmeas
              hybound
        _ = V * (2 ^ n * W) := by rw [setIntegral_const]; simp [measureReal_def, hVdef]
        _ = V * 2 ^ n * W := by ring
    have hHhiInt : IntervalIntegrable
        (fun t => ∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
        volume (1/2) 1 :=
      intervalIntegrable_iff.2 hΦ_int_hi.integral_prod_left
    calc (∫ t in (1/2:ℝ)..1, ∫ q : E × E, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2 ∂μΩΩ)
        ≤ ∫ _t in (1/2:ℝ)..1, (V * 2 ^ n * W : ℝ) := by
          apply intervalIntegral.integral_mono_on (by norm_num) hHhiInt intervalIntegrable_const
          exact hInner
      _ = 1/2 * V * 2 ^ n * W := by
          rw [intervalIntegral.integral_const]
          simp; ring
  -- Combine.
  calc (∫ x in Ω, ∫ y in Ω, (F x - F y) ^ 2)
      = ∫ q : E × E, (F q.1 - F q.2) ^ 2 ∂μΩΩ := hDeq
    _ ≤ d ^ 2 * ∫ q : E × E,
          (∫ t in (0:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ := hstep1
    _ = d ^ 2 * ((∫ q : E × E,
          (∫ t in (0:ℝ)..(1/2), ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ)
        + ∫ q : E × E,
          (∫ t in (1/2:ℝ)..1, ‖Weak.classicalGrad F (q.2 + t • (q.1 - q.2))‖ ^ 2) ∂μΩΩ) := by
        rw [hSplit]
    _ ≤ d ^ 2 * (1/2 * V * 2 ^ n * W + 1/2 * V * 2 ^ n * W) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg d)
        linarith [hPieceA, hPieceB]
    _ = d ^ 2 * 2 ^ n * V * W := by ring

/-! ## Step 1: the Poincaré–Wirtinger inequality for `C¹` compactly supported `F` -/

/-- **Step 1 headline: the Poincaré–Wirtinger inequality for `C¹` compactly supported `F`**, on
any bounded convex measurable `Ω`. -/
theorem poincare_c1_convex_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    (hΩbdd : Bornology.IsBounded Ω) (hconv : Convex ℝ Ω) {F : E → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {d : ℝ} (hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ d) :
    (∫ x in Ω, (F x - (volume Ω).toReal⁻¹ * ∫ y in Ω, F y) ^ 2)
      ≤ d ^ 2 * 2 ^ n * ∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2 := by
  haveI hΩfin : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩbdd.measure_lt_top.ne
  set V : ℝ := (volume Ω).toReal with hVdef
  set W : ℝ := ∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2 with hWdef
  have hWnn : 0 ≤ W := integral_nonneg fun z => sq_nonneg _
  rcases eq_zero_or_pos (volume Ω) with hVz | hVpos
  · have hrestr0 : (volume.restrict Ω : Measure E) = 0 := Measure.restrict_eq_zero.mpr hVz
    have hLHS0 : (∫ x in Ω, (F x - V⁻¹ * ∫ y in Ω, F y) ^ 2) = 0 := by simp [hrestr0]
    rw [hLHS0]
    have h2n : (0:ℝ) ≤ 2 ^ n := by positivity
    exact mul_nonneg (mul_nonneg (sq_nonneg d) h2n) hWnn
  · have hVpos' : 0 < V := ENNReal.toReal_pos hVpos.ne' hΩbdd.measure_lt_top.ne
    set tmean : ℝ := V⁻¹ * ∫ y in Ω, F y with htmeandef
    have hFcont : Continuous F := hF.continuous
    have hDbound := doubleIntegral_bound_pcx hΩmeas hΩbdd hconv hF hFc hd
    obtain ⟨M0, hM00, hM0'⟩ := exists_global_bound_pcx hF hFc
    -- Integrability of `x ↦ ∫ y in Ω, (F x - F y)²` over `Ω`.
    have hFsubBound : ∀ q : E × E, (F q.1 - F q.2) ^ 2 ≤ (2 * M0) ^ 2 := by
      intro q
      have h1 := abs_le.1 (hM0' q.1)
      have h2 := abs_le.1 (hM0' q.2)
      have h3 : |F q.1 - F q.2| ≤ 2 * M0 :=
        abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      calc (F q.1 - F q.2) ^ 2 = |F q.1 - F q.2| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * M0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    have hFsub_integrable : Integrable (fun q : E × E => (F q.1 - F q.2) ^ 2)
        ((volume.restrict Ω).prod (volume.restrict Ω)) := by
      have := integrable_uncurry_of_bounded_pcx (volume.restrict Ω) (volume.restrict Ω)
        (f := fun x y => (F x - F y) ^ 2)
        (by fun_prop : Continuous (Function.uncurry (fun x y => (F x - F y) ^ 2)))
        (M := (2 * M0) ^ 2)
        (fun a b => by rw [abs_of_nonneg (sq_nonneg _)]; exact hFsubBound (a, b))
      simpa [Function.uncurry] using this
    have hFsubOn : IntegrableOn (fun x => ∫ y in Ω, (F x - F y) ^ 2) Ω volume :=
      hFsub_integrable.integral_prod_left
    -- Per-`x` Cauchy–Schwarz.
    have hperx : ∀ x ∈ Ω, (F x - tmean) ^ 2 ≤ V⁻¹ * ∫ y in Ω, (F x - F y) ^ 2 := by
      intro x _hx
      have hcont : Continuous (fun y => F x - F y) := by fun_prop
      have hcs := sq_setIntegral_le_measureReal_mul_pcx hΩmeas hΩbdd hcont
      have hlin : (∫ y in Ω, (F x - F y)) = V * (F x - tmean) := by
        have hIF : IntegrableOn F Ω volume :=
          integrableOn_of_continuous_bounded_pcx hΩmeas hΩbdd hFcont
        have hconst : (∫ _y in Ω, F x) = V * F x := by
          rw [setIntegral_const, measureReal_def, hVdef, smul_eq_mul]
        rw [integral_sub (integrableOn_const (C := F x) hΩbdd.measure_lt_top.ne) hIF, hconst,
          htmeandef, mul_sub, ← mul_assoc, mul_inv_cancel₀ hVpos'.ne', one_mul]
      rw [hlin] at hcs
      have h2 : V * (F x - tmean) ^ 2 ≤ ∫ y in Ω, (F x - F y) ^ 2 := by
        apply le_of_mul_le_mul_left _ hVpos'
        calc V * (V * (F x - tmean) ^ 2) = (V * (F x - tmean)) ^ 2 := by ring
          _ ≤ V * ∫ y in Ω, (F x - F y) ^ 2 := hcs
      have h3 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hVpos'.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hVpos'.ne', one_mul] at h3
    -- Integrate over `x`.
    have hLHScont : Continuous (fun x => (F x - tmean) ^ 2) := by fun_prop
    have hLHSon : IntegrableOn (fun x => (F x - tmean) ^ 2) Ω volume :=
      integrableOn_of_continuous_bounded_pcx hΩmeas hΩbdd hLHScont
    have hRHSon : IntegrableOn (fun x => V⁻¹ * ∫ y in Ω, (F x - F y) ^ 2) Ω volume :=
      hFsubOn.const_mul _
    calc (∫ x in Ω, (F x - tmean) ^ 2)
        ≤ ∫ x in Ω, V⁻¹ * ∫ y in Ω, (F x - F y) ^ 2 :=
          setIntegral_mono_on hLHSon hRHSon hΩmeas hperx
      _ = V⁻¹ * ∫ x in Ω, ∫ y in Ω, (F x - F y) ^ 2 := integral_const_mul _ _
      _ ≤ V⁻¹ * (d ^ 2 * 2 ^ n * V * W) :=
          mul_le_mul_of_nonneg_left hDbound (inv_nonneg.2 hVpos'.le)
      _ = d ^ 2 * 2 ^ n * W := by
          field_simp [hVpos'.ne']

/-! ## Step 2: the Minkowski / triangle inequality in `L²(Ω)`, and density -/

/-- **Minkowski's inequality in `L²(Ω)`.** -/
theorem sqrt_integral_norm_add_le_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω)
    {G : Type*} [NormedAddCommGroup G] {A B : E → G}
    (hA : MemLp A 2 (volume.restrict Ω)) (hB : MemLp B 2 (volume.restrict Ω)) :
    Real.sqrt (∫ x in Ω, ‖A x + B x‖ ^ 2)
      ≤ Real.sqrt (∫ x in Ω, ‖A x‖ ^ 2) + Real.sqrt (∫ x in Ω, ‖B x‖ ^ 2) := by
  have hAI : Integrable (fun x => ‖A x‖ ^ 2) (volume.restrict Ω) :=
    (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).1 hA
  have hBI : Integrable (fun x => ‖B x‖ ^ 2) (volume.restrict Ω) :=
    (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).1 hB
  have hABI : Integrable (fun x => ‖A x‖ * ‖B x‖) (volume.restrict Ω) := by
    have hdom : Integrable (fun x => (‖A x‖ ^ 2 + ‖B x‖ ^ 2) / 2) (volume.restrict Ω) :=
      (hAI.add hBI).div_const 2
    have hmeas : AEStronglyMeasurable (fun x => ‖A x‖ * ‖B x‖) (volume.restrict Ω) :=
      hA.aestronglyMeasurable.norm.mul hB.aestronglyMeasurable.norm
    apply hdom.mono' hmeas
    filter_upwards with x
    have hamgm : ‖A x‖ * ‖B x‖ ≤ (‖A x‖ ^ 2 + ‖B x‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖A x‖ - ‖B x‖)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hamgm
  have hCS := RobinCaps.Compact.integral_norm_mul_norm_le hA hB
  have hpt : ∀ x : E, ‖A x + B x‖ ^ 2 ≤ ‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖) + ‖B x‖ ^ 2 := by
    intro x
    calc ‖A x + B x‖ ^ 2 ≤ (‖A x‖ + ‖B x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ = ‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖) + ‖B x‖ ^ 2 := by ring
  have hIbound : Integrable (fun x => ‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖) + ‖B x‖ ^ 2)
      (volume.restrict Ω) := (hAI.add (hABI.const_mul 2)).add hBI
  have hstep : (∫ x in Ω, ‖A x + B x‖ ^ 2)
      ≤ ∫ x in Ω, (‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖) + ‖B x‖ ^ 2) :=
    setIntegral_mono_on
      ((memLp_two_iff_integrable_sq_norm (hA.aestronglyMeasurable.add hB.aestronglyMeasurable)).1
        (hA.add hB))
      hIbound hΩmeas (fun x _ => hpt x)
  have hexpand1 : (∫ x in Ω, (‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖) + ‖B x‖ ^ 2))
      = (∫ x in Ω, ‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖)) + ∫ x in Ω, ‖B x‖ ^ 2 :=
    integral_add (hAI.add (hABI.const_mul 2)) hBI
  have hexpand2 : (∫ x in Ω, (‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖)))
      = (∫ x in Ω, ‖A x‖ ^ 2) + ∫ x in Ω, 2 * (‖A x‖ * ‖B x‖) :=
    integral_add hAI (hABI.const_mul 2)
  have hexpand3 : (∫ x in Ω, 2 * (‖A x‖ * ‖B x‖)) = 2 * ∫ x in Ω, ‖A x‖ * ‖B x‖ :=
    integral_const_mul _ _
  have hexpand : (∫ x in Ω, (‖A x‖ ^ 2 + 2 * (‖A x‖ * ‖B x‖) + ‖B x‖ ^ 2))
      = (∫ x in Ω, ‖A x‖ ^ 2) + 2 * (∫ x in Ω, ‖A x‖ * ‖B x‖) + ∫ x in Ω, ‖B x‖ ^ 2 := by
    rw [hexpand1, hexpand2, hexpand3]
  have hAsq : Real.sqrt (∫ x in Ω, ‖A x‖ ^ 2) ^ 2 = ∫ x in Ω, ‖A x‖ ^ 2 :=
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)
  have hBsq : Real.sqrt (∫ x in Ω, ‖B x‖ ^ 2) ^ 2 = ∫ x in Ω, ‖B x‖ ^ 2 :=
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)
  have hle2 : (∫ x in Ω, ‖A x + B x‖ ^ 2)
      ≤ (Real.sqrt (∫ x in Ω, ‖A x‖ ^ 2) + Real.sqrt (∫ x in Ω, ‖B x‖ ^ 2)) ^ 2 := by
    rw [hexpand] at hstep
    nlinarith [hstep, hCS, hAsq, hBsq]
  calc Real.sqrt (∫ x in Ω, ‖A x + B x‖ ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∫ x in Ω, ‖A x‖ ^ 2) + Real.sqrt (∫ x in Ω, ‖B x‖ ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hle2
    _ = Real.sqrt (∫ x in Ω, ‖A x‖ ^ 2) + Real.sqrt (∫ x in Ω, ‖B x‖ ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- A real-valued norm-square equals the plain square. -/
theorem norm_sq_eq_sq_pcx (h : E → ℝ) : (fun x => ‖h x‖ ^ 2) = fun x => (h x) ^ 2 := by
  funext x; rw [Real.norm_eq_abs, sq_abs]

/-- A helper: `∀ ε > 0, a ≤ b + ε` implies `a ≤ b`, for reals. -/
theorem le_of_forall_pos_le_add_pcx {a b : ℝ} (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  have := h ((a - b) / 2) (by linarith)
  linarith

/-- The squared `L²(Ω)` distance between two real functions, via `‖·‖² = (·)²`. -/
theorem sqrtIntegral_sub_le_pcx {Ω : Set E} (hΩmeas : MeasurableSet Ω) {f g h : E → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hh : MemLp h 2 (volume.restrict Ω)) :
    Real.sqrt (∫ x in Ω, (f x - h x) ^ 2)
      ≤ Real.sqrt (∫ x in Ω, (f x - g x) ^ 2) + Real.sqrt (∫ x in Ω, (g x - h x) ^ 2) := by
  have key := sqrt_integral_norm_add_le_pcx hΩmeas (hf.sub hg) (hg.sub hh)
  simp only [Pi.sub_apply] at key
  have hcong2 : (∫ x in Ω, ‖f x - g x + (g x - h x)‖ ^ 2) = ∫ x in Ω, (f x - h x) ^ 2 := by
    refine setIntegral_congr_fun hΩmeas fun x _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  have hcong3 : (∫ x in Ω, ‖f x - g x‖ ^ 2) = ∫ x in Ω, (f x - g x) ^ 2 := by
    refine setIntegral_congr_fun hΩmeas fun x _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hcong4 : (∫ x in Ω, ‖g x - h x‖ ^ 2) = ∫ x in Ω, (g x - h x) ^ 2 := by
    refine setIntegral_congr_fun hΩmeas fun x _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  rw [hcong2, hcong3, hcong4] at key
  exact key

/-! ## The headline theorem -/

/-- **The Poincaré–Wirtinger inequality on a bounded convex open set.** -/
theorem poincare_wirtinger_convex_pcx {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ u : Weak.H1 Ω, ∃ t : ℝ,
      (∫ x in Ω, (u.toFun x - t) ^ 2) ≤ CP * Weak.dirichlet u := by
  have hΩmeas : MeasurableSet Ω := hopen.measurableSet
  haveI hΩfin : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hbdd.measure_lt_top.ne
  obtain ⟨r, hrsub⟩ := hbdd.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  have hrpos : 0 < r := by
    have := hrsub h0
    simpa using this
  have hd : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ 2 * r := by
    intro x hx y hy
    have hx' : ‖x‖ < r := by simpa using hrsub hx
    have hy' : ‖y‖ < r := by simpa using hrsub hy
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ 2 * r := by linarith
  set CP : ℝ := (2 * r) ^ 2 * 2 ^ n with hCPdef
  have hCPnn : 0 ≤ CP := by positivity
  refine ⟨CP, hCPnn, fun u => ?_⟩
  set V : ℝ := (volume Ω).toReal with hVdef
  set t : ℝ := V⁻¹ * ∫ x in Ω, u.toFun x with htdef
  refine ⟨t, ?_⟩
  rcases eq_zero_or_pos (volume Ω) with hVz | hVpos
  · have hrestr0 : (volume.restrict Ω : Measure (EuclideanSpace ℝ (Fin n))) = 0 :=
      Measure.restrict_eq_zero.mpr hVz
    have hLHS0 : (∫ x in Ω, (u.toFun x - t) ^ 2) = 0 := by simp [hrestr0]
    rw [hLHS0]
    exact mul_nonneg hCPnn (Weak.dirichlet_nonneg u)
  · have hVpos' : 0 < V := ENNReal.toReal_pos hVpos.ne' hbdd.measure_lt_top.ne
    have hDnn : 0 ≤ Weak.dirichlet u := Weak.dirichlet_nonneg u
    have main : ∀ ε : ℝ, 0 < ε →
        Real.sqrt (∫ x in Ω, (u.toFun x - t) ^ 2)
          ≤ (2 + Real.sqrt CP) * ε + Real.sqrt CP * Real.sqrt (Weak.dirichlet u) := by
      intro ε hε
      obtain ⟨F, hF, hFc, hclose⟩ :=
        RobinCaps.Sobolev.exists_smooth_close_cd hn hconv hopen hbdd h0 u
          (η := ε ^ 2) (by positivity)
      set w : Weak.H1 Ω := Weak.H1.ofCompactSupport Ω F hF hFc with hwdef
      have hmass_nonneg := Weak.mass_nonneg (w - u)
      have hdir_nonneg := Weak.dirichlet_nonneg (w - u)
      have hmass_le : Weak.mass (w - u) ≤ ε ^ 2 := by linarith
      have hdir_le : Weak.dirichlet (w - u) ≤ ε ^ 2 := by linarith
      have hmasseq : Weak.mass (w - u) = ∫ x in Ω, (F x - u.toFun x) ^ 2 := by
        rw [RobinCaps.Compact.mass_sub]
        exact setIntegral_congr_fun hΩmeas fun x _ => by simp [hwdef]
      have hFu2 : (∫ x in Ω, (F x - u.toFun x) ^ 2) ≤ ε ^ 2 := hmasseq ▸ hmass_le
      have hdireq : Weak.dirichlet (w - u)
          = ∫ x in Ω, ‖Weak.classicalGrad F x - u.grad x‖ ^ 2 := by
        show (∫ x in Ω, ‖(w - u).grad x‖ ^ 2) = _
        rw [RobinCaps.Compact.H1.sub_grad]
        exact setIntegral_congr_fun hΩmeas fun x _ => by simp [hwdef]
      have hgraddiff2 : (∫ x in Ω, ‖Weak.classicalGrad F x - u.grad x‖ ^ 2) ≤ ε ^ 2 :=
        hdireq ▸ hdir_le
      have hFcont : Continuous F := hF.continuous
      have hgcont : Continuous (Weak.classicalGrad F) := Weak.continuous_classicalGrad F hF
      have hMemF : MemLp F 2 (volume.restrict Ω) :=
        memLp_two_of_continuous_bounded_pcx hΩmeas hbdd hFcont
      have hMemGradF : MemLp (Weak.classicalGrad F) 2 (volume.restrict Ω) :=
        memLp_two_of_continuous_bounded_pcx hΩmeas hbdd hgcont
      have hgradsplit := sqrt_integral_norm_add_le_pcx hΩmeas u.grad_memL2
        (hMemGradF.sub u.grad_memL2)
      simp only [Pi.sub_apply] at hgradsplit
      have hgradeq : (∫ x in Ω, ‖u.grad x + (Weak.classicalGrad F x - u.grad x)‖ ^ 2)
          = ∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2 := by
        refine setIntegral_congr_fun hΩmeas fun x _ => ?_
        have hx : u.grad x + (Weak.classicalGrad F x - u.grad x) = Weak.classicalGrad F x := by
          abel
        rw [hx]
      rw [hgradeq] at hgradsplit
      have hdirform : (∫ x in Ω, ‖u.grad x‖ ^ 2) = Weak.dirichlet u := rfl
      rw [hdirform] at hgradsplit
      have hgraddiff_bound :
          Real.sqrt (∫ x in Ω, ‖Weak.classicalGrad F x - u.grad x‖ ^ 2) ≤ ε := by
        calc Real.sqrt (∫ x in Ω, ‖Weak.classicalGrad F x - u.grad x‖ ^ 2)
            ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hgraddiff2
          _ = ε := Real.sqrt_sq hε.le
      have hgradF_bound : Real.sqrt (∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2)
          ≤ Real.sqrt (Weak.dirichlet u) + ε := by
        calc Real.sqrt (∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2)
            ≤ Real.sqrt (Weak.dirichlet u)
              + Real.sqrt (∫ x in Ω, ‖Weak.classicalGrad F x - u.grad x‖ ^ 2) := hgradsplit
          _ ≤ Real.sqrt (Weak.dirichlet u) + ε := by linarith [hgraddiff_bound]
      have hFpoincare := poincare_c1_convex_pcx hΩmeas hbdd hconv hF hFc hd
      set tF : ℝ := V⁻¹ * ∫ x in Ω, F x with htFdef
      have hFpoincare' :
          (∫ x in Ω, (F x - tF) ^ 2) ≤ CP * ∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2 :=
        hFpoincare
      have hFtF_bound : Real.sqrt (∫ x in Ω, (F x - tF) ^ 2)
          ≤ Real.sqrt CP * (Real.sqrt (Weak.dirichlet u) + ε) := by
        calc Real.sqrt (∫ x in Ω, (F x - tF) ^ 2)
            ≤ Real.sqrt (CP * ∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2) :=
              Real.sqrt_le_sqrt hFpoincare'
          _ = Real.sqrt CP * Real.sqrt (∫ x in Ω, ‖Weak.classicalGrad F x‖ ^ 2) :=
              Real.sqrt_mul hCPnn _
          _ ≤ Real.sqrt CP * (Real.sqrt (Weak.dirichlet u) + ε) :=
              mul_le_mul_of_nonneg_left hgradF_bound (Real.sqrt_nonneg _)
      have htFtdiff : tF - t = V⁻¹ * ∫ x in Ω, (F x - u.toFun x) := by
        rw [htFdef, htdef,
          integral_sub (hMemF.integrable one_le_two) (u.memL2.integrable one_le_two)]
        ring
      have htFt_bound : Real.sqrt V * |tF - t| ≤ ε := by
        have hconst1 : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) 2
            (volume.restrict Ω) := memLp_const 1
        have hFu : MemLp (fun x => F x - u.toFun x) 2 (volume.restrict Ω) := hMemF.sub u.memL2
        have hCSconst := RobinCaps.Compact.abs_integral_mul_le_sqrt hconst1 hFu
        simp only [one_mul] at hCSconst
        have hone2 : (∫ x in Ω, (1:ℝ) ^ 2) = V := by
          rw [setIntegral_const]; simp [measureReal_def, hVdef]
        rw [hone2] at hCSconst
        have habs_bound : |∫ x in Ω, (F x - u.toFun x)| ≤ Real.sqrt V * ε := by
          calc |∫ x in Ω, (F x - u.toFun x)|
              ≤ Real.sqrt V * Real.sqrt (∫ x in Ω, (F x - u.toFun x) ^ 2) := hCSconst
            _ ≤ Real.sqrt V * Real.sqrt (ε ^ 2) :=
                mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hFu2) (Real.sqrt_nonneg _)
            _ = Real.sqrt V * ε := by rw [Real.sqrt_sq hε.le]
        rw [htFtdiff, abs_mul, abs_of_nonneg (inv_nonneg.2 hVpos'.le)]
        calc Real.sqrt V * (V⁻¹ * |∫ x in Ω, (F x - u.toFun x)|)
            ≤ Real.sqrt V * (V⁻¹ * (Real.sqrt V * ε)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left habs_bound (inv_nonneg.2 hVpos'.le))
                (Real.sqrt_nonneg _)
          _ = ε := by
              have hVV : Real.sqrt V * Real.sqrt V = V := Real.mul_self_sqrt hVpos'.le
              have heq : Real.sqrt V * (V⁻¹ * (Real.sqrt V * ε))
                  = Real.sqrt V * Real.sqrt V * V⁻¹ * ε := by ring
              rw [heq, hVV, mul_inv_cancel₀ hVpos'.ne', one_mul]
      have hMemt : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => t) 2 (volume.restrict Ω) :=
        memLp_const t
      have hMemtF : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => tF) 2 (volume.restrict Ω) :=
        memLp_const tF
      -- Step A: √∫(F - t)² ≤ √∫(F - tF)² + √∫(tF - t)²
      have hstepA := sqrtIntegral_sub_le_pcx hΩmeas hMemF hMemtF hMemt
      have htFtconst : (∫ x in Ω, (tF - t) ^ 2) = V * (tF - t) ^ 2 := by
        rw [setIntegral_const]; simp [measureReal_def, hVdef]
      have hstepA' : Real.sqrt (∫ x in Ω, (F x - t) ^ 2)
          ≤ Real.sqrt (∫ x in Ω, (F x - tF) ^ 2) + ε := by
        rw [htFtconst, Real.sqrt_mul (le_of_lt hVpos'), Real.sqrt_sq_eq_abs] at hstepA
        linarith [hstepA, htFt_bound]
      have hFt_bound : Real.sqrt (∫ x in Ω, (F x - t) ^ 2)
          ≤ Real.sqrt CP * (Real.sqrt (Weak.dirichlet u) + ε) + ε := by
        calc Real.sqrt (∫ x in Ω, (F x - t) ^ 2)
            ≤ Real.sqrt (∫ x in Ω, (F x - tF) ^ 2) + ε := hstepA'
          _ ≤ Real.sqrt CP * (Real.sqrt (Weak.dirichlet u) + ε) + ε := by linarith [hFtF_bound]
      -- Step B: √∫(u.toFun - t)² ≤ √∫(u.toFun - F)² + √∫(F - t)²
      have hstepB := sqrtIntegral_sub_le_pcx hΩmeas u.memL2 hMemF hMemt
      have huF_eq : (∫ x in Ω, (u.toFun x - F x) ^ 2) = ∫ x in Ω, (F x - u.toFun x) ^ 2 := by
        refine setIntegral_congr_fun hΩmeas fun x _ => ?_
        ring
      have huF_bound : Real.sqrt (∫ x in Ω, (u.toFun x - F x) ^ 2) ≤ ε := by
        rw [huF_eq]
        calc Real.sqrt (∫ x in Ω, (F x - u.toFun x) ^ 2) ≤ Real.sqrt (ε ^ 2) :=
              Real.sqrt_le_sqrt hFu2
          _ = ε := Real.sqrt_sq hε.le
      calc Real.sqrt (∫ x in Ω, (u.toFun x - t) ^ 2)
          ≤ Real.sqrt (∫ x in Ω, (u.toFun x - F x) ^ 2) + Real.sqrt (∫ x in Ω, (F x - t) ^ 2) :=
            hstepB
        _ ≤ ε + (Real.sqrt CP * (Real.sqrt (Weak.dirichlet u) + ε) + ε) := by
            linarith [huF_bound, hFt_bound]
        _ = (2 + Real.sqrt CP) * ε + Real.sqrt CP * Real.sqrt (Weak.dirichlet u) := by ring
    -- Take ε → 0.
    have hmainδ : ∀ δ : ℝ, 0 < δ →
        Real.sqrt (∫ x in Ω, (u.toFun x - t) ^ 2)
          ≤ Real.sqrt CP * Real.sqrt (Weak.dirichlet u) + δ := by
      intro δ hδ
      have hCfactor : 0 < 2 + Real.sqrt CP := by positivity
      have := main (δ / (2 + Real.sqrt CP)) (by positivity)
      have hcancel : (2 + Real.sqrt CP) * (δ / (2 + Real.sqrt CP)) = δ := by
        field_simp
      rw [hcancel] at this
      linarith
    have hfinal : Real.sqrt (∫ x in Ω, (u.toFun x - t) ^ 2)
        ≤ Real.sqrt CP * Real.sqrt (Weak.dirichlet u) :=
      le_of_forall_pos_le_add_pcx hmainδ
    have hCPD : Real.sqrt CP * Real.sqrt (Weak.dirichlet u) = Real.sqrt (CP * Weak.dirichlet u) :=
      (Real.sqrt_mul hCPnn _).symm
    rw [hCPD] at hfinal
    have hLHSnn : 0 ≤ ∫ x in Ω, (u.toFun x - t) ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hRHSnn : 0 ≤ CP * Weak.dirichlet u := mul_nonneg hCPnn hDnn
    calc (∫ x in Ω, (u.toFun x - t) ^ 2)
        = Real.sqrt (∫ x in Ω, (u.toFun x - t) ^ 2) ^ 2 := (Real.sq_sqrt hLHSnn).symm
      _ ≤ Real.sqrt (CP * Weak.dirichlet u) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hfinal 2
      _ = CP * Weak.dirichlet u := Real.sq_sqrt hRHSnn

end RobinCaps.Sobolev.PoincareConvex
