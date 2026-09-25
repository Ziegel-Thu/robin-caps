import RobinCaps.Hausdorff.LateralChart
import RobinCaps.Domain.ThinConvex
import RobinCaps.ThinDomain.BoundaryPieces
import RobinCaps.ThinDomain.BoundaryIntegrable

/-!
# Regularity of the thin-domain profile, and consequences for the Hausdorff/lateral integral

This file collects the analytic regularity facts about the radial profile
`r = RobinCaps.Domain.profile Cm Cp L R` of the thin domain `Ω_R`
(`RobinCaps.Domain.Thin`) that are needed to compare the concrete `lateralIntegral`
of `RobinCaps.ThinDomain.Boundary` with the Hausdorff-measure boundary integral of the
`RobinCaps.Hausdorff` chapter, together with two applications:

* **Positivity and continuity** of `r` on the open axial interval
  `I = Ioo (-L/2) (L/2)` (`profile_pos_prg`, `continuousOn_profile_prg` — restatements of
  `RobinCaps.Domain.profile_pos` / `continuousOn_profile` under the `_prg` naming convention).
* **Almost-everywhere differentiability** of `r` on `I` (`ae_hasDerivAt_profile_prg`), obtained
  from the concavity of `r` (`RobinCaps.Domain.concaveOn_profile`): on the left cap piece `r` is
  monotone, on the bulk it is (trivially, everywhere) differentiable with derivative `0`, and on
  the right cap piece it is antitone; `MonotoneOn.ae_differentiableWithinAt_of_mem` (mathlib,
  `Analysis/Calculus/Monotone.lean`) then gives a.e. differentiability on each piece, and lifting
  from `DifferentiableWithinAt` to `DifferentiableAt` at the (open) interior points of each piece
  and discarding the two interface points (a null set) assembles the global statement. The set
  `D` of differentiability points of `r` on `I` is measurable
  (`measurableSet_of_differentiableAt`, unconditional in mathlib) and `I \ D` is null
  (`volume_diff_differentiableSet_profile_prg`).
* **Null images under the lateral chart** (`hausdorff_latChart_null_prg`): if `N ⊆ I` is
  Lebesgue-null then so is `latChart_lch n r '' {w | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c}` for the
  Hausdorff measure `μH[m]` on `ℝ^{n+2}` (`m = n+1`), `c < 1`. The domain set has Lebesgue measure
  zero (`RobinCaps.Domain.measurePreserving_ofEuclid` transports it to a product
  `N ×ˢ closedBall 0 c`, null by `Measure.prod_prod`), hence Hausdorff measure zero
  (`hausdorffVolume_hlin`); on a compact axial sub-box the chart is Lipschitz (`r` is Lipschitz on
  compact subintervals of `I` since it is concave there, and `hemi n` is Lipschitz on
  `closedBall 0 c`, `c < 1`, since its Fréchet derivative is operator-norm-bounded there), and a
  Lipschitz image of a Hausdorff-null set is null
  (`LipschitzOnWith.hausdorffMeasure_image_le`); a countable exhaustion of `I` by compact axial
  intervals and countable subadditivity finish the proof.
* **Integrability of the lateral density and its `ENNReal.ofReal`/`lintegral` form**
  (`integrableOn_lateralDensity_prg`, `ofReal_lateralIntegral_prg`) for a continuous nonnegative
  `g : CapSpace m → ℝ`: `lateralDensity g` is dominated, pointwise on `I`, by a constant multiple
  of `lateralDensity 1` (bounding `g` on the compact set `Icc (-L/2) (L/2) ×ˢ closedBall 0 R`),
  and `lateralDensity 1` is integrable on `I` (`RobinCaps.ThinDomain.integrableOn_lateralDensity_one_*`
  on the three axial pieces); measurability of `lateralDensity g` follows from continuity of `r`
  on `I`, unconditional measurability of `deriv r` (`measurable_deriv`), and continuity in `x` of
  the parametric sphere integral `∫ ω, g (x, r x • ω) ∂ (sphereMeasure m)`
  (`continuous_parametric_integral_of_continuous`, the sphere being compact).

Namespace `RobinCaps.Hausdorff`; every declaration name ends with the suffix `_prg`. No `sorry`,
`admit`, `axiom`, or `native_decide`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology NNReal

namespace RobinCaps.Hausdorff

open RobinCaps.Domain RobinCaps.ThinDomain RobinCaps.Cap

variable {m : ℕ} (hm : 1 ≤ m) {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
  (hL : (Cm.K + Cp.K) * R < L)

/-! ## 0. Notation -/

/-- The open axial interval `I = (-L/2, L/2)`. -/
local notation "I_prg" => Ioo (-L/2) (L/2)

/-- The radial profile `r = profile Cm Cp L R`. -/
local notation "r_prg" => profile Cm Cp L R

/-! ## 1. Positivity and continuity of the profile -/

/-- **The profile is positive on `I`.** Restatement of `RobinCaps.Domain.profile_pos`. -/
theorem profile_pos_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ∀ x ∈ (I_prg : Set ℝ), 0 < r_prg x :=
  fun x hx => profile_pos hR hL hx

/-- **The profile is continuous on `I`.** Restatement of `RobinCaps.Domain.continuousOn_profile`. -/
theorem continuousOn_profile_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ContinuousOn r_prg (I_prg : Set ℝ) :=
  continuousOn_profile hR hL

/-! ## 2. Almost-everywhere differentiability of the profile -/

/-- On the left cap the profile is monotone (nondecreasing): `θ` is antitone, and the
reparametrisation `x ↦ (-L/2 - x)/R` is (weakly) antitone in `x`, so their composition is
monotone. -/
theorem monotoneOn_profile_left_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    MonotoneOn r_prg (Ioc (-L/2) (-L/2 + Cm.K * R)) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hy.2 with hya | hya
  · have hxI : x ∈ (I_prg : Set ℝ) := ⟨hx.1, by linarith [hx.2]⟩
    have hyeq : r_prg y = R := by rw [hya]; exact profile_bulk le_rfl hmid.le
    rw [hyeq]
    exact profile_le_R hR hL hxI
  · have hxa : x < -L/2 + Cm.K * R := lt_of_le_of_lt hxy hya
    rw [profile_left hxa, profile_left hya]
    have hsx := left_param_mem hR ⟨hx.1, hxa⟩
    have hsy := left_param_mem hR ⟨hy.1, hya⟩
    have hsxy : (-L/2 - y) / R ≤ (-L/2 - x) / R := by
      have heq : (-L/2 - x) / R - (-L/2 - y) / R = (y - x) / R := by field_simp; ring
      have hnn : 0 ≤ (y - x) / R := div_nonneg (by linarith) hR.le
      linarith
    exact mul_le_mul_of_nonneg_left (Cm.θ_antitone hsy hsx hsxy) hR.le

/-- On the right cap the profile is antitone (nonincreasing). -/
theorem antitoneOn_profile_right_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    AntitoneOn r_prg (Ico (L/2 - Cp.K * R) (L/2)) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with hxb | hxb
  · have hyI : y ∈ (I_prg : Set ℝ) := ⟨by linarith [hy.1], hy.2⟩
    have hxeq : r_prg x = R := by rw [← hxb]; exact profile_bulk hmid.le le_rfl
    rw [hxeq]
    exact profile_le_R hR hL hyI
  · have hyb : L/2 - Cp.K * R < y := lt_of_lt_of_le hxb hxy
    have h1x : -L/2 + Cm.K * R ≤ x := by linarith
    have h1y : -L/2 + Cm.K * R ≤ y := by linarith
    rw [profile_right h1x hxb, profile_right h1y hyb]
    have hsx := right_param_mem hR ⟨hxb, hx.2⟩
    have hsy := right_param_mem hR ⟨hyb, hy.2⟩
    have hsxy : (x - L/2) / R ≤ (y - L/2) / R := by
      have heq : (y - L/2) / R - (x - L/2) / R = (y - x) / R := by field_simp; ring
      have hnn : 0 ≤ (y - x) / R := div_nonneg (by linarith) hR.le
      linarith
    exact mul_le_mul_of_nonneg_left (Cp.θ_antitone hsx hsy hsxy) hR.le

/-- On the (open) bulk the profile is differentiable everywhere, with derivative `0` — no
almost-everywhere exception is needed there. -/
theorem hasDerivAt_profile_bulk_prg {x : ℝ} (h1 : -L/2 + Cm.K * R < x)
    (h2 : x < L/2 - Cp.K * R) : HasDerivAt r_prg 0 x := by
  have hEv : r_prg =ᶠ[𝓝 x] fun _ => R :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds h1 h2) fun y hy => profile_bulk hy.1.le hy.2.le
  exact (hasDerivAt_const x R).congr_of_eventuallyEq hEv

/-- **The set of differentiability points of the profile within `I`.** -/
def differentiableSet_profile_prg (Cm Cp : Cap m) (L R : ℝ) : Set ℝ :=
  {x ∈ (Ioo (-L/2) (L/2) : Set ℝ) | DifferentiableAt ℝ (profile Cm Cp L R) x}

/-- **`differentiableSet_profile_prg` is measurable**, unconditionally
(`measurable_of_differentiableAt`, itself unconditional). -/
theorem measurableSet_differentiableSet_profile_prg :
    MeasurableSet (differentiableSet_profile_prg Cm Cp L R) :=
  measurableSet_Ioo.inter (measurableSet_of_differentiableAt ℝ r_prg)

/-- **The exceptional set `I \ D` is Lebesgue-null.** -/
theorem volume_diff_differentiableSet_profile_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    volume ((I_prg : Set ℝ) \ differentiableSet_profile_prg Cm Cp L R) = 0 := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  set a := -L/2 + Cm.K * R with ha_def
  set b := L/2 - Cp.K * R with hb_def
  have hML : MonotoneOn r_prg (Ioc (-L/2) a) := monotoneOn_profile_left_prg hR hL
  have hAR : AntitoneOn r_prg (Ico b (L/2)) := antitoneOn_profile_right_prg hR hL
  have hMR : MonotoneOn (fun x => -r_prg x) (Ico b (L/2)) :=
    fun x hx y hy hxy => neg_le_neg (hAR hx hy hxy)
  have haeL := hML.ae_differentiableWithinAt_of_mem
  have haeR := hMR.ae_differentiableWithinAt_of_mem
  have hSL : volume {x | x ∈ Ioc (-L/2) a ∧ ¬ DifferentiableWithinAt ℝ r_prg (Ioc (-L/2) a) x}
      = 0 := by
    have h := (MeasureTheory.ae_iff).1 haeL
    have heq : {x : ℝ | ¬ (x ∈ Ioc (-L/2) a → DifferentiableWithinAt ℝ r_prg (Ioc (-L/2) a) x)}
        = {x | x ∈ Ioc (-L/2) a ∧ ¬ DifferentiableWithinAt ℝ r_prg (Ioc (-L/2) a) x} := by
      ext x; simp only [Set.mem_setOf_eq, _root_.not_imp]
    rwa [heq] at h
  have hSR : volume {x | x ∈ Ico b (L/2) ∧
      ¬ DifferentiableWithinAt ℝ (fun x => -r_prg x) (Ico b (L/2)) x} = 0 := by
    have h := (MeasureTheory.ae_iff).1 haeR
    have heq : {x : ℝ | ¬ (x ∈ Ico b (L/2) →
        DifferentiableWithinAt ℝ (fun x => -r_prg x) (Ico b (L/2)) x)}
        = {x | x ∈ Ico b (L/2) ∧
            ¬ DifferentiableWithinAt ℝ (fun x => -r_prg x) (Ico b (L/2)) x} := by
      ext x; simp only [Set.mem_setOf_eq, _root_.not_imp]
    rwa [heq] at h
  have hsub : (I_prg : Set ℝ) \ differentiableSet_profile_prg Cm Cp L R
      ⊆ ({a, b} : Set ℝ)
        ∪ {x | x ∈ Ioc (-L/2) a ∧ ¬ DifferentiableWithinAt ℝ r_prg (Ioc (-L/2) a) x}
        ∪ {x | x ∈ Ico b (L/2) ∧
            ¬ DifferentiableWithinAt ℝ (fun x => -r_prg x) (Ico b (L/2)) x} := by
    rintro x ⟨hxI, hxD⟩
    have hnD : ¬ DifferentiableAt ℝ r_prg x := fun h => hxD ⟨hxI, h⟩
    rcases lt_trichotomy x a with hxa | hxa | hxa
    · refine Or.inl (Or.inr ⟨⟨hxI.1, hxa.le⟩, ?_⟩)
      intro hdwa
      exact hnD (hdwa.differentiableAt
        (Filter.mem_of_superset (Ioo_mem_nhds hxI.1 hxa) Ioo_subset_Ioc_self))
    · exact Or.inl (Or.inl (Or.inl hxa))
    · rcases lt_trichotomy x b with hxb | hxb | hxb
      · exact absurd (hasDerivAt_profile_bulk_prg hxa hxb).differentiableAt hnD
      · exact Or.inl (Or.inl (Or.inr hxb))
      · refine Or.inr ⟨⟨hxb.le, hxI.2⟩, ?_⟩
        intro hdwb
        have hda : DifferentiableAt ℝ (fun x => -r_prg x) x :=
          hdwb.differentiableAt
            (Filter.mem_of_superset (Ioo_mem_nhds hxb hxI.2) Ioo_subset_Ico_self)
        exact hnD (by simpa using hda.neg)
  refine measure_mono_null hsub ?_
  refine measure_union_null (measure_union_null ?_ hSL) hSR
  exact ((Set.finite_singleton b).insert a).countable.measure_zero volume

/-- **A.e. differentiability of the profile on `I`, with `HasDerivAt` at the value `deriv r`.** -/
theorem ae_hasDerivAt_profile_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ∀ᵐ x ∂(volume.restrict (I_prg : Set ℝ)), HasDerivAt r_prg (deriv r_prg x) x := by
  have hnull := volume_diff_differentiableSet_profile_prg hR hL
  have hae : ∀ᵐ x ∂ volume.restrict (I_prg : Set ℝ),
      x ∈ differentiableSet_profile_prg Cm Cp L R := by
    rw [ae_restrict_iff' measurableSet_Ioo, MeasureTheory.ae_iff]
    have heq : {a : ℝ | ¬ (a ∈ (I_prg : Set ℝ) → a ∈ differentiableSet_profile_prg Cm Cp L R)}
        = (I_prg : Set ℝ) \ differentiableSet_profile_prg Cm Cp L R := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_diff, _root_.not_imp]
    rw [heq]
    exact hnull
  filter_upwards [hae] with x hx
  exact hx.2.hasDerivAt

/-! ## 3. Null images under the lateral chart -/

/-! ### 3.0 Coordinate-splitting estimates in `Esp_lch (n+1)` -/

/-- **Pythagorean identity** for the axial/tail splitting of `Esp_lch (n+1)`. -/
theorem norm_sq_lch_prg (n : ℕ) (w : Esp_lch (n + 1)) :
    ‖w‖ ^ 2 = (w 0) ^ 2 + ‖tailE_lch n w‖ ^ 2 := by
  conv_lhs => rw [← consE_tailE_lch n w]
  exact norm_sq_consE_lch n (w 0) (tailE_lch n w)

theorem sub_apply_zero_lch_prg (n : ℕ) (w w' : Esp_lch (n + 1)) : (w - w') 0 = w 0 - w' 0 := by
  have h := map_sub (proj0CLM_lch n) w w'
  rwa [proj0_apply_lch, proj0_apply_lch, proj0_apply_lch] at h

theorem tailE_sub_lch_prg (n : ℕ) (w w' : Esp_lch (n + 1)) :
    tailE_lch n (w - w') = tailE_lch n w - tailE_lch n w' := by
  rw [← tailCLM_eq_tailE_lch, ← tailCLM_eq_tailE_lch, ← tailCLM_eq_tailE_lch, map_sub]

/-- The axial coordinate is `1`-Lipschitz on `Esp_lch (n+1)`. -/
theorem abs_sub_apply_zero_le_lch_prg (n : ℕ) (w w' : Esp_lch (n + 1)) :
    |w 0 - w' 0| ≤ ‖w - w'‖ := by
  have h := norm_sq_lch_prg n (w - w')
  rw [sub_apply_zero_lch_prg] at h
  have h2 : (w 0 - w' 0) ^ 2 ≤ ‖w - w'‖ ^ 2 := by nlinarith [sq_nonneg ‖tailE_lch n (w - w')‖]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h3

/-- The tail projection is `1`-Lipschitz on `Esp_lch (n+1)`. -/
theorem norm_tailE_sub_le_lch_prg (n : ℕ) (w w' : Esp_lch (n + 1)) :
    ‖tailE_lch n w - tailE_lch n w'‖ ≤ ‖w - w'‖ := by
  have h := norm_sq_lch_prg n (w - w')
  rw [tailE_sub_lch_prg] at h
  have h2 : ‖tailE_lch n w - tailE_lch n w'‖ ^ 2 ≤ ‖w - w'‖ ^ 2 := by
    nlinarith [sq_nonneg ((w - w') 0)]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-! ### 3.1 Lipschitz bound for `hemi` on a closed sub-ball -/

/-- The Fréchet derivative of `hemi n` at `z` has operator norm `≤ 1/√(1-c²)` on
`‖z‖ ≤ c < 1`. -/
theorem norm_Fderiv_sch_le_prg {n : ℕ} {z : Esp_lch n} {c : ℝ} (hzc : ‖z‖ ≤ c) (hc1 : c < 1) :
    ‖Fderiv_sch n z‖ ≤ 1 / Real.sqrt (1 - c ^ 2) := by
  have hc0 : 0 ≤ c := le_trans (norm_nonneg z) hzc
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hzc hc1
  have hzsqle : ‖z‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hzc 2
  have hcsq : (0 : ℝ) < 1 - c ^ 2 := by nlinarith
  have hzsq : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hinner := inner_Fderiv_sch hz1 v v
  have hself : (inner ℝ (Fderiv_sch n z v) (Fderiv_sch n z v) : ℝ) = ‖Fderiv_sch n z v‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have hvv : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hcs : (inner ℝ z v : ℝ) * inner ℝ z v ≤ ‖z‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := abs_real_inner_le_norm z v
    have h2 : |(inner ℝ z v : ℝ)| * |(inner ℝ z v : ℝ)| ≤ (‖z‖ * ‖v‖) * (‖z‖ * ‖v‖) :=
      mul_le_mul h h (abs_nonneg _) (by positivity)
    calc (inner ℝ z v : ℝ) * inner ℝ z v
        = |(inner ℝ z v : ℝ)| * |(inner ℝ z v : ℝ)| := (abs_mul_abs_self _).symm
      _ ≤ (‖z‖ * ‖v‖) * (‖z‖ * ‖v‖) := h2
      _ = ‖z‖ ^ 2 * ‖v‖ ^ 2 := by ring
  have heq : ‖Fderiv_sch n z v‖ ^ 2
      = ‖v‖ ^ 2 + (1 / (1 - ‖z‖ ^ 2)) * (inner ℝ z v * inner ℝ z v) := by
    rw [← hself, hinner, hvv]
  have hbound : ‖Fderiv_sch n z v‖ ^ 2 ≤ ‖v‖ ^ 2 / (1 - c ^ 2) := by
    rw [heq]
    have hrecip : 1 / (1 - ‖z‖ ^ 2) ≤ 1 / (1 - c ^ 2) :=
      one_div_le_one_div_of_le hcsq (by linarith)
    have ht0 : 0 ≤ (inner ℝ z v : ℝ) * inner ℝ z v := mul_self_nonneg _
    have h1 : (1 / (1 - ‖z‖ ^ 2)) * (inner ℝ z v * inner ℝ z v)
        ≤ (1 / (1 - c ^ 2)) * (‖z‖ ^ 2 * ‖v‖ ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right hrecip ht0)
        (mul_le_mul_of_nonneg_left hcs (by positivity))
    have h2 : (1 / (1 - c ^ 2)) * (‖z‖ ^ 2 * ‖v‖ ^ 2) ≤ (1 / (1 - c ^ 2)) * (c ^ 2 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hzsqle (sq_nonneg ‖v‖)) (by positivity)
    have halg : ‖v‖ ^ 2 + (1 / (1 - c ^ 2)) * (c ^ 2 * ‖v‖ ^ 2) = ‖v‖ ^ 2 / (1 - c ^ 2) := by
      field_simp
      ring
    linarith [h1, h2, halg]
  have hrhs_sq : (‖v‖ / Real.sqrt (1 - c ^ 2)) ^ 2 = ‖v‖ ^ 2 / (1 - c ^ 2) := by
    rw [div_pow, Real.sq_sqrt hcsq.le]
  have hfin : ‖Fderiv_sch n z v‖ ≤ ‖v‖ / Real.sqrt (1 - c ^ 2) := by
    have h1 : ‖Fderiv_sch n z v‖ ^ 2 ≤ (‖v‖ / Real.sqrt (1 - c ^ 2)) ^ 2 := by
      rw [hrhs_sq]; exact hbound
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h2
  rwa [div_eq_mul_inv, mul_comm, ← one_div] at hfin

/-- **`hemi n` is Lipschitz on `closedBall 0 c`, `c < 1`.** -/
theorem lipschitzOnWith_hemi_prg (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    LipschitzOnWith (Real.toNNReal (1 / Real.sqrt (1 - c ^ 2))) (hemi n)
      (Metric.closedBall (0 : Esp_lch n) c) := by
  refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := Fderiv_sch n) (fun z hz => ?_) (fun z hz => ?_) (convex_closedBall _ _)
  · have hzc : ‖z‖ ≤ c := by simpa using mem_closedBall_iff_norm.mp hz
    exact (hasFDerivAt_hemi_sch (lt_of_le_of_lt hzc hc1)).hasFDerivWithinAt
  · have hzc : ‖z‖ ≤ c := by simpa using mem_closedBall_iff_norm.mp hz
    have hb := norm_Fderiv_sch_le_prg hzc hc1
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    exact hb

/-! ### 3.2 Lipschitz bound for the profile on a compact axial sub-interval -/

/-- **The profile is Lipschitz on `Icc a b`** for `a ≤ b` in `I`. -/
theorem lipschitzOnWith_profile_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {a b : ℝ}
    (ha : -L/2 < a) (hb : b < L/2) (hab : a ≤ b) :
    ∃ K : ℝ≥0, LipschitzOnWith K r_prg (Icc a b) := by
  have hconc : ConcaveOn ℝ (I_prg : Set ℝ) r_prg := concaveOn_profile hR hL
  have hI : (I_prg : Set ℝ) = Metric.ball (0 : ℝ) (L/2) := by
    rw [Real.ball_eq_Ioo]
    congr 1 <;> ring
  rw [hI] at hconc
  have haa : |a| < L/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hbb : |b| < L/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  set ρ := (max |a| |b| + L/2) / 2 with hρ_def
  have hmax : max |a| |b| < L/2 := max_lt haa hbb
  have hρ1 : max |a| |b| < ρ := by rw [hρ_def]; linarith
  have hρ2 : ρ < L/2 := by rw [hρ_def]; linarith
  have hbdd : Bornology.IsBounded (r_prg '' Metric.ball (0 : ℝ) (L/2)) := by
    refine Bornology.IsBounded.subset (isCompact_Icc (a := (0:ℝ)) (b := R)).isBounded ?_
    rintro y ⟨x, hx, rfl⟩
    rw [← hI] at hx
    exact ⟨(profile_pos hR hL hx).le, profile_le_R hR hL hx⟩
  obtain ⟨K, hK⟩ := hconc.exists_lipschitzOnWith_of_isBounded hρ2 hbdd
  refine ⟨K, hK.mono fun x hx => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq]
  have h1 : x ≤ max |a| |b| := hx.2.trans (le_max_of_le_right (le_abs_self b))
  have h2 : -max |a| |b| ≤ x := by
    have h3 : -|a| ≤ a := neg_abs_le a
    have h4 : -max |a| |b| ≤ -|a| := by linarith [le_max_left |a| |b|]
    linarith [hx.1]
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-! ### 3.3 Lipschitz bound for the lateral chart on a compact axial-and-transverse box -/

/-- **The lateral chart is Lipschitz on `{w | w 0 ∈ Icc a b, ‖tailE_lch n w‖ ≤ c}`** for
`Icc a b ⊆ I` and `c < 1`. -/
theorem lipschitzOnWith_latChart_prg {n : ℕ} (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {a b c : ℝ} (ha : -L/2 < a) (hb : b < L/2) (hab : a ≤ b) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ K : ℝ≥0, LipschitzOnWith K (latChart_lch n r_prg)
      {w : Esp_lch (n + 1) | w 0 ∈ Icc a b ∧ ‖tailE_lch n w‖ ≤ c} := by
  obtain ⟨Kr, hKr⟩ := lipschitzOnWith_profile_prg hR hL ha hb hab
  set Kh : ℝ≥0 := Real.toNNReal (1 / Real.sqrt (1 - c ^ 2)) with hKh_def
  have hKh : LipschitzOnWith Kh (hemi n) (Metric.closedBall (0 : Esp_lch n) c) :=
    lipschitzOnWith_hemi_prg n hc0 hc1
  refine ⟨Real.toNNReal (1 + R * Kh + Kr), LipschitzOnWith.of_dist_le' fun w hw w' hw' => ?_⟩
  simp only [Set.mem_setOf_eq] at hw hw'
  have hRz : ‖tailE_lch n w‖ ≤ c := hw.2
  have hRz' : ‖tailE_lch n w'‖ ≤ c := hw'.2
  have hzmem : tailE_lch n w ∈ Metric.closedBall (0 : Esp_lch n) c := by
    simpa using hRz
  have hzmem' : tailE_lch n w' ∈ Metric.closedBall (0 : Esp_lch n) c := by
    simpa using hRz'
  have hprofw : |r_prg (w 0) - r_prg (w' 0)| ≤ Kr * |w 0 - w' 0| := by
    have := hKr.dist_le_mul (w 0) hw.1 (w' 0) hw'.1
    rwa [Real.dist_eq, Real.dist_eq] at this
  have hhemi : ‖hemi n (tailE_lch n w) - hemi n (tailE_lch n w')‖
      ≤ Kh * ‖tailE_lch n w - tailE_lch n w'‖ := by
    have := hKh.dist_le_mul (tailE_lch n w) hzmem (tailE_lch n w') hzmem'
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hw0I : w 0 ∈ (I_prg : Set ℝ) := ⟨lt_of_lt_of_le ha hw.1.1, lt_of_le_of_lt hw.1.2 hb⟩
  have hRle : |r_prg (w 0)| ≤ R := by
    rw [abs_of_pos (profile_pos hR hL hw0I)]; exact profile_le_R hR hL hw0I
  have hnormhemi' : ‖hemi n (tailE_lch n w')‖ = 1 :=
    norm_hemi_lch (lt_of_le_of_lt hRz' hc1)
  have hconsSub : consE_lch (n + 1) (w 0) (r_prg (w 0) • hemi n (tailE_lch n w))
      - consE_lch (n + 1) (w' 0) (r_prg (w' 0) • hemi n (tailE_lch n w'))
      = consE_lch (n + 1) (w 0 - w' 0)
          (r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')) := by
    rw [consE_eq_add_lch, consE_eq_add_lch, consE_eq_add_lch, map_sub, map_sub]
    abel
  have hnormsq : ‖latChart_lch n r_prg w - latChart_lch n r_prg w'‖ ^ 2
      = (w 0 - w' 0) ^ 2
        + ‖r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')‖ ^ 2 := by
    show ‖consE_lch (n + 1) (w 0) (r_prg (w 0) • hemi n (tailE_lch n w))
        - consE_lch (n + 1) (w' 0) (r_prg (w' 0) • hemi n (tailE_lch n w'))‖ ^ 2 = _
    rw [hconsSub, norm_sq_consE_lch]
  have hzpart : ‖r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')‖
      ≤ R * Kh * ‖tailE_lch n w - tailE_lch n w'‖ + Kr * |w 0 - w' 0| := by
    have hsplit : r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')
        = r_prg (w 0) • (hemi n (tailE_lch n w) - hemi n (tailE_lch n w'))
          + (r_prg (w 0) - r_prg (w' 0)) • hemi n (tailE_lch n w') := by
      rw [smul_sub, sub_smul]; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖r_prg (w 0) • (hemi n (tailE_lch n w) - hemi n (tailE_lch n w'))‖
        ≤ R * Kh * ‖tailE_lch n w - tailE_lch n w'‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |r_prg (w 0)| * ‖hemi n (tailE_lch n w) - hemi n (tailE_lch n w')‖
          ≤ R * ‖hemi n (tailE_lch n w) - hemi n (tailE_lch n w')‖ :=
            mul_le_mul_of_nonneg_right hRle (norm_nonneg _)
        _ ≤ R * (Kh * ‖tailE_lch n w - tailE_lch n w'‖) :=
            mul_le_mul_of_nonneg_left hhemi hR.le
        _ = R * Kh * ‖tailE_lch n w - tailE_lch n w'‖ := by ring
    have h2 : ‖(r_prg (w 0) - r_prg (w' 0)) • hemi n (tailE_lch n w')‖ ≤ Kr * |w 0 - w' 0| := by
      rw [norm_smul, Real.norm_eq_abs, hnormhemi', mul_one]
      exact hprofw
    linarith [h1, h2]
  have hnorm_le : ‖latChart_lch n r_prg w - latChart_lch n r_prg w'‖
      ≤ |w 0 - w' 0| + ‖r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')‖ := by
    have hsq : ‖latChart_lch n r_prg w - latChart_lch n r_prg w'‖ ^ 2
        ≤ (|w 0 - w' 0|
            + ‖r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')‖) ^ 2 := by
      have habs : |w 0 - w' 0| ^ 2 = (w 0 - w' 0) ^ 2 := sq_abs _
      nlinarith [hnormsq, habs, norm_nonneg
        (r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')),
        abs_nonneg (w 0 - w' 0)]
    have h3 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h3
  have hfinal : ‖latChart_lch n r_prg w - latChart_lch n r_prg w'‖
      ≤ (1 + R * Kh + Kr) * ‖w - w'‖ := by
    have hb1 : |w 0 - w' 0| ≤ ‖w - w'‖ := abs_sub_apply_zero_le_lch_prg n w w'
    have hb2 : ‖tailE_lch n w - tailE_lch n w'‖ ≤ ‖w - w'‖ := norm_tailE_sub_le_lch_prg n w w'
    have hstep : |w 0 - w' 0|
        + ‖r_prg (w 0) • hemi n (tailE_lch n w) - r_prg (w' 0) • hemi n (tailE_lch n w')‖
        ≤ (1 + R * Kh + Kr) * ‖w - w'‖ := by
      have h4 : R * Kh * ‖tailE_lch n w - tailE_lch n w'‖ ≤ R * Kh * ‖w - w'‖ :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
      have h5 : Kr * |w 0 - w' 0| ≤ Kr * ‖w - w'‖ :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
      nlinarith [hzpart, h4, h5, hb1]
    linarith [hnorm_le, hstep]
  rw [dist_eq_norm, dist_eq_norm]
  refine hfinal.trans ?_
  gcongr

/-! ### 3.4 Countable exhaustion of `I` by compact axial intervals -/

/-- The compact axial interval `J_k = [-L/2 + d_k, L/2 - d_k]`, `d_k = (L/2)/(k+1)`. -/
def axialPiece_prg (L : ℝ) (k : ℕ) : Set ℝ :=
  Icc (-L/2 + (L/2) / (k + 1)) (L/2 - (L/2) / (k + 1))

/-- The box `{w | w 0 ∈ J_k} ∩ S` inside `Esp_lch (n+1)`, for a set `S`. -/
def pieceSet_prg {n : ℕ} (S : Set (Esp_lch (n + 1))) (L : ℝ) (k : ℕ) : Set (Esp_lch (n + 1)) :=
  S ∩ {w | w 0 ∈ axialPiece_prg L k}

theorem exists_exhaust_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (x : ℝ)
    (hx : x ∈ (I_prg : Set ℝ)) :
    ∃ k : ℕ, x ∈ axialPiece_prg L k := by
  have hLpos : 0 < L := span_pos hR hL
  set δ := min (x - (-L/2)) (L/2 - x) with hδ_def
  have hδpos : 0 < δ := lt_min (by linarith [hx.1]) (by linarith [hx.2])
  obtain ⟨N, hN⟩ := exists_nat_gt (L / (2 * δ))
  refine ⟨N, ?_, ?_⟩
  · have hNpos : (0:ℝ) < (N:ℝ) + 1 := by positivity
    have hd : (L/2) / ((N:ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ hNpos]
      rw [div_lt_iff₀ (by positivity)] at hN
      nlinarith [hN]
    have := min_le_left (x - (-L/2)) (L/2 - x)
    linarith [hd, this]
  · have hNpos : (0:ℝ) < (N:ℝ) + 1 := by positivity
    have hd : (L/2) / ((N:ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ hNpos]
      rw [div_lt_iff₀ (by positivity)] at hN
      nlinarith [hN]
    have := min_le_right (x - (-L/2)) (L/2 - x)
    linarith [hd, this]

/-! ### 3.5 Assembly: null images of `latChart_lch` -/

/-- **A Lipschitz image of a Lebesgue-null axial-and-transverse box is `μH[m]`-null.** -/
theorem hausdorff_image_box_null_prg {n : ℕ} (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {a b c : ℝ} (ha : -L/2 < a) (hb : b < L/2) (hab : a ≤ b) (hc0 : 0 ≤ c) (hc1 : c < 1)
    {S : Set (Esp_lch (n + 1))} (hS : volume S = 0)
    (hSbox : S ⊆ {w : Esp_lch (n + 1) | w 0 ∈ Icc a b ∧ ‖tailE_lch n w‖ ≤ c}) :
    (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) : Measure (Esp_lch (n + 2)))
      (latChart_lch n r_prg '' S) = 0 := by
  obtain ⟨K, hK⟩ := lipschitzOnWith_latChart_prg (n := n) hR hL ha hb hab hc0 hc1
  have hKS : LipschitzOnWith K (latChart_lch n r_prg) S := hK.mono hSbox
  have hvol : (HausdorffVolumeProp (n + 1)) := hausdorffVolume_hlin (n + 1)
  have hSm : (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) : Measure (Esp_lch (n + 1))) S = 0 := by
    rw [hvol.1]
    simp [hS]
  have hle := hKS.hausdorffMeasure_image_le (d := ((n + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _)
  rw [hSm, mul_zero] at hle
  exact le_antisymm hle (zero_le _)

/-- **The `k`-th piece of the null image**: for `T` with `‖tailE_lch n w‖ ≤ c` on `T` and
`volume T = 0`, the image of `pieceSet_prg T L k` under the lateral chart is `μH[n+1]`-null. -/
theorem hausdorff_image_pieceSet_null_prg {n : ℕ} (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {T : Set (Esp_lch (n + 1))}
    (hTc : ∀ w ∈ T, ‖tailE_lch n w‖ ≤ c) (hTvol : volume T = 0) (k : ℕ) :
    (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) : Measure (Esp_lch (n + 2)))
      (latChart_lch n r_prg '' pieceSet_prg T L k) = 0 := by
  have hLpos : 0 < L := span_pos hR hL
  have hkpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hdpos : (0:ℝ) < (L/2) / ((k:ℝ) + 1) := by positivity
  have hdle : (L/2) / ((k:ℝ) + 1) ≤ L/2 := by
    rw [div_le_iff₀ hkpos]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hak : -L/2 < -L/2 + (L/2) / (k + 1) := by linarith
  have hbk : L/2 - (L/2) / (k + 1) < L/2 := by linarith
  have habk : -L/2 + (L/2) / (k + 1) ≤ L/2 - (L/2) / (k + 1) := by linarith
  exact hausdorff_image_box_null_prg (n := n) hR hL hak hbk habk hc0 hc1
    (measure_mono_null Set.inter_subset_left hTvol)
    (fun w hw => ⟨hw.2, hTc w hw.1⟩)

/-- **Null images under the lateral chart, core statement** (with the dimension index written
as `n + 1` directly, avoiding any relation to the ambient `m`). If `N ⊆ I` is Lebesgue-null then
the image of `{w | w 0 ∈ N, ‖tailE_lch n w‖ ≤ c}` under the lateral chart is `μH[n+1]`-null
(`c < 1`). -/
theorem hausdorff_latChart_null_core_prg {n : ℕ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) {c : ℝ} (hc1 : c < 1) {N : Set ℝ}
    (hN : N ⊆ (I_prg : Set ℝ)) (hNvol : volume N = 0) :
    (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) : Measure (Esp_lch (n + 2)))
      (latChart_lch n r_prg '' {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c}) = 0 := by
  set T : Set (Esp_lch (n + 1)) := {w | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c} with hT_def
  rcases le_or_lt 0 c with hc0 | hc0
  swap
  · have hTe : T = ∅ := by
      ext w
      simp only [hT_def, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hc⟩
      exact absurd hc (not_le.mpr (lt_of_lt_of_le hc0 (norm_nonneg _)))
    rw [hTe, Set.image_empty, measure_empty]
  · have hTeq : T = (ofEuclid n) ⁻¹' (N ×ˢ Metric.closedBall (0 : Esp_lch n) c) := by
      ext w
      simp only [hT_def, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod,
        Metric.mem_closedBall, dist_zero_right, ofEuclid_fst, ← tailE_lch_eq_ofEuclid_snd_lch]
    have hprod0 : volume (N ×ˢ Metric.closedBall (0 : Esp_lch n) c) = 0 := by
      show (volume : Measure ℝ).prod (volume : Measure (Esp_lch n))
          (N ×ˢ Metric.closedBall (0 : Esp_lch n) c) = 0
      rw [Measure.prod_prod, hNvol, zero_mul]
    have hTvol : volume T = 0 := by
      rw [hTeq]; exact (measurePreserving_ofEuclid n).preimage_null hprod0
    have hLpos : 0 < L := span_pos hR hL
    have hpiece : ∀ k : ℕ, -L/2 < -L/2 + (L/2) / (k + 1) ∧ L/2 - (L/2) / (k + 1) < L/2
        ∧ -L/2 + (L/2) / (k + 1) ≤ L/2 - (L/2) / (k + 1) := by
      intro k
      have hkpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
      have hdpos : (0:ℝ) < (L/2) / ((k:ℝ) + 1) := by positivity
      have hdle : (L/2) / ((k:ℝ) + 1) ≤ L/2 := by
        rw [div_le_iff₀ hkpos]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      exact ⟨by linarith, by linarith, by linarith⟩
    have hcover : T ⊆ ⋃ k : ℕ, pieceSet_prg T L k := by
      intro w hw
      obtain ⟨k, hk⟩ := exists_exhaust_prg hR hL (w 0) (hN hw.1)
      exact Set.mem_iUnion.mpr ⟨k, hw, hk⟩
    have hTeq2 : T = ⋃ k : ℕ, pieceSet_prg T L k :=
      Set.Subset.antisymm hcover (Set.iUnion_subset fun k => Set.inter_subset_left)
    have hstep1 : (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) : Measure (Esp_lch (n + 2)))
        (latChart_lch n r_prg '' T) = (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) :
          Measure (Esp_lch (n + 2))) (⋃ k : ℕ, latChart_lch n r_prg '' pieceSet_prg T L k) := by
      conv_lhs => rw [hTeq2]
      rw [Set.image_iUnion]
    have hstep2 : (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) : Measure (Esp_lch (n + 2)))
        (⋃ k : ℕ, latChart_lch n r_prg '' pieceSet_prg T L k)
        ≤ ∑' k : ℕ, (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) : Measure (Esp_lch (n + 2)))
          (latChart_lch n r_prg '' pieceSet_prg T L k) := measure_iUnion_le _
    have hstep3 : (∑' k : ℕ, (Measure.hausdorffMeasure ((n + 1 : ℕ) : ℝ) :
        Measure (Esp_lch (n + 2))) (latChart_lch n r_prg '' pieceSet_prg T L k)) = 0 := by
      rw [tsum_congr
        (fun k => hausdorff_image_pieceSet_null_prg hR hL hc0 hc1 (fun w hw => hw.2) hTvol k)]
      exact tsum_zero
    rw [hstep1]
    exact le_antisymm (hstep2.trans_eq hstep3) (zero_le _)

/-- **Null images under the lateral chart.** If `N ⊆ I` is Lebesgue-null then so is
`latChart_lch n r '' {w | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c}` for the Hausdorff measure `μH[m]`
(`m = n + 1`, `c < 1`). Thin wrapper around `hausdorff_latChart_null_core_prg`, which is stated
without reference to `m`; the `subst` here only has to discharge a one-line goal, avoiding an
elaboration issue that otherwise arises when `subst`-ing `m` deep inside a long nested proof. -/
theorem hausdorff_latChart_null_prg {n : ℕ} (hmn : m = n + 1) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) {c : ℝ} (hc1 : c < 1) {N : Set ℝ}
    (hN : N ⊆ (I_prg : Set ℝ)) (hNvol : volume N = 0) :
    (Measure.hausdorffMeasure (m : ℝ) : Measure (Esp_lch (n + 2)))
      (latChart_lch n r_prg '' {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c}) = 0 := by
  subst hmn
  exact hausdorff_latChart_null_core_prg hR hL hc1 hN hNvol

/-! ## 4. Integrability of the lateral density -/

/-- **The lateral density is integrable on `I`** for continuous `g` (in fact for any continuous
`g`, not only nonnegative ones: `RobinCaps.ThinDomain.integrableOn_lateralDensity_of_continuous`
already gives integrability on the three axial pieces; stitching them via
`IntervalIntegrable.trans` gives integrability on all of `I`). -/
theorem integrableOn_lateralDensity_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hg : Continuous g) :
    IntegrableOn (lateralDensity Cm Cp L R g) (I_prg : Set ℝ) := by
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  obtain ⟨h1, h2, h3⟩ := integrableOn_lateralDensity_of_continuous hR hL g hg
  have i1 : IntervalIntegrable (lateralDensity Cm Cp L R g) volume (-L/2) (-L/2 + Cm.K * R) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le).mpr h1
  have i2 : IntervalIntegrable (lateralDensity Cm Cp L R g) volume
      (-L/2 + Cm.K * R) (L/2 - Cp.K * R) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le).mpr h2
  have i3 : IntervalIntegrable (lateralDensity Cm Cp L R g) volume (L/2 - Cp.K * R) (L/2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).mpr h3
  have hcomb := (i1.trans i2).trans i3
  have hle : (-L/2 : ℝ) ≤ L/2 := by linarith
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp hcomb

/-- **Pointwise nonnegativity of the lateral density on `I`**, for `g ≥ 0`. -/
theorem nonneg_lateralDensity_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hg0 : ∀ p, 0 ≤ g p) {x : ℝ} (hx : x ∈ (I_prg : Set ℝ)) :
    0 ≤ lateralDensity Cm Cp L R g x := by
  rw [lateralDensity_eq_areaElement]
  have harea : 0 ≤ areaElement Cm Cp L R x :=
    mul_nonneg (pow_nonneg (profile_pos hR hL hx).le _) (Real.sqrt_nonneg _)
  exact mul_nonneg harea (integral_nonneg (fun ω => hg0 _))

/-- **The `ENNReal.ofReal`/`lintegral` form of the lateral integral**, for continuous `g ≥ 0`. -/
theorem ofReal_lateralIntegral_prg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hg : Continuous g) (hg0 : ∀ p, 0 ≤ g p) :
    ENNReal.ofReal (lateralIntegral Cm Cp L R g)
      = ∫⁻ x in (I_prg : Set ℝ), ENNReal.ofReal (lateralDensity Cm Cp L R g x) := by
  have hInt : IntegrableOn (lateralDensity Cm Cp L R g) (I_prg : Set ℝ) :=
    integrableOn_lateralDensity_prg hR hL g hg
  have hnn : 0 ≤ᵐ[volume.restrict (I_prg : Set ℝ)] (lateralDensity Cm Cp L R g) :=
    (ae_restrict_mem measurableSet_Ioo).mono
      (fun x hx => nonneg_lateralDensity_prg hR hL g hg0 hx)
  exact ofReal_integral_eq_lintegral_ofReal hInt hnn

end RobinCaps.Hausdorff
