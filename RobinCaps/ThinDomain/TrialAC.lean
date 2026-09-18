import Mathlib
import RobinCaps.ThinDomain.BulkEnergy
import RobinCaps.ThinDomain.BulkProj
import RobinCaps.ThinDomain.Trial
import RobinCaps.ThinDomain.Restrict
import RobinCaps.ThinDomain.SliceThin

/-!
# U-TRIAL-AC: the trial extension `𝒯_R F` for a merely absolutely continuous axial factor

This file formalizes the manuscript's trial extension (`eq:trial-extension`)

`𝒯_R F (x, z) = F (clamp_{[x₋,x₊]} x) · ψ_R (z)`,   `x₋ = -L/2 + K₋R`,  `x₊ = L/2 - K₊R`,

for an **arbitrary** `F ∈ H¹(0, ℓ_R)` (absolutely continuous, *not* `C¹`), where
`ℓ_R = bulkLength Cm Cp L R`.  `RobinCaps/ThinDomain/Trial.lean` treats the same object under
the extra hypothesis `F ∈ C¹` (via `H1P.ofPiecewise`); here the axial factor is only weakly
differentiable, so the one-dimensional integration by parts has to be the *weak* one
(`RobinCaps.Sobolev.hasWeakDeriv_primitive`).

## Contents

1. `trialACProfile xm W`, `trialACProfileDeriv xm W` — the translated, clamped axial profile
   `x ↦ W (clamp_{[0,ℓ]} (x - xm))` and its a.e. derivative (`W' (· - xm)` inside
   `(xm, xm+ℓ)`, `0` outside), with
   * `trialACProfile_eq_add_integral` — the profile is the primitive of its derivative (the
     only use of the `ftc` field of `RobinCaps.Sobolev.H1`), and
   * `trialACProfile_integral_mul_deriv` — the resulting **global** weak integration by parts
     `∫_ℝ W_c φ' = - ∫_ℝ W_c' φ` for every test function `φ` on the line.
2. `trialACFun`, `trialACGx`, `trialACGz`, `hasWeakGradP_trialAC`, `trialAC` — the trial
   extension and its weak gradient on the thin domain `Ω_R`, as an element of `H1P Ω_R`.
   The axial half of the weak-gradient identity is Fubini in `z` plus the one-dimensional
   identity above on every line; the transverse half is Fubini in `x` plus `ψ_R.hasWeakGrad`
   on every slice (every transverse slice of `Ω_R` is contained in `B_m(R)`).
3. `trialAC_add`, `trialAC_smul`, `trialACₗ`, `liftQ`, `liftQ_mk` — the **linear lift**.
   *Honest modelling note.*  `W ↦ trialAC W ψ` is additive only at the level of the
   representative `toFun`: the *chosen* axial weak derivative is `deriv W.toFun`, and `deriv`
   is additive only almost everywhere (an `H¹` function need not be differentiable at a given
   point).  Consequently the linear map is
   `trialACₗ : Sobolev.H1 ℓ_R →ₗ[ℝ] H1PQ Ω_R` — the target is the **a.e. quotient**, whose
   null space `nullAEP` only sees `toFun` — and it descends to
   `liftQ : Sobolev.H1Q ℓ_R →ₗ[ℝ] H1PQ Ω_R`.  This is exactly the type of the `lift` field of
   `RobinCaps.ThinDomain.GlobalComparisonData`.
4. `restrictBulkP_trialAC_toFun`, `axialCoeff_trialAC`, `bulkRepT_trialAC`,
   `bulkProjThin_liftQ`, `bulkProjThin_surjective_trialAC` — on the bulk cylinder the trial
   extension **is** the tensor `W(· - x₋) ⊗ ψ_R`, so the bulk projection undoes the trial
   extension, which discharges the target
   `RobinCaps.ThinDomain.BulkProjThinSurjective` of `RobinCaps/ThinDomain/BulkProj.lean`.
   The auxiliary `h1Congr` / `h1QCongr` / `eqMpr_linearMap` make explicit the transport
   `ℓ_R = x₊ - x₋` hidden inside the definition of `bulkProjThin`.
5. `massP_trialAC`, `dirichletP_trialAC` — the exact three-piece splittings
   `N_{Ω_R}[𝒯_RW] = N_cap⁻ + M[W]·N_B[ψ_R] + N_cap⁺`,
   `D_{Ω_R}[𝒯_RW] = D_cap⁻ + (D[W]·N_B[ψ_R] + M[W]·D_B[ψ_R]) + D_cap⁺`,
   and `mass_le_massP_trialAC` / `massQ_le_massPQ_liftQ` — `eq:trial-mass` (left half), i.e.
   the `trial_mass` field of `GlobalComparisonData`.

Everything is proved: no `sorry`, `admit`, `axiom` or `native_decide`.
-/
open MeasureTheory Set Filter Metric

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Domain

noncomputable section

variable {m : ℕ}

/-! ## 1. The clamped, translated axial profile of an `H¹(0,ℓ)` function -/

section Profile

variable {ℓ xm : ℝ}

/-- **The axial factor of the trial extension.**  `W` is first translated by `xm` and then
clamped to `[0, ℓ]`: the profile is constant `W 0` to the left of `xm`, equal to `W (· - xm)` on
`[xm, xm + ℓ]` and constant `W ℓ` to the right. -/
def trialACProfile (xm : ℝ) {ℓ : ℝ} (W : Sobolev.H1 ℓ) (x : ℝ) : ℝ :=
  W.toFun (axialClamp 0 ℓ (x - xm))

/-- The almost-everywhere derivative of `trialACProfile`: `W' (· - xm)` inside `(xm, xm+ℓ)`
and `0` outside. -/
def trialACProfileDeriv (xm : ℝ) {ℓ : ℝ} (W : Sobolev.H1 ℓ) (x : ℝ) : ℝ :=
  Set.indicator (Ioo xm (xm + ℓ)) (fun t => deriv W.toFun (t - xm)) x

theorem trialACProfile_of_le (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) {x : ℝ} (hx : x ≤ xm) :
    trialACProfile xm W x = W.toFun 0 := by
  have h : axialClamp (0 : ℝ) ℓ (x - xm) = 0 := by
    rcases lt_or_eq_of_le (sub_nonpos.2 hx) with h | h
    · exact axialClamp_of_lt h
    · rw [h, axialClamp_of_mem le_rfl hℓ]
  rw [trialACProfile, h]

theorem trialACProfile_of_mem (W : Sobolev.H1 ℓ) {x : ℝ} (h1 : xm ≤ x) (h2 : x ≤ xm + ℓ) :
    trialACProfile xm W x = W.toFun (x - xm) := by
  rw [trialACProfile, axialClamp_of_mem (by linarith) (by linarith)]

theorem trialACProfile_of_ge (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) {x : ℝ} (hx : xm + ℓ ≤ x) :
    trialACProfile xm W x = W.toFun ℓ := by
  have h : axialClamp (0 : ℝ) ℓ (x - xm) = ℓ := by
    rcases lt_or_eq_of_le (by linarith : ℓ ≤ x - xm) with h | h
    · exact axialClamp_of_gt (by linarith) h
    · rw [← h]; exact axialClamp_of_mem hℓ le_rfl
  rw [trialACProfile, h]

theorem trialACProfile_mem_image (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) (x : ℝ) :
    ∃ y ∈ Icc (0 : ℝ) ℓ, trialACProfile xm W x = W.toFun y :=
  ⟨axialClamp 0 ℓ (x - xm), axialClamp_mem_Icc hℓ _, rfl⟩

theorem continuous_trialACProfile (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) :
    Continuous (trialACProfile xm W) := by
  have hW : ContinuousOn W.toFun (Icc 0 ℓ) := h1_continuousOn hℓ W
  have hc : Continuous fun x : ℝ => axialClamp 0 ℓ (x - xm) :=
    (continuous_axialClamp hℓ).comp (continuous_id.sub continuous_const)
  exact hW.comp_continuous hc fun x => axialClamp_mem_Icc hℓ _

/-- The clamped profile is globally bounded: its values are the values of `W` on `[0,ℓ]`. -/
theorem exists_bound_trialACProfile (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |trialACProfile xm W x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := ℓ)).exists_bound_of_continuousOn (h1_continuousOn hℓ W)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have := hC _ (axialClamp_mem_Icc hℓ (x - xm))
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem measurable_trialACProfileDeriv (W : Sobolev.H1 ℓ) :
    Measurable (trialACProfileDeriv xm W) := by
  have h : Measurable fun t : ℝ => deriv W.toFun (t - xm) :=
    (measurable_deriv W.toFun).comp (measurable_id.sub_const xm)
  exact h.indicator measurableSet_Ioo

theorem intervalIntegrable_deriv_translate (W : Sobolev.H1 ℓ) :
    IntervalIntegrable (fun t => deriv W.toFun (t - xm)) volume xm (xm + ℓ) := by
  have h := W.deriv_int.comp_sub_right xm
  rw [zero_add, add_comm ℓ xm] at h
  exact h

theorem intervalIntegrable_deriv_translate_sq (W : Sobolev.H1 ℓ) :
    IntervalIntegrable (fun t => deriv W.toFun (t - xm) ^ 2) volume xm (xm + ℓ) := by
  have h := W.deriv_sq_int.comp_sub_right xm
  rw [zero_add, add_comm ℓ xm] at h
  exact h

theorem integrable_trialACProfileDeriv (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) :
    Integrable (trialACProfileDeriv xm W) volume := by
  have he : trialACProfileDeriv xm W
      = Set.indicator (Ioo xm (xm + ℓ)) (fun t => deriv W.toFun (t - xm)) := rfl
  rw [he, integrable_indicator_iff measurableSet_Ioo]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1
    (intervalIntegrable_deriv_translate W)

theorem memLp_two_trialACProfileDeriv (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) :
    MemLp (trialACProfileDeriv xm W) 2 volume := by
  refine (memLp_two_iff_integrable_sq
    (measurable_trialACProfileDeriv W).aestronglyMeasurable).2 ?_
  have hsq : (fun x => trialACProfileDeriv xm W x ^ 2)
      = Set.indicator (Ioo xm (xm + ℓ)) (fun t => deriv W.toFun (t - xm) ^ 2) := by
    funext x
    by_cases h : x ∈ Ioo xm (xm + ℓ)
    · simp [trialACProfileDeriv, Set.indicator_of_mem h]
    · simp [trialACProfileDeriv, Set.indicator_of_notMem h]
  rw [hsq, integrable_indicator_iff measurableSet_Ioo]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1
    (intervalIntegrable_deriv_translate_sq W)

/-- **The clamped profile is the primitive of its derivative.**  This is the only place where
the `ftc` field of `RobinCaps.Sobolev.H1` is used. -/
theorem trialACProfile_eq_add_integral (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) (x : ℝ) :
    trialACProfile xm W x = W.toFun 0 + ∫ t in xm..x, trialACProfileDeriv xm W t := by
  have hgi : Integrable (trialACProfileDeriv xm W) volume :=
    integrable_trialACProfileDeriv hℓ W
  have hzero : ∀ a b : ℝ, (∀ t ∈ uIcc a b, t ∉ Ioo xm (xm + ℓ)) →
      (∫ t in a..b, trialACProfileDeriv xm W t) = 0 := by
    intro a b h
    have : (∫ t in a..b, trialACProfileDeriv xm W t) = ∫ _t in a..b, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      simp [trialACProfileDeriv, Set.indicator_of_notMem (h t ht)]
    rw [this, intervalIntegral.integral_zero]
  have hmid : ∀ y : ℝ, xm ≤ y → y ≤ xm + ℓ →
      (∫ t in xm..y, trialACProfileDeriv xm W t) = W.toFun (y - xm) - W.toFun 0 := by
    intro y h1 h2
    have hae : ∀ᵐ t : ℝ, t ≠ xm + ℓ := by rw [ae_iff]; simp
    have hcongr : (∫ t in xm..y, trialACProfileDeriv xm W t)
        = ∫ t in xm..y, deriv W.toFun (t - xm) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with t ht hmem
      rw [Set.uIoc_of_le h1] at hmem
      have hmem' : t ∈ Ioo xm (xm + ℓ) := ⟨hmem.1, lt_of_le_of_ne (hmem.2.trans h2) ht⟩
      simp [trialACProfileDeriv, Set.indicator_of_mem hmem']
    rw [hcongr, intervalIntegral.integral_comp_sub_right (fun s => deriv W.toFun s) xm, sub_self]
    have hftc := W.ftc (y - xm) ⟨by linarith, by linarith⟩
    linarith
  rcases le_or_gt x xm with hx | hx
  · have h0 : (∫ t in xm..x, trialACProfileDeriv xm W t) = 0 := by
      refine hzero _ _ fun t ht => ?_
      rw [uIcc_of_ge hx] at ht
      exact fun hmem => absurd hmem.1 (not_lt.2 ht.2)
    rw [trialACProfile_of_le hℓ W hx, h0, add_zero]
  · rcases le_or_gt x (xm + ℓ) with hx' | hx'
    · rw [trialACProfile_of_mem W hx.le hx', hmid x hx.le hx']
      ring
    · have hsplit : (∫ t in xm..x, trialACProfileDeriv xm W t)
          = (∫ t in xm..(xm + ℓ), trialACProfileDeriv xm W t)
            + ∫ t in (xm + ℓ)..x, trialACProfileDeriv xm W t :=
        (intervalIntegral.integral_add_adjacent_intervals hgi.intervalIntegrable
          hgi.intervalIntegrable).symm
      have h2 : (∫ t in (xm + ℓ)..x, trialACProfileDeriv xm W t) = 0 := by
        refine hzero _ _ fun t ht => ?_
        rw [uIcc_of_le hx'.le] at ht
        exact fun hmem => absurd hmem.2 (not_lt.2 ht.1)
      have h1 := hmid (xm + ℓ) (by linarith) le_rfl
      rw [add_sub_cancel_left] at h1
      rw [trialACProfile_of_ge hℓ W hx'.le, hsplit, h1, h2]
      ring

/-! ### The one-dimensional weak integration by parts -/

/-- **The clamped profile has `trialACProfileDeriv` as a global weak derivative on `ℝ`.**

This is the analytic heart of the file: no differentiability of `W` is used, only that `W` is
the primitive of `deriv W` (`RobinCaps.Sobolev.hasWeakDeriv_primitive`). -/
theorem trialACProfile_integral_mul_deriv (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ)
    {xm : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, trialACProfile xm W x * deriv φ x)
      = - ∫ x, trialACProfileDeriv xm W x * φ x := by
  classical
  set g : ℝ → ℝ := trialACProfileDeriv xm W with hgdef
  have hgi : Integrable g volume := integrable_trialACProfileDeriv hℓ W
  have hcont : Continuous (trialACProfile xm W) := continuous_trialACProfile hℓ W
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  have hφ1 : Continuous φ := hφ.continuous
  -- a large interval containing the support of `φ` and the translation point
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hφc.isBounded
  set N : ℝ := max r |xm| + 1 with hNdef
  have hr0 : r ≤ max r |xm| := le_max_left _ _
  have hxm0 : |xm| ≤ max r |xm| := le_max_right _ _
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ |xm| := abs_nonneg _
    have : (0 : ℝ) ≤ max r |xm| := le_trans this hxm0
    linarith
  have hNlt : -N < N := by linarith
  have hφs : tsupport φ ⊆ Ioo (-N) N := by
    intro t ht
    have h1 : |t| ≤ r := by
      simpa [Real.norm_eq_abs, mem_closedBall_zero_iff] using hr ht
    rcases abs_le.1 h1 with ⟨h2, h3⟩
    exact ⟨by linarith, by linarith⟩
  have hxmMem : xm ∈ Icc (-N) N := by
    rcases abs_le.1 (le_refl |xm|) with _
    exact ⟨by cases abs_le.1 (le_refl |xm|) with | intro h _ => linarith,
      by cases abs_le.1 (le_refl |xm|) with | intro _ h => linarith⟩
  -- the weak derivative of the primitive
  have hgOn : IntegrableOn g (Ioo (-N) N) := hgi.integrableOn
  have hprim : Sobolev.HasWeakDeriv (-N) N (fun x => ∫ t in xm..x, g t) g :=
    Sobolev.hasWeakDeriv_primitive hNlt hgOn hxmMem
  have hIBP := hprim φ hφ hφc hφs
  -- rewrite the primitive as the profile minus a constant
  have hPeq : ∀ x : ℝ, (∫ t in xm..x, g t) = trialACProfile xm W x - W.toFun 0 := by
    intro x
    rw [trialACProfile_eq_add_integral hℓ W x]
    ring
  have hIBP' : (∫ x in Ioo (-N) N, (trialACProfile xm W x - W.toFun 0) * deriv φ x)
      = - ∫ x in Ioo (-N) N, g x * φ x := by
    rw [← hIBP]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    show (trialACProfile xm W x - W.toFun 0) * deriv φ x = (∫ t in xm..x, g t) * deriv φ x
    rw [hPeq x]
  -- split the left-hand side
  have hint1 : IntegrableOn (fun x => trialACProfile xm W x * deriv φ x) (Ioo (-N) N) volume :=
    ((hcont.mul hφ'.continuous).continuousOn.integrableOn_compact
      (isCompact_Icc (a := -N) (b := N))).mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun x => W.toFun 0 * deriv φ x) (Ioo (-N) N) volume :=
    (((continuous_const.mul hφ'.continuous)).continuousOn.integrableOn_compact
      (isCompact_Icc (a := -N) (b := N))).mono_set Ioo_subset_Icc_self
  have hsub : (∫ x in Ioo (-N) N, (trialACProfile xm W x - W.toFun 0) * deriv φ x)
      = (∫ x in Ioo (-N) N, trialACProfile xm W x * deriv φ x)
        - ∫ x in Ioo (-N) N, W.toFun 0 * deriv φ x := by
    rw [← integral_sub hint1 hint2]
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    ring
  have hdz : (∫ x in Ioo (-N) N, W.toFun 0 * deriv φ x) = 0 := by
    rw [integral_const_mul, setIntegral_deriv_test_zero hφ hφc hφs, mul_zero]
  -- pass from the interval to all of `ℝ`
  have hL : (∫ x in Ioo (-N) N, trialACProfile xm W x * deriv φ x)
      = ∫ x, trialACProfile xm W x * deriv φ x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxs : x ∉ tsupport φ := fun h => hx (hφs h)
    have hts : tsupport (deriv φ) ⊆ tsupport φ :=
      closure_minimal support_deriv_subset (isClosed_tsupport φ)
    have hd0 : deriv φ x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hxs (hts h)
    rw [hd0, mul_zero]
  have hR : (∫ x in Ioo (-N) N, g x * φ x) = ∫ x, g x * φ x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxs : x ∉ tsupport φ := fun h => hx (hφs h)
    rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero]
  rw [hsub, hdz, sub_zero, hL, hR] at hIBP'
  exact hIBP'

/-- `L²` on a bounded interval: the clamped profile is bounded and continuous. -/
theorem memLp_two_trialACProfile (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) (a b : ℝ) :
    MemLp (trialACProfile xm W) 2 (volume.restrict (Ioo a b)) := by
  obtain ⟨C, _, hC⟩ := exists_bound_trialACProfile (xm := xm) hℓ W
  haveI : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  refine MemLp.of_bound (continuous_trialACProfile hℓ W).aestronglyMeasurable C ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hC x

theorem trialACProfileDeriv_of_le (W : Sobolev.H1 ℓ) {x : ℝ} (hx : x ≤ xm) :
    trialACProfileDeriv xm W x = 0 :=
  Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.2 hx)) _

theorem trialACProfileDeriv_of_ge (W : Sobolev.H1 ℓ) {x : ℝ} (hx : xm + ℓ ≤ x) :
    trialACProfileDeriv xm W x = 0 :=
  Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.2 hx)) _

theorem trialACProfileDeriv_of_mem (W : Sobolev.H1 ℓ) {x : ℝ} (h1 : xm < x) (h2 : x < xm + ℓ) :
    trialACProfileDeriv xm W x = deriv W.toFun (x - xm) :=
  Set.indicator_of_mem (show x ∈ Ioo xm (xm + ℓ) from ⟨h1, h2⟩) _

/-- The translated `L²` norm of the axial factor. -/
theorem setIntegral_trialACProfile_sq (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) :
    (∫ x in Ioo xm (xm + ℓ), W.toFun (x - xm) ^ 2) = Sobolev.mass ℓ W := by
  have h1 : (∫ x in Ioo xm (xm + ℓ), W.toFun (x - xm) ^ 2)
      = ∫ x in xm..(xm + ℓ), W.toFun (x - xm) ^ 2 :=
    (Sobolev.intervalIntegral_eq_setIntegral_Ioo (by linarith)).symm
  rw [h1, intervalIntegral.integral_comp_sub_right (fun s => W.toFun s ^ 2) xm, sub_self,
    add_sub_cancel_left]
  rfl

/-- The translated `L²` norm of the derivative of the axial factor. -/
theorem setIntegral_trialACProfileDeriv_sq (hℓ : 0 ≤ ℓ) (W : Sobolev.H1 ℓ) :
    (∫ x in Ioo xm (xm + ℓ), deriv W.toFun (x - xm) ^ 2) = Sobolev.dirichlet ℓ W := by
  have h1 : (∫ x in Ioo xm (xm + ℓ), deriv W.toFun (x - xm) ^ 2)
      = ∫ x in xm..(xm + ℓ), deriv W.toFun (x - xm) ^ 2 :=
    (Sobolev.intervalIntegral_eq_setIntegral_Ioo (by linarith)).symm
  rw [h1, intervalIntegral.integral_comp_sub_right (fun s => deriv W.toFun s ^ 2) xm, sub_self,
    add_sub_cancel_left]
  rfl

end Profile

/-! ## 2. The trial extension on the thin domain -/

section Trial

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- `ℓ_R > 0` on the admissible range. -/
theorem trialAC_bulkLength_pos (hL : (Cm.K + Cp.K) * R < L) : 0 < bulkLength Cm Cp L R := by
  simp only [Domain.bulkLength]
  linarith

/-- `x₋ + ℓ_R = x₊`: the clamping interval of the trial extension is exactly the bulk
interval. -/
theorem trialAC_interface_add :
    (-L/2 + Cm.K * R) + bulkLength Cm Cp L R = L/2 - Cp.K * R := by
  simp only [Domain.bulkLength]
  ring

/-- **The trial extension `𝒯_R W` of `eq:trial-extension`**, for an axial factor which is only
absolutely continuous. -/
def trialACFun (Cm Cp : RobinCaps.Cap m) (L R : ℝ)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) (p : CapSpace m) : ℝ :=
  trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2

/-- The axial weak derivative of the trial extension. -/
def trialACGx (Cm Cp : RobinCaps.Cap m) (L R : ℝ)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) (p : CapSpace m) : ℝ :=
  trialACProfileDeriv (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2

/-- The transverse weak gradient of the trial extension. -/
def trialACGz (Cm Cp : RobinCaps.Cap m) (L R : ℝ)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) (p : CapSpace m) :
    EuclideanSpace ℝ (Fin m) :=
  trialACProfile (-L/2 + Cm.K * R) W p.1 • ψ.grad p.2

/-- The thin domain sits inside the product `(-L/2, L/2) × B_m(R)`. -/
theorem thinDomain_subset_prodBall (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    thinDomain Cm Cp L R ⊆ Ioo (-L/2) (L/2) ×ˢ transverseBall m R := by
  intro p hp
  have hzR := mem_thinDomain_norm_lt hR hL hp
  exact ⟨⟨hp.1, hp.2.1⟩, mem_ball_zero_iff.2 hzR⟩

variable (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)

theorem memLp_trialACFun (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    MemLp (trialACFun Cm Cp L R W ψ) 2 (volume.restrict (thinDomain Cm Cp L R)) := by
  have h : MemLp (fun p : CapSpace m =>
      trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) 2
      (volume.restrict (Ioo (-L/2) (L/2) ×ˢ transverseBall m R)) :=
    memLp_two_prodMul
      (memLp_two_trialACProfile (trialAC_bulkLength_pos hL).le W (-L/2) (L/2)) ψ.memL2
  exact h.mono_measure (Measure.restrict_mono (thinDomain_subset_prodBall hR hL) le_rfl)

theorem memLp_trialACGx (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    MemLp (trialACGx Cm Cp L R W ψ) 2 (volume.restrict (thinDomain Cm Cp L R)) := by
  have h : MemLp (fun p : CapSpace m =>
      trialACProfileDeriv (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) 2
      (volume.restrict (Ioo (-L/2) (L/2) ×ˢ transverseBall m R)) :=
    memLp_two_prodMul
      ((memLp_two_trialACProfileDeriv (trialAC_bulkLength_pos hL).le W).restrict _) ψ.memL2
  exact h.mono_measure (Measure.restrict_mono (thinDomain_subset_prodBall hR hL) le_rfl)

theorem memLp_trialACGz (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    MemLp (trialACGz Cm Cp L R W ψ) 2 (volume.restrict (thinDomain Cm Cp L R)) := by
  have h : MemLp (fun p : CapSpace m =>
      trialACProfile (-L/2 + Cm.K * R) W p.1 • ψ.grad p.2) 2
      (volume.restrict (Ioo (-L/2) (L/2) ×ˢ transverseBall m R)) :=
    memLp_two_prodSmul
      (memLp_two_trialACProfile (trialAC_bulkLength_pos hL).le W (-L/2) (L/2)) ψ.grad_memL2
  exact h.mono_measure (Measure.restrict_mono (thinDomain_subset_prodBall hR hL) le_rfl)

set_option maxHeartbeats 1600000 in
/-- **The weak gradient of the trial extension on the thin domain.**

The axial half is Fubini in the transverse variable followed by the one-dimensional weak
integration by parts `trialACProfile_integral_mul_deriv` on each line; the transverse half is
Fubini in the axial variable followed by the weak gradient of `ψ_R` on each slice (every slice
of the thin domain is contained in `B_m(R)`). -/
theorem hasWeakGradP_trialAC (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    HasWeakGradP (thinDomain Cm Cp L R) (trialACFun Cm Cp L R W ψ)
      (trialACGx Cm Cp L R W ψ) (trialACGz Cm Cp L R W ψ) := by
  have hℓ : (0 : ℝ) ≤ bulkLength Cm Cp L R := (trialAC_bulkLength_pos hL).le
  have hu2 := memLp_trialACFun W ψ hR hL
  have hgx2 := memLp_trialACGx W ψ hR hL
  have hgz2 := memLp_trialACGz W ψ hR hL
  intro φ hφ hφc hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hext : ∀ f : CapSpace m → ℝ, (∀ p, p ∉ tsupport φ → f p = 0) →
      (∫ p in thinDomain Cm Cp L R, f p) = ∫ p, f p := by
    intro f hf
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => hf p fun h => hp (hφs h)
  have hint : ∀ f : CapSpace m → ℝ, (∀ p, p ∉ tsupport φ → f p = 0) →
      IntegrableOn f (thinDomain Cm Cp L R) volume → Integrable f volume := by
    intro f hf hOn
    refine (integrableOn_iff_integrable_of_support_subset
      (s := thinDomain Cm Cp L R) ?_).1 hOn
    intro p hp
    by_contra hpΩ
    exact (Function.mem_support.1 hp) (hf p fun h => hpΩ (hφs h))
  have hφ0 : ∀ p : CapSpace m, p ∉ tsupport φ → fderiv ℝ φ p = 0 := fun p hp =>
    Function.notMem_support.1 fun h => hp (support_fderiv_subset ℝ h)
  constructor
  · -- ### the axial identity
    have hzL : ∀ p : CapSpace m, p ∉ tsupport φ →
        trialACFun Cm Cp L R W ψ p *
          fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) = 0 := by
      intro p hp; rw [hφ0 p hp]; simp
    have hzR : ∀ p : CapSpace m, p ∉ tsupport φ →
        trialACGx Cm Cp L R W ψ p * φ p = 0 := by
      intro p hp; rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
    have hIL : Integrable (fun p : CapSpace m => trialACFun Cm Cp L R W ψ p *
        fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))) volume :=
      hint _ hzL (integrable_mul_dirDeriv hu2 hφ hφc _)
    have hIR : Integrable (fun p : CapSpace m =>
        trialACGx Cm Cp L R W ψ p * φ p) volume :=
      hint _ hzR (integrable_gx_mul hgx2 hφ hφc)
    have hkey : ∀ z : EuclideanSpace ℝ (Fin m),
        (∫ x, trialACFun Cm Cp L R W ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = - ∫ x, trialACGx Cm Cp L R W ψ (x, z) * φ (x, z) := by
      intro z
      have hφz : ContDiff ℝ ∞ fun t : ℝ => φ (t, z) :=
        hφ.comp (contDiff_id.prodMk contDiff_const)
      have hφzc : HasCompactSupport fun t : ℝ => φ (t, z) := hasCompactSupport_sliceFst hφc z
      have h1 : (∫ x, trialACFun Cm Cp L R W ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
          = ψ.toFun z * ∫ x, trialACProfile (-L/2 + Cm.K * R) W x *
              deriv (fun t : ℝ => φ (t, z)) x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [trialACFun, deriv_sliceFst hφ1]
        ring
      have h2 : (∫ x, trialACGx Cm Cp L R W ψ (x, z) * φ (x, z))
          = ψ.toFun z * ∫ x, trialACProfileDeriv (-L/2 + Cm.K * R) W x * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [trialACGx]
        ring
      rw [h1, h2, trialACProfile_integral_mul_deriv hℓ W hφz hφzc]
      ring
    rw [hext _ hzL, hext _ hzR]
    have hprod : (volume : Measure (CapSpace m))
        = (volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
      Measure.volume_eq_prod ℝ (EuclideanSpace ℝ (Fin m))
    calc (∫ p, trialACFun Cm Cp L R W ψ p *
            fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        = ∫ z, ∫ x, trialACFun Cm Cp L R W ψ (x, z) *
            fderiv ℝ φ (x, z) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
          rw [hprod]; exact integral_prod_symm _ (by rwa [← hprod])
      _ = ∫ z, -∫ x, trialACGx Cm Cp L R W ψ (x, z) * φ (x, z) :=
          integral_congr_ae (.of_forall hkey)
      _ = -∫ z, ∫ x, trialACGx Cm Cp L R W ψ (x, z) * φ (x, z) := integral_neg _
      _ = -∫ p, trialACGx Cm Cp L R W ψ p * φ p := by
          congr 1
          rw [hprod]; exact (integral_prod_symm _ (by rwa [← hprod])).symm
  · -- ### the transverse identities
    intro i
    have hzL : ∀ p : CapSpace m, p ∉ tsupport φ →
        trialACFun Cm Cp L R W ψ p *
          fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) = 0 := by
      intro p hp; rw [hφ0 p hp]; simp
    have hzR : ∀ p : CapSpace m, p ∉ tsupport φ →
        trialACGz Cm Cp L R W ψ p i * φ p = 0 := by
      intro p hp; rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
    have hIL : Integrable (fun p : CapSpace m => trialACFun Cm Cp L R W ψ p *
        fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))) volume :=
      hint _ hzL (integrable_mul_dirDeriv hu2 hφ hφc _)
    have hIR : Integrable (fun p : CapSpace m =>
        trialACGz Cm Cp L R W ψ p i * φ p) volume :=
      hint _ hzR (integrable_compP_mul hgz2 hφ hφc i)
    have hkey : ∀ x : ℝ,
        (∫ z, trialACFun Cm Cp L R W ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = - ∫ z, trialACGz Cm Cp L R W ψ (x, z) i * φ (x, z) := by
      intro x
      have hφx : ContDiff ℝ ∞ fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hφ.comp (contDiff_const.prodMk contDiff_id)
      have hφxc : HasCompactSupport fun w : EuclideanSpace ℝ (Fin m) => φ (x, w) :=
        hasCompactSupport_sliceSnd hφc x
      have hφxs : tsupport (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w))
          ⊆ transverseBall m R := by
        intro z hz
        have hz' : ((x, z) : CapSpace m) ∈ thinDomain Cm Cp L R :=
          hφs (tsupport_sliceSnd_subset φ x hz)
        have hzR := mem_thinDomain_norm_lt hR hL hz'
        exact mem_ball_zero_iff.2 hzR
      have hw := ψ.hasWeakGrad (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) hφx hφxc hφxs i
      have hLg : (∫ z in transverseBall m R, ψ.toFun z *
            fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
              (EuclideanSpace.single i 1))
          = ∫ z, ψ.toFun z * fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
              (EuclideanSpace.single i 1) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
        have h0 : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z = 0 :=
          Function.notMem_support.1 fun h => (fun hmem => hz (hφxs hmem))
            (support_fderiv_subset ℝ h)
        rw [h0]; simp
      have hRg : (∫ z in transverseBall m R, ψ.grad z i * φ (x, z))
          = ∫ z, ψ.grad z i * φ (x, z) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
        have hnot : z ∉ tsupport (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) :=
          fun h => hz (hφxs h)
        have h0 : φ (x, z) = 0 := by
          have h1 := image_eq_zero_of_notMem_tsupport hnot
          exact h1
        rw [h0, mul_zero]
      rw [hLg, hRg] at hw
      have h1 : (∫ z, trialACFun Cm Cp L R W ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
          = trialACProfile (-L/2 + Cm.K * R) W x *
              ∫ z, ψ.toFun z * fderiv ℝ (fun w : EuclideanSpace ℝ (Fin m) => φ (x, w)) z
                (EuclideanSpace.single i 1) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [trialACFun, fderiv_sliceSnd hφ1]
        ring
      have h2 : (∫ z, trialACGz Cm Cp L R W ψ (x, z) i * φ (x, z))
          = trialACProfile (-L/2 + Cm.K * R) W x * ∫ z, ψ.grad z i * φ (x, z) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [trialACGz, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [h1, h2, hw]
      ring
    rw [hext _ hzL, hext _ hzR]
    have hprod : (volume : Measure (CapSpace m))
        = (volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
      Measure.volume_eq_prod ℝ (EuclideanSpace ℝ (Fin m))
    calc (∫ p, trialACFun Cm Cp L R W ψ p *
            fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        = ∫ x, ∫ z, trialACFun Cm Cp L R W ψ (x, z) *
            fderiv ℝ φ (x, z) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
          rw [hprod]; exact integral_prod _ (by rwa [← hprod])
      _ = ∫ x, -∫ z, trialACGz Cm Cp L R W ψ (x, z) i * φ (x, z) :=
          integral_congr_ae (.of_forall hkey)
      _ = -∫ x, ∫ z, trialACGz Cm Cp L R W ψ (x, z) i * φ (x, z) := integral_neg _
      _ = -∫ p, trialACGz Cm Cp L R W ψ p i * φ p := by
          congr 1
          rw [hprod]; exact (integral_prod _ (by rwa [← hprod])).symm

end Trial

/-! ## 3. The bundled trial extension and the linear lift -/

section Lift

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- **The trial extension `𝒯_R W` of `eq:trial-extension` as an element of `H1P (Ω_R)`.** -/
def trialAC (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    H1P (thinDomain Cm Cp L R) where
  toFun := trialACFun Cm Cp L R W ψ
  gx := trialACGx Cm Cp L R W ψ
  gz := trialACGz Cm Cp L R W ψ
  memL2 := memLp_trialACFun W ψ hR hL
  gx_memL2 := memLp_trialACGx W ψ hR hL
  gz_memL2 := memLp_trialACGz W ψ hR hL
  hasWeakGrad := hasWeakGradP_trialAC W ψ hR hL

variable (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)

@[simp] theorem trialAC_toFun (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    (trialAC hR hL W ψ).toFun = trialACFun Cm Cp L R W ψ := rfl

@[simp] theorem trialAC_gx (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    (trialAC hR hL W ψ).gx = trialACGx Cm Cp L R W ψ := rfl

@[simp] theorem trialAC_gz (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    (trialAC hR hL W ψ).gz = trialACGz Cm Cp L R W ψ := rfl

/-- **Additivity of the trial extension in the axial factor**, at the level of the
representatives.  (Only the representative is additive: the *chosen* axial weak derivative
`deriv W` is additive merely almost everywhere, which is why the linear lift below has to take
values in the a.e. quotient `H1PQ`.) -/
theorem trialAC_add (W₁ W₂ : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    (trialAC hR hL (W₁ + W₂) ψ).toFun
      = (trialAC hR hL W₁ ψ).toFun + (trialAC hR hL W₂ ψ).toFun := by
  funext p
  show trialACProfile (-L/2 + Cm.K * R) (W₁ + W₂) p.1 * ψ.toFun p.2
      = trialACProfile (-L/2 + Cm.K * R) W₁ p.1 * ψ.toFun p.2
        + trialACProfile (-L/2 + Cm.K * R) W₂ p.1 * ψ.toFun p.2
  simp only [trialACProfile, Sobolev.H1.add_toFun, Pi.add_apply]
  ring

/-- **Homogeneity of the trial extension in the axial factor.** -/
theorem trialAC_smul (c : ℝ) (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R) :
    (trialAC hR hL (c • W) ψ).toFun = c • (trialAC hR hL W ψ).toFun := by
  funext p
  show trialACProfile (-L/2 + Cm.K * R) (c • W) p.1 * ψ.toFun p.2
      = c * (trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2)
  simp only [trialACProfile, Sobolev.H1.smul_toFun]
  ring

/-- Two elements of `H1P Ω` with the same representative have the same class. -/
theorem h1pq_mk_eq_of_toFun {Ω : Set (CapSpace m)} {u v : H1P Ω} (h : u.toFun = v.toFun) :
    (Submodule.Quotient.mk u : H1PQ Ω) = Submodule.Quotient.mk v := by
  refine H1PQ_eq_iff.2 ?_
  filter_upwards with p
  exact congrFun h p

/-- **The trial extension as a linear map into the a.e. quotient.** -/
def trialACₗ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (ψ : TransH1 m R) :
    Sobolev.H1 (bulkLength Cm Cp L R) →ₗ[ℝ] H1PQ (thinDomain Cm Cp L R) where
  toFun W := Submodule.Quotient.mk (trialAC hR hL W ψ)
  map_add' W₁ W₂ := by
    have hsum : (Submodule.Quotient.mk (trialAC hR hL W₁ ψ)
          + Submodule.Quotient.mk (trialAC hR hL W₂ ψ) : H1PQ (thinDomain Cm Cp L R))
        = Submodule.Quotient.mk (trialAC hR hL W₁ ψ + trialAC hR hL W₂ ψ) := rfl
    rw [hsum]
    exact h1pq_mk_eq_of_toFun (trialAC_add hR hL W₁ W₂ ψ)
  map_smul' c W := by
    have hsmul : (c • Submodule.Quotient.mk (trialAC hR hL W ψ) :
          H1PQ (thinDomain Cm Cp L R))
        = Submodule.Quotient.mk (c • trialAC hR hL W ψ) := rfl
    show Submodule.Quotient.mk (trialAC hR hL (c • W) ψ)
        = (RingHom.id ℝ) c • Submodule.Quotient.mk (trialAC hR hL W ψ)
    rw [RingHom.id_apply, hsmul]
    exact h1pq_mk_eq_of_toFun (trialAC_smul hR hL c W ψ)

@[simp] theorem trialACₗ_apply (ψ : TransH1 m R) (W : Sobolev.H1 (bulkLength Cm Cp L R)) :
    trialACₗ hR hL ψ W = Submodule.Quotient.mk (trialAC hR hL W ψ) := rfl

/-- **The trial extension `𝒯_R` as a linear lift `H¹(0,ℓ_R)/N →ₗ H¹(Ω_R)/N`.**

This is the `lift` field of `RobinCaps.ThinDomain.GlobalComparisonData`. -/
def liftQ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (ψ : TransH1 m R) :
    Sobolev.H1Q (bulkLength Cm Cp L R) →ₗ[ℝ] H1PQ (thinDomain Cm Cp L R) := by
  refine Submodule.liftQ _ (trialACₗ hR hL ψ) ?_
  intro W hW
  have hℓ : (0 : ℝ) ≤ bulkLength Cm Cp L R := (trialAC_bulkLength_pos hL).le
  have hW' : ∀ x ∈ Icc (0 : ℝ) (bulkLength Cm Cp L R), W.toFun x = 0 :=
    (Sobolev.mem_nullOff_of_nonneg hℓ).1 hW
  show Submodule.Quotient.mk (trialAC hR hL W ψ) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  show (trialAC hR hL W ψ).toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0
  filter_upwards with p
  show trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2 = 0
  rw [trialACProfile, hW' _ (axialClamp_mem_Icc hℓ _), zero_mul]

@[simp] theorem liftQ_mk (ψ : TransH1 m R) (W : Sobolev.H1 (bulkLength Cm Cp L R)) :
    liftQ hR hL ψ (Submodule.Quotient.mk W)
      = Submodule.Quotient.mk (trialAC hR hL W ψ) := rfl

end Lift

/-! ## 4. The bulk projection of the trial extension -/

section Transport

/-- Transport of the concrete one-dimensional model along an equality of lengths. -/
def h1Congr {ℓ ℓ' : ℝ} (e : ℓ = ℓ') : Sobolev.H1 ℓ ≃ₗ[ℝ] Sobolev.H1 ℓ' := by
  subst e; exact LinearEquiv.refl ℝ _

@[simp] theorem h1Congr_toFun {ℓ ℓ' : ℝ} (e : ℓ = ℓ') (W : Sobolev.H1 ℓ) :
    (h1Congr e W).toFun = W.toFun := by subst e; rfl

/-- Transport of the quotient one-dimensional model along an equality of lengths. -/
def h1QCongr {ℓ ℓ' : ℝ} (e : ℓ = ℓ') : Sobolev.H1Q ℓ ≃ₗ[ℝ] Sobolev.H1Q ℓ' := by
  subst e; exact LinearEquiv.refl ℝ _

@[simp] theorem h1QCongr_mk {ℓ ℓ' : ℝ} (e : ℓ = ℓ') (W : Sobolev.H1 ℓ) :
    h1QCongr e (Submodule.Quotient.mk W)
      = (Submodule.Quotient.mk (h1Congr e W) : Sobolev.H1Q ℓ') := by
  subst e; rfl

/-- The transport hidden in the definition of `RobinCaps.ThinDomain.bulkProjThin`. -/
theorem eqMpr_linearMap {A : Type*} [AddCommGroup A] [Module ℝ A] {ℓ ℓ' : ℝ} (e : ℓ = ℓ')
    (G : A →ₗ[ℝ] Sobolev.H1Q ℓ') :
    (Eq.mpr (id (congrArg (fun b : ℝ => A →ₗ[ℝ] Sobolev.H1Q b) e)) G :
        A →ₗ[ℝ] Sobolev.H1Q ℓ)
      = (h1QCongr e).symm.toLinearMap.comp G := by
  subst e; rfl

end Transport

/-! ### The bulk projection of the trial extension -/

section Proj

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}
variable (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
variable (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)

/-- **On the bulk cylinder the trial extension is the plain tensor `W(· - x₋) ⊗ ψ_R`.** -/
theorem restrictBulkP_trialAC_toFun {p : CapSpace m}
    (hp : p ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R) :
    (restrictBulkP hR (trialAC hR hL W ψ)).toFun p
      = W.toFun (p.1 - (-L/2 + Cm.K * R)) * ψ.toFun p.2 := by
  have h1 : (-L/2 + Cm.K * R) ≤ p.1 := hp.1.1.le
  have h2 : p.1 ≤ (-L/2 + Cm.K * R) + bulkLength Cm Cp L R := by
    rw [trialAC_interface_add]; exact hp.1.2.le
  show trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2
      = W.toFun (p.1 - (-L/2 + Cm.K * R)) * ψ.toFun p.2
  rw [trialACProfile_of_mem W h1 h2]

/-- **The axial coefficient of the trial extension is the translated axial factor.** -/
theorem axialCoeff_trialAC (hψ1 : ∫ z in transverseBall m R, ψ.toFun z ^ 2 = 1)
    {x : ℝ} (hx : x ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R)) :
    axialCoeff (transverseBall m R) (restrictBulkP hR (trialAC hR hL W ψ)).toFun ψ.toFun x
      = W.toFun (x - (-L/2 + Cm.K * R)) := by
  have h : (∫ z in transverseBall m R,
        (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z) * ψ.toFun z)
      = ∫ z in transverseBall m R, W.toFun (x - (-L/2 + Cm.K * R)) * ψ.toFun z ^ 2 := by
    refine setIntegral_congr_fun isOpen_transverseBall.measurableSet fun z hz => ?_
    rw [restrictBulkP_trialAC_toFun hR hL W ψ (p := (x, z)) ⟨hx, hz⟩]
    ring
  show (∫ z in transverseBall m R,
      (restrictBulkP hR (trialAC hR hL W ψ)).toFun (x, z) * ψ.toFun z) = _
  rw [h, integral_const_mul, hψ1, mul_one]

/-- **The one-dimensional representative of the bulk projection of the trial extension is the
axial factor itself.** -/
theorem bulkRepT_trialAC (hψ1 : ∫ z in transverseBall m R, ψ.toFun z ^ 2 = 1) :
    (Submodule.Quotient.mk (bulkRepT (Domain.interface_lt hR hL) isOpen_transverseBall
        volume_transverseBall_ne_top ψ.memL2 hψ1 (restrictBulkP hR (trialAC hR hL W ψ)))
      : Sobolev.H1Q (L/2 - Cp.K * R - (-L/2 + Cm.K * R)))
      = Submodule.Quotient.mk (h1Congr bulkLength_eq_sub W) := by
  have hab : (-L/2 + Cm.K * R) < L/2 - Cp.K * R := Domain.interface_lt hR hL
  refine h1Q_mk_eq_of_eqOn (by linarith) (repT_eqOn_of_ae hab ?_)
  filter_upwards [bulkRepT_ae hab isOpen_transverseBall volume_transverseBall_ne_top
      ψ.memL2 hψ1 (restrictBulkP hR (trialAC hR hL W ψ)),
    self_mem_ae_restrict (measurableSet_Ioo (a := -L/2 + Cm.K * R) (b := L/2 - Cp.K * R))]
    with x hx hxmem
  show (bulkRepT hab isOpen_transverseBall volume_transverseBall_ne_top ψ.memL2 hψ1
        (restrictBulkP hR (trialAC hR hL W ψ))).toFun (x - (-L/2 + Cm.K * R))
      = (h1Congr bulkLength_eq_sub W).toFun (x - (-L/2 + Cm.K * R))
  rw [hx, axialCoeff_trialAC hR hL W ψ hψ1 hxmem, h1Congr_toFun]

/-- The transport hidden in `RobinCaps.ThinDomain.bulkProjThin`, made explicit. -/
theorem bulkProjThin_eq {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (transverseBall m R)))
    (hψ1 : ∫ z in transverseBall m R, ψ z ^ 2 = 1) :
    bulkProjThin hR hL hψ hψ1
      = (h1QCongr (bulkLength_eq_sub (Cm := Cm) (Cp := Cp)
            (L := L) (R := R))).symm.toLinearMap.comp
          ((bulkProjT (Domain.interface_lt hR hL) isOpen_transverseBall
            volume_transverseBall_ne_top hψ hψ1).comp (restrictBulkPQ hR)) :=
  eqMpr_linearMap _ _

/-- **The bulk projection undoes the trial extension** (`eq:trial-extension`): with a normalised
transverse profile, `π (𝒯_R F) = F`. -/
theorem bulkProjThin_liftQ (hψ1 : ∫ z in transverseBall m R, ψ.toFun z ^ 2 = 1)
    (w : Sobolev.H1Q (bulkLength Cm Cp L R)) :
    bulkProjThin hR hL ψ.memL2 hψ1 (liftQ hR hL ψ w) = w := by
  obtain ⟨V, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) w
  rw [bulkProjThin_eq hR hL ψ.memL2 hψ1]
  simp only [LinearMap.comp_apply, liftQ_mk, restrictBulkPQ_mk, bulkProjT_mk,
    LinearEquiv.coe_coe]
  rw [bulkRepT_trialAC hR hL V ψ hψ1, ← h1QCongr_mk]
  exact (h1QCongr _).symm_apply_apply _

/-- **Surjectivity of the bulk projection from the thin domain** — the target
`RobinCaps.ThinDomain.BulkProjThinSurjective` of `RobinCaps/ThinDomain/BulkProj.lean`. -/
theorem bulkProjThin_surjective_trialAC
    (hψ1 : ∫ z in transverseBall m R, ψ.toFun z ^ 2 = 1) :
    BulkProjThinSurjective hR hL ψ.memL2 hψ1 :=
  fun w => ⟨liftQ hR hL ψ w, bulkProjThin_liftQ hR hL ψ hψ1 w⟩

end Proj

/-! ## 5. The exact mass and energy splittings, and `eq:trial-mass` -/

section Forms

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}
variable (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
variable (W : Sobolev.H1 (bulkLength Cm Cp L R)) (ψ : TransH1 m R)

/-- **The mass of the trial extension splits exactly** into the two cap masses and the bulk
mass `M[F] · N_B[ψ_R]`. -/
theorem massP_trialAC :
    massP (trialAC hR hL W ψ)
      = (∫ p in leftCap Cm L R, (W.toFun 0 * ψ.toFun p.2) ^ 2)
        + Sobolev.mass (bulkLength Cm Cp L R) W * NB ψ
        + ∫ p in rightCap Cp L R, (W.toFun (bulkLength Cm Cp L R) * ψ.toFun p.2) ^ 2 := by
  have hab : (-L/2 + Cm.K * R) < L/2 - Cp.K * R := Domain.interface_lt hR hL
  have hℓ : (0 : ℝ) ≤ bulkLength Cm Cp L R := (trialAC_bulkLength_pos hL).le
  have hInt : IntegrableOn (fun p => trialACFun Cm Cp L R W ψ p ^ 2)
      (thinDomain Cm Cp L R) := (trialAC hR hL W ψ).memL2.integrable_sq
  have hsplit := setIntegral_thinDomain_split hR hL hInt
  have hleft : (∫ p in leftCap Cm L R, trialACFun Cm Cp L R W ψ p ^ 2)
      = ∫ p in leftCap Cm L R, (W.toFun 0 * ψ.toFun p.2) ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_leftCap' hR) fun p hp => ?_
    show (trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) ^ 2 = _
    rw [trialACProfile_of_le hℓ W (leftCap_fst_lt hR hp).le]
  have hright : (∫ p in rightCap Cp L R, trialACFun Cm Cp L R W ψ p ^ 2)
      = ∫ p in rightCap Cp L R, (W.toFun (bulkLength Cm Cp L R) * ψ.toFun p.2) ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_rightCap' hR) fun p hp => ?_
    have hge : (-L/2 + Cm.K * R) + bulkLength Cm Cp L R ≤ p.1 := by
      rw [trialAC_interface_add]; exact (rightCap_lt_fst hR hp).le
    show (trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) ^ 2 = _
    rw [trialACProfile_of_ge hℓ W hge]
  have hbulk : (∫ p in bulkCylinder Cm Cp L R, trialACFun Cm Cp L R W ψ p ^ 2)
      = Sobolev.mass (bulkLength Cm Cp L R) W * NB ψ := by
    rw [setIntegral_bulkCylinder]
    have h : (∫ p in bulkCyl (-L/2 + Cm.K * R) (L/2 - Cp.K * R) m R,
          trialACFun Cm Cp L R W ψ p ^ 2)
        = ∫ p in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R,
            W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ψ.toFun p.2 ^ 2 := by
      refine setIntegral_congr_fun isOpen_bulkCyl.measurableSet fun p hp => ?_
      have h2 : p.1 ≤ (-L/2 + Cm.K * R) + bulkLength Cm Cp L R := by
        rw [trialAC_interface_add]; exact hp.1.2.le
      show (trialACProfile (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) ^ 2 = _
      rw [trialACProfile_of_mem W hp.1.1.le h2]
      ring
    have hpm : (∫ p in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R,
          W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ψ.toFun p.2 ^ 2)
        = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
              W.toFun (x - (-L/2 + Cm.K * R)) ^ 2)
          * ∫ z in transverseBall m R, ψ.toFun z ^ 2 :=
      setIntegral_prod_mul (fun x : ℝ => W.toFun (x - (-L/2 + Cm.K * R)) ^ 2)
        (fun z : EuclideanSpace ℝ (Fin m) => ψ.toFun z ^ 2) _ _
    rw [h, hpm]
    congr 1
    rw [← trialAC_interface_add (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
    exact setIntegral_trialACProfile_sq hℓ W
  show (∫ p in thinDomain Cm Cp L R, trialACFun Cm Cp L R W ψ p ^ 2) = _
  rw [hsplit, hleft, hright, hbulk]

/-- **The Dirichlet energy of the trial extension splits exactly.** -/
theorem dirichletP_trialAC :
    dirichletP (trialAC hR hL W ψ)
      = (∫ p in leftCap Cm L R, ‖W.toFun 0 • ψ.grad p.2‖ ^ 2)
        + (Sobolev.dirichlet (bulkLength Cm Cp L R) W * NB ψ
            + Sobolev.mass (bulkLength Cm Cp L R) W * Sobolev.Weak.dirichlet ψ)
        + ∫ p in rightCap Cp L R, ‖W.toFun (bulkLength Cm Cp L R) • ψ.grad p.2‖ ^ 2 := by
  have hab : (-L/2 + Cm.K * R) < L/2 - Cp.K * R := Domain.interface_lt hR hL
  have hℓ : (0 : ℝ) ≤ bulkLength Cm Cp L R := (trialAC_bulkLength_pos hL).le
  set u := trialAC hR hL W ψ with hu
  have hI1 : Integrable (fun p => u.gx p ^ 2) (volume.restrict (thinDomain Cm Cp L R)) :=
    u.gx_memL2.integrable_sq
  have hI2 : Integrable (fun p => ‖u.gz p‖ ^ 2) (volume.restrict (thinDomain Cm Cp L R)) :=
    (memLp_two_iff_integrable_sq_norm u.gz_memL2.aestronglyMeasurable).1 u.gz_memL2
  have hInt : IntegrableOn (fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2) (thinDomain Cm Cp L R) :=
    hI1.add hI2
  have hsplit := setIntegral_thinDomain_split hR hL hInt
  have hleft : (∫ p in leftCap Cm L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2))
      = ∫ p in leftCap Cm L R, ‖W.toFun 0 • ψ.grad p.2‖ ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_leftCap' hR) fun p hp => ?_
    have hlt : p.1 ≤ (-L/2 + Cm.K * R) := (leftCap_fst_lt hR hp).le
    show (trialACProfileDeriv (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) ^ 2
        + ‖trialACProfile (-L/2 + Cm.K * R) W p.1 • ψ.grad p.2‖ ^ 2 = _
    rw [trialACProfileDeriv_of_le W hlt, trialACProfile_of_le hℓ W hlt, zero_mul]
    ring
  have hright : (∫ p in rightCap Cp L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2))
      = ∫ p in rightCap Cp L R, ‖W.toFun (bulkLength Cm Cp L R) • ψ.grad p.2‖ ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_rightCap' hR) fun p hp => ?_
    have hge : (-L/2 + Cm.K * R) + bulkLength Cm Cp L R ≤ p.1 := by
      rw [trialAC_interface_add]; exact (rightCap_lt_fst hR hp).le
    show (trialACProfileDeriv (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) ^ 2
        + ‖trialACProfile (-L/2 + Cm.K * R) W p.1 • ψ.grad p.2‖ ^ 2 = _
    rw [trialACProfileDeriv_of_ge W hge, trialACProfile_of_ge hℓ W hge, zero_mul]
    ring
  have hbulk : (∫ p in bulkCylinder Cm Cp L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2))
      = Sobolev.dirichlet (bulkLength Cm Cp L R) W * NB ψ
        + Sobolev.mass (bulkLength Cm Cp L R) W * Sobolev.Weak.dirichlet ψ := by
    rw [setIntegral_bulkCylinder]
    have hsub : Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R
        ⊆ thinDomain Cm Cp L R := bulkCyl_subset_thinDomain hR
    have hcongr : ∀ p ∈ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R,
        u.gx p ^ 2 + ‖u.gz p‖ ^ 2
          = deriv W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ψ.toFun p.2 ^ 2
            + W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ‖ψ.grad p.2‖ ^ 2 := by
      intro p hp
      have h2 : p.1 < (-L/2 + Cm.K * R) + bulkLength Cm Cp L R := by
        rw [trialAC_interface_add]; exact hp.1.2
      show (trialACProfileDeriv (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) ^ 2
          + ‖trialACProfile (-L/2 + Cm.K * R) W p.1 • ψ.grad p.2‖ ^ 2 = _
      rw [trialACProfileDeriv_of_mem W hp.1.1 h2, trialACProfile_of_mem W hp.1.1.le h2.le,
        norm_smul, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
    have hA : IntegrableOn (fun p : CapSpace m =>
        deriv W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ψ.toFun p.2 ^ 2)
        (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R) := by
      refine IntegrableOn.congr_fun (IntegrableOn.mono_set hI1 hsub) (fun p hp => ?_)
        (isOpen_bulkCyl.measurableSet)
      have h2 : p.1 < (-L/2 + Cm.K * R) + bulkLength Cm Cp L R := by
        rw [trialAC_interface_add]; exact hp.1.2
      show (trialACProfileDeriv (-L/2 + Cm.K * R) W p.1 * ψ.toFun p.2) ^ 2 = _
      rw [trialACProfileDeriv_of_mem W hp.1.1 h2, mul_pow]
    have hB : IntegrableOn (fun p : CapSpace m =>
        W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ‖ψ.grad p.2‖ ^ 2)
        (Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R) := by
      refine IntegrableOn.congr_fun (IntegrableOn.mono_set hI2 hsub) (fun p hp => ?_)
        (isOpen_bulkCyl.measurableSet)
      have h2 : p.1 < (-L/2 + Cm.K * R) + bulkLength Cm Cp L R := by
        rw [trialAC_interface_add]; exact hp.1.2
      show ‖trialACProfile (-L/2 + Cm.K * R) W p.1 • ψ.grad p.2‖ ^ 2 = _
      rw [trialACProfile_of_mem W hp.1.1.le h2.le, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hstep : (∫ p in bulkCyl (-L/2 + Cm.K * R) (L/2 - Cp.K * R) m R,
          (u.gx p ^ 2 + ‖u.gz p‖ ^ 2))
        = (∫ p in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R,
              deriv W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ψ.toFun p.2 ^ 2)
          + ∫ p in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R,
              W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ‖ψ.grad p.2‖ ^ 2 := by
      rw [← integral_add hA hB]
      exact setIntegral_congr_fun isOpen_bulkCyl.measurableSet hcongr
    have hpm1 : (∫ p in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R,
          deriv W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ψ.toFun p.2 ^ 2)
        = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
              deriv W.toFun (x - (-L/2 + Cm.K * R)) ^ 2)
          * ∫ z in transverseBall m R, ψ.toFun z ^ 2 :=
      setIntegral_prod_mul (fun x : ℝ => deriv W.toFun (x - (-L/2 + Cm.K * R)) ^ 2)
        (fun z : EuclideanSpace ℝ (Fin m) => ψ.toFun z ^ 2) _ _
    have hpm2 : (∫ p in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) ×ˢ transverseBall m R,
          W.toFun (p.1 - (-L/2 + Cm.K * R)) ^ 2 * ‖ψ.grad p.2‖ ^ 2)
        = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R),
              W.toFun (x - (-L/2 + Cm.K * R)) ^ 2)
          * ∫ z in transverseBall m R, ‖ψ.grad z‖ ^ 2 :=
      setIntegral_prod_mul (fun x : ℝ => W.toFun (x - (-L/2 + Cm.K * R)) ^ 2)
        (fun z : EuclideanSpace ℝ (Fin m) => ‖ψ.grad z‖ ^ 2) _ _
    rw [hstep, hpm1, hpm2]
    congr 1
    · congr 1
      rw [← trialAC_interface_add (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
      exact setIntegral_trialACProfileDeriv_sq hℓ W
    · congr 1
      rw [← trialAC_interface_add (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
      exact setIntegral_trialACProfile_sq hℓ W
  show (∫ p in thinDomain Cm Cp L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2)) = _
  rw [hsplit, hleft, hright, hbulk]

/-- **`eq:trial-mass` (left half)**: with a normalised transverse profile the mass of the trial
extension dominates the interval mass of the axial factor (the two cap contributions are
nonnegative). -/
theorem mass_le_massP_trialAC (hNB : NB ψ = 1) :
    Sobolev.mass (bulkLength Cm Cp L R) W ≤ massP (trialAC hR hL W ψ) := by
  have hcapL : 0 ≤ ∫ p in leftCap Cm L R, (W.toFun 0 * ψ.toFun p.2) ^ 2 :=
    setIntegral_nonneg (measurableSet_leftCap' hR) fun p _ => sq_nonneg _
  have hcapR : 0 ≤ ∫ p in rightCap Cp L R,
      (W.toFun (bulkLength Cm Cp L R) * ψ.toFun p.2) ^ 2 :=
    setIntegral_nonneg (measurableSet_rightCap' hR) fun p _ => sq_nonneg _
  rw [massP_trialAC hR hL W ψ, hNB, mul_one]
  linarith

/-- **`eq:trial-mass` on the quotients**: this is the `trial_mass` field of
`RobinCaps.ThinDomain.GlobalComparisonData`. -/
theorem massQ_le_massPQ_liftQ (hNB : NB ψ = 1)
    (w : Sobolev.H1Q (bulkLength Cm Cp L R)) :
    Sobolev.massQ (bulkLength Cm Cp L R) w ≤ massPQ (liftQ hR hL ψ w) := by
  obtain ⟨V, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) w
  rw [Sobolev.massQ_mk, liftQ_mk, massPQ_mk]
  exact mass_le_massP_trialAC hR hL V ψ hNB

end Forms

end

end RobinCaps.ThinDomain
