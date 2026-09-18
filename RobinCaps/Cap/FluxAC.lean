import Mathlib
import RobinCaps.Cap.Regular
import RobinCaps.Cap.SharpInequality
import RobinCaps.Cap.SharpComplete
import RobinCaps.Cap.Sphere

/-!
# The flux identity and the sharp cap inequality under weak regularity

This file generalises the one-dimensional FTC machinery of
`RobinCaps/Cap/SharpInequality.lean` from the (too strong) predicate
`ProfileRegular` — a *continuous derivative on the closed interval* — to the
weak predicate `ProfileAC` of `RobinCaps/Cap/Regular.lean`:

* continuity of `θ` on `[-K,0]`, entrance value `θ(-K) = 1`,
* differentiability on `(-K,0)` off a countable set,
* interval integrability of the area element `θ^{m-1}√(1+θ'²)`.

The hemisphere satisfies `ProfileAC` (indeed `ProfileC1`) although its
derivative blows up at the terminal point, so the results below cover the
equality case of the manuscript's `thm:calibration`.

The fundamental theorem of calculus used is
`MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`.  All integrands
are shown integrable by **domination by the area element**: on `(-K,0)`,
`|θ'| ≤ √(1+θ'²)`, `1 ≤ √(1+θ'²)`, `0 ≤ slog ≤ 1`, `0 < θ ≤ 1`.

## Main results

* `fluxIdentity_of_profileAC` — the flux identity;
* `lateralFlux_le_lateralArea_of_profileAC`, `terminalFlux_le_terminalArea_of_profileAC`;
* `sharp_revolutionF_of_profileAC` — `𝓕(C) ≥ ω_{m+1}/2` for every `ProfileAC` cap;
* `defectIdentity_of_profileAC` — the defect identity;
* `hemisphere_profileC1`, `flat_profileC1`, `truncatedSemi_profileC1` — instances;
* `revolutionF_ge_of_profileC1` — the sharp inequality for `ProfileC1` caps.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps
namespace Cap

noncomputable section

variable {m : ℕ}

/-! ## Elementary bounds -/

theorem abs_le_sqrt_one_add_sq (x : ℝ) : |x| ≤ Real.sqrt (1 + x ^ 2) :=
  Real.abs_le_sqrt (by nlinarith)

theorem one_le_sqrt_one_add_sq (x : ℝ) : 1 ≤ Real.sqrt (1 + x ^ 2) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [sq_nonneg x]

/-- The lateral-flux integrand is dominated in absolute value by
`(1 + |t|)` times the area element, on the open interval. -/
theorem abs_lateralFlux_integrand_le_of_profileAC (C : Cap m) (t : ℝ) {s : ℝ}
    (hs : s ∈ Ioo (-C.K) 0) :
    |(C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)|
      ≤ (1 + |t|) * ((C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2)) := by
  have hθpos : 0 < C.θ s := C.θ_pos s hs
  have hθle : C.θ s ≤ 1 := C.θ_le_one s hs
  have hp : 0 ≤ (C.θ s) ^ (m - 1) := pow_nonneg hθpos.le _
  have h1 : |deriv C.θ s| ≤ Real.sqrt (1 + (deriv C.θ s) ^ 2) := abs_le_sqrt_one_add_sq _
  have h2 : 1 ≤ Real.sqrt (1 + (deriv C.θ s) ^ 2) := one_le_sqrt_one_add_sq _
  have hσ0 : 0 ≤ slog t (C.θ s) := slog_nonneg _ _
  have hσ1 : slog t (C.θ s) ≤ 1 := slog_le_one _ _
  have hinner : |-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s|
      ≤ (1 + |t|) * Real.sqrt (1 + (deriv C.θ s) ^ 2) := by
    calc |-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s|
        ≤ |-(deriv C.θ s) * slog t (C.θ s)| + |t * C.θ s| := abs_add_le _ _
      _ = |deriv C.θ s| * slog t (C.θ s) + |t| * C.θ s := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hσ0, abs_of_nonneg hθpos.le]
      _ ≤ Real.sqrt (1 + (deriv C.θ s) ^ 2) * 1 + |t| * 1 :=
          add_le_add (mul_le_mul h1 hσ1 hσ0 (Real.sqrt_nonneg _))
            (mul_le_mul_of_nonneg_left hθle (abs_nonneg t))
      _ ≤ (1 + |t|) * Real.sqrt (1 + (deriv C.θ s) ^ 2) := by
          nlinarith [abs_nonneg t, h2]
  rw [abs_mul, abs_of_nonneg hp]
  calc (C.θ s) ^ (m - 1) * |-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s|
      ≤ (C.θ s) ^ (m - 1) * ((1 + |t|) * Real.sqrt (1 + (deriv C.θ s) ^ 2)) :=
        mul_le_mul_of_nonneg_left hinner hp
    _ = (1 + |t|) * ((C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2)) := by ring

/-- The chain-rule integrand `θ^{m-1} slog(θ) θ'` is dominated by the area element. -/
theorem abs_chain_integrand_le_of_profileAC (C : Cap m) (t : ℝ) {s : ℝ}
    (hs : s ∈ Ioo (-C.K) 0) :
    |(C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s|
      ≤ 1 * ((C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2)) := by
  have hθpos : 0 < C.θ s := C.θ_pos s hs
  have hp : 0 ≤ (C.θ s) ^ (m - 1) := pow_nonneg hθpos.le _
  have h1 : |deriv C.θ s| ≤ Real.sqrt (1 + (deriv C.θ s) ^ 2) := abs_le_sqrt_one_add_sq _
  have hσ0 : 0 ≤ slog t (C.θ s) := slog_nonneg _ _
  have hσ1 : slog t (C.θ s) ≤ 1 := slog_le_one _ _
  rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hσ0, one_mul]
  calc (C.θ s) ^ (m - 1) * slog t (C.θ s) * |deriv C.θ s|
      ≤ (C.θ s) ^ (m - 1) * 1 * Real.sqrt (1 + (deriv C.θ s) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hσ1 hp) h1 (abs_nonneg _)
          (mul_nonneg hp zero_le_one)
    _ = (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2) := by ring

/-! ## Measurability and domination -/

theorem ProfileAC.aestronglyMeasurable_theta {C : Cap m} (h : ProfileAC C) :
    AEStronglyMeasurable C.θ (volume.restrict (Ioc (-C.K) 0)) :=
  (h.continuousOn.aestronglyMeasurable measurableSet_Icc).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-- **Domination principle.**  A function on `(-K,0)` which is measurable on the
half-open interval and dominated pointwise on the open interval by a constant
multiple of the area element is interval integrable. -/
theorem intervalIntegrable_of_le_areaElement_of_profileAC {C : Cap m} (h : ProfileAC C)
    (f : ℝ → ℝ) (hfm : AEStronglyMeasurable f (volume.restrict (Ioc (-C.K) 0))) (c : ℝ)
    (hle : ∀ s ∈ Ioo (-C.K) 0,
      |f s| ≤ c * ((C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))) :
    IntervalIntegrable f volume (-C.K) 0 := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hA := h.areaElement_intervalIntegrable.const_mul c
  refine hA.mono_fun' ?_ ?_
  · rw [Set.uIoc_of_le hKle]; exact hfm
  · rw [Set.uIoc_of_le hKle]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_lt_of_ae_restrict_Ioc (a := -C.K) (b := 0)] with x hx hx0
    rw [Real.norm_eq_abs]
    exact hle x ⟨hx.1, hx0⟩

/-- Integrability of the lateral-flux integrand under `ProfileAC`. -/
theorem lateralFlux_integrand_intervalIntegrable_of_profileAC {C : Cap m} (h : ProfileAC C)
    (t : ℝ) :
    IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s))
      volume (-C.K) 0 := by
  have hθm := h.aestronglyMeasurable_theta
  have hdm : AEStronglyMeasurable (deriv C.θ) (volume.restrict (Ioc (-C.K) 0)) :=
    (measurable_deriv C.θ).aestronglyMeasurable
  have hslogm : AEStronglyMeasurable (fun s => slog t (C.θ s))
      (volume.restrict (Ioc (-C.K) 0)) :=
    (continuous_slog t).comp_aestronglyMeasurable hθm
  refine intervalIntegrable_of_le_areaElement_of_profileAC h _ ?_ (1 + |t|)
    (fun s hs => abs_lateralFlux_integrand_le_of_profileAC C t hs)
  exact (hθm.pow _).mul ((hdm.neg.mul hslogm).add (hθm.const_mul t))

/-- Integrability of the chain-rule integrand under `ProfileAC`. -/
theorem chain_integrand_intervalIntegrable_of_profileAC {C : Cap m} (h : ProfileAC C)
    (t : ℝ) :
    IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s) volume (-C.K) 0 := by
  have hθm := h.aestronglyMeasurable_theta
  have hdm : AEStronglyMeasurable (deriv C.θ) (volume.restrict (Ioc (-C.K) 0)) :=
    (measurable_deriv C.θ).aestronglyMeasurable
  have hslogm : AEStronglyMeasurable (fun s => slog t (C.θ s))
      (volume.restrict (Ioc (-C.K) 0)) :=
    (continuous_slog t).comp_aestronglyMeasurable hθm
  refine intervalIntegrable_of_le_areaElement_of_profileAC h _ ?_ 1
    (fun s hs => abs_chain_integrand_le_of_profileAC C t hs)
  exact ((hθm.pow _).mul hslogm).mul hdm

/-! ## The flux identity -/

/-- **The flux identity under weak regularity.**  For every `ProfileAC` cap and
every `t`, `m t |C| = (lateral flux) + (terminal flux) − (entrance flux)`.  The
FTC in `s` is applied in the form with a countable exceptional set. -/
theorem fluxIdentity_of_profileAC (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileAC C) :
    FluxIdentity C := by
  have hθcont := h.continuousOn
  have hθK := h.entrance
  obtain ⟨S, hS, hSderiv⟩ := h.hasDerivAt_off_countable
  intro t
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hcont_bp : Continuous (ballProfileIntegral m t) :=
    intervalIntegral.continuous_primitive
      (fun a b => (continuous_ballIntegrand m t).intervalIntegrable a b) 0
  have hfint := lateralFlux_integrand_intervalIntegrable_of_profileAC h t
  have hgint := chain_integrand_intervalIntegrable_of_profileAC h t
  -- chain rule off the countable set and FTC in `s`
  have hFderiv : ∀ s ∈ Ioo (-C.K) 0 \ S,
      HasDerivAt (fun s => ballProfileIntegral m t (C.θ s))
        ((C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s) s := by
    intro s hs
    have h := (ballProfileIntegral_hasDerivAt m t (C.θ s)).comp s (hSderiv s hs)
    simpa only [Function.comp_apply] using h
  have hcontF : ContinuousOn (fun s => ballProfileIntegral m t (C.θ s)) (Icc (-C.K) 0) :=
    hcont_bp.continuousOn.comp hθcont (fun x _ => Set.mem_univ (C.θ x))
  have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun s => ballProfileIntegral m t (C.θ s))
    (fun s => (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s)
    hKle hS hcontF hFderiv hgint
  have hFTC' : ballProfileIntegral m t (C.θ 0) - ballProfileIntegral m t 1
      = ∫ s in (-C.K)..0, (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s := by
    have h := hFTC
    simp only [hθK] at h
    exact h.symm
  -- pointwise algebra: `f + g = t θ^m`
  have hpoint : ∀ s ∈ Icc (-C.K) 0,
      (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)
        + (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s
      = t * (C.θ s) ^ m := by
    intro s _
    have hp : (C.θ s) ^ (m - 1) * C.θ s = (C.θ s) ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    calc (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)
            + (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s
          = t * ((C.θ s) ^ (m - 1) * C.θ s) := by ring
        _ = t * (C.θ s) ^ m := by rw [hp]
  have hsum : (∫ s in (-C.K)..0,
          (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s))
      + (∫ s in (-C.K)..0, (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s)
      = t * ∫ s in (-C.K)..0, (C.θ s) ^ m := by
    rw [← intervalIntegral.integral_add hfint hgint]
    have hcongr : (∫ s in (-C.K)..0,
          ((C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)
            + (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s))
        = ∫ s in (-C.K)..0, t * (C.θ s) ^ m := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      have hsIcc : s ∈ Icc (-C.K) 0 := by
        rw [Set.uIcc_of_le hKle] at hs
        exact hs
      exact hpoint s hsIcc
    rw [hcongr, intervalIntegral.integral_const_mul]
  have hkey : (∫ s in (-C.K)..0,
          (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s))
        + (ballProfileIntegral m t (C.θ 0) - ballProfileIntegral m t 1)
      = t * ∫ s in (-C.K)..0, (C.θ s) ^ m := by
    rw [hFTC', hsum]
  have hmain : C.lateralFlux t + C.terminalFlux t - C.entryFlux t
      = (m : ℝ) * omega m *
        ((∫ s in (-C.K)..0,
            (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s))
          + (ballProfileIntegral m t (C.θ 0) - ballProfileIntegral m t 1)) := by
    simp only [lateralFlux, terminalFlux, entryFlux]
    ring
  rw [hmain, hkey]
  simp only [revolutionVolume]
  ring

/-! ## Pointwise domination of the fluxes by the areas -/

/-- The Cauchy–Schwarz bound of `lateralFlux_integrand_le_area_integrand`, for
the closed parameter range `0 ≤ t ≤ 1`. -/
theorem lateralFlux_integrand_le_area_integrand_of_Icc (m : ℕ) (C : Cap m)
    {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs : s ∈ Ioo (-C.K) 0) :
    (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)
      ≤ (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2) := by
  have hθpos : 0 < C.θ s := C.θ_pos s hs
  have hθle : C.θ s ≤ 1 := C.θ_le_one s hs
  have hpow : 0 ≤ (C.θ s) ^ (m - 1) := pow_nonneg (le_of_lt hθpos) _
  apply mul_le_mul_of_nonneg_left _ hpow
  have hs2 : (slog t (C.θ s)) ^ 2 = 1 - t ^ 2 * (C.θ s) ^ 2 := by
    apply slog_sq
    have htθ0 : 0 ≤ t * C.θ s := mul_nonneg ht0 (le_of_lt hθpos)
    have htθ1 : t * C.θ s ≤ 1 := by
      have hle : t * C.θ s ≤ t := by
        simpa using mul_le_mul_of_nonneg_left hθle ht0
      linarith
    nlinarith [htθ0, htθ1]
  have hkey : (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s) ^ 2
      ≤ 1 + (deriv C.θ s) ^ 2 := by
    have hexp : 1 + (deriv C.θ s) ^ 2
          - (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s) ^ 2
        = (deriv C.θ s * (t * C.θ s) + slog t (C.θ s)) ^ 2 := by
      nlinarith [hs2]
    nlinarith [sq_nonneg (deriv C.θ s * (t * C.θ s) + slog t (C.θ s)), hexp]
  calc -(deriv C.θ s) * slog t (C.θ s) + t * C.θ s
        ≤ |-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s| := le_abs_self _
      _ = Real.sqrt ((-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (1 + (deriv C.θ s) ^ 2) := Real.sqrt_le_sqrt hkey

/-- **Lateral bound under weak regularity.**  For `0 ≤ t ≤ 1` the lateral flux
is at most the lateral area. -/
theorem lateralFlux_le_lateralArea_of_profileAC (m : ℕ) (C : Cap m) (h : ProfileAC C)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    C.lateralFlux t ≤ C.lateralArea := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hfint := lateralFlux_integrand_intervalIntegrable_of_profileAC h t
  have hgint := h.areaElement_intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hKle hfint hgint
    (fun s hs => lateralFlux_integrand_le_area_integrand_of_Icc m C ht0 ht1 hs)
  have hm0 : 0 ≤ (m : ℝ) * omega m :=
    mul_nonneg (Nat.cast_nonneg m) (le_of_lt (omega_pos m))
  calc C.lateralFlux t
        = (m : ℝ) * omega m *
            ∫ s in (-C.K)..0,
              (C.θ s) ^ (m - 1) *
                (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s) := rfl
      _ ≤ (m : ℝ) * omega m *
            ∫ s in (-C.K)..0, (C.θ s) ^ (m - 1) *
              Real.sqrt (1 + (deriv C.θ s) ^ 2) :=
            mul_le_mul_of_nonneg_left hmono hm0
      _ = C.lateralArea := by
            rw [lateralArea]

/-- **Terminal bound** (no regularity needed).  For `θ(0) ≥ 0` and `0 ≤ t` the
terminal flux is at most `ω_m θ(0)^m`. -/
theorem terminalFlux_le_terminalArea_of_profileAC (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    {t : ℝ} (hθ0 : 0 ≤ C.θ 0) :
    C.terminalFlux t ≤ C.terminalArea := by
  have hfcont : ContinuousOn (fun r : ℝ => r ^ (m - 1) * slog t r)
      (Icc (0:ℝ) (C.θ 0)) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.pow _
    · exact (continuous_slog t).continuousOn
  have hgcont : ContinuousOn (fun r : ℝ => r ^ (m - 1)) (Icc (0:ℝ) (C.θ 0)) :=
    continuousOn_id.pow _
  have hpoint : ∀ r ∈ Icc (0:ℝ) (C.θ 0), r ^ (m - 1) * slog t r ≤ r ^ (m - 1) := by
    intro r hr
    have hpow : 0 ≤ r ^ (m - 1) := pow_nonneg hr.1 _
    calc r ^ (m - 1) * slog t r ≤ r ^ (m - 1) * 1 :=
          mul_le_mul_of_nonneg_left (slog_le_one t r) hpow
      _ = r ^ (m - 1) := mul_one _
  have hfu : ContinuousOn (fun r : ℝ => r ^ (m - 1) * slog t r)
      (Set.uIcc (0:ℝ) (C.θ 0)) := by rw [Set.uIcc_of_le hθ0]; exact hfcont
  have hgu : ContinuousOn (fun r : ℝ => r ^ (m - 1)) (Set.uIcc (0:ℝ) (C.θ 0)) := by
    rw [Set.uIcc_of_le hθ0]; exact hgcont
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hθ0 hfu.intervalIntegrable
    hgu.intervalIntegrable hpoint
  have hval : ∫ r in (0:ℝ)..(C.θ 0), r ^ (m - 1) = (C.θ 0) ^ m / (m : ℝ) := by
    rw [integral_pow, Nat.sub_add_cancel hm, zero_pow (by omega : m ≠ 0), sub_zero]
    have hden : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      rw [show (1:ℝ) = ((1:ℕ) : ℝ) by norm_num, ← Nat.cast_add, Nat.sub_add_cancel hm]
    rw [hden]
  have hmne : (m : ℝ) ≠ 0 := by
    have : (0:ℕ) < m := by omega
    exact_mod_cast (ne_of_gt this)
  have hbound : C.terminalFlux t
      ≤ (m : ℝ) * omega m * ((C.θ 0) ^ m / (m : ℝ)) := by
    simp only [terminalFlux, ballProfileIntegral]
    exact mul_le_mul_of_nonneg_left (by rw [← hval]; exact hmono)
      (mul_nonneg (Nat.cast_nonneg m) (le_of_lt (omega_pos m)))
  have hfinal : (m : ℝ) * omega m * ((C.θ 0) ^ m / (m : ℝ)) = C.terminalArea := by
    simp only [terminalArea]
    field_simp
  linarith

/-! ## Nonnegativity of the terminal radius -/

/-- Under `ProfileAC` the terminal radius `θ(0)` is nonnegative: it is the limit
of the positive values `θ(s)`, `s ∈ (-K,0)`. -/
theorem ProfileAC.theta_zero_nonneg {C : Cap m} (h : ProfileAC C) : 0 ≤ C.θ 0 := by
  have hKlt : (-C.K : ℝ) < 0 := neg_neg_of_pos C.hK
  have hKle : (-C.K : ℝ) ≤ 0 := hKlt.le
  have h0 : (0 : ℝ) ∈ Icc (-C.K) 0 := right_mem_Icc.mpr hKle
  have hcw : Tendsto C.θ (𝓝[Icc (-C.K) 0] (0 : ℝ)) (𝓝 (C.θ 0)) := h.continuousOn 0 h0
  have hmono : 𝓝[Ioo (-C.K) 0] (0 : ℝ) ≤ 𝓝[Icc (-C.K) 0] (0 : ℝ) :=
    nhdsWithin_mono _ Ioo_subset_Icc_self
  haveI : NeBot (𝓝[Ioo (-C.K) 0] (0 : ℝ)) := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hKlt)]
    exact h0
  refine ge_of_tendsto (hcw.mono_left hmono) ?_
  exact eventually_of_mem self_mem_nhdsWithin (fun x hx => (C.θ_pos x hx).le)

/-! ## The sharp inequality -/

/-- **Sharp inequality for the explicit revolution functional under weak
regularity.**  Every `ProfileAC` cap satisfies `𝓕(C) ≥ ω_{m+1}/2`.  In
particular this covers the hemisphere (`hemisphere_profileC1`). -/
theorem sharp_revolutionF_of_profileAC (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileAC C) :
    C.revolutionF ≥ omega (m + 1) / 2 := by
  have hθ0 : 0 ≤ C.θ 0 := h.theta_zero_nonneg
  apply sharp_of_sliced_inequality m C _ (entryFluxLimit m hm C)
  intro t ht
  have hflux := fluxIdentity_of_profileAC m hm C h t
  have hlat := lateralFlux_le_lateralArea_of_profileAC m C h ht.1.le ht.2.le
  have hterm := terminalFlux_le_terminalArea_of_profileAC m hm C (t := t) hθ0
  rw [revolutionArea]
  linarith

/-! ## The defect identity -/

theorem lateralArea_sub_lateralFlux_one_of_profileAC (m : ℕ) (C : Cap m) (h : ProfileAC C) :
    C.lateralArea - C.lateralFlux 1 = C.lateralDefect := by
  have hA := h.areaElement_intervalIntegrable
  have hF := lateralFlux_integrand_intervalIntegrable_of_profileAC h 1
  have hpt : ∀ s ∈ Set.uIcc (-C.K) 0,
      (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2)
        - (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog 1 (C.θ s) + 1 * C.θ s)
      = (C.θ s) ^ (m - 1) *
          (Real.sqrt (1 + (deriv C.θ s) ^ 2)
            + (deriv C.θ s) * Real.sqrt (1 - (C.θ s) ^ 2) - C.θ s) := by
    intro s _
    simp only [slog, one_pow, one_mul]
    ring
  rw [lateralArea, lateralFlux, lateralDefect, ← mul_sub, ← intervalIntegral.integral_sub hA hF]
  congr 1
  exact intervalIntegral.integral_congr hpt

/-- **Defect identity under weak regularity.**
`𝓕(C) - ω_{m+1}/2 = lateralDefect + terminalDefect` for every `ProfileAC` cap. -/
theorem defectIdentity_of_profileAC (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileAC C) :
    DefectIdentity C := by
  have hlim1 : C.entryFlux 1 = omega (m + 1) / 2 := by
    simpa only [entryFlux] using entryFluxValueTarget m hm
  have hflux := fluxIdentity_of_profileAC m hm C h 1
  have hV : (m : ℝ) * C.revolutionVolume
      = C.lateralFlux 1 + C.terminalFlux 1 - C.entryFlux 1 := by
    simpa using hflux
  have hlat := lateralArea_sub_lateralFlux_one_of_profileAC m C h
  have hterm := terminalArea_sub_terminalFlux_one m C
  unfold DefectIdentity
  rw [show C.revolutionF = C.revolutionArea - (m : ℝ) * C.revolutionVolume from rfl,
    show C.revolutionArea = C.lateralArea + C.terminalArea from rfl, hV]
  linarith [hlat, hterm, hlim1]

/-! ## Instances: the semicircular profiles -/

theorem continuous_semi (K : ℝ) : Continuous (semi K) := by
  apply Continuous.sqrt
  fun_prop

theorem semi_le_one' (K s : ℝ) : semi K s ≤ 1 := by
  rw [semi, Real.sqrt_le_one]
  nlinarith [sq_nonneg (s + K)]

theorem semi_nonneg (K s : ℝ) : 0 ≤ semi K s := Real.sqrt_nonneg _

theorem semi_inner_pos (K : ℝ) (hK1 : K ≤ 1) {s : ℝ} (hs : s ∈ Ioo (-K) 0) :
    0 < 1 - (s + K) ^ 2 := by
  have hs1 : 0 < s + K := by linarith [hs.1]
  have hs2 : s + K < 1 := by linarith [hs.2, hK1]
  nlinarith

theorem semi_hasDerivAt_deriv (K : ℝ) (hK1 : K ≤ 1) {s : ℝ} (hs : s ∈ Ioo (-K) 0) :
    HasDerivAt (semi K) (deriv (semi K) s) s :=
  (semi_hasDerivAt K (semi_inner_pos K hK1 hs)).differentiableAt.hasDerivAt

theorem semi_deriv_continuousOn (K : ℝ) (hK1 : K ≤ 1) :
    ContinuousOn (fun s => deriv (semi K) s) (Ioo (-K) 0) := by
  have hD : ContinuousOn (semiD K) (Ioo (-K) 0) := by
    have hnum : ContinuousOn (fun s : ℝ => -(s + K)) (Ioo (-K) 0) := by fun_prop
    have hden : ContinuousOn (fun s : ℝ => (Real.sqrt (1 - (s + K) ^ 2))⁻¹) (Ioo (-K) 0) := by
      apply ContinuousOn.inv₀
      · apply ContinuousOn.sqrt; fun_prop
      · intro s hs
        exact ne_of_gt (Real.sqrt_pos.2 (semi_inner_pos K hK1 hs))
    exact hnum.mul hden
  exact hD.congr (fun s hs => deriv_semi K (semi_inner_pos K hK1 hs))

/-- The arc-length density of the semicircular profile is interval integrable on
`(-K,0)` for `0 < K ≤ 1` (including the singular endpoint at `K = 1`): it is the
nonnegative derivative of `s ↦ arcsin(s+K)`. -/
theorem semi_arc_intervalIntegrable (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    IntervalIntegrable (fun s => Real.sqrt (1 + (deriv (semi K) s) ^ 2)) volume (-K) 0 := by
  set F : ℝ → ℝ := fun s => Real.arcsin (s + K) with hF
  have hcont : ContinuousOn F (Icc (-K) 0) := by
    rw [hF]; fun_prop
  have hderiv : ∀ x ∈ Ioo (-K) 0,
      HasDerivAt F (Real.sqrt (1 + (deriv (semi K) x) ^ 2)) x := by
    intro x hx
    have hx1 : x + K ≠ -1 := by linarith [hx.1]
    have hx2 : x + K ≠ 1 := by
      have : x + K < 1 := by linarith [hx.2, hK1]
      linarith
    have hbase : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (x + K) ^ 2)) (x + K) :=
      Real.hasDerivAt_arcsin hx1 hx2
    have hlin : HasDerivAt (fun s : ℝ => s + K) 1 x := (hasDerivAt_id x).add_const K
    have hcomp := hbase.comp x hlin
    have hpos : 0 < 1 - (x + K) ^ 2 := semi_inner_pos K hK1 hx
    have hvalue : 1 / Real.sqrt (1 - (x + K) ^ 2) =
        Real.sqrt (1 + (deriv (semi K) x) ^ 2) := by
      rw [deriv_semi K hpos]
      have hsq : (Real.sqrt (1 - (x + K) ^ 2)) ^ 2 = 1 - (x + K) ^ 2 :=
        Real.sq_sqrt (le_of_lt hpos)
      have hmain : 1 + (semiD K x) ^ 2 = ((Real.sqrt (1 - (x + K) ^ 2))⁻¹) ^ 2 := by
        simp only [semiD]
        field_simp
        nlinarith [hsq]
      rw [hmain, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity), one_div]
    have hfun : (Real.arcsin ∘ fun s : ℝ => s + K) = F := by rw [hF]; rfl
    rw [hfun] at hcomp
    exact hcomp.congr_deriv (by simpa using hvalue)
  have hpos' : ∀ x ∈ Ioo (-K) 0,
      0 ≤ Real.sqrt (1 + (deriv (semi K) x) ^ 2) := fun x hx => Real.sqrt_nonneg _
  have huIcc : Set.uIcc (-K) 0 = Icc (-K) 0 :=
    Set.uIcc_of_le (neg_nonpos.mpr (le_of_lt hK))
  have hcont' : ContinuousOn F (Set.uIcc (-K) 0) := by rw [huIcc]; exact hcont
  have hmin : min (-K) (0 : ℝ) = -K := min_eq_left (neg_nonpos.mpr (le_of_lt hK))
  have hmax : max (-K) (0 : ℝ) = 0 := max_eq_right (neg_nonpos.mpr (le_of_lt hK))
  exact intervalIntegral.intervalIntegrable_deriv_of_nonneg (a := -K) (b := 0) hcont'
    (fun x hx => by
      have hx' : x ∈ Ioo (-K) 0 := by simpa only [hmin, hmax] using hx
      exact hderiv x hx')
    (fun x hx => by
      have hx' : x ∈ Ioo (-K) 0 := by simpa only [hmin, hmax] using hx
      exact hpos' x hx')

/-- The area element of the semicircular profile is interval integrable, for
every transverse dimension `m` (domination by the arc-length density). -/
theorem semi_areaElement_intervalIntegrable (m : ℕ) (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    IntervalIntegrable
      (fun s => (semi K s) ^ (m - 1) * Real.sqrt (1 + (deriv (semi K) s) ^ 2))
      volume (-K) 0 := by
  have harc := semi_arc_intervalIntegrable K hK hK1
  refine harc.mono_fun' ?_ ?_
  · have hmeas : Measurable
        (fun s => (semi K s) ^ (m - 1) * Real.sqrt (1 + (deriv (semi K) s) ^ 2)) := by
      apply Measurable.mul
      · exact ((continuous_semi K).measurable).pow_const _
      · exact (measurable_const.add ((measurable_deriv (semi K)).pow_const 2)).sqrt
    exact hmeas.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun s => ?_)
    show ‖(semi K s) ^ (m - 1) * Real.sqrt (1 + (deriv (semi K) s) ^ 2)‖
      ≤ Real.sqrt (1 + (deriv (semi K) s) ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (semi_nonneg K s) _),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hpow : (semi K s) ^ (m - 1) ≤ 1 := pow_le_one₀ (semi_nonneg K s) (semi_le_one' K s)
    calc (semi K s) ^ (m - 1) * Real.sqrt (1 + (deriv (semi K) s) ^ 2)
        ≤ 1 * Real.sqrt (1 + (deriv (semi K) s) ^ 2) :=
          mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)
      _ = Real.sqrt (1 + (deriv (semi K) s) ^ 2) := one_mul _

/-- The semicircular profile of radius `K ∈ (0,1]` is `ProfileC1`-regular, as
the profile of any cap with `θ = semi K` on the axial interval `(-K,0)`. -/
theorem semi_profileC1 (C : Cap m) (hθ : C.θ = semi C.K) (hK1 : C.K ≤ 1) : ProfileC1 C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hθ]; exact (continuous_semi C.K).continuousOn
  · rw [hθ, semi, show -C.K + C.K = (0 : ℝ) by ring]
    simp
  · intro s hs
    rw [hθ]
    exact semi_hasDerivAt_deriv C.K hK1 hs
  · rw [hθ]
    exact semi_deriv_continuousOn C.K hK1
  · rw [hθ]
    exact semi_areaElement_intervalIntegrable m C.K C.hK hK1

/-- **The hemisphere is `ProfileC1`** (hence `ProfileAC`), for every `m`. -/
theorem hemisphere_profileC1 (m : ℕ) (_hm : 1 ≤ m) : ProfileC1 (hemisphere m) :=
  semi_profileC1 (hemisphere m) rfl (le_refl 1)

theorem hemisphere_profileAC (m : ℕ) (hm : 1 ≤ m) : ProfileAC (hemisphere m) :=
  (hemisphere_profileC1 m hm).profileAC

/-- **The truncated semicircle is `ProfileC1`.** -/
theorem truncatedSemi_profileC1 (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    ProfileC1 (truncatedSemi γ hγ hγ1) :=
  semi_profileC1 (truncatedSemi γ hγ hγ1) rfl (by
    show Real.sqrt (1 - γ ^ 2) ≤ 1
    rw [Real.sqrt_le_one]; nlinarith)

/-- **The flat cap is `ProfileC1`.** -/
theorem flat_profileC1 (m : ℕ) (K : ℝ) (hK : 0 < K) : ProfileC1 (flat m K hK) := by
  have hderiv : (fun s => deriv (flat m K hK).θ s) = fun _ : ℝ => (0 : ℝ) := by
    funext s; simp [flat]
  refine ⟨continuousOn_const, by simp [flat], ?_, ?_, ?_⟩
  · intro s _
    rw [show deriv (flat m K hK).θ s = 0 by simp [flat]]
    exact hasDerivAt_const s 1
  · rw [hderiv]
    exact continuousOn_const
  · have h : (fun s => ((flat m K hK).θ s) ^ (m - 1) *
        Real.sqrt (1 + (deriv (flat m K hK).θ s) ^ 2)) = fun _ : ℝ => (1 : ℝ) := by
      funext s; simp [flat]
    rw [h]
    exact intervalIntegrable_const

/-! ## Corollaries -/

/-- **Sharp inequality for `ProfileC1` caps.** -/
theorem revolutionF_ge_of_profileC1 (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileC1 C) :
    C.revolutionF ≥ omega (m + 1) / 2 :=
  sharp_revolutionF_of_profileAC m hm C h.profileAC

/-- The sharp inequality holds for the hemisphere (with equality, by
`hemisphere_revolutionF_eq`), the flat cap and the truncated semicircle. -/
theorem hemisphere_revolutionF_ge (m : ℕ) (hm : 1 ≤ m) :
    (hemisphere m).revolutionF ≥ omega (m + 1) / 2 :=
  revolutionF_ge_of_profileC1 m hm _ (hemisphere_profileC1 m hm)

theorem flat_revolutionF_ge (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) :
    (flat m K hK).revolutionF ≥ omega (m + 1) / 2 :=
  revolutionF_ge_of_profileC1 m hm _ (flat_profileC1 m K hK)

theorem truncatedSemi_revolutionF_ge (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).revolutionF ≥ omega 2 / 2 :=
  revolutionF_ge_of_profileC1 1 le_rfl _ (truncatedSemi_profileC1 γ hγ hγ1)

/-- The defect identity for the hemisphere. -/
theorem hemisphere_defectIdentity (m : ℕ) (hm : 1 ≤ m) : DefectIdentity (hemisphere m) :=
  defectIdentity_of_profileAC m hm _ (hemisphere_profileAC m hm)

end

end Cap
end RobinCaps
