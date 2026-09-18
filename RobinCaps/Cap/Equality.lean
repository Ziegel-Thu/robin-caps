import Mathlib
import RobinCaps.Cap.Regular
import RobinCaps.Cap.SharpInequality
import RobinCaps.Cap.SharpComplete
import RobinCaps.Cap.Sphere

/-!
# The equality case of the sharp end-cap inequality

This file proves the equality characterisation of the sharp cap inequality
(manuscript `thm:calibration`, equality case) for the explicit revolution
functional, under the `C¹`-on-the-open-interval regularity `ProfileC1`.

The defect identity `𝓕(C) - ω_{m+1}/2 = lateralDefect + terminalDefect` is taken
as a hypothesis (`DefectIdentity C`); it is proved elsewhere.  Here we show:

* the lateral defect integrand `θ^{m-1}(√(1+θ'²) + θ'√(1-θ²) - θ)` is pointwise
  nonnegative (two-dimensional Cauchy–Schwarz), with equality iff the profile
  ODE `θ' = -√(1-θ²)/θ` holds (`defect_bracket_nonneg`,
  `defect_bracket_eq_zero_iff`);
* the terminal defect `ω_m θ₀^m - m ω_m ∫_0^{θ₀} u^{m-1}√(1-u²) du` is
  nonnegative and vanishes iff `θ₀ = 0` (`terminalDefect_nonneg`,
  `terminalDefect_eq_zero_iff`);
* the lateral defect is nonnegative and vanishes only if the ODE holds on the
  whole open interval (`lateralDefect_nonneg_of_profileC1`,
  `equalityODE_of_lateralDefect_eq_zero`);
* the ODE together with `θ(0) = 0` forces the equality profile (a straight unit
  cylinder followed by the unit semicircle), by integrating `h = √(1-θ²)`,
  `h' = 1` (`equalityProfile_of_equalityODE`);
* conversely the equality profile has `𝓕 = ω_{m+1}/2`
  (`revolutionF_eq_of_equalityProfile`), via `revF_append` and the hemisphere
  computation;
* assembly: `revolutionF_eq_iff_of_defectIdentity`.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RobinCaps
namespace Cap

noncomputable section

namespace Equality

/-! ## Measure-theoretic helpers -/

/-- A property holding at every point of the open interval holds a.e. on the
unordered-interval restriction. -/
theorem ae_restrict_uIoc_of_forall_Ioo {a b : ℝ} (hab : a ≤ b) {p : ℝ → Prop}
    (h : ∀ x ∈ Ioo a b, p x) : ∀ᵐ x ∂(volume.restrict (Ι a b)), p x := by
  rw [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall h

theorem ae_ne_point (p : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ p := by
  rw [ae_iff]
  have : {x : ℝ | ¬ x ≠ p} = {p} := by
    ext x; simp
  rw [this]
  exact measure_singleton p

/-- Almost every point of `Ι a b` lies in the open interval and differs from a
given exceptional point `p`. -/
theorem ae_uIoc_Ioo_ne {a b : ℝ} (hab : a ≤ b) (p : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι a b → (x ∈ Ioo a b ∧ x ≠ p) := by
  filter_upwards [ae_ne_point b, ae_ne_point p] with x hxb hxp hx
  rw [uIoc_of_le hab] at hx
  exact ⟨⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩, hxp⟩

/-- Two functions agreeing on an open interval minus a point have the same
derivative there. -/
theorem deriv_eq_of_eqOn_Ioo_ne {θ₁ θ₂ : ℝ → ℝ} {a b p s : ℝ}
    (h : ∀ x ∈ Ioo a b, x ≠ p → θ₁ x = θ₂ x) (hs : s ∈ Ioo a b) (hsp : s ≠ p) :
    deriv θ₁ s = deriv θ₂ s := by
  apply Filter.EventuallyEq.deriv_eq
  have hopen : IsOpen (Ioo a b ∩ {p}ᶜ) := isOpen_Ioo.inter isClosed_singleton.isOpen_compl
  have hmem : s ∈ Ioo a b ∩ {p}ᶜ := ⟨hs, hsp⟩
  filter_upwards [hopen.mem_nhds hmem] with x hx
  exact h x hx.1 hx.2

/-! ## Item 1: the pointwise Cauchy–Schwarz bracket -/

/-- Lagrange identity underlying the bracket bound: with `b = √(1-θ²)`,
`1 + d² - (θ - d b)² = (θ d + b)²`. -/
theorem bracket_lagrange {θ d b : ℝ} (hb2 : b ^ 2 = 1 - θ ^ 2) :
    1 + d ^ 2 - (θ - d * b) ^ 2 = (θ * d + b) ^ 2 := by
  linear_combination (-(1 + d ^ 2)) * hb2

/-- The lateral defect bracket `√(1+d²) + d√(1-θ²) - θ` is nonnegative for
`0 ≤ θ ≤ 1` and every real `d`. -/
theorem defect_bracket_nonneg {θ d : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 ≤ Real.sqrt (1 + d ^ 2) + d * Real.sqrt (1 - θ ^ 2) - θ := by
  have hb2 : (Real.sqrt (1 - θ ^ 2)) ^ 2 = 1 - θ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hid := bracket_lagrange (d := d) hb2
  have hkey : (θ - d * Real.sqrt (1 - θ ^ 2)) ^ 2 ≤ 1 + d ^ 2 := by
    nlinarith [sq_nonneg (θ * d + Real.sqrt (1 - θ ^ 2))]
  have hle : θ - d * Real.sqrt (1 - θ ^ 2) ≤ Real.sqrt (1 + d ^ 2) := by
    calc θ - d * Real.sqrt (1 - θ ^ 2) ≤ |θ - d * Real.sqrt (1 - θ ^ 2)| := le_abs_self _
      _ = Real.sqrt ((θ - d * Real.sqrt (1 - θ ^ 2)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (1 + d ^ 2) := Real.sqrt_le_sqrt hkey
  linarith

/-- Equality in the bracket bound holds exactly along the profile ODE
`d = -√(1-θ²)/θ` (for `0 < θ ≤ 1`). -/
theorem defect_bracket_eq_zero_iff {θ d : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) :
    Real.sqrt (1 + d ^ 2) + d * Real.sqrt (1 - θ ^ 2) - θ = 0 ↔
      d = -Real.sqrt (1 - θ ^ 2) / θ := by
  have hb2 : (Real.sqrt (1 - θ ^ 2)) ^ 2 = 1 - θ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hid := bracket_lagrange (d := d) hb2
  have hθne : θ ≠ 0 := ne_of_gt h0
  constructor
  · intro h
    have hs : Real.sqrt (1 + d ^ 2) = θ - d * Real.sqrt (1 - θ ^ 2) := by linarith
    have hsq : (θ - d * Real.sqrt (1 - θ ^ 2)) ^ 2 = 1 + d ^ 2 := by
      rw [← hs]; exact Real.sq_sqrt (by positivity)
    have hz : (θ * d + Real.sqrt (1 - θ ^ 2)) ^ 2 = 0 := by linarith
    have hz' : θ * d + Real.sqrt (1 - θ ^ 2) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    field_simp
    linarith
  · intro hd
    have h1d : 1 + d ^ 2 = (1 / θ) ^ 2 := by
      rw [hd]
      field_simp
      linarith [hb2]
    have hs : Real.sqrt (1 + d ^ 2) = 1 / θ := by
      rw [h1d, Real.sqrt_sq (by positivity)]
    rw [hs, hd]
    field_simp
    linarith [hb2]

/-! ## Item 2: the terminal defect -/

/-- The terminal defect as a single integral:
`m ω_m ∫_0^{θ₀} u^{m-1}(1 - √(1-u²)) du`. -/
theorem terminalDefect_eq_integral (m : ℕ) (hm : 1 ≤ m) (C : Cap m) :
    C.terminalDefect = (m : ℝ) * omega m *
      ∫ u in (0 : ℝ)..(C.θ 0), u ^ (m - 1) * (1 - Real.sqrt (1 - u ^ 2)) := by
  have hmne : (m : ℝ) ≠ 0 := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast (ne_of_gt this)
  have hpow : ∫ u in (0 : ℝ)..(C.θ 0), u ^ (m - 1) = (C.θ 0) ^ m / (m : ℝ) := by
    rw [integral_pow, Nat.sub_add_cancel hm, zero_pow (by omega : m ≠ 0), sub_zero]
    have hden : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_add, Nat.sub_add_cancel hm]
    rw [hden]
  have hI1 : IntervalIntegrable (fun u : ℝ => u ^ (m - 1)) volume 0 (C.θ 0) :=
    (continuous_id.pow _).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun u : ℝ => u ^ (m - 1) * slog 1 u) volume 0 (C.θ 0) :=
    (continuous_ballIntegrand m 1).intervalIntegrable _ _
  have hsplit : ∫ u in (0 : ℝ)..(C.θ 0), u ^ (m - 1) * (1 - Real.sqrt (1 - u ^ 2))
      = (∫ u in (0 : ℝ)..(C.θ 0), u ^ (m - 1))
        - ∫ u in (0 : ℝ)..(C.θ 0), u ^ (m - 1) * slog 1 u := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp only [slog, one_pow, one_mul]
    ring
  rw [terminalDefect, ballProfileIntegral, hsplit, hpow]
  field_simp

/-- **Terminal defect is nonnegative** for `θ₀ ≥ 0`. -/
theorem terminalDefect_nonneg (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h0 : 0 ≤ C.θ 0) :
    0 ≤ C.terminalDefect := by
  rw [terminalDefect_eq_integral m hm C]
  apply mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (omega_pos m).le)
  apply intervalIntegral.integral_nonneg h0
  intro u hu
  have hsqrt : Real.sqrt (1 - u ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith
  exact mul_nonneg (pow_nonneg hu.1 _) (by linarith)

/-- **Terminal defect vanishes iff the terminal radius is zero** (for `θ₀ ≥ 0`). -/
theorem terminalDefect_eq_zero_iff (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h0 : 0 ≤ C.θ 0) :
    C.terminalDefect = 0 ↔ C.θ 0 = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < C.θ 0 := lt_of_le_of_ne h0 (Ne.symm hne)
    have hI : IntervalIntegrable
        (fun u : ℝ => u ^ (m - 1) * (1 - Real.sqrt (1 - u ^ 2))) volume 0 (C.θ 0) := by
      apply Continuous.intervalIntegrable
      apply Continuous.mul (continuous_id.pow _)
      apply Continuous.sub continuous_const
      apply Continuous.sqrt
      fun_prop
    have hposint := intervalIntegral.intervalIntegral_pos_of_pos_on hI (fun u hu => ?_) hpos
    · rw [terminalDefect_eq_integral m hm C] at h
      have hm0 : 0 < (m : ℝ) * omega m := by
        apply mul_pos _ (omega_pos m)
        exact_mod_cast (show 0 < m by omega)
      have := mul_pos hm0 hposint
      linarith
    · have hu0 : 0 < u := hu.1
      have hsqrt : Real.sqrt (1 - u ^ 2) < 1 := by
        rw [Real.sqrt_lt' one_pos]
        nlinarith
      exact mul_pos (pow_pos hu0 _) (by linarith)
  · intro h
    rw [terminalDefect_eq_integral m hm C, h]
    simp

/-! ## Item 3: the lateral defect is nonnegative -/

/-- The lateral defect integrand. -/
def defectIntegrand (m : ℕ) (C : Cap m) (s : ℝ) : ℝ :=
  (C.θ s) ^ (m - 1) *
    (Real.sqrt (1 + (deriv C.θ s) ^ 2)
      + (deriv C.θ s) * Real.sqrt (1 - (C.θ s) ^ 2) - C.θ s)

/-- The area element `θ^{m-1}√(1+θ'²)`. -/
def areaElement (m : ℕ) (C : Cap m) (s : ℝ) : ℝ :=
  (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2)

theorem lateralDefect_eq_integral (m : ℕ) (C : Cap m) :
    C.lateralDefect = (m : ℝ) * omega m * ∫ s in (-C.K)..0, defectIntegrand m C s := rfl

theorem areaElement_intervalIntegrable (m : ℕ) (C : Cap m) (h : ProfileC1 C) :
    IntervalIntegrable (areaElement m C) volume (-C.K) 0 := h.2.2.2.2

theorem defectIntegrand_nonneg (m : ℕ) (C : Cap m) :
    ∀ s ∈ Ioo (-C.K) 0, 0 ≤ defectIntegrand m C s := by
  intro s hs
  have hθ := C.θ_pos s hs
  exact mul_nonneg (pow_nonneg hθ.le _) (defect_bracket_nonneg hθ.le (C.θ_le_one s hs))

theorem defectIntegrand_continuousOn (m : ℕ) (C : Cap m) (h : ProfileC1 C) :
    ContinuousOn (defectIntegrand m C) (Ioo (-C.K) 0) := by
  have hθ : ContinuousOn C.θ (Ioo (-C.K) 0) := h.1.mono Ioo_subset_Icc_self
  have hd : ContinuousOn (fun s => deriv C.θ s) (Ioo (-C.K) 0) := h.2.2.2.1
  unfold defectIntegrand
  apply ContinuousOn.mul (hθ.pow _)
  apply ContinuousOn.sub _ hθ
  apply ContinuousOn.add
  · exact (continuousOn_const.add (hd.pow 2)).sqrt
  · exact hd.mul (continuousOn_const.sub (hθ.pow 2)).sqrt

/-- Domination of the defect integrand by three times the area element on the
open interval. -/
theorem norm_defectIntegrand_le (m : ℕ) (C : Cap m) :
    ∀ s ∈ Ioo (-C.K) 0, ‖defectIntegrand m C s‖ ≤ 3 * areaElement m C s := by
  intro s hs
  have hθ := C.θ_pos s hs
  have hθ1 := C.θ_le_one s hs
  set d := deriv C.θ s with hd
  set S := Real.sqrt (1 + d ^ 2) with hS
  set b := Real.sqrt (1 - (C.θ s) ^ 2) with hb
  have hS1 : 1 ≤ S := by
    rw [hS, Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hdS : |d| ≤ S := Real.abs_le_sqrt (by linarith)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb1 : b ≤ 1 := by
    rw [hb, Real.sqrt_le_one]
    nlinarith
  have hdb : |d * b| ≤ S := by
    rw [abs_mul, abs_of_nonneg hb0]
    calc |d| * b ≤ |d| * 1 := mul_le_mul_of_nonneg_left hb1 (abs_nonneg d)
      _ = |d| := mul_one _
      _ ≤ S := hdS
  have hbr : |S + d * b - C.θ s| ≤ 3 * S := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (d * b)]
    · linarith [le_abs_self (d * b)]
  have hpow : 0 ≤ (C.θ s) ^ (m - 1) := pow_nonneg hθ.le _
  unfold defectIntegrand areaElement
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
  calc (C.θ s) ^ (m - 1) * |S + d * b - C.θ s|
      ≤ (C.θ s) ^ (m - 1) * (3 * S) := mul_le_mul_of_nonneg_left hbr hpow
    _ = 3 * ((C.θ s) ^ (m - 1) * S) := by ring

theorem defectIntegrand_intervalIntegrable (m : ℕ) (C : Cap m) (h : ProfileC1 C) :
    IntervalIntegrable (defectIntegrand m C) volume (-C.K) 0 := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hA := (areaElement_intervalIntegrable m C h).const_mul 3
  refine hA.mono_fun' ?_ ?_
  · rw [uIoc_of_le hKle, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (defectIntegrand_continuousOn m C h).aestronglyMeasurable measurableSet_Ioo
  · exact ae_restrict_uIoc_of_forall_Ioo hKle (norm_defectIntegrand_le m C)

/-- **Lateral defect is nonnegative** under `ProfileC1`. -/
theorem lateralDefect_nonneg_of_profileC1 (m : ℕ) (C : Cap m) (h : ProfileC1 C) :
    0 ≤ C.lateralDefect := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  rw [lateralDefect_eq_integral]
  apply mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (omega_pos m).le)
  have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-C.K) 0 := intervalIntegrable_const
  have := intervalIntegral.integral_mono_on_of_le_Ioo hKle h0
    (defectIntegrand_intervalIntegrable m C h) (defectIntegrand_nonneg m C)
  simpa using this

/-! ## Item 4: zero lateral defect forces the ODE -/

/-- **Zero lateral defect forces the profile ODE** on the open interval. -/
theorem equalityODE_of_lateralDefect_eq_zero (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (h : ProfileC1 C) (hz : C.lateralDefect = 0) : EqualityODE C := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hint := defectIntegrand_intervalIntegrable m C h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (-C.K) 0 ∪ Ioc 0 (-C.K))] defectIntegrand m C := by
    rw [Ioc_eq_empty (not_lt.mpr hKle), union_empty, ← uIoc_of_le hKle]
    exact ae_restrict_uIoc_of_forall_Ioo hKle (defectIntegrand_nonneg m C)
  have hI0 : ∫ s in (-C.K)..0, defectIntegrand m C s = 0 := by
    have hpos : 0 < (m : ℝ) * omega m := by
      apply mul_pos _ (omega_pos m)
      exact_mod_cast (show 0 < m by omega)
    rw [lateralDefect_eq_integral] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)
  have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hI0
  have hae' : defectIntegrand m C =ᵐ[volume.restrict (Ioo (-C.K) 0)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioc_self.trans subset_union_left) hae
  have heq := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo
    (defectIntegrand_continuousOn m C h) continuousOn_const
  intro s hs
  have h0 : defectIntegrand m C s = 0 := heq hs
  unfold defectIntegrand at h0
  have hθ := C.θ_pos s hs
  have hpow : (C.θ s) ^ (m - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hθ)
  have hbr := (mul_eq_zero.mp h0).resolve_left hpow
  exact (defect_bracket_eq_zero_iff hθ (C.θ_le_one s hs)).mp hbr

/-! ## Item 5: integrating the ODE -/

/-- Along the ODE, `h = √(1-θ²)` has derivative `1` (where `0 < θ < 1`). -/
theorem hasDerivAt_sqrt_one_sub_sq {θ : ℝ → ℝ} {s : ℝ}
    (hd : HasDerivAt θ (deriv θ s) s) (h0 : 0 < θ s) (h1 : θ s < 1)
    (hode : deriv θ s = -(Real.sqrt (1 - (θ s) ^ 2)) / θ s) :
    HasDerivAt (fun t => Real.sqrt (1 - (θ t) ^ 2)) 1 s := by
  have hu : 0 < 1 - (θ s) ^ 2 := by nlinarith
  have hsq : HasDerivAt (fun t => 1 - (θ t) ^ 2) (-(2 * θ s * deriv θ s)) s := by
    have := (hd.fun_pow 2).const_sub 1
    convert this using 1
    push_cast
    ring
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp s hsq
  have hval : 1 / (2 * Real.sqrt (1 - θ s ^ 2)) * -(2 * θ s * deriv θ s) = 1 := by
    rw [hode]
    have hsne : Real.sqrt (1 - θ s ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
    field_simp
  have hfun : ((fun x => Real.sqrt x) ∘ fun t => 1 - (θ t) ^ 2)
      = fun t => Real.sqrt (1 - (θ t) ^ 2) := rfl
  rw [hfun] at hsqrt
  exact hsqrt.congr_deriv hval

/-- **The ODE with `θ(0) = 0` forces the equality profile.** -/
theorem equalityProfile_of_equalityODE (m : ℕ) (C : Cap m) (h : ProfileC1 C)
    (hode : EqualityODE C) (h0 : C.θ 0 = 0) : EqualityProfile C := by
  obtain ⟨hcont, hent, hderiv, _, _⟩ := h
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  set g : ℝ → ℝ := fun t => Real.sqrt (1 - (C.θ t) ^ 2) with hg
  have hgcont : ContinuousOn g (Icc (-C.K) 0) := (continuousOn_const.sub (hcont.pow 2)).sqrt
  have hg0 : g 0 = 1 := by simp [hg, h0]
  have hgderiv : ∀ s ∈ Ioo (-C.K) 0, C.θ s < 1 → HasDerivAt g 1 s := fun s hs hlt =>
    hasDerivAt_sqrt_one_sub_sq (hderiv s hs) (C.θ_pos s hs) hlt (hode s hs)
  -- FTC on `[a, 0]` whenever `θ < 1` on `(a, 0)`
  have hFTC : ∀ a ∈ Icc (-C.K) 0, (∀ s ∈ Ioo a 0, C.θ s < 1) → g a = a + 1 := by
    intro a ha hlt
    have hsub : Icc a 0 ⊆ Icc (-C.K) 0 := Icc_subset_Icc ha.1 le_rfl
    have hsub' : Ioo a 0 ⊆ Ioo (-C.K) 0 := Ioo_subset_Ioo ha.1 le_rfl
    have hI : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a 0 := intervalIntegrable_const
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2 (hgcont.mono hsub)
      (fun s hs => hgderiv s (hsub' hs) (hlt s hs)) hI
    rw [intervalIntegral.integral_const, hg0, smul_eq_mul, mul_one] at hF
    linarith
  -- the closed set where `θ = 1`, and its supremum
  set T : Set ℝ := Icc (-C.K) 0 ∩ C.θ ⁻¹' {1} with hT
  have hTclosed : IsClosed T :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := ⟨-C.K, ⟨⟨le_rfl, hKle⟩, by simpa using hent⟩⟩
  have hTbdd : BddAbove T := ⟨0, fun x hx => hx.1.2⟩
  set s₀ := sSup T with hs₀
  have hs₀mem : s₀ ∈ T := hTclosed.csSup_mem hTne hTbdd
  have hs₀Icc : s₀ ∈ Icc (-C.K) 0 := hs₀mem.1
  have hθs₀ : C.θ s₀ = 1 := by simpa using hs₀mem.2
  have hs₀ne : s₀ ≠ 0 := by
    intro hz
    rw [hz, h0] at hθs₀
    norm_num at hθs₀
  have hs₀lt : s₀ < 0 := lt_of_le_of_ne hs₀Icc.2 hs₀ne
  have hlt : ∀ s ∈ Ioo s₀ 0, C.θ s < 1 := by
    intro s hs
    have hsIoo : s ∈ Ioo (-C.K) 0 := ⟨lt_of_le_of_lt hs₀Icc.1 hs.1, hs.2⟩
    refine lt_of_le_of_ne (C.θ_le_one s hsIoo) (fun heq => ?_)
    have hsT : s ∈ T := ⟨⟨hsIoo.1.le, hs.2.le⟩, by simpa using heq⟩
    exact absurd (le_csSup hTbdd hsT) (not_le.mpr hs.1)
  have hgs₀ : g s₀ = 0 := by simp [hg, hθs₀]
  have hs₀eq : s₀ = -1 := by
    have := hFTC s₀ hs₀Icc hlt
    linarith
  have hK1 : 1 ≤ C.K := by linarith [hs₀Icc.1]
  refine ⟨hK1, ?_, ?_⟩
  · intro s hs
    have hsIoo : s ∈ Ioo (-C.K) 0 := ⟨hs.1, by linarith [hs.2]⟩
    have hs₀Ioo : s₀ ∈ Ioo (-C.K) 0 := ⟨by linarith [hs.1, hs.2], hs₀lt⟩
    have hmono := C.θ_antitone hsIoo hs₀Ioo (by rw [hs₀eq]; exact hs.2.le)
    rw [hθs₀] at hmono
    exact le_antisymm (C.θ_le_one s hsIoo) hmono
  · intro s hs
    have hsIoo : s ∈ Ioo (-C.K) 0 := ⟨by linarith [hs.1], hs.2⟩
    have hgs : g s = s + 1 :=
      hFTC s ⟨hsIoo.1.le, hs.2.le⟩
        (fun t ht => hlt t ⟨by rw [hs₀eq]; linarith [ht.1, hs.1], ht.2⟩)
    have hθpos := C.θ_pos s hsIoo
    have hθle := C.θ_le_one s hsIoo
    have hsq : (g s) ^ 2 = 1 - (C.θ s) ^ 2 := Real.sq_sqrt (by nlinarith)
    rw [hgs] at hsq
    have hθsq : (C.θ s) ^ 2 = 1 - (s + 1) ^ 2 := by linarith
    rw [← hθsq, Real.sqrt_sq hθpos.le]

/-! ## Item 6: the equality profile attains the bound -/

/-- Under the equality profile and continuity, the terminal radius vanishes. -/
theorem theta_zero_eq_zero_of_equalityProfile (m : ℕ) (C : Cap m) (h : ProfileC1 C)
    (hp : EqualityProfile C) : C.θ 0 = 0 := by
  obtain ⟨hK1, _, hright⟩ := hp
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hcw : ContinuousWithinAt C.θ (Icc (-C.K) 0) 0 := h.1 0 ⟨hKle, le_rfl⟩
  have hsub : Ioo (-1 : ℝ) 0 ⊆ Icc (-C.K) 0 := fun x hx => ⟨by linarith [hx.1], hx.2.le⟩
  have h1 : Tendsto C.θ (𝓝[Ioo (-1 : ℝ) 0] 0) (𝓝 (C.θ 0)) :=
    hcw.tendsto.mono_left (nhdsWithin_mono _ hsub)
  have hsemi_cont : Continuous (semi 1) := by
    apply Continuous.sqrt
    fun_prop
  have h2 : Tendsto C.θ (𝓝[Ioo (-1 : ℝ) 0] 0) (𝓝 0) := by
    have hsemi : Tendsto (semi 1) (𝓝[Ioo (-1 : ℝ) 0] 0) (𝓝 (semi 1 0)) :=
      hsemi_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h00 : semi 1 0 = 0 := by simp [semi]
    rw [h00] at hsemi
    refine hsemi.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hright x hx).symm
  haveI : (𝓝[Ioo (-1 : ℝ) 0] 0).NeBot := right_nhdsWithin_Ioo_neBot (by norm_num)
  exact tendsto_nhds_unique h1 h2

/-- The explicit functional only depends on the profile on the open interval
minus one point, together with the terminal value. -/
theorem revF_congr_of_eqOn (m : ℕ) {K : ℝ} (hK : 0 < K) {θ₁ θ₂ : ℝ → ℝ} (p : ℝ)
    (h : ∀ x ∈ Ioo (-K) 0, x ≠ p → θ₁ x = θ₂ x) (h0 : θ₁ 0 = θ₂ 0) :
    revF m K θ₁ = revF m K θ₂ := by
  have hKle : (-K : ℝ) ≤ 0 := by linarith
  have hae := ae_uIoc_Ioo_ne hKle p
  have hL : ∫ s in (-K)..0, (θ₁ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ₁ s) ^ 2)
      = ∫ s in (-K)..0, (θ₂ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ₂ s) ^ 2) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    obtain ⟨hxIoo, hxp⟩ := hx hxI
    rw [deriv_eq_of_eqOn_Ioo_ne h hxIoo hxp, h x hxIoo hxp]
  have hV : ∫ s in (-K)..0, (θ₁ s) ^ m = ∫ s in (-K)..0, (θ₂ s) ^ m := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    obtain ⟨hxIoo, hxp⟩ := hx hxI
    rw [h x hxIoo hxp]
  simp only [revF, revLateral, revVolume, revTerminal, hL, hV, h0]

/-- The hemisphere value of `revF`. -/
theorem revF_semi_one (m : ℕ) (hm : 1 ≤ m) : revF m 1 (semi 1) = omega (m + 1) / 2 := by
  have h := hemisphere_revolutionF_eq m hm
  rw [revF_eq] at h
  exact h

/-- **The equality profile attains the sharp bound.** -/
theorem revolutionF_eq_of_equalityProfile (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileC1 C)
    (hp : EqualityProfile C) : C.revolutionF = omega (m + 1) / 2 := by
  have h0 := theta_zero_eq_zero_of_equalityProfile m C h hp
  obtain ⟨hK1, hleft, hright⟩ := hp
  have hsemi0 : semi 1 0 = 0 := by simp [semi]
  rw [revF_eq]
  rcases eq_or_lt_of_le hK1 with hK | hK
  · -- `K = 1`: the profile is the hemisphere off the null set `{0}`.
    rw [← hK]
    rw [revF_congr_of_eqOn m one_pos (θ₂ := semi 1) (-1)
      (fun x hx _ => hright x hx) (by rw [h0, hsemi0])]
    exact revF_semi_one m hm
  · -- `K > 1`: the profile is a hemisphere extended by a cylinder of length `K - 1`.
    have hδ : 0 < C.K - 1 := by linarith
    have hcongr : revF m C.K C.θ = revF m C.K (appendProfile 1 (C.K - 1) (semi 1)) := by
      apply revF_congr_of_eqOn m C.hK (-1)
      · intro x hx hxp
        rcases lt_or_gt_of_ne hxp with hlt | hgt
        · rw [appendProfile_cyl _ _ _ hlt]
          exact hleft x ⟨hx.1, hlt⟩
        · rw [appendProfile_cap _ _ _ hgt]
          exact hright x ⟨hgt, hx.2⟩
      · rw [appendProfile_cap _ _ _ (by norm_num), h0, hsemi0]
    rw [hcongr]
    -- integrability of the hemisphere integrands on `(-1, 0)`
    have hsemi_cont : Continuous (semi 1) := by
      apply Continuous.sqrt
      fun_prop
    have hintV : IntervalIntegrable (fun s => (semi 1 s) ^ m) volume (-1) 0 :=
      (hsemi_cont.pow m).intervalIntegrable _ _
    have hintL : IntervalIntegrable
        (fun s => (semi 1 s) ^ (m - 1) * Real.sqrt (1 + (deriv (semi 1) s) ^ 2)) volume (-1) 0 := by
      have hsub : uIcc (-1 : ℝ) 0 ⊆ uIcc (-C.K) 0 := by
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), uIcc_of_le (by linarith : (-C.K : ℝ) ≤ 0)]
        exact Icc_subset_Icc (by linarith) le_rfl
      have hA := (areaElement_intervalIntegrable m C h).mono_set hsub
      refine hA.congr_ae (ae_restrict_uIoc_of_forall_Ioo (by norm_num) ?_)
      intro x hx
      have hxne : x ≠ -1 := ne_of_gt hx.1
      have hθx : C.θ x = semi 1 x := hright x hx
      have hdx : deriv C.θ x = deriv (semi 1) x :=
        deriv_eq_of_eqOn_Ioo_ne (a := -1) (b := 0) (p := -1)
          (fun y hy _ => hright y hy) hx hxne
      simp only [areaElement, hθx, hdx]
    set δ := C.K - 1 with hδdef
    have hKeq : C.K = 1 + δ := by rw [hδdef]; ring
    rw [hKeq, revF_append m 1 δ hδ one_pos (semi 1) hintL hintV]
    exact revF_semi_one m hm

/-! ## Item 7: assembly -/

/-- Under `ProfileC1` the terminal radius is nonnegative (by continuity). -/
theorem theta_zero_nonneg_of_profileC1 (m : ℕ) (C : Cap m) (h : ProfileC1 C) :
    0 ≤ C.θ 0 := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hcw : ContinuousWithinAt C.θ (Icc (-C.K) 0) 0 := h.1 0 ⟨hKle, le_rfl⟩
  have h1 : Tendsto C.θ (𝓝[Ioo (-C.K) 0] 0) (𝓝 (C.θ 0)) :=
    hcw.tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  haveI : (𝓝[Ioo (-C.K) 0] 0).NeBot := right_nhdsWithin_Ioo_neBot (by linarith [C.hK])
  refine ge_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (C.θ_pos x hx).le

/-- **Equality characterisation** for the explicit revolution functional, given
the defect identity: `𝓕(C) = ω_{m+1}/2` iff `C` is a unit hemisphere optionally
extended by a straight unit cylinder. -/
theorem revolutionF_eq_iff_of_defectIdentity (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (h : ProfileC1 C) (hD : DefectIdentity C) :
    C.revolutionF = omega (m + 1) / 2 ↔ EqualityProfile C := by
  constructor
  · intro hF
    have h0 := theta_zero_nonneg_of_profileC1 m C h
    have hL := lateralDefect_nonneg_of_profileC1 m C h
    have hT := terminalDefect_nonneg m hm C h0
    have hsum : C.lateralDefect + C.terminalDefect = 0 := by
      unfold DefectIdentity at hD
      linarith
    have hL0 : C.lateralDefect = 0 := by linarith
    have hT0 : C.terminalDefect = 0 := by linarith
    exact equalityProfile_of_equalityODE m C h
      (equalityODE_of_lateralDefect_eq_zero m hm C h hL0)
      ((terminalDefect_eq_zero_iff m hm C h0).mp hT0)
  · exact revolutionF_eq_of_equalityProfile m hm C h

end Equality

end

end Cap
end RobinCaps
