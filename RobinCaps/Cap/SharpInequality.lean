import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Sharp
import RobinCaps.Cap.Checks

/-!
# The sharp cap inequality: sliced (Fubini/FTC) reduction

This file formalises the *analytic skeleton* of the divergence-theorem proof of
the sharp cap inequality of `sec:calibration` of
`reference/robin_endcaps_corrected_en.tex`, without appealing to a general
divergence theorem for curved domains (mathlib only has the box divergence
theorem).

The manuscript's argument uses the vector field
`X_t(s,z) = (√(1-t²|z|²), t z)` on the unit cylinder and the identity

  `m t |C| = ∫_Γ X_t·ν dH^m − ∫_{B_m(1)} √(1-t²|z|²) dz`.       (∗)

Rather than proving (∗) for the Hausdorff functional (which would require a
surface-area/area formula that mathlib lacks — this is the existing predicate
`Cap.HausdorffIntegralBridge`), we observe that for the **explicit revolution
functional** (`Cap.revolutionArea`, `Cap.revolutionVolume`) the identity (∗)
becomes a *one-dimensional* statement, obtained by (a) writing the flux through
the lateral boundary as an explicit `s`-integral and (b) differentiating the
transverse slice integral `s ↦ ∫_{B_{θ(s)}} √(1-t²|z|²) dz`.  Fact (b) is the
fundamental theorem of calculus applied in the transverse variable, and is
proved here (`ballProfileIntegral_hasDerivAt`).  Consequently the flux identity
`FluxIdentity` is a *theorem* under mild regularity (`ProfileRegular`), and the
sharp inequality reduces to the value `ω_{m+1}/2` of the limiting entrance
integral `EntryFluxLimit` — i.e. the sphere-slicing/Beta identity
(`Cap.SphereSlicingTarget` in `Checks.lean`) — together with `θ(0) ≥ 0`.

## Status

* **Proved:** `slog`/`Xfield` elementary identities; the transverse FTC
  `ballProfileIntegral_hasDerivAt`; the flux identity
  `fluxIdentity_of_profileRegular`; the pointwise Cauchy–Schwarz bounds
  `lateralFlux_le_lateralArea`, `terminalFlux_le_terminalArea`; the t↑1 reduction
  `sharp_of_sliced_inequality`; the defect identity
  `defectIdentity_of_entryFlux`.
  `sharp_of_sliced_inequality`; the defect identity
  `defectIdentity_of_entryFlux`; and `profileRegular_flat`, a concrete instance
  of the regularity hypothesis.
* **Not proved (explicit targets):** `EntryFluxValueTarget`/`EntryFluxLimit`
  (the manuscript's sphere-slicing/Beta identity; compare
  `Cap.SphereSlicingTarget` in `Checks.lean`); the geometric identification of
  the explicit functionals with `ℋ^m(Γ)`/`|C|` (`Cap.HausdorffIntegralBridge`);
  the equality-characterisation `EqualityCharacterization`; and
  `DefectCharacterization` (nonnegativity of the defect and the profile ODE).
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps
namespace Cap

noncomputable section

/-! ## The calibrating vector field -/

/-- `slog t r = √(1 - t² r²)`, the axial component of the calibrating vector
field at transverse radius `r`.  (Clamped at `0` by `Real.sqrt`.) -/
def slog (t r : ℝ) : ℝ := Real.sqrt (1 - t ^ 2 * r ^ 2)

theorem slog_nonneg (t r : ℝ) : 0 ≤ slog t r := Real.sqrt_nonneg _

theorem slog_sq {t r : ℝ} (h : 0 ≤ 1 - t ^ 2 * r ^ 2) :
    (slog t r) ^ 2 = 1 - t ^ 2 * r ^ 2 := Real.sq_sqrt h

theorem slog_le_one (t r : ℝ) : slog t r ≤ 1 := by
  rw [slog, Real.sqrt_le_one]
  have : 0 ≤ t ^ 2 * r ^ 2 := by positivity
  linarith

theorem continuous_slog (t : ℝ) : Continuous (slog t) := by
  unfold slog; fun_prop

/-- Euclidean squared norm on `ℝ × ℝ^m` (the product norm is the sup norm, so we
use the Euclidean norm explicitly). -/
def euclidSq {m : ℕ} (p : CapSpace m) : ℝ := p.1 ^ 2 + ‖p.2‖ ^ 2

/-- The calibrating vector field `X_t(s,z) = (√(1-t²|z|²), t z)`. -/
def Xfield (m : ℕ) (t : ℝ) (p : CapSpace m) : CapSpace m :=
  (slog t ‖p.2‖, t • p.2)

theorem euclidSq_Xfield (m : ℕ) (t : ℝ) (p : CapSpace m) :
    euclidSq (Xfield m t p) = (slog t ‖p.2‖) ^ 2 + t ^ 2 * ‖p.2‖ ^ 2 := by
  rw [euclidSq, Xfield]
  simp only [norm_smul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]

/-- `|X_t|² = 1` at every point where `t²|z|² ≤ 1`. -/
theorem euclidSq_Xfield_eq_one {m : ℕ} {t : ℝ} {p : CapSpace m}
    (h : 0 ≤ 1 - t ^ 2 * ‖p.2‖ ^ 2) : euclidSq (Xfield m t p) = 1 := by
  rw [euclidSq_Xfield]
  have : (slog t ‖p.2‖) ^ 2 = 1 - t ^ 2 * ‖p.2‖ ^ 2 := slog_sq h
  rw [this]; ring

/-- The limiting vector field `X(s,z) = (√(1-|z|²), z)` (the manuscript's `X`). -/
def Xlim (m : ℕ) (p : CapSpace m) : CapSpace m :=
  (Real.sqrt (1 - ‖p.2‖ ^ 2), p.2)

theorem Xfield_one_eq_Xlim (m : ℕ) (p : CapSpace m) :
    Xfield m 1 p = Xlim m p := by
  simp only [Xfield, Xlim, slog]
  norm_num

/-! ## Transverse slice integrals

`ballProfileIntegral m t r = ∫_0^r u^{m-1} √(1-t²u²) du` is the primitive whose
value at `r = θ(s)` is `1/(m ω_m)` times the slice integral
`∫_{B_{θ(s)}} √(1-t²|z|²) dz` (polar coordinates). -/

/-- Transverse slice primitive. -/
def ballProfileIntegral (m : ℕ) (t r : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..r, u ^ (m - 1) * slog t u

theorem continuous_ballIntegrand (m : ℕ) (t : ℝ) :
    Continuous (fun u : ℝ => u ^ (m - 1) * slog t u) := by
  have : Continuous (fun u : ℝ => u ^ (m - 1)) := by fun_prop
  exact this.mul (continuous_slog t)

/-- **Fundamental theorem of calculus in the transverse variable**: the slice
primitive has derivative `r^{m-1} √(1-t²r²)` at every `r`. -/
theorem ballProfileIntegral_hasDerivAt (m : ℕ) (t r : ℝ) :
    HasDerivAt (ballProfileIntegral m t) (r ^ (m - 1) * slog t r) r :=
  ((continuous_ballIntegrand m t).integral_hasStrictDerivAt 0 r).hasDerivAt

/-! ## Explicit fluxes and the flux identity -/

/-- The flux of `X_t` through the lateral boundary, written as the explicit
`s`-integral obtained from the parametrisation `z = θ(s) ξ`, `|ξ| = 1`
(`∫_{S^{m-1}} dσ = m ω_m`). -/
def lateralFlux (C : Cap m) (t : ℝ) : ℝ :=
  (m : ℝ) * omega m *
    ∫ s in (-C.K)..0,
      (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)

/-- The flux of `X_t` through the terminal disk at `s = 0`, as a transverse
slice integral. -/
def terminalFlux (C : Cap m) (t : ℝ) : ℝ :=
  (m : ℝ) * omega m * ballProfileIntegral m t (C.θ 0)

/-- The flux of `X_t` through the entrance disk `Σ = {-K} × B_m(1)` (towards the
interior, i.e. the manuscript's subtracted integral). -/
def entryFlux (_C : Cap m) (t : ℝ) : ℝ :=
  (m : ℝ) * omega m * ballProfileIntegral m t 1

/-- **Flux identity** for the explicit revolution functional: for every `t`,
`m t |C| = (lateral flux) + (terminal flux) − (entrance flux)`.
Proved as `fluxIdentity_of_profileRegular`. -/
def FluxIdentity (C : Cap m) : Prop :=
  ∀ t : ℝ, (m : ℝ) * t * C.revolutionVolume
    = C.lateralFlux t + C.terminalFlux t - C.entryFlux t

/-- Regularity of the profile needed for the one-dimensional FTC argument:
continuity on the closed axial interval, the entrance value `1`, a derivative on
the open interval, and continuity of that derivative. -/
def ProfileRegular (C : Cap m) : Prop :=
  ContinuousOn C.θ (Set.Icc (-C.K) 0) ∧
  C.θ (-C.K) = 1 ∧
  (∀ s ∈ Set.Ioo (-C.K) 0, HasDerivAt C.θ (deriv C.θ s) s) ∧
  ContinuousOn (fun s => deriv C.θ s) (Set.Icc (-C.K) 0)

/-! ## Proof of the flux identity -/

/-- **The flux identity, proved.**  Under profile regularity (continuity on the
closed interval, entrance value `1`, and a continuous derivative) the explicit
revolution functional satisfies
`m t |C| = (lateral flux) + (terminal flux) − (entrance flux)` for every `t`.

The proof differentiates the transverse slice integral
`s ↦ ∫_0^{θ(s)} u^{m-1}√(1-t²u²) du` (FTC in the transverse variable,
`ballProfileIntegral_hasDerivAt`) and applies the FTC in `s`; the resulting
boundary term is exactly the difference between the terminal and entrance
fluxes.  No curved divergence theorem and no surface measure are used. -/
theorem fluxIdentity_of_profileRegular (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hreg : ProfileRegular C) : FluxIdentity C := by
  obtain ⟨hθcont, hθK, hθderiv, hθ'cont⟩ := hreg
  intro t
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have huIcc : Set.uIcc (-C.K) 0 = Set.Icc (-C.K) 0 := Set.uIcc_of_le hKle
  have hcont_bp : Continuous (ballProfileIntegral m t) :=
    intervalIntegral.continuous_primitive
      (fun a b => (continuous_ballIntegrand m t).intervalIntegrable a b) 0
  -- continuity of the two integrands
  have hfcont : ContinuousOn
      (fun s => (C.θ s) ^ (m - 1) *
        (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)) (Set.Icc (-C.K) 0) := by
    apply ContinuousOn.mul (hθcont.pow _)
    apply ContinuousOn.add
    · exact (hθ'cont.neg).mul
        ((continuous_slog t).continuousOn.comp hθcont (fun x _ => Set.mem_univ (C.θ x)))
    · exact continuousOn_const.mul hθcont
  have hgcont : ContinuousOn
      (fun s => (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s)
      (Set.Icc (-C.K) 0) := by
    apply ContinuousOn.mul
    · exact (hθcont.pow _).mul
        ((continuous_slog t).continuousOn.comp hθcont (fun x _ => Set.mem_univ (C.θ x)))
    · exact hθ'cont
  have hfint : IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) *
        (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)) volume (-C.K) 0 := by
    have h : ContinuousOn
        (fun s => (C.θ s) ^ (m - 1) *
          (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s))
        (Set.uIcc (-C.K) 0) := by rw [huIcc]; exact hfcont
    exact h.intervalIntegrable
  have hgint : IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s)
      volume (-C.K) 0 := by
    have h : ContinuousOn
        (fun s => (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s)
        (Set.uIcc (-C.K) 0) := by rw [huIcc]; exact hgcont
    exact h.intervalIntegrable
  -- chain rule and FTC in `s`
  have hFderiv : ∀ s ∈ Set.Ioo (-C.K) 0,
      HasDerivAt (fun s => ballProfileIntegral m t (C.θ s))
        ((C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s) s := by
    intro s hs
    have h := (ballProfileIntegral_hasDerivAt m t (C.θ s)).comp s (hθderiv s hs)
    simpa only [Function.comp_apply] using h
  have hcontF : ContinuousOn (fun s => ballProfileIntegral m t (C.θ s))
      (Set.Icc (-C.K) 0) :=
    hcont_bp.continuousOn.comp hθcont (fun x _ => Set.mem_univ (C.θ x))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hKle hcontF
    (fun x hx => hFderiv x hx) hgint
  have hFTC' : ballProfileIntegral m t (C.θ 0) - ballProfileIntegral m t 1
      = ∫ s in (-C.K)..0, (C.θ s) ^ (m - 1) * slog t (C.θ s) * deriv C.θ s := by
    have h := hFTC
    simp only [hθK] at h
    exact h.symm
  -- pointwise algebra: `f + g = t θ^m`
  have hpoint : ∀ s ∈ Set.Icc (-C.K) 0,
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
      have hsIcc : s ∈ Set.Icc (-C.K) 0 := by
        rw [Set.uIcc_of_le hKle] at hs
        exact hs
      exact hpoint s hsIcc
    rw [hcongr, intervalIntegral.integral_const_mul]
  have hkey : (∫ s in (-C.K)..0,
          (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s))
        + (ballProfileIntegral m t (C.θ 0) - ballProfileIntegral m t 1)
      = t * ∫ s in (-C.K)..0, (C.θ s) ^ m := by
    rw [hFTC', hsum]
  -- assemble the fluxes
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

/-- The lateral flux integrand is dominated by the lateral area integrand: this
is the two-dimensional Cauchy–Schwarz inequality
`(-θ',1)·(√(1-t²θ²), tθ) ≤ |(-θ',1)| |(√(1-t²θ²), tθ)| = √(1+θ'²)`. -/
theorem lateralFlux_integrand_le_area_integrand (m : ℕ) (C : Cap m)
    {t s : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioo (-C.K) 0) :
    (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)
      ≤ (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hθpos : 0 < C.θ s := C.θ_pos s hs
  have hθle : C.θ s ≤ 1 := C.θ_le_one s hs
  have hpow : 0 ≤ (C.θ s) ^ (m - 1) := pow_nonneg (le_of_lt hθpos) _
  apply mul_le_mul_of_nonneg_left _ hpow
  have hs2 : (slog t (C.θ s)) ^ 2 = 1 - t ^ 2 * (C.θ s) ^ 2 := by
    apply slog_sq
    have htθ0 : 0 ≤ t * C.θ s := mul_nonneg (le_of_lt ht0) (le_of_lt hθpos)
    have htθ1 : t * C.θ s < 1 := by
      have hle : t * C.θ s ≤ t := by
        simpa using mul_le_mul_of_nonneg_left hθle (le_of_lt ht0)
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

/-- **Lateral bound.**  For `[0<t<1]` the lateral flux is at most the lateral
area, by the pointwise Cauchy–Schwarz bound. -/
theorem lateralFlux_le_lateralArea (m : ℕ) (C : Cap m) (hreg : ProfileRegular C)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    C.lateralFlux t ≤ C.lateralArea := by
  obtain ⟨hθcont, hθK, hθderiv, hθ'cont⟩ := hreg
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hIcc : Set.uIcc (-C.K) 0 = Set.Icc (-C.K) 0 := Set.uIcc_of_le hKle
  have hfcont : ContinuousOn
      (fun s => (C.θ s) ^ (m - 1) *
        (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)) (Set.Icc (-C.K) 0) := by
    apply ContinuousOn.mul (hθcont.pow _)
    apply ContinuousOn.add
    · exact (hθ'cont.neg).mul
        ((continuous_slog t).continuousOn.comp hθcont (fun x _ => Set.mem_univ (C.θ x)))
    · exact continuousOn_const.mul hθcont
  have hgcont : ContinuousOn
      (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
      (Set.Icc (-C.K) 0) := by
    apply ContinuousOn.mul (hθcont.pow _)
    apply ContinuousOn.sqrt
    exact continuousOn_const.add (hθ'cont.pow 2)
  have hfint : IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) *
        (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s)) volume (-C.K) 0 := by
    have h : ContinuousOn
        (fun s => (C.θ s) ^ (m - 1) *
          (-(deriv C.θ s) * slog t (C.θ s) + t * C.θ s))
        (Set.uIcc (-C.K) 0) := by rw [hIcc]; exact hfcont
    exact h.intervalIntegrable
  have hgint : IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
      volume (-C.K) 0 := by
    have h : ContinuousOn
        (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
        (Set.uIcc (-C.K) 0) := by rw [hIcc]; exact hgcont
    exact h.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hKle hfint hgint
    (fun s hs => lateralFlux_integrand_le_area_integrand m C ht hs)
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

/-- **Terminal bound.**  For `θ(0) ≥ 0` and `t ∈ (0,1)` the terminal flux is at
most `ω_m θ(0)^m`, the terminal disk area. -/
theorem terminalFlux_le_terminalArea (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (_hreg : ProfileRegular C)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hθ0 : 0 ≤ C.θ 0) :
    C.terminalFlux t ≤ C.terminalArea := by
  obtain ⟨ht0, ht1⟩ := ht
  have hfcont : ContinuousOn (fun r : ℝ => r ^ (m - 1) * slog t r)
      (Set.Icc (0:ℝ) (C.θ 0)) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.pow _
    · exact (continuous_slog t).continuousOn
  have hgcont : ContinuousOn (fun r : ℝ => r ^ (m - 1)) (Set.Icc (0:ℝ) (C.θ 0)) :=
    continuousOn_id.pow _
  have hpoint : ∀ r ∈ Set.Icc (0:ℝ) (C.θ 0), r ^ (m - 1) * slog t r ≤ r ^ (m - 1) := by
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

/-! ## The t↑1 reduction -/

/-- **Sliced-inequality reduction.**  If for every `t ∈ (0,1)` the entrance flux
is dominated by `|Γ| - m t |C|`, and if the entrance flux tends to `ω_{m+1}/2`
as `t↑1`, then the sharp inequality holds.  This is the manuscript's
`t↑1` step, separated from the geometric input. -/
theorem sharp_of_sliced_inequality (m : ℕ) (C : Cap m)
    (hineq : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      C.entryFlux t ≤ C.revolutionArea - (m : ℝ) * t * C.revolutionVolume)
    (hlim : Tendsto C.entryFlux (𝓝[<] (1 : ℝ)) (𝓝 (omega (m + 1) / 2))) :
    C.revolutionF ≥ omega (m + 1) / 2 := by
  have hcont : Tendsto (fun t : ℝ => C.revolutionArea - (m : ℝ) * t * C.revolutionVolume)
      (𝓝[<] (1 : ℝ))
      (𝓝 (C.revolutionArea - (m : ℝ) * 1 * C.revolutionVolume)) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_right inf_le_left
    exact tendsto_const_nhds.sub
      (((hid.const_mul (m : ℝ)).mul tendsto_const_nhds))
  have hev : C.entryFlux ≤ᶠ[𝓝[<] (1 : ℝ)]
      fun t : ℝ => C.revolutionArea - (m : ℝ) * t * C.revolutionVolume := by
    change ∀ᶠ t in 𝓝[<] (1 : ℝ),
      C.entryFlux t ≤ C.revolutionArea - (m : ℝ) * t * C.revolutionVolume
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (by norm_num : (0:ℝ) < 1)] with t ht0 ht1
    exact hineq t ⟨ht0, ht1⟩
  have hle := le_of_tendsto_of_tendsto hlim hcont hev
  have hF : C.revolutionF = C.revolutionArea - (m : ℝ) * C.revolutionVolume := rfl
  rw [hF]
  simpa using hle

/-- **Conditional sharp inequality for the explicit revolution functional.**
Under profile regularity, `θ(0) ≥ 0`, and the entrance-flux limit
(`EntryFluxLimit`), the explicit functional satisfies `𝓕 ≥ ω_{m+1}/2`.

Note: this is the *explicit* `revolutionF`; the identification with the
Hausdorff functional is the separate open bridge `Cap.HausdorffIntegralBridge`. -/
theorem sharp_revolutionF_of_regular (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hreg : ProfileRegular C) (hθ0 : 0 ≤ C.θ 0)
    (hlim : Tendsto C.entryFlux (𝓝[<] (1 : ℝ)) (𝓝 (omega (m + 1) / 2))) :
    C.revolutionF ≥ omega (m + 1) / 2 := by
  apply sharp_of_sliced_inequality m C _ hlim
  intro t ht
  have hflux := fluxIdentity_of_profileRegular m hm C hreg t
  have hlat := lateralFlux_le_lateralArea m C hreg ht
  have hterm := terminalFlux_le_terminalArea m hm C hreg ht hθ0
  rw [revolutionArea]
  linarith

/-! ## The defect identity

The manuscript's defect form of the sharp inequality,
`𝓕(C) - ω_{m+1}/2 = ∫_Γ (1 - X·ν) dH^m`, becomes an explicit one-dimensional
identity for the revolution functional.  On the lateral boundary the integrand is

`1 - X·ν = 1 - (-θ'√(1-θ²) + θ)/√(1+θ'²)`,

which after multiplying by the area element `θ^{m-1}√(1+θ'²)` gives
`θ^{m-1}(√(1+θ'²) + θ'√(1-θ²) - θ)`.  On the terminal disk the integrand is
`1 - √(1-|z|²)`.  The two explicit expressions below encode exactly this. -/

/-- Lateral part of the defect integral `∫_Γ (1 - X·ν) dH^m`. -/
def lateralDefect (C : Cap m) : ℝ :=
  (m : ℝ) * omega m *
    ∫ s in (-C.K)..0, (C.θ s) ^ (m - 1) *
      (Real.sqrt (1 + (deriv C.θ s) ^ 2)
        + (deriv C.θ s) * Real.sqrt (1 - (C.θ s) ^ 2) - C.θ s)

/-- Terminal-disk part of the defect integral `∫_Γ (1 - X·ν) dH^m`,
`ω_m θ(0)^m − ∫_{B_{θ(0)}} √(1-|z|²) dz`. -/
def terminalDefect (C : Cap m) : ℝ :=
  omega m * (C.θ 0) ^ m - (m : ℝ) * omega m * ballProfileIntegral m 1 (C.θ 0)

/-- **Defect identity** (manuscript `eq:defect-identity`) for the explicit
revolution functional.  This is *not* asserted as an unconditional theorem here;
it is proved conditionally in `defectIdentity_of_entryFlux`. -/
def DefectIdentity (C : Cap m) : Prop :=
  C.revolutionF - omega (m + 1) / 2 = C.lateralDefect + C.terminalDefect

theorem lateralArea_sub_lateralFlux_one (m : ℕ) (C : Cap m) (hreg : ProfileRegular C) :
    C.lateralArea - C.lateralFlux 1 = C.lateralDefect := by
  obtain ⟨hθcont, hθK, hθderiv, hθ'cont⟩ := hreg
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hIcc : Set.uIcc (-C.K) 0 = Set.Icc (-C.K) 0 := Set.uIcc_of_le hKle
  have hAcont : ContinuousOn
      (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
      (Set.Icc (-C.K) 0) := by
    apply ContinuousOn.mul (hθcont.pow _)
    apply ContinuousOn.sqrt
    exact continuousOn_const.add (hθ'cont.pow 2)
  have hFcont : ContinuousOn
      (fun s => (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog 1 (C.θ s) + 1 * C.θ s))
      (Set.Icc (-C.K) 0) := by
    apply ContinuousOn.mul (hθcont.pow _)
    apply ContinuousOn.add
    · exact (hθ'cont.neg).mul
        ((continuous_slog 1).continuousOn.comp hθcont (fun x _ => Set.mem_univ (C.θ x)))
    · exact continuousOn_const.mul hθcont
  have hA : IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
      volume (-C.K) 0 := by
    have h : ContinuousOn
        (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
        (Set.uIcc (-C.K) 0) := by rw [hIcc]; exact hAcont
    exact h.intervalIntegrable
  have hF : IntervalIntegrable
      (fun s => (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog 1 (C.θ s) + 1 * C.θ s))
      volume (-C.K) 0 := by
    have h : ContinuousOn
        (fun s => (C.θ s) ^ (m - 1) * (-(deriv C.θ s) * slog 1 (C.θ s) + 1 * C.θ s))
        (Set.uIcc (-C.K) 0) := by rw [hIcc]; exact hFcont
    exact h.intervalIntegrable
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

theorem terminalArea_sub_terminalFlux_one (m : ℕ) (C : Cap m) :
    C.terminalArea - C.terminalFlux 1 = C.terminalDefect := by
  simp only [terminalArea, terminalFlux, terminalDefect, ballProfileIntegral, slog,
    one_pow, one_mul]

/-- **Defect identity, proved** from the flux identity at `t = 1` and the value
`entryFlux 1 = ω_{m+1}/2` of the entrance integral. -/
theorem defectIdentity_of_entryFlux (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hreg : ProfileRegular C) (hlim1 : C.entryFlux 1 = omega (m + 1) / 2) :
    DefectIdentity C := by
  have hflux := fluxIdentity_of_profileRegular m hm C hreg 1
  have hV : (m : ℝ) * C.revolutionVolume
      = C.lateralFlux 1 + C.terminalFlux 1 - C.entryFlux 1 := by
    simpa using hflux
  have hlat := lateralArea_sub_lateralFlux_one m C hreg
  have hterm := terminalArea_sub_terminalFlux_one m C
  unfold DefectIdentity
  rw [show C.revolutionF = C.revolutionArea - (m : ℝ) * C.revolutionVolume from rfl,
    show C.revolutionArea = C.lateralArea + C.terminalArea from rfl, hV]
  linarith [hlat, hterm, hlim1]

/-! ## Explicit remaining targets and equality characterisation -/

/-- **Auxiliary target** (a `Prop`; not a hypothesis of any headline theorem).  The limiting entrance integral equals
`ω_{m+1}/2`, equivalently `∫_{B_m(1)} √(1-|z|²) dz = ω_{m+1}/2` or
`m ω_m ∫_0^1 r^{m-1}√(1-r²) dr = ω_{m+1}/2`.  This is the sphere-slicing /
Beta-integral identity (`Cap.SphereSlicingTarget` in `Checks.lean`); mathlib has
the complex Beta integral but not the packaged real change of variables. -/
def EntryFluxValueTarget (m : ℕ) : Prop :=
  (m : ℝ) * omega m * ballProfileIntegral m 1 1 = omega (m + 1) / 2

/-- **Auxiliary target** (a `Prop`; not a hypothesis of any headline theorem).  The entrance flux converges to `ω_{m+1}/2`
as `t↑1`. -/
def EntryFluxLimit (m : ℕ) : Prop :=
  ∀ C : Cap m, Tendsto C.entryFlux (𝓝[<] (1 : ℝ)) (𝓝 (omega (m + 1) / 2))

/-- The profile ODE `θ' = -√(1-θ²)/θ` characterising the equality case
(manuscript `eq:equality-ode`). -/
def EqualityODE (C : Cap m) : Prop :=
  ∀ s ∈ Set.Ioo (-C.K) 0,
    deriv C.θ s = -(Real.sqrt (1 - (C.θ s) ^ 2)) / C.θ s

/-- The equality profile (manuscript `eq:equality-profile`): a straight unit
cylinder followed by a unit semicircle. -/
def EqualityProfile (C : Cap m) : Prop :=
  1 ≤ C.K ∧
  (∀ s ∈ Set.Ioo (-C.K) (-1), C.θ s = 1) ∧
  (∀ s ∈ Set.Ioo (-1) 0, C.θ s = Real.sqrt (1 - (s + 1) ^ 2))

/-- **Explicit target** (proved: `Cap.equalityCharacterization_uc` in
`RobinCaps/Cap/Unconditional.lean`).  Equality in the sharp inequality holds
exactly for the hemisphere optionally extended by a straight cylinder. -/
def EqualityCharacterization (m : ℕ) : Prop :=
  ∀ C : Cap m, C.revolutionF = omega (m + 1) / 2 ↔ EqualityProfile C

/-- **Auxiliary target** (a `Prop`; not a hypothesis of any headline theorem).  The defect is nonnegative and equality
forces the profile ODE.  This is the analytic content of the manuscript's
equality argument (`1-X·ν ≥ 0` and `ν = X` a.e.). -/
def DefectCharacterization (m : ℕ) : Prop :=
  ∀ C : Cap m, 0 ≤ C.lateralDefect + C.terminalDefect
    ∧ (C.lateralDefect + C.terminalDefect = 0 → EqualityODE C)

/-- **Auxiliary target** (a `Prop`; not a hypothesis of any headline theorem).  The profile ODE, together with the cap
monotonicity `θ ≤ 1` and the terminal condition, forces the hemisphere profile.
This is the ODE integration step `h = √(1-θ²)`, `h' = 1` of the manuscript. -/
def EqualityODE_to_Profile (m : ℕ) : Prop :=
  ∀ C : Cap m, EqualityODE C → EqualityProfile C

/-! ## A concrete instance of the regularity hypothesis -/

/-- The flat cap `θ ≡ 1` satisfies `ProfileRegular`, showing the regularity
hypothesis of the flux identity is satisfiable (and non-vacuous). -/
theorem profileRegular_flat (m : ℕ) (K : ℝ) (hK : 0 < K) :
    ProfileRegular (flat m K hK) := by
  refine ⟨continuousOn_const, by simp [flat], ?_, ?_⟩
  · intro s hs
    rw [show deriv (flat m K hK).θ s = 0 by simp [flat]]
    exact hasDerivAt_const s 1
  · have h : (fun s => deriv (flat m K hK).θ s) = fun _ : ℝ => (0 : ℝ) := by
      funext s; simp [flat]
    rw [h]
    exact continuousOn_const

/-- The flux identity holds for every flat cap. -/
theorem fluxIdentity_flat (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) :
    FluxIdentity (flat m K hK) :=
  fluxIdentity_of_profileRegular m hm (flat m K hK) (profileRegular_flat m K hK)

end

end Cap
end RobinCaps
