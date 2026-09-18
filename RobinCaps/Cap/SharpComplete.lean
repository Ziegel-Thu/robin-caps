import Mathlib
import RobinCaps.Cap.Sphere
import RobinCaps.Cap.SharpInequality

/-!
# Closing the cap-flux targets

This file discharges the remaining explicit targets of
`RobinCaps.Cap.SharpInequality` for the **explicit revolution functional**:

* `entryFluxValueTarget` proves `EntryFluxValueTarget m` for every `m ≥ 1`, i.e.
  `m ω_m ∫_0^1 r^{m-1} √(1-r²) dr = ω_{m+1}/2`.
  The proof is elementary: the substitution `r = sin θ` turns the integral into
  `∫_0^{π/2} sin^{m-1}θ cos²θ dθ = sinSlice (m-1) - sinSlice (m+1)`, while the
  already-proved sphere-slicing identity `sphereSlicingTarget` identifies
  `sphereSlice m = sinSlice (m+1)`; the classical sine-power reduction
  (`integral_sin_pow`) gives the recurrence `(m+1) sinSlice (m+1) = m sinSlice (m-1)`.
  No Beta-integral packaging is used.

* `entryFluxLimit` upgrades the value at `t = 1` to the limit `t ↑ 1`, using
  continuity of the transverse slice integral in `t`
  (`continuous_parametric_intervalIntegral_of_continuous'`).

* `sharp_revolutionF_of_regular_uncond` is the **unconditional** sharp inequality
  `𝓕(C) ≥ ω_{m+1}/2` for `ProfileRegular` caps with `θ(0) ≥ 0`.

* `defectIdentity_of_regular` derives the defect identity
  `𝓕(C) - ω_{m+1}/2 = lateralDefect + terminalDefect` unconditionally.

The equality characterisation and the Hausdorff/area bridge remain separate
targets, recorded explicitly at the end:

* the **converse** half of the equality classification is proved away from the
  junction `s = -1` (`equalityProfile_equalityODE`), together with the direct
  fact that the unit semicircle solves the ODE (`hemiProfile_equalityODE`); the
  forward ODE-integration direction is the explicit target
  `EqualityODE_terminal_hemisphere`;
* the Hausdorff/area bridge for the flat cap is the explicit target
  (removed: `Cap.F` is now defined as `revolutionF`). -/

open MeasureTheory Set Filter intervalIntegral
open scoped Topology Interval

namespace RobinCaps
namespace Cap

noncomputable section

/-! ## The sine slice integral

`sinSlice m = ∫_0^{π/2} sin^m θ dθ` is the exact shape obtained from
`sphereSlice m = ∫_{-1}^0 (1-s²)^{m/2} ds` by the substitution `s = sin θ`. -/

/-- `sinSlice m = ∫_0^{π/2} sin θ ^ m dθ`. -/
noncomputable def sinSlice (m : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ m

/-- The classical sine-power reduction:
`sinSlice (n+2) = (n+1)/(n+2) · sinSlice n`. -/
theorem sinSlice_rec (n : ℕ) :
    sinSlice (n + 2) = ((n : ℝ) + 1) / ((n : ℝ) + 2) * sinSlice n := by
  unfold sinSlice
  have h := integral_sin_pow (a := (0 : ℝ)) (b := Real.pi / 2) (n := n)
  rw [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  have hb : (0 : ℝ) ^ (n + 1) * 1 - 1 ^ (n + 1) * 0 = 0 := by simp
  rw [hb, zero_div, zero_add] at h
  exact h

/-- The reflection `θ ↦ π/2 - θ` identifies the cosine and sine slice integrals:
`sphereSlice m = sinSlice (m+1)`. -/
theorem sphereSlice_eq_sinSlice (m : ℕ) : sphereSlice m = sinSlice (m + 1) := by
  rw [sphereSlice_eq_cos, sinSlice]
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
    (d := Real.pi / 2) (f := fun x => Real.cos x ^ (m + 1))
  rw [sub_zero, sub_self] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [Real.cos_pi_div_two_sub]

/-- The recurrence in the form used below: for `m ≥ 1`,
`(m+1) sinSlice (m+1) = m sinSlice (m-1)`. -/
theorem sinSlice_rec' (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * sinSlice (m + 1) = (m : ℝ) * sinSlice (m - 1) := by
  have hrec := sinSlice_rec (m - 1)
  rw [show m - 1 + 2 = m + 1 by omega] at hrec
  have hc1 : (((m - 1 : ℕ)) : ℝ) + 1 = (m : ℝ) := by
    rw [Nat.cast_sub hm]; ring
  have hc2 : (((m - 1 : ℕ)) : ℝ) + 2 = (m : ℝ) + 1 := by
    rw [Nat.cast_sub hm]; ring
  have hrec' : sinSlice (m + 1) = (m : ℝ) / ((m : ℝ) + 1) * sinSlice (m - 1) := by
    rw [hrec, hc1, hc2]
  rw [hrec']
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## The entrance integral at `t = 1` -/

/-- The substitution `r = sin θ` for the transverse primitive at `t = 1`:
`∫_0^1 r^{m-1}√(1-r²) dr = sinSlice (m-1) - sinSlice (m+1)`. -/
theorem ballProfileIntegral_one_eq (m : ℕ) (hm : 1 ≤ m) :
    ballProfileIntegral m 1 1 = sinSlice (m - 1) - sinSlice (m + 1) := by
  have hg : Continuous (fun u : ℝ => u ^ (m - 1) * Real.sqrt (1 - u ^ 2)) := by
    exact (continuous_id.pow _).mul (Real.continuous_sqrt.comp (by fun_prop))
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := Real.sin) (f' := Real.cos)
    (g := fun u => u ^ (m - 1) * Real.sqrt (1 - u ^ 2))
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn hg
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [ballProfileIntegral]
  simp only [slog, one_pow, one_mul]
  rw [← hsub]
  rw [sinSlice, sinSlice]
  rw [← intervalIntegral.integral_sub
    ((Real.continuous_sin.pow _).intervalIntegrable _ _)
    ((Real.continuous_sin.pow _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    rwa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hx
  have hcos0 : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx'.1], hx'.2⟩
  have hcs : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    have := Real.sin_sq x
    linarith
  have hsqrt : Real.sqrt (1 - Real.sin x ^ 2) = Real.cos x := by
    rw [← hcs, Real.sqrt_sq_eq_abs, abs_of_nonneg hcos0]
  have hpow : Real.sin x ^ (m - 1) * Real.sin x ^ 2 = Real.sin x ^ (m + 1) := by
    rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
  calc (Real.sin x) ^ (m - 1) * Real.sqrt (1 - Real.sin x ^ 2) * Real.cos x
      = Real.sin x ^ (m - 1) * (Real.cos x * Real.cos x) := by rw [hsqrt]; ring
    _ = Real.sin x ^ (m - 1) * (1 - Real.sin x ^ 2) := by
        rw [show Real.cos x * Real.cos x = Real.cos x ^ 2 by ring, hcs]
    _ = Real.sin x ^ (m - 1) - Real.sin x ^ (m + 1) := by
        rw [mul_sub, mul_one, hpow]

/-- **Item 1.**  `EntryFluxValueTarget m` holds for every `m ≥ 1`:
`m ω_m ∫_0^1 r^{m-1}√(1-r²) dr = ω_{m+1}/2`. -/
theorem entryFluxValueTarget (m : ℕ) (hm : 1 ≤ m) : EntryFluxValueTarget m := by
  have hJ := ballProfileIntegral_one_eq m hm
  have hslice := sphereSlice_eq_sinSlice m
  have hrec := sinSlice_rec' m hm
  have hkey : (m : ℝ) * ballProfileIntegral m 1 1 = sphereSlice m := by
    rw [hJ, hslice]
    have hs : (m : ℝ) * sinSlice (m - 1) = ((m : ℝ) + 1) * sinSlice (m + 1) := hrec.symm
    nlinarith [hs]
  unfold EntryFluxValueTarget
  rw [show (m : ℝ) * omega m * ballProfileIntegral m 1 1
      = omega m * ((m : ℝ) * ballProfileIntegral m 1 1) by ring, hkey]
  have hs := sphereSlicingTarget m
  unfold SphereSlicingTarget at hs
  rw [hs]
  ring

/-! ## The entrance-flux limit -/

/-- The transverse slice integral is continuous in the parameter `t`. -/
theorem continuous_ballProfileIntegral (m : ℕ) :
    Continuous (fun t : ℝ => ballProfileIntegral m t 1) := by
  have hf : Continuous (Function.uncurry (fun t u : ℝ => u ^ (m - 1) * slog t u)) := by
    have hcont : Continuous
        (fun p : ℝ × ℝ => p.2 ^ (m - 1) * Real.sqrt (1 - p.1 ^ 2 * p.2 ^ 2)) := by
      fun_prop
    simpa only [Function.uncurry, slog] using hcont
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun t u : ℝ => u ^ (m - 1) * slog t u) hf 0 1
  simpa only [ballProfileIntegral] using h

/-- **Item 2 (limit).**  `EntryFluxLimit m` holds for `m ≥ 1`: the entrance flux
tends to `ω_{m+1}/2` as `t ↑ 1`. -/
theorem entryFluxLimit (m : ℕ) (hm : 1 ≤ m) : EntryFluxLimit m := by
  intro C
  have hcont := continuous_ballProfileIntegral m
  have htend : Tendsto (fun t : ℝ => ballProfileIntegral m t 1) (𝓝[<] (1 : ℝ))
      (𝓝 (ballProfileIntegral m 1 1)) :=
    hcont.continuousAt.tendsto.mono_left inf_le_left
  have hval := entryFluxValueTarget m hm
  have hgoal : Tendsto (fun t : ℝ => (m : ℝ) * omega m * ballProfileIntegral m t 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (omega (m + 1) / 2)) := by
    rw [← hval]
    exact htend.const_mul ((m : ℝ) * omega m)
  simpa only [entryFlux] using hgoal

/-! ## The unconditional sharp inequality -/

/-- **Item 2.**  Unconditional sharp inequality for the explicit revolution
functional: every `ProfileRegular` admissible cap with `θ(0) ≥ 0` satisfies
`𝓕(C) ≥ ω_{m+1}/2`.  The `Tendsto` hypothesis of
`sharp_revolutionF_of_regular` is discharged by `entryFluxLimit`. -/
theorem sharp_revolutionF_of_regular_uncond (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hreg : ProfileRegular C) (hθ0 : 0 ≤ C.θ 0) :
    C.revolutionF ≥ omega (m + 1) / 2 :=
  sharp_revolutionF_of_regular m hm C hreg hθ0 (entryFluxLimit m hm C)

/-! ## The unconditional defect identity -/

/-- **Item 3.**  Unconditional defect identity for the explicit revolution
functional: `𝓕(C) - ω_{m+1}/2 = lateralDefect + terminalDefect`. -/
theorem defectIdentity_of_regular (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hreg : ProfileRegular C) : DefectIdentity C :=
  defectIdentity_of_entryFlux m hm C hreg
    (by simpa only [entryFlux] using entryFluxValueTarget m hm)

/-! ## Item 4: the equality profile satisfies the equality ODE

The *converse* half of the equality classification is elementary: the profile of
`EqualityProfile` (a straight cylinder followed by the unit semicircle) satisfies
the ODE `θ' = -√(1-θ²)/θ` at every interior point except the single junction
`s = -1`.  The junction genuinely cannot be included: `EqualityProfile` prescribes
`θ` only on the two open intervals `Ioo (-K) (-1)` and `Ioo (-1) 0`, so the value
`θ(-1)` is completely unconstrained, and `deriv C.θ (-1)` may depend on it.  We
therefore state the converse on `s ≠ -1`, which is the exact content of the
piecewise profile.

The forward direction (ODE ⇒ hemisphere on the terminal interval) is the missing
ODE-integration step and is recorded as the explicit target
`EqualityODE_terminal_hemisphere`.  Note that the *unconditional*
`EqualityODE_to_Profile` is false: a spherical cap of radius `< 1` satisfies the
ODE but has `K < 1`. -/

/-- The unit semicircle `s ↦ √(1-(s+1)²)` satisfies the equality ODE on `(-1,0)`. -/
theorem hemiProfile_equalityODE {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    deriv (fun t : ℝ => Real.sqrt (1 - (t + 1) ^ 2)) s
      = -(Real.sqrt (1 - (Real.sqrt (1 - (s + 1) ^ 2)) ^ 2))
          / (Real.sqrt (1 - (s + 1) ^ 2)) := by
  have hpos : 0 < 1 - (s + 1) ^ 2 := by nlinarith [hs.1, hs.2]
  have hfun : (fun t : ℝ => Real.sqrt (1 - (t + 1) ^ 2)) = semi 1 := by
    funext t; rfl
  have hder : deriv (fun t : ℝ => Real.sqrt (1 - (t + 1) ^ 2)) s = semiD 1 s := by
    rw [hfun]; exact deriv_semi 1 hpos
  rw [hder]
  have hsq : (Real.sqrt (1 - (s + 1) ^ 2)) ^ 2 = 1 - (s + 1) ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  have hspos : 0 < s + 1 := by linarith [hs.1]
  have hinner : 1 - (Real.sqrt (1 - (s + 1) ^ 2)) ^ 2 = (s + 1) ^ 2 := by
    rw [hsq]; ring
  rw [hinner, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hspos)]
  simp only [semiD, div_eq_mul_inv]

/-- **Item 4 (converse).**  The equality profile satisfies the equality ODE away
from the junction `s = -1`. -/
theorem equalityProfile_equalityODE (m : ℕ) (C : Cap m) (h : EqualityProfile C) :
    ∀ s ∈ Set.Ioo (-C.K) 0, s ≠ -1 →
      deriv C.θ s = -(Real.sqrt (1 - (C.θ s) ^ 2)) / C.θ s := by
  obtain ⟨_hK1, hleft, hright⟩ := h
  intro s hs hsne
  rcases lt_or_gt_of_ne hsne with hlt | hgt
  · -- `s < -1`: the profile is locally constant `1`.
    have hsleft : s ∈ Set.Ioo (-C.K) (-1 : ℝ) := ⟨hs.1, hlt⟩
    have hev : C.θ =ᶠ[𝓝 s] (fun _ : ℝ => (1 : ℝ)) :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hsleft) (fun y hy => hleft y hy)
    have hder : deriv C.θ s = deriv (fun _ : ℝ => (1 : ℝ)) s := hev.deriv_eq
    rw [hder]
    have hθs : C.θ s = 1 := hleft s hsleft
    rw [hθs]
    simp
  · -- `-1 < s`: the profile is locally the unit semicircle.
    have hsright : s ∈ Set.Ioo (-1 : ℝ) 0 := ⟨hgt, hs.2⟩
    have hev : C.θ =ᶠ[𝓝 s] semi 1 :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hsright) (fun y hy => hright y hy)
    have hder : deriv C.θ s = deriv (semi 1) s := hev.deriv_eq
    have hpos : 0 < 1 - (s + 1) ^ 2 := by nlinarith [hsright.1, hsright.2]
    rw [hder, deriv_semi 1 hpos]
    have hθs : C.θ s = Real.sqrt (1 - (s + 1) ^ 2) := hright s hsright
    rw [hθs]
    have hsq : (Real.sqrt (1 - (s + 1) ^ 2)) ^ 2 = 1 - (s + 1) ^ 2 :=
      Real.sq_sqrt (le_of_lt hpos)
    have hspos : 0 < s + 1 := by linarith [hsright.1]
    have hinner : 1 - (Real.sqrt (1 - (s + 1) ^ 2)) ^ 2 = (s + 1) ^ 2 := by
      rw [hsq]; ring
    rw [hinner, Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hspos)]
    simp only [semiD, div_eq_mul_inv]

/-- **Auxiliary target** (a `Prop`; not a hypothesis of any headline theorem).  The forward ODE-integration direction: under
the ODE and the terminal condition `θ(0) = 0`, the profile is the unit hemisphere
on the terminal interval.  Without `θ(0) = 0` this is false (e.g. a spherical cap
of radius `< 1`). -/
def EqualityODE_terminal_hemisphere (m : ℕ) : Prop :=
  ∀ C : Cap m, EqualityODE C → C.θ 0 = 0 →
    ∀ s ∈ Set.Ioo (-1 : ℝ) 0, C.θ s = Real.sqrt (1 - (s + 1) ^ 2)

end

end Cap
end RobinCaps
