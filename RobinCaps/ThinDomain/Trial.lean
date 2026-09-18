import Mathlib
import RobinCaps.ThinDomain.Piecewise
import RobinCaps.ThinDomain.Tensor
import RobinCaps.ThinDomain.Rescale
import RobinCaps.ThinDomain.Boundary
import RobinCaps.Domain.Thin

/-!
# U-TRIAL: the trial functions `𝒯_R F` of the upper bound (`eq:trial-extension`)

This file formalizes the trial functions of the manuscript
`reference/robin_endcaps_corrected_en.tex`, `sec:proof`, subsection *"Upper bound uniformly on
the entire low-dimensional trial space"* (lines 795–815).  The manuscript defines, for
`F ∈ W_{j,R}` (a span of interval eigenfunctions on `I_R = (x₋, x₊)`),

```
 (\mathcal T_RF)(x,y)=
 \begin{cases}
 F(x_-)\psi_R(y),&a<x<x_-,\\
 F(x)\psi_R(y),&x_-<x<x_+,\\
 F(x_+)\psi_R(y),&x_+<x<b.
 \end{cases}                                               (eq:trial-extension)
```

with `a = -L/2`, `b = L/2`, `x₋ = -L/2 + K₋R`, `x₊ = L/2 - K₊R`, and

> This is well-defined because every cap cross-section is contained in `B_m(R)`.

That last sentence is exactly what makes the Lean formalization painless: the *same* transverse
factor `ψ_R` is used on the caps and on the bulk, and no cap-dependent auxiliary lifting occurs
in `eq:trial-extension`.  (The lifting `g_σ` of `lem:cap-upper` is *not* part of the trial
function; it is the tool used to *estimate* the cap contributions, which is why the cap
estimates are recorded here as targets in the last section.)  So

`𝒯_R F (x, z) = F(clamp_{[x₋,x₊]}(x)) · ψ_R(z)`,

a continuous function on `CapSpace m`, `C¹` off the two interface hyperplanes `{x = x₋}`,
`{x = x₊}`, with bounded classical derivatives.  `RobinCaps.ThinDomain.H1P.ofPiecewise`
(file `Piecewise.lean`) turns it into an element of `H1P (thinDomain Cm Cp L R)`.

## Contents

* `TransverseGroundStateReg` — the transverse ground state *with the regularity the trial
  function needs*: `ψ_R` is `C¹` and its weak gradient is the classical one on `B_m(R)`.
  (For `m = 1` the explicit ground state `RobinCaps.Transverse.psi1` satisfies both fields:
  `contDiff_psiFun` and `psi1_grad` — its weak gradient is *literally*
  `Weak.classicalGrad`, so `grad_eq` holds by `rfl`.)
* `axialClamp`, `clampProfile`, `clampProfileDeriv` — the clamped axial profile and its
  piecewise derivative;
* `trialExt` — the trial function `eq:trial-extension` itself, with the three branch lemmas
  `trialExt_left`, `trialExt_bulk`, `trialExt_right` transcribing the display verbatim;
* `trialH1P` — the trial function as an element of `H1P (thinDomain Cm Cp L R)`;
* `capTrialLeft`, `capTrialRight` — the restrictions of the trial function to the two caps as
  elements of `H1P (leftCap …)`, `H1P (rightCap …)`;
* `massP_trialH1P`, `dirichletP_trialH1P` — the **exact** splittings
  `N_{Ω_R}[𝒯_RF] = N_cap⁻ + (∫_{I_R}F²)·N_B[ψ_R] + N_cap⁺` and
  `D_{Ω_R}[𝒯_RF] = D_cap⁻ + (∫_{I_R}F'²)·N_B[ψ_R] + (∫_{I_R}F²)·D_B[ψ_R] + D_cap⁺`,
  together with the normalized corollaries and the change-of-variables form of the cap
  contributions (`massP_capTrialLeft_eq`, `dirichletP_capTrialLeft_eq`, …) and their
  `Rescale.lean` form (`massP_capTrialLeft_rescale`, … — this is `eq:exact-cap-mass` and
  `eq:exact-cap-energy`);
* the targets `CapUpperGradientTarget`, `CapUpperMassTarget` (`eq:upper-gradient`,
  `eq:upper-mass` of `lem:cap-upper`), `TrialMassTarget` (`eq:trial-mass`) and
  `TrialEnergyTarget` (`eq:trial-energy`).

Everything outside the last section is **proved**: no `sorry`, `admit`, `axiom` or
`native_decide`.
-/

open MeasureTheory Set Filter Metric

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain

noncomputable section

variable {m : ℕ}

/-! ## 0. Two elementary boundedness helpers -/

/-- A continuous function is bounded on a bounded set (the ambient space is proper). -/
theorem exists_bound_on_bounded {F : Type*} [NormedAddCommGroup F] {f : CapSpace m → F}
    (hf : Continuous f) {Ω : Set (CapSpace m)} (hΩ : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Ω, ‖f p‖ ≤ C := by
  obtain ⟨r, hr⟩ := hΩ.subset_closedBall (0 : CapSpace m)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : CapSpace m) r).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p (hr hp)).trans (le_max_left _ _)⟩

/-- A continuous function on `ℝ` is bounded on a compact interval. -/
theorem exists_bound_on_Icc {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  simpa [Real.norm_eq_abs] using (hC x hx).trans (le_max_left C 0)

/-- Bounded measurable functions are integrable on sets of finite measure. -/
theorem integrableOn_of_bound {Ω : Set (CapSpace m)} (hΩ : volume Ω ≠ ⊤)
    {f : CapSpace m → ℝ} (hf : AEStronglyMeasurable f (volume.restrict Ω)) {C : ℝ}
    (hC : ∀ᵐ p ∂(volume.restrict Ω), ‖f p‖ ≤ C) : IntegrableOn f Ω := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hΩ⟩
  exact Integrable.mono' (integrable_const C) hf hC

/-! ## 1. The transverse ground state with the regularity the trial function needs

`TransverseGroundState` (file `GroundState.lean`) carries `ψ_R` only as an element of the *weak*
space `TransH1 m R = Weak.H1 (B_m(R))`.  The trial function of `eq:trial-extension` has to be
differentiated pointwise, so we need `ψ_R` to be `C¹` and its *chosen* weak gradient to be the
classical one on the ball. -/

variable {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **The transverse ground state, with pointwise regularity.**

`psiC1` and `grad_eq` are exactly the two facts used by `trialH1P`: without `psiC1` the trial
function is not differentiable in the transverse directions, and without `grad_eq` its Dirichlet
energy would not be expressible through `Weak.dirichlet ψ_R`.

For `m = 1` the explicit ground state of `RobinCaps/Transverse/GroundStateOne.lean` satisfies
both: `RobinCaps.Transverse.contDiff_psiFun` gives `psiC1`, and
`RobinCaps.Transverse.psi1_grad` says `(psi1 α R hα hR).grad = Weak.classicalGrad (psiFun …)`,
so `grad_eq` holds by `fun _ _ => rfl`. -/
structure TransverseGroundStateReg (m : ℕ) (α R : ℝ)
    (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    extends TransverseGroundState m α R bd where
  /-- `ψ_R` is `C¹` (up to and beyond the boundary of the ball). -/
  psiC1 : ContDiff ℝ 1 (fun z => psi.toFun z)
  /-- The chosen weak gradient of `ψ_R` is the classical gradient on `B_m(R)`. -/
  grad_eq : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R,
    psi.grad z = Weak.classicalGrad (fun w => psi.toFun w) z

namespace TransverseGroundStateReg

variable (gsr : TransverseGroundStateReg m α R bd)

theorem continuous_psi : Continuous (fun z => gsr.psi.toFun z) := gsr.psiC1.continuous

theorem continuous_classicalGrad_psi :
    Continuous (Weak.classicalGrad (fun z => gsr.psi.toFun z)) :=
  Weak.continuous_classicalGrad _ gsr.psiC1

end TransverseGroundStateReg

/-- The manuscript's radiality of `ψ_R` (`sec:transverse`), as a separate predicate: it is not
needed by any statement in this file, so it is deliberately *not* a field of
`TransverseGroundStateReg`. -/
def IsRadialGroundState (gsr : TransverseGroundStateReg m α R bd) : Prop :=
  ∃ f : ℝ → ℝ, ∀ z : EuclideanSpace ℝ (Fin m), gsr.psi.toFun z = f ‖z‖

/-- The manuscript's positivity of `ψ_R`, as a separate predicate (also unused below). -/
def IsPositiveGroundState (gsr : TransverseGroundStateReg m α R bd) : Prop :=
  ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R, 0 < gsr.psi.toFun z

/-! ## 2. The clamped axial profile -/

/-- The clamp `x ↦ max x₋ (min x₊ x)` written as in `eq:trial-extension`. -/
def axialClamp (xm xp x : ℝ) : ℝ := if x < xm then xm else if x ≤ xp then x else xp

variable {xm xp x : ℝ}

@[simp] theorem axialClamp_of_lt (h : x < xm) : axialClamp xm xp x = xm := by
  simp [axialClamp, h]

@[simp] theorem axialClamp_of_mem (h1 : xm ≤ x) (h2 : x ≤ xp) : axialClamp xm xp x = x := by
  simp [axialClamp, not_lt.2 h1, h2]

@[simp] theorem axialClamp_of_gt (h1 : xm ≤ x) (h2 : xp < x) : axialClamp xm xp x = xp := by
  simp [axialClamp, not_lt.2 h1, not_le.2 h2]

theorem axialClamp_eq_max_min (h : xm ≤ xp) (x : ℝ) :
    axialClamp xm xp x = max xm (min xp x) := by
  rcases lt_or_ge x xm with hx | hx
  · rw [axialClamp_of_lt hx, min_eq_right (le_trans hx.le h), max_eq_left hx.le]
  · rcases le_or_gt x xp with hx' | hx'
    · rw [axialClamp_of_mem hx hx', min_eq_right hx', max_eq_right hx]
    · rw [axialClamp_of_gt hx hx', min_eq_left hx'.le, max_eq_right h]

theorem continuous_axialClamp (h : xm ≤ xp) : Continuous (axialClamp xm xp) := by
  simpa [funext (axialClamp_eq_max_min h)] using
    (continuous_const.max (continuous_const.min continuous_id))

theorem axialClamp_mem_Icc (h : xm ≤ xp) (x : ℝ) : axialClamp xm xp x ∈ Icc xm xp := by
  rcases lt_or_ge x xm with hx | hx
  · rw [axialClamp_of_lt hx]; exact ⟨le_rfl, h⟩
  · rcases le_or_gt x xp with hx' | hx'
    · rw [axialClamp_of_mem hx hx']; exact ⟨hx, hx'⟩
    · rw [axialClamp_of_gt hx hx']; exact ⟨h, le_rfl⟩

/-- The axial factor of the trial function: `F` clamped to `[x₋, x₊]`. -/
def clampProfile (xm xp : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ := F (axialClamp xm xp x)

/-- Its derivative off the two interfaces: `F'` inside `[x₋, x₊]` and `0` outside. -/
def clampProfileDeriv (xm xp : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < xm then 0 else if x ≤ xp then deriv F x else 0

theorem continuous_clampProfile {F : ℝ → ℝ} (hF : Continuous F) (h : xm ≤ xp) :
    Continuous (clampProfile xm xp F) := hF.comp (continuous_axialClamp h)

theorem clampProfile_mem_image {F : ℝ → ℝ} (h : xm ≤ xp) (x : ℝ) :
    ∃ y ∈ Icc xm xp, clampProfile xm xp F x = F y :=
  ⟨axialClamp xm xp x, axialClamp_mem_Icc h x, rfl⟩

/-- **The clamped profile is differentiable off the two interfaces**, with derivative
`clampProfileDeriv`. -/
theorem hasDerivAt_clampProfile {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (h : xm ≤ xp)
    (h1 : x ≠ xm) (h2 : x ≠ xp) :
    HasDerivAt (clampProfile xm xp F) (clampProfileDeriv xm xp F x) x := by
  rcases lt_or_ge x xm with hx | hx
  · have hmem : {y : ℝ | y < xm} ∈ 𝓝 x := (isOpen_lt continuous_id continuous_const).mem_nhds hx
    have heq : clampProfile xm xp F =ᶠ[𝓝 x] fun _ => F xm := by
      filter_upwards [hmem] with y hy
      simp [clampProfile, axialClamp_of_lt hy]
    have : clampProfileDeriv xm xp F x = 0 := by simp [clampProfileDeriv, hx]
    rw [this]
    exact (hasDerivAt_const x (F xm)).congr_of_eventuallyEq heq
  · rcases lt_or_ge x xp with hx' | hx'
    · have hxm : xm < x := lt_of_le_of_ne hx (Ne.symm h1)
      have hmem : Ioo xm xp ∈ 𝓝 x := isOpen_Ioo.mem_nhds ⟨hxm, hx'⟩
      have heq : clampProfile xm xp F =ᶠ[𝓝 x] F := by
        filter_upwards [hmem] with y hy
        simp [clampProfile, axialClamp_of_mem hy.1.le hy.2.le]
      have hval : clampProfileDeriv xm xp F x = deriv F x := by
        simp [clampProfileDeriv, not_lt.2 hx, hx'.le]
      rw [hval]
      exact ((hF.differentiable le_rfl x).hasDerivAt).congr_of_eventuallyEq heq
    · have hxp : xp < x := lt_of_le_of_ne hx' (Ne.symm h2)
      have hmem : {y : ℝ | xp < y} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_id).mem_nhds hxp
      have heq : clampProfile xm xp F =ᶠ[𝓝 x] fun _ => F xp := by
        filter_upwards [hmem] with y hy
        have hy' : xm ≤ y := h.trans (le_of_lt hy)
        simp [clampProfile, axialClamp_of_gt hy' hy]
      have hval : clampProfileDeriv xm xp F x = 0 := by
        simp [clampProfileDeriv, not_lt.2 hx, not_le.2 hxp]
      rw [hval]
      exact (hasDerivAt_const x (F xp)).congr_of_eventuallyEq heq

theorem continuous_clampProfileDeriv_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (_h : xm ≤ xp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |clampProfileDeriv xm xp F x| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_on_Icc (hF.continuous_deriv le_rfl) xm xp
  refine ⟨C, hC0, fun x => ?_⟩
  rcases lt_or_ge x xm with hx | hx
  · simp [clampProfileDeriv, hx, hC0]
  · rcases le_or_gt x xp with hx' | hx'
    · rw [show clampProfileDeriv xm xp F x = deriv F x by
        simp [clampProfileDeriv, not_lt.2 hx, hx']]
      exact hC x ⟨hx, hx'⟩
    · simp [clampProfileDeriv, not_lt.2 hx, not_le.2 hx', hC0]

/-! ## 3. Derivatives of an axial ⊗ transverse product -/

section Product

variable {g : ℝ → ℝ} {g' : ℝ} {ψ : EuclideanSpace ℝ (Fin m) → ℝ} {p : CapSpace m}

/-- The Fréchet derivative of `(x, z) ↦ g x · ψ z`. -/
theorem hasFDerivAt_axialTensor (hg : HasDerivAt g g' p.1) (hψ : ContDiff ℝ 1 ψ) :
    HasFDerivAt (fun q : CapSpace m => g q.1 * ψ q.2)
      (g p.1 • (fderiv ℝ ψ p.2).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))
        + ψ p.2 • (g' • (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))))) p := by
  have h1 : HasFDerivAt (fun q : CapSpace m => g q.1)
      (g' • (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))) p := by
    simpa [Function.comp_def] using hg.comp_hasFDerivAt p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : CapSpace m => ψ q.2)
      ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))) p := by
    simpa [Function.comp_def] using
      ((hψ.differentiable le_rfl p.2).hasFDerivAt).comp p hasFDerivAt_snd
  simpa using h1.mul h2

/-- The axial weak derivative of `(x, z) ↦ g x · ψ z` is `g' ⊗ ψ`. -/
theorem dxP_axialTensor (hg : HasDerivAt g g' p.1) (hψ : ContDiff ℝ 1 ψ) :
    dxP (fun q : CapSpace m => g q.1 * ψ q.2) p = g' * ψ p.2 := by
  rw [dxP, (hasFDerivAt_axialTensor hg hψ).fderiv]
  simp [mul_comm]

/-- The transverse gradient of `(x, z) ↦ g x · ψ z` is `g ⊗ ∇ψ`. -/
theorem gradZP_axialTensor (hg : HasDerivAt g g' p.1) (hψ : ContDiff ℝ 1 ψ) :
    gradZP (fun q : CapSpace m => g q.1 * ψ q.2) p = g p.1 • Weak.classicalGrad ψ p.2 := by
  ext i
  rw [gradZP_apply, (hasFDerivAt_axialTensor hg hψ).fderiv]
  simp

end Product

/-! ## 4. The trial function `eq:trial-extension` -/

variable {Cm Cp : RobinCaps.Cap m} {L : ℝ}

/-- **The trial function `𝒯_R F` of `eq:trial-extension`.**

`𝒯_RF (x, z) = F(x₋)ψ_R(z)` for `x < x₋`, `= F(x)ψ_R(z)` for `x₋ ≤ x ≤ x₊`, and
`= F(x₊)ψ_R(z)` for `x > x₊`, with `x₋ = -L/2 + K₋R`, `x₊ = L/2 - K₊R`. -/
def trialExt (Cm Cp : RobinCaps.Cap m) (L R : ℝ) (F : ℝ → ℝ) (ψ : TransH1 m R)
    (p : CapSpace m) : ℝ :=
  clampProfile (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 * ψ.toFun p.2

variable {F : ℝ → ℝ} {ψ : TransH1 m R}

/-- First branch of `eq:trial-extension`: `a < x < x₋ ⟹ 𝒯_RF(x,z) = F(x₋)ψ_R(z)`. -/
theorem trialExt_left {p : CapSpace m} (hp : p.1 < -L/2 + Cm.K * R) :
    trialExt Cm Cp L R F ψ p = F (-L/2 + Cm.K * R) * ψ.toFun p.2 := by
  simp [trialExt, clampProfile, axialClamp_of_lt hp]

/-- Second branch of `eq:trial-extension`: `x₋ < x < x₊ ⟹ 𝒯_RF(x,z) = F(x)ψ_R(z)`. -/
theorem trialExt_bulk {p : CapSpace m} (h1 : -L/2 + Cm.K * R ≤ p.1)
    (h2 : p.1 ≤ L/2 - Cp.K * R) : trialExt Cm Cp L R F ψ p = F p.1 * ψ.toFun p.2 := by
  simp [trialExt, clampProfile, axialClamp_of_mem h1 h2]

/-- Third branch of `eq:trial-extension`: `x₊ < x < b ⟹ 𝒯_RF(x,z) = F(x₊)ψ_R(z)`. -/
theorem trialExt_right {p : CapSpace m} (h1 : -L/2 + Cm.K * R ≤ p.1)
    (h2 : L/2 - Cp.K * R < p.1) :
    trialExt Cm Cp L R F ψ p = F (L/2 - Cp.K * R) * ψ.toFun p.2 := by
  simp [trialExt, clampProfile, axialClamp_of_gt h1 h2]

theorem continuous_trialExt (hF : Continuous F) (hψ : Continuous (fun z => ψ.toFun z))
    (h : -L/2 + Cm.K * R ≤ L/2 - Cp.K * R) : Continuous (trialExt Cm Cp L R F ψ) :=
  ((continuous_clampProfile hF h).comp continuous_fst).mul (hψ.comp continuous_snd)

/-- Off the two interfaces the trial function is `C¹`. -/
theorem contDiffAt_trialExt (hF : ContDiff ℝ 1 F) (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z))
    (h : -L/2 + Cm.K * R ≤ L/2 - Cp.K * R) {p : CapSpace m}
    (h1 : p.1 ≠ -L/2 + Cm.K * R) (h2 : p.1 ≠ L/2 - Cp.K * R) :
    ContDiffAt ℝ 1 (trialExt Cm Cp L R F ψ) p := by
  set a := -L/2 + Cm.K * R with ha
  set b := L/2 - Cp.K * R with hb
  have hsnd : ContDiff ℝ 1 (fun q : CapSpace m => ψ.toFun q.2) := hψ.comp contDiff_snd
  rcases lt_or_ge p.1 a with hx | hx
  · have hmem : {q : CapSpace m | q.1 < a} ∈ 𝓝 p :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hx
    have hbr : ContDiffAt ℝ 1 (fun q : CapSpace m => F a * ψ.toFun q.2) p :=
      ((contDiff_const (c := F a)).mul hsnd).contDiffAt
    refine hbr.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with q hq
    exact trialExt_left hq
  · rcases lt_or_ge p.1 b with hx' | hx'
    · have hxa : a < p.1 := lt_of_le_of_ne hx (Ne.symm h1)
      have hmem : {q : CapSpace m | a < q.1 ∧ q.1 < b} ∈ 𝓝 p :=
        ((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hxa, hx'⟩
      have hbr : ContDiffAt ℝ 1 (fun q : CapSpace m => F q.1 * ψ.toFun q.2) p :=
        ((hF.comp contDiff_fst).mul hsnd).contDiffAt
      refine hbr.congr_of_eventuallyEq ?_
      filter_upwards [hmem] with q hq
      exact trialExt_bulk hq.1.le hq.2.le
    · have hxb : b < p.1 := lt_of_le_of_ne hx' (Ne.symm h2)
      have hmem : {q : CapSpace m | b < q.1} ∈ 𝓝 p :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hxb
      have hbr : ContDiffAt ℝ 1 (fun q : CapSpace m => F b * ψ.toFun q.2) p :=
        ((contDiff_const (c := F b)).mul hsnd).contDiffAt
      refine hbr.congr_of_eventuallyEq ?_
      filter_upwards [hmem] with q hq
      exact trialExt_right (h.trans hq.le) hq

/-- The axial weak derivative of the trial function off the interfaces. -/
theorem dxP_trialExt (hF : ContDiff ℝ 1 F) (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z))
    (h : -L/2 + Cm.K * R ≤ L/2 - Cp.K * R) {p : CapSpace m}
    (h1 : p.1 ≠ -L/2 + Cm.K * R) (h2 : p.1 ≠ L/2 - Cp.K * R) :
    dxP (trialExt Cm Cp L R F ψ) p
      = clampProfileDeriv (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 * ψ.toFun p.2 :=
  dxP_axialTensor (hasDerivAt_clampProfile hF h h1 h2) hψ

/-- The transverse gradient of the trial function off the interfaces. -/
theorem gradZP_trialExt (hF : ContDiff ℝ 1 F) (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z))
    (h : -L/2 + Cm.K * R ≤ L/2 - Cp.K * R) {p : CapSpace m}
    (h1 : p.1 ≠ -L/2 + Cm.K * R) (h2 : p.1 ≠ L/2 - Cp.K * R) :
    gradZP (trialExt Cm Cp L R F ψ) p
      = clampProfile (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 •
          Weak.classicalGrad (fun z => ψ.toFun z) p.2 :=
  gradZP_axialTensor (hasDerivAt_clampProfile hF h h1 h2) hψ

/-! ### The constant-in-`x` pieces used on the caps -/

/-- The trial function on a cap: `c · ψ_R(z)`, independent of the axial coordinate. -/
def constTensor (c : ℝ) (ψ : TransH1 m R) (p : CapSpace m) : ℝ := c * ψ.toFun p.2

theorem contDiff_constTensor (c : ℝ) (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z)) :
    ContDiff ℝ 1 (constTensor c ψ) := contDiff_const.mul (hψ.comp contDiff_snd)

theorem dxP_constTensor (c : ℝ) (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z)) (p : CapSpace m) :
    dxP (constTensor c ψ) p = 0 := by
  have := dxP_axialTensor (g := fun _ : ℝ => c) (g' := 0) (p := p)
    (hasDerivAt_const p.1 c) hψ
  simpa [constTensor] using this

theorem gradZP_constTensor (c : ℝ) (hψ : ContDiff ℝ 1 (fun z => ψ.toFun z)) (p : CapSpace m) :
    gradZP (constTensor c ψ) p = c • Weak.classicalGrad (fun z => ψ.toFun z) p.2 := by
  have := gradZP_axialTensor (g := fun _ : ℝ => c) (g' := 0) (p := p)
    (hasDerivAt_const p.1 c) hψ
  simpa [constTensor] using this

/-! ## 5. The trial function as an element of `H1P (thinDomain …)` -/

/-- A `C¹` function on a bounded set is an element of `H1P`.  (`hasWeakGradP_classical` needs no
openness; boundedness is what gives `L²`.) -/
def H1P.ofContDiffOfBounded (Ω : Set (CapSpace m)) (hΩm : MeasurableSet Ω)
    (hΩ : Bornology.IsBounded Ω) (u : CapSpace m → ℝ) (hu : ContDiff ℝ 1 u) : H1P Ω where
  toFun := u
  gx := dxP u
  gz := gradZP u
  memL2 := by
    obtain ⟨C, _, hC⟩ := exists_bound_on_bounded hu.continuous hΩ
    refine memLp_two_of_bounded_on hΩ hu.continuous.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hΩm] with p hp using hC p hp
  gx_memL2 := by
    obtain ⟨C, _, hC⟩ := exists_bound_on_bounded (continuous_dxP u hu) hΩ
    refine memLp_two_of_bounded_on hΩ (continuous_dxP u hu).aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hΩm] with p hp using hC p hp
  gz_memL2 := by
    obtain ⟨C, _, hC⟩ := exists_bound_on_bounded (continuous_gradZP u hu) hΩ
    refine memLp_two_of_bounded_on hΩ (continuous_gradZP u hu).aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hΩm] with p hp using hC p hp
  hasWeakGrad := hasWeakGradP_classical Ω u hu

/-- Bound for a continuous function on a closed transverse ball. -/
theorem exists_bound_on_closedBall {F : Type*} [NormedAddCommGroup F]
    {f : EuclideanSpace ℝ (Fin m) → F} (hf : Continuous f) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclideanSpace ℝ (Fin m), ‖z‖ ≤ r → ‖f z‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) r).exists_bound_of_continuousOn
      hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  exact (hC z (by simpa [mem_closedBall_zero_iff] using hz)).trans (le_max_left _ _)

/-! ## 6. The three pieces of the thin domain -/

section Pieces

theorem mem_thinDomain_norm_lt (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {p : CapSpace m}
    (hp : p ∈ thinDomain Cm Cp L R) : ‖p.2‖ < R := by
  obtain ⟨h1, h2, h3⟩ := hp
  exact lt_of_lt_of_le h3 (profile_le_R hR hL ⟨h1, h2⟩)

theorem leftCap_fst_lt (hR : 0 < R) {p : CapSpace m} (hp : p ∈ leftCap Cm L R) :
    p.1 < -L/2 + Cm.K * R := ((mem_leftCap_iff hR).1 hp).2.1

theorem rightCap_lt_fst (hR : 0 < R) {p : CapSpace m} (hp : p ∈ rightCap Cp L R) :
    L/2 - Cp.K * R < p.1 := ((mem_rightCap_iff hR).1 hp).1

theorem mem_bulkCylinder_fst {p : CapSpace m} (hp : p ∈ bulkCylinder Cm Cp L R) :
    -L/2 + Cm.K * R ≤ p.1 ∧ p.1 ≤ L/2 - Cp.K * R := hp.1

theorem measurableSet_bulkCylinder :
    MeasurableSet (bulkCylinder Cm Cp L R) := measurableSet_Icc.prod measurableSet_ball

theorem measurableSet_leftCap' (hR : 0 < R) : MeasurableSet (leftCap Cm L R) :=
  measurableSet_leftCap Cm L hR.ne' (RobinCaps.Cap.Concave.continuousOn_Ioo Cm)

theorem measurableSet_rightCap' (hR : 0 < R) : MeasurableSet (rightCap Cp L R) :=
  measurableSet_rightCap Cp L hR.ne' (RobinCaps.Cap.Concave.continuousOn_Ioo Cp)

theorem leftCap_subset (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    leftCap Cm L R ⊆ thinDomain Cm Cp L R := by
  rw [thinDomain_eq_union hR hL]; exact subset_union_left.trans subset_union_left

theorem bulkCylinder_subset (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    bulkCylinder Cm Cp L R ⊆ thinDomain Cm Cp L R := by
  rw [thinDomain_eq_union hR hL]; exact subset_union_right.trans subset_union_left

theorem rightCap_subset (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    rightCap Cp L R ⊆ thinDomain Cm Cp L R := by
  rw [thinDomain_eq_union hR hL]; exact subset_union_right

theorem isBounded_leftCap (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Bornology.IsBounded (leftCap Cm L R) :=
  (isBounded_thinDomain hR hL).subset (leftCap_subset hR hL)

theorem isBounded_rightCap (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Bornology.IsBounded (rightCap Cp L R) :=
  (isBounded_thinDomain (Cm := Cm) hR hL).subset (rightCap_subset hR hL)

theorem disjoint_leftCap_bulkCylinder (hR : 0 < R) :
    Disjoint (leftCap Cm L R) (bulkCylinder Cm Cp L R) :=
  Set.disjoint_left.2 fun _p hp hq =>
    absurd (mem_bulkCylinder_fst hq).1 (not_le.2 (leftCap_fst_lt hR hp))

theorem disjoint_bulkCylinder_rightCap (hR : 0 < R) :
    Disjoint (bulkCylinder Cm Cp L R) (rightCap Cp L R) :=
  Set.disjoint_left.2 fun _p hp hq =>
    absurd (mem_bulkCylinder_fst hp).2 (not_le.2 (rightCap_lt_fst hR hq))

theorem disjoint_leftCap_rightCap (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Disjoint (leftCap Cm L R) (rightCap Cp L R) :=
  Set.disjoint_left.2 fun _p hp hq => by
    have h1 := leftCap_fst_lt hR hp
    have h2 := rightCap_lt_fst (Cp := Cp) hR hq
    have := interface_lt (Cm := Cm) (Cp := Cp) hR hL
    linarith

/-- The closed bulk cylinder and the open one of `Tensor.lean` differ by the two interface
slices, which are null. -/
theorem bulkCylinder_ae_eq_bulkCyl (Cm Cp : RobinCaps.Cap m) (L R : ℝ) :
    bulkCylinder Cm Cp L R
      =ᵐ[volume] bulkCyl (-L/2 + Cm.K * R) (L/2 - Cp.K * R) m R := by
  have hsub : bulkCyl (-L/2 + Cm.K * R) (L/2 - Cp.K * R) m R ⊆ bulkCylinder Cm Cp L R :=
    Set.prod_mono Ioo_subset_Icc_self (subset_refl _)
  have hnull : volume {p : CapSpace m |
      p.1 ∈ ({-L/2 + Cm.K * R, L/2 - Cp.K * R} : Finset ℝ)} = 0 :=
    volume_interfaces_eq_zero _
  refine ae_eq_set.2 ⟨measure_mono_null ?_ hnull, ?_⟩
  · rintro p ⟨⟨hx1, hx2⟩, hnp⟩
    have hz : p.2 ∈ transverseBall m R := hx2
    have h1 : p.1 ∉ Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R) := fun h => hnp ⟨h, hz⟩
    have h2 : p.1 = -L/2 + Cm.K * R ∨ p.1 = L/2 - Cp.K * R := by
      rcases eq_or_lt_of_le hx1.1 with h | h
      · exact Or.inl h.symm
      · rcases eq_or_lt_of_le hx1.2 with h' | h'
        · exact Or.inr h'
        · exact absurd ⟨h, h'⟩ h1
    simpa using h2
  · simp [Set.diff_eq_empty.2 hsub]

theorem setIntegral_bulkCylinder (Cm Cp : RobinCaps.Cap m) (L R : ℝ) (f : CapSpace m → ℝ) :
    ∫ p in bulkCylinder Cm Cp L R, f p
      = ∫ p in bulkCyl (-L/2 + Cm.K * R) (L/2 - Cp.K * R) m R, f p :=
  setIntegral_congr_set (bulkCylinder_ae_eq_bulkCyl Cm Cp L R)

/-- **The integral over `Ω_R` splits into the three pieces.** -/
theorem setIntegral_thinDomain_split (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {f : CapSpace m → ℝ} (hf : IntegrableOn f (thinDomain Cm Cp L R)) :
    ∫ p in thinDomain Cm Cp L R, f p
      = (∫ p in leftCap Cm L R, f p) + (∫ p in bulkCylinder Cm Cp L R, f p)
        + ∫ p in rightCap Cp L R, f p := by
  have hU := thinDomain_eq_union (Cm := Cm) (Cp := Cp) hR hL
  have hsubLB : leftCap Cm L R ∪ bulkCylinder Cm Cp L R ⊆ thinDomain Cm Cp L R := by
    rw [hU]; exact subset_union_left
  have hd2 : Disjoint (leftCap Cm L R ∪ bulkCylinder Cm Cp L R) (rightCap Cp L R) :=
    Disjoint.union_left (disjoint_leftCap_rightCap hR hL) (disjoint_bulkCylinder_rightCap hR)
  have e1 : ∫ p in thinDomain Cm Cp L R, f p
      = (∫ p in leftCap Cm L R ∪ bulkCylinder Cm Cp L R, f p)
        + ∫ p in rightCap Cp L R, f p := by
    rw [hU]
    exact setIntegral_union hd2 (measurableSet_rightCap' hR) (hf.mono_set hsubLB)
      (hf.mono_set (rightCap_subset hR hL))
  rw [e1, setIntegral_union (disjoint_leftCap_bulkCylinder hR) measurableSet_bulkCylinder
    (hf.mono_set (leftCap_subset hR hL)) (hf.mono_set (bulkCylinder_subset hR hL))]

end Pieces

/-! ## 7. The trial function as an element of `H1P (Ω_R)` -/

variable {F : ℝ → ℝ}

/-- **The trial function `𝒯_R F` as an element of `H¹(Ω_R)`** (`eq:trial-extension`).

It is glued across the two interface slices `x = x₋`, `x = x₊`, so
`RobinCaps.ThinDomain.H1P.ofPiecewise` with `S = {x₋, x₊}` is exactly the right constructor. -/
def trialH1P (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (gsr : TransverseGroundStateReg m α R bd) :
    H1P (thinDomain Cm Cp L R) := by
  classical
  refine H1P.ofPiecewise (thinDomain Cm Cp L R) (isOpen_thinDomain hR hL)
    (isBounded_thinDomain hR hL) {-L/2 + Cm.K * R, L/2 - Cp.K * R}
    (trialExt Cm Cp L R F gsr.psi)
    (continuous_trialExt hF.continuous gsr.psiC1.continuous
      (interface_lt hR hL).le).continuousOn ?_ ?_ ?_
  · intro p hp
    have h1 : p.1 ≠ -L/2 + Cm.K * R := fun h => hp.2 (by simp [h])
    have h2 : p.1 ≠ L/2 - Cp.K * R := fun h => hp.2 (by simp [h])
    exact (contDiffAt_trialExt hF gsr.psiC1 (interface_lt hR hL).le h1 h2).contDiffWithinAt
  · obtain ⟨C1, hC10, hC1⟩ := continuous_clampProfileDeriv_bound (xm := -L/2 + Cm.K * R)
      (xp := L/2 - Cp.K * R) hF (interface_lt hR hL).le
    obtain ⟨C2, hC20, hC2⟩ := exists_bound_on_closedBall gsr.psiC1.continuous R
    obtain ⟨C3, hC30, hC3⟩ :=
      exists_bound_on_Icc hF.continuous (-L/2 + Cm.K * R) (L/2 - Cp.K * R)
    obtain ⟨C4, hC40, hC4⟩ :=
      exists_bound_on_closedBall gsr.continuous_classicalGrad_psi R
    refine ⟨max (C1 * C2) (C3 * C4), fun p hp => ?_⟩
    have h1 : p.1 ≠ -L/2 + Cm.K * R := fun h => hp.2 (by simp [h])
    have h2 : p.1 ≠ L/2 - Cp.K * R := fun h => hp.2 (by simp [h])
    have hz : ‖p.2‖ ≤ R := (mem_thinDomain_norm_lt hR hL hp.1).le
    constructor
    · rw [dxP_trialExt hF gsr.psiC1 (interface_lt hR hL).le h1 h2, abs_mul]
      refine le_trans (mul_le_mul (hC1 _) ?_ (abs_nonneg _) hC10) (le_max_left _ _)
      simpa [Real.norm_eq_abs] using hC2 p.2 hz
    · rw [gradZP_trialExt hF gsr.psiC1 (interface_lt hR hL).le h1 h2, norm_smul,
        Real.norm_eq_abs]
      obtain ⟨y, hy, hyeq⟩ :=
        clampProfile_mem_image (F := F) (interface_lt hR hL).le p.1
      rw [hyeq]
      exact le_trans (mul_le_mul (hC3 y hy) (hC4 p.2 hz) (norm_nonneg _) hC30)
        (le_max_right _ _)
  · obtain ⟨C, _, hC⟩ := exists_bound_on_bounded
      (continuous_trialExt hF.continuous gsr.psiC1.continuous (interface_lt hR hL).le)
      (isBounded_thinDomain (Cm := Cm) (Cp := Cp) (L := L) hR hL)
    exact ⟨C, fun p hp => by simpa [Real.norm_eq_abs] using hC p hp⟩

@[simp] theorem trialH1P_toFun (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    (trialH1P Cm Cp L hR hL F hF gsr).toFun = trialExt Cm Cp L R F gsr.psi := rfl

@[simp] theorem trialH1P_gx (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    (trialH1P Cm Cp L hR hL F hF gsr).gx = dxP (trialExt Cm Cp L R F gsr.psi) := rfl

@[simp] theorem trialH1P_gz (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    (trialH1P Cm Cp L hR hL F hF gsr).gz = gradZP (trialExt Cm Cp L R F gsr.psi) := rfl

/-! ## 8. The two cap pieces -/

/-- The restriction of the trial function to the left cap, `F(x₋)ψ_R(z)`, as an element of
`H¹(𝒞₋^R)`. -/
def capTrialLeft (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    H1P (leftCap Cm L R) :=
  H1P.ofContDiffOfBounded _ (measurableSet_leftCap' hR)
    (isBounded_leftCap (Cp := Cp) hR hL)
    (constTensor (F (-L/2 + Cm.K * R)) gsr.psi) (contDiff_constTensor _ gsr.psiC1)

/-- The restriction of the trial function to the right cap, `F(x₊)ψ_R(z)`. -/
def capTrialRight (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    H1P (rightCap Cp L R) :=
  H1P.ofContDiffOfBounded _ (measurableSet_rightCap' hR)
    (isBounded_rightCap (Cm := Cm) hR hL)
    (constTensor (F (L/2 - Cp.K * R)) gsr.psi) (contDiff_constTensor _ gsr.psiC1)

@[simp] theorem capTrialLeft_toFun (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    (capTrialLeft Cm Cp L hR hL F gsr).toFun
      = constTensor (F (-L/2 + Cm.K * R)) gsr.psi := rfl

@[simp] theorem capTrialRight_toFun (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    (capTrialRight Cm Cp L hR hL F gsr).toFun
      = constTensor (F (L/2 - Cp.K * R)) gsr.psi := rfl

/-! ## 9. Pointwise identification of the derivatives on the three pieces -/

theorem trialDerivs_on_left (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) {p : CapSpace m}
    (hp : p.1 < -L/2 + Cm.K * R) :
    dxP (trialExt Cm Cp L R F gsr.psi) p
        = dxP (constTensor (F (-L/2 + Cm.K * R)) gsr.psi) p ∧
      gradZP (trialExt Cm Cp L R F gsr.psi) p
        = gradZP (constTensor (F (-L/2 + Cm.K * R)) gsr.psi) p := by
  have hab := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have h1 : p.1 ≠ -L/2 + Cm.K * R := ne_of_lt hp
  have h2 : p.1 ≠ L/2 - Cp.K * R := ne_of_lt (hp.trans hab)
  refine ⟨?_, ?_⟩
  · rw [dxP_trialExt hF gsr.psiC1 hab.le h1 h2, dxP_constTensor _ gsr.psiC1,
      show clampProfileDeriv (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 = 0 by
        simp [clampProfileDeriv, hp], zero_mul]
  · rw [gradZP_trialExt hF gsr.psiC1 hab.le h1 h2, gradZP_constTensor _ gsr.psiC1,
      show clampProfile (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 = F (-L/2 + Cm.K * R) by
        simp [clampProfile, axialClamp_of_lt hp]]

theorem trialDerivs_on_right (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) {p : CapSpace m}
    (hp : L/2 - Cp.K * R < p.1) :
    dxP (trialExt Cm Cp L R F gsr.psi) p
        = dxP (constTensor (F (L/2 - Cp.K * R)) gsr.psi) p ∧
      gradZP (trialExt Cm Cp L R F gsr.psi) p
        = gradZP (constTensor (F (L/2 - Cp.K * R)) gsr.psi) p := by
  have hab := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hge : -L/2 + Cm.K * R ≤ p.1 := (hab.trans hp).le
  have h1 : p.1 ≠ -L/2 + Cm.K * R := ne_of_gt (hab.trans hp)
  have h2 : p.1 ≠ L/2 - Cp.K * R := ne_of_gt hp
  refine ⟨?_, ?_⟩
  · rw [dxP_trialExt hF gsr.psiC1 hab.le h1 h2, dxP_constTensor _ gsr.psiC1,
      show clampProfileDeriv (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 = 0 by
        simp [clampProfileDeriv, not_lt.2 hge, not_le.2 hp], zero_mul]
  · rw [gradZP_trialExt hF gsr.psiC1 hab.le h1 h2, gradZP_constTensor _ gsr.psiC1,
      show clampProfile (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 = F (L/2 - Cp.K * R) by
        simp [clampProfile, axialClamp_of_gt hge hp]]

theorem trialDerivs_on_bulk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) {p : CapSpace m}
    (h1 : -L/2 + Cm.K * R < p.1) (h2 : p.1 < L/2 - Cp.K * R)
    (hz : p.2 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R) :
    dxP (trialExt Cm Cp L R F gsr.psi) p = deriv F p.1 * gsr.psi.toFun p.2 ∧
      gradZP (trialExt Cm Cp L R F gsr.psi) p = F p.1 • gsr.psi.grad p.2 := by
  have hab := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  refine ⟨?_, ?_⟩
  · rw [dxP_trialExt hF gsr.psiC1 hab.le (ne_of_gt h1) (ne_of_lt h2),
      show clampProfileDeriv (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 = deriv F p.1 by
        simp [clampProfileDeriv, not_lt.2 h1.le, h2.le]]
  · rw [gradZP_trialExt hF gsr.psiC1 hab.le (ne_of_gt h1) (ne_of_lt h2),
      show clampProfile (-L/2 + Cm.K * R) (L/2 - Cp.K * R) F p.1 = F p.1 by
        simp [clampProfile, axialClamp_of_mem h1.le h2.le], gsr.grad_eq p.2 hz]

/-! ## 10. The exact splitting of the mass and of the Dirichlet energy -/

/-- **The mass of the trial function splits exactly** into the two cap masses and the bulk mass
`(∫_{I_R} F²)·N_{B_m(R)}[ψ_R]`. -/
theorem massP_trialH1P (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    massP (trialH1P Cm Cp L hR hL F hF gsr)
      = massP (capTrialLeft Cm Cp L hR hL F gsr)
        + (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2) * NB gsr.psi
        + massP (capTrialRight Cm Cp L hR hL F gsr) := by
  have hab : (-L/2 + Cm.K * R) < L/2 - Cp.K * R := interface_lt hR hL
  have hInt : IntegrableOn (fun p => trialExt Cm Cp L R F gsr.psi p ^ 2)
      (thinDomain Cm Cp L R) := (trialH1P Cm Cp L hR hL F hF gsr).memL2.integrable_sq
  have hsplit := setIntegral_thinDomain_split hR hL hInt
  have hleft : massP (capTrialLeft Cm Cp L hR hL F gsr)
      = ∫ p in leftCap Cm L R, trialExt Cm Cp L R F gsr.psi p ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_leftCap' hR) fun p hp => ?_
    rw [trialExt_left (leftCap_fst_lt hR hp)]
    rfl
  have hright : massP (capTrialRight Cm Cp L hR hL F gsr)
      = ∫ p in rightCap Cp L R, trialExt Cm Cp L R F gsr.psi p ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_rightCap' hR) fun p hp => ?_
    rw [trialExt_right (hab.trans (rightCap_lt_fst hR hp)).le (rightCap_lt_fst hR hp)]
    rfl
  have hbulk : ∫ p in bulkCylinder Cm Cp L R, trialExt Cm Cp L R F gsr.psi p ^ 2
      = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2) * NB gsr.psi := by
    rw [setIntegral_bulkCylinder, ← massP_tensor F hF hab gsr.psi]
    refine setIntegral_congr_fun isOpen_bulkCyl.measurableSet fun p hp => ?_
    rw [trialExt_bulk hp.1.1.le hp.1.2.le]
    rfl
  rw [show massP (trialH1P Cm Cp L hR hL F hF gsr)
      = ∫ p in thinDomain Cm Cp L R, trialExt Cm Cp L R F gsr.psi p ^ 2 from rfl,
    hsplit, hleft, hright, hbulk]

/-- **The Dirichlet energy of the trial function splits exactly**; the bulk part factorises by
`dirichletP_tensor`. -/
theorem dirichletP_trialH1P (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    dirichletP (trialH1P Cm Cp L hR hL F hF gsr)
      = dirichletP (capTrialLeft Cm Cp L hR hL F gsr)
        + ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2) * NB gsr.psi
          + (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2) * Weak.dirichlet gsr.psi)
        + dirichletP (capTrialRight Cm Cp L hR hL F gsr) := by
  have hab : (-L/2 + Cm.K * R) < L/2 - Cp.K * R := interface_lt hR hL
  set u := trialH1P Cm Cp L hR hL F hF gsr with hu
  have hI1 : Integrable (fun p => u.gx p ^ 2) (volume.restrict (thinDomain Cm Cp L R)) :=
    u.gx_memL2.integrable_sq
  have hI2 : Integrable (fun p => ‖u.gz p‖ ^ 2) (volume.restrict (thinDomain Cm Cp L R)) :=
    (memLp_two_iff_integrable_sq_norm u.gz_memL2.aestronglyMeasurable).1 u.gz_memL2
  have hInt : IntegrableOn (fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2) (thinDomain Cm Cp L R) :=
    hI1.add hI2
  have hsplit := setIntegral_thinDomain_split hR hL hInt
  have hleft : dirichletP (capTrialLeft Cm Cp L hR hL F gsr)
      = ∫ p in leftCap Cm L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2) := by
    refine setIntegral_congr_fun (measurableSet_leftCap' hR) fun p hp => ?_
    obtain ⟨e1, e2⟩ := trialDerivs_on_left hR hL hF gsr (leftCap_fst_lt hR hp)
    show _ = dxP (trialExt Cm Cp L R F gsr.psi) p ^ 2
        + ‖gradZP (trialExt Cm Cp L R F gsr.psi) p‖ ^ 2
    rw [e1, e2]
    rfl
  have hright : dirichletP (capTrialRight Cm Cp L hR hL F gsr)
      = ∫ p in rightCap Cp L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2) := by
    refine setIntegral_congr_fun (measurableSet_rightCap' hR) fun p hp => ?_
    obtain ⟨e1, e2⟩ := trialDerivs_on_right hR hL hF gsr (rightCap_lt_fst hR hp)
    show _ = dxP (trialExt Cm Cp L R F gsr.psi) p ^ 2
        + ‖gradZP (trialExt Cm Cp L R F gsr.psi) p‖ ^ 2
    rw [e1, e2]
    rfl
  have hbulk : ∫ p in bulkCylinder Cm Cp L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2)
      = (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2) * NB gsr.psi
        + (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2) * Weak.dirichlet gsr.psi := by
    rw [setIntegral_bulkCylinder, ← dirichletP_tensor F hF hab gsr.psi]
    refine setIntegral_congr_fun isOpen_bulkCyl.measurableSet fun p hp => ?_
    obtain ⟨e1, e2⟩ := trialDerivs_on_bulk hR hL hF gsr hp.1.1 hp.1.2 hp.2
    show dxP (trialExt Cm Cp L R F gsr.psi) p ^ 2
        + ‖gradZP (trialExt Cm Cp L R F gsr.psi) p‖ ^ 2 = _
    rw [e1, e2]
    rfl
  rw [show dirichletP u = ∫ p in thinDomain Cm Cp L R, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2) from rfl,
    hsplit, hleft, hright, hbulk]

/-- With the normalized ground state (`NB ψ_R = 1`) the bulk mass is exactly `∫_{I_R} F²`. -/
theorem massP_trialH1P_normalized (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    massP (trialH1P Cm Cp L hR hL F hF gsr)
      = massP (capTrialLeft Cm Cp L hR hL F gsr)
        + (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
        + massP (capTrialRight Cm Cp L hR hL F gsr) := by
  rw [massP_trialH1P, gsr.normalized, mul_one]

/-- With the normalized ground state the bulk energy is `∫_{I_R} F'² + (∫_{I_R} F²)·D_B[ψ_R]`. -/
theorem dirichletP_trialH1P_normalized (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (gsr : TransverseGroundStateReg m α R bd) :
    dirichletP (trialH1P Cm Cp L hR hL F hF gsr)
      = dirichletP (capTrialLeft Cm Cp L hR hL F gsr)
        + ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
          + (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2) * Weak.dirichlet gsr.psi)
        + dirichletP (capTrialRight Cm Cp L hR hL F gsr) := by
  rw [dirichletP_trialH1P, gsr.normalized, mul_one]

/-! ## 11. The cap contributions in cap coordinates

Two forms are given for each cap contribution: the explicit change-of-variables form
`R^{m+1} · (integral over the fixed cap body `𝒞`)`, and the `Rescale.lean` form, which is
`eq:exact-cap-mass` / `eq:exact-cap-energy` of the manuscript. -/

/-- `Ψ_R` of `lem:cap-upper`: the transverse ground state rescaled to the unit ball and lifted
to the cap body independently of the axial coordinate, `Ψ_R(s, z) = R^{m/2} ψ_R(R z)`. -/
def capGroundLift (m : ℕ) (R : ℝ) (ψ : TransH1 m R) (p : CapSpace m) : ℝ :=
  R ^ ((m : ℝ) / 2) * ψ.toFun (R • p.2)

/-- The left cap mass in cap coordinates. -/
theorem massP_capTrialLeft_eq (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    massP (capTrialLeft Cm Cp L hR hL F gsr)
      = F (-L/2 + Cm.K * R) ^ 2 *
        (R ^ (m + 1) * ∫ p in Cm.body, gsr.psi.toFun (R • p.2) ^ 2) := by
  have hbody := Cm.measurableSet_body (RobinCaps.Cap.Concave.continuousOn_Ioo Cm)
  have hcov := setIntegral_image_affP (m := m) (-L/2) (ε := -1) hR (by norm_num) hbody
    (fun q : CapSpace m => (F (-L/2 + Cm.K * R) * gsr.psi.toFun q.2) ^ 2)
  have h0 : massP (capTrialLeft Cm Cp L hR hL F gsr)
      = ∫ q in affP (-L/2) (-1) R '' Cm.body,
          (F (-L/2 + Cm.K * R) * gsr.psi.toFun q.2) ^ 2 := by
    rw [← leftCap_eq_image]; rfl
  have key : (∫ p in Cm.body,
        (F (-L/2 + Cm.K * R) * gsr.psi.toFun ((affP (-L/2) (-1) R p).2)) ^ 2)
      = F (-L/2 + Cm.K * R) ^ 2 * ∫ p in Cm.body, gsr.psi.toFun (R • p.2) ^ 2 := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun p => by simp only [affP_snd]; ring)
  rw [h0, hcov, key]
  ring

/-- The right cap mass in cap coordinates. -/
theorem massP_capTrialRight_eq (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    massP (capTrialRight Cm Cp L hR hL F gsr)
      = F (L/2 - Cp.K * R) ^ 2 *
        (R ^ (m + 1) * ∫ p in Cp.body, gsr.psi.toFun (R • p.2) ^ 2) := by
  have hbody := Cp.measurableSet_body (RobinCaps.Cap.Concave.continuousOn_Ioo Cp)
  have hcov := setIntegral_image_affP (m := m) (L/2) (ε := 1) hR (by norm_num) hbody
    (fun q : CapSpace m => (F (L/2 - Cp.K * R) * gsr.psi.toFun q.2) ^ 2)
  have h0 : massP (capTrialRight Cm Cp L hR hL F gsr)
      = ∫ q in affP (L/2) 1 R '' Cp.body,
          (F (L/2 - Cp.K * R) * gsr.psi.toFun q.2) ^ 2 := by
    rw [← rightCap_eq_image]; rfl
  have key : (∫ p in Cp.body,
        (F (L/2 - Cp.K * R) * gsr.psi.toFun ((affP (L/2) 1 R p).2)) ^ 2)
      = F (L/2 - Cp.K * R) ^ 2 * ∫ p in Cp.body, gsr.psi.toFun (R • p.2) ^ 2 := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun p => by simp only [affP_snd]; ring)
  rw [h0, hcov, key]
  ring

/-- The cap trial functions have no axial derivative, so their Dirichlet energy is purely
transverse. -/
theorem dirichlet_integrand_constTensor (c : ℝ) (gsr : TransverseGroundStateReg m α R bd)
    (p : CapSpace m) :
    dxP (constTensor c gsr.psi) p ^ 2 + ‖gradZP (constTensor c gsr.psi) p‖ ^ 2
      = c ^ 2 * ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) p.2‖ ^ 2 := by
  rw [dxP_constTensor _ gsr.psiC1, gradZP_constTensor _ gsr.psiC1, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

/-- The left cap energy in cap coordinates. -/
theorem dirichletP_capTrialLeft_eq (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    dirichletP (capTrialLeft Cm Cp L hR hL F gsr)
      = F (-L/2 + Cm.K * R) ^ 2 * (R ^ (m + 1) *
          ∫ p in Cm.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2) := by
  have hbody := Cm.measurableSet_body (RobinCaps.Cap.Concave.continuousOn_Ioo Cm)
  have hcov := setIntegral_image_affP (m := m) (-L/2) (ε := -1) hR (by norm_num) hbody
    (fun q : CapSpace m => F (-L/2 + Cm.K * R) ^ 2 *
      ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) q.2‖ ^ 2)
  have h0 : dirichletP (capTrialLeft Cm Cp L hR hL F gsr)
      = ∫ q in affP (-L/2) (-1) R '' Cm.body, F (-L/2 + Cm.K * R) ^ 2 *
          ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) q.2‖ ^ 2 := by
    rw [← leftCap_eq_image]
    exact integral_congr_ae (.of_forall fun p =>
      dirichlet_integrand_constTensor _ gsr p)
  rw [h0, hcov]
  simp only [affP_snd]
  rw [integral_const_mul]
  ring

/-- The right cap energy in cap coordinates. -/
theorem dirichletP_capTrialRight_eq (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    dirichletP (capTrialRight Cm Cp L hR hL F gsr)
      = F (L/2 - Cp.K * R) ^ 2 * (R ^ (m + 1) *
          ∫ p in Cp.body, ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) (R • p.2)‖ ^ 2) := by
  have hbody := Cp.measurableSet_body (RobinCaps.Cap.Concave.continuousOn_Ioo Cp)
  have hcov := setIntegral_image_affP (m := m) (L/2) (ε := 1) hR (by norm_num) hbody
    (fun q : CapSpace m => F (L/2 - Cp.K * R) ^ 2 *
      ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) q.2‖ ^ 2)
  have h0 : dirichletP (capTrialRight Cm Cp L hR hL F gsr)
      = ∫ q in affP (L/2) 1 R '' Cp.body, F (L/2 - Cp.K * R) ^ 2 *
          ‖Weak.classicalGrad (fun z => gsr.psi.toFun z) q.2‖ ^ 2 := by
    rw [← rightCap_eq_image]
    exact integral_congr_ae (.of_forall fun p =>
      dirichlet_integrand_constTensor _ gsr p)
  rw [h0, hcov]
  simp only [affP_snd]
  rw [integral_const_mul]
  ring

/-! ### The `Rescale.lean` form: `eq:exact-cap-mass` and `eq:exact-cap-energy` -/

/-- `N_cap⁻ = R ‖U‖²_{L²(𝒞₋)}` with `U = R^{m/2} u ∘ A₋` (`eq:exact-cap-mass`). -/
theorem massP_capTrialLeft_rescale (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd)
    (c : ℝ) (hc : c ^ 2 = R ^ m) :
    massP (capTrialLeft Cm Cp L hR hL F gsr)
      = R * massP (H1P.rescaleLeft Cm L c hR (RobinCaps.Cap.Concave.continuousOn_Ioo Cm)
          (capTrialLeft Cm Cp L hR hL F gsr)) := by
  rw [massP_rescaleLeft_of_sq_eq Cm L c hR hc _ _, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

/-- `D_cap⁻ = R⁻¹ ‖∇U‖²_{L²(𝒞₋)}` (`eq:exact-cap-energy`, gradient part). -/
theorem dirichletP_capTrialLeft_rescale (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd)
    (c : ℝ) (hc : c ^ 2 = R ^ m) :
    dirichletP (capTrialLeft Cm Cp L hR hL F gsr)
      = R⁻¹ * dirichletP (H1P.rescaleLeft Cm L c hR (RobinCaps.Cap.Concave.continuousOn_Ioo Cm)
          (capTrialLeft Cm Cp L hR hL F gsr)) := by
  rw [dirichletP_rescaleLeft_of_sq_eq Cm L c hR hc _ _, ← mul_assoc,
    inv_mul_cancel₀ hR.ne', one_mul]

/-- `N_cap⁺ = R ‖U‖²_{L²(𝒞₊)}`. -/
theorem massP_capTrialRight_rescale (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd)
    (c : ℝ) (hc : c ^ 2 = R ^ m) :
    massP (capTrialRight Cm Cp L hR hL F gsr)
      = R * massP (H1P.rescaleRight Cp L c hR (RobinCaps.Cap.Concave.continuousOn_Ioo Cp)
          (capTrialRight Cm Cp L hR hL F gsr)) := by
  rw [massP_rescaleRight_of_sq_eq Cp L c hR hc _ _, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

/-- `D_cap⁺ = R⁻¹ ‖∇U‖²_{L²(𝒞₊)}`. -/
theorem dirichletP_capTrialRight_rescale (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd)
    (c : ℝ) (hc : c ^ 2 = R ^ m) :
    dirichletP (capTrialRight Cm Cp L hR hL F gsr)
      = R⁻¹ * dirichletP (H1P.rescaleRight Cp L c hR (RobinCaps.Cap.Concave.continuousOn_Ioo Cp)
          (capTrialRight Cm Cp L hR hL F gsr)) := by
  rw [dirichletP_rescaleRight_of_sq_eq Cp L c hR hc _ _, ← mul_assoc,
    inv_mul_cancel₀ hR.ne', one_mul]

/-- The rescaled left cap trial function is `F(x₋)·Ψ_R` with `Ψ_R` the lifted ground state of
`lem:cap-upper`. -/
theorem rescaleLeft_capTrialLeft_toFun (Cm Cp : RobinCaps.Cap m) (L : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (F : ℝ → ℝ) (gsr : TransverseGroundStateReg m α R bd) :
    (H1P.rescaleLeft Cm L (R ^ ((m : ℝ) / 2)) hR
        (RobinCaps.Cap.Concave.continuousOn_Ioo Cm)
        (capTrialLeft Cm Cp L hR hL F gsr)).toFun
      = fun p => F (-L/2 + Cm.K * R) * capGroundLift m R gsr.psi p := by
  funext p
  rw [H1P.rescaleLeft, H1P.cast_toFun]
  show R ^ ((m : ℝ) / 2) * (F (-L/2 + Cm.K * R) * gsr.psi.toFun ((affP (-L/2) (-1) R p).2)) = _
  simp only [affP_snd, capGroundLift]
  ring

/-! ## 12. The manuscript's estimates, as targets

These are the statements that would close the upper bound of `sec:proof`.  They are *not*
proved here: `eq:upper-gradient`/`eq:upper-mass` are quantitative expansions of `ψ_R`
(`lem:transverse`), and the `J`-estimate `eq:upper-J` additionally needs the cap boundary form
`eq:J-definition`, which is not formalized in this project — so it is stated with `J` and `δ_R`
as parameters. -/

/-- **`eq:upper-gradient`** of `lem:cap-upper`: `R⁻¹∫_𝒞|∇_zΨ_R|² = O(R)`. -/
def CapUpperGradientTarget (m : ℕ) (α : ℝ) (C : RobinCaps.Cap m) : Prop :=
  ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    ∀ (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
      (gsr : TransverseGroundStateReg m α R bd),
      |R⁻¹ * ∫ p in C.body, ‖gradZP (capGroundLift m R gsr.psi) p‖ ^ 2| ≤ A * R

/-- **`eq:upper-mass`** of `lem:cap-upper`: `R‖Ψ_R‖²_{L²(𝒞)} = O(R)`. -/
def CapUpperMassTarget (m : ℕ) (α : ℝ) (C : RobinCaps.Cap m) : Prop :=
  ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    ∀ (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
      (gsr : TransverseGroundStateReg m α R bd),
      |R * ∫ p in C.body, capGroundLift m R gsr.psi p ^ 2| ≤ A * R

/-- **`eq:upper-J`** of `lem:cap-upper`: `J[Ψ_R] - δ_R‖Ψ_R‖²_{L²(𝒞)} = β(𝒞) + O(R)`.
`J` (`eq:J-definition`) and `δ_R` are parameters because the cap boundary form is not
formalized in this project. -/
def CapUpperJTarget (m : ℕ) (α : ℝ) (C : RobinCaps.Cap m)
    (J : (CapSpace m → ℝ) → ℝ) (delta : ℝ → ℝ) : Prop :=
  ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    ∀ (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
      (gsr : TransverseGroundStateReg m α R bd),
      |J (capGroundLift m R gsr.psi)
        - delta R * (∫ p in C.body, capGroundLift m R gsr.psi p ^ 2)
        - RobinCaps.Cap.beta C α| ≤ A * R

/-- **`eq:trial-mass`**: `M[F] ≤ N_R[𝒯_RF] ≤ M[F] + C R S[F]`. -/
def TrialMassTarget (m : ℕ) (α : ℝ) (Cm Cp : RobinCaps.Cap m) (L : ℝ) : Prop :=
  ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
    ∀ hL : (Cm.K + Cp.K) * R < L,
      ∀ (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
        (gsr : TransverseGroundStateReg m α R bd) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F),
        (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
            ≤ massP (trialH1P Cm Cp L hR hL F hF gsr) ∧
          massP (trialH1P Cm Cp L hR hL F hF gsr)
            ≤ (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
              + A * R * (F (-L/2 + Cm.K * R) ^ 2 + F (L/2 - Cp.K * R) ^ 2)

/-- The renormalized energy `E_R[u] = q_{Ω_R}[u] - ν_R N_{Ω_R}[u]` of `sec:proof`.  The Robin
boundary term is the concrete `RobinCaps.ThinDomain.boundaryEnergy` of `Boundary.lean`, applied
to the pointwise representative (legitimate for the trial function, which is continuous up to
`∂Ω_R`). -/
def renormEnergy (Cm Cp : RobinCaps.Cap m) (L R alpha nu : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP u + alpha * boundaryEnergy Cm Cp L R u.toFun - nu * massP u

/-- **`eq:trial-energy`**: `E_R[𝒯_RF] = a_{β₋,β₊;I_R}[F] + ε_R[F]` with `|ε_R[F]| ≤ C R S[F]`,
where `a_{β₋,β₊;I_R}[F] = ∫_{I_R}|F'|² + β₋|F(x₋)|² + β₊|F(x₊)|²` (`eq:interval-form`). -/
def TrialEnergyTarget (m : ℕ) (α : ℝ) (Cm Cp : RobinCaps.Cap m) (L : ℝ) : Prop :=
  ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
    ∀ hL : (Cm.K + Cp.K) * R < L,
      ∀ (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
        (gsr : TransverseGroundStateReg m α R bd) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F),
        |renormEnergy Cm Cp L R α gsr.nu (trialH1P Cm Cp L hR hL F hF gsr)
            - ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
              + RobinCaps.Cap.beta Cm α * F (-L/2 + Cm.K * R) ^ 2
              + RobinCaps.Cap.beta Cp α * F (L/2 - Cp.K * R) ^ 2)|
          ≤ A * R * (F (-L/2 + Cm.K * R) ^ 2 + F (L/2 - Cp.K * R) ^ 2)

/-! ## 13. Axiom audit -/


end

end RobinCaps.ThinDomain
