import RobinCaps.ThinDomain.BridgeCapLowerOne
import RobinCaps.ThinDomain.BridgeInterfaceOne
import RobinCaps.ThinDomain.BridgeTrialOne
import RobinCaps.ThinDomain.BridgeTraceIneqOne
import RobinCaps.Cap.PoincareOne

/-!
# `thm:main` and `cor:counterexample` for the planar capsule with two hemispherical caps

This is the **final combination** of the `m = 1` main theorem.  The abstract assembly
`RobinCaps.ThinDomain.mainTheorem_one_a1` (`RobinCaps/ThinDomain/AssemblyOne.lean`) consumes
four interface `Prop`s, each with its own constant and its own radius threshold:

* `TraceIneqInput_a1` — discharged for the hemispherical caps by
  `traceIneqInput_hemisphere_bti` (`RobinCaps/ThinDomain/BridgeTraceIneqOne.lean`);
* `CapLowerInput_a1` — discharged by `capLowerInput_one_bc`
  (`RobinCaps/ThinDomain/BridgeCapLowerOne.lean`);
* `InterfaceTraceInput_a1` — discharged by `interfaceTraceInput_one_bi`
  (`RobinCaps/ThinDomain/BridgeInterfaceOne.lean`);
* `TrialEnergyInput_a1` — discharged by `trialEnergyInput_one_bt`
  (`RobinCaps/ThinDomain/BridgeTrialOne.lean`).

This file aligns the four thresholds (and the stadium threshold `R₀ ≤ L / 2` of the planar
trace inequality) at their minimum, using the monotonicity lemmas `traceIneqInput_le_bti`,
`interfaceTraceInput_le_bi`, `trialEnergyInput_le_bt` and `capLowerInput_le_m1` (proved here,
since `RobinCaps/ThinDomain/BridgeCapLowerOne.lean` does not record it), feeds the result to
`mainTheorem_one_a1`, and then to `counterexample_of_mainTheorem'`
(`RobinCaps/ThinDomain/Eigen.lean`).

The Poincaré constant of the fixed unit hemisphere is supplied internally by
`RobinCaps.Cap.capPoincare_one` (`RobinCaps/Cap/PoincareOne.lean`), so it does **not** appear
as a hypothesis.

## The two hypotheses that remain

Both theorems below are stated against exactly **two** hypotheses, both about the *fixed* unit
hemisphere `(Cap.hemisphere 1)`; everything else is proved:

1. `td : CapTraceData (Cap.hemisphere 1)` together with
   `hmatch : ∀ R hR hL, CapTraceMatch_bc td L R (√R) hR hL` — the trace operator on the
   exposed boundary `Γ` of the unit cap, and the identification of its `Γ`-form on the cap
   components with the cap pieces `bdCapL_a1` / `bdCapR_a1` of the `m = 1` vertical-trace
   density (the factor `c² / R` of `CapTraceMatch_bc` is `1` at `c = √R`).
   *Expected to be supplied by* `RobinCaps/Cap/TraceDataHemi.lean` (the `CapTraceData`
   instance, by even reflection) *and* `RobinCaps/ThinDomain/BridgeCapMatchOne.lean` (the
   scaling match `hmatch`).  Both are in progress and are **not** imported here.

2. `hen : CapEntranceL2 (Cap.hemisphere 1) C₁` — the `L²(Σ)` trace theorem on the entrance
   disk of the unit cap.
   *Expected to be supplied by* `RobinCaps/Cap/EntranceL2Hemi.lean`, also in progress and not
   imported here.

Feeding those two files' outputs to `mainTheorem_hemisphere_m1` and
`counterexample_hemisphere_m1` closes the `m = 1` chain unconditionally.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## 1.  The missing monotonicity lemma for `CapLowerInput_a1` -/

/-- **`CapLowerInput_a1` is monotone in the radius threshold.**  Its single field is a
universally quantified implication over the admissible radii `R < R₀`, so shrinking `R₀`
preserves it.  (`RobinCaps/ThinDomain/BridgeCapLowerOne.lean` records no such lemma; the three
sibling interfaces have `traceIneqInput_le_bti`, `interfaceTraceInput_le_bi` and
`trialEnergyInput_le_bt`.) -/
theorem capLowerInput_le_m1 {Cm Cp : Cap 1} {L α : ℝ} {hα : 0 < α} {Ccap R₀ R₀' : ℝ}
    (h : CapLowerInput_a1 Cm Cp L α hα Ccap R₀) (hle : R₀' ≤ R₀) :
    CapLowerInput_a1 Cm Cp L α hα Ccap R₀' :=
  ⟨fun R hR hR0 hL => h.cap R hR (lt_of_lt_of_le hR0 hle) hL⟩

/-! ## 2.  The aligned threshold and the four interface inputs at it -/

/-- **All four interface inputs of `AssemblyOne`, at one common threshold.**

The threshold `R₀` is the minimum of the four thresholds produced by the four bridge files and
of `L / 2` (the stadium condition of `traceIneqInput_hemisphere_bti`, which also gives the
hypothesis `(K₋ + K₊) R₀ ≤ L` of `traceFamilyOne_a1` since `K = 1` for the hemisphere).

The hypotheses are the two remaining analytic bricks `td`/`hmatch` and `hen`; the Poincaré
constant comes from `RobinCaps.Cap.capPoincare_one`. -/
theorem inputs_hemisphere_m1 (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (td : CapTraceData (Cap.hemisphere 1)) {C₁ : ℝ}
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁)
    (hmatch : ∀ (R : ℝ) (hR : 0 < R)
      (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L),
      CapTraceMatch_bc td L R (Real.sqrt R) hR hL) :
    ∃ R₀ : ℝ, ∃ _ : 0 < R₀, ∃ _ : R₀ ≤ L / 2, ∃ Ccap Cif Ctr : ℝ, 0 ≤ Ccap ∧
      CapLowerInput_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hα Ccap R₀ ∧
      InterfaceTraceInput_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hα Cif R₀ ∧
      TrialEnergyInput_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hα
        (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) Ctr R₀ := by
  obtain ⟨CP, hP⟩ := RobinCaps.Cap.capPoincare_one (Cap.hemisphere 1)
  obtain ⟨Ccap, Rc, hCcap, hRc, hcap⟩ :=
    capLowerInput_one_bc α hα L hL0 td CP C₁ hP hen hmatch
  obtain ⟨Cif, Ri, hCif, hRi, hif⟩ :=
    interfaceTraceInput_one_bi (Cap.hemisphere 1) (Cap.hemisphere 1) L α hα hL0
  obtain ⟨Ctr, Rt, hCtr, hRt, hRt1, htr⟩ :=
    trialEnergyInput_one_bt (Cap.hemisphere 1) (Cap.hemisphere 1) L α hα
      (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1)
  refine ⟨min (min Rc Ri) (min Rt (L / 2)),
    lt_min (lt_min hRc hRi) (lt_min hRt (by linarith)),
    le_trans (min_le_right _ _) (min_le_right _ _),
    Ccap, Cif, Ctr, hCcap,
    capLowerInput_le_m1 hcap (le_trans (min_le_left _ _) (min_le_left _ _)),
    interfaceTraceInput_le_bi hif (le_trans (min_le_left _ _) (min_le_right _ _)),
    trialEnergyInput_le_bt htr (le_trans (min_le_right _ _) (min_le_left _ _))⟩

/-! ## 3.  `thm:main` for two hemispherical caps -/

/-- **`thm:main` for `m = 1`, two hemispherical caps** (manuscript, statement lines 222–250).

For the planar capsule `Ω_R` with two hemispherical end caps there is a threshold `R₀ > 0`
with `R₀ ≤ L / 2` such that the genuine variational Robin eigenvalues
`λ_j(Ω_R;α) = lambdaThin …`, computed with the recorded trace family
`traceFamilyHemi_bti` of `RobinCaps/ThinDomain/BridgeTraceIneqOne.lean`, satisfy the two-term
asymptotics

> for every `J` there are `C_J ≥ 0`, `R_J > 0` with
> `|λ_j(Ω_R;α) − ν_R − μ_j(β₀,β₀;L)| ≤ C_J R` for `0 < R < R_J`, `1 ≤ j ≤ J`,

with `ν_R = λ₁(B_1(R);α) = nuOneDim α hα R` and `β₀ = (hemisphere 1).beta α > 0`.

The only hypotheses are the two analytic bricks about the *fixed* unit hemisphere described in
the module docstring: `td` with `hmatch`, and `hen`. -/
theorem mainTheorem_hemisphere_m1 (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (td : CapTraceData (Cap.hemisphere 1)) {C₁ : ℝ}
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁)
    (hmatch : ∀ (R : ℝ) (hR : 0 < R)
      (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L),
      CapTraceMatch_bc td L R (Real.sqrt R) hR hL) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      MainTheorem 1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hL0
        (hemisphere_beta_pos 1 le_rfl hα) (hemisphere_beta_pos 1 le_rfl hα)
        (nuOneDim α hα) R₀ (traceFamilyHemi_bti L hL0 hR₀ hR₀L) := by
  obtain ⟨R₀, hR₀, hR₀L, Ccap, Cif, Ctr, hCcap, hcap, hif, htr⟩ :=
    inputs_hemisphere_m1 L α hL0 hα td hen hmatch
  exact ⟨R₀, hR₀, hR₀L,
    mainTheorem_one_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hL0 hα
      (hemisphere_beta_pos 1 le_rfl hα) (hemisphere_beta_pos 1 le_rfl hα)
      (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1) R₀ hR₀
      (hemisphere_two_mul_le_bti hR₀L) hCcap
      (traceIneqInput_hemisphere_bti L hL0 hR₀ hR₀L) hcap hif htr⟩

/-! ## 4.  `cor:counterexample` for two hemispherical caps -/

/-- **`cor:counterexample` for `m = 1`** (`n = 2`), in its strongest recorded form
(`RobinCaps.ThinDomain.counterexample_of_mainTheorem'`).

For the planar capsule `Ω_R` with two hemispherical caps — by
`Domain.toEuclid_thinDomain_hemisphere` isometric to `{x : dist(x, S) < R}` — there are
thresholds `R₀ > 0` (with `R₀ ≤ L / 2`) and `R₁ > 0` such that for every `0 < R < R₁` with
`2 R < L` the genuine variational Robin eigenvalues satisfy

* `λ₂(Ω_R;α) − λ₁(Ω_R;α) ≤ G_α(L) − Δ/2` (manuscript `eq:finite-deficit`), with
  `Δ = Delta 1 L hL0 α > 0`;
* hence `λ₂(Ω_R;α) − λ₁(Ω_R;α) < G_α(L) = Interval.gap L hL0 α`;
* and `euclidDiam Ω_R = L` (`Domain.euclidDiam_thinDomain_hemisphere`), so the last bound
  reads `λ₂ − λ₁ < G_α(diam Ω_R)`: the pair `(Ω_R, α)` violates the conjectured gap bound,
  which is the manuscript's `eq:counterexample`.

The hypotheses are the same two analytic bricks as in `mainTheorem_hemisphere_m1`. -/
theorem counterexample_hemisphere_m1 (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (td : CapTraceData (Cap.hemisphere 1)) {C₁ : ℝ}
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁)
    (hmatch : ∀ (R : ℝ) (hR : 0 < R)
      (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L),
      CapTraceMatch_bc td L R (Real.sqrt R) hR hL) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2, ∃ R₁ : ℝ, 0 < R₁ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L) (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R)
              (traceFamilyHemi_bti L hL0 hR₀ hR₀L R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R)
              (traceFamilyHemi_bti L hL0 hR₀ hR₀L R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta 1 L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R)
              (traceFamilyHemi_bti L hL0 hR₀ hR₀L R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R)
              (traceFamilyHemi_bti L hL0 hR₀ hR₀L R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) = L := by
  obtain ⟨R₀, hR₀, hR₀L, hmain⟩ := mainTheorem_hemisphere_m1 L α hL0 hα td hen hmatch
  obtain ⟨R₁, hR₁, hconc⟩ :=
    counterexample_of_mainTheorem' 1 le_rfl L α hL0 hα (nuOneDim α hα) R₀ hR₀
      (traceFamilyHemi_bti L hL0 hR₀ hR₀L) hmain
  exact ⟨R₀, hR₀, hR₀L, R₁, hR₁, hconc⟩

end RobinCaps.ThinDomain

end
