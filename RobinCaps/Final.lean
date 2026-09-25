import RobinCaps.Cap.Main
import RobinCaps.Cap.Unconditional
import RobinCaps.ThinDomain.MainOneFinal
import RobinCaps.ThinDomain.MainGenFinal
import RobinCaps.ThinDomain.GradientLeading
import RobinCaps.ThinDomain.NuBall
import RobinCaps.ThinDomain.MainGeneralFinal

set_option linter.unusedVariables false

/-!
# Summary of headline theorems

This file re-exports the project's headline theorems, with names suffixed `_final`/`_top`. The
manuscript numbering used in docstrings below refers to the arXiv version of the paper:
`thm:calibration` = Theorem 1.4, `thm:main` = Theorem 1.3, `cor:counterexample` = Theorem 1.2.

1. `RobinCaps/Cap/Main.lean` — the sharp geometric inequality for end-caps (`thm:calibration`)
2. `RobinCaps/ThinDomain/MainOneFinal.lean` — main result for `m = 1` with hemispherical caps
3. `RobinCaps/ThinDomain/MainGenFinal.lean` — main result for all `m ≥ 1`
4. `RobinCaps/ThinDomain/GradientLeading.lean` — second-order transverse expansion
5. `RobinCaps/ThinDomain/NuBall.lean` — **recommended entry points**: `thm:main`,
   `eq:single-cap` and `cor:counterexample` with `ν_R = λ₁(B_m(R);α)` explicit (`nuBall`),
   existence of a trace family, and validity for every trace family
6. `RobinCaps/ThinDomain/MainGeneralFinal.lean` — **`RobinCaps.mainTheorem_general_top`**:
   `thm:main` for every pair of admissible caps and every `m ≥ 1` (the main entry point;
   imported here, not restated)

-/

namespace RobinCaps

open Cap Domain ThinDomain Compact MeasureTheory

/-- Manuscript `thm:calibration` (sharp geometric inequality for end-caps).
Proved in `RobinCaps/Cap/Main.lean`. -/
theorem sharp_cap_inequality_final_top (m : ℕ) (hm : 1 ≤ m) (C : Cap m) :
    C.F ≥ omega (m + 1) / 2 :=
  Cap.sharp_cap_inequality_uc m hm C

/-- Manuscript `thm:calibration`, equality case (`eq:equality-profile`): equality holds exactly
for the unit hemisphere, optionally extended at the entrance by a unit cylinder.
Proved in `RobinCaps/Cap/EqualityAC.lean`. -/
theorem equality_iff_final_top (m : ℕ) (hm : 1 ≤ m) (C : Cap m) :
    C.F = omega (m + 1) / 2 ↔ Cap.EqualityProfile C :=
  Cap.equality_iff_uc m hm C

/-- Manuscript `thm:main` for `m = 1` (two hemispherical caps).
Proved in `RobinCaps/ThinDomain/MainOneFinal.lean`. -/
theorem mainTheorem_hemisphere_final_top (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      MainTheorem 1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hL0
        (hemisphere_beta_pos 1 le_rfl hα) (hemisphere_beta_pos 1 le_rfl hα)
        (nuOneDim α hα) R₀ (traceFamilyHemi_bti L hL0 hR₀ hR₀L) :=
  ThinDomain.mainTheorem_hemisphere_final L α hL0 hα

/-- Manuscript `cor:counterexample` for `m = 1` (hemispherical caps).
Proved in `RobinCaps/ThinDomain/MainOneFinal.lean`. -/
theorem counterexample_hemisphere_final_top (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) :
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
        euclidDiam (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) = L :=
  ThinDomain.counterexample_hemisphere_final L α hL0 hα

/-- Manuscript `thm:main` for general `m ≥ 1` (two hemispherical caps).
Proved in `RobinCaps/ThinDomain/MainGenFinal.lean`. -/
theorem mainTheorem_hemisphere_gen_final_top (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.hemisphere m) (Cap.hemisphere m) L α hL0
        (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf :=
  ThinDomain.mainTheorem_hemisphere_gen_final m hm L α hL0 hα

/-- Manuscript `cor:counterexample` for general `m ≥ 1` (hemispherical capsule).
Proved in `RobinCaps/ThinDomain/MainGenFinal.lean`. -/
theorem counterexample_hemisphere_gen_final_top (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      ∃ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L) (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) = L :=
  ThinDomain.counterexample_hemisphere_gen_final m hm L α hL0 hα

/-- Manuscript `thm:main` for single-cap domain (flat left end, hemispherical right cap, general `m ≥ 1`).
Proved in `RobinCaps/ThinDomain/MainGenFinal.lean`. -/
theorem mainTheorem_single_final_top (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0
        (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf :=
  ThinDomain.mainTheorem_single_final m hm K hK L α hL0 hα

/-- Manuscript `eq:single-cap` (error term `O(R)` for single-cap domain, general `m ≥ 1`).
Proved in `RobinCaps/ThinDomain/MainGenFinal.lean`. -/
theorem mainTheorem_single_alpha_final_top (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      ∀ J : ℕ, ∃ C R₁' : ℝ, 0 ≤ C ∧ 0 < R₁' ∧ R₁' ≤ R₀ ∧
        ∀ (R : ℝ) (hR : 0 < R) (hRR₀ : R < R₀) (_hR₁ : R < R₁')
          (hLR : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (j : ℕ) (hj : 1 ≤ j),
          j ≤ J →
          |lambdaThin hR hLR (tdf R hR hRR₀) α j - nu' R
              - Interval.mu α ((Cap.hemisphere m).beta α) L j hα (hemisphere_beta_pos m hm hα)
                  hL0 hj| ≤ C * R :=
  ThinDomain.mainTheorem_single_alpha_final m hm K hK L α hL0 hα

/-- Manuscript `rem:gradient-leading` and `eq:gradient-leading` (second-order transverse expansion, general `m ≥ 1`).
Proved in `RobinCaps/ThinDomain/GradientLeading.lean`. -/
theorem gradient_leading_gl_final_top (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (Cexp : ℝ) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 < R₀ ∧ ∀ R (hR : 0 < R), R < R₀ →
      ∀ gs : TransverseGroundState m α R (bdR m R), ExpW_tw m α R gs Cexp →
        |(∫ p in (Cap.hemisphere m).body, ‖(capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz p‖ ^ 2)
            - α ^ 2 * R ^ 2 / omega m * (∫ p in (Cap.hemisphere m).body, ‖p.2‖ ^ 2)|
          ≤ C * R ^ 3 :=
  ThinDomain.gradient_leading_gl m hm α hα Cexp

/-! ## Recommended entry points (`NuBall.lean`)

`nuBall m α R = Compact.lam1 α (bdR m R)` is the bottom of the Rayleigh quotient of the Robin
form on `B_m(R)`, i.e. the manuscript's `ν_R = λ₁(B_m(R); α)`.  Each statement asserts that trace
families exist and that the conclusion holds for **every** trace family. -/

/-- Manuscript `thm:main`, two hemispherical caps, every `m ≥ 1`, explicit `ν_R`. -/
theorem mainTheorem_hemisphere_top (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      Nonempty (TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀,
        MainTheorem m (Cap.hemisphere m) (Cap.hemisphere m) L α hL0
          (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) (nuBall m α) R₀ tdf :=
  ThinDomain.mainTheorem_hemisphere_nb m hm L α hL0 hα

/-- Manuscript `cor:counterexample`, every `m ≥ 1`, for every trace family. -/
theorem counterexample_hemisphere_top (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      Nonempty (TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L) (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) = L :=
  ThinDomain.counterexample_hemisphere_nb m hm L α hL0 hα

/-- Manuscript `eq:single-cap` (flat left end, hemispherical right cap), every `m ≥ 1`,
explicit `ν_R`, for every trace family. -/
theorem mainTheorem_single_alpha_top (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L,
      Nonempty (TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      ∀ J : ℕ, ∃ C R₁' : ℝ, 0 ≤ C ∧ 0 < R₁' ∧ R₁' ≤ R₀ ∧
        ∀ (R : ℝ) (hR : 0 < R) (hRR₀ : R < R₀) (_hR₁ : R < R₁')
          (hLR : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (j : ℕ) (hj : 1 ≤ j),
          j ≤ J →
          |lambdaThin hR hLR (tdf R hR hRR₀) α j - nuBall m α R
              - Interval.mu α ((Cap.hemisphere m).beta α) L j hα (hemisphere_beta_pos m hm hα)
                  hL0 hj| ≤ C * R :=
  ThinDomain.mainTheorem_single_alpha_nb m hm K hK L α hL0 hα

end RobinCaps
