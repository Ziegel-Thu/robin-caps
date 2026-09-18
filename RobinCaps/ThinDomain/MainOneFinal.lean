import RobinCaps.ThinDomain.MainOne
import RobinCaps.ThinDomain.BridgeCapMatchOne
import RobinCaps.Cap.TraceDataHemi
import RobinCaps.Cap.EntranceL2Hemi

/-!
# `thm:main` and `cor:counterexample` for `m = 1`, two hemispherical caps — unconditional

This file instantiates the two remaining hypotheses of `RobinCaps/ThinDomain/MainOne.lean`:

* the trace datum on the unit hemispherical cap, `Cap.capTraceDataHemi_th 1 le_rfl`
  (`RobinCaps/Cap/TraceDataHemi.lean`), whose boundary form is the half-sphere integral of the
  reflection trace (`capTraceDataHemi_bdΓ_eq_th`), which is exactly the interface
  `BdGammaIsSphere_cm` of `RobinCaps/ThinDomain/BridgeCapMatchOne.lean`;
* the entrance-trace bound `Cap.capEntranceL2_hemi_el` (`RobinCaps/Cap/EntranceL2Hemi.lean`).

The scaling match `CapTraceMatch_bc` is then `capTraceMatch_of_sphere_cm`.  The resulting
theorems have **no interface hypotheses left**: only `0 < L` and `0 < α`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.ThinDomain

open RobinCaps.Cap RobinCaps.Domain

/-- The hemisphere trace datum satisfies the half-sphere interface of `BridgeCapMatchOne`. -/
theorem bdGammaIsSphere_hemi_final :
    BdGammaIsSphere_cm (capTraceDataHemi_th 1 le_rfl) :=
  fun v => capTraceDataHemi_bdΓ_eq_th 1 le_rfl v

/-- The scaling match for the hemisphere trace datum, at the manuscript normalisation
`c = √R`, for every admissible radius. -/
theorem capTraceMatch_hemi_final (L : ℝ) :
    ∀ (R : ℝ) (hR : 0 < R)
      (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L),
      CapTraceMatch_bc (capTraceDataHemi_th 1 le_rfl) L R (Real.sqrt R) hR hL := by
  intro R hR hL
  have h2 : 2 * R < L := by rw [hemisphere_K_st] at hL; linarith
  exact capTraceMatch_of_sphere_cm _ bdGammaIsSphere_hemi_final hR h2 _

/-- **`thm:main` for `m = 1` with two hemispherical caps, unconditional.** -/
theorem mainTheorem_hemisphere_final (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      MainTheorem 1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hL0
        (hemisphere_beta_pos 1 le_rfl hα) (hemisphere_beta_pos 1 le_rfl hα)
        (nuOneDim α hα) R₀ (traceFamilyHemi_bti L hL0 hR₀ hR₀L) := by
  obtain ⟨C₁, hen⟩ := capEntranceL2_hemi_el
  exact mainTheorem_hemisphere_m1 L α hL0 hα (capTraceDataHemi_th 1 le_rfl) hen
    (capTraceMatch_hemi_final L)

/-- **`cor:counterexample` (`eq:counterexample`, `eq:finite-deficit`) for the planar stadium,
unconditional**: for all sufficiently small `R`, the genuine variational Robin eigenvalues of
`Ω_R` satisfy `λ₂ − λ₁ ≤ G_α(L) − Δ/2 < G_α(L)`, and `diam Ω_R = L`. -/
theorem counterexample_hemisphere_final (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) :
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
  obtain ⟨C₁, hen⟩ := capEntranceL2_hemi_el
  exact counterexample_hemisphere_m1 L α hL0 hα (capTraceDataHemi_th 1 le_rfl) hen
    (capTraceMatch_hemi_final L)

end RobinCaps.ThinDomain
