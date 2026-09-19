import RobinCaps.ThinDomain.CounterexampleGeneral
import RobinCaps.Cap.Frustum

/-!
# Counterexamples close to flat ends (manuscript Section 9.3)

Entry points for the extension of `cor:counterexample` beyond hemispherical caps.

* `RobinCaps.counterexample_of_beta_lt_top`: for **every** admissible cap `C` with
  `β(C) < α`, the thin domain with two copies of `C` satisfies
  `λ₂(Ω_R;α) − λ₁(Ω_R;α) < G_α(diam Ω_R)` for all small `R`, where `diam Ω_R` is the Euclidean
  diameter of `Ω_R` (for general caps only `L ≤ diam Ω_R ≤ √(L² + 4R²)` is known).
* `RobinCaps.counterexample_nearFlat_top`: the frustum caps `θ_δ(s) = 1 − δ(s+1)`, `K = 1`
  (`Cap.frustum`), which are `δ`-close to the flat end, have `β < α` for all small `δ > 0`
  (`Cap.frustum_beta_lt_fr`, from the linearization `eq:linearization` with `κ = m/2`), hence
  give such counterexamples.

Both statements assert that a trace family exists and that the conclusion holds for every trace
family, as for the other headline theorems.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

set_option linter.unusedVariables false

namespace RobinCaps

open Cap Domain ThinDomain

/-- Manuscript Section 9.3, general form: any admissible cap with `β(C) < α` gives a strict
reverse inequality at the true diameter, for all small `R` and every trace family. -/
theorem counterexample_of_beta_lt_top (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) (hβ : C.beta α < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (C.K + C.K) * R₀ ≤ L,
      Nonempty (TraceFamily C C L R₀) ∧
      ∀ tdf : TraceFamily C C L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
        ∀ (R : ℝ) (hR : 0 < R), R < R₁ →
          ∀ (hLR : (C.K + C.K) * R < L) (hR₀' : R < R₀)
            (hD : 0 < euclidDiam (thinDomain C C L R)),
            lambdaThin hR hLR (tdf R hR hR₀') α 2 - lambdaThin hR hLR (tdf R hR hR₀') α 1
              < Interval.gap (euclidDiam (thinDomain C C L R)) hD α :=
  ThinDomain.counterexample_of_beta_lt_cg m hm C L α hL0 hα hβ

/-- Manuscript Section 9.3, caps close to a flat end: there is `δ₀ > 0` such that for every
amplitude `0 < δ < δ₀`, every `L > 0` and every `α > 0`, the thin domain closed by two frustum
caps `θ_δ(s) = 1 − δ(s+1)` violates the Robin gap inequality at its true diameter for all
small `R`. -/
theorem counterexample_nearFlat_top (m : ℕ) (hm : 1 ≤ m) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1), δ < δ₀ →
        ∀ (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α),
          (Cap.frustum m δ hδ0 hδ1).beta α < α ∧
          ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀,
            ∃ hR₀L : ((Cap.frustum m δ hδ0 hδ1).K + (Cap.frustum m δ hδ0 hδ1).K) * R₀ ≤ L,
            Nonempty (TraceFamily (Cap.frustum m δ hδ0 hδ1) (Cap.frustum m δ hδ0 hδ1) L R₀) ∧
            ∀ tdf : TraceFamily (Cap.frustum m δ hδ0 hδ1) (Cap.frustum m δ hδ0 hδ1) L R₀,
              ∃ R₁ : ℝ, 0 < R₁ ∧
              ∀ (R : ℝ) (hR : 0 < R), R < R₁ →
                ∀ (hLR : ((Cap.frustum m δ hδ0 hδ1).K + (Cap.frustum m δ hδ0 hδ1).K) * R < L)
                  (hR₀' : R < R₀)
                  (hD : 0 < euclidDiam (thinDomain (Cap.frustum m δ hδ0 hδ1)
                    (Cap.frustum m δ hδ0 hδ1) L R)),
                  lambdaThin hR hLR (tdf R hR hR₀') α 2 - lambdaThin hR hLR (tdf R hR hR₀') α 1
                    < Interval.gap (euclidDiam (thinDomain (Cap.frustum m δ hδ0 hδ1)
                        (Cap.frustum m δ hδ0 hδ1) L R)) hD α := by
  obtain ⟨δ₀, hδ₀pos, hδ₀le, hlt⟩ := Cap.frustum_beta_lt_fr m hm
  refine ⟨δ₀, hδ₀pos, hδ₀le, fun δ hδ0 hδ1 hδ L α hL0 hα => ?_⟩
  have hβ := hlt δ hδ0 hδ1 hδ α hα
  exact ⟨hβ, counterexample_of_beta_lt_top m hm (Cap.frustum m δ hδ0 hδ1) L α hL0 hα hβ⟩

end RobinCaps
