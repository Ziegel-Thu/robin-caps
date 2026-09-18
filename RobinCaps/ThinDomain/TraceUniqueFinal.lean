import RobinCaps.ThinDomain.TraceUnique
import RobinCaps.Sobolev.ConvexDensity

/-!
# Trace-independence of the main results — unconditional

`RobinCaps/ThinDomain/TraceUnique.lean` shows that any two trace data on the thin domain have the
same boundary form, hence the same Robin eigenvalues, and restates the headline theorems for an
**arbitrary** trace family, modulo the density interface `C1Dense_tu` (functions continuous up to
the boundary are `H¹`-dense).  `RobinCaps/Sobolev/ConvexDensity.lean` proves that density for the
(convex) thin domain.  This file combines the two: the final theorems below hold for every trace
family satisfying the `TraceData` axioms, so they are statements about the Robin eigenvalues of
`Ω_R` and not about one particular construction of the trace.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.ThinDomain

open RobinCaps.Cap RobinCaps.Domain RobinCaps.Sobolev

/-- The density interface of `TraceUnique.lean` holds on every thin domain. -/
theorem c1Dense_tuf {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) : C1Dense_tu Cm Cp L R := by
  intro u η hη
  obtain ⟨v, hv, hclose⟩ := exists_c1_h1_close_cd hR hL u hη
  exact ⟨v, hv.continuous.continuousOn, hclose⟩

/-- **`thm:main`, general `m ≥ 1`, two hemispherical caps, for every trace family.** -/
theorem mainTheorem_hemisphere_any_final (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2, ∃ nu' : ℝ → ℝ,
      ∀ tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀,
        MainTheorem m (hemisphere m) (hemisphere m) L α hL0
          (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf :=
  mainTheorem_hemisphere_any_tu m hm L α hL0 hα
    (fun R hR hL => c1Dense_tuf hR (by linarith))

/-- **`cor:counterexample`, general `m ≥ 1`, for every trace family.** -/
theorem counterexample_hemisphere_any_final (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      ∀ tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L) (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (hemisphere m) (hemisphere m) L R) = L :=
  counterexample_hemisphere_any_tu m hm L α hL0 hα
    (fun R hR hL => c1Dense_tuf hR (by linarith))

/-- **`thm:main` for the single-cap thin domain, general `m ≥ 1`, for every trace family.** -/
theorem mainTheorem_single_any_final (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∀ tdf : TraceFamily (Cap.flat m K hK) (hemisphere m) L R₀,
        MainTheorem m (Cap.flat m K hK) (hemisphere m) L α hL0
          (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf :=
  mainTheorem_single_any_tu m hm K hK L α hL0 hα
    (fun R hR hL => c1Dense_tuf hR hL)

end RobinCaps.ThinDomain
