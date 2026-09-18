import RobinCaps.ThinDomain.MainSingle
import RobinCaps.Cap.TraceDataFlatDerived

/-!
# The single-cap case `eq:single-cap`, general `m`: the flat-cap inputs discharged

`RobinCaps/ThinDomain/MainSingle.lean` proves `thm:main` for the single-cap thin domain
(flat left end `Cap.flat m K hK`, hemispherical right cap) modulo three hypotheses.  Two of them
concern the flat cap's trace datum and are proved in `RobinCaps/Cap/TraceDataFlatDerived.lean`
(`capTraceIntegrableAbs_flat_tfd`, `flatLiftBd_tfd`).  After this file the only remaining
hypothesis is the entrance-trace bound `CapEntranceL2 (Cap.hemisphere m) C₁` of the
hemispherical cap (discharged for `m = 1` by `Cap.capEntranceL2_hemi_el`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.ThinDomain

open RobinCaps.Cap

/-- **`thm:main` for the single-cap thin domain, general `m ≥ 1`**, modulo the hemisphere entrance
bound only. -/
theorem mainTheorem_single_msf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) {C₁' : ℝ} (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0
        (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf :=
  mainTheorem_single_ms m hm K hK L α hL0 hα (capTraceIntegrableAbs_flat_tfd m hm K hK)
    (flatLiftBd_tfd m hm K hK) henH

/-- **`eq:single-cap`**: `λ_j(Ω_R;α) − ν_R = μ_j(α, β₊; L) + O(R)`, the flat end contributing the
Robin parameter `α` itself as its effective end coefficient. -/
theorem mainTheorem_single_alpha_msf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) {C₁' : ℝ} (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      ∀ J : ℕ, ∃ C R₁' : ℝ, 0 ≤ C ∧ 0 < R₁' ∧ R₁' ≤ R₀ ∧
        ∀ (R : ℝ) (hR : 0 < R) (hRR₀ : R < R₀) (_hR₁ : R < R₁')
          (hLR : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (j : ℕ) (hj : 1 ≤ j),
          j ≤ J →
          |lambdaThin hR hLR (tdf R hR hRR₀) α j - nu' R
              - Interval.mu α ((Cap.hemisphere m).beta α) L j hα (hemisphere_beta_pos m hm hα)
                  hL0 hj| ≤ C * R :=
  mainTheorem_single_alpha_ms m hm K hK L α hL0 hα (capTraceIntegrableAbs_flat_tfd m hm K hK)
    (flatLiftBd_tfd m hm K hK) henH

end RobinCaps.ThinDomain
