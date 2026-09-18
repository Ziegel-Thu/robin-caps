import RobinCaps.ThinDomain.MainGen
import RobinCaps.ThinDomain.MainSingleFlat
import RobinCaps.Cap.ShortSliceHemi

/-!
# `thm:main`, `cor:counterexample` and `eq:single-cap` for every `m ≥ 1` — unconditional

The last interface of the general-`m` chain, the entrance-trace bound
`CapEntranceL2 (Cap.hemisphere m) C₁` of the unit hemispherical cap, is discharged by
`RobinCaps/Cap/ShortSliceHemi.lean: capEntranceL2_hemi_ssh`.  This file instantiates it in
`RobinCaps/ThinDomain/MainGen.lean` (two hemispherical caps) and
`RobinCaps/ThinDomain/MainSingleFlat.lean` (flat left end, hemispherical right cap).
The resulting theorems have **no interface hypotheses left**: only `1 ≤ m`, `0 < L`, `0 < α`
(and `0 < K` for the bookkeeping length of the flat end).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.ThinDomain

open RobinCaps.Cap RobinCaps.Domain

/-- **`thm:main` for every `m ≥ 1`, two hemispherical caps, unconditional.** -/
theorem mainTheorem_hemisphere_gen_final (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.hemisphere m) (Cap.hemisphere m) L α hL0
        (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf := by
  obtain ⟨C₁, hen⟩ := capEntranceL2_hemi_ssh m hm
  exact mainTheorem_hemisphere_gen_mg m hm L α hL0 hα hen

/-- **`cor:counterexample` (`eq:counterexample`, `eq:finite-deficit`) for every `m ≥ 1`,
unconditional**: for all sufficiently small `R` the variational Robin eigenvalues of the capsule
`Ω_R` satisfy `λ₂ − λ₁ ≤ G_α(L) − Δ/2 < G_α(L)` while `diam Ω_R = L`. -/
theorem counterexample_hemisphere_gen_final (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
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
        euclidDiam (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) = L := by
  obtain ⟨C₁, hen⟩ := capEntranceL2_hemi_ssh m hm
  exact counterexample_hemisphere_gen_mg m hm L α hL0 hα hen

/-- **`thm:main` for the single-cap thin domain (flat left end, hemispherical right cap), every
`m ≥ 1`, unconditional.** -/
theorem mainTheorem_single_final (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0
        (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf := by
  obtain ⟨C₁, hen⟩ := capEntranceL2_hemi_ssh m hm
  exact mainTheorem_single_msf m hm K hK L α hL0 hα hen

/-- **`eq:single-cap`, unconditional**: `λ_j(Ω_R;α) − ν_R = μ_j(α, β₊; L) + O(R)` for the
single-cap thin domain, the flat end contributing the Robin parameter `α` as its end
coefficient. -/
theorem mainTheorem_single_alpha_final (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      ∀ J : ℕ, ∃ C R₁' : ℝ, 0 ≤ C ∧ 0 < R₁' ∧ R₁' ≤ R₀ ∧
        ∀ (R : ℝ) (hR : 0 < R) (hRR₀ : R < R₀) (_hR₁ : R < R₁')
          (hLR : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (j : ℕ) (hj : 1 ≤ j),
          j ≤ J →
          |lambdaThin hR hLR (tdf R hR hRR₀) α j - nu' R
              - Interval.mu α ((Cap.hemisphere m).beta α) L j hα (hemisphere_beta_pos m hm hα)
                  hL0 hj| ≤ C * R := by
  obtain ⟨C₁, hen⟩ := capEntranceL2_hemi_ssh m hm
  exact mainTheorem_single_alpha_msf m hm K hK L α hL0 hα hen

end RobinCaps.ThinDomain
