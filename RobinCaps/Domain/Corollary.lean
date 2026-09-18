import RobinCaps.Interval.Gap
import RobinCaps.Domain.Capsule

/-!
# The capsule counterexample, real-analysis step (`cor:counterexample`)

This file closes the *one-dimensional / real-analysis* part of the manuscript's
Corollary `cor:counterexample` (`reference/robin_endcaps_corrected_en.tex`,
Section `sec:capsule`), as a **conditional** theorem.

## What is proved here

* `gap_beta0_lt_gap_alpha`: `G_{β₀}(L) < G_α(L)` for `m ≥ 1`, `L > 0`, `α > 0`,
  where `G_β(L) = μ₂(β,β;L) − μ₁(β,β;L)` is the interval Robin gap
  (`RobinCaps.Interval.gap`) and `β₀ = α ω_{m+1}/(2 ω_m)` is the hemispherical-cap
  constant (`RobinCaps.Domain.beta0`).  This combines the strict monotonicity
  `prop:gap-monotone` (`Interval.gap_strictMonoOn`) with `0 < β₀ < α`
  (`beta0_pos`, `beta0_lt`).
* `Delta m L hL α := G_α(L) − G_{β₀}(L)` and `Delta_pos : 0 < Delta`.
* `counterexample_of_asymptotics`: **assuming** the two-term spectral asymptotics
  `|λ_j(Ω_R) − ν_R − μ_j(β₀,β₀;L)| ≤ C R` for `j = 1, 2` and `0 < R < R₀`, there is
  `R₁ > 0` such that for `0 < R < R₁`
  `λ₂ − λ₁ ≤ G_α(L) − Δ/2` (manuscript `eq:finite-deficit`) and in particular
  `λ₂ − λ₁ < G_α(L)`.
* `counterexample_of_asymptotics_diam`: the same, with the right-hand side
  recognised as `G_α(diam Ω_R)` via `diam_capsule : Metric.diam (capsule m L R) = L`
  (manuscript `eq:exact-diameter`), so that the conclusion is literally
  `eq:counterexample`.

## What is NOT proved here

The hypotheses `h₁`, `h₂` of `counterexample_of_asymptotics` — the asymptotics
`λ_j(Ω_R; α) = ν_R + μ_j(β₀, β₀; L) + O(R)` for the first two Robin eigenvalues of
the hemispherical capsule `Ω_R` — are the content of the manuscript's main theorem
`thm:main` specialised to hemispherical caps.  They are **not formalised in this
project yet**; they enter this file only as explicit hypotheses on abstract
functions `lam₁ lam₂ nu : ℝ → ℝ` (eigenvalue branches and the transverse ground
energy `ν_R`).  In particular nothing here defines the Robin Laplacian on the
capsule or its eigenvalues.  Once those asymptotics are formalised, instantiating
`lam₁, lam₂, nu, C, R₀` in `counterexample_of_asymptotics_diam` yields the full
corollary.

The constant `R₁ := min R₀ (Δ / (4C + 4))` is a harmless variant of the manuscript's
`min(R_J, Δ/(4C))` that avoids division by zero when `C = 0`.
-/

open Set

namespace RobinCaps
namespace Domain

noncomputable section

/-- **`G_{β₀}(L) < G_α(L)`**: the interval gap at the hemispherical-cap constant is
strictly smaller than the gap at the original Robin parameter (manuscript,
proof of `cor:counterexample`, via `prop:gap-monotone` and `0 < β₀ < α`). -/
theorem gap_beta0_lt_gap_alpha (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 0 < L)
    (α : ℝ) (hα : 0 < α) :
    Interval.gap L hL (beta0 m α) < Interval.gap L hL α :=
  Interval.gap_strictMonoOn L hL (beta0_pos hα) hα (beta0_lt hm hα)

/-- The gap deficit `Δ = G_α(L) − G_{β₀}(L)` of `cor:counterexample`. -/
def Delta (m : ℕ) (L : ℝ) (hL : 0 < L) (α : ℝ) : ℝ :=
  Interval.gap L hL α - Interval.gap L hL (beta0 m α)

/-- `Δ > 0` for `m ≥ 1`, `L > 0`, `α > 0`. -/
theorem Delta_pos (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 0 < L) (α : ℝ) (hα : 0 < α) :
    0 < Delta m L hL α :=
  sub_pos.mpr (gap_beta0_lt_gap_alpha m hm L hL α hα)

/-- **The abstract counterexample (`cor:counterexample`, `eq:finite-deficit`).**

Let `lam₁ lam₂ : ℝ → ℝ` be the first two Robin eigenvalues of the capsule as
functions of the cap radius `R`, and `nu : ℝ → ℝ` the transverse ground energy
`ν_R`.  *Assume* (this is `thm:main`, not proved here) that for `0 < R < R₀`
`|λ_j(R) − ν_R − μ_j(β₀,β₀;L)| ≤ C R` for `j = 1, 2`.  Then there is `R₁ > 0` such
that for all `0 < R < R₁`
`λ₂(R) − λ₁(R) ≤ G_α(L) − Δ/2` and `λ₂(R) − λ₁(R) < G_α(L)`. -/
theorem counterexample_of_asymptotics (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 0 < L)
    (α : ℝ) (hα : 0 < α) (lam₁ lam₂ nu : ℝ → ℝ) (C R₀ : ℝ) (hR₀ : 0 < R₀) (hC : 0 ≤ C)
    (h₁ : ∀ R, 0 < R → R < R₀ →
      |lam₁ R - nu R - Interval.mu (beta0 m α) (beta0 m α) L 1
        (beta0_pos hα) (beta0_pos hα) hL (le_refl 1)| ≤ C * R)
    (h₂ : ∀ R, 0 < R → R < R₀ →
      |lam₂ R - nu R - Interval.mu (beta0 m α) (beta0 m α) L 2
        (beta0_pos hα) (beta0_pos hα) hL (by norm_num)| ≤ C * R) :
    ∃ R₁, 0 < R₁ ∧ ∀ R, 0 < R → R < R₁ →
      lam₂ R - lam₁ R ≤ Interval.gap L hL α - Delta m L hL α / 2 ∧
      lam₂ R - lam₁ R < Interval.gap L hL α := by
  have hΔ : 0 < Delta m L hL α := Delta_pos m hm L hL α hα
  have hden : 0 < 4 * C + 4 := by positivity
  refine ⟨min R₀ (Delta m L hL α / (4 * C + 4)), lt_min hR₀ (div_pos hΔ hden), ?_⟩
  intro R hR hR₁
  have hRR₀ : R < R₀ := lt_of_lt_of_le hR₁ (min_le_left _ _)
  have hRΔ : R < Delta m L hL α / (4 * C + 4) := lt_of_lt_of_le hR₁ (min_le_right _ _)
  have hRΔ' : R * (4 * C + 4) < Delta m L hL α := (lt_div_iff₀ hden).mp hRΔ
  -- the error term is at most `Δ/4`
  have hCR : C * R ≤ Delta m L hL α / 4 := by nlinarith
  have e₁ := abs_le.mp (h₁ R hR hRR₀)
  have e₂ := abs_le.mp (h₂ R hR hRR₀)
  have hgap := Interval.gap_eq_mu L hL (beta0_pos (m := m) hα)
  have hΔdef : Delta m L hL α
      = Interval.gap L hL α - Interval.gap L hL (beta0 m α) := rfl
  constructor
  · linarith [e₁.1, e₁.2, e₂.1, e₂.2]
  · linarith [e₁.1, e₁.2, e₂.1, e₂.2]

/-- **`cor:counterexample`, `eq:counterexample`, with the diameter.**
Under the same (unproved) asymptotic hypotheses, for `0 < R < R₁` with `2R < L`
one has `λ₂(R) − λ₁(R) < G_α(L)` and `diam (capsule m L R) = L`, i.e.
`λ₂(Ω_R) − λ₁(Ω_R) < G_α(diam Ω_R)`. -/
theorem counterexample_of_asymptotics_diam (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 0 < L)
    (α : ℝ) (hα : 0 < α) (lam₁ lam₂ nu : ℝ → ℝ) (C R₀ : ℝ) (hR₀ : 0 < R₀) (hC : 0 ≤ C)
    (h₁ : ∀ R, 0 < R → R < R₀ →
      |lam₁ R - nu R - Interval.mu (beta0 m α) (beta0 m α) L 1
        (beta0_pos hα) (beta0_pos hα) hL (le_refl 1)| ≤ C * R)
    (h₂ : ∀ R, 0 < R → R < R₀ →
      |lam₂ R - nu R - Interval.mu (beta0 m α) (beta0 m α) L 2
        (beta0_pos hα) (beta0_pos hα) hL (by norm_num)| ≤ C * R) :
    ∃ R₁, 0 < R₁ ∧ ∀ R, 0 < R → R < R₁ → 2 * R < L →
      lam₂ R - lam₁ R < Interval.gap L hL α ∧
      Metric.diam (capsule m L R) = L := by
  obtain ⟨R₁, hR₁, h⟩ :=
    counterexample_of_asymptotics m hm L hL α hα lam₁ lam₂ nu C R₀ hR₀ hC h₁ h₂
  exact ⟨R₁, hR₁, fun R hR hRR₁ h2R => ⟨(h R hR hRR₁).2, diam_capsule hR h2R⟩⟩

/-- **Quantitative form with the diameter** (`eq:counterexample` + `eq:finite-deficit`):
under the asymptotics, for small `R` the gap deficit is at least `Δ/2` and
`diam Ω_R = L`. -/
theorem counterexample_of_asymptotics_diam' (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 0 < L)
    (α : ℝ) (hα : 0 < α) (lam₁ lam₂ nu : ℝ → ℝ) (C R₀ : ℝ) (hR₀ : 0 < R₀) (hC : 0 ≤ C)
    (h₁ : ∀ R, 0 < R → R < R₀ →
      |lam₁ R - nu R - Interval.mu (beta0 m α) (beta0 m α) L 1
        (beta0_pos hα) (beta0_pos hα) hL (le_refl 1)| ≤ C * R)
    (h₂ : ∀ R, 0 < R → R < R₀ →
      |lam₂ R - nu R - Interval.mu (beta0 m α) (beta0 m α) L 2
        (beta0_pos hα) (beta0_pos hα) hL (by norm_num)| ≤ C * R) :
    ∃ R₁, 0 < R₁ ∧ ∀ R, 0 < R → R < R₁ → 2 * R < L →
      lam₂ R - lam₁ R ≤ Interval.gap L hL α - Delta m L hL α / 2 ∧
      lam₂ R - lam₁ R < Interval.gap L hL α ∧
      Metric.diam (capsule m L R) = L := by
  obtain ⟨R₁, hR₁, h⟩ :=
    counterexample_of_asymptotics m hm L hL α hα lam₁ lam₂ nu C R₀ hR₀ hC h₁ h₂
  exact ⟨R₁, hR₁, fun R hR hRR₁ h2R =>
    ⟨(h R hR hRR₁).1, (h R hR hRR₁).2, diam_capsule hR h2R⟩⟩

end

end Domain
end RobinCaps
