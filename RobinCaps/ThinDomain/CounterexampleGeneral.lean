import RobinCaps.ThinDomain.MainGeneralFinal
import RobinCaps.Interval.Smooth
import RobinCaps.Domain.ThinDiam

/-!
# `cor:counterexample` for an arbitrary admissible cap with sub-critical coefficient

`RobinCaps/ThinDomain/NuBall.lean` proves the capsule counterexample
(`counterexample_of_mainTheorem'`) only for the *hemispherical* end caps, where the true
Euclidean diameter of the thin domain happens to equal `L` exactly
(`Domain.euclidDiam_thinDomain_hemisphere`). This file generalizes the mechanism (manuscript
`sec:nearflat`, Section 8.2) to **any** admissible cap `C : Cap m` with sub-critical effective coefficient
`β(C,α) < α`, comparing against the interval gap evaluated at the *true* diameter of the thin
domain `Ω_R`, which for a general cap only satisfies the two-sided bound `eq:diam-bound`
`L ≤ diam Ω_R ≤ √(L² + 4R²) ≤ L + 2R²/L` (`Domain.euclidDiam_thinDomain_bounds`), not an exact
equality.

## What is proved here

* `gap_length_tendsto_cg`: a one-sided continuity estimate for the interval gap `G_α` in the
  *length* variable: `G_α(D) > G_α(L) - ε` for `D` close enough to `L` from above. This is proved
  directly from the explicit local Lipschitz bound `Interval.mu_perturbation_bound` for `μ_1` and
  `μ_2` at the fixed parameter `α`, without needing the scaling law or the derivative formula for
  `G_β(L)` in `β`.
* `counterexample_of_beta_lt_cg`: assuming only `thm:main` (`mainTheorem_general_nb`, proved
  unconditionally for every pair of admissible caps in `MainGeneralFinal.lean`), attaching two
  copies of a sub-critical cap `C` (`β(C,α) < α`) to the thin domain, for all small `R`
  `λ₂(Ω_R;α) − λ₁(Ω_R;α) < G_α(diam Ω_R)`, where `diam Ω_R` is the genuine Euclidean diameter of
  the thin domain (not the length parameter `L`).

  The mechanism: `G_β(L) < G_α(L)` (`Interval.gap_strictMonoOn`, since `β < α`) gives a gap
  deficit `Δ = G_α(L) - G_β(L) > 0`; `thm:main` with `J = 2` gives
  `λ₂ − λ₁ ≤ G_β(L) + 2 C_J R`; and `diam Ω_R ≤ L + 2R²/L → L` as `R → 0`, so `G_α(diam Ω_R)` is,
  by `gap_length_tendsto_cg`, eventually within `Δ/2` of `G_α(L)` from below, closing the gap.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

set_option linter.unusedSectionVars false

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap

/-! ## Continuity of the interval gap in the length variable -/

/-- **One-sided continuity of the interval gap `G_α(L)` in the length variable `L`.**
For fixed `α > 0`, `G_α(D) > G_α(L) - ε` once `D ∈ [L, L + η]` for `η` small enough (depending on
`ε`). Proved from the explicit Lipschitz bound `Interval.mu_perturbation_bound` applied to `μ_1`
and `μ_2` at the common (fixed) endpoint parameter `α`, via `Interval.gap_eq_mu`. Only this
one-sided lower bound is needed for `counterexample_of_beta_lt_cg`. -/
theorem gap_length_tendsto_cg (L α : ℝ) (hL : 0 < L) (hα : 0 < α) :
    ∀ ε > 0, ∃ η > 0, ∀ (D : ℝ) (hD : 0 < D), L ≤ D → D ≤ L + η →
      Interval.gap L hL α - ε < Interval.gap D hD α := by
  intro ε hε
  obtain ⟨C1, δ1, hδ1pos, hC1⟩ := Interval.mu_perturbation_bound 1 (by norm_num) α α L hα hα hL
  obtain ⟨C2, δ2, hδ2pos, hC2⟩ := Interval.mu_perturbation_bound 2 (by norm_num) α α L hα hα hL
  set M : ℝ := |C1| + |C2| + 1 with hMdef
  have hMpos : 0 < M := by positivity
  refine ⟨min δ1 (min δ2 (ε / (4 * M))), lt_min hδ1pos (lt_min hδ2pos
    (div_pos hε (by positivity))), ?_⟩
  intro D hD hLD hDL
  have hDLnonneg : 0 ≤ D - L := by linarith
  have hDLη : D - L ≤ min δ1 (min δ2 (ε / (4 * M))) := by linarith
  have hDLδ1 : |D - L| ≤ δ1 := by
    rw [abs_of_nonneg hDLnonneg]; exact le_trans hDLη (min_le_left _ _)
  have hDLδ2 : |D - L| ≤ δ2 := by
    rw [abs_of_nonneg hDLnonneg]
    exact le_trans hDLη (le_trans (min_le_right _ _) (min_le_left _ _))
  have hDLε : D - L ≤ ε / (4 * M) :=
    le_trans hDLη (le_trans (min_le_right _ _) (min_le_right _ _))
  have hz1 : |α - α| ≤ δ1 := by rw [sub_self, abs_zero]; exact hδ1pos.le
  have hz2 : |α - α| ≤ δ2 := by rw [sub_self, abs_zero]; exact hδ2pos.le
  have e1 := hC1 α α D hz1 hz1 hDLδ1 hα hα hD
  have e2 := hC2 α α D hz2 hz2 hDLδ2 hα hα hD
  simp only [sub_self, abs_zero, zero_add] at e1 e2
  rw [abs_of_nonneg hDLnonneg] at e1 e2
  have h1 := abs_le.mp e1
  have h2 := abs_le.mp e2
  have hC1M : C1 ≤ M := by
    have h := le_abs_self C1
    rw [hMdef]; linarith [abs_nonneg C2]
  have hC2M : C2 ≤ M := by
    have h := le_abs_self C2
    rw [hMdef]; linarith [abs_nonneg C1]
  have hC12 : C1 + C2 ≤ 2 * M := by linarith
  have hstep : (C1 + C2) * (D - L) ≤ (2 * M) * (D - L) :=
    mul_le_mul_of_nonneg_right hC12 hDLnonneg
  have hstep2 : (2 * M) * (D - L) ≤ (2 * M) * (ε / (4 * M)) :=
    mul_le_mul_of_nonneg_left hDLε (by linarith)
  have hstep3 : (2 * M) * (ε / (4 * M)) = ε / 2 := by field_simp; ring
  have hbound : C1 * (D - L) + C2 * (D - L) ≤ ε / 2 := by nlinarith [hstep, hstep2, hstep3]
  rw [Interval.gap_eq_mu L hL hα, Interval.gap_eq_mu D hD hα]
  linarith [h1.1, h1.2, h2.1, h2.2, hbound]

/-! ## The generalized counterexample -/

/-- **`cor:counterexample` for an arbitrary admissible cap with sub-critical effective
coefficient.**

Let `C : Cap m` be any admissible cap with `β(C,α) < α`, and attach two copies of `C` as the two
end caps of the thin domain (manuscript `sec:nearflat`, Section 8.2). Assuming only `thm:main`
(`mainTheorem_general_nb`, proved unconditionally in `MainGeneralFinal.lean` for every pair of
admissible caps), for all sufficiently small `R` the genuine Robin eigenvalues of the thin domain
violate the conjectured gap bound at the *true* Euclidean diameter of `Ω_R`:

`λ₂(Ω_R;α) − λ₁(Ω_R;α) < G_α(diam Ω_R)`.

This generalizes `counterexample_of_mainTheorem'` (hemispherical caps only, where
`diam Ω_R = L` exactly) to an arbitrary sub-critical cap, comparing against the interval gap at
the true, only two-sidedly bounded, diameter `L ≤ diam Ω_R ≤ √(L² + 4R²) ≤ L + 2R²/L`
(`Domain.euclidDiam_thinDomain_bounds`). -/
theorem counterexample_of_beta_lt_cg (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) (hβ : C.beta α < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (C.K + C.K) * R₀ ≤ L,
      Nonempty (TraceFamily C C L R₀) ∧
      ∀ tdf : TraceFamily C C L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
        ∀ (R : ℝ) (hR : 0 < R), R < R₁ →
          ∀ (hLR : (C.K + C.K) * R < L) (hR₀' : R < R₀)
            (hD : 0 < euclidDiam (thinDomain C C L R)),
            lambdaThin hR hLR (tdf R hR hR₀') α 2 - lambdaThin hR hLR (tdf R hR hR₀') α 1
              < Interval.gap (euclidDiam (thinDomain C C L R)) hD α := by
  obtain ⟨R₀, hR₀, hR₀L, hne, hall⟩ := mainTheorem_general_nb m hm C C L α hL0 hα
  refine ⟨R₀, hR₀, hR₀L, hne, fun tdf => ?_⟩
  have hβpos : 0 < C.beta α := cap_beta_pos_bg2 m hm C hα
  have hΔpos : 0 < Interval.gap L hL0 α - Interval.gap L hL0 (C.beta α) :=
    sub_pos.mpr (Interval.gap_strictMonoOn L hL0 hβpos hα hβ)
  set Δ : ℝ := Interval.gap L hL0 α - Interval.gap L hL0 (C.beta α) with hΔdef
  obtain ⟨η, hηpos, hcont⟩ := gap_length_tendsto_cg L α hL0 hα (Δ / 2) (by linarith)
  obtain ⟨Cc, R₁', hCc0, hR₁'pos, hR₁'le, hbound⟩ := hall tdf 2
  have hCc1pos : 0 < 4 * (Cc + 1) := by linarith
  set R₁ : ℝ := min R₁' (min (Δ / (4 * (Cc + 1))) (Real.sqrt (η * L / 2))) with hR₁def
  have hR₁pos : 0 < R₁ :=
    lt_min hR₁'pos (lt_min (div_pos hΔpos hCc1pos) (Real.sqrt_pos.mpr (by positivity)))
  refine ⟨R₁, hR₁pos, ?_⟩
  intro R hR hRR₁ hLR hR₀' hD
  have hRR₁' : R < R₁' := lt_of_lt_of_le hRR₁ (min_le_left _ _)
  have hRΔ : R < Δ / (4 * (Cc + 1)) :=
    lt_of_lt_of_le hRR₁ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRsqrt : R < Real.sqrt (η * L / 2) :=
    lt_of_lt_of_le hRR₁ (le_trans (min_le_right _ _) (min_le_right _ _))
  -- error-term control: `C_c R < Δ / 4`, hence `2 C_c R < Δ / 2`
  have hmul : R * (4 * (Cc + 1)) < Δ := (lt_div_iff₀ hCc1pos).mp hRΔ
  have hCcR : Cc * R < Δ / 4 := by nlinarith [hmul, hR, hCc0]
  -- radius control: `2 R² / L ≤ η`
  have hRηL : R ^ 2 < η * L / 2 := (Real.lt_sqrt hR.le).mp hRsqrt
  have h2R2L : 2 * R ^ 2 / L ≤ η := by
    rw [div_le_iff₀ hL0]; nlinarith [hRηL]
  -- the diameter estimate
  have hLd : L ≤ euclidDiam (thinDomain C C L R) := le_euclidDiam_thinDomain hR hLR
  have hDadd : euclidDiam (thinDomain C C L R) ≤ L + 2 * R ^ 2 / L :=
    euclidDiam_thinDomain_le_add hR hLR
  have hDη : euclidDiam (thinDomain C C L R) ≤ L + η := by linarith
  have hgapcont := hcont (euclidDiam (thinDomain C C L R)) hD hLd hDη
  -- the two-term asymptotics at `j = 1, 2`, at the sub-critical parameter `β = C.beta α`
  have e1 := hbound R hR hR₀' hRR₁' hLR 1 (le_refl 1) (by norm_num)
  have e2 := hbound R hR hR₀' hRR₁' hLR 2 (by norm_num) (le_refl 2)
  have h1 := abs_le.mp e1
  have h2 := abs_le.mp e2
  have hgapbeta := Interval.gap_eq_mu L hL0 hβpos
  have hlam : lambdaThin hR hLR (tdf R hR hR₀') α 2 - lambdaThin hR hLR (tdf R hR hR₀') α 1
      < Interval.gap L hL0 α - Δ / 2 := by
    linarith [h1.1, h1.2, h2.1, h2.2, hgapbeta, hΔdef, hCcR]
  linarith [hlam, hgapcont]

end RobinCaps.ThinDomain
