import RobinCaps.ThinDomain.EigenFinal
import RobinCaps.ThinDomain.RobinOperator
import RobinCaps.Spectrum.WeakSpectrum

/-!
# Wave 12 (B3): the min–max values are exactly the Robin eigenvalues

Assembly (all hypotheses discharged) of `Spectrum/WeakSpectrum.lean` (abstract: every weak
eigenvalue is a min–max value, min–max values are weak eigenvalues, they tend to `∞`) with the
thin-domain setting `robinSetting_eth` and the Robin operator `IsRobinImage_rop`
(`ThinDomain/RobinOperator.lean`: `−Δu = f` in `Ω_R`, `∂ₙu + α u = 0` on `∂Ω_R`, weakly).

* `lambdaThin_tendsto_atTop_final`: `λ_j(Ω_R; α) → ∞`.
* `weakEigen_eq_lambdaThin_final`: every weak Robin eigenvalue (eigenfunction of positive mass)
  is one of the `λ_j(Ω_R; α)`.
* `robinOperator_spectrum_final`: `μ` is an eigenvalue of the Robin operator (with an
  `H¹` eigenfunction of positive mass) iff `μ = λ_j(Ω_R; α)` for some `j ≥ 1`.
* Headline re-exports `RobinCaps.lambdaThin_tendsto_top`, `RobinCaps.robin_weakEigen_top`,
  `RobinCaps.robin_operator_spectrum_top`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open RobinCaps.Domain RobinCaps.Cap

namespace RobinCaps.ThinDomain

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

theorem h1pComplete_thin_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1PCompleteProp (thinDomain Cm Cp L R) :=
  h1pComplete_h1c (isOpen_thinDomain hR hL).measurableSet

theorem exists_finrank_thin_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (j : ℕ) :
    ∃ V : Submodule ℝ (H1PQ (thinDomain Cm Cp L R)), Module.finrank ℝ V = j :=
  exists_finrank_H1PQ_inf (isOpen_thinDomain hR hL)
    ⟨0, RobinCaps.Sobolev.zero_mem_thinDomain_cd hR hL⟩ j

/-- **`λ_j(Ω_R; α) → ∞`.** -/
theorem lambdaThin_tendsto_atTop_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun j => lambdaThin hR hL td α (j + 1)) atTop atTop := by
  have h := RobinCaps.Spectrum.minmax_tendsto_atTop_wsp
    (robinSetting_eth hR hL td hα (rellichP_thinDomain_final hR hL)
      (h1pComplete_thin_final hR hL)) (exists_finrank_thin_final hR hL)
  refine h.congr fun j => ?_
  exact minmax_robinSetting_eth hR hL td hα _ _ (j + 1)

/-- **Every weak Robin eigenvalue is a min–max value.** -/
theorem weakEigen_eq_lambdaThin_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (u : H1P (thinDomain Cm Cp L R))
    (hu : 0 < massP u) {μ : ℝ}
    (heq : ∀ v : H1P (thinDomain Cm Cp L R),
      dirichletBilinP u v + α * td.bd u v = μ * massBilinP u v) :
    ∃ a : ℕ, μ = lambdaThin hR hL td α (a + 1) := by
  obtain ⟨a, ha⟩ := RobinCaps.Spectrum.weakEigen_eq_minmax_wsp
    (robinSetting_eth hR hL td hα (rellichP_thinDomain_final hR hL)
      (h1pComplete_thin_final hR hL)) (exists_finrank_thin_final hR hL)
    ((mk_ne_zero_iff_rop u).2 hu)
    ((eigen_quotient_rop hR hL td hα _ _ u μ).1 heq)
  exact ⟨a, ha.trans (minmax_robinSetting_eth hR hL td hα _ _ (a + 1))⟩

/-- **Every min–max value is a weak Robin eigenvalue** (with an eigenfunction of positive mass). -/
theorem lambdaThin_isWeakEigen_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (a : ℕ) :
    ∃ u : H1P (thinDomain Cm Cp L R), 0 < massP u ∧
      ∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP u v + α * td.bd u v = lambdaThin hR hL td α (a + 1) * massBilinP u v := by
  obtain ⟨w, hw0, hw⟩ := RobinCaps.Spectrum.minmax_isWeakEigen_wsp
    (robinSetting_eth hR hL td hα (rellichP_thinDomain_final hR hL)
      (h1pComplete_thin_final hR hL)) (exists_finrank_thin_final hR hL) a
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) w
  refine ⟨u, (mk_ne_zero_iff_rop u).1 hw0, ?_⟩
  rw [← minmax_robinSetting_eth hR hL td hα (rellichP_thinDomain_final hR hL)
    (h1pComplete_thin_final hR hL) (a + 1)]
  exact (eigen_quotient_rop hR hL td hα _ _ u _).2 hw

/-- **The eigenvalues of the Robin operator are exactly the min–max values.** -/
theorem robinOperator_spectrum_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (μ : ℝ) :
    (∃ u : H1P (thinDomain Cm Cp L R), 0 < massP u ∧ IsRobinImage_rop td α u (μ • u.toFun)) ↔
      ∃ a : ℕ, μ = lambdaThin hR hL td α (a + 1) := by
  constructor
  · rintro ⟨u, hu, himg⟩
    exact weakEigen_eq_lambdaThin_final hR hL td hα u hu (isRobinImage_eigen_iff_rop.1 himg)
  · rintro ⟨a, rfl⟩
    obtain ⟨u, hu, heq⟩ := lambdaThin_isWeakEigen_final hR hL td hα a
    exact ⟨u, hu, isRobinImage_eigen_iff_rop.2 heq⟩

end RobinCaps.ThinDomain

namespace RobinCaps

open RobinCaps.ThinDomain

/-- **`λ_j(Ω_R; α) → ∞`** (headline re-export). -/
theorem lambdaThin_tendsto_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun j => lambdaThin hR hL td α (j + 1)) atTop atTop :=
  lambdaThin_tendsto_atTop_final hR hL td hα

/-- **The weak Robin eigenvalues are exactly the min–max values** (headline re-export). -/
theorem robin_weakEigen_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (μ : ℝ) :
    (∃ u : H1P (thinDomain Cm Cp L R), 0 < massP u ∧
        ∀ v : H1P (thinDomain Cm Cp L R),
          dirichletBilinP u v + α * td.bd u v = μ * massBilinP u v) ↔
      ∃ a : ℕ, μ = lambdaThin hR hL td α (a + 1) := by
  constructor
  · rintro ⟨u, hu, heq⟩
    exact weakEigen_eq_lambdaThin_final hR hL td hα u hu heq
  · rintro ⟨a, rfl⟩
    exact lambdaThin_isWeakEigen_final hR hL td hα a

/-- **The eigenvalues of the Robin operator are exactly the min–max values** (headline
re-export). -/
theorem robin_operator_spectrum_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (μ : ℝ) :
    (∃ u : H1P (thinDomain Cm Cp L R), 0 < massP u ∧ IsRobinImage_rop td α u (μ • u.toFun)) ↔
      ∃ a : ℕ, μ = lambdaThin hR hL td α (a + 1) :=
  robinOperator_spectrum_final hR hL td hα μ

end RobinCaps

end
