import RobinCaps.Domain.Capsule
import RobinCaps.Cap.Main

/-!
# The hemispherical cap realises `β₀`

`β(hemisphere m) = β₀ = α ω_{m+1}/(2 ω_m)` for the paper's coefficient `Cap.beta`,
and every admissible cap has `β(C) ≥ β(hemisphere m)` (`eq:positive-beta`). -/

namespace RobinCaps.Domain

open RobinCaps.Cap

/-- `β(hemisphere m) = β₀` (manuscript `eq:positive-beta`, equality case). -/
theorem hemisphere_beta_eq_beta0 (m : ℕ) (hm : 1 ≤ m) (α : ℝ) :
    (hemisphere m).beta α = beta0 m α := by
  rw [Cap.beta, F_eq_revolutionF]
  exact hemisphere_revolutionF_ratio m hm α

/-- Every admissible cap has `β(C) ≥ β₀ = β(hemisphere m)`. -/
theorem beta_ge_hemisphere_beta (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hK : C.θ (-C.K) = 1) (h0 : TerminalContinuous C) {α : ℝ} (hα : 0 < α) :
    C.beta α ≥ (hemisphere m).beta α := by
  rw [hemisphere_beta_eq_beta0 m hm α]
  exact (beta_ge_beta0 m hm C hK h0 hα).1

end RobinCaps.Domain
