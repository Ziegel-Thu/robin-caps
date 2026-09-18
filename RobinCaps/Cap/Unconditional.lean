import RobinCaps.Cap.EqualityAC
import RobinCaps.Domain.HemisphereBeta

/-!
# `thm:calibration` without endpoint hypotheses

The theorems of `Cap/Main.lean` and `Cap/EqualityAC.lean` carry the two hypotheses
`C.θ (-C.K) = 1` and `TerminalContinuous C`.  They are the storage conventions of the `Cap`
structure (fields `θ_entrance`, `θ_terminal`: the recorded endpoint values are the one-sided
limits of the profile), so they hold for every cap.  This file restates the sharp cap inequality,
the equality characterisation and the positivity of `β` with no hypotheses beyond `1 ≤ m`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps
namespace Cap

variable {m : ℕ}

/-- Every cap is left-continuous at its terminal point (storage convention `θ_terminal`). -/
theorem terminalContinuous (C : Cap m) : TerminalContinuous C := C.θ_terminal

/-- **`thm:calibration`, `eq:sharp-geometric`**: every admissible cap satisfies
`𝓕(C) = ℋ^m(Γ) − m|C| ≥ ω_{m+1}/2`. -/
theorem sharp_cap_inequality_uc (m : ℕ) (hm : 1 ≤ m) (C : Cap m) :
    C.F ≥ omega (m + 1) / 2 :=
  sharp_cap_inequality_F m hm C C.θ_entrance C.terminalContinuous

/-- **`eq:positive-beta`**: `β(C) ≥ β₀ = α ω_{m+1}/(2 ω_m) > 0`. -/
theorem beta_ge_beta0_uc (m : ℕ) (hm : 1 ≤ m) (C : Cap m) {α : ℝ} (hα : 0 < α) :
    C.beta α ≥ α * omega (m + 1) / (2 * omega m) ∧ 0 < α * omega (m + 1) / (2 * omega m) :=
  beta_ge_beta0 m hm C C.θ_entrance C.terminalContinuous hα

/-- **`thm:calibration`, equality case (`eq:equality-profile`)**: `𝓕(C) = ω_{m+1}/2` iff the
cap is the unit hemisphere, possibly extended at the entrance by a unit cylinder. -/
theorem equality_iff_uc (m : ℕ) (hm : 1 ≤ m) (C : Cap m) :
    C.F = omega (m + 1) / 2 ↔ EqualityProfile C :=
  EqualityAC.equality_iff_AC m hm C C.θ_entrance C.terminalContinuous

/-- The target `EqualityCharacterization` of `Cap/SharpInequality.lean` holds. -/
theorem equalityCharacterization_uc (m : ℕ) (hm : 1 ≤ m) : EqualityCharacterization m :=
  fun C => equality_iff_uc m hm C

end Cap

namespace Domain

/-- Every admissible cap has `β(C) ≥ β(hemisphere)`. -/
theorem beta_ge_hemisphere_beta_uc (m : ℕ) (hm : 1 ≤ m) (C : Cap m) {α : ℝ} (hα : 0 < α) :
    C.beta α ≥ (Cap.hemisphere m).beta α :=
  beta_ge_hemisphere_beta m hm C C.θ_entrance C.terminalContinuous hα

end Domain
end RobinCaps
