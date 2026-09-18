import Mathlib
import RobinCaps.Domain.Capsule

/-!
# Explicit values of the ratio `β₀/α = ω_{m+1} / (2 ω_m)`

This file verifies the numerical table in the manuscript
(`reference/robin_endcaps_corrected_en.tex`, `eq:ratios` in `sec:checks`):

  `β₀/α = π/4, 2/3, 3π/16, 8/15` for `n = m + 1 = 2, 3, 4, 5`.

Ingredients: `omega_zero`, `omega_one`, `omega_two` and the two-step recurrence
`omega_rec : ω_{k+2} = 2π/(k+2) · ω_k` (from `RobinCaps.Cap.Sphere`, `Sharp`), and
`beta0 m α = α ω_{m+1} / (2 ω_m)` with `beta0_lt : β₀ < α` (from
`RobinCaps.Domain.Capsule`).

Main results:
* `omega_three : ω₃ = 4π/3`, `omega_four : ω₄ = π²/2`, `omega_five : ω₅ = 8π²/15`;
* `beta0_ratio_one … beta0_ratio_four`: the four entries of `eq:ratios`;
* `beta0_ratio_lt_one : β₀/α < 1` for `m ≥ 1`, `α > 0`.
-/

namespace RobinCaps
namespace Domain

open RobinCaps.Cap

/-! ## Small unit-ball volumes -/

/-- `ω₃ = 4π/3` (volume of the unit ball in `ℝ³`). -/
theorem omega_three : omega 3 = 4 * Real.pi / 3 := by
  have h := omega_rec 1
  rw [omega_one] at h
  norm_num at h
  rw [h]; ring

/-- `ω₄ = π²/2`. -/
theorem omega_four : omega 4 = Real.pi ^ 2 / 2 := by
  have h := omega_rec 2
  rw [omega_two] at h
  norm_num at h
  rw [h]; ring

/-- `ω₅ = 8π²/15`. -/
theorem omega_five : omega 5 = 8 * Real.pi ^ 2 / 15 := by
  have h := omega_rec 3
  rw [omega_three] at h
  norm_num at h
  rw [h]; ring

/-! ## The ratios `β₀/α` of manuscript `eq:ratios` -/

/-- `n = 2` (`m = 1`): `β₀/α = ω₂/(2ω₁) = π/4`. -/
theorem beta0_ratio_one (α : ℝ) (hα : α ≠ 0) : beta0 1 α / α = Real.pi / 4 := by
  unfold beta0
  rw [omega_two, omega_one]
  field_simp
  ring

/-- `n = 3` (`m = 2`): `β₀/α = ω₃/(2ω₂) = 2/3`. -/
theorem beta0_ratio_two (α : ℝ) (hα : α ≠ 0) : beta0 2 α / α = 2 / 3 := by
  unfold beta0
  rw [omega_three, omega_two]
  have hπ := Real.pi_ne_zero
  field_simp
  ring

/-- `n = 4` (`m = 3`): `β₀/α = ω₄/(2ω₃) = 3π/16`. -/
theorem beta0_ratio_three (α : ℝ) (hα : α ≠ 0) :
    beta0 3 α / α = 3 * Real.pi / 16 := by
  unfold beta0
  rw [omega_four, omega_three]
  have hπ := Real.pi_ne_zero
  field_simp
  ring

/-- `n = 5` (`m = 4`): `β₀/α = ω₅/(2ω₄) = 8/15`. -/
theorem beta0_ratio_four (α : ℝ) (hα : α ≠ 0) : beta0 4 α / α = 8 / 15 := by
  unfold beta0
  rw [omega_five, omega_four]
  have hπ := Real.pi_ne_zero
  field_simp

/-! ## `β₀/α < 1` in general -/

/-- For `m ≥ 1` and `α > 0` the ratio `β₀/α` is strictly less than `1`
(the general statement behind `eq:ratios`; from `beta0_lt`). -/
theorem beta0_ratio_lt_one (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) :
    beta0 m α / α < 1 := by
  rw [div_lt_one hα]
  exact beta0_lt hm hα

end Domain
end RobinCaps
