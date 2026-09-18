import Mathlib

/-!
# Pointwise Picone Identity

This file proves the pointwise Picone identity for real inner product spaces:
`‖a‖² − ⟪(2v/ψ) a − (v²/ψ²) b, b⟫ = ‖a − (v/ψ) b‖²`.
This is an algebraic identity useful in the study of Robin cap eigenvalue problems.
-/

noncomputable section

open scoped InnerProductSpace

namespace RobinCaps.Compact

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Pointwise Picone identity.** For reals `v ψ` with `ψ ≠ 0` and vectors `a b`
(think `a = ∇v`, `b = ∇ψ`): `‖a‖² − ⟪(2v/ψ) a − (v²/ψ²) b, b⟫ = ‖a − (v/ψ) b‖²`. -/
theorem picone_pointwise {v ψ : ℝ} (hψ : ψ ≠ 0) (a b : F) :
    ‖a‖ ^ 2 - ⟪(2 * v / ψ) • a - (v ^ 2 / ψ ^ 2) • b, b⟫_ℝ = ‖a - (v / ψ) • b‖ ^ 2 := by
  rw [norm_sub_sq_real]
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  rw [inner_smul_right]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [mul_pow]
  have key : ∀ r : ℝ, (|r| : ℝ) ^ 2 = r ^ 2 := sq_abs
  rw [key]
  field_simp
  ring

/-- The same with the roles of the two arguments of the inner product swapped. -/
theorem picone_pointwise' {v ψ : ℝ} (hψ : ψ ≠ 0) (a b : F) :
    ‖a‖ ^ 2 - ⟪b, (2 * v / ψ) • a - (v ^ 2 / ψ ^ 2) • b⟫_ℝ = ‖a - (v / ψ) • b‖ ^ 2 := by
  rw [show ⟪b, (2 * v / ψ) • a - (v ^ 2 / ψ ^ 2) • b⟫_ℝ =
           ⟪(2 * v / ψ) • a - (v ^ 2 / ψ ^ 2) • b, b⟫_ℝ
       from (real_inner_comm b ((2 * v / ψ) • a - (v ^ 2 / ψ ^ 2) • b)).symm]
  exact picone_pointwise hψ a b

/-- Nonnegativity consequence. -/
theorem picone_pointwise_nonneg {v ψ : ℝ} (hψ : ψ ≠ 0) (a b : F) :
    ⟪(2 * v / ψ) • a - (v ^ 2 / ψ ^ 2) • b, b⟫_ℝ ≤ ‖a‖ ^ 2 := by
  have h : ‖a‖ ^ 2 - ⟪(2 * v / ψ) • a - (v ^ 2 / ψ ^ 2) • b, b⟫_ℝ = ‖a - (v / ψ) • b‖ ^ 2 :=
    picone_pointwise hψ a b
  have h_nonneg : 0 ≤ ‖a - (v / ψ) • b‖ ^ 2 := sq_nonneg _
  linarith [h, h_nonneg]

end RobinCaps.Compact
