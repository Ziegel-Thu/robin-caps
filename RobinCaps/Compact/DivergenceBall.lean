import RobinCaps.Compact.BoundaryForm
import RobinCaps.Compact.GroundStateGap

/-!
# The divergence theorem on the ball for radial vector fields

This file proves the divergence theorem on a ball for vector fields of the form `h(z) z`, namely
`∫_B (n h + ⟪z, ∇h⟫) = R ∫_{∂B} h dσ` for `C¹` functions `h`.
-/

noncomputable section

open MeasureTheory Metric Set Filter

open scoped InnerProductSpace

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- **Divergence theorem on the ball for vector fields of the form `h(z) z`:**
`∫_B (n h + ⟪z, ∇h⟫) = R ∫_{∂B} h dσ` for `C¹` `h`. -/
theorem integral_ball_div_radial (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) (h : E → ℝ)
    (hh : ContDiff ℝ 1 h) :
    ∫ x in ball (0 : E) R, ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ)
      = R * ThinDomain.sphereIntegral n R h := by
  -- Apply the boundary form identity with constant function 1
  have h_bd := bdR_ofC1 hn hR h (fun _ => 1) hh contDiff_const
  -- Unfold bdR_apply on the left side
  rw [bdR_apply] at h_bd
  -- Simplify using ofC1_toFun and ofC1_grad
  simp only [ofC1_toFun, ofC1_grad] at h_bd
  -- The gradient of the constant 1 is 0
  have h_grad_const : classicalGrad (fun _ : E => (1 : ℝ)) = fun _ => (0 : E) := by
    funext x
    apply PiLp.ext
    intro i
    simp [classicalGrad_apply, fderiv_fun_const]
  rw [h_grad_const] at h_bd
  -- Simplify the integrand
  have h_integrand : ∀ x : E, (n : ℝ) * (h x * 1) + h x * ⟪x, (0 : E)⟫_ℝ + 1 * ⟪x, classicalGrad h x⟫_ℝ
      = (n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ := by
    intro x
    simp [inner_zero_right, mul_one, one_mul, mul_zero, add_zero]
  -- Rewrite the integral with the simplified integrand
  have h_integral : ∫ x in ball (0 : E) R,
      ((n : ℝ) * (h x * 1) + h x * ⟪x, (0 : E)⟫_ℝ + 1 * ⟪x, classicalGrad h x⟫_ℝ)
      = ∫ x in ball (0 : E) R, ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ) := by
    congr 1
    funext x
    exact h_integrand x
  rw [h_integral] at h_bd
  -- Simplify the right side: sphereIntegral n R (fun z => h z * 1) = sphereIntegral n R h
  have h_sphere : ThinDomain.sphereIntegral n R (fun z => h z * 1) = ThinDomain.sphereIntegral n R h := by
    simp only [mul_one]
  rw [h_sphere] at h_bd
  -- From R⁻¹ * I = S, we get I = R * S
  have : ∫ x in ball (0 : E) R, ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ)
      = R * ThinDomain.sphereIntegral n R h := by
    have h_eq : R⁻¹ * ∫ x in ball (0 : E) R, ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ)
        = ThinDomain.sphereIntegral n R h := h_bd
    have : ∫ x in ball (0 : E) R, ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ)
        = R * (R⁻¹ * ∫ x in ball (0 : E) R, ((n : ℝ) * h x + ⟪x, classicalGrad h x⟫_ℝ)) := by
      field_simp [hR.ne']
    rw [this, h_eq]
  exact this

end RobinCaps.Compact
