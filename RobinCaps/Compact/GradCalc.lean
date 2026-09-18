import RobinCaps.Sobolev.Weak
import RobinCaps.Compact.WeakGradMollify

/-!
# Calculus rules for the classical gradient

This file develops calculus rules for the classical gradient `classicalGrad` defined in
`RobinCaps.Sobolev.Weak`. The classical gradient of `u : E → ℝ` at `x : E` is the vector
with components `∂ᵢu(x)` represented via `fderiv`. This module provides differentiation rules
for addition, scalar multiplication, products, quotients, and composition, all proved
componentwise using the corresponding rules for `fderiv`.

Key lemmas include:
- `fderiv_apply_eq_inner_classicalGrad`: The Fréchet derivative equals the inner product
  with the classical gradient.
- `classicalGrad_add`, `classicalGrad_sub`, `classicalGrad_const_mul`: Linear combinations.
- `classicalGrad_mul`, `classicalGrad_div`: Product and quotient rules.
- `classicalGrad_comp_of_hasDerivAt`: Chain rule for scalar functions.
- `classicalGrad_norm_sq`: The gradient of the squared norm.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory InnerProductSpace
open scoped Convolution ContDiff ENNReal Topology InnerProductSpace

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The Fréchet derivative equals the inner product with the classical gradient. -/
theorem fderiv_apply_eq_inner_classicalGrad (u : E → ℝ) (x v : E) :
    fderiv ℝ u x v = ⟪classicalGrad u x, v⟫_ℝ :=
  apply_eq_inner (fderiv ℝ u x) v

/-- The gradient of a constant function is zero. -/
theorem classicalGrad_const (c : ℝ) (x : E) : classicalGrad (fun _ => c) x = 0 := by
  ext i
  simp only [classicalGrad_apply, PiLp.zero_apply, fderiv_const_apply]
  simp

/-- The gradient of a sum is the sum of the gradients. -/
theorem classicalGrad_add {u v : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    classicalGrad (fun y => u y + v y) x = classicalGrad u x + classicalGrad v x := by
  ext i
  simp only [classicalGrad_apply, PiLp.add_apply]
  have h : fderiv ℝ (fun y => u y + v y) x = fderiv ℝ u x + fderiv ℝ v x := fderiv_add hu hv
  rw [h]
  simp [ContinuousLinearMap.add_apply]

/-- The gradient of a difference is the difference of the gradients. -/
theorem classicalGrad_sub {u v : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    classicalGrad (fun y => u y - v y) x = classicalGrad u x - classicalGrad v x := by
  ext i
  simp only [classicalGrad_apply, PiLp.sub_apply]
  have h : fderiv ℝ (fun y => u y - v y) x = fderiv ℝ u x - fderiv ℝ v x := fderiv_sub hu hv
  rw [h]
  simp [ContinuousLinearMap.sub_apply]

/-- The gradient of a scalar multiple. -/
theorem classicalGrad_const_mul (c : ℝ) {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) :
    classicalGrad (fun y => c * u y) x = c • classicalGrad u x := by
  ext i
  simp only [classicalGrad_apply, PiLp.smul_apply]
  have h : fderiv ℝ (fun y => c * u y) x = c • fderiv ℝ u x := fderiv_const_mul hu c
  rw [h]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The gradient of a product (Leibniz rule). -/
theorem classicalGrad_mul {u v : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    classicalGrad (fun y => u y * v y) x = u x • classicalGrad v x + v x • classicalGrad u x := by
  ext i
  simp only [classicalGrad_apply, PiLp.add_apply, PiLp.smul_apply]
  have h : fderiv ℝ (fun y => u y * v y) x = u x • fderiv ℝ v x + v x • fderiv ℝ u x := fderiv_mul hu hv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The chain rule for the classical gradient when composing with a scalar function. -/
theorem classicalGrad_comp_of_hasDerivAt {g : ℝ → ℝ} {u : E → ℝ} {x : E} {g' : ℝ}
    (hg : HasDerivAt g g' (u x)) (hu : DifferentiableAt ℝ u x) :
    classicalGrad (fun y => g (u y)) x = g' • classicalGrad u x := by
  ext i
  simp only [classicalGrad_apply, PiLp.smul_apply]
  have h_comp := HasDerivAt.comp_hasFDerivAt x hg hu.hasFDerivAt
  have h_fd : fderiv ℝ (fun y => g (u y)) x = g' • fderiv ℝ u x := h_comp.fderiv
  rw [h_fd]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The gradient of a quotient. -/
theorem classicalGrad_div {u v : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (hvx : v x ≠ 0) :
    classicalGrad (fun y => u y / v y) x =
      (1 / v x) • classicalGrad u x - (u x / v x ^ 2) • classicalGrad v x := by
  have heq : (fun y => u y / v y) = fun y => u y * (fun t : ℝ => t⁻¹) (v y) := by
    funext y; simp [div_eq_mul_inv]
  rw [heq]
  have hvinv : DifferentiableAt ℝ (fun y => (fun t : ℝ => t⁻¹) (v y)) x :=
    DifferentiableAt.inv hv hvx
  rw [classicalGrad_mul hu hvinv,
    classicalGrad_comp_of_hasDerivAt (hasDerivAt_inv hvx) hv]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The gradient of a square. -/
theorem classicalGrad_sq {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) :
    classicalGrad (fun y => u y ^ 2) x = (2 * u x) • classicalGrad u x := by
  ext i
  simp only [classicalGrad_apply, PiLp.smul_apply]
  have eq_form : (fun y => u y ^ 2) = (fun y => u y * u y) := by ext y; ring_nf
  rw [eq_form]
  have h : fderiv ℝ (fun y => u y * u y) x = u x • fderiv ℝ u x + u x • fderiv ℝ u x := fderiv_mul hu hu
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The gradient of `v²/ψ` at a point where `ψ ≠ 0`. -/
theorem classicalGrad_sq_div {v ψ : E → ℝ} {x : E}
    (hv : DifferentiableAt ℝ v x) (hψ : DifferentiableAt ℝ ψ x) (hψx : ψ x ≠ 0) :
    classicalGrad (fun y => v y ^ 2 / ψ y) x =
      (2 * v x / ψ x) • classicalGrad v x - (v x ^ 2 / ψ x ^ 2) • classicalGrad ψ x := by
  have hvsq : DifferentiableAt ℝ (fun y => v y ^ 2) x := hv.pow 2
  have h := classicalGrad_div hvsq hψ hψx
  rw [classicalGrad_sq hv] at h
  rw [h]
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp

/-- The squared norm is differentiable everywhere. -/
theorem differentiableAt_norm_sq (x : E) : DifferentiableAt ℝ (fun y : E => ‖y‖ ^ 2) x :=
  (hasStrictFDerivAt_norm_sq x).differentiableAt

/-- The gradient of the squared norm is twice the input vector. -/
theorem classicalGrad_norm_sq (x : E) : classicalGrad (fun y : E => ‖y‖ ^ 2) x = (2 : ℝ) • x := by
  ext i
  simp only [classicalGrad_apply, PiLp.smul_apply]
  have h_fderiv := fderiv_norm_sq_apply x
  rw [h_fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply]
  rw [EuclideanSpace.inner_single_right]
  simp

end RobinCaps.Compact

end
