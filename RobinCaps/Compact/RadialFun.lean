import RobinCaps.Sobolev.Weak
import RobinCaps.Compact.WeakGradMollify

/-!
# Radial functions and their classical gradients

This file defines radial functions `radialFun g z := g (‖z‖²)` built from a profile function `g : ℝ → ℝ`,
and proves essential properties about their continuity, differentiability, and classical gradients.

For a `C¹` profile `g`, the classical gradient of `radialFun g` at `z` is `∇ψ = 2 g'(‖z‖²) z`.

The key result for the Robin caps construction is `div_grad_radialFun`, which computes the
divergence-form Laplacian of a radial function: if `h z := 2 * deriv g (‖z‖²)`, then
`n h + ⟪z, ∇h⟫ = 4 ‖z‖² g''(‖z‖²) + 2 n g'(‖z‖²)`.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

noncomputable section

open scoped InnerProductSpace ContDiff

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Definition and basic properties -/

/-- A radial function built from a profile in the variable `s = ‖z‖²`. -/
def radialFun (g : ℝ → ℝ) : E → ℝ := fun z => g (‖z‖ ^ 2)

@[simp]
theorem radialFun_apply (g : ℝ → ℝ) (z : E) : radialFun g z = g (‖z‖ ^ 2) := rfl

/-! ## Continuity and differentiability -/

/-- The square of the norm is smooth. -/
theorem contDiff_norm_sq' : ContDiff ℝ ∞ (fun z : E => ‖z‖ ^ 2) :=
  contDiff_norm_sq ℝ

/-- A radial function is `Cᵏ` if its profile is `Cᵏ`. -/
theorem contDiff_radialFun {k : ℕ∞} {g : ℝ → ℝ} (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (radialFun (n := n) g) :=
  hg.comp (contDiff_norm_sq ℝ)

/-- A radial function is continuous if its profile is continuous. -/
theorem continuous_radialFun {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (radialFun (n := n) g) :=
  hg.comp (continuous_norm.pow 2)

/-! ## Fréchet derivative of the norm squared -/

/-- The Fréchet derivative of `‖·‖²` at `z` is `2 • (innerSL ℝ z)`. -/
theorem hasFDerivAt_norm_sq (z : E) :
    HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ z) z :=
  (hasStrictFDerivAt_norm_sq z).hasFDerivAt

/-! ## Fréchet derivative of radial functions -/

/-- The directional derivative of `radialFun g` at `z` in direction `v` is `2 g'(‖z‖²) ⟪z, v⟫`. -/
theorem fderiv_radialFun {g : ℝ → ℝ} {z : E} {g' : ℝ} (hg : HasDerivAt g g' (‖z‖ ^ 2)) (v : E) :
    fderiv ℝ (radialFun g) z v = 2 * g' * ⟪z, v⟫_ℝ := by
  -- norm_sq has Fréchet derivative 2 • innerSL ℝ z at z
  have hns : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ z) z :=
    hasFDerivAt_norm_sq z
  -- By the chain rule for composing a scalar function with a vector function
  have hcomp : HasFDerivAt (radialFun g) (g' • (2 • innerSL ℝ z)) z :=
    hg.comp_hasFDerivAt z hns
  -- Extract the fderiv and apply to v
  -- The Fréchet derivative is (g' • (2 • innerSL ℝ z))
  -- When applied to v, this gives: (g' * 2) * ((innerSL ℝ z) v) = (g' * 2) * ⟪z, v⟫
  rw [hcomp.fderiv]
  show (g' • (2 • innerSL ℝ z)) v = 2 * g' * ⟪z, v⟫_ℝ
  dsimp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply (𝕜 := ℝ)]
  norm_num [mul_comm, mul_assoc]

/-! ## Classical gradient of radial functions -/

/-- The classical gradient of `radialFun g` at `z` is `2 g'(‖z‖²) z`. -/
theorem classicalGrad_radialFun {g : ℝ → ℝ} {z : E} {g' : ℝ} (hg : HasDerivAt g g' (‖z‖ ^ 2)) :
    classicalGrad (radialFun g) z = (2 * g') • z := by
  ext i
  simp only [classicalGrad_apply, PiLp.smul_apply]
  have hfd := fderiv_radialFun hg (EuclideanSpace.single i 1)
  rw [hfd]
  -- ⟪z, EuclideanSpace.single i 1⟫ = z i (after simplifying the inner product)
  simp only [EuclideanSpace.inner_single_right]
  -- Now simplify the mul, conj (which is identity on ℝ), and compare
  norm_num

/-- The classical gradient of a smooth radial function. -/
theorem classicalGrad_radialFun' {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (z : E) :
    classicalGrad (radialFun g) z = (2 * deriv g (‖z‖ ^ 2)) • z :=
  classicalGrad_radialFun (hg.differentiable le_rfl _ |>.hasDerivAt)

/-- The inner product of `z` with its classical gradient. -/
theorem inner_classicalGrad_radialFun {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (z : E) :
    ⟪z, classicalGrad (radialFun g) z⟫_ℝ = 2 * deriv g (‖z‖ ^ 2) * ‖z‖ ^ 2 := by
  rw [classicalGrad_radialFun' hg]
  simp only [inner_smul_right]
  rw [real_inner_self_eq_norm_sq]

/-! ## Divergence-form Laplacian of radial functions -/

/-- The Laplacian of a radial function in divergence form.

For `h z := 2 * deriv g (‖z‖²)` (so that `∇(radialFun g) = h z`), we have
`n h + ⟪z, ∇h⟫ = 4 ‖z‖² g''(‖z‖²) + 2 n g'(‖z‖²)`.
-/
theorem div_grad_radialFun {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (z : E) :
    (n : ℝ) * (2 * deriv g (‖z‖ ^ 2)) + ⟪z, classicalGrad (fun y : E => 2 * deriv g (‖y‖ ^ 2)) z⟫_ℝ
      = 4 * ‖z‖ ^ 2 * deriv (deriv g) (‖z‖ ^ 2) + 2 * (n : ℝ) * deriv g (‖z‖ ^ 2) := by
  -- The profile function s ↦ 2 * deriv g s is C¹ because g is C²
  have hderiv : ContDiff ℝ 1 (fun s => 2 * deriv g s) := by
    -- If g is C², then deriv g is C¹
    have h_deriv_g : ContDiff ℝ 1 (deriv g) := hg.deriv'
    -- Multiply by 2: multiply by a constant preserves smoothness
    have : (fun s => 2 * deriv g s) = (fun s => (2 : ℝ) • (deriv g s)) := rfl
    rw [this]
    exact h_deriv_g.const_smul (2 : ℝ)
  -- Apply classicalGrad_radialFun' to the radial function
  have h_grad_form : classicalGrad (fun y : E => 2 * deriv g (‖y‖ ^ 2)) z =
      (2 * deriv (fun s => 2 * deriv g s) (‖z‖ ^ 2)) • z := by
    -- The function y ↦ 2 * deriv g (‖y‖²) is radialFun (fun s => 2 * deriv g s)
    have : (fun y : E => 2 * deriv g (‖y‖ ^ 2)) = radialFun (fun s => 2 * deriv g s) := rfl
    rw [this]
    exact classicalGrad_radialFun' hderiv z
  rw [h_grad_form]
  -- Compute deriv (fun s => 2 * deriv g s) s = 2 * deriv (deriv g) s
  have h_deriv_deriv : deriv (fun s => 2 * deriv g s) (‖z‖ ^ 2) = 2 * deriv (deriv g) (‖z‖ ^ 2) := by
    have h_derivg : ContDiff ℝ 1 (deriv g) := hg.deriv'
    rw [deriv_const_mul (c := (2 : ℝ))]
    -- deriv g is C¹, hence differentiable everywhere, in particular at ‖z‖²
    exact (h_derivg.differentiable (by norm_num : (1 : WithTop ℕ∞) ≤ 1)) _
  rw [h_deriv_deriv]
  -- Now compute the inner product
  rw [inner_smul_right, real_inner_self_eq_norm_sq]
  ring

end RobinCaps.Compact
