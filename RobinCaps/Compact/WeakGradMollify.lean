import RobinCaps.Compact.Basic

/-!
# (WG): mollification commutes with the weak gradient in the interior

This file proves the single identity through which every *weak* fact about an element
`u ∈ H¹(B_R)` enters the compactness argument of `RobinCaps/Compact/` (see `PLAN.md`):

`∂ᵢ (ρ ⋆ ext u) (x) = (ρ ⋆ extGrad u i) (x)`  whenever  `‖x‖ + δ < R`,

for a mollifier `ρ` at scale `δ` (`IsMollifier δ ρ`), where `ext u` is the zero-extension of `u`
and `extGrad u i` the zero-extension of the `i`-th component of its weak gradient
(both from `RobinCaps/Compact/Basic.lean`).  Convolutions are scalar convolutions with respect
to Lebesgue measure, `ρ ⋆ g = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g`.

## Contents

* `sum_smul_single`, `apply_eq_inner`, `norm_fderiv_eq_norm_classicalGrad`: the elementary Riesz
  representation of a continuous linear functional on `EuclideanSpace ℝ (Fin n)` by the vector of
  its values on the standard basis; in particular `‖fderiv ℝ f x‖ = ‖classicalGrad f x‖`.
* `fderiv_conv_ext`: the identity (WG) above.
* `classicalGrad_conv_ext`: its vector form.
* `norm_fderiv_conv_ext_eq`, `norm_fderiv_conv_ext_sq_le`: the resulting (in fact exact)
  bound `‖fderiv ℝ (ρ ⋆ ext u) x‖ ^ 2 ≤ ∑ i, ((ρ ⋆ extGrad u i) x) ^ 2`.

The proof of (WG) is the standard one: differentiating under the integral sign
(`HasCompactSupport.hasFDerivAt_convolution_left`) puts the derivative on `ρ`, the substitution
`y = x - t` turns the convolution into the pairing of `u` with the test function
`φ y = ρ (x - y)`, whose support `closedBall x δ` is contained in `B_R` precisely because
`‖x‖ + δ < R`, and the defining property of the weak gradient moves the derivative onto `u`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Riesz representation of a linear functional on `E` -/

/-- Every vector of `E` is the sum of its coordinates times the standard basis vectors. -/
theorem sum_smul_single (h : EuclideanSpace ℝ (Fin n)) :
    ∑ i, h i • EuclideanSpace.single i (1 : ℝ) = h := by
  classical
  simpa using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h

/-- **Riesz representation.**  A continuous linear functional on `E` is the inner product with
the vector of its values on the standard basis. -/
theorem apply_eq_inner (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (h : EuclideanSpace ℝ (Fin n)) :
    L h = inner ℝ (WithLp.toLp 2 fun i => L (EuclideanSpace.single i 1) : E) h := by
  conv_lhs => rw [← sum_smul_single h]
  rw [map_sum]
  simp [PiLp.inner_apply]

/-- The Fréchet derivative of a real-valued function on `E` has the same norm as the vector
of its partial derivatives. -/
theorem norm_fderiv_eq_norm_classicalGrad (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖classicalGrad f x‖ := by
  have hL : fderiv ℝ f x = innerSL ℝ (classicalGrad f x) := by
    ext h
    exact apply_eq_inner (fderiv ℝ f x) h
  rw [hL, innerSL_apply_norm]

/-! ## (WG): the derivative of the mollification -/

variable {δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **(WG).**  For `x` well inside the ball (`‖x‖ + δ < R`), the `i`-th partial derivative of the
mollification of the zero-extension of `u ∈ H¹(B_R)` is the mollification of the zero-extension
of the `i`-th component of the weak gradient of `u`. -/
theorem fderiv_conv_ext (hρ : IsMollifier δ ρ) {R : ℝ} (u : H1 (ball (0 : E) R)) {x : E}
    (hx : ‖x‖ + δ < R) (i : Fin n) :
    fderiv ℝ (ρ ⋆ ext u) x (EuclideanSpace.single i 1) = (ρ ⋆ extGrad u i) x := by
  classical
  have hcont : ContDiff ℝ 1 ρ := hρ.contDiff.of_le (by simp)
  -- Step 1: differentiate under the integral sign.
  have hfd : HasFDerivAt (ρ ⋆ ext u)
      ((fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL E, volume] ext u) x) x :=
    hρ.hasCompactSupport.hasFDerivAt_convolution_left _ hcont (locallyIntegrable_ext u) x
  have hint : Integrable (fun t => ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E)
      (fderiv ℝ ρ t) (ext u (x - t))) volume := by
    have h := (hρ.hasCompactSupport.fderiv ℝ).convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E)
      (hρ.contDiff.continuous_fderiv (by simp)) (locallyIntegrable_ext u) x
    simpa [ConvolutionExistsAt] using h
  have h2 : (fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL E, volume] ext u) x
        (EuclideanSpace.single i 1)
      = ∫ t, fderiv ℝ ρ t (EuclideanSpace.single i 1) * ext u (x - t) := by
    rw [convolution_def, ContinuousLinearMap.integral_apply hint]
    simp
  -- Step 2: substitute `y = x - t`.
  have h3 : (∫ t, fderiv ℝ ρ t (EuclideanSpace.single i 1) * ext u (x - t))
      = ∫ y, fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * ext u y := by
    have h := integral_sub_left_eq_self
      (fun y => fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * ext u y) volume x
    simpa only [sub_sub_self] using h
  -- Step 3: restrict to the ball.
  have h4 : (∫ y, fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * ext u y)
      = ∫ y in ball (0 : E) R,
          u.toFun y * fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := ball (0 : E) R)
      (f := fun y => fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) * ext u y)
      (fun y hy => by simp [ext_apply_of_not_mem u hy])]
    refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
    rw [ext_apply_of_mem u hy]
    ring
  -- Step 4: the test function `φ y = ρ (x - y)`.
  have hsupp : ∀ y : E, ρ (x - y) ≠ 0 → y ∈ closedBall x δ := by
    intro y hy
    by_contra hmem
    refine hy (hρ.eq_zero_of_lt_norm ?_)
    have : δ < dist y x := by simpa [mem_closedBall] using hmem
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at this
  have htsupp : tsupport (fun y : E => ρ (x - y)) ⊆ closedBall x δ :=
    closure_minimal (fun y hy => hsupp y hy) isClosed_closedBall
  have hball : closedBall x δ ⊆ ball (0 : E) R := by
    intro y hy
    have hyx : ‖y - x‖ ≤ δ := by rw [← dist_eq_norm]; exact hy
    have h1 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by simpa using norm_add_le x (y - x)
    simp only [mem_ball, dist_zero_right]
    linarith
  have hφsmooth : ContDiff ℝ ∞ (fun y : E => ρ (x - y)) :=
    hρ.contDiff.comp (contDiff_const.sub contDiff_id)
  have hφcompact : HasCompactSupport (fun y : E => ρ (x - y)) :=
    HasCompactSupport.intro (isCompact_closedBall x δ) fun y hy => by
      by_contra h
      exact hy (hsupp y h)
  have hφderiv : ∀ y : E, fderiv ℝ (fun z : E => ρ (x - z)) y (EuclideanSpace.single i 1)
      = -fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1) := by
    intro y
    have h1 : HasFDerivAt (fun z : E => x - z) (-ContinuousLinearMap.id ℝ E) y := by
      simpa using (hasFDerivAt_id y).const_sub x
    have h2' : HasFDerivAt ρ (fderiv ℝ ρ (x - y)) (x - y) :=
      (hρ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h3' : HasFDerivAt (fun z : E => ρ (x - z))
        ((fderiv ℝ ρ (x - y)).comp (-ContinuousLinearMap.id ℝ E)) y :=
      HasFDerivAt.comp y h2' h1
    rw [h3'.fderiv]
    simp
  -- Step 5: the weak-gradient identity for this test function.
  have hkey : (∫ y in ball (0 : E) R,
        u.toFun y * fderiv ℝ ρ (x - y) (EuclideanSpace.single i 1))
      = ∫ y in ball (0 : E) R, u.grad y i * ρ (x - y) := by
    have hw := u.hasWeakGrad (fun y : E => ρ (x - y)) hφsmooth hφcompact
      (htsupp.trans hball) i
    simp only [hφderiv, mul_neg, integral_neg, neg_inj] at hw
    exact hw
  -- Step 6: recognise the right-hand side as a convolution.
  have h5 : (∫ y in ball (0 : E) R, u.grad y i * ρ (x - y)) = (ρ ⋆ extGrad u i) x := by
    have h5a : (∫ y in ball (0 : E) R, u.grad y i * ρ (x - y))
        = ∫ y, extGrad u i y * ρ (x - y) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := ball (0 : E) R) (f := fun y => extGrad u i y * ρ (x - y))
        (fun y hy => by simp [extGrad_apply_of_not_mem u i hy])]
      refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
      rw [extGrad_apply_of_mem u i hy]
    have h5b := integral_sub_left_eq_self
      (fun y => extGrad u i y * ρ (x - y)) volume x
    simp only [sub_sub_self] at h5b
    rw [h5a, IsMollifier.conv_apply, ← h5b]
    exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
  rw [hfd.fderiv, h2, h3, h4, hkey, h5]

/-- The vector form of (WG): the classical gradient of the mollification is the vector of the
mollifications of the components of the weak gradient. -/
theorem classicalGrad_conv_ext (hρ : IsMollifier δ ρ) {R : ℝ} (u : H1 (ball (0 : E) R)) {x : E}
    (hx : ‖x‖ + δ < R) :
    classicalGrad (ρ ⋆ ext u) x = WithLp.toLp 2 (fun i => (ρ ⋆ extGrad u i) x) := by
  unfold classicalGrad
  congr 1
  funext i
  exact fderiv_conv_ext hρ u hx i

/-- The squared norm of the derivative of the mollification, in terms of the mollified
components of the weak gradient. -/
theorem norm_fderiv_conv_ext_eq (hρ : IsMollifier δ ρ) {R : ℝ} (u : H1 (ball (0 : E) R)) {x : E}
    (hx : ‖x‖ + δ < R) :
    ‖fderiv ℝ (ρ ⋆ ext u) x‖ ^ 2 = ∑ i, ((ρ ⋆ extGrad u i) x) ^ 2 := by
  rw [norm_fderiv_eq_norm_classicalGrad, norm_sq_eq_sum, classicalGrad_conv_ext hρ u hx]

/-- **The pointwise gradient bound.**  A restatement of `norm_fderiv_conv_ext_eq` as the
inequality used in the compactness argument. -/
theorem norm_fderiv_conv_ext_sq_le (hρ : IsMollifier δ ρ) {R : ℝ} (u : H1 (ball (0 : E) R))
    {x : E} (hx : ‖x‖ + δ < R) :
    ‖fderiv ℝ (ρ ⋆ ext u) x‖ ^ 2 ≤ ∑ i, ((ρ ⋆ extGrad u i) x) ^ 2 :=
  le_of_eq (norm_fderiv_conv_ext_eq hρ u hx)

end RobinCaps.Compact

end
