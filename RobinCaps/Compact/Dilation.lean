import Mathlib
import RobinCaps.Compact.Basic

/-!
# Dilations of the weak Sobolev space on a ball

This file implements the **dilation** step of the compactness sub-project (see
`RobinCaps/Compact/PLAN.md`, step 1 of the mathematical route): for `lam > 0` the map

`D_lam u (x) = u (lam • x)`

carries `H¹(ball 0 R)` to `H¹(ball 0 (R / lam))`, a *strictly larger* ball when `lam < 1`.
This is the substitute, available because the ball is star-shaped, for the extension operator
`H¹(B) → H¹(ℝⁿ)` which mathlib does not have.

## Main results

* `preimage_smul_ball`: `(lam • ·) ⁻¹' ball 0 r = ball 0 (r / lam)` for `lam > 0`.
* `map_volume_smul`: `(lam • ·)_* volume = (lam ^ n)⁻¹ • volume`.
* `setIntegral_comp_smul`, `setIntegral_ball_comp_smul`: the change-of-variables formulas
  `∫_{(lam•·)⁻¹ Ω} F (lam • x) dx = (lam ^ n)⁻¹ ∫_Ω F` and
  `∫_{ball 0 r} f (lam • x) dx = lam⁻¹ ^ n ∫_{ball 0 (lam r)} f`.
* `integral_ball_comp_smul_sq`, `integral_comp_smul_sq`, `memLp_comp_smul`: the `L²` scaling.
* `hasWeakGrad_comp_smul`: weak gradients transform by `(u, g) ↦ (u ∘ (lam • ·), lam • g ∘ (lam • ·))`.
* `dilate` together with `mass_dilate`, `dirichlet_dilate`, `ext_dilate`, `extGrad_dilate`.
* `castRadius`: transport of `H1 (ball 0 R)` along an equality of radii.

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

/-! ## The dilation map -/

/-- The dilation `x ↦ c • x` (`c ≠ 0`) as a homeomorphism of `ℝⁿ`. -/
def smulHomeo (c : ℝ) (hc : c ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  Homeomorph.smulOfNeZero c hc

@[simp] theorem coe_smulHomeo (c : ℝ) (hc : c ≠ 0) :
    ⇑(smulHomeo (n := n) c hc) = fun x : E => c • x := rfl

/-- The dilation `x ↦ c • x` (`c ≠ 0`) as a measurable equivalence of `ℝⁿ`. -/
def smulMeasEquiv (c : ℝ) (hc : c ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
  (smulHomeo (n := n) c hc).toMeasurableEquiv

@[simp] theorem coe_smulMeasEquiv (c : ℝ) (hc : c ≠ 0) :
    ⇑(smulMeasEquiv (n := n) c hc) = fun x : E => c • x := rfl

section Smul

variable {lam : ℝ}

/-- The preimage of a ball centred at the origin under a positive dilation. -/
theorem preimage_smul_ball (hlam : 0 < lam) (r : ℝ) :
    (fun x : E => lam • x) ⁻¹' ball (0 : E) r = ball (0 : E) (r / lam) := by
  ext x
  simp only [mem_preimage, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hlam]
  rw [lt_div_iff₀ hlam, mul_comm ‖x‖ lam]

/-! ### The measure identity -/

/-- **Pushforward of the Lebesgue measure under a dilation**: `(lam • ·)_* volume
= (lam ^ n)⁻¹ • volume`. -/
theorem map_volume_smul (hlam : 0 < lam) :
    Measure.map (fun x : E => lam • x) volume
      = ENNReal.ofReal ((lam ^ n)⁻¹) • (volume : Measure E) := by
  have h := Measure.map_addHaar_smul (volume : Measure E) hlam.ne'
  rw [finrank_euclideanSpace_fin] at h
  rw [h, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hlam.le n))]

/-- The pushforward of the restricted measure. -/
theorem map_restrict_smul (hlam : 0 < lam) {Ω : Set E} (hΩ : MeasurableSet Ω) :
    Measure.map (fun x : E => lam • x) (volume.restrict ((fun x : E => lam • x) ⁻¹' Ω))
      = ENNReal.ofReal ((lam ^ n)⁻¹) • volume.restrict Ω := by
  rw [← Measure.restrict_map (measurable_const_smul lam) hΩ, map_volume_smul hlam,
    Measure.restrict_smul]

/-- **Change of variables, preimage form.**  No integrability or measurability is needed, since
`x ↦ lam • x` is a measurable embedding. -/
theorem setIntegral_comp_smul (hlam : 0 < lam) {Ω : Set E} (hΩ : MeasurableSet Ω) (F : E → ℝ) :
    (∫ x in (fun x : E => lam • x) ⁻¹' Ω, F (lam • x)) = (lam ^ n)⁻¹ * ∫ y in Ω, F y := by
  have hemb : MeasurableEmbedding (fun x : E => lam • x) :=
    (smulMeasEquiv (n := n) lam hlam.ne').measurableEmbedding
  have htoReal : (ENNReal.ofReal ((lam ^ n)⁻¹)).toReal = (lam ^ n)⁻¹ :=
    ENNReal.toReal_ofReal (inv_nonneg.2 (pow_nonneg hlam.le n))
  calc (∫ x in (fun x : E => lam • x) ⁻¹' Ω, F (lam • x))
      = ∫ y, F y ∂(Measure.map (fun x : E => lam • x)
          (volume.restrict ((fun x : E => lam • x) ⁻¹' Ω))) := (hemb.integral_map F).symm
    _ = ∫ y, F y ∂(ENNReal.ofReal ((lam ^ n)⁻¹) • volume.restrict Ω) := by
        rw [map_restrict_smul hlam hΩ]
    _ = (lam ^ n)⁻¹ * ∫ y in Ω, F y := by
        rw [integral_smul_measure, htoReal, smul_eq_mul]

/-- **Change of variables on balls.**  `∫_{ball 0 r} f (lam • x) dx
= lam⁻¹ ^ n ∫_{ball 0 (lam r)} f`. -/
theorem setIntegral_ball_comp_smul (f : E → ℝ) (hlam : 0 < lam) (r : ℝ) :
    (∫ x in ball (0 : E) r, f (lam • x))
      = lam⁻¹ ^ n * ∫ y in ball (0 : E) (lam * r), f y := by
  have hdiv : lam * r / lam = r := by field_simp
  have hpre : (fun x : E => lam • x) ⁻¹' ball (0 : E) (lam * r) = ball (0 : E) r := by
    rw [preimage_smul_ball hlam, hdiv]
  have h := setIntegral_comp_smul hlam (measurableSet_ball (x := (0 : E)) (ε := lam * r)) f
  rw [hpre] at h
  rw [h, inv_pow]

/-- **`L²` scaling on balls.** -/
theorem integral_ball_comp_smul_sq (g : E → ℝ) {lam : ℝ} (hlam : 0 < lam) (r : ℝ) :
    (∫ x in ball (0 : E) r, g (lam • x) ^ 2)
      = lam⁻¹ ^ n * ∫ x in ball (0 : E) (lam * r), g x ^ 2 :=
  setIntegral_ball_comp_smul (fun y => g y ^ 2) hlam r

/-- **`L²` scaling on all of `ℝⁿ`.** -/
theorem integral_comp_smul_sq (g : E → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (∫ x, g (lam • x) ^ 2) = lam⁻¹ ^ n * ∫ x, g x ^ 2 := by
  have h := Measure.integral_comp_smul (volume : Measure E) (fun y => g y ^ 2) lam
  rw [finrank_euclideanSpace_fin] at h
  rw [h, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hlam.le n)), smul_eq_mul, inv_pow]

/-! ### `L²`-membership under dilation -/

/-- `Lᵠ`-membership transports along a dilation (restricted measures). -/
theorem memLp_comp_smul_restrict {F : Type*} [NormedAddCommGroup F] {q : ℝ≥0∞} (hlam : 0 < lam)
    {Ω : Set E} (hΩ : MeasurableSet Ω) {f : E → F} (hf : MemLp f q (volume.restrict Ω)) :
    MemLp (fun x => f (lam • x)) q
      (volume.restrict ((fun x : E => lam • x) ⁻¹' Ω)) := by
  have h1 : MemLp f q (ENNReal.ofReal ((lam ^ n)⁻¹) • volume.restrict Ω) :=
    hf.smul_measure ENNReal.ofReal_ne_top
  rw [← map_restrict_smul hlam hΩ] at h1
  exact (MeasurableEquiv.memLp_map_measure_iff (smulMeasEquiv (n := n) lam hlam.ne')).1 h1

/-- `L²`-membership transports along a dilation. -/
theorem memLp_comp_smul {g : E → ℝ} (hg : MemLp g 2 volume) {lam : ℝ} (hlam : 0 < lam) :
    MemLp (fun x => g (lam • x)) 2 volume := by
  have hg' : MemLp g 2 (volume.restrict (univ : Set E)) := by rwa [Measure.restrict_univ]
  have h := memLp_comp_smul_restrict hlam MeasurableSet.univ hg'
  rwa [preimage_univ, Measure.restrict_univ] at h

/-! ### Weak gradients under dilation -/

/-- **Weak gradients transform under a dilation.**  If `g` is a weak gradient of `u` on `Ω`, then
`lam • (g ∘ (lam • ·))` is a weak gradient of `u ∘ (lam • ·)` on `(lam • ·) ⁻¹' Ω`. -/
theorem hasWeakGrad_comp_smul (hlam : 0 < lam) {Ω : Set E} (hΩ : MeasurableSet Ω)
    {u : E → ℝ} {g : E → E} (h : HasWeakGrad Ω u g) :
    HasWeakGrad ((fun x : E => lam • x) ⁻¹' Ω) (fun x => u (lam • x))
      (fun x => lam • g (lam • x)) := by
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hlaminv0 : lam⁻¹ ≠ 0 := inv_ne_zero hlam0
  intro φ hφ hφc hφs i
  set ψ : E → ℝ := fun y => φ (lam⁻¹ • y) with hψdef
  have hψA : ∀ x : E, ψ (lam • x) = φ x := by
    intro x
    simp only [hψdef, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  -- `ψ` is a legitimate test function on `Ω`
  have hcd : ContDiff ℝ ∞ (fun y : E => lam⁻¹ • y) := contDiff_id.const_smul lam⁻¹
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp hcd
  have hψc : HasCompactSupport ψ :=
    hφc.comp_homeomorph (smulHomeo (n := n) lam⁻¹ hlaminv0)
  have hψs : tsupport ψ ⊆ Ω := by
    have h1 : tsupport ψ = (fun y : E => lam⁻¹ • y) ⁻¹' tsupport φ := by
      show closure (Function.support (φ ∘ fun y : E => lam⁻¹ • y)) = _
      rw [Function.support_comp_eq_preimage]
      exact ((smulHomeo (n := n) lam⁻¹ hlaminv0).preimage_closure _).symm
    intro y hy
    rw [h1] at hy
    have h2 : lam • (lam⁻¹ • y) ∈ Ω := hφs hy
    rwa [smul_smul, mul_inv_cancel₀ hlam0, one_smul] at h2
  -- the chain rule
  have hdiffψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hfd : ∀ x : E, fderiv ℝ φ x
      = (fderiv ℝ ψ (lam • x)).comp
          (lam • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) := by
    intro x
    have hs : HasFDerivAt (fun y : E => lam • y)
        (lam • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x :=
      (hasFDerivAt_id x).const_smul lam
    have hc : HasFDerivAt (ψ ∘ fun y : E => lam • y)
        ((fderiv ℝ ψ (lam • x)).comp
          (lam • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) x :=
      (hdiffψ (lam • x)).hasFDerivAt.comp x hs
    have hfun : (ψ ∘ fun y : E => lam • y) = φ := funext hψA
    rw [hfun] at hc
    exact hc.fderiv
  have hderiv : ∀ x : E, fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))
      = lam * fderiv ℝ ψ (lam • x) (EuclideanSpace.single i (1 : ℝ)) := by
    intro x
    rw [hfd x]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
      map_smul, smul_eq_mul]
  -- the two changes of variables
  have c1 := setIntegral_comp_smul hlam hΩ
    (fun y => u y * fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ)))
  have c2 := setIntegral_comp_smul hlam hΩ (fun y => g y i * ψ y)
  have e1 := h ψ hψ hψc hψs i
  have l1 : (∫ x in (fun x : E => lam • x) ⁻¹' Ω,
        u (lam • x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = lam * ∫ x in (fun x : E => lam • x) ⁻¹' Ω,
          u (lam • x) * fderiv ℝ ψ (lam • x) (EuclideanSpace.single i (1 : ℝ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [hderiv x]
    ring
  have l2 : (∫ x in (fun x : E => lam • x) ⁻¹' Ω, (lam • g (lam • x)) i * φ x)
      = lam * ∫ x in (fun x : E => lam • x) ⁻¹' Ω, g (lam • x) i * ψ (lam • x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [hψA x, PiLp.smul_apply, smul_eq_mul]
    ring
  show (∫ x in (fun x : E => lam • x) ⁻¹' Ω,
      u (lam • x) * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
    = -∫ x in (fun x : E => lam • x) ⁻¹' Ω, (lam • g (lam • x)) i * φ x
  rw [l1, c1, e1, l2, c2]
  ring

end Smul

/-! ## The dilation of an `H1` element -/

section Dilate

variable {R lam : ℝ}

/-- **Dilation** `D_lam u (x) = u (lam • x)`, an element of `H1 (ball 0 (R / lam))`. -/
def dilate (lam : ℝ) (hlam : 0 < lam) (u : H1 (ball (0 : E) R)) :
    H1 (ball (0 : E) (R / lam)) where
  toFun := fun x => u.toFun (lam • x)
  grad := fun x => lam • u.grad (lam • x)
  memL2 := by
    have h := memLp_comp_smul_restrict hlam
      (measurableSet_ball (x := (0 : E)) (ε := R)) u.memL2
    rwa [preimage_smul_ball hlam] at h
  grad_memL2 := by
    have h := (memLp_comp_smul_restrict hlam
      (measurableSet_ball (x := (0 : E)) (ε := R)) u.grad_memL2).const_smul lam
    rwa [preimage_smul_ball hlam] at h
  hasWeakGrad := by
    have h := hasWeakGrad_comp_smul hlam
      (measurableSet_ball (x := (0 : E)) (ε := R)) u.hasWeakGrad
    rwa [preimage_smul_ball hlam] at h

@[simp] theorem dilate_toFun (hlam : 0 < lam) (u : H1 (ball (0 : E) R)) :
    (dilate lam hlam u).toFun = fun x => u.toFun (lam • x) := rfl

@[simp] theorem dilate_grad (hlam : 0 < lam) (u : H1 (ball (0 : E) R)) :
    (dilate lam hlam u).grad = fun x => lam • u.grad (lam • x) := rfl

/-- The mass scales by `lam⁻ⁿ`. -/
theorem mass_dilate (hlam : 0 < lam) (u : H1 (ball (0 : E) R)) :
    mass (dilate lam hlam u) = lam⁻¹ ^ n * mass u := by
  have hR : lam * (R / lam) = R := by field_simp
  have h1 : mass (dilate lam hlam u)
      = ∫ x in ball (0 : E) (R / lam), u.toFun (lam • x) ^ 2 := rfl
  rw [h1, integral_ball_comp_smul_sq u.toFun hlam (R / lam), hR]
  rfl

/-- The Dirichlet energy scales by `lam² lam⁻ⁿ`. -/
theorem dirichlet_dilate (hlam : 0 < lam) (u : H1 (ball (0 : E) R)) :
    dirichlet (dilate lam hlam u) = lam ^ 2 * lam⁻¹ ^ n * dirichlet u := by
  have hR : lam * (R / lam) = R := by field_simp
  have h1 : dirichlet (dilate lam hlam u)
      = lam ^ 2 * ∫ x in ball (0 : E) (R / lam), ‖u.grad (lam • x)‖ ^ 2 := by
    unfold dirichlet
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [dilate_grad, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h1, integral_ball_comp_smul_sq (fun y => ‖u.grad y‖) hlam (R / lam), hR]
  unfold dirichlet
  ring

/-- The zero-extension of a dilation is the dilation of the zero-extension. -/
theorem ext_dilate (hlam : 0 < lam) (u : H1 (ball (0 : E) R)) (x : E) :
    ext (dilate lam hlam u) x = ext u (lam • x) := by
  by_cases hx : x ∈ ball (0 : E) (R / lam)
  · have hx' : lam • x ∈ ball (0 : E) R := by
      have hmem : x ∈ (fun y : E => lam • y) ⁻¹' ball (0 : E) R := by
        rw [preimage_smul_ball hlam]
        exact hx
      exact hmem
    rw [ext_apply_of_mem _ hx, ext_apply_of_mem _ hx']
    rfl
  · have hx' : lam • x ∉ ball (0 : E) R := by
      intro hmem
      apply hx
      have : x ∈ (fun y : E => lam • y) ⁻¹' ball (0 : E) R := hmem
      rwa [preimage_smul_ball hlam] at this
    rw [ext_apply_of_not_mem _ hx, ext_apply_of_not_mem _ hx']

/-- The zero-extension of the weak gradient of a dilation. -/
theorem extGrad_dilate (hlam : 0 < lam) (u : H1 (ball (0 : E) R)) (i : Fin n) (x : E) :
    extGrad (dilate lam hlam u) i x = lam * extGrad u i (lam • x) := by
  by_cases hx : x ∈ ball (0 : E) (R / lam)
  · have hx' : lam • x ∈ ball (0 : E) R := by
      have hmem : x ∈ (fun y : E => lam • y) ⁻¹' ball (0 : E) R := by
        rw [preimage_smul_ball hlam]
        exact hx
      exact hmem
    rw [extGrad_apply_of_mem _ _ hx, extGrad_apply_of_mem _ _ hx', dilate_grad]
    simp only [PiLp.smul_apply, smul_eq_mul]
  · have hx' : lam • x ∉ ball (0 : E) R := by
      intro hmem
      apply hx
      have : x ∈ (fun y : E => lam • y) ⁻¹' ball (0 : E) R := hmem
      rwa [preimage_smul_ball hlam] at this
    rw [extGrad_apply_of_not_mem _ _ hx, extGrad_apply_of_not_mem _ _ hx', mul_zero]

end Dilate

/-! ## Transport along an equality of radii -/

/-- Transport of `H1` along an equality of radii (so that `H1 (ball 0 (R / R))` can be used as
`H1 (ball 0 1)`). -/
def castRadius {R R' : ℝ} (h : R = R') (u : H1 (ball (0 : E) R)) : H1 (ball (0 : E) R') where
  toFun := u.toFun
  grad := u.grad
  memL2 := by subst h; exact u.memL2
  grad_memL2 := by subst h; exact u.grad_memL2
  hasWeakGrad := by subst h; exact u.hasWeakGrad

@[simp] theorem castRadius_toFun {R R' : ℝ} (h : R = R') (u : H1 (ball (0 : E) R)) :
    (castRadius h u).toFun = u.toFun := rfl

@[simp] theorem castRadius_grad {R R' : ℝ} (h : R = R') (u : H1 (ball (0 : E) R)) :
    (castRadius h u).grad = u.grad := rfl

theorem mass_castRadius {R R' : ℝ} (h : R = R') (u : H1 (ball (0 : E) R)) :
    mass (castRadius h u) = mass u := by subst h; rfl

theorem dirichlet_castRadius {R R' : ℝ} (h : R = R') (u : H1 (ball (0 : E) R)) :
    dirichlet (castRadius h u) = dirichlet u := by subst h; rfl

end RobinCaps.Compact

end
