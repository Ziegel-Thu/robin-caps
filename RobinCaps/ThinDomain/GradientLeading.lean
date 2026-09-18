import RobinCaps.ThinDomain.ExpansionGen
import RobinCaps.ThinDomain.TrialBoundW
import RobinCaps.Cap.Sharp
import RobinCaps.Cap.Slices

/-!
# `rem:gradient-leading` / `eq:gradient-leading`: the second-order transverse expansion

This file proves the manuscript's second-order refinement of the transverse ground state
expansion (`rem:gradient-leading`), and its consequence for the leading order of the
transverse gradient energy on the unit hemispherical cap (`eq:gradient-leading`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.ThinDomain

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology InnerProductSpace

open RobinCaps.Sobolev.Weak RobinCaps.Compact

/-! ## 0. The explicit quadratic `v` and its gradient -/

/-- The explicit quadratic `v(z) = ω_m^{-1/2}·(m/(2(m+2)) − ‖z‖²/2)` of `rem:gradient-leading`,
on the unit ball `B_m(1)`. -/
def vquad_gl (m : ℕ) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (Real.sqrt (omega m))⁻¹ * ((m : ℝ) / (2 * ((m : ℝ) + 2)) - ‖y‖ ^ 2 / 2)

/-- The gradient of `vquad_gl`: `∇v(z) = -ω_m^{-1/2} z`. -/
def gradVquad_gl (m : ℕ) (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  -(Real.sqrt (omega m))⁻¹ • y

theorem continuous_gradVquad_gl (m : ℕ) : Continuous (gradVquad_gl m) := by
  unfold gradVquad_gl; fun_prop

theorem contDiff_vquad_gl (m : ℕ) : ContDiff ℝ 1 (vquad_gl m) := by
  unfold vquad_gl
  exact contDiff_const.mul (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const 2))

/-- The classical derivative of `vquad_gl` at `y`, as an explicit `HasFDerivAt` statement. -/
theorem hasFDerivAt_vquad_gl (m : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (vquad_gl m) (innerSL ℝ (gradVquad_gl m y)) y := by
  set d : ℝ := (Real.sqrt (omega m))⁻¹ with hd
  set A : ℝ := (m : ℝ) / (2 * ((m : ℝ) + 2)) with hA
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖ ^ 2 / 2)
      ((2 : ℝ)⁻¹ • (2 • innerSL ℝ y)) y := by
    have h1' := h1.const_smul (2 : ℝ)⁻¹
    simpa [div_eq_inv_mul, smul_eq_mul, mul_comm] using h1'
  have h3 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin m) => A - ‖z‖ ^ 2 / 2)
      (-((2 : ℝ)⁻¹ • (2 • innerSL ℝ y))) y :=
    h2.const_sub A
  have h4 := h3.fun_const_smul d
  have heq : d • (-((2 : ℝ)⁻¹ • (2 • innerSL ℝ y))) = innerSL ℝ (gradVquad_gl m y) := by
    have hs : d • (-((2 : ℝ)⁻¹ • (2 • innerSL ℝ y))) = (-d) • innerSL ℝ y := by module
    rw [hs, ← map_smul]
    congr 1
  rw [heq] at h4
  have hfun : (fun z : EuclideanSpace ℝ (Fin m) => d • (A - ‖z‖ ^ 2 / 2)) = vquad_gl m := by
    funext z
    simp only [vquad_gl, hd, hA, smul_eq_mul]
  rwa [hfun] at h4

theorem classicalGrad_vquad_gl (m : ℕ) : classicalGrad (vquad_gl m) = gradVquad_gl m := by
  funext y
  apply PiLp.ext
  intro i
  rw [classicalGrad_apply, (hasFDerivAt_vquad_gl m y).fderiv, innerSL_apply_apply,
    EuclideanSpace.inner_single_right]
  simp

/-- `∫_{B_1} ‖y‖² dy = m ω_m / (m+2)`. -/
theorem integral_normSq_ball_one_gl (m : ℕ) (hm : 1 ≤ m) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2)
      = (m : ℝ) * omega m / ((m : ℝ) + 2) := by
  have h := integral_ball_radial' m hm 1 (fun r => r ^ 2)
  simp only at h
  rw [h]
  have hpow : ∀ r : ℝ, r ^ (m - 1) * r ^ 2 = r ^ (m + 1) := by
    intro r
    rw [← pow_add]
    congr 1
    omega
  simp_rw [hpow]
  have hint : (∫ r in Ioo (0 : ℝ) 1, r ^ (m + 1)) = 1 / ((m : ℝ) + 2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    have hne : m + 1 + 1 ≠ 0 := by omega
    rw [one_pow, zero_pow hne]
    push_cast
    ring
  rw [hint]
  ring

/-- **`∫_{B_1} v = 0`**: the quadratic `vquad_gl` has zero mean on the unit ball. -/
theorem integral_vquad_ball_one_gl (m : ℕ) (hm : 1 ≤ m) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, vquad_gl m y) = 0 := by
  have hω : 0 < omega m := Cap.omega_pos m
  have hInt : IntegrableOn (fun y : EuclideanSpace ℝ (Fin m) => ‖y‖ ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    (integrableOn_ball_one_of_continuous (m := m) (by fun_prop))
  have hsplit : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, vquad_gl m y)
      = (Real.sqrt (omega m))⁻¹ *
        ((∫ _y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (m : ℝ) / (2 * ((m : ℝ) + 2)))
          - (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2) / 2) := by
    unfold vquad_gl
    rw [integral_const_mul]
    congr 1
    rw [← integral_div]
    exact integral_sub (integrable_const _) (hInt.div_const 2)
  rw [hsplit, setIntegral_const, measureReal_def, volume_ball_toReal m hm zero_le_one,
    integral_normSq_ball_one_gl m hm, one_pow, smul_eq_mul, one_mul]
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-! ## 1. The transverse ball `B_m(R)`: the quadratic `sqNormH1_gl` and the linearization -/

section GS

variable {m : ℕ} {α R : ℝ}

/-- The ambient Euclidean space `ℝᵐ`. -/
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- `z ↦ ‖z‖²` as an element of `H1(B_m(R))`. -/
noncomputable def sqNormH1_gl : H1 (ball (0 : E) R) :=
  ofC1 R (fun z => ‖z‖ ^ 2) (contDiff_norm_sq ℝ)

theorem sqNormH1_toFun_gl : (sqNormH1_gl (m := m) (R := R)).toFun = fun z => ‖z‖ ^ 2 := rfl

/-- The classical gradient of `‖·‖²` at any point: `∇(‖z‖²) = 2z`. -/
theorem classicalGrad_normSq_gl (z : E) :
    classicalGrad (fun w : E => ‖w‖ ^ 2) z = (2 : ℝ) • z := by
  apply PiLp.ext
  intro i
  rw [classicalGrad_apply, fderiv_norm_sq_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, EuclideanSpace.inner_single_right]
  simp

theorem sqNormH1_grad_gl :
    (sqNormH1_gl (m := m) (R := R)).grad = fun z => (2 : ℝ) • z := by
  unfold sqNormH1_gl
  rw [ofC1_grad]
  funext z
  exact classicalGrad_normSq_gl z

/-! ## 2. The linearization `d + t·v(·/R)`, pulled back to `B_m(R)` -/

/-- The constant (order-`1`) coefficient of the pullback linearization on `B_m(R)`. -/
noncomputable def linCoeff0_gl (m : ℕ) (R α : ℝ) : ℝ :=
  R ^ (-(m : ℝ) / 2) * (Real.sqrt (omega m))⁻¹ *
    (1 + α * R * ((m : ℝ) / (2 * ((m : ℝ) + 2))))

/-- The quadratic (order-`t`) coefficient of the pullback linearization on `B_m(R)`. -/
noncomputable def linCoeff2_gl (m : ℕ) (R α : ℝ) : ℝ :=
  R ^ (-(m : ℝ) / 2 - 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2

/-- **The pullback to `B_m(R)` of the affine approximation `d + t·v(·/R)`**, as an `H1(B_m(R))`
element: `linH1_gl = c₀ • 1 - c₂ • ‖·‖²`. -/
noncomputable def linH1_gl (α : ℝ) : H1 (ball (0 : E) R) :=
  linCoeff0_gl m R α • oneB m R - linCoeff2_gl m R α • sqNormH1_gl

theorem linH1_toFun_gl (α : ℝ) :
    (linH1_gl (m := m) (R := R) α).toFun
      = fun z => linCoeff0_gl m R α - linCoeff2_gl m R α * ‖z‖ ^ 2 := by
  funext z
  show ((linCoeff0_gl m R α • oneB m R : H1 (ball (0 : E) R))
      - linCoeff2_gl m R α • sqNormH1_gl).toFun z = _
  rw [H1.sub_toFun, H1.smul_toFun, H1.smul_toFun, oneB_toFun, sqNormH1_toFun_gl]
  simp

theorem linH1_grad_gl (α : ℝ) :
    (linH1_gl (m := m) (R := R) α).grad
      = fun z => -(2 * linCoeff2_gl m R α) • z := by
  funext z
  show ((linCoeff0_gl m R α • oneB m R : H1 (ball (0 : E) R))
      - linCoeff2_gl m R α • sqNormH1_gl).grad z = _
  rw [H1.sub_grad, H1.smul_grad, H1.smul_grad, oneB_grad, sqNormH1_grad_gl]
  simp [smul_smul, mul_comm]

/-- **The design identity for `linH1_gl`**: at `z = R•y`, the linearization pulls back exactly
to `R^{-m/2}·(d + αR·v(y))`. -/
theorem linH1_toFun_smul_gl (hR : 0 < R) (α : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    (linH1_gl (m := m) (R := R) α).toFun (R • y)
      = R ^ (-(m : ℝ) / 2) * ((Real.sqrt (omega m))⁻¹ + α * R * vquad_gl m y) := by
  rw [linH1_toFun_gl]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, abs_of_pos hR]
  unfold linCoeff0_gl linCoeff2_gl vquad_gl
  have e1 : R ^ (-(m : ℝ) / 2 - 2) * R ^ 2 = R ^ (-(m : ℝ) / 2) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR]
    norm_num
  have key : R ^ (-(m : ℝ) / 2 - 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2 * (R ^ 2 * ‖y‖ ^ 2)
      = R ^ (-(m : ℝ) / 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2 * ‖y‖ ^ 2 := by
    rw [show R ^ (-(m : ℝ) / 2 - 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2 * (R ^ 2 * ‖y‖ ^ 2)
        = (R ^ (-(m : ℝ) / 2 - 2) * R ^ 2) * ((α * R) * (Real.sqrt (omega m))⁻¹ / 2 * ‖y‖ ^ 2)
        from by ring, e1]
    ring
  rw [key]
  ring

/-! ## 3. Bilinearity of `bdR`, `dirichletBilin`, `NBilin` against `linH1_gl` -/

theorem bdR_linH1_gl (φ : H1 (ball (0 : E) R)) :
    bdR m R (linH1_gl α) φ = linCoeff0_gl m R α * bdR m R (oneB m R) φ
      - linCoeff2_gl m R α * bdR m R sqNormH1_gl φ := by
  unfold linH1_gl
  rw [map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

theorem dirichletBilin_oneB_gl (φ : H1 (ball (0 : E) R)) :
    dirichletBilin (oneB m R) φ = 0 := by
  unfold dirichletBilin
  rw [oneB_grad]
  simp

theorem dirichletBilin_linH1_gl (φ : H1 (ball (0 : E) R)) :
    dirichletBilin (linH1_gl (m := m) (R := R) α) φ
      = -linCoeff2_gl m R α * dirichletBilin sqNormH1_gl φ := by
  unfold linH1_gl
  rw [← dirichletBilinₗ_apply, map_sub, map_smul, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, dirichletBilinₗ_apply, dirichletBilinₗ_apply,
    dirichletBilin_oneB_gl, smul_eq_mul, smul_eq_mul]
  ring

theorem NBilin_linH1_gl (φ : H1 (ball (0 : E) R)) :
    NBilin (linH1_gl (m := m) (R := R) α) φ = linCoeff0_gl m R α * (∫ z in ball (0 : E) R, φ.toFun z)
      - linCoeff2_gl m R α * (∫ z in ball (0 : E) R, ‖z‖ ^ 2 * φ.toFun z) := by
  unfold linH1_gl
  show NBilinₗ m R _ φ = _
  rw [map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, NBilinₗ_apply, NBilinₗ_apply,
    NBilin_comm (oneB m R) φ, NBilin_oneB]
  congr 2

/-! ## 4. The remainder `qR_gl := ψ - linH1_gl`, and its basic bounds -/

/-- `transLiftGrad_tw` and `transLiftGrad_xg` coincide (they are defined by the same formula). -/
theorem transLiftGrad_tw_eq_xg_gl (ψ : TransH1 m R) :
    transLiftGrad_tw m R ψ = transLiftGrad_xg m R ψ := rfl

/-- **`dirichlet(ψ_R) ≤ Cexp²`**, an `R`-uniform bound coming from `hexp.grad_le`. -/
theorem dirichlet_psi_le_Cexp_sq_gl (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R))
    {Cexp : ℝ} (hexp : ExpW_tw m α R gs Cexp) :
    dirichlet gs.psi ≤ Cexp ^ 2 := by
  have h1 := hexp.grad_le
  rw [transLiftGrad_tw_eq_xg_gl, integral_transLiftGrad_sq_eq_xg hR gs.psi] at h1
  have hR2 : (0:ℝ) < R ^ 2 := by positivity
  have h3 : dirichlet gs.psi * R ^ 2 ≤ Cexp ^ 2 * R ^ 2 := by nlinarith [h1]
  exact le_of_mul_le_mul_right h3 hR2

/-- **The remainder** `q_R := ψ_R - linH1_gl α`, whose lift to `B_m(1)` is
`Ψ_R - d - α R · v`. -/
noncomputable def qR_gl (gs : TransverseGroundState m α R (bdR m R)) : H1 (ball (0 : E) R) :=
  @HSub.hSub (H1 (ball (0 : E) R)) (H1 (ball (0 : E) R)) (H1 (ball (0 : E) R)) _
    gs.psi (linH1_gl α)

theorem qR_toFun_gl (gs : TransverseGroundState m α R (bdR m R)) :
    (qR_gl gs).toFun = fun z => gs.psi.toFun z - (linH1_gl (m := m) (R := R) α).toFun z := by
  unfold qR_gl
  rw [H1.sub_toFun]
  rfl

theorem qR_grad_gl (gs : TransverseGroundState m α R (bdR m R)) :
    (qR_gl gs).grad = fun z => gs.psi.grad z - (linH1_gl (m := m) (R := R) α).grad z := by
  unfold qR_gl
  rw [H1.sub_grad]
  rfl

/-- **The pointwise design identity**: `Ψ_R(y) - d - αR·v(y) = R^{m/2}·q_R(Ry)`. -/
theorem F_eq_qR_gl_smul_gl (hR : 0 < R) (α : ℝ) (gs : TransverseGroundState m α R (bdR m R))
    (y : EuclideanSpace ℝ (Fin m)) :
    transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y
      = R ^ ((m : ℝ) / 2) * (qR_gl gs).toFun (R • y) := by
  have hexp : (m : ℝ) / 2 + -(m : ℝ) / 2 = 0 := by ring
  have e : R ^ ((m : ℝ) / 2) * R ^ (-(m : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hR, hexp, Real.rpow_zero]
  simp only [qR_toFun_gl]
  rw [linH1_toFun_smul_gl hR α y, mul_sub, ← mul_assoc, e, one_mul]
  unfold transLift
  ring

theorem qR_toFun_smul_gl (hR : 0 < R) (α : ℝ) (gs : TransverseGroundState m α R (bdR m R))
    (y : EuclideanSpace ℝ (Fin m)) :
    (qR_gl gs).toFun (R • y)
      = R ^ (-(m : ℝ) / 2) *
        (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y) := by
  rw [F_eq_qR_gl_smul_gl hR α gs y, ← mul_assoc]
  have hexp : -(m : ℝ) / 2 + (m : ℝ) / 2 = 0 := by ring
  have e : R ^ (-(m : ℝ) / 2) * R ^ ((m : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hR, hexp, Real.rpow_zero]
  rw [e, one_mul]

/-- **The exact first-moment identity**: `∫_{B_R} q_R = R^{m/2}·(∫_{B_1}Ψ_R - √ω_m)`. -/
theorem integral_qR_gl_toFun_gl (hm : 1 ≤ m) (hR : 0 < R) (α : ℝ)
    (gs : TransverseGroundState m α R (bdR m R)) :
    (∫ z in ball (0 : E) R, (qR_gl gs).toFun z)
      = R ^ ((m : ℝ) / 2) *
        ((∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
          - Real.sqrt (omega m)) := by
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR (qR_gl gs).toFun
  rw [mul_one] at h
  rw [h, show (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (qR_gl gs).toFun (R • y))
      = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, R ^ (-(m : ℝ) / 2) *
        (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y)
      from setIntegral_congr_fun measurableSet_ball
        (fun y _ => qR_toFun_smul_gl hR α gs y)]
  rw [integral_const_mul]
  have hTL : IntegrableOn (transLift m R gs.psi) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    (memLp_transLift_tw hR gs.psi).integrable one_le_two
  have hv : IntegrableOn (vquad_gl m) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    integrableOn_ball_one_of_continuous (contDiff_vquad_gl m).continuous
  have hVone : (volume (ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal = omega m := by
    rw [volume_ball_toReal m hm zero_le_one, one_pow, one_mul]
  have hc : (∫ _y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, (Real.sqrt (omega m))⁻¹)
      = Real.sqrt (omega m) := by
    rw [setIntegral_const, measureReal_def, hVone, smul_eq_mul]
    have hωeq : omega m = Real.sqrt (omega m) * Real.sqrt (omega m) :=
      (Real.mul_self_sqrt (Cap.omega_pos m).le).symm
    have hω0 : Real.sqrt (omega m) ≠ 0 := (Real.sqrt_pos.mpr (Cap.omega_pos m)).ne'
    field_simp
    linarith [hωeq]
  have hv0 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, α * R * vquad_gl m y) = 0 := by
    rw [integral_const_mul, integral_vquad_ball_one_gl m hm, mul_zero]
  have e1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y)
      = (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹)
        - ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, α * R * vquad_gl m y := by
    apply integral_sub
    · exact hTL.sub (integrable_const _)
    · exact hv.const_mul _
  have e3 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹)
      = (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        - Real.sqrt (omega m) := by
    rw [integral_sub hTL (integrable_const _), hc]
  have hsplit : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y))
      = (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        - Real.sqrt (omega m) := by
    rw [e1, e3, hv0, sub_zero]
  rw [hsplit, ← mul_assoc]
  have hexp : (m : ℝ) + -(m : ℝ) / 2 = (m : ℝ) / 2 := by ring
  have e2 : R ^ m * R ^ (-(m : ℝ) / 2) = R ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast R m, ← Real.rpow_add hR, hexp]
  rw [e2]

/-! ## 6. The sharp `O(R²)` mean bound, from `dR_sq_eq_xg` and Poincaré–Wirtinger -/

/-- `hexp.dR_ge` forces `0 ≤ ∫_{B_R} ψ`. -/
theorem hI0_of_dR_ge_gl (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R)) {Cexp : ℝ}
    (hexp : ExpW_tw m α R gs Cexp) :
    0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z := by
  have h1 := hexp.dR_ge
  rw [integral_transLift_eq_xg hR gs.psi] at h1
  have hωpos : 0 < omega m := Cap.omega_pos m
  have hRpow : 0 < R ^ ((m : ℝ) / 2) := Real.rpow_pos_of_pos hR _
  have hsqrtpos : 0 < Real.sqrt (omega m) := Real.sqrt_pos.mpr hωpos
  have hmeanB_pos : 0 < meanB gs.psi := by
    by_contra hle
    push_neg at hle
    have hnp : meanB gs.psi * omega m * R ^ ((m : ℝ) / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle hωpos.le) hRpow.le
    linarith [h1, hsqrtpos]
  have hMB := meanB_mul_volume hR gs.psi
  have hVpos := volume_ball_toReal_pos (n := m) hR
  nlinarith [hMB, mul_pos hmeanB_pos hVpos]

/-- **The sharp `O(R²)` bound on `d_R − √ω_m`**, using `dR_sq_eq_xg` and Poincaré–Wirtinger
in place of the generic `O(R)` estimate `dR_close_xg`. -/
theorem sharp_mean_bound_gl (hR : 0 < R) {Cexp CP : ℝ} (hCP : 0 < CP)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ CP * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R)) (hexp : ExpW_tw m α R gs Cexp)
    (hsmall : CP * Cexp ^ 2 * R ^ 2 ≤ 1) :
    |(∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        - Real.sqrt (omega m)| ≤ Real.sqrt (omega m) * (CP * Cexp ^ 2 * R ^ 2) := by
  have hI0 := hI0_of_dR_ge_gl hR gs hexp
  have hd := dirichlet_psi_le_Cexp_sq_gl hR gs hexp
  have hpo := mass_meanZero_le_poincare hR hpw gs.psi
  have he1 : mass (meanZero gs.psi) ≤ CP * Cexp ^ 2 * R ^ 2 := by
    have hstep : CP * R ^ 2 * dirichlet gs.psi ≤ CP * R ^ 2 * Cexp ^ 2 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    nlinarith [hpo, hstep]
  have he1' : mass (meanZero gs.psi) ≤ 1 := le_trans he1 hsmall
  have hclose := dR_close_xg hR gs hI0 he1'
  have hωnn : (0:ℝ) ≤ Real.sqrt (omega m) := Real.sqrt_nonneg _
  calc |(∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      - Real.sqrt (omega m)| ≤ Real.sqrt (omega m) * mass (meanZero gs.psi) := hclose
    _ ≤ Real.sqrt (omega m) * (CP * Cexp ^ 2 * R ^ 2) := by
        exact mul_le_mul_of_nonneg_left he1 hωnn

theorem psi_eq_qR_gl_add_linH1_gl (gs : TransverseGroundState m α R (bdR m R)) :
    (gs.psi : H1 (ball (0 : E) R)) = qR_gl gs + linH1_gl α := by
  unfold qR_gl
  rw [sub_add_cancel]

/-! ## 5. The mean-zero testing identities (mirroring `ExpansionSharp.lean`'s pattern, but for
`qR_gl` instead of `ψ`) -/

theorem dirichletBilin_congr_right_grad_gl {u v w : H1 (ball (0 : E) R)} (h : v.grad = w.grad) :
    dirichletBilin u v = dirichletBilin u w := by
  unfold dirichletBilin
  simp only [h]

theorem dirichletBilin_meanZero_self_gl (u : H1 (ball (0 : E) R)) :
    dirichletBilin u (meanZero u) = dirichlet u := by
  rw [dirichletBilin_congr_right_grad_gl (meanZero_grad u), dirichletBilin_self]

theorem NBilin_meanZero_self_gl (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    NBilin u (meanZero u) = mass (meanZero u) := by
  have heq : u = meanZero u + meanB u • oneB m R := by
    have h := sub_meanZero u
    rw [sub_eq_iff_eq_add'] at h
    exact h
  have hstep : NBilin u (meanZero u)
      = NBilin (meanZero u + meanB u • oneB m R) (meanZero u) := by rw [← heq]
  rw [hstep]
  show NBilinₗ m R (meanZero u + meanB u • oneB m R) (meanZero u) = mass (meanZero u)
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    NBilinₗ_apply, NBilinₗ_apply]
  have hcross0 : NBilin (oneB m R) (meanZero u) = 0 := by
    show massBilin (oneB m R) (meanZero u) = 0
    unfold massBilin
    rw [oneB_toFun]
    simp only [one_mul]
    exact integral_meanZero hR u
  rw [hcross0, NBilin_self]
  show mass (meanZero u) + meanB u * 0 = mass (meanZero u)
  ring

/-- **The bilinear decomposition of `bdR(u, meanZero u)`**: `bdR(u,u₀) = bdR(u₀,u₀) +
meanB(u)·bdR(1,u₀)`, `u₀ = meanZero u`. -/
theorem bdR_meanZero_self_expand_gl (u : H1 (ball (0 : E) R)) :
    bdR m R u (meanZero u) = bdR m R (meanZero u) (meanZero u)
      + meanB u * bdR m R (oneB m R) (meanZero u) := by
  have heq : u = meanZero u + meanB u • oneB m R := by
    have h := sub_meanZero u
    rw [sub_eq_iff_eq_add'] at h
    exact h
  have hstep : bdR m R u (meanZero u)
      = bdR m R (meanZero u + meanB u • oneB m R) (meanZero u) := by rw [← heq]
  rw [hstep, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-! ## 7. The mean-square bound on `q_R` -/

/-- **`meanB(q_R)² · V ≤ (CP·Cexp²·R²)²`**: the mean of `q_R` is `O(R²)`-small in the
`meanB²·V` sense. -/
theorem meanB_sq_mul_volume_qR_gl (hm : 1 ≤ m) (hR : 0 < R) {Cexp CP : ℝ} (hCP : 0 < CP)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ CP * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R)) (hexp : ExpW_tw m α R gs Cexp)
    (hsmall : CP * Cexp ^ 2 * R ^ 2 ≤ 1) :
    meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal ≤ (CP * Cexp ^ 2 * R ^ 2) ^ 2 := by
  set X : ℝ := (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    - Real.sqrt (omega m) with hX
  have hωpos : 0 < omega m := Cap.omega_pos m
  have hVpos : 0 < (volume (ball (0 : E) R)).toReal := volume_ball_toReal_pos (n := m) hR
  have hclose := sharp_mean_bound_gl hR hCP hpw gs hexp hsmall
  rw [← hX] at hclose
  have hsq : X ^ 2 ≤ (Real.sqrt (omega m) * (CP * Cexp ^ 2 * R ^ 2)) ^ 2 := by
    calc X ^ 2 = |X| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt (omega m) * (CP * Cexp ^ 2 * R ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hclose 2
  have hsq2 : X ^ 2 ≤ omega m * (CP * Cexp ^ 2 * R ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hωpos.le] at hsq
    exact hsq
  have hMB := meanB_mul_volume hR (qR_gl gs)
  rw [integral_qR_gl_toFun_gl hm hR α gs, ← hX] at hMB
  have hVeq := volume_ball_toReal_eq (n := m) hR
  have hrm2 : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hkey : (meanB (qR_gl gs) * (volume (ball (0 : E) R)).toReal) ^ 2
      ≤ (volume (ball (0 : E) R)).toReal * (CP * Cexp ^ 2 * R ^ 2) ^ 2 := by
    rw [hMB, mul_pow, hrm2, hVeq]
    calc R ^ m * X ^ 2 ≤ R ^ m * (omega m * (CP * Cexp ^ 2 * R ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq2 (by positivity)
      _ = omega m * R ^ m * (CP * Cexp ^ 2 * R ^ 2) ^ 2 := by ring
  have hstep : (meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal)
      * (volume (ball (0 : E) R)).toReal
      ≤ (CP * Cexp ^ 2 * R ^ 2) ^ 2 * (volume (ball (0 : E) R)).toReal := by
    have hrw : (meanB (qR_gl gs) * (volume (ball (0 : E) R)).toReal) ^ 2
        = (meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal)
          * (volume (ball (0 : E) R)).toReal := by ring
    rw [hrw] at hkey
    linarith [hkey]
  exact le_of_mul_le_mul_right hstep hVpos

/-! ## 8. Cauchy–Schwarz bounds for `sqNormH1_gl`, and its exact link to `bdR(oneB,·)` -/

/-- **Cauchy–Schwarz**: `∫_{B_R} |f| ≤ √V·√(∫f²)`. -/
theorem integral_abs_le_sqrt_mul_sqrt_gl (f : E → ℝ)
    (hf : MemLp f 2 (volume.restrict (ball (0 : E) R))) :
    (∫ z in ball (0 : E) R, |f z|)
      ≤ Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (∫ z in ball (0 : E) R, f z ^ 2) := by
  have hf1 : MemLp (fun _ : E => (1 : ℝ)) 2 (volume.restrict (ball (0 : E) R)) :=
    memLp_two_of_continuous continuous_const
  have hcs := integral_norm_mul_norm_le hf1 hf
  simp only [norm_one, one_mul] at hcs
  have hcsR1 : (∫ _z in ball (0 : E) R, (1 : ℝ) ^ 2) = (volume (ball (0 : E) R)).toReal := by
    simp only [one_pow]
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
  rw [hcsR1] at hcs
  have heq : (∫ z in ball (0 : E) R, ‖f z‖ ^ 2) = ∫ z in ball (0 : E) R, f z ^ 2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _
    simp [Real.norm_eq_abs, sq_abs]
  have heq2 : (∫ z in ball (0 : E) R, ‖f z‖) = ∫ z in ball (0 : E) R, |f z| := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _
    simp [Real.norm_eq_abs]
  rwa [heq, heq2] at hcs

/-- `|∫_{B_R} ‖z‖² φ(z)| ≤ R² · √V · √(mass φ)`. -/
theorem abs_integral_normSq_mul_le_gl (hR : 0 < R) (φ : H1 (ball (0 : E) R)) :
    |∫ z in ball (0 : E) R, ‖z‖ ^ 2 * φ.toFun z|
      ≤ R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (mass φ) := by
  have hφ1 : Integrable φ.toFun (volume.restrict (ball (0 : E) R)) := integrable_toFun φ
  have hdom : Integrable (fun z : E => R ^ 2 * |φ.toFun z|) (volume.restrict (ball (0 : E) R)) :=
    hφ1.abs.const_mul _
  have hmeas : AEStronglyMeasurable (fun z : E => ‖z‖ ^ 2 * φ.toFun z)
      (volume.restrict (ball (0 : E) R)) :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul hφ1.aestronglyMeasurable
  have hle : ∀ᵐ z ∂(volume.restrict (ball (0 : E) R)), ‖‖z‖ ^ 2 * φ.toFun z‖ ≤ R ^ 2 * |φ.toFun z| := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖z‖)]
    have hzR : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.1 hz)
    have hzR2 : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z, hzR]
    exact mul_le_mul_of_nonneg_right hzR2 (abs_nonneg _)
  have hint : Integrable (fun z : E => ‖z‖ ^ 2 * φ.toFun z) (volume.restrict (ball (0 : E) R)) :=
    hdom.mono' hmeas hle
  have h1 : |∫ z in ball (0 : E) R, ‖z‖ ^ 2 * φ.toFun z| ≤ ∫ z in ball (0 : E) R, R ^ 2 * |φ.toFun z| :=
    (abs_integral_le_integral_abs).trans (integral_mono_ae hint.abs hdom hle)
  have h2 : (∫ z in ball (0 : E) R, R ^ 2 * |φ.toFun z|) = R ^ 2 * ∫ z in ball (0 : E) R, |φ.toFun z| :=
    integral_const_mul _ _
  have h3 : (∫ z in ball (0 : E) R, |φ.toFun z|)
      ≤ Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (mass φ) :=
    integral_abs_le_sqrt_mul_sqrt_gl φ.toFun φ.memL2
  calc |∫ z in ball (0 : E) R, ‖z‖ ^ 2 * φ.toFun z| ≤ ∫ z in ball (0 : E) R, R ^ 2 * |φ.toFun z| := h1
    _ = R ^ 2 * ∫ z in ball (0 : E) R, |φ.toFun z| := h2
    _ ≤ R ^ 2 * (Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (mass φ)) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg R)
    _ = R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (mass φ) := by ring

/-- `|∫_{B_R} ⟪z, ∇φ(z)⟫| ≤ R · √V · √(dirichlet φ)`. -/
theorem abs_integral_inner_grad_le_gl (hR : 0 < R) (φ : H1 (ball (0 : E) R)) :
    |∫ z in ball (0 : E) R, ⟪z, φ.grad z⟫_ℝ|
      ≤ R * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ) := by
  have hgint : Integrable (fun z : E => ‖φ.grad z‖) (volume.restrict (ball (0 : E) R)) :=
    φ.grad_memL2.norm.integrable one_le_two
  have hIinner : Integrable (fun z : E => ⟪z, φ.grad z⟫_ℝ) (volume.restrict (ball (0 : E) R)) :=
    (memLp_inner_grad φ).integrable one_le_two
  have hbound : Integrable (fun z : E => R * ‖φ.grad z‖) (volume.restrict (ball (0 : E) R)) :=
    hgint.const_mul R
  have hle : ∀ᵐ z ∂(volume.restrict (ball (0 : E) R)), |⟪z, φ.grad z⟫_ℝ| ≤ R * ‖φ.grad z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact abs_inner_le_of_mem_ball hz (φ.grad z)
  have h1 : |∫ z in ball (0 : E) R, ⟪z, φ.grad z⟫_ℝ| ≤ ∫ z in ball (0 : E) R, R * ‖φ.grad z‖ :=
    (abs_integral_le_integral_abs).trans (integral_mono_ae hIinner.abs hbound hle)
  have h2 : (∫ z in ball (0 : E) R, R * ‖φ.grad z‖) = R * ∫ z in ball (0 : E) R, ‖φ.grad z‖ :=
    integral_const_mul R _
  have h3 : (∫ z in ball (0 : E) R, ‖φ.grad z‖)
      ≤ Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ) := by
    have hf1 : MemLp (fun _ : E => (1 : ℝ)) 2 (volume.restrict (ball (0 : E) R)) :=
      memLp_two_of_continuous continuous_const
    have hcs := integral_norm_mul_norm_le hf1 φ.grad_memL2
    have hcsL : (∫ z in ball (0 : E) R, ‖(1 : ℝ)‖ * ‖φ.grad z‖) = ∫ z in ball (0 : E) R, ‖φ.grad z‖ := by
      simp
    have hcsR1 : (∫ z in ball (0 : E) R, ‖(1 : ℝ)‖ ^ 2) = (volume (ball (0 : E) R)).toReal := by
      simp only [norm_one, one_pow]
      rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
    have hcsR2 : (∫ z in ball (0 : E) R, ‖φ.grad z‖ ^ 2) = dirichlet φ := integral_norm_grad_sq φ
    rw [hcsL, hcsR1, hcsR2] at hcs
    exact hcs
  calc |∫ z in ball (0 : E) R, ⟪z, φ.grad z⟫_ℝ| ≤ ∫ z in ball (0 : E) R, R * ‖φ.grad z‖ := h1
    _ = R * ∫ z in ball (0 : E) R, ‖φ.grad z‖ := h2
    _ ≤ R * (Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ)) :=
        mul_le_mul_of_nonneg_left h3 hR.le
    _ = R * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ) := by ring

/-- `|∫_{B_R} ‖z‖² ⟪z, ∇φ(z)⟫| ≤ R³ · √V · √(dirichlet φ)`. -/
theorem abs_integral_normSq_inner_grad_le_gl (hR : 0 < R) (φ : H1 (ball (0 : E) R)) :
    |∫ z in ball (0 : E) R, ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ|
      ≤ R ^ 3 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ) := by
  have hgint : Integrable (fun z : E => ‖φ.grad z‖) (volume.restrict (ball (0 : E) R)) :=
    φ.grad_memL2.norm.integrable one_le_two
  have hIinner : Integrable (fun z : E => ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ)
      (volume.restrict (ball (0 : E) R)) := by
    have hmeas : AEStronglyMeasurable (fun z : E => ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ)
        (volume.restrict (ball (0 : E) R)) :=
      (continuous_norm.pow 2).aestronglyMeasurable.mul
        (memLp_inner_grad φ).aestronglyMeasurable
    have hdom : Integrable (fun z : E => R ^ 3 * ‖φ.grad z‖) (volume.restrict (ball (0 : E) R)) :=
      hgint.const_mul _
    have hle : ∀ᵐ z ∂(volume.restrict (ball (0 : E) R)),
        ‖‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ‖ ≤ R ^ 3 * ‖φ.grad z‖ := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hzR : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.1 hz)
      have hzn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖z‖)]
      calc ‖z‖ ^ 2 * |⟪z, φ.grad z⟫_ℝ| ≤ ‖z‖ ^ 2 * (‖z‖ * ‖φ.grad z‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z (φ.grad z)) (sq_nonneg _)
        _ = ‖z‖ ^ 3 * ‖φ.grad z‖ := by ring
        _ ≤ R ^ 3 * ‖φ.grad z‖ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hzn hzR 3) (norm_nonneg _)
    exact hdom.mono' hmeas hle
  have hdom : Integrable (fun z : E => R ^ 3 * ‖φ.grad z‖) (volume.restrict (ball (0 : E) R)) :=
    hgint.const_mul _
  have hle : ∀ᵐ z ∂(volume.restrict (ball (0 : E) R)),
      |‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ| ≤ R ^ 3 * ‖φ.grad z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzR : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.1 hz)
    have hzn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖z‖)]
    calc ‖z‖ ^ 2 * |⟪z, φ.grad z⟫_ℝ| ≤ ‖z‖ ^ 2 * (‖z‖ * ‖φ.grad z‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z (φ.grad z)) (sq_nonneg _)
      _ = ‖z‖ ^ 3 * ‖φ.grad z‖ := by ring
      _ ≤ R ^ 3 * ‖φ.grad z‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hzn hzR 3) (norm_nonneg _)
  have h1 : |∫ z in ball (0 : E) R, ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ|
      ≤ ∫ z in ball (0 : E) R, R ^ 3 * ‖φ.grad z‖ :=
    (abs_integral_le_integral_abs).trans (integral_mono_ae hIinner.abs hdom hle)
  have h2 : (∫ z in ball (0 : E) R, R ^ 3 * ‖φ.grad z‖) = R ^ 3 * ∫ z in ball (0 : E) R, ‖φ.grad z‖ :=
    integral_const_mul _ _
  have h3 : (∫ z in ball (0 : E) R, ‖φ.grad z‖)
      ≤ Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ) := by
    have hf1 : MemLp (fun _ : E => (1 : ℝ)) 2 (volume.restrict (ball (0 : E) R)) :=
      memLp_two_of_continuous continuous_const
    have hcs := integral_norm_mul_norm_le hf1 φ.grad_memL2
    have hcsL : (∫ z in ball (0 : E) R, ‖(1 : ℝ)‖ * ‖φ.grad z‖) = ∫ z in ball (0 : E) R, ‖φ.grad z‖ := by
      simp
    have hcsR1 : (∫ z in ball (0 : E) R, ‖(1 : ℝ)‖ ^ 2) = (volume (ball (0 : E) R)).toReal := by
      simp only [norm_one, one_pow]
      rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
    have hcsR2 : (∫ z in ball (0 : E) R, ‖φ.grad z‖ ^ 2) = dirichlet φ := integral_norm_grad_sq φ
    rw [hcsL, hcsR1, hcsR2] at hcs
    exact hcs
  calc |∫ z in ball (0 : E) R, ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ|
      ≤ ∫ z in ball (0 : E) R, R ^ 3 * ‖φ.grad z‖ := h1
    _ = R ^ 3 * ∫ z in ball (0 : E) R, ‖φ.grad z‖ := h2
    _ ≤ R ^ 3 * (Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = R ^ 3 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ) := by ring

/-! ## 9. `bdR(sqNormH1_gl,·)` and `dirichletBilin(sqNormH1_gl,·)`: formulas and bounds -/

/-- **The explicit formula for `bdR(‖·‖², φ)`** via `bdR_apply`. -/
theorem bdR_sqNormH1_eq_gl (φ : H1 (ball (0 : E) R)) :
    bdR m R sqNormH1_gl φ
      = R⁻¹ * (((m : ℝ) + 2) * (∫ z in ball (0 : E) R, ‖z‖ ^ 2 * φ.toFun z)
          + ∫ z in ball (0 : E) R, ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ) := by
  have hφ1 : Integrable φ.toFun (volume.restrict (ball (0 : E) R)) := integrable_toFun φ
  have hmeas1 : AEStronglyMeasurable (fun z : E => ‖z‖ ^ 2 * φ.toFun z)
      (volume.restrict (ball (0 : E) R)) :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul hφ1.aestronglyMeasurable
  have hdom1 : Integrable (fun z : E => R ^ 2 * |φ.toFun z|) (volume.restrict (ball (0 : E) R)) :=
    hφ1.abs.const_mul _
  have hle1 : ∀ᵐ z ∂(volume.restrict (ball (0 : E) R)), ‖‖z‖ ^ 2 * φ.toFun z‖ ≤ R ^ 2 * |φ.toFun z| := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖z‖)]
    have hzR2 : ‖z‖ ^ 2 ≤ R ^ 2 := by
      have := mem_ball_zero_iff.1 hz
      nlinarith [norm_nonneg z, this]
    exact mul_le_mul_of_nonneg_right hzR2 (abs_nonneg _)
  have hint1 : Integrable (fun z : E => ‖z‖ ^ 2 * φ.toFun z) (volume.restrict (ball (0 : E) R)) :=
    hdom1.mono' hmeas1 hle1
  have hgint : Integrable (fun z : E => ‖φ.grad z‖) (volume.restrict (ball (0 : E) R)) :=
    φ.grad_memL2.norm.integrable one_le_two
  have hmeas2 : AEStronglyMeasurable (fun z : E => ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ)
      (volume.restrict (ball (0 : E) R)) :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul (memLp_inner_grad φ).aestronglyMeasurable
  have hdom2 : Integrable (fun z : E => R ^ 3 * ‖φ.grad z‖) (volume.restrict (ball (0 : E) R)) :=
    hgint.const_mul _
  have hle2 : ∀ᵐ z ∂(volume.restrict (ball (0 : E) R)),
      ‖‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ‖ ≤ R ^ 3 * ‖φ.grad z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzR : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.1 hz)
    have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖z‖)]
    calc ‖z‖ ^ 2 * |⟪z, φ.grad z⟫_ℝ| ≤ ‖z‖ ^ 2 * (‖z‖ * ‖φ.grad z‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm z (φ.grad z)) (sq_nonneg _)
      _ = ‖z‖ ^ 3 * ‖φ.grad z‖ := by ring
      _ ≤ R ^ 3 * ‖φ.grad z‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hzn hzR 3) (norm_nonneg _)
  have hint2 : Integrable (fun z : E => ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ)
      (volume.restrict (ball (0 : E) R)) :=
    hdom2.mono' hmeas2 hle2
  rw [bdR_apply]
  congr 1
  rw [show (fun z : E => (m : ℝ) * (sqNormH1_gl.toFun z * φ.toFun z)
        + sqNormH1_gl.toFun z * ⟪z, φ.grad z⟫_ℝ + φ.toFun z * ⟪z, sqNormH1_gl.grad z⟫_ℝ)
      = (fun z => ((m : ℝ) + 2) * (‖z‖ ^ 2 * φ.toFun z) + ‖z‖ ^ 2 * ⟪z, φ.grad z⟫_ℝ) from ?_,
    integral_add (hint1.const_mul _) hint2, integral_const_mul]
  funext z
  rw [sqNormH1_toFun_gl, sqNormH1_grad_gl]
  have hinner2 : (⟪z, (2 : ℝ) • z⟫_ℝ) = 2 * ‖z‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hinner2]
  ring

/-- **The Cauchy–Schwarz bound on `bdR(‖·‖², φ)`.** -/
theorem abs_bdR_sqNormH1_le_gl (hR : 0 < R) (φ : H1 (ball (0 : E) R)) :
    |bdR m R sqNormH1_gl φ|
      ≤ R⁻¹ * (((m : ℝ) + 2)
          * (R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (mass φ))
        + R ^ 3 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (dirichlet φ)) := by
  rw [bdR_sqNormH1_eq_gl, abs_mul, abs_of_pos (inv_pos.2 hR)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hR).le
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2)]
    exact mul_le_mul_of_nonneg_left (abs_integral_normSq_mul_le_gl hR φ) (by positivity)
  · exact abs_integral_normSq_inner_grad_le_gl hR φ

/-- **`dirichletBilin(‖·‖², φ) = 2·∫⟪z, ∇φ⟫`.** -/
theorem dirichletBilin_sqNormH1_eq_gl (φ : H1 (ball (0 : E) R)) :
    dirichletBilin sqNormH1_gl φ = 2 * ∫ z in ball (0 : E) R, ⟪z, φ.grad z⟫_ℝ := by
  unfold dirichletBilin
  rw [sqNormH1_grad_gl, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_ball
  intro z _
  simp [real_inner_smul_left]

/-- **The exact cancellation identity**: at `φ = meanZero u`, `dirichletBilin(‖·‖², φ)` reduces
exactly to `2R·bdR(1, φ)` (no error, since `∫φ = 0` kills the `m·∫φ` term of the Rellich
identity). -/
theorem dirichletBilin_sqNormH1_meanZero_eq_gl (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    dirichletBilin sqNormH1_gl (meanZero u) = 2 * R * bdR m R (oneB m R) (meanZero u) := by
  rw [dirichletBilin_sqNormH1_eq_gl]
  have hgrad : (∫ z in ball (0 : E) R, ⟪z, (meanZero u).grad z⟫_ℝ)
      = ∫ z in ball (0 : E) R, ⟪z, u.grad z⟫_ℝ := by
    rw [meanZero_grad]
  rw [hgrad, bdR_oneB_meanZero_eq_xg hR u]
  field_simp

/-! ## 10. The master weak-equation identity, and the `O(R²)` bound on `dirichlet(q_R)` -/

theorem nu_nonneg_gl (hα : 0 ≤ α) (gs : TransverseGroundState m α R (bdR m R)) :
    0 ≤ gs.nu := by
  rw [gs.nu_eq_rayleigh]
  show 0 ≤ dirichlet gs.psi + α * bdR m R gs.psi gs.psi
  have h1 := dirichlet_nonneg gs.psi
  have h2 := gs.bdNonneg gs.psi
  exact add_nonneg h1 (mul_nonneg hα h2)

/-! ### The `qR_gl`-vs-`gs.psi` real-number identities (avoiding any `H1`-level `+`) -/

theorem dirichletBilin_qR_eq_gl (gs : TransverseGroundState m α R (bdR m R))
    (φ : H1 (ball (0 : E) R)) :
    dirichletBilin (qR_gl gs) φ
      = dirichletBilin gs.psi φ - dirichletBilin (linH1_gl (m := m) (R := R) α) φ := by
  unfold qR_gl
  rw [← dirichletBilinₗ_apply, map_sub, LinearMap.sub_apply, dirichletBilinₗ_apply,
    dirichletBilinₗ_apply]

theorem bdR_qR_eq_gl (gs : TransverseGroundState m α R (bdR m R)) (φ : H1 (ball (0 : E) R)) :
    bdR m R (qR_gl gs) φ = bdR m R gs.psi φ - bdR m R (linH1_gl α) φ := by
  unfold qR_gl
  rw [map_sub, LinearMap.sub_apply]

theorem NBilin_qR_eq_gl (gs : TransverseGroundState m α R (bdR m R)) (φ : H1 (ball (0 : E) R)) :
    NBilin (qR_gl gs) φ = NBilin gs.psi φ - NBilin (linH1_gl (m := m) (R := R) α) φ := by
  unfold qR_gl
  show NBilinₗ m R _ φ = _
  rw [map_sub, LinearMap.sub_apply, NBilinₗ_apply, NBilinₗ_apply]

/-- `sq_le_of_le_mul_sqrt`: if `0 ≤ x`, `0 ≤ k` and `x ≤ k·√x`, then `x ≤ k²`. -/
theorem sq_le_of_le_mul_sqrt_gl {x k : ℝ} (hx : 0 ≤ x) (hk : 0 ≤ k)
    (h : x ≤ k * Real.sqrt x) : x ≤ k ^ 2 := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0]; positivity
  · have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxeq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx).symm
    have h3 : Real.sqrt x ≤ k := by
      by_contra hcon
      push_neg at hcon
      have hlt : k * Real.sqrt x < Real.sqrt x * Real.sqrt x :=
        mul_lt_mul_of_pos_right hcon hsx
      linarith [h, hxeq, hlt]
    calc x = Real.sqrt x * Real.sqrt x := hxeq
      _ ≤ k * k := mul_le_mul h3 h3 (Real.sqrt_nonneg x) hk
      _ = k ^ 2 := (sq k).symm

/-- **The master weak-equation identity**, testing `gs.weak_eq` at `φ = meanZero(q_R)`. -/
theorem weak_eq_meanZero_qR_gl (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R)) :
    dirichlet (qR_gl gs) + α * bdR m R (meanZero (qR_gl gs)) (meanZero (qR_gl gs))
      = gs.nu * mass (meanZero (qR_gl gs))
        - gs.nu * linCoeff2_gl m R α *
          (∫ z in ball (0 : E) R, ‖z‖ ^ 2 * (meanZero (qR_gl gs)).toFun z)
        + (2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α) *
          bdR m R (oneB m R) (meanZero (qR_gl gs))
        - α * meanB (qR_gl gs) * bdR m R (oneB m R) (meanZero (qR_gl gs))
        + α * linCoeff2_gl m R α * bdR m R sqNormH1_gl (meanZero (qR_gl gs)) := by
  set mz := meanZero (qR_gl gs) with hmz
  have hweq0 := gs.weak_eq mz
  rw [qBilin_eq] at hweq0
  have hweq : dirichletBilin gs.psi mz + α * bdR m R gs.psi mz = gs.nu * NBilin gs.psi mz := hweq0
  -- Solve the three `qR_gl`-vs-`gs.psi` identities for the `gs.psi` quantities.
  have hd0 : dirichletBilin gs.psi mz
      = dirichletBilin (qR_gl gs) mz + dirichletBilin (linH1_gl (m := m) (R := R) α) mz := by
    have := dirichletBilin_qR_eq_gl gs mz
    linarith [this]
  have hb0 : bdR m R gs.psi mz = bdR m R (qR_gl gs) mz + bdR m R (linH1_gl α) mz := by
    have := bdR_qR_eq_gl gs mz
    linarith [this]
  have hn0 : NBilin gs.psi mz = NBilin (qR_gl gs) mz + NBilin (linH1_gl (m := m) (R := R) α) mz := by
    have := NBilin_qR_eq_gl gs mz
    linarith [this]
  rw [hd0, hb0, hn0] at hweq
  have hdself : dirichletBilin (qR_gl gs) mz = dirichlet (qR_gl gs) := by
    rw [hmz]; exact dirichletBilin_meanZero_self_gl (qR_gl gs)
  have hbself : bdR m R (qR_gl gs) mz
      = bdR m R mz mz + meanB (qR_gl gs) * bdR m R (oneB m R) mz := by
    rw [hmz]; exact bdR_meanZero_self_expand_gl (qR_gl gs)
  have hnself : NBilin (qR_gl gs) mz = mass mz := by
    rw [hmz]; exact NBilin_meanZero_self_gl hR (qR_gl gs)
  rw [hdself, hbself, hnself] at hweq
  have hint0 : (∫ x in ball (0 : E) R, mz.toFun x) = 0 := by
    rw [hmz]; exact integral_meanZero hR (qR_gl gs)
  have hNlin : NBilin (linH1_gl (m := m) (R := R) α) mz
      = -linCoeff2_gl m R α * (∫ z in ball (0 : E) R, ‖z‖ ^ 2 * mz.toFun z) := by
    rw [NBilin_linH1_gl, hint0, mul_zero, zero_sub, neg_mul]
  have hdlin : dirichletBilin (linH1_gl (m := m) (R := R) α) mz
      = -(2 * linCoeff2_gl m R α * R) * bdR m R (oneB m R) mz := by
    rw [dirichletBilin_linH1_gl, hmz, dirichletBilin_sqNormH1_meanZero_eq_gl hR (qR_gl gs), ← hmz]
    ring
  rw [hNlin, hdlin, bdR_linH1_gl] at hweq
  linarith [hweq]

/-! ## 11. Clean combination identities: `linCoeff_i · R^k · √V` simplify to `α`-polynomials -/

theorem sqrtV_eq_gl (hm : 1 ≤ m) (hR : 0 < R) :
    Real.sqrt (volume (ball (0 : E) R)).toReal = Real.sqrt (omega m) * R ^ ((m : ℝ) / 2) := by
  rw [volume_ball_toReal_eq (n := m) hR, Real.sqrt_mul (Cap.omega_pos m).le]
  congr 1
  rw [← sq_rpow_half m hR, Real.sqrt_sq (Real.rpow_nonneg hR.le _)]

theorem rpow_comb_e_gl (hR : 0 < R) :
    R ^ (-(m : ℝ) / 2 - 2) * R ^ 2 * R ^ ((m : ℝ) / 2) = 1 := by
  rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR, ← Real.rpow_add hR]
  have : -(m : ℝ) / 2 - 2 + (2 : ℕ) + (m : ℝ) / 2 = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

theorem rpow_comb_e3_gl (hR : 0 < R) :
    R ^ (-(m : ℝ) / 2 - 2) * R ^ 4 * R ^ ((m : ℝ) / 2) = R ^ 2 := by
  have h : R ^ (-(m : ℝ) / 2 - 2) * R ^ 4 * R ^ ((m : ℝ) / 2)
      = (R ^ (-(m : ℝ) / 2 - 2) * R ^ 2 * R ^ ((m : ℝ) / 2)) * R ^ 2 := by ring
  rw [h, rpow_comb_e_gl hR, one_mul]

theorem rpow_comb_e0_gl (hR : 0 < R) :
    R ^ (-(m : ℝ) / 2) * R ^ ((m : ℝ) / 2) = 1 := by
  rw [← Real.rpow_add hR]
  have : -(m : ℝ) / 2 + (m : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero]

theorem d_mul_sqrt_omega_gl (m : ℕ) : (Real.sqrt (omega m))⁻¹ * Real.sqrt (omega m) = 1 :=
  inv_mul_cancel₀ (Real.sqrt_pos.mpr (Cap.omega_pos m)).ne'

theorem linCoeff2_R2_sqrtV_eq_gl (hm : 1 ≤ m) (hR : 0 < R) :
    linCoeff2_gl m R α * R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal = α / 2 * R := by
  rw [sqrtV_eq_gl hm hR]
  unfold linCoeff2_gl
  have key : R ^ (-(m : ℝ) / 2 - 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2 * R ^ 2 *
      (Real.sqrt (omega m) * R ^ ((m : ℝ) / 2))
      = (R ^ (-(m : ℝ) / 2 - 2) * R ^ 2 * R ^ ((m : ℝ) / 2)) * (α * R) *
        ((Real.sqrt (omega m))⁻¹ * Real.sqrt (omega m)) / 2 := by ring
  rw [key, rpow_comb_e_gl hR, d_mul_sqrt_omega_gl m]
  ring

theorem linCoeff2_R3_sqrtV_eq_gl (hm : 1 ≤ m) (hR : 0 < R) :
    linCoeff2_gl m R α * R ^ 3 * Real.sqrt (volume (ball (0 : E) R)).toReal = α / 2 * R ^ 2 := by
  rw [sqrtV_eq_gl hm hR]
  unfold linCoeff2_gl
  have key : R ^ (-(m : ℝ) / 2 - 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2 * R ^ 3 *
      (Real.sqrt (omega m) * R ^ ((m : ℝ) / 2))
      = (R ^ (-(m : ℝ) / 2 - 2) * R ^ 4 * R ^ ((m : ℝ) / 2)) * α *
        ((Real.sqrt (omega m))⁻¹ * Real.sqrt (omega m)) / 2 := by ring
  rw [key, rpow_comb_e3_gl hR, d_mul_sqrt_omega_gl m]
  ring

theorem two_linCoeff2_R_sqrtV_eq_gl (hm : 1 ≤ m) (hR : 0 < R) :
    2 * linCoeff2_gl m R α * R * Real.sqrt (volume (ball (0 : E) R)).toReal = α := by
  rw [sqrtV_eq_gl hm hR]
  unfold linCoeff2_gl
  have key : 2 * (R ^ (-(m : ℝ) / 2 - 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2) * R *
      (Real.sqrt (omega m) * R ^ ((m : ℝ) / 2))
      = (R ^ (-(m : ℝ) / 2 - 2) * R ^ 2 * R ^ ((m : ℝ) / 2)) * α *
        ((Real.sqrt (omega m))⁻¹ * Real.sqrt (omega m)) := by ring
  rw [key, rpow_comb_e_gl hR, d_mul_sqrt_omega_gl m]
  ring

theorem linCoeff0_sqrtV_eq_gl (hm : 1 ≤ m) (hR : 0 < R) :
    linCoeff0_gl m R α * Real.sqrt (volume (ball (0 : E) R)).toReal
      = 1 + α * R * ((m : ℝ) / (2 * ((m : ℝ) + 2))) := by
  rw [sqrtV_eq_gl hm hR]
  unfold linCoeff0_gl
  have key : R ^ (-(m : ℝ) / 2) * (Real.sqrt (omega m))⁻¹ *
      (1 + α * R * ((m : ℝ) / (2 * ((m : ℝ) + 2)))) * (Real.sqrt (omega m) * R ^ ((m : ℝ) / 2))
      = (R ^ (-(m : ℝ) / 2) * R ^ ((m : ℝ) / 2)) *
        ((Real.sqrt (omega m))⁻¹ * Real.sqrt (omega m)) *
        (1 + α * R * ((m : ℝ) / (2 * ((m : ℝ) + 2)))) := by ring
  rw [key, rpow_comb_e0_gl hR, d_mul_sqrt_omega_gl m]
  ring

theorem linCoeff2_R_sqrtV_eq_gl (hm : 1 ≤ m) (hR : 0 < R) :
    linCoeff2_gl m R α * R * Real.sqrt (volume (ball (0 : E) R)).toReal = α / 2 := by
  rw [sqrtV_eq_gl hm hR]
  unfold linCoeff2_gl
  have key : R ^ (-(m : ℝ) / 2 - 2) * (α * R) * (Real.sqrt (omega m))⁻¹ / 2 * R *
      (Real.sqrt (omega m) * R ^ ((m : ℝ) / 2))
      = (R ^ (-(m : ℝ) / 2 - 2) * R ^ 2 * R ^ ((m : ℝ) / 2)) * α *
        ((Real.sqrt (omega m))⁻¹ * Real.sqrt (omega m)) / 2 := by ring
  rw [key, rpow_comb_e_gl hR, d_mul_sqrt_omega_gl m]
  ring

/-! ## 12. The `O(R²)` bound on `dirichlet(q_R)` -/

/-- **The explicit constant** bounding `dirichlet(q_R)` and (via `mass_qR_gl_le_gl`) `mass(q_R)`,
independent of `R` and of the ground state `gs`. -/
noncomputable def boundK_gl (m : ℕ) (α Cexp CP : ℝ) : ℝ :=
  2 * (((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) + (α ^ 2 * ((m : ℝ) / (2 * ((m : ℝ) + 2))))
    + (α * CP * Cexp ^ 2) + (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2))

set_option maxHeartbeats 1000000 in
/-- **The master `O(R²)` bound**: for `R` small enough (relative to `m, α, Cexp, CP`),
`dirichlet(q_R) ≤ K² R²` for the explicit `K = boundK_gl m α Cexp CP`. -/
theorem dirichlet_qR_gl_le_gl (hm : 1 ≤ m) (hα : 0 < α) (hR : 0 < R) (hR1 : R ≤ 1)
    {Cexp CP : ℝ} (hCP : 0 < CP)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ CP * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R)) (hexp : ExpW_tw m α R gs Cexp)
    (hsmall : CP * Cexp ^ 2 * R ^ 2 ≤ 1) (hRsmall : (m : ℝ) * α * CP * R ≤ 1 / 2) :
    dirichlet (qR_gl gs) ≤ (boundK_gl m α Cexp CP) ^ 2 * R ^ 2 := by
  set x : ℝ := dirichlet (qR_gl gs) with hx
  set mz : H1 (ball (0 : E) R) := meanZero (qR_gl gs) with hmz
  have hxnn : 0 ≤ x := dirichlet_nonneg _
  have hVpos : 0 < (volume (ball (0 : E) R)).toReal := volume_ball_toReal_pos (n := m) hR
  have hVnn : 0 ≤ (volume (ball (0 : E) R)).toReal := hVpos.le
  have hsqrtVnn : 0 ≤ Real.sqrt (volume (ball (0 : E) R)).toReal := Real.sqrt_nonneg _
  have hsqrtxnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  set A : ℝ := (m : ℝ) / (2 * ((m : ℝ) + 2)) with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  clear_value x mz A
  -- The master identity.
  have hmaster := weak_eq_meanZero_qR_gl hR gs
  rw [← hx, ← hmz] at hmaster
  have hbdmz : 0 ≤ bdR m R mz mz := gs.bdNonneg mz
  have hxle : x ≤ gs.nu * mass mz
      - gs.nu * linCoeff2_gl m R α * (∫ z in ball (0 : E) R, ‖z‖ ^ 2 * mz.toFun z)
      + (2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α) * bdR m R (oneB m R) mz
      - α * meanB (qR_gl gs) * bdR m R (oneB m R) mz
      + α * linCoeff2_gl m R α * bdR m R sqNormH1_gl mz := by
    nlinarith [hmaster, mul_nonneg hα.le hbdmz]
  -- Basic bounds.
  have hdmz : dirichlet mz = x := by rw [hmz, hx]; exact dirichlet_meanZero (qR_gl gs)
  have hmassmz : mass mz ≤ CP * R ^ 2 * x := by
    rw [hmz]
    have h := mass_meanZero_le_poincare hR hpw (qR_gl gs)
    rwa [hx]
  have hmassmznn : 0 ≤ mass mz := mass_nonneg mz
  have hnu_le : gs.nu ≤ (m : ℝ) * α / R := nu_bdR_le_xg hm hR gs
  have hnu_ge : 0 ≤ gs.nu := nu_nonneg_gl hα.le gs
  have hc2nn : 0 ≤ linCoeff2_gl m R α := by unfold linCoeff2_gl; positivity
  -- √(mass mz) ≤ √CP · R · √x
  have hsqrtmassmz : Real.sqrt (mass mz) ≤ Real.sqrt CP * R * Real.sqrt x := by
    have h2 : Real.sqrt (CP * R ^ 2 * x) = Real.sqrt CP * R * Real.sqrt x := by
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ CP * R ^ 2), Real.sqrt_mul hCP.le,
        Real.sqrt_sq hR.le]
    calc Real.sqrt (mass mz) ≤ Real.sqrt (CP * R ^ 2 * x) := Real.sqrt_le_sqrt hmassmz
      _ = Real.sqrt CP * R * Real.sqrt x := h2
  have hsqrtCPnn : 0 ≤ Real.sqrt CP := Real.sqrt_nonneg _
  -- bdR(oneB, mz)^2 ≤ V·x, hence |bdR(oneB,mz)| ≤ √V·√x
  have hbdoneBsq : bdR m R (oneB m R) mz ^ 2 ≤ (volume (ball (0 : E) R)).toReal * x := by
    have h := sq_bdR_oneB_meanZero_le_xg hR (qR_gl gs)
    rw [← hmz, ← hx] at h
    exact h
  have hbdoneB_abs : |bdR m R (oneB m R) mz|
      ≤ Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (bdR m R (oneB m R) mz ^ 2)
        ≤ Real.sqrt ((volume (ball (0 : E) R)).toReal * x) := Real.sqrt_le_sqrt hbdoneBsq
      _ = Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x := Real.sqrt_mul hVnn x
  -- bdR(sqNormH1_gl, mz) and ∫‖z‖²mz bounds
  have hbdsqNorm := abs_bdR_sqNormH1_le_gl hR mz
  rw [hdmz] at hbdsqNorm
  have hz2 := abs_integral_normSq_mul_le_gl hR mz
  have hmeanBV : meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal
      ≤ (CP * Cexp ^ 2 * R ^ 2) ^ 2 :=
    meanB_sq_mul_volume_qR_gl hm hR hCP hpw gs hexp hsmall
  have hmeanB_sqrtV : |meanB (qR_gl gs)| * Real.sqrt (volume (ball (0 : E) R)).toReal
      ≤ CP * Cexp ^ 2 * R ^ 2 := by
    have hpow : (|meanB (qR_gl gs)| * Real.sqrt (volume (ball (0 : E) R)).toReal) ^ 2
        = meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hVnn]
    have hnn1 : 0 ≤ |meanB (qR_gl gs)| * Real.sqrt (volume (ball (0 : E) R)).toReal := by positivity
    have hnn2 : 0 ≤ CP * Cexp ^ 2 * R ^ 2 := by positivity
    have hab : (|meanB (qR_gl gs)| * Real.sqrt (volume (ball (0 : E) R)).toReal) ^ 2
        ≤ (CP * Cexp ^ 2 * R ^ 2) ^ 2 := hpow ▸ hmeanBV
    calc |meanB (qR_gl gs)| * Real.sqrt (volume (ball (0 : E) R)).toReal
        = Real.sqrt ((|meanB (qR_gl gs)| * Real.sqrt (volume (ball (0 : E) R)).toReal) ^ 2) :=
          (Real.sqrt_sq hnn1).symm
      _ ≤ Real.sqrt ((CP * Cexp ^ 2 * R ^ 2) ^ 2) := Real.sqrt_le_sqrt hab
      _ = CP * Cexp ^ 2 * R ^ 2 := Real.sqrt_sq hnn2
  -- The clean combination identities.
  have hc2R2 := linCoeff2_R2_sqrtV_eq_gl (α := α) hm hR
  have hc2R3 := linCoeff2_R3_sqrtV_eq_gl (α := α) hm hR
  have hc2R1 := linCoeff2_R_sqrtV_eq_gl (α := α) hm hR
  have h2c2R := two_linCoeff2_R_sqrtV_eq_gl (α := α) hm hR
  have hc0 := linCoeff0_sqrtV_eq_gl (α := α) hm hR
  -- Term 1: ν·mass(mz) ≤ mαCP·R·x
  have hT1 : gs.nu * mass mz ≤ (m : ℝ) * α * CP * R * x := by
    have h1 : gs.nu * mass mz ≤ ((m : ℝ) * α / R) * mass mz :=
      mul_le_mul_of_nonneg_right hnu_le hmassmznn
    have h2 : ((m : ℝ) * α / R) * mass mz ≤ ((m : ℝ) * α / R) * (CP * R ^ 2 * x) :=
      mul_le_mul_of_nonneg_left hmassmz (by positivity)
    have h3 : ((m : ℝ) * α / R) * (CP * R ^ 2 * x) = (m : ℝ) * α * CP * R * x := by
      field_simp
    linarith [h1, h2, h3]
  -- Term 2
  have hT2 : -(gs.nu * linCoeff2_gl m R α *
        (∫ z in ball (0 : E) R, ‖z‖ ^ 2 * mz.toFun z))
      ≤ ((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) * R * Real.sqrt x := by
    have hνc2nn : 0 ≤ gs.nu * linCoeff2_gl m R α := mul_nonneg hnu_ge hc2nn
    have h1 : -(∫ z in ball (0 : E) R, ‖z‖ ^ 2 * mz.toFun z)
        ≤ |∫ z in ball (0 : E) R, ‖z‖ ^ 2 * mz.toFun z| := neg_le_abs _
    have h2 : gs.nu * linCoeff2_gl m R α * (-(∫ z in ball (0 : E) R, ‖z‖ ^ 2 * mz.toFun z))
        ≤ gs.nu * linCoeff2_gl m R α *
          (R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (mass mz)) :=
      mul_le_mul_of_nonneg_left (h1.trans hz2) hνc2nn
    have h3a : gs.nu * (linCoeff2_gl m R α * R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal)
        ≤ (m : ℝ) * α ^ 2 / 2 := by
      rw [hc2R2]
      have step : gs.nu * (α / 2 * R) ≤ ((m : ℝ) * α / R) * (α / 2 * R) :=
        mul_le_mul_of_nonneg_right hnu_le (by positivity)
      have eq1 : ((m : ℝ) * α / R) * (α / 2 * R) = (m : ℝ) * α ^ 2 / 2 := by
        field_simp
      linarith [step, eq1]
    have h3 : gs.nu * (linCoeff2_gl m R α * R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal)
        * Real.sqrt (mass mz) ≤ (m : ℝ) * α ^ 2 / 2 * Real.sqrt (mass mz) :=
      mul_le_mul_of_nonneg_right h3a (Real.sqrt_nonneg _)
    have h4 : (m : ℝ) * α ^ 2 / 2 * Real.sqrt (mass mz)
        ≤ (m : ℝ) * α ^ 2 / 2 * (Real.sqrt CP * R * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hsqrtmassmz (by positivity)
    have h5 : (m : ℝ) * α ^ 2 / 2 * (Real.sqrt CP * R * Real.sqrt x)
        = ((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) * R * Real.sqrt x := by ring
    have h6 : gs.nu * linCoeff2_gl m R α *
        (R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt (mass mz))
        = gs.nu * (linCoeff2_gl m R α * R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal)
          * Real.sqrt (mass mz) := by ring
    linarith [h2, h3, h4, h5, h6]
  -- Term 3
  have hT3 : (2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α) * bdR m R (oneB m R) mz
      ≤ (α ^ 2 * A) * R * Real.sqrt x := by
    have hcoeff : (2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α)
        * Real.sqrt (volume (ball (0 : E) R)).toReal = -(α ^ 2 * A * R) := by
      have e : (2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α)
          * Real.sqrt (volume (ball (0 : E) R)).toReal
          = 2 * linCoeff2_gl m R α * R * Real.sqrt (volume (ball (0 : E) R)).toReal
            - α * (linCoeff0_gl m R α * Real.sqrt (volume (ball (0 : E) R)).toReal) := by ring
      rw [e, h2c2R, hc0, hA]
      ring
    have hVpos' : 0 < Real.sqrt (volume (ball (0 : E) R)).toReal := by positivity
    have hstep : ((2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α)
          * bdR m R (oneB m R) mz) * Real.sqrt (volume (ball (0 : E) R)).toReal
        ≤ (α ^ 2 * A * R * Real.sqrt x) * Real.sqrt (volume (ball (0 : E) R)).toReal := by
      have e1 : ((2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α)
            * bdR m R (oneB m R) mz) * Real.sqrt (volume (ball (0 : E) R)).toReal
          = ((2 * linCoeff2_gl m R α * R - α * linCoeff0_gl m R α)
              * Real.sqrt (volume (ball (0 : E) R)).toReal) * bdR m R (oneB m R) mz := by ring
      rw [e1, hcoeff]
      have hb2 : -bdR m R (oneB m R) mz ≤ |bdR m R (oneB m R) mz| := neg_le_abs _
      have hb3 : -(α ^ 2 * A * R) * bdR m R (oneB m R) mz
          = (α ^ 2 * A * R) * (-bdR m R (oneB m R) mz) := by ring
      rw [hb3]
      calc (α ^ 2 * A * R) * (-bdR m R (oneB m R) mz)
          ≤ (α ^ 2 * A * R) * |bdR m R (oneB m R) mz| :=
            mul_le_mul_of_nonneg_left hb2 (by positivity)
        _ ≤ (α ^ 2 * A * R) * (Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hbdoneB_abs (by positivity)
        _ = (α ^ 2 * A * R * Real.sqrt x) * Real.sqrt (volume (ball (0 : E) R)).toReal := by ring
    exact le_of_mul_le_mul_right hstep hVpos'
  -- Term 4
  have hT4 : -(α * meanB (qR_gl gs) * bdR m R (oneB m R) mz)
      ≤ α * CP * Cexp ^ 2 * R * Real.sqrt x := by
    have h1 : -(α * meanB (qR_gl gs) * bdR m R (oneB m R) mz)
        ≤ α * (|meanB (qR_gl gs)| * |bdR m R (oneB m R) mz|) := by
      have e : -(α * meanB (qR_gl gs) * bdR m R (oneB m R) mz)
          = α * (-(meanB (qR_gl gs) * bdR m R (oneB m R) mz)) := by ring
      rw [e]
      have h2 : -(meanB (qR_gl gs) * bdR m R (oneB m R) mz)
          ≤ |meanB (qR_gl gs) * bdR m R (oneB m R) mz| := neg_le_abs _
      have h3 : |meanB (qR_gl gs) * bdR m R (oneB m R) mz|
          = |meanB (qR_gl gs)| * |bdR m R (oneB m R) mz| := abs_mul _ _
      calc α * (-(meanB (qR_gl gs) * bdR m R (oneB m R) mz))
          ≤ α * |meanB (qR_gl gs) * bdR m R (oneB m R) mz| :=
            mul_le_mul_of_nonneg_left h2 hα.le
        _ = α * (|meanB (qR_gl gs)| * |bdR m R (oneB m R) mz|) := by rw [h3]
    have h5 : |meanB (qR_gl gs)| * |bdR m R (oneB m R) mz|
        ≤ (CP * Cexp ^ 2 * R ^ 2) * Real.sqrt x := by
      calc |meanB (qR_gl gs)| * |bdR m R (oneB m R) mz|
          ≤ |meanB (qR_gl gs)| *
            (Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hbdoneB_abs (abs_nonneg _)
        _ = (|meanB (qR_gl gs)| * Real.sqrt (volume (ball (0 : E) R)).toReal)
              * Real.sqrt x := by ring
        _ ≤ (CP * Cexp ^ 2 * R ^ 2) * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hmeanB_sqrtV (Real.sqrt_nonneg _)
    have h4 : α * (|meanB (qR_gl gs)| * |bdR m R (oneB m R) mz|)
        ≤ α * ((CP * Cexp ^ 2 * R ^ 2) * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left h5 hα.le
    have hR2R : R ^ 2 ≤ R := by nlinarith [hR.le, hR1]
    have h6 : α * ((CP * Cexp ^ 2 * R ^ 2) * Real.sqrt x)
        ≤ α * CP * Cexp ^ 2 * R * Real.sqrt x := by
      have h7 : α * (CP * Cexp ^ 2 * R ^ 2) ≤ α * (CP * Cexp ^ 2 * R) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR2R (by positivity)) hα.le
      have h8 : α * (CP * Cexp ^ 2 * R ^ 2) * Real.sqrt x ≤ α * (CP * Cexp ^ 2 * R) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right h7 (Real.sqrt_nonneg _)
      nlinarith [h8]
    linarith [h1, h4, h6]
  -- Term 5
  have hT5 : α * linCoeff2_gl m R α * bdR m R sqNormH1_gl mz
      ≤ (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2) * R * Real.sqrt x := by
    have hαc2nn : 0 ≤ α * linCoeff2_gl m R α := mul_nonneg hα.le hc2nn
    have h1 : α * linCoeff2_gl m R α * bdR m R sqNormH1_gl mz
        ≤ α * linCoeff2_gl m R α * |bdR m R sqNormH1_gl mz| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hαc2nn
    have h2 : α * linCoeff2_gl m R α * |bdR m R sqNormH1_gl mz|
        ≤ α * linCoeff2_gl m R α *
          (R⁻¹ * (((m : ℝ) + 2) * (R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal
              * Real.sqrt (mass mz))
            + R ^ 3 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left hbdsqNorm hαc2nn
    have hRinv : (0:ℝ) < R⁻¹ := by positivity
    have hRne : R ≠ 0 := hR.ne'
    have e1 : R⁻¹ * R ^ 2 = R := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hRne, one_mul]
    have e2 : R⁻¹ * R ^ 3 = R ^ 2 := by
      rw [show R ^ 3 = R ^ 2 * R from by ring, mul_comm (R^2) R, ← mul_assoc,
        inv_mul_cancel₀ hRne, one_mul]
    have h3 : α * linCoeff2_gl m R α *
        (R⁻¹ * (((m : ℝ) + 2) * (R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal
            * Real.sqrt (mass mz))
          + R ^ 3 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x))
        = ((m : ℝ) + 2) * (α * (linCoeff2_gl m R α * R * Real.sqrt (volume (ball (0 : E) R)).toReal))
            * Real.sqrt (mass mz)
          + (α * (linCoeff2_gl m R α * R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal))
            * Real.sqrt x := by
      have expand : R⁻¹ * (((m : ℝ) + 2) * (R ^ 2 * Real.sqrt (volume (ball (0 : E) R)).toReal
            * Real.sqrt (mass mz))
          + R ^ 3 * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x)
          = ((m : ℝ) + 2) * ((R⁻¹ * R ^ 2) * Real.sqrt (volume (ball (0 : E) R)).toReal
              * Real.sqrt (mass mz))
            + (R⁻¹ * R ^ 3) * Real.sqrt (volume (ball (0 : E) R)).toReal * Real.sqrt x := by
        ring
      rw [expand, e1, e2]
      ring
    rw [h3, hc2R1, hc2R2] at h2
    have h4 : ((m : ℝ) + 2) * (α * (α / 2)) * Real.sqrt (mass mz)
        ≤ ((m : ℝ) + 2) * (α * (α / 2)) * (Real.sqrt CP * R * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hsqrtmassmz (by positivity)
    have h5 : ((m : ℝ) + 2) * (α * (α / 2)) * (Real.sqrt CP * R * Real.sqrt x)
          + α * (α / 2 * R) * Real.sqrt x
        = (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2) * R * Real.sqrt x := by
      ring
    linarith [h1, h2, h4, h5]
  -- Final combination
  have hxle2 : x ≤ (m : ℝ) * α * CP * R * x
      + (((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) * R * Real.sqrt x)
      + (α ^ 2 * A) * R * Real.sqrt x + (α * CP * Cexp ^ 2) * R * Real.sqrt x
      + (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2) * R * Real.sqrt x := by
    linarith [hxle, hT1, hT2, hT3, hT4, hT5]
  have hexpand : (((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) * R * Real.sqrt x)
      + (α ^ 2 * A) * R * Real.sqrt x + (α * CP * Cexp ^ 2) * R * Real.sqrt x
      + (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2) * R * Real.sqrt x
      = (((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) + (α ^ 2 * A) + (α * CP * Cexp ^ 2)
          + (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2)) * R * Real.sqrt x := by
    ring
  have hcombine : x * (1 - (m : ℝ) * α * CP * R)
      ≤ (((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) + (α ^ 2 * A) + (α * CP * Cexp ^ 2)
          + (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2)) * R * Real.sqrt x := by
    have e : x * (1 - (m : ℝ) * α * CP * R) = x - (m : ℝ) * α * CP * R * x := by ring
    rw [e]
    linarith [hxle2, hexpand]
  set B : ℝ := ((m : ℝ) * α ^ 2 * Real.sqrt CP / 2) + (α ^ 2 * A) + (α * CP * Cexp ^ 2)
      + (((m : ℝ) + 2) * (α ^ 2 * Real.sqrt CP / 2) + α ^ 2 / 2) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have h1mCPR : (1:ℝ) / 2 ≤ 1 - (m : ℝ) * α * CP * R := by linarith [hRsmall]
  have hxhalf : x / 2 ≤ B * R * Real.sqrt x := by
    have hstep : x * (1 / 2) ≤ x * (1 - (m : ℝ) * α * CP * R) :=
      mul_le_mul_of_nonneg_left h1mCPR hxnn
    linarith [hstep, hcombine]
  have hxfinal : x ≤ (2 * B * R) * Real.sqrt x := by
    have e : (2 * B * R) * Real.sqrt x = 2 * (B * R * Real.sqrt x) := by ring
    rw [e]
    linarith [hxhalf]
  have hK : 0 ≤ 2 * B * R := by positivity
  have hfin := sq_le_of_le_mul_sqrt_gl hxnn hK hxfinal
  have hBeq : boundK_gl m α Cexp CP = 2 * B := by unfold boundK_gl; rw [hBdef, hA]
  calc x ≤ (2 * B * R) ^ 2 := hfin
    _ = (2 * B) ^ 2 * R ^ 2 := by ring
    _ = (boundK_gl m α Cexp CP) ^ 2 * R ^ 2 := by rw [hBeq]

/-! ## 13. The `O(R⁴)` bound on `mass(q_R)`, and the pointwise gradient identity -/

theorem mass_qR_gl_le_gl (hm : 1 ≤ m) (hα : 0 < α) (hR : 0 < R) (hR1 : R ≤ 1) {Cexp CP : ℝ}
    (hCP : 0 < CP)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ CP * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R)) (hexp : ExpW_tw m α R gs Cexp)
    (hsmall : CP * Cexp ^ 2 * R ^ 2 ≤ 1) (hRsmall : (m : ℝ) * α * CP * R ≤ 1 / 2) :
    mass (qR_gl gs) ≤ (CP * (boundK_gl m α Cexp CP) ^ 2 + CP ^ 2 * Cexp ^ 4) * R ^ 4 := by
  have hK1 := dirichlet_qR_gl_le_gl hm hα hR hR1 hCP hpw gs hexp hsmall hRsmall
  have hmzle := mass_meanZero_le_poincare hR hpw (qR_gl gs)
  have hmeanBV := meanB_sq_mul_volume_qR_gl hm hR hCP hpw gs hexp hsmall
  have hsplit := mass_eq_mass_meanZero_add hR (qR_gl gs)
  have h1 : mass (meanZero (qR_gl gs)) ≤ CP * ((boundK_gl m α Cexp CP) ^ 2 * R ^ 4) := by
    calc mass (meanZero (qR_gl gs)) ≤ CP * R ^ 2 * dirichlet (qR_gl gs) := hmzle
      _ ≤ CP * R ^ 2 * ((boundK_gl m α Cexp CP) ^ 2 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hK1 (by positivity)
      _ = CP * ((boundK_gl m α Cexp CP) ^ 2 * R ^ 4) := by ring
  have h2 : meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal ≤ CP ^ 2 * Cexp ^ 4 * R ^ 4 := by
    calc meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal
        ≤ (CP * Cexp ^ 2 * R ^ 2) ^ 2 := hmeanBV
      _ = CP ^ 2 * Cexp ^ 4 * R ^ 4 := by ring
  calc mass (qR_gl gs) = mass (meanZero (qR_gl gs))
        + meanB (qR_gl gs) ^ 2 * (volume (ball (0 : E) R)).toReal := hsplit
    _ ≤ CP * ((boundK_gl m α Cexp CP) ^ 2 * R ^ 4) + CP ^ 2 * Cexp ^ 4 * R ^ 4 := add_le_add h1 h2
    _ = (CP * (boundK_gl m α Cexp CP) ^ 2 + CP ^ 2 * Cexp ^ 4) * R ^ 4 := by ring

/-- **The pointwise gradient design identity**: `Ψ_R'(y) − αR·∇v(y) = R^{m/2}R · q_R'(Ry)`. -/
theorem grad_design_eq_gl (hR : 0 < R) (α : ℝ) (gs : TransverseGroundState m α R (bdR m R))
    (y : EuclideanSpace ℝ (Fin m)) :
    transLiftGrad_tw m R gs.psi y - (α * R) • gradVquad_gl m y
      = (R ^ ((m : ℝ) / 2) * R) • (qR_gl gs).grad (R • y) := by
  have hg : (qR_gl gs).grad (R • y)
      = gs.psi.grad (R • y) - (linH1_gl (m := m) (R := R) α).grad (R • y) := by
    rw [qR_grad_gl]
  rw [hg]
  have hlin : (R ^ ((m : ℝ) / 2) * R) • (linH1_gl (m := m) (R := R) α).grad (R • y)
      = (α * R) • gradVquad_gl m y := by
    simp only [linH1_grad_gl]
    unfold gradVquad_gl
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    unfold linCoeff2_gl
    have e2 : R ^ ((m : ℝ) / 2) * R ^ (-(m : ℝ) / 2 - 2) = R ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hR]
      congr 1
      ring
    have e3 : R ^ (-2 : ℝ) * R ^ (3 : ℕ) = R := by
      rw [← Real.rpow_natCast R 3, ← Real.rpow_add hR]
      norm_num
    have e4 : R ^ ((m : ℝ) / 2) * R ^ (-(m : ℝ) / 2 - 2) * R * R * R = R := by
      rw [e2]
      calc R ^ (-2 : ℝ) * R * R * R = R ^ (-2 : ℝ) * R ^ (3 : ℕ) := by ring
        _ = R := e3
    linear_combination (-(α * (Real.sqrt (omega m))⁻¹)) * e4
  have hsub : (R ^ ((m : ℝ) / 2) * R) •
      (gs.psi.grad (R • y) - (linH1_gl (m := m) (R := R) α).grad (R • y))
      = (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • y)
        - (R ^ ((m : ℝ) / 2) * R) • (linH1_gl (m := m) (R := R) α).grad (R • y) :=
    smul_sub _ _ _
  rw [hsub, hlin]
  unfold transLiftGrad_tw
  rfl

/-! ## 14. The two `B_m(1)` change-of-variables identities -/

/-- **(I)**: `∫_{B_1} (Ψ_R − d − αR v)² = mass(q_R)`. -/
theorem integral_toFun_sq_eq_mass_gl (hR : 0 < R) (α : ℝ)
    (gs : TransverseGroundState m α R (bdR m R)) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y) ^ 2)
      = mass (qR_gl gs) := by
  have hpt : ∀ y : EuclideanSpace ℝ (Fin m),
      (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y) ^ 2
        = R ^ m * ((qR_gl gs).toFun (R • y)) ^ 2 := by
    intro y
    rw [F_eq_qR_gl_smul_gl hR α gs y, mul_pow, sq_rpow_half m hR]
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR
    (fun z => ((qR_gl gs).toFun z) ^ 2)
  rw [mul_one] at h
  calc (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y) ^ 2)
      = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, R ^ m * ((qR_gl gs).toFun (R • y)) ^ 2 :=
        setIntegral_congr_fun measurableSet_ball (fun y _ => hpt y)
    _ = R ^ m * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ((qR_gl gs).toFun (R • y)) ^ 2 :=
        integral_const_mul _ _
    _ = ∫ z in ball (0 : E) R, ((qR_gl gs).toFun z) ^ 2 := h.symm
    _ = mass (qR_gl gs) := rfl

/-- **(II)**: `∫_{B_1} ‖Ψ_R' − αR·∇v‖² = R²·dirichlet(q_R)`. -/
theorem integral_grad_sq_eq_dirichlet_gl (hR : 0 < R) (α : ℝ)
    (gs : TransverseGroundState m α R (bdR m R)) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ‖transLiftGrad_tw m R gs.psi y - (α * R) • gradVquad_gl m y‖ ^ 2)
      = R ^ 2 * dirichlet (qR_gl gs) := by
  have hpt : ∀ y : EuclideanSpace ℝ (Fin m),
      ‖transLiftGrad_tw m R gs.psi y - (α * R) • gradVquad_gl m y‖ ^ 2
        = R ^ 2 * (R ^ m * ‖(qR_gl gs).grad (R • y)‖ ^ 2) := by
    intro y
    rw [grad_design_eq_gl hR α gs y, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow,
      sq_rpow_half m hR]
    ring
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR
    (fun z => ‖(qR_gl gs).grad z‖ ^ 2)
  rw [mul_one] at h
  calc (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ‖transLiftGrad_tw m R gs.psi y - (α * R) • gradVquad_gl m y‖ ^ 2)
      = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          R ^ 2 * (R ^ m * ‖(qR_gl gs).grad (R • y)‖ ^ 2) :=
        setIntegral_congr_fun measurableSet_ball (fun y _ => hpt y)
    _ = R ^ 2 * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          R ^ m * ‖(qR_gl gs).grad (R • y)‖ ^ 2 := integral_const_mul _ _
    _ = R ^ 2 * ∫ z in ball (0 : E) R, ‖(qR_gl gs).grad z‖ ^ 2 := by
        congr 1
        rw [integral_const_mul, ← h]
    _ = R ^ 2 * dirichlet (qR_gl gs) := rfl

end GS

/-! ## 15. Deliverable A: the second-order transverse expansion -/

/-- **`rem:gradient-leading`, second-order expansion.** For `R` small enough (depending on
`m, α, Cexp`), `Ψ_R − d − αR·v` is `O(R²)` in `H¹(B_m(1))`. -/
theorem second_order_expansion_gl (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (Cexp : ℝ) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 < R₀ ∧ ∀ R (hR : 0 < R), R < R₀ →
      ∀ gs : TransverseGroundState m α R (bdR m R), ExpW_tw m α R gs Cexp →
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y) ^ 2)
          + (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
              ‖transLiftGrad_tw m R gs.psi y - (α * R) • gradVquad_gl m y‖ ^ 2)
          ≤ C * R ^ 4 := by
  obtain ⟨CP, hCPpos, hpw0⟩ := poincare_wirtinger_ball (rellichSeq' m one_pos)
  set K : ℝ := boundK_gl m α Cexp CP with hKdef
  set R₀ : ℝ := min 1 (min (1 / Real.sqrt (CP * Cexp ^ 2 + 1)) (1 / (2 * (m : ℝ) * α * CP + 1)))
    with hR₀def
  refine ⟨K ^ 2 + (CP * K ^ 2 + CP ^ 2 * Cexp ^ 4), R₀, by positivity, ?_, ?_⟩
  · rw [hR₀def]
    apply lt_min one_pos
    apply lt_min <;> positivity
  · intro R hR hRR0 gs hexp
    have hR1 : R ≤ 1 := (hRR0.trans_le (min_le_left _ _)).le
    have hRsq : R < 1 / Real.sqrt (CP * Cexp ^ 2 + 1) :=
      hRR0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hRlin : R < 1 / (2 * (m : ℝ) * α * CP + 1) :=
      hRR0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hsmall : CP * Cexp ^ 2 * R ^ 2 ≤ 1 := by
      have h1 : R * Real.sqrt (CP * Cexp ^ 2 + 1) < 1 := by
        rw [← lt_div_iff₀ (by positivity : (0:ℝ) < Real.sqrt (CP * Cexp ^ 2 + 1))]
        exact hRsq
      have h1' : 0 ≤ R * Real.sqrt (CP * Cexp ^ 2 + 1) := by positivity
      have h2 : (R * Real.sqrt (CP * Cexp ^ 2 + 1)) ^ 2 < 1 := by nlinarith [h1, h1']
      have h3 : R ^ 2 * (CP * Cexp ^ 2 + 1) < 1 := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ CP * Cexp ^ 2 + 1)] at h2
        exact h2
      nlinarith [h3, sq_nonneg R]
    have hRsmall : (m : ℝ) * α * CP * R ≤ 1 / 2 := by
      have h1 : R * (2 * (m : ℝ) * α * CP + 1) < 1 := by
        rw [← lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (m : ℝ) * α * CP + 1)]
        exact hRlin
      nlinarith [h1, hR.le]
    have hpw := hpw0 R hR
    have hd := dirichlet_qR_gl_le_gl hm hα hR hR1 hCPpos hpw gs hexp hsmall hRsmall
    have hmassb := mass_qR_gl_le_gl hm hα hR hR1 hCPpos hpw gs hexp hsmall hRsmall
    calc (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y) ^ 2)
          + (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
              ‖transLiftGrad_tw m R gs.psi y - (α * R) • gradVquad_gl m y‖ ^ 2)
        = mass (qR_gl gs) + R ^ 2 * dirichlet (qR_gl gs) := by
          rw [integral_toFun_sq_eq_mass_gl hR α gs, integral_grad_sq_eq_dirichlet_gl hR α gs]
      _ ≤ (CP * K ^ 2 + CP ^ 2 * Cexp ^ 4) * R ^ 4 + R ^ 2 * (K ^ 2 * R ^ 2) := by
          have hstep : R ^ 2 * dirichlet (qR_gl gs) ≤ R ^ 2 * (K ^ 2 * R ^ 2) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
          linarith [hmassb, hstep]
      _ = (K ^ 2 + (CP * K ^ 2 + CP ^ 2 * Cexp ^ 4)) * R ^ 4 := by ring

/-! ## 16. Deliverable B: `eq:gradient-leading` on the unit hemispherical cap -/

set_option maxHeartbeats 1000000 in
/-- **`eq:gradient-leading`.** The leading order of the transverse gradient energy on the unit
hemispherical cap. Note the normalisation: `∫_{C.body} ‖gz‖² = R · ∫_{C_R} |∇_yψ_R|²` in the
manuscript's own variables, so this differs from the manuscript's stated rate by a factor of
`R` (the manuscript states `R⁻¹∫_{C_R}|∇_yψ_R|² = (α²/ω_m)∫_C|z|² + O(R)`, i.e. an `O(R)` error
after the same rescaling — here the error is `O(R³)` because both sides already carry an extra
factor of `R²` from `∫‖gz‖²` versus `R⁻¹∫|∇_yψ_R|²`). -/
theorem gradient_leading_gl (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (Cexp : ℝ) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 < R₀ ∧ ∀ R (hR : 0 < R), R < R₀ →
      ∀ gs : TransverseGroundState m α R (bdR m R), ExpW_tw m α R gs Cexp →
        |(∫ p in (Cap.hemisphere m).body, ‖(capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz p‖ ^ 2)
            - α ^ 2 * R ^ 2 / omega m * (∫ p in (Cap.hemisphere m).body, ‖p.2‖ ^ 2)|
          ≤ C * R ^ 3 := by
  obtain ⟨Ca, R₀, hCanp, hR₀pos, hmain⟩ := second_order_expansion_gl m hm α hα Cexp
  refine ⟨2 * α * Real.sqrt Ca + Ca, min R₀ 1, by positivity, lt_min hR₀pos one_pos, ?_⟩
  intro R hR hRR0 gs hexp
  have hR1 : R ≤ 1 := (hRR0.trans_le (min_le_right _ _)).le
  have hbound := hmain R hR (hRR0.trans_le (min_le_left _ _)) gs hexp
  set d : ℝ := (Real.sqrt (omega m))⁻¹ with hddef
  set E : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => transLiftGrad_tw m R gs.psi y - (α * R) • gradVquad_gl m y with hEdef
  have hE2nn : (0:ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _
  have hE2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2) ≤ Ca * R ^ 4 := by
    have h0 : (0:ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - (Real.sqrt (omega m))⁻¹ - α * R * vquad_gl m y) ^ 2 :=
      setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _
    linarith [hbound, h0]
  -- The pointwise identity `‖Ψ'(y)‖² − (α²R²/ω_m)‖y‖² = −2αRd·⟪E(y),y⟫ + ‖E(y)‖²`.
  have hpt : ∀ y : EuclideanSpace ℝ (Fin m),
      ‖transLiftGrad_tw m R gs.psi y‖ ^ 2 - α ^ 2 * R ^ 2 / omega m * ‖y‖ ^ 2
        = -(2 * α * R * d) * ⟪E y, y⟫_ℝ + ‖E y‖ ^ 2 := by
    intro y
    have hΨ : transLiftGrad_tw m R gs.psi y = E y - (α * R * d) • y := by
      have hgv : (α * R) • gradVquad_gl m y = -(α * R * d) • y := by
        unfold gradVquad_gl; rw [← hddef]; module
      rw [hEdef]; simp only; rw [hgv]; module
    rw [hΨ, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    have hd2 : (α * R * d) ^ 2 = α ^ 2 * R ^ 2 / omega m := by
      rw [hddef]
      have hω0 : (0:ℝ) < omega m := Cap.omega_pos m
      rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hω0.le]
      field_simp
    have habs : |α * R * d| ^ 2 = (α * R * d) ^ 2 := sq_abs _
    nlinarith [hd2, habs]
  -- `Dl(y) := ‖Ψ'(y)‖² − (α²R²/ω_m)‖y‖²`, a function on `B_1` alone.
  set Dl : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun y => ‖transLiftGrad_tw m R gs.psi y‖ ^ 2 - α ^ 2 * R ^ 2 / omega m * ‖y‖ ^ 2 with hDldef
  have hDlmemLp1 : IntegrableOn Dl (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    have h1 : IntegrableOn (fun y : EuclideanSpace ℝ (Fin m) => ‖transLiftGrad_tw m R gs.psi y‖ ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := (memLp_transLiftGrad_tw hR gs.psi).norm.integrable_sq
    have h2 : IntegrableOn (fun y : EuclideanSpace ℝ (Fin m) => α ^ 2 * R ^ 2 / omega m * ‖y‖ ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      (integrableOn_ball_one_of_continuous (m := m) (by fun_prop)).const_mul _
    exact h1.sub h2
  -- The bound `∫_{B_1} |Dl| ≤ 2α√Ca R³ + Ca R⁴`.
  have hDlbound : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |Dl y|)
      ≤ 2 * α * Real.sqrt Ca * R ^ 3 + Ca * R ^ 4 := by
    have hle : ∀ y : EuclideanSpace ℝ (Fin m), |Dl y| ≤ 2 * α * R * d * (‖E y‖ * ‖y‖) + ‖E y‖ ^ 2 := by
      intro y
      have heq : Dl y = -(2 * α * R * d) * ⟪E y, y⟫_ℝ + ‖E y‖ ^ 2 := hpt y
      have h1 : |Dl y| ≤ |(2 * α * R * d) * ⟪E y, y⟫_ℝ| + ‖E y‖ ^ 2 := by
        rw [heq, neg_mul]
        calc |-((2 * α * R * d) * ⟪E y, y⟫_ℝ) + ‖E y‖ ^ 2|
            ≤ |(2 * α * R * d) * ⟪E y, y⟫_ℝ| + |‖E y‖ ^ 2| := (abs_add_le _ _).trans_eq (by rw [abs_neg])
          _ = |(2 * α * R * d) * ⟪E y, y⟫_ℝ| + ‖E y‖ ^ 2 := by rw [abs_of_nonneg (sq_nonneg (‖E y‖))]
      have h2 : |(2 * α * R * d) * ⟪E y, y⟫_ℝ| ≤ 2 * α * R * d * (‖E y‖ * ‖y‖) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * α * R * d)]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      linarith [h1, h2]
    have hgvcont : Continuous (fun y : EuclideanSpace ℝ (Fin m) => (α * R) • gradVquad_gl m y) :=
      (continuous_gradVquad_gl m).const_smul (α * R)
    have hE : MemLp E 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
      rw [hEdef]
      exact (memLp_transLiftGrad_tw hR gs.psi).sub (memLp_two_of_continuous hgvcont)
    have hIntE2 : IntegrableOn (fun y : EuclideanSpace ℝ (Fin m) => ‖E y‖ ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := hE.norm.integrable_sq
    have hIntEy : IntegrableOn (fun y : EuclideanSpace ℝ (Fin m) => ‖E y‖ * ‖y‖)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := by
      have h2 : MemLp (fun y : EuclideanSpace ℝ (Fin m) => y) 2
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
        memLp_two_of_continuous (by fun_prop)
      exact hE.norm.integrable_mul h2.norm
    have h1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |Dl y|)
        ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          (2 * α * R * d * (‖E y‖ * ‖y‖) + ‖E y‖ ^ 2) :=
      integral_mono_ae hDlmemLp1.abs
        ((hIntEy.const_mul _).add hIntE2) (Filter.Eventually.of_forall hle)
    have h2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (2 * α * R * d * (‖E y‖ * ‖y‖) + ‖E y‖ ^ 2))
        = 2 * α * R * d * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ * ‖y‖)
          + ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2 := by
      rw [integral_add (hIntEy.const_mul _) hIntE2, integral_const_mul]
    have hCS : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ * ‖y‖)
        ≤ Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2)
          * Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2) := by
      have hid : MemLp (fun y : EuclideanSpace ℝ (Fin m) => y) 2
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
        memLp_two_of_continuous (by fun_prop)
      have hcs := integral_norm_mul_norm_le hE hid
      simpa using hcs
    have hy2le : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2) ≤ omega m := by
      rw [integral_normSq_ball_one_gl m hm, div_le_iff₀ (by positivity : (0:ℝ) < (m : ℝ) + 2)]
      nlinarith [Cap.omega_pos m]
    have hy2nn : (0:ℝ) ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2 :=
      setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _
    have hddef' : d = (Real.sqrt (omega m))⁻¹ := hddef
    have hωpos : (0:ℝ) < omega m := Cap.omega_pos m
    have hfinal : 2 * α * R * d * (Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2)
        * Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2))
        ≤ 2 * α * Real.sqrt Ca * R ^ 3 := by
      rw [hddef']
      have hsqrtE : Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2)
          ≤ Real.sqrt (Ca * R ^ 4) := Real.sqrt_le_sqrt hE2
      have hsqrtE2 : Real.sqrt (Ca * R ^ 4) = Real.sqrt Ca * R ^ 2 := by
        rw [show Ca * R ^ 4 = Ca * (R ^ 2) ^ 2 from by ring, Real.sqrt_mul (by nlinarith [hE2, hE2nn]),
          Real.sqrt_sq (by positivity)]
      have hsqrty : Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2)
          ≤ Real.sqrt (omega m) := Real.sqrt_le_sqrt hy2le
      have hR2 : 2 * α * R * (Real.sqrt (omega m))⁻¹ * (Real.sqrt (Ca * R ^ 4) * Real.sqrt (omega m))
          = 2 * α * Real.sqrt Ca * R ^ 3 := by
        rw [hsqrtE2]
        have hω0 : Real.sqrt (omega m) ≠ 0 := (Real.sqrt_pos.mpr hωpos).ne'
        field_simp
      calc 2 * α * R * (Real.sqrt (omega m))⁻¹ *
          (Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2)
            * Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2))
          ≤ 2 * α * R * (Real.sqrt (omega m))⁻¹ * (Real.sqrt (Ca * R ^ 4) * Real.sqrt (omega m)) := by
            gcongr
          _ = 2 * α * Real.sqrt Ca * R ^ 3 := hR2
    calc (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |Dl y|)
        ≤ 2 * α * R * d * (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ * ‖y‖)
          + ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2 := by rw [← h2]; exact h1
      _ ≤ 2 * α * R * d * (Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖E y‖ ^ 2)
            * Real.sqrt (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖y‖ ^ 2))
          + Ca * R ^ 4 := by
          have := mul_le_mul_of_nonneg_left hCS (by positivity : (0:ℝ) ≤ 2 * α * R * d)
          linarith [this, hE2]
      _ ≤ 2 * α * Real.sqrt Ca * R ^ 3 + Ca * R ^ 4 := by linarith [hfinal]
  -- Assemble via `abs_setIntegral_body_le_tw`.
  have hcap := abs_setIntegral_body_le_tw (Cap.hemisphere m) hDlmemLp1
  have hKeq : (Cap.hemisphere m).K = 1 := rfl
  rw [hKeq, one_mul] at hcap
  have hI1 : IntegrableOn (fun p : CapSpace m =>
      ‖(capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz p‖ ^ 2) (Cap.hemisphere m).body :=
    (capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz_memL2.norm.integrable_sq
  have hI2 : IntegrableOn (fun p : CapSpace m => α ^ 2 * R ^ 2 / omega m * ‖p.2‖ ^ 2)
      (Cap.hemisphere m).body :=
    Cap.integrableOn_body_of_continuous (Cap.hemisphere m) (by fun_prop)
  have heqbody : (∫ p in (Cap.hemisphere m).body, Dl p.2)
      = (∫ p in (Cap.hemisphere m).body,
          ‖(capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz p‖ ^ 2)
        - α ^ 2 * R ^ 2 / omega m * (∫ p in (Cap.hemisphere m).body, ‖p.2‖ ^ 2) := by
    have hfe : (fun p : CapSpace m => Dl p.2)
        = (fun p : CapSpace m => ‖(capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz p‖ ^ 2
            - α ^ 2 * R ^ 2 / omega m * ‖p.2‖ ^ 2) := by
      funext p
      rw [hDldef, capLiftW_tw_gz]
    rw [hfe, integral_sub hI1 hI2, integral_const_mul]
  rw [heqbody] at hcap
  have hR34 : Ca * R ^ 4 ≤ Ca * R ^ 3 := by nlinarith [hR1, hR.le, hCanp]
  calc |(∫ p in (Cap.hemisphere m).body, ‖(capLiftW_tw (Cap.hemisphere m) hR gs.psi).gz p‖ ^ 2)
      - α ^ 2 * R ^ 2 / omega m * (∫ p in (Cap.hemisphere m).body, ‖p.2‖ ^ 2)|
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, |Dl y| := hcap
    _ ≤ 2 * α * Real.sqrt Ca * R ^ 3 + Ca * R ^ 4 := hDlbound
    _ ≤ 2 * α * Real.sqrt Ca * R ^ 3 + Ca * R ^ 3 := by linarith [hR34]
    _ = (2 * α * Real.sqrt Ca + Ca) * R ^ 3 := by ring

/-! ## 17. `positive_gl`: the leading coefficient of `eq:gradient-leading` is strictly positive -/

/-- **The remark's positivity claim**: `∫_{C.body} ‖z‖² > 0` for the unit hemispherical cap
`C = Cap.hemisphere m`. -/
theorem positive_gl (m : ℕ) (hm : 1 ≤ m) :
    0 < ∫ p in (Cap.hemisphere m).body, ‖p.2‖ ^ 2 := by
  set θ : ℝ → ℝ := Cap.semi 1 with hθdef
  have hr_pos : 0 < θ (-(1:ℝ)/4) := Cap.semi_pos 1 le_rfl (by constructor <;> norm_num)
  set r : ℝ := θ (-(1:ℝ)/4) with hrdef
  set z₀ : EuclideanSpace ℝ (Fin m) := (r / 2) • (EuclideanSpace.single ⟨0, by omega⟩ (1:ℝ))
    with hz₀def
  have hnorm_single : ‖(EuclideanSpace.single (⟨0, by omega⟩ : Fin m) (1:ℝ) :
      EuclideanSpace ℝ (Fin m))‖ = 1 := by
    rw [EuclideanSpace.norm_single]; simp
  have hz₀norm : ‖z₀‖ = r / 2 := by
    rw [hz₀def, norm_smul, hnorm_single, Real.norm_eq_abs, mul_one, abs_of_pos (by linarith)]
  set ε : ℝ := r / 4 with hεdef
  set S : Set (CapSpace m) := Ioo (-(3:ℝ)/4) (-(1:ℝ)/4) ×ˢ Metric.ball z₀ ε with hSdef
  have hSsub : S ⊆ (Cap.hemisphere m).body := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hs1 : s ∈ Ioo (-(1:ℝ)) 0 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hsle : s ≤ -(1:ℝ)/4 := le_of_lt hs.2
    have hθanti : θ (-(1:ℝ)/4) ≤ θ s :=
      Cap.semi_antitoneOn 1 hs1 (by constructor <;> norm_num) hsle
    have hzz : ‖z - z₀‖ < ε := hz
    have hzbound : ‖z‖ < r := by
      have heq : z = z₀ + (z - z₀) := by abel
      calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by rw [← heq]
        _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
        _ < r / 2 + ε := by rw [hz₀norm]; linarith [hzz]
        _ = 3 * r / 4 := by rw [hεdef]; ring
        _ < r := by linarith
    refine ⟨hs1.1, hs1.2, ?_⟩
    show ‖z‖ < θ s
    exact hzbound.trans_le hθanti
  have hSlb : ∀ p ∈ S, r ^ 2 / 16 ≤ ‖p.2‖ ^ 2 := by
    rintro ⟨s, z⟩ ⟨-, hz⟩
    have hzz : ‖z - z₀‖ < ε := hz
    have h1 : ‖z₀‖ - ‖z‖ ≤ ‖z - z₀‖ := by
      have h0 := norm_sub_norm_le z₀ z
      rwa [norm_sub_rev z₀ z] at h0
    have h2 : r / 4 < ‖z‖ := by rw [hz₀norm] at h1; rw [hεdef] at hzz; linarith [h1, hzz]
    have h3 : (0:ℝ) ≤ r / 4 := by linarith
    calc r ^ 2 / 16 = (r / 4) ^ 2 := by ring
      _ ≤ ‖z‖ ^ 2 := by nlinarith [h2, h3]
  have hIbody : IntegrableOn (fun p : CapSpace m => ‖p.2‖ ^ 2) (Cap.hemisphere m).body :=
    Cap.integrableOn_body_of_continuous (Cap.hemisphere m) (by fun_prop)
  have hIS : IntegrableOn (fun p : CapSpace m => ‖p.2‖ ^ 2) S := hIbody.mono_set hSsub
  have hSmeas : MeasurableSet S := measurableSet_Ioo.prod measurableSet_ball
  have hvoleq : volume S = volume (Ioo (-(3:ℝ)/4) (-(1:ℝ)/4)) * volume (Metric.ball z₀ ε) := by
    rw [hSdef, Measure.volume_eq_prod ℝ (EuclideanSpace ℝ (Fin m)), Measure.prod_prod]
  have hI1pos : 0 < volume (Ioo (-(3:ℝ)/4) (-(1:ℝ)/4)) := by
    rw [Real.volume_Ioo]; norm_num
  have hI2pos : 0 < volume (Metric.ball z₀ ε) := measure_ball_pos volume z₀ (by linarith : 0 < ε)
  have hfin1 : volume (Ioo (-(3:ℝ)/4) (-(1:ℝ)/4)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hfin2 : volume (Metric.ball z₀ ε) ≠ ⊤ := measure_ball_lt_top.ne
  have hSfin : volume S ≠ ⊤ := by rw [hvoleq]; exact ENNReal.mul_ne_top hfin1 hfin2
  have hvolS : (0:ℝ) < (volume S).toReal := by
    rw [hvoleq, ENNReal.toReal_mul]
    exact mul_pos (ENNReal.toReal_pos hI1pos.ne' hfin1) (ENNReal.toReal_pos hI2pos.ne' hfin2)
  haveI hSfinite : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hSfin⟩
  have hIconst : IntegrableOn (fun _ : CapSpace m => r ^ 2 / 16) S := integrable_const _
  have h1 : (∫ p in S, r ^ 2 / 16) ≤ ∫ p in S, ‖p.2‖ ^ 2 :=
    setIntegral_mono_on hIconst hIS hSmeas hSlb
  have h2 : (∫ p in S, ‖p.2‖ ^ 2) ≤ ∫ p in (Cap.hemisphere m).body, ‖p.2‖ ^ 2 :=
    setIntegral_mono_set hIbody
      (Filter.Eventually.of_forall fun p => sq_nonneg _) hSsub.eventuallyLE
  have h3 : (∫ p in S, r ^ 2 / 16) = r ^ 2 / 16 * (volume S).toReal := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
  have hrsq : 0 < r ^ 2 / 16 * (volume S).toReal := by positivity
  linarith [h1, h2, h3, hrsq]

end RobinCaps.ThinDomain
