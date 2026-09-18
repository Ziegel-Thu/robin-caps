import RobinCaps.ThinDomain.TrialBound
import RobinCaps.Transverse.GroundStateOneReg
import RobinCaps.Transverse.OneDimExpansion

/-!
# The transverse expansions and the trial-function bounds for `m = 1`
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain

noncomputable section

/-! ## 1. `Ψ_R` for `m = 1` is `scaledGroundState` -/

/-- Scalar multiples act on `ept` by multiplication. -/
theorem smul_ept_one (c t : ℝ) :
    c • Transverse.ept t = Transverse.ept (c * t) := by
  ext i
  fin_cases i
  simp [Transverse.ept]

/-- `R ^ (1/2) = √R` with the natural-number cast of `m = 1`. -/
theorem rpow_one_half_eq_sqrt (R : ℝ) :
    R ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt R := by
  rw [Nat.cast_one]
  exact (Real.sqrt_eq_rpow R).symm

/-- **The lifted transverse ground state for `m = 1` is `scaledGroundState`.** -/
theorem transLift_one_ept (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (t : ℝ) :
    transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi (Transverse.ept t)
      = Transverse.scaledGroundState α R hα hR t := by
  rw [Transverse.psiN_scaled_eq α R hα hR t]
  show R ^ (((1 : ℕ) : ℝ) / 2) *
      (Transverse.psiN α R hα hR).toFun (R • Transverse.ept t) = _
  rw [smul_ept_one, rpow_one_half_eq_sqrt]

theorem transLift_one_eq (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi
      = fun y : EuclideanSpace ℝ (Fin 1) => Transverse.scaledGroundState α R hα hR (y 0) := by
  funext y
  rw [← transLift_one_ept α R hα hR (y 0), ← Transverse.eq_ept y]

/-! ## 2. The derivative of `scaledGroundState` is the classical gradient of `Ψ_R` -/

/-- `ept` as a continuous linear map. -/
def eptL : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Transverse.ept 1)

@[simp] theorem eptL_apply_one (t : ℝ) : eptL t = Transverse.ept t :=
  (Transverse.ept_eq_smul t).symm

/-- For a `C¹` function on the line `EuclideanSpace ℝ (Fin 1)`, the derivative of its
restriction to `ℝ` is the unique coordinate of its classical gradient. -/
theorem hasDerivAt_comp_ept_one {Φ : EuclideanSpace ℝ (Fin 1) → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => Φ (Transverse.ept s))
      (Weak.classicalGrad Φ (Transverse.ept t) 0) t := by
  have h1 : HasFDerivAt Φ (fderiv ℝ Φ (eptL t)) (eptL t) :=
    (hΦ.differentiable le_rfl _).hasFDerivAt
  have h3 : HasFDerivAt (fun s : ℝ => Φ (eptL s))
      ((fderiv ℝ Φ (eptL t)).comp eptL) t := h1.comp t eptL.hasFDerivAt
  have h4 := h3.hasDerivAt
  have hval : ((fderiv ℝ Φ (eptL t)).comp eptL) 1
      = Weak.classicalGrad Φ (Transverse.ept t) 0 := by
    rw [Weak.classicalGrad_apply]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, eptL_apply_one]
    rw [Transverse.ept_one]
  rw [hval] at h4
  simpa using h4

theorem deriv_scaledGroundState_one (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (t : ℝ) :
    deriv (Transverse.scaledGroundState α R hα hR) t
      = Weak.classicalGrad (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
          (Transverse.ept t) 0 := by
  have hC1 : ContDiff ℝ 1 (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi) :=
    contDiff_transLift (Transverse.groundStateOneReg α R hα hR).psiC1
  have h := hasDerivAt_comp_ept_one hC1 t
  have hfun : (fun s : ℝ =>
      transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi (Transverse.ept s))
      = Transverse.scaledGroundState α R hα hR :=
    funext fun s => transLift_one_ept α R hα hR s
  rw [hfun] at h
  exact h.deriv

theorem norm_classicalGrad_transLift_one (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (t : ℝ) :
    ‖Weak.classicalGrad (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
        (Transverse.ept t)‖ ^ 2
      = deriv (Transverse.scaledGroundState α R hα hR) t ^ 2 := by
  rw [Transverse.norm_sq_one_dim, deriv_scaledGroundState_one α R hα hR t]

/-! ## 3. The three unit-ball integrals of `TransverseExpansionData` for `m = 1` -/

theorem integral_ball_one_transLift_sub (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (c : ℝ) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y - c) ^ 2)
      = ∫ t in (-1 : ℝ)..1, (Transverse.scaledGroundState α R hα hR t - c) ^ 2 := by
  rw [Transverse.integral_ball_one (by norm_num : (0:ℝ) ≤ 1)]
  exact intervalIntegral.integral_congr fun t _ => by
    rw [transLift_one_ept α R hα hR t]

theorem integral_ball_one_grad_transLift (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        ‖Weak.classicalGrad (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi) y‖ ^ 2)
      = ∫ t in (-1 : ℝ)..1, deriv (Transverse.scaledGroundState α R hα hR) t ^ 2 := by
  rw [Transverse.integral_ball_one (by norm_num : (0:ℝ) ≤ 1)]
  exact intervalIntegral.integral_congr fun t _ =>
    norm_classicalGrad_transLift_one α R hα hR t

theorem integral_ball_one_transLift (α R : ℝ) (hα : 0 < α) (hR : 0 < R) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
      = Transverse.dR α R hα hR := by
  rw [Transverse.integral_ball_one (by norm_num : (0:ℝ) ≤ 1), Transverse.dR]
  exact intervalIntegral.integral_congr fun t _ => transLift_one_ept α R hα hR t

/-! ## 4. The transverse expansion data for `m = 1` -/

/-- **`lem:transverse` for `m = 1`, in the form required by `TrialBound.lean`.**  One explicit
constant `Cexp` and one threshold `R₀ ≤ 1` serve every `0 < R < R₀`. -/
theorem transverseExpansionData_one (α : ℝ) (hα : 0 < α) :
    ∃ Cexp R₀ : ℝ, 0 < R₀ ∧ R₀ ≤ 1 ∧ ∀ R : ℝ, ∀ hR : 0 < R, R < R₀ →
      TransverseExpansionData 1 α R (Transverse.groundStateOneReg α R hα hR) Cexp := by
  obtain ⟨C₁, R₁, hR₁, h₁⟩ := Transverse.psiH1_target α hα
  obtain ⟨C₂, R₂, hR₂, h₂⟩ := Transverse.dR_target α hα
  obtain ⟨C₃, R₃, hR₃, h₃⟩ := Transverse.nuR_expansion α hα
  set Cexp : ℝ := max (max |C₁| C₂) C₃ with hCexp
  have hC1le : |C₁| ≤ Cexp := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2le : C₂ ≤ Cexp := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3le : C₃ ≤ Cexp := le_max_right _ _
  have hCexp0 : 0 ≤ Cexp := le_trans (abs_nonneg C₁) hC1le
  refine ⟨Cexp, min (min R₁ R₂) (min R₃ 1), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hR₁ hR₂) (lt_min hR₃ one_pos)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)
  intro R hR hRlt
  have hR1 : R < R₁ := lt_of_lt_of_le hRlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hR2 : R < R₂ := lt_of_lt_of_le hRlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hR3 : R < R₃ := lt_of_lt_of_le hRlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRle1 : R ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hRlt (le_trans (min_le_right _ _) (min_le_right _ _)))
  obtain ⟨hdR1, hdR2⟩ := h₂ R hR hR2
  refine { psiH1 := ?_, dR_close := ?_, dR_ge := ?_, nuExp := ?_, bdSphere := ?_ }
  · rw [integral_ball_one_transLift_sub, integral_ball_one_grad_transLift, Cap.omega_one]
    have hsq : C₁ ^ 2 ≤ Cexp ^ 2 := by
      have : |C₁| ^ 2 ≤ Cexp ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg C₁) hC1le 2
      rwa [sq_abs] at this
    calc (∫ t in (-1 : ℝ)..1,
          (Transverse.scaledGroundState α R hα hR t - (Real.sqrt 2)⁻¹) ^ 2)
        + (∫ t in (-1 : ℝ)..1, deriv (Transverse.scaledGroundState α R hα hR) t ^ 2)
        ≤ C₁ ^ 2 * R ^ 2 := h₁ R hR hR1
      _ ≤ Cexp ^ 2 * R ^ 2 := by nlinarith [sq_nonneg R]
  · rw [integral_ball_one_transLift, Cap.omega_one]
    calc |Transverse.dR α R hα hR - Real.sqrt 2| ≤ C₂ * R ^ 2 := hdR1
      _ ≤ Cexp * R ^ 2 := by nlinarith [sq_nonneg R]
      _ ≤ Cexp * R := by
          nlinarith [mul_nonneg (mul_nonneg hCexp0 hR.le) (sub_nonneg.mpr hRle1)]
  · rw [integral_ball_one_transLift, Cap.omega_one]
    exact hdR2
  · rw [Transverse.groundStateOneReg_nu, Nat.cast_one, one_mul]
    calc |R ^ 2 * Transverse.nuR α R hα hR - α * R| ≤ C₃ * R ^ 2 := h₃ R hR hR3
      _ ≤ Cexp * R ^ 2 := by nlinarith [sq_nonneg R]
  · exact Transverse.bdTr_psiN_eq_sphereIntegral α R hα hR

/-! ## 5. The terminal radius of the hemispherical cap -/

/-- **The hemispherical cap closes up**: `θ(0) = √(1 - 1²) = 0`. -/
theorem hemisphere_theta_zero_one (m : ℕ) : (Cap.hemisphere m).θ 0 = 0 := by
  show Cap.semi 1 0 = 0
  rw [Cap.semi]
  norm_num

/-- The two bounds on `θ(0)` required by `cap_upper_J` for the hemisphere. -/
theorem hemisphere_theta_zero_bounds_one (m : ℕ) :
    0 ≤ (Cap.hemisphere m).θ 0 ∧ (Cap.hemisphere m).θ 0 ≤ 1 := by
  rw [hemisphere_theta_zero_one]
  constructor <;> norm_num

/-! ## 6. The trial-function mass bound for `m = 1` -/

/-- **`eq:trial-mass` for `m = 1`**, for the explicit transverse ground state.  The constant is
`A = K₋ + K₊`, and no smallness of `R` is needed. -/
theorem trial_mass_one (α : ℝ) (hα : 0 < α) (Cm Cp : Cap 1) (L : ℝ) :
    ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
      ∀ hL : (Cm.K + Cp.K) * R < L,
        ∀ (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F),
          (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
              ≤ massP (trialH1P Cm Cp L hR hL F hF
                  (Transverse.groundStateOneReg α R hα hR)) ∧
            massP (trialH1P Cm Cp L hR hL F hF (Transverse.groundStateOneReg α R hα hR))
              ≤ (∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), F x ^ 2)
                + A * R * (F (-L/2 + Cm.K * R) ^ 2 + F (L/2 - Cp.K * R) ^ 2) := by
  refine ⟨Cm.K + Cp.K, 1, one_pos, fun R hR _ hL F hF => ?_⟩
  set gsr := Transverse.groundStateOneReg α R hα hR with hgsr
  have hmass := massP_trialH1P_caps Cm Cp L hR hL F hF gsr
  have h1 := cap_mass_le hR Cm gsr
  have h2 := cap_mass_le hR Cp gsr
  have h01 := cap_mass_nonneg Cm gsr
  have h02 := cap_mass_nonneg Cp gsr
  have hsm := sq_nonneg (F (-L/2 + Cm.K * R))
  have hsp := sq_nonneg (F (L/2 - Cp.K * R))
  have hKm := Cm.hK.le
  have hKp := Cp.hK.le
  constructor
  · rw [hmass]
    linarith [mul_nonneg hsm (mul_nonneg hR.le h01), mul_nonneg hsp (mul_nonneg hR.le h02)]
  · rw [hmass]
    have hA : F (-L/2 + Cm.K * R) ^ 2
        * (R * ∫ p in Cm.body, capGroundLift 1 R gsr.psi p ^ 2)
        ≤ (Cm.K + Cp.K) * R * F (-L/2 + Cm.K * R) ^ 2 := by
      have hMle : (∫ p in Cm.body, capGroundLift 1 R gsr.psi p ^ 2) ≤ Cm.K + Cp.K := by
        linarith [h1, hKp]
      calc F (-L/2 + Cm.K * R) ^ 2 * (R * ∫ p in Cm.body, capGroundLift 1 R gsr.psi p ^ 2)
          ≤ F (-L/2 + Cm.K * R) ^ 2 * (R * (Cm.K + Cp.K)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMle hR.le) hsm
        _ = (Cm.K + Cp.K) * R * F (-L/2 + Cm.K * R) ^ 2 := by ring
    have hB : F (L/2 - Cp.K * R) ^ 2
        * (R * ∫ p in Cp.body, capGroundLift 1 R gsr.psi p ^ 2)
        ≤ (Cm.K + Cp.K) * R * F (L/2 - Cp.K * R) ^ 2 := by
      have hMle : (∫ p in Cp.body, capGroundLift 1 R gsr.psi p ^ 2) ≤ Cm.K + Cp.K := by
        linarith [h2, hKm]
      calc F (L/2 - Cp.K * R) ^ 2 * (R * ∫ p in Cp.body, capGroundLift 1 R gsr.psi p ^ 2)
          ≤ F (L/2 - Cp.K * R) ^ 2 * (R * (Cm.K + Cp.K)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMle hR.le) hsp
        _ = (Cm.K + Cp.K) * R * F (L/2 - Cp.K * R) ^ 2 := by ring
    linarith [hA, hB]

/-! ## 7. The trial-function energy bound for `m = 1` -/

/-- **`eq:trial-energy` for `m = 1`**, for the explicit transverse ground state: the
renormalized energy of the trial function is the one-dimensional Robin form of `F` on the
shortened interval, up to an error `O(R) S[F]`. -/
theorem trial_energy_one (α : ℝ) (hα : 0 < α) (Cm Cp : Cap 1) (L : ℝ)
    (hθ0m : 0 ≤ Cm.θ 0) (hθ1m : Cm.θ 0 ≤ 1) (hθ0p : 0 ≤ Cp.θ 0) (hθ1p : Cp.θ 0 ≤ 1) :
    ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₀ → ∀ hL : (Cm.K + Cp.K) * R < L,
      ∀ (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F),
        |renormEnergy Cm Cp L R α (Transverse.groundStateOneReg α R hα hR).nu
            (trialH1P Cm Cp L hR hL F hF (Transverse.groundStateOneReg α R hα hR))
          - ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
            + Cap.beta Cm α * F (-L/2 + Cm.K * R) ^ 2
            + Cap.beta Cp α * F (L/2 - Cp.K * R) ^ 2)|
        ≤ A * R * (F (-L/2 + Cm.K * R) ^ 2 + F (L/2 - Cp.K * R) ^ 2) := by
  obtain ⟨Cexp, R₀, hR₀, hR₀1, hh⟩ := transverseExpansionData_one α hα
  refine ⟨max (Cm.K * Cexp ^ 2 + (|α| * capBdryConst 1 Cm Cexp
      + ((1 : ℕ) : ℝ) * |α| * capMassConst 1 Cm Cexp + Cexp * Cm.K))
    (Cp.K * Cexp ^ 2 + (|α| * capBdryConst 1 Cp Cexp
      + ((1 : ℕ) : ℝ) * |α| * capMassConst 1 Cp Cexp + Cexp * Cp.K)),
    R₀, hR₀, fun R hR hRlt hL F hF => ?_⟩
  have hexp := hh R hR hRlt
  have hR1 : R ≤ 1 := le_of_lt (lt_of_lt_of_le hRlt hR₀1)
  have hm : 1 ≤ 1 := le_refl 1
  set gsr := Transverse.groundStateOneReg α R hα hR with hgsr
  rw [renormEnergy_trialH1P hm Cm Cp L hR hL F hF gsr hexp.bdSphere]
  set Am : ℝ := Cm.K * Cexp ^ 2 + (|α| * capBdryConst 1 Cm Cexp
      + ((1 : ℕ) : ℝ) * |α| * capMassConst 1 Cm Cexp + Cexp * Cm.K) with hAm
  set Ap : ℝ := Cp.K * Cexp ^ 2 + (|α| * capBdryConst 1 Cp Cexp
      + ((1 : ℕ) : ℝ) * |α| * capMassConst 1 Cp Cexp + Cexp * Cp.K) with hAp
  have hEm := capEnergyTerm_sub_beta hm hR hR1 Cm hθ0m hθ1m hexp
  have hEp := capEnergyTerm_sub_beta hm hR hR1 Cp hθ0p hθ1p hexp
  rw [← hAm] at hEm
  rw [← hAp] at hEp
  have hsplit : ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
        + F (-L/2 + Cm.K * R) ^ 2 * capEnergyTerm 1 α R Cm gsr
        + F (L/2 - Cp.K * R) ^ 2 * capEnergyTerm 1 α R Cp gsr)
      - ((∫ x in Ioo (-L/2 + Cm.K * R) (L/2 - Cp.K * R), deriv F x ^ 2)
        + Cap.beta Cm α * F (-L/2 + Cm.K * R) ^ 2
        + Cap.beta Cp α * F (L/2 - Cp.K * R) ^ 2)
      = F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm 1 α R Cm gsr - Cap.beta Cm α)
        + F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm 1 α R Cp gsr - Cap.beta Cp α) := by
    ring
  rw [hsplit]
  have hsm := sq_nonneg (F (-L/2 + Cm.K * R))
  have hsp := sq_nonneg (F (L/2 - Cp.K * R))
  have hAmle : Am ≤ max Am Ap := le_max_left _ _
  have hAple : Ap ≤ max Am Ap := le_max_right _ _
  have hb1 : |F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm 1 α R Cm gsr - Cap.beta Cm α)|
      ≤ F (-L/2 + Cm.K * R) ^ 2 * (max Am Ap * R) := by
    rw [abs_mul, abs_of_nonneg hsm]
    refine mul_le_mul_of_nonneg_left (hEm.trans ?_) hsm
    exact mul_le_mul_of_nonneg_right hAmle hR.le
  have hb2 : |F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm 1 α R Cp gsr - Cap.beta Cp α)|
      ≤ F (L/2 - Cp.K * R) ^ 2 * (max Am Ap * R) := by
    rw [abs_mul, abs_of_nonneg hsp]
    refine mul_le_mul_of_nonneg_left (hEp.trans ?_) hsp
    exact mul_le_mul_of_nonneg_right hAple hR.le
  calc |F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm 1 α R Cm gsr - Cap.beta Cm α)
        + F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm 1 α R Cp gsr - Cap.beta Cp α)|
      ≤ |F (-L/2 + Cm.K * R) ^ 2 * (capEnergyTerm 1 α R Cm gsr - Cap.beta Cm α)|
        + |F (L/2 - Cp.K * R) ^ 2 * (capEnergyTerm 1 α R Cp gsr - Cap.beta Cp α)| :=
        abs_add_le _ _
    _ ≤ F (-L/2 + Cm.K * R) ^ 2 * (max Am Ap * R)
        + F (L/2 - Cp.K * R) ^ 2 * (max Am Ap * R) := add_le_add hb1 hb2
    _ = max Am Ap * R * (F (-L/2 + Cm.K * R) ^ 2 + F (L/2 - Cp.K * R) ^ 2) := by ring

/-- **`eq:trial-energy` for two hemispherical caps and `m = 1`.** -/
theorem trial_energy_one_hemisphere (α : ℝ) (hα : 0 < α) (L : ℝ) :
    ∃ A R₀ : ℝ, 0 < R₀ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
      ∀ hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L,
      ∀ (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F),
        |renormEnergy (Cap.hemisphere 1) (Cap.hemisphere 1) L R α
            (Transverse.groundStateOneReg α R hα hR).nu
            (trialH1P (Cap.hemisphere 1) (Cap.hemisphere 1) L hR hL F hF
              (Transverse.groundStateOneReg α R hα hR))
          - ((∫ x in Ioo (-L/2 + (Cap.hemisphere 1).K * R) (L/2 - (Cap.hemisphere 1).K * R),
                deriv F x ^ 2)
            + Cap.beta (Cap.hemisphere 1) α * F (-L/2 + (Cap.hemisphere 1).K * R) ^ 2
            + Cap.beta (Cap.hemisphere 1) α * F (L/2 - (Cap.hemisphere 1).K * R) ^ 2)|
        ≤ A * R * (F (-L/2 + (Cap.hemisphere 1).K * R) ^ 2
            + F (L/2 - (Cap.hemisphere 1).K * R) ^ 2) :=
  trial_energy_one α hα (Cap.hemisphere 1) (Cap.hemisphere 1) L
    (hemisphere_theta_zero_bounds_one 1).1 (hemisphere_theta_zero_bounds_one 1).2
    (hemisphere_theta_zero_bounds_one 1).1 (hemisphere_theta_zero_bounds_one 1).2


end

end RobinCaps.ThinDomain
