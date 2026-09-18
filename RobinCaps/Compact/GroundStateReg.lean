import RobinCaps.Compact.RadialShooting
import RobinCaps.Compact.GroundStateExists
import RobinCaps.Compact.GradCalc
import RobinCaps.ThinDomain.Trial

/-!
# `C¹` regularity of the transverse Robin ground state, for small `R`

This file proves `GroundStateReg.lean` of `RobinCaps/Compact/PLAN_REG.md`: the radial
profile `g_{ν*} := radSeries n (nuStar n R α)` constructed by shooting
(`RobinCaps/Compact/RadialShooting.lean`) gives, after `L²`-normalisation, an element
`psiReg n R α hn` of `H¹(B_n(R))` which is a `TransverseGroundState` (the weak eigen-equation
`weak_eq_radial`, transported through the normalising scalar) **and** is `C¹` and radial and
positive by construction, so it upgrades `hasTransverseGroundState_bdR`
(`RobinCaps/Compact/GroundStateExists.lean`) to a genuine
`RobinCaps.ThinDomain.TransverseGroundStateReg` (`RobinCaps/ThinDomain/Trial.lean`).

The construction of `R₀` from the Poincaré–Wirtinger constant of the unit ball and the gap
estimate `gap_of_small` is exactly that of `hasTransverseGroundState_of`
(`RobinCaps/Compact/GroundStateGap.lean`); it is repeated here (rather than invoked) because the
ground state has to be built explicitly as `psiReg`, not obtained abstractly from
`exists_minimiser'`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter

open RobinCaps.Sobolev.Weak RobinCaps.ThinDomain

open scoped InnerProductSpace ContDiff ENNReal

namespace RobinCaps.Compact

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

variable {R α : ℝ}

/-! ## The unnormalised radial ground state -/

/-- The (unnormalised) radial ground state `ψ(z) = g_{ν*}(‖z‖²)`. -/
def psiRad (n : ℕ) (R α : ℝ) (hn : 1 ≤ n) : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
  radialH1 n R (radSeries n (nuStar n R α)) (contDiff_radSeries hn)

/-- `NB (psiRad …) > 0`: the radial profile is positive on the whole ball, so its `L²` mass is
positive. -/
theorem NB_psiRad_pos (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) :
    0 < NB (psiRad n R α hn) := by
  obtain ⟨_, hpos, _, _⟩ := nuStar_spec hn hR hα
  have hsub : ball (0 : E) R ⊆
      Function.support (fun x : E => radialFun (radSeries n (nuStar n R α)) x ^ 2) := by
    intro x hx
    have hxlt : ‖x‖ < R := mem_ball_zero_iff.1 hx
    have hxsqlt : ‖x‖ ^ 2 < R ^ 2 := pow_lt_pow_left₀ hxlt (norm_nonneg x) two_ne_zero
    have hgxpos : 0 < radialFun (radSeries n (nuStar n R α)) x :=
      hpos (‖x‖ ^ 2) (sq_nonneg _) hxsqlt.le
    exact (sq_pos_of_pos hgxpos).ne'
  have hmeas : (0 : ℝ≥0∞) <
      (volume.restrict (ball (0 : E) R))
        (Function.support (fun x : E => radialFun (radSeries n (nuStar n R α)) x ^ 2)) :=
    calc (0 : ℝ≥0∞) < volume (ball (0 : E) R) := Metric.measure_ball_pos volume 0 hR
      _ = (volume.restrict (ball (0 : E) R)) (ball (0 : E) R) :=
          (Measure.restrict_apply_self _ _).symm
      _ ≤ (volume.restrict (ball (0 : E) R))
            (Function.support (fun x : E => radialFun (radSeries n (nuStar n R α)) x ^ 2)) :=
          measure_mono hsub
  have hNBeq : NB (psiRad n R α hn)
      = ∫ x in ball (0 : E) R, radialFun (radSeries n (nuStar n R α)) x ^ 2 := by
    show mass (radialH1 n R (radSeries n (nuStar n R α)) (contDiff_radSeries hn)) = _
    show ∫ x in ball (0 : E) R,
        (radialH1 n R (radSeries n (nuStar n R α)) (contDiff_radSeries hn)).toFun x ^ 2 = _
    rw [radialH1_toFun]
  rw [hNBeq]
  refine (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) ?_).mpr hmeas
  have hmemL2 : MemLp (fun x : E => radialFun (radSeries n (nuStar n R α)) x)
      2 (volume.restrict (ball (0 : E) R)) := (psiRad n R α hn).memL2
  exact hmemL2.integrable_sq

/-! ## The normalised radial ground state -/

/-- The normalised radial ground state `c • psiRad`, `c = (NB psiRad)^{-1/2}`. -/
def psiReg (n : ℕ) (R α : ℝ) (hn : 1 ≤ n) : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
  (Real.sqrt (NB (psiRad n R α hn)))⁻¹ • psiRad n R α hn

theorem NB_psiReg (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) :
    NB (psiReg n R α hn) = 1 := by
  have hpos : 0 < NB (psiRad n R α hn) := NB_psiRad_pos hn hR hα
  show NB ((Real.sqrt (NB (psiRad n R α hn)))⁻¹ • psiRad n R α hn) = 1
  rw [NB_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

theorem qB_psiReg (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) :
    qB α (bdR n R) (psiReg n R α hn) = lam1 α (bdR n R) := by
  obtain ⟨_, _, hrobin, hlam⟩ := nuStar_spec hn hR hα
  have hpos : 0 < NB (psiRad n R α hn) := NB_psiRad_pos hn hR hα
  set c : ℝ := (Real.sqrt (NB (psiRad n R α hn)))⁻¹ with hc
  have hc2 : c ^ 2 * NB (psiRad n R α hn) = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  have hqrad : qB α (bdR n R) (psiRad n R α hn)
      = nuStar n R α * NB (psiRad n R α hn) :=
    qB_radial hn hR (contDiff_radSeries hn) (radSeries_ode_ball hn (nuStar n R α) R) α hrobin
  show qB α (bdR n R) (c • psiRad n R α hn) = lam1 α (bdR n R)
  rw [qB_smul, hqrad, ← hlam]
  calc c ^ 2 * (nuStar n R α * NB (psiRad n R α hn))
      = nuStar n R α * (c ^ 2 * NB (psiRad n R α hn)) := by ring
    _ = nuStar n R α * 1 := by rw [hc2]
    _ = nuStar n R α := mul_one _

theorem weak_eq_psiReg (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) (v : TransH1 n R) :
    qBilin α (bdR n R) (psiReg n R α hn) v
      = lam1 α (bdR n R) * NBilin (psiReg n R α hn) v := by
  obtain ⟨_, _, hrobin, hlam⟩ := nuStar_spec hn hR hα
  set c : ℝ := (Real.sqrt (NB (psiRad n R α hn)))⁻¹ with hc
  have hweak : qBilin α (bdR n R) (psiRad n R α hn) v
      = nuStar n R α * NBilin (psiRad n R α hn) v :=
    weak_eq_radial hn hR (contDiff_radSeries hn) (radSeries_ode_ball hn (nuStar n R α) R) α
      hrobin v
  have hq : qBilin α (bdR n R) (c • psiRad n R α hn) v
      = c * qBilin α (bdR n R) (psiRad n R α hn) v := by
    show qBilinₗ α (bdR n R) (c • psiRad n R α hn) v
      = c * qBilinₗ α (bdR n R) (psiRad n R α hn) v
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hN : NBilin (c • psiRad n R α hn) v = c * NBilin (psiRad n R α hn) v := by
    show NBilinₗ n R (c • psiRad n R α hn) v = c * NBilinₗ n R (psiRad n R α hn) v
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  show qBilin α (bdR n R) (c • psiRad n R α hn) v
      = lam1 α (bdR n R) * NBilin (c • psiRad n R α hn) v
  rw [hq, hweak, hN, ← hlam]
  ring

/-! ## Regularity of `psiReg` -/

theorem contDiff_psiReg (hn : 1 ≤ n) :
    ContDiff ℝ 1 (fun z => (psiReg n R α hn).toFun z) := by
  have heq : (fun z : E => (psiReg n R α hn).toFun z)
      = fun z => (Real.sqrt (NB (psiRad n R α hn)))⁻¹
        * radialFun (radSeries n (nuStar n R α)) z := by
    funext z
    simp [psiReg, psiRad, H1.smul_toFun, radialH1_toFun]
  rw [heq]
  exact contDiff_const.mul ((contDiff_radialFun (contDiff_radSeries hn)).of_le (by norm_num))

theorem grad_psiReg (hn : 1 ≤ n) (z : E) :
    (psiReg n R α hn).grad z = classicalGrad (fun w => (psiReg n R α hn).toFun w) z := by
  have hfun : (fun w : E => (psiReg n R α hn).toFun w)
      = fun w => (Real.sqrt (NB (psiRad n R α hn)))⁻¹
        * radialFun (radSeries n (nuStar n R α)) w := by
    funext w
    simp [psiReg, psiRad, H1.smul_toFun, radialH1_toFun]
  have hgradpsi : (psiReg n R α hn).grad z
      = (Real.sqrt (NB (psiRad n R α hn)))⁻¹ • (psiRad n R α hn).grad z := rfl
  have hgradrad : (psiRad n R α hn).grad z
      = classicalGrad (radialFun (radSeries n (nuStar n R α))) z :=
    congrFun (radialH1_grad n R (radSeries n (nuStar n R α)) (contDiff_radSeries hn)) z
  have hdiff : DifferentiableAt ℝ (radialFun (radSeries n (nuStar n R α))) z :=
    ((contDiff_radialFun (contDiff_radSeries hn)).of_le (by norm_num)).differentiable le_rfl z
  rw [hfun, hgradpsi, hgradrad, classicalGrad_const_mul _ hdiff]

theorem psiReg_pos (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) (z : E) (hz : z ∈ ball (0 : E) R) :
    0 < (psiReg n R α hn).toFun z := by
  obtain ⟨_, hpos, _, _⟩ := nuStar_spec hn hR hα
  have hpsipos : 0 < NB (psiRad n R α hn) := NB_psiRad_pos hn hR hα
  have hcpos : 0 < (Real.sqrt (NB (psiRad n R α hn)))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr hpsipos)
  have hgpos : 0 < radialFun (radSeries n (nuStar n R α)) z := by
    have hzlt : ‖z‖ < R := mem_ball_zero_iff.1 hz
    have hzsqlt : ‖z‖ ^ 2 < R ^ 2 := pow_lt_pow_left₀ hzlt (norm_nonneg z) two_ne_zero
    exact hpos (‖z‖ ^ 2) (sq_nonneg _) hzsqlt.le
  have heq : (psiReg n R α hn).toFun z
      = (Real.sqrt (NB (psiRad n R α hn)))⁻¹ * radialFun (radSeries n (nuStar n R α)) z := by
    simp [psiReg, psiRad, H1.smul_toFun, radialH1_toFun]
  rw [heq]
  exact mul_pos hcpos hgpos

/-! ## The main theorem -/

/-- **The regular transverse ground state for small `R`.** For `1 ≤ n` and `0 ≤ α` there is
`R₀ > 0` such that for every `0 < R < R₀` the Robin ground state on `B_n(R)`, with the boundary
form `bdR n R`, exists with the `C¹` regularity of `TransverseGroundStateReg`, and is radial and
strictly positive. -/
theorem exists_transverseGroundStateReg (n : ℕ) (hn : 1 ≤ n) {α : ℝ} (hα : 0 ≤ α) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∃ gsr : TransverseGroundStateReg n α R (bdR n R),
        IsRadialGroundState gsr ∧ IsPositiveGroundState gsr := by
  obtain ⟨C, hC, hpw⟩ := poincare_wirtinger_ball (n := n) (rellichSeq' n one_pos)
  set K : ℝ := 8 * C * ((n : ℝ) * α + 1) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨min 1 (1 / K), lt_min one_pos (by positivity), fun R hR hRR₀ => ?_⟩
  have hRK : R * K < 1 := by
    have h := lt_of_lt_of_le hRR₀ (min_le_right _ _)
    rwa [lt_div_iff₀ hKpos] at h
  have hθ : C * ((n : ℝ) * α) * R ≤ 1 / 8 := by
    have h1 : C * ((n : ℝ) * α) * R ≤ C * ((n : ℝ) * α + 1) * R := by
      apply mul_le_mul_of_nonneg_right _ hR.le
      apply mul_le_mul_of_nonneg_left _ hC.le
      linarith
    have h8 : 8 * (C * ((n : ℝ) * α + 1) * R) < 1 := by
      rw [hK] at hRK; linarith
    linarith
  have hbdnn : ∀ u : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R), 0 ≤ bdR n R u u :=
    bdR_nonneg hn hR
  refine ⟨⟨⟨bdR_symm, hbdnn, psiReg n R α hn, lam1 α (bdR n R), NB_psiReg hn hR hα,
      weak_eq_psiReg hn hR hα, 1 / (2 * C), by positivity,
      fun v hv => gap_of_small hR hα hbdnn (hpw R hR) hC hθ (psiReg n R α hn) (NB_psiReg hn hR hα)
        (qB_psiReg hn hR hα) (lam1_bdR_le hn hR hα hbdnn) v hv⟩,
    contDiff_psiReg hn, fun z _ => grad_psiReg hn z⟩, ?_, ?_⟩
  · exact ⟨fun r => (Real.sqrt (NB (psiRad n R α hn)))⁻¹ * radSeries n (nuStar n R α) (r ^ 2),
      fun z => by
        show (psiReg n R α hn).toFun z = _
        have heq : (psiReg n R α hn).toFun z
            = (Real.sqrt (NB (psiRad n R α hn)))⁻¹
              * radialFun (radSeries n (nuStar n R α)) z := by
          simp [psiReg, psiRad, H1.smul_toFun, radialH1_toFun]
        rw [heq, radialFun_apply]⟩
  · exact fun z hz => psiReg_pos hn hR hα z hz

/-- **Existence of the regular transverse ground state for small `R`**, as a bare `Nonempty`. -/
theorem hasTransverseGroundStateReg (n : ℕ) (hn : 1 ≤ n) {α : ℝ} (hα : 0 ≤ α) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      Nonempty (TransverseGroundStateReg n α R (bdR n R)) := by
  obtain ⟨R₀, hR₀, h⟩ := exists_transverseGroundStateReg n hn hα
  exact ⟨R₀, hR₀, fun R hR hRR₀ => ⟨(h R hR hRR₀).choose⟩⟩

end RobinCaps.Compact

end

#print axioms RobinCaps.Compact.exists_transverseGroundStateReg
