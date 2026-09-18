import RobinCaps.ThinDomain.BridgeCapLowerMixed
import RobinCaps.Cap.Unconditional

/-!
# `lem:cap` for the single-cap thin domain: an arbitrary pair of caps

This file redoes `RobinCaps/ThinDomain/BridgeCapLowerMixed.lean` for an **arbitrary** pair of
admissible caps `Cm Cp : Cap m`, with **abstract** trace data `tdM : CapTraceData Cm` and
`tdP : CapTraceData Cp` supplied by the caller (no analogue of `capTraceDataHemi_th` is assumed
for either cap). Every construction of `BridgeCapLowerMixed.lean` carries over unchanged once its
two cap-specific inputs

* `flat_theta_zero_nonneg_bcm`/`hemisphere_theta_zero_nonneg_bcg` (`0 ≤ C.θ 0`), and
* `flat_beta_pos`/`hemisphere_beta_pos` (`0 < C.beta α`)

are replaced by the two general facts `cap_theta_zero_nonneg_bg2`/`cap_beta_pos_bg2` proved below,
which hold for *every* admissible cap (the first from the `θ_terminal`/`θ_pos` fields of `Cap`,
the second from the sharp cap inequality `beta_ge_beta0_uc`). The bookkeeping constant
`capLowerConstGen_bcm` (`BridgeCapLowerMixed.lean`) is already stated for an arbitrary cap, so it
is reused as-is, instantiated once per side and combined by `max`, exactly as
`capLowerInput_mixed_bcm` does for the flat/hemisphere pair.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 0. Two facts holding for every admissible cap -/

/-- `0 ≤ θ(0)` for every admissible cap (the stored `θ(0)` is the left limit, and `θ > 0`
inside). The general-cap replacement for `flat_theta_zero_nonneg_bcm`/
`hemisphere_theta_zero_nonneg_bcg`. -/
theorem cap_theta_zero_nonneg_bg2 {m : ℕ} (C : Cap m) : 0 ≤ C.θ 0 := by
  have hmem : Set.Ioo (-C.K) (0 : ℝ) ∈ 𝓝[<] (0 : ℝ) :=
    Ioo_mem_nhdsLT (by linarith [C.hK])
  refine ge_of_tendsto C.θ_terminal ?_
  filter_upwards [hmem] with x hx
  exact (C.θ_pos x hx).le

/-- Every admissible cap has `0 < β(𝒞)` for `α > 0`, from the sharp cap inequality
(`beta_ge_beta0_uc`). The general-cap replacement for `flat_beta_pos`/`hemisphere_beta_pos`. -/
theorem cap_beta_pos_bg2 (m : ℕ) (hm : 1 ≤ m) (C : Cap m) {α : ℝ} (hα : 0 < α) :
    0 < C.beta α :=
  lt_of_lt_of_le (RobinCaps.Cap.beta_ge_beta0_uc m hm C hα).2
    (RobinCaps.Cap.beta_ge_beta0_uc m hm C hα).1

/-! ## 1. The two cap pieces of the mixed domain's boundary form, generically -/

/-- **The left-cap piece**: the rescaled unit-cap `Γ`-trace form, at `c = R^{m/2}`, against the
abstract trace datum `tdM`. The general-cap analogue of `bdCapLFlat_bcm`. -/
def bdCapL_bg2 {m : ℕ} (Cm Cp : Cap m) (tdM : CapTraceData Cm) (L R : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2
    * tdM.bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) u) (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)

/-- **The right-cap piece**: the rescaled unit-cap `Γ`-trace form, at `c = R^{m/2}`, against the
abstract trace datum `tdP`. The general-cap analogue of `bdCapRHemi_bcm`. -/
def bdCapR_bg2 {m : ℕ} (Cm Cp : Cap m) (tdP : CapTraceData Cp) (L R : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2
    * tdP.bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) u) (capRight hR hL (R ^ ((m : ℝ) / 2)) u)

/-- **The unit-cap energy of the left cap component is the thin-domain left-cap energy.**
The general-cap analogue of `capEnergyW_capLeftFlat_bcm`. -/
theorem capEnergyW_capLeft_bg2 {m : ℕ} (Cm Cp : Cap m) {α L R : ℝ} (tdM : CapTraceData Cm)
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (ν : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    capEnergyW Cm α tdM R (R * ν - (m : ℝ) * α) (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
      = capEnergyL_gm α ν hR hL (bdCapL_bg2 Cm Cp tdM L R hR hL) u := by
  have hc : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hRne : R ≠ 0 := hR.ne'
  have hRmne : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  rw [capEnergyW, capJW, capEnergyL_gm, bdCapL_bg2, inv_pow, hc,
    dirichletP_capLeft_of_sq_eq hR hL hc u, massP_capLeft_of_sq_eq hR hL hc u]
  field_simp
  ring

/-- **The unit-cap energy of the right cap component is the thin-domain right-cap energy.**
The general-cap analogue of `capEnergyW_capRightHemi_bcm`. -/
theorem capEnergyW_capRight_bg2 {m : ℕ} (Cm Cp : Cap m) {α L R : ℝ} (tdP : CapTraceData Cp)
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (ν : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    capEnergyW Cp α tdP R (R * ν - (m : ℝ) * α) (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
      = capEnergyR_gm α ν hR hL (bdCapR_bg2 Cm Cp tdP L R hR hL) u := by
  have hc : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hRne : R ≠ 0 := hR.ne'
  have hRmne : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  rw [capEnergyW, capJW, capEnergyR_gm, bdCapR_bg2, inv_pow, hc,
    dirichletP_capRight_of_sq_eq hR hL hc u, massP_capRight_of_sq_eq hR hL hc u]
  field_simp
  ring

/-! ## 2. `lem:cap` at a single admissible radius, for an arbitrary pair of caps

The general-cap copies of `cap_lower_left_flat_bcm`/`cap_lower_right_hemi_bcm`/
`cap_mass_left_flat_bcm`/`cap_mass_right_hemi_bcm`, each stated against an *external* bookkeeping
constant `Ccap`, together with the hypothesis that the relevant per-cap constant
`capLowerConstGen_bcm` is `≤ Ccap`, exactly as in `BridgeCapLowerMixed.lean`. -/

theorem cap_lower_left_bg2 {m : ℕ} (hm : 1 ≤ m) (Cm Cp : Cap m) {α L R : ℝ} (hα : 0 < α)
    (tdM : CapTraceData Cm) {CP C₁ Cexp Ccap : ℝ} (hP : CapPoincare Cm CP)
    (hen : CapEntranceL2 Cm C₁) (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (hCexp : 0 ≤ Cexp)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hδ : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R)
    (hRc : R < capR0W Cm α tdM CP C₁ Cexp)
    (hBR : capLowerConstW Cm α tdM CP C₁ Cexp * R ≤ omega m * Cm.beta α)
    (hCcap : capLowerConstGen_bcm Cm α tdM CP C₁ Cexp ≤ Ccap)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    (Cm.beta α - Ccap * R) * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW Cm (transLift m R gs.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
            (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyL_gm α gs.nu hR hL (bdCapL_bg2 Cm Cp tdM L R hR hL) u := by
  have hkey := cap_lower_weak_p Cm hm (cap_theta_zero_nonneg_bg2 Cm)
    tdM hP hen hCexp hα.le (cap_beta_pos_bg2 m hm Cm hα).le
    (memLp_transLift_gm_bcw hR gs) (integral_transLift_sq_gm_bcw hR gs) rfl
    hdR hR hRc hδ hBR (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capLeft_bg2 Cm Cp tdM hR hL gs.nu u,
    pCoefW_capLeft_gen_gm_bcw hR hL gs u] at hkey
  have hle : capLowerConstW Cm α tdM CP C₁ Cexp / omega m ≤ Ccap :=
    le_trans (capLowerConstW_div_le_gen_bcm Cm α tdM CP C₁ Cexp) hCcap
  have hcoef : Cm.beta α - Ccap * R
      ≤ Cm.beta α - capLowerConstW Cm α tdM CP C₁ Cexp / omega m * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ((axialRep_gm hR hL gs u).toFun 0))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW Cm (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW Cm (transLift m R gs.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
          (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by ring
  rw [hdiv]
  linarith

theorem cap_lower_right_bg2 {m : ℕ} (hm : 1 ≤ m) (Cm Cp : Cap m) {α L R : ℝ} (hα : 0 < α)
    (tdP : CapTraceData Cp) {CP C₁ Cexp Ccap : ℝ} (hP : CapPoincare Cp CP)
    (hen : CapEntranceL2 Cp C₁) (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (hCexp : 0 ≤ Cexp)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hδ : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R)
    (hRc : R < capR0W Cp α tdP CP C₁ Cexp)
    (hBR : capLowerConstW Cp α tdP CP C₁ Cexp * R ≤ omega m * Cp.beta α)
    (hCcap : capLowerConstGen_bcm Cp α tdP CP C₁ Cexp ≤ Ccap)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    (Cp.beta α - Ccap * R)
          * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW Cp (transLift m R gs.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
            (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyR_gm α gs.nu hR hL (bdCapR_bg2 Cm Cp tdP L R hR hL) u := by
  have hkey := cap_lower_weak_p Cp hm (cap_theta_zero_nonneg_bg2 Cp)
    tdP hP hen hCexp hα.le (cap_beta_pos_bg2 m hm Cp hα).le
    (memLp_transLift_gm_bcw hR gs) (integral_transLift_sq_gm_bcw hR gs) rfl
    hdR hR hRc hδ hBR (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capRight_bg2 Cm Cp tdP hR hL gs.nu u,
    pCoefW_capRight_gen_gm_bcw hR hL gs u] at hkey
  have hle : capLowerConstW Cp α tdP CP C₁ Cexp / omega m ≤ Ccap :=
    le_trans (capLowerConstW_div_le_gen_bcm Cp α tdP CP C₁ Cexp) hCcap
  have hcoef : Cp.beta α - Ccap * R
      ≤ Cp.beta α - capLowerConstW Cp α tdP CP C₁ Cexp / omega m * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ((axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R)))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW Cp (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW Cp (transLift m R gs.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
          (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by ring
  rw [hdiv]
  linarith

theorem cap_mass_left_bg2 {m : ℕ} (Cm Cp : Cap m) {α L R : ℝ} (tdM : CapTraceData Cm)
    {CP C₁ Cexp Ccap : ℝ} (hP : CapPoincare Cm CP) (hen : CapEntranceL2 Cm C₁) (hR : 0 < R)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hCcap : capLowerConstGen_bcm Cm α tdM CP C₁ Cexp ≤ Ccap)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictLeft hR hL u)
      ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + Ccap * R * dirichletP (gPartW Cm (transLift m R gs.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
              (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p Cm hP hen (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl hdR hR.le (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capLeft_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capLeft_gen_gm_bcw hR hL gs u] at hkey
  have hleV : 8 * Cm.revolutionVolume / omega m ≤ Ccap :=
    le_trans (revolutionVolume_div_le_gen_bcm Cm α tdM CP C₁ Cexp) hCcap
  have hleP : 2 * capPoincareConstW Cm CP C₁ ≤ Ccap :=
    le_trans (poincareConstW_le_gen_bcm Cm α tdM CP C₁ Cexp) hCcap
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleV hR.le) (sq_nonneg ((axialRep_gm hR hL gs u).toFun 0))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleP hR.le)
    (dirichletP_nonneg (gPartW Cm (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

theorem cap_mass_right_bg2 {m : ℕ} (Cm Cp : Cap m) {α L R : ℝ} (tdP : CapTraceData Cp)
    {CP C₁ Cexp Ccap : ℝ} (hP : CapPoincare Cp CP) (hen : CapEntranceL2 Cp C₁) (hR : 0 < R)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hCcap : capLowerConstGen_bcm Cp α tdP CP C₁ Cexp ≤ Ccap)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictRight hR hL u)
      ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
        + Ccap * R * dirichletP (gPartW Cp (transLift m R gs.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
              (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p Cp hP hen (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl hdR hR.le (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capRight_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capRight_gen_gm_bcw hR hL gs u] at hkey
  have hleV : 8 * Cp.revolutionVolume / omega m ≤ Ccap :=
    le_trans (revolutionVolume_div_le_gen_bcm Cp α tdP CP C₁ Cexp) hCcap
  have hleP : 2 * capPoincareConstW Cp CP C₁ ≤ Ccap :=
    le_trans (poincareConstW_le_gen_bcm Cp α tdP CP C₁ Cexp) hCcap
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleV hR.le) (sq_nonneg ((axialRep_gm hR hL gs u).toFun
      (bulkLength Cm Cp L R)))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hleP hR.le)
    (dirichletP_nonneg (gPartW Cp (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

/-! ## 3. `CapLowerInput_gm` for an arbitrary pair of caps -/

set_option linter.unusedVariables false in
/-- **`lem:cap` in thin-domain scaling for the single-cap thin domain** `eq:single-cap`, for an
**arbitrary** pair of admissible caps `Cm Cp : Cap m` with abstract trace data `tdM`/`tdP`, for a
weak transverse ground state. The general-cap analogue of `capLowerInput_mixed_bcm`.

Unlike `capLowerInput_mixed_bcm` — which only takes a `CapPoincare` hypothesis for the flat cap,
since the hemisphere's Poincaré constant is obtained internally from `capPoincare_hemi_phg` —
here *both* caps are abstract, so both receive an explicit `CapPoincare` hypothesis
(`hPm`/`hPp`). -/
theorem capLowerInput_gen2_bg2 (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (α : ℝ) (hα : 0 < α)
    (L : ℝ) (hL0 : 0 < L) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    {C₁ C₁' CPm CPp Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (henM : CapEntranceL2 Cm C₁) (hPM : CapPoincare Cm CPm)
    (henP : CapEntranceL2 Cp C₁') (hPP : CapPoincare Cp CPp) :
    ∃ Ccap R₀ : ℝ, 0 ≤ Ccap ∧ 0 < R₀ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
        ∀ (hL : (Cm.K + Cp.K) * R < L)
          {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd),
          Real.sqrt (omega m) / 2
              ≤ (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y) →
          |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R →
          CapLowerInput_gm gs Ccap hR hL (bdCapL_bg2 Cm Cp tdM L R hR hL)
            (bdCapR_bg2 Cm Cp tdP L R hR hL) := by
  have hβM := cap_beta_pos_bg2 m hm Cm hα
  have hβP := cap_beta_pos_bg2 m hm Cp hα
  have hCcapM0 : 0 ≤ capLowerConstGen_bcm Cm α tdM CPm C₁ Cexp :=
    capLowerConstGen_nonneg_bcm Cm α tdM CPm C₁ Cexp
  have hCcapP0 : 0 ≤ capLowerConstGen_bcm Cp α tdP CPp C₁' Cexp :=
    capLowerConstGen_nonneg_bcm Cp α tdP CPp C₁' Cexp
  have hB0M : 0 ≤ capLowerConstW Cm α tdM CPm C₁ Cexp :=
    capLowerConstW_nonneg_gen_bcm hα.le tdM hPM.nonneg henM.nonneg hCexp
  have hB0P : 0 ≤ capLowerConstW Cp α tdP CPp C₁' Cexp :=
    capLowerConstW_nonneg_gen_bcm hα.le tdP hPP.nonneg henP.nonneg hCexp
  have hdenM : (0 : ℝ) < capLowerConstW Cm α tdM CPm C₁ Cexp + 1 := by linarith
  have hdenP : (0 : ℝ) < capLowerConstW Cp α tdP CPp C₁' Cexp + 1 := by linarith
  refine ⟨max (capLowerConstGen_bcm Cm α tdM CPm C₁ Cexp)
      (capLowerConstGen_bcm Cp α tdP CPp C₁' Cexp),
    min (min (capR0W Cm α tdM CPm C₁ Cexp) (capR0W Cp α tdP CPp C₁' Cexp))
      (min (omega m * Cm.beta α / (capLowerConstW Cm α tdM CPm C₁ Cexp + 1))
        (omega m * Cp.beta α / (capLowerConstW Cp α tdP CPp C₁' Cexp + 1))),
    le_trans hCcapM0 (le_max_left _ _),
    lt_min
      (lt_min (capR0W_pos Cm hα.le tdM hPM.nonneg henM.nonneg hCexp)
        (capR0W_pos Cp hα.le tdP hPP.nonneg henP.nonneg hCexp))
      (lt_min (div_pos (mul_pos (omega_pos m) hβM) hdenM)
        (div_pos (mul_pos (omega_pos m) hβP) hdenP)),
    fun R hR hR0 hL bd gs hdR hδ => ?_⟩
  have hRcM : R < capR0W Cm α tdM CPm C₁ Cexp :=
    lt_of_lt_of_le hR0 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hRcP : R < capR0W Cp α tdP CPp C₁' Cexp :=
    lt_of_lt_of_le hR0 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hRbM : R < omega m * Cm.beta α / (capLowerConstW Cm α tdM CPm C₁ Cexp + 1) :=
    lt_of_lt_of_le hR0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRbP : R < omega m * Cp.beta α / (capLowerConstW Cp α tdP CPp C₁' Cexp + 1) :=
    lt_of_lt_of_le hR0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hBRM : capLowerConstW Cm α tdM CPm C₁ Cexp * R ≤ omega m * Cm.beta α := by
    have h := (lt_div_iff₀ hdenM).1 hRbM
    nlinarith [hR.le, hB0M]
  have hBRP : capLowerConstW Cp α tdP CPp C₁' Cexp * R ≤ omega m * Cp.beta α := by
    have h := (lt_div_iff₀ hdenP).1 hRbP
    nlinarith [hR.le, hB0P]
  have hCcapMle : capLowerConstGen_bcm Cm α tdM CPm C₁ Cexp
      ≤ max (capLowerConstGen_bcm Cm α tdM CPm C₁ Cexp)
          (capLowerConstGen_bcm Cp α tdP CPp C₁' Cexp) :=
    le_max_left _ _
  have hCcapPle : capLowerConstGen_bcm Cp α tdP CPp C₁' Cexp
      ≤ max (capLowerConstGen_bcm Cm α tdM CPm C₁ Cexp)
          (capLowerConstGen_bcm Cp α tdP CPp C₁' Cexp) :=
    le_max_right _ _
  exact ⟨fun u => dirichletP (gPartW Cm (transLift m R gs.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP (gPartW Cp (transLift m R gs.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP_nonneg _, fun u => dirichletP_nonneg _,
    fun u => cap_lower_left_bg2 hm Cm Cp hα tdM hPM henM hR gs hCexp hdR hδ hRcM hBRM
      hCcapMle hL u,
    fun u => cap_lower_right_bg2 hm Cm Cp hα tdP hPP henP hR gs hCexp hdR hδ hRcP hBRP
      hCcapPle hL u,
    fun u => cap_mass_left_bg2 Cm Cp tdM hPM henM hR gs hdR hCcapMle hL u,
    fun u => cap_mass_right_bg2 Cm Cp tdP hPP henP hR gs hdR hCcapPle hL u⟩

end RobinCaps.ThinDomain

end
