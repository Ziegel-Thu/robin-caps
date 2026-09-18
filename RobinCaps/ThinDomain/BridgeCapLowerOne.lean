import RobinCaps.ThinDomain.BridgeInterfaceOne
import RobinCaps.ThinDomain.TrialOne
import RobinCaps.Cap.LowerWeak

/-!
# Discharging `CapLowerInput_a1` for two hemispherical caps (`m = 1`)

This file is the last bridge of the `m = 1` main theorem: it derives the interface
`RobinCaps.ThinDomain.CapLowerInput_a1` of `RobinCaps/ThinDomain/AssemblyOne.lean` (the
manuscript's `lem:cap` written in *thin-domain* scaling) from

* `RobinCaps/Cap/LowerWeak.lean` — `lem:cap` on the **fixed unit cap** for weak `H¹`
  functions (`cap_lower_weak_p`, `cap_mass_bound_weak_p`);
* `RobinCaps/ThinDomain/Restrict.lean` — the mass/energy scaling laws between the cap
  component `capLeft` on the unit cap and the restriction `restrictLeft` to the left cap of
  `Ω_R`;
* `RobinCaps/ThinDomain/InterfaceTrace.lean` — `entranceVal_capLeft`, the identification of
  the cap entrance trace with the interface trace of the thin domain;
* `RobinCaps/ThinDomain/BridgeInterfaceOne.lean` — `eq:interval-trace`, the endpoint values of
  the axial profile `axialRepOne_a1` as the pairings `⟨Tr u, ψ_R⟩`;
* `RobinCaps/ThinDomain/TrialOne.lean` — `transverseExpansionData_one`, `lem:transverse`.

## The remaining hypotheses

`capLowerInput_one_bc` is stated against four hypotheses, all of them about the **fixed** unit
hemisphere `𝒞 = (Cap.hemisphere 1).body`:

1. `td : CapTraceData (Cap.hemisphere 1)` — the `Γ`-trace interface of
   `RobinCaps/Cap/LowerWeak.lean` (built by even reflection in
   `RobinCaps/ThinDomain/Reflect.lean`);
2. `hP : CapPoincare (Cap.hemisphere 1) CP` — the Poincaré–Wirtinger inequality on the fixed
   cap (`RobinCaps/Cap/PoincareOne.lean`);
3. `hen : CapEntranceL2 (Cap.hemisphere 1) C₁` — the `L²(Σ)` trace theorem on the **entrance
   disk**;
4. `hmatch : CapTraceMatch_bc td L R (√R) hR hL` — the identification of the unit-cap
   `Γ`-form of the cap components with the cap pieces `bdCapL_a1` / `bdCapR_a1` of the
   `m = 1` vertical-trace density, with the factor `c²/R` (`= 1` at `c = √R`).

Only 4 is genuinely new; 1–3 are the three interfaces that `RobinCaps/Cap/LowerWeak.lean`
itself declares.  Hypothesis 3 could **not** be eliminated:

* `weighted_poincare_lw` — and hence `cap_lower_weak_p` and `cap_mass_bound_weak_p` — uses the
  entrance bound not only at `U` but at `U − t` for a Poincaré constant `t` produced inside the
  proof, so the per-element bounds of `RobinCaps/ThinDomain/InterfaceTrace.lean` would have to
  be available for the whole family `{capLeft u − t}`;
* more importantly, `CapEntranceL2.bound` controls `‖Tr_Σ U‖²_{L²(Σ)}` by the **cap-side**
  quantities `massP U + dirichletP U`, whereas `integral_entranceVal_sq_capLeft_le`
  (the interface trace through the bulk) controls it by the **bulk-side** quantities
  `∫_{Ω_b}|u|² + ∫_{Ω_b}|∂ₓu|²`.  Using the latter would destroy the cap/bulk split that
  `energy_split_a1` and `CapLowerInput_a1` rest on;
* the naive axial slicing on the half-ball gives the weight `1/√(1−|z|²)`, which is unbounded
  on `Σ`, so it does not prove `CapEntranceL2` either.  On a Lipschitz domain the bound is a
  genuine trace theorem, exactly like `CapTraceData.trace_ineq`, and is therefore left as an
  interface of the same kind.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-! ## 1. The scaling laws between `restrictLeft/Right` and `capLeft/Right`

With the manuscript normalisation `c² = R^m` the cap component `U = capLeft hR hL c u` on the
*unit* cap and the restriction `u|_{C_-}` to the left cap of `Ω_R` are related by

* `‖u‖²_{L²(C_-)} = R ‖U‖²_{L²(𝒞)}`,
* `‖∇u‖²_{L²(C_-)} = R⁻¹ ‖∇U‖²_{L²(𝒞)}`,

so that `R⁻¹‖∇U‖² − δ‖U‖²` on the unit cap is exactly `‖∇u‖² − (R δ)‖u‖²/R ...` — see
`capEnergyW_capLeft_bc` below for the precise statement. -/

section Scaling

variable {m : ℕ} {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- **`eq:cap-rescale`, mass, left cap.** -/
theorem massP_restrictLeft_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictLeft hR hL u) = R * massP (capLeft hR hL c u) := by
  rw [massP_capLeft_of_sq_eq hR hL hc u, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

/-- **`eq:cap-rescale`, Dirichlet energy, left cap.** -/
theorem dirichletP_restrictLeft_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP (restrictLeft hR hL u) = R⁻¹ * dirichletP (capLeft hR hL c u) := by
  rw [dirichletP_capLeft_of_sq_eq hR hL hc u, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

/-- **`eq:cap-rescale`, mass, right cap.** -/
theorem massP_restrictRight_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    massP (restrictRight hR hL u) = R * massP (capRight hR hL c u) := by
  rw [massP_capRight_of_sq_eq hR hL hc u, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

/-- **`eq:cap-rescale`, Dirichlet energy, right cap.** -/
theorem dirichletP_restrictRight_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP (restrictRight hR hL u) = R⁻¹ * dirichletP (capRight hR hL c u) := by
  rw [dirichletP_capRight_of_sq_eq hR hL hc u, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

/-- **`eq:interval-trace`, unscaled form, left cap.**  The entrance pairing of the cap
component against the lifted transverse ground state `Ψ_R = transLift m R ψ` is the
interface pairing `⟨Tr_{x_-} u, ψ_R⟩_{L²(B_m(R))}`, up to the factor `c R^{m/2} R^{-m}`. -/
theorem pCoefW_capLeft_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (ψ : TransH1 m R) (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cm (transLift m R ψ) (capLeft hR hL c u)
      = c * R ^ ((m : ℝ) / 2) * (R ^ m)⁻¹
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceL u z * ψ.toFun z := by
  have hRm : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  have h1 : pCoefW Cm (transLift m R ψ) (capLeft hR hL c u)
      = ∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          (c * R ^ ((m : ℝ) / 2)) * ((fun z => ifaceL u z * ψ.toFun z) (R • z')) := by
    rw [pCoefW]
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (entranceVal_capLeft hR hL c u)]
      with z' hz' hz'b
    rw [hz' hz'b, transLift]
    ring
  have h2 := integral_ball_smul_radius m (R := R) (ρ := 1) hR
    (fun z => ifaceL u z * ψ.toFun z)
  rw [mul_one] at h2
  rw [h1, integral_const_mul, h2]
  field_simp

/-- **`eq:interval-trace`, unscaled form, right cap.** -/
theorem pCoefW_capRight_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (ψ : TransH1 m R) (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cp (transLift m R ψ) (capRight hR hL c u)
      = c * R ^ ((m : ℝ) / 2) * (R ^ m)⁻¹
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceR u z * ψ.toFun z := by
  have hRm : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  have h1 : pCoefW Cp (transLift m R ψ) (capRight hR hL c u)
      = ∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          (c * R ^ ((m : ℝ) / 2)) * ((fun z => ifaceR u z * ψ.toFun z) (R • z')) := by
    rw [pCoefW]
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (entranceVal_capRight hR hL c u)]
      with z' hz' hz'b
    rw [hz' hz'b, transLift]
    ring
  have h2 := integral_ball_smul_radius m (R := R) (ρ := 1) hR
    (fun z => ifaceR u z * ψ.toFun z)
  rw [mul_one] at h2
  rw [h1, integral_const_mul, h2]
  field_simp

end Scaling

/-! ## 2. `m = 1` with the manuscript normalisation `c = √R` -/

section OneScaling

variable {Cm Cp : RobinCaps.Cap 1} {L R α : ℝ}

/-- The manuscript normalisation `c² = R^m` for `m = 1`. -/
theorem sqrt_sq_eq_bc (hR : 0 < R) : Real.sqrt R ^ 2 = R ^ (1 : ℕ) := by
  rw [Real.sq_sqrt hR.le, pow_one]

/-- **`eq:interval-trace` with the scaling factor computed**: for `c = √R` and `m = 1` the
entrance pairing `p_- = ⟨Tr_Σ U, Ψ_R⟩_{L²(Σ)}` of the left cap component *is* the left endpoint
value `F(x_-)` of the axial profile — the factor `c R^{m/2} R^{-m}` equals `1`. -/
theorem pCoefW_capLeft_one_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cm (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
        (capLeft hR hL (Real.sqrt R) u)
      = (axialRepOne_a1 hR hL hα u).toFun 0 := by
  have hψ : (Transverse.groundStateOneReg α R hα hR).psi = psiOne_a1 α R hα hR := rfl
  have h : Real.sqrt R * R ^ (((1 : ℕ) : ℝ) / 2) * (R ^ (1 : ℕ))⁻¹ = 1 := by
    rw [rpow_one_half_eq_sqrt R, pow_one, Real.mul_self_sqrt hR.le,
      mul_inv_cancel₀ hR.ne']
  rw [hψ, pCoefW_capLeft_bc hR hL (Real.sqrt R) (psiOne_a1 α R hα hR) u,
    axialRepOne_endpoint_left_bi hR hL hα u, h, one_mul]
  rfl

/-- **`eq:interval-trace`, right endpoint.** -/
theorem pCoefW_capRight_one_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cp (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
        (capRight hR hL (Real.sqrt R) u)
      = (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) := by
  have hψ : (Transverse.groundStateOneReg α R hα hR).psi = psiOne_a1 α R hα hR := rfl
  have h : Real.sqrt R * R ^ (((1 : ℕ) : ℝ) / 2) * (R ^ (1 : ℕ))⁻¹ = 1 := by
    rw [rpow_one_half_eq_sqrt R, pow_one, Real.mul_self_sqrt hR.le,
      mul_inv_cancel₀ hR.ne']
  rw [hψ, pCoefW_capRight_bc hR hL (Real.sqrt R) (psiOne_a1 α R hα hR) u,
    axialRepOne_endpoint_right_bi hR hL hα u, h, one_mul]
  rfl

/-- **The thin-domain cap mass is the scaled unit-cap mass** (left cap). -/
theorem capMassScaledW_capLeft_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ (1 : ℕ)) (u : H1P (thinDomain Cm Cp L R)) :
    capMassScaledW R (capLeft hR hL c u) = massP (restrictLeft hR hL u) := by
  rw [capMassScaledW, massP_capLeft_of_sq_eq hR hL hc u, ← mul_assoc,
    mul_inv_cancel₀ hR.ne', one_mul]

/-- **The thin-domain cap mass is the scaled unit-cap mass** (right cap). -/
theorem capMassScaledW_capRight_bc (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ (1 : ℕ)) (u : H1P (thinDomain Cm Cp L R)) :
    capMassScaledW R (capRight hR hL c u) = massP (restrictRight hR hL u) := by
  rw [capMassScaledW, massP_capRight_of_sq_eq hR hL hc u, ← mul_assoc,
    mul_inv_cancel₀ hR.ne', one_mul]

/-- **The unit-cap energy of the left cap component is the thin-domain left-cap energy.**

This is the exact bookkeeping of `lem:cap` in thin-domain scaling: with `c² = R^m` (`m = 1`),

`E_W[U] = R⁻¹‖∇U‖² + α ∫_Γ|Tr U|² − mα‖U‖² − δ‖U‖²`  at  `δ = R ν − m α`

equals `‖∇u‖²_{L²(C_-)} + α b_-(u) − ν ‖u‖²_{L²(C_-)} = E_cap^-[u]`, provided the unit-cap
`Γ`-form of `U` is the cap piece `bdCapL_a1` of the thin-domain boundary form, rescaled by
`c²/R` (the `ℋ^m`-scaling of the exposed boundary, `m = 1`). -/
theorem capEnergyW_capLeft_bc (td : CapTraceData Cm) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) {c : ℝ} (hc : c ^ 2 = R ^ (1 : ℕ)) (ν : ℝ)
    (u : H1P (thinDomain Cm Cp L R))
    (hmatch : td.bdΓ (capLeft hR hL c u) (capLeft hR hL c u)
      = c ^ 2 / R * bdCapL_a1 Cm Cp L R u) :
    capEnergyW Cm α td R (R * ν - ((1 : ℕ) : ℝ) * α) (capLeft hR hL c u)
      = capEnergyL_a1 α ν hR hL u := by
  have hR0 : R ≠ 0 := hR.ne'
  rw [capEnergyW, capJW, capEnergyL_a1, hmatch,
    dirichletP_capLeft_of_sq_eq hR hL hc u, massP_capLeft_of_sq_eq hR hL hc u, hc, pow_one,
    Nat.cast_one]
  field_simp
  ring

/-- **The unit-cap energy of the right cap component is the thin-domain right-cap energy.** -/
theorem capEnergyW_capRight_bc (td : CapTraceData Cp) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) {c : ℝ} (hc : c ^ 2 = R ^ (1 : ℕ)) (ν : ℝ)
    (u : H1P (thinDomain Cm Cp L R))
    (hmatch : td.bdΓ (capRight hR hL c u) (capRight hR hL c u)
      = c ^ 2 / R * bdCapR_a1 Cm Cp L R u) :
    capEnergyW Cp α td R (R * ν - ((1 : ℕ) : ℝ) * α) (capRight hR hL c u)
      = capEnergyR_a1 α ν hR hL u := by
  have hR0 : R ≠ 0 := hR.ne'
  rw [capEnergyW, capJW, capEnergyR_a1, hmatch,
    dirichletP_capRight_of_sq_eq hR hL hc u, massP_capRight_of_sq_eq hR hL hc u, hc, pow_one,
    Nat.cast_one]
  field_simp
  ring

end OneScaling

/-! ## 3. The identification hypothesis

The one analytic fact left to a later file: the unit-cap `Γ`-trace form of a cap component is
(after the revolution-area rescaling) the cap piece of the vertical-trace density of
`RobinCaps/ThinDomain/TraceOne.lean`.  The factor is dictated by the two scalings involved:
the amplitude of `capLeft hR hL c u` is `c`, so the *squared* trace scales by `c²`, while the
`m`-dimensional surface measure `ℋ^m` of the exposed boundary scales by `R^m` when the unit cap
is blown up to the end cap of `Ω_R`; for `m = 1` this gives the factor `c²/R`, which is `1` at
the manuscript normalisation `c = √R`.

To be supplied from `RobinCaps/ThinDomain/Reflect.lean` (which builds a `CapTraceData` for the
hemisphere by even reflection), `RobinCaps/ThinDomain/BridgeRadial.lean` and
`RobinCaps/ThinDomain/VertRadIdent.lean`. -/

/-- **The trace-identification interface.**  `td.bdΓ` on the cap components of `u` is the
left/right cap piece of the `m = 1` boundary form of `Ω_R`, rescaled by `c²/R`. -/
def CapTraceMatch_bc (td : CapTraceData (Cap.hemisphere 1)) (L R c : ℝ) (hR : 0 < R)
    (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L) : Prop :=
  (∀ u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R),
      td.bdΓ (capLeft hR hL c u) (capLeft hR hL c u)
        = c ^ 2 / R * bdCapL_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R u)
    ∧ (∀ u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R),
      td.bdΓ (capRight hR hL c u) (capRight hR hL c u)
        = c ^ 2 / R * bdCapR_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R u)

/-! ## 4. The constant of `lem:cap` in thin-domain scaling -/

/-- The constant `C` of `CapLowerInput_a1`: it dominates the three constants produced by
`cap_lower_weak_p` and `cap_mass_bound_weak_p`. -/
def capLowerConst_bc (α : ℝ) (td : CapTraceData (Cap.hemisphere 1)) (CP C₁ Cexp : ℝ) : ℝ :=
  max (max (capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp / omega 1)
        (8 * (Cap.hemisphere 1).revolutionVolume / omega 1))
    (2 * capPoincareConstW (Cap.hemisphere 1) CP C₁)

theorem capLowerConst_nonneg_bc (α : ℝ) (td : CapTraceData (Cap.hemisphere 1))
    (CP C₁ Cexp : ℝ) : 0 ≤ capLowerConst_bc α td CP C₁ Cexp := by
  refine le_trans (le_trans ?_ (le_max_right _ _)) (le_max_left _ _)
  have : (0 : ℝ) ≤ 8 * (Cap.hemisphere 1).revolutionVolume :=
    mul_nonneg (by norm_num) (revolutionVolume_nonneg_lw _)
  exact div_nonneg this (omega_pos 1).le

theorem capLowerConstW_div_le_bc (α : ℝ) (td : CapTraceData (Cap.hemisphere 1))
    (CP C₁ Cexp : ℝ) :
    capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp / omega 1
      ≤ capLowerConst_bc α td CP C₁ Cexp :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem revolutionVolume_div_le_bc (α : ℝ) (td : CapTraceData (Cap.hemisphere 1))
    (CP C₁ Cexp : ℝ) :
    8 * (Cap.hemisphere 1).revolutionVolume / omega 1 ≤ capLowerConst_bc α td CP C₁ Cexp :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem poincareConstW_le_bc (α : ℝ) (td : CapTraceData (Cap.hemisphere 1))
    (CP C₁ Cexp : ℝ) :
    2 * capPoincareConstW (Cap.hemisphere 1) CP C₁ ≤ capLowerConst_bc α td CP C₁ Cexp :=
  le_max_right _ _

/-! ## 5. `lem:cap` at a single admissible radius -/

section Single

variable {α L R : ℝ}

theorem hemisphere_theta_zero_nonneg_bc : 0 ≤ (Cap.hemisphere 1).θ 0 :=
  le_of_eq (hemisphere_theta_zero_one 1).symm

/-- **`eq:cap-lower` for the left cap component, in thin-domain scaling.** -/
theorem cap_lower_left_bc (hα : 0 < α) (td : CapTraceData (Cap.hemisphere 1))
    {CP C₁ Cexp : ℝ} (hP : CapPoincare (Cap.hemisphere 1) CP)
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁) (hR : 0 < R)
    (ted : TransverseExpansionData 1 α R (Transverse.groundStateOneReg α R hα hR) Cexp)
    (hRc : R < capR0W (Cap.hemisphere 1) α td CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp * R
      ≤ omega 1 * (Cap.hemisphere 1).beta α)
    (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L)
    (hmatch : CapTraceMatch_bc td L R (Real.sqrt R) hR hL)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    ((Cap.hemisphere 1).beta α - capLowerConst_bc α td CP C₁ Cexp * R)
          * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere 1)
            (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
              transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
            (capLeft hR hL (Real.sqrt R) u))
      ≤ capEnergyL_a1 α (nuR α R hα hR) hR hL u := by
  have hkey := cap_lower_weak_p (Cap.hemisphere 1) le_rfl hemisphere_theta_zero_nonneg_bc td
    hP hen (Cexp_nonneg_lw ted hR) hα.le (hemisphere_beta_pos 1 le_rfl hα).le
    (memLp_transLift_lw (Transverse.groundStateOneReg α R hα hR))
    (integral_transLift_sq hR (Transverse.groundStateOneReg α R hα hR)) rfl ted.dR_ge
    hR hRc (abs_delta_le_lw ted hR) hBR (capLeft hR hL (Real.sqrt R) u)
  rw [capEnergyW_capLeft_bc td hR hL (sqrt_sq_eq_bc hR)
      (Transverse.groundStateOneReg α R hα hR).nu u (hmatch.1 u),
    pCoefW_capLeft_one_bc hR hL hα u, Transverse.groundStateOneReg_nu] at hkey
  have hle : capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp / omega 1
      ≤ capLowerConst_bc α td CP C₁ Cexp := capLowerConstW_div_le_bc α td CP C₁ Cexp
  have hcoef : (Cap.hemisphere 1).beta α - capLowerConst_bc α td CP C₁ Cexp * R
      ≤ (Cap.hemisphere 1).beta α
        - capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp / omega 1 * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ((axialRepOne_a1 hR hL hα u).toFun 0))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere 1)
      (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
      (capLeft hR hL (Real.sqrt R) u))
      = dirichletP (gPartW (Cap.hemisphere 1)
          (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
            transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
          (capLeft hR hL (Real.sqrt R) u)) / (2 * R) := by
    ring
  rw [hdiv]
  linarith

/-- **`eq:cap-lower` for the right cap component, in thin-domain scaling.** -/
theorem cap_lower_right_bc (hα : 0 < α) (td : CapTraceData (Cap.hemisphere 1))
    {CP C₁ Cexp : ℝ} (hP : CapPoincare (Cap.hemisphere 1) CP)
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁) (hR : 0 < R)
    (ted : TransverseExpansionData 1 α R (Transverse.groundStateOneReg α R hα hR) Cexp)
    (hRc : R < capR0W (Cap.hemisphere 1) α td CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp * R
      ≤ omega 1 * (Cap.hemisphere 1).beta α)
    (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L)
    (hmatch : CapTraceMatch_bc td L R (Real.sqrt R) hR hL)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    ((Cap.hemisphere 1).beta α - capLowerConst_bc α td CP C₁ Cexp * R)
          * (axialRepOne_a1 hR hL hα u).toFun
              (bulkLength (Cap.hemisphere 1) (Cap.hemisphere 1) L R) ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere 1)
            (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
              transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
            (capRight hR hL (Real.sqrt R) u))
      ≤ capEnergyR_a1 α (nuR α R hα hR) hR hL u := by
  have hkey := cap_lower_weak_p (Cap.hemisphere 1) le_rfl hemisphere_theta_zero_nonneg_bc td
    hP hen (Cexp_nonneg_lw ted hR) hα.le (hemisphere_beta_pos 1 le_rfl hα).le
    (memLp_transLift_lw (Transverse.groundStateOneReg α R hα hR))
    (integral_transLift_sq hR (Transverse.groundStateOneReg α R hα hR)) rfl ted.dR_ge
    hR hRc (abs_delta_le_lw ted hR) hBR (capRight hR hL (Real.sqrt R) u)
  rw [capEnergyW_capRight_bc td hR hL (sqrt_sq_eq_bc hR)
      (Transverse.groundStateOneReg α R hα hR).nu u (hmatch.2 u),
    pCoefW_capRight_one_bc hR hL hα u, Transverse.groundStateOneReg_nu] at hkey
  have hle : capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp / omega 1
      ≤ capLowerConst_bc α td CP C₁ Cexp := capLowerConstW_div_le_bc α td CP C₁ Cexp
  have hcoef : (Cap.hemisphere 1).beta α - capLowerConst_bc α td CP C₁ Cexp * R
      ≤ (Cap.hemisphere 1).beta α
        - capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp / omega 1 * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ((axialRepOne_a1 hR hL hα u).toFun
      (bulkLength (Cap.hemisphere 1) (Cap.hemisphere 1) L R)))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere 1)
      (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
      (capRight hR hL (Real.sqrt R) u))
      = dirichletP (gPartW (Cap.hemisphere 1)
          (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
            transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
          (capRight hR hL (Real.sqrt R) u)) / (2 * R) := by
    ring
  rw [hdiv]
  linarith


/-- **`eq:cap-mass-bound` for the left cap component, in thin-domain scaling.** -/
theorem cap_mass_left_bc (hα : 0 < α) (td : CapTraceData (Cap.hemisphere 1))
    {CP C₁ Cexp : ℝ} (hP : CapPoincare (Cap.hemisphere 1) CP)
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁) (hR : 0 < R)
    (ted : TransverseExpansionData 1 α R (Transverse.groundStateOneReg α R hα hR) Cexp)
    (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    massP (restrictLeft hR hL u)
      ≤ capLowerConst_bc α td CP C₁ Cexp * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
        + capLowerConst_bc α td CP C₁ Cexp * R * dirichletP (gPartW (Cap.hemisphere 1)
            (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
              transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
            (capLeft hR hL (Real.sqrt R) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.hemisphere 1) hP hen
    (memLp_transLift_lw (Transverse.groundStateOneReg α R hα hR))
    (integral_transLift_sq hR (Transverse.groundStateOneReg α R hα hR)) rfl ted.dR_ge
    hR.le (capLeft hR hL (Real.sqrt R) u)
  rw [capMassScaledW_capLeft_bc hR hL (sqrt_sq_eq_bc hR) u,
    pCoefW_capLeft_one_bc hR hL hα u] at hkey
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (revolutionVolume_div_le_bc α td CP C₁ Cexp) hR.le)
    (sq_nonneg ((axialRepOne_a1 hR hL hα u).toFun 0))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (poincareConstW_le_bc α td CP C₁ Cexp) hR.le)
    (dirichletP_nonneg (gPartW (Cap.hemisphere 1)
      (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
      (capLeft hR hL (Real.sqrt R) u)))
  linarith

/-- **`eq:cap-mass-bound` for the right cap component, in thin-domain scaling.** -/
theorem cap_mass_right_bc (hα : 0 < α) (td : CapTraceData (Cap.hemisphere 1))
    {CP C₁ Cexp : ℝ} (hP : CapPoincare (Cap.hemisphere 1) CP)
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁) (hR : 0 < R)
    (ted : TransverseExpansionData 1 α R (Transverse.groundStateOneReg α R hα hR) Cexp)
    (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    massP (restrictRight hR hL u)
      ≤ capLowerConst_bc α td CP C₁ Cexp * R * (axialRepOne_a1 hR hL hα u).toFun
            (bulkLength (Cap.hemisphere 1) (Cap.hemisphere 1) L R) ^ 2
        + capLowerConst_bc α td CP C₁ Cexp * R * dirichletP (gPartW (Cap.hemisphere 1)
            (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
              transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
            (capRight hR hL (Real.sqrt R) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.hemisphere 1) hP hen
    (memLp_transLift_lw (Transverse.groundStateOneReg α R hα hR))
    (integral_transLift_sq hR (Transverse.groundStateOneReg α R hα hR)) rfl ted.dR_ge
    hR.le (capRight hR hL (Real.sqrt R) u)
  rw [capMassScaledW_capRight_bc hR hL (sqrt_sq_eq_bc hR) u,
    pCoefW_capRight_one_bc hR hL hα u] at hkey
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (revolutionVolume_div_le_bc α td CP C₁ Cexp) hR.le)
    (sq_nonneg ((axialRepOne_a1 hR hL hα u).toFun
      (bulkLength (Cap.hemisphere 1) (Cap.hemisphere 1) L R)))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (poincareConstW_le_bc α td CP C₁ Cexp) hR.le)
    (dirichletP_nonneg (gPartW (Cap.hemisphere 1)
      (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
      (capRight hR hL (Real.sqrt R) u)))
  linarith

end Single


/-! ## 6. `CapLowerInput_a1` for two hemispherical caps -/

/-- `capLowerConstW ≥ 0`. -/
theorem capLowerConstW_nonneg_bc {α : ℝ} (hα : 0 ≤ α) (td : CapTraceData (Cap.hemisphere 1))
    {CP C₁ Cexp : ℝ} (hCP : 0 ≤ CP) (hC₁ : 0 ≤ C₁) (hCexp : 0 ≤ Cexp) :
    0 ≤ capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp := by
  have hA0 := (capConstW_ge (Cap.hemisphere 1) hα td hCP hC₁ hCexp).1
  rw [capLowerConstW]
  nlinarith [sq_nonneg (capConstW (Cap.hemisphere 1) α td CP C₁ Cexp),
    sq_nonneg (capConstW (Cap.hemisphere 1) α td CP C₁ Cexp
      + capConstW (Cap.hemisphere 1) α td CP C₁ Cexp ^ 2)]

set_option linter.unusedVariables false in
/-- **`lem:cap` in thin-domain scaling for two hemispherical caps** — the interface
`RobinCaps.ThinDomain.CapLowerInput_a1` of `RobinCaps/ThinDomain/AssemblyOne.lean`, discharged
from the unit-cap weak lower bound of `RobinCaps/Cap/LowerWeak.lean`.

The remaining hypotheses are exactly the three analytic interfaces that mathlib `v4.26.0` does
not provide, all of them about the **fixed** unit hemisphere:

* `td : CapTraceData (Cap.hemisphere 1)` — the trace operator on the exposed boundary `Γ`
  (built by even reflection in `RobinCaps/ThinDomain/Reflect.lean`);
* `hP : CapPoincare (Cap.hemisphere 1) CP` — the Poincaré–Wirtinger inequality on the fixed cap
  (`RobinCaps/Cap/PoincareOne.lean`);
* `hen : CapEntranceL2 (Cap.hemisphere 1) C₁` — the `L²` trace theorem on the entrance disk;

together with the identification `hmatch` of the unit-cap `Γ`-form with the cap piece of the
`m = 1` vertical-trace density, with the factor `c²/R = 1` at `c = √R`.

The constant is `capLowerConst_bc` and the threshold is the minimum of the three explicit
thresholds: the `lem:transverse` expansion radius, `capR0W` of `lem:cap` on the unit cap, and
`ω₁ β(𝒞) / (C' + 1)` (which makes `C' R ≤ ω₁ β(𝒞)`, the hypothesis `hBR` of
`cap_lower_weak_p`). -/
theorem capLowerInput_one_bc (α : ℝ) (hα : 0 < α) (L : ℝ) (hL0 : 0 < L)
    (td : CapTraceData (Cap.hemisphere 1)) (CP C₁ : ℝ)
    (hP : CapPoincare (Cap.hemisphere 1) CP)
    (hen : CapEntranceL2 (Cap.hemisphere 1) C₁)
    (hmatch : ∀ (R : ℝ) (hR : 0 < R)
      (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L),
      CapTraceMatch_bc td L R (Real.sqrt R) hR hL) :
    ∃ Ccap R₀ : ℝ, 0 ≤ Ccap ∧ 0 < R₀ ∧
      CapLowerInput_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L α hα Ccap R₀ := by
  obtain ⟨Cexp, R₀e, hR₀e, hR₀e1, hted⟩ := transverseExpansionData_one α hα
  have hCexp0 : 0 ≤ Cexp :=
    Cexp_nonneg_lw (hted (R₀e / 2) (by linarith) (by linarith)) (by linarith)
  have hβ := hemisphere_beta_pos 1 le_rfl hα
  have hB0 : 0 ≤ capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp :=
    capLowerConstW_nonneg_bc hα.le td hP.nonneg hen.nonneg hCexp0
  have hden : (0 : ℝ) < capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp + 1 := by linarith
  refine ⟨capLowerConst_bc α td CP C₁ Cexp,
    min (min R₀e (capR0W (Cap.hemisphere 1) α td CP C₁ Cexp))
      (omega 1 * (Cap.hemisphere 1).beta α
        / (capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp + 1)),
    capLowerConst_nonneg_bc α td CP C₁ Cexp,
    lt_min (lt_min hR₀e
      (capR0W_pos (Cap.hemisphere 1) hα.le td hP.nonneg hen.nonneg hCexp0))
      (div_pos (mul_pos (omega_pos 1) hβ) hden),
    ⟨fun R hR hR0 hL => ?_⟩⟩
  have hRe : R < R₀e := lt_of_lt_of_le hR0 ((min_le_left _ _).trans (min_le_left _ _))
  have hRc : R < capR0W (Cap.hemisphere 1) α td CP C₁ Cexp :=
    lt_of_lt_of_le hR0 ((min_le_left _ _).trans (min_le_right _ _))
  have hRb : R < omega 1 * (Cap.hemisphere 1).beta α
      / (capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp + 1) :=
    lt_of_lt_of_le hR0 (min_le_right _ _)
  have ted := hted R hR hRe
  have hBR : capLowerConstW (Cap.hemisphere 1) α td CP C₁ Cexp * R
      ≤ omega 1 * (Cap.hemisphere 1).beta α := by
    have h := (lt_div_iff₀ hden).1 hRb
    nlinarith [hR.le, hB0]
  exact ⟨fun u => dirichletP (gPartW (Cap.hemisphere 1)
        (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
          transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
        (capLeft hR hL (Real.sqrt R) u)),
    fun u => dirichletP (gPartW (Cap.hemisphere 1)
        (transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
          transLift 1 R (Transverse.groundStateOneReg α R hα hR).psi y)
        (capRight hR hL (Real.sqrt R) u)),
    fun u => dirichletP_nonneg _, fun u => dirichletP_nonneg _,
    fun u => cap_lower_left_bc hα td hP hen hR ted hRc hBR hL (hmatch R hR hL) u,
    fun u => cap_lower_right_bc hα td hP hen hR ted hRc hBR hL (hmatch R hR hL) u,
    fun u => cap_mass_left_bc hα td hP hen hR ted hL u,
    fun u => cap_mass_right_bc hα td hP hen hR ted hL u⟩

end RobinCaps.ThinDomain

end
