import RobinCaps.ThinDomain.BridgeCapLowerGen
import RobinCaps.ThinDomain.AssemblyGen
import RobinCaps.ThinDomain.BridgeInterfaceGen

/-!
# The weak-ground-state variant of `BridgeCapLowerGen.lean`

See the task docstring in the coordinator's instructions. This file re-derives `lem:cap` in
thin-domain scaling for the two hemispherical caps, for an arbitrary **weak** transverse ground
state `gs : TransverseGroundState m α R bd` (no `C¹` regularity), replacing the single expansion
fact `TransverseExpansionData m α R gsr Cexp` that `BridgeCapLowerGen.lean` uses by an explicit
hypothesis bundle.

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

/-! ## 0. A `MemLp` transfer lemma under scaling by a Haar measure -/

section MemLpSmul

/-- **`MemLp` is preserved under precomposition with `y ↦ R • y`** (`R ≠ 0`), for an additive
Haar measure. The companion fact for `Integrable` is `Integrable.comp_smul`
(`Mathlib.MeasureTheory.Measure.Haar.NormedSpace`); this is the analogue for `MemLp`, obtained the
same way via `Measure.map_addHaar_smul` and `MemLp.comp_of_map`. -/
theorem memLp_comp_smul_bcw {m : ℕ} {R : ℝ} (hR : 0 < R)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : MemLp g 2 volume) :
    MemLp (fun y => g (R • y)) 2 volume := by
  have hmap : Measure.map (fun y : EuclideanSpace ℝ (Fin m) => R • y) volume
      = ENNReal.ofReal (R ^ m)⁻¹ • volume := by
    have h := Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin m))) hR.ne'
    rwa [finrank_euclideanSpace_fin,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (R ^ m)⁻¹)] at h
  have hg' : MemLp g 2 (Measure.map (fun y : EuclideanSpace ℝ (Fin m) => R • y) volume) := by
    rw [hmap]; exact hg.smul_measure ENNReal.ofReal_ne_top
  exact hg'.comp_of_map (by fun_prop)

end MemLpSmul

/-! ## 1. `Ψ_R` for a weak ground state: `MemLp` and normalization

The general-`m` copies of `RobinCaps.Cap.LowerWeak.memLp_transLift_lw` and
`RobinCaps.ThinDomain.TrialBound.integral_transLift_sq`, for a weak `gs : TransverseGroundState`
instead of a `TransverseGroundStateReg gsr`.  The normalisation proof is *verbatim* the `gsr`
proof (it never uses `gsr`'s regularity fields, only `gsr.psi`/`gsr.normalized`); the `MemLp`
proof cannot reuse continuity/boundedness (`gs.psi` has no regularity), so it goes through
`gs.psi.memL2` and the scaling lemma `memLp_comp_smul_bcw` instead. -/

section TransLiftWeak

variable {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **`Ψ_R ∈ L²(B_m(1))`, for a weak ground state.** -/
theorem memLp_transLift_gm_bcw (hR : 0 < R) (gs : TransverseGroundState m α R bd) :
    MemLp (transLift m R gs.psi) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  set g : EuclideanSpace ℝ (Fin m) → ℝ :=
    (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator gs.psi.toFun with hgdef
  have hg : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).2 gs.psi.memL2
  have hcomp : MemLp (fun y => g (R • y)) 2 volume := memLp_comp_smul_bcw hR hg
  have hind : (ball (0 : EuclideanSpace ℝ (Fin m)) 1).indicator (transLift m R gs.psi)
      = fun y => R ^ ((m : ℝ) / 2) * g (R • y) := by
    funext y
    by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin m)) 1
    · have hRy : R • y ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R := by
        rw [mem_ball_zero_iff] at hy ⊢
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
        nlinarith [hy]
      rw [Set.indicator_of_mem hy, hgdef, Set.indicator_of_mem hRy]
      rfl
    · have hRy : R • y ∉ ball (0 : EuclideanSpace ℝ (Fin m)) R := by
        rw [mem_ball_zero_iff] at hy
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
        intro hcon
        exact hy (by nlinarith [norm_nonneg y])
      rw [Set.indicator_of_notMem hy, hgdef, Set.indicator_of_notMem hRy]
      ring
  rw [← memLp_indicator_iff_restrict measurableSet_ball, hind]
  simpa [smul_eq_mul] using hcomp.const_smul (R ^ ((m : ℝ) / 2))

/-- **`‖Ψ_R‖_{L²(B_m(1))} = 1`, for a weak ground state.**  Verbatim copy of
`RobinCaps.ThinDomain.integral_transLift_sq`: that proof never uses `gsr`'s regularity fields,
only `gsr.psi`/`gsr.normalized`. -/
theorem integral_transLift_sq_gm_bcw (hR : 0 < R) (gs : TransverseGroundState m α R bd) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y ^ 2) = 1 := by
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR
    (fun z => gs.psi.toFun z ^ 2)
  rw [mul_one] at h
  have h2 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y ^ 2)
      = R ^ m * ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, gs.psi.toFun (R • y) ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball fun y _ => transLift_sq m hR gs.psi y
  rw [h2, ← h]
  exact gs.normalized

end TransLiftWeak

/-! ## 2. The axial profile representative for a weak ground state

`RobinCaps.ThinDomain.AssemblyGen` already defines `axialRep_gm` for a weak `gs`, built from
`bulkRepT`; `RobinCaps.ThinDomain.BridgeInterfaceGen` independently builds `axialRep_big` for the
same `gs`, from `profileRep_pe`, and proves its endpoint values
(`axialRep_endpoint_left_big`/`_right_big`).  Since `profileRep_pe u hR hL hψ hψ1` unfolds to
*exactly* `bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top hψ
hψ1 (restrictBulkP hR u)` and `gs_normalized_big gs` unfolds to `psi_normalized_integral gs`, the
two representatives are definitionally equal — so the endpoint theorems of `BridgeInterfaceGen`
transfer to `axialRep_gm` for free, and none of the `axialRep_gm`/`bulkProjThin_mk_gm` machinery
of `AssemblyGen` needs to be redone here. -/

section AxialWeak

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

theorem axialRep_big_eq_gm_bcw (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    axialRep_big hR hL gs u = axialRep_gm hR hL gs u := rfl

/-- **`eq:interval-trace`, left endpoint, for `axialRep_gm`.** -/
theorem axialRep_endpoint_left_gm_bcw (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_gm hR hL gs u).toFun 0
      = ∫ z in transverseBall m R, ifaceL u z * gs.psi.toFun z := by
  rw [← axialRep_big_eq_gm_bcw hR hL gs u]
  exact axialRep_endpoint_left_big hR hL gs u

/-- **`eq:interval-trace`, right endpoint, for `axialRep_gm`.** -/
theorem axialRep_endpoint_right_gm_bcw (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R)
      = ∫ z in transverseBall m R, ifaceR u z * gs.psi.toFun z := by
  rw [← axialRep_big_eq_gm_bcw hR hL gs u]
  exact axialRep_endpoint_right_big hR hL gs u

end AxialWeak

/-! ## 3. The scaling identities at `c = R^{m/2}`, for a weak ground state

The general-`m` copies of `pCoefW_capLeft_gen_bcg`/`pCoefW_capRight_gen_bcg`, replacing
`axialRep_bcg`/`gsr` by `axialRep_gm`/`gs`. -/

section GenScalingWeak

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

theorem pCoefW_capLeft_gen_gm_bcw (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cm (transLift m R gs.psi) (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
      = (axialRep_gm hR hL gs u).toFun 0 := by
  have hsq : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) = R ^ m := by
    have h := sq_rpow_half m hR; rwa [sq] at h
  have h : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) * (R ^ m)⁻¹ = 1 := by
    rw [hsq, mul_inv_cancel₀ (pow_pos hR m).ne']
  rw [pCoefW_capLeft_bc hR hL (R ^ ((m : ℝ) / 2)) gs.psi u, h, one_mul,
    axialRep_endpoint_left_gm_bcw hR hL gs u]
  rfl

theorem pCoefW_capRight_gen_gm_bcw (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cp (transLift m R gs.psi) (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
      = (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) := by
  have hsq : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) = R ^ m := by
    have h := sq_rpow_half m hR; rwa [sq] at h
  have h : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) * (R ^ m)⁻¹ = 1 := by
    rw [hsq, mul_inv_cancel₀ (pow_pos hR m).ne']
  rw [pCoefW_capRight_bc hR hL (R ^ ((m : ℝ) / 2)) gs.psi u, h, one_mul,
    axialRep_endpoint_right_gm_bcw hR hL gs u]
  rfl

/-- `capEnergyL_gm` (`AssemblyGen.lean`) and `capEnergyL_bcg` (`BridgeCapLowerGen.lean`) are the
same definition under different names. -/
theorem capEnergyL_gm_eq_bcg_bcw {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} (ν : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (bdCapL : H1P (thinDomain Cm Cp L R) → ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    capEnergyL_gm α ν hR hL bdCapL u = capEnergyL_bcg α ν hR hL bdCapL u := rfl

/-- `capEnergyR_gm` and `capEnergyR_bcg` are the same definition under different names. -/
theorem capEnergyR_gm_eq_bcg_bcw {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} (ν : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (bdCapR : H1P (thinDomain Cm Cp L R) → ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    capEnergyR_gm α ν hR hL bdCapR u = capEnergyR_bcg α ν hR hL bdCapR u := rfl

end GenScalingWeak

/-! ## 4. `lem:cap` at a single admissible radius, for a weak ground state

The general-`m` copies of `cap_lower_left_bcg`/`cap_lower_right_bcg`/`cap_mass_left_bcg`/
`cap_mass_right_bcg`, for `gs : TransverseGroundState m α R bd` in place of
`gsr : TransverseGroundStateReg m α R bd` and `ted : TransverseExpansionData m α R gsr Cexp`.

`TransverseExpansionData` bundles *four* facts about `gsr`: `psiH1`, `dR_close`, `dR_ge`,
`nuExp` (plus `bdSphere`).  `cap_mass_left_bcg`/`cap_mass_right_bcg` only ever use `dR_ge`
(via `ted.dR_ge`), so their weak copies below take only the explicit hypothesis `hdR` in its
place, exactly as the task instructions anticipate.

`cap_lower_left_bcg`/`cap_lower_right_bcg`, however, *also* use `nuExp` — indirectly, through
`Cexp_nonneg_lw ted hR : 0 ≤ Cexp` and `abs_delta_le_lw ted hR : |R * gsr.nu - m * α| ≤ Cexp * R`
— to control the "Robin-eigenvalue deviation" `δ_R = R ν_R − m α` that the underlying
`cap_lower_weak_p` needs bounded by `Cexp * R`.  This bound is a genuine, separate fact about
`nu`: unlike `dR_ge`, it is *not* derivable from `TransverseGroundState`'s bare structure
(`bdSymm`, `bdNonneg`, `weak_eq`, `gap`, `normalized`) alone, since `nu = qB α bd gs.psi` and `bd`
is otherwise unconstrained by that structure. (For instance the structure only forces `qB α bd v
≥ nu * NB v` for every `v`, a *lower* bound on the family of Rayleigh quotients, not an upper
bound on `nu` itself.) So the weak copies below keep `Cexp` and take the two facts
`hCexp : 0 ≤ Cexp` and `hδ : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R` as explicit hypotheses, in
place of `Cexp_nonneg_lw ted hR` / `abs_delta_le_lw ted hR`. -/

section SingleWeak

variable {m : ℕ} (hm : 1 ≤ m) {α L R : ℝ}

theorem cap_lower_left_gm_bcw (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (hCexp : 0 ≤ Cexp)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hδ : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R)
    (hRc : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    ((Cap.hemisphere m).beta α - capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R)
          * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
            (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyL_gm α gs.nu hR hL (bdCapL_bcg hm L R hR hL) u := by
  rw [capEnergyL_gm_eq_bcg_bcw]
  have hkey := cap_lower_weak_p (Cap.hemisphere m) hm hemisphere_theta_zero_nonneg_bcg
    (capTraceDataHemi_th m hm) hP hen hCexp hα.le
    (hemisphere_beta_pos m hm hα).le (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl
    hdR hR hRc hδ hBR (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capLeft_bcg hm hR hL gs.nu u, pCoefW_capLeft_gen_gm_bcw hR hL gs u] at hkey
  have hle : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp / omega m
      ≤ capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp :=
    capLowerConstW_div_le_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp
  have hcoef : (Cap.hemisphere m).beta α
        - capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ (Cap.hemisphere m).beta α
        - capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp / omega m
          * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ((axialRep_gm hR hL gs u).toFun 0))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
          (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by
    ring
  rw [hdiv]
  linarith

theorem cap_lower_right_gm_bcw (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (hCexp : 0 ≤ Cexp)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hδ : |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R)
    (hRc : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    ((Cap.hemisphere m).beta α - capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R)
          * (axialRep_gm hR hL gs u).toFun
              (bulkLength (Cap.hemisphere m) (Cap.hemisphere m) L R) ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
            (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyR_gm α gs.nu hR hL (bdCapR_bcg hm L R hR hL) u := by
  rw [capEnergyR_gm_eq_bcg_bcw]
  have hkey := cap_lower_weak_p (Cap.hemisphere m) hm hemisphere_theta_zero_nonneg_bcg
    (capTraceDataHemi_th m hm) hP hen hCexp hα.le
    (hemisphere_beta_pos m hm hα).le (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl
    hdR hR hRc hδ hBR (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capRight_bcg hm hR hL gs.nu u, pCoefW_capRight_gen_gm_bcw hR hL gs u] at hkey
  have hle : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp / omega m
      ≤ capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp :=
    capLowerConstW_div_le_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp
  have hcoef : (Cap.hemisphere m).beta α
        - capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ (Cap.hemisphere m).beta α
        - capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp / omega m
          * R := by
    have := mul_le_mul_of_nonneg_right hle hR.le
    linarith
  have hstep := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ((axialRep_gm hR hL gs u).toFun (bulkLength (Cap.hemisphere m)
      (Cap.hemisphere m) L R)))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
          (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by
    ring
  rw [hdiv]
  linarith

theorem cap_mass_left_gm_bcw (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    massP (restrictLeft hR hL u)
      ≤ capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
              (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.hemisphere m) hP hen (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl hdR hR.le (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capLeft_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capLeft_gen_gm_bcw hR hL gs u] at hkey
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (revolutionVolume_div_le_bcg m α (capTraceDataHemi_th m hm) CP C₁
      Cexp) hR.le) (sq_nonneg ((axialRep_gm hR hL gs u).toFun 0))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (poincareConstW_le_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp) hR.le)
    (dirichletP_nonneg (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

theorem cap_mass_right_gm_bcw (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd)
    (hdR : Real.sqrt (omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    massP (restrictRight hR hL u)
      ≤ capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * (axialRep_gm hR hL gs u).toFun
              (bulkLength (Cap.hemisphere m) (Cap.hemisphere m) L R) ^ 2
        + capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
              (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.hemisphere m) hP hen (memLp_transLift_gm_bcw hR gs)
    (integral_transLift_sq_gm_bcw hR gs) rfl hdR hR.le (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capRight_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capRight_gen_gm_bcw hR hL gs u] at hkey
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (revolutionVolume_div_le_bcg m α (capTraceDataHemi_th m hm) CP C₁
      Cexp) hR.le) (sq_nonneg ((axialRep_gm hR hL gs u).toFun (bulkLength (Cap.hemisphere m)
        (Cap.hemisphere m) L R)))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (poincareConstW_le_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp) hR.le)
    (dirichletP_nonneg (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

end SingleWeak

/-! ## 5. `CapLowerInput_gm` for two hemispherical caps, every dimension, weak ground state

The weak-ground-state analogue of `capLowerInput_gen_bcg`.  As discussed in §4 above, `Cexp`
cannot be dropped: it is genuinely needed to control `R * gs.nu - m * α`, a fact that
`TransverseGroundState`'s bare axioms do not supply on their own.  So `capLowerInput_gen_bcw`
keeps the same top-level parameters `C₁, Cexp, hCexp` as `capLowerInput_gen_bcg`, and replaces
the single hypothesis `TransverseExpansionData m α R gsr Cexp` (supplied per radius inside the
`∀ R` quantifier) by the *two* explicit per-radius hypotheses `hdR` (in place of `ted.dR_ge`) and
`hδ` (in place of `abs_delta_le_lw ted hR`, i.e. `ted.nuExp`). -/

set_option linter.unusedVariables false in
theorem capLowerInput_gen_bcw (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (L : ℝ) (hL0 : 0 < L)
    {C₁ Cexp : ℝ} (hCexp : 0 ≤ Cexp) (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ Ccap R₀ : ℝ, 0 ≤ Ccap ∧ 0 < R₀ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
        ∀ (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
          {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd),
          Real.sqrt (omega m) / 2
              ≤ (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y) →
          |R * gs.nu - (m : ℝ) * α| ≤ Cexp * R →
          CapLowerInput_gm gs Ccap hR hL (bdCapL_bcg hm L R hR hL)
            (bdCapR_bcg hm L R hR hL) := by
  obtain ⟨CP, hP⟩ := capPoincare_hemi_phg m
  have hβ := hemisphere_beta_pos m hm hα
  have hB0 : 0 ≤ capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp :=
    capLowerConstW_nonneg_bcg hα.le (capTraceDataHemi_th m hm) hP.nonneg hen.nonneg hCexp
  have hden : (0 : ℝ) < capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁
      Cexp + 1 := by linarith
  refine ⟨capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp,
    min (capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp)
      (omega m * (Cap.hemisphere m).beta α
        / (capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp + 1)),
    capLowerConst_nonneg_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp,
    lt_min (capR0W_pos (Cap.hemisphere m) hα.le (capTraceDataHemi_th m hm) hP.nonneg hen.nonneg
        hCexp)
      (div_pos (mul_pos (omega_pos m) hβ) hden),
    fun R hR hR0 hL bd gs hdR hδ => ?_⟩
  have hRc : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp :=
    lt_of_lt_of_le hR0 (min_le_left _ _)
  have hRb : R < omega m * (Cap.hemisphere m).beta α
      / (capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp + 1) :=
    lt_of_lt_of_le hR0 (min_le_right _ _)
  have hBR : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α := by
    have h := (lt_div_iff₀ hden).1 hRb
    nlinarith [hR.le, hB0]
  exact ⟨fun u => dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP (gPartW (Cap.hemisphere m) (transLift m R gs.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP_nonneg _, fun u => dirichletP_nonneg _,
    fun u => cap_lower_left_gm_bcw hm hα hP hen hR gs hCexp hdR hδ hRc hBR hL u,
    fun u => cap_lower_right_gm_bcw hm hα hP hen hR gs hCexp hdR hδ hRc hBR hL u,
    fun u => cap_mass_left_gm_bcw hm hα hP hen hR gs hdR hL u,
    fun u => cap_mass_right_gm_bcw hm hα hP hen hR gs hdR hL u⟩

/-! ## 6. Consistency: `capLowerInput_gen_bcg` re-derived from `capLowerInput_gen_bcw`

`gsr.toTransverseGroundState` turns any `TransverseGroundStateReg` into a weak
`TransverseGroundState`, `ted.dR_ge` supplies `hdR`, and `abs_delta_le_lw ted hR` supplies `hδ`
(Cexp is shared, since `capLowerInput_gen_bcg` already takes it as a top-level hypothesis, exactly
like `capLowerInput_gen_bcw`).  `axialRep_gm_eq_bcw` shows the two axial-profile representatives
agree definitionally, so `CapLowerInput_gm gsr.toTransverseGroundState ...` and
`CapLowerInput_bcg gsr ...` have definitionally equal `cap` fields. -/

theorem axialRep_gm_eq_bcw {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ}
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (gsr : TransverseGroundStateReg m α R bd)
    (u : H1P (thinDomain Cm Cp L R)) :
    axialRep_gm hR hL gsr.toTransverseGroundState u = axialRep_bcg hR hL gsr u := rfl

theorem capLowerInput_gen_bcg_of_bcw (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (L : ℝ)
    (hL0 : 0 < L) {C₁ Cexp : ℝ} (hCexp : 0 ≤ Cexp) (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ Ccap R₀ : ℝ, 0 ≤ Ccap ∧ 0 < R₀ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
        ∀ (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
          {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
          (gsr : TransverseGroundStateReg m α R bd),
          TransverseExpansionData m α R gsr Cexp →
          CapLowerInput_bcg hα Ccap hR hL gsr (bdCapL_bcg hm L R hR hL)
            (bdCapR_bcg hm L R hR hL) := by
  obtain ⟨Ccap, R₀, hCcap, hR₀, hmain⟩ := capLowerInput_gen_bcw m hm α hα L hL0 hCexp hen
  refine ⟨Ccap, R₀, hCcap, hR₀, fun R hR hR0 hL bd gsr hexp => ?_⟩
  have hgm := hmain R hR hR0 hL gsr.toTransverseGroundState hexp.dR_ge (abs_delta_le_lw hexp hR)
  refine ⟨?_⟩
  obtain ⟨Gm, Gp, hGm, hGp, hcapL, hcapR, hmassL, hmassR⟩ := hgm.cap
  refine ⟨Gm, Gp, hGm, hGp, ?_, ?_, ?_, ?_⟩
  · intro u
    have := hcapL u
    rwa [axialRep_gm_eq_bcw hR hL gsr u] at this
  · intro u
    have := hcapR u
    rwa [axialRep_gm_eq_bcw hR hL gsr u] at this
  · intro u
    have := hmassL u
    rwa [axialRep_gm_eq_bcw hR hL gsr u] at this
  · intro u
    have := hmassR u
    rwa [axialRep_gm_eq_bcw hR hL gsr u] at this

end RobinCaps.ThinDomain

end
