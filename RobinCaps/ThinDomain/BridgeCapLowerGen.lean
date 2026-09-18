import RobinCaps.ThinDomain.BridgeCapLowerOne
import RobinCaps.ThinDomain.ProfileEndpoint
import RobinCaps.ThinDomain.TrialBound
import RobinCaps.ThinDomain.AssemblyOneGen
import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.TraceDataHemi
import RobinCaps.Cap.PoincareHemiGen

/-!
# Discharging `CapLowerInput_bcg` for two hemispherical caps, every dimension `m`

This file is the general-dimension analogue of `RobinCaps/ThinDomain/BridgeCapLowerOne.lean`: it
derives the manuscript's `lem:cap`, in thin-domain scaling, for the two hemispherical caps of
`Ω_R ⊂ ℝ × ℝ^m`, from

* `RobinCaps/Cap/LowerWeak.lean` — `lem:cap` on the **fixed unit cap** for weak `H¹` functions,
  already stated for a general `Cap m` (`cap_lower_weak_p`, `cap_mass_bound_weak_p`);
* `RobinCaps/ThinDomain/BridgeCapLowerOne.lean`, §1 — the general-`m` scaling laws between
  `restrictLeft/Right` and `capLeft/Right` (`massP_restrictLeft_bc`, `dirichletP_restrictLeft_bc`,
  `pCoefW_capLeft_bc`, `pCoefW_capRight_bc`);
* `RobinCaps/ThinDomain/ProfileEndpoint.lean` — `eq:interval-trace`, already general in `m`
  (`profileEndpoint_left_pe`, `bulkProjThin_endpoint_left_pe`, …);
* `RobinCaps/ThinDomain/TrialBound.lean` — `TransverseExpansionData`, `transLift`, `sq_rpow_half`,
  already general in `m`;
* `RobinCaps/Cap/TraceDataHemi.lean` — `capTraceDataHemi_th m hm`, the `Γ`-trace interface of the
  hemispherical cap, built by even reflection, for **every** `m`;
* `RobinCaps/Cap/PoincareHemiGen.lean` — `capPoincare_hemi_phg m`, the Poincaré–Wirtinger
  inequality on the hemispherical cap, for every `m`.

## The key simplification over the `m = 1` file

In `BridgeCapLowerOne.lean` the identification of the unit-cap `Γ`-trace form with the cap piece
of the (vertical-slice) boundary density of `Ω_R` is a genuine geometric fact left as the
hypothesis `CapTraceMatch_bc`, to be supplied later by `Reflect.lean` / `BridgeRadial.lean` /
`VertRadIdent.lean`.

Here there is no such external boundary density to match: the cap piece `bdCapL_bcg`/`bdCapR_bcg`
of the (still to be assembled) general-`m` trace splitting is *defined* to be the rescaled
unit-cap `Γ`-form itself,

`bdCapL_bcg u := R^m · c⁻² · (capTraceDataHemi_th m hm).bdΓ (capLeft hR hL c u) (capLeft hR hL c u)`
  at `c = R^{m/2}`,

and since `c² = R^m` at the manuscript normalisation the scaling factor `R^m·c⁻²` is *exactly*
`1`. So `capEnergyW_capLeft_bcg` below is a direct algebraic computation (`dirichletP_capLeft_of_sq_eq`,
`massP_capLeft_of_sq_eq`, `field_simp`, `ring`) with no matching hypothesis at all.

## Remaining hypotheses

`capLowerInput_gen_bcg` is stated against:

* `hen : CapEntranceL2 (Cap.hemisphere m) C₁` — the `L²(Σ)` trace theorem on the entrance disk,
  exactly as in `BridgeCapLowerOne.lean` (not eliminable, for the reasons documented there);
* `hCexp : 0 ≤ Cexp` — in the `m = 1` file this sign fact is bootstrapped for free from the
  *canonical* transverse ground state family `transverseExpansionData_one` (`TrialOne.lean`),
  which supplies a concrete admissible radius before the per-radius universal statement even
  starts.  In general dimension there is no such canonical family: `TransverseExpansionData m α R
  gsr Cexp` is supplied by the caller **per radius**, inside the `∀ R` quantifier, so `Cexp`'s
  sign cannot be extracted before `Ccap` and `R₀` (which must not depend on `R`) are chosen.  This
  is exactly the kind of genuinely new obstruction the task instructions ask to be recorded as a
  named hypothesis rather than worked around; `Cexp_nonneg_lw` shows it holds automatically the
  moment a single admissible radius is exhibited, so any concrete instantiation of
  `capLowerInput_gen_bcg` (as in the `m = 1` consistency check) discharges it trivially.

Given these, `capLowerInput_gen_bcg` produces `Ccap, R₀` (depending only on `m, α, C₁, Cexp`) such
that `CapLowerInput_bcg` holds at every radius `R < R₀`, for *every* admissible transverse ground
state `gsr` and boundary form `bd` satisfying `TransverseExpansionData m α R gsr Cexp` at that
radius — mirroring the "arbitrary trace datum" genericity of
`RobinCaps.ThinDomain.AssemblyOneGen.CapLowerInput_ag`, whose shape `CapLowerInput_bcg` copies.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-! ## 1. The general-`m` axial profile representative

The general-dimension analogue of `RobinCaps.ThinDomain.axialRepOne_a1`: the same construction,
with the `m = 1`-specific canonical ground state `psiOne_a1 α R hα hR` replaced by an arbitrary
`gsr : TransverseGroundStateReg m α R bd`, and the normalisation `psiOne_normalized_a1` replaced
by the general bridging equality `psi_normalized_integral` of `RobinCaps/ThinDomain/BulkEnergy.lean`
(already proved for every `TransverseGroundState`). -/

section Axial

variable {m : ℕ} {Cm Cp : RobinCaps.Cap m} {L R α : ℝ}
variable {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **The bridging normalisation equality**: `gsr.normalized : NB gsr.psi = 1` rewritten as the
integral `∫_{B_m(1)} ψ² = 1`, exactly as `psiOne_normalized_a1` does for `m = 1`. -/
theorem gsr_normalized_bcg (gsr : TransverseGroundStateReg m α R bd) :
    ∫ z in transverseBall m R, gsr.psi.toFun z ^ 2 = 1 :=
  psi_normalized_integral gsr.toTransverseGroundState

/-- **The absolutely continuous representative of the axial profile `F`**, general dimension.
The general-`m` copy of `axialRepOne_a1`. -/
def axialRep_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.H1 (bulkLength Cm Cp L R) :=
  (h1Congr (bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R))).symm
    (bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
      gsr.psi.memL2 (gsr_normalized_bcg gsr) (restrictBulkP hR u))

theorem axialRep_toFun_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_bcg hR hL gsr u).toFun
      = (bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
          gsr.psi.memL2 (gsr_normalized_bcg gsr) (restrictBulkP hR u)).toFun :=
  h1Congr_symm_toFun_pe _ _

/-- **The bulk projection `π`, computed**, general dimension. -/
theorem bulkProjThin_mk_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    bulkProjThin hR hL gsr.psi.memL2 (gsr_normalized_bcg gsr) (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (axialRep_bcg hR hL gsr u) := by
  rw [bulkProjThin_eq hR hL gsr.psi.memL2 (gsr_normalized_bcg gsr)]
  simp only [LinearMap.comp_apply, restrictBulkPQ_mk, bulkProjT_mk, LinearEquiv.coe_coe]
  rw [h1QCongr_symm_mk_pe]
  rfl

/-- **`eq:interval-trace`, left endpoint**, general dimension: the general-`m` copy of
`axialRepOne_endpoint_left_bi`. -/
theorem axialRep_endpoint_left_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_bcg hR hL gsr u).toFun 0
      = ∫ z in transverseBall m R, ifaceL u z * gsr.psi.toFun z :=
  bulkProjThin_endpoint_left_pe u hR hL gsr.psi.memL2 (gsr_normalized_bcg gsr)
    (bulkProjThin_mk_bcg hR hL gsr u).symm

/-- **`eq:interval-trace`, right endpoint**, general dimension. -/
theorem axialRep_endpoint_right_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_bcg hR hL gsr u).toFun (bulkLength Cm Cp L R)
      = ∫ z in transverseBall m R, ifaceR u z * gsr.psi.toFun z :=
  bulkProjThin_endpoint_right_pe u hR hL gsr.psi.memL2 (gsr_normalized_bcg gsr)
    (bulkProjThin_mk_bcg hR hL gsr u).symm

end Axial

/-! ## 2. The scaling identities at `c = R^{m/2}`, general dimension

The general-`m` copies of §2 of `BridgeCapLowerOne.lean` (there specialised to `m = 1` and
`c = √R`).  `capMassScaledW_capLeft_gen_bcg`/`pCoefW_capLeft_gen_bcg` do not involve any trace
datum; `capEnergyL_bcg`/`capEnergyR_bcg` are the generic (`bdCapL`-parametrised) cap energies of
`RobinCaps.ThinDomain.AssemblyOneGen.capEnergyL_ag`, copied here for a general `Cap m`. -/

section GenScaling

variable {m : ℕ} {Cm Cp : RobinCaps.Cap m} {L R α : ℝ}
variable {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **The thin-domain cap mass is the scaled unit-cap mass** (left cap), general dimension. -/
theorem capMassScaledW_capLeft_gen_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    capMassScaledW R (capLeft hR hL c u) = massP (restrictLeft hR hL u) := by
  rw [capMassScaledW, massP_capLeft_of_sq_eq hR hL hc u, ← mul_assoc,
    mul_inv_cancel₀ hR.ne', one_mul]

/-- **The thin-domain cap mass is the scaled unit-cap mass** (right cap), general dimension. -/
theorem capMassScaledW_capRight_gen_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    capMassScaledW R (capRight hR hL c u) = massP (restrictRight hR hL u) := by
  rw [capMassScaledW, massP_capRight_of_sq_eq hR hL hc u, ← mul_assoc,
    mul_inv_cancel₀ hR.ne', one_mul]

/-- **`eq:interval-trace` with the general-`m` scaling factor computed**: at `c = R^{m/2}` the
entrance pairing `p_- = ⟨Tr_Σ U, Ψ_R⟩_{L²(Σ)}` of the left cap component *is* the left endpoint
value `F(x_-)` of the axial profile — the factor `c R^{m/2} R^{-m}` of `pCoefW_capLeft_bc` equals
`1` because `c = R^{m/2}` makes it `R^{m/2}·R^{m/2}·R^{-m} = R^m·R^{-m} = 1`. -/
theorem pCoefW_capLeft_gen_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cm (transLift m R gsr.psi) (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
      = (axialRep_bcg hR hL gsr u).toFun 0 := by
  have hsq : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) = R ^ m := by
    have h := sq_rpow_half m hR; rwa [sq] at h
  have h : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) * (R ^ m)⁻¹ = 1 := by
    rw [hsq, mul_inv_cancel₀ (pow_pos hR m).ne']
  rw [pCoefW_capLeft_bc hR hL (R ^ ((m : ℝ) / 2)) gsr.psi u, h, one_mul,
    axialRep_endpoint_left_bcg hR hL gsr u]
  rfl

/-- **`eq:interval-trace`, right endpoint**, general dimension. -/
theorem pCoefW_capRight_gen_bcg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gsr : TransverseGroundStateReg m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    pCoefW Cp (transLift m R gsr.psi) (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
      = (axialRep_bcg hR hL gsr u).toFun (bulkLength Cm Cp L R) := by
  have hsq : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) = R ^ m := by
    have h := sq_rpow_half m hR; rwa [sq] at h
  have h : R ^ ((m : ℝ) / 2) * R ^ ((m : ℝ) / 2) * (R ^ m)⁻¹ = 1 := by
    rw [hsq, mul_inv_cancel₀ (pow_pos hR m).ne']
  rw [pCoefW_capRight_bc hR hL (R ^ ((m : ℝ) / 2)) gsr.psi u, h, one_mul,
    axialRep_endpoint_right_bcg hR hL gsr u]
  rfl

/-- The renormalized energy of the left cap component, for a generic cap piece — the general-`m`
copy of `RobinCaps.ThinDomain.capEnergyL_ag`. -/
def capEnergyL_bcg (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (bdCapL : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictLeft hR hL u) + α * bdCapL u - ν * massP (restrictLeft hR hL u)

/-- The renormalized energy of the right cap component, for a generic cap piece. -/
def capEnergyR_bcg (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (bdCapR : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictRight hR hL u) + α * bdCapR u - ν * massP (restrictRight hR hL u)

end GenScaling

/-! ## 3. The hemispherical cap pieces, general dimension

Since `bdCapL_bcg`/`bdCapR_bcg` are *defined* to be the rescaled `Γ`-trace form of
`capTraceDataHemi_th m hm`, `capEnergyW_capLeft_bcg`/`capEnergyW_capRight_bcg` below need no
matching hypothesis at all (contrast `CapTraceMatch_bc` of `BridgeCapLowerOne.lean`). -/

section Hemi

variable {m : ℕ} (hm : 1 ≤ m) {L R α : ℝ}

/-- **The left-cap piece**: the rescaled unit-cap `Γ`-trace form, at `c = R^{m/2}`.  The scaling
factor `R^m · c⁻²` is exactly `1` at this normalisation (`c² = R^m`), so this is really just
`(capTraceDataHemi_th m hm).bdΓ (capLeft hR hL (R^{m/2}) u) (capLeft hR hL (R^{m/2}) u)`, written
with the general factor for documentation of the scaling (`bdCapL_bcg_eq_bdΓ_bcg` below makes the
simplification explicit). -/
def bdCapL_bcg (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) : ℝ :=
  R ^ m * ((R ^ ((m : ℝ) / 2)) ^ 2)⁻¹
    * (capTraceDataHemi_th m hm).bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)

/-- **The right-cap piece**: the rescaled unit-cap `Γ`-trace form. -/
def bdCapR_bcg (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) : ℝ :=
  R ^ m * ((R ^ ((m : ℝ) / 2)) ^ 2)⁻¹
    * (capTraceDataHemi_th m hm).bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)

theorem bdCapL_bcg_eq_bdΓ_bcg (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_bcg hm L R hR hL u
      = (capTraceDataHemi_th m hm).bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
          (capLeft hR hL (R ^ ((m : ℝ) / 2)) u) := by
  rw [bdCapL_bcg, sq_rpow_half m hR, mul_inv_cancel₀ (pow_pos hR m).ne', one_mul]

theorem bdCapR_bcg_eq_bdΓ_bcg (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_bcg hm L R hR hL u
      = (capTraceDataHemi_th m hm).bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
          (capRight hR hL (R ^ ((m : ℝ) / 2)) u) := by
  rw [bdCapR_bcg, sq_rpow_half m hR, mul_inv_cancel₀ (pow_pos hR m).ne', one_mul]

/-- **The unit-cap energy of the left cap component is the thin-domain left-cap energy**, general
dimension — the general-`m` copy of `capEnergyW_capLeft_bc`, with the matching hypothesis
discharged for free by the definition of `bdCapL_bcg`. -/
theorem capEnergyW_capLeft_bcg (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L) (ν : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    capEnergyW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) R (R * ν - (m : ℝ) * α)
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
      = capEnergyL_bcg α ν hR hL (bdCapL_bcg hm L R hR hL) u := by
  have hc : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hRne : R ≠ 0 := hR.ne'
  have hRmne : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  rw [capEnergyW, capJW, capEnergyL_bcg, bdCapL_bcg,
    dirichletP_capLeft_of_sq_eq hR hL hc u, massP_capLeft_of_sq_eq hR hL hc u, hc]
  field_simp
  ring

/-- **The unit-cap energy of the right cap component is the thin-domain right-cap energy**,
general dimension. -/
theorem capEnergyW_capRight_bcg (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L) (ν : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    capEnergyW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) R (R * ν - (m : ℝ) * α)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
      = capEnergyR_bcg α ν hR hL (bdCapR_bcg hm L R hR hL) u := by
  have hc : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hRne : R ≠ 0 := hR.ne'
  have hRmne : (R : ℝ) ^ m ≠ 0 := (pow_pos hR m).ne'
  rw [capEnergyW, capJW, capEnergyR_bcg, bdCapR_bcg,
    dirichletP_capRight_of_sq_eq hR hL hc u, massP_capRight_of_sq_eq hR hL hc u, hc]
  field_simp
  ring

end Hemi

/-! ## 4. The constant of `lem:cap` in thin-domain scaling, general dimension

The general-`m` copy of §4 of `BridgeCapLowerOne.lean`. -/

/-- The constant `C` of `CapLowerInput_bcg`: it dominates the three constants produced by
`cap_lower_weak_p` and `cap_mass_bound_weak_p`. -/
def capLowerConst_bcg (m : ℕ) (α : ℝ) (td : CapTraceData (Cap.hemisphere m)) (CP C₁ Cexp : ℝ) :
    ℝ :=
  max (max (capLowerConstW (Cap.hemisphere m) α td CP C₁ Cexp / omega m)
        (8 * (Cap.hemisphere m).revolutionVolume / omega m))
    (2 * capPoincareConstW (Cap.hemisphere m) CP C₁)

theorem capLowerConst_nonneg_bcg (m : ℕ) (α : ℝ) (td : CapTraceData (Cap.hemisphere m))
    (CP C₁ Cexp : ℝ) : 0 ≤ capLowerConst_bcg m α td CP C₁ Cexp := by
  refine le_trans (le_trans ?_ (le_max_right _ _)) (le_max_left _ _)
  have : (0 : ℝ) ≤ 8 * (Cap.hemisphere m).revolutionVolume :=
    mul_nonneg (by norm_num) (revolutionVolume_nonneg_lw _)
  exact div_nonneg this (omega_pos m).le

theorem capLowerConstW_div_le_bcg (m : ℕ) (α : ℝ) (td : CapTraceData (Cap.hemisphere m))
    (CP C₁ Cexp : ℝ) :
    capLowerConstW (Cap.hemisphere m) α td CP C₁ Cexp / omega m
      ≤ capLowerConst_bcg m α td CP C₁ Cexp :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem revolutionVolume_div_le_bcg (m : ℕ) (α : ℝ) (td : CapTraceData (Cap.hemisphere m))
    (CP C₁ Cexp : ℝ) :
    8 * (Cap.hemisphere m).revolutionVolume / omega m ≤ capLowerConst_bcg m α td CP C₁ Cexp :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem poincareConstW_le_bcg (m : ℕ) (α : ℝ) (td : CapTraceData (Cap.hemisphere m))
    (CP C₁ Cexp : ℝ) :
    2 * capPoincareConstW (Cap.hemisphere m) CP C₁ ≤ capLowerConst_bcg m α td CP C₁ Cexp :=
  le_max_right _ _

/-- `capLowerConstW ≥ 0`, general dimension. -/
theorem capLowerConstW_nonneg_bcg {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (td : CapTraceData (Cap.hemisphere m)) {CP C₁ Cexp : ℝ} (hCP : 0 ≤ CP) (hC₁ : 0 ≤ C₁)
    (hCexp : 0 ≤ Cexp) : 0 ≤ capLowerConstW (Cap.hemisphere m) α td CP C₁ Cexp := by
  have hA0 := (capConstW_ge (Cap.hemisphere m) hα td hCP hC₁ hCexp).1
  rw [capLowerConstW]
  nlinarith [sq_nonneg (capConstW (Cap.hemisphere m) α td CP C₁ Cexp),
    sq_nonneg (capConstW (Cap.hemisphere m) α td CP C₁ Cexp
      + capConstW (Cap.hemisphere m) α td CP C₁ Cexp ^ 2)]

/-! ## 5. `lem:cap` at a single admissible radius, general dimension -/

section Single

variable {m : ℕ} (hm : 1 ≤ m) {α L R : ℝ}

theorem hemisphere_theta_zero_nonneg_bcg : 0 ≤ (Cap.hemisphere m).θ 0 :=
  le_of_eq (hemisphere_theta_zero_th m).symm

/-- **`eq:cap-lower` for the left cap component, in thin-domain scaling**, general dimension. -/
theorem cap_lower_left_bcg (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gsr : TransverseGroundStateReg m α R bd)
    (ted : TransverseExpansionData m α R gsr Cexp)
    (hRc : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    ((Cap.hemisphere m).beta α - capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R)
          * (axialRep_bcg hR hL gsr u).toFun 0 ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
            (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyL_bcg α gsr.nu hR hL (bdCapL_bcg hm L R hR hL) u := by
  have hkey := cap_lower_weak_p (Cap.hemisphere m) hm hemisphere_theta_zero_nonneg_bcg
    (capTraceDataHemi_th m hm) hP hen (Cexp_nonneg_lw ted hR) hα.le
    (hemisphere_beta_pos m hm hα).le (memLp_transLift_lw gsr) (integral_transLift_sq hR gsr) rfl
    ted.dR_ge hR hRc (abs_delta_le_lw ted hR) hBR (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capLeft_bcg hm hR hL gsr.nu u, pCoefW_capLeft_gen_bcg hR hL gsr u] at hkey
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
  have hstep := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ((axialRep_bcg hR hL gsr u).toFun 0))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
          (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by
    ring
  rw [hdiv]
  linarith

/-- **`eq:cap-lower` for the right cap component, in thin-domain scaling**, general dimension. -/
theorem cap_lower_right_bcg (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gsr : TransverseGroundStateReg m α R bd)
    (ted : TransverseExpansionData m α R gsr Cexp)
    (hRc : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp)
    (hBR : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    ((Cap.hemisphere m).beta α - capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R)
          * (axialRep_bcg hR hL gsr u).toFun
              (bulkLength (Cap.hemisphere m) (Cap.hemisphere m) L R) ^ 2
        + (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
            (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
            (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      ≤ capEnergyR_bcg α gsr.nu hR hL (bdCapR_bcg hm L R hR hL) u := by
  have hkey := cap_lower_weak_p (Cap.hemisphere m) hm hemisphere_theta_zero_nonneg_bcg
    (capTraceDataHemi_th m hm) hP hen (Cexp_nonneg_lw ted hR) hα.le
    (hemisphere_beta_pos m hm hα).le (memLp_transLift_lw gsr) (integral_transLift_sq hR gsr) rfl
    ted.dR_ge hR hRc (abs_delta_le_lw ted hR) hBR (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capEnergyW_capRight_bcg hm hR hL gsr.nu u, pCoefW_capRight_gen_bcg hR hL gsr u] at hkey
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
    (sq_nonneg ((axialRep_bcg hR hL gsr u).toFun (bulkLength (Cap.hemisphere m)
      (Cap.hemisphere m) L R)))
  have hdiv : (2 * R)⁻¹ * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u))
      = dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
          (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
          (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) / (2 * R) := by
    ring
  rw [hdiv]
  linarith

/-- **`eq:cap-mass-bound` for the left cap component, in thin-domain scaling**, general
dimension. -/
theorem cap_mass_left_bcg (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gsr : TransverseGroundStateReg m α R bd)
    (ted : TransverseExpansionData m α R gsr Cexp)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    massP (restrictLeft hR hL u)
      ≤ capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * (axialRep_bcg hR hL gsr u).toFun 0 ^ 2
        + capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
              (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.hemisphere m) hP hen (memLp_transLift_lw gsr)
    (integral_transLift_sq hR gsr) rfl ted.dR_ge hR.le (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capLeft_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capLeft_gen_bcg hR hL gsr u] at hkey
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (revolutionVolume_div_le_bcg m α (capTraceDataHemi_th m hm) CP C₁
      Cexp) hR.le) (sq_nonneg ((axialRep_bcg hR hL gsr u).toFun 0))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (poincareConstW_le_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp) hR.le)
    (dirichletP_nonneg (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
      (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

/-- **`eq:cap-mass-bound` for the right cap component, in thin-domain scaling**, general
dimension. -/
theorem cap_mass_right_bcg (hα : 0 < α) {CP C₁ Cexp : ℝ}
    (hP : CapPoincare (Cap.hemisphere m) CP) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (hR : 0 < R) {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gsr : TransverseGroundStateReg m α R bd)
    (ted : TransverseExpansionData m α R gsr Cexp)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    massP (restrictRight hR hL u)
      ≤ capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * (axialRep_bcg hR hL gsr u).toFun
              (bulkLength (Cap.hemisphere m) (Cap.hemisphere m) L R) ^ 2
        + capLowerConst_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
          * dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
              (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
              (capRight hR hL (R ^ ((m : ℝ) / 2)) u)) := by
  have hkey := cap_mass_bound_weak_p (Cap.hemisphere m) hP hen (memLp_transLift_lw gsr)
    (integral_transLift_sq hR gsr) rfl ted.dR_ge hR.le (capRight hR hL (R ^ ((m : ℝ) / 2)) u)
  rw [capMassScaledW_capRight_gen_bcg hR hL (sq_rpow_half m hR) u,
    pCoefW_capRight_gen_bcg hR hL gsr u] at hkey
  have e1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (revolutionVolume_div_le_bcg m α (capTraceDataHemi_th m hm) CP C₁
      Cexp) hR.le) (sq_nonneg ((axialRep_bcg hR hL gsr u).toFun (bulkLength (Cap.hemisphere m)
        (Cap.hemisphere m) L R)))
  have e2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (poincareConstW_le_bcg m α (capTraceDataHemi_th m hm) CP C₁ Cexp) hR.le)
    (dirichletP_nonneg (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
      (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
      (capRight hR hL (R ^ ((m : ℝ) / 2)) u)))
  linarith

end Single

/-! ## 6. `CapLowerInput_bcg` for two hemispherical caps, every dimension -/

/-- **`lem:cap` in thin-domain scaling, at one radius, every dimension** — the general-`m` shape
of `RobinCaps.ThinDomain.AssemblyOneGen.CapLowerInput_ag`, specialised to the two hemispherical
caps `Cm = Cp = Cap.hemisphere m` and to an arbitrary transverse ground state `gsr`. -/
structure CapLowerInput_bcg {m : ℕ} {α R L : ℝ} (hα : 0 < α) (Ccap : ℝ) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gsr : TransverseGroundStateReg m α R bd)
    (bdCapL bdCapR : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) → ℝ) : Prop where
  /-- The two cap decompositions of `lem:cap` exist at this radius. -/
  cap : ∃ Gm Gp : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) → ℝ,
    (∀ u, 0 ≤ Gm u) ∧ (∀ u, 0 ≤ Gp u) ∧
    (∀ u, ((Cap.hemisphere m).beta α - Ccap * R) * (axialRep_bcg hR hL gsr u).toFun 0 ^ 2
            + (2 * R)⁻¹ * Gm u
          ≤ dirichletP (restrictLeft hR hL u) + α * bdCapL u
              - gsr.nu * massP (restrictLeft hR hL u)) ∧
    (∀ u, ((Cap.hemisphere m).beta α - Ccap * R)
              * (axialRep_bcg hR hL gsr u).toFun
                  (bulkLength (Cap.hemisphere m) (Cap.hemisphere m) L R) ^ 2
            + (2 * R)⁻¹ * Gp u
          ≤ dirichletP (restrictRight hR hL u) + α * bdCapR u
              - gsr.nu * massP (restrictRight hR hL u)) ∧
    (∀ u, massP (restrictLeft hR hL u)
          ≤ Ccap * R * (axialRep_bcg hR hL gsr u).toFun 0 ^ 2 + Ccap * R * Gm u) ∧
    (∀ u, massP (restrictRight hR hL u)
          ≤ Ccap * R * (axialRep_bcg hR hL gsr u).toFun
                (bulkLength (Cap.hemisphere m) (Cap.hemisphere m) L R) ^ 2
              + Ccap * R * Gp u)

set_option linter.unusedVariables false in
/-- **`lem:cap` in thin-domain scaling for two hemispherical caps, every dimension `m ≥ 1`.**

The general-dimension analogue of `RobinCaps.ThinDomain.capLowerInput_one_bc`.  It produces
`Ccap, R₀` (depending only on `m, α, C₁, Cexp` and the hemisphere constants) such that, for every
admissible radius `R < R₀` and every transverse ground state `gsr` satisfying
`TransverseExpansionData m α R gsr Cexp` at that radius, `CapLowerInput_bcg` holds with the cap
pieces `bdCapL_bcg`/`bdCapR_bcg`.

**Remaining hypotheses**: `hen : CapEntranceL2 (Cap.hemisphere m) C₁` (as in the `m = 1` file, not
eliminable) and `hCexp : 0 ≤ Cexp` — recorded because, unlike the `m = 1` file, there is no
canonical transverse ground-state family here to bootstrap the sign of `Cexp` from a single
concrete radius before `Ccap, R₀` are chosen; see the module docstring. -/
theorem capLowerInput_gen_bcg (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (L : ℝ) (hL0 : 0 < L)
    {C₁ Cexp : ℝ} (hCexp : 0 ≤ Cexp) (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ Ccap R₀ : ℝ, 0 ≤ Ccap ∧ 0 < R₀ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₀ →
        ∀ (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
          {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gsr : TransverseGroundStateReg m α R bd),
          TransverseExpansionData m α R gsr Cexp →
          CapLowerInput_bcg hα Ccap hR hL gsr (bdCapL_bcg hm L R hR hL)
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
    fun R hR hR0 hL bd gsr hexp => ?_⟩
  have hRc : R < capR0W (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp :=
    lt_of_lt_of_le hR0 (min_le_left _ _)
  have hRb : R < omega m * (Cap.hemisphere m).beta α
      / (capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp + 1) :=
    lt_of_lt_of_le hR0 (min_le_right _ _)
  have hBR : capLowerConstW (Cap.hemisphere m) α (capTraceDataHemi_th m hm) CP C₁ Cexp * R
      ≤ omega m * (Cap.hemisphere m).beta α := by
    have h := (lt_div_iff₀ hden).1 hRb
    nlinarith [hR.le, hB0]
  exact ⟨fun u => dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
        (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP (gPartW (Cap.hemisphere m) (transLift m R gsr.psi)
        (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gsr.psi y)
        (capRight hR hL (R ^ ((m : ℝ) / 2)) u)),
    fun u => dirichletP_nonneg _, fun u => dirichletP_nonneg _,
    fun u => cap_lower_left_bcg hm hα hP hen hR gsr hexp hRc hBR hL u,
    fun u => cap_lower_right_bcg hm hα hP hen hR gsr hexp hRc hBR hL u,
    fun u => cap_mass_left_bcg hm hα hP hen hR gsr hexp hL u,
    fun u => cap_mass_right_bcg hm hα hP hen hR gsr hexp hL u⟩

end RobinCaps.ThinDomain

end
