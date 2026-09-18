import RobinCaps.ThinDomain.AssemblyOneGen

/-!
# The general transverse-dimension global comparison, generalised from `AssemblyOneGen.lean`

`RobinCaps/ThinDomain/AssemblyOneGen.lean` carries out the final `m = 1` assembly of `sec:proof`
for an **arbitrary trace datum**, but still against the one concrete transverse ground state
`groundStateOne α R hα hR : TransverseGroundState 1 α R (bdTr R)` of
`RobinCaps/Transverse/GroundStateOneFull.lean`.

This file isolates the two remaining `m = 1` specifics —

* the transverse boundary form `bdTr R` and the ground state `groundStateOne` built from it
  (replaced by an abstract `bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ` and
  `gs : TransverseGroundState m α R bd`), and
* the sliceability witness `bdSliceable_bdTr` (replaced by an abstract
  `hsl : BdSliceable a b bd`),

— and repeats the whole assembly for an **arbitrary transverse dimension** `m`, an arbitrary
`Cm Cp : Cap m`, and an arbitrary family of ground states.  All of the underlying bulk machinery
(`RobinCaps/ThinDomain/BulkEnergy.lean`'s `TransverseGroundState`, `BdSliceable`, `bdCyl`, `EB`,
`bulk_separation`, `bulk_mass_split`; `RobinCaps/ThinDomain/BulkProj.lean`'s `bulkRepT`,
`bulkProjThin`; `RobinCaps/ThinDomain/Assembly.lean`'s `GlobalComparisonData`,
`GlobalComparison`, `MainTheorem`; `RobinCaps/ThinDomain/Eigen.lean`'s `counterexample_of_mainTheorem'`,
`hemisphere`) is **already** stated for a general `m : ℕ`, so no changes are needed there; the
only genuinely new ingredient of this file is the *axial profile representative* built from a
generic ground state (Part 0) and the *ground-state family* interface that packages the uniform
spectral gap and the ground-state-energy function `nu' : ℝ → ℝ` needed by `GlobalComparison`
(Part 4b).

## Contents

1. Part 0: `axialRep_gm`, `bulkProjThin_mk_gm`, `mass_axialRep_gm`, `dirichlet_axialRep_gm` —
   the general-`m` analogue of `axialRepOne_a1` and its companions, built from an arbitrary
   `gs : TransverseGroundState m α R bd`.
2. Part 1: `TraceSplitInput_gm`, `capEnergyL_gm`, `capEnergyR_gm`, `energy_split_gm` — the generic
   copy of `TraceSplitInput_ag`/`energy_split_ag`, with `bdTr R` replaced by `bd`.
3. Part 2: `CapLowerInput_gm` — the generic copy of `CapLowerInput_ag`.
4. Part 3: `Zrep_gm`, `Zrep_nonneg_gm`, `lower_rep_gm`, `upper_rep_gm` — the generic copy of
   `Zrep_ag`, `lower_rep_ag`, `upper_rep_ag`.
5. Part 4: `Zone_gm`, `globalComparisonData_gm` — the generic copy of `globalComparisonData_gen_ag`.
6. Part 4b: `GroundStateFamily_gm` — the ground-state-family interface (uniform spectral gap,
   ground-state energy as a function of `R` alone).
7. Part 5: `TraceSplitFamilyInput_gm`, `InterfaceTraceInput_gm`, `TrialEnergyInput_gm`,
   `globalComparison_gm`, `mainTheorem_gm`, `counterexample_gm` — the generic global comparison,
   `thm:main` and `cor:counterexample`, for a general ground-state family.
8. Part 6: the consistency check — `groundStateFamilyOne_gm` builds a `GroundStateFamily_gm 1 α R₀`
   out of `groundStateOne`/`groundStateOne_gap_quant`/`nuOneDim`/`bdSliceable_bdTr`, and
   `globalComparisonData_gen_ag'`, `mainTheorem_gen_ag'` re-derive `AssemblyOneGen`'s own results
   from the generic ones.

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

/-! ## Part 0: the axial profile representative for a generic ground state -/

section Axial

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **The general-`m` analogue of `axialRepOne_a1`.**  The absolutely continuous representative
of the axial profile `F` of `eq:bulk-projection`, as an element of the concrete one-dimensional
model on the bulk interval `I_R`, built from an arbitrary transverse ground state
`gs : TransverseGroundState m α R bd`. -/
def axialRep_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (gs : TransverseGroundState m α R bd)
    (u : H1P (thinDomain Cm Cp L R)) : Sobolev.H1 (bulkLength Cm Cp L R) :=
  (h1Congr (bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R))).symm
    (bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
      gs.psi.memL2 (psi_normalized_integral gs) (restrictBulkP hR u))

theorem axialRep_toFun_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    (axialRep_gm hR hL gs u).toFun
      = (bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
          gs.psi.memL2 (psi_normalized_integral gs) (restrictBulkP hR u)).toFun :=
  h1Congr_symm_toFun_a1 _ _

/-- **The bulk projection `π`, computed, for a generic ground state.** -/
theorem bulkProjThin_mk_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    bulkProjThin hR hL gs.psi.memL2 (psi_normalized_integral gs) (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (axialRep_gm hR hL gs u) := by
  rw [bulkProjThin_eq hR hL gs.psi.memL2 (psi_normalized_integral gs)]
  simp only [LinearMap.comp_apply, restrictBulkPQ_mk, bulkProjT_mk, LinearEquiv.coe_coe]
  rw [h1QCongr_symm_mk_a1]
  rfl

/-- **`M[F]` is the `L²` norm of the axial profile on the bulk cylinder, for a generic ground
state.** -/
theorem mass_axialRep_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
      = ∫ x in Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
          axialProfile gs (restrictBulkP hR u) x ^ 2 := by
  set a : ℝ := -L / 2 + Cm.K * R with ha
  set b : ℝ := L / 2 - Cp.K * R with hb
  have hab : a < b := interface_lt hR hL
  set V := bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
    gs.psi.memL2 (psi_normalized_integral gs) (restrictBulkP hR u) with hV
  have hℓ : (0 : ℝ) < bulkLength Cm Cp L R := trialAC_bulkLength_pos hL
  have hfun : (axialRep_gm hR hL gs u).toFun = V.toFun := axialRep_toFun_gm hR hL gs u
  have h1 : Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
      = ∫ x in Ioo 0 (bulkLength Cm Cp L R), V.toFun x ^ 2 := by
    rw [Sobolev.mass, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le, hfun]
  have h2 : (∫ x in Ioo 0 (bulkLength Cm Cp L R), V.toFun x ^ 2)
      = ∫ x in Ioo 0 (b - a), V.toFun x ^ 2 := by
    rw [bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
  have h3 : (∫ x in Ioo a b, V.toFun (x - a) ^ 2) = ∫ y in Ioo 0 (b - a), V.toFun y ^ 2 :=
    setIntegral_Ioo_translate_a1 a b hab.le (fun y => V.toFun y ^ 2)
  have h4 : (∫ x in Ioo a b, V.toFun (x - a) ^ 2)
      = ∫ x in Ioo a b, axialProfile gs (restrictBulkP hR u) x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [bulkRepT_ae (interface_lt hR hL) isOpen_transverseBall
      volume_transverseBall_ne_top gs.psi.memL2 (psi_normalized_integral gs)
      (restrictBulkP hR u)] with x hx
    show V.toFun (x - a) ^ 2 = _
    rw [show V.toFun (x - a) = axialCoeff (transverseBall m R) (restrictBulkP hR u).toFun
        gs.psi.toFun x from hx]
    rfl
  rw [h1, h2, ← h3, h4]

/-- **`D[F]` is the axial Dirichlet energy of the profile on the bulk cylinder, for a generic
ground state.** -/
theorem dirichlet_axialRep_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
      = ∫ x in Ioo (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R),
          axialProfileDeriv gs (restrictBulkP hR u) x ^ 2 := by
  set a : ℝ := -L / 2 + Cm.K * R with ha
  set b : ℝ := L / 2 - Cp.K * R with hb
  have hab : a < b := interface_lt hR hL
  set V := bulkRepT (interface_lt hR hL) isOpen_transverseBall volume_transverseBall_ne_top
    gs.psi.memL2 (psi_normalized_integral gs) (restrictBulkP hR u) with hV
  have hℓ : (0 : ℝ) < bulkLength Cm Cp L R := trialAC_bulkLength_pos hL
  have hfun : (axialRep_gm hR hL gs u).toFun = V.toFun := axialRep_toFun_gm hR hL gs u
  have h1 : Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
      = ∫ x in Ioo 0 (bulkLength Cm Cp L R), deriv V.toFun x ^ 2 := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le, hfun]
  have h2 : (∫ x in Ioo 0 (bulkLength Cm Cp L R), deriv V.toFun x ^ 2)
      = ∫ x in Ioo 0 (b - a), deriv V.toFun x ^ 2 := by
    rw [bulkLength_eq_sub (Cm := Cm) (Cp := Cp) (L := L) (R := R)]
  have h3 : (∫ x in Ioo a b, deriv V.toFun (x - a) ^ 2)
      = ∫ y in Ioo 0 (b - a), deriv V.toFun y ^ 2 :=
    setIntegral_Ioo_translate_a1 a b hab.le (fun y => deriv V.toFun y ^ 2)
  have h4 : (∫ x in Ioo a b, deriv V.toFun (x - a) ^ 2)
      = ∫ x in Ioo a b, axialProfileDeriv gs (restrictBulkP hR u) x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [bulkRepT_deriv_ae (interface_lt hR hL) isOpen_transverseBall
      volume_transverseBall_ne_top gs.psi.memL2 (psi_normalized_integral gs)
      (restrictBulkP hR u)] with x hx
    show deriv V.toFun (x - a) ^ 2 = _
    rw [show deriv V.toFun (x - a) = axialCoeff (transverseBall m R) (restrictBulkP hR u).gx
        gs.psi.toFun x from hx]
    rfl
  rw [h1, h2, ← h3, h4]

end Axial

/-! ## Part 1: the trace-split interface, generically -/

section Split

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ}

/-- The bulk restriction of `RobinCaps/ThinDomain/Restrict.lean` and the one of
`RobinCaps/ThinDomain/BulkProj.lean` agree, for a general transverse dimension `m`. -/
theorem restrictBulk_eq_restrictBulkP_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    restrictBulk hR hL u = restrictBulkP hR u := rfl

/-- **The generic trace-split interface**, the copy of `TraceSplitInput_ag` with `bdTr R`
replaced by an arbitrary transverse boundary form `bd`. -/
structure TraceSplitInput_gm (hR : 0 < R) (td : TraceData Cm Cp L R)
    (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ) : Prop where
  /-- The left-cap piece of the boundary form is nonnegative. -/
  bdCapL_nonneg : ∀ u, 0 ≤ bdCapL u
  /-- The right-cap piece of the boundary form is nonnegative. -/
  bdCapR_nonneg : ∀ u, 0 ≤ bdCapR u
  /-- **The boundary form splits**, with the bulk piece the cylinder form of `bd`. -/
  split : ∀ u : H1P (thinDomain Cm Cp L R),
    td.bd u u
      = bdCapL u + bdCyl bd (restrictBulkP hR u) (restrictBulkP hR u) + bdCapR u

/-- The renormalized energy of the left cap component, for a generic cap piece. -/
def capEnergyL_gm (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (bdCapL : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictLeft hR hL u) + α * bdCapL u - ν * massP (restrictLeft hR hL u)

/-- The renormalized energy of the right cap component, for a generic cap piece. -/
def capEnergyR_gm (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (bdCapR : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictRight hR hL u) + α * bdCapR u - ν * massP (restrictRight hR hL u)

/-- **The generic analogue of `energy_split_ag`.**  The renormalized Robin energy of `Ω_R`
splits exactly into the two cap energies and the renormalized bulk energy. -/
theorem energy_split_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    {td : TraceData Cm Cp L R} {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hs : TraceSplitInput_gm hR td bd bdCapL bdCapR) (ν : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP u + α * td.bd u u - ν * massP u
      = capEnergyL_gm α ν hR hL bdCapL u
        + (EB α bd (restrictBulkP hR u) - ν * massP (restrictBulkP hR u))
        + capEnergyR_gm α ν hR hL bdCapR u := by
  rw [capEnergyL_gm, capEnergyR_gm, EB, hs.split u, dirichletP_eq_sum hR hL u,
    massP_eq_sum hR hL u, restrictBulk_eq_restrictBulkP_gm hR hL]
  ring

end Split

/-! ## Part 2: the cap interface, generically -/

section Interface

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **`lem:cap` in thin-domain scaling, at one radius, for a generic transverse ground state.**

This is `CapLowerInput_ag` with `groundStateOne`/`nuR`/`axialRepOne_a1` replaced by an arbitrary
`gs : TransverseGroundState m α R bd`. -/
structure CapLowerInput_gm (gs : TransverseGroundState m α R bd) (Ccap : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ) : Prop where
  /-- The two cap decompositions of `lem:cap` exist at this radius. -/
  cap : ∃ Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ,
    (∀ u, 0 ≤ Gm u) ∧ (∀ u, 0 ≤ Gp u) ∧
    (∀ u, (Cm.beta α - Ccap * R) * (axialRep_gm hR hL gs u).toFun 0 ^ 2
            + (2 * R)⁻¹ * Gm u
          ≤ capEnergyL_gm α gs.nu hR hL bdCapL u) ∧
    (∀ u, (Cp.beta α - Ccap * R)
              * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
            + (2 * R)⁻¹ * Gp u
          ≤ capEnergyR_gm α gs.nu hR hL bdCapR u) ∧
    (∀ u, massP (restrictLeft hR hL u)
          ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun 0 ^ 2 + Ccap * R * Gm u) ∧
    (∀ u, massP (restrictRight hR hL u)
          ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
              + Ccap * R * Gp u)

end Interface

/-! ## Part 3: `eq:Z-definition` and the two global bounds, generically -/

section Estimates

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- **`eq:Z-definition`**, at the level of representatives, for a generic ground state. -/
def Zrep_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (gs : TransverseGroundState m α R bd)
    (C₀ : ℝ) (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  massP (bulkRemainder (interface_lt hR hL) gs (restrictBulkP hR u))
    + C₀ * R * (Gm u + Gp u)

theorem Zrep_nonneg_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ} (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ Zrep_gm hR hL gs C₀ Gm Gp u := by
  have h1 : 0 ≤ massP (bulkRemainder (interface_lt hR hL) gs (restrictBulkP hR u)) :=
    massP_nonneg _
  have h2 : 0 ≤ C₀ * R * (Gm u + Gp u) := by
    have h3 := hGm u
    have h4 := hGp u
    have h5 : (0 : ℝ) ≤ R := hR.le
    positivity
  rw [Zrep_gm]
  linarith

/-- **`eq:global-energy-lower`, at the level of representatives, for a generic ground state and
a generic trace datum.** -/
theorem lower_rep_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd)
    (hsl : BdSliceable (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R) bd)
    {td : TraceData Cm Cp L R} {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hs : TraceSplitInput_gm hR td bd bdCapL bdCapR)
    {Ccap C C₀ c₀ cgap : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hcapL : ∀ u, (Cm.beta α - Ccap * R) * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + (2 * R)⁻¹ * Gm u ≤ capEnergyL_gm α gs.nu hR hL bdCapL u)
    (hcapR : ∀ u, (Cp.beta α - Ccap * R)
          * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * Gp u ≤ capEnergyR_gm α gs.nu hR hL bdCapR u)
    (hgap : cgap ≤ gs.gapConst)
    (hCC : Ccap ≤ C) (hc₀gap : c₀ ≤ cgap) (hc₀C₀ : c₀ * C₀ ≤ 1 / 2)
    (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.robinForm (Cm.beta α - C * R) (Cp.beta α - C * R) (bulkLength Cm Cp L R)
          (axialRep_gm hR hL gs u)
        + c₀ / R ^ 2 * Zrep_gm hR hL gs C₀ Gm Gp u
      ≤ dirichletP u + α * td.bd u u - gs.nu * massP u := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hZW0 : 0 ≤ massP (bulkRemainder (interface_lt hR hL) gs (restrictBulkP hR u)) :=
    massP_nonneg _
  have hG : 0 ≤ Gm u + Gp u := by linarith [hGm u, hGp u]
  have hD := dirichlet_axialRep_gm hR hL gs u
  have hbulk := bulk_separation (interface_lt hR hL) gs hsl (restrictBulkP hR u)
  rw [← hD] at hbulk
  have hsplit := energy_split_gm (α := α) hR hL hs gs.nu u
  have hcl := hcapL u
  have hcr := hcapR u
  -- the two spectral absorptions
  have e1 : c₀ / R ^ 2 * massP (bulkRemainder (interface_lt hR hL) gs (restrictBulkP hR u))
      ≤ gs.gapConst * R⁻¹ ^ 2
        * massP (bulkRemainder (interface_lt hR hL) gs (restrictBulkP hR u)) := by
    refine mul_le_mul_of_nonneg_right ?_ hZW0
    have hle : c₀ ≤ gs.gapConst := le_trans hc₀gap hgap
    have hrw : c₀ / R ^ 2 = c₀ * (R ^ 2)⁻¹ := by ring
    rw [hrw, inv_pow]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hcoef : c₀ / R ^ 2 * (C₀ * R) ≤ (2 * R)⁻¹ := by
    have h1 : c₀ / R ^ 2 * (C₀ * R) = c₀ * C₀ * R⁻¹ := by field_simp
    have h2 : (2 * R)⁻¹ = 1 / 2 * R⁻¹ := by field_simp
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right hc₀C₀ (by positivity)
  have e2 : c₀ / R ^ 2 * (C₀ * R * (Gm u + Gp u)) ≤ (2 * R)⁻¹ * (Gm u + Gp u) := by
    calc c₀ / R ^ 2 * (C₀ * R * (Gm u + Gp u))
        = c₀ / R ^ 2 * (C₀ * R) * (Gm u + Gp u) := by ring
      _ ≤ (2 * R)⁻¹ * (Gm u + Gp u) := mul_le_mul_of_nonneg_right hcoef hG
  -- weakening the two endpoint coefficients from `Ccap` to `C`
  have hendL : (Cm.beta α - C * R) * (axialRep_gm hR hL gs u).toFun 0 ^ 2
      ≤ (Cm.beta α - Ccap * R) * (axialRep_gm hR hL gs u).toFun 0 ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hCC, hR.le]
  have hendR : (Cp.beta α - C * R)
        * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
      ≤ (Cp.beta α - Ccap * R)
        * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hCC, hR.le]
  rw [Sobolev.robinForm, Zrep_gm, mul_add]
  linarith [hbulk, hcl, hcr, e1, e2, hendL, hendR, hsplit]

/-- **`eq:global-mass-upper`, at the level of representatives, for a generic ground state.** -/
theorem upper_rep_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd)
    {Ccap C C₀ Ctrace : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hCcap : 0 ≤ Ccap) (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hmassL : ∀ u, massP (restrictLeft hR hL u)
        ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun 0 ^ 2 + Ccap * R * Gm u)
    (hmassR : ∀ u, massP (restrictRight hR hL u)
        ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
            + Ccap * R * Gp u)
    (htrace : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
        v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
          ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
              + Sobolev.dirichlet (bulkLength Cm Cp L R) v))
    (hCC : Ccap * Ctrace ≤ C) (hC₀ : Ccap ≤ C₀)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP u
      ≤ (1 + C * R) * Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
        + C * R * Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
        + Zrep_gm hR hL gs C₀ Gm Gp u := by
  have hℓ : (0 : ℝ) < bulkLength Cm Cp L R := trialAC_bulkLength_pos hL
  have hMW : 0 ≤ Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u) :=
    Sobolev.mass_nonneg _ _ hℓ.le
  have hDW : 0 ≤ Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u) :=
    Sobolev.dirichlet_nonneg _ _ hℓ.le
  have hsum := massP_eq_sum hR hL u
  rw [restrictBulk_eq_restrictBulkP_gm hR hL] at hsum
  have hM := mass_axialRep_gm hR hL gs u
  have hbulkmass := bulk_mass_split (interface_lt hR hL) gs (restrictBulkP hR u)
  rw [← hM] at hbulkmass
  have hml := hmassL u
  have hmr := hmassR u
  have htr := htrace (axialRep_gm hR hL gs u)
  have hGsum : 0 ≤ Gm u + Gp u := by linarith [hGm u, hGp u]
  have hRG : 0 ≤ R * (Gm u + Gp u) := mul_nonneg hR.le hGsum
  have habsG : Ccap * R * Gm u + Ccap * R * Gp u ≤ C₀ * R * (Gm u + Gp u) := by
    have h : 0 ≤ (C₀ - Ccap) * (R * (Gm u + Gp u)) := mul_nonneg (by linarith) hRG
    nlinarith [h]
  have hnn : 0 ≤ R * (Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
      + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)) := by
    have hR' : (0 : ℝ) ≤ R := hR.le
    positivity
  have habs : Ccap * R * ((axialRep_gm hR hL gs u).toFun 0 ^ 2
        + (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2)
      ≤ C * R * (Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
          + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)) := by
    have h1 : Ccap * R * ((axialRep_gm hR hL gs u).toFun 0 ^ 2
          + (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2)
        ≤ Ccap * R * (Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
            + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u))) :=
      mul_le_mul_of_nonneg_left htr (mul_nonneg hCcap hR.le)
    have h2 : 0 ≤ (C - Ccap * Ctrace) * (R
        * (Sobolev.mass (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u)
          + Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs u))) :=
      mul_nonneg (by linarith) hnn
    nlinarith [h1, h2]
  rw [Zrep_gm]
  linarith [hsum, hbulkmass, hml, hmr, habs, habsG]

end Estimates

/-! ## Part 4: the `GlobalComparisonData` instance at one radius, generically -/

section Data

variable {m : ℕ} {Cm Cp : Cap m} {L R α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-- `eq:Z-definition` on the a.e. quotient, through the chosen representative `qrep_a1`. -/
def Zone_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (gs : TransverseGroundState m α R bd)
    (C₀ : ℝ) (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (w : H1PQ (thinDomain Cm Cp L R)) : ℝ :=
  Zrep_gm hR hL gs C₀ Gm Gp (qrep_a1 w)

theorem Zone_eq_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (gs : TransverseGroundState m α R bd)
    (C₀ : ℝ) (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (w : H1PQ (thinDomain Cm Cp L R)) :
    Zone_gm hR hL gs C₀ Gm Gp w = Zrep_gm hR hL gs C₀ Gm Gp (qrep_a1 w) := rfl

/-- **The bulk/cap decomposition data of `sec:proof` at one radius, for a general transverse
dimension `m` and an arbitrary transverse ground state `gs`.** -/
theorem globalComparisonData_gm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (gs : TransverseGroundState m α R bd)
    (hsl : BdSliceable (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R) bd)
    {td : TraceData Cm Cp L R} {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hs : TraceSplitInput_gm hR td bd bdCapL bdCapR)
    {Ccap C C₀ c₀ cgap Ctrace Ctr : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hCcap : 0 ≤ Ccap) (hC₀0 : 0 ≤ C₀)
    (hgap : cgap ≤ gs.gapConst)
    (hCC : Ccap ≤ C) (hCCt : Ccap * Ctrace ≤ C) (hCtrC : Ctr ≤ C) (hC₀ : Ccap ≤ C₀)
    (hc₀gap : c₀ ≤ cgap) (hc₀C₀ : c₀ * C₀ ≤ 1 / 2)
    (htrace : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
        v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
          ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
              + Sobolev.dirichlet (bulkLength Cm Cp L R) v))
    (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hcapL : ∀ u, (Cm.beta α - Ccap * R) * (axialRep_gm hR hL gs u).toFun 0 ^ 2
        + (2 * R)⁻¹ * Gm u ≤ capEnergyL_gm α gs.nu hR hL bdCapL u)
    (hcapR : ∀ u, (Cp.beta α - Ccap * R)
          * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * Gp u ≤ capEnergyR_gm α gs.nu hR hL bdCapR u)
    (hmassL : ∀ u, massP (restrictLeft hR hL u)
        ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun 0 ^ 2 + Ccap * R * Gm u)
    (hmassR : ∀ u, massP (restrictRight hR hL u)
        ≤ Ccap * R * (axialRep_gm hR hL gs u).toFun (bulkLength Cm Cp L R) ^ 2
            + Ccap * R * Gp u)
    (htrial : ∀ v : Sobolev.H1Q (bulkLength Cm Cp L R),
        robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
              (liftQ hR hL gs.psi v)
            - gs.nu * massPQ (liftQ hR hL gs.psi v)
          ≤ robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R) (bulkLength Cm Cp L R) v) :
    Nonempty (GlobalComparisonData Cm Cp L α hR hL td gs.nu C c₀) := by
  refine ⟨{
    π := bulkProjThin hR hL gs.psi.memL2 (psi_normalized_integral gs)
    π_surj := bulkProjThin_surjective_trialAC hR hL gs.psi (psi_normalized_integral gs)
    Z := Zone_gm hR hL gs C₀ Gm Gp
    Z_nonneg := fun w => Zrep_nonneg_gm hR hL gs hC₀0 hGm hGp (qrep_a1 w)
    lift := liftQ hR hL gs.psi
    trial_mass := massQ_le_massPQ_liftQ hR hL gs.psi gs.normalized
    lower := ?_
    upper := ?_
    trial_energy := ?_ }⟩
  · intro w
    have hw : (Submodule.Quotient.mk (qrep_a1 w) : H1PQ (thinDomain Cm Cp L R)) = w :=
      qrep_mk_a1 w
    have hpi := bulkProjThin_mk_gm hR hL gs (qrep_a1 w)
    rw [hw] at hpi
    have hq := robinFormPQ_mk (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α (qrep_a1 w)
    rw [hw] at hq
    have hm := massPQ_mk (qrep_a1 w)
    rw [hw] at hm
    rw [hpi, Sobolev.robinFormQ_mk, hq, hm, Zone_eq_gm]
    exact lower_rep_gm hR hL gs hsl hs hGm hGp hcapL hcapR hgap hCC hc₀gap hc₀C₀ (qrep_a1 w)
  · intro w
    have hw : (Submodule.Quotient.mk (qrep_a1 w) : H1PQ (thinDomain Cm Cp L R)) = w :=
      qrep_mk_a1 w
    have hpi := bulkProjThin_mk_gm hR hL gs (qrep_a1 w)
    rw [hw] at hpi
    have hm := massPQ_mk (qrep_a1 w)
    rw [hw] at hm
    have hrf : Sobolev.robinForm 0 0 (bulkLength Cm Cp L R) (axialRep_gm hR hL gs (qrep_a1 w))
        = Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRep_gm hR hL gs (qrep_a1 w)) := by
      rw [Sobolev.robinForm]; ring
    rw [hpi, Sobolev.massQ_mk, Sobolev.robinFormQ_mk, hrf, hm, Zone_eq_gm]
    exact upper_rep_gm hR hL gs hCcap hGm hGp hmassL hmassR htrace hCCt hC₀ (qrep_a1 w)
  · intro v
    refine le_trans (htrial v) ?_
    refine Sobolev.robinFormQ_mono ?_ ?_ v <;> nlinarith [hCtrC, hR.le]

end Data

/-! ## Part 4b: the ground-state family interface -/

/-- **A family of transverse ground states, uniform in the radius.**

This packages exactly what `groundStateOne`/`groundStateOne_gap_quant`/`nuOneDim` supply for
`m = 1`: a boundary form `bd R` and a ground state `gs R` at every admissible radius, the
sliceability of `bd R` (needed by `bulk_separation`), the ground-state energy as a genuine
function `nu' : ℝ → ℝ` of `R` alone (as required by `MainTheorem`/`GlobalComparison`), and a
uniform lower bound `cgap` for the spectral gap constant below the threshold `Rgap`. -/
structure GroundStateFamily_gm (m : ℕ) (α R₀ : ℝ) where
  /-- The transverse boundary form at radius `R`. -/
  bd : ∀ R : ℝ, TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ
  /-- The transverse ground state at every admissible radius. -/
  gs : ∀ (R : ℝ), 0 < R → R < R₀ → TransverseGroundState m α R (bd R)
  /-- `bd R` is sliceable on every bulk cylinder, at every admissible radius. -/
  hsl : ∀ (R : ℝ) (hR : 0 < R), R < R₀ → ∀ a b : ℝ, BdSliceable a b (bd R)
  /-- The ground-state energy, as a function of `R` alone. -/
  nu' : ℝ → ℝ
  /-- `nu'` computes the ground-state energy of the family. -/
  nu'_eq : ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀), (gs R hR hR₀).nu = nu' R
  /-- The constant of the uniform spectral gap. -/
  cgap : ℝ
  /-- The uniform gap constant is positive. -/
  cgap_pos : 0 < cgap
  /-- The threshold radius below which the uniform gap bound holds. -/
  Rgap : ℝ
  /-- The gap threshold is positive. -/
  Rgap_pos : 0 < Rgap
  /-- **The uniform spectral gap**: below the threshold `Rgap`, `cgap` lower-bounds the gap
  constant of every ground state of the family. -/
  gapConst_ge : ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀), R < Rgap → cgap ≤ (gs R hR hR₀).gapConst

/-! ## Part 5: the generic global comparison, `thm:main` and `cor:counterexample` -/

section Final

set_option linter.unusedVariables false

variable {m : ℕ}

/-- **The trace-split interface for a whole trace family, generically.**

For every admissible radius the trace datum `tdf R hR hR₀` splits into two cap pieces and the
cylinder form of the bulk (`TraceSplitInput_gm`, w.r.t. the family's boundary form `gsf.bd R`),
*and* `lem:cap` holds for those very cap pieces (`CapLowerInput_gm`, w.r.t. the family's ground
state `gsf.gs R hR hR₀`). -/
structure TraceSplitFamilyInput_gm (Cm Cp : Cap m) (L α : ℝ) (Ccap R₀ : ℝ)
    (gsf : GroundStateFamily_gm m α R₀) (tdf : TraceFamily Cm Cp L R₀) : Prop where
  /-- Split and cap lower bound, at every admissible radius, with matching cap pieces. -/
  data : ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) (hL : (Cm.K + Cp.K) * R < L),
    ∃ bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ,
      TraceSplitInput_gm hR (tdf R hR hR₀) (gsf.bd R) bdCapL bdCapR ∧
      CapLowerInput_gm (gsf.gs R hR hR₀) Ccap hR hL bdCapL bdCapR

/-- **`eq:interval-trace` / `eq:cap-rescale`, generically: a recorded interface hypothesis**
(the generic copy of `InterfaceTraceInput_a1`): it is not used by the assembly below (exactly as
in `AssemblyOne.lean`/`AssemblyOneGen.lean`), only carried in the signatures to record that it is
what justifies writing the entrance pairing `p_∓` of `CapLowerInput_gm` as `F(x_∓)`. -/
structure InterfaceTraceInput_gm (Cm Cp : Cap m) (L α : ℝ) (Cif R₀ : ℝ)
    (gsf : GroundStateFamily_gm m α R₀) : Prop where
  /-- The two interface values and their two properties. -/
  iface : ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) (hL : (Cm.K + Cp.K) * R < L)
      (u : H1P (thinDomain Cm Cp L R)),
    ∃ fm fp : EuclideanSpace ℝ (Fin m) → ℝ,
      MemLp fm 2 (volume.restrict (transverseBall m R)) ∧
      MemLp fp 2 (volume.restrict (transverseBall m R)) ∧
      (axialRep_gm hR hL (gsf.gs R hR hR₀) u).toFun 0
        = ∫ z in transverseBall m R, fm z * (gsf.gs R hR hR₀).psi.toFun z ∧
      (axialRep_gm hR hL (gsf.gs R hR hR₀) u).toFun (bulkLength Cm Cp L R)
        = ∫ z in transverseBall m R, fp z * (gsf.gs R hR hR₀).psi.toFun z ∧
      (∫ z in transverseBall m R, fm z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u)) ∧
      (∫ z in transverseBall m R, fp z ^ 2)
        ≤ Cif * (massP (restrictBulkP hR u) + axialDirichletP (restrictBulkP hR u))

/-- **`eq:trial-energy` for a generic trace family and a generic ground-state family**: the
generic copy of `TrialEnergyInput_ag`. -/
structure TrialEnergyInput_gm (Cm Cp : Cap m) (L α : ℝ) (Ctr R₀ : ℝ)
    (gsf : GroundStateFamily_gm m α R₀) (tdf : TraceFamily Cm Cp L R₀) : Prop where
  /-- `E_R[T_R F] ≤ a_{β₋+CR, β₊+CR; I_R}[F]`. -/
  trial : ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) (hL : (Cm.K + Cp.K) * R < L)
      (v : Sobolev.H1Q (bulkLength Cm Cp L R)),
    robinFormPQ (isOpen_thinDomain hR hL) (tdf R hR hR₀).bd (tdf R hR hR₀).vanishesOnNullAEP α
          (liftQ hR hL (gsf.gs R hR hR₀).psi v)
        - (gsf.gs R hR hR₀).nu * massPQ (liftQ hR hL (gsf.gs R hR hR₀).psi v)
      ≤ robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R) (bulkLength Cm Cp L R) v

/-- **The global comparison of `sec:proof`, for a general transverse dimension `m` and an
arbitrary ground-state family.**

The constants are `C = max (max C_cap (C_cap C_ℓ)) C_trial`, `C₀ = max C_cap 1`,
`c₀ = min c_gap (2C₀)^{-1}`, and the threshold is
`R₁ = min R₀ (min R_gap (L / (2(K₋+K₊))))`. -/
theorem globalComparison_gm (Cm Cp : Cap m) (L α : ℝ) (hL0 : 0 < L)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (gsf : GroundStateFamily_gm m α R₀) (tdf : TraceFamily Cm Cp L R₀)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hsplit : TraceSplitFamilyInput_gm Cm Cp L α Ccap R₀ gsf tdf)
    (hif : InterfaceTraceInput_gm Cm Cp L α Cif R₀ gsf)
    (htr : TrialEnergyInput_gm Cm Cp L α Ctr R₀ gsf tdf) :
    GlobalComparison Cm Cp L α gsf.nu' R₀ tdf := by
  obtain ⟨Ctrace, hCtrace0, htraceu⟩ := Sobolev.trace_ineq_uniform L hL0
  have hKK : 0 < Cm.K + Cp.K := by linarith [Cm.hK, Cp.hK]
  set C₀ : ℝ := max Ccap 1 with hC₀def
  set C : ℝ := max (max Ccap (Ccap * Ctrace)) Ctr with hCdef
  set c₀ : ℝ := min gsf.cgap (1 / (2 * C₀)) with hc₀def
  set R₁ : ℝ := min R₀ (min gsf.Rgap (L / (2 * (Cm.K + Cp.K)))) with hR₁def
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₀0 : 0 ≤ C₀ := hC₀pos.le
  have hC₀le : Ccap ≤ C₀ := le_max_left _ _
  have hCC : Ccap ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCCt : Ccap * Ctrace ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCtrC : Ctr ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := le_trans hCcap hCC
  have hc₀pos : 0 < c₀ := lt_min gsf.cgap_pos (by positivity)
  have hc₀gap : c₀ ≤ gsf.cgap := min_le_left _ _
  have hc₀C₀ : c₀ * C₀ ≤ 1 / 2 := by
    have h1 : c₀ ≤ 1 / (2 * C₀) := min_le_right _ _
    have h2 : c₀ * C₀ ≤ 1 / (2 * C₀) * C₀ := mul_le_mul_of_nonneg_right h1 hC₀0
    have h3 : 1 / (2 * C₀) * C₀ = 1 / 2 := by field_simp
    linarith
  have hR₁pos : 0 < R₁ := lt_min hR₀ (lt_min gsf.Rgap_pos (by positivity))
  have hR₁R₀ : R₁ ≤ R₀ := min_le_left _ _
  refine ⟨C, c₀, R₁, hC0, hc₀pos, hR₁pos, hR₁R₀, ?_⟩
  intro R hR hRR₀ hRR₁ hLR
  have hRRgap : R < gsf.Rgap :=
    lt_of_lt_of_le hRR₁ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRKK : R < L / (2 * (Cm.K + Cp.K)) :=
    lt_of_lt_of_le hRR₁ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hKKR : (Cm.K + Cp.K) * R < L / 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Cm.K + Cp.K))] at hRKK
    linarith
  have hℓlow : L / 2 ≤ bulkLength Cm Cp L R := by
    simp only [Domain.bulkLength]; linarith
  have hℓhigh : bulkLength Cm Cp L R ≤ L := by
    simp only [Domain.bulkLength]
    nlinarith [hKK, hR.le]
  have htraceR : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
      v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
        ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
            + Sobolev.dirichlet (bulkLength Cm Cp L R) v) := by
    intro v
    simpa only [sq_abs] using htraceu (bulkLength Cm Cp L R) hℓlow hℓhigh v
  obtain ⟨bdCapL, bdCapR, hts, hcap⟩ := hsplit.data R hR hRR₀ hLR
  obtain ⟨Gm, Gp, hGm, hGp, hcapL, hcapR, hmassL, hmassR⟩ := hcap.cap
  have htrialR := htr.trial R hR hRR₀ hLR
  rw [← gsf.nu'_eq R hR hRR₀]
  exact globalComparisonData_gm hR hLR (gsf.gs R hR hRR₀)
    (gsf.hsl R hR hRR₀ (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)) hts hCcap hC₀0
    (gsf.gapConst_ge R hR hRR₀ hRRgap) hCC hCCt hCtrC hC₀le hc₀gap hc₀C₀ htraceR hGm hGp hcapL
    hcapR hmassL hmassR htrialR

/-- **`thm:main`, for a general transverse dimension `m` and an arbitrary ground-state family**
satisfying the trace-split interface. -/
theorem mainTheorem_gm (Cm Cp : Cap m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (gsf : GroundStateFamily_gm m α R₀) (tdf : TraceFamily Cm Cp L R₀)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hsplit : TraceSplitFamilyInput_gm Cm Cp L α Ccap R₀ gsf tdf)
    (hif : InterfaceTraceInput_gm Cm Cp L α Cif R₀ gsf)
    (htr : TrialEnergyInput_gm Cm Cp L α Ctr R₀ gsf tdf) :
    MainTheorem m Cm Cp L α hL0 hβm hβp gsf.nu' R₀ tdf :=
  mainTheorem_of_globalComparison m Cm Cp L α hL0 hα.le hβm hβp gsf.nu' R₀ tdf
    (globalComparison_gm Cm Cp L α hL0 R₀ hR₀ gsf tdf hCcap hsplit hif htr)

/-- **`cor:counterexample`, for a general transverse dimension `m ≥ 1`**, for an arbitrary trace
family and ground-state family on the capsule with two hemispherical caps. -/
theorem counterexample_gm (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (gsf : GroundStateFamily_gm m α R₀)
    (tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hsplit : TraceSplitFamilyInput_gm (hemisphere m) (hemisphere m) L α Ccap R₀ gsf tdf)
    (hif : InterfaceTraceInput_gm (hemisphere m) (hemisphere m) L α Cif R₀ gsf)
    (htr : TrialEnergyInput_gm (hemisphere m) (hemisphere m) L α Ctr R₀ gsf tdf) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L)
        (hR₀' : R < R₀),
      lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
          - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
        ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
      lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
          - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
        < Interval.gap L hL0 α ∧
      euclidDiam (thinDomain (hemisphere m) (hemisphere m) L R) = L :=
  counterexample_of_mainTheorem' m hm L α hL0 hα gsf.nu' R₀ hR₀ tdf
    (mainTheorem_gm (hemisphere m) (hemisphere m) L α hL0 hα
      (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) R₀ hR₀ gsf tdf
      hCcap hsplit hif htr)

end Final

/-! ## Part 6: consistency — the `m = 1` results of `AssemblyOneGen.lean`, re-derived -/

section Consistency

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- **`axialRep_gm` at `m = 1`, `bd := bdTr R`, `gs := groundStateOne …`, is exactly
`axialRepOne_a1`.** Both sides unfold, through `psi_normalized_integral`/`psiOne_normalized_a1`
(the same proof term of the same proposition, by `Prop` proof irrelevance), to the same
`bulkRepT` application. -/
theorem axialRep_gm_eq_axialRepOne_a1 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    (u : H1P (thinDomain Cm Cp L R)) :
    axialRep_gm hR hL (groundStateOne α R hα hR) u = axialRepOne_a1 hR hL hα u := rfl

/-- **The `GroundStateFamily_gm 1 α R₀` built from `groundStateOne`.**  This packages exactly
`groundStateOne`, `groundStateOne_gap_quant`, `nuOneDim`/`nuOneDim_eq` and `bdSliceable_bdTr`. -/
def groundStateFamilyOne_gm (α R₀ : ℝ) (hα : 0 < α) : GroundStateFamily_gm 1 α R₀ :=
  { bd := fun R => bdTr R
    gs := fun R hR _ => groundStateOne α R hα hR
    hsl := fun R hR _ a b => bdSliceable_bdTr hR a b
    nu' := nuOneDim α hα
    nu'_eq := fun R hR _ => (nuOneDim_eq α hα hR).symm
    cgap := (groundStateOne_gap_quant α hα).choose
    cgap_pos := (groundStateOne_gap_quant α hα).choose_spec.choose_spec.1
    Rgap := (groundStateOne_gap_quant α hα).choose_spec.choose
    Rgap_pos := (groundStateOne_gap_quant α hα).choose_spec.choose_spec.2.1
    gapConst_ge := fun R hR _ hRgap' =>
      (groundStateOne_gap_quant α hα).choose_spec.choose_spec.2.2 R hR hRgap' }

/-- The trace-split interface for `traceDataOne`-style data converts directly from
`TraceSplitInput_ag` to `TraceSplitInput_gm` at `bd := bdTr R`: the two structures have exactly
the same fields once `bd` is fixed. -/
theorem traceSplitInput_gm_of_ag {hR : 0 < R} {td : TraceData Cm Cp L R}
    {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hs : TraceSplitInput_ag hR td bdCapL bdCapR) :
    TraceSplitInput_gm hR td (bdTr R) bdCapL bdCapR :=
  ⟨hs.bdCapL_nonneg, hs.bdCapR_nonneg, hs.split⟩

/-- `CapLowerInput_ag` converts directly to `CapLowerInput_gm` at `gs := groundStateOne …`: by
`axialRep_gm_eq_axialRepOne_a1` and `(groundStateOne α R hα hR).nu = nuR α R hα hR` (definitional),
the two existential statements are the same up to unfolding. -/
theorem capLowerInput_gm_of_ag {hR : 0 < R} {hL : (Cm.K + Cp.K) * R < L} {hα : 0 < α}
    {Ccap : ℝ} {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hcap : CapLowerInput_ag hα Ccap hR hL bdCapL bdCapR) :
    CapLowerInput_gm (groundStateOne α R hα hR) Ccap hR hL bdCapL bdCapR :=
  ⟨hcap.cap⟩

/-- **Consistency check.**  `globalComparisonData_gen_ag` of `AssemblyOneGen.lean`, re-derived by
instantiating the generic `globalComparisonData_gm` at `m := 1`, `bd := bdTr R`,
`gs := groundStateOne α R hα hR`, `hsl := bdSliceable_bdTr hR …`. -/
theorem globalComparisonData_gen_ag' (hα : 0 < α) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {td : TraceData Cm Cp L R} {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hs : TraceSplitInput_ag hR td bdCapL bdCapR)
    {Ccap C C₀ c₀ cgap Ctrace Ctr : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hCcap : 0 ≤ Ccap) (hC₀0 : 0 ≤ C₀)
    (hgap : cgap ≤ (groundStateOne α R hα hR).gapConst)
    (hCC : Ccap ≤ C) (hCCt : Ccap * Ctrace ≤ C) (hCtrC : Ctr ≤ C) (hC₀ : Ccap ≤ C₀)
    (hc₀gap : c₀ ≤ cgap) (hc₀C₀ : c₀ * C₀ ≤ 1 / 2)
    (htrace : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
        v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
          ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
              + Sobolev.dirichlet (bulkLength Cm Cp L R) v))
    (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hcapL : ∀ u, (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
        + (2 * R)⁻¹ * Gm u ≤ capEnergyL_ag α (nuR α R hα hR) hR hL bdCapL u)
    (hcapR : ∀ u, (Cp.beta α - Ccap * R)
          * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * Gp u ≤ capEnergyR_ag α (nuR α R hα hR) hR hL bdCapR u)
    (hmassL : ∀ u, massP (restrictLeft hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 + Ccap * R * Gm u)
    (hmassR : ∀ u, massP (restrictRight hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
            + Ccap * R * Gp u)
    (htrial : ∀ v : Sobolev.H1Q (bulkLength Cm Cp L R),
        robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
              (liftQ hR hL (psiOne_a1 α R hα hR) v)
            - nuR α R hα hR * massPQ (liftQ hR hL (psiOne_a1 α R hα hR) v)
          ≤ robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R) (bulkLength Cm Cp L R) v) :
    Nonempty (GlobalComparisonData Cm Cp L α hR hL td (nuR α R hα hR) C c₀) :=
  globalComparisonData_gm hR hL (groundStateOne α R hα hR)
    (bdSliceable_bdTr hR (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R))
    (traceSplitInput_gm_of_ag hs) hCcap hC₀0 hgap hCC hCCt hCtrC hC₀ hc₀gap hc₀C₀ htrace hGm hGp
    hcapL hcapR hmassL hmassR htrial

/-- **Consistency check, top-level.**  `mainTheorem_gen_ag` of `AssemblyOneGen.lean`, re-derived
from `mainTheorem_gm` via `groundStateFamilyOne_gm`. -/
theorem mainTheorem_gen_ag' (Cm Cp : Cap 1) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (tdf : TraceFamily Cm Cp L R₀)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hsplit : TraceSplitFamilyInput_ag Cm Cp L α hα Ccap R₀ tdf)
    (hif : InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀)
    (htr : TrialEnergyInput_ag Cm Cp L α hα Ctr R₀ tdf) :
    MainTheorem 1 Cm Cp L α hL0 hβm hβp (nuOneDim α hα) R₀ tdf := by
  refine mainTheorem_gm (Ccap := Ccap) (Cif := Cif) (Ctr := Ctr)
    Cm Cp L α hL0 hα hβm hβp R₀ hR₀ (groundStateFamilyOne_gm α R₀ hα) tdf hCcap ?_ ?_ ?_
  · refine ⟨fun R hR hR₀' hL => ?_⟩
    obtain ⟨bdCapL, bdCapR, hts, hcap⟩ := hsplit.data R hR hR₀' hL
    exact ⟨bdCapL, bdCapR, traceSplitInput_gm_of_ag hts, capLowerInput_gm_of_ag hcap⟩
  · exact ⟨fun R hR hR₀' hL u => by
      obtain ⟨fm, fp, hfm, hfp, hem, hep, hbm, hbp⟩ := hif.iface R hR hR₀' hL u
      exact ⟨fm, fp, hfm, hfp, hem, hep, hbm, hbp⟩⟩
  · exact ⟨fun R hR hR₀' hL v => htr.trial R hR hR₀' hL v⟩

end Consistency

end RobinCaps.ThinDomain

end
