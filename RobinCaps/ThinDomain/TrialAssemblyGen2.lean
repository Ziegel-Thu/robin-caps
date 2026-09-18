import RobinCaps.ThinDomain.TrialAssemblyMixed

/-!
# The trial side of the global comparison, arbitrary cap pair, weak ground state

`RobinCaps/ThinDomain/TrialAssemblyMixed.lean` proves the `trial_energy` field of
`RobinCaps.ThinDomain.GlobalComparisonData` for a **weak** transverse ground state, at the
**mixed** thin domain `thinDomain (Cap.flat m K hK) (Cap.hemisphere m) L R`. Its §3–§6 (the
`GenericCaps` section: `toFun_capLeft_trialAC_tam`, `toFun_capRight_trialAC_tam`,
`bdΓ_congr_ae_tam`, `bdΓ_capLeft_tam`, `bdΓ_capRight_tam`, `massP_leftCap_tam`,
`massP_rightCap_tam`, `dirichletP_leftCap_tam`, `dirichletP_rightCap_tam`, `bdCyl_bulk_tam`) are
already stated for an **arbitrary** pair of caps `Cm Cp : Cap m` — they are reused verbatim here.

This file redoes §1, §2, §7, §8 of `TrialAssemblyMixed.lean` for an arbitrary pair `Cm Cp : Cap m`
with abstract trace data `tdM : CapTraceData Cm`, `tdP : CapTraceData Cp` on each side.

## Contents

1. `TraceSplitGen2_ag2` — the trace-split interface for an arbitrary cap pair, the general
   analogue of `TraceSplitMixed_tam`.
2. `capEnergyTermGen_ag2` — the renormalized cap energy term for an arbitrary cap with abstract
   trace data; `capEnergyTermGen_eq_taw_ag2`/`capEnergyTermGen_eq_tam_ag2` identify it (by `rfl`)
   with `capEnergyTermW_taw`/`capEnergyTermL_tam` at the hemisphere/flat caps.
3. `bd_trialAC_ag2`, `renormEnergy_trialAC_ag2` — assembled at an arbitrary `Cm Cp : Cap m`.
4. `trial_energy_field_ag2` — the `trial_energy` field of `GlobalComparisonData` for an arbitrary
   cap pair.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain RobinCaps.Cap RobinCaps.Compact

noncomputable section

variable {m : ℕ} {α R L : ℝ} {Cm Cp : Cap m}

/-! ## 1. The trace-split interface for an arbitrary cap pair -/

/-- The trace split of a thin-domain trace datum for an arbitrary cap pair with abstract
cap trace data — the general analogue of `TraceSplitMixed_tam`. -/
def TraceSplitGen2_ag2 (Cm Cp : Cap m) (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) : Prop :=
  ∀ u : H1P (thinDomain Cm Cp L R),
    td.bd u u
      = R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 *
          tdM.bdΓ (capLeft hR hL (R ^ ((m : ℝ) / 2)) u) (capLeft hR hL (R ^ ((m : ℝ) / 2)) u)
        + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
        + R ^ m * (R ^ ((m : ℝ) / 2))⁻¹ ^ 2 *
          tdP.bdΓ (capRight hR hL (R ^ ((m : ℝ) / 2)) u) (capRight hR hL (R ^ ((m : ℝ) / 2)) u)

/-! ## 2. The cap energy term for an arbitrary cap -/

/-- **The renormalized cap energy term for an arbitrary cap with abstract trace data.**
Same shape as `capEnergyTermW_taw`/`capEnergyTermL_tam`, with an arbitrary `C.body`/`td.bdΓ` in
place of the hemisphere/flat-cap specialisations. -/
def capEnergyTermGen_ag2 (C : Cap m) (td : CapTraceData C) (α R : ℝ)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (Φ : H1P C.body) : ℝ :=
  R⁻¹ * (∫ p in C.body, ‖Φ.gz p‖ ^ 2)
    + (α * td.bdΓ Φ Φ - (m : ℝ) * α * massP Φ)
    - (R * gs.nu - (m : ℝ) * α) * massP Φ

/-- `capEnergyTermGen_ag2` at the hemispherical cap agrees with `capEnergyTermW_taw`. -/
theorem capEnergyTermGen_eq_taw_ag2 (m : ℕ) (hm : 1 ≤ m) {α R : ℝ}
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (Φ : H1P (Cap.hemisphere m).body) :
    capEnergyTermGen_ag2 (Cap.hemisphere m) (Cap.capTraceDataHemi_th m hm) α R gs Φ
      = capEnergyTermW_taw m hm α R gs Φ := rfl

/-- `capEnergyTermGen_ag2` at the flat cap agrees with `capEnergyTermL_tam`. -/
theorem capEnergyTermGen_eq_tam_ag2 (m : ℕ) (K : ℝ) (hK : 0 < K)
    (tdF : CapTraceData (Cap.flat m K hK)) {α R : ℝ}
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (Φ : H1P (Cap.flat m K hK).body) :
    capEnergyTermGen_ag2 (Cap.flat m K hK) tdF α R gs Φ
      = capEnergyTermL_tam m K hK tdF α R gs Φ := rfl

/-! ## 3. The trace split of the trial extension, arbitrary cap pair -/

/-- **`bd_trialAC_ag2`: the trace split of the trial extension, for a weak transverse ground
state, at an arbitrary cap pair with abstract trace data.** -/
theorem bd_trialAC_ag2 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (W : Sobolev.H1 (bulkLength Cm Cp L R))
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (td : TraceData Cm Cp L R) (hsplit : TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL td)
    (ΦL : H1P Cm.body) (hΦL : ΦL.toFun = fun p => transLift m R gs.psi p.2)
    (ΦR : H1P Cp.body) (hΦR : ΦR.toFun = fun p => transLift m R gs.psi p.2) :
    td.bd (trialAC hR hL W gs.psi) (trialAC hR hL W gs.psi)
      = W.toFun 0 ^ 2 * tdM.bdΓ ΦL ΦL
        + Sobolev.mass (bulkLength Cm Cp L R) W * bdR m R gs.psi gs.psi
        + W.toFun (bulkLength Cm Cp L R) ^ 2 * tdP.bdΓ ΦR ΦR := by
  rw [hsplit (trialAC hR hL W gs.psi), capScale_taw m hR,
    bdΓ_capLeft_tam tdM hR hL W gs.psi ΦL hΦL, bdCyl_bulk_tam hR hL W gs.psi,
    bdΓ_capRight_tam tdP hR hL W gs.psi ΦR hΦR]
  ring

/-- **`renormEnergy_trialAC_ag2`: `eq:trial-energy`, exact form, for a weak transverse ground
state, at an arbitrary cap pair with abstract trace data.** -/
theorem renormEnergy_trialAC_ag2 (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (W : Sobolev.H1 (bulkLength Cm Cp L R))
    (gs : TransverseGroundState m α R (bdR m R))
    (td : TraceData Cm Cp L R) (hsplit : TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL td)
    (ΦL : H1P Cm.body) (hΦLtoFun : ΦL.toFun = fun p => transLift m R gs.psi p.2)
    (hΦLgz : ΦL.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2))
    (ΦR : H1P Cp.body) (hΦRtoFun : ΦR.toFun = fun p => transLift m R gs.psi p.2)
    (hΦRgz : ΦR.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2)) :
    dirichletP (trialAC hR hL W gs.psi)
        + α * td.bd (trialAC hR hL W gs.psi) (trialAC hR hL W gs.psi)
        - gs.nu * massP (trialAC hR hL W gs.psi)
      = Sobolev.dirichlet (bulkLength Cm Cp L R) W
        + W.toFun 0 ^ 2 * capEnergyTermGen_ag2 Cm tdM α R gs ΦL
        + W.toFun (bulkLength Cm Cp L R) ^ 2 * capEnergyTermGen_ag2 Cp tdP α R gs ΦR := by
  have hbulk : Weak.dirichlet gs.psi + α * bdR m R gs.psi gs.psi = gs.nu := by
    have h := gs.weak_eq gs.psi
    rw [qBilin_self, NBilin_self, gs.normalized, mul_one, qB] at h
    exact h
  rw [dirichletP_trialAC, massP_trialAC,
    bd_trialAC_ag2 hR hL tdM tdP W gs td hsplit ΦL hΦLtoFun ΦR hΦRtoFun,
    massP_leftCap_tam hR hL W gs.psi ΦL hΦLtoFun, massP_rightCap_tam hR hL W gs.psi ΦR hΦRtoFun,
    dirichletP_leftCap_tam hR hL W gs.psi ΦL hΦLgz, dirichletP_rightCap_tam hR hL W gs.psi ΦR hΦRgz,
    gs.normalized]
  simp only [capEnergyTermGen_ag2]
  linear_combination (Sobolev.mass (bulkLength Cm Cp L R) W) * hbulk

/-! ## 4. The `trial_energy` field, arbitrary cap pair -/

/-- **`trial_energy_field_ag2`: the `trial_energy` field of `GlobalComparisonData`, for a weak
transverse ground state, at an arbitrary cap pair with abstract trace data.** -/
theorem trial_energy_field_ag2 (tdM : CapTraceData Cm) (tdP : CapTraceData Cp)
    (α : ℝ) (hα : 0 < α) (L A : ℝ) :
    ∃ Ctr : ℝ, 0 ≤ Ctr ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ (hL : (Cm.K + Cp.K) * R < L)
        (gs : TransverseGroundState m α R (bdR m R))
        (td : TraceData Cm Cp L R)
        (hsplit : TraceSplitGen2_ag2 Cm Cp tdM tdP hR hL td)
        (ΦL : H1P Cm.body) (hΦLtoFun : ΦL.toFun = fun p => transLift m R gs.psi p.2)
        (hΦLgz : ΦL.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2))
        (ΦR : H1P Cp.body)
        (hΦRtoFun : ΦR.toFun = fun p => transLift m R gs.psi p.2)
        (hΦRgz : ΦR.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2))
        (hcapL : |capEnergyTermGen_ag2 Cm tdM α R gs ΦL - Cm.beta α| ≤ Ctr * R)
        (hcapR : |capEnergyTermGen_ag2 Cp tdP α R gs ΦR - Cp.beta α| ≤ Ctr * R)
        (v : Sobolev.H1Q (bulkLength Cm Cp L R)),
        robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
            (liftQ hR hL gs.psi v)
          - gs.nu * massPQ (liftQ hR hL gs.psi v)
        ≤ Sobolev.robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R)
            (bulkLength Cm Cp L R) v := by
  refine ⟨|A|, abs_nonneg A, ?_⟩
  intro R hR hR1 hL gs td hsplit ΦL hΦLtoFun hΦLgz ΦR hΦRtoFun hΦRgz hcapL hcapR v
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [liftQ_mk, robinFormPQ_mk, massPQ_mk, Sobolev.robinFormQ_mk,
    renormEnergy_trialAC_ag2 hR hL tdM tdP W gs td hsplit ΦL hΦLtoFun hΦLgz ΦR hΦRtoFun hΦRgz,
    Sobolev.robinForm]
  have hb0L : capEnergyTermGen_ag2 Cm tdM α R gs ΦL ≤ Cm.beta α + |A| * R := by
    have := (abs_le.1 hcapL).2
    linarith
  have hb0R : capEnergyTermGen_ag2 Cp tdP α R gs ΦR ≤ Cp.beta α + |A| * R := by
    have := (abs_le.1 hcapR).2
    linarith
  have h1 : W.toFun 0 ^ 2 * capEnergyTermGen_ag2 Cm tdM α R gs ΦL
      ≤ (Cm.beta α + |A| * R) * W.toFun 0 ^ 2 := by
    nlinarith [sq_nonneg (W.toFun 0), hb0L]
  have h2 : W.toFun (bulkLength Cm Cp L R) ^ 2 * capEnergyTermGen_ag2 Cp tdP α R gs ΦR
      ≤ (Cp.beta α + |A| * R) * W.toFun (bulkLength Cm Cp L R) ^ 2 := by
    nlinarith [sq_nonneg (W.toFun (bulkLength Cm Cp L R)), hb0R]
  linarith

end

end RobinCaps.ThinDomain
