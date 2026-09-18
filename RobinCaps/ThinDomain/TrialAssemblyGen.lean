import RobinCaps.ThinDomain.TrialAssemblyOne
import RobinCaps.ThinDomain.AssemblyOneGen

/-!
# The trial side of the global comparison, for general transverse dimension `m`

`RobinCaps/ThinDomain/TrialAssemblyOne.lean` proves the `trial_energy` field of
`RobinCaps.ThinDomain.GlobalComparisonData` for transverse dimension `m = 1` and the specific
trace datum `traceDataOne`, and `RobinCaps/ThinDomain/AssemblyOneGen.lean` generalises it (still
at `m = 1`) to an arbitrary trace datum `td : TraceData Cm Cp L R`.

Most of the underlying machinery — `continuousOn_trialACFun_ta`, `boundaryEnergy_trialAC_ta`,
`renormEnergy_trialAC_ta`, `trialAC_energy_le_ta`, `massPQ_liftQ_ta`,
`TraceData.vanishesOnNullAEP` — is *already* stated for a general transverse dimension `m` in
`TrialAssemblyOne.lean` and `Eigen.lean`.  The only pieces that were specialised to `Cap 1` are
the ones that packaged an arbitrary boundary form `td.bd`/`traceDataOne.bd` through
`tr_continuous`: `bd_trialAC_ta`, `robinFormPQ_liftQ_ta` (both for `traceDataOne`), and
`AssemblyOneGen.bd_trialAC_gen_ag`, `robinFormPQ_liftQ_gen_ag`, `trial_energy_field_gen_ag`
(for an arbitrary `td`, but still `m = 1` and `gsr := groundStateOneReg`).

This file removes both specialisations at once: it proves the `trial_energy` field for an
arbitrary transverse dimension `m`, an arbitrary trace datum `td : TraceData Cm Cp L R`, and an
arbitrary transverse ground state `gsr : TransverseGroundStateReg m α R bd` (not just the
one-dimensional `groundStateOneReg`).

## Contents

1. `bd_trialAC_tg` — the generic copy of `bd_trialAC_ta`/`AssemblyOneGen.bd_trialAC_gen_ag`,
   for general `m` and an arbitrary trace datum `td`.
2. `robinFormPQ_liftQ_tg` — the generic copy of
   `robinFormPQ_liftQ_ta`/`AssemblyOneGen.robinFormPQ_liftQ_gen_ag`, for general `m`.
3. `trial_energy_field_tg` — **the `trial_energy` field of `GlobalComparisonData`, for general
   `m`, an arbitrary trace datum `td`, and an arbitrary transverse ground state `gsr`.**  The
   constant `A` is uniform: it depends only on `α`, the two caps `Cm, Cp` and the expansion
   constant `Cexp`, not on `R`, `bd`, `gsr`, `td` or the trial vector `v`.
4. `trial_energy_field_gen_ag_of_tg` — **consistency check**: `AssemblyOneGen.trial_energy_field_gen_ag`
   (the `m = 1`, `gsr := groundStateOneReg` statement) is recovered from `trial_energy_field_tg`
   by instantiation.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain

noncomputable section

variable {m : ℕ} {R : ℝ} {Cm Cp : Cap m} {L : ℝ}

/-! ## 1. The quotient Robin form of the trial lift, for a general trace datum -/

section Quotient

/-- **The generic copy of `bd_trialAC_ta`, for general transverse dimension `m` and an
arbitrary trace datum `td`.**  On the trial extension — which is continuous up to `∂Ω_R`
(`continuousOn_trialACFun_ta`, already general in `m`) — *any* abstract boundary form
`td.bd` is the honest surface integral, by `td.tr_continuous`. -/
theorem bd_trialAC_tg (td : TraceData Cm Cp L R) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (W : Sobolev.H1 (bulkLength Cm Cp L R)) {ψ : TransH1 m R}
    (hψ : Continuous fun z => ψ.toFun z) :
    td.bd (trialAC hR hL W ψ) (trialAC hR hL W ψ)
      = boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W ψ) :=
  td.tr_continuous _ (continuousOn_trialACFun_ta hR hL W hψ)

/-- **The generic copy of `robinFormPQ_liftQ_ta`, for general `m` and an arbitrary trace
datum.** -/
theorem robinFormPQ_liftQ_tg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (W : Sobolev.H1 (bulkLength Cm Cp L R))
    {ψ : TransH1 m R} (hψ : Continuous fun z => ψ.toFun z) :
    robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
        (liftQ hR hL ψ (Submodule.Quotient.mk W))
      = dirichletP (trialAC hR hL W ψ)
        + α * boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W ψ) := by
  rw [liftQ_mk, robinFormPQ_mk, bd_trialAC_tg td hR hL W hψ]

end Quotient

/-! ## 2. The `trial_energy` field, for general `m` -/

section Field

/-- **The `trial_energy` field of `GlobalComparisonData`, for general transverse dimension
`m`, an arbitrary trace datum `td`, and an arbitrary transverse ground state `gsr`.**

The constant `A` is uniform: it depends only on `α`, the two caps `Cm, Cp` and the expansion
constant `Cexp` of `TransverseExpansionData` (through `trialEnergyConst_ta`, already general in
`m`) — in particular not on `R`, on `bd`, on `gsr`, on `td`, nor on the trial vector `v`. -/
theorem trial_energy_field_tg (hm : 1 ≤ m) (α : ℝ) (Cm Cp : Cap m) (L Cexp : ℝ)
    (hθ0m : 0 ≤ Cm.θ 0) (hθ1m : Cm.θ 0 ≤ 1) (hθ0p : 0 ≤ Cp.θ 0) (hθ1p : Cp.θ 0 ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ (hL : (Cm.K + Cp.K) * R < L) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
        (gsr : TransverseGroundStateReg m α R bd) (td : TraceData Cm Cp L R),
        TransverseExpansionData m α R gsr Cexp →
        ∀ v : Sobolev.H1Q (bulkLength Cm Cp L R),
          robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
              (liftQ hR hL gsr.psi v)
            - gsr.nu * massPQ (liftQ hR hL gsr.psi v)
          ≤ Sobolev.robinFormQ (Cm.beta α + A * R) (Cp.beta α + A * R)
              (bulkLength Cm Cp L R) v := by
  refine ⟨trialEnergyConst_ta m α Cm Cp Cexp, trialEnergyConst_ta_nonneg m α Cm Cp Cexp, ?_⟩
  intro R hR hR1 hL bd gsr td hexp v
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [robinFormPQ_liftQ_tg hR hL td α W gsr.psiC1.continuous,
    massPQ_liftQ_ta hR hL W gsr.psi,
    Sobolev.robinFormQ_mk]
  exact trialAC_energy_le_ta hm Cm Cp L hθ0m hθ1m hθ0p hθ1p hR hR1 hL hexp W

end Field

/-! ## 3. Consistency check: `AssemblyOneGen.trial_energy_field_gen_ag` from `trial_energy_field_tg` -/

section Consistency

/-- **Consistency check.**  `AssemblyOneGen.trial_energy_field_gen_ag` (`m = 1`,
`gsr := Transverse.groundStateOneReg α R hα hR`) is recovered from the general
`trial_energy_field_tg` by instantiating `m := 1` and `gsr` at the one-dimensional ground
state. -/
theorem trial_energy_field_gen_ag_of_tg (α : ℝ) (hα : 0 < α) (Cm Cp : Cap 1) (L Cexp : ℝ)
    (hθ0m : 0 ≤ Cm.θ 0) (hθ1m : Cm.θ 0 ≤ 1) (hθ0p : 0 ≤ Cp.θ 0) (hθ1p : Cp.θ 0 ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ hL : (Cm.K + Cp.K) * R < L, ∀ td : TraceData Cm Cp L R,
        TransverseExpansionData 1 α R (Transverse.groundStateOneReg α R hα hR) Cexp →
        ∀ v : Sobolev.H1Q (bulkLength Cm Cp L R),
          robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
              (liftQ hR hL (Transverse.groundStateOneReg α R hα hR).psi v)
            - (Transverse.groundStateOneReg α R hα hR).nu
                * massPQ (liftQ hR hL (Transverse.groundStateOneReg α R hα hR).psi v)
          ≤ Sobolev.robinFormQ (Cm.beta α + A * R) (Cp.beta α + A * R)
              (bulkLength Cm Cp L R) v := by
  obtain ⟨A, hA0, hA⟩ := trial_energy_field_tg le_rfl α Cm Cp L Cexp hθ0m hθ1m hθ0p hθ1p
  refine ⟨A, hA0, ?_⟩
  intro R hR hR1 hL td hexp v
  exact hA R hR hR1 hL _ (Transverse.groundStateOneReg α R hα hR) td hexp v

end Consistency

end

end RobinCaps.ThinDomain
