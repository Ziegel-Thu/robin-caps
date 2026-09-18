import RobinCaps.ThinDomain.AssemblyOne
import RobinCaps.ThinDomain.TrialAssemblyOne
import RobinCaps.ThinDomain.BridgeTrialOne

/-!
# The `m = 1` global comparison, generalised to an arbitrary trace datum

`RobinCaps/ThinDomain/AssemblyOne.lean` carries out the final `m = 1` assembly for the
**specific** trace datum `traceDataOne hR hL hm0 hp0 hti` of
`RobinCaps/ThinDomain/TraceOne.lean` (vertical-slice traces everywhere).  Its only use of that
specific datum is the pair of geometric facts

* `traceForm_split_a1` — the boundary form of `Ω_R` splits into a left-cap piece, a bulk piece
  and a right-cap piece, and
* `bdBulk_eq_bdCyl_a1` — the bulk piece *is* the cylinder boundary form `bdCyl (bdTr R)`.

This file isolates exactly that pair into the interface `TraceSplitInput_ag` and repeats the
whole assembly for an **arbitrary** `td : TraceData Cm Cp L R` satisfying it.  A second trace
construction (radial traces on the caps, vertical traces on the bulk) can therefore be plugged
in without the vertical/radial identification.

## Contents

1. `TraceSplitInput_ag` — the trace-split interface (`bdCapL`, `bdCapR` as parameters, so that
   the interface stays a `Prop`).
2. `capEnergyL_ag`, `capEnergyR_ag`, `energy_split_ag` — the generic three-piece splitting of
   the renormalized Robin energy.
3. `CapLowerInput_ag` — `lem:cap` at one radius, stated with the split's `bdCapL`/`bdCapR`.
4. `Zrep_ag`, `lower_rep_ag`, `upper_rep_ag`, `globalComparisonData_gen_ag` — the generic
   assembly at one radius.
5. `TraceSplitFamilyInput_ag`, `TrialEnergyInput_ag`, `globalComparison_gen_ag`,
   `mainTheorem_gen_ag`, `counterexample_gen_ag` — the generic global comparison, `thm:main`
   and `cor:counterexample`.
6. `trial_energy_field_gen_ag` — the trial-energy field of `TrialAssemblyOne.lean`, re-proved
   for an arbitrary trace datum (only `tr_continuous` is used).
7. `traceSplitInput_one_ag`, `globalComparisonData_one_ag`, `mainTheorem_one_ag` — the
   consistency check: `AssemblyOne`'s own results, re-derived from the generic ones.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-! ## Part 1: the trace-split interface -/

section Split

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- **The trace-split interface.**

The two cap functionals `bdCapL`, `bdCapR` are *parameters* (not fields), so that the interface
is a genuine `Prop`; they play the role of `bdCapL_a1`/`bdCapR_a1` of
`RobinCaps/ThinDomain/AssemblyOne.lean`.

The single analytic content is the `split` field, which is exactly the combination of
`traceForm_split_a1` and `bdBulk_eq_bdCyl_a1`: the boundary form of `Ω_R` is the left-cap piece
plus the cylinder boundary form `bdCyl (bdTr R)` of the bulk restriction plus the right-cap
piece. -/
structure TraceSplitInput_ag (hR : 0 < R) (td : TraceData Cm Cp L R)
    (bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ) : Prop where
  /-- The left-cap piece of the boundary form is nonnegative. -/
  bdCapL_nonneg : ∀ u, 0 ≤ bdCapL u
  /-- The right-cap piece of the boundary form is nonnegative. -/
  bdCapR_nonneg : ∀ u, 0 ≤ bdCapR u
  /-- **The boundary form splits**, with the bulk piece the cylinder form of `bdTr R`. -/
  split : ∀ u : H1P (thinDomain Cm Cp L R),
    td.bd u u
      = bdCapL u + bdCyl (bdTr R) (restrictBulkP hR u) (restrictBulkP hR u) + bdCapR u

/-- The renormalized energy of the left cap component, for a generic cap piece. -/
def capEnergyL_ag (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (bdCapL : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictLeft hR hL u) + α * bdCapL u - ν * massP (restrictLeft hR hL u)

/-- The renormalized energy of the right cap component, for a generic cap piece. -/
def capEnergyR_ag (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (bdCapR : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  dirichletP (restrictRight hR hL u) + α * bdCapR u - ν * massP (restrictRight hR hL u)

/-- **The generic analogue of `energy_split_a1`.**  The renormalized Robin energy of `Ω_R`
splits exactly into the two cap energies and the renormalized bulk energy. -/
theorem energy_split_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {td : TraceData Cm Cp L R} {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hs : TraceSplitInput_ag hR td bdCapL bdCapR) (ν : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP u + α * td.bd u u - ν * massP u
      = capEnergyL_ag α ν hR hL bdCapL u
        + (EB α (bdTr R) (restrictBulkP hR u) - ν * massP (restrictBulkP hR u))
        + capEnergyR_ag α ν hR hL bdCapR u := by
  rw [capEnergyL_ag, capEnergyR_ag, EB, hs.split u, dirichletP_eq_sum_P_a1 hR hL u,
    massP_eq_sum_P_a1 hR hL u]
  ring

end Split

/-! ## Part 2: the cap interface, restated with the generic cap pieces -/

section Interface

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- **`lem:cap` in thin-domain scaling** (`eq:cap-lower`, `eq:cap-mass-bound`), for `m = 1`, at
**one** radius and for the generic cap pieces `bdCapL`, `bdCapR` supplied by
`TraceSplitInput_ag`.

This is `CapLowerInput_a1` with `capEnergyL_a1`/`capEnergyR_a1` replaced by
`capEnergyL_ag`/`capEnergyR_ag`; the entrance pairings `p_∓` are again written, through
`eq:interval-trace`, as the endpoint values of the axial profile `axialRepOne_a1`. -/
structure CapLowerInput_ag (hα : 0 < α) (Ccap : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ) : Prop where
  /-- The two cap decompositions of `lem:cap` exist at this radius. -/
  cap : ∃ Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ,
    (∀ u, 0 ≤ Gm u) ∧ (∀ u, 0 ≤ Gp u) ∧
    (∀ u, (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
            + (2 * R)⁻¹ * Gm u
          ≤ capEnergyL_ag α (nuR α R hα hR) hR hL bdCapL u) ∧
    (∀ u, (Cp.beta α - Ccap * R)
              * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
            + (2 * R)⁻¹ * Gp u
          ≤ capEnergyR_ag α (nuR α R hα hR) hR hL bdCapR u) ∧
    (∀ u, massP (restrictLeft hR hL u)
          ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 + Ccap * R * Gm u) ∧
    (∀ u, massP (restrictRight hR hL u)
          ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
              + Ccap * R * Gp u)

end Interface

/-! ## Part 3: `eq:Z-definition` and the two global bounds, generically -/

section Estimates

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- **`eq:Z-definition`**, at the level of representatives (the generic copy of `Zrep_a1`; it
does not involve the trace datum at all). -/
def Zrep_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ :=
  massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR) (restrictBulkP hR u))
    + C₀ * R * (Gm u + Gp u)

theorem Zrep_eq_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    Zrep_ag hR hL hα C₀ Gm Gp u = Zrep_a1 hR hL hα C₀ Gm Gp u := rfl

theorem Zrep_nonneg_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀) {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ} (hGm : ∀ u, 0 ≤ Gm u)
    (hGp : ∀ u, 0 ≤ Gp u) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ Zrep_ag hR hL hα C₀ Gm Gp u :=
  Zrep_nonneg_a1 hR hL hα hC₀ hGm hGp u

/-- **`eq:global-energy-lower`, at the level of representatives, for a generic trace datum.**

The generic copy of `lower_rep_a1`: the bulk contribution is `bulk_separation`, the two cap
contributions are `eq:cap-lower`, and the three pieces are glued by `energy_split_ag`. -/
theorem lower_rep_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    {td : TraceData Cm Cp L R} {bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ}
    (hs : TraceSplitInput_ag hR td bdCapL bdCapR)
    {Ccap C C₀ c₀ cgap : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hcapL : ∀ u, (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
        + (2 * R)⁻¹ * Gm u ≤ capEnergyL_ag α (nuR α R hα hR) hR hL bdCapL u)
    (hcapR : ∀ u, (Cp.beta α - Ccap * R)
          * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * Gp u ≤ capEnergyR_ag α (nuR α R hα hR) hR hL bdCapR u)
    (hgap : cgap ≤ (groundStateOne α R hα hR).gapConst)
    (hCC : Ccap ≤ C) (hc₀gap : c₀ ≤ cgap) (hc₀C₀ : c₀ * C₀ ≤ 1 / 2)
    (u : H1P (thinDomain Cm Cp L R)) :
    Sobolev.robinForm (Cm.beta α - C * R) (Cp.beta α - C * R) (bulkLength Cm Cp L R)
          (axialRepOne_a1 hR hL hα u)
        + c₀ / R ^ 2 * Zrep_ag hR hL hα C₀ Gm Gp u
      ≤ dirichletP u + α * td.bd u u - nuR α R hα hR * massP u := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hZW0 : 0 ≤ massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
      (restrictBulkP hR u)) := massP_nonneg _
  have hG : 0 ≤ Gm u + Gp u := by linarith [hGm u, hGp u]
  have hnu : (groundStateOne α R hα hR).nu = nuR α R hα hR := rfl
  have hD := dirichlet_axialRepOne_a1 hR hL hα u
  have hbulk := bulk_separation (interface_lt hR hL) (groundStateOne α R hα hR)
    (bdSliceable_bdTr hR (-L / 2 + Cm.K * R) (L / 2 - Cp.K * R)) (restrictBulkP hR u)
  rw [← hD, hnu] at hbulk
  have hsplit := energy_split_ag (α := α) hR hL hs (nuR α R hα hR) u
  have hcl := hcapL u
  have hcr := hcapR u
  -- the two spectral absorptions
  have e1 : c₀ / R ^ 2 * massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
        (restrictBulkP hR u))
      ≤ (groundStateOne α R hα hR).gapConst * R⁻¹ ^ 2
        * massP (bulkRemainder (interface_lt hR hL) (groundStateOne α R hα hR)
            (restrictBulkP hR u)) := by
    refine mul_le_mul_of_nonneg_right ?_ hZW0
    have hle : c₀ ≤ (groundStateOne α R hα hR).gapConst := le_trans hc₀gap hgap
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
  have hendL : (Cm.beta α - C * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2
      ≤ (Cm.beta α - Ccap * R) * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hCC, hR.le]
  have hendR : (Cp.beta α - C * R)
        * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
      ≤ (Cp.beta α - Ccap * R)
        * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hCC, hR.le]
  rw [Sobolev.robinForm, Zrep_ag, mul_add]
  linarith [hbulk, hcl, hcr, e1, e2, hendL, hendR, hsplit]

/-- **`eq:global-mass-upper`, at the level of representatives.**  This statement does not
mention the trace datum, so it is `upper_rep_a1` verbatim. -/
theorem upper_rep_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α)
    {Ccap C C₀ Ctrace : ℝ} {Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ}
    (hCcap : 0 ≤ Ccap) (hGm : ∀ u, 0 ≤ Gm u) (hGp : ∀ u, 0 ≤ Gp u)
    (hmassL : ∀ u, massP (restrictLeft hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 + Ccap * R * Gm u)
    (hmassR : ∀ u, massP (restrictRight hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
            + Ccap * R * Gp u)
    (htrace : ∀ v : Sobolev.H1 (bulkLength Cm Cp L R),
        v.toFun 0 ^ 2 + v.toFun (bulkLength Cm Cp L R) ^ 2
          ≤ Ctrace * (Sobolev.mass (bulkLength Cm Cp L R) v
              + Sobolev.dirichlet (bulkLength Cm Cp L R) v))
    (hCC : Ccap * Ctrace ≤ C) (hC₀ : Ccap ≤ C₀)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP u
      ≤ (1 + C * R) * Sobolev.mass (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
        + C * R * Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα u)
        + Zrep_ag hR hL hα C₀ Gm Gp u :=
  upper_rep_a1 hR hL hα hCcap hGm hGp hmassL hmassR htrace hCC hC₀ u

end Estimates

/-! ## Part 4: the `GlobalComparisonData` instance at one radius, generically -/

section Data

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- `eq:Z-definition` on the a.e. quotient, through the chosen representative `qrep_a1`. -/
def Zone_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (w : H1PQ (thinDomain Cm Cp L R)) : ℝ :=
  Zrep_ag hR hL hα C₀ Gm Gp (qrep_a1 w)

theorem Zone_eq_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hα : 0 < α) (C₀ : ℝ)
    (Gm Gp : H1P (thinDomain Cm Cp L R) → ℝ) (w : H1PQ (thinDomain Cm Cp L R)) :
    Zone_ag hR hL hα C₀ Gm Gp w = Zrep_ag hR hL hα C₀ Gm Gp (qrep_a1 w) := rfl

/-- **The bulk/cap decomposition data of `sec:proof` at one radius, for `m = 1` and an
arbitrary trace datum `td` satisfying the trace-split interface.** -/
theorem globalComparisonData_gen_ag (hα : 0 < α) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
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
    Nonempty (GlobalComparisonData Cm Cp L α hR hL td (nuR α R hα hR) C c₀) := by
  refine ⟨{
    π := bulkProjThin hR hL (psiOne_a1 α R hα hR).memL2 (psiOne_normalized_a1 hα hR)
    π_surj := bulkProjThin_surjective_trialAC hR hL (psiOne_a1 α R hα hR)
      (psiOne_normalized_a1 hα hR)
    Z := Zone_ag hR hL hα C₀ Gm Gp
    Z_nonneg := fun w => Zrep_nonneg_ag hR hL hα hC₀0 hGm hGp (qrep_a1 w)
    lift := liftQ hR hL (psiOne_a1 α R hα hR)
    trial_mass := massQ_le_massPQ_liftQ hR hL (psiOne_a1 α R hα hR)
      (groundStateOne α R hα hR).normalized
    lower := ?_
    upper := ?_
    trial_energy := ?_ }⟩
  · intro w
    have hw : (Submodule.Quotient.mk (qrep_a1 w) : H1PQ (thinDomain Cm Cp L R)) = w :=
      qrep_mk_a1 w
    have hpi := bulkProjThin_mk_a1 hR hL hα (qrep_a1 w)
    rw [hw] at hpi
    have hq := robinFormPQ_mk (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α (qrep_a1 w)
    rw [hw] at hq
    have hm := massPQ_mk (qrep_a1 w)
    rw [hw] at hm
    rw [hpi, Sobolev.robinFormQ_mk, hq, hm, Zone_eq_ag]
    exact lower_rep_ag hR hL hα hs hGm hGp hcapL hcapR hgap hCC hc₀gap hc₀C₀ (qrep_a1 w)
  · intro w
    have hw : (Submodule.Quotient.mk (qrep_a1 w) : H1PQ (thinDomain Cm Cp L R)) = w :=
      qrep_mk_a1 w
    have hpi := bulkProjThin_mk_a1 hR hL hα (qrep_a1 w)
    rw [hw] at hpi
    have hm := massPQ_mk (qrep_a1 w)
    rw [hw] at hm
    have hrf : Sobolev.robinForm 0 0 (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα (qrep_a1 w))
        = Sobolev.dirichlet (bulkLength Cm Cp L R) (axialRepOne_a1 hR hL hα (qrep_a1 w)) := by
      rw [Sobolev.robinForm]; ring
    rw [hpi, Sobolev.massQ_mk, Sobolev.robinFormQ_mk, hrf, hm, Zone_eq_ag]
    exact upper_rep_ag hR hL hα hCcap hGm hGp hmassL hmassR htrace hCCt hC₀ (qrep_a1 w)
  · intro v
    refine le_trans (htrial v) ?_
    refine Sobolev.robinFormQ_mono ?_ ?_ v <;> nlinarith [hCtrC, hR.le]

end Data

/-! ## Part 5: the generic global comparison, `thm:main` and `cor:counterexample` -/

section Final

-- `hif` (`InterfaceTraceInput_a1`) is a *recorded* interface hypothesis, exactly as in
-- `RobinCaps/ThinDomain/AssemblyOne.lean`: it is the statement that justifies writing the
-- entrance pairing `p_∓` of `CapLowerInput_ag` as `F(x_∓)`.
set_option linter.unusedVariables false

/-- **The trace-split interface for a whole trace family.**

For every admissible radius the trace datum `tdf R hR hR₀` splits into two cap pieces and the
cylinder form of the bulk (`TraceSplitInput_ag`), *and* `lem:cap` holds for those very cap
pieces (`CapLowerInput_ag`).  The two are bundled because they must refer to the **same**
`bdCapL`, `bdCapR`. -/
structure TraceSplitFamilyInput_ag (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α) (Ccap R₀ : ℝ)
    (tdf : TraceFamily Cm Cp L R₀) : Prop where
  /-- Split and cap lower bound, at every admissible radius, with matching cap pieces. -/
  data : ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) (hL : (Cm.K + Cp.K) * R < L),
    ∃ bdCapL bdCapR : H1P (thinDomain Cm Cp L R) → ℝ,
      TraceSplitInput_ag hR (tdf R hR hR₀) bdCapL bdCapR ∧
      CapLowerInput_ag hα Ccap hR hL bdCapL bdCapR

/-- **`eq:trial-energy` for a generic trace family**: the generic copy of
`TrialEnergyInput_a1`, with `traceDataOne …` replaced by `tdf R hR hR₀`. -/
structure TrialEnergyInput_ag (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α) (Ctr R₀ : ℝ)
    (tdf : TraceFamily Cm Cp L R₀) : Prop where
  /-- `E_R[T_R F] ≤ a_{β₋+CR, β₊+CR; I_R}[F]`. -/
  trial : ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) (hL : (Cm.K + Cp.K) * R < L)
      (v : Sobolev.H1Q (bulkLength Cm Cp L R)),
    robinFormPQ (isOpen_thinDomain hR hL) (tdf R hR hR₀).bd (tdf R hR hR₀).vanishesOnNullAEP α
          (liftQ hR hL (psiOne_a1 α R hα hR) v)
        - nuR α R hα hR * massPQ (liftQ hR hL (psiOne_a1 α R hα hR) v)
      ≤ robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R) (bulkLength Cm Cp L R) v

/-- **The global comparison of `sec:proof` for `m = 1` and an arbitrary trace family.**

The constants are `C = max (max C_cap (C_cap C_ℓ)) C_trial`, `C₀ = max C_cap 1`,
`c₀ = min c_gap (2C₀)^{-1}`, and the threshold is
`R₁ = min R₀ (min R_gap (L / (2(K₋+K₊))))`. -/
theorem globalComparison_gen_ag (Cm Cp : Cap 1) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (tdf : TraceFamily Cm Cp L R₀)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hsplit : TraceSplitFamilyInput_ag Cm Cp L α hα Ccap R₀ tdf)
    (hif : InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀)
    (htr : TrialEnergyInput_ag Cm Cp L α hα Ctr R₀ tdf) :
    GlobalComparison Cm Cp L α (nuOneDim α hα) R₀ tdf := by
  obtain ⟨Ctrace, hCtrace0, htraceu⟩ := Sobolev.trace_ineq_uniform L hL0
  obtain ⟨cgap, Rgap, hcgap, hRgap, hgapq⟩ := groundStateOne_gap_quant α hα
  have hKK : 0 < Cm.K + Cp.K := by linarith [Cm.hK, Cp.hK]
  set C₀ : ℝ := max Ccap 1 with hC₀def
  set C : ℝ := max (max Ccap (Ccap * Ctrace)) Ctr with hCdef
  set c₀ : ℝ := min cgap (1 / (2 * C₀)) with hc₀def
  set R₁ : ℝ := min R₀ (min Rgap (L / (2 * (Cm.K + Cp.K)))) with hR₁def
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₀0 : 0 ≤ C₀ := hC₀pos.le
  have hC₀le : Ccap ≤ C₀ := le_max_left _ _
  have hCC : Ccap ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCCt : Ccap * Ctrace ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCtrC : Ctr ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := le_trans hCcap hCC
  have hc₀pos : 0 < c₀ := lt_min hcgap (by positivity)
  have hc₀gap : c₀ ≤ cgap := min_le_left _ _
  have hc₀C₀ : c₀ * C₀ ≤ 1 / 2 := by
    have h1 : c₀ ≤ 1 / (2 * C₀) := min_le_right _ _
    have h2 : c₀ * C₀ ≤ 1 / (2 * C₀) * C₀ := mul_le_mul_of_nonneg_right h1 hC₀0
    have h3 : 1 / (2 * C₀) * C₀ = 1 / 2 := by field_simp
    linarith
  have hR₁pos : 0 < R₁ := lt_min hR₀ (lt_min hRgap (by positivity))
  have hR₁R₀ : R₁ ≤ R₀ := min_le_left _ _
  refine ⟨C, c₀, R₁, hC0, hc₀pos, hR₁pos, hR₁R₀, ?_⟩
  intro R hR hRR₀ hRR₁ hLR
  have hRRgap : R < Rgap :=
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
  rw [nuOneDim_eq α hα hR]
  exact globalComparisonData_gen_ag hα hR hLR hts hCcap hC₀0 (hgapq R hR hRRgap) hCC hCCt
    hCtrC hC₀le hc₀gap hc₀C₀ htraceR hGm hGp hcapL hcapR hmassL hmassR htrialR

/-- **`thm:main` for `m = 1` and an arbitrary trace family** satisfying the trace-split
interface. -/
theorem mainTheorem_gen_ag (Cm Cp : Cap 1) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (tdf : TraceFamily Cm Cp L R₀)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hsplit : TraceSplitFamilyInput_ag Cm Cp L α hα Ccap R₀ tdf)
    (hif : InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀)
    (htr : TrialEnergyInput_ag Cm Cp L α hα Ctr R₀ tdf) :
    MainTheorem 1 Cm Cp L α hL0 hβm hβp (nuOneDim α hα) R₀ tdf :=
  mainTheorem_of_globalComparison 1 Cm Cp L α hL0 hα.le hβm hβp (nuOneDim α hα) R₀ tdf
    (globalComparison_gen_ag Cm Cp L α hL0 hα R₀ hR₀ tdf hCcap hsplit hif htr)

/-- **`cor:counterexample` for `m = 1`** (`n = 2`), for an arbitrary trace family on the planar
capsule with two hemispherical caps. -/
theorem counterexample_gen_ag (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (tdf : TraceFamily (hemisphere 1) (hemisphere 1) L R₀)
    {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hsplit : TraceSplitFamilyInput_ag (hemisphere 1) (hemisphere 1) L α hα Ccap R₀ tdf)
    (hif : InterfaceTraceInput_a1 (hemisphere 1) (hemisphere 1) L α hα Cif R₀)
    (htr : TrialEnergyInput_ag (hemisphere 1) (hemisphere 1) L α hα Ctr R₀ tdf) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L)
        (hR₀' : R < R₀),
      lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
          - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
        ≤ Interval.gap L hL0 α - Delta 1 L hL0 α / 2 ∧
      lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
          - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
        < Interval.gap L hL0 α ∧
      euclidDiam (thinDomain (hemisphere 1) (hemisphere 1) L R) = L :=
  counterexample_of_mainTheorem' 1 le_rfl L α hL0 hα (nuOneDim α hα) R₀ hR₀ tdf
    (mainTheorem_gen_ag (hemisphere 1) (hemisphere 1) L α hL0 hα
      (hemisphere_beta_pos 1 le_rfl hα) (hemisphere_beta_pos 1 le_rfl hα) R₀ hR₀ tdf
      hCcap hsplit hif htr)

end Final

/-! ## Part 6: the trial-energy field is `TraceData`-generic

The proof of `trial_energy_field_one` (`RobinCaps/ThinDomain/TrialAssemblyOne.lean`) uses the
specific datum `traceDataOne` only through its `tr_continuous` field, which every `TraceData`
has.  The three lemmas below are the verbatim copies with `traceDataOne …` replaced by an
arbitrary `td`, and `trialEnergyInput_gen_ag` discharges `TrialEnergyInput_ag` for **every**
trace family. -/

section Trial

variable {Cm Cp : Cap 1} {L R : ℝ}

/-- The generic copy of `bd_trialAC_ta`: on the trial extension — which is continuous up to
`∂Ω_R` — *any* abstract boundary form is the honest surface integral. -/
theorem bd_trialAC_gen_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (W : Sobolev.H1 (bulkLength Cm Cp L R)) {ψ : TransH1 1 R}
    (hψ : Continuous fun z => ψ.toFun z) :
    td.bd (trialAC hR hL W ψ) (trialAC hR hL W ψ)
      = boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W ψ) :=
  td.tr_continuous _ (continuousOn_trialACFun_ta hR hL W hψ)

/-- The generic copy of `robinFormPQ_liftQ_ta`. -/
theorem robinFormPQ_liftQ_gen_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (W : Sobolev.H1 (bulkLength Cm Cp L R))
    {ψ : TransH1 1 R} (hψ : Continuous fun z => ψ.toFun z) :
    robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α
        (liftQ hR hL ψ (Submodule.Quotient.mk W))
      = dirichletP (trialAC hR hL W ψ)
        + α * boundaryEnergy Cm Cp L R (trialACFun Cm Cp L R W ψ) := by
  rw [liftQ_mk, robinFormPQ_mk, bd_trialAC_gen_ag hR hL td W hψ]

/-- **The `trial_energy` field for `m = 1` and an arbitrary trace datum.**  The generic copy of
`trial_energy_field_one`; the trace datum enters only through `tr_continuous`. -/
theorem trial_energy_field_gen_ag (α : ℝ) (hα : 0 < α) (Cm Cp : Cap 1) (L Cexp : ℝ)
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
  refine ⟨trialEnergyConst_ta 1 α Cm Cp Cexp, trialEnergyConst_ta_nonneg 1 α Cm Cp Cexp, ?_⟩
  intro R hR hR1 hL td hexp v
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [robinFormPQ_liftQ_gen_ag hR hL td α W
      (Transverse.groundStateOneReg α R hα hR).psiC1.continuous,
    massPQ_liftQ_ta hR hL W (Transverse.groundStateOneReg α R hα hR).psi,
    Sobolev.robinFormQ_mk]
  exact trialAC_energy_le_ta le_rfl Cm Cp L hθ0m hθ1m hθ0p hθ1p hR hR1 hL hexp W

/-- **`eq:trial-energy` holds for every trace family**: the `TrialEnergyInput_ag` interface is
not an assumption at all, it is a theorem.  This is `trialEnergyInput_one_bt` with
`traceFamilyOne_a1` replaced by an arbitrary family. -/
theorem trialEnergyInput_gen_ag (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α)
    (hθ0m : 0 ≤ Cm.θ 0) (hθ1m : Cm.θ 0 ≤ 1) (hθ0p : 0 ≤ Cp.θ 0) (hθ1p : Cp.θ 0 ≤ 1) :
    ∃ Ctr R₀ : ℝ, 0 ≤ Ctr ∧ 0 < R₀ ∧ R₀ ≤ 1 ∧
      ∀ (R₀' : ℝ), R₀' ≤ R₀ → ∀ tdf : TraceFamily Cm Cp L R₀',
        TrialEnergyInput_ag Cm Cp L α hα Ctr R₀' tdf := by
  obtain ⟨Cexp, R₀, hR₀, hR₀1, hexp⟩ := transverseExpansionData_one α hα
  obtain ⟨A, hA0, hA⟩ :=
    trial_energy_field_gen_ag α hα Cm Cp L Cexp hθ0m hθ1m hθ0p hθ1p
  refine ⟨A, R₀, hA0, hR₀, hR₀1, fun R₀' hle tdf => ⟨fun R hR hR₀' hL v => ?_⟩⟩
  have hRR₀ : R < R₀ := lt_of_lt_of_le hR₀' hle
  exact hA R hR (le_of_lt (lt_of_lt_of_le hRR₀ hR₀1)) hL (tdf R hR hR₀') (hexp R hR hRR₀) v

end Trial

/-! ## Part 7: consistency — `AssemblyOne`'s results, re-derived from the generic ones -/

section Consistency

variable {Cm Cp : Cap 1} {L R α : ℝ}

/-- The left-cap piece of the `m = 1` boundary form is nonnegative. -/
theorem bdCapL_nonneg_ag (Cm Cp : Cap 1) (L R : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdCapL_a1 Cm Cp L R u :=
  setIntegral_nonneg measurableSet_Ioo fun x _ =>
    mul_nonneg (areaElement_nonneg x) (by positivity)

/-- The right-cap piece of the `m = 1` boundary form is nonnegative. -/
theorem bdCapR_nonneg_ag (Cm Cp : Cap 1) (L R : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    0 ≤ bdCapR_a1 Cm Cp L R u :=
  setIntegral_nonneg measurableSet_Ioo fun x _ =>
    mul_nonneg (areaElement_nonneg x) (by positivity)

/-- **The trace-split interface holds for `traceDataOne`**, with the cap pieces `bdCapL_a1`,
`bdCapR_a1` of `RobinCaps/ThinDomain/AssemblyOne.lean`.  This is exactly the combination of
`traceForm_split_a1` and `bdBulk_eq_bdCyl_a1`, and it is what makes the generalisation of this
file faithful. -/
theorem traceSplitInput_one_ag (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hm0 : Cm.θ 0 = 0)
    (hp0 : Cp.θ 0 = 0) (hti : TraceIneqOne Cm Cp L R) :
    TraceSplitInput_ag hR (traceDataOne hR hL hm0 hp0 hti)
      (bdCapL_a1 Cm Cp L R) (bdCapR_a1 Cm Cp L R) where
  bdCapL_nonneg := bdCapL_nonneg_ag Cm Cp L R
  bdCapR_nonneg := bdCapR_nonneg_ag Cm Cp L R
  split u := by
    have hbd : (traceDataOne hR hL hm0 hp0 hti).bd u u = traceForm hR hL u u := rfl
    rw [hbd, traceForm_split_a1 hR hL hti u, bdBulk_eq_bdCyl_a1 hR hL u]

/-- The two cap energies of `AssemblyOne` are the generic ones for the pieces `bdCapL_a1`,
`bdCapR_a1`. -/
theorem capEnergyL_eq_ag (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    capEnergyL_a1 α ν hR hL u = capEnergyL_ag α ν hR hL (bdCapL_a1 Cm Cp L R) u := rfl

theorem capEnergyR_eq_ag (α ν : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    capEnergyR_a1 α ν hR hL u = capEnergyR_ag α ν hR hL (bdCapR_a1 Cm Cp L R) u := rfl

/-- **Consistency check.**  `globalComparisonData_one_a1` of
`RobinCaps/ThinDomain/AssemblyOne.lean`, re-proved by instantiating the generic
`globalComparisonData_gen_ag` at `td := traceDataOne …`. -/
theorem globalComparisonData_one_ag (hα : 0 < α) (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0)
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (hti : TraceIneqOne Cm Cp L R)
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
        + (2 * R)⁻¹ * Gm u ≤ capEnergyL_a1 α (nuR α R hα hR) hR hL u)
    (hcapR : ∀ u, (Cp.beta α - Ccap * R)
          * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
        + (2 * R)⁻¹ * Gp u ≤ capEnergyR_a1 α (nuR α R hα hR) hR hL u)
    (hmassL : ∀ u, massP (restrictLeft hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun 0 ^ 2 + Ccap * R * Gm u)
    (hmassR : ∀ u, massP (restrictRight hR hL u)
        ≤ Ccap * R * (axialRepOne_a1 hR hL hα u).toFun (bulkLength Cm Cp L R) ^ 2
            + Ccap * R * Gp u)
    (htrial : ∀ v : Sobolev.H1Q (bulkLength Cm Cp L R),
        robinFormPQ (isOpen_thinDomain hR hL) (traceDataOne hR hL hm0 hp0 hti).bd
              (traceDataOne hR hL hm0 hp0 hti).vanishesOnNullAEP α
              (liftQ hR hL (psiOne_a1 α R hα hR) v)
            - nuR α R hα hR * massPQ (liftQ hR hL (psiOne_a1 α R hα hR) v)
          ≤ robinFormQ (Cm.beta α + Ctr * R) (Cp.beta α + Ctr * R) (bulkLength Cm Cp L R) v) :
    Nonempty (GlobalComparisonData Cm Cp L α hR hL (traceDataOne hR hL hm0 hp0 hti)
      (nuR α R hα hR) C c₀) :=
  globalComparisonData_gen_ag (Gm := Gm) (Gp := Gp) hα hR hL
    (traceSplitInput_one_ag hR hL hm0 hp0 hti) hCcap hC₀0 hgap hCC hCCt hCtrC hC₀ hc₀gap
    hc₀C₀ htrace hGm hGp hcapL hcapR hmassL hmassR htrial

/-- **Consistency check, family level.**  The trace-split family interface holds for
`traceFamilyOne_a1`, given `CapLowerInput_a1`. -/
theorem traceSplitFamilyInput_one_ag (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α) (R₀ : ℝ)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L)
    {Ccap : ℝ} (hti : TraceIneqInput_a1 Cm Cp L R₀)
    (hcap : CapLowerInput_a1 Cm Cp L α hα Ccap R₀) :
    TraceSplitFamilyInput_ag Cm Cp L α hα Ccap R₀
      (traceFamilyOne_a1 Cm Cp L R₀ hm0 hp0 hR₀L hti) where
  data R hR hR₀ hL := by
    obtain ⟨Gm, Gp, hGm, hGp, hcapL, hcapR, hmassL, hmassR⟩ := hcap.cap R hR hR₀ hL
    exact ⟨bdCapL_a1 Cm Cp L R, bdCapR_a1 Cm Cp L R,
      traceSplitInput_one_ag hR _ hm0 hp0 (hti.ineq R hR hR₀),
      ⟨Gm, Gp, hGm, hGp, hcapL, hcapR, hmassL, hmassR⟩⟩

/-- **Consistency check.**  `mainTheorem_one_a1`, re-derived from `mainTheorem_gen_ag`. -/
theorem mainTheorem_one_ag (Cm Cp : Cap 1) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hR₀L : (Cm.K + Cp.K) * R₀ ≤ L) {Ccap Cif Ctr : ℝ} (hCcap : 0 ≤ Ccap)
    (hti : TraceIneqInput_a1 Cm Cp L R₀)
    (hcap : CapLowerInput_a1 Cm Cp L α hα Ccap R₀)
    (hif : InterfaceTraceInput_a1 Cm Cp L α hα Cif R₀)
    (htr : TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀) :
    MainTheorem 1 Cm Cp L α hL0 hβm hβp (nuOneDim α hα) R₀
      (traceFamilyOne_a1 Cm Cp L R₀ hm0 hp0 hR₀L hti) :=
  mainTheorem_gen_ag Cm Cp L α hL0 hα hβm hβp R₀ hR₀ _ (Cif := Cif) hCcap
    (traceSplitFamilyInput_one_ag Cm Cp L α hα R₀ hm0 hp0 hR₀L hti hcap) hif
    ⟨fun R hR hR₀' hL v => htr.trial R hR hR₀' hL (hti.ineq R hR hR₀') v⟩

end Consistency

end RobinCaps.ThinDomain

end
