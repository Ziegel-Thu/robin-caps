import RobinCaps.ThinDomain.AssemblyOne
import RobinCaps.ThinDomain.TrialAssemblyOne
import RobinCaps.ThinDomain.TrialOne

/-!
# Bridge: the `TrialEnergyInput_a1` interface of `AssemblyOne` from the `m = 1` trial bounds

`RobinCaps/ThinDomain/AssemblyOne.lean` carries out the final `m = 1` global comparison
against an interface; one of its hypotheses is the `Prop`

`TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀`,

i.e. `eq:trial-energy`: for every admissible radius `R < R₀` the renormalised energy of the
trial extension `liftQ … (psiOne_a1 α R hα hR) v` is bounded by the one-dimensional Robin form
with the shifted Robin parameters `β_∓ + Ctr · R`.

This file discharges that interface.  Nothing new is proved here: the two ingredients are

* `trial_energy_field_one` (`RobinCaps/ThinDomain/TrialAssemblyOne.lean`), which supplies the
  bound for every `R ≤ 1` at which a `TransverseExpansionData 1 α R (groundStateOneReg …) Cexp`
  is available, and
* `transverseExpansionData_one` (`RobinCaps/ThinDomain/TrialOne.lean`), which supplies such an
  expansion datum for every `R < R₀`, with `0 < R₀ ≤ 1`.

The only glue needed is that `(groundStateOneReg α R hα hR).psi` and
`(groundStateOneReg α R hα hR).nu` are definitionally `psiOne_a1 α R hα hR` and
`nuR α R hα hR` (see `groundStateOneReg_psi`, `groundStateOneReg_nu`), together with the
observation `R < R₀ ≤ 1 → R ≤ 1`.

Finally `trialEnergyInput_le_bt` records the (trivial) monotonicity of the interface in the
radius threshold `R₀`, which the final assembly needs in order to align the thresholds of the
four interface inputs.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap

/-- **Monotonicity of `TrialEnergyInput_a1` in the radius threshold.**  The statement is a
universally quantified implication over `R < R₀`, so shrinking `R₀` preserves it. -/
theorem trialEnergyInput_le_bt {Cm Cp : Cap 1} {L α : ℝ} {hα : 0 < α}
    {hm0 : Cm.θ 0 = 0} {hp0 : Cp.θ 0 = 0} {Ctr R₀ R₀' : ℝ}
    (h : TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀) (hle : R₀' ≤ R₀) :
    TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀' :=
  ⟨fun R hR hRlt => h.trial R hR (lt_of_lt_of_le hRlt hle)⟩

/-- **`eq:trial-energy` for `m = 1`: the `TrialEnergyInput_a1` interface of
`RobinCaps/ThinDomain/AssemblyOne.lean` holds.**

There is a nonnegative constant `Ctr` and a threshold `0 < R₀ ≤ 1` such that for every
`0 < R < R₀` with `(K_∓ + K_±) R < L`, every planar trace inequality `TraceIneqOne` and every
`v : H¹(0, ℓ_R)/N`,

`E_R[𝒯_R v] - ν_R ‖𝒯_R v‖² ≤ a_{β_∓ + Ctr·R, β_± + Ctr·R; I_R}[v]`. -/
theorem trialEnergyInput_one_bt (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) :
    ∃ Ctr R₀ : ℝ, 0 ≤ Ctr ∧ 0 < R₀ ∧ R₀ ≤ 1 ∧
      TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀ := by
  obtain ⟨Cexp, R₀, hR₀, hR₀1, hexp⟩ := transverseExpansionData_one α hα
  obtain ⟨A, hA0, hA⟩ := trial_energy_field_one α hα Cm Cp L Cexp hm0 hp0
  refine ⟨A, R₀, hA0, hR₀, hR₀1, ⟨fun R hR hRlt hL hti v => ?_⟩⟩
  exact hA R hR (le_of_lt (lt_of_lt_of_le hRlt hR₀1)) hL hti (hexp R hR hRlt) v

/-- **The same, at any smaller threshold.**  This is the form the final assembly consumes: the
other three interface inputs of `AssemblyOne` come with thresholds of their own, and the
assembly instantiates all four at the minimum. -/
theorem trialEnergyInput_one_of_le_bt (Cm Cp : Cap 1) (L α : ℝ) (hα : 0 < α)
    (hm0 : Cm.θ 0 = 0) (hp0 : Cp.θ 0 = 0) :
    ∃ Ctr R₀ : ℝ, 0 ≤ Ctr ∧ 0 < R₀ ∧ R₀ ≤ 1 ∧
      ∀ R₀' : ℝ, 0 < R₀' → R₀' ≤ R₀ →
        TrialEnergyInput_a1 Cm Cp L α hα hm0 hp0 Ctr R₀' := by
  obtain ⟨Ctr, R₀, hCtr, hR₀, hR₀1, h⟩ := trialEnergyInput_one_bt Cm Cp L α hα hm0 hp0
  exact ⟨Ctr, R₀, hCtr, hR₀, hR₀1, fun _ _ hle => trialEnergyInput_le_bt h hle⟩

end RobinCaps.ThinDomain

end

