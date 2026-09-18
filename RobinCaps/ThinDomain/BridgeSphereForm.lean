import RobinCaps.ThinDomain.TraceGenBulk
import RobinCaps.Sobolev.SphereTraceForm

/-!
# Discharging the sphere-form interface of `TraceGenBulk`

`RobinCaps/ThinDomain/TraceGenBulk.lean` states the identity "sphere-trace form = Rellich form
`bdR`" as the interface `SphFormEqBdR_tgb m R`.  `RobinCaps/Sobolev/SphereTraceForm.lean` proves
exactly this identity (`sphForm_eq_bdR_stf`, by C¹ density).  This file connects the two, so the
bulk lateral boundary form of the general-`m` thin domain is unconditionally `bdCyl (bdR m R)`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Compact RobinCaps.Cap

/-- The interface `SphFormEqBdR_tgb` holds for every `m ≥ 1`, `R > 0`. -/
theorem sphFormEqBdR_bsf (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 < R) : SphFormEqBdR_tgb m R := by
  intro v
  have h := sphForm_eq_bdR_stf hm hR v v
  unfold sphForm_stf at h
  simpa only [sq] using h

/-- **The bulk lateral boundary form is `bdCyl (bdR m R)`, unconditionally.** -/
theorem integral_bulkDensity_bsf {m : ℕ} (hm : 1 ≤ m) {L R : ℝ} {Cm Cp : Cap m} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), bulkDensity_tgb hR hL u x)
      = bdCyl (bdR m R) (restrictBulkP_tgb hR u) (restrictBulkP_tgb hR u) :=
  integral_bulkDensity_tgb (sphFormEqBdR_bsf m hm R hR) hR hL u

end RobinCaps.ThinDomain
