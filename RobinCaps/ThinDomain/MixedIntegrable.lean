import RobinCaps.ThinDomain.TraceGenAbs
import RobinCaps.ThinDomain.TraceGenIntegrable
import RobinCaps.Cap.Sharp

/-!
# Discharging the abstract-cap integrability hypotheses, for the flat/hemisphere pair

`RobinCaps/ThinDomain/TraceGenAbs.lean` builds the thin-domain trace datum
`traceDataAbs_tga` for two **abstract** admissible caps `Cm Cp : Cap m` equipped with
abstract trace data, conditional on two remaining Fubini/polar-coordinates facts,
`CapTraceIntegrableAbs_tga` (per cap) and `ContinuousBoundaryIntegrableAbs_tga` (for the pair).

`RobinCaps/ThinDomain/TraceGenIntegrable.lean` already discharges the hemisphere-specific
versions of both facts (`CapTraceIntegrable_tgn` / `ContinuousBoundaryIntegrable_tgn`, for two
copies of `Cap.hemisphere m`).  This file

1. converts the hemisphere `CapTraceIntegrable_tgn` witness into the abstract
   `CapTraceIntegrableAbs_tga` for `Cap.hemisphere m` (field-for-field, the statements coincide),
2. discharges `ContinuousBoundaryIntegrableAbs_tga` for the **mixed** pair
   `Cm := Cap.flat m K hK`, `Cp := Cap.hemisphere m`, and
3. converts the hemisphere `ContinuousBoundaryIntegrable_tgn` witness into the abstract
   `ContinuousBoundaryIntegrableAbs_tga` for two copies of `Cap.hemisphere m`, for completeness.

The workhorse for (2) is `RobinCaps.ThinDomain.integrableOn_lateralDensity_of_continuousOn_closure_tgi`
(`RobinCaps/ThinDomain/TraceGenIntegrable.lean`), which turns out to already be stated for
**arbitrary** `Cm Cp : Cap m` (it is built from `RobinCaps.ThinDomain.intervalIntegrable_areaElement_left`
/ `_bulk` / `_right` in `RobinCaps/ThinDomain/Boundary.lean`, themselves proved for arbitrary
`Cm Cp` from concavity alone via `RobinCaps.Cap.Concave.areaElement_intervalIntegrable`, and from
`RobinCaps.ThinDomain.isCompact_closure_thinDomain` / `mem_closure_thinDomain_lateral`
(`RobinCaps/ThinDomain/BoundaryIntegrable.lean`), likewise general).  In particular no
flat-cap-specific area-element computation is needed: (2) is a direct instantiation.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap RobinCaps.Sobolev RobinCaps.Compact

/-! ## 1. The hemisphere cap-trace integrability, converted to the abstract form -/

/-- **Deliverable 1.**  The hemisphere's `CapTraceIntegrable_tgn` witness
(`RobinCaps.ThinDomain.capTraceIntegrable_tgi`), converted field-for-field into the abstract
`CapTraceIntegrableAbs_tga` for `Cap.hemisphere m` with its concrete trace datum
`capTraceDataHemi_th`. The two statements coincide verbatim. -/
theorem capTraceIntegrableAbs_hemi_mi (m : ℕ) (hm : 1 ≤ m) :
    CapTraceIntegrableAbs_tga (Cap.hemisphere m) (capTraceDataHemi_th m hm) :=
  ⟨(capTraceIntegrable_tgi m hm).integrableOn⟩

/-! ## 2. The mixed flat/hemisphere continuous-boundary integrability -/

/-- **Deliverable 2.**  `ContinuousBoundaryIntegrableAbs_tga`, discharged for the mixed pair
`Cm := Cap.flat m K hK`, `Cp := Cap.hemisphere m`.  A direct instantiation of
`integrableOn_lateralDensity_of_continuousOn_closure_tgi`, which is already general in the two
caps. -/
theorem continuousBoundaryIntegrableAbs_mixed_mi (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) :
    ContinuousBoundaryIntegrableAbs_tga m (Cap.flat m K hK) (Cap.hemisphere m) L R hR hL where
  integrableOn u hc :=
    integrableOn_lateralDensity_of_continuousOn_closure_tgi hR hL (hc.pow 2)

/-! ## 3. The two-hemisphere continuous-boundary integrability, converted to the abstract form -/

/-- **Deliverable 3.**  The hemisphere pair's `ContinuousBoundaryIntegrable_tgn` witness
(`RobinCaps.ThinDomain.continuousBoundaryIntegrable_tgi`), converted field-for-field into the
abstract `ContinuousBoundaryIntegrableAbs_tga` for two copies of `Cap.hemisphere m`.  The two
statements coincide verbatim. -/
theorem continuousBoundaryIntegrableAbs_hemi_mi (m : ℕ) (hm : 1 ≤ m) (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L) :
    ContinuousBoundaryIntegrableAbs_tga m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL :=
  ⟨(continuousBoundaryIntegrable_tgi m hm L R hR hL).integrableOn⟩

end RobinCaps.ThinDomain

end

