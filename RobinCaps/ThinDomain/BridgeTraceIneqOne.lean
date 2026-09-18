import RobinCaps.ThinDomain.AssemblyOne
import RobinCaps.ThinDomain.BridgeRadial

/-!
# Discharging `TraceIneqInput_a1` for the hemispherical caps

`RobinCaps/ThinDomain/AssemblyOne.lean` records the planar trace inequality for the whole
admissible radius range as the interface `Prop`

```
structure TraceIneqInput_a1 (Cm Cp : Cap 1) (L R₀ : ℝ) : Prop where
  ineq : ∀ R : ℝ, 0 < R → R < R₀ → TraceIneqOne Cm Cp L R
```

and `RobinCaps/ThinDomain/BridgeRadial.lean` proves the single-radius statement

```
traceIneqOne_hemisphere_br (hR : 0 < R) (hL : 2 * R < L) :
    TraceIneqOne (Cap.hemisphere 1) (Cap.hemisphere 1) L R
```

for the planar stadium.  This file is the (purely arithmetic) bridge between the two: for
`R₀ ≤ L / 2` every admissible radius `0 < R < R₀` satisfies `2 R < L`, so the family version
holds.  Combined with `traceFamilyOne_a1` it produces the recorded `TraceFamily` for the
stadium.

## Main results

* `traceIneqInput_hemisphere_bti` — the interface `Prop` for the hemispherical caps;
* `traceIneqInput_le_bti` — monotonicity of the interface in the radius threshold;
* `traceFamilyHemi_bti` — the resulting `TraceFamily`, with the unfolding lemma
  `traceFamilyHemi_bti_apply`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Cap

set_option autoImplicit false
set_option linter.unusedVariables false

variable {Cm Cp : Cap 1} {L R₀ R₀' : ℝ}

/-- **`TraceIneqInput_a1` for the planar stadium.**  If the radius threshold satisfies
`R₀ ≤ L / 2`, then every admissible radius `0 < R < R₀` obeys `2 R < L`, so the trace
inequality `traceIneqOne_hemisphere_br` of `RobinCaps/ThinDomain/BridgeRadial.lean` applies at
every such radius. -/
theorem traceIneqInput_hemisphere_bti (L : ℝ) (hL0 : 0 < L) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hR₀L : R₀ ≤ L / 2) :
    TraceIneqInput_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R₀ :=
  ⟨fun R hR hRlt => traceIneqOne_hemisphere_br hR (by linarith)⟩

/-- **The interface is monotone in the radius threshold**: shrinking `R₀` only shrinks the
range of radii over which the trace inequality is asserted. -/
theorem traceIneqInput_le_bti (h : TraceIneqInput_a1 Cm Cp L R₀) (hle : R₀' ≤ R₀) :
    TraceIneqInput_a1 Cm Cp L R₀' :=
  ⟨fun R hR hRlt => h.ineq R hR (lt_of_lt_of_le hRlt hle)⟩

/-- The threshold hypothesis of `traceFamilyOne_a1` for the hemispherical caps, in the form
`(K₋ + K₊) R₀ ≤ L`, from `R₀ ≤ L / 2`. -/
theorem hemisphere_two_mul_le_bti {R₀ : ℝ} (hR₀L : R₀ ≤ L / 2) :
    ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R₀ ≤ L := by
  rw [hemisphere_K_st]; linarith

/-- **The recorded trace family of the planar stadium.**  This is `traceFamilyOne_a1` fed with
`traceIneqInput_hemisphere_bti`. -/
def traceFamilyHemi_bti (L : ℝ) (hL0 : 0 < L) {R₀ : ℝ} (hR₀ : 0 < R₀) (hR₀L : R₀ ≤ L / 2) :
    TraceFamily (Cap.hemisphere 1) (Cap.hemisphere 1) L R₀ :=
  traceFamilyOne_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R₀
    (hemisphere_theta_zero_a1 1) (hemisphere_theta_zero_a1 1)
    (hemisphere_two_mul_le_bti hR₀L) (traceIneqInput_hemisphere_bti L hL0 hR₀ hR₀L)

/-- Unfolding `traceFamilyHemi_bti`: at each admissible radius it is the `traceDataOne` built
from the stadium trace inequality `traceIneqOne_hemisphere_br`. -/
theorem traceFamilyHemi_bti_apply (L : ℝ) (hL0 : 0 < L) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hR₀L : R₀ ≤ L / 2) (R : ℝ) (hR : 0 < R) (hRlt : R < R₀) :
    traceFamilyHemi_bti L hL0 hR₀ hR₀L R hR hRlt
      = traceDataOne hR (hLK_st (by linarith)) (hemisphere_theta_zero_a1 1)
          (hemisphere_theta_zero_a1 1) (traceIneqOne_hemisphere_br hR (by linarith)) :=
  rfl

end RobinCaps.ThinDomain
