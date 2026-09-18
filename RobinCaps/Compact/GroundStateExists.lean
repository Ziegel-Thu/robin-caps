import RobinCaps.Compact.Rellich
import RobinCaps.Compact.BoundaryNonneg
import RobinCaps.Compact.GroundStateGap

/-!
# Existence of the transverse Robin ground state on `B_n(R)` for small `R`

This file discharges the two hypotheses of `hasTransverseGroundState_of`
(`RobinCaps/Compact/GroundStateGap.lean`):

* Rellich–Kondrachov compactness on every ball (`rellichSeq`, from `Rellich.lean`);
* nonnegativity of the Rellich boundary form `bdR` (`bdR_nonneg`, from `BoundaryNonneg.lean`).

The result is the target `RobinCaps.ThinDomain.HasTransverseGroundState n α R (bdR n R)` of
`RobinCaps/ThinDomain/GroundState.lean`, unconditionally, for every `0 ≤ α` and every
`0 < R < R₀(n, α)`.  The boundary form `bdR` is the Rellich-identity form
`R⁻¹ ∫_{B_R} (n u v + u ⟪x, ∇v⟫ + v ⟪x, ∇u⟫)`, which coincides with the sphere integral
`∫_{∂B_R} u v dσ` on `C¹` functions (`bdR_ofC1`) and is its unique `H¹`-continuous extension.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak RobinCaps.ThinDomain

/-- **The transverse ground state exists for small `R`.**  For `1 ≤ n` and `0 ≤ α` there is
`R₀ > 0` such that for every `0 < R < R₀` the Robin ground state on `B_n(R)` with the boundary
form `bdR n R` exists, with the gap `λ₂ − ν_R ≥ c R⁻²` built into the data. -/
theorem hasTransverseGroundState_bdR (n : ℕ) (hn : 1 ≤ n) {α : ℝ} (hα : 0 ≤ α) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      HasTransverseGroundState n α R (bdR n R) :=
  hasTransverseGroundState_of hn hα (fun _ hR => rellichSeq n hR)
    (fun _ hR u => bdR_nonneg hn hR u)

end RobinCaps.Compact

end

#print axioms RobinCaps.Compact.hasTransverseGroundState_bdR
#print axioms RobinCaps.Compact.rellich_ball
#print axioms RobinCaps.Compact.bdR_nonneg
#print axioms RobinCaps.Compact.bdR_ofC1
#print axioms RobinCaps.Compact.poincare_wirtinger_ball
