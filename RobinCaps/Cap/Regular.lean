import Mathlib
import RobinCaps.Cap.Basic

/-!
# Weak regularity of cap profiles (shared predicate)

The manuscript's admissible profiles (`eq:cap-definition`) are concave and
non-increasing on the open interval `(-K,0)`; they are therefore continuous
there, differentiable off a countable set, and the area element
`θ^{m-1}√(1+θ'²)` is (improperly) integrable.  The earlier predicate
`ProfileRegular` (`RobinCaps/Cap/SharpInequality.lean`) demanded a *continuous
derivative on the closed interval*, which excludes the hemisphere itself
(`θ' → -∞` at the terminal point).  This file introduces the weaker predicate
`ProfileAC` under which all the one-dimensional FTC arguments still go
through, via `intervalIntegral.integral_eq_of_hasDerivWithinAt_off_countable_of_le`.

Conventions: the terminal radius of the manuscript is the left limit
`θ(0⁻)`; under `ProfileAC` (continuity on the closed interval) it equals the
recorded value `C.θ 0`, so `terminalArea` is the manuscript's terminal disk.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps
namespace Cap

variable {m : ℕ}

/-- **Weak profile regularity.**
* `θ` is continuous on the closed axial interval `[-K,0]` (so `θ(-K) = θ(-K⁺)`
  and `θ(0) = θ(0⁻)`, the manuscript's terminal radius);
* the entrance value is `θ(-K) = 1`;
* `θ` is differentiable at every point of `(-K,0)` off a countable set;
* the area element `θ^{m-1}√(1+θ'²)` is interval integrable on `(-K,0)`. -/
def ProfileAC (C : Cap m) : Prop :=
  ContinuousOn C.θ (Icc (-C.K) 0) ∧
  C.θ (-C.K) = 1 ∧
  (∃ S : Set ℝ, S.Countable ∧ ∀ s ∈ Ioo (-C.K) 0 \ S, HasDerivAt C.θ (deriv C.θ s) s) ∧
  IntervalIntegrable (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
    volume (-C.K) 0

theorem ProfileAC.continuousOn {C : Cap m} (h : ProfileAC C) :
    ContinuousOn C.θ (Icc (-C.K) 0) := h.1

theorem ProfileAC.entrance {C : Cap m} (h : ProfileAC C) : C.θ (-C.K) = 1 := h.2.1

theorem ProfileAC.hasDerivAt_off_countable {C : Cap m} (h : ProfileAC C) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ s ∈ Ioo (-C.K) 0 \ S, HasDerivAt C.θ (deriv C.θ s) s :=
  h.2.2.1

theorem ProfileAC.areaElement_intervalIntegrable {C : Cap m} (h : ProfileAC C) :
    IntervalIntegrable (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
      volume (-C.K) 0 := h.2.2.2

/-- **`C¹` profile regularity on the open interval.**  Continuity on the closed
interval, entrance value `1`, differentiability at every point of `(-K,0)`,
continuity of the derivative on the *open* interval (the derivative may blow up
at the terminal point, as for the hemisphere), and integrability of the area
element.  This is strictly weaker than `ProfileRegular` and strictly stronger
than `ProfileAC`; it holds for the hemisphere, the flat cap, the truncated
semicircle, and a hemisphere extended by a straight cylinder. -/
def ProfileC1 (C : Cap m) : Prop :=
  ContinuousOn C.θ (Icc (-C.K) 0) ∧
  C.θ (-C.K) = 1 ∧
  (∀ s ∈ Ioo (-C.K) 0, HasDerivAt C.θ (deriv C.θ s) s) ∧
  ContinuousOn (fun s => deriv C.θ s) (Ioo (-C.K) 0) ∧
  IntervalIntegrable (fun s => (C.θ s) ^ (m - 1) * Real.sqrt (1 + (deriv C.θ s) ^ 2))
    volume (-C.K) 0

theorem ProfileC1.profileAC {C : Cap m} (h : ProfileC1 C) : ProfileAC C :=
  ⟨h.1, h.2.1, ⟨∅, Set.countable_empty, fun s hs => h.2.2.1 s hs.1⟩, h.2.2.2.2⟩

/-- Left-continuity of the profile at the terminal point: the recorded value
`θ 0` is the manuscript's terminal radius `θ(0⁻)`. -/
def TerminalContinuous (C : Cap m) : Prop :=
  Tendsto C.θ (𝓝[<] (0 : ℝ)) (𝓝 (C.θ 0))

end Cap
end RobinCaps
