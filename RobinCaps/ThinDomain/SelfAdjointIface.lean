import RobinCaps.ThinDomain.Boundary
import RobinCaps.ThinDomain.H1PQuotient

/-!
# The self-adjoint Robin Laplacian — interface (wave 13)

* `SelfAdjointCriterionProp` — an abstract criterion in a real Hilbert space: a symmetric,
  nonnegative `LinearPMap` `A` with `A + 1` surjective (every `h` is `A x + x` for some `x` in the domain) is
  self-adjoint (`IsSelfAdjoint A`, i.e. `A† = A`, mathlib's `LinearPMap.adjoint`).
* `RobinLaxMilgramProp td α` — solvability of `(−Δ + 1) v = h` with the Robin condition, weakly:
  for every `h ∈ L²(Ω_R)` there is `v ∈ H¹(Ω_R)` with
  `∫∇v·∇φ + α bd(v, φ) + ∫ v φ = ∫ h φ` for all `φ ∈ H¹(Ω_R)`.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap

/-- Abstract criterion: symmetric + nonnegative + `A + 1` surjective ⇒ self-adjoint. -/
def SelfAdjointCriterionProp : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H),
    (∀ x y : A.domain, ⟪A x, (y : H)⟫ = ⟪(x : H), A y⟫) →
    (∀ x : A.domain, 0 ≤ ⟪A x, (x : H)⟫) →
    (∀ h : H, ∃ x : A.domain, A x + (x : H) = h) →
    IsSelfAdjoint A

/-- Weak solvability of the Robin problem `(−Δ + 1) v = h`. -/
def RobinLaxMilgramProp {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (td : TraceData Cm Cp L R) (α : ℝ) :
    Prop :=
  ∀ h : CapSpace m → ℝ, MemLp h 2 (volume.restrict (thinDomain Cm Cp L R)) →
    ∃ v : H1P (thinDomain Cm Cp L R), ∀ φ : H1P (thinDomain Cm Cp L R),
      dirichletBilinP v φ + α * td.bd v φ + massBilinP v φ
        = ∫ p in thinDomain Cm Cp L R, h p * φ.toFun p

end RobinCaps.ThinDomain

end
