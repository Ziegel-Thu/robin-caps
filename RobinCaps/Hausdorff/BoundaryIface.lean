import RobinCaps.Hausdorff.SphereIface
import RobinCaps.Sobolev.ConvexDensity
import RobinCaps.ThinDomain.Boundary

/-!
# The boundary of `Ω_R`: `boundaryIntegral` versus Hausdorff measure — interface (wave 12, A4)

The cap profiles are only concave, so the lateral boundary of `Ω_R` is a Lipschitz (not `C¹`)
surface of revolution. The `C¹` area formula `AreaFormulaProp` is therefore upgraded to the
general form of mathlib's `Jacobian.lean` (derivative *within* the set at every point; no
continuity of the derivative, no injectivity of the derivative).

* `AreaFormulaInjProp m k` — area formula when `F'` is injective at every point of `S`;
* `AreaFormulaGenProp m k` — area formula in full generality (`F` injective on `S`);
* `AreaLintegralProp m k` — the integral form `∫⁻_{F '' S} g dμH[m] = ∫⁻_S g(F x) √gramDet dμH[m]`;
* `latSurf`, `diskL`, `diskR`, `FrontierProp` — the frontier of `Ω_R` (in `CapSpace m`) is the
  lateral surface `{‖z‖ = r_R(x), |x| < L/2}` plus the two closed end disks;
* `BoundaryHausdorffProp` — the target: for continuous `g ≥ 0`,
  `∫⁻_{∂Ω_R'} g dμH[m] = hConst m · boundaryIntegral g`, where `Ω_R' = toEuclid '' Ω_R ⊆ ℝ^{m+1}`.
  Equivalently: `boundaryIntegral` is integration against the `m`-dimensional Hausdorff measure
  normalised to agree with Lebesgue measure on `ℝ^m` (`(hConst m)⁻¹ • μH[m]`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace RobinCaps.Hausdorff

open RobinCaps.Domain RobinCaps.Cap RobinCaps.ThinDomain

/-- Area formula for maps with injective derivative, derivative within `S`. -/
def AreaFormulaInjProp (m k : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin m))) (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (F' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)),
    MeasurableSet S → (∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) → InjOn F S →
    (∀ x ∈ S, Function.Injective (F' x)) →
      (Measure.hausdorffMeasure (m : ℝ)) (F '' S)
        = ∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
            ∂(Measure.hausdorffMeasure (m : ℝ))

/-- **General area formula** (mathlib `Jacobian.lean` form, different dimensions). -/
def AreaFormulaGenProp (m k : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin m))) (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (F' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)),
    MeasurableSet S → (∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) → InjOn F S →
      (Measure.hausdorffMeasure (m : ℝ)) (F '' S)
        = ∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
            ∂(Measure.hausdorffMeasure (m : ℝ))

/-- **Area formula, integral form.** -/
def AreaLintegralProp (m k : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin m))) (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (F' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)),
    MeasurableSet S → (∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) → InjOn F S →
    ∀ g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞, Measurable g →
      ∫⁻ y in F '' S, g y ∂(Measure.hausdorffMeasure (m : ℝ))
        = ∫⁻ x in S, g (F x) * ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
            ∂(Measure.hausdorffMeasure (m : ℝ))

/-- **Area formula, integral form, injective derivative.** -/
def AreaLintegralInjProp (m k : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin m))) (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (F' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)),
    MeasurableSet S → (∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) → InjOn F S →
    (∀ x ∈ S, Function.Injective (F' x)) →
    ∀ g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞, Measurable g →
      ∫⁻ y in F '' S, g y ∂(Measure.hausdorffMeasure (m : ℝ))
        = ∫⁻ x in S, g (F x) * ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
            ∂(Measure.hausdorffMeasure (m : ℝ))

/-- The lateral surface `{(x, z) : |x| < L/2, ‖z‖ = r_R(x)}` of `Ω_R`. -/
def latSurf {m : ℕ} (Cm Cp : Cap m) (L R : ℝ) : Set (CapSpace m) :=
  {p | -L/2 < p.1 ∧ p.1 < L/2 ∧ ‖p.2‖ = profile Cm Cp L R p.1}

/-- The closed left end disk `{-L/2} × closedBall 0 (R θ₋(0))`. -/
def diskL {m : ℕ} (Cm : Cap m) (L R : ℝ) : Set (CapSpace m) :=
  {p | p.1 = -L/2 ∧ ‖p.2‖ ≤ R * Cm.θ 0}

/-- The closed right end disk `{L/2} × closedBall 0 (R θ₊(0))`. -/
def diskR {m : ℕ} (Cp : Cap m) (L R : ℝ) : Set (CapSpace m) :=
  {p | p.1 = L/2 ∧ ‖p.2‖ ≤ R * Cp.θ 0}

/-- The frontier of `Ω_R` is the lateral surface plus the two closed end disks. -/
def FrontierProp {m : ℕ} (Cm Cp : Cap m) (L R : ℝ) : Prop :=
  frontier (thinDomain Cm Cp L R) = latSurf Cm Cp L R ∪ diskL Cm L R ∪ diskR Cp L R

/-- **Target (A4)**: `boundaryIntegral` is integration over `∂Ω_R` against `μH[m] / hConst m`. -/
def BoundaryHausdorffProp {m : ℕ} (Cm Cp : Cap m) (L R : ℝ) : Prop :=
  ∀ g : CapSpace m → ℝ, Continuous g → (∀ p, 0 ≤ g p) →
    ∫⁻ y in frontier (RobinCaps.Sobolev.thinDomainE_cd Cm Cp L R),
        ENNReal.ofReal (g (ofEuclid m y))
        ∂(Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = hConst m * ENNReal.ofReal (boundaryIntegral Cm Cp L R g)

end RobinCaps.Hausdorff

end
