import Mathlib

/-!
# Area formula for Hausdorff measure: interface (wave 12, Problem A)

mathlib's `μH[d]` is the raw covering measure `∑ diam^d` (no `ω_d / 2^d` normalisation). On
`EuclideanSpace ℝ (Fin m)` it is an additive Haar measure (`isAddHaarMeasure_hausdorffMeasure`),
hence a constant multiple `hConst m • volume` of Lebesgue measure; computing the constant
(`2^m / ω_m`) is the isodiametric inequality, which is not needed here.

The statements below are phrased so that the constant never appears: the area formula uses
`μH[m]` itself on the parameter domain.

* `HausdorffVolumeProp m` — `μH[m] = hConst m • volume` on `ℝ^m`, with `0 < hConst m < ∞`;
* `LinearImageProp m k` — for an injective linear `A : ℝ^m → ℝ^k`,
  `μH[m] (A '' S) = √det (A* A) · μH[m] S`;
* `NearLinearProp m k` — if `F` is `ε`-close to a linear `A` with `‖A v‖ ≥ σ ‖v‖` on `S`
  (in the sense `‖F x − F y − A (x − y)‖ ≤ ε ‖x − y‖`), then `μH[m] (F '' S)` is between
  `((σ−ε)/σ)^m` and `((σ+ε)/σ)^m` times `μH[m] (A '' S)`;
* `AreaFormulaProp m k` — the area formula for an injective `C¹` immersion `F : U → ℝ^k`,
  `U ⊆ ℝ^m` open: `μH[m] (F '' S) = ∫⁻_S √det (DF(x)* DF(x)) dμH[m]`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-- The normalising constant: `μH[m] (closedBall 0 1) / volume (closedBall 0 1)` in `ℝ^m`. -/
def hConst (m : ℕ) : ℝ≥0∞ :=
  (Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin m)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) /
    (volume : Measure (EuclideanSpace ℝ (Fin m))) (Metric.closedBall 0 1)

/-- The Gram determinant `det (A* A)` of a linear map `A : ℝ^m → ℝ^k`. -/
def gramDet {m k : ℕ} (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) : ℝ :=
  LinearMap.det (((ContinuousLinearMap.adjoint A).comp A : EuclideanSpace ℝ (Fin m) →L[ℝ] _) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))

/-- `μH[m]` on `ℝ^m` is `hConst m` times Lebesgue measure, with a finite positive constant. -/
def HausdorffVolumeProp (m : ℕ) : Prop :=
  (Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin m))) = hConst m • volume ∧
    0 < hConst m ∧ hConst m < ∞

/-- Hausdorff measure of an injective linear image. -/
def LinearImageProp (m k : ℕ) : Prop :=
  ∀ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k), Function.Injective A →
    ∀ S : Set (EuclideanSpace ℝ (Fin m)),
      (Measure.hausdorffMeasure (m : ℝ)) (A '' S)
        = ENNReal.ofReal (Real.sqrt (gramDet A)) * (Measure.hausdorffMeasure (m : ℝ)) S

/-- Comparison of `F '' S` with `A '' S` when `F` is uniformly close to the linear map `A`. -/
def NearLinearProp (m k : ℕ) : Prop :=
  ∀ (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) (σ ε : ℝ),
    0 < σ → 0 ≤ ε → ε < σ → (∀ v, σ * ‖v‖ ≤ ‖A v‖) →
    ∀ S : Set (EuclideanSpace ℝ (Fin m)),
      (∀ x ∈ S, ∀ y ∈ S, ‖F x - F y - A (x - y)‖ ≤ ε * ‖x - y‖) →
      ENNReal.ofReal (((σ - ε) / σ) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (A '' S)
          ≤ (Measure.hausdorffMeasure (m : ℝ)) (F '' S) ∧
        (Measure.hausdorffMeasure (m : ℝ)) (F '' S)
          ≤ ENNReal.ofReal (((σ + ε) / σ) ^ m) * (Measure.hausdorffMeasure (m : ℝ)) (A '' S)

/-- **The area formula** for an injective `C¹` immersion of an open `U ⊆ ℝ^m` into `ℝ^k`. -/
def AreaFormulaProp (m k : ℕ) : Prop :=
  ∀ (U : Set (EuclideanSpace ℝ (Fin m))) (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (F' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)),
    IsOpen U → (∀ x ∈ U, HasFDerivAt F (F' x) x) → ContinuousOn F' U → InjOn F U →
    (∀ x ∈ U, Function.Injective (F' x)) →
    ∀ S ⊆ U, MeasurableSet S →
      (Measure.hausdorffMeasure (m : ℝ)) (F '' S)
        = ∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x)))
            ∂(Measure.hausdorffMeasure (m : ℝ))

end RobinCaps.Hausdorff

end
