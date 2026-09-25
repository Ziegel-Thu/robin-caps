import RobinCaps.Hausdorff.AreaIface

/-!
# The unit sphere: `toSphere` versus Hausdorff measure — interface (wave 12, Problem A)

`hemi n z = (z, √(1 − ‖z‖²))` is the upper-hemisphere chart of the unit sphere of
`ℝ^{n+1} = EuclideanSpace ℝ (Fin (n+1))` over the unit ball of `ℝ^n` (last coordinate positive).
The three statements, proved in `Hausdorff/SphereChartVolume.lean`,
`Hausdorff/SphereChartHausdorff.lean` and `Hausdorff/SphereHausdorff.lean`:

* `HemiToSphereProp n` — mathlib's sphere measure `volume.toSphere` of a chart image is
  `∫_A (1 − ‖z‖²)^{-1/2} dz`;
* `HemiHausdorffProp n` — the Hausdorff measure `μH[n]` of a chart image is
  `hConst n · ∫_A (1 − ‖z‖²)^{-1/2} dz` (area formula);
* `SphereHausdorffProp n` — on the whole sphere, `μH[n] = hConst n · volume.toSphere`, i.e.
  `volume.toSphere` is the `n`-dimensional Hausdorff measure normalised to agree with Lebesgue
  measure on `ℝ^n`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-- The upper-hemisphere chart `z ↦ (z, √(1 − ‖z‖²))`. -/
def hemi (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Fin.snoc (fun i => z i) (Real.sqrt (1 - ‖z‖ ^ 2)))

/-- The chart density `(1 − ‖z‖²)^{-1/2}`. -/
def hemiDensity (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.sqrt (1 - ‖z‖ ^ 2))

/-- `volume.toSphere` of a chart image. -/
def HemiToSphereProp (n : ℕ) : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin n)), A ⊆ ball 0 1 → MeasurableSet A →
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        {x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 | (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ hemi n '' A}
      = ∫⁻ z in A, hemiDensity n z

/-- `μH[n]` of a chart image. -/
def HemiHausdorffProp (n : ℕ) : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin n)), A ⊆ ball 0 1 → MeasurableSet A →
    (Measure.hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (hemi n '' A)
      = hConst n * ∫⁻ z in A, hemiDensity n z

/-- **`toSphere` is normalised Hausdorff measure** on the unit sphere of `ℝ^{n+1}`. -/
def SphereHausdorffProp (n : ℕ) : Prop :=
  ∀ s : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1), MeasurableSet s →
    (Measure.hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin (n + 1))))
        ((↑) '' s)
      = hConst n * (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere s

end RobinCaps.Hausdorff

end
