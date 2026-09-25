import RobinCaps.Hausdorff.AreaFormula
import RobinCaps.Hausdorff.AreaFormulaInj
import RobinCaps.Hausdorff.GramMeasurable
import RobinCaps.Hausdorff.SphereChartVolume
import RobinCaps.Hausdorff.SphereChartHausdorff
import RobinCaps.Hausdorff.SphereHausdorff

/-!
# Wave 12 (Problem A): area formula and the sphere measure — unconditional statements

mathlib's `μH[d]` is the unnormalised Hausdorff measure (`∑ diam^d`); on `ℝ^m` it equals
`hConst m • volume` for a constant `0 < hConst m < ∞` (whose value `2^m/ω_m` would need the
isodiametric inequality and is not used).  The statements below never depend on its value.

* `RobinCaps.hausdorff_eq_smul_volume_top`: `μH[m] = hConst m • volume` on `ℝ^m`.
* `RobinCaps.areaFormula_C1_top`: area formula for injective `C¹` immersions of open sets.
* `RobinCaps.areaFormula_top`: area formula for maps with a derivative within a measurable set
  (injective derivative), in the form of mathlib's `Jacobian.lean`.
* `RobinCaps.areaFormula_lintegral_top`: its integral form.
* `RobinCaps.sphere_hausdorff_top`: on the unit sphere of `ℝ^{n+1}`,
  `μH[n] = hConst n · volume.toSphere`, i.e. mathlib's sphere measure `toSphere` (used for the
  project's `sphereIntegral`/`sphereMeasure`) is the `n`-dimensional Hausdorff measure
  normalised to agree with Lebesgue measure on `ℝ^n`.
-/

namespace RobinCaps

open RobinCaps.Hausdorff

theorem hausdorff_eq_smul_volume_top (m : ℕ) : HausdorffVolumeProp m :=
  hausdorffVolume_hlin m

theorem areaFormula_C1_top (m k : ℕ) : AreaFormulaProp m k :=
  areaFormula_har m k (hausdorffVolume_hlin m) (linearImage_hlin m k) (nearLinear_hnl m k)

theorem areaFormula_top (m k : ℕ) : AreaFormulaInjProp m k :=
  areaFormulaInj_agi m k

theorem areaFormula_lintegral_top (m k : ℕ) : AreaLintegralInjProp m k :=
  areaLintegralInj_gam m k

theorem sphere_hausdorff_top (n : ℕ) : SphereHausdorffProp n :=
  sphereHausdorff_shd n (hemiToSphere_scv n) (hemiHausdorff_sch n (areaFormula_C1_top n (n + 1)))

end RobinCaps
