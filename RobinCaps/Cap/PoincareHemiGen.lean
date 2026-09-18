import RobinCaps.Cap.LowerWeak
import RobinCaps.ThinDomain.Reflect
import RobinCaps.Compact.Poincare
import RobinCaps.Compact.Rellich

/-!
# The Poincaré–Wirtinger inequality on the hemispherical cap, in every dimension

This file discharges the `CapPoincare` interface of `RobinCaps/Cap/LowerWeak.lean` for the
hemispherical cap `Cap.hemisphere m`, for every `m`, by **even reflection to the unit ball**
(`RobinCaps/ThinDomain/Reflect.lean`) together with the Poincaré–Wirtinger inequality on the
ball (`RobinCaps/Compact/Poincare.lean`), whose Rellich hypothesis is supplied by
`RobinCaps/Compact/Rellich.lean`.

This is pure plumbing: given `u ∈ H¹(𝒞)`, its even reflection `v := reflectEven u` lies in
`H¹(B_1)`; subtracting the mean `t` of `v` on `B_1` from `u` reflects to (literally, pointwise)
the mean-zero part of `v`, so the ball Poincaré inequality applies to it directly, doubling both
sides via `mass_reflectEven` / `dirichlet_reflectEven` to land back on `massP` / `dirichletP`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Compact

noncomputable section

/-- **The Poincaré–Wirtinger inequality on the hemispherical cap, every dimension.**

Obtained from the ball inequality (`RobinCaps.Compact.poincare_wirtinger_ball`) by even
reflection: for `u ∈ H¹(𝒞)`, letting `t` be the mean of `reflectEven u` on `B_1`, the reflection
of `u − t` is (pointwise) the mean-zero part of `reflectEven u`, so the ball Poincaré inequality
gives `mass (reflectEven (u − t)) ≤ C · dirichlet (reflectEven u)`, and dividing by the common
factor `2` from `mass_reflectEven` / `dirichlet_reflectEven` yields the cap statement with the
very same constant `C`. -/
theorem capPoincare_hemi_phg (m : ℕ) : ∃ CP : ℝ, CapPoincare (Cap.hemisphere m) CP := by
  classical
  have hrel : RellichSeq' (m + 1) 1 := rellichSeq' (m + 1) (R := 1) one_pos
  obtain ⟨C, hCpos, hC⟩ := poincare_wirtinger_ball hrel
  refine ⟨C, hCpos.le, fun u => ?_⟩
  set B : Set (EuclideanSpace ℝ (Fin (m + 1))) := ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
    with hB
  -- the mean of the reflected function on the ball
  have hVpos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set t : ℝ := (∫ x in B, (reflectEven u).toFun x) / (volume B).toReal with ht
  refine ⟨t, ?_⟩
  -- the pointwise identity: reflecting `u − t` is reflecting `u`, shifted by `t`
  have hwtfun : (reflectEven (u - constP (Cap.hemisphere m) t)).toFun
      = fun x => (reflectEven u).toFun x - t := by
    funext x
    simp only [reflectEven_toFun, reflectEvenFun]
    exact sub_constP_toFun (Cap.hemisphere m) u t (capPt m x)
  -- integrability of the reflected function on `B`
  have hVint : IntegrableOn (reflectEven u).toFun B volume :=
    (reflectEven u).memL2.integrable (by norm_num)
  -- the shifted reflection has mean zero on `B`
  have hzero : (∫ x in B, (reflectEven (u - constP (Cap.hemisphere m) t)).toFun x) = 0 := by
    rw [hwtfun, integral_sub hVint (integrable_const t), setIntegral_const, measureReal_def,
      smul_eq_mul, ht]
    field_simp
    ring
  -- apply the ball Poincaré inequality to it
  have h2 := hC 1 one_pos (reflectEven (u - constP (Cap.hemisphere m) t)) hzero
  rw [mass_reflectEven, dirichlet_reflectEven, dirichletP_sub_constP] at h2
  nlinarith [h2]

end
end Cap
end RobinCaps

