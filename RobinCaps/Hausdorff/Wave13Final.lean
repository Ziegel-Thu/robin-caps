import RobinCaps.Hausdorff.SteinerCompact
import RobinCaps.Hausdorff.SteinerVolume
import RobinCaps.Hausdorff.SteinerDiam
import RobinCaps.Hausdorff.SteinerSymm
import RobinCaps.Hausdorff.Isodiametric
import RobinCaps.Hausdorff.HConstValue
import RobinCaps.Hausdorff.BoundaryFinal
import RobinCaps.Spectrum.SelfAdjointCriterion
import RobinCaps.ThinDomain.RobinLaxMilgram
import RobinCaps.ThinDomain.RobinLinearPMap

/-!
# Wave 13: the standard Hausdorff measure and the self-adjoint Robin Laplacian

* `RobinCaps.isodiametric_top`: `|A| ≤ ω_m (diam A / 2)^m` for compact `A ⊆ ℝ^m`
  (Steiner symmetrisation).
* `RobinCaps.hConst_eq_top`: `hConst m = 2^m / ω_m`, i.e. mathlib's `μH[m] = (2^m/ω_m) • volume`
  on `ℝ^m`; hence `stdHausdorff m := (ω_m / 2^m) • μH[m]` is the textbook-normalised `ℋ^m`,
  and it equals Lebesgue measure on `ℝ^m` (`RobinCaps.stdHausdorff_eq_volume_top`).
* `RobinCaps.boundaryIntegral_eq_stdHausdorff_top`: for continuous `g ≥ 0`,
  `∫_{∂Ω_R'} g dℋ^m = boundaryIntegral g` — the formalization's boundary integral is the
  surface integral against the standard Hausdorff measure `ℋ^m`, with no normalising constant.
* `RobinCaps.robin_selfAdjoint_top`: the Robin Laplacian `robinOp_rlp` (a `LinearPMap` on
  `L²(Ω_R)`: `−Δu = f` in `Ω_R`, `∂ₙu + αu = 0` on `∂Ω_R`, weakly) is self-adjoint
  (`IsSelfAdjoint`, i.e. equal to its mathlib `LinearPMap.adjoint`), for `α ≥ 0`.
* `RobinCaps.robin_selfAdjoint_spectrum_top`: its eigenvalues are exactly the min–max values
  `λ_j(Ω_R; α)`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-- The textbook-normalised `m`-dimensional Hausdorff measure `ℋ^m = (ω_m / 2^m) μH[m]`, on any
Euclidean space. -/
def stdHausdorff (m : ℕ) (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin m))) (ball 0 1) / 2 ^ m) •
    (Measure.hausdorffMeasure (m : ℝ))

theorem isodiametric_w13 (m : ℕ) : IsodiametricProp m :=
  isodiametric_iso m (steinerCompact_stc m) (steinerVolume_stv m) (steinerDiam_std m)
    (steinerSymm_sts m)

theorem hConst_eq_w13 (m : ℕ) : HConstValueProp m :=
  hConstValue_hcv m (isodiametric_w13 m)

theorem omega_pos_w13 (m : ℕ) :
    0 < (volume : Measure (EuclideanSpace ℝ (Fin m))) (ball 0 1) :=
  measure_ball_pos _ _ one_pos

theorem omega_lt_top_w13 (m : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin m))) (ball 0 1) < ∞ :=
  measure_ball_lt_top

/-- `(ω_m / 2^m) · hConst m = 1`. -/
theorem stdFactor_mul_hConst_w13 (m : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin m))) (ball 0 1) / 2 ^ m * hConst m = 1 := by
  rw [hConst_eq_w13 m]
  have h1 := (omega_pos_w13 m).ne'
  have h2 := (omega_lt_top_w13 m).ne
  have h3 : (2 : ℝ≥0∞) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  have h4 : (2 : ℝ≥0∞) ^ m ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc ((2 : ℝ≥0∞) ^ m)⁻¹,
    ENNReal.inv_mul_cancel h3 h4, one_mul, ENNReal.mul_inv_cancel h1 h2]

/-- On `ℝ^m` the standard Hausdorff measure is Lebesgue measure. -/
theorem stdHausdorff_eq_volume_w13 (m : ℕ) :
    stdHausdorff m m = (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
  rw [stdHausdorff, (hausdorffVolume_hlin m).1, smul_smul, stdFactor_mul_hConst_w13, one_smul]

/-- **`boundaryIntegral` is the surface integral against the standard `ℋ^m`.** -/
theorem boundaryIntegral_eq_stdHausdorff_w13 {m : ℕ} (hm : 1 ≤ m)
    {Cm Cp : RobinCaps.Cap m} {L R : ℝ} (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (g : CapSpace m → ℝ) (hg : Continuous g) (hg0 : ∀ p, 0 ≤ g p) :
    ∫⁻ y in frontier (RobinCaps.Sobolev.thinDomainE_cd Cm Cp L R),
        ENNReal.ofReal (g (RobinCaps.Domain.ofEuclid m y)) ∂(stdHausdorff m (m + 1))
      = ENNReal.ofReal (RobinCaps.ThinDomain.boundaryIntegral Cm Cp L R g) := by
  rw [stdHausdorff, Measure.restrict_smul, lintegral_smul_measure,
    boundaryHausdorff_bfin hm hR hL g hg hg0, smul_eq_mul, ← mul_assoc, stdFactor_mul_hConst_w13,
    one_mul]

end RobinCaps.Hausdorff

namespace RobinCaps

open RobinCaps.Hausdorff RobinCaps.ThinDomain

theorem isodiametric_top (m : ℕ) : IsodiametricProp m := isodiametric_w13 m

theorem hConst_eq_top (m : ℕ) : HConstValueProp m := hConst_eq_w13 m

theorem stdHausdorff_eq_volume_top (m : ℕ) :
    stdHausdorff m m = (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
  stdHausdorff_eq_volume_w13 m

/-- **The boundary integral of the formalization is the surface integral against the standard
`m`-dimensional Hausdorff measure** `ℋ^m` on `∂Ω_R`. -/
theorem boundaryIntegral_eq_stdHausdorff_top {m : ℕ} (hm : 1 ≤ m) {Cm Cp : Cap m} {L R : ℝ}
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (g : CapSpace m → ℝ) (hg : Continuous g)
    (hg0 : ∀ p, 0 ≤ g p) :
    ∫⁻ y in frontier (RobinCaps.Sobolev.thinDomainE_cd Cm Cp L R),
        ENNReal.ofReal (g (RobinCaps.Domain.ofEuclid m y)) ∂(stdHausdorff m (m + 1))
      = ENNReal.ofReal (boundaryIntegral Cm Cp L R g) :=
  boundaryIntegral_eq_stdHausdorff_w13 hm hR hL g hg hg0

/-- **The Robin Laplacian on `Ω_R` is self-adjoint** (unbounded-operator sense, mathlib's
`LinearPMap.adjoint`), for every trace datum and `α ≥ 0`. -/
theorem robin_selfAdjoint_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) :
    IsSelfAdjoint (robinOp_rlp hR hL td α) :=
  robinOp_isSelfAdjoint_rlp hR hL td hα (robinLaxMilgram_lmg hR hL td hα)
    RobinCaps.Spectrum.selfAdjointCriterion_sac

/-- **The eigenvalues of the self-adjoint Robin Laplacian are exactly the min–max values.** -/
theorem robin_selfAdjoint_spectrum_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (μ : ℝ) :
    (∃ x : robinDomain_rlp hR hL td α, (x : robinH_rlp Cm Cp L R) ≠ 0 ∧
        robinOp_rlp hR hL td α x = μ • (x : robinH_rlp Cm Cp L R)) ↔
      ∃ a : ℕ, μ = lambdaThin hR hL td α (a + 1) :=
  robinOp_eigen_iff_rlp hR hL td hα μ

end RobinCaps

end
