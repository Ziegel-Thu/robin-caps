import RobinCaps.Sobolev.ConvexDensity
import RobinCaps.Compact.Rellich

/-!
# Rellich–Kondrachov on a bounded convex set: interface (wave 12)

Definitions and `Prop`-valued statements shared by the wave-12 files

* `Compact/SmoothEstimatesSet.lean` (proves `SmoothConvSetEst`, `SmoothDilateSetEst`),
* `Compact/ApproxConvex.lean` (proves `ApproxEstimateCvx Ω` from the two smooth estimates),
* `Compact/RellichConvex.lean` (proves `Weak.RellichEmbedding Ω` from `ApproxEstimateCvx Ω`).

`approxCvx u lam ε` is the smooth approximant of the ball proof (`Compact/Approx.lean: approx`)
for a general domain: the mollification at scale `ε` of the zero extension of the dilation
`x ↦ u (lam • x)`, which lives on the dilated domain `dilatedDomainCd Ω lam = (lam • ·)⁻¹' Ω`.
It is written out as a plain function so that no proof arguments appear; it is definitionally
`mollifier ε ⋆ extCd (dilateWideCd hΩ u hlam0)` (`approxCvx_eq_extCd`).
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- **The smooth approximant on a general domain** `Ω`:
`ρ_ε ⋆ 1_{Ω/lam} · u(lam ·)`. -/
def approxCvx {Ω : Set E} (u : H1 Ω) (lam ε : ℝ) : E → ℝ :=
  mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (RobinCaps.Sobolev.dilatedDomainCd Ω lam).indicator (fun x => u.toFun (lam • x))

theorem approxCvx_eq_extCd {Ω : Set E} (hΩ : MeasurableSet Ω) (u : H1 Ω) {lam : ℝ}
    (hlam0 : 0 < lam) (ε : ℝ) :
    approxCvx u lam ε = mollifier (n := n) ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      RobinCaps.Sobolev.extCd (RobinCaps.Sobolev.dilateWideCd hΩ u hlam0) := rfl

/-- **(S-smooth) on a bounded set.**  For a `C¹` function `v`, a mollifier `ρ` at scale `ε` and a
bounded measurable `Ω`, the mollification error on `Ω` is controlled by the gradient on the
closed `ε`-thickening of `Ω`. -/
def SmoothConvSetEst (n : ℕ) : Prop :=
  ∀ (ε : ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ), IsMollifier ε ρ → 0 ≤ ε →
    ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 v →
    ∀ Ω : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet Ω → Bornology.IsBounded Ω →
      ∫ x in Ω, ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x - v x) ^ 2
        ≤ ε ^ 2 * ∫ x in Metric.cthickening ε Ω, ‖fderiv ℝ v x‖ ^ 2

/-- **(D-smooth) on a bounded star-shaped set.**  For a `C¹` function `v` and a bounded
measurable `Ω` that is star-shaped about `0` and contained in `closedBall 0 ρ₀`,
`∫_Ω (v(lam x) − v x)² ≤ (1 − lam)² ρ₀² 2ⁿ ∫_Ω |∇v|²` for `1/2 ≤ lam ≤ 1`. -/
def SmoothDilateSetEst (n : ℕ) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 v →
    ∀ Ω : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet Ω → Bornology.IsBounded Ω →
    (∀ x ∈ Ω, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s • x ∈ Ω) →
    ∀ ρ₀ : ℝ, 0 ≤ ρ₀ → (∀ x ∈ Ω, ‖x‖ ≤ ρ₀) →
    ∀ lam : ℝ, 1 / 2 ≤ lam → lam ≤ 1 →
      ∫ x in Ω, (v (lam • x) - v x) ^ 2
        ≤ (1 - lam) ^ 2 * ρ₀ ^ 2 * 2 ^ n * ∫ x in Ω, ‖fderiv ℝ v x‖ ^ 2

/-- **(A1) on a convex domain.**  With `ball 0 r₀ ⊆ Ω ⊆ closedBall 0 ρ₀`, for
`1/2 ≤ lam < 1` and `0 < ε < (1 − lam) r₀` the approximant is `L²(Ω)`-close to `u`, uniformly
in `u` relative to the Dirichlet energy. -/
def ApproxEstimateCvx (Ω : Set (EuclideanSpace ℝ (Fin n))) (r₀ ρ₀ : ℝ) : Prop :=
  ∀ (u : H1 Ω) (lam ε : ℝ), 1 / 2 ≤ lam → lam < 1 → 0 < ε → ε < (1 - lam) * r₀ →
    ∫ x in Ω, (approxCvx u lam ε x - u.toFun x) ^ 2
      ≤ 2 ^ (n + 1) * (ε + (1 - lam) * ρ₀) ^ 2 * dirichlet u

/-- **Rellich–Kondrachov with an `L²` limit.**  The same as `Weak.RellichEmbedding D` but the
limit `v` is recorded to lie in `L²(D)`; without this clause the convergence statement could
hold vacuously (the Bochner integral of a non-integrable function is `0`). -/
def RellichEmbeddingL2 (D : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ u : ℕ → H1 D, (∃ C : ℝ, ∀ k, dirichlet (u k) + mass (u k) ≤ C) →
    ∃ (ν : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin n) → ℝ), StrictMono ν ∧
      MemLp v 2 (volume.restrict D) ∧
      Tendsto (fun k => ∫ x in D, ((u (ν k)).toFun x - v x) ^ 2) atTop (𝓝 0)

end RobinCaps.Compact

end
