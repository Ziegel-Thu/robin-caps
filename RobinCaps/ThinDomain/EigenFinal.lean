import RobinCaps.Compact.SmoothEstimatesSet
import RobinCaps.Compact.ApproxConvex
import RobinCaps.Compact.RellichConvex
import RobinCaps.ThinDomain.RellichThin
import RobinCaps.ThinDomain.H1PComplete
import RobinCaps.ThinDomain.H1PQInfDim
import RobinCaps.ThinDomain.EigenThin
import RobinCaps.Spectrum.ConstrainedMin
import RobinCaps.Spectrum.EigenFamily

/-!
# Wave 12: Rellich–Kondrachov on the thin domain and weak Robin eigenfunctions

Assembly of the wave-12 files (all hypotheses discharged).

* `RobinCaps.Compact.rellichL2_convex_final`, `rellich_convex_final`: Rellich–Kondrachov on every
  bounded convex open `Ω ∋ 0` in `ℝⁿ`, `n ≥ 1` (compact embedding `H¹(Ω) ↪ L²(Ω)`).
* `RobinCaps.ThinDomain.rellichP_thinDomain_final`: Rellich–Kondrachov for the product Sobolev
  model on the thin domain `Ω_R`.
* `RobinCaps.ThinDomain.exists_robin_eigenfunctions_final`: for every `j`, the first `j` min–max
  values `λ_1 ≤ … ≤ λ_j` of the Robin form on `Ω_R` (the manuscript's `eq:minmax`, Lean
  `lambdaThin`) are attained by `L²`-orthonormal weak eigenfunctions
  `ψ_0, …, ψ_{j-1} ∈ H¹(Ω_R)`:
  `∫ ∇ψ_a·∇v + α ∫_{∂Ω_R} Tr ψ_a Tr v = λ_{a+1} ∫ ψ_a v` for every `v ∈ H¹(Ω_R)`.
* Top-level names: `RobinCaps.rellich_thinDomain_top`, `RobinCaps.robin_eigenfunctions_top`,
  `RobinCaps.robin_eigenfunctions_two_top` (the case `j = 2` used by the counterexample).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open RobinCaps.Domain RobinCaps.Cap

namespace RobinCaps.Compact

/-- **Rellich–Kondrachov on a bounded convex open set** containing `0`, with an `L²` limit. -/
theorem rellichL2_convex_final {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) : RellichEmbeddingL2 Ω :=
  rellichL2_convex_rcx hconv hopen hbdd h0 fun _ _ hr₀ hball hρ₀ hΩρ =>
    approxEstimateCvx_acx hn hconv hopen hbdd hr₀ hball hρ₀ hΩρ
      (smoothConvSetEst_ses n) (smoothDilateSetEst_ses n)

/-- **Rellich–Kondrachov on a bounded convex open set** containing `0`, in the form of the
target `Weak.RellichEmbedding`. -/
theorem rellich_convex_final {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) : RobinCaps.Sobolev.Weak.RellichEmbedding Ω :=
  rellich_convex_rcx hconv hopen hbdd h0 fun _ _ hr₀ hball hρ₀ hΩρ =>
    approxEstimateCvx_acx hn hconv hopen hbdd hr₀ hball hρ₀ hΩρ
      (smoothConvSetEst_ses n) (smoothDilateSetEst_ses n)

end RobinCaps.Compact

namespace RobinCaps.ThinDomain

variable {m : ℕ} {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- **Rellich–Kondrachov on the thin domain** `Ω_R` (product Sobolev model `H1P`). -/
theorem rellichP_thinDomain_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    RellichEmbeddingP (thinDomain Cm Cp L R) :=
  rellichP_thin_rth hR hL
    (RobinCaps.Compact.rellichL2_convex_final (Nat.succ_pos m)
      (RobinCaps.Sobolev.convex_thinDomainE_cd hR hL)
      (RobinCaps.Sobolev.isOpen_thinDomainE_cd hR hL)
      (RobinCaps.Sobolev.isBounded_thinDomainE_cd hR hL)
      (RobinCaps.Sobolev.zero_mem_thinDomainE_cd hR hL))

/-- **The min–max values of the Robin form on `Ω_R` are attained by weak eigenfunctions.**
For every `j` there are `ψ_0, …, ψ_{j-1} ∈ H¹(Ω_R)`, orthonormal in `L²(Ω_R)`, with
`q(ψ_a, v) = λ_{a+1}(Ω_R; α) ⟨ψ_a, v⟩` for all `v ∈ H¹(Ω_R)`, where
`q(u, v) = ∫ ∇u·∇v + α bd(u, v)` is the Robin form of the trace data `td`. -/
theorem exists_robin_eigenfunctions_final (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (j : ℕ) :
    ∃ ψ : ℕ → H1P (thinDomain Cm Cp L R),
      (∀ a < j, ∀ b < j, massBilinP (ψ a) (ψ b) = if a = b then 1 else 0) ∧
      (∀ a < j, ∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP (ψ a) v + α * td.bd (ψ a) v
          = lambdaThin hR hL td α (a + 1) * massBilinP (ψ a) v) ∧
      (∀ a < j, ∀ b < j, a ≤ b → lambdaThin hR hL td α (a + 1) ≤ lambdaThin hR hL td α (b + 1)) :=
  exists_eigenfunctions_eth hR hL td hα (rellichP_thinDomain_final hR hL)
    (h1pComplete_h1c (isOpen_thinDomain hR hL).measurableSet) j
    (exists_finrank_H1PQ_inf (isOpen_thinDomain hR hL)
      ⟨0, RobinCaps.Sobolev.zero_mem_thinDomain_cd hR hL⟩ j)
    (RobinCaps.Spectrum.eigenFamily_efam _ (RobinCaps.Spectrum.constrainedMin_cmin _) j)

end RobinCaps.ThinDomain

namespace RobinCaps

open RobinCaps.ThinDomain

/-- **Rellich–Kondrachov on the thin domain** (headline re-export). -/
theorem rellich_thinDomain_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) : RellichEmbeddingP (thinDomain Cm Cp L R) :=
  rellichP_thinDomain_final hR hL

/-- **Min–max values are weak Robin eigenvalues** (headline re-export, every `j`). -/
theorem robin_eigenfunctions_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (j : ℕ) :
    ∃ ψ : ℕ → H1P (thinDomain Cm Cp L R),
      (∀ a < j, ∀ b < j, massBilinP (ψ a) (ψ b) = if a = b then 1 else 0) ∧
      (∀ a < j, ∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP (ψ a) v + α * td.bd (ψ a) v
          = lambdaThin hR hL td α (a + 1) * massBilinP (ψ a) v) ∧
      (∀ a < j, ∀ b < j, a ≤ b → lambdaThin hR hL td α (a + 1) ≤ lambdaThin hR hL td α (b + 1)) :=
  exists_robin_eigenfunctions_final hR hL td hα j

/-- **The case `j = 2`** (what the counterexample uses): `λ₁(Ω_R; α)` and `λ₂(Ω_R; α)` are
attained by `L²`-orthonormal weak Robin eigenfunctions `ψ₁, ψ₂ ∈ H¹(Ω_R)`. -/
theorem robin_eigenfunctions_two_top {m : ℕ} {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) :
    ∃ ψ₁ ψ₂ : H1P (thinDomain Cm Cp L R),
      massP ψ₁ = 1 ∧ massP ψ₂ = 1 ∧ massBilinP ψ₁ ψ₂ = 0 ∧
      (∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP ψ₁ v + α * td.bd ψ₁ v = lambdaThin hR hL td α 1 * massBilinP ψ₁ v) ∧
      (∀ v : H1P (thinDomain Cm Cp L R),
        dirichletBilinP ψ₂ v + α * td.bd ψ₂ v = lambdaThin hR hL td α 2 * massBilinP ψ₂ v) := by
  obtain ⟨ψ, horth, heq, -⟩ := exists_robin_eigenfunctions_final hR hL td hα 2
  refine ⟨ψ 0, ψ 1, ?_, ?_, ?_, heq 0 (by norm_num), heq 1 (by norm_num)⟩
  · rw [← massBilinP_self]; simpa using horth 0 (by norm_num) 0 (by norm_num)
  · rw [← massBilinP_self]; simpa using horth 1 (by norm_num) 1 (by norm_num)
  · simpa using horth 0 (by norm_num) 1 (by norm_num)

end RobinCaps

end
