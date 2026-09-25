import RobinCaps.ThinDomain.H1PQuotient

/-!
# Interface for the wave-12 eigenfunction theorem on the thin domain

`Prop`-valued statements shared by

* `ThinDomain/RellichThin.lean` (proves `RellichEmbeddingP (thinDomain Cm Cp L R)`),
* `ThinDomain/H1PComplete.lean` (proves `H1PCompleteProp Ω`),
* `ThinDomain/EigenThin.lean` (uses both to build the compact form setting on `H1PQ`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RobinCaps.ThinDomain

variable {m : ℕ}

/-- **Rellich–Kondrachov for the product `H¹` model** on `Ω ⊆ CapSpace m`: every sequence
bounded in `H¹` has a subsequence converging in `L²(Ω)` to some `v ∈ L²(Ω)`.  (The clause
`MemLp v 2` matters: without it the integral could vanish for the trivial reason that the
integrand is not integrable.) -/
def RellichEmbeddingP (Ω : Set (CapSpace m)) : Prop :=
  ∀ u : ℕ → H1P Ω, (∃ C : ℝ, ∀ k, dirichletP (u k) + massP (u k) ≤ C) →
    ∃ (ν : ℕ → ℕ) (v : CapSpace m → ℝ), StrictMono ν ∧ MemLp v 2 (volume.restrict Ω) ∧
      Tendsto (fun k => ∫ p in Ω, ((u (ν k)).toFun p - v p) ^ 2) atTop (𝓝 0)

/-- **Completeness of the product `H¹` model** `H1P Ω`. -/
def H1PCompleteProp (Ω : Set (CapSpace m)) : Prop :=
  ∀ u : ℕ → H1P Ω,
    (∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k l, K ≤ k → K ≤ l →
      massP (u k - u l) + dirichletP (u k - u l) ≤ η) →
    ∃ v : H1P Ω, Tendsto (fun k => massP (u k - v) + dirichletP (u k - v)) atTop (𝓝 0)

end RobinCaps.ThinDomain

end
