import Mathlib
import RobinCaps.Spectrum.FormEngine

/-!
# Abstract compact form setting (wave 12 interface)

A pair of symmetric bilinear forms on a real vector space `W`:

* the **energy** `Q` (nonnegative on the diagonal), e.g. the Robin form
  `dirichlet + α · bd` on `H¹(Ω)/null`;
* the **mass** `N` (positive definite), e.g. the `L²` inner product;

together with the two analytic inputs of the direct method, phrased through the energy norm
`e u = Q u u + N u u`:

* `complete`: `e`-Cauchy sequences have an `e`-limit (completeness of `H¹`);
* `compact`: `e`-bounded sequences have an `N`-Cauchy subsequence (Rellich–Kondrachov).

The file only contains definitions and the `Prop`-valued statements of the two results of
wave 12 (`ConstrainedMinProp`, `EigenFamilyProp`); they are proved in
`Spectrum/ConstrainedMin.lean` and `Spectrum/EigenFamily.lean`.
-/

noncomputable section

open Filter Topology

namespace RobinCaps.Spectrum

/-- **Abstract compact form setting.** -/
structure CompactFormSetting (W : Type*) [AddCommGroup W] [Module ℝ W] where
  /-- the energy form -/
  Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ
  /-- the mass form -/
  N : W →ₗ[ℝ] W →ₗ[ℝ] ℝ
  Q_symm : ∀ u v, Q u v = Q v u
  N_symm : ∀ u v, N u v = N v u
  Q_nonneg : ∀ u, 0 ≤ Q u u
  N_pos : ∀ u, u ≠ 0 → 0 < N u u
  /-- completeness for the energy norm `Q u u + N u u` -/
  complete : ∀ w : ℕ → W,
    (∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k l, K ≤ k → K ≤ l →
      Q (w k - w l) (w k - w l) + N (w k - w l) (w k - w l) ≤ η) →
    ∃ ψ : W, Tendsto (fun k => Q (w k - ψ) (w k - ψ) + N (w k - ψ) (w k - ψ)) atTop (𝓝 0)
  /-- compactness: energy-bounded sequences have an `N`-Cauchy subsequence -/
  compact : ∀ w : ℕ → W, (∃ M : ℝ, ∀ k, Q (w k) (w k) + N (w k) (w k) ≤ M) →
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k l, K ≤ k → K ≤ l →
      N (w (ν k) - w (ν l)) (w (ν k) - w (ν l)) ≤ η

namespace CompactFormSetting

variable {W : Type*} [AddCommGroup W] [Module ℝ W] (S : CompactFormSetting W)

/-- the energy quadratic form `q u = Q u u` -/
def q (u : W) : ℝ := S.Q u u

/-- the mass quadratic form `n u = N u u` -/
def n (u : W) : ℝ := S.N u u

/-- the energy norm squared `e u = Q u u + N u u` -/
def e (u : W) : ℝ := S.Q u u + S.N u u

/-- A subspace is **energy-closed** if it contains the `e`-limits of its sequences. -/
def EClosed (V : Submodule ℝ W) : Prop :=
  ∀ (w : ℕ → W) (ψ : W), (∀ k, w k ∈ V) →
    Tendsto (fun k => S.e (w k - ψ)) atTop (𝓝 0) → ψ ∈ V

/-- The `N`-orthogonal complement of the first `k` vectors of a family `ψ`. -/
def orthFirst (ψ : ℕ → W) (k : ℕ) : Submodule ℝ W where
  carrier := {u | ∀ a < k, S.N u (ψ a) = 0}
  add_mem' := by
    intro u v hu hv a ha
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    rw [map_add, LinearMap.add_apply, hu a ha, hv a ha, add_zero]
  zero_mem' := by
    intro a _
    simp
  smul_mem' := by
    intro c u hu a ha
    simp only [Set.mem_setOf_eq] at hu ⊢
    rw [map_smul, LinearMap.smul_apply, hu a ha, smul_zero]

theorem mem_orthFirst {ψ : ℕ → W} {k : ℕ} {u : W} :
    u ∈ S.orthFirst ψ k ↔ ∀ a < k, S.N u (ψ a) = 0 := Iff.rfl

end CompactFormSetting

open CompactFormSetting

/-- **Target 1 (constrained direct method).**  On an energy-closed subspace `V` containing a
nonzero vector, the Rayleigh quotient `q / n` attains its infimum at some `ψ ∈ V` with
`n ψ = 1`, and `ψ` satisfies the weak eigenvalue equation *on `V`*. -/
def ConstrainedMinProp {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) : Prop :=
  ∀ V : Submodule ℝ W, S.EClosed V → (∃ u ∈ V, u ≠ 0) →
    ∃ ψ ∈ V, S.n ψ = 1 ∧ (∀ u ∈ V, S.q ψ * S.n u ≤ S.q u) ∧
      (∀ v ∈ V, S.Q ψ v = S.q ψ * S.N ψ v)

/-- **Target 2 (the min–max values are attained by eigenvectors).**  If `W` has a
`j`-dimensional subspace, there are `N`-orthonormal `ψ 0, …, ψ (j-1)` which satisfy the weak
eigenvalue equation `Q (ψ a) v = μ a · N (ψ a) v` for **all** `v ∈ W`, with eigenvalue
`μ a = minmax q n (a+1)` (the `(a+1)`-st min–max value); the `μ a` are nondecreasing. -/
def EigenFamilyProp {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (j : ℕ) : Prop :=
  (∃ V : Submodule ℝ W, Module.finrank ℝ V = j) →
    ∃ (ψ : ℕ → W) (μ : ℕ → ℝ),
      (∀ a < j, ∀ b < j, S.N (ψ a) (ψ b) = if a = b then 1 else 0) ∧
      (∀ a < j, ∀ v : W, S.Q (ψ a) v = μ a * S.N (ψ a) v) ∧
      (∀ a < j, ∀ b < j, a ≤ b → μ a ≤ μ b) ∧
      (∀ a < j, μ a = minmax S.q S.n (a + 1))

end RobinCaps.Spectrum

end
