import Mathlib
import RobinCaps.Spectrum.FormEngine

/-!
# The abstract two-sided min–max comparison (U-MAIN-ABSTRACT)

This file isolates, in a purely algebraic/order-theoretic setting, the
`sec:proof` argument of the manuscript that compares the `j`-th min–max value
of the renormalized energy/mass pair `(E, N)` on the full space `H` with the
`j`-th min–max value of the bulk pair `(a, b)` on the `F`-variable `V`.

The decomposition `u ↦ (F, Z)` is encoded by

* a linear projection `π : H →ₗ[ℝ] V`, `F = π u`;
* a remainder functional `Z : H → ℝ` with `Z u ≥ 0`;
* an energy weight `h`.

The **structural hypotheses** are the two pointwise comparisons
(`eq:global-energy-lower`, `eq:global-mass-upper` in the manuscript)

* `a (π u) + h * Z u ≤ E u`;
* `N u ≤ b (π u) + Z u`,

bundled as `BulkComparison`, together with `0 ≤ Z`, positivity of the mass
`N` on nonzero vectors, and the ratio-boundedness hypotheses required by the
form engine (`BddAboveRatio`, `BddBelowRatio`).

## Lower bound (`minmax_lower_of_bulk_codim`)

A finite-codimension constraint on the bulk variable — a `(j-1)`-dimensional
space of linear conditions `ψ : V →ₗ[ℝ] (Fin (j-1) → ℝ)` such that
`a ≥ ρ b` on `ker ψ` — pulls back along `π` to a codimension-`(j-1)` constraint
on `H`.  Whenever `h ≥ ρ ≥ 0` and `Z ≥ 0`, the comparisons turn
`a (π u) ≥ ρ b (π u)` into `ρ * N u ≤ E u` on that kernel, so
`FormEngine.le_minmax_of_codim` gives `ρ ≤ minmax E N j`.

## Upper bound (`minmax_upper_of_bulk_trial`)

A `j`-dimensional trial space `W ≤ V` on which `a ≤ η b` and a lift
`L : V →ₗ[ℝ] H`, injective on `W`, with a *defect* functional `s : V → ℝ`
(controlling the energy/mass remainder) and constants `δ, γ ≥ 0`:

* `s ≤ γ b` on `W` (defect controlled by bulk mass);
* `b ≤ N (L ·)` on `W` (mass lower bound);
* `E (L ·) ≤ a + δ s` on `W` (energy upper bound),

yield `E (L v) ≤ (η + δ γ) * N (L v)` on `W`.  Since `L` is injective on `W`,
its image is a `j`-dimensional subspace of `H`, and
`FormEngine.minmax_le_of_trial` gives `minmax E N j ≤ η + δ γ`.

Everything below is proved without `sorry`, `axiom` or `admit`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped InnerProductSpace RealInnerProductSpace

namespace RobinCaps.Spectrum

variable {H V : Type*} [AddCommGroup H] [Module ℝ H] [AddCommGroup V] [Module ℝ V]

/-! ### Structural data of the bulk decomposition -/

/-- **Structural pointwise comparison of the bulk decomposition.**

`E` is the energy form and `N` the mass form on the full space `H`; `a` and `b`
are their bulk counterparts on `V`, `π : H →ₗ[ℝ] V` is the projection
`u ↦ F = π u`, `Z : H → ℝ` is the nonnegative high-energy remainder and `h` is
the energy weight attached to it.

The two fields are exactly the manuscript's inequalities

* `a (π u) + h * Z u ≤ E u` (`eq:global-energy-lower`);
* `N u ≤ b (π u) + Z u` (`eq:global-mass-upper`). -/
def BulkComparison (E N : H → ℝ) (a b : V → ℝ) (Z : H → ℝ)
    (π : H →ₗ[ℝ] V) (h : ℝ) : Prop :=
  (∀ u : H, a (π u) + h * Z u ≤ E u) ∧ (∀ u : H, N u ≤ b (π u) + Z u)

/-! ### Lower-bound step -/

/-- **Lower-bound step of the abstract min–max comparison.**

Let `ψ : V →ₗ[ℝ] (Fin (j-1) → ℝ)` be `(j-1)` linear conditions on the bulk
variable and suppose that on `ker ψ` the bulk energy dominates `ρ` times the
bulk mass, `ρ * b v ≤ a v`.  If `π` is surjective, `Z ≥ 0`, `0 ≤ ρ ≤ h`, and
the pair `(E, N)` satisfies the structural `BulkComparison`, then
`ρ ≤ minmax E N j`.

This is obtained by pulling `ψ` back to `φ = ψ.comp π` (a codimension-`(j-1)`
constraint on `H`) and applying `FormEngine.le_minmax_of_codim` to `(E, N)`;
the key pointwise inequality is
`ρ * N u ≤ ρ * (b (π u) + Z u) ≤ a (π u) + h * Z u ≤ E u` on `ker φ`. -/
theorem minmax_lower_of_bulk_codim
    (E N : H → ℝ) (a b : V → ℝ) (Z : H → ℝ) (π : H →ₗ[ℝ] V) (h : ℝ)
    (hcmp : BulkComparison E N a b Z π h)
    (hπ : Function.Surjective π)
    (hNpos : ∀ u : H, u ≠ 0 → 0 < N u)
    (hNA : BddAboveRatio E N)
    (hZ : ∀ u : H, 0 ≤ Z u)
    (j : ℕ) (hj : 1 ≤ j) (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (ψ : V →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hψ : Module.finrank ℝ (LinearMap.range ψ) = j - 1)
    (hbulk : ∀ v : V, ψ v = 0 → ρ * b v ≤ a v)
    (hex : ∃ W : Submodule ℝ H, Module.finrank ℝ W = j) :
    ρ ≤ minmax E N j := by
  have hφ : Module.finrank ℝ (LinearMap.range (ψ.comp π)) = j - 1 := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hπ, Submodule.map_top]
    exact hψ
  refine le_minmax_of_codim E N j hj hNpos hNA (ψ.comp π) hφ ρ ?_ hex
  intro u _hu hφu
  have hψu : ψ (π u) = 0 := by simpa only [LinearMap.comp_apply] using hφu
  have hkey : ρ * N u ≤ E u := by
    have h1 : ρ * N u ≤ ρ * (b (π u) + Z u) :=
      mul_le_mul_of_nonneg_left (hcmp.2 u) hρ₀
    have h2 : ρ * (b (π u) + Z u) ≤ a (π u) + h * Z u := by
      rw [mul_add]
      exact add_le_add (hbulk (π u) hψu)
        (mul_le_mul_of_nonneg_right hρh (hZ u))
    linarith [hcmp.1 u]
  exact hkey

/-! ### Upper-bound step -/

/-- **Upper-bound step of the abstract min–max comparison.**

Let `W ≤ V` be a `j`-dimensional (`j > 0`) trial space in the bulk variable,
let `L : V →ₗ[ℝ] H` be a lift that is injective on `W`, and let `s : V → ℝ` be
a defect functional.  Suppose that on `W`, for constants `η`, `δ`, `γ` with
`δ ≥ 0` and `η + δ γ ≥ 0`:

* `a ≤ η * b` (bulk energy bounded by the spectral value `η`);
* `s ≤ γ * b` (defect controlled by the bulk mass);
* `b ≤ N (L ·)` (mass lower bound for the lift);
* `E (L ·) ≤ a + δ * s` (energy upper bound for the lift).

Then `minmax E N j ≤ η + δ γ`.

Indeed, for `v ∈ W`, `v ≠ 0`, the four hypotheses combine into
`E (L v) ≤ (η + δ γ) * b v ≤ (η + δ γ) * N (L v)`.  Since `L` is injective on
`W`, `L '' W` is a `j`-dimensional subspace of `H`, and
`FormEngine.minmax_le_of_trial` applies. -/
theorem minmax_upper_of_bulk_trial
    (E N : H → ℝ) (a b s : V → ℝ) (L : V →ₗ[ℝ] H)
    (hNpos : ∀ u : H, u ≠ 0 → 0 < N u)
    (hNA : BddAboveRatio E N) (hNB : BddBelowRatio E N)
    (j : ℕ) (hj : 0 < j) (η δ γ : ℝ) (hδ : 0 ≤ δ)
    (W : Submodule ℝ V) (hW : Module.finrank ℝ W = j)
    (hLinj : ∀ v ∈ W, L v = 0 → v = 0)
    (ha : ∀ v ∈ W, a v ≤ η * b v)
    (hs : ∀ v ∈ W, s v ≤ γ * b v)
    (hbN : ∀ v ∈ W, b v ≤ N (L v))
    (hE : ∀ v ∈ W, E (L v) ≤ a v + δ * s v)
    (hη : 0 ≤ η + δ * γ) :
    minmax E N j ≤ η + δ * γ := by
  haveI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; exact hj)
  have hker : LinearMap.ker (L.comp W.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hLinj (x : V) x.2 (by simpa using hx))
  have hfin : Module.finrank ℝ (LinearMap.range (L.comp W.subtype)) = j := by
    have h := LinearMap.finrank_range_add_finrank_ker (L.comp W.subtype)
    rw [hker, hW] at h
    simpa using h
  have hmap : Submodule.map L W = LinearMap.range (L.comp W.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hmapfin : Module.finrank ℝ (Submodule.map L W) = j := by
    rw [hmap]; exact hfin
  refine minmax_le_of_trial E N j hj hNpos hNA hNB (Submodule.map L W) hmapfin
    (η + δ * γ) ?_
  intro u hu _hu_ne
  rw [Submodule.mem_map] at hu
  obtain ⟨v, hvW, rfl⟩ := hu
  have hstep : E (L v) ≤ η * b v + δ * (γ * b v) := by
    have h1 : E (L v) ≤ a v + δ * s v := hE v hvW
    have h2 : a v ≤ η * b v := ha v hvW
    have h3 : s v ≤ γ * b v := hs v hvW
    have h4 : δ * s v ≤ δ * (γ * b v) := mul_le_mul_of_nonneg_left h3 hδ
    linarith
  calc E (L v) ≤ η * b v + δ * (γ * b v) := hstep
    _ = (η + δ * γ) * b v := by ring
    _ ≤ (η + δ * γ) * N (L v) :=
        mul_le_mul_of_nonneg_left (hbN v hvW) hη

end RobinCaps.Spectrum
