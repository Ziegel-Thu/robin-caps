import RobinCaps.ThinDomain.Eigen
import RobinCaps.ThinDomain.BulkMass
import RobinCaps.Spectrum.MainAbstract
import RobinCaps.Sobolev.PiconeGeneral
import RobinCaps.Interval.Uniform

set_option linter.style.longLine false

/-!
# The final assembly step of the thin-domain main theorem (manuscript `sec:proof`)

This file performs the *reduction* of the manuscript's `thm:main` (available as the `Prop`
`RobinCaps.ThinDomain.MainTheorem`, `RobinCaps/ThinDomain/Eigen.lean`) to a **single**
`Prop`-level statement, `GlobalComparison`, which packages exactly the analytic content of
`sec:proof` lines 687–865 and nothing else.

## What `sec:proof` says (transcription)

With `E_R[u] = q_{Ω_R}[u] - ν_R N_{Ω_R}[u]`, `N_R[u] = N_{Ω_R}[u]`, and with the bulk
decomposition `u ↦ (F, Z_R[u])` (`eq:Z-definition`: `Z_R[u] = ‖w‖²_{L²(B_R)} + C₀ R Σ_σ
‖∇g_σ‖²_{L²(C_σ)} ≥ 0`), the manuscript records, for all sufficiently small `R`:

* `eq:global-energy-lower`:  `E_R[u] ≥ a_R[F] + h_R Z_R[u]`,  `h_R = c₀ R^{-2}`;
* `eq:global-mass-upper`:   `N_R[u] ≤ (1+CR) M[F] + CR D[F] + Z_R[u]`;
* `eq:a-R`:  `a_R[F] = D[F] + (β₋ - CR)|F(x₋)|² + (β₊ - CR)|F(x₊)|²`;
* `eq:D-less-a`:  `D[F] ≤ a_R[F]`, hence `N_R[u] ≤ b̂_R[F] + Z_R[u]` with
  `b̂_R[F] = (1+CR) M[F] + CR a_R[F]` (valid once `CR ≤ β₀/2`, so `β_± - CR > 0`);
* `eq:trial-extension` and its consequences `eq:trial-energy`, `eq:trial-mass`:
  `E_R[T_R F] = a_{β₋,β₊;I_R}[F] + ε_R[F]` with `|ε_R[F]| ≤ CR S[F]`, and
  `M[F] ≤ N_R[T_R F]`, where `S[F] = |F(x₋)|² + |F(x₊)|²`.

  Since `a_{β₋+CR, β₊+CR; I_R}[F] = a_{β₋,β₊;I_R}[F] + CR·S[F]` **identically**, the two
  displayed trial estimates are transcribed below in the equivalent, endpoint-shifted form
  `E_R[T_R F] ≤ a_{β₋+CR, β₊+CR; I_R}[F]` and `M[F] ≤ N_R[T_R F]`.  This is why no
  separate interval trace inequality `eq:interval-trace` enters the formal statement.

In the formalisation:

* the bulk variable `F` lives in `Sobolev.H1Q ℓ_R`, the interval quotient space for
  `ℓ_R = bulkLength Cm Cp L R = L - (K₋+K₊)R` (the length of `I_R`);
* `M[F] = Sobolev.massQ ℓ_R F`, `D[F] = Sobolev.robinFormQ 0 0 ℓ_R F` (the Robin form with
  both endpoint parameters `0` *is* the Dirichlet energy, by definition of `robinForm`),
  and `a_R[F] = Sobolev.robinFormQ (β₋-CR) (β₊-CR) ℓ_R F` is literally `eq:a-R`;
* `u` lives in `H1PQ (thinDomain Cm Cp L R)`, `q_{Ω_R} = robinFormPQ …`,
  `N_{Ω_R} = massPQ`;
* the projection `π_R : u ↦ F` (`eq:bulk-projection`, the axial coefficient
  `∫ u ψ_R` translated to `(0,ℓ_R)`, cf. `RobinCaps.ThinDomain.axialCoeff`) is taken as a
  **parameter**, together with its surjectivity, since the a.c. representative it needs is
  not available in this project.

## Contents

* `RobinCaps.Spectrum.minmax_lower_of_bulk_codim'` and
  `RobinCaps.Spectrum.minmax_upper_of_bulk_trial'` — the two abstract comparison steps of
  `RobinCaps/Spectrum/MainAbstract.lean` re-proved in the form actually usable for Robin
  forms: the global `BddAboveRatio` hypothesis (**false** for Robin forms, whose spectrum
  is unbounded above) is replaced by the per-subspace bound of
  `RobinCaps.Spectrum.le_minmax_of_codim'` / dropped via
  `RobinCaps.Spectrum.minmax_le_of_trial'`; in addition an explicit spectral **shift** `t`
  is built into the statements, so that they apply to the renormalized pair
  `(q_{Ω_R} - ν_R N_{Ω_R}, N_{Ω_R})` while concluding about `minmax q_{Ω_R} N_{Ω_R} =
  λ_j(Ω_R;α)`.
* `GlobalComparisonData` — the bundled data of `sec:proof` for one radius `R`;
  `GlobalComparison` — the target `Prop`, with the constants `C`, `c₀` and the radius
  threshold `R₁` quantified **outside** the `∀ R`, so that their uniformity in `R` is
  visible in the statement.
* `lower_of_globalComparison`, `upper_of_globalComparison` — the two one-sided reductions.
* `mainTheorem_of_globalComparison` — **the reduction** `GlobalComparison ⇒ MainTheorem`.

No `sorry`, `admit`, `axiom` or `native_decide`.  All unproven analytic content sits in the
fields of `GlobalComparisonData`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter
open scoped Topology Interval

/-! ## Part 0: two small auxiliary facts -/

namespace RobinCaps.Interval

/-- `μ_j = k_j² ≥ 0`. -/
theorem mu_nonneg (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    0 ≤ mu p q ℓ j hp hq hℓ hj := by
  simp only [mu]
  positivity

end RobinCaps.Interval

namespace RobinCaps.Sobolev

/-- Monotonicity of the interval Robin form in the two endpoint parameters. -/
theorem robinFormQ_mono {p q p' q' ℓ : ℝ} (hp : p ≤ p') (hq : q ≤ q') (w : H1Q ℓ) :
    robinFormQ p q ℓ w ≤ robinFormQ p' q' ℓ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullOff ℓ) w
  rw [robinFormQ_mk, robinFormQ_mk]
  simp only [robinForm]
  have h1 : p * u.toFun 0 ^ 2 ≤ p' * u.toFun 0 ^ 2 :=
    mul_le_mul_of_nonneg_right hp (sq_nonneg _)
  have h2 : q * u.toFun ℓ ^ 2 ≤ q' * u.toFun ℓ ^ 2 :=
    mul_le_mul_of_nonneg_right hq (sq_nonneg _)
  linarith

end RobinCaps.Sobolev

/-! ## Part A: the abstract two-step comparison, primed (per-subspace) and shifted -/

namespace RobinCaps.Spectrum

variable {H V : Type*} [AddCommGroup H] [Module ℝ H] [AddCommGroup V] [Module ℝ V]

/-- **The image of a `j`-dimensional subspace under a map injective on it is
`j`-dimensional.**  (Extracted from the proof of
`RobinCaps.Spectrum.minmax_upper_of_bulk_trial`.) -/
theorem finrank_map_of_injOn (Lft : V →ₗ[ℝ] H) (W : Submodule ℝ V) (j : ℕ) (hj : 0 < j)
    (hW : Module.finrank ℝ W = j) (hLinj : ∀ v ∈ W, Lft v = 0 → v = 0) :
    Module.finrank ℝ (Submodule.map Lft W) = j := by
  haveI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_finrank_pos (by rw [hW]; exact hj)
  have hker : LinearMap.ker (Lft.comp W.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hLinj (x : V) x.2 (by simpa using hx))
  have hfin : Module.finrank ℝ (LinearMap.range (Lft.comp W.subtype)) = j := by
    have h := LinearMap.finrank_range_add_finrank_ker (Lft.comp W.subtype)
    rw [hker, hW] at h
    simpa using h
  rw [LinearMap.range_comp, Submodule.range_subtype] at hfin
  exact hfin

/-- **Lower-bound step of the min–max comparison, primed and shifted.**

Same as `RobinCaps.Spectrum.minmax_lower_of_bulk_codim`, with two changes forced by the
Robin setting:

* the global hypothesis `BddAboveRatio q N` (false for Robin forms) is replaced by the
  per-subspace boundedness `hA` of `RobinCaps.Spectrum.le_minmax_of_codim'`;
* the structural `BulkComparison` is imposed on the **shifted** energy `q - t·N`
  (in the application `q = q_{Ω_R}`, `N = N_{Ω_R}`, `t = ν_R`, so `q - t·N = E_R`), and the
  conclusion is about `minmax q N j` itself, i.e. `ρ + t ≤ λ_j`.

The pointwise inequality on `ker (ψ ∘ π)` is
`ρ·N u ≤ ρ·(b (π u) + Z u) ≤ a (π u) + h·Z u ≤ q u - t·N u`. -/
theorem minmax_lower_of_bulk_codim'
    (q N : H → ℝ) (t : ℝ) (a b : V → ℝ) (Z : H → ℝ) (π : H →ₗ[ℝ] V) (h : ℝ)
    (j : ℕ) (hj : 1 ≤ j)
    (hcmp : BulkComparison (fun u => q u - t * N u) N a b Z π h)
    (hπ : Function.Surjective π)
    (hNpos : ∀ u : H, u ≠ 0 → 0 < N u)
    (hA : ∀ W : Submodule ℝ H, Module.finrank ℝ W = j →
      BddAbove (Set.range fun u : {u : W // u ≠ 0} => q ((u : W) : H) / N ((u : W) : H)))
    (hZ : ∀ u : H, 0 ≤ Z u)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρh : ρ ≤ h)
    (ψ : V →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hψ : Module.finrank ℝ (LinearMap.range ψ) = j - 1)
    (hbulk : ∀ v : V, ψ v = 0 → ρ * b v ≤ a v)
    (hex : ∃ W : Submodule ℝ H, Module.finrank ℝ W = j) :
    ρ + t ≤ minmax q N j := by
  have hφ : Module.finrank ℝ (LinearMap.range (ψ.comp π)) = j - 1 := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hπ, Submodule.map_top]
    exact hψ
  refine le_minmax_of_codim' q N j hj hNpos hA (ψ.comp π) hφ (ρ + t) ?_ hex
  intro u _hu hφu
  have hψu : ψ (π u) = 0 := by simpa only [LinearMap.comp_apply] using hφu
  have h1 : ρ * N u ≤ ρ * (b (π u) + Z u) :=
    mul_le_mul_of_nonneg_left (hcmp.2 u) hρ₀
  have h2 : ρ * (b (π u) + Z u) ≤ a (π u) + h * Z u := by
    rw [mul_add]
    exact add_le_add (hbulk (π u) hψu) (mul_le_mul_of_nonneg_right hρh (hZ u))
  have h3 : a (π u) + h * Z u ≤ q u - t * N u := hcmp.1 u
  have h4 : (ρ + t) * N u = ρ * N u + t * N u := by ring
  linarith

/-- **Upper-bound step of the min–max comparison, primed and shifted.**

Same as `RobinCaps.Spectrum.minmax_upper_of_bulk_trial`, with the global `BddAboveRatio`
dropped (via `RobinCaps.Spectrum.minmax_le_of_trial'`, which only needs `BddBelowRatio`)
and with the spectral shift `t` built in: the trial estimate is imposed on the shifted
energy `q - t·N` and the conclusion is `minmax q N j ≤ η + δγ + t`. -/
theorem minmax_upper_of_bulk_trial'
    (q N : H → ℝ) (t : ℝ) (a b s : V → ℝ) (Lft : V →ₗ[ℝ] H)
    (hNpos : ∀ u : H, u ≠ 0 → 0 < N u) (hB : BddBelowRatio q N)
    (j : ℕ) (hj : 0 < j) (η δ γ : ℝ) (hδ : 0 ≤ δ)
    (W : Submodule ℝ V) (hW : Module.finrank ℝ W = j)
    (hLinj : ∀ v ∈ W, Lft v = 0 → v = 0)
    (ha : ∀ v ∈ W, v ≠ 0 → a v ≤ η * b v)
    (hs : ∀ v ∈ W, v ≠ 0 → s v ≤ γ * b v)
    (hbN : ∀ v ∈ W, v ≠ 0 → b v ≤ N (Lft v))
    (hE : ∀ v ∈ W, v ≠ 0 → q (Lft v) - t * N (Lft v) ≤ a v + δ * s v)
    (hη : 0 ≤ η + δ * γ) :
    minmax q N j ≤ η + δ * γ + t := by
  have hmapfin : Module.finrank ℝ (Submodule.map Lft W) = j :=
    finrank_map_of_injOn Lft W j hj hW hLinj
  refine minmax_le_of_trial' q N j hj hNpos hB (Submodule.map Lft W) hmapfin
    (η + δ * γ + t) ?_
  intro u hu hune
  rw [Submodule.mem_map] at hu
  obtain ⟨v, hvW, rfl⟩ := hu
  have hvne : v ≠ 0 := by
    intro h0
    exact hune (by rw [h0, map_zero])
  have h1 := hE v hvW hvne
  have h2 := ha v hvW hvne
  have h3 := hs v hvW hvne
  have h4 := hbN v hvW hvne
  have h5 : δ * s v ≤ δ * (γ * b v) := mul_le_mul_of_nonneg_left h3 hδ
  have h6 : (η + δ * γ) * b v ≤ (η + δ * γ) * N (Lft v) :=
    mul_le_mul_of_nonneg_left h4 hη
  have h7 : (η + δ * γ) * b v = η * b v + δ * (γ * b v) := by ring
  have h8 : (η + δ * γ + t) * N (Lft v) = (η + δ * γ) * N (Lft v) + t * N (Lft v) := by ring
  linarith

end RobinCaps.Spectrum

/-! ## Part B: the interval constraint functionals on the quotient space -/

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap RobinCaps.Sobolev

/-- The `(j-1)` interior nodes of the `j`-th interval eigenfunction lie in `[[0,ℓ]]`. -/
theorem nodes_mem_uIcc (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) (i : Fin (j - 1)) :
    PiconeGeneral.nodes p q ℓ hp hq hℓ j hj i ∈ uIcc (0 : ℝ) ℓ := by
  rw [uIcc_of_le hℓ.le]
  exact Ioo_subset_Icc_self (PiconeGeneral.nodes_mem p q ℓ hp hq hℓ j hj i)

/-- **The `(j-1)` interval constraints of `eq:orth-conditions`, on the quotient space.**
Evaluation at the `j-1` interior nodes of the `j`-th eigenfunction descends from `H1 ℓ` to
`H1Q ℓ` because the nodes lie in `[0,ℓ]`. -/
def nodesEvalQ (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j) :
    H1Q ℓ →ₗ[ℝ] (Fin (j - 1) → ℝ) :=
  (nullOff ℓ).liftQ (PiconeGeneral.nodesEval p q ℓ hp hq hℓ j hj)
    (by
      intro v hv
      refine LinearMap.mem_ker.mpr ?_
      funext i
      exact evalAt_eq_zero_of_mem_nullOff (nodes_mem_uIcc p q ℓ hp hq hℓ j hj i) hv)

/-- The constraint functional has `(j-1)`-dimensional range (Lagrange interpolation). -/
theorem finrank_range_nodesEvalQ (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) :
    Module.finrank ℝ (LinearMap.range (nodesEvalQ p q ℓ hp hq hℓ j hj)) = j - 1 := by
  have hrange : LinearMap.range (nodesEvalQ p q ℓ hp hq hℓ j hj)
      = LinearMap.range (PiconeGeneral.nodesEval p q ℓ hp hq hℓ j hj) :=
    Submodule.range_liftQ _ _ _
  rw [hrange]
  exact PiconeGeneral.finrank_range_nodesEval p q ℓ hp hq hℓ j hj

/-- **Picone's inequality for `μ_j`, on the quotient space** (`RobinCaps.Sobolev.PiconeGeneral.picone_general`):
`μ_j(p,q;ℓ) · M[F] ≤ a_{p,q;ℓ}[F]` for `F` satisfying the `(j-1)` node constraints. -/
theorem picone_generalQ (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) (w : H1Q ℓ) (hw : nodesEvalQ p q ℓ hp hq hℓ j hj w = 0) :
    Interval.mu p q ℓ j hp hq hℓ hj * massQ ℓ w ≤ robinFormQ p q ℓ w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullOff ℓ) w
  rw [massQ_mk, robinFormQ_mk]
  refine PiconeGeneral.picone_general p q ℓ hp hq hℓ j hj u (fun i => ?_)
  have hi := congrFun hw i
  simpa using hi

/-! ## Part C: the target `Prop` `GlobalComparison` -/

variable {m : ℕ}

/-- **The bulk/cap decomposition data of `sec:proof` at one radius `R`.**

All fields are *exactly* the manuscript's inequalities, in the objects of this project
(`ℓ_R = bulkLength Cm Cp L R` is the length of the bulk interval `I_R`, `F = π u`,
`M[F] = massQ ℓ_R F`, `D[F] = robinFormQ 0 0 ℓ_R F`,
`a_R[F] = robinFormQ (β₋-CR) (β₊-CR) ℓ_R F` is `eq:a-R`):

* `lower` is `eq:global-energy-lower`, `E_R[u] ≥ a_R[F] + h_R Z_R[u]` with `h_R = c₀R^{-2}`;
* `upper` is `eq:global-mass-upper`, `N_R[u] ≤ (1+CR)M[F] + CR D[F] + Z_R[u]`;
* `trial_mass` is the left half of `eq:trial-mass`, `M[F] ≤ N_R[T_R F]`;
* `trial_energy` is `eq:trial-energy` combined with the identity
  `a_{β₋,β₊;I_R}[F] + CR·S[F] = a_{β₋+CR,β₊+CR;I_R}[F]`:
  `E_R[T_R F] ≤ a_{β₋+CR,β₊+CR;I_R}[F]`.

The projection `π` (the bulk axial coefficient `eq:bulk-projection`), its surjectivity, the
remainder `Z` (`eq:Z-definition`) and the trial extension `lift` (`eq:trial-extension`) are
data.  Injectivity of `lift` on the trial space is *not* a field: it follows from
`trial_mass`, exactly as the manuscript argues ("`T_R` is injective on `W_{j,R}` because the
bulk `L²` mass of its image is exactly `M[F]`"). -/
structure GlobalComparisonData (Cm Cp : Cap m) (L α : ℝ) {R : ℝ} (hR : 0 < R)
    (hLR : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R) (nu C c₀ : ℝ) where
  /-- The bulk projection `u ↦ F` of `eq:bulk-projection`. -/
  π : H1PQ (thinDomain Cm Cp L R) →ₗ[ℝ] H1Q (bulkLength Cm Cp L R)
  /-- The bulk projection is onto. -/
  π_surj : Function.Surjective π
  /-- The nonnegative high-energy remainder `Z_R` of `eq:Z-definition`. -/
  Z : H1PQ (thinDomain Cm Cp L R) → ℝ
  /-- `Z_R ≥ 0` (`eq:Z-definition`). -/
  Z_nonneg : ∀ u, 0 ≤ Z u
  /-- `eq:global-energy-lower`:  `E_R[u] ≥ a_R[F] + h_R Z_R[u]`, `h_R = c₀ R^{-2}`. -/
  lower : ∀ u,
    robinFormQ (Cm.beta α - C * R) (Cp.beta α - C * R) (bulkLength Cm Cp L R) (π u)
        + c₀ / R ^ 2 * Z u
      ≤ robinFormPQ (isOpen_thinDomain hR hLR) td.bd td.vanishesOnNullAEP α u - nu * massPQ u
  /-- `eq:global-mass-upper`:  `N_R[u] ≤ (1+CR)M[F] + CR D[F] + Z_R[u]`. -/
  upper : ∀ u,
    massPQ u ≤ (1 + C * R) * massQ (bulkLength Cm Cp L R) (π u)
        + C * R * robinFormQ 0 0 (bulkLength Cm Cp L R) (π u) + Z u
  /-- The trial extension `T_R` of `eq:trial-extension`. -/
  lift : H1Q (bulkLength Cm Cp L R) →ₗ[ℝ] H1PQ (thinDomain Cm Cp L R)
  /-- `eq:trial-mass` (left half):  `M[F] ≤ N_R[T_R F]`. -/
  trial_mass : ∀ v, massQ (bulkLength Cm Cp L R) v ≤ massPQ (lift v)
  /-- `eq:trial-energy`:  `E_R[T_R F] ≤ a_{β₋,β₊;I_R}[F] + CR·S[F] = a_{β₋+CR,β₊+CR;I_R}[F]`. -/
  trial_energy : ∀ v,
    robinFormPQ (isOpen_thinDomain hR hLR) td.bd td.vanishesOnNullAEP α (lift v)
        - nu * massPQ (lift v)
      ≤ robinFormQ (Cm.beta α + C * R) (Cp.beta α + C * R) (bulkLength Cm Cp L R) v

/-- **The target `Prop`: the global comparison of `sec:proof`.**

There are constants `C ≥ 0`, `c₀ > 0` and a threshold `0 < R₁ ≤ R₀` — quantified *outside*
the `∀ R`, so that their **uniformity in `R`** is part of the statement — such that for
every admissible `0 < R < R₁` the decomposition data `GlobalComparisonData` exists.

This single `Prop` carries all the remaining analytic work of the manuscript
(`eq:exact-separation`, `eq:cap-lower`, `eq:cap-mass-bound`, `eq:interval-trace`,
`lem:cap-upper` and the construction of the bulk projection and of the trial extension). -/
def GlobalComparison (Cm Cp : Cap m) (L α : ℝ) (nu : ℝ → ℝ) (R₀ : ℝ)
    (tf : TraceFamily Cm Cp L R₀) : Prop :=
  ∃ C c₀ R₁ : ℝ, 0 ≤ C ∧ 0 < c₀ ∧ 0 < R₁ ∧ R₁ ≤ R₀ ∧
    ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀), R < R₁ →
      ∀ hLR : (Cm.K + Cp.K) * R < L,
        Nonempty (GlobalComparisonData Cm Cp L α hR hLR (tf R hR hR₀) (nu R) C c₀)

/-! ## Part D: the two one-sided reductions -/

variable {Cm Cp : Cap m} {L α R : ℝ}

/-- `ℓ_R = L - (K₋+K₊)R > 0` on the admissible range. -/
theorem bulkLength_pos (hLR : (Cm.K + Cp.K) * R < L) : 0 < bulkLength Cm Cp L R := by
  simp only [bulkLength]
  linarith

/-- **The lower bound of `sec:proof`** (`eq:main-lower`, before the interval perturbation
step): with `ℓ_j(R) = μ_j(β₋-CR, β₊-CR; ℓ_R)` and
`ρ_j(R) = ℓ_j(R) / (1 + CR + CR ℓ_j(R))` (`eq:rho-definition`),

`ρ_j(R) + ν_R ≤ λ_j(Ω_R;α)`,

i.e. `λ_j(Ω_R;α) - ν_R ≥ ρ_j(R)`.

The proof is the manuscript's finite-codimension argument: the `(j-1)` interval
constraints `eq:orth-conditions` are pulled back along `π`; on their kernel the interval
Picone inequality gives `a_R[F] ≥ ℓ_j(R) M[F]`, which by `eq:rho-definition` is exactly
`a_R[F] ≥ ρ_j(R) b̂_R[F]` (`eq:modified-mass-comparison`); the abstract step
`minmax_lower_of_bulk_codim'` then converts this into the eigenvalue bound. -/
theorem lower_of_globalComparison (hR : 0 < R) (hLR : (Cm.K + Cp.K) * R < L)
    {td : TraceData Cm Cp L R} {nu C c₀ : ℝ} (hC : 0 ≤ C) (_hc₀ : 0 < c₀)
    (gc : GlobalComparisonData Cm Cp L α hR hLR td nu C c₀)
    (hβm' : 0 < Cm.beta α - C * R) (hβp' : 0 < Cp.beta α - C * R)
    (hβm'' : 0 < Cm.beta α + C * R) (hβp'' : 0 < Cp.beta α + C * R)
    (j : ℕ) (hj : 1 ≤ j)
    (hρh : Interval.mu (Cm.beta α - C * R) (Cp.beta α - C * R) (bulkLength Cm Cp L R) j
              hβm' hβp' (bulkLength_pos hLR) hj
            / (1 + C * R + C * R * Interval.mu (Cm.beta α - C * R) (Cp.beta α - C * R)
              (bulkLength Cm Cp L R) j hβm' hβp' (bulkLength_pos hLR) hj)
          ≤ c₀ / R ^ 2) :
    Interval.mu (Cm.beta α - C * R) (Cp.beta α - C * R) (bulkLength Cm Cp L R) j
          hβm' hβp' (bulkLength_pos hLR) hj
        / (1 + C * R + C * R * Interval.mu (Cm.beta α - C * R) (Cp.beta α - C * R)
          (bulkLength Cm Cp L R) j hβm' hβp' (bulkLength_pos hLR) hj) + nu
      ≤ lambdaThin hR hLR td α j := by
  have hℓR : 0 < bulkLength Cm Cp L R := bulkLength_pos hLR
  have hCR : 0 ≤ C * R := mul_nonneg hC hR.le
  set ℓ : ℝ := bulkLength Cm Cp L R with hℓdef
  set lj : ℝ := Interval.mu (Cm.beta α - C * R) (Cp.beta α - C * R) ℓ j hβm' hβp' hℓR hj
    with hljdef
  have hlj0 : 0 ≤ lj := by
    rw [hljdef]; exact Interval.mu_nonneg _ _ _ _ _ _ _ _
  have hD : 0 < 1 + C * R + C * R * lj := by nlinarith
  -- injectivity of the trial extension, from `trial_mass`
  have hliftinj : ∀ v : H1Q ℓ, gc.lift v = 0 → v = 0 := by
    intro v hv
    by_contra hne
    have h1 : 0 < massQ ℓ v := massQ_pos hℓR v hne
    have h2 := gc.trial_mass v
    rw [hv] at h2
    have h3 : massPQ (0 : H1PQ (thinDomain Cm Cp L R)) = 0 := by
      simp only [massPQ, map_zero]
    rw [h3] at h2
    linarith
  -- a `j`-dimensional subspace of `H1PQ Ω_R` exists (the image of the interval trial space)
  have hex : ∃ W : Submodule ℝ (H1PQ (thinDomain Cm Cp L R)), Module.finrank ℝ W = j := by
    refine ⟨Submodule.map gc.lift (trialSpaceQ (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ
      hβm'' hβp'' hℓR j), ?_⟩
    exact Spectrum.finrank_map_of_injOn gc.lift _ j hj
      (trialSpaceQ_finrank _ _ _ _ _ _ _) (fun v _ hv => hliftinj v hv)
  refine Spectrum.minmax_lower_of_bulk_codim'
    (robinFormPQ (isOpen_thinDomain hR hLR) td.bd td.vanishesOnNullAEP α)
    (massPQ (Ω := thinDomain Cm Cp L R)) nu
    (robinFormQ (Cm.beta α - C * R) (Cp.beta α - C * R) ℓ)
    (fun v => (1 + C * R) * massQ ℓ v
      + C * R * robinFormQ (Cm.beta α - C * R) (Cp.beta α - C * R) ℓ v)
    gc.Z gc.π (c₀ / R ^ 2) j hj ⟨?_, ?_⟩ gc.π_surj massPQ_pos ?_ gc.Z_nonneg _ ?_ hρh
    (nodesEvalQ (Cm.beta α - C * R) (Cp.beta α - C * R) ℓ hβm' hβp' hℓR j hj)
    (finrank_range_nodesEvalQ _ _ _ _ _ _ _ _) ?_ hex
  · -- `eq:global-energy-lower`
    intro u
    exact gc.lower u
  · -- `eq:global-mass-upper` together with `eq:D-less-a`
    intro u
    have h1 := gc.upper u
    have h2 : robinFormQ 0 0 ℓ (gc.π u)
        ≤ robinFormQ (Cm.beta α - C * R) (Cp.beta α - C * R) ℓ (gc.π u) :=
      robinFormQ_mono hβm'.le hβp'.le _
    nlinarith [h1, h2, hCR]
  · -- per-subspace boundedness of the Rayleigh ratio
    intro W hW
    haveI : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_pos (by omega)
    exact bddAboveRatio_robinFormPQ_on (isOpen_thinDomain hR hLR) td.bd
      td.vanishesOnNullAEP α W
  · -- `ρ_j(R) ≥ 0`
    exact div_nonneg hlj0 hD.le
  · -- `eq:modified-mass-comparison`:  `ρ_j(R) b̂_R[F] ≤ a_R[F]`
    intro v hv
    have hpic := picone_generalQ (Cm.beta α - C * R) (Cp.beta α - C * R) ℓ hβm' hβp' hℓR j hj
      v hv
    rw [← hljdef] at hpic
    have hA0 : 0 ≤ robinFormQ (Cm.beta α - C * R) (Cp.beta α - C * R) ℓ v :=
      robinFormQ_nonneg _ _ _ hβm'.le hβp'.le hℓR.le v
    have hM0 : 0 ≤ massQ ℓ v := massQ_nonneg hℓR.le v
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    have h1CR : (0 : ℝ) ≤ 1 + C * R := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hpic h1CR]

/-- **The upper bound of `sec:proof`** (`eq:main-upper`, before the interval perturbation
step): with `η_j(R) = μ_j(β₋+CR, β₊+CR; ℓ_R)`,

`λ_j(Ω_R;α) ≤ η_j(R) + ν_R`.

The trial space is the image under `T_R` of the span `W_{j,R}` of the first `j` interval
eigenfunctions (`RobinCaps.Sobolev.trialSpaceQ`), and the two hypotheses
`eq:trial-mass`/`eq:trial-energy` feed the abstract step `minmax_upper_of_bulk_trial'` with
zero defect (`s = 0`, `δ = γ = 0`). -/
theorem upper_of_globalComparison (hR : 0 < R) (hLR : (Cm.K + Cp.K) * R < L)
    {td : TraceData Cm Cp L R} {nu C c₀ : ℝ} (hα : 0 ≤ α)
    (gc : GlobalComparisonData Cm Cp L α hR hLR td nu C c₀)
    (hβm'' : 0 < Cm.beta α + C * R) (hβp'' : 0 < Cp.beta α + C * R)
    (j : ℕ) (hj : 1 ≤ j) :
    lambdaThin hR hLR td α j
      ≤ Interval.mu (Cm.beta α + C * R) (Cp.beta α + C * R) (bulkLength Cm Cp L R) j
          hβm'' hβp'' (bulkLength_pos hLR) hj + nu := by
  have hℓR : 0 < bulkLength Cm Cp L R := bulkLength_pos hLR
  set ℓ : ℝ := bulkLength Cm Cp L R with hℓdef
  have hliftinj : ∀ v : H1Q ℓ, gc.lift v = 0 → v = 0 := by
    intro v hv
    by_contra hne
    have h1 : 0 < massQ ℓ v := massQ_pos hℓR v hne
    have h2 := gc.trial_mass v
    rw [hv] at h2
    have h3 : massPQ (0 : H1PQ (thinDomain Cm Cp L R)) = 0 := by
      simp only [massPQ, map_zero]
    rw [h3] at h2
    linarith
  have hmain := Spectrum.minmax_upper_of_bulk_trial'
    (robinFormPQ (isOpen_thinDomain hR hLR) td.bd td.vanishesOnNullAEP α)
    (massPQ (Ω := thinDomain Cm Cp L R)) nu
    (robinFormQ (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ) (massQ ℓ) (fun _ => (0 : ℝ))
    gc.lift massPQ_pos
    (bddBelowRatio_robinFormPQ (isOpen_thinDomain hR hLR) td.bd td.vanishesOnNullAEP hα
      td.bd_nonneg)
    j hj
    (Interval.mu (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ j hβm'' hβp'' hℓR hj) 0 0 le_rfl
    (trialSpaceQ (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ hβm'' hβp'' hℓR j)
    (trialSpaceQ_finrank _ _ _ _ _ _ _)
    (fun v _ hv => hliftinj v hv)
    (trialSpaceQ_le (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ hβm'' hβp'' hℓR j hj)
    (fun v _ _ => by norm_num)
    (fun v _ _ => gc.trial_mass v)
    (fun v _ _ => by
      have h := gc.trial_energy v
      norm_num
      linarith)
    (by
      have := Interval.mu_nonneg (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ j hβm'' hβp''
        hℓR hj
      linarith)
  have hz : Interval.mu (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ j hβm'' hβp'' hℓR hj
      + 0 * 0 + nu
      = Interval.mu (Cm.beta α + C * R) (Cp.beta α + C * R) ℓ j hβm'' hβp'' hℓR hj + nu := by
    ring
  rw [hz] at hmain
  exact hmain

/-! ## Part E: the reduction `GlobalComparison ⇒ MainTheorem` -/

set_option maxHeartbeats 1000000 in

/-- **The reduction.**  `GlobalComparison` (the single remaining analytic statement of
`sec:proof`) implies the manuscript's `thm:main` for the genuine variational Robin
eigenvalues `λ_j(Ω_R;α) = lambdaThin …`.

The proof follows `sec:proof` line by line:

* the lower bound `eq:main-lower` comes from `lower_of_globalComparison` (finite-codimension
  constraints + interval Picone), followed by `ρ_j(R) ≥ ℓ_j(R) - C R` (the elementary
  estimate for `eq:rho-definition`, using `ℓ_j(R) = O(1)`) and
  `ℓ_j(R) = μ_j(β₋,β₊;L) + O(R)` (`eq:ell-to-limit`, i.e.
  `RobinCaps.Interval.mu_O_R` applied with `p_R = β₋ - CR`, `q_R = β₊ - CR`, `ℓ_R`);
* the upper bound `eq:main-upper` comes from `upper_of_globalComparison` (trial space
  `T_R W_{j,R}`) followed by `η_j(R) = μ_j(β₋,β₊;L) + O(R)` (`eq:interval-O-R`, i.e.
  `RobinCaps.Interval.mu_O_R` with `p_R = β₋ + CR`, `q_R = β₊ + CR`);
* the thresholds are finitely many and uniform over `j ≤ J`, because
  `RobinCaps.Interval.mu_O_R` is already uniform in `j ≤ J`
  (`mu_perturbation_bound_uniform`). -/
theorem mainTheorem_of_globalComparison (m : ℕ) (Cm Cp : Cap m) (L α : ℝ) (hL : 0 < L)
    (hα : 0 ≤ α) (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α)
    (nu : ℝ → ℝ) (R₀ : ℝ) (tf : TraceFamily Cm Cp L R₀)
    (hG : GlobalComparison Cm Cp L α nu R₀ tf) :
    MainTheorem m Cm Cp L α hL hβm hβp nu R₀ tf := by
  obtain ⟨Cg, c₀, R₁, hCg, hc₀, hR₁, hR₁R₀, hdata⟩ := hG
  intro J
  -- `Jp = max J 1`, so that `μ_{Jp}` is defined and dominates all `μ_j`, `j ≤ J`
  have hJp : 1 ≤ max J 1 := le_max_right _ _
  -- the two interval perturbation bounds (`eq:ell-to-limit` and `eq:interval-O-R`)
  obtain ⟨Km, Rm, hRm, hminus⟩ :=
    Interval.mu_O_R (max J 1) (Cm.beta α) (Cp.beta α) L hβm hβp hL
      (fun r => Cm.beta α - Cg * r) (fun r => Cp.beta α - Cg * r)
      (fun r => bulkLength Cm Cp L r) Cg Cg |Cm.K + Cp.K|
      (by
        intro r hr
        show |Cm.beta α - Cg * r - Cm.beta α| ≤ Cg * r
        have h : |Cm.beta α - Cg * r - Cm.beta α| = Cg * r := by
          rw [show Cm.beta α - Cg * r - Cm.beta α = -(Cg * r) from by ring, abs_neg,
            abs_of_nonneg (mul_nonneg hCg hr.le)]
        exact le_of_eq h)
      (by
        intro r hr
        show |Cp.beta α - Cg * r - Cp.beta α| ≤ Cg * r
        have h : |Cp.beta α - Cg * r - Cp.beta α| = Cg * r := by
          rw [show Cp.beta α - Cg * r - Cp.beta α = -(Cg * r) from by ring, abs_neg,
            abs_of_nonneg (mul_nonneg hCg hr.le)]
        exact le_of_eq h)
      (by
        intro r hr
        show |bulkLength Cm Cp L r - L| ≤ |Cm.K + Cp.K| * r
        have h : |bulkLength Cm Cp L r - L| = |Cm.K + Cp.K| * r := by
          rw [show bulkLength Cm Cp L r - L = -((Cm.K + Cp.K) * r) from by
                simp only [bulkLength]; ring, abs_neg, abs_mul, abs_of_pos hr]
        exact le_of_eq h)
  obtain ⟨Kp, Rp, hRp, hplus⟩ :=
    Interval.mu_O_R (max J 1) (Cm.beta α) (Cp.beta α) L hβm hβp hL
      (fun r => Cm.beta α + Cg * r) (fun r => Cp.beta α + Cg * r)
      (fun r => bulkLength Cm Cp L r) Cg Cg |Cm.K + Cp.K|
      (by
        intro r hr
        show |Cm.beta α + Cg * r - Cm.beta α| ≤ Cg * r
        have h : |Cm.beta α + Cg * r - Cm.beta α| = Cg * r := by
          rw [show Cm.beta α + Cg * r - Cm.beta α = Cg * r from by ring,
            abs_of_nonneg (mul_nonneg hCg hr.le)]
        exact le_of_eq h)
      (by
        intro r hr
        show |Cp.beta α + Cg * r - Cp.beta α| ≤ Cg * r
        have h : |Cp.beta α + Cg * r - Cp.beta α| = Cg * r := by
          rw [show Cp.beta α + Cg * r - Cp.beta α = Cg * r from by ring,
            abs_of_nonneg (mul_nonneg hCg hr.le)]
        exact le_of_eq h)
      (by
        intro r hr
        show |bulkLength Cm Cp L r - L| ≤ |Cm.K + Cp.K| * r
        have h : |bulkLength Cm Cp L r - L| = |Cm.K + Cp.K| * r := by
          rw [show bulkLength Cm Cp L r - L = -((Cm.K + Cp.K) * r) from by
                simp only [bulkLength]; ring, abs_neg, abs_mul, abs_of_pos hr]
        exact le_of_eq h)
  -- nonnegative versions of the two perturbation constants
  have hKm0 : (0 : ℝ) ≤ max Km 0 := le_max_right _ _
  have hKp0 : (0 : ℝ) ≤ max Kp 0 := le_max_right _ _
  -- the uniform bound `M` for `ℓ_j(R)`, `j ≤ J`
  have hmuJ0 : 0 ≤ Interval.mu (Cm.beta α) (Cp.beta α) L (max J 1) hβm hβp hL hJp :=
    Interval.mu_nonneg _ _ _ _ _ _ _ _
  set M : ℝ := Interval.mu (Cm.beta α) (Cp.beta α) L (max J 1) hβm hβp hL hJp + max Km 0
    with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  -- the threshold
  have hβ0 : 0 < min (Cm.beta α) (Cp.beta α) := lt_min hβm hβp
  have hCg1 : (0 : ℝ) < Cg + 1 := by linarith
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  refine ⟨max (max Km 0 + Cg * M * (1 + M)) (max Kp 0),
    min (min R₁ (min Rm Rp))
      (min 1 (min (min (Cm.beta α) (Cp.beta α) / (Cg + 1)) (c₀ / (M + 1)))),
    le_trans (by positivity) (le_max_left _ _),
    lt_min (lt_min hR₁ (lt_min hRm hRp))
      (lt_min one_pos (lt_min (div_pos hβ0 hCg1) (div_pos hc₀ hM1))),
    le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) hR₁R₀, ?_⟩
  intro R hR hRR₀ hRRJ hLR j hj hjJ
  -- unpack the threshold
  have hRR₁ : R < R₁ :=
    lt_of_lt_of_le hRRJ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hRRm : R < Rm :=
    lt_of_lt_of_le hRRJ
      (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hRRp : R < Rp :=
    lt_of_lt_of_le hRRJ
      (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hR1 : R < 1 :=
    lt_of_lt_of_le hRRJ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRβ : R < min (Cm.beta α) (Cp.beta α) / (Cg + 1) :=
    lt_of_lt_of_le hRRJ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hRc : R < c₀ / (M + 1) :=
    lt_of_lt_of_le hRRJ
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- positivity of the shifted endpoint parameters
  have hCR : 0 ≤ Cg * R := mul_nonneg hCg hR.le
  have hCRβ : Cg * R < min (Cm.beta α) (Cp.beta α) := by
    rw [lt_div_iff₀ hCg1] at hRβ
    linarith
  have hβm' : 0 < Cm.beta α - Cg * R := by
    have := lt_of_lt_of_le hCRβ (min_le_left _ _); linarith
  have hβp' : 0 < Cp.beta α - Cg * R := by
    have := lt_of_lt_of_le hCRβ (min_le_right _ _); linarith
  have hβm'' : 0 < Cm.beta α + Cg * R := by linarith
  have hβp'' : 0 < Cp.beta α + Cg * R := by linarith
  have hℓR : 0 < bulkLength Cm Cp L R := bulkLength_pos hLR
  obtain ⟨gc⟩ := hdata R hR hRR₀ hRR₁ hLR
  -- the two interval eigenvalues at the perturbed parameters
  have hjJp : j ≤ max J 1 := le_trans hjJ (le_max_left _ _)
  have hmin := hminus R hR hRRm j hj hjJp hβm' hβp' hℓR
  have hpls := hplus R hR hRRp j hj hjJp hβm'' hβp'' hℓR
  set lj : ℝ := Interval.mu (Cm.beta α - Cg * R) (Cp.beta α - Cg * R)
    (bulkLength Cm Cp L R) j hβm' hβp' hℓR hj with hljdef
  set ej : ℝ := Interval.mu (Cm.beta α + Cg * R) (Cp.beta α + Cg * R)
    (bulkLength Cm Cp L R) j hβm'' hβp'' hℓR hj with hejdef
  set muj : ℝ := Interval.mu (Cm.beta α) (Cp.beta α) L j hβm hβp hL hj with hmujdef
  have hlj0 : 0 ≤ lj := by rw [hljdef]; exact Interval.mu_nonneg _ _ _ _ _ _ _ _
  have hmujJ : muj ≤ Interval.mu (Cm.beta α) (Cp.beta α) L (max J 1) hβm hβp hL hJp := by
    rw [hmujdef]
    exact mu_le_mu (Cm.beta α) (Cp.beta α) L hβm hβp hL hj hJp hjJp
  obtain ⟨hmin1, hmin2⟩ := abs_le.mp hmin
  obtain ⟨hpls1, hpls2⟩ := abs_le.mp hpls
  have hKmR : Km * R ≤ max Km 0 * R :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le
  have hKpR : Kp * R ≤ max Kp 0 * R :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le
  -- uniform bound `ℓ_j(R) ≤ M`
  have hljM : lj ≤ M := by
    have h1 : max Km 0 * R ≤ max Km 0 * 1 :=
      mul_le_mul_of_nonneg_left hR1.le hKm0
    rw [hMdef]
    linarith
  -- the denominator of `eq:rho-definition`
  have hCRlj : 0 ≤ Cg * R * lj := mul_nonneg hCR hlj0
  have hD : 0 < 1 + Cg * R + Cg * R * lj := by linarith
  have hDne : (1 + Cg * R + Cg * R * lj) ≠ 0 := ne_of_gt hD
  set ρ : ℝ := lj / (1 + Cg * R + Cg * R * lj) with hρdef
  have hρ0 : 0 ≤ ρ := div_nonneg hlj0 hD.le
  have hρD : ρ * (1 + Cg * R + Cg * R * lj) = lj := by
    rw [hρdef]; field_simp
  have hρlj : ρ ≤ lj := by
    rw [hρdef]; exact div_le_self hlj0 (by linarith)
  have hρM : ρ ≤ M := le_trans hρlj hljM
  -- `ρ_j(R) ≤ h_R = c₀ R^{-2}`
  have hRsq : R ^ 2 ≤ R := by
    have h : R * R ≤ R * 1 := mul_le_mul_of_nonneg_left hR1.le hR.le
    rw [pow_two]; linarith
  have hRsq0 : (0 : ℝ) < R ^ 2 := by positivity
  have hρh : ρ ≤ c₀ / R ^ 2 := by
    have h1 : R * (M + 1) < c₀ := by
      rw [lt_div_iff₀ hM1] at hRc; linarith
    have h2 : M + 1 < c₀ / R := by
      rw [lt_div_iff₀ hR]; linarith
    have h3 : c₀ / R ≤ c₀ / R ^ 2 := by
      apply div_le_div_of_nonneg_left hc₀.le hRsq0 hRsq
    linarith
  -- the lower bound
  have hlow := lower_of_globalComparison hR hLR hCg hc₀ gc hβm' hβp' hβm'' hβp'' j hj
    (by rw [← hljdef, ← hρdef]; exact hρh)
  rw [← hljdef, ← hρdef] at hlow
  -- `ρ_j(R) ≥ ℓ_j(R) - Cg M (1+M) R`
  have hgap : lj - ρ = ρ * (Cg * R) * (1 + lj) := by linear_combination -hρD
  have hgaple : ρ * (Cg * R) * (1 + lj) ≤ M * (Cg * R) * (1 + M) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hρM hCR) (by linarith) (by linarith)
      (mul_nonneg hM0 hCR)
  have hlowfin : muj - (max Km 0 + Cg * M * (1 + M)) * R ≤ ρ := by
    have h1 : muj - max Km 0 * R ≤ lj := by linarith
    linarith
  -- the upper bound
  have hup := upper_of_globalComparison hR hLR hα gc hβm'' hβp'' j hj
  rw [← hejdef] at hup
  have hupfin : ej ≤ muj + max Kp 0 * R := by linarith
  -- combine
  rw [abs_le]
  constructor
  · have h1 : max Km 0 + Cg * M * (1 + M)
        ≤ max (max Km 0 + Cg * M * (1 + M)) (max Kp 0) := le_max_left _ _
    linarith [mul_le_mul_of_nonneg_right h1 hR.le]
  · have h1 : max Kp 0 ≤ max (max Km 0 + Cg * M * (1 + M)) (max Kp 0) := le_max_right _ _
    linarith [mul_le_mul_of_nonneg_right h1 hR.le]

end RobinCaps.ThinDomain

end

