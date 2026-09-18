import RobinCaps.ThinDomain.Boundary
import RobinCaps.ThinDomain.H1PQuotient
import RobinCaps.Domain.Corollary
import RobinCaps.Domain.CapsuleThin
import RobinCaps.Domain.HemisphereBeta
import RobinCaps.Transverse.OneDimBall

/-!
# The genuine Robin eigenvalues `λ_j(Ω_R;α)` of the thin domain, `thm:main`, and
# `cor:counterexample` for those eigenvalues

This file is the *join* of the three layers already built in the project:

* `RobinCaps/ThinDomain/H1PQuotient.lean` supplies the variational values
  `lambdaPQ hΩ bd hbd α j` (manuscript `eq:minmax`) of the Robin form
  `q_Ω[u] = ∫_Ω (|∂ₓu|² + ‖∇_z u‖²) + α · bd[u]` on the a.e.-quotient `H1PQ Ω` of the
  product weak-`H¹` model, where the mass is positive definite;
* `RobinCaps/ThinDomain/Boundary.lean` supplies the concrete boundary integral of
  `∂Ω_R` and packages the (not available in mathlib `v4.26.0`) trace operator as data,
  `TraceData Cm Cp L R`, whose field `bd` is exactly the boundary pairing needed above;
* `RobinCaps/Domain/Corollary.lean` supplies the real-analysis step of
  `cor:counterexample` for *abstract* eigenvalue branches `lam₁ lam₂ : ℝ → ℝ`.

## What is **defined** here

* `lambdaThin hR hL td α j` — the manuscript's `λ_j(Ω_R;α)`, i.e. `lambdaPQ` for
  `Ω = thinDomain Cm Cp L R` (open by `Domain.isOpen_thinDomain`) and for the boundary
  pairing `td.bd` of the given trace data.  This is the genuine min–max eigenvalue of
  the Robin problem on `Ω_R`, not a placeholder: it is the infimum over `j`-dimensional
  subspaces of the supremum of the Rayleigh quotient `q_{Ω_R}/N_{Ω_R}`.
* `TraceFamily Cm Cp L R₀` — the *recorded trace assumption*: a choice of trace data for
  **every** small radius `0 < R < R₀`.  This is the only input of the main theorem that
  mathlib does not provide; it is a Π-type, so `MainTheorem` below quantifies over
  honest eigenvalues of honest Robin forms.
* `lambdaThinFun` — `lambdaThin` turned into a total function of `R` (junk value `0`
  outside the admissible range), so that it can be fed to the abstract corollary of
  `RobinCaps/Domain/Corollary.lean`.
* `MainTheorem` (and `OneCapMainTheorem`) — the statement of the manuscript's `thm:main`
  as a `Prop`:

  > for every `J` there are `C_J ≥ 0` and `R_J > 0` such that
  > `|λ_j(Ω_R;α) − ν_R − μ_j(β₋,β₊;L)| ≤ C_J R` for all `0 < R < R_J` and `1 ≤ j ≤ J`.

  **`MainTheorem` is a target, not a theorem**: nothing in this file (or in this project)
  proves it.  It is stated so that the reduction below is a theorem *about the genuine
  variational eigenvalues*.

## What is **proved** here

* `TraceData.vanishesOnNullAEP` — trace data descends to the a.e.-quotient, so that
  `lambdaThin` is well defined (this is what makes the join of the two layers legitimate).
* The two engine wrappers `lambdaThin_le_of_trial`, `le_lambdaThin_of_codim`, monotonicity
  `lambdaThin_mono_alpha` and positivity `lambdaThin_nonneg` for `lambdaThin`.
* `counterexample_of_mainTheorem` and `counterexample_of_mainTheorem'` — **the reduction**
  `thm:main ⇒ cor:counterexample`, now for the genuine eigenvalues: assuming only
  `MainTheorem` for the hemispherical capsule, for all small `R`
  `λ₂(Ω_R;α) − λ₁(Ω_R;α) < G_α(L) = G_α(diam Ω_R)` (and quantitatively
  `≤ G_α(L) − Δ/2`), together with `euclidDiam Ω_R = L`.

So the logical status is: *conditional only on `thm:main`* (and on the existence of the
trace data, which is the `TraceFamily` argument), the capsule counterexample holds for the
min–max Robin eigenvalues of `Ω_R`.

There are no `sorry`, `admit`, `axiom` or `native_decide` in this file.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter

/-! ## Part A: nonnegativity of the abstract min–max value -/

namespace RobinCaps.Spectrum

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- **The min–max value of a nonnegative Rayleigh quotient is nonnegative.**  No
boundedness hypothesis is needed: an empty inner index set gives `sSup ∅ = 0`, an inner
range unbounded above gives `⨆ = 0` (`Real.iSup_of_not_bddAbove`), and an empty family of
`j`-dimensional subspaces gives `⨅ = 0` (`Real.iInf_of_isEmpty`). -/
theorem minmax_nonneg {q b : H → ℝ} (h : ∀ u : H, u ≠ 0 → 0 ≤ q u / b u) (j : ℕ) :
    0 ≤ minmax q b j := by
  unfold minmax
  rcases isEmpty_or_nonempty {V : Submodule ℝ H // Module.finrank ℝ V = j} with he | hne
  · haveI := he
    simp
  · refine le_ciInf ?_
    intro V
    rcases isEmpty_or_nonempty {u : V.1 // u ≠ 0} with h2 | h2
    · haveI := h2
      rw [iSup_of_empty']
      simp
    · by_cases hb : BddAbove (Set.range fun u : {u : V.1 // u ≠ 0} =>
          q ((u : V.1) : H) / b ((u : V.1) : H))
      · exact le_trans (h _ (fun hh => h2.some.2 (Subtype.ext hh))) (le_ciSup hb h2.some)
      · rw [Real.iSup_of_not_bddAbove hb]

end RobinCaps.Spectrum

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## Part B: the genuine eigenvalues `λ_j(Ω_R;α)` -/

/-- **Trace data descends to the a.e.-quotient.**  The field `vanishes_ae` of `TraceData`
gives the left half of `VanishesOnNullAEP`, and `bd_symm` gives the right half.  This is
the hypothesis under which the boundary pairing `td.bd` defines a form on `H1PQ Ω_R`, hence
under which the min–max values `eq:minmax` of the Robin form are available. -/
theorem TraceData.vanishesOnNullAEP (td : TraceData Cm Cp L R) :
    VanishesOnNullAEP (thinDomain Cm Cp L R) td.bd := by
  constructor
  · intro u hu v
    exact td.vanishes_ae u (mem_nullAEP.mp hu) v
  · intro u v hv
    rw [td.bd_symm]
    exact td.vanishes_ae v (mem_nullAEP.mp hv) u

/-- **The Robin eigenvalues of the thin domain** `λ_j(Ω_R;α)` (manuscript `eq:minmax` on
`Ω_R`):

`λ_j(Ω_R;α) = min_{V ⊆ H¹(Ω_R), dim V = j} max_{0 ≠ u ∈ V} q_{Ω_R}[u] / N_{Ω_R}[u]`,

where `q_{Ω_R}[u] = ∫_{Ω_R} (|∂ₓu|² + ‖∇_z u‖²) + α ∫_{∂Ω_R} |Tr u|² dℋ^m` and
`N_{Ω_R}[u] = ∫_{Ω_R} u²`.  The Sobolev space is the a.e.-quotient `H1PQ (Ω_R)` of the
product weak-`H¹` model, on which the mass is positive definite (`massPQ_pos`), and the
boundary term is the one supplied by the trace data `td` (whose `bd_eq` identifies it with
the concrete revolution boundary integral `boundaryIntegral`).

`λ_j` does not depend on the proofs `hR`, `hL` (they only enter through
`isOpen_thinDomain`, and proofs are irrelevant), so the definition is a genuine function
of `(Cm, Cp, L, R, td, α, j)`. -/
def lambdaThin (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    (α : ℝ) (j : ℕ) : ℝ :=
  lambdaPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α j

theorem lambdaThin_eq_lambdaPQ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (j : ℕ) :
    lambdaThin hR hL td α j
      = lambdaPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α j := rfl

/-- **Trial-space upper bound for `λ_j(Ω_R;α)`** (`lambdaPQ_le_of_trial`): a
`j`-dimensional subspace `W` of `H1PQ (Ω_R)` on which `q_{Ω_R} ≤ t · N_{Ω_R}` bounds
`λ_j(Ω_R;α)` by `t`. -/
theorem lambdaThin_le_of_trial (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (j : ℕ) (hj : 0 < j)
    (W : Submodule ℝ (H1PQ (thinDomain Cm Cp L R))) (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ w ∈ W, w ≠ 0 →
      robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α w ≤ t * massPQ w) :
    lambdaThin hR hL td α j ≤ t :=
  lambdaPQ_le_of_trial (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP hα td.bd_nonneg
    j hj W hW t h

/-- **Finite-codimension lower bound for `λ_j(Ω_R;α)`** (`le_lambdaPQ_of_codim`): if
`t · N_{Ω_R} ≤ q_{Ω_R}` on the kernel of a `(j−1)`-dimensional constraint `φ`, then
`t ≤ λ_j(Ω_R;α)`. -/
theorem le_lambdaThin_of_codim (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) (α : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (φ : H1PQ (thinDomain Cm Cp L R) →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1) (t : ℝ)
    (h : ∀ w : H1PQ (thinDomain Cm Cp L R), w ≠ 0 → φ w = 0 →
      t * massPQ w ≤ robinFormPQ (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α w)
    (hex : ∃ V : Submodule ℝ (H1PQ (thinDomain Cm Cp L R)), Module.finrank ℝ V = j) :
    t ≤ lambdaThin hR hL td α j :=
  le_lambdaPQ_of_codim (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP α j hj φ hφ t h hex

/-- **Monotonicity of `λ_j(Ω_R;α)` in the Robin parameter `α`** (for `j ≥ 1`). -/
theorem lambdaThin_mono_alpha (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α₁ α₂ : ℝ} (hα₁ : 0 ≤ α₁) (hα : α₁ ≤ α₂) (j : ℕ)
    (hj : 1 ≤ j) :
    lambdaThin hR hL td α₁ j ≤ lambdaThin hR hL td α₂ j :=
  lambdaPQ_mono_alpha (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP td.bd_nonneg
    hα₁ hα j hj

/-- **`λ_j(Ω_R;α) ≥ 0` for `α ≥ 0`**: the Robin form is nonnegative (Dirichlet energy plus
`α` times a nonnegative boundary energy) and the mass is nonnegative. -/
theorem lambdaThin_nonneg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (td : TraceData Cm Cp L R) {α : ℝ} (hα : 0 ≤ α) (j : ℕ) :
    0 ≤ lambdaThin hR hL td α j :=
  Spectrum.minmax_nonneg (fun w _ =>
    div_nonneg
      (robinFormPQ_nonneg (isOpen_thinDomain hR hL) td.bd td.vanishesOnNullAEP hα
        td.bd_nonneg w)
      (massPQ_nonneg w)) j

/-! ## Part C: the recorded trace assumption, and `thm:main` as a `Prop` -/

/-- **The recorded trace assumption.**  A `TraceFamily Cm Cp L R₀` is a choice of trace
data on the thin domain `Ω_R` for **every** radius `0 < R < R₀`.  Mathlib `v4.26.0` has no
trace operator on the product ambient space `CapSpace m`, so this is taken as data; every
statement below that mentions `λ_j(Ω_R;α)` for a range of `R` is quantified over such a
family. -/
def TraceFamily (Cm Cp : Cap m) (L R₀ : ℝ) : Type :=
  ∀ R : ℝ, 0 < R → R < R₀ → TraceData Cm Cp L R

/-- **`thm:main` as a `Prop`** (manuscript `eq:minmax` on `Ω_R`, statement of the main
theorem, lines 222–250).

Fix `n ≥ 2`, `m = n − 1`, `α > 0`, `L > 0` and two admissible caps `C₋ = Cm`, `C₊ = Cp`.
With `ν_R` the transverse ground energy `λ₁(B_m(R);α)` (the parameter `nu`; for `m = 1`
this is `Transverse.nuR α R`, see `nuOneDim` below) and `μ_j(β₋,β₊;L)` the `j`-th Robin
eigenvalue of the interval model (`Interval.mu`, with `β∓ = C∓.beta α`), the theorem says:

> for every `J` there are `C_J ≥ 0` and `R_J > 0` with
> `|λ_j(Ω_R;α) − ν_R − μ_j(β₋,β₊;L)| ≤ C_J R` for all `0 < R < R_J` and `1 ≤ j ≤ J`.

The eigenvalues `λ_j(Ω_R;α)` are the genuine min–max values `lambdaThin` of the Robin form
on `Ω_R`, computed with the trace data `tf R _ _` of the recorded family.

**Status:** proved for every pair of admissible caps and every `m ≥ 1`, with
`nu = nuBall m α` (`RobinCaps.mainTheorem_general_top`, `ThinDomain/MainGeneralFinal.lean`).
It is also the hypothesis of `counterexample_of_mainTheorem` below.  (`C_J ≥ 0` rather than the manuscript's `C_J > 0`
makes the hypothesis formally weaker, hence the reduction stronger.) -/
def MainTheorem (m : ℕ) (Cm Cp : Cap m) (L α : ℝ) (hL : 0 < L)
    (hβm : 0 < Cm.beta α) (hβp : 0 < Cp.beta α) (nu : ℝ → ℝ) (R₀ : ℝ)
    (tf : TraceFamily Cm Cp L R₀) : Prop :=
  ∀ J : ℕ, ∃ C R₁ : ℝ, 0 ≤ C ∧ 0 < R₁ ∧ R₁ ≤ R₀ ∧
    ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) (_hR₁ : R < R₁)
      (hLR : (Cm.K + Cp.K) * R < L) (j : ℕ) (hj : 1 ≤ j), j ≤ J →
      |lambdaThin hR hLR (tf R hR hR₀) α j - nu R
        - Interval.mu (Cm.beta α) (Cp.beta α) L j hβm hβp hL hj| ≤ C * R

/-- The flat cap has `β = α` (`Cap.flat_beta_eq_alpha`), in particular `β > 0` for
`α > 0`. -/
theorem flat_beta_pos (m : ℕ) (K : ℝ) (hK : 0 < K) {α : ℝ} (hα : 0 < α) :
    0 < (Cap.flat m K hK).beta α := by
  rw [Cap.flat_beta_eq_alpha m K hK (ne_of_gt (Cap.omega_pos m))]
  exact hα

/-- **The one-cap case of `thm:main`** (manuscript, second half of the statement): the
left cap is the flat cap `Cap.flat m K hK`, for which `β₋ = α`
(`Cap.flat_beta_eq_alpha`), so the asymptotics read
`|λ_j(Ω_R;α) − ν_R − μ_j(α,β₊;L)| ≤ C_J R`.  Like `MainTheorem`, this is a target. -/
def OneCapMainTheorem (m : ℕ) (K : ℝ) (hK : 0 < K) (Cp : Cap m) (L α : ℝ) (hL : 0 < L)
    (hα : 0 < α) (hβp : 0 < Cp.beta α) (nu : ℝ → ℝ) (R₀ : ℝ)
    (tf : TraceFamily (Cap.flat m K hK) Cp L R₀) : Prop :=
  MainTheorem m (Cap.flat m K hK) Cp L α hL (flat_beta_pos m K hK hα) hβp nu R₀ tf

/-- The transverse ground energy `ν_R = λ₁(B_m(R);α)` for `m = 1`, as a total function of
`R` (junk value `0` for `R ≤ 0`): this is the intended instantiation of the parameter `nu`
of `MainTheorem` in transverse dimension one, from
`RobinCaps.Transverse.nuR`. -/
def nuOneDim (α : ℝ) (hα : 0 < α) (R : ℝ) : ℝ :=
  if h : 0 < R then Transverse.nuR α R hα h else 0

theorem nuOneDim_eq (α : ℝ) (hα : 0 < α) {R : ℝ} (hR : 0 < R) :
    nuOneDim α hα R = Transverse.nuR α R hα hR :=
  dif_pos hR

/-! ## Part D: `thm:main ⇒ cor:counterexample`, for the genuine eigenvalues -/

open scoped Classical

/-- `λ_j(Ω_R;α)` as a **total** function of `R`, with junk value `0` outside the range in
which the thin domain is defined.  This is the shape required by the abstract corollary
`RobinCaps.Domain.counterexample_of_asymptotics`, which only inspects `0 < R < R₀`. -/
def lambdaThinFun (Cm Cp : Cap m) (L R₀ α : ℝ) (tf : TraceFamily Cm Cp L R₀) (j : ℕ)
    (R : ℝ) : ℝ :=
  if h : 0 < R ∧ R < R₀ ∧ (Cm.K + Cp.K) * R < L then
    lambdaThin h.1 h.2.2 (tf R h.1 h.2.1) α j
  else 0

theorem lambdaThinFun_eq {L R₀ α : ℝ} (tf : TraceFamily Cm Cp L R₀) (j : ℕ)
    (hR : 0 < R) (hR₀ : R < R₀) (hL : (Cm.K + Cp.K) * R < L) :
    lambdaThinFun Cm Cp L R₀ α tf j R = lambdaThin hR hL (tf R hR hR₀) α j := by
  unfold lambdaThinFun
  rw [dif_pos (show 0 < R ∧ R < R₀ ∧ (Cm.K + Cp.K) * R < L from ⟨hR, hR₀, hL⟩)]

/-- Transport of `Interval.mu` along an equality of the two (equal) Robin coefficients.
Needed because `Interval.mu` takes the positivity proofs as arguments, so a plain `rw`
would produce an ill-typed motive; proof irrelevance closes the goal after `subst`. -/
theorem mu_congr_beta {β β' L : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hL : 0 < L)
    (h : β = β') (j : ℕ) (hj : 1 ≤ j) :
    Interval.mu β β L j hβ hβ hL hj = Interval.mu β' β' L j hβ' hβ' hL hj := by
  subst h
  rfl

/-- `β(hemisphere m) = β₀ > 0` for `α > 0` and `m ≥ 1`
(`Domain.hemisphere_beta_eq_beta0`, `Domain.beta0_pos`). -/
theorem hemisphere_beta_pos (m : ℕ) (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) :
    0 < (hemisphere m).beta α := by
  rw [hemisphere_beta_eq_beta0 m hm α]
  exact beta0_pos hα

/-- **`cor:counterexample` for the genuine Robin eigenvalues of the capsule.**

Let `Ω_R` be the thin domain with two hemispherical caps — by
`Domain.toEuclid_thinDomain_hemisphere` this is (isometrically, through `toEuclid`) the
capsule `{x : dist(x, S) < R}` — and let `λ_j(Ω_R;α) = lambdaThin …` be its genuine
variational Robin eigenvalues, computed from a recorded trace family `tf`.

**Assuming only `MainTheorem`** (the two-term asymptotics of `thm:main`, not proved in this
project) there is `R₁ > 0` such that for every `0 < R < R₁` with `2R < L`:

* `λ₂(Ω_R;α) − λ₁(Ω_R;α) ≤ G_α(L) − Δ/2` (manuscript `eq:finite-deficit`), where
  `Δ = G_α(L) − G_{β₀}(L) > 0` is `Domain.Delta`;
* hence `λ₂(Ω_R;α) − λ₁(Ω_R;α) < G_α(L)`;
* and `euclidDiam Ω_R = L`, so the right-hand side is `G_α(diam Ω_R)`: the pair
  `(Ω_R, α)` violates the conjectured gap bound `λ₂ − λ₁ ≥ G_α(diam)`
  (manuscript `eq:counterexample`).

The mechanism is `β(hemisphere m) = β₀ < α` (`Domain.hemisphere_beta_eq_beta0`,
`Domain.beta0_lt`) together with the strict monotonicity of the interval gap. -/
theorem counterexample_of_mainTheorem' (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL : 0 < L)
    (hα : 0 < α) (nu : ℝ → ℝ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (tf : TraceFamily (hemisphere m) (hemisphere m) L R₀)
    (hmain : MainTheorem m (hemisphere m) (hemisphere m) L α hL
      (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) nu R₀ tf) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L)
        (hR₀' : R < R₀),
      lambdaThin hR (hemisphere_hL h2R) (tf R hR hR₀') α 2
          - lambdaThin hR (hemisphere_hL h2R) (tf R hR hR₀') α 1
        ≤ Interval.gap L hL α - Delta m L hL α / 2 ∧
      lambdaThin hR (hemisphere_hL h2R) (tf R hR hR₀') α 2
          - lambdaThin hR (hemisphere_hL h2R) (tf R hR hR₀') α 1
        < Interval.gap L hL α ∧
      euclidDiam (thinDomain (hemisphere m) (hemisphere m) L R) = L := by
  obtain ⟨C, RJ, hC, hRJ, hRJle, hbound⟩ := hmain 2
  -- the radius range on which the asymptotics are available *and* `Ω_R` is a capsule
  set Rg : ℝ := min RJ (L / 2) with hRgdef
  have hRgpos : 0 < Rg := lt_min hRJ (by linarith)
  have hguard : ∀ R : ℝ, 0 < R → R < Rg →
      R < R₀ ∧ R < RJ ∧ 2 * R < L := by
    intro R hR hRg
    have h1 : R < RJ := lt_of_lt_of_le hRg (min_le_left _ _)
    have h2 : R < L / 2 := lt_of_lt_of_le hRg (min_le_right _ _)
    exact ⟨lt_of_lt_of_le h1 hRJle, h1, by linarith⟩
  -- the eigenvalue branches, as total functions of `R`
  have hmu : ∀ (j : ℕ) (hj : 1 ≤ j),
      Interval.mu ((hemisphere m).beta α) ((hemisphere m).beta α) L j
          (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) hL hj
        = Interval.mu (beta0 m α) (beta0 m α) L j (beta0_pos hα) (beta0_pos hα) hL hj :=
    fun j hj => mu_congr_beta (hemisphere_beta_pos m hm hα) (beta0_pos hα) hL
      (hemisphere_beta_eq_beta0 m hm α) j hj
  have key : ∀ (j : ℕ) (hj : 1 ≤ j), j ≤ 2 → ∀ R : ℝ, 0 < R → R < Rg →
      |lambdaThinFun (hemisphere m) (hemisphere m) L R₀ α tf j R - nu R
        - Interval.mu (beta0 m α) (beta0 m α) L j (beta0_pos hα) (beta0_pos hα) hL hj|
        ≤ C * R := by
    intro j hj hj2 R hR hRg
    obtain ⟨hRR₀, hRRJ, h2R⟩ := hguard R hR hRg
    rw [lambdaThinFun_eq tf j hR hRR₀ (hemisphere_hL h2R), ← hmu j hj]
    exact hbound R hR hRR₀ hRRJ (hemisphere_hL h2R) j hj hj2
  obtain ⟨R₁, hR₁, hconc⟩ :=
    counterexample_of_asymptotics m hm L hL α hα
      (lambdaThinFun (hemisphere m) (hemisphere m) L R₀ α tf 1)
      (lambdaThinFun (hemisphere m) (hemisphere m) L R₀ α tf 2)
      nu C Rg hRgpos hC
      (key 1 (le_refl 1) (by norm_num))
      (key 2 (by norm_num) (le_refl 2))
  refine ⟨R₁, hR₁, ?_⟩
  intro R hR hRR₁ h2R hR₀'
  obtain ⟨hle, hlt⟩ := hconc R hR hRR₁
  rw [lambdaThinFun_eq tf 1 hR hR₀' (hemisphere_hL h2R),
    lambdaThinFun_eq tf 2 hR hR₀' (hemisphere_hL h2R)] at hle hlt
  exact ⟨hle, hlt, euclidDiam_thinDomain_hemisphere hR h2R⟩

/-- **`cor:counterexample`, short form** (`eq:counterexample`): assuming `thm:main`, for
all small `R` the genuine Robin eigenvalues of the hemispherical capsule satisfy
`λ₂(Ω_R;α) − λ₁(Ω_R;α) < G_α(diam Ω_R)`. -/
theorem counterexample_of_mainTheorem (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL : 0 < L)
    (hα : 0 < α) (nu : ℝ → ℝ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (tf : TraceFamily (hemisphere m) (hemisphere m) L R₀)
    (hmain : MainTheorem m (hemisphere m) (hemisphere m) L α hL
      (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) nu R₀ tf) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L)
        (hR₀' : R < R₀),
      lambdaThin hR (hemisphere_hL h2R) (tf R hR hR₀') α 2
          - lambdaThin hR (hemisphere_hL h2R) (tf R hR hR₀') α 1
        < Interval.gap L hL α ∧
      euclidDiam (thinDomain (hemisphere m) (hemisphere m) L R) = L := by
  obtain ⟨R₁, hR₁, h⟩ :=
    counterexample_of_mainTheorem' m hm L α hL hα nu R₀ hR₀ tf hmain
  exact ⟨R₁, hR₁, fun R hR hRR₁ h2R hR₀' =>
    ⟨(h R hR hRR₁ h2R hR₀').2.1, (h R hR hRR₁ h2R hR₀').2.2⟩⟩

end RobinCaps.ThinDomain

end
