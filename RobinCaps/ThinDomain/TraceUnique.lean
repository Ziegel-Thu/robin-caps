import RobinCaps.ThinDomain.Eigen
import RobinCaps.ThinDomain.MainGenFinal

/-!
# Uniqueness of the boundary form across trace data, and eigenvalue invariance

`RobinCaps/ThinDomain/Eigen.lean` packages the trace operator on the thin domain `Ω_R` as
*data* (`TraceData Cm Cp L R`), because mathlib `v4.26.0` has no trace theorem for Lipschitz
domains.  This raises an obvious question: if two different `TraceData` records are supplied,
do they give the same Robin eigenvalues `lambdaThin`?  This file shows **yes**, granted the one
extra analytic fact that is *not* yet in mathlib either: density of `C¹`-up-to-the-boundary
functions in `H¹(Ω_R)` (`C1Dense_tu`, taken here as an explicit hypothesis; it is the subject of
a parallel file, `RobinCaps/Sobolev/ConvexDensity.lean`, not imported here).

## Contents

* `hnormSq_add_le_tu` — the `H¹`-seminorm triangle inequality
  `√(D(u+v)+M(u+v)) ≤ √(Du+Mu) + √(Dv+Mv)`, obtained from the Cauchy–Schwarz inequality
  `RobinCaps.Compact.bilin_cauchy_schwarz` applied to the nonnegative symmetric bilinear form
  `dirichletBilinPₗ + massBilinPₗ`.
* `bd_sub_le_tu` — the diagonal of a trace form is Lipschitz in the `H¹` seminorm:
  `|bd u u − bd v v| ≤ C · ‖u−v‖ · (‖u‖+‖v‖)`, from bilinearity
  (`bd u u − bd v v = bd (u−v) (u+v)`), Cauchy–Schwarz for `bd`, and `trace_ineq`.
* `bd_diag_unique_tu`, `bd_unique_tu` — **uniqueness**: any two `TraceData` records agree on
  `bd`, granted `C1Dense_tu`.
* `lambdaThin_congr_tu` — **eigenvalue invariance**: `lambdaThin` does not depend on which
  `TraceData` is used.
* `mainTheorem_of_any_traceFamily_tu` and the three corollaries
  `mainTheorem_hemisphere_any_tu`, `counterexample_hemisphere_any_tu`,
  `mainTheorem_single_any_tu` — `thm:main`/`cor:counterexample`, once proved for *some* recorded
  trace family, transport to *every* recorded trace family.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap RobinCaps.Compact

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## Part 0: the `H¹` seminorm triangle inequality -/

/-- The combined bilinear form `D + M` on `H1P Ω` is symmetric. -/
theorem dirichletMassBilin_symm_tu {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (dirichletBilinPₗ + massBilinPₗ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ) u v
      = (dirichletBilinPₗ + massBilinPₗ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ) v u := by
  simp only [LinearMap.add_apply, dirichletBilinPₗ_apply, massBilinPₗ_apply]
  rw [dirichletBilinP_comm, massBilinP_comm]

/-- The combined bilinear form `D + M` on `H1P Ω` is nonnegative on the diagonal, with diagonal
value `dirichletP w + massP w`. -/
theorem dirichletMassBilin_diag_tu {Ω : Set (CapSpace m)} (w : H1P Ω) :
    (dirichletBilinPₗ + massBilinPₗ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ) w w
      = dirichletP w + massP w := by
  simp only [LinearMap.add_apply, dirichletBilinPₗ_apply, massBilinPₗ_apply,
    dirichletBilinP_self, massBilinP_self]

/-- **The `H¹`-seminorm triangle inequality.** -/
theorem hnormSq_add_le_tu {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    Real.sqrt (dirichletP (u + v) + massP (u + v))
      ≤ Real.sqrt (dirichletP u + massP u) + Real.sqrt (dirichletP v + massP v) := by
  set Q := (dirichletBilinPₗ + massBilinPₗ : H1P Ω →ₗ[ℝ] H1P Ω →ₗ[ℝ] ℝ) with hQdef
  have hQsymm : ∀ a b : H1P Ω, Q a b = Q b a := dirichletMassBilin_symm_tu
  have hQnonneg : ∀ w : H1P Ω, 0 ≤ Q w w := fun w => by
    rw [hQdef, dirichletMassBilin_diag_tu]
    exact add_nonneg (dirichletP_nonneg w) (massP_nonneg w)
  have hQadd : Q (u + v) (u + v) = Q u u + 2 * Q u v + Q v v :=
    RobinCaps.Compact.bilin_add_add hQsymm u v
  have hcs : Q u v ^ 2 ≤ Q u u * Q v v :=
    RobinCaps.Compact.bilin_cauchy_schwarz hQsymm hQnonneg u v
  have hQuu : 0 ≤ Q u u := hQnonneg u
  have hQvv : 0 ≤ Q v v := hQnonneg v
  set a : ℝ := Real.sqrt (Q u u) with ha_def
  set b : ℝ := Real.sqrt (Q v v) with hb_def
  have hsu : a ^ 2 = Q u u := Real.sq_sqrt hQuu
  have hsv : b ^ 2 = Q v v := Real.sq_sqrt hQvv
  have hQuv_le : Q u v ≤ a * b := by
    have h1 : |Q u v| ≤ Real.sqrt (Q u u * Q v v) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hcs
    have h2 : Real.sqrt (Q u u * Q v v) = a * b := by
      rw [ha_def, hb_def, Real.sqrt_mul hQuu]
    calc Q u v ≤ |Q u v| := le_abs_self _
      _ ≤ Real.sqrt (Q u u * Q v v) := h1
      _ = a * b := h2
  have hstep : Q (u + v) (u + v) ≤ (a + b) ^ 2 := by
    have hle : Q u u + 2 * Q u v + Q v v ≤ Q u u + 2 * (a * b) + Q v v := by linarith
    calc Q (u + v) (u + v) = Q u u + 2 * Q u v + Q v v := hQadd
      _ ≤ Q u u + 2 * (a * b) + Q v v := hle
      _ = (a + b) ^ 2 := by rw [← hsu, ← hsv]; ring
  have hfinal : Real.sqrt (Q (u + v) (u + v)) ≤ Real.sqrt ((a + b) ^ 2) :=
    Real.sqrt_le_sqrt hstep
  have hrhs_nonneg : 0 ≤ a + b := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_sq hrhs_nonneg] at hfinal
  have haeq : a = Real.sqrt (dirichletP u + massP u) := by
    rw [ha_def, hQdef, dirichletMassBilin_diag_tu]
  have hbeq : b = Real.sqrt (dirichletP v + massP v) := by
    rw [hb_def, hQdef, dirichletMassBilin_diag_tu]
  rw [hQdef, dirichletMassBilin_diag_tu] at hfinal
  rwa [haeq, hbeq] at hfinal

/-! ## Part 1: continuity of the diagonal boundary form in the `H¹` seminorm -/

/-- The diagonal-difference identity for a symmetric bilinear form:
`bd u u − bd v v = bd (u−v) (u+v)`. -/
theorem bd_diag_sub_eq_tu (td : TraceData Cm Cp L R) (u v : H1P (thinDomain Cm Cp L R)) :
    td.bd u u - td.bd v v = td.bd (u - v) (u + v) := by
  simp only [map_sub, map_add, LinearMap.sub_apply]
  rw [td.bd_symm v u]
  ring

/-- **Continuity of the diagonal boundary form in the `H¹` seminorm.**  For a `TraceData` with
trace constant `C` (`trace_ineq`):
`|bd u u − bd v v| ≤ C · ‖u−v‖ · (‖u‖+‖v‖)`, where `‖w‖ = √(dirichletP w + massP w)`.

Route: `bd u u − bd v v = bd (u−v) (u+v)` (`bd_diag_sub_eq_tu`), Cauchy–Schwarz for the
nonnegative symmetric bilinear form `bd` (`RobinCaps.Compact.bilin_cauchy_schwarz`), the trace
inequality on each factor, and the seminorm triangle inequality (`hnormSq_add_le_tu`) to bound
`‖u+v‖ ≤ ‖u‖+‖v‖`. -/
theorem bd_sub_le_tu (td : TraceData Cm Cp L R) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w : H1P (thinDomain Cm Cp L R), td.bd w w ≤ C * (dirichletP w + massP w))
    (u v : H1P (thinDomain Cm Cp L R)) :
    |td.bd u u - td.bd v v|
      ≤ C * Real.sqrt (dirichletP (u - v) + massP (u - v))
        * (Real.sqrt (dirichletP u + massP u) + Real.sqrt (dirichletP v + massP v)) := by
  set w1 : H1P (thinDomain Cm Cp L R) := u - v with hw1def
  set w2 : H1P (thinDomain Cm Cp L R) := u + v with hw2def
  have hnn1 : 0 ≤ dirichletP w1 + massP w1 := add_nonneg (dirichletP_nonneg w1) (massP_nonneg w1)
  have hnn2 : 0 ≤ dirichletP w2 + massP w2 := add_nonneg (dirichletP_nonneg w2) (massP_nonneg w2)
  have hbd1 : 0 ≤ td.bd w1 w1 := td.bd_nonneg w1
  have hbd2 : 0 ≤ td.bd w2 w2 := td.bd_nonneg w2
  have hbd1le : td.bd w1 w1 ≤ C * (dirichletP w1 + massP w1) := hC w1
  have hbd2le : td.bd w2 w2 ≤ C * (dirichletP w2 + massP w2) := hC w2
  have hcs : td.bd w1 w2 ^ 2 ≤ td.bd w1 w1 * td.bd w2 w2 :=
    RobinCaps.Compact.bilin_cauchy_schwarz td.bd_symm td.bd_nonneg w1 w2
  have habs : |td.bd w1 w2| ≤ Real.sqrt (td.bd w1 w1) * Real.sqrt (td.bd w2 w2) := by
    have h1 : |td.bd w1 w2| = Real.sqrt (td.bd w1 w2 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    rw [h1, ← Real.sqrt_mul hbd1]
    exact Real.sqrt_le_sqrt hcs
  have hstep1 : Real.sqrt (td.bd w1 w1) ≤ Real.sqrt (C * (dirichletP w1 + massP w1)) :=
    Real.sqrt_le_sqrt hbd1le
  have hstep2 : Real.sqrt (td.bd w2 w2) ≤ Real.sqrt (C * (dirichletP w2 + massP w2)) :=
    Real.sqrt_le_sqrt hbd2le
  have hCsqrt : Real.sqrt (C * (dirichletP w1 + massP w1))
      = Real.sqrt C * Real.sqrt (dirichletP w1 + massP w1) := Real.sqrt_mul hC0 _
  have hCsqrt2 : Real.sqrt (C * (dirichletP w2 + massP w2))
      = Real.sqrt C * Real.sqrt (dirichletP w2 + massP w2) := Real.sqrt_mul hC0 _
  have htri : Real.sqrt (dirichletP w2 + massP w2)
      ≤ Real.sqrt (dirichletP u + massP u) + Real.sqrt (dirichletP v + massP v) := by
    rw [hw2def]; exact hnormSq_add_le_tu u v
  have hfin : Real.sqrt (td.bd w1 w1) * Real.sqrt (td.bd w2 w2)
      ≤ C * Real.sqrt (dirichletP w1 + massP w1)
        * (Real.sqrt (dirichletP u + massP u) + Real.sqrt (dirichletP v + massP v)) := by
    have hnn_sC : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
    have hnn_s1 : 0 ≤ Real.sqrt (dirichletP w1 + massP w1) := Real.sqrt_nonneg _
    have hnn_s2 : 0 ≤ Real.sqrt (dirichletP w2 + massP w2) := Real.sqrt_nonneg _
    have hCsq : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC0
    calc Real.sqrt (td.bd w1 w1) * Real.sqrt (td.bd w2 w2)
        ≤ Real.sqrt (C * (dirichletP w1 + massP w1))
            * Real.sqrt (C * (dirichletP w2 + massP w2)) :=
          mul_le_mul hstep1 hstep2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (Real.sqrt C * Real.sqrt (dirichletP w1 + massP w1))
            * (Real.sqrt C * Real.sqrt (dirichletP w2 + massP w2)) := by
            rw [hCsqrt, hCsqrt2]
      _ = C * Real.sqrt (dirichletP w1 + massP w1) * Real.sqrt (dirichletP w2 + massP w2) := by
            rw [mul_mul_mul_comm, hCsq, mul_assoc]
      _ ≤ C * Real.sqrt (dirichletP w1 + massP w1)
            * (Real.sqrt (dirichletP u + massP u) + Real.sqrt (dirichletP v + massP v)) := by
            have hCnn : 0 ≤ C * Real.sqrt (dirichletP w1 + massP w1) :=
              mul_nonneg hC0 hnn_s1
            exact mul_le_mul_of_nonneg_left htri hCnn
  calc |td.bd u u - td.bd v v| = |td.bd w1 w2| := by rw [bd_diag_sub_eq_tu td u v]
    _ ≤ Real.sqrt (td.bd w1 w1) * Real.sqrt (td.bd w2 w2) := habs
    _ ≤ C * Real.sqrt (dirichletP w1 + massP w1)
          * (Real.sqrt (dirichletP u + massP u) + Real.sqrt (dirichletP v + massP v)) := hfin

/-! ## Part 2: uniqueness of the boundary form -/

/-- **Interface: `C¹`-up-to-the-boundary functions are `H¹`-dense in the thin domain.**  Proved
in parallel (`RobinCaps/Sobolev/ConvexDensity.lean`, not imported here); taken as an explicit
hypothesis of the results below. -/
def C1Dense_tu (Cm Cp : Cap m) (L R : ℝ) : Prop :=
  ∀ u : H1P (thinDomain Cm Cp L R), ∀ η : ℝ, 0 < η →
    ∃ v : H1P (thinDomain Cm Cp L R), ContinuousOn v.toFun (closure (thinDomain Cm Cp L R)) ∧
      massP (u - v) + dirichletP (u - v) ≤ η

/-- The triangle inequality for subtraction, in the form used repeatedly below. -/
theorem abs_sub_le_tu (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [abs_neg, ← sub_eq_add_neg] at h

/-- A real number bounded, for every `ε ∈ (0,1]`, by `C * √ε` must be zero. -/
theorem eq_zero_of_forall_le_sqrt_tu {x C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |x| ≤ C * Real.sqrt ε) : x = 0 := by
  by_contra hx
  have ha : 0 < |x| := abs_pos.2 hx
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have h1 := h (1 / 2) (by norm_num) (by norm_num)
    rw [← hC0, zero_mul] at h1
    linarith
  · set ε : ℝ := min (1 / 2) ((|x| / (2 * C)) ^ 2) with hεdef
    have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hb : ε ≤ (|x| / (2 * C)) ^ 2 := min_le_right _ _
    have h0 : 0 ≤ |x| / (2 * C) := by positivity
    have hsqrt : Real.sqrt ε ≤ |x| / (2 * C) := by
      calc Real.sqrt ε ≤ Real.sqrt ((|x| / (2 * C)) ^ 2) := Real.sqrt_le_sqrt hb
        _ = |x| / (2 * C) := Real.sqrt_sq h0
    have h2 := h ε hεpos hε1
    have h3 : C * Real.sqrt ε ≤ C * (|x| / (2 * C)) := mul_le_mul_of_nonneg_left hsqrt hCpos.le
    have h4 : C * (|x| / (2 * C)) = |x| / 2 := by field_simp
    rw [h4] at h3
    linarith

/-- **Uniqueness of the boundary form on the diagonal**: any two `TraceData` records agree on
`bd u u`, granted `C1Dense_tu`.

Route: for `ε > 0`, `hd` gives a `C¹`-up-to-the-boundary approximant `v` of `u` with
`massP (u−v) + dirichletP (u−v) ≤ ε`; `tr_continuous` identifies `td₁.bd v v` and `td₂.bd v v`
with the same concrete `boundaryEnergy … v.toFun` (so they agree); `bd_sub_le_tu` bounds
`|tdᵢ.bd u u − tdᵢ.bd v v|` by `Cᵢ · √ε · (2 ‖u‖ + √ε)` (using the seminorm triangle inequality
to bound `‖v‖ ≤ ‖u‖ + √ε`); summing the two bounds and letting `ε → 0`
(`eq_zero_of_forall_le_sqrt_tu`) forces `td₁.bd u u = td₂.bd u u`. -/
theorem bd_diag_unique_tu (hd : C1Dense_tu Cm Cp L R) (td₁ td₂ : TraceData Cm Cp L R)
    (u : H1P (thinDomain Cm Cp L R)) : td₁.bd u u = td₂.bd u u := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := td₁.trace_ineq
  obtain ⟨C₂, hC₂0, hC₂⟩ := td₂.trace_ineq
  set su : ℝ := Real.sqrt (dirichletP u + massP u) with hsu_def
  have hsu_nonneg : 0 ≤ su := Real.sqrt_nonneg _
  have key : td₁.bd u u - td₂.bd u u = 0 := by
    apply eq_zero_of_forall_le_sqrt_tu
      (mul_nonneg (add_nonneg hC₁0 hC₂0) (by linarith [hsu_nonneg] : (0:ℝ) ≤ 2 * su + 1))
    intro ε hε hε1
    obtain ⟨v, hv_cont, hv_close⟩ := hd u ε hε
    have hbd1 : td₁.bd v v = boundaryEnergy Cm Cp L R v.toFun := td₁.tr_continuous v hv_cont
    have hbd2 : td₂.bd v v = boundaryEnergy Cm Cp L R v.toFun := td₂.tr_continuous v hv_cont
    have hmid : td₁.bd v v = td₂.bd v v := hbd1.trans hbd2.symm
    have hv_close' : dirichletP (u - v) + massP (u - v) ≤ ε := by
      rw [add_comm]; exact hv_close
    have hse : Real.sqrt (dirichletP (u - v) + massP (u - v)) ≤ Real.sqrt ε :=
      Real.sqrt_le_sqrt hv_close'
    have hsv : Real.sqrt (dirichletP v + massP v) ≤ su + Real.sqrt ε := by
      have habel : u + (v - u) = v := by abel
      have htri := hnormSq_add_le_tu u (v - u)
      rw [habel] at htri
      have hvu_eq : dirichletP (v - u) + massP (v - u) = dirichletP (u - v) + massP (u - v) := by
        have h1 : v - u = (-1 : ℝ) • (u - v) := by rw [neg_one_smul]; abel
        rw [h1, dirichletP_smul, massP_smul]
        ring
      rw [hvu_eq] at htri
      calc Real.sqrt (dirichletP v + massP v)
          ≤ su + Real.sqrt (dirichletP (u - v) + massP (u - v)) := htri
        _ ≤ su + Real.sqrt ε := by linarith [hse]
    have hse_nonneg : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
    have hb1 : |td₁.bd u u - td₁.bd v v| ≤ C₁ * Real.sqrt ε * (2 * su + Real.sqrt ε) := by
      have h1 := bd_sub_le_tu td₁ hC₁0 hC₁ u v
      have h2 : Real.sqrt (dirichletP (u - v) + massP (u - v))
            * (su + Real.sqrt (dirichletP v + massP v))
          ≤ Real.sqrt ε * (2 * su + Real.sqrt ε) := by
        have h2a : Real.sqrt (dirichletP v + massP v) ≤ su + Real.sqrt ε := hsv
        have h2b : su + Real.sqrt (dirichletP v + massP v) ≤ su + (su + Real.sqrt ε) := by
          linarith
        calc Real.sqrt (dirichletP (u - v) + massP (u - v))
              * (su + Real.sqrt (dirichletP v + massP v))
            ≤ Real.sqrt ε * (su + Real.sqrt (dirichletP v + massP v)) :=
              mul_le_mul_of_nonneg_right hse (by positivity)
          _ ≤ Real.sqrt ε * (su + (su + Real.sqrt ε)) :=
              mul_le_mul_of_nonneg_left h2b hse_nonneg
          _ = Real.sqrt ε * (2 * su + Real.sqrt ε) := by ring
      calc |td₁.bd u u - td₁.bd v v|
          ≤ C₁ * Real.sqrt (dirichletP (u - v) + massP (u - v))
              * (su + Real.sqrt (dirichletP v + massP v)) := h1
        _ = C₁ * (Real.sqrt (dirichletP (u - v) + massP (u - v))
              * (su + Real.sqrt (dirichletP v + massP v))) := by ring
        _ ≤ C₁ * (Real.sqrt ε * (2 * su + Real.sqrt ε)) :=
              mul_le_mul_of_nonneg_left h2 hC₁0
        _ = C₁ * Real.sqrt ε * (2 * su + Real.sqrt ε) := by ring
    have hb2 : |td₂.bd u u - td₂.bd v v| ≤ C₂ * Real.sqrt ε * (2 * su + Real.sqrt ε) := by
      have h1 := bd_sub_le_tu td₂ hC₂0 hC₂ u v
      have h2 : Real.sqrt (dirichletP (u - v) + massP (u - v))
            * (su + Real.sqrt (dirichletP v + massP v))
          ≤ Real.sqrt ε * (2 * su + Real.sqrt ε) := by
        have h2b : su + Real.sqrt (dirichletP v + massP v) ≤ su + (su + Real.sqrt ε) := by
          linarith [hsv]
        calc Real.sqrt (dirichletP (u - v) + massP (u - v))
              * (su + Real.sqrt (dirichletP v + massP v))
            ≤ Real.sqrt ε * (su + Real.sqrt (dirichletP v + massP v)) :=
              mul_le_mul_of_nonneg_right hse (by positivity)
          _ ≤ Real.sqrt ε * (su + (su + Real.sqrt ε)) :=
              mul_le_mul_of_nonneg_left h2b hse_nonneg
          _ = Real.sqrt ε * (2 * su + Real.sqrt ε) := by ring
      calc |td₂.bd u u - td₂.bd v v|
          ≤ C₂ * Real.sqrt (dirichletP (u - v) + massP (u - v))
              * (su + Real.sqrt (dirichletP v + massP v)) := h1
        _ = C₂ * (Real.sqrt (dirichletP (u - v) + massP (u - v))
              * (su + Real.sqrt (dirichletP v + massP v))) := by ring
        _ ≤ C₂ * (Real.sqrt ε * (2 * su + Real.sqrt ε)) :=
              mul_le_mul_of_nonneg_left h2 hC₂0
        _ = C₂ * Real.sqrt ε * (2 * su + Real.sqrt ε) := by ring
    have hdiff : td₁.bd u u - td₂.bd u u
        = (td₁.bd u u - td₁.bd v v) - (td₂.bd u u - td₂.bd v v) := by
      rw [hmid]; ring
    calc |td₁.bd u u - td₂.bd u u|
        = |(td₁.bd u u - td₁.bd v v) - (td₂.bd u u - td₂.bd v v)| := by rw [hdiff]
      _ ≤ |td₁.bd u u - td₁.bd v v| + |td₂.bd u u - td₂.bd v v| := abs_sub_le_tu _ _
      _ ≤ C₁ * Real.sqrt ε * (2 * su + Real.sqrt ε) + C₂ * Real.sqrt ε * (2 * su + Real.sqrt ε) :=
          add_le_add hb1 hb2
      _ = (C₁ + C₂) * Real.sqrt ε * (2 * su + Real.sqrt ε) := by ring
      _ ≤ (C₁ + C₂) * Real.sqrt ε * (2 * su + 1) := by
          have hCC0 : 0 ≤ (C₁ + C₂) * Real.sqrt ε := mul_nonneg (add_nonneg hC₁0 hC₂0) hse_nonneg
          have hse1 : Real.sqrt ε ≤ 1 := by
            calc Real.sqrt ε ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hε1
              _ = 1 := Real.sqrt_one
          have hab : 2 * su + Real.sqrt ε ≤ 2 * su + 1 := by linarith
          exact mul_le_mul_of_nonneg_left hab hCC0
      _ = (C₁ + C₂) * (2 * su + 1) * Real.sqrt ε := by ring
  linarith [key]

/-- **Uniqueness of the boundary form.**  Any two `TraceData` records agree on `bd`, granted
`C1Dense_tu`.  Diagonal case: `bd_diag_unique_tu`; general case: polarisation
`bd u v = (bd (u+v) (u+v) − bd u u − bd v v) / 2`, applied with both `td₁` and `td₂`. -/
theorem bd_unique_tu (hd : C1Dense_tu Cm Cp L R) (td₁ td₂ : TraceData Cm Cp L R)
    (u v : H1P (thinDomain Cm Cp L R)) : td₁.bd u v = td₂.bd u v := by
  have hpol₁ : td₁.bd (u + v) (u + v) = td₁.bd u u + 2 * td₁.bd u v + td₁.bd v v :=
    RobinCaps.Compact.bilin_add_add td₁.bd_symm u v
  have hpol₂ : td₂.bd (u + v) (u + v) = td₂.bd u u + 2 * td₂.bd u v + td₂.bd v v :=
    RobinCaps.Compact.bilin_add_add td₂.bd_symm u v
  have he1 : td₁.bd (u + v) (u + v) = td₂.bd (u + v) (u + v) := bd_diag_unique_tu hd td₁ td₂ (u + v)
  have he2 : td₁.bd u u = td₂.bd u u := bd_diag_unique_tu hd td₁ td₂ u
  have he3 : td₁.bd v v = td₂.bd v v := bd_diag_unique_tu hd td₁ td₂ v
  have : 2 * td₁.bd u v = 2 * td₂.bd u v := by
    rw [he1, he2, he3] at hpol₁
    linarith [hpol₁, hpol₂]
  linarith [this]

/-! ## Part 3: eigenvalue invariance -/

/-- **The Robin form on the quotient does not depend on the trace data**, granted
`C1Dense_tu`: `robinFormPQ` for `td₁.bd` and `td₂.bd` agree pointwise.  Route: unfold to the
representative `u` (`Submodule.Quotient.mk_surjective`) and apply `bd_diag_unique_tu`. -/
theorem robinFormPQ_congr_tu (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hd : C1Dense_tu Cm Cp L R) (td₁ td₂ : TraceData Cm Cp L R)
    (α : ℝ) (w : H1PQ (thinDomain Cm Cp L R)) :
    robinFormPQ (isOpen_thinDomain hR hL) td₁.bd td₁.vanishesOnNullAEP α w
      = robinFormPQ (isOpen_thinDomain hR hL) td₂.bd td₂.vanishesOnNullAEP α w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) w
  rw [robinFormPQ_mk, robinFormPQ_mk, bd_diag_unique_tu hd td₁ td₂ u]

/-- **Eigenvalue invariance.**  `lambdaThin` does not depend on which `TraceData` is used,
granted `C1Dense_tu`. -/
theorem lambdaThin_congr_tu (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (hd : C1Dense_tu Cm Cp L R) (td₁ td₂ : TraceData Cm Cp L R) (α : ℝ) (j : ℕ) :
    lambdaThin hR hL td₁ α j = lambdaThin hR hL td₂ α j := by
  unfold lambdaThin lambdaPQ
  have hfun : robinFormPQ (isOpen_thinDomain hR hL) td₁.bd td₁.vanishesOnNullAEP α
      = robinFormPQ (isOpen_thinDomain hR hL) td₂.bd td₂.vanishesOnNullAEP α :=
    funext (robinFormPQ_congr_tu hR hL hd td₁ td₂ α)
  rw [hfun]

/-! ## Part 4: `thm:main`/`cor:counterexample` transport to every recorded trace family -/

/-- **`thm:main` transports across recorded trace families.**  If `MainTheorem` holds for one
`TraceFamily`, it holds for every `TraceFamily`, granted `C1Dense_tu` on the admissible range of
radii.  This is immediate from `lambdaThin_congr_tu`: `MainTheorem` only mentions `lambdaThin`,
which does not depend on the trace data. -/
theorem mainTheorem_of_any_traceFamily_tu {L α : ℝ} {hL0 : 0 < L}
    {hβm : 0 < Cm.beta α} {hβp : 0 < Cp.beta α} {nu' : ℝ → ℝ} {R₀ : ℝ}
    (hd : ∀ (R : ℝ) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L), C1Dense_tu Cm Cp L R)
    (tdf tdf' : TraceFamily Cm Cp L R₀) :
    MainTheorem m Cm Cp L α hL0 hβm hβp nu' R₀ tdf →
      MainTheorem m Cm Cp L α hL0 hβm hβp nu' R₀ tdf' := by
  intro hmain J
  obtain ⟨C, R₁, hC, hR₁, hR₁le, hbound⟩ := hmain J
  refine ⟨C, R₁, hC, hR₁, hR₁le, ?_⟩
  intro R hR hR₀' hR₁' hLR j hj hjJ
  rw [← lambdaThin_congr_tu hR hLR (hd R hR hLR) (tdf R hR hR₀') (tdf' R hR hR₀') α j]
  exact hbound R hR hR₀' hR₁' hLR j hj hjJ

/-- **`thm:main` for every recorded trace family of the hemispherical capsule.** -/
theorem mainTheorem_hemisphere_any_tu (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α)
    (hd : ∀ (R : ℝ) (hR : 0 < R) (hL : (hemisphere m).K * 2 * R < L),
      C1Dense_tu (hemisphere m) (hemisphere m) L R) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2, ∃ nu' : ℝ → ℝ,
      ∀ tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀,
        MainTheorem m (hemisphere m) (hemisphere m) L α hL0
          (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf := by
  obtain ⟨R₀, hR₀, hR₀L, nu', tdf₀, hmain⟩ := mainTheorem_hemisphere_gen_final m hm L α hL0 hα
  refine ⟨R₀, hR₀, hR₀L, nu', fun tdf => ?_⟩
  refine mainTheorem_of_any_traceFamily_tu (fun R hR hLR => ?_) tdf₀ tdf hmain
  have hLR' : (hemisphere m).K * 2 * R < L := by
    have : (hemisphere m).K + (hemisphere m).K = (hemisphere m).K * 2 := by ring
    rwa [this] at hLR
  exact hd R hR hLR'

/-- **`cor:counterexample` for every recorded trace family of the hemispherical capsule.** -/
theorem counterexample_hemisphere_any_tu (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α)
    (hd : ∀ (R : ℝ) (hR : 0 < R) (hL : (hemisphere m).K * 2 * R < L),
      C1Dense_tu (hemisphere m) (hemisphere m) L R) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      ∀ tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L) (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (hemisphere m) (hemisphere m) L R) = L := by
  obtain ⟨R₀, hR₀, hR₀L, nu', hallmain⟩ := mainTheorem_hemisphere_any_tu m hm L α hL0 hα hd
  refine ⟨R₀, hR₀, hR₀L, fun tdf => ?_⟩
  exact counterexample_of_mainTheorem' m hm L α hL0 hα nu' R₀ hR₀ tdf (hallmain tdf)

/-- **`thm:main` for every recorded trace family of the single-cap thin domain** (flat left end,
hemispherical right cap). -/
theorem mainTheorem_single_any_tu (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α)
    (hd : ∀ (R : ℝ) (hR : 0 < R) (hL : ((Cap.flat m K hK).K + (hemisphere m).K) * R < L),
      C1Dense_tu (Cap.flat m K hK) (hemisphere m) L R) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∀ tdf : TraceFamily (Cap.flat m K hK) (hemisphere m) L R₀,
        MainTheorem m (Cap.flat m K hK) (hemisphere m) L α hL0
          (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf := by
  obtain ⟨R₀, hR₀, hR₀L, nu', tdf₀, hmain⟩ :=
    mainTheorem_single_final m hm K hK L α hL0 hα
  refine ⟨R₀, hR₀, hR₀L, nu', fun tdf => ?_⟩
  exact mainTheorem_of_any_traceFamily_tu hd tdf₀ tdf hmain

end RobinCaps.ThinDomain

end
