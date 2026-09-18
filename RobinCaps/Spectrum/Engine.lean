import Mathlib

/-!
# The abstract variational (min–max) spectral engine

This file is the abstract, purely Hilbert/order-theoretic core of the
manuscript's min–max construction (the engine used in `sec:proof`).  It contains
no Sobolev theory: the concrete realization (`robinForm`, traces, the space
`H¹`, …) is supplied separately (interface §6).

## Formulation choice

For a bounded linear operator `T : H →L[ℝ] H` on a real inner product space we
define the Rayleigh quotient

`rayleigh T u = ⟪T u, u⟫_ℝ / ‖u‖ ^ 2`

and the `j`-th variational value as an *indexed* infimum of indexed suprema

`lambda T j = ⨅ V (hV : finrank ℝ V = j), ⨆ u : {u : V // u ≠ 0}, rayleigh T u`.

We use `iInf`/`iSup` (rather than `sInf`/`sSup` over explicit sets) because the
indexed lemmas `ciInf_mono`, `ciInf_le`, `le_ciInf`, `ciSup_le`, `le_ciSup` give
exactly the monotonicity/trial/lower-bound steps needed below.  Boundedness is
automatic here: since `T` is a *continuous* linear map,

`-‖T‖ ≤ rayleigh T u ≤ ‖T‖` for every `u`,

so all relevant infima/suprema are bounded (`bddAbove_range_rayleigh`,
`bddBelow_range_rayleigh`).

Self-adjointness of `T` is *not* needed for the order-theoretic facts proved
here (indeed `rayleigh` is real-valued on a real space regardless); it only
enters when identifying `lambda T j` with the `j`-th eigenvalue, which is the
job of the realization bridge.  The notions below are therefore stated for an
arbitrary continuous linear `T`.

## Contents

* `rayleigh_smul`, `rayleigh_pos`, `rayleigh_nonneg` — elementary invariance and
  positivity;
* bounds `rayleigh_le_opNorm`, `neg_opNorm_le_rayleigh`;
* `lambda_mono` — `⟪T₁u,u⟫ ≤ ⟪T₂u,u⟫` pointwise implies `lambda T₁ j ≤ lambda T₂ j`;
* `trial_upper` — a `j`-dimensional trial space with form bounded by
  `t * ‖·‖²` gives `lambda T j ≤ t`;
* `lower_of_codim` — a codimension-`(j-1)` constraint along which the form is
  bounded below by `t * ‖·‖²` gives `t ≤ lambda T j`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped InnerProductSpace RealInnerProductSpace

namespace RobinCaps.Spectrum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The **Rayleigh quotient** of `T` at `u`, `⟪T u, u⟫_ℝ / ‖u‖ ^ 2`.
At `u = 0` this is `0 / 0 = 0` by the conventions of division by zero. -/
def rayleigh (T : H →L[ℝ] H) (u : H) : ℝ :=
  ⟪T u, u⟫_ℝ / ‖u‖ ^ 2

/-- The **`j`-th variational (min–max) value** of `T`:

`lambda T j = ⨅ V (hV : finrank ℝ V = j), ⨆ u : {u : V // u ≠ 0}, rayleigh T u`.

The infimum runs over the `j`-dimensional linear subspaces `V ≤ H` and the
supremum over the nonzero vectors of `V`. -/
def lambda (T : H →L[ℝ] H) (j : ℕ) : ℝ :=
  ⨅ V : {V : Submodule ℝ H // Module.finrank ℝ V = j},
    ⨆ u : {u : V.1 // u ≠ 0}, rayleigh T ((u : V.1) : H)

/-! ### Elementary properties of the Rayleigh quotient -/

/-- **Scaling invariance** of the Rayleigh quotient: `rayleigh T (c • u) = rayleigh T u`
for `c ≠ 0`. -/
theorem rayleigh_smul (T : H →L[ℝ] H) (c : ℝ) (hc : c ≠ 0) (u : H) :
    rayleigh T (c • u) = rayleigh T u := by
  have hnum : ⟪T (c • u), c • u⟫_ℝ = c ^ 2 * ⟪T u, u⟫_ℝ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  have hden : ‖c • u‖ ^ 2 = c ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [rayleigh, hnum, hden, rayleigh]
  rw [show c ^ 2 * ⟪T u, u⟫_ℝ = c * (c * ⟪T u, u⟫_ℝ) by ring,
    show c ^ 2 * ‖u‖ ^ 2 = c * (c * ‖u‖ ^ 2) by ring]
  rw [mul_div_mul_left (c * ⟪T u, u⟫_ℝ) (c * ‖u‖ ^ 2) hc]
  rw [mul_div_mul_left ⟪T u, u⟫_ℝ (‖u‖ ^ 2) hc]

/-- **Positivity** of the Rayleigh quotient at a nonzero vector where the form is
positive. -/
theorem rayleigh_pos (T : H →L[ℝ] H) (u : H) (hu : u ≠ 0)
    (h : 0 < ⟪T u, u⟫_ℝ) : 0 < rayleigh T u := by
  rw [rayleigh]
  exact div_pos h (pow_pos (norm_pos_iff.mpr hu) 2)

/-- **Nonnegativity** of the Rayleigh quotient at a nonzero vector where the form
is nonnegative. -/
theorem rayleigh_nonneg (T : H →L[ℝ] H) (u : H)
    (h : 0 ≤ ⟪T u, u⟫_ℝ) : 0 ≤ rayleigh T u := by
  rw [rayleigh]
  exact div_nonneg h (sq_nonneg _)

/-! ### Uniform bounds on the Rayleigh quotient -/

/-- The quadratic form of a continuous `T` is bounded above by `‖T‖ ‖u‖²`. -/
theorem inner_T_le (T : H →L[ℝ] H) (u : H) :
    ⟪T u, u⟫_ℝ ≤ ‖T‖ * ‖u‖ ^ 2 := by
  have h := real_inner_le_norm (T u) u
  have h' : ‖T u‖ * ‖u‖ ≤ ‖T‖ * ‖u‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right (T.le_opNorm u) (norm_nonneg u)
    calc ‖T u‖ * ‖u‖ ≤ (‖T‖ * ‖u‖) * ‖u‖ := hmul
      _ = ‖T‖ * ‖u‖ ^ 2 := by ring
  linarith

/-- The quadratic form of a continuous `T` is bounded below by `-‖T‖ ‖u‖²`. -/
theorem neg_opNorm_mul_sq_le_inner (T : H →L[ℝ] H) (u : H) :
    -‖T‖ * ‖u‖ ^ 2 ≤ ⟪T u, u⟫_ℝ := by
  have h := abs_real_inner_le_norm (T u) u
  have h' : ‖T u‖ * ‖u‖ ≤ ‖T‖ * ‖u‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right (T.le_opNorm u) (norm_nonneg u)
    calc ‖T u‖ * ‖u‖ ≤ (‖T‖ * ‖u‖) * ‖u‖ := hmul
      _ = ‖T‖ * ‖u‖ ^ 2 := by ring
  have habs : -(‖T‖ * ‖u‖ ^ 2) ≤ ⟪T u, u⟫_ℝ :=
    (abs_le.mp (le_trans h h')).1
  have heq : -(‖T‖ * ‖u‖ ^ 2) = -‖T‖ * ‖u‖ ^ 2 := by ring
  rwa [heq] at habs

/-- Uniform upper bound `rayleigh T u ≤ ‖T‖`. -/
theorem rayleigh_le_opNorm (T : H →L[ℝ] H) (u : H) : rayleigh T u ≤ ‖T‖ := by
  rw [rayleigh]
  rcases eq_or_lt_of_le (sq_nonneg ‖u‖ : (0 : ℝ) ≤ ‖u‖ ^ 2) with h | h
  · rw [← h, div_zero]; exact norm_nonneg T
  · rw [div_le_iff₀ h]; exact inner_T_le T u

/-- Uniform lower bound `-‖T‖ ≤ rayleigh T u`. -/
theorem neg_opNorm_le_rayleigh (T : H →L[ℝ] H) (u : H) : -‖T‖ ≤ rayleigh T u := by
  rw [rayleigh]
  rcases eq_or_lt_of_le (sq_nonneg ‖u‖ : (0 : ℝ) ≤ ‖u‖ ^ 2) with h | h
  · rw [← h, div_zero]; exact neg_nonpos.mpr (norm_nonneg T)
  · rw [le_div_iff₀ h]; exact neg_opNorm_mul_sq_le_inner T u

/-- The range of `rayleigh T` is bounded above (uniformly, even for empty index
sets). -/
theorem bddAbove_range_rayleigh (T : H →L[ℝ] H) {ι : Type*} (f : ι → H) :
    BddAbove (Set.range fun i => rayleigh T (f i)) :=
  ⟨‖T‖, by rintro y ⟨i, rfl⟩; exact rayleigh_le_opNorm T (f i)⟩

/-- The range of `rayleigh T` is bounded below (uniformly, even for empty index
sets). -/
theorem bddBelow_range_rayleigh (T : H →L[ℝ] H) {ι : Type*} (f : ι → H) :
    BddBelow (Set.range fun i => rayleigh T (f i)) :=
  ⟨-‖T‖, by rintro y ⟨i, rfl⟩; exact neg_opNorm_le_rayleigh T (f i)⟩

/-- `-‖T‖` is a lower bound for the supremum of `rayleigh T` over the nonzero
vectors of any subspace `V` (the case `V = ⊥`, where the index is empty, uses
`sSup ∅ = 0`). -/
theorem neg_opNorm_le_ciSup_rayleigh (T : H →L[ℝ] H) (V : Submodule ℝ H) :
    -‖T‖ ≤ ⨆ u : {u : V // u ≠ 0}, rayleigh T ((u : V) : H) := by
  rcases isEmpty_or_nonempty {u : V // u ≠ 0} with h | h
  · haveI := h
    rw [iSup_of_empty']
    simp
  · exact le_trans (neg_opNorm_le_rayleigh T _)
      (le_ciSup
        (bddAbove_range_rayleigh T (fun u : {u : V // u ≠ 0} => ((u : V) : H)))
        h.some)

/-! ### Monotonicity in the operator -/

/-- **Monotonicity of the min–max values in the operator.**  If the quadratic
form of `T₁` is pointwise bounded above by that of `T₂`, then `lambda T₁ j ≤
lambda T₂ j`. -/
theorem lambda_mono (T₁ T₂ : H →L[ℝ] H)
    (h : ∀ u, ⟪T₁ u, u⟫_ℝ ≤ ⟪T₂ u, u⟫_ℝ) (j : ℕ) :
    lambda T₁ j ≤ lambda T₂ j := by
  unfold lambda
  apply ciInf_mono
  · exact ⟨-‖T₁‖, by rintro y ⟨V, rfl⟩; exact neg_opNorm_le_ciSup_rayleigh T₁ V.1⟩
  · intro V
    apply ciSup_mono
      (bddAbove_range_rayleigh T₂ (fun u : {u : V.1 // u ≠ 0} => ((u : V.1) : H)))
    intro u
    rw [rayleigh, rayleigh]
    exact div_le_div_of_nonneg_right (h ((u : V.1) : H)) (sq_nonneg _)

/-! ### Trial (upper bound) direction -/

/-- **Trial-space upper bound.**  If `W` is a `j`-dimensional subspace on which
the quadratic form is bounded above by `t ‖·‖²`, then `lambda T j ≤ t`. -/
theorem trial_upper (T : H →L[ℝ] H) (j : ℕ) (hj : 0 < j) (W : Submodule ℝ H)
    (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ u ∈ W, u ≠ 0 → ⟪T u, u⟫_ℝ ≤ t * ‖u‖ ^ 2) :
    lambda T j ≤ t := by
  have hfin : 0 < Module.finrank ℝ W := by rw [hW]; exact hj
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hfin
  haveI : Nonempty {u : W // u ≠ 0} := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact ⟨⟨w, hw⟩⟩
  unfold lambda
  refine ciInf_le_of_le
    (f := fun V : {V : Submodule ℝ H // Module.finrank ℝ V = j} =>
      ⨆ u : {u : V.1 // u ≠ 0}, rayleigh T ((u : V.1) : H)) ?_ ⟨W, hW⟩ ?_
  · exact ⟨-‖T‖, by rintro y ⟨V, rfl⟩; exact neg_opNorm_le_ciSup_rayleigh T V.1⟩
  · apply ciSup_le
    intro u
    have huW : ((u : W) : H) ∈ W := (u : W).2
    have hune : ((u : W) : H) ≠ 0 := fun hh => u.2 (Subtype.ext hh)
    rw [rayleigh, div_le_iff₀ (pow_pos (norm_pos_iff.mpr hune) 2)]
    exact h ((u : W) : H) huW hune

/-! ### Finite-codimension (lower bound) direction -/

/-- **Finite-codimension lower bound.**  Let `φ : H →ₗ[ℝ] (Fin (j-1) → ℝ)` have
`(j-1)`-dimensional range and suppose the quadratic form is bounded below by
`t ‖·‖²` on `ker φ`.  Then `t ≤ lambda T j`.

The hypothesis `hex` (existence of a `j`-dimensional subspace) is needed because
the infimum defining `lambda T j` is an infimum over a possibly empty index type;
in the intended application `H` is infinite-dimensional and `hex` is immediate.
For `j = 0` and a zero map this is exactly what one must assume, and the statement
is otherwise false. -/
theorem lower_of_codim (T : H →L[ℝ] H) (j : ℕ) (hj : 1 ≤ j)
    (φ : H →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1) (t : ℝ)
    (h : ∀ u : H, u ≠ 0 → φ u = 0 → t * ‖u‖ ^ 2 ≤ ⟪T u, u⟫_ℝ)
    (hex : ∃ V : Submodule ℝ H, Module.finrank ℝ V = j) :
    t ≤ lambda T j := by
  haveI : Nonempty {V : Submodule ℝ H // Module.finrank ℝ V = j} := by
    obtain ⟨V, hV⟩ := hex
    exact ⟨⟨V, hV⟩⟩
  unfold lambda
  apply le_ciInf
  intro V
  set W : Submodule ℝ H := V.1 with hWdef
  have hWfin : Module.finrank ℝ W = j := by rw [hWdef]; exact V.2
  haveI : FiniteDimensional ℝ W :=
    FiniteDimensional.of_finrank_pos (by rw [hWfin]; omega)
  let ψ : W →ₗ[ℝ] (Fin (j - 1) → ℝ) := φ.comp W.subtype
  have hrangeψ : LinearMap.range ψ = Submodule.map φ W := by
    change LinearMap.range (φ.comp W.subtype) = Submodule.map φ W
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hle : Module.finrank ℝ ↥(LinearMap.range ψ) ≤ j - 1 := by
    rw [hrangeψ]
    calc Module.finrank ℝ ↥(Submodule.map φ W)
        ≤ Module.finrank ℝ ↥(LinearMap.range φ) := by
          apply Submodule.finrank_mono
          rw [Submodule.map_le_iff_le_comap]
          intro x _
          exact ⟨x, rfl⟩
      _ = j - 1 := hφ
  have hker : 1 ≤ Module.finrank ℝ ↥(LinearMap.ker ψ) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker ψ
    have hle' : Module.finrank ℝ ↥(LinearMap.range ψ) ≤ Module.finrank ℝ W - 1 := by
      rw [hWfin]; exact hle
    omega
  haveI : Nontrivial ↥(LinearMap.ker ψ) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := ↥(LinearMap.ker ψ)) (by omega)
  obtain ⟨w, hwne0⟩ := exists_ne (0 : ↥(LinearMap.ker ψ))
  have hwne : w.1 ≠ (0 : W) := fun h0 => hwne0 (Subtype.ext h0)
  have hwker : w.1 ∈ LinearMap.ker ψ := w.2
  have hphi : φ ((w.1 : W) : H) = 0 := by
    have hmem := LinearMap.mem_ker.mp hwker
    simpa only [ψ, LinearMap.comp_apply, Submodule.subtype_apply] using hmem
  have hwHne : ((w.1 : W) : H) ≠ 0 := fun hh => hwne (Subtype.ext hh)
  have hlow : t ≤ rayleigh T ((w.1 : W) : H) := by
    rw [rayleigh, le_div_iff₀ (pow_pos (norm_pos_iff.mpr hwHne) 2)]
    exact h ((w.1 : W) : H) hwHne hphi
  exact le_trans hlow
    (le_ciSup
      (bddAbove_range_rayleigh T (fun u : {u : W // u ≠ 0} => ((u : W) : H)))
      ⟨w.1, hwne⟩)

/-! ### Self-adjoint operators -/

/-- For a self-adjoint operator the quadratic form is symmetric:
`⟪T u, v⟫_ℝ = ⟪u, T v⟫_ℝ`.  This is the only place self-adjointness appears; the
order-theoretic engine above does not need it (it only enters when identifying
`lambda T j` with the `j`-th eigenvalue). -/
theorem inner_selfAdjoint (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (u v : H) :
    ⟪T u, v⟫_ℝ = ⟪u, T v⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, hT.adjoint_eq]

end RobinCaps.Spectrum
