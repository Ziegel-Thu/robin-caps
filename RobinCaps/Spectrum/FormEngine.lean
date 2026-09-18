import Mathlib
import RobinCaps.Spectrum.Engine

/-!
# The abstract form-based min–max spectral engine (U-SPEC-3)

`RobinCaps.Spectrum.Engine` formalizes the min–max values `lambda T j` of a
*continuous linear operator* `T`.  The manuscript (`sec:proof`) instead works
with two *forms*: an energy form `q` (written `E_R` there) and a *mass* `N_R`,
which is **not** the Hilbert norm but is only compared with the energy through
`N_R ≤ b[F] + Z`.  For such a pair the operator Rayleigh quotient
`⟪T u, u⟫ / ‖u‖²` is not available; the relevant quotient is `q u / b u`.

This file builds the corresponding **form engine**: for a real vector space `H`
and functions `q b : H → ℝ` (with `b` positive on nonzero vectors) we define

`minmax q b j = ⨅ V (hV : finrank ℝ V = j), ⨆ u : {u : V // u ≠ 0}, q u / b u`,

and prove the three order-theoretic steps used in the proof:

* `minmax_mono` — monotonicity in `q`;
* `minmax_le_of_trial` — a trial space on which `q ≤ t · b` gives
  `minmax q b j ≤ t`;
* `le_minmax_of_codim` — a codimension-`(j-1)` constraint on which
  `t · b ≤ q` gives `t ≤ minmax q b j`.

The operator engine is recovered in the last section by taking
`q u = ⟪T u, u⟫_ℝ` and `b u = ‖u‖ ^ 2` (`minmax_rayleigh`), together with the
fact that the boundedness hypotheses used below are then automatic
(`bddAboveRatio_inner`, `bddBelowRatio_inner`).

## Boundedness

As in `Engine.lean` the defining object is an indexed `iInf` of indexed `iSup`s,
and mathlib's `ciInf_*`/`ciSup_*` lemmas for a *conditionally* complete lattice
require boundedness side conditions.  In `Engine.lean` these were free because
`T` is continuous (`-‖T‖ ≤ rayleigh T u ≤ ‖T‖`).  For arbitrary forms they are
not, and we add them as explicit hypotheses:

* `BddAboveRatio q b` — `∃ C ≥ 0, ∀ u ≠ 0, q u / b u ≤ C`;
* `BddBelowRatio q b` — `∃ c ≤ 0, ∀ u ≠ 0, c ≤ q u / b u`.

The signs are chosen so that the empty-index cases (`iSup` over the nonzero
vectors of the zero subspace, or `iInf` over no `j`-dimensional subspaces) are
handled by the same constants: lowering an upper bound to `≥ 0` or raising a
lower bound to `≤ 0` never loses generality.  The hypotheses are *not* needed
for the definition of `minmax`, only for the order-theoretic lemmas.

Everything below is proved without `sorry`, `axiom` or `admit`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped InnerProductSpace RealInnerProductSpace

namespace RobinCaps.Spectrum

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The **form min–max value**

`minmax q b j = ⨅ V (hV : finrank ℝ V = j), ⨆ u : {u : V // u ≠ 0}, q u / b u`.

The infimum runs over the `j`-dimensional linear subspaces `V ≤ H` and the
supremum over the nonzero vectors of `V`; `b` is intended to be positive on
nonzero vectors, so that the quotient is the natural "energy divided by mass". -/
def minmax (q b : H → ℝ) (j : ℕ) : ℝ :=
  ⨅ V : {V : Submodule ℝ H // Module.finrank ℝ V = j},
    ⨆ u : {u : V.1 // u ≠ 0}, q ((u : V.1) : H) / b ((u : V.1) : H)

/-- `q / b` is bounded above by a nonnegative constant.  The sign condition on
the constant is harmless (an upper bound can always be enlarged to a
nonnegative one) and lets the empty-index case of the inner `iSup` (`0`) be
bounded by the same constant. -/
def BddAboveRatio (q b : H → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H, u ≠ 0 → q u / b u ≤ C

/-- `q / b` is bounded below by a nonpositive constant.  As for
`BddAboveRatio`, the sign condition is harmless and handles empty index sets. -/
def BddBelowRatio (q b : H → ℝ) : Prop :=
  ∃ c : ℝ, c ≤ 0 ∧ ∀ u : H, u ≠ 0 → c ≤ q u / b u

/-! ### Transfer of the ratio bounds -/

/-- An upper ratio bound transfers from `q₂` to a pointwise smaller `q₁`
(needs `b > 0` on nonzero vectors). -/
theorem BddAboveRatio_mono {q₁ q₂ b : H → ℝ} (hq : ∀ u, q₁ u ≤ q₂ u)
    (hb : ∀ u, u ≠ 0 → 0 < b u) (h : BddAboveRatio q₂ b) : BddAboveRatio q₁ b := by
  obtain ⟨C, hC0, hC⟩ := h
  exact ⟨C, hC0, fun u hu =>
    le_trans (div_le_div_of_nonneg_right (hq u) (le_of_lt (hb u hu))) (hC u hu)⟩

/-- A lower ratio bound transfers from a pointwise smaller `q₁` to `q₂`
(needs `b > 0` on nonzero vectors). -/
theorem BddBelowRatio_mono {q₁ q₂ b : H → ℝ} (hq : ∀ u, q₁ u ≤ q₂ u)
    (hb : ∀ u, u ≠ 0 → 0 < b u) (h : BddBelowRatio q₁ b) : BddBelowRatio q₂ b := by
  obtain ⟨c, hc0, hc⟩ := h
  exact ⟨c, hc0, fun u hu =>
    le_trans (hc u hu) (div_le_div_of_nonneg_right (hq u) (le_of_lt (hb u hu)))⟩

/-! ### Boundedness of the inner suprema and of the outer family -/

/-- The range of `u ↦ q u / b u` restricted to a family of nonzero vectors is
bounded above whenever `BddAboveRatio q b` holds. -/
theorem bddAbove_range_div (q b : H → ℝ) (h : BddAboveRatio q b) {ι : Type*}
    (f : ι → H) (hf : ∀ i, f i ≠ 0) :
    BddAbove (Set.range fun i => q (f i) / b (f i)) := by
  obtain ⟨C, _, hC⟩ := h
  exact ⟨C, by rintro y ⟨i, rfl⟩; exact hC (f i) (hf i)⟩

/-- The range of `u ↦ q u / b u` restricted to a family of nonzero vectors is
bounded below whenever `BddBelowRatio q b` holds. -/
theorem bddBelow_range_div (q b : H → ℝ) (h : BddBelowRatio q b) {ι : Type*}
    (f : ι → H) (hf : ∀ i, f i ≠ 0) :
    BddBelow (Set.range fun i => q (f i) / b (f i)) := by
  obtain ⟨c, _, hc⟩ := h
  exact ⟨c, by rintro y ⟨i, rfl⟩; exact hc (f i) (hf i)⟩

/-- The outer family `V ↦ ⨆ u ∈ V∖{0}, q u / b u` is bounded below.  The empty
cases (zero subspace, or no `j`-dimensional subspace at all) are covered by the
sign convention in `BddBelowRatio` and `BddAboveRatio`; the nonempty case uses
`le_ciSup`, which is where `BddAboveRatio` is needed. -/
theorem bddBelow_range_minmaxFamily (q b : H → ℝ) (hA : BddAboveRatio q b)
    (hB : BddBelowRatio q b) (j : ℕ) :
    BddBelow (Set.range fun V : {V : Submodule ℝ H // Module.finrank ℝ V = j} =>
      ⨆ u : {u : V.1 // u ≠ 0}, q ((u : V.1) : H) / b ((u : V.1) : H)) := by
  obtain ⟨c, hc0, hc⟩ := hB
  refine ⟨c, ?_⟩
  rintro y ⟨V, rfl⟩
  change c ≤ ⨆ u : {u : V.1 // u ≠ 0}, q ((u : V.1) : H) / b ((u : V.1) : H)
  rcases isEmpty_or_nonempty {u : V.1 // u ≠ 0} with hempty | hne
  · haveI := hempty
    rw [iSup_of_empty']
    simpa using hc0
  · have hbdd : BddAbove (Set.range fun u : {u : V.1 // u ≠ 0} =>
        q ((u : V.1) : H) / b ((u : V.1) : H)) :=
      bddAbove_range_div q b hA (fun u : {u : V.1 // u ≠ 0} => ((u : V.1) : H))
        (fun u => fun hh => u.2 (Subtype.ext hh))
    exact le_trans (hc _ (fun hh => hne.some.2 (Subtype.ext hh)))
      (le_ciSup hbdd hne.some)

/-! ### Monotonicity in the form -/

/-- **Monotonicity of the min–max values in the form.**  If `q₁ ≤ q₂` pointwise
and `b` is positive on nonzero vectors, then `minmax q₁ b j ≤ minmax q₂ b j`.

Only an upper bound for the larger form `q₂` and a lower bound for the smaller
form `q₁` are needed (the missing bounds follow by monotonicity). -/
theorem minmax_mono {q₁ q₂ b : H → ℝ} (h : ∀ u, q₁ u ≤ q₂ u)
    (hb : ∀ u, u ≠ 0 → 0 < b u) (hA : BddAboveRatio q₂ b) (hB : BddBelowRatio q₁ b)
    (j : ℕ) : minmax q₁ b j ≤ minmax q₂ b j := by
  have hA₁ : BddAboveRatio q₁ b := BddAboveRatio_mono h hb hA
  unfold minmax
  apply ciInf_mono (bddBelow_range_minmaxFamily q₁ b hA₁ hB j)
  intro V
  apply ciSup_mono
    (bddAbove_range_div q₂ b hA (fun u : {u : V.1 // u ≠ 0} => ((u : V.1) : H))
      (fun u => fun hh => u.2 (Subtype.ext hh)))
  intro u
  exact div_le_div_of_nonneg_right (h _)
    (le_of_lt (hb _ (fun hh => u.2 (Subtype.ext hh))))

/-! ### Trial (upper bound) direction -/

/-- **Trial-space upper bound.**  If `W` is a `j`-dimensional subspace
(`j > 0`) on which `q ≤ t · b`, then `minmax q b j ≤ t`. -/
theorem minmax_le_of_trial (q b : H → ℝ) (j : ℕ) (hj : 0 < j)
    (hb : ∀ u, u ≠ 0 → 0 < b u) (hA : BddAboveRatio q b) (hB : BddBelowRatio q b)
    (W : Submodule ℝ H) (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ u ∈ W, u ≠ 0 → q u ≤ t * b u) : minmax q b j ≤ t := by
  have hfin : 0 < Module.finrank ℝ W := by rw [hW]; exact hj
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hfin
  haveI : Nonempty {u : W // u ≠ 0} := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact ⟨⟨w, hw⟩⟩
  unfold minmax
  refine ciInf_le_of_le (bddBelow_range_minmaxFamily q b hA hB j) ⟨W, hW⟩ ?_
  apply ciSup_le
  intro u
  have huW : ((u : W) : H) ∈ W := (u : W).2
  have hune : ((u : W) : H) ≠ 0 := fun hh => u.2 (Subtype.ext hh)
  rw [div_le_iff₀ (hb _ hune)]
  exact h _ huW hune

/-! ### Finite-codimension (lower bound) direction -/

/-- **Finite-codimension lower bound.**  Let `φ : H →ₗ[ℝ] (Fin (j-1) → ℝ)` have
`(j-1)`-dimensional range and suppose `t · b ≤ q` on `ker φ`.  Then
`t ≤ minmax q b j`.

As in `Engine.lower_of_codim`, the hypothesis `hex` (existence of a
`j`-dimensional subspace) is needed because the infimum defining `minmax q b j`
runs over a possibly empty index type. -/
theorem le_minmax_of_codim (q b : H → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hb : ∀ u, u ≠ 0 → 0 < b u) (hA : BddAboveRatio q b)
    (φ : H →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1) (t : ℝ)
    (h : ∀ u : H, u ≠ 0 → φ u = 0 → t * b u ≤ q u)
    (hex : ∃ V : Submodule ℝ H, Module.finrank ℝ V = j) :
    t ≤ minmax q b j := by
  haveI : Nonempty {V : Submodule ℝ H // Module.finrank ℝ V = j} := by
    obtain ⟨V, hV⟩ := hex
    exact ⟨⟨V, hV⟩⟩
  unfold minmax
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
  have hlow : t ≤ q ((w.1 : W) : H) / b ((w.1 : W) : H) := by
    rw [le_div_iff₀ (hb _ hwHne)]
    exact h ((w.1 : W) : H) hwHne hphi
  exact le_trans hlow
    (le_ciSup
      (bddAbove_range_div q b hA (fun u : {u : W // u ≠ 0} => ((u : W) : H))
        (fun u => fun hh => u.2 (Subtype.ext hh)))
      ⟨w.1, hwne⟩)

/-! ### Recovering the operator engine

For `q u = ⟪T u, u⟫_ℝ` and `b u = ‖u‖ ^ 2` the form quotient is literally the
Rayleigh quotient of `Engine.lean`, so `minmax` is `lambda`; moreover the ratio
bounds required by the form engine are then automatic, with constants
`±‖T‖`. -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The operator engine is the form engine at `b u = ‖u‖²`.** -/
theorem minmax_rayleigh (T : H →L[ℝ] H) (j : ℕ) :
    minmax (fun u => ⟪T u, u⟫_ℝ) (fun u => ‖u‖ ^ 2) j = lambda T j := by
  unfold minmax lambda rayleigh
  rfl

/-- The upper ratio bound needed by the form engine is automatic for an
operator form, with constant `‖T‖`. -/
theorem bddAboveRatio_inner (T : H →L[ℝ] H) :
    BddAboveRatio (fun u => ⟪T u, u⟫_ℝ) (fun u => ‖u‖ ^ 2) :=
  ⟨‖T‖, norm_nonneg T, fun u _ => by
    simpa only [rayleigh] using rayleigh_le_opNorm T u⟩

/-- The lower ratio bound needed by the form engine is automatic for an
operator form, with constant `-‖T‖`. -/
theorem bddBelowRatio_inner (T : H →L[ℝ] H) :
    BddBelowRatio (fun u => ⟪T u, u⟫_ℝ) (fun u => ‖u‖ ^ 2) :=
  ⟨-‖T‖, neg_nonpos.mpr (norm_nonneg T), fun u _ => by
    simpa only [rayleigh] using neg_opNorm_le_rayleigh T u⟩

/-- `Engine.lambda_mono` recovered from `minmax_mono`. -/
theorem lambda_mono_via_minmax (T₁ T₂ : H →L[ℝ] H)
    (h : ∀ u, ⟪T₁ u, u⟫_ℝ ≤ ⟪T₂ u, u⟫_ℝ) (j : ℕ) :
    lambda T₁ j ≤ lambda T₂ j := by
  rw [← minmax_rayleigh T₁ j, ← minmax_rayleigh T₂ j]
  exact minmax_mono h (fun u hu => pow_pos (norm_pos_iff.mpr hu) 2)
    (bddAboveRatio_inner T₂) (bddBelowRatio_inner T₁) j

/-- `Engine.trial_upper` recovered from `minmax_le_of_trial`. -/
theorem trial_upper_via_minmax (T : H →L[ℝ] H) (j : ℕ) (hj : 0 < j)
    (W : Submodule ℝ H) (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ u ∈ W, u ≠ 0 → ⟪T u, u⟫_ℝ ≤ t * ‖u‖ ^ 2) :
    lambda T j ≤ t := by
  rw [← minmax_rayleigh T j]
  exact minmax_le_of_trial (fun u => ⟪T u, u⟫_ℝ) (fun u => ‖u‖ ^ 2) j hj
    (fun u hu => pow_pos (norm_pos_iff.mpr hu) 2)
    (bddAboveRatio_inner T) (bddBelowRatio_inner T) W hW t h

/-- `Engine.lower_of_codim` recovered from `le_minmax_of_codim`. -/
theorem lower_of_codim_via_minmax (T : H →L[ℝ] H) (j : ℕ) (hj : 1 ≤ j)
    (φ : H →ₗ[ℝ] (Fin (j - 1) → ℝ))
    (hφ : Module.finrank ℝ (LinearMap.range φ) = j - 1) (t : ℝ)
    (h : ∀ u : H, u ≠ 0 → φ u = 0 → t * ‖u‖ ^ 2 ≤ ⟪T u, u⟫_ℝ)
    (hex : ∃ V : Submodule ℝ H, Module.finrank ℝ V = j) :
    t ≤ lambda T j := by
  rw [← minmax_rayleigh T j]
  exact le_minmax_of_codim (fun u => ⟪T u, u⟫_ℝ) (fun u => ‖u‖ ^ 2) j hj
    (fun u hu => pow_pos (norm_pos_iff.mpr hu) 2) (bddAboveRatio_inner T)
    φ hφ t h hex

end Hilbert

end RobinCaps.Spectrum
