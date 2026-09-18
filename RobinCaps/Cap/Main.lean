import RobinCaps.Cap.FluxAC
import RobinCaps.Cap.Concave
import RobinCaps.Cap.Equality
import RobinCaps.Cap.Volume

/-!
# G-cap: the sharp end-cap inequality and its equality cases (assembly)

This file assembles the manuscript's Theorem `thm:calibration`
(`reference/robin_endcaps_corrected_en.tex`, lines 253–276) from the pieces

* `Cap.Concave.profileAC_of_cap` — every admissible profile (concave,
  non-increasing, `0 < θ ≤ 1`) is automatically weakly regular (`ProfileAC`);
* `Cap.sharp_revolutionF_of_profileAC` — the flux/calibration argument under
  `ProfileAC`;
* `Cap.defectIdentity_of_profileAC` and `Cap.Equality.revolutionF_eq_iff_of_defectIdentity`
  — the defect identity and the equality characterisation under `ProfileC1`;
* `Cap.volume_body_eq` — the body volume `|C|` is the genuine Lebesgue measure.

## What the hypotheses mean

The `Cap` structure records the profile on all of `ℝ`; the manuscript only uses
its values on `(-K,0)` and the limits `θ(-K⁺) = 1` (a structure field) and the
terminal radius `θ(0⁻)`.  The two hypotheses `C.θ (-C.K) = 1` and
`TerminalContinuous C` state that the recorded endpoint values are these limits,
so that `terminalArea` is the manuscript's terminal disk.  They are now storage
conventions of the `Cap` structure (fields `θ_entrance`, `θ_terminal`), so they hold
for every cap; hypothesis-free versions are in `RobinCaps/Cap/Unconditional.lean`.

The equality characterisation is stated here for `ProfileC1` caps (derivative
continuous on the *open* interval); the version for every admissible cap
(merely concave profiles, via the right-derivative ODE argument) is
`Cap.EqualityAC.equality_iff_AC` in `RobinCaps/Cap/EqualityAC.lean`. -/

open MeasureTheory Set

namespace RobinCaps
namespace Cap

noncomputable section

variable {m : ℕ}

/-- **Sharp end-cap inequality** (`eq:sharp-geometric`) for every admissible cap:
`𝓕(C) = |Γ| − m|C| ≥ ω_{m+1}/2`. -/
theorem sharp_cap_inequality (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hK : C.θ (-C.K) = 1) (h0 : TerminalContinuous C) :
    C.revolutionF ≥ omega (m + 1) / 2 :=
  sharp_revolutionF_of_profileAC m hm C (Concave.profileAC_of_cap C hK h0)

/-- **Positivity of the end coefficient** (`eq:positive-beta`):
`β(C) = (α/ω_m) 𝓕(C) ≥ β₀ = α ω_{m+1}/(2 ω_m) > 0`. -/
theorem positive_beta (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hK : C.θ (-C.K) = 1) (h0 : TerminalContinuous C) {α : ℝ} (hα : 0 < α) :
    α / omega m * C.revolutionF ≥ α * omega (m + 1) / (2 * omega m) ∧
      0 < α * omega (m + 1) / (2 * omega m) := by
  have hF := sharp_cap_inequality m hm C hK h0
  have hω := omega_pos m
  have hω' := omega_pos (m + 1)
  refine ⟨?_, by positivity⟩
  rw [ge_iff_le, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hω]
  nlinarith [hF, hω, hα, mul_le_mul_of_nonneg_left hF hα.le]

/-- **Equality characterisation** (`eq:equality-profile`) for `C¹` profiles:
`𝓕(C) = ω_{m+1}/2` iff `K ≥ 1` and the profile is a straight unit cylinder on
`(-K,-1)` followed by the unit semicircle on `(-1,0)`. -/
theorem equality_iff (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileC1 C) :
    C.revolutionF = omega (m + 1) / 2 ↔ EqualityProfile C :=
  Equality.revolutionF_eq_iff_of_defectIdentity m hm C h
    (defectIdentity_of_profileAC m hm C h.profileAC)

/-- **Sharp inequality for the paper's functional `F`** (`F = revolutionF` by definition). -/
theorem sharp_cap_inequality_F (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hK : C.θ (-C.K) = 1) (h0 : TerminalContinuous C) :
    C.F ≥ omega (m + 1) / 2 :=
  sharp_cap_inequality m hm C hK h0

/-- **`β(C) ≥ β₀ > 0`** for the paper's coefficient `beta`. -/
theorem beta_ge_beta0 (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hK : C.θ (-C.K) = 1) (h0 : TerminalContinuous C) {α : ℝ} (hα : 0 < α) :
    C.beta α ≥ α * omega (m + 1) / (2 * omega m) ∧ 0 < α * omega (m + 1) / (2 * omega m) :=
  positive_beta m hm C hK h0 hα

/-- **Equality characterisation for `F`** (`C¹` profiles). -/
theorem equality_iff_F (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileC1 C) :
    C.F = omega (m + 1) / 2 ↔ EqualityProfile C :=
  equality_iff m hm C h

/-- The hemisphere attains equality. -/
theorem hemisphere_equality (m : ℕ) (hm : 1 ≤ m) :
    (hemisphere m).revolutionF = omega (m + 1) / 2 :=
  hemisphere_revolutionF_eq m hm

/-- The body volume in the functional is the Lebesgue volume of the cap. -/
theorem volume_body_eq_of_cap (m : ℕ) (C : Cap m) :
    (volume C.body).toReal = C.revolutionVolume :=
  volume_body_toReal m C (Concave.continuousOn_Ioo C)

end

end Cap
end RobinCaps
