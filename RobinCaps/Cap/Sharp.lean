import Mathlib
import RobinCaps.Cap.Basic

/-!
# End caps of revolution: explicit results

This file collects the *proved* concrete facts about the cap functional
`sec:calibration` of `reference/robin_endcaps_corrected_en.tex` (line 251).

Everything proved here is about the **explicit revolution functional**
(`Cap.revolutionArea`, `Cap.revolutionVolume`, `Cap.revolutionF`), i.e. the
classical surface/volume-of-revolution integrals.  The identification with the
Hausdorff functional `Cap.F = ℋ^ m(Γ) - m|C|` is the open predicate
(historical note: an earlier `HausdorffIntegralBridge` predicate was removed as false; `Cap.F` is now *defined* as `revolutionF`); statements about `Cap.F`/`Cap.beta` are
recorded conditionally on that bridge and are **not** claimed as unconditional
theorems.

## Summary of contents

* `omega_one : ω₁ = 2`;
* arc-length and volume integrals of the semicircular profile
  (`semi_lateral_integral`, `semi_volume_integral`);
* the flat cap: `revolutionF = ω_m`;
* the truncated semicircular cap (`m = 1`), manuscript `eq:truncated-area`,
  `eq:truncated-beta`;
* the hemisphere at `m = 1` (`β₀/α = π/4`);
* explicit target predicates for the general-`m` hemisphere and for the sharp
  inequality `𝓕 ≥ ω_{m+1}/2`, which are **not** proved here.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps

namespace Cap

noncomputable section

/-! ## `ω₁ = 2` -/

/-- The volume of the unit ball in dimension `1` is `2`. -/
theorem omega_one : omega 1 = 2 := by
  unfold RobinCaps.omega
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, pow_one]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1), one_mul]
  have hg : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    have h : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
    rw [h, Real.Gamma_add_one (by norm_num : ((1 : ℝ) / 2) ≠ 0), Real.Gamma_one_half_eq]
    ring
  norm_num only [Nat.cast_one]
  rw [hg]
  rw [ENNReal.toReal_ofReal
    (by positivity : (0 : ℝ) ≤ Real.sqrt Real.pi / (Real.sqrt Real.pi / 2))]
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

/-! ## Integrals of the semicircular profile -/

/-- The arc-length density `√(1 + (deriv θ)²)` integrates to `arcsin K` for the
semicircular profile `θ = semi K`, `0 < K ≤ 1` (this is `eq:truncated-area`,
lateral part).  The proof uses the FTC in the form that only requires
differentiability on the open interval and nonnegativity of the derivative
(so it covers the endpoint singularity at `K = 1`). -/
theorem semi_lateral_integral (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    ∫ s in (-K)..0, Real.sqrt (1 + (deriv (semi K) s) ^ 2) = Real.arcsin K := by
  set F : ℝ → ℝ := fun s => Real.arcsin (s + K) with hF
  have hcont : ContinuousOn F (Set.Icc (-K) 0) := by
    rw [hF]; fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (-K) 0,
      HasDerivAt F (Real.sqrt (1 + (deriv (semi K) x) ^ 2)) x := by
    intro x hx
    have hx1 : x + K ≠ -1 := by linarith [hx.1]
    have hx2 : x + K ≠ 1 := by
      have : x + K < 1 := by linarith [hx.2, hK1]
      linarith
    have hbase : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (x + K) ^ 2)) (x + K) :=
      Real.hasDerivAt_arcsin hx1 hx2
    have hlin : HasDerivAt (fun s : ℝ => s + K) 1 x := (hasDerivAt_id x).add_const K
    have hcomp := hbase.comp x hlin
    have hpos : 0 < 1 - (x + K) ^ 2 := by
      have hx1' : 0 < x + K := by linarith [hx.1]
      have hx2' : x + K < 1 := by linarith [hx.2, hK1]
      nlinarith
    have hvalue : 1 / Real.sqrt (1 - (x + K) ^ 2) =
        Real.sqrt (1 + (deriv (semi K) x) ^ 2) := by
      rw [deriv_semi K hpos]
      have hsq : (Real.sqrt (1 - (x + K) ^ 2)) ^ 2 = 1 - (x + K) ^ 2 :=
        Real.sq_sqrt (le_of_lt hpos)
      have hmain : 1 + (semiD K x) ^ 2 = ((Real.sqrt (1 - (x + K) ^ 2))⁻¹) ^ 2 := by
        simp only [semiD]
        field_simp
        nlinarith [hsq]
      rw [hmain, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity), one_div]
    have hfun : (Real.arcsin ∘ fun s : ℝ => s + K) = F := by rw [hF]; rfl
    rw [hfun] at hcomp
    exact hcomp.congr_deriv (by simpa using hvalue)
  have hpos' : ∀ x ∈ Set.Ioo (-K) 0,
      0 ≤ Real.sqrt (1 + (deriv (semi K) x) ^ 2) := fun x hx => Real.sqrt_nonneg _
  have huIcc : Set.uIcc (-K) 0 = Set.Icc (-K) 0 :=
    Set.uIcc_of_le (neg_nonpos.mpr (le_of_lt hK))
  have hcont' : ContinuousOn F (Set.uIcc (-K) 0) := by rw [huIcc]; exact hcont
  have hmin : min (-K) (0 : ℝ) = -K := min_eq_left (neg_nonpos.mpr (le_of_lt hK))
  have hmax : max (-K) (0 : ℝ) = 0 := max_eq_right (neg_nonpos.mpr (le_of_lt hK))
  have hint : IntervalIntegrable (fun x => Real.sqrt (1 + (deriv (semi K) x) ^ 2))
      volume (-K) 0 :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg (a := -K) (b := 0) hcont'
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (-K) 0 := by simpa only [hmin, hmax] using hx
        exact hderiv x hx')
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (-K) 0 := by simpa only [hmin, hmax] using hx
        exact hpos' x hx')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := -K) (b := 0)
    (show (-K : ℝ) ≤ 0 by linarith) hcont (fun x hx => hderiv x hx) hint
  rw [hFTC]
  simp only [hF]
  rw [zero_add, show (-K) + K = (0 : ℝ) by ring, Real.arcsin_zero, sub_zero]

/-- Primitive for the volume integral of the semicircular profile:
`(1/2)((s+K)√(1-(s+K)²) + arcsin(s+K))`. -/
noncomputable def semiPrim (K s : ℝ) : ℝ :=
  (1 / 2) * ((s + K) * Real.sqrt (1 - (s + K) ^ 2) + Real.arcsin (s + K))

/-- Derivative of `semiPrim` is the semicircular profile. -/
theorem semiPrim_hasDerivAt (K : ℝ) {s : ℝ} (hs : 0 < 1 - (s + K) ^ 2) :
    HasDerivAt (semiPrim K) (semi K s) s := by
  have hs_ne1 : s + K ≠ -1 := by nlinarith [hs]
  have hs_ne2 : s + K ≠ 1 := by nlinarith [hs]
  have hlin : HasDerivAt (fun s : ℝ => s + K) 1 s := (hasDerivAt_id s).add_const K
  have hsemi : HasDerivAt (semi K) (semiD K s) s := semi_hasDerivAt K hs
  have hprod : HasDerivAt (fun s => (s + K) * semi K s)
      (1 * semi K s + (s + K) * semiD K s) s := hlin.mul hsemi
  have hbase : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (s + K) ^ 2)) (s + K) :=
    Real.hasDerivAt_arcsin hs_ne1 hs_ne2
  have hcomp : HasDerivAt (fun s => Real.arcsin (s + K)) (1 / Real.sqrt (1 - (s + K) ^ 2)) s := by
    have := hbase.comp s hlin
    simpa [Function.comp, mul_one] using this
  have hsum := hprod.add hcomp
  have hconst : HasDerivAt (fun s => (1 / 2) * ((s + K) * semi K s + Real.arcsin (s + K)))
      ((1 / 2) * ((1 * semi K s + (s + K) * semiD K s) + 1 / Real.sqrt (1 - (s + K) ^ 2))) s :=
    hsum.const_mul (1 / 2)
  have hval : (1 / 2) * ((1 * semi K s + (s + K) * semiD K s) + 1 / Real.sqrt (1 - (s + K) ^ 2))
      = semi K s := by
    simp only [semiD, semi]
    have hsq : (Real.sqrt (1 - (s + K) ^ 2)) ^ 2 = 1 - (s + K) ^ 2 := Real.sq_sqrt (le_of_lt hs)
    have hsp : Real.sqrt (1 - (s + K) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
    field_simp
    nlinarith [hsq]
  have hfun : (fun s => (1 / 2) * ((s + K) * semi K s + Real.arcsin (s + K))) = semiPrim K := by
    funext t; simp only [semiPrim, semi]
  rw [hfun] at hconst
  exact hconst.congr_deriv hval

/-- The volume integral of the semicircular profile (`eq:truncated-area`, volume part):
`∫ semi K = (1/2)(K√(1-K²) + arcsin K)`. -/
theorem semi_volume_integral (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    ∫ s in (-K)..0, semi K s = (1 / 2) * (K * Real.sqrt (1 - K ^ 2) + Real.arcsin K) := by
  have hcont : ContinuousOn (semiPrim K) (Set.Icc (-K) 0) := by
    rw [show semiPrim K = fun s =>
      (1 / 2) * ((s + K) * Real.sqrt (1 - (s + K) ^ 2) + Real.arcsin (s + K)) by
        funext t; simp only [semiPrim]]
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (-K) 0, HasDerivAt (semiPrim K) (semi K x) x := by
    intro x hx
    apply semiPrim_hasDerivAt K
    have hx1 : 0 < x + K := by linarith [hx.1]
    have hx2 : x + K < 1 := by linarith [hx.2, hK1]
    nlinarith
  have hint : IntervalIntegrable (semi K) volume (-K) 0 :=
    (by apply Continuous.sqrt; fun_prop : Continuous (semi K)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := -K) (b := 0)
    (show (-K : ℝ) ≤ 0 by linarith) hcont hderiv hint
  rw [hFTC]
  have h0 : semiPrim K 0 = (1 / 2) * (K * Real.sqrt (1 - K ^ 2) + Real.arcsin K) := by
    simp only [semiPrim]
    rw [zero_add]
  have hmK : semiPrim K (-K) = 0 := by
    simp only [semiPrim]
    rw [show -K + K = (0 : ℝ) by ring, Real.arcsin_zero]
    norm_num
  rw [h0, hmK, sub_zero]

/-! ## The flat cap `θ ≡ 1` -/

theorem flat_lateralArea (m : ℕ) (K : ℝ) (hK : 0 < K) :
    (flat m K hK).lateralArea = (m : ℝ) * omega m * K := by
  simp only [flat, lateralArea]
  have hderiv : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by
    funext s; simp
  rw [hderiv]
  simp only [one_pow, one_mul]
  rw [intervalIntegral.integral_const]
  simp

theorem flat_terminalArea (m : ℕ) (K : ℝ) (hK : 0 < K) :
    (flat m K hK).terminalArea = omega m := by
  simp only [flat, terminalArea, one_pow, mul_one]

theorem flat_revolutionVolume (m : ℕ) (K : ℝ) (hK : 0 < K) :
    (flat m K hK).revolutionVolume = omega m * K := by
  simp only [flat, revolutionVolume]
  rw [intervalIntegral.integral_const]
  simp

/-- **Flat cap** (manuscript `sec:checks`): for `θ ≡ 1` the explicit functional
equals `ω_m`, so `β/α = 1`. -/
theorem flat_revolutionF (m : ℕ) (K : ℝ) (hK : 0 < K) :
    (flat m K hK).revolutionF = omega m := by
  simp only [revolutionF, revolutionArea, flat_lateralArea, flat_terminalArea,
    flat_revolutionVolume]
  ring

/-- Flat-cap identity for the paper's functional `F`. -/
theorem flat_F_eq_omega (m : ℕ) (K : ℝ) (hK : 0 < K) :
    (flat m K hK).F = omega m := by
  rw [F_eq_revolutionF, flat_revolutionF]

/-- Flat-cap coefficient: `β = α`. -/
theorem flat_beta_eq_alpha (m : ℕ) (K : ℝ) (hK : 0 < K) (hω : omega m ≠ 0) :
    (flat m K hK).beta α = α := by
  rw [beta, flat_F_eq_omega m K hK]
  field_simp

/-! ## The truncated semicircular cap (`m = 1`) -/

theorem truncatedSemi_K (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).K = Real.sqrt (1 - γ ^ 2) := rfl

/-- The terminal radius of the truncated cap is `γ`. -/
theorem truncatedSemi_theta_zero (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).θ 0 = γ := by
  have hKsq : (Real.sqrt (1 - γ ^ 2)) ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt (by nlinarith [hγ, hγ1])
  have hsub : 1 - (Real.sqrt (1 - γ ^ 2)) ^ 2 = γ ^ 2 := by rw [hKsq]; ring
  simp only [truncatedSemi, semi, zero_add]
  rw [hsub, Real.sqrt_sq_eq_abs, abs_of_nonneg hγ]

theorem sqrt_one_sub_truncatedKsq (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Real.sqrt (1 - (Real.sqrt (1 - γ ^ 2)) ^ 2) = γ := by
  have hKsq : (Real.sqrt (1 - γ ^ 2)) ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt (by nlinarith [hγ, hγ1])
  have hsub : 1 - (Real.sqrt (1 - γ ^ 2)) ^ 2 = γ ^ 2 := by rw [hKsq]; ring
  rw [hsub, Real.sqrt_sq_eq_abs, abs_of_nonneg hγ]

/-- **Truncated lateral length** (`eq:truncated-area`, lateral part):
the lateral boundary contributes `2 arccos γ`. -/
theorem truncatedSemi_lateralArea (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).lateralArea = 2 * Real.arccos γ := by
  have hKpos : 0 < Real.sqrt (1 - γ ^ 2) := by rw [Real.sqrt_pos]; nlinarith
  have hK1 : Real.sqrt (1 - γ ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; nlinarith
  have hlat := semi_lateral_integral (Real.sqrt (1 - γ ^ 2)) hKpos hK1
  simp only [truncatedSemi, lateralArea]
  rw [omega_one]
  norm_num
  rw [hlat, ← Real.arccos_eq_arcsin hγ]

/-- The terminal disk of the truncated cap contributes `2γ` (`m = 1`). -/
theorem truncatedSemi_terminalArea (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).terminalArea = 2 * γ := by
  simp only [truncatedSemi, terminalArea]
  rw [omega_one]
  simp only [semi, zero_add, pow_one]
  rw [sqrt_one_sub_truncatedKsq γ hγ (le_of_lt hγ1)]

/-- **`eq:truncated-area`**: `|Γ_γ| = 2 arccos γ + 2γ`. -/
theorem truncatedSemi_revolutionArea (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).revolutionArea = 2 * Real.arccos γ + 2 * γ := by
  simp only [revolutionArea, truncatedSemi_lateralArea, truncatedSemi_terminalArea]

/-- **`eq:truncated-area`**: `|C_γ| = arccos γ + γ√(1-γ²)`. -/
theorem truncatedSemi_revolutionVolume (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).revolutionVolume =
      Real.arccos γ + γ * Real.sqrt (1 - γ ^ 2) := by
  have hKpos : 0 < Real.sqrt (1 - γ ^ 2) := by rw [Real.sqrt_pos]; nlinarith
  have hK1 : Real.sqrt (1 - γ ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; nlinarith
  have hvol := semi_volume_integral (Real.sqrt (1 - γ ^ 2)) hKpos hK1
  simp only [truncatedSemi, revolutionVolume, pow_one]
  rw [omega_one, hvol]
  rw [sqrt_one_sub_truncatedKsq γ hγ (le_of_lt hγ1), ← Real.arccos_eq_arcsin hγ]
  ring

/-- **`eq:truncated-beta`**: `𝓕_γ = arccos γ + 2γ - γ√(1-γ²)`. -/
theorem truncatedSemi_revolutionF (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (truncatedSemi γ hγ hγ1).revolutionF =
      Real.arccos γ + 2 * γ - γ * Real.sqrt (1 - γ ^ 2) := by
  simp only [revolutionF, truncatedSemi_revolutionArea, truncatedSemi_revolutionVolume]
  ring

/-- **`eq:truncated-beta`**:
`β_γ/α = (arccos γ + 2γ - γ√(1-γ²))/2`. -/
theorem truncatedSemi_beta_div (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (α : ℝ)
    (hα : α ≠ 0) :
    (truncatedSemi γ hγ hγ1).beta α / α =
      (Real.arccos γ + 2 * γ - γ * Real.sqrt (1 - γ ^ 2)) / 2 := by
  rw [beta, F_eq_revolutionF, truncatedSemi_revolutionF, omega_one]
  field_simp

/-! ## The hemisphere (`m = 1`) -/

/-- The hemispherical cap of transverse dimension `m`: `K = 1`,
`θ(s) = √(1-(s+1)²)`. -/
def hemisphere (m : ℕ) : Cap m where
  K := 1
  hK := one_pos
  θ := semi 1
  θ_pos := fun _ hs => semi_pos 1 (le_refl 1) hs
  θ_le_one := fun _ hs => semi_le_one 1 (le_refl 1) hs
  θ_concave := semi_concaveOn 1 (le_refl 1)
  θ_antitone := semi_antitoneOn 1
  θ_tendsto := semi_tendsto 1
  θ_entrance := semi_neg_self 1
  θ_terminal := semi_tendsto_left 1 0

/-- Hemisphere at `m = 1`: the explicit functional equals `π/2 = ω₂/2`. -/
theorem hemisphere_one_revolutionF :
    (hemisphere 1).revolutionF = Real.pi / 2 := by
  have hKpos : 0 < (1 : ℝ) := one_pos
  have hK1 : (1 : ℝ) ≤ 1 := le_refl 1
  have hlat := semi_lateral_integral 1 hKpos hK1
  have hvol := semi_volume_integral 1 hKpos hK1
  simp only [hemisphere, revolutionF, revolutionArea, lateralArea, terminalArea,
    revolutionVolume]
  rw [omega_one]
  simp only [tsub_self, pow_zero, pow_one, one_mul]
  rw [hlat, hvol]
  norm_num [semi, Real.arcsin_one, Real.arcsin_zero]
  ring

/-- Hemisphere at `m = 1`: `β₀/α = π/4`. -/
theorem hemisphere_one_beta_div (α : ℝ) (hα : α ≠ 0) :
    (hemisphere 1).beta α / α = Real.pi / 4 := by
  rw [beta, F_eq_revolutionF, hemisphere_one_revolutionF, omega_one]
  field_simp [hα]
  norm_num

/-! ## Extension invariance under appending a straight cylinder

Appending a straight unit cylinder of length `δ` at the entrance is
modelled by the profile `Cap.appendProfile K δ θ`.  The explicit
functional `revF` is unchanged, because both `|Γ|` and `m|C|` grow by
`m ω_m δ`.  This is proved for the explicit revolution functionals
(under the natural interval-integrability hypotheses). -/

noncomputable def revLateral (m : ℕ) (K : ℝ) (θ : ℝ → ℝ) : ℝ :=
  (m:ℝ) * omega m * ∫ s in (-K)..0, (θ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ s) ^ 2)

noncomputable def revVolume (m : ℕ) (K : ℝ) (θ : ℝ → ℝ) : ℝ :=
  omega m * ∫ s in (-K)..0, (θ s) ^ m

noncomputable def revTerminal (m : ℕ) (θ : ℝ → ℝ) : ℝ := omega m * (θ 0)^ m

noncomputable def revF (m : ℕ) (K : ℝ) (θ : ℝ → ℝ) : ℝ :=
  revLateral m K θ + revTerminal m θ - (m:ℝ) * revVolume m K θ

noncomputable def appendProfile (K _δ : ℝ) (θ : ℝ → ℝ) : ℝ → ℝ :=
  fun s => if s < -K then 1 else θ s

theorem revLateral_eq (m : ℕ) (C : Cap m) :
    C.lateralArea = revLateral m C.K C.θ := rfl

theorem revVolume_eq (m : ℕ) (C : Cap m) :
    C.revolutionVolume = revVolume m C.K C.θ := rfl

theorem revTerminal_eq (m : ℕ) (C : Cap m) :
    C.terminalArea = revTerminal m C.θ := rfl

theorem revF_eq (m : ℕ) (C : Cap m) :
    C.revolutionF = revF m C.K C.θ := rfl

theorem deriv_appendProfile_cyl (K δ : ℝ) (θ : ℝ → ℝ) {s : ℝ} (hs : s < -K) :
    deriv (appendProfile K δ θ) s = 0 := by
  rw [show deriv (appendProfile K δ θ) s = deriv (fun _ : ℝ => (1:ℝ)) s from
    Filter.EventuallyEq.deriv_eq ?_]
  · simp
  · apply Filter.eventually_of_mem (isOpen_Iio.mem_nhds hs)
    intro t ht
    rw [Set.mem_Iio] at ht
    rw [appendProfile, if_pos ht]

theorem deriv_appendProfile_cap (K δ : ℝ) (θ : ℝ → ℝ) {s : ℝ} (hs : -K < s) :
    deriv (appendProfile K δ θ) s = deriv θ s := by
  apply Filter.EventuallyEq.deriv_eq
  apply Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs)
  intro t ht
  rw [Set.mem_Ioi] at ht
  rw [appendProfile, if_neg (not_lt.mpr (le_of_lt ht))]

theorem appendProfile_cyl (K δ : ℝ) (θ : ℝ → ℝ) {s : ℝ} (hs : s < -K) :
    appendProfile K δ θ s = 1 := by rw [appendProfile, if_pos hs]

theorem appendProfile_cap (K δ : ℝ) (θ : ℝ → ℝ) {s : ℝ} (hs : -K < s) :
    appendProfile K δ θ s = θ s := by
  rw [appendProfile, if_neg (not_lt.mpr (le_of_lt hs))]

theorem ae_lt_of_ae_restrict_Ioc {a b : ℝ} :
    ∀ᵐ x ∂volume.restrict (Set.Ioc a b), x < b := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (Real.volume_singleton (a := b))
  intro x hx
  have hx' := Classical.not_imp.mp hx
  rw [Set.mem_Ioc] at hx'
  rw [not_lt] at hx'
  exact le_antisymm hx'.1.2 hx'.2

theorem ae_gt_of_ae_restrict_Ioc {a b : ℝ} :
    ∀ᵐ x ∂volume.restrict (Set.Ioc a b), a < x := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (Real.volume_singleton (a := a))
  intro x hx
  have hx' := Classical.not_imp.mp hx
  rw [Set.mem_Ioc] at hx'
  rw [not_lt] at hx'
  exact le_antisymm hx'.2 (le_of_lt hx'.1.1)

theorem lateral_integral_append (m : ℕ) (K δ : ℝ) (hδ : 0 < δ) (hK : 0 < K) (θ : ℝ → ℝ)
    (hintθ : IntervalIntegrable
      (fun s => (θ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ s) ^ 2)) volume (-K) 0) :
    ∫ s in (-(K + δ))..0, (appendProfile K δ θ s)^ (m - 1) *
        Real.sqrt (1 + (deriv (appendProfile K δ θ) s)^ 2)
      = (∫ s in (-K)..0, (θ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ s) ^ 2)) + δ := by
  have hsplit : (-(K + δ) : ℝ) ≤ -K := by linarith
  have hK0 : (-K : ℝ) ≤ 0 := by linarith
  have hcyl_r : (fun s => (appendProfile K δ θ s)^ (m - 1) *
      Real.sqrt (1 + (deriv (appendProfile K δ θ) s)^ 2))
      =ᵐ[volume.restrict (Set.uIoc (-(K + δ)) (-K))] (fun _ => (1:ℝ)) := by
    rw [Set.uIoc_of_le hsplit]
    filter_upwards [ae_lt_of_ae_restrict_Ioc] with x hx
    rw [deriv_appendProfile_cyl K δ θ hx, appendProfile_cyl K δ θ hx]
    simp
  have hcyl_ae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (-(K + δ)) (-K) →
      (appendProfile K δ θ x)^ (m - 1) * Real.sqrt (1 + (deriv (appendProfile K δ θ) x)^ 2) = 1 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp hcyl_r
  have hcap_r : (fun s => (appendProfile K δ θ s)^ (m - 1) *
      Real.sqrt (1 + (deriv (appendProfile K δ θ) s)^ 2))
      =ᵐ[volume.restrict (Set.uIoc (-K) 0)]
      (fun s => (θ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ s) ^ 2)) := by
    rw [Set.uIoc_of_le hK0]
    filter_upwards [ae_gt_of_ae_restrict_Ioc] with x hx
    rw [deriv_appendProfile_cap K δ θ hx, appendProfile_cap K δ θ hx]
  have hcap_ae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (-K) 0 →
      (appendProfile K δ θ x)^ (m - 1) * Real.sqrt (1 + (deriv (appendProfile K δ θ) x)^ 2)
        = (θ x)^ (m - 1) * Real.sqrt (1 + (deriv θ x)^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp hcap_r
  have hI1 : IntervalIntegrable (fun s => (appendProfile K δ θ s)^ (m - 1) *
      Real.sqrt (1 + (deriv (appendProfile K δ θ) s)^ 2)) volume (-(K + δ)) (-K) :=
    (intervalIntegrable_const).congr_ae hcyl_r.symm
  have hI2 : IntervalIntegrable (fun s => (appendProfile K δ θ s)^ (m - 1) *
      Real.sqrt (1 + (deriv (appendProfile K δ θ) s)^ 2)) volume (-K) 0 :=
    hintθ.congr_ae hcap_r.symm
  have hadj := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hc : ∫ s in (-(K + δ))..(-K), (appendProfile K δ θ s)^ (m - 1) *
      Real.sqrt (1 + (deriv (appendProfile K δ θ) s)^ 2) = δ := by
    rw [intervalIntegral.integral_congr_ae hcyl_ae]
    rw [intervalIntegral.integral_const]
    simp [sub_eq_add_neg, add_comm]
  have hp : ∫ s in (-K)..0, (appendProfile K δ θ s)^ (m - 1) *
      Real.sqrt (1 + (deriv (appendProfile K δ θ) s)^ 2)
      = ∫ s in (-K)..0, (θ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ s) ^ 2) :=
    intervalIntegral.integral_congr_ae hcap_ae
  rw [← hadj, hc, hp]
  ring

theorem volume_integral_append (m : ℕ) (K δ : ℝ) (hδ : 0 < δ) (hK : 0 < K) (θ : ℝ → ℝ)
    (hintθ : IntervalIntegrable (fun s => (θ s) ^ m) volume (-K) 0) :
    ∫ s in (-(K + δ))..0, (appendProfile K δ θ s)^ m
      = (∫ s in (-K)..0, (θ s) ^ m) + δ := by
  have hsplit : (-(K + δ) : ℝ) ≤ -K := by linarith
  have hK0 : (-K : ℝ) ≤ 0 := by linarith
  have hcyl_r : (fun s => (appendProfile K δ θ s)^ m)
      =ᵐ[volume.restrict (Set.uIoc (-(K + δ)) (-K))] (fun _ => (1:ℝ)) := by
    rw [Set.uIoc_of_le hsplit]
    filter_upwards [ae_lt_of_ae_restrict_Ioc] with x hx
    rw [appendProfile_cyl K δ θ hx]
    simp
  have hcyl_ae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (-(K + δ)) (-K) →
      (appendProfile K δ θ x)^ m = 1 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp hcyl_r
  have hcap_r : (fun s => (appendProfile K δ θ s)^ m)
      =ᵐ[volume.restrict (Set.uIoc (-K) 0)] (fun s => (θ s) ^ m) := by
    rw [Set.uIoc_of_le hK0]
    filter_upwards [ae_gt_of_ae_restrict_Ioc] with x hx
    rw [appendProfile_cap K δ θ hx]
  have hcap_ae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (-K) 0 →
      (appendProfile K δ θ x)^ m = (θ x)^ m :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp hcap_r
  have hI1 : IntervalIntegrable (fun s => (appendProfile K δ θ s)^ m) volume (-(K + δ)) (-K) :=
    (intervalIntegrable_const).congr_ae hcyl_r.symm
  have hI2 : IntervalIntegrable (fun s => (appendProfile K δ θ s)^ m) volume (-K) 0 :=
    hintθ.congr_ae hcap_r.symm
  have hadj := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hc : ∫ s in (-(K + δ))..(-K), (appendProfile K δ θ s)^ m = δ := by
    rw [intervalIntegral.integral_congr_ae hcyl_ae]
    rw [intervalIntegral.integral_const]
    simp [sub_eq_add_neg, add_comm]
  have hp : ∫ s in (-K)..0, (appendProfile K δ θ s)^ m = ∫ s in (-K)..0, (θ s) ^ m :=
    intervalIntegral.integral_congr_ae hcap_ae
  rw [← hadj, hc, hp]
  ring

theorem revF_append (m : ℕ) (K δ : ℝ) (hδ : 0 < δ) (hK : 0 < K) (θ : ℝ → ℝ)
    (hintL : IntervalIntegrable
      (fun s => (θ s) ^ (m - 1) * Real.sqrt (1 + (deriv θ s) ^ 2)) volume (-K) 0)
    (hintV : IntervalIntegrable (fun s => (θ s) ^ m) volume (-K) 0) :
    revF m (K + δ) (appendProfile K δ θ) = revF m K θ := by
  have hL := lateral_integral_append m K δ hδ hK θ hintL
  have hV := volume_integral_append m K δ hδ hK θ hintV
  have h0 : appendProfile K δ θ 0 = θ 0 := appendProfile_cap K δ θ (by linarith)
  simp only [revF, revLateral, revVolume, revTerminal, hL, hV, h0]
  ring

/-! ## Unproven targets (explicitly *not* proved here) -/

/-- **Target** (recorded as a `Prop`; the proved headline results are in `RobinCaps/Final.lean`). For the general-`m` hemisphere the explicit exposed
area should equal `(m+1) ω_{m+1}/2`.  (Note: the manuscript prompt's
`m ω_{m+1}/2` is off by a factor; the correct value follows from
`|Γ| = (m+1)ω_{m+1}/2` and `|C| = ω_{m+1}/2`.)  The missing ingredient is the
solid-of-revolution/sphere-area identity, which mathlib does not provide. -/
def HemisphereAreaTarget (m : ℕ) : Prop :=
  (hemisphere m).revolutionArea = ((m : ℝ) + 1) * omega (m + 1) / 2

/-- **Target** (recorded as a `Prop`; the proved headline results are in `RobinCaps/Final.lean`). The hemispherical body volume should be `ω_{m+1}/2`. -/
def HemisphereVolumeTarget (m : ℕ) : Prop :=
  (hemisphere m).revolutionVolume = omega (m + 1) / 2

/-- **Target** (recorded as a `Prop`; the proved headline results are in `RobinCaps/Final.lean`). The sharp cap inequality `𝓕(C) ≥ ω_{m+1}/2`
(manuscript `eq:sharp-geometric`) for the explicit revolution functional. The
proof requires the divergence-theorem argument over a curved (non-box) domain;
mathlib's divergence theorem is box-only. -/
def SharpCapInequalityTarget (m : ℕ) : Prop :=
  ∀ C : Cap m, C.revolutionF ≥ omega (m + 1) / 2

end

end Cap

end RobinCaps
