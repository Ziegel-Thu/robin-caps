import RobinCaps.Cap.Equality
import RobinCaps.Cap.FluxAC
import RobinCaps.Cap.Concave
import RobinCaps.Cap.Main

/-!
# The equality case for merely concave (admissible) profiles

`RobinCaps/Cap/Equality.lean` characterises the equality case of the sharp
end-cap inequality for `C¹` profiles (`ProfileC1`).  This file removes the `C¹`
hypothesis: the characterisation is proved for every admissible cap, i.e. under
the weak regularity `ProfileAC` (in fact under no hypothesis beyond the `Cap`
structure plus the two endpoint-value conventions `θ(-K) = 1` and
`TerminalContinuous`, via `Concave.profileAC_of_cap`).

## The route

Under `ProfileAC C` and `revolutionF C = ω_{m+1}/2`, the defect identity forces
both defects to vanish; hence `θ(0) = 0` and the lateral defect integrand
vanishes **a.e.** on `(-K,0)`, i.e. `deriv θ = R` a.e. where
`R s = -√(1-θ(s)²)/θ(s)` is *continuous* on the open interval.

The `C¹` proof upgraded "a.e." to "everywhere" by continuity of `deriv θ`.  Here
we use instead the *right derivative* `D s = derivWithin θ (Ioi s) s`, which
exists at every point of `(-K,0)` and is **antitone** there
(`Concave.hasDerivWithinAt_Ioi`, `Concave.antitoneOn_rightDeriv`), and agrees
a.e. with `deriv θ` (`Concave.rightDeriv_ae_eq_deriv`).  The key step
(`rightDeriv_eq_of_ae_eq_continuous`) is that an antitone function agreeing a.e.
with a continuous function agrees with it *everywhere*: a full-measure set meets
every subinterval of positive length, so one can pick sequences `tₙ ↓ s` and
`t'ₙ ↑ s` inside it, and antitonicity sandwiches `R tₙ = D tₙ ≤ D s ≤ D t'ₙ =
R t'ₙ`; continuity of `R` at `s` closes the sandwich.

This yields `HasDerivWithinAt θ (R s) (Ioi s) s` at *every* point of `(-K,0)`,
which is exactly the hypothesis of the one-sided fundamental theorem of calculus
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`.  Integrating
`h = √(1-θ²)`, `h' = 1` then reproduces the equality profile exactly as in the
`C¹` case.  No absolutely-continuous/Lipschitz FTC is used anywhere.

## Main results

* `rightDeriv_eq_of_ae_eq_continuous` — antitone + a.e. equal to continuous ⟹ equal;
* `equalityODE_right_of_lateralDefect_eq_zero` — the profile ODE in right-derivative form;
* `equalityProfile_of_profileAC` — equality forces the equality profile;
* `revolutionF_eq_of_equalityProfile_AC` — the converse;
* `equality_iff_AC` — the full characterisation for every admissible cap.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RobinCaps
namespace Cap

noncomputable section

namespace EqualityAC

variable {m : ℕ}

/-! ## Step 0: a full-measure set meets every interval of positive length -/

/-- A property holding almost everywhere holds at some point of every nonempty
open interval. -/
theorem exists_mem_Ioo_of_ae {a b : ℝ} (hab : a < b) {p : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume : Measure ℝ), p t) : ∃ t ∈ Ioo a b, p t := by
  by_contra hcon
  push_neg at hcon
  have hnull : volume (Ioo a b) = 0 :=
    measure_mono_null (fun t ht => hcon t ht) (ae_iff.mp h)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hnull
  linarith

/-- `s + 1/(n+1) → s`. -/
theorem tendsto_add_one_div (s : ℝ) :
    Tendsto (fun n : ℕ => s + 1 / ((n : ℝ) + 1)) atTop (𝓝 s) := by
  have h := (tendsto_const_nhds (x := s) (f := (atTop : Filter ℕ))).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using h

/-- `s - 1/(n+1) → s`. -/
theorem tendsto_sub_one_div (s : ℝ) :
    Tendsto (fun n : ℕ => s - 1 / ((n : ℝ) + 1)) atTop (𝓝 s) := by
  have h := (tendsto_const_nhds (x := s) (f := (atTop : Filter ℕ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using h

/-- A sequence of points of `(s,b)` satisfying an a.e. property and decreasing to `s`. -/
theorem exists_seq_right {p : ℝ → Prop} (hp : ∀ᵐ t ∂(volume : Measure ℝ), p t) {s b : ℝ}
    (hsb : s < b) :
    ∃ v : ℕ → ℝ, (∀ n, v n ∈ Ioo s b) ∧ (∀ n, p (v n)) ∧ Tendsto v atTop (𝓝 s) := by
  have hchoice : ∀ n : ℕ, ∃ t ∈ Ioo s (min b (s + 1 / ((n : ℝ) + 1))), p t := by
    intro n
    refine exists_mem_Ioo_of_ae (lt_min hsb ?_) hp
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose v hv hpv using hchoice
  refine ⟨v, fun n => ⟨(hv n).1, lt_of_lt_of_le (hv n).2 (min_le_left _ _)⟩, hpv, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_add_one_div s)
    (fun n => (hv n).1.le) (fun n => (lt_of_lt_of_le (hv n).2 (min_le_right _ _)).le)

/-- A sequence of points of `(a,s)` satisfying an a.e. property and increasing to `s`. -/
theorem exists_seq_left {p : ℝ → Prop} (hp : ∀ᵐ t ∂(volume : Measure ℝ), p t) {a s : ℝ}
    (has : a < s) :
    ∃ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a s) ∧ (∀ n, p (v n)) ∧ Tendsto v atTop (𝓝 s) := by
  have hchoice : ∀ n : ℕ, ∃ t ∈ Ioo (max a (s - 1 / ((n : ℝ) + 1))) s, p t := by
    intro n
    refine exists_mem_Ioo_of_ae (max_lt has ?_) hp
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose v hv hpv using hchoice
  refine ⟨v, fun n => ⟨lt_of_le_of_lt (le_max_left _ _) (hv n).1, (hv n).2⟩, hpv, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_sub_one_div s) tendsto_const_nhds
    (fun n => (lt_of_le_of_lt (le_max_right _ _) (hv n).1).le) (fun n => (hv n).2.le)

/-! ## Step 1: antitone + a.e. equal to continuous ⟹ equal everywhere -/

/-- **Key step.**  The right derivative of a cap profile is antitone on `(-K,0)`;
if it agrees almost everywhere with a function continuous on `(-K,0)`, then it
agrees with it at *every* point of `(-K,0)`. -/
theorem rightDeriv_eq_of_ae_eq_continuous (C : Cap m) (R : ℝ → ℝ)
    (hR : ContinuousOn R (Ioo (-C.K) 0))
    (hae : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) 0)), derivWithin C.θ (Ioi s) s = R s) :
    ∀ s ∈ Ioo (-C.K) 0, derivWithin C.θ (Ioi s) s = R s := by
  have hp : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Ioo (-C.K) 0 → derivWithin C.θ (Ioi t) t = R t := by
    rwa [ae_restrict_iff' measurableSet_Ioo] at hae
  have hanti := Concave.antitoneOn_rightDeriv C
  intro s hs
  -- approach from the right: `R tₙ = D tₙ ≤ D s`
  obtain ⟨v, hv, hpv, hvlim⟩ := exists_seq_right hp hs.2
  have hvmem : ∀ n, v n ∈ Ioo (-C.K) 0 := fun n => ⟨hs.1.trans (hv n).1, (hv n).2⟩
  have hRv : ∀ n, R (v n) ≤ derivWithin C.θ (Ioi s) s := by
    intro n
    rw [← hpv n (hvmem n)]
    exact hanti hs (hvmem n) (hv n).1.le
  have hRtend : Tendsto (fun n => R (v n)) atTop (𝓝 (R s)) :=
    (hR s hs).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hvlim
      (Eventually.of_forall hvmem))
  have h1 : R s ≤ derivWithin C.θ (Ioi s) s :=
    le_of_tendsto hRtend (Eventually.of_forall hRv)
  -- approach from the left: `D s ≤ D t'ₙ = R t'ₙ`
  obtain ⟨w, hw, hpw, hwlim⟩ := exists_seq_left hp hs.1
  have hwmem : ∀ n, w n ∈ Ioo (-C.K) 0 := fun n => ⟨(hw n).1, (hw n).2.trans hs.2⟩
  have hRw : ∀ n, derivWithin C.θ (Ioi s) s ≤ R (w n) := by
    intro n
    rw [← hpw n (hwmem n)]
    exact hanti (hwmem n) hs (hw n).2.le
  have hRtend' : Tendsto (fun n => R (w n)) atTop (𝓝 (R s)) :=
    (hR s hs).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hwlim
      (Eventually.of_forall hwmem))
  have h2 : derivWithin C.θ (Ioi s) s ≤ R s :=
    ge_of_tendsto hRtend' (Eventually.of_forall hRw)
  linarith

/-! ## Step 2: the lateral defect vanishes ⟹ the ODE in right-derivative form -/

/-- The right-hand side of the equality ODE, `-√(1-θ²)/θ`. -/
def odeRHS (C : Cap m) (s : ℝ) : ℝ := -(Real.sqrt (1 - (C.θ s) ^ 2)) / C.θ s

theorem continuousOn_odeRHS (C : Cap m) : ContinuousOn (odeRHS C) (Ioo (-C.K) 0) := by
  have hθ := Concave.continuousOn_Ioo C
  refine ContinuousOn.div ?_ hθ (fun s hs => ne_of_gt (C.θ_pos s hs))
  exact ((continuousOn_const.sub (hθ.pow 2)).sqrt).neg

/-- Interval integrability of the lateral defect integrand under `ProfileAC`
(domination by three times the area element). -/
theorem defectIntegrand_intervalIntegrable_of_profileAC (m : ℕ) (C : Cap m) (h : ProfileAC C) :
    IntervalIntegrable (Equality.defectIntegrand m C) volume (-C.K) 0 := by
  have hθm := h.aestronglyMeasurable_theta
  have hdm : AEStronglyMeasurable (deriv C.θ) (volume.restrict (Ioc (-C.K) 0)) :=
    (measurable_deriv C.θ).aestronglyMeasurable
  refine intervalIntegrable_of_le_areaElement_of_profileAC h _ ?_ 3 ?_
  · have h1 : AEStronglyMeasurable (fun s => Real.sqrt (1 + (deriv C.θ s) ^ 2))
        (volume.restrict (Ioc (-C.K) 0)) :=
      ((measurable_const.add ((measurable_deriv C.θ).pow_const 2)).sqrt).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun s => Real.sqrt (1 - (C.θ s) ^ 2))
        (volume.restrict (Ioc (-C.K) 0)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub (hθm.pow 2))
    exact (hθm.pow _).mul ((h1.add (hdm.mul h2)).sub hθm)
  · intro s hs
    have hle := Equality.norm_defectIntegrand_le m C s hs
    rw [Real.norm_eq_abs] at hle
    simpa only [Equality.areaElement] using hle

/-- **Lateral defect is nonnegative** under `ProfileAC`. -/
theorem lateralDefect_nonneg_of_profileAC (m : ℕ) (C : Cap m) (h : ProfileAC C) :
    0 ≤ C.lateralDefect := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  rw [Equality.lateralDefect_eq_integral]
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (omega_pos m).le) ?_
  have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-C.K) 0 := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hKle h0
    (defectIntegrand_intervalIntegrable_of_profileAC m C h) (Equality.defectIntegrand_nonneg m C)
  simpa using hmono

/-- Vanishing of the lateral defect forces the defect integrand to vanish a.e. -/
theorem ae_defectIntegrand_eq_zero (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileAC C)
    (hz : C.lateralDefect = 0) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo (-C.K) 0 → Equality.defectIntegrand m C s = 0 := by
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hint := defectIntegrand_intervalIntegrable_of_profileAC m C h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (-C.K) 0 ∪ Ioc 0 (-C.K))]
      Equality.defectIntegrand m C := by
    rw [Ioc_eq_empty (not_lt.mpr hKle), union_empty, ← uIoc_of_le hKle]
    exact Equality.ae_restrict_uIoc_of_forall_Ioo hKle (Equality.defectIntegrand_nonneg m C)
  have hI0 : ∫ s in (-C.K)..0, Equality.defectIntegrand m C s = 0 := by
    have hpos : 0 < (m : ℝ) * omega m := by
      refine mul_pos ?_ (omega_pos m)
      exact_mod_cast (show 0 < m by omega)
    rw [Equality.lateralDefect_eq_integral] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)
  have hae := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hI0
  have hae' : Equality.defectIntegrand m C =ᵐ[volume.restrict (Ioo (-C.K) 0)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioc_self.trans subset_union_left) hae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at hae'
  filter_upwards [hae'] with x hx hxm
  simpa using hx hxm

/-- **The profile ODE in right-derivative form.**  If the lateral defect vanishes
then, at *every* point of `(-K,0)`, the profile has right derivative
`-√(1-θ²)/θ`. -/
theorem equalityODE_right_of_lateralDefect_eq_zero (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (h : ProfileAC C) (hz : C.lateralDefect = 0) :
    ∀ s ∈ Ioo (-C.K) 0,
      HasDerivWithinAt C.θ (-(Real.sqrt (1 - (C.θ s) ^ 2)) / C.θ s) (Ioi s) s := by
  have hzero := ae_defectIntegrand_eq_zero m hm C h hz
  have hrd := Concave.rightDeriv_ae_eq_deriv C
  have hae : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) 0)),
      derivWithin C.θ (Ioi s) s = odeRHS C s := by
    have hzero' : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) 0)),
        Equality.defectIntegrand m C s = 0 := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact hzero
    have hmem : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) 0)), s ∈ Ioo (-C.K) 0 :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [hzero', hrd, hmem] with s h0 hd hsm
    rw [hd]
    have hθ := C.θ_pos s hsm
    rw [Equality.defectIntegrand] at h0
    have hbr := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (ne_of_gt hθ))
    exact (Equality.defect_bracket_eq_zero_iff hθ (C.θ_le_one s hsm)).mp hbr
  have key := rightDeriv_eq_of_ae_eq_continuous C (odeRHS C) (continuousOn_odeRHS C) hae
  intro s hs
  have hderiv := Concave.hasDerivWithinAt_Ioi C hs
  rw [key s hs] at hderiv
  simpa only [odeRHS] using hderiv

/-! ## Step 3: integrating the ODE with right derivatives -/

/-- Along the ODE (in right-derivative form), `h = √(1-θ²)` has right derivative
`1` wherever `0 < θ < 1`. -/
theorem hasDerivWithinAt_sqrt_one_sub_sq {θ : ℝ → ℝ} {s d : ℝ}
    (hd : HasDerivWithinAt θ d (Ioi s) s) (h0 : 0 < θ s) (h1 : θ s < 1)
    (hode : d = -(Real.sqrt (1 - (θ s) ^ 2)) / θ s) :
    HasDerivWithinAt (fun t => Real.sqrt (1 - (θ t) ^ 2)) 1 (Ioi s) s := by
  have hu : 0 < 1 - (θ s) ^ 2 := by nlinarith
  have hsq : HasDerivWithinAt (fun t => 1 - (θ t) ^ 2) (-(2 * θ s * d)) (Ioi s) s := by
    have hp := (hd.fun_pow 2).const_sub 1
    refine hp.congr_deriv ?_
    push_cast
    ring
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp_hasDerivWithinAt s hsq
  have hval : 1 / (2 * Real.sqrt (1 - (θ s) ^ 2)) * -(2 * θ s * d) = 1 := by
    rw [hode]
    have hsne : Real.sqrt (1 - (θ s) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
    field_simp
  have hfun : (Real.sqrt ∘ fun t => 1 - (θ t) ^ 2) = fun t => Real.sqrt (1 - (θ t) ^ 2) := rfl
  rw [hfun] at hsqrt
  exact hsqrt.congr_deriv hval

/-- **The ODE (in right-derivative form) together with `θ(0) = 0` forces the
equality profile.**  Exactly the `C¹` argument of
`Equality.equalityProfile_of_equalityODE`, with the one-sided fundamental
theorem of calculus in place of the two-sided one. -/
theorem equalityProfile_of_rightODE (m : ℕ) (C : Cap m) (h : ProfileAC C)
    (hode : ∀ s ∈ Ioo (-C.K) 0,
      HasDerivWithinAt C.θ (-(Real.sqrt (1 - (C.θ s) ^ 2)) / C.θ s) (Ioi s) s)
    (h0 : C.θ 0 = 0) : EqualityProfile C := by
  have hcont := h.continuousOn
  have hent := h.entrance
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  set g : ℝ → ℝ := fun t => Real.sqrt (1 - (C.θ t) ^ 2) with hg
  have hgcont : ContinuousOn g (Icc (-C.K) 0) := (continuousOn_const.sub (hcont.pow 2)).sqrt
  have hg0 : g 0 = 1 := by simp [hg, h0]
  -- FTC on `[a, 0]` whenever `θ < 1` on `(a, 0)`
  have hFTC : ∀ a ∈ Icc (-C.K) 0, (∀ s ∈ Ioo a 0, C.θ s < 1) → g a = a + 1 := by
    intro a ha hlt
    have hsub : Icc a 0 ⊆ Icc (-C.K) 0 := Icc_subset_Icc ha.1 le_rfl
    have hsub' : Ioo a 0 ⊆ Ioo (-C.K) 0 := Ioo_subset_Ioo ha.1 le_rfl
    have hI : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a 0 := intervalIntegrable_const
    have hF := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (f := g) (f' := fun _ : ℝ => (1 : ℝ)) ha.2 (hgcont.mono hsub)
      (fun s hs => hasDerivWithinAt_sqrt_one_sub_sq (hode s (hsub' hs)) (C.θ_pos s (hsub' hs))
        (hlt s hs) rfl) hI
    rw [intervalIntegral.integral_const, hg0, smul_eq_mul, mul_one] at hF
    linarith
  -- the closed set where `θ = 1`, and its supremum
  set T : Set ℝ := Icc (-C.K) 0 ∩ C.θ ⁻¹' {1} with hT
  have hTclosed : IsClosed T :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := ⟨-C.K, ⟨⟨le_rfl, hKle⟩, by simpa using hent⟩⟩
  have hTbdd : BddAbove T := ⟨0, fun x hx => hx.1.2⟩
  set s₀ := sSup T with hs₀
  have hs₀mem : s₀ ∈ T := hTclosed.csSup_mem hTne hTbdd
  have hs₀Icc : s₀ ∈ Icc (-C.K) 0 := hs₀mem.1
  have hθs₀ : C.θ s₀ = 1 := by simpa using hs₀mem.2
  have hs₀ne : s₀ ≠ 0 := by
    intro hzz
    rw [hzz, h0] at hθs₀
    norm_num at hθs₀
  have hs₀lt : s₀ < 0 := lt_of_le_of_ne hs₀Icc.2 hs₀ne
  have hlt : ∀ s ∈ Ioo s₀ 0, C.θ s < 1 := by
    intro s hs
    have hsIoo : s ∈ Ioo (-C.K) 0 := ⟨lt_of_le_of_lt hs₀Icc.1 hs.1, hs.2⟩
    refine lt_of_le_of_ne (C.θ_le_one s hsIoo) (fun heq => ?_)
    have hsT : s ∈ T := ⟨⟨hsIoo.1.le, hs.2.le⟩, by simpa using heq⟩
    exact absurd (le_csSup hTbdd hsT) (not_le.mpr hs.1)
  have hgs₀ : g s₀ = 0 := by simp [hg, hθs₀]
  have hs₀eq : s₀ = -1 := by
    have := hFTC s₀ hs₀Icc hlt
    linarith
  have hK1 : 1 ≤ C.K := by linarith [hs₀Icc.1]
  refine ⟨hK1, ?_, ?_⟩
  · intro s hs
    have hsIoo : s ∈ Ioo (-C.K) 0 := ⟨hs.1, by linarith [hs.2]⟩
    have hs₀Ioo : s₀ ∈ Ioo (-C.K) 0 := ⟨by linarith [hs.1, hs.2], hs₀lt⟩
    have hmono := C.θ_antitone hsIoo hs₀Ioo (by rw [hs₀eq]; exact hs.2.le)
    rw [hθs₀] at hmono
    exact le_antisymm (C.θ_le_one s hsIoo) hmono
  · intro s hs
    have hsIoo : s ∈ Ioo (-C.K) 0 := ⟨by linarith [hs.1], hs.2⟩
    have hgs : g s = s + 1 :=
      hFTC s ⟨hsIoo.1.le, hs.2.le⟩
        (fun t ht => hlt t ⟨by rw [hs₀eq]; linarith [ht.1, hs.1], ht.2⟩)
    have hθpos := C.θ_pos s hsIoo
    have hθle := C.θ_le_one s hsIoo
    have hsq : (g s) ^ 2 = 1 - (C.θ s) ^ 2 := Real.sq_sqrt (by nlinarith)
    rw [hgs] at hsq
    have hθsq : (C.θ s) ^ 2 = 1 - (s + 1) ^ 2 := by linarith
    rw [← hθsq, Real.sqrt_sq hθpos.le]

/-- **Equality forces the equality profile, for every admissible profile.** -/
theorem equalityProfile_of_profileAC (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileAC C)
    (hF : C.revolutionF = omega (m + 1) / 2) : EqualityProfile C := by
  have hD := defectIdentity_of_profileAC m hm C h
  have hθ0 := h.theta_zero_nonneg
  have hL := lateralDefect_nonneg_of_profileAC m C h
  have hT := Equality.terminalDefect_nonneg m hm C hθ0
  have hsum : C.lateralDefect + C.terminalDefect = 0 := by
    unfold DefectIdentity at hD
    linarith
  have hL0 : C.lateralDefect = 0 := by linarith
  have hT0 : C.terminalDefect = 0 := by linarith
  exact equalityProfile_of_rightODE m C h
    (equalityODE_right_of_lateralDefect_eq_zero m hm C h hL0)
    ((Equality.terminalDefect_eq_zero_iff m hm C hθ0).mp hT0)

/-! ## Step 4: the converse, under `ProfileAC` -/

/-- Under `ProfileAC` and the equality profile, the terminal radius vanishes. -/
theorem theta_zero_eq_zero_of_equalityProfile (m : ℕ) (C : Cap m) (h : ProfileAC C)
    (hp : EqualityProfile C) : C.θ 0 = 0 := by
  obtain ⟨hK1, _, hright⟩ := hp
  have hKle : (-C.K : ℝ) ≤ 0 := neg_nonpos.mpr C.hK.le
  have hcw : ContinuousWithinAt C.θ (Icc (-C.K) 0) 0 := h.continuousOn 0 ⟨hKle, le_rfl⟩
  have hsub : Ioo (-1 : ℝ) 0 ⊆ Icc (-C.K) 0 := fun x hx => ⟨by linarith [hx.1], hx.2.le⟩
  have h1 : Tendsto C.θ (𝓝[Ioo (-1 : ℝ) 0] 0) (𝓝 (C.θ 0)) :=
    hcw.tendsto.mono_left (nhdsWithin_mono _ hsub)
  have hsemi_cont : Continuous (semi 1) := by
    apply Continuous.sqrt
    fun_prop
  have h2 : Tendsto C.θ (𝓝[Ioo (-1 : ℝ) 0] 0) (𝓝 0) := by
    have hsemi : Tendsto (semi 1) (𝓝[Ioo (-1 : ℝ) 0] 0) (𝓝 (semi 1 0)) :=
      hsemi_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h00 : semi 1 0 = 0 := by simp [semi]
    rw [h00] at hsemi
    refine hsemi.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hright x hx).symm
  haveI : (𝓝[Ioo (-1 : ℝ) 0] 0).NeBot := right_nhdsWithin_Ioo_neBot (by norm_num)
  exact tendsto_nhds_unique h1 h2

/-- **The equality profile attains the sharp bound, under `ProfileAC`.**  (The
`C¹` hypothesis of `Equality.revolutionF_eq_of_equalityProfile` was used only for
`θ(0) = 0` and for integrability of the area element; both hold under
`ProfileAC`.) -/
theorem revolutionF_eq_of_equalityProfile_AC (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (h : ProfileAC C)
    (hp : EqualityProfile C) : C.revolutionF = omega (m + 1) / 2 := by
  have h0 := theta_zero_eq_zero_of_equalityProfile m C h hp
  have hAC : IntervalIntegrable (Equality.areaElement m C) volume (-C.K) 0 :=
    h.areaElement_intervalIntegrable
  obtain ⟨hK1, hleft, hright⟩ := hp
  have hsemi0 : semi 1 0 = 0 := by simp [semi]
  rw [revF_eq]
  rcases eq_or_lt_of_le hK1 with hK | hK
  · -- `K = 1`: the profile is the hemisphere off the null set `{0}`.
    rw [← hK]
    rw [Equality.revF_congr_of_eqOn m one_pos (θ₂ := semi 1) (-1)
      (fun x hx _ => hright x hx) (by rw [h0, hsemi0])]
    exact Equality.revF_semi_one m hm
  · -- `K > 1`: a hemisphere extended by a cylinder of length `K - 1`.
    have hδ : 0 < C.K - 1 := by linarith
    have hcongr : revF m C.K C.θ = revF m C.K (appendProfile 1 (C.K - 1) (semi 1)) := by
      apply Equality.revF_congr_of_eqOn m C.hK (-1)
      · intro x hx hxp
        rcases lt_or_gt_of_ne hxp with hlt | hgt
        · rw [appendProfile_cyl _ _ _ hlt]
          exact hleft x ⟨hx.1, hlt⟩
        · rw [appendProfile_cap _ _ _ hgt]
          exact hright x ⟨hgt, hx.2⟩
      · rw [appendProfile_cap _ _ _ (by norm_num), h0, hsemi0]
    rw [hcongr]
    have hsemi_cont : Continuous (semi 1) := by
      apply Continuous.sqrt
      fun_prop
    have hintV : IntervalIntegrable (fun s => (semi 1 s) ^ m) volume (-1) 0 :=
      (hsemi_cont.pow m).intervalIntegrable _ _
    have hintL : IntervalIntegrable
        (fun s => (semi 1 s) ^ (m - 1) * Real.sqrt (1 + (deriv (semi 1) s) ^ 2))
        volume (-1) 0 := by
      have hsub : uIcc (-1 : ℝ) 0 ⊆ uIcc (-C.K) 0 := by
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), uIcc_of_le (by linarith : (-C.K : ℝ) ≤ 0)]
        exact Icc_subset_Icc (by linarith) le_rfl
      have hA := hAC.mono_set hsub
      refine hA.congr_ae (Equality.ae_restrict_uIoc_of_forall_Ioo (by norm_num) ?_)
      intro x hx
      have hxne : x ≠ -1 := ne_of_gt hx.1
      have hθx : C.θ x = semi 1 x := hright x hx
      have hdx : deriv C.θ x = deriv (semi 1) x :=
        Equality.deriv_eq_of_eqOn_Ioo_ne (a := -1) (b := 0) (p := -1)
          (fun y hy _ => hright y hy) hx hxne
      simp only [Equality.areaElement, hθx, hdx]
    set δ := C.K - 1 with hδdef
    have hKeq : C.K = 1 + δ := by rw [hδdef]; ring
    rw [hKeq, revF_append m 1 δ hδ one_pos (semi 1) hintL hintV]
    exact Equality.revF_semi_one m hm

/-! ## Step 5: the full equality characterisation -/

/-- **Equality characterisation for every admissible cap** (manuscript
`thm:calibration`, equality case).  No regularity beyond the `Cap` structure and
the two endpoint-value conventions is assumed. -/
theorem equality_iff_AC (m : ℕ) (hm : 1 ≤ m) (C : Cap m) (hK : C.θ (-C.K) = 1)
    (h0 : TerminalContinuous C) :
    C.F = omega (m + 1) / 2 ↔ EqualityProfile C := by
  have h := Concave.profileAC_of_cap C hK h0
  rw [F_eq_revolutionF]
  exact ⟨fun hF => equalityProfile_of_profileAC m hm C h hF,
    fun hp => revolutionF_eq_of_equalityProfile_AC m hm C h hp⟩

end EqualityAC

end

end Cap
end RobinCaps
