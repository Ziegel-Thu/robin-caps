import Mathlib
import RobinCaps.Cap.Basic
import RobinCaps.Cap.Regular

/-!
# Automatic regularity of admissible cap profiles

Every admissible profile `θ` of a `Cap` (concave, non-increasing, `0 < θ ≤ 1` on the open
interval `(-K,0)`) automatically has the weak regularity `ProfileAC` needed by the
sharp-inequality proof:

* `continuousOn_Ioo`: `θ` is continuous on `(-K,0)` (concave on an open set);
* `exists_terminalRadius`: the left limit `θ(0⁻)` exists and lies in `[0,1]`;
* `hasDerivWithinAt_Ioi` / `hasDerivWithinAt_Iio`: one-sided derivatives exist everywhere on
  `(-K,0)`; the right derivative is `≤ 0` and antitone;
* `countable_not_differentiableAt`: `θ` is differentiable off a countable set;
* `rightDeriv_integrableOn`, `deriv_integrableOn`, `areaElement_intervalIntegrable`:
  the derivative is (improperly) integrable on `(-K,0)`, hence so is the area element
  `θ^{m-1}√(1+θ'²)`;
* `profileAC_of_cap`: assembly of `ProfileAC` from the entrance value `θ(-K) = 1` and
  left-continuity at the terminal point.

Mathlib (at this version) has no `rightDeriv` function; the right derivative at `s` is written
`derivWithin C.θ (Set.Ioi s) s` throughout, and the left derivative `derivWithin C.θ (Set.Iio s) s`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps.Cap.Concave

variable {m : ℕ}

/-! ### Tier 1: continuity on the open interval -/

/-- A concave function on an open interval is continuous there. -/
theorem continuousOn_Ioo (C : Cap m) : ContinuousOn C.θ (Ioo (-C.K) 0) :=
  C.θ_concave.continuousOn isOpen_Ioo

theorem nonempty_Ioo (C : Cap m) : (Ioo (-C.K) 0).Nonempty :=
  Set.nonempty_Ioo.2 (by linarith [C.hK])

/-! ### Tier 2: existence of the terminal radius `θ(0⁻)` -/

/-- An antitone profile bounded between `0` and `1` has a left limit at the terminal point. -/
theorem exists_terminalRadius (C : Cap m) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ Tendsto C.θ (𝓝[<] (0 : ℝ)) (𝓝 r) := by
  have hne : (Ioo (-C.K) 0).Nonempty := nonempty_Ioo C
  have hbdd : BddBelow (C.θ '' Ioo (-C.K) 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact (C.θ_pos s hs).le
  refine ⟨sInf (C.θ '' Ioo (-C.K) 0), ?_, ?_, ?_⟩
  · apply le_csInf (hne.image _)
    rintro _ ⟨s, hs, rfl⟩
    exact (C.θ_pos s hs).le
  · obtain ⟨s, hs⟩ := hne
    exact csInf_le_of_le hbdd (mem_image_of_mem _ hs) (C.θ_le_one s hs)
  · exact C.θ_antitone.tendsto_nhdsWithin_Ioo_left hne hbdd

/-! ### Tier 3: one-sided derivatives and the countable exceptional set -/

theorem mem_interior_Ioo {C : Cap m} {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    s ∈ interior (Ioo (-C.K) 0) := by
  rwa [interior_Ioo]

/-- `-θ` is convex on `(-K,0)`. -/
theorem convexOn_neg (C : Cap m) : ConvexOn ℝ (Ioo (-C.K) 0) (-C.θ) := C.θ_concave.neg

/-- The right derivative exists at every point of `(-K,0)`. -/
theorem hasDerivWithinAt_Ioi (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    HasDerivWithinAt C.θ (derivWithin C.θ (Ioi s) s) (Ioi s) s := by
  have h := ((convexOn_neg C).hasDerivWithinAt_rightDeriv_of_mem_interior
    (mem_interior_Ioo hs)).neg
  rw [derivWithin.neg] at h
  simpa using h

/-- The left derivative exists at every point of `(-K,0)`. -/
theorem hasDerivWithinAt_Iio (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    HasDerivWithinAt C.θ (derivWithin C.θ (Iio s) s) (Iio s) s := by
  have h := ((convexOn_neg C).hasDerivWithinAt_leftDeriv_of_mem_interior
    (mem_interior_Ioo hs)).neg
  rw [derivWithin.neg] at h
  simpa using h

/-- For a concave profile the right derivative is at most the left derivative. -/
theorem rightDeriv_le_leftDeriv (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    derivWithin C.θ (Ioi s) s ≤ derivWithin C.θ (Iio s) s := by
  have h := (convexOn_neg C).leftDeriv_le_rightDeriv_of_mem_interior (mem_interior_Ioo hs)
  simp only [derivWithin.neg, neg_le_neg_iff] at h
  exact h

/-- The right derivative of a concave profile is antitone on `(-K,0)`. -/
theorem antitoneOn_rightDeriv (C : Cap m) :
    AntitoneOn (fun s => derivWithin C.θ (Ioi s) s) (Ioo (-C.K) 0) := by
  have h := (convexOn_neg C).monotoneOn_rightDeriv
  rw [interior_Ioo] at h
  intro x hx y hy hxy
  have := h hx hy hxy
  simp only [derivWithin.neg, neg_le_neg_iff] at this
  exact this

/-- The right derivative of a non-increasing profile is non-positive. -/
theorem rightDeriv_nonpos (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    derivWithin C.θ (Ioi s) s ≤ 0 := by
  set z : ℝ := (-C.K + s) / 2 with hz
  have hzs : z < s := by rw [hz]; linarith [hs.1]
  have hzI : z ∈ Ioo (-C.K) 0 :=
    ⟨by rw [hz]; linarith [hs.1], by rw [hz]; linarith [hs.1, hs.2]⟩
  have h1 := (convexOn_neg C).slope_le_leftDeriv_of_mem_interior hzI (mem_interior_Ioo hs) hzs
  have h2 := (convexOn_neg C).leftDeriv_le_rightDeriv_of_mem_interior (mem_interior_Ioo hs)
  have h3 : 0 ≤ slope (-C.θ) z s := by
    rw [slope_def_field]
    apply div_nonneg
    · have := C.θ_antitone hzI hs hzs.le
      simp only [Pi.neg_apply]
      linarith
    · linarith
  simp only [derivWithin.neg] at h1 h2
  linarith

/-- The set of points of `(-K,0)` where the right derivative is not continuous (within the
interval) is countable. -/
theorem countable_not_continuousWithinAt_rightDeriv (C : Cap m) :
    {s ∈ Ioo (-C.K) 0 |
      ¬ ContinuousWithinAt (fun s => derivWithin C.θ (Ioi s) s) (Ioo (-C.K) 0) s}.Countable :=
  (antitoneOn_rightDeriv C).countable_not_continuousWithinAt

/-- Where the right derivative is continuous, the profile is differentiable, with derivative
equal to the right derivative. -/
theorem hasDerivAt_of_continuousWithinAt (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0)
    (hc : ContinuousWithinAt (fun s => derivWithin C.θ (Ioi s) s) (Ioo (-C.K) 0) s) :
    HasDerivAt C.θ (derivWithin C.θ (Ioi s) s) s := by
  have hle : derivWithin C.θ (Iio s) s ≤ derivWithin C.θ (Ioi s) s := by
    have hIoo : Ioo (-C.K) 0 ∈ 𝓝[<] s :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hs.1 hs.2)
    have ht : Tendsto (fun s => derivWithin C.θ (Ioi s) s) (𝓝[<] s)
        (𝓝 (derivWithin C.θ (Ioi s) s)) :=
      hc.tendsto.mono_left (nhdsWithin_le_iff.2 hIoo)
    apply ge_of_tendsto ht
    filter_upwards [hIoo, self_mem_nhdsWithin] with z hz hzs
    have hzs' : z < s := hzs
    have h1 := (convexOn_neg C).rightDeriv_le_slope_of_mem_interior (mem_interior_Ioo hz) hs hzs'
    have h2 := (convexOn_neg C).slope_le_leftDeriv_of_mem_interior hz (mem_interior_Ioo hs) hzs'
    simp only [derivWithin.neg] at h1 h2
    linarith
  have heq : derivWithin C.θ (Iio s) s = derivWithin C.θ (Ioi s) s :=
    le_antisymm hle (rightDeriv_le_leftDeriv C hs)
  have hl := hasDerivWithinAt_Iio C hs
  rw [heq] at hl
  have h := hl.union (hasDerivWithinAt_Ioi C hs)
  rwa [Iio_union_Ioi, compl_eq_univ_diff, hasDerivWithinAt_diff_singleton,
    hasDerivWithinAt_univ] at h

/-- The profile is differentiable off a countable subset of `(-K,0)`. -/
theorem countable_not_differentiableAt (C : Cap m) :
    {s ∈ Ioo (-C.K) 0 | ¬ DifferentiableAt ℝ C.θ s}.Countable := by
  apply (countable_not_continuousWithinAt_rightDeriv C).mono
  rintro s ⟨hs, hnd⟩
  exact ⟨hs, fun hc => hnd (hasDerivAt_of_continuousWithinAt C hs hc).differentiableAt⟩

/-- The `ProfileAC` differentiability clause: `θ` has derivative `deriv θ` off a countable set. -/
theorem exists_countable_hasDerivAt (C : Cap m) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ s ∈ Ioo (-C.K) 0 \ S, HasDerivAt C.θ (deriv C.θ s) s := by
  refine ⟨_, countable_not_differentiableAt C, ?_⟩
  rintro s ⟨hs, hnS⟩
  simp only [mem_setOf_eq, not_and, not_not] at hnS
  exact (hnS hs).hasDerivAt

/-! ### Tier 4: integrability of the derivative and of the area element -/

/-- Fundamental theorem of calculus for the right derivative on compact subintervals. -/
theorem integral_rightDeriv (C : Cap m) {a b : ℝ} (ha : a ∈ Ioo (-C.K) 0)
    (hb : b ∈ Ioo (-C.K) 0) (hab : a ≤ b) :
    ∫ s in a..b, derivWithin C.θ (Ioi s) s = C.θ b - C.θ a := by
  have hIcc : Icc a b ⊆ Ioo (-C.K) 0 := Icc_subset_Ioo ha.1 hb.2
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    ((continuousOn_Ioo C).mono hIcc)
  · intro x hx
    exact hasDerivWithinAt_Ioi C (hIcc (Ioo_subset_Icc_self hx))
  · apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (antitoneOn_rightDeriv C).mono hIcc

/-- The right derivative is (improperly) integrable on `(-K,0)`: it is bounded near the
entrance and its integral over `[c, b]` equals `θ(c) - θ(b) ≤ 1` for `b → 0⁻`. -/
theorem rightDeriv_integrableOn (C : Cap m) :
    IntegrableOn (fun s => derivWithin C.θ (Ioi s) s) (Ioo (-C.K) 0) := by
  set g : ℝ → ℝ := fun s => derivWithin C.θ (Ioi s) s with hg
  set c : ℝ := -C.K / 2 with hc
  have hcI : c ∈ Ioo (-C.K) 0 := ⟨by rw [hc]; linarith [C.hK], by rw [hc]; linarith [C.hK]⟩
  have hmeas : Measurable g := measurable_derivWithin_Ioi C.θ
  -- near the entrance: bounded
  have h1 : IntegrableOn g (Ioc (-C.K) c) := by
    apply Measure.integrableOn_of_bounded (M := |g c|) measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ (fun x hx => ?_)
    have hxI : x ∈ Ioo (-C.K) 0 := ⟨hx.1, hx.2.trans_lt hcI.2⟩
    have hgx : g c ≤ g x := antitoneOn_rightDeriv C hxI hcI hx.2
    have hx0 : g x ≤ 0 := rightDeriv_nonpos C hxI
    have hc0 : g c ≤ 0 := rightDeriv_nonpos C hcI
    rw [Real.norm_eq_abs, abs_of_nonpos hx0, abs_of_nonpos hc0]
    linarith
  -- near the terminal point: FTC bound
  have h2 : IntegrableOn g (Ioc c 0) := by
    set b : ℕ → ℝ := fun n => c / 2 * (1 / ((n : ℝ) + 1)) with hb
    have hbI : ∀ n, b n ∈ Ioo c 0 := by
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have ht1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn]; linarith
      have ht0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have hcneg : c < 0 := hcI.2
      constructor
      · simp only [hb]; nlinarith
      · simp only [hb]; nlinarith
    have hbt : Tendsto b atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c / 2)
      simpa [hb] using this
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_right (I := 1) (b := b) ?_ hbt ?_
    · intro n
      have hsub : Icc c (b n) ⊆ Ioo (-C.K) 0 := Icc_subset_Ioo hcI.1 (hbI n).2
      have hint : IntervalIntegrable g volume c (b n) := by
        apply AntitoneOn.intervalIntegrable
        rw [uIcc_of_le (hbI n).1.le]
        exact (antitoneOn_rightDeriv C).mono hsub
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hbI n).1.le).1 hint
    · refine Eventually.of_forall (fun n => ?_)
      have hbn : b n ∈ Ioo (-C.K) 0 := ⟨hcI.1.trans (hbI n).1, (hbI n).2⟩
      have heq : ∫ x in Ioc c (b n), ‖g x‖ = ∫ x in Ioc c (b n), -g x := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hxI : x ∈ Ioo (-C.K) 0 := ⟨hcI.1.trans hx.1, hx.2.trans_lt hbn.2⟩
        show ‖g x‖ = -g x
        rw [Real.norm_eq_abs]
        exact abs_of_nonpos (rightDeriv_nonpos C hxI)
      rw [heq, ← intervalIntegral.integral_of_le (hbI n).1.le, intervalIntegral.integral_neg,
        integral_rightDeriv C hcI hbn (hbI n).1.le]
      linarith [C.θ_le_one c hcI, C.θ_pos (b n) hbn]
  have h12 := h1.union h2
  rw [Ioc_union_Ioc_eq_Ioc hcI.1.le hcI.2.le] at h12
  exact h12.mono_set Ioo_subset_Ioc_self

/-- On `(-K,0)`, `deriv θ` agrees a.e. with the right derivative. -/
theorem rightDeriv_ae_eq_deriv (C : Cap m) :
    (fun s => derivWithin C.θ (Ioi s) s) =ᵐ[volume.restrict (Ioo (-C.K) 0)] deriv C.θ := by
  have hS := countable_not_continuousWithinAt_rightDeriv C
  have hS0 : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ {s ∈ Ioo (-C.K) 0 |
      ¬ ContinuousWithinAt (fun s => derivWithin C.θ (Ioi s) s) (Ioo (-C.K) 0) s} := by
    rw [ae_iff]
    simpa [and_assoc] using hS.measure_zero volume
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hS0] with x hx hxI
  simp only [not_and, not_not] at hx
  exact ((hasDerivAt_of_continuousWithinAt C hxI (hx hxI)).deriv).symm

/-- `deriv θ` is (improperly) integrable on `(-K,0)`. -/
theorem deriv_integrableOn (C : Cap m) : IntegrableOn (deriv C.θ) (Ioo (-C.K) 0) :=
  (rightDeriv_integrableOn C).congr_fun_ae (rightDeriv_ae_eq_deriv C)

/-- The area element `θ^{m-1}√(1+θ'²)` is interval integrable on `(-K,0)`. -/
theorem areaElement_intervalIntegrable (C : Cap m) :
    IntervalIntegrable (fun s => C.θ s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2))
      volume (-C.K) 0 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [C.hK])]
  have hbound : IntegrableOn (fun s => 1 + |deriv C.θ s|) (Ioo (-C.K) 0) :=
    (integrableOn_const measure_Ioo_lt_top.ne).add (deriv_integrableOn C).abs
  have hmeas : AEStronglyMeasurable
      (fun s => C.θ s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2))
      (volume.restrict (Ioo (-C.K) 0)) := by
    have hθ : AEStronglyMeasurable C.θ (volume.restrict (Ioo (-C.K) 0)) :=
      (continuousOn_Ioo C).aestronglyMeasurable measurableSet_Ioo
    have h2 : Measurable (fun s => Real.sqrt (1 + deriv C.θ s ^ 2)) := by fun_prop
    exact (hθ.pow (m - 1)).mul h2.aestronglyMeasurable
  refine hbound.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine ae_of_all _ (fun s hs => ?_)
  have hθ0 := C.θ_pos s hs
  have hθ1 := C.θ_le_one s hs
  have hp : C.θ s ^ (m - 1) ≤ 1 := pow_le_one₀ hθ0.le hθ1
  have hp0 : 0 ≤ C.θ s ^ (m - 1) := by positivity
  have hsq : Real.sqrt (1 + deriv C.θ s ^ 2) ≤ 1 + |deriv C.θ s| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs (deriv C.θ s), abs_nonneg (deriv C.θ s)]
  have hsq0 : 0 ≤ Real.sqrt (1 + deriv C.θ s ^ 2) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 hsq0)]
  calc C.θ s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2)
      ≤ 1 * (1 + |deriv C.θ s|) := by gcongr
    _ = 1 + |deriv C.θ s| := one_mul _

/-! ### Tier 5: assembly -/

/-- Continuity on the closed interval, given the entrance value and left-continuity at `0`. -/
theorem continuousOn_Icc (C : Cap m) (hK : C.θ (-C.K) = 1) (h0 : TerminalContinuous C) :
    ContinuousOn C.θ (Icc (-C.K) 0) := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h | h
  · subst h
    have hcw : ContinuousWithinAt C.θ (Ioi (-C.K)) (-C.K) := by
      rw [ContinuousWithinAt, hK]
      exact C.θ_tendsto
    exact (continuousWithinAt_Ioi_iff_Ici.1 hcw).mono Icc_subset_Ici_self
  rcases eq_or_lt_of_le hs.2 with h' | h'
  · subst h'
    have hcw : ContinuousWithinAt C.θ (Iio 0) 0 := h0
    exact (continuousWithinAt_Iio_iff_Iic.1 hcw).mono Icc_subset_Iic_self
  · exact ((continuousOn_Ioo C).continuousAt (Ioo_mem_nhds h h')).continuousWithinAt

/-- **Every admissible cap profile is `ProfileAC`**, given the entrance value `θ(-K) = 1` and
left-continuity at the terminal point. -/
theorem profileAC_of_cap (C : Cap m) (hK : C.θ (-C.K) = 1) (h0 : TerminalContinuous C) :
    ProfileAC C :=
  ⟨continuousOn_Icc C hK h0, hK, exists_countable_hasDerivAt C, areaElement_intervalIntegrable C⟩

end RobinCaps.Cap.Concave
