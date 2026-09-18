import Mathlib
import RobinCaps.Cap.Concave
import RobinCaps.Cap.Unconditional
import RobinCaps.ThinDomain.Boundary

/-!
# The `r = θ(s)` substitution for the terminal chart

This file proves the change-of-variables inequality needed by the terminal chart of the trace
construction: near the terminal end of a cap, if the profile `θ` has slope `≤ -c < 0`
(a.e.) on an axial subinterval `(a,0)`, the lateral surface integral there is dominated by the
flat transverse integral over the annulus `θ(0) < ‖z‖ < θ(a)`.

All declarations carry the suffix `_ths`.
-/

open MeasureTheory Set Filter RobinCaps.ThinDomain
open scoped Topology ENNReal

namespace RobinCaps.Cap

variable {m : ℕ}

/-! ## 1. A point of strictly negative slope, or the flat alternative -/

/-- Either `θ ≡ 1` on `(-K,0)` (the cylindrical/flat profile), or there is `s* ∈ (-K,0)` at which
`θ` is differentiable with `deriv θ s* < 0`. -/
theorem exists_neg_slope_or_flat_ths (C : Cap m) :
    (∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) ∨
      ∃ s : ℝ, s ∈ Set.Ioo (-C.K) 0 ∧ DifferentiableAt ℝ C.θ s ∧ deriv C.θ s < 0 := by
  by_cases hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1
  · exact Or.inl hflat
  · right
    push_neg at hflat
    obtain ⟨s₀, hs₀, hne⟩ := hflat
    have hlt : C.θ s₀ < 1 := lt_of_le_of_ne (C.θ_le_one s₀ hs₀) hne
    -- find `a < s₀` in `Ioo(-K,0)` with `θ s₀ < θ a`, i.e. a genuine strict drop somewhere
    -- to the left of `s₀`
    obtain ⟨a, haI, has₀, hgt⟩ : ∃ a, a ∈ Set.Ioo (-C.K) 0 ∧ a < s₀ ∧ C.θ s₀ < C.θ a := by
      by_contra hcon
      push_neg at hcon
      have hconst : ∀ a ∈ Set.Ioo (-C.K) s₀, C.θ a = C.θ s₀ := by
        intro a ha
        have haI : a ∈ Set.Ioo (-C.K) 0 := ⟨ha.1, ha.2.trans hs₀.2⟩
        have h1 := C.θ_antitone haI hs₀ ha.2.le
        have h2 := hcon a haI ha.2
        linarith
      have hmem : Set.Ioo (-C.K) s₀ ∈ 𝓝[>] (-C.K) := Ioo_mem_nhdsGT hs₀.1
      have htendsto : Tendsto C.θ (𝓝[>] (-C.K)) (𝓝 (C.θ s₀)) := by
        have hconst' : Tendsto (fun _ : ℝ => C.θ s₀) (𝓝[>] (-C.K)) (𝓝 (C.θ s₀)) :=
          tendsto_const_nhds
        exact hconst'.congr' (Filter.eventuallyEq_of_mem hmem (fun x hx => (hconst x hx).symm))
      have heq := tendsto_nhds_unique htendsto C.θ_tendsto
      exact absurd heq hlt.ne
    have hint : ∫ s in a..s₀, derivWithin C.θ (Set.Ioi s) s = C.θ s₀ - C.θ a :=
      Concave.integral_rightDeriv C haI hs₀ has₀.le
    have hneg : ∫ s in a..s₀, derivWithin C.θ (Set.Ioi s) s < 0 := by rw [hint]; linarith
    by_contra hcon
    push_neg at hcon
    -- `hcon : ∀ s ∈ Ioo(-K,0), DifferentiableAt θ s → 0 ≤ deriv θ s`
    have hae0 : ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
        derivWithin C.θ (Set.Ioi s) s = 0 := by
      have hSc := Concave.countable_not_differentiableAt C
      have hSae : ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
          s ∉ {s ∈ Set.Ioo (-C.K) 0 | ¬ DifferentiableAt ℝ C.θ s} :=
        hSc.ae_notMem _
      have hmemae : ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)), s ∈ Set.Ioo (-C.K) 0 :=
        ae_restrict_mem measurableSet_Ioo
      have hreq := Concave.rightDeriv_ae_eq_deriv C
      filter_upwards [hSae, hmemae, hreq] with s hSae hmem hreq
      simp only [not_and, not_not] at hSae
      have hdiff : DifferentiableAt ℝ C.θ s := hSae hmem
      have hnonneg : 0 ≤ deriv C.θ s := hcon s hmem hdiff
      have hnonpos : derivWithin C.θ (Set.Ioi s) s ≤ 0 := Concave.rightDeriv_nonpos C hmem
      rw [hreq]
      linarith
    have hae0'' : ∀ᵐ s ∂volume, s ∈ Set.Ioo (-C.K) 0 → derivWithin C.θ (Set.Ioi s) s = 0 :=
      (ae_restrict_iff' measurableSet_Ioo).1 hae0
    have hsub : Set.Ioc a s₀ ⊆ Set.Ioo (-C.K) 0 :=
      fun x hx => ⟨haI.1.trans hx.1, hx.2.trans_lt hs₀.2⟩
    have hae0' : ∀ᵐ x ∂volume, x ∈ Set.Ioc a s₀ → derivWithin C.θ (Set.Ioi x) x = 0 := by
      filter_upwards [hae0''] with x hx hmem
      exact hx (hsub hmem)
    have hzero : ∫ s in a..s₀, derivWithin C.θ (Set.Ioi s) s = ∫ _s in a..s₀, (0:ℝ) := by
      apply intervalIntegral.integral_congr_ae'
      · rwa [] at hae0'
      · exact Filter.Eventually.of_forall
          (fun x hx => absurd hx (by simp [Set.Ioc_eq_empty_of_le has₀.le]))
    rw [hzero] at hneg
    simp at hneg

/-! ## 4. Strict monotonicity under a lower bound on the slope -/

/-- On an interval `[a,0)` where `deriv θ ≤ -c < 0` a.e. on `(a,0)`, `θ` is strictly
decreasing (in particular strictly below its value `θ a` at the left endpoint). -/
theorem strictAntiOn_of_slope_ths (C : Cap m) {a c : ℝ} (ha : a ∈ Set.Ioo (-C.K) 0) (hc : 0 < c)
    (hslope : ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)), deriv C.θ s ≤ -c) :
    StrictAntiOn C.θ (Set.Ico a 0) := by
  have hsubK : Set.Ioo a 0 ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨ha.1.trans hz.1, hz.2⟩
  intro x hx y hy hxy
  have hxI : x ∈ Set.Ioo (-C.K) 0 := ⟨ha.1.trans_le hx.1, hx.2⟩
  have hyI : y ∈ Set.Ioo (-C.K) 0 := ⟨ha.1.trans_le hy.1, hy.2⟩
  have hint : ∫ s in x..y, derivWithin C.θ (Set.Ioi s) s = C.θ y - C.θ x :=
    Concave.integral_rightDeriv C hxI hyI hxy.le
  have hxyIoo : Set.Ioo x y ⊆ Set.Ioo a 0 := fun z hz => ⟨hx.1.trans_lt hz.1, hz.2.trans hy.2⟩
  have hcomb : ∀ᵐ s ∂(volume.restrict (Set.Ioo x y)), derivWithin C.θ (Set.Ioi s) s ≤ -c := by
    have h1 : (fun s => derivWithin C.θ (Set.Ioi s) s)
        =ᵐ[volume.restrict (Set.Ioo x y)] deriv C.θ :=
      ae_restrict_of_ae_restrict_of_subset (hxyIoo.trans hsubK) (Concave.rightDeriv_ae_eq_deriv C)
    have h2 : ∀ᵐ s ∂(volume.restrict (Set.Ioo x y)), deriv C.θ s ≤ -c :=
      ae_restrict_of_ae_restrict_of_subset hxyIoo hslope
    filter_upwards [h1, h2] with s h1 h2
    rw [h1]; exact h2
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hcomb
  have hIcc : Set.Icc x y ⊆ Set.Ioo (-C.K) 0 := Set.Icc_subset_Ioo hxI.1 hyI.2
  have hfInt : IntervalIntegrable (fun s => derivWithin C.θ (Set.Ioi s) s) volume x y := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hxy.le]
    exact (Concave.antitoneOn_rightDeriv C).mono hIcc
  have hgInt : IntervalIntegrable (fun _ : ℝ => (-c : ℝ)) volume x y := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_ae_restrict hxy.le hfInt hgInt hcomb
  rw [hint, intervalIntegral.integral_const, smul_eq_mul] at hmono
  nlinarith [hmono]

/-! ## 2. The pointwise estimate -/

/-- **Pointwise estimate.**  Where the slope is `≤ -c < 0`, the area element
`θ^{m-1}√(1+θ'²)` is dominated by `√(1+c⁻²) |θ'| θ^{m-1}`. -/
theorem capAreaElement_le_ths (C : Cap m) {s c : ℝ} (hs : s ∈ Set.Ioo (-C.K) 0) (hc : 0 < c)
    (hslope : deriv C.θ s ≤ -c) :
    capAreaElement C s
      ≤ Real.sqrt (1 + c⁻¹ ^ 2) * (-deriv C.θ s) * C.θ s ^ (m - 1) := by
  have hθ0 : 0 ≤ C.θ s := (C.θ_pos s hs).le
  have hθpow : 0 ≤ C.θ s ^ (m - 1) := pow_nonneg hθ0 _
  have ht0 : 0 ≤ -deriv C.θ s := by linarith
  have ht : c ≤ -deriv C.θ s := by linarith
  have hc2 : c ^ 2 ≤ (-deriv C.θ s) ^ 2 := by nlinarith
  have hinv : c⁻¹ ^ 2 * c ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hc.ne', one_pow]
  have hstep : (1:ℝ) ≤ c⁻¹ ^ 2 * (-deriv C.θ s) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hc2 (sq_nonneg c⁻¹)
    rwa [hinv] at h
  have hkey : 1 + (deriv C.θ s) ^ 2 ≤ (1 + c⁻¹ ^ 2) * (-deriv C.θ s) ^ 2 := by
    calc 1 + (deriv C.θ s) ^ 2 = 1 + (-deriv C.θ s) ^ 2 := by rw [neg_sq]
      _ ≤ c⁻¹ ^ 2 * (-deriv C.θ s) ^ 2 + (-deriv C.θ s) ^ 2 := by linarith [hstep]
      _ = (1 + c⁻¹ ^ 2) * (-deriv C.θ s) ^ 2 := by ring
  have hrw : Real.sqrt (1 + c⁻¹ ^ 2) * (-deriv C.θ s)
      = Real.sqrt ((1 + c⁻¹ ^ 2) * (-deriv C.θ s) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ht0]
  have hbound : Real.sqrt (1 + deriv C.θ s ^ 2) ≤ Real.sqrt (1 + c⁻¹ ^ 2) * (-deriv C.θ s) := by
    rw [hrw]; exact Real.sqrt_le_sqrt hkey
  calc capAreaElement C s = C.θ s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2) := rfl
    _ ≤ C.θ s ^ (m - 1) * (Real.sqrt (1 + c⁻¹ ^ 2) * (-deriv C.θ s)) :=
        mul_le_mul_of_nonneg_left hbound hθpow
    _ = Real.sqrt (1 + c⁻¹ ^ 2) * (-deriv C.θ s) * C.θ s ^ (m - 1) := by ring

/-! ## 3. The substitution inequality, `lintegral` version -/

/-- **The `r = θ(s)` substitution, `lintegral` version.**  On an axial interval `(a,0)` on
which the profile has slope `≤ -c < 0` a.e., the lateral surface integral is dominated by the
flat transverse integral over the ball `‖z‖ < θ(a)`. -/
theorem lateral_le_annulus_lintegral_ths (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (ha : a ∈ Set.Ioo (-C.K) 0) (hc : 0 < c)
    (hslope : ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)), deriv C.θ s ≤ -c)
    {H : EuclideanSpace ℝ (Fin m) → ℝ≥0∞} (hHmeas : Measurable H) :
    (∫⁻ s in Set.Ioo a 0, ENNReal.ofReal (capAreaElement C s)
        * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2))
          * ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), H z := by
  classical
  have hsubK : Set.Ioo a 0 ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨ha.1.trans hz.1, hz.2⟩
  -- the countable non-differentiability set
  set S : Set ℝ := {s ∈ Set.Ioo (-C.K) 0 | ¬ DifferentiableAt ℝ C.θ s} with hS_def
  have hSc : S.Countable := Concave.countable_not_differentiableAt C
  -- the "good" set: differentiable, and slope `≤ -c`
  set G : Set ℝ := (Set.Ioo a 0 \ S) ∩ {x : ℝ | deriv C.θ x ≤ -c} with hG_def
  have hGsub : G ⊆ Set.Ioo a 0 := fun x hx => hx.1.1
  have hderiv_meas : Measurable (deriv C.θ) := measurable_deriv C.θ
  have hBadmeas : MeasurableSet {x : ℝ | deriv C.θ x ≤ -c} := hderiv_meas measurableSet_Iic
  have hGmeas : MeasurableSet G := by
    rw [hG_def]
    exact (measurableSet_Ioo.diff hSc.measurableSet).inter hBadmeas
  have hGdiffAt : ∀ x ∈ G, DifferentiableAt ℝ C.θ x := by
    intro x hx
    rw [hG_def] at hx
    have hxnS : x ∉ S := hx.1.2
    have hxK : x ∈ Set.Ioo (-C.K) 0 := hsubK hx.1.1
    rw [hS_def] at hxnS
    simp only [Set.mem_setOf_eq, not_and, not_not] at hxnS
    exact hxnS hxK
  have hGslope : ∀ x ∈ G, deriv C.θ x ≤ -c := by
    intro x hx; rw [hG_def] at hx; exact hx.2
  have hGdiff : ∀ x ∈ G, HasDerivWithinAt C.θ (deriv C.θ x) G x :=
    fun x hx => (hGdiffAt x hx).hasDerivAt.hasDerivWithinAt
  have hGantitone : AntitoneOn C.θ G := C.θ_antitone.mono (hGsub.trans hsubK)
  -- the radial density
  set u : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (m - 1))
      * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          H (r • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) with hu_def
  -- the lateral density
  set v : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (capAreaElement C s)
      * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) with hv_def
  have hcov : ∫⁻ x in C.θ '' G, u x = ∫⁻ x in G, ENNReal.ofReal (-deriv C.θ x) * u (C.θ x) :=
    lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hGmeas hGdiff hGantitone u
  -- pointwise bound: `v ≤ √(1+c⁻²) * (ofReal(-deriv θ) * u∘θ)` on `G`
  have hptwise : ∀ x ∈ G, v x ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2))
      * (ENNReal.ofReal (-deriv C.θ x) * u (C.θ x)) := by
    intro x hx
    have hxI : x ∈ Set.Ioo (-C.K) 0 := hsubK (hGsub hx)
    have hbound := capAreaElement_le_ths C hxI hc (hGslope x hx)
    have ht0 : 0 ≤ -deriv C.θ x := by linarith [hGslope x hx]
    have hθpow0 : 0 ≤ C.θ x ^ (m - 1) := pow_nonneg (C.θ_pos x hxI).le _
    have hveq : v x = ENNReal.ofReal (capAreaElement C x)
        * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            H (C.θ x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by rw [hv_def]
    have hueq : u (C.θ x) = ENNReal.ofReal (C.θ x ^ (m - 1))
        * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            H (C.θ x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) := by rw [hu_def]
    rw [hveq, hueq]
    have hfactor : ENNReal.ofReal (capAreaElement C x)
        ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2)) * ENNReal.ofReal (-deriv C.θ x)
          * ENNReal.ofReal (C.θ x ^ (m - 1)) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hbound
    calc ENNReal.ofReal (capAreaElement C x)
        * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            H (C.θ x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)
        ≤ (ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2)) * ENNReal.ofReal (-deriv C.θ x)
            * ENNReal.ofReal (C.θ x ^ (m - 1)))
          * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              H (C.θ x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) :=
          mul_le_mul_left hfactor _
      _ = ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2))
          * (ENNReal.ofReal (-deriv C.θ x)
            * (ENNReal.ofReal (C.θ x ^ (m - 1))
              * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
                  H (C.θ x • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))) := by ring
  have hGv_le : ∫⁻ x in G, v x
      ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2)) * ∫⁻ x in G, ENNReal.ofReal (-deriv C.θ x) * u (C.θ x) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hGmeas hptwise
  -- `Ioo a 0 \ G` is null
  have hSnull : volume (Set.Ioo a 0 ∩ S) = 0 :=
    measure_mono_null Set.inter_subset_right (hSc.measure_zero volume)
  have hBadNull : volume (Set.Ioo a 0 \ {x : ℝ | deriv C.θ x ≤ -c}) = 0 := by
    have h1 : volume.restrict (Set.Ioo a 0) {x : ℝ | ¬ deriv C.θ x ≤ -c} = 0 := ae_iff.1 hslope
    have h2 : volume.restrict (Set.Ioo a 0) {x : ℝ | ¬ deriv C.θ x ≤ -c}
        = volume (Set.Ioo a 0 \ {x : ℝ | deriv C.θ x ≤ -c}) := by
      rw [Measure.restrict_apply' measurableSet_Ioo]
      congr 1
      ext x
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    rwa [h2] at h1
  have hcomplNull : volume (Set.Ioo a 0 \ G) = 0 := by
    apply measure_mono_null (t := (Set.Ioo a 0 ∩ S) ∪ (Set.Ioo a 0 \ {x : ℝ | deriv C.θ x ≤ -c}))
    · intro x hx
      rw [hG_def] at hx
      simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and] at hx
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨hx.1, hxS⟩
      · refine Or.inr ⟨hx.1, ?_⟩
        have := hx.2 ⟨hx.1, hxS⟩
        exact this
    · exact measure_union_null hSnull hBadNull
  have hIoo_ae_G : Set.Ioo a 0 =ᵐ[volume] G :=
    ae_eq_set.2 ⟨hcomplNull, by rw [Set.diff_eq_empty.2 hGsub, measure_empty]⟩
  have hGv_eq : ∫⁻ s in Set.Ioo a 0, v s = ∫⁻ s in G, v s :=
    setLIntegral_congr hIoo_ae_G
  -- image containment: `θ '' G ⊆ Ioo 0 (θ a)`
  have hImgSub : C.θ '' G ⊆ Set.Ioo (0:ℝ) (C.θ a) := by
    rintro r ⟨x, hx, rfl⟩
    have hxI : x ∈ Set.Ioo (-C.K) 0 := hsubK (hGsub hx)
    refine ⟨C.θ_pos x hxI, ?_⟩
    have hxa : x ∈ Set.Ico a 0 := ⟨(hGsub hx).1.le, hxI.2⟩
    have hstrict : StrictAntiOn C.θ (Set.Ico a 0) :=
      strictAntiOn_of_slope_ths C ha hc hslope
    exact hstrict ⟨le_refl a, ha.2⟩ hxa (hGsub hx).1
  have hpolar : ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), H z
      = ∫⁻ r in Set.Ioo (0:ℝ) (C.θ a), u r :=
    lintegral_ball_polar m hm (C.θ a) H hHmeas
  have hImg_le : ∫⁻ x in C.θ '' G, u x ≤ ∫⁻ r in Set.Ioo (0:ℝ) (C.θ a), u r :=
    lintegral_mono_set hImgSub
  calc ∫⁻ s in Set.Ioo a 0, v s = ∫⁻ s in G, v s := hGv_eq
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2)) * ∫⁻ x in G, ENNReal.ofReal (-deriv C.θ x) * u (C.θ x) := hGv_le
    _ = ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2)) * ∫⁻ x in C.θ '' G, u x := by rw [hcov]
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2)) * ∫⁻ r in Set.Ioo (0:ℝ) (C.θ a), u r :=
        mul_le_mul_right hImg_le _
    _ = ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2)) * ∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), H z := by
        rw [hpolar]

end RobinCaps.Cap
