import RobinCaps.ThinDomain.TraceIneqStadium

/-!
# Identification of the vertical and the radial boundary traces on a cap arc (`m = 1`)

This file proves the field `vert_eq` of `RobinCaps.ThinDomain.ArcTraceSt`
(`RobinCaps/ThinDomain/TraceIneqStadium.lean`) from the *other* fields of that structure: for
almost every angle `φ ∈ (0, π/2)` the **vertical** endpoint trace `trPlus`/`trMinus` of
`RobinCaps/ThinDomain/TraceOne.lean` at the abscissa `capXSt c e R φ` of the arc point agrees
with the **radial** trace `T φ` (the endpoint value of the absolutely continuous representative
of the radial slice).

## The argument: two families of lines meeting at the point `Q(φ, φ')`

For `0 < φ' < φ < π/2` the vertical line through the arc point `γ(φ)` (abscissa
`x = c + e R cos φ`) meets the radial ray of angle `φ'` at the point

`Q(φ, φ') = (c + e R cos φ, s R cos φ tan φ')`   (`meetPt_vr`),

which is at polar radius `ρ = R cos φ / cos φ'` on the ray (`tRad_vr`) and at the shifted
transverse parameter `τ = R sin φ + s R cos φ tan φ'` on the vertical slice (`tauV_vr`).
Both parameters tend to their boundary values as `φ' → φ⁻`, uniformly like `R (φ - φ') / cos φ`.

* Along the vertical line, for a good abscissa (`SliceGood`), the absolutely continuous
  representative `w = sliceRep u x` is *continuous* up to the endpoint, so
  `|u(Q(φ,φ')) − trSideSt s u x| ≤ ε` for a.e. `φ'` close to `φ` (`vert_bound_vr`).
* Along the ray, the one-dimensional FTC and Cauchy–Schwarz give
  `|u(Q(φ,φ')) − T φ'| ≤ √(R/2 − t) · √((2/R) A(φ'))`, where `A(φ')` is the polar energy of
  the ray (`rad_bound_vr`).  This bound is obtained for a.e. `φ'` and then a.e. `φ`; Fubini
  (`Measure.ae_ae_comm`) reverses the order of the two almost-everywhere quantifiers
  (`swap_rad_bound_vr`), after replacing `u` by a measurable representative on the null set
  where they differ — the pull-back of that null set under `Q` is null because `Q` is a
  fibrewise one-dimensional diffeomorphism (`ae_ae_meetPt_notMem_vr`).
* Consequently, for a.e. `φ` and a.e. `φ' ∈ (φ − η, φ)`,
  `|V(φ) − T(φ')| ≤ ε + √(C (φ − φ')) √(E(φ'))` with `E ∈ L¹`.  Averaging over
  `φ' ∈ (φ − δ, φ)` and letting `δ → 0` at a **Lebesgue point** of `T` and of `E`
  (`IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`) gives `V(φ) = T(φ)`
  (`ae_eq_of_pair_bound_vr`).

The passage between a.e. statements in different one-dimensional parametrisations is done
with the one-dimensional change of variables `lintegral_image_eq_lintegral_abs_deriv_mul`
(`ae_comp_of_hasDerivWithinAt_vr`).

## Main result

`vert_eq_rad_vr`: given `aesm`, `radAC`, `radIntegrable` and `energy_integrable` for a
radial trace `T` on a quarter cap `CapGeomSt L R c e`, `s² = 1`,

`∀ᵐ φ ∂(volume.restrict (Ioo 0 (π/2))), trSideSt s u (capXSt c e R φ) = T φ`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse

/-! ## 1. Generic one-dimensional helpers -/

/-- **Pull-back of an almost-everywhere statement along a one-dimensional change of
variables.**  If `f` is injective on the measurable set `s` with a nonvanishing (continuous)
derivative there, then an a.e. statement on a measurable superset `T` of `f '' s` pulls back to
an a.e. statement on `s`.  This is the one-dimensional change-of-variables formula applied to
the indicator of a null set. -/
theorem ae_comp_of_hasDerivWithinAt_vr {f f' : ℝ → ℝ} {s T : Set ℝ} (hs : MeasurableSet s)
    (hT : MeasurableSet T) (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hinj : InjOn f s)
    (hf' : ∀ x ∈ s, f' x ≠ 0) (hf'c : ContinuousOn f' s) (himg : f '' s ⊆ T)
    {P : ℝ → Prop} (hP : ∀ᵐ y ∂(volume.restrict T), P y) :
    ∀ᵐ x ∂(volume.restrict s), P (f x) := by
  have hnull : volume ({y | ¬ P y} ∩ T) = 0 := by
    rw [ae_iff, Measure.restrict_apply' hT] at hP
    exact hP
  obtain ⟨N, hNsup, hNmeas, hNzero⟩ := exists_measurable_superset_of_null hnull
  have hkey := lintegral_image_eq_lintegral_abs_deriv_mul hs hf hinj (N.indicator 1)
  have hlhs : ∫⁻ y in f '' s, N.indicator 1 y = 0 := by
    rw [lintegral_indicator_one hNmeas, Measure.restrict_apply hNmeas]
    exact measure_mono_null inter_subset_left hNzero
  rw [hlhs] at hkey
  have hfc : ContinuousOn f s := fun x hx => (hf x hx).continuousWithinAt
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal |f' x| * N.indicator 1 (f x))
      (volume.restrict s) := by
    refine AEMeasurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp_aemeasurable
        (continuous_abs.measurable.comp_aemeasurable (hf'c.aemeasurable hs))
    · exact (measurable_one.indicator hNmeas).comp_aemeasurable (hfc.aemeasurable hs)
  have hae := (lintegral_eq_zero_iff' hmeas).1 hkey.symm
  filter_upwards [hae, ae_restrict_mem hs] with x hx hxs
  have hne : ENNReal.ofReal |f' x| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (hf' x hxs)
  have hind : N.indicator (1 : ℝ → ℝ≥0∞) (f x) = 0 := by
    have hx' : ENNReal.ofReal |f' x| * N.indicator 1 (f x) = 0 := hx
    rcases mul_eq_zero.1 hx' with h | h
    · exact absurd h hne
    · exact h
  have hnot : f x ∉ N := by
    intro hmem
    rw [Set.indicator_of_mem hmem] at hind
    exact one_ne_zero hind
  by_contra hcon
  exact hnot (hNsup ⟨hcon, himg ⟨x, hxs, rfl⟩⟩)

/-- **One-sided Lebesgue points on `ℝ`.**  For an integrable `f`, at almost every `φ` the
averages of `|f − f φ|` over the intervals `(φ − δ, φ)` tend to `0` as `δ → 0⁺`. -/
theorem ae_tendsto_oneSided_average_vr {f : ℝ → ℝ} (hf : Integrable f) :
    ∀ᵐ φ ∂(volume : Measure ℝ),
      Tendsto (fun δ : ℝ => δ⁻¹ * ∫ y in Ioo (φ - δ) φ, |f y - f φ|) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure ℝ)) hf.locallyIntegrable 1] with φ hφ
  have hδ : Tendsto (fun δ : ℝ => δ / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun δ : ℝ => δ / 2) (𝓝 0) (𝓝 (0 / 2)) :=
        (continuous_id.div_const 2).tendsto 0
      rw [zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact half_pos (show (0 : ℝ) < δ from hδ)
  have hmem : ∀ᶠ δ in 𝓝[>] (0 : ℝ), φ ∈ closedBall (φ - δ / 2) (1 * (δ / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    rw [mem_closedBall, Real.dist_eq, show φ - (φ - δ / 2) = δ / 2 by ring,
      abs_of_pos (half_pos hδ0)]
    linarith
  have h := hφ (fun δ => φ - δ / 2) (fun δ => δ / 2) hδ hmem
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  rw [setAverage_eq, Real.volume_real_closedBall (by linarith), Real.closedBall_eq_Icc,
    show φ - δ / 2 - δ / 2 = φ - δ by ring, show φ - δ / 2 + δ / 2 = φ by ring,
    ← restrict_Ioo_eq_restrict_Icc, show (2 : ℝ) * (δ / 2) = δ by ring, smul_eq_mul]
  simp only [Real.norm_eq_abs]

/-- The elementary inequality `2 √x ≤ 1 + x`. -/
theorem two_mul_sqrt_le_vr {x : ℝ} (hx : 0 ≤ x) : 2 * Real.sqrt x ≤ 1 + x := by
  nlinarith [sq_nonneg (Real.sqrt x - 1), Real.sq_sqrt hx, Real.sqrt_nonneg x]

/-- **Cauchy–Schwarz on an arbitrary interval** `[a, b]`:
`(∫ₐᵇ |g|)² ≤ (b − a) ∫ₐᵇ g²`. -/
theorem sq_integral_abs_le_vr {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, |g x|) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  have h1 : (∫ x in a..b, |g x|) = ∫ x in (0 : ℝ)..(b - a), |g (x + a)| := by
    rw [intervalIntegral.integral_comp_add_right (fun x => |g x|) a, zero_add, sub_add_cancel]
  have h2 : (∫ x in a..b, g x ^ 2) = ∫ x in (0 : ℝ)..(b - a), g (x + a) ^ 2 := by
    rw [intervalIntegral.integral_comp_add_right (fun x => g x ^ 2) a, zero_add, sub_add_cancel]
  rw [h1, h2]
  have hg' : IntervalIntegrable (fun x => g (x + a)) volume 0 (b - a) := by
    have := hg.comp_add_right a
    simpa using this
  have hg2' : IntervalIntegrable (fun x => g (x + a) ^ 2) volume 0 (b - a) := by
    have := hg2.comp_add_right a
    simpa using this
  exact abs_integral_sq_le (fun x => g (x + a)) (by linarith) hg' hg2'

/-! ## 2. The core lemma: from the pair bound to the a.e. identification -/

/-- **The core one-dimensional lemma.**  Let `T, E ∈ L¹(ℝ)`, `E ≥ 0`, and let `V` be an
arbitrary function.  Suppose that for a.e. `φ ∈ (a, b)` and every `ε > 0` there are `η > 0`
and `C ≥ 0` with

`|V φ − T φ'| ≤ ε + √(C (φ − φ')) · √(E φ')`   for a.e. `φ' ∈ (φ − η, φ)`.

Then `V = T` a.e. on `(a, b)`.  The proof averages the bound over `φ' ∈ (φ − δ, φ)` and lets
`δ → 0⁺` at a one-sided Lebesgue point of `T` and of `E`; no measurability of `V` is needed. -/
theorem ae_eq_of_pair_bound_vr {a b : ℝ} {V T E : ℝ → ℝ}
    (hT : Integrable T) (hE : Integrable E) (hE0 : ∀ φ, 0 ≤ E φ)
    (h : ∀ᵐ φ ∂(volume.restrict (Ioo a b)), ∀ ε > 0, ∃ η > 0, ∃ C, 0 ≤ C ∧
        ∀ᵐ φ' ∂(volume.restrict (Ioo a b)), φ - η < φ' → φ' < φ →
          |V φ - T φ'| ≤ ε + Real.sqrt (C * (φ - φ')) * Real.sqrt (E φ')) :
    ∀ᵐ φ ∂(volume.restrict (Ioo a b)), V φ = T φ := by
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (ae_tendsto_oneSided_average_vr hT),
    ae_restrict_of_ae (ae_tendsto_oneSided_average_vr hE)] with φ hφ hφab hLT hLE
  suffices hsuff : ∀ ε > 0, |V φ - T φ| ≤ ε by
    have h0 : |V φ - T φ| ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      exact hsuff ε hε
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)
  intro ε hε
  obtain ⟨η, hη, C, hC, hbound⟩ := hφ ε hε
  set LT : ℝ → ℝ := fun δ => δ⁻¹ * ∫ y in Ioo (φ - δ) φ, |T y - T φ| with hLTdef
  set LE : ℝ → ℝ := fun δ => δ⁻¹ * ∫ y in Ioo (φ - δ) φ, |E y - E φ| with hLEdef
  -- the majorant tends to `ε`
  have hsqrt : Tendsto (fun δ : ℝ => Real.sqrt (C * δ)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => C * δ) (𝓝 0) (𝓝 (C * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h1
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun δ => ε + Real.sqrt (C * δ) * (1 + (LE δ + E φ)) / 2 + LT δ)
      (𝓝[>] 0) (𝓝 (ε + 0 * (1 + (0 + E φ)) / 2 + 0)) := by
    refine (tendsto_const_nhds.add ((hsqrt.mul (tendsto_const_nhds.add
      (hLE.add tendsto_const_nhds))).div_const 2)).add hLT
  rw [zero_mul, zero_div, add_zero, add_zero] at hg
  refine ge_of_tendsto hg ?_
  have hηa : (0 : ℝ) < min η (φ - a) := lt_min hη (by linarith [hφab.1])
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hηa] with δ hδ hδ'
  have hδ0 : (0 : ℝ) < δ := hδ
  have hδη : δ < η := lt_of_lt_of_le hδ'.2 (min_le_left _ _)
  have hδa : δ < φ - a := lt_of_lt_of_le hδ'.2 (min_le_right _ _)
  set I : Set ℝ := Ioo (φ - δ) φ with hIdef
  have hIsub : I ⊆ Ioo a b := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2, hφab.2]⟩
  have hIvol : (volume : Measure ℝ).real I = δ := by
    rw [hIdef, Real.volume_real_Ioo_of_le (by linarith)]
    ring
  haveI : IsFiniteMeasure (volume.restrict I) :=
    ⟨by rw [Measure.restrict_apply_univ, hIdef, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  -- the constant and the two `L¹` pieces
  set K : ℝ := ε + Real.sqrt (C * δ) * (1 + E φ) / 2 with hKdef
  have hsq0 : 0 ≤ Real.sqrt (C * δ) := Real.sqrt_nonneg _
  -- a.e. on `I`, the pointwise bound
  have hae : ∀ᵐ y ∂(volume.restrict I), |V φ - T φ|
      ≤ K + (Real.sqrt (C * δ) / 2) * |E y - E φ| + |T y - T φ| := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hIsub hbound,
      ae_restrict_mem measurableSet_Ioo] with y hy hyI
    have hb := hy (by linarith [hyI.1]) hyI.2
    have hs1 : Real.sqrt (C * (φ - y)) ≤ Real.sqrt (C * δ) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith [hyI.1]) hC)
    have hs2 : Real.sqrt (E y) ≤ (1 + E y) / 2 := by
      linarith [two_mul_sqrt_le_vr (hE0 y)]
    have hprod : Real.sqrt (C * (φ - y)) * Real.sqrt (E y)
        ≤ Real.sqrt (C * δ) * ((1 + E y) / 2) :=
      mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) hsq0
    have hEy : E y ≤ |E y - E φ| + E φ := by
      have := le_abs_self (E y - E φ)
      linarith
    have htri : |V φ - T φ| ≤ |V φ - T y| + |T y - T φ| := abs_sub_le _ _ _
    have hmid : Real.sqrt (C * δ) * ((1 + E y) / 2)
        ≤ Real.sqrt (C * δ) * (1 + E φ) / 2 + (Real.sqrt (C * δ) / 2) * |E y - E φ| := by
      have := mul_le_mul_of_nonneg_left hEy hsq0
      nlinarith
    rw [hKdef]
    linarith
  -- integrability of the majorant on `I`
  have hTI : Integrable (fun y => |T y - T φ|) (volume.restrict I) :=
    (hT.restrict.sub (integrable_const _)).abs
  have hEI : Integrable (fun y => |E y - E φ|) (volume.restrict I) :=
    (hE.restrict.sub (integrable_const _)).abs
  have hEI' : Integrable (fun y => (Real.sqrt (C * δ) / 2) * |E y - E φ|) (volume.restrict I) :=
    hEI.const_mul (Real.sqrt (C * δ) / 2)
  have hfg : Integrable (fun y => K + (Real.sqrt (C * δ) / 2) * |E y - E φ|)
      (volume.restrict I) :=
    (integrable_const K).add hEI'
  have hmaj : Integrable (fun y => K + (Real.sqrt (C * δ) / 2) * |E y - E φ| + |T y - T φ|)
      (volume.restrict I) :=
    hfg.add hTI
  have hint := integral_mono_ae (integrable_const (|V φ - T φ|)) hmaj hae
  have e0 : ∫ _ in I, |V φ - T φ| = δ * |V φ - T φ| := by
    rw [setIntegral_const, hIvol, smul_eq_mul]
  have e1 : ∫ y in I, (K + (Real.sqrt (C * δ) / 2) * |E y - E φ| + |T y - T φ|)
      = (∫ y in I, (K + (Real.sqrt (C * δ) / 2) * |E y - E φ|)) + ∫ y in I, |T y - T φ| :=
    integral_add hfg hTI
  have e2 : ∫ y in I, (K + (Real.sqrt (C * δ) / 2) * |E y - E φ|)
      = (∫ _ in I, K) + ∫ y in I, (Real.sqrt (C * δ) / 2) * |E y - E φ| :=
    integral_add (integrable_const K) hEI'
  have e3 : ∫ _ in I, K = δ * K := by
    rw [setIntegral_const, hIvol, smul_eq_mul]
  have e4 : ∫ y in I, (Real.sqrt (C * δ) / 2) * |E y - E φ|
      = (Real.sqrt (C * δ) / 2) * ∫ y in I, |E y - E φ| := integral_const_mul _ _
  rw [e0, e1, e2, e3, e4] at hint
  -- divide by `δ`
  set IT : ℝ := ∫ y in I, |T y - T φ| with hITdef
  set IE : ℝ := ∫ y in I, |E y - E φ| with hIEdef
  have hLTδ : LT δ = δ⁻¹ * IT := rfl
  have hLEδ : LE δ = δ⁻¹ * IE := rfl
  have hdiv : |V φ - T φ| ≤ K + (Real.sqrt (C * δ) / 2) * LE δ + LT δ := by
    rw [hLTδ, hLEδ]
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    have h1 : |V φ - T φ| ≤ (δ * K + Real.sqrt (C * δ) / 2 * IE + IT) / δ := by
      rw [le_div_iff₀ hδ0]
      linarith [hint]
    have h2 : (δ * K + Real.sqrt (C * δ) / 2 * IE + IT) / δ
        = K + (Real.sqrt (C * δ) / 2) * (δ⁻¹ * IE) + δ⁻¹ * IT := by
      field_simp
    rw [h2] at h1
    exact h1
  rw [hKdef] at hdiv
  have : Real.sqrt (C * δ) * (1 + E φ) / 2 + Real.sqrt (C * δ) / 2 * LE δ
      = Real.sqrt (C * δ) * (1 + (LE δ + E φ)) / 2 := by ring
  linarith

/-! ## 3. The meeting point of a vertical line and a radial ray -/

section Geometry

variable {L R : ℝ}

/-- **The meeting point** `Q(φ, φ')` of the vertical line through the arc point of angle `φ`
(abscissa `capXSt c e R φ`) and the radial ray of angle `φ'` (centre `(c, 0)`): its ordinate is
`s R cos φ tan φ'`. -/
def meetPt_vr (c e s R φ φ' : ℝ) : CapSpace 1 :=
  (capXSt c e R φ, ept (s * (R * Real.cos φ) * Real.tan φ'))

/-- The shifted radial parameter `t = ρ − R/2` of the meeting point on the ray of angle `φ'`:
the polar radius is `ρ = R cos φ / cos φ'`. -/
def tRad_vr (R φ φ' : ℝ) : ℝ := R * Real.cos φ / Real.cos φ' - R / 2

/-- The transverse parameter `τ` of the meeting point on the vertical slice through
`capXSt c e R φ`, identified with `(0, 2 R sin φ)` by `eptSh (R sin φ)`. -/
def tauV_vr (s R φ φ' : ℝ) : ℝ := R * Real.sin φ + s * (R * Real.cos φ) * Real.tan φ'

theorem cos_pos_vr {φ : ℝ} (hφ : φ ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.cos φ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩

theorem sin_pos_vr {φ : ℝ} (hφ : φ ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.sin φ :=
  Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])

theorem cos_lt_cos_vr {φ φ' : ℝ} (hφ : φ ∈ Ioo 0 (Real.pi / 2)) (hφ' : φ' ∈ Ioo 0 φ) :
    Real.cos φ < Real.cos φ' :=
  Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hφ'.1.le hφ.2.le hφ'.2

theorem tan_pos_vr {φ' : ℝ} (hφ' : φ' ∈ Ioo 0 (Real.pi / 2)) : 0 < Real.tan φ' :=
  Real.tan_pos_of_pos_of_lt_pi_div_two hφ'.1 hφ'.2

/-- The Lipschitz bound `cos φ' − cos φ ≤ φ − φ'`. -/
theorem cos_sub_cos_le_vr {φ φ' : ℝ} (hφ' : φ' < φ) : Real.cos φ' - Real.cos φ ≤ φ - φ' := by
  have h := Real.abs_cos_sub_cos_le φ' φ
  have h1 : |φ' - φ| = φ - φ' := by
    rw [abs_sub_comm]
    exact abs_of_pos (by linarith)
  rw [h1] at h
  linarith [le_abs_self (Real.cos φ' - Real.cos φ)]

/-- The ordinate of the meeting point is below the arc: `R cos φ tan φ' < R sin φ`. -/
theorem cos_mul_tan_lt_vr {R φ φ' : ℝ} (hR : 0 < R) (hφ : φ ∈ Ioo 0 (Real.pi / 2))
    (hφ' : φ' ∈ Ioo 0 φ) : R * Real.cos φ * Real.tan φ' < R * Real.sin φ := by
  have hcφ := cos_pos_vr hφ
  have htlt : Real.tan φ' < Real.tan φ :=
    Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [hφ'.1, Real.pi_pos]) hφ.2 hφ'.2
  have h1 : Real.cos φ * Real.tan φ' < Real.cos φ * Real.tan φ := mul_lt_mul_of_pos_left htlt hcφ
  have h2 : Real.cos φ * Real.tan φ = Real.sin φ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [h2] at h1
  nlinarith

theorem capSliceSt_tRad_vr {c e s R φ φ' : ℝ} (hcos : Real.cos φ' ≠ 0) :
    capSliceSt c e s R φ' (tRad_vr R φ φ') = meetPt_vr c e s R φ φ' := by
  have h1 : R * Real.cos φ / Real.cos φ' - R / 2 + R / 2 = R * Real.cos φ / Real.cos φ' := by
    ring
  simp only [capSliceSt, capPtSt, meetPt_vr, tRad_vr, capXSt, h1, Prod.mk.injEq]
  constructor
  · rw [div_mul_cancel₀ _ hcos]
  · congr 1
    rw [Real.tan_eq_sin_div_cos]
    field_simp

theorem eptSh_tauV_vr (c e s R φ φ' : ℝ) :
    ((capXSt c e R φ, eptSh (R * Real.sin φ) (tauV_vr s R φ φ')) : CapSpace 1)
      = meetPt_vr c e s R φ φ' := by
  simp only [meetPt_vr, eptSh, tauV_vr, Prod.mk.injEq, true_and]
  congr 1
  ring

/-- The vertical parameter of the meeting point lies inside the slice `(0, 2 R sin φ)`. -/
theorem tauV_mem_vr {s R φ φ' : ℝ} (hR : 0 < R) (hs : s ^ 2 = 1) (hφ : φ ∈ Ioo 0 (Real.pi / 2))
    (hφ' : φ' ∈ Ioo 0 φ) : tauV_vr s R φ φ' ∈ Ioo 0 (2 * (R * Real.sin φ)) := by
  have hcφ := cos_pos_vr hφ
  have htpos := tan_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩
  have hkey := cos_mul_tan_lt_vr hR hφ hφ'
  have hA : 0 < R * Real.cos φ * Real.tan φ' := by positivity
  rcases mul_self_eq_one_iff.1 (by nlinarith [hs] : s * s = 1) with h1 | h1
  · subst h1
    unfold tauV_vr
    constructor <;> nlinarith
  · subst h1
    unfold tauV_vr
    constructor <;> nlinarith

/-- The radial parameter of the meeting point lies in `(0, R/2)` when `φ − φ' < cos φ`. -/
theorem tRad_mem_vr {R φ φ' : ℝ} (hR : 0 < R) (hφ : φ ∈ Ioo 0 (Real.pi / 2))
    (hφ' : φ' ∈ Ioo 0 φ) (hclose : φ - φ' < Real.cos φ) : tRad_vr R φ φ' ∈ Ioo 0 (R / 2) := by
  have hcφ := cos_pos_vr hφ
  have hcφ' : 0 < Real.cos φ' := cos_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩
  have hlt := cos_lt_cos_vr hφ hφ'
  have hlip := cos_sub_cos_le_vr hφ'.2
  unfold tRad_vr
  constructor
  · rw [sub_pos, lt_div_iff₀ hcφ']
    nlinarith [mul_pos hR (show 0 < 2 * Real.cos φ - Real.cos φ' by linarith)]
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hcφ']
    nlinarith [mul_lt_mul_of_pos_left hlt hR]

/-- The distance of the meeting point from the arc, along the ray: `R/2 − t ≤ (R / cos φ) (φ − φ')`. -/
theorem tRad_sub_le_vr {R φ φ' : ℝ} (hR : 0 < R) (hφ : φ ∈ Ioo 0 (Real.pi / 2))
    (hφ' : φ' ∈ Ioo 0 φ) : R / 2 - tRad_vr R φ φ' ≤ (R / Real.cos φ) * (φ - φ') := by
  have hcφ := cos_pos_vr hφ
  have hcφ' : 0 < Real.cos φ' := cos_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩
  have hlt := cos_lt_cos_vr hφ hφ'
  have hlip := cos_sub_cos_le_vr hφ'.2
  have e : R / 2 - tRad_vr R φ φ' = R * (Real.cos φ' - Real.cos φ) / Real.cos φ' := by
    unfold tRad_vr
    field_simp
    ring
  rw [e, div_le_iff₀ hcφ']
  have h1 : R * (Real.cos φ' - Real.cos φ) ≤ R * (φ - φ') := mul_le_mul_of_nonneg_left hlip hR.le
  have h2 : R * (φ - φ') ≤ (R / Real.cos φ) * (φ - φ') * Real.cos φ' := by
    have : R * (φ - φ') = (R / Real.cos φ) * (φ - φ') * Real.cos φ := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlt.le
      (mul_nonneg (div_nonneg hR.le hcφ.le) (by linarith [hφ'.2]))
  linarith

/-- The vertical distance of the meeting point from the arc:
`R sin φ − R cos φ tan φ' ≤ (R / cos φ) (φ − φ')`. -/
theorem vert_dist_le_vr {R φ φ' : ℝ} (hR : 0 < R) (hφ : φ ∈ Ioo 0 (Real.pi / 2))
    (hφ' : φ' ∈ Ioo 0 φ) :
    R * Real.sin φ - R * Real.cos φ * Real.tan φ' ≤ (R / Real.cos φ) * (φ - φ') := by
  have hcφ := cos_pos_vr hφ
  have hcφ' : 0 < Real.cos φ' := cos_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩
  have hlt := cos_lt_cos_vr hφ hφ'
  have e : R * Real.sin φ - R * Real.cos φ * Real.tan φ'
      = R * Real.sin (φ - φ') / Real.cos φ' := by
    rw [Real.sin_sub, Real.tan_eq_sin_div_cos]
    field_simp
  rw [e, div_le_iff₀ hcφ']
  have hsin : Real.sin (φ - φ') ≤ φ - φ' := (Real.sin_lt (by linarith [hφ'.2])).le
  have h1 : R * Real.sin (φ - φ') ≤ R * (φ - φ') := mul_le_mul_of_nonneg_left hsin hR.le
  have h2 : R * (φ - φ') ≤ (R / Real.cos φ) * (φ - φ') * Real.cos φ' := by
    have : R * (φ - φ') = (R / Real.cos φ) * (φ - φ') * Real.cos φ := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlt.le
      (mul_nonneg (div_nonneg hR.le hcφ.le) (by linarith [hφ'.2]))
  linarith

/-- The meeting point lies in the thin domain (it is strictly below the arc on the vertical
slice through `capXSt c e R φ`). -/
theorem meetPt_mem_vr (hR : 0 < R) {c e s : ℝ} (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1)
    {φ φ' : ℝ} (hφ : φ ∈ Ioo 0 (Real.pi / 2)) (hφ' : φ' ∈ Ioo 0 φ) :
    meetPt_vr c e s R φ φ' ∈ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R := by
  have hx := hg.sub (hg.capXSt_mem hR hφ)
  have hcφ := cos_pos_vr hφ
  have htpos := tan_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩
  have hs1 : |s| = 1 := by
    rcases mul_self_eq_one_iff.1 (by nlinarith [hs] : s * s = 1) with h1 | h1 <;> simp [h1]
  refine ⟨hx.1, hx.2, ?_⟩
  show ‖ept (s * (R * Real.cos φ) * Real.tan φ')‖
    < profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R (capXSt c e R φ)
  rw [ept_norm, hg.profile_capXSt hR hφ, abs_mul, abs_mul, hs1, one_mul,
    abs_of_pos (mul_pos hR hcφ), abs_of_pos htpos]
  exact cos_mul_tan_lt_vr hR hφ hφ'

theorem measurable_meetPt_vr (c e s R : ℝ) :
    Measurable (fun p : ℝ × ℝ => meetPt_vr c e s R p.1 p.2) := by
  have htan : Measurable Real.tan := by
    have : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
    rw [this]
    exact Real.measurable_sin.div Real.measurable_cos
  have hept : Measurable ept := measurePreserving_ept.measurable
  unfold meetPt_vr capXSt
  refine Measurable.prodMk ?_ (hept.comp ?_)
  · exact measurable_const.add
      (measurable_const.mul (measurable_const.mul (Real.measurable_cos.comp measurable_fst)))
  · exact (measurable_const.mul (measurable_const.mul (Real.measurable_cos.comp measurable_fst))).mul
      (htan.comp measurable_snd)

end Geometry

/-! ## 4. The vertical side: continuity of the slice representative at the endpoint -/

section Vertical

variable {L R : ℝ}

/-- **The vertical bound.**  For a good abscissa `x = capXSt c e R φ`, the absolutely
continuous slice representative is continuous up to the endpoint, so the value of `u` at the
meeting point `Q(φ, φ')` is within `ε` of the endpoint trace `trSideSt s u x` for a.e. `φ'`
close to `φ`. -/
theorem vert_bound_vr (hR : 0 < R) {c e s : ℝ} (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {φ : ℝ}
    (hφ : φ ∈ Ioo 0 (Real.pi / 2)) (hgood : SliceGood u (capXSt c e R φ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, ∀ᵐ φ' ∂(volume.restrict (Ioo 0 (Real.pi / 2))), φ - η < φ' → φ' < φ →
      |u.toFun (meetPt_vr c e s R φ φ') - trSideSt s u (capXSt c e R φ)| ≤ ε := by
  set x := capXSt c e R φ with hxdef
  set ℓ := 2 * profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R x with hℓdef
  set w := sliceRep u x with hwdef
  have hprof : profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R x = R * Real.sin φ :=
    hg.profile_capXSt hR hφ
  have hℓ : ℓ = 2 * (R * Real.sin φ) := by rw [hℓdef, hprof]
  have hcφ := cos_pos_vr hφ
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hcont : ContinuousOn w.toFun (Icc 0 ℓ) := H1_continuousOn hgood.len_pos w
  -- the endpoint `p` and the distance of the meeting point to it
  have hcase : ∃ p ∈ Icc (0 : ℝ) ℓ, trSideSt s u x = w.toFun p ∧
      ∀ φ', dist (tauV_vr s R φ φ') p
        = |R * Real.sin φ - R * Real.cos φ * Real.tan φ'| := by
    rcases mul_self_eq_one_iff.1 (by nlinarith [hs] : s * s = 1) with hs1 | hs1
    · refine ⟨ℓ, ⟨hgood.len_pos.le, le_rfl⟩, ?_, ?_⟩
      · rw [hs1, trSideSt_one]
        rfl
      · intro φ'
        rw [hs1, Real.dist_eq, tauV_vr, hℓ, abs_sub_comm]
        congr 1
        ring
    · refine ⟨0, ⟨le_rfl, hgood.len_pos.le⟩, ?_, ?_⟩
      · rw [hs1, trSideSt_neg_one]
        rfl
      · intro φ'
        rw [hs1, Real.dist_eq, tauV_vr, sub_zero]
        congr 1
        ring
  obtain ⟨p, hp, hpval, hdist⟩ := hcase
  have hcw : ContinuousWithinAt w.toFun (Icc 0 ℓ) p := hcont p hp
  obtain ⟨δ₁, hδ₁, hδ₁spec⟩ := Metric.continuousWithinAt_iff.1 hcw ε hε
  -- the a.e. identification of `w` with `u` along the slice, pulled back to `φ'`
  have hw := sliceRep_ae hgood
  have hae : ∀ᵐ φ' ∂(volume.restrict (Ioo 0 φ)),
      w.toFun (tauV_vr s R φ φ') = u.toFun (x, eptSh (profile (Cap.hemisphere 1)
        (Cap.hemisphere 1) L R x) (tauV_vr s R φ φ')) := by
    refine ae_comp_of_hasDerivWithinAt_vr (f := fun φ' => tauV_vr s R φ φ')
      (f' := fun φ' => s * (R * Real.cos φ) * (1 / Real.cos φ' ^ 2)) measurableSet_Ioo
      measurableSet_Ioo ?_ ?_ ?_ ?_ ?_ hw
    · intro φ' hφ'
      have hcφ' := cos_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩
      exact (((Real.hasDerivAt_tan hcφ'.ne').const_mul (s * (R * Real.cos φ))).const_add
        (R * Real.sin φ)).hasDerivWithinAt
    · intro a ha b hb hab
      have hk : s * (R * Real.cos φ) ≠ 0 := mul_ne_zero hs0 (mul_ne_zero hR.ne' hcφ.ne')
      have hab' : s * (R * Real.cos φ) * Real.tan a = s * (R * Real.cos φ) * Real.tan b := by
        have := hab
        simp only [tauV_vr] at this
        linarith
      have htan : Real.tan a = Real.tan b := mul_left_cancel₀ hk hab'
      exact Real.strictMonoOn_tan.injOn ⟨by linarith [ha.1, Real.pi_pos], ha.2.trans hφ.2⟩
        ⟨by linarith [hb.1, Real.pi_pos], hb.2.trans hφ.2⟩ htan
    · intro φ' hφ'
      have hcφ' := cos_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩
      exact mul_ne_zero (mul_ne_zero hs0 (mul_ne_zero hR.ne' hcφ.ne'))
        (one_div_ne_zero (pow_ne_zero 2 hcφ'.ne'))
    · refine continuousOn_const.mul (continuousOn_const.div
        (Real.continuous_cos.continuousOn.pow 2) ?_)
      intro φ' hφ'
      exact pow_ne_zero 2 (cos_pos_vr ⟨hφ'.1, hφ'.2.trans hφ.2⟩).ne'
    · rintro _ ⟨φ', hφ', rfl⟩
      show tauV_vr s R φ φ' ∈ Ioo 0 ℓ
      rw [hℓ]
      exact tauV_mem_vr hR hs hφ hφ'
  refine ⟨δ₁ * Real.cos φ / R, by positivity, ?_⟩
  filter_upwards [ae_imp_of_ae_restrict measurableSet_Ioo (Ioo 0 (Real.pi / 2)) hae,
    ae_restrict_mem measurableSet_Ioo] with φ' h1 hφ'
  intro hlow hup
  have hφ'I : φ' ∈ Ioo 0 φ := ⟨hφ'.1, hup⟩
  have hpt : ((x, eptSh (profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R x)
      (tauV_vr s R φ φ')) : CapSpace 1) = meetPt_vr c e s R φ φ' := by
    rw [hprof]
    exact eptSh_tauV_vr c e s R φ φ'
  rw [← hpt, ← h1 hφ'I, hpval]
  have hτ : tauV_vr s R φ φ' ∈ Icc 0 ℓ := by
    refine Ioo_subset_Icc_self ?_
    rw [hℓ]
    exact tauV_mem_vr hR hs hφ hφ'I
  have hdpos : 0 < R * Real.sin φ - R * Real.cos φ * Real.tan φ' := by
    linarith [cos_mul_tan_lt_vr hR hφ hφ'I]
  have hdlt : dist (tauV_vr s R φ φ') p < δ₁ := by
    rw [hdist φ', abs_of_pos hdpos]
    calc R * Real.sin φ - R * Real.cos φ * Real.tan φ'
        ≤ (R / Real.cos φ) * (φ - φ') := vert_dist_le_vr hR hφ hφ'I
      _ < (R / Real.cos φ) * (δ₁ * Real.cos φ / R) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = δ₁ := by field_simp
  have := hδ₁spec hτ hdlt
  rw [Real.dist_eq] at this
  exact this.le

end Vertical

/-! ## 5. The radial side: the FTC along the ray and Cauchy–Schwarz -/

section Radial

variable {L R : ℝ}

/-- The polar weight `ρ = t + R/2 ≥ R/2` converts the unweighted ray energy into the polar
one: `∫ D ≤ (2/R) ∫ D ρ`. -/
theorem capDens_integral_le_vr (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s φ : ℝ}
    (hint2 : IntegrableOn (fun t => capDensSt R u c e s φ t * (t + R / 2)) (Ioo 0 (R / 2))
      volume) :
    ∫ t in Ioo 0 (R / 2), capDensSt R u c e s φ t ≤ (2 / R) * arcEnergySt R u c e s φ := by
  rw [arcEnergySt, ← integral_const_mul]
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun t => capDensSt_nonneg R u c e s φ t)
    (hint2.const_mul (2 / R)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hw : (1 : ℝ) ≤ (2 / R) * (t + R / 2) := by
    have h1 : 0 < t := ht.1
    have hR0 : R ≠ 0 := ne_of_gt hR
    have heq : (2 / R) * (t + R / 2) = 1 + 2 * t / R := by field_simp; ring
    rw [heq]
    have : 0 < 2 * t / R := by positivity
    linarith
  nlinarith [capDensSt_nonneg R u c e s φ t, hw]

/-- The mass of the radial representative is bounded by the unweighted ray energy. -/
theorem mass_le_vr (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s φ : ℝ}
    (W : Sobolev.H1 (R / 2))
    (hW : W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
      fun t => u.toFun (capSliceSt c e s R φ t))
    (hint1 : IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume) :
    Sobolev.mass (R / 2) W ≤ ∫ t in Ioo 0 (R / 2), capDensSt R u c e s φ t := by
  have hl : (0 : ℝ) < R / 2 := by linarith
  have hmass : Sobolev.mass (R / 2) W
      = ∫ t in Ioo 0 (R / 2), u.toFun (capSliceSt c e s R φ t) ^ 2 := by
    rw [Sobolev.mass, Sobolev.intervalIntegral_eq_setIntegral_Ioo hl.le]
    exact integral_congr_ae (by filter_upwards [hW] with t ht; rw [ht])
  rw [hmass]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) hint1 ?_
  exact Eventually.of_forall fun t => by
    simp only [capDensSt]
    nlinarith [sq_nonneg (u.gx (capSliceSt c e s R φ t)),
      norm_nonneg (u.gz (capSliceSt c e s R φ t)), sq_nonneg ‖u.gz (capSliceSt c e s R φ t)‖]

/-- The Dirichlet energy of the radial representative is bounded by the unweighted ray
energy. -/
theorem dirichlet_le_vr (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s φ : ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (W : Sobolev.H1 (R / 2))
    (hWd : deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
      fun t => e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
        + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0)
    (hint1 : IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume) :
    Sobolev.dirichlet (R / 2) W ≤ ∫ t in Ioo 0 (R / 2), capDensSt R u c e s φ t := by
  have hl : (0 : ℝ) < R / 2 := by linarith
  have hdir : Sobolev.dirichlet (R / 2) W
      = ∫ t in Ioo 0 (R / 2), (e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
          + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ^ 2 := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hl.le]
    exact integral_congr_ae (by filter_upwards [hWd] with t ht; rw [ht])
  rw [hdir]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) hint1 ?_
  refine Eventually.of_forall fun t => ?_
  simp only [capDensSt]
  have hrad := radial_deriv_sq_le_st (e := e) (s := s) (φ := φ)
    (a := u.gx (capSliceSt c e s R φ t)) (b := u.gz (capSliceSt c e s R φ t) 0) he hs
  have hnorm := norm_sq_one_dim (u.gz (capSliceSt c e s R φ t))
  nlinarith [hrad, hnorm, sq_nonneg (u.toFun (capSliceSt c e s R φ t))]

/-- **The pointwise radial trace bound**: `T φ² ≤ (8/R² + 2) A(φ)` for a.e. `φ`, from the
radial absolute continuity and the ray integrability alone (this is `arc_sq_ae_le_st` of
`TraceIneqStadium.lean` without the `ArcTraceSt` packaging). -/
theorem T_sq_ae_le_vr (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1)
    (hrad : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∃ W : Sobolev.H1 (R / 2),
        W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => u.toFun (capSliceSt c e s R φ t)) ∧
          deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
              + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ∧
          W.toFun (R / 2) = T φ)
    (hint : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume ∧
        IntegrableOn (fun t => capDensSt R u c e s φ t * (t + R / 2)) (Ioo 0 (R / 2)) volume) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      T φ ^ 2 ≤ arcConstSt R * arcEnergySt R u c e s φ := by
  filter_upwards [hrad, hint] with φ hAC hInt
  obtain ⟨W, hW, hWd, hWend⟩ := hAC
  obtain ⟨hint1, hint2⟩ := hInt
  have hl : (0 : ℝ) < R / 2 := by linarith
  set E : ℝ := ∫ t in Ioo 0 (R / 2), capDensSt R u c e s φ t with hE
  set A : ℝ := arcEnergySt R u c e s φ with hA
  have hend := Sobolev.endpoint_ell_sq_le W hl
  rw [hWend] at hend
  have hM : Sobolev.mass (R / 2) W ≤ E := mass_le_vr hR W hW hint1
  have hD : Sobolev.dirichlet (R / 2) W ≤ E := dirichlet_le_vr hR he hs W hWd hint1
  have hEA : E ≤ (2 / R) * A := capDens_integral_le_vr hR hint2
  have e1 : (2 : ℝ) / (R / 2) = 4 / R := by field_simp; norm_num
  have e2 : (2 : ℝ) * (R / 2) = R := by ring
  rw [e1, e2] at hend
  have s1 : (4 / R) * Sobolev.mass (R / 2) W ≤ (4 / R) * E :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have s2 : R * Sobolev.dirichlet (R / 2) W ≤ R * E := mul_le_mul_of_nonneg_left hD hR.le
  have s3 : (4 / R + R) * E ≤ (4 / R + R) * ((2 / R) * A) :=
    mul_le_mul_of_nonneg_left hEA (by positivity)
  have s4 : (4 / R + R) * ((2 / R) * A) = arcConstSt R * A := by
    have hR0 : R ≠ 0 := ne_of_gt hR
    rw [arcConstSt]
    field_simp
    ring
  linarith [hend, s1, s2, s3, s4]

/-- **The radial trace is square integrable in the angle**, hence integrable. -/
theorem integrableOn_T_vr (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1)
    (haesm : AEStronglyMeasurable T (volume.restrict (Ioo 0 (Real.pi / 2))))
    (hrad : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∃ W : Sobolev.H1 (R / 2),
        W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => u.toFun (capSliceSt c e s R φ t)) ∧
          deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
              + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ∧
          W.toFun (R / 2) = T φ)
    (hint : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume ∧
        IntegrableOn (fun t => capDensSt R u c e s φ t * (t + R / 2)) (Ioo 0 (R / 2)) volume)
    (henergy : IntegrableOn (arcEnergySt R u c e s) (Ioo 0 (Real.pi / 2)) volume) :
    IntegrableOn T (Ioo 0 (Real.pi / 2)) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hsq : Integrable (fun φ => T φ ^ 2) (volume.restrict (Ioo 0 (Real.pi / 2))) := by
    refine Integrable.mono' (henergy.const_mul (arcConstSt R)) (haesm.pow 2) ?_
    filter_upwards [T_sq_ae_le_vr hR he hs hrad hint] with φ hφ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hφ
  exact ((memLp_two_iff_integrable_sq haesm).2 hsq).integrable one_le_two

/-- **The radial bound.**  For an angle `φ'` at which the radial slice has an absolutely
continuous representative with endpoint value `T φ'`, the value of `u` at the meeting point
`Q(φ, φ')` differs from `T φ'` by at most `√((R / cos φ)(φ − φ')) · √((2/R) A(φ'))`, for a.e.
`φ > φ'` with `φ − φ' < cos φ`. -/
theorem rad_bound_vr (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1) {φ' : ℝ} (hφ' : φ' ∈ Ioo 0 (Real.pi / 2))
    (hAC : ∃ W : Sobolev.H1 (R / 2),
        W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => u.toFun (capSliceSt c e s R φ' t)) ∧
          deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => e * Real.cos φ' * u.gx (capSliceSt c e s R φ' t)
              + s * Real.sin φ' * u.gz (capSliceSt c e s R φ' t) 0) ∧
          W.toFun (R / 2) = T φ')
    (hInt : IntegrableOn (fun t => capDensSt R u c e s φ' t) (Ioo 0 (R / 2)) volume ∧
        IntegrableOn (fun t => capDensSt R u c e s φ' t * (t + R / 2)) (Ioo 0 (R / 2)) volume) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))), φ' < φ → φ - φ' < Real.cos φ →
      |u.toFun (meetPt_vr c e s R φ φ') - T φ'|
        ≤ Real.sqrt ((R / Real.cos φ) * (φ - φ'))
          * Real.sqrt ((2 / R) * arcEnergySt R u c e s φ') := by
  obtain ⟨W, hW, hWd, hWend⟩ := hAC
  have hl : (0 : ℝ) < R / 2 := by linarith
  have hcφ' := cos_pos_vr hφ'
  set A2 : ℝ := (2 / R) * arcEnergySt R u c e s φ' with hA2
  have hD : Sobolev.dirichlet (R / 2) W ≤ A2 :=
    (dirichlet_le_vr hR he hs W hWd hInt.1).trans (capDens_integral_le_vr hR hInt.2)
  -- the pointwise bound on the closed interval
  have hpt : ∀ t ∈ Icc (0 : ℝ) (R / 2),
      |W.toFun t - T φ'| ≤ Real.sqrt (R / 2 - t) * Real.sqrt A2 := by
    intro t ht
    have hftc := W.right_sub_integral ht
    rw [hWend] at hftc
    have hsub : uIcc t (R / 2) ⊆ uIcc 0 (R / 2) := by
      rw [uIcc_of_le ht.2, uIcc_of_le hl.le]
      exact Icc_subset_Icc ht.1 le_rfl
    have hg : IntervalIntegrable (fun x => deriv W.toFun x) volume t (R / 2) :=
      W.deriv_int.mono_set hsub
    have hg2 : IntervalIntegrable (fun x => deriv W.toFun x ^ 2) volume t (R / 2) :=
      W.deriv_sq_int.mono_set hsub
    have h1 : |W.toFun t - T φ'| = |∫ x in t..(R / 2), deriv W.toFun x| := by
      rw [hftc, abs_sub_comm, add_sub_cancel_left]
    have h2 : |∫ x in t..(R / 2), deriv W.toFun x| ≤ ∫ x in t..(R / 2), |deriv W.toFun x| :=
      intervalIntegral.abs_integral_le_integral_abs ht.2
    have h3 := sq_integral_abs_le_vr ht.2 hg hg2
    have h4 : ∫ x in t..(R / 2), deriv W.toFun x ^ 2 ≤ Sobolev.dirichlet (R / 2) W := by
      rw [Sobolev.dirichlet]
      exact intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
        (Eventually.of_forall fun x => sq_nonneg _) W.deriv_sq_int
    have h5 : (∫ x in t..(R / 2), |deriv W.toFun x|) ^ 2 ≤ (R / 2 - t) * A2 :=
      h3.trans (mul_le_mul_of_nonneg_left (h4.trans hD) (by linarith [ht.2]))
    have h6 : ∫ x in t..(R / 2), |deriv W.toFun x| ≤ Real.sqrt ((R / 2 - t) * A2) := by
      have hnn : 0 ≤ ∫ x in t..(R / 2), |deriv W.toFun x| :=
        intervalIntegral.integral_nonneg ht.2 (fun x _ => abs_nonneg _)
      have := Real.abs_le_sqrt h5
      rwa [abs_of_nonneg hnn] at this
    rw [h1]
    calc |∫ x in t..(R / 2), deriv W.toFun x|
        ≤ ∫ x in t..(R / 2), |deriv W.toFun x| := h2
      _ ≤ Real.sqrt ((R / 2 - t) * A2) := h6
      _ = Real.sqrt (R / 2 - t) * Real.sqrt A2 := Real.sqrt_mul (by linarith [ht.2]) _
  -- the a.e. bound along the ray, in the radial parameter
  have haet : ∀ᵐ t ∂(volume.restrict (Ioo 0 (R / 2))),
      |u.toFun (capSliceSt c e s R φ' t) - T φ'| ≤ Real.sqrt (R / 2 - t) * Real.sqrt A2 := by
    filter_upwards [hW, ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [← ht]
    exact hpt t (Ioo_subset_Icc_self htI)
  -- pull back to the angle `φ`
  set S : Set ℝ := Ioo 0 (Real.pi / 2) ∩ {φ | tRad_vr R φ φ' ∈ Ioo 0 (R / 2)} with hSdef
  have hScont : Continuous (fun φ => tRad_vr R φ φ') := by
    unfold tRad_vr
    fun_prop
  have hSmeas : MeasurableSet S :=
    measurableSet_Ioo.inter (measurableSet_Ioo.preimage hScont.measurable)
  have haeφ : ∀ᵐ φ ∂(volume.restrict S),
      |u.toFun (capSliceSt c e s R φ' (tRad_vr R φ φ')) - T φ'|
        ≤ Real.sqrt (R / 2 - tRad_vr R φ φ') * Real.sqrt A2 := by
    refine ae_comp_of_hasDerivWithinAt_vr (f := fun φ => tRad_vr R φ φ')
      (f' := fun φ => R * (-Real.sin φ) / Real.cos φ') hSmeas measurableSet_Ioo ?_ ?_ ?_ ?_ ?_
      haet
    · intro φ _
      exact ((((Real.hasDerivAt_cos φ).const_mul R).div_const (Real.cos φ')).sub_const
        (R / 2)).hasDerivWithinAt
    · intro a ha b hb hab
      have hab' : R * Real.cos a / Real.cos φ' = R * Real.cos b / Real.cos φ' := by
        have := hab
        simp only [tRad_vr] at this
        linarith
      have h' : R * Real.cos a = R * Real.cos b := (div_left_inj' hcφ'.ne').1 hab'
      have hcos : Real.cos a = Real.cos b := mul_left_cancel₀ hR.ne' h'
      exact Real.injOn_cos ⟨ha.1.1.le, by linarith [ha.1.2, Real.pi_pos]⟩
        ⟨hb.1.1.le, by linarith [hb.1.2, Real.pi_pos]⟩ hcos
    · intro φ hφ
      have := sin_pos_vr hφ.1
      exact div_ne_zero (mul_ne_zero hR.ne' (neg_ne_zero.2 this.ne')) hcφ'.ne'
    · exact (continuousOn_const.mul Real.continuous_sin.continuousOn.neg).div_const _
    · rintro _ ⟨φ, hφ, rfl⟩
      exact hφ.2
  filter_upwards [ae_imp_of_ae_restrict hSmeas (Ioo 0 (Real.pi / 2)) haeφ,
    ae_restrict_mem measurableSet_Ioo] with φ h1 hφ
  intro hlt hclose
  have hφ'I : φ' ∈ Ioo 0 φ := ⟨hφ'.1, hlt⟩
  have hS : φ ∈ S := ⟨hφ, tRad_mem_vr hR hφ hφ'I hclose⟩
  have h2 := h1 hS
  rw [capSliceSt_tRad_vr hcφ'.ne'] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (tRad_sub_le_vr hR hφ hφ'I)) (Real.sqrt_nonneg _))

end Radial

/-! ## 6. Fubini: reversing the two a.e. quantifiers, and the null pull-back under `Q` -/

section Fubini

variable {L R : ℝ}

/-- **Reversal of the two a.e. quantifiers** in the radial bound (for measurable data), by
Fubini (`Measure.ae_ae_comm`). -/
theorem swap_rad_bound_vr {c e s R : ℝ} {v : CapSpace 1 → ℝ} (hv : Measurable v)
    {T' E' : ℝ → ℝ} (hT' : Measurable T') (hE' : Measurable E')
    (h : ∀ᵐ φ' ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))), φ' < φ → φ - φ' < Real.cos φ →
        |v (meetPt_vr c e s R φ φ') - T' φ'|
          ≤ Real.sqrt ((R / Real.cos φ) * (φ - φ')) * Real.sqrt (E' φ')) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∀ᵐ φ' ∂(volume.restrict (Ioo 0 (Real.pi / 2))), φ' < φ → φ - φ' < Real.cos φ →
        |v (meetPt_vr c e s R φ φ') - T' φ'|
          ≤ Real.sqrt ((R / Real.cos φ) * (φ - φ')) * Real.sqrt (E' φ') := by
  have hA : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  have hB : MeasurableSet {p : ℝ × ℝ | p.2 - p.1 < Real.cos p.2} :=
    measurableSet_lt (measurable_snd.sub measurable_fst) (Real.measurable_cos.comp measurable_snd)
  have hC : MeasurableSet {p : ℝ × ℝ | |v (meetPt_vr c e s R p.2 p.1) - T' p.1|
      ≤ Real.sqrt ((R / Real.cos p.2) * (p.2 - p.1)) * Real.sqrt (E' p.1)} := by
    refine measurableSet_le ?_ ?_
    · exact continuous_abs.measurable.comp
        ((hv.comp ((measurable_meetPt_vr c e s R).comp measurable_swap)).sub
          (hT'.comp measurable_fst))
    · exact (Real.continuous_sqrt.measurable.comp
        ((measurable_const.div (Real.measurable_cos.comp measurable_snd)).mul
          (measurable_snd.sub measurable_fst))).mul
        (Real.continuous_sqrt.measurable.comp (hE'.comp measurable_fst))
  have heq : {p : ℝ × ℝ | p.1 < p.2 → p.2 - p.1 < Real.cos p.2 →
      |v (meetPt_vr c e s R p.2 p.1) - T' p.1|
        ≤ Real.sqrt ((R / Real.cos p.2) * (p.2 - p.1)) * Real.sqrt (E' p.1)}
      = ({p : ℝ × ℝ | p.1 < p.2} ∩ {p : ℝ × ℝ | p.2 - p.1 < Real.cos p.2})ᶜ
        ∪ {p : ℝ × ℝ | |v (meetPt_vr c e s R p.2 p.1) - T' p.1|
          ≤ Real.sqrt ((R / Real.cos p.2) * (p.2 - p.1)) * Real.sqrt (E' p.1)} := by
    ext p
    simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff, not_and]
    tauto
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 → p.2 - p.1 < Real.cos p.2 →
      |v (meetPt_vr c e s R p.2 p.1) - T' p.1|
        ≤ Real.sqrt ((R / Real.cos p.2) * (p.2 - p.1)) * Real.sqrt (E' p.1)} := by
    rw [heq]
    exact (hA.inter hB).compl.union hC
  exact (Measure.ae_ae_comm hmeas).1 h

/-- **The pull-back of a null set under the meeting-point map is null**, in the order
"a.e. `φ`, a.e. `φ'`".  The map `(φ, φ') ↦ Q(φ, φ')` is a fibrewise one-dimensional
diffeomorphism (`φ ↦ capXSt c e R φ` in the first coordinate, then `φ' ↦ s R cos φ tan φ'` in
the second), so the statement follows from Fubini and the one-dimensional change of
variables. -/
theorem ae_ae_meetPt_notMem_vr (hR : 0 < R) {c e s : ℝ} (hg : CapGeomSt L R c e)
    (hs : s ^ 2 = 1) {N : Set (CapSpace 1)} (hN : MeasurableSet N) (hN0 : volume N = 0) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∀ᵐ φ' ∂(volume.restrict (Ioo 0 (Real.pi / 2))), meetPt_vr c e s R φ φ' ∉ N := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have he0 : e ≠ 0 := by
    have := hg.sq_one
    rintro rfl
    norm_num at this
  -- almost every axial section of `N` is null
  have hsec : ∀ᵐ x ∂(volume : Measure ℝ),
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) (Prod.mk x ⁻¹' N) = 0 := by
    have hN0' : ((volume : Measure ℝ).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 1)))) N = 0 := by
      rw [← Measure.volume_eq_prod]
      exact hN0
    have h := (Measure.measure_prod_null hN).1 hN0'
    filter_upwards [h] with x hx
    exact hx
  -- transported to the angle `φ`
  have hφsec : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) (Prod.mk (capXSt c e R φ) ⁻¹' N) = 0 := by
    refine ae_comp_of_hasDerivWithinAt_vr (f := capXSt c e R)
      (f' := fun φ => -(e * (R * Real.sin φ))) measurableSet_Ioo MeasurableSet.univ
      (fun φ _ => CapGeomSt.hasDerivWithinAt_capXSt (c := c) (e := e) (R := R) φ _)
      (hg.injOn_capXSt hR) ?_ ?_ (subset_univ _)
      (P := fun x => (volume : Measure (EuclideanSpace ℝ (Fin 1))) (Prod.mk x ⁻¹' N) = 0) ?_
    · intro φ hφ
      exact neg_ne_zero.2 (mul_ne_zero he0 (mul_ne_zero hR.ne' (sin_pos_vr hφ).ne'))
    · exact (continuousOn_const.mul (continuousOn_const.mul
        Real.continuous_sin.continuousOn)).neg
    · rw [Measure.restrict_univ]
      exact hsec
  filter_upwards [hφsec, ae_restrict_mem measurableSet_Ioo] with φ hφN hφ
  have hcφ := cos_pos_vr hφ
  -- pull back through `ept`
  have hz : ∀ᵐ z ∂(volume : Measure ℝ), ((capXSt c e R φ, ept z) : CapSpace 1) ∉ N := by
    have h1 : (volume : Measure ℝ) (ept ⁻¹' (Prod.mk (capXSt c e R φ) ⁻¹' N)) = 0 :=
      measurePreserving_ept.quasiMeasurePreserving.preimage_null hφN
    rw [ae_iff]
    have : {z : ℝ | ¬ ((capXSt c e R φ, ept z) : CapSpace 1) ∉ N}
        = ept ⁻¹' (Prod.mk (capXSt c e R φ) ⁻¹' N) := by
      ext z
      simp
    rw [this]
    exact h1
  -- pull back through the tangent map
  have key : ∀ᵐ φ' ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ((capXSt c e R φ, ept (s * (R * Real.cos φ) * Real.tan φ')) : CapSpace 1) ∉ N := by
    refine ae_comp_of_hasDerivWithinAt_vr
      (f := fun φ' => s * (R * Real.cos φ) * Real.tan φ')
      (f' := fun φ' => s * (R * Real.cos φ) * (1 / Real.cos φ' ^ 2)) measurableSet_Ioo
      MeasurableSet.univ ?_ ?_ ?_ ?_ (subset_univ _)
      (P := fun y => ((capXSt c e R φ, ept y) : CapSpace 1) ∉ N) ?_
    · intro φ' hφ'
      exact ((Real.hasDerivAt_tan (cos_pos_vr hφ').ne').const_mul _).hasDerivWithinAt
    · intro a ha b hb hab
      have hk : s * (R * Real.cos φ) ≠ 0 := mul_ne_zero hs0 (mul_ne_zero hR.ne' hcφ.ne')
      have htan : Real.tan a = Real.tan b := mul_left_cancel₀ hk hab
      exact Real.strictMonoOn_tan.injOn ⟨by linarith [ha.1, Real.pi_pos], ha.2⟩
        ⟨by linarith [hb.1, Real.pi_pos], hb.2⟩ htan
    · intro φ' hφ'
      exact mul_ne_zero (mul_ne_zero hs0 (mul_ne_zero hR.ne' hcφ.ne'))
        (one_div_ne_zero (pow_ne_zero 2 (cos_pos_vr hφ').ne'))
    · refine continuousOn_const.mul (continuousOn_const.div
        (Real.continuous_cos.continuousOn.pow 2) ?_)
      intro φ' hφ'
      exact pow_ne_zero 2 (cos_pos_vr hφ').ne'
    · rw [Measure.restrict_univ]
      exact hz
  exact key

end Fubini

/-! ## 7. The main theorem -/

section Main

variable {L R : ℝ}

/-- **Identification of the vertical and the radial traces on a cap arc.**  Given the fields
`aesm`, `radAC`, `radIntegrable` and `energy_integrable` of `ArcTraceSt L R u c e s T`, the
vertical endpoint trace `trSideSt s u` at the abscissa `capXSt c e R φ` of the arc point of
angle `φ` equals the radial trace `T φ` for almost every `φ ∈ (0, π/2)`: this is the field
`vert_eq`. -/
theorem vert_eq_rad_vr (hR : 0 < R) (hL : 2 * R < L)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1)
    (haesm : AEStronglyMeasurable T (volume.restrict (Ioo 0 (Real.pi / 2))))
    (hrad : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∃ W : Sobolev.H1 (R / 2),
        W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => u.toFun (capSliceSt c e s R φ t)) ∧
          deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
              + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ∧
          W.toFun (R / 2) = T φ)
    (hint : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume ∧
        IntegrableOn (fun t => capDensSt R u c e s φ t * (t + R / 2)) (Ioo 0 (R / 2)) volume)
    (henergy : IntegrableOn (arcEnergySt R u c e s) (Ioo 0 (Real.pi / 2)) volume) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))), trSideSt s u (capXSt c e R φ) = T φ := by
  classical
  have he := hg.sq_one
  have hL' := hLK_st hL
  set I : Set ℝ := Ioo 0 (Real.pi / 2) with hIdef
  have hImeas : MeasurableSet I := measurableSet_Ioo
  have hΩ : MeasurableSet (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) :=
    measurableSet_thinDomain hR hL'
  -- measurable versions of `T`, of the polar energy, and of `u`
  set T' : ℝ → ℝ := haesm.mk T with hT'def
  have hT'm : Measurable T' := haesm.stronglyMeasurable_mk.measurable
  have hT'ae : T =ᵐ[volume.restrict I] T' := haesm.ae_eq_mk
  set E0 : ℝ → ℝ := henergy.aestronglyMeasurable.mk (arcEnergySt R u c e s) with hE0def
  set E' : ℝ → ℝ := fun φ => (2 / R) * |E0 φ| with hE'def
  have hE'm : Measurable E' :=
    measurable_const.mul
      (continuous_abs.measurable.comp henergy.aestronglyMeasurable.stronglyMeasurable_mk.measurable)
  have hE'ae : ∀ᵐ φ ∂(volume.restrict I), E' φ = (2 / R) * arcEnergySt R u c e s φ := by
    filter_upwards [henergy.aestronglyMeasurable.ae_eq_mk] with φ hφ
    have hφ' : arcEnergySt R u c e s φ = E0 φ := hφ
    show (2 / R) * |E0 φ| = (2 / R) * arcEnergySt R u c e s φ
    rw [← hφ', abs_of_nonneg (arcEnergySt_nonneg hR u c e s φ)]
  have hE'nn : ∀ φ, 0 ≤ E' φ := fun φ => by
    show 0 ≤ (2 / R) * |E0 φ|
    positivity
  set v : CapSpace 1 → ℝ := u.memL2.aestronglyMeasurable.mk u.toFun with hvdef
  have hvm : Measurable v := u.memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hbad : volume ({p | ¬ u.toFun p = v p}
      ∩ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R) = 0 := by
    have := u.memL2.aestronglyMeasurable.ae_eq_mk
    rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' hΩ] at this
    exact this
  obtain ⟨N, hNsup, hNmeas, hNzero⟩ := exists_measurable_superset_of_null hbad
  have huv : ∀ p ∈ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R, p ∉ N →
      u.toFun p = v p := by
    intro p hp hpN
    by_contra hcon
    exact hpN (hNsup ⟨hcon, hp⟩)
  -- the null pull-back under `Q`, in both orders
  have hnot : ∀ᵐ φ ∂(volume.restrict I), ∀ᵐ φ' ∂(volume.restrict I),
      meetPt_vr c e s R φ φ' ∉ N := ae_ae_meetPt_notMem_vr hR hg hs hNmeas hNzero
  have hnot' : ∀ᵐ φ' ∂(volume.restrict I), ∀ᵐ φ ∂(volume.restrict I),
      meetPt_vr c e s R φ φ' ∉ N := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | meetPt_vr c e s R p.1 p.2 ∉ N} :=
      ((measurable_meetPt_vr c e s R) hNmeas).compl
    exact (Measure.ae_ae_comm hmeas).1 hnot
  -- the radial bound with the measurable versions, a.e. `φ'` then a.e. `φ`
  have hrad2 : ∀ᵐ φ' ∂(volume.restrict I), ∀ᵐ φ ∂(volume.restrict I),
      φ' < φ → φ - φ' < Real.cos φ →
        |v (meetPt_vr c e s R φ φ') - T' φ'|
          ≤ Real.sqrt ((R / Real.cos φ) * (φ - φ')) * Real.sqrt (E' φ') := by
    filter_upwards [hrad, hint, hT'ae, hE'ae, ae_restrict_mem hImeas, hnot']
      with φ' hAC hInt hT'φ hE'φ hφ' hnotφ'
    filter_upwards [rad_bound_vr hR he hs hφ' hAC hInt, hnotφ', ae_restrict_mem hImeas]
      with φ h1 h2 hφ
    intro hlt hclose
    have hmem := meetPt_mem_vr hR hg hs hφ ⟨hφ'.1, hlt⟩
    rw [← huv _ hmem h2, ← hT'φ, hE'φ]
    exact h1 hlt hclose
  have hswap := swap_rad_bound_vr hvm hT'm hE'm hrad2
  -- almost every arc abscissa is a good slice
  have hgood : ∀ᵐ φ ∂(volume.restrict I), SliceGood u (capXSt c e R φ) := by
    have he0 : e ≠ 0 := by
      rintro rfl
      norm_num at he
    refine ae_comp_of_hasDerivWithinAt_vr (f := capXSt c e R)
      (f' := fun φ => -(e * (R * Real.sin φ))) hImeas measurableSet_Ioo
      (fun φ _ => CapGeomSt.hasDerivWithinAt_capXSt (c := c) (e := e) (R := R) φ _)
      (hg.injOn_capXSt hR) ?_ ?_ ?_ (ae_sliceGood hR hL' u)
    · intro φ hφ
      exact neg_ne_zero.2 (mul_ne_zero he0 (mul_ne_zero hR.ne' (sin_pos_vr hφ).ne'))
    · exact (continuousOn_const.mul (continuousOn_const.mul
        Real.continuous_sin.continuousOn)).neg
    · rintro _ ⟨φ, hφ, rfl⟩
      exact hg.sub (hg.capXSt_mem hR hφ)
  -- the integrable data of the core lemma
  set T₀ : ℝ → ℝ := I.indicator T' with hT₀def
  set E₀ : ℝ → ℝ := I.indicator E' with hE₀def
  have hTint : IntegrableOn T' I volume :=
    (integrableOn_T_vr hR he hs haesm hrad hint henergy).congr_fun_ae hT'ae
  have hT₀ : Integrable T₀ := hTint.integrable_indicator hImeas
  have hEint : IntegrableOn E' I volume :=
    (henergy.const_mul (2 / R)).congr (hE'ae.mono fun φ h => h.symm)
  have hE₀ : Integrable E₀ := hEint.integrable_indicator hImeas
  have hE₀nn : ∀ φ, 0 ≤ E₀ φ := fun φ => Set.indicator_nonneg (fun φ _ => hE'nn φ) φ
  -- the hypothesis of the core lemma
  have hcore : ∀ᵐ φ ∂(volume.restrict I), ∀ ε > 0, ∃ η > 0, ∃ C, 0 ≤ C ∧
      ∀ᵐ φ' ∂(volume.restrict I), φ - η < φ' → φ' < φ →
        |trSideSt s u (capXSt c e R φ) - T₀ φ'|
          ≤ ε + Real.sqrt (C * (φ - φ')) * Real.sqrt (E₀ φ') := by
    filter_upwards [hswap, hgood, hnot, ae_restrict_mem hImeas] with φ h1 h2 h3 hφ
    intro ε hε
    obtain ⟨η, hη, hvert⟩ := vert_bound_vr hR hg hs hφ h2 hε
    have hcφ := cos_pos_vr hφ
    refine ⟨min η (Real.cos φ), lt_min hη hcφ, R / Real.cos φ, by positivity, ?_⟩
    filter_upwards [h1, h3, hvert, ae_restrict_mem hImeas] with φ' h1' h3' hv hφ'
    intro hlow hup
    have hm1 := min_le_left η (Real.cos φ)
    have hm2 := min_le_right η (Real.cos φ)
    have hclose : φ - φ' < Real.cos φ := by linarith
    have hmem := meetPt_mem_vr hR hg hs hφ ⟨hφ'.1, hup⟩
    have huQ : u.toFun (meetPt_vr c e s R φ φ') = v (meetPt_vr c e s R φ φ') := huv _ hmem h3'
    have hb1 := hv (by linarith) hup
    have hb2 := h1' hup hclose
    rw [← huQ] at hb2
    have hT₀φ' : T₀ φ' = T' φ' := Set.indicator_of_mem hφ' _
    have hE₀φ' : E₀ φ' = E' φ' := Set.indicator_of_mem hφ' _
    rw [hT₀φ', hE₀φ']
    calc |trSideSt s u (capXSt c e R φ) - T' φ'|
        ≤ |trSideSt s u (capXSt c e R φ) - u.toFun (meetPt_vr c e s R φ φ')|
          + |u.toFun (meetPt_vr c e s R φ φ') - T' φ'| := abs_sub_le _ _ _
      _ ≤ ε + Real.sqrt ((R / Real.cos φ) * (φ - φ')) * Real.sqrt (E' φ') := by
          rw [abs_sub_comm] at hb1
          linarith
  -- conclusion
  have hfinal := ae_eq_of_pair_bound_vr hT₀ hE₀ hE₀nn hcore
  filter_upwards [hfinal, hT'ae, ae_restrict_mem hImeas] with φ h1 h2 hφ
  rw [h1, h2]
  exact Set.indicator_of_mem hφ _

/-- **`ArcTraceSt` from its five analytic fields.**  The identification field `vert_eq` is
supplied by `vert_eq_rad_vr`, so a radial trace `T` satisfying `aesm`, `radAC`,
`radIntegrable`, `energy_integrable` and `energy_le` is an `ArcTraceSt`. -/
theorem arcTraceSt_of_fields_vr (hR : 0 < R) (hL : 2 * R < L)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (hg : CapGeomSt L R c e) (hs : s ^ 2 = 1)
    (haesm : AEStronglyMeasurable T (volume.restrict (Ioo 0 (Real.pi / 2))))
    (hrad : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      ∃ W : Sobolev.H1 (R / 2),
        W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => u.toFun (capSliceSt c e s R φ t)) ∧
          deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
            (fun t => e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
              + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ∧
          W.toFun (R / 2) = T φ)
    (hint : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume ∧
        IntegrableOn (fun t => capDensSt R u c e s φ t * (t + R / 2)) (Ioo 0 (R / 2)) volume)
    (henergy : IntegrableOn (arcEnergySt R u c e s) (Ioo 0 (Real.pi / 2)) volume)
    (hle : (∫ φ in Ioo 0 (Real.pi / 2), arcEnergySt R u c e s φ) ≤ massP u + dirichletP u) :
    ArcTraceSt L R u c e s T where
  aesm := haesm
  radAC := hrad
  radIntegrable := hint
  energy_integrable := henergy
  energy_le := hle
  vert_eq := vert_eq_rad_vr hR hL hg hs haesm hrad hint henergy

end Main

end RobinCaps.ThinDomain

end
