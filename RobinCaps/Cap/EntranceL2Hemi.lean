import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.Concave
import RobinCaps.ThinDomain.TraceOne

/-!
# The entrance trace of a weak `H¹` function on the unit half-disk is square integrable

This file discharges the interface `RobinCaps.Cap.CapEntranceL2` of `RobinCaps/Cap/LowerWeak.lean`
for the two-dimensional hemispherical cap `Cap.hemisphere 1`, i.e. for the half-disk

`C = {(s,z) | -1 < s < 0, ‖z‖ < √(1-(s+1)²)} ⊆ ℝ × EuclideanSpace ℝ (Fin 1)`,

by an elementary two-region slicing argument (no Rellich, no compactness).

## The argument

Write `ℓ(z) = √(1-‖z‖²)` for the length of the axial slice through `z` and `V = Tr_Σ u` for the
entrance trace.  The one-dimensional trace inequality at the left endpoint
(`RobinCaps.Sobolev.endpoint_zero_sq_le`) applied to the absolutely continuous representative of
the axial slice (`RobinCaps.Cap.exists_h1_axialSlice`) gives, for almost every `z`,

`V(z)² ≤ (2/ℓ(z)) ∫_slice u² + 2ℓ(z) ∫_slice (∂ₓu)²`.

The second term is harmless (`ℓ ≤ 1`).  The first term carries the singular weight `1/ℓ(z)`,
which degenerates as `‖z‖ → 1`.  Two observations save it:

* **the weight is integrable**: `∫_{-1}^{1} (1-y²)^{-1/2} dy = π` (the arcsine primitive; the
  endpoint singularity is handled by `intervalIntegral.intervalIntegrable_deriv_of_nonneg`);
* **the axial mass of a short slice is uniformly bounded**: if `ℓ(z) < 1/√2` then the whole slice
  lies in the region `s + 1 < 1/√2`, where the transverse section is *wider* than `1/√2`; the
  transverse fundamental theorem of calculus (`sliceAC_transverse_cap_el`) then bounds
  `u(s,z)²` by a function `g(s)` of the axial variable alone whose integral is controlled by
  `‖u‖² + ‖∇u‖²`.

Combining, `∫_{B(0,1)} V² ≤ 40 (‖u‖²_{L²(C)} + ‖∇u‖²_{L²(C)})`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Transverse

noncomputable section

/-! ## 1. The geometry of the unit half-disk -/

/-- The cut-off radius `1/√2`: the transverse section of the half-disk at axial coordinate `s`
is wider than `rad_el` exactly when `s + 1 < rad_el`. -/
def rad_el : ℝ := 1 / Real.sqrt 2

theorem rad_pos_el : 0 < rad_el := by
  rw [rad_el]
  positivity

theorem rad_sq_el : rad_el ^ 2 = 1 / 2 := by
  rw [rad_el, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem rad_lt_one_el : rad_el < 1 := by
  nlinarith [rad_sq_el, rad_pos_el]

theorem inv_rad_el : 1 / rad_el = Real.sqrt 2 := by
  rw [rad_el, one_div_one_div]

theorem sqrt_two_lt_el : Real.sqrt 2 < 3 / 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

@[simp] theorem hemi_K_el : (hemisphere 1).K = 1 := rfl

theorem hemi_theta_el (s : ℝ) : (hemisphere 1).θ s = Real.sqrt (1 - (s + 1) ^ 2) := rfl

/-- Equality of two intervals with a common left endpoint forces equality of the right
endpoints. -/
theorem Ioo_right_eq_el {a b c : ℝ} (hb : a < b) (hc : a < c) (h : Ioo a b = Ioo a c) : b = c := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨x, hx1, hx2⟩ := exists_between hlt
    have hxa : a < x := hb.trans hx1
    have : x ∈ Ioo a c := ⟨hxa, hx2⟩
    rw [← h] at this
    exact absurd this.2 (not_lt.2 hx1.le)
  · obtain ⟨x, hx1, hx2⟩ := exists_between hlt
    have hxa : a < x := hc.trans hx1
    have : x ∈ Ioo a b := ⟨hxa, hx2⟩
    rw [h] at this
    exact absurd this.2 (not_lt.2 hx1.le)

/-- The radial slice of the half-disk at radius `t`. -/
theorem radialSlice_hemi_el {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) :
    radialSlice (hemisphere 1) t = Ioo (-1) (Real.sqrt (1 - t ^ 2) - 1) := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  have hs1 : Real.sqrt (1 - t ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  have hs0 : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hpos
  ext s
  simp only [mem_radialSlice, mem_Ioo, hemi_K_el, hemi_theta_el]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨by linarith, ?_⟩
    have hts : t ^ 2 < 1 - (s + 1) ^ 2 := (Real.lt_sqrt ht0).1 h3
    have : (s + 1) ^ 2 < 1 - t ^ 2 := by linarith
    have := (Real.lt_sqrt (by linarith : (0:ℝ) ≤ s + 1)).2 this
    linarith
  · rintro ⟨h1, h2⟩
    have hs2 : s < 0 := by linarith
    refine ⟨⟨by linarith, hs2⟩, ?_⟩
    have h3 : s + 1 < Real.sqrt (1 - t ^ 2) := by linarith
    have h4 : (s + 1) ^ 2 < 1 - t ^ 2 := (Real.lt_sqrt (by linarith : (0:ℝ) ≤ s + 1)).1 h3
    exact (Real.lt_sqrt ht0).2 (by linarith)

/-- **The length of the axial slice of the half-disk**: `exitTime + K = √(1-‖z‖²)`. -/
theorem exitTime_hemi_el {z : EuclideanSpace ℝ (Fin 1)} (hz : ‖z‖ < 1) :
    exitTime (hemisphere 1) z + 1 = Real.sqrt (1 - ‖z‖ ^ 2) := by
  have h1 : radialSlice (hemisphere 1) ‖z‖ = Ioo (-1) (exitTime (hemisphere 1) z) := by
    have := radialSlice_eq (hemisphere 1) ‖z‖
    rwa [hemi_K_el, ← exitTime] at this
  have h2 := radialSlice_hemi_el (norm_nonneg z) hz
  have hlt1 : (-1 : ℝ) < exitTime (hemisphere 1) z := by
    have := (exitTime_mem (hemisphere 1) hz).1
    rwa [hemi_K_el] at this
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hs0 : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.2 hpos
  have := Ioo_right_eq_el hlt1 (by linarith : (-1:ℝ) < Real.sqrt (1 - ‖z‖ ^ 2) - 1)
    (h1 ▸ h2)
  linarith

/-- On the far-left part of the half-disk the transverse section is wider than `rad_el`. -/
theorem rad_lt_theta_el {s : ℝ} (h1 : -1 < s) (h2 : s + 1 < rad_el) :
    rad_el < (hemisphere 1).θ s := by
  rw [hemi_theta_el]
  refine (Real.lt_sqrt rad_pos_el.le).2 ?_
  have h3 : (s + 1) ^ 2 < rad_el ^ 2 := by
    have h0 : 0 < s + 1 := by linarith
    nlinarith
  rw [rad_sq_el] at h3 ⊢
  linarith

/-! ## 2. The singular weight `1/ℓ` is integrable on the entrance disk -/

/-- The arcsine density `(1-y²)^{-1/2}`. -/
def arcDen_el (y : ℝ) : ℝ := 1 / Real.sqrt (1 - y ^ 2)

theorem arcDen_nonneg_el (y : ℝ) : 0 ≤ arcDen_el y := by
  rw [arcDen_el]; positivity

theorem hasDerivAt_arcsin_el {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.arcsin (arcDen_el y) y :=
  Real.hasDerivAt_arcsin (ne_of_gt hy.1) (ne_of_lt hy.2)

theorem intervalIntegrable_arcDen_el :
    IntervalIntegrable arcDen_el volume (-1) 1 := by
  have hcont : ContinuousOn Real.arcsin (uIcc (-1 : ℝ) 1) := Real.continuous_arcsin.continuousOn
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont ?_ ?_
  · intro x hx
    rw [min_eq_left (by norm_num : (-1:ℝ) ≤ 1), max_eq_right (by norm_num : (-1:ℝ) ≤ 1)] at hx
    exact hasDerivAt_arcsin_el hx
  · intro x _
    exact arcDen_nonneg_el x

/-- **The arcsine integral** `∫_{-1}^{1} (1-y²)^{-1/2} dy = π`. -/
theorem integral_arcDen_el : (∫ y in (-1 : ℝ)..1, arcDen_el y) = Real.pi := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hcont : ContinuousOn Real.arcsin (Icc (-1 : ℝ) 1) := Real.continuous_arcsin.continuousOn
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
    (fun x hx => hasDerivAt_arcsin_el hx) intervalIntegrable_arcDen_el
  rw [h, Real.arcsin_one, Real.arcsin_neg, Real.arcsin_one]
  ring

/-- The singular weight `z ↦ 2/ℓ(z)`, cut off to the outer annulus `‖z‖ > 1/√2`. -/
def wt_el (z : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  if rad_el < ‖z‖ then 2 / Real.sqrt (1 - ‖z‖ ^ 2) else 0

theorem wt_nonneg_el (z : EuclideanSpace ℝ (Fin 1)) : 0 ≤ wt_el z := by
  rw [wt_el]
  split
  · positivity
  · exact le_rfl

theorem measurable_ept_el : Measurable ept := eptEquiv.measurable

/-- Integrability through the identification `ept` (the one-dimensional companion of
`RobinCaps.Cap.integrableOn_prodBox_transverse`). -/
theorem integrableOn_comp_ept_el {ρ : ℝ} (f : EuclideanSpace ℝ (Fin 1) → ℝ) :
    IntegrableOn (fun y => f (ept y)) (Ioo (-ρ) ρ) volume
      ↔ IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ) volume := by
  rw [← ept_preimage_ball ρ]
  exact measurePreserving_ept.integrableOn_comp_preimage eptEquiv.measurableEmbedding

theorem measurable_wt_el : Measurable wt_el := by
  refine Measurable.ite (measurableSet_lt measurable_const measurable_norm) ?_ measurable_const
  fun_prop

theorem wt_le_el (y : ℝ) : wt_el (ept y) ≤ 2 * arcDen_el y := by
  have hn : ‖ept y‖ = |y| := ept_norm y
  have hsq : |y| ^ 2 = y ^ 2 := sq_abs y
  rw [wt_el, hn, arcDen_el]
  split
  · rw [hsq]
    rw [mul_one_div]
  · positivity

/-- **The singular weight is integrable on the entrance disk, with `∫ ≤ 2π`.** -/
theorem integrableOn_wt_el :
    IntegrableOn wt_el (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) volume := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hmaj : IntervalIntegrable (fun y => 2 * arcDen_el y) volume (-1) 1 :=
    intervalIntegrable_arcDen_el.const_mul 2
  have hmeas : AEStronglyMeasurable (fun y => wt_el (ept y)) (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    (measurable_wt_el.comp measurable_ept_el).aestronglyMeasurable
  have hI : IntegrableOn (fun y => wt_el (ept y)) (Ioc (-1 : ℝ) 1) volume := by
    refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hmaj)
      hmeas ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (wt_nonneg_el _)]
    exact wt_le_el y
  have hIoo : IntegrableOn (fun y => wt_el (ept y)) (Ioo (-1 : ℝ) 1) volume :=
    hI.mono_set Ioo_subset_Ioc_self
  exact (integrableOn_comp_ept_el (ρ := 1) wt_el).1 hIoo

theorem integral_wt_le_el :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, wt_el z) ≤ 2 * Real.pi := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hmaj : IntervalIntegrable (fun y => 2 * arcDen_el y) volume (-1) 1 :=
    intervalIntegrable_arcDen_el.const_mul 2
  have hmeas : AEStronglyMeasurable (fun y => wt_el (ept y)) (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    (measurable_wt_el.comp measurable_ept_el).aestronglyMeasurable
  have hI : IntervalIntegrable (fun y => wt_el (ept y)) volume (-1) 1 := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 ?_
    refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hmaj)
      hmeas ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (wt_nonneg_el _)]
    exact wt_le_el y
  rw [integral_ball_one (by norm_num : (0:ℝ) ≤ 1) wt_el]
  have hmono : (∫ y in (-1 : ℝ)..1, wt_el (ept y)) ≤ ∫ y in (-1 : ℝ)..1, 2 * arcDen_el y :=
    intervalIntegral.integral_mono_on hle hI hmaj (fun y _ => wt_le_el y)
  rw [intervalIntegral.integral_const_mul, integral_arcDen_el] at hmono
  exact hmono

/-! ## 3. Transverse slice-wise absolute continuity on a two-dimensional cap

This section re-derives, for a general two-dimensional cap, the transverse companion of
`RobinCaps.Cap.sliceAC_axial_cap`: on almost every level `σ` the transverse slice
`y ↦ u(σ, ept y)` has `y ↦ (∇_z u)(σ, ept y)₀` as a weak derivative on the whole section. -/

variable {m : ℕ}

/-- **Translation of a one-dimensional weak derivative.** -/
theorem hasWeakDeriv_shift_el {a b h : ℝ} {F G : ℝ → ℝ} (hw : HasWeakDeriv a b F G) :
    HasWeakDeriv (a - h) (b - h) (fun y => F (y + h)) (fun y => G (y + h)) := by
  intro φ hφ hφc hφs
  rcases le_or_gt b a with hba | hab
  · have e2 : Ioo (a - h) (b - h) = ∅ := Ioo_eq_empty (by push_neg; linarith)
    simp [e2]
  have hχ : ContDiff ℝ ∞ fun x : ℝ => φ (x - h) := hφ.comp (contDiff_id.sub contDiff_const)
  have hKφ : IsCompact (tsupport φ) := hφc
  have himg : IsCompact ((fun y : ℝ => y + h) '' tsupport φ) :=
    hKφ.image (continuous_id.add continuous_const)
  have hsub : tsupport (fun x : ℝ => φ (x - h)) ⊆ (fun y : ℝ => y + h) '' tsupport φ :=
    closure_minimal (fun x hx => ⟨x - h, subset_tsupport φ hx, by ring⟩) himg.isClosed
  have hχc : HasCompactSupport fun x : ℝ => φ (x - h) :=
    himg.of_isClosed_subset (isClosed_tsupport _) hsub
  have hχs : tsupport (fun x : ℝ => φ (x - h)) ⊆ Ioo a b := by
    refine hsub.trans ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hφs hy
    simp only [Set.mem_Ioo] at hy' ⊢
    exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  have hd : ∀ x : ℝ, deriv (fun t : ℝ => φ (t - h)) x = deriv φ (x - h) := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t - h) 1 x := (hasDerivAt_id x).sub_const h
    have h2 : HasDerivAt φ (deriv φ (x - h)) (x - h) :=
      (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
    simpa using (h2.comp x h1).deriv
  have hmain := hw (fun x : ℝ => φ (x - h)) hχ hχc hχs
  have hle : (a - h) ≤ (b - h) := by linarith
  have t1 : (∫ y in Ioo (a - h) (b - h), F (y + h) * deriv φ y)
      = ∫ x in Ioo a b, F x * deriv (fun t : ℝ => φ (t - h)) x := by
    rw [← Sobolev.intervalIntegral_eq_setIntegral_Ioo hle,
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hab.le]
    simp only [hd]
    have key := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => F x * deriv φ (x - h)) (a := a - h) (b := b - h) h
    simpa using key
  have t2 : (∫ y in Ioo (a - h) (b - h), G (y + h) * φ y)
      = ∫ x in Ioo a b, G x * φ (x - h) := by
    rw [← Sobolev.intervalIntegral_eq_setIntegral_Ioo hle,
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hab.le]
    have key := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => G x * φ (x - h)) (a := a - h) (b := b - h) h
    simpa using key
  rw [t1, t2]
  exact hmain

/-- **The transverse slice transport on a symmetric interval.** -/
theorem hasWeakDeriv_ept_of_hasWeakGrad_el {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} {g : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
    (h : Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ) f g) :
    HasWeakDeriv (-ρ) ρ (fun y => f (ept y)) (fun y => g (ept y) 0) := by
  have h0 := ThinDomain.hasWeakDeriv_of_hasWeakGrad_ball hρ h
  have h1 := hasWeakDeriv_shift_el (h := ρ) h0
  have hshift : ∀ y : ℝ, eptSh ρ (y + ρ) = ept y := by
    intro y; simp [eptSh]
  have e1 : (0 : ℝ) - ρ = -ρ := by ring
  have e2 : 2 * ρ - ρ = ρ := by ring
  rw [e1, e2] at h1
  simpa only [hshift] using h1

/-- The transverse slice statement on one sub-cylinder `(-K,c) × B(0, θ c)`. -/
theorem sliceAC_transverse_sub_el (C : Cap 1) (u : H1P C.body) {c : ℝ} (hc : c ∈ Ioo (-C.K) 0) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) c)),
      HasWeakDeriv (-(C.θ c)) (C.θ c) (fun y => u.toFun (σ, ept y))
        (fun y => u.gz (σ, ept y) 0) := by
  have hsub := prodSub_subset_body C hc
  have h : ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) c)),
      Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ c))
        (fun z => (u.restrict hsub).toFun (σ, z)) (fun z => (u.restrict hsub).gz (σ, z)) :=
    ThinDomain.sliceACL_transverse (a := -C.K) (b := c)
      (B := ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ c)) (u.restrict hsub)
  filter_upwards [h] with σ hσ
  simp only [H1P.restrict_toFun, H1P.restrict_gz] at hσ
  exact hasWeakDeriv_ept_of_hasWeakGrad_el (C.θ_pos c hc) hσ

/-- Two-sided version of `RobinCaps.Cap.setIntegral_Ioo_eq_of_vanishing`. -/
theorem setIntegral_Ioo_eq_of_vanishing_el {a b a' b' : ℝ} (h1 : a ≤ a') (h2 : b' ≤ b)
    {f w : ℝ → ℝ} (hw : ∀ x, x ∉ Ioo a' b' → w x = 0) :
    ∫ x in Ioo a b, f x * w x = ∫ x in Ioo a' b', f x * w x := by
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo
    (Ioo_subset_Ioo h1 h2) ?_
  rintro x ⟨-, hx2⟩
  rw [hw x hx2, mul_zero]

/-- Two-sided version of `RobinCaps.Cap.hasWeakDeriv_extend_test`. -/
theorem hasWeakDeriv_extend_test_el {a b a' b' : ℝ} (h1 : a ≤ a') (h2 : b' ≤ b) {v g : ℝ → ℝ}
    (h : HasWeakDeriv a' b' v g) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a' b') :
    ∫ x in Ioo a b, v x * deriv φ x = - ∫ x in Ioo a b, g x * φ x := by
  obtain ⟨hv1, hv2⟩ := test_vanishing hφs
  rw [setIntegral_Ioo_eq_of_vanishing_el h1 h2 hv2, setIntegral_Ioo_eq_of_vanishing_el h1 h2 hv1]
  exact h φ hφ hφc hφs

/-- **The profile is almost attained from the right by rational arguments.** -/
theorem exists_rat_theta_gt_el (C : Cap m) {σ M : ℝ} (hσ : σ ∈ Ioo (-C.K) 0)
    (hM : M < C.θ σ) : ∃ q : ℚ, (q : ℝ) ∈ Ioo σ 0 ∧ M < C.θ (q : ℝ) := by
  have hcont : ContinuousAt C.θ σ :=
    (Concave.continuousOn_Ioo C).continuousAt (Ioo_mem_nhds hσ.1 hσ.2)
  have hev : ∀ᶠ x in 𝓝 σ, M < C.θ x := hcont (lt_mem_nhds hM)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set d : ℝ := min (ε / 2) (-σ / 2) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by linarith [hσ.2])
  have hd1 : d ≤ ε / 2 := min_le_left _ _
  have hd2 : d ≤ -σ / 2 := min_le_right _ _
  set x₀ : ℝ := σ + d with hx₀
  have hx₀1 : σ < x₀ := by rw [hx₀]; linarith
  have hx₀2 : x₀ < 0 := by rw [hx₀]; linarith
  have hx₀K : -C.K < x₀ := by linarith [hσ.1]
  have hdist : dist x₀ σ < ε := by
    rw [Real.dist_eq, hx₀]
    have : |σ + d - σ| = d := by rw [show σ + d - σ = d by ring, abs_of_pos hd0]
    rw [this]; linarith
  have hx₀θ : M < C.θ x₀ := hball hdist
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx₀1
  refine ⟨q, ⟨hq1, hq2.trans hx₀2⟩, ?_⟩
  have hqI : (q : ℝ) ∈ Ioo (-C.K) 0 := ⟨hσ.1.trans hq1, hq2.trans hx₀2⟩
  have hx₀I : x₀ ∈ Ioo (-C.K) 0 := ⟨hx₀K, hx₀2⟩
  exact lt_of_lt_of_le hx₀θ (C.θ_antitone hqI hx₀I hq2.le)

/-- **Transverse ACL on a two-dimensional cap body.** -/
theorem sliceAC_transverse_cap_el (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)),
      HasWeakDeriv (-(C.θ σ)) (C.θ σ) (fun y => u.toFun (σ, ept y))
        (fun y => u.gz (σ, ept y) 0) := by
  have hfam : ∀ q : ℚ, ∀ᵐ σ ∂(volume : Measure ℝ),
      (q : ℝ) ∈ Ioo (-C.K) 0 → σ ∈ Ioo (-C.K) (q : ℝ) →
        HasWeakDeriv (-(C.θ (q : ℝ))) (C.θ (q : ℝ)) (fun y => u.toFun (σ, ept y))
          (fun y => u.gz (σ, ept y) 0) := by
    intro q
    by_cases hq : (q : ℝ) ∈ Ioo (-C.K) 0
    · have h := sliceAC_transverse_sub_el C u hq
      rw [ae_restrict_iff' measurableSet_Ioo] at h
      filter_upwards [h] with σ hσ _ hmem
      exact hσ hmem
    · filter_upwards with σ h1
      exact absurd h1 hq
  have hall := ae_all_iff.2 hfam
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hall] with σ hσ hσmem
  intro φ hφ hφc hφs
  have hθ : 0 < C.θ σ := C.θ_pos σ hσmem
  set S : Set ℝ := tsupport φ ∪ {(0 : ℝ)} with hS
  have hScompact : IsCompact S := hφc.union isCompact_singleton
  have hSne : S.Nonempty := ⟨0, Or.inr rfl⟩
  have hSsub : S ⊆ Ioo (-(C.θ σ)) (C.θ σ) := by
    rintro x (hx | hx)
    · exact hφs hx
    · rw [mem_singleton_iff] at hx; rw [hx]; exact ⟨by linarith, hθ⟩
  have hsup : sSup S ∈ S := hScompact.sSup_mem hSne
  have hinf : sInf S ∈ S := hScompact.sInf_mem hSne
  set M : ℝ := max (sSup S) (-(sInf S)) with hM
  have hMlt : M < C.θ σ := by
    rw [hM]
    exact max_lt (hSsub hsup).2 (by linarith [(hSsub hinf).1])
  obtain ⟨q, hqI, hqθ⟩ := exists_rat_theta_gt_el C hσmem hMlt
  have hqIoo : (q : ℝ) ∈ Ioo (-C.K) 0 := ⟨hσmem.1.trans hqI.1, hqI.2⟩
  have hkey := hσ q hqIoo ⟨hσmem.1, hqI.1⟩
  have hφq : tsupport φ ⊆ Ioo (-(C.θ (q : ℝ))) (C.θ (q : ℝ)) := by
    intro x hx
    have hx1 : x ≤ sSup S := le_csSup hScompact.bddAbove (Or.inl hx)
    have hx2 : sInf S ≤ x := csInf_le hScompact.bddBelow (Or.inl hx)
    have hx3 : x ≤ M := hx1.trans (le_max_left _ _)
    have hx4 : -M ≤ x := by
      have : -(sInf S) ≤ M := le_max_right _ _
      linarith
    exact ⟨by linarith, by linarith⟩
  have hmono : C.θ (q : ℝ) ≤ C.θ σ := C.θ_antitone hσmem hqIoo hqI.1.le
  refine hasWeakDeriv_extend_test_el ?_ hmono hkey hφ hφc hφq
  linarith

/-! ## 4. Measurable representatives and the two slice energies -/

theorem memL2_repFun_el (C : Cap m) (u : H1P C.body) :
    MemLp (repFun C u) 2 (volume.restrict C.body) :=
  (memLp_congr_ae u.memL2.aestronglyMeasurable.ae_eq_mk).1 u.memL2

theorem memL2_repGx_el (C : Cap m) (u : H1P C.body) :
    MemLp (repGx C u) 2 (volume.restrict C.body) :=
  (memLp_congr_ae u.gx_memL2.aestronglyMeasurable.ae_eq_mk).1 u.gx_memL2

/-- A globally strongly measurable representative of `∇_z u`. -/
def repGz_el (C : Cap m) (u : H1P C.body) : CapSpace m → EuclideanSpace ℝ (Fin m) :=
  u.gz_memL2.aestronglyMeasurable.mk u.gz

theorem stronglyMeasurable_repGz_el (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (repGz_el C u) := u.gz_memL2.aestronglyMeasurable.stronglyMeasurable_mk

theorem repGz_ae_eq_el (C : Cap m) (u : H1P C.body) :
    u.gz =ᵐ[volume.restrict C.body] repGz_el C u :=
  u.gz_memL2.aestronglyMeasurable.ae_eq_mk

theorem memL2_repGz_el (C : Cap m) (u : H1P C.body) :
    MemLp (repGz_el C u) 2 (volume.restrict C.body) :=
  (memLp_congr_ae (repGz_ae_eq_el C u)).1 u.gz_memL2

theorem integrableOn_repGx_sq_el (C : Cap m) (u : H1P C.body) :
    IntegrableOn (fun p => repGx C u p ^ 2) C.body volume :=
  (memL2_repGx_el C u).integrable_sq

theorem integrableOn_repFun_sq_el (C : Cap m) (u : H1P C.body) :
    IntegrableOn (fun p => repFun C u p ^ 2) C.body volume :=
  (memL2_repFun_el C u).integrable_sq

theorem integrableOn_repGz_sq_el (C : Cap m) (u : H1P C.body) :
    IntegrableOn (fun p => ‖repGz_el C u p‖ ^ 2) C.body volume :=
  ((memL2_repGz_el C u).norm).integrable_sq

theorem integrable_indicator_repGx_sq_el (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator fun p => repGx C u p ^ 2) volume :=
  (integrableOn_repGx_sq_el C u).integrable_indicator (measurableSet_body' C)

theorem integrable_indicator_repFun_sq_el (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator fun p => repFun C u p ^ 2) volume :=
  (integrableOn_repFun_sq_el C u).integrable_indicator (measurableSet_body' C)

theorem integrable_indicator_repGz_sq_el (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator fun p => ‖repGz_el C u p‖ ^ 2) volume :=
  (integrableOn_repGz_sq_el C u).integrable_indicator (measurableSet_body' C)

/-- The **axial energy** of the slice through `z`. -/
def axEnergy_el (C : Cap m) (u : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ s in Ioo (-C.K) (exitTime C z), repGx C u (s, z) ^ 2

/-- The **axial mass** of the slice through `z`. -/
def axMass_el (C : Cap m) (u : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ s in Ioo (-C.K) (exitTime C z), repFun C u (s, z) ^ 2

theorem axEnergy_nonneg_el (C : Cap m) (u : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) :
    0 ≤ axEnergy_el C u z :=
  setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _

theorem axMass_nonneg_el (C : Cap m) (u : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) :
    0 ≤ axMass_el C u z :=
  setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _

theorem integrable_axEnergy_el (C : Cap m) (u : H1P C.body) :
    Integrable (axEnergy_el C u) volume :=
  integrable_slice_integral C (integrable_indicator_repGx_sq_el C u)

theorem integrable_axMass_el (C : Cap m) (u : H1P C.body) :
    Integrable (axMass_el C u) volume :=
  integrable_slice_integral C (integrable_indicator_repFun_sq_el C u)

theorem integral_axEnergy_el (C : Cap m) (u : H1P C.body) :
    (∫ z, axEnergy_el C u z) = ∫ p in C.body, repGx C u p ^ 2 :=
  (integral_body_eq_integral_slices C (integrable_indicator_repGx_sq_el C u)).symm

theorem integral_axMass_el (C : Cap m) (u : H1P C.body) :
    (∫ z, axMass_el C u z) = ∫ p in C.body, repFun C u p ^ 2 :=
  (integral_body_eq_integral_slices C (integrable_indicator_repFun_sq_el C u)).symm

/-- The **transverse energy** of the level `σ`. -/
def trEnergy_el (C : Cap m) (u : H1P C.body) (σ : ℝ) : ℝ :=
  ∫ z, (C.body.indicator fun p => ‖repGz_el C u p‖ ^ 2) (σ, z)

theorem integrable_trEnergy_el (C : Cap m) (u : H1P C.body) :
    Integrable (trEnergy_el C u) volume := by
  have h := integrable_indicator_repGz_sq_el C u
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

theorem integral_trEnergy_el (C : Cap m) (u : H1P C.body) :
    (∫ σ, trEnergy_el C u σ) = ∫ p in C.body, ‖repGz_el C u p‖ ^ 2 := by
  have h := integrable_indicator_repGz_sq_el C u
  rw [← integral_indicator (measurableSet_body' C), Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at h
  exact (integral_prod _ h).symm

theorem trEnergy_nonneg_el (C : Cap m) (u : H1P C.body) (σ : ℝ) : 0 ≤ trEnergy_el C u σ :=
  integral_nonneg fun z => Set.indicator_nonneg (fun p _ => by positivity) _

/-- The **transverse mass** of the level `σ`. -/
def trMass_el (C : Cap m) (u : H1P C.body) (σ : ℝ) : ℝ :=
  ∫ z, (C.body.indicator fun p => repFun C u p ^ 2) (σ, z)

theorem integrable_trMass_el (C : Cap m) (u : H1P C.body) :
    Integrable (trMass_el C u) volume := by
  have h := integrable_indicator_repFun_sq_el C u
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

theorem integral_trMass_el (C : Cap m) (u : H1P C.body) :
    (∫ σ, trMass_el C u σ) = ∫ p in C.body, repFun C u p ^ 2 := by
  have h := integrable_indicator_repFun_sq_el C u
  rw [← integral_indicator (measurableSet_body' C), Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at h
  exact (integral_prod _ h).symm

theorem trMass_nonneg_el (C : Cap m) (u : H1P C.body) (σ : ℝ) : 0 ≤ trMass_el C u σ :=
  integral_nonneg fun z => Set.indicator_nonneg (fun p _ => by positivity) _

/-! ## 5. Elementary one-dimensional estimates -/

theorem integral_ball_ept_el {ρ : ℝ} (hρ : 0 ≤ ρ) (F : EuclideanSpace ℝ (Fin 1) → ℝ) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) ρ, F z) = ∫ y in Ioo (-ρ) ρ, F (ept y) := by
  rw [integral_ball_one hρ F, intervalIntegral_eq_setIntegral_Ioo (by linarith : -ρ ≤ ρ)]

/-- **Cauchy–Schwarz on an arbitrary subinterval.** -/
theorem sq_intervalIntegral_sub_le_el {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b) volume)
    (hg2 : IntegrableOn (fun t => g t ^ 2) (Ioo a b) volume) :
    (∫ t in x..y, g t) ^ 2 ≤ (b - a) * ∫ t in Ioo a b, g t ^ 2 := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hgI : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hg
  have hg2I : IntervalIntegrable (fun t => g t ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hg2
  have heq : (∫ t in a..b, g t ^ 2) = ∫ t in Ioo a b, g t ^ 2 :=
    intervalIntegral_eq_setIntegral_Ioo hab
  have key : ∀ x' y' : ℝ, x' ∈ Icc a b → y' ∈ Icc a b → x' ≤ y' →
      (∫ t in x'..y', g t) ^ 2 ≤ (b - a) * ∫ t in Ioo a b, g t ^ 2 := by
    intro x' y' hx' hy' hxy
    have hsub : uIcc x' y' ⊆ uIcc a b := by
      rw [uIcc_of_le hxy, uIcc_of_le hab]
      exact Icc_subset_Icc hx'.1 hy'.2
    have hgs : IntervalIntegrable g volume x' y' := hgI.mono_set hsub
    have hg2s : IntervalIntegrable (fun t => g t ^ 2) volume x' y' := hg2I.mono_set hsub
    have habs : |∫ t in x'..y', g t| ≤ ∫ t in x'..y', |g t| :=
      intervalIntegral.abs_integral_le_integral_abs hxy
    have habs0 : 0 ≤ ∫ t in x'..y', |g t| :=
      intervalIntegral.integral_nonneg hxy fun t _ => abs_nonneg _
    have hcs : (∫ t in x'..y', |g t|) ^ 2 ≤ (y' - x') * ∫ t in x'..y', g t ^ 2 :=
      RobinCaps.Transverse.abs_integral_sq_le_on hxy g hgs hg2s
    have hmono : (∫ t in x'..y', g t ^ 2) ≤ ∫ t in a..b, g t ^ 2 :=
      intervalIntegral.integral_mono_interval hx'.1 hxy hy'.2
        (ae_of_all _ fun t => sq_nonneg _) hg2I
    have hs0 : 0 ≤ ∫ t in x'..y', g t ^ 2 :=
      intervalIntegral.integral_nonneg hxy fun t _ => sq_nonneg _
    have hsq : (∫ t in x'..y', g t) ^ 2 ≤ (∫ t in x'..y', |g t|) ^ 2 := by
      nlinarith [sq_abs (∫ t in x'..y', g t), abs_nonneg (∫ t in x'..y', g t)]
    have hfin : (y' - x') * (∫ t in x'..y', g t ^ 2) ≤ (b - a) * ∫ t in a..b, g t ^ 2 :=
      mul_le_mul (by linarith [hx'.1, hy'.2]) hmono hs0 (by linarith)
    rw [← heq]
    linarith
  rcases le_total x y with hxy | hxy
  · exact key x y hx hy hxy
  · have h := key y x hy hx hxy
    rw [intervalIntegral.integral_symm, neg_pow] at h
    simpa using h

/-! ## 6. The transverse deviation bound -/

theorem ae_ae_transverse_repFun_el (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (σ, z) ∈ C.body → repFun C u (σ, z) = u.toFun (σ, z) := by
  have h : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → repFun C u p = u.toFun p := by
    have h0 : u.toFun =ᵐ[volume.restrict C.body] repFun C u :=
      u.memL2.aestronglyMeasurable.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at h0
    filter_upwards [h0] with p hp hpb using (hp hpb).symm
  rw [Measure.volume_eq_prod] at h
  exact Measure.ae_ae_of_ae_prod h

theorem ae_ae_transverse_repGz_el (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (σ, z) ∈ C.body → repGz_el C u (σ, z) = u.gz (σ, z) := by
  have h : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → repGz_el C u p = u.gz p := by
    have h0 := repGz_ae_eq_el C u
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at h0
    filter_upwards [h0] with p hp hpb using (hp hpb).symm
  rw [Measure.volume_eq_prod] at h
  exact Measure.ae_ae_of_ae_prod h

/-- The transverse slice of the body-indicator is the ball-indicator of the slice. -/
theorem indicator_body_transverse_el (C : Cap m) (f : CapSpace m → ℝ) {σ : ℝ}
    (hσ : σ ∈ Ioo (-C.K) 0) (z : EuclideanSpace ℝ (Fin m)) :
    C.body.indicator f (σ, z)
      = (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ)).indicator (fun z => f (σ, z)) z := by
  by_cases h : ‖z‖ < C.θ σ
  · rw [Set.indicator_of_mem (show ((σ, z) : CapSpace m) ∈ C.body from ⟨hσ.1, hσ.2, h⟩),
      Set.indicator_of_mem (mem_ball_zero_iff.2 h)]
  · rw [Set.indicator_of_notMem (fun hb => h hb.2.2),
      Set.indicator_of_notMem (fun hb => h (mem_ball_zero_iff.1 hb))]

/-- Almost every transverse slice of a function integrable on the body is integrable on the
transverse section, read through `ept`. -/
theorem ae_transverse_integrableOn_el (C : Cap 1) {f : CapSpace 1 → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      IntegrableOn (fun y => f (σ, ept y)) (Ioo (-(C.θ σ)) (C.θ σ)) volume := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hf
  filter_upwards [hf'.prod_right_ae] with σ hσ hσI
  refine (integrableOn_comp_ept_el (fun z => f (σ, z))).2 ?_
  refine (integrable_indicator_iff measurableSet_ball).1 ?_
  exact hσ.congr (Eventually.of_forall fun z => indicator_body_transverse_el C f hσI z)

/-- The transverse energy of a level, read through `ept`. -/
theorem ae_trEnergy_eq_el (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      trEnergy_el C u σ = ∫ y in Ioo (-(C.θ σ)) (C.θ σ), (u.gz (σ, ept y) 0) ^ 2 := by
  filter_upwards [ae_ae_transverse_repGz_el C u] with σ hrg hσI
  have hrg' : ∀ᵐ y ∂(volume : Measure ℝ),
      ((σ, ept y) : CapSpace 1) ∈ C.body → repGz_el C u (σ, ept y) = u.gz (σ, ept y) :=
    measurePreserving_ept.quasiMeasurePreserving.ae hrg
  have hmem : ∀ y ∈ Ioo (-(C.θ σ)) (C.θ σ), ((σ, ept y) : CapSpace 1) ∈ C.body := by
    intro y hy
    exact ⟨hσI.1, hσI.2, by rw [ept_norm]; exact abs_lt.2 ⟨hy.1, hy.2⟩⟩
  have hstep1 : trEnergy_el C u σ
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ σ), ‖repGz_el C u (σ, z)‖ ^ 2 := by
    rw [trEnergy_el]
    rw [show (fun z => C.body.indicator (fun p => ‖repGz_el C u p‖ ^ 2) (σ, z))
        = fun z => (ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ σ)).indicator
          (fun z => ‖repGz_el C u (σ, z)‖ ^ 2) z from
      funext fun z => indicator_body_transverse_el C _ hσI z]
    rw [integral_indicator measurableSet_ball]
  rw [hstep1, integral_ball_ept_el (C.θ_pos σ hσI).le]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [hrg'] with y hy hymem
  rw [hy (hmem y hymem), ← norm_sq_one_dim]

/-- **The transverse deviation bound.** -/
theorem ae_transverse_bound_el (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)),
      ∀ᵐ y ∂(volume.restrict (Ioo (-(C.θ σ)) (C.θ σ))),
        ∀ᵐ y' ∂(volume.restrict (Ioo (-(C.θ σ)) (C.θ σ))),
          (repFun C u (σ, ept y) - repFun C u (σ, ept y')) ^ 2 ≤ 2 * trEnergy_el C u σ := by
  have hu_ind : Integrable (C.body.indicator u.toFun) volume :=
    (integrableOn_body_of_memL2 C u.memL2).integrable_indicator (measurableSet_body' C)
  have hgz_ind : Integrable (C.body.indicator fun p => u.gz p 0) volume := by
    have h : IntegrableOn (fun p : CapSpace 1 => u.gz p 0) C.body volume :=
      (memLp_two_compP u.gz_memL2 0).integrable one_le_two
    exact h.integrable_indicator (measurableSet_body' C)
  have hgz2_ind : Integrable (C.body.indicator fun p => (u.gz p 0) ^ 2) volume := by
    have h : IntegrableOn (fun p : CapSpace 1 => (u.gz p 0) ^ 2) C.body volume :=
      (memLp_two_compP u.gz_memL2 0).integrable_sq
    exact h.integrable_indicator (measurableSet_body' C)
  filter_upwards [sliceAC_transverse_cap_el C u,
    ae_restrict_of_ae (ae_ae_transverse_repFun_el C u),
    ae_restrict_of_ae (ae_transverse_integrableOn_el C hu_ind),
    ae_restrict_of_ae (ae_transverse_integrableOn_el C hgz_ind),
    ae_restrict_of_ae (ae_transverse_integrableOn_el C hgz2_ind),
    ae_restrict_of_ae (ae_trEnergy_eq_el C u),
    ae_restrict_mem measurableSet_Ioo] with σ hw hrf hiu hig hig2 htr hσI
  have hθ : 0 < C.θ σ := C.θ_pos σ hσI
  have hθ1 : C.θ σ ≤ 1 := C.θ_le_one σ hσI
  have hab : -(C.θ σ) < C.θ σ := by linarith
  have hmem : ∀ y ∈ Ioo (-(C.θ σ)) (C.θ σ), ((σ, ept y) : CapSpace 1) ∈ C.body := by
    intro y hy
    exact ⟨hσI.1, hσI.2, by rw [ept_norm]; exact abs_lt.2 ⟨hy.1, hy.2⟩⟩
  have hrf' : ∀ᵐ y ∂(volume : Measure ℝ),
      ((σ, ept y) : CapSpace 1) ∈ C.body → repFun C u (σ, ept y) = u.toFun (σ, ept y) :=
    measurePreserving_ept.quasiMeasurePreserving.ae hrf
  obtain ⟨B, hB⟩ := ae_eq_const_add_integral hab (hiu hσI) (hig hσI) hw
  simp only [show (-(C.θ σ) + C.θ σ) / 2 = (0 : ℝ) by ring] at hB
  have hgoodE : ∫ r in Ioo (-(C.θ σ)) (C.θ σ), (u.gz (σ, ept r) 0) ^ 2
      = trEnergy_el C u σ := (htr hσI).symm
  filter_upwards [hB, ae_restrict_of_ae hrf', ae_restrict_mem measurableSet_Ioo]
    with y hy hyr hymem
  filter_upwards [hB, ae_restrict_of_ae hrf', ae_restrict_mem measurableSet_Ioo]
    with y' hy' hyr' hymem'
  have e1 : repFun C u (σ, ept y) - repFun C u (σ, ept y')
      = ∫ r in y'..y, u.gz (σ, ept r) 0 := by
    rw [hyr (hmem y hymem), hyr' (hmem y' hymem'), hy, hy']
    have hsplit : (∫ r in (0 : ℝ)..y, u.gz (σ, ept r) 0)
        - ∫ r in (0 : ℝ)..y', u.gz (σ, ept r) 0 = ∫ r in y'..y, u.gz (σ, ept r) 0 := by
      have hI : IntervalIntegrable (fun r => u.gz (σ, ept r) 0) volume (-(C.θ σ)) (C.θ σ) :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hig hσI)
      have hsub : ∀ x ∈ Icc (-(C.θ σ)) (C.θ σ), ∀ w ∈ Icc (-(C.θ σ)) (C.θ σ),
          IntervalIntegrable (fun r => u.gz (σ, ept r) 0) volume x w := by
        intro x hx w hw
        refine hI.mono_set (uIcc_subset_uIcc ?_ ?_) <;> rw [uIcc_of_le hab.le]
        · exact hx
        · exact hw
      have h0 : (0 : ℝ) ∈ Icc (-(C.θ σ)) (C.θ σ) := ⟨by linarith, by linarith⟩
      have hy0 : y ∈ Icc (-(C.θ σ)) (C.θ σ) := Ioo_subset_Icc_self hymem
      have hy0' : y' ∈ Icc (-(C.θ σ)) (C.θ σ) := Ioo_subset_Icc_self hymem'
      have := intervalIntegral.integral_add_adjacent_intervals
        (hsub y' hy0' 0 h0) (hsub 0 h0 y hy0)
      rw [← this, intervalIntegral.integral_symm y' 0]
      ring
    linarith [hsplit]
  rw [e1]
  have hbnd := sq_intervalIntegral_sub_le_el (Ioo_subset_Icc_self hymem')
    (Ioo_subset_Icc_self hymem) (hig hσI) (hig2 hσI)
  rw [hgoodE] at hbnd
  have h2 : (C.θ σ - -(C.θ σ)) * trEnergy_el C u σ ≤ 2 * trEnergy_el C u σ :=
    mul_le_mul_of_nonneg_right (by linarith) (trEnergy_nonneg_el C u σ)
  linarith

/-! ## 7. The axial majorant `g` -/

/-- The inner (transverse) integral of a body-indicator, read through `ept`. -/
theorem inner_slice_eq_el (C : Cap 1) (F : CapSpace 1 → ℝ) {σ : ℝ} (hσ : σ ∈ Ioo (-C.K) 0) :
    (∫ z, (C.body.indicator F) (σ, z)) = ∫ y in Ioo (-(C.θ σ)) (C.θ σ), F (σ, ept y) := by
  rw [show (fun z => C.body.indicator F (σ, z))
      = fun z => (ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ σ)).indicator
        (fun z => F (σ, z)) z from funext (indicator_body_transverse_el C F hσ),
    integral_indicator measurableSet_ball, integral_ball_ept_el (C.θ_pos σ hσ).le]

/-- **The axial majorant.**  On the far-left region of the half-disk the square of `u` at a point
is bounded by this function of the axial coordinate alone. -/
def gfun_el (C : Cap 1) (u : H1P C.body) (σ : ℝ) : ℝ :=
  Real.sqrt 2 * trMass_el C u σ + 4 * trEnergy_el C u σ

theorem gfun_nonneg_el (C : Cap 1) (u : H1P C.body) (σ : ℝ) : 0 ≤ gfun_el C u σ := by
  have h1 := trMass_nonneg_el C u σ
  have h2 := trEnergy_nonneg_el C u σ
  have h3 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [gfun_el]; positivity

theorem stronglyMeasurable_trMass_el (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (trMass_el C u) :=
  (((stronglyMeasurable_repFun C u).pow 2).indicator (measurableSet_body' C)).integral_prod_right'

theorem stronglyMeasurable_trEnergy_el (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (trEnergy_el C u) :=
  ((((stronglyMeasurable_repGz_el C u).norm).pow 2).indicator
    (measurableSet_body' C)).integral_prod_right'

theorem measurable_gfun_el (C : Cap 1) (u : H1P C.body) : Measurable (gfun_el C u) := by
  refine Measurable.add ?_ ?_
  · exact (stronglyMeasurable_trMass_el C u).measurable.const_mul _
  · exact (stronglyMeasurable_trEnergy_el C u).measurable.const_mul _

theorem integrable_gfun_el (C : Cap 1) (u : H1P C.body) : Integrable (gfun_el C u) volume :=
  ((integrable_trMass_el C u).const_mul _).add ((integrable_trEnergy_el C u).const_mul _)

/-- `∫ g` is controlled by the mass and the transverse energy of `u`. -/
theorem integral_gfun_el (C : Cap 1) (u : H1P C.body) :
    (∫ σ, gfun_el C u σ)
      = Real.sqrt 2 * (∫ p in C.body, repFun C u p ^ 2)
        + 4 * ∫ p in C.body, ‖repGz_el C u p‖ ^ 2 := by
  rw [show (fun σ => gfun_el C u σ)
      = fun σ => Real.sqrt 2 * trMass_el C u σ + 4 * trEnergy_el C u σ from rfl,
    integral_add ((integrable_trMass_el C u).const_mul _)
      ((integrable_trEnergy_el C u).const_mul _),
    integral_const_mul, integral_const_mul, integral_trMass_el, integral_trEnergy_el]

/-- **The transverse bound, levelwise.**  On a level whose section is wider than `rad_el`, the
square of `u` at almost every point of the section is at most `g`. -/
theorem ae_level_sq_le_gfun_el (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 → rad_el < C.θ σ →
      ∀ᵐ y ∂(volume : Measure ℝ), |y| < C.θ σ →
        repFun C u (σ, ept y) ^ 2 ≤ gfun_el C u σ := by
  have hr0 : 0 < rad_el := rad_pos_el
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (ae_transverse_bound_el C u),
    ae_transverse_integrableOn_el C (integrable_indicator_repFun_sq_el C u)]
    with σ hbnd hint hσI hrad
  have hθ : 0 < C.θ σ := C.θ_pos σ hσI
  have hsub : Ioo (-rad_el) rad_el ⊆ Ioo (-(C.θ σ)) (C.θ σ) :=
    Ioo_subset_Ioo (by linarith) hrad.le
  have hbig : IntegrableOn (fun y => repFun C u (σ, ept y) ^ 2)
      (Ioo (-(C.θ σ)) (C.θ σ)) volume := hint hσI
  have hsmall : IntegrableOn (fun y => repFun C u (σ, ept y) ^ 2)
      (Ioo (-rad_el) rad_el) volume := hbig.mono_set hsub
  have htrM : trMass_el C u σ = ∫ y in Ioo (-(C.θ σ)) (C.θ σ), repFun C u (σ, ept y) ^ 2 :=
    inner_slice_eq_el C _ hσI
  have hcmp : (∫ y in Ioo (-rad_el) rad_el, repFun C u (σ, ept y) ^ 2) ≤ trMass_el C u σ := by
    rw [htrM]
    exact setIntegral_mono_set hbig (Eventually.of_forall fun y => sq_nonneg _)
      (HasSubset.Subset.eventuallyLE hsub)
  have hvol : (volume.real (Ioo (-rad_el) rad_el)) = 2 * rad_el := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]; ring
  have hbnd' := hbnd hσI
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hbnd'] with y hy hyabs
  have hymem : y ∈ Ioo (-(C.θ σ)) (C.θ σ) := abs_lt.1 hyabs
  have hy' : ∀ᵐ y' ∂(volume.restrict (Ioo (-rad_el) rad_el)),
      (repFun C u (σ, ept y) - repFun C u (σ, ept y')) ^ 2 ≤ 2 * trEnergy_el C u σ :=
    ae_mono (Measure.restrict_mono hsub le_rfl) (hy hymem)
  -- the pointwise chain bound on the central segment
  have hkey : ∀ᵐ y' ∂(volume.restrict (Ioo (-rad_el) rad_el)),
      repFun C u (σ, ept y) ^ 2
        ≤ 2 * repFun C u (σ, ept y') ^ 2 + 4 * trEnergy_el C u σ := by
    filter_upwards [hy'] with y' h1
    nlinarith [h1, sq_nonneg (repFun C u (σ, ept y) - 2 * repFun C u (σ, ept y'))]
  have hconst : IntegrableOn (fun _ : ℝ => repFun C u (σ, ept y) ^ 2)
      (Ioo (-rad_el) rad_el) volume := integrableOn_const measure_Ioo_lt_top.ne
  have hmaj : IntegrableOn
      (fun y' => 2 * repFun C u (σ, ept y') ^ 2 + 4 * trEnergy_el C u σ)
      (Ioo (-rad_el) rad_el) volume :=
    (hsmall.const_mul 2).add (integrableOn_const measure_Ioo_lt_top.ne)
  have hmono := integral_mono_ae hconst hmaj hkey
  rw [setIntegral_const, smul_eq_mul, hvol,
    integral_add (hsmall.const_mul 2) (integrableOn_const measure_Ioo_lt_top.ne),
    integral_const_mul, setIntegral_const, smul_eq_mul, hvol] at hmono
  -- divide by the length of the central segment
  have hfin : 2 * rad_el * repFun C u (σ, ept y) ^ 2
      ≤ 2 * trMass_el C u σ + 4 * trEnergy_el C u σ * (2 * rad_el) := by
    have h2 : 2 * (∫ y' in Ioo (-rad_el) rad_el, repFun C u (σ, ept y') ^ 2)
        ≤ 2 * trMass_el C u σ := by linarith
    linarith
  have hgoal : repFun C u (σ, ept y) ^ 2 ≤ (1 / rad_el) * trMass_el C u σ
      + 4 * trEnergy_el C u σ := by
    rw [← sub_nonneg]
    have hkey2 : (1 / rad_el) * trMass_el C u σ + 4 * trEnergy_el C u σ
        - repFun C u (σ, ept y) ^ 2
        = (1 / (2 * rad_el)) * (2 * trMass_el C u σ
            + 4 * trEnergy_el C u σ * (2 * rad_el) - 2 * rad_el * repFun C u (σ, ept y) ^ 2) := by
      field_simp
    rw [hkey2]
    exact mul_nonneg (by positivity) (by linarith)
  rw [gfun_el, ← inv_rad_el]
  exact hgoal

/-! ## 8. The axial majorant, read along the axial slices -/

/-- Transport of an a.e. statement from the line to the one-dimensional transverse space. -/
theorem ae_of_ae_comp_ept_el {P : EuclideanSpace ℝ (Fin 1) → Prop}
    (h : ∀ᵐ y ∂(volume : Measure ℝ), P (ept y)) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))), P z := by
  have h0 : MeasurePreserving (⇑eptEquiv) (volume : Measure ℝ)
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) := measurePreserving_ept
  have hs := h0.symm eptEquiv
  filter_upwards [hs.quasiMeasurePreserving.ae h] with z hz
  have hid : ept (eptEquiv.symm z) = z := eptEquiv.apply_symm_apply z
  rwa [hid] at hz

/-- **The transverse bound as a two-dimensional almost-everywhere statement.** -/
theorem ae_body_sq_le_gfun_el (u : H1P (hemisphere 1).body) :
    ∀ᵐ p ∂(volume : Measure (CapSpace 1)), p ∈ (hemisphere 1).body → p.1 + 1 < rad_el →
      repFun (hemisphere 1) u p ^ 2 ≤ gfun_el (hemisphere 1) u p.1 := by
  have hmeas : MeasurableSet {p : CapSpace 1 |
      p ∈ (hemisphere 1).body → p.1 + 1 < rad_el →
        repFun (hemisphere 1) u p ^ 2 ≤ gfun_el (hemisphere 1) u p.1} := by
    have h1 : MeasurableSet {p : CapSpace 1 |
        repFun (hemisphere 1) u p ^ 2 ≤ gfun_el (hemisphere 1) u p.1} :=
      measurableSet_le ((stronglyMeasurable_repFun (hemisphere 1) u).measurable.pow_const 2)
        ((measurable_gfun_el (hemisphere 1) u).comp measurable_fst)
    have h2 : MeasurableSet {p : CapSpace 1 | p.1 + 1 < rad_el} :=
      measurableSet_lt (measurable_fst.add_const 1) measurable_const
    have h3 : {p : CapSpace 1 | p ∈ (hemisphere 1).body → p.1 + 1 < rad_el →
        repFun (hemisphere 1) u p ^ 2 ≤ gfun_el (hemisphere 1) u p.1}
        = ((hemisphere 1).body)ᶜ ∪ (({p : CapSpace 1 | p.1 + 1 < rad_el})ᶜ ∪
            {p : CapSpace 1 | repFun (hemisphere 1) u p ^ 2 ≤ gfun_el (hemisphere 1) u p.1}) := by
      ext p
      by_cases hp : p ∈ (hemisphere 1).body <;> by_cases hq : p.1 + 1 < rad_el <;>
        simp [hp, hq, Set.mem_setOf_eq]
    rw [h3]
    exact ((measurableSet_body' (hemisphere 1)).compl).union (h2.compl.union h1)
  rw [Measure.volume_eq_prod]
  refine (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 1)))) hmeas).2 ?_
  filter_upwards [ae_level_sq_le_gfun_el (hemisphere 1) u] with σ hσ
  by_cases hσ1 : -1 < σ
  · by_cases hσ2 : σ + 1 < rad_el
    · have hlt1 : rad_el < 1 := rad_lt_one_el
      have hσI : σ ∈ Ioo (-(hemisphere 1).K) 0 := by
        rw [hemi_K_el]
        exact ⟨hσ1, by linarith⟩
      have hrad : rad_el < (hemisphere 1).θ σ := rad_lt_theta_el hσ1 hσ2
      have hy := hσ hσI hrad
      refine ae_of_ae_comp_ept_el (P := fun z => ((σ, z) : CapSpace 1) ∈ (hemisphere 1).body →
        σ + 1 < rad_el → repFun (hemisphere 1) u (σ, z) ^ 2 ≤ gfun_el (hemisphere 1) u σ) ?_
      filter_upwards [hy] with y hy' hmem _
      refine hy' ?_
      have hn : ‖ept y‖ < (hemisphere 1).θ σ := hmem.2.2
      rwa [ept_norm] at hn
    · filter_upwards with z _ hcon
      exact absurd hcon hσ2
  · filter_upwards with z hmem
    have hb : -(hemisphere 1).K < σ := hmem.1
    rw [hemi_K_el] at hb
    exact absurd hb hσ1

/-- **The transverse bound, read along the axial slices.** -/
theorem ae_slice_sq_le_gfun_el (u : H1P (hemisphere 1).body) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))), ∀ᵐ s ∂(volume : Measure ℝ),
      ((s, z) : CapSpace 1) ∈ (hemisphere 1).body → s + 1 < rad_el →
        repFun (hemisphere 1) u (s, z) ^ 2 ≤ gfun_el (hemisphere 1) u s :=
  ae_ae_axial (ae_body_sq_le_gfun_el u)

/-- **The axial mass of a short slice is uniformly bounded.** -/
theorem ae_axMass_le_el (u : H1P (hemisphere 1).body) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))),
      exitTime (hemisphere 1) z + 1 ≤ rad_el →
        axMass_el (hemisphere 1) u z ≤ ∫ σ, gfun_el (hemisphere 1) u σ := by
  have hg := integrable_gfun_el (hemisphere 1) u
  filter_upwards [ae_slice_sq_le_gfun_el u,
    ae_integrableOn_cap_slice (hemisphere 1) (integrableOn_repFun_sq_el (hemisphere 1) u)]
    with z h1 h2 hshort
  have hgI : IntegrableOn (gfun_el (hemisphere 1) u)
      (Ioo (-(hemisphere 1).K) (exitTime (hemisphere 1) z)) volume := hg.integrableOn
  have hptw : ∀ᵐ s ∂(volume.restrict
      (Ioo (-(hemisphere 1).K) (exitTime (hemisphere 1) z))),
      repFun (hemisphere 1) u (s, z) ^ 2 ≤ gfun_el (hemisphere 1) u s := by
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    have hmem : ((s, z) : CapSpace 1) ∈ (hemisphere 1).body := by
      have hmm : s ∈ axialSlice (hemisphere 1) z := by rw [axialSlice_eq]; exact hsmem
      exact hmm
    refine hs hmem ?_
    have h4 : s < exitTime (hemisphere 1) z := hsmem.2
    linarith
  have hstep : axMass_el (hemisphere 1) u z
      ≤ ∫ s in Ioo (-(hemisphere 1).K) (exitTime (hemisphere 1) z), gfun_el (hemisphere 1) u s :=
    integral_mono_ae h2 hgI hptw
  have hlast : (∫ s in Ioo (-(hemisphere 1).K) (exitTime (hemisphere 1) z),
      gfun_el (hemisphere 1) u s) ≤ ∫ σ, gfun_el (hemisphere 1) u σ :=
    setIntegral_le_integral hg
      (Eventually.of_forall fun σ => gfun_nonneg_el (hemisphere 1) u σ)
  linarith

/-! ## 9. The one-dimensional trace bound on an axial slice -/

/-- **The entrance value is controlled by the axial slice data.**  This is the one-dimensional
trace inequality `RobinCaps.Sobolev.endpoint_zero_sq_le` applied to the absolutely continuous
representative of the axial slice. -/
theorem ae_entranceVal_sq_le_el (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      entranceVal C u z ^ 2
        ≤ (2 / (exitTime C z + C.K)) * axMass_el C u z
          + (2 * (exitTime C z + C.K)) * axEnergy_el C u z := by
  filter_upwards [exists_h1_axialSlice C u,
    ae_restrict_of_ae (ae_slice_repFun C u), ae_restrict_of_ae (ae_slice_repGx C u),
    ae_restrict_mem measurableSet_ball] with z hex hrf hrg hzb
  obtain ⟨w, hw0, hwf, hwd⟩ := hex
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  have hℓ : 0 < exitTime C z + C.K := by linarith
  have hmemslice : ∀ s : ℝ, s ∈ Ioo (-C.K) (exitTime C z) → ((s, z) : CapSpace m) ∈ C.body := by
    intro s hs
    have hmm : s ∈ axialSlice C z := by rw [axialSlice_eq]; exact hs
    exact hmm
  -- the mass of the slice representative
  have hmass : Sobolev.mass (exitTime C z + C.K) w = axMass_el C u z := by
    rw [Sobolev.mass, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le]
    have h1 : (fun x => w.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo (0:ℝ) (exitTime C z + C.K))]
          fun x => u.toFun (x - C.K, z) ^ 2 := by
      filter_upwards [hwf] with x hx
      rw [hx]
    rw [integral_congr_ae h1, ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le,
      intervalIntegral.integral_comp_sub_right (fun s => u.toFun (s, z) ^ 2) C.K,
      show (0:ℝ) - C.K = -C.K by ring, show exitTime C z + C.K - C.K = exitTime C z by ring,
      Sobolev.intervalIntegral_eq_setIntegral_Ioo hKe.le, axMass_el]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrf] with s hs hsmem
    rw [hs (hmemslice s hsmem)]
  -- the Dirichlet energy of the slice representative
  have hdir : Sobolev.dirichlet (exitTime C z + C.K) w = axEnergy_el C u z := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le]
    have h1 : (fun x => deriv w.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo (0:ℝ) (exitTime C z + C.K))]
          fun x => u.gx (x - C.K, z) ^ 2 := by
      filter_upwards [hwd] with x hx
      rw [hx]
    rw [integral_congr_ae h1, ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le,
      intervalIntegral.integral_comp_sub_right (fun s => u.gx (s, z) ^ 2) C.K,
      show (0:ℝ) - C.K = -C.K by ring, show exitTime C z + C.K - C.K = exitTime C z by ring,
      Sobolev.intervalIntegral_eq_setIntegral_Ioo hKe.le, axEnergy_el]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrg] with s hs hsmem
    rw [hs (hmemslice s hsmem)]
  have hkey := Sobolev.endpoint_zero_sq_le w hℓ
  rw [hw0, hmass, hdir] at hkey
  exact hkey

/-! ## 10. The majorant on the entrance disk -/

/-- The majorant of the squared entrance trace on the entrance disk. -/
def majFun_el (u : H1P (hemisphere 1).body) (z : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  2 * Real.sqrt 2 * axMass_el (hemisphere 1) u z + 2 * axEnergy_el (hemisphere 1) u z
    + (∫ σ, gfun_el (hemisphere 1) u σ) * wt_el z

theorem sqrt_one_sub_rad_sq_el : Real.sqrt (1 - rad_el ^ 2) = rad_el := by
  rw [rad_sq_el, show (1:ℝ) - 1 / 2 = rad_el ^ 2 by rw [rad_sq_el]; norm_num,
    Real.sqrt_sq rad_pos_el.le]

theorem two_div_le_el {ℓ : ℝ} (hℓ : rad_el ≤ ℓ) : 2 / ℓ ≤ 2 * Real.sqrt 2 := by
  have h0 : 0 < ℓ := lt_of_lt_of_le rad_pos_el hℓ
  rw [div_le_iff₀ h0]
  have h1 : 2 * Real.sqrt 2 * rad_el = 2 := by
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    rw [rad_el]
    field_simp
  nlinarith [Real.sqrt_nonneg 2]

/-- **The pointwise bound on the entrance disk.** -/
theorem ae_entranceVal_sq_le_maj_el (u : H1P (hemisphere 1).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) 1)),
      entranceVal (hemisphere 1) u z ^ 2 ≤ majFun_el u z := by
  have hGnn : 0 ≤ ∫ σ, gfun_el (hemisphere 1) u σ :=
    integral_nonneg fun σ => gfun_nonneg_el (hemisphere 1) u σ
  filter_upwards [ae_entranceVal_sq_le_el (hemisphere 1) u,
    ae_restrict_of_ae (ae_axMass_le_el u), ae_restrict_mem measurableSet_ball]
    with z h1 h2 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  have hℓ : exitTime (hemisphere 1) z + 1 = Real.sqrt (1 - ‖z‖ ^ 2) := exitTime_hemi_el hznorm
  have hℓpos : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_pos.2 hpos
  have hℓle : Real.sqrt (1 - ‖z‖ ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; nlinarith
  rw [hemi_K_el, hℓ] at h1
  rw [hℓ] at h2
  have hA0 : 0 ≤ axEnergy_el (hemisphere 1) u z := axEnergy_nonneg_el _ _ _
  have hM0 : 0 ≤ axMass_el (hemisphere 1) u z := axMass_nonneg_el _ _ _
  have hdir : 2 * Real.sqrt (1 - ‖z‖ ^ 2) * axEnergy_el (hemisphere 1) u z
      ≤ 2 * axEnergy_el (hemisphere 1) u z := by nlinarith
  rw [majFun_el]
  by_cases hcase : rad_el < ‖z‖
  · -- the outer region: the slice is short, so its mass is bounded by `∫ g`
    have hshort : Real.sqrt (1 - ‖z‖ ^ 2) ≤ rad_el := by
      have h3 : 1 - ‖z‖ ^ 2 ≤ rad_el ^ 2 := by nlinarith [rad_sq_el, rad_pos_el]
      have := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq rad_pos_el.le] at this
    have hmass := h2 hshort
    have hwt : wt_el z = 2 / Real.sqrt (1 - ‖z‖ ^ 2) := by rw [wt_el, if_pos hcase]
    have hstep : 2 / Real.sqrt (1 - ‖z‖ ^ 2) * axMass_el (hemisphere 1) u z
        ≤ (∫ σ, gfun_el (hemisphere 1) u σ) * wt_el z := by
      rw [hwt, mul_comm ((∫ σ, gfun_el (hemisphere 1) u σ)) _]
      refine mul_le_mul_of_nonneg_left hmass ?_
      positivity
    have hsq0 : 0 ≤ 2 * Real.sqrt 2 * axMass_el (hemisphere 1) u z := by
      have : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      positivity
    linarith
  · -- the central region: the slice is long, so the weight is bounded
    push_neg at hcase
    have hlong : rad_el ≤ Real.sqrt (1 - ‖z‖ ^ 2) := by
      have h3 : rad_el ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [rad_sq_el, rad_pos_el]
      have := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq rad_pos_el.le] at this
    have hwt : wt_el z = 0 := by rw [wt_el, if_neg (not_lt.2 hcase)]
    have hstep : 2 / Real.sqrt (1 - ‖z‖ ^ 2) * axMass_el (hemisphere 1) u z
        ≤ 2 * Real.sqrt 2 * axMass_el (hemisphere 1) u z :=
      mul_le_mul_of_nonneg_right (two_div_le_el hlong) hM0
    rw [hwt, mul_zero]
    linarith

theorem integrableOn_majFun_el (u : H1P (hemisphere 1).body) :
    IntegrableOn (majFun_el u) (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) volume := by
  refine Integrable.add (Integrable.add ?_ ?_) ?_
  · exact (integrable_axMass_el (hemisphere 1) u).integrableOn.const_mul _
  · exact (integrable_axEnergy_el (hemisphere 1) u).integrableOn.const_mul _
  · exact integrableOn_wt_el.const_mul _

/-! ## 11. The two identities relating the forms to the representatives -/

theorem massP_eq_rep_el (C : Cap m) (u : H1P C.body) :
    massP u = ∫ p in C.body, repFun C u p ^ 2 := by
  rw [massP]
  refine integral_congr_ae ?_
  filter_upwards [u.memL2.aestronglyMeasurable.ae_eq_mk] with p hp
  rw [hp]
  rfl

theorem dirichletP_eq_rep_el (C : Cap m) (u : H1P C.body) :
    dirichletP u = (∫ p in C.body, repGx C u p ^ 2)
      + ∫ p in C.body, ‖repGz_el C u p‖ ^ 2 := by
  have hae : ∀ᵐ p ∂(volume.restrict C.body),
      u.gx p ^ 2 + ‖u.gz p‖ ^ 2 = repGx C u p ^ 2 + ‖repGz_el C u p‖ ^ 2 := by
    filter_upwards [u.gx_memL2.aestronglyMeasurable.ae_eq_mk, repGz_ae_eq_el C u] with p h1 h2
    have e2 : repGz_el C u p = u.gz_memL2.aestronglyMeasurable.mk u.gz p := rfl
    have h2' : u.gz p = u.gz_memL2.aestronglyMeasurable.mk u.gz p := h2.trans e2
    rw [show repGx C u p = u.gx_memL2.aestronglyMeasurable.mk u.gx p from rfl, e2, ← h1, ← h2']
  rw [dirichletP, integral_congr_ae hae,
    integral_add (integrableOn_repGx_sq_el C u) (integrableOn_repGz_sq_el C u)]

/-! ## 12. The trace bound -/

theorem integral_majFun_le_el (u : H1P (hemisphere 1).body) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, majFun_el u z)
      ≤ 40 * (massP u + dirichletP u) := by
  set M : ℝ := ∫ p in (hemisphere 1).body, repFun (hemisphere 1) u p ^ 2 with hM
  set A : ℝ := ∫ p in (hemisphere 1).body, repGx (hemisphere 1) u p ^ 2 with hA
  set B : ℝ := ∫ p in (hemisphere 1).body, ‖repGz_el (hemisphere 1) u p‖ ^ 2 with hB
  have hM0 : 0 ≤ M := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hA0 : 0 ≤ A := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_body' _) fun p _ => by positivity
  have hmass : massP u = M := massP_eq_rep_el _ u
  have hdir : dirichletP u = A + B := dirichletP_eq_rep_el _ u
  -- the three pieces
  have hax : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, axMass_el (hemisphere 1) u z)
      ≤ M := by
    rw [hM, ← integral_axMass_el (hemisphere 1) u]
    exact setIntegral_le_integral (integrable_axMass_el _ u)
      (Eventually.of_forall fun z => axMass_nonneg_el _ _ _)
  have hae : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, axEnergy_el (hemisphere 1) u z)
      ≤ A := by
    rw [hA, ← integral_axEnergy_el (hemisphere 1) u]
    exact setIntegral_le_integral (integrable_axEnergy_el _ u)
      (Eventually.of_forall fun z => axEnergy_nonneg_el _ _ _)
  have hG : (∫ σ, gfun_el (hemisphere 1) u σ) = Real.sqrt 2 * M + 4 * B := by
    rw [integral_gfun_el, hM, hB]
  have hGnn : 0 ≤ ∫ σ, gfun_el (hemisphere 1) u σ :=
    integral_nonneg fun σ => gfun_nonneg_el (hemisphere 1) u σ
  have hI1 : IntegrableOn (fun z => 2 * Real.sqrt 2 * axMass_el (hemisphere 1) u z)
      (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) volume :=
    (integrable_axMass_el (hemisphere 1) u).integrableOn.const_mul (2 * Real.sqrt 2)
  have hI2 : IntegrableOn (fun z => 2 * axEnergy_el (hemisphere 1) u z)
      (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) volume :=
    (integrable_axEnergy_el (hemisphere 1) u).integrableOn.const_mul 2
  have hI3 : IntegrableOn (fun z => (∫ σ, gfun_el (hemisphere 1) u σ) * wt_el z)
      (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) volume :=
    integrableOn_wt_el.const_mul (∫ σ, gfun_el (hemisphere 1) u σ)
  have hI12 : IntegrableOn (fun z => 2 * Real.sqrt 2 * axMass_el (hemisphere 1) u z
      + 2 * axEnergy_el (hemisphere 1) u z)
      (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) volume := hI1.add hI2
  have hsplit : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, majFun_el u z)
      = 2 * Real.sqrt 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
            axMass_el (hemisphere 1) u z)
        + 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, axEnergy_el (hemisphere 1) u z)
        + (∫ σ, gfun_el (hemisphere 1) u σ)
            * ∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, wt_el z := by
    simp only [majFun_el]
    rw [integral_add hI12 hI3, integral_add hI1 hI2,
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hwt := integral_wt_le_el
  have hs2 : Real.sqrt 2 < 3 / 2 := sqrt_two_lt_el
  have hs2' : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  rw [hsplit, hmass, hdir]
  have hterm1 : 2 * Real.sqrt 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
      axMass_el (hemisphere 1) u z) ≤ 2 * Real.sqrt 2 * M :=
    mul_le_mul_of_nonneg_left hax (by positivity)
  have hterm2 : 2 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
      axEnergy_el (hemisphere 1) u z) ≤ 2 * A :=
    mul_le_mul_of_nonneg_left hae (by norm_num)
  have hterm3 : (∫ σ, gfun_el (hemisphere 1) u σ)
      * (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, wt_el z)
      ≤ (Real.sqrt 2 * M + 4 * B) * (2 * Real.pi) := by
    rw [← hG]
    exact mul_le_mul_of_nonneg_left hwt hGnn
  nlinarith [hterm1, hterm2, hterm3, hM0, hA0, hB0, hs2, hpi, hs2', hpi0]

/-- **The entrance trace of a weak `H¹` function on the unit half-disk is square integrable**,
with the explicit bound `‖Tr_Σ u‖²_{L²(Σ)} ≤ 40 (‖u‖² + ‖∇u‖²)`.  This discharges the interface
`RobinCaps.Cap.CapEntranceL2` for `Cap.hemisphere 1`. -/
theorem capEntranceL2_hemi_el : ∃ C₁ : ℝ, CapEntranceL2 (Cap.hemisphere 1) C₁ := by
  refine ⟨40, ⟨by norm_num, fun u => ?_, fun u => ?_⟩⟩
  · have hmeas : AEStronglyMeasurable (entranceVal (hemisphere 1) u)
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
      (measurable_entranceVal (hemisphere 1) u).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hmeas).2 ?_
    refine Integrable.mono' (integrableOn_majFun_el u) (hmeas.pow 2) ?_
    filter_upwards [ae_entranceVal_sq_le_maj_el u] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  · have hmeas : AEStronglyMeasurable (entranceVal (hemisphere 1) u)
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
      (measurable_entranceVal (hemisphere 1) u).aestronglyMeasurable
    have hint : IntegrableOn (fun z => entranceVal (hemisphere 1) u z ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) volume := by
      refine Integrable.mono' (integrableOn_majFun_el u) (hmeas.pow 2) ?_
      filter_upwards [ae_entranceVal_sq_le_maj_el u] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz
    have hstep : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1,
        entranceVal (hemisphere 1) u z ^ 2)
        ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, majFun_el u z :=
      integral_mono_ae hint (integrableOn_majFun_el u) (ae_entranceVal_sq_le_maj_el u)
    exact hstep.trans (integral_majFun_le_el u)

end

end Cap
end RobinCaps
