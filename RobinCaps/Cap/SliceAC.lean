import RobinCaps.ThinDomain.Slice
import RobinCaps.ThinDomain.Restrict
import RobinCaps.Cap.EnergyC1

/-!
# Axial slice-wise absolute continuity on an end cap

This file upgrades the ACL (absolutely continuous on lines) theory of
`RobinCaps/ThinDomain/Slice.lean`, which is stated for a **product** domain
`(a,b) ×ˢ B`, to the **end-cap body**

`C = {(s,z) | -K < s < 0, ‖z‖ < θ s}`,

which is not a product but is, by `RobinCaps.Cap.axialSlice_eq`, a union of *initial* axial
intervals `(-K, e(z))` with `e = exitTime C z`.

The key geometric observation is that for `-K < c < 0` the open **sub-cylinder**

`Ω_c = (-K, c) ×ˢ B(0, θ c)`

is contained in the body (`prodSub_subset_body`), and that a point `z` of the entrance disk
satisfies `z ∈ B(0, θ c)` exactly when `c < e(z)` (`mem_ball_theta_iff_lt_exitTime`).  Running
`RobinCaps.ThinDomain.sliceACL_axial` on `Ω_c` for every **rational** `c` therefore produces a
single null set outside of which every axial slice has a weak derivative on all of `(-K, e(z))`
(a test function supported in `(-K,e(z))` has compact support, so it is already supported in
`(-K,c)` for some rational `c < e(z)`).

## Main results

* `sliceAC_axial_cap`: axial ACL on the cap body (**deliverable 1**);
* `entranceVal`, `measurable_entranceVal`, `entranceVal_spec`: the (measurable) entrance trace
  `Tr_Σ u` and the slice-wise fundamental theorem of calculus
  `u(s,z) = (Tr_Σ u)(z) + ∫_{-K}^s ∂ₓu(t,z) dt` characterising it;
* `exists_h1_axialSlice`: the absolutely continuous representative
  `w ∈ RobinCaps.Sobolev.H1 (e(z)+K)` of the axial slice, with `w(0) = (Tr_Σ u)(z)`
  (**deliverable 2**);
* `axial_poincare_weak` (**deliverable 3**): the weak-function version of
  `RobinCaps.Cap.axial_poincare_c1` / `RobinCaps.Cap.weighted_poincare_c1`,
  `‖u‖²_{L²(C)} ≤ 2K ‖Tr_Σ u‖²_{L²(B_m(1))} + 2K² ‖∂ₓu‖²_{L²(C)}`.

**A remark on the hypothesis of `axial_poincare_weak`.**  The statement carries the extra
hypothesis that `Tr_Σ u` is square integrable on the entrance disk.  This cannot be dropped as
stated: Lebesgue's integral of a non-integrable function is `0` in mathlib, so without the
hypothesis the right-hand side would collapse to `2K² ‖∂ₓu‖²` and the inequality would be false.
That `Tr_Σ u ∈ L²(B_m(1))` does hold for every `u ∈ H¹(C)` is the *trace theorem* for the cap; it
genuinely uses the transverse gradient `∇_z u` (the axial slice length `e(z)+K` degenerates to
`0` as `‖z‖ → 1`, so `∫_C (Tr_Σ u)(p₂)² < ∞` — which *is* unconditional — does not by itself give
`∫_{B_m(1)} (Tr_Σ u)² < ∞`), and it is not proved here.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology Interval

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev

noncomputable section

variable {m : ℕ}

/-! ## 1. The sub-cylinders of the cap body -/

/-- For `-K < c < 0` the open cylinder `(-K,c) × B(0, θ c)` is contained in the cap body:
the profile is non-increasing, so `‖z‖ < θ c ≤ θ s` for every `s ≤ c`. -/
theorem prodSub_subset_body (C : Cap m) {c : ℝ} (hc : c ∈ Ioo (-C.K) 0) :
    Ioo (-C.K) c ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ c) ⊆ C.body := by
  rintro ⟨s, z⟩ ⟨⟨hs1, hs2⟩, hz⟩
  rw [mem_ball_zero_iff] at hz
  have hsI : s ∈ Ioo (-C.K) 0 := ⟨hs1, hs2.trans hc.2⟩
  exact ⟨hs1, hsI.2, lt_of_lt_of_le hz (C.θ_antitone hsI hc hs2.le)⟩

/-- For `-K < c < 0`, the transverse points whose axial line is still inside the cap at `c`
are exactly the points of the ball of radius `θ c`. -/
theorem mem_ball_theta_iff_lt_exitTime (C : Cap m) {c : ℝ} (hc : c ∈ Ioo (-C.K) 0)
    (z : EuclideanSpace ℝ (Fin m)) : ‖z‖ < C.θ c ↔ c < exitTime C z := by
  constructor
  · intro h
    have : c ∈ axialSlice C z := mem_axialSlice.2 ⟨hc, h⟩
    rw [axialSlice_eq] at this
    exact this.2
  · intro h
    have : c ∈ axialSlice C z := by rw [axialSlice_eq]; exact ⟨hc.1, h⟩
    exact (mem_axialSlice.1 this).2

/-! ## 2. A localisation lemma for one-dimensional test integrals -/

/-- Enlarging the right endpoint does not change an integral against a function that vanishes
outside the smaller interval. -/
theorem setIntegral_Ioo_eq_of_vanishing {a b c : ℝ} (hbc : b ≤ c) {f w : ℝ → ℝ}
    (hw : ∀ x, x ∉ Ioo a b → w x = 0) :
    ∫ x in Ioo a c, f x * w x = ∫ x in Ioo a b, f x * w x := by
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo
    (Ioo_subset_Ioo le_rfl hbc) ?_
  rintro x ⟨-, hx2⟩
  rw [hw x hx2, mul_zero]

/-- A test function supported in `(a,b)` and its derivative both vanish outside `(a,b)`. -/
theorem test_vanishing {a b : ℝ} {φ : ℝ → ℝ} (hφs : tsupport φ ⊆ Ioo a b) :
    (∀ x, x ∉ Ioo a b → φ x = 0) ∧ (∀ x, x ∉ Ioo a b → deriv φ x = 0) := by
  refine ⟨fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφs h), fun x hx => ?_⟩
  have : x ∉ tsupport φ := fun h => hx (hφs h)
  exact Function.notMem_support.1 fun h => this (support_deriv_subset h)

/-- **Weak derivative on a shorter interval implies the identity for test functions supported
there.**  If `g` is a weak derivative of `v` on `(a,b)` and `b ≤ c`, then the
integration-by-parts identity on `(a,c)` holds for every test function supported in `(a,b)`. -/
theorem hasWeakDeriv_extend_test {a b c : ℝ} (hbc : b ≤ c) {v g : ℝ → ℝ}
    (h : HasWeakDeriv a b v g) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b) :
    ∫ x in Ioo a c, v x * deriv φ x = - ∫ x in Ioo a c, g x * φ x := by
  obtain ⟨hv1, hv2⟩ := test_vanishing hφs
  rw [setIntegral_Ioo_eq_of_vanishing hbc hv2, setIntegral_Ioo_eq_of_vanishing hbc hv1]
  exact h φ hφ hφc hφs

/-! ## 3. Deliverable 1: slice-wise absolute continuity on the cap -/

/-- The slice statement on one sub-cylinder `(-K,c) × B(0, θ c)`. -/
theorem sliceAC_axial_sub (C : Cap m) (u : H1P C.body) {c : ℝ} (hc : c ∈ Ioo (-C.K) 0) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))), ‖z‖ < C.θ c →
      HasWeakDeriv (-C.K) c (fun s => u.toFun (s, z)) (fun s => u.gx (s, z)) := by
  have hsub := prodSub_subset_body C hc
  have h := ThinDomain.sliceACL_axial (a := -C.K) (b := c)
    (B := ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ c)) hc.1 isOpen_ball (u.restrict hsub)
  rw [ae_restrict_iff' measurableSet_ball] at h
  filter_upwards [h] with z hz hzn
  exact hz (mem_ball_zero_iff.2 hzn)

/-- **Deliverable 1: axial ACL on the cap body.**  For almost every transverse point `z` of the
entrance disk, the axial slice `s ↦ u(s,z)` has `s ↦ (∂ₓu)(s,z)` as a weak derivative on the
whole axial slice `(-K, exitTime C z)`. -/
theorem sliceAC_axial_cap (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      HasWeakDeriv (-C.K) (exitTime C z) (fun s => u.toFun (s, z)) (fun s => u.gx (s, z)) := by
  have hfam : ∀ q : ℚ, ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (q : ℝ) ∈ Ioo (-C.K) 0 → ‖z‖ < C.θ (q : ℝ) →
        HasWeakDeriv (-C.K) (q : ℝ) (fun s => u.toFun (s, z)) (fun s => u.gx (s, z)) := by
    intro q
    by_cases hq : (q : ℝ) ∈ Ioo (-C.K) 0
    · filter_upwards [sliceAC_axial_sub C u hq] with z hz
      intro _ hzn
      exact hz hzn
    · filter_upwards with z h1
      exact absurd h1 hq
  have hall := ae_all_iff.2 hfam
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hall] with z hz hzball
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzball
  have heI : exitTime C z ∈ Ioc (-C.K) 0 := exitTime_mem C hznorm
  intro φ hφ hφc hφs
  -- a compact, nonempty subset of the slice containing `tsupport φ`
  set S : Set ℝ := tsupport φ ∪ {(-C.K + exitTime C z) / 2} with hS
  have hmid : (-C.K + exitTime C z) / 2 ∈ Ioo (-C.K) (exitTime C z) :=
    ⟨by linarith [heI.1], by linarith [heI.1]⟩
  have hScompact : IsCompact S := hφc.union isCompact_singleton
  have hSne : S.Nonempty := ⟨_, Or.inr rfl⟩
  have hSsub : S ⊆ Ioo (-C.K) (exitTime C z) := by
    rintro x (hx | hx)
    · exact hφs hx
    · rw [mem_singleton_iff] at hx; rw [hx]; exact hmid
  have hM : sSup S ∈ S := hScompact.sSup_mem hSne
  have hMI : sSup S ∈ Ioo (-C.K) (exitTime C z) := hSsub hM
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hMI.2
  have hqI : (q : ℝ) ∈ Ioo (-C.K) 0 := ⟨hMI.1.trans hq1, hq2.trans_le heI.2⟩
  have hφq : tsupport φ ⊆ Ioo (-C.K) (q : ℝ) := by
    intro x hx
    exact ⟨(hφs hx).1, lt_of_le_of_lt (le_csSup hScompact.bddAbove (Or.inl hx)) hq1⟩
  have hkey := hz q hqI ((mem_ball_theta_iff_lt_exitTime C hqI z).2 hq2)
  exact hasWeakDeriv_extend_test hq2.le hkey hφ hφc hφq

/-! ## 4. Integrability of the axial slices of the cap -/

/-- The axial line of the body-indicator of `f` is the slice-indicator of the line of `f`. -/
theorem indicator_body_line (C : Cap m) (f : CapSpace m → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    C.body.indicator f (s, z)
      = (Ioo (-C.K) (exitTime C z)).indicator (fun s => f (s, z)) s := by
  by_cases h : (s, z) ∈ C.body
  · have h' : s ∈ Ioo (-C.K) (exitTime C z) := by rw [← axialSlice_eq]; exact h
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : s ∉ Ioo (-C.K) (exitTime C z) := by rw [← axialSlice_eq]; exact h
    rw [indicator_of_notMem h, indicator_of_notMem h']

/-- The cap body has finite volume. -/
theorem volume_body_ne_top (C : Cap m) : (volume : Measure (CapSpace m)) C.body ≠ (⊤ : ℝ≥0∞) :=
  ((measure_mono (body_subset_box C)).trans_lt (isCompact_box C).measure_lt_top).ne

instance isFiniteMeasure_restrict_body (C : Cap m) :
    IsFiniteMeasure ((volume : Measure (CapSpace m)).restrict C.body) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (volume_body_ne_top C)⟩

/-- An `L²` function on the (finite-volume) body is integrable there. -/
theorem integrableOn_body_of_memL2 (C : Cap m) {f : CapSpace m → ℝ}
    (hf : MemLp f 2 (volume.restrict C.body)) : IntegrableOn f C.body volume :=
  hf.integrable one_le_two

/-- **Almost every axial slice of an integrable function is integrable.** -/
theorem ae_integrableOn_cap_slice (C : Cap m) {f : CapSpace m → ℝ}
    (hf : IntegrableOn f C.body volume) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      IntegrableOn (fun s => f (s, z)) (Ioo (-C.K) (exitTime C z)) volume := by
  have hi : Integrable (C.body.indicator f) volume :=
    hf.integrable_indicator (measurableSet_body' C)
  rw [Measure.volume_eq_prod] at hi
  filter_upwards [hi.prod_left_ae] with z hz
  refine (integrable_indicator_iff measurableSet_Ioo).1 ?_
  exact hz.congr (Eventually.of_forall fun s => indicator_body_line C f z s)

/-- Transfer of an almost-everywhere statement on the product to almost every axial line. -/
theorem ae_ae_axial {Q : CapSpace m → Prop} (h : ∀ᵐ p ∂(volume : Measure (CapSpace m)), Q p) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ᵐ s ∂(volume : Measure ℝ), Q (s, z) := by
  rw [Measure.volume_eq_prod] at h
  exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae h)

/-! ## 5. The entrance constant of an axial slice -/

/-- **The entrance constant exists on almost every axial line.**  For almost every `z` in the
entrance disk there is a constant `c` with `u(s,z) = c + ∫_{-K}^s ∂ₓu(t,z) dt` for almost every
`s` in the axial slice; `c` is the value of the absolutely continuous representative at the
entrance. -/
theorem exists_entranceConst (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)), ∃ c : ℝ,
      ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) (exitTime C z))),
        u.toFun (s, z) = c + ∫ t in (-C.K)..s, u.gx (t, z) := by
  filter_upwards [sliceAC_axial_cap C u,
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.memL2)),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hw hu hg hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  obtain ⟨c, hc⟩ := ae_eq_const_add_integral hKe hu hg hw
  set e := exitTime C z with hedef
  set mid : ℝ := (-C.K + e) / 2 with hmid
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-C.K) e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hg
  have hII : ∀ y w : ℝ, y ∈ Icc (-C.K) e → w ∈ Icc (-C.K) e →
      IntervalIntegrable (fun t => u.gx (t, z)) volume y w := by
    intro y w hy hw'
    refine hgI.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le hKe.le]; exact hy
    · rw [uIcc_of_le hKe.le]; exact hw'
  refine ⟨c + ∫ t in mid..(-C.K), u.gx (t, z), ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  have hs' : u.toFun (s, z) = c + ∫ t in mid..s, u.gx (t, z) := hs
  have hmidIcc : mid ∈ Icc (-C.K) e := ⟨by rw [hmid]; linarith, by rw [hmid]; linarith⟩
  have hsIcc : s ∈ Icc (-C.K) e := Ioo_subset_Icc_self hsmem
  have hsplit : (∫ t in mid..s, u.gx (t, z))
      = (∫ t in mid..(-C.K), u.gx (t, z)) + ∫ t in (-C.K)..s, u.gx (t, z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hII mid (-C.K) hmidIcc ⟨le_rfl, hKe.le⟩) (hII (-C.K) s ⟨le_rfl, hKe.le⟩ hsIcc)).symm
  rw [hs', hsplit]; ring

/-! ## 6. A measurable entrance trace -/

/-- A globally strongly measurable representative of `u` (equal to `u` a.e. on the body). -/
def repFun (C : Cap m) (u : H1P C.body) : CapSpace m → ℝ :=
  u.memL2.aestronglyMeasurable.mk u.toFun

/-- A globally strongly measurable representative of `∂ₓu`. -/
def repGx (C : Cap m) (u : H1P C.body) : CapSpace m → ℝ :=
  u.gx_memL2.aestronglyMeasurable.mk u.gx

theorem stronglyMeasurable_repFun (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (repFun C u) := u.memL2.aestronglyMeasurable.stronglyMeasurable_mk

theorem stronglyMeasurable_repGx (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (repGx C u) := u.gx_memL2.aestronglyMeasurable.stronglyMeasurable_mk

/-- The region `{(t,p) | -K < t < p.1}` used to define the axial primitive. -/
theorem measurableSet_primRegion (C : Cap m) :
    MeasurableSet {r : ℝ × CapSpace m | r.1 ∈ Ioo (-C.K) r.2.1} := by
  have h1 : IsOpen {r : ℝ × CapSpace m | -C.K < r.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {r : ℝ × CapSpace m | r.1 < r.2.1} :=
    isOpen_lt continuous_fst (continuous_fst.comp continuous_snd)
  exact (h1.inter h2).measurableSet

/-- The integration kernel of the axial primitive of `∂ₓu` from the entrance. -/
def primKernel (C : Cap m) (u : H1P C.body) : ℝ × CapSpace m → ℝ :=
  {r : ℝ × CapSpace m | r.1 ∈ Ioo (-C.K) r.2.1}.indicator fun r => repGx C u (r.1, r.2.2)

/-- The **axial primitive** `p ↦ ∫_{-K}^{p.1} ∂ₓu(t, p.2) dt`, in a manifestly measurable form. -/
def slicePrim (C : Cap m) (u : H1P C.body) (p : CapSpace m) : ℝ := ∫ t, primKernel C u (t, p)

theorem stronglyMeasurable_primKernel (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (primKernel C u) := by
  refine StronglyMeasurable.indicator ?_ (measurableSet_primRegion C)
  exact (stronglyMeasurable_repGx C u).comp_measurable
    (by fun_prop : Measurable fun r : ℝ × CapSpace m => (r.1, r.2.2))

theorem stronglyMeasurable_slicePrim (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (slicePrim C u) :=
  (stronglyMeasurable_primKernel C u).integral_prod_left'

theorem slicePrim_eq (C : Cap m) (u : H1P C.body) (s : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    slicePrim C u (s, z) = ∫ t in Ioo (-C.K) s, repGx C u (t, z) := by
  rw [slicePrim, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [primKernel, Set.indicator_apply, Set.mem_setOf_eq]

/-- The integrand whose slice average is the entrance value. -/
def entranceIntegrand (C : Cap m) (u : H1P C.body) : CapSpace m → ℝ :=
  C.body.indicator fun p => repFun C u p - slicePrim C u p

/-- **The entrance trace of a weak-`H¹` function.**  On almost every axial line the function
`s ↦ u(s,z) - ∫_{-K}^s ∂ₓu(t,z) dt` is a.e. constant, and `entranceVal C u z` is that constant,
written as its average over the axial slice so as to be manifestly measurable in `z`. -/
def entranceVal (C : Cap m) (u : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (∫ s, entranceIntegrand C u (s, z)) / (exitTime C z + C.K)

theorem stronglyMeasurable_entranceIntegrand (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (entranceIntegrand C u) :=
  ((stronglyMeasurable_repFun C u).sub (stronglyMeasurable_slicePrim C u)).indicator
    (measurableSet_body' C)

/-- **The entrance trace is measurable.** -/
theorem measurable_entranceVal (C : Cap m) (u : H1P C.body) : Measurable (entranceVal C u) := by
  have h1 : StronglyMeasurable fun z => ∫ s, entranceIntegrand C u (s, z) :=
    (stronglyMeasurable_entranceIntegrand C u).integral_prod_left'
  exact h1.measurable.div ((measurable_exitTime C).add measurable_const)

/-! ### The defining property of the entrance trace -/

theorem ae_slice_repFun (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ᵐ s ∂(volume : Measure ℝ), (s, z) ∈ C.body → repFun C u (s, z) = u.toFun (s, z) := by
  refine ae_ae_axial (Q := fun p => p ∈ C.body → repFun C u p = u.toFun p) ?_
  have h : u.toFun =ᵐ[volume.restrict C.body] repFun C u :=
    u.memL2.aestronglyMeasurable.ae_eq_mk
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at h
  filter_upwards [h] with p hp hpb using (hp hpb).symm

theorem ae_slice_repGx (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ᵐ s ∂(volume : Measure ℝ), (s, z) ∈ C.body → repGx C u (s, z) = u.gx (s, z) := by
  refine ae_ae_axial (Q := fun p => p ∈ C.body → repGx C u p = u.gx p) ?_
  have h : u.gx =ᵐ[volume.restrict C.body] repGx C u :=
    u.gx_memL2.aestronglyMeasurable.ae_eq_mk
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at h
  filter_upwards [h] with p hp hpb using (hp hpb).symm

/-- **Deliverable 2.**  For almost every `z` in the entrance disk, the axial slice of `u` is
(a.e. equal to) the absolutely continuous function `s ↦ entranceVal C u z + ∫_{-K}^s ∂ₓu`. -/
theorem entranceVal_spec (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) (exitTime C z))),
        u.toFun (s, z) = entranceVal C u z + ∫ t in (-C.K)..s, u.gx (t, z) := by
  filter_upwards [exists_entranceConst C u, ae_restrict_of_ae (ae_slice_repFun C u),
    ae_restrict_of_ae (ae_slice_repGx C u), ae_restrict_mem measurableSet_ball]
    with z hc hrf hrg hzb
  obtain ⟨c, hc⟩ := hc
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  have hmemslice : ∀ s : ℝ, s ∈ Ioo (-C.K) e → (s, z) ∈ C.body := by
    intro s hs
    have : s ∈ axialSlice C z := by rw [axialSlice_eq]; exact hs
    exact this
  -- the primitive of the representative agrees with the interval integral of `∂ₓu`
  have hprim : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)),
      slicePrim C u (s, z) = ∫ t in (-C.K)..s, u.gx (t, z) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [slicePrim_eq, intervalIntegral_eq_setIntegral_Ioo hs.1.le]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrg] with t ht htmem
    exact ht (hmemslice t ⟨htmem.1, htmem.2.trans hs.2⟩)
  -- hence the integrand is a.e. equal to the constant `c` on the slice
  have hconst : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)),
      repFun C u (s, z) - slicePrim C u (s, z) = c := by
    filter_upwards [hc, hprim, ae_restrict_of_ae hrf, ae_restrict_mem measurableSet_Ioo]
      with s hs1 hs2 hs3 hs4
    rw [hs3 (hmemslice s hs4), hs2, hs1]; ring
  -- compute the slice average
  have hint : (∫ s, entranceIntegrand C u (s, z)) = (e + C.K) * c := by
    rw [entranceIntegrand, integral_indicator_body_line C
      (fun p => repFun C u p - slicePrim C u p) z, ← hedef]
    rw [setIntegral_congr_ae measurableSet_Ioo ((ae_restrict_iff' measurableSet_Ioo).1 hconst)]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le hKe.le, smul_eq_mul]
    ring
  have hne : e + C.K ≠ 0 := by linarith
  have hev : entranceVal C u z = c := by
    rw [entranceVal, hint, ← hedef]
    field_simp
  rw [hev]
  filter_upwards [hc] with s hs using hs

/-! ## 7. The transverse bound on the body -/

/-- The body sits inside the product box `(-K,0) × B(0,1)`. -/
theorem body_subset_prod (C : Cap m) :
    C.body ⊆ Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  rintro p ⟨h1, h2, h3⟩
  exact ⟨⟨h1, h2⟩, mem_ball_zero_iff.2 (lt_of_lt_of_le h3 (C.θ_le_one _ ⟨h1, h2⟩))⟩

theorem integrableOn_prodBox_transverse (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hfi : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume) :
    IntegrableOn (fun p : CapSpace m => f p.2)
      (Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  rw [IntegrableOn, restrict_prodDomain]
  exact hfi.comp_snd _

theorem integral_prodBox_transverse (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hfi : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume) :
    (∫ p in Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1, f p.2)
      = C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f z := by
  rw [restrict_prodDomain, integral_prod_symm _ (hfi.comp_snd _), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (∫ _x : ℝ in Ioo (-C.K) 0, f z) = C.K * f z
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [C.hK] : -C.K ≤ (0 : ℝ)),
    smul_eq_mul]
  ring

/-- **Slice bound for measurable transverse data.**  This is the version of
`RobinCaps.Cap.integral_body_transverse_le` for a merely integrable (not continuous) `f`. -/
theorem integral_body_transverse_le' (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf0 : ∀ z, 0 ≤ f z)
    (hfi : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume) :
    (∫ p in C.body, f p.2) ≤ C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f z := by
  have h1 : (∫ p in C.body, f p.2)
      ≤ ∫ p in Ioo (-C.K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1, f p.2 :=
    setIntegral_mono_set (integrableOn_prodBox_transverse C hfi)
      (Eventually.of_forall fun p => hf0 p.2)
      (HasSubset.Subset.eventuallyLE (body_subset_prod C))
  rwa [integral_prodBox_transverse C hfi] at h1

/-! ## 8. The one-dimensional estimate on an axial slice -/

/-- Cauchy–Schwarz on an initial subinterval `[a,s]` of `(a,e)`. -/
theorem sq_intervalIntegral_le {a s e : ℝ} (has : a ≤ s) (hse : s ≤ e) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a e) volume)
    (hg2 : IntegrableOn (fun t => g t ^ 2) (Ioo a e) volume) :
    (∫ t in a..s, g t) ^ 2 ≤ (e - a) * ∫ t in Ioo a e, g t ^ 2 := by
  have hae : a ≤ e := has.trans hse
  have hgI : IntervalIntegrable g volume a e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hae).2 hg
  have hg2I : IntervalIntegrable (fun t => g t ^ 2) volume a e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hae).2 hg2
  have hsub : uIcc a s ⊆ uIcc a e := by
    rw [uIcc_of_le has, uIcc_of_le hae]; exact Icc_subset_Icc le_rfl hse
  have hgs : IntervalIntegrable g volume a s := hgI.mono_set hsub
  have hg2s : IntervalIntegrable (fun t => g t ^ 2) volume a s := hg2I.mono_set hsub
  have habs : |∫ t in a..s, g t| ≤ ∫ t in a..s, |g t| :=
    intervalIntegral.abs_integral_le_integral_abs has
  have habs0 : 0 ≤ ∫ t in a..s, |g t| :=
    intervalIntegral.integral_nonneg has fun t _ => abs_nonneg _
  have hcs : (∫ t in a..s, |g t|) ^ 2 ≤ (s - a) * ∫ t in a..s, g t ^ 2 :=
    RobinCaps.Transverse.abs_integral_sq_le_on has g hgs hg2s
  have hmono : (∫ t in a..s, g t ^ 2) ≤ ∫ t in a..e, g t ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl has hse
      (ae_of_all _ fun t => sq_nonneg _) hg2I
  have hs0 : 0 ≤ ∫ t in a..s, g t ^ 2 :=
    intervalIntegral.integral_nonneg has fun t _ => sq_nonneg _
  have hsq : (∫ t in a..s, g t) ^ 2 ≤ (∫ t in a..s, |g t|) ^ 2 := by
    nlinarith [sq_abs (∫ t in a..s, g t), abs_nonneg (∫ t in a..s, g t)]
  have heq : (∫ t in a..e, g t ^ 2) = ∫ t in Ioo a e, g t ^ 2 :=
    intervalIntegral_eq_setIntegral_Ioo hae
  have hfin : (s - a) * (∫ t in a..s, g t ^ 2) ≤ (e - a) * ∫ t in a..e, g t ^ 2 :=
    mul_le_mul (by linarith) hmono hs0 (by linarith)
  rw [← heq]
  linarith

/-- **Line-wise Poincaré inequality from the entrance, weak version.** -/
theorem slice_poincare_weak (C : Cap m) (u : H1P C.body) {z : EuclideanSpace ℝ (Fin m)}
    (hz : ‖z‖ < 1)
    (hc : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) (exitTime C z))),
      u.toFun (s, z) = entranceVal C u z + ∫ t in (-C.K)..s, u.gx (t, z))
    (hD : IntegrableOn (fun s => (u.toFun (s, z) - entranceVal C u z) ^ 2)
      (Ioo (-C.K) (exitTime C z)) volume)
    (hg : IntegrableOn (fun s => u.gx (s, z)) (Ioo (-C.K) (exitTime C z)) volume)
    (hg2 : IntegrableOn (fun s => u.gx (s, z) ^ 2) (Ioo (-C.K) (exitTime C z)) volume) :
    (∫ s in Ioo (-C.K) (exitTime C z), (u.toFun (s, z) - entranceVal C u z) ^ 2)
      ≤ C.K ^ 2 * ∫ s in Ioo (-C.K) (exitTime C z), u.gx (s, z) ^ 2 := by
  have hKe : -C.K < exitTime C z := (exitTime_mem C hz).1
  have he0 : exitTime C z ≤ 0 := (exitTime_mem C hz).2
  set e := exitTime C z with hedef
  set J : ℝ := ∫ s in Ioo (-C.K) e, u.gx (s, z) ^ 2 with hJ
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioo fun s _ => sq_nonneg _
  have hbound : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)),
      (u.toFun (s, z) - entranceVal C u z) ^ 2 ≤ C.K * J := by
    filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with s hs hsm
    have h1 : u.toFun (s, z) - entranceVal C u z = ∫ t in (-C.K)..s, u.gx (t, z) := by
      rw [hs]; ring
    have h2 := sq_intervalIntegral_le hsm.1.le hsm.2.le hg hg2
    have h3 : (e - -C.K) * J ≤ C.K * J := mul_le_mul_of_nonneg_right (by linarith) hJ0
    rw [h1]
    linarith
  have hstep : (∫ s in Ioo (-C.K) e, (u.toFun (s, z) - entranceVal C u z) ^ 2)
      ≤ ∫ _s in Ioo (-C.K) e, C.K * J :=
    integral_mono_ae hD (integrable_const _) hbound
  rw [setIntegral_const, Real.volume_real_Ioo_of_le hKe.le, smul_eq_mul] at hstep
  have h4 : (e - -C.K) * (C.K * J) ≤ C.K * (C.K * J) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg C.hK.le hJ0)
  nlinarith [hstep, h4]

/-! ## 9. Deliverable 3: the axial Poincaré inequality for weak-`H¹` functions -/

/-- **The weak-function version of `RobinCaps.Cap.axial_poincare_c1` / `weighted_poincare_c1`.**

`‖u‖²_{L²(C)} ≤ 2K ‖Tr_Σ u‖²_{L²(B_m(1))} + 2K² ‖∂ₓu‖²_{L²(C)}`,

for every `u ∈ H¹(C)` whose entrance trace is square integrable on the entrance disk. -/
theorem axial_poincare_weak (C : Cap m) (u : H1P C.body)
    (hev : IntegrableOn (fun z => entranceVal C u z ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume) :
    massP u ≤ 2 * C.K * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, entranceVal C u z ^ 2)
      + 2 * C.K ^ 2 * ∫ p in C.body, u.gx p ^ 2 := by
  have hbody := measurableSet_body' C
  have hMi : IntegrableOn (fun p : CapSpace m => u.toFun p ^ 2) C.body volume :=
    u.memL2.integrable_sq
  have hGi : IntegrableOn (fun p : CapSpace m => u.gx p ^ 2) C.body volume :=
    u.gx_memL2.integrable_sq
  have hEi : IntegrableOn (fun p : CapSpace m => entranceVal C u p.2 ^ 2) C.body volume :=
    (integrableOn_prodBox_transverse C hev).mono_set (body_subset_prod C)
  have hDmeas : AEStronglyMeasurable
      (fun p : CapSpace m => (u.toFun p - entranceVal C u p.2) ^ 2)
      (volume.restrict C.body) :=
    (u.memL2.aestronglyMeasurable.sub
      ((measurable_entranceVal C u).comp measurable_snd).aestronglyMeasurable).pow 2
  have hDi : IntegrableOn (fun p : CapSpace m => (u.toFun p - entranceVal C u p.2) ^ 2)
      C.body volume := by
    refine Integrable.mono' ((hMi.const_mul 2).add (hEi.const_mul 2)) hDmeas ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (u.toFun p + entranceVal C u p.2)]
  -- the Dirichlet part
  have hDle : (∫ p in C.body, (u.toFun p - entranceVal C u p.2) ^ 2)
      ≤ C.K ^ 2 * ∫ p in C.body, u.gx p ^ 2 := by
    have hDind : Integrable (C.body.indicator
        fun p : CapSpace m => (u.toFun p - entranceVal C u p.2) ^ 2) volume :=
      hDi.integrable_indicator hbody
    have hGind : Integrable (C.body.indicator fun p : CapSpace m => u.gx p ^ 2) volume :=
      hGi.integrable_indicator hbody
    rw [integral_body_eq_integral_slices C hDind, integral_body_eq_integral_slices C hGind,
      ← integral_const_mul]
    refine integral_mono_ae (integrable_slice_integral C hDind)
      ((integrable_slice_integral C hGind).const_mul _) ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (entranceVal_spec C u),
      ae_integrableOn_cap_slice C hDi,
      ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2),
      ae_integrableOn_cap_slice C hGi] with z hz1 hz2 hz3 hz4
    by_cases hzb : ‖z‖ < 1
    · exact slice_poincare_weak C u hzb (hz1 (mem_ball_zero_iff.2 hzb)) hz2 hz3 hz4
    · push_neg at hzb
      rw [exitTime_eq_neg_K_of_one_le C hzb]
      simp
  -- the trace part
  have hEle : (∫ p in C.body, entranceVal C u p.2 ^ 2)
      ≤ C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, entranceVal C u z ^ 2 :=
    integral_body_transverse_le' C (fun z => sq_nonneg _) hev
  -- assembling
  have hptw : ∀ p ∈ C.body, u.toFun p ^ 2
      ≤ 2 * (u.toFun p - entranceVal C u p.2) ^ 2 + 2 * entranceVal C u p.2 ^ 2 := by
    intro p _
    nlinarith [sq_nonneg (u.toFun p - 2 * entranceVal C u p.2)]
  have hsum : IntegrableOn (fun p : CapSpace m =>
      2 * (u.toFun p - entranceVal C u p.2) ^ 2 + 2 * entranceVal C u p.2 ^ 2) C.body volume :=
    (hDi.const_mul 2).add (hEi.const_mul 2)
  have hstep := setIntegral_mono_on hMi hsum hbody hptw
  rw [integral_add (hDi.const_mul 2) (hEi.const_mul 2), integral_const_mul,
    integral_const_mul] at hstep
  have hmass : massP u = ∫ p in C.body, u.toFun p ^ 2 := rfl
  rw [hmass]
  linarith

/-! ## 10. The absolutely continuous representative of an axial slice -/

/-- **Deliverable 2 (absolutely continuous representative).**  For almost every `z` in the
entrance disk, the axial slice of `u`, read on the translated interval `(0, e(z)+K)`, has an
absolutely continuous representative `w : RobinCaps.Sobolev.H1 (e(z)+K)` whose derivative is the
slice of `∂ₓu` and whose value at the entrance point `0` is exactly `entranceVal C u z`. -/
theorem exists_h1_axialSlice (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      ∃ w : Sobolev.H1 (exitTime C z + C.K),
        w.toFun 0 = entranceVal C u z ∧
        w.toFun =ᵐ[volume.restrict (Ioo 0 (exitTime C z + C.K))]
          (fun x => u.toFun (x - C.K, z)) ∧
        deriv w.toFun =ᵐ[volume.restrict (Ioo 0 (exitTime C z + C.K))]
          (fun x => u.gx (x - C.K, z)) := by
  filter_upwards [entranceVal_spec C u,
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2)),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C u.gx_memL2.integrable_sq),
    ae_restrict_mem measurableSet_ball] with z hc hg hg2 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  set ℓ : ℝ := e + C.K with hℓdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; linarith
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-C.K) e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hg
  have hg2I : IntervalIntegrable (fun t => u.gx (t, z) ^ 2) volume (-C.K) e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hg2
  have hGI : IntervalIntegrable (fun t => u.gx (t - C.K, z)) volume 0 ℓ := by
    have h := hgI.comp_sub_right C.K
    rw [neg_add_cancel] at h
    exact h
  have hG2I : IntervalIntegrable (fun t => u.gx (t - C.K, z) ^ 2) volume 0 ℓ := by
    have h := hg2I.comp_sub_right C.K
    rw [neg_add_cancel] at h
    exact h
  have hmem : ∀ x ∈ Ioo (0 : ℝ) ℓ, x - C.K ∈ Ioo (-C.K) e := by
    intro x hx
    rw [hℓdef] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hc' : ∀ᵐ x ∂(volume : Measure ℝ), x - C.K ∈ Ioo (-C.K) e →
      u.toFun (x - C.K, z) = entranceVal C u z + ∫ t in (-C.K)..(x - C.K), u.gx (t, z) :=
    (measurePreserving_sub_right (volume : Measure ℝ) C.K).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).1 hc)
  refine ⟨Sobolev.primitiveH1 hℓ.le hGI hG2I (entranceVal C u z), ?_, ?_, ?_⟩
  · rw [Sobolev.primitiveH1_toFun]; simp
  · rw [Sobolev.primitiveH1_toFun, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hc'] with x hx hxmem
    show entranceVal C u z + (∫ t in (0 : ℝ)..x, u.gx (t - C.K, z)) = u.toFun (x - C.K, z)
    rw [hx (hmem x hxmem),
      intervalIntegral.integral_comp_sub_right (fun t => u.gx (t, z)) C.K, zero_sub]
  · rw [Sobolev.primitiveH1_toFun]
    have hae := Sobolev.ae_deriv_primitive hGI (entranceVal C u z) (x₀ := (0 : ℝ)) left_mem_uIcc
    have hsub : Ioo (0 : ℝ) ℓ ⊆ Ι (0 : ℝ) ℓ := by
      rw [uIoc_of_le hℓ.le]; exact Ioo_subset_Ioc_self
    exact hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))

end

end Cap
end RobinCaps
