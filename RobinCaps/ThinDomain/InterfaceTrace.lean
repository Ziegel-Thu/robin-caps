import RobinCaps.ThinDomain.SliceThin
import RobinCaps.ThinDomain.Restrict
import RobinCaps.Cap.SliceAC
import RobinCaps.Sobolev.Interval

/-!
# The interface trace of a weak-`H¹` function on the thin domain

This file formalizes the manuscript's `eq:interface-trace` / `eq:interval-trace` ingredient.

For `u ∈ H¹(Ω_R)` (the weak product model `H1P` of `RobinCaps/ThinDomain/H1P.lean`) the axial
ACL property `RobinCaps.ThinDomain.sliceACL_axial_thin` says that for a.e. transverse point
`z ∈ B_m(R)` the axial slice `x ↦ u(x,z)` has a weak derivative on the *whole* axial slice
`(aZ z, bZ z)` of `Ω_R`.  Consequently that slice has an absolutely continuous representative,
and its value at the **left interface abscissa** `x₋ = -L/2 + K₋ R` is a well-defined number
`ifaceL u z` (resp. `ifaceR u z` at `x₊ = L/2 - K₊ R`).

The three results are:

1. `ifaceL`, `measurable_ifaceL`, `ifaceL_spec` (and the `R` analogues): the interface values,
   measurable in `z`, characterised by the slice-wise fundamental theorem of calculus.
2. `integral_ifaceL_sq_le`, `integrableOn_ifaceL_sq`: the `L²(B_m(R))` bound with the explicit
   constant of the one-dimensional trace inequality `RobinCaps.Sobolev.endpoint_zero_sq_le` on
   the bulk interval of length `ℓ_R = bulkLength Cm Cp L R`.
3. `entranceVal_capLeft`: the identification `Tr_Σ (capLeft c u) (z') = c · ifaceL u (R z')` of
   the cap entrance trace of `RobinCaps/Cap/SliceAC.lean` with the interface trace, hence
   `integrableOn_entranceVal_sq_capLeft` and `axial_poincare_capLeft` — the hypothesis `hev` of
   `RobinCaps.Cap.axial_poincare_weak` discharged for the cap components of a thin-domain
   function.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.

## A remark on imports

`RobinCaps/ThinDomain/Slice.lean` and `RobinCaps/ThinDomain/AxialCoeff.lean` both declare
`RobinCaps.ThinDomain.prodTest`, so they cannot be imported together; everything imported here
goes through `Slice.lean` (via `SliceThin.lean`, `Restrict.lean` and `Cap/SliceAC.lean`), and
`AxialCoeff.lean` is not used.
-/

open MeasureTheory Set Filter Metric

open scoped ContDiff ENNReal Topology Interval

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev

noncomputable section

variable {m : ℕ} {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-! ## 1. The bulk interval inside the axial slices -/

/-- The open bulk cylinder is the product of the bulk interval and the transverse ball. -/
theorem bulkOpen_eq_prod_it :
    bulkOpen Cm Cp L R
      = Ioo (interfaceL Cm L R) (interfaceR Cp L R)
          ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) R := rfl

/-- The bulk length is the length of the bulk interval. -/
theorem bulkLength_eq_sub_it :
    bulkLength Cm Cp L R = interfaceR Cp L R - interfaceL Cm L R := by
  simp only [bulkLength, interfaceL, interfaceR]; ring

theorem interfaceL_lt_interfaceR_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    interfaceL Cm L R < interfaceR Cp L R := interface_lt hR hL

theorem bulkLength_pos_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    0 < bulkLength Cm Cp L R := by
  rw [bulkLength_eq_sub_it]
  linarith [interfaceL_lt_interfaceR_it (Cm := Cm) (Cp := Cp) hR hL]

/-- **The bulk interval is contained in every axial slice through the transverse ball.** -/
theorem Ioo_interface_subset_axialSlice_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < R) :
    Ioo (interfaceL Cm L R) (interfaceR Cp L R)
      ⊆ Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z) := by
  rw [← thinDomain_axialSlice hR hL]
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  simp only [interfaceL, interfaceR] at h1 h2
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  refine ⟨by linarith, by linarith, ?_⟩
  rw [profile_bulk h1.le h2.le]
  exact hz

theorem aZ_le_interfaceL_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < R) :
    aZ Cm Cp L R z ≤ interfaceL Cm L R :=
  ((Ioo_subset_Ioo_iff (interfaceL_lt_interfaceR_it hR hL)).1
    (Ioo_interface_subset_axialSlice_it hR hL hz)).1

theorem interfaceR_le_bZ_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < R) :
    interfaceR Cp L R ≤ bZ Cm Cp L R z :=
  ((Ioo_subset_Ioo_iff (interfaceL_lt_interfaceR_it hR hL)).1
    (Ioo_interface_subset_axialSlice_it hR hL hz)).2

theorem aZ_lt_bZ_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < R) :
    aZ Cm Cp L R z < bZ Cm Cp L R z :=
  lt_of_le_of_lt (aZ_le_interfaceL_it hR hL hz)
    (lt_of_lt_of_le (interfaceL_lt_interfaceR_it hR hL) (interfaceR_le_bZ_it hR hL hz))

/-! ## 2. Integrability of the axial slices of the thin domain -/

/-- The thin domain has finite volume. -/
theorem volume_thinDomain_ne_top_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    (volume : Measure (CapSpace m)) (thinDomain Cm Cp L R) ≠ (⊤ : ℝ≥0∞) := by
  have hsub : thinDomain Cm Cp L R
      ⊆ Ioo (-L / 2) (L / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) R := fun p hp =>
    ⟨⟨hp.1, hp.2.1⟩,
      mem_ball_zero_iff.2 (lt_of_lt_of_le hp.2.2 (profile_le_R hR hL ⟨hp.1, hp.2.1⟩))⟩
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
    (lt_top_iff_ne_top.2 (volume_prod_ne_top measure_ball_lt_top.ne)))

/-- An `L²` function on the (finite-volume) thin domain is integrable there. -/
theorem integrableOn_thin_of_memL2_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {f : CapSpace m → ℝ} (hf : MemLp f 2 (volume.restrict (thinDomain Cm Cp L R))) :
    IntegrableOn f (thinDomain Cm Cp L R) volume := by
  haveI : IsFiniteMeasure ((volume : Measure (CapSpace m)).restrict (thinDomain Cm Cp L R)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.2 (volume_thinDomain_ne_top_it hR hL)⟩
  exact hf.integrable one_le_two

/-- The axial line of the `Ω_R`-indicator of `f` is the slice-indicator of the axial line. -/
theorem indicator_thin_line_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (f : CapSpace m → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (x : ℝ) :
    (thinDomain Cm Cp L R).indicator f (x, z)
      = (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z)).indicator (fun x => f (x, z)) x := by
  have hiff : (x, z) ∈ thinDomain Cm Cp L R
      ↔ x ∈ Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z) := by
    rw [← thinDomain_axialSlice hR hL]; exact Iff.rfl
  by_cases h : (x, z) ∈ thinDomain Cm Cp L R
  · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun hc => h (hiff.2 hc))]

/-- **Almost every axial slice of an integrable function is integrable.** -/
theorem ae_integrableOn_thin_slice_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {f : CapSpace m → ℝ} (hf : IntegrableOn f (thinDomain Cm Cp L R) volume) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      IntegrableOn (fun x => f (x, z)) (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z)) volume := by
  have hi : Integrable ((thinDomain Cm Cp L R).indicator f) volume :=
    hf.integrable_indicator (isOpen_thinDomain hR hL).measurableSet
  rw [Measure.volume_eq_prod] at hi
  filter_upwards [hi.prod_left_ae] with z hz
  refine (integrable_indicator_iff measurableSet_Ioo).1 ?_
  exact hz.congr (Eventually.of_forall fun x => indicator_thin_line_it hR hL f z x)

/-! ## 3. A measurable interface trace -/

/-- A globally strongly measurable representative of `u` (equal to `u` a.e. on `Ω_R`). -/
def repFunT (u : H1P (thinDomain Cm Cp L R)) : CapSpace m → ℝ :=
  u.memL2.aestronglyMeasurable.mk u.toFun

/-- A globally strongly measurable representative of `∂ₓu`. -/
def repGxT (u : H1P (thinDomain Cm Cp L R)) : CapSpace m → ℝ :=
  u.gx_memL2.aestronglyMeasurable.mk u.gx

theorem stronglyMeasurable_repFunT (u : H1P (thinDomain Cm Cp L R)) :
    StronglyMeasurable (repFunT u) := u.memL2.aestronglyMeasurable.stronglyMeasurable_mk

theorem stronglyMeasurable_repGxT (u : H1P (thinDomain Cm Cp L R)) :
    StronglyMeasurable (repGxT u) := u.gx_memL2.aestronglyMeasurable.stronglyMeasurable_mk

theorem measurableSet_primRegionFwd_it (x₀ : ℝ) :
    MeasurableSet {r : ℝ × CapSpace m | r.1 ∈ Ioo x₀ r.2.1} := by
  have h1 : IsOpen {r : ℝ × CapSpace m | x₀ < r.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {r : ℝ × CapSpace m | r.1 < r.2.1} :=
    isOpen_lt continuous_fst (continuous_fst.comp continuous_snd)
  exact (h1.inter h2).measurableSet

theorem measurableSet_primRegionBwd_it (x₀ : ℝ) :
    MeasurableSet {r : ℝ × CapSpace m | r.1 ∈ Ioo r.2.1 x₀} := by
  have h1 : IsOpen {r : ℝ × CapSpace m | r.2.1 < r.1} :=
    isOpen_lt (continuous_fst.comp continuous_snd) continuous_fst
  have h2 : IsOpen {r : ℝ × CapSpace m | r.1 < x₀} := isOpen_lt continuous_fst continuous_const
  exact (h1.inter h2).measurableSet

/-- The forward part of the integration kernel of the axial primitive from `x₀`. -/
def primKernelFwd (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ × CapSpace m → ℝ :=
  {r : ℝ × CapSpace m | r.1 ∈ Ioo x₀ r.2.1}.indicator fun r => repGxT u (r.1, r.2.2)

/-- The backward part of the integration kernel of the axial primitive from `x₀`. -/
def primKernelBwd (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) : ℝ × CapSpace m → ℝ :=
  {r : ℝ × CapSpace m | r.1 ∈ Ioo r.2.1 x₀}.indicator fun r => repGxT u (r.1, r.2.2)

/-- The **axial primitive** `p ↦ ∫_{x₀}^{p.1} ∂ₓu(t, p.2) dt`, in a manifestly measurable form. -/
def slicePrim0 (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) : ℝ :=
  (∫ t, primKernelFwd x₀ u (t, p)) - ∫ t, primKernelBwd x₀ u (t, p)

theorem stronglyMeasurable_primKernelFwd_it (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    StronglyMeasurable (primKernelFwd x₀ u) := by
  refine StronglyMeasurable.indicator ?_ (measurableSet_primRegionFwd_it x₀)
  exact (stronglyMeasurable_repGxT u).comp_measurable
    (by fun_prop : Measurable fun r : ℝ × CapSpace m => (r.1, r.2.2))

theorem stronglyMeasurable_primKernelBwd_it (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    StronglyMeasurable (primKernelBwd x₀ u) := by
  refine StronglyMeasurable.indicator ?_ (measurableSet_primRegionBwd_it x₀)
  exact (stronglyMeasurable_repGxT u).comp_measurable
    (by fun_prop : Measurable fun r : ℝ × CapSpace m => (r.1, r.2.2))

theorem stronglyMeasurable_slicePrim0_it (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    StronglyMeasurable (slicePrim0 x₀ u) :=
  ((stronglyMeasurable_primKernelFwd_it x₀ u).integral_prod_left').sub
    ((stronglyMeasurable_primKernelBwd_it x₀ u).integral_prod_left')

/-- The axial primitive really is the interval integral of the representative of `∂ₓu`. -/
theorem slicePrim0_eq_it (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) (x : ℝ)
    (z : EuclideanSpace ℝ (Fin m)) :
    slicePrim0 x₀ u (x, z) = ∫ t in x₀..x, repGxT u (t, z) := by
  have hfwd : (∫ t, primKernelFwd x₀ u (t, (x, z))) = ∫ t in Ioo x₀ x, repGxT u (t, z) := by
    rw [← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [primKernelFwd, Set.indicator_apply, Set.mem_setOf_eq]
  have hbwd : (∫ t, primKernelBwd x₀ u (t, (x, z))) = ∫ t in Ioo x x₀, repGxT u (t, z) := by
    rw [← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [primKernelBwd, Set.indicator_apply, Set.mem_setOf_eq]
  rw [slicePrim0, hfwd, hbwd, intervalIntegral, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

/-- The integrand whose bulk-slice average is the interface value at `x₀`. -/
def ifaceIntegrand (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) : CapSpace m → ℝ :=
  (bulkOpen Cm Cp L R).indicator fun p => repFunT u p - slicePrim0 x₀ u p

/-- **The interface value at `x₀`.**  On almost every axial line through the transverse ball
the function `x ↦ u(x,z) - ∫_{x₀}^{x} ∂ₓu(t,z) dt` is a.e. constant on the bulk interval;
`ifaceVal x₀ u z` is that constant, written as its average over the bulk interval so as to be
manifestly measurable in `z`. -/
def ifaceVal (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R))
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (∫ x, ifaceIntegrand x₀ u (x, z)) / bulkLength Cm Cp L R

/-- **The left interface trace** of a weak-`H¹` function on `Ω_R`: the value of the absolutely
continuous representative of the axial slice at `x₋ = -L/2 + K₋ R`. -/
def ifaceL (u : H1P (thinDomain Cm Cp L R)) : EuclideanSpace ℝ (Fin m) → ℝ :=
  ifaceVal (interfaceL Cm L R) u

/-- **The right interface trace**: the value at `x₊ = L/2 - K₊ R`. -/
def ifaceR (u : H1P (thinDomain Cm Cp L R)) : EuclideanSpace ℝ (Fin m) → ℝ :=
  ifaceVal (interfaceR Cp L R) u

theorem stronglyMeasurable_ifaceIntegrand_it (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    StronglyMeasurable (ifaceIntegrand x₀ u) :=
  ((stronglyMeasurable_repFunT u).sub (stronglyMeasurable_slicePrim0_it x₀ u)).indicator
    measurableSet_bulkOpen

/-- **The interface value is measurable in the transverse variable.** -/
theorem measurable_ifaceVal (x₀ : ℝ) (u : H1P (thinDomain Cm Cp L R)) :
    Measurable (ifaceVal x₀ u) := by
  have h1 : StronglyMeasurable fun z => ∫ x, ifaceIntegrand x₀ u (x, z) :=
    (stronglyMeasurable_ifaceIntegrand_it x₀ u).integral_prod_left'
  exact h1.measurable.div_const _

theorem measurable_ifaceL (u : H1P (thinDomain Cm Cp L R)) : Measurable (ifaceL u) :=
  measurable_ifaceVal _ u

theorem measurable_ifaceR (u : H1P (thinDomain Cm Cp L R)) : Measurable (ifaceR u) :=
  measurable_ifaceVal _ u

/-! ## 4. The defining property of the interface trace -/

/-- Almost every real number avoids a given pair of points. -/
theorem ae_ne_pair_it (c d : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c ∧ t ≠ d := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) (((Set.finite_singleton d).insert c).measure_zero _)
  simp only [mem_setOf_eq, not_and_or, not_not] at ht
  rcases ht with h | h <;> simp [h]

theorem ae_slice_repFunT_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ᵐ x ∂(volume : Measure ℝ),
        (x, z) ∈ thinDomain Cm Cp L R → repFunT u (x, z) = u.toFun (x, z) := by
  refine RobinCaps.Cap.ae_ae_axial
    (Q := fun p => p ∈ thinDomain Cm Cp L R → repFunT u p = u.toFun p) ?_
  have h : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] repFunT u :=
    u.memL2.aestronglyMeasurable.ae_eq_mk
  rw [Filter.EventuallyEq, ae_restrict_iff' (isOpen_thinDomain hR hL).measurableSet] at h
  filter_upwards [h] with p hp hpb using (hp hpb).symm

theorem ae_slice_repGxT_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ᵐ x ∂(volume : Measure ℝ),
        (x, z) ∈ thinDomain Cm Cp L R → repGxT u (x, z) = u.gx (x, z) := by
  refine RobinCaps.Cap.ae_ae_axial
    (Q := fun p => p ∈ thinDomain Cm Cp L R → repGxT u p = u.gx p) ?_
  have h : u.gx =ᵐ[volume.restrict (thinDomain Cm Cp L R)] repGxT u :=
    u.gx_memL2.aestronglyMeasurable.ae_eq_mk
  rw [Filter.EventuallyEq, ae_restrict_iff' (isOpen_thinDomain hR hL).measurableSet] at h
  filter_upwards [h] with p hp hpb using (hp hpb).symm

/-- **The interface constant exists on almost every axial line.** -/
theorem exists_ifaceConst_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (interfaceL Cm L R) (interfaceR Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)), ∃ c : ℝ,
      ∀ᵐ x ∂(volume.restrict (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z))),
        u.toFun (x, z) = c + ∫ t in x₀..x, u.gx (t, z) := by
  filter_upwards [sliceACL_axial_thin hR hL u,
    ae_restrict_of_ae (ae_integrableOn_thin_slice_it hR hL
      (integrableOn_thin_of_memL2_it hR hL u.memL2)),
    ae_restrict_of_ae (ae_integrableOn_thin_slice_it hR hL
      (integrableOn_thin_of_memL2_it hR hL u.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hw hu hg hzb
  have hznorm : ‖z‖ < R := mem_ball_zero_iff.1 hzb
  have hab : aZ Cm Cp L R z < bZ Cm Cp L R z := aZ_lt_bZ_it hR hL hznorm
  obtain ⟨c, hc⟩ := ae_eq_const_add_integral hab hu hg hw
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume
      (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg
  have hII : ∀ y w : ℝ, y ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) →
      w ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) →
      IntervalIntegrable (fun t => u.gx (t, z)) volume y w := by
    intro y w hy hw'
    refine hgI.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le hab.le]; exact hy
    · rw [uIcc_of_le hab.le]; exact hw'
  have hx₀Icc : x₀ ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
    ⟨le_trans (aZ_le_interfaceL_it hR hL hznorm) hx₀.1,
      le_trans hx₀.2 (interfaceR_le_bZ_it hR hL hznorm)⟩
  have hmidIcc : (aZ Cm Cp L R z + bZ Cm Cp L R z) / 2
      ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) := ⟨by linarith, by linarith⟩
  refine ⟨c + ∫ t in ((aZ Cm Cp L R z + bZ Cm Cp L R z) / 2)..x₀, u.gx (t, z), ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with x hs hxmem
  have hs' : u.toFun (x, z)
      = c + ∫ t in ((aZ Cm Cp L R z + bZ Cm Cp L R z) / 2)..x, u.gx (t, z) := hs
  have hxIcc : x ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) := Ioo_subset_Icc_self hxmem
  have hsplit : (∫ t in ((aZ Cm Cp L R z + bZ Cm Cp L R z) / 2)..x, u.gx (t, z))
      = (∫ t in ((aZ Cm Cp L R z + bZ Cm Cp L R z) / 2)..x₀, u.gx (t, z))
        + ∫ t in x₀..x, u.gx (t, z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hII _ x₀ hmidIcc hx₀Icc) (hII x₀ x hx₀Icc hxIcc)).symm
  rw [hs', hsplit]; ring

/-- **Deliverable 1.**  For almost every `z ∈ B_m(R)` the axial slice of `u` is (a.e. equal to)
the absolutely continuous function `x ↦ ifaceVal x₀ u z + ∫_{x₀}^{x} ∂ₓu(t,z) dt` on the whole
axial slice `(aZ z, bZ z)` of `Ω_R`. -/
theorem ifaceVal_spec (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (interfaceL Cm L R) (interfaceR Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ∀ᵐ x ∂(volume.restrict (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z))),
        u.toFun (x, z) = ifaceVal x₀ u z + ∫ t in x₀..x, u.gx (t, z) := by
  have hℓ : 0 < bulkLength Cm Cp L R := bulkLength_pos_it hR hL
  have hmid := interfaceL_lt_interfaceR_it (Cm := Cm) (Cp := Cp) hR hL
  filter_upwards [exists_ifaceConst_it hR hL u hx₀,
    ae_restrict_of_ae (ae_slice_repFunT_it hR hL u),
    ae_restrict_of_ae (ae_slice_repGxT_it hR hL u),
    ae_restrict_mem measurableSet_ball] with z hcz hrf hrg hzb
  obtain ⟨c, hc⟩ := hcz
  have hznorm : ‖z‖ < R := mem_ball_zero_iff.1 hzb
  -- membership of the bulk line in the thin domain
  have hmembulk : ∀ x : ℝ, x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) →
      (x, z) ∈ bulkOpen Cm Cp L R := fun x hx =>
    (mem_bulkOpen_iff (p := (x, z))).2 ⟨⟨hx.1, hx.2⟩, hznorm⟩
  have hmemthin : ∀ x : ℝ, x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) →
      (x, z) ∈ thinDomain Cm Cp L R := fun x hx =>
    bulkOpen_subset_thinDomain hR hL (hmembulk x hx)
  -- the primitive of the representative is the interval integral of `∂ₓu`
  have hprim : ∀ x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R),
      slicePrim0 x₀ u (x, z) = ∫ t in x₀..x, u.gx (t, z) := by
    intro x hx
    rw [slicePrim0_eq_it]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hrg, ae_ne_pair_it (interfaceL Cm L R) (interfaceR Cp L R)]
      with t ht htne htmem
    have htIcc : t ∈ Icc (interfaceL Cm L R) (interfaceR Cp L R) := by
      rw [Set.mem_uIoc] at htmem
      rcases htmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact ⟨by linarith [hx₀.1, hx₀.2, hx.1, hx.2], by linarith [hx₀.1, hx₀.2, hx.1, hx.2]⟩
    exact ht (hmemthin t ⟨lt_of_le_of_ne htIcc.1 (Ne.symm htne.1),
      lt_of_le_of_ne htIcc.2 htne.2⟩)
  -- the integrand is a.e. equal to `c` on the bulk interval
  have hconst : ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      repFunT u (x, z) - slicePrim0 x₀ u (x, z) = c := by
    have hsub : Ioo (interfaceL Cm L R) (interfaceR Cp L R)
        ⊆ Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
      Ioo_interface_subset_axialSlice_it hR hL hznorm
    have hcb : ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
        u.toFun (x, z) = c + ∫ t in x₀..x, u.gx (t, z) :=
      hc.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hcb, ae_restrict_of_ae hrf, ae_restrict_mem measurableSet_Ioo]
      with x hx1 hx2 hx3
    rw [hx2 (hmemthin x hx3), hprim x hx3, hx1]; ring
  -- compute the slice average
  have hind : ∀ x : ℝ, ifaceIntegrand x₀ u (x, z)
      = (Ioo (interfaceL Cm L R) (interfaceR Cp L R)).indicator
          (fun x => repFunT u (x, z) - slicePrim0 x₀ u (x, z)) x := by
    intro x
    by_cases h : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)
    · rw [indicator_of_mem h]
      exact indicator_of_mem (hmembulk x h) _
    · rw [indicator_of_notMem h]
      exact indicator_of_notMem
        (fun hcc => h ((mem_bulkOpen_iff (p := (x, z))).1 hcc).1) _
  have hint : (∫ x, ifaceIntegrand x₀ u (x, z)) = bulkLength Cm Cp L R * c := by
    simp_rw [hind]
    rw [integral_indicator measurableSet_Ioo,
      setIntegral_congr_ae measurableSet_Ioo ((ae_restrict_iff' measurableSet_Ioo).1 hconst),
      setIntegral_const, Real.volume_real_Ioo_of_le hmid.le, smul_eq_mul, bulkLength_eq_sub_it]
  have hval : ifaceVal x₀ u z = c := by
    rw [ifaceVal, hint]
    field_simp
  rw [hval]
  filter_upwards [hc] with x hx using hx

/-- **Deliverable 1, left interface.** -/
theorem ifaceL_spec (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ∀ᵐ x ∂(volume.restrict (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z))),
        u.toFun (x, z) = ifaceL u z + ∫ t in (interfaceL Cm L R)..x, u.gx (t, z) :=
  ifaceVal_spec hR hL u ⟨le_rfl, (interfaceL_lt_interfaceR_it hR hL).le⟩

/-- **Deliverable 1, right interface.** -/
theorem ifaceR_spec (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ∀ᵐ x ∂(volume.restrict (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z))),
        u.toFun (x, z) = ifaceR u z + ∫ t in (interfaceR Cp L R)..x, u.gx (t, z) :=
  ifaceVal_spec hR hL u ⟨(interfaceL_lt_interfaceR_it hR hL).le, le_rfl⟩

/-! ## 5. The absolutely continuous representative of a bulk axial slice -/

/-- Translation invariance of a set integral over an open interval. -/
theorem setIntegral_Ioo_comp_add_right_it {f : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d) (e : ℝ) :
    (∫ y in Ioo c d, f (y + e)) = ∫ x in Ioo (c + e) (d + e), f x := by
  rw [← intervalIntegral_eq_setIntegral_Ioo hcd, intervalIntegral.integral_comp_add_right,
    intervalIntegral_eq_setIntegral_Ioo (by linarith : c + e ≤ d + e)]

/-- **The two interface values differ by the axial flux across the bulk.** -/
theorem ifaceR_eq_ifaceL_add_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ifaceR u z
        = ifaceL u z + ∫ t in (interfaceL Cm L R)..(interfaceR Cp L R), u.gx (t, z) := by
  have hmid := interfaceL_lt_interfaceR_it (Cm := Cm) (Cp := Cp) hR hL
  filter_upwards [ifaceL_spec hR hL u, ifaceR_spec hR hL u,
    ae_restrict_of_ae (ae_integrableOn_thin_slice_it hR hL
      (integrableOn_thin_of_memL2_it hR hL u.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hL' hR' hg hzb
  have hznorm : ‖z‖ < R := mem_ball_zero_iff.1 hzb
  have hab : aZ Cm Cp L R z < bZ Cm Cp L R z := aZ_lt_bZ_it hR hL hznorm
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume
      (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg
  have hII : ∀ y w : ℝ, y ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) →
      w ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) →
      IntervalIntegrable (fun t => u.gx (t, z)) volume y w := by
    intro y w hy hw'
    refine hgI.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le hab.le]; exact hy
    · rw [uIcc_of_le hab.le]; exact hw'
  have hLIcc : interfaceL Cm L R ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
    ⟨aZ_le_interfaceL_it hR hL hznorm,
      le_trans hmid.le (interfaceR_le_bZ_it hR hL hznorm)⟩
  have hRIcc : interfaceR Cp L R ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
    ⟨le_trans (aZ_le_interfaceL_it hR hL hznorm) hmid.le,
      interfaceR_le_bZ_it hR hL hznorm⟩
  have hne : (volume.restrict (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z))) ≠ 0 := by
    intro h
    have h0 : (volume.restrict (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z)))
        (univ : Set ℝ) = 0 := by rw [h]; rfl
    rw [Measure.restrict_apply_univ, Real.volume_Ioo] at h0
    rw [ENNReal.ofReal_eq_zero] at h0
    linarith
  haveI : (ae (volume.restrict (Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z)))).NeBot :=
    ae_neBot.2 hne
  obtain ⟨x, ⟨hx1, hx2⟩, hxmem⟩ :=
    ((hL'.and hR').and (ae_restrict_mem measurableSet_Ioo)).exists
  have hxIcc : x ∈ Icc (aZ Cm Cp L R z) (bZ Cm Cp L R z) := Ioo_subset_Icc_self hxmem
  have hsplit : (∫ t in (interfaceL Cm L R)..x, u.gx (t, z))
      = (∫ t in (interfaceL Cm L R)..(interfaceR Cp L R), u.gx (t, z))
        + ∫ t in (interfaceR Cp L R)..x, u.gx (t, z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hII _ _ hLIcc hRIcc) (hII _ _ hRIcc hxIcc)).symm
  rw [hsplit] at hx1
  linarith [hx1, hx2]

/-- **The absolutely continuous representative of the bulk part of an axial slice.**  For a.e.
`z ∈ B_m(R)` the axial slice of `u`, read on the translated bulk interval `(0, ℓ_R)`, has an
absolutely continuous representative `w ∈ H1 ℓ_R` with `w(0) = ifaceL u z`, `w(ℓ_R) = ifaceR u z`,
and whose mass and Dirichlet energy are the corresponding bulk slice integrals. -/
theorem exists_h1_bulkSlice_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ∃ w : Sobolev.H1 (bulkLength Cm Cp L R),
        w.toFun 0 = ifaceL u z ∧ w.toFun (bulkLength Cm Cp L R) = ifaceR u z ∧
        Sobolev.mass (bulkLength Cm Cp L R) w
          = (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), u.toFun (x, z) ^ 2) ∧
        Sobolev.dirichlet (bulkLength Cm Cp L R) w
          = ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), u.gx (x, z) ^ 2 := by
  have hmid := interfaceL_lt_interfaceR_it (Cm := Cm) (Cp := Cp) hR hL
  have hℓ : 0 < bulkLength Cm Cp L R := bulkLength_pos_it hR hL
  have hℓeq : bulkLength Cm Cp L R = interfaceR Cp L R - interfaceL Cm L R :=
    bulkLength_eq_sub_it
  filter_upwards [ifaceL_spec hR hL u, ifaceR_eq_ifaceL_add_it hR hL u,
    ae_restrict_of_ae (ae_integrableOn_thin_slice_it hR hL
      (integrableOn_thin_of_memL2_it hR hL u.memL2)),
    ae_restrict_of_ae (ae_integrableOn_thin_slice_it hR hL
      (integrableOn_thin_of_memL2_it hR hL u.gx_memL2)),
    ae_restrict_of_ae (ae_integrableOn_thin_slice_it hR hL u.gx_memL2.integrable_sq),
    ae_restrict_mem measurableSet_ball] with z hspec hrel hu hg hg2 hzb
  have hznorm : ‖z‖ < R := mem_ball_zero_iff.1 hzb
  have hsub : Ioo (interfaceL Cm L R) (interfaceR Cp L R)
      ⊆ Ioo (aZ Cm Cp L R z) (bZ Cm Cp L R z) :=
    Ioo_interface_subset_axialSlice_it hR hL hznorm
  -- interval integrability on the (translated) bulk interval
  have hgb : IntervalIntegrable (fun t => u.gx (t, z)) volume
      (interfaceL Cm L R) (interfaceR Cp L R) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le).2 (hg.mono_set hsub)
  have hg2b : IntervalIntegrable (fun t => u.gx (t, z) ^ 2) volume
      (interfaceL Cm L R) (interfaceR Cp L R) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le).2 (hg2.mono_set hsub)
  have hGI : IntervalIntegrable (fun y => u.gx (y + interfaceL Cm L R, z)) volume
      0 (bulkLength Cm Cp L R) := by
    have h := hgb.comp_add_right (interfaceL Cm L R)
    rwa [sub_self, ← hℓeq] at h
  have hG2I : IntervalIntegrable (fun y => u.gx (y + interfaceL Cm L R, z) ^ 2) volume
      0 (bulkLength Cm Cp L R) := by
    have h := hg2b.comp_add_right (interfaceL Cm L R)
    rwa [sub_self, ← hℓeq] at h
  set w : Sobolev.H1 (bulkLength Cm Cp L R) :=
    Sobolev.primitiveH1 hℓ.le hGI hG2I (ifaceL u z) with hwdef
  -- the reconstruction of `w` from the interface value
  have hwval : ∀ y : ℝ, w.toFun y
      = ifaceL u z + ∫ t in (interfaceL Cm L R)..(y + interfaceL Cm L R), u.gx (t, z) := by
    intro y
    rw [hwdef, Sobolev.primitiveH1_toFun]
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := y)
      (f := fun t => u.gx (t, z)) (interfaceL Cm L R)
    rw [zero_add] at h
    show ifaceL u z + ∫ t in (0 : ℝ)..y, u.gx (t + interfaceL Cm L R, z) = _
    rw [h]
  have hw0 : w.toFun 0 = ifaceL u z := by
    rw [hwval, zero_add, intervalIntegral.integral_same, add_zero]
  have hwℓ : w.toFun (bulkLength Cm Cp L R) = ifaceR u z := by
    rw [hwval, hrel, hℓeq]
    ring_nf
  -- `w` represents the axial slice of `u` on the bulk interval
  have hspec' : ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      u.toFun (x, z) = ifaceL u z + ∫ t in (interfaceL Cm L R)..x, u.gx (t, z) :=
    hspec.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hshift : ∀ᵐ y ∂(volume : Measure ℝ),
      (y + interfaceL Cm L R) ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) →
        u.toFun (y + interfaceL Cm L R, z)
          = ifaceL u z + ∫ t in (interfaceL Cm L R)..(y + interfaceL Cm L R), u.gx (t, z) :=
    (measurePreserving_add_right (volume : Measure ℝ) (interfaceL Cm L R)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).1 hspec')
  have hwae : ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) (bulkLength Cm Cp L R))),
      w.toFun y ^ 2 = u.toFun (y + interfaceL Cm L R, z) ^ 2 := by
    filter_upwards [ae_restrict_of_ae hshift, ae_restrict_mem measurableSet_Ioo] with y hy hymem
    have hymem' : (y + interfaceL Cm L R) ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) := by
      constructor
      · linarith [hymem.1]
      · have := hymem.2; rw [hℓeq] at this; linarith
    rw [hwval y, ← hy hymem']
  have hdae : ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) (bulkLength Cm Cp L R))),
      deriv w.toFun y ^ 2 = u.gx (y + interfaceL Cm L R, z) ^ 2 := by
    have hae := Sobolev.ae_deriv_primitive hGI (ifaceL u z) (x₀ := (0 : ℝ)) left_mem_uIcc
    have hsub' : Ioo (0 : ℝ) (bulkLength Cm Cp L R) ⊆ Ι (0 : ℝ) (bulkLength Cm Cp L R) := by
      rw [uIoc_of_le hℓ.le]; exact Ioo_subset_Ioc_self
    have hae' := hae.filter_mono (ae_mono (Measure.restrict_mono hsub' le_rfl))
    filter_upwards [hae'] with y hy
    rw [hwdef, Sobolev.primitiveH1_toFun, hy]
  refine ⟨w, hw0, hwℓ, ?_, ?_⟩
  · rw [Sobolev.mass, intervalIntegral_eq_setIntegral_Ioo hℓ.le,
      setIntegral_congr_ae measurableSet_Ioo ((ae_restrict_iff' measurableSet_Ioo).1 hwae),
      setIntegral_Ioo_comp_add_right_it hℓ.le (f := fun x => u.toFun (x, z) ^ 2), zero_add, hℓeq]
    congr 1
    ring_nf
  · rw [Sobolev.dirichlet, intervalIntegral_eq_setIntegral_Ioo hℓ.le,
      setIntegral_congr_ae measurableSet_Ioo ((ae_restrict_iff' measurableSet_Ioo).1 hdae),
      setIntegral_Ioo_comp_add_right_it hℓ.le (f := fun x => u.gx (x, z) ^ 2), zero_add, hℓeq]
    congr 1
    ring_nf

/-! ## 6. The uniform `L²` bound on the interface traces -/

/-- The closed and the open bulk cylinders agree almost everywhere. -/
theorem bulkCylinder_ae_eq_bulkOpen_it :
    (bulkCylinder Cm Cp L R : Set (CapSpace m)) =ᵐ[volume] bulkOpen Cm Cp L R := by
  rw [ae_eq_set]
  refine ⟨measure_mono_null ?_ (volume_axial_pair_eq_zero (m := m)
    (interfaceL Cm L R) (interfaceR Cp L R)), ?_⟩
  · rintro p ⟨hp, hnot⟩
    obtain ⟨hx, hz⟩ := hp
    by_cases h1 : interfaceL Cm L R < p.1
    · by_cases h2 : p.1 < interfaceR Cp L R
      · exact absurd ((mem_bulkOpen_iff (p := p)).2 ⟨⟨h1, h2⟩, mem_ball_zero_iff.1 hz⟩) hnot
      · exact Or.inr (le_antisymm (by simpa [interfaceR] using hx.2) (not_lt.1 h2))
    · exact Or.inl (le_antisymm (not_lt.1 h1) (by simpa [interfaceL] using hx.1))
  · rw [Set.diff_eq_empty.2 bulkOpen_subset_bulkCylinder, measure_empty]

/-- Integration over the closed bulk cylinder is integration over the open one. -/
theorem setIntegral_bulkCylinder_it (f : CapSpace m → ℝ) :
    (∫ p in bulkCylinder Cm Cp L R, f p) = ∫ p in bulkOpen Cm Cp L R, f p :=
  setIntegral_congr_set bulkCylinder_ae_eq_bulkOpen_it

/-- The bulk slice integrals form an integrable function of the transverse variable. -/
theorem integrableOn_bulkSliceIntegral_it {f : CapSpace m → ℝ}
    (hf : IntegrableOn f (bulkOpen Cm Cp L R) volume) :
    IntegrableOn (fun z => ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), f (x, z))
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) volume := by
  rw [IntegrableOn, bulkOpen_eq_prod_it, restrict_prodDomain] at hf
  have h := hf.swap.integral_prod_left
  simpa [Function.comp_def] using h

/-- **Fubini on the bulk cylinder**, in the order `z` outer, `x` inner. -/
theorem integral_bulkOpen_eq_slices_it {f : CapSpace m → ℝ}
    (hf : IntegrableOn f (bulkOpen Cm Cp L R) volume) :
    (∫ p in bulkOpen Cm Cp L R, f p)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R,
          ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), f (x, z) := by
  rw [IntegrableOn, bulkOpen_eq_prod_it, restrict_prodDomain] at hf
  rw [bulkOpen_eq_prod_it, restrict_prodDomain, integral_prod_symm _ hf]

/-- **The slice trace bound at the left interface.** -/
theorem ae_ifaceL_sq_le_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ifaceL u z ^ 2
        ≤ (2 / bulkLength Cm Cp L R)
            * (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), u.toFun (x, z) ^ 2)
          + (2 * bulkLength Cm Cp L R)
            * ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), u.gx (x, z) ^ 2 := by
  have hℓ : 0 < bulkLength Cm Cp L R := bulkLength_pos_it hR hL
  filter_upwards [exists_h1_bulkSlice_it hR hL u] with z hz
  obtain ⟨w, hw0, -, hmass, hdir⟩ := hz
  have h := Sobolev.endpoint_zero_sq_le w hℓ
  rw [hw0, hmass, hdir] at h
  exact h

/-- **The slice trace bound at the right interface.** -/
theorem ae_ifaceR_sq_le_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)),
      ifaceR u z ^ 2
        ≤ (2 / bulkLength Cm Cp L R)
            * (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), u.toFun (x, z) ^ 2)
          + (2 * bulkLength Cm Cp L R)
            * ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), u.gx (x, z) ^ 2 := by
  have hℓ : 0 < bulkLength Cm Cp L R := bulkLength_pos_it hR hL
  filter_upwards [exists_h1_bulkSlice_it hR hL u] with z hz
  obtain ⟨w, -, hwℓ, hmass, hdir⟩ := hz
  have h := Sobolev.endpoint_ell_sq_le w hℓ
  rw [hwℓ, hmass, hdir] at h
  exact h

/-- The bulk mass slice function. -/
private theorem integrableOn_bulkMassSlice_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z => ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
        u.toFun (x, z) ^ 2) (ball (0 : EuclideanSpace ℝ (Fin m)) R) volume :=
  integrableOn_bulkSliceIntegral_it
    (IntegrableOn.mono_set u.memL2.integrable_sq (bulkOpen_subset_thinDomain hR hL))

private theorem integrableOn_bulkEnergySlice_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z => ∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
        u.gx (x, z) ^ 2) (ball (0 : EuclideanSpace ℝ (Fin m)) R) volume :=
  integrableOn_bulkSliceIntegral_it
    (IntegrableOn.mono_set u.gx_memL2.integrable_sq (bulkOpen_subset_thinDomain hR hL))

/-- **The interface trace is square integrable on the transverse ball** (left interface). -/
theorem integrableOn_ifaceL_sq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z => ifaceL u z ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) volume := by
  refine Integrable.mono'
    (((integrableOn_bulkMassSlice_it hR hL u).const_mul (2 / bulkLength Cm Cp L R)).add
      ((integrableOn_bulkEnergySlice_it hR hL u).const_mul (2 * bulkLength Cm Cp L R)))
    (((measurable_ifaceL u).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_ifaceL_sq_le_it hR hL u] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hz

/-- **The interface trace is square integrable on the transverse ball** (right interface). -/
theorem integrableOn_ifaceR_sq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z => ifaceR u z ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) R) volume := by
  refine Integrable.mono'
    (((integrableOn_bulkMassSlice_it hR hL u).const_mul (2 / bulkLength Cm Cp L R)).add
      ((integrableOn_bulkEnergySlice_it hR hL u).const_mul (2 * bulkLength Cm Cp L R)))
    (((measurable_ifaceR u).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_ifaceR_sq_le_it hR hL u] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hz

/-- **Deliverable 2, left interface.**  The `L²(B_m(R))` bound on the interface trace, with the
explicit constants of the one-dimensional trace inequality on an interval of length
`ℓ_R = bulkLength Cm Cp L R` — uniform in `R` as soon as `ℓ_R` is. -/
theorem integral_ifaceL_sq_le (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceL u z ^ 2)
      ≤ (2 / bulkLength Cm Cp L R) * (∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2)
        + (2 * bulkLength Cm Cp L R) * ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 := by
  have hb1 := integrableOn_bulkMassSlice_it hR hL u
  have hb2 := integrableOn_bulkEnergySlice_it hR hL u
  have hstep := integral_mono_ae (integrableOn_ifaceL_sq hR hL u)
    ((hb1.const_mul (2 / bulkLength Cm Cp L R)).add
      (hb2.const_mul (2 * bulkLength Cm Cp L R)))
    (ae_ifaceL_sq_le_it hR hL u)
  simp only [Pi.add_apply] at hstep
  rw [integral_add (hb1.const_mul _) (hb2.const_mul _),
    integral_const_mul, integral_const_mul] at hstep
  rw [setIntegral_bulkCylinder_it, setIntegral_bulkCylinder_it,
    integral_bulkOpen_eq_slices_it
      (IntegrableOn.mono_set u.memL2.integrable_sq (bulkOpen_subset_thinDomain hR hL)),
    integral_bulkOpen_eq_slices_it
      (IntegrableOn.mono_set u.gx_memL2.integrable_sq (bulkOpen_subset_thinDomain hR hL))]
  exact hstep

/-- **Deliverable 2, right interface.** -/
theorem integral_ifaceR_sq_le (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceR u z ^ 2)
      ≤ (2 / bulkLength Cm Cp L R) * (∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2)
        + (2 * bulkLength Cm Cp L R) * ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 := by
  have hb1 := integrableOn_bulkMassSlice_it hR hL u
  have hb2 := integrableOn_bulkEnergySlice_it hR hL u
  have hstep := integral_mono_ae (integrableOn_ifaceR_sq hR hL u)
    ((hb1.const_mul (2 / bulkLength Cm Cp L R)).add
      (hb2.const_mul (2 * bulkLength Cm Cp L R)))
    (ae_ifaceR_sq_le_it hR hL u)
  simp only [Pi.add_apply] at hstep
  rw [integral_add (hb1.const_mul _) (hb2.const_mul _),
    integral_const_mul, integral_const_mul] at hstep
  rw [setIntegral_bulkCylinder_it, setIntegral_bulkCylinder_it,
    integral_bulkOpen_eq_slices_it
      (IntegrableOn.mono_set u.memL2.integrable_sq (bulkOpen_subset_thinDomain hR hL)),
    integral_bulkOpen_eq_slices_it
      (IntegrableOn.mono_set u.gx_memL2.integrable_sq (bulkOpen_subset_thinDomain hR hL))]
  exact hstep

/-- **Deliverable 2, single-constant phrasing.**  With
`C_ℓ = max (2/ℓ_R) (2 ℓ_R)` the interface trace obeys
`‖Tr u‖²_{L²(B_m(R))} ≤ C_ℓ (‖u‖²_{L²(Ω_b)} + ‖∂ₓu‖²_{L²(Ω_b)})`. -/
theorem integral_ifaceL_sq_le' (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceL u z ^ 2)
      ≤ max (2 / bulkLength Cm Cp L R) (2 * bulkLength Cm Cp L R)
        * ((∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2)
          + ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2) := by
  have hM : 0 ≤ ∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2 :=
    integral_nonneg fun p => sq_nonneg _
  have hG : 0 ≤ ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2 :=
    integral_nonneg fun p => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_right
    (le_max_left (2 / bulkLength Cm Cp L R) (2 * bulkLength Cm Cp L R)) hM
  have h2 := mul_le_mul_of_nonneg_right
    (le_max_right (2 / bulkLength Cm Cp L R) (2 * bulkLength Cm Cp L R)) hG
  have h3 := integral_ifaceL_sq_le hR hL u
  nlinarith [h1, h2, h3]

/-! ## 7. Identification with the cap entrance trace -/

/-- The axial component of the left-cap rescaling: `s ↦ -L/2 - R s`, which carries the cap
entrance `s = -K₋` to the left interface `x₋` and the tip `s = 0` to `-L/2`. -/
theorem capLine_neg_K_it (Cm : RobinCaps.Cap m) (L R : ℝ) :
    -L / 2 - R * (-Cm.K) = interfaceL Cm L R := by
  simp only [interfaceL]; ring

theorem quasiMeasurePreserving_mulLeft_it {a : ℝ} (ha : a ≠ 0) :
    Measure.QuasiMeasurePreserving (fun s : ℝ => a * s) volume volume := by
  refine ⟨by fun_prop, Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_⟩
  rw [Measure.map_apply (by fun_prop) hS, Real.volume_preimage_mul_left ha, hS0, mul_zero]

theorem quasiMeasurePreserving_capLine_it (hR : 0 < R) (L : ℝ) :
    Measure.QuasiMeasurePreserving (fun s : ℝ => -L / 2 - R * s) volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun s : ℝ => (-R) * s) volume volume :=
    quasiMeasurePreserving_mulLeft_it (neg_ne_zero.2 hR.ne')
  have h2 : Measure.QuasiMeasurePreserving (fun y : ℝ => -L / 2 + y) volume volume :=
    (measurePreserving_add_left (volume : Measure ℝ) (-L / 2)).quasiMeasurePreserving
  have heq : (fun s : ℝ => -L / 2 - R * s)
      = (fun y : ℝ => -L / 2 + y) ∘ (fun s : ℝ => (-R) * s) := by
    funext s; simp only [Function.comp_apply]; ring
  rw [heq]
  exact h2.comp h1

@[simp] theorem capLeft_toFun_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) :
    (capLeft hR hL c u).toFun p = c * u.toFun (-L / 2 - R * p.1, R • p.2) := by
  have h : (capLeft hR hL c u).toFun p = c * u.toFun (affP (-L / 2) (-1) R p) := by
    simp [capLeft, H1P.rescaleLeft]
  rw [h]
  congr 2
  simp only [affP, Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  trivial

@[simp] theorem capLeft_gx_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) :
    (capLeft hR hL c u).gx p = -(c * R) * u.gx (-L / 2 - R * p.1, R • p.2) := by
  have h : (capLeft hR hL c u).gx p = c * ((-1 : ℝ) * R * u.gx (affP (-L / 2) (-1) R p)) := by
    simp [capLeft, H1P.rescaleLeft]
  rw [h]
  have hp : affP (-L / 2) (-1) R p = (-L / 2 - R * p.1, R • p.2) := by
    simp only [affP, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    trivial
  rw [hp]
  ring

theorem quasiMeasurePreserving_smul_it (hR : 0 < R) :
    Measure.QuasiMeasurePreserving
      (fun z' : EuclideanSpace ℝ (Fin m) => R • z') volume volume := by
  refine ⟨by fun_prop, Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_⟩
  rw [Measure.map_apply (by fun_prop) hS,
    Measure.addHaar_preimage_smul (volume : Measure (EuclideanSpace ℝ (Fin m))) hR.ne' S,
    hS0, mul_zero]

/-- Transport of an a.e. statement on `B_m(R)` to `B_m(1)` along the scaling `z' ↦ R z'`. -/
theorem ae_ball_smul_it (hR : 0 < R) {P : EuclideanSpace ℝ (Fin m) → Prop}
    (h : ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) R)), P z) :
    ∀ᵐ z' ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)), P (R • z') := by
  have h' : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R → P z :=
    (ae_restrict_iff' measurableSet_ball).1 h
  have h'' := (quasiMeasurePreserving_smul_it (m := m) hR).ae h'
  filter_upwards [ae_restrict_of_ae h'', ae_restrict_mem measurableSet_ball] with z' hz' hz'b
  refine hz' (mem_ball_zero_iff.2 ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  nlinarith [mem_ball_zero_iff.1 hz'b, norm_nonneg z']

/-- **Deliverable 3.**  The cap entrance trace of the left-cap component of a thin-domain
function is (up to the rescaling constant `c`) the left interface trace, read at `z = R z'`. -/
theorem entranceVal_capLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z' ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      Cap.entranceVal Cm (capLeft hR hL c u) z' = c * ifaceL u (R • z') := by
  filter_upwards [Cap.entranceVal_spec Cm (capLeft hR hL c u),
    ae_ball_smul_it hR (ifaceL_spec hR hL u),
    ae_restrict_mem measurableSet_ball] with z' hA hB hz'b
  have hz'n : ‖z'‖ < 1 := mem_ball_zero_iff.1 hz'b
  have hKe : -Cm.K < Cap.exitTime Cm z' := (Cap.exitTime_mem Cm hz'n).1
  -- the cap axial line lands inside the axial slice of the thin domain
  have hline : ∀ s ∈ Ioo (-Cm.K) (Cap.exitTime Cm z'),
      (-L / 2 - R * s) ∈ Ioo (aZ Cm Cp L R (R • z')) (bZ Cm Cp L R (R • z')) := by
    intro s hs
    have hbody : ((s, z') : CapSpace m) ∈ Cm.body := by
      have hmem : s ∈ Cap.axialSlice Cm z' := by rw [Cap.axialSlice_eq]; exact hs
      exact hmem
    have himg : ((-L / 2 - R * s, R • z') : CapSpace m) ∈ leftCap Cm L R := by
      rw [leftCap_eq_image]
      refine ⟨(s, z'), hbody, ?_⟩
      simp only [affP, Prod.mk.injEq]
      refine ⟨by ring, ?_⟩
      trivial
    have hthin := leftCap_subset_thinDomain hR hL himg
    rw [← thinDomain_axialSlice hR hL]
    exact hthin
  -- change of variables in the entrance integral
  have hcov : ∀ s : ℝ, (∫ t in (-Cm.K)..s, (capLeft hR hL c u).gx (t, z'))
      = c * ∫ x in (interfaceL Cm L R)..(-L / 2 - R * s), u.gx (x, R • z') := by
    intro s
    have h1 : (∫ t in (-Cm.K)..s, (capLeft hR hL c u).gx (t, z'))
        = -(c * R) * ∫ t in (-Cm.K)..s, u.gx (-L / 2 - R * t, R • z') := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => capLeft_gx_it hR hL c u (t, z')
    rw [h1, intervalIntegral.integral_comp_sub_mul (fun x => u.gx (x, R • z')) hR.ne' (-L / 2),
      smul_eq_mul, capLine_neg_K_it,
      intervalIntegral.integral_symm (interfaceL Cm L R) (-L / 2 - R * s)]
    field_simp
  -- transport of the interface identity along the (affine) cap line
  have hB' : ∀ᵐ s ∂(volume : Measure ℝ),
      (-L / 2 - R * s) ∈ Ioo (aZ Cm Cp L R (R • z')) (bZ Cm Cp L R (R • z')) →
        u.toFun (-L / 2 - R * s, R • z') = ifaceL u (R • z')
          + ∫ t in (interfaceL Cm L R)..(-L / 2 - R * s), u.gx (t, R • z') :=
    (quasiMeasurePreserving_capLine_it hR L).ae ((ae_restrict_iff' measurableSet_Ioo).1 hB)
  -- a common point of the cap axial slice
  have hne : (volume.restrict (Ioo (-Cm.K) (Cap.exitTime Cm z'))) ≠ 0 := by
    intro h
    have h0 : (volume.restrict (Ioo (-Cm.K) (Cap.exitTime Cm z'))) (univ : Set ℝ) = 0 := by
      rw [h]; rfl
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    linarith
  haveI : (ae (volume.restrict (Ioo (-Cm.K) (Cap.exitTime Cm z')))).NeBot := ae_neBot.2 hne
  obtain ⟨s, ⟨hAs, hBs⟩, hsmem⟩ :=
    ((hA.and (ae_restrict_of_ae hB')).and (ae_restrict_mem measurableSet_Ioo)).exists
  have hBs' := hBs (hline s hsmem)
  have hLHS : (capLeft hR hL c u).toFun (s, z') = c * u.toFun (-L / 2 - R * s, R • z') :=
    capLeft_toFun_it hR hL c u (s, z')
  rw [hLHS, hcov s, hBs'] at hAs
  linarith

/-! ## 8. The hypothesis `hev` of `axial_poincare_weak`, discharged -/

theorem indicator_ball_smul_it (hR : 0 < R) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (z' : EuclideanSpace ℝ (Fin m)) :
    (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator h (R • z')
      = (ball (0 : EuclideanSpace ℝ (Fin m)) 1).indicator (fun w => h (R • w)) z' := by
  have hiff : R • z' ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R
      ↔ z' ∈ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact ⟨fun h1 => (mul_lt_iff_lt_one_right hR).1 h1, fun h1 => mul_lt_of_lt_one_right hR h1⟩
  by_cases hz : z' ∈ ball (0 : EuclideanSpace ℝ (Fin m)) 1
  · rw [indicator_of_mem (hiff.2 hz), indicator_of_mem hz]
  · rw [indicator_of_notMem (fun hc => hz (hiff.1 hc)), indicator_of_notMem hz]

/-- The scaled interface trace is square integrable on the unit ball. -/
theorem integrableOn_ifaceL_smul_sq_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z' => ifaceL u (R • z') ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  have hF : Integrable ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator
      (fun z => ifaceL u z ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_ifaceL_sq hR hL u)
  have hFs := hF.comp_smul (R := R) hR.ne'
  refine (integrable_indicator_iff measurableSet_ball).1 ?_
  exact hFs.congr (Eventually.of_forall fun z' => indicator_ball_smul_it hR _ z')

/-- The scaling of the interface `L²` norm under `z = R z'`. -/
theorem integral_ifaceL_smul_sq_it (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ifaceL u (R • z') ^ 2)
      = (R ^ m)⁻¹ * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceL u z ^ 2 := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  have h := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin m)))
    ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator (fun z => ifaceL u z ^ 2)) R
  rw [hdim, smul_eq_mul] at h
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  rw [show (∫ z', (ball (0 : EuclideanSpace ℝ (Fin m)) 1).indicator
        (fun w => ifaceL u (R • w) ^ 2) z')
      = ∫ z', (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator
        (fun z => ifaceL u z ^ 2) (R • z') from
    integral_congr_ae (Eventually.of_forall fun z' => by
      simpa using (indicator_ball_smul_it hR (fun z => ifaceL u z ^ 2) z').symm)]
  rw [h, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (R ^ m)⁻¹)]

/-- **Deliverable 4 (integrability).**  The entrance trace of the left-cap component of a
thin-domain function is square integrable on the entrance disk — this is exactly the
hypothesis `hev` of `RobinCaps.Cap.axial_poincare_weak`. -/
theorem integrableOn_entranceVal_sq_capLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z' => Cap.entranceVal Cm (capLeft hR hL c u) z' ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  refine ((integrableOn_ifaceL_smul_sq_it hR hL u).const_mul (c ^ 2)).congr ?_
  filter_upwards [entranceVal_capLeft hR hL c u] with z' hz'
  rw [hz', mul_pow]

/-- **The `L²` norm of the cap entrance trace in terms of the bulk.** -/
theorem integral_entranceVal_sq_capLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        Cap.entranceVal Cm (capLeft hR hL c u) z' ^ 2)
      = c ^ 2 * (R ^ m)⁻¹
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceL u z ^ 2 := by
  have h1 : (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        Cap.entranceVal Cm (capLeft hR hL c u) z' ^ 2)
      = ∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1, c ^ 2 * ifaceL u (R • z') ^ 2 := by
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (entranceVal_capLeft hR hL c u)]
      with z' hz' hz'b
    rw [hz' hz'b, mul_pow]
  rw [h1, integral_const_mul, integral_ifaceL_smul_sq_it hR u, mul_assoc]

/-- **Deliverable 4 (the bulk bound on the cap entrance trace).** -/
theorem integral_entranceVal_sq_capLeft_le (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        Cap.entranceVal Cm (capLeft hR hL c u) z' ^ 2)
      ≤ c ^ 2 * (R ^ m)⁻¹
        * ((2 / bulkLength Cm Cp L R) * (∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2)
          + (2 * bulkLength Cm Cp L R) * ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2) := by
  rw [integral_entranceVal_sq_capLeft hR hL c u]
  exact mul_le_mul_of_nonneg_left (integral_ifaceL_sq_le hR hL u)
    (by positivity)

/-- **Deliverable 4 (the axial Poincaré inequality on the left cap).**  The hypothesis `hev` of
`RobinCaps.Cap.axial_poincare_weak` is now available for the cap components of a thin-domain
function, so the cap Poincaré inequality holds unconditionally for them. -/
theorem axial_poincare_capLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP (capLeft hR hL c u)
      ≤ 2 * Cm.K * (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          Cap.entranceVal Cm (capLeft hR hL c u) z' ^ 2)
        + 2 * Cm.K ^ 2 * ∫ p in Cm.body, (capLeft hR hL c u).gx p ^ 2 :=
  Cap.axial_poincare_weak Cm (capLeft hR hL c u)
    (integrableOn_entranceVal_sq_capLeft hR hL c u)

/-! ## 9. The same for the right cap -/

theorem quasiMeasurePreserving_affLine_it {a b : ℝ} (ha : a ≠ 0) :
    Measure.QuasiMeasurePreserving (fun s : ℝ => a * s + b) volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun s : ℝ => a * s) volume volume :=
    quasiMeasurePreserving_mulLeft_it ha
  have h2 : Measure.QuasiMeasurePreserving (fun y : ℝ => b + y) volume volume :=
    (measurePreserving_add_left (volume : Measure ℝ) b).quasiMeasurePreserving
  have heq : (fun s : ℝ => a * s + b) = (fun y : ℝ => b + y) ∘ (fun s : ℝ => a * s) := by
    funext s; simp only [Function.comp_apply]; ring
  rw [heq]
  exact h2.comp h1

/-- The axial component of the right-cap rescaling carries the entrance `s = -K₊` to `x₊`. -/
theorem capLine_neg_K_right_it (Cp : RobinCaps.Cap m) (L R : ℝ) :
    R * (-Cp.K) + L / 2 = interfaceR Cp L R := by
  simp only [interfaceR]; ring

@[simp] theorem capRight_toFun_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) :
    (capRight hR hL c u).toFun p = c * u.toFun (R * p.1 + L / 2, R • p.2) := by
  have h : (capRight hR hL c u).toFun p = c * u.toFun (affP (L / 2) 1 R p) := by
    simp [capRight, H1P.rescaleRight]
  rw [h]
  congr 2
  simp only [affP, Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  trivial

@[simp] theorem capRight_gx_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) :
    (capRight hR hL c u).gx p = (c * R) * u.gx (R * p.1 + L / 2, R • p.2) := by
  have h : (capRight hR hL c u).gx p
      = c * ((1 : ℝ) * R * u.gx (affP (L / 2) 1 R p)) := by
    simp [capRight, H1P.rescaleRight]
  rw [h]
  have hp : affP (L / 2) 1 R p = (R * p.1 + L / 2, R • p.2) := by
    simp only [affP, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    trivial
  rw [hp]
  ring

/-- **Deliverable 3, right cap.** -/
theorem entranceVal_capRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ z' ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      Cap.entranceVal Cp (capRight hR hL c u) z' = c * ifaceR u (R • z') := by
  filter_upwards [Cap.entranceVal_spec Cp (capRight hR hL c u),
    ae_ball_smul_it hR (ifaceR_spec hR hL u),
    ae_restrict_mem measurableSet_ball] with z' hA hB hz'b
  have hz'n : ‖z'‖ < 1 := mem_ball_zero_iff.1 hz'b
  have hKe : -Cp.K < Cap.exitTime Cp z' := (Cap.exitTime_mem Cp hz'n).1
  have hline : ∀ s ∈ Ioo (-Cp.K) (Cap.exitTime Cp z'),
      (R * s + L / 2) ∈ Ioo (aZ Cm Cp L R (R • z')) (bZ Cm Cp L R (R • z')) := by
    intro s hs
    have hbody : ((s, z') : CapSpace m) ∈ Cp.body := by
      have hmem : s ∈ Cap.axialSlice Cp z' := by rw [Cap.axialSlice_eq]; exact hs
      exact hmem
    have himg : ((R * s + L / 2, R • z') : CapSpace m) ∈ rightCap Cp L R := by
      rw [rightCap_eq_image]
      refine ⟨(s, z'), hbody, ?_⟩
      simp only [affP, Prod.mk.injEq]
      refine ⟨by ring, ?_⟩
      trivial
    have hthin := rightCap_subset_thinDomain hR hL himg
    rw [← thinDomain_axialSlice hR hL]
    exact hthin
  have hcov : ∀ s : ℝ, (∫ t in (-Cp.K)..s, (capRight hR hL c u).gx (t, z'))
      = c * ∫ x in (interfaceR Cp L R)..(R * s + L / 2), u.gx (x, R • z') := by
    intro s
    have h1 : (∫ t in (-Cp.K)..s, (capRight hR hL c u).gx (t, z'))
        = (c * R) * ∫ t in (-Cp.K)..s, u.gx (R * t + L / 2, R • z') := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => capRight_gx_it hR hL c u (t, z')
    rw [h1, intervalIntegral.integral_comp_mul_add (fun x => u.gx (x, R • z')) hR.ne' (L / 2),
      smul_eq_mul, capLine_neg_K_right_it]
    field_simp
  have hB' : ∀ᵐ s ∂(volume : Measure ℝ),
      (R * s + L / 2) ∈ Ioo (aZ Cm Cp L R (R • z')) (bZ Cm Cp L R (R • z')) →
        u.toFun (R * s + L / 2, R • z') = ifaceR u (R • z')
          + ∫ t in (interfaceR Cp L R)..(R * s + L / 2), u.gx (t, R • z') :=
    (quasiMeasurePreserving_affLine_it hR.ne').ae
      ((ae_restrict_iff' measurableSet_Ioo).1 hB)
  have hne : (volume.restrict (Ioo (-Cp.K) (Cap.exitTime Cp z'))) ≠ 0 := by
    intro h
    have h0 : (volume.restrict (Ioo (-Cp.K) (Cap.exitTime Cp z'))) (univ : Set ℝ) = 0 := by
      rw [h]; rfl
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    linarith
  haveI : (ae (volume.restrict (Ioo (-Cp.K) (Cap.exitTime Cp z')))).NeBot := ae_neBot.2 hne
  obtain ⟨s, ⟨hAs, hBs⟩, hsmem⟩ :=
    ((hA.and (ae_restrict_of_ae hB')).and (ae_restrict_mem measurableSet_Ioo)).exists
  have hBs' := hBs (hline s hsmem)
  have hLHS : (capRight hR hL c u).toFun (s, z') = c * u.toFun (R * s + L / 2, R • z') :=
    capRight_toFun_it hR hL c u (s, z')
  rw [hLHS, hcov s, hBs'] at hAs
  linarith

theorem integrableOn_ifaceR_smul_sq_it (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z' => ifaceR u (R • z') ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  have hF : Integrable ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator
      (fun z => ifaceR u z ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_ifaceR_sq hR hL u)
  have hFs := hF.comp_smul (R := R) hR.ne'
  refine (integrable_indicator_iff measurableSet_ball).1 ?_
  exact hFs.congr (Eventually.of_forall fun z' => indicator_ball_smul_it hR _ z')

theorem integral_ifaceR_smul_sq_it (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ifaceR u (R • z') ^ 2)
      = (R ^ m)⁻¹ * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceR u z ^ 2 := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  have h := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin m)))
    ((ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator (fun z => ifaceR u z ^ 2)) R
  rw [hdim, smul_eq_mul] at h
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  rw [show (∫ z', (ball (0 : EuclideanSpace ℝ (Fin m)) 1).indicator
        (fun w => ifaceR u (R • w) ^ 2) z')
      = ∫ z', (ball (0 : EuclideanSpace ℝ (Fin m)) R).indicator
        (fun z => ifaceR u z ^ 2) (R • z') from
    integral_congr_ae (Eventually.of_forall fun z' => by
      simpa using (indicator_ball_smul_it hR (fun z => ifaceR u z ^ 2) z').symm)]
  rw [h, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (R ^ m)⁻¹)]

/-- **Deliverable 4 (integrability), right cap.** -/
theorem integrableOn_entranceVal_sq_capRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (fun z' => Cap.entranceVal Cp (capRight hR hL c u) z' ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  refine ((integrableOn_ifaceR_smul_sq_it hR hL u).const_mul (c ^ 2)).congr ?_
  filter_upwards [entranceVal_capRight hR hL c u] with z' hz'
  rw [hz', mul_pow]

/-- **The `L²` norm of the right-cap entrance trace in terms of the bulk.** -/
theorem integral_entranceVal_sq_capRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        Cap.entranceVal Cp (capRight hR hL c u) z' ^ 2)
      = c ^ 2 * (R ^ m)⁻¹
        * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, ifaceR u z ^ 2 := by
  have h1 : (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        Cap.entranceVal Cp (capRight hR hL c u) z' ^ 2)
      = ∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1, c ^ 2 * ifaceR u (R • z') ^ 2 := by
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (entranceVal_capRight hR hL c u)]
      with z' hz' hz'b
    rw [hz' hz'b, mul_pow]
  rw [h1, integral_const_mul, integral_ifaceR_smul_sq_it hR u, mul_assoc]

/-- **Deliverable 4 (the bulk bound on the right-cap entrance trace).** -/
theorem integral_entranceVal_sq_capRight_le (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        Cap.entranceVal Cp (capRight hR hL c u) z' ^ 2)
      ≤ c ^ 2 * (R ^ m)⁻¹
        * ((2 / bulkLength Cm Cp L R) * (∫ p in bulkCylinder Cm Cp L R, u.toFun p ^ 2)
          + (2 * bulkLength Cm Cp L R) * ∫ p in bulkCylinder Cm Cp L R, u.gx p ^ 2) := by
  rw [integral_entranceVal_sq_capRight hR hL c u]
  exact mul_le_mul_of_nonneg_left (integral_ifaceR_sq_le hR hL u) (by positivity)

/-- **Deliverable 4 (the axial Poincaré inequality on the right cap).** -/
theorem axial_poincare_capRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP (capRight hR hL c u)
      ≤ 2 * Cp.K * (∫ z' in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          Cap.entranceVal Cp (capRight hR hL c u) z' ^ 2)
        + 2 * Cp.K ^ 2 * ∫ p in Cp.body, (capRight hR hL c u).gx p ^ 2 :=
  Cap.axial_poincare_weak Cp (capRight hR hL c u)
    (integrableOn_entranceVal_sq_capRight hR hL c u)

end

end RobinCaps.ThinDomain
