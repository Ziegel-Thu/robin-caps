import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.SliceAC
import RobinCaps.Cap.EntranceL2Flat
import RobinCaps.ThinDomain.TraceGenBulk

/-!
# The trace datum of the flat cap

This file constructs `CapTraceData (Cap.flat m K hK)` (`RobinCaps/Cap/LowerWeak.lean`) for the
**flat cap** `θ ≡ 1`, whose body is the cylinder `(-K,0) × B_m(1)`, for every `m ≥ 1`, `K > 0`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology Interval

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

/-! ## 1. The flat cap body as a cylinder -/

/-- The body of the flat cap is the literal product `(-K,0) × B_m(1)`, i.e. the bulk cylinder. -/
theorem flatBody_eq_bulkCyl_tf (m : ℕ) (K : ℝ) (hK : 0 < K) :
    (Cap.flat m K hK).body = bulkCyl (-K) 0 m 1 := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [flat_theta_elf] at h3
    exact ⟨⟨h1, h2⟩, by simpa [transverseBall, Metric.mem_ball, dist_eq_norm] using h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [flat_theta_elf]
    simpa [transverseBall, Metric.mem_ball, dist_eq_norm] using h3

/-- **Transport of `u : H1P (flat).body` to the bulk cylinder.** -/
def toCyl_tf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    H1P (bulkCyl (-K) 0 m 1) :=
  u.restrictTo (flatBody_eq_bulkCyl_tf m K hK).symm.subset

@[simp] theorem toCyl_tf_toFun (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) : (toCyl_tf m K hK u).toFun = u.toFun := rfl

@[simp] theorem toCyl_tf_gx (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) : (toCyl_tf m K hK u).gx = u.gx := rfl

@[simp] theorem toCyl_tf_gz (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) : (toCyl_tf m K hK u).gz = u.gz := rfl

theorem toCyl_tf_add (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u v : H1P (Cap.flat m K hK).body) :
    toCyl_tf m K hK (u + v) = toCyl_tf m K hK u + toCyl_tf m K hK v :=
  H1P.ext rfl rfl rfl

theorem toCyl_tf_smul (m : ℕ) (K : ℝ) (hK : 0 < K) (c : ℝ)
    (u : H1P (Cap.flat m K hK).body) :
    toCyl_tf m K hK (c • u) = c • toCyl_tf m K hK u :=
  H1P.ext rfl rfl rfl

theorem massP_toCyl_tf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    massP (toCyl_tf m K hK u) = massP u := by
  have h : (volume : Measure (CapSpace m)).restrict (bulkCyl (-K) 0 m 1)
      = (volume : Measure (CapSpace m)).restrict (Cap.flat m K hK).body := by
    rw [flatBody_eq_bulkCyl_tf m K hK]
  simp only [massP, toCyl_tf_toFun]
  exact congrArg (fun μ => ∫ p, u.toFun p ^ 2 ∂μ) h

theorem dirichletP_toCyl_tf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    dirichletP (toCyl_tf m K hK u) = dirichletP u := by
  have h : (volume : Measure (CapSpace m)).restrict (bulkCyl (-K) 0 m 1)
      = (volume : Measure (CapSpace m)).restrict (Cap.flat m K hK).body := by
    rw [flatBody_eq_bulkCyl_tf m K hK]
  simp only [dirichletP, toCyl_tf_gx, toCyl_tf_gz]
  exact congrArg (fun μ => ∫ p, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2) ∂μ) h

/-! ## 2. The terminal-disc trace

This mirrors `RobinCaps.Cap.entranceVal` (`RobinCaps/Cap/SliceAC.lean`), but anchored at the
**exit point `s = 0`** instead of the entrance `s = -K`: the axial primitive of `repGx` is taken
*backward* from `0`, and the slice average of `repFun + (backward primitive)` is the (manifestly
measurable) terminal value. -/

variable (m) (K : ℝ) (hK : 0 < K)

/-- The region `{(t,p) | p.1 < t < 0}` used to define the backward axial primitive. -/
theorem measurableSet_primRegionExit_tf :
    MeasurableSet {r : ℝ × CapSpace m | r.2.1 < r.1 ∧ r.1 < (0 : ℝ)} := by
  have h1 : IsOpen {r : ℝ × CapSpace m | r.2.1 < r.1} :=
    isOpen_lt (continuous_fst.comp continuous_snd) continuous_fst
  have h2 : IsOpen {r : ℝ × CapSpace m | r.1 < (0 : ℝ)} := isOpen_lt continuous_fst continuous_const
  exact (h1.inter h2).measurableSet

/-- The integration kernel of the **backward** axial primitive of `∂ₓu`, from the exit point `0`. -/
def primKernelExit_tf (u : H1P (Cap.flat m K hK).body) : ℝ × CapSpace m → ℝ :=
  {r : ℝ × CapSpace m | r.2.1 < r.1 ∧ r.1 < (0 : ℝ)}.indicator
    fun r => repGx (Cap.flat m K hK) u (r.1, r.2.2)

/-- The **backward axial primitive** `p ↦ ∫_{p.1}^0 ∂ₓu(t, p.2) dt`, in a manifestly measurable
form. -/
def slicePrimExit_tf (u : H1P (Cap.flat m K hK).body) (p : CapSpace m) : ℝ :=
  ∫ t, primKernelExit_tf m K hK u (t, p)

theorem stronglyMeasurable_primKernelExit_tf (u : H1P (Cap.flat m K hK).body) :
    StronglyMeasurable (primKernelExit_tf m K hK u) := by
  refine StronglyMeasurable.indicator ?_ (measurableSet_primRegionExit_tf m)
  exact (stronglyMeasurable_repGx (Cap.flat m K hK) u).comp_measurable
    (by fun_prop : Measurable fun r : ℝ × CapSpace m => (r.1, r.2.2))

theorem stronglyMeasurable_slicePrimExit_tf (u : H1P (Cap.flat m K hK).body) :
    StronglyMeasurable (slicePrimExit_tf m K hK u) :=
  (stronglyMeasurable_primKernelExit_tf m K hK u).integral_prod_left'

theorem slicePrimExit_eq_tf (u : H1P (Cap.flat m K hK).body) (s : ℝ)
    (z : EuclideanSpace ℝ (Fin m)) :
    slicePrimExit_tf m K hK u (s, z) = ∫ t in Ioo s (0 : ℝ), repGx (Cap.flat m K hK) u (t, z) := by
  rw [slicePrimExit_tf, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [primKernelExit_tf, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioo]

/-- The integrand whose slice average is the terminal-disc value. -/
def exitIntegrand_tf (u : H1P (Cap.flat m K hK).body) : CapSpace m → ℝ :=
  (Cap.flat m K hK).body.indicator fun p =>
    repFun (Cap.flat m K hK) u p + slicePrimExit_tf m K hK u p

/-- **The terminal-disc trace of a weak-`H¹` function on the flat cap.**  On almost every axial
line `s ↦ u(s,z) + ∫_s^0 ∂ₓu(t,z) dt` is a.e. constant, and `discTrace_tf` is that constant,
written as the average over the full axial slice `(-K,0)` so as to be manifestly measurable. -/
def discTrace_tf (u : H1P (Cap.flat m K hK).body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (∫ s, exitIntegrand_tf m K hK u (s, z)) / K

theorem stronglyMeasurable_exitIntegrand_tf (u : H1P (Cap.flat m K hK).body) :
    StronglyMeasurable (exitIntegrand_tf m K hK u) :=
  ((stronglyMeasurable_repFun (Cap.flat m K hK) u).add
    (stronglyMeasurable_slicePrimExit_tf m K hK u)).indicator (measurableSet_body' _)

/-- **The terminal-disc trace is measurable.** -/
theorem measurable_discTrace_tf (u : H1P (Cap.flat m K hK).body) :
    Measurable (discTrace_tf m K hK u) := by
  have h1 : StronglyMeasurable fun z => ∫ s, exitIntegrand_tf m K hK u (s, z) :=
    (stronglyMeasurable_exitIntegrand_tf m K hK u).integral_prod_left'
  exact h1.measurable.div_const K

/-! ### The defining property of the terminal-disc trace -/

/-- **The exit constant exists on almost every axial line.**  For almost every `z` in the
entrance disk there is a constant `c` with `u(s,z) = c - ∫_s^0 ∂ₓu(t,z) dt` for almost every `s`
in the axial slice `(-K,0)`; `c` is the value of the absolutely continuous representative at the
exit point `s = 0`. -/
theorem exists_exitConst_tf (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)), ∃ c : ℝ,
      ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
        u.toFun (s, z) = c - ∫ t in s..(0 : ℝ), u.gx (t, z) := by
  filter_upwards [sliceAC_axial_cap (Cap.flat m K hK) u,
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) (integrableOn_body_of_memL2 _ u.memL2)),
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) (integrableOn_body_of_memL2 _ u.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hw hu hg hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  rw [exitTime_flat_elf m K hK hznorm] at hw hu hg
  rw [flat_K_elf] at hw hu hg
  have hKab : (-K : ℝ) < 0 := by linarith
  obtain ⟨c, hc⟩ := ae_eq_const_add_integral hKab hu hg hw
  set mid : ℝ := (-K + 0) / 2 with hmid
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKab.le).2 hg
  have hII : ∀ y w : ℝ, y ∈ Icc (-K) (0 : ℝ) → w ∈ Icc (-K) (0 : ℝ) →
      IntervalIntegrable (fun t => u.gx (t, z)) volume y w := by
    intro y w hy hw'
    refine hgI.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le hKab.le]; exact hy
    · rw [uIcc_of_le hKab.le]; exact hw'
  refine ⟨c + ∫ t in mid..(0 : ℝ), u.gx (t, z), ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  have hs' : u.toFun (s, z) = c + ∫ t in mid..s, u.gx (t, z) := hs
  have hmidIcc : mid ∈ Icc (-K) (0 : ℝ) := ⟨by rw [hmid]; linarith, by rw [hmid]; linarith⟩
  have hsIcc : s ∈ Icc (-K) (0 : ℝ) := Ioo_subset_Icc_self hsmem
  have hsplit : (∫ t in mid..s, u.gx (t, z))
      = (∫ t in mid..(0 : ℝ), u.gx (t, z)) + ∫ t in (0 : ℝ)..s, u.gx (t, z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hII mid 0 hmidIcc ⟨by linarith, le_rfl⟩) (hII 0 s ⟨by linarith, le_rfl⟩ hsIcc)).symm
  rw [hs', hsplit, intervalIntegral.integral_symm s 0]
  ring

/-- **The terminal-disc trace spec.**  For almost every `z` in the entrance ball, the axial slice
of `u` is (a.e. equal to) the absolutely continuous function `s ↦ discTrace_tf u z - ∫_s^0 ∂ₓu`. -/
theorem discTrace_spec_tf (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
        u.toFun (s, z) = discTrace_tf m K hK u z - ∫ t in s..(0 : ℝ), u.gx (t, z) := by
  filter_upwards [exists_exitConst_tf m K hK u, ae_restrict_of_ae (ae_slice_repFun (Cap.flat m K hK) u),
    ae_restrict_of_ae (ae_slice_repGx (Cap.flat m K hK) u), ae_restrict_mem measurableSet_ball]
    with z hc hrf hrg hzb
  obtain ⟨c, hc⟩ := hc
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKab : (-K : ℝ) < 0 := by linarith
  have hmemslice : ∀ s : ℝ, s ∈ Ioo (-K) (0 : ℝ) → ((s, z) : CapSpace m) ∈ (Cap.flat m K hK).body := by
    intro s hs
    have : s ∈ axialSlice (Cap.flat m K hK) z := by
      rw [axialSlice_flat_elf m K hK hznorm]; exact hs
    exact this
  -- the backward primitive of the representative agrees with the interval integral of `∂ₓu`
  have hprim : ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      slicePrimExit_tf m K hK u (s, z) = ∫ t in s..(0 : ℝ), u.gx (t, z) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [slicePrimExit_eq_tf, intervalIntegral_eq_integral_Ioo hs.2.le]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrg] with t ht htmem
    exact ht (hmemslice t ⟨hs.1.trans htmem.1, htmem.2⟩)
  -- hence the integrand is a.e. equal to the constant `c` on the slice
  have hconst : ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      repFun (Cap.flat m K hK) u (s, z) + slicePrimExit_tf m K hK u (s, z) = c := by
    filter_upwards [hc, hprim, ae_restrict_of_ae hrf, ae_restrict_mem measurableSet_Ioo]
      with s hs1 hs2 hs3 hs4
    rw [hs3 (hmemslice s hs4), hs2, hs1]; ring
  -- compute the slice average
  have hint : (∫ s, exitIntegrand_tf m K hK u (s, z)) = K * c := by
    rw [exitIntegrand_tf, integral_indicator_body_line (Cap.flat m K hK)
      (fun p => repFun (Cap.flat m K hK) u p + slicePrimExit_tf m K hK u p) z,
      flat_K_elf, exitTime_flat_elf m K hK hznorm,
      setIntegral_congr_ae measurableSet_Ioo ((ae_restrict_iff' measurableSet_Ioo).1 hconst),
      setIntegral_const, Real.volume_real_Ioo_of_le hKab.le, smul_eq_mul]
    ring
  have hK0 : (K : ℝ) ≠ 0 := hK.ne'
  have hdv : discTrace_tf m K hK u z = c := by
    rw [discTrace_tf, hint]; field_simp
  rw [hdv]
  filter_upwards [hc] with s hs using hs

/-- **`discTrace_tf` is a.e. additive in `u`.**  Both sides are pinned, for a.e. `z`, by
agreement with the axial slice at a single (existing) point `s` in the positive-measure set
`Ioo (-K) 0`, using pointwise additivity of `(u+v).toFun`/`(u+v).gx` and integrability of
`u.gx(·,z)`, `v.gx(·,z)` on the full slice. -/
theorem discTrace_add_tf (u v : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      discTrace_tf m K hK (u + v) z = discTrace_tf m K hK u z + discTrace_tf m K hK v z := by
  have hmne : (volume.restrict (Ioo (-K) (0 : ℝ))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  haveI : (ae (volume.restrict (Ioo (-K) (0 : ℝ)))).NeBot := ae_neBot.2 hmne
  have hKab : (-K : ℝ) < 0 := by linarith
  filter_upwards [discTrace_spec_tf m K hK u, discTrace_spec_tf m K hK v,
    discTrace_spec_tf m K hK (u + v),
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) (integrableOn_body_of_memL2 _ u.gx_memL2)),
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) (integrableOn_body_of_memL2 _ v.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hu hv huv hgu hgv hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  rw [exitTime_flat_elf m K hK hznorm, flat_K_elf] at hgu hgv
  have hguI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKab.le).2 hgu
  have hgvI : IntervalIntegrable (fun t => v.gx (t, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKab.le).2 hgv
  obtain ⟨s, hus, hvs, huvs, hsmem⟩ :=
    (hu.and (hv.and (huv.and (ae_restrict_mem (μ := volume) measurableSet_Ioo)))).exists
  have hII : ∀ w x : ℝ, w ∈ Icc (-K) (0 : ℝ) → x ∈ Icc (-K) (0 : ℝ) →
      IntervalIntegrable (fun t => u.gx (t, z)) volume w x ∧
        IntervalIntegrable (fun t => v.gx (t, z)) volume w x := by
    intro w x hw hx
    refine ⟨hguI.mono_set (uIcc_subset_uIcc ?_ ?_), hgvI.mono_set (uIcc_subset_uIcc ?_ ?_)⟩ <;>
      rw [uIcc_of_le hKab.le] <;> assumption
  have hsuv : (u + v).toFun (s, z) = u.toFun (s, z) + v.toFun (s, z) := by simp [H1P.add_toFun]
  have hsIcc : s ∈ Icc (-K) (0 : ℝ) := Ioo_subset_Icc_self hsmem
  have h0Icc : (0 : ℝ) ∈ Icc (-K) (0 : ℝ) := ⟨hKab.le, le_rfl⟩
  have hIadd : (∫ t in s..(0 : ℝ), (u + v).gx (t, z))
      = (∫ t in s..(0 : ℝ), u.gx (t, z)) + ∫ t in s..(0 : ℝ), v.gx (t, z) := by
    have hcongr : (∫ t in s..(0 : ℝ), (u + v).gx (t, z))
        = ∫ t in s..(0 : ℝ), (u.gx (t, z) + v.gx (t, z)) :=
      intervalIntegral.integral_congr fun t _ => by simp [H1P.add_gx]
    rw [hcongr, intervalIntegral.integral_add (hII s 0 hsIcc h0Icc).1 (hII s 0 hsIcc h0Icc).2]
  linarith [hus, hvs, huvs, hsuv, hIadd]

/-- **`discTrace_tf` is a.e. homogeneous in `u`.** -/
theorem discTrace_smul_tf (c : ℝ) (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      discTrace_tf m K hK (c • u) z = c * discTrace_tf m K hK u z := by
  have hmne : (volume.restrict (Ioo (-K) (0 : ℝ))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  haveI : (ae (volume.restrict (Ioo (-K) (0 : ℝ)))).NeBot := ae_neBot.2 hmne
  have hKab : (-K : ℝ) < 0 := by linarith
  filter_upwards [discTrace_spec_tf m K hK u, discTrace_spec_tf m K hK (c • u),
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) (integrableOn_body_of_memL2 _ u.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hu hcu hgu hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  rw [exitTime_flat_elf m K hK hznorm, flat_K_elf] at hgu
  have hguI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKab.le).2 hgu
  obtain ⟨s, hus, hcus, hsmem⟩ :=
    (hu.and (hcu.and (ae_restrict_mem (μ := volume) measurableSet_Ioo))).exists
  have hscu : (c • u).toFun (s, z) = c * u.toFun (s, z) := by simp [H1P.smul_toFun]
  have hIsmul : (∫ t in s..(0 : ℝ), (c • u).gx (t, z)) = c * ∫ t in s..(0 : ℝ), u.gx (t, z) := by
    have hcongr : (∫ t in s..(0 : ℝ), (c • u).gx (t, z))
        = ∫ t in s..(0 : ℝ), c * u.gx (t, z) :=
      intervalIntegral.integral_congr fun t _ => by simp [H1P.smul_gx]
    rw [hcongr, intervalIntegral.integral_const_mul]
  have hgoal : discTrace_tf m K hK (c • u) z - (∫ t in s..(0 : ℝ), (c • u).gx (t, z))
      = c * (discTrace_tf m K hK u z - ∫ t in s..(0 : ℝ), u.gx (t, z)) := by
    rw [← hcus, hscu, hus]
  rw [hIsmul, mul_sub] at hgoal
  linarith [hgoal]

/-- **The absolutely continuous representative of the axial slice, anchored at the exit `0`.**
Mirrors `RobinCaps.Cap.exists_h1_axialSlice`, shifted so that the value at the *right* endpoint
`K` of the translated interval `(0,K)` is `discTrace_tf`. -/
theorem exists_h1_axialSliceExit_tf (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      ∃ w : Sobolev.H1 K,
        w.toFun K = discTrace_tf m K hK u z ∧
        w.toFun =ᵐ[volume.restrict (Ioo (0 : ℝ) K)] (fun x => u.toFun (x - K, z)) ∧
        deriv w.toFun =ᵐ[volume.restrict (Ioo (0 : ℝ) K)] (fun x => u.gx (x - K, z)) := by
  filter_upwards [discTrace_spec_tf m K hK u,
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) (integrableOn_body_of_memL2 _ u.gx_memL2)),
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) u.gx_memL2.integrable_sq),
    ae_restrict_mem measurableSet_ball] with z hc hg hg2 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  rw [exitTime_flat_elf m K hK hznorm, flat_K_elf] at hg hg2
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : (-K : ℝ) ≤ 0)).2 hg
  have hg2I : IntervalIntegrable (fun t => u.gx (t, z) ^ 2) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : (-K : ℝ) ≤ 0)).2 hg2
  have hGI : IntervalIntegrable (fun t => u.gx (t - K, z)) volume 0 K := by
    have h := hgI.comp_sub_right K
    rw [neg_add_cancel, zero_add] at h
    exact h
  have hG2I : IntervalIntegrable (fun t => u.gx (t - K, z) ^ 2) volume 0 K := by
    have h := hg2I.comp_sub_right K
    rw [neg_add_cancel, zero_add] at h
    exact h
  have hK0 : (0 : ℝ) ≤ K := hK.le
  have hInt0K : (∫ t in (0 : ℝ)..K, u.gx (t - K, z))
      = ∫ t in (-K : ℝ)..0, u.gx (t, z) := by
    have h := intervalIntegral.integral_comp_sub_right (fun t => u.gx (t, z)) K (a := (0:ℝ)) (b := K)
    rw [zero_sub, sub_self] at h
    exact h
  have hc' : ∀ᵐ x ∂(volume : Measure ℝ), x - K ∈ Ioo (-K) (0 : ℝ) →
      u.toFun (x - K, z) = discTrace_tf m K hK u z - ∫ t in (x - K)..(0 : ℝ), u.gx (t, z) :=
    (measurePreserving_sub_right (volume : Measure ℝ) K).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).1 hc)
  refine ⟨Sobolev.primitiveH1 hK0 hGI hG2I
      (discTrace_tf m K hK u z - ∫ t in (0 : ℝ)..K, u.gx (t - K, z)), ?_, ?_, ?_⟩
  · rw [Sobolev.primitiveH1_toFun]; ring
  · rw [Sobolev.primitiveH1_toFun, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hc'] with x hx hxmem
    have hmem : x - K ∈ Ioo (-K) (0 : ℝ) := ⟨by linarith [hxmem.1], by linarith [hxmem.2]⟩
    show (discTrace_tf m K hK u z - ∫ t in (0 : ℝ)..K, u.gx (t - K, z))
        + (∫ t in (0 : ℝ)..x, u.gx (t - K, z)) = u.toFun (x - K, z)
    rw [hx hmem]
    have hsplit : (∫ t in (0 : ℝ)..K, u.gx (t - K, z))
        = (∫ t in (0 : ℝ)..x, u.gx (t - K, z)) + ∫ t in x..K, u.gx (t - K, z) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hGI.mono_set
          (by rw [uIcc_of_le hK0, uIcc_of_le hxmem.1.le]
              exact Icc_subset_Icc (by linarith [hxmem.1]) (by linarith [hxmem.2])))
        (hGI.mono_set
          (by rw [uIcc_of_le hK0, uIcc_of_le hxmem.2.le]
              exact Icc_subset_Icc (by linarith [hxmem.1]) le_rfl))).symm
    have hshiftxK : (∫ t in x..K, u.gx (t - K, z)) = ∫ t in (x - K)..(0 : ℝ), u.gx (t, z) := by
      have h := intervalIntegral.integral_comp_sub_right (fun t => u.gx (t, z)) K (a := x) (b := K)
      rw [sub_self] at h
      exact h
    rw [hsplit, hshiftxK]
    ring
  · rw [Sobolev.primitiveH1_toFun]
    have hae := Sobolev.ae_deriv_primitive hGI
        (discTrace_tf m K hK u z - ∫ t in (0 : ℝ)..K, u.gx (t - K, z)) (x₀ := (0 : ℝ)) left_mem_uIcc
    have hsub : Ioo (0 : ℝ) K ⊆ Ι (0 : ℝ) K := by
      rw [uIoc_of_le hK0]; exact Ioo_subset_Ioc_self
    exact hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))

/-- **The disc trace is controlled by the axial slice data**, mirroring
`RobinCaps.Cap.ae_entranceVal_sq_le_el`. -/
theorem ae_discTrace_sq_le_tf (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      discTrace_tf m K hK u z ^ 2
        ≤ (2 / K) * axMass_el (Cap.flat m K hK) u z + (2 * K) * axEnergy_el (Cap.flat m K hK) u z := by
  filter_upwards [exists_h1_axialSliceExit_tf m K hK u,
    ae_restrict_of_ae (ae_slice_repFun (Cap.flat m K hK) u),
    ae_restrict_of_ae (ae_slice_repGx (Cap.flat m K hK) u),
    ae_restrict_mem measurableSet_ball] with z hex hrf hrg hzb
  obtain ⟨w, hw0, hwf, hwd⟩ := hex
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hmemslice : ∀ s : ℝ, s ∈ Ioo (-K) (0 : ℝ) → ((s, z) : CapSpace m) ∈ (Cap.flat m K hK).body := by
    intro s hs
    have : s ∈ axialSlice (Cap.flat m K hK) z := by rw [axialSlice_flat_elf m K hK hznorm]; exact hs
    exact this
  have hmass : Sobolev.mass K w = axMass_el (Cap.flat m K hK) u z := by
    rw [Sobolev.mass, Sobolev.intervalIntegral_eq_setIntegral_Ioo hK.le]
    have h1 : (fun x => w.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) K)] fun x => u.toFun (x - K, z) ^ 2 := by
      filter_upwards [hwf] with x hx; rw [hx]
    rw [integral_congr_ae h1, ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hK.le,
      intervalIntegral.integral_comp_sub_right (fun s => u.toFun (s, z) ^ 2) K,
      show (0 : ℝ) - K = -K by ring, show K - K = (0 : ℝ) by ring,
      Sobolev.intervalIntegral_eq_setIntegral_Ioo (by linarith : (-K : ℝ) ≤ 0), axMass_el,
      exitTime_flat_elf m K hK hznorm, flat_K_elf]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrf] with s hs hsmem
    rw [hs (hmemslice s hsmem)]
  have hdir : Sobolev.dirichlet K w = axEnergy_el (Cap.flat m K hK) u z := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hK.le]
    have h1 : (fun x => deriv w.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) K)] fun x => u.gx (x - K, z) ^ 2 := by
      filter_upwards [hwd] with x hx; rw [hx]
    rw [integral_congr_ae h1, ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hK.le,
      intervalIntegral.integral_comp_sub_right (fun s => u.gx (s, z) ^ 2) K,
      show (0 : ℝ) - K = -K by ring, show K - K = (0 : ℝ) by ring,
      Sobolev.intervalIntegral_eq_setIntegral_Ioo (by linarith : (-K : ℝ) ≤ 0), axEnergy_el,
      exitTime_flat_elf m K hK hznorm, flat_K_elf]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrg] with s hs hsmem
    rw [hs (hmemslice s hsmem)]
  have hkey := Sobolev.endpoint_ell_sq_le w hK
  rw [hw0, hmass, hdir] at hkey
  exact hkey

/-- **`discTrace_tf` is bounded pointwise by the same majorant `majFun_elf`** used to control
`entranceVal` in `RobinCaps/Cap/EntranceL2Flat.lean`. -/
theorem ae_discTrace_sq_le_maj_tf (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      discTrace_tf m K hK u z ^ 2 ≤ majFun_elf m K hK u z := by
  filter_upwards [ae_discTrace_sq_le_tf m K hK u] with z hz
  exact hz

theorem integrableOn_discTrace_sq_tf (u : H1P (Cap.flat m K hK).body) :
    IntegrableOn (fun z => discTrace_tf m K hK u z ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  have hmeas : AEStronglyMeasurable (discTrace_tf m K hK u)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    (measurable_discTrace_tf m K hK u).aestronglyMeasurable
  refine Integrable.mono' (integrableOn_majFun_elf m K hK u) (hmeas.pow 2) ?_
  filter_upwards [ae_discTrace_sq_le_maj_tf m K hK u] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hz

/-- **The `L²(B_m(1))` trace bound for the disc trace.** -/
theorem integral_discTrace_sq_le_tf (u : H1P (Cap.flat m K hK).body) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, discTrace_tf m K hK u z ^ 2)
      ≤ max (2 / K) (2 * K) * (massP u + dirichletP u) := by
  have hstep : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, discTrace_tf m K hK u z ^ 2)
      ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, majFun_elf m K hK u z :=
    integral_mono_ae (integrableOn_discTrace_sq_tf m K hK u) (integrableOn_majFun_elf m K hK u)
      (ae_discTrace_sq_le_maj_tf m K hK u)
  exact hstep.trans (integral_majFun_le_elf m K hK u)

/-- **The closure of the flat cap body** is the closed cylinder. -/
theorem closure_flatBody_tf :
    closure (Cap.flat m K hK).body
      = Icc (-K) (0 : ℝ) ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  rw [flatBody_eq_bulkCyl_tf m K hK, bulkCyl_eq, transverseBall, closure_prod_eq,
    closure_Ioo (by linarith : (-K : ℝ) ≠ 0), closure_ball (0 : EuclideanSpace ℝ (Fin m)) one_ne_zero]

/-- **Consistency of the disc trace with a continuous representative.**  If `u.toFun` is
continuous on the closure of the flat cap body, then for a.e. `z` in the entrance ball the disc
trace agrees with `u.toFun (0, z)`. -/
theorem discTrace_eq_of_continuousOn_tf (u : H1P (Cap.flat m K hK).body)
    (hcont : ContinuousOn u.toFun (closure (Cap.flat m K hK).body)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      discTrace_tf m K hK u z = u.toFun (0, z) := by
  filter_upwards [discTrace_spec_tf m K hK u, ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae
      (ae_integrableOn_cap_slice (Cap.flat m K hK) (integrableOn_body_of_memL2 _ u.gx_memL2))]
    with z hz hzb hgOn
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKab : (-K : ℝ) < 0 := by linarith
  rw [exitTime_flat_elf m K hK hznorm, flat_K_elf] at hgOn
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKab.le).2 hgOn
  have hmapsto : MapsTo (fun s : ℝ => (s, z)) (Icc (-K) (0 : ℝ)) (closure (Cap.flat m K hK).body) := by
    intro s hs
    rw [closure_flatBody_tf]
    exact ⟨hs, mem_closedBall_zero_iff.2 hznorm.le⟩
  have h1 : ContinuousOn (fun s => u.toFun (s, z)) (Icc (-K) (0 : ℝ)) :=
    hcont.comp (continuous_id.prodMk continuous_const).continuousOn hmapsto
  have h2 : ContinuousOn (fun s => discTrace_tf m K hK u z - ∫ t in s..(0 : ℝ), u.gx (t, z))
      (Icc (-K) (0 : ℝ)) := by
    have heq : (fun s => discTrace_tf m K hK u z - ∫ t in s..(0 : ℝ), u.gx (t, z))
        = fun s => discTrace_tf m K hK u z + ∫ t in (0 : ℝ)..s, u.gx (t, z) := by
      funext s
      rw [intervalIntegral.integral_symm (0 : ℝ) s]
      ring
    rw [heq]
    have hmidIcc : (0 : ℝ) ∈ uIcc (-K) (0 : ℝ) := by rw [uIcc_of_le hKab.le]; exact right_mem_Icc.2 hKab.le
    have hcontprim : ContinuousOn (fun s => ∫ t in (0 : ℝ)..s, u.gx (t, z)) (uIcc (-K) (0 : ℝ)) :=
      intervalIntegral.continuousOn_primitive_interval' hgI hmidIcc
    rw [uIcc_of_le hKab.le] at hcontprim
    exact continuousOn_const.add hcontprim
  have hfin := eq_of_ae_eq_of_continuousOn hKab h1 h2 hz
  rw [intervalIntegral.integral_same, sub_zero] at hfin
  exact hfin.symm

/-! ## 3. The lateral wall trace on the bulk cylinder

This mirrors `RobinCaps.ThinDomain.bulkTrace_tgb` (`RobinCaps/ThinDomain/TraceGenBulk.lean`), but
for a **bare cylinder** `bulkCyl (-K) 0 m 1` rather than the bulk of a `thinDomain`: no restriction
step, no `hL`, and `Ioo (-K) 0` in place of `Ioo (interfaceL Cm L R) (interfaceR Cp L R)`.  Every
underlying ingredient (`IsGoodSlice`, `slice`, `stronglyMeasurable_traceSphere_joint_tgb`,
`ae_radial_congr_joint_tgb`, `traceSphere_congr_th`, `traceSphere_add_tgb`,
`traceSphere_smul_tgb`) is already stated for an abstract cylinder, so the proofs below are
essentially the `_tgb` proofs with the thin-domain bookkeeping stripped out. -/

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- **The lateral wall trace on the bare cylinder.** -/
def lateralTraceCyl_tf (u : H1P (bulkCyl (-K) 0 m 1)) : CapSpace m → ℝ :=
  fun p =>
    if p.1 ∈ Ioo (-K) (0 : ℝ) ∧ p.2 ≠ 0 then
      Weak.traceSphere 1 (slice u p.1).toFun (slice u p.1).grad (‖p.2‖⁻¹ • p.2)
    else 0

theorem lateralTraceCyl_tf_apply (u : H1P (bulkCyl (-K) 0 m 1)) {x : ℝ}
    (hx : x ∈ Ioo (-K) (0 : ℝ)) (w : sphere (0 : E) 1) :
    lateralTraceCyl_tf m K u (x, (w : E))
      = Weak.traceSphere 1 (slice u x).toFun (slice u x).grad (w : E) := by
  have hwn : ‖(w : E)‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
  have hwne : (w : E) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hwn; exact one_ne_zero hwn.symm
  have hquot : ‖(w : E)‖⁻¹ • (w : E) = (w : E) := by rw [hwn, inv_one, one_smul]
  show (if x ∈ Ioo (-K) (0 : ℝ) ∧ (w : E) ≠ 0 then
      Weak.traceSphere 1 (slice u x).toFun (slice u x).grad (‖(w : E)‖⁻¹ • (w : E)) else 0)
      = Weak.traceSphere 1 (slice u x).toFun (slice u x).grad (w : E)
  rw [if_pos ⟨hx, hwne⟩, hquot]

/-- **The lateral wall trace is jointly almost-everywhere strongly measurable** in the axial
coordinate and the direction (mirrors `aestronglyMeasurable_bulkTrace_tgb`). -/
theorem aestronglyMeasurable_lateralTraceCyl_tf (hm : 1 ≤ m) (u : H1P (bulkCyl (-K) 0 m 1)) :
    AEStronglyMeasurable (fun p : ℝ × sphere (0 : E) 1 => lateralTraceCyl_tf m K u (p.1, (p.2 : E)))
      ((volume.restrict (Ioo (-K) (0 : ℝ))).prod (sphereMeasure m)) := by
  set F : CapSpace m → ℝ := u.memL2.aestronglyMeasurable.mk u.toFun with hF_def
  set Gv : CapSpace m → E := u.gz_memL2.aestronglyMeasurable.mk u.gz with hGv_def
  have hFmeas : Measurable F := u.memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hGvmeas : Measurable Gv := u.gz_memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hFeq := u.memL2.aestronglyMeasurable.ae_eq_mk
  have hGveq := u.gz_memL2.aestronglyMeasurable.ae_eq_mk
  refine ⟨fun p => traceSphere 1 (fun z => F (p.1, z)) (fun z => Gv (p.1, z)) (p.2 : E),
    stronglyMeasurable_traceSphere_joint_tgb hFmeas hGvmeas, ?_⟩
  have h0 : ∀ᵐ p : ℝ × sphere (0 : E) 1 ∂((volume.restrict (Ioo (-K) (0 : ℝ))).prod (sphereMeasure m)),
      p.1 ∈ Ioo (-K) (0 : ℝ) := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  have h1 : ∀ᵐ p : ℝ × sphere (0 : E) 1 ∂((volume.restrict (Ioo (-K) (0 : ℝ))).prod (sphereMeasure m)),
      IsGoodSlice u p.1 := Measure.quasiMeasurePreserving_fst.ae (ae_isGoodSlice u)
  have h2 := ae_radial_congr_joint_tgb (m := m) hm (a := (-K : ℝ)) (b := (0 : ℝ)) (R := (1 : ℝ)) hFeq
  have h3 := ae_radial_congr_joint_tgb (m := m) hm (a := (-K : ℝ)) (b := (0 : ℝ)) (R := (1 : ℝ)) hGveq
  filter_upwards [h0, h1, h2, h3] with p hxmem hgood hp2 hp3
  rw [lateralTraceCyl_tf_apply m K u hxmem p.2, slice_toFun hgood, slice_grad hgood]
  exact traceSphere_congr_th one_pos hp2 hp3

/-- **The lateral trace density.** -/
def lateralDensityCyl_tf (u : H1P (bulkCyl (-K) 0 m 1)) (x : ℝ) : ℝ :=
  ∫ w : sphere (0 : E) 1, (lateralTraceCyl_tf m K u (x, (w : E))) ^ 2 ∂(sphereMeasure m)

/-- **The trace bound on the lateral wall** (mirrors `bulkDensity_integral_le_tgb`, with `R = 1`,
so the `R^{m-1}` prefactor is `1`). -/
theorem lateralDensityCyl_integral_le_tf (hm : 1 ≤ m) (u : H1P (bulkCyl (-K) 0 m 1)) :
    (∫ x in Ioo (-K) (0 : ℝ), lateralDensityCyl_tf m K u x)
      ≤ max (4 / (1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹) ((1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹)
        * (massP u + dirichletP u) := by
  set C := max (4 / (1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹) ((1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹)
    with hC_def
  have hCnn : 0 ≤ C := le_trans (by positivity) (le_max_left _ _)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (-K) (0 : ℝ))] (lateralDensityCyl_tf m K u) :=
    Eventually.of_forall fun x => integral_nonneg fun w => sq_nonneg _
  have hmaj : Integrable (fun x => C * (NB (slice u x) + Weak.dirichlet (slice u x)))
      (volume.restrict (Ioo (-K) (0 : ℝ))) :=
    ((integrableOn_NB_slice u).add (integrableOn_dirichlet_slice u)).const_mul _
  have hle : (lateralDensityCyl_tf m K u)
      ≤ᵐ[volume.restrict (Ioo (-K) (0 : ℝ))]
      fun x => C * (NB (slice u x) + Weak.dirichlet (slice u x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hpt : lateralDensityCyl_tf m K u x
        = ∫ w : sphere (0 : E) 1,
            (Weak.traceSphere 1 (slice u x).toFun (slice u x).grad (w : E)) ^ 2
              ∂(sphereMeasure m) := by
      rw [lateralDensityCyl_tf]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      dsimp only
      rw [lateralTraceCyl_tf_apply m K u hx w]
    rw [hpt]
    have hb : (∫ w : sphere (0 : E) 1,
        (Weak.traceSphere 1 (slice u x).toFun (slice u x).grad (w : E)) ^ 2 ∂(sphereMeasure m))
        ≤ C * (NB (slice u x) + Weak.dirichlet (slice u x)) :=
      traceSphere_sq_integral_le hm one_pos (slice u x)
    exact hb
  have hmono := integral_mono_of_nonneg hnn hmaj hle
  have hstep1 : (∫ x in Ioo (-K) (0 : ℝ), (NB (slice u x) + Weak.dirichlet (slice u x)))
      = massP u + ∫ x in Ioo (-K) (0 : ℝ), Weak.dirichlet (slice u x) := by
    rw [integral_add (integrableOn_NB_slice u) (integrableOn_dirichlet_slice u),
      ← massP_eq_integral_NB_slice]
  have hstep2 : (∫ x in Ioo (-K) (0 : ℝ), Weak.dirichlet (slice u x)) ≤ dirichletP u := by
    have hax := dirichletP_eq_axial_add_slice u
    linarith [axialDirichletP_nonneg u]
  rw [integral_const_mul, hstep1] at hmono
  have hfin : massP u + ∫ x in Ioo (-K) (0 : ℝ), Weak.dirichlet (slice u x) ≤ massP u + dirichletP u := by
    linarith
  calc (∫ x in Ioo (-K) (0 : ℝ), lateralDensityCyl_tf m K u x)
      ≤ C * (massP u + ∫ x in Ioo (-K) (0 : ℝ), Weak.dirichlet (slice u x)) := hmono
    _ ≤ C * (massP u + dirichletP u) := mul_le_mul_of_nonneg_left hfin hCnn

/-- **A lateral sphere point lies in the closure of the cylinder.**  Simpler than the
`thinDomain` case (`bulkSpherePt_mem_closure_thinDomain_tgb`): the closure of `bulkCyl (-K) 0 m 1`
is the closed cylinder `Icc (-K) 0 ×ˢ closedBall 0 1` outright. -/
theorem cylRadialPt_mem_closure_bulkCyl_tf (hK : 0 < K) {x : ℝ} (hx : x ∈ Ioo (-K) (0 : ℝ))
    (w : sphere (0 : E) 1) {r : ℝ} (hr0 : 0 < r) (hrR : r ≤ 1) :
    (x, r • (w : E)) ∈ closure (bulkCyl (-K) 0 m 1) := by
  rw [← flatBody_eq_bulkCyl_tf m K hK, closure_flatBody_tf]
  refine ⟨Ioo_subset_Icc_self hx, ?_⟩
  rw [mem_closedBall_zero_iff, norm_smul_sphere hr0 w]
  exact hrR

/-- **Consistency with a continuous representative.** -/
theorem lateralTraceCyl_eq_of_continuousOn_tf (hm : 1 ≤ m) (hK : 0 < K)
    (u : H1P (bulkCyl (-K) 0 m 1))
    (hcont : ContinuousOn u.toFun (closure (bulkCyl (-K) 0 m 1))) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        lateralTraceCyl_tf m K u (x, (w : E)) = u.toFun (x, (w : E)) := by
  filter_upwards [ae_isGoodSlice u, ae_restrict_mem measurableSet_Ioo] with x hgood hx
  have hcont' : ∀ w : sphere (0 : E) 1,
      ContinuousOn (fun r : ℝ => (slice u x).toFun (r • (w : E))) (Icc ((1 : ℝ) / 2) 1) := by
    intro w
    have heq : (fun r : ℝ => (slice u x).toFun (r • (w : E)))
        = fun r : ℝ => u.toFun (x, r • (w : E)) := by
      funext r; rw [slice_toFun hgood]
    rw [heq]
    have hmap : MapsTo (fun r : ℝ => (x, r • (w : E))) (Icc ((1 : ℝ) / 2) 1)
        (closure (bulkCyl (-K) 0 m 1)) := fun r hr =>
      cylRadialPt_mem_closure_bulkCyl_tf m K hK hx w (by linarith [hr.1]) hr.2
    exact hcont.comp
      ((continuous_const.prodMk (continuous_id.smul continuous_const)).continuousOn) hmap
  have h := traceSphere_eq_of_continuousOn_th hm one_pos (slice u x) hcont'
  filter_upwards [h] with w hw
  rw [lateralTraceCyl_tf_apply m K u hx w, hw, slice_toFun hgood, one_smul]

/-- `lateralTraceCyl_tf` is a.e. additive in `u`. -/
theorem lateralTraceCyl_add_tf (hm : 1 ≤ m) (u v : H1P (bulkCyl (-K) 0 m 1)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        lateralTraceCyl_tf m K (u + v) (x, (w : E))
          = lateralTraceCyl_tf m K u (x, (w : E)) + lateralTraceCyl_tf m K v (x, (w : E)) := by
  filter_upwards [ae_isGoodSlice u, ae_isGoodSlice v, ae_restrict_mem measurableSet_Ioo]
    with x h1 h2 hx
  have hslice_eq : slice (u + v) x = slice u x + slice v x := slice_add_tgb h1 h2
  filter_upwards [traceSphere_add_tgb hm one_pos (slice u x) (slice v x)] with w hw
  rw [lateralTraceCyl_tf_apply m K (u + v) hx w, hslice_eq,
    lateralTraceCyl_tf_apply m K u hx w, lateralTraceCyl_tf_apply m K v hx w]
  exact hw

/-- `lateralTraceCyl_tf` is a.e. homogeneous in `u`. -/
theorem lateralTraceCyl_smul_tf (hm : 1 ≤ m) (c : ℝ) (u : H1P (bulkCyl (-K) 0 m 1)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        lateralTraceCyl_tf m K (c • u) (x, (w : E)) = c * lateralTraceCyl_tf m K u (x, (w : E)) := by
  filter_upwards [ae_isGoodSlice u, ae_restrict_mem measurableSet_Ioo] with x h1 hx
  have hslice_eq : slice (c • u) x = c • slice u x := slice_smul_tgb c h1
  filter_upwards [traceSphere_smul_tgb hm one_pos c (slice u x)] with w hw
  rw [lateralTraceCyl_tf_apply m K (c • u) hx w, hslice_eq, lateralTraceCyl_tf_apply m K u hx w]
  exact hw

/-! ## 4. The combined (raw) trace, and its linearization

`rawTraceFun_tf` combines the disc trace (at `s = 0`) and the lateral trace (elsewhere) into a
single function on `CapSpace m`, exactly as prescribed for `trΓ`. It is only a.e.-additive /
a.e.-homogeneous on the two loci that matter (`{0} × B_m(1)` and `Ioo (-K) 0 × S^{m-1}`); a
`Submodule` of functions null on these loci and a linear section of the quotient map (mirroring
`RobinCaps.Cap.trGamma_th` of `TraceDataHemi.lean`) turn this into a genuinely pointwise-linear
representative. -/

/-- **The combined raw trace on `Γ`.** -/
def rawTraceFun_tf (u : H1P (Cap.flat m K hK).body) : CapSpace m → ℝ :=
  fun p => if p.1 = 0 then discTrace_tf m K hK u p.2 else lateralTraceCyl_tf m K (toCyl_tf m K hK u) p

theorem rawTraceFun_disc_tf (u : H1P (Cap.flat m K hK).body) (z : E) :
    rawTraceFun_tf m K hK u (0, z) = discTrace_tf m K hK u z := if_pos rfl

theorem rawTraceFun_lat_tf (u : H1P (Cap.flat m K hK).body) {s : ℝ} (hs : s ≠ 0) (z : E) :
    rawTraceFun_tf m K hK u (s, z) = lateralTraceCyl_tf m K (toCyl_tf m K hK u) (s, z) := if_neg hs

/-- **Functions null on the two loci of `Γ`.** -/
def nullGammaFlat_tf : Submodule ℝ (CapSpace m → ℝ) where
  carrier := {f : CapSpace m → ℝ |
    (∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)), f (0, z) = 0) ∧
    (∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m), f (s, (w : E)) = 0)}
  zero_mem' := ⟨Eventually.of_forall fun _ => rfl,
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [hf1, hg1] with z h1 h2
      show f (0, z) + g (0, z) = 0
      rw [h1, h2, add_zero]
    · filter_upwards [hf2, hg2] with s h1 h2
      filter_upwards [h1, h2] with w hw1 hw2
      show f (s, (w : E)) + g (s, (w : E)) = 0
      rw [hw1, hw2, add_zero]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [hf1] with z h1
      show c * f (0, z) = 0
      rw [h1, mul_zero]
    · filter_upwards [hf2] with s h1
      filter_upwards [h1] with w hw1
      show c * f (s, (w : E)) = 0
      rw [hw1, mul_zero]

theorem nullGamma_disc_tf {f : CapSpace m → ℝ} (hf : f ∈ nullGammaFlat_tf m K) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)), f (0, z) = 0 := hf.1

theorem nullGamma_lat_tf {f : CapSpace m → ℝ} (hf : f ∈ nullGammaFlat_tf m K) :
    ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m), f (s, (w : E)) = 0 := hf.2

/-- **The class of the raw trace in the quotient by `nullGammaFlat_tf` is linear.** -/
def rawTraceQ_tf (hm : 1 ≤ m) :
    H1P (Cap.flat m K hK).body →ₗ[ℝ] ((CapSpace m → ℝ) ⧸ nullGammaFlat_tf m K) where
  toFun u := Submodule.Quotient.mk (rawTraceFun_tf m K hK u)
  map_add' u v := by
    have hmem : rawTraceFun_tf m K hK (u + v)
        - (rawTraceFun_tf m K hK u + rawTraceFun_tf m K hK v) ∈ nullGammaFlat_tf m K := by
      refine ⟨?_, ?_⟩
      · filter_upwards [discTrace_add_tf m K hK u v] with z hz
        rw [Pi.sub_apply, Pi.add_apply, rawTraceFun_disc_tf, rawTraceFun_disc_tf,
          rawTraceFun_disc_tf]
        linarith [hz]
      · filter_upwards [lateralTraceCyl_add_tf m K hm (toCyl_tf m K hK u) (toCyl_tf m K hK v),
          ae_restrict_mem measurableSet_Ioo] with s hs hsmem
        filter_upwards [hs] with w hw
        have hsne : s ≠ 0 := ne_of_lt hsmem.2
        rw [Pi.sub_apply, Pi.add_apply, rawTraceFun_lat_tf m K hK (u + v) hsne,
          rawTraceFun_lat_tf m K hK u hsne, rawTraceFun_lat_tf m K hK v hsne, toCyl_tf_add]
        linarith [hw]
    have h := (Submodule.Quotient.eq (nullGammaFlat_tf m K)).2 hmem
    rw [h]; rfl
  map_smul' c u := by
    have hmem : rawTraceFun_tf m K hK (c • u) - c • rawTraceFun_tf m K hK u ∈ nullGammaFlat_tf m K := by
      refine ⟨?_, ?_⟩
      · filter_upwards [discTrace_smul_tf m K hK c u] with z hz
        rw [Pi.sub_apply, Pi.smul_apply, rawTraceFun_disc_tf, rawTraceFun_disc_tf, smul_eq_mul]
        linarith [hz]
      · filter_upwards [lateralTraceCyl_smul_tf m K hm c (toCyl_tf m K hK u),
          ae_restrict_mem measurableSet_Ioo] with s hs hsmem
        filter_upwards [hs] with w hw
        have hsne : s ≠ 0 := ne_of_lt hsmem.2
        rw [Pi.sub_apply, Pi.smul_apply, rawTraceFun_lat_tf m K hK (c • u) hsne,
          rawTraceFun_lat_tf m K hK u hsne, toCyl_tf_smul, smul_eq_mul]
        linarith [hw]
    have h := (Submodule.Quotient.eq (nullGammaFlat_tf m K)).2 hmem
    rw [h]; rfl

theorem exists_gammaSection_flat_tf :
    ∃ s : ((CapSpace m → ℝ) ⧸ nullGammaFlat_tf m K) →ₗ[ℝ] (CapSpace m → ℝ),
      (nullGammaFlat_tf m K).mkQ.comp s = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)

/-- **A linear section of the quotient map by `nullGammaFlat_tf`.** -/
def gammaSectionFlat_tf :
    ((CapSpace m → ℝ) ⧸ nullGammaFlat_tf m K) →ₗ[ℝ] (CapSpace m → ℝ) :=
  Classical.choose (exists_gammaSection_flat_tf m K)

theorem gammaSectionFlat_spec_tf (q : (CapSpace m → ℝ) ⧸ nullGammaFlat_tf m K) :
    (Submodule.Quotient.mk (gammaSectionFlat_tf m K q) : (CapSpace m → ℝ) ⧸ nullGammaFlat_tf m K)
      = q := by
  have h := congrArg
    (fun F : ((CapSpace m → ℝ) ⧸ nullGammaFlat_tf m K) →ₗ[ℝ]
        ((CapSpace m → ℝ) ⧸ nullGammaFlat_tf m K) => F q)
    (Classical.choose_spec (exists_gammaSection_flat_tf m K))
  simpa only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    LinearMap.id_coe, id_eq] using h

theorem gammaSectionFlat_sub_mem_tf (f : CapSpace m → ℝ) :
    gammaSectionFlat_tf m K (Submodule.Quotient.mk f) - f ∈ nullGammaFlat_tf m K :=
  (Submodule.Quotient.eq (nullGammaFlat_tf m K)).1 (gammaSectionFlat_spec_tf m K _)

/-- **The pointwise-linear `Γ`-trace of the flat cap.** -/
def trGammaFlat_tf (hm : 1 ≤ m) :
    H1P (Cap.flat m K hK).body →ₗ[ℝ] (CapSpace m → ℝ) :=
  (gammaSectionFlat_tf m K).comp (rawTraceQ_tf m K hK hm)

theorem trGammaFlat_disc_ae_tf (hm : 1 ≤ m) (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)),
      trGammaFlat_tf m K hK hm u (0, z) = discTrace_tf m K hK u z := by
  have h := nullGamma_disc_tf m K
    (gammaSectionFlat_sub_mem_tf m K (rawTraceFun_tf m K hK u))
  filter_upwards [h] with z hz
  have hw' : gammaSectionFlat_tf m K (Submodule.Quotient.mk (rawTraceFun_tf m K hK u)) (0, z)
      - rawTraceFun_tf m K hK u (0, z) = 0 := hz
  have heq : trGammaFlat_tf m K hK hm u (0, z)
      = gammaSectionFlat_tf m K (Submodule.Quotient.mk (rawTraceFun_tf m K hK u)) (0, z) := rfl
  rw [heq]
  have : rawTraceFun_tf m K hK u (0, z) = discTrace_tf m K hK u z := rawTraceFun_disc_tf m K hK u z
  linarith [hw', this]

theorem trGammaFlat_lat_ae_tf (hm : 1 ≤ m) (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
      trGammaFlat_tf m K hK hm u (s, (w : E))
        = lateralTraceCyl_tf m K (toCyl_tf m K hK u) (s, (w : E)) := by
  have h := nullGamma_lat_tf m K
    (gammaSectionFlat_sub_mem_tf m K (rawTraceFun_tf m K hK u))
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  filter_upwards [hs] with w hw
  have hw' : gammaSectionFlat_tf m K (Submodule.Quotient.mk (rawTraceFun_tf m K hK u)) (s, (w : E))
      - rawTraceFun_tf m K hK u (s, (w : E)) = 0 := hw
  have heq : trGammaFlat_tf m K hK hm u (s, (w : E))
      = gammaSectionFlat_tf m K (Submodule.Quotient.mk (rawTraceFun_tf m K hK u)) (s, (w : E)) := rfl
  rw [heq]
  have hsne : s ≠ 0 := ne_of_lt hsmem.2
  have : rawTraceFun_tf m K hK u (s, (w : E))
      = lateralTraceCyl_tf m K (toCyl_tf m K hK u) (s, (w : E)) := rawTraceFun_lat_tf m K hK u hsne (w : E)
  linarith [hw', this]

/-! ## 5. The lateral boundary integral of the flat cap reduces to a plain cylindrical integral -/

theorem capAreaElement_flat_tf (s : ℝ) : capAreaElement (Cap.flat m K hK) s = 1 := by
  rw [capAreaElement]
  have hthetaeq : (Cap.flat m K hK).θ = fun _ : ℝ => (1 : ℝ) := rfl
  have hderiv : deriv (Cap.flat m K hK).θ s = 0 := by rw [hthetaeq]; simp
  rw [hderiv, flat_theta_elf]
  norm_num

/-- **The lateral boundary integral of the flat cap is the plain cylindrical integral**
`∫_{-K}^0 ∫_{S^{m-1}} G(s,w) dσ(w) ds`. -/
theorem capLateralIntegral_flat_tf (G : CapSpace m → ℝ) :
    ThinDomain.capLateralIntegral (Cap.flat m K hK) G
      = ∫ s in Ioo (-K) (0 : ℝ), ∫ w : sphere (0 : E) 1, G (s, (w : E)) ∂(sphereMeasure m) := by
  rw [ThinDomain.capLateralIntegral]
  refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
  rw [ThinDomain.capLateralDensity, capAreaElement_flat_tf, flat_theta_elf, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [one_smul]

/-! ## 6. `L²` bounds needed for bilinearity of the `Γ`-pairing -/

theorem aestronglyMeasurable_discTrace_tf (u : H1P (Cap.flat m K hK).body) :
    AEStronglyMeasurable (discTrace_tf m K hK u) (volume.restrict (ball (0 : E) 1)) :=
  (measurable_discTrace_tf m K hK u).aestronglyMeasurable

theorem memLp_discTrace_tf (u : H1P (Cap.flat m K hK).body) :
    MemLp (discTrace_tf m K hK u) 2 (volume.restrict (ball (0 : E) 1)) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_discTrace_tf m K hK u)).2
    (integrableOn_discTrace_sq_tf m K hK u)

theorem integrable_discTrace_mul_tf (u v : H1P (Cap.flat m K hK).body) :
    Integrable (fun z => discTrace_tf m K hK u z * discTrace_tf m K hK v z)
      (volume.restrict (ball (0 : E) 1)) :=
  (memLp_discTrace_tf m K hK u).integrable_mul (memLp_discTrace_tf m K hK v)

theorem memLp_lateralTraceCyl_slice_tf (hm : 1 ≤ m) (u' : H1P (bulkCyl (-K) 0 m 1)) {x : ℝ}
    (hx : x ∈ Ioo (-K) (0 : ℝ)) :
    MemLp (fun w : sphere (0 : E) 1 => lateralTraceCyl_tf m K u' (x, (w : E))) 2 (sphereMeasure m) := by
  have heq : (fun w : sphere (0 : E) 1 => lateralTraceCyl_tf m K u' (x, (w : E)))
      = fun w : sphere (0 : E) 1 => Weak.traceSphere 1 (slice u' x).toFun (slice u' x).grad (w : E) := by
    funext w; exact lateralTraceCyl_tf_apply m K u' hx w
  rw [heq]
  exact (memLp_two_iff_integrable_sq
    (aestronglyMeasurable_traceSphere_th (by omega) one_pos (slice u' x))).2
    (integrable_traceSphere_sq_th (by omega) one_pos (slice u' x))

theorem integrable_lateralTraceCyl_mul_slice_tf (hm : 1 ≤ m) (u v : H1P (bulkCyl (-K) 0 m 1))
    {x : ℝ} (hx : x ∈ Ioo (-K) (0 : ℝ)) :
    Integrable (fun w : sphere (0 : E) 1 =>
        lateralTraceCyl_tf m K u (x, (w : E)) * lateralTraceCyl_tf m K v (x, (w : E)))
      (sphereMeasure m) :=
  (memLp_lateralTraceCyl_slice_tf m K hm u hx).integrable_mul (memLp_lateralTraceCyl_slice_tf m K hm v hx)

theorem aestronglyMeasurable_lateralDensityCyl_tf (hm : 1 ≤ m) (u : H1P (bulkCyl (-K) 0 m 1)) :
    AEStronglyMeasurable (lateralDensityCyl_tf m K u) (volume.restrict (Ioo (-K) (0 : ℝ))) := by
  have h := aestronglyMeasurable_lateralTraceCyl_tf m K hm u
  exact (h.pow 2).integral_prod_right'

/-- **`lateralDensityCyl_tf` is integrable on `Ioo (-K) 0`** (extracted from the domination
argument of `lateralDensityCyl_integral_le_tf`). -/
theorem integrableOn_lateralDensityCyl_tf (hm : 1 ≤ m) (u : H1P (bulkCyl (-K) 0 m 1)) :
    IntegrableOn (lateralDensityCyl_tf m K u) (Ioo (-K) (0 : ℝ)) volume := by
  set C := max (4 / (1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹) ((1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹)
    with hC_def
  have hCnn : 0 ≤ C := le_trans (by positivity) (le_max_left _ _)
  have hmaj : Integrable (fun x => C * (NB (slice u x) + Weak.dirichlet (slice u x)))
      (volume.restrict (Ioo (-K) (0 : ℝ))) :=
    ((integrableOn_NB_slice u).add (integrableOn_dirichlet_slice u)).const_mul _
  have hle : (lateralDensityCyl_tf m K u)
      ≤ᵐ[volume.restrict (Ioo (-K) (0 : ℝ))]
      fun x => C * (NB (slice u x) + Weak.dirichlet (slice u x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hpt : lateralDensityCyl_tf m K u x
        = ∫ w : sphere (0 : E) 1,
            (Weak.traceSphere 1 (slice u x).toFun (slice u x).grad (w : E)) ^ 2
              ∂(sphereMeasure m) := by
      rw [lateralDensityCyl_tf]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      dsimp only
      rw [lateralTraceCyl_tf_apply m K u hx w]
    rw [hpt]
    have hb : (∫ w : sphere (0 : E) 1,
        (Weak.traceSphere 1 (slice u x).toFun (slice u x).grad (w : E)) ^ 2 ∂(sphereMeasure m))
        ≤ C * (NB (slice u x) + Weak.dirichlet (slice u x)) :=
      traceSphere_sq_integral_le hm one_pos (slice u x)
    exact hb
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (-K) (0 : ℝ))] (lateralDensityCyl_tf m K u) :=
    Eventually.of_forall fun x => integral_nonneg fun w => sq_nonneg _
  refine hmaj.mono' (aestronglyMeasurable_lateralDensityCyl_tf m K hm u) ?_
  filter_upwards [hnn, hle] with x hx1 hx2
  rw [Real.norm_eq_abs, abs_of_nonneg hx1]
  exact hx2

/-- **The lateral `Γ`-density**: the sphere integral of the product of two lateral traces. -/
def latGammaDensity_tf (u v : H1P (bulkCyl (-K) 0 m 1)) (x : ℝ) : ℝ :=
  ∫ w : sphere (0 : E) 1, lateralTraceCyl_tf m K u (x, (w : E)) * lateralTraceCyl_tf m K v (x, (w : E))
    ∂(sphereMeasure m)

theorem aestronglyMeasurable_latGammaDensity_tf (hm : 1 ≤ m) (u v : H1P (bulkCyl (-K) 0 m 1)) :
    AEStronglyMeasurable (latGammaDensity_tf m K u v) (volume.restrict (Ioo (-K) (0 : ℝ))) := by
  have hu := aestronglyMeasurable_lateralTraceCyl_tf m K hm u
  have hv := aestronglyMeasurable_lateralTraceCyl_tf m K hm v
  exact (hu.mul hv).integral_prod_right'

theorem abs_latGammaDensity_le_tf (hm : 1 ≤ m) (u v : H1P (bulkCyl (-K) 0 m 1)) {x : ℝ}
    (hx : x ∈ Ioo (-K) (0 : ℝ)) :
    |latGammaDensity_tf m K u v x| ≤ (lateralDensityCyl_tf m K u x + lateralDensityCyl_tf m K v x) / 2 := by
  have hintprod := integrable_lateralTraceCyl_mul_slice_tf m K hm u v hx
  have hintu := (memLp_lateralTraceCyl_slice_tf m K hm u hx).integrable_sq
  have hintv := (memLp_lateralTraceCyl_slice_tf m K hm v hx).integrable_sq
  have h1 : |latGammaDensity_tf m K u v x|
      ≤ ∫ w : sphere (0 : E) 1,
          |lateralTraceCyl_tf m K u (x, (w : E)) * lateralTraceCyl_tf m K v (x, (w : E))|
          ∂(sphereMeasure m) := by
    rw [latGammaDensity_tf]
    have hnorm := norm_integral_le_integral_norm (μ := sphereMeasure m)
      (f := fun w : sphere (0 : E) 1 =>
        lateralTraceCyl_tf m K u (x, (w : E)) * lateralTraceCyl_tf m K v (x, (w : E)))
    simpa [Real.norm_eq_abs] using hnorm
  have h2 : (∫ w : sphere (0 : E) 1,
      |lateralTraceCyl_tf m K u (x, (w : E)) * lateralTraceCyl_tf m K v (x, (w : E))|
        ∂(sphereMeasure m))
      ≤ (lateralDensityCyl_tf m K u x + lateralDensityCyl_tf m K v x) / 2 := by
    rw [lateralDensityCyl_tf, lateralDensityCyl_tf, ← integral_add hintu hintv, ← integral_div]
    refine integral_mono hintprod.abs ((hintu.add hintv).div_const 2) fun w => ?_
    dsimp only
    rw [abs_mul]
    nlinarith [sq_nonneg (|lateralTraceCyl_tf m K u (x, (w : E))|
        - |lateralTraceCyl_tf m K v (x, (w : E))|),
      sq_abs (lateralTraceCyl_tf m K u (x, (w : E))), sq_abs (lateralTraceCyl_tf m K v (x, (w : E)))]
  linarith [h1, h2]

theorem integrableOn_latGammaDensity_tf (hm : 1 ≤ m) (u v : H1P (bulkCyl (-K) 0 m 1)) :
    IntegrableOn (latGammaDensity_tf m K u v) (Ioo (-K) (0 : ℝ)) volume := by
  have hmaj : Integrable (fun x => (lateralDensityCyl_tf m K u x + lateralDensityCyl_tf m K v x) / 2)
      (volume.restrict (Ioo (-K) (0 : ℝ))) :=
    ((integrableOn_lateralDensityCyl_tf m K hm u).add
      (integrableOn_lateralDensityCyl_tf m K hm v)).div_const 2
  refine Integrable.mono' hmaj (aestronglyMeasurable_latGammaDensity_tf m K hm u v) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  exact abs_latGammaDensity_le_tf m K hm u v hx

/-! ## 7. The `Γ`-form of the flat cap, its explicit value, and bilinearity -/

/-- **The `Γ`-form of the flat cap**, i.e. `capGammaPair` of the pointwise-linear traces. -/
def gammaFormFlat_tf (hm : 1 ≤ m) (u v : H1P (Cap.flat m K hK).body) : ℝ :=
  capGammaPair (Cap.flat m K hK) (trGammaFlat_tf m K hK hm u) (trGammaFlat_tf m K hK hm v)

/-- **The `Γ`-form is the concrete lateral-plus-disc integral.** -/
theorem gammaFormFlat_eq_tf (hm : 1 ≤ m) (u v : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm u v
      = (∫ s in Ioo (-K) (0 : ℝ),
          latGammaDensity_tf m K (toCyl_tf m K hK u) (toCyl_tf m K hK v) s)
        + ∫ z in ball (0 : E) 1, discTrace_tf m K hK u z * discTrace_tf m K hK v z := by
  rw [gammaFormFlat_tf, capGammaPair, capLateralIntegral_flat_tf]
  congr 1
  · refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (trGammaFlat_lat_ae_tf m K hK hm u),
      (ae_restrict_iff' measurableSet_Ioo).1 (trGammaFlat_lat_ae_tf m K hK hm v)]
      with s hsu' hsv' hsmem
    have hsu := hsu' hsmem
    have hsv := hsv' hsmem
    rw [latGammaDensity_tf]
    refine integral_congr_ae ?_
    filter_upwards [hsu, hsv] with w hwu hwv
    rw [hwu, hwv]
  · refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (trGammaFlat_disc_ae_tf m K hK hm u),
      (ae_restrict_iff' measurableSet_ball).1 (trGammaFlat_disc_ae_tf m K hK hm v)]
      with z hzu' hzv' hzmem
    rw [hzu' hzmem, hzv' hzmem]

theorem discGammaIntegral_add_left_tf (u u' v : H1P (Cap.flat m K hK).body) :
    (∫ z in ball (0 : E) 1, discTrace_tf m K hK (u + u') z * discTrace_tf m K hK v z)
      = (∫ z in ball (0 : E) 1, discTrace_tf m K hK u z * discTrace_tf m K hK v z)
        + ∫ z in ball (0 : E) 1, discTrace_tf m K hK u' z * discTrace_tf m K hK v z := by
  rw [← integral_add (integrable_discTrace_mul_tf m K hK u v)
    (integrable_discTrace_mul_tf m K hK u' v)]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (discTrace_add_tf m K hK u u')]
    with z hz'
  intro hzmem
  rw [hz' hzmem]; ring

theorem discGammaIntegral_smul_left_tf (c : ℝ) (u v : H1P (Cap.flat m K hK).body) :
    (∫ z in ball (0 : E) 1, discTrace_tf m K hK (c • u) z * discTrace_tf m K hK v z)
      = c * ∫ z in ball (0 : E) 1, discTrace_tf m K hK u z * discTrace_tf m K hK v z := by
  rw [← integral_const_mul]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (discTrace_smul_tf m K hK c u)]
    with z hz'
  intro hzmem
  rw [hz' hzmem]; ring

theorem latGammaIntegral_add_left_tf (hm : 1 ≤ m) (u u' v : H1P (Cap.flat m K hK).body) :
    (∫ s in Ioo (-K) (0 : ℝ),
        latGammaDensity_tf m K (toCyl_tf m K hK (u + u')) (toCyl_tf m K hK v) s)
      = (∫ s in Ioo (-K) (0 : ℝ), latGammaDensity_tf m K (toCyl_tf m K hK u) (toCyl_tf m K hK v) s)
        + ∫ s in Ioo (-K) (0 : ℝ),
            latGammaDensity_tf m K (toCyl_tf m K hK u') (toCyl_tf m K hK v) s := by
  rw [toCyl_tf_add,
    ← integral_add (integrableOn_latGammaDensity_tf m K hm (toCyl_tf m K hK u) (toCyl_tf m K hK v))
      (integrableOn_latGammaDensity_tf m K hm (toCyl_tf m K hK u') (toCyl_tf m K hK v))]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
    (lateralTraceCyl_add_tf m K hm (toCyl_tf m K hK u) (toCyl_tf m K hK u'))]
    with s hs' hsmem
  have hs := hs' hsmem
  rw [latGammaDensity_tf, latGammaDensity_tf, latGammaDensity_tf,
    ← integral_add
      (integrable_lateralTraceCyl_mul_slice_tf m K hm (toCyl_tf m K hK u) (toCyl_tf m K hK v) hsmem)
      (integrable_lateralTraceCyl_mul_slice_tf m K hm (toCyl_tf m K hK u') (toCyl_tf m K hK v) hsmem)]
  refine integral_congr_ae ?_
  filter_upwards [hs] with w hw
  rw [hw]; ring

theorem latGammaIntegral_smul_left_tf (hm : 1 ≤ m) (c : ℝ) (u v : H1P (Cap.flat m K hK).body) :
    (∫ s in Ioo (-K) (0 : ℝ), latGammaDensity_tf m K (toCyl_tf m K hK (c • u)) (toCyl_tf m K hK v) s)
      = c * ∫ s in Ioo (-K) (0 : ℝ),
          latGammaDensity_tf m K (toCyl_tf m K hK u) (toCyl_tf m K hK v) s := by
  rw [toCyl_tf_smul, ← integral_const_mul]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
    (lateralTraceCyl_smul_tf m K hm c (toCyl_tf m K hK u))] with s hs' hsmem
  have hs := hs' hsmem
  rw [latGammaDensity_tf, latGammaDensity_tf, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hs] with w hw
  rw [hw]; ring

theorem gammaFormFlat_add_left_tf (hm : 1 ≤ m) (u u' v : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm (u + u') v
      = gammaFormFlat_tf m K hK hm u v + gammaFormFlat_tf m K hK hm u' v := by
  rw [gammaFormFlat_eq_tf, gammaFormFlat_eq_tf, gammaFormFlat_eq_tf,
    latGammaIntegral_add_left_tf m K hK hm u u' v, discGammaIntegral_add_left_tf m K hK u u' v]
  ring

theorem gammaFormFlat_smul_left_tf (hm : 1 ≤ m) (c : ℝ) (u v : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm (c • u) v = c * gammaFormFlat_tf m K hK hm u v := by
  rw [gammaFormFlat_eq_tf, gammaFormFlat_eq_tf,
    latGammaIntegral_smul_left_tf m K hK hm c u v, discGammaIntegral_smul_left_tf m K hK c u v]
  ring

theorem gammaFormFlat_symm_tf (hm : 1 ≤ m) (u v : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm u v = gammaFormFlat_tf m K hK hm v u := by
  rw [gammaFormFlat_eq_tf, gammaFormFlat_eq_tf]
  congr 1
  · refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards with s _
    rw [latGammaDensity_tf, latGammaDensity_tf]
    exact integral_congr_ae (Eventually.of_forall fun w => by ring)
  · exact setIntegral_congr_ae measurableSet_ball (Eventually.of_forall fun z _ => by ring)

theorem gammaFormFlat_add_right_tf (hm : 1 ≤ m) (u v v' : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm u (v + v')
      = gammaFormFlat_tf m K hK hm u v + gammaFormFlat_tf m K hK hm u v' := by
  rw [gammaFormFlat_symm_tf m K hK hm, gammaFormFlat_add_left_tf m K hK hm,
    gammaFormFlat_symm_tf m K hK hm v u, gammaFormFlat_symm_tf m K hK hm v' u]

theorem gammaFormFlat_smul_right_tf (hm : 1 ≤ m) (c : ℝ) (u v : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm u (c • v) = c * gammaFormFlat_tf m K hK hm u v := by
  rw [gammaFormFlat_symm_tf m K hK hm, gammaFormFlat_smul_left_tf m K hK hm,
    gammaFormFlat_symm_tf m K hK hm v u]

theorem gammaFormFlat_nonneg_tf (hm : 1 ≤ m) (u : H1P (Cap.flat m K hK).body) :
    0 ≤ gammaFormFlat_tf m K hK hm u u := by
  rw [gammaFormFlat_eq_tf]
  have h1 : (0 : ℝ) ≤ ∫ s in Ioo (-K) (0 : ℝ),
      latGammaDensity_tf m K (toCyl_tf m K hK u) (toCyl_tf m K hK u) s :=
    setIntegral_nonneg measurableSet_Ioo fun s _ =>
      integral_nonneg fun w => mul_self_nonneg _
  have h2 : (0 : ℝ) ≤ ∫ z in ball (0 : E) 1, discTrace_tf m K hK u z * discTrace_tf m K hK u z :=
    setIntegral_nonneg measurableSet_ball fun z _ => mul_self_nonneg _
  linarith

/-- **The `Γ`-form, bundled as a bilinear map.** -/
def bdGammaFlat_tf (hm : 1 ≤ m) :
    H1P (Cap.flat m K hK).body →ₗ[ℝ] H1P (Cap.flat m K hK).body →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (gammaFormFlat_tf m K hK hm) (gammaFormFlat_add_left_tf m K hK hm)
    (gammaFormFlat_smul_left_tf m K hK hm) (gammaFormFlat_add_right_tf m K hK hm)
    (gammaFormFlat_smul_right_tf m K hK hm)

@[simp] theorem bdGammaFlat_apply_tf (hm : 1 ≤ m) (u v : H1P (Cap.flat m K hK).body) :
    bdGammaFlat_tf m K hK hm u v = gammaFormFlat_tf m K hK hm u v := rfl

/-! ## 8. The trace inequality -/

theorem gammaFormFlat_self_le_tf (hm : 1 ≤ m) (u : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm u u
      ≤ (max (4 / (1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹) ((1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹)
          + max (2 / K) (2 * K)) * (massP u + dirichletP u) := by
  rw [gammaFormFlat_eq_tf]
  have hlat_eq : (∫ s in Ioo (-K) (0 : ℝ),
      latGammaDensity_tf m K (toCyl_tf m K hK u) (toCyl_tf m K hK u) s)
      = ∫ s in Ioo (-K) (0 : ℝ), lateralDensityCyl_tf m K (toCyl_tf m K hK u) s := by
    refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall fun s _ => ?_)
    rw [latGammaDensity_tf, lateralDensityCyl_tf]
    exact integral_congr_ae (Eventually.of_forall fun w => (sq _).symm)
  rw [hlat_eq]
  have hlat_le : (∫ s in Ioo (-K) (0 : ℝ), lateralDensityCyl_tf m K (toCyl_tf m K hK u) s)
      ≤ max (4 / (1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹) ((1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹)
        * (massP u + dirichletP u) := by
    rw [← massP_toCyl_tf m K hK u, ← dirichletP_toCyl_tf m K hK u]
    exact lateralDensityCyl_integral_le_tf m K hm (toCyl_tf m K hK u)
  have hdisc_eq : (∫ z in ball (0 : E) 1, discTrace_tf m K hK u z * discTrace_tf m K hK u z)
      = ∫ z in ball (0 : E) 1, (discTrace_tf m K hK u z) ^ 2 :=
    setIntegral_congr_ae measurableSet_ball (Eventually.of_forall fun z _ => (sq _).symm)
  rw [hdisc_eq]
  have hdisc_le := integral_discTrace_sq_le_tf m K hK u
  nlinarith [hlat_le, hdisc_le]

/-! ## 9. `vanishes_ae`: the trace kills a.e.-zero elements -/

theorem isOpen_flatBody_tf : IsOpen (Cap.flat m K hK).body := by
  rw [flatBody_eq_bulkCyl_tf m K hK]; exact isOpen_bulkCyl

theorem discTrace_ae_zero_tf (u : H1P (Cap.flat m K hK).body)
    (hu : u.toFun =ᵐ[volume.restrict (Cap.flat m K hK).body] 0) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)), discTrace_tf m K hK u z = 0 := by
  have hu' : u ∈ nullAEP (Cap.flat m K hK).body := hu
  have hgx0 : u.gx =ᵐ[volume.restrict (Cap.flat m K hK).body] 0 :=
    gx_ae_zero_of_mem_nullAEP (isOpen_flatBody_tf m K hK) hu'
  have hu_ae : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ (Cap.flat m K hK).body → u.toFun p = 0 :=
    (ae_restrict_iff' (measurableSet_body' _)).1 hu
  have hgx_ae : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ (Cap.flat m K hK).body → u.gx p = 0 :=
    (ae_restrict_iff' (measurableSet_body' _)).1 hgx0
  have h1 := ae_ae_axial hu_ae
  have h2 := ae_ae_axial hgx_ae
  have hmne : (volume.restrict (Ioo (-K) (0 : ℝ))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  haveI : (ae (volume.restrict (Ioo (-K) (0 : ℝ)))).NeBot := ae_neBot.2 hmne
  have hKab : (-K : ℝ) < 0 := by linarith
  filter_upwards [discTrace_spec_tf m K hK u,
    ae_restrict_of_ae h1, ae_restrict_of_ae h2, ae_restrict_mem measurableSet_ball]
    with z hspec hz1 hz2 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hz1' : ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))), u.toFun (s, z) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz1] with s hs
    intro hsmem
    have hmems : s ∈ axialSlice (Cap.flat m K hK) z := by
      rw [axialSlice_flat_elf m K hK hznorm]; exact hsmem
    exact hs hmems
  obtain ⟨s, hspecs, hzs1, hsmem⟩ :=
    (hspec.and (hz1'.and (ae_restrict_mem (μ := volume) measurableSet_Ioo))).exists
  have hmem : ((s, z) : CapSpace m) ∈ (Cap.flat m K hK).body := by
    have : s ∈ axialSlice (Cap.flat m K hK) z := by
      rw [axialSlice_flat_elf m K hK hznorm]; exact hsmem
    exact this
  have hu0 : u.toFun (s, z) = 0 := hzs1
  have hgxI : (∫ t in s..(0 : ℝ), u.gx (t, z)) = 0 := by
    rw [intervalIntegral_eq_integral_Ioo hsmem.2.le]
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo s (0 : ℝ) → u.gx (t, z) = 0 := by
      filter_upwards [hz2] with t ht htmem
      have hmemt : ((t, z) : CapSpace m) ∈ (Cap.flat m K hK).body := by
        have : t ∈ axialSlice (Cap.flat m K hK) z := by
          rw [axialSlice_flat_elf m K hK hznorm]
          exact ⟨hsmem.1.trans htmem.1, htmem.2⟩
        exact this
      exact ht hmemt
    rw [setIntegral_congr_ae measurableSet_Ioo hae]
    simp
  linarith [hspecs, hu0, hgxI]

theorem traceSphere_zero_tf (w : E) :
    Weak.traceSphere (1 : ℝ) (fun _ : E => (0 : ℝ)) (fun _ : E => (0 : E)) w = 0 := by
  simp [Weak.traceSphere]

/-- **The lateral trace of an a.e.-vanishing element vanishes almost everywhere.** -/
theorem lateralTraceCyl_ae_zero_tf (hm : 1 ≤ m) (u : H1P (Cap.flat m K hK).body)
    (hu : u.toFun =ᵐ[volume.restrict (Cap.flat m K hK).body] 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        lateralTraceCyl_tf m K (toCyl_tf m K hK u) (x, (w : E)) = 0 := by
  set u' := toCyl_tf m K hK u with hu'_def
  have hu0 : u'.toFun =ᵐ[volume.restrict (bulkCyl (-K) 0 m 1)] 0 := by
    rw [hu'_def, toCyl_tf_toFun, ← flatBody_eq_bulkCyl_tf m K hK]; exact hu
  have hu'' : u' ∈ nullAEP (bulkCyl (-K) 0 m 1) := hu0
  have hgz0 : u'.gz =ᵐ[volume.restrict (bulkCyl (-K) 0 m 1)] 0 :=
    gz_ae_zero_of_mem_nullAEP isOpen_bulkCyl hu''
  have h0 : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (-K) (0 : ℝ))).prod (sphereMeasure m)),
      p.1 ∈ Ioo (-K) (0 : ℝ) := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  have h1 : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (-K) (0 : ℝ))).prod (sphereMeasure m)),
      IsGoodSlice u' p.1 := Measure.quasiMeasurePreserving_fst.ae (ae_isGoodSlice u')
  have h2 := ae_radial_congr_joint_tgb (m := m) hm (a := (-K : ℝ)) (b := (0 : ℝ)) (R := (1 : ℝ)) hu0
  have h3 := ae_radial_congr_joint_tgb (m := m) hm (a := (-K : ℝ)) (b := (0 : ℝ)) (R := (1 : ℝ)) hgz0
  have hprod : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (-K) (0 : ℝ))).prod (sphereMeasure m)),
      lateralTraceCyl_tf m K u' (p.1, (p.2 : E)) = 0 := by
    filter_upwards [h0, h1, h2, h3] with p hxmem hgood hp2 hp3
    simp only [Pi.zero_apply] at hp2 hp3
    rw [lateralTraceCyl_tf_apply m K u' hxmem p.2, slice_toFun hgood, slice_grad hgood,
      traceSphere_congr_th (R := (1 : ℝ)) (v₂ := fun _ : E => (0 : ℝ)) (g₂ := fun _ : E => (0 : E))
        one_pos hp2 hp3]
    exact traceSphere_zero_tf m (p.2 : E)
  exact Measure.ae_ae_of_ae_prod hprod

theorem gammaFormFlat_eq_zero_of_ae_zero_tf (hm : 1 ≤ m) (u : H1P (Cap.flat m K hK).body)
    (hu : u.toFun =ᵐ[volume.restrict (Cap.flat m K hK).body] 0) (v : H1P (Cap.flat m K hK).body) :
    gammaFormFlat_tf m K hK hm u v = 0 := by
  rw [gammaFormFlat_eq_tf]
  have hlat0 : (∫ s in Ioo (-K) (0 : ℝ),
      latGammaDensity_tf m K (toCyl_tf m K hK u) (toCyl_tf m K hK v) s) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [lateralTraceCyl_ae_zero_tf m K hK hm u hu] with s hs
    rw [latGammaDensity_tf]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hs] with w hw
    show lateralTraceCyl_tf m K (toCyl_tf m K hK u) (s, (w:E))
        * lateralTraceCyl_tf m K (toCyl_tf m K hK v) (s, (w:E)) = 0
    rw [hw, zero_mul]
  have hdisc0 : (∫ z in ball (0 : E) 1, discTrace_tf m K hK u z * discTrace_tf m K hK v z) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [discTrace_ae_zero_tf m K hK u hu] with z hz
    show discTrace_tf m K hK u z * discTrace_tf m K hK v z = 0
    rw [hz, zero_mul]
  rw [hlat0, hdisc0]; ring

/-! ## 10. Consistency with a continuous representative -/

theorem gammaFormFlat_self_eq_capBoundary_tf (hm : 1 ≤ m) (u : H1P (Cap.flat m K hK).body)
    (hcont : ContinuousOn u.toFun (closure (Cap.flat m K hK).body)) :
    gammaFormFlat_tf m K hK hm u u = capBoundary (Cap.flat m K hK) u.toFun := by
  rw [gammaFormFlat_eq_tf, capBoundary, capLateralIntegral_flat_tf, flat_theta_elf]
  congr 1
  · have hcont' : ContinuousOn (toCyl_tf m K hK u).toFun (closure (bulkCyl (-K) 0 m 1)) := by
      rw [← toCyl_tf_toFun m K hK u] at hcont
      rwa [flatBody_eq_bulkCyl_tf m K hK] at hcont
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
      (lateralTraceCyl_eq_of_continuousOn_tf m K hm hK (toCyl_tf m K hK u) hcont')]
      with s hs' hsmem
    have hs := hs' hsmem
    rw [latGammaDensity_tf]
    refine integral_congr_ae ?_
    filter_upwards [hs] with w hw
    rw [hw, toCyl_tf_toFun, sq]
  · refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1
      (discTrace_eq_of_continuousOn_tf m K hK u hcont)] with z hz hzmem
    rw [hz hzmem, sq]

/-! ## 11. Assembly: the trace datum of the flat cap -/

/-- **The trace datum of the flat cap**, discharging `RobinCaps.Cap.CapTraceData` for
`Cap.flat m K hK`, for every `m ≥ 1` and `K > 0`. -/
noncomputable def capTraceDataFlat_tf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) :
    CapTraceData (Cap.flat m K hK) where
  trΓ u := trGammaFlat_tf m K hK hm u
  trΓ_add u v := (trGammaFlat_tf m K hK hm).map_add u v
  trΓ_smul c u := (trGammaFlat_tf m K hK hm).map_smul c u
  bdΓ := bdGammaFlat_tf m K hK hm
  bdΓ_eq u v := rfl
  bdΓ_symm u v := gammaFormFlat_symm_tf m K hK hm u v
  bdΓ_nonneg u := gammaFormFlat_nonneg_tf m K hK hm u
  trΓ_continuous u hu := gammaFormFlat_self_eq_capBoundary_tf m K hK hm u hu
  traceConst := max (4 / (1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹) ((1 : ℝ) * (((1 : ℝ) / 2) ^ (m - 1))⁻¹)
    + max (2 / K) (2 * K)
  traceConst_nonneg := by positivity
  trace_ineq u := by
    have h := gammaFormFlat_self_le_tf m K hK hm u
    rw [add_comm (dirichletP u) (massP u)]
    exact h
  vanishes_ae u hu v := gammaFormFlat_eq_zero_of_ae_zero_tf m K hK hm u hu v

/-- **The boundary form of the flat cap's trace datum is the concrete lateral-plus-disc
integral.** -/
theorem capTraceDataFlat_bdΓ_eq_tf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K)
    (u v : H1P (Cap.flat m K hK).body) :
    (capTraceDataFlat_tf m hm K hK).bdΓ u v
      = (∫ s in Ioo (-K) (0 : ℝ),
          latGammaDensity_tf m K (toCyl_tf m K hK u) (toCyl_tf m K hK v) s)
        + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            discTrace_tf m K hK u z * discTrace_tf m K hK v z := by
  show gammaFormFlat_tf m K hK hm u v = _
  exact gammaFormFlat_eq_tf m K hK hm u v

end

end Cap
end RobinCaps
