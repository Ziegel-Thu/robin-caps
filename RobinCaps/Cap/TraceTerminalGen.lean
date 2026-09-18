import RobinCaps.Cap.TraceDataFlat
import RobinCaps.Cap.CapGeometry

/-!
# The terminal (axial-exit) trace on an arbitrary admissible cap

For a general admissible cap `C : Cap m` the axial slice through a transverse point `z` of the
entrance disk is the *initial* interval `(-K, e(z))` with `e(z) = exitTime C z`
(`RobinCaps.Cap.axialSlice_eq`).  `RobinCaps/Cap/SliceAC.lean` constructs the trace at the
**entrance** end `s = -K` (`entranceVal`), and `RobinCaps/Cap/TraceDataFlat.lean` constructs the
trace at the **exit** end for the flat cap, where the exit time is the constant `0`
(`discTrace_tf`).

This file carries out the exit-end construction for an arbitrary cap, i.e. with the *variable*
exit time `e(z)`:

* `exitVal_ttg`, `measurable_exitVal_ttg`, `exitVal_spec_ttg`: the measurable terminal trace and
  the slice-wise fundamental theorem of calculus
  `u(s,z) = exitVal(z) - ∫_s^{e(z)} ∂ₓu(t,z) dt`;
* `exitVal_add_ae_ttg`, `exitVal_smul_ae_ttg`: a.e. linearity;
* `exitVal_sq_integral_le_ttg`: the `L²` trace bound on the *interior* disk `B(0, θ a)`, where the
  slice length `ℓ(z) = e(z) + K` is bounded below by `a + K`;
* `exitVal_eq_of_continuousOn_ttg`: consistency with a continuous representative;
* `exitVal_ae_zero_ttg`: the trace kills a.e.-vanishing elements.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology Interval

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Transverse

noncomputable section

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## 1. The backward axial primitive, anchored at the variable exit time -/

/-- The region `{(t,p) | p.1 < t < e(p.2)}` used to define the backward axial primitive.  Unlike
the flat case the right endpoint is the (merely measurable) exit time. -/
theorem measurableSet_primRegionExit_ttg (C : Cap m) :
    MeasurableSet {r : ℝ × CapSpace m | r.2.1 < r.1 ∧ r.1 < exitTime C r.2.2} := by
  have h1 : MeasurableSet {r : ℝ × CapSpace m | r.2.1 < r.1} :=
    (isOpen_lt (continuous_fst.comp continuous_snd) continuous_fst).measurableSet
  have h2 : MeasurableSet {r : ℝ × CapSpace m | r.1 < exitTime C r.2.2} :=
    measurableSet_lt measurable_fst ((measurable_exitTime C).comp measurable_snd.snd)
  exact h1.inter h2

/-- The integration kernel of the **backward** axial primitive of `∂ₓu`, from the exit point
`e(z)`. -/
def primKernelExit_ttg (C : Cap m) (u : H1P C.body) : ℝ × CapSpace m → ℝ :=
  {r : ℝ × CapSpace m | r.2.1 < r.1 ∧ r.1 < exitTime C r.2.2}.indicator
    fun r => repGx C u (r.1, r.2.2)

/-- The **backward axial primitive** `p ↦ ∫_{p.1}^{e(p.2)} ∂ₓu(t, p.2) dt`, in a manifestly
measurable form. -/
def slicePrimExit_ttg (C : Cap m) (u : H1P C.body) (p : CapSpace m) : ℝ :=
  ∫ t, primKernelExit_ttg C u (t, p)

theorem stronglyMeasurable_primKernelExit_ttg (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (primKernelExit_ttg C u) := by
  refine StronglyMeasurable.indicator ?_ (measurableSet_primRegionExit_ttg C)
  exact (stronglyMeasurable_repGx C u).comp_measurable
    (by fun_prop : Measurable fun r : ℝ × CapSpace m => (r.1, r.2.2))

theorem stronglyMeasurable_slicePrimExit_ttg (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (slicePrimExit_ttg C u) :=
  (stronglyMeasurable_primKernelExit_ttg C u).integral_prod_left'

theorem slicePrimExit_eq_ttg (C : Cap m) (u : H1P C.body) (s : ℝ) (z : E) :
    slicePrimExit_ttg C u (s, z) = ∫ t in Ioo s (exitTime C z), repGx C u (t, z) := by
  rw [slicePrimExit_ttg, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [primKernelExit_ttg, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioo]

/-! ## 2. The terminal trace -/

/-- The integrand whose slice average is the terminal value. -/
def exitIntegrand_ttg (C : Cap m) (u : H1P C.body) : CapSpace m → ℝ :=
  C.body.indicator fun p => repFun C u p + slicePrimExit_ttg C u p

/-- **The terminal (axial-exit) trace of a weak-`H¹` function on an arbitrary cap.**  On almost
every axial line the function `s ↦ u(s,z) + ∫_s^{e(z)} ∂ₓu(t,z) dt` is a.e. constant, and
`exitVal_ttg C u z` is that constant, written as the average over the full axial slice
`(-K, e(z))` so as to be manifestly measurable. -/
def exitVal_ttg (C : Cap m) (u : H1P C.body) (z : E) : ℝ :=
  (∫ s, exitIntegrand_ttg C u (s, z)) / (exitTime C z + C.K)

theorem stronglyMeasurable_exitIntegrand_ttg (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (exitIntegrand_ttg C u) :=
  ((stronglyMeasurable_repFun C u).add
    (stronglyMeasurable_slicePrimExit_ttg C u)).indicator (measurableSet_body' C)

/-- **The terminal trace is measurable.** -/
theorem measurable_exitVal_ttg (C : Cap m) (u : H1P C.body) : Measurable (exitVal_ttg C u) := by
  have h1 : StronglyMeasurable fun z : E => ∫ s, exitIntegrand_ttg C u (s, z) :=
    (stronglyMeasurable_exitIntegrand_ttg C u).integral_prod_left'
  exact h1.measurable.div ((measurable_exitTime C).add measurable_const)

/-! ## 3. The defining property of the terminal trace -/

/-- **The exit constant exists on almost every axial line.**  This is the entrance statement
(`RobinCaps.Cap.entranceVal_spec`) re-anchored at the right endpoint `e(z)` of the slice. -/
theorem exists_exitConst_ttg (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)), ∃ c : ℝ,
      ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) (exitTime C z))),
        u.toFun (s, z) = c - ∫ t in s..(exitTime C z), u.gx (t, z) := by
  filter_upwards [entranceVal_spec C u,
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hspec hg hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-C.K) e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hg
  have hII : ∀ y w : ℝ, y ∈ Icc (-C.K) e → w ∈ Icc (-C.K) e →
      IntervalIntegrable (fun t => u.gx (t, z)) volume y w := by
    intro y w hy hw'
    refine hgI.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le hKe.le]; exact hy
    · rw [uIcc_of_le hKe.le]; exact hw'
  refine ⟨entranceVal C u z + ∫ t in (-C.K)..e, u.gx (t, z), ?_⟩
  filter_upwards [hspec, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  have hsIcc : s ∈ Icc (-C.K) e := Ioo_subset_Icc_self hsmem
  have hsplit : (∫ t in (-C.K)..e, u.gx (t, z))
      = (∫ t in (-C.K)..s, u.gx (t, z)) + ∫ t in s..e, u.gx (t, z) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hII (-C.K) s ⟨le_rfl, hKe.le⟩ hsIcc) (hII s e hsIcc ⟨hKe.le, le_rfl⟩)).symm
  rw [hs, hsplit]; ring

/-- **The terminal-trace spec.**  For almost every `z` in the entrance ball, the axial slice of
`u` is (a.e. equal to) the absolutely continuous function
`s ↦ exitVal_ttg C u z - ∫_s^{e(z)} ∂ₓu`. -/
theorem exitVal_spec_ttg (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)),
      ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) (exitTime C z))),
        u.toFun (s, z) = exitVal_ttg C u z - ∫ t in s..(exitTime C z), u.gx (t, z) := by
  filter_upwards [exists_exitConst_ttg C u, ae_restrict_of_ae (ae_slice_repFun C u),
    ae_restrict_of_ae (ae_slice_repGx C u), ae_restrict_mem measurableSet_ball]
    with z hc hrf hrg hzb
  obtain ⟨c, hc⟩ := hc
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  have hmemslice : ∀ s : ℝ, s ∈ Ioo (-C.K) e → ((s, z) : CapSpace m) ∈ C.body := by
    intro s hs
    have hmm : s ∈ axialSlice C z := by rw [axialSlice_eq]; exact hs
    exact hmm
  have hprim : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)),
      slicePrimExit_ttg C u (s, z) = ∫ t in s..e, u.gx (t, z) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [slicePrimExit_eq_ttg, ← hedef, intervalIntegral_eq_setIntegral_Ioo hs.2.le]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrg] with t ht htmem
    exact ht (hmemslice t ⟨hs.1.trans htmem.1, htmem.2⟩)
  have hconst : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)),
      repFun C u (s, z) + slicePrimExit_ttg C u (s, z) = c := by
    filter_upwards [hc, hprim, ae_restrict_of_ae hrf, ae_restrict_mem measurableSet_Ioo]
      with s hs1 hs2 hs3 hs4
    rw [hs3 (hmemslice s hs4), hs2, hs1]; ring
  have hint : (∫ s, exitIntegrand_ttg C u (s, z)) = (e + C.K) * c := by
    rw [exitIntegrand_ttg, integral_indicator_body_line C
      (fun p => repFun C u p + slicePrimExit_ttg C u p) z, ← hedef,
      setIntegral_congr_ae measurableSet_Ioo ((ae_restrict_iff' measurableSet_Ioo).1 hconst),
      setIntegral_const, Real.volume_real_Ioo_of_le hKe.le, smul_eq_mul]
    ring
  have hne : e + C.K ≠ 0 := by linarith
  have hev : exitVal_ttg C u z = c := by
    rw [exitVal_ttg, hint, ← hedef]
    field_simp
  rw [hev]
  filter_upwards [hc] with s hs using hs

/-! ## 4. A.e. linearity -/

/-- **`exitVal_ttg` is a.e. additive in `u`.**  Both sides are pinned, for a.e. `z`, by the value
of the slice at a single common point of the slice. -/
theorem exitVal_add_ae_ttg (C : Cap m) (u v : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)),
      exitVal_ttg C (u + v) z = exitVal_ttg C u z + exitVal_ttg C v z := by
  filter_upwards [exitVal_spec_ttg C u, exitVal_spec_ttg C v, exitVal_spec_ttg C (u + v),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2)),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C v.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hu hv huv hgu hgv hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  have hmne : (volume.restrict (Ioo (-C.K) e)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  haveI : (ae (volume.restrict (Ioo (-C.K) e))).NeBot := ae_neBot.2 hmne
  have hguI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-C.K) e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hgu
  have hgvI : IntervalIntegrable (fun t => v.gx (t, z)) volume (-C.K) e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hgv
  obtain ⟨s, hus, hvs, huvs, hsmem⟩ :=
    (hu.and (hv.and (huv.and (ae_restrict_mem (μ := volume) measurableSet_Ioo)))).exists
  have hsIcc : s ∈ Icc (-C.K) e := Ioo_subset_Icc_self hsmem
  have heIcc : e ∈ Icc (-C.K) e := ⟨hKe.le, le_rfl⟩
  have hII : ∀ y w : ℝ, y ∈ Icc (-C.K) e → w ∈ Icc (-C.K) e →
      IntervalIntegrable (fun t => u.gx (t, z)) volume y w ∧
        IntervalIntegrable (fun t => v.gx (t, z)) volume y w := by
    intro y w hy hw
    refine ⟨hguI.mono_set (uIcc_subset_uIcc ?_ ?_), hgvI.mono_set (uIcc_subset_uIcc ?_ ?_)⟩ <;>
      rw [uIcc_of_le hKe.le] <;> assumption
  have hsuv : (u + v).toFun (s, z) = u.toFun (s, z) + v.toFun (s, z) := by simp [H1P.add_toFun]
  have hIadd : (∫ t in s..e, (u + v).gx (t, z))
      = (∫ t in s..e, u.gx (t, z)) + ∫ t in s..e, v.gx (t, z) := by
    have hcongr : (∫ t in s..e, (u + v).gx (t, z))
        = ∫ t in s..e, (u.gx (t, z) + v.gx (t, z)) :=
      intervalIntegral.integral_congr fun t _ => by simp [H1P.add_gx]
    rw [hcongr, intervalIntegral.integral_add (hII s e hsIcc heIcc).1 (hII s e hsIcc heIcc).2]
  linarith [hus, hvs, huvs, hsuv, hIadd]

/-- **`exitVal_ttg` is a.e. homogeneous in `u`.** -/
theorem exitVal_smul_ae_ttg (C : Cap m) (c : ℝ) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)),
      exitVal_ttg C (c • u) z = c * exitVal_ttg C u z := by
  filter_upwards [exitVal_spec_ttg C u, exitVal_spec_ttg C (c • u),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2)),
    ae_restrict_mem measurableSet_ball] with z hu hcu hgu hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  have hmne : (volume.restrict (Ioo (-C.K) e)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  haveI : (ae (volume.restrict (Ioo (-C.K) e))).NeBot := ae_neBot.2 hmne
  obtain ⟨s, hus, hcus, hsmem⟩ :=
    (hu.and (hcu.and (ae_restrict_mem (μ := volume) measurableSet_Ioo))).exists
  have hscu : (c • u).toFun (s, z) = c * u.toFun (s, z) := by simp [H1P.smul_toFun]
  have hIsmul : (∫ t in s..e, (c • u).gx (t, z)) = c * ∫ t in s..e, u.gx (t, z) := by
    have hcongr : (∫ t in s..e, (c • u).gx (t, z)) = ∫ t in s..e, c * u.gx (t, z) :=
      intervalIntegral.integral_congr fun t _ => by simp [H1P.smul_gx]
    rw [hcongr, intervalIntegral.integral_const_mul]
  have hgoal : exitVal_ttg C (c • u) z - (∫ t in s..e, (c • u).gx (t, z))
      = c * (exitVal_ttg C u z - ∫ t in s..e, u.gx (t, z)) := by
    rw [← hcus, hscu, hus]
  rw [hIsmul, mul_sub] at hgoal
  linarith [hgoal]

/-! ## 5. The absolutely continuous representative anchored at the exit -/

/-- **The absolutely continuous representative of the axial slice, anchored at the exit `e(z)`.**
Mirrors `RobinCaps.Cap.exists_h1_axialSlice`, shifted so that the value at the *right* endpoint
`ℓ(z) = e(z)+K` of the translated interval `(0, ℓ(z))` is `exitVal_ttg`. -/
theorem exists_h1_axialSliceExit_ttg (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)),
      ∃ w : Sobolev.H1 (exitTime C z + C.K),
        w.toFun (exitTime C z + C.K) = exitVal_ttg C u z ∧
        w.toFun =ᵐ[volume.restrict (Ioo (0 : ℝ) (exitTime C z + C.K))]
          (fun x => u.toFun (x - C.K, z)) ∧
        deriv w.toFun =ᵐ[volume.restrict (Ioo (0 : ℝ) (exitTime C z + C.K))]
          (fun x => u.gx (x - C.K, z)) := by
  filter_upwards [exitVal_spec_ttg C u,
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2)),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C u.gx_memL2.integrable_sq),
    ae_restrict_mem measurableSet_ball] with z hc hg hg2 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  set ℓ : ℝ := e + C.K with hℓdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; linarith
  have hlK : ℓ - C.K = e := by rw [hℓdef]; ring
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
  have hc' : ∀ᵐ x ∂(volume : Measure ℝ), x - C.K ∈ Ioo (-C.K) e →
      u.toFun (x - C.K, z) = exitVal_ttg C u z - ∫ t in (x - C.K)..e, u.gx (t, z) :=
    (measurePreserving_sub_right (volume : Measure ℝ) C.K).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).1 hc)
  refine ⟨Sobolev.primitiveH1 hℓ.le hGI hG2I
      (exitVal_ttg C u z - ∫ t in (0 : ℝ)..ℓ, u.gx (t - C.K, z)), ?_, ?_, ?_⟩
  · rw [Sobolev.primitiveH1_toFun]; ring
  · rw [Sobolev.primitiveH1_toFun, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hc'] with x hx hxmem
    have hmem : x - C.K ∈ Ioo (-C.K) e :=
      ⟨by linarith [hxmem.1], by rw [← hlK]; linarith [hxmem.2]⟩
    show (exitVal_ttg C u z - ∫ t in (0 : ℝ)..ℓ, u.gx (t - C.K, z))
        + (∫ t in (0 : ℝ)..x, u.gx (t - C.K, z)) = u.toFun (x - C.K, z)
    rw [hx hmem]
    have hsplit : (∫ t in (0 : ℝ)..ℓ, u.gx (t - C.K, z))
        = (∫ t in (0 : ℝ)..x, u.gx (t - C.K, z)) + ∫ t in x..ℓ, u.gx (t - C.K, z) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hGI.mono_set
          (by rw [uIcc_of_le hℓ.le, uIcc_of_le hxmem.1.le]
              exact Icc_subset_Icc le_rfl hxmem.2.le))
        (hGI.mono_set
          (by rw [uIcc_of_le hℓ.le, uIcc_of_le hxmem.2.le]
              exact Icc_subset_Icc hxmem.1.le le_rfl))).symm
    have hshift : (∫ t in x..ℓ, u.gx (t - C.K, z)) = ∫ t in (x - C.K)..e, u.gx (t, z) := by
      have h := intervalIntegral.integral_comp_sub_right (fun t => u.gx (t, z)) C.K
        (a := x) (b := ℓ)
      rw [hlK] at h
      exact h
    rw [hsplit, hshift]
    ring
  · rw [Sobolev.primitiveH1_toFun]
    have hae := Sobolev.ae_deriv_primitive hGI
      (exitVal_ttg C u z - ∫ t in (0 : ℝ)..ℓ, u.gx (t - C.K, z)) (x₀ := (0 : ℝ)) left_mem_uIcc
    have hsub : Ioo (0 : ℝ) ℓ ⊆ Ι (0 : ℝ) ℓ := by
      rw [uIoc_of_le hℓ.le]; exact Ioo_subset_Ioc_self
    exact hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))

/-! ## 6. The one-dimensional trace bound on an axial slice -/

/-- **The terminal value is controlled by the axial slice data.**  This is the one-dimensional
trace inequality `RobinCaps.Sobolev.endpoint_ell_sq_le` at the *right* endpoint, applied to the
absolutely continuous representative of the axial slice. -/
theorem ae_exitVal_sq_le_ttg (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)),
      exitVal_ttg C u z ^ 2
        ≤ (2 / (exitTime C z + C.K)) * axMass_el C u z
          + (2 * (exitTime C z + C.K)) * axEnergy_el C u z := by
  filter_upwards [exists_h1_axialSliceExit_ttg C u,
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
  have hmass : Sobolev.mass (exitTime C z + C.K) w = axMass_el C u z := by
    rw [Sobolev.mass, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le]
    have h1 : (fun x => w.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) (exitTime C z + C.K))]
          fun x => u.toFun (x - C.K, z) ^ 2 := by
      filter_upwards [hwf] with x hx
      rw [hx]
    rw [integral_congr_ae h1, ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le,
      intervalIntegral.integral_comp_sub_right (fun s => u.toFun (s, z) ^ 2) C.K,
      show (0 : ℝ) - C.K = -C.K by ring, show exitTime C z + C.K - C.K = exitTime C z by ring,
      Sobolev.intervalIntegral_eq_setIntegral_Ioo hKe.le, axMass_el]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrf] with s hs hsmem
    rw [hs (hmemslice s hsmem)]
  have hdir : Sobolev.dirichlet (exitTime C z + C.K) w = axEnergy_el C u z := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le]
    have h1 : (fun x => deriv w.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) (exitTime C z + C.K))]
          fun x => u.gx (x - C.K, z) ^ 2 := by
      filter_upwards [hwd] with x hx
      rw [hx]
    rw [integral_congr_ae h1, ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le,
      intervalIntegral.integral_comp_sub_right (fun s => u.gx (s, z) ^ 2) C.K,
      show (0 : ℝ) - C.K = -C.K by ring, show exitTime C z + C.K - C.K = exitTime C z by ring,
      Sobolev.intervalIntegral_eq_setIntegral_Ioo hKe.le, axEnergy_el]
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hrg] with s hs hsmem
    rw [hs (hmemslice s hsmem)]
  have hkey := Sobolev.endpoint_ell_sq_le w hℓ
  rw [hw0, hmass, hdir] at hkey
  exact hkey

/-! ## 7. The `L²` bound on an interior transverse disk

For `‖z‖ < θ a` with `a ∈ (-K,0)` the antitonicity of `θ` gives `‖z‖ < θ s` for every
`s ∈ (-K,a]`, i.e. `a < e(z)`; hence the slice length `ℓ(z) = e(z)+K` lies in `(a+K, K]` and the
one-dimensional bound becomes uniform. -/

/-- The pointwise majorant of the squared terminal trace on the disk `B(0, θ a)`. -/
def majFunExit_ttg (C : Cap m) (a : ℝ) (u : H1P C.body) (z : E) : ℝ :=
  (2 / (a + C.K)) * axMass_el C u z + (2 * C.K) * axEnergy_el C u z

/-- **The key geometric fact**: a transverse point of the disk of radius `θ a` has not left the
cap at the axial coordinate `a`. -/
theorem lt_exitTime_of_mem_ball_theta_ttg (C : Cap m) {a : ℝ} (ha : a ∈ Ioo (-C.K) 0) {z : E}
    (hz : ‖z‖ < C.θ a) : a < exitTime C z :=
  (mem_ball_theta_iff_lt_exitTime C ha z).1 hz

theorem ball_theta_subset_ball_one_ttg (C : Cap m) {a : ℝ} (ha : a ∈ Ioo (-C.K) 0) :
    ball (0 : E) (C.θ a) ⊆ ball (0 : E) 1 :=
  ball_subset_ball (C.θ_le_one a ha)

/-- **The uniform pointwise bound on the disk `B(0, θ a)`.** -/
theorem ae_exitVal_sq_le_maj_ttg (C : Cap m) {a : ℝ} (ha : a ∈ Ioo (-C.K) 0) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) (C.θ a))),
      exitVal_ttg C u z ^ 2 ≤ majFunExit_ttg C a u z := by
  have hsub := ball_theta_subset_ball_one_ttg C ha
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (ae_exitVal_sq_le_ttg C u),
    ae_restrict_mem measurableSet_ball] with z h1 hzb
  have hz : ‖z‖ < C.θ a := mem_ball_zero_iff.1 hzb
  have hlt : a < exitTime C z := lt_exitTime_of_mem_ball_theta_ttg C ha hz
  have he0 : exitTime C z ≤ 0 := exitTime_le_zero C z
  have hak : (0 : ℝ) < a + C.K := by linarith [ha.1]
  have hℓ : 0 < exitTime C z + C.K := by linarith
  have h2l : 2 / (exitTime C z + C.K) ≤ 2 / (a + C.K) := by gcongr
  have hM := axMass_nonneg_el C u z
  have hA := axEnergy_nonneg_el C u z
  have t1 : (2 / (exitTime C z + C.K)) * axMass_el C u z
      ≤ (2 / (a + C.K)) * axMass_el C u z := mul_le_mul_of_nonneg_right h2l hM
  have t2 : (2 * (exitTime C z + C.K)) * axEnergy_el C u z
      ≤ (2 * C.K) * axEnergy_el C u z :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  rw [majFunExit_ttg]
  linarith

theorem integrableOn_majFunExit_ttg (C : Cap m) (a : ℝ) (u : H1P C.body) (R : ℝ) :
    IntegrableOn (majFunExit_ttg C a u) (ball (0 : E) R) volume :=
  ((integrable_axMass_el C u).integrableOn.const_mul _).add
    ((integrable_axEnergy_el C u).integrableOn.const_mul _)

/-- **The integrated majorant bound.**  Mirrors `RobinCaps.Cap.integral_majFun_le_elf`. -/
theorem integral_majFunExit_le_ttg (C : Cap m) {a : ℝ} (ha : a ∈ Ioo (-C.K) 0)
    (u : H1P C.body) :
    (∫ z in ball (0 : E) (C.θ a), majFunExit_ttg C a u z)
      ≤ max (2 / (a + C.K)) (2 * C.K) * (massP u + dirichletP u) := by
  have hak : (0 : ℝ) < a + C.K := by linarith [ha.1]
  set M : ℝ := ∫ p in C.body, repFun C u p ^ 2 with hM
  set A : ℝ := ∫ p in C.body, repGx C u p ^ 2 with hA
  set B : ℝ := ∫ p in C.body, ‖repGz_el C u p‖ ^ 2 with hB
  have hM0 : 0 ≤ M := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hA0 : 0 ≤ A := setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_body' _) fun p _ => by positivity
  have hmass : massP u = M := massP_eq_rep_el C u
  have hdir : dirichletP u = A + B := dirichletP_eq_rep_el C u
  have hax : (∫ z in ball (0 : E) (C.θ a), axMass_el C u z) ≤ M := by
    rw [hM, ← integral_axMass_el C u]
    exact setIntegral_le_integral (integrable_axMass_el C u)
      (Eventually.of_forall fun z => axMass_nonneg_el _ _ _)
  have hae : (∫ z in ball (0 : E) (C.θ a), axEnergy_el C u z) ≤ A := by
    rw [hA, ← integral_axEnergy_el C u]
    exact setIntegral_le_integral (integrable_axEnergy_el C u)
      (Eventually.of_forall fun z => axEnergy_nonneg_el _ _ _)
  have hI1 : IntegrableOn (fun z => (2 / (a + C.K)) * axMass_el C u z)
      (ball (0 : E) (C.θ a)) volume :=
    (integrable_axMass_el C u).integrableOn.const_mul _
  have hI2 : IntegrableOn (fun z => (2 * C.K) * axEnergy_el C u z)
      (ball (0 : E) (C.θ a)) volume :=
    (integrable_axEnergy_el C u).integrableOn.const_mul _
  have hsplit : (∫ z in ball (0 : E) (C.θ a), majFunExit_ttg C a u z)
      = (2 / (a + C.K)) * (∫ z in ball (0 : E) (C.θ a), axMass_el C u z)
        + (2 * C.K) * (∫ z in ball (0 : E) (C.θ a), axEnergy_el C u z) := by
    simp only [majFunExit_ttg]
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul]
  rw [hsplit, hmass, hdir]
  have h1nn : (0 : ℝ) ≤ 2 / (a + C.K) := div_nonneg (by norm_num) hak.le
  have h2nn : (0 : ℝ) ≤ 2 * C.K := by linarith [C.hK]
  have hterm1 : (2 / (a + C.K)) * (∫ z in ball (0 : E) (C.θ a), axMass_el C u z)
      ≤ max (2 / (a + C.K)) (2 * C.K) * M :=
    (mul_le_mul_of_nonneg_left hax h1nn).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)
  have hterm2 : (2 * C.K) * (∫ z in ball (0 : E) (C.θ a), axEnergy_el C u z)
      ≤ max (2 / (a + C.K)) (2 * C.K) * A :=
    (mul_le_mul_of_nonneg_left hae h2nn).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0)
  have hmax0 : (0 : ℝ) ≤ max (2 / (a + C.K)) (2 * C.K) := le_trans h1nn (le_max_left _ _)
  have hexpand : max (2 / (a + C.K)) (2 * C.K) * (M + (A + B))
      = max (2 / (a + C.K)) (2 * C.K) * M + max (2 / (a + C.K)) (2 * C.K) * A
        + max (2 / (a + C.K)) (2 * C.K) * B := by ring
  rw [hexpand]
  have hBnn : 0 ≤ max (2 / (a + C.K)) (2 * C.K) * B := mul_nonneg hmax0 hB0
  linarith [hterm1, hterm2, hBnn]

/-- **The `L²` trace bound for the terminal trace on the interior disk `B(0, θ a)`.** -/
theorem exitVal_sq_integral_le_ttg (C : Cap m) {a : ℝ} (ha : a ∈ Ioo (-C.K) 0)
    (u : H1P C.body) :
    IntegrableOn (fun z => exitVal_ttg C u z ^ 2) (ball (0 : E) (C.θ a)) volume ∧
      (∫ z in ball (0 : E) (C.θ a), exitVal_ttg C u z ^ 2)
        ≤ max (2 / (a + C.K)) (2 * C.K) * (massP u + dirichletP u) := by
  have hmeas : AEStronglyMeasurable (exitVal_ttg C u)
      (volume.restrict (ball (0 : E) (C.θ a))) :=
    (measurable_exitVal_ttg C u).aestronglyMeasurable
  have hint : IntegrableOn (fun z => exitVal_ttg C u z ^ 2) (ball (0 : E) (C.θ a)) volume := by
    refine Integrable.mono' (integrableOn_majFunExit_ttg C a u (C.θ a)) (hmeas.pow 2) ?_
    filter_upwards [ae_exitVal_sq_le_maj_ttg C ha u] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  refine ⟨hint, ?_⟩
  have hstep : (∫ z in ball (0 : E) (C.θ a), exitVal_ttg C u z ^ 2)
      ≤ ∫ z in ball (0 : E) (C.θ a), majFunExit_ttg C a u z :=
    integral_mono_ae hint (integrableOn_majFunExit_ttg C a u (C.θ a))
      (ae_exitVal_sq_le_maj_ttg C ha u)
  exact hstep.trans (integral_majFunExit_le_ttg C ha u)

/-! ## 8. Consistency with a continuous representative -/

/-- **The closed axial slice lies in the closure of the body.**  In particular the exit point
`(e(z), z)` does. -/
theorem axialPt_mem_closure_body_ttg (C : Cap m) {z : E} (hz : ‖z‖ < 1) {s : ℝ}
    (hs : s ∈ Icc (-C.K) (exitTime C z)) : ((s, z) : CapSpace m) ∈ closure C.body := by
  have hKe : -C.K < exitTime C z := (exitTime_mem C hz).1
  have hs' : s ∈ closure (Ioo (-C.K) (exitTime C z)) := by
    rw [closure_Ioo (ne_of_lt hKe)]; exact hs
  have himg : (fun t : ℝ => ((t, z) : CapSpace m)) '' Ioo (-C.K) (exitTime C z) ⊆ C.body := by
    rintro _ ⟨t, ht, rfl⟩
    have hmm : t ∈ axialSlice C z := by rw [axialSlice_eq]; exact ht
    exact hmm
  have hmap : (fun t : ℝ => ((t, z) : CapSpace m)) '' closure (Ioo (-C.K) (exitTime C z))
      ⊆ closure ((fun t : ℝ => ((t, z) : CapSpace m)) '' Ioo (-C.K) (exitTime C z)) :=
    image_closure_subset_closure_image (continuous_id.prodMk continuous_const)
  exact closure_mono himg (hmap (mem_image_of_mem _ hs'))

/-- **Consistency of the terminal trace with a continuous representative.**  If `u.toFun` is
continuous on the closure of the cap body, then for a.e. `z` in the entrance ball the terminal
trace agrees with the value of `u` at the exit point `(e(z), z)`. -/
theorem exitVal_eq_of_continuousOn_ttg (C : Cap m) (u : H1P C.body)
    (hcont : ContinuousOn u.toFun (closure C.body)) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)),
      exitVal_ttg C u z = u.toFun (exitTime C z, z) := by
  filter_upwards [exitVal_spec_ttg C u, ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2))]
    with z hz hzb hgOn
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  have hgI : IntervalIntegrable (fun t => u.gx (t, z)) volume (-C.K) e :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hgOn
  have hmapsto : MapsTo (fun s : ℝ => ((s, z) : CapSpace m)) (Icc (-C.K) e) (closure C.body) :=
    fun s hs => axialPt_mem_closure_body_ttg C hznorm hs
  have h1 : ContinuousOn (fun s => u.toFun (s, z)) (Icc (-C.K) e) :=
    hcont.comp (continuous_id.prodMk continuous_const).continuousOn hmapsto
  have h2 : ContinuousOn (fun s => exitVal_ttg C u z - ∫ t in s..e, u.gx (t, z))
      (Icc (-C.K) e) := by
    have heq : (fun s => exitVal_ttg C u z - ∫ t in s..e, u.gx (t, z))
        = fun s => exitVal_ttg C u z + ∫ t in e..s, u.gx (t, z) := by
      funext s
      rw [intervalIntegral.integral_symm e s]
      ring
    rw [heq]
    have hmidIcc : e ∈ uIcc (-C.K) e := by
      rw [uIcc_of_le hKe.le]; exact right_mem_Icc.2 hKe.le
    have hcontprim : ContinuousOn (fun s => ∫ t in e..s, u.gx (t, z)) (uIcc (-C.K) e) :=
      intervalIntegral.continuousOn_primitive_interval' hgI hmidIcc
    rw [uIcc_of_le hKe.le] at hcontprim
    exact continuousOn_const.add hcontprim
  have hfin := eq_of_ae_eq_of_continuousOn hKe h1 h2 hz
  rw [intervalIntegral.integral_same, sub_zero] at hfin
  exact hfin.symm

/-! ## 9. The terminal trace kills a.e.-vanishing elements -/

/-- **Vanishing.**  If `u.toFun` vanishes a.e. on the body, so does its terminal trace. -/
theorem exitVal_ae_zero_ttg (C : Cap m) (u : H1P C.body)
    (h0 : u.toFun =ᵐ[volume.restrict C.body] 0) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : E) 1)), exitVal_ttg C u z = 0 := by
  have hu' : u ∈ nullAEP C.body := h0
  have hgx0 : u.gx =ᵐ[volume.restrict C.body] 0 :=
    gx_ae_zero_of_mem_nullAEP (isOpen_body_cg C) hu'
  have hu_ae : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → u.toFun p = 0 :=
    (ae_restrict_iff' (measurableSet_body' C)).1 h0
  have hgx_ae : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → u.gx p = 0 :=
    (ae_restrict_iff' (measurableSet_body' C)).1 hgx0
  have h1 := ae_ae_axial hu_ae
  have h2 := ae_ae_axial hgx_ae
  filter_upwards [exitVal_spec_ttg C u, ae_restrict_of_ae h1, ae_restrict_of_ae h2,
    ae_restrict_mem measurableSet_ball] with z hspec hz1 hz2 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  set e := exitTime C z with hedef
  have hmne : (volume.restrict (Ioo (-C.K) e)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  haveI : (ae (volume.restrict (Ioo (-C.K) e))).NeBot := ae_neBot.2 hmne
  have hmemslice : ∀ s : ℝ, s ∈ Ioo (-C.K) e → ((s, z) : CapSpace m) ∈ C.body := by
    intro s hs
    have hmm : s ∈ axialSlice C z := by rw [axialSlice_eq]; exact hs
    exact hmm
  have hz1' : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)), u.toFun (s, z) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz1] with s hs hsmem
    exact hs (hmemslice s hsmem)
  obtain ⟨s, hspecs, hzs1, hsmem⟩ :=
    (hspec.and (hz1'.and (ae_restrict_mem (μ := volume) measurableSet_Ioo))).exists
  have hgxI : (∫ t in s..e, u.gx (t, z)) = 0 := by
    rw [Sobolev.intervalIntegral_eq_setIntegral_Ioo hsmem.2.le]
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo s e → u.gx (t, z) = 0 := by
      filter_upwards [hz2] with t ht htmem
      exact ht (hmemslice t ⟨hsmem.1.trans htmem.1, htmem.2⟩)
    rw [setIntegral_congr_ae measurableSet_Ioo hae]
    simp
  linarith [hspecs, hzs1, hgxI]

end

end Cap
end RobinCaps
