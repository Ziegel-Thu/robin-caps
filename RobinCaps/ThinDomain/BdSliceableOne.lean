import RobinCaps.ThinDomain.BulkEnergy
import RobinCaps.Transverse.GroundStateOneFull

/-!
# `BdSliceable` for the transverse trace form in dimension `m = 1`

`RobinCaps/ThinDomain/BulkEnergy.lean` records the single analytic fact about an *abstract*
transverse boundary form `bd` that the bulk separation needs, namely

```
structure BdSliceable (a b : ℝ) (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) : Prop where
  integrableOn : ∀ u v : H1P (bulkCyl a b m R),
    IntegrableOn (fun x => bd (slice u x) (slice v x)) (Ioo a b)
```

This file **proves** it for `m = 1` and the concrete trace form
`RobinCaps.Transverse.bdTr R`, i.e. produces `bdSliceable_bdTr : BdSliceable a b (bdTr R)`.

## The two halves of the statement

*Integrability of the majorant* is immediate.  For every `v : TransH1 1 R` the one-dimensional
trace inequality `RobinCaps.Sobolev.trace_ineq`, applied to the absolutely continuous
representative `rep hR v : Sobolev.H1 (2R)` of `RobinCaps/Transverse/GroundStateOneFull.lean`,
gives the *pointwise* (not merely a.e.) bound

`trZero hR v ^ 2 + trEnd hR v ^ 2 ≤ traceConstBso R * (NB v + Weak.dirichlet v)`,

with `traceConstBso R = max (4 / (2R)) (4 * (2R))`; the two identifications
`NB v = Sobolev.mass (2R) (rep hR v)` (`NB_eq_mass_rep`) and
`Weak.dirichlet v = Sobolev.dirichlet (2R) (rep hR v)` (`dirichletBilin_eq_rep`) are already
available.  Specialised to `v = slice u x` the right-hand side is integrable on `(a,b)` by
`integrableOn_NB_slice` and `integrableOn_dirichlet_slice`.

*Measurability* is the real work.  `rep` is defined by `Classical.choose`, so
`x ↦ trZero hR (slice u x)` carries no measurability whatsoever on its face.  Following the
worked example `RobinCaps/Cap/SliceAC.lean` (`entranceVal`, `slicePrim`), the trace is
re-expressed through *globally strongly measurable* representatives

* `repFBso u = u.memL2.aestronglyMeasurable.mk u.toFun`,
* `repGBso u = (memLp_two_compP u.gz_memL2 0).aestronglyMeasurable.mk (fun p => u.gz p 0)`,

by averaging the fundamental theorem of calculus of `Sobolev.H1` over the slice:

`trZero hR (slice u x) = (2R)⁻¹ ∫₀^{2R} ( u(x, eptSh R t) − ∫₀^t ∂_z u(x, eptSh R s) ds ) dt`,
`trEnd  hR (slice u x) = trZero hR (slice u x) + ∫₀^{2R} ∂_z u(x, eptSh R s) ds`.

The right-hand sides are `trZeroSl` and `trEndSl` below; they are *honestly* strongly
measurable in `x`, by the indicator/`StronglyMeasurable.integral_prod_left'` technique of
`SliceAC.lean` applied twice (once for the inner primitive `slicePrimBso`, once for the outer
average `tr0RawBso`).  The identity holds for every `x` in the a.e. set `IsTraceGoodBso`
(`ae_isTraceGoodBso`), which combines `ae_isGoodSlice` with the two Fubini statements saying
that the chosen representatives agree with `u.toFun` and `(u.gz)₀` on a.e. transverse slice.

Note that the second formula for `trEnd` is just `Sobolev.H1.ftc` at the right endpoint, so no
second averaging argument is needed.

## Main results

* `ae_isTraceGoodBso`, `trZero_slice_eq_bso` — the slice-average formulae;
* `measurable_trZero_slice`, `measurable_trEnd_slice` — a.e. strong measurability (deliverable 1);
* `sq_trZero_add_sq_trEnd_le_bso`, `sq_trZero_slice_le`, `sq_trEnd_slice_le` — the trace bound
  (deliverable 2);
* `integrableOn_traceMajorant_bso` — integrability of the majorant (deliverable 3);
* `bdSliceable_bdTr` — `BdSliceable a b (bdTr R)` (deliverable 4).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.ThinDomain

open MeasureTheory Set Metric RobinCaps.Sobolev RobinCaps.Transverse

open scoped ENNReal

section Bso

variable {a b R : ℝ}

/-! ## 1. Transport of a.e. statements from the transverse ball to `(0, 2R)` -/

/-- Transport of an a.e. statement on the transverse ball `B_1(R)` to the interval `(0, 2R)`
through the affine identification `eptSh R`.  (This is the analogue, for `transverseBall`, of
`RobinCaps.ThinDomain.ae_comp_eptSh` of `TraceOne.lean`, which cannot be imported here.) -/
theorem ae_comp_eptSh_bso {P : EuclideanSpace ℝ (Fin 1) → Prop}
    (h : ∀ᵐ z ∂(volume.restrict (transverseBall 1 R)), P z) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (2 * R))), P (eptSh R t) := by
  have hmp : MeasurePreserving (eptSh R) (volume.restrict (Ioo (0 : ℝ) (2 * R)))
      (volume.restrict (transverseBall 1 R)) := by
    have h0 := (measurePreserving_eptSh R).restrict_preimage
      (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin 1))) (ε := R))
    rwa [eptSh_preimage_ball R] at h0
  exact hmp.quasiMeasurePreserving.ae h

/-! ## 2. Globally strongly measurable representatives -/

/-- A globally strongly measurable representative of `u.toFun`. -/
def repFBso (u : H1P (bulkCyl a b 1 R)) : CapSpace 1 → ℝ :=
  u.memL2.aestronglyMeasurable.mk u.toFun

/-- A globally strongly measurable representative of the single coordinate `(∇_z u)₀` of the
transverse gradient. -/
def repGBso (u : H1P (bulkCyl a b 1 R)) : CapSpace 1 → ℝ :=
  (memLp_two_compP u.gz_memL2 0).aestronglyMeasurable.mk (fun p => u.gz p 0)

theorem stronglyMeasurable_repFBso (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (repFBso u) := u.memL2.aestronglyMeasurable.stronglyMeasurable_mk

theorem stronglyMeasurable_repGBso (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (repGBso u) :=
  (memLp_two_compP u.gz_memL2 0).aestronglyMeasurable.stronglyMeasurable_mk

/-! ## 3. The slice primitive of `(∇_z u)₀`, in a manifestly measurable form -/

/-- The region `{(s, (t, x)) | 0 < s < t}` used to define the transverse primitive. -/
theorem measurableSet_primRegion_bso :
    MeasurableSet {r : ℝ × ℝ × ℝ | r.1 ∈ Ioo (0 : ℝ) r.2.1} := by
  have h1 : IsOpen {r : ℝ × ℝ × ℝ | (0 : ℝ) < r.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {r : ℝ × ℝ × ℝ | r.1 < r.2.1} :=
    isOpen_lt continuous_fst (continuous_fst.comp continuous_snd)
  exact (h1.inter h2).measurableSet

/-- The integration kernel of the transverse primitive of `(∇_z u)₀` from the left endpoint. -/
def primKernelBso (u : H1P (bulkCyl a b 1 R)) : ℝ × ℝ × ℝ → ℝ :=
  {r : ℝ × ℝ × ℝ | r.1 ∈ Ioo (0 : ℝ) r.2.1}.indicator
    fun r => repGBso u (r.2.2, eptSh R r.1)

/-- **The transverse primitive** `(t, x) ↦ ∫₀^t (∇_z u)₀(x, eptSh R s) ds`, written so as to be
manifestly jointly measurable. -/
def slicePrimBso (u : H1P (bulkCyl a b 1 R)) (q : ℝ × ℝ) : ℝ := ∫ s, primKernelBso u (s, q)

theorem stronglyMeasurable_primKernelBso (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (primKernelBso u) := by
  refine StronglyMeasurable.indicator ?_ measurableSet_primRegion_bso
  refine (stronglyMeasurable_repGBso u).comp_measurable ?_
  exact (measurable_snd.comp measurable_snd).prodMk
    ((continuous_eptSh R).measurable.comp measurable_fst)

theorem stronglyMeasurable_slicePrimBso (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (slicePrimBso u) :=
  (stronglyMeasurable_primKernelBso u).integral_prod_left'

theorem slicePrimBso_eq (u : H1P (bulkCyl a b 1 R)) (t x : ℝ) :
    slicePrimBso u (t, x) = ∫ s in Ioo (0 : ℝ) t, repGBso u (x, eptSh R s) := by
  rw [slicePrimBso, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [primKernelBso, Set.indicator_apply, Set.mem_setOf_eq]

/-! ## 4. The measurable slice traces -/

/-- The integrand whose slice average is the left endpoint trace. -/
def trKernelBso (u : H1P (bulkCyl a b 1 R)) : ℝ × ℝ → ℝ :=
  {q : ℝ × ℝ | q.1 ∈ Ioo (0 : ℝ) (2 * R)}.indicator
    fun q => repFBso u (q.2, eptSh R q.1) - slicePrimBso u q

theorem measurableSet_trRegion_bso :
    MeasurableSet {q : ℝ × ℝ | q.1 ∈ Ioo (0 : ℝ) (2 * R)} :=
  measurable_fst measurableSet_Ioo

theorem stronglyMeasurable_trKernelBso (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (trKernelBso u) := by
  refine StronglyMeasurable.indicator ?_ measurableSet_trRegion_bso
  refine StronglyMeasurable.sub ?_ (stronglyMeasurable_slicePrimBso u)
  refine (stronglyMeasurable_repFBso u).comp_measurable ?_
  exact measurable_snd.prodMk ((continuous_eptSh R).measurable.comp measurable_fst)

/-- The unnormalised slice average `∫₀^{2R} ( u(x, eptSh R t) − ∫₀^t ∂_z u ) dt`. -/
def tr0RawBso (u : H1P (bulkCyl a b 1 R)) (x : ℝ) : ℝ := ∫ t, trKernelBso u (t, x)

theorem stronglyMeasurable_tr0RawBso (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (tr0RawBso u) :=
  (stronglyMeasurable_trKernelBso u).integral_prod_left'

theorem tr0RawBso_eq (u : H1P (bulkCyl a b 1 R)) (x : ℝ) :
    tr0RawBso u x
      = ∫ t in Ioo (0 : ℝ) (2 * R), (repFBso u (x, eptSh R t) - slicePrimBso u (t, x)) := by
  rw [tr0RawBso, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [trKernelBso, Set.indicator_apply, Set.mem_setOf_eq]

/-- **The measurable model of the left endpoint trace** of the transverse slice at `x`. -/
def trZeroSl (u : H1P (bulkCyl a b 1 R)) (x : ℝ) : ℝ := tr0RawBso u x / (2 * R)

/-- **The measurable model of the right endpoint trace** of the transverse slice at `x`. -/
def trEndSl (u : H1P (bulkCyl a b 1 R)) (x : ℝ) : ℝ :=
  trZeroSl u x + slicePrimBso u (2 * R, x)

theorem stronglyMeasurable_trZeroSl (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (trZeroSl u) := by
  have h : trZeroSl u = fun x => (2 * R)⁻¹ * tr0RawBso u x := by
    funext x; rw [trZeroSl]; ring
  rw [h]
  exact (stronglyMeasurable_tr0RawBso u).const_mul _

theorem stronglyMeasurable_trEndSl (u : H1P (bulkCyl a b 1 R)) :
    StronglyMeasurable (trEndSl u) := by
  refine (stronglyMeasurable_trZeroSl u).add ?_
  exact (stronglyMeasurable_slicePrimBso u).comp_measurable
    (measurable_const.prodMk measurable_id)

/-! ## 5. The good set for the slice-average formulae -/

/-- The axial coordinates at which the slice-average formulae for the two endpoint traces
hold: the slice is a genuine `H¹(B_1(R))` element, and the two globally measurable
representatives agree with `u` on that slice. -/
def IsTraceGoodBso (u : H1P (bulkCyl a b 1 R)) (x : ℝ) : Prop :=
  IsGoodSlice u x ∧
    (∀ᵐ z ∂(volume.restrict (transverseBall 1 R)), repFBso u (x, z) = u.toFun (x, z)) ∧
      ∀ᵐ z ∂(volume.restrict (transverseBall 1 R)), repGBso u (x, z) = u.gz (x, z) 0

/-- **Almost every axial coordinate is trace-good.** -/
theorem ae_isTraceGoodBso (u : H1P (bulkCyl a b 1 R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), IsTraceGoodBso u x := by
  have hF : ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      ∀ᵐ z ∂(volume.restrict (transverseBall 1 R)), repFBso u (x, z) = u.toFun (x, z) := by
    have h : u.toFun =ᵐ[volume.restrict (bulkCyl a b 1 R)] repFBso u :=
      u.memL2.aestronglyMeasurable.ae_eq_mk
    rw [volume_restrict_bulkCyl] at h
    filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
    filter_upwards [hx] with z hz using hz.symm
  have hG : ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      ∀ᵐ z ∂(volume.restrict (transverseBall 1 R)), repGBso u (x, z) = u.gz (x, z) 0 := by
    have h : (fun p => u.gz p 0) =ᵐ[volume.restrict (bulkCyl a b 1 R)] repGBso u :=
      (memLp_two_compP u.gz_memL2 0).aestronglyMeasurable.ae_eq_mk
    rw [volume_restrict_bulkCyl] at h
    filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
    filter_upwards [hx] with z hz using hz.symm
  filter_upwards [ae_isGoodSlice u, hF, hG] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-! ## 6. The slice-average formulae -/

/-- **The endpoint traces of the transverse slice are given by the measurable formulae.**

For a trace-good `x`, `trZero hR (slice u x)` is the slice average of
`t ↦ u(x, eptSh R t) − ∫₀^t ∂_z u(x, eptSh R s) ds`, and `trEnd hR (slice u x)` is
`trZero hR (slice u x) + ∫₀^{2R} ∂_z u(x, eptSh R s) ds`. -/
theorem trZero_slice_eq_bso (hR : 0 < R) {u : H1P (bulkCyl a b 1 R)} {x : ℝ}
    (hx : IsTraceGoodBso u x) :
    trZero hR (slice u x) = trZeroSl u x ∧ trEnd hR (slice u x) = trEndSl u x := by
  obtain ⟨hg, hFa, hGa⟩ := hx
  have h2R : (0 : ℝ) < 2 * R := by linarith
  -- the representative of the slice, read through `repFBso`
  have hrepF : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (2 * R))),
      (rep hR (slice u x)).toFun t = repFBso u (x, eptSh R t) := by
    filter_upwards [rep_ae hR (slice u x), ae_comp_eptSh_bso hFa] with t ht ht2
    simp only [slice_toFun hg] at ht
    rw [ht, ht2]
  -- and its derivative, read through `repGBso`
  have hrepG : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (2 * R))),
      deriv (rep hR (slice u x)).toFun t = repGBso u (x, eptSh R t) := by
    filter_upwards [rep_deriv_ae hR (slice u x), ae_comp_eptSh_bso hGa] with t ht ht2
    simp only [slice_grad hg] at ht
    rw [ht, ht2]
  -- the primitive of the measurable representative is the primitive of the derivative
  have hprim : ∀ t ∈ Icc (0 : ℝ) (2 * R),
      slicePrimBso u (t, x) = ∫ s in (0 : ℝ)..t, deriv (rep hR (slice u x)).toFun s := by
    intro t ht
    rw [slicePrimBso_eq, Sobolev.intervalIntegral_eq_setIntegral_Ioo ht.1]
    refine (integral_congr_ae ?_).symm
    exact hrepG.filter_mono
      (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2) le_rfl))
  -- the fundamental theorem of calculus at the left endpoint
  have hftc : ∀ t ∈ Icc (0 : ℝ) (2 * R),
      trZero hR (slice u x)
        = (rep hR (slice u x)).toFun t - slicePrimBso u (t, x) := by
    intro t ht
    rw [hprim t ht, trZero]
    exact Sobolev.H1.sub_integral _ ht
  -- hence the integrand of the slice average is a.e. constant
  have hconst : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (2 * R))),
      repFBso u (x, eptSh R t) - slicePrimBso u (t, x) = trZero hR (slice u x) := by
    filter_upwards [hrepF, ae_restrict_mem measurableSet_Ioo] with t ht htm
    rw [← ht, ← hftc t (Ioo_subset_Icc_self htm)]
  -- compute the slice average
  have hraw : tr0RawBso u x = (2 * R) * trZero hR (slice u x) := by
    rw [tr0RawBso_eq,
      setIntegral_congr_ae measurableSet_Ioo ((ae_restrict_iff' measurableSet_Ioo).1 hconst),
      setIntegral_const, Real.volume_real_Ioo_of_le h2R.le, smul_eq_mul]
    ring
  have hzero : trZero hR (slice u x) = trZeroSl u x := by
    rw [trZeroSl, hraw]
    field_simp
  refine ⟨hzero, ?_⟩
  -- the right endpoint, by the fundamental theorem of calculus at `2R`
  have hend : trEnd hR (slice u x)
      = trZero hR (slice u x) + slicePrimBso u (2 * R, x) := by
    rw [hprim (2 * R) (end_mem_Icc hR), trEnd, trZero]
    exact (rep hR (slice u x)).ftc (2 * R) (end_mem_Icc hR)
  rw [hend, trEndSl, hzero]

/-! ## 7. Deliverable 1: a.e. measurability of the slice traces -/

/-- **The left endpoint trace of the transverse slice is a.e. strongly measurable.** -/
theorem measurable_trZero_slice (hR : 0 < R) (u : H1P (bulkCyl a b 1 R)) :
    AEStronglyMeasurable (fun x => trZero hR (slice u x)) (volume.restrict (Ioo a b)) := by
  refine AEStronglyMeasurable.congr (stronglyMeasurable_trZeroSl u).aestronglyMeasurable ?_
  filter_upwards [ae_isTraceGoodBso u] with x hx
  exact ((trZero_slice_eq_bso hR hx).1).symm

/-- **The right endpoint trace of the transverse slice is a.e. strongly measurable.** -/
theorem measurable_trEnd_slice (hR : 0 < R) (u : H1P (bulkCyl a b 1 R)) :
    AEStronglyMeasurable (fun x => trEnd hR (slice u x)) (volume.restrict (Ioo a b)) := by
  refine AEStronglyMeasurable.congr (stronglyMeasurable_trEndSl u).aestronglyMeasurable ?_
  filter_upwards [ae_isTraceGoodBso u] with x hx
  exact ((trZero_slice_eq_bso hR hx).2).symm

/-! ## 8. Deliverable 2: the trace bound -/

/-- The constant of the one-dimensional trace inequality on `[0, 2R]`, from
`RobinCaps.Sobolev.trace_ineq`. -/
def traceConstBso (R : ℝ) : ℝ := max (4 / (2 * R)) (4 * (2 * R))

theorem traceConstBso_nonneg (hR : 0 < R) : 0 ≤ traceConstBso R :=
  le_trans (by positivity) (le_max_left _ _)

/-- The transverse Dirichlet energy is the one-dimensional Dirichlet energy of the
representative. -/
theorem dirichlet_rep_eq_bso (hR : 0 < R) (v : TransH1 1 R) :
    Sobolev.dirichlet (2 * R) (rep hR v) = Weak.dirichlet v := by
  have h := dirichletBilin_eq_rep hR v v
  rw [dirichletBilin_self] at h
  rw [Sobolev.dirichlet]
  simp only [pow_two]
  exact h.symm

/-- **The trace bound on a transverse slice**, valid for *every* `v : TransH1 1 R` (no a.e.
qualifier): the sum of the squared endpoint traces is controlled by the transverse `H¹` energy,
with the explicit constant `traceConstBso R = max (4 / (2R)) (4 * (2R))`. -/
theorem sq_trZero_add_sq_trEnd_le_bso (hR : 0 < R) (v : TransH1 1 R) :
    trZero hR v ^ 2 + trEnd hR v ^ 2
      ≤ traceConstBso R * (NB v + Weak.dirichlet v) := by
  have h := Sobolev.trace_ineq (rep hR v) (by linarith : (0 : ℝ) < 2 * R)
  rw [traceConstBso, trZero, trEnd, NB_eq_mass_rep hR v, ← dirichlet_rep_eq_bso hR v]
  exact h

/-- **Deliverable 2 (left endpoint).**  The squared left endpoint trace of the slice of `u` at
`x` is a.e. bounded by `traceConstBso R` times the transverse `H¹` energy of the slice. -/
theorem sq_trZero_slice_le (hR : 0 < R) (u : H1P (bulkCyl a b 1 R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      trZero hR (slice u x) ^ 2
        ≤ traceConstBso R * ((∫ z in transverseBall 1 R, u.toFun (x, z) ^ 2)
            + ∫ z in transverseBall 1 R, ‖u.gz (x, z)‖ ^ 2) := by
  filter_upwards [ae_NB_slice u, ae_dirichlet_slice u] with x h1 h2
  have h := sq_trZero_add_sq_trEnd_le_bso hR (slice u x)
  rw [h1, h2] at h
  nlinarith [sq_nonneg (trEnd hR (slice u x))]

/-- **Deliverable 2 (right endpoint).** -/
theorem sq_trEnd_slice_le (hR : 0 < R) (u : H1P (bulkCyl a b 1 R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      trEnd hR (slice u x) ^ 2
        ≤ traceConstBso R * ((∫ z in transverseBall 1 R, u.toFun (x, z) ^ 2)
            + ∫ z in transverseBall 1 R, ‖u.gz (x, z)‖ ^ 2) := by
  filter_upwards [ae_NB_slice u, ae_dirichlet_slice u] with x h1 h2
  have h := sq_trZero_add_sq_trEnd_le_bso hR (slice u x)
  rw [h1, h2] at h
  nlinarith [sq_nonneg (trZero hR (slice u x))]

/-! ## 9. Deliverable 3: integrability of the majorant -/

/-- **The majorant is integrable on the axial interval.**  By Fubini
(`integrableOn_NB_slice`, `integrableOn_dirichlet_slice` of `BulkEnergy.lean`) this is the
statement that `x ↦ ∫_B u(x,·)² + ∫_B ‖∇_z u(x,·)‖²` is integrable, its integral being
`massP u` plus the transverse part of `dirichletP u`. -/
theorem integrableOn_traceMajorant_bso (u : H1P (bulkCyl a b 1 R)) :
    IntegrableOn (fun x => NB (slice u x) + Weak.dirichlet (slice u x)) (Ioo a b) :=
  (integrableOn_NB_slice u).add (integrableOn_dirichlet_slice u)

end Bso

/-! ## 10. Deliverable 4: the main theorem -/

/-- **The `m = 1` transverse trace form is slice-integrable on the bulk cylinder.**

This discharges, for the concrete one-dimensional trace form `RobinCaps.Transverse.bdTr R`, the
hypothesis structure `RobinCaps.ThinDomain.BdSliceable` left open in
`RobinCaps/ThinDomain/BulkEnergy.lean`. -/
theorem bdSliceable_bdTr {R : ℝ} (hR : 0 < R) (a b : ℝ) : BdSliceable a b (bdTr R) := by
  refine ⟨fun u v => ?_⟩
  have hC0 : 0 ≤ traceConstBso R := traceConstBso_nonneg hR
  -- the dominating function
  have hgi : IntegrableOn
      (fun x => traceConstBso R / 2 *
        ((NB (slice u x) + Weak.dirichlet (slice u x))
          + (NB (slice v x) + Weak.dirichlet (slice v x)))) (Ioo a b) :=
    ((integrableOn_traceMajorant_bso u).add (integrableOn_traceMajorant_bso v)).const_mul _
  have hform : (fun x => bdTr R (slice u x) (slice v x))
      = fun x => trZero hR (slice u x) * trZero hR (slice v x)
          + trEnd hR (slice u x) * trEnd hR (slice v x) := by
    funext x
    exact bdTr_apply hR _ _
  rw [IntegrableOn, hform]
  refine Integrable.mono' hgi ?_ ?_
  · exact ((measurable_trZero_slice hR u).mul (measurable_trZero_slice hR v)).add
      ((measurable_trEnd_slice hR u).mul (measurable_trEnd_slice hR v))
  · filter_upwards with x
    have h1 := sq_trZero_add_sq_trEnd_le_bso hR (slice u x)
    have h2 := sq_trZero_add_sq_trEnd_le_bso hR (slice v x)
    rw [Real.norm_eq_abs]
    refine le_trans (abs_le.2 ⟨?_, ?_⟩) (le_refl _)
    · nlinarith [sq_nonneg (trZero hR (slice u x) + trZero hR (slice v x)),
        sq_nonneg (trEnd hR (slice u x) + trEnd hR (slice v x))]
    · nlinarith [sq_nonneg (trZero hR (slice u x) - trZero hR (slice v x)),
        sq_nonneg (trEnd hR (slice u x) - trEnd hR (slice v x))]

end RobinCaps.ThinDomain

end
