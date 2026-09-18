import RobinCaps.Compact.BoundaryForm
import RobinCaps.ThinDomain.BulkEnergy

/-!
# `BdSliceable` for the Rellich boundary form `bdR`, in every dimension `m ≥ 1`

`RobinCaps/Compact/BoundaryForm.lean` defines the Rellich boundary form `bdR m R` by an
*interior* integral (the Rellich identity)

`bdR m R u v = R⁻¹ ∫_{B_m(R)} ( m u v + u ⟪z, ∇v⟫ + v ⟪z, ∇u⟫ ) dz`.

Since this is already an interior (bulk) integral, `RobinCaps.ThinDomain.BdSliceable` for `bdR`
is a pure Fubini exercise, with no trace operator involved: for a.e. axial coordinate `x`, the
transverse slices `slice u x` and `slice v x` satisfy `bdR m R (slice u x) (slice v x))` equal
to the *inner* transverse integral of the pointwise Rellich integrand evaluated on the slice of
`u` and `v` at `x`.  Each of the three terms of that integrand is integrable on the whole bulk
cylinder `bulkCyl a b m R` (products/inner-products of `L²` functions, using that the transverse
coordinate is bounded by `R` on `transverseBall m R`), so Fubini
(`RobinCaps.ThinDomain.integrableOn_inner_bulk`) gives integrability of the axial integral, and
an a.e.-equality argument (`RobinCaps.ThinDomain.ae_isGoodSlice`) transports this to
`x ↦ bdR m R (slice u x) (slice v x)`.

Main result: `bdSliceable_bdR_bsg`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.ThinDomain

open MeasureTheory Set Metric RobinCaps.Compact

open scoped ENNReal InnerProductSpace

variable {m : ℕ} {a b R : ℝ}

/-! ## 1. The pointwise Rellich integrand is integrable on the bulk cylinder -/

/-- `p ↦ ⟪p.2, v.gz p⟫` is `L²` on the bulk cylinder: the transverse coordinate `p.2` is bounded
by `R` there, exactly as `abs_inner_le_of_mem_ball` bounds `⟪x, ∇v x⟫` on the ball. -/
theorem memLp_inner_gz_bsg (v : H1P (bulkCyl a b m R)) :
    MemLp (fun p : CapSpace m => ⟪p.2, v.gz p⟫_ℝ) 2 (volume.restrict (bulkCyl a b m R)) := by
  have hmeas : AEStronglyMeasurable (fun p : CapSpace m => ⟪p.2, v.gz p⟫_ℝ)
      (volume.restrict (bulkCyl a b m R)) :=
    (continuous_snd.aestronglyMeasurable).inner v.gz_memL2.aestronglyMeasurable
  refine MemLp.of_le (v.gz_memL2.norm.const_mul R) hmeas ?_
  filter_upwards [ae_restrict_mem isOpen_bulkCyl.measurableSet] with p hp
  obtain ⟨-, hp2⟩ := mem_bulkCyl_iff.1 hp
  have hxR : ‖p.2‖ < R := mem_ball_zero_iff.1 hp2
  have hR : (0 : ℝ) < R := lt_of_le_of_lt (norm_nonneg p.2) hxR
  have h1 : |⟪p.2, v.gz p⟫_ℝ| ≤ R * ‖v.gz p‖ :=
    (abs_real_inner_le_norm p.2 (v.gz p)).trans
      (mul_le_mul_of_nonneg_right hxR.le (norm_nonneg _))
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos hR,
    abs_of_nonneg (norm_nonneg (v.gz p))] using h1

/-- **The Rellich integrand is integrable on the whole bulk cylinder.** -/
theorem integrable_bdIntegrandP_bsg (u v : H1P (bulkCyl a b m R)) :
    Integrable (fun p : CapSpace m => (m : ℝ) * (u.toFun p * v.toFun p)
      + u.toFun p * ⟪p.2, v.gz p⟫_ℝ + v.toFun p * ⟪p.2, u.gz p⟫_ℝ)
      (volume.restrict (bulkCyl a b m R)) :=
  (((u.memL2.integrable_mul v.memL2).const_mul (m : ℝ)).add
    (u.memL2.integrable_mul (memLp_inner_gz_bsg v))).add
    (v.memL2.integrable_mul (memLp_inner_gz_bsg u))

/-! ## 2. `bdR` on good slices is the inner transverse integral -/

/-- **On a jointly good axial coordinate, `bdR` of the two slices is the inner transverse
integral of the Rellich integrand.**  Immediate from `bdR_apply`, `slice_toFun` and
`slice_grad`: `transverseBall m R` and `ball (0 : EuclideanSpace ℝ (Fin m)) R` are definitionally
equal, so no cast is needed. -/
theorem bdR_slice_eq_bsg {u v : H1P (bulkCyl a b m R)} {x : ℝ}
    (hu : IsGoodSlice u x) (hv : IsGoodSlice v x) :
    bdR m R (slice u x) (slice v x)
      = R⁻¹ * ∫ z in transverseBall m R,
          ((m : ℝ) * (u.toFun (x, z) * v.toFun (x, z))
            + u.toFun (x, z) * ⟪z, v.gz (x, z)⟫_ℝ
            + v.toFun (x, z) * ⟪z, u.gz (x, z)⟫_ℝ) := by
  rw [bdR_apply, slice_toFun hu, slice_toFun hv, slice_grad hu, slice_grad hv]
  rfl

/-- The a.e. version of `bdR_slice_eq_bsg`, over the good set of both `u` and `v`
(`ae_isGoodSlice`). -/
theorem ae_bdR_slice_eq_bsg (u v : H1P (bulkCyl a b m R)) :
    (fun x => bdR m R (slice u x) (slice v x)) =ᵐ[volume.restrict (Ioo a b)]
      fun x => R⁻¹ * ∫ z in transverseBall m R,
        ((m : ℝ) * (u.toFun (x, z) * v.toFun (x, z))
          + u.toFun (x, z) * ⟪z, v.gz (x, z)⟫_ℝ
          + v.toFun (x, z) * ⟪z, u.gz (x, z)⟫_ℝ) := by
  filter_upwards [ae_isGoodSlice u, ae_isGoodSlice v] with x hu hv
  exact bdR_slice_eq_bsg hu hv

/-! ## 3. Main theorem -/

/-- **The Rellich boundary form `bdR m R` is slice-integrable on every bulk cylinder.**

`bdR` is defined by an interior integral over the transverse ball, so this is a pure Fubini
statement: no trace operator is needed, unlike the concrete lateral trace form
`RobinCaps.Transverse.bdTr R` of `BdSliceableOne.lean` (which needs the extra measurability
work of that file because the endpoint traces are defined through `Classical.choose`). -/
theorem bdSliceable_bdR_bsg (hR : 0 < R) (a b : ℝ) : BdSliceable a b (bdR m R) := by
  refine ⟨fun u v => ?_⟩
  have hint : IntegrableOn (fun x => ∫ z in transverseBall m R,
      ((m : ℝ) * (u.toFun (x, z) * v.toFun (x, z))
        + u.toFun (x, z) * ⟪z, v.gz (x, z)⟫_ℝ
        + v.toFun (x, z) * ⟪z, u.gz (x, z)⟫_ℝ)) (Ioo a b) :=
    integrableOn_inner_bulk (integrable_bdIntegrandP_bsg u v)
  have hint2 : IntegrableOn (fun x => R⁻¹ * ∫ z in transverseBall m R,
      ((m : ℝ) * (u.toFun (x, z) * v.toFun (x, z))
        + u.toFun (x, z) * ⟪z, v.gz (x, z)⟫_ℝ
        + v.toFun (x, z) * ⟪z, u.gz (x, z)⟫_ℝ)) (Ioo a b) := hint.const_mul R⁻¹
  exact hint2.congr_fun_ae (ae_bdR_slice_eq_bsg u v).symm

end RobinCaps.ThinDomain
