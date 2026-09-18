import RobinCaps.ThinDomain.TraceOne
import RobinCaps.ThinDomain.BdSliceableOne
import RobinCaps.ThinDomain.Restrict

/-!
# The trace inequality on the planar stadium (two hemispherical caps, `m = 1`)

This file proves the hypothesis `RobinCaps.ThinDomain.TraceIneqOne (Cap.hemisphere 1)
(Cap.hemisphere 1) L R` of `RobinCaps/ThinDomain/TraceOne.lean` for the **stadium**: the planar
thin domain `Ω_R` with two hemispherical end caps, i.e. the `R`-neighbourhood of the axial
segment `[x₋, x₊] × {0}`, `x∓ = ∓(L/2 − R)`.

Everything is proved **except one interface**, the radial absolute continuity on the caps
(`ArcTraceSt` / `RadialACL`, section 4), which is the analytic brick that
`RobinCaps/Sobolev/RadialSlice.lean` is to supply; that file is *not* imported here.

## The strategy

The axial interval `(−L/2, L/2)` is split into three pieces,

* the **bulk** `(x₋, x₊)`, where the profile is the constant `R` and the area element is `1`.
  There the vertical slice `{x} × (−R, R)` has uniform length `2R` and the one-dimensional
  trace inequality of `RobinCaps/Sobolev/Interval.lean` costs only `max(2/R, 8R)`.  All the
  work is already done in `RobinCaps/ThinDomain/BdSliceableOne.lean` for the bulk cylinder;
  the only new ingredient is the identification `trPlus u = trEnd (slice (restrictBulk u))`
  a.e. on the bulk (`ae_trPlus_eq_trEnd_bulk_st`, via `TraceOne.trPlus_eq_trEnd`).  This part
  uses **no** interface (`bulk_trace_bound_st`).

* the two **arcs** `(−L/2, x₋)` and `(x₊, L/2)`.  Vertical slices are useless there: their
  length `2 r(x)` tends to `0` at the tips, and the trace cost `r(x)⁻¹` is not integrable
  against the area element.  Instead the boundary is parametrised by the polar angle `φ` from
  the centre `(c, 0)` of the cap (`c = x∓`, axial sign `e = ∓1`),

  `x = capXSt c e R φ = c + e R cos φ`,  `r(x) = R sin φ`,  `φ ∈ (0, π/2)`,

  and the area element becomes `A(x) = √(1 + r'(x)²) = R / r(x) = 1 / sin φ`
  (`CapGeomSt.areaElement_capXSt`), so that `A(x) dx = R dφ` — the arc-length element.  The
  radial ray of angle `φ` hits the arc orthogonally; the one-dimensional trace inequality on
  its outer half `ρ ∈ [R/2, R]` costs `4/R` on the mass and `R` on the Dirichlet energy, and
  the polar weight `ρ ≥ R/2` converts these into `8/R²` and `2` against the polar measure
  `ρ dρ dφ` (`arc_sq_ae_le_st`).  Integrating in `φ` gives `arc_trace_bound_st`.

## What is assumed: `ArcTraceSt L R u c e s T`

For each of the four quarter-disks (two caps `e = ∓1`, two transverse signs `s = ±1`) the
interface provides a **radial trace** `T : ℝ → ℝ` — `T φ` is the boundary value of `u` at the
arc point `capPtSt c e s φ R` — with six fields:

* `aesm` — `T` is a.e. strongly measurable on `(0, π/2)`;
* `radAC` — for a.e. `φ` the radial slice `t ↦ u(capSliceSt c e s R φ t)`, `ρ = t + R/2`, has an
  absolutely continuous representative `W : Sobolev.H1 (R/2)` whose derivative is the radial
  component `⟪∇u, (e cos φ, s sin φ)⟫` of the weak gradient and with `W(R/2) = T φ`;
* `radIntegrable` — Fubini along the rays: the `H¹` density is integrable on each ray, with
  and without the polar weight;
* `energy_integrable` — Fubini in the angle;
* `energy_le` — the polar change of variables on the quarter-annulus, together with its
  inclusion in `Ω_R`: `∫_0^{π/2} ∫_{R/2}^R (u² + |∇u|²) ρ dρ dφ ≤ N[u] + D[u]`;
* `vert_eq` — the **identification** of the vertical-slice endpoint trace `trPlus`/`trMinus` of
  `TraceOne.lean` with the radial trace `T` at the same boundary point.  This is a genuinely
  two-dimensional statement (two absolutely continuous representatives along two different
  directions agreeing at the boundary point) and is left to the interface.

`RadialACL L R u` bundles the four instances.  `capPtSt_mem_thinDomain_st` records that the
points the interface speaks about really lie in `Ω_R`.

## Main results

* `bulk_trace_bound_st` — the bulk bound, with **no** interface;
* `arc_trace_bound_st` — the arc bound, given `ArcTraceSt`;
* `aesm_trPlus_bulk_st`, `aesm_trSide_cap_st` — measurability of the endpoint traces on the
  three pieces (on the caps it is transported along the arc parametrisation, which maps null
  sets to null sets by `null_image_capXSt`);
* `traceIneqOne_hemisphere` — `TraceIneqOne (Cap.hemisphere 1) (Cap.hemisphere 1) L R`;
* `traceConstSt R = max (2/R) (8R) + 4 R (8/R² + 2)` and
  `traceIneqOne_hemisphere_const` — the explicit constant, with `traceConstSt R ≤ 34/R + 16 R`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse

section Stadium

variable {L R : ℝ}

/-- The hemispherical caps have `K = 1`. -/
theorem hemisphere_K_st : ((Cap.hemisphere 1).K : ℝ) = 1 := rfl

/-- The admissibility hypothesis `2R < L` in the form required by the general lemmas. -/
theorem hLK_st (hL : 2 * R < L) :
    ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L := by
  rw [hemisphere_K_st]; linarith

theorem interfaceL_st : interfaceL (Cap.hemisphere 1) L R = -L / 2 + R := by
  rw [interfaceL, hemisphere_K_st, one_mul]

theorem interfaceR_st : interfaceR (Cap.hemisphere 1) L R = L / 2 - R := by
  rw [interfaceR, hemisphere_K_st, one_mul]

/-- The open bulk axial interval `(x₋, x₊)` is contained in the full axial interval. -/
theorem bulkIoo_subset_st (hR : 0 < R) :
    Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R)
      ⊆ Ioo (-L / 2) (L / 2) := by
  rw [interfaceL_st, interfaceR_st]
  exact Ioo_subset_Ioo (by linarith) (by linarith)

/-- The restriction of `u` to the open bulk cylinder. -/
def bulkOf (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    H1P (bulkOpen (Cap.hemisphere 1) (Cap.hemisphere 1) L R) :=
  restrictBulk hR (hLK_st hL) u

/-! ## 1. The bulk part of the lateral boundary -/

/-- On the bulk the two endpoint traces of `TraceOne.lean` are the transverse endpoint
traces `trEnd`, `trZero` of the slice, for almost every axial coordinate. -/
theorem ae_trPlus_eq_trEnd_bulk_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL (Cap.hemisphere 1) L R)
        (interfaceR (Cap.hemisphere 1) L R))),
      trPlus u x = trEnd hR (slice (bulkOf hR hL u) x) ∧
        trMinus u x = trZero hR (slice (bulkOf hR hL u) x) := by
  have hgood : ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL (Cap.hemisphere 1) L R)
      (interfaceR (Cap.hemisphere 1) L R))), SliceGood u x :=
    ae_mono (Measure.restrict_mono (bulkIoo_subset_st hR) le_rfl)
      (ae_sliceGood hR (hLK_st hL) u)
  filter_upwards [hgood, ae_isGoodSlice (bulkOf hR hL u), ae_restrict_mem measurableSet_Ioo]
    with x hg hgs hxI
  have hprof : profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R x = R :=
    profile_bulk hxI.1.le hxI.2.le
  refine trPlus_eq_trEnd hR (hLK_st hL) hg hprof (slice (bulkOf hR hL u) x) ?_
  rw [slice_toFun hgs]
  exact Filter.EventuallyEq.rfl

theorem aesm_trPlus_bulk_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    AEStronglyMeasurable (trPlus u) (volume.restrict
      (Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R))) := by
  refine AEStronglyMeasurable.congr (measurable_trEnd_slice hR (bulkOf hR hL u)) ?_
  filter_upwards [ae_trPlus_eq_trEnd_bulk_st hR hL u] with x hx
  exact (hx.1).symm

theorem aesm_trMinus_bulk_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    AEStronglyMeasurable (trMinus u) (volume.restrict
      (Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R))) := by
  refine AEStronglyMeasurable.congr (measurable_trZero_slice hR (bulkOf hR hL u)) ?_
  filter_upwards [ae_trPlus_eq_trEnd_bulk_st hR hL u] with x hx
  exact (hx.2).symm

/-- **The pointwise bulk trace bound.**  On the bulk the area element is `1` and the vertical
slice has uniform length `2R`, so the one-dimensional trace inequality applies directly. -/
theorem bulk_trace_ae_le_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL (Cap.hemisphere 1) L R)
        (interfaceR (Cap.hemisphere 1) L R))),
      areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
          * (trPlus u x ^ 2 + trMinus u x ^ 2)
        ≤ traceConstBso R * (NB (slice (bulkOf hR hL u) x)
            + Weak.dirichlet (slice (bulkOf hR hL u) x)) := by
  filter_upwards [ae_trPlus_eq_trEnd_bulk_st hR hL u, ae_restrict_mem measurableSet_Ioo]
    with x hx hxI
  have harea : areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x = 1 := by
    rw [areaElement_bulk hxI.1 hxI.2]
    norm_num
  rw [harea, one_mul, hx.1, hx.2]
  have h := sq_trZero_add_sq_trEnd_le_bso hR (slice (bulkOf hR hL u) x)
  linarith


/-- Integrability of the trace density on the bulk interval. -/
theorem integrableOn_bulk_density_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    IntegrableOn (fun x => areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
        * (trPlus u x ^ 2 + trMinus u x ^ 2))
      (Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R)) volume := by
  refine Integrable.mono'
    ((integrableOn_traceMajorant_bso (bulkOf hR hL u)).const_mul (traceConstBso R)) ?_ ?_
  · exact (measurable_areaElement.aestronglyMeasurable).mul
      (((aesm_trPlus_bulk_st hR hL u).pow 2).add ((aesm_trMinus_bulk_st hR hL u).pow 2))
  · filter_upwards [bulk_trace_ae_le_st hR hL u] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (areaElement_nonneg x) (by positivity))]
    exact hx

/-- The transverse part of the bulk Dirichlet energy is at most the full one. -/
theorem integral_dirichlet_slice_le_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    (∫ x in Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R),
        Weak.dirichlet (slice (bulkOf hR hL u) x)) ≤ dirichletP (bulkOf hR hL u) := by
  have h := dirichletP_eq_axial_add_slice (bulkOf hR hL u)
  have h0 := axialDirichletP_nonneg (bulkOf hR hL u)
  linarith

theorem massP_bulk_le_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    massP (bulkOf hR hL u) ≤ massP u := by
  have h := massP_eq_sum hR (hLK_st hL) u
  have h1 := massP_nonneg (restrictLeft hR (hLK_st hL) u)
  have h2 := massP_nonneg (restrictRight hR (hLK_st hL) u)
  simp only [bulkOf]
  linarith

theorem dirichletP_bulk_le_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    dirichletP (bulkOf hR hL u) ≤ dirichletP u := by
  have h := dirichletP_eq_sum hR (hLK_st hL) u
  have h1 := dirichletP_nonneg (restrictLeft hR (hLK_st hL) u)
  have h2 := dirichletP_nonneg (restrictRight hR (hLK_st hL) u)
  simp only [bulkOf]
  linarith

/-- **Deliverable 2: the bulk trace bound.**  The trace density is integrable on the bulk
interval `(x₋, x₊)` and its integral is at most `max (2/R) (8R)` times the full energy. -/
theorem bulk_trace_bound_st (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    (∫ x in Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R),
        areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
          * (trPlus u x ^ 2 + trMinus u x ^ 2))
      ≤ traceConstBso R * (massP u + dirichletP u) := by
  have hmaj : IntegrableOn (fun x => traceConstBso R * (NB (slice (bulkOf hR hL u) x)
      + Weak.dirichlet (slice (bulkOf hR hL u) x)))
      (Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R)) volume :=
    (integrableOn_traceMajorant_bso (bulkOf hR hL u)).const_mul (traceConstBso R)
  refine le_trans (integral_mono_ae (integrableOn_bulk_density_st hR hL u) hmaj
    (bulk_trace_ae_le_st hR hL u)) ?_
  rw [integral_const_mul, integral_add (integrableOn_NB_slice (bulkOf hR hL u))
    (integrableOn_dirichlet_slice (bulkOf hR hL u)),
    ← massP_eq_integral_NB_slice (bulkOf hR hL u)]
  have hc := traceConstBso_nonneg hR
  have h1 := massP_bulk_le_st hR hL u
  have h2 := le_trans (integral_dirichlet_slice_le_st hR hL u) (dirichletP_bulk_le_st hR hL u)
  nlinarith


/-! ## 2. Geometry of the hemispherical caps -/

/-- **The area element on a hemispherical cap is `R / r(x)`.**  If the profile coincides, near
`x`, with the circular arc of radius `R` centred at `(c, 0)`, then
`√(1 + r'(x)²) = R / r(x)`; this is the statement that the arc meets the radial ray from the
centre orthogonally. -/
theorem areaElement_arc_st (hR : 0 < R) (c : ℝ) {x : ℝ}
    (hev : profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R
      =ᶠ[nhds x] fun y => Real.sqrt (R ^ 2 - (y - c) ^ 2))
    (hx : (x - c) ^ 2 < R ^ 2) :
    areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
      = R / profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R x := by
  have hg : (0 : ℝ) < R ^ 2 - (x - c) ^ 2 := by linarith
  have hsq : Real.sqrt (R ^ 2 - (x - c) ^ 2) > 0 := Real.sqrt_pos.2 hg
  have hprof : profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
      = Real.sqrt (R ^ 2 - (x - c) ^ 2) := hev.self_of_nhds
  -- the derivative of the circular arc
  have hbase : HasDerivAt (fun y : ℝ => R ^ 2 - (y - c) ^ 2) (-(2 * (x - c))) x := by
    have h1 : HasDerivAt (fun y : ℝ => (y - c) ^ 2) (2 * (x - c) ^ 1 * 1) x :=
      ((hasDerivAt_id x).sub_const c).pow 2
    simpa using (hasDerivAt_const x (R ^ 2)).sub h1
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (R ^ 2 - (y - c) ^ 2))
      (-(2 * (x - c)) / (2 * Real.sqrt (R ^ 2 - (x - c) ^ 2))) x :=
    hbase.sqrt (ne_of_gt hg)
  have hderiv : deriv (profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R) x
      = -(2 * (x - c)) / (2 * Real.sqrt (R ^ 2 - (x - c) ^ 2)) := by
    rw [hev.deriv_eq]; exact hsqrt.deriv
  rw [areaElement_one_eq, hderiv, hprof]
  have hkey : 1 + (-(2 * (x - c)) / (2 * Real.sqrt (R ^ 2 - (x - c) ^ 2))) ^ 2
      = (R / Real.sqrt (R ^ 2 - (x - c) ^ 2)) ^ 2 := by
    have hs2 : Real.sqrt (R ^ 2 - (x - c) ^ 2) ^ 2 = R ^ 2 - (x - c) ^ 2 :=
      Real.sq_sqrt hg.le
    field_simp
    nlinarith [hs2]
  rw [hkey, Real.sqrt_sq (by positivity)]

/-! ### The left cap -/

theorem profile_eventuallyEq_left_st (hR : 0 < R) (hL : 2 * R < L) {x : ℝ}
    (hx : x ∈ Ioo (-L / 2) (interfaceL (Cap.hemisphere 1) L R)) :
    profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R
      =ᶠ[nhds x] fun y => Real.sqrt (R ^ 2 - (y - interfaceL (Cap.hemisphere 1) L R) ^ 2) := by
  refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => ?_)
  rw [interfaceL_st] at hy ⊢
  have h2 : y < -(L / 2 - R) := by have := hy.2; linarith
  rw [profile_hemisphere_left hR hL hy.1 h2]
  congr 1
  ring

theorem profile_eventuallyEq_right_st (hR : 0 < R) (hL : 2 * R < L) {x : ℝ}
    (hx : x ∈ Ioo (interfaceR (Cap.hemisphere 1) L R) (L / 2)) :
    profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R
      =ᶠ[nhds x] fun y => Real.sqrt (R ^ 2 - (y - interfaceR (Cap.hemisphere 1) L R) ^ 2) := by
  refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => ?_)
  rw [interfaceR_st] at hy ⊢
  have h1 : L / 2 - R < y := hy.1
  rw [profile_hemisphere_right hR hL h1 hy.2]


/-! ## 3. The angular parametrisation of a cap arc -/

/-- The point of the plane at polar radius `ρ` and polar angle `φ` around the cap centre
`(c, 0)`, in the quadrant selected by the axial sign `e` and the transverse sign `s`
(both `±1`).  For `ρ = R` and `φ ∈ (0, π/2)` this is the point of the cap arc at angle `φ`. -/
def capPtSt (c e s φ ρ : ℝ) : CapSpace 1 :=
  (c + e * (ρ * Real.cos φ), ept (s * (ρ * Real.sin φ)))

/-- The abscissa of the arc point of angle `φ`. -/
def capXSt (c e R φ : ℝ) : ℝ := c + e * (R * Real.cos φ)

@[simp] theorem capPtSt_fst_at_R (c e s R φ : ℝ) :
    (capPtSt c e s φ R).1 = capXSt c e R φ := rfl

/-- The open axial interval swept by the cap: `e (x - c) ∈ (0, R)`. -/
def capSetSt (c e R : ℝ) : Set ℝ := {y : ℝ | e * (y - c) ∈ Ioo 0 R}

/-- **The geometric data of one hemispherical cap of the stadium.**  `c` is the abscissa of the
centre of the cap (an interface abscissa `x∓`), and `e = ∓1` is the outward axial direction. -/
structure CapGeomSt (L R c e : ℝ) : Prop where
  /-- `e` is a sign. -/
  sq_one : e ^ 2 = 1
  /-- On the axial interval swept by the cap the profile is the circular arc of radius `R`
  centred at `(c, 0)`. -/
  prof : ∀ y ∈ capSetSt c e R,
    profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R
      =ᶠ[nhds y] fun z => Real.sqrt (R ^ 2 - (z - c) ^ 2)
  /-- The cap interval is part of the axial interval. -/
  sub : capSetSt c e R ⊆ Ioo (-L / 2) (L / 2)

namespace CapGeomSt

variable {c e : ℝ}

theorem abs_eq_one (h : CapGeomSt L R c e) : |e| = 1 := by
  have := h.sq_one
  rcases abs_cases e with ⟨h1, _⟩ | ⟨h1, _⟩ <;> nlinarith [h1]

/-- Basic trigonometric bounds on the open angular interval `(0, π/2)`. -/
theorem trig_bounds_st {φ : ℝ} (hφ : φ ∈ Ioo 0 (Real.pi / 2)) :
    0 < Real.sin φ ∧ 0 < Real.cos φ ∧ Real.cos φ < 1 := by
  have hsin : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])
  have hcos : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
  refine ⟨hsin, hcos, ?_⟩
  have hpy := Real.sin_sq_add_cos_sq φ
  nlinarith [hsin, hcos, hpy]

theorem capXSt_sub_centre (c e R φ : ℝ) : capXSt c e R φ - c = e * (R * Real.cos φ) := by
  simp [capXSt]

theorem capXSt_mem (hR : 0 < R) (h : CapGeomSt L R c e) {φ : ℝ}
    (hφ : φ ∈ Ioo 0 (Real.pi / 2)) : capXSt c e R φ ∈ capSetSt c e R := by
  obtain ⟨hsin, hcos0, hcos1⟩ := trig_bounds_st hφ
  have h1 := h.sq_one
  have hkey : e * (capXSt c e R φ - c) = R * Real.cos φ := by
    rw [capXSt_sub_centre]
    linear_combination (R * Real.cos φ) * h1
  exact ⟨by rw [hkey]; positivity, by rw [hkey]; nlinarith⟩

theorem sq_sub_lt (hR : 0 < R) (h : CapGeomSt L R c e) {φ : ℝ}
    (hφ : φ ∈ Ioo 0 (Real.pi / 2)) : (capXSt c e R φ - c) ^ 2 < R ^ 2 := by
  obtain ⟨hsin, hcos0, hcos1⟩ := trig_bounds_st hφ
  have h1 := h.sq_one
  have hexp : (capXSt c e R φ - c) ^ 2 = R ^ 2 * Real.cos φ ^ 2 := by
    rw [capXSt_sub_centre]
    linear_combination (R ^ 2 * Real.cos φ ^ 2) * h1
  have hpos : (0 : ℝ) < R ^ 2 * (1 - Real.cos φ ^ 2) := by
    have : (0 : ℝ) < 1 - Real.cos φ ^ 2 := by nlinarith
    positivity
  nlinarith [hexp, hpos]

theorem profile_capXSt (hR : 0 < R) (h : CapGeomSt L R c e) {φ : ℝ}
    (hφ : φ ∈ Ioo 0 (Real.pi / 2)) :
    profile (Cap.hemisphere 1) (Cap.hemisphere 1) L R (capXSt c e R φ) = R * Real.sin φ := by
  obtain ⟨hsin, hcos0, hcos1⟩ := trig_bounds_st hφ
  have hval := (h.prof _ (h.capXSt_mem hR hφ)).self_of_nhds
  rw [hval]
  show Real.sqrt (R ^ 2 - (capXSt c e R φ - c) ^ 2) = R * Real.sin φ
  have h1 := h.sq_one
  have hsq : R ^ 2 - (capXSt c e R φ - c) ^ 2 = (R * Real.sin φ) ^ 2 := by
    rw [capXSt_sub_centre]
    have h2 := Real.sin_sq_add_cos_sq φ
    linear_combination (-(R ^ 2 * Real.cos φ ^ 2)) * h1 + (-(R ^ 2)) * h2
  rw [hsq, Real.sqrt_sq (by positivity)]

/-- **The area element on the arc, in the angular variable**: `√(1 + r'²) = 1 / sin φ`. -/
theorem areaElement_capXSt (hR : 0 < R) (h : CapGeomSt L R c e) {φ : ℝ}
    (hφ : φ ∈ Ioo 0 (Real.pi / 2)) :
    areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R (capXSt c e R φ)
      = 1 / Real.sin φ := by
  obtain ⟨hsin, hcos0, hcos1⟩ := trig_bounds_st hφ
  rw [areaElement_arc_st hR c (h.prof _ (h.capXSt_mem hR hφ)) (h.sq_sub_lt hR hφ),
    h.profile_capXSt hR hφ]
  field_simp

/-- The arc parametrisation is injective on `(0, π/2)`. -/
theorem injOn_capXSt (hR : 0 < R) (h : CapGeomSt L R c e) :
    InjOn (capXSt c e R) (Ioo 0 (Real.pi / 2)) := by
  intro a ha b hb hab
  have h1 := h.sq_one
  have hcos : Real.cos a = Real.cos b := by
    have hd : capXSt c e R a - c = capXSt c e R b - c := by rw [hab]
    rw [capXSt_sub_centre, capXSt_sub_centre] at hd
    have h2 : R * Real.cos a = R * Real.cos b := by
      have := congrArg (fun z => e * z) hd
      simp only at this
      nlinarith [this, h1]
    exact mul_left_cancel₀ (ne_of_gt hR) h2
  have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ Icc 0 Real.pi := fun t ht =>
    ⟨ht.1.le, by linarith [ht.2, Real.pi_pos]⟩
  exact Real.injOn_cos (hsub ha) (hsub hb) hcos

theorem hasDerivWithinAt_capXSt (φ : ℝ) (s : Set ℝ) :
    HasDerivWithinAt (capXSt c e R) (-(e * (R * Real.sin φ))) s φ := by
  have hc : HasDerivAt Real.cos (-Real.sin φ) φ := Real.hasDerivAt_cos φ
  have h2 := ((hc.const_mul R).const_mul e).const_add c
  have h3 : HasDerivAt (capXSt c e R) (e * (R * -Real.sin φ)) φ := h2
  have h4 : e * (R * -Real.sin φ) = -(e * (R * Real.sin φ)) := by ring
  rw [h4] at h3
  exact h3.hasDerivWithinAt

/-- **The inverse of the arc parametrisation** on a cap interval: `φ = arccos(e(x-c)/R)`. -/
theorem capSetSt_inv (hR : 0 < R) (h : CapGeomSt L R c e) {y : ℝ} (hy : y ∈ capSetSt c e R) :
    Real.arccos (e * (y - c) / R) ∈ Ioo 0 (Real.pi / 2) ∧
      capXSt c e R (Real.arccos (e * (y - c) / R)) = y := by
  have h1 := h.sq_one
  obtain ⟨hy1, hy2⟩ := hy
  have hle : e * (y - c) / R ≤ 1 := by rw [div_le_one hR]; exact hy2.le
  have hge : (-1 : ℝ) ≤ e * (y - c) / R := by
    have : (0 : ℝ) ≤ e * (y - c) / R := le_of_lt (by positivity)
    linarith
  refine ⟨⟨Real.arccos_pos.2 (by rw [div_lt_one hR]; exact hy2), ?_⟩, ?_⟩
  · rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    have : 0 < Real.arcsin (e * (y - c) / R) := Real.arcsin_pos.2 (by positivity)
    linarith
  · rw [capXSt, Real.cos_arccos hge hle]
    have hRne : R ≠ 0 := ne_of_gt hR
    field_simp
    linear_combination (y - c) * h1

/-- The inverse formula, on the angular side. -/
theorem arccos_capXSt (h : CapGeomSt L R c e) (hR : 0 < R) {φ : ℝ}
    (hφ : φ ∈ Ioo 0 (Real.pi / 2)) :
    Real.arccos (e * (capXSt c e R φ - c) / R) = φ := by
  have h1 := h.sq_one
  have hRne : R ≠ 0 := ne_of_gt hR
  have hval : e * (capXSt c e R φ - c) / R = Real.cos φ := by
    rw [capXSt_sub_centre]
    have hcancel : e * (e * (R * Real.cos φ)) = R * Real.cos φ := by
      linear_combination (R * Real.cos φ) * h1
    rw [hcancel]
    field_simp
  rw [hval, Real.arccos_cos hφ.1.le (by linarith [hφ.2, Real.pi_pos])]

/-- **The cap interval is the image of `(0, π/2)` under the arc parametrisation.** -/
theorem capSetSt_eq_image (hR : 0 < R) (h : CapGeomSt L R c e) :
    capSetSt c e R = capXSt c e R '' Ioo 0 (Real.pi / 2) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hmem, heq⟩ := h.capSetSt_inv hR hy
    exact ⟨_, hmem, heq⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact h.capXSt_mem hR hφ

end CapGeomSt


/-! ### The change of variables `x = c + e R cos φ`, i.e. `A(x) dx = R dφ` -/

/-- **The angular change of variables on a cap interval.**  The Jacobian is `R sin φ`. -/
theorem integral_capSetSt_eq (hR : 0 < R) (h : CapGeomSt L R c e) (G : ℝ → ℝ) :
    (∫ x in capSetSt c e R, G x)
      = ∫ φ in Ioo 0 (Real.pi / 2), (R * Real.sin φ) * G (capXSt c e R φ) := by
  rw [h.capSetSt_eq_image hR,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun φ _ => CapGeomSt.hasDerivWithinAt_capXSt (c := c) (e := e) (R := R) φ _)
      (h.injOn_capXSt hR) G]
  refine setIntegral_congr_fun measurableSet_Ioo (fun φ hφ => ?_)
  obtain ⟨hsin, _, _⟩ := CapGeomSt.trig_bounds_st hφ
  rw [smul_eq_mul]
  congr 1
  rw [abs_neg, abs_mul, h.abs_eq_one, one_mul, abs_mul, abs_of_pos hR, abs_of_pos hsin]

/-- Integrability transfers along the angular change of variables. -/
theorem integrableOn_capSetSt_iff (hR : 0 < R) (h : CapGeomSt L R c e) (G : ℝ → ℝ) :
    IntegrableOn G (capSetSt c e R) volume
      ↔ IntegrableOn (fun φ => (R * Real.sin φ) * G (capXSt c e R φ))
          (Ioo 0 (Real.pi / 2)) volume := by
  rw [h.capSetSt_eq_image hR,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun φ _ => CapGeomSt.hasDerivWithinAt_capXSt (c := c) (e := e) (R := R) φ _)
      (h.injOn_capXSt hR) G]
  refine integrableOn_congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with φ hφ
  obtain ⟨hsin, _, _⟩ := CapGeomSt.trig_bounds_st hφ
  rw [smul_eq_mul, abs_neg, abs_mul, h.abs_eq_one, one_mul, abs_mul, abs_of_pos hR,
    abs_of_pos hsin]

/-! ### The two caps of the stadium -/

theorem capSetSt_left_eq (_hR : 0 < R) :
    capSetSt (interfaceL (Cap.hemisphere 1) L R) (-1) R
      = Ioo (-L / 2) (interfaceL (Cap.hemisphere 1) L R) := by
  ext y
  simp only [capSetSt, mem_setOf_eq, mem_Ioo, interfaceL_st]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem capSetSt_right_eq (_hR : 0 < R) :
    capSetSt (interfaceR (Cap.hemisphere 1) L R) 1 R
      = Ioo (interfaceR (Cap.hemisphere 1) L R) (L / 2) := by
  ext y
  simp only [capSetSt, mem_setOf_eq, mem_Ioo, interfaceR_st]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem capGeomSt_left (hR : 0 < R) (hL : 2 * R < L) :
    CapGeomSt L R (interfaceL (Cap.hemisphere 1) L R) (-1) where
  sq_one := by norm_num
  prof := by
    intro y hy
    rw [capSetSt_left_eq hR] at hy
    exact profile_eventuallyEq_left_st hR hL hy
  sub := by
    rw [capSetSt_left_eq hR, interfaceL_st]
    exact Ioo_subset_Ioo le_rfl (by linarith)

theorem capGeomSt_right (hR : 0 < R) (hL : 2 * R < L) :
    CapGeomSt L R (interfaceR (Cap.hemisphere 1) L R) 1 where
  sq_one := by norm_num
  prof := by
    intro y hy
    rw [capSetSt_right_eq hR] at hy
    exact profile_eventuallyEq_right_st hR hL hy
  sub := by
    rw [capSetSt_right_eq hR, interfaceR_st]
    exact Ioo_subset_Ioo (by linarith) le_rfl


/-! ## 4. The interface: radial absolute continuity on the caps -/

/-- The point of the radial ray of angle `φ` at the shifted radial parameter `t`, i.e. at polar
radius `ρ = t + R/2`.  For `t ∈ (0, R/2)` this sweeps the outer half `ρ ∈ (R/2, R)` of the
ray, the part on which the one-dimensional trace inequality is applied. -/
def capSliceSt (c e s R φ t : ℝ) : CapSpace 1 := capPtSt c e s φ (t + R / 2)

@[simp] theorem capSliceSt_end (c e s R φ : ℝ) :
    capSliceSt c e s R φ (R / 2) = capPtSt c e s φ R := by
  simp only [capSliceSt]
  norm_num

/-- The full `H¹` density `u² + (∂ₓu)² + ‖∇_z u‖²` of `u` along the radial ray of angle `φ`. -/
def capDensSt (R : ℝ) (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c e s φ t : ℝ) : ℝ :=
  u.toFun (capSliceSt c e s R φ t) ^ 2 + u.gx (capSliceSt c e s R φ t) ^ 2
    + ‖u.gz (capSliceSt c e s R φ t)‖ ^ 2

theorem capDensSt_nonneg (R : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c e s φ t : ℝ) :
    0 ≤ capDensSt R u c e s φ t := by
  unfold capDensSt; positivity

/-- **The polar energy of `u` on the outer half of the radial ray of angle `φ`**,
`∫_{R/2}^{R} (u² + |∇u|²) ρ dρ`, written in the shifted variable `t = ρ − R/2`. -/
def arcEnergySt (R : ℝ) (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c e s : ℝ) (φ : ℝ) : ℝ :=
  ∫ t in Ioo 0 (R / 2), capDensSt R u c e s φ t * (t + R / 2)

theorem arcEnergySt_nonneg (hR : 0 < R)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) (c e s φ : ℝ) :
    0 ≤ arcEnergySt R u c e s φ := by
  refine setIntegral_nonneg measurableSet_Ioo (fun t ht => ?_)
  exact mul_nonneg (capDensSt_nonneg R u c e s φ t) (by linarith [ht.1, hR])

/-- The endpoint trace on the upper (`s = 1`) or lower (`s = -1`) half of the lateral
boundary. -/
def trSideSt (s : ℝ) (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (x : ℝ) : ℝ := if 0 < s then trPlus u x else trMinus u x

@[simp] theorem trSideSt_one (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (x : ℝ) : trSideSt 1 u x = trPlus u x := by rw [trSideSt, if_pos one_pos]

@[simp] theorem trSideSt_neg_one (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (x : ℝ) : trSideSt (-1) u x = trMinus u x := by
  rw [trSideSt, if_neg (by norm_num : ¬ (0 : ℝ) < -1)]

theorem trSideSt_one_eq (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    trSideSt 1 u = trPlus u := funext fun x => trSideSt_one u x

theorem trSideSt_neg_one_eq (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    trSideSt (-1) u = trMinus u := funext fun x => trSideSt_neg_one u x

/-- **The interface: radial absolute continuity along one quarter of one hemispherical cap.**

This is the single analytic input of this file; it is exactly what
`RobinCaps/Sobolev/RadialSlice.lean` (radial ACL on a ball, polar coordinates) has to deliver,
transported to the quarter-disk `{(c + e ρ cos φ, s ρ sin φ) | ρ ∈ (0,R), φ ∈ (0, π/2)}` of the
cap centred at `(c, 0)`, with axial sign `e = ±1` and transverse sign `s = ±1`.

`T : ℝ → ℝ` is the **radial trace**: `T φ` is the boundary value of `u` at the arc point
`capPtSt c e s φ R` of angle `φ`, obtained as the endpoint value at `ρ = R` of the absolutely
continuous representative of the radial slice.

All the fields are a.e. statements in the angle `φ ∈ (0, π/2)`. -/
structure ArcTraceSt (L R : ℝ) (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R))
    (c e s : ℝ) (T : ℝ → ℝ) : Prop where
  /-- (M) The radial trace is a.e. strongly measurable in the angle. -/
  aesm : AEStronglyMeasurable T (volume.restrict (Ioo 0 (Real.pi / 2)))
  /-- (AC) **Radial absolute continuity.**  For a.e. angle `φ` the radial slice
  `ρ ↦ u(c + e ρ cos φ, s ρ sin φ)` has, on the outer half `ρ ∈ (R/2, R)` — written with
  `ρ = t + R/2`, `t ∈ (0, R/2)` — an absolutely continuous representative `W` in the concrete
  one-dimensional Sobolev model `RobinCaps.Sobolev.H1 (R/2)`, whose classical derivative is
  the radial component `⟪∇u, ν⟫` of the weak gradient, `ν = (e cos φ, s sin φ)` being the unit
  radial direction, and whose value at the right endpoint `t = R/2` (i.e. at the arc point
  `ρ = R`) is the radial trace `T φ`. -/
  radAC : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
    ∃ W : Sobolev.H1 (R / 2),
      W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
          (fun t => u.toFun (capSliceSt c e s R φ t)) ∧
        deriv W.toFun =ᵐ[volume.restrict (Ioo 0 (R / 2))]
          (fun t => e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
            + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ∧
        W.toFun (R / 2) = T φ
  /-- (F1) **Fubini along the rays.**  For a.e. angle the `H¹` density of `u` is integrable
  along the outer half of the ray, both with and without the polar weight `ρ = t + R/2`. -/
  radIntegrable : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
    IntegrableOn (fun t => capDensSt R u c e s φ t) (Ioo 0 (R / 2)) volume ∧
      IntegrableOn (fun t => capDensSt R u c e s φ t * (t + R / 2)) (Ioo 0 (R / 2)) volume
  /-- (F2) **Fubini in the angle.**  The polar energy of the rays is integrable in `φ`. -/
  energy_integrable : IntegrableOn (arcEnergySt R u c e s) (Ioo 0 (Real.pi / 2)) volume
  /-- (P) **The polar change of variables on the quarter-disk**, together with the inclusion of
  the quarter-disk in the thin domain: the total polar energy of the quarter-annulus
  `{R/2 < ρ < R, 0 < φ < π/2}` is at most the full `H¹` energy of `u` on `Ω_R`. -/
  energy_le : (∫ φ in Ioo 0 (Real.pi / 2), arcEnergySt R u c e s φ) ≤ massP u + dirichletP u
  /-- (I) **The identification of the two traces.**  For a.e. angle `φ` the vertical-slice
  endpoint trace of `TraceOne.lean` at the abscissa `capXSt c e R φ` of the arc point — that is
  `trPlus` for `s = 1` and `trMinus` for `s = -1` — coincides with the radial trace `T φ`.
  Both are boundary values of `u` at the *same* point of the lateral boundary, reached along
  two different directions; the equality is a genuinely two-dimensional fact. -/
  vert_eq : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
    trSideSt s u (capXSt c e R φ) = T φ

/-- **The radial absolute continuity hypothesis for the whole stadium**: all four quarters
(two caps `e = ∓1`, two transverse signs `s = ±1`) carry a radial trace. -/
structure RadialACL (L R : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) : Prop where
  /-- Each quarter of each cap has a radial trace satisfying `ArcTraceSt`. -/
  arc : ∀ c e s : ℝ, CapGeomSt L R c e → s ^ 2 = 1 →
    ∃ T : ℝ → ℝ, ArcTraceSt L R u c e s T


/-! ## 5. The one-dimensional trace bound along the radial rays -/

/-- The arc trace constant: `8/R² + 2`. -/
def arcConstSt (R : ℝ) : ℝ := 8 / R ^ 2 + 2

theorem arcConstSt_nonneg (hR : 0 < R) : 0 ≤ arcConstSt R := by
  unfold arcConstSt; positivity

/-- **The radial component of the gradient is dominated by the full gradient.**  Since
`(e cos φ, s sin φ)` is a unit vector for `e² = s² = 1`, Cauchy–Schwarz gives
`⟪∇u, ν⟫² ≤ (∂ₓu)² + ‖∇_z u‖²`. -/
theorem radial_deriv_sq_le_st {e s φ a b : ℝ} (he : e ^ 2 = 1) (hs : s ^ 2 = 1) :
    (e * Real.cos φ * a + s * Real.sin φ * b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have hpy := Real.sin_sq_add_cos_sq φ
  have key : a ^ 2 + b ^ 2 - (e * Real.cos φ * a + s * Real.sin φ * b) ^ 2
      = (a * Real.sin φ - e * s * b * Real.cos φ) ^ 2 := by
    linear_combination (-(a ^ 2 * Real.cos φ ^ 2) - b ^ 2 * Real.cos φ ^ 2) * he
      + (-(b ^ 2 * Real.sin φ ^ 2) - b ^ 2 * Real.cos φ ^ 2 * e ^ 2) * hs
      + (-(a ^ 2) - b ^ 2) * hpy
  nlinarith [key, sq_nonneg (a * Real.sin φ - e * s * b * Real.cos φ)]

/-- **Deliverable 3 (pointwise).**  For a.e. angle, the squared radial trace is bounded by
`(8/R² + 2)` times the polar energy of the ray: this is the one-dimensional trace inequality
on `[R/2, R]` (`Sobolev.endpoint_ell_sq_le`), followed by the insertion of the polar weight
`ρ ≥ R/2`. -/
theorem arc_sq_ae_le_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (ha : ArcTraceSt L R u c e s T) :
    ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
      T φ ^ 2 ≤ arcConstSt R * arcEnergySt R u c e s φ := by
  filter_upwards [ha.radAC, ha.radIntegrable] with φ hAC hInt
  obtain ⟨W, hW, hWd, hWend⟩ := hAC
  obtain ⟨hint1, hint2⟩ := hInt
  have hl : (0 : ℝ) < R / 2 := by linarith
  set E : ℝ := ∫ t in Ioo 0 (R / 2), capDensSt R u c e s φ t with hE
  set A : ℝ := arcEnergySt R u c e s φ with hA
  -- the trace inequality of `Sobolev/Interval.lean` at the right endpoint
  have hend := Sobolev.endpoint_ell_sq_le W hl
  rw [hWend] at hend
  -- the mass of the radial slice
  have hmass : Sobolev.mass (R / 2) W
      = ∫ t in Ioo 0 (R / 2), u.toFun (capSliceSt c e s R φ t) ^ 2 := by
    rw [Sobolev.mass, Sobolev.intervalIntegral_eq_setIntegral_Ioo hl.le]
    exact integral_congr_ae (by filter_upwards [hW] with t ht; rw [ht])
  have hdir : Sobolev.dirichlet (R / 2) W
      = ∫ t in Ioo 0 (R / 2), (e * Real.cos φ * u.gx (capSliceSt c e s R φ t)
          + s * Real.sin φ * u.gz (capSliceSt c e s R φ t) 0) ^ 2 := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hl.le]
    exact integral_congr_ae (by filter_upwards [hWd] with t ht; rw [ht])
  -- both are bounded by the full `H¹` density of the ray
  have hM : Sobolev.mass (R / 2) W ≤ E := by
    rw [hmass, hE]
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) hint1 ?_
    exact Eventually.of_forall fun t => by
      simp only [capDensSt]; nlinarith [sq_nonneg (u.gx (capSliceSt c e s R φ t)),
        norm_nonneg (u.gz (capSliceSt c e s R φ t)), sq_nonneg ‖u.gz (capSliceSt c e s R φ t)‖]
  have hD : Sobolev.dirichlet (R / 2) W ≤ E := by
    rw [hdir, hE]
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) hint1 ?_
    refine Eventually.of_forall fun t => ?_
    simp only [capDensSt]
    have hrad := radial_deriv_sq_le_st (e := e) (s := s) (φ := φ)
      (a := u.gx (capSliceSt c e s R φ t)) (b := u.gz (capSliceSt c e s R φ t) 0) he hs
    have hnorm := norm_sq_one_dim (u.gz (capSliceSt c e s R φ t))
    nlinarith [hrad, hnorm, sq_nonneg (u.toFun (capSliceSt c e s R φ t))]
  -- the polar weight `ρ = t + R/2 ≥ R/2`
  have hEA : E ≤ (2 / R) * A := by
    rw [hE, hA, arcEnergySt, ← integral_const_mul]
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
  have hEnn : 0 ≤ E := by
    rw [hE]
    exact setIntegral_nonneg measurableSet_Ioo fun t _ => capDensSt_nonneg R u c e s φ t
  -- assembling
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


/-! ## 6. From the rays to the arc: integrability, measurability and the arc bound -/

theorem integrableOn_arc_sq_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (ha : ArcTraceSt L R u c e s T) :
    IntegrableOn (fun φ => T φ ^ 2) (Ioo 0 (Real.pi / 2)) volume := by
  refine Integrable.mono' (ha.energy_integrable.const_mul (arcConstSt R)) (ha.aesm.pow 2) ?_
  filter_upwards [arc_sq_ae_le_st hR he hs ha] with φ hφ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hφ

theorem integral_arc_sq_le_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (ha : ArcTraceSt L R u c e s T) :
    (∫ φ in Ioo 0 (Real.pi / 2), T φ ^ 2) ≤ arcConstSt R * (massP u + dirichletP u) := by
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun φ => sq_nonneg _)
    (ha.energy_integrable.const_mul (arcConstSt R)) (arc_sq_ae_le_st hR he hs ha)) ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left ha.energy_le (arcConstSt_nonneg hR)

/-- **The arc parametrisation maps null sets to null sets** (it is Lipschitz; here this is
obtained from the one-dimensional change-of-variables formula for `lintegral`). -/
theorem null_image_capXSt (hR : 0 < R) {c e : ℝ} (hg : CapGeomSt L R c e) {N : Set ℝ}
    (hN : MeasurableSet N) (hNs : N ⊆ Ioo 0 (Real.pi / 2)) (hN0 : volume N = 0) :
    volume (capXSt c e R '' N) = 0 := by
  have hkey := lintegral_image_eq_lintegral_abs_deriv_mul (f := capXSt c e R)
    (f' := fun φ => -(e * (R * Real.sin φ))) hN
    (fun φ _ => CapGeomSt.hasDerivWithinAt_capXSt (c := c) (e := e) (R := R) φ N)
    ((hg.injOn_capXSt hR).mono hNs) (fun _ => 1)
  simp only [mul_one] at hkey
  rw [lintegral_one, Measure.restrict_apply_univ] at hkey
  rw [hkey]
  exact setLIntegral_measure_zero _ _ hN0

/-- The cap interval is open, hence measurable. -/
theorem isOpen_capSetSt (c e R : ℝ) : IsOpen (capSetSt c e R) :=
  isOpen_Ioo.preimage (continuous_const.mul (continuous_id.sub continuous_const))

theorem measurableSet_capSetSt (c e R : ℝ) : MeasurableSet (capSetSt c e R) :=
  (isOpen_capSetSt c e R).measurableSet

/-- **Measurability of the endpoint trace on a cap interval**, transported from the angular
measurability of the radial trace along the arc parametrisation.  The transport is legitimate
because the arc parametrisation maps null sets to null sets (`null_image_capXSt`). -/
theorem aesm_trSide_cap_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e s : ℝ} {T : ℝ → ℝ}
    (hg : CapGeomSt L R c e) (ha : ArcTraceSt L R u c e s T) :
    AEStronglyMeasurable (trSideSt s u) (volume.restrict (capSetSt c e R)) := by
  classical
  set g0 : ℝ → ℝ := ha.aesm.mk T with hg0def
  set ψ : ℝ → ℝ := fun x => Real.arccos (e * (x - c) / R) with hψdef
  have hψm : Measurable ψ :=
    (Real.continuous_arccos.comp
      ((continuous_const.mul (continuous_id.sub continuous_const)).div_const R)).measurable
  refine ⟨g0 ∘ ψ, ha.aesm.stronglyMeasurable_mk.comp_measurable hψm, ?_⟩
  have hnull : volume ({φ | ¬ trSideSt s u (capXSt c e R φ) = g0 φ}
      ∩ Ioo 0 (Real.pi / 2)) = 0 := by
    have hae : ∀ᵐ φ ∂(volume.restrict (Ioo 0 (Real.pi / 2))),
        trSideSt s u (capXSt c e R φ) = g0 φ := by
      filter_upwards [ha.vert_eq, ha.aesm.ae_eq_mk] with φ h1 h2
      rw [h1, h2]
    rw [ae_iff, Measure.restrict_apply' measurableSet_Ioo] at hae
    exact hae
  obtain ⟨N, hNsup, hNmeas, hNzero⟩ := exists_measurable_superset_of_null hnull
  have hN'meas : MeasurableSet (N ∩ Ioo 0 (Real.pi / 2)) := hNmeas.inter measurableSet_Ioo
  have hN'zero : volume (N ∩ Ioo 0 (Real.pi / 2)) = 0 :=
    measure_mono_null inter_subset_left hNzero
  have himg := null_image_capXSt hR hg hN'meas inter_subset_right hN'zero
  have hBsub : {x | ¬ trSideSt s u x = (g0 ∘ ψ) x} ∩ capSetSt c e R
      ⊆ capXSt c e R '' (N ∩ Ioo 0 (Real.pi / 2)) := by
    rintro x ⟨hx1, hx2⟩
    obtain ⟨hmem, heq⟩ := hg.capSetSt_inv hR hx2
    have hne : ¬ trSideSt s u (capXSt c e R (ψ x)) = g0 (ψ x) := by
      intro hcon
      exact hx1 (by rw [Function.comp_apply, ← hcon, heq])
    exact ⟨ψ x, ⟨hNsup (Set.mem_inter hne hmem), hmem⟩, heq⟩
  rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' (measurableSet_capSetSt c e R)]
  exact measure_mono_null hBsub himg


/-! ## 7. The arc bound on a cap interval -/

/-- **The angular density of the lateral boundary integral on a cap is `R (T₊² + T₋²)`.**
The area element `1/sin φ` cancels against the Jacobian `R sin φ` of the angular change of
variables: this is the identity `A(x) dx = R dφ` (arc length). -/
theorem cap_density_ae_eq_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e : ℝ}
    {Tp Tm : ℝ → ℝ} (hg : CapGeomSt L R c e)
    (hp : ArcTraceSt L R u c e 1 Tp) (hm : ArcTraceSt L R u c e (-1) Tm) :
    (fun φ => (R * Real.sin φ) * (areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R
        (capXSt c e R φ)
        * (trPlus u (capXSt c e R φ) ^ 2 + trMinus u (capXSt c e R φ) ^ 2)))
      =ᵐ[volume.restrict (Ioo 0 (Real.pi / 2))] fun φ => R * (Tp φ ^ 2 + Tm φ ^ 2) := by
  filter_upwards [hp.vert_eq, hm.vert_eq, ae_restrict_mem measurableSet_Ioo] with φ h1 h2 hφ
  obtain ⟨hsin, _, _⟩ := CapGeomSt.trig_bounds_st hφ
  rw [trSideSt_one] at h1
  rw [trSideSt_neg_one] at h2
  rw [hg.areaElement_capXSt hR hφ, h1, h2]
  field_simp

theorem integrableOn_cap_density_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e : ℝ}
    {Tp Tm : ℝ → ℝ} (hg : CapGeomSt L R c e)
    (hp : ArcTraceSt L R u c e 1 Tp) (hm : ArcTraceSt L R u c e (-1) Tm) :
    IntegrableOn (fun x => areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
        * (trPlus u x ^ 2 + trMinus u x ^ 2)) (capSetSt c e R) volume := by
  rw [integrableOn_capSetSt_iff hR hg]
  refine (integrableOn_congr_fun_ae (cap_density_ae_eq_st hR hg hp hm)).2 ?_
  exact ((integrableOn_arc_sq_st hR hg.sq_one (by norm_num) hp).add
    (integrableOn_arc_sq_st hR hg.sq_one (by norm_num) hm)).const_mul R

/-- **Deliverable 3: the arc trace bound.**  On a cap interval the lateral boundary integral of
the squared trace is at most `2 R (8/R² + 2)` times the full `H¹` energy of `u`. -/
theorem arc_trace_bound_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e : ℝ}
    {Tp Tm : ℝ → ℝ} (hg : CapGeomSt L R c e)
    (hp : ArcTraceSt L R u c e 1 Tp) (hm : ArcTraceSt L R u c e (-1) Tm) :
    (∫ x in capSetSt c e R, areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
        * (trPlus u x ^ 2 + trMinus u x ^ 2))
      ≤ 2 * R * arcConstSt R * (massP u + dirichletP u) := by
  rw [integral_capSetSt_eq hR hg, integral_congr_ae (cap_density_ae_eq_st hR hg hp hm),
    integral_const_mul,
    integral_add (integrableOn_arc_sq_st hR hg.sq_one (by norm_num) hp)
      (integrableOn_arc_sq_st hR hg.sq_one (by norm_num) hm)]
  have h1 := integral_arc_sq_le_st hR hg.sq_one (by norm_num : (1 : ℝ) ^ 2 = 1) hp
  have h2 := integral_arc_sq_le_st hR hg.sq_one (by norm_num : (-1 : ℝ) ^ 2 = 1) hm
  nlinarith [h1, h2, hR.le]

theorem aesm_trPlus_cap_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e : ℝ} {Tp : ℝ → ℝ}
    (hg : CapGeomSt L R c e) (hp : ArcTraceSt L R u c e 1 Tp) :
    AEStronglyMeasurable (trPlus u) (volume.restrict (capSetSt c e R)) := by
  have h := aesm_trSide_cap_st hR hg hp
  rwa [trSideSt_one_eq] at h

theorem aesm_trMinus_cap_st (hR : 0 < R)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} {c e : ℝ} {Tm : ℝ → ℝ}
    (hg : CapGeomSt L R c e) (hm : ArcTraceSt L R u c e (-1) Tm) :
    AEStronglyMeasurable (trMinus u) (volume.restrict (capSetSt c e R)) := by
  have h := aesm_trSide_cap_st hR hg hm
  rwa [trSideSt_neg_one_eq] at h


/-! ## 8. Assembling the three pieces of the axial interval -/

theorem Ioo_ae_eq_three_st {p a b q : ℝ} (h1 : p < a) (h2 : a < b) (h3 : b < q) :
    Ioo p q =ᵐ[volume] (((Ioo p a ∪ Ioo a b) ∪ Ioo b q : Set ℝ)) := by
  have hsub : Ioo p q \ ((Ioo p a ∪ Ioo a b) ∪ Ioo b q) ⊆ ({a, b} : Set ℝ) := by
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    simp only [mem_union, mem_Ioo, not_or] at hx3
    obtain ⟨⟨hA, hB⟩, hC⟩ := hx3
    push_neg at hA hB hC
    have hax : a ≤ x := hA hx1
    rcases eq_or_lt_of_le hax with h | h
    · exact Or.inl h.symm
    · have hbx : b ≤ x := hB h
      rcases eq_or_lt_of_le hbx with h' | h'
      · exact Or.inr (mem_singleton_iff.2 h'.symm)
      · exact absurd (hC h') (by linarith)
  have hsub2 : ((Ioo p a ∪ Ioo a b) ∪ Ioo b q : Set ℝ) ⊆ Ioo p q := by
    rintro x ((⟨hx, hx'⟩ | ⟨hx, hx'⟩) | ⟨hx, hx'⟩) <;>
      exact ⟨by linarith, by linarith⟩
  rw [ae_eq_set]
  refine ⟨measure_mono_null hsub ?_, by rw [Set.diff_eq_empty.2 hsub2]; simp⟩
  exact (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume

theorem axial_lt_st (hR : 0 < R) (hL : 2 * R < L) :
    -L / 2 < interfaceL (Cap.hemisphere 1) L R ∧
      interfaceL (Cap.hemisphere 1) L R < interfaceR (Cap.hemisphere 1) L R ∧
        interfaceR (Cap.hemisphere 1) L R < L / 2 := by
  rw [interfaceL_st, interfaceR_st]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem axial_ae_eq_union_st (hR : 0 < R) (hL : 2 * R < L) :
    Ioo (-L / 2) (L / 2)
      =ᵐ[volume] ((capSetSt (interfaceL (Cap.hemisphere 1) L R) (-1) R
          ∪ Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R))
        ∪ capSetSt (interfaceR (Cap.hemisphere 1) L R) 1 R : Set ℝ) := by
  obtain ⟨ha, hb, hc⟩ := axial_lt_st hR hL
  rw [capSetSt_left_eq hR, capSetSt_right_eq hR]
  exact Ioo_ae_eq_three_st ha hb hc

theorem disjoint_pieces_st (hR : 0 < R) (hL : 2 * R < L) :
    Disjoint (capSetSt (interfaceL (Cap.hemisphere 1) L R) (-1) R)
        (Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R)) ∧
      Disjoint (capSetSt (interfaceL (Cap.hemisphere 1) L R) (-1) R
          ∪ Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R))
        (capSetSt (interfaceR (Cap.hemisphere 1) L R) 1 R) := by
  obtain ⟨ha, hb, hc⟩ := axial_lt_st hR hL
  rw [capSetSt_left_eq hR, capSetSt_right_eq hR]
  constructor
  · rw [Set.disjoint_left]
    rintro x ⟨_, hx⟩ ⟨hy, _⟩
    linarith
  · rw [Set.disjoint_left]
    rintro x hx ⟨hy, _⟩
    rcases hx with ⟨_, hx2⟩ | ⟨_, hx2⟩ <;> linarith



/-! ### Consistency: the quarter-disks really lie inside the stadium -/

/-- **The radial rays of a cap stay inside the thin domain.**  Every point at polar radius
`ρ < R` around the centre `(c, 0)` of a cap belongs to `Ω_R` (the stadium is the `R`-neighbourhood
of the axial segment `[x₋, x₊] × {0}`, and `c` is an endpoint of that segment).  This lemma is
not used in the proofs below; it records that the interface `ArcTraceSt` speaks about points of
`Ω_R`, so that it is not vacuous. -/
theorem capPtSt_mem_thinDomain_st (hR : 0 < R) (hL : 2 * R < L) {c e s : ℝ}
    (he : e ^ 2 = 1) (hs : s ^ 2 = 1) (hc : c ∈ Icc (-(L / 2 - R)) (L / 2 - R))
    {φ ρ : ℝ} (hρ : ρ ^ 2 < R ^ 2) :
    capPtSt c e s φ ρ ∈ thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R := by
  rw [mem_thinDomain_hemisphere_iff hR hL]
  refine ⟨c, hc, ?_⟩
  have hpy := Real.sin_sq_add_cos_sq φ
  have h1 : (capPtSt c e s φ ρ).1 - c = e * (ρ * Real.cos φ) := by simp [capPtSt]
  have h2 : ‖(capPtSt c e s φ ρ).2‖ = |s * (ρ * Real.sin φ)| := ept_norm _
  rw [h1, h2, sq_abs]
  have hid : (e * (ρ * Real.cos φ)) ^ 2 + (s * (ρ * Real.sin φ)) ^ 2 = ρ ^ 2 := by
    linear_combination (ρ ^ 2 * Real.cos φ ^ 2) * he + (ρ ^ 2 * Real.sin φ ^ 2) * hs
      + ρ ^ 2 * hpy
  rw [hid]
  exact hρ

theorem interfaceL_mem_Icc_st (_hR : 0 < R) (hL : 2 * R < L) :
    interfaceL (Cap.hemisphere 1) L R ∈ Icc (-(L / 2 - R)) (L / 2 - R) := by
  rw [interfaceL_st]
  exact ⟨by linarith, by linarith⟩

theorem interfaceR_mem_Icc_st (_hR : 0 < R) (hL : 2 * R < L) :
    interfaceR (Cap.hemisphere 1) L R ∈ Icc (-(L / 2 - R)) (L / 2 - R) := by
  rw [interfaceR_st]
  exact ⟨by linarith, by linarith⟩

/-! ## 9. The main theorem -/

/-- **The trace constant of the stadium**: the bulk constant `max (2/R) (8R)` plus twice the
arc constant `2R (8/R² + 2)` of each of the two caps. -/
def traceConstSt (R : ℝ) : ℝ := traceConstBso R + 4 * R * arcConstSt R

theorem traceConstSt_nonneg (hR : 0 < R) : 0 ≤ traceConstSt R := by
  have h1 := traceConstBso_nonneg hR
  have h2 := arcConstSt_nonneg hR
  have : 0 ≤ 4 * R * arcConstSt R := by positivity
  rw [traceConstSt]; linarith

/-- **The `R`-dependence of the trace constant**: `C(R) ≤ 34/R + 16 R`. -/
theorem traceConstSt_le (hR : 0 < R) : traceConstSt R ≤ 34 / R + 16 * R := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have h1 : (4 : ℝ) / (2 * R) = 2 / R := by field_simp; ring
  have hpos : (0 : ℝ) < 2 / R := by positivity
  have hmax : max (4 / (2 * R)) (4 * (2 * R)) ≤ 2 / R + 8 * R := by
    refine max_le ?_ ?_
    · rw [h1]; nlinarith [hR]
    · nlinarith [hpos, hR]
  have h2 : 4 * R * (8 / R ^ 2 + 2) = 32 / R + 8 * R := by field_simp; ring
  rw [traceConstSt, traceConstBso, arcConstSt, h2]
  have h3 : (2 : ℝ) / R + 32 / R = 34 / R := by field_simp; ring
  linarith [hmax, h3]

/-- **The four pieces of data** supplied by `RadialACL` for a single `u`, assembled into the
four statements of `TraceIneqOne`. -/
theorem trace_pieces_st (hR : 0 < R) (hL : 2 * R < L)
    {u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)} (hu : RadialACL L R u) :
    AEStronglyMeasurable (trPlus u) (volume.restrict (Ioo (-L / 2) (L / 2))) ∧
      AEStronglyMeasurable (trMinus u) (volume.restrict (Ioo (-L / 2) (L / 2))) ∧
      IntegrableOn (fun x => areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
          * (trPlus u x ^ 2 + trMinus u x ^ 2)) (Ioo (-L / 2) (L / 2)) volume ∧
      (∫ x in Ioo (-L / 2) (L / 2), areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
          * (trPlus u x ^ 2 + trMinus u x ^ 2)) ≤ traceConstSt R * (massP u + dirichletP u) := by
  obtain ⟨TLp, hTLp⟩ := hu.arc (interfaceL (Cap.hemisphere 1) L R) (-1) 1
    (capGeomSt_left hR hL) (by norm_num)
  obtain ⟨TLm, hTLm⟩ := hu.arc (interfaceL (Cap.hemisphere 1) L R) (-1) (-1)
    (capGeomSt_left hR hL) (by norm_num)
  obtain ⟨TRp, hTRp⟩ := hu.arc (interfaceR (Cap.hemisphere 1) L R) 1 1
    (capGeomSt_right hR hL) (by norm_num)
  obtain ⟨TRm, hTRm⟩ := hu.arc (interfaceR (Cap.hemisphere 1) L R) 1 (-1)
    (capGeomSt_right hR hL) (by norm_num)
  obtain ⟨hd1, hd2⟩ := disjoint_pieces_st hR hL
  set F : ℝ → ℝ := fun x => areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
    * (trPlus u x ^ 2 + trMinus u x ^ 2) with hF
  have hIL : IntegrableOn F (capSetSt (interfaceL (Cap.hemisphere 1) L R) (-1) R) volume :=
    integrableOn_cap_density_st hR (capGeomSt_left hR hL) hTLp hTLm
  have hIB : IntegrableOn F (Ioo (interfaceL (Cap.hemisphere 1) L R)
      (interfaceR (Cap.hemisphere 1) L R)) volume := integrableOn_bulk_density_st hR hL u
  have hIR : IntegrableOn F (capSetSt (interfaceR (Cap.hemisphere 1) L R) 1 R) volume :=
    integrableOn_cap_density_st hR (capGeomSt_right hR hL) hTRp hTRm
  have hIU : IntegrableOn F (capSetSt (interfaceL (Cap.hemisphere 1) L R) (-1) R
      ∪ Ioo (interfaceL (Cap.hemisphere 1) L R) (interfaceR (Cap.hemisphere 1) L R)) volume :=
    integrableOn_union.2 ⟨hIL, hIB⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Measure.restrict_congr_set (axial_ae_eq_union_st hR hL), aestronglyMeasurable_union_iff,
      aestronglyMeasurable_union_iff]
    exact ⟨⟨aesm_trPlus_cap_st hR (capGeomSt_left hR hL) hTLp, aesm_trPlus_bulk_st hR hL u⟩,
      aesm_trPlus_cap_st hR (capGeomSt_right hR hL) hTRp⟩
  · rw [Measure.restrict_congr_set (axial_ae_eq_union_st hR hL), aestronglyMeasurable_union_iff,
      aestronglyMeasurable_union_iff]
    exact ⟨⟨aesm_trMinus_cap_st hR (capGeomSt_left hR hL) hTLm, aesm_trMinus_bulk_st hR hL u⟩,
      aesm_trMinus_cap_st hR (capGeomSt_right hR hL) hTRm⟩
  · exact (integrableOn_union.2 ⟨hIU, hIR⟩).congr_set_ae (axial_ae_eq_union_st hR hL)
  · rw [setIntegral_congr_set (axial_ae_eq_union_st hR hL),
      setIntegral_union hd2 (measurableSet_capSetSt _ _ _) hIU hIR,
      setIntegral_union hd1 measurableSet_Ioo hIL hIB]
    have b1 := arc_trace_bound_st hR (capGeomSt_left hR hL) hTLp hTLm
    have b2 := bulk_trace_bound_st hR hL u
    have b3 := arc_trace_bound_st hR (capGeomSt_right hR hL) hTRp hTRm
    have hsum : traceConstSt R * (massP u + dirichletP u)
        = 2 * R * arcConstSt R * (massP u + dirichletP u)
          + traceConstBso R * (massP u + dirichletP u)
          + 2 * R * arcConstSt R * (massP u + dirichletP u) := by
      rw [traceConstSt]; ring
    rw [hsum]
    exact add_le_add (add_le_add b1 b2) b3

/-- **The trace inequality for the planar stadium**, granted the radial absolute continuity
`RadialACL` on the two hemispherical caps. -/
theorem traceIneqOne_hemisphere (hR : 0 < R) (hL : 2 * R < L)
    (hrad : ∀ u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R), RadialACL L R u) :
    TraceIneqOne (Cap.hemisphere 1) (Cap.hemisphere 1) L R where
  aesm_trPlus u := (trace_pieces_st hR hL (hrad u)).1
  aesm_trMinus u := (trace_pieces_st hR hL (hrad u)).2.1
  integrable u := (trace_pieces_st hR hL (hrad u)).2.2.1
  bound := ⟨traceConstSt R, fun u => by
    have h := (trace_pieces_st hR hL (hrad u)).2.2.2
    rwa [add_comm (dirichletP u) (massP u)]⟩

/-- **The explicit `R`-dependence of the constant.**  The trace inequality holds with the
constant `traceConstSt R ≤ 34/R + 16 R`. -/
theorem traceIneqOne_hemisphere_const (hR : 0 < R) (hL : 2 * R < L)
    (hrad : ∀ u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R), RadialACL L R u) :
    ∃ C : ℝ, C ≤ 34 / R + 16 * R ∧
      ∀ u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R),
        (∫ x in Ioo (-L / 2) (L / 2), areaElement (Cap.hemisphere 1) (Cap.hemisphere 1) L R x
            * (trPlus u x ^ 2 + trMinus u x ^ 2)) ≤ C * (massP u + dirichletP u) :=
  ⟨traceConstSt R, traceConstSt_le hR, fun u => (trace_pieces_st hR hL (hrad u)).2.2.2⟩

end Stadium

end RobinCaps.ThinDomain

end
