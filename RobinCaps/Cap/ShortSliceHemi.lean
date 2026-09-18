import RobinCaps.Cap.EntranceL2HemiGen
import RobinCaps.ThinDomain.Restrict
import RobinCaps.Cap.TraceDataHemi

/-!
# The transverse short-slice bound for the hemispherical cap (general transverse dimension)

This file discharges the hypothesis `RobinCaps.Cap.TransverseShortSliceBound_elg` of
`RobinCaps/Cap/EntranceL2HemiGen.lean`, completing the general-`m` entrance-trace bound for the
hemispherical cap `capEntranceL2_hemi_elg` unconditionally.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Transverse

noncomputable section

variable {m : ℕ}

/-! ## 1. General-dimension transverse ACL on the cap body

`RobinCaps.Cap.SliceAC` establishes the *axial* ACL property on a general `Cap m` body by
restricting to the sub-cylinders `Ω_c = (-K,c) ×ˢ B(0,θ c) ⊆ C.body` and running
`RobinCaps.ThinDomain.sliceACL_axial` there.  The *transverse* analogue is not recorded anywhere
for `m ≥ 2` (only for `Cap 1`, via the one-dimensional identification `ept`, in
`RobinCaps.Cap.PoincareOne`/`RobinCaps.Cap.EntranceL2Hemi`).  We supply it here, running
`RobinCaps.ThinDomain.sliceACL_transverse` on the same sub-cylinders. -/

/-- The transverse slice statement on one sub-cylinder `(-K,c) × B(0, θ c)`: for a.e. axial
level `s < c`, the transverse slice `z ↦ u(s,z)` has weak gradient `z ↦ (∇_z u)(s,z)` on the
ball `B(0, θ c)`. -/
theorem sliceAC_transverse_sub_ssh (C : Cap m) (u : H1P C.body) {c : ℝ} (hc : c ∈ Ioo (-C.K) 0) :
    ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) c)),
      HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ c))
        (fun z => u.toFun (s, z)) (fun z => u.gz (s, z)) := by
  have hsub := prodSub_subset_body C hc
  have h := RobinCaps.ThinDomain.sliceACL_transverse (a := -C.K) (b := c)
    (B := ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ c)) (u.restrict hsub)
  simpa [RobinCaps.ThinDomain.SliceACLTransverse] using h

/-- **General-dimension transverse ACL on the cap body.**  For almost every axial level `σ` of
the cap body, the transverse slice `z ↦ u(σ,z)` has `z ↦ (∇_z u)(σ,z)` as a weak gradient on the
whole transverse section `B(0, θ σ)`.  Mirrors `RobinCaps.Cap.sliceAC_axial_cap`, using a
countable family of rational sub-cylinder parameters `c ↓ σ` together with the two generic
`RobinCaps.Sobolev.Weak.HasWeakGrad` "test function only sees its support" lemmas
(`setIntegral_mul_pderiv_eq_integral`, `setIntegral_comp_mul_eq_integral`) to transport the
identity from the smaller ball `B(0,θ c)` to the full target ball `B(0, θ σ)`. -/
theorem sliceAC_transverse_cap_ssh (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)),
      HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ))
        (fun z => u.toFun (σ, z)) (fun z => u.gz (σ, z)) := by
  have hfam : ∀ q : ℚ, ∀ᵐ σ ∂(volume : Measure ℝ),
      (q : ℝ) ∈ Ioo (-C.K) 0 → σ ∈ Ioo (-C.K) (q : ℝ) →
        HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ (q : ℝ)))
          (fun z => u.toFun (σ, z)) (fun z => u.gz (σ, z)) := by
    intro q
    by_cases hq : (q : ℝ) ∈ Ioo (-C.K) 0
    · have h := sliceAC_transverse_sub_ssh C u hq
      rw [ae_restrict_iff' measurableSet_Ioo] at h
      filter_upwards [h] with σ hσ _ hmem
      exact hσ hmem
    · filter_upwards with σ h1
      exact absurd h1 hq
  have hall := ae_all_iff.2 hfam
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hall] with σ hσ hσmem
  intro φ hφ hφc hφs i
  have hθ : 0 < C.θ σ := C.θ_pos σ hσmem
  by_cases hSemp : tsupport φ = (∅ : Set (EuclideanSpace ℝ (Fin m)))
  · have hφ0 : ∀ x, φ x = 0 := fun x => by
      have : x ∉ tsupport φ := by rw [hSemp]; exact Set.notMem_empty x
      exact image_eq_zero_of_notMem_tsupport this
    have hφd0 : ∀ x, fderiv ℝ φ x = 0 := fun x => by
      have hns' : x ∉ tsupport φ := by rw [hSemp]; exact Set.notMem_empty x
      exact Function.notMem_support.1 fun h => hns' (support_fderiv_subset ℝ h)
    simp [hφd0, hφ0]
  · have hSne : (tsupport φ).Nonempty := Set.nonempty_iff_ne_empty.2 hSemp
    obtain ⟨x₀, hx₀, hx₀max⟩ :=
      IsCompact.exists_isMaxOn hφc hSne continuous_norm.continuousOn
    set M : ℝ := ‖x₀‖ with hM
    have hMlt : M < C.θ σ := mem_ball_zero_iff.1 (hφs hx₀)
    have hMbound : ∀ x ∈ tsupport φ, ‖x‖ ≤ M := fun x hx => hx₀max hx
    obtain ⟨q, hqI, hqθ⟩ := exists_rat_theta_gt_el C hσmem hMlt
    have hqIoo : (q : ℝ) ∈ Ioo (-C.K) 0 := ⟨hσmem.1.trans hqI.1, hqI.2⟩
    have hkey := hσ q hqIoo ⟨hσmem.1, hqI.1⟩
    have hφq : tsupport φ ⊆ ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ (q : ℝ)) := fun x hx =>
      mem_ball_zero_iff.2 (lt_of_le_of_lt (hMbound x hx) hqθ)
    have h1 := hkey φ hφ hφc hφq i
    have hL1 : (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ (q : ℝ)),
        u.toFun (σ, x) * fderiv ℝ φ x (EuclideanSpace.single i 1))
        = ∫ x, u.toFun (σ, x) * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_mul_pderiv_eq_integral
        (u := fun x => u.toFun (σ, x)) i hφq
    have hL2 : (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ),
        u.toFun (σ, x) * fderiv ℝ φ x (EuclideanSpace.single i 1))
        = ∫ x, u.toFun (σ, x) * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_mul_pderiv_eq_integral
        (u := fun x => u.toFun (σ, x)) i hφs
    have hR1 : (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ (q : ℝ)),
        u.gz (σ, x) i * φ x) = ∫ x, u.gz (σ, x) i * φ x :=
      RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_comp_mul_eq_integral
        (g := fun x => u.gz (σ, x)) i hφq
    have hR2 : (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ),
        u.gz (σ, x) i * φ x) = ∫ x, u.gz (σ, x) i * φ x :=
      RobinCaps.Sobolev.Weak.HasWeakGrad.setIntegral_comp_mul_eq_integral
        (g := fun x => u.gz (σ, x)) i hφs
    rw [hL2, ← hL1, h1, hR1, ← hR2]

/-! ## 2. `MemLp` bookkeeping for the transverse slice

Almost every axial level `σ` gives a square-integrable transverse slice on `B(0, θ σ)`, both for
the globally strongly measurable representatives `repFun`/`repGz_el` of `RobinCaps.Cap.EntranceL2Hemi`
(so that measurability is automatic on *every* slice, not just a.e.) and, after transport along
the a.e. equalities `ae_ae_transverse_repFun_el`/`ae_ae_transverse_repGz_el`, for `u.toFun`/`u.gz`
themselves. -/

/-- General-dimension version of `RobinCaps.Cap.ae_transverse_integrableOn_el`, without the
one-dimensional `ept` identification. -/
theorem ae_transverse_integrableOn_ssh (C : Cap m) {f : CapSpace m → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      IntegrableOn (fun z => f (σ, z)) (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ)) volume := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hf
  filter_upwards [hf'.prod_right_ae] with σ hσ hσI
  refine (integrable_indicator_iff measurableSet_ball).1 ?_
  exact hσ.congr (Eventually.of_forall fun z => indicator_body_transverse_el C f hσI z)

/-- Almost every transverse slice of `repFun C u` is `L²` on `B(0, θ σ)`. -/
theorem ae_transverse_repFun_memLp_ssh (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      MemLp (fun z => repFun C u (σ, z)) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ))) := by
  have hf := ae_transverse_integrableOn_ssh C (integrable_indicator_repFun_sq_el C u)
  filter_upwards [hf] with σ hσ hσmem
  have hsq := hσ hσmem
  have hmeasu : StronglyMeasurable (fun z : EuclideanSpace ℝ (Fin m) => repFun C u (σ, z)) :=
    (stronglyMeasurable_repFun C u).comp_measurable measurable_prodMk_left
  exact (memLp_two_iff_integrable_sq hmeasu.aestronglyMeasurable).2 hsq

/-- Almost every transverse slice of `repGz_el C u` is `L²` on `B(0, θ σ)`. -/
theorem ae_transverse_repGz_memLp_ssh (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      MemLp (fun z => repGz_el C u (σ, z)) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ))) := by
  have hf := ae_transverse_integrableOn_ssh C (integrable_indicator_repGz_sq_el C u)
  filter_upwards [hf] with σ hσ hσmem
  have hsq := hσ hσmem
  have hmeasu : StronglyMeasurable (fun z : EuclideanSpace ℝ (Fin m) => repGz_el C u (σ, z)) :=
    (stronglyMeasurable_repGz_el C u).comp_measurable measurable_prodMk_left
  exact (memLp_two_iff_integrable_sq_norm hmeasu.aestronglyMeasurable).2 hsq

/-- Transport of `MemLp` for `repFun`/`repGz_el` to `u.toFun`/`u.gz` on almost every transverse
slice. -/
theorem ae_transverse_memLp_ssh (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)),
      MemLp (fun z => u.toFun (σ, z)) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ))) ∧
      MemLp (fun z => u.gz (σ, z)) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ))) := by
  have h1 := ae_ae_transverse_repFun_el C u
  have h2 := ae_ae_transverse_repGz_el C u
  have h3 := ae_transverse_repFun_memLp_ssh C u
  have h4 := ae_transverse_repGz_memLp_ssh C u
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [h1, h2, h3, h4] with σ hσ1 hσ2 hσ3 hσ4 hσmem
  have heq1 : (fun z => u.toFun (σ, z)) =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ))]
      (fun z => repFun C u (σ, z)) := by
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hσ1] with z hz hzmem
    exact (hz ⟨hσmem.1, hσmem.2, mem_ball_zero_iff.1 hzmem⟩).symm
  have heq2 : (fun z => u.gz (σ, z)) =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ))]
      (fun z => repGz_el C u (σ, z)) := by
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hσ2] with z hz hzmem
    exact (hz ⟨hσmem.1, hσmem.2, mem_ball_zero_iff.1 hzmem⟩).symm
  exact ⟨(memLp_congr_ae heq1).2 (hσ3 hσmem), (memLp_congr_ae heq2).2 (hσ4 hσmem)⟩

/-! ## 3. The radial ACL package on almost every axial level -/

set_option maxHeartbeats 1000000 in
/-- **Radial ACL of the transverse slice, on almost every axial level.**  Combines the
transverse ACL of Part 1 with the `MemLp` bookkeeping of Part 2 through
`RobinCaps.Sobolev.Weak.radialSlice_ae_of_hasWeakGrad`: for almost every axial level `σ` and
almost every direction `w` of the unit sphere, the ray function `r ↦ u(σ, r w)` is a
one-dimensional Sobolev function on every `(ε, θ σ)`, with weak derivative the radial component
of `u.gz(σ,·)`. -/
theorem ae_transverse_radialSlice_ssh (C : Cap m) (hm : 1 ≤ m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)),
      ∀ᵐ w ∂(sphereMeasure m), ∀ ε ∈ Ioo (0 : ℝ) (C.θ σ),
        HasWeakDeriv ε (C.θ σ)
          (fun r => u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m))))
          (fun r => inner ℝ (u.gz (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
            EuclideanSpace ℝ (Fin m))) := by
  have h1 := sliceAC_transverse_cap_ssh C u
  have h2 := ae_transverse_memLp_ssh C u
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioo] with σ hσ1 hσ2 hσmem
  have hθ : 0 < C.θ σ := C.θ_pos σ hσmem
  have hres := radialSlice_ae_of_hasWeakGrad hm hθ hσ2.1 hσ2.2 hσ1
  exact hres

/-! ## 4. The bundled transverse `Weak.H1` element, on almost every axial level -/

/-- **The transverse slice bundled as an element of `Weak.H1`.**  On almost every axial level
`σ`, Parts 1–2 supply exactly the three data (`HasWeakGrad`, and the two `MemLp` facts) needed to
bundle the transverse slice `z ↦ u(σ,z)` as an element of `RobinCaps.Sobolev.Weak.H1 (B(0,θσ))`. -/
theorem ae_transverse_H1_ssh (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)), ∃ v : Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ σ)),
      v.toFun = (fun z => u.toFun (σ, z)) ∧ v.grad = (fun z => u.gz (σ, z)) := by
  have h1 := sliceAC_transverse_cap_ssh C u
  have h2 := ae_transverse_memLp_ssh C u
  filter_upwards [h1, h2] with σ hσ1 hσ2
  exact ⟨⟨_, _, hσ2.1, hσ2.2, hσ1⟩, rfl, rfl⟩

/-! ## 5. A generic one-dimensional interior FTC / averaged Cauchy–Schwarz bound

These two lemmas are purely about `RobinCaps.Sobolev.H1 ℓ` (the concrete AC one-dimensional
Sobolev model of `RobinCaps/Sobolev/Interval.lean`) and do not mention caps at all. -/

/-- **Interior fundamental theorem of calculus.** For any two points `x, y ∈ [0,ℓ]` of an
element of `RobinCaps.Sobolev.H1 ℓ`, `f(x) - f(y) = ∫_y^x f'`. -/
theorem sub_eq_integral_ssh {ℓ : ℝ} (W : RobinCaps.Sobolev.H1 ℓ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) ℓ) (hy : y ∈ Icc (0 : ℝ) ℓ) :
    W.toFun x - W.toFun y = ∫ t in y..x, deriv W.toFun t := by
  have h0le : (0 : ℝ) ≤ ℓ := hx.1.trans hx.2
  have h0x : IntervalIntegrable (deriv W.toFun) volume 0 x :=
    W.deriv_int.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le h0le]; exact Icc_subset_Icc le_rfl hx.2)
  have h0y : IntervalIntegrable (deriv W.toFun) volume 0 y :=
    W.deriv_int.mono_set (by rw [uIcc_of_le hy.1, uIcc_of_le h0le]; exact Icc_subset_Icc le_rfl hy.2)
  have hyx : IntervalIntegrable (deriv W.toFun) volume y x :=
    W.deriv_int.mono_set (uIcc_subset_Icc (by rw [min_eq_left h0le, max_eq_right h0le]; exact hy)
      (by rw [min_eq_left h0le, max_eq_right h0le]; exact hx))
  have hsum : (∫ t in (0:ℝ)..y, deriv W.toFun t) + ∫ t in y..x, deriv W.toFun t
      = ∫ t in (0:ℝ)..x, deriv W.toFun t :=
    intervalIntegral.integral_add_adjacent_intervals h0y hyx
  have hxeq := W.ftc x hx
  have hyeq := W.ftc y hy
  linarith [hsum, hxeq, hyeq]

/-- **Interior Cauchy–Schwarz bound, crude version.**  For `x, y ∈ [0,ℓ]`,
`(f(x)-f(y))² ≤ ℓ · dirichlet ℓ f`. -/
theorem sq_sub_le_dirichlet_ssh {ℓ : ℝ} (W : RobinCaps.Sobolev.H1 ℓ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) ℓ) (hy : y ∈ Icc (0 : ℝ) ℓ) :
    (W.toFun x - W.toFun y) ^ 2 ≤ ℓ * RobinCaps.Sobolev.dirichlet ℓ W := by
  have h0le : (0 : ℝ) ≤ ℓ := hx.1.trans hx.2
  rw [sub_eq_integral_ssh W hx hy]
  have hg : IntegrableOn (deriv W.toFun) (Ioo (0:ℝ) ℓ) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le h0le).1 W.deriv_int
  have hg2 : IntegrableOn (fun t => deriv W.toFun t ^ 2) (Ioo (0:ℝ) ℓ) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le h0le).1 W.deriv_sq_int
  have hcs := sq_intervalIntegral_sub_le_el hy hx hg hg2
  rw [sub_zero] at hcs
  rwa [RobinCaps.Sobolev.dirichlet,
    RobinCaps.Sobolev.intervalIntegral_eq_setIntegral_Ioo h0le]

/-- **The averaged pointwise bound.**  For a reference length `c ∈ (0,ℓ]`, every point
`x ∈ [0,ℓ]` of an element of `RobinCaps.Sobolev.H1 ℓ` satisfies
`f(x)² ≤ (2/c) ∫₀ᶜ f(x₀)² dx₀ + 2ℓ · dirichlet ℓ f`. -/
theorem interior_avg_sq_le_ssh {ℓ : ℝ} (W : RobinCaps.Sobolev.H1 ℓ) {c : ℝ} (hc : 0 < c)
    (hcℓ : c ≤ ℓ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ℓ) :
    W.toFun x ^ 2 ≤ (2 / c) * (∫ x₀ in Ioo (0 : ℝ) c, W.toFun x₀ ^ 2)
      + 2 * ℓ * RobinCaps.Sobolev.dirichlet ℓ W := by
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hc hcℓ
  have hDnn : 0 ≤ RobinCaps.Sobolev.dirichlet ℓ W := RobinCaps.Sobolev.dirichlet_nonneg ℓ W hℓ0.le
  have hptw : ∀ x₀ ∈ Ioo (0 : ℝ) c, W.toFun x ^ 2
      ≤ 2 * W.toFun x₀ ^ 2 + 2 * ℓ * RobinCaps.Sobolev.dirichlet ℓ W := by
    intro x₀ hx₀
    have hx₀mem : x₀ ∈ Icc (0 : ℝ) ℓ := ⟨hx₀.1.le, hx₀.2.le.trans hcℓ⟩
    have h := sq_sub_le_dirichlet_ssh W hx hx₀mem
    nlinarith [h, sq_nonneg (W.toFun x - 2 * W.toFun x₀)]
  have hWcont : ContinuousOn W.toFun (Icc (0:ℝ) ℓ) := by
    have h := W.ac.continuousOn; rwa [uIcc_of_le hℓ0.le] at h
  have hWcont' : ContinuousOn (fun x₀ => W.toFun x₀ ^ 2) (Icc (0:ℝ) c) :=
    (hWcont.mono (Icc_subset_Icc le_rfl hcℓ)).pow 2
  have hWint : IntegrableOn (fun x₀ => W.toFun x₀ ^ 2) (Ioo (0:ℝ) c) volume :=
    (hWcont'.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hconstint : IntegrableOn (fun _ : ℝ => W.toFun x ^ 2) (Ioo (0:ℝ) c) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hmajint : IntegrableOn
      (fun x₀ => 2 * W.toFun x₀ ^ 2 + 2 * ℓ * RobinCaps.Sobolev.dirichlet ℓ W)
      (Ioo (0:ℝ) c) volume := (hWint.const_mul 2).add (integrableOn_const measure_Ioo_lt_top.ne)
  have hvol : (volume.real (Ioo (0:ℝ) c)) = c := by
    rw [Real.volume_real_Ioo_of_le hc.le]; ring
  have hmono := setIntegral_mono_on hconstint hmajint measurableSet_Ioo
    (fun x₀ hx₀ => hptw x₀ hx₀)
  rw [setIntegral_const, hvol, smul_eq_mul,
    integral_add (hWint.const_mul 2) (integrableOn_const measure_Ioo_lt_top.ne),
    integral_const_mul, setIntegral_const, hvol, smul_eq_mul] at hmono
  have hfin : c * W.toFun x ^ 2 ≤ 2 * (∫ x₀ in Ioo (0:ℝ) c, W.toFun x₀ ^ 2)
      + 2 * ℓ * RobinCaps.Sobolev.dirichlet ℓ W * c := by nlinarith [hmono]
  rw [← sub_nonneg]
  have hkey : (2 / c) * (∫ x₀ in Ioo (0 : ℝ) c, W.toFun x₀ ^ 2)
      + 2 * ℓ * RobinCaps.Sobolev.dirichlet ℓ W - W.toFun x ^ 2
      = (1 / c) * (2 * (∫ x₀ in Ioo (0:ℝ) c, W.toFun x₀ ^ 2)
          + 2 * ℓ * RobinCaps.Sobolev.dirichlet ℓ W * c - c * W.toFun x ^ 2) := by
    field_simp
  rw [hkey]
  exact mul_nonneg (by positivity) (by linarith [hfin])

/-! ## 6. The uniform (direction- and level-independent) weight-integral bound -/

/-- **The weight integral along a ray is uniformly bounded**, independently of the ray length
`ρ ≤ 1` and of the direction. -/
theorem integral_wt_ray_le_ssh {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {dv : EuclideanSpace ℝ (Fin m)} (hω : ‖dv‖ = 1) :
    (∫ r in Ioo (0 : ℝ) ρ, wt_elg m (r • dv)) ≤ 2 * Real.pi := by
  have hmaj : ∀ r ∈ Ioo (0 : ℝ) ρ, wt_elg m (r • dv) ≤ 2 * arcDen_el r := by
    intro r hr
    have hrnorm : ‖r • dv‖ = r := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr.1]
    have := wt_le_elg m (r • dv)
    rwa [hrnorm] at this
  have hsub : Ioo (0 : ℝ) ρ ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo (by norm_num) hρ1
  have hI : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo (-1 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1:ℝ) ≤ 1)).1
      (intervalIntegrable_arcDen_el.const_mul 2)
  have hImaj : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo (0 : ℝ) ρ) volume := hI.mono_set hsub
  have hImeas : AEStronglyMeasurable (wt_elg m ∘ fun r : ℝ => r • dv)
      (volume.restrict (Ioo (0 : ℝ) ρ)) :=
    ((measurable_wt_elg m).comp (measurable_id.smul_const dv)).aestronglyMeasurable
  have hIray : IntegrableOn (fun r => wt_elg m (r • dv)) (Ioo (0 : ℝ) ρ) volume := by
    refine Integrable.mono' hImaj hImeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (wt_nonneg_elg m (r • dv))]
    exact hmaj r hr
  have hmono : (∫ r in Ioo (0 : ℝ) ρ, wt_elg m (r • dv))
      ≤ ∫ r in Ioo (0 : ℝ) ρ, 2 * arcDen_el r :=
    setIntegral_mono_on hIray hImaj measurableSet_Ioo hmaj
  have hext : (∫ r in Ioo (0 : ℝ) ρ, 2 * arcDen_el r) ≤ ∫ r in Ioo (-1 : ℝ) 1, 2 * arcDen_el r :=
    setIntegral_mono_set hI (Eventually.of_forall fun r => by
      simp only [Pi.zero_apply]; have := arcDen_nonneg_el r; linarith)
      (HasSubset.Subset.eventuallyLE hsub)
  have hval : (∫ r in Ioo (-1 : ℝ) 1, 2 * arcDen_el r) = 2 * Real.pi := by
    rw [integral_const_mul,
      ← RobinCaps.Sobolev.intervalIntegral_eq_setIntegral_Ioo (by norm_num : (-1:ℝ) ≤ 1),
      integral_arcDen_el]
  linarith [hmono, hext, hval.le, hval.ge]

/-- **The weight along a ray is integrable** on any sub-interval `(a,ρ)` with `ρ ≤ 1`. -/
theorem integrableOn_wt_ray_ssh {a ρ : ℝ} (ha : 0 ≤ a) (hρ1 : ρ ≤ 1)
    {dv : EuclideanSpace ℝ (Fin m)} (hω : ‖dv‖ = 1) :
    IntegrableOn (fun r => wt_elg m (r • dv)) (Ioo a ρ) volume := by
  rcases le_or_gt ρ a with hρa | hρa
  · rw [Ioo_eq_empty (by linarith)]; exact integrableOn_empty
  · have hmaj : ∀ r ∈ Ioo a ρ, wt_elg m (r • dv) ≤ 2 * arcDen_el r := by
      intro r hr
      have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
      have hrnorm : ‖r • dv‖ = r := by
        rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
      have := wt_le_elg m (r • dv)
      rwa [hrnorm] at this
    have hsub : Ioo a ρ ⊆ Ioo (-1 : ℝ) 1 := by
      refine Ioo_subset_Ioo (by linarith) hρ1
    have hI : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo (-1 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1:ℝ) ≤ 1)).1
        (intervalIntegrable_arcDen_el.const_mul 2)
    have hImaj : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo a ρ) volume := hI.mono_set hsub
    have hImeas : AEStronglyMeasurable (wt_elg m ∘ fun r : ℝ => r • dv)
        (volume.restrict (Ioo a ρ)) :=
      ((measurable_wt_elg m).comp (measurable_id.smul_const dv)).aestronglyMeasurable
    refine Integrable.mono' hImaj hImeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (wt_nonneg_elg m (r • dv))]
    exact hmaj r hr

/-- The same bound, on a sub-interval `(a, ρ) ⊆ (0, ρ)`. -/
theorem integral_wt_ray_sub_le_ssh {a ρ : ℝ} (ha : 0 ≤ a) (hρ1 : ρ ≤ 1)
    {dv : EuclideanSpace ℝ (Fin m)} (hω : ‖dv‖ = 1) :
    (∫ r in Ioo a ρ, wt_elg m (r • dv)) ≤ 2 * Real.pi := by
  rcases le_or_gt ρ 0 with hρ0 | hρ0
  · rw [Ioo_eq_empty (by linarith)]
    simp [Real.pi_pos.le]
  · have hsub : Ioo a ρ ⊆ Ioo (0 : ℝ) ρ := Ioo_subset_Ioo ha le_rfl
    have hmaj : ∀ r ∈ Ioo (0 : ℝ) ρ, wt_elg m (r • dv) ≤ 2 * arcDen_el r := by
      intro r hr
      have hrnorm : ‖r • dv‖ = r := by
        rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr.1]
      have := wt_le_elg m (r • dv)
      rwa [hrnorm] at this
    have hsub1 : Ioo (0 : ℝ) ρ ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo (by norm_num) hρ1
    have hI : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo (-1 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1:ℝ) ≤ 1)).1
        (intervalIntegrable_arcDen_el.const_mul 2)
    have hImaj : IntegrableOn (fun y => 2 * arcDen_el y) (Ioo (0 : ℝ) ρ) volume := hI.mono_set hsub1
    have hImeas : AEStronglyMeasurable (wt_elg m ∘ fun r : ℝ => r • dv)
        (volume.restrict (Ioo (0:ℝ) ρ)) :=
      ((measurable_wt_elg m).comp (measurable_id.smul_const dv)).aestronglyMeasurable
    have hIray0 : IntegrableOn (fun r => wt_elg m (r • dv)) (Ioo (0:ℝ) ρ) volume := by
      refine Integrable.mono' hImaj hImeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (wt_nonneg_elg m (r • dv))]
      exact hmaj r hr
    have hmono : (∫ r in Ioo a ρ, wt_elg m (r • dv)) ≤ ∫ r in Ioo (0 : ℝ) ρ, wt_elg m (r • dv) := by
      refine setIntegral_mono_set hIray0 ?_ (HasSubset.Subset.eventuallyLE hsub)
      exact Eventually.of_forall fun r => by
        simp only [Pi.zero_apply]; exact wt_nonneg_elg m (r • dv)
    have := integral_wt_ray_le_ssh (m := m) hρ0 hρ1 hω
    linarith [hmono, this]

/-! ## 7. A generic "pointwise bound implies weighted-integral bound" helper -/

/-- If `f x ^ 2 ≤ M` for every `x` in `Icc 0 ℓ` and `wt ≥ 0` is integrable there, then the
`wt`-weighted integral of `f²` is bounded by `M` times the integral of `wt`. -/
theorem integral_weighted_le_of_forall_ssh {ℓ : ℝ} {f wt : ℝ → ℝ} {M : ℝ}
    (hwt_nonneg : ∀ x, 0 ≤ wt x) (hwt_int : IntegrableOn wt (Ioo (0 : ℝ) ℓ) volume)
    (hf_meas : AEStronglyMeasurable f (volume.restrict (Ioo (0 : ℝ) ℓ)))
    (hbound : ∀ x ∈ Icc (0 : ℝ) ℓ, f x ^ 2 ≤ M) (hM0 : 0 ≤ M) :
    (∫ x in Ioo (0 : ℝ) ℓ, wt x * f x ^ 2) ≤ M * ∫ x in Ioo (0 : ℝ) ℓ, wt x := by
  have hmaj : IntegrableOn (fun x => wt x * M) (Ioo (0:ℝ) ℓ) volume := hwt_int.mul_const M
  have hfint : IntegrableOn (fun x => wt x * f x ^ 2) (Ioo (0:ℝ) ℓ) volume := by
    refine Integrable.mono' hmaj (hwt_int.aestronglyMeasurable.mul (hf_meas.pow 2)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have h1 : 0 ≤ wt x * f x ^ 2 := mul_nonneg (hwt_nonneg x) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact mul_le_mul_of_nonneg_left (hbound x (Ioo_subset_Icc_self hx)) (hwt_nonneg x)
  have hmono := setIntegral_mono_on hfint hmaj measurableSet_Ioo
    (fun x hx => mul_le_mul_of_nonneg_left (hbound x (Ioo_subset_Icc_self hx)) (hwt_nonneg x))
  rw [integral_mul_const] at hmono
  linarith [hmono]

/-! ## 8. The per-direction ray bound -/

set_option maxHeartbeats 1000000 in
/-- **The per-direction ray bound.**  On almost every axial level `σ` whose transverse radius
`ρ = θ σ` exceeds `rad_el` (in particular `ρ > 1/2`), for almost every direction `w`, the
weighted integral of `u(σ,·)²` along the ray, from `1/4` to `ρ`, is controlled by (a constant
times) the mass of the ray on the fixed reference segment `(1/4,1/2)` and the "energy" of the
ray on the whole segment `(1/4,ρ)`. -/
theorem ae_ray_bound_ssh (C : Cap m) (hm : 1 ≤ m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)), rad_el < C.θ σ →
      ∀ᵐ w ∂(sphereMeasure m),
        (∫ r in Ioo ((1:ℝ)/4) (C.θ σ),
            wt_elg m (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m)))
            * u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m))) ^ 2)
          ≤ (8 * (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ),
                u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
                  EuclideanSpace ℝ (Fin m))) ^ 2)
              + 2 * (∫ r in Ioo ((1:ℝ)/4) (C.θ σ),
                inner ℝ (u.gz (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
                  EuclideanSpace ℝ (Fin m))))
                  ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
                    EuclideanSpace ℝ (Fin m)) ^ 2)) * (2 * Real.pi) := by
  have h1 := ae_transverse_H1_ssh C u
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with σ hex hσmem hrad
  obtain ⟨v, hv1, hv2⟩ := hex
  have hθ : 0 < C.θ σ := C.θ_pos σ hσmem
  have hθ1 : C.θ σ ≤ 1 := C.θ_le_one σ hσmem
  have hq4 : (1:ℝ)/4 < rad_el := by nlinarith [rad_sq_el, rad_pos_el]
  have hh2 : (1:ℝ)/2 < rad_el := by nlinarith [rad_sq_el, rad_pos_el]
  have hquarter : (1:ℝ)/4 ∈ Ioo (0:ℝ) (C.θ σ) := ⟨by norm_num, lt_trans hq4 hrad⟩
  have hhalf_lt : (1:ℝ)/2 < C.θ σ := lt_trans hh2 hrad
  have hlen : (0:ℝ) < C.θ σ - 1/4 := by linarith [hquarter.2]
  have hradlt : rad_el < 1 := rad_lt_one_el
  filter_upwards [radialSlice_h1 hm hθ v] with w hw
  obtain ⟨W, hW1, hW2⟩ := hw (1/4) hquarter
  -- Step 1: the pointwise-for-every-x bound from the interior averaged Cauchy–Schwarz estimate.
  have hcℓ : (1:ℝ)/4 ≤ C.θ σ - 1/4 := by linarith [hhalf_lt]
  have hbound : ∀ x ∈ Icc (0:ℝ) (C.θ σ - 1/4), W.toFun x ^ 2
      ≤ 8 * (∫ x₀ in Ioo (0:ℝ) (1/4), W.toFun x₀ ^ 2)
        + 2 * (C.θ σ - 1/4) * RobinCaps.Sobolev.dirichlet (C.θ σ - 1/4) W := by
    intro x hx
    have := interior_avg_sq_le_ssh W (c := (1:ℝ)/4) (by norm_num) hcℓ hx
    norm_num at this
    convert this using 2
  set ref : ℝ := ∫ x₀ in Ioo (0:ℝ) (1/4), W.toFun x₀ ^ 2 with href
  set dir : ℝ := RobinCaps.Sobolev.dirichlet (C.θ σ - 1/4) W with hdirdef
  have hDnn : 0 ≤ dir := RobinCaps.Sobolev.dirichlet_nonneg (C.θ σ - 1/4) W hlen.le
  have hrefnn : 0 ≤ ref := by
    rw [href]; exact setIntegral_nonneg measurableSet_Ioo fun x _ => sq_nonneg _
  have hcrude : 2 * (C.θ σ - 1/4) * dir ≤ 2 * dir := by nlinarith [hθ1, hDnn]
  have hbound2 : ∀ x ∈ Icc (0:ℝ) (C.θ σ - 1/4), W.toFun x ^ 2 ≤ 8 * ref + 2 * dir := by
    intro x hx; have := hbound x hx; linarith
  set M : ℝ := 8 * ref + 2 * dir with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  -- Step 2: the weighted-integral bound on the whole segment `(0, ρ - 1/4)`.
  have hwn : ‖((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))‖ = 1 :=
    mem_sphere_zero_iff_norm.1 w.2
  have hwt_shift_int : IntegrableOn
      (fun x => wt_elg m ((x + 1/4) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)))) (Ioo (0:ℝ) (C.θ σ - 1/4)) volume := by
    have hbase := integrableOn_wt_ray_ssh (m := m) (a := (1:ℝ)/4) (ρ := C.θ σ)
      (by norm_num) hθ1 hwn
    have htr := integrableOn_translate (c := (1:ℝ)/4) hbase
    rwa [preimage_addRight_Ioo,
      show (1:ℝ)/4 - 1/4 = 0 by ring, show C.θ σ - 1/4 = C.θ σ - 1/4 by ring] at htr
  have hWmeas : AEStronglyMeasurable W.toFun (volume.restrict (Ioo (0:ℝ) (C.θ σ - 1/4))) := by
    have hc : ContinuousOn W.toFun (Icc (0:ℝ) (C.θ σ - 1/4)) := by
      have h := W.ac.continuousOn; rwa [uIcc_of_le hlen.le] at h
    exact (hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hkey := integral_weighted_le_of_forall_ssh (ℓ := C.θ σ - 1/4)
    (f := W.toFun) (wt := fun x => wt_elg m ((x + 1/4) •
      ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))))
    (M := M) (fun x => wt_nonneg_elg m _) hwt_shift_int hWmeas hbound2 hM0
  -- Step 3: translate the weighted integral back to the original ray data.
  have htransL : (∫ x in Ioo (0:ℝ) (C.θ σ - 1/4),
      wt_elg m ((x + 1/4) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))) * W.toFun x ^ 2)
      = ∫ r in Ioo ((1:ℝ)/4) (C.θ σ), wt_elg m (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) * u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) ^ 2 := by
    have hcongr : (fun x => wt_elg m ((x + 1/4) •
        ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) * W.toFun x ^ 2)
        =ᵐ[volume.restrict (Ioo (0:ℝ) (C.θ σ - 1/4))]
        (fun x => wt_elg m ((x + 1/4) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) * u.toFun (σ, (x + 1/4) •
          ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) ^ 2) := by
      filter_upwards [hW1] with x hx
      rw [hx, hv1]
    rw [integral_congr_ae hcongr]
    have h2 := setIntegral_translate (1/4) (fun r => wt_elg m (r •
      ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) *
        u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) ^ 2)
      (Ioo ((1:ℝ)/4) (C.θ σ))
    rwa [preimage_addRight_Ioo, show (1:ℝ)/4 - 1/4 = 0 by ring] at h2
  -- Step 4: translate the reference mass and the Dirichlet energy.
  have href2 : ref = ∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ),
      u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))) ^ 2 := by
    rw [href]
    have hsub14 : Ioo (0:ℝ) (1/4) ⊆ Ioo (0:ℝ) (C.θ σ - 1/4) := Ioo_subset_Ioo_right hcℓ
    have hW1' : W.toFun =ᵐ[volume.restrict (Ioo (0:ℝ) (1/4))]
        (fun s => v.toFun ((s + 1/4) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))) :=
      ae_mono (Measure.restrict_mono hsub14 le_rfl) hW1
    have hcongr : (fun x₀ => W.toFun x₀ ^ 2) =ᵐ[volume.restrict (Ioo (0:ℝ) (1/4))]
        (fun x₀ => u.toFun (σ, (x₀ + 1/4) •
          ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) ^ 2) := by
      filter_upwards [hW1'] with x hx
      rw [hx, hv1]
    rw [integral_congr_ae hcongr]
    have h2 := setIntegral_translate (1/4) (fun r => u.toFun (σ,
      r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) ^ 2)
      (Ioo ((1:ℝ)/4) (1/2 : ℝ))
    rwa [preimage_addRight_Ioo, show (1:ℝ)/4 - 1/4 = 0 by ring,
      show (1:ℝ)/2 - 1/4 = 1/4 by ring] at h2
  have hdir2 : dir = ∫ r in Ioo ((1:ℝ)/4) (C.θ σ),
      inner ℝ (u.gz (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m)) ^ 2 := by
    rw [hdirdef, RobinCaps.Sobolev.dirichlet,
      RobinCaps.Sobolev.intervalIntegral_eq_setIntegral_Ioo hlen.le]
    have hcongr : (fun x => deriv W.toFun x ^ 2) =ᵐ[volume.restrict (Ioo (0:ℝ) (C.θ σ - 1/4))]
        (fun x => inner ℝ (u.gz (σ, (x + 1/4) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)) ^ 2) := by
      filter_upwards [hW2] with x hx
      rw [hx, hv2]
    rw [integral_congr_ae hcongr]
    have h2 := setIntegral_translate (1/4) (fun r => inner ℝ (u.gz (σ,
      r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))))
        ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m)) ^ 2)
      (Ioo ((1:ℝ)/4) (C.θ σ))
    rwa [preimage_addRight_Ioo, show (1:ℝ)/4 - 1/4 = 0 by ring] at h2
  -- Step 5: assemble.
  have htransR : (∫ x in Ioo (0:ℝ) (C.θ σ - 1/4),
      wt_elg m ((x + 1/4) • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))))
      = ∫ r in Ioo ((1:ℝ)/4) (C.θ σ), wt_elg m (r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) := by
    have h2 := setIntegral_translate (1/4) (fun r => wt_elg m (r •
      ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))))
      (Ioo ((1:ℝ)/4) (C.θ σ))
    rwa [preimage_addRight_Ioo, show (1:ℝ)/4 - 1/4 = 0 by ring] at h2
  have hwtbound : (∫ r in Ioo ((1:ℝ)/4) (C.θ σ), wt_elg m (r •
      ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))))
      ≤ 2 * Real.pi := integral_wt_ray_sub_le_ssh (m := m) (by norm_num) hθ1 hwn
  rw [htransL, htransR] at hkey
  have hMval : M ≤ 8 * (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ),
      u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
        EuclideanSpace ℝ (Fin m))) ^ 2)
      + 2 * (∫ r in Ioo ((1:ℝ)/4) (C.θ σ),
        inner ℝ (u.gz (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m)) ^ 2) := by rw [hMdef, href2, hdir2]
  have hfin : (0:ℝ) ≤ ∫ r in Ioo ((1:ℝ)/4) (C.θ σ), wt_elg m (r •
      ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) := by
    refine setIntegral_nonneg measurableSet_Ioo fun r _ => wt_nonneg_elg m _
  calc (∫ r in Ioo ((1:ℝ)/4) (C.θ σ), wt_elg m (r •
        ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m)))
        * u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
          EuclideanSpace ℝ (Fin m))) ^ 2)
      ≤ M * ∫ r in Ioo ((1:ℝ)/4) (C.θ σ), wt_elg m (r •
          ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : EuclideanSpace ℝ (Fin m))) := hkey
    _ ≤ (8 * (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ),
            u.toFun (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m))) ^ 2)
          + 2 * (∫ r in Ioo ((1:ℝ)/4) (C.θ σ),
            inner ℝ (u.gz (σ, r • ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m)))) ((w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
              EuclideanSpace ℝ (Fin m)) ^ 2)) * (2 * Real.pi) :=
        mul_le_mul hMval hwtbound hfin (by positivity)

/-! ## 9. Integrability of the weighted square on a sub-ball, via a pointwise bound -/

/-- **The weight is bounded on any ball strictly inside the unit ball**, by a constant depending
only on the ball's radius. -/
theorem wt_elg_le_of_mem_ball_ssh {ρ : ℝ} (hρ1 : ρ < 1) {z : EuclideanSpace ℝ (Fin m)}
    (hz : ‖z‖ < ρ) : wt_elg m z ≤ 2 / Real.sqrt (1 - ρ ^ 2) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg z).trans hz.le
  have hzpos : 0 < 1 - ρ ^ 2 := by nlinarith
  rw [wt_elg]
  split
  · have hlt : ‖z‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg z]
    have h1 : 1 - ρ ^ 2 < 1 - ‖z‖ ^ 2 := by linarith
    have h2 : Real.sqrt (1 - ρ ^ 2) < Real.sqrt (1 - ‖z‖ ^ 2) := Real.sqrt_lt_sqrt hzpos.le h1
    exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hzpos) h2.le
  · positivity

/-- **The weighted square is integrable on any ball of radius `< 1`**, given `L²`-membership of
the underlying function. -/
theorem integrableOn_wt_mul_sq_ssh {ρ : ℝ} (hρ1 : ρ < 1) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ρ))) :
    IntegrableOn (fun z => wt_elg m z * f z ^ 2) (ball (0 : EuclideanSpace ℝ (Fin m)) ρ) volume := by
  have hfsq : IntegrableOn (fun z => f z ^ 2) (ball (0 : EuclideanSpace ℝ (Fin m)) ρ) volume :=
    hf.integrable_sq
  have hmeas : AEStronglyMeasurable (fun z => wt_elg m z * f z ^ 2)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ρ)) :=
    (measurable_wt_elg m).aestronglyMeasurable.mul hfsq.aestronglyMeasurable
  refine Integrable.mono' (hfsq.const_mul (2 / Real.sqrt (1 - ρ ^ 2))) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have h1 : 0 ≤ wt_elg m z * f z ^ 2 := mul_nonneg (wt_nonneg_elg m z) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact mul_le_mul_of_nonneg_right (wt_elg_le_of_mem_ball_ssh hρ1 (mem_ball_zero_iff.1 hz))
    (sq_nonneg _)

/-! ## 9b. A generic "unweight then re-extend" comparison for the radial power weight -/

/-- **Comparing an unweighted sub-range integral to the `r^{m-1}`-weighted integral on the whole
range.**  If `H ≥ 0` and `r^{m-1} H(r)` is integrable on `(0,ρ)`, then the plain (unweighted)
integral of `H` on any sub-range `(a,b) ⊆ (0,ρ)` with `a > 0` is bounded by `a^{-(m-1)}` times the
weighted integral on the whole range. -/
theorem interval_le_weighted_ssh (hm : 1 ≤ m) {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbρ : b ≤ ρ)
    {H : ℝ → ℝ} (hHnn : ∀ r, 0 ≤ H r)
    (hInt : IntegrableOn (fun r => r ^ (m-1) * H r) (Ioo (0:ℝ) ρ) volume) :
    (∫ r in Ioo a b, H r) ≤ (a⁻¹) ^ (m-1) * ∫ r in Ioo (0:ℝ) ρ, r ^ (m-1) * H r := by
  have hsub : Ioo a b ⊆ Ioo (0:ℝ) ρ := Ioo_subset_Ioo ha.le hbρ
  have hIntab : IntegrableOn (fun r => r ^ (m-1) * H r) (Ioo a b) volume := hInt.mono_set hsub
  have hbound : ∀ r ∈ Ioo a b, H r ≤ (a⁻¹) ^ (m-1) * (r ^ (m-1) * H r) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1.le
    have hle : a ≤ r := hr.1.le
    have hpow : a ^ (m-1) ≤ r ^ (m-1) := pow_le_pow_left₀ ha.le hle (m-1)
    have hstep : (1:ℝ) ≤ (a⁻¹) ^ (m-1) * r ^ (m-1) := by
      have h1 : (a⁻¹) ^ (m-1) * a ^ (m-1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ ha.ne', one_pow]
      nlinarith [mul_le_mul_of_nonneg_left hpow (pow_nonneg (inv_nonneg.2 ha.le) (m-1)), h1]
    calc H r = 1 * H r := (one_mul _).symm
      _ ≤ ((a⁻¹) ^ (m-1) * r ^ (m-1)) * H r := mul_le_mul_of_nonneg_right hstep (hHnn r)
      _ = (a⁻¹) ^ (m-1) * (r ^ (m-1) * H r) := by ring
  have hmeas : AEStronglyMeasurable H (volume.restrict (Ioo a b)) := by
    have heq : ∀ r ∈ Ioo a b, H r = (r ^ (m-1))⁻¹ * (r ^ (m-1) * H r) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le ha hr.1.le
      have : r ^ (m-1) ≠ 0 := pow_ne_zero _ hr0.ne'
      field_simp
    have hmeasInv : AEStronglyMeasurable (fun r : ℝ => (r ^ (m-1))⁻¹) (volume.restrict (Ioo a b)) :=
      ((measurable_id.pow_const (m-1)).inv).aestronglyMeasurable
    refine (hmeasInv.mul hIntab.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr using (heq r hr).symm
  have hmaj : IntegrableOn H (Ioo a b) volume := by
    refine Integrable.mono' (hIntab.const_mul ((a⁻¹) ^ (m-1))) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hHnn r)]
    exact hbound r hr
  have hmono : (∫ r in Ioo a b, H r)
      ≤ ∫ r in Ioo a b, (a⁻¹) ^ (m-1) * (r ^ (m-1) * H r) :=
    setIntegral_mono_on hmaj (hIntab.const_mul _) measurableSet_Ioo hbound
  rw [integral_const_mul] at hmono
  have hext : (∫ r in Ioo a b, r ^ (m-1) * H r) ≤ ∫ r in Ioo (0:ℝ) ρ, r ^ (m-1) * H r :=
    setIntegral_mono_set hInt (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      simp only [Pi.zero_apply]
      exact mul_nonneg (pow_nonneg hr.1.le _) (hHnn r))
      (HasSubset.Subset.eventuallyLE hsub)
  have h4nn : (0:ℝ) ≤ (a⁻¹) ^ (m-1) := by positivity
  calc (∫ r in Ioo a b, H r) ≤ (a⁻¹) ^ (m-1) * ∫ r in Ioo a b, r ^ (m-1) * H r := hmono
    _ ≤ (a⁻¹) ^ (m-1) * ∫ r in Ioo (0:ℝ) ρ, r ^ (m-1) * H r :=
        mul_le_mul_of_nonneg_left hext h4nn

/-- **The unweighted integrability of `H` on a sub-range bounded away from `0`**, extracted from
the domination argument of `interval_le_weighted_ssh`. -/
theorem integrableOn_of_weighted_ssh (hm : 1 ≤ m) {a b ρ : ℝ} (ha : 0 < a) (hbρ : b ≤ ρ)
    {H : ℝ → ℝ} (hHnn : ∀ r, 0 ≤ H r)
    (hInt : IntegrableOn (fun r => r ^ (m-1) * H r) (Ioo (0:ℝ) ρ) volume) :
    IntegrableOn H (Ioo a b) volume := by
  rcases le_or_gt a b with hab | hab
  · have hsub : Ioo a b ⊆ Ioo (0:ℝ) ρ := Ioo_subset_Ioo ha.le hbρ
    have hIntab : IntegrableOn (fun r => r ^ (m-1) * H r) (Ioo a b) volume := hInt.mono_set hsub
    have hbound : ∀ r ∈ Ioo a b, H r ≤ (a⁻¹) ^ (m-1) * (r ^ (m-1) * H r) := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le ha hr.1.le
      have hle : a ≤ r := hr.1.le
      have hpow : a ^ (m-1) ≤ r ^ (m-1) := pow_le_pow_left₀ ha.le hle (m-1)
      have hstep : (1:ℝ) ≤ (a⁻¹) ^ (m-1) * r ^ (m-1) := by
        have h1 : (a⁻¹) ^ (m-1) * a ^ (m-1) = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ ha.ne', one_pow]
        nlinarith [mul_le_mul_of_nonneg_left hpow (pow_nonneg (inv_nonneg.2 ha.le) (m-1)), h1]
      calc H r = 1 * H r := (one_mul _).symm
        _ ≤ ((a⁻¹) ^ (m-1) * r ^ (m-1)) * H r := mul_le_mul_of_nonneg_right hstep (hHnn r)
        _ = (a⁻¹) ^ (m-1) * (r ^ (m-1) * H r) := by ring
    have hmeas : AEStronglyMeasurable H (volume.restrict (Ioo a b)) := by
      have heq : ∀ r ∈ Ioo a b, H r = (r ^ (m-1))⁻¹ * (r ^ (m-1) * H r) := by
        intro r hr
        have hr0 : 0 < r := lt_of_lt_of_le ha hr.1.le
        have : r ^ (m-1) ≠ 0 := pow_ne_zero _ hr0.ne'
        field_simp
      have hmeasInv : AEStronglyMeasurable (fun r : ℝ => (r ^ (m-1))⁻¹) (volume.restrict (Ioo a b)) :=
        ((measurable_id.pow_const (m-1)).inv).aestronglyMeasurable
      refine (hmeasInv.mul hIntab.aestronglyMeasurable).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr using (heq r hr).symm
    refine Integrable.mono' (hIntab.const_mul ((a⁻¹) ^ (m-1))) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hHnn r)]
    exact hbound r hr
  · rw [Ioo_eq_empty (by linarith)]; exact integrableOn_empty

/-! ## 10. The per-level bound via polar coordinates -/

set_option maxHeartbeats 1000000 in
/-- **The per-level bound.**  For almost every axial level `σ` of the hemispherical cap body,
the weighted transverse integral over the whole ball `B(0, θ σ)` is controlled by a
dimension-dependent multiple of the mass and the Dirichlet energy of the transverse slice. -/
theorem ae_level_wt_bound_ssh (hm : 1 ≤ m) (u : H1P (hemisphere m).body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-(1:ℝ)) 0)),
      (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          wt_elg m z * u.toFun (σ, z) ^ 2)
        ≤ (16 * Real.pi * 4 ^ (m - 1)) *
          ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ), u.toFun (σ, z) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
                ‖u.gz (σ, z)‖ ^ 2) := by
  have hKm : (hemisphere m).K = 1 := hemi_K_elg m
  have h1 := ae_transverse_H1_ssh (hemisphere m) u
  have h2 := ae_ray_bound_ssh (hemisphere m) hm u
  have h3 := ae_restrict_of_ae (s := Ioo (-(1:ℝ)) 0) (ae_ae_transverse_repFun_el (hemisphere m) u)
  have h4 := ae_restrict_of_ae (s := Ioo (-(1:ℝ)) 0) (ae_ae_transverse_repGz_el (hemisphere m) u)
  rw [hKm] at h1 h2
  filter_upwards [h1, h2, h3, h4, ae_restrict_mem measurableSet_Ioo]
    with σ hex hray hrepF hrepG hσmem
  set ρ : ℝ := (hemisphere m).θ σ with hρdef
  obtain ⟨v, hv1, hv2⟩ := hex
  have hρ0 : 0 < ρ := (hemisphere m).θ_pos σ hσmem
  have hρ1 : ρ < 1 := by
    rw [hρdef, hemi_theta_elg m σ]
    have h1 : (0:ℝ) < σ + 1 := by linarith [hσmem.1]
    have h2 : σ + 1 < 1 := by linarith [hσmem.2]
    have h4 : 1 - (σ + 1) ^ 2 < 1 := by nlinarith
    have h5 : (0:ℝ) ≤ 1 - (σ + 1) ^ 2 := by nlinarith
    calc Real.sqrt (1 - (σ + 1) ^ 2) < Real.sqrt 1 := Real.sqrt_lt_sqrt h5 h4
      _ = 1 := Real.sqrt_one
  rcases le_or_gt ρ rad_el with hρle | hρgt
  · -- Trivial case: the weight vanishes identically on `B(0,ρ)`.
    have hzero : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) ρ, wt_elg m z * u.toFun (σ, z) ^ 2 = 0 := by
      intro z hz
      have hzn : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
      have : ¬ rad_el < ‖z‖ := by linarith
      rw [wt_elg, if_neg this, zero_mul]
    rw [setIntegral_congr_fun measurableSet_ball hzero, integral_zero]
    positivity
  · -- Main case: `ρ > rad_el`.
    have hq4 : (1:ℝ)/4 < rad_el := by nlinarith [rad_sq_el, rad_pos_el]
    have hu_memLp : MemLp (fun z => u.toFun (σ, z)) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ρ)) :=
      hv1 ▸ v.memL2
    have hg_memLp : MemLp (fun z => u.gz (σ, z)) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ρ)) :=
      hv2 ▸ v.grad_memL2
    set F : EuclideanSpace ℝ (Fin m) → ℝ := fun z => wt_elg m z * u.toFun (σ, z) ^ 2 with hFdef
    have hFint : IntegrableOn F (ball (0 : EuclideanSpace ℝ (Fin m)) ρ) volume :=
      integrableOn_wt_mul_sq_ssh hρ1 hu_memLp
    have hpolar : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, F z)
        = ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            (∫ r in Ioo (0 : ℝ) ρ, r ^ (m - 1) * F (r • (w : EuclideanSpace ℝ (Fin m))))
          ∂(sphereMeasure m) :=
      integral_ball_polar_symm hm hFint
    have houterInt := ae_integrableOn_weighted (R := ρ) hm hFint
    have hbnd := hray hρgt
    have hptw : ∀ᵐ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        (∫ r in Ioo (0 : ℝ) ρ, r ^ (m - 1) * F (r • (w : EuclideanSpace ℝ (Fin m))))
          ≤ (8 * (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ),
                u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
              + 2 * (∫ r in Ioo ((1:ℝ)/4) ρ,
                inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
                  (w : EuclideanSpace ℝ (Fin m)) ^ 2)) * (2 * Real.pi) := by
      filter_upwards [houterInt, hbnd] with w hwint hwbnd
      have hwn : ‖(w : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
      have hvanish : ∀ r : ℝ, 0 < r → r ≤ (1:ℝ)/4 →
          r ^ (m - 1) * F (r • (w : EuclideanSpace ℝ (Fin m))) = 0 := by
        intro r hr0 hr4
        have hrn : ‖r • (w : EuclideanSpace ℝ (Fin m))‖ = r := by
          rw [norm_smul, hwn, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
        have hnot : ¬ rad_el < ‖r • (w : EuclideanSpace ℝ (Fin m))‖ := by
          rw [hrn]; linarith
        rw [hFdef]
        show r ^ (m-1) * (wt_elg m (r • (w:EuclideanSpace ℝ (Fin m))) * u.toFun (σ, r • (w:EuclideanSpace ℝ (Fin m))) ^ 2) = 0
        rw [wt_elg, if_neg hnot, zero_mul, mul_zero]
      have hsplit : (∫ r in Ioo (0:ℝ) ρ, r ^ (m-1) * F (r • (w:EuclideanSpace ℝ (Fin m))))
          = ∫ r in Ioo ((1:ℝ)/4) ρ, r ^ (m-1) * F (r • (w:EuclideanSpace ℝ (Fin m))) := by
        refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo
          (Ioo_subset_Ioo (by norm_num) le_rfl) ?_
        rintro r ⟨hr1, hr2⟩
        have hr4 : r ≤ (1:ℝ)/4 := by
          by_contra hcon
          push_neg at hcon
          exact hr2 ⟨hcon, hr1.2⟩
        exact hvanish r hr1.1 hr4
      rw [hsplit]
      have hFnn : ∀ r : ℝ, 0 ≤ F (r • (w : EuclideanSpace ℝ (Fin m))) := fun r =>
        mul_nonneg (wt_nonneg_elg m _) (sq_nonneg _)
      have hle1 : ∀ r ∈ Ioo ((1:ℝ)/4) ρ, r ^ (m-1) ≤ 1 := by
        intro r hr
        refine pow_le_one₀ (by linarith [hr.1]) ?_
        linarith [hr.2, hρ1]
      have hge : ∀ r ∈ Ioo ((1:ℝ)/4) ρ, ((4:ℝ) ^ (m-1))⁻¹ ≤ r ^ (m-1) := by
        intro r hr
        have h1 : ((4:ℝ))⁻¹ ≤ r := by
          rw [show (4:ℝ)⁻¹ = 1/4 by norm_num]
          linarith [hr.1]
        have h2 : (0:ℝ) ≤ (4:ℝ)⁻¹ := by norm_num
        rw [← inv_pow]
        exact pow_le_pow_left₀ h2 h1 (m-1)
      have hwint' : IntegrableOn (fun r => r ^ (m-1) * F (r • (w:EuclideanSpace ℝ (Fin m))))
          (Ioo ((1:ℝ)/4) ρ) volume := hwint.mono_set (Ioo_subset_Ioo (by norm_num) le_rfl)
      have heq : ∀ r ∈ Ioo ((1:ℝ)/4) ρ,
          F (r • (w : EuclideanSpace ℝ (Fin m))) = (r ^ (m-1))⁻¹
            * (r ^ (m-1) * F (r • (w : EuclideanSpace ℝ (Fin m)))) := by
        intro r hr
        have hrne : r ≠ 0 := by intro h; rw [h] at hr; exact absurd hr.1 (by norm_num)
        have : r ^ (m-1) ≠ 0 := pow_ne_zero _ hrne
        field_simp
      have hmeasInv : AEStronglyMeasurable (fun r : ℝ => (r ^ (m-1))⁻¹)
          (volume.restrict (Ioo ((1:ℝ)/4) ρ)) :=
        ((measurable_id.pow_const (m-1)).inv).aestronglyMeasurable
      have hunwt_meas : AEStronglyMeasurable (fun r => F (r • (w : EuclideanSpace ℝ (Fin m))))
          (volume.restrict (Ioo ((1:ℝ)/4) ρ)) := by
        have hcongr : (fun r : ℝ => (r ^ (m-1))⁻¹ * (r ^ (m-1) * F (r • (w : EuclideanSpace ℝ (Fin m)))))
            =ᵐ[volume.restrict (Ioo ((1:ℝ)/4) ρ)] (fun r => F (r • (w : EuclideanSpace ℝ (Fin m)))) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr using (heq r hr).symm
        exact (hmeasInv.mul hwint'.aestronglyMeasurable).congr hcongr
      have hunwt : IntegrableOn (fun r => F (r • (w : EuclideanSpace ℝ (Fin m))))
          (Ioo ((1:ℝ)/4) ρ) volume := by
        refine Integrable.mono' (hwint'.const_mul ((4:ℝ) ^ (m-1))) hunwt_meas ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnn r)]
        calc F (r • (w : EuclideanSpace ℝ (Fin m)))
            = (r ^ (m-1))⁻¹ * (r ^ (m-1) * F (r • (w : EuclideanSpace ℝ (Fin m)))) := heq r hr
          _ ≤ (4:ℝ) ^ (m-1) * (r ^ (m-1) * F (r • (w : EuclideanSpace ℝ (Fin m)))) := by
              have hr0 : (0:ℝ) < r := by linarith [hr.1]
              have hrpos : 0 < r ^ (m-1) := by positivity
              have h4pos : (0:ℝ) < (4:ℝ) ^ (m-1) := by positivity
              have hstep : (1:ℝ) ≤ r ^ (m-1) * (4:ℝ) ^ (m-1) := by
                have := mul_le_mul_of_nonneg_right (hge r hr) h4pos.le
                rwa [inv_mul_cancel₀ h4pos.ne'] at this
              have hinvle : (r ^ (m-1))⁻¹ ≤ (4:ℝ) ^ (m-1) := by
                rw [inv_le_iff_one_le_mul₀ hrpos]
                linarith [hstep]
              exact mul_le_mul_of_nonneg_right hinvle (mul_nonneg hrpos.le (hFnn r))
      have hmono : (∫ r in Ioo ((1:ℝ)/4) ρ, r ^ (m-1) * F (r • (w:EuclideanSpace ℝ (Fin m))))
          ≤ ∫ r in Ioo ((1:ℝ)/4) ρ, F (r • (w:EuclideanSpace ℝ (Fin m))) :=
        setIntegral_mono_on hwint' hunwt measurableSet_Ioo
          (fun r hr => mul_le_of_le_one_left (hFnn r) (hle1 r hr))
      exact hmono.trans hwbnd
    -- Step 6: measurability of the reference-mass and energy functions of `w`, via `repFun`.
    have heqU : (fun z => u.toFun (σ, z)) =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ρ)]
        (fun z => repFun (hemisphere m) u (σ, z)) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
      filter_upwards [hrepF] with z hz hzmem
      exact (hz ⟨hσmem.1, hσmem.2, mem_ball_zero_iff.1 hzmem⟩).symm
    have heqG : (fun z => u.gz (σ, z)) =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ρ)]
        (fun z => repGz_el (hemisphere m) u (σ, z)) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
      filter_upwards [hrepG] with z hz hzmem
      exact (hz ⟨hσmem.1, hσmem.2, mem_ball_zero_iff.1 hzmem⟩).symm
    have hradU := ae_radial_congr_th (n := m) hm heqU
    have hradG := ae_radial_congr_th (n := m) hm heqG
    have hmeasp : Measurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × ℝ =>
        ((σ, p.2 • (p.1 : EuclideanSpace ℝ (Fin m))) : CapSpace m)) :=
      measurable_const.prodMk (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst))
    have hjointFun : StronglyMeasurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × ℝ =>
        repFun (hemisphere m) u (σ, p.2 • (p.1 : EuclideanSpace ℝ (Fin m))) ^ 2) :=
      ((stronglyMeasurable_repFun (hemisphere m) u).comp_measurable hmeasp).pow 2
    have hrefMeas0 : StronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ),
          repFun (hemisphere m) u (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2) :=
      hjointFun.integral_prod_right' (ν := volume.restrict (Ioo ((1:ℝ)/4) (1/2 : ℝ)))
    have hjointFun2 : StronglyMeasurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × ℝ =>
        inner ℝ (repGz_el (hemisphere m) u (σ, p.2 • (p.1 : EuclideanSpace ℝ (Fin m))))
          (p.1 : EuclideanSpace ℝ (Fin m)) ^ 2) := by
      have h1 : Measurable (fun p : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 × ℝ =>
          repGz_el (hemisphere m) u (σ, p.2 • (p.1 : EuclideanSpace ℝ (Fin m)))) :=
        (stronglyMeasurable_repGz_el (hemisphere m) u).measurable.comp hmeasp
      exact (h1.inner (measurable_subtype_coe.comp measurable_fst)).pow_const 2
        |>.stronglyMeasurable
    have hdirMeas0 : StronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ r in Ioo ((1:ℝ)/4) ρ,
          inner ℝ (repGz_el (hemisphere m) u (σ, r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)) ^ 2) :=
      hjointFun2.integral_prod_right' (ν := volume.restrict (Ioo ((1:ℝ)/4) ρ))
    have hh2 : (1:ℝ)/2 < rad_el := by nlinarith [rad_sq_el, rad_pos_el]
    have hsub12 : Ioo ((1:ℝ)/4) (1/2 : ℝ) ⊆ Ioo (0:ℝ) ρ :=
      Ioo_subset_Ioo (by norm_num) (by linarith [hh2, hρgt])
    have hsub14 : Ioo ((1:ℝ)/4) ρ ⊆ Ioo (0:ℝ) ρ := Ioo_subset_Ioo (by norm_num) le_rfl
    have hrefMeas : AEStronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
        (sphereMeasure m) := by
      refine hrefMeas0.aestronglyMeasurable.congr ?_
      filter_upwards [hradU] with w hw
      have hw' := ae_mono (Measure.restrict_mono hsub12 le_rfl) hw
      refine integral_congr_ae ?_
      filter_upwards [hw'] with r hr using by rw [hr]
    have hdirMeas : AEStronglyMeasurable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) ^ 2) (sphereMeasure m) := by
      refine hdirMeas0.aestronglyMeasurable.congr ?_
      filter_upwards [hradG] with w hw
      have hw' := ae_mono (Measure.restrict_mono hsub14 le_rfl) hw
      refine integral_congr_ae ?_
      filter_upwards [hw'] with r hr using by rw [hr]
    have hInnerMeas : ∀ᵐ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        AEStronglyMeasurable (fun r => inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) ^ 2) (volume.restrict (Ioo ((1:ℝ)/4) ρ)) := by
      filter_upwards [hradG] with w hw
      have hw' := ae_mono (Measure.restrict_mono hsub14 le_rfl) hw
      have hmeasr : Measurable (fun r : ℝ => ((σ, r • (w : EuclideanSpace ℝ (Fin m))) : CapSpace m)) :=
        measurable_const.prodMk (measurable_id.smul_const (w : EuclideanSpace ℝ (Fin m)))
      have hjointMeas : StronglyMeasurable (fun r : ℝ =>
          inner ℝ (repGz_el (hemisphere m) u (σ, r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)) ^ 2) := by
        have h1 : Measurable (fun r : ℝ => repGz_el (hemisphere m) u (σ, r • (w : EuclideanSpace ℝ (Fin m)))) :=
          (stronglyMeasurable_repGz_el (hemisphere m) u).measurable.comp hmeasr
        exact (h1.inner measurable_const).pow_const 2 |>.stronglyMeasurable
      refine (hjointMeas.aestronglyMeasurable).congr ?_
      filter_upwards [hw'] with r hr using by rw [hr]
    -- Step 7: `ref`, `dir` are honestly integrable in `w`, via the `4^{m-1}` comparison.
    have hu_ρ_int : IntegrableOn (fun z => u.toFun (σ, z) ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) ρ) volume := hu_memLp.integrable_sq
    have hu_half_int : IntegrableOn (fun z => u.toFun (σ, z) ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) (1/2 : ℝ)) volume :=
      hu_ρ_int.mono_set (ball_subset_ball (by linarith [hh2, hρgt] : (1:ℝ)/2 ≤ ρ))
    have hg_int : IntegrableOn (fun z => ‖u.gz (σ, z)‖ ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) ρ) volume := (hg_memLp.norm).integrable_sq
    have hrefInt : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
        (sphereMeasure m) := by
      have hae := ae_integrableOn_weighted (R := (1:ℝ)/2) hm hu_half_int
      have hballang := integrable_ball_angular (R := (1:ℝ)/2) hm hu_half_int
      refine Integrable.mono' (hballang.const_mul ((4:ℝ) ^ (m-1))) hrefMeas ?_
      filter_upwards [hae] with w hw
      have hbnd := interval_le_weighted_ssh hm (a := (1:ℝ)/4) (b := (1:ℝ)/2) (ρ := (1:ℝ)/2)
        (by norm_num) (by norm_num) le_rfl
        (H := fun r => u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
        (fun r => sq_nonneg _) hw
      have hrefnn : (0:ℝ) ≤ ∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ),
          u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2 :=
        setIntegral_nonneg measurableSet_Ioo (fun r _ => sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hrefnn]
      have h4eq : ((1:ℝ)/4)⁻¹ ^ (m-1) = (4:ℝ) ^ (m-1) := by norm_num
      rwa [h4eq] at hbnd
    have hdirInt : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) ^ 2) (sphereMeasure m) := by
      have hae := ae_integrableOn_weighted (R := ρ) hm hg_int
      have hballang := integrable_ball_angular (R := ρ) hm hg_int
      refine Integrable.mono' (hballang.const_mul ((4:ℝ) ^ (m-1))) hdirMeas ?_
      filter_upwards [hae, hInnerMeas] with w hw hwmeas
      have hwn : ‖(w : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
      have hCS : ∀ r : ℝ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) ^ 2 ≤ ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := by
        intro r
        have hcs := abs_real_inner_le_norm (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m))
        rw [hwn, mul_one] at hcs
        calc inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m)) ^ 2
            ≤ |inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m))| ^ 2 := by
              rw [sq_abs]
          _ ≤ ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hcs 2
      have hH'nn : ∀ r : ℝ, 0 ≤ ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := fun r => sq_nonneg _
      have hab14 : (1:ℝ)/4 ≤ ρ := by linarith [hq4, hρgt]
      have hIntabH' : IntegrableOn (fun r => ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2)
          (Ioo ((1:ℝ)/4) ρ) volume :=
        integrableOn_of_weighted_ssh hm (by norm_num) le_rfl hH'nn hw
      have hIntabH : IntegrableOn (fun r => inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) ^ 2) (Ioo ((1:ℝ)/4) ρ) volume := by
        refine Integrable.mono' hIntabH' ?_ ?_
        · exact hwmeas
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r _
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hCS r
      have hmono1 : (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) ^ 2)
          ≤ ∫ r in Ioo ((1:ℝ)/4) ρ, ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 :=
        setIntegral_mono_on hIntabH hIntabH' measurableSet_Ioo (fun r _ => hCS r)
      have hbnd := interval_le_weighted_ssh hm (a := (1:ℝ)/4) (b := ρ) (ρ := ρ)
        (by norm_num) hab14 le_rfl
        (H := fun r => ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2) hH'nn hw
      have hdirnn : (0:ℝ) ≤ ∫ r in Ioo ((1:ℝ)/4) ρ,
          inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m)) ^ 2 :=
        setIntegral_nonneg measurableSet_Ioo (fun r _ => sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hdirnn]
      have h4eq : ((1:ℝ)/4)⁻¹ ^ (m-1) = (4:ℝ) ^ (m-1) := by norm_num
      rw [h4eq] at hbnd
      exact hmono1.trans hbnd
    -- Step 8: assemble.
    have hLHS_int : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ∫ r in Ioo (0 : ℝ) ρ, r ^ (m-1) * F (r • (w : EuclideanSpace ℝ (Fin m)))) (sphereMeasure m) :=
      integrable_ball_angular hm hFint
    have hRHS_int : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        (8 * (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
          + 2 * (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
              (w : EuclideanSpace ℝ (Fin m)) ^ 2)) * (2 * Real.pi)) (sphereMeasure m) :=
      ((hrefInt.const_mul 8).add (hdirInt.const_mul 2)).mul_const (2 * Real.pi)
    have hstep1 := integral_mono_ae hLHS_int hRHS_int hptw
    rw [← hpolar] at hstep1
    have hint_add : (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (8 * (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
          + 2 * (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
              (w : EuclideanSpace ℝ (Fin m)) ^ 2)) * (2 * Real.pi) ∂(sphereMeasure m))
        = (8 * (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
              ∂(sphereMeasure m))
            + 2 * (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
                (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
                  (w : EuclideanSpace ℝ (Fin m)) ^ 2) ∂(sphereMeasure m))) * (2 * Real.pi) := by
      rw [integral_mul_const, integral_add (hrefInt.const_mul 8) (hdirInt.const_mul 2),
        integral_const_mul, integral_const_mul]
    rw [hint_add] at hstep1
    -- the `4^{m-1}` comparison with the ball masses.
    have hrefBall : (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
        ∂(sphereMeasure m))
        ≤ (4:ℝ) ^ (m-1) * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, u.toFun (σ, z) ^ 2 := by
      have hae := ae_integrableOn_weighted (R := (1:ℝ)/2) hm hu_half_int
      have hballang := integrable_ball_angular (R := (1:ℝ)/2) hm hu_half_int
      have hptw2 : ∀ᵐ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
          (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
            ≤ (4:ℝ) ^ (m-1) * ∫ r in Ioo (0:ℝ) (1/2 : ℝ),
                r ^ (m-1) * u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2 := by
        filter_upwards [hae] with w hw
        have hbnd := interval_le_weighted_ssh hm (a := (1:ℝ)/4) (b := (1:ℝ)/2) (ρ := (1:ℝ)/2)
          (by norm_num) (by norm_num) le_rfl
          (H := fun r => u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
          (fun r => sq_nonneg _) hw
        have h4eq : ((1:ℝ)/4)⁻¹ ^ (m-1) = (4:ℝ) ^ (m-1) := by norm_num
        rwa [h4eq] at hbnd
      have hmono := integral_mono_ae hrefInt (hballang.const_mul _) hptw2
      rw [integral_const_mul, ← integral_ball_polar_symm hm hu_half_int] at hmono
      refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact setIntegral_mono_set hu_ρ_int
        (Eventually.of_forall fun z => by simp only [Pi.zero_apply]; exact sq_nonneg _)
        (HasSubset.Subset.eventuallyLE
          (ball_subset_ball (by linarith [hh2, hρgt] : (1:ℝ)/2 ≤ ρ)))
    have hdirBall : (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
          (w : EuclideanSpace ℝ (Fin m)) ^ 2) ∂(sphereMeasure m))
        ≤ (4:ℝ) ^ (m-1) * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, ‖u.gz (σ, z)‖ ^ 2 := by
      have hae := ae_integrableOn_weighted (R := ρ) hm hg_int
      have hballang := integrable_ball_angular (R := ρ) hm hg_int
      have hptw2 : ∀ᵐ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
          (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
              (w : EuclideanSpace ℝ (Fin m)) ^ 2)
            ≤ (4:ℝ) ^ (m-1) * ∫ r in Ioo (0:ℝ) ρ,
                r ^ (m-1) * ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := by
        filter_upwards [hae, hInnerMeas] with w hw hwmeas
        have hwn : ‖(w : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.1 w.2
        have hCS : ∀ r : ℝ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)) ^ 2 ≤ ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := by
          intro r
          have hcs := abs_real_inner_le_norm (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m))
          rw [hwn, mul_one] at hcs
          calc inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m)) ^ 2
              ≤ |inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))) (w : EuclideanSpace ℝ (Fin m))| ^ 2 := by
                rw [sq_abs]
            _ ≤ ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) hcs 2
        have hH'nn : ∀ r : ℝ, 0 ≤ ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 := fun r => sq_nonneg _
        have hab14 : (1:ℝ)/4 ≤ ρ := by linarith [hq4, hρgt]
        have hIntabH' : IntegrableOn (fun r => ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2)
            (Ioo ((1:ℝ)/4) ρ) volume :=
          integrableOn_of_weighted_ssh hm (by norm_num) le_rfl hH'nn hw
        have hIntabH : IntegrableOn (fun r => inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)) ^ 2) (Ioo ((1:ℝ)/4) ρ) volume := by
          refine Integrable.mono' hIntabH' hwmeas ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r _
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hCS r
        have hmono1 : (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)) ^ 2)
            ≤ ∫ r in Ioo ((1:ℝ)/4) ρ, ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2 :=
          setIntegral_mono_on hIntabH hIntabH' measurableSet_Ioo (fun r _ => hCS r)
        have hbnd := interval_le_weighted_ssh hm (a := (1:ℝ)/4) (b := ρ) (ρ := ρ)
          (by norm_num) hab14 le_rfl
          (H := fun r => ‖u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m)))‖ ^ 2) hH'nn hw
        have h4eq : ((1:ℝ)/4)⁻¹ ^ (m-1) = (4:ℝ) ^ (m-1) := by norm_num
        rw [h4eq] at hbnd
        exact hmono1.trans hbnd
      have hmono := integral_mono_ae hdirInt (hballang.const_mul _) hptw2
      rwa [integral_const_mul,
        ← integral_ball_polar_symm hm hg_int] at hmono
    have hfin : (8 * (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
              (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
              ∂(sphereMeasure m))
            + 2 * (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
                (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
                  (w : EuclideanSpace ℝ (Fin m)) ^ 2) ∂(sphereMeasure m))) * (2 * Real.pi)
        ≤ (16 * Real.pi * 4 ^ (m-1)) *
          ((∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, u.toFun (σ, z) ^ 2)
            + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, ‖u.gz (σ, z)‖ ^ 2) := by
      have hpi : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
      have h4nn : (0:ℝ) ≤ (4:ℝ) ^ (m-1) := by positivity
      have hDnn : (0:ℝ) ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, ‖u.gz (σ, z)‖ ^ 2 :=
        setIntegral_nonneg measurableSet_ball (fun z _ => sq_nonneg _)
      have h1 : Real.pi * (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          (∫ r in Ioo ((1:ℝ)/4) (1/2 : ℝ), u.toFun (σ, r • (w : EuclideanSpace ℝ (Fin m))) ^ 2)
          ∂(sphereMeasure m))
          ≤ Real.pi * ((4:ℝ) ^ (m-1) * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, u.toFun (σ, z) ^ 2) :=
        mul_le_mul_of_nonneg_left hrefBall hpi
      have h2 : Real.pi * (∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          (∫ r in Ioo ((1:ℝ)/4) ρ, inner ℝ (u.gz (σ, r • (w : EuclideanSpace ℝ (Fin m))))
            (w : EuclideanSpace ℝ (Fin m)) ^ 2) ∂(sphereMeasure m))
          ≤ Real.pi * ((4:ℝ) ^ (m-1) * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, ‖u.gz (σ, z)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdirBall hpi
      nlinarith [h1, h2, mul_nonneg (mul_nonneg hpi h4nn) hDnn]
    exact hstep1.trans hfin

/-- The hemisphere's transverse radius is strictly less than `1` for every interior level. -/
theorem hemi_theta_lt_one_ssh {σ : ℝ} (hσ : σ ∈ Ioo (-(1:ℝ)) 0) : (hemisphere m).θ σ < 1 := by
  rw [hemi_theta_elg m σ]
  have h1 : (0:ℝ) < σ + 1 := by linarith [hσ.1]
  have h2 : σ + 1 < 1 := by linarith [hσ.2]
  have h4 : 1 - (σ + 1) ^ 2 < 1 := by nlinarith
  have h5 : (0:ℝ) ≤ 1 - (σ + 1) ^ 2 := by nlinarith
  calc Real.sqrt (1 - (σ + 1) ^ 2) < Real.sqrt 1 := Real.sqrt_lt_sqrt h5 h4
    _ = 1 := Real.sqrt_one

/-! ## 11. Assembling the transverse short-slice bound -/

/-- The level bound of Part 10, transported to the globally measurable representatives
`repFun`/`repGz_el` and to the already-integrable transverse mass/energy `trMass_el`/`trEnergy_el`
of `RobinCaps.Cap.EntranceL2Hemi`. -/
theorem ae_level_wt_bound_repFun_ssh (hm : 1 ≤ m) (u : H1P (hemisphere m).body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-(1:ℝ)) 0)),
      (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          wt_elg m z * repFun (hemisphere m) u (σ, z) ^ 2)
        ≤ (16 * Real.pi * 4 ^ (m - 1)) *
          (trMass_el (hemisphere m) u σ + trEnergy_el (hemisphere m) u σ) := by
  have hKm : (hemisphere m).K = 1 := hemi_K_elg m
  have h1 := ae_level_wt_bound_ssh hm u
  have h2 := ae_restrict_of_ae (s := Ioo (-(1:ℝ)) 0) (ae_ae_transverse_repFun_el (hemisphere m) u)
  have h3 := ae_restrict_of_ae (s := Ioo (-(1:ℝ)) 0) (ae_ae_transverse_repGz_el (hemisphere m) u)
  filter_upwards [h1, h2, h3, ae_restrict_mem measurableSet_Ioo] with σ hbound hrepF hrepG hσmem
  have hσmemK : σ ∈ Ioo (-(hemisphere m).K) 0 := by rw [hKm]; exact hσmem
  have heqU : (fun z => u.toFun (σ, z)) =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ))]
      (fun z => repFun (hemisphere m) u (σ, z)) := by
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hrepF] with z hz hzmem
    exact (hz ⟨hσmemK.1, hσmemK.2, mem_ball_zero_iff.1 hzmem⟩).symm
  have heqG : (fun z => u.gz (σ, z)) =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ))]
      (fun z => repGz_el (hemisphere m) u (σ, z)) := by
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hrepG] with z hz hzmem
    exact (hz ⟨hσmemK.1, hσmemK.2, mem_ball_zero_iff.1 hzmem⟩).symm
  have hc1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
      wt_elg m z * u.toFun (σ, z) ^ 2)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          wt_elg m z * repFun (hemisphere m) u (σ, z) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [heqU] with z hz
    rw [hz]
  have hc2 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ), u.toFun (σ, z) ^ 2)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          repFun (hemisphere m) u (σ, z) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [heqU] with z hz
    rw [hz]
  have hc3 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ), ‖u.gz (σ, z)‖ ^ 2)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          ‖repGz_el (hemisphere m) u (σ, z)‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [heqG] with z hz
    rw [hz]
  have htrM : trMass_el (hemisphere m) u σ
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          repFun (hemisphere m) u (σ, z) ^ 2 := by
    rw [trMass_el, show (fun z => ((hemisphere m).body.indicator fun p => repFun (hemisphere m) u p ^ 2) (σ, z))
        = fun z => (ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ)).indicator
          (fun z => repFun (hemisphere m) u (σ, z) ^ 2) z from
      funext (indicator_body_transverse_el (hemisphere m) _ hσmemK),
      integral_indicator measurableSet_ball]
  have htrE : trEnergy_el (hemisphere m) u σ
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          ‖repGz_el (hemisphere m) u (σ, z)‖ ^ 2 := by
    rw [trEnergy_el, show (fun z => ((hemisphere m).body.indicator fun p => ‖repGz_el (hemisphere m) u p‖ ^ 2) (σ, z))
        = fun z => (ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ)).indicator
          (fun z => ‖repGz_el (hemisphere m) u (σ, z)‖ ^ 2) z from
      funext (indicator_body_transverse_el (hemisphere m) _ hσmemK),
      integral_indicator measurableSet_ball]
  rw [← hc1, htrM, htrE, ← hc2, ← hc3]
  exact hbound

/-- **Global integrability of the weighted mass** `wt(z) · repFun(p)²` on the whole cap body,
established from `ae_level_wt_bound_repFun_ssh` via the converse Fubini criterion
`MeasureTheory.integrable_prod_iff`, without any circularity. -/
theorem integrable_body_wt_mul_repFun_sq_ssh (hm : 1 ≤ m) (u : H1P (hemisphere m).body) :
    Integrable ((hemisphere m).body.indicator
      (fun p => wt_elg m p.2 * repFun (hemisphere m) u p ^ 2)) volume := by
  set H : ℝ × EuclideanSpace ℝ (Fin m) → ℝ := fun p =>
      wt_elg m p.2 * ((hemisphere m).body.indicator (fun p => repFun (hemisphere m) u p ^ 2) p)
    with hHdef
  have hHeq : ((hemisphere m).body.indicator
      (fun p => wt_elg m p.2 * repFun (hemisphere m) u p ^ 2)) = H := by
    funext p
    show ((hemisphere m).body.indicator (fun p => wt_elg m p.2 * repFun (hemisphere m) u p ^ 2)) p
      = wt_elg m p.2 * ((hemisphere m).body.indicator (fun p => repFun (hemisphere m) u p ^ 2) p)
    by_cases hp : p ∈ (hemisphere m).body
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
  rw [hHeq, Measure.volume_eq_prod]
  have hmeasH : StronglyMeasurable H := by
    have h1 : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin m) => wt_elg m p.2) :=
      (measurable_wt_elg m).comp measurable_snd
    have h2 : StronglyMeasurable ((hemisphere m).body.indicator
        (fun p => repFun (hemisphere m) u p ^ 2)) :=
      ((stronglyMeasurable_repFun (hemisphere m) u).pow 2).indicator (measurableSet_body' _)
    exact h1.stronglyMeasurable.mul h2
  refine (integrable_prod_iff hmeasH.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · have hmemlp := ae_transverse_repFun_memLp_ssh (hemisphere m) u
    filter_upwards [hmemlp] with σ hmemlp
    by_cases hσ : σ ∈ Ioo (-(1:ℝ)) 0
    · have hKm : (hemisphere m).K = 1 := hemi_K_elg m
      have hσK : σ ∈ Ioo (-(hemisphere m).K) 0 := by rw [hKm]; exact hσ
      have hρ1 : (hemisphere m).θ σ < 1 := hemi_theta_lt_one_ssh hσ
      have hIntOn := integrableOn_wt_mul_sq_ssh (m := m) hρ1 (hmemlp hσK)
      have heqInd : (fun z => H (σ, z))
          = (ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ)).indicator
            (fun z => wt_elg m z * repFun (hemisphere m) u (σ, z) ^ 2) := by
        funext z
        rw [hHdef]
        dsimp only
        rw [indicator_body_transverse_el (hemisphere m) _ hσK]
        by_cases hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ)
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
      rw [heqInd]
      exact hIntOn.integrable_indicator measurableSet_ball
    · have heqzero : (fun z => H (σ, z)) = fun _ => (0:ℝ) := by
        funext z
        rw [hHdef]
        dsimp only
        rw [Set.indicator_of_notMem (fun hb => hσ ⟨hb.1, hb.2.1⟩), mul_zero]
      rw [heqzero]
      exact integrable_zero _ _ _
  · have hbnd := ae_level_wt_bound_repFun_ssh hm u
    have hMTint := integrable_trMass_el (hemisphere m) u
    have hETint := integrable_trEnergy_el (hemisphere m) u
    have hmeasσ : StronglyMeasurable (fun σ => ∫ z, ‖H (σ, z)‖) := by
      have : (fun σ => ∫ z, ‖H (σ, z)‖) = fun σ => ∫ z, H (σ, z) := by
        funext σ
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        show ‖H (σ, z)‖ = H (σ, z)
        rw [Real.norm_eq_abs, abs_of_nonneg]
        rw [hHdef]
        dsimp only
        exact mul_nonneg (wt_nonneg_elg m z)
          (Set.indicator_nonneg (fun p _ => sq_nonneg _) _)
      rw [this]
      exact hmeasH.integral_prod_right'
    refine Integrable.mono' ((hMTint.add hETint).const_mul (16 * Real.pi * 4 ^ (m-1)))
      hmeasσ.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo] at hbnd
    filter_upwards [hbnd] with σ hσimp
    have hHnn : ∀ z, 0 ≤ H (σ, z) := fun z => by
      rw [hHdef]; dsimp only
      exact mul_nonneg (wt_nonneg_elg m z) (Set.indicator_nonneg (fun p _ => sq_nonneg _) _)
    have hInorm : (∫ z, ‖H (σ, z)‖) = ∫ z, H (σ, z) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      show ‖H (σ, z)‖ = H (σ, z)
      rw [Real.norm_eq_abs, abs_of_nonneg (hHnn z)]
    rw [Real.norm_eq_abs, hInorm, abs_of_nonneg (integral_nonneg hHnn)]
    by_cases hσmem : σ ∈ Ioo (-(1:ℝ)) 0
    · have hKm : (hemisphere m).K = 1 := hemi_K_elg m
      have hσK : σ ∈ Ioo (-(hemisphere m).K) 0 := by rw [hKm]; exact hσmem
      have heqInd : (fun z => H (σ, z))
          = (ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ)).indicator
            (fun z => wt_elg m z * repFun (hemisphere m) u (σ, z) ^ 2) := by
        funext z
        rw [hHdef]
        dsimp only
        rw [indicator_body_transverse_el (hemisphere m) _ hσK]
        by_cases hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ)
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
      rw [heqInd, integral_indicator measurableSet_ball]
      exact hσimp hσmem
    · have heqzero : (fun z => H (σ, z)) = fun _ => (0:ℝ) := by
        funext z
        rw [hHdef]
        dsimp only
        rw [Set.indicator_of_notMem (fun hb => hσmem ⟨hb.1, hb.2.1⟩), mul_zero]
      rw [heqzero, integral_zero]
      have h1 := trMass_nonneg_el (hemisphere m) u σ
      have h2 := trEnergy_nonneg_el (hemisphere m) u σ
      have h3 : (0:ℝ) ≤ 16 * Real.pi * 4 ^ (m-1) := by positivity
      have h4 : (0:ℝ) ≤ trMass_el (hemisphere m) u σ + trEnergy_el (hemisphere m) u σ := by
        linarith [h1, h2]
      exact mul_nonneg h3 h4

/-- **The full-space weighted axial-mass bound.**  Assembles `integrable_body_wt_mul_repFun_sq_ssh`
and `ae_level_wt_bound_repFun_ssh` via the two orders of Fubini for the cap body
(`integral_body_eq_integral_slices`, z outer / s inner, matching `axMass_el`'s own definition;
`integral_body_eq_slices_tr_po`, σ outer / z inner, matching the per-level bound) into the
`massP`/`dirichletP` bound. -/
theorem integral_wt_axMass_le_ssh (hm : 1 ≤ m) (u : H1P (hemisphere m).body) :
    (∫ z, wt_elg m z * axMass_el (hemisphere m) u z)
      ≤ (16 * Real.pi * 4 ^ (m-1)) * (massP u + dirichletP u) := by
  set F : CapSpace m → ℝ := fun p => wt_elg m p.2 * repFun (hemisphere m) u p ^ 2 with hFdef
  have hF : Integrable ((hemisphere m).body.indicator F) volume :=
    integrable_body_wt_mul_repFun_sq_ssh hm u
  have hKm : (hemisphere m).K = 1 := hemi_K_elg m
  have heqZ : (∫ p in (hemisphere m).body, F p)
      = ∫ z, ∫ s in Ioo (-(hemisphere m).K) (exitTime (hemisphere m) z), F (s, z) :=
    integral_body_eq_integral_slices (hemisphere m) hF
  have heqZ' : (∫ z, ∫ s in Ioo (-(hemisphere m).K) (exitTime (hemisphere m) z), F (s, z))
      = ∫ z, wt_elg m z * axMass_el (hemisphere m) u z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show (∫ s in Ioo (-(hemisphere m).K) (exitTime (hemisphere m) z), wt_elg m z * repFun (hemisphere m) u (s, z) ^ 2)
      = wt_elg m z * axMass_el (hemisphere m) u z
    rw [integral_const_mul, axMass_el]
  have heqS : (∫ p in (hemisphere m).body, F p)
      = ∫ σ, ∫ z, ((hemisphere m).body.indicator F) (σ, z) :=
    integral_body_eq_slices_tr_po (hemisphere m) hF
  set wtrMass : ℝ → ℝ := fun σ => ∫ z, ((hemisphere m).body.indicator F) (σ, z) with hwtrMassdef
  have hwtrMassInt : Integrable wtrMass volume :=
    integrable_slice_integral_tr_po (hemisphere m) hF
  have hwtrMassBound : ∀ᵐ σ ∂(volume : Measure ℝ),
      wtrMass σ ≤ 16 * Real.pi * 4 ^ (m-1)
        * (trMass_el (hemisphere m) u σ + trEnergy_el (hemisphere m) u σ) := by
    have hbnd := ae_level_wt_bound_repFun_ssh hm u
    rw [ae_restrict_iff' measurableSet_Ioo] at hbnd
    filter_upwards [hbnd] with σ hσimp
    by_cases hσ : σ ∈ Ioo (-(1:ℝ)) 0
    · have hσK : σ ∈ Ioo (-(hemisphere m).K) 0 := by rw [hKm]; exact hσ
      have heqInd : wtrMass σ = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ),
          wt_elg m z * repFun (hemisphere m) u (σ, z) ^ 2 := by
        rw [hwtrMassdef]
        show (∫ z, ((hemisphere m).body.indicator F) (σ, z)) = _
        rw [show (fun z => ((hemisphere m).body.indicator F) (σ, z))
            = fun z => (ball (0 : EuclideanSpace ℝ (Fin m)) ((hemisphere m).θ σ)).indicator
              (fun z => wt_elg m z * repFun (hemisphere m) u (σ, z) ^ 2) z from
          funext (indicator_body_transverse_el (hemisphere m) F hσK), integral_indicator measurableSet_ball]
      rw [heqInd]
      exact hσimp hσ
    · have heqzero : wtrMass σ = 0 := by
        rw [hwtrMassdef]
        show (∫ z, ((hemisphere m).body.indicator F) (σ, z)) = 0
        have hz0 : ∀ z, ((hemisphere m).body.indicator F) (σ, z) = 0 := fun z =>
          Set.indicator_of_notMem (fun hb => hσ ⟨hb.1, hb.2.1⟩) F
        simp only [hz0, integral_zero]
      rw [heqzero]
      have h1 := trMass_nonneg_el (hemisphere m) u σ
      have h2 := trEnergy_nonneg_el (hemisphere m) u σ
      have h3 : (0:ℝ) ≤ 16 * Real.pi * 4 ^ (m-1) := by positivity
      have h4 : (0:ℝ) ≤ trMass_el (hemisphere m) u σ + trEnergy_el (hemisphere m) u σ := by
        linarith [h1, h2]
      exact mul_nonneg h3 h4
  have hMTint := integrable_trMass_el (hemisphere m) u
  have hETint := integrable_trEnergy_el (hemisphere m) u
  have hfinal : (∫ σ, wtrMass σ)
      ≤ 16 * Real.pi * 4 ^ (m-1)
        * ((∫ σ, trMass_el (hemisphere m) u σ) + ∫ σ, trEnergy_el (hemisphere m) u σ) := by
    have hmono := integral_mono_ae hwtrMassInt ((hMTint.add hETint).const_mul _) hwtrMassBound
    rw [integral_const_mul] at hmono
    have hadd : (∫ a, ((hemisphere m).trMass_el u + (hemisphere m).trEnergy_el u) a)
        = (∫ σ, trMass_el (hemisphere m) u σ) + ∫ σ, trEnergy_el (hemisphere m) u σ := by
      rw [← integral_add hMTint hETint]
      exact integral_congr_ae (Eventually.of_forall fun a => by rw [Pi.add_apply])
    rwa [hadd] at hmono
  rw [integral_trMass_el, integral_trEnergy_el] at hfinal
  have hmassEq : massP u = ∫ p in (hemisphere m).body, repFun (hemisphere m) u p ^ 2 :=
    massP_eq_rep_el (hemisphere m) u
  have hdirEq : dirichletP u = (∫ p in (hemisphere m).body, repGx (hemisphere m) u p ^ 2)
      + ∫ p in (hemisphere m).body, ‖repGz_el (hemisphere m) u p‖ ^ 2 :=
    dirichletP_eq_rep_el (hemisphere m) u
  have hgxnn : (0:ℝ) ≤ ∫ p in (hemisphere m).body, repGx (hemisphere m) u p ^ 2 :=
    setIntegral_nonneg (measurableSet_body' _) fun p _ => sq_nonneg _
  have hfin2 : (∫ p in (hemisphere m).body, repFun (hemisphere m) u p ^ 2)
      + ∫ p in (hemisphere m).body, ‖repGz_el (hemisphere m) u p‖ ^ 2
      ≤ massP u + dirichletP u := by
    rw [hmassEq, hdirEq]; linarith [hgxnn]
  have h3 : (0:ℝ) ≤ 16 * Real.pi * 4 ^ (m-1) := by positivity
  calc (∫ z, wt_elg m z * axMass_el (hemisphere m) u z)
      = ∫ σ, wtrMass σ := by rw [← heqZ', ← heqZ, heqS]
    _ ≤ 16 * Real.pi * 4 ^ (m-1)
        * ((∫ p in (hemisphere m).body, repFun (hemisphere m) u p ^ 2)
          + ∫ p in (hemisphere m).body, ‖repGz_el (hemisphere m) u p‖ ^ 2) := hfinal
    _ ≤ 16 * Real.pi * 4 ^ (m-1) * (massP u + dirichletP u) :=
        mul_le_mul_of_nonneg_left hfin2 h3

/-- **The transverse short-slice bound for the hemispherical cap, general transverse dimension.**
Discharges `RobinCaps.Cap.TransverseShortSliceBound_elg` unconditionally. -/
theorem transverseShortSliceBound_hemi_ssh (m : ℕ) (hm : 1 ≤ m) :
    ∃ C0 : ℝ, TransverseShortSliceBound_elg m C0 := by
  refine ⟨16 * Real.pi * 4 ^ (m-1), ⟨by positivity, fun u => ?_, fun u => ?_⟩⟩
  · have h1 : Integrable (fun z => wt_elg m z * axMass_el (hemisphere m) u z) volume := by
      have hF : Integrable ((hemisphere m).body.indicator
          (fun p => wt_elg m p.2 * repFun (hemisphere m) u p ^ 2)) volume :=
        integrable_body_wt_mul_repFun_sq_ssh hm u
      have h2 := integrable_slice_integral (hemisphere m) hF
      have hKm : (hemisphere m).K = 1 := hemi_K_elg m
      rw [hKm] at h2
      refine h2.congr (Eventually.of_forall fun z => ?_)
      show (∫ s in Ioo (-(1:ℝ)) (exitTime (hemisphere m) z),
          wt_elg m z * repFun (hemisphere m) u (s, z) ^ 2) = wt_elg m z * axMass_el (hemisphere m) u z
      rw [integral_const_mul, axMass_el, hKm]
    exact h1.integrableOn
  · have h1 := integral_wt_axMass_le_ssh hm u
    have h2 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        wt_elg m z * axMass_el (hemisphere m) u z)
        ≤ ∫ z, wt_elg m z * axMass_el (hemisphere m) u z := by
      have hInt : Integrable (fun z => wt_elg m z * axMass_el (hemisphere m) u z) volume := by
        have hF : Integrable ((hemisphere m).body.indicator
            (fun p => wt_elg m p.2 * repFun (hemisphere m) u p ^ 2)) volume :=
          integrable_body_wt_mul_repFun_sq_ssh hm u
        have h2 := integrable_slice_integral (hemisphere m) hF
        have hKm : (hemisphere m).K = 1 := hemi_K_elg m
        rw [hKm] at h2
        refine h2.congr (Eventually.of_forall fun z => ?_)
        show (∫ s in Ioo (-(1:ℝ)) (exitTime (hemisphere m) z),
            wt_elg m z * repFun (hemisphere m) u (s, z) ^ 2) = wt_elg m z * axMass_el (hemisphere m) u z
        rw [integral_const_mul, axMass_el, hKm]
      refine setIntegral_le_integral hInt (Eventually.of_forall fun z => ?_)
      exact mul_nonneg (wt_nonneg_elg m z) (axMass_nonneg_el _ _ _)
    exact h2.trans h1

/-- **The general-`m` entrance-trace bound for the hemispherical cap, proved unconditionally.**
Combines `transverseShortSliceBound_hemi_ssh` with `RobinCaps.Cap.capEntranceL2_hemi_elg`. -/
theorem capEntranceL2_hemi_ssh (m : ℕ) (hm : 1 ≤ m) :
    ∃ C₁ : ℝ, CapEntranceL2 (Cap.hemisphere m) C₁ := by
  obtain ⟨C0, hC0⟩ := transverseShortSliceBound_hemi_ssh m hm
  exact capEntranceL2_hemi_elg m hm hC0

end
end Cap
end RobinCaps
