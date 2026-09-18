import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.Concave
import RobinCaps.ThinDomain.TraceOne

/-!
# The Poincaré–Wirtinger inequality on a two-dimensional cap body (`m = 1`)

This file discharges the interface `RobinCaps.Cap.CapPoincare` of `RobinCaps/Cap/LowerWeak.lean`
in transverse dimension `m = 1`, i.e. for the plane region

`C = {(s,z) | -K < s < 0, ‖z‖ < θ s} ⊆ ℝ × EuclideanSpace ℝ (Fin 1)`,

for weak `H¹` functions, **without** any compactness (Rellich) input.

## The argument

The profile `θ` is non-increasing, so the horizontal segment joining `(s,z)` to `(σ,z)` stays in
the body whenever `σ ≤ s`, and the far-left strip `(-K,-K/2) × (-c,c)`, `c = θ(-K/2)/2`, is
contained in the body.  Every point of the body is therefore joined to the strip by an *L-shaped
path* with three legs: from `(s,y)` horizontally to the **anchoring level** `τ s = (s-K)/2`
(which is affine in `s`, always lies in `(-K,-K/2)` and to the left of `s`), then vertically
inside the section at that level to a point `(τ s, w)` of the strip, then horizontally to the
**anchor level** `σ₀ ∈ (-K,-K/2)`.  Squaring and using Cauchy–Schwarz on each leg gives, at
almost every point,

`(u(s,y) − t)² ≤ 10K·G(y) + 10·H(τ s) + 10K·(mean of G over the strip segment)`,

where `G` is the axial energy of the axial line through the point, `H` the transverse energy of
a level, and `t` the mean of `u` over the transverse segment of the strip at `σ₀`.  Integrating
(`σ` outer, transverse inner) gives `CP = 10K² + 20K²/θ(-K/2) + 40`.

The bookkeeping that makes this work is that the two slice-wise fundamental theorems of calculus
are used in *opposite* Fubini orders.  The axial one is therefore upgraded here to a genuine
two-dimensional a.e. statement (`ae_axialDefect_po`), which is legitimate because the defect
`repFun − entranceVal − slicePrim` of `RobinCaps/Cap/SliceAC.lean` is measurable; the transverse
one (`sliceAC_transverse_cap_po`, the transverse companion of `sliceAC_axial_cap`) is only ever
used with the axial variable outermost.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Transverse

noncomputable section

/-! ## 1. Translation of a one-dimensional weak derivative -/

/-- **Translation of the one-dimensional weak derivative by `h`.**  This is the two-sided
companion of `RobinCaps.ThinDomain.hasWeakDeriv_translate` (which only produces intervals with
left endpoint `0`). -/
theorem hasWeakDeriv_shift_po {a b h : ℝ} {F G : ℝ → ℝ} (hw : HasWeakDeriv a b F G) :
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

/-- **The transverse slice transport on a symmetric interval.**  A weak gradient on the ball
`B(0,ρ) ⊆ EuclideanSpace ℝ (Fin 1)` gives a one-dimensional weak derivative on `(-ρ, ρ)`
through the identification `ept`. -/
theorem hasWeakDeriv_ept_of_hasWeakGrad_po {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} {g : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
    (h : Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ) f g) :
    HasWeakDeriv (-ρ) ρ (fun y => f (ept y)) (fun y => g (ept y) 0) := by
  have h0 := ThinDomain.hasWeakDeriv_of_hasWeakGrad_ball hρ h
  have h1 := hasWeakDeriv_shift_po (h := ρ) h0
  have hshift : ∀ y : ℝ, eptSh ρ (y + ρ) = ept y := by
    intro y; simp [eptSh]
  have e1 : (0 : ℝ) - ρ = -ρ := by ring
  have e2 : 2 * ρ - ρ = ρ := by ring
  rw [e1, e2] at h1
  simpa only [hshift] using h1

/-! ## 2. Transverse slice-wise absolute continuity on the cap body -/

/-- The transverse slice statement on one sub-cylinder `(-K,c) × B(0, θ c)`. -/
theorem sliceAC_transverse_sub_po (C : Cap 1) (u : H1P C.body) {c : ℝ} (hc : c ∈ Ioo (-C.K) 0) :
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
  exact hasWeakDeriv_ept_of_hasWeakGrad_po (C.θ_pos c hc) hσ

/-- Two-sided version of `RobinCaps.Cap.setIntegral_Ioo_eq_of_vanishing`. -/
theorem setIntegral_Ioo_eq_of_vanishing_po {a b a' b' : ℝ} (h1 : a ≤ a') (h2 : b' ≤ b)
    {f w : ℝ → ℝ} (hw : ∀ x, x ∉ Ioo a' b' → w x = 0) :
    ∫ x in Ioo a b, f x * w x = ∫ x in Ioo a' b', f x * w x := by
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo
    (Ioo_subset_Ioo h1 h2) ?_
  rintro x ⟨-, hx2⟩
  rw [hw x hx2, mul_zero]

/-- Two-sided version of `RobinCaps.Cap.hasWeakDeriv_extend_test`. -/
theorem hasWeakDeriv_extend_test_po {a b a' b' : ℝ} (h1 : a ≤ a') (h2 : b' ≤ b) {v g : ℝ → ℝ}
    (h : HasWeakDeriv a' b' v g) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a' b') :
    ∫ x in Ioo a b, v x * deriv φ x = - ∫ x in Ioo a b, g x * φ x := by
  obtain ⟨hv1, hv2⟩ := test_vanishing hφs
  rw [setIntegral_Ioo_eq_of_vanishing_po h1 h2 hv2, setIntegral_Ioo_eq_of_vanishing_po h1 h2 hv1]
  exact h φ hφ hφc hφs

/-- **The profile is almost attained from the right by rational arguments.**  The profile is
continuous (it is concave on an open interval) and non-increasing, so any value `M < θ σ` is
still `< θ q` for some rational `q ∈ (σ, 0)`. -/
theorem exists_rat_theta_gt_po {m : ℕ} (C : Cap m) {σ M : ℝ} (hσ : σ ∈ Ioo (-C.K) 0)
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

/-- **Transverse ACL on the cap body (`m = 1`).**  For almost every axial coordinate
`σ ∈ (-K, 0)`, the transverse slice `y ↦ u(σ, ept y)` has `y ↦ (∇_z u)(σ, ept y)₀` as a weak
derivative on the whole transverse section `(-θ σ, θ σ)`. -/
theorem sliceAC_transverse_cap_po (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)),
      HasWeakDeriv (-(C.θ σ)) (C.θ σ) (fun y => u.toFun (σ, ept y))
        (fun y => u.gz (σ, ept y) 0) := by
  have hfam : ∀ q : ℚ, ∀ᵐ σ ∂(volume : Measure ℝ),
      (q : ℝ) ∈ Ioo (-C.K) 0 → σ ∈ Ioo (-C.K) (q : ℝ) →
        HasWeakDeriv (-(C.θ (q : ℝ))) (C.θ (q : ℝ)) (fun y => u.toFun (σ, ept y))
          (fun y => u.gz (σ, ept y) 0) := by
    intro q
    by_cases hq : (q : ℝ) ∈ Ioo (-C.K) 0
    · have h := sliceAC_transverse_sub_po C u hq
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
  obtain ⟨q, hqI, hqθ⟩ := exists_rat_theta_gt_po C hσmem hMlt
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
  refine hasWeakDeriv_extend_test_po ?_ hmono hkey hφ hφc hφq
  linarith

/-! ## 3. The axial fundamental theorem of calculus as a two-dimensional a.e. statement -/

/-- The converse of `RobinCaps.Cap.ae_ae_axial`, for a **measurable** predicate. -/
theorem ae_of_ae_ae_axial_po {m : ℕ} {Q : CapSpace m → Prop} (hmeas : MeasurableSet {p | Q p})
    (h : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ᵐ s ∂(volume : Measure ℝ), Q (s, z)) :
    ∀ᵐ p ∂(volume : Measure (CapSpace m)), Q p := by
  have hswap : Measurable fun w : EuclideanSpace ℝ (Fin m) × ℝ => (w.2, w.1) := by fun_prop
  have hmeas' : MeasurableSet {w : EuclideanSpace ℝ (Fin m) × ℝ | Q (w.2, w.1)} :=
    hswap hmeas
  have h1 : ∀ᵐ w ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).prod (volume : Measure ℝ)),
      Q (w.2, w.1) := (Measure.ae_prod_iff_ae_ae hmeas').2 h
  have h2 := Measure.measurePreserving_swap.quasiMeasurePreserving.ae h1
  rw [Measure.volume_eq_prod]
  exact h2

variable {m : ℕ}

/-- The measurable defect of the slice-wise fundamental theorem of calculus in the axial
direction.  It vanishes a.e. on the body (`ae_axialDefect_po`). -/
def axialDefect_po (C : Cap m) (u : H1P C.body) (p : CapSpace m) : ℝ :=
  repFun C u p - entranceVal C u p.2 - slicePrim C u p

theorem measurable_axialDefect_po (C : Cap m) (u : H1P C.body) :
    Measurable (axialDefect_po C u) :=
  (((stronglyMeasurable_repFun C u).measurable.sub
    ((measurable_entranceVal C u).comp measurable_snd)).sub
    (stronglyMeasurable_slicePrim C u).measurable)

/-- **The axial fundamental theorem of calculus, as an a.e. statement on the plane.**
This is `RobinCaps.Cap.entranceVal_spec` with the two exceptional null sets (the one in `z` and
the one in `s`) merged into a single two-dimensional null set; the passage from the iterated to
the product statement is legitimate because the defect is measurable. -/
theorem ae_axialDefect_po (C : Cap m) (u : H1P C.body) :
    ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → axialDefect_po C u p = 0 := by
  refine ae_of_ae_ae_axial_po (Q := fun p => p ∈ C.body → axialDefect_po C u p = 0) ?_ ?_
  · have h1 : MeasurableSet {p : CapSpace m | axialDefect_po C u p = 0} :=
      (measurable_axialDefect_po C u) (measurableSet_singleton (0 : ℝ))
    have h2 : {p : CapSpace m | p ∈ C.body → axialDefect_po C u p = 0}
        = (C.body)ᶜ ∪ {p : CapSpace m | axialDefect_po C u p = 0} := by
      ext p; by_cases hp : p ∈ C.body <;> simp [hp]
    rw [h2]
    exact ((measurableSet_body' C).compl).union h1
  · filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (entranceVal_spec C u),
      ae_slice_repFun C u, ae_slice_repGx C u] with z hz hrf hrg
    by_cases hzb : ‖z‖ < 1
    · have hspec := hz (mem_ball_zero_iff.2 hzb)
      have hKe : -C.K < exitTime C z := (exitTime_mem C hzb).1
      set e := exitTime C z with hedef
      have hmemslice : ∀ s : ℝ, s ∈ Ioo (-C.K) e → (s, z) ∈ C.body := by
        intro s hs
        have : s ∈ axialSlice C z := by rw [axialSlice_eq]; exact hs
        exact this
      have hprim : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)),
          slicePrim C u (s, z) = ∫ t in (-C.K)..s, u.gx (t, z) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        rw [slicePrim_eq, intervalIntegral_eq_setIntegral_Ioo hs.1.le]
        refine setIntegral_congr_ae measurableSet_Ioo ?_
        filter_upwards [hrg] with t ht htmem
        exact ht (hmemslice t ⟨htmem.1, htmem.2.trans hs.2⟩)
      have hzero : ∀ᵐ s ∂(volume.restrict (Ioo (-C.K) e)), axialDefect_po C u (s, z) = 0 := by
        filter_upwards [hspec, hprim, ae_restrict_of_ae hrf, ae_restrict_mem measurableSet_Ioo]
          with s h1 h2 h3 h4
        rw [axialDefect_po, h3 (hmemslice s h4), h1, h2]
        ring
      rw [ae_restrict_iff' measurableSet_Ioo] at hzero
      filter_upwards [hzero] with s hs hmem
      refine hs ?_
      have : s ∈ axialSlice C z := hmem
      rwa [axialSlice_eq] at this
    · push_neg at hzb
      filter_upwards with s hs
      have : s ∈ axialSlice C z := hs
      rw [axialSlice_eq, exitTime_eq_neg_K_of_one_le C hzb] at this
      simp at this

/-! ## 4. The axial deviation bound, pointwise a.e. on the plane -/

theorem memL2_repFun_po (C : Cap m) (u : H1P C.body) :
    MemLp (repFun C u) 2 (volume.restrict C.body) :=
  (memLp_congr_ae u.memL2.aestronglyMeasurable.ae_eq_mk).1 u.memL2

theorem memL2_repGx_po (C : Cap m) (u : H1P C.body) :
    MemLp (repGx C u) 2 (volume.restrict C.body) :=
  (memLp_congr_ae u.gx_memL2.aestronglyMeasurable.ae_eq_mk).1 u.gx_memL2

/-- The axial energy of the slice through `z`. -/
def axEnergy_po (C : Cap m) (u : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ s in Ioo (-C.K) (exitTime C z), repGx C u (s, z) ^ 2

theorem axEnergy_nonneg_po (C : Cap m) (u : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) :
    0 ≤ axEnergy_po C u z :=
  setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _

theorem integrableOn_repGx_sq_po (C : Cap m) (u : H1P C.body) :
    IntegrableOn (fun p => repGx C u p ^ 2) C.body volume :=
  (memL2_repGx_po C u).integrable_sq

theorem integrable_indicator_repGx_sq_po (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator fun p => repGx C u p ^ 2) volume :=
  (integrableOn_repGx_sq_po C u).integrable_indicator (measurableSet_body' C)

theorem integrable_axEnergy_po (C : Cap m) (u : H1P C.body) :
    Integrable (axEnergy_po C u) volume :=
  integrable_slice_integral C (integrable_indicator_repGx_sq_po C u)

theorem integral_axEnergy_po (C : Cap m) (u : H1P C.body) :
    (∫ z, axEnergy_po C u z) = ∫ p in C.body, repGx C u p ^ 2 :=
  (integral_body_eq_integral_slices C (integrable_indicator_repGx_sq_po C u)).symm

/-- **The axial deviation bound.**  Almost everywhere on the body, the deviation of `u` from its
entrance value is controlled by the axial energy of the slice. -/
theorem ae_axial_bound_po (C : Cap m) (u : H1P C.body) :
    ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body →
      (repFun C u p - entranceVal C u p.2) ^ 2 ≤ C.K * axEnergy_po C u p.2 := by
  have hint : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      IntegrableOn (fun t => repGx C u (t, z)) (Ioo (-C.K) (exitTime C z)) volume ∧
        IntegrableOn (fun t => repGx C u (t, z) ^ 2) (Ioo (-C.K) (exitTime C z)) volume := by
    filter_upwards [ae_integrableOn_cap_slice C
        (integrableOn_body_of_memL2 C (memL2_repGx_po C u)),
      ae_integrableOn_cap_slice C (integrableOn_repGx_sq_po C u)] with z h1 h2
    exact ⟨h1, h2⟩
  have hlift : ∀ᵐ p ∂(volume : Measure (CapSpace m)),
      IntegrableOn (fun t => repGx C u (t, p.2)) (Ioo (-C.K) (exitTime C p.2)) volume ∧
        IntegrableOn (fun t => repGx C u (t, p.2) ^ 2)
          (Ioo (-C.K) (exitTime C p.2)) volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hint
  filter_upwards [ae_axialDefect_po C u, hlift] with p hdef hI hp
  have hslice : p.1 ∈ Ioo (-C.K) (exitTime C p.2) := ((mem_body_iff C p).1 hp).2
  have hd := hdef hp
  have hval : repFun C u p - entranceVal C u p.2 = ∫ t in (-C.K)..p.1, repGx C u (t, p.2) := by
    have h1 : repFun C u p - entranceVal C u p.2 = slicePrim C u p := by
      rw [axialDefect_po] at hd; linarith
    rw [h1]
    have h2 : slicePrim C u (p.1, p.2) = ∫ t in Ioo (-C.K) p.1, repGx C u (t, p.2) :=
      slicePrim_eq C u p.1 p.2
    rw [show p = (p.1, p.2) from rfl, h2, intervalIntegral_eq_setIntegral_Ioo hslice.1.le]
  rw [hval]
  have hb := sq_intervalIntegral_le hslice.1.le hslice.2.le hI.1 hI.2
  have h0 : 0 ≤ axEnergy_po C u p.2 := axEnergy_nonneg_po C u p.2
  have he : exitTime C p.2 - -C.K ≤ C.K := by
    have := exitTime_le_zero C p.2
    linarith
  have : (exitTime C p.2 - -C.K) * axEnergy_po C u p.2 ≤ C.K * axEnergy_po C u p.2 :=
    mul_le_mul_of_nonneg_right he h0
  exact le_trans hb this

/-! ## 5. The transverse energy of a level -/

/-- A globally strongly measurable representative of `∇_z u`. -/
def repGz_po (C : Cap m) (u : H1P C.body) : CapSpace m → EuclideanSpace ℝ (Fin m) :=
  u.gz_memL2.aestronglyMeasurable.mk u.gz

theorem stronglyMeasurable_repGz_po (C : Cap m) (u : H1P C.body) :
    StronglyMeasurable (repGz_po C u) := u.gz_memL2.aestronglyMeasurable.stronglyMeasurable_mk

theorem repGz_ae_eq_po (C : Cap m) (u : H1P C.body) :
    u.gz =ᵐ[volume.restrict C.body] repGz_po C u :=
  u.gz_memL2.aestronglyMeasurable.ae_eq_mk

theorem memL2_repGz_po (C : Cap m) (u : H1P C.body) :
    MemLp (repGz_po C u) 2 (volume.restrict C.body) :=
  (memLp_congr_ae (repGz_ae_eq_po C u)).1 u.gz_memL2

/-- The transverse energy of the level `σ`, written with an indicator so as to be manifestly
measurable in `σ`. -/
def trEnergy_po (C : Cap m) (u : H1P C.body) (σ : ℝ) : ℝ :=
  ∫ z, (C.body.indicator fun p => ‖repGz_po C u p‖ ^ 2) (σ, z)

theorem integrable_indicator_repGz_sq_po (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator fun p => ‖repGz_po C u p‖ ^ 2) volume := by
  have h : IntegrableOn (fun p => ‖repGz_po C u p‖ ^ 2) C.body volume := by
    have h2 := (memL2_repGz_po C u).norm
    exact h2.integrable_sq
  exact h.integrable_indicator (measurableSet_body' C)

theorem integrable_trEnergy_po (C : Cap m) (u : H1P C.body) :
    Integrable (trEnergy_po C u) volume := by
  have h := integrable_indicator_repGz_sq_po C u
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

theorem integral_trEnergy_po (C : Cap m) (u : H1P C.body) :
    (∫ σ, trEnergy_po C u σ) = ∫ p in C.body, ‖repGz_po C u p‖ ^ 2 := by
  have h := integrable_indicator_repGz_sq_po C u
  rw [← integral_indicator (measurableSet_body' C), Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at h
  exact (integral_prod _ h).symm

theorem trEnergy_nonneg_po (C : Cap m) (u : H1P C.body) (σ : ℝ) : 0 ≤ trEnergy_po C u σ := by
  exact integral_nonneg fun z => Set.indicator_nonneg (fun p _ => by positivity) _

/-! ## 6. Two elementary one-dimensional estimates -/

theorem integrableOn_comp_ept_po {ρ : ℝ} (f : EuclideanSpace ℝ (Fin 1) → ℝ) :
    IntegrableOn (fun y => f (ept y)) (Ioo (-ρ) ρ) volume
      ↔ IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin 1)) ρ) volume := by
  rw [← ept_preimage_ball ρ]
  exact measurePreserving_ept.integrableOn_comp_preimage eptEquiv.measurableEmbedding

theorem integral_ball_ept_po {ρ : ℝ} (hρ : 0 ≤ ρ) (F : EuclideanSpace ℝ (Fin 1) → ℝ) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) ρ, F z) = ∫ y in Ioo (-ρ) ρ, F (ept y) := by
  rw [integral_ball_one hρ F, intervalIntegral_eq_setIntegral_Ioo (by linarith : -ρ ≤ ρ)]

/-- **Cauchy–Schwarz on an arbitrary subinterval.** -/
theorem sq_intervalIntegral_le_po {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
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
    rw [intervalIntegral.integral_symm, neg_pow, ] at h
    simpa using h

/-! ## 7. The transverse deviation bound -/

theorem ae_ae_transverse_repFun_po (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (σ, z) ∈ C.body → repFun C u (σ, z) = u.toFun (σ, z) := by
  have h : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → repFun C u p = u.toFun p := by
    have h0 : u.toFun =ᵐ[volume.restrict C.body] repFun C u :=
      u.memL2.aestronglyMeasurable.ae_eq_mk
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at h0
    filter_upwards [h0] with p hp hpb using (hp hpb).symm
  rw [Measure.volume_eq_prod] at h
  exact Measure.ae_ae_of_ae_prod h

theorem ae_ae_transverse_repGz_po (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (σ, z) ∈ C.body → repGz_po C u (σ, z) = u.gz (σ, z) := by
  have h : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → repGz_po C u p = u.gz p := by
    have h0 := repGz_ae_eq_po C u
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at h0
    filter_upwards [h0] with p hp hpb using (hp hpb).symm
  rw [Measure.volume_eq_prod] at h
  exact Measure.ae_ae_of_ae_prod h

/-- The transverse slice of the body-indicator is the ball-indicator of the slice. -/
theorem indicator_body_transverse_po (C : Cap m) (f : CapSpace m → ℝ) {σ : ℝ}
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
theorem ae_transverse_integrableOn_po (C : Cap 1) {f : CapSpace 1 → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      IntegrableOn (fun y => f (σ, ept y)) (Ioo (-(C.θ σ)) (C.θ σ)) volume := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hf
  filter_upwards [hf'.prod_right_ae] with σ hσ hσI
  refine (integrableOn_comp_ept_po (fun z => f (σ, z))).2 ?_
  refine (integrable_indicator_iff measurableSet_ball).1 ?_
  exact hσ.congr (Eventually.of_forall fun z => indicator_body_transverse_po C f hσI z)

/-- The transverse energy of a level, read through `ept`. -/
theorem ae_trEnergy_eq_po (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      trEnergy_po C u σ = ∫ y in Ioo (-(C.θ σ)) (C.θ σ), (u.gz (σ, ept y) 0) ^ 2 := by
  filter_upwards [ae_ae_transverse_repGz_po C u] with σ hrg hσI
  have hrg' : ∀ᵐ y ∂(volume : Measure ℝ),
      ((σ, ept y) : CapSpace 1) ∈ C.body → repGz_po C u (σ, ept y) = u.gz (σ, ept y) :=
    measurePreserving_ept.quasiMeasurePreserving.ae hrg
  have hmem : ∀ y ∈ Ioo (-(C.θ σ)) (C.θ σ), ((σ, ept y) : CapSpace 1) ∈ C.body := by
    intro y hy
    exact ⟨hσI.1, hσI.2, by rw [ept_norm]; exact abs_lt.2 ⟨hy.1, hy.2⟩⟩
  have hstep1 : trEnergy_po C u σ
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ σ), ‖repGz_po C u (σ, z)‖ ^ 2 := by
    rw [trEnergy_po]
    rw [show (fun z => C.body.indicator (fun p => ‖repGz_po C u p‖ ^ 2) (σ, z))
        = fun z => (ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ σ)).indicator
          (fun z => ‖repGz_po C u (σ, z)‖ ^ 2) z from
      funext fun z => indicator_body_transverse_po C _ hσI z]
    rw [integral_indicator measurableSet_ball]
  rw [hstep1, integral_ball_ept_po (C.θ_pos σ hσI).le]
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [hrg'] with y hy hymem
  rw [hy (hmem y hymem), ← norm_sq_one_dim]

/-- **The transverse deviation bound.**  For almost every level `σ`, any two points of the
transverse section carry values of `u` differing by at most the transverse energy of the
level. -/
theorem ae_transverse_bound_po (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) 0)),
      ∀ᵐ y ∂(volume.restrict (Ioo (-(C.θ σ)) (C.θ σ))),
        ∀ᵐ y' ∂(volume.restrict (Ioo (-(C.θ σ)) (C.θ σ))),
          (repFun C u (σ, ept y) - repFun C u (σ, ept y')) ^ 2 ≤ 2 * trEnergy_po C u σ := by
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
  filter_upwards [sliceAC_transverse_cap_po C u,
    ae_restrict_of_ae (ae_ae_transverse_repFun_po C u),
    ae_restrict_of_ae (ae_transverse_integrableOn_po C hu_ind),
    ae_restrict_of_ae (ae_transverse_integrableOn_po C hgz_ind),
    ae_restrict_of_ae (ae_transverse_integrableOn_po C hgz2_ind),
    ae_restrict_of_ae (ae_trEnergy_eq_po C u),
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
      = trEnergy_po C u σ := (htr hσI).symm
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
  have hbnd := sq_intervalIntegral_le_po (Ioo_subset_Icc_self hymem')
    (Ioo_subset_Icc_self hymem) (hig hσI) (hig2 hσI)
  rw [hgoodE] at hbnd
  have h2 : (C.θ σ - -(C.θ σ)) * trEnergy_po C u σ ≤ 2 * trEnergy_po C u σ :=
    mul_le_mul_of_nonneg_right (by linarith) (trEnergy_nonneg_po C u σ)
  linarith

/-! ## 8. The anchoring level and the far-left strip -/

/-- The anchoring level `τ s = (s - K)/2` of the axial coordinate `s`.  It lies in `(-K,-K/2)`,
to the left of `s`, and depends affinely on `s`. -/
def tau_po (C : Cap m) (s : ℝ) : ℝ := (s - C.K) / 2

theorem tau_mem_po (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    tau_po C s ∈ Ioo (-C.K) (-C.K / 2) :=
  ⟨by simp only [tau_po]; linarith [hs.1], by simp only [tau_po]; linarith [hs.2]⟩

theorem tau_le_po (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) : tau_po C s ≤ s := by
  simp only [tau_po]; linarith [hs.1]

/-- The half-width of the far-left strip, `c = θ(-K/2)/2`. -/
def cwid_po (C : Cap m) : ℝ := C.θ (-C.K / 2) / 2

theorem neg_half_mem_po (C : Cap m) : (-C.K / 2 : ℝ) ∈ Ioo (-C.K) 0 :=
  ⟨by linarith [C.hK], by linarith [C.hK]⟩

theorem cwid_pos_po (C : Cap m) : 0 < cwid_po C := by
  have := C.θ_pos _ (neg_half_mem_po C)
  simp only [cwid_po]; linarith

/-- On the far-left half of the cap the section is wider than the strip. -/
theorem cwid_lt_theta_po (C : Cap m) {σ : ℝ} (hσ : σ ∈ Ioo (-C.K) (-C.K / 2)) :
    cwid_po C < C.θ σ := by
  have h1 : C.θ (-C.K / 2) ≤ C.θ σ :=
    C.θ_antitone ⟨hσ.1, hσ.2.trans (by linarith [C.hK])⟩ (neg_half_mem_po C) hσ.2.le
  have h2 := C.θ_pos _ (neg_half_mem_po C)
  simp only [cwid_po]; linarith

/-! ## 9. Sliced forms of the two deviation bounds -/

theorem ae_ae_axial_bound_po (C : Cap m) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (σ, z) ∈ C.body →
        (repFun C u (σ, z) - entranceVal C u z) ^ 2 ≤ C.K * axEnergy_po C u z := by
  have h := ae_axial_bound_po C u
  rw [Measure.volume_eq_prod] at h
  exact Measure.ae_ae_of_ae_prod h

theorem ae_axial_bound_ept_po (C : Cap 1) (u : H1P C.body) :
    ∀ᵐ σ ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure ℝ),
      ((σ, ept y) : CapSpace 1) ∈ C.body →
        (repFun C u (σ, ept y) - entranceVal C u (ept y)) ^ 2
          ≤ C.K * axEnergy_po C u (ept y) := by
  filter_upwards [ae_ae_axial_bound_po C u] with σ hσ
  exact measurePreserving_ept.quasiMeasurePreserving.ae hσ

theorem integrable_axEnergy_ept_po (C : Cap 1) (u : H1P C.body) :
    Integrable (fun y : ℝ => axEnergy_po C u (ept y)) volume :=
  (measurePreserving_ept.integrable_comp_emb eptEquiv.measurableEmbedding).2
    (integrable_axEnergy_po C u)

/-- Membership of a strip point in the body. -/
theorem mem_body_of_abs_lt_po (C : Cap 1) {σ y : ℝ} (hσ : σ ∈ Ioo (-C.K) 0)
    (hy : |y| < C.θ σ) : ((σ, ept y) : CapSpace 1) ∈ C.body :=
  ⟨hσ.1, hσ.2, by rw [ept_norm]; exact hy⟩

/-- The anchoring map is quasi measure preserving: it is affine with nonzero slope. -/
theorem quasiMeasurePreserving_tau_po (C : Cap m) :
    Measure.QuasiMeasurePreserving (tau_po C) (volume : Measure ℝ) volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun σ : ℝ => σ - C.K) volume volume :=
    (measurePreserving_sub_right (volume : Measure ℝ) C.K).quasiMeasurePreserving
  have h2 : Measure.QuasiMeasurePreserving (fun x : ℝ => (1 / 2 : ℝ) * x) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [Real.map_volume_mul_left (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact Measure.AbsolutelyContinuous.mk fun s hs hs0 => by simp [hs0]
  have h3 := h2.comp h1
  have heq : ((fun x : ℝ => (1 / 2 : ℝ) * x) ∘ fun σ : ℝ => σ - C.K) = tau_po C := by
    funext σ; simp only [Function.comp_apply, tau_po]; ring
  rwa [heq] at h3

theorem ae_comp_tau_po (C : Cap m) {Q : ℝ → Prop} (h : ∀ᵐ x ∂(volume : Measure ℝ), Q x) :
    ∀ᵐ σ ∂(volume : Measure ℝ), Q (tau_po C σ) :=
  (quasiMeasurePreserving_tau_po C).ae h

/-! ## 10. The anchor level -/

theorem integrable_indicator_repFun_po (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator (repFun C u)) volume :=
  (integrableOn_body_of_memL2 C (memL2_repFun_po C u)).integrable_indicator
    (measurableSet_body' C)

theorem integrable_indicator_repFun_sq_po (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator fun p => repFun C u p ^ 2) volume := by
  have h : IntegrableOn (fun p => repFun C u p ^ 2) C.body volume :=
    (memL2_repFun_po C u).integrable_sq
  exact h.integrable_indicator (measurableSet_body' C)

/-- **The anchor level exists.**  Almost every level of the far-left half of the cap carries the
axial deviation bound and an integrable (square integrable) slice; in particular some level
does. -/
theorem exists_anchor_po (C : Cap 1) (u : H1P C.body) :
    ∃ σ₀ : ℝ, σ₀ ∈ Ioo (-C.K) (-C.K / 2) ∧
      (∀ᵐ y ∂(volume : Measure ℝ), ((σ₀, ept y) : CapSpace 1) ∈ C.body →
        (repFun C u (σ₀, ept y) - entranceVal C u (ept y)) ^ 2
          ≤ C.K * axEnergy_po C u (ept y)) ∧
      IntegrableOn (fun y => repFun C u (σ₀, ept y)) (Ioo (-(C.θ σ₀)) (C.θ σ₀)) volume ∧
      IntegrableOn (fun y => repFun C u (σ₀, ept y) ^ 2)
        (Ioo (-(C.θ σ₀)) (C.θ σ₀)) volume := by
  have hpos : (volume : Measure ℝ) (Ioo (-C.K) (-C.K / 2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith [C.hK]
  haveI hne : (ae (volume.restrict (Ioo (-C.K) (-C.K / 2)))).NeBot :=
    ae_neBot.2 (by rw [Ne, Measure.restrict_eq_zero]; exact hpos)
  have hev : ∀ᵐ σ ∂(volume.restrict (Ioo (-C.K) (-C.K / 2))),
      σ ∈ Ioo (-C.K) (-C.K / 2) ∧
      (∀ᵐ y ∂(volume : Measure ℝ), ((σ, ept y) : CapSpace 1) ∈ C.body →
        (repFun C u (σ, ept y) - entranceVal C u (ept y)) ^ 2
          ≤ C.K * axEnergy_po C u (ept y)) ∧
      IntegrableOn (fun y => repFun C u (σ, ept y)) (Ioo (-(C.θ σ)) (C.θ σ)) volume ∧
      IntegrableOn (fun y => repFun C u (σ, ept y) ^ 2)
        (Ioo (-(C.θ σ)) (C.θ σ)) volume := by
    filter_upwards [ae_restrict_of_ae (ae_axial_bound_ept_po C u),
      ae_restrict_of_ae (ae_transverse_integrableOn_po C (integrable_indicator_repFun_po C u)),
      ae_restrict_of_ae
        (ae_transverse_integrableOn_po C (integrable_indicator_repFun_sq_po C u)),
      ae_restrict_mem measurableSet_Ioo] with σ h1 h2 h3 hσ
    have hσ' : σ ∈ Ioo (-C.K) 0 := ⟨hσ.1, hσ.2.trans (by linarith [C.hK])⟩
    exact ⟨hσ, h1, h2 hσ', h3 hσ'⟩
  obtain ⟨σ₀, hσ₀⟩ := hev.exists
  exact ⟨σ₀, hσ₀.1, hσ₀.2.1, hσ₀.2.2.1, hσ₀.2.2.2⟩

/-! ## 11. The pointwise bound -/

/-- Five terms, crudely. -/
theorem sq_five_po (a₁ a₂ a₃ a₄ a₅ : ℝ) :
    (a₁ - a₂ + a₃ + a₄ - a₅) ^ 2 ≤ 5 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 + a₅ ^ 2) := by
  nlinarith [sq_nonneg (a₁ + a₂), sq_nonneg (a₁ - a₃), sq_nonneg (a₁ - a₄), sq_nonneg (a₁ + a₅),
    sq_nonneg (a₂ + a₃), sq_nonneg (a₂ + a₄), sq_nonneg (a₂ - a₅), sq_nonneg (a₃ - a₄),
    sq_nonneg (a₃ + a₅), sq_nonneg (a₄ + a₅)]

/-- The reference constant: the mean of `u` over the transverse segment of the far-left strip
at the anchor level. -/
def tref_po (C : Cap 1) (u : H1P C.body) (σ₀ : ℝ) : ℝ :=
  (2 * cwid_po C)⁻¹ * ∫ w in Ioo (-(cwid_po C)) (cwid_po C), repFun C u (σ₀, ept w)

/-- The mean axial energy over the transverse segment of the far-left strip. -/
def avgA_po (C : Cap 1) (u : H1P C.body) : ℝ :=
  (2 * cwid_po C)⁻¹ * ∫ w in Ioo (-(cwid_po C)) (cwid_po C), axEnergy_po C u (ept w)

/-- **The pointwise bound.**  For almost every level `σ` of the cap and almost every point of
its transverse section, `u` differs from the reference constant by at most the axial energy of
the axial line through the point, the transverse energy of the anchoring level `τ σ`, and the
mean axial energy of the strip. -/
theorem ae_pointwise_bound_po (C : Cap 1) (u : H1P C.body) {σ₀ : ℝ}
    (hσ₀ : σ₀ ∈ Ioo (-C.K) (-C.K / 2))
    (hanch : ∀ᵐ y ∂(volume : Measure ℝ), ((σ₀, ept y) : CapSpace 1) ∈ C.body →
      (repFun C u (σ₀, ept y) - entranceVal C u (ept y)) ^ 2
        ≤ C.K * axEnergy_po C u (ept y))
    (hi1 : IntegrableOn (fun y => repFun C u (σ₀, ept y)) (Ioo (-(C.θ σ₀)) (C.θ σ₀)) volume)
    (hi2 : IntegrableOn (fun y => repFun C u (σ₀, ept y) ^ 2)
      (Ioo (-(C.θ σ₀)) (C.θ σ₀)) volume) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (-C.K) 0 →
      ∀ᵐ y ∂(volume.restrict (Ioo (-(C.θ σ)) (C.θ σ))),
        (repFun C u (σ, ept y) - tref_po C u σ₀) ^ 2
          ≤ 10 * C.K * axEnergy_po C u (ept y) + 10 * trEnergy_po C u (tau_po C σ)
            + 10 * C.K * avgA_po C u := by
  set c := cwid_po C with hcdef
  have hc0 : 0 < c := cwid_pos_po C
  have hcc : -c ≤ c := by linarith
  have hcθ0 : c < C.θ σ₀ := cwid_lt_theta_po C hσ₀
  have hsub0 : Ioo (-c) c ⊆ Ioo (-(C.θ σ₀)) (C.θ σ₀) :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have hi1' : IntegrableOn (fun y => repFun C u (σ₀, ept y)) (Ioo (-c) c) volume :=
    hi1.mono_set hsub0
  have hi2' : IntegrableOn (fun y => repFun C u (σ₀, ept y) ^ 2) (Ioo (-c) c) volume :=
    hi2.mono_set hsub0
  have hA : IntegrableOn (fun y => axEnergy_po C u (ept y)) (Ioo (-c) c) volume :=
    (integrable_axEnergy_ept_po C u).integrableOn
  have hvol : (volume.real (Ioo (-c) c)) = 2 * c := by
    rw [Real.volume_real_Ioo_of_le hcc]; ring
  have htrefval : (∫ w in Ioo (-c) c, repFun C u (σ₀, ept w)) = 2 * c * tref_po C u σ₀ := by
    rw [tref_po, ← hcdef, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have havgval : (∫ w in Ioo (-c) c, axEnergy_po C u (ept w)) = 2 * c * avgA_po C u := by
    rw [avgA_po, ← hcdef, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  filter_upwards [ae_axial_bound_ept_po C u,
    ae_comp_tau_po C (ae_axial_bound_ept_po C u),
    ae_comp_tau_po C ((ae_restrict_iff' measurableSet_Ioo).1 (ae_transverse_bound_po C u))]
    with σ hb1 hb2 hb3 hσI
  have hτ : tau_po C σ ∈ Ioo (-C.K) (-C.K / 2) := tau_mem_po C hσI
  have hτ0 : tau_po C σ ∈ Ioo (-C.K) 0 := ⟨hτ.1, hτ.2.trans (by linarith [C.hK])⟩
  have hθτ : C.θ σ ≤ C.θ (tau_po C σ) := C.θ_antitone hτ0 hσI (tau_le_po C hσI)
  have hcτ : c < C.θ (tau_po C σ) := cwid_lt_theta_po C hτ
  have hsubτ : Ioo (-(C.θ σ)) (C.θ σ) ⊆ Ioo (-(C.θ (tau_po C σ))) (C.θ (tau_po C σ)) :=
    Ioo_subset_Ioo (by linarith) hθτ
  have hsubc : Ioo (-c) c ⊆ Ioo (-(C.θ (tau_po C σ))) (C.θ (tau_po C σ)) :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have hb3' := hb3 hτ0
  have hb3'' : ∀ᵐ y ∂(volume.restrict (Ioo (-(C.θ σ)) (C.θ σ))),
      ∀ᵐ y' ∂(volume.restrict (Ioo (-(C.θ (tau_po C σ))) (C.θ (tau_po C σ)))),
        (repFun C u (tau_po C σ, ept y) - repFun C u (tau_po C σ, ept y')) ^ 2
          ≤ 2 * trEnergy_po C u (tau_po C σ) :=
    ae_mono (Measure.restrict_mono hsubτ le_rfl) hb3'
  filter_upwards [ae_restrict_of_ae hb1, ae_restrict_of_ae hb2, hb3'',
    ae_restrict_mem measurableSet_Ioo] with y hy1 hy2 hy3 hymem
  have habsy : |y| < C.θ σ := abs_lt.2 ⟨hymem.1, hymem.2⟩
  have hmemσ : ((σ, ept y) : CapSpace 1) ∈ C.body := mem_body_of_abs_lt_po C hσI habsy
  have hmemτ : ((tau_po C σ, ept y) : CapSpace 1) ∈ C.body :=
    mem_body_of_abs_lt_po C hτ0 (lt_of_lt_of_le habsy hθτ)
  set V : ℝ := repFun C u (σ, ept y) with hV
  set R : ℝ := 10 * C.K * axEnergy_po C u (ept y) + 10 * trEnergy_po C u (tau_po C σ) with hR
  -- the pointwise chain bound, for almost every point of the strip segment
  have hkey : ∀ᵐ w ∂(volume.restrict (Ioo (-c) c)),
      (V - repFun C u (σ₀, ept w)) ^ 2 ≤ R + 10 * C.K * axEnergy_po C u (ept w) := by
    have hy3c : ∀ᵐ w ∂(volume.restrict (Ioo (-c) c)),
        (repFun C u (tau_po C σ, ept y) - repFun C u (tau_po C σ, ept w)) ^ 2
          ≤ 2 * trEnergy_po C u (tau_po C σ) :=
      ae_mono (Measure.restrict_mono hsubc le_rfl) hy3
    filter_upwards [hy3c, ae_restrict_of_ae hb2, ae_restrict_of_ae hanch,
      ae_restrict_mem measurableSet_Ioo] with w t1 t2 t3 hwmem
    have habsw : |w| < c := abs_lt.2 ⟨hwmem.1, hwmem.2⟩
    have hmemτw : ((tau_po C σ, ept w) : CapSpace 1) ∈ C.body :=
      mem_body_of_abs_lt_po C hτ0 (by linarith)
    have hmem0w : ((σ₀, ept w) : CapSpace 1) ∈ C.body :=
      mem_body_of_abs_lt_po C ⟨hσ₀.1, hσ₀.2.trans (by linarith [C.hK])⟩ (by linarith)
    have e1 := hy1 hmemσ
    have e2 := hy2 hmemτ
    have e4 := t2 hmemτw
    have e5 := t3 hmem0w
    have hchain : V - repFun C u (σ₀, ept w)
        = (V - entranceVal C u (ept y))
          - (repFun C u (tau_po C σ, ept y) - entranceVal C u (ept y))
          + (repFun C u (tau_po C σ, ept y) - repFun C u (tau_po C σ, ept w))
          + (repFun C u (tau_po C σ, ept w) - entranceVal C u (ept w))
          - (repFun C u (σ₀, ept w) - entranceVal C u (ept w)) := by ring
    rw [hchain]
    have h5 := sq_five_po (V - entranceVal C u (ept y))
      (repFun C u (tau_po C σ, ept y) - entranceVal C u (ept y))
      (repFun C u (tau_po C σ, ept y) - repFun C u (tau_po C σ, ept w))
      (repFun C u (tau_po C σ, ept w) - entranceVal C u (ept w))
      (repFun C u (σ₀, ept w) - entranceVal C u (ept w))
    rw [hR]
    linarith
  -- Cauchy-Schwarz over the segment
  have hconstV : IntegrableOn (fun _ : ℝ => V) (Ioo (-c) c) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hconstV2 : IntegrableOn (fun _ : ℝ => V ^ 2) (Ioo (-c) c) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hconstR : IntegrableOn (fun _ : ℝ => R) (Ioo (-c) c) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hdiff : IntegrableOn (fun w => V - repFun C u (σ₀, ept w)) (Ioo (-c) c) volume :=
    hconstV.sub hi1'
  have hdiff2 : IntegrableOn (fun w => (V - repFun C u (σ₀, ept w)) ^ 2) (Ioo (-c) c) volume := by
    have h : (fun w => (V - repFun C u (σ₀, ept w)) ^ 2)
        = fun w => V ^ 2 - 2 * V * repFun C u (σ₀, ept w) + repFun C u (σ₀, ept w) ^ 2 := by
      funext w; ring
    rw [h]
    exact (hconstV2.sub (hi1'.const_mul (2 * V))).add hi2'
  have hmaj : IntegrableOn (fun w => R + 10 * C.K * axEnergy_po C u (ept w))
      (Ioo (-c) c) volume :=
    hconstR.add (hA.const_mul _)
  have hint1 : (∫ w in Ioo (-c) c, (V - repFun C u (σ₀, ept w)))
      = 2 * c * (V - tref_po C u σ₀) := by
    rw [integral_sub hconstV hi1', setIntegral_const, htrefval, smul_eq_mul, hvol]
    ring
  have hcs : (∫ w in Ioo (-c) c, (V - repFun C u (σ₀, ept w))) ^ 2
      ≤ (2 * c) * ∫ w in Ioo (-c) c, (V - repFun C u (σ₀, ept w)) ^ 2 := by
    have h := sq_intervalIntegral_le_po (a := -c) (b := c) (x := -c) (y := c)
      ⟨le_rfl, hcc⟩ ⟨hcc, le_rfl⟩ hdiff hdiff2
    rw [intervalIntegral_eq_setIntegral_Ioo hcc] at h
    have : c - -c = 2 * c := by ring
    rwa [this] at h
  have hmono : (∫ w in Ioo (-c) c, (V - repFun C u (σ₀, ept w)) ^ 2)
      ≤ ∫ w in Ioo (-c) c, (R + 10 * C.K * axEnergy_po C u (ept w)) :=
    integral_mono_ae hdiff2 hmaj hkey
  have hmajval : (∫ w in Ioo (-c) c, (R + 10 * C.K * axEnergy_po C u (ept w)))
      = 2 * c * R + 10 * C.K * (2 * c * avgA_po C u) := by
    rw [integral_add hconstR (hA.const_mul _), setIntegral_const,
      integral_const_mul, havgval, smul_eq_mul, hvol]
  rw [hint1] at hcs
  have hfin : (2 * c) ^ 2 * (V - tref_po C u σ₀) ^ 2
      ≤ (2 * c) * (2 * c * R + 10 * C.K * (2 * c * avgA_po C u)) := by
    calc (2 * c) ^ 2 * (V - tref_po C u σ₀) ^ 2 = (2 * c * (V - tref_po C u σ₀)) ^ 2 := by ring
      _ ≤ (2 * c) * ∫ w in Ioo (-c) c, (V - repFun C u (σ₀, ept w)) ^ 2 := hcs
      _ ≤ (2 * c) * ∫ w in Ioo (-c) c, (R + 10 * C.K * axEnergy_po C u (ept w)) := by
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (2 * c) * (2 * c * R + 10 * C.K * (2 * c * avgA_po C u)) := by rw [hmajval]
  have hfin2 : (2 * c) ^ 2 * (V - tref_po C u σ₀) ^ 2
      ≤ (2 * c) ^ 2 * (R + 10 * C.K * avgA_po C u) :=
    calc (2 * c) ^ 2 * (V - tref_po C u σ₀) ^ 2
        ≤ (2 * c) * (2 * c * R + 10 * C.K * (2 * c * avgA_po C u)) := hfin
      _ = (2 * c) ^ 2 * (R + 10 * C.K * avgA_po C u) := by ring
  exact le_of_mul_le_mul_left hfin2 (by positivity)

/-! ## 12. Fubini in the transverse direction -/

/-- **Fubini for the cap body** in the order `σ` outer, `z` inner. -/
theorem integral_body_eq_slices_tr_po (C : Cap m) {F : CapSpace m → ℝ}
    (hF : Integrable (C.body.indicator F) volume) :
    (∫ p in C.body, F p) = ∫ σ, ∫ z, (C.body.indicator F) (σ, z) := by
  rw [← integral_indicator (measurableSet_body' C), Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at hF
  exact integral_prod _ hF

theorem integrable_slice_integral_tr_po (C : Cap m) {F : CapSpace m → ℝ}
    (hF : Integrable (C.body.indicator F) volume) :
    Integrable (fun σ => ∫ z, (C.body.indicator F) (σ, z)) volume := by
  rw [Measure.volume_eq_prod] at hF
  exact hF.integral_prod_left

theorem inner_slice_eq_po (C : Cap 1) (F : CapSpace 1 → ℝ) {σ : ℝ} (hσ : σ ∈ Ioo (-C.K) 0) :
    (∫ z, (C.body.indicator F) (σ, z)) = ∫ y in Ioo (-(C.θ σ)) (C.θ σ), F (σ, ept y) := by
  rw [show (fun z => C.body.indicator F (σ, z))
      = fun z => (ball (0 : EuclideanSpace ℝ (Fin 1)) (C.θ σ)).indicator
        (fun z => F (σ, z)) z from funext (indicator_body_transverse_po C F hσ),
    integral_indicator measurableSet_ball, integral_ball_ept_po (C.θ_pos σ hσ).le]

theorem inner_slice_zero_po (C : Cap m) (F : CapSpace m → ℝ) {σ : ℝ}
    (hσ : σ ∉ Ioo (-C.K) 0) : (∫ z, (C.body.indicator F) (σ, z)) = 0 := by
  have h : ∀ z, (C.body.indicator F) (σ, z) = 0 := fun z =>
    Set.indicator_of_notMem (fun hb => hσ ⟨hb.1, hb.2.1⟩) _
  simp only [h]
  exact integral_zero _ _

/-! ## 13. Integrability of the majorant -/

theorem integrable_trEnergy_tau_po (C : Cap m) (u : H1P C.body) :
    Integrable (fun σ => trEnergy_po C u (tau_po C σ)) volume := by
  have h1 : Integrable (fun x : ℝ => trEnergy_po C u (x / 2)) volume :=
    (integrable_trEnergy_po C u).comp_div (by norm_num : (2 : ℝ) ≠ 0)
  have h2 := h1.comp_sub_right C.K
  refine h2.congr (Eventually.of_forall fun σ => ?_)
  simp only [tau_po]

theorem integrable_indicator_axEnergy_snd_po (C : Cap m) (u : H1P C.body) :
    Integrable (C.body.indicator fun p : CapSpace m => axEnergy_po C u p.2) volume := by
  have hev : IntegrableOn (axEnergy_po C u) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume :=
    (integrable_axEnergy_po C u).integrableOn
  have h : IntegrableOn (fun p : CapSpace m => axEnergy_po C u p.2) C.body volume :=
    (integrableOn_prodBox_transverse C hev).mono_set (body_subset_prod C)
  exact h.integrable_indicator (measurableSet_body' C)

theorem inv_two_cwid_nonneg_po (C : Cap m) : (0 : ℝ) ≤ (2 * cwid_po C)⁻¹ :=
  inv_nonneg.2 (by linarith [cwid_pos_po C])

theorem avgA_nonneg_po (C : Cap 1) (u : H1P C.body) : 0 ≤ avgA_po C u := by
  refine mul_nonneg (inv_two_cwid_nonneg_po C) ?_
  exact setIntegral_nonneg measurableSet_Ioo fun y _ => axEnergy_nonneg_po C u (ept y)

theorem avgA_le_po (C : Cap 1) (u : H1P C.body) :
    avgA_po C u ≤ (2 * cwid_po C)⁻¹ * ∫ p in C.body, repGx C u p ^ 2 := by
  have h1 : (∫ w in Ioo (-(cwid_po C)) (cwid_po C), axEnergy_po C u (ept w))
      ≤ ∫ w : ℝ, axEnergy_po C u (ept w) :=
    setIntegral_le_integral (integrable_axEnergy_ept_po C u)
      (Eventually.of_forall fun y => axEnergy_nonneg_po C u (ept y))
  have h2 : (∫ w : ℝ, axEnergy_po C u (ept w)) = ∫ p in C.body, repGx C u p ^ 2 := by
    rw [measurePreserving_ept.integral_comp eptEquiv.measurableEmbedding (axEnergy_po C u),
      integral_axEnergy_po]
  rw [avgA_po]
  refine mul_le_mul_of_nonneg_left ?_ (inv_two_cwid_nonneg_po C)
  rw [← h2]; exact h1

/-! ## 14. The Poincaré–Wirtinger inequality on a two-dimensional cap -/

theorem exists_t_massP_bound_po (C : Cap 1) (u : H1P C.body) :
    ∃ t : ℝ, massP (u - constP C t)
      ≤ (10 * C.K ^ 2 + 10 * C.K ^ 2 / cwid_po C) * (∫ p in C.body, repGx C u p ^ 2)
        + 40 * ∫ p in C.body, ‖repGz_po C u p‖ ^ 2 := by
  obtain ⟨σ₀, hσ₀, hanch, hi1, hi2⟩ := exists_anchor_po C u
  refine ⟨tref_po C u σ₀, ?_⟩
  set t := tref_po C u σ₀ with htdef
  have hc0 : 0 < cwid_po C := cwid_pos_po C
  set A : ℝ := ∫ p in C.body, repGx C u p ^ 2 with hA
  set B : ℝ := ∫ p in C.body, ‖repGz_po C u p‖ ^ 2 with hB
  -- the integrand and its integrability
  have hFmem : MemLp (fun p => repFun C u p - t) 2 (volume.restrict C.body) :=
    (memL2_repFun_po C u).sub (memLp_const t)
  have hFsq : IntegrableOn (fun p => (repFun C u p - t) ^ 2) C.body volume :=
    hFmem.integrable_sq
  have hFint : Integrable (C.body.indicator fun p => (repFun C u p - t) ^ 2) volume :=
    hFsq.integrable_indicator (measurableSet_body' C)
  have hAint : Integrable (C.body.indicator fun p : CapSpace 1 => axEnergy_po C u p.2) volume :=
    integrable_indicator_axEnergy_snd_po C u
  -- step 1: pass to the measurable representative
  have hstep1 : massP (u - constP C t) = ∫ p in C.body, (repFun C u p - t) ^ 2 := by
    rw [massP]
    refine integral_congr_ae ?_
    filter_upwards [u.memL2.aestronglyMeasurable.ae_eq_mk] with p hp
    rw [sub_constP_toFun C u t p, hp]
    rfl
  -- step 2: Fubini
  have hstep2 : (∫ p in C.body, (repFun C u p - t) ^ 2)
      = ∫ σ, ∫ z, (C.body.indicator fun p => (repFun C u p - t) ^ 2) (σ, z) :=
    integral_body_eq_slices_tr_po C hFint
  -- step 3: the slice-wise bound
  have hIM : ∀ᵐ σ ∂(volume : Measure ℝ),
      (∫ z, (C.body.indicator fun p => (repFun C u p - t) ^ 2) (σ, z))
        ≤ 10 * C.K * (∫ z, (C.body.indicator fun p : CapSpace 1 => axEnergy_po C u p.2) (σ, z))
          + (Ioo (-C.K) 0).indicator
            (fun σ => 20 * trEnergy_po C u (tau_po C σ) + 20 * C.K * avgA_po C u) σ := by
    filter_upwards [ae_pointwise_bound_po C u hσ₀ hanch hi1 hi2,
      ae_transverse_integrableOn_po C hFint] with σ hpt hint
    by_cases hσ : σ ∈ Ioo (-C.K) 0
    · have hθ0 : 0 < C.θ σ := C.θ_pos σ hσ
      have hθ1 : C.θ σ ≤ 1 := C.θ_le_one σ hσ
      have hcc : -(C.θ σ) ≤ C.θ σ := by linarith
      have hvol : (volume.real (Ioo (-(C.θ σ)) (C.θ σ))) = 2 * C.θ σ := by
        rw [Real.volume_real_Ioo_of_le hcc]; ring
      have hA' : IntegrableOn (fun y => axEnergy_po C u (ept y))
          (Ioo (-(C.θ σ)) (C.θ σ)) volume := (integrable_axEnergy_ept_po C u).integrableOn
      have hconst : IntegrableOn
          (fun _ : ℝ => 10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u)
          (Ioo (-(C.θ σ)) (C.θ σ)) volume := integrableOn_const measure_Ioo_lt_top.ne
      have hmaj : IntegrableOn (fun y => 10 * C.K * axEnergy_po C u (ept y)
          + (10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u))
          (Ioo (-(C.θ σ)) (C.θ σ)) volume := (hA'.const_mul _).add hconst
      have hmono : (∫ y in Ioo (-(C.θ σ)) (C.θ σ), (repFun C u (σ, ept y) - t) ^ 2)
          ≤ ∫ y in Ioo (-(C.θ σ)) (C.θ σ), (10 * C.K * axEnergy_po C u (ept y)
            + (10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u)) := by
        refine integral_mono_ae (hint hσ) hmaj ?_
        filter_upwards [hpt hσ] with y hy
        linarith [hy]
      have hval : (∫ y in Ioo (-(C.θ σ)) (C.θ σ), (10 * C.K * axEnergy_po C u (ept y)
            + (10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u)))
          = 10 * C.K * (∫ y in Ioo (-(C.θ σ)) (C.θ σ), axEnergy_po C u (ept y))
            + (2 * C.θ σ) * (10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u) := by
        rw [integral_add (hA'.const_mul _) hconst, integral_const_mul, setIntegral_const,
          smul_eq_mul, hvol]
      rw [inner_slice_eq_po C _ hσ, inner_slice_eq_po C _ hσ, Set.indicator_of_mem hσ]
      have hbr : 0 ≤ 10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u := by
        have := trEnergy_nonneg_po C u (tau_po C σ)
        have := avgA_nonneg_po C u
        have := C.hK.le
        positivity
      have hle2 : (2 * C.θ σ) * (10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u)
          ≤ 2 * (10 * trEnergy_po C u (tau_po C σ) + 10 * C.K * avgA_po C u) :=
        mul_le_mul_of_nonneg_right (by linarith) hbr
      rw [hval] at hmono
      linarith
    · rw [inner_slice_zero_po C _ hσ, inner_slice_zero_po C _ hσ,
        Set.indicator_of_notMem hσ]
      simp
  -- step 4: integrate the slice-wise bound
  have hIntInner : Integrable
      (fun σ => ∫ z, (C.body.indicator fun p => (repFun C u p - t) ^ 2) (σ, z)) volume :=
    integrable_slice_integral_tr_po C hFint
  have hIntA : Integrable
      (fun σ => ∫ z, (C.body.indicator fun p : CapSpace 1 => axEnergy_po C u p.2) (σ, z))
      volume := integrable_slice_integral_tr_po C hAint
  have hIntInd : Integrable ((Ioo (-C.K) 0).indicator
      (fun σ => 20 * trEnergy_po C u (tau_po C σ) + 20 * C.K * avgA_po C u)) volume := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioo
    exact ((integrable_trEnergy_tau_po C u).integrableOn.const_mul _).add
      (integrableOn_const measure_Ioo_lt_top.ne)
  have hMajInt : Integrable (fun σ =>
      10 * C.K * (∫ z, (C.body.indicator fun p : CapSpace 1 => axEnergy_po C u p.2) (σ, z))
        + (Ioo (-C.K) 0).indicator
          (fun σ => 20 * trEnergy_po C u (tau_po C σ) + 20 * C.K * avgA_po C u) σ) volume :=
    (hIntA.const_mul (10 * C.K)).add hIntInd
  have hstep4 : (∫ σ, ∫ z, (C.body.indicator fun p => (repFun C u p - t) ^ 2) (σ, z))
      ≤ 10 * C.K * (∫ σ, ∫ z,
            (C.body.indicator fun p : CapSpace 1 => axEnergy_po C u p.2) (σ, z))
        + ∫ σ, (Ioo (-C.K) 0).indicator
            (fun σ => 20 * trEnergy_po C u (tau_po C σ) + 20 * C.K * avgA_po C u) σ := by
    have h := integral_mono_ae hIntInner hMajInt hIM
    rwa [integral_add (hIntA.const_mul _) hIntInd, integral_const_mul] at h
  -- step 5a: the axial term
  have haxint : (∫ σ, ∫ z, (C.body.indicator fun p : CapSpace 1 => axEnergy_po C u p.2) (σ, z))
      = ∫ p in C.body, axEnergy_po C u p.2 := (integral_body_eq_slices_tr_po C hAint).symm
  have haxle : (∫ p in C.body, axEnergy_po C u p.2) ≤ C.K * A := by
    have h1 : (∫ p in C.body, axEnergy_po C u p.2)
        ≤ C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, axEnergy_po C u z :=
      integral_body_transverse_le' C (fun z => axEnergy_nonneg_po C u z)
        (integrable_axEnergy_po C u).integrableOn
    have h2 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, axEnergy_po C u z)
        ≤ ∫ z, axEnergy_po C u z :=
      setIntegral_le_integral (integrable_axEnergy_po C u)
        (Eventually.of_forall fun z => axEnergy_nonneg_po C u z)
    have h3 : (∫ z, axEnergy_po C u z) = A := integral_axEnergy_po C u
    rw [← h3]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 C.hK.le)
  -- step 5b: the transverse term
  have htrle : (∫ σ, (Ioo (-C.K) 0).indicator
      (fun σ => 20 * trEnergy_po C u (tau_po C σ) + 20 * C.K * avgA_po C u) σ)
      ≤ 40 * B + 20 * C.K ^ 2 * avgA_po C u := by
    rw [integral_indicator measurableSet_Ioo,
      integral_add ((integrable_trEnergy_tau_po C u).integrableOn.const_mul _)
        (integrableOn_const measure_Ioo_lt_top.ne), integral_const_mul, setIntegral_const,
      smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith [C.hK] : -C.K ≤ (0 : ℝ))]
    have hT : (∫ σ in Ioo (-C.K) 0, trEnergy_po C u (tau_po C σ)) ≤ 2 * B := by
      have he : (fun σ : ℝ => trEnergy_po C u (tau_po C σ))
          = fun σ : ℝ => trEnergy_po C u (σ / 2 - C.K / 2) := by
        funext σ; simp only [tau_po]; ring_nf
      have h1 : (∫ σ in Ioo (-C.K) 0, trEnergy_po C u (tau_po C σ))
          = ∫ σ in (-C.K)..(0 : ℝ), trEnergy_po C u (tau_po C σ) :=
        (intervalIntegral_eq_setIntegral_Ioo (by linarith [C.hK])).symm
      rw [h1, he, intervalIntegral.integral_comp_div_sub (trEnergy_po C u)
        (by norm_num : (2 : ℝ) ≠ 0) (C.K / 2)]
      have h2 : (-C.K) / 2 - C.K / 2 = -C.K := by ring
      have h3 : (0 : ℝ) / 2 - C.K / 2 = -C.K / 2 := by ring
      rw [h2, h3, smul_eq_mul,
        intervalIntegral_eq_setIntegral_Ioo (by linarith [C.hK] : -C.K ≤ -C.K / 2)]
      have h4 : (∫ x in Ioo (-C.K) (-C.K / 2), trEnergy_po C u x) ≤ ∫ x, trEnergy_po C u x :=
        setIntegral_le_integral (integrable_trEnergy_po C u)
          (Eventually.of_forall fun x => trEnergy_nonneg_po C u x)
      have h5 : (∫ x, trEnergy_po C u x) = B := integral_trEnergy_po C u
      rw [h5] at h4
      linarith
    have hBnn : 0 ≤ B :=
      setIntegral_nonneg (measurableSet_body' C) fun p _ => by positivity
    nlinarith [hT, C.hK.le]
  -- assembling
  have havg : 20 * C.K ^ 2 * avgA_po C u ≤ 10 * C.K ^ 2 / cwid_po C * A := by
    have h := avgA_le_po C u
    rw [← hA] at h
    have h2 : 20 * C.K ^ 2 * avgA_po C u ≤ 20 * C.K ^ 2 * ((2 * cwid_po C)⁻¹ * A) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : 20 * C.K ^ 2 * ((2 * cwid_po C)⁻¹ * A) = 10 * C.K ^ 2 / cwid_po C * A := by
      field_simp
      ring
    linarith [h2, h3.le, h3.ge]
  rw [hstep1, hstep2]
  have hfinal := hstep4
  rw [haxint] at hfinal
  have hK0 : (0 : ℝ) ≤ 10 * C.K := by linarith [C.hK.le]
  have h6 : 10 * C.K * (∫ p in C.body, axEnergy_po C u p.2) ≤ 10 * C.K * (C.K * A) :=
    mul_le_mul_of_nonneg_left haxle hK0
  nlinarith [hfinal, h6, htrle, havg]

theorem integrableOn_repGz_sq_po (C : Cap m) (u : H1P C.body) :
    IntegrableOn (fun p => ‖repGz_po C u p‖ ^ 2) C.body volume :=
  ((memL2_repGz_po C u).norm).integrable_sq

theorem dirichletP_eq_rep_po (C : Cap m) (u : H1P C.body) :
    dirichletP u = (∫ p in C.body, repGx C u p ^ 2)
      + ∫ p in C.body, ‖repGz_po C u p‖ ^ 2 := by
  have hae : ∀ᵐ p ∂(volume.restrict C.body),
      u.gx p ^ 2 + ‖u.gz p‖ ^ 2 = repGx C u p ^ 2 + ‖repGz_po C u p‖ ^ 2 := by
    filter_upwards [u.gx_memL2.aestronglyMeasurable.ae_eq_mk, repGz_ae_eq_po C u] with p h1 h2
    have e2 : repGz_po C u p = u.gz_memL2.aestronglyMeasurable.mk u.gz p := rfl
    have h2' : u.gz p = u.gz_memL2.aestronglyMeasurable.mk u.gz p := h2.trans e2
    rw [show repGx C u p = u.gx_memL2.aestronglyMeasurable.mk u.gx p from rfl, e2, ← h1, ← h2']
  rw [dirichletP, integral_congr_ae hae,
    integral_add (integrableOn_repGx_sq_po C u) (integrableOn_repGz_sq_po C u)]

/-- **The Poincaré–Wirtinger inequality on a two-dimensional cap body.**  Every weak `H¹`
function on the body of a cap of transverse dimension `1` is `L²`-close to a constant at the
scale of its Dirichlet energy; this discharges the interface `RobinCaps.Cap.CapPoincare`.

An admissible constant is `CP = 10K² + 20K²/θ(-K/2) + 40`. -/
theorem capPoincare_one (C : Cap 1) : ∃ CP : ℝ, CapPoincare C CP := by
  have hc0 : 0 < cwid_po C := cwid_pos_po C
  have hK0 : (0 : ℝ) < C.K := C.hK
  refine ⟨10 * C.K ^ 2 + 10 * C.K ^ 2 / cwid_po C + 40, ⟨by positivity, fun u => ?_⟩⟩
  obtain ⟨t, ht⟩ := exists_t_massP_bound_po C u
  refine ⟨t, ?_⟩
  set A : ℝ := ∫ p in C.body, repGx C u p ^ 2 with hAdef
  set B : ℝ := ∫ p in C.body, ‖repGz_po C u p‖ ^ 2 with hBdef
  have hA0 : 0 ≤ A := setIntegral_nonneg (measurableSet_body' C) fun p _ => sq_nonneg _
  have hB0 : 0 ≤ B := setIntegral_nonneg (measurableSet_body' C) fun p _ => by positivity
  have hdir : dirichletP u = A + B := dirichletP_eq_rep_po C u
  rw [hdir]
  have hα : (0 : ℝ) ≤ 10 * C.K ^ 2 + 10 * C.K ^ 2 / cwid_po C := by positivity
  nlinarith [ht, hA0, hB0, hα]

end

end Cap
end RobinCaps
